// Copyright 2024-2025 Irreducible Inc.

//! Example of a Binius SNARK that proves execution of Poseidon2b permutations.

use std::array;

use anyhow::Result;
use binius_core::{oracle::OracleId, transparent::constant::Constant};
use binius_field::{BinaryField32b, Field, PackedField, TowerField};
use binius_math::{ArithCircuit, ArithExpr};

use crate::builder::{ConstraintSystemBuilder, types::F};

type B32 = BinaryField32b;
const P_ROUNDS: usize = 15;
const F_ROUNDS: usize = 8;
const N_ROUNDS: usize = F_ROUNDS + P_ROUNDS;

const STATE_SIZE: usize = 16;

fn plain_permutation(state: &mut [BinaryField32b; STATE_SIZE], n_rounds: usize) {
	// initial mds matrix mult
	let mds_input = state.clone();
	for i in 0..state.len() {
		// mds matrix mult
		let mut mds_out_curr = B32::ZERO;
		for j in 0..STATE_SIZE {
			mds_out_curr += BinaryField32b::new(MDS_FULL[i][j] as u32) * mds_input[j];
		}
		state[i] = mds_out_curr;
	}

	//full and partial rounds
	for r in 0..n_rounds {
		if r < F_ROUNDS / 2 || r >= F_ROUNDS / 2 + P_ROUNDS {
			//  Full (external) rounds

			for i in 0..state.len() {
				//rc add
				state[i] = state[i] + BinaryField32b::new(RC[i][r]);
			}

			for i in 0..state.len() {
				//sbox
				state[i] = state[i].pow(7);
			}

			let mds_input = state.clone();
			for i in 0..state.len() {
				// mds matrix mult
				let mut mds_out_curr = B32::ZERO;
				for j in 0..STATE_SIZE {
					mds_out_curr += BinaryField32b::new(MDS_FULL[i][j] as u32) * mds_input[j];
				}
				state[i] = mds_out_curr;
			}
		} else {
			//  Partial (internal) rounds
			// rc add
			state[0] = state[0] + BinaryField32b::new(RC[0][r]);
			//sbox
			state[0] = state[0].pow(7);
			// mds matrix mult
			let mds_input = state.clone();
			for i in 0..state.len() {
				// mds matrix mult
				let mut mds_out_curr = B32::ZERO;
				for j in 0..STATE_SIZE {
					mds_out_curr += BinaryField32b::new(MDS_PARTIAL[i][j] as u32) * mds_input[j];
				}
				state[i] = mds_out_curr;
			}
		}
	}
}

pub fn permutation(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	p_in: [OracleId; STATE_SIZE],
) -> Result<[OracleId; STATE_SIZE]> {
	println!("Number of rounds: {}", F_ROUNDS + P_ROUNDS);

	let round_0_input: [OracleId; STATE_SIZE] = array::from_fn(|row| {
		builder
			.add_linear_combination(
				format!("mds_out_full_{}", row),
				log_size,
				MDS_FULL[row]
					.iter()
					.enumerate()
					.map(|(i, &elem)| (p_in[i], F::from(BinaryField32b::from(elem as u32)))),
			)
			.unwrap()
	});

	if let Some(witness) = builder.witness() {
		let perm_in_data_owned: [_; STATE_SIZE] =
			array_util::try_from_fn(|i| witness.get::<B32>(p_in[i]))?;
		let perm_in_data: [_; STATE_SIZE] = perm_in_data_owned.map(|elem| elem.as_slice::<B32>());
		let mut round_0_input_data: [_; STATE_SIZE] =
			round_0_input.map(|id| witness.new_column::<B32>(id));
		let round_0_input_32b = round_0_input_data
			.each_mut()
			.map(|elem| elem.as_mut_slice::<B32>());

		for z in 0..1 << log_size {
			for i in 0..STATE_SIZE {
				let mut mds_out_curr = B32::ZERO;
				for j in 0..STATE_SIZE {
					mds_out_curr += BinaryField32b::new(MDS_FULL[i][j] as u32) * perm_in_data[j][z];
				}
				round_0_input_32b[i][z] = mds_out_curr;
			}
		}
	}

	let full_0_out = (0..F_ROUNDS / 2).try_fold(round_0_input, |state, round_i| {
		full_round(builder, log_size, round_i, state, RC)
	})?;

	let partial_out = (F_ROUNDS / 2..(F_ROUNDS / 2 + P_ROUNDS))
		.try_fold(full_0_out, |state, round_i| {
			partial_round(builder, log_size, round_i, state, RC)
		})?;

	let perm_out = (F_ROUNDS / 2 + P_ROUNDS..N_ROUNDS)
		.try_fold(partial_out, |state, round_i| {
			full_round(builder, log_size, round_i, state, RC)
		})?;

	#[cfg(debug_assertions)]
	if let Some(witness) = builder.witness() {
		let p_in_data: [_; STATE_SIZE] =
			array_util::try_from_fn(|i| witness.get::<B32>(p_in[i])).unwrap();
		let p_in_32b: [_; STATE_SIZE] = p_in_data.map(|elem| elem.as_slice::<B32>());
		let p_out_data: [_; STATE_SIZE] =
			array_util::try_from_fn(|i| witness.get::<B32>(perm_out[i])).unwrap();
		let p_out_32b: [_; STATE_SIZE] = p_out_data.map(|elem| elem.as_slice::<B32>());
		for z in 0..1 << log_size {
			let expected_out: [B32; STATE_SIZE] = array::from_fn(|s| p_out_32b[s][z]);
			let mut state_in: [BinaryField32b; STATE_SIZE] =
				std::array::from_fn(|i| p_in_32b[i][z]);
			plain_permutation(&mut state_in, N_ROUNDS);
			assert_eq!(state_in, expected_out);
		}
	}
	Ok(perm_out)
}

#[rustfmt::skip]
const RC: [[u32; N_ROUNDS]; STATE_SIZE] = [
[0x85efb674,0x25c24b1a,0xf92e9446,0x21d4b314,0x29d4059e,0x5851c0d7,0x7bd5625b,0x50173d9c,0x56d99b78,0xcbf0644f,0xa8f8e2f6,0x5627d46c,0xa0890459,0x32d06935,0x5e0f419f,0x360120ef,0xdb8a6148,0xfc5381a2,0xf67eeb8c,0xc18d4ca6,0x269c7f20,0x11208ead,0x4e8008fc],
[0x4480060e,0x0cfe844c,0xf5211ab4,0xf3978ecd,0xd61e4270,0x652ba7d9,0x00a6cd49,0xbfc303d3,0x53c7a98d,0x6a9f818f,0x6931a959,0x6d9dcae4,0x6c85d8c3,0x55b0404b,0xf434099e,0x8a247e30,0x59f117fa,0xbff91429,0xb1e683ce,0xbad26dd3,0x49bee901,0x9c7cb6f3,0x920b87bb],
[0x4cd42fc2,0x18e5d5b8,0x2b24a965,0x50f06f7d,0xa80adeb7,0x062213d1,0x047914c8,0xe79cb049,0xba027147,0x86705bb2,0xdb43b616,0xa2db8f90,0x586a82d9,0x3a1b1e92,0x9fd00e48,0xf351ad77,0x2e74b494,0x1017841a,0x60942898,0xf0d43f70,0xf1bbc04a,0x45428dc2,0x33a2bc20],
[0x112257ba,0x106df769,0x22eaedd1,0x6cbb8852,0x1d96a87b,0x8f37d0f8,0x1a132b47,0x7886d817,0xa449b164,0x1358e773,0x4ef69ffc,0xc3cebb26,0x3391bd08,0xbc9e7079,0xc3bb221c,0x5e41a2f6,0x593d9e65,0xed1931c1,0x9463ba1a,0x5b50dbb8,0xa5099df5,0x65dd5b14,0xcb5d132b],
[0xe5269bd5,0xa2cb67b2,0xa86069fa,0x9b0510aa,0x16c7193e,0x9a629e8d,0xf83f78ab,0xadca21e1,0xaca4de3d,0x227c15fa,0xce530ddd,0x5a4cfe35,0x0f8e3706,0x6352180e,0x9c882dfa,0xc34fe7d3,0x0c7e1556,0x645cbb58,0xe0f615c7,0x228f2fb6,0xe34c25c3,0x17ceef3f,0xcee74a54],
[0xbbb074b0,0x2e7c1260,0x1f53c654,0x9baabb6f,0x711dc83e,0xea837ac2,0x652e63dd,0x2de44274,0xc282c5bf,0x6ac08a8b,0xb9205180,0x785fc09c,0x4f056a8c,0x713b896e,0xf84d0694,0xeed5c082,0x24ea3c6b,0xf66e1e43,0x94a42d3f,0x5b295750,0x58ee9a1d,0x82e66855,0xef78193d],
[0x9e9c2d11,0xa5a127e9,0x3d0e5391,0x75c964ea,0x6d780333,0xec0f243f,0x8a38ed6d,0xa76d30e3,0x1a655ef2,0xf980fa18,0x49795fb8,0xca334614,0x3dc52dca,0x73158a96,0x320fc140,0xde5e6572,0xc0ea8d81,0x7d7378cb,0x6f70bab1,0x7e2b530d,0xede2c73a,0xad993e8f,0x729b4aa6],
[0x7f6aaf32,0x3f856aac,0xc2f153e4,0xe267c055,0x132f5187,0xac58c230,0x868e7f4e,0x069a1a85,0x262c519f,0x1028a8e0,0x8c5a0c98,0xe40cee83,0x9f1e9575,0x573e9e78,0x314f2158,0xeac35ec2,0x9f7ba309,0x074649bc,0x98caef5e,0x5c4dbaa2,0x6becfe5a,0x31ec18ac,0xb241a131],
[0x41057e63,0xdf13952c,0xb47f76c5,0x4b438ba8,0xe162d660,0x8ab03f4d,0x69f44098,0xf586aad9,0xff47ec1a,0x55b6466d,0x6416c4eb,0xe3931196,0xc19ed30d,0xb89db3dd,0x11e2cead,0x8e50e15b,0xd47f3aad,0xd4fee405,0x31a92224,0x15141b24,0x6031af2e,0x3bef048f,0x371c2fbf],
[0x020e5dab,0x6330836f,0x26b1b2de,0xe9c32231,0x788d39f1,0x0fa8dee4,0x4f5413e6,0x5bf0e4bd,0x76d500cc,0x4056e3f7,0x9f1aa362,0x475d3ba6,0x3701ebdf,0x5e912110,0x9811f1de,0x2db819c1,0x00a02809,0x2930bbdf,0x5a406543,0x5e80750b,0x6bb5a648,0xa864d49f,0x85607d2e],
[0x87f0fddd,0xb6547914,0x18fa2cbf,0x82c62377,0x1b21519a,0x364ade1e,0xa50b85cf,0x2399b3ff,0x01e83c44,0xd790555a,0x3c0dfbe2,0x44ef361c,0x643fed9e,0x47afe3bb,0xf38c7e0b,0xced5ba0c,0x1d5c13de,0x931f7e13,0xc4f30404,0x635d9bd9,0xf9afa8f9,0x5cdad754,0xabf15995],
[0x28e923ca,0xffc89497,0xae505d1f,0x19a89b6d,0x6ec31819,0xd6823afd,0x6c744457,0xe19d59b9,0x9e60ec0b,0xba9d16d6,0x02db975e,0x95070fe5,0xa63e3600,0x846590e5,0x7b81eabe,0xe00ca8a6,0x7b0ba784,0xbbeba2df,0x287b9815,0xf0adb48c,0x4f287436,0x404b092b,0xbd66c0b5],
[0x6370ba5e,0x71d6e841,0xb289f727,0x21ecd446,0x7693860d,0xab53fa11,0x2579673a,0x1c7135c2,0x17a86eb2,0xa38d29b5,0xbd10fded,0xac891235,0x7c9d8a78,0x4d2b8793,0xb11e6c71,0x33bdb6cb,0x0d2f4fb4,0x21e4ee08,0xe2359747,0xf7427068,0x9197e797,0x7cd9ec7d,0x18bff9d8],
[0x858bf3fc,0x077683e9,0xb0ae7901,0x3465da2c,0xb9198299,0x815ab8d6,0xc727ecdb,0xd15c647d,0x4c2dd636,0x1eac2280,0xd524fc9f,0x028b7aa7,0x60e01aa6,0x1c5a2ad0,0x3c2d72eb,0xfce809e3,0xa7ac1dcf,0x30da94bb,0x7b96c634,0x24ab9bbc,0x48b07c8f,0x8605f57b,0xbbe0f8b5],
[0x7be52aff,0x63e516a8,0x635fedc6,0xf45c2d0c,0x2f28d5f8,0xca5e2e39,0x89e96ed7,0x5a438390,0xb38d2cf5,0x269b9290,0xf9b457ed,0xe1d7e8cb,0x85317d06,0x4d6f452a,0x176e1106,0xec0e03a4,0x4260ef3d,0xda568fb5,0xe962b8de,0x80c0cad6,0xcd486eff,0xcf13b4f1,0x2b635d62],
[0x81f605b6,0x46e67dea,0x36335eec,0x057be984,0x4e083c2b,0x41298657,0xaef3c2f3,0xb1649635,0xb831e2b0,0xaa274e21,0x0efca5eb,0x21a203a4,0x8a09bddb,0x4d278dd8,0xfa1c4fd6,0xee1f5f09,0x637672f9,0x82ddf00c,0xe7991f90,0x778d349d,0x96c04047,0x5e1b58f5,0xa1ce635a]];

#[rustfmt::skip]
 const MDS_FULL: [[u32; STATE_SIZE]; STATE_SIZE] =[
[0x80fffc00, 0x8b9f6584, 0x099ea10f, 0x02fe388b, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e],
[0x89615d0f, 0x8201c48b, 0x099ea10f, 0x099ea10f, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001],
[0x099ea10f, 0x02fe388b, 0x80fffc00, 0x8b9f6584, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a],
[0x099ea10f, 0x099ea10f, 0x89615d0f, 0x8201c48b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b],
[0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x80fffc00, 0x8b9f6584, 0x099ea10f, 0x02fe388b, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e],
[0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x89615d0f, 0x8201c48b, 0x099ea10f, 0x099ea10f, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001],
[0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x099ea10f, 0x02fe388b, 0x80fffc00, 0x8b9f6584, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a],
[0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x099ea10f, 0x099ea10f, 0x89615d0f, 0x8201c48b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b],
[0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x80fffc00, 0x8b9f6584, 0x099ea10f, 0x02fe388b, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e],
[0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x89615d0f, 0x8201c48b, 0x099ea10f, 0x099ea10f, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001],
[0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x099ea10f, 0x02fe388b, 0x80fffc00, 0x8b9f6584, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a],
[0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x099ea10f, 0x099ea10f, 0x89615d0f, 0x8201c48b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b],
[0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x80fffc00, 0x8b9f6584, 0x099ea10f, 0x02fe388b],
[0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x89615d0f, 0x8201c48b, 0x099ea10f, 0x099ea10f],
[0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x00000001, 0x099ea10e, 0x0b609985, 0x02fe388a, 0x099ea10f, 0x02fe388b, 0x80fffc00, 0x8b9f6584],
[0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x00000001, 0x00000001, 0x0b609984, 0x02fe388b, 0x099ea10f, 0x099ea10f, 0x89615d0f, 0x8201c48b]];

#[rustfmt::skip]
const MDS_PARTIAL: [[u32; STATE_SIZE]; STATE_SIZE] = [
[0x8c0bb651, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x89615d0f, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x6b2db9bb, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x67eb1cee, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x8905ce18, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0xbc09f4e9, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x8c0bb650, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0xba501121, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x0b609985, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x16c54bd1, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x8639d1f2, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x205759fb, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x0b609984, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0xde3fbed6, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x099ea10e]
];
fn x7_constraint_expr<F: TowerField>() -> Result<ArithCircuit<F>> {
	let x = ArithExpr::Var(0);
	let x7 = ArithExpr::Var(1);

	let input_pow2 = x.clone().pow(2);
	let input_pow4 = input_pow2.clone().pow(2);
	let input_pow6 = input_pow2 * input_pow4;
	let input_pow7 = input_pow6 * x.clone();

	Ok((x7.clone() - input_pow7).into())
}

fn full_round(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	round_i: usize,
	state_in: [OracleId; STATE_SIZE],
	round_constants: [[u32; N_ROUNDS]; STATE_SIZE],
) -> Result<[OracleId; STATE_SIZE]>
where {
	builder.push_namespace(format!("full round[{round_i}]"));
	// let state_size = state_in.len();
	let full_round_consts: [OracleId; STATE_SIZE] = array::from_fn(|i| {
		builder
			.add_transparent(
				format!("full_round_const{}", i),
				Constant::new(log_size, BinaryField32b::new(round_constants[i][round_i])),
			)
			.unwrap()
	});

	let add_rc: [OracleId; STATE_SIZE] = array::from_fn(|row| {
		builder
			.add_linear_combination(
				format!("add_rc_full_{}", row),
				log_size,
				[
					(state_in[row], Field::ONE),
					(full_round_consts[row], Field::ONE),
				],
			)
			.unwrap()
	});

	let s_box_out = builder.add_committed_multiple::<STATE_SIZE>(
		"sbox_out_full",
		log_size,
		BinaryField32b::TOWER_LEVEL,
	);

	let mds_out: [OracleId; STATE_SIZE] = array::from_fn(|row| {
		builder
			.add_linear_combination(
				format!("mds_out_full_{}", row),
				log_size,
				MDS_FULL[row]
					.iter()
					.enumerate()
					.map(|(i, &elem)| (s_box_out[i], F::from(BinaryField32b::new(elem as u32)))),
			)
			.unwrap()
	});

	builder.pop_namespace();

	// Witness gen
	if let Some(witness) = builder.witness() {
		let state_in: [_; STATE_SIZE] =
			array_util::try_from_fn(|i| witness.get::<B32>(state_in[i]))?;
		let state_in_u32: [_; STATE_SIZE] = state_in.map(|elem| elem.as_slice::<B32>());

		let mut full_round_consts = full_round_consts.map(|id| witness.new_column::<B32>(id));
		let full_round_consts_32b = full_round_consts
			.each_mut()
			.map(|elem| elem.as_mut_slice::<B32>());

		let mut add_rc = add_rc.map(|id| witness.new_column::<B32>(id));
		let add_rc_32b: [&mut [BinaryField32b]; STATE_SIZE] =
			add_rc.each_mut().map(|elem| elem.as_mut_slice());

		let mut s_box_out = s_box_out.map(|id| witness.new_column::<B32>(id));
		let s_box_out_32b: [&mut [BinaryField32b]; STATE_SIZE] =
			s_box_out.each_mut().map(|elem| elem.as_mut_slice());

		let mut mds_out = mds_out.map(|id| witness.new_column::<B32>(id));
		let mds_out_32b: [&mut [BinaryField32b]; STATE_SIZE] =
			mds_out.each_mut().map(|elem| elem.as_mut_slice());

		// Fill in constants
		for i in 0..STATE_SIZE {
			full_round_consts_32b[i]
				.iter_mut()
				.for_each(|rc| *rc = BinaryField32b::new(round_constants[i][round_i]));
		}

		for z in 0..1 << log_size {
			for i in 0..STATE_SIZE {
				add_rc_32b[i][z] = state_in_u32[i][z] + full_round_consts_32b[i][z];
			}

			for i in 0..STATE_SIZE {
				s_box_out_32b[i][z] = add_rc_32b[i][z].pow(7);
			}

			for i in 0..STATE_SIZE {
				let mut mds_out_curr = B32::ZERO;
				for j in 0..STATE_SIZE {
					mds_out_curr +=
						BinaryField32b::new(MDS_FULL[i][j] as u32) * s_box_out_32b[j][z];
				}
				mds_out_32b[i][z] = mds_out_curr;
			}
		}
	}

	// zero check constraints
	for s in 0..STATE_SIZE {
		builder.assert_zero(format!("x7_{s}"), [add_rc[s], s_box_out[s]], x7_constraint_expr()?);
	}

	Ok(mds_out)
}

fn partial_round(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	round_i: usize,
	state_in: [OracleId; STATE_SIZE],
	round_constants: [[u32; N_ROUNDS]; STATE_SIZE],
) -> Result<[OracleId; STATE_SIZE]>
where {
	builder.push_namespace(format!("round[{round_i}]"));

	let partial_round_const: OracleId = builder
		.add_transparent(
			format!("partial_round_const{}", 0),
			Constant::new(log_size, BinaryField32b::new(round_constants[0][round_i])),
		)
		.unwrap();

	let add_rc: OracleId = builder
		.add_linear_combination(
			format!("add_rc_partial_0"),
			log_size,
			[(state_in[0], Field::ONE), (partial_round_const, Field::ONE)],
		)
		.unwrap();

	let s_box_out: OracleId =
		builder.add_committed("sbox_out_partial", log_size, BinaryField32b::TOWER_LEVEL);

	let mds_out: [OracleId; STATE_SIZE] = array::from_fn(|row| {
		builder
			.add_linear_combination(
				format!("mds_out_partial_{}", row),
				log_size,
				MDS_PARTIAL[row].iter().enumerate().map(|(i, &elem)| {
					if i == 0 {
						(s_box_out, F::from(BinaryField32b::new(elem as u32)))
					} else {
						(state_in[i], F::from(BinaryField32b::new(elem as u32)))
					}
				}),
			)
			.unwrap()
	});

	builder.pop_namespace();

	// let mds_trans = Vision32MDSTransform::default();

	type B32 = BinaryField32b;

	// Witness gen
	if let Some(witness) = builder.witness() {
		let state_in: [_; STATE_SIZE] =
			array_util::try_from_fn(|i| witness.get::<B32>(state_in[i]))?;
		let state_in_u32: [_; STATE_SIZE] = state_in.map(|elem| elem.as_slice::<B32>());
		let mut partial_round_const = witness.new_column::<B32>(partial_round_const);
		let partial_round_const_32b = partial_round_const.as_mut_slice();

		let mut add_rc = witness.new_column::<B32>(add_rc);
		let add_rc_32b: &mut [BinaryField32b] = add_rc.as_mut_slice();

		let mut s_box_out = witness.new_column::<B32>(s_box_out);
		let s_box_out_32b: &mut [BinaryField32b] = s_box_out.as_mut_slice();

		let mut mds_out = mds_out.map(|id| witness.new_column::<B32>(id));
		let mds_out_32b: [&mut [BinaryField32b]; STATE_SIZE] =
			mds_out.each_mut().map(|elem| elem.as_mut_slice());

		// partial_round_consts_32b[round_i] = BinaryField32b::new(round_constants[0][round_i]);

		// Fill in constants
		partial_round_const_32b
			.iter_mut()
			.for_each(|rc| *rc = BinaryField32b::new(round_constants[0][round_i]));

		for z in 0..1 << log_size {
			// Fill in constants

			add_rc_32b[z] = state_in_u32[0][z] + partial_round_const_32b[z];

			s_box_out_32b[z] = add_rc_32b[z].pow(7);

			let mut input_mds = [B32::ZERO; STATE_SIZE];
			input_mds[0] = s_box_out_32b[z];

			for i in 1..STATE_SIZE {
				input_mds[i] = state_in_u32[i][z];
			}

			for i in 0..STATE_SIZE {
				let mut mds_out_curr = B32::ZERO;

				for j in 0..STATE_SIZE {
					mds_out_curr += BinaryField32b::new(MDS_PARTIAL[i][j] as u32) * input_mds[j];
				}
				mds_out_32b[i][z] = mds_out_curr;
			}
		}
	}

	// zero check constraints
	builder.assert_zero(format!("x7_0_partial"), [add_rc, s_box_out], x7_constraint_expr()?);

	Ok(mds_out)
}

#[cfg(test)]
mod tests {

	use binius_core::oracle::OracleId;
	use binius_field::{BinaryField8b, BinaryField32b, Field};
	use binius_math::evaluate_univariate;

	use super::permutation;
	use crate::{
		builder::test_utils::test_circuit,
		hades::poseidon2b_x7_32_512::{N_ROUNDS, STATE_SIZE, plain_permutation},
		unconstrained::unconstrained,
	};
	#[test]
	fn test_poseidon2b() {
		test_circuit(|builder| {
			let log_size = 8;
			let state_in: [OracleId; STATE_SIZE] = std::array::from_fn(|i| {
				unconstrained::<BinaryField32b>(builder, format!("p_in[{i}]"), log_size).unwrap()
			});
			let _state_out = permutation(builder, log_size, state_in).unwrap();
			Ok(vec![])
		})
		.unwrap();
	}
}
