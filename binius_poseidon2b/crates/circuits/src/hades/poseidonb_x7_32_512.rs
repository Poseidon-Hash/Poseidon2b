// Copyright 2024-2025 Irreducible Inc.

//! Example of a Binius SNARK that proves execution of Poseidonb permutations.

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
[0x3ab6, 0x1926, 0x3710, 0x4a03, 0x5758, 0x2ac5, 0x2f28, 0x6dd9, 0x3aaa, 0x4eb7, 0x5807, 0x6d75, 0x2ebd, 0x2dae, 0x430d, 0x5e71, 0x5814, 0x4c7c, 0x6389, 0x7c22, 0x68f6, 0x2e32, 0x671a, ],
[0x439c, 0x5668, 0x3306, 0x142c, 0x21b2, 0x4e5e, 0x7452, 0x46c2, 0x542e, 0x42c4, 0x146b, 0x1971, 0x5b20, 0x5475, 0x1e8b, 0xce7, 0x2ec5, 0x4d21, 0x6717, 0x4ef6, 0x34b9, 0x1b01, 0x5d45, ],
[0x17ff, 0x4c3c, 0x1076, 0x2a3b, 0x1f91, 0x7335, 0x618b, 0x239b, 0x43b8, 0x4314, 0x7e8c, 0x2929, 0x1949, 0x7d2c, 0x4b88, 0x22d4, 0x1323, 0x41c3, 0x5c34, 0x6795, 0x16af, 0x6ebf, 0x3a05, ],
[0x1ed0, 0x10f5, 0x20d1, 0x2146, 0x677d, 0x2ee0, 0x41ce, 0x6145, 0x3a40, 0x5da, 0x69bb, 0x28d8, 0x5543, 0x33c4, 0x743, 0x5071, 0x7d5f, 0x4a44, 0x68f, 0x3e2, 0x41ba, 0x2b4, 0x2623, ],
[0x7dce, 0x7e33, 0x609, 0xeab, 0x5fb2, 0x3ea0, 0x1fda, 0x5e11, 0x1097, 0x5192, 0x289b, 0x5a8b, 0x2986, 0x1ba2, 0x6f63, 0x2e9d, 0x2285, 0x3f9c, 0x630, 0x67e8, 0x5580, 0x43a0, 0x17dd, ],
[0x7b5a, 0x7a8d, 0x57c4, 0x623, 0x4e29, 0x47e7, 0x9e1, 0x3ed2, 0x3ade, 0x1aaf, 0x1b84, 0x6b94, 0x5962, 0x5fc2, 0x55e0, 0x1ae6, 0x96d, 0x7826, 0x6d7e, 0x6375, 0x5904, 0x1d2b, 0x1d1, ],
[0x62d9, 0x223a, 0x552d, 0x56a7, 0x2eb6, 0x22de, 0x574a, 0x1831, 0x7a1f, 0x7b80, 0x58a9, 0x2c4, 0x50e4, 0x6824, 0x2733, 0x256e, 0x5f12, 0x284f, 0x421b, 0x176b, 0x15c6, 0x541d, 0x7341, ],
[0x3c27, 0x2456, 0x5b24, 0x4d41, 0x3c0f, 0x43d2, 0x5f7a, 0x391b, 0x318b, 0x2c0e, 0x7336, 0x17f2, 0x3cf1, 0x5fc8, 0x3b12, 0x51a1, 0x1a31, 0x6e32, 0x822, 0x195f, 0x4dac, 0x2cc7, 0x6f91, ],
[0x62f0, 0x166, 0x2c4a, 0x1293, 0x755c, 0x1c29, 0x72ce, 0x5671, 0x42b6, 0x1b65, 0x28a7, 0x502, 0x1656, 0x7176, 0x55dc, 0x624b, 0x187d, 0x79d, 0x7f22, 0x24f4, 0x23d7, 0x606f, 0x39dc, ],
[0x7015, 0x1c02, 0x5c0b, 0x22c8, 0x7a0c, 0x1da9, 0x1a51, 0xddc, 0x653d, 0x5336, 0x1fe4, 0x47b, 0x49cd, 0x60e3, 0x513d, 0xea9, 0x314, 0x3d70, 0x34a1, 0x578b, 0x3cec, 0x2101, 0x5537, ],
[0x3e83, 0x5b57, 0x5b3e, 0x56d7, 0x18c3, 0x2301, 0x5372, 0x2b9f, 0x2bdc, 0x4777, 0x5959, 0x1525, 0x1cb6, 0x2430, 0x37fb, 0x7fb8, 0x5095, 0x569d, 0x6267, 0x448d, 0xa68, 0x75c9, 0x1b44, ],
[0x79a0, 0x109c, 0x299b, 0x106a, 0x4f23, 0x3b0b, 0x246a, 0x167, 0x6759, 0x6340, 0x890, 0x5a1e, 0x4dba, 0x4456, 0x331, 0x6831, 0x462d, 0x2937, 0x4b9c, 0x73f, 0x7f1, 0x527e, 0x79d8, ],
[0x14e5, 0x3733, 0x1a5, 0x3587, 0x3599, 0x15f5, 0x3448, 0x790f, 0x1ed3, 0x4743, 0x5502, 0x3b7b, 0x322f, 0x1a1f, 0x2de4, 0x6e05, 0x652d, 0x6ea0, 0x4266, 0x7890, 0x46a1, 0x3789, 0x7004, ],
[0x683f, 0x5868, 0x7275, 0x3337, 0x2204, 0x4163, 0x6c9b, 0x1c44, 0x1c70, 0x574a, 0x16d6, 0x2669, 0x3b26, 0x7af4, 0x6fb1, 0x75ca, 0x6dfe, 0x3582, 0x1a22, 0xffe, 0x1d3a, 0x333c, 0x102c, ],
[0x7bec, 0x54ce, 0x1a22, 0x2fe9, 0x21b6, 0x4b25, 0x1e51, 0x2b56, 0x2ef2, 0x59d1, 0x31b9, 0x40f8, 0x6d3c, 0x22e0, 0xb06, 0x688a, 0x5775, 0x2603, 0x681, 0x7fa8, 0x4716, 0x423b, 0x4c3, ],
[0x5430, 0x44b9, 0x68cb, 0x72fe, 0x5449, 0x1559, 0x1c1b, 0x47a3, 0x7696, 0xd25, 0x73fc, 0x66a6, 0x1186, 0x10c6, 0x44aa, 0x1544, 0x4b92, 0x2b4e, 0x42fa, 0x56d9, 0x2b1b, 0x59c8, 0x1211, ],
];

pub const MDS_FULL: [[u32; STATE_SIZE]; STATE_SIZE] = [
	[
		0x1c0ec89f, 0xbb521539, 0xb5403ba3, 0xf6c149fb, 0xfbdd011e, 0x76d63ece, 0x54598501,
		0x70ddaa24, 0x0ffddca5, 0xa6ab5103, 0xdea1a041, 0x81c71fee, 0xff27eea1, 0xa927112a,
		0xd70bd4f7, 0xa6066f23,
	],
	[
		0xd2cac6e1, 0x3e5a241f, 0x9778daa6, 0x8c409f08, 0xe2db5e29, 0xe8487c20, 0xcdc43058,
		0xb80796ea, 0xa52dcd70, 0x8f2a6ed7, 0xb7a0930f, 0x6f6df2d1, 0x6de39116, 0xc29f7a7f,
		0x9989844d, 0x05c359db,
	],
	[
		0x5f3d5e12, 0xc46f4c0c, 0x9450b53a, 0xe358e978, 0xda8a618d, 0x3df4766a, 0x292692e8,
		0xb7d98b8a, 0x19eeb6bd, 0x9849f11c, 0x5a5050c9, 0x8ba18b71, 0xb2417db3, 0x06c93b38,
		0x7e6d789c, 0x6081aea0,
	],
	[
		0x9811bb76, 0x886d9aa6, 0x143cbd46, 0xdbdda97d, 0x20599039, 0x986bef84, 0xe3ca227d,
		0xee085f49, 0xbf65d109, 0xb85fa5b8, 0x2301c876, 0xd13cbc47, 0xdbc00c55, 0xb3e9f88b,
		0x7ce89717, 0x25539043,
	],
	[
		0xeb504a55, 0x5b851302, 0x78f4d635, 0x539f617d, 0xd502f64e, 0x9abe156a, 0xd5c545e7,
		0xb6e52c81, 0x175f26cd, 0x5937fc9e, 0x0ca8bc1a, 0x6f1eac28, 0x0e075203, 0x38c141aa,
		0x8c9cb2a2, 0x6adaf365,
	],
	[
		0x91c012a4, 0xf7adba4e, 0x6a244d8e, 0xb745ba55, 0x49f05564, 0xb0991556, 0x8c93c7e2,
		0xbd6e2953, 0x72093b0c, 0x4ff9bfeb, 0xd9734839, 0x8d664c57, 0x6c379082, 0xd6de3acc,
		0xc061951b, 0x623aa2b4,
	],
	[
		0x94916d7b, 0xd12212be, 0x1628e6ed, 0x9e9f8d85, 0x5552a161, 0xaf92b9ce, 0x7723a6bf,
		0xe5f4687a, 0xe3a2287a, 0xd1bfdf2c, 0xee878fe6, 0x4c6bb18d, 0x783583d0, 0xf03754b3,
		0x028b1a48, 0xe0327466,
	],
	[
		0x9773d882, 0x47c00b57, 0xc7137548, 0xf27efd12, 0x287f4ce9, 0x026d231b, 0xf70cc393,
		0x961b1a53, 0xc4e1839c, 0x891c2bba, 0x16f72c83, 0x5edeae89, 0x6adc2a1b, 0xc508ea3a,
		0x59f9103c, 0x74a112c0,
	],
	[
		0x6529f3e4, 0xfb8a4d7e, 0xf435f389, 0xed911562, 0x47d6bb7e, 0x5721dc13, 0x946c4bb8,
		0x736d56ce, 0x2bc50cf1, 0xc99e2f8c, 0x7beb636e, 0x118af390, 0xbebbfa56, 0x899defcc,
		0x190613da, 0x6892b523,
	],
	[
		0x4fbe3953, 0xa5007db1, 0xb4df0c22, 0x618dcd81, 0xf8655af6, 0xd0659dda, 0xbbcab8f5,
		0x0fae3ceb, 0x1af66d69, 0xce63c6bd, 0x8ade9859, 0x35806bb6, 0xa08fec5d, 0x40d2651e,
		0xd09b85df, 0x0ae463cf,
	],
	[
		0x62cb1c04, 0xb4f1def3, 0xfe36b22c, 0x763a06f3, 0x1cecfcac, 0x43a848d6, 0x79627530,
		0x346fa653, 0xb51764df, 0x9867ab2e, 0xf9f8eaec, 0xc73bb585, 0x312d3b6b, 0x1ac3c1a2,
		0x3e42d816, 0x3a505085,
	],
	[
		0x53417fde, 0x84d2b73f, 0x3cb9d7eb, 0xa60111b9, 0x033a604a, 0x23ce188b, 0x67144892,
		0x785a719e, 0x7ab0084b, 0x96b1c06d, 0x024bbabe, 0x2ea9e7ce, 0xacd75e56, 0x2122ad31,
		0x47c9aad2, 0x19a15a8a,
	],
	[
		0xdf77e7de, 0x478e2374, 0xe122e6e1, 0xa13311db, 0x07777550, 0x7e9b3410, 0x5cf20974,
		0x2cae6051, 0x4fae5a26, 0x60e8276c, 0x9b8b7a92, 0x1673ca99, 0x34074edf, 0x2ed92638,
		0x4fcc8787, 0x148dfdea,
	],
	[
		0x2a4049aa, 0x110d8898, 0x072e8287, 0x65ecc9f2, 0x979586bb, 0x5f9dfa51, 0xa406b3fe,
		0x4c057000, 0x46635bcb, 0x6c2c8142, 0x5651283d, 0xffe71a33, 0x143a3c12, 0xf96fbe5d,
		0x864fad92, 0xe485897a,
	],
	[
		0x1afe3f03, 0xad2d9b14, 0x5d9fa98c, 0x0494bed2, 0xbc1773e7, 0x0f28642d, 0xcce8234e,
		0xdec60c3a, 0x89125f8d, 0xa2efd8d8, 0xe69b6040, 0xa0fcfa42, 0x5fbfd496, 0x04937542,
		0x2ed4614b, 0xc4ae5204,
	],
	[
		0x945de862, 0x665dcd04, 0xa6b3d982, 0x3dd0b2c3, 0xdc113da2, 0xfcd439be, 0x8bb9f9b6,
		0x74425e33, 0xb265ae36, 0xd13dc7cd, 0x6dde32bd, 0xe764014d, 0xb7e7f8b9, 0xadfceb70,
		0x16ce52a7, 0xb48fc9bf,
	],
];
#[rustfmt::skip]
const MDS_PARTIAL: [[u32; STATE_SIZE]; STATE_SIZE] = [
	[0x400, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x8, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x100, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x800, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x4000, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x8000, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x401, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x10, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x5, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x40, 0x1, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x80, 0x1, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x2001, 0x1, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x4, 0x1, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x20, 0x1,],
	[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x3,],
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
	use binius_field::BinaryField32b;

	use super::permutation;
	use crate::{
		builder::test_utils::test_circuit, hades::poseidonb_x7_32_512::STATE_SIZE,
		unconstrained::unconstrained,
	};
	#[test]
	fn test_poseidonb() {
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
