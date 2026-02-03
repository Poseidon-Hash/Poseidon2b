// Copyright 2024-2025 Irreducible Inc.

//! Example of a Binius SNARK that proves execution of Poseidonb permutations.

use std::array;

use anyhow::Result;
use binius_core::{oracle::OracleId, transparent::constant::Constant};
use binius_field::{BinaryField64b, Field, PackedField, TowerField};
use binius_math::{ArithCircuit, ArithExpr};

use crate::builder::{ConstraintSystemBuilder, types::F};

type B64 = BinaryField64b;
const P_ROUNDS: usize = 29;
const F_ROUNDS: usize = 8;
const N_ROUNDS: usize = F_ROUNDS + P_ROUNDS;

const STATE_SIZE: usize = 12;

fn plain_permutation(state: &mut [B64; STATE_SIZE], n_rounds: usize) {
	// initial mds matrix mult
	let mds_input = state.clone();
	for i in 0..state.len() {
		// mds matrix mult
		let mut mds_out_curr = B64::ZERO;
		for j in 0..STATE_SIZE {
			mds_out_curr += B64::new(MDS_FULL[i][j] as u64) * mds_input[j];
		}
		state[i] = mds_out_curr;
	}
	//full and partial rounds
	for r in 0..n_rounds {
		if r < F_ROUNDS / 2 || r >= F_ROUNDS / 2 + P_ROUNDS {
			//  Full (external) rounds
			for i in 0..state.len() {
				//rc add
				state[i] = state[i] + B64::new(RC[i][r]);
			}
			for i in 0..state.len() {
				//sbox
				state[i] = state[i].pow(7);
			}
			let mds_input = state.clone();
			for i in 0..state.len() {
				// mds matrix mult
				let mut mds_out_curr = B64::ZERO;
				for j in 0..STATE_SIZE {
					mds_out_curr += B64::new(MDS_FULL[i][j] as u64) * mds_input[j];
				}
				state[i] = mds_out_curr;
			}

		} else {
			//  Partial (internal) rounds
			//rc add
			state[0] = state[0] + B64::new(RC[0][r]);
			//sbox
			state[0] = state[0].pow(7);
			// mds matrix mult
			let mds_input = state.clone();
			for i in 0..state.len() {
				// mds matrix mult
				let mut mds_out_curr = B64::ZERO;
				for j in 0..STATE_SIZE {
					mds_out_curr += B64::new(MDS_PARTIAL[i][j] as u64) * mds_input[j];
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
					.map(|(i, &elem)| (p_in[i], F::from(B64::from(elem as u64)))),
			)
			.unwrap()
	});

	if let Some(witness) = builder.witness() {
		let perm_in_data_owned: [_; STATE_SIZE] =
			array_util::try_from_fn(|i| witness.get::<B64>(p_in[i]))?;
		let perm_in_data: [_; STATE_SIZE] = perm_in_data_owned.map(|elem| elem.as_slice::<B64>());
		let mut round_0_input_data: [_; STATE_SIZE] =
			round_0_input.map(|id| witness.new_column::<B64>(id));
		let round_0_input_64b = round_0_input_data
			.each_mut()
			.map(|elem| elem.as_mut_slice::<B64>());

		for z in 0..1 << log_size {
			for i in 0..STATE_SIZE {
				let mut mds_out_curr = B64::ZERO;
				for j in 0..STATE_SIZE {
					mds_out_curr += B64::new(MDS_FULL[i][j] as u64) * perm_in_data[j][z];
				}
				round_0_input_64b[i][z] = mds_out_curr;
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
			array_util::try_from_fn(|i| witness.get::<B64>(p_in[i])).unwrap();
		let p_in_64b: [_; STATE_SIZE] = p_in_data.map(|elem| elem.as_slice::<B64>());
		let p_out_data: [_; STATE_SIZE] =
			array_util::try_from_fn(|i| witness.get::<B64>(perm_out[i])).unwrap();
		let p_out_64b: [_; STATE_SIZE] = p_out_data.map(|elem| elem.as_slice::<B64>());
		for z in 0..1 << log_size {
			let expected_out: [B64; STATE_SIZE] = array::from_fn(|s| p_out_64b[s][z]);
			let mut state_in: [B64; STATE_SIZE] = std::array::from_fn(|i| p_in_64b[i][z]);
			plain_permutation(&mut state_in, N_ROUNDS);
			assert_eq!(state_in, expected_out);
		}
	}

	Ok(perm_out)
}

#[rustfmt::skip]
const RC: [[u64; N_ROUNDS]; STATE_SIZE] =[
[0x1b9, 0x3ec, 0x26e, 0x20f, 0x77a, 0x5c2, 0x127, 0x9c, 0x36d, 0x37, 0x72, 0x9d, 0x505, 0x622, 0x6eb, 0x3da, 0x332, 0x7a6, 0x6eb, 0x30a, 0xa3, 0x6d6, 0x2ae, 0x237, 0x41, 0x218, 0x650, 0x1f2, 0x92, 0x5d9, 0x778, 0x539, 0x30a, 0x33f, 0x445, 0x29, 0x17c, ],
[0x4ab, 0x724, 0x3e1, 0x4e0, 0x654, 0x5bd, 0x485, 0x7d3, 0x363, 0x7ba, 0x15a, 0x2d, 0xcd, 0x4e9, 0x6b7, 0x1f, 0x8f, 0x30b, 0x601, 0x7ea, 0x289, 0x6df, 0x697, 0x10b, 0x432, 0x153, 0x30e, 0x63, 0x47f, 0x662, 0x7a1, 0x94, 0x4f7, 0x2b3, 0x332, 0x189, 0xc0, ],
[0x7db, 0x538, 0x451, 0xcd, 0x11e, 0x74a, 0x150, 0x72b, 0x5df, 0x62e, 0xb9, 0x5b4, 0x587, 0x79e, 0x2d4, 0x132, 0x21f, 0x68, 0x83, 0x2c3, 0xf0, 0x706, 0x112, 0x6f1, 0x355, 0x3db, 0x2d4, 0x5f1, 0x7e, 0x19c, 0x35, 0x57a, 0x114, 0x65a, 0x472, 0x4c6, 0x75e, ],
[0x7af, 0x4f2, 0x403, 0x740, 0x77e, 0x4cd, 0x7bd, 0xd1, 0xae, 0x347, 0x6fe, 0x496, 0x769, 0x87, 0x678, 0x6cc, 0x6f, 0x116, 0x63e, 0x52, 0x289, 0x189, 0x6a8, 0x119, 0x91, 0x11c, 0x162, 0x3d2, 0xcd, 0x61f, 0x735, 0x18f, 0x38e, 0x3fd, 0x2d7, 0x511, 0x3e8, ],
[0x412, 0x58e, 0x73d, 0x159, 0x363, 0x21a, 0x1c0, 0x5, 0x2db, 0x480, 0x12e, 0x244, 0x146, 0x3fe, 0x588, 0x9d, 0x671, 0x64b, 0x4f7, 0x792, 0x479, 0x4fd, 0x6f, 0x76, 0x4fa, 0x4a0, 0x51d, 0x85, 0x78, 0x108, 0x2c9, 0x571, 0x138, 0x14a, 0x484, 0x91, 0x795, ],
[0x558, 0x69c, 0x7ab, 0x21f, 0x215, 0x6ce, 0x466, 0x1b3, 0x3d, 0x435, 0x681, 0x5a6, 0x4c, 0x36e, 0x61b, 0x55, 0x6b2, 0x660, 0x645, 0x1d9, 0x76a, 0x790, 0x269, 0x4a1, 0x562, 0x7f, 0x2ad, 0x2b1, 0x5f8, 0xc, 0x7c8, 0x288, 0x412, 0x7ce, 0x19a, 0x5ff, 0x7ca, ],
[0x315, 0x6df, 0x527, 0x299, 0x66a, 0x1b3, 0x3d7, 0x33c, 0x1fa, 0x2b4, 0x165, 0x3eb, 0x5c9, 0x1e1, 0x73, 0x6fe, 0x591, 0x3d8, 0x4aa, 0x65b, 0x446, 0x271, 0x4c9, 0x565, 0x532, 0x496, 0x79a, 0x2d2, 0x5f1, 0x45d, 0x7e6, 0x43a, 0x137, 0x2f, 0x34d, 0x328, 0x733, ],
[0x7bb, 0x6f7, 0x73d, 0x333, 0xac, 0x33, 0x6ff, 0x1c7, 0xe9, 0x51b, 0x579, 0x470, 0x785, 0x6e9, 0x26, 0x2ca, 0x5cb, 0x4c0, 0x446, 0xea, 0x579, 0x40f, 0x11, 0x241, 0x16f, 0x518, 0x1b8, 0x30b, 0x493, 0x21a, 0x1e7, 0x680, 0x3b1, 0xcd, 0x2fd, 0x1a3, 0x2d8, ],
[0x708, 0x759, 0x79d, 0x444, 0x75b, 0x487, 0x63c, 0x79a, 0x19a, 0x2f8, 0x8c, 0x26e, 0x2ac, 0x388, 0x610, 0xbf, 0x329, 0x318, 0x3af, 0x618, 0x5f0, 0x2b9, 0x66d, 0xd5, 0x1f0, 0x45a, 0x298, 0x60c, 0x2b, 0x6de, 0x123, 0x528, 0x6a3, 0x5e0, 0x412, 0x74, 0x4d4, ],
[0x35e, 0x2e, 0x529, 0x407, 0x453, 0x47, 0x2a0, 0x6c1, 0x87, 0x750, 0x306, 0x524, 0x1d, 0x4d1, 0xdf, 0x22d, 0x70a, 0x260, 0x4c8, 0x5ce, 0x40c, 0x361, 0x437, 0x268, 0x2e2, 0x665, 0x316, 0x6e4, 0x736, 0x28a, 0x5e, 0x1a2, 0x1a1, 0x111, 0x206, 0x41e, 0x17, ],
[0x5cc, 0x45f, 0x5b9, 0x3e3, 0x3a4, 0x7f9, 0x232, 0x1b9, 0x12a, 0x324, 0x15e, 0x40b, 0x7a1, 0x688, 0x105, 0x52f, 0x719, 0x11b, 0x40a, 0xf5, 0x5e1, 0x6be, 0x778, 0x417, 0x587, 0x495, 0xf4, 0x38, 0x71c, 0x688, 0x458, 0x3c7, 0x25b, 0x3cf, 0x7a0, 0x19d, 0x59f, ],
[0x5d7, 0x315, 0x358, 0x762, 0x690, 0x1cd, 0x431, 0x2b7, 0x58, 0x791, 0x7e4, 0x9, 0x32d, 0x574, 0x2a6, 0x620, 0x51a, 0x725, 0x155, 0x461, 0x72f, 0xf7, 0x4f1, 0x15c, 0x70, 0x15e, 0x1e2, 0x6d2, 0x525, 0x720, 0x25b, 0x2c6, 0x7dc, 0xa5, 0x4ad, 0x51b, 0x6f, ],];


pub const MDS_FULL: [[u64; STATE_SIZE]; STATE_SIZE] = [
[0x9402138fb0eb5088,0x4f29c9818e8f9279,0x25616c7719e075cf,0x1fe2f35212949507,0xe24f3a21077a1e1b,0x4916ca92e00a54fd,0x410e66aec44638b2,0x7f5e9a3d97b050c2,0x5a0cfd7c4a0ff8ee,0x23cb27382f1c82d1,0xec9be257c8adfe3d,0x9c8733ac5c2cbe5e],
[0xba780a786c503051,0x57f50bd0e5949fee,0xafe468b37884f179,0x927904d363390f8b,0xe8b7149c26c32ec1,0xe56cbd821a704266,0xdb95299e14c78f7b,0x87c84ee234f0291d,0xc4c7d526b45cfbb3,0xd1bf6681ff00c5b5,0x047dcf60211267d3,0x86ce4938d76deb52],
[0x5efafdeffa6bd2e6,0xc4c760505c39e797,0x53f2d98f25549226,0x91597ba35f86b5cf,0xb01e5e295b3c99e9,0x6c9c488d796f9db2,0x9f3a71087428c5d4,0xa91115f0937d9fb9,0xb939abe12c85327c,0x8e49c741141dfe3c,0x7248e390f4eb1a9e,0x4bc4ed5bcd8adfcd],
[0xa60e848730410d24,0xe0d1e4348c2ca6e9,0x8a1ace6a2f7f2562,0x172b75d92c6c703b,0x506b77f8f3fb6b2b,0x2b1dd95a445d4ff4,0x045e39715cdc8f1e,0xa999d668b54cdfbf,0x5d859a810d53d453,0xd5197bbcb118e93c,0xe6a49d426de99b3c,0x5d614fb0d9406053],
[0xbfb7e05a0e2af956,0x7c6031d1ecb71af4,0x5447f07fcdea4bf5,0xb381d564e913441e,0xde38c905fd41c91d,0xb72129a48abec3e5,0xa7d445b970e296f5,0x1ee89f929c8d6b03,0x868801faafe14bfd,0x94ea95f9bff99b34,0x05c426f496fb5da1,0x099ee0d1696d4313],
[0x8d72a2c996e96fcf,0xd28061a02e5e588c,0x6a5cb15b57b81487,0x1273a0d9d99c9fd3,0xce5da50975d0eb02,0x838a219c79ad48db,0x35d1a6cbad6fceb5,0x18b1a4340dcc4bdd,0xe24763d9714f29d4,0x52e7958bce9a96b1,0x39160b23beef549b,0xcb09837f84f46126],
[0xc24d4ebc37dec608,0xe642fb3689892cb1,0x9700e6eaade32cb8,0x21b22dd42aed892f,0x7c93cb3391f63ff1,0x7dafd9c5a0f43470,0xf8cbbb2920d77e13,0xca73621b62da6501,0xbf9482ff88bdc6ce,0x4fd978330c3d8a9a,0x46322fd1463c091c,0xe685beb36663fc1a],
[0x75540c19eb21aa22,0x7bb7c42a56edc1dc,0x2df57e2f54db4902,0xba02f25ace3a77c9,0x0b266aee23dea34a,0x89b09a2c55a492d4,0x207682a3cdc451b2,0xeeec6f01c6152de4,0xa025267306a93732,0x96083e7095f4d6b3,0xf90678a4e17d0732,0x1f723f280fd560c6],
[0x223da7a48022d9ed,0xb0cf311531cd63eb,0xf667df9aa117f29b,0x434d144f1e36f885,0x96736fa48cec25c5,0xc92d91c711df9717,0x18776f5cdf502718,0x16c6168b49a073ed,0x6ada5cf32c142238,0x8225f1d0c3be84c2,0xcb7556a2b05f5650,0x9c37bb9a420b12a7],
[0xb18cd68745f50261,0xeb0df151cd3e16c1,0x5fa8d7a9b684cdb2,0x08e9eb57a2f69c65,0xf9ccba5bd417c881,0x6725e67a5e6d310d,0xa4eb7f625be8ffc1,0x073255ca7f0ed0f9,0xb0e48233601df40f,0x2323bf519015b76e,0x30340ce2eefb6c09,0x2cf44c9e67b04adc],
[0xc9a57ba137719eb6,0x9f8f6864a2f39640,0x1f59777aebb62da3,0x07250cbd7af0d73c,0xc698b51ccab32ee6,0xaf64b8dbbb4afad7,0x7320b1afe576a04e,0x709357a00e3b086c,0x238c27c95f8a8a9e,0xbf8e08c1b5359ce4,0xfe69c1aeb9d74c03,0x92073e50913c355b],
[0x2765f82a9b361e0d,0x39f2dc75ff9ce725,0xc8d7d8596164c87d,0x06544b03e22800de,0x971e14e47eeaee79,0xb9ac9d41ef0054a1,0xd8541f763306ffc7,0x382282b5020a7323,0x0ed58cddebd60c52,0x33e654b922744e9f,0x66f02f905e84f5e3,0x457eb8f938e964b8],
];

#[rustfmt::skip]
const MDS_PARTIAL: [[u64; STATE_SIZE]; STATE_SIZE] = [
[0x3, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x8, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x80, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x2000, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x8000, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x8001, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x800, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x2, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x401, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1000, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x400,],
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
	round_constants: [[u64; N_ROUNDS]; STATE_SIZE],
) -> Result<[OracleId; STATE_SIZE]>
where {
	builder.push_namespace(format!("full round[{round_i}]"));
	let full_round_consts: [OracleId; STATE_SIZE] = array::from_fn(|i| {
		builder
			.add_transparent(
				format!("full_round_const{}", i),
				Constant::new(log_size, B64::new(round_constants[i][round_i])),
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

	let s_box_out =
		builder.add_committed_multiple::<STATE_SIZE>("sbox_out_full", log_size, B64::TOWER_LEVEL);

	let mds_out: [OracleId; STATE_SIZE] = array::from_fn(|row| {
		builder
			.add_linear_combination(
				format!("mds_out_full_{}", row),
				log_size,
				MDS_FULL[row]
					.iter()
					.enumerate()
					.map(|(i, &elem)| (s_box_out[i], F::from(B64::new(elem as u64)))),
			)
			.unwrap()
	});

	builder.pop_namespace();

	// Witness gen
	if let Some(witness) = builder.witness() {
		let state_in: [_; STATE_SIZE] =
			array_util::try_from_fn(|i| witness.get::<B64>(state_in[i]))?;
		let state_in_u64: [_; STATE_SIZE] = state_in.map(|elem| elem.as_slice::<B64>());

		let mut full_round_consts = full_round_consts.map(|id| witness.new_column::<B64>(id));
		let full_round_consts_64b = full_round_consts
			.each_mut()
			.map(|elem| elem.as_mut_slice::<B64>());

		let mut add_rc = add_rc.map(|id| witness.new_column::<B64>(id));
		let add_rc_64b: [&mut [B64]; STATE_SIZE] =
			add_rc.each_mut().map(|elem| elem.as_mut_slice());

		let mut s_box_out = s_box_out.map(|id| witness.new_column::<B64>(id));
		let s_box_out_64b: [&mut [B64]; STATE_SIZE] =
			s_box_out.each_mut().map(|elem| elem.as_mut_slice());

		let mut mds_out = mds_out.map(|id| witness.new_column::<B64>(id));
		let mds_out_64b: [&mut [B64]; STATE_SIZE] =
			mds_out.each_mut().map(|elem| elem.as_mut_slice());

		// Fill in constants
		for i in 0..STATE_SIZE {
			full_round_consts_64b[i]
				.iter_mut()
				.for_each(|rc| *rc = B64::new(round_constants[i][round_i]));
		}

		for z in 0..1 << log_size {
			for i in 0..STATE_SIZE {
				add_rc_64b[i][z] = state_in_u64[i][z] + full_round_consts_64b[i][z];
			}

			for i in 0..STATE_SIZE {
				s_box_out_64b[i][z] = add_rc_64b[i][z].pow(7);
			}

			for i in 0..STATE_SIZE {
				let mut mds_out_curr = B64::ZERO;
				for j in 0..STATE_SIZE {
					mds_out_curr += B64::new(MDS_FULL[i][j] as u64) * s_box_out_64b[j][z];
				}
				mds_out_64b[i][z] = mds_out_curr;
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
	round_constants: [[u64; N_ROUNDS]; STATE_SIZE],
) -> Result<[OracleId; STATE_SIZE]>
where {
	builder.push_namespace(format!("round[{round_i}]"));

	let partial_round_const: OracleId = builder
		.add_transparent(
			format!("partial_round_const{}", 0),
			Constant::new(log_size, B64::new(round_constants[0][round_i])),
		)
		.unwrap();

	let add_rc: OracleId = builder
		.add_linear_combination(
			format!("add_rc_partial_0"),
			log_size,
			[(state_in[0], Field::ONE), (partial_round_const, Field::ONE)],
		)
		.unwrap();

	let s_box_out: OracleId = builder.add_committed("sbox_out_partial", log_size, B64::TOWER_LEVEL);

	let mds_out: [OracleId; STATE_SIZE] = array::from_fn(|row| {
		builder
			.add_linear_combination(
				format!("mds_out_partial_{}", row),
				log_size,
				MDS_PARTIAL[row].iter().enumerate().map(|(i, &elem)| {
					if i == 0 {
						(s_box_out, F::from(B64::new(elem as u64)))
					} else {
						(state_in[i], F::from(B64::new(elem as u64)))
					}
				}),
			)
			.unwrap()
	});

	builder.pop_namespace();

	type B64 = BinaryField64b;

	// Witness gen
	if let Some(witness) = builder.witness() {
		let state_in: [_; STATE_SIZE] =
			array_util::try_from_fn(|i| witness.get::<B64>(state_in[i]))?;
		let state_in_u64: [_; STATE_SIZE] = state_in.map(|elem| elem.as_slice::<B64>());
		let mut partial_round_const = witness.new_column::<B64>(partial_round_const);
		let partial_round_const_64b = partial_round_const.as_mut_slice::<B64>();

		let mut add_rc = witness.new_column::<B64>(add_rc);
		let add_rc_64b: &mut [B64] = add_rc.as_mut_slice();

		let mut s_box_out = witness.new_column::<B64>(s_box_out);
		let s_box_out_64b: &mut [B64] = s_box_out.as_mut_slice();

		let mut mds_out = mds_out.map(|id| witness.new_column::<B64>(id));
		let mds_out_64b: [&mut [B64]; STATE_SIZE] =
			mds_out.each_mut().map(|elem| elem.as_mut_slice());

		// Fill in constants
		partial_round_const_64b
			.iter_mut()
			.for_each(|rc| *rc = B64::new(round_constants[0][round_i]));
		for z in 0..1 << log_size {
			add_rc_64b[z] = state_in_u64[0][z] + partial_round_const_64b[z];

			s_box_out_64b[z] = add_rc_64b[z].pow(7);

			let mut input_mds = [B64::ZERO; STATE_SIZE];
			input_mds[0] = s_box_out_64b[z];

			for i in 1..STATE_SIZE {
				input_mds[i] = state_in_u64[i][z];
			}

			for i in 0..STATE_SIZE {
				let mut mds_out_curr = B64::ZERO;

				for j in 0..STATE_SIZE {
					mds_out_curr += B64::new(MDS_PARTIAL[i][j] as u64) * input_mds[j];
				}
				mds_out_64b[i][z] = mds_out_curr;
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
	use binius_field::BinaryField64b;

	use super::permutation;
	use crate::{
		builder::test_utils::test_circuit,
		hades::poseidonb_x7_64_768::STATE_SIZE,
		unconstrained::unconstrained,
	};
	#[test]
	fn test_poseidonb() {
		test_circuit(|builder| {
			let log_size = 8;
			let state_in: [OracleId; STATE_SIZE] = std::array::from_fn(|i| {
				unconstrained::<BinaryField64b>(builder, format!("p_in[{i}]"), log_size).unwrap()
			});
			let _state_out = permutation(builder, log_size, state_in).unwrap();
			Ok(vec![])
		})
		.unwrap();
	}
}