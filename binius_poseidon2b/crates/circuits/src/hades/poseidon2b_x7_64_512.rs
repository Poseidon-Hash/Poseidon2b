// Copyright 2024-2025 Irreducible Inc.
//! Example of a Binius SNARK that proves execution of Poseidon2b permutations.

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

const STATE_SIZE: usize = 8;

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
				state[i] =
					state[i] * state[i] * state[i] * state[i] * state[i] * state[i] * state[i];
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
const RC: [[u64; N_ROUNDS]; STATE_SIZE] = [
[0x8350993c,0x09f46234,0x450fc2a8,0xaba3b165,0xaf6dcea1,0x70344eab,0xdd1aa62b,0xc8956637,0x3a5bf88d,0xa11bb67b,0x0925dafb,0xac0bbee5,0x170fd883,0x751750d3,0x5e53deb4,0xcaf72b54,0xb6abd986,0x79896afe,0x5c92d96d,0x8350993c,0x09f46234,0x450fc2a8,0xaba3b165,0xaf6dcea1,0x70344eab,0xdd1aa62b,0xc8956637,0x3a5bf88d,0xa11bb67b,0x0925dafb,0xac0bbee5,0x170fd883,0x751750d3,0x5e53deb4,0xcaf72b54,0xb6abd986,0x79896afe,],
[0x12d38a1d,0x879f4bfe,0xe07d617d,0x18a49513,0x8294e0d7,0xa5515736,0x89a13175,0xff59d9ad,0x51cf6b4f,0x78fd57b9,0x6576a7eb,0xfb791ebc,0xf8435d45,0x17d69902,0xabcbff3f,0x89aea264,0x91e6f391,0x286bd78c,0xa88e1e29,0x12d38a1d,0x879f4bfe,0xe07d617d,0x18a49513,0x8294e0d7,0xa5515736,0x89a13175,0xff59d9ad,0x51cf6b4f,0x78fd57b9,0x6576a7eb,0xfb791ebc,0xf8435d45,0x17d69902,0xabcbff3f,0x89aea264,0x91e6f391,0x286bd78c,],
[0x06c0dd87,0x3e450272,0x3ec5806d,0x61756fbd,0x1fa17803,0xd850d59d,0x007e529a,0x4f98acc2,0x1743134b,0xb50fc7ba,0xdc27da82,0xd1356bee,0x85ce8d51,0xb208d924,0x9adb5f7f,0x2ac01a18,0x2bc84d52,0x8b78825e,0x24fd0e23,0x06c0dd87,0x3e450272,0x3ec5806d,0x61756fbd,0x1fa17803,0xd850d59d,0x007e529a,0x4f98acc2,0x1743134b,0xb50fc7ba,0xdc27da82,0xd1356bee,0x85ce8d51,0xb208d924,0x9adb5f7f,0x2ac01a18,0x2bc84d52,0x8b78825e,],
[0x01e7b769,0x9cda9d0f,0xd03d453a,0x4de8bced,0xed94125c,0xd01fed52,0xa742ffaf,0x9d3140f9,0x299a0fb2,0x1f69eb2e,0xcd3cb636,0xc28059aa,0x0291f830,0xd44c9cf9,0x959e3cb9,0x96ea4c56,0x2c405f0e,0x38c2b3f7,0x51550cce,0x01e7b769,0x9cda9d0f,0xd03d453a,0x4de8bced,0xed94125c,0xd01fed52,0xa742ffaf,0x9d3140f9,0x299a0fb2,0x1f69eb2e,0xcd3cb636,0xc28059aa,0x0291f830,0xd44c9cf9,0x959e3cb9,0x96ea4c56,0x2c405f0e,0x38c2b3f7,],
[0xa040e852,0xd4410199,0x0e9e4511,0x24420004,0x3bdfe36b,0x3bdc3bb2,0xad595d1e,0x73d7f1ff,0x5665cc02,0xbc8a762c,0x9492451a,0x7420bc00,0xf8d13192,0xf18691df,0x455fcb2f,0xed686c67,0x0838708c,0xd6e5d8cb,0xf5449f0c,0xa040e852,0xd4410199,0x0e9e4511,0x24420004,0x3bdfe36b,0x3bdc3bb2,0xad595d1e,0x73d7f1ff,0x5665cc02,0xbc8a762c,0x9492451a,0x7420bc00,0xf8d13192,0xf18691df,0x455fcb2f,0xed686c67,0x0838708c,0xd6e5d8cb,],
[0x14afec18,0x3444a0c9,0x3fecc24c,0x053af182,0x23dd66ff,0x1c79a102,0x08e513b9,0x3182c015,0xb9e70105,0x794d3fda,0xa006abb1,0x4c35731d,0x556fd586,0xfc157344,0xcc4ea93d,0x477b9215,0xd2df003c,0x669f3a5a,0x6d742151,0x14afec18,0x3444a0c9,0x3fecc24c,0x053af182,0x23dd66ff,0x1c79a102,0x08e513b9,0x3182c015,0xb9e70105,0x794d3fda,0xa006abb1,0x4c35731d,0x556fd586,0xfc157344,0xcc4ea93d,0x477b9215,0xd2df003c,0x669f3a5a,],
[0x7800c5b5,0xa8b7a96d,0x1e4e08f2,0x2bd7fede,0x92383a3a,0x5c15732f,0xe696b2c1,0x970fb122,0x23dba041,0x1c35baf1,0x43a81629,0xf5d14f9b,0x819201cf,0x42bd56a8,0xcecd5e28,0xa3dd3aa1,0xca9b693a,0xc67320e4,0x130bf5da,0x7800c5b5,0xa8b7a96d,0x1e4e08f2,0x2bd7fede,0x92383a3a,0x5c15732f,0xe696b2c1,0x970fb122,0x23dba041,0x1c35baf1,0x43a81629,0xf5d14f9b,0x819201cf,0x42bd56a8,0xcecd5e28,0xa3dd3aa1,0xca9b693a,0xc67320e4,],
[0xe6946ce4,0x99444656,0xd2f5f2a1,0x3a4c0305,0xae2dba9d,0x2170c140,0x5d62dea2,0x88cc6c3d,0xa50f6b51,0xfb7c35ce,0xb85d354b,0xdc4c5606,0xe79e4158,0x1ead6211,0x4f7f23f6,0x50ee7005,0x0c8ae855,0xf1750996,0xed22b67e,0xe6946ce4,0x99444656,0xd2f5f2a1,0x3a4c0305,0xae2dba9d,0x2170c140,0x5d62dea2,0x88cc6c3d,0xa50f6b51,0xfb7c35ce,0xb85d354b,0xdc4c5606,0xe79e4158,0x1ead6211,0x4f7f23f6,0x50ee7005,0x0c8ae855,0xf1750996,],
];

#[rustfmt::skip]
const MDS_FULL: [[u64; STATE_SIZE]; STATE_SIZE] =[
[0x59255cd8, 0x63fed572, 0x613e437a, 0x5be5cad0, 0x3adb89ab, 0x5be5cad1, 0x00000001, 0x613e437b,],
[0x381b1fa2, 0x02c09608, 0x613e437a, 0x613e437a, 0x3adb89aa, 0x5be5cad0, 0x00000001, 0x00000001,],
[0x613e437a, 0x5be5cad0, 0x59255cd8, 0x63fed572, 0x00000001, 0x613e437b, 0x3adb89ab, 0x5be5cad1,],
[0x613e437a, 0x613e437a, 0x381b1fa2, 0x02c09608, 0x00000001, 0x00000001, 0x3adb89aa, 0x5be5cad0,],
[0x3adb89ab, 0x5be5cad1, 0x00000001, 0x613e437b, 0x59255cd8, 0x63fed572, 0x613e437a, 0x5be5cad0,],
[0x3adb89aa, 0x5be5cad0, 0x00000001, 0x00000001, 0x381b1fa2, 0x02c09608, 0x613e437a, 0x613e437a,],
[0x00000001, 0x613e437b, 0x3adb89ab, 0x5be5cad1, 0x613e437a, 0x5be5cad0, 0x59255cd8, 0x63fed572,],
[0x00000001, 0x00000001, 0x3adb89aa, 0x5be5cad0, 0x613e437a, 0x613e437a, 0x381b1fa2, 0x02c09608,],
];
#[rustfmt::skip]
const MDS_PARTIAL: [[u64; STATE_SIZE]; STATE_SIZE] = [
[0x4e03b689, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x08ef573b, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x3988ebad, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0xc0d70a71, 0x00000001, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x316e0c1a, 0x00000001, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x55db14c2, 0x00000001, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x966e7508, 0x00000001],
[0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0x00000001, 0xa46ba225],
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
	// let state_size = state_in.len();
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
	// round_constants: [u64; N_ROUNDS],
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
	use binius_field:: BinaryField64b;

	use super::permutation;
	use crate::{
		builder::test_utils::test_circuit,
		hades::poseidon2b_x7_64_512::STATE_SIZE,
		unconstrained::unconstrained,
	};
	#[test]
	fn test_poseidon2b() {
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