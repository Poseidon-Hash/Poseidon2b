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
pub const RC: [[u64; N_ROUNDS]; STATE_SIZE] = [[0x2e, 0x79, 0x70, 0x2, 0x79, 0x66, 0x28, 0x53, 0x6c, 0x14, 0x65, 0x22, 0x1b, 0x65, 0x36, 0x9, 0xc, 0x5, 0x50, 0x2d, 0x37, 0x71, 0x4e, 0x7a, 0x6f, 0x48, 0x2b, 0x2d, 0xa, 0x1b, 0x74, 0x2a, 0x21, 0x42, 0x1f, 0x32, 0x3c, ],
[0x1b, 0x4c, 0x2a, 0x54, 0x5c, 0x6a, 0x51, 0x59, 0x10, 0x6f, 0x2, 0x77, 0x79, 0x6e, 0x4c, 0x40, 0x3f, 0x51, 0x66, 0x5e, 0x5c, 0x36, 0x12, 0x28, 0x4d, 0x1c, 0x19, 0x6c, 0x16, 0x6, 0x49, 0x5c, 0x7d, 0x78, 0x4a, 0x47, 0x67, ],
[0x1c, 0x50, 0x22, 0x2c, 0x16, 0x5f, 0x9, 0x6e, 0x5, 0x36, 0x8, 0x1, 0x3b, 0x4d, 0x3c, 0x38, 0x5c, 0x2c, 0x47, 0x62, 0x2a, 0xc, 0x25, 0x13, 0x29, 0x29, 0x17, 0x20, 0x61, 0x1c, 0x3f, 0x66, 0x53, 0x18, 0x56, 0x76, 0x7c, ],
[0x0, 0x36, 0x45, 0x6a, 0x79, 0x35, 0x33, 0x17, 0x61, 0x32, 0x6e, 0x3d, 0x12, 0x32, 0xc, 0x3a, 0x2d, 0x36, 0x29, 0x19, 0x55, 0x22, 0x42, 0x28, 0x5, 0x23, 0x11, 0x1f, 0xe, 0x11, 0x7b, 0x43, 0x6c, 0x7f, 0x1c, 0x29, 0x7c, ],
[0x77, 0x67, 0x67, 0x1b, 0x27, 0x1a, 0x70, 0x3d, 0x1b, 0x4b, 0x62, 0xf, 0x1f, 0x2d, 0x52, 0x3f, 0x1b, 0x5e, 0x9, 0x2d, 0xd, 0x6d, 0x66, 0x6b, 0x4a, 0x26, 0x7e, 0x26, 0x12, 0x13, 0x22, 0x25, 0x73, 0x64, 0x14, 0x38, 0x53, ],
[0x74, 0x6d, 0x78, 0x7a, 0xe, 0x35, 0x1f, 0x62, 0xe, 0x1f, 0x38, 0x4a, 0x33, 0x33, 0x15, 0x50, 0x4, 0x22, 0x75, 0x7, 0x4a, 0x63, 0x7, 0x52, 0x4c, 0x35, 0x12, 0x26, 0x68, 0x7c, 0x16, 0x57, 0x20, 0x3a, 0x13, 0x24, 0x4c, ],
[0x4d, 0x4e, 0x6a, 0x1, 0xc, 0x65, 0x16, 0x4e, 0x5f, 0x7c, 0x4d, 0x3a, 0x73, 0x4f, 0x4b, 0x7a, 0x74, 0x72, 0x38, 0x24, 0x51, 0x6c, 0x6d, 0x7a, 0xb, 0xe, 0x6a, 0x18, 0x69, 0x6, 0x5f, 0x63, 0x5b, 0x30, 0x63, 0x5c, 0x53, ],
[0x36, 0x62, 0x35, 0x2c, 0x42, 0x7e, 0x51, 0x25, 0x5a, 0x3, 0x6f, 0x57, 0x48, 0x5b, 0x79, 0x5f, 0x44, 0x7b, 0x34, 0x2e, 0x46, 0x5c, 0x58, 0x23, 0x4d, 0x46, 0x63, 0x1b, 0x68, 0x29, 0x3b, 0x31, 0x5, 0x6, 0x50, 0x17, 0x39, ]
];

pub const MDS_FULL: [[u64; STATE_SIZE]; STATE_SIZE] = [
[0xcd0fe740fd9497b5,0xebb2a1bc3f3c4892,0xdc2e39b30464356c,0xb358e851e1415a8e,0xd4c8e3b711e95c6a,0x6159edbec5a863d5,0x6e16001c1f9def47,0xafe4aa83acdfa525],
[0x4c23a913dd92fb1d,0x7bdb722d546d5657,0x64eafd4a57c53dc0,0xfb6cf006911c26ad,0x2df305bf073163bb,0xabba2ed74d67ff40,0xe29190fb0e955821,0xd5e9d4d4c63e0b16],
[0x848e30bca74d0c80,0xd076a7e7726ae53f,0x053443c76b0fa837,0x48da289545dbe552,0x395dd8757ba1ecfa,0x329cf003203f16f8,0xf25c155ed79e4570,0x262c3d45b420481c],
[0x6aa016fe1990a896,0x43ea2ec1fa8a8ff1,0xee0351f5955d09eb,0x6fb5a6c3795387f7,0x55100638fb36968c,0x17fc72fd88871b3f,0xaf3bda217e64ee9e,0x9ec849d3a6c432b0],
[0x057dcac62a6414a1,0x3703406c3003a7fd,0xb77ff993ca335a90,0x3451ced3dd99dca7,0x764be78cc795dc40,0x1e571c053193e2d4,0x92f5c26fbd0d5bec,0x534691e888abcee8],
[0xe883c0a8ccdc6b28,0x7482192c6e386436,0x83cc8d3c39d440ef,0x5039c53e7c697359,0x48740353f5167afe,0xf250ae0a816cefb4,0xdb02139bc42ae1de,0xd211bab362d5f4be],
[0xa24e6373eae260f5,0x0579d43fca8c2221,0x09128263c6ef4bcd,0x5e7614dca82c36d0,0x794a84dd0c0e2d09,0xfda9df54ac1ac25c,0x33f9b946f5cff428,0x196ddef20e24e7fb],
[0xdbc8fd7e6b15d4c7,0x9552d3fe45413156,0xb3af6231a7b1e861,0x21047162f80943d1,0xf365173ab870eae6,0x76e442ccf7792066,0xb2cdf0bfa3441f72,0x8321d0d48c5e1a30],
];
#[rustfmt::skip]
const MDS_PARTIAL: [[u64; STATE_SIZE]; STATE_SIZE] = [
[0x81, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x2, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x200, 0x1, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x80, 0x1, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x2000, 0x1, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1000, 0x1, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x4000, 0x1,],
[0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x1, 0x40,],
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
		hades::poseidonb_x7_64_512::STATE_SIZE,
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