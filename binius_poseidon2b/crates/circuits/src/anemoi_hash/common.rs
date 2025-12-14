//! Example of a Binius SNARK that proves execution of Anemoi permutations over characteristic-2 binary fields.

use std::fmt::Debug;

use anyhow::Result;
use bytemuck::Pod;
use binius_core::oracle::OracleId;
use binius_field::{
	as_packed_field::PackScalar, BinaryField, BinaryField128b, BinaryField32b, BinaryField64b,
	ExtensionField, Field as BiniusField, TowerField,
};
use binius_math::{ArithCircuit, ArithExpr};

use crate::builder::{types::{F, U}, ConstraintSystemBuilder};

use super::params;

type FF = F;

pub trait FieldOps:
	'static + Copy + Clone + Debug + Default + PartialEq + Send + Sync + BiniusField
{
	fn safe_add(self, rhs: Self) -> Self;
	fn safe_mul(self, rhs: Self) -> Self;
	fn safe_square(self) -> Self;
	fn from_u8(v: u8) -> Self;
}

pub trait FieldConst: FieldOps {
	type Raw: Copy;
	fn from_raw(v: Self::Raw) -> Self;
}

macro_rules! impl_field_ops {
	($ty:ty, $raw:ty) => {
		impl FieldOps for $ty {
			#[inline(always)]
			fn safe_add(self, rhs: Self) -> Self { self + rhs }
			#[inline(always)]
			fn safe_mul(self, rhs: Self) -> Self { self * rhs }
			#[inline(always)]
			fn safe_square(self) -> Self { self * self }
			#[inline(always)]
			fn from_u8(v: u8) -> Self { Self::from(v as $raw) }
		}
		impl FieldConst for $ty {
			type Raw = $raw;
			#[inline(always)]
			fn from_raw(v: Self::Raw) -> Self { Self::from(v) }
		}
	};
}

impl_field_ops!(BinaryField32b, u32);
impl_field_ops!(BinaryField64b, u64);
impl_field_ops!(BinaryField128b, u128);

#[inline(always)]
fn pow_const<F: FieldOps>(mut base: F, mut exp: u128) -> F {
	let mut acc = F::from_u8(1);
	while exp > 0 {
		if exp & 1 == 1 {
			acc = acc.safe_mul(base);
		}
		base = base.safe_square();
		exp >>= 1;
	}
	acc
}

#[inline(always)]
fn pow_alpha<F: FieldOps>(x: F) -> F {
	let x2 = x.safe_square();
	let x4 = x2.safe_square();
	x.safe_mul(x2).safe_mul(x4) // x^7
}

pub trait AnemoiField: FieldConst + BinaryField + TowerField + Pod {
	const ALPHA_INV: u128;
}

impl AnemoiField for BinaryField32b {
	const ALPHA_INV: u128 = params::ALPHA_INV_32;
}

impl AnemoiField for BinaryField64b {
	const ALPHA_INV: u128 = params::ALPHA_INV_64;
}

impl AnemoiField for BinaryField128b {
	const ALPHA_INV: u128 = params::ALPHA_INV_128;
}

#[derive(Clone)]
pub struct AnemoiParams<F: FieldConst> {
	pub t: usize,
	pub l: usize,
	pub rounds: usize,
	pub alpha_inv: u128,
	pub beta: F,
	pub delta: F,
	pub c: Vec<Vec<F>>,
	pub d: Vec<Vec<F>>,
	pub mds: Vec<Vec<F>>,
}

pub fn prep_params<F: AnemoiField, const L: usize, const R: usize>(
	alpha_inv: u128,
	mds_raw: &[[F::Raw; L]; L],
	c_raw: &[[F::Raw; L]; R],
	d_raw: &[[F::Raw; L]; R],
) -> AnemoiParams<F> {
	let t = 2 * L;
	let mds = mds_raw
		.iter()
		.map(|row| row.iter().copied().map(F::from_raw).collect())
		.collect();
	let c = c_raw
		.iter()
		.map(|row| row.iter().copied().map(F::from_raw).collect())
		.collect();
	let d = d_raw
		.iter()
		.map(|row| row.iter().copied().map(F::from_raw).collect())
		.collect();
	AnemoiParams {
		t,
		l: L,
		rounds: R,
		alpha_inv,
		beta: F::MULTIPLICATIVE_GENERATOR,
		delta: F::MULTIPLICATIVE_GENERATOR
			.invert()
			.expect("generator non-zero"),
		c,
		d,
		mds,
	}
}

pub fn plain_permutation<F: AnemoiField>(state: &mut [F], params: &AnemoiParams<F>) {
	let l = params.l;
	let mut x: Vec<F> = state[..l].to_vec();
	let mut y: Vec<F> = state[l..].to_vec();

	for r in 0..params.rounds {
		for i in 0..l {
			x[i] = x[i].safe_add(params.c[r][i]);
			y[i] = y[i].safe_add(params.d[r][i]);
		}
		linear_layer_plain(&mut x, &mut y, &params.mds);
		for i in 0..l {
			let y_pow = pow_alpha(y[i]);
			let t = x[i].safe_add(params.beta.safe_mul(y_pow)).safe_add(params.delta);
			let inv = pow_const(t, params.alpha_inv);
			y[i] = y[i].safe_add(inv);
			let y_pow_new = pow_alpha(y[i]);
			x[i] = t.safe_add(params.beta.safe_mul(y_pow_new));
		}
	}

	apply_mds_only_plain(&mut x, &mut y, &params.mds);

	state[..l].copy_from_slice(&x);
	state[l..].copy_from_slice(&y);
}

fn linear_layer_plain<F: FieldOps>(x: &mut [F], y: &mut [F], mds: &[Vec<F>]) {
	let l = x.len();
	let mut new_x = vec![F::default(); l];
	let mut new_y = vec![F::default(); l];

	for r in 0..l {
		for c in 0..l {
			new_x[r] = new_x[r].safe_add(mds[r][c].safe_mul(x[c]));
		}
	}

	let mut y_rot = vec![F::default(); l];
	for i in 0..l - 1 {
		y_rot[i] = y[i + 1];
	}
	y_rot[l - 1] = y[0];

	for r in 0..l {
		for c in 0..l {
			new_y[r] = new_y[r].safe_add(mds[r][c].safe_mul(y_rot[c]));
		}
	}

	for i in 0..l {
		new_y[i] = new_y[i].safe_add(new_x[i]);
		new_x[i] = new_x[i].safe_add(new_y[i]);
	}

	x.copy_from_slice(&new_x);
	y.copy_from_slice(&new_y);
}

fn apply_mds_only_plain<F: FieldOps>(x: &mut [F], y: &mut [F], mds: &[Vec<F>]) {
	let l = x.len();
	let mut new_x = vec![F::default(); l];
	let mut new_y = vec![F::default(); l];

	for r in 0..l {
		for c in 0..l {
			new_x[r] = new_x[r].safe_add(mds[r][c].safe_mul(x[c]));
		}
	}

	let mut y_rot = vec![F::default(); l];
	for i in 0..l - 1 {
		y_rot[i] = y[i + 1];
	}
	y_rot[l - 1] = y[0];

	for r in 0..l {
		for c in 0..l {
			new_y[r] = new_y[r].safe_add(mds[r][c].safe_mul(y_rot[c]));
		}
	}

	x.copy_from_slice(&new_x);
	y.copy_from_slice(&new_y);
}

// enforce that output = input^2

fn enforce_square(builder: &mut ConstraintSystemBuilder, name: impl ToString, input: OracleId, output: OracleId) {
	let expr = (ArithExpr::Var(0) * ArithExpr::Var(0) - ArithExpr::Var(1)).into();
	builder.assert_zero(name, [input, output], expr);
}

//enforce that output = left * right

fn enforce_product(
	builder: &mut ConstraintSystemBuilder,
	name: impl ToString,
	left: OracleId,
	right: OracleId,
	output: OracleId,
) {
	let expr = (ArithExpr::Var(0) * ArithExpr::Var(1) - ArithExpr::Var(2)).into();
	builder.assert_zero(name, [left, right, output], expr);
}

//enforce that left == right

fn enforce_eq(builder: &mut ConstraintSystemBuilder, name: impl ToString, left: OracleId, right: OracleId) {
	let expr = (ArithExpr::Var(0) - ArithExpr::Var(1)).into();
	builder.assert_zero(name, [left, right], expr);
}

//enforce that output = sum_i coeffs[i] * inputs[i] + offset

fn enforce_lin_comb<FBase: FieldConst>(
	builder: &mut ConstraintSystemBuilder,
	name: impl ToString,
	inputs: &[OracleId],
	coeffs: &[FBase],
	output: OracleId,
	offset: FBase,
) where
	FF: ExtensionField<FBase>,
{
	let mut expr = ArithExpr::Var(inputs.len()) - ArithExpr::Const(FF::from(offset));
	for (idx, coeff) in coeffs.iter().enumerate() {
		expr = expr - ArithExpr::Const(FF::from(*coeff)) * ArithExpr::Var(idx);
	}
	let ids: Vec<_> = inputs.iter().copied().chain(std::iter::once(output)).collect();
	builder.assert_zero(name, ids, ArithCircuit::from(expr));
}


#[derive(Copy, Clone)]
struct Pow7Cols {
	sq: OracleId,
	quad: OracleId,
	pow6: OracleId,
	pow7: OracleId,
}

// Adds columns and constraints to compute input^7

fn add_pow7<F: FieldConst>(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	prefix: &str,
	input: OracleId,
) -> Pow7Cols
where
	FF: ExtensionField<F>,
	F: TowerField,
{
	let sq = builder.add_committed(format!("{prefix}_sq"), log_size, F::TOWER_LEVEL);
	let quad = builder.add_committed(format!("{prefix}_quad"), log_size, F::TOWER_LEVEL);
	let pow6 = builder.add_committed(format!("{prefix}_pow6"), log_size, F::TOWER_LEVEL);
	let pow7 = builder.add_committed(format!("{prefix}_pow7"), log_size, F::TOWER_LEVEL);

	enforce_square(builder, format!("{prefix}_sq_check"), input, sq);
	enforce_square(builder, format!("{prefix}_quad_check"), sq, quad);
	enforce_product(builder, format!("{prefix}_pow6_check"), quad, sq, pow6);
	enforce_product(builder, format!("{prefix}_pow7_check"), pow6, input, pow7);

	Pow7Cols { sq, quad, pow6, pow7 }
}

struct SboxCols {
	y_pow: Pow7Cols,
	t: OracleId,
	y_out: OracleId,
	sum: OracleId,
	sum_pow: Pow7Cols,
	y_out_pow: Pow7Cols,
	x_out: OracleId,
}

// Adds columns and constraints for one Anemoi S-box in the closed mode of flystel sturcture 

fn add_sbox<F: AnemoiField>(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	idx: usize,
	params: &AnemoiParams<F>,
	x_in: OracleId,
	y_in: OracleId,
) -> SboxCols
where
	FF: ExtensionField<F>,
{
	let y_pow = add_pow7::<F>(builder, log_size, &format!("sbox_{idx}_y_in"), y_in);
	let t = builder.add_committed(format!("sbox_{idx}_t"), log_size, F::TOWER_LEVEL);
	let y_out = builder.add_committed(format!("sbox_{idx}_y_out"), log_size, F::TOWER_LEVEL);
	let sum = builder.add_committed(format!("sbox_{idx}_sum"), log_size, F::TOWER_LEVEL);
	let sum_pow = add_pow7::<F>(builder, log_size, &format!("sbox_{idx}_sum"), sum);
	let y_out_pow = add_pow7::<F>(builder, log_size, &format!("sbox_{idx}_y_out"), y_out);
	let x_out = builder.add_committed(format!("sbox_{idx}_x_out"), log_size, F::TOWER_LEVEL);

	enforce_lin_comb(
		builder,
		format!("sbox_{idx}_t_check"),
		&[x_in, y_pow.pow7],
		&[F::ONE, params.beta],
		t,
		params.delta,
	);
	enforce_lin_comb(
		builder,
		format!("sbox_{idx}_sum_check"),
		&[y_out, y_in],
		&[F::ONE, F::ONE],
		sum,
		F::ZERO,
	);
	enforce_eq(builder, format!("sbox_{idx}_closed_check"), sum_pow.pow7, t);
	enforce_lin_comb(
		builder,
		format!("sbox_{idx}_x_out_check"),
		&[t, y_out_pow.pow7],
		&[F::ONE, params.beta],
		x_out,
		F::ZERO,
	);

	SboxCols {
		y_pow,
		t,
		y_out,
		sum,
		sum_pow,
		y_out_pow,
		x_out,
	}
}

// Fills columns for value^2, value^4, value^6, value^7

fn fill_pow7_column<F: FieldOps>(value: F) -> (F, F, F, F) {
	let sq = value.safe_square();
	let quad = sq.safe_square();
	let pow6 = quad.safe_mul(sq);
	let pow7 = pow6.safe_mul(value);
	(sq, quad, pow6, pow7)
}

// One single Anemoi round in the permutation

fn anemoi_round<F: AnemoiField>(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	round: usize,
	x_state: Vec<OracleId>,
	y_state: Vec<OracleId>,
	params: &AnemoiParams<F>,
) -> Result<(Vec<OracleId>, Vec<OracleId>)>
where
	FF: ExtensionField<F>,
	U: PackScalar<F>,
{
	let l = params.l;
	builder.push_namespace(format!("round_{round}"));

	let mut x_rc = Vec::with_capacity(l);
	let mut y_rc = Vec::with_capacity(l);
	let mut mds_x = Vec::with_capacity(l);
	let mut mds_y = Vec::with_capacity(l);
	let mut new_y = Vec::with_capacity(l);
	let mut new_x = Vec::with_capacity(l);
	let mut sboxes = Vec::with_capacity(l);

	for i in 0..l {
		x_rc.push(builder.add_committed(format!("r{round}_x_rc_{i}"), log_size, F::TOWER_LEVEL));
		y_rc.push(builder.add_committed(format!("r{round}_y_rc_{i}"), log_size, F::TOWER_LEVEL));
		mds_x.push(builder.add_committed(format!("r{round}_mds_x_{i}"), log_size, F::TOWER_LEVEL));
		mds_y.push(builder.add_committed(format!("r{round}_mds_y_{i}"), log_size, F::TOWER_LEVEL));
		new_y.push(builder.add_committed(format!("r{round}_new_y_{i}"), log_size, F::TOWER_LEVEL));
		new_x.push(builder.add_committed(format!("r{round}_new_x_{i}"), log_size, F::TOWER_LEVEL));
	}

	for i in 0..l {
		enforce_lin_comb(
			builder,
			format!("r{round}_x_const_{i}"),
			&[x_state[i]],
			&[F::ONE],
			x_rc[i],
			params.c[round][i],
		);
		enforce_lin_comb(
			builder,
			format!("r{round}_y_const_{i}"),
			&[y_state[i]],
			&[F::ONE],
			y_rc[i],
			params.d[round][i],
		);
	}

	for row in 0..l {
		enforce_lin_comb(
			builder,
			format!("r{round}_mds_x_{row}_check"),
			&x_rc,
			&params.mds[row],
			mds_x[row],
			F::ZERO,
		);

		let rotated_inputs: Vec<_> = (0..l).map(|i| y_rc[(i + 1) % l]).collect();
		enforce_lin_comb(
			builder,
			format!("r{round}_mds_y_{row}_check"),
			&rotated_inputs,
			&params.mds[row],
			mds_y[row],
			F::ZERO,
		);

		enforce_lin_comb(
			builder,
			format!("r{round}_new_y_{row}_check"),
			&[mds_y[row], mds_x[row]],
			&[F::ONE, F::ONE],
			new_y[row],
			F::ZERO,
		);
		enforce_lin_comb(
			builder,
			format!("r{round}_new_x_{row}_check"),
			&[mds_x[row], new_y[row]],
			&[F::ONE, F::ONE],
			new_x[row],
			F::ZERO,
		);
	}

	for i in 0..l {
		let sbox = add_sbox(builder, log_size, i, params, new_x[i], new_y[i]);
		sboxes.push(sbox);
	}

	builder.pop_namespace();

	if let Some(witness) = builder.witness() {
		let rows = 1 << log_size;

		let x_prev: Vec<_> = x_state
			.iter()
			.map(|&id| witness.get::<F>(id).unwrap().as_slice::<F>())
			.collect();
		let y_prev: Vec<_> = y_state
			.iter()
			.map(|&id| witness.get::<F>(id).unwrap().as_slice::<F>())
			.collect();

		let mut x_rc_cols: Vec<_> = x_rc.iter().map(|&id| witness.new_column::<F>(id)).collect();
		let mut y_rc_cols: Vec<_> = y_rc.iter().map(|&id| witness.new_column::<F>(id)).collect();
		let mut mds_x_cols: Vec<_> = mds_x.iter().map(|&id| witness.new_column::<F>(id)).collect();
		let mut mds_y_cols: Vec<_> = mds_y.iter().map(|&id| witness.new_column::<F>(id)).collect();
		let mut new_y_cols: Vec<_> = new_y.iter().map(|&id| witness.new_column::<F>(id)).collect();
		let mut new_x_cols: Vec<_> = new_x.iter().map(|&id| witness.new_column::<F>(id)).collect();

		for z in 0..rows {
			for i in 0..l {
				x_rc_cols[i].as_mut_slice::<F>()[z] = x_prev[i][z].safe_add(params.c[round][i]);
				y_rc_cols[i].as_mut_slice::<F>()[z] = y_prev[i][z].safe_add(params.d[round][i]);
			}
		}

		for z in 0..rows {
			for row in 0..l {
				let mut acc_x = F::ZERO;
				for col in 0..l {
					acc_x = acc_x.safe_add(params.mds[row][col].safe_mul(x_rc_cols[col].as_mut_slice::<F>()[z]));
				}
				mds_x_cols[row].as_mut_slice::<F>()[z] = acc_x;

				let mut acc_y = F::ZERO;
				for col in 0..l {
					let src = (col + 1) % l;
					acc_y = acc_y.safe_add(params.mds[row][col].safe_mul(y_rc_cols[src].as_mut_slice::<F>()[z]));
				}
				mds_y_cols[row].as_mut_slice::<F>()[z] = acc_y;

				let ny = acc_y.safe_add(acc_x);
				new_y_cols[row].as_mut_slice::<F>()[z] = ny;
				new_x_cols[row].as_mut_slice::<F>()[z] = ny.safe_add(acc_x);
			}
		}

		let mut sbox_y_pow: Vec<_> = sboxes
			.iter()
			.map(|ids| {
				(
					witness.new_column::<F>(ids.y_pow.sq),
					witness.new_column::<F>(ids.y_pow.quad),
					witness.new_column::<F>(ids.y_pow.pow6),
					witness.new_column::<F>(ids.y_pow.pow7),
				)
			})
			.collect();
		let mut sbox_t: Vec<_> = sboxes.iter().map(|ids| witness.new_column::<F>(ids.t)).collect();
		let mut sbox_y_out: Vec<_> = sboxes.iter().map(|ids| witness.new_column::<F>(ids.y_out)).collect();
		let mut sbox_sum: Vec<_> = sboxes.iter().map(|ids| witness.new_column::<F>(ids.sum)).collect();
		let mut sbox_sum_pow: Vec<_> = sboxes
			.iter()
			.map(|ids| {
				(
					witness.new_column::<F>(ids.sum_pow.sq),
					witness.new_column::<F>(ids.sum_pow.quad),
					witness.new_column::<F>(ids.sum_pow.pow6),
					witness.new_column::<F>(ids.sum_pow.pow7),
				)
			})
			.collect();
		let mut sbox_y_out_pow: Vec<_> = sboxes
			.iter()
			.map(|ids| {
				(
					witness.new_column::<F>(ids.y_out_pow.sq),
					witness.new_column::<F>(ids.y_out_pow.quad),
					witness.new_column::<F>(ids.y_out_pow.pow6),
					witness.new_column::<F>(ids.y_out_pow.pow7),
				)
			})
			.collect();
		let mut sbox_x_out: Vec<_> = sboxes.iter().map(|ids| witness.new_column::<F>(ids.x_out)).collect();

		for z in 0..rows {
			for i in 0..l {
				let y_lin = new_y_cols[i].as_mut_slice::<F>()[z];
				let (y_sq, y_quad, y_pow6, y_pow7) = fill_pow7_column(y_lin);
				let x_lin = new_x_cols[i].as_mut_slice::<F>()[z];
				let t_val = x_lin.safe_add(params.beta.safe_mul(y_pow7)).safe_add(params.delta);
				let inv = pow_const(t_val, params.alpha_inv);
				let y_out_val = y_lin.safe_add(inv);
				let sum_val = y_out_val.safe_add(y_lin);
				let (sum_sq, sum_quad, sum_pow6, sum_pow7) = fill_pow7_column(sum_val);
				let (y_out_sq, y_out_quad, y_out_pow6, y_out_pow7) = fill_pow7_column(y_out_val);
				let x_out_val = t_val.safe_add(params.beta.safe_mul(y_out_pow7));

				sbox_y_pow[i].0.as_mut_slice::<F>()[z] = y_sq;
				sbox_y_pow[i].1.as_mut_slice::<F>()[z] = y_quad;
				sbox_y_pow[i].2.as_mut_slice::<F>()[z] = y_pow6;
				sbox_y_pow[i].3.as_mut_slice::<F>()[z] = y_pow7;
				sbox_t[i].as_mut_slice::<F>()[z] = t_val;
				sbox_y_out[i].as_mut_slice::<F>()[z] = y_out_val;
				sbox_sum[i].as_mut_slice::<F>()[z] = sum_val;
				sbox_sum_pow[i].0.as_mut_slice::<F>()[z] = sum_sq;
				sbox_sum_pow[i].1.as_mut_slice::<F>()[z] = sum_quad;
				sbox_sum_pow[i].2.as_mut_slice::<F>()[z] = sum_pow6;
				sbox_sum_pow[i].3.as_mut_slice::<F>()[z] = sum_pow7;
				sbox_y_out_pow[i].0.as_mut_slice::<F>()[z] = y_out_sq;
				sbox_y_out_pow[i].1.as_mut_slice::<F>()[z] = y_out_quad;
				sbox_y_out_pow[i].2.as_mut_slice::<F>()[z] = y_out_pow6;
				sbox_y_out_pow[i].3.as_mut_slice::<F>()[z] = y_out_pow7;
				sbox_x_out[i].as_mut_slice::<F>()[z] = x_out_val;
			}
		}
	}

	let x_out: Vec<OracleId> = sboxes.iter().map(|s| s.x_out).collect();
	let y_out: Vec<OracleId> = sboxes.iter().map(|s| s.y_out).collect();
	Ok((x_out, y_out))
}

// Final MDS layer in the round function

fn apply_mds_only<F: AnemoiField>(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	x_state: Vec<OracleId>,
	y_state: Vec<OracleId>,
	params: &AnemoiParams<F>,
) -> Result<(Vec<OracleId>, Vec<OracleId>)>
where
	FF: ExtensionField<F>,
	U: PackScalar<F>,
{
	let l = params.l;
	builder.push_namespace("final_mds");

	let mut mds_x = Vec::with_capacity(l);
	let mut mds_y = Vec::with_capacity(l);

	for i in 0..l {
		mds_x.push(builder.add_committed(format!("final_mds_x_{i}"), log_size, F::TOWER_LEVEL));
		mds_y.push(builder.add_committed(format!("final_mds_y_{i}"), log_size, F::TOWER_LEVEL));
	}

	for row in 0..l {
		enforce_lin_comb(
			builder,
			format!("final_mds_x_{row}_check"),
			&x_state,
			&params.mds[row],
			mds_x[row],
			F::ZERO,
		);

		let rotated_inputs: Vec<_> = (0..l).map(|i| y_state[(i + 1) % l]).collect();
		enforce_lin_comb(
			builder,
			format!("final_mds_y_{row}_check"),
			&rotated_inputs,
			&params.mds[row],
			mds_y[row],
			F::ZERO,
		);
	}

	builder.pop_namespace();

	if let Some(witness) = builder.witness() {
		let rows = 1 << log_size;
		let x_prev: Vec<_> = x_state
			.iter()
			.map(|&id| witness.get::<F>(id).unwrap().as_slice::<F>())
			.collect();
		let y_prev: Vec<_> = y_state
			.iter()
			.map(|&id| witness.get::<F>(id).unwrap().as_slice::<F>())
			.collect();

		let mut mds_x_cols: Vec<_> = mds_x.iter().map(|&id| witness.new_column::<F>(id)).collect();
		let mut mds_y_cols: Vec<_> = mds_y.iter().map(|&id| witness.new_column::<F>(id)).collect();

		for z in 0..rows {
			for row in 0..l {
				let mut acc_x = F::ZERO;
				for col in 0..l {
					acc_x = acc_x.safe_add(params.mds[row][col].safe_mul(x_prev[col][z]));
				}
				mds_x_cols[row].as_mut_slice::<F>()[z] = acc_x;

				let mut acc_y = F::ZERO;
				for col in 0..l {
					let src = (col + 1) % l;
					acc_y = acc_y.safe_add(params.mds[row][col].safe_mul(y_prev[src][z]));
				}
				mds_y_cols[row].as_mut_slice::<F>()[z] = acc_y;
			}
		}
	}

	Ok((mds_x, mds_y))
}

// Full Anemoi permutation

pub fn anemoi_permutation<F: AnemoiField>(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	state_in: &[OracleId],
	params: &AnemoiParams<F>,
) -> Result<Vec<OracleId>>
where
	FF: ExtensionField<F>,
	U: PackScalar<F>,
{
	let l = params.l;
	debug_assert_eq!(state_in.len(), params.t, "anemoi state size mismatch");
	let mut x_state = state_in[..l].to_vec();
	let mut y_state = state_in[l..].to_vec();

	for r in 0..params.rounds {
		let (x_next, y_next) = anemoi_round(builder, log_size, r, x_state, y_state, params)?;
		x_state = x_next;
		y_state = y_next;
	}

	let (x_final, y_final) = apply_mds_only(builder, log_size, x_state, y_state, params)?;

	let mut out = x_final;
	out.extend_from_slice(&y_final);

	#[cfg(debug_assertions)]
	if let Some(witness) = builder.witness() {
		let rows = 1 << log_size;
		let input_data: Vec<_> = state_in
			.iter()
			.map(|&id| witness.get::<F>(id).unwrap().as_slice::<F>())
			.collect();
		let output_data: Vec<_> = out
			.iter()
			.map(|&id| witness.get::<F>(id).unwrap().as_slice::<F>())
			.collect();

		let mut tmp = vec![F::ZERO; 2 * l];
		for z in 0..rows {
			for i in 0..2 * l {
				tmp[i] = input_data[i][z];
			}
			plain_permutation(&mut tmp, params);
			for i in 0..2 * l {
				assert_eq!(tmp[i], output_data[i][z]);
			}
		}
	}

	Ok(out)
}
