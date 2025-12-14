use std::convert::TryInto;

use anyhow::Result;
use binius_core::oracle::OracleId;
use binius_field::BinaryField32b;

use crate::{
	anemoi_hash::{
		common::{anemoi_permutation, prep_params, AnemoiParams},
		params,
	},
	builder::ConstraintSystemBuilder,
};

const STATE_SIZE: usize = 24;

fn params_32_l12() -> AnemoiParams<BinaryField32b> {
	use params::params32_l12 as p;
	prep_params::<BinaryField32b, { p::L }, { p::ROUNDS }>(params::ALPHA_INV_32, &p::MDS, &p::C, &p::D)
}

pub fn permutation(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	state_in: [OracleId; STATE_SIZE],
) -> Result<[OracleId; STATE_SIZE]> {
	let params = params_32_l12();
	let out = anemoi_permutation::<BinaryField32b>(builder, log_size, &state_in, &params)?;
	Ok(out.try_into().expect("anemoi state size mismatch"))
}
