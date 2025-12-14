use std::convert::TryInto;

use anyhow::Result;
use binius_core::oracle::OracleId;
use binius_field::BinaryField64b;

use crate::{
	anemoi_hash::{
		common::{anemoi_permutation, prep_params, AnemoiParams},
		params,
	},
	builder::ConstraintSystemBuilder,
};

const STATE_SIZE: usize = 12;

fn params_64_l6() -> AnemoiParams<BinaryField64b> {
	use params::params64_l6 as p;
	prep_params::<BinaryField64b, { p::L }, { p::ROUNDS }>(params::ALPHA_INV_64, &p::MDS, &p::C, &p::D)
}

pub fn permutation(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	state_in: [OracleId; STATE_SIZE],
) -> Result<[OracleId; STATE_SIZE]> {
	let params = params_64_l6();
	let out = anemoi_permutation::<BinaryField64b>(builder, log_size, &state_in, &params)?;
	Ok(out.try_into().expect("anemoi state size mismatch"))
}
