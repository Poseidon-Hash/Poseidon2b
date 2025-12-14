use std::convert::TryInto;

use anyhow::Result;
use binius_core::oracle::OracleId;
use binius_field::BinaryField128b;

use crate::{
	anemoi_hash::{
		common::{anemoi_permutation, prep_params, AnemoiParams},
		params,
	},
	builder::ConstraintSystemBuilder,
};

const STATE_SIZE: usize = 6;

fn params_128_l3() -> AnemoiParams<BinaryField128b> {
	use params::params128_l3 as p;
	prep_params::<BinaryField128b, { p::L }, { p::ROUNDS }>(params::ALPHA_INV_128, &p::MDS, &p::C, &p::D)
}

pub fn permutation(
	builder: &mut ConstraintSystemBuilder,
	log_size: usize,
	state_in: [OracleId; STATE_SIZE],
) -> Result<[OracleId; STATE_SIZE]> {
	let params = params_128_l3();
	let out = anemoi_permutation::<BinaryField128b>(builder, log_size, &state_in, &params)?;
	Ok(out.try_into().expect("anemoi state size mismatch"))
}
