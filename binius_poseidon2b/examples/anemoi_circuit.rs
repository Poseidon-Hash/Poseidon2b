#![allow(deprecated)]

use std::array;

use anyhow::Result;
use binius_circuits::{
	anemoi_hash,
	builder::{ConstraintSystemBuilder, types::U},
};
use binius_core::{constraint_system, fiat_shamir::HasherChallenger, oracle::OracleId};
use binius_field::{BinaryField128b, BinaryField32b, BinaryField64b, tower::CanonicalTowerFamily};
use binius_hal::make_portable_backend;
use binius_hash::groestl::{Groestl256, Groestl256ByteCompression};
use binius_utils::{checked_arithmetics::log2_ceil_usize, rayon::adjust_thread_pool};
use bytesize::ByteSize;
use clap::{Parser, value_parser};
use tracing_profile::init_tracing;

#[derive(Debug, Parser)]
struct Args {
	/// The number of permutations to verify.
	#[arg(short, long, default_value_t = 256, value_parser = value_parser!(u32).range(0..))]
	n_permutations: u32,
	/// The negative binary logarithm of the Reed–Solomon code rate.
	#[arg(long, default_value_t = 1, value_parser = value_parser!(u32).range(1..))]
	log_inv_rate: u32,
	// field size in bit, supported are: 32, 64, 128
	#[arg(long, default_value_t = 32, value_parser = value_parser!(u32).range(32..129))]
	n: u32,
	// state size t
	#[arg(long, default_value_t = 16, value_parser = value_parser!(u32).range(4..25))]
	t: u32,
}

fn main() -> Result<()> {
	const SECURITY_BITS: usize = 100;

	adjust_thread_pool()
		.as_ref()
		.expect("failed to init thread pool");

	let args = Args::parse();

	let _guard = init_tracing().expect("failed to initialize tracing");

	println!("Verifying {} Anemoi permutations", args.n_permutations);

	let log_n_permutations = log2_ceil_usize(args.n_permutations as usize);

	let allocator = bumpalo::Bump::new();
	let mut builder = ConstraintSystemBuilder::new_with_witness(&allocator);

	let trace_gen_scope = tracing::info_span!("generating trace").entered();

	match args.n {
		32 => {
			if args.t == 16 {
				init_32_t16(&mut builder, log_n_permutations);
			} else if args.t == 24 {
				init_32_t24(&mut builder, log_n_permutations);
			} else {
				println!("Unsupported combination.");
			}
		}
		64 => {
			if args.t == 8 {
				init_64_t8(&mut builder, log_n_permutations);
			} else if args.t == 12 {
				init_64_t12(&mut builder, log_n_permutations);
			} else {
				println!("Unsupported combination.");
			}
		}
		128 => {
			if args.t == 4 {
				init_128_t4(&mut builder, log_n_permutations);
			} else if args.t == 6 {
				init_128_t6(&mut builder, log_n_permutations);
			} else {
				println!("Unsupported combination.");
			}
		}
		_ => println!("Unsupported combination."),
	}

	drop(trace_gen_scope);

	let witness = builder
		.take_witness()
		.expect("builder created with witness");
	let constraint_system = builder.build()?;

	let backend = make_portable_backend();

	let proof =
		constraint_system::prove::<
			U,
			CanonicalTowerFamily,
			Groestl256,
			Groestl256ByteCompression,
			HasherChallenger<Groestl256>,
			_,
		>(&constraint_system, args.log_inv_rate as usize, SECURITY_BITS, &[], witness, &backend)?;

	println!("Proof size: {}", ByteSize::b(proof.get_proof_size() as u64));

	constraint_system::verify::<
		U,
		CanonicalTowerFamily,
		Groestl256,
		Groestl256ByteCompression,
		HasherChallenger<Groestl256>,
	>(&constraint_system, args.log_inv_rate as usize, SECURITY_BITS, &[], proof)?;
	Ok(())
}

fn init_32_t16(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 16] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField32b>(
			&mut builder,
			format!("anemoi_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		anemoi_hash::anemoi_32_16::permutation(&mut builder, log_size, state_in);
}

fn init_32_t24(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 24] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField32b>(
			&mut builder,
			format!("anemoi_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		anemoi_hash::anemoi_32_24::permutation(&mut builder, log_size, state_in);
}

fn init_64_t8(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 8] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField64b>(
			&mut builder,
			format!("anemoi_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		anemoi_hash::anemoi_64_8::permutation(&mut builder, log_size, state_in);
}

fn init_64_t12(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 12] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField64b>(
			&mut builder,
			format!("anemoi_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		anemoi_hash::anemoi_64_12::permutation(&mut builder, log_size, state_in);
}

fn init_128_t4(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 4] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField128b>(
			&mut builder,
			format!("anemoi_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		anemoi_hash::anemoi_128_4::permutation(&mut builder, log_size, state_in);
}

fn init_128_t6(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 6] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField128b>(
			&mut builder,
			format!("anemoi_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		anemoi_hash::anemoi_128_6::permutation(&mut builder, log_size, state_in);
}
