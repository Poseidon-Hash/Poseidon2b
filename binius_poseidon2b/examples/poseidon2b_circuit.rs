// Copyright 2024-2025 Irreducible Inc.

//! Example of a Binius SNARK that proves execution of [Vision Mark-32] permutations.
//!
//! The arithmetization uses committed columns of 32-bit binary tower field elements. Every row of
//! the trace attests to the validity of 2 Vision rounds. Each permutation consists of 16 rounds.
//!
//! [Vision Mark-32]: https://eprint.iacr.org/2024/633

// Uses binius_circuits which is being phased out.
#![allow(deprecated)]

use std::{array, env, path::Path};

use anyhow::Result;
use binius_circuits::builder::{ConstraintSystemBuilder, types::U};
use binius_core::{constraint_system, fiat_shamir::HasherChallenger, oracle::OracleId};
use binius_field::{BinaryField32b, BinaryField64b, BinaryField128b, tower::CanonicalTowerFamily};
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
	#[arg(long, default_value_t = 24, value_parser = value_parser!(u32).range(4..25))]
	t: u32,
}

fn main() -> Result<()> {
	const SECURITY_BITS: usize = 100;

	adjust_thread_pool()
		.as_ref()
		.expect("failed to init thread pool");

	let args = Args::parse();

	let _guard = init_tracing().expect("failed to initialize tracing");

	println!("Verifying {} Poseidon2b permutations", args.n_permutations);

	let log_n_permutations = log2_ceil_usize(args.n_permutations as usize);

	let allocator = bumpalo::Bump::new();
	let mut builder = ConstraintSystemBuilder::new_with_witness(&allocator);

	let trace_gen_scope = tracing::info_span!("generating trace").entered();

	match args.n {
		32 => {
			if args.t == 16 {
				init_8x32_512(&mut builder, log_n_permutations);
			} else if args.t == 24 {
				init_8x32_768(&mut builder, log_n_permutations);
			} else {
				println!("Unsupported combination.");
			}
		}

		64 => {
			if args.t == 8 {
				init_8x64_512(&mut builder, log_n_permutations);
			} else if args.t == 12 {
				init_8x64_768(&mut builder, log_n_permutations);
			} else {
				println!("Unsupported combination.");
			}
		}
		128 => {
			if args.t == 4 {
				init_8x128_512(&mut builder, log_n_permutations);
			} else if args.t == 6 {
				init_8x128_768(&mut builder, log_n_permutations);
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

fn init_8x32_768(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 24] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField32b>(
			&mut builder,
			format!("p_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		binius_circuits::hades::poseidon2b_x7_32_768::permutation(&mut builder, log_size, state_in);
}

fn init_8x32_512(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 16] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField32b>(
			&mut builder,
			format!("p_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		binius_circuits::hades::poseidon2b_x7_32_512::permutation(&mut builder, log_size, state_in);
}
fn init_8x64_768(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 12] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField64b>(
			&mut builder,
			format!("p_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		binius_circuits::hades::poseidon2b_x7_64_768::permutation(&mut builder, log_size, state_in);
}

fn init_8x64_512(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 8] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField64b>(
			&mut builder,
			format!("p_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out =
		binius_circuits::hades::poseidon2b_x7_64_512::permutation(&mut builder, log_size, state_in);
}
fn init_8x128_768(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 6] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField128b>(
			&mut builder,
			format!("p_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out = binius_circuits::hades::poseidon2b_x7_128_768::permutation(
		&mut builder,
		log_size,
		state_in,
	);
}
fn init_8x128_512(mut builder: &mut ConstraintSystemBuilder, log_size: usize) {
	let state_in: [OracleId; 4] = array::from_fn(|i| {
		binius_circuits::unconstrained::unconstrained::<BinaryField128b>(
			&mut builder,
			format!("p_in_{i}"),
			log_size,
		)
		.unwrap()
	});
	let _state_out = binius_circuits::hades::poseidon2b_x7_128_512::permutation(
		&mut builder,
		log_size,
		state_in,
	);
}
