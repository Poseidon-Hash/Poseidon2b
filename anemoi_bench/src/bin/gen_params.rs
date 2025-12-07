//Compute Anemoi parameters.


#[path = "../anemoi_gen.rs"]
mod anemoi_gen;

use anemoi_gen::{compute_params, FieldConst, FieldOps};
use binius_field::{
    BinaryField, BinaryField128b, BinaryField32b, BinaryField64b, PackedField,
    underlier::WithUnderlier,
};
use std::fmt::Debug;

macro_rules! impl_field_ops {
    ($ty:ty, $raw:ty) => {
        impl FieldOps for $ty {
            #[inline(always)]
            fn add(self, rhs: Self) -> Self { self + rhs }
            #[inline(always)]
            fn mul(self, rhs: Self) -> Self { self * rhs }
            #[inline(always)]
            fn safe_square(self) -> Self { self.square() }
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


const PI0_32: u32 = 0xb559_eff7;
const PI1_32: u32 = 0x9ac6_c074;
const PI0_64: u64 = 0x944c_e62e_b559_eff7;
const PI1_64: u64 = 0xdf30_73d3_9ac6_c074;
const PI0_128: u128 = 0x7464_2e34_fa54_06ba_944c_e62e_b559_eff7;
const PI1_128: u128 = 0x28e9_55fd_ff9b_d7e6_df30_73d3_9ac6_c074;

fn print_params<F>(name: &str, t: usize, pi0: F::Raw, pi1: F::Raw)
where
    F: FieldConst + FieldOps + BinaryField + Debug + WithUnderlier,
{
    let p = compute_params::<F>(t, pi0, pi1);
    println!("== {} ==", name);
    println!("t={} l={} rounds={}", t, p.l, p.rounds);
    println!("mds:");
    for row in p.mds.iter() {
        println!("{:?}", row.iter().map(|v| v.to_underlier()).collect::<Vec<_>>());
    }
    println!("c:");
    for row in p.c.iter() {
        println!("{:?}", row.iter().map(|v| v.to_underlier()).collect::<Vec<_>>());
    }
    println!("d:");
    for row in p.d.iter() {
        println!("{:?}", row.iter().map(|v| v.to_underlier()).collect::<Vec<_>>());
    }
}

fn main() {
    
    print_params::<BinaryField128b>("GF(2^128) t=4", 4, PI0_128, PI1_128); // l=2
    print_params::<BinaryField128b>("GF(2^128) t=6", 6, PI0_128, PI1_128); // l=3
    print_params::<BinaryField64b>("GF(2^64) t=8", 8, PI0_64, PI1_64); // l=4
    print_params::<BinaryField64b>("GF(2^64) t=12", 12, PI0_64, PI1_64); // l=6
    print_params::<BinaryField32b>("GF(2^32) t=16", 16, PI0_32, PI1_32); // l=8
    print_params::<BinaryField32b>("GF(2^32) t=24", 24, PI0_32, PI1_32); // l=12
}
