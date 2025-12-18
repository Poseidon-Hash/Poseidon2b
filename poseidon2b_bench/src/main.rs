mod params;

use binius_field::{
    BinaryField128b, BinaryField32b, BinaryField64b, Field, PackedField,
};
use std::fmt::Debug;
use std::time::Instant;


pub trait FieldOps:
    'static + Copy + Clone + Debug + Default + PartialEq + Send + Sync
{
    fn add(self, rhs: Self) -> Self;
    fn mul(self, rhs: Self) -> Self;
    fn safe_square(self) -> Self;
    fn inv(self) -> Self;
    fn from_u8(v: u8) -> Self;
    fn pow_alpha(self) -> Self {
        let x2 = self.safe_square();
        let x4 = x2.safe_square();
        self.mul(x2).mul(x4) // x^7
    }
}

// Allows populating constants from "native representation" (consistent with the tower basis in binius_field).
pub trait FieldConst: FieldOps {
    type Raw: Copy;
    fn from_raw(v: Self::Raw) -> Self;
}

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
            fn inv(self) -> Self { Field::invert(&self).unwrap() }
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


// Poseidon2b parameter structure

struct PreparedParams<F: FieldConst> {
    t: usize,
    rf: usize,
    rp: usize,
    rc: Vec<Vec<F>>,
    mds_full: Vec<Vec<F>>,
    mds_partial: Vec<Vec<F>>,
}

struct MdsFullFast<F: FieldConst> {
    k: usize,
    x_plus_one: F,
}

impl<F: FieldConst> MdsFullFast<F> {
    fn new(mds_full: &[Vec<F>], t: usize) -> Option<Self> {
        if t < 8 || t % 4 != 0 {
            return None;
        }

        // extract X for C from the ratio of the upper-left block to the upper-right M4
        // (mds_full[r][c] / mds_full[r][c + 4]);

        let k = t / 4;
        let mut x = None;
        'find_x: for r in 0..4 {
            for c in 0..4 {
                let m = mds_full[r][c + 4];
                if m != F::default() {
                    x = Some(mds_full[r][c].mul(m.inv()));
                    break 'find_x;
                }
            }
        }

        let x = x?;
        let x_plus_one = x.add(F::from_u8(1));
        Some(Self { k, x_plus_one })
    }
}

fn prep_params<F: FieldConst, const T: usize, const R: usize>(
    rc_raw: &[[F::Raw; R]; T],
    mds_full_raw: &[[F::Raw; T]; T],
    mds_partial_raw: &[[F::Raw; T]; T],
    rf: usize,
    rp: usize,
) -> PreparedParams<F> {
    PreparedParams {
        t: T,
        rf,
        rp,
        rc: rc_raw
            .iter()
            .map(|row| row.iter().copied().map(F::from_raw).collect())
            .collect(),
        mds_full: mds_full_raw
            .iter()
            .map(|row| row.iter().copied().map(F::from_raw).collect())
            .collect(),
        mds_partial: mds_partial_raw
            .iter()
            .map(|row| row.iter().copied().map(F::from_raw).collect())
            .collect(),
    }
}

// 6 instance parameters (directly reusing tables from binius_poseidon2b/hades)
fn params_32_t16() -> PreparedParams<BinaryField32b> {
    use params::params32_t16 as p;
    prep_params(
        &p::RC,
        &p::MDS_FULL,
        &p::MDS_PARTIAL,
        p::R_F,
        p::R_P,
    )
}
fn params_32_t24() -> PreparedParams<BinaryField32b> {
    use params::params32_t24 as p;
    prep_params(
        &p::RC,
        &p::MDS_FULL,
        &p::MDS_PARTIAL,
        p::R_F,
        p::R_P,
    )
}
fn params_64_t8() -> PreparedParams<BinaryField64b> {
    use params::params64_t8 as p;
    prep_params(
        &p::RC,
        &p::MDS_FULL,
        &p::MDS_PARTIAL,
        p::R_F,
        p::R_P,
    )
}
fn params_64_t12() -> PreparedParams<BinaryField64b> {
    use params::params64_t12 as p;
    prep_params(
        &p::RC,
        &p::MDS_FULL,
        &p::MDS_PARTIAL,
        p::R_F,
        p::R_P,
    )
}
fn params_128_t4() -> PreparedParams<BinaryField128b> {
    use params::params128_t4 as p;
    prep_params(
        &p::RC,
        &p::MDS_FULL,
        &p::MDS_PARTIAL,
        p::R_F,
        p::R_P,
    )
}
fn params_128_t6() -> PreparedParams<BinaryField128b> {
    use params::params128_t6 as p;
    prep_params(
        &p::RC,
        &p::MDS_FULL,
        &p::MDS_PARTIAL,
        p::R_F,
        p::R_P,
    )
}


// Poseidon2b Permutation

struct Poseidon2b<F: FieldConst> {
    t: usize,
    rf: usize,
    rp: usize,
    rc: Vec<Vec<F>>,
    mds_full: Vec<Vec<F>>,
    mds_partial: Vec<Vec<F>>,
    mds_full_fast: Option<MdsFullFast<F>>,
}

impl<F: FieldConst> Poseidon2b<F> {
    fn new(params: PreparedParams<F>) -> Self {
        let mds_full_fast = MdsFullFast::new(&params.mds_full, params.t);
        Self {
            t: params.t,
            rf: params.rf,
            rp: params.rp,
            rc: params.rc,
            mds_full: params.mds_full,
            mds_partial: params.mds_partial,
            mds_full_fast,
        }
    }

    fn permute(&self, state: &mut [F]) {
        debug_assert_eq!(state.len(), self.t);
        let half_f = self.rf / 2;
        let mut round = 0usize;

        // Minit = MDS_FULL
        self.mul_mds_full(state);

        // First half of full rounds
        for _ in 0..half_f {
            self.round_full(state, round);
            round += 1;
        }

        // Partial rounds
        for _ in 0..self.rp {
            self.round_partial(state, round);
            round += 1;
        }

        // Second half of full rounds
        for _ in 0..half_f {
            self.round_full(state, round);
            round += 1;
        }
    }

    #[inline(always)]
    fn round_full(&self, state: &mut [F], r: usize) {
        for i in 0..self.t {
            state[i] = state[i].add(self.rc[i][r]);
        }
        for x in state.iter_mut() {
            *x = x.pow_alpha();
        }
        self.mul_mds_full(state);
    }

    #[inline(always)]
    fn round_partial(&self, state: &mut [F], r: usize) {
        state[0] = state[0].add(self.rc[0][r]);
        state[0] = state[0].pow_alpha();
        self.mul_mds_partial(state);
    }

    fn mul_mds_full(&self, state: &mut [F]) {
        // t=4: fast algorithm using the ((A B),(B,A)) structure of M4（12 times muls over GF instead of naive 16 times muls over GF）
        if self.t == 4 {
            // 2x2 decomposition for M4 
            let x0 = state[0];
            let x1 = state[1];
            let x2 = state[2];
            let x3 = state[3];

            let a00 = self.mds_full[0][0];
            let a01 = self.mds_full[0][1];
            let a10 = self.mds_full[1][0];
            let a11 = self.mds_full[1][1];

            let b00 = self.mds_full[0][2];
            let b01 = self.mds_full[0][3];
            let b10 = self.mds_full[1][2];
            let b11 = self.mds_full[1][3];

            // 3 block multiplications：
            // P1 = A * x1, P2 = B * x2, P3 = (A+B)*(x1+x2); y1 = P1+P2, y2 = P3+y1
            let s0 = x0.add(x2);
            let s1 = x1.add(x3);

            let p1_0 = a00.mul(x0).add(a01.mul(x1));
            let p1_1 = a10.mul(x0).add(a11.mul(x1));

            let p2_0 = b00.mul(x2).add(b01.mul(x3));
            let p2_1 = b10.mul(x2).add(b11.mul(x3));

            let ab00 = a00.add(b00);
            let ab01 = a01.add(b01);
            let ab10 = a10.add(b10);
            let ab11 = a11.add(b11);

            let p3_0 = ab00.mul(s0).add(ab01.mul(s1));
            let p3_1 = ab10.mul(s0).add(ab11.mul(s1));

            let y0 = p1_0.add(p2_0);
            let y1 = p1_1.add(p2_1);
            let y2 = p3_0.add(y0);
            let y3 = p3_1.add(y1);

            state[0] = y0;
            state[1] = y1;
            state[2] = y2;
            state[3] = y3;
            return;
        }

        if self.t == 6 {

            // t=6: naive O(n^2) matrix multiplication

            let mut res = vec![F::default(); self.t];
            for (r, row) in self.mds_full.iter().enumerate() {
                let mut acc = F::default();
                for c in 0..self.t {
                    acc = acc.add(row[c].mul(state[c]));
                }
                res[r] = acc;
            }
            state.copy_from_slice(&res);
            return;
        }

        if matches!(self.t, 8 | 12 | 16 | 24) {

            // t=8/12/16/24: use a MDS_FULL algorithm expoiting its special structure of C⊗M4

            let fast = self.mds_full_fast.as_ref().expect("mds_full_fast missing");
            let mut tmp = vec![F::default(); self.t];
            let mut sum = [F::default(); 4];

            // apply M4 to each 4-element block and accumulate by row
            // reuse the ((A B),(B,A)) structure of M4

            let a00 = self.mds_full[0][4];
            let a01 = self.mds_full[0][5];
            let a10 = self.mds_full[1][4];
            let a11 = self.mds_full[1][5];

            let b00 = self.mds_full[0][6];
            let b01 = self.mds_full[0][7];
            let b10 = self.mds_full[1][6];
            let b11 = self.mds_full[1][7];

            for block in 0..fast.k {
                let base = block * 4;
                let x0 = state[base];
                let x1 = state[base + 1];
                let x2 = state[base + 2];
                let x3 = state[base + 3];

                // 3 block-mults: P1=A*x1, P2=B*x2, P3=(A+B)*(x1+x2); y1=P1+P2, y2=P3+y1
                let s0 = x0.add(x2);
                let s1 = x1.add(x3);

                let p1_0 = a00.mul(x0).add(a01.mul(x1));
                let p1_1 = a10.mul(x0).add(a11.mul(x1));

                let p2_0 = b00.mul(x2).add(b01.mul(x3));
                let p2_1 = b10.mul(x2).add(b11.mul(x3));

                let ab00 = a00.add(b00);
                let ab01 = a01.add(b01);
                let ab10 = a10.add(b10);
                let ab11 = a11.add(b11);

                let p3_0 = ab00.mul(s0).add(ab01.mul(s1));
                let p3_1 = ab10.mul(s0).add(ab11.mul(s1));

                let y0 = p1_0.add(p2_0);
                let y1 = p1_1.add(p2_1);
                let y2 = p3_0.add(y0);
                let y3 = p3_1.add(y1);

                tmp[base] = y0;
                tmp[base + 1] = y1;
                tmp[base + 2] = y2;
                tmp[base + 3] = y3;
                sum[0] = sum[0].add(y0);
                sum[1] = sum[1].add(y1);
                sum[2] = sum[2].add(y2);
                sum[3] = sum[3].add(y3);
            }

            // combine results using C = (X-1)I + J, where J is all-ones matrix

            for block in 0..fast.k {
                let base = block * 4;
                for i in 0..4 {
                    state[base + i] = sum[i].add(tmp[base + i].mul(fast.x_plus_one));
                }
            }
            return;
        }

        // Other t: naive O(n^2) matrix multiplication

        let mut res = vec![F::default(); self.t];
        for (r, row) in self.mds_full.iter().enumerate() {
            let mut acc = F::default();
            for c in 0..self.t {
                acc = acc.add(row[c].mul(state[c]));
            }
            res[r] = acc;
        }
        state.copy_from_slice(&res);
    }

    //$$y_i = (\mu_i - 1)x_i + \sum_{j=0}^{t-1} x_j$$
    
    fn mul_mds_partial(&self, state: &mut [F]) {
        let mut sum = F::default();
        for &x in state.iter() {
            sum = sum.add(x);
        }
        for i in 0..self.t {
            let mu = self.mds_partial[i][i];
            let mu_minus_one = mu.add(F::from_u8(1));
            state[i] = sum.add(mu_minus_one.mul(state[i]));
        }
    }
}


// Benchmark


fn run_poseidon_bench<F: FieldConst>(title: &str, params: PreparedParams<F>) {
    println!("--------------------------------------------------");
    println!(
        "{} | t={} | rf={} | rp={}",
        title, params.t, params.rf, params.rp
    );

    let poseidon = Poseidon2b::new(params);

    let mut state: Vec<F> = (0..poseidon.t)
        .map(|i| F::from_u8((i as u8).wrapping_add(1)))
        .collect();

    let base_iter = 100000usize;
    // Calculate a scaling factor based on state size 't'.
    // Larger states (larger 't') are slower, so we reduce iterations to keep runtime reasonable.
    let scale = (poseidon.t / 4).max(1);
    // Ensure we run at least 20,000 iterations for statistical significance.
    let iterations = (base_iter / scale).max(20_000);

    let start = Instant::now();
    for _ in 0..iterations {
        poseidon.permute(&mut state);
    }
    let elapsed = start.elapsed();
    let ns_per_op = elapsed.as_nanos() as f64 / iterations as f64;
    let ops_per_sec = iterations as f64 / elapsed.as_secs_f64();

    println!("Time per perm: {:.2} ns", ns_per_op);
    println!("Throughput:    {:.2} perms/sec", ops_per_sec);
    
}

fn main() {
    println!("=== Poseidon2b Benchmark ===");

    run_poseidon_bench("GF(2^32) t=16 (Poseidon2b)", params_32_t16());
    run_poseidon_bench("GF(2^32) t=24 (Poseidon2b)", params_32_t24());
    run_poseidon_bench("GF(2^64) t=8 (Poseidon2b)", params_64_t8());
    run_poseidon_bench("GF(2^64) t=12 (Poseidon2b)", params_64_t12());
    run_poseidon_bench("GF(2^128) t=4 (Poseidon2b)", params_128_t4());
    run_poseidon_bench("GF(2^128) t=6 (Poseidon2b)", params_128_t6());
}
