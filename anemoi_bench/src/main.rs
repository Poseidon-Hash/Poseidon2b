mod anemoi_gen;
mod params;

use anemoi_gen::{FieldConst, FieldOps, ANEMOI_ALPHA};
use binius_field::{
    BinaryField, BinaryField128b, BinaryField32b, BinaryField64b, PackedField,
};
use params::{ALPHA_INV_128, ALPHA_INV_32, ALPHA_INV_64};
use std::time::Instant;



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

#[inline(always)]
fn pow_const<F: FieldOps>(mut base: F, mut exp: u128) -> F {
    let mut acc = F::from_u8(1);
    while exp > 0 {
        if exp & 1 == 1 {
            acc = acc.mul(base);
        }
        base = base.safe_square();
        exp >>= 1;
    }
    acc
}


// Parameter preparation 

struct PreparedParams<F: FieldConst> {
    t: usize,
    l: usize,
    rounds: usize,
    alpha_inv: u128,
    beta: F,
    delta: F,
    c: Vec<Vec<F>>,
    d: Vec<Vec<F>>,
    mds: Vec<Vec<F>>,
}

fn prep_params<F: FieldConst + BinaryField, const L: usize, const R: usize>(
    alpha_inv: u128,
    mds_raw: &[[F::Raw; L]; L],
    c_raw: &[[F::Raw; L]; R],
    d_raw: &[[F::Raw; L]; R],
) -> PreparedParams<F> {
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
    PreparedParams {
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

fn params_32_l8() -> PreparedParams<BinaryField32b> {
    use params::params32_l8 as p;
    prep_params::<BinaryField32b, { p::L }, { p::ROUNDS }>(
        ALPHA_INV_32,
        &p::MDS, 
        &p::C, 
        &p::D
    )
}

fn params_32_l12() -> PreparedParams<BinaryField32b> {
    use params::params32_l12 as p;
    prep_params::<BinaryField32b, { p::L }, { p::ROUNDS }>(
        ALPHA_INV_32, 
        &p::MDS, 
        &p::C, 
        &p::D
    )
}

fn params_64_l4() -> PreparedParams<BinaryField64b> {
    use params::params64_l4 as p;
    prep_params::<BinaryField64b, { p::L }, { p::ROUNDS }>(
        ALPHA_INV_64,
        &p::MDS,
        &p::C,
        &p::D,
    )
}

fn params_64_l6() -> PreparedParams<BinaryField64b> {
    use params::params64_l6 as p;
    prep_params::<BinaryField64b, { p::L }, { p::ROUNDS }>(
        ALPHA_INV_64,
        &p::MDS,
        &p::C,
        &p::D,
    )
}

fn params_128_l2() -> PreparedParams<BinaryField128b> {
    use params::params128_l2 as p;
    prep_params::<BinaryField128b, { p::L }, { p::ROUNDS }>(
        ALPHA_INV_128,
        &p::MDS,
        &p::C,
        &p::D,
    )
}

fn params_128_l3() -> PreparedParams<BinaryField128b> {
    use params::params128_l3 as p;
    prep_params::<BinaryField128b, { p::L }, { p::ROUNDS }>(
        ALPHA_INV_128,
        &p::MDS,
        &p::C,
        &p::D,
    )
}

// Anemoi permutation

struct AnemoiParams<F: FieldConst> {
    l: usize,
    rounds: usize,
    alpha_inv: u128,
    beta: F,
    delta: F,
    c: Vec<Vec<F>>,
    d: Vec<Vec<F>>,
    mds: Vec<Vec<F>>,
}

impl<F: FieldConst> AnemoiParams<F> {
    fn from_prepared(p: PreparedParams<F>) -> Self {
        Self {
            l: p.l,
            rounds: p.rounds,
            alpha_inv: p.alpha_inv,
            beta: p.beta,
            delta: p.delta,
            c: p.c,
            d: p.d,
            mds: p.mds,
        }
    }
}

struct Anemoi<F: FieldConst> {
    params: AnemoiParams<F>,
}

impl<F: FieldConst> Anemoi<F> {
    fn new(params: AnemoiParams<F>) -> Self {
        Self { params }
    }

    //$$\text{Anemoi} = \mathcal{M} \circ R_{n_r-1} \circ ... \circ R_0$$
    fn permute(&self, state: &mut [F]) {
        debug_assert_eq!(state.len(), 2 * self.params.l);

        let l = self.params.l;
        let mut x: Vec<F> = state[..l].to_vec();
        let mut y: Vec<F> = state[l..].to_vec();

        for r in 0..self.params.rounds {
            for i in 0..l {
                x[i] = x[i].add(self.params.c[r][i]);
                y[i] = y[i].add(self.params.d[r][i]);
            }
            self.linear_layer(&mut x, &mut y);
            for i in 0..l {
                let (nx, ny) = self.apply_sbox(x[i], y[i]);
                x[i] = nx;
                y[i] = ny;
            }
        }

        self.apply_mds_only(&mut x, &mut y);

        state[..l].copy_from_slice(&x);
        state[l..].copy_from_slice(&y);
    }

    fn linear_layer(&self, x: &mut [F], y: &mut [F]) {
        let l = self.params.l;
        let mut new_x = vec![F::default(); l];
        let mut new_y = vec![F::default(); l];

        // M_x(X)
        for r in 0..l {
            let mut acc = F::default();
            for c in 0..l {
                acc = acc.add(self.params.mds[r][c].mul(x[c]));
            }
            new_x[r] = acc;
        }
        
        // M_y(Y) (including rotation rho) 
        let mut y_rot = vec![F::default(); l];
        for i in 0..l - 1 {
            y_rot[i] = y[i + 1];
        }
        y_rot[l - 1] = y[0];

        for r in 0..l {
            let mut acc = F::default();
            for c in 0..l {
                acc = acc.add(self.params.mds[r][c].mul(y_rot[c]));
            }
            new_y[r] = acc;
        }

        for i in 0..l {
            new_y[i] = new_y[i].add(new_x[i]);
            new_x[i] = new_x[i].add(new_y[i]);
        }

        x.copy_from_slice(&new_x);
        y.copy_from_slice(&new_y);
    }

    fn apply_mds_only(&self, x: &mut [F], y: &mut [F]) {
        let l = self.params.l;
        let mut new_x = vec![F::default(); l];
        let mut new_y = vec![F::default(); l];

        // M_x(X)
        for r in 0..l {
            let mut acc = F::default();
            for c in 0..l {
                acc = acc.add(self.params.mds[r][c].mul(x[c]));
            }
            new_x[r] = acc;
        }

        // M_y(Y) (including rotation rho) 
        let mut y_rot = vec![F::default(); l];
        for i in 0..l - 1 {
            y_rot[i] = y[i + 1];
        }
        y_rot[l - 1] = y[0];

        for r in 0..l {
            let mut acc = F::default();
            for c in 0..l {
                acc = acc.add(self.params.mds[r][c].mul(y_rot[c]));
            }
            new_y[r] = acc;
        }

        x.copy_from_slice(&new_x);
        y.copy_from_slice(&new_y);
    }

    fn apply_sbox(&self, x: F, y: F) -> (F, F) {
        let mut x = x;
        let mut y = y;

        let y_pow = pow_const(y, ANEMOI_ALPHA as u128);

        //$x \leftarrow x + g \cdot y^\alpha + \mathbf{g^{-1}}$
        x = x.add(self.params.beta.mul(y_pow))
             .add(self.params.delta);

        //$y \leftarrow y + x^{1/\alpha}$
        let x_alpha_inv = pow_const(x, self.params.alpha_inv);
        y = y.add(x_alpha_inv);

        //$x \leftarrow x + g \cdot y^\alpha$
        let y_pow_new = pow_const(y, ANEMOI_ALPHA as u128);
        x = x.add(self.params.beta.mul(y_pow_new));

        (x, y)
    }
}

// Benchmark

fn run_anemoi_bench<F: FieldConst>(title: &str, pre: PreparedParams<F>) {
    let t = pre.t;
    let params = AnemoiParams::<F>::from_prepared(pre);

    println!("--------------------------------------------------");
    println!(
        "{} | t={} | l={} | rounds={} | alpha={} ",
        title, t, params.l, params.rounds, ANEMOI_ALPHA
    );

    let anemoi = Anemoi::new(params);

    let mut state: Vec<F> = (0..t)
        .map(|i| F::from_u8((i as u8).wrapping_add(1)))
        .collect();

    let base_iter = 100000usize;
    let scale = (t / 4).max(1);
    let iterations = (base_iter / scale).max(20_000);

    let start = Instant::now();
    for _ in 0..iterations {
        anemoi.permute(&mut state);
    }
    let elapsed = start.elapsed();
    let ns_per_op = elapsed.as_nanos() as f64 / iterations as f64;
    let ops_per_sec = iterations as f64 / elapsed.as_secs_f64();

    println!("Time per perm: {:.2} ns", ns_per_op);
    println!("Throughput:    {:.2} perms/sec", ops_per_sec);
 
}

fn main() {
    println!("=== Anemoi Benchmark  ===");

    run_anemoi_bench::<BinaryField32b>("GF(2^32) t=16 (Anemoi)", params_32_l8());
    run_anemoi_bench::<BinaryField32b>("GF(2^32) t=24 (Anemoi)", params_32_l12());
    run_anemoi_bench::<BinaryField64b>("GF(2^64) t=8  (Anemoi)", params_64_l4());
    run_anemoi_bench::<BinaryField64b>("GF(2^64) t=12 (Anemoi)", params_64_l6());
    run_anemoi_bench::<BinaryField128b>("GF(2^128) t=4 (Anemoi)", params_128_l2());
    run_anemoi_bench::<BinaryField128b>("GF(2^128) t=6 (Anemoi)", params_128_l3());
    
}
