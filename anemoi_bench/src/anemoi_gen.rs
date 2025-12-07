//Define the functions to generate the parameters of Anemoi: estimate the number of rounds, search for a circulant MDS matrix,
//derive the round constants from the given $\pi_0/\pi_1$ and $\beta/\delta$, and wrap them into a parameter structure to return.

use binius_field::BinaryField;
use std::collections::HashMap;
use std::cmp::min;
use std::fmt::Debug;

pub trait FieldOps:
    'static + Copy + Clone + Debug + Default + PartialEq + Send + Sync
{
    fn add(self, rhs: Self) -> Self;
    fn mul(self, rhs: Self) -> Self;
    fn safe_square(self) -> Self;
    fn from_u8(v: u8) -> Self;
    fn pow_alpha(self) -> Self {
        let x2 = self.safe_square();
        let x4 = x2.safe_square();
        self.mul(x2).mul(x4) // x^7
    }
}

pub trait FieldConst: FieldOps {
    type Raw: Copy;
    fn from_raw(v: Self::Raw) -> Self;
}

pub const ANEMOI_ALPHA: u32 = 7;


#[allow(dead_code)]
pub fn estimate_rounds(alpha: u32, l: usize, security: usize) -> usize {
    let _kappa = match alpha {
        3 => 1,
        5 => 2,
        7 => 4,
        9 => 7,
        11 => 9,
        _ => panic!("unsupported alpha={}", alpha),
    };
    let mut r = 0usize;
    let log2_9 = 9f64.log2();
    loop {
        r += 1;
        let lr = (l * r) as f64;
        // For binary fields (q = 2^n): C_alg(r) = l*r * 9^(2*l*r); compare log2.
        let log_complexity = lr.log2() + (2 * l * r) as f64 * log2_9;
        if log_complexity >= security as f64 {
            break;
        }
    }
    r += 2 + min(5, l + 1);
    r.max(8)
}

#[allow(dead_code)]
fn combinations(n: usize, k: usize, start: usize, cur: &mut Vec<usize>, f: &mut impl FnMut(&[usize])) {
    if cur.len() == k {
        f(cur);
        return;
    }
    for i in start..n {
        cur.push(i);
        combinations(n, k, i + 1, cur, f);
        cur.pop();
    }
}

#[allow(dead_code)]
#[inline(always)]
fn mask_from_indices(indices: &[usize]) -> u16 {
    let mut mask = 0u16;
    for &i in indices {
        mask |= 1u16 << i;
    }
    mask
}

#[allow(dead_code)]
fn is_mds<F: FieldOps>(m: &[Vec<F>]) -> bool {
    let n = m.len();
    debug_assert!(n > 0 && m.iter().all(|row| row.len() == n));

    for row in m {
        for &v in row {
            if v == F::default() {
                return false;
            }
        }
    }

    let mut det_cache = HashMap::<(u16, u16), F>::new();
    for r in 0..n {
        for c in 0..n {
            det_cache.insert(((1u16 << r), (1u16 << c)), m[r][c]);
        }
    }

    let mut rows = Vec::new();
    let mut cols = Vec::new();

    for size in 2..=n {
        let mut new_det_cache = HashMap::<(u16, u16), F>::new();
        let mut ok = true;

        combinations(n, size, 0, &mut rows, &mut |row_idx| {
            combinations(n, size, 0, &mut cols, &mut |col_idx| {
                let row_mask_tail = mask_from_indices(&row_idx[1..]);
                let col_mask_full = mask_from_indices(col_idx);
                let mut det = F::default();
                let i = row_idx[0];
                for &c in col_idx {
                    let cofactor_key = (row_mask_tail, col_mask_full & !(1u16 << c));
                    let cofactor = det_cache
                        .get(&cofactor_key)
                        .expect("cofactor should exist for smaller minors");
                    det = det.add(m[i][c].mul(*cofactor));
                }
                if det == F::default() {
                    ok = false;
                    return;
                }
                new_det_cache.insert((mask_from_indices(row_idx), col_mask_full), det);
            });
        });

        if !ok || new_det_cache.is_empty() {
            return false;
        }
        det_cache = new_det_cache;
    }

    true
}

//Search for a circulant MDS matrix, used in the ``large-state'' setting (eprint 2022/840, Appendix~C, $l>4$). 
//The strategy is to enumerate the coefficients of the first row in lexicographic order, construct the corresponding circulant matrix,
//and return the first one that satisfies the MDS property.

#[allow(dead_code)]
fn build_circulant_mds<F: FieldOps + BinaryField>(l: usize) -> Vec<Vec<F>> {
   
    fn gen_vectors(
        l: usize,
        limit: usize,
        start: usize,
        cur: &mut Vec<usize>,
        f: &mut impl FnMut(&[usize]),
    ) {
        if cur.len() == l {
            f(cur);
            return;
        }
        for v in start..=limit {
            cur.push(v);
            gen_vectors(l, limit, v, cur, f);
            cur.pop();
        }
    }

    let mut limit = l + 1;
    let mut cur = Vec::with_capacity(l);
    loop {
        let mut found: Option<Vec<Vec<F>>> = None;
        gen_vectors(l, limit, 1, &mut cur, &mut |coeffs| {
            if found.is_some() {
                return;
            }
            let coeffs_f: Vec<F> = coeffs.iter().map(|&v| F::from_u8(v as u8)).collect();
            let mut m = vec![vec![F::default(); l]; l];
            for r in 0..l {
                for c in 0..l {
                    m[r][c] = coeffs_f[(c + l - r) % l];
                }
            }
            if is_mds(&m) {
                found = Some(m);
            }
        });
        if let Some(m) = found {
            return m;
        }
        limit += 1;
    }
}


#[allow(dead_code)]
pub fn build_mds_big<F: FieldOps + BinaryField>(l: usize) -> Vec<Vec<F>> {
    assert!(l > 4, "build_mds_big is intended for l>4 only");
    build_circulant_mds::<F>(l)
}

#[allow(dead_code)]
fn build_mds_small<F: FieldOps + BinaryField>(l: usize) -> Option<Vec<Vec<F>>> {
    if l < 2 || l > 4 {
        return None;
    }

    fn m2<F: FieldOps + BinaryField>(b: F) -> Vec<Vec<F>> {
        let mut mat = vec![vec![F::default(); 2]; 2];
        for col in 0..2 {
            let mut v = vec![F::default(); 2];
            v[col] = F::from_u8(1);
            v[0] = FieldOps::add(v[0], FieldOps::mul(b, v[1]));
            v[1] = FieldOps::add(v[1], FieldOps::mul(b, v[0]));
            mat[0][col] = v[0];
            mat[1][col] = v[1];
        }
        mat
    }

    fn m3<F: FieldOps + BinaryField>(b: F) -> Vec<Vec<F>> {
        let mut mat = vec![vec![F::default(); 3]; 3];
        for col in 0..3 {
            let mut v = vec![F::default(); 3];
            v[col] = F::from_u8(1);
            let t = FieldOps::add(v[0], FieldOps::mul(b, v[2]));
            v[2] = FieldOps::add(v[2], v[1]);
            v[2] = FieldOps::add(v[2], FieldOps::mul(b, v[0]));
            v[0] = FieldOps::add(t, v[2]);
            v[1] = FieldOps::add(v[1], t);
            for row in 0..3 {
                mat[row][col] = v[row];
            }
        }
        mat
    }

    fn m4<F: FieldOps + BinaryField>(b: F) -> Vec<Vec<F>> {
        let mut mat = vec![vec![F::default(); 4]; 4];
        for col in 0..4 {
            let mut v = vec![F::default(); 4];
            v[col] = F::from_u8(1);
            v[0] = FieldOps::add(v[0], v[1]);
            v[2] = FieldOps::add(v[2], v[3]);
            v[3] = FieldOps::add(v[3], FieldOps::mul(b, v[0]));
            v[1] = FieldOps::mul(b, FieldOps::add(v[1], v[2]));
            v[0] = FieldOps::add(v[0], v[1]);
            v[2] = FieldOps::add(v[2], FieldOps::mul(b, v[3]));
            v[1] = FieldOps::add(v[1], v[2]);
            v[3] = FieldOps::add(v[3], v[0]);
            for row in 0..4 {
                mat[row][col] = v[row];
            }
        }
        mat
    }

    let a = F::MULTIPLICATIVE_GENERATOR;
    let mut b = F::from_u8(1);
    for _ in 0..(l * 8 + 16) {
        b = FieldOps::mul(b, a);
        let m = match l {
            2 => m2(b),
            3 => m3(b),
            4 => m4(b),
            _ => unreachable!(),
        };
        if is_mds(&m) {
            return Some(m);
        }
    }
    None
}

#[allow(dead_code)]
pub fn build_constants<F: FieldOps + FieldConst + BinaryField>(
    l: usize,
    rounds: usize,
    pi0_raw: F::Raw,
    pi1_raw: F::Raw,
    beta: F,
    delta: F,
) -> (Vec<Vec<F>>, Vec<Vec<F>>) {
    let mut c = vec![vec![F::default(); l]; rounds];
    let mut d = vec![vec![F::default(); l]; rounds];

    let pi0 = F::from_raw(pi0_raw);
    let pi1 = F::from_raw(pi1_raw);

    let mut pi0_r = F::from_u8(1);
    for r in 0..rounds {
        let mut pi1_i = F::from_u8(1);
        for i in 0..l {
            let pow_alpha = FieldOps::add(pi0_r, pi1_i).pow_alpha();
            c[r][i] = FieldOps::add(FieldOps::mul(beta, pi0_r.safe_square()), pow_alpha);
            d[r][i] = FieldOps::add(
                FieldOps::mul(beta, pi1_i.safe_square()),
                FieldOps::add(pow_alpha, delta),
            );
            pi1_i = FieldOps::mul(pi1_i, pi1);
        }
        pi0_r = FieldOps::mul(pi0_r, pi0);
    }

    (c, d)
}

#[allow(dead_code)]
pub struct ComputedParams<F: FieldOps + FieldConst> {
    pub l: usize,
    pub rounds: usize,
    #[allow(dead_code)]
    pub beta: F,
    #[allow(dead_code)]
    pub delta: F,
    pub mds: Vec<Vec<F>>,
    pub c: Vec<Vec<F>>,
    pub d: Vec<Vec<F>>,
}

#[allow(dead_code)]
pub fn compute_params<F: FieldOps + FieldConst + BinaryField>(
    t: usize,
    pi0: F::Raw,
    pi1: F::Raw,
) -> ComputedParams<F> {
    assert_eq!(t % 2, 0, "Anemoi expects even state size (2l)");
    let l = t / 2;
    let rounds = match l {
        2 => 13,
        3 => 12,
        4 => 11,
        6 => 10,
        8 => 9,
        _ => estimate_rounds(ANEMOI_ALPHA, l, 128),
    };
    let beta = F::MULTIPLICATIVE_GENERATOR;
    let delta = beta.invert().expect("generator is non-zero");
    let mds = if let Some(precomputed) = build_mds_small::<F>(l) {
        precomputed
    } else if l > 4 {
        build_mds_big::<F>(l)
    } else {
        panic!("unsupported (t={}, l={}) for this field type", t, l);
    };
    let (c, d) = build_constants::<F>(l, rounds, pi0, pi1, beta, delta);

    ComputedParams {
        l,
        rounds,
        beta,
        delta,
        mds,
        c,
        d,
    }
    
}
