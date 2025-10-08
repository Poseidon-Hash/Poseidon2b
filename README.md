# Poseidon2b

This repository provides research and reference code for integrating the **Poseidon2b** hash function into the [Binius](https://gitlab.com/IrreducibleOSS/binius/) framework.

The project is organized into two main components with distinct licensing origins:

1. **`binius_poseidon2b/` folder** – Based on code from the [Binius project](https://gitlab.com/IrreducibleOSS/binius/), commit [`924103fe50a9767b03c61981a5df12dafc1f44bd`](https://gitlab.com/IrreducibleOSS/binius/-/tree/924103fe50a9767b03c61981a5df12dafc1f44bd). The code has been **adapted and extended** to support the **Poseidon2b** hash function. The original Binius code is licensed under the **Apache License, Version 2.0**, see [`binius_poseidon2b/LICENSE`](binius_poseidon2b/LICENSE) for the full license text.

2. **`sage-ref/` folder** – Contains original SageMath reference implementations and related research code. This code, along with all top-level files not otherwise specified, is released under the **MIT License** (see [LICENSE](LICENSE)).

If you redistribute or reuse this code, ensure compliance with both the  **Apache 2.0** and **MIT** license conditions as they apply to each component.

---
## Proof implementation in Binius

Extensions to the Binius project: 

- [`poseidon2b_circuit.rs`](binius_poseidon2b/examples/poseidon2b_circuit.rs) – Poseidon2b circuit implementation.
  
The instances can be run inside the `binius_poseidon2b/` folder with: 
```bash
cargo run --release --example poseidon2b -- --n 32 --t 16
```

The parameters n and t define the field sizes and state sizes and can be combined as defined in the parameter specification. 

Additionally, `--n-permutations` can be used to specify the number of permutations to verify.

The concrete proof implementations for each parameter set can be found in the circuits subfolder [`hades`](binius_poseidon2b/crates/circuits/src/hades/poseidon2b_x7_32_512.rs).

- [`run_benchmark.py`](binius_poseidon2b/scripts/run_benchmark.py) – Benchmark script including the Poseidon2b examples.

The code was developed and tested using `cargo 1.88.0-nightly` and `Python 3.10.12`.

### **Benchmark Results**

| Permutation              |  n  |  t  |  #Perm  | Proof size (KiB) | Proving time (s) (*single-threaded*) | Proving time (s) (*multi-threaded*) | Verify time (ms) (*single-threaded*) | Verify time (ms) (*multi-threaded*) |
|--------------------|----:|----:|--------:|-----------------:|--------------------------:|--------------------------:|---------------------------:|--------------------------:|
| Keccak-f           |  64 |  24 |  2¹³    |              438 |                     3.038 |                     0.425 |                     45.70 |                     46.59 |
| SHA-256            |  32 |  16 |  2¹⁴    |              701 |                     5.248 |                     1.383 |                    233.55 |                    235.30 |
| Groestl-P          |   8 |  64 |  2¹⁴    |              416 |                     0.495 |                     0.170 |                    114.97 |                    115.81 |
| Vision-32b         |  32 |  24 |  2¹⁴    |              560 |                     1.764 |                     0.605 |                     10.12 |                     10.60 |
| **Poseidon2b<sup>π</sup>** |  32 |  16 |  2¹⁴    |              402 |                 **0.400** |                 **0.148** |                      5.07 |                      5.15 |
| **Poseidon2b<sup>π</sup>** |  32 |  24 |  2¹⁴    |              471 |                     0.528 |                     0.211 |                      5.99 |                      6.15 |
| **Poseidon2b<sup>π</sup>** |  64 |   8 |  2¹⁴    |          **366** |                     0.485 |                     0.150 |                 **4.34** |                 **4.39** |
| **Poseidon2b<sup>π</sup>** |  64 |  12 |  2¹⁴    |              426 |                     0.760 |                     0.220 |                      4.79 |                      4.91 |
| **Poseidon2b<sup>π</sup>** | 128 |   4 |  2¹⁴    |              507 |                     2.642 |                     0.564 |                      6.24 |                      6.52 |
| **Poseidon2b<sup>π</sup>** | 128 |   6 |  2¹⁴    |              525 |                     2.916 |                     0.617 |                      6.56 |                      6.84 |

For Keccak-f, we prove 2¹³ permutation calls, which results in a hash size of 1.1 MB. For all other permutation functions, the hash output size is 1.049 MB for 2¹⁴ permutation invocations.

**Benchmark setup:**  
All performances were measured on an **AMD Ryzen 9 7900X** (12 cores). The Rust implementations were compiled and executed in **release mode** using:

```bash
RUSTFLAGS="-C target-cpu=native"
```

---
## Sage implementations

Contents:
- [`Poseidon2b.sage`](sage-ref/Poseidon2b.sage) – SageMath reference implementation of the Poseidon2b permutation.  
- [`Poseidon2b.ipynb`](sage-ref/Poseidon2b.ipynb) – Jupyter notebook demonstrating example usage, including the definition of Poseidon2b instances.  
- [`AlgebraicModels.ipynb`](sage-ref/AlgebraicModels.ipynb) – SageMath implementations of the algebraic models analyzed in the accompanying paper.

The code and notebooks were developed and tested using `SageMath 10.6` with `Python 3.12.5`. Using the same version is recommended to ensure compatibility.
