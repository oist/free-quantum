# free-quantum

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24547865.svg)](https://doi.org/10.5281/zenodo.24547865)

A strict formalization in Lean 4 / Mathlib of Πk, the free model of reversible
quantum computing from "Free quantum computing" (Carette et al., PNAS 2026),
with the two-qubit Quantum Schur Transform as a case study.

## Modules

| Module | Content |
|---|---|
| `FreeQuantum.Extra.{Nat,Fin,Complex,ZMod}` | Project-independent lemmas on Mathlib types |
| `FreeQuantum.Eucl` | `Eucl n = EuclideanSpace ℂ (Fin n)`, `perm`, `sumEquiv`, `prodEquiv` |
| `FreeQuantum.Bipermutative.Basic` | Strict bipermutative categories (SI Definition S1) |
| `FreeQuantum.Bipermutative.Functor` | `BipermutativeFunctor`: strict bipermutative functors |
| `FreeQuantum.Bipermutative.Instances.Discrete` | `Discrete ℕ` instance |
| `FreeQuantum.Bipermutative.Instances.FinPerm` | `FinPerm`: permutations of `Fin n` |
| `FreeQuantum.Bipermutative.Instances.FinLin` | `FinLin`: ℂ-linear maps `Eucl m → Eucl n` |
| `FreeQuantum.PiK.Basic` | `PiK k`: circuit terms modulo `Rel k` (Theorem 1, SI Proposition S5) |
| `FreeQuantum.PiK.Model` | Models of `Πk` and soundness (universal property of SI Proposition S5) |
| `FreeQuantum.PiK.StdModel` | `stdModel` in `FinLin` (SI Proposition S9); non-triviality of `Πk` |
| `FreeQuantum.PiK.Free` | Freeness: `Model k C ≃ BipermutativeFunctor (PiK k) C` |
| `FreeQuantum.PiK.Hadamard` | `H ≫ H = 𝟙` |
| `FreeQuantum.PiK.FinPermModel` | No model of `Πk` in `FinPerm` |
| `FreeQuantum.PiK.DiscreteNatModel` | `Model k DiscreteNat` is unique (the trivial model) |
| `FreeQuantum.Algorithms.QST2` | `QST₂ : 2 ◆ 2 ≅ 3 ◇ 1` and its correctness in `FinLin` |

## Build

```
lake exe cache get
lake build FreeQuantum
```

## License

Copyright 2026 Okinawa Institute of Science and Technology. Licensed under Apache 2.0; see [LICENSE](LICENSE).
