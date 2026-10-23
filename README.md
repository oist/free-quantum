# free-quantum

A strict formalization in Lean 4 / Mathlib of Πk, the free model of reversible
quantum computing from "Free quantum computing" (Carette et al., PNAS 2026),
with the two-qubit Quantum Schur Transform as a case study.

## Modules

| Module | Content |
|---|---|
| `FreeQuantum.Extra.{Nat,Fin,Complex,ZMod}` | Project-independent lemmas on Mathlib types |
| `FreeQuantum.Bipermutative.Basic` | Strict bipermutative categories (SI Definition S1) |
| `FreeQuantum.Bipermutative.Functor` | `BipermutativeFunctor`: strict bipermutative functors |
| `FreeQuantum.Bipermutative.Instances.Discrete` | `Discrete ℕ` instance |
| `FreeQuantum.Bipermutative.Instances.FinPerm` | `FinPerm`: permutations of `Fin n` |
| `FreeQuantum.Bipermutative.Instances.Eucl` | `Eucl n = EuclideanSpace ℂ (Fin n)`, `BiEucl` |
| `FreeQuantum.Bipermutative.Instances.FinLin` | `FinLin`: ℂ-linear maps `Eucl m → Eucl n` |
| `FreeQuantum.PiK.Basic` | `PiK k`: circuit terms modulo `Rel k` (Theorem 1, SI Proposition S5) |
| `FreeQuantum.PiK.Model` | Models of `Πk` and soundness (SI Proposition S9) |
| `FreeQuantum.PiK.StdModel` | `stdModel` in `FinLin`; non-triviality of `Πk` |
| `FreeQuantum.PiK.Free` | Freeness: `Model k C ≃ BipermutativeFunctor (PiK k) C` |
| `FreeQuantum.PiK.Hadamard` | `H ≫ H = 𝟙` |
| `FreeQuantum.Algorithms.QST2` | `QST₂ : 2 ◆ 2 ≅ 3 ◇ 1` and its correctness in `FinLin` |

## Build

```
lake exe cache get
lake build FreeQuantum
```
