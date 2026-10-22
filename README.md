# free-quantum

A strict formalization in Lean 4 / Mathlib of Πk, the free model of reversible
quantum computing from "Free quantum computing" (Carette et al., PNAS 2026),
with the two-qubit Quantum Schur Transform as a case study.

## Modules

| Module | Content |
|---|---|
| `FreeQuantum.Bipermutative` | Strict bipermutative categories (SI Definition S1) |
| `FreeQuantum.Discrete` | `Discrete ℕ` instance |
| `FreeQuantum.FinPerm` | `FinPerm`: permutations of `Fin n` |
| `FreeQuantum.Eucl` | `Eucl n = EuclideanSpace ℂ (Fin n)`, `BiEucl` |
| `FreeQuantum.FinLin` | `FinLin`: ℂ-linear maps `Eucl m → Eucl n` |
| `FreeQuantum.PiK` | `PiK k`: circuit terms modulo `Rel k` (Theorem 1, SI Proposition S5) |
| `FreeQuantum.Hadamard` | `H ≫ H = 𝟙` |
| `FreeQuantum.Model` | Soundness (SI Proposition S9), `stdModel` in `FinLin` |
| `FreeQuantum.Free` | Freeness: `Model k C ≃ BipermutativeFunctor (PiK k) C` |
| `FreeQuantum.QST2` | `QST₂ : 2 ◆ 2 ≅ 3 ◇ 1` and its correctness in `FinLin` |

## Build

```
lake exe cache get
lake build FreeQuantum
```
