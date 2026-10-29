import FreeQuantum.Bipermutative.Instances.Discrete
import FreeQuantum.PiK.Model
import Mathlib.Tactic

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory

/-!
## The model of `Πk` in `Discrete ℕ`

Strictness for `0`, `1` and `+` forces `natObj n = ⟨n⟩`, and every Hom-set is a subsingleton,
so `Discrete ℕ` has exactly one model, whose `ζ` and `V` are identities.

- `DiscreteNat.model k`: the model with `natObj n = ⟨n⟩`, `ζ = 𝟙 _`, `V = 𝟙 _`.
- `DiscreteNat.natObj_eq`: `M.natObj n = ⟨n⟩` for every model `M` in `Discrete ℕ`.
- `Unique (Model k DiscreteNat)`.
-/

namespace DiscreteNat

variable {k : ℕ}

variable (k) in
def model : Model k DiscreteNat where
  natObj n := ⟨n⟩
  natObj_zero := rfl
  natObj_one := rfl
  natObj_add _ _ := rfl
  natObj_mul _ _ := rfl
  ζ := 𝟙 _
  V := 𝟙 _
  V_V := Subsingleton.elim _ _
  V_S_V := Subsingleton.elim _ _
  ζ_pow_two_k := Subsingleton.elim _ _

theorem natObj_eq (M : Model k DiscreteNat) (n : ℕ) : M.natObj n = ⟨n⟩ := by
  induction n with
  | zero => rw [M.natObj_zero]; rfl
  | succ n ih => rw [M.natObj_add, M.natObj_one, ih]; rfl

instance : Unique (Model k DiscreteNat) where
  default := model k
  uniq M := by
    ext n
    . rw [natObj_eq, natObj_eq]
    . exact Subsingleton.elim _ _
    . exact Subsingleton.elim _ _

end DiscreteNat

end FreeQuantum
