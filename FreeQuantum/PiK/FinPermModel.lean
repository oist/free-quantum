import FreeQuantum.Bipermutative.Instances.FinPerm
import FreeQuantum.PiK.Model
import Mathlib.Tactic

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory

/-!
## No model of `Πk` in `FinPerm`

Every endomorphism of `𝐈 ◇ 𝐈` in `FinPerm` is an involution, while `σ_◇ 𝐈 𝐈` is not the identity,
so no `V` satisfies `V ≫ V = σ_◇ 𝐈 𝐈`.

- `FinPerm.comp_self_of_two`: `f ≫ f = 𝟙 _` for every `f : 𝐈 ◇ 𝐈 ⟶ 𝐈 ◇ 𝐈`.
- `FinPerm.addSwap_one_one_ne_id`: `σ_◇ 𝐈 𝐈 ≠ 𝟙 _`.
- `FinPerm.isEmpty_model`: `Model k FinPerm` is empty.
-/

namespace FinPerm

theorem comp_self_of_two (f : (𝐈 ◇ 𝐈 : FinPerm) ⟶ 𝐈 ◇ 𝐈) : f ≫ f = 𝟙 _ := by
  have : ∀ (e : Equiv.Perm (Fin 2)), e.trans e = Equiv.refl _ := by decide
  exact this f

theorem addSwap_one_one_ne_id : σ_◇ (𝐈 : FinPerm) 𝐈 ≠ 𝟙 _ := by
  intro h
  replace h := congrArg (fun f ↦ toEquiv f 0) h
  conv at h =>
    rw [show (0 : Fin 2) = (0 : Fin 1).castAdd 1 by rfl]
    erw [toEquiv_addSwap_castAdd]
    simp
  exact h

theorem isEmpty_model (k : ℕ) : IsEmpty (Model k FinPerm) := by
  constructor
  intro M
  have := M.V_V
  rw [comp_self_of_two] at this
  exact addSwap_one_one_ne_id this.symm

end FinPerm

end FreeQuantum
