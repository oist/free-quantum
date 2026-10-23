import FreeQuantum.PiK.Basic
import Mathlib.Tactic

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory
open PiK

/-!
## `HH = id` in `Πk`

Carette et al. (2026), main text, "Reasoning". For `k ≥ 3`:
`ω := ζ ^ 2 ^ (k - 3)`, `S = 1 ◇ ω ^ 2`, `H := ω⁻¹ • (V ≫ S ≫ V)`.
`ω ^ 8 = 1`, so `ω⁻¹` is written `ω ^ 7` (as in SI Definition S10).
-/

variable {k : ℕ}

variable (k) in
def ω : Scalar (PiK k) := ζ k ^ 2 ^ (k - 3)

def H : (𝐈 ◇ 𝐈 : PiK k) ⟶ 𝐈 ◇ 𝐈 := ω k ^ 7 • (V ≫ S ≫ V)

theorem ω_pow_eight (hk : 3 ≤ k) : ω k ^ 8 = 1 := by
  rw [ω, ← pow_mul, show 8 = 2 ^ 3 by norm_num, ← pow_add, Nat.sub_add_cancel hk, ζ_pow_two_k]

theorem S_eq (hk : 3 ≤ k) : (S : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) = 𝟙 𝐈 ◇ₘ (ω k ^ 2) := by
  rw [S, ω, ← pow_mul, ← pow_succ]
  congr; omega

theorem S_X_S (hk : 3 ≤ k) :
    (S ≫ X ≫ S : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) = ω k ^ 2 • X := by
  rw [S_eq hk, X, ← addSwap_natural, reassoc_of% addHom_comp_addHom]
  simp only [Category.id_comp, Category.comp_id]
  rw [scalar_addHom_self, smul_id_comp]

theorem V_X_V : (V ≫ X ≫ V : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) = 𝟙 _ := by
  rw [← V_V, Category.assoc, V_V, reassoc_of% V_V, X, addSwap_addSwap]

theorem H_H (hk : 3 ≤ k) : (H ≫ H : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) = 𝟙 _ := by
  calc
    _ = ω k ^ 7 • ω k ^ 7 • (V ≫ S ≫ (V ≫ V) ≫ S ≫ V) := by
      rw [H, smul_comp, comp_smul]
      simp only [Category.assoc]
    _ = ω k ^ 7 • ω k ^ 7 • ω k ^ 2 • (V ≫ X ≫ V) := by
      rw [V_V, reassoc_of% (S_X_S hk), reassoc_of% comp_smul, smul_comp, Category.assoc]
    _ = 𝟙 _ := by
      rw [V_X_V, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add]
      rw [show 7 + 7 + 2 = 8 * 2 by norm_num]
      rw [pow_mul, ω_pow_eight hk, one_pow, one_smul]

end FreeQuantum
