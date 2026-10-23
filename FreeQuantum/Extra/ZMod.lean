import FreeQuantum.Extra.Complex
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Values of `ZMod.stdAddChar`

`𝛘` is notation for `ZMod.stdAddChar`, scoped in `FourierTransform`.
-/

scoped [FourierTransform] notation "𝛘" => ZMod.stdAddChar

open scoped Real -- π
open scoped FourierTransform -- 𝛘
open Complex (I)

namespace ZMod

theorem stdAddChar_one_pow (N j : ℕ) [NeZero N] : 𝛘 (1 : ZMod N) ^ j = 𝛘 (j : ZMod N) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_one]

theorem stdAddChar_two_pow_sub_two {k : ℕ} (hk : 2 ≤ k) :
    𝛘 ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) = I := by
  rw [show ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) = ((2 ^ (k - 2) : ℤ) : ZMod (2 ^ k)) by norm_cast,
    stdAddChar_coe]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  conv_rhs => rw [← Complex.exp_pi_div_two_mul_I]
  congr 1; push_cast; simp [pow_add]; field_simp

theorem stdAddChar_two_pow_sub_three {k : ℕ} (hk : 3 ≤ k) :
    𝛘 ((2 ^ (k - 3) : ℕ) : ZMod (2 ^ k)) = (1 + I) / √2 := by
  rw [show ((_ : ℕ) : ZMod (2 ^ k)) = ((2 ^ (k - 3) : ℤ) : ZMod (2 ^ k)) by norm_cast,
    stdAddChar_coe]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  conv_rhs => rw [← Complex.exp_pi_div_four_mul_I]
  rw [add_tsub_cancel_left, pow_add]
  congr 1; push_cast; field_simp; norm_num

end ZMod
