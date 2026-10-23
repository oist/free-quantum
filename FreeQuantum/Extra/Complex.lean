import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

open scoped Real -- π
open Complex (I)

namespace Complex

theorem exp_pi_div_four_mul_I : exp (π / 4 * I) = (1 + I) / √2 := by
  rw [exp_mul_I]
  norm_cast
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; field_simp; norm_cast
  rw [Real.sq_sqrt (by norm_num)]; norm_cast

end Complex
