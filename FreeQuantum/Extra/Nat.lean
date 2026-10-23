import Mathlib.Tactic

/-! # Lemmas on `Nat` division and modulo -/

namespace Nat

theorem add_mul_div_of_lt {a n : ℕ} (b : ℕ) (h : a < n) : (a + n * b) / n = b := by
  rw [add_mul_div_left _ _ (by omega), div_eq_of_lt h, zero_add]

theorem add_mul_mod_of_lt {a n : ℕ} (b : ℕ) (h : a < n) : (a + n * b) % n = a := by
  rw [add_mul_mod_self_left, mod_eq_of_lt h]

theorem mod_mul' (m n p : ℕ) : m % (n * p) = m % p + p * (m % (n * p) / p) := by
  rw [mul_div_self_eq_mod_sub_self, mod_mul_left_mod, add_sub_of_le]
  rw [mul_comm, mod_mul]
  omega

theorem pos_and_pos_of_mul_pos {m n : ℕ} (h : 0 < m * n) : 0 < m ∧ 0 < n := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h | h
  . exact h
  . omega

end Nat
