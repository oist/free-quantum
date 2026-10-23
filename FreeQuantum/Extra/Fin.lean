import FreeQuantum.Extra.Nat
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Lemmas on `Fin`

`Fin.cast` along `add_assoc`/`add_mul`/`mul_assoc` through `castAdd`, `natAdd`, `divNat`, `modNat`
and `finProdFinEquiv`; case splits on triple sums.
-/

@[simp] theorem finAddFlip_symm {m n : ℕ} :
    (finAddFlip : Fin (m + n) ≃ Fin (n + m)).symm = finAddFlip := by
  ext i; simp [finAddFlip]

@[simp] theorem finAddFlip_trans_finAddFlip {m n : ℕ} :
    (finAddFlip : Fin (m + n) ≃ Fin (n + m)).trans finAddFlip = Equiv.refl _ := by
  ext i; simp [finAddFlip]

namespace Fin

/-- Case split on `Fin (m + n + p)`. -/
@[elab_as_elim] def addAddCases {m n p : ℕ} {motive : Fin (m + n + p) → Sort*}
    (left : ∀ i : Fin m, motive (castAdd p (castAdd n i)))
    (mid : ∀ j : Fin n, motive (castAdd p (natAdd m j)))
    (right : ∀ k : Fin p, motive (natAdd (m + n) k)) (i : Fin (m + n + p)) :
    motive i :=
  addCases (addCases (motive := fun ij ↦ motive (castAdd p ij)) left mid) right i

/-- Case split on `Fin (m + (n + p))`. -/
@[elab_as_elim] def addAddCases' {m n p : ℕ} {motive : Fin (m + (n + p)) → Sort*}
    (left : ∀ i : Fin m, motive (castAdd (n + p) i))
    (mid : ∀ j : Fin n, motive (natAdd m (castAdd p j)))
    (right : ∀ k : Fin p, motive (natAdd m (natAdd n k))) (i : Fin (m + (n + p))) :
    motive i :=
  addCases left (addCases (motive := fun jk ↦ motive (natAdd m jk)) mid right) i

@[simp] theorem cast_castAdd_castAdd {m : ℕ} (i : Fin m) (n p : ℕ) :
    Fin.cast (add_assoc m n p) (castAdd p (castAdd n i)) = castAdd (n + p) i := by
  ext; simp

@[simp] theorem cast_castAdd_natAdd (m : ℕ) {n : ℕ} (j : Fin n) (p : ℕ) :
    Fin.cast (add_assoc m n p) (castAdd p (natAdd m j)) = natAdd m (castAdd p j) := by
  ext; simp

@[simp] theorem cast_natAdd_add (m n : ℕ) {p : ℕ} (k : Fin p) :
    Fin.cast (add_assoc m n p) (natAdd (m + n) k) = natAdd m (natAdd n k) := by
  ext; simp [add_assoc]

@[simp] theorem cast_castAdd_add {m : ℕ} (i : Fin m) (n p : ℕ) :
    Fin.cast (add_assoc m n p).symm (castAdd (n + p) i) = castAdd p (castAdd n i) := by
  rw [← cast_castAdd_castAdd, cast_cast, cast_eq_self]

@[simp] theorem cast_natAdd_castAdd (m : ℕ) {n : ℕ} (j : Fin n) (p : ℕ) :
    Fin.cast (add_assoc m n p).symm (natAdd m (castAdd p j)) = castAdd p (natAdd m j) := by
  rw [← cast_castAdd_natAdd, cast_cast, cast_eq_self]

@[simp] theorem cast_natAdd_natAdd (m n : ℕ) {p : ℕ} (k : Fin p) :
    Fin.cast (add_assoc m n p).symm (natAdd m (natAdd n k)) = natAdd (m + n) k := by
  rw [← cast_natAdd_add, cast_cast, cast_eq_self]

@[simp] theorem cast_finProdFinEquiv_castAdd
    {m : ℕ} (i : Fin m) (n : ℕ) {p : ℕ} (k : Fin p) :
    Fin.cast (add_mul m n p) (finProdFinEquiv ⟨castAdd n i, k⟩) =
    castAdd (n * p) (finProdFinEquiv ⟨i, k⟩) := by
  ext; simp

@[simp] theorem cast_finProdFinEquiv_natAdd
    (m : ℕ) {n : ℕ} (j : Fin n) {p : ℕ} (k : Fin p) :
    Fin.cast (add_mul m n p) (finProdFinEquiv ⟨natAdd m j, k⟩) =
    natAdd (m * p) (finProdFinEquiv ⟨j, k⟩) := by
  ext; simp; ring

section

variable {m n : ℕ} (i : Fin m) (j : Fin n)

theorem divNat_finProdFinEquiv : divNat (finProdFinEquiv ⟨i, j⟩) = i := by
  ext
  simp [finProdFinEquiv]
  exact Nat.add_mul_div_of_lt _ j.isLt

theorem modNat_finProdFinEquiv : modNat (finProdFinEquiv ⟨i, j⟩) = j := by
  ext
  simp [finProdFinEquiv]
  exact Nat.mod_eq_of_lt j.isLt

end

section

variable {m n p : ℕ} (i : Fin (m * n * p)) (j : Fin (m * (n * p)))

@[simp] theorem divNat_cast :
    divNat (Fin.cast (mul_assoc ..) i) = divNat (divNat i) := by
  ext; simp [Nat.div_div_eq_div_mul, mul_comm]

@[simp] theorem divNat_modNat_cast :
    divNat (modNat (Fin.cast (mul_assoc m n p) i)) = modNat (divNat i) := by
  ext; simp [Nat.mod_mul_left_div_self]

@[simp] theorem modNat_modNat_cast :
    modNat (modNat (Fin.cast (mul_assoc m n p) i)) = modNat i := by
  ext; simp

@[simp] theorem divNat_divNat_cast :
    divNat (divNat (Fin.cast (mul_assoc m n p).symm j)) = divNat j := by
  simp [← divNat_cast]

@[simp] theorem modNat_divNat_cast :
    modNat (divNat (Fin.cast (mul_assoc m n p).symm j)) = divNat (modNat j) := by
  simp [← divNat_modNat_cast]

@[simp] theorem modNat_cast :
    modNat (Fin.cast (mul_assoc m n p).symm j) = modNat (modNat j) := by
  simp [← modNat_modNat_cast]

end

end Fin
