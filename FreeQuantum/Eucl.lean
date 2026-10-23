import FreeQuantum.Extra.Fin
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Finite-dimensional Hilbert spaces

- `Eucl n` : `EuclideanSpace ℂ (Fin n)`, with standard basis `onb`
- `perm e` : coordinate permutation along `e : Fin m ≃ Fin n`
- `sumEquiv` : `Eucl m × Eucl n ≃ Eucl (m + n)` (index `finSumFinEquiv`)
- `prodEquiv` : `Eucl m ⊗ Eucl n ≃ Eucl (m * n)` (index `finProdFinEquiv`)
-/

noncomputable section

namespace FreeQuantum

abbrev Eucl n := EuclideanSpace ℂ (Fin n)

namespace Eucl

variable {m n p : ℕ}

def onb : OrthonormalBasis (Fin n) ℂ (Eucl n) where
  repr := LinearIsometryEquiv.refl _ _

lemma onb_apply (i : Fin n) : onb i = EuclideanSpace.single i (1 : ℂ) := by
  rw [← onb.repr_symm_single]
  apply onb.repr.symm_apply_eq.mpr
  rw [show onb.repr = LinearIsometryEquiv.refl ℂ (Eucl n) from rfl]
  simp [LinearIsometryEquiv.refl]

theorem toEuclideanLin_onb (A : Matrix (Fin n) (Fin m) ℂ) (i : Fin m) :
    Matrix.toEuclideanLin A (onb i) = ∑ k, A k i • onb k := by
  ext k
  simp [onb_apply, Matrix.toLpLin_apply, Pi.single_apply, Finset.sum_apply]

theorem eq_sum_onb (x : Eucl n) : x = ∑ k, x k • onb k := by
  conv_lhs => rw [← onb.sum_repr x]
  congr

/-- Coordinate permutation along `e`. -/
def perm (e : Fin m ≃ Fin n) : Eucl m ≃ₗ[ℂ] Eucl n :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e).toLinearEquiv

@[simp] theorem perm_apply_apply (e : Fin m ≃ Fin n) (x : Eucl m) (j : Fin n) :
    perm e x j = x (e.symm j) := by
  simp [perm, Equiv.piCongrLeft'_apply]

theorem perm_trans_perm (e₁ : Fin m ≃ Fin n) (e₂ : Fin n ≃ Fin p) :
    perm e₁ ≪≫ₗ perm e₂ = perm (e₁.trans e₂) := by
  simp only [perm]
  rw [← LinearIsometryEquiv.toLinearEquiv_trans]
  congr; ext; simp

@[simp] theorem perm_perm (e₁ : Fin m ≃ Fin n) (e₂ : Fin n ≃ Fin p) (x : Eucl m) :
    perm e₂ (perm e₁ x) = perm (e₁.trans e₂) x := by
  show (perm e₁ ≪≫ₗ perm e₂) x = _
  rw [perm_trans_perm]

@[simp] theorem perm_onb (e : Fin m ≃ Fin n) (i : Fin m) :
    perm e (onb i) = onb (e i) := by
  ext; simp [perm, onb_apply]

@[simp] theorem perm_refl : perm (Equiv.refl (Fin n)) = LinearEquiv.refl ℂ (Eucl n) := by
  ext; simp

/-- `Eucl m × Eucl n ≃ Eucl (m + n)`, indexed by `finSumFinEquiv`. -/
def sumEquiv : (Eucl m × Eucl n) ≃ₗ[ℂ] Eucl (m + n) :=
  (LinearEquiv.prodCongr
    (EuclideanSpace.equiv (Fin m) ℂ)
    (EuclideanSpace.equiv (Fin n) ℂ)) ≪≫ₗ
  (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) ℂ ℂ).symm ≪≫ₗ
  LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm ≪≫ₗ
  (EuclideanSpace.equiv (Fin (m + n)) ℂ).toLinearEquiv.symm

@[simp] theorem sumEquiv_castAdd (x : Eucl m × Eucl n) (i : Fin m) :
    sumEquiv x (Fin.castAdd n i) = x.1 i := by
  simp [sumEquiv, LinearEquiv.funCongrLeft_apply]

@[simp] theorem sumEquiv_natAdd (x : Eucl m × Eucl n) (j : Fin n) :
    sumEquiv x (Fin.natAdd m j) = x.2 j := by
  simp [sumEquiv, LinearEquiv.funCongrLeft_apply]

theorem sumEquiv_apply_eq_ite (x : Eucl m × Eucl n) (i : Fin (m + n)) :
    sumEquiv x i = if h : i.val < m then x.1 ⟨i, h⟩ else x.2 ⟨i - m, by omega⟩ := by
  cases i using Fin.addCases <;> simp

theorem perm_sumEquiv_sumEquiv (x : Eucl m) (y : Eucl n) (z : Eucl p) :
    perm (finCongr (add_assoc m n p)) (sumEquiv ⟨sumEquiv ⟨x, y⟩, z⟩) =
      sumEquiv ⟨x, sumEquiv ⟨y, z⟩⟩ := by
  ext ijk; cases ijk using Fin.addAddCases' <;> simp

theorem perm_sumEquiv_sumEquiv' (x : Eucl m) (y : Eucl n) (z : Eucl p) :
    perm (finCongr (add_assoc m n p).symm) (sumEquiv ⟨x, sumEquiv ⟨y, z⟩⟩) =
      sumEquiv ⟨sumEquiv ⟨x, y⟩, z⟩ := by
  ext ijk; cases ijk using Fin.addAddCases <;> simp

@[simp] theorem sumEquiv_onb_left (i : Fin m) :
    sumEquiv ⟨onb i, 0⟩ = onb (i.castAdd n) := by
  ext ij
  simp [sumEquiv, onb_apply]
  obtain ⟨_ | j, rfl⟩ := finSumFinEquiv.surjective ij <;> simp
  . apply Fin.ne_of_val_ne; simp; omega

@[simp] theorem sumEquiv_onb_right (j : Fin n) :
    sumEquiv ⟨0, onb j⟩ = onb (j.natAdd m) := by
  ext ij
  simp [sumEquiv, onb_apply]
  obtain ⟨i | _, rfl⟩ := finSumFinEquiv.surjective ij <;> simp
  . apply Fin.ne_of_val_ne; simp; omega

@[simp] theorem sumEquiv_symm_onb_castAdd (i : Fin m) :
    sumEquiv.symm (onb (Fin.castAdd n i)) = ⟨onb i, 0⟩ := by
  simp [← sumEquiv_onb_left]

@[simp] theorem sumEquiv_symm_onb_natAdd (j : Fin n) :
    sumEquiv.symm (onb (Fin.natAdd m j)) = ⟨0, onb j⟩ := by
  simp [← sumEquiv_onb_right]

theorem sumEquiv_zero_left (x : Eucl n) :
    sumEquiv ⟨0, x⟩ = perm (finCongr (zero_add _).symm) x := by
  ext i
  set i' : Fin n := ⟨i.val, by omega⟩
  have : i = i'.natAdd 0 := by ext; simp [i']
  rw [this, sumEquiv_natAdd]
  simp

theorem sumEquiv_symm_onb_fin_zero_add (i : Fin (0 + n)) :
    sumEquiv.symm (onb i) = ⟨0, onb (i.cast (zero_add _))⟩ := by
  apply sumEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, sumEquiv_zero_left]
  ext j; simp

theorem sumEquiv_zero_right (x : Eucl n) :
    sumEquiv ⟨x, 0⟩ = perm (finCongr (add_zero _).symm) x := by
  ext i
  set i' : Fin n := ⟨i.val, by omega⟩
  have : i = i'.castAdd 0 := by ext; simp [i']
  rw [this, sumEquiv_castAdd]
  simp

theorem sumEquiv_symm_onb_fin_add_zero (i : Fin (n + 0)) :
    sumEquiv.symm (onb i) = ⟨onb (i.cast (add_zero _)), 0⟩ := by
  apply sumEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, sumEquiv_zero_right]
  ext j; simp

@[simp] theorem sumEquiv_symm_fst (x : Eucl (m + n)) (i : Fin m) :
    (sumEquiv.symm x).1 i = x (Fin.castAdd n i) := by
  obtain ⟨_, rfl⟩ := sumEquiv.surjective x; simp

@[simp] theorem sumEquiv_symm_snd (x : Eucl (m + n)) (j : Fin n) :
    (sumEquiv.symm x).2 j = x (Fin.natAdd m j) := by
  obtain ⟨_, rfl⟩ := sumEquiv.surjective x; simp

/-- `Eucl m ⊗ Eucl n ≃ Eucl (m * n)`, indexed by `finProdFinEquiv`. -/
def prodEquiv : TensorProduct ℂ (Eucl m) (Eucl n) ≃ₗ[ℂ] Eucl (m * n) :=
  TensorProduct.congr (EuclideanSpace.equiv (Fin m) ℂ).toLinearEquiv
    (EuclideanSpace.equiv (Fin n) ℂ).toLinearEquiv ≪≫ₗ
  TensorProduct.comm _ _ _ ≪≫ₗ
  TensorProduct.piScalarRight _ _ (Fin n → ℂ) (Fin m) ≪≫ₗ
  (LinearEquiv.curry _ _ (Fin m) (Fin n)).symm ≪≫ₗ
  LinearEquiv.funCongrLeft _ _ finProdFinEquiv.symm ≪≫ₗ
  (EuclideanSpace.equiv (Fin (m * n)) ℂ).toLinearEquiv.symm

@[simp] theorem prodEquiv_tmul_finProdFinEquiv (x : Eucl m) (y : Eucl n) (i : Fin m) (j : Fin n) :
    prodEquiv (x ⊗ₜ y) (finProdFinEquiv ⟨i, j⟩) = x i * y j := by
  simp [prodEquiv]

theorem prodEquiv_onb_tmul_onb (i : Fin m) (j : Fin n) :
    prodEquiv (onb i ⊗ₜ onb j) = onb (finProdFinEquiv ⟨i, j⟩) := by
  ext ij
  simp [prodEquiv, onb_apply]
  by_cases h : ij = finProdFinEquiv ⟨i, j⟩
  . simp [h, Fin.divNat_finProdFinEquiv, Fin.modNat_finProdFinEquiv]
  . simp [if_neg h]
    split_ifs with h' <;> simp
    simp [finProdFinEquiv] at h
    contrapose! h
    simp [← h, ← h', Nat.mod_add_div]

theorem prodEquiv_symm_onb_fin_mul (i : Fin (m * n)) :
    prodEquiv.symm (onb i) = onb i.divNat ⊗ₜ onb i.modNat := by
  apply prodEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, prodEquiv_onb_tmul_onb]
  simp [finProdFinEquiv, Nat.mod_add_div]

theorem prodEquiv_onb_zero_tmul (x : Eucl n) :
    prodEquiv (onb 0 ⊗ₜ x) = perm (finCongr (one_mul _).symm) x := by
  ext i
  simp [prodEquiv, onb_apply]
  rw [if_pos (by omega)]
  simp only [PiLp.continuousLinearEquiv_apply]
  apply congrArg; ext
  rw [Fin.coe_modNat, Nat.mod_eq_of_lt (by have := i.is_lt; omega)]
  simp

theorem prodEquiv_symm_onb_fin_one_mul (i : Fin (1 * n)) :
    prodEquiv.symm (onb i) = onb 0 ⊗ₜ onb (i.cast (one_mul _)) := by
  apply prodEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, prodEquiv_onb_zero_tmul]
  ext j
  simp [onb_apply]

theorem prodEquiv_tmul_onb_zero (x : Eucl n) :
    prodEquiv (x ⊗ₜ onb 0) = perm (finCongr (mul_one _).symm) x := by
  ext i
  simp [prodEquiv, onb_apply]
  rw [if_pos (by omega)]
  apply congrArg; ext
  rw [Fin.coe_divNat]
  simp

theorem prodEquiv_symm_onb_fin_mul_one (i : Fin (n * 1)) :
    prodEquiv.symm (onb i) = onb (i.cast (mul_one _)) ⊗ₜ onb 0 := by
  apply prodEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, prodEquiv_tmul_onb_zero]
  ext j
  simp [onb_apply]

theorem perm_prodEquiv_sumEquiv_tmul (x : Eucl m) (y : Eucl n) (z : Eucl p) :
    perm (finCongr (add_mul m n p)) (prodEquiv (sumEquiv ⟨x, y⟩ ⊗ₜ z)) =
      sumEquiv ⟨prodEquiv (x ⊗ₜ z), prodEquiv (y ⊗ₜ z)⟩ := by
  ext ijk
  cases ijk using Fin.addCases with
  | left ik =>
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ik
    rw [sumEquiv_castAdd, perm_apply_apply]
    simp [← Fin.cast_finProdFinEquiv_castAdd]
  | right jk =>
    obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective jk
    rw [sumEquiv_natAdd, perm_apply_apply]
    simp [← Fin.cast_finProdFinEquiv_natAdd]

end Eucl

end FreeQuantum
