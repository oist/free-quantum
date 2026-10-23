import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Finite-dimensional Hilbert spaces

- `Eucl n` : `EuclideanSpace ℂ (Fin n)`
- `BiEucl m n` : `Eucl m ⊗ Eucl n`, identified with `Eucl (m * n)` by `BiEucl.equiv`
  (index `finProdFinEquiv`)
-/

noncomputable section

local notation "⟪" x ", " y "⟫" => inner ℂ x y
local infixl:100 " ⊗ " => TensorProduct ℂ
local notation:50 x " ≃ₗ " y => LinearEquiv (RingHom.id ℂ) x y
local notation:50 x " ≃ₗᵢ " y => LinearIsometryEquiv (RingHom.id ℂ) x y

namespace FreeQuantum

abbrev Eucl n := EuclideanSpace ℂ (Fin n)
abbrev BiEucl m n := Eucl m ⊗ Eucl n

namespace Eucl

def oneEquiv : Eucl 1 ≃ₗ ℂ :=
  WithLp.linearEquiv 2 ℂ (Fin 1 → ℂ) ≪≫ₗ LinearEquiv.funUnique (Fin 1) ℂ ℂ

variable {n : ℕ}
def onb : OrthonormalBasis (Fin n) ℂ (Eucl n) where
  repr := LinearIsometryEquiv.refl _ _

lemma onb_apply (i : Fin n) : onb i = EuclideanSpace.single i (1 : ℂ) := by
  rw [← onb.repr_symm_single]
  apply onb.repr.symm_apply_eq.mpr
  rw [show onb.repr = LinearIsometryEquiv.refl ℂ (Eucl n) from rfl]
  simp [LinearIsometryEquiv.refl]

lemma onb_repr_apply_apply (x : Eucl n) (i : Fin n) : onb.repr x i = x i := by
  rw [onb.repr_apply_apply]
  simp [inner, onb_apply]

end Eucl

namespace BiEucl
variable {m n : ℕ}

/-- Canonical map for indices that match `equiv` mapping. -/
@[simps!]
def ix : (Fin m × Fin n) ≃ Fin (m * n) := finProdFinEquiv

/-- Canonical equivalence from BiEucl to Eucl. -/
def equiv : BiEucl m n ≃ₗ Eucl (m * n) :=
  TensorProduct.congr (EuclideanSpace.equiv (Fin m) ℂ).toLinearEquiv
    (EuclideanSpace.equiv (Fin n) ℂ).toLinearEquiv ≪≫ₗ
  TensorProduct.comm _ _ _ ≪≫ₗ
  TensorProduct.piScalarRight _ _ (Fin n → ℂ) (Fin m) ≪≫ₗ
  (LinearEquiv.curry _ _ (Fin m) (Fin n)).symm ≪≫ₗ
  LinearEquiv.funCongrLeft _ _ ix.symm ≪≫ₗ
  (EuclideanSpace.equiv (Fin (m * n)) ℂ).toLinearEquiv.symm

@[coe]
def toFun (x : BiEucl m n) (ij : Fin m × Fin n) : ℂ := equiv x (ix ij)

instance instCoeFun : CoeFun (BiEucl m n) (fun _ ↦ (Fin m × Fin n) → ℂ) where
  coe := toFun

lemma coe_equiv (x : BiEucl m n) (ij : Fin m × Fin n) : x ij = equiv x (ix ij) := by rfl

@[simp]
lemma coe_smul_apply (s : ℂ) (x : BiEucl m n) (ij : Fin m × Fin n) : (s • x) ij = s * x ij := by
  simp [coe_equiv]

instance instInnerProductSpace : InnerProductSpace ℂ (BiEucl m n) := TensorProduct.instInnerProductSpace

@[simp]
lemma equiv_tmul_ix (x : Eucl m) (y : Eucl n) (i : Fin m) (j : Fin n) : equiv (x ⊗ₜ[ℂ] y) (ix ⟨i, j⟩) = x i * y j := by
  simp [equiv]

@[simp]
lemma coe_equiv_apply (x : Eucl m) (y : Eucl n) (i : Fin m) (j : Fin n) : (x ⊗ₜ[ℂ] y) ⟨i, j⟩ = x i * y j := by
  rw [coe_equiv, equiv_tmul_ix]

lemma inner_tmul_tmul (x y : Eucl m) (z w : Eucl n) : ⟪x ⊗ₜ[ℂ] z, y ⊗ₜ[ℂ] w⟫ = ⟪x, y⟫ * ⟪z, w⟫ := by
  rw [TensorProduct.inner_tmul]

def reindex : Eucl (m * n) ≃ₗ EuclideanSpace ℂ (Fin m × Fin n) :=
  (EuclideanSpace.equiv (Fin (m * n)) ℂ).toLinearEquiv ≪≫ₗ
  LinearEquiv.funCongrLeft _ _ ix ≪≫ₗ
  (EuclideanSpace.equiv (Fin m × Fin n) ℂ).toLinearEquiv.symm

lemma inner_reindex_reindex (x y : Eucl (m * n)) :
    ⟪reindex x, reindex y⟫ = ⟪x, y⟫ := by
  simp [reindex, PiLp.inner_apply]
  rw [← Equiv.sum_comp ix]

def reindexIsometry : Eucl (m * n) ≃ₗᵢ EuclideanSpace ℂ (Fin m × Fin n) :=
  reindex |>.isometryOfInner inner_reindex_reindex

lemma inner_equiv_equiv (x y : BiEucl m n) : ⟪equiv x, equiv y⟫ = ⟪x, y⟫ := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul x₁ x₂ =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul y₁ y₂ =>
      rw [inner_tmul_tmul]
      simp only [PiLp.inner_apply]
      rw [← Equiv.sum_comp ix, Fintype.sum_prod_type, Fintype.sum_mul_sum]
      congr ; ext i; congr; ext j
      simp [equiv_tmul_ix]
      ring
    | add _ _ _ _ =>
      simp only [inner_add_right, map_add, *]
  | add _ _ _ _ =>
    simp only [inner_add_left, map_add, *]

def isometry : BiEucl m n ≃ₗᵢ Eucl (m * n) :=
  equiv |>.isometryOfInner inner_equiv_equiv

def onb : OrthonormalBasis (Fin m × Fin n) ℂ (BiEucl m n) where
  repr := isometry.trans reindexIsometry

lemma onb_apply (ij : Fin m × Fin n) : onb ij = Eucl.onb ij.1 ⊗ₜ Eucl.onb ij.2 := by
  rw [← onb.repr_symm_single]
  apply onb.repr.symm_apply_eq.mpr
  rw [show onb.repr = isometry.trans reindexIsometry from rfl]

  ext ij'
  obtain ⟨i', j'⟩ := ij'
  simp [isometry, reindexIsometry, reindex]
  obtain ⟨i, j⟩ := ij
  simp [Eucl.onb_apply]
  split_ifs <;> simp <;> omega

lemma equiv_apply_ix (x : BiEucl m n) (ij : Fin m × Fin n) : equiv x (ix ij) = onb.repr x ij := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul =>
    rw [equiv_tmul_ix]
    rw [onb.repr_apply_apply, onb_apply, inner_tmul_tmul]
    repeat rw [← Eucl.onb.repr_apply_apply, Eucl.onb_repr_apply_apply]
  | add x y hx hy =>
    obtain ⟨i, j⟩ := ij
    simp [map_add, *]

lemma equiv_onb_ix_eq_ite (ij ij' : Fin m × Fin n) : equiv (onb ij') (ix ij) = if ij = ij' then 1 else 0 := by
  rw [BiEucl.equiv_apply_ix]
  simp

end BiEucl

end FreeQuantum
