import FreeQuantum.FinPerm
import FreeQuantum.Eucl

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory

/-!
## Instance: `FinLin`

Objects are natural numbers, `m ⟶ n` is `Eucl m →ₗ[ℂ] Eucl n`.
`◆` is `TensorProduct.map` conjugated by `BiEucl.equiv` (index `finProdFinEquiv`),
`◇` is `LinearMap.prodMap` conjugated by `Eucl.sumEquiv` (index `finSumFinEquiv`),
so index conventions agree with `FinPerm`.
Symmetries and `eqToHom` are coordinate permutations `perm`.
-/

noncomputable section

@[simp] theorem _root_.finAddFlip_symm {m n : ℕ} :
    (finAddFlip : Fin (m + n) ≃ Fin (n + m)).symm = finAddFlip := by
  ext i; simp [finAddFlip]

@[simp] theorem _root_.finAddFlip_trans_finAddFlip {m n : ℕ} :
    (finAddFlip : Fin (m + n) ≃ Fin (n + m)).trans finAddFlip = Equiv.refl _ := by
  ext i; simp [finAddFlip]

/-- Case split on `Fin (m + n + p)`. -/
@[elab_as_elim] def _root_.Fin.addAddCases {m n p : ℕ} {motive : Fin (m + n + p) → Sort*}
    (left : ∀ i : Fin m, motive (Fin.castAdd p (Fin.castAdd n i)))
    (mid : ∀ j : Fin n, motive (Fin.castAdd p (Fin.natAdd m j)))
    (right : ∀ k : Fin p, motive (Fin.natAdd (m + n) k)) (i : Fin (m + n + p)) :
    motive i :=
  Fin.addCases (Fin.addCases (motive := fun ij ↦ motive (Fin.castAdd p ij)) left mid) right i

/-- Case split on `Fin (m + (n + p))`. -/
@[elab_as_elim] def _root_.Fin.addAddCases' {m n p : ℕ} {motive : Fin (m + (n + p)) → Sort*}
    (left : ∀ i : Fin m, motive (Fin.castAdd (n + p) i))
    (mid : ∀ j : Fin n, motive (Fin.natAdd m (Fin.castAdd p j)))
    (right : ∀ k : Fin p, motive (Fin.natAdd m (Fin.natAdd n k))) (i : Fin (m + (n + p))) :
    motive i :=
  Fin.addCases left (Fin.addCases (motive := fun jk ↦ motive (Fin.natAdd m jk)) mid right) i

namespace Eucl

variable {m n p : ℕ}

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
    perm e (Eucl.onb i) = Eucl.onb (e i) := by
  ext; simp [perm, Eucl.onb_apply]

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

theorem perm_sumEquiv_sumEquiv (x : Eucl m) (y : Eucl n) (z : Eucl p) :
    perm (finCongr (add_assoc m n p)) (sumEquiv ⟨sumEquiv ⟨x, y⟩, z⟩) =
      sumEquiv ⟨x, sumEquiv ⟨y, z⟩⟩ := by
  ext ijk; cases ijk using Fin.addAddCases' <;> simp

theorem perm_sumEquiv_sumEquiv' (x : Eucl m) (y : Eucl n) (z : Eucl p) :
    perm (finCongr (add_assoc m n p).symm) (sumEquiv ⟨x, sumEquiv ⟨y, z⟩⟩) =
      sumEquiv ⟨sumEquiv ⟨x, y⟩, z⟩ := by
  ext ijk; cases ijk using Fin.addAddCases <;> simp

@[simp] theorem sumEquiv_onb_left (i : Fin m) :
    sumEquiv ⟨Eucl.onb i, 0⟩ = Eucl.onb (i.castAdd n) := by
  ext ij
  simp [Eucl.sumEquiv, Eucl.onb_apply]
  obtain ⟨_ | j, rfl⟩ := finSumFinEquiv.surjective ij <;> simp
  . apply Fin.ne_of_val_ne; simp; omega

@[simp] theorem sumEquiv_onb_right (j : Fin n) :
    sumEquiv ⟨0, Eucl.onb j⟩ = Eucl.onb (j.natAdd m) := by
  ext ij
  simp [Eucl.sumEquiv, Eucl.onb_apply]
  obtain ⟨i | _, rfl⟩ := finSumFinEquiv.surjective ij <;> simp
  . apply Fin.ne_of_val_ne; simp; omega

@[simp] theorem sumEquiv_symm_onb_castAdd (i : Fin m) :
    sumEquiv.symm (Eucl.onb (Fin.castAdd n i)) = ⟨Eucl.onb i, 0⟩ := by
  simp [← sumEquiv_onb_left]

@[simp] theorem sumEquiv_symm_onb_natAdd (j : Fin n) :
    sumEquiv.symm (Eucl.onb (Fin.natAdd m j)) = ⟨0, Eucl.onb j⟩ := by
  simp [← sumEquiv_onb_right]

theorem sumEquiv_zero_left (x : Eucl n) :
    sumEquiv ⟨0, x⟩ = perm (finCongr (zero_add _).symm) x := by
  ext i
  set i' : Fin n := ⟨i.val, by omega⟩
  have : i = i'.natAdd 0 := by ext; simp [i']
  rw [this, sumEquiv_natAdd]
  simp

theorem sumEquiv_symm_onb_fin_zero_add (i : Fin (0 + n)) :
    sumEquiv.symm (Eucl.onb i) = ⟨0, Eucl.onb (i.cast (zero_add _))⟩ := by
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
    sumEquiv.symm (Eucl.onb i) = ⟨Eucl.onb (i.cast (add_zero _)), 0⟩ := by
  apply sumEquiv.injective
  simp only [LinearEquiv.apply_symm_apply, sumEquiv_zero_right]
  ext j; simp

@[simp] theorem sumEquiv_symm_fst (x : Eucl (m + n)) (i : Fin m) :
    (sumEquiv.symm x).1 i = x (Fin.castAdd n i) := by
  obtain ⟨_, rfl⟩ := sumEquiv.surjective x; simp

@[simp] theorem sumEquiv_symm_snd (x : Eucl (m + n)) (j : Fin n) :
    (sumEquiv.symm x).2 j = x (Fin.natAdd m j) := by
  obtain ⟨_, rfl⟩ := sumEquiv.surjective x; simp

theorem toEuclideanLin_onb (A : Matrix (Fin n) (Fin m) ℂ) (i : Fin m) :
    Matrix.toEuclideanLin A (Eucl.onb i) = ∑ k, A k i • Eucl.onb k := by
  ext k
  simp [Eucl.onb_apply, Matrix.toLpLin_apply, Pi.single_apply, Finset.sum_apply]

theorem eq_sum_onb (x : Eucl n) : x = ∑ k, x k • Eucl.onb k := by
  conv_lhs => rw [← Eucl.onb.sum_repr x]
  congr

end Eucl

section finProdFinEquiv_helpers

variable {m n : ℕ} (i : Fin m) (j : Fin n)

theorem _root_.Fin.divNat_finProdFinEquiv :
    Fin.divNat (finProdFinEquiv ⟨i, j⟩) = i := by
  ext
  simp [finProdFinEquiv]
  exact Nat.add_mul_div_of_lt _ j.isLt

theorem _root_.Fin.modNat_finProdFinEquiv :
    Fin.modNat (finProdFinEquiv ⟨i, j⟩) = j := by
  ext
  simp [finProdFinEquiv]
  exact Nat.mod_eq_of_lt j.isLt

end finProdFinEquiv_helpers

namespace BiEucl

variable {m n p : ℕ}

theorem equiv_onb_tmul_onb (i : Fin m) (j : Fin n) :
    BiEucl.equiv (Eucl.onb i ⊗ₜ Eucl.onb j) =
      Eucl.onb (finProdFinEquiv ⟨i, j⟩) := by
  ext ij
  simp [BiEucl.equiv, Eucl.onb_apply]
  by_cases h : ij = finProdFinEquiv ⟨i, j⟩
  . simp [h, Fin.divNat_finProdFinEquiv, Fin.modNat_finProdFinEquiv]
  . simp [if_neg h]
    split_ifs with h' <;> simp
    simp [finProdFinEquiv] at h
    contrapose! h
    simp [← h, ← h', Nat.mod_add_div]

theorem equiv_symm_onb_fin_mul (i : Fin (m * n)) :
    BiEucl.equiv.symm (Eucl.onb i) =
      Eucl.onb i.divNat ⊗ₜ Eucl.onb i.modNat := by
  apply BiEucl.equiv.injective
  simp only [LinearEquiv.apply_symm_apply, equiv_onb_tmul_onb]
  simp [finProdFinEquiv, Nat.mod_add_div]

theorem equiv_onb_zero_tmul (x : Eucl n) :
    BiEucl.equiv (Eucl.onb 0 ⊗ₜ x) =
      Eucl.perm (finCongr (one_mul _).symm) x := by
  ext i
  simp [BiEucl.equiv, Eucl.onb_apply]
  rw [if_pos (by omega)]
  simp only [PiLp.continuousLinearEquiv_apply]
  apply congrArg; ext
  rw [Fin.coe_modNat, Nat.mod_eq_of_lt (by have := i.is_lt; omega)]
  simp

theorem equiv_symm_onb_fin_one_mul (i : Fin (1 * n)) :
    BiEucl.equiv.symm (Eucl.onb i) =
      Eucl.onb 0 ⊗ₜ Eucl.onb (i.cast (one_mul _)) := by
  apply BiEucl.equiv.injective
  simp only [LinearEquiv.apply_symm_apply, equiv_onb_zero_tmul]
  ext j
  simp [Eucl.onb_apply]

theorem equiv_tmul_onb_zero (x : Eucl n) :
    BiEucl.equiv (x ⊗ₜ Eucl.onb 0) =
      Eucl.perm (finCongr (mul_one _).symm) x := by
  ext i
  simp [BiEucl.equiv, Eucl.onb_apply]
  rw [if_pos (by omega)]
  apply congrArg; ext
  rw [Fin.coe_divNat]
  simp

theorem equiv_symm_onb_fin_mul_one (i : Fin (n * 1)) :
    BiEucl.equiv.symm (Eucl.onb i) =
      Eucl.onb (i.cast (mul_one _)) ⊗ₜ Eucl.onb 0 := by
  apply BiEucl.equiv.injective
  simp only [LinearEquiv.apply_symm_apply, equiv_tmul_onb_zero]
  ext j
  simp [Eucl.onb_apply]

@[simp] theorem equiv_tmul_finProdFinEquiv (x : Eucl m) (y : Eucl n) (i : Fin m) (j : Fin n) :
    BiEucl.equiv (x ⊗ₜ y) (finProdFinEquiv ⟨i, j⟩) = x i * y j :=
  BiEucl.equiv_tmul_ix x y i j

theorem perm_equiv_sumEquiv_tmul (x : Eucl m) (y : Eucl n) (z : Eucl p) :
    Eucl.perm (finCongr (add_mul m n p)) (BiEucl.equiv (Eucl.sumEquiv ⟨x, y⟩ ⊗ₜ z)) =
      Eucl.sumEquiv ⟨BiEucl.equiv (x ⊗ₜ z), BiEucl.equiv (y ⊗ₜ z)⟩ := by
  ext ijk
  cases ijk using Fin.addCases with
  | left ik =>
    obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective ik
    rw [Eucl.sumEquiv_castAdd, Eucl.perm_apply_apply]
    simp [← Fin.cast_finProdFinEquiv_castAdd]
  | right jk =>
    obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective jk
    rw [Eucl.sumEquiv_natAdd, Eucl.perm_apply_apply]
    simp [← Fin.cast_finProdFinEquiv_natAdd]

end BiEucl

@[ext]
structure FinLin where
  n : ℕ

namespace FinLin

instance : Category FinLin where
  Hom X Y := Eucl X.n →ₗ[ℂ] Eucl Y.n
  id X := LinearMap.id
  comp f g := g ∘ₗ f

/-- View a morphism as the underlying linear map. -/
abbrev toLin {X Y : FinLin} (f : X ⟶ Y) : Eucl X.n →ₗ[ℂ] Eucl Y.n := f

/-- View a linear map as a morphism. -/
abbrev ofLin {X Y : FinLin} (f : Eucl X.n →ₗ[ℂ] Eucl Y.n) : X ⟶ Y := f

@[simp] theorem toLin_id (X : FinLin) : toLin (𝟙 X) = LinearMap.id := rfl

theorem toLin_comp {X Y Z : FinLin} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toLin (f ≫ g) = toLin g ∘ₗ toLin f := rfl

theorem toLin_eqToHom {X Y : FinLin} (h : X = Y) :
    toLin (eqToHom h) = (Eucl.perm (finCongr (congrArg FinLin.n h))).toLinearMap := by
  subst h; ext x i; simp

@[ext] theorem hom_ext {X Y : FinLin} {f g : X ⟶ Y}
    (h : ∀ i, toLin f (Eucl.onb i) = toLin g (Eucl.onb i)) :
    f = g := by
  apply LinearMap.ext
  intro x
  rw [← Eucl.onb.sum_repr x]
  simp only [map_sum, map_smul]
  congr; ext i j; rw [h]

/-- Reduce a `≍` between morphisms to equality on basis vectors. -/
theorem hom_heq_iff {X X' Y Y' : FinLin} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') :
    f ≍ g ↔ ∀ i, Eucl.perm (finCongr (congrArg FinLin.n hY)) (toLin f (Eucl.onb i)) =
      toLin g (Eucl.onb (Fin.cast (congrArg FinLin.n hX) i)) := by
  subst hX hY
  constructor
  . intro h i; cases h; rfl
  . intro h; apply heq_of_eq (hom_ext h)

/-- Reduce a `≍` between morphisms to equality on all vectors. -/
theorem hom_heq_iff' {X X' Y Y' : FinLin} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') :
    f ≍ g ↔ ∀ x, Eucl.perm (finCongr (congrArg FinLin.n hY)) (toLin f x) =
      toLin g (Eucl.perm (finCongr (congrArg FinLin.n hX)) x) := by
  subst hX hY
  constructor
  . intro h x; cases h; simp
  . intro h; apply heq_of_eq; apply LinearMap.ext; intro x
    simpa using h x

open BipermutativeCategory

section Fin_helpers
variable {m n p : ℕ} (i : Fin (m * n * p)) (j : Fin (m * (n * p)))

@[simp] theorem _root_.Fin.divNat_cast :
    Fin.divNat (.cast (mul_assoc ..) i) = .divNat (.divNat i) := by
  ext; simp [Nat.div_div_eq_div_mul, mul_comm]

@[simp] theorem _root_.Fin.divNat_modNat_cast :
    Fin.divNat (.modNat (.cast (mul_assoc m n p) i)) = .modNat (.divNat i) := by
  ext; simp [Nat.mod_mul_left_div_self]

@[simp] theorem _root_.Fin.modNat_modNat_cast :
    Fin.modNat (.modNat (.cast (mul_assoc m n p) i)) = .modNat i := by
  ext; simp

@[simp] theorem _root_.Fin.divNat_divNat_cast :
    Fin.divNat (.divNat (.cast (mul_assoc m n p).symm j)) = .divNat j := by
  simp [← Fin.divNat_cast]

@[simp] theorem _root_.Fin.modNat_divNat_cast :
    Fin.modNat (.divNat (.cast (mul_assoc m n p).symm j)) = .divNat (.modNat j) := by
  simp [← Fin.divNat_modNat_cast]

@[simp] theorem _root_.Fin.modNat_cast :
    Fin.modNat (.cast (mul_assoc m n p).symm j) = .modNat (.modNat j) := by
  simp [← Fin.modNat_modNat_cast]

end Fin_helpers

theorem _root_.Nat.mod_mul' (m n p : ℕ) : m % (n * p) = m % p + p * (m % (n * p) / p) := by
  rw [Nat.mul_div_self_eq_mod_sub_self, Nat.mod_mul_left_mod, Nat.add_sub_of_le]
  rw [mul_comm, Nat.mod_mul]
  omega

theorem _root_.Nat.pos_and_pos_of_mul_pos {m n : ℕ} (h : 0 < m * n) : 0 < m ∧ 0 < n := by
  rcases pos_and_pos_or_neg_and_neg_of_mul_pos h with h | h
  . exact h
  . omega

instance instMul : StrictMulSymmetricMonoidalCategory FinLin where
  mulObj X Y := ⟨X.n * Y.n⟩
  mulUnit := ⟨1⟩
  mulHom f g := ofLin <|
    BiEucl.equiv.toLinearMap ∘ₗ TensorProduct.map (toLin f) (toLin g) ∘ₗ BiEucl.equiv.symm.toLinearMap

  mulObj_assoc X Y Z := by simp [mul_assoc]
  one_mulObj X := by simp
  mulObj_one X := by simp

  id_one_mulHom_heq f := by
    rw [hom_heq_iff (by ring_nf) (by ring_nf)]
    simp; intro i
    rw [BiEucl.equiv_symm_onb_fin_one_mul, TensorProduct.map_tmul]
    simp only [LinearMap.id_coe, id_eq]
    rw [BiEucl.equiv_onb_zero_tmul, Eucl.perm_perm]
    ext j
    simp [Eucl.onb_apply]
  mulHom_id_one_heq f := by
    rw [hom_heq_iff (by ring_nf) (by ring_nf)]
    simp; intro i
    rw [BiEucl.equiv_symm_onb_fin_mul_one, TensorProduct.map_tmul]
    simp only [LinearMap.id_coe, id_eq]
    rw [BiEucl.equiv_tmul_onb_zero, Eucl.perm_perm]
    ext j
    simp [Eucl.onb_apply]
  mulHom_assoc_heq {X₁ Y₁ X₂ Y₂ X₃ Y₃} f g h := by
    rw [hom_heq_iff (by ring_nf) (by ring_nf)]
    simp; intro i
    simp only [BiEucl.equiv_symm_onb_fin_mul, TensorProduct.map_tmul]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    simp only [BiEucl.equiv_symm_onb_fin_mul, TensorProduct.map_tmul]
    ext; simp [BiEucl.equiv, mul_assoc]
  id_mulHom_id X Y := by simp
  mulHom_comp_mulHom f₁ f₂ g₁ g₂ := by
    ext; simp [BiEucl.equiv_symm_onb_fin_mul, toLin_comp]

  mulSwap X Y := ofLin <|
    (Eucl.perm (finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv))).toLinearMap
  mulSwap_mulSwap X Y := by
    ext _ i; simp [finProdFinEquiv, Eucl.onb_apply, toLin_comp]
    congr
    have : i.val / Y.n < X.n := by
      apply Nat.div_lt_of_lt_mul
      rw [mul_comm Y.n X.n]
      apply i.isLt
    rw [Nat.add_mul_div_of_lt _ this, Nat.mod_eq_of_lt this, Nat.mod_add_div]
  mulSwap_natural f g := by
    ext _ ij; simp [toLin_comp]
    simp only [BiEucl.equiv_symm_onb_fin_mul, TensorProduct.map_tmul]
    simp [BiEucl.equiv, Fin.divNat_finProdFinEquiv, Fin.modNat_finProdFinEquiv]
    ring
  mulSwap_hexagon X Y Z := by
    ext i j
    simp [toLin_comp, toLin_eqToHom, BiEucl.equiv_onb_tmul_onb, BiEucl.equiv_symm_onb_fin_mul]
    simp [Eucl.onb_apply]
    have h₁ : i.val % Z.n < Z.n := by
      apply Nat.mod_lt
      obtain ⟨_, h⟩ := Nat.pos_and_pos_of_mul_pos i.pos
      exact (Nat.pos_and_pos_of_mul_pos h).2
    have h₂ : i.val / (Y.n * Z.n) < X.n := by
      apply Nat.div_lt_of_lt_mul
      rw [mul_comm (Y.n * Z.n) X.n]
      exact i.isLt
    by_cases h : j = finProdFinEquiv ⟨i.modNat, i.divNat⟩
    . simp [h, finProdFinEquiv]
      rw [Nat.add_mul_div_of_lt _ h₁, Nat.add_mul_div_of_lt _ h₂, Nat.add_mul_mod_of_lt _ h₂]
      rw [add_assoc, mul_comm Z.n X.n, mul_assoc X.n Z.n, ← mul_add]
      rw [← Nat.mod_mul']
    . rw [if_neg h]
      simp [finProdFinEquiv] at ⊢ h
      contrapose! h
      have h' := Fin.val_eq_of_eq h
      simp at h'
      ext; simp only
      rw [h']
      rw [Nat.add_mul_div_of_lt _ h₁, Nat.add_mul_div_of_lt _ h₂, Nat.add_mul_mod_of_lt _ h₂]
      rw [add_assoc, mul_comm Z.n X.n, mul_assoc X.n Z.n, ← mul_add]
      rw [← Nat.mod_mul']

instance instAdd : StrictAddSymmetricMonoidalCategory FinLin where
  addObj X Y := ⟨X.n + Y.n⟩
  addUnit := ⟨0⟩
  addHom f g := ofLin <|
    Eucl.sumEquiv.toLinearMap ∘ₗ LinearMap.prodMap (toLin f) (toLin g) ∘ₗ
    Eucl.sumEquiv.symm.toLinearMap

  addObj_assoc X Y Z := by simp [add_assoc]
  zero_addObj X := by simp
  addObj_zero X := by simp

  id_zero_addHom_heq f := by
    rw [hom_heq_iff (by ring_nf) (by ring_nf)]
    simp; intro i
    simp only [Eucl.sumEquiv_symm_onb_fin_zero_add, Eucl.sumEquiv_zero_left]
    ext j; simp [Eucl.onb_apply]
  addHom_id_zero_heq f := by
    rw [hom_heq_iff (by ring_nf) (by ring_nf)]
    simp; intro i
    simp only [Eucl.sumEquiv_symm_onb_fin_add_zero, Eucl.sumEquiv_zero_right]
    ext j; simp [Eucl.onb_apply]
  addHom_assoc_heq f g h := by
    rw [hom_heq_iff' (by ring_nf) (by ring_nf)]
    simp; intro xyz
    obtain ⟨⟨xy, z⟩, rfl⟩ := Eucl.sumEquiv.surjective xyz
    obtain ⟨⟨x, y⟩, rfl⟩ := Eucl.sumEquiv.surjective xy
    simp [Eucl.perm_sumEquiv_sumEquiv]
  id_addHom_id X Y := by simp
  addHom_comp_addHom f₁ f₂ g₁ g₂ := by ext; simp [toLin_comp]

  addSwap X Y := ofLin (Eucl.perm finAddFlip).toLinearMap
  addSwap_addSwap X Y := by
    simp [Eucl.perm_trans_perm, toLin_comp]
  addSwap_natural f g := by
    ext ij ji'
    cases ij using Fin.addCases <;> cases ji' using Fin.addCases <;> simp [toLin_comp]
  addSwap_hexagon X Y Z := by
    ext ijk jki'
    cases ijk using Fin.addAddCases' <;> cases jki' using Fin.addAddCases <;>
      simp [toLin_comp, toLin_eqToHom]

@[simp] theorem mulObj_n (X Y : FinLin) : (X ◆ Y).n = X.n * Y.n := rfl
@[simp] theorem mulUnit_n : (𝐈_ FinLin).n = 1 := rfl
@[simp] theorem addObj_n (X Y : FinLin) : (X ◇ Y).n = X.n + Y.n := rfl
@[simp] theorem addUnit_n : (𝐎_ FinLin).n = 0 := rfl

@[simp] theorem toLin_mulHom_onb {X₁ Y₁ X₂ Y₂ : FinLin} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (ij : Fin (X₁ ◆ X₂).n) :
    toLin (f ◆ₘ g) (Eucl.onb ij) =
      BiEucl.equiv (
        toLin f (Eucl.onb (finProdFinEquiv.symm ij).1) ⊗ₜ
        toLin g (Eucl.onb (finProdFinEquiv.symm ij).2)) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective ij
  dsimp [mulHom]
  rw [BiEucl.equiv_symm_onb_fin_mul]
  simp [finProdFinEquiv]

@[simp] theorem toLin_mulHom_equiv_tmul {X₁ Y₁ X₂ Y₂ : FinLin} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (x : Eucl X₁.n) (y : Eucl X₂.n) :
    toLin (f ◆ₘ g) (BiEucl.equiv (x ⊗ₜ y)) = BiEucl.equiv (toLin f x ⊗ₜ toLin g y) := by
  dsimp [mulHom]
  simp

@[simp] theorem toLin_addHom_sumEquiv {X₁ Y₁ X₂ Y₂ : FinLin} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (x : Eucl X₁.n) (y : Eucl X₂.n) :
    toLin (f ◇ₘ g) (Eucl.sumEquiv ⟨x, y⟩) = Eucl.sumEquiv ⟨toLin f x, toLin g y⟩ := by
  dsimp [addHom]
  simp

@[simp] theorem toLin_smul {X Y : FinLin} (c : Scalar FinLin) (f : X ⟶ Y) :
    toLin (c • f) = toLin c (Eucl.onb 0) 0 • toLin f := by
  apply hom_ext; intro i
  simp only [Scalar.smul_def, toLin_comp, toLin_eqToHom, LinearMap.comp_apply,
    LinearEquiv.coe_coe]
  rw [← BiEucl.equiv_tmul_onb_zero, toLin_mulHom_equiv_tmul]
  have : toLin c (Eucl.onb 0) = toLin c (Eucl.onb 0) 0 • Eucl.onb 0 := by
    ext i; fin_cases i; simp [Eucl.onb_apply]
  conv_lhs => rw [this]
  rw [TensorProduct.tmul_smul, map_smul, BiEucl.equiv_tmul_onb_zero]
  simp; congr 1

theorem ofLin_smul {X Y : FinLin} (c : ℂ) (f : Eucl X.n →ₗ[ℂ] Eucl Y.n) :
    ofLin (c • f) = (ofLin (c • LinearMap.id) : Scalar FinLin) • ofLin f := by
  show c • f = toLin ((ofLin (c • LinearMap.id) : Scalar FinLin) • ofLin f)
  rw [toLin_smul]
  simp [Eucl.onb_apply]

theorem ofLin_scalar_pow (c : ℂ) (n : ℕ) :
    ofLin ((c • LinearMap.id) : Scalar FinLin) ^ n = ofLin (c ^ n • LinearMap.id) := by
  induction n with
  | zero => ext; simp
  | succ n ih =>
    rw [pow_succ, Scalar.mul_def, ih]
    show (c ^ n • LinearMap.id) ∘ₗ (c • LinearMap.id) = c ^ (n + 1) • LinearMap.id
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ← mul_smul, LinearMap.id_comp, pow_succ]

instance : BipermutativeCategoryBase FinLin where
  zero_mulObj X := by ext; simp
  id_zero_mulHom_heq f := by
    rw [hom_heq_iff (by ext; simp) (by ext; simp)]
    intro i
    exact (i.cast (zero_mul _)).elim0
  mulObj_zero X := by ext; simp
  mulHom_id_zero_heq f := by
    rw [hom_heq_iff (by ext; simp) (by ext; simp)]
    simp
  addObj_mulObj X Y Z := by ext; simp [add_mul]
  addHom_mulHom_heq f g h := by
    rw [hom_heq_iff' (by ext; simp [add_mul]) (by ext; simp [add_mul])]
    simp; intro x
    obtain ⟨t, rfl⟩ := BiEucl.equiv.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x _ =>
      obtain ⟨⟨x₁, x₂⟩, rfl⟩ := Eucl.sumEquiv.surjective x
      rw [toLin_mulHom_equiv_tmul, toLin_addHom_sumEquiv]
      rw [BiEucl.perm_equiv_sumEquiv_tmul, BiEucl.perm_equiv_sumEquiv_tmul]
      rw [toLin_addHom_sumEquiv (f ◆ₘ h) (g ◆ₘ h)]
      simp only [toLin_mulHom_equiv_tmul]
    | add _ _ h₁ h₂ => simp [h₁, h₂]

section
open Eucl (sumEquiv)

variable {X Y Z W : FinLin} (x : Eucl X.n) (y : Eucl Y.n) (z : Eucl Z.n) (w : Eucl W.n)

@[simp] theorem toLin_eqToHom_addObj_mulObj :
    toLin (eqToHom (addObj_mulObj X Y Z)) (BiEucl.equiv (sumEquiv ⟨x, y⟩ ⊗ₜ z)) =
      sumEquiv ⟨BiEucl.equiv (x ⊗ₜ z), BiEucl.equiv (y ⊗ₜ z)⟩ := by
  rw [toLin_eqToHom]
  exact BiEucl.perm_equiv_sumEquiv_tmul x y z

@[simp] theorem toLin_mulSwap_equiv_tmul :
    toLin (σ_◆ X Y) (BiEucl.equiv (x ⊗ₜ y)) = BiEucl.equiv (y ⊗ₜ x) := by
  ext ji
  obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective ji
  simp [mulSwap, mul_comm]

@[simp] theorem toLin_mulSwap_onb (ij : Fin (X ◆ Y).n) :
    toLin (σ_◆ X Y) (Eucl.onb ij) =
      Eucl.onb (finProdFinEquiv ⟨(finProdFinEquiv.symm ij).2, (finProdFinEquiv.symm ij).1⟩) := by
  simp [mulSwap]

@[simp] theorem toLin_addSwap_sumEquiv : toLin (σ_◇ X Y) (sumEquiv ⟨x, y⟩) = sumEquiv ⟨y, x⟩ := by
  ext ji
  cases ji using Fin.addCases <;> simp [addSwap]

theorem toLin_distrib :
    toLin (δ_ X Y Z) (BiEucl.equiv (x ⊗ₜ sumEquiv ⟨y, z⟩)) =
      sumEquiv ⟨BiEucl.equiv (x ⊗ₜ y), BiEucl.equiv (x ⊗ₜ z)⟩ := by
  simp [distrib, toLin_comp]
  rw [toLin_mulSwap_equiv_tmul, toLin_eqToHom_addObj_mulObj, toLin_addHom_sumEquiv]
  rw [toLin_mulSwap_equiv_tmul, toLin_mulSwap_equiv_tmul]

theorem toLin_addMedial :
    toLin (addMedial X Y Z W) (sumEquiv ⟨sumEquiv ⟨x, y⟩, sumEquiv ⟨z, w⟩⟩) =
      sumEquiv ⟨sumEquiv ⟨x, z⟩, sumEquiv ⟨y, w⟩⟩ := by
  ext ikjl
  cases ikjl using Fin.addCases <;>
    rename_i ik <;> cases ik using Fin.addCases <;>
    simp [addMedial_def, toLin_comp, toLin_eqToHom, addHom, addSwap]

end

instance : BipermutativeCategory FinLin where
  distrib_square X Y Z := by
    apply LinearMap.ext; intro x
    obtain ⟨t, rfl⟩ := BiEucl.equiv.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul xy z =>
      obtain ⟨⟨x, y⟩, rfl⟩ := Eucl.sumEquiv.surjective xy
      simp only [toLin_comp, LinearMap.comp_apply]
      rw [toLin_eqToHom_addObj_mulObj, toLin_addSwap_sumEquiv]
      rw [toLin_mulHom_equiv_tmul, toLin_addSwap_sumEquiv, toLin_eqToHom_addObj_mulObj]
      simp
    | add _ _ h₁ h₂ => simp only [map_add]; rw [h₁, h₂]
  distrib_pentagon X Y Z W := by
    apply LinearMap.ext; intro x
    obtain ⟨t, rfl⟩ := BiEucl.equiv.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul xy zw =>
      obtain ⟨⟨x, y⟩, rfl⟩ := Eucl.sumEquiv.surjective xy
      obtain ⟨⟨z, w⟩, rfl⟩ := Eucl.sumEquiv.surjective zw
      simp only [toLin_comp, LinearMap.comp_apply]
      rw [toLin_eqToHom_addObj_mulObj, toLin_addHom_sumEquiv, toLin_distrib, toLin_distrib, toLin_addMedial]
      rw [toLin_distrib, toLin_addHom_sumEquiv, toLin_eqToHom_addObj_mulObj, toLin_eqToHom_addObj_mulObj]
    | add _ _ h₁ h₂ => simp only [map_add]; rw [h₁, h₂]

/-! ### Basis vectors and matrix entries -/

section
open Eucl

theorem onb_addObj_of_lt {X Y : FinLin} {i : Fin (X ◇ Y).n} (h : i.val < X.n) :
    onb i = sumEquiv ⟨onb ⟨i, h⟩, 0⟩ := by
  rw [sumEquiv_onb_left]; rfl

theorem onb_addObj_of_ge {X Y : FinLin} {i : Fin (X ◇ Y).n} (h : X.n ≤ i.val) :
    onb i = sumEquiv ⟨0, onb ⟨i - X.n, by have : i.val < X.n + Y.n := i.isLt; omega⟩⟩ := by
  rw [sumEquiv_onb_right]; congr; ext; simp; omega

theorem onb_addObj_eq_ite {X Y : FinLin} (i : Fin (X ◇ Y).n) :
    onb i =
      if h : i.val < X.n
      then sumEquiv ⟨onb ⟨i.val, h⟩, 0⟩
      else sumEquiv ⟨0, (onb ⟨i - X.n, by have : i.val < X.n + Y.n := i.isLt; omega⟩)⟩ := by
  split_ifs with h
  . rw [onb_addObj_of_lt h]
  . rw [onb_addObj_of_ge (Nat.le_of_not_lt h)]

theorem toLin_addHom_onb {X₁ Y₁ X₂ Y₂ : FinLin} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (i : Fin (X₁ ◇ X₂).n) :
    toLin (f ◇ₘ g) (onb i) =
      if h : i.val < X₁.n
      then sumEquiv ⟨toLin f (onb ⟨i.val, h⟩), 0⟩
      else sumEquiv ⟨0, toLin g (onb ⟨i - X₁.n, by have : i.val < X₁.n + X₂.n := i.isLt; omega⟩)⟩ := by
  rw [onb_addObj_eq_ite]
  split_ifs <;> rw [toLin_addHom_sumEquiv] <;> simp

theorem sumEquiv_apply_eq_ite {m n : ℕ} (x : Eucl m × Eucl n) (i : Fin (m + n)) :
    sumEquiv x i = if h : i.val < m then x.1 ⟨i, h⟩ else x.2 ⟨i - m, by omega⟩ := by
  cases i using Fin.addCases <;> simp

/-- The `(i, j)` entry of a hom: the `i`-th coordinate of the image of `onb j`. -/
def entry {X Y : FinLin} (f : X ⟶ Y) (i : Fin Y.n) (j : Fin X.n) : ℂ :=
  toLin f (onb j) i

theorem hom_ext_entry {X Y : FinLin} {f g : X ⟶ Y} (h : ∀ i j, entry f i j = entry g i j) :
    f = g :=
  hom_ext fun j ↦ by ext i; exact h i j

@[simp] theorem entry_comp {X Y Z : FinLin} (f : X ⟶ Y) (g : Y ⟶ Z) (i : Fin Z.n) (j : Fin X.n) :
    entry (f ≫ g) i j = ∑ l, entry g i l * entry f l j := by
  simp only [entry, toLin_comp, LinearMap.comp_apply]
  conv_lhs => rw [Eucl.eq_sum_onb (toLin f (onb j))]
  simp [map_sum, mul_comm]

@[simp] theorem entry_id (X : FinLin) (i j : Fin X.n) :
    entry (𝟙 X) i j = if i = j then 1 else 0 := by
  simp [entry, onb_apply]

@[simp] theorem entry_mulHom {X₁ Y₁ X₂ Y₂ : FinLin} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (i : Fin (Y₁ ◆ Y₂).n) (j : Fin (X₁ ◆ X₂).n) :
    entry (f ◆ₘ g) i j =
      entry f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        entry g (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 := by
  unfold entry
  rw [toLin_mulHom_onb]
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp

@[simp] theorem entry_mulSwap (X Y : FinLin) (i : Fin (Y ◆ X).n) (j : Fin (X ◆ Y).n) :
    entry (σ_◆ X Y) i j =
      if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).2 ∧
        (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).1
      then 1 else 0 := by
  unfold entry
  rw [toLin_mulSwap_onb]
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := finProdFinEquiv.surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp [Eucl.onb_apply]

@[simp] theorem entry_addHom {X₁ Y₁ X₂ Y₂ : FinLin} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (i : Fin (Y₁ ◇ Y₂).n) (j : Fin (X₁ ◇ X₂).n) :
    entry (f ◇ₘ g) i j =
      if hj : j.val < X₁.n then
        if hi : i.val < Y₁.n then entry f ⟨i, hi⟩ ⟨j, hj⟩ else 0
      else
        if hi : i.val < Y₁.n then 0
        else entry g ⟨i - Y₁.n, by have : i.val < Y₁.n + Y₂.n := i.isLt; omega⟩
          ⟨j - X₁.n, by have : j.val < X₁.n + X₂.n := j.isLt; omega⟩ := by
  unfold entry
  rw [toLin_addHom_onb]
  split_ifs <;> rw [sumEquiv_apply_eq_ite] <;> simp_all

@[simp] theorem entry_addSwap (X Y : FinLin) (i : Fin (Y ◇ X).n) (j : Fin (X ◇ Y).n) :
    entry (σ_◇ X Y) i j =
      if j.val < X.n then (if i.val = j.val + Y.n then 1 else 0)
      else (if i.val = j.val - X.n then 1 else 0) := by
  unfold entry
  rw [onb_addObj_eq_ite]
  split_ifs <;> rw [toLin_addSwap_sumEquiv, sumEquiv_apply_eq_ite] <;>
    simp_all [onb_apply, Fin.ext_iff] <;>
    (have hj : j.val < X.n + Y.n := j.isLt; omega)

@[simp] theorem entry_ofLin_toEuclideanLin {m n : ℕ} (A : Matrix (Fin n) (Fin m) ℂ)
    (i : Fin n) (j : Fin m) :
    entry (ofLin (Matrix.toEuclideanLin A) : (⟨m⟩ : FinLin) ⟶ ⟨n⟩) i j = A i j := by
  simp [entry, onb_apply]

theorem ofLin_toEuclideanLin_comp {l m n : ℕ}
    (A : Matrix (Fin m) (Fin l) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) :
    (ofLin (Matrix.toEuclideanLin A) : (⟨l⟩ : FinLin) ⟶ ⟨m⟩) ≫
      (ofLin (Matrix.toEuclideanLin B) : (⟨m⟩ : FinLin) ⟶ ⟨n⟩) =
      ofLin (Matrix.toEuclideanLin (B * A)) := by
  simp [toLin, ofLin, toLin_comp]

theorem id_one_addHom_scalar (s : Scalar FinLin) :
    𝟙 𝐈 ◇ₘ s = ofLin (Matrix.toEuclideanLin !![1, 0; 0, toLin s (Eucl.onb 0) 0]) := by
  ext i j
  simp [toLin, ofLin]
  simp [Matrix.vecHead, Matrix.vecTail]
  have e0 (x : Eucl 1 × Eucl 1) : Eucl.sumEquiv x (0 : Fin (1 + 1)) = x.1 0 :=
    Eucl.sumEquiv_castAdd x 0
  have e1 (x : Eucl 1 × Eucl 1) : Eucl.sumEquiv x (1 : Fin (1 + 1)) = x.2 0 :=
    Eucl.sumEquiv_natAdd x 0
  cases i using Fin.addCases <;> cases j using Fin.addCases <;> rename_i i j
  . erw [← Eucl.sumEquiv_onb_left, toLin_addHom_sumEquiv]
    fin_cases i; fin_cases j; simp
  . erw [← Eucl.sumEquiv_onb_left, toLin_addHom_sumEquiv]
    fin_cases i; fin_cases j; simp [e1]
  . erw [← Eucl.sumEquiv_onb_right, toLin_addHom_sumEquiv]
    fin_cases i; fin_cases j; simp [e0]
  . erw [← Eucl.sumEquiv_onb_right, toLin_addHom_sumEquiv]
    fin_cases i; fin_cases j; simp [e1, Eucl.onb_apply]

end

end FinLin

end

end FreeQuantum
