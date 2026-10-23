import FreeQuantum.Bipermutative.Instances.FinPerm
import FreeQuantum.Eucl

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory

/-!
## Instance: `FinLin`

Objects are natural numbers, `m ⟶ n` is `Eucl m →ₗ[ℂ] Eucl n`.
`◆` is `TensorProduct.map` conjugated by `Eucl.prodEquiv` (index `finProdFinEquiv`),
`◇` is `LinearMap.prodMap` conjugated by `Eucl.sumEquiv` (index `finSumFinEquiv`),
so index conventions agree with `FinPerm`.
Symmetries and `eqToHom` are coordinate permutations `perm`.
-/

noncomputable section

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

instance instMul : StrictMulSymmetricMonoidalCategory FinLin where
  mulObj X Y := ⟨X.n * Y.n⟩
  mulUnit := ⟨1⟩
  mulHom f g := ofLin <|
    Eucl.prodEquiv.toLinearMap ∘ₗ TensorProduct.map (toLin f) (toLin g) ∘ₗ Eucl.prodEquiv.symm.toLinearMap

  mulObj_assoc X Y Z := by simp [mul_assoc]
  one_mulObj X := by simp
  mulObj_one X := by simp

  id_one_mulHom_heq f := by
    rw [hom_heq_iff (by ring_nf) (by ring_nf)]
    simp; intro i
    rw [Eucl.prodEquiv_symm_onb_fin_one_mul, TensorProduct.map_tmul]
    simp only [LinearMap.id_coe, id_eq]
    rw [Eucl.prodEquiv_onb_zero_tmul, Eucl.perm_perm]
    ext j
    simp [Eucl.onb_apply]
  mulHom_id_one_heq f := by
    rw [hom_heq_iff (by ring_nf) (by ring_nf)]
    simp; intro i
    rw [Eucl.prodEquiv_symm_onb_fin_mul_one, TensorProduct.map_tmul]
    simp only [LinearMap.id_coe, id_eq]
    rw [Eucl.prodEquiv_tmul_onb_zero, Eucl.perm_perm]
    ext j
    simp [Eucl.onb_apply]
  mulHom_assoc_heq {X₁ Y₁ X₂ Y₂ X₃ Y₃} f g h := by
    rw [hom_heq_iff (by ring_nf) (by ring_nf)]
    simp; intro i
    simp only [Eucl.prodEquiv_symm_onb_fin_mul, TensorProduct.map_tmul]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
    simp only [Eucl.prodEquiv_symm_onb_fin_mul, TensorProduct.map_tmul]
    ext; simp [Eucl.prodEquiv, mul_assoc]
  id_mulHom_id X Y := by simp
  mulHom_comp_mulHom f₁ f₂ g₁ g₂ := by
    ext; simp [Eucl.prodEquiv_symm_onb_fin_mul, toLin_comp]

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
    simp only [Eucl.prodEquiv_symm_onb_fin_mul, TensorProduct.map_tmul]
    simp [Eucl.prodEquiv, Fin.divNat_finProdFinEquiv, Fin.modNat_finProdFinEquiv]
    ring
  mulSwap_hexagon X Y Z := by
    ext i j
    simp [toLin_comp, toLin_eqToHom, Eucl.prodEquiv_onb_tmul_onb, Eucl.prodEquiv_symm_onb_fin_mul]
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
      Eucl.prodEquiv (
        toLin f (Eucl.onb (finProdFinEquiv.symm ij).1) ⊗ₜ
        toLin g (Eucl.onb (finProdFinEquiv.symm ij).2)) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := finProdFinEquiv.surjective ij
  dsimp [mulHom]
  rw [Eucl.prodEquiv_symm_onb_fin_mul]
  simp [finProdFinEquiv]

@[simp] theorem toLin_mulHom_prodEquiv_tmul {X₁ Y₁ X₂ Y₂ : FinLin} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (x : Eucl X₁.n) (y : Eucl X₂.n) :
    toLin (f ◆ₘ g) (Eucl.prodEquiv (x ⊗ₜ y)) = Eucl.prodEquiv (toLin f x ⊗ₜ toLin g y) := by
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
  rw [← Eucl.prodEquiv_tmul_onb_zero, toLin_mulHom_prodEquiv_tmul]
  have : toLin c (Eucl.onb 0) = toLin c (Eucl.onb 0) 0 • Eucl.onb 0 := by
    ext i; fin_cases i; simp [Eucl.onb_apply]
  conv_lhs => rw [this]
  rw [TensorProduct.tmul_smul, map_smul, Eucl.prodEquiv_tmul_onb_zero]
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
    obtain ⟨t, rfl⟩ := Eucl.prodEquiv.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x _ =>
      obtain ⟨⟨x₁, x₂⟩, rfl⟩ := Eucl.sumEquiv.surjective x
      rw [toLin_mulHom_prodEquiv_tmul, toLin_addHom_sumEquiv]
      rw [Eucl.perm_prodEquiv_sumEquiv_tmul, Eucl.perm_prodEquiv_sumEquiv_tmul]
      rw [toLin_addHom_sumEquiv (f ◆ₘ h) (g ◆ₘ h)]
      simp only [toLin_mulHom_prodEquiv_tmul]
    | add _ _ h₁ h₂ => simp [h₁, h₂]

section
open Eucl (sumEquiv)

variable {X Y Z W : FinLin} (x : Eucl X.n) (y : Eucl Y.n) (z : Eucl Z.n) (w : Eucl W.n)

@[simp] theorem toLin_eqToHom_addObj_mulObj :
    toLin (eqToHom (addObj_mulObj X Y Z)) (Eucl.prodEquiv (sumEquiv ⟨x, y⟩ ⊗ₜ z)) =
      sumEquiv ⟨Eucl.prodEquiv (x ⊗ₜ z), Eucl.prodEquiv (y ⊗ₜ z)⟩ := by
  rw [toLin_eqToHom]
  exact Eucl.perm_prodEquiv_sumEquiv_tmul x y z

@[simp] theorem toLin_mulSwap_prodEquiv_tmul :
    toLin (σ_◆ X Y) (Eucl.prodEquiv (x ⊗ₜ y)) = Eucl.prodEquiv (y ⊗ₜ x) := by
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
    toLin (δ_ X Y Z) (Eucl.prodEquiv (x ⊗ₜ sumEquiv ⟨y, z⟩)) =
      sumEquiv ⟨Eucl.prodEquiv (x ⊗ₜ y), Eucl.prodEquiv (x ⊗ₜ z)⟩ := by
  simp [distrib, toLin_comp]
  rw [toLin_mulSwap_prodEquiv_tmul, toLin_eqToHom_addObj_mulObj, toLin_addHom_sumEquiv]
  rw [toLin_mulSwap_prodEquiv_tmul, toLin_mulSwap_prodEquiv_tmul]

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
    obtain ⟨t, rfl⟩ := Eucl.prodEquiv.surjective x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul xy z =>
      obtain ⟨⟨x, y⟩, rfl⟩ := Eucl.sumEquiv.surjective xy
      simp only [toLin_comp, LinearMap.comp_apply]
      rw [toLin_eqToHom_addObj_mulObj, toLin_addSwap_sumEquiv]
      rw [toLin_mulHom_prodEquiv_tmul, toLin_addSwap_sumEquiv, toLin_eqToHom_addObj_mulObj]
      simp
    | add _ _ h₁ h₂ => simp only [map_add]; rw [h₁, h₂]
  distrib_pentagon X Y Z W := by
    apply LinearMap.ext; intro x
    obtain ⟨t, rfl⟩ := Eucl.prodEquiv.surjective x
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
