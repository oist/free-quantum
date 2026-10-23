import FreeQuantum.Bipermutative.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

namespace FreeQuantum

open CategoryTheory

/-!
## Instance: `FinPerm`

The PROP `FinPerm` of Carette et al. (2026), SI (initial rig category).

Objects are natural numbers, `n ⟶ m` is `Fin n ≃ Fin m` (empty unless `n = m`).
`◆ := ×` via `finProdFinEquiv` (left factor is the major index), `◇ := +` via `finSumFinEquiv`.
With this indexing `(X ◇ Y) ◆ Z = (X ◆ Z) ◇ (Y ◆ Z)` holds on the nose, and `δ_` is a
nontrivial shuffle.
-/

@[ext]
structure FinPerm where
  n : ℕ

namespace FinPerm

instance : Category FinPerm where
  Hom X Y := Fin X.n ≃ Fin Y.n
  id X := Equiv.refl _
  comp f g := f.trans g

/-- View a morphism as the underlying equiv. -/
abbrev toEquiv {X Y : FinPerm} (f : X ⟶ Y) : Fin X.n ≃ Fin Y.n := f

/-- View an equiv as a morphism. -/
abbrev ofEquiv {X Y : FinPerm} (e : Fin X.n ≃ Fin Y.n) : X ⟶ Y := e

@[simp] theorem toEquiv_id (X : FinPerm) : toEquiv (𝟙 X) = Equiv.refl _ := rfl

@[simp] theorem toEquiv_comp {X Y Z : FinPerm} (f : X ⟶ Y) (g : Y ⟶ Z) :
    toEquiv (f ≫ g) = (toEquiv f).trans (toEquiv g) := rfl

@[simp] theorem toEquiv_eqToHom {X Y : FinPerm} (h : X = Y) :
    toEquiv (eqToHom h) = finCongr (congrArg FinPerm.n h) := by
  subst h; rfl

@[ext] theorem hom_ext {X Y : FinPerm} {f g : X ⟶ Y}
    (h : ∀ i, (toEquiv f i : ℕ) = toEquiv g i) : f = g :=
  Equiv.ext fun i => Fin.ext (h i)

/-- Reduce a `≍` between morphisms to pointwise equality of `Fin` values. -/
theorem hom_heq_iff {X X' Y Y' : FinPerm} (hX : X = X') (hY : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y') :
    f ≍ g ↔ ∀ i, (toEquiv f i : ℕ) = toEquiv g (Fin.cast (congrArg FinPerm.n hX) i) := by
  subst hX hY
  refine ⟨fun h i => by cases h; rfl, fun h => heq_of_eq (hom_ext h)⟩

open BipermutativeCategory

theorem _root_.Nat.add_mul_div_of_lt {a n : ℕ} (b : ℕ) (h : a < n) : (a + n * b) / n = b := by
  rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt h, zero_add]

theorem _root_.Nat.add_mul_mod_of_lt {a n : ℕ} (b : ℕ) (h : a < n) : (a + n * b) % n = a := by
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

instance instMul : StrictMulSymmetricMonoidalCategory FinPerm where
  mulObj X Y := ⟨X.n * Y.n⟩
  mulUnit := ⟨1⟩
  mulHom f g := ofEquiv <|
    finProdFinEquiv.symm.trans ((Equiv.prodCongr (toEquiv f) (toEquiv g)).trans finProdFinEquiv)

  mulObj_assoc X Y Z := by simp [mul_assoc]
  one_mulObj X := by simp
  mulObj_one X := by simp

  id_one_mulHom_heq f := by
    rw [hom_heq_iff (by simp) (by simp)]
    simp; intro i; congr; ext
    rw [Fin.val_cast, i.coe_modNat, Nat.mod_eq_of_lt (by omega)]
  mulHom_id_one_heq f := by
    rw [hom_heq_iff (by simp) (by simp)]
    simp; intro i; congr; ext
    rw [Fin.val_cast, i.coe_divNat, Nat.div_one]
  mulHom_assoc_heq f g h := by
    rw [hom_heq_iff (by simp [mul_assoc]) (by simp [mul_assoc])]
    simp; intro i
    simp only [mul_add, add_assoc]
    congr 2
    . congr 1; ext
      simp only [Fin.coe_modNat, Fin.val_cast]
      rw [Nat.mod_mul_left_mod]
    . congr; ext
      simp only [Fin.coe_modNat, Fin.coe_divNat, Fin.val_cast]
      rw [Nat.mod_mul_left_div_self]
    . simp only [← mul_assoc]
      congr 1
      . rw [mul_comm]
      . congr 2; ext
        simp only [Fin.coe_divNat, Fin.val_cast]
        rw [Nat.div_div_eq_div_mul]
        congr 1
        rw [mul_comm]
  id_mulHom_id X Y := by
    ext; simp [Nat.mod_add_div]
  mulHom_comp_mulHom f₁ f₂ g₁ g₂ := by
    ext; simp

  mulSwap X Y := ofEquiv <|
    finProdFinEquiv.symm.trans ((Equiv.prodComm _ _).trans finProdFinEquiv)
  mulSwap_mulSwap X Y := by
    ext; simp [Nat.mod_add_div]
  mulSwap_natural f g := by
    ext; simp
  mulSwap_hexagon X Y Z := by
    ext ijk; simp
    obtain ⟨⟨i, jk⟩, rfl⟩ := finProdFinEquiv.surjective ijk
    obtain ⟨⟨j, k⟩, rfl⟩ := finProdFinEquiv.surjective jk
    simp only [finProdFinEquiv_apply_val]
    have hi := i.isLt
    have hj := j.isLt
    have hk := k.isLt
    have hkj : k.val + Z.n * j < Y.n * Z.n := by nlinarith
    have hki : k.val + Z.n * i < X.n * Z.n := by nlinarith
    have e₁ : k.val + Z.n * j + Y.n * Z.n * i = k + Z.n * (j + Y.n * i) := by ring
    have e₂ : k.val + Z.n * (i + X.n * j) = k + Z.n * i + X.n * Z.n * j := by ring
    rw [Nat.add_mul_div_of_lt _ hkj, Nat.add_mul_mod_of_lt _ hkj, e₁,
      Nat.add_mul_mod_of_lt _ hk, Nat.add_mul_div_of_lt _ hk,
      Nat.add_mul_div_of_lt _ hj, Nat.add_mul_mod_of_lt _ hj, e₂,
      Nat.add_mul_mod_of_lt _ hki, Nat.add_mul_div_of_lt _ hki,
      Nat.add_mul_div_of_lt _ hk]
    ring

@[simp] theorem _root_.Fin.cast_castAdd_castAdd {m : ℕ} (i : Fin m) (n p : ℕ) :
    Fin.cast (add_assoc m n p) (.castAdd p (.castAdd n i)) = .castAdd (n + p) i := by
  ext; simp

@[simp] theorem _root_.Fin.cast_castAdd_natAdd (m : ℕ) {n : ℕ} (j : Fin n) (p : ℕ) :
    Fin.cast (add_assoc m n p) (.castAdd p (.natAdd m j)) = .natAdd m (.castAdd p j) := by
  ext; simp

@[simp] theorem _root_.Fin.cast_natAdd_add (m n : ℕ) {p : ℕ} (k : Fin p) :
    Fin.cast (add_assoc m n p) (.natAdd (m + n) k) = .natAdd m (.natAdd n k) := by
  ext; simp [add_assoc]

@[simp] theorem _root_.Fin.cast_castAdd_add {m : ℕ} (i : Fin m) (n p : ℕ) :
    Fin.cast (add_assoc m n p).symm (.castAdd (n + p) i) = .castAdd p (.castAdd n i) := by
  rw [← Fin.cast_castAdd_castAdd, Fin.cast_cast, Fin.cast_eq_self]

@[simp] theorem _root_.Fin.cast_natAdd_castAdd (m : ℕ) {n : ℕ} (j : Fin n) (p : ℕ) :
    Fin.cast (add_assoc m n p).symm (.natAdd m (.castAdd p j)) = .castAdd p (.natAdd m j) := by
  rw [← Fin.cast_castAdd_natAdd, Fin.cast_cast, Fin.cast_eq_self]

@[simp] theorem _root_.Fin.cast_natAdd_natAdd (m n : ℕ) {p : ℕ} (k : Fin p) :
    Fin.cast (add_assoc m n p).symm (.natAdd m (.natAdd n k)) = .natAdd (m + n) k := by
  rw [← Fin.cast_natAdd_add, Fin.cast_cast, Fin.cast_eq_self]

instance instAdd : StrictAddSymmetricMonoidalCategory FinPerm where
  addObj X Y := ⟨X.n + Y.n⟩
  addUnit := ⟨0⟩
  addHom f g := ofEquiv <|
    finSumFinEquiv.symm.trans ((Equiv.sumCongr (toEquiv f) (toEquiv g)).trans finSumFinEquiv)

  addObj_assoc X Y Z := by simp [add_assoc]
  zero_addObj X := by simp
  addObj_zero X := by simp

  id_zero_addHom_heq {X Y} f := by
    rw [hom_heq_iff (by simp) (by simp)]
    simp; intro i
    set j : Fin X.n := i.cast (by omega)
    have : i = j.natAdd 0 := by ext; simp [j]
    rw [this, finSumFinEquiv_symm_apply_natAdd]
    simp
  addHom_id_zero_heq {X Y} f := by
    rw [hom_heq_iff (by simp) (by simp)]
    simp; intro i
    set j : Fin (X.n + 0) := i.cast (by omega)
    have : i = j.castAdd 0 := by ext; simp [j]
    rw [this, finSumFinEquiv_symm_apply_castAdd]
    simp
    rw [finSumFinEquiv_apply_left]
    simp
  addHom_assoc_heq {X₁ Y₁ X₂ Y₂ X₃ Y₃} f g h := by
    rw [hom_heq_iff (by simp [add_assoc]) (by simp [add_assoc])]
    simp; intro ijk
    obtain ⟨ij | k, rfl⟩ := finSumFinEquiv.surjective ijk
    . obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective ij <;> simp
    . simp; ring

  id_addHom_id X Y := by simp
  addHom_comp_addHom f₁ f₂ g₁ g₂ := by ext i; simp

  addSwap X Y := ofEquiv finAddFlip
  addSwap_addSwap X Y := by
    ext; simp [finAddFlip]
  addSwap_natural f g := by
    ext ij; simp [finAddFlip]
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective ij <;> simp
  addSwap_hexagon X Y Z := by
    ext ijk; simp
    obtain ⟨i | jk, rfl⟩ := finSumFinEquiv.surjective ijk
    . simp [add_assoc]
    . obtain ⟨j | k, rfl⟩ := finSumFinEquiv.surjective jk <;> simp

@[simp] theorem mulObj_n (X Y : FinPerm) : (X ◆ Y).n = X.n * Y.n := rfl
@[simp] theorem mulUnit_n : (𝐈_ FinPerm).n = 1 := rfl
@[simp] theorem addObj_n (X Y : FinPerm) : (X ◇ Y).n = X.n + Y.n := rfl
@[simp] theorem addUnit_n : (𝐎_ FinPerm).n = 0 := rfl

theorem toEquiv_mulHom_finProdFinEquiv {X₁ Y₁ X₂ Y₂ : FinPerm} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (i : Fin X₁.n) (j : Fin X₂.n) :
    toEquiv (f ◆ₘ g) (finProdFinEquiv (i, j)) = finProdFinEquiv ⟨toEquiv f i, toEquiv g j⟩ := by
  dsimp [toEquiv, mulHom]
  simp

theorem toEquiv_addHom_castAdd {X₁ Y₁ X₂ Y₂ : FinPerm} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (i : Fin X₁.n) :
    toEquiv (f ◇ₘ g) (Fin.castAdd X₂.n i) = Fin.castAdd Y₂.n (toEquiv f i) := by
  dsimp [toEquiv, addHom]
  simp

theorem toEquiv_addHom_natAdd {X₁ Y₁ X₂ Y₂ : FinPerm} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (j : Fin X₂.n) :
    toEquiv (f ◇ₘ g) (Fin.natAdd X₁.n j) = Fin.natAdd Y₁.n (toEquiv g j) := by
  dsimp [toEquiv, addHom]
  simp

@[simp] theorem _root_.Fin.cast_finProdFinEquiv_castAdd
    {m : ℕ} (i : Fin m) (n : ℕ) {p : ℕ} (k : Fin p) :
    Fin.cast (add_mul m n p) (finProdFinEquiv ⟨.castAdd n i, k⟩) =
    .castAdd (n * p) (finProdFinEquiv ⟨i, k⟩) := by
  ext; simp

@[simp] theorem _root_.Fin.cast_finProdFinEquiv_natAdd
    (m : ℕ) {n : ℕ} (j : Fin n) {p : ℕ} (k : Fin p) :
    Fin.cast (add_mul m n p) (finProdFinEquiv ⟨.natAdd m j, k⟩) =
    .natAdd (m * p) (finProdFinEquiv ⟨j, k⟩) := by
  ext; simp; ring

theorem toEquiv_mulSwap_finProdFinEquiv
    {X Y : FinPerm} (i : Fin X.n) (j : Fin Y.n) :
    toEquiv (σ_◆ X Y) (finProdFinEquiv ⟨i, j⟩) = finProdFinEquiv ⟨j, i⟩ := by
  ext; simp [mulSwap]

theorem toEquiv_addSwap_castAdd
    {X : FinPerm} (i : Fin X.n) (Y : FinPerm) :
    toEquiv (σ_◇ X Y) (Fin.castAdd Y.n i) = Fin.natAdd Y.n i := by
  ext; simp [addSwap]

theorem toEquiv_addSwap_natAdd
    (X : FinPerm) {Y : FinPerm} (j : Fin Y.n) :
    toEquiv (σ_◇ X Y) (Fin.natAdd X.n j) = Fin.castAdd X.n j := by
  ext; simp [addSwap]

instance : BipermutativeCategoryBase FinPerm where
  zero_mulObj X := by ext; simp
  id_zero_mulHom_heq {X Y} f := by
    rw [hom_heq_iff (by ext; simp) (by ext; simp)]
    simp; intro i
    exact (i.cast (by simp)).elim0

  mulObj_zero X := by ext; simp
  mulHom_id_zero_heq f := by
    rw [hom_heq_iff (by ext; simp) (by ext; simp)]
    simp
  addObj_mulObj X Y Z := by ext; simp [add_mul]
  addHom_mulHom_heq {X₁ Y₁ X₂ Y₂ X₃ Y₃} f g h := by
    rw [hom_heq_iff (by ext; simp [add_mul]) (by ext; simp [add_mul])]
    simp; intro ijk
    obtain ⟨⟨ij, k⟩, rfl⟩ := finProdFinEquiv.surjective ijk
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective ij
    . simp only [finSumFinEquiv_apply_left, Fin.cast_finProdFinEquiv_castAdd]
      rw [toEquiv_mulHom_finProdFinEquiv, toEquiv_addHom_castAdd]
      erw [toEquiv_addHom_castAdd]
      rw [toEquiv_mulHom_finProdFinEquiv]
      simp
    . simp only [finSumFinEquiv_apply_right, Fin.cast_finProdFinEquiv_natAdd]
      rw [toEquiv_mulHom_finProdFinEquiv, toEquiv_addHom_natAdd]
      erw [toEquiv_addHom_natAdd]
      rw [toEquiv_mulHom_finProdFinEquiv]
      simp; ring

theorem toEquiv_distrib_castAdd {X Y : FinPerm} (i : Fin X.n) (j : Fin Y.n) (Z : FinPerm) :
    toEquiv (δ_ X Y Z) (finProdFinEquiv (i, Fin.castAdd Z.n j)) =
    Fin.castAdd (X.n * Z.n) (finProdFinEquiv (i, j)) := by
  simp [distrib]
  rw [toEquiv_mulSwap_finProdFinEquiv, Fin.cast_finProdFinEquiv_castAdd]
  erw [toEquiv_addHom_castAdd]
  rw [toEquiv_mulSwap_finProdFinEquiv]
  simp

theorem toEquiv_distrib_natAdd (X Y : FinPerm) {Z : FinPerm} (i : Fin X.n) (k : Fin Z.n) :
    toEquiv (δ_ X Y Z) (finProdFinEquiv (i, Fin.natAdd Y.n k)) =
    Fin.natAdd (X.n * Y.n) (finProdFinEquiv (i, k)) := by
  simp [distrib]
  rw [toEquiv_mulSwap_finProdFinEquiv, Fin.cast_finProdFinEquiv_natAdd]
  erw [toEquiv_addHom_natAdd]
  rw [toEquiv_mulSwap_finProdFinEquiv]
  simp

theorem toEquiv_addMedial_castAdd_castAdd
    {X : FinPerm} (i : Fin X.n) (Y Z W : FinPerm) :
    toEquiv (addMedial X Y Z W) (Fin.castAdd (Z.n + W.n) (Fin.castAdd Y.n i)) =
    Fin.castAdd (Y.n + W.n) (Fin.castAdd Z.n i) := by
  simp [addMedial_def]
  erw [toEquiv_addHom_castAdd, toEquiv_addHom_castAdd, toEquiv_addHom_castAdd]
  ext; simp

theorem toEquiv_addMedial_castAdd_natAdd
    (X : FinPerm) {Y : FinPerm} (j : Fin Y.n) (Z W : FinPerm) :
    toEquiv (addMedial X Y Z W) (Fin.castAdd (Z.n + W.n) (Fin.natAdd X.n j)) =
    Fin.natAdd (X.n + Z.n) (Fin.castAdd W.n j) := by
  simp [addMedial_def]
  erw [toEquiv_addHom_natAdd, toEquiv_addHom_natAdd, toEquiv_addHom_natAdd]
  simp
  erw [toEquiv_addHom_castAdd, toEquiv_addSwap_castAdd]
  ext; simp

theorem toEquiv_addMedial_natAdd_castAdd
    (X Y : FinPerm) {Z : FinPerm} (k : Fin Z.n) (W : FinPerm) :
    toEquiv (addMedial X Y Z W) (Fin.natAdd (X.n + Y.n) (Fin.castAdd W.n k)) =
    Fin.castAdd (Y.n + W.n) (Fin.natAdd X.n k) := by
  simp [addMedial_def]
  erw [toEquiv_addHom_natAdd, toEquiv_addHom_natAdd, toEquiv_addHom_natAdd]
  simp
  erw [toEquiv_addHom_castAdd, toEquiv_addSwap_natAdd]
  ext; simp

theorem toEquiv_addMedial_natAdd_natAdd
    (X Y Z : FinPerm) {W : FinPerm} (l : Fin W.n) :
    toEquiv (addMedial X Y Z W) (Fin.natAdd (X.n + Y.n) (Fin.natAdd Z.n l)) =
    Fin.natAdd (X.n + Z.n) (Fin.natAdd Y.n l) := by
  simp [addMedial_def]
  erw [toEquiv_addHom_natAdd, toEquiv_addHom_natAdd, toEquiv_addHom_natAdd]
  simp
  erw [toEquiv_addHom_natAdd]
  ext; simp

instance : BipermutativeCategory FinPerm where
  distrib_square X Y Z := by
    ext ijk; simp
    obtain ⟨⟨ij, k⟩, rfl⟩ := finProdFinEquiv.surjective ijk
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective ij
    . simp only [addObj_n, finSumFinEquiv_apply_left, Fin.cast_finProdFinEquiv_castAdd]
      erw [toEquiv_addSwap_castAdd]
      rw [toEquiv_mulHom_finProdFinEquiv, toEquiv_addSwap_castAdd]
      simp; ring
    . simp only [addObj_n, finSumFinEquiv_apply_right, Fin.cast_finProdFinEquiv_natAdd]
      erw [toEquiv_addSwap_natAdd]
      rw [toEquiv_mulHom_finProdFinEquiv, toEquiv_addSwap_natAdd]
      simp
  distrib_pentagon X Y Z W := by
    ext ijkl; simp
    obtain ⟨⟨ij, kl⟩, rfl⟩ := finProdFinEquiv.surjective ijkl
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective ij <;>
    obtain ⟨k | l, rfl⟩ := finSumFinEquiv.surjective kl
    . simp only [addObj_n, finSumFinEquiv_apply_left, Fin.cast_finProdFinEquiv_castAdd]
      erw [toEquiv_addHom_castAdd]
      rw [toEquiv_distrib_castAdd]
      erw [toEquiv_addMedial_castAdd_castAdd]
      rw [toEquiv_distrib_castAdd]
      erw [toEquiv_addHom_castAdd]
      simp
    . simp only [addObj_n, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.cast_finProdFinEquiv_castAdd]
      erw [toEquiv_addHom_castAdd]
      rw [toEquiv_distrib_natAdd]
      erw [toEquiv_addMedial_castAdd_natAdd]
      rw [toEquiv_distrib_natAdd]
      erw [toEquiv_addHom_natAdd]
      simp
    . simp only [addObj_n, finSumFinEquiv_apply_right, finSumFinEquiv_apply_left,
        Fin.cast_finProdFinEquiv_natAdd]
      erw [toEquiv_addHom_natAdd]
      rw [toEquiv_distrib_castAdd]
      erw [toEquiv_addMedial_natAdd_castAdd]
      rw [toEquiv_distrib_castAdd]
      erw [toEquiv_addHom_castAdd]
      simp
    . simp only [addObj_n, finSumFinEquiv_apply_right, Fin.cast_finProdFinEquiv_natAdd]
      erw [toEquiv_addHom_natAdd]
      rw [toEquiv_distrib_natAdd]
      erw [toEquiv_addMedial_natAdd_natAdd]
      rw [toEquiv_distrib_natAdd]
      erw [toEquiv_addHom_natAdd]
      simp

end FinPerm

end FreeQuantum
