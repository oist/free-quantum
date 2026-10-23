import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.EqToHom
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Group.Action.Defs

namespace FreeQuantum

open CategoryTheory

/-!
# Strict bipermutative categories (Carette et al. 2026, SI Definition S1)

Design:
- `◆` and `◇` are two parallel class hierarchies, `StrictMul…` and `StrictAdd…`, which
  `BipermutativeCategory` extends together, as Mathlib's `Ring` extends the `Mul`/`Add` hierarchies.
- Each monoidal layer is split into data (`…Struct`, carrying the notation) and laws, as Mathlib's
  `MonoidalCategoryStruct`/`MonoidalCategory`, so the laws are stated in notation.
- Associativity/unit are `Eq` rather than `≅`, so there is no associator/unitor. Morphism-level
  axioms whose source/target only agree up to one of these equations use `HEq`.
- `◇` lemmas are transported from their `◆` counterparts via `toMul`, which views a `StrictAdd…`
  structure as a `StrictMul…` one.
- All lemmas and notation live in `BipermutativeCategory`; each class exports its fields there.
- `BipermutativeCategoryBase` holds the axioms of Definition S1 not involving `δ_`;
  `BipermutativeCategory` adds the coherence axioms stated with it.

Naming:
- `one` is `𝐈` and `zero` is `𝐎`, whichever operation the lemma is about.
- `distrib` is distributivity: the morphism `δ_` and the coherence laws `distrib_square`/`distrib_pentagon`;
  the distributivity equation itself is `addObj_mulObj`.
- A lemma whose conclusion is `≍` ends in `_heq`; Eq lemmas carry no suffix. When the RHS must be named,
  they read `lhs_heq_rhs` / `lhs_eq_rhs`.
-/

namespace BipermutativeCategory

variable {C : Type*} [Category C] {X X' Y Y' : C}

theorem id_eq_conj_eqToHom (h : X = X') : 𝟙 X = eqToHom h ≫ 𝟙 X' ≫ eqToHom h.symm := by simp

theorem eq_conj_eqToHom_iff (f : X ⟶ Y) (g : X' ⟶ Y') (hX : X = X') (hY : Y = Y') :
    f = eqToHom hX ≫ g ≫ eqToHom hY.symm ↔ eqToHom hX.symm ≫ f ≫ eqToHom hY = g := by
  subst hX hY
  constructor <;> simp

end BipermutativeCategory
open BipermutativeCategory

class StrictMulMonoidalCategoryStruct (C : Type*) [Category C] where
  mulObj : C → C → C
  mulUnit : C
  mulHom {X₁ Y₁ X₂ Y₂ : C} : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → (mulObj X₁ X₂ ⟶ mulObj Y₁ Y₂)

namespace BipermutativeCategory

scoped infixr:95 " ◆ " => StrictMulMonoidalCategoryStruct.mulObj
scoped infixr:95 " ◆ₘ " => StrictMulMonoidalCategoryStruct.mulHom
scoped notation "𝐈" => StrictMulMonoidalCategoryStruct.mulUnit
scoped notation "𝐈_ " D:arg => StrictMulMonoidalCategoryStruct.mulUnit (C := D)

end BipermutativeCategory

class StrictMulMonoidalCategory (C : Type*) [Category C] extends
    StrictMulMonoidalCategoryStruct C where
  mulObj_assoc (X Y Z : C) : (X ◆ Y) ◆ Z = X ◆ (Y ◆ Z)
  one_mulObj (X : C) : 𝐈 ◆ X = X
  mulObj_one (X : C) : X ◆ 𝐈 = X

  id_one_mulHom_heq {X Y : C} (f : X ⟶ Y) : 𝟙 𝐈 ◆ₘ f ≍ f
  mulHom_id_one_heq {X Y : C} (f : X ⟶ Y) : f ◆ₘ 𝟙 𝐈 ≍ f
  mulHom_assoc_heq {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
      (f ◆ₘ g) ◆ₘ h ≍ f ◆ₘ (g ◆ₘ h)
  id_mulHom_id (X Y : C) : (𝟙 X) ◆ₘ (𝟙 Y) = 𝟙 (X ◆ Y)
  mulHom_comp_mulHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
      f₁ ◆ₘ f₂ ≫ g₁ ◆ₘ g₂ = (f₁ ≫ g₁) ◆ₘ (f₂ ≫ g₂)

namespace BipermutativeCategory

export StrictMulMonoidalCategoryStruct (mulObj mulUnit mulHom)
export StrictMulMonoidalCategory (
  mulObj_assoc one_mulObj mulObj_one
  id_one_mulHom_heq mulHom_id_one_heq mulHom_assoc_heq id_mulHom_id mulHom_comp_mulHom)

variable {C : Type*} [Category C] [StrictMulMonoidalCategory C]

theorem mulHom_interchange {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ◆ₘ 𝟙 X₂ ≫ 𝟙 Y₁ ◆ₘ g = 𝟙 X₁ ◆ₘ g ≫ f ◆ₘ 𝟙 Y₂ := by
  rw [mulHom_comp_mulHom, mulHom_comp_mulHom, Category.comp_id, Category.id_comp,
    Category.id_comp, Category.comp_id]

/-- Congr of `mulHom`. Use `conj_eqToHom_iff_heq` for inverse direction. -/
theorem mulHom_congr_heq {X₁ Y₁ X₂ Y₂ X₁' Y₁' X₂' Y₂' : C}
    {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂} {f' : X₁' ⟶ Y₁'} {g' : X₂' ⟶ Y₂'}
    (hX₁ : X₁ = X₁') (hY₁ : Y₁ = Y₁') (hX₂ : X₂ = X₂') (hY₂ : Y₂ = Y₂')
    (hf : f ≍ f') (hg : g ≍ g') :
    f ◆ₘ g ≍ f' ◆ₘ g' := by
  subst hX₁ hY₁ hX₂ hY₂
  cases hf; cases hg; rfl

theorem mulHom_congr_left_heq {X₁ Y₁ X₂ Y₂ X₁' Y₁' : C}
    {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂} {f' : X₁' ⟶ Y₁'}
    (hX₁ : X₁ = X₁') (hY₁ : Y₁ = Y₁') (hf : f ≍ f') :
    f ◆ₘ g ≍ f' ◆ₘ g := mulHom_congr_heq hX₁ hY₁ rfl rfl hf (heq_iff_eq.mpr rfl)

theorem mulHom_congr_right_heq {X₁ Y₁ X₂ Y₂ X₂' Y₂' : C}
    {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂} {g' : X₂' ⟶ Y₂'}
    (hX₂ : X₂ = X₂') (hY₂ : Y₂ = Y₂') (hg : g ≍ g') :
    f ◆ₘ g ≍ f ◆ₘ g' := mulHom_congr_heq rfl rfl hX₂ hY₂ (heq_iff_eq.mpr rfl) hg

@[simp] theorem eqToHom_mulHom_eqToHom {X₁ Y₁ X₂ Y₂ : C} (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂) :
    eqToHom h₁ ◆ₘ eqToHom h₂ = eqToHom (congrArg₂ (· ◆ ·) h₁ h₂) := by
  subst h₁ h₂; simp [id_mulHom_id]

@[simp] theorem id_mulHom_eqToHom (X : C) {Y₁ Y₂ : C} (h : Y₁ = Y₂) :
    𝟙 X ◆ₘ eqToHom h = eqToHom (congrArg (X ◆ ·) h) := by
  subst h; simp [id_mulHom_id]

@[simp] theorem eqToHom_mulHom_id {X₁ X₂ : C} (h : X₁ = X₂) (Y : C) :
    eqToHom h ◆ₘ 𝟙 Y = eqToHom (congrArg (· ◆ Y) h) := by
  subst h; simp [id_mulHom_id]

theorem conj_eqToHom_mulHom {X₁ X₁' Y₁ Y₁' X₂ Y₂ : C} (h : X₁ = X₁') (h' : Y₁' = Y₁)
    (f : X₁' ⟶ Y₁') (g : X₂ ⟶ Y₂) :
    (eqToHom h ≫ f ≫ eqToHom h') ◆ₘ g =
      eqToHom (congrArg (· ◆ X₂) h) ≫ f ◆ₘ g ≫ eqToHom (congrArg (· ◆ Y₂) h') := by
  subst h h'; simp

theorem mulHom_conj_eqToHom {X₁ Y₁ X₂ X₂' Y₂ Y₂' : C} (h : X₂ = X₂') (h' : Y₂' = Y₂)
    (f : X₁ ⟶ Y₁) (g : X₂' ⟶ Y₂') :
    f ◆ₘ (eqToHom h ≫ g ≫ eqToHom h') =
      eqToHom (congrArg (X₁ ◆ ·) h) ≫ f ◆ₘ g ≫ eqToHom (congrArg (Y₁ ◆ ·) h') := by
  subst h h'; simp

theorem id_one_mulHom {X Y : C} (f : X ⟶ Y) :
    𝟙 𝐈 ◆ₘ f = eqToHom (one_mulObj X) ≫ f ≫ eqToHom (one_mulObj Y).symm :=
  (conj_eqToHom_iff_heq _ _ (one_mulObj X) (one_mulObj Y)).mpr (id_one_mulHom_heq f)

theorem mulHom_id_one {X Y : C} (f : X ⟶ Y) :
    f ◆ₘ 𝟙 𝐈 = eqToHom (mulObj_one X) ≫ f ≫ eqToHom (mulObj_one Y).symm :=
  (conj_eqToHom_iff_heq _ _ (mulObj_one X) (mulObj_one Y)).mpr (mulHom_id_one_heq f)

theorem mulHom_assoc {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    (f ◆ₘ g) ◆ₘ h =
      eqToHom (mulObj_assoc X₁ X₂ X₃) ≫ f ◆ₘ (g ◆ₘ h) ≫ eqToHom (mulObj_assoc Y₁ Y₂ Y₃).symm :=
  (conj_eqToHom_iff_heq _ _ (mulObj_assoc X₁ X₂ X₃) (mulObj_assoc Y₁ Y₂ Y₃)).mpr
    (mulHom_assoc_heq f g h)

abbrev Scalar (C) [Category C] [StrictMulMonoidalCategory C] := 𝐈_ C ⟶ 𝐈_ C

theorem scalar_mulHom_heq (s t : Scalar C) : s ◆ₘ t ≍ t ≫ s := by
  have : s ◆ₘ t = (𝟙 _) ◆ₘ t ≫ s ◆ₘ (𝟙 _) := by
    rw [mulHom_comp_mulHom, Category.id_comp, Category.comp_id]
  rw [this]
  apply heq_comp (one_mulObj _) (one_mulObj _) (one_mulObj _)
    (id_one_mulHom_heq t) (mulHom_id_one_heq s)

theorem scalar_mulHom_heq_comp (s t : Scalar C) : s ◆ₘ t ≍ s ≫ t := by
  have : s ◆ₘ t = s ◆ₘ (𝟙 _) ≫ (𝟙 _) ◆ₘ t := by
    rw [mulHom_comp_mulHom, Category.id_comp, Category.comp_id]
  rw [this]
  apply heq_comp (one_mulObj _) (one_mulObj _) (one_mulObj _)
    (mulHom_id_one_heq s) (id_one_mulHom_heq t)

theorem scalar_mulHom (s t : Scalar C) :
    s ◆ₘ t = eqToHom (one_mulObj 𝐈) ≫ (t ≫ s) ≫ eqToHom (one_mulObj 𝐈).symm :=
  (conj_eqToHom_iff_heq _ _ (one_mulObj 𝐈) (one_mulObj 𝐈)).mpr (scalar_mulHom_heq s t)

theorem scalar_mulHom_eq_comp (s t : Scalar C) :
    s ◆ₘ t = eqToHom (one_mulObj 𝐈) ≫ (s ≫ t) ≫ eqToHom (one_mulObj 𝐈).symm :=
  (conj_eqToHom_iff_heq _ _ (one_mulObj 𝐈) (one_mulObj 𝐈)).mpr (scalar_mulHom_heq_comp s t)

def smul {X Y : C} (s : Scalar C) (f : X ⟶ Y) : X ⟶ Y :=
  eqToHom (mulObj_one X).symm ≫ f ◆ₘ s ≫ eqToHom (mulObj_one Y)

instance {X Y : C} : SMul (Scalar C) (X ⟶ Y) where
  smul := smul

theorem Scalar.smul_def {X Y : C} (s : Scalar C) (f : X ⟶ Y) :
    s • f = eqToHom (mulObj_one X).symm ≫ f ◆ₘ s ≫ eqToHom (mulObj_one Y) := rfl

/-- `a * b := smul a b`, so on `𝐈 ⟶ 𝐈` the action `s • t` of `Mul.toSMul` and of the hom-set
`SMul` agree by `rfl`. -/
instance : Monoid (Scalar C) where
  mul a b := smul a b
  one := 𝟙 𝐈
  mul_assoc a b c := by
    show (smul (smul a b) c) = (smul a (smul b c))
    simp [smul, conj_eqToHom_mulHom, mulHom_conj_eqToHom, mulHom_assoc]
  one_mul a := by
    show (smul (𝟙 𝐈) a) = a
    simp [smul, mulHom_id_one]
  mul_one a := by
    show (smul a (𝟙 𝐈)) = a
    simp [smul, id_one_mulHom]

theorem Scalar.mul_eq_smul (a b : Scalar C) : a * b = smul a b := rfl

@[simp] theorem Scalar.mul_def (a b : Scalar C) : a * b = b ≫ a := by
  simp [mul_eq_smul, smul, scalar_mulHom_eq_comp]

@[simp] theorem Scalar.one_def : 1 = 𝟙 (𝐈_ C) := rfl

instance : CommMonoid (Scalar C) where
  mul_comm a b := by
    simp only [Scalar.mul_def]
    rw [← cancel_mono (eqToHom (one_mulObj _).symm), ← cancel_epi (eqToHom (one_mulObj _))]
    rw [← scalar_mulHom, ← scalar_mulHom_eq_comp]

instance {X Y : C} : MulAction (Scalar C) (X ⟶ Y) where
  one_smul f := by
    simp [Scalar.smul_def, mulHom_id_one]
  mul_smul s t f := by
    simp only [Scalar.mul_def, Scalar.smul_def]
    rw [conj_eqToHom_mulHom, mulHom_assoc, scalar_mulHom_eq_comp, mulHom_conj_eqToHom]
    simp

section smul_lemmas
variable (s t : Scalar C)
variable {X Y Z : C}
variable (f : X ⟶ Y) (g : Y ⟶ Z)

theorem smul_comp : (s • f) ≫ g = s • (f ≫ g) := by
  simp only [Scalar.smul_def]
  conv_rhs => rw [← Category.comp_id s, ← mulHom_comp_mulHom, mulHom_id_one]
  simp

theorem comp_smul : f ≫ (s • g) = s • (f ≫ g) := by
  simp only [Scalar.smul_def]
  conv_rhs => rw [← Category.id_comp s, ← mulHom_comp_mulHom, mulHom_id_one]
  simp

theorem smul_id_comp : (s • 𝟙 X) ≫ f = s • f := by
  rw [smul_comp, Category.id_comp]

theorem comp_smul_id : f ≫ (s • 𝟙 Y) = s • f := by
  rw [comp_smul, Category.comp_id]

theorem mulHom_smul : f ◆ₘ (s • g) = s • (f ◆ₘ g) := by
  simp only [Scalar.smul_def]
  rw [mulHom_conj_eqToHom, mulHom_assoc]
  simp

end smul_lemmas

end BipermutativeCategory

class StrictMulSymmetricMonoidalCategoryStruct (C : Type*) [Category C] extends
    StrictMulMonoidalCategoryStruct C where
  mulSwap (X Y : C) : X ◆ Y ⟶ Y ◆ X

namespace BipermutativeCategory

scoped notation "σ_◆" => StrictMulSymmetricMonoidalCategoryStruct.mulSwap

end BipermutativeCategory

class StrictMulSymmetricMonoidalCategory (C : Type*) [Category C] extends
    StrictMulSymmetricMonoidalCategoryStruct C, StrictMulMonoidalCategory C where
  mulSwap_mulSwap (X Y : C) : σ_◆ X Y ≫ σ_◆ Y X = 𝟙 _

  mulSwap_natural {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ◆ₘ g ≫ σ_◆ Y₁ Y₂ = σ_◆ X₁ X₂ ≫ g ◆ₘ f

  mulSwap_hexagon (X Y Z : C) :
    σ_◆ X (Y ◆ Z) =
      eqToHom (mulObj_assoc X Y Z).symm ≫
      σ_◆ X Y ◆ₘ 𝟙 Z ≫
      eqToHom (mulObj_assoc Y X Z) ≫
      𝟙 Y ◆ₘ σ_◆ X Z ≫
      eqToHom (mulObj_assoc Y Z X).symm

namespace BipermutativeCategory

export StrictMulSymmetricMonoidalCategoryStruct (mulSwap)
export StrictMulSymmetricMonoidalCategory (mulSwap_mulSwap mulSwap_natural mulSwap_hexagon)

variable {C : Type*} [Category C] [StrictMulSymmetricMonoidalCategory C]
variable (X Y Z W : C)

def mulMedial : (X ◆ Y) ◆ (Z ◆ W) ⟶ (X ◆ Z) ◆ (Y ◆ W) :=
  eqToHom (mulObj_assoc X Y (Z ◆ W)) ≫
    𝟙 _ ◆ₘ eqToHom (mulObj_assoc Y Z W).symm ≫
    𝟙 _ ◆ₘ (σ_◆ Y Z ◆ₘ 𝟙 _) ≫
    𝟙 _ ◆ₘ eqToHom (mulObj_assoc Z Y W) ≫
    eqToHom (mulObj_assoc X Z (Y ◆ W)).symm

theorem mulSwap_one_right :
    σ_◆ X 𝐈 = eqToHom ((mulObj_one X).trans (one_mulObj X).symm) := by
  let α : X ⟶ X := eqToHom (mulObj_one X).symm ≫ σ_◆ X 𝐈 ≫ eqToHom (one_mulObj X)
  let β : X ⟶ X := eqToHom (one_mulObj X).symm ≫ σ_◆ 𝐈 X ≫ eqToHom (mulObj_one X)
  have hαβ : α ≫ β = 𝟙 X := by
    simp [α, β, reassoc_of% mulSwap_mulSwap]
  have hαα : α ≫ α = α := by
    have hσ : ∀ {Y} (h : Y = 𝐈), σ_◆ X Y =
        eqToHom (congrArg (X ◆ ·) h) ≫ σ_◆ X 𝐈 ≫ eqToHom (congrArg (· ◆ X) h).symm := by
      rintro _ rfl; simp
    have := mulSwap_hexagon X 𝐈 𝐈
    rw [hσ (one_mulObj 𝐈), mulHom_id_one, id_one_mulHom] at this
    have e₁ : X = X ◆ (𝐈 ◆ 𝐈) := by rw [one_mulObj, mulObj_one]
    have e₂ : (𝐈 ◆ 𝐈) ◆ X = X := by rw [one_mulObj, one_mulObj]
    replace := congrArg (eqToHom e₁ ≫ · ≫ eqToHom e₂) this
    simp at this
    simp [α, ← this]
  have hα : α = 𝟙 X := by
    rw [← Category.comp_id α, ← hαβ, ← Category.assoc, hαα, hαβ]
  calc σ_◆ X 𝐈 = eqToHom (mulObj_one X) ≫ α ≫ eqToHom (one_mulObj X).symm := by simp [α]
    _ = _ := by rw [hα]; simp

theorem mulSwap_one_left :
    σ_◆ 𝐈 X = eqToHom ((one_mulObj X).trans (mulObj_one X).symm) := by
  calc σ_◆ 𝐈 X = eqToHom ((one_mulObj X).trans (mulObj_one X).symm) ≫ σ_◆ X 𝐈 ≫ σ_◆ 𝐈 X := by
        rw [mulSwap_one_right]; simp
    _ = _ := by rw [mulSwap_mulSwap]; simp

theorem mulSwap_one_right_heq : σ_◆ X 𝐈 ≍ 𝟙 X :=
  (conj_eqToHom_iff_heq _ _ (mulObj_one X) (one_mulObj X)).mp (by simp [mulSwap_one_right])

theorem mulSwap_one_left_heq : σ_◆ 𝐈 X ≍ 𝟙 X :=
  (conj_eqToHom_iff_heq _ _ (one_mulObj X) (mulObj_one X)).mp (by simp [mulSwap_one_left])

theorem mulSwap_eq_conj_eqToHom {X X' Y Y' : C} (hX : X = X') (hY : Y = Y') :
    σ_◆ X Y = eqToHom (by rw [hX, hY]) ≫ σ_◆ X' Y' ≫ eqToHom (by rw [hX, hY]) := by
  subst hX hY; simp

section smul_lemmas
variable (s : Scalar C)
variable {X Y Z : C}
variable (f : X ⟶ Y) (g : Y ⟶ Z)

variable (X) in
theorem scalar_mulHom_id_comm :
    s ◆ₘ 𝟙 X =
      eqToHom ((one_mulObj X).trans (mulObj_one X).symm) ≫ 𝟙 X ◆ₘ s ≫
        eqToHom ((mulObj_one X).trans (one_mulObj X).symm) := by
  calc s ◆ₘ 𝟙 X = (s ◆ₘ 𝟙 X ≫ σ_◆ 𝐈 X) ≫ eqToHom ((mulObj_one X).trans (one_mulObj X).symm) := by
        rw [mulSwap_one_left]; simp
    _ = _ := by rw [mulSwap_natural, mulSwap_one_left]; simp

variable (X) in
theorem scalar_mulHom_id_comm_heq : s ◆ₘ 𝟙 X ≍ 𝟙 X ◆ₘ s :=
  (conj_eqToHom_iff_heq _ _ _ ((mulObj_one X).trans (one_mulObj X).symm).symm).mp
    (scalar_mulHom_id_comm s X)

theorem scalar_mulHom_comm :
    s ◆ₘ g =
      eqToHom ((one_mulObj Y).trans (mulObj_one Y).symm) ≫ g ◆ₘ s ≫
        eqToHom ((mulObj_one Z).trans (one_mulObj Z).symm) := by
  have e₁ : s ◆ₘ g = s ◆ₘ 𝟙 Y ≫ 𝟙 𝐈 ◆ₘ g := by
    rw [mulHom_comp_mulHom, Category.id_comp, Category.comp_id]
  have e₂ : g ◆ₘ s = 𝟙 Y ◆ₘ s ≫ g ◆ₘ 𝟙 𝐈 := by
    rw [mulHom_comp_mulHom, Category.id_comp, Category.comp_id]
  rw [e₁, e₂, scalar_mulHom_id_comm, id_one_mulHom, mulHom_id_one]
  simp

theorem smul_mulHom : (s • f) ◆ₘ g = s • (f ◆ₘ g) := by
  simp only [Scalar.smul_def]
  rw [conj_eqToHom_mulHom, mulHom_assoc, scalar_mulHom_comm, mulHom_conj_eqToHom,
    mulHom_assoc]
  simp

end smul_lemmas

end BipermutativeCategory

class StrictAddMonoidalCategoryStruct (C : Type*) [Category C] where
  addObj : C → C → C
  addUnit : C
  addHom {X₁ Y₁ X₂ Y₂ : C} : (X₁ ⟶ Y₁) → (X₂ ⟶ Y₂) → (addObj X₁ X₂ ⟶ addObj Y₁ Y₂)

namespace BipermutativeCategory

scoped infixr:90 " ◇ " => StrictAddMonoidalCategoryStruct.addObj
scoped infixr:90 " ◇ₘ " => StrictAddMonoidalCategoryStruct.addHom
scoped notation "𝐎" => StrictAddMonoidalCategoryStruct.addUnit
scoped notation "𝐎_ " D:arg => StrictAddMonoidalCategoryStruct.addUnit (C := D)

end BipermutativeCategory

class StrictAddMonoidalCategory (C : Type*) [Category C] extends
    StrictAddMonoidalCategoryStruct C where
  addObj_assoc (X Y Z : C) : (X ◇ Y) ◇ Z = X ◇ (Y ◇ Z)
  zero_addObj (X : C) : 𝐎 ◇ X = X
  addObj_zero (X : C) : X ◇ 𝐎 = X

  id_zero_addHom_heq {X Y : C} (f : X ⟶ Y) : 𝟙 𝐎 ◇ₘ f ≍ f
  addHom_id_zero_heq {X Y : C} (f : X ⟶ Y) : f ◇ₘ 𝟙 𝐎 ≍ f
  addHom_assoc_heq {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
      (f ◇ₘ g) ◇ₘ h ≍ f ◇ₘ (g ◇ₘ h)
  id_addHom_id (X Y : C) : 𝟙 X ◇ₘ 𝟙 Y = 𝟙 (X ◇ Y)
  addHom_comp_addHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂) (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
      f₁ ◇ₘ f₂ ≫ g₁ ◇ₘ g₂ = (f₁ ≫ g₁) ◇ₘ (f₂ ≫ g₂)

namespace BipermutativeCategory

export StrictAddMonoidalCategoryStruct (addObj addUnit addHom)
export StrictAddMonoidalCategory (
  addObj_assoc zero_addObj addObj_zero
  id_zero_addHom_heq addHom_id_zero_heq addHom_assoc_heq id_addHom_id addHom_comp_addHom)

end BipermutativeCategory

/-- `◇` as a `◆`-structure. Not an instance. -/
abbrev StrictAddMonoidalCategory.toMul
    (C : Type*) [Category C] [StrictAddMonoidalCategory C] :
    StrictMulMonoidalCategory C where
  mulObj := addObj
  mulUnit := addUnit
  mulHom := addHom
  mulObj_assoc := addObj_assoc
  one_mulObj := zero_addObj
  mulObj_one := addObj_zero
  id_one_mulHom_heq := id_zero_addHom_heq
  mulHom_id_one_heq := addHom_id_zero_heq
  mulHom_assoc_heq := addHom_assoc_heq
  id_mulHom_id := id_addHom_id
  mulHom_comp_mulHom := addHom_comp_addHom

namespace BipermutativeCategory

variable {C : Type*} [Category C] [StrictAddMonoidalCategory C]

theorem addHom_interchange {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ◇ₘ 𝟙 X₂ ≫ 𝟙 Y₁ ◇ₘ g = 𝟙 X₁ ◇ₘ g ≫ f ◇ₘ 𝟙 Y₂ :=
  @mulHom_interchange C _ (StrictAddMonoidalCategory.toMul C) _ _ _ _ f g

theorem addHom_congr_heq {X₁ Y₁ X₂ Y₂ X₁' Y₁' X₂' Y₂' : C}
    {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂} {f' : X₁' ⟶ Y₁'} {g' : X₂' ⟶ Y₂'}
    (hX₁ : X₁ = X₁') (hY₁ : Y₁ = Y₁') (hX₂ : X₂ = X₂') (hY₂ : Y₂ = Y₂')
    (hf : f ≍ f') (hg : g ≍ g') :
    f ◇ₘ g ≍ f' ◇ₘ g' :=
  @mulHom_congr_heq C _ (StrictAddMonoidalCategory.toMul C)
    _ _ _ _ _ _ _ _ _ _ _ _ hX₁ hY₁ hX₂ hY₂ hf hg

theorem addHom_congr_left_heq {X₁ Y₁ X₂ Y₂ X₁' Y₁' : C}
    {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂} {f' : X₁' ⟶ Y₁'}
    (hX₁ : X₁ = X₁') (hY₁ : Y₁ = Y₁') (hf : f ≍ f') :
    f ◇ₘ g ≍ f' ◇ₘ g :=
  @mulHom_congr_left_heq C _ (StrictAddMonoidalCategory.toMul C)
    _ _ _ _ _ _ _ _ _ hX₁ hY₁ hf

theorem addHom_congr_right_heq {X₁ Y₁ X₂ Y₂ X₂' Y₂' : C}
    {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂} {g' : X₂' ⟶ Y₂'}
    (hX₂ : X₂ = X₂') (hY₂ : Y₂ = Y₂') (hg : g ≍ g') :
    f ◇ₘ g ≍ f ◇ₘ g' :=
  @mulHom_congr_right_heq C _ (StrictAddMonoidalCategory.toMul C)
    _ _ _ _ _ _ _ _ _ hX₂ hY₂ hg

@[simp] theorem eqToHom_addHom_eqToHom {X₁ Y₁ X₂ Y₂ : C} (h₁ : X₁ = Y₁) (h₂ : X₂ = Y₂) :
    eqToHom h₁ ◇ₘ eqToHom h₂ = eqToHom (congrArg₂ (· ◇ ·) h₁ h₂) :=
  @eqToHom_mulHom_eqToHom C _ (StrictAddMonoidalCategory.toMul C) _ _ _ _ h₁ h₂

@[simp] theorem id_addHom_eqToHom (X : C) {Y₁ Y₂ : C} (h : Y₁ = Y₂) :
    𝟙 X ◇ₘ eqToHom h = eqToHom (congrArg (X ◇ ·) h) :=
  @id_mulHom_eqToHom C _ (StrictAddMonoidalCategory.toMul C) X _ _ h

@[simp] theorem eqToHom_addHom_id {X₁ X₂ : C} (h : X₁ = X₂) (Y : C) :
    eqToHom h ◇ₘ 𝟙 Y = eqToHom (congrArg (· ◇ Y) h) :=
  @eqToHom_mulHom_id C _ (StrictAddMonoidalCategory.toMul C) _ _ h Y

theorem conj_eqToHom_addHom {X₁ X₁' Y₁ Y₁' X₂ Y₂ : C} (h : X₁ = X₁') (h' : Y₁' = Y₁)
    (f : X₁' ⟶ Y₁') (g : X₂ ⟶ Y₂) :
    (eqToHom h ≫ f ≫ eqToHom h') ◇ₘ g =
      eqToHom (congrArg (· ◇ X₂) h) ≫ f ◇ₘ g ≫ eqToHom (congrArg (· ◇ Y₂) h') :=
  @conj_eqToHom_mulHom C _ (StrictAddMonoidalCategory.toMul C) _ _ _ _ _ _ h h' f g

theorem addHom_conj_eqToHom {X₁ Y₁ X₂ X₂' Y₂ Y₂' : C} (h : X₂ = X₂') (h' : Y₂' = Y₂)
    (f : X₁ ⟶ Y₁) (g : X₂' ⟶ Y₂') :
    f ◇ₘ (eqToHom h ≫ g ≫ eqToHom h') =
      eqToHom (congrArg (X₁ ◇ ·) h) ≫ f ◇ₘ g ≫ eqToHom (congrArg (Y₁ ◇ ·) h') :=
  @mulHom_conj_eqToHom C _ (StrictAddMonoidalCategory.toMul C) _ _ _ _ _ _ h h' f g

theorem id_zero_addHom {X Y : C} (f : X ⟶ Y) :
    𝟙 𝐎 ◇ₘ f = eqToHom (zero_addObj X) ≫ f ≫ eqToHom (zero_addObj Y).symm :=
  @id_one_mulHom C _ (StrictAddMonoidalCategory.toMul C) _ _ f

theorem addHom_id_zero {X Y : C} (f : X ⟶ Y) :
    f ◇ₘ 𝟙 𝐎 = eqToHom (addObj_zero X) ≫ f ≫ eqToHom (addObj_zero Y).symm :=
  @mulHom_id_one C _ (StrictAddMonoidalCategory.toMul C) _ _ f

theorem addHom_assoc {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    (f ◇ₘ g) ◇ₘ h =
      eqToHom (addObj_assoc X₁ X₂ X₃) ≫ f ◇ₘ (g ◇ₘ h) ≫ eqToHom (addObj_assoc Y₁ Y₂ Y₃).symm :=
  @mulHom_assoc C _ (StrictAddMonoidalCategory.toMul C) _ _ _ _ _ _ f g h

end BipermutativeCategory

class StrictAddSymmetricMonoidalCategoryStruct (C : Type*) [Category C] extends
    StrictAddMonoidalCategoryStruct C where
  addSwap (X Y : C) : X ◇ Y ⟶ Y ◇ X

namespace BipermutativeCategory

scoped notation "σ_◇" => StrictAddSymmetricMonoidalCategoryStruct.addSwap

end BipermutativeCategory

class StrictAddSymmetricMonoidalCategory (C : Type*) [Category C] extends
    StrictAddSymmetricMonoidalCategoryStruct C, StrictAddMonoidalCategory C where
  addSwap_addSwap (X Y : C) : σ_◇ X Y ≫ σ_◇ Y X = 𝟙 _

  addSwap_natural {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    f ◇ₘ g ≫ σ_◇ Y₁ Y₂ = σ_◇ X₁ X₂ ≫ g ◇ₘ f

  addSwap_hexagon (X Y Z : C) :
    σ_◇ X (Y ◇ Z) =
      eqToHom (addObj_assoc X Y Z).symm ≫
      σ_◇ X Y ◇ₘ 𝟙 Z ≫
      eqToHom (addObj_assoc Y X Z) ≫
      𝟙 Y ◇ₘ σ_◇ X Z ≫
      eqToHom (addObj_assoc Y Z X).symm

namespace BipermutativeCategory

export StrictAddSymmetricMonoidalCategoryStruct (addSwap)
export StrictAddSymmetricMonoidalCategory (addSwap_addSwap addSwap_natural addSwap_hexagon)

end BipermutativeCategory

/-- `◇` as a symmetric `◆`-structure. Not an instance. -/
abbrev StrictAddSymmetricMonoidalCategory.toMul
    (C : Type*) [Category C] [StrictAddSymmetricMonoidalCategory C] :
    StrictMulSymmetricMonoidalCategory C where
  __ := StrictAddMonoidalCategory.toMul C
  mulSwap := addSwap
  mulSwap_mulSwap := addSwap_addSwap
  mulSwap_natural := addSwap_natural
  mulSwap_hexagon := addSwap_hexagon

namespace BipermutativeCategory

variable {C : Type*} [Category C] [StrictAddSymmetricMonoidalCategory C]
variable (X Y Z W : C)

def addMedial : (X ◇ Y) ◇ (Z ◇ W) ⟶ (X ◇ Z) ◇ (Y ◇ W) :=
  @mulMedial C _ (StrictAddSymmetricMonoidalCategory.toMul C) X Y Z W

theorem addMedial_def (X Y Z W : C) :
    addMedial X Y Z W =
      eqToHom (addObj_assoc X Y (Z ◇ W)) ≫
        𝟙 X ◇ₘ eqToHom (addObj_assoc Y Z W).symm ≫
        𝟙 X ◇ₘ (σ_◇ Y Z ◇ₘ 𝟙 W) ≫
        𝟙 X ◇ₘ eqToHom (addObj_assoc Z Y W) ≫
        eqToHom (addObj_assoc X Z (Y ◇ W)).symm := rfl

theorem addSwap_zero_right_heq : σ_◇ X 𝐎 ≍ 𝟙 X :=
  @mulSwap_one_right_heq C _ (StrictAddSymmetricMonoidalCategory.toMul C) X

theorem addSwap_zero_left_heq : σ_◇ 𝐎 X ≍ 𝟙 X :=
  @mulSwap_one_left_heq C _ (StrictAddSymmetricMonoidalCategory.toMul C) X

theorem addSwap_zero_right : σ_◇ X 𝐎 = eqToHom ((addObj_zero X).trans (zero_addObj X).symm) :=
  @mulSwap_one_right C _ (StrictAddSymmetricMonoidalCategory.toMul C) X

theorem addSwap_zero_left : σ_◇ 𝐎 X = eqToHom ((zero_addObj X).trans (addObj_zero X).symm) :=
  @mulSwap_one_left C _ (StrictAddSymmetricMonoidalCategory.toMul C) X

theorem addSwap_eq_conj_eqToHom {X X' Y Y' : C} (hX : X = X') (hY : Y = Y') :
    σ_◇ X Y = eqToHom (by rw [hX, hY]) ≫ σ_◇ X' Y' ≫ eqToHom (by rw [hX, hY]) := by
  subst hX hY; simp

theorem addMedial_eq_conj_eqToHom {X X' Y Y' Z Z' W W' : C}
    (hX : X = X') (hY : Y = Y') (hZ : Z = Z') (hW : W = W') :
    addMedial X Y Z W =
      eqToHom (by rw [hX, hY, hZ, hW]) ≫
      addMedial X' Y' Z' W' ≫
      eqToHom (by rw [hX, hY, hZ, hW]) := by
  subst hX hY hZ hW; simp

end BipermutativeCategory

class BipermutativeCategoryBase (C : Type*) [Category C] extends
  StrictMulSymmetricMonoidalCategory C, StrictAddSymmetricMonoidalCategory C where
  zero_mulObj (X : C) : 𝐎 ◆ X = 𝐎
  id_zero_mulHom_heq {X Y : C} (f : X ⟶ Y) : 𝟙 𝐎 ◆ₘ f ≍ 𝟙 (𝐎_ C)
  mulObj_zero (X : C) : X ◆ 𝐎 = 𝐎
  mulHom_id_zero_heq {X Y : C} (f : X ⟶ Y) : f ◆ₘ 𝟙 𝐎 ≍ 𝟙 (𝐎_ C)
  addObj_mulObj (X Y Z : C) : (X ◇ Y) ◆ Z = (X ◆ Z) ◇ (Y ◆ Z)
  addHom_mulHom_heq {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
      (f ◇ₘ g) ◆ₘ h ≍ (f ◆ₘ h) ◇ₘ (g ◆ₘ h)

namespace BipermutativeCategory

export BipermutativeCategoryBase (
  zero_mulObj id_zero_mulHom_heq mulObj_zero mulHom_id_zero_heq addObj_mulObj addHom_mulHom_heq)

variable {C : Type*} [Category C] [BipermutativeCategoryBase C]

def distrib (X Y Z : C) : X ◆ (Y ◇ Z) ⟶ (X ◆ Y) ◇ (X ◆ Z) :=
  σ_◆ X (Y ◇ Z) ≫ eqToHom (addObj_mulObj Y Z X) ≫ (σ_◆ Y X) ◇ₘ (σ_◆ Z X)

scoped notation "δ_" => distrib

theorem id_zero_mulHom {X Y : C} (f : X ⟶ Y) :
    𝟙 𝐎 ◆ₘ f = eqToHom ((zero_mulObj X).trans (zero_mulObj Y).symm) := by
  rw [(conj_eqToHom_iff_heq _ _ (zero_mulObj X) (zero_mulObj Y)).mpr (id_zero_mulHom_heq f)]
  simp

theorem mulHom_id_zero {X Y : C} (f : X ⟶ Y) :
    f ◆ₘ 𝟙 𝐎 = eqToHom ((mulObj_zero X).trans (mulObj_zero Y).symm) := by
  rw [(conj_eqToHom_iff_heq _ _ (mulObj_zero X) (mulObj_zero Y)).mpr (mulHom_id_zero_heq f)]
  simp

theorem addHom_mulHom {X₁ Y₁ X₂ Y₂ X₃ Y₃ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (h : X₃ ⟶ Y₃) :
    (f ◇ₘ g) ◆ₘ h =
      eqToHom (addObj_mulObj X₁ X₂ X₃) ≫ (f ◆ₘ h) ◇ₘ (g ◆ₘ h) ≫
        eqToHom (addObj_mulObj Y₁ Y₂ Y₃).symm :=
  (conj_eqToHom_iff_heq _ _ (addObj_mulObj X₁ X₂ X₃) (addObj_mulObj Y₁ Y₂ Y₃)).mpr
    (addHom_mulHom_heq f g h)

theorem distrib_eq_conj_eqToHom {X X' Y Y' Z Z' : C} (hX : X = X') (hY : Y = Y') (hZ : Z = Z') :
    δ_ X Y Z =
      eqToHom (by rw [hX, hY, hZ]) ≫
      δ_ X' Y' Z' ≫
      eqToHom (by rw [hX, hY, hZ]) := by
  subst hX hY hZ; simp

end BipermutativeCategory

class BipermutativeCategory (C : Type*) [Category C] extends
    BipermutativeCategoryBase C where
  distrib_square (X Y Z : C) :
    eqToHom (addObj_mulObj X Y Z) ≫ σ_◇ (X ◆ Z) (Y ◆ Z) =
      (σ_◇ X Y) ◆ₘ (𝟙 Z) ≫ eqToHom (addObj_mulObj Y X Z)

  -- (X ◇ Y) ◆ (Z ◇ W) ⟶ (X ◆ (Z ◇ W)) ◇ (Y ◆ (Z ◇ W)) ⟶ ((X ◆ Z) ◇ (X ◆ W)) ◇ ((Y ◆ Z) ◇ (Y ◆ W))
  --         ↓                                                               ↓
  -- ((X ◇ Y) ◆ Z) ◇ ((X ◇ Y) ◆ W)            ⟶           ((X ◆ Z) ◇ (Y ◆ Z)) ◇ ((X ◆ W) ◇ (Y ◆ W))
  distrib_pentagon (X Y Z W : C) :
    eqToHom (addObj_mulObj X Y (Z ◇ W)) ≫  -- ... ⟶ (X ◆ (Z ◇ W)) ◇ (Y ◆ (Z ◇ W))
      δ_ X Z W ◇ₘ δ_ Y Z W ≫            -- ... ⟶ ((X ◆ Z) ◇ (X ◆ W)) ◇ ((Y ◆ Z) ◇ (Y ◆ W))
      addMedial _ _ _ _ =                 -- ... ⟶ ((X ◆ Z) ◇ (Y ◆ Z)) ◇ ((X ◆ W) ◇ (Y ◆ W))
      δ_ (X ◇ Y) Z W ≫
      eqToHom (addObj_mulObj _ _ _) ◇ₘ eqToHom (addObj_mulObj _ _ _)

namespace BipermutativeCategory

section smul_lemmas
variable {C : Type*} [Category C] [BipermutativeCategory C]
variable (s : Scalar C)
variable {X₁ Y₁ X₂ Y₂ : C}
variable (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)

theorem smul_id_zero : s • 𝟙 (𝐎_ C) = 𝟙 𝐎 := by
  simp [Scalar.smul_def, id_zero_mulHom]

theorem smul_id_one : s • 𝟙 (𝐈_ C) = s := by
  simp

theorem smul_addHom : s • (f ◇ₘ g) = (s • f) ◇ₘ (s • g) := by
  simp only [Scalar.smul_def]
  rw [addHom_mulHom, conj_eqToHom_addHom, addHom_conj_eqToHom]
  simp

theorem scalar_addHom_self : s ◇ₘ s = s • 𝟙 (𝐈 ◇ 𝐈) := by
  simp [← id_addHom_id, smul_addHom s]

end smul_lemmas

end BipermutativeCategory

end FreeQuantum
