import FreeQuantum.Model
import Mathlib.Tactic

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory

/-!
## Freeness of `Πk`

Carette et al. (2026), main text Theorem 1.

- `BipermutativeFunctor C D`: a functor strictly preserving the bipermutative structure.
- `liftBip M`: `Model.lift M` as a bipermutative functor.
- `BipermutativeFunctor.toModel F`: the model of `F : PiK k ⥤ C`, given by `F` on `ζ` and `V`.
- `toModel_liftBip`: `(liftBip M).toModel = M`.
- `lift_toModel`: `F.toModel.lift = F.toFunctor`.
- `lift_unique`: a bipermutative functor out of `PiK k` is determined by its model.
- `BipermutativeFunctor.modelEquiv`: `Model k C ≃ BipermutativeFunctor (PiK k) C`, i.e. `Πk` is free.
-/

/-- A functor that strictly preserves the bipermutative structure:
- `𝐈`, `𝐎`, `◆`, `◇` on objects, as equations;
- `◆ₘ`, `◇ₘ`, `σ_◆`, `σ_◇` on morphisms, up to the `eqToHom`s induced by the object equations.

`δ_` is defined from `σ_◆` and `◇ₘ`, so it needs no separate condition. -/
structure BipermutativeFunctor (C D : Type*)
    [Category C] [BipermutativeCategory C] [Category D] [BipermutativeCategory D]
    extends C ⥤ D where
  obj_one : obj 𝐈 = 𝐈
  obj_zero : obj 𝐎 = 𝐎
  obj_mulObj (X Y : C) : obj (X ◆ Y) = obj X ◆ obj Y
  obj_addObj (X Y : C) : obj (X ◇ Y) = obj X ◇ obj Y
  map_mulHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    map (f ◆ₘ g) = eqToHom (obj_mulObj X₁ X₂) ≫ map f ◆ₘ map g ≫ eqToHom (obj_mulObj Y₁ Y₂).symm
  map_addHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    map (f ◇ₘ g) = eqToHom (obj_addObj X₁ X₂) ≫ map f ◇ₘ map g ≫ eqToHom (obj_addObj Y₁ Y₂).symm
  map_mulSwap (X Y : C) :
    map (σ_◆ X Y) = eqToHom (obj_mulObj X Y) ≫ σ_◆ (obj X) (obj Y) ≫ eqToHom (obj_mulObj Y X).symm
  map_addSwap (X Y : C) :
    map (σ_◇ X Y) = eqToHom (obj_addObj X Y) ≫ σ_◇ (obj X) (obj Y) ≫ eqToHom (obj_addObj Y X).symm

variable {k : ℕ} {C : Type*} [Category C] [BipermutativeCategory C]

/-! ### Models give bipermutative functors -/

def liftBip (M : Model k C) : BipermutativeFunctor (PiK k) C where
  __ := M.lift
  obj_one := M.natObj_one
  obj_zero := M.natObj_zero
  obj_mulObj X Y := M.natObj_mul X.n Y.n
  obj_addObj X Y := M.natObj_add X.n Y.n
  map_mulHom f g := by obtain ⟨_⟩ := f; obtain ⟨_⟩ := g; rfl
  map_addHom f g := by obtain ⟨_⟩ := f; obtain ⟨_⟩ := g; rfl
  map_mulSwap X Y := rfl
  map_addSwap X Y := rfl

/-! ### Bipermutative functors give models -/

namespace BipermutativeFunctor

variable (F G : BipermutativeFunctor (PiK k) C)

variable {F G} in
theorem ext' (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F; cases G; cases h; rfl

theorem obj_one_addObj_one : F.obj (𝐈 ◇ 𝐈) = 𝐈 ◇ 𝐈 := by
  rw [F.obj_addObj, F.obj_one]

theorem id_one_eq_conj_eqToHom_map :
    𝟙 𝐈 = eqToHom F.obj_one.symm ≫ F.map (𝟙 𝐈) ≫ eqToHom F.obj_one := by simp

theorem id_one_addHom_map {X Y : PiK k} (f : X ⟶ Y) :
    𝟙 𝐈 ◇ₘ F.map f =
      eqToHom (by rw [F.obj_addObj, F.obj_one]) ≫
      F.map (𝟙 𝐈 ◇ₘ f) ≫
      eqToHom (by rw [F.obj_addObj, F.obj_one]) := by
  rw [F.id_one_eq_conj_eqToHom_map, conj_eqToHom_addHom, F.map_addHom]
  simp

theorem conj_eqToHom_map_npow (s : Scalar (PiK k)) (n : ℕ) :
    (eqToHom F.obj_one.symm ≫ F.map s ≫ eqToHom F.obj_one) ^ n =
      eqToHom F.obj_one.symm ≫ F.map (s ^ n) ≫ eqToHom F.obj_one := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

def toModel : Model k C where
  natObj n := F.obj ⟨n⟩
  natObj_zero := F.obj_zero
  natObj_one := F.obj_one
  natObj_add m n := F.obj_addObj ⟨m⟩ ⟨n⟩
  natObj_mul m n := F.obj_mulObj ⟨m⟩ ⟨n⟩
  ζ := eqToHom F.obj_one.symm ≫ F.map (PiK.ζ k) ≫ eqToHom F.obj_one
  V := eqToHom F.obj_one_addObj_one.symm ≫ F.map PiK.V ≫ eqToHom F.obj_one_addObj_one
  V_V := by
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← reassoc_of% F.map_comp, PiK.V_V, PiK.X, F.map_addSwap,
      addSwap_eq_conj_eqToHom F.obj_one F.obj_one]
    simp
  V_S_V := by
    rw [conj_eqToHom_map_npow, addHom_conj_eqToHom, F.id_one_addHom_map, ← PiK.S]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans]
    repeat rw [← reassoc_of% F.map_comp]
    simp only [Category.assoc]
    rw [PiK.V_S_V]
  ζ_pow_two_k := by
    rw [conj_eqToHom_map_npow, PiK.ζ_pow_two_k]
    simp

/-- `F` agrees with the evaluation in its own model on every term. -/
theorem eval_toModel {m n : ℕ} (t : Term m n) :
    F.toModel.eval t = F.map (PiK.ofTerm (X := ⟨m⟩) (Y := ⟨n⟩) t) := by
  induction t with
  | id n =>
    show 𝟙 _ = F.map (𝟙 (⟨n⟩ : PiK k))
    rw [F.map_id]
  | comp f g ihf ihg =>
    show _ ≫ _ = F.map (PiK.ofTerm f ≫ PiK.ofTerm g)
    rw [F.map_comp, ihf, ihg]; rfl
  | mul f g ihf ihg =>
    show _ = F.map (PiK.ofTerm f ◆ₘ PiK.ofTerm g)
    rw [F.map_mulHom, ← ihf, ← ihg]; rfl
  | add f g ihf ihg =>
    show _ = F.map (PiK.ofTerm f ◇ₘ PiK.ofTerm g)
    rw [F.map_addHom, ← ihf, ← ihg]; rfl
  | mulSwap m n =>
    show _ = F.map (σ_◆ (⟨m⟩ : PiK k) (⟨n⟩ : PiK k))
    rw [F.map_mulSwap]; rfl
  | addSwap m n =>
    show _ = F.map (σ_◇ (⟨m⟩ : PiK k) (⟨n⟩ : PiK k))
    rw [F.map_addSwap]; rfl
  | zeta =>
    show _ = F.map (PiK.ζ k)
    simp [Model.eval, toModel]
  | V =>
    show _ = F.map PiK.V
    simp [Model.eval, toModel]

theorem lift_toModel : F.toModel.lift = F.toFunctor := by
  apply CategoryTheory.Functor.ext _ _
  . intro _; rfl
  . rintro ⟨m⟩ ⟨n⟩ ⟨t⟩
    show F.toModel.eval t = 𝟙 _ ≫ F.map ⟦t⟧ ≫ 𝟙 _
    simp [F.eval_toModel]

end BipermutativeFunctor

/-! ### Freeness -/

theorem toModel_liftBip (M : Model k C) : (liftBip M).toModel = M := by
  set F := liftBip M
  ext
  . rfl
  . simp only [BipermutativeFunctor.toModel]
    rw [← eq_conj_eqToHom_iff]; rfl
  . simp only [BipermutativeFunctor.toModel]
    rw [← eq_conj_eqToHom_iff]; rfl

theorem lift_unique (M : Model k C) (F : BipermutativeFunctor (PiK k) C) (h : F.toModel = M) :
    F.toFunctor = M.lift := by
  rw [← h, F.lift_toModel]

def BipermutativeFunctor.modelEquiv : Model k C ≃ BipermutativeFunctor (PiK k) C where
  toFun := liftBip
  invFun := BipermutativeFunctor.toModel
  left_inv := toModel_liftBip
  right_inv F := BipermutativeFunctor.ext' (lift_unique _ F rfl).symm

end FreeQuantum
