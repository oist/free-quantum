import FreeQuantum.Bipermutative.Basic

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory

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

end FreeQuantum
