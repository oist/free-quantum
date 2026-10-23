import FreeQuantum.Bipermutative.Basic

namespace FreeQuantum

open CategoryTheory

/-!
## Instance: `Discrete ℕ`

`◆ := ×` (unit `1`), `◇ := +` (unit `0`). Every Hom-set here is a subsingleton, so this shows the
axioms are non-contradictory, nothing more.
-/
section DiscreteInstance

abbrev DiscreteNat := Discrete ℕ

instance (n : ℕ) : OfNat DiscreteNat n where
  ofNat := ⟨n⟩

@[simp] theorem ofNat_eq_mk (n : ℕ) : (OfNat.ofNat n : DiscreteNat) = ⟨n⟩ := rfl

open BipermutativeCategory

/-- The `(·*·)`/`1` strict symmetric monoidal structure on `Discrete ℕ`. -/
instance natMul : StrictMulSymmetricMonoidalCategory DiscreteNat where
  mulObj X Y := ⟨X.as * Y.as⟩
  mulUnit := 1
  mulHom f g := eqToHom (by rw [Discrete.eq_of_hom f, Discrete.eq_of_hom g])

  mulObj_assoc X Y Z := by simp [mul_assoc]
  one_mulObj X := by simp
  mulObj_one X := by simp

  id_one_mulHom_heq _ := Subsingleton.helim (by simp) _ _
  mulHom_id_one_heq _ := Subsingleton.helim (by simp) _ _
  mulHom_assoc_heq _ _ _ := Subsingleton.helim (by simp [mul_assoc]) _ _
  id_mulHom_id _ _ := Subsingleton.elim _ _
  mulHom_comp_mulHom _ _ _ _ := Subsingleton.elim _ _

  mulSwap X Y := eqToHom (by simp [mul_comm])
  mulSwap_mulSwap _ _ := Subsingleton.elim _ _
  mulSwap_natural _ _ := Subsingleton.elim _ _
  mulSwap_hexagon _ _ _ := Subsingleton.elim _ _

/-- The `(·+·)`/`0` strict symmetric monoidal structure on `Discrete ℕ`. -/
instance natAdd : StrictAddSymmetricMonoidalCategory DiscreteNat where
  addObj X Y := ⟨X.as + Y.as⟩
  addUnit := 0
  addHom f g := eqToHom (by rw [Discrete.eq_of_hom f, Discrete.eq_of_hom g])

  addObj_assoc X Y Z := by simp [add_assoc]
  zero_addObj X := by simp
  addObj_zero X := by simp

  id_zero_addHom_heq _ := Subsingleton.helim (by simp) _ _
  addHom_id_zero_heq _ := Subsingleton.helim (by simp) _ _
  addHom_assoc_heq _ _ _ := Subsingleton.helim (by simp [add_assoc]) _ _
  id_addHom_id _ _ := Subsingleton.elim _ _
  addHom_comp_addHom _ _ _ _ := Subsingleton.elim _ _

  addSwap X Y := eqToHom (by simp [add_comm])
  addSwap_addSwap _ _ := Subsingleton.elim _ _
  addSwap_natural _ _ := Subsingleton.elim _ _
  addSwap_hexagon _ _ _ := Subsingleton.elim _ _

instance : BipermutativeCategory DiscreteNat where
  zero_mulObj X := by simp [mulObj, addUnit]
  id_zero_mulHom_heq _ := Subsingleton.helim (by simp [mulObj, addUnit]) _ _
  mulObj_zero X := by simp [mulObj, addUnit]
  mulHom_id_zero_heq _ := Subsingleton.helim (by simp [mulObj, addUnit]) _ _
  addObj_mulObj X Y Z := by simp [mulObj, addObj, add_mul]
  addHom_mulHom_heq _ _ _ := Subsingleton.helim (by simp [mulObj, addObj, add_mul]) _ _

  distrib_square X Y Z := Subsingleton.elim _ _
  distrib_pentagon X Y Z W := Subsingleton.elim _ _

end DiscreteInstance

end FreeQuantum
