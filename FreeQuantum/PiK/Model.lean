import FreeQuantum.PiK.Basic
import Mathlib.Tactic

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory

/-!
## Soundness of `Πk`

Carette et al. (2026), SI Proposition S9.

A `Model k C` is a bipermutative category `C` with an object map `natObj : ℕ → C` that is strict
for `0`, `1`, `+`, `*`, and morphisms `ζ : 𝐈 ⟶ 𝐈`, `V : 𝐈 ◇ 𝐈 ⟶ 𝐈 ◇ 𝐈` satisfying Axioms [1]–[3].
`Model.eval` interprets terms, `Model.eval_sound` shows that it respects `Rel k`, and
`Model.lift : PiK k ⥤ C` is the induced functor.

`Model.V_ne_id_of` and `Model.ζ_ne_one_of` transfer non-triviality of `V` and `ζ` from any model
to `Πk`.
-/

@[ext]
structure Model (k : ℕ) (C : Type*) [Category C] [BipermutativeCategory C] where
  natObj : ℕ → C
  natObj_zero : natObj 0 = 𝐎
  natObj_one : natObj 1 = 𝐈
  natObj_add (m n : ℕ) : natObj (m + n) = natObj m ◇ natObj n
  natObj_mul (m n : ℕ) : natObj (m * n) = natObj m ◆ natObj n
  ζ : Scalar C
  V : 𝐈 ◇ 𝐈 ⟶ (𝐈 ◇ 𝐈 : C)
  V_V : V ≫ V = σ_◇ 𝐈 𝐈
  V_S_V : V ≫ (𝟙 𝐈 ◇ₘ (ζ ^ 2 ^ (k - 2))) ≫ V =
    (𝟙 𝐈 ◇ₘ (ζ ^ 2 ^ (k - 2))) ≫ V ≫ (𝟙 𝐈 ◇ₘ (ζ ^ 2 ^ (k - 2)))
  ζ_pow_two_k : ζ ^ 2 ^ k = 1

namespace Model

variable {k : ℕ} {C : Type*} [Category C] [BipermutativeCategory C] (M : Model k C)

theorem natObj_two : M.natObj 2 = 𝐈 ◇ 𝐈 := by
  rw [← one_add_one_eq_two, M.natObj_add, M.natObj_one]

def eval : {m n : ℕ} → Term m n → (M.natObj m ⟶ M.natObj n)
  | _, _, .id n => 𝟙 (M.natObj n)
  | _, _, .comp f g => eval f ≫ eval g
  | _, _, .mul (m₁ := m₁) (n₁ := n₁) (m₂ := m₂) (n₂ := n₂) f g =>
    eqToHom (M.natObj_mul m₁ m₂) ≫ eval f ◆ₘ eval g ≫ eqToHom (M.natObj_mul n₁ n₂).symm
  | _, _, .add (m₁ := m₁) (n₁ := n₁) (m₂ := m₂) (n₂ := n₂) f g =>
    eqToHom (M.natObj_add m₁ m₂) ≫ eval f ◇ₘ eval g ≫ eqToHom (M.natObj_add n₁ n₂).symm
  | _, _, .mulSwap m n =>
    eqToHom (M.natObj_mul m n) ≫ σ_◆ (M.natObj m) (M.natObj n) ≫ eqToHom (M.natObj_mul n m).symm
  | _, _, .addSwap m n =>
    eqToHom (M.natObj_add m n) ≫ σ_◇ (M.natObj m) (M.natObj n) ≫ eqToHom (M.natObj_add n m).symm
  | _, _, .zeta => eqToHom M.natObj_one ≫ M.ζ ≫ eqToHom M.natObj_one.symm
  | _, _, .V => eqToHom M.natObj_two ≫ M.V ≫ eqToHom M.natObj_two.symm

/-! ### Terms defined from other terms -/

theorem eval_cast {m n : ℕ} (h : m = n) :
    M.eval (Term.cast h) = eqToHom (congrArg M.natObj h) := by
  rw [Term.cast]; subst h; rfl

theorem eval_zeta_npow (j : ℕ) :
    M.eval (Term.zeta.npow j) = eqToHom M.natObj_one ≫ (M.ζ ^ j) ≫ eqToHom M.natObj_one.symm := by
  induction j with
  | zero => simp [Term.npow, eval]
  | succ n ih => simp [Term.npow, eval, ih, pow_succ, mul_comm, Scalar.mul_def]

theorem eval_X : M.eval Term.X = eqToHom M.natObj_two ≫ σ_◇ 𝐈 𝐈 ≫ eqToHom M.natObj_two.symm := by
  simp [Term.X, eval, addSwap_eq_conj_eqToHom M.natObj_one M.natObj_one]

theorem eval_S :
    M.eval (Term.S k) =
      eqToHom M.natObj_two ≫ (𝟙 𝐈 ◇ₘ (M.ζ ^ 2 ^ (k - 2))) ≫ eqToHom M.natObj_two.symm := by
  simp only [Term.S, eval, eval_zeta_npow]
  rw [id_eq_conj_eqToHom M.natObj_one, conj_eqToHom_addHom]
  simp [addHom_conj_eqToHom]

theorem eval_distrib (a b c : ℕ) :
    M.eval (Term.distrib a b c) =
      eqToHom (by simp only [M.natObj_mul, M.natObj_add]) ≫
      δ_ (M.natObj a) (M.natObj b) (M.natObj c) ≫
      eqToHom (by simp only [M.natObj_mul, M.natObj_add]) := by
  simp [Term.distrib, eval, eval_cast,
    mulSwap_eq_conj_eqToHom rfl (M.natObj_add ..), conj_eqToHom_addHom, addHom_conj_eqToHom,
    distrib]

theorem eval_addMedial (a b c d : ℕ) :
    M.eval (Term.addMedial a b c d) =
      eqToHom (by simp only [M.natObj_add]) ≫
      addMedial (M.natObj a) (M.natObj b) (M.natObj c) (M.natObj d) ≫
      eqToHom (by simp only [M.natObj_add]) := by
  simp [Term.addMedial, eval, eval_cast, conj_eqToHom_addHom, addHom_conj_eqToHom, addMedial_def]

/-! ### Soundness -/

theorem eval_sound {m n : ℕ} {t t' : Term m n} (h : Rel k t t') : M.eval t = M.eval t' := by
  induction h with
  | refl f => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | comp_congr _ _ ih₁ ih₂ => rw [eval, eval, ih₁, ih₂]
  | mulHom_congr _ _ ih₁ ih₂ => rw [eval, eval, ih₁, ih₂]
  | addHom_congr _ _ ih₁ ih₂ => rw [eval, eval, ih₁, ih₂]
  | id_comp f => rw [eval, eval, Category.id_comp]
  | comp_id f => rw [eval, eval, Category.comp_id]
  | assoc f g h => rw [eval, eval, eval, eval, Category.assoc]
  | id_one_mulHom f =>
    simp only [eval, eval_cast]
    rw [id_eq_conj_eqToHom M.natObj_one, conj_eqToHom_mulHom]
    simp [id_one_mulHom]
  | mulHom_id_one f =>
    simp only [eval, eval_cast]
    rw [id_eq_conj_eqToHom M.natObj_one, mulHom_conj_eqToHom]
    simp [mulHom_id_one]
  | mulHom_assoc f g h =>
    simp [eval, eval_cast, conj_eqToHom_mulHom, mulHom_conj_eqToHom, mulHom_assoc]
  | id_mulHom_id m n => simp [eval, id_mulHom_id]
  | mulHom_comp_mulHom f₁ f₂ g₁ g₂ => simp [eval, reassoc_of% mulHom_comp_mulHom]
  | mulSwap_mulSwap m n => simp [eval, reassoc_of% mulSwap_mulSwap]
  | mulSwap_natural f g => simp [eval, reassoc_of% mulSwap_natural]
  | mulSwap_hexagon a b c =>
    simp only [eval, eval_cast]
    rw [mulSwap_eq_conj_eqToHom rfl (M.natObj_mul ..)]
    simp [conj_eqToHom_mulHom, mulHom_conj_eqToHom, mulSwap_hexagon]
  | id_zero_addHom f =>
    simp only [eval, eval_cast]
    rw [id_eq_conj_eqToHom M.natObj_zero, conj_eqToHom_addHom]
    simp [id_zero_addHom]
  | addHom_id_zero f =>
    simp only [eval, eval_cast]
    rw [id_eq_conj_eqToHom M.natObj_zero, addHom_conj_eqToHom]
    simp [addHom_id_zero]
  | addHom_assoc f g h =>
    simp [eval, eval_cast, conj_eqToHom_addHom, addHom_conj_eqToHom, addHom_assoc]
  | id_addHom_id m n => simp [eval, id_addHom_id]
  | addHom_comp_addHom f₁ f₂ g₁ g₂ => simp [eval, reassoc_of% addHom_comp_addHom]
  | addSwap_addSwap m n => simp [eval, reassoc_of% addSwap_addSwap]
  | addSwap_natural f g => simp [eval, reassoc_of% addSwap_natural]
  | addSwap_hexagon a b c =>
    simp only [eval, eval_cast]
    rw [addSwap_eq_conj_eqToHom rfl (M.natObj_add ..)]
    simp [conj_eqToHom_addHom, addHom_conj_eqToHom, addSwap_hexagon]
  | id_zero_mulHom f =>
    simp only [eval, eval_cast]
    rw [id_eq_conj_eqToHom M.natObj_zero, conj_eqToHom_mulHom]
    simp [id_zero_mulHom]
  | mulHom_id_zero f =>
    simp only [eval, eval_cast]
    rw [id_eq_conj_eqToHom M.natObj_zero, mulHom_conj_eqToHom]
    simp [mulHom_id_zero]
  | addHom_mulHom f g h =>
    simp only [eval, eval_cast]
    simp [conj_eqToHom_mulHom, conj_eqToHom_addHom, addHom_conj_eqToHom, addHom_mulHom]
  | distrib_square a b c =>
    simp only [eval, eval_cast,
      Category.assoc, eqToHom_trans_assoc,
      conj_eqToHom_mulHom, addSwap_eq_conj_eqToHom (M.natObj_mul ..) (M.natObj_mul ..)]
    have : M.natObj ((a + b) * c) = (M.natObj a ◇ M.natObj b) ◆ M.natObj c := by
      simp [M.natObj_mul, M.natObj_add]
    rw [← eqToHom_trans_assoc this (addObj_mulObj ..)]
    simp [reassoc_of% distrib_square]
  | distrib_pentagon a b c d =>
    simp only [eval, eval_cast, eval_distrib, eval_addMedial,
      Category.assoc, eqToHom_trans_assoc,
      eqToHom_addHom_eqToHom, conj_eqToHom_addHom, addHom_conj_eqToHom,
      addMedial_eq_conj_eqToHom
        (M.natObj_mul ..) (M.natObj_mul ..) (M.natObj_mul ..) (M.natObj_mul ..),
      distrib_eq_conj_eqToHom (M.natObj_add ..) rfl rfl]
    have : M.natObj ((a + b) * (c + d)) =
        (M.natObj a ◇ M.natObj b) ◆ (M.natObj c ◇ M.natObj d) := by
      simp [M.natObj_mul, M.natObj_add]
    rw [← eqToHom_trans_assoc this (addObj_mulObj ..)]
    simp [reassoc_of% distrib_pentagon]
  | V_V => simp [eval, eval_X, reassoc_of% M.V_V]
  | V_S_V => simp [eval, eval_S, reassoc_of% M.V_S_V]
  | zeta_pow => simp [eval, eval_zeta_npow, M.ζ_pow_two_k]

/-! ### The induced functor -/

def lift : PiK k ⥤ C where
  obj X := M.natObj X.n
  map {X Y} := Quotient.lift (M.eval (m := X.n) (n := Y.n)) fun _ _ h ↦ M.eval_sound h
  map_id _ := rfl
  map_comp f g := by obtain ⟨_⟩ := f; obtain ⟨_⟩ := g; rfl

theorem lift_map_ofTerm {X Y : PiK k} (t : Term X.n Y.n) :
    (M.lift).map (PiK.ofTerm t) = M.eval t := rfl

theorem lift_map_V :
    M.lift.map (PiK.V : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) =
      eqToHom M.natObj_two ≫ M.V ≫ eqToHom M.natObj_two.symm := rfl

theorem lift_map_ζ :
    M.lift.map (PiK.ζ k) =
      eqToHom M.natObj_one ≫ M.ζ ≫ eqToHom M.natObj_one.symm := rfl

theorem V_ne_id_of (hV : M.V ≠ 𝟙 _) : (PiK.V : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) ≠ 𝟙 _ := by
  intro h
  have h' : eqToHom M.natObj_two ≫ M.V ≫ eqToHom M.natObj_two.symm = 𝟙 (M.natObj 2) := by
    rw [← M.lift_map_V, congrArg M.lift.map h, M.lift.map_id]
    rfl
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at h'
  exact hV (by simpa using h')

theorem ζ_ne_one_of (hζ : M.ζ ≠ 1) : PiK.ζ k ≠ 1 := by
  intro h
  have h' : eqToHom M.natObj_one ≫ M.ζ ≫ eqToHom M.natObj_one.symm = 𝟙 (M.natObj 1) := by
    rw [← M.lift_map_ζ, congrArg M.lift.map h]
    erw [M.lift.map_id]
    rfl
  rw [eqToHom_comp_iff, comp_eqToHom_iff] at h'
  exact hζ (by simpa using h')

end Model

end FreeQuantum
