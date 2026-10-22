import FreeQuantum.FinLin
import FreeQuantum.PiK
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Tactic

scoped [FourierTransform] notation "𝛘" => ZMod.stdAddChar

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

`stdModel k` is the model in `FinLin` with `ζ ↦ 𝛘 1`, where `𝛘 = ZMod.stdAddChar` on `ZMod (2 ^ k)`,
and `V ↦ (√2)⁻¹[[ω₈, ω₈⁻¹], [ω₈⁻¹, ω₈]]`, where `ω₈ = 𝛘 1` on `ZMod 8`. It requires `2 ≤ k`.
The `stdModel_lift_*` lemmas compute `(stdModel k hk).lift` on `◆ₘ`, `◇ₘ`, `σ_◆`, `σ_◇`, `•`, `^`,
`V` and `S`.

Non-triviality of `Πk`: `V_ne_id` and `ζ_ne_one` show, via `stdModel k`, that `Rel k` does not identify `V`
with `𝟙` or `ζ` with `1`. `Model.V_ne_id_of` and `Model.ζ_ne_one_of` transfer non-triviality from
any model.
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

/-! ### The model in `FinLin` -/

section FinLin
open scoped Real -- π
open scoped FourierTransform -- 𝛘
open Complex (I)
open FinLin

attribute [local grind =] Complex.I_sq

theorem stdAddChar_one_pow (N j : ℕ) [NeZero N] : 𝛘 (1 : ZMod N) ^ j = 𝛘 (j : ZMod N) := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_one]

theorem stdAddChar_two_pow_sub_two {k : ℕ} (hk : 2 ≤ k) :
    𝛘 ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) = I := by
  rw [show ((2 ^ (k - 2) : ℕ) : ZMod (2 ^ k)) = ((2 ^ (k - 2) : ℤ) : ZMod (2 ^ k)) by norm_cast,
    ZMod.stdAddChar_coe]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  conv_rhs => rw [← Complex.exp_pi_div_two_mul_I]
  congr 1; push_cast; simp [pow_add]; field_simp

theorem _root_.Complex.exp_pi_div_four_mul_I :
    Complex.exp (π / 4 * I) = (1 + I) / √2 := by
  rw [Complex.exp_mul_I]
  norm_cast
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  push_cast; field_simp; norm_cast
  rw [Real.sq_sqrt (by norm_num)]; norm_cast

theorem stdAddChar_two_pow_sub_three {k : ℕ} (hk : 3 ≤ k) :
    𝛘 ((2 ^ (k - 3) : ℕ) : ZMod (2 ^ k)) = (1 + I) / √2 := by
  rw [show ((_ : ℕ) : ZMod (2 ^ k)) = ((2 ^ (k - 3) : ℤ) : ZMod (2 ^ k)) by norm_cast,
    ZMod.stdAddChar_coe]
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  conv_rhs => rw [← Complex.exp_pi_div_four_mul_I]
  rw [add_tsub_cancel_left, pow_add]
  congr 1; push_cast; field_simp; norm_num

open FinLin

/-- `ω₈ = 𝛘 1 = e^{2πi/8}`, a primitive 8th root of unity. -/
noncomputable def eighth : ℂ := 𝛘 (1 : ZMod 8)

@[inherit_doc] scoped notation "ω₈" => eighth

theorem eighth_eq : ω₈ = (1 + I) / √2 := by
  rw [eighth,
    show (1 : ZMod 8) = ((1 : ℤ) : ZMod 8) by norm_cast, ZMod.stdAddChar_coe,
    show 2 * π * I * _ / _ = π / 4 * I by ring, Complex.exp_pi_div_four_mul_I]

theorem eighth_nonzero : ω₈ ≠ 0 := by simp [eighth_eq, Complex.ext_iff]

theorem eighth_inv : ω₈⁻¹ = (1 - I) / √2 := by
  rw [eighth_eq]
  field_simp; ring_nf
  rw [mul_inv_eq_iff_eq_mul₀ (by simp [Complex.ext_iff])]
  ring_nf; simp; norm_cast; simp

theorem eighth_mul_eighth_inv : ω₈ * ω₈⁻¹ = 1 :=
  mul_inv_cancel₀ eighth_nonzero

@[grind =]
theorem eighth_add_eighth_inv : ω₈ + ω₈⁻¹ = √2 := by
  rw [eighth_inv, eighth_eq]
  field_simp; ring_nf; norm_cast; simp

@[grind =]
theorem eighth_sq : ω₈ ^ 2 = I := by
  rw [eighth, stdAddChar_one_pow,
    show ((_ : ℕ) : ZMod 8) = ((2 : ℤ) : ZMod 8) by norm_cast, ZMod.stdAddChar_coe,
    show 2 * π * I * _ / _ = π / 2 * I by ring, Complex.exp_pi_div_two_mul_I]

noncomputable def stdModel (k : ℕ) (hk : 2 ≤ k) : Model k FinLin where
  natObj n := ⟨n⟩
  natObj_zero := rfl
  natObj_one := rfl
  natObj_add _ _ := rfl
  natObj_mul _ _ := rfl
  ζ := ofLin (𝛘 (1 : ZMod (2 ^ k)) • LinearMap.id)
  V := ofLin (Matrix.toEuclideanLin ((√2)⁻¹ • !![ω₈, ω₈⁻¹; ω₈⁻¹, ω₈]))
  V_V := by
    ext i j
    simp [addSwap, ofLin, toLin, toLin_comp]
    have h0 : finAddFlip (0 : Fin (1 + 1)) = 1 := by decide
    have h1 : finAddFlip (1 : Fin (1 + 1)) = 0 := by decide
    simp [Matrix.vecHead, Matrix.vecTail, Eucl.onb_apply]
    fin_cases i <;> fin_cases j <;> simp [h0, h1] <;> grind
  V_S_V := by
    rw [ofLin_scalar_pow, stdAddChar_one_pow, stdAddChar_two_pow_sub_two hk]
    rw [id_one_addHom_scalar]
    simp [ofLin, toLin, toLin_comp]
    ext i j
    simp [Matrix.vecHead, Matrix.vecTail, Eucl.onb_apply]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  ζ_pow_two_k := by
    rw [ofLin_scalar_pow, stdAddChar_one_pow, ZMod.natCast_self, AddChar.map_zero_eq_one, one_smul]
    rfl

theorem stdModel_ζ_def {k : ℕ} {hk : 2 ≤ k} :
    (stdModel k hk).ζ = ofLin (𝛘 (1 : ZMod (2 ^ k)) • LinearMap.id) := rfl

section
variable {k : ℕ} (hk : 2 ≤ k)

@[simp] theorem stdModel_lift_obj (X : PiK k) : (stdModel k hk).lift.obj X = ⟨X.n⟩ := rfl

@[simp] theorem stdModel_lift_map_addHom {X₁ Y₁ X₂ Y₂ : PiK k} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (stdModel k hk).lift.map (f ◇ₘ g) = (stdModel k hk).lift.map f ◇ₘ (stdModel k hk).lift.map g := by
  obtain ⟨_⟩ := f; obtain ⟨_⟩ := g; rfl

@[simp] theorem stdModel_lift_map_mulHom {X₁ Y₁ X₂ Y₂ : PiK k} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (stdModel k hk).lift.map (f ◆ₘ g) = (stdModel k hk).lift.map f ◆ₘ (stdModel k hk).lift.map g := by
  obtain ⟨_⟩ := f; obtain ⟨_⟩ := g; rfl

@[simp] theorem stdModel_lift_map_addSwap (X Y : PiK k) :
    (stdModel k hk).lift.map (σ_◇ X Y) = σ_◇ ((stdModel k hk).lift.obj X) ((stdModel k hk).lift.obj Y) := rfl

@[simp] theorem stdModel_lift_map_mulSwap (X Y : PiK k) :
    (stdModel k hk).lift.map (σ_◆ X Y) = σ_◆ ((stdModel k hk).lift.obj X) ((stdModel k hk).lift.obj Y) := rfl

@[simp] theorem stdModel_lift_map_smul {X Y : PiK k} (s : Scalar (PiK k)) (f : X ⟶ Y) :
    (stdModel k hk).lift.map (s • f) =
      (show Scalar FinLin from (stdModel k hk).lift.map s) • (stdModel k hk).lift.map f := by
  rw [Scalar.smul_def, CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    eqToHom_map, eqToHom_map, stdModel_lift_map_mulHom]
  rfl

@[simp] theorem stdModel_lift_map_pow (s : Scalar (PiK k)) (n : ℕ) :
    (stdModel k hk).lift.map (s ^ n) = (show Scalar FinLin from (stdModel k hk).lift.map s) ^ n := by
  induction n with
  | zero => exact (stdModel k hk).lift.map_id _
  | succ n ih =>
    rw [pow_succ, Scalar.mul_def, CategoryTheory.Functor.map_comp, ih, pow_succ, Scalar.mul_def]
    rfl

@[simp] theorem stdModel_lift_map_V :
    (stdModel k hk).lift.map (PiK.V : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) =
      ofLin (Matrix.toEuclideanLin ((√2)⁻¹ • !![ω₈, ω₈⁻¹; ω₈⁻¹, ω₈])) := rfl

@[simp] theorem stdModel_lift_map_S :
    (stdModel k hk).lift.map (PiK.S : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) = 𝟙 𝐈 ◇ₘ ((stdModel k hk).ζ ^ 2 ^ (k - 2)) := by
  rw [PiK.S, stdModel_lift_map_addHom, PiK.ζ_pow_eq]
  change _ ◇ₘ (stdModel k hk).eval (Term.zeta.npow _) = _
  rw [Model.eval_zeta_npow]
  rfl

end

/-- `Πk` does not collapse `V` to the identity. -/
theorem V_ne_id {k : ℕ} (hk : 2 ≤ k) : (PiK.V : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) ≠ 𝟙 _ := by
  apply (stdModel k hk).V_ne_id_of
  intro h
  replace h := congrArg (fun f ↦ (toLin f (Eucl.onb 0)).ofLp 0) h
  simp [stdModel, ofLin, toLin, Eucl.onb_apply, eighth_eq, Complex.ext_iff] at h

/-- `Πk` does not collapse `ζ` to `1`. -/
theorem ζ_ne_one {k : ℕ} (hk : 2 ≤ k) : PiK.ζ k ≠ 1 := by
  apply (stdModel k hk).ζ_ne_one_of
  intro h
  replace h := congrArg (fun f ↦ (toLin f (Eucl.onb 0)).ofLp 0) h
  simp [stdModel, ofLin, toLin, Eucl.onb_apply] at h
  replace h := congrArg (· ^ 2 ^ (k - 2)) h
  rw [stdAddChar_one_pow, stdAddChar_two_pow_sub_two hk, one_pow] at h
  simp [Complex.ext_iff] at h

end FinLin

end FreeQuantum
