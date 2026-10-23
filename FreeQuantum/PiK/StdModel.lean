import FreeQuantum.Bipermutative.Instances.FinLin
import FreeQuantum.PiK.Model
import FreeQuantum.Extra.ZMod
import Mathlib.Tactic

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory

/-!
## The standard model of `Πk` in `FinLin`

`stdModel k` is the model in `FinLin` with `ζ ↦ 𝛘 1`, where `𝛘 = ZMod.stdAddChar` on `ZMod (2 ^ k)`,
and `V ↦ (√2)⁻¹[[ω₈, ω₈⁻¹], [ω₈⁻¹, ω₈]]`, where `ω₈ = 𝛘 1` on `ZMod 8`. It requires `2 ≤ k`.
The `stdModel_lift_*` lemmas compute `(stdModel k hk).lift` on `◆ₘ`, `◇ₘ`, `σ_◆`, `σ_◇`, `•`, `^`,
`V` and `S`.

Non-triviality of `Πk`: `V_ne_id` and `ζ_ne_one` show, via `stdModel k`, that `Rel k` does not identify `V`
with `𝟙` or `ζ` with `1`.
-/

section FinLin
open scoped Real -- π
open scoped FourierTransform -- 𝛘
open Complex (I)
open FinLin

attribute [local grind =] Complex.I_sq

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
  rw [eighth, ZMod.stdAddChar_one_pow,
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
    rw [ofLin_scalar_pow, ZMod.stdAddChar_one_pow, ZMod.stdAddChar_two_pow_sub_two hk]
    rw [id_one_addHom_scalar]
    simp [ofLin, toLin, toLin_comp]
    ext i j
    simp [Matrix.vecHead, Matrix.vecTail, Eucl.onb_apply]
    fin_cases i <;> fin_cases j <;> simp <;> grind
  ζ_pow_two_k := by
    rw [ofLin_scalar_pow, ZMod.stdAddChar_one_pow, ZMod.natCast_self, AddChar.map_zero_eq_one, one_smul]
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
  rw [ZMod.stdAddChar_one_pow, ZMod.stdAddChar_two_pow_sub_two hk, one_pow] at h
  simp [Complex.ext_iff] at h

end FinLin

end FreeQuantum
