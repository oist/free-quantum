import FreeQuantum.PiK.Hadamard
import FreeQuantum.PiK.StdModel
import Mathlib.Tactic

namespace FreeQuantum

open CategoryTheory
open BipermutativeCategory
open PiK

/-!
## Two-qubit Quantum Schur Transform in `Πk`

For `k ≥ 3`, `QST₂_hom : 2 ◆ 2 ⟶ 3 ◇ 1` sends the Schur basis of two qubits (triplet `T₀, T₁, T₂`,
singlet `S`) to the computational basis. It is `H` on the middle block `{01, 10}` of
`2 ◆ 2 = 1 ◇ 2 ◇ 1`, followed by swapping the last two wires so that the singlet comes last.
The object equations `2 ◆ 2 = 1 ◇ 2 ◇ 1 = 2 ◇ 2 = 3 ◇ 1` hold by `rfl`.

- `QST₂_hom_inv`, `QST₂_inv_hom`: `QST₂_hom` is invertible in `Πk`, by `H_H`.
- `model_QST₂`, `model_QST₂_inv`: in `stdModel`, `QST₂_hom` and `QST₂_inv` evaluate to `qstMatrix`
  and its transpose.
- `model_QST₂_schurVec`: in `stdModel`, `QST₂_hom` sends the Schur basis vectors to `Eucl.onb`.
- `model_QST₂_mulSwap`: in `stdModel`, conjugating the qubit swap `σ_◆` by `QST₂` gives
  `diag(1, 1, 1, -1)`.
- `model_QST₂_mulHom_self`: in `FinLin`, conjugating `u ◆ u` by `QST₂` gives
  `schurBlocks u = sym2 u ◇ det2 u`, for every `u : ⟨2⟩ ⟶ ⟨2⟩`.
- `model_QST₂_mulHom_self_PiK`: the same for `u` the image of a one-qubit circuit of `Πk`.
-/

variable {k : ℕ}

def QST₂_hom : ((𝐈 ◇ 𝐈) ◆ (𝐈 ◇ 𝐈) : PiK k) ⟶ (𝐈 ◇ 𝐈 ◇ 𝐈) ◇ 𝐈 :=
  (𝟙 𝐈 ◇ₘ H ◇ₘ 𝟙 𝐈 : 𝐈 ◇ (𝐈 ◇ 𝐈) ◇ 𝐈 ⟶ _) ≫ (𝟙 (𝐈 ◇ 𝐈) ◇ₘ σ_◇ 𝐈 𝐈 : (𝐈 ◇ 𝐈) ◇ (𝐈 ◇ 𝐈) ⟶ _)

def QST₂_inv : ((𝐈 ◇ 𝐈 ◇ 𝐈) ◇ 𝐈 : PiK k) ⟶ (𝐈 ◇ 𝐈) ◆ (𝐈 ◇ 𝐈) :=
  (𝟙 (𝐈 ◇ 𝐈) ◇ₘ σ_◇ 𝐈 𝐈 : (𝐈 ◇ 𝐈) ◇ (𝐈 ◇ 𝐈) ⟶ _) ≫ (𝟙 𝐈 ◇ₘ H ◇ₘ 𝟙 𝐈 : 𝐈 ◇ (𝐈 ◇ 𝐈) ◇ 𝐈 ⟶ _)

theorem QST₂_hom_inv (hk : 3 ≤ k) : (QST₂_hom ≫ QST₂_inv : ((𝐈 ◇ 𝐈) ◆ (𝐈 ◇ 𝐈) : PiK k) ⟶ _) = 𝟙 _ := by
  simp only [QST₂_hom, QST₂_inv, Category.assoc]
  rw [reassoc_of% addHom_comp_addHom]
  simp only [Category.comp_id, id_addHom_id, Category.id_comp, addHom_comp_addHom,
    addHom_comp_addHom, addSwap_addSwap, H_H hk]
  congr

theorem QST₂_inv_hom (hk : 3 ≤ k) : (QST₂_inv ≫ QST₂_hom : ((𝐈 ◇ 𝐈 ◇ 𝐈) ◇ 𝐈 : PiK k) ⟶ _) = 𝟙 _ := by
  simp only [QST₂_hom, QST₂_inv, Category.assoc]
  rw [reassoc_of% addHom_comp_addHom]
  simp only [Category.comp_id, id_addHom_id, Category.id_comp, addHom_comp_addHom,
    addHom_comp_addHom, addSwap_addSwap, H_H hk]
  congr

def QST₂ (hk : 3 ≤ k) : ((𝐈 ◇ 𝐈) ◆ (𝐈 ◇ 𝐈) : PiK k) ≅ (𝐈 ◇ 𝐈 ◇ 𝐈) ◇ 𝐈 where
  hom := QST₂_hom
  inv := QST₂_inv
  hom_inv_id := QST₂_hom_inv hk
  inv_hom_id := QST₂_inv_hom hk

/-! ### The model in `FinLin` -/

section FinLin
open scoped Real -- π
open scoped FourierTransform -- 𝛘
open Complex (I)
open FinLin

attribute [local grind =] Complex.I_sq

/-- `stdModel k` for `3 ≤ k`, where `ω` and `H` are defined. -/
noncomputable abbrev model (hk : 3 ≤ k) : Model k FinLin := stdModel k (by omega)

variable (hk : 3 ≤ k)

theorem model_ω :
    (model hk).lift.map (ω k) = ofLin (ω₈ • LinearMap.id) := by
  set M := model hk
  rw [ω, ζ_pow_eq]
  show M.eval (Term.zeta.npow _) = _
  simp only [Model.eval_zeta_npow, toLin_comp]
  show ofLin (𝛘 (1 : ZMod (2 ^ k)) • LinearMap.id : Scalar FinLin) ^ 2 ^ _ = _
  rw [ofLin_scalar_pow]
  congr
  rw [stdAddChar_one_pow, stdAddChar_two_pow_sub_three hk, eighth_eq]

theorem model_H :
    (model hk).lift.map (H : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) =
      (ofLin (Matrix.toEuclideanLin ((√2)⁻¹ • !![1, 1; 1, -1])) : (⟨2⟩ : FinLin) ⟶ ⟨2⟩) := by
  rw [H, V_S_V]
  simp only [stdModel_lift_map_smul, stdModel_lift_map_pow, Functor.map_comp, stdModel_lift_map_V,
    stdModel_lift_map_S]
  erw [model_ω hk, ofLin_scalar_pow]
  rw [stdModel_ζ_def, ofLin_scalar_pow, stdAddChar_one_pow, stdAddChar_two_pow_sub_two (by omega)]
  rw [FinLin.id_one_addHom_scalar]

  dsimp only [stdModel_lift_obj, PiK.addObj_n, PiK.mulUnit_n, Nat.reduceAdd]
  rw [ofLin_toEuclideanLin_comp, ofLin_toEuclideanLin_comp]
  erw [← ofLin_smul]
  rw [toLin, ← Matrix.toEuclideanLin.map_smul]
  congr 2
  ext i j
  simp [Eucl.onb_apply]
  fin_cases i <;> fin_cases j <;> simp <;> grind

/-- The matrix of `QST₂` in the computational basis `00, 01, 10, 11`. -/
noncomputable def qstMatrix : Matrix (Fin 4) (Fin 4) ℂ :=
  let s : ℂ := (√2)⁻¹
  !![1, 0, 0, 0;
     0, s, s, 0;
     0, 0, 0, 1;
     0, s, -s, 0]

open Eucl in
theorem model_QST₂ :
    (model hk).lift.map (QST₂_hom : ((𝐈 ◇ 𝐈) ◆ (𝐈 ◇ 𝐈) : PiK k) ⟶ _) =
      ofLin (Matrix.toEuclideanLin qstMatrix) := by
  simp only [QST₂_hom, Functor.map_comp, stdModel_lift_map_addHom, stdModel_lift_map_addSwap,
    CategoryTheory.Functor.map_id]
  erw [model_H hk]
  apply hom_ext_entry
  intro i j
  dsimp only [stdModel_lift_obj, PiK.addObj_n, PiK.mulObj_n, PiK.mulUnit_n, Nat.reduceAdd, Nat.reduceMul]
  rw [entry_ofLin_toEuclideanLin qstMatrix i j]
  simp only [entry_comp, entry_addHom, entry_addSwap, entry_id]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, qstMatrix] <;>
    rw [entry_ofLin_toEuclideanLin] <;> simp

/-- The Schur basis of `ℂ² ⊗ ℂ²`: the triplet `T₀ = |00⟩`, `T₁ = (|01⟩ + |10⟩)/√2`, `T₂ = |11⟩`,
and the singlet `S = (|01⟩ - |10⟩)/√2`. -/
noncomputable def schurVec : Fin 4 → Eucl 4 :=
  let s : ℂ := (√2 : ℂ)⁻¹
  ![Eucl.onb 0, s • (Eucl.onb 1 + Eucl.onb 2), Eucl.onb 3, s • (Eucl.onb 1 - Eucl.onb 2)]

theorem model_QST₂_schurVec (i : Fin 4) :
    toLin ((model hk).lift.map (QST₂_hom : ((𝐈 ◇ 𝐈) ◆ (𝐈 ◇ 𝐈) : PiK k) ⟶ _)) (schurVec i) =
      Eucl.onb i := by
  rw [model_QST₂ hk]
  show Matrix.toEuclideanLin qstMatrix (schurVec i) = _
  have hs : ((√2 : ℂ)⁻¹) ^ 2 = 1 / 2 := by rw [inv_pow]; norm_cast; simp
  simp [schurVec, qstMatrix]
  fin_cases i <;> simp [Eucl.toEuclideanLin_onb, Fin.sum_univ_four] <;>
    simp only [smul_smul, ← sq, hs] <;> module

theorem model_QST₂_inv :
    (model hk).lift.map (QST₂_inv : ((𝐈 ◇ 𝐈 ◇ 𝐈) ◇ 𝐈 : PiK k) ⟶ _) =
      ofLin (Matrix.toEuclideanLin qstMatrix.transpose) := by
  simp only [QST₂_inv, Functor.map_comp, stdModel_lift_map_addHom, stdModel_lift_map_addSwap,
    CategoryTheory.Functor.map_id]
  erw [model_H hk]
  apply hom_ext_entry
  intro i j
  dsimp only [stdModel_lift_obj, PiK.addObj_n, PiK.mulObj_n, PiK.mulUnit_n, Nat.reduceAdd, Nat.reduceMul]
  rw [entry_ofLin_toEuclideanLin qstMatrix.transpose i j]
  simp only [entry_comp, entry_addHom, entry_addSwap, entry_id]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_four, qstMatrix] <;>
    rw [entry_ofLin_toEuclideanLin] <;> simp

/-- In the Schur basis, the qubit swap is `+1` on the triplet and `-1` on the singlet. -/
theorem model_QST₂_mulSwap :
    (model hk).lift.map ((QST₂ hk).inv ≫ σ_◆ _ _ ≫ (QST₂ hk).hom) =
      ofLin (Matrix.toEuclideanLin (Matrix.diagonal ![1, 1, 1, -1])) := by
  simp only [QST₂]
  simp only [stdModel_lift_obj, PiK.addObj_n, PiK.mulUnit_n, Nat.reduceAdd, Functor.map_comp,
    PiK.mulObj_n, Nat.reduceMul, stdModel_lift_map_mulSwap, Nat.succ_eq_add_one]
  rw [model_QST₂ hk, model_QST₂_inv]
  apply hom_ext_entry; intro i j
  simp only [entry_comp, entry_mulSwap]
  rw [entry_ofLin_toEuclideanLin]
  conv_lhs => arg 2; intro; arg 1; arg 2; intro; rw [entry_ofLin_toEuclideanLin]
  conv_lhs => arg 2; intro; arg 2; rw [entry_ofLin_toEuclideanLin]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, qstMatrix, finProdFinEquiv, Fin.divNat, Fin.modNat] <;>
    (ring_nf; norm_cast; simp)

/-- The matrix of `u ◆ u` on the triplet `T₀, T₁, T₂`, where `A` is the matrix of `u`. -/
noncomputable def sym2 (A : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  let s : ℂ := √2
  !![A 0 0 ^ 2,         s * A 0 0 * A 0 1,                  A 0 1 ^ 2;
     s * A 0 0 * A 1 0, A 0 0 * A 1 1 + A 0 1 * A 1 0,     s * A 0 1 * A 1 1;
     A 1 0 ^ 2,         s * A 1 0 * A 1 1,                  A 1 1 ^ 2]

/-- The determinant of `A`: the action of `u ◆ u` on the singlet `S`. -/
noncomputable def det2 (A : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  A 0 0 * A 1 1 - A 0 1 * A 1 0

/-- `sym2 u ◇ det2 u`: the expected form of `u ◆ u` in the Schur basis. -/
noncomputable def schurBlocks (u : (⟨2⟩ : FinLin) ⟶ ⟨2⟩) : (⟨3⟩ ◇ ⟨1⟩ : FinLin) ⟶ ⟨3⟩ ◇ ⟨1⟩ :=
  ofLin (Matrix.toEuclideanLin (sym2 (Matrix.of (entry u)))) ◇ₘ
    ofLin (Matrix.toEuclideanLin !![det2 (Matrix.of (entry u))])

/-- In the Schur basis, `u ◆ u` is `schurBlocks u`, for every linear `u : ℂ² → ℂ²`. -/
theorem model_QST₂_mulHom_self (u : (⟨2⟩ : FinLin) ⟶ ⟨2⟩) :
    (model hk).lift.map (QST₂ hk).inv ≫ (u ◆ₘ u) ≫ (model hk).lift.map (QST₂ hk).hom =
      schurBlocks u := by
  simp only [QST₂]
  simp only [stdModel_lift_obj, PiK.addObj_n, PiK.mulUnit_n, Nat.reduceAdd, PiK.mulObj_n,
    Nat.reduceMul]
  rw [model_QST₂ hk, model_QST₂_inv]
  apply hom_ext_entry; intro i j
  simp only [entry_comp, entry_mulHom]
  conv_lhs =>
    simp [qstMatrix]
    conv => arg 2; intro; arg 1; arg 2; intro; rw [entry_ofLin_toEuclideanLin]
    conv => arg 2; intro; arg 2; rw [entry_ofLin_toEuclideanLin]
  conv_rhs =>
    simp [schurBlocks, sym2, det2]
    conv => arg 2; intro; arg 2; intro; rw [entry_ofLin_toEuclideanLin]
    conv => arg 3; intro; arg 3; intro; rw [entry_ofLin_toEuclideanLin]
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four, finProdFinEquiv, Fin.divNat, Fin.modNat] <;>
    field_simp <;> norm_cast <;> simp <;> ring

/-- Every one-qubit circuit `f` of `Πk`, applied to both qubits, is block diagonal in the Schur
basis. -/
theorem model_QST₂_mulHom_self_PiK (f : (𝐈 ◇ 𝐈 : PiK k) ⟶ 𝐈 ◇ 𝐈) :
    (model hk).lift.map ((QST₂ hk).inv ≫ (f ◆ₘ f) ≫ (QST₂ hk).hom) =
      schurBlocks ((model hk).lift.map f) := by
  simp only [stdModel_lift_obj, PiK.addObj_n, PiK.mulUnit_n, Nat.reduceAdd, Functor.map_comp,
    PiK.mulObj_n, Nat.reduceMul, stdModel_lift_map_mulHom]
  apply model_QST₂_mulHom_self

end FinLin

end FreeQuantum
