import FreeQuantum.Bipermutative
import Mathlib.Tactic

namespace FreeQuantum

open CategoryTheory

/-!
## `Πk`: the free model of reversible quantum computing

Carette et al. (2026), Theorem 1 / SI Proposition S5.

`Term m n` are raw terms built from the bipermutative combinators and the generators
`ζ : 1 → 1`, `V : 2 → 2`. `Rel k` is the smallest congruence containing the laws of a
bipermutative category (Definition S1) and Axioms [1]–[3]:
`V ≫ V = X`, `V ≫ S ≫ V = S ≫ V ≫ S`, `ζ ^ 2 ^ k = 1`,
where `X = σ_◇ 1 1` and `S = 1 ◇ ζ ^ 2 ^ (k - 2)`.
`PiK k` has objects `ℕ` and hom-sets `Term m n` modulo `Rel k`.

Laws whose sides only agree up to an object equation are stated in `Rel` as conjugation by
`Term.cast`, the term counterpart of `eqToHom` (cf. `conj_eqToHom_iff_heq`).
-/

inductive Term : ℕ → ℕ → Type
  | id (n : ℕ) : Term n n
  | comp {l m n : ℕ} : Term l m → Term m n → Term l n
  | mul {m₁ n₁ m₂ n₂ : ℕ} : Term m₁ n₁ → Term m₂ n₂ → Term (m₁ * m₂) (n₁ * n₂)
  | add {m₁ n₁ m₂ n₂ : ℕ} : Term m₁ n₁ → Term m₂ n₂ → Term (m₁ + m₂) (n₁ + n₂)
  | mulSwap (m n : ℕ) : Term (m * n) (n * m)
  | addSwap (m n : ℕ) : Term (m + n) (n + m)
  | zeta : Term 1 1
  | V : Term 2 2

namespace Term

def cast {m n : ℕ} (h : m = n) : Term m n := h ▸ id m

def npow {n : ℕ} (t : Term n n) : ℕ → Term n n
  | 0 => id n
  | j + 1 => (npow t j).comp t

def X : Term 2 2 := addSwap 1 1

def S (k : ℕ) : Term 2 2 := (id 1).add (zeta.npow (2 ^ (k - 2)))

def distrib (a b c : ℕ) : Term (a * (b + c)) (a * b + a * c) :=
  (mulSwap a (b + c)).comp <| (cast (add_mul b c a)).comp <| (mulSwap b a).add (mulSwap c a)

def addMedial (a b c d : ℕ) : Term (a + b + (c + d)) (a + c + (b + d)) :=
  (cast (add_assoc a b (c + d))).comp <|
  ((id a).add (cast (add_assoc b c d).symm)).comp <|
  ((id a).add ((addSwap b c).add (id d))).comp <|
  ((id a).add (cast (add_assoc c b d))).comp <|
  cast (add_assoc a c (b + d)).symm

end Term

open Term in
inductive Rel (k : ℕ) : {m n : ℕ} → Term m n → Term m n → Prop
  | refl {m n : ℕ} (f : Term m n) : Rel k f f
  | symm {m n : ℕ} {f g : Term m n} : Rel k f g → Rel k g f
  | trans {m n : ℕ} {f g h : Term m n} : Rel k f g → Rel k g h → Rel k f h
  | comp_congr {l m n : ℕ} {f f' : Term l m} {g g' : Term m n} :
      Rel k f f' → Rel k g g' → Rel k (f.comp g) (f'.comp g')
  | mulHom_congr {m₁ n₁ m₂ n₂ : ℕ} {f f' : Term m₁ n₁} {g g' : Term m₂ n₂} :
      Rel k f f' → Rel k g g' → Rel k (f.mul g) (f'.mul g')
  | addHom_congr {m₁ n₁ m₂ n₂ : ℕ} {f f' : Term m₁ n₁} {g g' : Term m₂ n₂} :
      Rel k f f' → Rel k g g' → Rel k (f.add g) (f'.add g')

  -- category
  | id_comp {m n : ℕ} (f : Term m n) : Rel k ((Term.id m).comp f) f
  | comp_id {m n : ℕ} (f : Term m n) : Rel k (f.comp (Term.id n)) f
  | assoc {l m n p : ℕ} (f : Term l m) (g : Term m n) (h : Term n p) :
      Rel k ((f.comp g).comp h) (f.comp (g.comp h))

  -- ◆
  | id_one_mulHom {m n : ℕ} (f : Term m n) :
      Rel k ((Term.id 1).mul f) ((cast (one_mul m)).comp (f.comp (cast (one_mul n).symm)))
  | mulHom_id_one {m n : ℕ} (f : Term m n) :
      Rel k (f.mul (Term.id 1)) ((cast (mul_one m)).comp (f.comp (cast (mul_one n).symm)))
  | mulHom_assoc {m₁ n₁ m₂ n₂ m₃ n₃ : ℕ} (f : Term m₁ n₁) (g : Term m₂ n₂) (h : Term m₃ n₃) :
      Rel k ((f.mul g).mul h)
        ((cast (mul_assoc m₁ m₂ m₃)).comp
          ((f.mul (g.mul h)).comp (cast (mul_assoc n₁ n₂ n₃).symm)))
  | id_mulHom_id (m n : ℕ) : Rel k ((Term.id m).mul (Term.id n)) (Term.id (m * n))
  | mulHom_comp_mulHom {l₁ m₁ n₁ l₂ m₂ n₂ : ℕ}
      (f₁ : Term l₁ m₁) (f₂ : Term l₂ m₂) (g₁ : Term m₁ n₁) (g₂ : Term m₂ n₂) :
      Rel k ((f₁.mul f₂).comp (g₁.mul g₂)) ((f₁.comp g₁).mul (f₂.comp g₂))
  | mulSwap_mulSwap (m n : ℕ) : Rel k ((mulSwap m n).comp (mulSwap n m)) (Term.id (m * n))
  | mulSwap_natural {m₁ n₁ m₂ n₂ : ℕ} (f : Term m₁ n₁) (g : Term m₂ n₂) :
      Rel k ((f.mul g).comp (mulSwap n₁ n₂)) ((mulSwap m₁ m₂).comp (g.mul f))
  | mulSwap_hexagon (a b c : ℕ) :
      Rel k (mulSwap a (b * c))
        ((cast (mul_assoc a b c).symm).comp <|
          ((mulSwap a b).mul (Term.id c)).comp <|
          (cast (mul_assoc b a c)).comp <|
          ((Term.id b).mul (mulSwap a c)).comp <|
          cast (mul_assoc b c a).symm)

  -- ◇
  | id_zero_addHom {m n : ℕ} (f : Term m n) :
      Rel k ((Term.id 0).add f) ((cast (zero_add m)).comp (f.comp (cast (zero_add n).symm)))
  | addHom_id_zero {m n : ℕ} (f : Term m n) :
      Rel k (f.add (Term.id 0)) ((cast (add_zero m)).comp (f.comp (cast (add_zero n).symm)))
  | addHom_assoc {m₁ n₁ m₂ n₂ m₃ n₃ : ℕ} (f : Term m₁ n₁) (g : Term m₂ n₂) (h : Term m₃ n₃) :
      Rel k ((f.add g).add h)
        ((cast (Nat.add_assoc m₁ m₂ m₃)).comp
          ((f.add (g.add h)).comp (cast (Nat.add_assoc n₁ n₂ n₃).symm)))
  | id_addHom_id (m n : ℕ) : Rel k ((Term.id m).add (Term.id n)) (Term.id (m + n))
  | addHom_comp_addHom {l₁ m₁ n₁ l₂ m₂ n₂ : ℕ}
      (f₁ : Term l₁ m₁) (f₂ : Term l₂ m₂) (g₁ : Term m₁ n₁) (g₂ : Term m₂ n₂) :
      Rel k ((f₁.add f₂).comp (g₁.add g₂)) ((f₁.comp g₁).add (f₂.comp g₂))
  | addSwap_addSwap (m n : ℕ) : Rel k ((addSwap m n).comp (addSwap n m)) (Term.id (m + n))
  | addSwap_natural {m₁ n₁ m₂ n₂ : ℕ} (f : Term m₁ n₁) (g : Term m₂ n₂) :
      Rel k ((f.add g).comp (addSwap n₁ n₂)) ((addSwap m₁ m₂).comp (g.add f))
  | addSwap_hexagon (a b c : ℕ) :
      Rel k (addSwap a (b + c))
        ((cast (Nat.add_assoc a b c).symm).comp <|
          ((addSwap a b).add (Term.id c)).comp <|
          (cast (Nat.add_assoc b a c)).comp <|
          ((Term.id b).add (addSwap a c)).comp <|
          cast (Nat.add_assoc b c a).symm)

  -- ◆ over ◇
  | id_zero_mulHom {m n : ℕ} (f : Term m n) :
      Rel k ((Term.id 0).mul f) ((cast (zero_mul m)).comp ((Term.id 0).comp (cast (zero_mul n).symm)))
  | mulHom_id_zero {m n : ℕ} (f : Term m n) :
      Rel k (f.mul (Term.id 0)) ((cast (mul_zero m)).comp ((Term.id 0).comp (cast (mul_zero n).symm)))
  | addHom_mulHom {m₁ n₁ m₂ n₂ m₃ n₃ : ℕ} (f : Term m₁ n₁) (g : Term m₂ n₂) (h : Term m₃ n₃) :
      Rel k ((f.add g).mul h)
        ((cast (add_mul m₁ m₂ m₃)).comp
          (((f.mul h).add (g.mul h)).comp (cast (add_mul n₁ n₂ n₃).symm)))
  | distrib_square (a b c : ℕ) :
      Rel k ((cast (add_mul a b c)).comp (addSwap (a * c) (b * c)))
        (((addSwap a b).mul (Term.id c)).comp (cast (add_mul b a c)))
  | distrib_pentagon (a b c d : ℕ) :
      Rel k
        ((cast (add_mul a b (c + d))).comp <|
          ((distrib a c d).add (distrib b c d)).comp <|
          addMedial (a * c) (a * d) (b * c) (b * d))
        ((distrib (a + b) c d).comp ((cast (add_mul a b c)).add (cast (add_mul a b d))))

  -- Axioms [1]–[3]
  | V_V : Rel k (V.comp V) X
  | V_S_V : Rel k (V.comp ((S k).comp V)) ((S k).comp (V.comp (S k)))
  | zeta_pow : Rel k (zeta.npow (2 ^ k)) (Term.id 1)

def setoid (k m n : ℕ) : Setoid (Term m n) where
  r := Rel k
  iseqv := ⟨Rel.refl, Rel.symm, Rel.trans⟩

@[ext]
structure PiK (k : ℕ) where
  n : ℕ

namespace PiK

variable {k : ℕ}

instance : Category (PiK k) where
  Hom X Y := Quotient (setoid k X.n Y.n)
  id X := Quotient.mk _ (.id X.n)
  comp := Quotient.map₂ Term.comp fun _ _ hf _ _ hg => Rel.comp_congr hf hg
  id_comp := by
    rintro _ _ ⟨f⟩; exact Quotient.sound (Rel.id_comp f)
  comp_id := by
    rintro _ _ ⟨f⟩; exact Quotient.sound (Rel.comp_id f)
  assoc := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩; exact Quotient.sound (Rel.assoc f g h)

/-- The morphism represented by a term. -/
abbrev ofTerm {X Y : PiK k} (t : Term X.n Y.n) : X ⟶ Y := Quotient.mk (setoid k X.n Y.n) t

theorem ofTerm_eq_ofTerm {X Y : PiK k} {t t' : Term X.n Y.n} (h : Rel k t t') : ofTerm t = ofTerm t' :=
  Quotient.sound h

theorem eqToHom_eq {X Y : PiK k} (h : X = Y) :
    eqToHom h = ofTerm (Term.cast (congrArg PiK.n h)) := by
  subst h; rfl

/-- Reduce a `≍` between represented morphisms to a `Rel` with conjugating casts. -/
theorem ofTerm_heq_ofTerm {X Y X' Y' : PiK k} (hX : X = X') (hY : Y = Y')
    {t : Term X.n Y.n} {t' : Term X'.n Y'.n}
    (h : Rel k t ((Term.cast (congrArg PiK.n hX)).comp
      (t'.comp (Term.cast (congrArg PiK.n hY).symm)))) :
    ofTerm t ≍ ofTerm t' := by
  rw [← conj_eqToHom_iff_heq _ _ hX hY, eqToHom_eq, eqToHom_eq]
  exact Quotient.sound h

open BipermutativeCategory

instance instMul : StrictMulSymmetricMonoidalCategory (PiK k) where
  mulObj X Y := ⟨X.n * Y.n⟩
  mulUnit := ⟨1⟩
  mulHom := Quotient.map₂ Term.mul fun _ _ hf _ _ hg => Rel.mulHom_congr hf hg

  mulObj_assoc X Y Z := PiK.ext (mul_assoc X.n Y.n Z.n)
  one_mulObj X := PiK.ext (one_mul X.n)
  mulObj_one X := PiK.ext (mul_one X.n)

  id_one_mulHom_heq := by
    rintro X Y ⟨f⟩
    exact ofTerm_heq_ofTerm (PiK.ext (one_mul X.n)) (PiK.ext (one_mul Y.n)) (Rel.id_one_mulHom f)
  mulHom_id_one_heq := by
    rintro X Y ⟨f⟩
    exact ofTerm_heq_ofTerm (PiK.ext (mul_one X.n)) (PiK.ext (mul_one Y.n)) (Rel.mulHom_id_one f)
  mulHom_assoc_heq := by
    rintro X₁ Y₁ X₂ Y₂ X₃ Y₃ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact ofTerm_heq_ofTerm (PiK.ext (mul_assoc X₁.n X₂.n X₃.n)) (PiK.ext (mul_assoc Y₁.n Y₂.n Y₃.n))
      (Rel.mulHom_assoc f g h)
  id_mulHom_id X Y := Quotient.sound (Rel.id_mulHom_id X.n Y.n)
  mulHom_comp_mulHom := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact Quotient.sound (Rel.mulHom_comp_mulHom f₁ f₂ g₁ g₂)

  mulSwap X Y := ofTerm (Term.mulSwap X.n Y.n)
  mulSwap_mulSwap X Y := Quotient.sound (Rel.mulSwap_mulSwap X.n Y.n)
  mulSwap_natural := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩
    exact Quotient.sound (Rel.mulSwap_natural f g)
  mulSwap_hexagon X Y Z := by
    simp only [eqToHom_eq]
    exact Quotient.sound (Rel.mulSwap_hexagon X.n Y.n Z.n)

instance instAdd : StrictAddSymmetricMonoidalCategory (PiK k) where
  addObj X Y := ⟨X.n + Y.n⟩
  addUnit := ⟨0⟩
  addHom := Quotient.map₂ Term.add fun _ _ hf _ _ hg => Rel.addHom_congr hf hg

  addObj_assoc X Y Z := PiK.ext (Nat.add_assoc X.n Y.n Z.n)
  zero_addObj X := PiK.ext (zero_add X.n)
  addObj_zero X := PiK.ext (add_zero X.n)

  id_zero_addHom_heq := by
    rintro X Y ⟨f⟩
    exact ofTerm_heq_ofTerm (PiK.ext (zero_add X.n)) (PiK.ext (zero_add Y.n)) (Rel.id_zero_addHom f)
  addHom_id_zero_heq := by
    rintro X Y ⟨f⟩
    exact ofTerm_heq_ofTerm (PiK.ext (add_zero X.n)) (PiK.ext (add_zero Y.n)) (Rel.addHom_id_zero f)
  addHom_assoc_heq := by
    rintro X₁ Y₁ X₂ Y₂ X₃ Y₃ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact ofTerm_heq_ofTerm (PiK.ext (Nat.add_assoc X₁.n X₂.n X₃.n))
      (PiK.ext (Nat.add_assoc Y₁.n Y₂.n Y₃.n)) (Rel.addHom_assoc f g h)
  id_addHom_id X Y := Quotient.sound (Rel.id_addHom_id X.n Y.n)
  addHom_comp_addHom := by
    rintro _ _ _ _ _ _ ⟨f₁⟩ ⟨f₂⟩ ⟨g₁⟩ ⟨g₂⟩
    exact Quotient.sound (Rel.addHom_comp_addHom f₁ f₂ g₁ g₂)

  addSwap X Y := ofTerm (Term.addSwap X.n Y.n)
  addSwap_addSwap X Y := Quotient.sound (Rel.addSwap_addSwap X.n Y.n)
  addSwap_natural := by
    rintro _ _ _ _ ⟨f⟩ ⟨g⟩
    exact Quotient.sound (Rel.addSwap_natural f g)
  addSwap_hexagon X Y Z := by
    simp only [eqToHom_eq]
    exact Quotient.sound (Rel.addSwap_hexagon X.n Y.n Z.n)

@[simp] theorem mulObj_n (X Y : PiK k) : (X ◆ Y).n = X.n * Y.n := rfl
@[simp] theorem mulUnit_n : (𝐈_ (PiK k)).n = 1 := rfl
@[simp] theorem addObj_n (X Y : PiK k) : (X ◇ Y).n = X.n + Y.n := rfl
@[simp] theorem addUnit_n : (𝐎_ (PiK k)).n = 0 := rfl

instance instBase : BipermutativeCategoryBase (PiK k) where
  zero_mulObj X := PiK.ext (zero_mul X.n)
  id_zero_mulHom_heq := by
    rintro X Y ⟨f⟩
    exact ofTerm_heq_ofTerm (PiK.ext (zero_mul X.n)) (PiK.ext (zero_mul Y.n))
      (Rel.id_zero_mulHom f)
  mulObj_zero X := PiK.ext (mul_zero X.n)
  mulHom_id_zero_heq := by
    rintro X Y ⟨f⟩
    exact ofTerm_heq_ofTerm (PiK.ext (mul_zero X.n)) (PiK.ext (mul_zero Y.n))
      (Rel.mulHom_id_zero f)
  addObj_mulObj X Y Z := PiK.ext (add_mul X.n Y.n Z.n)
  addHom_mulHom_heq := by
    rintro X₁ Y₁ X₂ Y₂ X₃ Y₃ ⟨f⟩ ⟨g⟩ ⟨h⟩
    exact ofTerm_heq_ofTerm (PiK.ext (add_mul X₁.n X₂.n X₃.n)) (PiK.ext (add_mul Y₁.n Y₂.n Y₃.n))
      (Rel.addHom_mulHom f g h)

theorem distrib_eq (X Y Z : PiK k) : δ_ X Y Z = ofTerm (Term.distrib X.n Y.n Z.n) := by
  simp only [distrib, eqToHom_eq]; rfl

theorem addMedial_eq (X Y Z W : PiK k) :
    addMedial X Y Z W = ofTerm (Term.addMedial X.n Y.n Z.n W.n) := by
  simp only [addMedial_def, eqToHom_eq]; rfl

instance : BipermutativeCategory (PiK k) where
  distrib_square X Y Z := by
    simp only [eqToHom_eq]
    exact Quotient.sound (Rel.distrib_square X.n Y.n Z.n)
  distrib_pentagon X Y Z W := by
    simp only [distrib_eq, addMedial_eq, eqToHom_eq]
    exact Quotient.sound (Rel.distrib_pentagon X.n Y.n Z.n W.n)

/-! ### Generators and Axioms [1]–[3] -/

variable (k) in
def ζ : Scalar (PiK k) := ofTerm Term.zeta

def V : (𝐈 ◇ 𝐈 : PiK k) ⟶ 𝐈 ◇ 𝐈 := ofTerm Term.V

def S : (𝐈 ◇ 𝐈 : PiK k) ⟶ 𝐈 ◇ 𝐈 := 𝟙 𝐈 ◇ₘ (ζ k ^ 2 ^ (k - 2))

def X : (𝐈 ◇ 𝐈 : PiK k) ⟶ 𝐈 ◇ 𝐈 := σ_◇ 𝐈 𝐈

theorem ζ_pow_eq (j : ℕ) : ζ k ^ j = ofTerm (Term.zeta.npow j) := by
  induction j with
  | zero => rw [pow_zero]; rfl
  | succ j ih => rw [pow_succ', ih, Scalar.mul_def]; rfl

theorem V_V : (V ≫ V : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) = X :=
  Quotient.sound Rel.V_V

theorem V_S_V : (V ≫ S ≫ V : (𝐈 ◇ 𝐈 : PiK k) ⟶ _) = S ≫ V ≫ S := by
  simp only [S, ζ_pow_eq]
  exact ofTerm_eq_ofTerm Rel.V_S_V

theorem ζ_pow_two_k : ζ k ^ 2 ^ k = 1 := by
  rw [ζ_pow_eq]
  exact Quotient.sound Rel.zeta_pow

end PiK

end FreeQuantum
