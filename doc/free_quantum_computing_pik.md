# Πk as a Quotient of Circuit Terms

How to read `FreeQuantum/PiK.lean`, which builds `PiK k`, the free model of
reversible quantum computing Πk ("Free quantum computing", Carette et al., 2026,
Theorem 1 / SI Proposition S5), and `FreeQuantum/Model.lean`, which interprets
it in any model (SI Proposition S9).

## The Presentation

- Generators: `ζk : 1 → 1` and `V : 1 ⊕ 1 → 1 ⊕ 1`.
- Derived gates: `X := σ⊕[1,1]` (NOT) and `S := id₁ ⊕ ζk^(2^(k-2))`.
- Axioms: [1] `V ≫ V = X`, [2] `V ≫ S ≫ V = S ≫ V ≫ S`, [3] `ζk^(2^k) = 1`,
  on top of the bipermutative category laws (SI Definition S1, `FreeQuantum.Bipermutative`).

Prose below uses the paper's `⊗`/`⊕`; Lean code writes them `◆`/`◇` (`◆ₘ`/`◇ₘ` on
morphisms, `σ_◆`/`σ_◇` for the swaps), e.g. `X` is `σ_◇ 𝐈 𝐈`.

It works like a group presentation: `Term` plays the role of words over the
generators, `Rel` the relations, and `PiK k` the presented object. The
construction follows Mathlib's `FreeMonoidalCategory`
(`CategoryTheory/Monoidal/Free/Basic.lean`: `Hom` / `HomEquiv` / `setoidHom`).

## Why Strict

`PiK k` is built strict from the start: objects are `ℕ`, and `⊗`/`⊕` are
associative, unital and distributive as object equalities (a PROP, SI
Definition S1). As far as we know, this is the first formalization to take this
route. The existing ones are in Agda and are non-strict: `SqrtPi` (POPL 2024)
and `QuantumPi` (ICFP 2024), both built on agda-categories' `RigCategory`.
Mathlib has no strict monoidal or rig category either; it notes that "in Lean,
it is considered difficult to formalize the concept of strict monoidal
categories due to the feature of dependent type theory"
(`Mathlib/Tactic/CategoryTheory/Coherence/Normalize.lean`). The closest it has
is `Bicategory.Strict` (`Mathlib/CategoryTheory/Bicategory/Strict/Basic.lean`),
a `Prop` mixin on an up-to-iso bicategory saying that the associators and
unitors are `eqToIso` of equalities, since they cannot be literal identities
when 2-morphism types depend on 1-morphisms.

- **It states the paper's theorem as written.** Theorem 1 says `Πk` is free
  among *bipermutative* (strict) categories. Over rig categories, freeness
  becomes 2-categorical: functors preserve structure only up to coherent iso,
  and the lift is unique only up to natural iso. Here it is an equation of
  functors, proved by `Quotient.ind` and induction on `Term`.
- **No rig-category coherence.** A rig category carries associators, unitors,
  distributors and annihilators as isomorphisms, subject to Laplaza's
  coherence axioms. Not every formal diagram commutes, and neither Mathlib nor
  agda-categories has a coherence tactic for rig categories. In `Rel`, all of
  these are object equations. Only `σ_◆`, `σ_◇` and `δ_` remain as morphisms,
  with a few laws (hexagons, `distrib_square`, `distrib_pentagon`).
- **Circuits on `n` wires.** `Term m n` is indexed by system sizes, so models
  are `Fin n`-indexed permutations and matrices (`FinPerm`, `FinLin`), and
  object equations such as `1 + 1 = 2` often hold by `rfl`.

There are two costs:

- **Casts.** Object equations that are not definitional, such as
  `(m + n) * p = m * p + n * p`, are handled with `eqToHom`/`HEq` (see below).
- **Models must be strict.** Hilbert spaces and `ModuleCat` with
  `TensorProduct` are rig categories only up to iso, so they are not direct
  targets of `Model`. The paper bridges this gap by the theorem that every rig
  category is rig equivalent to a bipermutative one; that theorem is not
  formalized here.

## Reading the Pieces

- **`Term m n` is a circuit, not a state.** It is syntax for a process from an
  `m`-dimensional system to an `n`-dimensional one, built from identity,
  composition, `⊗`, `⊕`, the two swaps, `zeta`, and `V`. A state would be a
  morphism `1 ⟶ n`. Every generator of Πk is `n → n`, so state preparation only
  appears with the measurement extension (`R`, `LR`, `Split(LR)`).
- **`Rel k t t'` relates pairs of terms.** Every `Term` is allowed. The relation
  holds only when there is a derivation from its constructors: the laws and
  axioms, chained with `refl`/`symm`/`trans` and applied inside larger circuits
  via the `*_congr` constructors. It is the smallest relation that contains the
  laws and is compatible with composition, `⊗` and `⊕`. Being the smallest is
  what makes the result *free*.
- **Equivalent vs. equal.** Related terms stay distinct as syntax, but become
  equal as morphisms: `ofTerm t = ofTerm t'` iff `Rel k t t'`
  (`Quotient.sound` / `Quotient.exact`).
- **One setoid per hom-set.** `setoid k m n` lives on `Term m n`, so only circuits
  with the same input and output sizes are ever compared.
- **A morphism is one equivalence class.** `X ⟶ Y` is
  `Quotient (setoid k X.n Y.n)`, and `ofTerm t` is the class of `t`. Composition,
  `◆ₘ` and `◇ₘ` don't depend on the representative, thanks to the `*_congr`
  constructors (the argument to `Quotient.map₂`).
- **Objects are system sizes.** An object is a `PiK k` structure wrapping
  `n : ℕ`, e.g. `2 = 1 ◇ 1` is a qubit and `2 ◆ 2 = 4` is two qubits. The wrapper
  keeps the category instance off `ℕ` (same pattern as `FinPerm` and `FinLin`).
- **`k` is the precision.** It appears only in Axioms [2] and [3] (via `S` and
  `ζ ^ 2 ^ k = 1`). The `Term`s are the same for every `k`, but `Rel k` differs,
  so each `k` gives a different category.

## Laws up to Object Equations

Laws whose two sides only have equal types up to an object equation (e.g.
`(f ◆ₘ g) ◆ₘ h ≍ f ◆ₘ (g ◆ₘ h)`) are stated in `Rel` as conjugation by
`Term.cast`, the term counterpart of `eqToHom`. This is the shape of the Eq
versions in `Bipermutative`, and each `Rel` constructor carries the name of the law it states
(`Rel.mulHom_assoc` ↔ `mulHom_assoc`). The instance fields are the `_heq`
forms (`mulHom_assoc_heq`); `ofTerm_heq_ofTerm` turns a `Rel` constructor
into one via Mathlib's `conj_eqToHom_iff_heq`. Because every law is a `Rel`
constructor, each field of the `BipermutativeCategory` instance is a one-line
`Quotient.sound`.

## Models (`Model`)

- **A model is a choice of two morphisms.** `M : Model k C` consists of
  `M.ζ : 𝐈 ⟶ 𝐈` and `M.V : 𝐈 ◇ 𝐈 ⟶ 𝐈 ◇ 𝐈` in a bipermutative category `C`,
  plus proofs of Axioms [1]–[3]. (`M.natObj` is forced by strictness.)
- **`C` does not fix the model.** The same `C` can have several models, e.g.
  `stdModel k hk : Model k FinLin` and its complex conjugate. `C` can also have
  none (`FinPerm`: no `V` with `V ≫ V = X`) or only trivial ones (`Discrete ℕ`).
- **`M.eval : Term m n → (M.natObj m ⟶ M.natObj n)` interprets terms.** `eval_sound`:
  if `Rel k t t'` then `M.eval t = M.eval t'`. Equivalent terms evaluate to the
  same morphism, i.e. `Rel k` is sound for `M`.
- **`M.lift : PiK k ⥤ C` is `Quotient.lift M.eval M.eval_sound`.** It sends
  `PiK.ζ ↦ M.ζ` and `PiK.V ↦ M.V` (up to `eqToHom`), and everything else
  follows, since every morphism of `PiK k` is built from these with `𝟙`, `≫`,
  `◆ₘ`, `◇ₘ` and the swaps.
- **Non-triviality of `Πk`.** `stdModel` shows that `Rel k` does not identify `V`
  with `𝟙` or `ζ` with `1` (`V_ne_id`, `ζ_ne_one`).

## Freeness (`Free`)

Freeness is existence (`M.lift`) plus uniqueness: `lift_unique` shows a
`BipermutativeFunctor` out of `PiK k` is determined by where it sends `PiK.ζ`
and `PiK.V`, and `BipermutativeFunctor.modelEquiv` packages both as
`Model k C ≃ BipermutativeFunctor (PiK k) C`.

## What This Does Not Yet Show

- **Completeness.** Soundness is "derivable implies true in `M`". The converse,
  "true in `M` implies derivable" (`M.lift` faithful), is not planned.
