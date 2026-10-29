import Lean

/-!
## Toy `Term` / `Rel` and a reflective tactic

One object, generators `a`, `b`, and `Rel` the smallest congruence containing the category laws
and `a ≫ a ~ id`, `a ≫ b ≫ a ~ b ≫ a ≫ b`.

`toy` proves `Rel t t'` for closed terms by reflection:
- normalization: `Term.flatten` sends a term to its word of generators (`flatten_sound`);
- search: breadth-first over rewrites of words by the axioms, at runtime, unverified;
- certificate: the steps found are re-checked by `check` in the kernel (`of_check`).

`toy?` also prints the steps. `toy n` bounds the search depth (default 6).
-/

namespace Toy

inductive Gen
  | a
  | b
  deriving DecidableEq, Repr, Lean.ToExpr

inductive Term
  | id
  | comp (f g : Term)
  | gen (x : Gen)

local infixr:80 " ≫ " => Term.comp
local notation "𝐚" => Term.gen Gen.a
local notation "𝐛" => Term.gen Gen.b

inductive Rel : Term → Term → Prop
  | refl (f : Term) : Rel f f
  | symm {f g : Term} : Rel f g → Rel g f
  | trans {f g h : Term} : Rel f g → Rel g h → Rel f h
  | comp_congr {f f' g g' : Term} : Rel f f' → Rel g g' → Rel (f ≫ g) (f' ≫ g')
  | id_comp (f : Term) : Rel (.id ≫ f) f
  | comp_id (f : Term) : Rel (f ≫ .id) f
  | assoc (f g h : Term) : Rel ((f ≫ g) ≫ h) (f ≫ g ≫ h)
  | a_a : Rel (𝐚 ≫ 𝐚) .id
  | a_b_a : Rel (𝐚 ≫ 𝐛 ≫ 𝐚) (𝐛 ≫ 𝐚 ≫ 𝐛)

/-! ### Normalization -/

def Term.flatten : Term → List Gen
  | .id => []
  | .comp f g => f.flatten ++ g.flatten
  | .gen x => [x]

def ofList : List Gen → Term
  | [] => .id
  | x :: xs => .gen x ≫ ofList xs

theorem ofList_append (u v : List Gen) : Rel (ofList (u ++ v)) (ofList u ≫ ofList v) := by
  induction u with
  | nil => exact (Rel.id_comp _).symm
  | cons x u ih => exact (Rel.comp_congr (.refl _) ih).trans (Rel.assoc _ _ _).symm

theorem flatten_sound (t : Term) : Rel t (ofList t.flatten) := by
  induction t with
  | id => exact .refl _
  | comp f g ihf ihg => exact (Rel.comp_congr ihf ihg).trans (ofList_append _ _).symm
  | gen x => exact (Rel.comp_id _).symm

theorem of_flatten_eq {t t' : Term} (h : t.flatten = t'.flatten) : Rel t t' :=
  (flatten_sound t).trans (h ▸ (flatten_sound t').symm)

theorem ofList_context (u v : List Gen) {l r : List Gen} (h : Rel (ofList l) (ofList r)) :
    Rel (ofList (u ++ l ++ v)) (ofList (u ++ r ++ v)) :=
  (ofList_append _ _).trans <|
    (Rel.comp_congr
      ((ofList_append _ _).trans ((Rel.comp_congr (.refl _) h).trans (ofList_append _ _).symm))
      (.refl _)).trans
    (ofList_append _ _).symm

/-! ### Rewriting words -/

inductive Rule
  | a_a
  | a_b_a
  deriving DecidableEq, Repr, Lean.ToExpr

def Rule.lhs : Rule → List Gen
  | .a_a => [.a, .a]
  | .a_b_a => [.a, .b, .a]

def Rule.rhs : Rule → List Gen
  | .a_a => []
  | .a_b_a => [.b, .a, .b]

def Rule.all : List Rule := [.a_a, .a_b_a]

theorem Rule.sound : (r : Rule) → Rel (ofList r.lhs) (ofList r.rhs)
  | .a_a => (flatten_sound (𝐚 ≫ 𝐚)).symm.trans (Rel.a_a.trans (flatten_sound _))
  | .a_b_a => (flatten_sound (𝐚 ≫ 𝐛 ≫ 𝐚)).symm.trans (Rel.a_b_a.trans (flatten_sound _))

/-- Rewrite by `rule` at `pos`, left-to-right if `fwd`. -/
structure Step where
  pos : Nat
  rule : Rule
  fwd : Bool
  deriving Repr, Lean.ToExpr

def Step.src (s : Step) : List Gen := if s.fwd then s.rule.lhs else s.rule.rhs
def Step.tgt (s : Step) : List Gen := if s.fwd then s.rule.rhs else s.rule.lhs

theorem Step.sound (s : Step) : Rel (ofList s.src) (ofList s.tgt) := by
  unfold Step.src Step.tgt
  cases s.fwd
  · exact s.rule.sound.symm
  · exact s.rule.sound

def Step.apply (s : Step) (w : List Gen) : Option (List Gen) :=
  if (w.drop s.pos).take s.src.length = s.src then
    some (w.take s.pos ++ s.tgt ++ w.drop (s.pos + s.src.length))
  else none

theorem Step.apply_sound {s : Step} {w w' : List Gen} (h : s.apply w = some w') :
    Rel (ofList w) (ofList w') := by
  unfold Step.apply at h
  split at h
  · next hm =>
    cases h
    have hw : w = w.take s.pos ++ s.src ++ w.drop (s.pos + s.src.length) := by
      conv => lhs; rw [← List.take_append_drop s.pos w,
        ← List.take_append_drop s.src.length (w.drop s.pos), hm]
      simp [List.drop_drop]
    conv => arg 1; rw [hw]
    exact ofList_context _ _ s.sound
  · cases h

def check (w : List Gen) : List Step → List Gen → Bool
  | [], w' => w == w'
  | s :: ss, w' =>
    match s.apply w with
    | some w₁ => check w₁ ss w'
    | none => false

theorem check_sound {w w' : List Gen} {ss : List Step} (h : check w ss w' = true) :
    Rel (ofList w) (ofList w') := by
  induction ss generalizing w with
  | nil =>
    have : w = w' := by simpa [check] using h
    exact this ▸ .refl _
  | cons s ss ih =>
    unfold check at h
    split at h
    · next w₁ hs => exact (Step.apply_sound hs).trans (ih h)
    · cases h

theorem of_check (t t' : Term) (ss : List Step) (h : check t.flatten ss t'.flatten = true) :
    Rel t t' :=
  (flatten_sound t).trans ((check_sound h).trans (flatten_sound t').symm)

/-! ### Search -/

def neighbors (w : List Gen) : List (Step × List Gen) :=
  (List.range (w.length + 1)).flatMap fun pos ↦
    Rule.all.flatMap fun rule ↦
      [true, false].filterMap fun fwd ↦
        let s : Step := { pos, rule, fwd }
        (s.apply w).map (s, ·)

/-- Breadth-first search for at most `depth` steps from `src` to `tgt`. -/
def search (depth : Nat) (src tgt : List Gen) : Option (List Step) := Id.run do
  let mut frontier : List (List Gen × List Step) := [(src, [])]
  let mut visited : List (List Gen) := [src]
  for _ in [0:depth + 1] do
    for (w, ss) in frontier do
      if w == tgt then return some ss.reverse
    let mut next := []
    for (w, ss) in frontier do
      for (s, w') in neighbors w do
        unless visited.contains w' do
          visited := w' :: visited
          next := (w', s :: ss) :: next
    frontier := next.reverse
  return none

/-! ### Tactic -/

open Lean Meta Elab Tactic

partial def reifyTerm (e : Expr) : MetaM Term := do
  let e ← whnfR (← instantiateMVars e)
  match_expr e with
  | Term.id => return .id
  | Term.comp f g => return .comp (← reifyTerm f) (← reifyTerm g)
  | Term.gen x =>
    match_expr ← whnfR x with
    | Gen.a => return .gen .a
    | Gen.b => return .gen .b
    | _ => throwError "toy: unknown generator {x}"
  | _ => throwError "toy: not a closed term {e}"

def toyTactic (depth : Nat) (verbose : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let_expr Rel t t' := ty | throwError "toy: goal is not `Rel _ _`"
  let w := (← reifyTerm t).flatten
  let w' := (← reifyTerm t').flatten
  let some ss := search depth w w' | throwError "toy: no derivation within {depth} steps"
  if verbose then logInfo m!"{repr ss}"
  let pf ← mkAppM ``of_check #[t, t', toExpr ss, ← mkEqRefl (toExpr true)]
  goal.assign pf
  replaceMainGoal []

syntax "toy" (ppSpace num)? : tactic
syntax "toy?" (ppSpace num)? : tactic

elab_rules : tactic
  | `(tactic| toy $[$n]?) => toyTactic (n.map (·.getNat) |>.getD 6) false
  | `(tactic| toy? $[$n]?) => toyTactic (n.map (·.getNat) |>.getD 6) true

/-! ### Tests -/

-- normalization only
example : Rel ((𝐚 ≫ .id) ≫ (𝐛 ≫ 𝐚)) (𝐚 ≫ 𝐛 ≫ .id ≫ 𝐚) := by toy
-- one axiom, inside context
example : Rel (𝐛 ≫ (𝐚 ≫ 𝐚) ≫ 𝐛) (𝐛 ≫ 𝐛) := by toy
-- several steps, both directions
example : Rel (𝐛 ≫ 𝐚 ≫ 𝐛 ≫ 𝐚) (𝐚 ≫ 𝐛) := by toy?
example : Rel (𝐛 ≫ 𝐚 ≫ 𝐛 ≫ 𝐛 ≫ 𝐚 ≫ 𝐛) (𝐚 ≫ 𝐛 ≫ 𝐛 ≫ 𝐚) := by toy?
-- not derivable (needs `𝐛 ≫ 𝐛 ~ id`); bounded search just gives up
example : Rel (𝐚 ≫ 𝐛 ≫ 𝐚 ≫ 𝐛 ≫ 𝐚 ≫ 𝐛) .id := by
  fail_if_success toy
  sorry

end Toy
