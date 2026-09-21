--#export InModelMutualRefl.red_of_infer InModelMutualRefl.infer_le InModelMutualRefl.red_le InModelMutualRefl.size_example InModelMutualRefl.count_example

/- End-to-end test: MUTUAL blocks with REFLEXIVE members modelled
   IN-PROCESS (2026-09-21).  The export flags a member `isReflexive`
   when a constructor field is a FUNCTION into the block, `∀ a⃗, T_m p⃗ e⃗`;
   the mutual rung used to decline on the flag (a shortcut of the port
   from lean-inductive-models, whose auxiliary family Lean's own kernel
   gave a recursor with the reflexive hypotheses).  Now the rung
   rewrites the occurrence under the field's binders, emits the
   auxiliary recursor with `∀ a⃗, motive e⃗(a⃗) (f a⃗)` hypotheses (the
   fixpoint route's own generators) and states each iota theorem with
   `λ a⃗, T_m.rec._model … (f a⃗)` at the reflexive field.

   Three shapes.  `Red`/`Infer` is the checker's OWN rules tier in
   miniature (`ConLeche.Rules.Red`, the block the self-check declined
   on): an indexed `Prop` pair whose premises are GUARDED by an
   equation, `(g = .full → Infer g d a b)`, which is a reflexive field
   with a `Prop` domain; `infer_le` eliminates it by mutual induction,
   consuming the reflexive hypotheses `g = .full → b ≤ c` at both
   guards.  `Tree`/`Forest` is a data pair with a function field across
   the block (`Nat → Forest`) beside finitary and reflexive fields of
   one constructor; `size_example`'s `rfl` forces iota through the
   model recursors, applying a reflexive hypothesis.  `A`/`B` is an
   indexed data pair whose reflexive field is at the member's index
   (`Fin (n+1) → B n`; `B.up` lands at a shifted index so that `n`
   stays an index — Lean promotes a uniform one to a parameter). -/

namespace InModelMutualRefl

inductive Grade where
  | full
  | io

mutual
inductive Red : Nat → Nat → Nat → Prop where
  | refl : ∀ d e, Red d e e
  | trans : ∀ d a b c, Red d a b → Red d b c → Red d a c
  | guarded : ∀ (g : Grade) d a b,
      (g = .io → Infer g d a b) → (g = .full → Infer g d a b) → Red d a b
inductive Infer : Grade → Nat → Nat → Nat → Prop where
  | base : ∀ g d a, Infer g d a a
  | step : ∀ g d a b c, Red d a b →
      (g = .full → Infer g d b c) → (g = .io → Infer g d b c) → Infer g d a c
end

theorem red_of_infer (d a b : Nat) (h : Infer .full d a b) : Red d a b :=
  .guarded .full d a b (fun hio => nomatch hio) (fun _ => h)

-- mutual induction into a `Prop` motive; at `guarded` and `step` the
-- inductive hypotheses are the reflexive ones, `g = .io → a ≤ b` and
-- `g = .full → a ≤ b`, discharged by a case split on the grade
theorem infer_le : ∀ g d a b, Infer g d a b → a ≤ b := fun _ _ _ _ h =>
  Infer.rec (motive_1 := fun _ a b _ => a ≤ b) (motive_2 := fun _ _ a b _ => a ≤ b)
    (fun _ _ => Nat.le_refl _)
    (fun _ _ _ _ _ _ ih1 ih2 => Nat.le_trans ih1 ih2)
    (fun g _ _ _ _ _ ih1 ih2 =>
      match g with
      | .io => ih1 rfl
      | .full => ih2 rfl)
    (fun _ _ _ => Nat.le_refl _)
    (fun g _ _ _ _ _ _ _ ih1 ih2 ih3 =>
      match g with
      | .full => Nat.le_trans ih1 (ih2 rfl)
      | .io => Nat.le_trans ih1 (ih3 rfl))
    h

theorem red_le : ∀ d a b, Red d a b → a ≤ b := fun _ _ _ h =>
  Red.rec (motive_1 := fun _ a b _ => a ≤ b) (motive_2 := fun _ _ a b _ => a ≤ b)
    (fun _ _ => Nat.le_refl _)
    (fun _ _ _ _ _ _ ih1 ih2 => Nat.le_trans ih1 ih2)
    (fun g _ _ _ _ _ ih1 ih2 =>
      match g with
      | .io => ih1 rfl
      | .full => ih2 rfl)
    (fun _ _ _ => Nat.le_refl _)
    (fun g _ _ _ _ _ _ _ ih1 ih2 ih3 =>
      match g with
      | .full => Nat.le_trans ih1 (ih2 rfl)
      | .io => Nat.le_trans ih1 (ih3 rfl))
    h

mutual
inductive Tree where
  | leaf : Tree
  | node : (Nat → Forest) → Tree
inductive Forest where
  | nil : Forest
  | cons : Tree → (Bool → Tree) → Forest → Forest
end

noncomputable def Tree.size (t : Tree) : Nat :=
  Tree.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    1 (fun _ ih => ih 0 + 1)
    0 (fun _ _ _ ih1 ih2 ih3 => ih1 + ih2 true + ih3) t

theorem size_example :
    Tree.size (.node fun _ => .cons .leaf (fun _ => .leaf) .nil) = 3 := rfl

mutual
inductive A : Nat → Type where
  | mk : ∀ n, (Fin (n + 1) → B n) → A n
inductive B : Nat → Type where
  | leaf : ∀ n, B n
  | up : ∀ n, A n → B (n + 1)
end

noncomputable def A.count (n : Nat) (a : A n) : Nat :=
  A.rec (motive_1 := fun _ _ => Nat) (motive_2 := fun _ _ => Nat)
    (fun n _ ih => ih ⟨0, Nat.succ_pos n⟩ + 1)
    (fun _ => 0) (fun _ _ ih => ih + 1) a

theorem count_example :
    A.count 3 (.mk 3 fun _ => .up 2 (.mk 2 fun _ => .leaf 2)) = 3 := rfl

end InModelMutualRefl
