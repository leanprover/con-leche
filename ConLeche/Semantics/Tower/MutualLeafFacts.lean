module

public import ConLeche.Semantics.Tower.MutualLeafI

@[expose] public section

/-!
# Facts about the tag objects (task #278, M2.4)

Two general facts the mutual block's chain reasoning needs beside
`MutualLeafI.lean`'s laws.

* **A lift mentions no shallow slot** (`NoBVar_liftN`): `e.liftN d 0`
  pushes every free variable of `e` to `d` and above, so it mentions
  none of a set of slots that all lie below `d`.  A tagged tuple's
  head is the member's tupler lifted past the fields read so far
  (`tagTupleAV`), and the recursive slots the X-chain's walk hides
  all lie below that lift — which is what the walk's no-mention
  premises ask.
* **The index telescopes' grading is monotone in the tag's sort**
  (`IdxOk.mono`): the tag's sort `W` is a join over the members'
  index sorts, so each member's telescope is graded at its own sort
  and must be read at `W`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## A lift mentions no slot below the lift -/

omit [SetTheory V] in
/-- **A lift mentions no slot below it**: `liftN d k` leaves the `k`
bound slots alone and pushes everything else to `d + k` and above, so
a predicate holding only between `k` and `d + k` catches nothing. -/
theorem NoBVar_liftN : ∀ (e : AnnotTerm) {d k : Nat} {P : Nat → Prop},
    (∀ i, P i → k ≤ i ∧ i < d + k) → NoBVar P (e.liftN d k) := by
  intro e
  induction e with
  | bvar i =>
    intro d k P hP
    show ¬ P (if i < k then i else i + d)
    split
    · next hik => intro hp; have := (hP i hp).1; omega
    · next hik => intro hp; have := (hP (i + d) hp).2; omega
  | sort _ => intros; trivial
  | const _ _ => intros; trivial
  | prf => intros; trivial
  | app f a ihf iha => intro d k P hP; exact ⟨ihf hP, iha hP⟩
  | eqE a b iha ihb => intro d k P hP; exact ⟨iha hP, ihb hP⟩
  | fst e ih => intro d k P hP; exact ih hP
  | snd e ih => intro d k P hP; exact ih hP
  | lam _ A b ihA ihb =>
    intro d k P hP
    refine ⟨ihA hP, ihb (k := k + 1) (P := shiftP P) ?_⟩
    intro i hi
    cases i with
    | zero => exact hi.elim
    | succ i => have := hP i hi; omega
  | pi _ _ A B ihA ihB =>
    intro d k P hP
    refine ⟨ihA hP, ihB (k := k + 1) (P := shiftP P) ?_⟩
    intro i hi
    cases i with
    | zero => exact hi.elim
    | succ i => have := hP i hi; omega

omit [SetTheory V] in
/-- The zero-depth case: every slot of `P` lies below the lift. -/
theorem NoBVar_liftN_zero {P : Nat → Prop} {d : Nat} (hP : ∀ i, P i → i < d)
    (e : AnnotTerm) : NoBVar P (e.liftN d 0) :=
  NoBVar_liftN e fun i hi => ⟨Nat.zero_le i, by simpa using hP i hi⟩

/-! ## The gradings are monotone in the universe -/

end ConLeche.Semantics
