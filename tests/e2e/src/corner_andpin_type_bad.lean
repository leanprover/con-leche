prelude
--#export And.fst

/- Corner case (lane ANDPIN, 2026-09-30): `And` is pinned.  This stream
   declares `And` as a `Type`-valued pair of proofs — a valid inductive,
   the standard constructor, the wrong sort — and uses it.  The fold
   rejects the block (`andPinOk`).  Official 0 (no pins).  Today 1;
   that is the target. -/

inductive And (a b : Prop) : Type where
  | intro (left : a) (right : b) : And a b

theorem And.fst {a b : Prop} (h : And a b) : a :=
  And.rec (motive := fun _ => a) (fun l _ => l) h
