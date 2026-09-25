--#export T

/- Corner case (lane UNITCAPS): a one-constructor, fieldless member `U`
   of a block that is RECURSIVE in official's sense — `T.mk`'s field
   domain mentions `U`, even though it reduces to `Nat`.  The forged
   bad twin (`scripts/mk_unitcaps_bad.py`) re-points the `@id` ascription
   to `P U b`, so typing the constructor needs `a =?= b : U`, which only
   unit-η at `U` would give; official's unit-η requires
   `is_non_rec_structure`, whose `is_rec` is the RAW occurrence.
   Official ACCEPTS this twin. -/

inductive P : (α : Type) → α → Prop
  | mk : P Nat 0

inductive R : (p : Prop) → p → Prop
  | mk : R True trivial

def Const (β : Type) (_ : Prop) : Type := β

mutual
  inductive U : Type where
    | mk : U
  inductive T : Type where
    | mk : Const Nat (∀ (a b : U) (x : P U a), R (P U a) (@id (P U a) x)) → T
end
