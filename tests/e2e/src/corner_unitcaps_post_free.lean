--#export f

/- Corner case (lane UNITCAPS): `U` is a one-constructor, fieldless
   member of a RECURSIVE mutual block (`T.mk : U → T`).  The forged bad
   twin (`scripts/mk_unitcaps_bad.py`) states `f : P U a → P U b`, which
   needs unit-η at `U`; official's `is_def_eq_unit_like` requires
   `is_non_rec_structure`, so it rejects.  Official ACCEPTS this twin. -/

inductive P : (α : Type) → α → Prop
  | mk : P Nat 0

mutual
  inductive U : Type where
    | mk : U
  inductive T : Type where
    | mk : U → T
end

theorem f (a b : U) (x : P U a) : P U a := x
