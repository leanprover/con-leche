/- End-to-end test (task #175 SigmaHom): an *indexed*
   one-constructor family in `Type` — the shape of Mathlib's
   `CategoryTheory.Sigma.SigmaHom` (parameters, two indices built from
   the fields, dependent fields, a `Type`-valued former).  It is not
   structure-like by the official kernel's test (`is_non_rec_structure`:
   one constructor AND no indices), so the install stores no projection
   table for it (`checkBlockTables`).  `IdxHom.val` consumes the
   family through `casesOn` (the only elimination official admits: no
   `.proj` node on such a type is ever well-formed) and `val_mk` forces
   the indexed iota reduction. -/

--#export IdxHom.val_mk

structure Pt where
  n : Nat
  b : Bool

inductive IdxHom : Pt → Pt → Type where
  | mk : (i : Nat) → (x y : Bool) → (h : Eq x y) → IdxHom (Pt.mk i x) (Pt.mk i y)

noncomputable def IdxHom.val (a b : Pt) (h : IdxHom a b) : Bool :=
  IdxHom.casesOn (motive := fun _ _ _ => Bool) h (fun _ x _ _ => x)

theorem IdxHom.val_mk :
    Eq (IdxHom.val (Pt.mk Nat.zero true) (Pt.mk Nat.zero true)
      (IdxHom.mk Nat.zero true true (Eq.refl true))) true :=
  Eq.refl true
