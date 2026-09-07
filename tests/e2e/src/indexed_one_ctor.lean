/- End-to-end test (task #175 SigmaHom, 2026-09-06): an *indexed*
   one-constructor family in `Type` — the shape of Mathlib's
   `CategoryTheory.Sigma.SigmaHom` (parameters, two indices built from
   the fields, dependent fields, a `Type`-valued former).  It is not
   structure-like by the official kernel's test (`is_non_rec_structure`:
   one constructor AND no indices), yet the model family carries
   `IdxHom._model.proj_{0..3}` artifacts for it (its indexed-fibre
   projection tranche).  The checker must ignore those at install — an
   indexed family gets no projection functions — instead of declining
   at the structure-shaped residual pin.  `IdxHom.val` consumes the
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
