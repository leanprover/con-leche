--#export T.rec T.rec_1 T.rec_2
-- F18's good twin (lane NESTIND s27): a container `C` whose constructor
-- holds `C` UNAPPLIED inside the phantom `Wrap` (accepted up to official
-- v4.33.0; v4.33.1+ rejects `C`, `check_uniform_ind_occs`), nested in
-- `T`.  The walk of `C`'s frame at `[T]` visits `Wrap H` (`H` the frame's
-- hole, bare) — a node whose read-back key `Wrap C` names no member of
-- `T`.  Here `T.mk`'s second field is the legitimate nested class
-- `Wrap (fun _ => T)`; the bad twin (`scripts/mk_nestind_f18_bad.py`)
-- repoints that class, field and recursor to `Wrap C`.
structure Wrap (F : Type → Type) : Type where
  mk ::
inductive C (α : Type) : Type where
  | mk (w : Wrap C) : C α
set_option genSizeOfSpec false in
inductive T : Type where
  | mk (c : C T) (k : Wrap (fun (_ : Type) => T)) : T
