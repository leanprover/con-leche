--#export L.len_cons

/- End-to-end fixture (task #208; inductive audit #206, §2 "not an
   accept-subset after all"): the RECURSIVE arm of the def-headed-former
   family.  `L`'s former is declared at `MyType := Type`, so the fixpoint
   recogniser's syntactic telescope pin (RecParts.lean:347) does not take
   it — but the preprocessor's native predicate agrees, models the block,
   and the modelled stream accepts.  This is the CLEAN twin of
   ind_defhead_struct / ind_defhead_k / ind_defhead_mutual: a regression
   guard that the tool keeps covering the recursive arm.

   official: 0.  lech at master 700a06ca: 0 piped, 2 raw (missing model
   for L; both modes).
   Probe of record: _tmp/indaudit/probes/P/DefHeadFixOnly.lean. -/
def MyType := Type

inductive L : MyType
  | nil
  | cons (h : Nat) (t : L)

noncomputable def L.len : L → Nat := fun l => L.rec 0 (fun _ _ ih => ih + 1) l

theorem L.len_cons : L.len (L.cons 3 L.nil) = 1 := rfl
