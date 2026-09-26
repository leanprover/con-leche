--#export L.len_cons

/- End-to-end fixture (task #208; inductive audit #206, §2 "not an
   accept-subset after all"): the RECURSIVE arm of the def-headed-former
   family.  `L`'s former is declared at `MyType := Type`.  The
   recursive twin of ind_defhead_struct / ind_defhead_k /
   ind_defhead_mutual.

   official: 0.  con-leche: 0.
   Probe of record: _tmp/indaudit/probes/P/DefHeadFixOnly.lean. -/
def MyType := Type

inductive L : MyType
  | nil
  | cons (h : Nat) (t : L)

noncomputable def L.len : L → Nat := fun l => L.rec 0 (fun _ _ ih => ih + 1) l

theorem L.len_cons : L.len (L.cons 3 L.nil) = 1 := rfl
