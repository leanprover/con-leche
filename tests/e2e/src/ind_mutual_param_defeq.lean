--#export MB2.self

/- End-to-end fixture (task #208; inductive audit #206, A4 / crack C4,
   the PARAMETER variant): a mutual block whose members' parameter
   domains are definitionally but not syntactically equal (`Type` vs
   `id Type`).  Official compares them with `is_def_eq`
   (`check_inductive_types`, inductive.cpp:230) and accepts; Lean's own
   elaborator writes the block down as it stands.

   (`h : id True` on the FIRST member makes `id` a dependency of the
   block's first member: the arena's official checker replays constants
   by dependency and otherwise never sees `id`, which only the second
   member's type mentions.)

   official: 0.  con-leche: 0.  The bad twin ind_mutual_param_bad
   (scripts/mk_mutual_bad.py) rejects, as official does.
   Probe of record: _tmp/indaudit/probes/P/MutualParamDefEq.lean. -/
mutual
  inductive MA2 (α : Type) : Type
    | mk (b : MB2 α) (h : id True)
  inductive MB2 (α : id Type) : Type
    | mk (a : MA2 α)
    | nil
end

theorem MB2.self (b : MB2 Nat) : b = b := rfl
