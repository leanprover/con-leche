--#export MB2.self

/- End-to-end fixture (task #208; inductive audit #206, A4 / crack C4,
   the PARAMETER variant): a mutual block whose members' parameter
   domains are definitionally but not syntactically equal (`Type` vs
   `id Type`).  Official compares them with `is_def_eq`
   (`check_inductive_types`, inductive.cpp:230) and accepts; Lean's own
   elaborator writes the block down as it stands.

   con-leche's in-process modeller compares the parameter telescopes and the
   result sorts SYNTACTICALLY (`piBinders … == …`,
   Frontend/InModel/Mutual.lean:164) and declines: "member MB2: parameter
   telescope or sort differs from MA2's".  The preprocessor's native
   predicate checks only counts, so the block stays in-process and the
   generator's decline is the run's — piped and raw alike.

   (`h : id True` on the FIRST member makes `id` a dependency of the
   block's first member: the arena's official checker replays constants
   by dependency and otherwise never sees `id`, which only the second
   member's type mentions.)

   official: 0.  con-leche at master 700a06ca: 2 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/MutualParamDefEq.lean.

   CLOSED by task #218: the modeller no longer compares the telescopes;
   it builds the auxiliary family over the first member's and emits
   `MB2._model : ∀ (α : id Type), Type := λ α, aux α (tag.1 α)`, whose
   type check is official's `is_def_eq` (`id Type` against `Type`).
   con-leche: 0 (both modes).  The bad twin ind_mutual_param_bad
   (scripts/mk_mutual_bad.py) rejects there, as official does. -/
mutual
  inductive MA2 (α : Type) : Type
    | mk (b : MB2 α) (h : id True)
  inductive MB2 (α : id Type) : Type
    | mk (a : MA2 α)
    | nil
end

theorem MB2.self (b : MB2 Nat) : b = b := rfl
