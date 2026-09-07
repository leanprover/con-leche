--#export Chain.h_mk

/- End-to-end fixture (task #208; inductive audit #206, A6 / crack C6):
   the projection FUNCTIONS of a finitary RECURSIVE `structure`.  Official
   types `.proj` on any structure-like family — one constructor, zero
   indices; recursion is irrelevant (`infer_proj`,
   type_checker.cpp:239-283) — so `Chain.h := fun self => self.1`
   type-checks.

   In con-leche the block goes native on the fixpoint route (`Chain fix`), so
   no `Chain._model.proj_i.iota` artifact exists; the frontend's
   projection rewrite (Frontend/ProjRec.lean:240-260) cannot read the
   field's sort, does not rewrite, and the raw `.proj` node declines
   ("projection on a non-structure-like type", Core.lean:2596-2622) —
   piped and raw alike.  A silent REGRESSION of task #188: before it the
   tool modelled the block and emitted the artifacts (cf.
   nested_struct_proj's reflexive `Stream'`, which still accepts).  No
   finitary one-constructor recursive block occurs in init-full or
   Mathlib, so nothing else in the suites covers it.

   official: 0.  con-leche at master 700a06ca: 2 piped, 2 raw (both modes).
   Probe of record: _tmp/indaudit/probes/P/RecStructOnly.lean. -/
structure Chain where
  h : Nat
  t : Chain

theorem Chain.h_mk (t : Chain) : (Chain.mk 3 t).h = 3 := rfl
