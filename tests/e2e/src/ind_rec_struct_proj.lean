--#export Chain.h_mk

/- End-to-end fixture (task #208; inductive audit #206, A6 / crack C6):
   the projection FUNCTIONS of a finitary RECURSIVE `structure`.  Official
   types `.proj` on any structure-like family — one constructor, zero
   indices; recursion is irrelevant (`infer_proj`,
   type_checker.cpp:239-283) — so `Chain.h := fun self => self.1`
   type-checks.

   con-leche types it from the block's projection table.  No finitary
   one-constructor recursive block occurs in init-full or Mathlib, so
   nothing else in the suites covers it.

   official: 0.  con-leche: 0.
   Probe of record: _tmp/indaudit/probes/P/RecStructOnly.lean. -/
structure Chain where
  h : Nat
  t : Chain

theorem Chain.h_mk (t : Chain) : (Chain.mk 3 t).h = 3 := rfl
