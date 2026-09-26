/- Regression test: projections on an all-Prop structure.  The
   projection table (`checkStructProjTable`) types the auto-generated
   projections (whose bodies are raw `Expr.proj` nodes).

   A `Prop` structure with data fields is exhibited by
   `tests/e2e/prop_proj_raw.ndjson` instead; there the projections
   only exist at certain level instantiations (the per-use guard
   level, `structProjGuards`). -/

--#export getSecond getBoth

structure PropPair (p q : Prop) : Prop where
  intro ::
  first : p
  second : q

theorem getSecond (p q : Prop) (h : PropPair p q) : q := h.second

theorem getBoth (p q : Prop) (h : PropPair p q) : PropPair q p :=
  PropPair.intro h.second h.first
