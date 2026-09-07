/- Regression test: projections on an all-Prop structure.  For these,
   the model family *does* carry `_model.proj_i` artifacts, so the
   installed-projection path types the auto-generated projections
   (whose bodies are raw `Expr.proj` nodes).

   The shape that needs the recursor-inlining fallback is exhibited
   by `tests/e2e/prop_proj_raw.ndjson` instead (see the note in
   `tests/e2e-expected.txt`); there the projections only exist at
   certain level instantiations, so per-declaration artifacts cannot
   cover them and the fallback is the permanent mechanism. -/

--#export getSecond getBoth

structure PropPair (p q : Prop) : Prop where
  intro ::
  first : p
  second : q

theorem getSecond (p q : Prop) (h : PropPair p q) : q := h.second

theorem getBoth (p q : Prop) (h : PropPair p q) : PropPair q p :=
  PropPair.intro h.second h.first
