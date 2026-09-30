prelude
--#export And.swap

/- Corner case (lane ANDPIN, 2026-09-30): `And` is pinned — a record
   declaring `And`, `And.intro` or `And.rec` must be the toolchain's
   block (`andPinOk`).  This stream (a `prelude` module, nothing else in
   scope) declares `And` exactly as `Init.Prelude` does, projections
   included, and uses them: its block agrees with the pin and installs
   through the ordinary installer.  Official 0.  Today 0. -/

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

theorem And.swap {a b : Prop} (h : And a b) : And b a :=
  And.intro h.right h.left
