/-
A `bv_decide`-named native axiom used directly (task #368).  The axiom
is installed as a `True` stub (it is level-free and named
`<decl>._native.bv_decide.ax_…`); its use outside a natively checked
certificate declines.  Today's verdict: decline (2); target: decline.
-/
--#export useAx

axiom demo._native.bv_decide.ax_1_1 : True

theorem useAx : True := demo._native.bv_decide.ax_1_1
