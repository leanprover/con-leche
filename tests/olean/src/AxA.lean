module
prelude
-- Guards task #444: an axiom of a propositional statement Lean's cheap test (`isPropCheap`)
-- recognises (`True`), declared again by AxB.  It is `Lean.trustCompiler`, whose pinned
-- statement con-leche accepts at its home, so each home's check accepts it too.
public import Init.Prelude
public section
axiom Lean.trustCompiler : True
end
