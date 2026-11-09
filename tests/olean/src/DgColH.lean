module
-- Guards task #399: H privately imports DgColQ; bar.eq_1 (exported, private
-- name) states bar = foo with Q's foo, which M's importers do not load.
import DgColQ
public def bar : Nat := foo
public theorem bar_eq : bar = 0 := by
  rw [bar]; rfl
