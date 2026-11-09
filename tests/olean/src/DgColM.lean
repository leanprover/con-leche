module
-- Guards task #399: M imports H (never loads Q) and declares its own foo := 1.
-- Lean accepts; H's exported constants name `foo` which now means M's foo.
import DgColH
public def foo : Nat := 1
