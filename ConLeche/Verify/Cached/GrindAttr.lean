module

public meta import Lean.Meta.Tactic.Grind.Attr
public import Std.Tactic.Do.Syntax
import Lean.Meta.Tactic.Grind.RegisterCommand

public section

/-!
# The cached-simulation `grind` lemma set

`register_grind_attr` declares the attribute with a `meta initialize`,
so it is usable only in modules that import this one; the lemmas are in
`ConLeche/Verify/Cached/Grind.lean` and next to the walks.
-/

/-- The cached-to-pure simulation's `grind` vocabulary.  A walk proof
uses it as `sym only [conleche_grind] => vcgen [...] <;> finish`. -/
register_grind_attr conleche_grind
