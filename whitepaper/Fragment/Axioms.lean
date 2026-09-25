module

public import Fragment.Sound

public section

/-!
# The axiom pin

The fragment's theorems use exactly Lean's three standard axioms and
nothing else — in particular no `sorryAx` and no axiom of the
fragment's own: the library `SetLib` and the level oracle
`LevelOracle` are *class parameters* of every theorem, not axioms.
`whitepaper/fragment-gate.sh` builds this file; a change in the list
is a build error here.
-/

/--
info: 'Fragment.soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.soundness

/--
info: 'Fragment.closed_infer' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.closed_infer

/--
info: 'Fragment.PropWhen.eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.PropWhen.eq_iff

/--
info: 'Fragment.Level.holds_zeroness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Fragment.Level.holds_zeroness
