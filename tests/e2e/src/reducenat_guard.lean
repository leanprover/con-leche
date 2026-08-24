/-!
Defeq-side Nat-literal-folding fvar guard (task #94).

The kernel must not attempt Nat-literal folding during definitional
equality when a side mentions free variables (official kernel
`type_checker.cpp` `lazy_delta_reduction`; lean4lean
`TypeChecker.lean:782`): an unguarded fold whnfs the *open* argument
`x + 2147483647`, delta-unfolds `Nat.add`, and iota-grinds the
`Nat.brecOn` tower down the 2^31 literal unarily — fuel exhaustion
(exit 3).  With the guard the pair falls through to lazy delta and
reduces cheaply.  Minimal spelling of the `Int32`
`instUpwardEnumerable_eq` detonation found in the full `Init` export.
-/

theorem reducenat_guard_open_fold (x : Nat) :
    x + 2147483647 + 1 = Nat.succ (x + 2147483647) := rfl

--#export reducenat_guard_open_fold
