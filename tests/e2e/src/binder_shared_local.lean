--#export w1
/-! Task #201 witness (DESIGN.md "THE BINDER ARMS OPEN ONE LOCAL"): the
official kernel's `is_def_eq_binding` instantiates BOTH bodies with ONE
fresh local (`type_checker.cpp:738`); lech's binder arms used to open
each body with its own `.fvar depth nᵢ tyᵢ`, so two bodies that are the
same term up to the bound variable's display name/domain spelling were
not `==`, and the comparison fell into `whnfCore` — whose projection
clause fully whnf's the struct.  Here that struct is `g x` with `x` a
variable: `Nat.mul x 4294967296` has no literal fold (the first
argument is stuck), so `Nat.mul`'s structural recursion is iota-ground
unarily down the literal — fuel exhaustion (exit 3) before the fix.

`aux`'s domain is the abbrev `N` so that lean4export does not intern
the two Π-types (which are equal up to the binder name) as one node.
The pre-fix binary already dies at `aux` itself: `fun _ => rfl`'s
inferred type carries the elaborator's hygienic binder name against the
declared `y`, the same shape one declaration earlier. -/
abbrev N := Nat

def g (x : Nat) : Nat × Nat :=
  if x * 4294967296 ≤ 5 then (x, 0) else (0, x)

theorem aux : ∀ (y : N), (g y).2 = (g y).2 := fun _ => rfl

theorem w1 : ∀ (x : Nat), (g x).2 = (g x).2 := aux
