--#export w2
/-! Task #203 witness (DESIGN.md "HASHING AND COMPARISON UP TO BINDER
NAMES AND BINDER INFO"): the official kernel's `is_equal` and `hash`
ignore binder names and binder infos, so `quick_is_def_eq` answers a
pair that differs only in a nested binder name in the structural walk.
Lech's `==` compares the display data structurally; until task #203
the parser kept the stream's binder names, so such a pair missed the
fast path and — when the difference sits inside a `.proj`-headed
struct's argument — paid the projection clause's full `whnf` of the
struct (the task #201 residual, (d)).  Here the struct is
`h (fun y => y) x` with `x` a variable: `Nat.mul x 4294967296` has no
literal fold, so `Nat.mul` is iota-ground unarily down the literal —
fuel exhaustion (exit 3) on a binary that compares names.

lean4export interns α-equivalent terms as one node, so the source
below exports with ONE `fun y => y`; the committed fixture
`tests/e2e/binder_name_proj.ndjson` is this export with the
right-hand side's λ CLONED under the binder name `z` and the binder
info `implicit` by `scripts/mk_binder_twin_fixture.py` — a pair that
differs only in display data, which the official kernel accepts. -/
def h (f : Nat → Nat) (x : Nat) : Nat × Nat :=
  if f x * 4294967296 ≤ 5 then (x, 0) else (0, x)

theorem w2 : ∀ (x : Nat), (h (fun y => y) x).2 = (h (fun y => y) x).2 :=
  fun _ => rfl
