--#export w2
/-! Task #203 witness (DESIGN.md "HASHING AND COMPARISON UP TO BINDER
NAMES AND BINDER INFO"): the official kernel's `is_equal` and `hash`
ignore binder names and binder infos, so `quick_is_def_eq` decides a
pair that differs only in a nested binder name in its structural walk.
Until task #203 con-leche's `==` read the display data, so such a pair
missed the fast path and — when the difference sits inside a
`.proj`-headed struct's argument — paid the projection clause's full
`whnf` of the struct (the divergence audit's D5; the task #201 residual
(d)).  Here the struct is `h (fun y => y) x`: a 40 000-step `Nat.rec`
tower that `whnf` grinds down unarily (~43 k instructions per step)
before the projection can reduce.

Two things are done to the raw export to make the pair reach the
checker at all (`scripts/mk_binder_twin_fixture.py --proj`):

* lean4export interns α-equivalent terms as one node, so the source
  below exports with ONE `fun y => y`; the script CLONES the
  right-hand side's λ under the binder name `tw_1` and the binder info
  `implicit` — a pair that differs only in display data;
* the elaborator exports `p.2` as the projection FUNCTION `Prod.snd`,
  and two `Prod.snd` applications meet the lazy-delta same-head spine
  congruence without ever whnf'ing the struct; the script rewrites the
  shared `Prod.snd Nat Nat s` node to the kernel projection
  `.proj Prod 1 s`, the shape the residual has in real streams (where
  the projection function has been unfolded).

The fixture is a `raw` line in `tests/e2e-expected.txt`: the
preprocessor's re-export goes through `Lean.Expr`, whose hash-consing
is α-equivalence, so a piped run collapses the twin back into one node
before con-leche sees it (DESIGN, task #203 §4).  Before #203 (master
`a77ac1d6`, raw, `--verified`): accept at 3.38 G instructions against
0.37 G for the same export without the twin; after: 0.37 G both. -/
noncomputable def h (f : Nat → Nat) (x : Nat) : Nat × Nat :=
  Nat.rec (motive := fun _ => Nat × Nat) (x, f 0) (fun _ ih => ih) 40000

theorem w2 : ∀ (x : Nat), (h (fun y => y) x).2 = (h (fun y => y) x).2 :=
  fun _ => rfl
