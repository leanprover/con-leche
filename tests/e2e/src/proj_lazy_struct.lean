--#export proj_lazy_struct
/-! Same-slot projections whose scrutinees differ only in a field the
projection does not select.  Official's `is_def_eq_core` reaches the
proj/proj check with `(P (slow 100000)).1 =?= (Q (slow 100001)).1` stuck
under the cheap `whnf_core`; `lazy_delta_proj_reduction` unfolds `P` and
`Q` lazily, the step leaves two constructor applications it cannot
unfold further, and `reduce_proj_core` projects both, so only `0 =?= 0`
is compared (4 kernel unfoldings: `Prod.fst` ×2, `P`, `Q`).  Comparing
the whole scrutinees instead reaches `slow 100000 =?= slow 100001`, a
Θ(100000) unfolding chain beyond the lazy-delta loop's fuel. -/
def loop : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop n (acc + 1)

def slow (n : Nat) : Nat := loop n 0

def P (a : Nat) : Nat × Nat := (0, a)

def Q (a : Nat) : Nat × Nat := (0, a)

theorem proj_lazy_struct : (P (slow 100000)).1 = (Q (slow 100001)).1 := rfl
