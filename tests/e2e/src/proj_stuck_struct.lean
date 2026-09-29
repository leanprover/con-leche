--#export step24
/- SELFCHECK / KEEPPROJ (2026-09-29): a projection whose structure argument
is stuck keeps that argument as it was (official `whnf_core`: `reduce_proj`
fails and the input is returned).  `(step (id c) 24 x).1 = (step c 24 x).1`
is then `step (id c) 24 x =?= step c 24 x`, arguments first, done.  A
`whnfCore` that returned the projection of the struct's WHNF (a stuck
`match x`) lost the `step` head and unrolled the recursion on both sides:
exponential in the fuel (~1.7× per unit; N = 20 took 17 s and 2.6 GB, this
N = 24 does not finish in the e2e timeout).  Distilled from
`ConLeche.nestRoot_datF._f`, on which the self-check ran out of memory. -/
def step (c : Nat) : Nat → Nat → Nat × Nat
  | 0, x => (x + c, c)
  | n+1, x => match x with
    | 0 => ((step c n 1).1 + (step c n 2).1, 0)
    | k+1 => ((step c n k).1 + (step c n (k+2)).1, k)

theorem step24 (c x : Nat) : (step (id c) 24 x).1 = (step c 24 x).1 := rfl
