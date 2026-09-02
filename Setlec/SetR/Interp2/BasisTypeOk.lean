import Setlec.SetR.Interp2.BasisOk
import Setlec.SetR.Interp2.BitAgree

/-!
# Towards `AnnotOkP` at every built-in type (task #161, ENDGAME E)

`AnnotOkV_bconst_type` (`Install/BasisS.lean:114`) is v1's "every
pinned type is truthful, and that is **one lemma for the whole
basis**".  The ENDGAME D resume-here's item 2 named its P mirror as the
single grading obligation the twenty-two type readings need, and called
the tier "mechanical".  It is *more* mechanical than v1's and it is not
free; this file lands the one non-structural move it needs and records
exactly what is left.

## Why the P mirror is two lemmas and not one

* `AnnotOk2`'s `.app` clause carries a **numeral** and a fibre
  obligation (`∃ v A B, f ∈ˢ piR v A B ∧ a ∈ˢ A ∧ (v = 0 → …)`) where
  `AnnotOkV`'s carries only `∃ A B`.  The numeral is not free: it is
  whichever one `bval2_mem_type` supplies, because that membership is
  the only source of the `piR` fact;
* there is a **second predicate**.  `AnnotValidV` is bit validity, and
  its one numeral-reading clause is `pi`'s `v = 0 → the codomain reads
  into `univZero``.  `BConst.type2`'s convention (every codomain slot
  carries the tower's *result* sort) is what makes those discharge: a
  `pi` slot is zero exactly when the tower's result is a proposition,
  and then every suffix of the tower is one too.

## STOP-AND-NAME: the residue of `AnnotValidV_bconst_type`

A `cases c` + structural `simp` + three closers (impredicativity
`piR_zero_mem_univZero`, the truth set `eqv_mem_univZero`, and the
`max u 1 = 0` premises' unsatisfiability — no universe is a
proposition once a relation type is in the tower) takes the eighteen
cases down to **fifteen residual goals**, in three shapes:

1. **`natRec` ×2, `punitRec`, `emptyRec`, `quotLift` ×2, `quotInd` ×2,
   `quotMk`, `psigmaMk`** — `interp2 ρ (.app M a) ∈ˢ univZero` where
   `M` is the bound motive and `v = 0` is in scope.
   `motive_app_univZero` below is exactly this move; what blocks the
   uniform closer is the **argument** membership, which differs per
   goal: at `natRec`'s successor row the argument is
   `natSucc n` and needs `natSuccV2_mem`, at `quotInd`'s it is a
   `quotMk` spine and needs `quotMkV2_app`, and so on.  Each is one
   line, and none is a new fact — they are `Interp2/Value.lean`'s
   existing application laws;
2. **`propext` ×2** — the same shape at `Prop`-valued implications;
3. **`choice` ×3** — the same at `dnegSpace2`'s two nested negations.

None of the fifteen is a wall, and none needs a bit lemma: every one is
the clause's own `v = 0` premise plus an application law that already
exists.  Recorded here rather than assumed, per the standing
discipline, and left for the successor with its shape named — the
generic closers are in place, so what remains is fifteen argument
memberships.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT SetTheory
open Setlec.SetR (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-- **A motive at a zero level lands in `univZero`.**  The one
non-structural move the bit-validity computation needs: every basis
recursor's type binds a motive in `piR (v + 1) A (fun _ => univ v)`,
and the `pi` clause's premise is exactly `v = 0`.  The `+ 1` is what
keeps the motive space in the graph regime whatever `v` is — a motive
is a *function into a universe*, never a proposition, which is the
`v'`-for-a-`Sort` trap of `Interp2/BasisType.lean`'s docstring showing
up on the validity side. -/
theorem motive_app_univZero {u : Nat} {A M a : V} (hu : u = 0)
    (hM : M ∈ˢ piR (u + 1) A (fun _ => (univ u : V))) (ha : a ∈ˢ A) :
    SetTheory.app M a ∈ˢ (univZero : V) := by
  have h := app_mem_piR_pos (Nat.succ_ne_zero u) hM ha
  rw [hu, univ_zero] at h
  exact h

end Setlec.SetR.Interp2
