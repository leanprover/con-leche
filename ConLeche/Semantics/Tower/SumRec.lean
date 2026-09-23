module

public import ConLeche.Semantics.Tower.SumRecCase

@[expose] public section

/-!
# The sum recursor leaf (task #175 sum-types, stage S4b; indexed)

`sumRecAV ℓ w rds Fss Ess srcs nIdx = mkLamsC ℓ rds (sumRecBodyAV …)` —
the constant-bit λ-tower (bit `ℓ`) over the recursor type reading's
binder data (parameters, motive, one minor per constructor, the
`nIdx` index binders, major), whose body sits one binder below the
K-frame `(p⃗, motive, minors, ı⃗)` and is, in the **graph regime**, the
case recursor (`caseRecAV`, stage `0`, depth `1`) on the major's tag
applied to the major's payload:

    sumRecBodyAV = (caseRec 0 (t.0)) (t.1)        t = bvar 0

and at a **squash instantiation** (`w = 0`, task #175 indexed) the
first minor applied to the fields' SOURCES — an index variable for a
field that is one of the constructor's index expressions, the point
for a proof field (`srcAV`): the squashed value carries no field, so
the recursor reads the data fields off the index arguments, which is
official's subsingleton elimination (`Eq`'s large eliminator).  A
squash body with no constructor is the point.

`sumRecBody_facts` gives the body's grading and its membership in
`M ı⃗ t` at every carrier member (the graph regime through the case
recursor's stage-`0` motive; the squash regime through the minors'
inhabitation at a zero elimination level, and through the sources'
fit when the elimination level is nonzero — then there is exactly one
constructor and the sources ARE the witness's fields, `SqHypS.hsrc`),
and `sumRecBody_iota` the iota: at `t = inj j (mkTower (f⃗ ++ [pt]))`
the body is minor `j` folded along `f⃗`.  The leaf's ONE hereditary
premise is `RecPreS` — the parameter walk ending in `RecBaseS`: the
motive entry graded, and under every motive, minor and index the
major entry reads to the carrier and the K-frame satisfies `RecHypS`
and `SqHypS` — and `underTowerOk_of_recPreS` turns it into the
tower's premise.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The sources -/

/-- The sources' values at an index tuple. -/
noncomputable def srcVals (is : List V) (src : List (Option Nat)) : List V :=
  src.map fun s => match s with
    | some l => is.getD l pt
    | none => pt

/-! ## The body -/

theorem foldl_app_pt_sum : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt_sum ts

end ConLeche.Semantics
