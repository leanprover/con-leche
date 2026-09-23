module

public import ConLeche.Model.Inductives.FixLeafOk
public section

/-!
# The recursive former's cons (task #188)

`stageFixFormer`: the P step at the recursive family's type former,
for given block data — the X-chain sources `Fss`, the index-expression
readings `Eiss`, the residual index readings `Ess`, the recursive
positions `rss` — `stageSumFormer` with the fixed-point leaf
`nativeTyAVI`.  The leaf's hereditary premises (`ParamsOkXI`, the
tower's validity) are walked from the former's data down to the frame
below the parameters and the index variables, where the functor's
premise (`XChainsOk`) and the index telescope's grading, both at the
parameter frame, are the base (`fixLeafWalks`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

omit [SetTheory V] in
theorem frameIdx_eq_reverse_map (n : Nat) (σ : Nat → V) :
    frameIdx n σ = (List.range n).reverse.map σ := by
  apply List.ext_getElem
  · simp [frameIdx]
  · intro l h1 h2
    simp only [frameIdx, List.getElem_map, List.getElem_reverse, List.getElem_range]
    simp only [List.length_range]

end ConLeche.Model
