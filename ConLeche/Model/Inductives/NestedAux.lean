module

public import ConLeche.Model.Inductives.MutualCore
public import ConLeche.Model.Inductives.BlockComposed
public import ConLeche.Kernel.Inductives.NestedElim
import ConLeche.Verify.Inductives.NestedCopySort
public section

/-!
# The nested block's premise from the auxiliary block's formers' stage (task #315, M6 s5)

The composed block model `BlockModel.ofNested` (`BlockComposed.lean`)
is stated at ONE frame under `NestedLfpOk ψ ρp` — the sealed former's
premise `TupleLfpOk` at the `k + n` components (the tag, the chains'
grading, the CASED WITNESS) — and its fibre law under `TupleLfpShape`.
Both are exactly what the mutual assembly's formers' stage
(`mutualFormersStage`, `MutualCore.lean`) establishes for a mutual
block: the nested route checks its auxiliary block with the SAME
installer (`checkMutualCore … b none true`, the scratch run), so the
nested assembly runs the mutual formers' stage on `b` and reads the
premise off `MutualFormersFacts` — with `b.k = k + n` (the members
followed by one copy per pin) and the lists the mutual stage names.
This is the cased witness "at the nested block" (DESIGN §U.16 (g)):
no new witness, `MutualFormersFacts.tupleOk` at the auxiliary block.

The SAME-UNIVERSE fact `hw` (`NestedFit.lean`: the container's sort at
the pin's level assignment equals the block's) is assembled from three
pieces; the middle one is here (`copySort_eval`): a copy minted by
`mkCopy` ends in the container's sort with the levels substituted
(`mkCopy_stripPis_sort`, `Verify/Inductives/NestedCopySort.lean`), so
its sort's value at the block's assignment `ψ` is the container's sort
at `substFn ψ J.lps lvls` — the pin's assignment.  The outer pieces are
the auxiliary block's `mutualCrossChecks` (`MutualFormersFacts.sEq`)
and the container block model's `strip`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind IndCaps RecRule
  MutualBlock)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

section Aux

variable {F : Nat} {g : Bool} {mp : EnvModelM V μ env} {b : MutualBlock} {fms : List MutualFormerA}
  {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
  {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF
    xFvsF xrestF eissF tssF)
include h

/-- **The nested block's frame premise is the auxiliary block's**
(`MutualFormersFacts.tupleOk` at `b.k = k + n`): the tag, the chains'
grading and the cased witness at the `k + n` components — plus, at
the per-component index universes, the squash bound of a pin whose
container's index universe is `0` (`hpin`, the container's `idxOk`
transported along the instantiation identity; `nestedPinBound_of`,
`NestedCore.lean`). -/
theorem nestedLfpOk_of_formers (hμ : μ.verifiedChecks = true) {k : Nat} {pins : List PinSyn}
    (hbk : b.k = k + pins.length) (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp)
    (hpin : ∀ q, q < pins.length → (pins.getD q default).u ψ = 0 →
      FieldsBound 0 ρp (blockIds b.nP ppsF ψ (k + q))) :
    NestedLfpOk (V := V) (nP := b.nP) (k := k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
      (pins := pins) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
      (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
      (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
      (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
      (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) ψ ρp := by
  unfold NestedLfpOk
  have hOk := h.tupleOk hμ ψ ρp hρp
  rw [hbk] at hOk
  refine hOk.of_bound fun m hm hz => ?_
  by_cases hmk : m < k
  · rw [nestedU_mem hmk] at hz
    exact absurd hz hOk.W_pos
  · obtain ⟨q, rfl⟩ : ∃ q, m = k + q := ⟨m - k, by omega⟩
    rw [nestedU_pin] at hz
    exact hpin q (by omega) hz

/-- **The nested block's lists' shape is the auxiliary block's**
(`MutualFormersFacts.shape` at `b.k = k + n`). -/
theorem nestedShape_of_formers {k : Nat} {pins : List PinSyn} (hbk : b.k = k + pins.length)
    (ψ : Name → Nat) :
    TupleLfpShape (k + pins.length) (blockIds b.nP ppsF ψ) (mutMems ctorsA.length (mutMemF b))
      (mutNFs ctorsA.length (mutNFOf ctorsA))
      (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
      (mutEiss0 ctorsA.length eissF ψ) (blkFss0 b ctorsA kinds dsF ψ)
      (mutEss0 ctorsA.length esF ψ) := by
  rw [← hbk]
  exact h.shape ψ

end Aux

/-! ## The copy's sort at the block's assignment -/

/-- **A copy's sort evaluates as the container's at the pin's level
assignment**: `mkCopy`'s output ends in `Level.subst J.lps lvls sJ`
(`mkCopy_stripPis_sort`), and `Level.eval_subst` moves the substitution
into the assignment. -/
theorem copySort_eval {pbs : List (Expr × ConLeche.BinderMeta)} {lvls : List Level} {Ds : List Expr}
    {auxName : Name} {J : ConLeche.ContainerMember} {t : ConLeche.AuxType}
    (h : ConLeche.mkCopy pbs lvls Ds auxName J = .ok t)
    {nIdx : Nat} {bsJ : List (Expr × ConLeche.BinderMeta)} {sJ : Level}
    (hJ : J.type.stripPis (Ds.length + nIdx) = some (bsJ, .sort sJ))
    {bs : List (Expr × ConLeche.BinderMeta)} {s : Level}
    (hs : t.type.stripPis (pbs.length + nIdx) = some (bs, .sort s)) (ψ : Name → Nat) :
    s.eval ψ = sJ.eval (Level.substFn ψ J.lps lvls) := by
  obtain ⟨bs', h'⟩ := ConLeche.mkCopy_stripPis_sort h hJ
  rw [hs] at h'
  obtain ⟨-, hsort⟩ := Prod.mk.inj (Option.some.inj h')
  obtain rfl := Expr.sort.inj hsort
  exact Level.eval_subst ψ J.lps lvls sJ

end ConLeche.Model
