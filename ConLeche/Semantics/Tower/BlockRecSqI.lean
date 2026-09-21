module

public import ConLeche.Semantics.Tower.FixSquashI
public import ConLeche.SetModel.UnionRec
@[expose] public section

/-!
# Regime SQ: the class kit is the squash kit, the step is the RESIDUE (task #315, M5 model half)

DESIGN "DESIGN DOCUMENT 2, v2" §3.4.  At `¬allProp ∧ w = 0` the guard
leaves a lone, non-nested block with at most one constructor under the
subsingleton criterion.  Every value of the carrier is then the point
(`mkZero`), so the major carries no information and the recursion runs
on the INDEX: the constructor's fields are a FUNCTION of its index
values (`srcVals`, the subsingleton criterion), and the predecessors
of an index tuple are the recursive calls' index tuples (`sqPred`),
accessible by the block's own lfp induction.

**What this file changes, and what it keeps.**  `BlockRecKitI`'s arm
already covers SQ: `famCand`/`famCand_hCand` are stated over a
`UnionRecKitC`, and the squash kit is one — only its `pred` and its
`acc` differ from regime WF's.  So `FixSquashI`'s kit is KEPT:
`isOfW`/`tupW` (the index tuple and its retraction), `srcOfEs`,
`srcList`, `srcVals` and `srcVals_of_fit` (the subsingleton
criterion), `sqSpine`, `sqPred`, and the accessibility argument
`sqGraph_singleton` rests on.

What the new arm SUBSUMES, and what may go with the generate-and-
compare route:

* `sqB` (the motive's fibre `M ı⃗ pt`) — the conclusion is arbitrary
  now, so the motive is read off the recursor's TYPE
  (`RecFamData.hconcl`), not spelled;
* `sqSt` (the lone minor applied at the source spine and the ih
  values) — replaced by `sqStep` below: the RESIDUE read at the source
  spine.  The minor is not a separate datum any more; it is a prefix
  variable of the residue's own frame, which is why the check never
  looks inside the `nP…rP-1` stretch;
* `sqIhs` — subsumed by the ih terms' readings (`ihFunAV`,
  `BlockRecI`), which are the same λ-towers;
* `sqFixBodyAV` and `fixRecBodyAVI`'s squash arm — the GENERATED body,
  which the residue replaces wholesale;
* `sqGraph` as a *spelled* object — the graph is now the kit's
  (`kitGraphAt`).

The SQ-specific content at THIS tier is one theorem: at a rule's own
spine the step defined at the SOURCE spine is the step at the rule's
FIELDS (`sqStep_at_rule`, `sqStep_at_rule_of`), because the fields are
sourced.  Everything else is `famCand_hCand`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The tagged index's index part

`WfRec.lean` reads a tagged index's VALUE (`tagVal`, the payload the
∈-order is taken on).  Regime SQ reads its INDEX instead: at `w = 0`
the payload is the point and the index is what the recursion runs
on. -/

/-- The INDEX of a tagged recursion index `tagged c i x = ⟨c, i, x⟩`. -/
noncomputable def tagIdx (u : V) : V := sfst (ssnd u)

@[simp] theorem tagIdx_tagged (c : Nat) (i x : V) : tagIdx (tagged c i x) = i := by
  unfold tagIdx tagged
  rw [ssnd_kpair, sfst_kpair]

/-! ## The step: the residue at the source spine -/

/-- **The SQ regime's step**, motive-free: the RESIDUE read at the
SOURCE spine — the constructor's fields recovered from the tagged
index's index values — and at the ih values.

This is the whole re-targeting: `sqSt`'s `m` (the lone minor) and
`sqSpine`'s use of it disappear into `Rb`'s frame, and `sqIhs` becomes
the caller's `ihv`. -/
noncomputable def sqStep (u nIdx : Nat) (ρ : Nat → V) (xs : List V)
    (src : List (Option Nat)) (ihv : List V → V → List V) (Rb : AnnotTerm) (uu g : V) : V :=
  interp V
    (consList (ihv (srcVals (isOfW u nIdx (tagIdx uu)) src) g)
      (consList (xs ++ srcVals (isOfW u nIdx (tagIdx uu)) src) ρ)) Rb

/-- **The step at a rule's own index**: when the rule's field spine IS
the source spine of its index values, the step defined at the source
spine is the residue at the rule's FIELDS.  This is what makes the ι
law's right-hand side the stored right-hand side's and not a
generated term's. -/
theorem sqStep_at_rule {u nIdx : Nat} {ρ : Nat → V} {xs : List V} {src : List (Option Nat)}
    {ihv : List V → V → List V} {Rb : AnnotTerm} {c : Nat} {i x g : V} {is fs : List V}
    (hidx : isOfW u nIdx i = is) (hsrc : fs = srcVals is src) :
    sqStep u nIdx ρ xs src ihv Rb (tagged c i x) g
      = interp V (consList (ihv fs g) (consList (xs ++ fs) ρ)) Rb := by
  rw [sqStep, tagIdx_tagged, hidx, ← hsrc]

/-- **The fields ARE sourced** — the subsingleton criterion in the
vocabulary the step is stated in: at the index tuple of a fitting
index spine, the source spine of a rule's fields is the fields.
`hprop` is the criterion itself (`checkStructFieldSortsI`'s `large`
arm: every field that is not an index source is a proposition),
`hI` the index telescope's grading. -/
theorem sq_fields_sourced {u : Nat} {ρp : Nat → V} {Ids Fs Es : List AnnotTerm}
    (hI : IdxOk u ρp Ids)
    (hprop : ∀ j, j < Fs.length → srcOfEs Es Fs.length j = none →
      ∀ fs : List V, SpineFit ρp (Fs.take j) fs →
        interp V (consList fs ρp) (Fs.getD j default) ∈ˢ (univZero : V))
    {fs is : List V} (hfit : SpineFit ρp Fs fs) (hidxsp : SpineFit ρp Ids is)
    (hidx : idxValsAt ρp Es fs = is) :
    isOfW u Ids.length (tupW u is) = is ∧ fs = srcVals is (srcList Es Fs.length) :=
  ⟨isOfW_tupW hI hidxsp, srcVals_of_fit hprop hfit hidx⟩

/-- **The SQ ι step, assembled**: at a rule whose fields fit and whose
index values are `is`, the step at the rule's own tagged index is the
residue at the rule's fields. -/
theorem sqStep_at_rule_of {u : Nat} {ρ : Nat → V} {xs : List V} {ρp : Nat → V}
    {Ids Fs Es : List AnnotTerm} {ihv : List V → V → List V} {Rb : AnnotTerm} {c : Nat} {x g : V}
    {fs is : List V}
    (hI : IdxOk u ρp Ids)
    (hprop : ∀ j, j < Fs.length → srcOfEs Es Fs.length j = none →
      ∀ fs' : List V, SpineFit ρp (Fs.take j) fs' →
        interp V (consList fs' ρp) (Fs.getD j default) ∈ˢ (univZero : V))
    (hfit : SpineFit ρp Fs fs) (hidxsp : SpineFit ρp Ids is)
    (hidx : idxValsAt ρp Es fs = is) :
    sqStep u Ids.length ρ xs (srcList Es Fs.length) ihv Rb (tagged c (tupW u is) x) g
      = interp V (consList (ihv fs g) (consList (xs ++ fs) ρ)) Rb :=
  let h := sq_fields_sourced hI hprop hfit hidxsp hidx
  sqStep_at_rule h.1 h.2

end ConLeche.Semantics
