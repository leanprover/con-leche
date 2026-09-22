module

public import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Annot.BitInst

public section

/-!
# The per-pair rule obligation's FIT and FIRED SPINE (task #315, M5 model half)

`BlockRuleDataB` (`BlockRecData.lean`) is the seam's rule-side
obligation at ONE environment and ONE valuation: five statements about
one (recursor, constructor) pair, all at the BASE frame `ρ`.  This
file discharges two of them — the first conjunct (the prefix and the
fields FIT the rule's domains) and the third (the FIRED SPINE reads to
the constructor at its own parameters) — and the two are one piece of
work, because both need the same fact:

> the constructor's field values fit the constructor's field domains
> **at the RECURSOR's parameter frame**, not only at the
> constructor's own.

The iota rule is `paramsBlind`: the kernel fires it on a syntactic
constructor head and takes the parameters from the RECURSOR's spine
and the fields from the CONSTRUCTOR's, comparing the two parameter
spines nowhere (`Model/Annot/Laws.lean`, and `recFireComparands` at a
`.plain` rule copies the level arguments and drops the comparison).
So nothing syntactic ties the two spines, and the model must pay for
the tie.  It pays with the MAJOR PREMISE: `BlockRuleDataB` hands a
`TeleFitPA` of the recursor's own type, whose last entry is the major,
so the major LIES IN the member's former applied to the RECURSOR's
parameters and indices — which is the carrier
(`BlockModelAt.leaf`), and an element of the carrier IS an injection
of a spine fitting one of the component's constructors THERE
(`blockCarrier_case`).  At a `Type`-valued block that decomposition is
unique (`blockCarrier_case_unique`), so the spine it produces is the
constructor's own field spine — read at the recursor's parameters.

The parts:

* **§1 the frame transport.**  Every §24 bridge (`blockRecSpF_of`,
  `blockRecCtorFitsFrom_of`) concludes at the CHAIN frame over `K`
  binders, and `K` is a FREE variable of those theorems: the chain is
  there because the KIT runs under it, not because the bridge needs
  it.  At `K = 0` the chain frame IS the base frame and `liftDomsK 0`
  is the identity, both unconditionally, so the bridges' base-frame
  instances cost two `simp` lemmas and no boundedness premise (§28's
  `liftDomsK_eq_self_of_bounded` pays for the same collapse at the `K`
  the kit actually runs at, and is the route for the kit's own guard;
  it is not the route here);
* **§2 the major premise's decomposition** — `hps`, the index tuple's
  membership and the field spine's `ChainFit`, all at the recursor's
  parameter frame, out of `BlockRecSplitAt` and the constructor's
  reading;
* **§3 the two conjuncts.**
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The frame transport: a ZERO chain is no chain -/

/-- **A zero lift is no lift**, at a binder list: `liftDomsK 0` is the
identity at every cutoff, with no boundedness side condition. -/
@[simp] theorem liftDomsK_zero :
    ∀ (k : Nat) (Ds : List AnnotTerm), liftDomsK 0 k Ds = Ds
  | _, [] => rfl
  | k, D :: Ds => by
    show AnnotTerm.liftN 0 D k :: liftDomsK 0 (k + 1) Ds = D :: Ds
    rw [AnnotTerm.liftN_zero, liftDomsK_zero (k + 1) Ds]

omit [SetTheory V] in
/-- **A zero chain is no chain**: `chainFrame 0` is the base frame. -/
@[simp] theorem chainFrame_zero (a ρ : Nat → V) : chainFrame 0 a ρ = ρ := rfl

/-- **§24's `hspF`, AT THE BASE FRAME** — `blockRecSpF_of` at `K = 0`.

`blockRecSpF_of` has `K` and the chain tuple `a` free; its conclusion
is a chain-frame statement because the KIT consumes it under the `K`
Σ' binders, not because the bridge needs them.  `BlockRuleDataB`'s
first conjunct is the same statement at `ρ` and at the UNLIFTED rule
domains, which is the `K = 0` instance — no boundedness premise, no
`liftDomsK_eq_self_of_bounded`.

Every other premise is `blockRecSpF_of`'s own; §2 below produces the
three that mention the block (`hps`, `ht`, `hfit`). -/
theorem blockRecSpF_base {envC : Env} {mpC : EnvModelM V μ envC} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mpC.base2 names d) {lps : List Name}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j : Nat} {mem : Nat → Nat} {ψ : Name → Nat}
    {ρ : Nat → V} {xs fs : List V} {t : V} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem c) j cA)
    (hfd : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []))
    (hasLen : (xs.take d.nP).length = d.nP)
    (hps : SpineFit ρ (d.params ψ) (xs.take d.nP))
    (htgt : ∀ l, l < cA.2 → d.tgts (mem c) j l < d.k)
    (hcN : mem c < d.N) (hj : j < (d.ctorsM (mem c)).length)
    (ht : t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c))
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))))
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c)
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs)
    (hfit : d.ChainFit ψ (consList (xs.take d.nP) ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))) t (mem c) j fs) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i) (xs ++ fs) := by
  have hq := blockRecSpF_of (K := 0) (a := fun _ => (pt : V)) hM hμ h hr hcj hcf hfd hasLen
    hps htgt hcN hj ht hX hxs
    (by simpa only [chainFrame_zero, blockRecPdomsK, liftDomsK_zero] using hpref) hfit
  simpa only [chainFrame_zero, blockRecPdomsK, blockRecFdomsK, liftDomsK_zero] using hq

end ConLeche.Model
