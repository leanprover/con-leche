module

import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Semantics.Tower.BlockRecI
public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Model.Claims
import ConLeche.Model.Capstone
import ConLeche.Model.CtxOkKit
import ConLeche.Model.IndFrame
import ConLeche.Model.Inductives.StructTele
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLeaves

public section

/-!
# G1 — `ResidueOk` from the rule stage's TYPING certificates (task #315, M5)

`checkBlockRule` (`Kernel/Inductives/BlockInstall.lean`) closes with
two runs at the CONSTRUCTORS' environment `envT`, at the depth
`d = rP + nF + nR` of the opened frame

```
p⃗ (the rP stretch)   f⃗ (the constructor's fields)   ih⃗ (the openers)
```

namely

```lean
let tyB ← opsT.inferType envT depth bodyO
unless ← opsT.isDefEq envT depth tyB concl do throw …
```

with `concl` the recursor's OWN conclusion instantiated at the rule's
prefix, the constructor's index expressions and the major `C_J p⃗ f⃗`.
`ResidueOk` (`Semantics/Tower/BlockRecI.lean`) is what the three
regimes consume of those two runs:

```lean
def ResidueOk (V) (Rb : AnnotTerm) (ihvals : List V) (ρ' : Nat → V) (B : V) : Prop :=
  WellDenoted V (consList ihvals ρ') Rb ∧ interp V (consList ihvals ρ') Rb ∈ˢ B
```

This file is the hop between the two, and it has exactly three parts.

* **The certified hop** (`residueOk_of_certs`): `InferClaim` at the
  residue plus `DefEqClaim` between the inferred type and the
  conclusion, both at the frame's context `Δa`, give membership at
  every `Δa`-satisfying valuation.  This is `sidesMem`
  (`Model/IndFire.lean`) with one side instead of two, packaged as
  `ResidueOk`; the k = 0 precedent is `checkConstantVal_reads`
  (`BlockRecRead.lean`), and **what is new is only that the context is
  not nil** — everything else is the same three lemmas.
* **The frame's valuation** (`sat_blockFrame`): the context is
  `ihdoms.reverse ++ (pdoms ++ fdoms).reverse` and `Sat` at it is two
  applications of `sat_of_spineFit` — the regimes' own
  `SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs)` for the prefix and
  the fields, and one `SpineFit` for the `ih` openers.  The second is
  where the regimes pay: the opener's value must lie in the opener's
  DOMAIN (WF: `graph_mem_B` at the kit's graph; IND: `pt` in the
  truth value).
* **The frame's context** (`ctxOk_blockFrame`): the frame is opened by
  THREE `openPisAtFvars` calls at the consecutive offsets `0`, `rP`
  and `rP + nF`, so the openers' concatenation is an
  `∃ ty, x = .fvar i ty` list and `ctxOk_of_openers`
  (`Model/IndFrame.lean`) applies unchanged.

**What is taken as a named premise, and why.**  The stage's own
inversion does NOT export the two runs: `checkBlockRule_facts`
(`Verify/Inductives/BlockWF.lean`, lane V2) stops at SCOPING —
fvar-freedom, level closure, resolution and `looseBVarsBounded` of the
returned right-hand side — and V2's report says so in as many words
("the stage facts stop at scoping … it says nothing about what the
stage CHECKED"). So the two runs, and the syntactic side conditions on
`bodyO`/`concl` that `InferClaim` asks for, are premises here,
collected in `BlockRuleCerts` below; extending
`checkBlockRule_facts` with them is the one item this lane leaves for
the Verify tier.

The `.full`/`.io` note of `BlockRecRegimes.lean` (G3) applies verbatim:
the run is `inferTypeCore` at the checker's certified grade, which is
where `InferClaim` lives.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The certified hop — `InferClaim` + `DefEqClaim` at a context -/

/-- **The residue's typing, converted at a context** — `sidesMem`
(`Model/IndFire.lean`) with ONE side.  The residue's reading inhabits
the conclusion's reading at every valuation satisfying the frame's
context, and is graded there.

`hctxT`, the inferred type's own context correspondence, is DERIVED
(`CtxOk.of_subset` along `inferTypeCore_fvarLeaves`): an inferred
type's leaves are the subject's, so nothing new has to be built for
it. -/
theorem residueMem_of_certs {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {F d : Nat}
    {res ty concl : Expr} {Δa : List AnnotTerm} {Rb Ca : AnnotTerm}
    (hinf : ConLeche.inferTypeCore μ envT F d res = .ok ty)
    (hdeq : ConLeche.isDefEqCore μ envT F d ty concl = .ok true)
    (hwsR : Expr.WScoped d res) (hbR : res.looseBVarsBounded 0 = true)
    (hLR : Expr.LeavesBounded res)
    (hwsC : Expr.WScoped d concl) (hbC : concl.looseBVarsBounded 0 = true)
    (hLC : Expr.LeavesBounded concl)
    (hctxR : CtxOk mp.base2 ψ d Δa res)
    (hctxC : CtxOk mp.base2 ψ d Δa concl)
    (hRb : denoteMeta mp.base2.acval envT ψ d res = some Rb)
    (hCa : denoteMeta mp.base2.acval envT ψ d concl = some Ca)
    (hokC : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Ca) :
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Rb) ∧
      ∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ Rb ∈ˢ interp V ρ Ca := by
  obtain ⟨-, -, ihd, ihi⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  -- the inferred type's syntax, and its context correspondence
  have hleafT : ∀ l ∈ ty.fvarLeaves, l ∈ res.fvarLeaves :=
    ConLeche.inferTypeCore_fvarLeaves mp.base2.wf F hinf hwsR
  have hwsT : Expr.WScoped d ty :=
    ConLeche.inferTypeCore_WScoped mp.base2.wf F hinf hwsR
  have hbT : ty.looseBVarsBounded 0 = true :=
    ConLeche.inferTypeCore_looseBVars mp.base2.wf F hinf hwsR hbR hLR
  have hLT : Expr.LeavesBounded ty := fun l hl => hLR l (hleafT l hl)
  have hctxT : CtxOk mp.base2 ψ d Δa ty := CtxOk.of_subset hctxR hleafT
  obtain ⟨ta, hta⟩ :=
    inferReads_of hμ (Rules.RulesInputs.ofSem mp ψ) hinf hwsR hbR hLR hctxR hRb
  obtain ⟨hokR, hokT, hmem⟩ := ihi hinf hwsR hbR hLR hctxR hRb hta
  refine ⟨hokR, fun ρ hρ => ?_⟩
  have heq := ihd hdeq hwsT hbT hLT hwsC hbC hLC hctxT hctxC hta hCa hokT hokC ρ hρ
  exact heq ▸ hmem ρ hρ

/-- **G1, at one valuation**: `ResidueOk` in the shape
`hres_of_residueOk` and `famCand_hCand`'s `hst` consume — the residue
reads, is graded, and lands in the conclusion's reading, at the frame
`ρ'` extended by the `ih` openers' VALUES. -/
theorem residueOk_of_certs {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {F d : Nat}
    {res ty concl : Expr} {Δa : List AnnotTerm} {Rb Ca : AnnotTerm}
    {ihvals : List V} {ρ' : Nat → V}
    (hinf : ConLeche.inferTypeCore μ envT F d res = .ok ty)
    (hdeq : ConLeche.isDefEqCore μ envT F d ty concl = .ok true)
    (hwsR : Expr.WScoped d res) (hbR : res.looseBVarsBounded 0 = true)
    (hLR : Expr.LeavesBounded res)
    (hwsC : Expr.WScoped d concl) (hbC : concl.looseBVarsBounded 0 = true)
    (hLC : Expr.LeavesBounded concl)
    (hctxR : CtxOk mp.base2 ψ d Δa res)
    (hctxC : CtxOk mp.base2 ψ d Δa concl)
    (hRb : denoteMeta mp.base2.acval envT ψ d res = some Rb)
    (hCa : denoteMeta mp.base2.acval envT ψ d concl = some Ca)
    (hokC : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ Ca)
    (hsat : Sat V Δa (consList ihvals ρ')) :
    ResidueOk V Rb ihvals ρ' (interp V (consList ihvals ρ') Ca) := by
  obtain ⟨hok, hmem⟩ :=
    residueMem_of_certs hμ mp hinf hdeq hwsR hbR hLR hwsC hbC hLC hctxR hctxC hRb hCa hokC
  exact ⟨(hok _ hsat).1, hmem _ hsat⟩

end ConLeche.Model
