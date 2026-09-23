module

public import ConLeche.Model.Inductives.BlockKitIhRun
public import ConLeche.Semantics.Tower.BlockRecGraphI
import ConLeche.Model.Inductives.BlockRuleCertsRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecIdxConv

public section

/-!
# The recursor model at the run: ONE graph producer (lane GRAPH1)

DESIGN, ruling of 2026-09-23.  The endpoint's regime premise
(`BlockRecPre` at every level assignment and base frame) is produced
here by ONE theorem, `blockRecPre_graph`, from the graph kit
(`GraphRecKit`, `SetModel/GraphRec.lean`; its family candidate
`famCandG_hCand`, `Semantics/Tower/BlockRecGraphI.lean`).  No level or
sort split reaches the candidate: the only sort-dependent fact is the
kit's `huniq` (§4), and it is the kernel's elimination guard read
three ways.

* **Majors** (§1): the classes' tagged elements at a prefix spine —
  `blockRecIs`/`blockRecCr`, the retired kit arm's own.
* **Decodings** (§1, `blockGraphDec`): the class, the constructor and
  the fields, which fit the constructor at the CARRIER and inject to
  the major.  A rule's own spine is one (`blockWfCtorAt_run`), at ANY
  sort — so the ι law never chooses a decoding.
* **Predecessors** (§1, `blockGraphPred`): the majors among the targets
  of the rule's guarded calls (`blockGraphCall`) — by DEFINITION, so no
  depth, no subterm relation, no regularity.
* **Bound and step**: the conclusion at the major (`blockRecMot`) and
  the residue at the decoding's fields and the graph's `ih` values
  (`blockGraphStep`).
* **Induction** (§5): the block's recorded LFP CLAUSE
  (`LfpClause.ind`), the property carried to every class of a member.
* **`huniq`** (§4): `ℓ = 0` — the bound is a truth value; `w ≠ 0` —
  `mkInj`; `w = 0, ℓ ≠ 0` — the counting guard leaves one constructor
  of one member and the subsingleton criterion makes its fields a
  function of the index (`blockChainFit_srcVals_zero`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockRuleFrame)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The kit's data at a block -/

section Data

/-- **A decoding at the prefix spine `xs`**: `u` is class `e.1`'s
tagged element built by constructor `e.2.1` from the fields `e.2.2`,
which fit that constructor at the CARRIER. -/
@[expose] def blockGraphDec (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (pdoms : Nat → List AnnotTerm) (mem nCt : Nat → Nat) (K : Nat) (xs : List V) (u : V)
    (e : Nat × Nat × List V) : Prop :=
  e.1 < K ∧ e.2.1 < nCt e.1 ∧ ∃ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs e.1 ∧
    d.ChainFit ψ (consList (xs.take d.nP) ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem e.1) e.2.1 e.2.2 ∧
    u = tagged e.1 i (d.inj ψ (mem e.1) e.2.1 e.2.2)

/-- **A decoding's predecessors**: the majors among the targets the
rule's guarded calls name at its fields (`call xs c j fs`). -/
@[expose] noncomputable def blockGraphPred (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (pdoms : Nat → List AnnotTerm) (mem : Nat → Nat) (K : Nat)
    (call : List V → Nat → Nat → List V → V → Prop) (xs : List V) (e : Nat × Nat × List V) :
    V :=
  sep (unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
    (call xs e.1 e.2.1 e.2.2)

/-- **The step**: the rule's residue at the decoding's fields and the
`ih` values the graph `g` supplies. -/
@[expose] noncomputable def blockGraphStep (ρ : Nat → V) (Rb0 : Nat → Nat → AnnotTerm)
    (ihv : List V → Nat → Nat → List V → V → List V) (xs : List V) (e : Nat × Nat × List V)
    (g : V) : V :=
  interp V (consList (ihv xs e.1 e.2.1 e.2.2 g) (consList (xs ++ e.2.2) ρ)) (Rb0 e.1 e.2.1)

theorem mem_blockGraphPred {d : BlockData V} {ψ : Name → Nat} {ρ : Nat → V}
    {pdoms : Nat → List AnnotTerm} {mem : Nat → Nat} {K : Nat}
    {call : List V → Nat → Nat → List V → V → Prop} {xs : List V} {e : Nat × Nat × List V}
    {v : V} :
    v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs e ↔
      v ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) ∧
        call xs e.1 e.2.1 e.2.2 v :=
  mem_sep

end Data

/-! ## 2. The kit at a prefix spine, and the family -/

section Kit

variable {env : Env} {mo : EnvModel V env} {names : List Name} {d : BlockData V}
  {ℓ K : Nat} {ψ : Name → Nat} {ρ : Nat → V} {mem nCt rP : Nat → Nat}
  {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm}
  {pdoms : Nat → List AnnotTerm} {fdoms ihdoms : Nat → Nat → List AnnotTerm}
  {Rb0 Ca : Nat → Nat → AnnotTerm} {ihv : List V → Nat → Nat → List V → V → List V}
  {call : List V → Nat → Nat → List V → V → Prop}
  {envT : Env} {mp : EnvModelM V μ envT} {F : Nat}

/-- **The graph kit at a prefix spine.**  Its typing obligation `hst`
is the rule's certificates at the decoding's own spine (G1), with the
`ih` openers' fit (`hihF`) given that the graph is bound-valued at the
PREDECESSORS; the two facts no certificate carries — the induction and
`huniq` — are premises, produced at the run (§4, §5). -/
noncomputable def blockGraphKit (hμ : μ.verifiedChecks = true) (xs : List V)
    (hconclTy : ∀ c, c < K → ∀ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ c, c < K → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ c, c < K → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ c, c < K → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs)))
    (huniq : ∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
      ∀ e e', blockGraphDec d ψ ρ pdoms mem nCt K xs u e →
        blockGraphDec d ψ ρ pdoms mem nCt K xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs u →
        v' ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs u →
        v = v')
    (hind : ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
        (∃ e, blockGraphDec d ψ ρ pdoms mem nCt K xs u e ∧
          ∀ v, v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) → P u) :
    GraphRecKit ℓ (unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
      (Nat × Nat × List V) where
  Dec := blockGraphDec d ψ ρ pdoms mem nCt K xs
  pred := blockGraphPred d ψ ρ pdoms mem K call xs
  B := blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
  st := blockGraphStep ρ Rb0 ihv xs
  hpred := fun _ _ _ _ => sep_subset
  hB := blockRecMot_mem_univ hconclTy
  hst := by
    intro u _ e he g hg
    obtain ⟨c, j, fs⟩ := e
    obtain ⟨hc, hj, i, hi, hfit, rfl⟩ := he
    obtain ⟨hparFit, hprefFit⟩ := blockRecIs_fits hi
    rw [blockRecIs_pos hparFit hprefFit] at hi
    have hgB : ∀ v, v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v := by
      intro v hv
      have h1 := app_mem_of_mem_piSet hg hv
      exact gGraph_mem_B (blockRecMot_mem_univ hconclTy) (fun _ _ _ _ => sep_subset)
        (mem_blockGraphPred.mp hv).1 h1
    have hres := (hcerts c hc j hj).residueOk hμ
      (hspF c hc hparFit hprefFit j hj i fs hi hfit)
      (hihF c hc hparFit hprefFit j hj i fs hi hfit g hgB)
    show interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j) ∈ˢ _
    rw [← hCaB c hc hparFit hprefFit j hj i fs hi hfit g]
    exact hres.2
  huniq := huniq
  ind := hind

/-- **The graph family at a block**: the kit at every prefix spine,
over the block's own index sets and carriers, with the two type
readings (`blockWf_hsplit`, `blockWf_hconcl`). -/
noncomputable def blockGraphFam (hμ : μ.verifiedChecks = true) (hM : BlockModelAt mo names d)
    (hmemK : ∀ c, c < K → mem c < d.k)
    (hlenIds : ∀ c, c < K → (d.IdsM (mem c) ψ).length = d.nIdxAt (mem c))
    (hsplitR : BlockRecSplitAt V mo d ψ K rP mem rds ρ)
    (hpdE : ∀ c, c < K → pdoms c = ((rds c).map (·.2.2)).take (rP c))
    (hconclTy : ∀ xs : List V, ∀ c, c < K → ∀ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ mem xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (mem c) ψ) (d.nIdxAt (mem c)) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp F ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      d.ChainFit ψ (consList (xs.take d.nP) ρ)
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ))) i (mem c) j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs)))
    (huniq : ∀ xs : List V,
      ∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
      ∀ e e', blockGraphDec d ψ ρ pdoms mem nCt K xs u e →
        blockGraphDec d ψ ρ pdoms mem nCt K xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs u →
        v' ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs u →
        v = v')
    (hind : ∀ xs : List V, ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
        (∃ e, blockGraphDec d ψ ρ pdoms mem nCt K xs u e ∧
          ∀ v, v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) → P u) :
    GraphFamData V ℓ K rP rds concl ρ (Nat × Nat × List V) where
  Is := blockRecIs d ψ ρ pdoms mem
  Cr := blockRecCr d ψ ρ mem
  tupOf := fun c is => d.tup ψ (mem c) is
  kit := fun xs => blockGraphKit (Rb0 := Rb0) (Ca := Ca) (ihv := ihv) (call := call) hμ xs
    (hconclTy xs) hcerts (hspF xs) (hihF xs) (hCaB xs) (huniq xs) (hind xs)
  hsplit := blockWf_hsplit hM hpdE hmemK hsplitR
  hconcl := blockWf_hconcl hM
    (fun c hc => Nat.lt_of_lt_of_le (hmemK c hc) (Nat.le_add_right _ _)) hlenIds hsplitR

end Kit

/-! ## 3. The rule's calls, and the two `ih` rows

`blockGraphCall` is the predecessor RELATION at the run: the targets
the rule's guarded calls name, per `ih` key and telescope spine — the
very tagged elements the pinned `ih` values (`blockKitIhv`) read the
graph at.  So "a call's target is a predecessor" holds BY DEFINITION
once it is a major (the callee's split), which is all the retired WF
arm's depth argument (`mkDepth`, `tcPred`) was for. -/

section Rows

/-- **The rule's call targets** at the prefix spine `xs` and fields
`fs`: per `ih` key `(fi, c')` and telescope spine `bs`, class `c'`'s
tagged element at the call's index readings and the applied field. -/
@[expose] def blockGraphCall (pp : ConLeche.BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (ψ : Name → Nat) (d : BlockData V)
    (ρ : Nat → V) (xs : List V) (c j : Nat) (fs : List V) (v : V) : Prop :=
  ∃ key ∈ (blockRuleFrameAt pp rs c j).ihKeys, ∃ bs : List V,
    SpineFit (consList (xs ++ fs) ρ) ((blockKitTlA pp rs acval envC ψ c j key.1).map (·.2.2)) bs ∧
    v = tagged key.2
      (d.tup ψ (pp.toBlockShape.recTgtAt key.2)
        ((blockKitEisA pp rs acval envC ψ c j key.1).map
          (interp V (consList bs (consList (xs ++ fs) ρ)))))
      (interp V (consList bs (consList (xs ++ fs) ρ)) (blockKitFapA pp rs c j key.1))

/-- **One opener's tower inhabits its Π-tower**, at EVERY level: the
retired `blockRecIhv_mem` with its `ℓ ≠ 0` replaced by what `ℓ = 0`
needs, the opener's conclusion read to a truth value. -/
theorem blockGraphIhv_mem {ℓ c' : Nat} {tl : List (Nat × Nat × AnnotTerm)} {Cih : AnnotTerm}
    {tup : Nat → List V → V} {σ : Nat → V} {g : V}
    {eis : List AnnotTerm} {fap : AnnotTerm}
    (hbits : ∀ dd ∈ tl, (ℓ = 0 ↔ dd.2.1 = 0))
    (hleaf : ∀ bs : List V, SpineFit σ (tl.map (·.2.2)) bs →
      app g (tagged c' (tup c' (eis.map (interp V (consList bs σ))))
          (interp V (consList bs σ) fap))
        ∈ˢ interp V (consList bs σ) Cih ∧
      (ℓ = 0 → interp V (consList bs σ) Cih ∈ˢ (univZero : V))) :
    lamTowerA ℓ σ [] tl
        (fun _ τ => app g (tagged c' (tup c' (eis.map (interp V τ))) (interp V τ fap)))
      ∈ˢ interp V σ (mkPisAV tl Cih) :=
  lamTowerA_mem hbits (towerWalkA_of_spines_body fun ys hsp => hleaf ys hsp)

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **The kit's `hihF`, PRODUCED** — at every level and every sort: the
graph-built `ih` values fit the pinned `ih` openers' domains, given
that the graph is bound-valued at the rule's PREDECESSORS.  Per opener
the tower inhabits the Π-tower over the callee's peeled conclusion
(`blockGraphIhv_mem`), because that conclusion reads to the bound at
the call's target (`blockRecCa_value`), and the target is a
predecessor: a major by the callee's split, a call by definition.  At
`ℓ = 0` the conclusion's reading is a truth value (`hconclTy`). -/
theorem blockGraphIhF_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hconclTy : ∀ c, c < rs.length →
      ∀ i, i ∈ˢ blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          p.toBlockShape.recTgtAt xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ p.toBlockShape.recTgtAt xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (p.toBlockShape.recTgtAt c) ψ)
            (d.nIdxAt (p.toBlockShape.recTgtAt c)) i ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim
          p.toBlockShape.large)) : V)) :
    ∀ c, c < rs.length →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) ((p.toBlockShape.recTgtAt) c) →
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        (∀ v, v ∈ˢ blockGraphPred d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt rs.length
            (blockGraphCall p rs mpC.base2.acval envC ψ d ρ) xs (c, j, fs) →
          app g v ∈ˢ blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs
            ψ) (fun c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ)
            (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt) c')) ρ xs v) →
        SpineFit (consList (xs ++ fs) ρ) (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j)
          ((blockKitIhv p rs mpC.base2.acval envC ψ (Level.eval ψ (ConLeche.structElimLevel
            p.toBlockShape.elim p.toBlockShape.large)) d ρ) xs c j fs g) := by
  intro c hc hpar hpref j hj i fs hi hfit g hg
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  have hbnd := blockRuleDoms_bounded_at hμ h hcore ψ
  -- the rule's field fit, off the witness
  have hspF := blockKitSpF_run hμ h hkLen hcore hmr hM hN rfl hctM ψ hbnd ρ rs.length xs c hc
    hpar hpref j hj i fs hi hfit
  rw [blockRecFdomsK_eq_of_bounded hbnd hr hcA hrhs] at hspF
  obtain ⟨xs₁, fs₁, heq, h1, hfsR⟩ := spineFit_append_split hspF
  have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hpref.length_eq]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  have hxs' : xs.length = p.toBlockShape.rulePrefixAt c := by rw [hpref.length_eq, hpl]
  have hct : blockRuleCtorOf rs c j = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨rbs, ty, concl, -, -, -, hopen, -, -, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  have hIlen : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length
      = (blockRuleFrameAt p rs c j).nR := by
    rw [blockRuleIhdomsAV, hct, readOpenedDoms_length_eq]
    exact openPisAtFvars_length _ hopen
  rw [(blockRuleCertsChain_eq hμ h hkLen hcore ψ hc hj rs.length).2.1]
  refine spineFit_of_getD (by rw [blockKitIhv_length, hIlen]) fun q hq => ?_
  rw [hIlen] at hq
  obtain ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hrPc', hrss, htgt, hIget, -, hcon, -, -, -, -, -, -, -,
    hframe⟩ := blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
  -- the domain, past the `q` values already bound
  have htk : ((blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs g).take q).length
      = q := by
    rw [List.length_take, blockKitIhv_length]; omega
  rw [hIget]
  have hcancel := interp_liftN_ihvals (V := V)
    (ihvals := (blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs g).take q)
    (σ := consList (xs ++ fs) ρ)
    (mkPisAV (blockKitTlA p rs mpC.base2.acval envC ψ c j fi) CihR)
  rw [htk] at hcancel
  rw [hcancel]
  -- the value: the tower of the graph over the moved telescope
  have hval : (blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs g).getD q pt
      = lamTowerA (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
          (consList (xs ++ fs) ρ) [] (blockKitTlA p rs mpC.base2.acval envC ψ c j fi)
          (fun _ τ => app g (tagged c'
            ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
              (p.toBlockShape.recTgtAt c')
              ((blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map (interp V τ)))
            (interp V τ (blockKitFapA p rs c j fi)))) := by
    rw [blockKitIhv, blockRecIhvAt, List.getD_eq_getElem?_getD, List.getElem?_map, hkeyE]
    rfl
  rw [hval]
  obtain ⟨-, -, -, -, -, -, -, hpw⟩ := blockRuleFrameAt_rows (pp := p) hct
  refine blockGraphIhv_mem (V := V) (c' := c')
    (tup := fun c'' is => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
      (p.toBlockShape.recTgtAt c'') is) (fun dd hdd => ?_) (fun bs hbs => ?_)
  · unfold blockKitTlA at hdd
    obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hdd
    rw [he, mem_rebit hd', hpw]
    exact (pwBit_zeronessOf ψ _).symm
  · obtain ⟨hbsC, hspC, hfap, -⟩ := hframe ρ xs fs hpref hfsR bs hbs
    rw [List.map_append, List.map_singleton] at hspC
    have hxl' : xs.length = p.toBlockShape.rulePrefixAt c' := by rw [hxs', hrPc']
    have hfsl : fs.length = cA.2 := by
      rw [hfsR.length_eq, blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ]
    have hbl : bs.length = (blockKitTlA p rs mpC.base2.acval envC ψ c j fi).length := by
      rw [hbs.length_eq, List.length_map]
    -- the callee's type and its split at the call's spine
    have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'K
    obtain ⟨-, -, -, -, hTyE, -, -, -, -, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ
    have hconclB := (checkBlockRecK_tyBounds hμ mpC h hr' ψ).2
    have hrdsL := hspC.length_eq
    rw [List.length_map, List.length_append, List.length_append, List.length_map,
      List.length_singleton, hxl'] at hrdsL
    have hCa := blockRecCa_value (V := V) (ρ := ρ) (xs := xs) (fs := fs) (ihvals := bs)
      (is := (blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
        (interp V (consList bs (consList (xs ++ fs) ρ))))
      (maj := interp V (consList bs (consList (xs ++ fs) ρ)) (blockKitFapA p rs c j fi))
      hcon hTyE (by rw [← hrdsL]; omega) rfl hconclB hxl' hfsl hbl rfl rfl
    rw [hCa]
    have hsplitA := blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ) c' hc'K _
      hspC
    rw [prefOf_split hxl', idxOf_split hxl'] at hsplitA
    obtain ⟨-, -, hparS, hidxS, -⟩ := hsplitA
    have hmemk' := (blockRecMajor_run hμ mpC h hmr hr' ψ).2.1
    have hmN' : p.toBlockShape.recTgtAt c'
        < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).N :=
      Nat.lt_of_lt_of_le hmemk' (Nat.le_add_right _ _)
    have hIok := hM.idxOk ψ _ ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
      ppsOf).satOfSpine hparS) _ hmN'
    have hisOf := isOfW_tupW hIok hidxS
    rw [blockMembers_IdsM_length hmr hmemk' ψ] at hisOf
    have hmot := blockRecMot_tagged (V := V) (K := rs.length) hc'K
      (concl := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (uOf := fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
        (p.toBlockShape.recTgtAt c') ψ)
      (nIdxOf := fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
        ppsOf).nIdxAt (p.recTgtAt c')) (ρ := ρ) (xs := xs)
      (i := (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
        (p.toBlockShape.recTgtAt c') ((blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
          (interp V (consList bs (consList (xs ++ fs) ρ)))))
      (x := interp V (consList bs (consList (xs ++ fs) ρ)) (blockKitFapA p rs c j fi))
    have hisOf' : isOfW ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
        (p.toBlockShape.recTgtAt c') ψ)
        ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt (p.recTgtAt c'))
        ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
          (p.toBlockShape.recTgtAt c') ((blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
            (interp V (consList bs (consList (xs ++ fs) ρ)))))
        = (blockKitEisA p rs mpC.base2.acval envC ψ c j fi).map
            (interp V (consList bs (consList (xs ++ fs) ρ))) := hisOf
    rw [hisOf'] at hmot
    rw [← hmot]
    -- the call's target is a major (the callee's split) and a call (by definition)
    have hsplit := blockWf_hsplit hM
      (pdoms := blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (mem := p.toBlockShape.recTgtAt) (rP := p.toBlockShape.rulePrefixAt)
      (rds := fun c => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      (fun c _ => by rw [blockRulePdomsAV, List.map_take])
      (fun c hc => (blockRecMajor_run hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1)
      (blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ)) c' hc'K _ hspC
    rw [prefOf_split hxl', idxOf_split hxl', majOf_split] at hsplit
    have hU := tagged_mem_unionSet hc'K hsplit.2.2.1 hsplit.2.2.2
    have hkm : (fi, c') ∈ (blockRuleFrameAt p rs c j).ihKeys := List.mem_of_getElem? hkeyE
    refine ⟨hg _ (mem_blockGraphPred.mpr ⟨hU, (fi, c'), hkm, bs, hbs, rfl⟩), fun h0 => ?_⟩
    have hmem := blockRecMot_mem_univ (K := rs.length) hconclTy _ hU
    rw [h0, univ_zero] at hmem
    exact hmem

/-- **The kit's `ih` chain, PRODUCED** — at every level: the
graph-built `ih` values, read off ANY recursor `r` over the rule's
predecessors, ARE the `ih` terms' readings at the chain frame of ANY
candidate `a` whose fold along a callee's spine is `r` at the tagged
call (`hfold` — `famCandG_fold` at the family the producer builds).
Per key the call's target is a predecessor (a major by the callee's
split, a call by definition), so the graph reads `r` there. -/
theorem blockGraphIhChain_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (ψ : Name → Nat) (ρ : Nat → V) (a : Nat → V) (xs : List V) (r : V → V)
    (hfold : ∀ c', c' < rs.length → ∀ (is : List V) (x : V),
      xs.length = p.toBlockShape.rulePrefixAt c' →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2))
        (xs ++ (is ++ [x])) →
      r (tagged c' (d.tup ψ (p.toBlockShape.recTgtAt c') is) x)
        = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) :
    ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c → ∀ fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
      SpineFit (chainFrame rs.length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) →
      blockKitIhv p rs mpC.base2.acval envC ψ
          (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) d ρ
          xs c j fs
          (graph r (blockGraphPred d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt rs.length (blockGraphCall p rs mpC.base2.acval envC ψ d ρ) xs
            (c, j, fs)))
        = (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame rs.length a ρ))) := by
  intro c hc j hj fs hxs hsp
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfsl, hnF, hpre, hps, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel hμ h hkLen hcore hmr rfl hctM hr hj hxs hsp
  -- the fields at the base frame
  have hfsR : SpineFit (consList xs ρ)
      (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) fs := by
    obtain ⟨xs₁, fs₁, heq, h1, h2⟩ := spineFit_append_split hsp
    have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hxs]
    obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
    rw [blockRecFdomsK, ← hxs] at h2
    exact (spineFit_liftDomsK (K := rs.length) _ _ _).mp h2
  obtain ⟨-, -, hfrF, -⟩ := blockRuleFrameAt_rows (pp := p) (blockRuleCtorOf_eq hr hcA)
  have hNb : (xs ++ fs).length = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [List.length_append, hxs', hfsl]
  have hkeyAt : ∀ key ∈ (blockRuleFrameAt p rs c j).ihKeys, ∃ q,
      q < (blockRuleFrameAt p rs c j).nR ∧ (blockRuleFrameAt p rs c j).ihKeys[q]? = some key := by
    intro key hkm
    obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hkm
    exact ⟨q, hq, by rw [List.getElem?_eq_getElem hq, hqe]⟩
  rw [blockRuleIhsRunAV_eq_ihsAt]
  refine blockRecIhvAt_eq_fit (N := (xs ++ fs).length) hxs' (by rw [hfsl, hfrF]) rfl
    (fun key hkm => ?_) (fun key hkm => ?_) (fun key hkm => ?_)
  · obtain ⟨q, hq, hqk⟩ := hkeyAt key hkm
    obtain ⟨fi, c', CihR, hkeyE, hc'K, -⟩ :=
      blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
    obtain rfl : key = (fi, c') := Option.some.inj (hqk.symm.trans hkeyE)
    exact hc'K
  · obtain ⟨q, hq, hqk⟩ := hkeyAt key hkm
    obtain ⟨fi, c', CihR, hkeyE, -, -, -, -, -, -, -, -, hDB, -⟩ :=
      blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
    obtain rfl : key = (fi, c') := Option.some.inj (hqk.symm.trans hkeyE)
    intro l hl
    rw [hNb]
    exact DomsBelow.getD_below l hDB hl
  · obtain ⟨q, hq, hqk⟩ := hkeyAt key hkm
    obtain ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hrPc', hrss, htgt, -, -, -, -, hEB, hFB, -, -, -, -,
      hframe⟩ := blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
    obtain rfl : key = (fi, c') := Option.some.inj (hqk.symm.trans hkeyE)
    intro bs hbs
    dsimp only at hbs ⊢
    obtain ⟨hbsC, hspC, hfap, -⟩ := hframe ρ xs fs hpre hfsR bs hbs
    have hbl : bs.length = (blockKitTlA p rs mpC.base2.acval envC ψ c j fi).length := by
      rw [hbs.length_eq, List.length_map]
    -- the chain readings of the call's arguments are the base ones
    have hchain : (blockKitEisA p rs mpC.base2.acval envC ψ c j fi
          ++ [blockKitFapA p rs c j fi]).map
          (interp V (consList bs (consList (xs ++ fs) (chainFrame rs.length a ρ))))
        = (blockKitEisA p rs mpC.base2.acval envC ψ c j fi
          ++ [blockKitFapA p rs c j fi]).map (interp V (consList bs (consList (xs ++ fs) ρ))) := by
      refine List.map_congr_left fun e he => (interp_leaf_chain rfl ?_).symm
      rw [hNb, hbl]
      rcases List.mem_append.mp he with he | he
      · exact hEB e he
      · rw [List.mem_singleton.mp he]; exact hFB
    rw [hchain]
    rw [List.map_append, List.map_singleton] at hspC ⊢
    have hxl' : xs.length = p.toBlockShape.rulePrefixAt c' := by rw [hxs', hrPc']
    -- the call's target is a major (the callee's split) and a call (by definition)
    have hsplit := blockWf_hsplit hM
      (pdoms := blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (mem := p.toBlockShape.recTgtAt) (rP := p.toBlockShape.rulePrefixAt)
      (rds := fun c => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      (fun c _ => by rw [blockRulePdomsAV, List.map_take])
      (fun c hc => (blockRecMajor_run hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1)
      (blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ)) c' hc'K _ hspC
    rw [prefOf_split hxl', idxOf_split hxl', majOf_split] at hsplit
    have hU := tagged_mem_unionSet hc'K hsplit.2.2.1 hsplit.2.2.2
    rw [app_graph (mem_blockGraphPred.mpr ⟨hU, (fi, c'), hkm, bs, hbs, rfl⟩)]
    exact hfold c' hc'K _ _ hxl' hspC

/-! ## 4. `huniq` — the kernel's elimination guard, read three ways -/

/-- **The kit's `huniq`, PRODUCED**: at every major two decodings are
equal, or the bound is a subsingleton.

* `ℓ = 0`: the bound is a truth value (`hconclTy` at level `0`);
* `w ≠ 0`: the injection is injective (`mkInj`,
  `blockCarrier_case_unique`);
* `w = 0, ℓ ≠ 0`: the counting guard (`blockSqGuard_run`) leaves one
  recursor of one member with at most one constructor, of the declared
  large shape, and the subsingleton criterion makes that constructor's
  fields a function of the INDEX (`blockChainFit_srcVals_zero`). -/
theorem blockGraphUniq_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hconclTy : ∀ c, c < rs.length →
      ∀ i, i ∈ˢ blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          p.toBlockShape.recTgtAt xs c →
      ∀ x, x ∈ˢ app (blockRecCr d ψ ρ p.toBlockShape.recTgtAt xs c) i →
      interp V
          (consList (xs ++ (isOfW (d.uM (p.toBlockShape.recTgtAt c) ψ)
            (d.nIdxAt (p.toBlockShape.recTgtAt c)) i ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim
          p.toBlockShape.large)) : V)) :
    ∀ u, u ∈ˢ unionSet rs.length
        (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          p.toBlockShape.recTgtAt xs)
        (blockRecCr d ψ ρ p.toBlockShape.recTgtAt xs) →
      ∀ e e',
        blockGraphDec d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          p.toBlockShape.recTgtAt (blockRecNCt rs) rs.length xs u e →
        blockGraphDec d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          p.toBlockShape.recTgtAt (blockRecNCt rs) rs.length xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
          (fun c' => d.uM (p.toBlockShape.recTgtAt c') ψ)
          (fun c' => d.nIdxAt (p.toBlockShape.recTgtAt c')) ρ xs u →
        v' ∈ˢ blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
          (fun c' => d.uM (p.toBlockShape.recTgtAt c') ψ)
          (fun c' => d.nIdxAt (p.toBlockShape.recTgtAt c')) ρ xs u →
        v = v' := by
  intro u hu e e' he he'
  obtain ⟨c, j, fs⟩ := e
  obtain ⟨c', j', fs'⟩ := e'
  obtain ⟨hc, hj, i, hi, hfit, rfl⟩ := he
  obtain ⟨-, hj', i', hi', hfit', heq⟩ := he'
  obtain ⟨rfl, rfl, hinj⟩ := tagged_inj heq
  by_cases hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim
      p.toBlockShape.large) = 0
  · -- the bound is a truth value
    right
    have hmem := blockRecMot_mem_univ (K := rs.length) hconclTy _ hu
    rw [hℓ, univ_zero] at hmem
    exact fun v v' hv hv' =>
      (eq_pt_of_mem_univZero hmem hv).trans (eq_pt_of_mem_univZero hmem hv').symm
  left
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  obtain ⟨hparFit, hprefFit⟩ := blockRecIs_fits hi
  rw [blockRecIs_pos hparFit hprefFit] at hi
  have hnCt := (blockRecNCt_seam (V := V) (env₀ := env₀) (pk := pk) (uOfD := uOfD)
    (ppsOf := ppsOf) h c hc).1
  have hjc : j < ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c)).length := by rw [hnCt]; exact hj
  have hj'c : j' < ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c)).length := by rw [hnCt]; exact hj'
  have hmemk := (blockRecMajor_run (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1
  have hmN : p.toBlockShape.recTgtAt c
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).N :=
    Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  by_cases hw : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).w ψ = 0
  · -- the subsingleton criterion: the fields are a function of the index
    obtain ⟨hK1, hmem0, hct1, hlarge⟩ := blockSqGuard_run hμ h hmr ψ hℓ hw
    obtain rfl : c = 0 := by omega
    have hj0 : j = 0 := by omega
    have hj'0 : j' = 0 := by omega
    subst hj0 hj'0
    rw [hmem0] at hi hfit hfit' hjc hmemk
    have hk0 : 0 < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k := hmemk
    have hlenP : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).params ψ).length
        = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP := by
      have hl := hS.lenPps 0 ψ hk0
      rw [BlockData.params, List.length_map, List.length_take]
      exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hl.symm))
    obtain ⟨cA, hcj⟩ : ∃ cA,
        ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM 0)[0]?
          = some cA := ⟨_, List.getElem?_eq_getElem hjc⟩
    obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 0 hk0 0 cA hcj
    obtain ⟨-, -, hcd⟩ := hcore.2.2.1 0 0 cA hcj
    have hsrc : ∀ gs : List V,
        (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ChainFit ψ
          (consList (xs.take (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP) ρ)
          (lfpTuple ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).w ψ)
            (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).N
            ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).idx ψ
              (consList (xs.take
                (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP) ρ))
            ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Φ ψ
              (consList (xs.take
                (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP) ρ)))
          i 0 0 gs →
        gs = srcVals (isOfW ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
            0 ψ) ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt 0) i)
          (srcList (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Ess
            0 ψ).getD 0 [])
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
              0 ψ).getD 0 []).length) := fun gs hgs =>
      blockChainFit_srcVals_zero hM hcj ⟨hfindC, hlpsC, hcd⟩ hlarge hw
        (fun σ => ⟨fun hσ => ((hS.frames 0 hk0 0 cA hcj).1 ψ σ).mp
            (hS.paramsOf 0 hk0 ψ σ hσ 0 hk0),
          fun hσ => hS.paramsOf 0 hk0 ψ σ (((hS.frames 0 hk0 0 cA hcj).1 ψ σ).mpr hσ) 0 hk0⟩)
        (blockMembers_IdsM_length hmr hk0 ψ) (by rw [hparFit.length_eq, hlenP]) hparFit
        (fun l _ => by have := hN.2.1 0 0 l; rwa [hN.2.2.2] at this)
        (Nat.lt_of_lt_of_le hk0 (Nat.le_add_right _ _)) hjc (lfpTuple_mem _ _ _ _)
        (TupleLe.refl _ _ _) hi hgs
    rw [hsrc fs hfit, hsrc fs' hfit']
  · -- `mkInj`
    obtain ⟨rfl, rfl⟩ := blockCarrier_case_unique hM hw hmN hjc hj'c hfit hfit' hinj
    rfl

/-! ## 5. The induction — from the block's recorded LFP CLAUSE -/

/-- **The kit's `ind`, PRODUCED from the lfp clause** (`LfpClause.ind`,
the clause `declBlock` records in the environment): the property, read
per MEMBER as "every class of this member at every major", holds at an
injection of fields fitting at the SEPARATED tuple because the rule's
own fields decode it and every call target is a recursive field
folded along its telescope — which the separated tuple puts in the
property (`blockIndPred_of`).  The two readings of a call (the rule's
`ih` key data, the block's slot data) meet at `blockKitIhKey_run`'s
frame conversion. -/
theorem blockGraphInd_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hC : LfpClause mpC.base2.acval d.toLfp)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet rs.length
          (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt xs)
          (blockRecCr d ψ ρ p.toBlockShape.recTgtAt xs) →
        (∃ e, blockGraphDec d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecNCt rs) rs.length xs u e ∧
          ∀ v, v ∈ˢ blockGraphPred d ψ ρ
              (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
              p.toBlockShape.recTgtAt rs.length
              (blockGraphCall p rs mpC.base2.acval envC ψ d ρ) xs e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet rs.length
          (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt xs)
          (blockRecCr d ψ ρ p.toBlockShape.recTgtAt xs) → P u := by
  intro P hP u hu
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  obtain ⟨c, hc, i, hi, x, hx, rfl⟩ := mem_unionSet.mp hu
  obtain ⟨hparFit, -⟩ := blockRecIs_fits hi
  have hsat := (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).satOfSpine hparFit
  have hmN : ∀ c', c' < rs.length → p.toBlockShape.recTgtAt c'
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).N := fun c' hc' =>
    Nat.lt_of_lt_of_le (blockRecMajor_run (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hc') ψ).2.1
      (Nat.le_add_right _ _)
  -- the property, per MEMBER: every class of it, at every major
  let P' : Nat → V → V → Prop := fun m t y => ∀ c', c' < rs.length →
    p.toBlockShape.recTgtAt c' = m →
    tagged c' t y ∈ˢ unionSet rs.length
      (blockRecIs (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) p.toBlockShape.recTgtAt xs)
      (blockRecCr (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
        p.toBlockShape.recTgtAt xs) →
    P (tagged c' t y)
  obtain ⟨hparI, hprefI⟩ := blockRecIs_fits hi
  rw [blockRecIs_pos hparI hprefI] at hi
  refine hC.ind hsat P' ?_ (p.toBlockShape.recTgtAt c) (hmN c hc) i hi x hx c hc rfl hu
  intro m _ t ht j fs hfitS c' hc' hmem hu'
  subst hmem
  obtain ⟨hjl, hfitS⟩ := hfitS
  obtain ⟨-, htI, -⟩ := tagged_mem_unionSet_iff.mp hu'
  obtain ⟨hpar', hpref'⟩ := blockRecIs_fits htI
  rw [blockRecIs_pos hpar' hpref'] at htI
  have hr : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
  have hjr : j < rs[c'].2.2.2.length := by rw [← hctM c' _ hr]; exact hjl
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c'].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c'))[j]? = some cA := by rw [hctM c' _ hr]; exact hcA
  have hmemk := (blockRecMajor_run (V := V) hμ mpC h hmr hr ψ).2.1
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  obtain ⟨-, -, hcd⟩ := hcore.2.2.1 _ j cA hcj
  -- the fields fit at the CARRIER
  have hfitC := blockChainFit_of_le hM hcj ⟨hfindC, hlpsC, hcd⟩ hpar'
    (fun l _ => by rw [← hN.2.2.2]; exact hN.2.1 _ j l) (hmN c' hc') hjl htI
    (sepTuple_mem _ _ _ _ _) (sepTuple_le _ _ _ _ _) hfitS
  have hjn : j < blockRecNCt rs c' := by
    rw [← (blockRecNCt_seam (V := V) (env₀ := env₀) (pk := pk) (uOfD := uOfD)
      (ppsOf := ppsOf) h c' hc').1]; exact hjl
  refine hP _ hu' ⟨(c', j, fs), ⟨hc', hjn, t, ?_, hfitC, rfl⟩, fun v hv => ?_⟩
  · rw [blockRecIs_pos hpar' hpref']; exact htI
  obtain ⟨hvU, key, hkm, bs, hbs, rfl⟩ := mem_blockGraphPred.mp hv
  -- the rule's field fit, off the carrier fit
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c'].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by
      rw [checkBlockRecK_rulesLen h hkLen hr]; exact (List.getElem?_eq_some_iff.mp hcA).1)⟩
  have hbnd := blockRuleDoms_bounded_at hμ h hcore ψ
  have hspF := blockKitSpF_run hμ h hkLen hcore hmr hM hN rfl hctM ψ hbnd ρ rs.length xs c' hc'
    hpar' hpref' j hjn t fs htI hfitC
  rw [blockRecFdomsK_eq_of_bounded hbnd hr hcA hrhs] at hspF
  obtain ⟨xs₁, fs₁, heq, h1, hfsR⟩ := spineFit_append_split hspF
  have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hpref'.length_eq]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
  have hfsl : fs.length = cA.2 := by
    rw [hfsR.length_eq, blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs ψ]
  -- the key's two readings
  obtain ⟨q, hq, hqe⟩ := List.getElem_of_mem hkm
  have hqk : (blockRuleFrameAt p rs c' j).ihKeys[q]? = some key := by
    rw [List.getElem?_eq_getElem hq, hqe]
  obtain ⟨fi, c'', CihR, hkeyE, hc''K, hfiC, -, hrss, htgt, -, -, -, -, -, -, -, -, -, -,
    hframe⟩ := blockKitIhKey_run hμ h hkLen hdR' hN hS hcore hmr hM hr hcA ψ hq
  obtain rfl : key = (fi, c'') := Option.some.inj (hqk.symm.trans hkeyE)
  obtain ⟨hbsC, -, hfap, hes⟩ := hframe ρ xs fs hpref' hfsR bs hbs
  have hfiF : fi < (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
      (p.toBlockShape.recTgtAt c') ψ).getD j []).length := by
    rw [← hfitS.length_eq, hfsl]; exact hfiC
  have htgtN : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tgts
      (p.toBlockShape.recTgtAt c') j fi
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).N := by
    rw [htgt]; exact hmN c'' hc''K
  obtain ⟨-, -, hPt⟩ := blockIndPred_of hM hsat (hmN c' hc') htI hjl hfitS hfiF hrss htgtN hbsC
  rw [htgt] at hPt
  have hes' : (blockKitEisA p rs mpC.base2.acval envC ψ c' j fi).map
        (interp V (consList bs (consList (xs ++ fs) ρ)))
      = ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Eiss
          (p.toBlockShape.recTgtAt c') ψ).getD j []).getD fi []).map
        (interp V (consList bs (consList (fs.take fi)
          (consList (xs.take (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
            ppsOf).nP) ρ)))) := hes
  dsimp only at hvU ⊢
  rw [hfap, hes'] at hvU ⊢
  exact hPt c'' hc''K rfl hvU

end Rows

/-! ## 6. THE PRODUCER — the endpoint's regime premise from the graph kit -/

section Producer

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **THE RECURSOR MODEL** — `declBlock_data`'s regime conjunct, from
the graph kit at every level assignment and base frame, with NO level
or sort split: the family at `blockGraphFam` (whose `huniq` is the
elimination guard, §4, and whose induction is the block's recorded
lfp clause, §5) handed to `famCandG_hCand`.  The ι law at a rule is
`rec_eq` at the rule's own decoding (`blockWfCtorAt_run`), its `ih`
values read off the graph at the call targets (§3).

Taken: the recorded clause `hlfp`, the family level's typing `hTy`,
and the ι equations' grading inputs in their producers' spellings
(`hokG` — `blockRuleGrading_run`, `hihsFit` — `blockIhFitTyped_run`,
`hcertsB` — `blockRuleCertsW_run`, `hG` — `blockGradeLhs_run`,
`blockGradeIhs_run`).  Everything else is paid from the run. -/
theorem blockRecPre_graph (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    {s : (Name → Nat) → Nat}
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (s ψ) : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c))
    (hokG : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∀ l, l < p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD l default))
    (hihsFit : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c → ∀ ys : List V,
        SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
        SpineFit (consList ys ρ) (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j)
          ((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
            (interp V (consList ys (consList tup ρ)))))
    (hcertsB : ∀ (ψ : Name → Nat), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c)
        (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
        (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j)
        (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j)
        (blockRuleRbAV p rs mpC.base2.acval envC ψ c j)
        (blockRuleCaAV p rs mpC.base2.acval envC ψ c j))
    (hG : BlockGradeOwed mpC p rs (fun ψ' => blockRuleIhsRunAV p rs mpC.base2.acval envC ψ')) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleIhsRunAV p rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleRbAV p rs mpC.base2.acval envC ψ') ψ) ρ := by
  intro ψ ρ
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  obtain ⟨us, uOf, helim, hmemU, hbitsE, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hℓeq := blockRecHeadLevel_run h helim hmemU hruns
  have hmemk : ∀ c, c < rs.length → p.toBlockShape.recTgtAt c
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k := fun c hc =>
    (blockRecMajor_run (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  obtain ⟨hlhs, hihsWd1⟩ := hG
  -- the certificates, lifted past the chain: every lift is the identity
  have hcertsW : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j).length
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)
        (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j)
        ((blockRuleRbAV p rs mpC.base2.acval envC ψ c j).liftN rs.length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
            + (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).length))
        (blockRuleCaAV p rs mpC.base2.acval envC ψ c j) := by
    intro c hc j hj
    obtain ⟨e1, e2, e3⟩ := blockRuleCertsChain_eq hμ h hkLen hcore ψ hc hj rs.length
    rw [e3, e1, e2]
    exact hcertsB ψ c hc j hj
  -- the conclusion's reading, at the checked elimination level
  have hconclTy : ∀ xs : List V, ∀ c, c < rs.length →
      ∀ i, i ∈ˢ blockRecIs (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
          ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          p.toBlockShape.recTgtAt xs c →
      ∀ x, x ∈ˢ app (blockRecCr (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
          ψ ρ p.toBlockShape.recTgtAt xs c) i →
      interp V
          (consList (xs ++ (isOfW ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
              ppsOf).uM (p.toBlockShape.recTgtAt c) ψ)
            ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt
              (p.toBlockShape.recTgtAt c)) i ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim
          p.toBlockShape.large)) : V) := by
    intro xs c hc i hi x hx
    rw [← hℓeq ψ]
    exact blockRecConclTy_run hμ mpC h hmr hM helim hmemU hruns ψ ρ xs c hc i hi x hx
  have hbnd := blockRuleDoms_bounded_at hμ h hcore ψ
  -- the family
  let D := blockGraphFam (V := V) (μ := μ) (mo := mpC.base2) (names := names)
    (ℓ := Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
    (K := rs.length) (ψ := ψ) (ρ := ρ) (mem := p.toBlockShape.recTgtAt)
    (nCt := blockRecNCt rs) (rP := p.toBlockShape.rulePrefixAt)
    (rds := blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
    (concl := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
    (pdoms := blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
    (fdoms := blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
    (ihdoms := blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ)
    (Rb0 := blockRuleRbAV p rs mpC.base2.acval envC ψ)
    (Ca := fun c j => blockRuleCaAV p rs mpC.base2.acval envC ψ c j)
    (ihv := blockKitIhv p rs mpC.base2.acval envC ψ
      (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ)
    (call := blockGraphCall p rs mpC.base2.acval envC ψ
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ)
    (mp := mpC) (F := F) hμ hM hmemk
    (fun c hc => blockMembers_IdsM_length hmr (hmemk c hc) ψ)
    (blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ))
    (fun c _ => by rw [blockRulePdomsAV, List.map_take])
    hconclTy
    (blockRuleCertsK_run hμ h hkLen hdR' hN hS hcore hmr hM rs.length ψ)
    (blockKitSpF_run hμ h hkLen hcore hmr hM hN rfl hctM ψ hbnd ρ rs.length)
    (fun xs => blockGraphIhF_run hμ h hkLen hdR' hN hS hcore hmr hM ψ ρ xs (hconclTy xs))
    (blockWfCaB_run hμ h hkLen hcore hmr hM hN rfl hctM ψ ρ
      (fun xs c j fs g => blockKitIhv_length p rs mpC.base2.acval envC ψ _ _ ρ xs c j fs g))
    (fun xs => blockGraphUniq_run hμ h hdR' hN hS hcore hmr hM ψ ρ xs (hconclTy xs))
    (fun xs => blockGraphInd_run hμ h hkLen hdR' hN hS hcore hmr hM (mpC.lfp_ok _ hlfp).1 ψ ρ xs)
  rw [← blockRecEqs_base (V := V) (ihs := fun ψ' => blockRuleIhsRunAV p rs mpC.base2.acval envC ψ')
    (Rb0 := fun ψ' => blockRuleRbAV p rs mpC.base2.acval envC ψ') hμ mpC h ψ]
  refine ⟨hTy ψ ρ,
    hEq_iotaEqsAV_of (blockRecHwd_of_rules (mp := mpC) hμ hcertsW
      (blockGradeHokA_chain hμ h hkLen (blockRuleDoms_bounded_at hμ h hcore) hokG ψ ρ) (hlhs ψ ρ)
      (fun as hl ht c hc j hj ys hys => ⟨hihsWd1 ψ ρ as hl ht c hc j hj ys hys,
        blockRecIhsFit_chain hμ h hl hc (hihsFit ψ ρ as hl ht c hc j hj) ys hys⟩)),
    famCandG_hCand D (fun _ c j fs => (c, j, fs)) ?_ ?_ ?_ ?_ ?_ ?_⟩
  -- the recursor types are the binder data's Π-towers
  · exact fun c hc =>
      (checkBlockRecK_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hc)
        ψ).choose_spec.choose_spec.2.2.1
  -- one elimination level
  · have hb := blockRecOneElimLevel helim ψ hmemU (hbitsE ψ)
    rwa [hℓeq ψ] at hb
  · exact fun c hc => blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc) ψ
  -- the rule's spine fits the recursor's type
  · exact blockKitRule_run hμ h hkLen hcore hmr hM hN rfl hctM ψ rs.length _ ρ
  -- the rule's own fields are a decoding of the constructed major
  · intro c hc j hj xs fs hxl hsp
    obtain ⟨hChain, hmkv⟩ :=
      blockWfCtorAt_run hμ h hkLen hcore hmr hM hN rfl hctM ψ rs.length _ ρ c hc j hj xs fs hxl hsp
    have hfit := blockKitRule_run hμ h hkLen hcore hmr hM hN rfl hctM ψ rs.length _ ρ c hc j hj
      xs fs hxl hsp
    have hxr : xs.length = p.toBlockShape.rulePrefixAt c := by
      rw [hxl, blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc) ψ]
    obtain ⟨-, -, hi, -⟩ := D.hsplit c hc _ hfit
    rw [prefOf_split hxr, idxOf_split hxr] at hi
    refine ⟨hc, hj, _, hi, hChain, ?_⟩
    show tagged c _ _ = _
    rw [hmkv]
  -- the step at that decoding is the residue at the `ih` terms' values
  · intro c hc j hj xs fs hxl hsp
    have hlen : (xs ++ fs).length
        = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length := by
      rw [hsp.length_eq, List.length_append]
    have hchain := blockGraphIhChain_run hμ h hkLen hdR' hN hS hcore hmr hM ψ ρ (famCandG D) xs
      (fun v => (D.kit xs).recAt v)
      (fun c' hc' is x hxl' hsp' => (famCandG_fold D hc' hxl' hsp').symm) c hc j hj fs hxl hsp
    show interp V (consList (blockKitIhv p rs mpC.base2.acval envC ψ
        (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
        (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ xs c j fs
        (graph (fun v => (D.kit xs).recAt v)
          (blockGraphPred (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
            (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) p.toBlockShape.recTgtAt
            rs.length (blockGraphCall p rs mpC.base2.acval envC ψ
              (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ρ) xs (c, j, fs))))
        (consList (xs ++ fs) ρ)) (blockRuleRbAV p rs mpC.base2.acval envC ψ c j) = _
    rw [hchain,
      show (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
          + (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).length
        = (xs ++ fs).length + ((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame rs.length (famCandG D) ρ)))).length from by
        rw [hlen, List.length_map],
      interp_Rb_chain]

end Producer

end ConLeche.Model
