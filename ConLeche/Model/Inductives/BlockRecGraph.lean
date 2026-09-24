module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.BlockKitIhRun
import ConLeche.Semantics.Tower.BlockRecGraphI
public import ConLeche.Model.Inductives.BlockRuleCaRun
public import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRuleCertsRun
import ConLeche.Model.Inductives.BlockKitRuleRun
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
  the major.  A rule's own spine is one (`blockRuleDecoding_run`), at ANY
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
  function of the index (`blockStoredFit_srcVals_zero`).
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

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The kit's data at a block -/

section Data

/-- **The fit of a decoding, as a parameter** (lane RECLIB): the kit is
stated over a relation `fit xs c i j fs` — "the fields `fs` fit class
`c`'s constructor `j` at the index tuple `i`, at the prefix spine
`xs`, at the CARRIER".  The block's own instance is the STORED fit
(`blockStoredFitRel`) — at the carrier the hole fit is the stored fit
(`BlockModelAt.carrier`); the target check's is the lfp clause's HOLE
fit (`Target*`). -/
@[expose] def blockStoredFitRel (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (mem : Nat → Nat) (xs : List V) (c : Nat) (i : V) (j : Nat) (fs : List V) : Prop :=
  d.StoredFit ψ (consList (xs.take d.nP) ρ) i (mem c) j fs

/-- **A decoding at the prefix spine `xs`**, at a fit relation: `u` is
class `e.1`'s tagged element built by constructor `e.2.1` from the
fields `e.2.2`, which `fit` that constructor. -/
@[expose] def blockGraphDecF (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (pdoms : Nat → List AnnotTerm) (mem nCt : Nat → Nat) (K : Nat)
    (fit : List V → Nat → V → Nat → List V → Prop) (xs : List V) (u : V)
    (e : Nat × Nat × List V) : Prop :=
  e.1 < K ∧ e.2.1 < nCt e.1 ∧ ∃ i, i ∈ˢ blockRecIs d ψ ρ pdoms mem xs e.1 ∧
    fit xs e.1 i e.2.1 e.2.2 ∧ u = tagged e.1 i (d.inj ψ (mem e.1) e.2.1 e.2.2)

/-- **A decoding at the prefix spine `xs`**: `u` is class `e.1`'s
tagged element built by constructor `e.2.1` from the fields `e.2.2`,
which fit that constructor at the CARRIER. -/
@[expose] def blockGraphDec (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (pdoms : Nat → List AnnotTerm) (mem nCt : Nat → Nat) (K : Nat) (xs : List V) (u : V)
    (e : Nat × Nat × List V) : Prop :=
  blockGraphDecF d ψ ρ pdoms mem nCt K (blockStoredFitRel d ψ ρ mem) xs u e

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
noncomputable def blockGraphKitF (hμ : μ.verifiedChecks = true)
    (fit : List V → Nat → V → Nat → List V → Prop) (xs : List V)
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
      fit xs c i j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ c, c < K → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      fit xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ c, c < K → SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      fit xs c i j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs)))
    (huniq : ∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
      ∀ e e', blockGraphDecF d ψ ρ pdoms mem nCt K fit xs u e →
        blockGraphDecF d ψ ρ pdoms mem nCt K fit xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs u →
        v' ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs u →
        v = v')
    (hind : ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
        (∃ e, blockGraphDecF d ψ ρ pdoms mem nCt K fit xs u e ∧
          ∀ v, v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) → P u) :
    GraphRecKit ℓ (unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs))
      (Nat × Nat × List V) where
  Dec := blockGraphDecF d ψ ρ pdoms mem nCt K fit xs
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
readings (`blockRec_hsplit`, `blockRec_hconcl`). -/
noncomputable def blockGraphFamF (hμ : μ.verifiedChecks = true)
    (fit : List V → Nat → V → Nat → List V → Prop) (hM : BlockModelAt mo names d)
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
      fit xs c i j fs →
      SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs))
    (hihF : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      fit xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ)
          (fun c' => d.nIdxAt (mem c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < K →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (pdoms c) xs →
      ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c) →
      fit xs c i j fs → ∀ g : V,
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
        = blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs
            (tagged c i (d.inj ψ (mem c) j fs)))
    (huniq : ∀ xs : List V,
      ∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
      ∀ e e', blockGraphDecF d ψ ρ pdoms mem nCt K fit xs u e →
        blockGraphDecF d ψ ρ pdoms mem nCt K fit xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs u →
        v' ∈ˢ blockRecMot K concl (fun c' => d.uM (mem c') ψ) (fun c' => d.nIdxAt (mem c')) ρ xs u →
        v = v')
    (hind : ∀ xs : List V, ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) →
        (∃ e, blockGraphDecF d ψ ρ pdoms mem nCt K fit xs u e ∧
          ∀ v, v ∈ˢ blockGraphPred d ψ ρ pdoms mem K call xs e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet K (blockRecIs d ψ ρ pdoms mem xs) (blockRecCr d ψ ρ mem xs) → P u) :
    GraphFamData V ℓ K rP rds concl ρ (Nat × Nat × List V) where
  Is := blockRecIs d ψ ρ pdoms mem
  Cr := blockRecCr d ψ ρ mem
  tupOf := fun c is => d.tup ψ (mem c) is
  kit := fun xs => blockGraphKitF (Rb0 := Rb0) (Ca := Ca) (ihv := ihv) (call := call) hμ fit xs
    (hconclTy xs) hcerts (hspF xs) (hihF xs) (hCaB xs) (huniq xs) (hind xs)
  hsplit := blockRec_hsplit hM hpdE hmemK hsplitR
  hconcl := blockRec_hconcl hM
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

/-- **The rule's call targets** at a frame `σ` (the prefix and field
values over the base frame), at `ih` key data: per key `(q, c')` and
telescope spine `bs`, class `c'`'s tagged element at the call's index
readings and the applied field.  The key data are a parameter: today's
check's (`blockGraphCall`) or the target check's (`Target*`). -/
@[expose] def blockGraphCallAt (tup : Nat → List V → V) (keys : List (Nat × Nat))
    (tlA : Nat → List (Nat × Nat × AnnotTerm)) (eisA : Nat → List AnnotTerm)
    (fapA : Nat → AnnotTerm) (σ : Nat → V) (v : V) : Prop :=
  ∃ key ∈ keys, ∃ bs : List V,
    SpineFit σ ((tlA key.1).map (·.2.2)) bs ∧
    v = tagged key.2 (tup key.2 ((eisA key.1).map (interp V (consList bs σ))))
      (interp V (consList bs σ) (fapA key.1))

/-- **One opener's tower inhabits its Π-tower**, at EVERY level: at
`ℓ = 0` the opener's conclusion must read to a truth value. -/
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

/-! ## 4. `huniq` — the kernel's elimination guard, read three ways -/

/-- **The kit's `huniq`, PRODUCED**: at every major two decodings are
equal, or the bound is a subsingleton.

* `ℓ = 0`: the bound is a truth value (`hconclTy` at level `0`);
* `w ≠ 0`: the injection is injective (`mkInj`,
  `blockCarrier_case_unique`);
* `w = 0, ℓ ≠ 0`: the counting guard (`blockCountingGuard_run`) leaves one
  recursor of one member with at most one constructor, of the declared
  large shape, and the subsingleton criterion makes that constructor's
  fields a function of the INDEX (`blockStoredFit_srcVals_zero`). -/
theorem blockGraphUniq_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
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
  by_cases hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim
      p.toBlockShape.large) = 0
  · -- the bound is a truth value
    refine huniq_of_prop fun u hu => ?_
    have hmem := blockRecMot_mem_univ (K := rs.length) hconclTy _ hu
    rwa [hℓ] at hmem
  refine huniq_of_dec fun u _ e e' he he' => ?_
  obtain ⟨c, j, fs⟩ := e
  obtain ⟨c', j', fs'⟩ := e'
  obtain ⟨hc, hj, i, hi, hfit, rfl⟩ := he
  obtain ⟨-, hj', i', hi', hfit', heq⟩ := he'
  dsimp only [blockStoredFitRel] at hfit hfit'
  obtain ⟨rfl, rfl, hinj⟩ := tagged_inj heq
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
    obtain ⟨hK1, hmem0, hct1, hlarge⟩ := blockCountingGuard_run hμ h hmr ψ hℓ hw
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
        (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).StoredFit ψ
          (consList (xs.take (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP) ρ)
          i 0 0 gs →
        gs = srcVals (isOfW ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
            0 ψ) ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt 0) i)
          (srcList (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Ess
            0 ψ).getD 0 [])
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
              0 ψ).getD 0 []).length) := fun gs hgs =>
      blockStoredFit_srcVals_zero hM hcj ⟨hfindC, hlpsC, hcd⟩ hlarge hw
        (fun σ => ⟨fun hσ => ((hS.frames 0 hk0 0 cA hcj).1 ψ σ).mp
            (hS.paramsOf 0 hk0 ψ σ hσ 0 hk0),
          fun hσ => hS.paramsOf 0 hk0 ψ σ (((hS.frames 0 hk0 0 cA hcj).1 ψ σ).mpr hσ) 0 hk0⟩)
        (blockMembers_IdsM_length hmr hk0 ψ) hparFit
        (Nat.lt_of_lt_of_le hk0 (Nat.le_add_right _ _)) hi hgs
    rw [hsrc fs hfit, hsrc fs' hfit']
  · -- `mkInj`
    obtain ⟨rfl, rfl⟩ := blockCarrier_case_unique hM hw hmN hfit hfit' hinj
    rfl

/-! ## 5. The induction — from the block's recorded LFP CLAUSE -/

end Rows

/-! ## 6. THE PRODUCER — the endpoint's regime premise from the graph kit -/

section Producer

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

set_option maxHeartbeats 2000000 in
/-- **THE RECURSOR MODEL, at any rule data** — the graph family at the
rule data `ihs`/`Rb0` of some recursor check, its `ih` openers'
domains `ihdoms`, conclusion `Ca`, graph-built `ih` values `ihv`, call
targets `call` and decoding fit `fit`, handed to `famCandG_hCand`.  The
rule data's own facts are premises (the kit's rows: `hcertsG`, `hihFG`,
`hCaBG`, the induction `hindG`, the `ih` chain `hchainG`, the
equations' grading `hEqG`); what the rule data do not touch — the
recursor types, the elimination level, the rule prefix, the fields'
fit and the decodings' uniqueness — is today's run's, through the fit's
two translations to today's slot fit (`hfitC`, `hCfit`).  Today's
producer (`blockRecPre_graph`) is this at today's data; the target
check's (`Model/Inductives/TargetGraph.lean`) at the target's. -/
theorem blockRecPre_graph_gen (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    {s : (Name → Nat) → Nat}
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (s ψ) : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c))
    -- the rule data
    (ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm)
    (ihdoms : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (Ca : (Name → Nat) → Nat → Nat → AnnotTerm)
    (ihv : (Name → Nat) → (Nat → V) → List V → Nat → Nat → List V → V → List V)
    (call : (Name → Nat) → (Nat → V) → List V → Nat → Nat → List V → V → Prop)
    (fit : (Name → Nat) → (Nat → V) → List V → Nat → V → Nat → List V → Prop)
    -- the fit, against today's slot fit
    (hfitC : ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) (c : Nat) (i : V) (j : Nat)
      (fs : List V), c < rs.length → SpineFit ρ (d.params ψ) (xs.take d.nP) →
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt c) →
      fit ψ ρ xs c i j fs → blockStoredFitRel d ψ ρ p.toBlockShape.recTgtAt xs c i j fs)
    (hCfit : ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) (c : Nat) (i : V) (j : Nat)
      (fs : List V), c < rs.length → j < blockRecNCt rs c →
      SpineFit ρ (d.params ψ) (xs.take d.nP) →
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt c) →
      blockStoredFitRel d ψ ρ p.toBlockShape.recTgtAt xs c i j fs → fit ψ ρ xs c i j fs)
    -- the rows
    (hEqG : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ c, c < rs.length →
        tup.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ e ∈ blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ') Rb0 ψ,
        interp V (consList tup ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList tup ρ) e)
    (hcertsG : ∀ (ψ : Name → Nat), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        (ihdoms ψ c j).length
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)
        (ihdoms ψ c j) (Rb0 ψ c j) (Ca ψ c j))
    (hihFG : ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V), ∀ c, c < rs.length →
      SpineFit ρ (d.params ψ) (xs.take d.nP) →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      ∀ j, j < blockRecNCt rs c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt c) →
      fit ψ ρ xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockGraphPred d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          p.toBlockShape.recTgtAt rs.length (call ψ ρ) xs (c, j, fs) →
        app g v ∈ˢ blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs
          ψ) (fun c' => d.uM (p.toBlockShape.recTgtAt c') ψ)
          (fun c' => d.nIdxAt (p.toBlockShape.recTgtAt c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (ihdoms ψ c j) (ihv ψ ρ xs c j fs g))
    (hCaBG : ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V), ∀ c, c < rs.length →
      SpineFit ρ (d.params ψ) (xs.take d.nP) →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      ∀ j, j < blockRecNCt rs c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt c) →
      fit ψ ρ xs c i j fs → ∀ g : V,
      interp V (consList (ihv ψ ρ xs c j fs g) (consList (xs ++ fs) ρ)) (Ca ψ c j)
        = blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
            (fun c' => d.uM (p.toBlockShape.recTgtAt c') ψ)
            (fun c' => d.nIdxAt (p.toBlockShape.recTgtAt c')) ρ xs
            (tagged c i (d.inj ψ (p.toBlockShape.recTgtAt c) j fs)))
    (hindG : ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V), ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet rs.length
          (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt xs)
          (blockRecCr d ψ ρ p.toBlockShape.recTgtAt xs) →
        (∃ e, blockGraphDecF d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecNCt rs) rs.length (fit ψ ρ) xs u e ∧
          ∀ v, v ∈ˢ blockGraphPred d ψ ρ
              (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
              p.toBlockShape.recTgtAt rs.length (call ψ ρ) xs e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet rs.length
          (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt xs)
          (blockRecCr d ψ ρ p.toBlockShape.recTgtAt xs) → P u)
    (hchainG : ∀ (ψ : Name → Nat) (ρ : Nat → V) (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < rs.length → ∀ (is : List V) (x : V),
        xs.length = p.toBlockShape.rulePrefixAt c' →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2))
          (xs ++ (is ++ [x])) →
        r (tagged c' (d.tup ψ (p.toBlockShape.recTgtAt c') is) x)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c → ∀ fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame rs.length a ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) →
        ihv ψ ρ xs c j fs
            (graph r (blockGraphPred d ψ ρ
              (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
              p.toBlockShape.recTgtAt rs.length (call ψ ρ) xs (c, j, fs)))
          = (ihs ψ c j).map (interp V (consList (xs ++ fs) (chainFrame rs.length a ρ)))) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ')
          Rb0 ψ) ρ := by
  intro ψ ρ
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  obtain ⟨uOf, hbitsE, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hmemk : ∀ c, c < rs.length → p.toBlockShape.recTgtAt c
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k := fun c hc =>
    (blockRecMajor_run (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := recStage_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
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
    exact blockRecConclTy_run hμ mpC h hmr hM hruns ψ ρ
  have hbnd := blockRuleDoms_bounded_at hμ h hcore ψ
  -- the decodings' uniqueness, today's (the fit translated)
  have huniq : ∀ xs : List V,
      ∀ u, u ∈ˢ unionSet rs.length
        (blockRecIs (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) p.toBlockShape.recTgtAt xs)
        (blockRecCr (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
          p.toBlockShape.recTgtAt xs) →
      ∀ e e', blockGraphDecF (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) p.toBlockShape.recTgtAt
          (blockRecNCt rs) rs.length (fit ψ ρ) xs u e →
        blockGraphDecF (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) p.toBlockShape.recTgtAt
          (blockRecNCt rs) rs.length (fit ψ ρ) xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
          (fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
            (p.toBlockShape.recTgtAt c') ψ)
          (fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt
            (p.toBlockShape.recTgtAt c')) ρ xs u →
        v' ∈ˢ blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
          (fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).uM
            (p.toBlockShape.recTgtAt c') ψ)
          (fun c' => (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt
            (p.toBlockShape.recTgtAt c')) ρ xs u →
        v = v' := by
    intro xs u hu e e' he he'
    have hconv : ∀ {e : Nat × Nat × List V},
        blockGraphDecF (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) p.toBlockShape.recTgtAt
          (blockRecNCt rs) rs.length (fit ψ ρ) xs u e →
        blockGraphDec (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) p.toBlockShape.recTgtAt
          (blockRecNCt rs) rs.length xs u e := by
      intro e he
      obtain ⟨hc, hj, i, hi, hf, hu⟩ := he
      have hi' := hi
      obtain ⟨hpar, hpref⟩ := blockRecIs_fits hi'
      rw [blockRecIs_pos hpar hpref] at hi'
      exact ⟨hc, hj, i, hi, hfitC ψ ρ xs e.1 i e.2.1 e.2.2 hc hpar hi' hf, hu⟩
    exact blockGraphUniq_run hμ h hdR' hN hS hcore hmr hM ψ ρ xs (hconclTy xs) u hu e e'
      (hconv he) (hconv he')
  -- the family
  let D := blockGraphFamF (V := V) (μ := μ) (mo := mpC.base2) (names := names)
    (ℓ := Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
    (K := rs.length) (ψ := ψ) (ρ := ρ) (mem := p.toBlockShape.recTgtAt)
    (nCt := blockRecNCt rs) (rP := p.toBlockShape.rulePrefixAt)
    (rds := blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
    (concl := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
    (pdoms := blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
    (fdoms := blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
    (ihdoms := ihdoms ψ) (Rb0 := Rb0 ψ) (Ca := Ca ψ) (ihv := ihv ψ ρ) (call := call ψ ρ)
    (mp := mpC) (F := F) hμ (fit ψ ρ) hM hmemk
    (fun c hc => blockMembers_IdsM_length hmr (hmemk c hc) ψ)
    (blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ))
    (fun c _ => by rw [blockRulePdomsAV, List.map_take])
    hconclTy (hcertsG ψ)
    (fun xs c hc hpar hpref j hj i fs hi hf =>
      blockKitSpF_run hμ h hcore hmr rfl hctM ψ hbnd ρ rs.length xs c hc
        hpar hpref j hj i fs hi (hfitC ψ ρ xs c i j fs hc hpar hi hf))
    (hihFG ψ ρ) (hCaBG ψ ρ) huniq (hindG ψ ρ)
  refine ⟨hTy ψ ρ, hEqG ψ ρ, ?_⟩
  rw [← blockRecEqs_base (V := V) (ihs := ihs) (Rb0 := Rb0) hμ mpC h ψ]
  refine famCandG_hCand D (fun _ c j fs => (c, j, fs)) ?_ ?_ ?_ ?_ ?_ ?_
  -- the recursor types are the binder data's Π-towers
  · exact fun c hc =>
      (recStage_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hc)
        ψ).choose_spec.choose_spec.2.2.1
  -- one elimination level
  · exact blockRecOneElimLevel ψ (fun c hc => blockRecElimPin_run h hruns ψ hc) (hbitsE ψ)
  · exact fun c hc => blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc) ψ
  -- the rule's spine fits the recursor's type
  · exact blockKitRule_run hμ h hcore hmr hM rfl hctM ψ rs.length _ ρ
  -- the rule's own fields are a decoding of the constructed major
  · intro c hc j hj xs fs hxl hsp
    obtain ⟨hChain, hmkv⟩ :=
      blockRuleDecoding_run hμ h hcore hmr hM rfl hctM ψ rs.length _ ρ c hc j hj xs fs hxl hsp
    have hfit := blockKitRule_run hμ h hcore hmr hM rfl hctM ψ rs.length _ ρ c hc j hj
      xs fs hxl hsp
    have hxr : xs.length = p.toBlockShape.rulePrefixAt c := by
      rw [hxl, blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc) ψ]
    obtain ⟨-, -, hi, -⟩ := D.hsplit c hc _ hfit
    rw [prefOf_split hxr, idxOf_split hxr] at hi
    obtain ⟨hpar, hpref⟩ := blockRecIs_fits hi
    have hi' : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tup ψ
          (p.toBlockShape.recTgtAt c)
          ((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame rs.length (famCandG D) ρ))))
        ∈ˢ (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).idx ψ
          (consList (xs.take (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
            ppsOf).nP) ρ) (p.toBlockShape.recTgtAt c) := by
      rw [← blockRecIs_pos hpar hpref]; exact hi
    refine ⟨hc, hj, _, hi, hCfit ψ ρ xs c _ j fs hc hj hpar hi' hChain, ?_⟩
    show tagged c _ _ = _
    rw [hmkv]
  -- the step at that decoding is the residue at the `ih` terms' values
  · intro c hc j hj xs fs hxl hsp
    have hlen : (xs ++ fs).length
        = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length := by
      rw [hsp.length_eq, List.length_append]
    have hchain := hchainG ψ ρ (famCandG D) xs (fun v => (D.kit xs).recAt v)
      (fun c' hc' is x hxl' hsp' => (famCandG_fold D hc' hxl' hsp').symm) c hc j hj fs hxl hsp
    show interp V (consList (ihv ψ ρ xs c j fs
        (graph (fun v => (D.kit xs).recAt v)
          (blockGraphPred (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) ψ ρ
            (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) p.toBlockShape.recTgtAt
            rs.length (call ψ ρ) xs (c, j, fs))))
        (consList (xs ++ fs) ρ)) (Rb0 ψ c j) = _
    rw [hchain,
      show (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
          + (ihs ψ c j).length
        = (xs ++ fs).length + ((ihs ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame rs.length (famCandG D) ρ)))).length from by
        rw [hlen, List.length_map],
      interp_Rb_chain]

end Producer

end ConLeche.Model
