module

public import ConLeche.Model.Inductives.TargetRank
public import ConLeche.Verify.Inductives.RecSccK
import ConLeche.Verify.Inductives.RecCallGraph

public section

/-!
# The class induction, component by component (PRIMREC / NESTKN-RP)

`tgtClassInd_of_route` (`TargetFlatInd.lean`) orders the recursor classes by RANK
layers and asks every layer's elements for derivations along the calls inside the
LAYER.  The nested route (`Kernel/Inductives/RecNestK.lean`) classifies calls per
STRONGLY CONNECTED COMPONENT (`hotRK`; NESTKN-R's finding: one rank may hold several
components, `corner_nestind_unreached_mates`), so its completeness facts are
derivations along the calls inside a COMPONENT.  This module assembles those:

* `graphInd_of_comps` — generic: ranks never climb along a call, and a call that keeps
  the rank level stays inside the caller's component; then derivations along the calls
  inside each class's own component give the induction over all classes;
* `tgtClassInd_of_comps` — at the target check's classes: the component is mutual
  reachability in the family's call graph (`GReach`, `RecSccK.lean`), the rank is
  `graphRank`, and the level-rank edges are component edges (`graphRank_edge_back`).

The per-component derivations are the completeness lemmas' (a cold component: its flat
home's lfp induction, `tgtFlat_der` restated per component; a hot one: the node lemma of
the nested route).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor GReach)

universe w

variable {V : Type w} [SetTheory V]

section Comps

variable {Is Cr : List V → Nat → V} {injX : Nat → Nat → List V → V} {nCt : Nat → Nat}
  {K : Nat} {fit : List V → Nat → V → Nat → List V → Prop}
  {call : List V → Nat → Nat → List V → V → Prop}

/-- **The induction over the classes, from derivations along each component's calls**:
the rank `r` never climbs along a call and a call keeping it level stays in the caller's
component (`hdown`); components are transitive and within one rank; every element of
every class has a derivation along the calls inside its class's component (`hcomp`). -/
theorem graphInd_of_comps {r : Nat → Nat} {S : Nat → Nat → Prop}
    (hSr : ∀ c c', S c c' → r c' = r c)
    (hStrans : ∀ a b c, S a b → S b c → S a c)
    (hdown : ∀ xs c, c < K → ∀ j, j < nCt c → ∀ fs c' t y,
      call xs c j fs (tagged c' t y) → r c' ≤ r c ∧ (r c' = r c → S c c'))
    (hcomp : ∀ xs c, c < K → ∀ t, t ∈ˢ Is xs c → ∀ y, y ∈ˢ app (Cr xs c) t →
      Der (Is := Is) (Cr := Cr) (injX := injX) (nCt := nCt) (K := K) (fit := fit)
        (call := call) xs (S c) (tagged c t y)) :
    ∀ xs P, GraphClosed Is Cr injX nCt K fit call xs P →
      ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) → P u := by
  refine graphInd_of_layers (r := r) fun n => ?_
  intro xs P hP hlow c₀ hc₀ hrc₀ t₀ ht₀ y₀ hy₀
  suffices hall : ∀ u, Der (Is := Is) (Cr := Cr) (injX := injX) (nCt := nCt) (K := K)
      (fit := fit) (call := call) xs (S c₀) u → P u from
    hall _ (hcomp xs c₀ hc₀ t₀ ht₀ y₀ hy₀)
  intro u hD
  induction hD with
  | @mk c t j fs hc hS ht hy hj hf _ ih =>
    refine hP _ (tagged_mem_unionSet hc ht hy)
      ⟨(c, j, fs), ⟨hc, hj, t, ht, hf, rfl⟩, fun v hv => ?_⟩
    obtain ⟨hvU, hcv⟩ := mem_graphPredG.mp hv
    obtain ⟨c', hc', t', ht', y', hy', rfl⟩ := mem_unionSet.mp hvU
    obtain ⟨hle, hlev⟩ := hdown xs c hc j hj fs c' t' y' hcv
    have hrc : r c = n := (hSr c₀ c hS).trans hrc₀
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hlow c' hc' (by omega) t' ht' y' hy'
    · exact ih c' t' y' (hStrans _ _ _ hS (hlev heq)) ht' hy' hcv

end Comps

/-! ## At the target check's classes -/

section Target

/-- **A class's component** in the family's call graph: mutual reachability. -/
@[expose] def tgtComp (p : BlockShape) (c c' : Nat) : Prop :=
  GReach (ConLeche.targetGraphOf p) c c' ∧ GReach (ConLeche.targetGraphOf p) c' c

theorem tgtComp_refl (p : BlockShape) (c : Nat) : tgtComp p c c := ⟨.refl c, .refl c⟩

theorem tgtComp_trans {p : BlockShape} {a b c : Nat} (h₁ : tgtComp p a b)
    (h₂ : tgtComp p b c) : tgtComp p a c :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem tgtComp_symm {p : BlockShape} {a b : Nat} (h : tgtComp p a b) : tgtComp p b a :=
  ⟨h.2, h.1⟩

/-- Classes of one component share their rank. -/
theorem tgtComp_rank {p : BlockShape} {c c' : Nat} (h : tgtComp p c c') :
    tgtRank p c' = tgtRank p c :=
  ConLeche.graphRank_comp_eq h.1 h.2

variable {μ : CheckMode} {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

/-- **A call never climbs the rank, and a call keeping it level stays in the caller's
component**: a recognised call is an edge of the family's call graph
(`tgtCallee_edge`), and a level edge has a path back (`graphRank_edge_back`). -/
theorem tgtCall_comp
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {acval : Name → (Name → Nat) → AnnotTerm} {ψ : Name → Nat} {tup : Nat → List V → V}
    {ρ : Nat → V} {xs : List V} {c : Nat} (hc : c < (tgtRs out).length) {j : Nat}
    (hj : j < blockRecNCt (tgtRs out) c) {fs : List V} {c' : Nat} {t y : V}
    (hcall : tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out acval envC ψ
      tup ρ xs c j fs (tagged c' t y)) :
    tgtRank pp.toBlockShape c' ≤ tgtRank pp.toBlockShape c ∧
      (tgtRank pp.toBlockShape c' = tgtRank pp.toBlockShape c → tgtComp pp.toBlockShape c c') := by
  obtain ⟨hcg, hcg', he⟩ := tgtCallee_edge h R hc hj (tgtCall_callee hcall)
  refine ⟨ConLeche.graphRank_mono hcg hcg' he, fun heq => ⟨GReach.edge he, ?_⟩⟩
  exact ConLeche.graphRank_edge_back hcg hcg' he heq

/-- **`TgtClassInd`, component by component**: every element of every class has a
derivation along the calls inside its class's component (`hcomp` — the completeness
lemmas: a cold component's flat home, a hot component's nested route). -/
theorem tgtClassInd_of_comps
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (ψ : Name → Nat) (ρ : Nat → V)
    (hcomp : ∀ xs c, c < (tgtRs out).length →
      ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      ∀ y, y ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) t →
        Der (Is := tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (Cr := tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (injX := tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (nCt := blockRecNCt (tgtRs out))
          (K := (tgtRs out).length)
          (fit := tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (call := tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ)
          xs (tgtComp pp.toBlockShape c) (tagged c t y)) :
    TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape (cvTas.map (·.type)) out d Dc mc cvc
      ψ ρ :=
  graphInd_of_comps (r := tgtRank pp.toBlockShape) (S := tgtComp pp.toBlockShape)
    (fun _ _ hS => tgtComp_rank hS) (fun _ _ _ => tgtComp_trans)
    (fun _ _ hc _ hj _ _ _ _ hcall => tgtCall_comp h R hc hj hcall) hcomp

end Target

end ConLeche.Model
