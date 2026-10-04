module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.BlockDatum
import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.BlockRecRun
public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun

public section

/-!
# The recursor model's seam facts at the run

`declBlock` (`DeclBlockStep.lean`) asks the recursor stage for, among
its conjuncts, the family's premise

```
∀ ψ ρ, BlockRecPre V (s ψ) rs.length (blockRecTyAV …)
         (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ
```

which ONE producer supplies, `graphRecPre_core`
(`BlockRecGraph.lean`).  This file holds the run facts it reads:

1. **The equation list** (§2): the `pdoms` collapse from the
   CHAIN-frame components to the BASE ones, paid in the equation list
   (`iotaEqsAV_congr`).
2. **The counting guard** (§2.5): at a `Prop` block eliminating above
   `Prop`, the kernel's large-elimination guard leaves one member with
   at most one constructor, of the declared large shape
   (`blockRecCounting_run`) — the graph kit's `huniq` at `w = 0`.
3. **The seam facts** (§4): the recursor count, the rule counts, the
   rule frame's lifts, the grading's chain carries, the fields' fit,
   the fired spine at the rule's frame (`blockRuleDecoding_at` — the
   rule's own decoding), and the family's level `s`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 2. The equation list at the BASE prefix domains

§20 states the components at the CHAIN frame (`blockRecPdomsK` =
`liftDomsK K 0 ∘ blockRulePdomsAV`); the prefix domains are closed, so
their chain lift is the identity (§28's `blockRecPdomsK_run`), and the
collapse is paid ONCE, in the equation list, where `iotaEqsAV` is
exposed and a congruence is available. -/

section BaseEqs

omit [SetTheory V] in
/-- A `flatMap` congruence at the members — core has none. -/
theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (.head _),
      ih fun b hb => h b (.tail _ hb)]

omit [SetTheory V] in
/-- **The equation list depends on `pdoms` and the residue only BELOW
`K`** — the congruence the `pdoms` collapse is paid through. -/
theorem iotaEqsAV_congr {K : Nat} {nCt : Nat → Nat} {pdoms pdoms' : Nat → List AnnotTerm}
    {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
    {ihs : Nat → Nat → List AnnotTerm} {Rb Rb' : Nat → Nat → AnnotTerm}
    (hp : ∀ c, c < K → pdoms c = pdoms' c)
    (hRb : ∀ c, c < K → ∀ j, j < nCt c → Rb c j = Rb' c j) :
    iotaEqsAV K nCt pdoms fdoms es mk ihs Rb
      = iotaEqsAV K nCt pdoms' fdoms es mk ihs Rb' := by
  show (List.range K).flatMap _ = (List.range K).flatMap _
  refine flatMap_congr_mem fun c hc => ?_
  have hcK := List.mem_range.mp hc
  refine List.map_congr_left fun j hj => ?_
  rw [hp c hcK, hRb c hcK j (List.mem_range.mp hj)]

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {d : BlockData V} {s : (Name → Nat) → Nat} {us : List Level}
  {ihs ihdoms : (Name → Nat) → Nat → Nat → List AnnotTerm}
  {Rb0 Ca : (Name → Nat) → Nat → Nat → AnnotTerm} {uOf : Nat → Level}


end BaseEqs


/-! ## 4. THE SEAM FACTS

What `graphRecPre_core` reads of the run besides its rows: the
recursor count, the constructor counts (`recStage_ctorsAt`), the
rule frame's field lengths and lifts, the certificates' and grading's
chain carries, the fields' fit at the rule's frame (`blockKitSpF_at`),
the rule's own decoding (`blockRuleDecoding_at`) and the family's level
`s` (`blockRecLevel_run`). -/

section Seam

section SeamFacts

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

omit [SetTheory V] in
/-- A member's constructors are among the block's. -/
theorem numCtorsOf_ge_of_mem {ms : ConLeche.MemberShape} :
    ∀ {l : List ConLeche.MemberShape}, ms ∈ l → ms.ctors.length ≤ ConLeche.numCtorsOf l
  | _ :: _, .head _ => by simp only [ConLeche.numCtorsOf]; omega
  | _ :: _, .tail _ h => by
    simp only [ConLeche.numCtorsOf]; have := numCtorsOf_ge_of_mem h; omega

end SeamFacts

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **The family's level `s`, CHOSEN — with both facts it owes.**
`s` is the max of the check's inferred sorts (`blockRecTy_univ_run`)
read at the level assignment RESTRICTED to the family's level
parameters (zero elsewhere).  So `s`'s parametricity — `heqP`'s `s`
half — is definitional: two assignments that
agree on the family's parameters restrict to the same one.  The typing
`hTy` survives the restriction because the recursor types' READINGS are
themselves parametric (`blockRecTyAV_params_ext`: every recursor carries
the family's one parameter list).  No level-footprint fact about the
inferred sorts is needed. -/
theorem blockRecLevel_run (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR) :
    ∃ s : (Name → Nat) → Nat,
      (∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
        rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
        interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (s ψ) : V) ∧
          WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) := by
  obtain ⟨us, hus⟩ := blockRecTy_univ_run (V := V) hμ mpC h
  let lps := (rs.getD 0 default).1.levelParams
  let res : (Name → Nat) → Name → Nat := fun ψ q => if q ∈ lps then ψ q else 0
  refine ⟨fun ψ => maxLevelEval us (res ψ), fun i r hr ψ₁ ψ₂ hq => ?_, fun ψ ρ c hc => ?_⟩
  · have hi : i < rs.length := (List.getElem?_eq_some_iff.mp hr).1
    have hr0 : rs[0]? = some (rs.getD 0 default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hl : lps = r.1.levelParams := recStage_lps h hr0 hr
    have hres : res ψ₁ = res ψ₂ := by
      funext q
      by_cases hqm : q ∈ lps
      · show (if q ∈ lps then ψ₁ q else 0) = (if q ∈ lps then ψ₂ q else 0)
        rw [ite_eq_left hqm, ite_eq_left hqm]
        exact hq q (hl ▸ hqm)
      · show (if q ∈ lps then ψ₁ q else 0) = (if q ∈ lps then ψ₂ q else 0)
        rw [ite_eq_right hqm, ite_eq_right hqm]
    show maxLevelEval us (res ψ₁) = maxLevelEval us (res ψ₂)
    rw [hres]
  · have hr0 : rs[0]? = some (rs.getD 0 default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hext := blockRecTyAV_params_ext (V := V) hμ mpC h hr0 (ψ₁ := ψ) (ψ₂ := res ψ)
      (fun q hqm => by show ψ q = if q ∈ lps then ψ q else 0; rw [ite_eq_left hqm]) hc
    refine ⟨?_, (hus ψ c hc ρ).2⟩
    rw [hext]
    exact (hus (res ψ) c hc ρ).1

/-- A tuple of the family's length IS the chain frame's block. -/
theorem consList_eq_chainFrame {K : Nat} {tup : List V} (hlen : tup.length = K) (ρ : Nat → V) :
    consList tup ρ = chainFrame K (fun c => tup.getD c pt) ρ := by
  have hmap : (List.range K).map (fun c => tup.getD c pt) = tup := by
    refine List.ext_getElem? fun n => ?_
    rw [List.getElem?_map]
    by_cases hn : n < K
    · rw [List.getElem?_range hn, List.getElem?_eq_getElem (by omega : n < tup.length)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : n < tup.length)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
      rfl
  rw [chainFrame, hmap]

end Seam

end ConLeche.Model
