module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.BlockDatum
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.Inductives.BlockRecRun
public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun

public section

/-!
# The recursor model's seam facts at the run

`declBlock_data` (`BlockRecData.lean` §A.18) asks the recursor stage
for, among eight conjuncts, the family's premise

```
∀ ψ ρ, BlockRecPre V (s ψ) rs.length (blockRecTyAV …)
         (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ
```

which ONE producer supplies, `blockRecPre_graph`
(`BlockRecGraph.lean`).  This file holds the run facts it reads:

1. **The equation list** (§1–§2): the producer concludes at
   `iotaEqsAV` over the CHAIN-frame components; the endpoint asks for
   `blockRecEqs` over the BASE ones.  `blockRecEqs_base` is that
   identification (§20's `…K` definitions, §31's
   `iotaEqsAV_eq_blockIotaEqsAV`, §28's `pdoms` collapse).
2. **The counting guard** (§2.5): at a `Prop` block eliminating above
   `Prop`, the kernel's large-elimination guard leaves one member with
   at most one constructor, of the declared large shape
   (`blockRecCounting_run`) — the graph kit's `huniq` at `w = 0`.
3. **The seam facts** (§4): the recursor count, the rule counts, the
   rule frame's lifts, the grading's chain carries, the fields' fit,
   the fired spine at the rule's frame (`blockRuleDecoding_run` — the
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

/-! ## 1. THE CURRENCY — the producer's equations ARE the endpoint's

The producer parameterises the ι equations at their components AT THE
CHAIN FRAME (§20's `blockRecPdomsK`/`blockRecFdomsK`/`blockRecEsK`/
`blockRecMkK`); the endpoint states its premise at `blockRecEqs`,
`blockIotaEqsAV` over the BASE components.  The two are one term, and
only the residue's cutoff separates them — the producer writes the
LIFTED prefix and field lengths, `blockRecEqs` the unlifted ones, and
`liftDomsK_length` is a theorem, not `rfl`.  The identification is
§31's, at the four `…K` definitions, so the two sides meet at a NAMED
term. -/

section Currency

/-- **The producer's equation list IS `blockRecEqs`** at the run's own
components. -/
theorem blockRecEqs_runK {envC : Env} {acval : Name → (Name → Nat) → AnnotTerm}
    {q : ConLeche.BlockShape}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {nCt : Nat → Nat}
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm} (ψ : Name → Nat) :
    iotaEqsAV rs.length nCt
        (blockRecPdomsK rs.length acval envC q rs ψ)
        (blockRecFdomsK rs.length acval envC q rs ψ)
        (blockRecEsK rs.length acval envC q rs ψ)
        (blockRecMkK rs.length acval envC q rs ψ)
        (ihs ψ)
        (fun c j => (Rb0 ψ c j).liftN rs.length
          ((blockRecPdomsK rs.length acval envC q rs ψ c).length
            + (blockRecFdomsK rs.length acval envC q rs ψ c j).length + (ihs ψ c j).length))
      = blockRecEqs nCt rs
          (fun ψ' => blockRulePdomsAV acval envC q rs ψ')
          (fun ψ' => blockRuleFdomsAV q rs acval envC ψ')
          (fun ψ' => blockRuleEsAV q rs acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV q rs acval envC ψ')
          Rb0 ψ :=
  iotaEqsAV_eq_blockIotaEqsAV
    (pdoms0 := blockRulePdomsAV acval envC q rs ψ)
    (fdoms0 := blockRuleFdomsAV q rs acval envC ψ)
    (es0 := blockRuleEsAV q rs acval envC ψ)
    (mk0 := blockRuleMkAV q rs acval envC ψ)

end Currency


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

/-- **The endpoint's equation list, at the BASE prefix domains** — §1
through §28's collapse. -/
theorem blockRecEqs_base (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (ψ : Name → Nat) :
    iotaEqsAV rs.length (blockRecNCt rs)
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (ihs ψ)
        (fun c j => (Rb0 ψ c j).liftN rs.length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
            + (ihs ψ c j).length))
      = blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ')
          Rb0 ψ := by
  rw [← blockRecEqs_runK (acval := mpC.base2.acval) (envC := envC) (q := p.toBlockShape)
    (nCt := blockRecNCt rs) (ihs := ihs) (Rb0 := Rb0) ψ]
  refine iotaEqsAV_congr (fun c hc => ?_) (fun c hc j _ => ?_)
  · exact (blockRecPdomsK_run (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ rs.length).symm
  · rw [blockRecPdomsK_run (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ rs.length]

/-! ## 2.5 THE COUNTING GUARD AT THE RUN

At `w = 0, ℓ ≠ 0` the graph kit's `huniq` needs the decoding to be a
function of the major: one recursor, one member, at most one
constructor, of the declared large shape.  No model fact implies it:
it is what the kernel's COUNTING guard says.

`blockLargeElimAllowed`'s own arm is a RUN (`isDefEq` of the
conclusion's inferred type against `Sort 0`), and the model holds of a
conclusion only the LEVEL `ensureSort` returned — so the checker says
the counting half a second time, in the level currency
(`checkBlockRecSmallElim`, `Kernel/Inductives/BlockInstall.lean`): a
block of SEVERAL families whose result sort may be `0` eliminates only
at a level equivalent to zero.  `hruns` is `blockRecElimLevel_run`'s
package component, and the level is the CHECKED one
(`blockRecElimPin_run`). -/

section Count

omit [SetTheory V] in
/-- **THE COUNTING GUARD'S FOUR FACTS, AT THE RUN.**

At a block whose result sort evaluates to zero and whose recursors
eliminate at a non-zero level, the pass's disjunction collapses onto
`blockLargeElimAllowed`'s own verdict, and `blockLargeElim_counting`
reads all four facts off it.  The pass is stated as the GUARD rather
than as the one counting fact because the squash arm wants all four,
and a second derivation of `k = 1` in the level currency would be one
fact under two names.

The pass is what licenses the collapse.  Stage (b)'s own disjunction
(`RecTyEntry.hsmall`) is
`blockLargeElimAllowed … = true ∨ isDefEq sty (Sort 0) = .ok true`, and
its second arm is a RUN about a term, which the model cannot refute;
the pass says the same implication with `every level is zero` in that
slot, which it can. -/
theorem blockRecCounting_run
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0)
    (hw : Level.eval ψ p.toBlockShape.resSort = 0) :
    0 < rs.length ∧ rs.length = p.toBlockShape.k ∧
      p.toBlockShape.large = true ∧ p.toBlockShape.k = 1 ∧ p.toBlockShape.numCtors ≤ 1 := by
  obtain ⟨R⟩ := id h
  have hcase := R.fam.small
  have hklen : rs.length = p.toBlockShape.k := by
    rw [R.len, (ConLeche.recPins_names R.pinsOk).1]; rfl
  have hpos : 0 < rs.length := by rw [hklen]; exact R.fam.k_pos
  have humem := blockRecUOf_run R hruns hpos
  have hu0 : Level.eval ψ (uOf 0) ≠ 0 := by
    rw [blockRecElimPin_run h hruns ψ hpos]; exact hℓ
  have hallow : ConLeche.blockLargeElimAllowed p.toBlockShape
      false = true := by
    rcases hcase with hg | hzero
    · exact hg
    · exact absurd (ConLeche.Level.isEquiv_sound (hzero _ humem) ψ) hu0
  obtain ⟨hl, hk, -, hc⟩ := blockLargeElim_counting hallow hw
  exact ⟨hpos, hklen, hl, hk, hc⟩

/-- **A non-zero elimination level forces the DECLARED large shape** —
the antecedent the constructors' stage's subsingleton clause
(`CtorDataI.srcProp`, keyed on `p.large`) wants, and the squash arm
through it.

`blockRecCounting_run`'s FIRST fact is the same flag, and this is not
a second derivation of it: that one is the counting guard's reading and
needs the block's result sort to evaluate to zero, this one is the
elimination-level PIN's and needs nothing.  Keep both, and reach for
this one wherever the `Prop`-valued hypothesis is not in hand — at a
`Type` block the counting route says nothing and this one still does.

Neither goes through the type stage's `isDefEq sty (Sort 0)`: that run
is a verdict about a TERM and inverting it to a statement about a LEVEL
is an induction over the whole lazy-delta loop.  The pin says it
syntactically — `structElimLevel p.elim p.large` is `Level.zero` at
`large = false`, so a recursor that eliminates at a non-zero level
cannot have declared the small shape. -/
theorem blockRecLarge_run
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) (hne : Level.eval ψ (uOf c) ≠ 0) :
    p.toBlockShape.large = true := by
  cases hb : p.toBlockShape.large with
  | true => rfl
  | false =>
    refine absurd ?_ hne
    rw [blockRecElimPin_run h hruns ψ hc]
    simp [ConLeche.structElimLevel, hb, ConLeche.Level.eval]

end Count

end BaseEqs


/-! ## 4. THE SEAM FACTS

What `blockRecPre_graph` reads of the run besides its rows: the
recursor count, the constructor counts (`recStage_ctorsAt`), the
rule frame's field lengths and lifts, the certificates' and grading's
chain carries, the fields' fit at the rule's frame (`blockKitSpF_run`),
the rule's own decoding (`blockRuleDecoding_run`) and the family's level
`s` (`blockRecLevel_run`).  The ι equations' remaining grading inputs
are one bundle, `BlockGradeOwed`, in its producers' spellings. -/

section Seam

section SeamFacts

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

omit [SetTheory V] in
/-- **The family is non-empty and has one recursor per member** — the
pins and the counting pass's first clause. -/
theorem blockRecLen_run
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs) :
    0 < rs.length ∧ rs.length = p.toBlockShape.k := by
  obtain ⟨R⟩ := id h
  have hklen : rs.length = p.toBlockShape.k := by
    rw [R.len, (ConLeche.recPins_names R.pinsOk).1]; rfl
  exact ⟨by rw [hklen]; exact R.fam.k_pos, hklen⟩

omit [SetTheory V] in
/-- A member's constructors are among the block's. -/
theorem numCtorsOf_ge_of_mem {ms : ConLeche.MemberShape} :
    ∀ {l : List ConLeche.MemberShape}, ms ∈ l → ms.ctors.length ≤ ConLeche.numCtorsOf l
  | _ :: _, .head _ => by simp only [ConLeche.numCtorsOf]; omega
  | _ :: _, .tail _ h => by
    simp only [ConLeche.numCtorsOf]; have := numCtorsOf_ge_of_mem h; omega

/-- **The constructor counts at the seam**: at the run's own block data
a recursor's member carries exactly the recursor's rules. -/
theorem blockRecNCt_at {pk : Nat → BlockMemberPick}
    {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} (hm : memR c) (hc : c < rs.length) :
      ((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
          (p.toBlockShape.recTgtAt c)).length = blockRecNCt rs c ∧
        ((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
          (p.toBlockShape.recTgtAt c)).length ≤ p.toBlockShape.numCtors := by
  obtain ⟨ms, hms, hctA, hlenms⟩ := recStage_ctorsAt (hm := hm) h (List.getElem?_eq_getElem hc)
  have hctM : (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c) = rs[c].2.2.2 := by
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  refine ⟨?_, ?_⟩
  · rw [hctM, blockRecNCt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; rfl
  · rw [hctM, hlenms]
    exact numCtorsOf_ge_of_mem (List.mem_of_getElem? hms)

theorem blockRecNCt_seam {pk : Nat → BlockMemberPick}
    {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs) :
    ∀ c, c < rs.length →
      ((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
          (p.toBlockShape.recTgtAt c)).length = blockRecNCt rs c ∧
        ((blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
          (p.toBlockShape.recTgtAt c)).length ≤ p.toBlockShape.numCtors :=
  fun _ hc => blockRecNCt_at h trivial hc

end SeamFacts

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- The rule's field domains number the constructor's fields. -/
theorem blockRuleFdomsAV_length_run
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) (ψ : Name → Nat) :
    (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).length = cA.2 := by
  obtain ⟨_, _, _, _, _, _, -, -, h₂, -, -, -, -, -⟩ := blockRuleData_run (hm := hm) h hr hcA hrhs
  rw [blockRuleFdomsAV, readOpenedDoms_length_eq]
  exact openPisAtFvars_length _ h₂

/-- **The field domains' chain lift is the identity** — they are
bounded at their own depths (`hbnd`, `blockRuleDoms_bounded_at` at the
run's block datum). -/
theorem blockRecFdomsK_eq_of_bounded {ψ : Name → Nat} {c : Nat}
    (hbnd : ∀ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).length →
        Term.bvarsBelow l (((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD l
            default).erase))
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {j : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[j]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[j]? = some rhs) (K : Nat) :
    blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j
      = blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j := by
  rw [blockRecFdomsK]
  refine liftDomsK_eq_self_of_bounded _ _ fun l hl => ?_
  have hb := hbnd r hr j cA rhs hcA hrhs
    ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length + l)
    (by rw [List.length_append]; omega)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD] at hb

/-- **The field domains' chain lift is the identity** at every stored
rule: the rule's field domains are bounded by their own frame. -/
theorem blockRecFdomsK_eq_run (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf) p.lps cvTas
      p.toBlockShape isRec A
      (blockDataOf V p.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (ψ : Name → Nat) {c : Nat} (hm : memR c) (hc : c < rs.length) {j : Nat}
    (hj : j < blockRecNCt rs c) (K : Nat) :
    blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j
      = blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j := by
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩
  exact blockRecFdomsK_eq_of_bounded (blockRuleDoms_bounded_one hμ h hcore ψ c · hm) hr hcA hrhs K

/-- **The dispatch's `hokA`, from the rule frame's grading (G)** — its
prefix and field segments, at the chain frame (any frame will do: (G)
is stated at every one), the field domains' chain lift being the
identity. -/
theorem blockGradeHokA_chain (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hbnd : ∀ (ψ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).length →
        Term.bvarsBelow l (((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).getD l
            default).erase))
    (hG : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∀ l, l < p.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).getD l default)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length →
      ∀ ys : List V,
        SpineFit (consList as ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).take l)
          ys →
        WellDenoted V (consList ys (consList as ρ))
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).getD l
            default) := by
  intro ψ ρ as _ _ c hc j hj l hl ys hys
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩
  rw [blockRecFdomsK_eq_of_bounded (hbnd ψ _) hr hcA hrhs] at hl hys ⊢
  have hlP := blockRulePdomsAV_length hμ mpC h hr ψ
  have hlF := blockRuleFdomsAV_length_run (hm := trivial) (mpC := mpC) h hr hcA hrhs ψ
  have hq := hG c rs[c] hr j cA hcA ψ l
    (by rw [List.length_append, hlP, hlF] at hl; omega) (consList as ρ) ys hys
  exact hq.1

/-- **The graph kit's `hspF`, at the run** — at the base frame and at
any chain width `K`.
§24's bridge at `K = 0` (`blockRecSpF_base`) at the stored fit's field
spine, and the field domains' `K` lift the identity (they are bounded
at their own depths, `blockRuleDoms_bounded_at` — `hbnd`, whose one
producer is that theorem at the run's block datum). -/
theorem blockKitSpF_at (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      memR c → rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat)
    (hbnd : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      memR j → rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).length →
        Term.bvarsBelow l (((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).getD l
            default).erase))
    (ρ : Nat → V) (K : Nat) :
    ∀ xs : List V, ∀ c, c < rs.length → memR c →
      SpineFit ρ (d.params ψ) (xs.take d.nP) →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      ∀ j, j < blockRecNCt rs c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt c) →
      d.StoredFit ψ (consList (xs.take d.nP) ρ) i (p.toBlockShape.recTgtAt c) j fs →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
  intro xs c hc hm _ hpref j hj i fs _ hfit
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩
  have hcj : (d.ctorsM (p.toBlockShape.recTgtAt c))[j]? = some cA := by
    rw [hctM c _ hm hr]; exact hcA
  have hmemk : p.toBlockShape.recTgtAt c < d.k :=
    (blockRecMajor_run (hm := hm) (V := V) hμ mpC h hmr hr (fun _ => 0)).2.1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  have hnP := TE.nP_le
  have hfd := blockRuleFdomsAV_datum (hm := hm) h hr hcA hrhs hcore hmemk hcj hnP hdnP ψ
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hxs : xs.length = p.toBlockShape.rulePrefixAt c := by rw [hpref.length_eq, hpl]
  have hq := blockRecSpF_base (mem := p.toBlockShape.recTgtAt) hμ h hr hfd hxs hpref hfit.2.1
  rw [blockRecFdomsK_eq_of_bounded (hbnd c · hm) hr hcA hrhs K]
  exact hq

/-- `blockKitSpF_at` at every recursor (all majors members). -/
theorem blockKitSpF_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat)
    (hbnd : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).length →
        Term.bvarsBelow l (((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).getD l
            default).erase))
    (ρ : Nat → V) (K : Nat) :
    ∀ xs : List V, ∀ c, c < rs.length →
      SpineFit ρ (d.params ψ) (xs.take d.nP) →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      ∀ j, j < blockRecNCt rs c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt c) →
      d.StoredFit ψ (consList (xs.take d.nP) ρ) i (p.toBlockShape.recTgtAt c) j fs →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) :=
  fun xs c hc => blockKitSpF_at hμ h hcore hmr hdnP (fun c r _ hr => hctM c r hr) ψ
    (fun j r _ hr => hbnd j r hr) ρ K xs c hc trivial

/-- **The rule's own DECODING, at the run** — at ANY chain frame
(nothing here reads the candidate): the rule's fields fit its
constructor at the carrier, at the rule's index readings, and the
fired spine is the constructor's injection — the decoding the graph
producer's ι law reads `rec_eq` at.  The fit half is the peel's field
spine, the index half §26's `blockRecCtorIdx`, the fired spine §22's
`blockRecMkK_value`; `blockRuleSpine_peel` (`BlockKitRuleRun.lean`) hands all three their
inputs. -/
theorem blockRuleDecoding_at (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      memR c → rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) (K : Nat) (a ρ : Nat → V) :
    ∀ c, c < rs.length → memR c → ∀ j, j < blockRecNCt rs c →
      ∀ xs fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame K a ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) →
        d.StoredFit ψ (consList (xs.take d.nP) ρ)
            (d.tup ψ (p.toBlockShape.recTgtAt c)
              ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                (interp V (consList (xs ++ fs) (chainFrame K a ρ)))))
            (p.toBlockShape.recTgtAt c) j fs ∧
          interp V (consList (xs ++ fs) (chainFrame K a ρ))
              (blockRecMkK K mpC.base2.acval envC p.toBlockShape rs ψ c j)
            = d.inj ψ (p.toBlockShape.recTgtAt c) j fs := by
  intro c hc hm j hj xs fs hxs hsp
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfs, hnF, -, hps, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel (hm := hm) hμ h hcore hmr hdnP hctM (List.getElem?_eq_getElem hc) hj hxs hsp
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hmN : p.toBlockShape.recTgtAt c < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : j < (d.ctorsM (p.toBlockShape.recTgtAt c)).length :=
    (List.getElem?_eq_some_iff.mp hcj).1
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [hfd, liftDomsK_length, hnF]
  refine ⟨⟨hjl, hfb, ?_⟩, ?_⟩
  · exact blockRecCtorIdx (mem := p.toBlockShape.recTgtAt) hM hes hpl hfl hxs' hfs hmN hjl hps hfb
  · exact blockRecMkK_value (hm := hm) (mem := p.toBlockShape.recTgtAt) hM h hr hcA hrhs hcf.1
      (by rw [← hcf.2.1]; rfl) hnP hmN hcj ψ hxs' hfs
      (by rw [hpl, hfl, hxs', hfs]) (by rw [← hdnP]; exact hps) (by rw [← hdnP]; exact hfb)

/-- `blockRuleDecoding_at` at every recursor (all majors members). -/
theorem blockRuleDecoding_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) (K : Nat) (a ρ : Nat → V) :
    ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ xs fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame K a ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) →
        d.StoredFit ψ (consList (xs.take d.nP) ρ)
            (d.tup ψ (p.toBlockShape.recTgtAt c)
              ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                (interp V (consList (xs ++ fs) (chainFrame K a ρ)))))
            (p.toBlockShape.recTgtAt c) j fs ∧
          interp V (consList (xs ++ fs) (chainFrame K a ρ))
              (blockRecMkK K mpC.base2.acval envC p.toBlockShape rs ψ c j)
            = d.inj ψ (p.toBlockShape.recTgtAt c) j fs :=
  fun c hc => blockRuleDecoding_at hμ h hcore hmr hM hdnP (fun c r _ hr => hctM c r hr) ψ K a ρ
    c hc trivial

/-- **The family's level `s`, CHOSEN — with both facts it owes.**
`s` is the max of the check's inferred sorts (`blockRecTy_univ_run`)
read at the level assignment RESTRICTED to the family's level
parameters (zero elsewhere).  So `s`'s parametricity — `heqP`'s `s`
half, owed by whoever fixes `s` — is definitional: two assignments that
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
        rw [if_pos hqm, if_pos hqm]
        exact hq q (hl ▸ hqm)
      · show (if q ∈ lps then ψ₁ q else 0) = (if q ∈ lps then ψ₂ q else 0)
        rw [if_neg hqm, if_neg hqm]
    show maxLevelEval us (res ψ₁) = maxLevelEval us (res ψ₂)
    rw [hres]
  · have hr0 : rs[0]? = some (rs.getD 0 default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hext := blockRecTyAV_params_ext (V := V) hμ mpC h hr0 (ψ₁ := ψ) (ψ₂ := res ψ)
      (fun q hqm => by show ψ q = if q ∈ lps then ψ q else 0; rw [if_pos hqm]) hc
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
