module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Model.Inductives.BlockRuleParams
import ConLeche.Model.Capstone
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRuleCertsRun
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Inductives.BlockKitIhRun
import ConLeche.Model.Inductives.BlockRecGraph
import ConLeche.Model.Inductives.BlockModelRecords

public section

/-!
# The recursor stage at the run — pieces of the composition (task #315)

The block step's recursors' stage (`nestedRecStage`, `DeclBlockStep.lean`)
reads these; the dispatch (`BlockRecPreHpre.lean`) and the rule contract
(`BlockRuleFit.lean`) produce the two largest of its obligations.  This
file holds the pieces of the stage that read the run directly.

## 1. The `ℓ = 0` arm's LEFT side

The endpoint's `ℓ = 0` arm (`blockRuleRhsOk_base`) asks for two facts:
the stored rule reads as the point (`blockRuleRaZ_seam`, §1b) and the
recursor's TYPE is a truth value.  The second is
here, because it needs the elimination-level package
(`blockRecElimLevel_run`) and the level PIN (`blockRecElimPin_run`),
both downstream of the endpoint's file: the type's binder bits follow
its conclusion's inferred sort, the pin equates that sort with the
checked elimination level `structElimLevel p.elim p.large`, and a
Π-tower whose head bit is `0` is a truth value. -/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}
  {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}

section TyZero

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **THE `ℓ = 0` ARM'S LEFT SIDE**: at a valuation where the checked
elimination level is zero, every recursor's type reads as a truth
value — so the recursor's value is the point, and so is every
application of it.  `FixKit.lean`'s `hRpt`, at the block route. -/
theorem blockRecTyZ_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR) :
    ∀ j, j < rs.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ j) ∈ˢ (univZero : V) := by
  intro j hj ψ ρ hℓ
  obtain ⟨uOf, hbits, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hu : (uOf j).eval ψ = 0 := by
    have := blockRecElimPin_run h hruns ψ hj
    rw [hℓ] at this
    exact this
  obtain ⟨-, -, -, -, heq, hlen, -⟩ :=
    recStage_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hj) ψ
  rw [heq]
  cases hrds : blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ j with
  | nil => rw [hrds] at hlen; exact absurd hlen (by simp)
  | cons d rest =>
    have hd : d.2.1 = 0 :=
      (hbits ψ j hj d (by rw [hrds]; exact List.mem_cons_self)).mpr hu
    show interp V ρ (.pi d.1 d.2.1 d.2.2 _) ∈ˢ _
    rw [interp_pi, hd]
    exact piR_zero_mem_univZero

end TyZero

/-! ## 1b. `BlockMembersRun` at the seam

The recursor model and the recursor type's split take the block's
members' run facts as ONE record, `BlockMembersRun`
(`BlockRecTyShapeRun.lean`).  At the run's own
block data (`blockDataOf`, which the seam hands) it is the
constructors' three records read member by member: the names and the
count off `BlockNamesOk`, the former's storage, reading and leaf off
`BlockCtorsCore`, the leaf's λ-shape and the parameter agreement off
`BlockCtorsStage`, the former's closedness off the environment's
well-formedness. -/

section MembersRun

variable {envC envI : Env} {pp : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {mpC : EnvModelM V μ envC} {F : Nat}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
 
  {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}

/-- **`BlockMembersRun` from the constructors' three records**, at the
run's own block data. -/
theorem blockMembersRun_seam
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k) :
    BlockMembersRun mpC.base2
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.toBlockShape
      cvTas := by
  obtain ⟨hname, -, hlen⟩ := hN
  refine ⟨rfl, rfl, hlen, ?_, ?_, ?_, ?_⟩
  · intro m cvTb hcv
    have hm : m < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hcv).1
    obtain ⟨hfind, -, -, hFD⟩ := hcore.1 m cvTb hcv
    have hwf := mpC.base2.wf _ (List.mem_of_find?_eq_some hfind)
    exact ⟨hname m cvTb hcv, hS.lpsT m cvTb hm hcv, ⟨_, hfind⟩, hwf.1, hwf.2.2.2.1, hFD⟩
  · intro m ms hms
    have hm : m < pp.toBlockShape.members.length := (List.getElem?_eq_some_iff.mp hms).1
    have hg : pp.toBlockShape.members.getD m default = ms := by
      rw [List.getD_eq_getElem?_getD, hms]; rfl
    refine ⟨?_, ?_⟩
    · show (pp.toBlockShape.members.map (·.cvT.name)).getD m .anonymous = ms.cvT.name
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hms]; rfl
    · show pp.toBlockShape.nIdxs.getD m 0 = ms.nIdx
      rw [blockNIdxs_getD hm, hg]
  · intro m ψ hm
    obtain ⟨cvTb, hcv⟩ : ∃ cvTb, cvTas[m]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hm)⟩
    obtain ⟨-, -, hleaf, -⟩ := hcore.1 m cvTb hcv
    rw [hname m cvTb hcv, hleaf ψ, hS.leaf m ψ]
    exact ⟨_, rfl⟩
  · intro m hm ψ ρ
    have h0 : 0 < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) hm
    exact ⟨fun h => hS.paramsOf m hm ψ ρ h 0 h0, fun h => hS.paramsOf 0 h0 ψ ρ h m hm⟩

/-- **The block's representation at the seam** — `blockModelAt_of_records`
with its four identifications `rfl` at the run's own block data, and
`0 < k` off the counting pass's first clause. -/
theorem blockModelAt_seam
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hlfp : (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).toLfp
      ∈ mpC.lfpBlocks) :
    BlockModelAt mpC.base2
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).memberNames
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) := by
  obtain ⟨R⟩ := id h
  -- the operator's monotonicity is the recorded clause's (lane HOLE2: the
  -- install derived it from positivity when it recorded the clause)
  exact blockModelAt_of_records hN hS hcore rfl R.fam.k_pos (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun ψ ρp hs => ((mpC.lfpClause_of_mem hlfp).functor ψ ρp hs).1)
    (mpC.lfpClause_of_mem hlfp).fitsMono

/-- **The seam's canonical constructor-type reading**: the stored type
of recursor `j`'s `i`-th constructor, read at the constructors'
environment.  `blockRecCtor_seam` shows the reading is never the
default for a constructor a recursor carries. -/
@[expose] noncomputable def blockRecCtorTy (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) (j i : Nat)
    (ψ : Name → Nat) : AnnotTerm :=
  (denoteMeta acval envC ψ 0 ((rs.getD j default).2.2.2.getD i default).1.type).getD default


omit [SetTheory V] in
/-- A field chain whose entries are bounded one by one is bounded. -/
theorem fieldsBelow_of_getD :
    ∀ {m : Nat} {Fs : List AnnotTerm},
      (∀ q, q < Fs.length → Term.bvarsBelow (m + q) (Fs.getD q default).erase) →
      FieldsBelow m Fs
  | _, [], _ => trivial
  | m, _ :: Fs, h => by
    refine ⟨by simpa using h 0 (by simp), fieldsBelow_of_getD (m := m + 1) (Fs := Fs)
      fun q hq => ?_⟩
    have := h (q + 1) (by simpa using hq)
    simpa [show m + (q + 1) = m + 1 + q from by omega] using this

/-- **`heqB` from the rows** (any majors): every equation is bound below
the family once every rule's components are bound by their frames; the
prefix is the recursor type's (`blockRulePdomsAV_bounded`). -/
theorem blockRecEqs_below_rows (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR)
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hrow : ∀ (ψ : Name → Nat) (c : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs →
        FieldsBelow (pp.toBlockShape.rulePrefixAt c) (fdoms0 ψ c j) ∧
        (∀ e ∈ es0 ψ c j, Term.bvarsBelow
          (pp.toBlockShape.rulePrefixAt c + (fdoms0 ψ c j).length) e.erase) ∧
        Term.bvarsBelow (pp.toBlockShape.rulePrefixAt c + (fdoms0 ψ c j).length)
          (mk0 ψ c j).erase ∧
        (∀ v ∈ ihs ψ c j, Term.bvarsBelow
          (rs.length + pp.toBlockShape.rulePrefixAt c + (fdoms0 ψ c j).length) v.erase) ∧
        Term.bvarsBelow (pp.toBlockShape.rulePrefixAt c + (fdoms0 ψ c j).length
          + (ihs ψ c j).length) (Rb0 ψ c j).erase) :
    ∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
          fdoms0 es0 ihs mk0 Rb0 ψ,
        Term.bvarsBelow rs.length e.erase := by
  intro ψ
  have hpair : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∃ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (cA : ConstantVal × Nat)
        (rhs : Expr), rs[c]? = some r ∧ r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs := by
    intro c hc j hj
    have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
    have hjl : j < rs[c].2.2.2.length := by
      rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
    have hlen := recStage_rulesLen h hr
    exact ⟨rs[c], rs[c].2.2.2[j], rs[c].2.1[j]'(by omega), hr, List.getElem?_eq_getElem hjl,
      List.getElem?_eq_getElem _⟩
  show ∀ e ∈ blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _, _
  refine bvarsBelow_blockIotaEqsAV (fun c hc => ?_) (fun c hc j hj => ?_) (fun c hc j hj => ?_)
    (fun c hc j hj => ?_) (fun c hc j hj => ?_) (fun c hc j hj => ?_)
  · -- the prefix
    have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
    exact fieldsBelow_of_getD fun q hq => by
      rw [Nat.zero_add]; exact blockRulePdomsAV_bounded hμ mpC h hr ψ q hq
  all_goals
    dsimp only
    obtain ⟨r, cA, rhs, hr, hcA, hrhs⟩ := hpair c hc j hj
    obtain ⟨hF, hE, hM, hI, hR⟩ := hrow ψ c r hr j cA rhs hcA hrhs
    have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  · rw [hpl]; exact hF
  · rw [hpl]; exact hE
  · rw [hpl]; exact hM
  · rw [hpl]; exact hI
  · rw [hpl]; exact hR

/-- **The member rows of `heqB`**: at a MEMBER major, the rule's field
domains, index readings and fired spine at the block's data are bound by
their frames (the constructors' record, `BlockCtorDataI`). -/
theorem blockRule_rowB_member
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {j : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[j]? = some cA) {rhs : Expr} (hrhs : r.2.1[j]? = some rhs) (ψ : Name → Nat) :
    FieldsBelow (pp.toBlockShape.rulePrefixAt c)
        (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j) ∧
      (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 ∧
      (∀ e ∈ blockRuleEsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j,
        Term.bvarsBelow (pp.toBlockShape.rulePrefixAt c + cA.2) e.erase) ∧
      Term.bvarsBelow (pp.toBlockShape.rulePrefixAt c + cA.2)
        (blockRuleMkAV pp.toBlockShape rs mpC.base2.acval envC ψ c j).erase := by
  have hcj : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
    obtain ⟨ms, hms, hctA, -⟩ := recStage_ctorsAt (hm := hm) h hr
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  have hmemk : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k := by
    obtain ⟨ms, hms, -, -⟩ := recStage_ctorsAt (hm := hm) h hr
    exact (List.getElem?_eq_some_iff.mp hms).1
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c := by
    obtain ⟨-, -, hall⟩ := recStageG_recNames h
    obtain ⟨_, _, _, hr', -, -, hle, -⟩ := hall c (by
      have := (List.getElem?_eq_some_iff.mp hr).1
      rw [(recStageG_recNames h).2.1] at this; exact this)
    exact hle
  have hfd := (blockRuleFdomsAV_eq (hm := hm) h hr hcA hrhs hcd hCf hnP ψ)
  have hfl : (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq]
    obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, -, -, h₂, -, -, -, -, -⟩ :=
      blockRuleData_run (hm := hm) h hr hcA hrhs
    exact openPisAtFvars_length _ h₂
  refine ⟨?_, hfl, ?_, ?_⟩
  · -- the fields
    rw [hfd.1]
    have hd := ConLeche.Model.DomsBelow.drop pp.nP (hcd.below ψ)
    rw [Nat.zero_add] at hd
    have := fieldsBelow_liftDomsK_at (pp.toBlockShape.rulePrefixAt c - pp.nP) (k := 0) hd.fields
    rwa [show pp.nP + (pp.toBlockShape.rulePrefixAt c - pp.nP)
      = pp.toBlockShape.rulePrefixAt c from by omega] at this
  · -- the index expressions
    intro e he
    rw [blockRuleEsAV_eq (hm := hm) h hr hcA hrhs hcd hCf hnP ψ] at he
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he
    have hE' : Term.bvarsBelow (pp.nP + cA.2) E.erase := hcd.belowE ψ E hE
    exact bvarsBelow_liftN_add hE' (by omega) _
  · -- the fired spine
    rw [blockRuleMkAV_eq (hm := hm) h hr hcA hrhs hfindC hlpsC hnP ψ, AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN ?_ ?_
    · rw [mpC.base2.acval_erase]
      exact Term.bvarsBelow.mono (Nat.zero_le _) (mpC.base2.cval_closed _ _)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rcases List.mem_append.mp hy with hy | hy
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
        have := List.mem_range.mp hk
        show _ < _
        omega
      · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hy
        have := List.mem_range.mp hk
        show _ < _
        omega


/-- **`heqP`'s equation half, from the rows** (any majors): the equation
list reads alike at two level valuations agreeing on ANY recursor's
parameters (the family shares them, `recStage_lps`) once every rule's
five components do; the prefix is the recursor type's
(`blockRulePdomsAV_params`). -/
theorem blockRecEqs_params_rows (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR)
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hrow : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        fdoms0 ψ₁ c j = fdoms0 ψ₂ c j ∧ es0 ψ₁ c j = es0 ψ₂ c j ∧ ihs ψ₁ c j = ihs ψ₂ c j ∧
          mk0 ψ₁ c j = mk0 ψ₂ c j ∧ Rb0 ψ₁ c j = Rb0 ψ₂ c j) :
    ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecEqs (blockRecNCt rs) rs
            (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
            fdoms0 es0 ihs mk0 Rb0 ψ₁
          = blockRecEqs (blockRecNCt rs) rs
            (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ')
            fdoms0 es0 ihs mk0 Rb0 ψ₂ := by
  intro i₀ r₀ hr₀ ψ₁ ψ₂ hq₀
  show blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _
    = blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _
  refine blockIotaEqsAV_congr (fun c hc => blockRulePdomsAV_params hμ mpC h hr₀ hq₀ hc)
    (fun c hc j hj => ?_)
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjl : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  have hlen := recStage_rulesLen h hr
  have hq : ∀ q ∈ rs[c].1.levelParams, ψ₁ q = ψ₂ q := by
    rw [recStage_lps h hr hr₀]; exact hq₀
  exact hrow c rs[c] hr j rs[c].2.2.2[j] (rs[c].2.1[j]'(by omega)) (List.getElem?_eq_getElem hjl)
    (List.getElem?_eq_getElem _) ψ₁ ψ₂ hq


end MembersRun

/-! ## 1b. The `ℓ = 0` arm's RIGHT side

The stored rule reads as the point at a valuation where the checked
elimination level is zero.  A rule that binds a variable carries the
elimination datum on its head binder (`blockRuleRaZ_run`).  A rule that
binds NONE — the zero-motive recursor `T.rec : (t : T) → True`,
`T.rec T.c ↦ True.intro`, which the kernel accepts since the
motive-count floor was removed (lane FLOOR) — is its own residue: no
field means no guarded call, so the abstraction is the identity on the
closed right-hand side, and the family's ι law at the empty spine says
that residue equals the recursor's value, which is the point
(`blockRecTyZ_run`).  No λ-head bit and no typing of the right-hand side
is needed: the graph producer's ι law already carries it. -/


/-! ## 2. The composition

`declBlock_run` is `declBlock_data` at the route's component choices —
`nCt := blockRecNCt`, the four syntactic components
`blockRulePdomsAV`/`blockRuleFdomsAV`/`blockRuleEsAV`/`blockRuleMkAV` —
with every seam conjunct DISCHARGED from the run. -/

section Compose

/-- The seam's `nCt` bound: a recursor carries `blockRecNCt` rules. -/
theorem blockRecNCt_ge {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) : r.2.2.2.length ≤ blockRecNCt rs j := by
  rw [blockRecNCt, List.getD_eq_getElem?_getD, hr]
  exact Nat.le_refl _

end Compose

end ConLeche.Model
