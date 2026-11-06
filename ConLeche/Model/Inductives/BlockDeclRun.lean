module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.Subst
import ConLeche.Model.Inductives.BlockRuleParams
import ConLeche.Model.Capstone
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Inductives.BlockRecGraph
import ConLeche.Model.Inductives.BlockModelRecords

public section

/-!
# The recursor stage at the run — pieces of the composition

The block step's recursors' stage (`nestedRecStage`, `DeclBlockStep.lean`)
reads these; the dispatch (`BlockRecPreHpre.lean`) and the rule contract
(`BlockRuleFit.lean`) produce the two largest of its obligations.  This
file holds the pieces of the stage that read the run directly.

The `ℓ = 0` arm's facts (the recursor type a truth value, the stored rule
the point) read the generated family's syntax and are proved at the
generated stage (`genRecTyZ`, `genRuleRaZ`, `GenClsFrame.lean`). -/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify

open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V]
  {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → Bool × List ConLeche.RecRule}


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

variable {envC envI : Env} {pp : ConLeche.BlockShape} {formers : List ConstantVal}
  {memberCtors : List (List (ConstantVal × Nat))} {mpC : EnvModelM V envC} {F : Nat}
  {isRec : Bool} {A : Nat → (Name → Nat) → Term}

  {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List Term}

/-- **`BlockMembersRun` from the constructors' three records**, at the
run's own block data. -/
theorem blockMembersRun_seam
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp pk uOfD ppsOf) pp.formers)
    (hS : BlockCtorsStage (V := V) F
      (blockDataOf V pp pk uOfD ppsOf) pp.lps pp.formers
      pp isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp pk uOfD ppsOf) pp.lps pp.formers
      pp isRec A
      (blockDataOf V pp pk uOfD ppsOf).k) :
    BlockMembersRun mpC.base2
      (blockDataOf V pp pk uOfD ppsOf) pp := by
  obtain ⟨hname, -, hlen⟩ := hN
  refine ⟨rfl, rfl, hlen, ?_, ?_, ?_, ?_⟩
  · intro m cvTb hcv
    have hm : m < (blockDataOf V pp pk uOfD ppsOf).k := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hcv).1
    obtain ⟨hfind, -, -, hFD⟩ := hcore.1 m cvTb hcv
    obtain ⟨cvS, -, hDS⟩ := id hfind
    exact ⟨hname m cvTb hcv, hS.lpsT m cvTb hm hcv, ⟨_, hfind⟩, hDS.readFvar, hDS.readBounded, hFD⟩
  · intro m ms hms
    have hm : m < pp.members.length := (List.getElem?_eq_some_iff.mp hms).1
    have hg : pp.members.getD m default = ms := by
      rw [List.getD_eq_getElem?_getD, hms]; rfl
    refine ⟨?_, ?_⟩
    · show (pp.members.map (·.cvT.name)).getD m .anonymous = ms.cvT.name
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hms]; rfl
    · show pp.nIdxs.getD m 0 = ms.nIdx
      rw [blockNIdxs_getD hm, hg]
  · intro m ψ hm
    obtain ⟨cvTb, hcv⟩ : ∃ cvTb, pp.formers[m]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact hm)⟩
    obtain ⟨-, -, hleaf, -⟩ := hcore.1 m cvTb hcv
    rw [hname m cvTb hcv, hleaf ψ, hS.leaf m ψ]
    exact ⟨_, rfl⟩
  · intro m hm ψ ρ
    have h0 : 0 < (blockDataOf V pp pk uOfD ppsOf).k :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) hm
    exact ⟨fun h => hS.paramsOf m hm ψ ρ h 0 h0, fun h => hS.paramsOf 0 h0 ψ ρ h m hm⟩

/-- **The block's representation at the seam** — `blockModelAt_of_records`
with its four identifications `rfl` at the run's own block data, and
`0 < k` off the counting pass's first clause. -/
theorem blockModelAt_seam
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageG .verified F envC pp rs)
    (hN : BlockNamesOk (V := V)
      (blockDataOf V pp pk uOfD ppsOf) pp.formers)
    (hS : BlockCtorsStage (V := V) F
      (blockDataOf V pp pk uOfD ppsOf) pp.lps pp.formers
      pp isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp pk uOfD ppsOf) pp.lps pp.formers
      pp isRec A
      (blockDataOf V pp pk uOfD ppsOf).k) :
    BlockModelAt mpC.base2
      (blockDataOf V pp pk uOfD ppsOf).memberNames
      (blockDataOf V pp pk uOfD ppsOf) := by
  obtain ⟨R⟩ := id h
  exact blockModelAt_of_records hN hS hcore rfl R.fam.k_pos (fun _ _ => rfl) (fun _ _ _ _ => rfl)

/-- **The seam's canonical constructor-type reading**: the stored type
of recursor `j`'s `i`-th constructor, read at the constructors'
environment. -/
@[expose] noncomputable def blockRecCtorTy (acval : Name → (Name → Nat) → Term) (envC : Env)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))) (j i : Nat)
    (ψ : Name → Nat) : Term :=
  (denote acval envC ψ 0 ((rs.getD j default).2.2.2.getD i default).1.type).getD default


omit [SetTheory V] in
/-- A field chain whose entries are bounded one by one is bounded. -/
theorem domsBelow_of_getD :
    ∀ {m : Nat} {Fs : List Term},
      (∀ q, q < Fs.length → Term.bvarsBelow (m + q) (Fs.getD q default)) →
      DomsBelow m Fs
  | _, [], _ => trivial
  | m, _ :: Fs, h => by
    refine ⟨by simpa using h 0 (by simp), domsBelow_of_getD (m := m + 1) (Fs := Fs)
      fun q hq => ?_⟩
    have := h (q + 1) (by simpa using hq)
    simpa [show m + (q + 1) = m + 1 + q from by omega] using this

/-- **`heqB` from the rows** (any majors): every equation is bound below
the family once every rule's components are bound by their frames; the
prefix is the recursor type's (`blockRulePdomsAV_bounded`). -/
theorem blockRecEqs_below_rows
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageG .verified F envC pp rs)
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List Term}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → Term}
    (hrow : ∀ (ψ : Name → Nat) (c : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (ctor : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some ctor → r.2.1[j]? = some rhs →
        DomsBelow (pp.rulePrefixAt c) (fdoms0 ψ c j) ∧
        (∀ e ∈ es0 ψ c j, Term.bvarsBelow
          (pp.rulePrefixAt c + (fdoms0 ψ c j).length) e) ∧
        Term.bvarsBelow (pp.rulePrefixAt c + (fdoms0 ψ c j).length)
          (mk0 ψ c j) ∧
        (∀ v ∈ ihs ψ c j, Term.bvarsBelow
          (rs.length + pp.rulePrefixAt c + (fdoms0 ψ c j).length) v) ∧
        Term.bvarsBelow (pp.rulePrefixAt c + (fdoms0 ψ c j).length
          + (ihs ψ c j).length) (Rb0 ψ c j)) :
    ∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp rs ψ')
          fdoms0 es0 ihs mk0 Rb0 ψ,
        Term.bvarsBelow rs.length e := by
  intro ψ
  have hpair : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∃ (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)) (ctor : ConstantVal × Nat)
        (rhs : Expr), rs[c]? = some r ∧ r.2.2.2[j]? = some ctor ∧ r.2.1[j]? = some rhs := by
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
    exact domsBelow_of_getD fun q hq => by
      rw [Nat.zero_add]; exact blockRulePdomsAV_bounded mpC h hr ψ q hq
  all_goals
    dsimp only
    obtain ⟨r, ctor, rhs, hr, hctor, hrhs⟩ := hpair c hc j hj
    obtain ⟨hF, hE, hM, hI, hR⟩ := hrow ψ c r hr j ctor rhs hctor hrhs
    have hpl := blockRulePdomsAV_length mpC h hr ψ
  · rw [hpl]; exact hF
  · rw [hpl]; exact hE
  · rw [hpl]; exact hM
  · rw [hpl]; exact hI
  · rw [hpl]; exact hR

/-- **`heqP`'s equation half, from the rows** (any majors): the equation
list reads alike at two level valuations agreeing on ANY recursor's
parameters (the family shares them, `recStage_lps`) once every rule's
five components do; the prefix is the recursor type's
(`blockRulePdomsAV_params`). -/
theorem blockRecEqs_params_rows
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.RecStageG .verified F envC pp rs)
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List Term}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → Term}
    (hrow : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → ∀ (j : Nat) (ctor : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some ctor → r.2.1[j]? = some rhs → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        fdoms0 ψ₁ c j = fdoms0 ψ₂ c j ∧ es0 ψ₁ c j = es0 ψ₂ c j ∧ ihs ψ₁ c j = ihs ψ₂ c j ∧
          mk0 ψ₁ c j = mk0 ψ₂ c j ∧ Rb0 ψ₁ c j = Rb0 ψ₂ c j) :
    ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecEqs (blockRecNCt rs) rs
            (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp rs ψ')
            fdoms0 es0 ihs mk0 Rb0 ψ₁
          = blockRecEqs (blockRecNCt rs) rs
            (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp rs ψ')
            fdoms0 es0 ihs mk0 Rb0 ψ₂ := by
  intro i₀ r₀ hr₀ ψ₁ ψ₂ hq₀
  show blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _
    = blockIotaEqsAV rs.length (blockRecNCt rs) _ _ _ _ _ _
  refine blockIotaEqsAV_congr (fun c hc => blockRulePdomsAV_params mpC h hr₀ hq₀ hc)
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

/-! ## 2. The `nCt` bound

The composition (`declBlock`, `DeclBlockStep.lean`) takes
`nCt := blockRecNCt`. -/

section Compose

/-- The seam's `nCt` bound: a recursor carries `blockRecNCt` rules. -/
theorem blockRecNCt_ge {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) : r.2.2.2.length ≤ blockRecNCt rs j := by
  rw [blockRecNCt, List.getD_eq_getElem?_getD, hr]
  exact Nat.le_refl _

end Compose

end ConLeche.Model
