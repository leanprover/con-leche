module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetGraph
public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.BlockRuleGrading

public section

/-!
# The seam's conjuncts at the target check's rule data (lane RECLIB, B3 (d))

`declBlock_data`'s existential (`BlockRecData.lean` §A.18) at
`ihs := tgtIhsAV`, `Rb0 := tgtRbAV` (`TargetRuleData.lean`) and today's
four syntactic components, for blocks where both checks ran
(`checkBlockRecK … = .ok (tgtRs out)` and a `TargetRecRun … out`).
Each conjunct is today's producer made generic in `ihs`/`Rb0`
(`…_gen`, `BlockDeclRun.lean`) fed the target rows.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts
  TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Seam

variable {fe : FEnv} {envI : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {mpC : EnvModelM V μ fe.env} {F : Nat}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
 
  {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {nested : Bool} {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {Rr : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}

/-- The formers' types are closed — off the members' run record. -/
theorem tgtFormer_facts
    (hmr : BlockMembersRun mpC.base2
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.toBlockShape cvTas) :
    ∀ cv ∈ cvTas, cv.type.hasFvar = false := by
  intro cv hcv
  obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
  exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1

/-- The rule's field readings — off the constructors' record (today's
`blockRuleFdomsAV_eq`, kind-free). -/
theorem blockRuleHdF_seam {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs rs memR)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k) :
    ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), memR c →
      rs[c]? = some r → ∀ (j : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA → r.2.1[j]? = some rhs → ∀ (ψ : Name → Nat) (l : Nat) (x : Expr),
      (blockRuleFieldFvs pp.toBlockShape rs c j)[l]? = some x →
        denoteMeta mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt c + l) (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval fe.env ψ c j).getD l
              default) := by
  intro c r hm hr j cA rhs hcA hrhs ψ
  obtain ⟨ms, hms, hctA, -⟩ := recStage_ctorsAt (hm := hm) h hr
  have hmemk : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hcj : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hcd := blockCtorData_of_core hcore hcj
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  exact (blockRuleFdomsAV_eq (hm := hm) h hr hcA hrhs hcd hwfC.1 TE.nP_le ψ).2

omit [SetTheory V] in
/-- The indexed bare-recursor cons carries the plain one's environment. -/
theorem consBlockRecsBareF_env (q : ConLeche.BlockShape) :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (fe' : FEnv),
      (ConLeche.consBlockRecsBareF q m cvRas fe').env = ConLeche.consBlockRecsBare q m cvRas fe'.env
  | _, [], _ => rfl
  | m, (cvRa, nIdx) :: rest, fe' => by
    simp only [ConLeche.consBlockRecsBareF, ConLeche.consBlockRecsBare]
    exact consBlockRecsBareF_env q (m + 1) rest _

/-- **A rule binding a variable reads as the point at `ℓ = 0`**, at ANY
major: its head λ carries the elimination level's zeroness. -/
theorem tgtRuleRaZ_pos {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hpos : 0 < pp.toBlockShape.rulePrefixAt j + cA.2)
    {acv : Name → (Name → Nat) → AnnotTerm} {env₃ : Env} {ψ : Name → Nat} {Ra : AnnotTerm}
    (hread : denoteMeta acv env₃ ψ 0 rhs = some Ra)
    (hℓ : Level.eval ψ
      (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0)
    (ρ : Nat → V) : interp V ρ Ra = pt := by
  obtain ⟨rP, rbs, body, hrP, hstrip, hpw⟩ : ∃ rP rbs body,
      rP = pp.toBlockShape.rulePrefixAt j ∧
      ConLeche.Expr.stripLams (rP + cA.2) rhs = some (rbs, body) ∧
      ∀ b ∈ rbs, b.2.pw = Level.zeronessOf
        (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) := by
    obtain ⟨rc, rhs0, M, Q, hrP, -, -, -, -, -, -⟩ := tgtRuleAt_factsG h R hr hcA hrhs
    exact ⟨rc.rP, Q.rbs, Q.body, hrP, Q.hstrip, Q.hpw⟩
  obtain ⟨k, hk⟩ : ∃ k, rP + cA.2 = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos (hrP ▸ hpos)).symm⟩
  rw [hk] at hstrip
  match rhs, hstrip with
  | .lam dom bd mb, hstrip =>
    simp only [ConLeche.Expr.stripLams] at hstrip
    cases hs : bd.stripLams k with
    | none => rw [hs] at hstrip; exact nomatch hstrip
    | some q =>
      rw [hs] at hstrip
      simp only [Option.map_some, Option.some.injEq] at hstrip
      have hmb : mb.pw = Level.zeronessOf
          (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) :=
        hpw (dom, mb) (by rw [← (Prod.mk.inj hstrip).1]; exact List.mem_cons_self)
      obtain ⟨ta, ba, -, -, rfl⟩ := denoteMeta_lam_inv hread
      have hb : pwBit ψ mb.pw = 0 := by rw [hmb]; exact (pwBit_zeronessOf ψ _).mpr hℓ
      rw [interp_lam, hb, ConLeche.SetModel.lamR_zero]

/-- **The `ℓ = 0` arm at a rule binding no variable, at the target data**
— the rule is its own residue (no field, no call: `targetAbstract_noFields`),
so the family's ι law at the empty spine says it reads as the recursor's
value, which is the point there. -/
theorem tgtRuleRaZ_empty (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    {s : (Name → Nat) → Nat} {fdoms0 es0 : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ) ((blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            fdoms0
            es0
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval fe.env ψ')
            mk0
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval fe.env ψ')) ψ) ρ)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hz : pp.toBlockShape.rulePrefixAt j + cA.2 = 0)
    (hfl : ∀ ψ : Name → Nat, (fdoms0 ψ j i).length = cA.2)
    {ψ : Name → Nat} {Ra : AnnotTerm}
    (hread : denoteMeta (blockRecAcv mpC.base2.acval fe.env (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            fdoms0
            es0
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval fe.env ψ')
            mk0
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval fe.env ψ')))
      (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) fe.env) ψ 0 rhs = some Ra)
    (hℓ : Level.eval ψ
      (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0)
    (ρ : Nat → V) : interp V ρ Ra = pt := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hi : i < blockRecNCt (tgtRs out) j := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr]
    exact (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨rc, rhs0, M, Q, hrP, hle, -, hB, -, hAbs, -⟩ := tgtRuleAt_factsG h R hr hcA hrhs
  -- the stored rule: closed, fvar-free
  obtain ⟨-, -, -, -, hrhsF⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  obtain ⟨hrf, -, hres, hrb⟩ := hrhsF rhs (List.mem_of_getElem? hrhs)
  -- an empty telescope: the body is the rule, and nothing is abstracted
  have hrP0 : rc.rP = 0 := by omega
  have hnF0 : cA.2 = 0 := by omega
  have hbody : Q.body = rhs := by
    have key : ∀ (n : Nat) (bs : List (Expr × ConLeche.BinderMeta)) (b : Expr),
        ConLeche.Expr.stripLams n rhs = some (bs, b) → n = 0 → b = rhs := by
      intro n bs b hs hn
      subst hn
      simp only [ConLeche.Expr.stripLams, Option.some.injEq] at hs
      exact (Prod.mk.inj hs).2.symm
    exact key _ _ _ Q.hstrip (by omega)
  have hfvsP : Q.fvsPref = [] :=
    List.eq_nil_of_length_eq_zero (by rw [openPisAtFvars_length _ Q.hpref, hrP0])
  have hfvsF : Q.fvsF = [] :=
    List.eq_nil_of_length_eq_zero (by rw [openPisAtFvars_length _ Q.hfld, hnF0])
  have hmono : ∀ n : Name,
      ((ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe).env.find? n).isSome = true →
      (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
        Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large))).recNames.contains n = false →
      (fe.env.find? n).isSome = true := by
    intro n hn hnot
    rw [consBlockRecsBareF_env] at hn
    rcases find?_consBlockRecsBare_isSome 0 _ fe.env n hn with hm | hm
    · have hnames : (tgtFam pp.toBlockShape (tgtRs out)).recNames = (tgtRs out).map (·.1.name) :=
        recStage_recNamesEq h
      simp only [ConLeche.targetFrameOf] at hnot
      rw [hnames] at hnot
      rw [List.map_map] at hm
      exact absurd (List.contains_iff_mem.mpr hm) (by simpa using hnot)
    · exact hm
  have hab := Q.habs
  rw [hbody] at hab
  have hinst : rhs.instantiateList (Q.fvsPref ++ Q.fvsF).reverse = rhs := by
    rw [hfvsP, hfvsF]; exact ConLeche.Expr.instantiateList_nil rhs 0
  rw [hinst] at hab
  obtain ⟨hbO, hihs, hcbT⟩ := targetAbstract_noFields (B := rc.rP + cA.2)
    (by simp only [ConLeche.targetFrameOf]; exact hfvsF) hle hmono 0 rhs #[] _ _ hab hrf
  have hcb : ConstsBound fe.env rhs := hcbT (by
    rw [consBlockRecsBareF_env]; exact constsBound_of_constsResolve _ hres)
  have hreadC : denoteMeta mpC.base2.acval fe.env ψ 0 rhs = some Ra :=
    (blockRecDenote_cross_eq h ψ 0 rhs hcb).trans hread
  have hRacl : Term.bvarsBelow 0 Ra.erase :=
    bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hrf) hrb hreadC
  -- the target residue IS the rule, and there is no `ih` term
  have hRb : tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
      fe.env ψ j i = Ra := by
    rw [tgtRbAV, ← hAbs, hB]
    simp only
    rw [hbO, hihs, hrP0, hnF0]
    simp only [Array.size_empty, Nat.add_zero]
    rw [hreadC]; rfl
  have hIh : tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
      fe.env ψ j i = [] := by
    rw [tgtIhsAV, ← hAbs]
    simp only
    rw [hihs]; rfl
  -- the ι law at the empty spine
  have hpl : (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j).length
      = 0 := by
    rw [blockRulePdomsAV_length hμ mpC h hr ψ]; omega
  have hfl : (fdoms0 ψ j i).length = 0 := by rw [hfl ψ]; omega
  obtain ⟨a, ha, hlaw⟩ := blockRecAV_iota (hpre ψ ρ)
  have ha0 : a j = pt :=
    eq_pt_of_mem_univZero (blockRecTyZ_run hμ mpC h j hj ψ ρ hℓ) (ha j hj).1
  have hsp : SpineFit (chainFrame (tgtRs out).length a ρ)
      (liftDomsK (tgtRs out).length 0
          (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j)
        ++ liftDomsK (tgtRs out).length
          (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j).length
          (fdoms0 ψ j i)) ([] ++ []) := by
    rw [List.eq_nil_of_length_eq_zero hpl, List.eq_nil_of_length_eq_zero hfl]
    trivial
  have hlawE := hlaw j hj i hi [] [] (by simp [hpl]) hsp
  dsimp only at hlawE
  rw [ha0, List.nil_append, foldl_app_pt', hRb, hIh, liftN_eq_self_of_closed hRacl,
    interp_closed V hRacl _ ρ] at hlawE
  exact hlawE.symm

/-- **THE `ℓ = 0` ARM'S RIGHT SIDE at the target data**: every stored
rule reads as the point where the checked elimination level is zero —
by its head binder's datum (`blockRuleRaZ_run`, kind-free) or, binding
no variable, by the ι law (`tgtRuleRaZ_empty`). -/
theorem tgtRuleRaZ_seam (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    {s : (Name → Nat) → Nat} {fdoms0 es0 : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ) ((blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            fdoms0
            es0
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval fe.env ψ')
            mk0
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval fe.env ψ')) ψ) ρ)
    (hfl : ∀ (ψ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      (fdoms0 ψ j i).length = cA.2) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ∀ (ψ : Name → Nat) (Ra : AnnotTerm),
        denoteMeta (blockRecAcv mpC.base2.acval fe.env (tgtRs out) s (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
            (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
            fdoms0
            es0
            (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval fe.env ψ')
            mk0
            (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval fe.env ψ')))
          (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) fe.env) ψ 0 rhs
            = some Ra →
        Level.eval ψ
          (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0 →
        ∀ ρ : Nat → V, interp V ρ Ra = pt := by
  intro j r hr i cA rhs hcA hrhs ψ Ra hread hℓ ρ
  by_cases hz : pp.toBlockShape.rulePrefixAt j + cA.2 = 0
  · exact tgtRuleRaZ_empty hμ h R hpre hr hcA hrhs hz (fun ψ => hfl ψ j r hr i cA hcA) hread hℓ ρ
  · exact tgtRuleRaZ_pos (V := V) h R hr hcA hrhs (Nat.pos_of_ne_zero hz) hread hℓ ρ

end Seam

end ConLeche.Model
