module

import ConLeche.Model.Inductives.TargetFrame
public import ConLeche.Model.Inductives.TargetIhSlot
public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Verify.Inductives.BlockRecNames
import ConLeche.Verify.Inductives.BlockRecRun
public import ConLeche.Model.Inductives.BlockRuleParams

public section

/-!
# The seam's residue conjunct over the target check (lane RECLIB, B3 (c′))

`BlockRuleResidueB` (`BlockRecData.lean` §A.19b) is the seam's fourth
conjunct: the rule's λ-tower core, read at the fired frame, against the
residue at the `ih` values.  Here it is proved at the TARGET check's
rule data — `ihs := tgtIhsAV`, `Rb0 := tgtRbAV` (`TargetRuleData.lean`)
— from `targetRuleBodyEq_run` (`TargetFrame.lean`) at the `(j, i)`-th
rule run `targetRuleAt` pins.

The two runs are taken together (`h`, today's; `R`, the target's, with
`rs = tgtRs out`): the frame's prefix and field readings, the recursor
types' facts and the callees' leaves are today's kind-free inversions,
which B1 re-points at one generic stage record.  Nothing here reads a
field kind.

What crosses:
* the call's `ih` value — the tgt `ih` term `L.inst (bvar (B + K-1-c))`
  at the chain frame is `L` at the callee's chain value (`interp_inst`,
  `chainFrame_apply`), and `L` is bound below `B + 1`
  (`targetRuleBodyEq_run`'s second conclusion), so the chain below the
  frame is invisible;
* the residue's reading IS `tgtRbAV` (the pinning's `tgtAbs`);
* the callee's leaf is typed at its recursor type (`blockRecAV_facts` at
  the family's regime `hpre`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo CheckMode FEnv BlockShape BlockParts
  TargetMajor TargetIh RecShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- A call's callee is a position of the family: its stored type is
opened past the prefix and index arguments to a `∀`, which the default
`Sort 0` past the family is not. -/
theorem targetCall_callee_lt {F : Nat} {env : Env} {fam : ConLeche.TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × ConLeche.BinderMeta))}
    {absM : Expr → Expr} {base k : Nat} {pw : ConLeche.PropWhen} {ih : TargetIh}
    (C : ConLeche.TargetCallRun μ F env fam fvsPref fvsF fnorm teles absM base k pw ih) :
    ih.callee < fam.recTys.length := by
  refine Nat.lt_of_not_le fun hc => ?_
  have hg : fam.recTys.getD ih.callee (.sort .zero) = .sort .zero := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hc]; rfl
  have h1 := C.hcallee
  rw [hg, C.hmajDom] at h1
  cases hl : fvsPref ++ ih.idx with
  | nil => rw [hl] at h1; simp [Expr.instPisAtLift] at h1
  | cons a as => rw [hl] at h1; simp [Expr.instPisAtLift] at h1

/-- The recomputed width `tgtB` at a stored rule. -/
theorem tgtB_at {p : BlockShape} {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[j]? = some r)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA) :
    tgtB p rs j i = p.rulePrefixAt j + cA.2 := by
  have hct : tgtCtorOf rs j i = cA := by
    simp only [tgtCtorOf, List.getD_eq_getElem?_getD, hr, Option.getD_some, hcA]
  rw [tgtB, hct]; rfl

/-- **The seam's RESIDUE conjunct at the target check's rule data**
(B3 (c′)): `BlockRuleResidueB` with `ihs := tgtIhsAV` and
`Rb0 := tgtRbAV`, the prefix and field domains today's
(`blockRulePdomsAV`/`blockRuleFdomsAV`), from both runs.

The premises are `blockRuleResidueB_run`'s kind-free ones — the consed
environment's model and the leaf's closedness, the right-hand side's
reading `hread`, the contract's first conjunct `hsp` — plus the family's
regime `hpre` (the callees' leaves are typed), the stored constructor
type's scoping, the formers', the field readings `hdF` and the frame's
grading at the prefix and the fields `hokPF`. -/
theorem tgtRuleResidueB (hμ : μ.verifiedChecks = true) {F : Nat} {fe : FEnv}
    {mpC : EnvModelM V μ fe.env} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    (hndM : pp.toBlockShape.memberNames.Nodup)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {es0 : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    {ctorTy : (Name → Nat) → AnnotTerm} {φ : Name → Nat} {rl : ConLeche.RecRule}
    {m₃ : EnvModel V (consBlockRecs fe.env.find? pp.toBlockShape pp.nP 0 (tgtRs out) fe.env)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval fe.env (tgtRs out) s
      (blockRecEqs nCt (tgtRs out)
        (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
        (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ') es0
        (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
          mpC.base2.acval fe.env ψ') mk0
        (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
          mpC.base2.acval fe.env ψ')))
    (hleafCl : ∀ (ψ : Name → Nat) (q : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval fe.env (tgtRs out) s
        (blockRecEqs nCt (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ') es0
          (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ') mk0
          (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ')) ψ q).erase))
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ)
        (blockRecEqs nCt (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ') es0
          (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ') mk0
          (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
            mpC.base2.acval fe.env ψ') ψ) ρ)
    -- the stored constructor type, and the formers'
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hCc : ConstsBound fe.env cA.1.type)
    (hformer : ∀ cv ∈ cvTas, cv.type.hasFvar = false)
    -- the field readings, and the frame's grading at the prefix and the fields
    (hdF : ∀ (ψ : Name → Nat) (l : Nat) (x : Expr),
      (blockRuleFieldFvs pp.toBlockShape (tgtRs out) j i)[l]? = some x →
        denoteMeta mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).getD l
              default))
    (hokPF : ∀ ψ : Name → Nat,
      ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).getD l
              default))
    -- the right-hand side's reading
    (hread : ∀ us : List Level, us.length = r.1.levelParams.length →
      denoteMeta m₃.acval (consBlockRecs fe.env.find? pp.toBlockShape pp.nP 0 (tgtRs out) fe.env)
          (Level.substFn φ r.1.levelParams us) 0 rhs
        = some (blockRuleRaOf m₃.acval
            (consBlockRecs fe.env.find? pp.toBlockShape pp.nP 0 (tgtRs out) fe.env) rhs
            (Level.substFn φ r.1.levelParams us)))
    -- the contract's FIRST conjunct at the base frame
    (hsp : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0 →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
        xs.length = pp.toBlockShape.majorIdxAt j → ys.length = pp.nP + cA.2 →
        usj.length = cA.1.levelParams.length →
        Level.substFn φ cA.1.levelParams usj
          = Level.substFn φ cA.1.levelParams
              (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
                (pp.toBlockShape.rulePrefixAt j)).1 →
        IotaIndexPin (V := V) ρ restC pp.nP
          (pp.toBlockShape.majorIdxAt j) (pp.toBlockShape.rulePrefixAt j) xs →
        TeleFitPA V ρ
          (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) (Level.substFn φ r.1.levelParams us) j)
          (xs ++ [AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
        TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
        SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out)
              (Level.substFn φ r.1.levelParams us) j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env
              (Level.substFn φ r.1.levelParams us) j i)
          ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop pp.nP).map (interp V ρ))) :
    BlockRuleResidueB (V := V) mpC pp (tgtRs out) s nCt
      (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
      (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ') es0
      (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
        mpC.base2.acval fe.env ψ') mk0
      (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
        mpC.base2.acval fe.env ψ')
      ctorTy φ j i r cA rl rhs := by
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC a hleaf
    lds A hlam hldslen
  have hcv := checkBlockRecK_cvFacts h
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  -- the `(j, i)`-th target rule run, pinned
  obtain ⟨rc, rhs0, M, Q, hrc, hmem, hds, hPref, hFld, hBody, hFn, hAbs⟩ :=
    targetRuleAt R hr hcA hrhs
  have hrP : rc.rP = pp.toBlockShape.rulePrefixAt j := by
    simp only [BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, hrc]; rfl
  have hct : ConLeche.targetCtorAt M cA.1 = cA.1.type := by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hmem
    simp [ConLeche.targetCtorAt, ht]
  -- the stored recursor type's and rule's scoping
  obtain ⟨hTf, -, hTres, hTb, hallRhs⟩ :=
    ConLeche.checkBlockRecK_facts h r (List.mem_of_getElem? hr)
  have hTc : ConstsBound fe.env r.1.type := constsBound_of_constsResolve _ hTres
  obtain ⟨hfvRhs, -⟩ := hallRhs rhs (List.mem_of_getElem? hrhs)
  have hbf : Q.body.hasFvar = false := (stripLams_not_hasFvar _ Q.hstrip hfvRhs).2
  -- the frame's openers are today's
  have hPrefEq : Q.fvsPref = blockRulePrefFvs pp.toBlockShape (tgtRs out) j := hPref.trans rfl
  have hcrestEq : Q.crest = blockRuleCrest pp.toBlockShape (tgtRs out) j i := by
    have hc := Q.hcrest
    rw [hct, hds, instPisWith_eq_instPisAt] at hc
    rw [blockRuleCrest, blockRuleCtorOf_eq hr hcA, ← hPrefEq, hc, Option.getD_some]
  have hFldEq : Q.fvsF = blockRuleFieldFvs pp.toBlockShape (tgtRs out) j i := by
    rw [blockRuleFieldFvs, blockRuleCtorOf_eq hr hcA, ← hcrestEq, ← hrP, Q.hfld, Option.map_some,
      Option.getD_some]
  -- the family's prefixes lie below its majors
  obtain ⟨-, hlenR, hallN⟩ := checkBlockRecK_recNames h
  have hle : ∀ c', (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD c' 0
      ≤ (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD c' 0 := by
    intro c'
    by_cases hc' : c' < pp.recs.length
    · obtain ⟨rc', -, hrc', -, -, -, -, nIdx, hmI⟩ := hallN c' hc'
      simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [show pp.toBlockShape.recs = pp.recs from rfl, hrc']
      simp only [BlockShape.majorIdxAt, BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD] at hmI
      rw [show pp.toBlockShape.recs = pp.recs from rfl, hrc'] at hmI
      simp only [Option.map_some, Option.getD_some] at hmI ⊢
      omega
    · simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_none (by omega)]
      simp
  -- the family's recursor types
  have hRT : ∀ c',
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).hasFvar = false ∧
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
        = true ∧
      ConstsBound fe.env ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)) ∧
      ∃ RTa : AnnotTerm,
        denoteMeta mpC.base2.acval fe.env (Level.substFn φ r.1.levelParams us) (rc.rP + cA.2)
          ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)) = some RTa ∧
        (∀ σ : Nat → V, WellDenotedV V σ RTa) := by
    intro c'
    by_cases hc' : c' < (tgtRs out).length
    · have hr' : (tgtRs out)[c']? = some (tgtRs out)[c'] := List.getElem?_eq_getElem hc'
      have hg : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)
          = (tgtRs out)[c'].1.type := by
        simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
      rw [hg]
      obtain ⟨hf, -, hres, hb, -⟩ :=
        ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')
      obtain ⟨-, -, -, hread0, -, -, -, -, -, hwd⟩ :=
        checkBlockRecK_tyPis hμ mpC h hr' (Level.substFn φ r.1.levelParams us)
      exact ⟨hf, hb, constsBound_of_constsResolve _ hres, _,
        denoteMeta_depth_of_closed mpC.base2.acval_closed hf
          (fun k => liftN_eq_self_of_closed
            (closed_blockRecTyAV hμ mpC h hr' (Level.substFn φ r.1.levelParams us)) k 1)
          hread0 _, hwd⟩
    · have hg : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)
          = .sort .zero := by
        simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_none (by omega)]; rfl
      rw [hg]
      exact ⟨rfl, rfl, by simp,
        AnnotTerm.sort (Level.eval (Level.substFn φ r.1.levelParams us) Level.zero),
        by simp [denoteMeta], fun σ => ⟨trivial, trivial⟩⟩
  -- the frame's readings and grading at the prefix and the fields
  have hpl : (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out)
      (Level.substFn φ r.1.levelParams us) j).length = rc.rP := by
    rw [blockRulePdomsAV_length hμ mpC h hr, hrP]
  have hfl : (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env
      (Level.substFn φ r.1.levelParams us) j i).length = cA.2 :=
    blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs _
  have hdoms : ∀ (q : Nat) (x : Expr), (Q.fvsPref ++ Q.fvsF)[q]? = some x →
      denoteMeta mpC.base2.acval fe.env (Level.substFn φ r.1.levelParams us) q (Expr.fvarTypeD x)
        = some ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out)
              (Level.substFn φ r.1.levelParams us) j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env
              (Level.substFn φ r.1.levelParams us) j i).reverse.getD (rc.rP + cA.2 - 1 - q)
              default) := by
    intro q x hx
    have hq := blockRuleHdoms_of (acval := mpC.base2.acval) (envT := fe.env)
      (ψ := Level.substFn φ r.1.levelParams us) (ihdoms := []) (fvsIh := []) hpl hfl rfl
      (openPisAtFvars_length _ Q.hpref) (openPisAtFvars_length _ Q.hfld) rfl
      (blockRulePdomsAV_reads hμ mpC h hr _ (by rw [← hrP]; exact Q.hpref))
      (by rw [hFldEq, hrP]; exact hdF _)
      (fun l x hx => nomatch hx) q x (by simpa using hx)
    simpa using hq
  have hokΔ : ∀ q, q < rc.rP + cA.2 → ∀ ρ' : Nat → V,
      Sat V (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out)
              (Level.substFn φ r.1.levelParams us) j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env
              (Level.substFn φ r.1.levelParams us) j i).reverse ρ' →
      WellDenotedV V (fun l => ρ' (l + (rc.rP + cA.2 - 1 - q) + 1))
        ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out)
              (Level.substFn φ r.1.levelParams us) j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env
              (Level.substFn φ r.1.levelParams us) j i).reverse.getD (rc.rP + cA.2 - 1 - q)
              default) := by
    intro q hq ρ' hsat
    have hk := blockRuleHokΔ_of (V := V) (ihdoms := []) hpl hfl rfl
      (fun l hl σ' ys hys => by
        have := hokPF (Level.substFn φ r.1.levelParams us) l (by rw [← hrP]; omega) σ' ys
          (by simpa using hys)
        simpa using this) q (by simpa using hq) ρ' (by simpa using hsat)
    simpa using hk
  -- the callees' values are the chain's: typed at their recursor types
  have hR : ∀ ih ∈ Q.ihs.toList, ∀ RTa : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env (Level.substFn φ r.1.levelParams us) (rc.rP + cA.2)
          ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD ih.callee (.sort .zero)) = some RTa →
      a ih.callee ∈ˢ interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ (ys.drop pp.nP).map (interp V ρ)) ρ) RTa := by
    intro ih hih RTa hRTa
    obtain ⟨C⟩ := Q.call hih
    have hc : ih.callee < (tgtRs out).length := by
      have := targetCall_callee_lt C
      simpa [tgtFam] using this
    have hr' : (tgtRs out)[ih.callee]? = some (tgtRs out)[ih.callee] :=
      List.getElem?_eq_getElem hc
    have hg : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD ih.callee (.sort .zero)
        = (tgtRs out)[ih.callee].1.type := by
      simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
    rw [hg] at hRTa
    obtain ⟨hf, -⟩ := ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')
    obtain ⟨-, -, -, hread0, -⟩ :=
      checkBlockRecK_tyPis hμ mpC h hr' (Level.substFn φ r.1.levelParams us)
    have hcl := closed_blockRecTyAV hμ mpC h hr' (Level.substFn φ r.1.levelParams us)
    rw [denoteMeta_depth_of_closed mpC.base2.acval_closed hf
      (fun k => liftN_eq_self_of_closed hcl k 1) hread0 _] at hRTa
    obtain rfl := Option.some.inj hRTa
    rw [interp_closed (V := V) hcl _ ρ]
    obtain ⟨a', ha', -⟩ := blockRecAV_facts (hpre (Level.substFn φ r.1.levelParams us) ρ)
    have hmem := (ha' ih.callee hc).1
    rw [← (ha' ih.callee hc).2.1] at hmem
    rw [← hleaf ih.callee hc]
    exact hmem
  -- the family's names and levels are the stored recursors'
  have hnd : ((tgtRs out).map (·.1.name)).Nodup := checkBlockRecK_nodup h hndM
  have hnames : (tgtFam pp.toBlockShape (tgtRs out)).recNames = (tgtRs out).map (·.1.name) :=
    checkBlockRecK_recNamesEq h
  have hrlvls : (tgtFam pp.toBlockShape (tgtRs out)).rlvls
      = r.1.levelParams.map Level.param := by
    obtain ⟨rc0, r0, hrc0, hr0, -, hcv0, -⟩ := hallN 0 (by omega)
    have hl0 : r0.1.levelParams = rc0.cvR.levelParams := (ConLeche.checkConstantVal_lps hcv0).2
    have hlr : r.1.levelParams = r0.1.levelParams := checkBlockRecK_lps h hr hr0
    show (pp.toBlockShape.recs.head?.map fun q => q.cvR.levelParams.map Level.param).getD [] = _
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.head?_eq_getElem?, hrc0, hlr, hl0]
    rfl
  have hcallee : ∀ (nm : Name) (c' : Nat),
      ConLeche.nameIdxOf? (tgtFam pp.toBlockShape (tgtRs out)).recNames nm = some c' →
      ∃ ci : ConstantInfo,
        (consBlockRecs fe.env.find? pp.toBlockShape pp.nP 0 (tgtRs out) fe.env).find? nm
          = some ci ∧
        (tgtFam pp.toBlockShape (tgtRs out)).rlvls.length = ci.toConstantVal.levelParams.length ∧
        ∀ ρ' : Nat → V,
          interp V ρ' (blockRecAcv mpC.base2.acval fe.env (tgtRs out) s
            (blockRecEqs nCt (tgtRs out)
              (fun ψ' => blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ')
              (fun ψ' => blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ')
              es0
              (fun ψ' => tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
                mpC.base2.acval fe.env ψ') mk0
              (fun ψ' => tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
                mpC.base2.acval fe.env ψ'))
            nm (Level.substFn (Level.substFn φ r.1.levelParams us)
            ci.toConstantVal.levelParams (tgtFam pp.toBlockShape (tgtRs out)).rlvls)) = a c' := by
    intro nm c' hnm
    rw [hnames] at hnm
    obtain ⟨hval, hlt, -⟩ :
        ((tgtRs out).map (·.1.name))[c']?.getD default = nm ∧
          c' < ((tgtRs out).map (·.1.name)).length ∧
          ∀ j, j < c' → ¬ ((tgtRs out).map (·.1.name))[j]?.getD default = nm := by
      simpa [ConLeche.nameIdxOf?] using hnm
    rw [List.length_map] at hlt
    obtain ⟨r', hr'⟩ : ∃ r', (tgtRs out)[c']? = some r' := ⟨_, List.getElem?_eq_getElem hlt⟩
    have hnmr : r'.1.name = nm := by
      rw [← hval, List.getElem?_map, hr']; rfl
    have hlps : r'.1.levelParams = r.1.levelParams := checkBlockRecK_lps h hr' hr
    have hfind := find?_consBlockRecs_at (find? := fe.env.find?) (q := pp.toBlockShape)
      (nP := pp.nP) (m := 0) hnd (fun r₀ hr₀ => (hcv r₀ hr₀).1) hr'
    rw [hnmr] at hfind
    refine ⟨_, hfind, ?_, fun ρ' => ?_⟩
    · show (tgtFam pp.toBlockShape (tgtRs out)).rlvls.length = r'.1.levelParams.length
      rw [hrlvls, List.length_map, hlps]
    · show interp V ρ' (blockRecAcv mpC.base2.acval fe.env (tgtRs out) s _ nm
          (Level.substFn (Level.substFn φ r.1.levelParams us)
          r'.1.levelParams (tgtFam pp.toBlockShape (tgtRs out)).rlvls)) = a c'
      rw [hlps, hrlvls, Level.substFn_param_self, ← hnmr, blockRecAcv,
        blockRecAcvOf_at hnd (by rw [List.getElem?_map, hr']; rfl)]
      rw [interp_closed (V := V) (hleafCl _ c') _ ρ]
      exact hleaf c' hlt
  -- the frame's openers, as a local list
  obtain ⟨hFr, -, -, -⟩ := targetFrame_facts (envT := fe.env) Q.hpref Q.hcrest hds Q.hfld
    hTf hTb hTc (by rw [hct]; exact hCf) (by rw [hct]; exact hCb) (by rw [hct]; exact hCc)
  have h1 : LocList 0 (rc.rP + cA.2) (Q.fvsPref ++ Q.fvsF).reverse :=
    ⟨hFr.1, fun q hq => by
      obtain ⟨ty, hty⟩ := hFr.2.1 q hq
      exact ⟨ty, by rw [Nat.zero_add]; exact hty⟩⟩
  -- the tower's core IS the stripped body, opened at the frame
  have hread' := hread us hus
  rw [hac] at hread'
  have hsplen : (Q.fvsPref ++ Q.fvsF).length = rc.rP + cA.2 := by
    rw [List.length_append, openPisAtFvars_length _ Q.hpref, openPisAtFvars_length _ Q.hfld]
  obtain ⟨Γ, C, htele, hΓlen, hrest, -⟩ :=
    instLamsAt_denotePTele (Q.fvsPref ++ Q.fvsF) Q.hlams
      (blockRuleOpeners_index Q.hpref Q.hfld) hread'
  obtain ⟨lds0, hmap, hT⟩ := lamTele_mkLamsAV htele
  have hlen0 : lds0.length = rc.rP + cA.2 := by
    have hq : (lds0.map (·.2)).length = Γ.reverse.length := by rw [hmap]
    simp only [List.length_map, List.length_reverse] at hq
    rw [hq, hΓlen, hsplen]
  obtain ⟨-, rfl⟩ : lds = lds0 ∧ A = C :=
    mkLamsAV_length_inj (by rw [hldslen, hlen0, hrP]) (hlam ▸ hT)
  have hrestEq : Q.lrest = Q.body.instantiateList (Q.fvsPref ++ Q.fvsF).reverse 0 :=
    instLamsAt_rest_eq _ Q.hlams (by rw [hsplen]; exact Q.hstrip)
  rw [Nat.zero_add, hsplen, hrestEq] at hrest
  -- THE BODY EQUATION at the target run
  obtain ⟨⟨Bv, hBv, heq⟩, hLb⟩ := targetRuleBodyEq_run (V := V) hμ (mT := mpC.base2)
    (fun n ψ' m k => by rw [← hac]; exact liftN_eq_self_of_closed (m₃.cval_closedL n ψ') k m)
    (fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m)
    (Rules.RulesInputs.ofSem mpC _)
    (fun sn q => (findProj?_consBlockRecs (fun r₀ hr₀ => (hcv r₀ hr₀).2.2.1) sn q).symm)
    (fun D y ya hcby hy => by
      have := blockRecDenote_cross h hac _ D y hcby hy
      rwa [hac] at this)
    Q hle hbf hds hTf hTb hTc (by rw [hct]; exact hCf) (by rw [hct]; exact hCb)
    (by rw [hct]; exact hCc)
    (fun t ht => by obtain ⟨cv, hcv', rfl⟩ := List.mem_map.mp ht; exact hformer cv hcv')
    hRT hpl hfl hdoms hokΔ
    (hsp us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC)
    (fun h0 => hℓ ((pwBit_zeronessOf _ _).mp h0)) a hR hcallee h1 hrest
  -- the residue's reading IS `tgtRbAV`
  have hB : tgtB pp.toBlockShape (tgtRs out) j i = rc.rP + cA.2 := by
    rw [tgtB_at hr hcA, hrP]
  have hRB : tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
      fe.env (Level.substFn φ r.1.levelParams us) j i = Bv := by
    rw [tgtRbAV, ← hAbs, hB]
    simp only
    rw [hBv, Option.getD_some]
  -- the `ih` terms at the chain frame ARE the call λs at the callees' chain values
  have hframeLen : ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
      ++ (ys.drop pp.nP).map (interp V ρ)).length = rc.rP + cA.2 := by
    have := blockRecHrPle (p := pp) h hj
    simp only [List.length_append, List.length_map, List.length_take, List.length_drop, hxl, hyl]
    rw [hrP]; omega
  have hIH : (tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env (Level.substFn φ r.1.levelParams us) j i).map
        (interp V (blockRuleFrame (tgtRs out).length a ρ (pp.toBlockShape.rulePrefixAt j) pp.nP
          xs ys))
      = ihValsAt a (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ (ys.drop pp.nP).map (interp V ρ)) ρ) Q.ihs.toList
          (ihLamReads mpC.base2.acval fe.env (Level.substFn φ r.1.levelParams us)
            (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref Q.fvsF
            (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
            (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
              pp.toBlockShape.large)) Q.ihs.toList) := by
    have hFrEq : tgtFrame μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) j i
        = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
            Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
              pp.toBlockShape.large)) := by
      rw [tgtFrame, ← hPref, ← hFld, ← hFn]
      congr 1
      simp only [tgtRP, List.getD_eq_getElem?_getD]
      rw [show pp.toBlockShape.recs = pp.recs from rfl, hrc]; rfl
    rw [tgtIhsAV, ← hAbs, hFrEq, hB]
    simp only [List.map_map]
    apply List.ext_getElem
    · simp [ihValsAt]
    intro q hq1 hq2
    have hq : q < Q.ihs.size := by simpa using hq1
    have hq' : q < Q.ihs.toList.length := by simpa using hq
    simp only [List.getElem_map, Function.comp, ihValsAt, List.getElem_range]
    have hgd : Q.ihs.toList.getD q default = Q.ihs.toList[q] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq']; rfl
    have hLr : (ihLamReads mpC.base2.acval fe.env (Level.substFn φ r.1.levelParams us)
          (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref Q.fvsF
          (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
          (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) Q.ihs.toList).getD q default
        = (denoteMeta mpC.base2.acval fe.env (Level.substFn φ r.1.levelParams us)
            (rc.rP + cA.2 + 1)
            (targetCallE (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP
              Q.fvsPref Q.fvsF Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel
                pp.toBlockShape.elim pp.toBlockShape.large)))
              (rc.rP + cA.2) (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
                pp.toBlockShape.large)) Q.ihs.toList[q])).getD default := by
      rw [ihLamReads, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hq']
      rfl
    have hb := hLb q hq
    rw [hLr] at hb
    rw [hgd, hLr, interp_inst0]
    obtain ⟨C⟩ := Q.call (List.getElem_mem hq')
    have hc : Q.ihs.toList[q].callee < (tgtRs out).length := by
      simpa [tgtFam] using targetCall_callee_lt C
    have hval : interp V (blockRuleFrame (tgtRs out).length a ρ (pp.toBlockShape.rulePrefixAt j)
          pp.nP xs ys)
        (AnnotTerm.bvar (rc.rP + cA.2 + ((tgtRs out).length - 1 - Q.ihs.toList[q].callee)))
        = a Q.ihs.toList[q].callee := by
      rw [interp_bvar, blockRuleFrame,
        show rc.rP + cA.2 + ((tgtRs out).length - 1 - Q.ihs.toList[q].callee)
          = ((tgtRs out).length - 1 - Q.ihs.toList[q].callee)
            + ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
              ++ (ys.drop pp.nP).map (interp V ρ)).length by rw [hframeLen]; omega,
        consList_apply_add, chainFrame_apply hc]
    rw [hval]
    refine interp_congr_below V _ (rc.rP + cA.2 + 1) _ _ hb (fun k hk => ?_)
    cases k with
    | zero => rfl
    | succ k =>
      exact consList_below_indep _ _ _ k (by rw [hframeLen]; omega)
  dsimp only
  rw [hRB, hIH]
  exact heq

/-- **A stored rule's target run, with the facts every B3 row reads**:
the `(j, i)`-th `TargetRuleRun` (`targetRuleAt`) together with the rule
prefix, the constructor at the major, the parameters, the rule body's
and the recursor types' scoping (today's inversions of the same stored
family), the frame's openers (today's), the recomputed frame, width
and abstraction. -/
theorem tgtRuleAt_facts {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    ∃ (rc : RecShape) (rhs0 : Expr) (M : TargetMajor)
      (Q : ConLeche.TargetRuleRun μ F
        (ConLeche.consBlockRecsBareF pp.toBlockShape 0
          ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe) fe pp.toBlockShape
        (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r.1 rc.rP r.1.type M cA rhs0
        rhs),
      rc.rP = pp.toBlockShape.rulePrefixAt j ∧
      ConLeche.targetCtorAt M cA.1 = cA.1.type ∧
      M.ds = Q.fvsPref.take pp.toBlockShape.nP ∧
      Q.body.hasFvar = false ∧
      r.1.type.hasFvar = false ∧ r.1.type.looseBVarsBounded 0 = true ∧
      ConstsBound fe.env r.1.type ∧
      (∀ c', (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD c' 0
        ≤ (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD c' 0) ∧
      (∀ c',
        ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).hasFvar = false ∧
        ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
          = true ∧
        ConstsBound fe.env ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero))) ∧
      Q.fvsPref = blockRulePrefFvs pp.toBlockShape (tgtRs out) j ∧
      Q.fvsF = blockRuleFieldFvs pp.toBlockShape (tgtRs out) j i ∧
      tgtB pp.toBlockShape (tgtRs out) j i = rc.rP + cA.2 ∧
      tgtFrame μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) j i
        = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
            Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
              pp.toBlockShape.large)) ∧
      (Q.bodyO, Q.ihs) = tgtAbs μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) j i := by
  obtain ⟨rc, rhs0, M, Q, hrc, hmem, hds, hPref, hFld, hBody, hFn, hAbs⟩ :=
    targetRuleAt R hr hcA hrhs
  have hrP : rc.rP = pp.toBlockShape.rulePrefixAt j := by
    simp only [BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, hrc]; rfl
  have hct : ConLeche.targetCtorAt M cA.1 = cA.1.type := by
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hmem
    simp [ConLeche.targetCtorAt, ht]
  obtain ⟨hTf, -, hTres, hTb, hallRhs⟩ :=
    ConLeche.checkBlockRecK_facts h r (List.mem_of_getElem? hr)
  obtain ⟨hfvRhs, -⟩ := hallRhs rhs (List.mem_of_getElem? hrhs)
  have hPrefEq : Q.fvsPref = blockRulePrefFvs pp.toBlockShape (tgtRs out) j := hPref.trans rfl
  have hcrestEq : Q.crest = blockRuleCrest pp.toBlockShape (tgtRs out) j i := by
    have hc := Q.hcrest
    rw [hct, hds, instPisWith_eq_instPisAt] at hc
    rw [blockRuleCrest, blockRuleCtorOf_eq hr hcA, ← hPrefEq, hc, Option.getD_some]
  obtain ⟨-, hlenR, hallN⟩ := checkBlockRecK_recNames h
  refine ⟨rc, rhs0, M, Q, hrP, hct, hds, (stripLams_not_hasFvar _ Q.hstrip hfvRhs).2, hTf, hTb,
    constsBound_of_constsResolve _ hTres, fun c' => ?_, fun c' => ?_, hPrefEq, ?_,
    by rw [tgtB_at hr hcA, hrP], ?_, hAbs⟩
  · by_cases hc' : c' < pp.recs.length
    · obtain ⟨rc', -, hrc', -, -, -, -, nIdx, hmI⟩ := hallN c' hc'
      simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [show pp.toBlockShape.recs = pp.recs from rfl, hrc']
      simp only [BlockShape.majorIdxAt, BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD] at hmI
      rw [show pp.toBlockShape.recs = pp.recs from rfl, hrc'] at hmI
      simp only [Option.map_some, Option.getD_some] at hmI ⊢
      omega
    · simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_none (by omega)]
      simp
  · by_cases hc' : c' < (tgtRs out).length
    · have hr' : (tgtRs out)[c']? = some (tgtRs out)[c'] := List.getElem?_eq_getElem hc'
      have hg : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)
          = (tgtRs out)[c'].1.type := by
        simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
      rw [hg]
      obtain ⟨hf, -, hres, hb, -⟩ :=
        ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')
      exact ⟨hf, hb, constsBound_of_constsResolve _ hres⟩
    · have hg : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)
          = .sort .zero := by
        simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_none (by omega)]; rfl
      rw [hg]
      exact ⟨rfl, rfl, by simp⟩
  · rw [blockRuleFieldFvs, blockRuleCtorOf_eq hr hcA, ← hcrestEq, ← hrP, Q.hfld, Option.map_some,
      Option.getD_some]
  · rw [tgtFrame, ← hPref, ← hFld, ← hFn]
    congr 1
    simp only [tgtRP, List.getD_eq_getElem?_getD]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, hrc]; rfl

/-- **The target rule data are bound by their frames** (`heqB`'s two
rows at the target data): every `ih` term below the chain and the rule's
frame, the residue below the frame and the `ih` variables. -/
theorem tgtRule_below (hμ : μ.verifiedChecks = true) {F : Nat} {fe : FEnv}
    (mT : EnvModel V fe.env) {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    (hformer : ∀ cv ∈ cvTas, cv.type.hasFvar = false)
    (ψ : Name → Nat)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hCc : ConstsBound fe.env cA.1.type) :
    (∀ v ∈ tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env
        ψ j i,
      Term.bvarsBelow ((tgtRs out).length + pp.toBlockShape.rulePrefixAt j + cA.2) v.erase) ∧
    Term.bvarsBelow (pp.toBlockShape.rulePrefixAt j + cA.2
        + (tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env
            ψ j i).length)
      (tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env
        ψ j i).erase := by
  obtain ⟨rc, rhs0, M, Q, hrP, hct, hds, hbf, hTf, hTb, hTc, hle, hRT, -, -, hB, hFrEq, hAbs⟩ :=
    tgtRuleAt_facts h R hr hcA hrhs
  obtain ⟨⟨Bv, hBv, hBb⟩, hlam, -, -, -⟩ := targetRule_reads hμ mT ψ Q hle hbf hds hTf hTb hTc
    (by rw [hct]; exact hCf) (by rw [hct]; exact hCb) (by rw [hct]; exact hCc)
    (fun t ht => by obtain ⟨cv, hcv', rfl⟩ := List.mem_map.mp ht; exact hformer cv hcv') hRT
  have hlen : (tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env
      ψ j i).length = Q.ihs.size := by
    rw [tgtIhsAV, ← hAbs]; simp
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [tgtIhsAV, ← hAbs, hFrEq, hB] at hv
    obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp hv
    obtain ⟨q, hq, hget⟩ := List.getElem_of_mem hih
    have hq' : q < Q.ihs.size := by simpa using hq
    have hr' : Q.ihs[q]? = some ih := by
      rw [Array.getElem?_eq_getElem hq']; simpa using hget
    obtain ⟨Lr, hLr, -, hb⟩ := hlam q ih hr'
    obtain ⟨C⟩ := Q.call hih
    have hc : ih.callee < (tgtRs out).length := by
      simpa [tgtFam] using targetCall_callee_lt C
    have hLr' : denoteMeta mT.acval fe.env ψ (rc.rP + cA.2 + 1)
        (targetCallE (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP
          Q.fvsPref Q.fvsF Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel
            pp.toBlockShape.elim pp.toBlockShape.large))) (rc.rP + cA.2)
          (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) ih) = some Lr := hLr
    rw [hLr', Option.getD_some, AnnotTerm.erase_inst]
    have hq2 := bvarsBelow_inst (m := (tgtRs out).length + pp.toBlockShape.rulePrefixAt j + cA.2)
      (a := (AnnotTerm.bvar (rc.rP + cA.2 + ((tgtRs out).length - 1 - ih.callee))).erase)
      (show _ < _ by rw [hrP]; omega) Lr.erase 0
      (Term.bvarsBelow.mono (by rw [hrP]; omega) hb)
    simpa using hq2
  · have hRB : tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env
        ψ j i = Bv := by
      rw [tgtRbAV, ← hAbs, hB]
      simp only
      rw [hBv, Option.getD_some]
    rw [hRB, hlen, ← hrP]
    exact hBb

/-- **The target `ih` terms at the chain frame ARE the call λs at the
callees' chain values**: `L.inst (bvar (B + K-1-c))` read at
`consList X (chainFrame K a ρ)` is `L` at `a c` over `consList X ρ` —
the chain below the frame is invisible to `L` (bound below `B + 1`). -/
theorem tgtIhs_map_interp {F : Nat} {fe : FEnv} (mT : EnvModel V fe.env) {pp : BlockParts}
    {cvTas : List ConstantVal} {out : List (ConstantVal × TargetMajor × List Expr)}
    {ψ : Name → Nat} {j i : Nat} {cA : ConstantVal × Nat} {r : ConstantVal × List Expr × Nat
      × List (ConstantVal × Nat)} {rc : RecShape} {rhs0 rhs : Expr} {M : TargetMajor}
    {Q : ConLeche.TargetRuleRun μ F
      (ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe) fe pp.toBlockShape
      (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r.1 rc.rP r.1.type M cA rhs0 rhs}
    (hB : tgtB pp.toBlockShape (tgtRs out) j i = rc.rP + cA.2)
    (hFrEq : tgtFrame μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) j i
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)))
    (hAbs : (Q.bodyO, Q.ihs) = tgtAbs μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) j i)
    (hLb : ∀ q, q < Q.ihs.size →
      Term.bvarsBelow (rc.rP + cA.2 + 1)
        ((ihLamReads mT.acval fe.env ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref Q.fvsF
          (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
          (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) Q.ihs.toList).getD q default).erase)
    (a ρ : Nat → V) {X : List V} (hX : X.length = rc.rP + cA.2) :
    (tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env ψ j i).map
        (interp V (consList X (chainFrame (tgtRs out).length a ρ)))
      = ihValsAt a (consList X ρ) Q.ihs.toList
          (ihLamReads mT.acval fe.env ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref Q.fvsF
            (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
            (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
              pp.toBlockShape.large)) Q.ihs.toList) := by
  rw [tgtIhsAV, ← hAbs, hFrEq, hB]
  simp only [List.map_map]
  apply List.ext_getElem
  · simp [ihValsAt]
  intro q hq1 hq2
  have hq : q < Q.ihs.size := by simpa using hq1
  have hq' : q < Q.ihs.toList.length := by simpa using hq
  simp only [List.getElem_map, Function.comp, ihValsAt, List.getElem_range]
  have hgd : Q.ihs.toList.getD q default = Q.ihs.toList[q] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq']; rfl
  have hLr : (ihLamReads mT.acval fe.env ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref Q.fvsF
        (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large)) Q.ihs.toList).getD q default
      = (denoteMeta mT.acval fe.env ψ (rc.rP + cA.2 + 1)
          (targetCallE (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP
            Q.fvsPref Q.fvsF Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel
              pp.toBlockShape.elim pp.toBlockShape.large)))
            (rc.rP + cA.2) (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
              pp.toBlockShape.large)) Q.ihs.toList[q])).getD default := by
    rw [ihLamReads, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem hq']
    rfl
  have hb := hLb q hq
  rw [hLr] at hb
  rw [hgd, hLr, interp_inst0]
  obtain ⟨C⟩ := Q.call (List.getElem_mem hq')
  have hc : Q.ihs.toList[q].callee < (tgtRs out).length := by
    simpa [tgtFam] using targetCall_callee_lt C
  have hval : interp V (consList X (chainFrame (tgtRs out).length a ρ))
      (AnnotTerm.bvar (rc.rP + cA.2 + ((tgtRs out).length - 1 - Q.ihs.toList[q].callee)))
      = a Q.ihs.toList[q].callee := by
    rw [interp_bvar,
      show rc.rP + cA.2 + ((tgtRs out).length - 1 - Q.ihs.toList[q].callee)
        = ((tgtRs out).length - 1 - Q.ihs.toList[q].callee) + X.length by rw [hX]; omega,
      consList_apply_add, chainFrame_apply hc]
  rw [hval]
  refine interp_congr_below V _ (rc.rP + cA.2 + 1) _ _ hb (fun k hk => ?_)
  cases k with
  | zero => rfl
  | succ k => exact consList_below_indep _ _ _ k (by rw [hX]; omega)

set_option maxHeartbeats 1000000 in
/-- **`heqV`'s two target rows at one rule** — at a typed tuple and a
frame the prefix and the fields fit: every target `ih` term is valid at
the chain frame, and the residue is valid at the `ih` values
(`targetRule_graded`, `tgtIhs_map_interp`). -/
theorem tgtRule_valid (hμ : μ.verifiedChecks = true) {F : Nat} {fe : FEnv}
    (mpC : EnvModelM V μ fe.env) {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    (hformer : ∀ cv ∈ cvTas, cv.type.hasFvar = false)
    (ψ : Name → Nat)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hCc : ConstsBound fe.env cA.1.type)
    (hdF : ∀ (l : Nat) (x : Expr),
      (blockRuleFieldFvs pp.toBlockShape (tgtRs out) j i)[l]? = some x →
        denoteMeta mpC.base2.acval fe.env ψ (pp.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).getD l
              default))
    (hokPF : ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).getD l
              default))
    (ρ : Nat → V) (tup : List V) (hlen : tup.length = (tgtRs out).length)
    (htyp : ∀ mm, mm < (tgtRs out).length →
      tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval fe.env (tgtRs out) ψ mm))
    (ys : List V)
    (hys : SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
      ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i) ys) :
    (∀ v ∈ tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env ψ j i, AnnotValid V (consList ys (consList tup ρ)) v) ∧
    AnnotValid V (consList ((tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
        mpC.base2.acval fe.env ψ j i).map (interp V (consList ys (consList tup ρ))))
        (consList ys ρ))
      (tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env ψ j i) := by
  obtain ⟨rc, rhs0, M, Q, hrP, hct, hds, hbf, hTf, hTb, hTc, hle, hRT3, hPrefEq, hFldEq, hB,
    hFrEq, hAbs⟩ := tgtRuleAt_facts h R hr hcA hrhs
  have hcf := consList_eq_chainFrame hlen ρ
  -- the family's recursor types, read
  have hRT : ∀ c',
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).hasFvar = false ∧
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
        = true ∧
      ConstsBound fe.env ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)) ∧
      ∃ RTa : AnnotTerm,
        denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2)
          ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)) = some RTa ∧
        (∀ σ : Nat → V, WellDenotedV V σ RTa) := by
    intro c'
    obtain ⟨hf, hb, hcb⟩ := hRT3 c'
    refine ⟨hf, hb, hcb, ?_⟩
    by_cases hc' : c' < (tgtRs out).length
    · have hr' : (tgtRs out)[c']? = some (tgtRs out)[c'] := List.getElem?_eq_getElem hc'
      have hg : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)
          = (tgtRs out)[c'].1.type := by
        simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
      rw [hg] at hf ⊢
      obtain ⟨-, -, -, hread0, -, -, -, -, -, hwd⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ
      exact ⟨_, denoteMeta_depth_of_closed mpC.base2.acval_closed hf
          (fun k => liftN_eq_self_of_closed (closed_blockRecTyAV hμ mpC h hr' ψ) k 1)
          hread0 _, hwd⟩
    · have hg : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)
          = .sort .zero := by
        simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map]
        rw [List.getElem?_eq_none (by omega)]; rfl
      rw [hg]
      exact ⟨AnnotTerm.sort (Level.eval ψ Level.zero), by simp [denoteMeta],
        fun σ => ⟨trivial, trivial⟩⟩
  -- the frame's readings and grading
  have hpl : (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j).length
      = rc.rP := by
    rw [blockRulePdomsAV_length hμ mpC h hr, hrP]
  have hfl : (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).length
      = cA.2 := blockRuleFdomsAV_length_run (mpC := mpC) h hr hcA hrhs _
  have hdoms : ∀ (q : Nat) (x : Expr), (Q.fvsPref ++ Q.fvsF)[q]? = some x →
      denoteMeta mpC.base2.acval fe.env ψ q (Expr.fvarTypeD x)
        = some ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).reverse.getD
              (rc.rP + cA.2 - 1 - q) default) := by
    intro q x hx
    have hq := blockRuleHdoms_of (acval := mpC.base2.acval) (envT := fe.env)
      (ψ := ψ) (ihdoms := []) (fvsIh := []) hpl hfl rfl
      (openPisAtFvars_length _ Q.hpref) (openPisAtFvars_length _ Q.hfld) rfl
      (blockRulePdomsAV_reads hμ mpC h hr _ (by rw [← hrP]; exact Q.hpref))
      (by rw [hFldEq, hrP]; exact hdF)
      (fun l x hx => nomatch hx) q x (by simpa using hx)
    simpa using hq
  have hokΔ : ∀ q, q < rc.rP + cA.2 → ∀ ρ' : Nat → V,
      Sat V (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).reverse ρ' →
      WellDenotedV V (fun l => ρ' (l + (rc.rP + cA.2 - 1 - q) + 1))
        ((blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
            ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i).reverse.getD
              (rc.rP + cA.2 - 1 - q) default) := by
    intro q hq ρ' hsat
    have hk := blockRuleHokΔ_of (V := V) (ihdoms := []) hpl hfl rfl
      (fun l hl σ' ys hys => by
        have := hokPF l (by rw [← hrP]; omega) σ' ys (by simpa using hys)
        simpa using this) q (by simpa using hq) ρ' (by simpa using hsat)
    simpa using hk
  -- the callees' values are the typed tuple's
  have hR : ∀ ih ∈ Q.ihs.toList, ∀ RTa : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2)
          ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD ih.callee (.sort .zero)) = some RTa →
      (fun c => tup.getD c pt) ih.callee ∈ˢ interp V (consList (ys ++ []) ρ) RTa := by
    intro ih hih RTa hRTa
    obtain ⟨C⟩ := Q.call hih
    have hc : ih.callee < (tgtRs out).length := by
      simpa [tgtFam] using targetCall_callee_lt C
    have hr' : (tgtRs out)[ih.callee]? = some (tgtRs out)[ih.callee] :=
      List.getElem?_eq_getElem hc
    have hg : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD ih.callee (.sort .zero)
        = (tgtRs out)[ih.callee].1.type := by
      simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
    rw [hg] at hRTa
    obtain ⟨hf, -⟩ := ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')
    obtain ⟨-, -, -, hread0, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ
    have hcl := closed_blockRecTyAV hμ mpC h hr' ψ
    rw [denoteMeta_depth_of_closed mpC.base2.acval_closed hf
      (fun k => liftN_eq_self_of_closed hcl k 1) hread0 _] at hRTa
    obtain rfl := Option.some.inj hRTa
    rw [interp_closed (V := V) hcl _ ρ]
    exact htyp ih.callee hc
  have hys' : SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ j
      ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ j i) (ys ++ []) := by
    rw [List.append_nil]; exact hys
  have hin := Rules.RulesInputs.ofSem mpC ψ
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  obtain ⟨hlamG, Bv, hBv, hBG⟩ := targetRule_graded hμ hacl hin Q hle hbf hds hTf hTb hTc
    (by rw [hct]; exact hCf) (by rw [hct]; exact hCb) (by rw [hct]; exact hCc)
    (fun t ht => by obtain ⟨cv, hcv', rfl⟩ := List.mem_map.mp ht; exact hformer cv hcv')
    hRT (by rw [hpl]) (by rw [hfl]) hdoms hokΔ hys' (fun c => tup.getD c pt) hR
  obtain ⟨-, hlamB, -, -, -⟩ := targetRule_reads hμ mpC.base2 ψ Q hle hbf hds hTf hTb hTc
    (by rw [hct]; exact hCf) (by rw [hct]; exact hCb) (by rw [hct]; exact hCc)
    (fun t ht => by obtain ⟨cv, hcv', rfl⟩ := List.mem_map.mp ht; exact hformer cv hcv') hRT3
  have hLb : ∀ q, q < Q.ihs.size →
      Term.bvarsBelow (rc.rP + cA.2 + 1)
        ((ihLamReads mpC.base2.acval fe.env ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref
          Q.fvsF (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
          (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) Q.ihs.toList).getD q default).erase := by
    intro q hq
    obtain ⟨Lr, hLr, -, hb⟩ := hlamB q Q.ihs[q] (by simp [hq])
    have e2 : (ihLamReads mpC.base2.acval fe.env ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref
        Q.fvsF (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large)) Q.ihs.toList).getD q default = Lr := by
      rw [ihLamReads, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem hq]
      simp [hLr]
    rw [e2]; exact hb
  have hyl : ys.length = rc.rP + cA.2 := by
    rw [hys.length_eq, List.length_append, hpl, hfl]
  rw [hcf]
  refine ⟨fun v hv => ?_, ?_⟩
  · rw [tgtIhsAV, ← hAbs, hFrEq, hB] at hv
    obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp hv
    obtain ⟨q, hq, hget⟩ := List.getElem_of_mem hih
    have hq' : q < Q.ihs.size := by simpa using hq
    have hr' : Q.ihs[q]? = some ih := by
      rw [Array.getElem?_eq_getElem hq']; simpa using hget
    obtain ⟨Lr, hLr, hG⟩ := hlamG q ih hr'
    obtain ⟨Lr', hLr', -, hb⟩ := hlamB q ih hr'
    obtain rfl : Lr' = Lr := Option.some.inj (hLr'.symm.trans hLr)
    obtain ⟨C⟩ := Q.call hih
    have hc : ih.callee < (tgtRs out).length := by
      simpa [tgtFam] using targetCall_callee_lt C
    have hLr2 : denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + 1)
        (targetCallE (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP
          Q.fvsPref Q.fvsF Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel
            pp.toBlockShape.elim pp.toBlockShape.large))) (rc.rP + cA.2)
          (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) ih) = some Lr' := hLr'
    rw [hLr2, Option.getD_some, AnnotValid_inst0 V (a := AnnotTerm.bvar _) (by simp [AnnotValid]),
      interp_bvar,
      show rc.rP + cA.2 + ((tgtRs out).length - 1 - ih.callee)
        = ((tgtRs out).length - 1 - ih.callee) + ys.length by rw [hyl]; omega,
      consList_apply_add, chainFrame_apply hc]
    refine (AnnotValid_congr_below (V := V) Lr' (rc.rP + cA.2 + 1) _ _ hb (fun k hk => ?_)).mpr
      (by simpa using hG.2)
    cases k with
    | zero => rfl
    | succ k => exact consList_below_indep _ _ _ k (by rw [hyl]; omega)
  · have hRB : tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env ψ j i = Bv := by
      rw [tgtRbAV, ← hAbs, hB]
      simp only
      rw [hBv, Option.getD_some]
    rw [hRB, tgtIhs_map_interp mpC.base2 hB hFrEq hAbs hLb _ ρ hyl]
    simpa using hBG.2

/-! ## `heqP`'s target rows: the level footprint -/

section Params

variable {ps : List Name}

omit [SetTheory V] in
/-- A spine's arguments carry its footprint. -/
theorem lpDefF_mkAppN_args :
    ∀ (as : List Expr) {f : Expr}, lpDefF ps (Expr.mkAppN f as) = true →
      lpDefF ps f = true ∧ ∀ a ∈ as, lpDefF ps a = true
  | [], f, h => ⟨h, fun a ha => nomatch ha⟩
  | a :: as, f, h => by
    obtain ⟨h1, h2⟩ := lpDefF_mkAppN_args as (f := Expr.app f a) h
    simp only [lpDefF, Bool.and_eq_true] at h1
    refine ⟨h1.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h1.2
    · exact h2 x hx

omit [SetTheory V] in
/-- A Π-telescope's domains carry the type's footprint. -/
theorem lpDefF_piBinders :
    ∀ (e : Expr), e.allLevelParamsDefined ps = true → ∀ b ∈ e.piBinders.1,
      lpDefF ps b.1 = true := by
  intro e
  induction e with
  | forallE ty body m _ ihb =>
    intro h b hb
    simp only [Expr.allLevelParamsDefined, Bool.and_eq_true] at h
    simp only [Expr.piBinders, List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact lpDefF_of_allLevelParamsDefined _ h.1.1
    · exact ihb h.1.2 b hb
  | _ => intro _ b hb; simp [Expr.piBinders] at hb

omit [SetTheory V] in
theorem lpDefF_mkLamsOf :
    ∀ (bs : List (Expr × ConLeche.BinderMeta)) {body : Expr},
      (∀ b ∈ bs, lpDefF ps b.1 = true ∧ b.2.pw.paramsDefined ps = true) →
      lpDefF ps body = true → lpDefF ps (Expr.mkLamsOf bs body) = true
  | [], _, _, hb => hb
  | (ty, m) :: bs, body, hbs, hb => by
    have h0 := hbs (ty, m) List.mem_cons_self
    simp only [Expr.mkLamsOf, lpDefF, h0.1, h0.2,
      lpDefF_mkLamsOf bs (fun b hb' => hbs b (List.mem_cons_of_mem _ hb')) hb, Bool.and_self]

omit [SetTheory V] in
/-- **The target abstraction keeps the footprint**, and so do the calls'
index arguments it records: a call becomes an `ih` variable applied to
bound variables; its index arguments are the call's own arguments. -/
theorem lpDefF_targetAbstract {fr : ConLeche.TargetFrame} {B : Nat}
    (hle : ∀ c, fr.rPs.getD c 0 ≤ fr.mIs.getD c 0) :
    ∀ (d : Nat) (e : Expr) (acc : Array TargetIh) (e' : Expr) (acc' : Array TargetIh),
      ConLeche.targetAbstract fr B d e acc = some (e', acc') →
      lpDefF ps e = true →
      (∀ ih ∈ acc.toList, lpDefF ps ih.fv = true ∧ ∀ x ∈ ih.idx, lpDefF ps x = true) →
      lpDefF ps e' = true ∧
        ∀ ih ∈ acc'.toList, lpDefF ps ih.fv = true ∧ ∀ x ∈ ih.idx, lpDefF ps x = true
  | _, .bvar _, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨he, hacc⟩
  | _, .sort _, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨he, hacc⟩
  | _, .lit _, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨he, hacc⟩
  | _, .fvar _ _, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨he, hacc⟩
  | _, .const n us, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact ⟨he, hacc⟩
  | d, .lam ty b bi, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [lpDefF, Bool.and_eq_true] at he
    obtain ⟨hty, hacc1⟩ := lpDefF_targetAbstract hle d ty acc ty' acc1 h1 he.1.1 hacc
    obtain ⟨hb, hacc2⟩ := lpDefF_targetAbstract hle (d + 1) b acc1 b' acc2 h2 he.1.2 hacc1
    exact ⟨by simp [lpDefF, hty, hb, he.2], hacc2⟩
  | d, .forallE ty b bi, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [lpDefF, Bool.and_eq_true] at he
    obtain ⟨hty, hacc1⟩ := lpDefF_targetAbstract hle d ty acc ty' acc1 h1 he.1.1 hacc
    obtain ⟨hb, hacc2⟩ := lpDefF_targetAbstract hle (d + 1) b acc1 b' acc2 h2 he.1.2 hacc1
    exact ⟨by simp [lpDefF, hty, hb, he.2], hacc2⟩
  | d, .letE ty v b, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨v', acc2⟩, h2, ⟨b', acc3⟩, h3, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [lpDefF, Bool.and_eq_true] at he
    obtain ⟨hty, hacc1⟩ := lpDefF_targetAbstract hle d ty acc ty' acc1 h1 he.1.1 hacc
    obtain ⟨hv, hacc2⟩ := lpDefF_targetAbstract hle d v acc1 v' acc2 h2 he.1.2 hacc1
    obtain ⟨hb, hacc3⟩ := lpDefF_targetAbstract hle (d + 1) b acc2 b' acc3 h3 he.2 hacc2
    exact ⟨by simp [lpDefF, hty, hv, hb], hacc3⟩
  | d, .proj sn i x, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x', acc1⟩, h1, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [lpDefF] at he
      obtain ⟨hx, hacc1⟩ := lpDefF_targetAbstract hle d x acc x' acc1 h1 he hacc
      exact ⟨by simpa [lpDefF] using hx, hacc1⟩
  | d, .app f a, acc, _, _, h, he, hacc => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · next i c m idx hc =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ty, hty, h⟩ := h
      have hout : ∀ fv : Expr, (∃ n t, fv = .fvar n t) →
          lpDefF ps (Expr.mkAppN fv (ConLeche.structTeleVars m)) = true := by
        rintro fv ⟨n, t, rfl⟩
        refine lpDefF_mkAppN _ rfl (fun x hx => ?_)
        simp only [ConLeche.structTeleVars, List.mem_map] at hx
        obtain ⟨k, -, rfl⟩ := hx
        rfl
      split at h
      · next r hr =>
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨?_, hacc⟩
        refine lpDefF_mkAppN _ ?_ (fun x hx => ?_)
        · simp only [Array.getD]
          split
          · next hlt => exact (hacc _ (Array.getElem_mem_toList hlt)).1
          · rfl
        · simp only [ConLeche.structTeleVars, List.mem_map] at hx
          obtain ⟨k, -, rfl⟩ := hx
          rfl
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨hout _ ⟨_, _, rfl⟩, fun ih hih => ?_⟩
        rw [Array.toList_push, List.mem_append, List.mem_singleton] at hih
        rcases hih with hih | rfl
        · exact hacc ih hih
        · refine ⟨rfl, fun x hx => ?_⟩
          obtain ⟨rn, he', -⟩ := targetCall?_inv hc hle
          rw [he'] at he
          exact (lpDefF_mkAppN_args _ he).2 x
            (List.mem_append_left _ (List.mem_append_right _ hx))
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨f', acc1⟩, h1, ⟨a', acc2⟩, h2, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [lpDefF, Bool.and_eq_true] at he
      obtain ⟨hf, hacc1⟩ := lpDefF_targetAbstract hle d f acc f' acc1 h1 he.1 hacc
      obtain ⟨ha, hacc2⟩ := lpDefF_targetAbstract hle d a acc1 a' acc2 h2 he.2 hacc1
      exact ⟨by simp [lpDefF, hf, ha], hacc2⟩

/-- **`heqP`'s two target rows at one rule**: the target `ih` terms and
the residue read alike at two level valuations agreeing on the
recursor's parameters — the stored rule's footprint (the run's `hlp`)
survives the opening and the abstraction (`lpDefF_targetAbstract`), and
the call λs' binder domains are the fields' telescopes (K4). -/
theorem tgtRule_params {F : Nat} {fe : FEnv} (mT : EnvModel V fe.env) {pp : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
    {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {ψ₁ ψ₂ : Name → Nat} (hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) :
    tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env ψ₁ j i
      = tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env ψ₂ j i ∧
    tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env ψ₁ j i
      = tgtRbAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mT.acval fe.env ψ₂ j i := by
  obtain ⟨rc, rhs0, M, Q, hrP, hct, hds, hbf, hTf, hTb, hTc, hle, hRT3, hPrefEq, hFldEq, hB,
    hFrEq, hAbs⟩ := tgtRuleAt_facts h R hr hcA hrhs
  -- the opened body's footprint, and the abstraction's
  have hfvs : ∀ v ∈ (Q.fvsPref ++ Q.fvsF).reverse, ∃ (n : Nat) (t : Expr), v = .fvar n t := by
    intro v hv
    rcases List.mem_append.mp (List.mem_reverse.mp hv) with hv | hv
    · exact openPisAtFvars_mem_fvar Q.hpref v hv
    · exact openPisAtFvars_mem_fvar Q.hfld v hv
  have hbody : lpDefF r.1.levelParams (Q.body.instantiateList (Q.fvsPref ++ Q.fvsF).reverse 0)
      = true :=
    lpDefF_instantiateList hfvs _ 0
      (lpDefF_stripLams _ (lpDefF_of_allLevelParamsDefined _ Q.hlp) Q.hstrip)
  obtain ⟨hbO, hihs⟩ := lpDefF_targetAbstract (ps := r.1.levelParams) (B := rc.rP + cA.2)
    (fr := ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
      Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large))) hle 0 _ #[] _ _ Q.habs hbody (by simp)
  refine ⟨?_, ?_⟩
  · rw [tgtIhsAV, tgtIhsAV, ← hAbs, hFrEq, hB]
    refine List.map_congr_left fun ih hih => ?_
    -- the elimination datum names the recursor's parameters
    have hpw : (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large)).paramsDefined r.1.levelParams = true := by
      refine ConLeche.Level.zeronessOf_paramsDefined ?_
      unfold ConLeche.structElimLevel
      split
      · next hb =>
        simp only [Level.allParamsDefined, List.contains_iff_mem]
        rw [checkBlockRecK_lpsPin h hr, if_pos hb]
        exact List.mem_cons_self
      · rfl
    have hlam : lpDefF r.1.levelParams
        (targetCallE (ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP
          Q.fvsPref Q.fvsF Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel
            pp.toBlockShape.elim pp.toBlockShape.large))) (rc.rP + cA.2)
          (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) ih) = true := by
      refine lpDefF_mkLamsOf _ (fun b hb => ?_) ?_
      · obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
        refine ⟨?_, hpw⟩
        show lpDefF r.1.levelParams b0.1 = true
        simp only [ConLeche.targetFrameOf, List.getD_eq_getElem?_getD, List.getElem?_map] at hb0
        cases ht : Q.fnorm[ih.field]? with
        | none => rw [ht] at hb0; simp at hb0
        | some t =>
          rw [ht] at hb0
          exact lpDefF_piBinders t (Q.hfnormLp t (List.mem_of_getElem? ht)) b0 hb0
      · refine lpDefF_mkAppN _ rfl (fun x hx => ?_)
        rcases List.mem_append.mp hx with hx | hx
        · rcases List.mem_append.mp hx with hx | hx
          · obtain ⟨n, t, rfl⟩ := openPisAtFvars_mem_fvar Q.hpref x hx; rfl
          · exact (hihs ih hih).2 x hx
        · rw [List.mem_singleton] at hx
          subst hx
          refine lpDefF_mkAppN _ ?_ (fun y hy => ?_)
          · simp only [ConLeche.targetFrameOf, List.getD_eq_getElem?_getD]
            cases hf : Q.fvsF[ih.field]? with
            | none => rfl
            | some x =>
              obtain ⟨n, t, rfl⟩ := openPisAtFvars_mem_fvar Q.hfld x (List.mem_of_getElem? hf)
              rfl
          · simp only [ConLeche.structTeleVars, List.mem_map] at hy
            obtain ⟨k, -, rfl⟩ := hy
            rfl
    rw [denoteMeta_params_extF mT hq _ _ hlam]
  · rw [tgtRbAV, tgtRbAV, ← hAbs, hB]
    simp only
    rw [denoteMeta_params_extF mT hq _ _ hbO]

end Params

/-! ## The `ℓ = 0` arm at a rule binding no variable -/

section RuleZero

omit [SetTheory V] in
/-- **A frame without fields abstracts nothing**: no call is recognised
(a call names one of the frame's fields), so the walk is the identity,
and its success says no family recursor occurs — the term's constants
are bound below the recursors. -/
theorem targetAbstract_noFields {fr : ConLeche.TargetFrame} {B : Nat}
    (hf : fr.fields = []) (hle : ∀ c, fr.rPs.getD c 0 ≤ fr.mIs.getD c 0)
    {env' envC : Env}
    (hmono : ∀ n : Name, (env'.find? n).isSome = true →
      fr.recNames.contains n = false → (envC.find? n).isSome = true) :
    ∀ (d : Nat) (e : Expr) (acc : Array TargetIh) (e' : Expr) (acc' : Array TargetIh),
      ConLeche.targetAbstract fr B d e acc = some (e', acc') → e.hasFvar = false →
      e' = e ∧ acc' = acc ∧ (ConstsBound env' e → ConstsBound envC e)
  | _, .bvar _, acc, _, _, h, _ => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, fun _ => by simp⟩
  | _, .sort _, acc, _, _, h, _ => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, fun _ => by simp⟩
  | _, .lit _, acc, _, _, h, _ => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, fun _ => by simp⟩
  | _, .fvar _ _, _, _, _, _, hfv => by simp [Expr.hasFvar] at hfv
  | _, .const n us, acc, _, _, h, _ => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · next hn =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, rfl, fun hc => ?_⟩
      rw [constsBound_const] at hc ⊢
      exact hmono n hc (by simpa using hn)
  | d, .lam ty b bi, acc, _, _, h, hfv => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    obtain ⟨rfl, rfl, hc1⟩ := targetAbstract_noFields hf hle hmono d ty acc ty' acc1 h1 hfv.1
    obtain ⟨rfl, rfl, hc2⟩ := targetAbstract_noFields hf hle hmono (d + 1) b acc1 b' acc2 h2 hfv.2
    exact ⟨rfl, rfl, fun hc => by
      rw [constsBound_lam] at hc ⊢; exact ⟨hc1 hc.1, hc2 hc.2⟩⟩
  | d, .forallE ty b bi, acc, _, _, h, hfv => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    obtain ⟨rfl, rfl, hc1⟩ := targetAbstract_noFields hf hle hmono d ty acc ty' acc1 h1 hfv.1
    obtain ⟨rfl, rfl, hc2⟩ := targetAbstract_noFields hf hle hmono (d + 1) b acc1 b' acc2 h2 hfv.2
    exact ⟨rfl, rfl, fun hc => by
      rw [constsBound_forallE] at hc ⊢; exact ⟨hc1 hc.1, hc2 hc.2⟩⟩
  | d, .letE ty v b, acc, _, _, h, hfv => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨v', acc2⟩, h2, ⟨b', acc3⟩, h3, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
    obtain ⟨rfl, rfl, hc1⟩ := targetAbstract_noFields hf hle hmono d ty acc ty' acc1 h1 hfv.1.1
    obtain ⟨rfl, rfl, hc2⟩ := targetAbstract_noFields hf hle hmono d v acc1 v' acc2 h2 hfv.1.2
    obtain ⟨rfl, rfl, hc3⟩ := targetAbstract_noFields hf hle hmono (d + 1) b acc2 b' acc3 h3 hfv.2
    exact ⟨rfl, rfl, fun hc => by
      rw [constsBound_letE] at hc ⊢; exact ⟨hc1 hc.1, hc2 hc.2.1, hc3 hc.2.2⟩⟩
  | d, .proj sn i x, acc, _, _, h, hfv => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x', acc1⟩, h1, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.hasFvar] at hfv
      obtain ⟨rfl, rfl, hc1⟩ := targetAbstract_noFields hf hle hmono d x acc x' acc1 h1 hfv
      exact ⟨rfl, rfl, fun hc => by rw [constsBound_proj] at hc ⊢; exact hc1 hc⟩
  | d, .app f a, acc, _, _, h, hfv => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · next i c m idx hc =>
      obtain ⟨-, -, -, -, -, -, hi, -⟩ := targetCall?_inv hc hle
      rw [hf] at hi
      exact absurd hi (Nat.not_lt_zero _)
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨f', acc1⟩, h1, ⟨a', acc2⟩, h2, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hfv
      obtain ⟨rfl, rfl, hc1⟩ := targetAbstract_noFields hf hle hmono d f acc f' acc1 h1 hfv.1
      obtain ⟨rfl, rfl, hc2⟩ := targetAbstract_noFields hf hle hmono d a acc1 a' acc2 h2 hfv.2
      exact ⟨rfl, rfl, fun hc => by
        rw [constsBound_app] at hc ⊢; exact ⟨hc1 hc.1, hc2 hc.2⟩⟩

end RuleZero

end ConLeche.Model
