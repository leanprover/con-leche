module

public import ConLeche.Model.Inductives.TargetFrame
public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Verify.Inductives.BlockRecNames
import ConLeche.Verify.Inductives.BlockRecRun

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

end ConLeche.Model
