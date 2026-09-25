module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockDeclRun
public import ConLeche.Model.Inductives.TargetIhData
public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.TargetRuleData
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutGrade
import ConLeche.Model.Inductives.TargetOutConv
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.ContInst
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.NestedRecEqs
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.CheckerF
public import ConLeche.Model.Rules.RedSoundKit

public section

/-!
# The nested recursors' rule contract at every fired pair (lane RECREST, `data`)

`NestedRecRest.data` (L5/O12): `BlockRuleDataB` at the target rule data
at every `(recursor, constructor)` pair whose stored rule fires.  The
contract's five conjuncts split as the `eqB` rows did:

* the FIRST three (the frame's fit, the index readings, the fired
  spine) are about the rule's DATA — at a member major the block's
  (`blockRuleFit_tele`, `blockRuleHes_run`, `blockRuleHmk_run` at one
  recursor, through `tgt…_eq_block`), at an outside major the
  instantiated container constructor's (the NESTIND outside kit);
* the last two (the residue at the `ih` values, the λ-tower's fit) are
  about the rule's RIGHT-HAND SIDE and hold at ANY major from the
  target rule run (`tgtRuleResidueG`, `tgtRuleTowerFitG` below), given
  the first conjunct, the field readings (`hdF`) and the frame's
  grading (`hokPF`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Value-level fits along a peel -/

section Fits

open ConLeche.Model.Rules (PiChain piChain_succ_inv PiChain.inst)

/-- **The fit re-instantiates, under the ∀-chain guard** (the converse
of `teleFit_of_inst`). -/
theorem teleFit_inst_of {aa : AnnotTerm} :
    ∀ {L : List V} {E : AnnotTerm} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChain L.length E →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest →
      TeleFit V ρ (E.inst aa k) L rest := by
  intro L
  induction L with
  | nil =>
    intro E k ρ rest _ h
    rw [teleFit_nil_inv h, ← interp_inst]
    exact .nil
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc
    rw [AnnotTerm.inst_pi]
    cases h with
    | cons hmem hfit =>
      refine .cons (by rw [interp_inst]; exact hmem) ?_
      rw [cons_instE, ← shiftE_succ_cons y k ρ] at hfit
      exact ih (E := B) (k := k + 1) (ρ := cons y ρ) hB hfit

/-- `teleFit_inst_of` at the head binder. -/
theorem teleFit_inst0_of {aa : AnnotTerm} {L : List V} {E : AnnotTerm}
    {ρ : Nat → V} {rest : V} (hpc : PiChain L.length E)
    (h : TeleFit V (cons (interp V ρ aa) ρ) E L rest) :
    TeleFit V ρ (E.inst aa) L rest := by
  refine teleFit_inst_of (k := 0) hpc ?_
  rwa [shiftE_zero_zero, instE_zero]

/-- **A fit continues past a peel**: fitting a ∀-chain at a spine's
values followed by more values, the peel's residual fits the rest. -/
theorem teleFit_peel :
    ∀ (ws : List AnnotTerm) {T C : AnnotTerm} {σ : Nat → V} {fs : List V} {X : V},
      ConLeche.Model.AnnotTerm.peelPis T ws = some C →
      PiChain (ws.length + fs.length) T →
      TeleFit V σ T (ws.map (interp V σ) ++ fs) X → TeleFit V σ C fs X
  | [], T, C, σ, fs, X, hp, _, h => by
    obtain rfl : T = C := Option.some.inj hp
    simpa using h
  | w :: ws, T, C, σ, fs, X, hp, hpc, h => by
    have hpc' : PiChain ((ws.length + fs.length) + 1) T := by
      simpa [Nat.add_right_comm] using hpc
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc'
    simp only [ConLeche.Model.AnnotTerm.peelPis] at hp
    rw [List.map_cons, List.cons_append] at h
    cases h with
    | cons _ hfit =>
      exact teleFit_peel ws hp (PiChain.inst w 0 hB)
        (teleFit_inst0_of (by simpa using hB) hfit)

/-- **A fit moves between frames agreeing below the term's bound.** -/
theorem teleFit_congr_frame :
    ∀ (vals : List V) {T : AnnotTerm} {n : Nat} {ρ ρ' : Nat → V} {X : V},
      Term.bvarsBelow n T.erase → (∀ k, k < n → ρ k = ρ' k) →
      TeleFit V ρ T vals X → ∃ X', TeleFit V ρ' T vals X'
  | [], T, _, _, ρ', _, _, _, _ => ⟨_, .nil⟩
  | a :: as, _, n, ρ, ρ', X, hb, hag, h => by
    cases h with
    | cons hmem hfit =>
      simp only [AnnotTerm.erase_pi] at hb
      obtain ⟨hA, hB⟩ := hb
      obtain ⟨X', hX'⟩ := teleFit_congr_frame as (n := n + 1) (ρ := cons a ρ)
        (ρ' := cons a ρ') hB (fun k hk => by
          cases k with
          | zero => rfl
          | succ k => exact hag k (by omega)) hfit
      exact ⟨X', .cons (by rw [← interp_congr_below V _ n ρ ρ' hA hag]; exact hmem) hX'⟩

end Fits

section AnyMajor

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {outside nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC}

/-! ## The λ-tower's fit, at any major -/

/-- **`BlockRuleDataB`'s FIFTH conjunct at ANY major** (`blockRuleTowerFit_run`
at the target rule run): the rule's λ-domains, read, fit wherever the
openers' stored types do — the check's own binder-by-binder comparison
(`TargetRuleRun.hG2`) through `twoStageOpeners_spineFit`, the openers'
readings and gradings at the frame (`hdF`, `hokPF`), the λ-domains'
off the graded reading of the rule (`hokRa`). -/
theorem tgtRuleTowerFitG (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hDs : TgtDsOk envC (tgtRP pp.toBlockShape j) (tgtPrefFvs pp.toBlockShape out j)
      (tgtMajor out j).ds)
    (hCf : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).looseBVarsBounded 0 = true)
    {ψ : Name → Nat} {acv : Name → (Name → Nat) → AnnotTerm} {env₃ : Env} {Ra : AnnotTerm}
    (hread : denoteMeta acv env₃ ψ 0 rhs = some Ra)
    (hokRa : ∀ σ : Nat → V, WellDenotedV V σ Ra)
    (hcross : ∀ (l : Nat) (e : Expr), ConstsBound envC e →
      denoteMeta mpC.base2.acval envC ψ l e = denoteMeta acv env₃ ψ l e)
    (hdF : ∀ (l : Nat) (x : Expr), (tgtFieldFvs pp.toBlockShape out j i)[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
        = some ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default))
    (hokPF : ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default))
    {ρ : Nat → V} {as : List V}
    (hfit : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i) as) :
    ∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A →
      lds.length = pp.toBlockShape.rulePrefixAt j + cA.2 →
      SpineFit ρ (lds.map (·.2)) as := by
  intro lds A hlam hldslen
  obtain ⟨rc, rhs0, M, Q, hrP, -, hFld, -, -, -, hMaj, hPref⟩ :=
    tgtRuleAt_factsG (fe := ConLeche.mkFEnv envC) h R hr hcA hrhs
  subst hMaj
  have hds : TgtDsOk envC rc.rP Q.fvsPref (tgtMajor out j).ds := by
    rw [hPref, hrP]; exact hDs
  -- the stored recursor type and rule
  obtain ⟨hfvR, -, -, hbR, hallRhs⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  obtain ⟨hfvRhs, -, -, hbRhs⟩ := hallRhs rhs (List.mem_of_getElem? hrhs)
  -- the instantiated constructor's scoping
  have hcr := Q.hcrest
  rw [ConLeche.instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨doms, crest'⟩, hinstC, hcr'⟩ := Option.map_eq_some_iff.mp hcr
  obtain rfl : crest' = Q.crest := hcr'
  have hwC : Expr.WScoped rc.rP Q.crest :=
    (instPisAt_WScoped (d := rc.rP) _ _ hinstC (Expr.WScoped.of_not_hasFvar hCf)
      (fun a ha => (hds a ha).1)).2
  have hbC : Q.crest.looseBVarsBounded 0 = true :=
    (ConLeche.Verify.instPisAt_bounded _ hinstC hCb (fun a ha => (hds a ha).2.1)).2
  have hleafC : ∀ lf ∈ Q.crest.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ Q.fvsPref := by
    intro lf hlf
    rcases ConLeche.Verify.instPisAt_leaves _ hinstC lf (Or.inr hlf) with hq | hq
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hq; exact nomatch hq
    · obtain ⟨a, ha, hlfa⟩ := hq
      exact (hds a ha).2.2.2 lf hlfa
  -- lengths
  have hlenP : Q.fvsPref.length = rc.rP := ConLeche.Verify.openPisAtFvars_length _ Q.hpref
  have hlenF : Q.fvsF.length = cA.2 := ConLeche.Verify.openPisAtFvars_length _ Q.hfld
  have hlenPd : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr ψ, hrP]
  have hlenFd : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length = cA.2 := by
    rw [tgtFdomsAV, readOpenedDoms_length_eq, ← hFld, hlenF]
  -- the rule's λ-tower, read
  obtain ⟨Γ, C, htele, hΓlen, -, hdoms₀⟩ :=
    instLamsAt_denotePTele (acval := acv) (env := env₃) (φ := ψ) _ Q.hlams
      (blockRuleOpeners_index Q.hpref Q.hfld) hread
  obtain ⟨lds₀, hmap, hT⟩ := lamTele_mkLamsAV htele
  have hsplen : (Q.fvsPref ++ Q.fvsF).length = rc.rP + cA.2 := by
    rw [List.length_append, hlenP, hlenF]
  have hlen₀ : lds₀.length = rc.rP + cA.2 := by
    have hq : (lds₀.map (·.2)).length = Γ.reverse.length := by rw [hmap]
    simp only [List.length_map, List.length_reverse] at hq
    rw [hq, hΓlen, hsplen]
  obtain ⟨rfl, rfl⟩ : lds = lds₀ ∧ A = C :=
    mkLamsAV_length_inj (by rw [hldslen, hlen₀, hrP]) (hlam ▸ hT)
  have hlenLd : Q.ldoms.length = rc.rP + cA.2 := by
    rw [ConLeche.Verify.instLamsAt_length _ Q.hlams, hsplen]
  -- the openers' readings
  have hdA : ∀ (l : Nat) (x : Expr), (Q.fvsPref ++ Q.fvsF)[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ l (Expr.fvarTypeD x)
        = some ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default) := by
    intro l x hx
    rcases Nat.lt_or_ge l Q.fvsPref.length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hx
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      exact blockRulePdomsAV_reads hμ mpC h hr ψ (by rw [← hrP]; exact Q.hpref) l x hx
    · rw [List.getElem?_append_right hge, hlenP, hFld] at hx
      rw [hlenP] at hge
      have hq := hdF (l - rc.rP) x hx
      rw [← hrP, show rc.rP + (l - rc.rP) = l from by omega] at hq
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenPd,
        ← List.getD_eq_getElem?_getD]
      exact hq
  -- the tower's domains
  have hdB : ∀ l, l < rc.rP + cA.2 →
      denoteMeta mpC.base2.acval envC ψ l (Q.ldoms.getD l default)
        = some ((lds.map (·.2)).getD l default) := by
    intro l hl
    obtain ⟨x, hx⟩ : ∃ x, Q.ldoms[l]? = some x :=
      ⟨Q.ldoms[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hcb : ConstsBound envC x := by
      refine constsBound_of_constsResolve _ ?_
      have hres := Q.hldomsRes x (List.mem_of_getElem? hx)
      simp only [ConLeche.StructWalkers.plain] at hres
      rwa [ConLeche.constsResolveF_eq] at hres
    rw [List.getD_eq_getElem?_getD, hx, Option.getD_some, hcross l x hcb]
    have hd := hdoms₀ l x hx
    rw [Nat.zero_add] at hd
    rw [hd, hmap, getD_reverse_lt (by rw [hΓlen, hsplen]; exact hl), hΓlen]
  have hokB : ∀ l, l < rc.rP + cA.2 → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((lds.map (·.2)).take l) ys →
      WellDenotedV V (consList ys σ) ((lds.map (·.2)).getD l default) :=
    fun l hl σ ys hys =>
      mkLamsAV_doms_graded (b := A) (by rw [← hlam]; exact hokRa σ)
        (by rw [hlen₀]; exact hl) hys
  exact twoStageOpeners_spineFit (fuel := F) hμ mpC Q.hpref Q.hfld hfvR hbR hwC hbC hleafC
    Q.hlams hfvRhs hbRhs
    (by rw [List.length_append, hlenPd, hlenFd])
    (by rw [List.length_map, hlen₀]) hdA hdB
    (fun l hl => hokPF l (by rw [← hrP]; exact hl)) hokB
    (fun l hl => Q.hG2 l (by rw [List.length_map, hsplen]; exact hl))
    hfit


/-! ## The contract from its three DATA conjuncts, at any major -/

/-- **`BlockRuleDataB` at the target rule data, at ANY major, from its
first three conjuncts** (the rule's data rows, `hrow`): the residue is
`tgtRuleResidueCore` at the frame the first conjunct fits, β-reduced
through the rule's own λ-tower (`tgtRuleTower_run`, `blockRuleHRa_val`);
the tower's fit is `tgtRuleTowerFitG`.  Generic in the constructor
parameter count `nP`, the stored rule `rl`, the index readings `es0` and
the fired spine `mk0` — the rows are the caller's. -/
theorem tgtRuleDataB_of_rows (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    (hnd : ((tgtRs out).map (·.1.name)).Nodup)
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {es0 : (Name → Nat) → Nat → Nat → List AnnotTerm} {mk0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    {Rr : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}
    {m₃ : EnvModel V (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC (tgtRs out) s
      (blockRecEqs nCt (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') es0
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ') mk0
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ')))
    (hleafCl : ∀ (ψ : Name → Nat) (q : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC (tgtRs out) s
        (blockRecEqs nCt (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') es0
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ') mk0
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ')) ψ q).erase))
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
        ((blockRecEqs nCt (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') es0
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ') mk0
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ')) ψ) ρ)
    (hformer : ∀ cv ∈ cvTas, cv.type.hasFvar = false)
    {φ : Name → Nat} {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {nP : Nat} {rl : ConLeche.RecRule} {ctorTy : (Name → Nat) → AnnotTerm}
    (hDs : TgtDsOk envC (tgtRP pp.toBlockShape j) (tgtPrefFvs pp.toBlockShape out j)
      (tgtMajor out j).ds)
    (hCf : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt (tgtMajor out j) cA.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound envC (ConLeche.targetCtorAt (tgtMajor out j) cA.1))
    (hdF : ∀ (ψ : Name → Nat) (l : Nat) (x : Expr),
      (tgtFieldFvs pp.toBlockShape out j i)[l]? = some x →
        denoteMeta mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
          = some ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default))
    (hokPF : ∀ ψ : Name → Nat, ∀ l, l < pp.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).getD l default))
    (hread : ∀ us : List Level, us.length = r.1.levelParams.length →
      denoteMeta m₃.acval (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC)
          (Level.substFn φ r.1.levelParams us) 0 rhs
        = some (blockRuleRaOf m₃.acval (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) rhs
            (Level.substFn φ r.1.levelParams us)))
    (hokRa : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      WellDenotedV V ρ (blockRuleRaOf m₃.acval (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) rhs ψ))
    -- the rule's DATA rows: the contract's first three conjuncts
    (hrow : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0 →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
        xs.length = pp.toBlockShape.majorIdxAt j →
        ys.length = nP + cA.2 →
        usj.length = cA.1.levelParams.length →
        Level.substFn φ cA.1.levelParams usj
          = Level.substFn φ cA.1.levelParams
              (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
                (pp.toBlockShape.rulePrefixAt j)).1 →
        (∀ lvls pins, ConLeche.RecRule.fire rl = .nested lvls pins →
          ∀ q, q < nP → ∀ vpa : AnnotTerm,
            denoteMeta mpC.base2.acval envC φ (pp.toBlockShape.rulePrefixAt j)
              (openRev 0 (pp.toBlockShape.rulePrefixAt j)
                ((pins.getD q default).instantiateLevelParams r.1.levelParams us))
              = some vpa →
            interp V ρ (ys.getD q default)
              = interp V ρ (AnnotTerm.instRevChain
                  (xs.take (pp.toBlockShape.rulePrefixAt j)) vpa)) →
        IotaIndexPin (V := V) ρ restC nP
          (pp.toBlockShape.majorIdxAt j) (pp.toBlockShape.rulePrefixAt j) xs →
        TeleFitPA V ρ
          (blockRecTyAV mpC.base2.acval envC (tgtRs out) (Level.substFn φ r.1.levelParams us) j)
          (xs ++ [AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
        TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
        SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out)
              (Level.substFn φ r.1.levelParams us) j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC
              (Level.substFn φ r.1.levelParams us) j i)
          ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ∧
        (es0 (Level.substFn φ r.1.levelParams us) j i).map
            (interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
              ++ (ys.drop nP).map (interp V ρ)) ρ))
          = (xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) ∧
        interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ)
            (mk0 (Level.substFn φ r.1.levelParams us) j i)
          = interp V ρ (AnnotTerm.mkAppN
              (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys)) :
    BlockRuleDataB (V := V) mpC pp nP (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) (tgtRs out) s nCt
      (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
      (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') es0
      (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
        mpC.base2.acval envC ψ') mk0
      (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
        mpC.base2.acval envC ψ')
      ctorTy φ j i r cA rl rhs := by
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hnest hidx hfitR hfitC
  obtain ⟨h1, h2, h3⟩ := hrow us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hnest hidx
    hfitR hfitC
  have hread' := hread us hus
  rw [hac] at hread'
  have hok' : ∀ ρ' : Nat → V, WellDenotedV V ρ' (blockRuleRaOf (blockRecAcv mpC.base2.acval envC
      (tgtRs out) s (blockRecEqs nCt (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') es0
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ') mk0
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
            mpC.base2.acval envC ψ'))) (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) rhs (Level.substFn φ r.1.levelParams us)) := by
    intro ρ'; rw [← hac]; exact hokRa _ ρ'
  have htow := tgtRuleTowerFitG hμ h R hr hcA hrhs hDs hCf hCb hread' hok'
    (fun l e hcb => blockRecDenote_cross_eq h _ l e hcb) (hdF _) (hokPF _) h1
  refine ⟨h1, h2, h3, fun a hleaf => ?_, htow⟩
  obtain ⟨lds, A, hlam, hlen⟩ := tgtRuleTower_run R j r hr i cA rhs hcA hrhs _ _ _ _ hread'
  exact blockRuleHRa_val hlam (hok' ρ).1 (htow lds A hlam hlen)
    (tgtRuleResidueCore hμ h R hnd hr hcA hrhs hac hleafCl hpre hDs hCf hCb hCc hformer hdF hokPF
      hread us hus hℓ ρ xs ys hxl hyl h1 a hleaf lds A hlam hlen)

/-! ## The DATA rows at a MEMBER major -/

omit [SetTheory V] in
/-- **The counting guard at ANY majors** (`blockRecCounting_run` without
the family-size facts): at a `Prop` result and a non-zero elimination
level the recorded guard (`RecFamFacts.small`, the block's own bit) says
the declared shape is large and there is at most one constructor. -/
theorem blockRecCountG {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) {uOf : Nat → Level}
    (hruns : ∀ c, c < (tgtRs out).length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (pp.toBlockShape.majorIdxAt c + 1)
          ((tgtRs out).getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (pp.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (pp.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0)
    (hw : Level.eval ψ pp.toBlockShape.resSort = 0) {c : Nat} (hc : c < (tgtRs out).length) :
    pp.toBlockShape.large = true ∧ pp.toBlockShape.numCtors ≤ 1 := by
  obtain ⟨R'⟩ := id h
  have humem := blockRecUOf_run R' hruns hc
  have hu0 : Level.eval ψ (uOf c) ≠ 0 := by
    rw [blockRecElimPin_run h hruns ψ hc]; exact hℓ
  have hallow : ConLeche.blockLargeElimAllowed pp.toBlockShape false = true := by
    rcases R'.fam.small with hg | hzero
    · exact hg
    · exact absurd (ConLeche.Level.isEquiv_sound (hzero _ humem) ψ) hu0
  obtain ⟨hl, -, -, hcn⟩ := blockLargeElim_counting hallow hw
  exact ⟨hl, hcn⟩

section Member

variable {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {isRec : Bool}
  {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}

/-- **The contract's three DATA conjuncts at a MEMBER major** of a family
with any majors: `blockRuleData3_run` at the fired recursor (its split
`blockRecTyShape_at`, the counting guard `blockRecCountG`), moved to the
target data by `tgt…_eq_block`. -/
theorem tgtDataRows_member (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    (hN : BlockNamesOk (V := V) (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf) cvTas)
    (hS : BlockCtorsStage (V := V) μ F (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A envI pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
      pp.lps cvTas pp.toBlockShape isRec A (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k)
    (hlfp : (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).toLfp ∈ mpC.lfpBlocks)
    {φ : Name → Nat} {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR j) (hms : (tgtMajor out j).member.isSome = true)
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {rl : ConLeche.RecRule} (hplain : ConLeche.RecRule.fire rl = .plain) :
    ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0 →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
        xs.length = pp.toBlockShape.majorIdxAt j →
        ys.length = pp.nP + cA.2 →
        usj.length = cA.1.levelParams.length →
        Level.substFn φ cA.1.levelParams usj
          = Level.substFn φ cA.1.levelParams
              (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
                (pp.toBlockShape.rulePrefixAt j)).1 →
        IotaIndexPin (V := V) ρ restC pp.nP
          (pp.toBlockShape.majorIdxAt j) (pp.toBlockShape.rulePrefixAt j) xs →
        TeleFitPA V ρ
          (blockRecTyAV mpC.base2.acval envC (tgtRs out) (Level.substFn φ r.1.levelParams us) j)
          (xs ++ [AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
        TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i
          (Level.substFn φ cA.1.levelParams usj)) ys restC →
        SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out)
              (Level.substFn φ r.1.levelParams us) j
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC
              (Level.substFn φ r.1.levelParams us) j i)
          ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop pp.nP).map (interp V ρ)) ∧
        (tgtEsAV pp.toBlockShape out mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).map
            (interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
              ++ (ys.drop pp.nP).map (interp V ρ)) ρ))
          = (xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) ∧
        interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop pp.nP).map (interp V ρ)) ρ)
            (tgtMkAV pp.toBlockShape out mpC.base2.acval envC
              (Level.substFn φ r.1.levelParams us) j i)
          = interp V ρ (AnnotTerm.mkAppN
              (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys) := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hM := blockModelAt_seam h hN hS hcore hlfp
  have hmr := blockMembersRun_seam hN hS hcore
  -- the member link and the constructor's facts
  obtain ⟨ms, hmsA, hctA, hlenms⟩ := recStage_ctorsAt (hm := hm) h hr
  have hmemk : pp.toBlockShape.recTgtAt j
      < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hmsA).1
  have hctM : (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt j) = r.2.2.2 := by
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hcj : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt j))[i]? = some cA := by rw [hctM]; exact hcA
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk i cA hcj
  obtain ⟨-, -, hcd, -⟩ := hcore.2.2.1 _ i cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  have hnP := TE.nP_le
  obtain ⟨uOf, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hk0 : 0 < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) hmemk
  have hctorRead : ∀ ψ : Name → Nat, denoteMeta mpC.base2.acval envC ψ 0 cA.1.type
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) := by
    intro ψ
    have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
      rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
    rw [blockRecCtorTy, hsel, hcd.read ψ]
    rfl
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC
  obtain ⟨h1, h2, h3⟩ := blockRuleData3_run (mem := pp.toBlockShape.recTgtAt) (jc := i)
    hM hμ h hm hr hcA hrhs hplain hcj ⟨hfindC, hlpsC, hcd⟩ hlpsC rfl hnP hmemk hctorRead
    (fun us _ => blockRuleFdomsAV_datum (hm := hm) h hr hcA hrhs hcore hmemk hcj hnP rfl _)
    (fun us _ => by
      rw [blockRuleEsAV_eq (hm := hm) h hr hcA hrhs hcd hCf hnP _]
      exact congrArg (List.map _) (essOfR_fixCtorDataList_getD hcj).symm)
    (fun us _ => by
      have hl := hS.lenPps 0 (Level.substFn φ r.1.levelParams us) hk0
      show (((ppsOf 0 _).take pp.toBlockShape.nP).map (·.2.2)).length = pp.toBlockShape.nP
      rw [List.length_map, List.length_take]
      exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hl.symm)))
    (fun us _ σ =>
      ⟨fun hσ => ((hS.frames _ hmemk i cA hcj).1 _ σ).mp (hS.paramsOf 0 hk0 _ σ hσ _ hmemk),
        fun hσ => hS.paramsOf _ hmemk _ σ (((hS.frames _ hmemk i cA hcj).1 _ σ).mpr hσ) 0 hk0⟩)
    (fun us _ ρ' => blockRecSplitOne_of_shape (blockRecTyShape_at hμ mpC h hmr _ ρ' hm hj))
    (fun us _ hne _ => by
      refine blockRecLarge_run h hruns (Level.substFn φ r.1.levelParams us) hj ?_
      rw [blockRecElimPin_run h hruns _ hj]
      exact hne)
    (fun us _ hne hw0 => by
      obtain ⟨-, hc⟩ := blockRecCountG h hruns _ hne hw0 hj
      rw [hctM, hlenms]
      exact Nat.le_trans (numCtorsOf_ge_of_mem (List.mem_of_getElem? hmsA)) hc)
    us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC
  rw [tgtFdomsAV_eq_block R hr hcA hrhs hms, tgtEsAV_eq_block R hr hcA hrhs hms,
    tgtMkAV_eq_block R hr hcA hrhs hms]
  exact ⟨h1, h2, h3⟩

end Member

end AnyMajor

end ConLeche.Model
