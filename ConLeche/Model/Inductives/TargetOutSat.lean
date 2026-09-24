module

public import ConLeche.Model.Inductives.TargetClass
public import ConLeche.Model.Inductives.TargetRuleData
public import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Inductives.BlockRecTyping
public import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Capstone
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Leaves
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.BridgeWfImp

public section

/-!
# An outside class's reading at the rule prefix (lane NESTIND, session 5)

At a recursor whose major is an outside container `I.{us} D⃗`, the rule
rows of the class (`tgtOutDec_core`, `TargetOutRow.lean`) read the
container's parameters `D⃗` at the rule prefix and need them to SATISFY
the container's parameter telescope at the key frame.  Both come from
the check's own run:

* the scoping of `D⃗` — the major type's first `nPc` arguments, whose
  free variables are the recursor type's first `nP` openers
  (`TargetTyEntry.outside_of`);
* F2-extended (NESTKERN s2, `TargetTyEntry.pinTys_of`): the
  instantiation `I.{us} D⃗` INFERS at the rule prefix `rP`, whose
  context is the recursor type's first `rP` binder readings
  (`blockRulePdomsAV`).  `infer_sound` grades its reading under that
  context, and a graded instance of a recorded member reads its
  parameters in the member's parameter telescope (`keyParamsFit`).

`tgtOutSat` packages the class reading premises of `tgtOutDec_core`
(`hul`, `hds`, `hdsa`, `hlenP`) and its satisfaction premise `hsat` at
every prefix spine fitting the rule's prefix domains — the only spines
the graph producer's rule rows quantify over.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal FEnv BlockShape TargetMajor RecShape
  CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

omit [SetTheory V] in
/-- An application's argument is scoped wherever the application is. -/
theorem wscoped_of_getAppArgs : ∀ {e : Expr} {d : Nat}, Expr.WScoped d e →
    ∀ x ∈ e.getAppArgs, Expr.WScoped d x
  | .app f a, d, h, x, hx => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    simp only [Expr.WScoped] at h
    rcases hx with hx | rfl
    · exact wscoped_of_getAppArgs h.1 x hx
    · exact h.2
  | .bvar _, _, _, _, hx | .fvar _ _, _, _, _, hx | .sort _, _, _, _, hx
  | .const _ _, _, _, _, hx | .lam _ _ _, _, _, _, hx | .forallE _ _ _, _, _, _, hx
  | .letE _ _ _, _, _, _, hx | .lit _, _, _, _, hx | .proj _ _ _, _, _, _, hx => by
    simp [Expr.getAppArgs] at hx

/-- **The `j`-th stored recursor's type-stage record**, at a
`targetRecCheck` run (either `outside`). -/
theorem targetEntryAt {mode : CheckMode} {F : Nat} {fe : FEnv} {p : BlockShape}
    {outside nested : Bool} {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : ConLeche.TargetRecRun mode F fe p outside nested block cvTas ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) :
    ∃ (rc : RecShape) (u : Level), p.recs[j]? = some rc ∧
      Nonempty (ConLeche.TargetTyEntry mode F fe p outside nested cvTas ctorsAs rc r.1
        (tgtMajor out j) u) := by
  obtain ⟨hlenT, hallT⟩ := ConLeche.targetRecTys_run R.htys
  obtain ⟨hlenO, hallO⟩ := ConLeche.targetRecsRules_run R.rules
  obtain ⟨t', ht', rfl⟩ : ∃ t', out[j]? = some t' ∧
      r = (t'.1, t'.2.2, t'.2.1.nIdx, t'.2.1.ctors) := by
    simp only [tgtRs, List.getElem?_map] at hr
    cases ho : out[j]? with
    | none => rw [ho] at hr; exact nomatch hr
    | some t' => rw [ho] at hr; exact ⟨t', rfl, (Option.some.inj hr).symm⟩
  have hj : j < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp ht').1
    rw [hlenO] at this; omega
  obtain ⟨rc, hrc⟩ : ∃ rc, p.recs[j]? = some rc := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨t, ht⟩ : ∃ t, R.tys[j]? = some t :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenT]; exact hj)⟩
  obtain ⟨rhssA, ho, -, -⟩ := hallO j rc t hrc ht
  obtain rfl : t' = (t.1, t.2.1, rhssA) := Option.some.inj (ht'.symm.trans ho)
  obtain ⟨cvRi, M, u⟩ := t
  obtain ⟨cvRi', M', u', ht2, ⟨E⟩⟩ := hallT j rc hrc
  obtain ⟨e1, e2, e3⟩ : cvRi = cvRi' ∧ M = M' ∧ u = u' := by
    have := ht.symm.trans ht2; simpa using this
  subst e1; subst e2; subst e3
  have hMaj : tgtMajor out j = M := by
    rw [tgtMajor, List.getD_eq_getElem?_getD, ht', Option.getD_some]
  exact ⟨rc, u, hrc, by rw [hMaj]; exact ⟨E⟩⟩

/-- **An outside major's parameters, scoped** (`TargetTyEntry.outside_of`):
each is an argument of the major's type, below the recursor type's first
`nP` binders — its free-variable leaves are openers of the recursor type
of index `< nP`. -/
theorem outsideDs_scoped {mode : CheckMode} {F : Nat} {fe : FEnv} {p : BlockShape}
    {outside nested : Bool} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {rc : RecShape} {cvRi : ConstantVal}
    {M : TargetMajor} {u : Level}
    (E : ConLeche.TargetTyEntry mode F fe p outside nested cvTas ctorsAs rc cvRi M u)
    (hM : M.member = none) (hw0 : Expr.WScoped 0 cvRi.type) :
    ∀ x ∈ M.ds, Expr.WScoped p.nP x ∧ x.looseBVarsBounded 0 = true ∧
      ∀ l ∈ x.fvarLeaves, l.1 < p.nP ∧ Expr.fvar l.1 l.2 ∈ E.fvs := by
  obtain ⟨-, -, -, -, -, -, hdsE, -, hsc, -, -⟩ := E.outside_of hM
  have hwM : Expr.WScoped rc.mI E.maj.fvarTypeD := by
    have := openPisAtFvars_typeWScoped (rc.mI + 1) E.hopen hw0 rc.mI E.maj E.hmaj
    rwa [Nat.zero_add] at this
  obtain ⟨tyM, hmajE⟩ := ConLeche.openPisAtFvars_index _ _ _ E.hopen rc.mI E.maj E.hmaj
  have hmajMem : E.maj ∈ E.fvs := List.mem_of_getElem? E.hmaj
  have hnil : cvRi.type.fvarLeaves = [] := fvarLeaves_nil_of_wscoped_zero hw0
  intro x hx
  rw [hdsE] at hx
  have hxA : x ∈ E.maj.fvarTypeD.getAppArgs := List.mem_of_mem_take hx
  obtain ⟨hb, hfv⟩ := hsc x (by rw [hdsE]; exact hx)
  have hwx : Expr.WScoped p.nP x :=
    ConLeche.WScoped.of_fvarsBelow (wscoped_of_getAppArgs hwM x hxA)
      (ConLeche.Expr.fvarB_le hfv)
  refine ⟨hwx, ConLeche.Expr.bvarB_le (by omega), fun l hl => ⟨?_, ?_⟩⟩
  · exact ConLeche.Expr.fvarLeaves_lt_of_wscoped hwx l hl
  · have hlM : l ∈ E.maj.fvarLeaves := by
      have h1 := ConLeche.fvarLeaves_getAppArgs hxA l hl
      rw [hmajE] at h1 ⊢
      simp only [Expr.fvarTypeD] at h1
      simp only [Expr.fvarLeaves, List.mem_cons]
      exact Or.inr h1
    rcases openPisAtFvars_leaves _ E.hopen l (Or.inr ⟨E.maj, hmajMem, hlM⟩) with h' | h'
    · rw [hnil] at h'; exact nomatch h'
    · exact h'

set_option maxHeartbeats 1000000 in
/-- **An outside class's reading at the rule prefix** (lane NESTIND,
session 5): at the `j`-th recursor, whose major is an OUTSIDE container
recorded as member `mm` of `D` (`TgtOutCls`), the major's parameters
read at the rule prefix (`dsa`), at the inductive's level arity, scoped,
as many as `D`'s parameters — and at every prefix spine fitting the
rule's prefix domains they satisfy `D`'s parameter telescope at the key
frame (F2-extended: the instantiation infers at the prefix). -/
theorem tgtOutSat (hμ : μ.verifiedChecks = true) {envC : Env} (mpC : EnvModelM V μ envC)
    (hcov : LfpCover mpC []) {F : Nat} {pp : ConLeche.BlockParts} {outside nested : Bool}
    {block : List ConstantInfo} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) :
    ∃ dsa : List AnnotTerm,
      DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j) (tgtMajor out j).ds dsa ∧
      (tgtMajor out j).lvls.length = cvI.levelParams.length ∧
      (∀ x ∈ (tgtMajor out j).ds, Expr.WScoped (tgtRP pp.toBlockShape j) x ∧
        x.looseBVarsBounded 0 = true) ∧
      (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)).length
        = (tgtMajor out j).ds.length ∧
      ∀ (σ : Nat → V) (xs : List V),
        SpineFit σ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j) xs →
        Sat V (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)).reverse
          (keyFrame dsa (tgtRP pp.toBlockShape j) (consList xs σ)) := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  generalize hMg : tgtMajor out j = M at hMo hcl E ⊢
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hMI : pp.toBlockShape.majorIdxAt j = rc.mI := by
    rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  rw [hRP]
  obtain ⟨-, -, -, -, -, hct, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  obtain ⟨-, ty, hinf⟩ := E.pinTys_of hMo
  obtain ⟨hw0, -⟩ := recStage_tyClosed h hr
  have hsc := outsideDs_scoped E hMo hw0
  -- the recursor type's reading: its binder data and its grading
  obtain ⟨fvs', concl', hop', -, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h hr ψ
  rw [hMI] at hop' hlenRds
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hop'.symm.trans E.hopen))
  have hrP : rc.rP ≤ rc.mI := E.hle
  have hnP : pp.toBlockShape.nP ≤ rc.rP := E.hroom
  -- the prefix context
  generalize hPd : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j = pdoms
  have hPdE : pdoms = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).take
      rc.rP).map (·.2.2) := by
    rw [← hPd, blockRulePdomsAV, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc,
      Option.getD_some]
  have hlenPd : pdoms.length = rc.rP := by
    rw [hPdE, List.length_map, List.length_take, hlenRds]; omega
  obtain ⟨oP, hopP⟩ := ConLeche.openPisAtFvars_prefix rc.rP (rc.mI + 1) _ 0 (by omega) E.hopen
  have hwsP := (ConLeche.openPisAtFvars_WScoped _ _ 0 hopP hw0).1
  rw [Nat.zero_add] at hwsP
  have hAa : ∀ i, i < rc.rP → ∀ x, E.fvs[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x) = some (pdoms.getD i default) := by
    intro i hi x hx
    obtain ⟨pd, hpd, -, hrd⟩ := hdomsR i x hx
    rw [hrd, hPdE, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      if_pos hi, hpd]
    rfl
  have hokTower : ∀ l, l < rc.rP → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((pdoms ++ [] ++ []).take l) ys →
      WellDenotedV V (consList ys σ) ((pdoms ++ [] ++ []).getD l default) := by
    intro l hl σ ys hys
    simp only [List.append_nil] at hys ⊢
    rw [hPdE] at hys ⊢
    exact prefixDoms_graded_of_tower
      (cc := blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      (by rw [hlenRds]; omega) (fun ρ' => by rw [← hTyE]; exact hwdTy ρ') hl hys
  have hokΔ := blockRuleHokΔ_of (V := V) (pdoms := pdoms) (fdoms := []) (ihdoms := [])
    (nF := 0) (nR := 0) hlenPd rfl rfl (by simpa using hokTower)
  simp only [List.reverse_nil, List.append_nil, List.nil_append, Nat.add_zero] at hokΔ
  have hent : ∀ i, i < rc.rP → pdoms.reverse[rc.rP - 1 - i]? = some (pdoms.getD i default) := by
    intro i hi
    rw [List.getElem?_reverse (by omega), hlenPd,
      show rc.rP - 1 - (rc.rP - 1 - i) = i from by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  -- the instantiation, framed
  obtain ⟨e, he⟩ : ∃ e, e = Expr.mkAppN (.const M.ind M.lvls) M.ds := ⟨_, rfl⟩
  rw [← he] at hinf
  have hleafE : ∀ l ∈ e.fvarLeaves, l.1 < pp.toBlockShape.nP ∧ Expr.fvar l.1 l.2 ∈ E.fvs := by
    intro l hl
    rw [he] at hl
    rcases ConLeche.fvarLeaves_mkAppN hl with h' | ⟨x, hx, hlx⟩
    · simp [Expr.fvarLeaves] at h'
    · exact (hsc x hx).2.2 l hlx
  have hleafP : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ E.fvs.take rc.rP := by
    intro l hl
    obtain ⟨hlt, hmem⟩ := hleafE l hl
    obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
    obtain ⟨ty', hty'⟩ := ConLeche.openPisAtFvars_index _ _ _ E.hopen pos _ hpos
    have h1 : l.1 = pos := by injection hty' with a b; omega
    have hpt : (E.fvs.take rc.rP)[pos]? = some (Expr.fvar l.1 l.2) := by
      rw [List.getElem?_take, if_pos (show pos < rc.rP by omega)]; exact hpos
    exact List.mem_of_getElem? hpt
  have hwsE : Expr.WScoped rc.rP e := he ▸
    Expr.WScoped.mkAppN (by simp [Expr.WScoped]) fun x hx =>
      (hsc x hx).1.mono hnP
  have hbE : e.looseBVarsBounded 0 = true := he ▸
    ConLeche.looseBVarsBounded_mkAppN (by simp [Expr.looseBVarsBounded]) fun x hx => (hsc x hx).2.1
  have hlbF : ∀ x ∈ E.fvs.take rc.rP, (Expr.fvarTypeD x).looseBVarsBounded 0 = true :=
    (openPisAtFvars_bounded _ hopP (recStage_tyClosed h hr).2).2
  have hLE : Expr.LeavesBounded e := leavesBounded_of_openers hlbF hleafP
  have hCE : CtxOk mpC.base2 ψ rc.rP pdoms.reverse e :=
    ctxOk_of_openers mpC.base2.acval_closed (Aa := fun i => pdoms.getD i default)
      (by rw [List.length_reverse, hlenPd])
      (fun i x hx => by
        simpa using ConLeche.openPisAtFvars_index _ _ _ hopP i x hx)
      hwsP
      (fun i x hx => by
        have hi : i < rc.rP := by
          have := (List.getElem?_eq_some_iff.mp hx).1
          rw [List.length_take] at this; omega
        rw [List.getElem?_take, if_pos hi] at hx
        exact hAa i hi x hx)
      hleafP (fun l hl => by have := (hleafE l hl).1; omega) hent
      (fun i hi ρ hρ => by
        have hq := hokΔ i hi ρ hρ
        rwa [List.getD_eq_getElem?_getD, hent i hi, Option.getD_some] at hq)
  -- its reading, graded
  have hinf' : ConLeche.inferTypeCore .verified envC F rc.rP e = .ok ty := hinf
  obtain ⟨wa, hwa⟩ := acceptedReads_of mpC.base2 ψ hinf' hwsE hbE hLE
  obtain ⟨-, -, -, -, hgr, -⟩ :=
    Rules.infer_sound (Rules.RulesInputs.ofSem mpC ψ) (Rules.inferTypeCore_bridge hinf')
      ⟨hwsE, hbE, hLE⟩ hCE hwa
  rw [he] at hwa
  obtain ⟨fa, dsa, hfa, hdsa, -⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨caps, hfI⟩ := hcl.hfind
  obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK hfI hfa
  -- the parameter count: off the first constructor's reading, or the
  -- recorded former's (a container without constructors)
  have hlenP : ∀ ψ', (D.params ψ').length = M.ds.length := by
    intro ψ'
    rw [hdsLen]
    by_cases hL : M.ctors = []
    · have hnc : ConLeche.nestContainer (envCtx envC) (D.member mm) = some (M.nPc, []) := by
        rw [hcl.hmem, ← targetCtorsOf_mkFEnv, hct, hL]
      obtain ⟨-, -, -, -, hlen, -⟩ := (hcov.own D hcl.hD).noCtors mm hcl.hmm M.nPc hnc
      exact hlen ψ'
    · have h0 : 0 < M.ctors.length := List.length_pos_iff.mpr hL
      obtain ⟨-, -, -, hcrd⟩ := mpC.lfp_ok D hcl.hD
      obtain ⟨cv0, nPc0, nF0, hf0, -, -, -, _A, -, hread0⟩ :=
        hcrd.2 mm hcl.hmm 0 (by rw [← hcl.hlen]; exact h0)
      rw [hcl.hctor 0 h0] at hf0
      obtain ⟨-, rfl, -⟩ : M.ctors[0].1 = cv0 ∧ M.nPc = nPc0 ∧ M.ctors[0].2 = nF0 := by
        simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hf0
        exact ⟨hf0.1, hf0.2.1, hf0.2.2⟩
      exact (hread0 ψ').1
  refine ⟨dsa, hdsa, hul, fun x hx => ⟨(hsc x hx).1.mono hnP, (hsc x hx).2.1⟩,
    hlenP _, fun σ xs hfit => ?_⟩
  have hsat : Sat V pdoms.reverse (consList xs σ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V σ) hfit
    simpa using this
  have hwa' : denoteMeta mpC.base2.acval envC ψ rc.rP
      (Expr.mkAppN (.const (D.member mm) M.lvls) (M.ds ++ [])) = some wa := by
    rw [List.append_nil, hcl.hmem]; exact hwa
  have := keyParamsFit mpC hcl.hD hcl.hmm (by rw [hcl.hmem]; exact hfI) (Nat.le_refl _) hwa'
    (by rw [hlenP]) (fun x hx => (hsc x hx).1.mono hnP) hdsa (consList xs σ) (hgr _ hsat)
  have e0 : dropV 0 (consList xs σ) = consList xs σ := funext fun _ => rfl
  rwa [Nat.sub_self, e0] at this

end ConLeche.Model
