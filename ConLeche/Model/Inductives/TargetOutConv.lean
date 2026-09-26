module

public import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockHoleValid
import ConLeche.Model.Inductives.StructRead
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Semantics.Tower.BlockHoleChain
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.StructWF
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.EnvBound

public section

/-!
# The index clause's CONVERSE at an outside major (lane NESTIND, O13)

At an outside major `I.{us} D⃗ ı⃗` the target check compares the
recursor's index binder domains, binder by binder (`TargetTyEntry.hidx`),
with `targetIdxDoms`' outside arm: the container's type instantiated at
the levels and the parameters, opened at the rule prefix
(`openPisAtFvars M.nIdx ty rP`).  This file is that comparison's model
side, the twin of `blockRecIdxConv_run` (`BlockRecIdxConv.lean`) at a
container:

* `instFormer_read` (`ContN2.lean`) reads the instantiated former as the
  recorded index telescope `D.ids` substituted at the parameters'
  readings, so a spine fits the opened domains at the prefix exactly
  when it fits `D.ids` at the key frame (`tgtOutIdxFit_iff`);
* the opened domains are graded at the fitting spines — the stored
  former's reading is graded (`type_wellDenotedV`), the parameters'
  readings are (`tgtOutSatW`), and grading crosses the substitution
  (`WellDenoted_substAV`, `AnnotValid_substAV`);
* **`tgtOutIdxConv`** — at a prefix fitting the rule's prefix domains,
  index values fitting the container's index telescope at the key frame
  fit the recursor's index binders: `defeqDom_agree_at` position by
  position, at the context "recursor prefix ++ opened container
  indices" (the container side's list IS the context, so only the
  recursor side is walked);
* **`tgtOutConclTy`** — the graph kit's `hconclTy` at an outside class.
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

/-- A term with at least `n` leading syntactic binders strips `n`. -/
theorem stripPis_isSome_of_piCount : ∀ (n : Nat) (e : Expr), n ≤ piCount e →
    (e.stripPis n).isSome = true
  | 0, _, _ => rfl
  | n + 1, .forallE t b mb, h => by
    simp only [piCount] at h
    simp only [ConLeche.Expr.stripPis, Option.isSome_map]
    exact stripPis_isSome_of_piCount n b (by omega)
  | _ + 1, .bvar _, h | _ + 1, .fvar _ _, h | _ + 1, .sort _, h | _ + 1, .const _ _, h
  | _ + 1, .lit _, h | _ + 1, .app _ _, h | _ + 1, .lam _ _ _, h | _ + 1, .letE _ _ _, h
  | _ + 1, .proj _ _ _, h => by simp [piCount] at h

/-- **`targetIdxDoms` at an outside major**: the container's type
instantiated at the major's levels and parameters, opened at the rule
prefix. -/
theorem targetIdxDoms_outside {fe : FEnv} {p : BlockShape} {cvTas : List ConstantVal}
    {rP : Nat} {M : TargetMajor} (hM : M.member = none) {idoms : List Expr}
    (h : ConLeche.targetIdxDoms (m := ConLeche.CheckM) fe p cvTas rP M = .ok idoms) :
    ∃ cvI caps ty ifs rest, fe.find? M.ind = some (.indInfo cvI caps) ∧
      ConLeche.instPisWith M.ds (cvI.type.instantiateLevelParams cvI.levelParams M.lvls)
        = some ty ∧
      ConLeche.openPisAtFvars M.nIdx ty rP = some (ifs, rest) ∧
      idoms = ifs.map Expr.fvarTypeD := by
  unfold ConLeche.targetIdxDoms at h
  rw [hM] at h
  simp only at h
  split at h
  · next cvI caps hf =>
    split at h
    · next ty hty =>
      obtain ⟨x, hx, h⟩ := ConLeche.exceptBind_ok h
      obtain ⟨ifs, rest⟩ := x
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact ⟨cvI, caps, ty, ifs, rest, hf, hty, ConLeche.unwrapOr_ok hx, h.symm⟩
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

omit [SetTheory V] in
/-- A substituted telescope's entries are the entries substituted at
their own depth. -/
theorem substTele_getD (τ : Nat → AnnotTerm) :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) (k q : Nat), q < ab.length →
      ((AnnotTerm.substTele τ k ab).map (·.2.2)).getD q default
        = AnnotTerm.substAV τ ((ab.map (·.2.2)).getD q default) (k + q)
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, k, 0, _ => by simp [AnnotTerm.substTele]
  | _ :: ab, k, q + 1, h => by
    simp only [AnnotTerm.substTele, List.map_cons, List.getD_cons_succ]
    rw [substTele_getD τ ab (k + 1) q (by simpa using h)]
    rw [show k + 1 + q = k + (q + 1) by omega]

omit [SetTheory V] in
/-- A substituted telescope's prefix is the prefix's substitution. -/
theorem substTele_take (τ : Nat → AnnotTerm) :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) (k q : Nat),
      (AnnotTerm.substTele τ k ab).take q = AnnotTerm.substTele τ k (ab.take q)
  | [], _, q => by simp [AnnotTerm.substTele]
  | _ :: _, _, 0 => by simp [AnnotTerm.substTele]
  | _ :: ab, k, q + 1 => by
    simp only [AnnotTerm.substTele, List.take_succ_cons]
    rw [substTele_take τ ab (k + 1) q]

section Conv

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

set_option maxHeartbeats 4000000 in
/-- **THE INDEX CLAUSE'S CONVERSE AT AN OUTSIDE MAJOR** (O13; the twin of
`blockRecIdxConv_run`).  At a prefix fitting the rule's prefix domains,
index values fitting the container's recorded index telescope at the
key frame fit the recursor's index binders. -/
theorem tgtOutIdxConv (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs is : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j) xs →
      SpineFit (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs ρ))
        (D.ids mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)) is →
      SpineFit (consList xs ρ)
        ((((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)).drop
          (tgtRP pp.toBlockShape j)).take (tgtMajor out j).nIdx) is := by
  intro xs is hxfit hisfit
  obtain ⟨dsa, hdsa, hul, hds, hlenP, hsatF⟩ := tgtOutSatW hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  have hlenI0 := tgtOutIdx_len R hr hMo hcl ψ hlenP
  generalize hdsaG : tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j = dsa
    at hdsa hsatF hisfit ⊢
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hMI : pp.toBlockShape.majorIdxAt j = rc.mI := by
    rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hPdE : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)).take
          rc.rP := by
    rw [blockRulePdomsAV, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc,
      Option.getD_some, List.map_take]
  rw [hRP] at hds hdsa hsatF hisfit ⊢
  rw [hPdE] at hsatF hxfit
  -- the recursor type: its binder data, its grading
  obtain ⟨fvs', concl', hop', -, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h hr ψ
  rw [hMI] at hop' hlenRds
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hop'.symm.trans E.hopen))
  obtain ⟨hw0, hb0⟩ := recStage_tyClosed h hr
  obtain ⟨-, -, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  have hsc := outsideDs_scoped E hMo hw0
  have hmI := E.hmI
  have hnP : pp.toBlockShape.nP ≤ rc.rP := E.hroom
  -- the container side: `targetIdxDoms`' outside arm
  obtain ⟨cvI', caps', ty, ifs, rest, hf', hty, hopI, hidE⟩ := targetIdxDoms_outside hMo E.hidoms
  obtain ⟨caps, hfI⟩ := hcl.hfind
  rw [mkFEnv_find?, hfI] at hf'
  obtain ⟨rfl, rfl⟩ : cvI = cvI' ∧ caps = caps' := by simpa using hf'
  have hfM : envC.find? (D.member mm) = some (.indInfo cvI caps) := by rw [hcl.hmem]; exact hfI
  obtain ⟨hC, -, hrd, -⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv₂, caps₂, hf₂, hab⟩ := hrd mm hcl.hmm
  rw [hfM] at hf₂
  obtain ⟨rfl, rfl⟩ : cvI = cv₂ ∧ caps = caps₂ := by simpa using hf₂
  have hwfI := mpC.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfI)
  have hclI : cvI.type.hasFvar = false := hwfI.1
  have hbI : cvI.type.looseBVarsBounded 0 = true := hwfI.2.2.2.1
  obtain ⟨ab0, hta0, -, -⟩ := hab ψ
  have hstrip : (cvI.type.stripPis (tgtMajor out j).ds.length).isSome = true := by
    have hok := tailOk_of_read _ cvI.type rfl hta0
    obtain ⟨l1, -, l3⟩ := tail_instantiateLevelParams cvI.levelParams (tgtMajor out j).lvls cvI.type
    obtain ⟨k1, -⟩ := tail_instPisWith (tgtMajor out j).ds (l3.mpr hok) hty
    exact stripPis_isSome_of_piCount _ _ (by omega)
  generalize hψ' : Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls = ψ' at *
  have hψ'' := hψ'
  obtain ⟨abR, hmapR, hread⟩ := instFormer_read mpC hcl.hD hcl.hmm hfM hcl.hnd hul
    (by rw [hψ']; exact hlenP) hds hdsa hstrip hty
  rw [hψ'] at hmapR hread
  -- names
  generalize hnI : (tgtMajor out j).nIdx = nI at *
  generalize hτ : substTau (tgtMajor out j).ds.length rc.rP (fun i => dsa.getD i default) = τ
    at hread
  have hdl : dsa.length = (tgtMajor out j).ds.length := (DenoteMetaSpine.length_eq hdsa).symm
  have hkf : ∀ σ : Nat → V, keyFrame dsa rc.rP σ = substE V τ 0 σ := fun σ => by
    rw [← hτ]; exact keyFrame_eq_substE hdl σ
  have hlenAbR : abR.length = nI := by rw [← hlenI0, ← hmapR, List.length_map]
  -- the opened container indices read as the substituted telescope
  obtain ⟨pps, bI, hstI, -, -, hbindI⟩ := denoteMeta_openPis nI hopI hread
  rw [stripPisAV_mkPisAV_take _ _ _ (by rw [substTele_length]; omega)] at hstI
  have hppsE : pps = AnnotTerm.substTele τ 0 abR := by
    obtain ⟨h1, -⟩ := Prod.mk.inj (Option.some.inj hstI)
    rw [← h1, List.take_of_length_le (by rw [substTele_length]; omega)]
  subst hppsE
  -- the recursor's binder data, and its grading
  generalize hRds : blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j = rds at *
  have hwdR : ∀ ρ' : Nat → V, WellDenotedV V ρ'
      (mkPisAV rds (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)) :=
    fun ρ' => by rw [← hTyE]; exact hwdTy ρ'
  obtain ⟨dR, hdR⟩ : ∃ L, L = rds.map (·.2.2) := ⟨_, rfl⟩
  rw [← hdR] at hxfit hsatF ⊢
  have hlR : dR.length = rc.rP + nI + 1 := by rw [hdR, List.length_map, hlenRds, hmI]
  have gradR : ∀ i, i < rc.rP + nI + 1 → ∀ (ρ' : Nat → V) (zs : List V),
      SpineFit ρ' (dR.take i) zs → WellDenotedV V (consList zs ρ') (dR.getD i default) := by
    intro i hi ρ' zs hzs
    have := prefixDoms_graded_of_tower (V := V) (rds := rds) (rP := rds.length)
      (Nat.le_refl _) hwdR (l := i) (by omega) (ρ := ρ') (ys := zs)
      (by rw [List.take_length, ← hdR]; exact hzs)
    rwa [List.take_length, ← hdR] at this
  -- the container's side of the context
  obtain ⟨dI, hdI⟩ : ∃ L, L = (AnnotTerm.substTele τ 0 abR).map (·.2.2) := ⟨_, rfl⟩
  have hlI : dI.length = nI := by rw [hdI, List.length_map, substTele_length, hlenAbR]
  have FitIq : ∀ (q : Nat) (σ : Nat → V) (zs : List V), SpineFit σ (dI.take q) zs ↔
      SpineFit (keyFrame dsa rc.rP σ) ((D.ids mm ψ').take q) zs := by
    intro q σ zs
    rw [hdI, ← List.map_take, substTele_take, spineFit_substTele, ← hkf, ← hmapR, List.map_take]
  have FitI : ∀ (σ : Nat → V) (zs : List V), SpineFit σ dI zs ↔
      SpineFit (keyFrame dsa rc.rP σ) (D.ids mm ψ') zs := by
    intro σ zs
    have h1 := FitIq nI σ zs
    rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at h1
  -- the stored former's reading is graded
  have hconsI := ConLeche.Semantics.Env.find?_mem hfI
  obtain ⟨abF, htaF, hmapF, -⟩ := hab ψ'
  have hwdF : ∀ ρ' : Nat → V, WellDenotedV V ρ' (mkPisAV abF (.sort (D.w ψ'))) :=
    mpC.type_wellDenotedV _ hconsI ψ' _ htaF
  have hparsL : (D.pars mm ψ').length = (tgtMajor out j).ds.length :=
    (hC.parsLen mm hcl.hmm ψ').trans hlenP
  have habFl : abF.length = (tgtMajor out j).ds.length + nI := by
    have := congrArg List.length hmapF
    rw [List.length_map, List.length_append, hparsL, hlenI0] at this
    exact this
  -- the opened container domains are graded along the context
  have GradI : ∀ q, q < nI → ∀ (σ : Nat → V) (zs is' : List V),
      SpineFit σ (dR.take rc.rP) zs → SpineFit (consList zs σ) (dI.take q) is' →
      WellDenotedV V (consList is' (consList zs σ)) (dI.getD q default) := by
    intro q hq σ zs is' hz hi'
    obtain ⟨hsat, hwdD⟩ := hsatF σ zs hz
    have hql : is'.length = q := by rw [hi'.length_eq, List.length_take, hlI]; omega
    have hτV : ∀ j', WellDenotedV V (shiftE q 0 (consList is' (consList zs σ))) (τ j') := by
      intro j'
      rw [← hql, shiftE_consList, ← hτ]
      unfold substTau
      split
      · apply hwdD
        show dsa.getD _ default ∈ dsa
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _
      · exact ⟨by simp [WellDenoted], by simp [AnnotValid]⟩
    have hsub : substE V τ q (consList is' (consList zs σ))
        = consList is' (keyFrame dsa rc.rP (consList zs σ)) := by
      have := substE_consList (V := V) τ is' 0 (consList zs σ)
      rw [Nat.add_zero, hql] at this
      rw [this, hkf]
    -- the recorded index domain, graded at the key frame
    have hWK : WellDenotedV V (consList is' (keyFrame dsa rc.rP (consList zs σ)))
        ((D.ids mm ψ').getD q default) := by
      have hl : (tgtMajor out j).ds.length + q < abF.length := by omega
      have hparsFit : SpineFit (fun i => consList zs σ (i + rc.rP)) (D.pars mm ψ')
          (dsa.map (interp V (consList zs σ))) :=
        spineFit_of_sat_consList' (by rw [List.length_map, hdl, hparsL])
          (hC.parsSat mm hcl.hmm ψ' _ hsat)
      have hys : SpineFit (fun i => consList zs σ (i + rc.rP))
          (((abF.take abF.length).map (·.2.2)).take ((tgtMajor out j).ds.length + q))
          (dsa.map (interp V (consList zs σ)) ++ is') := by
        rw [List.take_length, hmapF, List.take_append, List.take_of_length_le (by omega),
          hparsL, Nat.add_sub_cancel_left]
        exact SpineFit.append hparsFit ((FitIq q (consList zs σ) is').mp hi')
      have := prefixDoms_graded_of_tower (V := V) (rds := abF) (cc := .sort (D.w ψ'))
        (rP := abF.length) (Nat.le_refl _) hwdF hl hys
      rw [List.take_length, hmapF, getD_append_ge' (by omega), hparsL, Nat.add_sub_cancel_left,
        consList_append] at this
      exact this
    rw [hdI, substTele_getD τ abR 0 q (by omega), hmapR, Nat.zero_add]
    rw [← hsub] at hWK
    exact ⟨(WellDenoted_substAV τ _ q _ (fun j' => (hτV j').1)).mpr hWK.1,
      (AnnotValid_substAV τ _ q _ (fun j' => (hτV j').2)).mpr hWK.2⟩
  -- the context: the recursor's prefix, then the opened container indices
  obtain ⟨dC, hdC⟩ : ∃ L, L = dR.take rc.rP ++ dI := ⟨_, rfl⟩
  have hltake : (dR.take rc.rP).length = rc.rP := by rw [List.length_take, hlR]; omega
  have hlC : dC.length = rc.rP + nI := by rw [hdC, List.length_append, hltake, hlI]
  have C_lt : ∀ i, i < rc.rP → dC.getD i default = dR.getD i default := fun i hi => by
    rw [hdC, getD_append_lt' (by rw [hltake]; exact hi), getD_take' hi]
  have C_ge : ∀ i, rc.rP ≤ i → dC.getD i default = dI.getD (i - rc.rP) default := fun i hi => by
    rw [hdC, getD_append_ge' (by rw [hltake]; exact hi), hltake]
  have hsplitC : ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
      SpineFit ρ₁ (dR.take rc.rP) (ys.take rc.rP) ∧
        SpineFit (consList (ys.take rc.rP) ρ₁) dI (ys.drop rc.rP) := by
    intro ρ₁ ys hfit
    rw [hdC] at hfit
    obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_split hfit
    have hl1 : as₁.length = rc.rP := by rw [h1.length_eq, hltake]
    have e1 : ys.take rc.rP = as₁ := by rw [heq]; exact List.take_left' hl1
    have e2 : ys.drop rc.rP = as₂ := by rw [heq]; exact List.drop_left' hl1
    rw [e1, e2]; exact ⟨h1, h2⟩
  -- the two fvar lists
  have hidxR := ConLeche.openPisAtFvars_index _ _ _ E.hopen
  have hidxI := ConLeche.openPisAtFvars_index _ _ _ hopI
  have hwsR := fun i x hx => openPisAtFvars_typeWScoped _ E.hopen hw0 i x hx
  have hwTy : Expr.WScoped rc.rP ty := ConLeche.wscoped_instPisWith (fun x hx => (hds x hx).1)
    (Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hclI)) hty
  have hwTyL : Expr.WScoped 0 (cvI.type.instantiateLevelParams cvI.levelParams
      (tgtMajor out j).lvls) :=
    Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hclI)
  have hbTy : ty.looseBVarsBounded 0 = true :=
    ConLeche.looseBVarsBounded_instPisWith (fun x hx => (hds x hx).2)
      (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hbI) hty
  have hwsI := fun q x hx => openPisAtFvars_typeWScoped _ hopI hwTy q x hx
  have hlbRl := (ConLeche.Verify.openPisAtFvars_bounded _ E.hopen hb0).2
  have hlbIl := (ConLeche.Verify.openPisAtFvars_bounded _ hopI hbTy).2
  have hlenF : E.fvs.length = rc.rP + nI + 1 := by
    rw [ConLeche.Verify.openPisAtFvars_length _ E.hopen, hmI]
  have hlenIf : ifs.length = nI := ConLeche.Verify.openPisAtFvars_length _ hopI
  obtain ⟨LA, hLA⟩ : ∃ L, L = E.fvs.take rc.rP ++ ifs := ⟨_, rfl⟩
  obtain ⟨LB, hLB⟩ : ∃ L, L = E.fvs.take (rc.rP + nI) := ⟨_, rfl⟩
  have hlenTk : (E.fvs.take rc.rP).length = rc.rP := by rw [List.length_take, hlenF]; omega
  have hLAget : ∀ i x, LA[i]? = some x →
      (i < rc.rP ∧ E.fvs[i]? = some x) ∨ (rc.rP ≤ i ∧ ifs[i - rc.rP]? = some x) := by
    intro i x hx
    rw [hLA] at hx
    by_cases h1 : i < rc.rP
    · rw [List.getElem?_append_left (by rw [hlenTk]; exact h1), List.getElem?_take,
        if_pos h1] at hx
      exact Or.inl ⟨h1, hx⟩
    · rw [List.getElem?_append_right (by rw [hlenTk]; omega), hlenTk] at hx
      exact Or.inr ⟨by omega, hx⟩
  have hLBget : ∀ i x, LB[i]? = some x → i < rc.rP + nI ∧ E.fvs[i]? = some x := by
    intro i x hx
    rw [hLB, List.getElem?_take] at hx
    by_cases hi : i < rc.rP + nI
    · rw [if_pos hi] at hx; exact ⟨hi, hx⟩
    · rw [if_neg hi] at hx; exact absurd hx (by simp)
  have hlenLA : LA.length ≤ rc.rP + nI := by
    rw [hLA, List.length_append, hlenTk, hlenIf]; exact Nat.le_refl _
  have hlenLB : LB.length ≤ rc.rP + nI := by rw [hLB, List.length_take]; omega
  have shA : ∀ i x, LA[i]? = some x → ∃ ty, x = Expr.fvar i ty := fun i x hx => by
    rcases hLAget i x hx with ⟨_, h⟩ | ⟨h1, h⟩
    · obtain ⟨ty', h'⟩ := hidxR i x h; exact ⟨ty', by simpa using h'⟩
    · obtain ⟨ty', h'⟩ := hidxI _ x h; exact ⟨ty', by rw [h']; congr 1; omega⟩
  have shB : ∀ i x, LB[i]? = some x → ∃ ty, x = Expr.fvar i ty := fun i x hx => by
    obtain ⟨ty', h⟩ := hidxR i x (hLBget i x hx).2; exact ⟨ty', by simpa using h⟩
  have wA : ∀ i x, LA[i]? = some x → Expr.WScoped i (Expr.fvarTypeD x) := fun i x hx => by
    rcases hLAget i x hx with ⟨_, h⟩ | ⟨h1, h⟩
    · simpa using hwsR i x h
    · have := hwsI _ x h; rwa [show rc.rP + (i - rc.rP) = i from by omega] at this
  have wB : ∀ i x, LB[i]? = some x → Expr.WScoped i (Expr.fvarTypeD x) := fun i x hx => by
    simpa using hwsR i x (hLBget i x hx).2
  have lbA : ∀ x ∈ LA, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
    intro x hx
    rw [hLA] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hlbRl x (List.mem_of_mem_take hx)
    · exact hlbIl x hx
  have lbB : ∀ x ∈ LB, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := fun x hx =>
    hlbRl x (by rw [hLB] at hx; exact List.mem_of_mem_take hx)
  have rdA : ∀ i x, LA[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x) = some (dC.getD i default) := by
    intro i x hx
    rcases hLAget i x hx with ⟨h1, h⟩ | ⟨h1, h⟩
    · obtain ⟨pd, hpd, -, hrd⟩ := hdomsR i x h
      rw [hrd, C_lt i h1, hdR, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
    · obtain ⟨pd, hpd, -, hrd⟩ := hbindI _ x h
      rw [show rc.rP + (i - rc.rP) = i from by omega] at hrd
      rw [hrd, C_ge i h1, hdI, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
  have rdB : ∀ i x, LB[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x) = some (dR.getD i default) := by
    intro i x hx
    obtain ⟨pd, hpd, -, hrd⟩ := hdomsR i x (hLBget i x hx).2
    rw [hrd, hdR, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
  -- leaves
  have leafI : ∀ (q : Nat) (x : Expr), ifs[q]? = some x →
      ∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ LA := by
    intro q x hx lf hlf
    obtain ⟨ty', hty'⟩ := hidxI q x hx
    have hxx : lf ∈ x.fvarLeaves := by
      rw [hty'] at hlf ⊢
      simp only [Expr.fvarTypeD] at hlf
      simp only [Expr.fvarLeaves]
      exact List.mem_cons_of_mem _ hlf
    rcases openPisAtFvars_leaves nI hopI lf (Or.inr ⟨x, List.mem_of_getElem? hx, hxx⟩) with
      h' | h'
    · rcases ConLeche.fvarLeaves_instPisWith hty lf h' with h'' | ⟨a, ha, hla⟩
      · exact absurd (Expr.fvarLeaves_lt_of_wscoped hwTyL lf h'') (Nat.not_lt_zero _)
      · obtain ⟨hlt, hmem⟩ := (hsc a ha).2.2 lf hla
        obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
        obtain ⟨ty'', hty''⟩ := hidxR pos _ hpos
        have h1 : lf.1 = pos := by injection hty'' with a b; omega
        have hpt : (E.fvs.take rc.rP)[pos]? = some (Expr.fvar lf.1 lf.2) := by
          rw [List.getElem?_take, if_pos (show pos < rc.rP by omega)]; exact hpos
        rw [hLA]; exact List.mem_append_left _ (List.mem_of_getElem? hpt)
    · rw [hLA]; exact List.mem_append_right _ h'
  have leafR : ∀ (i : Nat) (x : Expr), i < rc.rP + nI → E.fvs[i]? = some x →
      ∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ LB := by
    intro i x hi hx lf hlf
    have hm := openerType_leaves E.hopen hw0 hx lf hlf
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
    obtain ⟨ty', hty'⟩ := hidxR k _ hk
    have hkl : lf.1 = 0 + k := by injection hty'
    have hlt : lf.1 < i := Expr.fvarLeaves_lt_of_wscoped (by simpa using hwsR i x hx) lf hlf
    rw [hLB]
    exact List.mem_of_getElem? (show (E.fvs.take (rc.rP + nI))[k]? = some _ from by
      rw [List.getElem?_take, if_pos (by omega)]; exact hk)
  -- THE INDUCTION on the index position
  have agreeI : ∀ q, q < nI → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
      interp V (consList (ys.take (rc.rP + q)) ρ₁) (dC.getD (rc.rP + q) default)
        = interp V (consList (ys.take (rc.rP + q)) ρ₁) (dR.getD (rc.rP + q) default) := by
    intro q
    induction q using Nat.strongRecOn with
    | _ q IH =>
    intro hq
    have hbelow : ∀ i, i < rc.rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        interp V (consList (ys.take i) ρ₁) (dR.getD i default)
          = interp V (consList (ys.take i) ρ₁) (dC.getD i default) := by
      intro i hi ρ₁ ys hfit
      by_cases h1 : i < rc.rP
      · rw [C_lt i h1]
      · have := IH (i - rc.rP) (by omega) (by omega) ρ₁ ys hfit
        rw [show rc.rP + (i - rc.rP) = i from by omega] at this
        exact this.symm
    have fitR : ∀ i, i ≤ rc.rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        SpineFit ρ₁ (dR.take i) (ys.take i) := by
      intro i hi ρ₁ ys hfit
      refine spineFit_congr_walk (by rw [List.length_take, List.length_take, hlC, hlR]; omega)
        ?_ (spineFit_take hfit (by rw [hlC]; omega))
      intro l hl
      rw [List.length_take] at hl
      rw [getD_take' (show l < i by omega), getD_take' (show l < i by omega), List.take_take,
        show min l i = l from by omega]
      exact (hbelow l (by omega) ρ₁ ys hfit).symm
    obtain ⟨xA, hxA⟩ : ∃ x, ifs[q]? = some x :=
      ⟨ifs[q]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨xB, hxB⟩ : ∃ x, E.fvs[rc.rP + q]? = some x :=
      ⟨E.fvs[rc.rP + q]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hxA' : LA[rc.rP + q]? = some xA := by
      rw [hLA, List.getElem?_append_right (by rw [hlenTk]; omega), hlenTk,
        show rc.rP + q - rc.rP = q from by omega]
      exact hxA
    have hxB' : LB[rc.rP + q]? = some xB := by
      rw [hLB, List.getElem?_take, if_pos (by omega)]; exact hxB
    have hdeq : ConLeche.isDefEqCore μ envC F (rc.rP + nI) (Expr.fvarTypeD xA)
        (Expr.fvarTypeD xB) = .ok true := by
      have h0 := E.hidx q (by rw [hidE, List.length_map, hlenIf]; exact hq)
      rw [hidE, getD_map_of_getElem? hxA, getD_map_of_getElem? (show
        (List.take (rc.mI - rc.rP) (List.drop rc.rP E.fvs))[q]? = some xB from by
          rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop]; exact hxB), hmI] at h0
      exact h0
    have hokC : ∀ i, i ≤ rc.rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        WellDenotedV V (consList (ys.take i) ρ₁) (dC.getD i default) := by
      intro i hi ρ₁ ys hfit
      by_cases h1 : i < rc.rP
      · rw [C_lt i h1]
        exact gradR i (by omega) ρ₁ (ys.take i) (fitR i (by omega) ρ₁ ys hfit)
      · rw [C_ge i (by omega)]
        obtain ⟨hs1, hs2⟩ := hsplitC ρ₁ ys hfit
        have hsplitY : ys.take i = ys.take rc.rP ++ (ys.drop rc.rP).take (i - rc.rP) := by
          rw [show i = rc.rP + (i - rc.rP) from by omega, List.take_add,
            show rc.rP + (i - rc.rP) - rc.rP = i - rc.rP from by omega]
        rw [hsplitY, consList_append]
        exact GradI (i - rc.rP) (by omega) ρ₁ _ _ hs1 (spineFit_take_any hs2 (i - rc.rP))
    have hokR : ∀ i, i ≤ rc.rP + q → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ dC ys →
        WellDenotedV V (consList (ys.take i) ρ₁) (dR.getD i default) := fun i hi ρ₁ ys hfit =>
      gradR i (by omega) ρ₁ (ys.take i) (fitR i hi ρ₁ ys hfit)
    exact defeqDom_agree_at (V := V) hμ mpC (fuel := F) (N := rc.rP + nI)
      (LA := LA) (LB := LB) (dA := dC) (dB := dR) (dC := dC) hlC hlenLA hlenLB shA shB wA wB
      lbA lbB rdA rdB (l := rc.rP + q) (by omega) hxA' hxB' (leafI q xA hxA)
      (leafR (rc.rP + q) xB (by omega) hxB) hdeq (fun _ _ _ _ _ => rfl) hbelow hokC hokR
  -- the spine `x⃗ ++ ı⃗` fits the context, and the walk
  have hxlen : xs.length = rc.rP := by rw [hxfit.length_eq, hltake]
  have hisI : SpineFit (consList xs ρ) dI is := (FitI _ _).mpr hisfit
  have hfitC : SpineFit ρ dC (xs ++ is) := by rw [hdC]; exact SpineFit.append hxfit hisI
  refine spineFit_congr_walk (by rw [hlI, List.length_take, List.length_drop, hlR]; omega)
    ?_ hisI
  intro q hq
  rw [hlI] at hq
  have e1 : consList (is.take q) (consList xs ρ) = consList ((xs ++ is).take (rc.rP + q)) ρ := by
    rw [← hxlen, List.take_length_add_append, consList_append]
  rw [e1, getD_take' hq, getD_drop', ← Nat.add_sub_cancel_left (n := rc.rP) (m := q),
    ← C_ge (rc.rP + q) (by omega), Nat.add_sub_cancel_left]
  exact agreeI q hq ρ (xs ++ is) hfitC

set_option maxHeartbeats 1000000 in
/-- **The major's domain at an outside class**, at a prefix fitting the
rule's prefix domains and index values fitting the recursor's index
binders: the container's carrier at the key frame, at the index tuple
(`keyLeaf` at the major's domain `I.{us} D⃗ ı⃗`). -/
theorem tgtOutMajor (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs is : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j) xs →
      SpineFit (consList xs ρ)
        ((((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)).drop
          (tgtRP pp.toBlockShape j)).take (tgtMajor out j).nIdx) is →
      interp V (consList (xs ++ is) ρ)
          (((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map
            (·.2.2)).getD (pp.toBlockShape.majorIdxAt j) default)
        = app (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
            (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
              (tgtRP pp.toBlockShape j) (consList xs ρ)) mm)
          (tupW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)) is) := by
  intro xs is hxfit hisfit
  obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  have hlenI0 := tgtOutIdx_len R hr hMo hcl ψ hlenP
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hMI : pp.toBlockShape.majorIdxAt j = rc.mI := by
    rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  obtain ⟨sI, hfn, -, -, -, hdsE, hdsLen, -, -, -⟩ := E.outside_of hMo
  obtain ⟨fvs', concl', hop', -, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h hr ψ
  rw [hMI] at hop' hlenRds ⊢
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hop'.symm.trans E.hopen))
  have hPdE : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)).take
          rc.rP := by
    rw [blockRulePdomsAV, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc,
      Option.getD_some, List.map_take]
  rw [hPdE] at hxfit
  rw [hRP] at hisfit ⊢
  generalize hRds : blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j = rds
    at hxfit hisfit hTyE hlenRds hdomsR ⊢
  have hmI := E.hmI
  have hxl : xs.length = rc.rP := by
    rw [hxfit.length_eq, List.length_take, List.length_map, hlenRds]; have := E.hle; omega
  have hisl : is.length = (tgtMajor out j).nIdx := by
    rw [hisfit.length_eq, List.length_take, List.length_drop, List.length_map, hlenRds]; omega
  obtain ⟨pd, hpd, -, hrdM⟩ := hdomsR rc.mI E.maj E.hmaj
  have hDM : (rds.map (·.2.2)).getD rc.mI default = pd.2.2 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hpd]; rfl
  have hsplitM : E.maj.fvarTypeD
      = Expr.mkAppN (.const (D.member mm) (tgtMajor out j).lvls)
          ((tgtMajor out j).ds ++ (E.fvs.drop rc.rP).take (rc.mI - rc.rP)) := by
    rw [hcl.hmem, ← hfn, hdsE, ← E.hmajIdx, List.take_append_drop, Expr.mkAppN_getApp]
  rw [hsplitM] at hrdM
  obtain ⟨caps, hfI⟩ := hcl.hfind
  have hisLen : ((E.fvs.drop rc.rP).take (rc.mI - rc.rP)).length = (tgtMajor out j).nIdx := by
    have hl := ConLeche.Verify.openPisAtFvars_length _ E.hopen
    rw [List.length_take, List.length_drop, hl]; omega
  obtain ⟨-, isa, hisa, hleaf⟩ := keyLeaf mpC hcl.hD hcl.hmm (by rw [hcl.hmem]; exact hfI)
    (show rc.rP ≤ rc.mI from E.hle) hrdM hlenP.symm
    (by rw [hisLen, hlenI0]) (fun x hx => by rw [← hRP]; exact (hds x hx).1)
    (by rw [← hRP]; exact hdsa)
  have hisaE : isa = (List.range (tgtMajor out j).nIdx).map
      fun k => AnnotTerm.bvar (rc.mI - 1 - (rc.rP + k)) := by
    have hF := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ) rc.mI
      ((E.fvs.drop rc.rP).take (rc.mI - rc.rP)) rc.rP (fun k x hx => by
        rw [List.getElem?_take, List.getElem?_drop] at hx
        split at hx
        · exact ConLeche.openPisAtFvars_index _ _ _ E.hopen _ x hx |>.imp fun _ h => by
            rw [h]; congr 1; omega
        · exact nomatch hx)
    rw [hisLen] at hF
    exact DenoteMetaSpine.unique hisa hF
  have hvals : isa.map (interp V (consList (xs ++ is) ρ)) = is := by
    rw [hisaE, show rc.mI = rc.rP + (tgtMajor out j).nIdx from hmI]
    exact map_fieldBvars hxl hisl
  have hwd : WellDenotedV V (consList (xs ++ is) ρ) pd.2.2 := by
    have htk : rds.take (rc.mI + 1) = rds := List.take_of_length_le (by omega)
    have hfitPI : SpineFit ρ (((rds.take (rc.mI + 1)).map (·.2.2)).take rc.mI) (xs ++ is) := by
      rw [htk, show rc.mI = rc.rP + (tgtMajor out j).nIdx from hmI, List.take_add]
      exact SpineFit.append hxfit hisfit
    have := prefixDoms_graded_of_tower (cc := blockRecConclAV mpC.base2.acval envC pp.toBlockShape
        (tgtRs out) ψ j) (rds := rds) (rP := rc.mI + 1) (by omega) (fun ρ' => by
          rw [← hTyE]; exact hwdTy ρ') (Nat.lt_succ_self _) hfitPI
    rwa [htk, hDM] at this
  obtain ⟨-, -, hmemE⟩ := hleaf _ hwd
  have hdrop : dropV (rc.mI - rc.rP) (consList (xs ++ is) ρ) = consList xs ρ := by
    funext k
    rw [dropV, consList_append, show rc.mI - rc.rP = is.length by rw [hisl]; omega,
      consList_apply_add]
  rw [hdrop, hvals] at hmemE
  rw [hDM, hmemE]

set_option maxHeartbeats 1000000 in
/-- **Row `hconclTy` at an outside class**: the conclusion read at a
prefix fitting the rule's prefix domains, at an index tuple of the
container's index set at the key frame and a carrier element there, is a
set of the checked elimination level. -/
theorem tgtOutConclTy (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V)
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j) xs)
    (i : V)
    (hi : i ∈ˢ D.idx (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j) (consList xs ρ)) mm)
    (x : V)
    (hx : x ∈ˢ app (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j) (consList xs ρ)) mm) i) :
    interp V
        (consList (xs ++ (isOfW (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
          (tgtMajor out j).nIdx i ++ [x])) ρ)
        (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large)) : V) := by
  obtain ⟨-, -, -, -, hlenP, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hlenI0 := tgtOutIdx_len R hr hMo hcl ψ hlenP
  have hi' : i ∈ˢ idxSet (D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j) (consList xs ρ))
      (D.ids mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)) := hi
  obtain ⟨is, hisfit, rfl⟩ := mem_idxSet_elim hi'
  obtain ⟨dsa, hdsa, -, -, -, hsatF'⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok D hcl.hD
  have hIdx := hC.idxOk _ _ (hsatF' ρ xs hpref) mm (Nat.lt_of_lt_of_le hcl.hmm hC.kN)
  rw [← hlenI0, isOfW_tupW hIdx hisfit, ← List.append_assoc]
  have hconv := tgtOutIdxConv hμ hcov h R hr hMo hcl ψ ρ xs is hpref hisfit
  have hmaj := tgtOutMajor hμ hcov h R hr hMo hcl ψ ρ xs is hpref hconv
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hMI : pp.toBlockShape.majorIdxAt j = rc.mI := by
    rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hPdE : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
      = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)).take
          rc.rP := by
    rw [blockRulePdomsAV, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc,
      Option.getD_some, List.map_take]
  obtain ⟨-, -, -, -, -, hlenRds, -, -, -, -⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
  rw [hMI] at hlenRds hmaj
  rw [hRP] at hconv hmaj
  rw [hPdE] at hpref
  have hmI := E.hmI
  -- the whole spine fits the recursor's binder data
  have hsplitL : (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)
      = ((((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)).take
          rc.rP)
        ++ ((((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)).drop
          rc.rP).take (tgtMajor out j).nIdx))
        ++ [((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2)).getD
          rc.mI default] := by
    have hlen : ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map
        (·.2.2)).length = rc.rP + (tgtMajor out j).nIdx + 1 := by
      rw [List.length_map, hlenRds, hmI]
    rw [hmI]
    generalize ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map
      (·.2.2)) = L at hlen ⊢
    rw [← List.take_add]
    have hd : L.drop (rc.rP + (tgtMajor out j).nIdx) = [L.getD (rc.rP + (tgtMajor out j).nIdx) default] := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    rw [← hd, List.take_append_drop]
  have hfull : SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map
      (·.2.2)) (xs ++ is ++ [x]) := by
    rw [hsplitL]
    refine SpineFit.append (SpineFit.append hpref hconv) ⟨?_, trivial⟩
    rw [hmaj, ← hRP]; exact hx
  have hsat : Sat V (((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map
      (·.2.2)).reverse) (consList (xs ++ is ++ [x]) ρ) := by
    simpa using sat_of_spineFit (Sat_nil V ρ) hfull
  obtain ⟨uOf, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hc : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨fvs, conclE, sty, hop, hinf, hens⟩ := hruns j hc
  have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
  rw [hrd] at hop
  have hu := blockRecConcl_univ hμ mpC h hr ψ hop hinf hens _ hsat
  rwa [blockRecElimPin_run h hruns ψ hc] at hu

end Conv

end ConLeche.Model
