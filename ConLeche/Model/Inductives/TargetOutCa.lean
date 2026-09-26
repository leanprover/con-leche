module

public import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutConcl
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.BlockRuleCaRun
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InstLevels
import ConLeche.Semantics.Tower.FixTower

public section

/-!
# The rule's conclusion `Ca` at an OUTSIDE class — `hCaB` (lane NESTIND, session 7)

The graph producer's `hCaB` (`graphRecPre_core`) reads the rule's
conclusion `Ca` (`tgtCaAV`: the recursor type instantiated at the rule's
prefix, the constructor's index expressions and the fired constructor,
read past the `ih` openers) at a decoding of the class, and asks it to
be the motive at the tagged element.  At a member class that is
`tgtKitCaB_at` (`TargetRowCerts.lean`); here it is stated at an outside
class — the major a container `C.{us} ds`, the class the recorded block
`D` holding `C` (`TgtOutCls`):

* `tgtOutCaAt` — the peel (`BlockRuleConclAt`) at the TARGET spellings:
  the prefix openers read to `paramBvarsAt`, the constructor's index
  arguments to `tgtEsAV`, the fired spine to `tgtMkAV`, each lifted past
  the `ih` openers;
* `tgtOutCaB` — `hCaB`: the index values at a hole fit of `D`'s
  constructor at the tuple `t` are `t`'s components (the fit's result
  indices, against the rule's own decoding `tgtOutDec`), the fired spine
  reads to the injection, and `blockRecCa_run` evaluates the peel.

The `ih` values enter only through their number: the `ih` block sits
above the conclusion's frame.
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

section Ca

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {nested : Bool} {block : List ConstantInfo}

/-- The recomputed recursor type is the stored one. -/
theorem tgtRecTy_at {out : List (ConstantVal × TargetMajor × List Expr)} {j : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) : tgtRecTy out j = r.1.type := by
  simp only [tgtRs, List.getElem?_map] at hr
  cases ho : out[j]? with
  | none => rw [ho] at hr; exact nomatch hr
  | some t =>
    rw [ho] at hr
    obtain rfl := Option.some.inj hr
    simp only [tgtRecTy, List.getD_eq_getElem?_getD, ho, Option.getD_some]

set_option maxHeartbeats 1000000 in
/-- **The fired spine at an outside class, read**: `C.{M.lvls} (M.ds ++ f⃗)`
reads at the rule's width as the constructor's leaf at the instantiation's
levels applied to the parameters' readings (lifted past the fields) and
the fields' variables. -/
theorem tgtOutMkAV_eq (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) :
    denoteMeta mpC.base2.acval envC ψ (tgtB pp.toBlockShape out j i)
        (Expr.mkAppN (.const cA.1.name (tgtMajor out j).lvls)
          ((tgtMajor out j).ds ++ tgtFieldFvs pp.toBlockShape out j i))
      = some (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i) ∧
    tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i
      = AnnotTerm.mkAppN (mpC.base2.acval cA.1.name
          (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
          ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map (AnnotTerm.liftN cA.2 · 0)
            ++ (List.range cA.2).map fun k =>
              AnnotTerm.bvar (tgtRP pp.toBlockShape j + cA.2 - 1 - (tgtRP pp.toBlockShape j + k))) := by
  obtain ⟨dsa, hdsa, hul, hds, -, -⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, -, hQcr, hQfF, -, -, -⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  obtain ⟨-, -, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  have hct' : tgtCtorOf out j i = cA := tgtCtorOf_at hr hcA
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
    rw [← tgtRs_ctors hr]; exact hcA
  have hiL : i < (tgtMajor out j).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
  have hcAi : (tgtMajor out j).ctors[i] = cA := (List.getElem?_eq_some_iff.mp hcAM).2
  have hiD : i < D.nctors mm := by rw [← hcl.hlen]; exact hiL
  have hfc0 := hcl.hctor i hiL
  rw [hcAi] at hfc0
  have hname : cA.1.name = D.ctorName mm i := Env.find?_name hfc0
  obtain ⟨-, -, -, hcrd⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv', nPc', nF', hf', -, hlpsC, -⟩ := hcrd.2 mm hcl.hmm i hiD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out j).nPc = nPc' ∧ cA.2 = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hlpsI : cvI.levelParams = cA.1.levelParams := by
    obtain ⟨caps, hfI⟩ := hcl.hfind
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC mm hcl.hmm
    rw [hcl.hmem, hfI] at hfm
    injection hfm with h; injection h with h1 _
    rw [h1, hlm]
  rw [hlpsI] at hul ⊢
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hB : tgtB pp.toBlockShape out j i = tgtRP pp.toBlockShape j + cA.2 := by
    rw [tgtB, hct']
  have hcr : ConLeche.instPisWith (tgtMajor out j).ds
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls) = some Q.crest := by
    have h0 := Q.hcrest
    simpa [ConLeche.targetCtorAt, hMo] using h0
  have hfld : ConLeche.openPisAtFvars cA.2 Q.crest (tgtRP pp.toBlockShape j)
      = some (Q.fvsF, Q.cbody) := by
    rw [hRP]; exact Q.hfld
  have hfc : envC.find? (D.ctorName mm i)
      = some (.ctorInfo cA.1 (tgtMajor out j).ds.length cA.2) := by
    rw [hdsLen]; exact hfc0
  have hconst : denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j + cA.2)
      (.const cA.1.name (tgtMajor out j).lvls)
      = some (mpC.base2.acval cA.1.name
          (Level.substFn ψ cA.1.levelParams (tgtMajor out j).lvls)) := by
    rw [hname]
    exact denoteMeta_const (ci := .ctorInfo cA.1 _ cA.2) hfc (by rw [hul]; rfl)
  have hdsaL : DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j + cA.2)
      (tgtMajor out j).ds
      ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map (AnnotTerm.liftN cA.2 · 0)) :=
    denoteMetaSpine_liftD mpC.base2.acval_closed hdsa (fun x hx => (hds x hx).1) cA.2
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hfld
  have hspF := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (tgtRP pp.toBlockShape j + cA.2) Q.fvsF (tgtRP pp.toBlockShape j) hidxF
  rw [openPisAtFvars_length _ hfld] at hspF
  have hmk0 := denoteMeta_mkAppN_of _ hconst (DenoteMetaSpine.append hdsaL hspF)
  have hmkE : tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i
      = (denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j + cA.2)
          (Expr.mkAppN (.const cA.1.name (tgtMajor out j).lvls)
            ((tgtMajor out j).ds ++ Q.fvsF))).getD default := by
    rw [tgtMkAV, hct', hB, hQfF]
  rw [hmk0, Option.getD_some] at hmkE
  refine ⟨?_, hmkE⟩
  rw [hB, ← hQfF, hmk0, hmkE]

set_option maxHeartbeats 2000000 in
/-- **The rule's conclusion at an outside class, peeled** (the twin of
`blockRuleCaAt_run`'s second half at the target spellings): read at the
rule's width plus `nR`, the target check's conclusion is the recursor
type's reading peeled along the prefix openers' bvars, the index
expressions and the fired spine, both lifted past the `nR` binders. -/
theorem tgtOutCaAt (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[i]? = some cA) {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (nR : Nat) :
    denoteMeta mpC.base2.acval envC ψ (tgtB pp.toBlockShape out j i + nR)
        (tgtConclExpr pp.toBlockShape out j i)
      = some ((denoteMeta mpC.base2.acval envC ψ (tgtB pp.toBlockShape out j i + nR)
          (tgtConclExpr pp.toBlockShape out j i)).getD default) ∧
    BlockRuleConclAt (tgtRP pp.toBlockShape j) cA.2 nR
      (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).map (·.liftN nR 0))
      ((tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i).liftN nR 0)
      ((denoteMeta mpC.base2.acval envC ψ (tgtB pp.toBlockShape out j i + nR)
          (tgtConclExpr pp.toBlockShape out j i)).getD default) := by
  have hacl := mpC.base2.acval_closed
  obtain ⟨dsa, hdsa, hul, hds, -, -⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  obtain ⟨cargs, -, -, hrdCb⟩ := tgtOutCbody hμ hcov h R hr hcA hrhs hMo hcl ψ
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, hPref, hQcr, hQfF, -, -, -⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  obtain ⟨-, -, -, -, -, -, hdsLen, -, -, -⟩ := E.outside_of hMo
  have hct' : tgtCtorOf out j i = cA := tgtCtorOf_at hr hcA
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by
    rw [← tgtRs_ctors hr]; exact hcA
  have hiL : i < (tgtMajor out j).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
  have hcAi : (tgtMajor out j).ctors[i] = cA := (List.getElem?_eq_some_iff.mp hcAM).2
  have hiD : i < D.nctors mm := by rw [← hcl.hlen]; exact hiL
  have hfc0 := hcl.hctor i hiL
  rw [hcAi] at hfc0
  have hname : cA.1.name = D.ctorName mm i := Env.find?_name hfc0
  obtain ⟨-, -, -, hcrd⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv', nPc', nF', hf', -, hlpsC, -⟩ := hcrd.2 mm hcl.hmm i hiD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out j).nPc = nPc' ∧ cA.2 = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hlpsI : cvI.levelParams = cA.1.levelParams := by
    obtain ⟨caps, hfI⟩ := hcl.hfind
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC mm hcl.hmm
    rw [hcl.hmem, hfI] at hfm
    injection hfm with h; injection h with h1 _
    rw [h1, hlm]
  rw [hlpsI] at hul
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfc0)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  -- the run's pieces at the recomputed spellings
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hB : tgtB pp.toBlockShape out j i = tgtRP pp.toBlockShape j + cA.2 := by
    rw [tgtB, hct']
  have hTy : tgtRecTy out j = r.1.type := tgtRecTy_at hr
  have hcr : ConLeche.instPisWith (tgtMajor out j).ds
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls) = some Q.crest := by
    have h0 := Q.hcrest
    simpa [ConLeche.targetCtorAt, hMo] using h0
  have hfld : ConLeche.openPisAtFvars cA.2 Q.crest (tgtRP pp.toBlockShape j)
      = some (Q.fvsF, Q.cbody) := by
    rw [hRP]; exact Q.hfld
  have hcb : tgtCbody pp.toBlockShape out j i = Q.cbody := by
    rw [tgtCbody, ← hQcr, hct', hfld]; rfl
  have hop : ConLeche.openPisAtFvars (tgtRP pp.toBlockShape j) r.1.type 0
      = some (Q.fvsPref, Q.oPref) := by
    rw [hRP]; exact Q.hpref
  have hE : tgtConclExpr pp.toBlockShape out j i = Q.concl := by
    rw [tgtConclExpr, ← hPref, hcb, ← hQfF, hct', hTy, Q.hconcl]; rfl
  -- scoping
  obtain ⟨hw₁, hb₁⟩ := recStage_tyClosed h hr
  have hf₁ : r.1.type.hasFvar = false :=
    (ConLeche.recStage_facts h _ (List.mem_of_getElem? hr)).1
  have hwPref := (ConLeche.openPisAtFvars_WScoped _ _ 0 hop hw₁).1
  rw [Nat.zero_add] at hwPref
  have hlenPref : Q.fvsPref.length = tgtRP pp.toBlockShape j := openPisAtFvars_length _ hop
  obtain ⟨doms, hinst⟩ : ∃ doms, Expr.instPisAt (tgtMajor out j).ds
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls)
        = some (doms, Q.crest) := by
    rw [ConLeche.instPisWith_eq_instPisAt] at hcr
    cases hq : Expr.instPisAt (tgtMajor out j).ds
        (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out j).lvls) with
    | none => rw [hq] at hcr; exact nomatch hcr
    | some pr =>
      rw [hq] at hcr
      exact ⟨pr.1, by rw [← Option.some.inj hcr]⟩
  have hwCr : Expr.WScoped (tgtRP pp.toBlockShape j) Q.crest :=
    (instPisAt_WScoped _ _ hinst (Expr.WScoped.of_not_hasFvar
      (by rw [Expr.hasFvar_instantiateLevelParams]; exact hCf))
      (fun a ha => (hds a ha).1)).2
  have hbCr : Q.crest.looseBVarsBounded 0 = true :=
    (instPisAt_bounded _ hinst (by rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hCb)
      (fun a ha => (hds a ha).2)).2
  obtain ⟨hwF, hwCb⟩ := ConLeche.openPisAtFvars_WScoped _ _ _ hfld hwCr
  have hbCb : Q.cbody.looseBVarsBounded 0 = true := (openPisAtFvars_bounded cA.2 hfld hbCr).1
  -- the index arguments' spine
  rw [hcb, hB] at hrdCb
  obtain ⟨vsA, hspA⟩ := denoteMetaSpine_getAppArgs hrdCb
  have hspEs := hspA.drop (tgtMajor out j).nPc
  have hesE : tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i
      = vsA.drop (tgtMajor out j).nPc := by
    rw [tgtEsAV, hcb, hB]
    exact DenoteMetaSpine.getD_eq hspEs
  have hwEs : ∀ a ∈ Q.cbody.getAppArgs.drop (tgtMajor out j).nPc,
      Expr.WScoped (tgtRP pp.toBlockShape j + cA.2) a :=
    fun a ha => Expr.WScoped.getAppArgs hwCb a (List.mem_of_mem_drop ha)
  -- the fired spine's reading
  have hmk0 : denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j + cA.2)
      (Expr.mkAppN (.const cA.1.name (tgtMajor out j).lvls) ((tgtMajor out j).ds ++ Q.fvsF))
      = some (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i) := by
    have := (tgtOutMkAV_eq hμ hcov h R hr hcA hrhs hMo hcl ψ).1
    rwa [hB, ← hQfF] at this
  have hwMk : Expr.WScoped (tgtRP pp.toBlockShape j + cA.2)
      (Expr.mkAppN (.const cA.1.name (tgtMajor out j).lvls) ((tgtMajor out j).ds ++ Q.fvsF)) := by
    refine Expr.WScoped.mkAppN (by simp [Expr.WScoped]) fun x hx => ?_
    rcases List.mem_append.mp hx with hx' | hx'
    · exact Expr.WScoped.mono (Nat.le_add_right _ _) (hds x hx').1
    · exact hwF x hx'
  -- the whole spine, `nR` binders deeper
  have hsp : DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j + cA.2 + nR)
      (Q.fvsPref ++ Q.cbody.getAppArgs.drop (tgtMajor out j).nPc
        ++ [Expr.mkAppN (.const cA.1.name (tgtMajor out j).lvls)
            ((tgtMajor out j).ds ++ Q.fvsF)])
      (paramBvarsAt (tgtRP pp.toBlockShape j) (tgtRP pp.toBlockShape j + cA.2 + nR)
        ++ (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).map (·.liftN nR 0)
        ++ [(tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ j i).liftN nR 0]) := by
    refine DenoteMetaSpine.append (DenoteMetaSpine.append
      (denoteMetaSpine_prefFvs hop hlenPref) ?_) ?_
    · rw [hesE]
      exact DenoteMetaSpine.liftDepth hacl nR hspEs hwEs
    · exact DenoteMetaSpine.liftDepth hacl nR (.cons hmk0 .nil)
        (fun a ha => by rw [List.mem_singleton.mp ha]; exact hwMk)
  have ha : ∀ a ∈ Q.fvsPref ++ Q.cbody.getAppArgs.drop (tgtMajor out j).nPc
        ++ [Expr.mkAppN (.const cA.1.name (tgtMajor out j).lvls)
            ((tgtMajor out j).ds ++ Q.fvsF)],
      Expr.WScoped (tgtRP pp.toBlockShape j + cA.2 + nR) a ∧ a.looseBVarsBounded 0 = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha' | ha'
    · rcases List.mem_append.mp ha' with ha'' | ha''
      · exact ⟨Expr.WScoped.mono (by omega) (hwPref a ha''),
          openPisAtFvars_fvars_closed hop a ha''⟩
      · exact ⟨Expr.WScoped.mono (Nat.le_add_right _ _) (hwEs a ha''),
          ConLeche.looseBVarsBounded_getAppArgs hbCb a (List.mem_of_mem_drop ha'')⟩
    · rw [List.mem_singleton] at ha'
      subst ha'
      refine ⟨Expr.WScoped.mono (Nat.le_add_right _ _) hwMk,
        ConLeche.looseBVarsBounded_mkAppN rfl (fun x hx => ?_)⟩
      rcases List.mem_append.mp hx with hx' | hx'
      · exact (hds x hx').2
      · exact openPisAtFvars_fvars_closed hfld x hx'
  -- the recursor type, read at the deep frame
  obtain ⟨-, -, -, hread, -⟩ := recStage_tyPis hμ mpC h hr ψ
  have htyD : denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape j + cA.2 + nR)
      r.1.type = some (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j) :=
    denoteMeta_depth_of_closed hacl hf₁
      (fun k => denoteMeta_closed mpC.base2.acval_erase mpC.base2.cval_closed hf₁ hb₁ hread 1 k)
      hread _
  obtain ⟨restA, hrest, hpeel⟩ := denoteMeta_instPisAtLift_peel hacl (acval_inst_self mpC.base2)
    _ Q.hconcl (Expr.WScoped.mono (Nat.zero_le _) hw₁) ha htyD hsp
  rw [hE, hB, hrest]
  exact ⟨rfl, hpeel⟩

set_option maxHeartbeats 2000000 in
/-- **Row `hCaB` at an outside class**: at a prefix `xs` fitting the
rule's prefix domains, a hole fit `fs` of `D`'s constructor `(mm, i)` at
the carrier of the key frame, at an index tuple `t` of the class, makes
the rule's conclusion (read past ANY `ih` values) the motive at the
tagged injection. -/
theorem tgtOutCaB (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {pp : ConLeche.BlockParts} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out j) D mm cvI) (ψ : Name → Nat) (ρ : Nat → V)
    {K : Nat} {uX nIdxX : Nat → Nat} (hc : j < K)
    (huX : uX j = D.u mm (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls))
    (hnX : nIdxX j = (tgtMajor out j).nIdx) (ℓ : Nat) (tup : Nat → List V → V)
    {xs : List V}
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j) xs)
    {i : Nat} (hi : i < blockRecNCt (tgtRs out) j) {t : V} {fs : List V}
    (ht : t ∈ˢ D.idx (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j) (consList xs ρ)) mm)
    (hf : D.HFits (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j) (consList xs ρ))
      (D.carrier (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j) (consList xs ρ))) t mm i fs) (g : V) :
    interp V (consList (tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
        mpC.base2.acval envC ψ ℓ tup ρ xs j i fs g) (consList (xs ++ fs) ρ))
        (tgtCaAV μ F (mkFEnv envC) (cvTas.map (·.type)) out mpC.base2.acval envC pp ψ j i)
      = blockRecMot K (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          uX nIdxX ρ xs
          (tagged j t (D.inj (Level.substFn ψ cvI.levelParams (tgtMajor out j).lvls) mm i fs)) := by
  -- the rule at `(j, i)`
  have hjr : i < r.2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hi; exact hi
  obtain ⟨cA, hcA⟩ : ∃ cA, r.2.2.2[i]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[i]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hjr)⟩
  -- the rule's own decoding at the fields
  have hsp := tgtOutSpF hμ hcov h R hr hcA hrhs hMo hcl ψ ρ hpref hf
  have hxl : xs.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length :=
    hpref.length_eq
  obtain ⟨hHF', hmk, hids'⟩ := tgtOutDec hμ hcov h R hr hcA hrhs hMo hcl ψ ρ hxl hsp
  -- the class's index clause at the key frame
  obtain ⟨dsa, hdsa, -, -, hlenP, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hMo hcl ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  have hsat := hsatF ρ xs hpref
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok D hcl.hD
  have hmN : mm < D.N := Nat.lt_of_lt_of_le hcl.hmm hC.kN
  have hIdx := hC.idxOk _ _ hsat mm hmN
  have hlenI := tgtOutIdx_len R hr hMo hcl ψ hlenP
  -- `t` is an index spine's tuple, and the rule's index values ARE that spine
  obtain ⟨is, hIs, rfl⟩ := mem_idxSet_elim ht
  generalize hvs : (tgtOutEs mpC D mm cvI.levelParams (tgtMajor out j) (tgtRP pp.toBlockShape j)
      ψ i).map (interp V (consList (xs ++ fs) ρ)) = vs at hHF' hids'
  have hvsE : vs = is := by
    apply List.ext_getElem (by rw [hids'.length_eq, hIs.length_eq])
    intro l hl₁ hl₂
    have hl := hl₁
    rw [hids'.length_eq] at hl
    obtain ⟨e, he, hv⟩ := hf.2.2 l hl
    obtain ⟨e', he', hv'⟩ := hHF'.2.2 l hl
    rw [he] at he'
    obtain rfl := Option.some.inj he'
    rw [projS_tupW hIdx hIs hl] at hv
    rw [projS_tupW hIdx hids' hl] at hv'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl₂, Option.getD_some] at hv
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl₁, Option.getD_some] at hv'
    rw [← hv', ← hv]
  subst hvsE
  -- the conclusion, evaluated
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hMI : pp.toBlockShape.majorIdxAt j = rc.mI := by
    rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  obtain ⟨-, -, -, -, hTyE, hlenRds, -, -, -, -⟩ := recStage_tyPis hμ mpC h hr ψ
  have hrds : (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).length
      = tgtRP pp.toBlockShape j + (tgtMajor out j).nIdx + 1 := by
    rw [hlenRds, hMI, E.hmI, hRP]
  have hihl : (tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
      mpC.base2.acval envC ψ ℓ tup ρ xs j i fs g).length
      = (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out j i).length := by
    rw [tgtIhv, blockRecIhvAt_length, tgtKeys, List.length_map, List.length_range]
  have hcon := (tgtOutCaAt hμ hcov h R hr hcA hrhs hMo hcl ψ
    (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out j i).length).2
  have hEs := tgtEsAV_outside hμ hcov h R hr hcA hrhs hMo hcl ψ
  have hxs : xs.length = tgtRP pp.toBlockShape j := by
    rw [hxl, blockRulePdomsAV_length hμ mpC h hr ψ]; rfl
  have hfsl : fs.length = cA.2 := by
    obtain ⟨as₁, as₂, heq, hp, hfs⟩ := spineFit_append_inv hsp
    have hl₁ : as₁.length = xs.length := by rw [hp.length_eq, hxl]
    obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl₁
    obtain ⟨rc', rhs0', M', u', Q, hrc', hMaj', hE', hPref', hCr', hQfF, -⟩ :=
      targetRuleAtG R hr hcA hrhs
    rw [hfs.length_eq, tgtFdomsAV, readOpenedDoms_length_eq, ← hQfF]
    exact openPisAtFvars_length _ Q.hfld
  have hesLen : (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ j i).length
      = (tgtMajor out j).nIdx := by
    have := congrArg List.length hvs
    rw [List.length_map, ← hEs, hIs.length_eq, hlenI] at this
    exact this
  have hCa := blockRecCa_run (is := vs) hcon hTyE hrds hesLen (recStage_tyBounds (V := V) hμ mpC h hr ψ).2
    hxs hfsl hihl rfl rfl hmk (by rw [hEs]; exact hvs)
  have hCaE : tgtCaAV μ F (mkFEnv envC) (cvTas.map (·.type)) out mpC.base2.acval envC pp ψ j i
      = (denoteMeta mpC.base2.acval envC ψ (tgtB pp.toBlockShape out j i
          + (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out j i).length)
          (tgtConclExpr pp.toBlockShape out j i)).getD default := rfl
  rw [hCaE, hCa, blockRecMot_tagged hc, huX, hnX, ← hlenI, isOfW_tupW hIdx hIs]

end Ca

end ConLeche.Model
