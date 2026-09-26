module

public import ConLeche.Model.Inductives.TargetClassFrame
public import ConLeche.Verify.Inductives.NestCallRun
import ConLeche.Model.Inductives.TargetClassCall
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Model.Inductives.TargetCallKey
import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.StructBits
import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Semantics.Tower.FixSquashI
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetResidue

public section

/-!
# A call's data, off the target check's run (lane NESTIND, session 27)

A call target of the graph recursor (`tgtCall`) at the `(c, j)`-th rule is
one of the rule's `ih` keys: an `ih` entry of the abstraction, whose call
typing ran (`TargetCallRun`, and K.53′), a spine `bs` fitting the call's
telescope read at the rule's frame, the target the callee's index tuple of
the call's index readings, and the value the called field applied to
`bs` (`tgtCall_data`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor TargetIh RecShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Data

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {outside nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

set_option maxHeartbeats 8000000 in
/-- **A call target's data** (see the module docstring), at the rule's
frame fit. -/
theorem tgtCall_data (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas) (ψ : Name → Nat) (ρ : Nat → V)
    {c : Nat} (hc : c < (tgtRs out).length) {j : Nat} (hj : j < blockRecNCt (tgtRs out) c)
    {xs fs : List V}
    (hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs))
    (hxs : xs.length = pp.toBlockShape.rulePrefixAt c) (tup : Nat → List V → V) {v : V}
    (hcall : tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
      envC ψ tup ρ xs c j fs v) :
    ∃ (rc : RecShape) (rhs0 rhs : Expr) (cA : ConstantVal × Nat)
      (Q : ConLeche.TargetRuleRun μ F
        (ConLeche.consBlockRecsBareF pp.toBlockShape 0
          ((tgtRs out).map fun r => (r.1, r.2.2.1)) (mkFEnv envC)) (mkFEnv envC) pp.toBlockShape
        (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) (tgtRs out)[c].1 rc.rP
        (tgtRs out)[c].1.type (tgtMajor out c) cA rhs0 rhs)
      (ih : TargetIh) (bs : List V),
      (tgtRs out)[c].2.2.2[j]? = some cA ∧ rc.rP = pp.toBlockShape.rulePrefixAt c ∧
      Q.fvsF.length = cA.2 ∧ Q.fvsPref.length = rc.rP ∧
      (∀ l, l < cA.2 → ∃ ty, Q.fvsF[l]? = some (.fvar (rc.rP + l) ty)) ∧
      (∀ l, l < rc.rP → ∃ ty, Q.fvsPref[l]? = some (.fvar l ty)) ∧
      (∀ x ∈ Q.fvsF, Expr.WScoped (rc.rP + cA.2) x) ∧
      ih ∈ Q.ihs.toList ∧ ih.field < cA.2 ∧ fs.length = cA.2 ∧ xs.length = rc.rP ∧
      ConLeche.targetCallOk (ConLeche.fueledOps μ F) envC cA.1.name
        (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref Q.fvsF Q.fnorm
        (Q.fnorm.map fun t => t.piBinders.1)
        (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
          (ConLeche.targetHoles (cvTas.map (·.type)) (rc.rP + cA.2)))
        (rc.rP + cA.2) (cvTas.map (·.type)).length
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
        (ConLeche.targetFieldNfs (tgtMajor out c) cA.1.name Q.fvsF) ih = .ok () ∧
      ih.idx.length + rc.rP = (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD ih.callee 0 ∧
      (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD ih.callee 0 = rc.rP ∧
      ih.callee < (tgtRs out).length ∧
      (∀ x ∈ ih.idx, x.looseBVarsBounded
        ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length = true ∧
        ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF) ∧
      SpineFit (consList (xs ++ fs) ρ)
        ((teleDoms mpC.base2.acval envC ψ (rc.rP + cA.2) []
          (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1))).getD []) bs ∧
      (bs.length = ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length →
      v = tagged ih.callee (tup ih.callee (ih.idx.map fun x =>
          interp V (consList bs (consList (xs ++ fs) ρ))
            ((denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + bs.length)
              (x.instantiateList (locOpen (rc.rP + cA.2) bs.length) 0)).getD default)))
        (bs.foldl app (fs.getD ih.field pt))) := by
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  obtain ⟨rc, rhs0, Q, hrP, -, -, hB, hFrEq, hAbs, hbf, hTf, hTb, hTc, hle, hRT3, hdsOk, hCf, hCb,
    hCc, hfl, hF, -⟩ := tgtFrame_cls hμ hcov h R hcls hdR hS hcore hmr ψ hc hr hcA hrhs
  have hver : μ = .verified := CheckMode.eq_verified hμ
  -- the frame
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf hCb hCc
  have hlp : Q.fvsPref.length = rc.rP := ConLeche.Verify.openPisAtFvars_length _ Q.hpref
  have hlf : Q.fvsF.length = cA.2 := ConLeche.Verify.openPisAtFvars_length _ Q.hfld
  have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr ψ, hrP]
  have hxl : xs.length = rc.rP := by rw [hxs, hrP]
  have hfsl : fs.length = cA.2 := by
    have hsl := hsp.length_eq
    simp only [List.length_append, hpl, hfl] at hsl
    omega
  have hlenS : (xs ++ fs).length = rc.rP + cA.2 := by rw [List.length_append, hxl, hfsl]
  -- the frame's variables
  have hvarF : ∀ l, l < cA.2 → ∃ ty, Q.fvsF[l]? = some (.fvar (rc.rP + l) ty) := by
    intro l hl
    have hlt : rc.rP + l < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hFr.reverse_idx (rc.rP + l) _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    refine ⟨ty, ?_⟩
    rw [List.getElem?_eq_getElem (by omega)]
    rw [List.getElem_append_right (by omega)] at hty
    simp only [hlp, Nat.add_sub_cancel_left] at hty
    exact congrArg some hty
  have hvarP : ∀ l, l < rc.rP → ∃ ty, Q.fvsPref[l]? = some (.fvar l ty) := by
    intro l hl
    have hlt : l < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hFr.reverse_idx l _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    refine ⟨ty, ?_⟩
    rw [List.getElem?_eq_getElem (by omega)]
    rw [List.getElem_append_left (by omega)] at hty
    exact congrArg some hty
  -- the call: one of the rule's keys
  obtain ⟨key, hkey, bs, hbs, hv⟩ := hcall
  obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hkey
  have hrl := List.mem_range.mp hr'
  have hIhL : tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j
      = Q.ihs.toList := by
    rw [tgtIhL, ← hAbs]
  generalize hih : (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
    default = ih at *
  have hrl' : r < Q.ihs.toList.length := by rw [← hIhL]; exact hrl
  have hihMem : ih ∈ Q.ihs.toList := by
    rw [← hih, hIhL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl', Option.getD_some]
    exact List.getElem_mem hrl'
  obtain ⟨C⟩ := Q.call hihMem
  have hcallOk := ConLeche.targetCallsOk_each Q.hcalls ih hihMem
  -- the called field is a field of the constructor
  have hfi : ih.field < cA.2 := by
    refine Nat.lt_of_not_le fun hge => ?_
    have hg : Q.fvsF.getD ih.field default = .bvar 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h0 := C.hfld
    rw [hg] at h0
    exact inferTypeCore_bvar_absurd' h0
  -- the call's shape
  have hframeL : ∀ x ∈ Q.fvsPref ++ Q.fvsF, ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := frame_leaves_mem hFr hher
  have hidxL : ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := by
    rcases targetAbstract_entries (fr := ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out))
        rc.rP Q.fvsPref Q.fvsF Q.fnorm
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)))
        (B := rc.rP + cA.2) hle 0 _ #[] _ _ Q.habs ih hihMem with h0 | h0
    · simp at h0
    · intro x hx l hl
      obtain ⟨y, hy, hly⟩ := fvarLeaves_instantiateList hFr Q.body hbf 0 l (h0 x hx l hl)
      exact hframeL y (List.mem_reverse.mp hy) l hly
  obtain ⟨hidxLen, hrPc, hidxB⟩ : ih.idx.length + rc.rP
        = (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD ih.callee 0 ∧
      (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD ih.callee 0 = rc.rP ∧
      ∀ x ∈ ih.idx, x.looseBVarsBounded ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length
        = true := by
    rcases targetAbstract_callShape (fr := ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out))
        rc.rP Q.fvsPref Q.fvsF Q.fnorm
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)))
        (B := rc.rP + cA.2) hle 0 _ #[] _ _ Q.habs ih hihMem with h0 | h0
    · simp at h0
    · exact h0
  have hcal : ih.callee < (tgtRs out).length := by
    simpa [tgtFam] using targetCall_callee_lt C
  -- the telescope
  have hTel : (tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).teles
      = Q.fnorm.map fun t => t.piBinders.1 := congrArg (·.teles) hFrEq
  have hFF' : (tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).fields
      = Q.fvsF := congrArg (·.fields) hFrEq
  have hbs' : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mpC.base2.acval envC ψ (rc.rP + cA.2) []
        (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1))).getD []) bs := by
    have := hbs
    simp only [tgtTlA, tgtTeleTys] at this
    rw [hih, hTel, hB, List.map_map] at this
    simpa [Function.comp_def] using this
  -- the value: the called field applied along the telescope
  obtain ⟨fty0, hfty0⟩ : ∃ ty, Q.fvsF.getD ih.field default = Expr.fvar (rc.rP + ih.field) ty := by
    obtain ⟨ty, hty⟩ := hvarF ih.field hfi
    exact ⟨ty, by rw [List.getD_eq_getElem?_getD, hty]; rfl⟩
  refine ⟨rc, rhs0, rhs, cA, Q, ih, bs, hcA, hrP, hlf, hlp, hvarF, hvarP,
    fun x hx => hFr.2.2 x (List.mem_reverse.mpr (List.mem_append_right _ hx)), hihMem, hfi, hfsl, hxl,
    hcallOk, hidxLen, hrPc, hcal, fun x hx => ⟨hidxB x hx, hidxL x hx⟩, hbs', fun hbl => ?_⟩
  have hmT : (tgtTeleTys μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j r).length
      = bs.length := by
    simp only [tgtTeleTys]; rw [hih, hTel, List.length_map, hbl]
  have hfap : interp V (consList bs (consList (xs ++ fs) ρ))
      (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
        ψ c j r)
      = bs.foldl SetTheory.app (fs.getD ih.field pt) := by
    simp only [tgtFapA]
    rw [hmT, hih, hFF', hB, instantiateList_mkAppN, hfty0]
    simp only [Expr.instantiateList]
    rw [denoteMeta_mkAppN (denoteMetaSpine_teleVars (acval := mpC.base2.acval) (env := envC)
      (φ := ψ) (locOpen_locList (rc.rP + cA.2) bs.length) (Nat.le_refl _))
      (denoteMeta_fvar _ _ _ _), Option.getD_some,
      interp_mkAppN_foldl, map_teleVarsAV_interp' rfl,
      interp_frame_fvar hlenS rfl (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hxl, Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD]
  have hEis : (tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
        mpC.base2.acval envC ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))
      = ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + bs.length)
            (x.instantiateList (locOpen (rc.rP + cA.2) bs.length) 0)).getD default)) := by
    simp only [tgtEisA]
    rw [hmT, hih, hB, List.map_map]
    rfl
  rw [hv, hEis, hfap]

end Data

end ConLeche.Model
