module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.TargetCallGen
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Verify.Rules.InferBridge
public import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Capstone
import ConLeche.Semantics.Kit
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.BetaGate

public section

/-!
# A target call's target, at a valuation of the holes

The target check types every recursive call on the member-ABSTRACTED
terms (`targetCallOk`): at the rule frame extended by the block's
member HOLES (`targetHoles`, after the prefix and the fields), the
field's abstract type through whnf (`fnorm`) is defeq to
`∀ a⃗, hole_m x⃗ e⃗` (`hdeq`), whose body was inferred (`hwant`).  So at
EVERY valuation of the holes satisfying their types (each hole at its
member former's type), a field lying in its abstract type's reading has
its call target in the hole's family: the index readings fit the
member's index telescope at the parameters, and the applied field lies
in the hole applied to them.

`tgtCall_coreFitG` states that once, at a hole valuation `hv` with a
member-application law (`hlaw`: the hole of the callee's member, applied
to the parameters and a fitting index spine, is `Y` at the index
tuple), at any caller rule.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- An inference run never types a loose bound variable. -/
theorem inferTypeCore_bvar_absurd' {mode : CheckMode} {env : Env} {F d i : Nat} {t : Expr}
    (h : ConLeche.inferTypeCore mode env F d (.bvar i) = .ok t) : False := by
  cases F with
  | zero =>
    simp [ConLeche.inferTypeCore, ConLeche.pureFns, ConLeche.coreKnot, throw, throwThe,
      MonadExceptOf.throw] at h
  | succ F => exact ConLeche.Rules.inferTypeCore_bvar_inv h

section MajDom

/-- **A major's domain, peeled at closed arguments** (the shared core of
`tgtMajDom_open` and `tgtMajDom_openOut`): a free-variable-free type
opened at `n + 1` binders, the last opener being the major `maj`, and
instantiated at `n` bvar-closed arguments, is a `∀` whose domain is the
major's type with the first `n` openers replaced by the arguments. -/
theorem majDom_peel {ty concl maj : Expr} {n : Nat} {fvs : List Expr}
    (hop : ConLeche.openPisAtFvars (n + 1) ty 0 = some (fvs, concl))
    (hmaj : fvs[n]? = some maj) (hTf : ty.hasFvar = false)
    {args : List Expr} (hcl : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (hlen : args.length = n) {res : Expr}
    (hres : Expr.instPisAtLift args ty = some res) :
    ∃ (fvs1 : List Expr) (body : Expr) (bm : ConLeche.BinderMeta),
      fvs = fvs1 ++ [maj] ∧ fvs1.length = n ∧ fvs1.map (replF fun i => args[i]?) = args ∧
      res = .forallE (replF (fun i => args[i]?) (Expr.fvarTypeD maj)) body bm := by
  obtain ⟨fvs1, fvs', o, hop1, hop2, hF⟩ := openPisAtFvars_split n (m := 1) hop
  obtain ⟨dom, body, bm, rfl, rfl⟩ : ∃ dom body bm, o = .forallE dom body bm ∧
      fvs' = [Expr.fvar n dom] := by
    match o, hop2 with
    | .forallE dom body bm, hop2 =>
      simp only [ConLeche.openPisAtFvars, Nat.zero_add] at hop2
      simp only [Option.some.injEq, Prod.mk.injEq] at hop2
      exact ⟨dom, body, bm, rfl, hop2.1.symm⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [ConLeche.openPisAtFvars] at h
  have hl1 : fvs1.length = n := ConLeche.Verify.openPisAtFvars_length _ hop1
  obtain rfl : maj = Expr.fvar n dom := by
    rw [hF, List.getElem?_append_right (by omega), hl1, Nat.sub_self] at hmaj
    exact (Option.some.inj hmaj).symm
  -- the peel at the openers, and at the arguments
  have hins1 := ConLeche.Verify.openPisAtFvars_instPisAt _ hop1
  rw [ConLeche.instPisAtLift_eq_instPisAt hcl] at hres
  obtain ⟨⟨ds, res'⟩, hres2, rfl⟩ := Option.map_eq_some_iff.mp hres
  have hidx := ConLeche.openPisAtFvars_index _ _ _ hop1
  have hrep := instPisAt_replF (g := fun i => args[i]?)
    (fun i x hx => hcl x (List.mem_of_getElem? hx))
    fvs1 args ty hins1 (by rw [hl1, hlen]) (fun j hj hj' => by
      obtain ⟨ty, hty⟩ := hidx j _ (List.getElem?_eq_getElem hj)
      rw [hty]
      simp [replF, List.getElem?_eq_getElem hj'])
  rw [replF_of_not_hasFvar _ _ hTf, hres2] at hrep
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hrep)
  refine ⟨fvs1, replF (fun i => args[i]?) body, bm, hF, hl1, ?_, rfl⟩
  apply List.ext_getElem (by simp [hl1, hlen])
  intro j h1 h2
  simp only [List.getElem_map]
  obtain ⟨ty, hty⟩ := hidx j _ (List.getElem?_eq_getElem (by simpa using h1))
  rw [hty]
  simp [replF, List.getElem?_eq_getElem h2]

/-- **A stored recursor's major domain, peeled at closed arguments**: the
recursor's type opened at its `mI` leading binders by any bvar-closed
terms is a `∀` whose domain is the eliminated member at the arguments'
parameters and indices (the type pin, `RecTyEntry`). -/
theorem tgtMajDom_open {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hm : memR c) (hr : rs[c]? = some r)
    {args : List Expr} (hcl : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (hlen : args.length = pp.toBlockShape.majorIdxAt c) {res : Expr}
    (hres : Expr.instPisAtLift args r.1.type = some res) :
    ∃ (ms : ConLeche.MemberShape) (body : Expr) (bm : ConLeche.BinderMeta),
      pp.toBlockShape.members[pp.toBlockShape.recTgtAt c]? = some ms ∧
      res = .forallE (Expr.mkAppN (.const ms.cvT.name (pp.toBlockShape.lps.map .param))
        (args.take pp.toBlockShape.nP ++ args.drop (pp.toBlockShape.rulePrefixAt c))) body bm := by
  obtain ⟨rc, u, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyAt h hm hr
  obtain ⟨hTf, -, -, -, -⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  obtain ⟨fvs1, body, bm, hF, hl1, hmapF, rfl⟩ := majDom_peel TE.hopen TE.hmaj hTf hcl hlen hres
  have hdom : Expr.fvarTypeD TE.maj = Expr.mkAppN (.const TE.ms.cvT.name
      (pp.toBlockShape.lps.map .param))
      (fvs1.take pp.toBlockShape.nP ++ fvs1.drop (pp.toBlockShape.rulePrefixAt c)) := by
    conv => lhs; rw [← ConLeche.Expr.mkAppN_getApp (Expr.fvarTypeD TE.maj)]
    rw [TE.hmajFn, ← List.take_append_drop pp.toBlockShape.nP (Expr.fvarTypeD TE.maj).getAppArgs,
      TE.hmajParams, TE.hmajIdx, hF]
    have hnP := TE.hroom
    have hmI := TE.hmI
    congr 2
    · rw [List.take_append_of_le_length (by omega)]
    · rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]
      rw [List.take_of_length_le (by simp; omega)]
  refine ⟨TE.ms, body, bm, TE.hms, ?_⟩
  rw [hdom]
  simp only [replF, replF_mkAppN, List.map_append]
  rw [List.map_take, List.map_drop, hmapF]

end MajDom

/-- A family position's entries are its stored recursor's: the major
index, the rule prefix and the type. -/
theorem tgtFam_at {F : Nat} {env : Env} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F env pp cvTas ctorsAs (tgtRs out) memR)
    {e : Nat} {r1 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr1 : (tgtRs out)[e]? = some r1) :
    (tgtFam pp.toBlockShape out).mIs.getD e 0 = pp.toBlockShape.majorIdxAt e ∧
    (tgtFam pp.toBlockShape out).rPs.getD e 0 = pp.toBlockShape.rulePrefixAt e ∧
    (tgtFam pp.toBlockShape out).recTys.getD e (.sort .zero) = r1.1.type := by
  have hcal : e < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr1).1
  obtain ⟨-, hlenR, -⟩ := ConLeche.recStageG_recNames h
  have hcalR : e < pp.recs.length := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [tgtFam, ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_getElem hcalR]; rfl
  · simp only [tgtFam, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_getElem hcalR]; rfl
  · simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr1]; rfl

section IhPrelude

/-! ### One `ih` entry of a rule's run: the facts every call lemma opens with -/

variable {F : Nat} {feR feT : FEnv} {p : ConLeche.BlockShape} {formerTys : List Expr}
  {fam : ConLeche.TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr} {M : TargetMajor}
  {c : ConstantVal × Nat} {rhs out : Expr}
  (Q : ConLeche.TargetRuleRun μ F feR feT p formerTys fam cvR rP recTy M c rhs out)
  {ih : TargetIh}

/-- An `ih`'s called field is one of the constructor's fields. -/
theorem tgtIh_field_lt (hih : ih ∈ Q.ihs.toList) : ih.field < c.2 := by
  obtain ⟨C⟩ := Q.call hih
  have hlf : Q.fvsF.length = c.2 := openPisAtFvars_length _ Q.hfld
  refine Nat.lt_of_not_le fun hge => ?_
  have hg : Q.fvsF.getD ih.field default = .bvar 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
  have h0 := C.hfld
  rw [hg] at h0
  exact inferTypeCore_bvar_absurd' h0

/-- The call's index arguments' leaves are the frame's entries. -/
theorem tgtIh_idxLeaves (hle : ∀ c', fam.rPs.getD c' 0 ≤ fam.mIs.getD c' 0)
    (hbf : Q.body.hasFvar = false) (hFr : FvarList (rP + c.2) (Q.fvsPref ++ Q.fvsF).reverse)
    (hher : ∀ x ∈ Q.fvsPref ++ Q.fvsF, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF) (hih : ih ∈ Q.ihs.toList) :
    ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := by
  rcases targetAbstract_entries (fr := ConLeche.targetFrameOf fam rP Q.fvsPref Q.fvsF Q.fnorm
      (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)))
      (B := rP + c.2) hle 0 _ #[] _ _ Q.habs ih hih with h0 | h0
  · simp at h0
  · intro x hx l hl
    obtain ⟨y, hy, hly⟩ := fvarLeaves_instantiateList hFr Q.body hbf 0 l (h0 x hx l hl)
    exact frame_leaves_mem hFr hher y (List.mem_reverse.mp hy) l hly

/-- The call's shape: as many index arguments as the callee's indices,
the callee's prefix the caller's, the index arguments bounded by the
field's telescope. -/
theorem tgtIh_callShape (hle : ∀ c', fam.rPs.getD c' 0 ≤ fam.mIs.getD c' 0)
    (hih : ih ∈ Q.ihs.toList) :
    ih.idx.length + rP = fam.mIs.getD ih.callee 0 ∧ fam.rPs.getD ih.callee 0 = rP ∧
      ∀ x ∈ ih.idx,
        x.looseBVarsBounded ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length
          = true := by
  rcases targetAbstract_callShape (fr := ConLeche.targetFrameOf fam rP Q.fvsPref Q.fvsF Q.fnorm
      (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)))
      (B := rP + c.2) hle 0 _ #[] _ _ Q.habs ih hih with h0 | h0
  · simp at h0
  · exact h0

end IhPrelude

section FapEis

/-- **Entry `r`'s applied field and index arguments, read** at the frame's
values `xs ++ fs` and the telescope's values `bs`: the applied field is
the field's value applied along `bs`, the index arguments are the
opened ones, read. -/
theorem tgtFapEis_interp {envC : Env} (mpC : EnvModelM V μ envC) {F : Nat} {pp : BlockParts}
    {cvTas : List ConstantVal} {out : List (ConstantVal × TargetMajor × List Expr)}
    (ψ : Name → Nat) (ρ : Nat → V) {c j r rP nF : Nat} {ih : TargetIh}
    {fvsF : List Expr} {tl : List (List (Expr × ConLeche.BinderMeta))} {fty : Expr}
    {xs fs bs : List V}
    (hih : (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
      default = ih)
    (hTel : (tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).teles = tl)
    (hFF : (tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).fields
      = fvsF)
    (hB : tgtB pp.toBlockShape out c j = rP + nF)
    (hfty : fvsF.getD ih.field default = Expr.fvar (rP + ih.field) fty)
    (hxl : xs.length = rP) (hfsl : fs.length = nF) (hfi : ih.field < nF)
    (hbl : bs.length = (tl.getD ih.field []).length) :
    interp V (consList bs (consList (xs ++ fs) ρ))
        (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
          ψ c j r)
      = bs.foldl SetTheory.app (fs.getD ih.field pt) ∧
    (tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
        mpC.base2.acval envC ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))
      = ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval envC ψ (rP + nF + bs.length)
            (x.instantiateList (locOpen (rP + nF) bs.length) 0)).getD default)) := by
  have hlenS : (xs ++ fs).length = rP + nF := by rw [List.length_append, hxl, hfsl]
  have hmT : (tgtTeleTys μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j r).length
      = bs.length := by
    simp only [tgtTeleTys]; rw [hih, hTel, List.length_map, hbl]
  refine ⟨?_, ?_⟩
  · simp only [tgtFapA]
    rw [hmT, hih, hFF, hB, instantiateList_mkAppN, hfty]
    simp only [Expr.instantiateList]
    rw [denoteMeta_mkAppN (denoteMetaSpine_teleVars (acval := mpC.base2.acval) (env := envC)
      (φ := ψ) (locOpen_locList (rP + nF) bs.length) (Nat.le_refl _))
      (denoteMeta_fvar _ _ _ _), Option.getD_some,
      interp_mkAppN_foldl, map_teleVarsAV_interp' rfl,
      interp_frame_fvar hlenS rfl (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hxl, Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD]
  · simp only [tgtEisA]
    rw [hmT, hih, hB, List.map_map]
    rfl

end FapEis

section MemberHoles

variable {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V} {pp : BlockParts}
  {cvTas : List ConstantVal}

/-- **The holes' values at their formers' types**: each member former's
type is closed and read, graded at every valuation, and holds the hole's
value `hv` — the formers' facts a call's typing (`targetCall_genW`) asks
for, from the members' run and `hv`'s typing. -/
theorem memberHoles_formers (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (ψ : Name → Nat) (ρ : Nat → V) {hv : List V}
    (hvTy : ∀ t, t < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 (cvTas.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T) :
    ∀ t', t' < (cvTas.map (fun cv : ConstantVal => cv.type)).length →
      ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default).hasFvar = false ∧
      ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default).looseBVarsBounded 0 = true ∧
      ConstsBound envC ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default) ∧
      ∃ T : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0
          ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default)
          = some T ∧ (∀ σ : Nat → V, WellDenotedV V σ T) ∧
        ∀ σ : Nat → V, hv.getD t' pt ∈ˢ interp V σ T := by
  intro t' ht'
  have ht'' : t' < cvTas.length := by simpa using ht'
  obtain ⟨cv, hcv⟩ : ∃ cv, cvTas[t']? = some cv := ⟨_, List.getElem?_eq_getElem ht''⟩
  obtain ⟨-, -, ⟨caps, hfind⟩, hfv, hbv, hFD'⟩ := hmr.2.2.2.1 t' cv hcv
  have hg : (cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default = cv.type := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hcv]; rfl
  have hwf := mpC.base2.wf _ (List.mem_of_find?_eq_some hfind)
  obtain ⟨T', hT', hmemT'⟩ := hvTy t' ht''
  have hgc : (cvTas.getD t' default).type = cv.type := by
    rw [List.getD_eq_getElem?_getD, hcv]; rfl
  rw [hgc, hFD'.read ψ] at hT'
  obtain rfl := Option.some.inj hT'
  have hcl := bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hfv) hbv
    (hFD'.read ψ)
  rw [hg]
  exact ⟨hfv, hbv, constsBound_of_constsResolve _ hwf.2.2.1, _, hFD'.read ψ, hFD'.okTy ψ,
    fun σ => by rw [interp_closed V hcl σ ρ]; exact hmemT'⟩

end MemberHoles

section Core

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {envI : Env}

set_option maxHeartbeats 8000000 in
/-- **A target call's target as a FIT, at ANY caller**: at the caller
rule's frame facts and walk context (`tgtFrame_cls`, `tgtFrame_walk` — a member's or
an outside container's rule), for a MEMBER callee (`memR` at the
callee: its major domain is the callee member at the prefix's
parameters and the call's indices, `tgtMajDom_open`). -/
theorem tgtCall_coreFitG (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F fe.env pp cvTas ctorsAs (tgtRs out) memR)
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hnd : d.memberNames.Nodup)
    (hformerF : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false)
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat}
    {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    {rc : ConLeche.RecShape} {M : TargetMajor} {cA : ConstantVal × Nat} {rhs0 rhs : Expr}
    (Q : ConLeche.TargetRuleRun μ F
      (ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) fe) fe pp.toBlockShape
      (cvTas.map (·.type)) (tgtFam pp.toBlockShape out) r0.1 rc.rP r0.1.type M cA rhs0 rhs)
    (hrP : rc.rP = pp.toBlockShape.rulePrefixAt c)
    (hnP : pp.toBlockShape.nP ≤ rc.rP)
    (hdsOk : TgtDsOk fe.env rc.rP Q.fvsPref M.ds)
    (hCf : (ConLeche.targetCtorAt M cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M cA.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound fe.env (ConLeche.targetCtorAt M cA.1))
    (hbf : Q.body.hasFvar = false)
    (hTf : r0.1.type.hasFvar = false) (hTb : r0.1.type.looseBVarsBounded 0 = true)
    (hTc : ConstsBound fe.env r0.1.type)
    (hle : ∀ c', (tgtFam pp.toBlockShape out).rPs.getD c' 0
      ≤ (tgtFam pp.toBlockShape out).mIs.getD c' 0)
    (hRT3 : ∀ c',
      ((tgtFam pp.toBlockShape out).recTys.getD c' (.sort .zero)).hasFvar = false ∧
      ((tgtFam pp.toBlockShape out).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
        = true ∧
      ConstsBound fe.env ((tgtFam pp.toBlockShape out).recTys.getD c' (.sort .zero)))
    (hB : tgtB pp.toBlockShape out c j = rc.rP + cA.2)
    (hFrEq : tgtFrame μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape out) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)))
    (hAbs : (Q.bodyO, Q.ihs) = tgtAbs μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j)
    {xs fs : List V} {Δ : List AnnotTerm}
    (hW : WalkCtx V mpC.base2 ψ (rc.rP + cA.2) (consList (xs ++ fs) ρ) Δ
      (Q.fvsPref ++ Q.fvsF).reverse)
    (hxs : xs.length = pp.toBlockShape.rulePrefixAt c) (hfsl : fs.length = cA.2)
    {r : Nat}
    (hr : r < (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).length)
    (hm1 : memR ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
      default).callee)
    (hv : List V) (hvl : hv.length = cvTas.length)
    (hvTy : ∀ t, t < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ 0 (cvTas.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T)
    (hii : ∀ q, q < cA.2 → ∀ Aty : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ
          (tgtB pp.toBlockShape out c j + cvTas.length)
          (tgtAbsM pp.toBlockShape (cvTas.map (·.type)) out c j
            ((tgtFieldFvs pp.toBlockShape out c j).getD q default).fvarTypeD) = some Aty →
      fs.getD q pt ∈ˢ interp V (consList (xs ++ fs ++ hv) ρ) Aty)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env ψ
        c j r).map (·.2.2)) bs) :
    SpineFit (consList (xs.take d.nP) ρ)
      (d.IdsM (pp.toBlockShape.recTgtAt
        ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).callee) ψ)
      ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env
        ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))) ∧
    interp V (consList bs (consList (xs ++ fs) ρ))
        (tgtFapA μ F fe pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval fe.env
          ψ c j r)
      ∈ˢ (xs.take d.nP ++ (tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) out
          mpC.base2.acval fe.env ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))).foldl
          SetTheory.app
          (hv.getD (pp.toBlockShape.recTgtAt
            ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
              default).callee) pt) := by
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  -- the entry
  have hIhL : tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j = Q.ihs.toList := by
    rw [tgtIhL, ← hAbs]
  generalize hih : (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
    default = ih at *
  have hihMem : ih ∈ Q.ihs.toList := by rw [← hih, ← hIhL]; exact ConLeche.getD_mem hr
  obtain ⟨C⟩ := Q.call hihMem
  -- the frame
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf hCb hCc
  -- the frame's two segments
  have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hlf : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
  have hxl : xs.length = rc.rP := by rw [hxs, hrP]
  -- the called field is a field of the constructor
  have hfi : ih.field < cA.2 := tgtIh_field_lt Q hihMem
  -- the telescope's and the index arguments' leaves
  have hscope := targetIh_scope hμ Q mpC.base2.wf hle hbf hFr hher hcbF hformerF
    (fun c' => (hRT3 c').1) hihMem
  have htL := hscope.2.2.2.2.2
  have hidxL := tgtIh_idxLeaves Q hle hbf hFr hher hihMem
  -- the call's shape
  obtain ⟨hidxLen, hrPc, hidxB⟩ := tgtIh_callShape Q hle hihMem
  -- the callee
  have hcal : ih.callee < (tgtRs out).length := by
    simpa [tgtFam] using targetCall_callee_lt C
  obtain ⟨r1, hr1⟩ : ∃ r1, (tgtRs out)[ih.callee]? = some r1 := ⟨_, List.getElem?_eq_getElem hcal⟩
  obtain ⟨hmIc, hrPe, hrecTy⟩ := tgtFam_at h hr1
  have hrPc' : pp.toBlockShape.rulePrefixAt ih.callee = rc.rP := by rw [← hrPe, hrPc]
  obtain ⟨hnPc, hmemk, hmI, -, -⟩ := blockRecMajor_run (hm := hm1) hμ mpC h hmr hr1 ψ
  obtain ⟨_, _, -, ⟨TE1⟩⟩ := ConLeche.recStageG_tyAt h hm1 hr1
  have hdnP : (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).nP
      = pp.toBlockShape.nP := hmr.1
  have hidxLen' : ih.idx.length
      = (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).nIdxAt
          (pp.toBlockShape.recTgtAt ih.callee) := by
    rw [hmIc, hmI, hrPc'] at hidxLen; omega
  -- the call's major domain, opened
  have hmaj : ∀ os : List Expr, LocList (rc.rP + cA.2 + (cvTas.map (·.type)).length)
      ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length os →
      C.majDom.instantiateList os 0 = Expr.mkAppN
        (.const TE1.ms.cvT.name (pp.toBlockShape.lps.map .param))
        ((Q.fvsPref.take pp.toBlockShape.nP).map (·.instantiateList os 0)
          ++ ih.idx.map (·.instantiateList os 0)) := by
    intro os hos
    have hall := hos.allFvars
    have hoscl : ∀ o ∈ os, o.looseBVarsBounded 0 = true := by
      intro o ho; obtain ⟨i, ty, rfl⟩ := hall o ho; rfl
    have hprefF : ∀ x ∈ Q.fvsPref, ∃ i ty, x = Expr.fvar i ty := fun x hx =>
      hFr.mem_fvar (List.mem_reverse.mpr (List.mem_append_left _ hx))
    have hargsB : ∀ a ∈ Q.fvsPref ++ ih.idx, a.looseBVarsBounded os.length = true := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨i, ty, rfl⟩ := hprefF a ha; rfl
      · rw [hos.1]; exact hidxB a ha
    have hins := instPisAtLift_instantiateList hoscl (Q.fvsPref ++ ih.idx) hargsB
      (hRT3 ih.callee).2.1 C.hcallee
    rw [C.hmajDom, hrecTy] at hins
    simp only [Expr.instantiateList] at hins
    have hclA : ∀ a ∈ (Q.fvsPref ++ ih.idx).map (·.instantiateList os 0),
        a.looseBVarsBounded 0 = true := by
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      exact looseBVarsBounded_instantiateList_allFvars hall b 0
        (by simpa using hargsB b hb)
    have hlenA : ((Q.fvsPref ++ ih.idx).map (·.instantiateList os 0)).length
        = pp.toBlockShape.majorIdxAt ih.callee := by
      rw [List.length_map, List.length_append, hlp, ← hmIc]; omega
    obtain ⟨ms, body, bm', hms, heq⟩ := tgtMajDom_open (hm := hm1) h hr1 hclA hlenA hins
    obtain rfl : ms = TE1.ms := Option.some.inj (hms.symm.trans TE1.hms)
    injection heq with hdom
    rw [hdom, List.map_append, List.take_append_of_le_length (by rw [List.length_map, hlp]; omega),
      hrPc', List.drop_append_of_le_length (by simp [hlp]),
      List.drop_eq_nil_of_le (by simp [hlp]), List.nil_append, List.map_take]
  -- the callee's member: its hole and its former
  generalize htdef : pp.toBlockShape.recTgtAt ih.callee = t at *
  have hnd' : pp.toBlockShape.memberNames.Nodup := hnd
  have hI : pp.toBlockShape.memberNames.findIdx? (· == TE1.ms.cvT.name) = some t := by
    refine findIdx?_of_nodup hnd' ?_
    simp [ConLeche.BlockShape.memberNames, List.getElem?_map, ← htdef, TE1.hms]
  have hkN := hN.2.2
  have htk : t < (cvTas.map (fun cv : ConstantVal => cv.type)).length := by rw [List.length_map, hkN]; exact hmemk
  obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by simpa using htk)⟩
  obtain ⟨-, -, -, -, -, hFD⟩ := hmr.2.2.2.1 t cvTb hcvTb
  have hgetT : (cvTas.map (fun cv : ConstantVal => cv.type)).getD t default = cvTb.type := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hcvTb]; rfl
  have hTt : denoteMeta mpC.base2.acval fe.env ψ 0 ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t default)
      = some (mkPisAV ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM t ψ)
          (.sort ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).resSort.eval
            ψ))) := by
    rw [hgetT]; exact hFD.read ψ
  have hpdsLen : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM t ψ).length
      = pp.toBlockShape.nP + ih.idx.length := by
    rw [hFD.len ψ, hdnP, hidxLen']
  -- the holes' values at their formers' types
  have hformerG := memberHoles_formers (mpC := mpC) hmr ψ ρ hvTy
  -- the frame data, in the rule data's spelling
  have hFF : tgtFieldFvs pp.toBlockShape out c j = Q.fvsF := congrArg (·.fields) hFrEq
  have hTel : (tgtFrame μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type)) out c j).teles
      = Q.fnorm.map fun t => t.piBinders.1 := congrArg (·.teles) hFrEq
  have hiiG : ∀ q, q < cA.2 → ∀ Aty : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ
        (rc.rP + cA.2 + (cvTas.map (fun cv : ConstantVal => cv.type)).length)
        (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
          (ConLeche.targetHoles (cvTas.map (fun cv : ConstantVal => cv.type)) (rc.rP + cA.2))
          (Q.fvsF.getD q default).fvarTypeD) = some Aty →
      fs.getD q pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) Aty := by
    intro q hq Aty hA
    rw [← consList_append]
    refine hii q hq Aty ?_
    rw [tgtAbsM, hB, hFF, List.length_map] at *
    exact hA
  have hbs' : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mpC.base2.acval fe.env ψ (rc.rP + cA.2) []
        (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1))).getD []) bs := by
    have := hbs
    simp only [tgtTlA, tgtTeleTys] at this
    rw [hih, hTel, hB, List.map_map] at this
    simpa [Function.comp_def] using this
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  obtain ⟨hspP, hmemF⟩ := targetCall_gen hμ hacl (Rules.RulesInputs.ofSem mpC ψ) C
    (Q.fvsA_eq hihMem) Q.hfA hlp hlf
    hFr hxl hfsl hW hfi htL hidxL (by rw [hvl, List.length_map]) hformerG hiiG
    (nP := pp.toBlockShape.nP) hnP ((hRT3 ih.callee).1) hmaj hI htk hTt
    (hFD.bits ψ) hpdsLen bs hbs'
  have hFF' : (tgtFrame μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
      out c j).fields = Q.fvsF := congrArg (·.fields) hFrEq
  have hEis : (tgtEisA μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
        out mpC.base2.acval fe.env ψ c j r).map
        (interp V (consList bs (consList (xs ++ fs) ρ)))
      = ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval fe.env ψ
            (rc.rP + cA.2 + ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)
            (x.instantiateList (locOpen (rc.rP + cA.2)
              ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length) 0)).getD default)) := by
    simp only [tgtEisA, tgtTeleTys]
    rw [hih, hTel, hB, List.length_map, List.map_map]
    rfl
  have hFap : interp V (consList bs (consList (xs ++ fs) ρ))
        (tgtFapA μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type)) out
          mpC.base2.acval fe.env ψ c j r)
      = interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval fe.env ψ
            (rc.rP + cA.2 + ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)
            ((Expr.mkAppN (Q.fvsF.getD ih.field default)
              (ConLeche.structTeleVars ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)).instantiateList
              (locOpen (rc.rP + cA.2) ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)
                0)).getD default) := by
    simp only [tgtFapA, tgtTeleTys]
    rw [hih, hTel, hB, hFF', List.length_map]
  rw [hEis, hFap]
  -- the parameters and the member's index telescope
  generalize hE : ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
      ((denoteMeta mpC.base2.acval fe.env ψ
        (rc.rP + cA.2 + ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length)
        (x.instantiateList (locOpen (rc.rP + cA.2)
          ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length) 0)).getD default)) = E
    at hspP hmemF ⊢
  have hsplitP : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM t ψ).map
        (·.2.2)
      = (((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ppsM t ψ).take
          pp.toBlockShape.nP).map (·.2.2)
        ++ (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).IdsM t ψ := by
    rw [BlockData.IdsM, hdnP, ← List.map_append, List.take_append_drop]
  rw [hsplitP] at hspP
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_split hspP
  have hl1 : as₁.length = (xs.take pp.toBlockShape.nP).length := by
    rw [h1.length_eq, List.length_map, List.length_take, List.length_take, hFD.len ψ, hdnP, hxl]
    omega
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl1
  rw [← hdnP] at h2 hmemF
  exact ⟨h2, hmemF⟩

end Core

end ConLeche.Model
