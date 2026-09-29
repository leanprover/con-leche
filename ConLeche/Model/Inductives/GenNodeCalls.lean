module

import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.TargetNestKit
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.TargetGuardParams
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Verify.Inductives.NestCallRun
import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Semantics.EnvFacts
import ConLeche.Verify.InferLeaves
import ConLeche.Model.IndPointKit
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.TargetNodeCover
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.TargetCallAdm
import ConLeche.Model.Inductives.TargetCallData
import ConLeche.Model.Inductives.TargetCallEntry
import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Model.Inductives.TargetCallEval
import ConLeche.Model.Inductives.TargetCallFrame
import ConLeche.Model.Inductives.TargetCallKid
import ConLeche.Model.Inductives.TargetCallMaj
import ConLeche.Model.Inductives.TargetCallPatch
import ConLeche.Model.Inductives.TargetCallWalk
import ConLeche.Model.Inductives.TargetCallTie
import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Inductives.TargetNodeCalls
public import ConLeche.Model.Inductives.GenCallData
public import ConLeche.Model.Inductives.GenOutFacts
public import ConLeche.Model.Inductives.TargetNodeDynOf
public import ConLeche.Verify.Inductives.ClassMatchRun

public section

/-!
# The generated calls at the admissible frames (lane GENREC-B2)

`genNodeCalls` — `nestedNodeCalls` (`TargetNodeCalls.lean`) at the
GENERATED calls (`genCallT` at `genIhdAV`): every generated call of a rule
at a related (class, node) pair lands (`NodeLands`).

* the RULE side is by construction (`genCall_data`): the call is a
  recursive field `i` of the class's constructor, its telescope and
  indices the datum entry's walked field at the rule's declared fields,
  its callee the family's recursor at the `ih`'s class;
* K.53′ at the node: the node's own entry is among the class's recorded
  normal forms, so node agreement (`classFieldsAgree`) ran at it, at the
  datum's variables; moved to the rule's fields (`k53_rename`) it is the
  target check's erasure equation (`GenK53At`), the leaf headed by the
  `ih`'s class (`classLeafAt`);
* the WALK side and the SEMANTICS are the target check's, unchanged
  (`callWalkSyn`, `fieldCall_core`, the three landings).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx
  NestHole NestCtorNf BinderMeta BlockParts BlockShape TargetMajor fueledOps PosD PosTree
  NestFieldKind PosNodeOk nestHoleConst closeTelescope targetPiDomsWith targetMajorNfs
  openPisAtFvars GenRecRun ClassCtor ClassCtorRun ClassMajorRun mkFEnv)

universe w

variable {V : Type w} [SetTheory V]

/-- **K.53′ at the rule's fields** (`k53_rename`'s conclusion): the datum's
walked field `i` (telescope `tele`) at the rule's declared fields `fvsR`
strips to `teleR` and a leaf headed by the class `Mt`'s inductive, and the
node telescope `T`'s field `i` is, up to annotations, that telescope over
the container at the node leaf's levels `us'` and parameters `Pw` (matching
`Mt`) and the datum leaf's index arguments. -/
@[expose] def GenK53At (F : Nat) (envC : Env) (p : BlockShape) (formerTys : List Expr)
    (Mt : TargetMajor) (fvsR : List Expr) (T0 : Expr) (i tele : Nat) (T : Expr) : Prop :=
  ∃ (ws : List Expr) (teleR : List (Expr × BinderMeta)) (leafR : Expr) (I : Name)
    (us us' : List Level) (Pw : List Expr) (fR : Expr),
    targetPiDomsWith fvsR T0 = some ws ∧
    (ws.getD i default).stripPis tele = some (teleR, leafR) ∧
    leafR.getAppFn = .const I us ∧ I = Mt.ind ∧
    ((targetPiDomsWith fvsR T).getD [])[i]? = some fR ∧
    fR.eraseFVarTys = (Expr.mkPisOf teleR
      (Expr.mkAppN (.const I us') (Pw ++ leafR.getAppArgs.drop Mt.nPc))).eraseFVarTys ∧
    (Expr.mkAppN (.const I us') Pw).nestOcc p.memberNames 0 0 = true ∧
    ConLeche.targetClassMatch (fueledOps .verified F) envC p formerTys Mt.pfvs Mt.lvls Mt.ds us' Pw
      = .ok true ∧
    (∀ x ∈ Pw, x.looseBVarsBounded 0 = true)

/-- **A class's constructor count is its clause's** at the generated run
(`tgtCls_hctM` and `TgtOutCls.hlen`). -/
theorem genNCt {μ : CheckMode} {F : Nat} {envI envC : Env} {pp : BlockParts} {nested : Bool}
    {posR : ConLeche.NestState} {cvTasR : List ConstantVal} {block : List ConstantInfo}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V}
    (R : GenRecRun μ F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nested posR cvTasR
      block ctorsAsR out) (hg : ConLeche.ClassGenScoped R.g)
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      dR = blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {c : Nat} (hc : c < (tgtRs out).length) :
    (tgtClsD dR Dc out c).nctors (tgtClsM mc pp.toBlockShape out c)
      = (tgtMajor out c).ctors.length := by
  cases hmb : (tgtMajor out c).member with
  | some m =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    obtain ⟨-, -, -, hmem⟩ := genRec_at R hg hc
    obtain ⟨hrt, hct, -⟩ := hmem m hmb
    simp only [tgtClsD, tgtClsM, hm, if_true, hrt]
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
    show (ctorsAsR.getD m []).length = _
    rw [List.getD_eq_getElem?_getD, hct, Option.getD_some]
  | none =>
    have hm : (tgtMajor out c).member.isSome = false := by rw [hmb]; rfl
    simp only [tgtClsD, tgtClsM, hm, Bool.false_eq_true, if_false]
    exact (hcls c hc hmb).hlen.symm


/-- **K.53′ at a recorded entry of the class's constructor** (`k53_entry`
at the generated stage): an entry of the constructor `cA` that the class
matches is among its recorded normal forms, so node agreement ran at it;
moved to the rule's declared fields it is `GenK53At`. -/
theorem genK53_entry {μ : CheckMode} {F : Nat} {envI envC : Env} {pp : BlockParts}
    {nested : Bool} {posR : ConLeche.NestState} {cvTasR : List ConstantVal}
    {block : List ConstantInfo} {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : GenRecRun .verified F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nested posR
      cvTasR block ctorsAsR out) (hg : ConLeche.ClassGenScoped R.g)
    (hTbl : ∀ e ∈ R.st.ctorNfs.toList, ConLeche.ScB pp.nP e.ty)
    {cls : Nat} {M₀ : TargetMajor} {nfs : List NestCtorNf} {cA : ConstantVal × Nat}
    {x : ClassCtor} {j : Nat}
    (Rc : ClassCtorRun .verified F envC pp.toBlockShape (cvTasR.map (·.type)) R.rd R.Ms cls cA x)
    (hMs : R.Ms[cls]? = some { M₀ with nfs := nfs })
    (hnfs : targetMajorNfs (fueledOps .verified F) envC pp.toBlockShape (cvTasR.map (·.type))
      M₀.pfvs M₀.lvls M₀.ds M₀.ctors R.st.ctorNfs.toList = .ok nfs)
    (hcA : M₀.ctors[j]? = some cA) (hxj : (R.ctors.getD cls [])[j]? = some x)
    {i tt tele : Nat} (hk : x.kinds.getD i .ordinary = .recursive tt tele)
    {fvsR : List Expr} {oR : Expr}
    (hopR : openPisAtFvars x.nF x.tyD R.pre.length = some (fvsR, oR))
    {e : NestCtorNf} (he : e ∈ R.st.ctorNfs.toList) (hcn : e.ctor = cA.1.name)
    (hCM : ConLeche.targetClassMatch (fueledOps .verified F) envC pp.toBlockShape
      (cvTasR.map (·.type)) M₀.pfvs M₀.lvls M₀.ds e.lvls e.ds = .ok true) :
    GenK53At F envC pp.toBlockShape (cvTasR.map (·.type)) (R.Ms.getD tt default) fvsR x.tyN i
      tele e.ty := by
  have hcM : M₀.ctors.any (·.1.name == e.ctor) = true := by
    rw [hcn]; exact List.any_eq_true.mpr ⟨cA, List.mem_of_getElem? hcA, by simp⟩
  have hmem := ConLeche.targetMajorNfs_mem hnfs e he hcM hCM
  have hE : e ∈ Rc.E := by
    rw [Rc.hE, List.getD_eq_getElem?_getD, hMs, Option.getD_some]
    exact List.mem_filter.mpr ⟨hmem, by simp [hcn]⟩
  have hk' : x.kinds[i - 0]? = some (.recursive tt tele) := by
    rw [Nat.sub_zero]
    rw [List.getD_eq_getElem?_getD] at hk
    cases h' : x.kinds[i]? with
    | none => rw [h'] at hk; exact nomatch hk
    | some k0 => rw [h'] at hk; simp only [Option.getD_some] at hk; rw [hk]
  obtain ⟨teleB, leaf, f0, hst, hleaf, hf0, hK⟩ :=
    ConLeche.classFieldsAgree_at Rc.hna hk' (Nat.zero_le i) hE
  have hxmem : x ∈ R.g.ctors.getD cls [] := List.mem_of_getElem? hxj
  have hnF : x.nF = cA.2 := congrArg ClassCtor.nF Rc.hx
  have hxN : x.tyN = Rc.e0.ty := congrArg ClassCtor.tyN Rc.hx
  have hpl : R.pre.length = pp.nP + R.rd.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  obtain ⟨hlR, hfvR, -⟩ := ConLeche.ScB.openPis hopR ((hg.tyD cls x hxmem).mono
    (show R.g.nP ≤ R.pre.length by show pp.nP ≤ _; omega))
  have hT0 : Rc.e0.ty.fvarsBelow (pp.nP + pp.toBlockShape.k) := by
    rw [← hxN]
    exact ConLeche.Expr.fvarsBelow_mono (Nat.le_add_right _ _)
      (ConLeche.Expr.WScoped.fvarsBelow (hg.tyN cls x hxmem).1)
  have hT : e.ty.fvarsBelow (pp.nP + pp.toBlockShape.k) :=
    ConLeche.Expr.fvarsBelow_mono (Nat.le_add_right _ _)
      (ConLeche.Expr.WScoped.fvarsBelow (hTbl e he).1)
  have hpf : (R.Ms.getD tt default).pfvs.length ≤ pp.nP + pp.toBlockShape.k := by
    sorry
  have hK' := ConLeche.k53_rename (n := cA.2) (bR := R.pre.length) (fvsR := fvsR) Rc.hopen
    (fun l hl => by
      obtain ⟨z, hz⟩ : ∃ z, fvsR[l]? = some z :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlR, hnF]; exact hl)⟩
      obtain ⟨ty, rfl, -⟩ := hfvR l z hz
      exact ⟨ty, hz⟩)
    (by rw [hlR, hnF]) hT hT0 hpf hst hleaf hf0 hK
  rw [← hxN] at hK'
  exact hK'

end ConLeche.Model
