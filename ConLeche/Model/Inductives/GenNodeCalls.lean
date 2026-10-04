module

import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.TargetNestKit
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.PosDerivTie
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
import ConLeche.Verify.EnvBound
import ConLeche.Model.Annot.BitRename
import ConLeche.Semantics.Inductives.DeclBlockEta
public import ConLeche.Model.Inductives.GenCallData
import ConLeche.Model.Inductives.GenOutFacts
public import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Verify.Inductives.ClassMatchRun

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
  NestFieldKind PosNodeOk closeTelescope targetPiDomsWith targetMajorNfs
  openPisAtFvars GenRecRun ClassCtor ClassCtorRun ClassMajorRun mkFEnv)

universe w

variable {V : Type w} [SetTheory V]

theorem erasedEqs_refl' : ∀ (l : List Expr), ConLeche.ErasedEqs l l
  | [] => trivial
  | a :: as => ⟨ConLeche.Expr.ErasedEq.rfl a, erasedEqs_refl' as⟩

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
    simp only [tgtClsD, tgtClsM, hm, ite_true, hrt]
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
    show (ctorsAsR.getD m []).length = _
    rw [List.getD_eq_getElem?_getD, hct, Option.getD_some]
  | none =>
    have hm : (tgtMajor out c).member.isSome = false := by rw [hmb]; rfl
    simp only [tgtClsD, tgtClsM, hm, Bool.false_eq_true, ite_false]
    exact (hcls c hc hmb).hlen.symm


/-- **K.53′ at a recorded entry of the class's constructor** (`k53_entry`
at the generated stage): an entry of the constructor `cA` that the class
matches is among its recorded normal forms, so node agreement ran at it;
moved to the rule's declared fields it is `GenK53At`. -/
theorem genK53_entry {F : Nat} {envI envC : Env} {pp : BlockParts}
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
  have hpf : (R.Ms.getD tt default).pfvs.length ≤ pp.nP + pp.toBlockShape.k :=
    Nat.le_trans (genMs_pfvs_len R hg tt) (Nat.le_add_right _ _)
  have hK' := ConLeche.k53_rename (n := cA.2) (bR := R.pre.length) (fvsR := fvsR) Rc.hopen
    (fun l hl => by
      obtain ⟨z, hz⟩ : ∃ z, fvsR[l]? = some z :=
        ⟨_, List.getElem?_eq_getElem (by rw [hlR, hnF]; exact hl)⟩
      obtain ⟨ty, rfl, -⟩ := hfvR l z hz
      exact ⟨ty, hz⟩)
    (by rw [hlR, hnF]) hT hT0 hpf hst hleaf hf0 hK
  rw [← hxN] at hK'
  exact hK'


/-- **A recorded clause's constructor has its stored field count** (the
clause's constructor readings, `LfpCtorReads`). -/
theorem lfpCtor_fieldsLen {μ : CheckMode} {env : Env} {mp : EnvModelM V μ env}
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm j : Nat} (hmm : mm < D.k)
    (hj : j < D.nctors mm) {cv : ConstantVal} {nPc nF : Nat}
    (hf : env.find? (D.ctorName mm j) = some (.ctorInfo cv nPc nF)) (ψ : Name → Nat) :
    (D.fields ψ mm j).length = nF := by
  obtain ⟨-, -, -, hrdC⟩ := mp.lfp_ok D hD
  obtain ⟨cv', nPc', nF', hf', -, -, -, A, -, -, hA⟩ := hrdC.2 mm hmm j hj
  rw [hf] at hf'
  obtain ⟨-, -, rfl⟩ : cv = cv' ∧ nPc = nPc' ∧ nF = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  exact (hA ψ).2.1

/-- **An outside class's constructor has the class's field count** at its
recorded clause. -/
theorem tgtOutCls_fieldsLen {μ : CheckMode} {env : Env} {mp : EnvModelM V μ env}
    {M : TargetMajor} {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mp M D mm cvI) {j : Nat} {cA : ConstantVal × Nat}
    (hcA : M.ctors[j]? = some cA) (ψ : Name → Nat) : (D.fields ψ mm j).length = cA.2 := by
  obtain ⟨hjL, hcAj⟩ := List.getElem?_eq_some_iff.mp hcA
  have hjD : j < D.nctors mm := by rw [← hcl.hlen]; exact hjL
  have hf' := hcl.hctor j hjL
  rw [hcAj] at hf'
  exact lfpCtor_fieldsLen hcl.hD hcl.hmm hjD hf' ψ

/-- **The member forests' parameters are the canonical ones**: the
variables `0 ..< nP`, closed below `nP` (opened off the head former's
closed type). -/
theorem canonPars_of_forests {μ : CheckMode} {F : Nat} {envC envI : Env} {pp : BlockParts}
    {cvTasR : List ConstantVal} {ctorsAsR : List (List (ConstantVal × Nat))}
    {mpC : EnvModelM V μ envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : RecCtxBase V μ F envC envI pp cvTasR ctorsAsR mpC dR isRecR A kindsR nfsR posR)
    {fvsP : List Expr} {tbl : List ConLeche.NestCtorNf} {ns : List PosTree}
    (hmemF : MemberForests F envI pp cvTasR ctorsAsR nfsR fvsP tbl ns) :
    (fvsP.length = pp.nP ∧ ∀ (i : Nat) (x : Expr), fvsP[i]? = some x → ∃ ty, x = .fvar i ty) ∧
    ∀ x ∈ fvsP, ConLeche.ScB pp.nP x := by
  obtain ⟨cvTa0, rest0, holes0, hcv0, hop0, -, -⟩ := hmemF
  obtain ⟨-, -, -, -, -, -, hcore, -⟩ := hctx
  have h0' : cvTasR[0]? = some cvTa0 := by rw [List.head?_eq_getElem?] at hcv0; exact hcv0
  obtain ⟨hf0, -⟩ := hcore.1 0 cvTa0 h0'
  have hw0 := mpC.base2.wf _ (List.mem_of_find?_eq_some hf0)
  exact canonPars_of_open hop0 ⟨Expr.WScoped.of_not_hasFvar hw0.1, hw0.2.2.2.1⟩

set_option maxHeartbeats 16000000 in
/-- **THE GENERATED CALLS AT THE ADMISSIBLE FRAMES** (see the module docstring): at the
generated stage's context, a related (class, node) pair and a true decoding, every generated
call lands at a node related to its class (`NodeLands`). -/
theorem genNodeCalls {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)}
    {mpC : EnvModelM V μ envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState} {nested : Bool}
    (hctx : RecCtxBase V μ F envC envI pp cvTasR ctorsAsR mpC dR isRecR A kindsR nfsR posR)
    (R : GenRecRun μ F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nested posR cvTasR
      block ctorsAsR out)
    (h : ConLeche.RecStageG μ F envC pp cvTasR ctorsAsR (tgtRs out) (fun _ => False))
    (hg : ConLeche.ClassGenScoped R.g)
    (hTbl : ∀ e ∈ R.st.ctorNfs.toList, ConLeche.ScB pp.nP e.ty)
    {mk : EnvModelM V μ envI} (hmkC : LfpCover mk pp.toBlockShape.memberNames)
    (hmk : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks)
    (hag : ∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n)
    (hsubC : ∀ D ∈ mpC.lfpBlocks, D = dR.toLfp ∨ D ∈ mk.lfpBlocks)
    (htr : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mk.base2.acval envI ψ dd e = some ea →
        denoteMeta mpC.base2.acval envC ψ dd e = some ea)
    (hcoreK : BlockHoleCtxFacts mk.base2 dR pp.lps cvTasR pp.toBlockShape isRecR)
    {fvsP : List Expr} {ns : List PosTree}
    (hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?) t)
    (hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns)
    (hpar : ∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids)
    (hsem : ∀ t ∈ ns, ∀ ψ, NodeSemAt mk.base2 ψ (pp.nestCtx fvsP envI.find?)
      (dR.holeCtx ψ).reverse t)
    (hctxR : R.ctx = pp.nestCtx fvsP envI.find?)
    (hfrec : ∀ t ∈ ns, ConLeche.FrameRec (fueledOps .verified F) envI
      (pp.nestCtx fvsP envI.find?) R.st.ctorNfs.toList t.anc t.key.lvls t.key.ds t.grp)
    (hmemF : MemberForests F envI pp cvTasR ctorsAsR nfsR fvsP R.st.ctorNfs.toList ns)
    {par : Nat → Nat} (hPP : ParentPtrs ns par)
    (hF : NodeListFacts mpC (pp.nestCtx fvsP envI.find?) ns)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind)
    {ψ : Name → Nat} {ρ : Nat → V} {xs : List V}
    (hparams : SpineFit ρ (dR.params ψ) (xs.take dR.nP)) (hxs : dR.nP ≤ xs.length)
    (hfrT : NodeFrameTie mpC.base2.acval (pp.nestCtx fvsP envI.find?) pp.toBlockShape
      out ns ψ ρ xs envC F (cvTasR.map (·.type))) :
    ∀ c b, c < (tgtRs out).length →
      nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find?) dR pp.toBlockShape out ns
        ψ ρ xs envC F (cvTasR.map (·.type)) c b → ∀ t j fs,
      t ∈ˢ (nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
        (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)
        (tgtClsM mc pp.toBlockShape out c) →
      (nlDb mpC dR ns b).HFits (nlψ envC ns ψ b)
        (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)
        ((nlDb mpC dR ns b).carrier (nlψ envC ns ψ b)
          (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)) t
        (tgtClsM mc pp.toBlockShape out c) j fs →
      ∀ c' t' y, c' < (tgtRs out).length →
        t' ∈ˢ tgtClsIs dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c' →
        y ∈ˢ app (tgtClsCr dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c') t' →
        genCallT (tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ) ρ
          (fun c j => genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j) xs c j fs
          (tagged c' t' y) →
        ∃ b', nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find?) dR pp.toBlockShape
            out ns ψ ρ xs envC F (cvTasR.map (·.type)) c' b' ∧
          NodeLands (ns.length + 1) (nlDb mpC dR ns) (nlψ envC ns ψ)
            (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs) (nlDp ns)
            (nodeAdm mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs par) b
            (tgtClsM mc pp.toBlockShape out c) t j fs b' (tgtClsM mc pp.toBlockShape out c') t' y := by
  intro c b hc hR t j fs ht hHF c' t' y hc' ht' hy hcall
  obtain rfl := CheckMode.eq_verified hμ
  have hctx' := hctx
  obtain ⟨hPos, henvC, hnames, hndM, hN, hS, hcore, hctorsAs, hdR, hlfp, hcov, -, -, -⟩ := hctx'
  obtain ⟨hparF, hparS⟩ := canonPars_of_forests hctx hmemF
  obtain ⟨cvTa0, rest0, holes0, hcv0, hop0, hholes0, hMF⟩ := hmemF
  have H := dynCtx_of hctx hmkC hmk hag hsubC htr hcoreK hok hkids hpar hsem hF hparF hparS
  have hmr : BlockMembersRun mpC.base2 dR pp.toBlockShape cvTasR := by
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; exact blockMembersRun_seam hN hS hcore
  have hrs : ∀ c (hc : c < (tgtRs out).length),
      (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := fun c hc => List.getElem?_eq_getElem hc
  have hnPc : ∀ c, c < (tgtRs out).length →
      (pp.nestCtx fvsP envI.find?).nP ≤ tgtRP pp.toBlockShape c := by
    intro c hc
    obtain ⟨-, hlen, hall⟩ := ConLeche.recStageG_recNames h
    obtain ⟨_, _, _, _, -, -, hle, -⟩ := hall c (by rw [← hlen]; exact hc)
    exact hle
  have hpd : ∀ c, c < (tgtRs out).length →
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        = tgtRP pp.toBlockShape c := fun c hc => blockRulePdomsAV_length hμ mpC h (hrs c hc) ψ
  -- the rule side: the class's decoding, fitting the rule
  obtain ⟨hDeq, hψeq, hFreq⟩ := nlRel_tie (Dc := Dc) (mc := mc) (cvc := cvc) hcov hF hcls hsel
    hnPc hpd hfrT hc hR
  have hti : t ∈ˢ tgtClsIs dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c := by
    unfold tgtClsIs; rw [ite_eq_left hR.1, hDeq, hψeq, hFreq]; exact ht
  have hxl : xs.length = R.pre.length := by
    rw [(tgtClsIs_pref hti).length_eq, blockRulePdomsAV_length hμ mpC h (hrs c hc) ψ]
    exact (genRec_at R hg hc).2.1
  have hjM : j < (tgtMajor out c).ctors.length := by
    have hj0 := hHF.1
    rw [← hDeq, genNCt R hg hdR hcls hc] at hj0
    exact hj0
  -- THE CALL, decoded: a recursive field of the class's constructor
  obtain ⟨cls, M₀, nfs, cA, x, iF, tt, tele, fvsR, oR, ws, xsO, leafO, bs, hcl, hlt, hM₀, hMs,
    hMeq, ⟨CM⟩, hnfs, hcA, hxj, ⟨Rc⟩, hiK, hkK, hopR, hws, hopO, hrr, hrl, hbsO, hv⟩ :=
    genCall_data R hc hjM mpC.base2.acval (genBit pp ψ) ψ _ ρ hcall
  generalize hrdef : genRecIdx R.rd tt = r at hrr hrl hv
  have hcal : r < (tgtRs out).length := hrl
  -- the rule's declared fields
  have hnF : x.nF = cA.2 := congrArg ClassCtor.nF Rc.hx
  have hxmem : x ∈ R.g.ctors.getD cls [] := List.mem_of_getElem? hxj
  have hpl : R.pre.length = pp.nP + R.rd.slots.length := (genRec_at R hg hc).2.2.1
  obtain ⟨hlR, hfvR, -⟩ := ConLeche.ScB.openPis hopR ((hg.tyD cls x hxmem).mono
    (show R.g.nP ≤ R.pre.length by show pp.nP ≤ _; omega))
  have hfvF' : ∀ l, l < fvsR.length → ∃ ty, fvsR[l]? = some (.fvar (R.pre.length + l) ty) := by
    intro l hl
    obtain ⟨z, hz⟩ : ∃ z, fvsR[l]? = some z := ⟨_, List.getElem?_eq_getElem hl⟩
    obtain ⟨ty, rfl, -⟩ := hfvR l z hz
    exact ⟨ty, hz⟩
  have hfvWF : ∀ z ∈ fvsR, Expr.WScoped (R.pre.length + fvsR.length) z := by
    intro z hz
    obtain ⟨l, hl⟩ := List.getElem?_of_mem hz
    obtain ⟨ty, rfl, hty⟩ := hfvR l _ hl
    have hll := (List.getElem?_eq_some_iff.mp hl).1
    exact (ConLeche.ScB.fvar (by omega) hty).1
  have hnPr : (pp.nestCtx fvsP envI.find?).nP ≤ R.pre.length := by
    show pp.nP ≤ _; omega
  have hxsC : (pp.nestCtx fvsP envI.find?).nP ≤ xs.length := by rw [H.hnP]; exact hxs
  have hwb : ∀ d e w, (fueledOps .verified F).whnf envI d e = .ok w →
      e.looseBVarsBounded 0 = true → w.looseBVarsBounded 0 = true :=
    fun d e w hw hb => ConLeche.whnf_looseBVars mk.base2.wf F hw hb
  -- the callee's class: the family's recursor at the `ih`'s class
  obtain ⟨clsR, M₀R, nfsR', hclR, -, -, hMsR, hMtR, ⟨CMt⟩, -⟩ := genTgtMajor R hcal
  rw [hrr] at hclR
  obtain rfl : tt = clsR := Option.some.inj hclR
  have hMsT : R.Ms.getD tt default = tgtMajor out r := by
    rw [hMtR, List.getD_eq_getElem?_getD, hMsR, Option.getD_some]
  -- a group name is no member
  have hgrpNM : ∀ {o : PosTree}, o ∈ ns → ∀ n ∈ o.grp.map (·.1),
      n ∉ pp.toBlockShape.memberNames := by
    intro o ho n hn hmem
    obtain ⟨D, hD, -, h2⟩ := posNodeOk_blk H.hcov (H.hok o ho) n hn
    obtain ⟨i, hi, rfl⟩ := exists_member_of_mem_names (lfp_namesLen mk hD) h2
    exact hmkC.fresh D hD i hi hmem
  -- an outside callee landing at a related node: its component and tuple there
  have htupOut : ∀ {o : Nat}, nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find?) dR
      pp.toBlockShape out ns ψ ρ xs envC F (cvTasR.map (·.type)) r o → (tgtMajor out r).member = none →
      tgtClsM mc pp.toBlockShape out r = nlComp mpC dR ns o (tgtMajor out r).ind ∧
      tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ r
        = tupW ((nlDb mpC dR ns o).u (nlComp mpC dR ns o (tgtMajor out r).ind)
          (nlψ envC ns ψ o)) := by
    intro o hRo hMo'
    obtain ⟨hD', hψ', -⟩ := nlRel_tie (Dc := Dc) (mc := mc) (cvc := cvc) hcov hF hcls hsel hnPc
      hpd hfrT hcal hRo
    have hTO' := hcls _ hcal hMo'
    have hcomp : nlComp mpC dR ns o (tgtMajor out r).ind = mc r := by
      unfold nlComp
      rw [← hD']
      simp only [tgtClsD, hMo', Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [← hTO'.hmem]
      exact idxOf_member hTO'.hnN hTO'.hkN hTO'.hmm
    have hM' : tgtClsM mc pp.toBlockShape out r = mc r := by
      simp [tgtClsM, hMo']
    refine ⟨by rw [hM', hcomp], ?_⟩
    funext is
    simp only [tgtClsTup, tgtClsU]
    rw [hD', hψ', hM', hcomp]
  have hbN : b ≤ ns.length := by
    rcases hR.2 with ⟨-, h'⟩ | ⟨-, h', -⟩
    · omega
    · exact h'
  /- The visited node: node `0` (the member constructors, stack `[]`) or a
  derived node (its group's constructors, over its stack `prog`) — the walked
  constructor, its reading at an admissible visit, the owners of its stack's
  holes, and the listed nodes its container instances land at. -/
  obtain ⟨prog, own, nF, crest, ks, nds, cur, ts, hd, hcrC, hcurC, hndC, hndl, hnFc, hK, hread,
      hvisit, hstk, hkidN⟩ : ∃ (prog : List NestHole) (own : Nat → Nat) (nF : Nat) (crest : Expr)
      (ks : List NestFieldKind) (nds : List (Expr × ConLeche.BinderMeta)) (cur : Expr)
      (ts : List PosTree),
      PosD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?)
        (.tele prog ((pp.nestCtx fvsP envI.find?).hiAt prog.length) nF 0 crest ks
          nds cur) ts ∧
      crest.looseBVarsBounded 0 = true ∧ cur.looseBVarsBounded 0 = true ∧
      (∀ (l : Nat) (p : Expr × ConLeche.BinderMeta), nds[l]? = some p →
        p.1.looseBVarsBounded 0 = true ∧
          Expr.WScoped ((pp.nestCtx fvsP envI.find?).hiAt prog.length + l) p.1) ∧
      nds.length = nF ∧
      nF = cA.2 ∧
      GenK53At F envC pp.toBlockShape (cvTasR.map (·.type)) (R.Ms.getD tt default) fvsR x.tyN iF
        tele ((ConLeche.closeTelescope nds
          ((pp.nestCtx fvsP envI.find?).hiAt prog.length) cur).replaceFVars
            (ConLeche.nestHoleImg (pp.nestCtx fvsP envI.find?) prog)) ∧
      NodeHolesRead mpC.base2.acval envC (pp.nestCtx fvsP envI.find?) prog ∧
      (∀ (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V),
        nodeAdm mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs par b G ρ' →
        ∀ Y, InTupleSpace ((nlDb mpC dR ns b).w (nlψ envC ns ψ b)) (nlDb mpC dR ns b).N
            ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
              (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)) Y →
        (nlDb mpC dR ns b).HFits (nlψ envC ns ψ b) ρ' Y t (tgtClsM mc pp.toBlockShape out c) j fs →
        ∃ σN, AdmVal mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs own
            (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
              (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)) Y) prog σN ∧
          fs.length = nF ∧
          ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
            ∃ nda, denoteMeta mpC.base2.acval envC ψ
                ((pp.nestCtx fvsP envI.find?).hiAt prog.length + i) nd = some nda ∧
              fs.getD i pt ∈ˢ interp V (consList (fs.take i) σN) nda ∧
              AnnotValid V (consList (fs.take i) σN) nda) ∧
      (prog = [] ∨ ∃ u, 0 < b ∧ ns.getD (b - 1) default = u ∧
        (ConLeche.grpNews u.key.lvls u.key.ds
          ((pp.nestCtx fvsP envI.find?).hiAt u.anc.length) u.grp).reverse ++ u.anc
            = prog ∧
        own = fun i => if i < u.anc.length then holeOwner ns par b i else b) ∧
      (∀ u'' ∈ ts, u''.occ = prog → u'' ∈ ns ∧ ∃ b'', 0 < b'' ∧ b'' ≤ ns.length ∧
        ns.getD (b'' - 1) default = u'' ∧ nlDp ns b < nlDp ns b'' ∧
        (u''.anc = prog → u''.anc ≠ [] → holeOwner ns par b'' = own)) := by
    by_cases hb0 : b = 0
    · /- ### Node `0` -/
      subst hb0
      have hmem : (tgtMajor out c).member.isSome = true := by
        obtain ⟨-, ⟨h', -⟩ | ⟨h', -⟩⟩ := hR
        · exact h'
        · exact absurd h' (Nat.lt_irrefl 0)
      obtain ⟨m, hmb⟩ : ∃ m, (tgtMajor out c).member = some m := Option.isSome_iff_exists.mp hmem
      obtain ⟨hrt, hcsR, hfiM, hlvM, hdsM, -⟩ := (genRec_at R hg hc).2.2.2 m hmb
      have hmM : tgtClsM mc pp.toBlockShape out c = m := by simp [tgtClsM, hmem, hrt]
      have hmc : m < ctorsAsR.length := (List.getElem?_eq_some_iff.mp hcsR).1
      have hctM : dR.ctorsM m = (tgtMajor out c).ctors := by
        have := hctorsAs m hmc; rw [hcsR] at this; exact (Option.some.inj this).symm
      have hcA' : (tgtMajor out c).ctors[j]? = some cA := by rw [hMeq]; exact hcA
      have hcj : (dR.ctorsM m)[j]? = some cA := by rw [hctM]; exact hcA'
      have hfacts : pp.toBlockShape.memberNames = dR.memberNames ∧ pp.nP = dR.nP ∧
          pp.nIdxs = dR.nIdxs ∧ dR.k = dR.memberNames.length ∧ m < dR.k := by
        obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
        exact ⟨rfl, rfl, rfl, by simp [blockDataOf, blockDataPre, BlockData.withPhi,
          ConLeche.BlockShape.k, ConLeche.BlockShape.memberNames],
          by
            have h1 := (List.findIdx?_eq_some_iff_getElem.mp hfiM).1
            simpa [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
              ConLeche.BlockShape.memberNames] using h1⟩
      obtain ⟨hnamesD, hnPD, hnIdxsD, hkD, hmk⟩ := hfacts
      obtain ⟨hfC, -⟩ := hcore.2.2.2 m hmk j cA hcj
      have hw := mpC.base2.wf _ (List.mem_of_find?_eq_some hfC)
      -- the member forest
      obtain ⟨crest, ks, ts, hcrest, hd, ⟨ty, hty⟩, hforest, he⟩ :=
        hMF m _ (by rw [hcsR, ← hctM]) j cA hcj
      obtain ⟨nds, cur, htele0, htyN, hndC, hnl, hcrC, hcurC, -, hsemB⟩ := blk_ctorFit mk ψ hN
        hcoreK hnamesD rfl hnPD hkD hcv0 hop0 hholes0 hcj hw.1 hw.2.2.2.1 hcrest hty hd
      -- the entry: the member constructor's recorded normal form (the root
      -- frame's, `MemberForests`), the class matching it (its parameters the
      -- canonical ones)
      have hlP : fvsP.length = pp.nP := ConLeche.Verify.openPisAtFvars_length _ hop0
      have hdsE : M₀.ds = fvsP := by
        have e1 : (tgtMajor out c).ds = M₀.ds := by rw [hMeq]
        rw [← e1, hdsM, hctxR]
        show fvsP.take pp.nP = fvsP
        rw [List.take_of_length_le (Nat.le_of_eq hlP)]
      have hpfE : M₀.pfvs = fvsP := by rw [CM.pfvs_eq, hctxR]; rfl
      have hlvE : M₀.lvls = pp.lps.map .param := by
        have e1 : (tgtMajor out c).lvls = M₀.lvls := by rw [hMeq]
        rw [← e1, hlvM]
      have hCM : ConLeche.targetClassMatch (fueledOps .verified F) envC pp.toBlockShape
          (cvTasR.map (·.type)) M₀.pfvs M₀.lvls M₀.ds
          ((pp.nestCtx fvsP envI.find?).lps.map .param)
          (pp.nestCtx fvsP envI.find?).params = .ok true := by
        rw [hlvE, hdsE]
        refine ConLeche.targetClassMatch_self (fun a ha => ?_) (erasedEqs_refl' _)
        obtain ⟨q, hq⟩ := List.getElem?_of_mem ha
        obtain ⟨ty', rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ hop0 q _ hq
        have hql : q < fvsP.length := (List.getElem?_eq_some_iff.mp hq).1
        refine ⟨by rw [ConLeche.Expr.bvarB_eq]; rfl, ?_⟩
        rw [ConLeche.Expr.fvarB_eq, hpfE]
        simp only [ConLeche.Expr.fvarRange]
        omega
      have hK := genK53_entry R hg hTbl Rc hMs hnfs hcA hxj hkK hopR he rfl hCM
      rw [htyN] at hK
      -- the members' index counts
      have hids0 : ∀ t, t < (pp.nestCtx fvsP envI.find?).names.length →
          (dR.toLfp.ids t ψ).length = (pp.nestCtx fvsP envI.find?).nIdxs.getD t 0 := by
        intro t htn
        have htk : t < dR.k := by rw [hkD, ← hnamesD]; exact htn
        have := blockMembers_IdsM_length hmr htk ψ
        rw [BlockData.nIdxAt, ← hnIdxsD] at this
        exact this
      have hnl0 : nlDb mpC dR ns 0 = dR.toLfp := by unfold nlDb; rw [ite_eq_left rfl]
      have hnψ0 : nlψ envC ns ψ 0 = ψ := by unfold nlψ; rw [ite_eq_left rfl]
      have hnF0 : nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs 0
          = consList (xs.take dR.nP) ρ := by unfold nlFr; rw [ite_eq_left rfl]
      have hsP : Sat V (dR.params ψ).reverse (consList (xs.take dR.nP) ρ) := by
        have := sat_of_spineFit (Sat_nil (V := V) ρ) hparams
        rwa [List.append_nil] at this
      -- the constructor at an admissible visit: the hole frame
      have hvisit : ∀ (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V),
          nodeAdm mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs par 0 G ρ' →
          ∀ Y, InTupleSpace ((nlDb mpC dR ns 0).w (nlψ envC ns ψ 0)) (nlDb mpC dR ns 0).N
              ((nlDb mpC dR ns 0).idx (nlψ envC ns ψ 0)
                (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs 0)) Y →
          (nlDb mpC dR ns 0).HFits (nlψ envC ns ψ 0) ρ' Y t (tgtClsM mc pp.toBlockShape out c) j fs →
          ∃ σN, (∀ own, AdmVal mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs own
              (addOwn G 0 (nlDb mpC dR ns 0).N ((nlDb mpC dR ns 0).idx (nlψ envC ns ψ 0)
                (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs 0)) Y) [] σN) ∧
            fs.length = cA.2 ∧
            ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
              ∃ nda, denoteMeta mpC.base2.acval envC ψ
                  ((pp.nestCtx fvsP envI.find?).hiAt ([] : List NestHole).length + i) nd
                    = some nda ∧
                fs.getD i pt ∈ˢ interp V (consList (fs.take i) σN) nda ∧
                AnnotValid V (consList (fs.take i) σN) nda := by
        intro G ρ' hA Y hY hH
        have hA' := hA
        unfold nodeAdm at hA'
        rw [ite_eq_left rfl] at hA'
        subst hA'
        rw [hnl0, hnψ0, hnF0, hmM] at hH
        have hY' := hY
        rw [hnl0, hnψ0, hnF0] at hY'
        refine ⟨dR.toLfp.frame ψ (consList (xs.take dR.nP) ρ) Y,
          fun own => admVal_frame0 H ψ ρ xs hparams hids0 hY' own G, ?_, fun i nd hnd => ?_⟩
        · exact (hsemB _ (frame0_sat H ψ hsP hY') fs hH.2.1).1
        obtain ⟨-, hmemB⟩ := hsemB _ (frame0_sat H ψ hsP hY') fs hH.2.1
        obtain ⟨nda, hnda, hmemI, hval⟩ := hmemB i nd hnd
        exact ⟨nda, H.htr ψ _ nd hnda, hmemI, hval⟩
      have hread : NodeHolesRead mpC.base2.acval envC (pp.nestCtx fvsP envI.find?) [] := by
        refine nodeHolesRead_nil H.hparF H.hparS fun n hn => ?_
        change n ∈ pp.toBlockShape.memberNames at hn
        obtain ⟨c0, hc0, rfl⟩ := List.getElem_of_mem hn
        have hck : c0 < dR.k := by rw [hkD, ← hnamesD]; exact hc0
        obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTasR[c0]? = some cvTb :=
          ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hck)⟩
        have hname := hN.1 c0 cvTb hcvb
        have hlpsT := hS.lpsT c0 cvTb hck hcvb
        obtain ⟨hf, -⟩ := hcore.1 c0 cvTb hcvb
        rw [← hname] at hf
        unfold BlockData.memberName at hf
        rw [← hnamesD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc0,
          Option.getD_some] at hf
        refine ⟨_, hf, ?_⟩
        show pp.lps.length = cvTb.levelParams.length
        rw [hlpsT]
      refine ⟨[], fun _ => 0, cA.2, crest, ks, nds, cur, ts, htele0, hcrC, hcurC, hndC, hnl, rfl,
        hK, hread, fun G ρ' hA Y hY hH => ?_, Or.inl rfl, fun u'' hu'' _ => ?_⟩
      · obtain ⟨σN, hAdm, hfsl, hmemN⟩ := hvisit G ρ' hA Y hY hH
        exact ⟨σN, hAdm _, hfsl, hmemN⟩
      · have hu''ns : u'' ∈ ns := hforest u'' (PosTree.mem_forest_iff.mpr
          ⟨u'', hu'', PosTree.mem_nodes.mpr (Or.inl rfl)⟩)
        obtain ⟨b'', hb''0, hb''l, hb''u⟩ := exists_pos hu''ns
        refine ⟨hu''ns, b'', Nat.pos_of_ne_zero hb''0, hb''l, hb''u, ?_, fun h1 h2 => absurd h1 h2⟩
        unfold nlDp
        rw [ite_eq_left rfl, ite_eq_right hb''0, hb''u]
        have h2 := height_le_nlDd hu''ns
        omega
    · /- ### A derived node -/
      have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      obtain ⟨-, ⟨-, hb0'⟩ | ⟨-, hbl, hNM⟩⟩ := hR
      · exact absurd hb0' hb0
      have hu : ns.getD (b - 1) default ∈ ns := getD_mem_of_lt hbpos hbl
      obtain ⟨u, hub⟩ : ∃ u, ns.getD (b - 1) default = u := ⟨_, rfl⟩
      rw [hub] at hu hNM
      have hMo : (tgtMajor out c).member = none := hNM.1
      have hTO := hcls c hc hMo
      have hnlDb : nlDb mpC dR ns b = lfpSel mpC dR.toLfp u.key.cname := by
        unfold nlDb; rw [ite_eq_right hb0, hub]
      have hnlψ : nlψ envC ns ψ b = nodeψ envC ψ u := by unfold nlψ; rw [ite_eq_right hb0, hub]
      have hDc : Dc c = lfpSel mpC dR.toLfp u.key.cname := by
        have := hDeq; rw [hnlDb] at this; simpa [tgtClsD, hMo] using this
      have hmc : tgtClsM mc pp.toBlockShape out c = mc c := by simp [tgtClsM, hMo]
      have hm : mc c < (lfpSel mpC dR.toLfp u.key.cname).k := hDc ▸ hTO.hmm
      have hjn : j < (lfpSel mpC dR.toLfp u.key.cname).nctors (mc c) := by
        have := hHF.1; rwa [hnlDb, hmc] at this
      obtain ⟨cv, nF, ctors, crest, ks, nds, cur, ts', hcvI, hctors, hxmem, hcr, hd, hts', hndl, hcrC,
        hcurC, hndC, hsemU⟩ := dyn_ctorFit H hu ψ hm hjn
      -- the rule's constructor is the node's
      have hcAM : (tgtMajor out c).ctors[j]? = some cA := by rw [hMeq]; exact hcA
      have hjM' : j < (tgtMajor out c).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
      have hcAj : (tgtMajor out c).ctors[j] = cA := by
        rw [List.getElem?_eq_getElem hjM'] at hcAM; exact Option.some.inj hcAM
      have hcn : (cv, nF).1.name = cA.1.name := by
        have e1 := ConLeche.Semantics.Env.find?_name hcvI
        have e2 := ConLeche.Semantics.Env.find?_name (hTO.hctor j hjM')
        rw [hDc] at e2
        simp only [ConLeche.ConstantInfo.name] at e1 e2
        rw [hcAj] at e2
        exact e1.trans e2.symm
      -- its field count: the recorded clause's, at both environments
      have hnFc : nF = cA.2 := by
        obtain ⟨hDmk, -⟩ := dyn_nodeBlock H hu
        have h1 := lfpCtor_fieldsLen hDmk hm hjn hcvI ψ
        have h2 := tgtOutCls_fieldsLen hTO hcAM ψ
        rw [hDc] at h2
        omega
      have hK := genK53_entry R hg hTbl Rc hMs hnfs hcA hxj hkK hopR
        ((hfrec u hu).entry hctors hxmem hcr hd) hcn (by
          show ConLeche.targetClassMatch _ _ _ _ M₀.pfvs M₀.lvls M₀.ds u.key.lvls
            (u.key.ds.map (·.replaceFVars (ConLeche.nestHoleImg
              (pp.nestCtx fvsP envI.find?)
              ((ConLeche.grpNews u.key.lvls u.key.ds
                ((pp.nestCtx fvsP envI.find?).hiAt u.anc.length) u.grp).reverse
                ++ u.anc)))) = _
          rw [entryDs_readback (H.hok u hu)]
          have hNM2 := hNM.2.2
          unfold ClassMatches at hNM2
          rw [hMeq] at hNM2
          exact hNM2)
      simp only [ConLeche.nestCtorNf] at hK
      generalize hprog : (ConLeche.grpNews u.key.lvls u.key.ds
        ((pp.nestCtx fvsP envI.find?).hiAt u.anc.length) u.grp).reverse ++ u.anc = prog
        at hK
      have hhiP : (pp.nestCtx fvsP envI.find?).hiAt prog.length
          = (pp.nestCtx fvsP envI.find?).hiAt u.anc.length + u.grp.length := by
        rw [← hprog]
        simp only [List.length_append, List.length_reverse, ConLeche.grpNews, List.length_map,
          ConLeche.NestCtx.hiAt]
        omega
      rw [hprog, ← hhiP] at hd
      rw [← hhiP] at hndC hK
      -- the node's constructor at an admissible visit
      have hvisit : ∀ (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V),
          nodeAdm mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs par b G ρ' →
          ∀ Y, InTupleSpace ((nlDb mpC dR ns b).w (nlψ envC ns ψ b)) (nlDb mpC dR ns b).N
              ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
                (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)) Y →
          (nlDb mpC dR ns b).HFits (nlψ envC ns ψ b) ρ' Y t (tgtClsM mc pp.toBlockShape out c) j fs →
          ∃ σN, AdmVal mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs
              (fun i => if i < u.anc.length then holeOwner ns par b i else b)
              (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
                (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)) Y) prog σN ∧
            fs.length = nF ∧
            ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
              ∃ nda, denoteMeta mpC.base2.acval envC ψ
                  ((pp.nestCtx fvsP envI.find?).hiAt prog.length + i) nd = some nda ∧
                fs.getD i pt ∈ˢ interp V (consList (fs.take i) σN) nda ∧
                AnnotValid V (consList (fs.take i) σN) nda := by
        intro G ρ' hA Y hY hH
        have hA' := hA
        unfold nodeAdm at hA'
        rw [ite_eq_right hb0, hub] at hA'
        obtain ⟨σ, hσ, rfl⟩ := hA'
        have hidxEq := (dyn_hAdm H ψ ρ xs hparams par b (by omega) G _ hA).2
        rw [hnlDb, hnlψ, hmc] at hH
        rw [hnlDb, hnlψ] at hidxEq
        have hY' : InTupleSpace ((lfpSel mpC dR.toLfp u.key.cname).w (nodeψ envC ψ u))
            (lfpSel mpC dR.toLfp u.key.cname).N ((lfpSel mpC dR.toLfp u.key.cname).idx (nodeψ envC ψ u)
              (keyFrame (nodeDsaI mk (pp.nestCtx fvsP envI.find?) ψ u)
                ((pp.nestCtx fvsP envI.find?).hiAt u.anc.length) σ)) Y := by
          intro m' hm'
          rw [hidxEq m' hm']
          have := hY m' (by rw [hnlDb]; exact hm')
          rwa [hnlDb, hnlψ] at this
        obtain ⟨hsatN, hfl, hmem⟩ := hsemU σ hσ.sat Y hY' t fs hH
        refine ⟨_, admVal_kid H hbpos hbl hub hσ hsatN (fun i => rfl)
          (u' := .node [] prog default [] []) hprog.symm, hfl, fun i nd hnd => ?_⟩
        obtain ⟨nda, hnda, hmemI, hval⟩ := hmem i nd hnd
        rw [← hhiP] at hnda
        exact ⟨nda, H.htr ψ _ nd hnda, hmemI, hval⟩
      have hread : NodeHolesRead mpC.base2.acval envC (pp.nestCtx fvsP envI.find?) prog := by
        rw [← hprog]
        have hrdA : NodeHolesRead mpC.base2.acval envC (pp.nestCtx fvsP envI.find?) u.anc := by
          have h := hF.read u hu
          obtain ⟨-, -, -, -, -, hanc⟩ := H.hok u hu
          rcases hanc with ⟨hao, -⟩ | ⟨han, -⟩
          · rwa [hao]
          · rw [han]
            have h' : NodeHolesRead mpC.base2.acval envC (pp.nestCtx fvsP envI.find?)
                (u.occ ++ []) := by rwa [List.append_nil]
            exact h'.suffix
        obtain ⟨nPc0, ctorsAs0, henvC0⟩ := H.henvC
        exact nodeHolesRead_grp' (H.hok u hu) hrdA
          (fun ψ' => ⟨_, DenoteMetaSpine.transport (fun e _ he => H.htr ψ' _ e he)
            (dyn_dsaI H hu ψ')⟩)
          (grp_find_of H.hcov H.hsub henvC0 (H.hok u hu))
      refine ⟨prog, fun i => if i < u.anc.length then holeOwner ns par b i else b, nF, crest, ks, nds,
        cur, ts', hd, hcrC, hcurC, hndC, hndl, hnFc, hK, hread, hvisit,
        Or.inr ⟨u, hbpos, hub, hprog, rfl⟩,
        fun u'' hu'' hocc => ?_⟩
      have hkid : u'' ∈ u.kids := hts' u'' hu''
      have hu''ns : u'' ∈ ns := H.hkids u hu u'' hkid
      obtain ⟨b'', hb''0, hb''l, hb''u, hparb''⟩ := hPP.2 b hbpos hbl u'' (by rw [hub]; exact hkid)
      -- the kid is deeper than its parent
      have hprogNE : prog ≠ [] := by
        rw [← hprog]
        obtain ⟨hne, -⟩ := posD_frame_inv (H.hok u hu).1
        intro h0
        have := congrArg List.length h0
        simp [ConLeche.grpNews] at this
        exact hne this.1
      have hbb : b < b'' := by
        obtain ⟨-, hlt', hk'⟩ := hPP.1 b'' hb''0 hb''l (by rw [hb''u, hocc]; exact hprogNE)
        rw [hparb''] at hlt'; exact hlt'
      refine ⟨hu''ns, b'', hb''0, hb''l, hb''u, ?_, fun _ _ => funext (holeOwner_kid hparb'' hbb hub)⟩
      unfold nlDp
      rw [ite_eq_right hb0, ite_eq_right (by omega), hub, hb''u]
      have h1 := PosTree.height_kid hkid
      have h2 := height_le_nlDd hu
      omega
  -- the true visit: the fields' count, and the call's telescope fits
  obtain ⟨σT, hAT, hflT, hmemT⟩ := hvisit (fun _ _ _ _ => True) _
    (dyn_top H ψ ρ xs hparams hxs hPP b (by omega) _ (fun _ _ _ _ _ _ _ _ _ => trivial)) _
    (lfpTuple_mem _ _ _ _) hHF
  have hfsl : fs.length = cA.2 := by rw [hflT, hnFc]
  have hlenF : fvsR.length = nds.length := by rw [hlR, hnF, hndl, hnFc]
  have hiF : iF < fvsR.length := by rw [hlR]; exact hiK
  have hiN : iF < nds.length := by rw [← hlenF]; exact hiF
  have hflF : fs.length = fvsR.length := by rw [hfsl, hlR, hnF]
  obtain ⟨e, k, nd, tsi, hnd, hfd, heC, htsi⟩ := tele_field hd hcrC (i := iF)
    (by rw [← hndl]; exact hiN)
  -- K.53′ at the rule's fields
  obtain ⟨ws', teleR, leafR, I, us, us', Pw, fR, hws', hstR, hleafHd, hIM, hfR, hErase, hmentW,
    hcmW, hPwB⟩ := hK
  rw [hws] at hws'
  obtain rfl := Option.some.inj hws'
  have hcmW' : ClassMatches F envC pp.toBlockShape (cvTasR.map (·.type)) (tgtMajor out r)
      us' Pw := by
    unfold ClassMatches; rw [← hMsT]; exact hcmW
  obtain ⟨hlvW, hPwM⟩ := ConLeche.targetClassMatch_true hcmW'
  obtain ⟨hPwLen, hPwAll⟩ := ConLeche.targetParamsDefEq_true hPwM
  have hIMt : I = (tgtMajor out r).ind := by rw [hIM, hMsT]
  have hnPcT : (R.Ms.getD tt default).nPc = (tgtMajor out r).nPc := by rw [hMsT]
  have hKX : ((ConLeche.targetPiDomsWith fvsR ((ConLeche.closeTelescope nds
      ((pp.nestCtx fvsP envI.find?).hiAt prog.length) cur).replaceFVars
        (ConLeche.nestHoleImg (pp.nestCtx fvsP envI.find?) prog))).getD
          [])[iF]?.map Expr.eraseFVarTys
      = some (Expr.mkPisOf teleR (Expr.mkAppN (.const I us')
          (Pw ++ leafR.getAppArgs.drop (R.Ms.getD tt default).nPc))).eraseFVarTys := by
    rw [hfR, Option.map_some, hErase]
  have hmajX : (Expr.mkAppN (.const I us')
      (Pw ++ leafR.getAppArgs.drop (R.Ms.getD tt default).nPc)).instantiateList
        (locOpen (R.pre.length + fvsR.length) teleR.length) 0
      = Expr.mkAppN (.const I us') (Pw ++ (leafR.getAppArgs.drop (R.Ms.getD tt default).nPc).map
        (·.instantiateList (locOpen (R.pre.length + fvsR.length) teleR.length) 0)) := by
    rw [instantiateList_mkAppN, List.map_append,
      show Pw.map (·.instantiateList (locOpen (R.pre.length + fvsR.length) teleR.length) 0) = Pw
        from (List.map_congr_left fun x hx => ConLeche.Expr.instantiateList_eq_self (hPwB x hx)).trans
          (List.map_id' _),
      ConLeche.Expr.instantiateList_eq_self (show (Expr.const I us').looseBVarsBounded 0 = true
        from rfl)]
  have hmentX : (Expr.mkAppN (.const I us') Pw).nestOcc
      (pp.nestCtx fvsP envI.find?).names 0 0 = true := hmentW
  obtain ⟨teleW, leafC, w, pre, hndEq, htl, htel, hteleHF, hopen, hwF, hargsLen, hpreE, hargs,
    hcase⟩ := callWalkSyn hwb H.hparS hread.2.1 hndC hcurC hfvF' hlenF hiN hnd hfd heC hKX hmajX
      hmentX
  -- the call's telescope: the `ih`'s, opened
  obtain ⟨teleO, leafO', hstO, hxsOl, hxsO, hleafO, hRO⟩ := openPis_stripPis_locOpen hopO
  rw [hstR] at hstO
  obtain ⟨rfl, rfl⟩ : teleR = teleO ∧ leafR = leafO' := by
    simpa only [Option.some.injEq, Prod.mk.injEq] using hstO
  have hteleL : teleR.length = tele := ConLeche.Expr.stripPis_length _ hstR
  obtain ⟨hparT, htailT⟩ := parTail_of_agree mpC _ ψ ρ xs hxsC hAT.agree
  obtain ⟨ndaT, hndaT, hfT, hvalT⟩ := hmemT iF nd hnd
  rw [hndEq] at hndaT
  have hbsF : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mpC.base2.acval envC ψ (R.pre.length + fvsR.length) []
        (teleR.map (·.1))).getD []) bs := by
    cases hTD : teleDoms mpC.base2.acval envC ψ (R.pre.length + fvsR.length) []
        (teleR.map (·.1)) with
    | some doms =>
      rw [Option.getD_some]
      rw [hlR] at hTD
      rw [← hRO mpC.base2.acval envC ψ doms hTD]
      exact hbsO
    | none =>
      exfalso
      have h0 := (fieldCall_core mpC.base2 ψ htl htel hteleHF hopen hwF (off := 0) (idxR := [])
        (fun _ _ _ h _ => by simp at h) hnPr hfvF' hfvWF
        hread hiF hndaT hxl hflF hparT htailT hfT hvalT (bs := [])
        (by rw [hTD]; trivial)).1
      have hte : teleR = [] := List.length_eq_zero_iff.mp h0.symm
      rw [hte] at hTD
      exact nomatch hTD
  have hbsl : bs.length = teleR.length :=
    (fieldCall_core mpC.base2 ψ htl htel hteleHF hopen hwF (off := 0) (idxR := [])
      (fun _ _ _ h _ => by simp at h) hnPr hfvF' hfvWF hread hiF
      hndaT hxl hflF hparT htailT hfT hvalT hbsF).1
  -- the call's target: the `ih`'s callee, index readings and applied field
  obtain ⟨hcr', ht'r, hyr⟩ := tagged_inj hv
  subst c' t' y
  have hyE : interp V (consList bs (consList (xs ++ fs) ρ))
      ((denoteMeta mpC.base2.acval envC ψ (R.pre.length + x.nF + xsO.length)
        (Expr.mkAppN (fvsR.getD iF default) xsO)).getD default) = bs.foldl app (fs.getD iF pt) := by
    obtain ⟨tyF, htyF⟩ := hfvF' iF hiF
    rw [hxsOl]
    refine genFap_read (m := tele) hiK ⟨tyF, ?_⟩ hxsO hxsOl hxl (by rw [hflF, hlR])
      (by rw [hbsl, hteleL]) ρ
    rw [List.getD_eq_getElem?_getD, htyF, Option.getD_some]
  rw [hyE]
  -- the index readings: the opened leaf's
  have hleafApp : leafR = Expr.mkAppN (.const I us) leafR.getAppArgs := by
    rw [← hleafHd, ConLeche.Expr.mkAppN_getApp]
  have hidxE : ((leafO.getAppArgs.drop (R.Ms.getD tt default).nPc).map fun e =>
        interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval envC ψ (R.pre.length + x.nF + xsO.length) e).getD default))
      = ((leafR.getAppArgs.drop (R.Ms.getD tt default).nPc).map
          (·.instantiateList (locOpen (R.pre.length + fvsR.length) teleR.length) 0)).map
        (fun xR => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval envC ψ (R.pre.length + fvsR.length + bs.length) xR).getD
            default)) := by
    have hL := hleafO
    rw [hleafApp, instantiateList_mkAppN] at hL
    obtain ⟨-, hlenA, hallA⟩ := erasedEq_getApp _ _ hL
    rw [ConLeche.Expr.getAppArgs_mkAppN] at hlenA hallA
    have hc0 : ∀ (os : List Expr) (d : Nat), ((Expr.const I us).instantiateList os d).getAppArgs
        = [] := by
      intro os d; rw [ConLeche.Expr.instantiateList_eq_self rfl]; rfl
    rw [hc0, List.nil_append] at hlenA hallA
    rw [List.map_map]
    apply List.ext_getElem?
    intro q
    rw [List.getElem?_map, List.getElem?_map, List.getElem?_drop, List.getElem?_drop]
    cases hq : leafO.getAppArgs[(R.Ms.getD tt default).nPc + q]? with
    | none =>
      have : (leafR.getAppArgs.map fun z => z.instantiateList
          (locOpen (R.pre.length + x.nF) tele) 0)[(R.Ms.getD tt default).nPc + q]? = none := by
        rw [List.getElem?_eq_none_iff] at hq ⊢; rw [← hlenA]; exact hq
      rw [List.getElem?_map] at this
      rw [Option.map_none]
      cases hq2 : leafR.getAppArgs[(R.Ms.getD tt default).nPc + q]? with
      | none => rfl
      | some _ => rw [hq2] at this; exact nomatch this
    | some a =>
      obtain ⟨b0, hb0⟩ : ∃ b0, leafR.getAppArgs[(R.Ms.getD tt default).nPc + q]? = some b0 := by
        have hl := (List.getElem?_eq_some_iff.mp hq).1
        exact ⟨_, List.getElem?_eq_getElem (by rw [hlenA, List.length_map] at hl; exact hl)⟩
      rw [hb0, Option.map_some, Option.map_some]
      have hab := hallA _ a _ hq (by rw [List.getElem?_map, hb0]; rfl)
      congr 1
      simp only [Function.comp]
      rw [denoteMeta_erasedEq hab, hlR, hbsl, hxsOl, hteleL]
  rw [hidxE]
  generalize hidxR : (leafR.getAppArgs.drop (R.Ms.getD tt default).nPc).map
    (·.instantiateList (locOpen (R.pre.length + fvsR.length) teleR.length) 0) = idxR
    at hargs hargsLen hpreE ⊢
  -- the callee's class: outside, it names no member
  have hcalOut : ∀ {o : PosTree}, o ∈ ns → I ∈ o.grp.map (·.1) →
      (tgtMajor out r).member = none ∧ I = (tgtMajor out r).ind := by
    intro o ho hIo
    refine ⟨?_, hIMt⟩
    cases hmb : (tgtMajor out r).member with
    | none => rfl
    | some m' =>
      exfalso
      obtain ⟨-, -, hfi', -⟩ := (genRec_at R hg hcal).2.2.2 m' hmb
      refine hgrpNM ho I hIo ?_
      rw [hIMt]
      obtain ⟨hlt', hb', -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi'
      have := beq_iff_eq.mp hb'
      rw [← this]; exact List.getElem_mem hlt'
  have hOutR : (tgtMajor out r).member = none → ∃ sI,
      pp.toBlockShape.memberNames.findIdx? (· == (tgtMajor out r).ind) = none ∧
      ConLeche.targetCtorsOf (mkFEnv envC) (tgtMajor out r).ind
        = some ((tgtMajor out r).nPc, (tgtMajor out r).ctors) ∧
      (tgtMajor out r).ds.length = (tgtMajor out r).nPc ∧
      ConLeche.targetOutsideInst (m := CheckM) (mkFEnv envC) (tgtMajor out r).ind
        (tgtMajor out r).lvls (tgtMajor out r).ds = .ok ((tgtMajor out r).nIdx, sI) := by
    intro hMo'
    rw [hMtR] at hMo' ⊢
    obtain ⟨sI, hfi, -, hct, hdsLen, -, hinst, -⟩ := CMt.outside_of hMo'
    exact ⟨sI, hfi, hct, hdsLen, hinst⟩
  -- an outside callee at a listed node naming it: as many parameters as the node's key
  have houtLen : ∀ {o : PosTree}, o ∈ ns → (tgtMajor out r).member = none →
      (tgtMajor out r).ind ∈ o.grp.map (·.1) →
      (tgtMajor out r).ds.length = o.key.ds.length := by
    intro o ho hMo' hind
    obtain ⟨sI, -, hct, hdsLen, hinst⟩ := hOutR hMo'
    have hlenP := genOutParamsLen hcov (hcls r hcal hMo') hinst hct hdsLen ψ
    rw [hsel r hcal hMo'] at hlenP
    obtain ⟨D, hD, h1, h2⟩ := posNodeOk_blk H.hcov (H.hok o ho) _ hind
    rw [lfpSel_eq_of_mem H.hcovC dR.toLfp (H.hsub D hD) h1 h2] at hlenP
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hlenPo, -, -⟩ := dyn_nodeBlock H ho
    rw [← hlenP, hlenPo]
  -- the call, at an admissible visit
  have hcallV : ∀ (off : Nat), (∀ (l : Nat) (xR xW : Expr), idxR[l]? = some xR →
      w.getAppArgs[off + l]? = some xW →
      Expr.ErasedEq xR (Expr.substFvars ((pp.nestCtx fvsP envI.find?).hiAt prog.length + iF)
        (R.pre.length + fvsR.length) (callSubst (pp.nestCtx fvsP envI.find?) prog fvsR) xW)) →
      (∀ (l : Nat) (xW : Expr), w.getAppArgs[off + l]? = some xW → ∃ xR, idxR[l]? = some xR) →
      ∀ (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V),
      nodeAdm mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs par b G ρ' →
      ∀ Y, InTupleSpace ((nlDb mpC dR ns b).w (nlψ envC ns ψ b)) (nlDb mpC dR ns b).N
          ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
            (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)) Y →
      (nlDb mpC dR ns b).HFits (nlψ envC ns ψ b) ρ' Y t (tgtClsM mc pp.toBlockShape out c) j fs →
      ∃ σN, AdmVal mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs own
          (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
            (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)) Y) prog σN ∧
        (∀ v, v < (pp.nestCtx fvsP envI.find?).nP →
          σN ((pp.nestCtx fvsP envI.find?).hiAt prog.length - 1 - v) = xs.getD v pt) ∧
        ∃ (ha : AnnotTerm) (argsA : List AnnotTerm),
          denoteMeta mpC.base2.acval envC ψ
            ((pp.nestCtx fvsP envI.find?).hiAt prog.length + iF + bs.length)
            w.getAppFn = some ha ∧
          DenoteMetaSpine mpC.base2.acval envC ψ
            ((pp.nestCtx fvsP envI.find?).hiAt prog.length + iF + bs.length)
            w.getAppArgs argsA ∧
          bs.foldl app (fs.getD iF pt) ∈ˢ
            (argsA.map (interp V (consList (fs.take iF ++ bs) σN))).foldl app
              (interp V (consList (fs.take iF ++ bs) σN) ha) ∧
          ∀ (l : Nat) (xa : AnnotTerm), argsA[off + l]? = some xa →
            (∀ xW, w.getAppArgs[off + l]? = some xW →
              xW.nestOcc (pp.nestCtx fvsP envI.find?).names
                (pp.nestCtx fvsP envI.find?).nP
                ((pp.nestCtx fvsP envI.find?).hiAt prog.length) = false) →
            (idxR.map fun xR => interp V (consList bs (consList (xs ++ fs) ρ))
              ((denoteMeta mpC.base2.acval envC ψ (R.pre.length + fvsR.length + bs.length) xR).getD
                default))[l]? = some (interp V (consList (fs.take iF ++ bs) σN) xa) := by
    intro off hargsO hoffL G ρ' hA Y hY hH
    obtain ⟨σN, hAdmN, -, hmemN⟩ := hvisit G ρ' hA Y hY hH
    obtain ⟨hparN, htailN⟩ := parTail_of_agree mpC _ ψ ρ xs hxsC hAdmN.agree
    obtain ⟨nda, hnda, hfN, hvalN⟩ := hmemN iF nd hnd
    rw [hndEq] at hnda
    obtain ⟨-, ha, argsA, hha, hspA, hyA, hidxA⟩ := fieldCall_core mpC.base2 ψ htl htel hteleHF
      hopen hwF hargsO hnPr hfvF' hfvWF hread hiF hnda hxl hflF hparN htailN hfN hvalN hbsF
    rw [← consList_append (fs.take iF) bs σN] at hyA hidxA
    refine ⟨σN, hAdmN, hparN, ha, argsA, hha, hspA, hyA, fun l xa hxa hhf => ?_⟩
    have hl : off + l < argsA.length := (List.getElem?_eq_some_iff.mp hxa).1
    have hlA : argsA.length = w.getAppArgs.length := hspA.length.symm
    obtain ⟨xW, hxW⟩ : ∃ xW, w.getAppArgs[off + l]? = some xW :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨xR, hxR⟩ : ∃ xR, idxR[l]? = some xR := hoffL l xW hxW
    rw [List.getElem?_map, hxR, Option.map_some, hidxA l xR xW xa hxR hxW hxa (hhf xW hxW)]
  -- a spine read entrywise
  have hmapI : ∀ (argsA : List AnnotTerm) (f : AnnotTerm → V) (L : List V),
      argsA.length = L.length → (∀ (l : Nat) (xa : AnnotTerm), argsA[l]? = some xa →
        L[l]? = some (f xa)) →
      argsA.map f = L := by
    intro argsA f L hlen h
    apply List.ext_getElem?
    intro l
    rw [List.getElem?_map]
    cases hx : argsA[l]? with
    | none =>
      rw [List.getElem?_eq_none (by have := List.getElem?_eq_none_iff.mp hx; omega)]; rfl
    | some xa => rw [Option.map_some, h l xa hx]
  -- a leaf whose prefix stands for the class's parameters: its arguments are the indices
  have hoff0 : pre.length = Pw.length →
      (∀ (l : Nat) (xR xW : Expr), idxR[l]? = some xR → w.getAppArgs[0 + l]? = some xW →
        Expr.ErasedEq xR (Expr.substFvars ((pp.nestCtx fvsP envI.find?).hiAt prog.length + iF)
          (R.pre.length + fvsR.length) (callSubst (pp.nestCtx fvsP envI.find?) prog fvsR) xW)) ∧
      (∀ (l : Nat) (xW : Expr), w.getAppArgs[0 + l]? = some xW → ∃ xR, idxR[l]? = some xR) ∧
      w.getAppArgs.length = idxR.length := by
    intro hpreL
    refine ⟨fun l xR xW h1 h2 => hargs l xR xW ?_ (by simpa using h2),
      fun l xW h => ⟨_, List.getElem?_eq_getElem ?_⟩, by omega⟩
    · rw [hpreL, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]; exact h1
    · have := (List.getElem?_eq_some_iff.mp h).1; omega
  rcases hcase with ⟨tm, tyv, htm, hfn, hI, hus, hal, hpre0, hhf⟩ |
    ⟨v, tyv, hk, hv0, hvl, hfn, hvk, hI, hus, hpreE', hhf, har⟩ |
    ⟨u'', nPc, L, hpre0, hu''m, hocc, hfn, hnc, hnPcL, hkey, hhf, nI, cty, hlenW, hnIW⟩
  · -- a member hole: the target lands at node `0`
    have hPlen : Pw.length = pp.nP ∧ (tgtMajor out r).member.isSome = true ∧
        pp.toBlockShape.recTgtAt r = tm := by
      have htl' : tm < pp.toBlockShape.memberNames.length := htm
      cases hmb : (tgtMajor out r).member with
      | some m' =>
        obtain ⟨hrt', -, hfi', -, hds', -⟩ := (genRec_at R hg hcal).2.2.2 m' hmb
        refine ⟨?_, rfl, ?_⟩
        · rw [← hPwLen, hds', hctxR]
          show (fvsP.take pp.nP).length = pp.nP
          rw [List.length_take, ConLeche.Verify.openPisAtFvars_length _ hop0, Nat.min_self]
        · rw [hrt']
          obtain ⟨hlt', hb', -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi'
          have e1 : pp.toBlockShape.memberNames[m']'hlt' = I := by
            rw [hIMt]; exact beq_iff_eq.mp hb'
          have e2 : pp.toBlockShape.memberNames[tm]'htl' = I := by
            rw [hI]
            show _ = pp.toBlockShape.memberNames.getD tm .anonymous
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl', Option.getD_some]
          exact (List.Nodup.getElem_inj hndM).mp (e1.trans e2.symm)
      | none =>
        exfalso
        obtain ⟨-, hnone, -⟩ := hOutR hmb
        rw [← hIMt, hI] at hnone
        have hmemN : (pp.nestCtx fvsP envI.find?).names.getD tm .anonymous
            ∈ pp.toBlockShape.memberNames := by
          show pp.toBlockShape.memberNames.getD tm .anonymous ∈ _
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem htl', Option.getD_some]
          exact List.getElem_mem htl'
        rw [List.findIdx?_eq_none_iff] at hnone
        exact absurd (hnone _ hmemN) (by simp)
    obtain ⟨hPl, hmemC, hrt⟩ := hPlen
    have hkc : (pp.nestCtx fvsP envI.find?).names.length = dR.k := by
      rw [H.hnames]; exact lfp_namesLen mpC H.hd0
    have htk : tm < dR.k := by rw [← hkc]; exact htm
    have hnIdxs : dR.nIdxs = pp.toBlockShape.nIdxs := by
      obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; rfl
    have hids : (dR.toLfp.ids tm ψ).length
        = (pp.nestCtx fvsP envI.find?).nIdxs.getD tm 0 := by
      have := blockMembers_IdsM_length hmr htk ψ
      rw [BlockData.nIdxAt, hnIdxs] at this
      exact this
    have hpreL : pre.length = Pw.length := by
      rw [hpre0, hPl]; exact H.hparF.1
    obtain ⟨hargsO, hoffL, hwl⟩ := hoff0 hpreL
    have hisl : idxR.length = (pp.nestCtx fvsP envI.find?).nIdxs.getD tm 0 := by
      rw [← hwl, hal]
    have hlt : iF < fs.length := by rw [hflF]; exact hiF
    refine ⟨0, ⟨tgtClsG_of_mem ht', Or.inl ⟨hmemC, rfl⟩⟩, fun G ρ' hA Y hY hH => ?_⟩
    obtain ⟨σN, hAdmN, -, ha, argsA, hha, hspA, hyA, hidxA⟩ :=
      hcallV 0 hargsO hoffL G ρ' hA Y hY hH
    rw [hfn] at hha
    have hLl : (pp.nestCtx fvsP envI.find?).hiAt prog.length + iF + bs.length
        = (pp.nestCtx fvsP envI.find?).hiAt prog.length
          + (fs.take iF ++ bs).length := by
      rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega
    have htmh : (pp.nestCtx fvsP envI.find?).nP + tm
        < (pp.nestCtx fvsP envI.find?).hiAt prog.length := by
      simp only [ConLeche.NestCtx.hiAt]; omega
    rw [headRead_fvar hha htmh hLl σN] at hyA
    have hmA : argsA.map (interp V (consList (List.take iF fs ++ bs) σN))
        = idxR.map fun xR => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval envC ψ (R.pre.length + fvsR.length + bs.length) xR).getD
            default) :=
      hmapI argsA _ _ (by rw [List.length_map, ← hwl, hspA.length])
        (fun l xa hxa => by
          have := hidxA l xa (by simpa using hxa)
            (fun xW hxW => hhf xW (List.mem_of_getElem? (by simpa using hxW)))
          simpa using this)
    rw [hmA] at hyA
    obtain ⟨-, hG⟩ := admVal_memberLand H hparams hxs hAdmN htm
      (by rw [List.length_map]; exact hisl) hids hyA
    have hM1 : tgtClsM mc pp.toBlockShape out r = tm := by
      simp [tgtClsM, hmemC, hrt]
    have hT1 : tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ r
        = tupW (dR.toLfp.u tm ψ) := by
      funext is; simp [tgtClsTup, tgtClsU, tgtClsD, tgtClsM, tgtClsψ, hmemC, hrt]
    rcases hG with hG | ⟨hb', -, -, hyY⟩
    · refine Or.inr (Or.inl ?_)
      rw [hM1, hT1]; exact hG
    · refine Or.inl ⟨hb', ?_⟩
      rw [hM1, hT1]; exact hyY
  · -- a frame hole (none at node `0`): the target lands at the hole's owner
    rcases hstk with rfl | ⟨u, hbpos, hub, hprog, rfl⟩
    · exact absurd hvl (by simp only [List.length_nil]; omega)
    have hlt : iF < fs.length := by rw [hflF]; exact hiF
    generalize hi : v - (pp.nestCtx fvsP envI.find?).hiAt 0 = i at hvk hpreE'
    have hv' : v = (pp.nestCtx fvsP envI.find?).hiAt 0 + i := by omega
    -- the owner, off the true visit
    obtain ⟨ho0, hol, hkm, ⟨Ys, hYs⟩, -, -⟩ := hAT.frame i hk hvk
    generalize hog : (if i < u.anc.length then holeOwner ns par b i else b) = o
      at ho0 hol hkm hYs
    have hoN : ns.getD (o - 1) default ∈ ns := getD_mem_of_lt ho0 hol
    -- the hole is a group member of its owner
    simp only [ConLeche.grpNews, List.mem_map] at hkm
    obtain ⟨p, hp, rfl⟩ := hkm
    simp only at hI hus hpreE' hhf har
    have hIo : I ∈ (ns.getD (o - 1) default).grp.map (·.1) := by
      rw [hI]; exact List.mem_map_of_mem hp
    obtain ⟨hMo', hIM⟩ := hcalOut hoN hIo
    have hPl : Pw.length = (ns.getD (o - 1) default).key.ds.length := by
      rw [← hPwLen]
      exact houtLen hoN hMo' (by rw [← hIM]; exact hIo)
    have hRo : nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find?) dR pp.toBlockShape
        out ns ψ ρ xs envC F (cvTasR.map (·.type)) r o := by
      refine ⟨tgtClsG_of_mem ht', Or.inr ⟨ho0, hol, ?_⟩⟩
      refine nodeMajor_of_pre (H.hok _ hoN) hMo' (by rw [← hIM]; exact hIo)
        hus hcmW' hYs hPl (fun q xM xP h1 h2 => hpreE q xM xP ?_ (by rw [hpreE']; exact h2))
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1]; exact h1
    obtain ⟨hMc, hTc⟩ := htupOut hRo hMo'
    have hpreL : pre.length = Pw.length := by rw [hpreE', List.length_map, hPl]
    obtain ⟨hargsO, hoffL, hwl⟩ := hoff0 hpreL
    refine ⟨o, hRo, fun G ρ' hA Y hY hH => ?_⟩
    obtain ⟨σN, hAdmN, -, ha, argsA, hha, hspA, hyA, hidxA⟩ :=
      hcallV 0 hargsO hoffL G ρ' hA Y hY hH
    rw [hfn] at hha
    have hLl : (pp.nestCtx fvsP envI.find?).hiAt prog.length + iF + bs.length
        = (pp.nestCtx fvsP envI.find?).hiAt prog.length
          + (fs.take iF ++ bs).length := by
      rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega
    rw [headRead_fvar hha hvl hLl σN, hv'] at hyA
    have hmA : argsA.map (interp V (consList (List.take iF fs ++ bs) σN))
        = idxR.map fun xR => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval envC ψ (R.pre.length + fvsR.length + bs.length) xR).getD
            default) :=
      hmapI argsA _ _ (by rw [List.length_map, ← hwl, hspA.length])
        (fun l xa hxa => by
          have := hidxA l xa (by simpa using hxa)
            (fun xW hxW => hhf xW (List.mem_of_getElem? (by simpa using hxW)))
          simpa using this)
    rw [hmA] at hyA
    obtain ⟨-, hG⟩ := admVal_frameLand H hparams hxs hAdmN hvk
      (by rw [List.length_map, ← hwl]; exact har) hyA
    simp only at hG
    rw [← hI, hIM, hog] at hG
    rcases hG with hG | ⟨hob, -, -, hyY⟩
    · refine Or.inr (Or.inl ?_)
      rw [hMc, hTc]; exact hG
    · refine Or.inl ⟨hob, ?_⟩
      rw [hMc, hTc]; exact hyY
  · -- a container instance: the target lands at a root's or a kid's node
    have hlt : iF < fs.length := by rw [hflF]; exact hiF
    obtain ⟨hu''ns, b'', hb''0, hb''l, hb''u, hdp, hown⟩ := hkidN u'' (htsi u'' hu''m) hocc
    have hok'' := H.hok u'' hu''ns
    have hcn'' : u''.key.cname = I := by rw [hkey]
    have hIo : I ∈ u''.grp.map (·.1) := hcn'' ▸ hok''.2.1
    obtain ⟨hMo', hIM⟩ := hcalOut hu''ns hIo
    have hdsK : u''.key.ds = w.getAppArgs.take nPc := by rw [hkey]
    have hdsl : u''.key.ds.length = nPc := by rw [hdsK, List.length_take]; omega
    have hPl : Pw.length = u''.key.ds.length := by
      rw [← hPwLen]
      exact houtLen hu''ns hMo' (by rw [← hIM]; exact hIo)
    have hanc'' : u''.anc = prog ∨ u''.anc = [] := by
      rcases hok''.2.2.2.2.2 with ⟨h', -⟩ | ⟨h', -⟩
      · exact Or.inl (h'.trans hocc)
      · exact Or.inr h'
    obtain ⟨X'', hX''⟩ : ∃ X, prog = X ++ u''.anc := by
      rcases hanc'' with h' | h'
      · exact ⟨[], by rw [h', List.nil_append]⟩
      · exact ⟨prog, by rw [h', List.append_nil]⟩
    have hRb : nlRel mpC.base2.acval (pp.nestCtx fvsP envI.find?) dR pp.toBlockShape
        out ns ψ ρ xs envC F (cvTasR.map (·.type)) r b'' := by
      refine ⟨tgtClsG_of_mem ht', Or.inr ⟨hb''0, hb''l, ?_⟩⟩
      rw [hb''u]
      refine nodeMajor_of_call hok'' hMo' (by rw [← hIM]; exact hIo)
        (by rw [hkey]) hcmW' (args := w.getAppArgs) hX'' (Nat.le_add_right _ iF) hPl
        (by rw [hdsl, hdsK]) (fun q xM xW h1 h2 => hargs q xM xW ?_ h2)
      rw [hpre0, List.length_nil, Nat.zero_add,
        List.getElem?_append_left (List.getElem?_eq_some_iff.mp h1).1]; exact h1
    obtain ⟨hMc, hTc⟩ := htupOut hRb hMo'
    have hargsLen' : w.getAppArgs.length = Pw.length + idxR.length := by
      have := hargsLen; rw [hpre0, List.length_nil, Nat.zero_add] at this; exact this
    obtain ⟨hDb'', hψb'', -⟩ := nlRel_tie (Dc := Dc) (mc := mc) (cvc := cvc) hcov hF hcls hsel
      hnPc hpd hfrT hcal hRb
    have hTO' := hcls _ hcal hMo'
    have hDcb : nlDb mpC dR ns b'' = Dc r := by
      rw [← hDb'']; simp [tgtClsD, hMo']
    refine ⟨b'', hRb, fun G ρ' hA Y hY hH => ?_⟩
    obtain ⟨σN, hAdmN, -, ha, argsA, hha, hspA, hyA, hidxA⟩ := hcallV Pw.length
      (fun l xR xW h1 h2 => hargs (Pw.length + l) xR xW (by
        rw [hpre0, List.length_nil, Nat.zero_add, List.getElem?_append_right (by omega),
          Nat.add_sub_cancel_left]; exact h1) h2)
      (fun l xW h => ⟨_, List.getElem?_eq_getElem (by
        have := (List.getElem?_eq_some_iff.mp h).1; omega)⟩) G ρ' hA Y hY hH
    -- the kid's admissible valuation
    obtain ⟨σK, hσK, hσKe⟩ : ∃ σK, AdmVal mk mpC (pp.nestCtx fvsP envI.find?) dR ns
        ψ ρ xs (holeOwner ns par b'')
        (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
          (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)) Y) u''.anc σK ∧
        ((u''.anc = prog ∧ σK = σN) ∨ (u''.anc = [] ∧ σK = fun q => σN (q + prog.length))) := by
      by_cases h0 : u''.anc = []
      · exact ⟨_, by rw [h0]; exact hAdmN.drop _, Or.inr ⟨h0, rfl⟩⟩
      · have h' : u''.anc = prog := hanc''.resolve_right h0
        refine ⟨σN, ?_, Or.inl ⟨h', rfl⟩⟩
        rw [h', hown h' h0]
        exact hAdmN
    have hAdm'' : nodeAdm mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs par b''
        (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
          (nlFr mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs b)) Y)
        (keyFrame (nodeDsaI mk (pp.nestCtx fvsP envI.find?) ψ u'')
          ((pp.nestCtx fvsP envI.find?).hiAt u''.anc.length) σK) := by
      unfold nodeAdm
      rw [ite_eq_right (by omega), hb''u]
      exact ⟨σK, hσK, rfl⟩
    obtain ⟨hsat'', hidx''⟩ := dyn_hAdm H ψ ρ xs hparams par b'' (by omega) _ _ hAdm''
    refine Or.inr (Or.inr ⟨hdp, by omega, _, hAdm'', ?_⟩)
    have hmN : tgtClsM mc pp.toBlockShape out r < (nlDb mpC dR ns b'').N := by
      rw [hDcb, show tgtClsM mc pp.toBlockShape out r = mc r by simp [tgtClsM, hMo']]
      exact Nat.lt_of_lt_of_le hTO'.hmm (mpC.lfpClause_of_mem hTO'.hD).kN
    rw [lfpSClause_carrier_of hidx'' hmN]
    rw [hDcb, show nlψ envC ns ψ b'' = tgtClsψ cvc out ψ r from hψb''.symm,
      show tgtClsM mc pp.toBlockShape out r = mc r by simp [tgtClsM, hMo'],
      show tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ r
        = tupW ((Dc r).u (mc r) (tgtClsψ cvc out ψ r)) by
          funext is; simp [tgtClsTup, tgtClsU, tgtClsD, tgtClsM, hMo']]
    rw [hDcb, show nlψ envC ns ψ b'' = tgtClsψ cvc out ψ r from hψb''.symm] at hsat''
    -- the head: the container's former
    rw [hfn] at hha
    obtain ⟨caps', hfI'⟩ := hTO'.hfind
    obtain ⟨-, rfl⟩ := Rules.denoteMeta_const_arityK hfI' (hIM ▸ hha)
    have hLl : (pp.nestCtx fvsP envI.find?).hiAt prog.length + iF + bs.length
        = (pp.nestCtx fvsP envI.find?).hiAt prog.length
          + (fs.take iF ++ bs).length := by
      rw [List.length_append, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]; omega
    -- the arguments: the key's parameters, then the call's indices
    have hdsW : ∀ x ∈ u''.key.ds, Expr.WScoped ((pp.nestCtx fvsP envI.find?).hiAt
        prog.length) x := fun x hx => by
      have := (hok''.2.2.2.2.1 x hx).1; rwa [hocc] at this
    rw [argsA_split mpC.base2 ψ hspA (n := nPc) hnPcL (by rw [← hdsK]; exact hdsW) hLl σN
        (by rw [List.length_map, hargsLen', hPl, hdsl]; omega)
        (fun l xa hxa => hidxA l xa (by rwa [hPl, hdsl])
          (fun xW hxW => hhf xW (List.mem_iff_getElem?.mpr ⟨l, by
            rw [List.getElem?_drop]; rw [hPl, hdsl] at hxW; exact hxW⟩))),
      ← hdsK] at hyA
    -- the key's parameters, read at the kid's valuation
    have hdsaK := dyn_dsaI H hu''ns ψ
    have hmapK : (u''.key.ds.map fun x => interp V σN ((denoteMeta mpC.base2.acval envC ψ
        ((pp.nestCtx fvsP envI.find?).hiAt prog.length) x).getD default))
        = (nodeDsaI mk (pp.nestCtx fvsP envI.find?) ψ u'').map (interp V σK) := by
      rcases hσKe with ⟨h', rfl⟩ | ⟨h', rfl⟩
      · rw [h'] at hdsaK
        have hC := DenoteMetaSpine.transport (fun e _ he => H.htr ψ _ e he) hdsaK
        rw [← DenoteMetaSpine.getD_eq hC, List.map_map]; rfl
      · rw [h'] at hdsaK
        have hle0 : (pp.nestCtx fvsP envI.find?).hiAt ([] : List NestHole).length
            ≤ (pp.nestCtx fvsP envI.find?).hiAt prog.length := by
          simp only [ConLeche.NestCtx.hiAt, List.length_nil]; omega
        have hL := DenoteMetaSpine.lift (m := mk.base2) (φ := ψ) hle0
          (fun x hx => by
            have := (posNodeOk_dsAnc hok'' x hx).1; rwa [h'] at this) hdsaK
        have hC := DenoteMetaSpine.transport (fun e _ he => H.htr ψ _ e he) hL
        have e0 : (u''.key.ds.map fun x => interp V σN ((denoteMeta mpC.base2.acval envC ψ
            ((pp.nestCtx fvsP envI.find?).hiAt prog.length) x).getD default))
            = (u''.key.ds.map fun x => (denoteMeta mpC.base2.acval envC ψ
              ((pp.nestCtx fvsP envI.find?).hiAt prog.length) x).getD default).map
                (interp V σN) := by rw [List.map_map]; rfl
        rw [e0, DenoteMetaSpine.getD_eq hC, List.map_map]
        refine List.map_congr_left fun a _ => ?_
        show interp V σN (a.liftN _ 0) = _
        rw [interp_liftN]
        congr 1
        funext q
        simp only [shiftE, Nat.not_lt_zero, ite_false, ConLeche.NestCtx.hiAt, List.length_nil]
        congr 1
        omega
    rw [hmapK] at hyA
    -- the container's clause
    obtain ⟨sI', -, hct', hdsLen', hinst'⟩ := hOutR hMo'
    have hlenP := genOutParamsLen hcov hTO' hinst' hct' hdsLen' ψ
    have hψc : tgtClsψ cvc out ψ r
        = Level.substFn ψ (cvc r).levelParams (tgtMajor out r).lvls := by
      simp [tgtClsψ, hMo']
    have hfI : frameIdx ((Dc r).params (tgtClsψ cvc out ψ r)).length
        (keyFrame (nodeDsaI mk (pp.nestCtx fvsP envI.find?) ψ u'')
          ((pp.nestCtx fvsP envI.find?).hiAt u''.anc.length) σK)
        = (nodeDsaI mk (pp.nestCtx fvsP envI.find?) ψ u'').map (interp V σK) := by
      unfold keyFrame
      refine frameIdx_consList ?_ _
      rw [List.length_map, ← DenoteMetaSpine.length_eq hdsaK, hψc, hlenP,
        houtLen hu''ns hMo' (by rw [← hIM]; exact hIo)]
    rw [← hfI] at hyA
    have his : ((idxR.map fun xR => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mpC.base2.acval envC ψ (R.pre.length + fvsR.length + bs.length) xR).getD
          default))).length
        = ((Dc r).ids (mc r) (tgtClsψ cvc out ψ r)).length := by
      rw [List.length_map, hψc, genOutIdxLen hTO' hinst' ψ hlenP]
      have hPl' : Pw.length = nPc := by rw [hPl, hdsl]
      have e1 : idxR.length = nI := by
        have := hargsLen'; rw [hlenW, hPl'] at this; omega
      rw [e1]
      obtain ⟨caps', hfC⟩ := hTO'.hfind
      refine nestInstType_count hnIW (by rw [hIM]; exact hinst')
        ⟨cvc r, caps', ?_, ?_, hTO'.tailOk⟩ ?_
      · show envI.find? I = _
        rw [hIM]
        rw [henvC] at hfC
        exact ConLeche.Semantics.consBlockCtors_find?_indInfo hfC
      · rw [ConLeche.mkFEnv_find?, hIM]; exact hfC
      · rw [List.length_take, Nat.min_eq_left hnPcL, ← hPl', hPwLen]
    have hhead : (mpC.base2.acval (tgtMajor out r).ind
        (Level.substFn ψ (cvc r).levelParams us'))
        = mpC.base2.acval ((Dc r).member (mc r))
          (tgtClsψ cvc out ψ r) := by
      rw [hTO'.hmem, hψc, ConLeche.Level.substFn_congr (ConLeche.Level.isEquivList_sound hlvW ψ)]
    simp only [ConLeche.ConstantInfo.toConstantVal] at hyA
    rw [hhead] at hyA
    exact (former_foldl_mem mpC hTO'.hD hTO'.hmm hsat'' _ his hyA).2



end ConLeche.Model
