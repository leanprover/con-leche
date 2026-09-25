module

public import ConLeche.Model.Inductives.TargetClassFrame
public import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutConv
import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetCallCarrier
import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Model.Inductives.TargetCallKey
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Subst
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.BridgeWfImp

public section

/-!
# A target call's target is a MAJOR of its callee's class (lane NESTIND, session 9, F3)

The graph kit's two `ih` rows (`hihF`, `hchain`) read, per `ih` key, the
call's target as a major of the CALLEE's recursor: the callee spine
`x⃗ ++ e⃗ ++ [f a⃗]` (the caller's prefix, the key's index readings and
the applied field) fits the callee's recursor binder data.  At a member
callee this is the member rows' argument (`tgtCall_carrierG` +
`blockRecSpineFit_of_parts`), at any caller.  At an OUTSIDE callee (a
container's auxiliary recursor): the call's typing puts the applied
field in the callee's major domain `I.{us} D⃗ ı⃗` read at the members' own
values (`targetCall_genW`, `targetAbs_read`), the container's recorded
leaf (`keyLeaf`) reads that domain as the container's carrier at the
callee's KEY frame at the index tuple, with the index values fitting the
container's index telescope there — the call's parameters `D⃗` are the
callee major's own, read at the caller's prefix openers, which the
reading does not distinguish from the callee's (`replF_erasedEq`) —
and the index converse (`tgtOutIdxConv`) and the major's reading
(`tgtOutMajor`) turn that into the callee spine's fit.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor RecShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Two syntactic facts -/

/-- **Replacing free variables by free variables at the same index is
invisible to the reading**: `replF` at such a map is erasure-equal to
the identity. -/
theorem replF_erasedEq {g : Nat → Option Expr} :
    ∀ e : Expr, (∀ l ∈ e.fvarLeaves, ∀ x, g l.1 = some x → ∃ ty, x = .fvar l.1 ty) →
      Expr.ErasedEq (replF g e) e := by
  intro e
  induction e with
  | bvar j => intro _; exact Expr.ErasedEq.rfl _
  | fvar i ty =>
    intro h
    simp only [replF]
    cases hgi : g i with
    | none => exact Expr.ErasedEq.rfl _
    | some x =>
      obtain ⟨ty', rfl⟩ := h (i, ty) (by simp [Expr.fvarLeaves]) x hgi
      show Expr.ErasedEq (.fvar i ty') (.fvar i ty)
      simp [Expr.ErasedEq]
  | sort u => intro _; exact Expr.ErasedEq.rfl _
  | const n us => intro _; exact Expr.ErasedEq.rfl _
  | lit l => intro _; exact Expr.ErasedEq.rfl _
  | app f a ihf iha =>
    intro h
    refine ⟨ihf fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      iha fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | lam t b m iht ihb =>
    intro h
    refine ⟨rfl, iht fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | forallE t b m iht ihb =>
    intro h
    refine ⟨rfl, iht fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | letE t v b iht ihv ihb =>
    intro h
    refine ⟨iht fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihv fun l hl => h l (by simp [Expr.fvarLeaves, hl]),
      ihb fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩
  | proj s i e ih =>
    intro h
    exact ⟨rfl, rfl, ih fun l hl => h l (by simp [Expr.fvarLeaves, hl])⟩

/-- Erasure equality through an application spine. -/
theorem erasedEq_mkAppN :
    ∀ {as as' : List Expr} {f f' : Expr}, Expr.ErasedEq f f' → as.length = as'.length →
      (∀ (i : Nat) (h : i < as.length) (h' : i < as'.length), Expr.ErasedEq as[i] as'[i]) →
      Expr.ErasedEq (Expr.mkAppN f as) (Expr.mkAppN f' as')
  | [], [], _, _, hf, _, _ => hf
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl
  | a :: as, a' :: as', f, f', hf, hl, h => by
    show Expr.ErasedEq (Expr.mkAppN (.app f a) as) (Expr.mkAppN (.app f' a') as')
    exact erasedEq_mkAppN ⟨hf, h 0 (by simp) (by simp)⟩ (by simpa using hl)
      (fun i h1 h2 => h (i + 1) (by simpa using h1) (by simpa using h2))

section MajDom

/-- **An OUTSIDE recursor's major domain, peeled at closed arguments**
(`tgtMajDom_open`'s twin): the recursor's type opened at its `mI` leading
binders by any bvar-closed terms is a `∀` whose domain is the major's
inductive at the major's levels, at the major's parameters with the
prefix openers replaced by the arguments, and at the arguments' index
part. -/
theorem tgtMajDom_openOut {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {outside nested : Bool}
    {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape outside nested block cvTas ctorsAs out)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[c]? = some r) (hMo : (tgtMajor out c).member = none)
    {args : List Expr} (hcl : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (hlen : args.length = pp.toBlockShape.majorIdxAt c) (hTf : r.1.type.hasFvar = false)
    (hw0 : Expr.WScoped 0 r.1.type) {res : Expr}
    (hres : Expr.instPisAtLift args r.1.type = some res) :
    (∀ x ∈ (tgtMajor out c).ds, Expr.WScoped pp.toBlockShape.nP x ∧
      x.looseBVarsBounded 0 = true ∧ ∀ l ∈ x.fvarLeaves, l.1 < pp.toBlockShape.nP) ∧
    ∃ (body : Expr) (bm : ConLeche.BinderMeta),
      res = .forallE (Expr.mkAppN (.const (tgtMajor out c).ind (tgtMajor out c).lvls)
        ((tgtMajor out c).ds.map (replF fun i => args[i]?)
          ++ args.drop (pp.toBlockShape.rulePrefixAt c))) body bm := by
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hsc := outsideDs_scoped E hMo hw0
  refine ⟨fun x hx => ⟨(hsc x hx).1, (hsc x hx).2.1, fun l hl => ((hsc x hx).2.2 l hl).1⟩, ?_⟩
  have hMI : pp.toBlockShape.majorIdxAt c = rc.mI := by
    rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hRP : pp.toBlockShape.rulePrefixAt c = rc.rP := by
    rw [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  rw [hMI] at hlen
  rw [hRP]
  obtain ⟨-, -, hfn, -, -, -, hdsE, -, -, -, -⟩ := E.outside_of hMo
  have hop := E.hopen
  obtain ⟨fvs1, fvs', o, hop1, hop2, hF⟩ := openPisAtFvars_split rc.mI (m := 1) hop
  obtain ⟨dom, body, bm, rfl, rfl⟩ : ∃ dom body bm, o = .forallE dom body bm ∧
      fvs' = [Expr.fvar rc.mI dom] := by
    match o, hop2 with
    | .forallE dom body bm, hop2 =>
      simp only [ConLeche.openPisAtFvars, Nat.zero_add] at hop2
      simp only [Option.some.injEq, Prod.mk.injEq] at hop2
      exact ⟨dom, body, bm, rfl, hop2.1.symm⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [ConLeche.openPisAtFvars] at h
  have hl1 : fvs1.length = rc.mI := ConLeche.Verify.openPisAtFvars_length _ hop1
  have hmajE : E.maj = Expr.fvar rc.mI dom := by
    have := E.hmaj
    rw [hF, List.getElem?_append_right (by omega), hl1, Nat.sub_self] at this
    exact (Option.some.inj this).symm
  have hidx := ConLeche.openPisAtFvars_index _ _ _ hop1
  have hle := E.hle
  have hfv : (E.fvs.drop rc.rP).take (rc.mI - rc.rP) = fvs1.drop rc.rP := by
    rw [hF, List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega),
      List.take_of_length_le (by simp; omega)]
  have hdom : dom = Expr.mkAppN (.const (tgtMajor out c).ind (tgtMajor out c).lvls)
      ((tgtMajor out c).ds ++ fvs1.drop rc.rP) := by
    have hd : Expr.fvarTypeD E.maj = dom := by rw [hmajE]; rfl
    rw [← hd, ← hfv, ← hfn, hdsE, ← E.hmajIdx, List.take_append_drop, Expr.mkAppN_getApp]
  -- the peel at the openers, and at the arguments
  have hins1 := ConLeche.Verify.openPisAtFvars_instPisAt _ hop1
  rw [ConLeche.instPisAtLift_eq_instPisAt hcl] at hres
  obtain ⟨⟨ds, res'⟩, hres2, rfl⟩ := Option.map_eq_some_iff.mp hres
  have hrep := instPisAt_replF (g := fun i => args[i]?)
    (fun i x hx => hcl x (List.mem_of_getElem? hx))
    fvs1 args r.1.type hins1 (by rw [hl1, hlen]) (fun j hj hj' => by
      obtain ⟨ty, hty⟩ := hidx j _ (List.getElem?_eq_getElem hj)
      rw [hty]
      simp [replF, List.getElem?_eq_getElem hj'])
  rw [replF_of_not_hasFvar _ _ hTf, hres2] at hrep
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hrep)
  have hmapF : fvs1.map (replF fun i => args[i]?) = args := by
    apply List.ext_getElem (by simp [hl1, hlen])
    intro j h1 h2
    simp only [List.getElem_map]
    obtain ⟨ty, hty⟩ := hidx j _ (List.getElem?_eq_getElem (by simpa using h1))
    rw [hty]
    simp [replF, List.getElem?_eq_getElem h2]
  refine ⟨replF (fun i => args[i]?) body, bm, ?_⟩
  rw [hdom]
  simp only [replF, replF_mkAppN, List.map_append]
  rw [List.map_drop, hmapF]

end MajDom

/-! ## The call's typing at the members' own values, at any callee -/

section MemVal

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {d : BlockData V}

set_option maxHeartbeats 8000000 in
/-- **A call's typing, read at the members' own values** (any caller,
any callee): the callee's type peeled at the call's prefix and indices
is a `∀` whose domain `majDom`, opened at the key's telescope and read
past the member holes, is graded at the valuation carrying the members'
own values `hv` at the holes and contains the applied field — the call's
typing (`targetCall_genW`) with the abstraction read back at the
members' values (`targetAbs_read`). -/
theorem tgtCall_memVal (hμ : μ.verifiedChecks = true)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat}
    {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    {rc : ConLeche.RecShape} {M : TargetMajor} {cA : ConstantVal × Nat} {rhs0 rhs : Expr}
    (Q : ConLeche.TargetRuleRun μ F
      (ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) (mkFEnv envC)) (mkFEnv envC) pp.toBlockShape
      (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r0.1 rc.rP r0.1.type M cA rhs0 rhs)
    (hrP : rc.rP = pp.toBlockShape.rulePrefixAt c)
    (hdsOk : TgtDsOk envC rc.rP Q.fvsPref M.ds)
    (hCf : (ConLeche.targetCtorAt M cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M cA.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound envC (ConLeche.targetCtorAt M cA.1))
    (hbf : Q.body.hasFvar = false)
    (hTf : r0.1.type.hasFvar = false) (hTb : r0.1.type.looseBVarsBounded 0 = true)
    (hTc : ConstsBound envC r0.1.type)
    (hle : ∀ c', (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD c' 0
      ≤ (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD c' 0)
    (hRT3 : ∀ c',
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).hasFvar = false ∧
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
        = true ∧
      ConstsBound envC ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)))
    (hB : tgtB pp.toBlockShape out c j = rc.rP + cA.2)
    (hFrEq : tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)))
    (hAbs : (Q.bodyO, Q.ihs)
      = tgtAbs μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j)
    {pd fd : List AnnotTerm} (hpl : pd.length = rc.rP) (hfl : fd.length = cA.2)
    (hF : ∀ (l : Nat) (x : Expr), Q.fvsF[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (rc.rP + l) x.fvarTypeD = some (fd.getD l default))
    {xs fs : List V} (hsp : SpineFit ρ (pd ++ fd) (xs ++ fs)) {Δ : List AnnotTerm}
    (hW : WalkCtx V mpC.base2 ψ (rc.rP + cA.2) (consList (xs ++ fs) ρ) Δ
      (Q.fvsPref ++ Q.fvsF).reverse)
    (hxs : xs.length = pp.toBlockShape.rulePrefixAt c)
    {hv : List V} (hvl : hv.length = cvTas.length)
    (hvget : ∀ t, t < cvTas.length →
      hv.getD t pt = interp V ρ (mpC.base2.acval (d.memberName t) ψ))
    {r : Nat}
    (hr : r < (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
        c j r).map (·.2.2)) bs) :
    ∃ (majDom majBody : Expr) (majBm : ConLeche.BinderMeta),
      Expr.instPisAtLift (Q.fvsPref
          ++ ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
            default).idx)
        ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD
          ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
            default).callee (.sort .zero))
        = some (.forallE majDom majBody majBm) ∧
      ∃ (os' : List Expr) (X1 : AnnotTerm),
        LocList (rc.rP + cA.2 + (cvTas.map (·.type)).length) bs.length os' ∧
        denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + (cvTas.map (·.type)).length + bs.length)
          (majDom.instantiateList os' 0) = some X1 ∧
        (∀ x ∈ ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
            default).idx, x.looseBVarsBounded bs.length = true ∧
          ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF) ∧
        ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
            default).idx.length + rc.rP
          = (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD
            ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
              default).callee 0 ∧
        (tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
            ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))
          = ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
            default).idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
              ((denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + bs.length)
                (x.instantiateList (locOpen (rc.rP + cA.2) bs.length) 0)).getD default)) ∧
        WellDenoted V (consList bs (consList hv (consList (xs ++ fs) ρ))) X1 ∧
        interp V (consList bs (consList (xs ++ fs) ρ))
            (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
              envC ψ c j r)
          ∈ˢ interp V (consList bs (consList hv (consList (xs ++ fs) ρ))) X1 := by
  have hver : μ = .verified := CheckMode.eq_verified hμ
  -- the entry
  have hIhL : tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j
      = Q.ihs.toList := by
    rw [tgtIhL, ← hAbs]
  generalize hih : (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
    default = ih at *
  have hrl : r < Q.ihs.toList.length := by rw [← hIhL]; exact hr
  have hihMem : ih ∈ Q.ihs.toList := by
    rw [← hih, hIhL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hrl, Option.getD_some]
    exact List.getElem_mem hrl
  obtain ⟨C⟩ := Q.call hihMem
  -- the frame
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf hCb hCc
  have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hlf : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
  have hxl : xs.length = rc.rP := by rw [hxs, hrP]
  have hfsl : fs.length = cA.2 := by
    have hsl := hsp.length_eq
    simp only [List.length_append, hpl, hfl] at hsl
    omega
  have hformerF : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
    exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1
  -- the called field is a field of the constructor
  have hfi : ih.field < cA.2 := by
    refine Nat.lt_of_not_le fun hge => ?_
    have hg : Q.fvsF.getD ih.field default = .bvar 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    have h0 := C.hfld
    rw [hg] at h0
    exact inferTypeCore_bvar_absurd' h0
  -- the field's abstract telescope through whnf
  obtain ⟨-, hallN⟩ := ConLeche.targetFieldNorms_run Q.hfnorm
  obtain ⟨t0, ht0, hrun0⟩ := hallN ih.field _ (List.getElem?_eq_getElem (by omega))
  have hfnorm : ConLeche.targetWhnfPis (ConLeche.fueledOps μ F) envC
      (rc.rP + cA.2 + (cvTas.map (·.type)).length)
      (ConLeche.whnfWalkFuel
        (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
          (ConLeche.targetHoles (cvTas.map (·.type)) (rc.rP + cA.2))
          (Q.fvsF.getD ih.field default).fvarTypeD))
      (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
        (ConLeche.targetHoles (cvTas.map (·.type)) (rc.rP + cA.2))
        (Q.fvsF.getD ih.field default).fvarTypeD) = .ok (Q.fnorm.getD ih.field default) := by
    have e1 : Q.fnorm.getD ih.field default = t0 := by
      rw [List.getD_eq_getElem?_getD, ht0]; rfl
    have e2 : Q.fvsF.getD ih.field default = Q.fvsF[ih.field]'(by omega) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [e1, e2]
    exact hrun0
  -- the telescope's and the index arguments' leaves
  have hscope := targetIh_scope hμ Q mpC.base2.wf hle hbf hFr hher hcbF hformerF
    (fun c' => (hRT3 c').1) hihMem
  have htL := hscope.2.2.2.2.2
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
  obtain ⟨hidxLen, -, hidxB⟩ : ih.idx.length + rc.rP
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
  -- the holes at the members' own values
  have hkN := hN.2.2
  have hvTy : ∀ t, t < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 (cvTas.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T := by
    intro t ht
    obtain ⟨cv, hcv⟩ : ∃ cv, cvTas[t]? = some cv := ⟨_, List.getElem?_eq_getElem ht⟩
    obtain ⟨hname, -, ⟨caps, hfind⟩, -, -, hFD⟩ := hmr.2.2.2.1 t cv hcv
    have hgc : cvTas.getD t default = cv := by rw [List.getD_eq_getElem?_getD, hcv]; rfl
    rw [hgc, hvget t ht]
    refine ⟨_, hFD.read ψ, ?_⟩
    have hm := mpC.mem_type (.indInfo cv caps) (List.mem_of_find?_eq_some hfind) ψ _
      (hFD.read ψ) ρ
    rw [hname]
    exact hm
  have hnames : ∀ (n : Name) (t : Nat),
      pp.toBlockShape.memberNames.findIdx? (· == n) = some t →
      t < (cvTas.map (·.type)).length ∧ ∃ ci : ConstantInfo, envC.find? n = some ci ∧
        (pp.toBlockShape.lps.map Level.param).length = ci.toConstantVal.levelParams.length ∧
        ∀ σ : Nat → V, interp V σ (mpC.base2.acval n
          (Level.substFn ψ ci.toConstantVal.levelParams (pp.toBlockShape.lps.map Level.param)))
          = hv.getD t pt := by
    intro n t hft
    obtain ⟨htl, hbeq, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hft
    have hmn : pp.toBlockShape.memberNames[t] = n := by simpa using hbeq
    have htl' : t < pp.toBlockShape.members.length := by
      simpa [ConLeche.BlockShape.memberNames] using htl
    have htc : t < cvTas.length := by rw [hkN, hmr.2.1]; exact htl'
    obtain ⟨cv, hcv⟩ : ∃ cv, cvTas[t]? = some cv := ⟨_, List.getElem?_eq_getElem htc⟩
    obtain ⟨hname, hlps, ⟨caps, hfind⟩, -, -, -⟩ := hmr.2.2.2.1 t cv hcv
    obtain ⟨hnameMs, -⟩ := hmr.2.2.2.2.1 t _ (List.getElem?_eq_getElem htl')
    have hn : n = cv.name := by
      rw [← hmn, ← hname, hnameMs]
      simp [ConLeche.BlockShape.memberNames]
    subst hn
    refine ⟨by simpa using htc, .indInfo cv caps, hfind,
      by show _ = cv.levelParams.length; rw [hlps]; simp, fun σ => ?_⟩
    show interp V σ (mpC.base2.acval cv.name (Level.substFn ψ cv.levelParams
      (pp.toBlockShape.lps.map Level.param))) = _
    rw [hlps, Level.substFn_param_self, ← hname, hvget t htc]
    exact acval_interp_closed mpC.base2 _ ψ σ ρ
  -- the called field lies in its member-abstracted type's reading
  have hFF : tgtFieldFvs pp.toBlockShape out c j = Q.fvsF := congrArg (·.fields) hFrEq
  have hiiG : ∀ Aty : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + (cvTas.map (fun cv : ConstantVal => cv.type)).length)
        (ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
          (ConLeche.targetHoles (cvTas.map (fun cv : ConstantVal => cv.type)) (rc.rP + cA.2))
          (Q.fvsF.getD ih.field default).fvarTypeD) = some Aty →
      fs.getD ih.field pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) Aty := by
    intro Aty hA
    obtain ⟨fi, hfi'⟩ : ∃ fi, ih.field = fi := ⟨_, rfl⟩
    rw [hfi'] at hA hfi ⊢
    -- the field variable and its concrete type
    have hlt : rc.rP + fi < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hFr.reverse_idx (rc.rP + fi) _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    have hfvi : Q.fvsF.getD fi default = Expr.fvar (rc.rP + fi) ty := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [List.getElem_append_right (by omega)] at hty
      simpa [hlp] using hty
    have hwty : Expr.WScoped (rc.rP + fi) ty := by
      have := hFr.2.2 _ (List.mem_reverse.mpr (List.getElem_mem hlt))
      rw [hty] at this
      unfold Expr.WScoped at this
      exact this.2
    have hleaves : ∀ l ∈ ty.fvarLeaves, l.1 < rc.rP + fi :=
      fun l hl => ConLeche.Expr.fvarLeaves_lt_of_wscoped hwty l hl
    rw [hfvi] at hA
    have hAty : denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + (cvTas.map (·.type)).length + 0)
        ((ConLeche.targetAbs pp.toBlockShape.memberNames (pp.toBlockShape.lps.map .param)
          (ConLeche.targetHoles (cvTas.map (·.type)) (rc.rP + cA.2)) ty).instantiateList [] 0)
        = some Aty := by
      rw [ConLeche.Expr.instantiateList_nil, Nat.add_zero]; exact hA
    have hdF : denoteMeta mpC.base2.acval envC ψ (rc.rP + fi) ty = some (fd.getD fi default) := by
      have h1 := hF fi (Expr.fvar (rc.rP + fi) ty)
        (by
          have := hfvi
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
          rw [List.getElem?_eq_getElem (by omega)]
          exact congrArg some this)
      exact h1
    have hd := denoteMeta_open_deepen (acval := mpC.base2.acval) (env := envC) (φ := ψ)
      (fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m)
      (cA.2 - fi + cvTas.length) (rc.rP + fi) ty 0 [] [] hleaves (LocList.nil _) (LocList.nil _)
    simp only [ConLeche.Expr.instantiateList_nil, Nat.add_zero, hdF, Option.map_some] at hd
    have hSr := targetAbs_read (m := mpC.base2) (env := envC) (φ := ψ)
      (names := pp.toBlockShape.memberNames) (lvls := pp.toBlockShape.lps.map .param)
      (formerTys := cvTas.map (·.type)) (B := rc.rP + cA.2) (hvC := fun t => hv.getD t pt) hnames
      ty 0 [] [] (LocList.nil _) (LocList.nil _)
    rw [hAty, ConLeche.Expr.instantiateList_nil,
      show rc.rP + cA.2 + (cvTas.map (·.type)).length + 0
        = rc.rP + fi + (cA.2 - fi + cvTas.length) from by rw [List.length_map]; omega, hd] at hSr
    obtain ⟨hval, -⟩ := hSr [] (consList hv (consList (xs ++ fs) ρ)) rfl (fun t ht => by
      rw [List.length_map] at ht ⊢
      rw [consList_getD_of_lt _ _ _ (by rw [hvl]; omega), hvl,
        show cvTas.length - 1 - (cvTas.length - 1 - t) = t from by omega])
    rw [consList_nil] at hval
    rw [hval, interp_liftN]
    have hsh : shiftE (cA.2 - fi + cvTas.length) 0 (consList hv (consList (xs ++ fs) ρ))
        = consList ((xs ++ fs).take (rc.rP + fi)) ρ := by
      have hsplit : consList hv (consList (xs ++ fs) ρ)
          = consList ((xs ++ fs).drop (rc.rP + fi) ++ hv)
              (consList ((xs ++ fs).take (rc.rP + fi)) ρ) := by
        rw [← consList_append ((xs ++ fs).take (rc.rP + fi)), ← List.append_assoc,
          List.take_append_drop, consList_append (xs ++ fs) hv ρ]
      rw [hsplit, show cA.2 - fi + cvTas.length
        = ((xs ++ fs).drop (rc.rP + fi) ++ hv).length from by
          simp [hvl, hxl, hfsl]; omega, shiftE_consList]
    rw [hsh]
    have hmemF := FixKI.spineFit_getD_mem' hsp (l := rc.rP + fi) (by simp [hpl, hfl]; omega)
    have e1 : (pd ++ fd).getD (rc.rP + fi) default = fd.getD fi default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hpl,
        show rc.rP + fi - rc.rP = fi from by omega, ← List.getD_eq_getElem?_getD]
    have e2 : (xs ++ fs).getD (rc.rP + fi) pt = fs.getD fi pt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hxl,
        show rc.rP + fi - rc.rP = fi from by omega, ← List.getD_eq_getElem?_getD]
    rw [e1, e2] at hmemF
    exact hmemF
  -- the holes' values at their formers' types
  have hformerG : ∀ t', t' < (cvTas.map (fun cv : ConstantVal => cv.type)).length →
      ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default).hasFvar = false ∧
      ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default).looseBVarsBounded 0 = true ∧
      ConstsBound envC ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default) ∧
      ∃ T : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0 ((cvTas.map (fun cv : ConstantVal => cv.type)).getD t' default)
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
  have hTel : (tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type)) out c j).teles
      = Q.fnorm.map fun t => t.piBinders.1 := congrArg (·.teles) hFrEq
  have hbs' : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mpC.base2.acval envC ψ (rc.rP + cA.2) []
        (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1))).getD []) bs := by
    have := hbs
    simp only [tgtTlA, tgtTeleTys] at this
    rw [hih, hTel, hB, List.map_map] at this
    simpa [Function.comp_def] using this
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  obtain ⟨os', Xr, hos', hXr, hbl, hwdX, hfoldX⟩ := targetCall_genW hμ hacl
    (Rules.RulesInputs.ofSem mpC ψ) C hfnorm hlf hFr hxl hfsl hW hfi htL hidxL
    (by rw [hvl, List.length_map]) hformerG hiiG ((hRT3 ih.callee).1) bs hbs'
  -- the abstraction read back at the members' values
  rw [← hbl] at hos' hXr hidxB
  have hSr := targetAbs_read (m := mpC.base2) (env := envC) (φ := ψ)
    (names := pp.toBlockShape.memberNames) (lvls := pp.toBlockShape.lps.map .param)
    (formerTys := cvTas.map (·.type)) (B := rc.rP + cA.2) (hvC := fun t => hv.getD t pt) hnames
    C.majDom bs.length os' os' hos' hos'
  rw [hXr] at hSr
  cases hX1 : denoteMeta mpC.base2.acval envC ψ
      (rc.rP + cA.2 + (cvTas.map (·.type)).length + bs.length)
      (C.majDom.instantiateList os' 0) with
  | none => rw [hX1] at hSr; exact nomatch hSr
  | some X1 =>
    rw [hX1] at hSr
    obtain ⟨hval, hwdT⟩ := hSr bs (consList hv (consList (xs ++ fs) ρ)) rfl (fun t ht => by
      rw [List.length_map] at ht ⊢
      rw [consList_getD_of_lt _ _ _ (by rw [hvl]; omega), hvl,
        show cvTas.length - 1 - (cvTas.length - 1 - t) = t from by omega])
    -- the applied field's value
    have hfvF : ∃ ty, Q.fvsF.getD ih.field default = Expr.fvar (rc.rP + ih.field) ty := by
      have hlt : rc.rP + ih.field < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
      obtain ⟨ty, hty⟩ := hFr.reverse_idx (rc.rP + ih.field) _
        (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
      refine ⟨ty, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      rw [List.getElem_append_right (by omega)] at hty
      simpa [hlp] using hty
    obtain ⟨fty0, hfty0⟩ := hfvF
    have hlenS : (xs ++ fs).length = rc.rP + cA.2 := by rw [List.length_append, hxl, hfsl]
    have hFF' : (tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
        out c j).fields = Q.fvsF := congrArg (·.fields) hFrEq
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
    refine ⟨C.majDom, C.majBody, C.majBm, by rw [← C.hmajDom]; exact C.hcallee, os', X1, hos', hX1,
      fun x hx => ⟨hidxB x hx, hidxL x hx⟩, hidxLen, hEis, hwdT hwdX, ?_⟩
    rw [hfap, ← hval]
    exact hfoldX

set_option maxHeartbeats 8000000 in
/-- **F3 at an OUTSIDE callee**: at any caller's frame, a call whose
callee's major is an outside container (`TgtOutCls`) targets a major of
the callee's class — the callee spine (the caller's prefix, the key's
index readings, the applied field) fits the callee recursor's binder
data.  The call's typing at the members' own values (`tgtCall_memVal`)
puts the applied field in the callee's major domain, which is the
container `I.{us}` at the callee major's own parameters (read at the
caller's openers, erasure-equal, `replF_erasedEq`) and the call's
indices; the container's leaf (`keyLeafW`) reads that at the callee's
key frame; the index converse and the major's reading at the callee
(`tgtOutIdxConv`, `tgtOutMajor`) give the fit. -/
theorem tgtCall_outSpine (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {outside nested : Bool} {block : List ConstantInfo}
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat}
    {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr0 : (tgtRs out)[c]? = some r0)
    {rc : ConLeche.RecShape} {M : TargetMajor} {cA : ConstantVal × Nat} {rhs0 rhs : Expr}
    (Q : ConLeche.TargetRuleRun μ F
      (ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) (mkFEnv envC)) (mkFEnv envC) pp.toBlockShape
      (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r0.1 rc.rP r0.1.type M cA rhs0 rhs)
    (hrP : rc.rP = pp.toBlockShape.rulePrefixAt c)
    (hnP : pp.toBlockShape.nP ≤ rc.rP)
    (hdsOk : TgtDsOk envC rc.rP Q.fvsPref M.ds)
    (hCf : (ConLeche.targetCtorAt M cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M cA.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound envC (ConLeche.targetCtorAt M cA.1))
    (hbf : Q.body.hasFvar = false)
    (hTf : r0.1.type.hasFvar = false) (hTb : r0.1.type.looseBVarsBounded 0 = true)
    (hTc : ConstsBound envC r0.1.type)
    (hle : ∀ c', (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD c' 0
      ≤ (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD c' 0)
    (hRT3 : ∀ c',
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).hasFvar = false ∧
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
        = true ∧
      ConstsBound envC ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)))
    (hB : tgtB pp.toBlockShape out c j = rc.rP + cA.2)
    (hFrEq : tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)))
    (hAbs : (Q.bodyO, Q.ihs)
      = tgtAbs μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j)
    {fd : List AnnotTerm} (hfl : fd.length = cA.2)
    (hF : ∀ (l : Nat) (x : Expr), Q.fvsF[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (rc.rP + l) x.fvarTypeD = some (fd.getD l default))
    {xs fs : List V}
    (hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c ++ fd)
      (xs ++ fs)) {Δ : List AnnotTerm}
    (hW : WalkCtx V mpC.base2 ψ (rc.rP + cA.2) (consList (xs ++ fs) ρ) Δ
      (Q.fvsPref ++ Q.fvsF).reverse)
    (hxs : xs.length = pp.toBlockShape.rulePrefixAt c)
    {r : Nat}
    (hr : r < (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length)
    {r1 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr1 : (tgtRs out)[((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c
      j).getD r default).callee]? = some r1)
    (hrPc : pp.toBlockShape.rulePrefixAt ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape
      (cvTas.map (·.type)) out c j).getD r default).callee = pp.toBlockShape.rulePrefixAt c)
    (hMo1 : (tgtMajor out ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c
      j).getD r default).callee).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl1 : TgtOutCls mpC (tgtMajor out ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape
      (cvTas.map (·.type)) out c j).getD r default).callee) D mm cvI)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
        c j r).map (·.2.2)) bs) :
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ
        ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).callee).map (·.2.2))
      (xs ++ ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          envC ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))
        ++ [interp V (consList bs (consList (xs ++ fs) ρ))
          (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ c j r)])) := by
  have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr0 ψ, hrP]
  -- the members' own values at the holes
  let hv : List V := (List.range cvTas.length).map fun t =>
    interp V ρ (mpC.base2.acval (d.memberName t) ψ)
  have hvl : hv.length = cvTas.length := by simp [hv]
  have hvget : ∀ t, t < cvTas.length →
      hv.getD t pt = interp V ρ (mpC.base2.acval (d.memberName t) ψ) := by
    intro t ht; simp [hv, List.getD_eq_getElem?_getD, List.getElem?_range ht]
  obtain ⟨majDom, majBody, majBm, hcallee, os', X1, hos', hX1, hidxF, hidxLen, hEis, hwd1,
    hmem1⟩ := tgtCall_memVal hμ hN hmr ψ ρ Q hrP hdsOk hCf hCb hCc hbf hTf hTb hTc hle hRT3 hB
      hFrEq hAbs hpl hfl hF hsp hW hxs hvl hvget hr bs hbs
  -- names
  generalize hEisV : (tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
    mpC.base2.acval envC ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ))) = eis
    at hEis ⊢
  generalize hFapV : interp V (consList bs (consList (xs ++ fs) ρ))
    (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
      c j r) = fapv at hmem1 ⊢
  generalize hih : (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
    default = ih at *
  generalize hcq : ih.callee = cq at *
  -- the frame
  obtain ⟨hFr, -, -, -⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf hCb hCc
  have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
  have hxl : xs.length = rc.rP := by rw [hxs, hrP]
  have hprefI := ConLeche.openPisAtFvars_index _ _ _ Q.hpref
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  -- the callee's family data
  obtain ⟨-, hlenR, -⟩ := recStageG_recNames h
  have hcal : cq < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr1).1
  have hcalR : cq < pp.recs.length := by omega
  have hmIc : (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD cq 0
      = pp.toBlockShape.majorIdxAt cq := by
    simp only [tgtFam, ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_getElem hcalR]; rfl
  have hrecTy : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD cq (.sort .zero)
      = r1.1.type := by
    simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr1]; rfl
  obtain ⟨hTf1, -, -, -, -⟩ := ConLeche.recStage_facts h r1 (List.mem_of_getElem? hr1)
  obtain ⟨hw01, -⟩ := recStage_tyClosed h hr1
  -- the callee's type peeled at the opened call arguments
  have hall := hos'.allFvars
  have hoscl : ∀ o ∈ os', o.looseBVarsBounded 0 = true := by
    intro o ho; obtain ⟨i, ty, rfl⟩ := hall o ho; rfl
  have hprefF : ∀ x ∈ Q.fvsPref, ∃ i ty, x = Expr.fvar i ty := fun x hx =>
    hFr.mem_fvar (List.mem_reverse.mpr (List.mem_append_left _ hx))
  have hargsB : ∀ a ∈ Q.fvsPref ++ ih.idx, a.looseBVarsBounded os'.length = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i, ty, rfl⟩ := hprefF a ha; rfl
    · rw [hos'.1]; exact (hidxF a ha).1
  have hins := instPisAtLift_instantiateList hoscl (Q.fvsPref ++ ih.idx) hargsB
    (hRT3 cq).2.1 hcallee
  rw [hrecTy] at hins
  simp only [Expr.instantiateList] at hins
  have hclA : ∀ a ∈ (Q.fvsPref ++ ih.idx).map (·.instantiateList os' 0),
      a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact looseBVarsBounded_instantiateList_allFvars hall b 0 (by simpa using hargsB b hb)
  have hlenA : ((Q.fvsPref ++ ih.idx).map (·.instantiateList os' 0)).length
      = pp.toBlockShape.majorIdxAt cq := by
    rw [List.length_map, List.length_append, hlp, ← hmIc]; omega
  obtain ⟨hdsS, body', bm', heq⟩ := tgtMajDom_openOut R hr1 hMo1 hclA hlenA hTf1 hw01 hins
  injection heq with hdom
  have hdropA : ((Q.fvsPref ++ ih.idx).map (·.instantiateList os' 0)).drop
      (pp.toBlockShape.rulePrefixAt cq) = ih.idx.map (·.instantiateList os' 0) := by
    rw [hrPc, ← hrP, List.map_append, List.drop_append_of_le_length (by simp [hlp]),
      List.drop_eq_nil_of_le (by simp [hlp]), List.nil_append]
  rw [hdropA] at hdom
  -- the call's parameters are the callee major's own, up to the openers' annotations
  have herased : Expr.ErasedEq
      (Expr.mkAppN (.const (tgtMajor out cq).ind (tgtMajor out cq).lvls)
        ((tgtMajor out cq).ds.map (replF fun i =>
            ((Q.fvsPref ++ ih.idx).map (·.instantiateList os' 0))[i]?)
          ++ ih.idx.map (·.instantiateList os' 0)))
      (Expr.mkAppN (.const (tgtMajor out cq).ind (tgtMajor out cq).lvls)
        ((tgtMajor out cq).ds ++ ih.idx.map (·.instantiateList os' 0))) := by
    refine erasedEq_mkAppN (Expr.ErasedEq.rfl _) (by simp) fun i h1 h2 => ?_
    rcases Nat.lt_or_ge i (tgtMajor out cq).ds.length with hi | hi
    · rw [List.getElem_append_left (by simpa using hi), List.getElem_append_left hi,
        List.getElem_map]
      refine replF_erasedEq _ fun l hl y hy => ?_
      have hlt : l.1 < pp.toBlockShape.nP := (hdsS _ (List.getElem_mem hi)).2.2 l hl
      rw [List.getElem?_map, List.getElem?_append_left (by omega)] at hy
      obtain ⟨ty, hty⟩ := hprefI l.1 (Q.fvsPref[l.1]'(by omega))
        (List.getElem?_eq_getElem (by omega))
      rw [List.getElem?_eq_getElem (by omega), Option.map_some, hty] at hy
      obtain rfl := Option.some.inj hy
      exact ⟨ty, by simp [Expr.instantiateList]⟩
    · rw [List.getElem_append_right (by simpa using hi), List.getElem_append_right hi]
      simp only [List.length_map]
      exact Expr.ErasedEq.rfl _
  have hwa : denoteMeta mpC.base2.acval envC ψ
      (rc.rP + cA.2 + (cvTas.map (·.type)).length + bs.length)
      (Expr.mkAppN (.const (D.member mm) (tgtMajor out cq).lvls)
        ((tgtMajor out cq).ds ++ ih.idx.map (·.instantiateList os' 0))) = some X1 := by
    rw [hcl1.hmem, ← denoteMeta_erasedEq herased, ← hdom]
    exact hX1
  -- the callee's reading of its major's parameters
  obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSatW hμ mpC hcov h R hr1 hMo1 hcl1 ψ
  have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ cq :=
    denoteMetaSpine_eq_map hdsa
  subst hdsaE
  have hlenI0 := tgtOutIdx_len R hr1 hMo1 hcl1 ψ hlenP
  obtain ⟨rc1, u1, hrc1, ⟨E1⟩⟩ := targetEntryAt R hr1
  have hRP1 : tgtRP pp.toBlockShape cq = rc.rP := by
    rw [tgtRP_eq, hrPc, hrP]
  have hMI1 : pp.toBlockShape.majorIdxAt cq = rc.rP + (tgtMajor out cq).nIdx := by
    have h1 : pp.toBlockShape.majorIdxAt cq = rc1.mI := by
      rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc1, Option.getD_some]
    have h2 : pp.toBlockShape.rulePrefixAt cq = rc1.rP := by
      rw [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc1, Option.getD_some]
    rw [h1, E1.hmI, ← h2, hrPc, hrP]
  have hidxL : ih.idx.length = (tgtMajor out cq).nIdx := by
    rw [hmIc, hMI1] at hidxLen; omega
  obtain ⟨caps, hfI⟩ := hcl1.hfind
  have hf : envC.find? (D.member mm) = some (.indInfo cvI caps) := by rw [hcl1.hmem]; exact hfI
  obtain ⟨-, isa, hisa, hleaf⟩ := keyLeafW mpC hcl1.hD hcl1.hmm hf
    (b := tgtRP pp.toBlockShape cq) (by rw [hRP1]; omega) hwa hlenP.symm
    (by rw [List.length_map, hlenI0, hidxL]) (fun x hx => (hds x hx).1) hdsa
  obtain ⟨-, hfitK, hvalK⟩ := hleaf _ hwd1
  -- the key frame's valuation is the prefix's
  have hdrop : dropV (rc.rP + cA.2 + (cvTas.map (·.type)).length + bs.length
        - tgtRP pp.toBlockShape cq) (consList bs (consList hv (consList (xs ++ fs) ρ)))
      = consList xs ρ := by
    have hfsl : fs.length = cA.2 := by
      have hsl := hsp.length_eq
      simp only [List.length_append, hpl, hfl] at hsl
      omega
    funext k
    rw [dropV, hRP1, ← consList_append, ← consList_append, List.append_assoc,
      consList_append xs (fs ++ (hv ++ bs)),
      show rc.rP + cA.2 + (cvTas.map (·.type)).length + bs.length - rc.rP
        = (fs ++ (hv ++ bs)).length from by simp [hvl, hfsl]; omega, consList_apply_add]
  -- the index readings are the key's
  have hisaV : isa.map (interp V (consList bs (consList hv (consList (xs ++ fs) ρ)))) = eis := by
    rw [spine_map_getD (mT := mpC.base2) hisa, hEis, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    have hxL : ∀ l ∈ x.fvarLeaves, l.1 < rc.rP + cA.2 :=
      leaf_lt_of_mem hFr (fun l hl => List.mem_reverse.mpr ((hidxF x hx).2 l hl))
    have hd := denoteMeta_open_deepen (acval := mpC.base2.acval) (env := envC) (φ := ψ) hacl
      (cvTas.map (·.type)).length (rc.rP + cA.2) x bs.length
      (locOpen (rc.rP + cA.2) bs.length) os' hxL (locOpen_locList _ _) hos'
    simp only [Function.comp]
    rw [hd]
    cases hA0 : denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + bs.length)
        (x.instantiateList (locOpen (rc.rP + cA.2) bs.length) 0) with
    | none =>
      exfalso
      obtain ⟨v1, hv1⟩ := spine_reads (mT := mpC.base2) hisa _
        (List.mem_map_of_mem (f := (·.instantiateList os' 0)) hx)
      rw [hd, hA0] at hv1
      exact nomatch hv1
    | some A0 =>
      simp only [Option.map_some, Option.getD_some]
      rw [interp_liftN, shiftE_consList_ih rfl (by rw [hvl, List.length_map])]
  rw [hdrop, hisaV] at hfitK hvalK
  -- the callee's side: its prefix, indices and major
  obtain ⟨xs₁, fs₁, hxfs, hpre, -⟩ := spineFit_append_split hsp
  have hx₁ : xs₁ = xs := by
    have hl : xs₁.length = xs.length := by rw [hpre.length_eq, hpl, hxl]
    exact (List.append_inj hxfs.symm hl).1
  subst hx₁
  have hpref1 := blockRecHpref_run hμ mpC h ψ hr0 hr1 hpre
  have hIdxFit := tgtOutIdxConv hμ hcov h R hr1 hMo1 hcl1 ψ ρ xs₁ eis hpref1 hfitK
  have hMaj := tgtOutMajor hμ hcov h R hr1 hMo1 hcl1 ψ ρ xs₁ eis hpref1 hIdxFit
  obtain ⟨-, -, -, -, -, hlenRds, -, -, -, -⟩ := recStage_tyPis (V := V) hμ mpC h hr1 ψ
  have hLlen : ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ cq).map
      (·.2.2)).length = tgtRP pp.toBlockShape cq + (tgtMajor out cq).nIdx + 1 := by
    rw [List.length_map, hlenRds, hRP1, hMI1]
  rw [rds_split3 hLlen, List.append_assoc]
  have hPd : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ cq
      = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ cq).map
          (·.2.2)).take (tgtRP pp.toBlockShape cq) := by
    rw [blockRulePdomsAV, List.map_take, tgtRP_eq]
  rw [hPd] at hpref1
  refine SpineFit.append hpref1 (SpineFit.append hIdxFit ⟨?_, trivial⟩)
  rw [← consList_append, show tgtRP pp.toBlockShape cq + (tgtMajor out cq).nIdx
    = pp.toBlockShape.majorIdxAt cq from by rw [hRP1, hMI1], hMaj, ← hvalK]
  exact hmem1

/-- **F3 at a MEMBER callee, at any caller**: the member rows' argument
(`tgtCall_carrierG`: the index readings fit the callee member's index
telescope at the parameters and the applied field lies in the member at
them; `blockRecSpineFit_of_parts`) at the caller's frame facts. -/
theorem tgtCall_memSpine (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hnd : d.memberNames.Nodup)
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat}
    {r0 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr0 : (tgtRs out)[c]? = some r0)
    {rc : ConLeche.RecShape} {M : TargetMajor} {cA : ConstantVal × Nat} {rhs0 rhs : Expr}
    (Q : ConLeche.TargetRuleRun μ F
      (ConLeche.consBlockRecsBareF pp.toBlockShape 0
        ((tgtRs out).map fun r => (r.1, r.2.2.1)) (mkFEnv envC)) (mkFEnv envC) pp.toBlockShape
      (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r0.1 rc.rP r0.1.type M cA rhs0 rhs)
    (hrP : rc.rP = pp.toBlockShape.rulePrefixAt c)
    (hnP : pp.toBlockShape.nP ≤ rc.rP)
    (hdsOk : TgtDsOk envC rc.rP Q.fvsPref M.ds)
    (hCf : (ConLeche.targetCtorAt M cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M cA.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound envC (ConLeche.targetCtorAt M cA.1))
    (hbf : Q.body.hasFvar = false)
    (hTf : r0.1.type.hasFvar = false) (hTb : r0.1.type.looseBVarsBounded 0 = true)
    (hTc : ConstsBound envC r0.1.type)
    (hle : ∀ c', (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD c' 0
      ≤ (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD c' 0)
    (hRT3 : ∀ c',
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).hasFvar = false ∧
      ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
        = true ∧
      ConstsBound envC ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)))
    (hB : tgtB pp.toBlockShape out c j = rc.rP + cA.2)
    (hFrEq : tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)))
    (hAbs : (Q.bodyO, Q.ihs)
      = tgtAbs μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j)
    {fd : List AnnotTerm} (hfl : fd.length = cA.2)
    (hF : ∀ (l : Nat) (x : Expr), Q.fvsF[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (rc.rP + l) x.fvarTypeD = some (fd.getD l default))
    {xs fs : List V}
    (hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c ++ fd)
      (xs ++ fs)) {Δ : List AnnotTerm}
    (hW : WalkCtx V mpC.base2 ψ (rc.rP + cA.2) (consList (xs ++ fs) ρ) Δ
      (Q.fvsPref ++ Q.fvsF).reverse)
    (hxs : xs.length = pp.toBlockShape.rulePrefixAt c)
    {r : Nat}
    (hr : r < (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length)
    {r1 : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr1 : (tgtRs out)[((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c
      j).getD r default).callee]? = some r1)
    (hm1 : memR ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
      default).callee)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
        c j r).map (·.2.2)) bs) :
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ
        ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
          default).callee).map (·.2.2))
      (xs ++ ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          envC ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ)))
        ++ [interp V (consList bs (consList (xs ++ fs) ρ))
          (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ c j r)])) := by
  have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr0 ψ, hrP]
  obtain ⟨hIds, hmemX⟩ := tgtCall_carrierG (fe := mkFEnv envC) hμ h hdR hN hmr hnd ψ ρ Q hrP hnP
    hdsOk hCf hCb hCc hbf hTf hTb hTc hle hRT3 hB hFrEq hAbs hpl hfl hF hsp hW hxs hr hm1 bs hbs
  obtain ⟨xs₁, fs₁, hxfs, hpre, -⟩ := spineFit_append_split hsp
  have hx₁ : xs₁ = xs := by
    have hl : xs₁.length = xs.length := by rw [hpre.length_eq, hpl, hxs, hrP]
    exact (List.append_inj hxfs.symm hl).1
  subst hx₁
  have hpref1 := blockRecHpref_run hμ mpC h ψ hr0 hr1 hpre
  have hprefR : SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ
      ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
        default).callee).map (·.2.2)).take (pp.toBlockShape.rulePrefixAt
          ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD r
            default).callee)) xs₁ := by
    rw [← List.map_take]; exact hpref1
  have hspC := blockRecSpineFit_of_parts (hm := hm1) hμ h hmr hr1 ψ ρ hprefR hIds hmemX
  rw [List.append_assoc] at hspC
  exact hspC

end MemVal

/-! ## One `ih` key at every class -/

section Key

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {outside nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

set_option maxHeartbeats 4000000 in
/-- **One `ih` key of the `(c, j)`-th rule, at EVERY class** (F3): the
callee is a position of the family sharing the rule's prefix, the key's
telescope carries the elimination bit, the `ih` type reads as the
Π-tower over the telescope whose body is the callee's conclusion at the
call's spine — and that spine FITS the callee recursor's binder data
(a major of the callee's class: a member's, `tgtCall_memSpine`, or a
container's, `tgtCall_outSpine`). -/
theorem tgtKey_cls (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hnd : d.memberNames.Nodup) (ψ : Name → Nat) (ρ : Nat → V)
    {c : Nat} (hc : c < (tgtRs out).length) {j : Nat} (hj : j < blockRecNCt (tgtRs out) c)
    {xs fs : List V}
    (hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs))
    (hxs : xs.length = pp.toBlockShape.rulePrefixAt c)
    {q : Nat} (hq : q < (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length) :
    ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q default).callee < (tgtRs out).length ∧
    pp.toBlockShape.rulePrefixAt ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q default).callee = pp.toBlockShape.rulePrefixAt c ∧
    (∀ dd ∈ (tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q), dd.2.1 = pwBit ψ (Level.zeronessOf
      (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))) ∧
    (∃ Xr : AnnotTerm,
      (∀ σ' : Nat → V, interp V σ' ((ihTyReads mpC.base2.acval envC ψ
          (tgtB pp.toBlockShape out c j) (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j)).getD q default)
        = interp V σ' (mkPisAV (tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q) Xr)) ∧
      ∀ bs : List V, SpineFit (consList (xs ++ fs) ρ) ((tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q).map (·.2.2)) bs →
        interp V (consList bs (consList (xs ++ fs) ρ)) Xr
          = interp V (consList (xs ++ ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))
              ++ [interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q)])) ρ)
            (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q default).callee)) ∧
    ∀ bs : List V, SpineFit (consList (xs ++ fs) ρ) ((tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q).map (·.2.2)) bs →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q default).callee).map
          (·.2.2))
        (xs ++ ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))
          ++ [interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q)])) := by
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  obtain ⟨rc, rhs0, Q, hrP, -, -, hB, hFrEq, hAbs, hbf, hTf, hTb, hTc, hle, hRT3, hdsOk, hCf, hCb,
    hCc, hfl, hF, hokPF⟩ := tgtFrame_cls hμ hcov h R hcls hdR hS hcore hmr ψ hc hr hcA hrhs
  have hW := tgtFrame_walk hμ h ψ hr Q hrP hTf hTb hTc hdsOk hCf hCb hCc hfl hF hokPF hsp
  have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr ψ, hrP]
  have hfsl : fs.length = cA.2 := by
    have hsl := hsp.length_eq
    simp only [List.length_append, hpl, hfl] at hsl
    omega
  have hformerF : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
    exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1
  obtain ⟨hcal, hrPc, hbits, hX⟩ := tgtIhKey_core (fe := mkFEnv envC) (mpC := mpC) hμ h hformerF ψ ρ
    Q hrP hdsOk hCf hCb hCc hbf hTf hTb hTc hle hRT3 hB hFrEq hAbs hxs hfsl hq
  refine ⟨hcal, hrPc, hbits, hX, fun bs hbs => ?_⟩
  obtain ⟨rcE, uE, hrcE, ⟨E⟩⟩ := targetEntryAt R hr
  have hnP : pp.toBlockShape.nP ≤ rc.rP := by
    have h2 : pp.toBlockShape.rulePrefixAt c = rcE.rP := by
      rw [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrcE, Option.getD_some]
    rw [hrP, h2]; exact E.hroom
  obtain ⟨r1, hr1⟩ : ∃ r1, (tgtRs out)[((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q default).callee]? = some r1 := ⟨_, List.getElem?_eq_getElem hcal⟩
  cases hmb1 : (tgtMajor out ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q default).callee).member with
  | some t =>
    have hm1 : (tgtMajor out ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q default).callee).member.isSome = true := by rw [hmb1]; rfl
    exact tgtCall_memSpine hμ h hdR hN hmr hnd ψ ρ hr Q hrP hnP hdsOk hCf hCb hCc hbf hTf hTb hTc
      hle hRT3 hB hFrEq hAbs hfl hF hsp hW hxs hq hr1 (tgtMemAt_of_member hcal hm1) bs hbs
  | none =>
    exact tgtCall_outSpine hμ hcov h R hN hmr ψ ρ hr Q hrP hnP hdsOk hCf hCb hCc hbf hTf hTb hTc
      hle hRT3 hB hFrEq hAbs hfl hF hsp hW hxs hq hr1 hrPc hmb1 (hcls _ hcal hmb1) bs hbs

end Key

end ConLeche.Model
