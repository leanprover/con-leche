module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetResidue
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

section FapEis

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

end Core

end ConLeche.Model
