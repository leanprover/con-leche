module

public import ConLeche.Model.Inductives.TargetCallTie
public import ConLeche.Model.Inductives.TargetNodeRb
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Model.Inductives.TargetClassCall
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetCallWalk
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetRecRead
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Verify.Inductives.NestCallSyn
public import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.TargetRuleData

public section

/-!
# The callee's major, opened (lane NESTIND, session 27)

* `callMajor_open` — a call's typing run (`TargetCallRun`) peels the
  callee's type at the call's arguments to a `∀` whose domain, opened at
  bvar-closed terms, is a constant `I.{us}` applied to parameters `P` and
  the call's (opened) indices; `I.{us} P` names a member (a member callee:
  its head; an outside one: official's `is_nested`), and `P` is the
  prefix's first `nP` variables (member callee) or the callee major's own
  parameters up to the variables' annotations (outside callee);
* `readback_erasedEq_substFvars` — below a frame stack's holes, the one
  substitution of a call (`callSubst`) is the node read-back
  (`nodeRb`), up to the variables' annotations.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor RecShape NestCtx NestHole BinderMeta nestHoleConst)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- A constant spine naming a member names it. -/
theorem nestOcc_mkAppN_const_mem {names : List Name} {lo hi : Nat} {n : Name} {us : List Level}
    (hn : n ∈ names) (P : List Expr) : (Expr.mkAppN (.const n us) P).nestOcc names lo hi = true := by
  rw [nestOcc_mkAppN]
  simp [Expr.nestOcc, hn]

theorem erasedEqL_map {f : Expr → Expr} :
    ∀ {l : List Expr}, (∀ x ∈ l, Expr.ErasedEq (f x) x) → Expr.ErasedEqL (l.map f) l
  | [], _ => trivial
  | x :: _, h => ⟨h x List.mem_cons_self, erasedEqL_map fun y hy => h y (List.mem_cons_of_mem _ hy)⟩

/-- **The callee's major, opened** (see the module docstring). -/
theorem callMajor_open {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {outside nested : Bool}
    {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape outside nested block
      cvTas ctorsAs out)
    {env : Env} {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k : Nat} {pw : ConLeche.PropWhen} {ih : ConLeche.TargetIh}
    (C : ConLeche.TargetCallRun μ F env (tgtFam pp.toBlockShape (tgtRs out)) fvsPref fvsF fnorm
      teles absM base k pw ih)
    {rP : Nat} (hlp : fvsPref.length = rP)
    (hfvP : ∀ l, l < rP → ∃ ty, fvsPref[l]? = some (.fvar l ty))
    (hcal : ih.callee < (tgtRs out).length)
    (hidxLen : ih.idx.length + rP = (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD ih.callee 0)
    (hrPc : (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD ih.callee 0 = rP)
    {os : List Expr} (hos : AllFvars os)
    (hidxB : ∀ x ∈ ih.idx, x.looseBVarsBounded os.length = true) :
    ∃ (I : Name) (us : List Level) (P : List Expr),
      C.majDom.instantiateList os 0
        = Expr.mkAppN (.const I us) (P ++ ih.idx.map (·.instantiateList os 0)) ∧
      (Expr.mkAppN (.const I us) P).nestOcc pp.toBlockShape.memberNames 0 0 = true ∧
      (((tgtMajor out ih.callee).member.isSome = true ∧
          ∃ ms, pp.toBlockShape.members[pp.toBlockShape.recTgtAt ih.callee]? = some ms ∧
            I = ms.cvT.name ∧ us = pp.toBlockShape.lps.map .param ∧
            P = fvsPref.take pp.toBlockShape.nP) ∨
        ((tgtMajor out ih.callee).member = none ∧ I = (tgtMajor out ih.callee).ind ∧
          us = (tgtMajor out ih.callee).lvls ∧ Expr.ErasedEqL P (tgtMajor out ih.callee).ds)) := by
  generalize hcq : ih.callee = cq at *
  have hoscl : ∀ o ∈ os, o.looseBVarsBounded 0 = true := by
    intro o ho; obtain ⟨i, ty, rfl⟩ := hos o ho; rfl
  obtain ⟨r1, hr1⟩ : ∃ r1, (tgtRs out)[cq]? = some r1 := ⟨_, List.getElem?_eq_getElem hcal⟩
  obtain ⟨-, hlenR, -⟩ := ConLeche.recStageG_recNames h
  have hcalR : cq < pp.recs.length := by omega
  have hmIc : (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD cq 0
      = pp.toBlockShape.majorIdxAt cq := by
    simp only [tgtFam, ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_getElem hcalR]; rfl
  have hrPc' : pp.toBlockShape.rulePrefixAt cq = rP := by
    rw [← hrPc]
    simp only [tgtFam, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD,
      List.getElem?_map]
    rw [show pp.toBlockShape.recs = pp.recs from rfl, List.getElem?_eq_getElem hcalR]; rfl
  have hrecTy : (tgtFam pp.toBlockShape (tgtRs out)).recTys.getD cq (.sort .zero)
      = r1.1.type := by
    simp only [tgtFam, List.getD_eq_getElem?_getD, List.getElem?_map, hr1]; rfl
  obtain ⟨hTf1, -, -, hTb1, -⟩ := ConLeche.recStage_facts h r1 (List.mem_of_getElem? hr1)
  obtain ⟨hw01, -⟩ := recStage_tyClosed h hr1
  have hcallee := C.hcallee
  rw [hcq, hrecTy, C.hmajDom] at hcallee
  have hargsB : ∀ a ∈ fvsPref ++ ih.idx, a.looseBVarsBounded os.length = true := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, hty⟩ := hfvP l (by omega)
      rw [List.getElem?_eq_getElem hl, Option.some.injEq] at hty
      rw [hty]; rfl
    · exact hidxB a ha
  have hins := instPisAtLift_instantiateList hoscl (fvsPref ++ ih.idx) hargsB hTb1 hcallee
  simp only [Expr.instantiateList] at hins
  have hclA : ∀ a ∈ (fvsPref ++ ih.idx).map (·.instantiateList os 0),
      a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact looseBVarsBounded_instantiateList_allFvars hos b 0 (by simpa using hargsB b hb)
  have hlenA : ((fvsPref ++ ih.idx).map (·.instantiateList os 0)).length
      = pp.toBlockShape.majorIdxAt cq := by
    rw [List.length_map, List.length_append, hlp, ← hmIc]; omega
  -- the prefix's variables are kept by the opening
  have hprefI : fvsPref.map (·.instantiateList os 0) = fvsPref := by
    apply List.ext_getElem (by simp)
    intro l h1 h2
    obtain ⟨ty, hty⟩ := hfvP l (by simp at h1; omega)
    rw [List.getElem?_eq_getElem h2, Option.some.injEq] at hty
    simp only [List.getElem_map, hty]
    exact ConLeche.Expr.instantiateList_eq_self rfl
  have hdropA : ((fvsPref ++ ih.idx).map (·.instantiateList os 0)).drop
      (pp.toBlockShape.rulePrefixAt cq) = ih.idx.map (·.instantiateList os 0) := by
    rw [hrPc', List.map_append, List.drop_append_of_le_length (by simp [hlp]),
      List.drop_eq_nil_of_le (by simp [hlp]), List.nil_append]
  cases hmb : (tgtMajor out cq).member with
  | some t =>
    have hm : (tgtMajor out cq).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hcal hm
    obtain ⟨ms, body, bm, hms, heq⟩ := tgtMajDom_open h hmR hr1 hclA hlenA hins
    injection heq with hdom
    rw [hdropA] at hdom
    have hnP : pp.toBlockShape.nP ≤ rP := by
      obtain ⟨_, _, hall⟩ := ConLeche.recStageG_recNames h
      obtain ⟨_, _, _, _, -, -, hle, -⟩ := hall cq (by omega)
      rw [← hrPc']; exact hle
    have htake : ((fvsPref ++ ih.idx).map (·.instantiateList os 0)).take pp.toBlockShape.nP
        = fvsPref.take pp.toBlockShape.nP := by
      rw [List.map_append, hprefI, List.take_append_of_le_length (by omega)]
    rw [htake] at hdom
    refine ⟨_, _, _, hdom, nestOcc_mkAppN_const_mem ?_ _, Or.inl ⟨rfl, ms, hms, rfl, rfl, rfl⟩⟩
    show ms.cvT.name ∈ pp.toBlockShape.members.map (·.cvT.name)
    exact List.mem_map_of_mem (List.mem_of_getElem? hms)
  | none =>
    obtain ⟨hdsS, body', bm', heq⟩ := tgtMajDom_openOut R hr1 hmb hclA hlenA hTf1 hw01 hins
    injection heq with hdom
    rw [hdropA] at hdom
    have hpt : ∀ x ∈ (tgtMajor out cq).ds, Expr.ErasedEq (replF (fun i =>
        ((fvsPref ++ ih.idx).map (·.instantiateList os 0))[i]?) x) x := by
      refine fun x hx => replF_erasedEq _ fun l hl y hy => ?_
      have hlt : l.1 < pp.toBlockShape.nP := (hdsS x hx).2.2 l hl
      have hnP : pp.toBlockShape.nP ≤ rP := by
        obtain ⟨_, _, hall⟩ := ConLeche.recStageG_recNames h
        obtain ⟨_, _, _, _, -, -, hle, -⟩ := hall cq (by omega)
        rw [← hrPc']; exact hle
      rw [List.map_append, hprefI, List.getElem?_append_left (by omega)] at hy
      obtain ⟨ty, hty⟩ := hfvP l.1 (by omega)
      rw [hty, Option.some.injEq] at hy
      exact ⟨ty, hy.symm⟩
    have hEL := erasedEqL_map hpt
    obtain ⟨rc1, u1, -, ⟨E1⟩⟩ := targetEntryAt R hr1
    obtain ⟨x, hx, hxo⟩ := E1.outside_ment hmb
    refine ⟨_, _, _, hdom, ?_, Or.inr ⟨rfl, rfl, rfl, hEL⟩⟩
    rw [nestOcc_mkAppN, Bool.or_eq_true]
    refine Or.inr (List.any_eq_true.mpr ⟨replF (fun i =>
      ((fvsPref ++ ih.idx).map (·.instantiateList os 0))[i]?) x, List.mem_map_of_mem hx, ?_⟩)
    rw [erasedEq_nestOcc _ _ (hpt x hx)]
    exact hxo

/-! ## The one substitution below the holes is the read-back -/

/-- Below `b₀ ≤ b`, the substitution does not see its bound. -/
theorem substFvars_congr_below {D : Nat} {s : Nat → Expr} {b₀ b : Nat} (hb : b₀ ≤ b) :
    ∀ (X : Expr), X.fvarsBelow b₀ → Expr.substFvars b D s X = Expr.substFvars b₀ D s X := by
  intro X
  induction X with
  | bvar i => intro _; rfl
  | fvar i ty _ =>
    intro h
    simp only [Expr.fvarsBelow] at h
    simp only [Expr.substFvars, if_pos h, if_pos (Nat.lt_of_lt_of_le h hb)]
  | sort u => intro _; rfl
  | const n us => intro _; rfl
  | lit l => intro _; rfl
  | app f a ihf iha => intro h; simp only [Expr.substFvars, ihf h.1, iha h.2]
  | lam t body m iht ihb => intro h; simp only [Expr.substFvars, iht h.1, ihb h.2]
  | forallE t body m iht ihb => intro h; simp only [Expr.substFvars, iht h.1, ihb h.2]
  | letE t v body iht ihv ihb =>
    intro h; simp only [Expr.substFvars, iht h.1, ihv h.2.1, ihb h.2.2]
  | proj n i e ih => intro h; simp only [Expr.substFvars, ih h]

/-- **The one substitution below the holes is the read-back**, up to the
variables' annotations. -/
theorem readback_erasedEq_substFvars {ctx : NestCtx} {prog : List NestHole} {fvsF : List Expr}
    {b D : Nat} (hb : ctx.hiAt prog.length ≤ b) {x : Expr}
    (hx : x.fvarsBelow (ctx.hiAt prog.length)) :
    Expr.ErasedEq (nodeRb ctx prog x) (Expr.substFvars b D (callSubst ctx prog fvsF) x) := by
  rw [← concrete_eq_nodeRb ctx prog hx, substFvars_congr_below hb x hx]
  refine Expr.replaceFVars_erasedEq_substFvars (fun v hv ty => ?_) x hx
  by_cases h1 : v < ctx.nP
  · rw [nestHoleConst_lt_nP h1]
    simp only [callSubst, if_pos h1, Option.getD_none]
    simp [Expr.ErasedEq]
  · obtain ⟨n, us, hc⟩ := nestHoleConst_hole (prog := prog) (Nat.le_of_not_lt h1) hv
    simp only [callSubst, if_neg h1, if_pos hv, hc, Option.getD_some]
    exact Expr.ErasedEq.rfl _

end ConLeche.Model
