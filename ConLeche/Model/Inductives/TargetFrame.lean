module

public import ConLeche.Model.Inductives.TargetIhSlot
public import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope

public section

/-!
# The target rule's frame: prefix and fields (lane RECLIB, B3 (a))

The rule's frame is opened by the target check exactly as by today's:
the recursor's prefix off its stored type (`openPisAtFvars rP recTy 0`),
the constructor at the major's parameters (`instPisWith`), its fields
off that (`openPisAtFvars nF crest rP`).  The frame's opener list is
therefore scoped, and its annotations are bvar-closed, name stored
constants and draw their leaves from the frame again — the frame facts
`walkCtx_blockFrame` and `targetIh_scope` take, proved here from the
three openings with today's helpers.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

/-- **The target rule's frame facts** from its three openings. -/
theorem targetFrame_facts {envT : Env} {rP nF nP : Nat} {recTy cty crest oP cbody : Expr}
    {fvsPref fvsF ds : List Expr}
    (h₁ : ConLeche.openPisAtFvars rP recTy 0 = some (fvsPref, oP))
    (hcr : ConLeche.instPisWith ds cty = some crest) (hds : ds = fvsPref.take nP)
    (h₂ : ConLeche.openPisAtFvars nF crest rP = some (fvsF, cbody))
    (hTf : recTy.hasFvar = false) (hTb : recTy.looseBVarsBounded 0 = true)
    (hTc : ConstsBound envT recTy)
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hCc : ConstsBound envT cty) :
    FvarList (rP + nF) (fvsPref ++ fvsF).reverse ∧
    (∀ x ∈ fvsPref ++ fvsF, (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
    (∀ x ∈ fvsPref ++ fvsF, ConstsBound envT x) ∧
    (∀ x ∈ fvsPref ++ fvsF, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF) := by
  subst hds
  rw [instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨cpref, crest'⟩, hinstC, hcr⟩ := Option.map_eq_some_iff.mp hcr
  have hcr' : crest = crest' := hcr.symm
  subst hcr'
  have hw₁ : Expr.WScoped 0 recTy := Expr.WScoped.of_not_hasFvar hTf
  have hL1 : FvarList rP fvsPref.reverse := by
    have := fvarList_of_open fvarList_nil h₁ hw₁
    rwa [Nat.zero_add, List.append_nil] at this
  have hw₂ := blockRuleHw2_of h₁ hw₁ hCf hinstC
  have hL2 := fvarList_of_open hL1 h₂ hw₂
  have h₃ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (rP + nF)
      = some ([], Expr.sort .zero) := rfl
  have hb₂ : crest.looseBVarsBounded 0 = true :=
    (ConLeche.Verify.instPisAt_bounded _ hinstC hCb
      (fun a ha => openPisAtFvars_fvars_closed h₁ a (List.mem_of_mem_take ha))).2
  have hc₂ : ConstsBound envT crest :=
    constsBound_instPisAt _ hinstC hCc
      (fun a ha => (openPisAtFvars_constsBound _ hTc h₁).1 a (List.mem_of_mem_take ha))
  obtain ⟨hlb, -⟩ := blockRuleHlbF_of h₁ h₂ h₃ hTb hb₂ rfl
  have hcb := blockRuleHcbF_of h₁ h₂ h₃ hTc hc₂ (by simp)
  have hcl := blockRuleHclF_of (nR := 0) (ihTele' := Expr.sort .zero) (o₃ := Expr.sort .zero)
    (fvsIh := []) h₁ h₂ rfl hTf hCf hinstC (fun l hl => by simp [Expr.fvarLeaves] at hl)
  simp only [List.append_nil] at hlb hcb hcl
  exact ⟨by rw [List.reverse_append]; exact hL2, hlb, hcb, hcl⟩

/-- The frame's opener list extended by the `ih` variables. -/
theorem fvarList_ihs {B : Nat} {L : List Expr} (hL : FvarList B L) (tys : List Expr)
    (hws : ∀ t ∈ tys, Expr.WScoped B t) :
    FvarList (B + tys.length) ((ihFvarsAt B tys).reverse ++ L) := by
  suffices key : ∀ n, n ≤ tys.length →
      FvarList (B + n)
        (((List.range n).map fun r => Expr.fvar (B + r) (tys.getD r default)).reverse ++ L) by
    exact key tys.length (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro _; simpa using hL
  | succ n ih =>
    intro hn
    have h := (ih (by omega)).cons (tys.getD n default)
      (((hws _ (by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact List.getElem_mem _)).mono (by omega)))
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [show B + (n + 1) = B + n + 1 from by omega]
    exact h

/-- The `ih` variables are `fvar (B + r)` at their types. -/
theorem ihs_fv_eq {fr : ConLeche.TargetFrame} {B : Nat} {ihs : Array ConLeche.TargetIh}
    (hwf : TargetIhWF fr B ihs) :
    ihs.toList.map (·.fv) = ihFvarsAt B (ihs.toList.map (·.ty)) := by
  apply List.ext_getElem (by simp [ihFvarsAt])
  intro r h1 h2
  simp only [List.getElem_map, ihFvarsAt, List.getElem_range, List.length_map] at h1 ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
    Array.getElem?_eq_getElem (by simpa using h1)]
  simpa using (hwf r (by simpa using h1)).1

/-- A frame entry's leaves are frame entries. -/
theorem frame_leaves_mem {E : Nat} {Lf : List Expr} (hFr : FvarList E Lf.reverse)
    (hher : ∀ x ∈ Lf, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar l.1 l.2 ∈ Lf) :
    ∀ x ∈ Lf, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lf := by
  intro x hx l hl
  obtain ⟨i, ty, rfl⟩ := hFr.mem_fvar (List.mem_reverse.mpr hx)
  simp only [Expr.fvarLeaves, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact hx
  · exact hher _ hx l hl

universe uv

variable {V : Type uv} [SetTheory V] {μ : CheckMode}

set_option maxHeartbeats 2000000 in
/-- **The residue's context at a target rule's entry, from the run** (B3
(a)): the frame opened by the rule's run, read to `pdoms ++ fdoms` and
fitted by the prefix and field values, with every `ih` slot on top at the
call's value at the callee's value `Rv c`.  What stays a premise is what
the rule's run does not see: the frame's readings, grading and fit (the
contract's), the stored recursor and constructor types' facts, and the
callees' values. -/
theorem walkCtx_targetRule (hμ : μ.verifiedChecks = true) {feR feT : ConLeche.FEnv}
    {mT : EnvModel V feT.env} {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F : Nat} {p : ConLeche.BlockShape} {formerTys : List Expr}
    {fam : ConLeche.TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr}
    {M : ConLeche.TargetMajor} {c : ConstantVal × Nat} {rhs out : Expr}
    (R : ConLeche.TargetRuleRun μ F feR feT p formerTys fam cvR rP recTy M c rhs out)
    (hle : ∀ c', fam.rPs.getD c' 0 ≤ fam.mIs.getD c' 0)
    (hbf : R.body.hasFvar = false)
    (hds : M.ds = R.fvsPref.take p.nP)
    (hTf : recTy.hasFvar = false) (hTb : recTy.looseBVarsBounded 0 = true)
    (hTc : ConstsBound feT.env recTy)
    (hCf : (ConLeche.targetCtorAt M c.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M c.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound feT.env (ConLeche.targetCtorAt M c.1))
    (hformer : ∀ t ∈ formerTys, t.hasFvar = false)
    (hRT : ∀ c',
      (fam.recTys.getD c' (.sort .zero)).hasFvar = false ∧
      (fam.recTys.getD c' (.sort .zero)).looseBVarsBounded 0 = true ∧
      ConstsBound feT.env (fam.recTys.getD c' (.sort .zero)) ∧
      ∃ RTa : AnnotTerm,
        denoteMeta mT.acval feT.env φ (rP + c.2) (fam.recTys.getD c' (.sort .zero)) = some RTa ∧
        (∀ σ : Nat → V, WellDenotedV V σ RTa))
    -- the frame's readings, grading and fit
    {pdoms fdoms : List AnnotTerm} (hp : pdoms.length = rP) (hf : fdoms.length = c.2)
    (hdoms : ∀ (i : Nat) (x : Expr), (R.fvsPref ++ R.fvsF)[i]? = some x →
      denoteMeta mT.acval feT.env φ i (Expr.fvarTypeD x)
        = some ((pdoms ++ fdoms).reverse.getD (rP + c.2 - 1 - i) default))
    (hokΔ : ∀ i, i < rP + c.2 →
      ∀ ρ : Nat → V, Sat V (pdoms ++ fdoms).reverse ρ →
        WellDenotedV V (fun j => ρ (j + (rP + c.2 - 1 - i) + 1))
          ((pdoms ++ fdoms).reverse.getD (rP + c.2 - 1 - i) default))
    {ρ₀ : Nat → V} {xs fs : List V} (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    -- the callees' values
    (Rv : Nat → V)
    (hR : ∀ ih ∈ R.ihs.toList, ∀ RTa : AnnotTerm,
      denoteMeta mT.acval feT.env φ (rP + c.2) (fam.recTys.getD ih.callee (.sort .zero))
        = some RTa →
      Rv ih.callee ∈ˢ interp V (consList (xs ++ fs) ρ₀) RTa) :
    WalkCtx V mT φ (rP + c.2 + R.ihs.size)
      (consList (ihValsAt Rv (consList (xs ++ fs) ρ₀) R.ihs.toList
        (ihLamReads mT.acval feT.env φ fam R.fvsPref R.fvsF (R.fnorm.map fun t => t.piBinders.1)
          (rP + c.2) (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) R.ihs.toList))
        (consList (xs ++ fs) ρ₀))
      ((ihDomsLifted (ihTyReads mT.acval feT.env φ (rP + c.2) R.ihs.toList)).reverse
        ++ (pdoms ++ fdoms).reverse)
      (targetFrameIh (R.fvsPref ++ R.fvsF) R.ihs) := by
  -- the frame's own facts
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts R.hpref R.hcrest hds R.hfld hTf hTb hTc
    hCf hCb hCc
  -- the frame's context
  have h₃ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (rP + c.2)
      = some ([], Expr.sort .zero) := rfl
  have hW0 := walkCtx_blockFrame (V := V) (mT := mT) (ψ := φ) (ihdoms := []) (ihvals := [])
    R.hpref R.hfld h₃ hp hf rfl
    (by simpa using hdoms) (by simpa using hokΔ)
    (by simpa using hlbF) (by simpa using hcbF) (by simpa using hher) hsp (by simp [SpineFit])
  simp only [List.append_nil, List.reverse_nil, List.nil_append, consList_nil,
    Nat.add_zero] at hW0
  -- every `ih` slot
  have hcalls := fun ih (hih : ih ∈ R.ihs.toList) => R.call hih
  have hwf : TargetIhWF (ConLeche.targetFrameOf fam rP R.fvsPref R.fvsF R.fnorm
      (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))) (rP + c.2) R.ihs :=
    (targetAbstract_acc 0 _ #[] _ _ R.habs).2 (fun r hr => absurd hr (by simp))
  have h := walkCtx_targetEntry hμ hacl hin hcalls hwf hFr hW0
    (fun ih hih => (targetIh_scope hμ R mT.wf hle hbf hFr hher hcbF hformer
      (fun c' => (hRT c').1) hih).imp id fun h => h.imp id fun h => h.imp id
        fun h => h.imp id fun h => h.1)
    (fun ih _ => hRT ih.callee) Rv hR
  have e : targetFrameIh (R.fvsPref ++ R.fvsF) R.ihs
      = (R.ihs.toList.map (·.fv)).reverse ++ (R.fvsPref ++ R.fvsF).reverse := by
    rw [targetFrameIh, List.reverse_append]
  rw [e]
  exact h.2

set_option maxHeartbeats 2000000 in
/-- **A target rule's two readings exist and are bound by their frames**
(from the run alone): the residue at the frame and the `ih` variables,
and every call λ at the frame and its callee slot.  The residue's
leaves are the frame's or an `ih` variable's, whose type the walk
records bvar-closed (`targetIh_scope`); both terms are inferred
(`R.hty`, K1's `hcall`), so they read (`acceptedReads_of`). -/
theorem targetRule_reads (hμ : μ.verifiedChecks = true) {feR feT : ConLeche.FEnv}
    (mT : EnvModel V feT.env) (φ : Name → Nat)
    {F : Nat} {p : ConLeche.BlockShape} {formerTys : List Expr}
    {fam : ConLeche.TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr}
    {M : ConLeche.TargetMajor} {c : ConstantVal × Nat} {rhs out : Expr}
    (R : ConLeche.TargetRuleRun μ F feR feT p formerTys fam cvR rP recTy M c rhs out)
    (hle : ∀ c', fam.rPs.getD c' 0 ≤ fam.mIs.getD c' 0)
    (hbf : R.body.hasFvar = false)
    (hds : M.ds = R.fvsPref.take p.nP)
    (hTf : recTy.hasFvar = false) (hTb : recTy.looseBVarsBounded 0 = true)
    (hTc : ConstsBound feT.env recTy)
    (hCf : (ConLeche.targetCtorAt M c.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M c.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound feT.env (ConLeche.targetCtorAt M c.1))
    (hformer : ∀ t ∈ formerTys, t.hasFvar = false)
    (hRT : ∀ c',
      (fam.recTys.getD c' (.sort .zero)).hasFvar = false ∧
      (fam.recTys.getD c' (.sort .zero)).looseBVarsBounded 0 = true ∧
      ConstsBound feT.env (fam.recTys.getD c' (.sort .zero))) :
    (∃ Bv : AnnotTerm,
      denoteMeta mT.acval feT.env φ (rP + c.2 + R.ihs.size) R.bodyO = some Bv ∧
      ConLeche.Term.Term.bvarsBelow (rP + c.2 + R.ihs.size) Bv.erase) ∧
    (∀ (r : Nat) (ih : ConLeche.TargetIh), R.ihs[r]? = some ih →
      ∃ Lr : AnnotTerm, denoteMeta mT.acval feT.env φ (rP + c.2 + 1)
          (targetCallLam fam R.fvsPref R.fvsF (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
            (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) = some Lr ∧
        ConstsBound feT.env (targetCallLam fam R.fvsPref R.fvsF
          (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
          (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) ∧
        ConLeche.Term.Term.bvarsBelow (rP + c.2 + 1) Lr.erase) ∧
    -- the residue's scoping at the frame and the `ih` variables
    FvarList (rP + c.2 + R.ihs.size) (targetFrameIh (R.fvsPref ++ R.fvsF) R.ihs) ∧
    (∀ l ∈ R.bodyO.fvarLeaves, Expr.fvar l.1 l.2 ∈ targetFrameIh (R.fvsPref ++ R.fvsF) R.ihs) ∧
    R.bodyO.looseBVarsBounded 0 = true := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts R.hpref R.hcrest hds R.hfld hTf hTb hTc
    hCf hCb hCc
  have hframeL := frame_leaves_mem hFr hher
  have hwf : TargetIhWF (ConLeche.targetFrameOf fam rP R.fvsPref R.fvsF R.fnorm
      (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))) (rP + c.2) R.ihs :=
    (targetAbstract_acc 0 _ #[] _ _ R.habs).2 (fun r hr => absurd hr (by simp))
  have hscope := fun ih (hih : ih ∈ R.ihs.toList) =>
    targetIh_scope hμ R mT.wf hle hbf hFr hher hcbF hformer (fun c' => (hRT c').1) hih
  have hfvEq := ihs_fv_eq hwf
  have hL : FvarList (rP + c.2 + R.ihs.size) (targetFrameIh (R.fvsPref ++ R.fvsF) R.ihs) := by
    have h := fvarList_ihs hFr (R.ihs.toList.map (·.ty)) (fun t ht => by
      obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp ht
      exact wscoped_of_leaves_mem hFr _ (hscope ih hih).1)
    rw [targetFrameIh, List.reverse_append, hfvEq]
    simpa using h
  -- the residue's leaves, and their types' bvar-closedness
  have hlL : ∀ l ∈ R.bodyO.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ targetFrameIh (R.fvsPref ++ R.fvsF) R.ihs ∧
        l.2.looseBVarsBounded 0 = true := by
    intro l hl
    rw [targetFrameIh, List.mem_reverse]
    rcases targetAbstract_out_leaves 0 _ #[] _ _ R.habs l hl with h0 | ⟨ih, hih, h0⟩
    · obtain ⟨x, hx, hlx⟩ := fvarLeaves_instantiateList hFr R.body hbf 0 l h0
      have hm := hframeL x (List.mem_reverse.mp hx) l hlx
      exact ⟨List.mem_append_left _ hm, hlbF _ hm⟩
    · obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hih
      have hr' : r < R.ihs.size := by simpa using hr
      obtain ⟨hfv, -⟩ := hwf r hr'
      have hget' : R.ihs[r] = ih := by simpa using hget
      rw [hget'] at hfv
      rw [hfv] at h0
      simp only [Expr.fvarLeaves, List.mem_cons] at h0
      rcases h0 with rfl | h0
      · exact ⟨List.mem_append_right _ (List.mem_map.mpr ⟨ih, hih, hfv⟩), (hscope ih hih).2.1⟩
      · have hm := (hscope ih hih).1 l h0 |> List.mem_reverse.mp
        exact ⟨List.mem_append_left _ hm, hlbF _ hm⟩
  have hinfB := Rules.inferTypeCore_bridge R.hty
  have hbT : R.bodyO.looseBVarsBounded 0 = true := ConLeche.infer_full_bvarClosed hinfB
  have hws := wscoped_of_leaves_mem hL _ (fun l hl => (hlL l hl).1)
  obtain ⟨Bv, hBv⟩ := acceptedReads_of mT φ R.hty hws hbT (fun l hl => (hlL l hl).2)
  refine ⟨⟨Bv, hBv, bvarsBelow_of_reading (m := mT) hws hbT hBv⟩, fun r ih hr => ?_, hL,
    fun l hl => (hlL l hl).1, hbT⟩
  obtain ⟨hrl, hrget⟩ := Array.getElem?_eq_some_iff.mp hr
  have hih : ih ∈ R.ihs.toList := by rw [← hrget]; exact Array.getElem_mem_toList hrl
  obtain ⟨C⟩ := R.call hih
  obtain ⟨-, -, -, hlE, -, -⟩ := hscope ih hih
  obtain ⟨hRf, hRb, hRcb⟩ := hRT ih.callee
  have hL1 : FvarList (rP + c.2 + 1)
      (Expr.fvar (rP + c.2) (fam.recTys.getD ih.callee (.sort .zero))
        :: (R.fvsPref ++ R.fvsF).reverse) :=
    hFr.cons _ (Expr.WScoped.of_not_hasFvar hRf)
  have hLE : Expr.LeavesBounded (targetCallLam fam R.fvsPref R.fvsF
      (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
      (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) := by
    intro l hl
    rcases List.mem_cons.mp (hlE l hl) with h0 | h0
    · injection h0 with _ h2; rw [h2]; exact hRb
    · exact hlbF _ (List.mem_reverse.mp h0)
  have hbC := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge C.hcall)
  obtain ⟨Lr, hLr⟩ := acceptedReads_of mT φ C.hcall
    (wscoped_of_leaves_mem hL1 _ hlE) hbC hLE
  have hcbLam : ConstsBound feT.env (targetCallLam fam R.fvsPref R.fvsF
      (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
      (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) := by
    refine infer_constsBound_of_full (Rules.inferTypeCore_bridge C.hcall) rfl (fun l hl => ?_)
    rcases List.mem_cons.mp (hlE l hl) with h0 | h0
    · injection h0 with _ h2; rw [h2]; exact hRcb
    · have := hcbF _ (List.mem_reverse.mp h0); simpa using this
  exact ⟨Lr, hLr, hcbLam,
    bvarsBelow_of_reading (m := mT) (wscoped_of_leaves_mem hL1 _ hlE) hbC hLr⟩

set_option maxHeartbeats 4000000 in
/-- **A target rule's two readings are GRADED at the caller's frame**
(`heqV`'s target rows): at a frame the prefix and the fields fit, and
callee values typed at their stored types, every call λ is graded at
its callee's value (`targetCall_ihSlot`, K1's run) and the residue is
graded at the frame extended by the `ih` values (`walkCtx_targetRule`
and the residue's own inference). -/
theorem targetRule_graded (hμ : μ.verifiedChecks = true) {feR feT : ConLeche.FEnv}
    {mT : EnvModel V feT.env} {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F : Nat} {p : ConLeche.BlockShape} {formerTys : List Expr}
    {fam : ConLeche.TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr}
    {M : ConLeche.TargetMajor} {c : ConstantVal × Nat} {rhs out : Expr}
    (R : ConLeche.TargetRuleRun μ F feR feT p formerTys fam cvR rP recTy M c rhs out)
    (hle : ∀ c', fam.rPs.getD c' 0 ≤ fam.mIs.getD c' 0)
    (hbf : R.body.hasFvar = false)
    (hds : M.ds = R.fvsPref.take p.nP)
    (hTf : recTy.hasFvar = false) (hTb : recTy.looseBVarsBounded 0 = true)
    (hTc : ConstsBound feT.env recTy)
    (hCf : (ConLeche.targetCtorAt M c.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M c.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound feT.env (ConLeche.targetCtorAt M c.1))
    (hformer : ∀ t ∈ formerTys, t.hasFvar = false)
    (hRT : ∀ c',
      (fam.recTys.getD c' (.sort .zero)).hasFvar = false ∧
      (fam.recTys.getD c' (.sort .zero)).looseBVarsBounded 0 = true ∧
      ConstsBound feT.env (fam.recTys.getD c' (.sort .zero)) ∧
      ∃ RTa : AnnotTerm,
        denoteMeta mT.acval feT.env φ (rP + c.2) (fam.recTys.getD c' (.sort .zero)) = some RTa ∧
        (∀ σ : Nat → V, WellDenotedV V σ RTa))
    {pdoms fdoms : List AnnotTerm} (hp : pdoms.length = rP) (hf : fdoms.length = c.2)
    (hdoms : ∀ (i : Nat) (x : Expr), (R.fvsPref ++ R.fvsF)[i]? = some x →
      denoteMeta mT.acval feT.env φ i (Expr.fvarTypeD x)
        = some ((pdoms ++ fdoms).reverse.getD (rP + c.2 - 1 - i) default))
    (hokΔ : ∀ i, i < rP + c.2 →
      ∀ ρ : Nat → V, Sat V (pdoms ++ fdoms).reverse ρ →
        WellDenotedV V (fun j => ρ (j + (rP + c.2 - 1 - i) + 1))
          ((pdoms ++ fdoms).reverse.getD (rP + c.2 - 1 - i) default))
    {ρ₀ : Nat → V} {xs fs : List V} (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (Rv : Nat → V)
    (hR : ∀ ih ∈ R.ihs.toList, ∀ RTa : AnnotTerm,
      denoteMeta mT.acval feT.env φ (rP + c.2) (fam.recTys.getD ih.callee (.sort .zero))
        = some RTa →
      Rv ih.callee ∈ˢ interp V (consList (xs ++ fs) ρ₀) RTa) :
    (∀ (r : Nat) (ih : ConLeche.TargetIh), R.ihs[r]? = some ih →
      ∃ Lr : AnnotTerm, denoteMeta mT.acval feT.env φ (rP + c.2 + 1)
          (targetCallLam fam R.fvsPref R.fvsF (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
            (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) = some Lr ∧
        WellDenotedV V (cons (Rv ih.callee) (consList (xs ++ fs) ρ₀)) Lr) ∧
    ∃ Bv : AnnotTerm,
      denoteMeta mT.acval feT.env φ (rP + c.2 + R.ihs.size) R.bodyO = some Bv ∧
      WellDenotedV V (consList (ihValsAt Rv (consList (xs ++ fs) ρ₀) R.ihs.toList
        (ihLamReads mT.acval feT.env φ fam R.fvsPref R.fvsF (R.fnorm.map fun t => t.piBinders.1)
          (rP + c.2) (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) R.ihs.toList))
        (consList (xs ++ fs) ρ₀)) Bv := by
  have hμ' := hμ
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts R.hpref R.hcrest hds R.hfld hTf hTb hTc
    hCf hCb hCc
  have h₃ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (rP + c.2)
      = some ([], Expr.sort .zero) := rfl
  have hW0 := walkCtx_blockFrame (V := V) (mT := mT) (ψ := φ) (ihdoms := []) (ihvals := [])
    R.hpref R.hfld h₃ hp hf rfl
    (by simpa using hdoms) (by simpa using hokΔ)
    (by simpa using hlbF) (by simpa using hcbF) (by simpa using hher) hsp (by simp [SpineFit])
  simp only [List.append_nil, List.reverse_nil, List.nil_append, consList_nil,
    Nat.add_zero] at hW0
  obtain ⟨⟨Bv, hBv, -⟩, -, hL, hlL, hbT⟩ := targetRule_reads hμ' mT φ R hle hbf hds hTf hTb hTc
    hCf hCb hCc hformer (fun c' => ⟨(hRT c').1, (hRT c').2.1, (hRT c').2.2.1⟩)
  have hW := walkCtx_targetRule hμ' hacl hin R hle hbf hds hTf hTb hTc hCf hCb hCc hformer hRT
    hp hf hdoms hokΔ hsp Rv hR
  refine ⟨fun r ih hr => ?_, Bv, hBv, ?_⟩
  · obtain ⟨hrl, hrget⟩ := Array.getElem?_eq_some_iff.mp hr
    have hih : ih ∈ R.ihs.toList := by rw [← hrget]; exact Array.getElem_mem_toList hrl
    obtain ⟨C⟩ := R.call hih
    obtain ⟨hlT, hbT', -, hlE, hbE, -⟩ :=
      targetIh_scope hμ' R mT.wf hle hbf hFr hher hcbF hformer (fun c' => (hRT c').1) hih
    obtain ⟨hRf, hRb, hRcb, RTa, hRTa, hRG⟩ := hRT ih.callee
    obtain ⟨-, Lr, -, -, hLr, -, hG⟩ := targetCall_ihSlot hμ' hacl hin C hFr hW0 hlT hbT' hlE hbE
      hRf hRb hRcb hRTa hRG (hR ih hih RTa hRTa)
    exact ⟨Lr, hLr, hG⟩
  · obtain ⟨-, -, hG⟩ := WalkCtx.subjOkL hacl1 hin hL hW hlL hbT hBv
      ⟨_, Rules.inferTypeCore_bridge R.hty⟩
    exact hG _ hW.2.1

set_option maxHeartbeats 4000000 in
/-- **The body equation of one target-checked rule, at its run** (B3 (c),
the rule side): the stored rule body, opened at the caller's frame and
read at the consed environment, is the residue read at the frame
extended by the `ih` values — the calls' λs at the callees' values.
`targetRuleBodyEq` with every premise the rule's run determines
discharged: the frame's facts (`targetFrame_facts`), the residue's
context (`walkCtx_targetRule`), its scoping and typing (the run's
inference, `targetAbstract_out_leaves`), the `ih` values' identification
with the λ readings.  Left: the frame's readings, grading and fit, the
stored types' facts, the callees' values and the two environments'
agreement. -/
theorem targetRuleBodyEq_run (hμ : μ.verifiedChecks = true) {feR feT : ConLeche.FEnv}
    {mT : EnvModel V feT.env} {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    (haclT : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    (hproj : ∀ (sn : Name) (i : Nat), feT.env.findProj? sn i = env.findProj? sn i)
    (hmono : ∀ (D : Nat) (y : Expr) (ya : AnnotTerm), ConstsBound feT.env y →
      denoteMeta mT.acval feT.env φ D y = some ya → denoteMeta acval env φ D y = some ya)
    {F : Nat} {p : ConLeche.BlockShape} {formerTys : List Expr}
    {fam : ConLeche.TargetFamily} {cvR : ConstantVal} {rP : Nat} {recTy : Expr}
    {M : ConLeche.TargetMajor} {c : ConstantVal × Nat} {rhs out : Expr}
    (R : ConLeche.TargetRuleRun μ F feR feT p formerTys fam cvR rP recTy M c rhs out)
    (hle : ∀ c', fam.rPs.getD c' 0 ≤ fam.mIs.getD c' 0)
    (hbf : R.body.hasFvar = false)
    (hds : M.ds = R.fvsPref.take p.nP)
    (hTf : recTy.hasFvar = false) (hTb : recTy.looseBVarsBounded 0 = true)
    (hTc : ConstsBound feT.env recTy)
    (hCf : (ConLeche.targetCtorAt M c.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt M c.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound feT.env (ConLeche.targetCtorAt M c.1))
    (hformer : ∀ t ∈ formerTys, t.hasFvar = false)
    (hRT : ∀ c',
      (fam.recTys.getD c' (.sort .zero)).hasFvar = false ∧
      (fam.recTys.getD c' (.sort .zero)).looseBVarsBounded 0 = true ∧
      ConstsBound feT.env (fam.recTys.getD c' (.sort .zero)) ∧
      ∃ RTa : AnnotTerm,
        denoteMeta mT.acval feT.env φ (rP + c.2) (fam.recTys.getD c' (.sort .zero)) = some RTa ∧
        (∀ σ : Nat → V, WellDenotedV V σ RTa))
    {pdoms fdoms : List AnnotTerm} (hp : pdoms.length = rP) (hf : fdoms.length = c.2)
    (hdoms : ∀ (i : Nat) (x : Expr), (R.fvsPref ++ R.fvsF)[i]? = some x →
      denoteMeta mT.acval feT.env φ i (Expr.fvarTypeD x)
        = some ((pdoms ++ fdoms).reverse.getD (rP + c.2 - 1 - i) default))
    (hokΔ : ∀ i, i < rP + c.2 →
      ∀ ρ : Nat → V, Sat V (pdoms ++ fdoms).reverse ρ →
        WellDenotedV V (fun j => ρ (j + (rP + c.2 - 1 - i) + 1))
          ((pdoms ++ fdoms).reverse.getD (rP + c.2 - 1 - i) default))
    {ρ₀ : Nat → V} {xs fs : List V} (hsp : SpineFit ρ₀ (pdoms ++ fdoms) (xs ++ fs))
    (hbit : pwBit φ (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ≠ 0)
    (Rv : Nat → V)
    (hR : ∀ ih ∈ R.ihs.toList, ∀ RTa : AnnotTerm,
      denoteMeta mT.acval feT.env φ (rP + c.2) (fam.recTys.getD ih.callee (.sort .zero))
        = some RTa →
      Rv ih.callee ∈ˢ interp V (consList (xs ++ fs) ρ₀) RTa)
    (hcallee : ∀ (nm : Name) (c' : Nat), ConLeche.nameIdxOf? fam.recNames nm = some c' →
      ∃ ci : ConLeche.ConstantInfo, env.find? nm = some ci ∧
        fam.rlvls.length = ci.toConstantVal.levelParams.length ∧
        ∀ ρ : Nat → V,
          interp V ρ (acval nm (Level.substFn φ ci.toConstantVal.levelParams fam.rlvls)) = Rv c')
    {as1 : List Expr} (h1 : LocList 0 (rP + c.2) as1) {A : AnnotTerm}
    (hA : denoteMeta acval env φ (rP + c.2) (R.body.instantiateList as1 0) = some A) :
    (∃ Bv : AnnotTerm,
      denoteMeta mT.acval feT.env φ (rP + c.2 + R.ihs.size) R.bodyO = some Bv ∧
      interp V (consList (xs ++ fs) ρ₀) A
        = interp V (consList (ihValsAt Rv (consList (xs ++ fs) ρ₀) R.ihs.toList
            (ihLamReads mT.acval feT.env φ fam R.fvsPref R.fvsF
              (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
              (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) R.ihs.toList))
            (consList (xs ++ fs) ρ₀)) Bv) ∧
    -- every call λ's reading is bound by the frame and its callee slot
    ∀ r, r < R.ihs.size →
      ConLeche.Term.Term.bvarsBelow (rP + c.2 + 1)
        ((ihLamReads mT.acval feT.env φ fam R.fvsPref R.fvsF
          (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
          (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) R.ihs.toList).getD r
            default).erase := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have haclT1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => haclT n ψ 1 k
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts R.hpref R.hcrest hds R.hfld hTf hTb hTc
    hCf hCb hCc
  have hframeL := frame_leaves_mem hFr hher
  have hW := walkCtx_targetRule hμ haclT hin R hle hbf hds hTf hTb hTc hCf hCb hCc hformer hRT
    hp hf hdoms hokΔ hsp Rv hR
  have hwf : TargetIhWF (ConLeche.targetFrameOf fam rP R.fvsPref R.fvsF R.fnorm
      (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))) (rP + c.2) R.ihs :=
    (targetAbstract_acc 0 _ #[] _ _ R.habs).2 (fun r hr => absurd hr (by simp))
  have hscope := fun ih (hih : ih ∈ R.ihs.toList) =>
    targetIh_scope hμ R mT.wf hle hbf hFr hher hcbF hformer (fun c' => (hRT c').1) hih
  -- the `ih` variables' list
  have hfvEq := ihs_fv_eq hwf
  have hL : FvarList (rP + c.2 + R.ihs.size) (targetFrameIh (R.fvsPref ++ R.fvsF) R.ihs) := by
    have h := fvarList_ihs hFr (R.ihs.toList.map (·.ty)) (fun t ht => by
      obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp ht
      exact wscoped_of_leaves_mem hFr _ (hscope ih hih).1)
    rw [targetFrameIh, List.reverse_append, hfvEq]
    simpa using h
  -- the residue's leaves
  have hlL : ∀ l ∈ R.bodyO.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ targetFrameIh (R.fvsPref ++ R.fvsF) R.ihs := by
    intro l hl
    rw [targetFrameIh, List.mem_reverse]
    rcases targetAbstract_out_leaves 0 _ #[] _ _ R.habs l hl with h0 | ⟨ih, hih, h0⟩
    · obtain ⟨x, hx, hlx⟩ := fvarLeaves_instantiateList hFr R.body hbf 0 l h0
      exact List.mem_append_left _ (hframeL x (List.mem_reverse.mp hx) l hlx)
    · obtain ⟨r, hr, hget⟩ := List.getElem_of_mem hih
      have hr' : r < R.ihs.size := by simpa using hr
      obtain ⟨hfv, -⟩ := hwf r hr'
      have hget' : R.ihs[r] = ih := by simpa using hget
      rw [hget'] at hfv
      rw [hfv] at h0
      simp only [Expr.fvarLeaves, List.mem_cons] at h0
      rcases h0 with rfl | h0
      · refine List.mem_append_right _ (List.mem_map.mpr ⟨ih, hih, ?_⟩)
        exact hfv
      · exact List.mem_append_left _ ((hscope ih hih).1 l h0 |> List.mem_reverse.mp)
  have hinfB := Rules.inferTypeCore_bridge R.hty
  have hbT : R.bodyO.looseBVarsBounded 0 = true := ConLeche.infer_full_bvarClosed hinfB
  have hcbe : ConstsBound feT.env R.bodyO := by
    refine infer_constsBound_of_full hinfB rfl (fun l hl => ?_)
    have h := hW.2.2.2.2.2.1 _ (hlL l hl)
    simpa using h
  have hLB : Expr.LeavesBounded R.bodyO := fun l hl => hW.2.2.2.2.1 _ (hlL l hl)
  obtain ⟨Bv, hBv⟩ := acceptedReads_of mT φ R.hty (wscoped_of_leaves_mem hL _ hlL) hbT hLB
  -- each call λ reads at the constructors' environment, scoped and bound
  have hlam : ∀ (r : Nat) (ih : ConLeche.TargetIh), R.ihs[r]? = some ih →
      ∃ Lr : AnnotTerm, denoteMeta mT.acval feT.env φ (rP + c.2 + 1)
          (targetCallLam fam R.fvsPref R.fvsF (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
            (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) = some Lr ∧
        ConstsBound feT.env (targetCallLam fam R.fvsPref R.fvsF
          (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
          (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) ∧
        ConLeche.Term.Term.bvarsBelow (rP + c.2 + 1) Lr.erase := by
    intro r ih hr
    obtain ⟨hrl, hrget⟩ := Array.getElem?_eq_some_iff.mp hr
    have hih : ih ∈ R.ihs.toList := by rw [← hrget]; exact Array.getElem_mem_toList hrl
    obtain ⟨C⟩ := R.call hih
    obtain ⟨-, -, -, hlE, -, -⟩ := hscope ih hih
    obtain ⟨hRf, hRb, hRcb, -⟩ := hRT ih.callee
    have hL1 : FvarList (rP + c.2 + 1)
        (Expr.fvar (rP + c.2) (fam.recTys.getD ih.callee (.sort .zero))
          :: (R.fvsPref ++ R.fvsF).reverse) :=
      hFr.cons _ (Expr.WScoped.of_not_hasFvar hRf)
    have hLE : Expr.LeavesBounded (targetCallLam fam R.fvsPref R.fvsF
        (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
        (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) := by
      intro l hl
      rcases List.mem_cons.mp (hlE l hl) with h0 | h0
      · injection h0 with _ h2; rw [h2]; exact hRb
      · exact hlbF _ (List.mem_reverse.mp h0)
    have hbC := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge C.hcall)
    obtain ⟨Lr, hLr⟩ := acceptedReads_of mT φ C.hcall
      (wscoped_of_leaves_mem hL1 _ hlE) hbC hLE
    have hcbLam : ConstsBound feT.env (targetCallLam fam R.fvsPref R.fvsF
        (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
        (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) := by
      refine infer_constsBound_of_full (Rules.inferTypeCore_bridge C.hcall) rfl (fun l hl => ?_)
      rcases List.mem_cons.mp (hlE l hl) with h0 | h0
      · injection h0 with _ h2; rw [h2]; exact hRcb
      · have := hcbF _ (List.mem_reverse.mp h0); simpa using this
    exact ⟨Lr, hLr, hcbLam,
      bvarsBelow_of_reading (m := mT) (wscoped_of_leaves_mem hL1 _ hlE) hbC hLr⟩
  refine ⟨⟨Bv, hBv, ?_⟩, fun r hr => ?_⟩
  rotate_left
  · obtain ⟨Lr, hLr, -, hb⟩ := hlam r R.ihs[r] (by simp [hr])
    have e2 : (ihLamReads mT.acval feT.env φ fam R.fvsPref R.fvsF
        (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
        (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) R.ihs.toList).getD r default
        = Lr := by
      rw [ihLamReads, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem hr]
      simp [hLr]
    rw [e2]; exact hb
  -- the `ih` values are the λs' readings, transported to the consed environment
  have hihv : ∀ (r : Nat) (ih : ConLeche.TargetIh), R.ihs[r]? = some ih →
      ∃ L : AnnotTerm, denoteMeta acval env φ (rP + c.2 + 1)
          (targetCallE (ConLeche.targetFrameOf fam rP R.fvsPref R.fvsF R.fnorm
            (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))) (rP + c.2)
            (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) = some L ∧
        (ihValsAt Rv (consList (xs ++ fs) ρ₀) R.ihs.toList
            (ihLamReads mT.acval feT.env φ fam R.fvsPref R.fvsF
              (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
              (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) R.ihs.toList)).getD r pt
          = interp V (cons (Rv ih.callee) (consList (xs ++ fs) ρ₀)) L := by
    intro r ih hr
    obtain ⟨hrl, -⟩ := Array.getElem?_eq_some_iff.mp hr
    obtain ⟨Lr, hLr, hcbLam, -⟩ := hlam r ih hr
    refine ⟨Lr, hmono _ _ _ hcbLam hLr, ?_⟩
    rw [ihValsAt, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by simpa using hrl)]
    simp only [Option.map_some, Option.getD_some]
    have e1 : (R.ihs.toList.getD r default) = ih := by
      rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, hr]; rfl
    have e2 : (ihLamReads mT.acval feT.env φ fam R.fvsPref R.fvsF
        (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
        (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) R.ihs.toList).getD r default
        = Lr := by
      have hLr' : denoteMeta mT.acval feT.env φ (rP + c.2 + 1) (targetCallLam fam R.fvsPref
          R.fvsF (R.fnorm.map fun t => t.piBinders.1) (rP + c.2)
          (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large)) ih) = some Lr := hLr
      rw [ihLamReads, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList, hr]
      simp [hLr']
    rw [e1, e2]
  have hteles : ∀ (r : Nat) (ih : ConLeche.TargetIh), R.ihs[r]? = some ih →
      ∀ t ∈ ((ConLeche.targetFrameOf fam rP R.fvsPref R.fvsF R.fnorm
          (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))).teles.getD ih.field []).map
          (·.1),
        ∀ l ∈ t.fvarLeaves, l.1 < rP + c.2 := by
    intro r ih hr t ht l hl
    obtain ⟨hrl, hrget⟩ := Array.getElem?_eq_some_iff.mp hr
    have hih : ih ∈ R.ihs.toList := by rw [← hrget]; exact Array.getElem_mem_toList hrl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact leaf_lt_of_mem hFr (fun l' hl' => List.mem_reverse.mpr
      ((hscope ih hih).2.2.2.2.2 b hb l' hl')) l hl
  exact targetRuleBodyEq (acval := acval) (env := env) (φ := φ) hacl haclT1 hin hproj hmono
    R.habs hbf hFr hbit (by simp [ihValsAt]) hle
    (fun x hx => openPisAtFvars_fvars_closed R.hpref x hx)
    (fun x hx => openPisAtFvars_fvars_closed R.hfld x hx)
    hcallee hteles hihv hL hW hlL hbT hcbe ⟨_, hinfB⟩ h1 hA hBv

end ConLeche.Model
