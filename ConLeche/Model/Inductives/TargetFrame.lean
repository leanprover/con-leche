module

public import ConLeche.Model.Inductives.TargetIhSlot
public import ConLeche.Model.Inductives.BlockRuleRun
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Model.Inductives.BlockRecTyShapeRun

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

/-- `instPisWith` is `instPisAt`'s residual. -/
theorem instPisWith_eq_instPisAt :
    ∀ (as : List Expr) (e : Expr), ConLeche.instPisWith as e = (Expr.instPisAt as e).map (·.2)
  | [], e => by simp [ConLeche.instPisWith, Expr.instPisAt]
  | a :: as, e => by
    cases e with
    | forallE dom body bm =>
      simp only [ConLeche.instPisWith, Expr.instPisAt, Option.map_map]
      rw [instPisWith_eq_instPisAt as]
      cases Expr.instPisAt as (body.instantiate1 a) <;> rfl
    | _ => simp [ConLeche.instPisWith, Expr.instPisAt]

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
    (fun ih hih => targetIh_scope hμ R mT.wf hle hbf hFr hher hcbF hformer
      (fun c' => (hRT c').1) hih)
    (fun ih _ => hRT ih.callee) Rv hR
  have e : targetFrameIh (R.fvsPref ++ R.fvsF) R.ihs
      = (R.ihs.toList.map (·.fv)).reverse ++ (R.fvsPref ++ R.fvsF).reverse := by
    rw [targetFrameIh, List.reverse_append]
  rw [e]
  exact h.2

end ConLeche.Model
