module

import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Inductives.BlockShapeInv
public import ConLeche.Verify.Cached.TargetRecC
public import ConLeche.Kernel.Inductives.GenRec
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Cached.WalkersC
public import ConLeche.Verify.Cached.NestPosC
public import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Cached.DeclPushes
import ConLeche.Verify.Cached.BlockOverlay
public import ConLeche.Verify.Inductives.StreamRecsInv
public import ConLeche.Verify.Inductives.TargetAuxFire

public section

/-!
# The cached recursor stage, bridged: the GENERATED stage

The generated recursor stage `genRecCheck`
(`ConLeche/Kernel/Inductives/GenRec.lean`) is written once over
`ShadowOps`: the pure install runs it at `ShadowOps.ofOps`
(`checkBlockRec`), the cached driver at `shadowOpsC` (`checkBlockTailS`).
This file proves the cached run reproduced by the pure fueled one
(`genRecCheckS_spec`, `genRecCheckS_run`), reusing the class kit's
per-operation simulations (`TargetRecC.lean`), the pass's classes
(`checkBlockClassesS_spec`), and with them the cached uniform install
(`checkBlockPassS_run`, `checkBlockTailS_run`, `checkBlockKS_run`) and
the `.indDecl` dispatch (`checkModeledOrNativeSF_run`).  The stages are
`Std.WP` triples proved by `vcgen` and `grind`, as the positivity walk's
(`NestPosC.lean`); the rule stage runs from and to a flushed state
(`CSOKAll`); the check's assembly reads the triples back as runs
(`triple_iff_run`).

Scoping, per cached operation:
* the stream's recursor types and the GENERATED types are closed by
  `checkConstantValF` itself; the comparison runs on two closed terms;
* the classes' parameters are the pre-pass's reading of the stream's
  RAW recursor types, moved to the canonical parameters and kept below
  them by `classKeyOf`'s guard (every free variable left is a canonical
  parameter, `replaceFVars_WScoped_of_below`, `classKeyOf_ws`) — so
  every class is scoped by the parameter openers
  (`TargetMajScoped`), which is all the class match (`targetMajorNfs`,
  `targetK53`) and the pin typing need;
* each generated RULE is closed by `classRuleOk`'s own guard.
-/

set_option linter.unusedSimpArgs false
set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open Expr
open Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## 1. The pre-pass's reading -/

/-- The pre-pass's minor premise reading returns a minor premise. -/
theorem classReadMinor_minor {np : Nat} {motPos : List Nat} {d : Nat} {dom : Expr}
    {slot : ClassSlot} (h : classReadMinor np motPos d dom = some slot) :
    ∃ c C ihs, slot = .minor c C ihs := by
  unfold classReadMinor at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, -, h⟩ := h
  split at h
  · simp only [Option.bind_eq_some_iff] at h
    obtain ⟨c, -, x, -, h⟩ := h
    split at h
    · exact ⟨_, _, _, (Option.some.inj h).symm⟩
    · exact nomatch h
  · exact nomatch h

/-! ## 2. The stages, simulated -/

section Sims

variable {env : Env}

/-- `classMinorSlot` is operation-free. -/
theorem classMinorSlotS_spec {rd : ClassRead} {c : Nat} {C : Name} {s₀ : CState}
    (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄ classMinorSlot (m := CheckCM) rd c C
    ⦃fun v s' => CSOK mode false env s' ∧ Runs (classMinorSlot (m := FueledM) rd c C) v; ⊤⦄ := by
  sym only [conleche_grind, classMinorSlot.eq_1] =>
    vcgen [classMinorSlot] <;> finish

/-- `classFieldsOf` is operation-free. -/
theorem classFieldsOfS_spec {p : BlockShape} {ctor : Name} {ihs : List (Nat × Nat)} :
    ∀ (i : Nat) (fs : List Expr) {s₀ : CState}, CSOK mode false env s₀ →
      ⦃fun s => s = s₀⦄ classFieldsOf (m := CheckCM) p ctor ihs i fs
      ⦃fun v s' => CSOK mode false env s' ∧ Runs (classFieldsOf (m := FueledM) p ctor ihs i fs) v;
        ⊤⦄ := by
  intro i fs
  induction fs generalizing i with
  | nil =>
    intro _ hs
    sym only [conleche_grind, classFieldsOf.eq_1] =>
      vcgen [classFieldsOf] <;> finish
  | cons f fs ih =>
    intro _ hs
    sym only [conleche_grind, classFieldsOf.eq_2] =>
      vcgen [classFieldsOf, ih (i + 1)] <;> finish

/-- `classFormerTy` at the cached operations simulates its fueled original. -/
theorem classFormerTyS_spec (henv : EnvWF env) {formers : List ConstantVal} {M : TargetMajor}
    {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ classFormerTy (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) formers M
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (classFormerTy (fueledOpsM .verified) (mkFEnv env) formers M) v; ⊤⦄ := by
  sym only [conleche_grind, classFormerTy.eq_1, → find_closed henv] =>
    vcgen [classFormerTy, familyTelescopeF_spec henv] <;> finish

/-- `List.mapM`'s loop, simulated elementwise. -/
theorem mapMLoopS_spec {α β : Type} {f : α → CheckCM β} {g : α → FueledM β}
    (hf : ∀ a {s₀ : CState}, CSOK mode false env s₀ →
      ⦃fun s => s = s₀⦄ f a ⦃fun v s' => CSOK mode false env s' ∧ Runs (g a) v; ⊤⦄) :
    ∀ (l : List α) (bs : List β) {s₀ : CState}, CSOK mode false env s₀ →
      ⦃fun s => s = s₀⦄ List.mapM.loop f l bs
      ⦃fun v s' => CSOK mode false env s' ∧ Runs (List.mapM.loop g l bs) v; ⊤⦄ := by
  intro l
  induction l with
  | nil =>
    intro bs _ hs
    sym only [conleche_grind, List.mapM.loop.eq_1] =>
      vcgen [List.mapM.loop] <;> finish
  | cons a l ih =>
    intro bs _ hs
    sym only [conleche_grind, List.mapM.loop.eq_2] =>
      vcgen [List.mapM.loop, hf a, ih] <;> finish

/-- The classes' formers (`Ms.mapM classFormerTy`). -/
theorem classFormerTysS_spec (henv : EnvWF env) {formers : List ConstantVal} (Ms : List TargetMajor)
    {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ Ms.mapM (classFormerTy (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) formers)
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (Ms.mapM (classFormerTy (fueledOpsM .verified) (mkFEnv env) formers)) v; ⊤⦄ :=
  mapMLoopS_spec (fun _ _ hs => classFormerTyS_spec henv hs) Ms [] hs

/-- A constant's type is closed. -/
@[expose] def TyClosed (cv : ConstantVal) : Prop := WScoped 0 cv.type

@[conleche_grind =] theorem TyClosed.eq (cv : ConstantVal) : TyClosed cv = WScoped 0 cv.type :=
  rfl

/-- `checkConstantValS_spec` at the index (`checkConstantValF`). -/
theorem checkConstantValFS_spec (henv : EnvWF env)
    {cv : ConstantVal} {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ checkConstantValF (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) cv
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (checkConstantValF (fueledOpsM .verified) (mkFEnv env) cv) v ∧ TyClosed cv; ⊤⦄ := by
  rw [checkConstantValF_eq, checkConstantValF_eq]
  exact checkConstantValS_spec henv hs

/-- The stream's recursor constants, checked: each closed. -/
theorem classStreamRecsS_spec (henv : EnvWF env) :
    ∀ (recs : List RecShape) {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄ classStreamRecs (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) recs
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (classStreamRecs (fueledOpsM .verified) (mkFEnv env) recs) v ∧ ListAll TyClosed v; ⊤⦄ := by
  intro recs
  induction recs with
  | nil =>
    intro _ hs
    sym only [conleche_grind, classStreamRecs.eq_1] =>
      vcgen [classStreamRecs] <;> finish
  | cons rc rcs ih =>
    intro _ hs
    sym only [conleche_grind, classStreamRecs.eq_2] =>
      vcgen [classStreamRecs, checkConstantValFS_spec henv, ih] <;> finish

/-- **What a class checked as a major is** (`targetMajorOf` at the class
application; the twin of `TargetRecC`'s shape lemma): a member at the
openers' parameters, or an outside inductive whose parameters are the
class's own, below the parameters. -/
@[expose] def ClassShape (p : BlockShape) (pfvs fvs : List Expr) (mty : Expr)
    (M : TargetMajor) : Prop :=
  M.pfvs = pfvs ∧ ((∃ t, M.member = some t ∧ M.ds = fvs.take p.nP) ∨
    (M.member = none ∧ M.ds.length = M.nPc ∧
      ∀ x ∈ M.ds, x ∈ mty.getAppArgs ∧ x.bvarB = 0 ∧ x.fvarB ≤ p.nP))

private theorem classMajorOf_shape (ops : CheckerOps CheckCM) (fe : FEnv) (p : BlockShape) (pfvs fvs : List Expr) (mty : Expr) :
    ∀ s M s', targetMajorOf ops fe p pfvs fvs mty s = .ok (M, s') →
      ClassShape p pfvs fvs mty M := by
  show Yields _ _
  unfold targetMajorOf ClassShape
  dsimp only
  split
  · split
    · refine Yields.bind' Yields.unwrapOr fun ms _ => ?_
      split
      · exact Yields.pure ⟨rfl, Or.inl ⟨_, rfl, rfl⟩⟩
      · exact Yields.ofThrowBind
    · repeat' (first
        | exact Yields.ofThrow
        | exact Yields.ofThrowBind
        | (refine Yields.bind fun _ => ?_)
        | split)
      all_goals first
        | (simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at *
           have hck := (by assumption : _ ∧ ∀ y ∈ List.take _ mty.getAppArgs,
             y.bvarB = 0 ∧ y.fvarB ≤ p.nP)
           exact Yields.pure ⟨rfl, Or.inr ⟨rfl, hck.1,
             fun x hx => ⟨List.mem_of_mem_take hx, hck.2 x hx⟩⟩⟩)
  · exact Yields.ofThrow

/-- `targetMajorOfS_spec` with the class's shape. -/
theorem classMajorOfS_spec (henv : EnvWF env) {p : BlockShape}
    {pfvs : List Expr} {mty : Expr} {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ targetMajorOf (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) p pfvs
      pfvs mty
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (targetMajorOf (fueledOpsM .verified) (mkFEnv env) p pfvs pfvs mty) v ∧
      ClassShape p pfvs pfvs mty v; ⊤⦄ :=
  triple_iff_run.mpr fun v' s' hr => by
    obtain ⟨hs', hR⟩ := triple_iff_run.mp (targetMajorOfS_spec henv hs) v' s' hr
    exact ⟨hs', hR, classMajorOf_shape _ (mkFEnv env) p pfvs pfvs mty s₀ v' s' hr⟩

/-- A class checked as a major, scoped: its openers are the parameter
openers `pfvs`, its parameters scoped by them, an outside class's below
the parameters. -/
@[expose] def ClassMajScoped (nP : Nat) (M : TargetMajor) : Prop :=
  TargetMajScoped M ∧ ClassOutParams nP M ∧ M.pfvs.length = nP

/-- A class key's parameters are scoped at `nP`. -/
@[expose] def KeyWS (nP : Nat) (k : ClassKey) : Prop := AllWS nP k.ds

/-- What a class of the shape `targetMajorOf` checks is, scoped. -/
theorem classMajScoped_of_shape {p : BlockShape} {pfvs : List Expr} (hpl : pfvs.length = p.nP)
    (hp : AllWS p.nP pfvs) {key : ClassKey} (hk : KeyWS p.nP key) {M : TargetMajor}
    (h : ClassShape p pfvs pfvs (Expr.mkAppN (.const key.ind key.lvls) key.ds) M) :
    ClassMajScoped p.nP M := by
  obtain ⟨hMpf, hMsh⟩ := h
  have hdsN : ClassOutParams p.nP M := by
    intro hMn
    rcases hMsh with ⟨t, hmt, -⟩ | ⟨-, hl, hall⟩
    · rw [hMn] at hmt; exact nomatch hmt
    · exact ⟨hl, fun x hx => (hall x hx).2⟩
  have hds : ∀ x ∈ M.ds, WScoped p.nP x := by
    intro x hx
    rcases hMsh with ⟨t, -, hMds⟩ | ⟨-, -, hall⟩
    · rw [hMds] at hx
      exact hp x (List.mem_of_mem_take hx)
    · obtain ⟨hxa, -, -⟩ := hall x hx
      rw [Expr.getAppArgs_mkAppN] at hxa
      simp only [Expr.getAppArgs, List.nil_append] at hxa
      exact hk x hxa
  refine ⟨⟨?_, ?_⟩, hdsN, by rw [hMpf, hpl]⟩
  · rw [hMpf, hpl]; exact hp
  · rw [hMpf, hpl]; exact hds

/-- An outside class's parameters are scoped at `rP` (what its pin
typing needs). -/
@[expose] def PinsWS (rP : Nat) (M : TargetMajor) : Prop := M.member = none → AllWS rP M.ds

theorem pinsWS_of_classMajScoped {nP : Nat} {M : TargetMajor} (h : ClassMajScoped nP M) :
    PinsWS nP M := fun _ => h.2.2 ▸ h.1.2

/-- `targetMajorPinsS_spec` at a scoped class. -/
theorem targetMajorPinsS_specF (henv : EnvWF env) {rP : Nat}
    {M : TargetMajor} (hds : PinsWS rP M) {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ targetMajorPins (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) rP M
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (targetMajorPins (fueledOpsM .verified) (mkFEnv env) rP M) v; ⊤⦄ :=
  targetMajorPinsS_spec henv hds hs

/-- `blockNestCtx` at the shared operations, its lookups the formers'
environment `env₁`, the state the constructors' environment's: the same
value, the canonical parameters scoped at the parameter count. -/
theorem blockNestCtxS_spec₂ {env₁ env₂ : Env} (henv₁ : EnvWF env₁) (p : BlockShape) (hM : ∀ ms ∈ p.members, ms.cvT.type.hasFvar = false)
    (hT : ∀ cv ∈ p.formers, WScoped 0 cv.type) {s₀ : CState}
    (hs : CSOK mode false env₂ s₀) :
    ⦃fun s => s = s₀⦄ blockNestCtx (m := CheckCM) p env₁.find?
    ⦃fun v s' => CSOK mode false env₂ s' ∧ Runs (blockNestCtx (m := FueledM) p env₁.find?) v ∧
      NestCtxOk v.1 ∧ HolesOk (v.1.hiAt 0) v.2 ∧ AllWS p.nP v.1.params ∧
      v.1.params.length = v.1.nP ∧ nestHoles v.1 = some v.2 ∧ v.1.nP = p.nP; ⊤⦄ := by
  -- `ematch`: one E-matching round per pure-side bind (`Runs.pure_bind_eq`), and the
  -- context's facts after the last one
  sym only [conleche_grind, blockNestCtx.eq_1, unwrapOr.eq_1, → blockNestCtx_ok henv₁ hM hT,
      → holesOk_nestHoles] =>
    vcgen [blockNestCtx, unwrapOr] <;> finish (ematch := 8)

/-- **The classes, each checked as a major**: every class scoped. -/
theorem classMajorsS_spec (henv : EnvWF env)
    {p : BlockShape} {pfvs : List Expr}
    (hpl : pfvs.length = p.nP) (hp : AllWS p.nP pfvs) :
    ∀ (keys : List ClassKey) {s₀ : CState}, CSOK .verified false env s₀ → ListAll (KeyWS p.nP) keys →
      ⦃fun s => s = s₀⦄
        classMajors (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) p pfvs keys
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (classMajors (fueledOpsM .verified) (mkFEnv env) p pfvs keys) v ∧
        ListAll (ClassMajScoped p.nP) v; ⊤⦄ := by
  intro keys
  induction keys with
  | nil =>
    intro _ hs _
    sym only [conleche_grind, classMajors.eq_1] =>
      vcgen [classMajors] <;> finish
  | cons key keys ih =>
    intro _ hs hk
    sym only [conleche_grind, classMajors.eq_2, mkFEnv_env, → classMajScoped_of_shape hpl hp,
        → pinsWS_of_classMajScoped] =>
      vcgen [classMajors, classMajorOfS_spec henv, targetMajorPinsS_specF henv,
        ih] <;> finish

/-- **One class key made checkable**: its parameters scoped at
the parameter count (the guard keeps every free variable a canonical
parameter). -/
theorem classKeyOf_ws {nP : Nat} {params : List Expr} (hpl : params.length = nP)
    (hp : AllWS nP params) {k : ClassKey}
    (hg : ((classKeyCanon params k).ds.all fun x => x.bvarB == 0 && decide (x.fvarB ≤ nP))
      = true) : KeyWS nP (classKeyCanon params k) := by
  intro x hx
  have hx' := List.all_eq_true.mp hg x hx
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hx'
  simp only [classKeyCanon, List.mem_map] at hx
  obtain ⟨y, -, rfl⟩ := hx
  exact ConLeche.replaceFVars_WScoped_of_below
    (fun i r hr => hp r (List.mem_of_getElem? hr))
    (fun i hi => by simp [hpl, hi]) y (Expr.fvarB_le hx'.2)

/-- The class keys made checkable, one after another. -/
theorem classKeysLoopS_spec {nP : Nat} {params : List Expr} (hpl : params.length = nP)
    (hp : AllWS nP params) :
    ∀ (l bs : List ClassKey) {s₀ : CState}, CSOK mode false env s₀ → ListAll (KeyWS nP) bs →
      ⦃fun s => s = s₀⦄ List.mapM.loop (classKeyOf (m := CheckCM) nP params) l bs
      ⦃fun v s' => CSOK mode false env s' ∧
        Runs (List.mapM.loop (classKeyOf (m := FueledM) nP params) l bs) v ∧
        ListAll (KeyWS nP) v; ⊤⦄ := by
  intro l
  induction l with
  | nil =>
    intro bs _ hs hbs
    sym only [conleche_grind, List.mapM.loop.eq_1] =>
      vcgen [List.mapM.loop] <;> finish
  | cons a l ih =>
    intro bs _ hs hbs
    sym only [conleche_grind, List.mapM.loop.eq_2, classKeyOf.eq_1, → classKeyOf_ws hpl hp] =>
      vcgen [List.mapM.loop, classKeyOf, ih] <;> finish

/-- **The classes, read and checked** (the pass's `checkBlockClasses`):
every class scoped. -/
theorem checkBlockClassesS_spec (henv : EnvWF env)
    {p : BlockShape} {params : List Expr} (hpl : params.length = p.nP)
    (hp : AllWS p.nP params)
    {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄
      checkBlockClasses (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) p params
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (checkBlockClasses (fueledOpsM .verified) (mkFEnv env) p params) v ∧
      ListAll (ClassMajScoped p.nP) v.2; ⊤⦄ := by
  -- `ematch`: the pure side's `mapM` meets the loop's answer one round after its unfolding
  sym only [conleche_grind, checkBlockClasses.eq_1, unwrapOr.eq_1, List.mapM.eq_1] =>
    vcgen [checkBlockClasses, unwrapOr, List.mapM,
      classKeysLoopS_spec (mode := .verified) (env := env) hpl hp,
      classMajorsS_spec henv hpl hp] <;> finish (ematch := 8)

@[conleche_grind =] theorem TargetMajScoped.nfs_eq (M : TargetMajor) (es : List NestCtorNf) :
    TargetMajScoped { M with nfs := es } = TargetMajScoped M := rfl

/-- `targetMajorNfsS_spec` at a scoped class. -/
theorem classNfsS_spec (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : AllWS 0 formerTys) {M : TargetMajor}
    (hM : TargetMajScoped M) (es : List NestCtorNf) {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄
      targetMajorNfs (sharedOpsC .verified (mkFEnv env)) env p formerTys M.pfvs M.lvls M.ds M.ctors es
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (targetMajorNfs (fueledOpsM .verified) env p formerTys M.pfvs M.lvls M.ds M.ctors es) v;
      ⊤⦄ :=
  targetMajorNfsS_spec henv hformer hM.1 es hs

/-- Every class's table entries: the classes stay scoped. -/
theorem classesNfsS_spec (henv : EnvWF env) {p : BlockShape}
    {formerTys : List Expr} (hformer : AllWS 0 formerTys) {tbl : List NestCtorNf} :
    ∀ (Ms : List TargetMajor) {s₀ : CState}, CSOK .verified false env s₀ → ListAll TargetMajScoped Ms →
      ⦃fun s => s = s₀⦄ classesNfs (sharedOpsC .verified (mkFEnv env)) env p formerTys tbl Ms
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (classesNfs (fueledOpsM .verified) env p formerTys tbl Ms) v ∧
        ListAll TargetMajScoped v; ⊤⦄ := by
  intro Ms
  induction Ms with
  | nil =>
    intro _ hs _
    sym only [conleche_grind, classesNfs.eq_1] =>
      vcgen [classesNfs] <;> finish
  | cons M Ms ih =>
    intro _ hs hsc
    sym only [conleche_grind, classesNfs.eq_2] =>
      vcgen [classesNfs, classNfsS_spec henv hformer, ih] <;> finish

/-- Node agreement at one recursive field, at every entry. -/
theorem classNodesAgreeS_spec (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : AllWS 0 formerTys)
    {Mc : TargetMajor} (hMc : TargetMajScoped Mc) {tele : List Expr}
    {leaf : Expr} {fvs : List Expr} {i : Nat} {ctor : Name} :
    ∀ (es : List NestCtorNf) {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄
        classNodesAgree (sharedOpsC .verified (mkFEnv env)) env p formerTys Mc tele leaf fvs i ctor es
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (classNodesAgree (fueledOpsM .verified) env p formerTys Mc tele leaf fvs i ctor es) v;
        ⊤⦄ := by
  intro es
  induction es with
  | nil =>
    intro _ hs
    sym only [conleche_grind, classNodesAgree.eq_1] =>
      vcgen [classNodesAgree] <;> finish
  | cons e es ih =>
    intro _ hs
    sym only [conleche_grind, classNodesAgree.eq_2] =>
      vcgen [classNodesAgree, targetK53S_spec henv hformer hMc, ih] <;> finish

theorem targetMajScoped_getD {l : List TargetMajor} (h : ListAll TargetMajScoped l) (i : Nat) :
    TargetMajScoped (l.getD i default) :=
  TargetMajScoped.getD h i

/-- Node agreement at every recursive field of the datum. -/
theorem classFieldsAgreeS_spec (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : AllWS 0 formerTys)
    {Ms : List TargetMajor} (hMs : ListAll TargetMajScoped Ms) {fvs : List Expr}
    {ctor : Name} {E : List NestCtorNf} :
    ∀ (i : Nat) (ks : List ClassField) {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄
        classFieldsAgree (sharedOpsC .verified (mkFEnv env)) env p formerTys Ms fvs ctor E i ks
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (classFieldsAgree (fueledOpsM .verified) env p formerTys Ms fvs ctor E i ks) v; ⊤⦄ := by
  intro i ks
  induction ks generalizing i with
  | nil =>
    intro _ hs
    sym only [conleche_grind, classFieldsAgree.eq_1] =>
      vcgen [classFieldsAgree] <;> finish
  | cons k ks ih =>
    cases k with
    | ordinary =>
      intro _ hs
      sym only [conleche_grind, classFieldsAgree.eq_2] =>
        vcgen [classFieldsAgree, ih (i + 1)] <;> finish
    | recursive t tele =>
      intro _ hs
      sym only [conleche_grind, classFieldsAgree.eq_3, unwrapOr.eq_1] =>
        vcgen [classFieldsAgree, unwrapOr,
          classNodesAgreeS_spec henv hformer (targetMajScoped_getD hMs t),
          ih (i + 1)] <;> finish

/-- One constructor of a class, read for the generator. -/
theorem classCtorOfS_spec (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : AllWS 0 formerTys)
    {rd : ClassRead} {Ms : List TargetMajor} (hMs : ListAll TargetMajScoped Ms) {c : Nat}
    {ctor : ConstantVal × Nat} {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ classCtorOf (sharedOpsC .verified (mkFEnv env)) env p formerTys rd Ms c ctor
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (classCtorOf (fueledOpsM .verified) env p formerTys rd Ms c ctor) v; ⊤⦄ := by
  -- `gen`: E-matching evaluates the pure side bind by bind (`Runs.pure_bind_eq`), one
  -- generation per bind, through seven binds
  sym only [conleche_grind, classCtorOf.eq_1, unwrapOr.eq_1] =>
    vcgen [classCtorOf, unwrapOr, classMinorSlotS_spec (mode := .verified) (env := env),
      classFieldsOfS_spec (mode := .verified) (env := env),
      classFieldsAgreeS_spec henv hformer hMs] <;> finish (gen := 12)

theorem classCtorsOfS_spec (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : AllWS 0 formerTys)
    {rd : ClassRead} {Ms : List TargetMajor} (hMs : ListAll TargetMajScoped Ms) {c : Nat} :
    ∀ (cs : List (ConstantVal × Nat)) {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄ classCtorsOf (sharedOpsC .verified (mkFEnv env)) env p formerTys rd Ms c cs
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (classCtorsOf (fueledOpsM .verified) env p formerTys rd Ms c cs) v; ⊤⦄ := by
  intro cs
  induction cs with
  | nil =>
    intro _ hs
    sym only [conleche_grind, classCtorsOf.eq_1] =>
      vcgen [classCtorsOf] <;> finish
  | cons ctor cs ih =>
    intro _ hs
    sym only [conleche_grind, classCtorsOf.eq_2] =>
      vcgen [classCtorsOf, classCtorOfS_spec henv hformer hMs, ih] <;> finish

theorem classesCtorsS_spec (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : AllWS 0 formerTys)
    {rd : ClassRead} {Ms : List TargetMajor} (hMs : ListAll TargetMajScoped Ms) :
    ∀ (c : Nat) (l : List TargetMajor) {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄ classesCtors (sharedOpsC .verified (mkFEnv env)) env p formerTys rd Ms c l
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (classesCtors (fueledOpsM .verified) env p formerTys rd Ms c l) v; ⊤⦄ := by
  intro c l
  induction l generalizing c with
  | nil =>
    intro _ hs
    sym only [conleche_grind, classesCtors.eq_1] =>
      vcgen [classesCtors] <;> finish
  | cons M rest ih =>
    intro _ hs
    sym only [conleche_grind, classesCtors.eq_2] =>
      vcgen [classesCtors, classCtorsOfS_spec henv hformer hMs, ih (c + 1)] <;> finish

theorem tyClosed_of_not_hasFvar {cv : ConstantVal} (h : cv.type.hasFvar = false) :
    TyClosed cv :=
  WScoped.of_not_hasFvar h

/-- `inferS_spec` at the index's environment. -/
theorem inferS_specF (henv : EnvWF env) {d : Nat}
    {e : Expr} {s₀ : CState} (hs : CSOK .verified false env s₀) (hw : WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC .verified (mkFEnv env)).inferType (mkFEnv env).env d e
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).inferType (mkFEnv env).env d e) v
        ∧
      WScoped d v; ⊤⦄ :=
  inferS_spec henv hs hw

/-- `sortS_spec` at the index's environment. -/
theorem sortS_specF (henv : EnvWF env) {d : Nat}
    {e : Expr} {s₀ : CState} (hs : CSOK .verified false env s₀) (hw : WScoped d e) :
    ⦃fun s => s = s₀⦄ (sharedOpsC .verified (mkFEnv env)).ensureSort (mkFEnv env).env d e
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs ((fueledOpsM .verified).ensureSort (mkFEnv env).env d e) v; ⊤⦄ :=
  sortS_spec henv hs hw

/-- **A generated constant, checked** (`classConstOk`): the cached twin
of `checkConstantValS_spec` for a generated constant — the checked
constant's type is well-scoped. -/
theorem classConstOkS_spec (henv : EnvWF env)
    {cv : ConstantVal} {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ classConstOk (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) cv
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (classConstOk (fueledOpsM .verified) (mkFEnv env) cv) v ∧ TyClosed cv; ⊤⦄ := by
  sym only [conleche_grind, classConstOk.eq_1, mkFEnv_env, → tyClosed_of_not_hasFvar] =>
    vcgen [classConstOk, inferS_specF henv, sortS_specF henv] <;> finish

/-- `defeqS_spec` at the index's environment. -/
theorem defeqS_specF (henv : EnvWF env) {d : Nat} {a b : Expr}
    {s₀ : CState} (hs : CSOK .verified false env s₀) (hwa : WScoped d a) (hwb : WScoped d b) :
    ⦃fun s => s = s₀⦄ (sharedOpsC .verified (mkFEnv env)).isDefEq (mkFEnv env).env d a b
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs ((fueledOpsM .verified).isDefEq (mkFEnv env).env d a b) v;
      ⊤⦄ :=
  defeqS_spec henv hs hwa hwb

/-- **The check of a generated recursor type**: the checked constant is
closed. -/
theorem classRecTyCheckS_spec (henv : EnvWF env)
    {cvRi cvG : ConstantVal} (hRi : TyClosed cvRi) {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ classRecTyCheck (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) cvRi cvG
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (classRecTyCheck (fueledOpsM .verified) (mkFEnv env) cvRi cvG) v ∧ TyClosed cvG; ⊤⦄ := by
  sym only [conleche_grind, classRecTyCheck.eq_1, mkFEnv_env] =>
    vcgen [classRecTyCheck, classConstOkS_spec henv hs, defeqS_specF henv] <;> finish

/-- **One recursor's generated type, checked and compared**: the stored
constant is closed. -/
theorem classRecTyOkS_spec (henv : EnvWF env)
    {g : ClassGen} {k : Nat} {rc : RecShape} {cvRi : ConstantVal} {c : Nat}
    (hRi : TyClosed cvRi) {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ classRecTyOk (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) g k rc cvRi c
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (classRecTyOk (fueledOpsM .verified) (mkFEnv env) g k rc cvRi c) v ∧ TyClosed v; ⊤⦄ := by
  sym only [conleche_grind, classRecTyOk.eq_1, unwrapOr.eq_1, mkFEnv_env] =>
    vcgen [classRecTyOk, unwrapOr, classRecTyCheckS_spec henv hRi hs] <;> finish

theorem classRecTysOk_nil_left {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (ops : CheckerOps m) (fe : FEnv) (g : ClassGen) (k : Nat) (cvs : List ConstantVal)
    (cls : List Nat) : classRecTysOk ops fe g k [] cvs cls = pure [] := rfl

theorem classRecTysOk_short₁ {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (ops : CheckerOps m) (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (rcs : List RecShape) (cls : List Nat) :
    classRecTysOk ops fe g k (rc :: rcs) [] cls =
      throw (.internal "generated recursor: recursor list") := by
  cases cls <;> rfl

theorem classRecTysOk_short₂ {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (ops : CheckerOps m) (fe : FEnv) (g : ClassGen) (k : Nat) (rc : RecShape)
    (rcs : List RecShape) (cv : ConstantVal) (cvs : List ConstantVal) :
    classRecTysOk ops fe g k (rc :: rcs) (cv :: cvs) [] =
      throw (.internal "generated recursor: recursor list") := rfl

theorem classRecTysOkS_spec (henv : EnvWF env)
    {g : ClassGen} {k : Nat} :
    ∀ (recs : List RecShape) (cvs : List ConstantVal) (cls : List Nat) {s₀ : CState},
      CSOK .verified false env s₀ → ListAll TyClosed cvs →
      ⦃fun s => s = s₀⦄
        classRecTysOk (sharedOpsC .verified (mkFEnv env)) (mkFEnv env) g k recs cvs cls
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (classRecTysOk (fueledOpsM .verified) (mkFEnv env) g k recs cvs cls) v; ⊤⦄ := by
  intro recs
  induction recs with
  | nil =>
    intro cvs cls _ hs _
    sym only [conleche_grind, classRecTysOk_nil_left] =>
      vcgen [classRecTysOk_nil_left] <;> finish
  | cons rc rcs ih =>
    intro cvs cls
    cases cvs with
    | nil =>
      intro _ hs _
      sym only [conleche_grind, classRecTysOk_short₁] =>
        vcgen [classRecTysOk_short₁] <;> finish
    | cons cvRi cvs =>
      cases cls with
      | nil =>
        intro _ hs _
        sym only [conleche_grind, classRecTysOk_short₂] =>
          vcgen [classRecTysOk_short₂] <;> finish
      | cons c cs =>
        intro _ hs hw
        sym only [conleche_grind, classRecTysOk.eq_1] =>
          vcgen [classRecTysOk, classRecTyOkS_spec henv, ih cvs cs] <;> finish

end Sims

/-! ### The rule stage: two environments, one state

One rule infers at the rule-less recursors' environment and the rest
reads the constructors'; `sharedOpsRuleR` flushes at both transitions,
so the stage's triples run from and to a FLUSHED state (`CSOKAll`). -/

/-- A FLUSHED state: an invariant state of every environment (what a
flush hands on). -/
@[expose] def CSOKAll (mode : CheckMode) (s : CState) : Prop := ∀ env', CSOK mode false env' s

theorem CSOKAll.residue {s : CState} (h : CSOKAll mode s) : CSOKF s := (h default).residue

theorem CSOKAll.flushed {s : CState} (h : CSOKF s) : CSOKAll mode s.flushed :=
  fun _ => flushC_csok h
grind_pattern [conleche_grind] CSOKAll.flushed => CSOKAll mode s.flushed

theorem csok_residue {env : Env} {s : CState} (h : CSOK mode false env s) : CSOKF s := h.residue

theorem csokF_flushed {s : CState} (h : CSOKF s) : CSOKF s.flushed := h.flushed
grind_pattern [conleche_grind] csokF_flushed => CSOKF s.flushed

/-- The rule stage's `inferType` from a flushed state: it flushes last. -/
theorem ruleR_infer_spec {envR : Env} (henvR : EnvWF envR)
    {d : Nat} {e : Expr} (hw : WScoped d e) {s₀ : CState} (hs : CSOKAll .verified s₀) :
    ⦃fun s => s = s₀⦄ (sharedOpsRuleR .verified (mkFEnv envR)).inferType (mkFEnv envR).env d e
    ⦃fun v s' => CSOKAll .verified s' ∧
      Runs ((fueledOpsM .verified).inferType (mkFEnv envR).env d e) v; ⊤⦄ :=
  triple_iff_run.mpr fun v' s' hr => by
    obtain ⟨-, v, hv, F, hF⟩ := ruleR_infer_simG henvR envR hw s₀ (hs envR) v' s' hr
    obtain ⟨rfl, -⟩ := hv
    exact ⟨fun env' => (ruleR_infer_simG henvR env' hw s₀ (hs envR) v' s' hr).1, F, hF⟩

/-- A closed term is well scoped. -/
theorem wscoped_of_closed {gen : Expr}
    (h : (gen.looseBVarsBounded 0 && !gen.hasFvar) = true) : WScoped 0 gen :=
  WScoped.of_not_hasFvar (by simp only [Bool.and_eq_true, Bool.not_eq_true'] at h; exact h.2)

/-- **The check of one generated rule, simulated**, from a flushed state:
the rule, closed by its own guard, typed at the rule-less recursors'
environment `envR` (`sharedOpsRuleR`'s inference flushes last), its
λ-telescope read syntactically. -/
theorem classRuleCheckS_spec {envR : Env} (henvR : EnvWF envR)
    (envT : Env) {cvR : ConstantVal} {n : Nat} {gen : Expr} {s₀ : CState}
    (hs : CSOKAll .verified s₀) :
    ⦃fun s => s = s₀⦄
      classRuleCheck (sharedOpsRuleR .verified (mkFEnv envR)) .plain (mkFEnv envT) (mkFEnv envR) cvR n
        gen
    ⦃fun v s' => CSOKAll .verified s' ∧
      Runs (classRuleCheck (fueledOpsM .verified) .plain (mkFEnv envT) (mkFEnv envR) cvR n gen) v;
      ⊤⦄ := by
  sym only [conleche_grind, classRuleCheck.eq_1, unwrapOr.eq_1, → wscoped_of_closed] =>
    vcgen [classRuleCheck, unwrapOr, ruleR_infer_spec henvR] <;> finish

/-- **One generated rule, simulated.**  From a flushed state: the rule,
closed by the stage's own guard, stored as generated and typed at the
rule-less recursors' environment `envR` (`sharedOpsRuleR`'s inference
flushes last), its λ-telescope read syntactically. -/
theorem classRuleOkS_spec {envR : Env} (henvR : EnvWF envR)
    (envT : Env) {cvR : ConstantVal} {n : Nat} {gen : Expr} {s₀ : CState}
    (hs : CSOKAll .verified s₀) :
    ⦃fun s => s = s₀⦄
      classRuleOk (sharedOpsRuleR .verified (mkFEnv envR)) .plain (mkFEnv envT) (mkFEnv envR) cvR n gen
    ⦃fun v s' => CSOKAll .verified s' ∧
      Runs (classRuleOk (fueledOpsM .verified) .plain (mkFEnv envT) (mkFEnv envR) cvR n gen) v; ⊤⦄ := by
  sym only [conleche_grind, classRuleOk.eq_1] =>
    vcgen [classRuleOk, classRuleCheckS_spec henvR envT hs] <;> finish

theorem classRulesOkS_spec {envR envT : Env}
    (henvR : EnvWF envR) {g : ClassGen} {recOf : Nat → Option Name} {cvR : ConstantVal}
    {c : Nat} :
    ∀ (xs : List ClassCtor) {s₀ : CState}, CSOKAll .verified s₀ →
      ⦃fun s => s = s₀⦄
        classRulesOk (sharedOpsRuleR .verified (mkFEnv envR)) .plain (mkFEnv envT) (mkFEnv envR) g
          recOf cvR c xs
      ⦃fun v s' => CSOKAll .verified s' ∧
        Runs (classRulesOk (fueledOpsM .verified) .plain (mkFEnv envT) (mkFEnv envR) g recOf cvR c xs)
          v; ⊤⦄ := by
  intro xs
  induction xs with
  | nil =>
    intro _ hs
    sym only [conleche_grind, classRulesOk] =>
      vcgen [classRulesOk.eq_def] <;> finish
  | cons x xs ih =>
    intro _ hs
    sym only [conleche_grind, classRulesOk, unwrapOr.eq_1] =>
      vcgen [classRulesOk.eq_def, unwrapOr, classRuleOkS_spec henvR envT, ih] <;> finish

theorem classRecsRulesOkS_spec {envR envT : Env}
    {g : ClassGen} {recOf : Nat → Option Name} :
    ∀ (cvs : List ConstantVal) (cs : List Nat) {s₀ : CState}, EnvWF envR → CSOKAll .verified s₀ →
      ⦃fun s => s = s₀⦄
        classRecsRulesOk (sharedOpsRuleR .verified (mkFEnv envR)) .plain (mkFEnv envT) (mkFEnv envR)
          g recOf cvs cs
      ⦃fun v s' => CSOKAll .verified s' ∧
        Runs (classRecsRulesOk (fueledOpsM .verified) .plain (mkFEnv envT) (mkFEnv envR) g recOf cvs
          cs) v; ⊤⦄ := by
  intro cvs
  induction cvs with
  | nil =>
    intro cs _ henvR hs
    sym only [conleche_grind, classRecsRulesOk] =>
      vcgen [classRecsRulesOk.eq_def] <;> finish
  | cons cvG cvs ih =>
    intro cs
    cases cs with
    | nil =>
      intro _ henvR hs
      sym only [conleche_grind, classRecsRulesOk] =>
        vcgen [classRecsRulesOk.eq_def] <;> finish
    | cons c cs =>
      intro _ henvR hs
      sym only [conleche_grind, classRecsRulesOk] =>
        vcgen [classRecsRulesOk.eq_def, classRulesOkS_spec (envT := envT) henvR,
          ih cs] <;> finish

/-! ### The stored recursors against the generated ones (task #431) -/

/-- A term without free variables is well scoped (the stored check's
guards). -/
theorem wscoped_zero_of_hasFvar_false {e : Expr} (h : e.hasFvar = false) : WScoped 0 e :=
  WScoped.of_not_hasFvar h


/-- **The stored type's domains against the generated one's**, simulated:
both telescopes opened at their own locals. -/
theorem recDomsAtS_spec (henv : EnvWF env) {rec : Name}
    {sfvs gfvs : List Expr}
    (hcs : ∀ (i : Nat) (x : Expr), sfvs[i]? = some x → WScoped i (Expr.fvarTypeD x))
    (hcg : ∀ (i : Nat) (x : Expr), gfvs[i]? = some x → WScoped i (Expr.fvarTypeD x)) :
    ∀ (k j : Nat) {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun st => st = s₀⦄ recDomsAt (sharedOpsC .verified (mkFEnv env)) (mkFEnv env).env rec sfvs gfvs j k
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (recDomsAt (fueledOpsM .verified) (mkFEnv env).env rec sfvs gfvs j k) v; ⊤⦄ := by
  intro k
  induction k with
  | zero =>
    intro j _ hs
    sym only [conleche_grind, recDomsAt.eq_1] => vcgen [recDomsAt] <;> finish
  | succ k ih =>
    intro j _ hs
    sym only [conleche_grind, recDomsAt.eq_2, unwrapOr] =>
      vcgen [recDomsAt, unwrapOr, defeqS_specF henv, ih] <;> finish

/-- The two opened types, compared, simulated. -/
theorem recTyOpenedS_spec (henv : EnvWF env) {rec : Name}
    {n : Nat} {s g : Expr} (hws : WScoped 0 s) (hwg : WScoped 0 g) {s₀ : CState}
    (hs : CSOK .verified false env s₀) :
    ⦃fun st => st = s₀⦄
      recTyOpened (sharedOpsC .verified (mkFEnv env)) (mkFEnv env).env rec n (openPisAtFvars n s 0)
        (openPisAtFvars n g 0)
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (recTyOpened (fueledOpsM .verified) (mkFEnv env).env rec n (openPisAtFvars n s 0)
        (openPisAtFvars n g 0)) v; ⊤⦄ := by
  cases hos : openPisAtFvars n s 0 with
  | none =>
    sym only [conleche_grind, recTyOpened] => vcgen [recTyOpened.eq_def] <;> finish
  | some qs =>
    obtain ⟨sfvs, srest⟩ := qs
    cases hog : openPisAtFvars n g 0 with
    | none =>
      sym only [conleche_grind, recTyOpened] => vcgen [recTyOpened.eq_def] <;> finish
    | some qg =>
      obtain ⟨gfvs, grest⟩ := qg
      have hcs : ∀ (i : Nat) (x : Expr), sfvs[i]? = some x → WScoped i (Expr.fvarTypeD x) :=
        fun i x hx => by simpa using openers_fvarTypeD_WScoped hos hws hx
      have hcg : ∀ (i : Nat) (x : Expr), gfvs[i]? = some x → WScoped i (Expr.fvarTypeD x) :=
        fun i x hx => by simpa using openers_fvarTypeD_WScoped hog hwg hx
      have hrs : WScoped n srest := by
        simpa using (ConLeche.openPisAtFvars_WScoped n s 0 hos hws).2
      have hrg : WScoped n grest := by
        simpa using (ConLeche.openPisAtFvars_WScoped n g 0 hog hwg).2
      sym only [conleche_grind, recTyOpened] =>
        vcgen [recTyOpened.eq_def, recDomsAtS_spec henv hcs hcg, defeqS_specF henv]
          <;> finish

/-- **The stored type's check**, simulated. -/
theorem recTyCheckS_spec (henv : EnvWF env) {rec : Name}
    {lps : List Name} {n : Nat} {s g : Expr} {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun st => st = s₀⦄
      recTyCheck (sharedOpsC .verified (mkFEnv env)) StructWalkers.plain (mkFEnv env) rec lps n s g
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (recTyCheck (fueledOpsM .verified) .plain (mkFEnv env) rec lps n s g) v; ⊤⦄ := by
  sym only [conleche_grind, recTyCheck.eq_1, → wscoped_zero_of_hasFvar_false] =>
    vcgen [recTyCheck, inferS_specF henv, sortS_specF henv,
      recTyOpenedS_spec henv] <;> finish

/-- **One stored rule's check**, simulated. -/
theorem ruleAgreeS_spec (henv : EnvWF env)
    {rec ctor : Name} {lps : List Name} {s g : Expr} {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun st => st = s₀⦄
      ruleAgree (sharedOpsC .verified (mkFEnv env)) StructWalkers.plain (mkFEnv env) rec ctor lps s g
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (ruleAgree (fueledOpsM .verified) .plain (mkFEnv env) rec ctor lps s g) v; ⊤⦄ := by
  sym only [conleche_grind, ruleAgree.eq_1, → wscoped_zero_of_hasFvar_false] =>
    vcgen [ruleAgree, inferS_specF henv, defeqS_specF henv] <;> finish

theorem streamRulesCheckS_spec (henv : EnvWF env)
    {rec : Name} {lps : List Name} :
    ∀ (rs : List RecRule) (gs : List Expr) {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun st => st = s₀⦄
        streamRulesCheck (sharedOpsC .verified (mkFEnv env)) StructWalkers.plain (mkFEnv env) rec lps rs gs
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (streamRulesCheck (fueledOpsM .verified) .plain (mkFEnv env) rec lps rs gs) v; ⊤⦄ := by
  intro rs
  induction rs with
  | nil =>
    intro gs _ hs
    cases gs <;>
    sym only [conleche_grind, streamRulesCheck] =>
      vcgen [streamRulesCheck.eq_def] <;> finish
  | cons r rs ih =>
    intro gs
    cases gs with
    | nil =>
      intro _ hs
      sym only [conleche_grind, streamRulesCheck] =>
        vcgen [streamRulesCheck.eq_def] <;> finish
    | cons g gs =>
      intro _ hs
      sym only [conleche_grind, streamRulesCheck] =>
        vcgen [streamRulesCheck.eq_def, ruleAgreeS_spec henv, ih gs] <;> finish

/-- The stored recursors' comparison, simulated. -/
theorem streamRecCompareS_spec (henv : EnvWF env)
    {rc : RecShape} {g : ConstantVal × TargetMajor × List Expr} {s₀ : CState}
    (hs : CSOK .verified false env s₀) :
    ⦃fun st => st = s₀⦄
      streamRecCompare (sharedOpsC .verified (mkFEnv env)) StructWalkers.plain (mkFEnv env) rc g
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (streamRecCompare (fueledOpsM .verified) .plain (mkFEnv env) rc g) v; ⊤⦄ := by
  sym only [conleche_grind, streamRecCompare.eq_1] =>
    vcgen [streamRecCompare, recTyCheckS_spec henv, streamRulesCheckS_spec henv] <;> finish

/-- The stored rules' shape (no operation), simulated. -/
theorem streamRulesShapeS_spec {rec : Name} :
    ∀ (rs : List RecRule) (cs : List (ConstantVal × Nat)) {s₀ : CState}, CSOK mode false env s₀ →
      ⦃fun st => st = s₀⦄ streamRulesShape (m := CheckCM) rec rs cs
      ⦃fun v s' => CSOK mode false env s' ∧ Runs (streamRulesShape (m := FueledM) rec rs cs) v; ⊤⦄
          := by
  intro rs
  induction rs with
  | nil =>
    intro cs _ hs
    cases cs <;>
    sym only [conleche_grind, streamRulesShape] =>
      vcgen [streamRulesShape.eq_def] <;> finish
  | cons r rs ih =>
    intro cs
    cases cs with
    | nil =>
      intro _ hs
      sym only [conleche_grind, streamRulesShape] =>
        vcgen [streamRulesShape.eq_def] <;> finish
    | cons c cs =>
      intro _ hs
      sym only [conleche_grind, streamRulesShape] =>
        vcgen [streamRulesShape.eq_def, ih cs] <;> finish

/-- The records' K flags: the check reads no state, at the cached
driver as at the pure one. -/
theorem streamKCheck_run {p : BlockShape} :
    ∀ {recs : List RecShape} {out : List (ConstantVal × TargetMajor × List Expr)}
      {s s' : CState} {u : PUnit},
      streamKCheck (m := CheckCM) p recs out s = .ok (u, s') →
      s' = s ∧ streamKCheck (m := CheckM) p recs out = .ok ()
  | [], _, _, _, _, h => by
    simp only [streamKCheck, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm, rfl⟩
  | _ :: _, [], _, _, _, h => by
    simp only [streamKCheck, pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.2.symm, rfl⟩
  | rc :: rcs, g :: gs, s, s', u, h => by
    unfold streamKCheck at h ⊢
    by_cases hk : (rc.isK == recKExpected p g.2.1) = true
    · simp only [hk, Bool.not_true, reduceIte, pure, StateT.pure, Except.pure, Bind.bind,
        StateT.bind, Except.bind, Bool.false_eq_true, bind_pure_comp, pure_bind] at h ⊢
      exact streamKCheck_run h
    · simp only [Bool.not_eq_true] at hk
      simp [hk, Bind.bind, StateT.bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
        StateT.lift, liftM, monadLift, MonadLift.monadLift, instMonadExceptOfMonadExceptOf] at h

/-- The stored recursors' checks, simulated. -/
theorem streamRecCheckS_spec (henv : EnvWF env)
    {rc : RecShape} {g : ConstantVal × TargetMajor × List Expr} {s₀ : CState}
    (hs : CSOK .verified false env s₀) :
    ⦃fun st => st = s₀⦄
      streamRecCheck (sharedOpsC .verified (mkFEnv env)) StructWalkers.plain (mkFEnv env) rc g
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (streamRecCheck (fueledOpsM .verified) .plain (mkFEnv env) rc g) v; ⊤⦄ := by
  sym only [conleche_grind, streamRecCheck.eq_1] =>
    vcgen [streamRecCheck, streamRulesShapeS_spec (mode := .verified) (env := env),
      streamRecCompareS_spec henv] <;> finish

theorem streamRecsCheckS_spec (henv : EnvWF env) :
    ∀ (recs : List RecShape) (out : List (ConstantVal × TargetMajor × List Expr))
      {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun st => st = s₀⦄
        streamRecsCheck (sharedOpsC .verified (mkFEnv env)) StructWalkers.plain (mkFEnv env) recs out
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (streamRecsCheck (fueledOpsM .verified) .plain (mkFEnv env) recs out) v; ⊤⦄ := by
  intro recs
  induction recs with
  | nil =>
    intro out _ hs
    sym only [conleche_grind, streamRecsCheck] =>
      vcgen [streamRecsCheck.eq_def] <;> finish
  | cons rc rcs ih =>
    intro out
    cases out with
    | nil =>
      intro _ hs
      sym only [conleche_grind, streamRecsCheck] =>
        vcgen [streamRecsCheck.eq_def] <;> finish
    | cons g gs =>
      intro _ hs
      sym only [conleche_grind, streamRecsCheck] =>
        vcgen [streamRecsCheck.eq_def, streamRecCheckS_spec henv, ih gs] <;> finish

/-! ## 3. The assembly -/

/-- The seeds' parameters: every OUTSIDE class's, moved to the walk's
representation. -/
theorem mem_classSeeds {ctx : NestCtx} {holes : List Expr} {Ms : List TargetMajor}
    {s : NestKey × Nat} (h : s ∈ classSeeds ctx holes Ms) :
    ∃ M ∈ Ms, M.member = none ∧ s = nestSeedOf ctx holes M.ind M.lvls M.ds M.nPc := by
  simp only [classSeeds, List.mem_filterMap] at h
  obtain ⟨M, hM, hs⟩ := h
  split at hs
  · rename_i hn
    exact ⟨M, hM, Option.isNone_iff_eq_none.mp hn, (Option.some.inj hs).symm⟩
  · exact nomatch hs

/-- The rule-less recursors' environment the rule stage infers at. -/
@[expose] def ruleEnv (p : BlockShape) (Ms : List TargetMajor) (cvGs : List ConstantVal)
    (recCls : List Nat) (env : Env) : Env :=
  consBlockRecsBare p 0 ((cvGs.zip recCls).map fun (cv, c) => (cv, (Ms.getD c default).nIdx)) env

theorem classFeR_mkFEnv (p : BlockShape) (Ms : List TargetMajor) (cvGs : List ConstantVal)
    (recCls : List Nat) (env : Env) :
    classFeR p Ms cvGs recCls (mkFEnv env) = mkFEnv (ruleEnv p Ms cvGs recCls env) :=
  consBlockRecsBareF_mkFEnv p 0 _ env

/-- **The rule-less generated recursors' environment is well formed**:
every recursor's generated type passed `classConstOk`. -/
theorem envWF_ruleEnv {env₂ : Env} (henv₂ : EnvWF env₂) {p : BlockShape} {g : ClassGen}
    {k : Nat} {cvRis : List ConstantVal} {cls : List Nat} {cvGs : List ConstantVal}
    (h : Runs (classRecTysOk (fueledOpsM mode) (mkFEnv env₂) g k p.recs cvRis cls) cvGs)
    (Ms : List TargetMajor) (recCls : List Nat) :
    EnvWF (ruleEnv p Ms cvGs recCls env₂) := by
  obtain ⟨F, hF⟩ := h
  rw [classRecTysOk_datF] at hF
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run hF
  have key : ∀ c ∈ (cvGs.zip recCls).map (fun (x : ConstantVal × Nat) => (x.1, (Ms.getD x.2 default).nIdx)),
      ∃ F', classConstOk (fueledOps mode F') (mkFEnv env₂) c.1 = .ok () := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.of_mem_zip hx).1
    have hil : i < p.recs.length := by
      rw [← hlenG]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨c, cvG, -, hcvG, ⟨R⟩⟩ := hallG i _ (List.getElem?_eq_getElem hil)
    rw [hi] at hcvG
    obtain rfl := Option.some.inj hcvG
    exact ⟨F, R.hcv⟩
  refine envWF_consBlockRecsBare henv₂ (fun c hc => ?_) (fun c hc => ?_)
  · obtain ⟨_, hk⟩ := key c hc
    exact classConstOk_typeWF hk
  · obtain ⟨_, hk⟩ := key c hc
    exact classConstOk_litShapeAt hk
grind_pattern [conleche_grind] envWF_ruleEnv =>
  Runs (classRecTysOk (fueledOpsM mode) (mkFEnv env₂) g k p.recs cvRis cls) cvGs,
  ruleEnv p Ms cvGs recCls env₂

theorem listAll_targetMajScoped {nP : Nat} {Ms : List TargetMajor}
    (h : ListAll (ClassMajScoped nP) Ms) : ListAll TargetMajScoped Ms :=
  fun M hM => (h M hM).1

/-- The formers' types are closed (stated eta-reduced, as the stage's
unfolding leaves them). -/
theorem allWS_types {formers : List ConstantVal} (hT : ListAll TyClosed formers) :
    AllWS 0 (formers.map ConstantVal.type) := by
  intro t ht
  obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
  exact hT cv hcv

/-- **The generated recursor stage at the cached driver, simulated**:
from an invariant state of the constructors' environment to a residue,
on the pass's classes (scoped, `ClassMajScoped`) and table. -/
theorem genRecCheckS_spec {env₂ : Env}
    (henv₂ : EnvWF env₂) {p : BlockShape} {nestedBit : Bool} {params : List Expr}
    {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor}
    (hMs₀ : ListAll (ClassMajScoped p.nP) Ms₀) {block : List ConstantInfo}
    (hT : ListAll TyClosed p.formers) {s₀ : CState} (hs : CSOK .verified false env₂ s₀) :
    ⦃fun s => s = s₀⦄
      genRecCheck (shadowOpsC .verified) (mkFEnv env₂) p nestedBit params tbl rd Ms₀ block
    ⦃fun v s' => CSOKF s' ∧
      Runs (genRecCheck (ShadowOps.ofOps (fueledOpsM .verified)) (mkFEnv env₂) p nestedBit params tbl
        rd Ms₀ block) v; ⊤⦄ := by
  -- structural: the shadow operations' fields, and the cached rule stage at the overlay,
  -- which answers as the pushed rule-less recursors do
  unfold genRecCheck
  dsimp only [shadowOpsC, ShadowOps.ofOps]
  simp only [classRecsRulesOk_classFeROvl .verified (fe := mkFEnv env₂) rfl]
  simp only [structWalkersC_eq_plain, classFeR_mkFEnv, mkFEnv_env]
  -- `gen`: the pure side, evaluated bind by bind, through eleven binds and three guards
  sym only [conleche_grind, unwrapOr.eq_1, mkFEnv_env, listAll_targetMajScoped hMs₀,
      → csok_residue, → CSOKAll.residue] =>
    vcgen [unwrapOr, flushC, targetRecPinsS_spec (mode := .verified) (env := env₂),
      classStreamRecsS_spec henv₂, classesNfsS_spec henv₂ (allWS_types hT),
      classesCtorsS_spec henv₂ (allWS_types hT),
      classFormerTysS_spec henv₂,
      classRecTysOkS_spec henv₂, classRecsRulesOkS_spec (envT := env₂)] <;>
      finish (gen := 12)

/-- **The generated recursor stage at the cached driver** is reproduced
by the pure fueled stage. -/
theorem genRecCheckS_run {env₂ : Env}
    (henv₂ : EnvWF env₂) {p : BlockShape} {nestedBit : Bool} {params : List Expr}
    {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor}
    (hMs₀ : ∀ M ∈ Ms₀, ClassMajScoped p.nP M) {block : List ConstantInfo}
    (hT : ∀ cv ∈ p.formers, WScoped 0 cv.type)
    {s₀ : CState} (hs : CSOK .verified false env₂ s₀) {out : List (ConstantVal × TargetMajor × List
        Expr)}
    {s' : CState}
    (h : genRecCheck (shadowOpsC .verified) (mkFEnv env₂) p nestedBit params tbl rd Ms₀ block
      s₀ = .ok (out, s')) :
    CSOKF s' ∧ ∃ F, genRecCheck (ShadowOps.fueled .verified F) (mkFEnv env₂) p nestedBit params tbl
      rd Ms₀ block = .ok out := by
  obtain ⟨hs', F, hF⟩ := triple_iff_run.mp (genRecCheckS_spec henv₂ hMs₀ hT hs) out s' h
  exact ⟨hs', F, by rw [← genRecCheck_datF]; exact hF⟩

/-! ## The install after the pass, at the cached driver -/

/-- Each generated recursor passed a constant's check. -/
theorem genRecCheck_outShape {fe : FEnv} {env : Env} {p : BlockShape} {nestedBit : Bool}
    {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat} (hfe : fe = mkFEnv env)
    (h : genRecCheck (ShadowOps.fueled mode F) fe p nestedBit params tbl rd Ms₀ block
      = .ok out) : ∀ o ∈ out, LitShapeAt o.1 := by
  subst hfe
  obtain ⟨R⟩ := genRecCheck_run h
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run R.hcvGs
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run R.hrules
  intro o ho
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ho
  have hil : i < out.length := (List.getElem?_eq_some_iff.mp hi).1
  have hir : i < p.recs.length := by
    rw [← hlenG]; omega
  obtain ⟨c, cvG, hc, hG, ⟨T⟩⟩ := hallG i _ (List.getElem?_eq_getElem hir)
  obtain ⟨rhss, hoi, -⟩ := hallO i cvG c hG hc
  rw [hi] at hoi
  obtain rfl := Option.some.inj hoi
  exact classConstOk_litShapeAt T.hcv

/-- **The stored family's environment is well-formed**: every stored
recursor type is a checked generated constant's (`classConstOk`), every
stored rule a generated rule closed, at the recursor's level parameters
and resolved at the rule-less recursors' environment (`classRuleOk`), and
an outside class's `.nested` datum reads off the stored type
(`genStage_nestedRead`, at the block's canonical parameters and the
classes' checked parameters). -/
theorem genRecCheck_outFacts {env₂ : Env} {p : BlockShape}
    {nestedBit : Bool} {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead}
    {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (ShadowOps.fueled mode F) (mkFEnv env₂) p nestedBit params tbl rd Ms₀
      block = .ok out) (hpl : params.length = p.nP)
    (hMs₀ : ∀ M ∈ Ms₀, ClassOutParams p.nP M) :
    (∀ t ∈ out, t.1.type.hasFvar = false ∧
      t.1.type.allLevelParamsDefined t.1.levelParams = true ∧
      t.1.type.constsResolve env₂ = true ∧
      t.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ t.2.2, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined t.1.levelParams = true ∧
        rhs.constsResolve (consBlockRecsBare p 0 (out.map fun t => (t.1, t.2.1.nIdx)) env₂)
          = true ∧
        rhs.looseBVarsBounded 0 = true) ∧
    (∀ i t, out[i]? = some t → t.2.1.member = none →
      NestedRead (·.constsResolve env₂) t.1.levelParams t.1.type (p.majorIdxAt i)
        (p.rulePrefixAt i) t.2.1.nPc t.2.1.lvls
        (t.2.1.ds.map (Expr.abstractPrefix (p.rulePrefixAt i) 0))) := by
  obtain ⟨R⟩ := genRecCheck_run h
  have hcvGs := R.hcvGs
  have hrules := R.hrules
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run hcvGs
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run hrules
  -- every stored entry: a generated constant, its class, its rules
  have hat : ∀ (i : Nat) (o : ConstantVal × TargetMajor × List Expr), out[i]? = some o →
      ∃ rc c cvG, rd.recCls[i]? = some c ∧ R.cvGs[i]? = some cvG ∧
        o = (cvG, R.Ms.getD c default, o.2.2) ∧
        Nonempty (ClassRecTyRun mode F (mkFEnv env₂) R.g p.k rc c cvG) ∧
        classRulesOk (fueledOps mode F) .plain (mkFEnv env₂)
          (classFeR p R.Ms R.cvGs rd.recCls (mkFEnv env₂)) R.g
          (classRecOf rd.recCls R.cvGs) cvG
          c (R.ctors.getD c []) = .ok o.2.2 := by
    intro i o ho
    have hil : i < p.recs.length := by
      have := (List.getElem?_eq_some_iff.mp ho).1; rw [hlenO] at this; omega
    obtain ⟨c, cvG, hc, hG, T⟩ := hallG i p.recs[i] (List.getElem?_eq_getElem hil)
    obtain ⟨rhss, hoi, hr⟩ := hallO i cvG c hG hc
    rw [ho] at hoi
    obtain rfl := Option.some.inj hoi
    exact ⟨_, c, cvG, hc, hG, rfl, T, hr⟩
  have hbare : out.map (fun t => (t.1, t.2.1.nIdx))
      = (R.cvGs.zip rd.recCls).map fun q => (q.1, (R.Ms.getD q.2 default).nIdx) := by
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map]
    cases ho : out[i]? with
    | none =>
      have : (R.cvGs.zip rd.recCls)[i]? = none := by
        rw [List.getElem?_eq_none_iff] at ho ⊢; simp only [List.length_zip]; omega
      simp [this]
    | some o =>
      obtain ⟨rc, c, cvG, hc, hG, ho', -, -⟩ := hat i o ho
      have hz : (R.cvGs.zip rd.recCls)[i]? = some (cvG, c) :=
        List.getElem?_zip_eq_some.mpr ⟨hG, hc⟩
      rw [ho']
      simp [hz]
  have hfeR : classFeR p R.Ms R.cvGs rd.recCls (mkFEnv env₂)
      = mkFEnv (consBlockRecsBare p 0 (out.map fun t => (t.1, t.2.1.nIdx)) env₂) := by
    unfold classFeR
    rw [consBlockRecsBareF_mkFEnv, hbare]
  refine ⟨fun o ho => ?_, fun i t ht hm => genStage_nestedRead R hpl hMs₀ ht hm⟩
  obtain ⟨i, hoi⟩ := List.getElem?_of_mem ho
  obtain ⟨rc, c, cvG, -, -, ho', ⟨T⟩, hr⟩ := hat i o hoi
  obtain ⟨g1, g2, g3, g4⟩ := classConstOk_typeWF T.hcv
  rw [ho']
  refine ⟨g1, g2, g3, g4, fun rhs hrhs => ?_⟩
  obtain ⟨hlenR, hallR⟩ := classRulesOk_run hr
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hrhs
  have hjl : j < (R.ctors.getD c []).length := by
    have := (List.getElem?_eq_some_iff.mp hj).1; rw [hlenR] at this; exact this
  obtain ⟨gen, rhs', hrhs', -, ⟨Q⟩⟩ := hallR j _ (List.getElem?_eq_getElem hjl)
  rw [hj] at hrhs'
  obtain rfl := Option.some.inj hrhs'
  have hres := Q.hres
  rw [hfeR] at hres
  simp only [StructWalkers.plain, constsResolveF_eq] at hres
  refine ⟨by rw [Q.hout]; exact Q.hfv, Q.hlp, hres, by rw [Q.hout]; exact Q.hbv⟩

theorem genRecCheck_recsWF {env₂ : Env} (henv₂ : EnvWF env₂) {p : BlockShape}
    {nestedBit : Bool} {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead}
    {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (ShadowOps.fueled mode F) (mkFEnv env₂) p nestedBit params tbl rd Ms₀
      block = .ok out) (hpl : params.length = p.nP)
    (hMs₀ : ∀ M ∈ Ms₀, ClassOutParams p.nP M) :
    EnvWF (consBlockRecsT p 0 out env₂) :=
  envWF_consBlockRecsT henv₂ (genRecCheck_outFacts h hpl hMs₀).1 (genRecCheck_outFacts h hpl hMs₀).2
    (genRecCheck_outShape rfl h)

/-- The stream's recursor constants, checked at the constructors'
environment: each type closed, at its level parameters, resolving. -/
theorem classStreamRecs_typeWF {env : Env} {F : Nat} :
    ∀ {recs : List RecShape} {cvs : List ConstantVal},
      classStreamRecs (fueledOps mode F) (mkFEnv env) recs = .ok cvs →
      ∀ rc ∈ recs, rc.cvR.type.hasFvar = false ∧
        rc.cvR.type.allLevelParamsDefined rc.cvR.levelParams = true ∧
        rc.cvR.type.constsResolve env = true ∧
        rc.cvR.type.looseBVarsBounded 0 = true
  | [], _, _ => fun rc h => nomatch h
  | rc :: rcs, cvs, h => by
    unfold classStreamRecs at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    obtain ⟨xs, hxs, -⟩ := exceptBind_ok h
    cases u
    intro rc' hrc'
    rcases List.mem_cons.mp hrc' with rfl | hm
    · rw [checkConstantValF_eq] at hu
      exact checkConstantVal_typeWF hu
    · exact classStreamRecs_typeWF hxs rc' hm

/-- Each generated recursor is its record's constant at the generated
type. -/
theorem genRecCheck_outCv {fe : FEnv} {p : BlockShape} {nestedBit : Bool} {params : List Expr}
    {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (ShadowOps.fueled mode F) fe p nestedBit params tbl rd Ms₀ block
      = .ok out) :
    out.length = p.recs.length ∧
    ∀ (i : Nat) (rc : RecShape) (o : ConstantVal × TargetMajor × List Expr),
      p.recs[i]? = some rc → out[i]? = some o → o.1 = { rc.cvR with type := o.1.type } := by
  obtain ⟨R⟩ := genRecCheck_run h
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run R.hcvGs
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run R.hrules
  refine ⟨?_, fun i rc o hrc ho => ?_⟩
  · have hge : p.recs.length ≤ rd.recCls.length := by
      cases hp : p.recs.length with
      | zero => exact Nat.zero_le _
      | succ n =>
        obtain ⟨c, -, hc, -⟩ := hallG n p.recs[n] (List.getElem?_eq_getElem (by omega))
        have := (List.getElem?_eq_some_iff.mp hc).1
        omega
    rw [hlenO, hlenG]
    exact Nat.min_eq_left hge
  obtain ⟨c, cvG, hc, hG, ⟨T⟩⟩ := hallG i rc hrc
  obtain ⟨rhss, hoi, -⟩ := hallO i cvG c hG hc
  rw [ho] at hoi
  obtain rfl := Option.some.inj hoi
  have := T.hcvG
  simp only
  rw [this]

/-- The records' pins: no recursor takes a reserved name. -/
theorem targetRecPins_unreserved {p : BlockShape} {block : List ConstantInfo}
    (h : targetRecPins (m := CheckM) p block = .ok ()) :
    ∀ rc ∈ p.recs, reservedRecName rc.cvR.name = false := by
  unfold targetRecPins at h
  by_cases h1 : blockRecLpsOk p = true
  · simp only [h1, ↓reduceIte] at h
    by_cases h2 : blockRecNamesUnreserved p = true
    · intro rc hrc
      have := List.all_eq_true.mp h2 rc hrc
      exact eq_of_beq (by simpa using this)
    · simp [h2, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [h1, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- No generated recursor takes a reserved name. -/
theorem genRecCheck_out_unreserved {fe : FEnv} {p : BlockShape} {nestedBit : Bool}
    {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead} {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (ShadowOps.fueled mode F) fe p nestedBit params tbl rd Ms₀ block
      = .ok out) :
    ∀ o ∈ out, reservedRecName o.1.name = false := by
  obtain ⟨R⟩ := genRecCheck_run h
  obtain ⟨hlen, hcv⟩ := genRecCheck_outCv h
  intro o ho
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ho
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1; omega
  have hrc : p.recs[i]? = some p.recs[i] := List.getElem?_eq_getElem hil
  rw [hcv i _ o hrc hi]
  exact targetRecPins_unreserved R.pins _ (List.getElem_mem hil)

/-- **The stream's recursors are well formed**: each record's type
is the record's, checked as a constant at the constructors' environment
(`classStreamRecs`); each stored right-hand side is the generated one or
passed `ruleAgree`'s guards; an auxiliary recursor's stored type reads
its firing data (`streamNestedOk`). -/
theorem streamRecs_recsWF {env₂ : Env} (henv₂ : EnvWF env₂) {p : BlockShape}
    {nestedBit : Bool} {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead}
    {Ms₀ : List TargetMajor} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F F' : Nat}
    (h : genRecCheck (ShadowOps.fueled mode F) (mkFEnv env₂) p nestedBit params tbl rd Ms₀
      block = .ok out) (hpl : params.length = p.nP)
    (hMs₀ : ∀ M ∈ Ms₀, ClassOutParams p.nP M)
    (hS : streamRecsCheck (fueledOps mode F') .plain
      (mkFEnv (consBlockRecsT p 0 out env₂)) p.recs out = .ok ()) :
    EnvWF (consBlockRecsT p 0 (streamRecs p.recs out) env₂) := by
  obtain ⟨hF, hN⟩ := genRecCheck_outFacts h hpl hMs₀
  obtain ⟨hlenO, hcv⟩ := genRecCheck_outCv h
  obtain ⟨R⟩ := genRecCheck_run h
  have hstream := classStreamRecs_typeWF R.hcvRis
  obtain ⟨-, hallS⟩ := streamRecsCheck_inv hS
  have hnames : (streamRecs p.recs out).map (·.1.name) = out.map (·.1.name) :=
    streamRecs_map_name hlenO
  -- resolution at the generated install transfers to the stored bare cons
  have hres : ∀ e : Expr, e.constsResolve (consBlockRecsT p 0 out env₂) = true →
      e.constsResolve (consBlockRecsBare p 0
        ((streamRecs p.recs out).map fun t => (t.1, t.2.1.nIdx)) env₂) = true :=
    fun e he => Expr.constsResolve_of_find
      (isSome_consBlockRecsT_bare (fun _ hn => hn)
        (by simp only [List.map_map, Function.comp_def]; exact hnames.symm)) he
  have hresG : ∀ e : Expr,
      e.constsResolve (consBlockRecsBare p 0 (out.map fun t => (t.1, t.2.1.nIdx)) env₂) = true →
      e.constsResolve (consBlockRecsBare p 0
        ((streamRecs p.recs out).map fun t => (t.1, t.2.1.nIdx)) env₂) = true :=
    fun e he => Expr.constsResolve_of_find
      (isSome_consBlockRecsBare_bare (fun _ hn => hn)
        (by simp only [List.map_map, Function.comp_def]; exact hnames.symm)) he
  have hshS : ∀ t ∈ streamRecs p.recs out, LitShapeAt t.1 := by
    intro t ht
    obtain ⟨i, hti⟩ := List.getElem?_of_mem ht
    obtain ⟨rc, g, hrc, hg, rfl⟩ := streamRecs_getElem? hti
    have hgcv := hcv i rc g hrc hg
    have hrcS : LitShapeAt rc.cvR :=
      litShapeAt_of_reservedRec (targetRecPins_unreserved R.pins rc (List.mem_of_getElem? hrc))
    have e : ({ g.1 with type := rc.cvR.type } : ConstantVal) = rc.cvR := by rw [hgcv]
    show LitShapeAt ({ g.1 with type := rc.cvR.type } : ConstantVal)
    rw [e]
    exact hrcS
  refine envWF_consBlockRecsT henv₂ (fun t ht => ?_) (fun i t ht hm => ?_) hshS
  · obtain ⟨i, hti⟩ := List.getElem?_of_mem ht
    obtain ⟨rc, g, hrc, hg, rfl⟩ := streamRecs_getElem? hti
    have hgcv := hcv i rc g hrc hg
    obtain ⟨g1, g2, g3, g4, grhs⟩ := hF g (List.mem_of_getElem? hg)
    obtain ⟨s1, s2, s3, s4⟩ := hstream rc (List.mem_of_getElem? hrc)
    have hlps : g.1.levelParams = rc.cvR.levelParams := by rw [hgcv]
    obtain ⟨-, -, hcmp⟩ := streamRecCheck_inv (hallS i rc g hrc hg)
    obtain ⟨-, hrules⟩ := streamRecCompare_inv hcmp
    obtain ⟨hlenR, hallR⟩ := streamRulesCheck_inv hrules
    refine ⟨s1, by simp only; rw [hlps]; exact s2, s3, s4, fun rhs hrhs => ?_⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hrhs
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hr
    obtain ⟨gk, hgk⟩ : ∃ gk, g.2.2[k]? = some gk := by
      have := (List.getElem?_eq_some_iff.mp hk).1
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rcases hallR k r gk hk hgk with heq | hag
    · obtain ⟨r1, r2, r3, r4⟩ := grhs gk (List.mem_of_getElem? hgk)
      rw [heq]
      exact ⟨r1, r2, hresG _ r3, r4⟩
    · obtain ⟨a1, a2, -, a4, a5, -⟩ := ruleAgree_inv hag
      refine ⟨a2, a4, hres _ ?_, a1⟩
      simpa [StructWalkers.plain, constsResolveF_eq] using a5
  · obtain ⟨rc, g, hrc, hg, rfl⟩ := streamRecs_getElem? ht
    have hgcv := hcv i rc g hrc hg
    obtain ⟨n1, n2, n3, -, -, -, -, -, -, -, n4⟩ := hN i g hg hm
    obtain ⟨hn, -⟩ := (streamRecCheck_inv (hallS i rc g hrc hg)).2
    have hmI : p.majorIdxAt i = rc.mI := by
      simp only [BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
    have hrP : p.rulePrefixAt i = rc.rP := by
      simp only [BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
    simp only at hm
    simp only [generatedFire, auxRuleFire] at hn
    rw [hm] at hn
    obtain ⟨pre, dom, body, D, e1, e2, e3⟩ := streamNestedOk_read hn
    have hlps : g.1.levelParams = rc.cvR.levelParams := by rw [hgcv]
    refine ⟨n1, ?_, ?_, pre, dom, body, D, ?_, e2, ?_, n4⟩
    · simp only; rw [hlps]; rw [hlps] at n2; exact n2
    · simp only; rw [hlps]; rw [hlps] at n3; exact n3
    · simp only; rw [hmI]; exact e1
    · rw [hmI, hrP]; exact e3

/-- **The install after the pass, at k members, at the cached driver**,
is reproduced by the pure fueled `checkBlockTail`. -/
theorem checkBlockTailS_run
    {env₁ : Env} (henv₁ : EnvWF env₁) {block : List ConstantInfo}
    {p : BlockShape}
    {kinds : List (List (List NestFieldKind))} {params : List Expr}
    {rd : ClassRead} {Ms₀ : List TargetMajor} {tbl : Array NestCtorNf}
    (hT : ∀ cv ∈ p.formers, WScoped 0 cv.type)
    (henv₂ : EnvWF (consBlockCtors p.nP p.memberCtors env₁))
    (hMs₀ : ∀ M ∈ Ms₀, ClassMajScoped p.nP M) (hpl : params.length = p.nP)
    {s₀ : CState} (hs : CSOK .verified false env₁ s₀) {u : Unit} {s' : CState}
    (h : checkBlockTailS .verified block
      ⟨mkFEnv env₁, p, kinds, params, rd, Ms₀, tbl⟩
      s₀ = .ok (u, s')) :
    CSOKF s' ∧
    ∃ F, (checkBlockTail (fueledOpsM .verified) block
      ⟨env₁, p, kinds, params, rd, Ms₀, tbl⟩).val F
        = .ok () := by
  unfold checkBlockTailS at h
  dsimp only at h
  rw [checkBlockIdxSortsF_eqC] at h
  obtain ⟨isorts, sS, hsorts, h⟩ := bindC_ok h
  have hzT : ∀ x ∈ p.members, WScoped 0 x.cvT.type :=
    fun x hx => hT x.cvT (List.mem_map_of_mem hx)
  obtain ⟨hsS, F₀, hF₀⟩ :=
    triple_iff_run.mp (checkBlockIdxSortsS_spec henv₁ hzT hs) isorts sS hsorts
  rw [consBlockCtorsF_mkFEnv] at h
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : sS.flushed = sC := congrArg Prod.snd hfl2
  obtain ⟨out, s₃, hrec, h⟩ := bindC_ok h
  obtain ⟨hs₃, F₃, hF₃⟩ := genRecCheckS_run henv₂ hMs₀ hT
    (flushC_csok hsS.residue) hrec
  have henv₃ := genRecCheck_recsWF henv₂ hF₃ hpl (fun M hM => (hMs₀ M hM).2.1)
  rw [structWalkersC_eq_plain] at h
  -- the stored recursors' check, at the generated install (an overlay
  -- that answers as the pushed index)
  have hovl : (mkFEnv (consBlockCtors p.nP p.memberCtors env₁)).ovl = [] := rfl
  have hf : ((mkFEnv (consBlockCtors p.nP p.memberCtors env₁)).overlay
      (blockRecInfosTF p 0 out).reverse).find?
      = (mkFEnv (consBlockRecsT p 0 out
          (consBlockCtors p.nP p.memberCtors env₁))).find? := by
    rw [find?_overlay_pushAll hovl, pushAll_blockRecInfosTF_mkFEnv]
  have htb : ((mkFEnv (consBlockCtors p.nP p.memberCtors env₁)).overlay
      (blockRecInfosTF p 0 out).reverse
      ).findTable?
      = (mkFEnv (consBlockRecsT p 0 out
          (consBlockCtors p.nP p.memberCtors env₁))).findTable? := by
    rw [findTable?_overlay_pushAll hovl, pushAll_blockRecInfosTF_mkFEnv]
  have he : ((mkFEnv (consBlockCtors p.nP p.memberCtors env₁)).overlay
      (blockRecInfosTF p 0 out).reverse).env
      = (mkFEnv (consBlockRecsT p 0 out
          (consBlockCtors p.nP p.memberCtors env₁))).env := by
    rw [env_overlay_pushAll _ hovl, pushAll_blockRecInfosTF_mkFEnv]
  rw [sharedOpsC_congr hf htb,
    streamRecsCheck_congr (w := StructWalkers.plain)
      (by funext e; exact constsResolveF_congr hf e) he] at h
  obtain ⟨uK, sK, hKrun, hK⟩ := bindC_ok h
  obtain ⟨hsK, hKp⟩ := streamKCheck_run hKrun
  rw [hsK] at hK
  obtain ⟨u3, s₃', hfl3, h⟩ := bindC_ok hK
  rw [flushC_run] at hfl3
  injection hfl3 with hfl3
  obtain rfl : s₃.flushed = s₃' := congrArg Prod.snd hfl3
  obtain ⟨u4, s₄', hst, h⟩ := bindC_ok h
  obtain ⟨hs₄', F₄, hF₄⟩ := triple_iff_run.mp
    (streamRecsCheckS_spec henv₃ p.recs out (flushC_csok hs₃)) u4 s₄' hst
  obtain ⟨u5, s₄, hfl4, h⟩ := bindC_ok h
  rw [flushC_run] at hfl4
  injection hfl4 with hfl4
  obtain rfl : s₄'.flushed = s₄ := congrArg Prod.snd hfl4
  have hs₄ : CSOKF s₄'.flushed := hs₄'.residue.flushed
  have hF₄' : streamRecsCheck (fueledOps .verified F₄) .plain
      (mkFEnv (consBlockRecsT p 0 out
        (consBlockCtors p.nP p.memberCtors env₁))) p.recs out = .ok () := by
    rw [← streamRecsCheck_datF]; cases u4; exact hF₄
  obtain ⟨hs₅, hT₆⟩ := checkBlockTablesS_run _ _ _ h
  obtain ⟨G, hle₀, hle₃, hle₄⟩ : ∃ G, F₀ ≤ G ∧ F₃ ≤ G ∧ F₄ ≤ G :=
    ⟨max F₀ (max F₃ F₄), by omega, by omega, by omega⟩
  refine ⟨hs₅ ▸ hs₄, G, ?_⟩
  have g₄ : streamRecsCheck (fueledOps .verified G) .plain
      (mkFEnv (consBlockRecsT p 0 out
        (consBlockCtors p.nP p.memberCtors env₁))) p.recs out = .ok () := by
    rw [← streamRecsCheck_datF]; exact FueledM.up hle₄ (by rw [streamRecsCheck_datF]; exact hF₄')
  have g₀ : checkBlockIdxSorts (fueledOps .verified G) env₁ p
      p.members = .ok isorts := by
    rw [← checkBlockIdxSorts_datF]; exact FueledM.up hle₀ hF₀
  have g₃ : checkBlockRec (fueledOps .verified G) (consBlockCtors p.nP p.memberCtors env₁) p
      (blockNestedBit p kinds) params tbl.toList rd Ms₀ block = .ok out := by
    show genRecCheck (ShadowOps.fueled .verified G) _ _ _ _ _ _ _ _ = _
    rw [← genRecCheck_datF]
    exact FueledM.up hle₃ (by rw [genRecCheck_datF]; exact hF₃)
  rw [checkBlockTail_datF]
  unfold checkBlockTail
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₀]
  simp only [Except.bind]
  rw [g₃]
  simp only [Except.bind]
  rw [hKp]
  simp only [Except.bind]
  rw [g₄]
  exact hT₆

/-- **One pass at k members, at the cached driver**, is reproduced by
the pure fueled `checkBlockPass`: the formers' environment is the index
over the pure one, the memo state is an invariant state of it, the
formers' and the constructors' types are fvar-free, the classes scoped. -/
theorem checkBlockPassS_run {env : Env} (henv : EnvWF env)
    {p₀ : BlockShape} (hdecl : ∀ ms ∈ p₀.members, MemberDeclaredWF env ms) {isRec : Bool}
    {s₀ : CState} (hs : CSOK .verified false env s₀)
    {q : BlockPass FEnv} {s' : CState}
    (h : checkBlockPassS .verified (mkFEnv env) p₀ isRec s₀ = .ok (q, s')) :
    ∃ env₁ : Env, q.env₁ = mkFEnv env₁ ∧ CSOK .verified false env₁ s' ∧ EnvWF env₁ ∧
      (∀ cv ∈ q.p.formers, WScoped 0 cv.type) ∧
      (∀ ctorList ∈ q.p.memberCtors, ∀ c ∈ ctorList, WScoped 0 c.1.type) ∧
      (∀ ctorList ∈ q.p.memberCtors, ∀ c ∈ ctorList, env₁.find? c.1.name = none) ∧
      EnvWF (consBlockCtors q.p.nP q.p.memberCtors env₁) ∧
      (∀ M ∈ q.cls, ClassMajScoped q.p.nP M) ∧ q.params.length = q.p.nP ∧
      ∃ F, (checkBlockPass (fueledOpsM .verified) env p₀ isRec).val F
        = .ok ⟨env₁, q.p, q.kinds, q.params, q.rd, q.cls, q.tbl⟩ := by
  unfold checkBlockPassS at h
  rw [checkBlockIndsF_eqC] at h
  simp only [bind_assoc, pure_bind] at h
  obtain ⟨r₁, s₁, hind, h⟩ := bindC_ok h
  obtain ⟨hs₁, F₁, hF₁⟩ := triple_iff_run.mp (checkBlockIndsS_spec henv hs) r₁ s₁ hind
  obtain ⟨env₁, p₁⟩ := r₁
  have hF₁p : checkBlockInds (fueledOps .verified F₁) env p₀ isRec = .ok (env₁, p₁) := by
    rw [← checkBlockInds_datF]; exact hF₁
  obtain ⟨henv₁, hTf⟩ := direct_block_inds_wf henv hdecl hF₁p
  have hmem := checkBlockInds_members hF₁p
  have hfor : p₁.formers = p₀.formers := by
    show p₁.members.map _ = p₀.members.map _
    rw [hmem]
  have hwT : ∀ cv ∈ p₁.formers, WScoped 0 cv.type := fun cv hcv =>
    WScoped.of_not_hasFvar (hTf cv (hfor ▸ hcv))
  have hMc : ∀ ms ∈ p₁.members, ms.cvT.type.hasFvar = false :=
    fun ms hms => hTf _ (hfor ▸ List.mem_map_of_mem hms)
  try simp only at h
  obtain ⟨uB, sB, hflB, h⟩ := bindC_ok h
  rw [flushC_run] at hflB
  injection hflB with hflB
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hflB
  simp only [mkFEnv_find?_fun, mkFEnv_env] at h
  rw [checkBlockCtorsF_eqC] at h
  obtain ⟨u₂, s₂, hct, h⟩ := bindC_ok h
  cases u₂
  obtain ⟨hs₂, F₂, hF₂⟩ :=
    triple_iff_run.mp (checkBlockCtorsS_spec henv₁ hMc (flushC_csok hs₁.residue)) () s₂ hct
  have hF₂p : checkBlockCtors (fueledOps .verified F₂) env₁ env₁ p₁
      p₁.members = .ok () := by
    rw [← checkBlockCtors_datF]; exact hF₂
  obtain ⟨_, hF₂r⟩ := checkBlockCtors_inv hF₂p
  try simp only at h
  -- the walk's context
  obtain ⟨rc, sX, hX, h⟩ := bindC_ok h
  obtain ⟨hsX, ⟨FX, hFX⟩, hctx, hholes, hpar, hlen, hh, hnP⟩ := triple_iff_run.mp
    (blockNestCtxS_spec₂ henv₁ p₁ hMc hwT hs₂) rc sX hX
  rcases rc with ⟨ctx, holes⟩
  dsimp only at hctx hholes hpar hlen hh hnP h
  try simp only at h
  -- the classes
  obtain ⟨rcl, sL, hL, h⟩ := bindC_ok h
  have hpl : ctx.params.length = p₁.nP := by rw [hlen, hnP]
  obtain ⟨hsL, ⟨FL, hFL⟩, hMsc⟩ := triple_iff_run.mp
    (checkBlockClassesS_spec henv₁ hpl hpar hsX) rcl sL hL
  rcases rcl with ⟨rd, Ms⟩
  try simp only at h
  -- the positivity function on the stored constructors (the root frame)
  obtain ⟨⟨outs, pos⟩, sK, hK, h⟩ := bindC_ok h
  obtain ⟨hsK, FK, hFK⟩ := triple_iff_run.mp
    (checkBlockPositivityS_spec henv₁ p₁ hMc hwT
      (checkBlockCtors_types hF₂p) hsL) (outs, pos) sK hK
  try simp only at h
  -- every outside class, walked from its state
  obtain ⟨st, sT, hT', h⟩ := bindC_ok h
  have hpar' : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x := fun x hx =>
    WScoped.mono (by rw [← hnP]; simp [NestCtx.hiAt]) (hpar x hx)
  obtain ⟨hsT, FT, hFT⟩ := triple_iff_run.mp
    (nestSeedsS_spec henv₁ hctx _ pos hsK (fun k hk x hx => by
      obtain ⟨M, hM, hMn, rfl⟩ := mem_classSeeds hk
      exact (nestSeedOf_ds hh hlen (fun y hy => Expr.fvarB_le (by
        rw [hnP]; exact (((hMsc M hM).2.1 hMn).2 y hy).2)) x hx).2 (fun y hy => (hholes y hy).1)
        hpar')) st sT hT'
  obtain ⟨rfl, rfl⟩ := pureC_ok h
  obtain ⟨G, hle₁, hle₂, hleX, hleL, hleK, hleT⟩ :
      ∃ G, F₁ ≤ G ∧ F₂ ≤ G ∧ FX ≤ G ∧ FL ≤ G ∧ FK ≤ G ∧ FT ≤ G :=
    ⟨max F₁ (max F₂ (max FX (max FL (max FK FT)))), by omega, by omega, by omega, by omega,
      by omega, by omega⟩
  refine ⟨env₁, rfl, hsT, henv₁, hwT, checkBlockCtors_types hF₂p, checkBlockCtors_fresh hF₂r,
    direct_block_ctors_wf henv₁ hF₂r, hMsc, hpl, G, ?_⟩
  have g₁ : checkBlockInds (fueledOps .verified G) env p₀ isRec = .ok (env₁, p₁) := by
    rw [← checkBlockInds_datF]; exact FueledM.up hle₁ hF₁
  have g₂ : checkBlockCtors (fueledOps .verified G) env₁ env₁ p₁
      p₁.members = .ok () := by
    rw [← checkBlockCtors_datF]; exact FueledM.up hle₂ hF₂
  have gX : blockNestCtx (m := CheckM) p₁ env₁.find? = .ok (ctx, holes) := by
    rw [← blockNestCtx_datF (F := G)]; exact FueledM.up hleX hFX
  have gL : checkBlockClasses (fueledOps .verified G) (mkFEnv env₁)
      p₁ ctx.params
      = .ok (rd, Ms) := by
    rw [← checkBlockClasses_datF]; exact FueledM.up hleL hFL
  have gK : checkBlockPositivity (fueledOps .verified G) env₁ env₁.find?
      p₁ = .ok (outs, pos) := by
    rw [← checkBlockPositivity_datF]; exact FueledM.up hleK hFK
  have gT : nestSeeds (fueledOps .verified G) env₁ ctx (classSeeds ctx holes Ms) pos = .ok st := by
    rw [← nestSeeds_datF]; exact FueledM.up hleT hFT
  rw [checkBlockPass_datF]
  unfold checkBlockPass
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  rw [g₂]
  simp only [Except.bind]
  rw [gX]
  simp only [Except.bind]
  rw [gL]
  simp only [Except.bind]
  rw [gK]
  simp only [Except.bind]
  rw [gT]

/-- A member's reduction is its pure original at the cached operations. -/
theorem reduceMemberS_eq (env : Env) (ms : MemberShape) (nP : Nat) :
    reduceMemberS .verified (mkFEnv env) ms nP =
      reduceMember (sharedOpsC .verified (mkFEnv env)) env ms nP := by
  simp only [reduceMemberS, reduceMember, checkConstantValF_eq, mkFEnv_env]

/-- `reducedFormerS_spec`, its result scoped. -/
theorem reducedFormerWS_spec (henv : EnvWF env) {cv : ConstantVal} {n : Nat} {s₀ : CState}
    (hw : WScoped 0 cv.type) (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ reducedFormer (sharedOpsC .verified (mkFEnv env)) env cv n
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (reducedFormer (fueledOpsM .verified) env cv n) v ∧ WScoped 0 v.type; ⊤⦄ :=
  triple_iff_run.mpr fun v s' hr => by
    obtain ⟨h₁, h₂, h₃⟩ := triple_iff_run.mp (reducedFormerS_spec henv hw hs) v s' hr
    exact ⟨h₁, h₂, WScoped.of_not_hasFvar h₃⟩

/-- A member's reduction at the cached operations simulates its fueled original. -/
theorem reduceMemberS_spec (henv : EnvWF env) {nP : Nat} {ms : MemberShape} {s₀ : CState}
    (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ reduceMemberS .verified (mkFEnv env) ms nP
    ⦃fun v s' => CSOK .verified false env s' ∧
      Runs (reduceMember (fueledOpsM .verified) env ms nP) v; ⊤⦄ := by
  rw [reduceMemberS_eq]
  sym only [conleche_grind, reduceMember] =>
    vcgen [reduceMember, reducedFormerWS_spec henv, checkConstantValS_spec henv,
      defeqS_spec henv] <;> finish

theorem reduceMembersS_run (henv : EnvWF env) {nP : Nat} :
    ∀ {l l' : List MemberShape} {s₀ s' : CState}, CSOKF s₀ →
      reduceMembersS .verified (mkFEnv env) nP l s₀ = .ok (l', s') →
      CSOKF s' ∧ ∃ F, reduceMembers (fueledOps .verified F) env nP l = .ok l'
  | [], l', s₀, s', hs, h => by
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hs, 0, rfl⟩
  | ms :: rest, l', s₀, s', hs, h => by
    unfold reduceMembersS at h
    obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
    rw [flushC_run] at hfl0
    injection hfl0 with hfl0
    obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
    obtain ⟨m', s₁, hm, h⟩ := bindC_ok h
    obtain ⟨hs₁, F₁, hF₁⟩ :=
      triple_iff_run.mp (reduceMemberS_spec henv (flushC_csok hs)) m' s₁ hm
    obtain ⟨r', s₂, hr, h⟩ := bindC_ok h
    obtain ⟨hs₂, F₂, hF₂⟩ := reduceMembersS_run henv hs₁.residue hr
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    refine ⟨hs₂, max F₁ F₂, ?_⟩
    have g₁ : reduceMember (fueledOps .verified (max F₁ F₂)) env ms nP = .ok m' := by
      rw [← reduceMember_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
    have g₂ : reduceMembers (fueledOps .verified (max F₁ F₂)) env nP rest = .ok r' := by
      rw [← reduceMembers_datF]
      exact FueledM.up (Nat.le_max_right _ _) (by rw [reduceMembers_datF]; exact hF₂)
    unfold reduceMembers
    simp only [Bind.bind, Except.bind, g₁, g₂]
    rfl

/-- **The uniform install at k members, at the cached driver**, is reproduced by the pure
fueled `checkBlock`. -/
theorem checkBlockKS_run
    {env : Env} (henv : EnvWF env) {block : List ConstantInfo} {p₀ : BlockShape}
    (hd : ∀ ms ∈ p₀.members, ms.declared = ms.cvT)
    {s₀ : CState} (hwf : CSOKF s₀) {feOut : FEnv} {s' : CState}
    (h : checkBlockKS .verified (mkFEnv env) block p₀ s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkBlock (fueledOps .verified F) env block p₀ = .ok feOut.env := by
  unfold checkBlockKS at h
  by_cases hnd : (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup
  case neg => rw [ite_eq_right hnd] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_left hnd] at h
  by_cases hbool : boolTrueName ∉ p₀.memberNames ∧ boolFalseName ∉ p₀.memberNames
  case neg => rw [ite_eq_right hbool] at h; exact absurd h throwC_bind_ok
  rw [ite_eq_left hbool] at h
  obtain ⟨ms, s₁, hms, h⟩ := bindC_ok h
  obtain ⟨hs₁, F₁, hF₁⟩ := reduceMembersS_run henv hwf hms
  obtain ⟨hAt, -⟩ := ConLeche.reduceMembers_inv hd hF₁
  obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
  rw [flushC_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₁.flushed = sA := congrArg Prod.snd hfl0
  obtain ⟨r, s₂, hP, h⟩ := bindC_ok h
  obtain ⟨fe₁, p, kinds, params, rd, Ms₀, tbl⟩ := r
  obtain ⟨env₁, hq₁, hs₂, henv₁, hT, -, -, henv₂, hMs₀, hpl, F₂, hF₂⟩ :=
    checkBlockPassS_run henv (fun m hm => (hAt m hm).declaredWF) (flushC_csok hs₁) hP
  simp only at hq₁ hs₂ henv₁ hT henv₂ hMs₀ hpl hF₂
  subst hq₁
  obtain ⟨u₃, s₃, hTail, h⟩ := bindC_ok h
  obtain ⟨hwfO, F₃, hF₃⟩ := checkBlockTailS_run henv₁ hT henv₂ hMs₀ hpl hs₂ hTail
  obtain ⟨rfl, rfl⟩ := pureC_ok h
  refine ⟨hwfO, by rw [pushDelta_mkFEnv, mkFEnv_env], max F₁ (max F₂ F₃), ?_⟩
  have g₁ : reduceMembers (fueledOps .verified (max F₁ (max F₂ F₃))) env p₀.nP p₀.members
      = .ok ms := by
    rw [← reduceMembers_datF]
    exact FueledM.up (Nat.le_max_left _ _) (by rw [reduceMembers_datF]; exact hF₁)
  have g₂ : checkBlockPass (fueledOps .verified (max F₁ (max F₂ F₃))) env
      { p₀ with members := ms } (blockIsRec p₀)
      = .ok ⟨env₁, p, kinds, params, rd, Ms₀, tbl⟩ := by
    rw [← checkBlockPass_datF]
    exact FueledM.up (Nat.le_trans (Nat.le_max_left F₂ F₃) (Nat.le_max_right F₁ _)) hF₂
  have g₃ : checkBlockTail (fueledOps .verified (max F₁ (max F₂ F₃))) block
      ⟨env₁, p, kinds, params, rd, Ms₀, tbl⟩
      = .ok () := by
    rw [← checkBlockTail_datF]
    exact FueledM.up (Nat.le_trans (Nat.le_max_right F₂ F₃) (Nat.le_max_right F₁ _)) hF₃
  unfold checkBlock
  simp only [ite_eq_left hnd, ite_eq_left hbool, Bind.bind, Except.bind, g₁, g₂, g₃]
  rw [pushDelta_mkFEnv, mkFEnv_env]
  rfl

variable {pins : List NatOpPinSet}

/-- The inductive-block dispatch of the cached driver: a RECOGNISED
block goes to `checkBlockKS`, every other one
is rejected with `readBlock`'s error, and the pure fueled `checkDeclKind`
reproduces the run. -/
theorem checkModeledOrNativeSF_run {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {nP : Nat}
    (hok : indParamsOk nP block = true)
    {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match readBlock nP block with
          | .ok p => checkBlockKS .verified (mkFEnv env) block p
          | .error e => throw e) s₀ =
      .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDeclKind (fueledOps .verified F) pins env (.indDecl block nP) =
      .ok feOut.env := by
  -- the declared parameter count (task #228) is a pure guard shared by
  -- the two drivers: `hok` is the branch both take
  show CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (if indParamsOk nP block = true then
          (match readBlock nP block with
            | .ok p => checkBlock (fueledOps .verified F) env block p
            | .error e => throw e)
        else throw (CheckError.invalid "number of parameters mismatch")) = .ok feOut.env
  simp only [ite_eq_left hok]
  cases hfp : readBlock nP block with
  | ok p =>
    rw [hfp] at h
    simp only at h
    -- the block install, at any number of members, nested included
    obtain ⟨hres, hfe, F, hF⟩ := checkBlockKS_run henv (ConLeche.readBlock_declared hfp) hwf h
    exact ⟨hres, hfe, F, hF⟩
  | error e =>
    rw [hfp] at h
    -- the reader's error never returns an index
    exact nomatch h

end ConLeche.Cached
