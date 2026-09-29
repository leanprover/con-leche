module

public import ConLeche.Verify.Cached.TargetRecC
public import ConLeche.Kernel.Inductives.GenRec
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Verify.BridgeDecl
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Cached.WalkersC
import ConLeche.Verify.Cached.AgreeFloor
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The cached recursor stage, bridged: the GENERATED stage

The generated recursor stage `genRecCheck`
(`ConLeche/Kernel/Inductives/GenRec.lean`) is written once over
`ShadowOps`: the pure install runs it at `ShadowOps.ofOps`
(`checkBlockRec`), the cached driver at `shadowOpsC` (`checkBlockTailS`).
This file proves the cached run reproduced by the pure fueled one
(`genRecCheckS_simG`, `genRecCheckS_run`), reusing the class kit's
per-operation simulations (`TargetRecC.lean`), and with it the cached
uniform install (`checkBlockTailS_run`, `checkBlockKS_run`) and the
`.indDecl` dispatch (`checkModeledOrNativeSF_run`).

Scoping, per cached operation:
* the stream's recursor types and the GENERATED types are closed by
  `checkConstantValF` itself; the comparison runs on two closed terms;
* the classes' parameters are the pre-pass's reading of a CHECKED
  (closed) recursor type, hence well scoped wherever they are
  (`classRead_keys_scoped`), and `targetMajorOf` checks them below the
  parameters — so every class is scoped by the parameter openers
  (`TargetMajScoped`), which is all the class match (`targetMajorNfs`,
  `targetK53`) and the pin typing need;
* each generated RULE is closed by `classRuleOk`'s own guard before it
  is annotated.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## 1. The pre-pass's classes are well scoped -/

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

/-- The slots read off a telescope scoped at `d`: every motive's key's
parameters are well scoped (at the depth of their binder). -/
theorem classReadSlots_keys_scoped (nPc : Name → Nat) (np : Nat) :
    ∀ (n : Nat) (motPos : List Nat) (d : Nat) (body : Expr) (slots : List ClassSlot),
      WScoped d body → classReadSlots nPc np n motPos d body = some slots →
      ∀ key, ClassSlot.motive key ∈ slots → ∀ x ∈ key.ds, ∃ D, WScoped D x
  | 0, _, _, _, slots, _, h => by
    simp only [classReadSlots, Option.some.injEq] at h
    subst h
    intro key hk
    exact nomatch hk
  | n + 1, motPos, d, .forallE dom body bm, slots, hw, h => by
    simp only [WScoped] at hw
    have hrec := fun motPos' rest (hrest : classReadSlots nPc np n motPos' (d + 1)
        (body.instantiate1 (.fvar d dom)) = some rest) =>
      classReadSlots_keys_scoped nPc np n motPos' (d + 1) _ rest
        (WScoped.instantiate1 hw.1 0 hw.2) hrest
    unfold classReadSlots at h
    dsimp only at h
    split at h
    · cases hl : dom.piBinders.fst.getLast? with
      | none => simp [hl] at h
      | some md =>
        obtain ⟨mdom, mb⟩ := md
        simp only [hl, Option.bind_eq_bind, Option.bind_some] at h
        split at h
        · simp only [Option.pure_def, Option.bind_some, Option.bind_eq_some_iff] at h
          obtain ⟨rest, hrest, h⟩ := h
          obtain rfl := Option.some.inj h
          intro key hk x hx
          rcases List.mem_cons.mp hk with hk | hk
          · simp only [ClassSlot.motive.injEq] at hk
            subst hk
            have hmdom : WScoped d mdom :=
              (piBinders_WScoped hw.1).1 _ (List.mem_of_getLast? hl)
            exact ⟨d, Expr.WScoped.getAppArgs hmdom x (List.mem_of_mem_take hx)⟩
          · exact hrec _ rest hrest key hk x hx
        · simp at h
    · cases hm : classReadMinor np motPos d dom with
      | none => simp [hm] at h
      | some slot =>
        simp only [hm, Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
        obtain ⟨rest, hrest, h⟩ := h
        obtain rfl := Option.some.inj h
        intro key hk x hx
        rcases List.mem_cons.mp hk with hk | hk
        · obtain ⟨c, C, ihs, rfl⟩ := classReadMinor_minor hm
          exact nomatch hk
        · exact hrec _ rest hrest key hk x hx
  | _ + 1, _, _, .bvar _, _, _, h | _ + 1, _, _, .fvar .., _, _, h
  | _ + 1, _, _, .sort _, _, _, h | _ + 1, _, _, .const .., _, _, h
  | _ + 1, _, _, .app .., _, _, h | _ + 1, _, _, .lam .., _, _, h
  | _ + 1, _, _, .letE .., _, _, h | _ + 1, _, _, .lit _, _, _, h
  | _ + 1, _, _, .proj .., _, _, h => by simp [classReadSlots] at h

/-- **The pre-pass's classes are well scoped** when the recursor types it
reads are closed. -/
theorem classRead_keys_scoped {nP : Nat} {nPc : Name → Nat} {recs : List RecShape}
    {rd : ClassRead} (hw : ∀ rc ∈ recs, WScoped 0 rc.cvR.type)
    (h : classRead nP nPc recs = some rd) :
    ∀ key ∈ rd.classes, ∀ x ∈ key.ds, ∃ D, WScoped D x := by
  unfold classRead at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨rc0, h0, ⟨pf, body⟩, hopen, slots, hslots, recCls, -, h⟩ := h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  have hw0 := hw rc0 (List.mem_of_mem_head? h0)
  have hb := (openPisAtFvars_WScoped nP _ 0 hopen hw0).2
  rw [Nat.zero_add] at hb
  intro key hk
  simp only [ClassRead.classes, List.mem_filterMap] at hk
  obtain ⟨s, hs, hks⟩ := hk
  split at hks
  · rename_i k
    obtain rfl := Option.some.inj hks
    exact classReadSlots_keys_scoped nPc nP _ [] nP body slots hb hslots k hs
  · exact nomatch hks

/-! ## 2. The stages, simulated -/

section Sims

variable {env : Env}

/-- `classMinorSlot` is operation-free. -/
theorem classMinorSlotS_sim {rd : ClassRead} {c : Nat} {C : Name} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (classMinorSlot (m := CheckCM) rd c C)
      (classMinorSlot (m := FueledM) rd c C) := by
  unfold classMinorSlot
  dsimp only
  split
  · exact SimC.pure hs rfl
  · exact SimC.throw

/-- `classFieldsOf` is operation-free. -/
theorem classFieldsOfS_sim {p : BlockShape} {ctor : Name} {ihs : List (Nat × Nat)} :
    ∀ (i : Nat) (fs : List Expr) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC (classFieldsOf (m := CheckCM) p ctor ihs i fs)
        (classFieldsOf (m := FueledM) p ctor ihs i fs)
  | _, [], _, hs => SimC.pure hs rfl
  | i, f :: fs, _, hs => by
    unfold classFieldsOf
    dsimp only
    split
    all_goals first
      | exact SimC.throw_bind
      | (refine SimC.bind (SimC.pure hs rfl) (fun s₁ k k' hs₁ hK => ?_)
         obtain rfl : k = k' := hK
         refine SimC.bind (classFieldsOfS_sim (i + 1) fs hs₁) (fun s₂ ks ks' hs₂ hKs => ?_)
         obtain rfl : ks = ks' := hKs
         exact SimC.pure hs₂ rfl)

/-- `classFormerTy` is operation-free. -/
theorem classFormerTyS_sim {fe : FEnv} {cvTas : List ConstantVal} {M : TargetMajor}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (classFormerTy (m := CheckCM) fe cvTas M)
      (classFormerTy (m := FueledM) fe cvTas M) := by
  unfold classFormerTy
  repeat' split
  all_goals first
    | exact SimC.pure hs rfl
    | exact SimC.throw

/-- `List.mapM`'s loop, simulated elementwise. -/
theorem mapMLoopS_sim {α β : Type} {f : α → CheckCM β} {g : α → FueledM β}
    (hf : ∀ a {s₀ : CState}, CSOK mode env s₀ → SimC mode env s₀ RelVC (f a) (g a)) :
    ∀ (l : List α) (bs : List β) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC (List.mapM.loop f l bs) (List.mapM.loop g l bs)
  | [], bs, _, hs => SimC.pure hs rfl
  | a :: l, bs, _, hs => by
    simp only [List.mapM.loop]
    refine SimC.bind (hf a hs) (fun s₁ b b' hs₁ hB => ?_)
    obtain rfl : b = b' := hB
    exact mapMLoopS_sim hf l (b :: bs) hs₁

/-- The classes' formers (`Ms.mapM classFormerTy`), operation-free. -/
theorem classFormerTysS_sim {fe : FEnv} {cvTas : List ConstantVal} (Ms : List TargetMajor)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (Ms.mapM (classFormerTy (m := CheckCM) fe cvTas))
      (Ms.mapM (classFormerTy (m := FueledM) fe cvTas)) :=
  mapMLoopS_sim (fun _ _ hs => classFormerTyS_sim hs) Ms [] hs

/-- The stream's recursor constants, checked: each closed. -/
theorem classStreamRecsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) :
    ∀ (recs : List RecShape) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ cv ∈ v, WScoped 0 cv.type)
        (classStreamRecs (sharedOpsC mode (mkFEnv env)) (mkFEnv env) recs)
        (classStreamRecs (fueledOpsM mode) (mkFEnv env) recs)
  | [], _, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | rc :: rcs, _, hs => by
    unfold classStreamRecs
    simp only [checkConstantValF_eq]
    refine SimC.bind (checkConstantValS_sim hμ henv hs) (fun s₁ cv cv' hs₁ hC => ?_)
    obtain ⟨rfl, hw⟩ := hC
    refine SimC.bind (classStreamRecsS_sim hμ henv rcs hs₁) (fun s₂ cvs cvs' hs₂ hCs => ?_)
    obtain ⟨rfl, hws⟩ := hCs
    refine SimC.pure hs₂ ⟨rfl, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw
    · exact hws x hx

/-- **What a class checked as a major is** (`targetMajorOf` at the class
application; the twin of `TargetRecC`'s shape lemma): a member at the
openers' parameters, or an outside inductive whose parameters are the
class's own, below the parameters. -/
private theorem classMajorOf_shape (fe : FEnv) (p : BlockShape)
    (ctorsAs : List (List (ConstantVal × Nat))) (pfvs fvs : List Expr) (mty : Expr) :
    Yields (targetMajorOf (m := CheckCM) fe p ctorsAs pfvs fvs mty)
      (fun M => M.pfvs = pfvs ∧ ((∃ t, M.member = some t ∧ M.ds = fvs.take p.nP) ∨
        (M.member = none ∧ ∀ x ∈ M.ds, x ∈ mty.getAppArgs ∧ x.fvarB ≤ p.nP))) := by
  unfold targetMajorOf
  dsimp only
  split
  · split
    · refine Yields.bind' Yields.unwrapOr fun ms _ => ?_
      refine Yields.bind' Yields.unwrapOr fun ctorsA _ => ?_
      split
      · exact Yields.pure ⟨rfl, Or.inl ⟨_, rfl, rfl⟩⟩
      · exact Yields.ofThrowBind
    · repeat' (first
        | exact Yields.ofThrow
        | exact Yields.ofThrowBind
        | (refine Yields.bind fun _ => ?_)
        | split)
      all_goals first
        | (refine Yields.pure ⟨rfl, Or.inr ⟨rfl, fun x hx => ⟨List.mem_of_mem_take hx, ?_⟩⟩⟩
           simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at *
           exact ((by assumption : _ ∧ ∀ y ∈ List.take _ mty.getAppArgs,
             y.bvarB = 0 ∧ y.fvarB ≤ p.nP).2 x hx).2)
  · exact Yields.ofThrow

/-- A class checked as a major, scoped: its openers are the parameter
openers `pfvs`, its parameters scoped by them, an outside class's below
the parameters. -/
@[expose] def ClassMajScoped (nP : Nat) (M : TargetMajor) : Prop :=
  TargetMajScoped M ∧ (M.member = none → ∀ x ∈ M.ds, x.fvarB ≤ nP) ∧ M.pfvs.length = nP

/-- `blockNestCtx` at the shared operations, its lookups the formers'
environment `env₁`, the state the constructors' environment's: the same
value, the canonical parameters scoped at the parameter count. -/
theorem blockNestCtxS_sim₂ {env₁ env₂ : Env} (henv₁ : EnvWF env₁) (p : BlockShape)
    (cvTas : List ConstantVal) (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) {s₀ : CState}
    (hs : CSOK mode env₂ s₀) :
    SimC mode env₂ s₀
      (fun v w => v = w ∧ NestCtxOk v.1 ∧
        (∀ x ∈ v.2, WScoped (v.1.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty) ∧
        (∀ x ∈ v.1.params, WScoped p.nP x) ∧ v.1.params.length = v.1.nP ∧
        nestHoles v.1 = some v.2 ∧ v.1.nP = p.nP)
      (blockNestCtx (m := CheckCM) p cvTas env₁.find? env₁.consts)
      (blockNestCtx (m := FueledM) p cvTas env₁.find? env₁.consts) := by
  unfold blockNestCtx
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ cvTa0 cvTa0' hs₁ hP => ?_)
  obtain ⟨rfl, h0⟩ := hP
  have hw0 : WScoped 0 cvTa0.type := hT _ (List.mem_of_mem_head? h0)
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ pq pq' hs₂ hP => ?_)
  obtain ⟨rfl, hpq⟩ := hP
  have hctx : NestCtxOk (p.nestCtx pq.1 env₁.find? env₁.consts) :=
    ⟨fun ci hci => (henv₁ ci hci).1,
      fun n ci hf => (henv₁ ci (List.mem_of_find?_eq_some hf)).1⟩
  have hpar : ∀ x ∈ pq.1, WScoped p.nP x := by
    intro x hx
    have := (openPisAtFvars_WScoped p.nP cvTa0.type 0 hpq hw0).1 x hx
    rwa [Nat.zero_add] at this
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ holes holes' hs₃ hP => ?_)
  obtain ⟨rfl, hh⟩ := hP
  exact SimC.pure hs₃ ⟨rfl, hctx, nestHoles_ok hctx hh, hpar,
    ConLeche.Verify.openPisAtFvars_length _ hpq, hh, rfl⟩

/-- **The classes, each checked as a major**: every class scoped. -/
theorem classMajorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs : List Expr}
    (hpl : pfvs.length = p.nP) (hp : ∀ x ∈ pfvs, WScoped p.nP x) :
    ∀ (keys : List ClassKey) {s₀ : CState}, CSOK mode env s₀ →
      (∀ key ∈ keys, ∀ x ∈ key.ds, ∃ D, WScoped D x) →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ M ∈ v, ClassMajScoped p.nP M)
        (classMajors (sharedOpsC mode (mkFEnv env)) (mkFEnv env) p ctorsAs pfvs keys)
        (classMajors (fueledOpsM mode) (mkFEnv env) p ctorsAs pfvs keys)
  | [], _, hs, _ => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | key :: keys, _, hs, hk => by
    unfold classMajors
    simp only [mkFEnv_env]
    refine SimC.bind ((targetMajorOfS_sim hs).withYields
      (classMajorOf_shape (mkFEnv env) p ctorsAs pfvs pfvs _)) (fun s₁ M M' hs₁ hM => ?_)
    obtain ⟨rfl, hMpf, hMsh⟩ := hM
    have hdsN : M.member = none → ∀ x ∈ M.ds, x.fvarB ≤ p.nP := by
      intro hMn x hx
      rcases hMsh with ⟨t, hmt, -⟩ | ⟨-, hall⟩
      · rw [hMn] at hmt; exact nomatch hmt
      · exact (hall x hx).2
    have hds : ∀ x ∈ M.ds, WScoped p.nP x := by
      intro x hx
      rcases hMsh with ⟨t, -, hMds⟩ | ⟨-, hall⟩
      · rw [hMds] at hx
        exact hp x (List.mem_of_mem_take hx)
      · obtain ⟨hxa, hfb⟩ := hall x hx
        rw [Expr.getAppArgs_mkAppN] at hxa
        simp only [Expr.getAppArgs, List.nil_append] at hxa
        obtain ⟨D, hD⟩ := hk key List.mem_cons_self x hxa
        exact ConLeche.WScoped.of_fvarsBelow hD (ConLeche.Expr.fvarB_le hfb)
    refine SimC.bind (targetMajorPinsS_sim hμ henv (fun _ => hds) hs₁)
      (fun s₂ _ _ hs₂ _ => ?_)
    refine SimC.bind (classMajorsS_sim hμ henv hpl hp keys hs₂
      (fun k hk' => hk k (List.mem_cons_of_mem _ hk'))) (fun s₃ Ms Ms' hs₃ hMs => ?_)
    obtain ⟨rfl, hMs⟩ := hMs
    refine SimC.pure hs₃ ⟨rfl, fun N hN => ?_⟩
    rcases List.mem_cons.mp hN with rfl | hN
    · refine ⟨⟨?_, ?_⟩, hdsN, by rw [hMpf, hpl]⟩
      · rw [hMpf, hpl]; exact hp
      · rw [hMpf, hpl]; exact hds
    · exact hMs N hN

/-- Every class's table entries: the classes stay scoped. -/
theorem classesNfsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t) {tbl : List NestCtorNf} :
    ∀ (Ms : List TargetMajor) {s₀ : CState}, CSOK mode env s₀ →
      (∀ M ∈ Ms, TargetMajScoped M) →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ M ∈ v, TargetMajScoped M)
        (classesNfs (sharedOpsC mode (mkFEnv env)) env p formerTys tbl Ms)
        (classesNfs (fueledOpsM mode) env p formerTys tbl Ms)
  | [], _, hs, _ => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | M :: Ms, _, hs, hsc => by
    unfold classesNfs
    obtain ⟨hp, hds⟩ := hsc M List.mem_cons_self
    refine SimC.bind (targetMajorNfsS_sim hμ henv hformer hp hds tbl hs)
      (fun s₁ es es' hs₁ hE => ?_)
    obtain rfl : es = es' := hE
    refine SimC.bind (classesNfsS_sim hμ henv hformer Ms hs₁
      (fun N hN => hsc N (List.mem_cons_of_mem _ hN))) (fun s₂ r r' hs₂ hR => ?_)
    obtain ⟨rfl, hr⟩ := hR
    refine SimC.pure hs₂ ⟨rfl, fun N hN => ?_⟩
    rcases List.mem_cons.mp hN with rfl | hN
    · exact ⟨hp, hds⟩
    · exact hr N hN

/-- Node agreement at one recursive field, at every entry. -/
theorem classNodesAgreeS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {Mc : TargetMajor} (hMc : TargetMajScoped Mc) {tele : List (Expr × BinderMeta)}
    {leaf : Expr} {fvs : List Expr} {i : Nat} {ctor : Name} :
    ∀ (es : List NestCtorNf) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (classNodesAgree (sharedOpsC mode (mkFEnv env)) env p formerTys Mc tele leaf fvs i ctor
          es)
        (classNodesAgree (fueledOpsM mode) env p formerTys Mc tele leaf fvs i ctor es)
  | [], _, hs => SimC.pure hs rfl
  | e :: es, _, hs => by
    unfold classNodesAgree
    split
    · refine SimC.bind (targetK53S_sim hμ henv hformer hMc hs) (fun s₁ b b' hs₁ hB => ?_)
      obtain rfl : b = b' := hB
      cases b
      · exact SimC.throw_bind
      · exact classNodesAgreeS_sim hμ henv hformer hMc es hs₁
    · exact SimC.throw

/-- Node agreement at every recursive field of the datum. -/
theorem classFieldsAgreeS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {Ms : List TargetMajor} (hMs : ∀ M ∈ Ms, TargetMajScoped M) {fvs : List Expr}
    {ctor : Name} {E : List NestCtorNf} :
    ∀ (i : Nat) (ks : List ClassField) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (classFieldsAgree (sharedOpsC mode (mkFEnv env)) env p formerTys Ms fvs ctor E i ks)
        (classFieldsAgree (fueledOpsM mode) env p formerTys Ms fvs ctor E i ks)
  | _, [], _, hs => SimC.pure hs rfl
  | i, .ordinary :: ks, _, hs => by
    unfold classFieldsAgree
    exact classFieldsAgreeS_sim hμ henv hformer hMs (i + 1) ks hs
  | i, .recursive t tele :: ks, _, hs => by
    unfold classFieldsAgree
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ x x' hs₁ hX => ?_)
    obtain ⟨rfl, -⟩ := hX
    rcases x with ⟨teleB, leaf⟩
    dsimp only
    by_cases hl : classLeafAt (Ms.getD t default) leaf = true
    case neg => simp only [hl, Bool.false_eq_true, if_false]; exact SimC.throw_bind
    simp only [hl, if_true]
    refine SimC.bind (classNodesAgreeS_sim hμ henv hformer (TargetMajScoped.getD hMs t) E hs₁)
      (fun s₂ u u' hs₂ hU => ?_)
    obtain rfl : u = u' := hU
    exact classFieldsAgreeS_sim hμ henv hformer hMs (i + 1) ks hs₂

/-- One constructor of a class, read for the generator. -/
theorem classCtorOfS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {rd : ClassRead} {Ms : List TargetMajor} (hMs : ∀ M ∈ Ms, TargetMajScoped M) {c : Nat}
    {cA : ConstantVal × Nat} {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (classCtorOf (sharedOpsC mode (mkFEnv env)) env p formerTys rd Ms c cA)
      (classCtorOf (fueledOpsM mode) env p formerTys rd Ms c cA) := by
  unfold classCtorOf
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ e0 e0' hs₁ hE => ?_)
  obtain ⟨rfl, -⟩ := hE
  refine SimC.bind (classMinorSlotS_sim hs₁) (fun s₂ si si' hs₂ hS => ?_)
  obtain rfl : si = si' := hS
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ o o' hs₃ hO => ?_)
  obtain ⟨rfl, -⟩ := hO
  dsimp only
  refine SimC.bind (classFieldsOfS_sim 0 _ hs₃) (fun s₄ ks ks' hs₄ hK => ?_)
  obtain rfl : ks = ks' := hK
  refine SimC.bind (classFieldsAgreeS_sim hμ henv hformer hMs 0 ks hs₄)
    (fun s₅ u u' hs₅ hU => ?_)
  obtain rfl : u = u' := hU
  refine SimC.bind (SimC.unwrapOr' hs₅) (fun s₆ tyD tyD' hs₆ hT => ?_)
  obtain ⟨rfl, -⟩ := hT
  exact SimC.pure hs₆ rfl

theorem classCtorsOfS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {rd : ClassRead} {Ms : List TargetMajor} (hMs : ∀ M ∈ Ms, TargetMajScoped M) {c : Nat} :
    ∀ (cs : List (ConstantVal × Nat)) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (classCtorsOf (sharedOpsC mode (mkFEnv env)) env p formerTys rd Ms c cs)
        (classCtorsOf (fueledOpsM mode) env p formerTys rd Ms c cs)
  | [], _, hs => SimC.pure hs rfl
  | cA :: cs, _, hs => by
    unfold classCtorsOf
    refine SimC.bind (classCtorOfS_sim hμ henv hformer hMs hs) (fun s₁ x x' hs₁ hX => ?_)
    obtain rfl : x = x' := hX
    refine SimC.bind (classCtorsOfS_sim hμ henv hformer hMs cs hs₁)
      (fun s₂ xs xs' hs₂ hXs => ?_)
    obtain rfl : xs = xs' := hXs
    exact SimC.pure hs₂ rfl

theorem classesCtorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {rd : ClassRead} {Ms : List TargetMajor} (hMs : ∀ M ∈ Ms, TargetMajScoped M) :
    ∀ (c : Nat) (l : List TargetMajor) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (classesCtors (sharedOpsC mode (mkFEnv env)) env p formerTys rd Ms c l)
        (classesCtors (fueledOpsM mode) env p formerTys rd Ms c l)
  | _, [], _, hs => SimC.pure hs rfl
  | c, M :: rest, _, hs => by
    unfold classesCtors
    refine SimC.bind (classCtorsOfS_sim hμ henv hformer hMs _ hs) (fun s₁ x x' hs₁ hX => ?_)
    obtain rfl : x = x' := hX
    refine SimC.bind (classesCtorsS_sim hμ henv hformer hMs (c + 1) rest hs₁)
      (fun s₂ xs xs' hs₂ hXs => ?_)
    obtain rfl : xs = xs' := hXs
    exact SimC.pure hs₂ rfl

/-- **A generated constant, checked** (`classConstOk`): the cached twin
of `checkConstantValS_sim` without the annotation step — the stored
constant is the input, closed by the guard. -/
theorem classConstOkS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {cv : ConstantVal}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 v.type)
      (classConstOk (sharedOpsC mode (mkFEnv env)) (mkFEnv env) cv)
      (classConstOk (fueledOpsM mode) (mkFEnv env) cv) := by
  unfold classConstOk
  simp only [mkFEnv_find?, constsResolveF_eq, mkFEnv_env]
  dsimp only [sharedOpsC]
  by_cases h1 : (env.find? cv.name).isSome = true
  · simp only [if_pos h1]; exact SimC.throw_bind
  simp only [if_neg h1]
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · simp only [if_pos h2]; exact SimC.throw_bind
  simp only [if_neg h2]
  by_cases h3 : cv.name.isProjFnShape = true
  · simp only [if_pos h3]; exact SimC.throw_bind
  simp only [if_neg h3]
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => simp only [if_neg h5]; exact SimC.throw_bind
  simp only [if_pos h5]
  by_cases h6 : cv.type.hasFvar = true
  · simp only [if_pos h6]; exact SimC.throw_bind
  simp only [if_neg h6]
  have hwty : WScoped 0 cv.type := WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6)
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams cv.type = true
  case neg => simp only [if_neg h7]; exact SimC.throw_bind
  simp only [if_pos h7]
  by_cases h8 : Expr.constsResolve env cv.type = true
  case neg => simp only [if_neg h8]; exact SimC.throw_bind
  simp only [if_pos h8]
  refine SimC.bind (opE_infer_sim hμ henv hs hwty) (fun s₂ sty sty' hs₂ hP₂ => ?_)
  obtain ⟨rfl, hwsty⟩ := hP₂
  refine SimC.bind (opS_sim hμ henv hs₂ hwsty) (fun s₃ u u' hs₃ hP₃ => ?_)
  exact SimC.pure hs₃ ⟨rfl, hwty⟩

/-- **One recursor's generated type, checked and compared**: the stored
constant is closed. -/
theorem classRecTyOkS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {g : ClassGen}
    {k : Nat} {rc : RecShape} {cvRi : ConstantVal} {c : Nat} (hRi : WScoped 0 cvRi.type)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 v.type)
      (classRecTyOk (sharedOpsC mode (mkFEnv env)) (mkFEnv env) g k rc cvRi c)
      (classRecTyOk (fueledOpsM mode) (mkFEnv env) g k rc cvRi c) := by
  unfold classRecTyOk
  simp only [mkFEnv_env]
  split
  case isFalse => exact SimC.throw_bind
  split
  case isFalse => exact SimC.throw_bind
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ gty gty' hs₁ hG => ?_)
  obtain ⟨rfl, -⟩ := hG
  refine SimC.bind (classConstOkS_sim hμ henv hs₁) (fun s₂ cvG cvG' hs₂ hC => ?_)
  obtain ⟨rfl, hwG⟩ := hC
  dsimp only [sharedOpsC]
  refine SimC.bind (opB_sim hμ henv hs₂ hRi hwG) (fun s₃ b b' hs₃ hB => ?_)
  obtain rfl : b = b' := hB
  cases b
  · exact SimC.throw_bind
  · exact SimC.pure hs₃ ⟨rfl, hwG⟩

theorem classRecTysOkS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {g : ClassGen}
    {k : Nat} :
    ∀ (recs : List RecShape) (cvs : List ConstantVal) (cls : List Nat) {s₀ : CState},
      CSOK mode env s₀ → (∀ cv ∈ cvs, WScoped 0 cv.type) →
      SimC mode env s₀ RelVC
        (classRecTysOk (sharedOpsC mode (mkFEnv env)) (mkFEnv env) g k recs cvs cls)
        (classRecTysOk (fueledOpsM mode) (mkFEnv env) g k recs cvs cls)
  | rc :: rcs, cvRi :: cvs, c :: cs, _, hs, hw => by
    unfold classRecTysOk
    refine SimC.bind (classRecTyOkS_sim hμ henv (hw cvRi List.mem_cons_self) hs)
      (fun s₁ x x' hs₁ hX => ?_)
    obtain ⟨rfl, -⟩ := hX
    refine SimC.bind (classRecTysOkS_sim hμ henv rcs cvs cs hs₁
      (fun cv hcv => hw cv (List.mem_cons_of_mem _ hcv))) (fun s₂ xs xs' hs₂ hXs => ?_)
    obtain rfl : xs = xs' := hXs
    exact SimC.pure hs₂ rfl
  | [], _, _, _, hs, _ => SimC.pure hs rfl
  | _ :: _, [], _, _, _, _ => SimC.throw
  | _ :: _, _ :: _, [], _, _, _ => SimC.throw

end Sims

/-! ### The rule stage: two environments, one state (`SimG`) -/

/-- A FLUSHED state: an invariant state of every environment (what a
flush hands on). -/
@[expose] def CSOKAll (mode : CheckMode) (s : CState) : Prop := ∀ env', CSOK mode env' s

theorem CSOKAll.residue {s : CState} (h : CSOKAll mode s) : CSOKF s := (h default).residue

/-- A flush into every environment's invariant. -/
theorem flushC_simG_all : SimG CSOKF (CSOKAll mode) RelVC flushC (Pure.pure () : FueledM Unit) := by
  intro s₀ hs v' s' hr
  rw [flushC_run] at hr
  injection hr with hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨fun _ => flushC_csok hs, (), rfl, 0, rfl⟩

/-- The rule stage's `inferType` from a flushed state: it flushes last. -/
theorem ruleR_infer_simG_all (hμ : mode.verifiedChecks = true) {envR : Env} (henvR : EnvWF envR)
    {d : Nat} {e : Expr} (hw : WScoped d e) :
    SimG (CSOKAll mode) (CSOKAll mode) (RelW d)
      ((sharedOpsRuleR mode (mkFEnv envR)).inferType envR d e)
      ((fueledOpsM mode).inferType envR d e) := by
  intro s₀ hs v' s' hr
  obtain ⟨-, h2⟩ := ruleR_infer_simG hμ henvR envR hw s₀ (hs envR) v' s' hr
  exact ⟨fun env' => (ruleR_infer_simG hμ henvR env' hw s₀ (hs envR) v' s' hr).1, h2⟩

/-- **One generated rule, simulated.**  From a flushed state: the rule,
closed by the stage's own guard, stored as generated and typed at the
rule-less recursors' environment `envR` (`sharedOpsRuleR`'s inference
flushes last), its λ-telescope read syntactically. -/
theorem classRuleOkS_simG (hμ : mode.verifiedChecks = true) {envR : Env} (henvR : EnvWF envR)
    (envT : Env) {cvR : ConstantVal} {pw : PropWhen} {n : Nat} {gen : Expr} :
    SimG (CSOKAll mode) (CSOKAll mode) RelVC
      (classRuleOk (sharedOpsRuleR mode (mkFEnv envR)) .plain (mkFEnv envT) (mkFEnv envR) cvR
        pw n gen)
      (classRuleOk (fueledOpsM mode) .plain (mkFEnv envT) (mkFEnv envR) cvR pw n gen) := by
  unfold classRuleOk
  simp only [mkFEnv_env]
  by_cases h1 : (gen.looseBVarsBounded 0 && !gen.hasFvar) = true
  case neg => simp only [h1]; exact SimG.throw_bind
  simp only [h1, if_true]
  have hw : WScoped 0 gen := WScoped.of_not_hasFvar (by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at h1; exact h1.2)
  by_cases h3 : allLevelParamsDefined cvR.levelParams gen = true
  case neg => simp only [h3]; exact SimG.throw_bind
  simp only [h3, if_true]
  by_cases h4 : StructWalkers.plain.resolve (mkFEnv envR) gen = true
  case neg => simp only [h4]; exact SimG.throw_bind
  simp only [h4, if_true]
  refine SimG.bind (ruleR_infer_simG_all hμ henvR hw) (fun _ _ _ => ?_)
  refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun x x' hX => ?_)
  obtain ⟨rfl, -⟩ := hX
  obtain ⟨rbs, body⟩ := x
  dsimp only
  by_cases h5 : (rbs.all fun b => StructWalkers.plain.resolve (mkFEnv envT) b.1) = true
  case neg => simp only [h5]; exact SimG.throw_bind
  simp only [h5, if_true]
  by_cases h6 : (rbs.all fun b => b.2.pw == pw) = true
  case neg => simp only [h6]; exact SimG.throw_bind
  simp only [h6, if_true]
  exact SimG.pure (fun _ h => h) rfl

theorem classRulesOkS_simG (hμ : mode.verifiedChecks = true) {envR envT : Env}
    (henvR : EnvWF envR) {g : ClassGen} {recOf : Nat → Option Name} {cvR : ConstantVal}
    {pw : PropWhen} {c : Nat} :
    ∀ (xs : List ClassCtor),
      SimG (CSOKAll mode) (CSOKAll mode) RelVC
        (classRulesOk (sharedOpsRuleR mode (mkFEnv envR)) .plain (mkFEnv envT) (mkFEnv envR) g
          recOf cvR pw c xs)
        (classRulesOk (fueledOpsM mode) .plain (mkFEnv envT) (mkFEnv envR) g recOf cvR pw c xs)
  | [] => SimG.pure (fun _ h => h) rfl
  | x :: xs => by
    unfold classRulesOk
    refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun gen gen' hG => ?_)
    obtain ⟨rfl, -⟩ := hG
    refine SimG.bind (classRuleOkS_simG hμ henvR envT) (fun r r' hR => ?_)
    obtain rfl : r = r' := hR
    refine SimG.bind (classRulesOkS_simG hμ henvR xs) (fun rs rs' hRs => ?_)
    obtain rfl : rs = rs' := hRs
    exact SimG.pure (fun _ h => h) rfl

theorem classRecsRulesOkS_simG (hμ : mode.verifiedChecks = true) {envR envT : Env}
    (henvR : EnvWF envR) {g : ClassGen} {recOf : Nat → Option Name} {pw : PropWhen} :
    ∀ (cvs : List ConstantVal) (cs : List Nat),
      SimG (CSOKAll mode) (CSOKAll mode) RelVC
        (classRecsRulesOk (sharedOpsRuleR mode (mkFEnv envR)) .plain (mkFEnv envT) (mkFEnv envR)
          g recOf pw cvs cs)
        (classRecsRulesOk (fueledOpsM mode) .plain (mkFEnv envT) (mkFEnv envR) g recOf pw cvs
          cs)
  | cvG :: cvs, c :: cs => by
    unfold classRecsRulesOk
    refine SimG.bind (classRulesOkS_simG (envT := envT) hμ henvR _) (fun r r' hR => ?_)
    obtain rfl : r = r' := hR
    refine SimG.bind (classRecsRulesOkS_simG hμ henvR cvs cs) (fun rs rs' hRs => ?_)
    obtain rfl : rs = rs' := hRs
    exact SimG.pure (fun _ h => h) rfl
  | [], _ => SimG.pure (fun _ h => h) rfl
  | _ :: _, [] => SimG.pure (fun _ h => h) rfl

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

/-- **The generated recursor stage at the cached driver, simulated**:
from an invariant state of the constructors' environment to a residue.
The seeds are walked at a view of the index that looks names up as the
formers' environment (`hfe₁`), from a flushed state, the walk's state
`pos` closed (`NestStOk`). -/
theorem genRecCheckS_simG (hμ : mode.verifiedChecks = true) {env₁ env₂ : Env} {fe₁ : FEnv}
    (henv₁ : EnvWF env₁) (henv₂ : EnvWF env₂) (hfe₁ : fe₁.find? = (mkFEnv env₁).find?)
    {p : BlockShape} {nestedBit : Bool} {pos : NestState} (hpos : NestStOk pos)
    {cvTas : List ConstantVal} {block : List ConstantInfo}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) :
    SimG (CSOK mode env₂) CSOKF RelVC
      (genRecCheck (shadowOpsC mode) fe₁ env₁ (mkFEnv env₂) p nestedBit pos cvTas block
        ctorsAs)
      (genRecCheck (ShadowOps.ofOps (fueledOpsM mode)) fe₁ env₁ (mkFEnv env₂) p nestedBit
        pos cvTas block ctorsAs) := by
  unfold genRecCheck
  have hso : ∀ fe, (shadowOpsC mode).opsAt fe = sharedOpsC mode fe := fun _ => rfl
  have hsf : (shadowOpsC mode).flush = flushC := rfl
  have hsw : (shadowOpsC mode).walkers = structWalkersC := rfl
  have hsr : ∀ fe, (shadowOpsC mode).opsRuleR fe = sharedOpsRuleR mode fe := fun _ => rfl
  have hpo : ∀ fe, (ShadowOps.ofOps (fueledOpsM mode)).opsAt fe = fueledOpsM mode :=
    fun _ => rfl
  have hpr : ∀ fe, (ShadowOps.ofOps (fueledOpsM mode)).opsRuleR fe = fueledOpsM mode :=
    fun _ => rfl
  have hpw : (ShadowOps.ofOps (fueledOpsM mode)).walkers = .plain := rfl
  have hpf : (ShadowOps.ofOps (fueledOpsM mode)).flush = (Pure.pure () : FueledM Unit) := rfl
  simp only [hso, hsf, hsw, hsr, hpo, hpr, hpw, hpf, structWalkersC_eq_plain, mkFEnv_env,
    classFeR, consBlockRecsBareF_mkFEnv]
  rw [sharedOpsC_congr hfe₁, hfe₁, mkFEnv_find?_fun]
  have hformer : ∀ t ∈ cvTas.map (·.type), WScoped 0 t := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    exact hT cv hcv
  refine SimG.bind (SimG.ofC fun s hs => targetRecPinsS_sim hs) fun _ _ _ => ?_
  refine SimG.bind (SimG.ofC fun s hs => classStreamRecsS_sim hμ henv₂ p.recs hs)
    fun cvRis cvRis' hC => ?_
  obtain ⟨rfl, hwRis⟩ := hC
  refine SimG.bind (SimG.ofC fun s hs => SimC.unwrapOr' hs) fun rd rd' hR => ?_
  obtain ⟨rfl, hrd⟩ := hR
  refine SimG.bind (SimG.ofC fun s hs => blockNestCtxS_sim₂ henv₁ p cvTas hT hs)
    fun r r' hR => ?_
  obtain ⟨rfl, hctx, hholes, hpar, hlen, hh, hnP⟩ := hR
  rcases r with ⟨ctx, holes⟩
  dsimp only at hctx hholes hpar hlen hh hnP ⊢
  -- the pre-pass's classes, scoped, and moved to the canonical parameters
  have hkeys₀ : ∀ key ∈ rd.classes, ∀ x ∈ key.ds, ∃ D, WScoped D x := by
    refine classRead_keys_scoped (fun rc hrc => ?_) hrd
    obtain ⟨⟨rc', cv⟩, hmem, rfl⟩ := List.mem_map.mp hrc
    exact hwRis cv (List.of_mem_zip hmem).2
  have hkeys : ∀ key ∈ rd.classes.map (classKeyCanon ctx.params), ∀ x ∈ key.ds,
      ∃ D, WScoped D x := by
    intro key hkey x hx
    obtain ⟨k0, hk0, rfl⟩ := List.mem_map.mp hkey
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    obtain ⟨D, hD⟩ := hkeys₀ k0 hk0 y hy
    refine ⟨max D p.nP, replaceFVars_WScoped (fun i r hr => ?_) _
      (WScoped.mono (Nat.le_max_left _ _) hD)⟩
    exact WScoped.mono (Nat.le_max_right _ _) (hpar r (List.mem_of_getElem? hr))
  have hpl : ctx.params.length = p.nP := by rw [hlen, hnP]
  have hp : ∀ x ∈ ctx.params, WScoped p.nP x := hpar
  refine SimG.bind (SimG.ofC fun s hs => classMajorsS_sim hμ henv₂ hpl hp _ hs hkeys)
    fun Ms₀ Ms₀' hM => ?_
  obtain ⟨rfl, hMs₀⟩ := hM
  by_cases h1 : ((List.range p.k).all fun t =>
      (List.filter (fun x => x.member == some t) Ms₀).length == 1) = true
  case neg => simp only [h1]; exact SimG.throw_bind
  simp only [h1, if_true]
  by_cases h2 : 0 < p.k
  case neg => simp only [h2, if_false]; exact SimG.throw_bind
  simp only [h2, if_true]
  by_cases h3 : (p.large && !blockLargeElimAllowed p (nestedBit || Ms₀.any fun x =>
      x.member.isNone)) = true
  case pos => simp only [h3, if_true]; exact SimG.throw_bind
  simp only [h3]
  -- the seeds, at the formers' environment
  refine SimG.bind (flushC_simG_to (mode := mode)
    (fun s h => (h : CSOK mode env₂ s).residue) env₁) fun _ _ _ => ?_
  have hpar' : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x := fun x hx =>
    WScoped.mono (by rw [← hnP]; simp [NestCtx.hiAt]) (hpar x hx)
  refine SimG.bind (SimG.ofC fun s hs => nestSeedsS_sim hμ henv₁ hctx _ pos hs
    (fun k hk x hx => ?_) hpos) fun st st' hS => ?_
  · obtain ⟨M, hM, hMn, rfl⟩ := mem_classSeeds hk
    exact (nestSeedOf_ds hh hlen (fun y hy => Expr.fvarB_le (by
      rw [hnP]; exact (hMs₀ M hM).2.1 hMn y hy)) x hx).2 (fun y hy => (hholes y hy).1) hpar'
  obtain ⟨rfl, -⟩ := hS
  refine SimG.bind (flushC_simG_to (mode := mode)
    (fun s h => (h : CSOK mode env₁ s).residue) env₂) fun _ _ _ => ?_
  -- every class's table entries; the generator's constructors
  refine SimG.bind (SimG.ofC fun s hs => classesNfsS_sim hμ henv₂ hformer Ms₀ hs
    (fun M hM => (hMs₀ M hM).1)) fun Ms Ms' hN => ?_
  obtain ⟨rfl, hMs⟩ := hN
  refine SimG.bind (SimG.ofC fun s hs => classesCtorsS_sim hμ henv₂ hformer hMs 0 Ms hs)
    fun ctors ctors' hC => ?_
  obtain rfl : ctors = ctors' := hC
  by_cases h4 : ((List.filter ClassSlot.isMinor rd.slots).length ==
      (List.map List.length ctors).sum) = true
  case neg => simp only [h4]; exact SimG.throw_bind
  simp only [h4, if_true]
  -- generation
  refine SimG.bind (SimG.ofC fun s hs => classFormerTysS_sim Ms hs) fun fT fT' hF => ?_
  obtain rfl : fT = fT' := hF
  refine SimG.bind (SimG.ofC fun s hs => SimC.unwrapOr' hs) fun pre pre' hP => ?_
  obtain ⟨rfl, -⟩ := hP
  refine SimG.bindR (SimG.ofC fun s hs => classRecTysOkS_sim hμ henv₂ p.recs cvRis rd.recCls
    hs hwRis) fun cvGs cvGs' hG hrun => ?_
  obtain rfl : cvGs = cvGs' := hG
  obtain ⟨F, hF⟩ := hrun
  rw [classRecTysOk_datF] at hF
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run hF
  -- the rule-less generated recursors' environment is well formed
  have henvR : EnvWF (consBlockRecsBare p 0
      (List.map (fun x => (x.fst, (Ms.getD x.snd default).nIdx)) (cvGs.zip rd.recCls)) env₂) := by
    refine envWF_consBlockRecsBare henv₂ fun c hc => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.of_mem_zip hx).1
    have hil : i < p.recs.length := by
      rw [← hlenG]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨c, cvG, -, hcvG, ⟨R⟩⟩ := hallG i _ (List.getElem?_eq_getElem hil)
    rw [hi] at hcvG
    obtain rfl := Option.some.inj hcvG
    exact classConstOk_typeWF R.hcv
  refine SimG.bind ((flushC_simG_all (mode := mode)).mono (fun s h => (h : CSOK mode env₂ s).residue) (fun _ h => h))
    fun _ _ _ => ?_
  refine SimG.bind (classRecsRulesOkS_simG (envT := env₂) hμ henvR cvGs rd.recCls)
    fun out out' hO => ?_
  obtain rfl : out = out' := hO
  exact SimG.bind (flushC_simG.mono (fun _ h => CSOKAll.residue h) (fun _ h => h))
    fun _ _ _ => SimG.pure (fun _ h => h) rfl

/-- **The generated recursor stage at the cached driver** is reproduced
by the pure fueled stage. -/
theorem genRecCheckS_run (hμ : mode.verifiedChecks = true) {env₁ env₂ : Env} {fe₁ : FEnv}
    (henv₁ : EnvWF env₁) (henv₂ : EnvWF env₂) (hfe₁ : fe₁.find? = (mkFEnv env₁).find?)
    {p : BlockShape} {nestedBit : Bool} {pos : NestState} (hpos : NestStOk pos)
    {cvTas : List ConstantVal} {block : List ConstantInfo}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    {s₀ : CState} (hs : CSOK mode env₂ s₀) {out : List (ConstantVal × TargetMajor × List Expr)}
    {s' : CState}
    (h : genRecCheck (shadowOpsC mode) fe₁ env₁ (mkFEnv env₂) p nestedBit pos cvTas block
      ctorsAs s₀ = .ok (out, s')) :
    CSOKF s' ∧ ∃ F, genRecCheck (ShadowOps.fueled mode F) fe₁ env₁ (mkFEnv env₂) p nestedBit
      pos cvTas block ctorsAs = .ok out := by
  obtain ⟨hs', out', rfl, F, hF⟩ :=
    genRecCheckS_simG hμ henv₁ henv₂ hfe₁ hpos hT s₀ hs out s' h
  exact ⟨hs', F, by rw [← genRecCheck_datF]; exact hF⟩

/-- The stage reads its seeds' index only through `find?`. -/
theorem genRecCheck_fe₁_congr {F : Nat} {fe₁ fe₁' : FEnv} (hfe : fe₁.find? = fe₁'.find?)
    (env₁ : Env) (fe : FEnv) (p : BlockShape) (nestedBit : Bool) (pos : NestState)
    (cvTas : List ConstantVal) (block : List ConstantInfo)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    genRecCheck (ShadowOps.fueled mode F) fe₁ env₁ fe p nestedBit pos cvTas block ctorsAs
      = genRecCheck (ShadowOps.fueled mode F) fe₁' env₁ fe p nestedBit pos cvTas block
        ctorsAs := by
  unfold genRecCheck
  simp only [ShadowOps.fueled, ShadowOps.ofOps]
  rw [hfe]

/-! ## The install after the pass, at the cached driver -/

/-- **The stored family's environment is well-formed**: every stored
recursor type is a checked generated constant's (`classConstOk`), every
stored rule a generated rule closed, at the recursor's level parameters
and resolved at the rule-less recursors' environment (`classRuleOk`). -/
theorem genRecCheck_recsWF {env₂ : Env} (henv₂ : EnvWF env₂) {p : BlockShape}
    {nestedBit : Bool} {fe₁ : FEnv} {env₁ : Env} {pos : NestState}
    {cvTas : List ConstantVal} {block : List ConstantInfo}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {F : Nat}
    (h : genRecCheck (ShadowOps.fueled mode F) fe₁ env₁ (mkFEnv env₂) p nestedBit pos cvTas
      block ctorsAs = .ok out) (find? : Name → Option ConstantInfo) :
    EnvWF (consBlockRecsT find? (·.constsResolve env₂) p 0 out env₂) := by
  obtain ⟨R⟩ := genRecCheck_run h
  have hcvGs := R.hcvGs
  have hrules := R.hrules
  obtain ⟨hlenG, hallG⟩ := classRecTysOk_run hcvGs
  obtain ⟨hlenO, hallO⟩ := classRecsRulesOk_run hrules
  -- every stored entry: a generated constant, its class, its rules
  have hat : ∀ (i : Nat) (o : ConstantVal × TargetMajor × List Expr), out[i]? = some o →
      ∃ rc c cvG, R.rd.recCls[i]? = some c ∧ R.cvGs[i]? = some cvG ∧
        o = (cvG, R.Ms.getD c default, o.2.2) ∧
        Nonempty (ClassRecTyRun mode F (mkFEnv env₂) R.g p.k rc c cvG) ∧
        classRulesOk (fueledOps mode F) .plain (mkFEnv env₂)
          (classFeR p R.Ms R.cvGs R.rd.recCls (mkFEnv env₂)) R.g
          (classRecOf R.rd.recCls R.cvGs) cvG
          (Level.zeronessOf (structElimLevel p.elim p.large)) c (R.ctors.getD c []) = .ok o.2.2 := by
    intro i o ho
    have hil : i < p.recs.length := by
      have := (List.getElem?_eq_some_iff.mp ho).1; rw [hlenO] at this; omega
    obtain ⟨c, cvG, hc, hG, T⟩ := hallG i p.recs[i] (List.getElem?_eq_getElem hil)
    obtain ⟨rhss, hoi, hr⟩ := hallO i cvG c hG hc
    rw [ho] at hoi
    obtain rfl := Option.some.inj hoi
    exact ⟨_, c, cvG, hc, hG, rfl, T, hr⟩
  have hbare : out.map (fun t => (t.1, t.2.1.nIdx))
      = (R.cvGs.zip R.rd.recCls).map fun q => (q.1, (R.Ms.getD q.2 default).nIdx) := by
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_map]
    cases ho : out[i]? with
    | none =>
      have : (R.cvGs.zip R.rd.recCls)[i]? = none := by
        rw [List.getElem?_eq_none_iff] at ho ⊢; simp only [List.length_zip]; omega
      simp [this]
    | some o =>
      obtain ⟨rc, c, cvG, hc, hG, ho', -, -⟩ := hat i o ho
      have hz : (R.cvGs.zip R.rd.recCls)[i]? = some (cvG, c) :=
        List.getElem?_zip_eq_some.mpr ⟨hG, hc⟩
      rw [ho']
      simp [hz]
  have hfeR : classFeR p R.Ms R.cvGs R.rd.recCls (mkFEnv env₂)
      = mkFEnv (consBlockRecsBare p 0 (out.map fun t => (t.1, t.2.1.nIdx)) env₂) := by
    unfold classFeR
    rw [consBlockRecsBareF_mkFEnv, hbare]
  refine envWF_consBlockRecsT henv₂ fun o ho => ?_
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

/-- **The install after the pass, at k members, at the cached driver**,
is reproduced by the pure fueled `checkBlockTail`. -/
theorem checkBlockTailS_run (hμ : mode.verifiedChecks = true)
    {env₁ : Env} (henv₁ : EnvWF env₁) {block : List ConstantInfo} {cvTas : List ConstantVal}
    {p : BlockParts}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)} {pos : NestState}
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hfr : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, env₁.find? c.1.name = none)
    (henv₂ : EnvWF (consBlockCtors p.nP ctorsAs env₁)) (hpos : NestStOk pos)
    {s₀ : CState} (hs : CSOK mode env₁ s₀) {feOut : FEnv} {s' : CState}
    (h : checkBlockTailS mode block ⟨mkFEnv env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩
      s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (checkBlockTail (fueledOpsM mode) block ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩
     ).val F = .ok feOut.env := by
  unfold checkBlockTailS at h
  dsimp only at h
  by_cases hg : (p.large && !p.resSort.isNeverZero && decide (2 ≤ p.k ∨ 2 ≤ p.numCtors)) = true
  · rw [if_pos hg] at h; exact absurd h throwC_bind_ok
  rw [if_neg hg] at h
  rw [checkBlockIdxSortsF_eqC] at h
  obtain ⟨isorts, sS, hsorts, h⟩ := bindC_ok h
  have hzT : ∀ x ∈ p.members.zip cvTas, WScoped 0 x.2.type :=
    fun x hx => hT x.2 (List.of_mem_zip hx).2
  obtain ⟨hsS, isorts', hPs, F₀, hF₀⟩ :=
    checkBlockIdxSortsS_sim hμ henv₁ hzT hs isorts sS hsorts
  obtain rfl : isorts = isorts' := hPs
  have hview := restrictTo_consBlockCtors_mkFEnv (nP := p.nP) hfr
  rw [consBlockCtorsF_mkFEnv] at h hview
  rw [mkFEnv_env] at h
  obtain ⟨u2, sC, hfl2, h⟩ := bindC_ok h
  rw [flushC_run] at hfl2
  injection hfl2 with hfl2
  obtain rfl : sS.flushed = sC := congrArg Prod.snd hfl2
  obtain ⟨out, s₃, hrec, h⟩ := bindC_ok h
  obtain ⟨hs₃, F₃, hF₃⟩ := genRecCheckS_run hμ henv₁ henv₂ hview hpos hT
    (flushC_csok hsS.residue) hrec
  rw [genRecCheck_fe₁_congr hview] at hF₃
  have henv₃ := genRecCheck_recsWF henv₂ hF₃ (consBlockCtors p.nP ctorsAs env₁).find?
  rw [show FEnv.find? (mkFEnv (consBlockCtors p.nP ctorsAs env₁))
    = (consBlockCtors p.nP ctorsAs env₁).find? from mkFEnv_find?_fun _] at h
  simp only [constsResolveF_eq] at h
  rw [consBlockRecsTF_mkFEnv, structWalkersC_eq_plain] at h
  obtain ⟨hwfO, hfeO, -, hT₆⟩ := checkBlockTablesS_run _ _ _ henv₃ hs₃ h
  obtain ⟨G, hle₀, hle₃⟩ : ∃ G, F₀ ≤ G ∧ F₃ ≤ G := ⟨max F₀ F₃, by omega, by omega⟩
  refine ⟨hwfO, hfeO, G, ?_⟩
  have g₀ : checkBlockIdxSorts (fueledOps mode G) env₁ p.toBlockShape
      (p.members.zip cvTas) = .ok isorts := by
    rw [← checkBlockIdxSorts_datF]; exact FueledM.up hle₀ hF₀
  have g₃ : checkBlockRec (fueledOps mode G) env₁ (consBlockCtors p.nP ctorsAs env₁) p
      (blockNestedBit p.toBlockShape kinds) pos block cvTas ctorsAs = .ok out := by
    show genRecCheck (ShadowOps.fueled mode G) _ _ _ _ _ _ _ _ _ = _
    rw [← genRecCheck_datF]
    exact FueledM.up hle₃ (by rw [genRecCheck_datF]; exact hF₃)
  rw [checkBlockTail_datF]
  unfold checkBlockTail
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [if_neg hg]
  try simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₀]
  simp only [Except.bind]
  rw [g₃]
  simp only [Except.bind]
  exact hT₆

/-- **The uniform install at k members, at the recursor stage's CHECK,
at the cached driver**, is reproduced by the pure fueled `checkBlock`:
the pass at official's `is_rec` and the install after it. -/
theorem checkBlockKS_run (hμ : mode.verifiedChecks = true)
    {env : Env} (henv : EnvWF env) {block : List ConstantInfo} {p₀ : BlockParts}
    {s₀ : CState} (hwf : CSOKF s₀) {feOut : FEnv} {s' : CState}
    (h : checkBlockKS mode (mkFEnv env) block p₀ s₀ = .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkBlock (fueledOps mode F) env block p₀ = .ok feOut.env := by
  unfold checkBlockKS at h
  by_cases hnd : (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup
  case neg => rw [if_neg hnd] at h; exact absurd h throwC_bind_ok
  rw [if_pos hnd] at h
  obtain ⟨u0, sA, hfl0, h⟩ := bindC_ok h
  rw [flushC_run] at hfl0
  injection hfl0 with hfl0
  obtain rfl : s₀.flushed = sA := congrArg Prod.snd hfl0
  obtain ⟨r, s₁, hP, h⟩ := bindC_ok h
  obtain ⟨fe₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩ := r
  obtain ⟨env₁, hq₁, hs₁, henv₁, hT, -, hfr, henv₂, hpos, F₁, hF₁⟩ :=
    checkBlockPassS_run hμ henv (flushC_csok hwf) hP
  simp only at hq₁ hs₁ henv₁ hT hfr henv₂ hpos hF₁
  subst hq₁
  obtain ⟨hwfO, hfeO, F₂, hF₂⟩ := checkBlockTailS_run hμ henv₁ hT hfr henv₂ hpos hs₁ h
  refine ⟨hwfO, hfeO, max F₁ F₂, ?_⟩
  have g₁ : checkBlockPass (fueledOps mode (max F₁ F₂)) env p₀ (blockRawRec p₀)
      = .ok ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩ := by
    rw [← checkBlockPass_datF]; exact FueledM.up (Nat.le_max_left _ _) hF₁
  have g₂ : checkBlockTail (fueledOps mode (max F₁ F₂)) block
      ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, nfs, pos⟩
      = .ok feOut.env := by
    rw [← checkBlockTail_datF]; exact FueledM.up (Nat.le_max_right _ _) hF₂
  unfold checkBlock
  rw [if_pos hnd]
  simp only [Bind.bind, Except.bind, pure, Except.pure]
  rw [g₁]
  simp only [Except.bind]
  exact g₂

variable {pins : List NatOpPinSet}

/-- The inductive-block dispatch of the cached driver: a RECOGNISED
block goes to `checkBlockKS`, every other one
declines (`checkShapelessS`), and the pure fueled `checkDecl`
reproduces the run. -/
theorem checkModeledOrNativeSF_run (hμ : mode.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {block : List ConstantInfo} {nP : Nat} (hpin : basisPinHit block = none)
    (hok : indParamsOk nP block = true)
    {s₀ : CState} (hwf : CSOKF s₀)
    {feOut : FEnv} {s' : CState}
    (h : (match blockParts? nP block with
          | some p => checkBlockKS mode (mkFEnv env) block p
          | none => checkShapelessS mode (mkFEnv env) block) s₀ =
      .ok (feOut, s')) :
    CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, checkDecl mode (fueledOps mode F) pins env (.indDecl block nP) =
      .ok feOut.env := by
  -- the declared parameter count (task #228) is a pure guard shared by
  -- the two drivers: `hok` is the branch both take
  show CSOKF s' ∧ feOut = mkFEnv feOut.env ∧
    ∃ F, (match basisPinHit block with
      | some kind => checkBasisDecl (m := CheckM) env kind
      | none =>
        if indParamsOk nP block = true then
          (match blockParts? nP block with
            | some p => checkBlock (fueledOps mode F) env block p
            | none => checkShapeless (fueledOps mode F) env block)
        else throw (CheckError.invalid "number of parameters mismatch")) = .ok feOut.env
  -- task #293: this block is not one of the five pinned ones (the
  -- recognition happened before the dispatch, on both sides)
  simp only [hpin, if_pos hok]
  cases hfp : blockParts? nP block with
  | some p =>
    rw [hfp] at h
    simp only at h
    -- the block install, at any number of members, nested included
    obtain ⟨hres, hfe, F, hF⟩ := checkBlockKS_run hμ henv hwf h
    exact ⟨hres, hfe, F, hF⟩
  | none =>
    rw [hfp] at h
    -- the decline never returns an index
    exfalso
    unfold checkShapelessS at h
    obtain ⟨_, _, _, h⟩ := bindC_ok h
    exact nomatch h

end ConLeche.Cached
