module

public import ConLeche.Verify.Cached.TargetRecC
public import ConLeche.Kernel.Inductives.GenRec
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Verify.Inductives.GenRecDatF
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
`ShadowOps`, like the target check: the pure install is to run it at
`ShadowOps.ofOps`, the cached driver at `shadowOpsC`.  This file proves
the cached run reproduced by the pure fueled one (`genRecCheckS_simG`,
`genRecCheckS_run`) — the twin of `targetRecCheckS_simG`/
`targetRecCheckS_run` (`TargetRecC.lean`), whose per-operation
simulations it reuses.

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

/-- **One recursor's generated type, checked and compared**: the stored
constant is closed. -/
theorem classRecTyOkS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {g : ClassGen}
    {k : Nat} {rc : RecShape} {cvRi : ConstantVal} {c : Nat} (hRi : WScoped 0 cvRi.type)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 v.type)
      (classRecTyOk (sharedOpsC mode (mkFEnv env)) (mkFEnv env) g k rc cvRi c)
      (classRecTyOk (fueledOpsM mode) (mkFEnv env) g k rc cvRi c) := by
  unfold classRecTyOk
  simp only [checkConstantValF_eq, mkFEnv_env]
  split
  case isFalse => exact SimC.throw_bind
  split
  case isFalse => exact SimC.throw_bind
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ gty gty' hs₁ hG => ?_)
  obtain ⟨rfl, -⟩ := hG
  refine SimC.bind (checkConstantValS_sim hμ henv hs₁) (fun s₂ cvG cvG' hs₂ hC => ?_)
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

/-- **One generated rule, simulated.**  From any residue: the rule,
closed by the stage's own guard, annotated and typed at the rule-less
recursors' environment `envR` (`sharedOpsRuleR`'s flushes on either
side), its λ-telescope read syntactically. -/
theorem classRuleOkS_simG (hμ : mode.verifiedChecks = true) {envR : Env} (henvR : EnvWF envR)
    (envT : Env) {cvR : ConstantVal} {pw : PropWhen} {n : Nat} {gen : Expr} :
    SimG CSOKF (CSOK mode envT) RelVC
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
  refine SimG.bind (ruleR_annotate_simG hμ henvR hw) (fun genA genA' hA => ?_)
  obtain ⟨rfl, hwA⟩ := hA
  by_cases h3 : allLevelParamsDefined cvR.levelParams genA = true
  case neg => simp only [h3]; exact SimG.throw_bind
  simp only [h3, if_true]
  by_cases h4 : StructWalkers.plain.resolve (mkFEnv envR) genA = true
  case neg => simp only [h4]; exact SimG.throw_bind
  simp only [h4, if_true]
  refine SimG.bind (ruleR_infer_simG hμ henvR envT hwA) (fun _ _ _ => ?_)
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
      SimG CSOKF CSOKF RelVC
        (classRulesOk (sharedOpsRuleR mode (mkFEnv envR)) .plain (mkFEnv envT) (mkFEnv envR) g
          recOf cvR pw c xs)
        (classRulesOk (fueledOpsM mode) .plain (mkFEnv envT) (mkFEnv envR) g recOf cvR pw c xs)
  | [] => SimG.pure (fun _ h => h) rfl
  | x :: xs => by
    unfold classRulesOk
    refine SimG.bind (SimG.unwrapOr (fun _ h => h)) (fun gen gen' hG => ?_)
    obtain ⟨rfl, -⟩ := hG
    refine SimG.bind ((classRuleOkS_simG hμ henvR envT).mono (fun _ h => h)
      (fun _ h => h.residue)) (fun r r' hR => ?_)
    obtain rfl : r = r' := hR
    refine SimG.bind (classRulesOkS_simG hμ henvR xs) (fun rs rs' hRs => ?_)
    obtain rfl : rs = rs' := hRs
    exact SimG.pure (fun _ h => h) rfl

theorem classRecsRulesOkS_simG (hμ : mode.verifiedChecks = true) {envR envT : Env}
    (henvR : EnvWF envR) {g : ClassGen} {recOf : Nat → Option Name} {pw : PropWhen} :
    ∀ (cvs : List ConstantVal) (cs : List Nat),
      SimG CSOKF CSOKF RelVC
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
  refine SimG.bind (SimG.ofC fun s hs => SimC.unwrapOr' hs) fun cv0 cv0' hC0 => ?_
  obtain ⟨rfl, hcv0⟩ := hC0
  refine SimG.bind (SimG.ofC fun s hs => SimC.unwrapOr' hs) fun y y' hY => ?_
  obtain ⟨rfl, hy⟩ := hY
  obtain ⟨pfvs, o0⟩ := y
  dsimp only
  -- the parameter openers, scoped
  have hw0 : WScoped 0 cv0.type := hwRis cv0 (List.mem_of_mem_head? hcv0)
  have hpl : pfvs.length = p.nP := ConLeche.Verify.openPisAtFvars_length _ hy
  have hp : ∀ x ∈ pfvs, WScoped p.nP x := by
    have := (openPisAtFvars_WScoped p.nP cv0.type 0 hy hw0).1
    simpa using this
  -- the pre-pass's classes, scoped
  have hkeys : ∀ key ∈ rd.classes, ∀ x ∈ key.ds, ∃ D, WScoped D x := by
    refine classRead_keys_scoped (fun rc hrc => ?_) hrd
    obtain ⟨⟨rc', cv⟩, hmem, rfl⟩ := List.mem_map.mp hrc
    exact hwRis cv (List.of_mem_zip hmem).2
  refine SimG.bind (SimG.ofC fun s hs => classMajorsS_sim hμ henv₂ hpl hp rd.classes hs hkeys)
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
  refine SimG.bind (SimG.ofC fun s hs => blockNestCtxS_sim henv₁ p cvTas hT hs)
    fun r r' hR => ?_
  obtain ⟨rfl, hctx, hholes, hpar, hlen, hh, hnP⟩ := hR
  rcases r with ⟨ctx, holes⟩
  dsimp only at hctx hholes hpar hlen hh hnP ⊢
  refine SimG.bind (SimG.ofC fun s hs => nestSeedsS_sim hμ henv₁ hctx _ pos hs
    (fun k hk x hx => ?_) hpos) fun st st' hS => ?_
  · obtain ⟨M, hM, hMn, rfl⟩ := mem_classSeeds hk
    exact (nestSeedOf_ds hh hlen (fun y hy => Expr.fvarB_le (by
      rw [hnP]; exact (hMs₀ M hM).2.1 hMn y hy)) x hx).2 (fun y hy => (hholes y hy).1) hpar
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
    have hcv := R.hcv
    rw [checkConstantValF_eq] at hcv
    exact checkConstantVal_typeWF hcv
  refine SimG.bind (flushC_simG.mono (fun s h => (h : CSOK mode env₂ s).residue) (fun _ h => h))
    fun _ _ _ => ?_
  refine SimG.bind (classRecsRulesOkS_simG (envT := env₂) hμ henvR cvGs rd.recCls)
    fun out out' hO => ?_
  obtain rfl : out = out' := hO
  exact SimG.bind flushC_simG fun _ _ _ => SimG.pure (fun _ h => h) rfl

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

end ConLeche.Cached
