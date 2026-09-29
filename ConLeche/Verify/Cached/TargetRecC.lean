module

public import ConLeche.Verify.Cached.BlockRunC
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Cached.KnotCongr

public section

/-!
# The cached recursor stage, bridged: the TARGET check

The recursor stage's class kit (`ConLeche/Kernel/Inductives/RecCheck.lean`:
the class match, a class resolved and its pins, node agreement) at the
cached driver: each operation's simulation by the pure fueled one, the
scoping facts they need, and the cons at the majors (`consBlockRecsTF`,
`envWF_consBlockRecsT`).  The generated stage itself and the cached
uniform install are simulated in `GenRecC.lean`.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## 1. Scoping -/

theorem piBinders_WScoped {d : Nat} : ∀ {e : Expr}, WScoped d e →
    (∀ b ∈ e.piBinders.1, WScoped d b.1) ∧ WScoped d e.piBinders.2
  | .forallE ty b m, h => by
    simp only [WScoped] at h
    obtain ⟨h1, h2⟩ := piBinders_WScoped h.2
    simp only [Expr.piBinders]
    refine ⟨?_, h2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.1
    · exact h1 x hx
  | .bvar _, h | .fvar .., h | .sort _, h | .const .., h | .app .., h | .lam .., h
  | .letE .., h | .lit _, h | .proj .., h => by
    constructor
    · intro b hb; simp [Expr.piBinders] at hb
    · simpa [Expr.piBinders] using h

theorem WScoped.default_expr {d : Nat} : WScoped d (default : Expr) :=
  WScoped.of_not_hasFvar (by rfl)

theorem getD_WScoped {d : Nat} {l : List Expr} (h : ∀ x ∈ l, WScoped d x) (i : Nat) :
    WScoped d (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none => exact WScoped.default_expr
  | some x => exact h x (List.mem_of_getElem? hx)

/-- The frame's holes are scoped past the frame. -/
theorem targetHoles_WScoped {formerTys : List Expr} (hF : ∀ t ∈ formerTys, WScoped 0 t)
    (base : Nat) : ∀ h ∈ targetHoles formerTys base, WScoped (base + formerTys.length) h := by
  intro h hh
  simp only [targetHoles, List.mem_map, List.mem_range] at hh
  obtain ⟨t, ht, rfl⟩ := hh
  simp only [WScoped]
  exact ⟨by omega, ws_of_ws0 (getD_WScoped hF t)⟩

/-! ### The primitive-recursion abstraction's residue -/

/-! ## 2. The stages, simulated -/

/-- A simulation keeps what the cached run is known to yield. -/
theorem SimC.withYields {env : Env} {s₀ : CState} {β α : Type} {P : β → α → Prop}
    {Q : β → Prop} {c : CheckCM β} {p : FueledM α} (h : SimC mode env s₀ P c p)
    (hy : ∀ s a s', c s = .ok (a, s') → Q a) :
    SimC mode env s₀ (fun v w => P v w ∧ Q v) c p := by
  intro v' s' hr
  obtain ⟨hs', v, hP, F, hF⟩ := h v' s' hr
  exact ⟨hs', v, ⟨hP, hy s₀ v' s' hr⟩, F, hF⟩

section Sims

variable {env : Env}

/-- `targetOutsideInst` is operation-free: at the cached driver it
leaves the state alone and computes the pure value. -/
theorem targetOutsideInst_C {fe : FEnv} {I : Name} {us : List Level} {ds : List Expr}
    (s : CState) :
    targetOutsideInst (m := CheckCM) fe I us ds s =
      (match targetOutsideInst (m := CheckM) fe I us ds with
        | .ok v => .ok (v, s)
        | .error e => .error e) := by
  unfold targetOutsideInst
  cases h1 : fe.find? I with
  | none => rfl
  | some ci =>
    cases ci with
    | indInfo cvI caps =>
      dsimp only
      cases h2 : instPisWith ds (cvI.type.instantiateLevelParams cvI.levelParams us) with
      | none => rfl
      | some ty =>
        dsimp only
        rcases h3 : ty.piBinders with ⟨ibs, e⟩
        cases e <;> rfl
    | _ => rfl

theorem targetOutsideInstS_sim {fe : FEnv} {I : Name} {us : List Level} {ds : List Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (targetOutsideInst (m := CheckCM) fe I us ds)
      (targetOutsideInst (m := FueledM) fe I us ds) := by
  intro v' s' h
  rw [targetOutsideInst_C] at h
  cases hr : targetOutsideInst (m := CheckM) fe I us ds with
  | error e => rw [hr] at h; exact nomatch h
  | ok v =>
    rw [hr] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    exact ⟨hs, v, rfl, 0, by rw [targetOutsideInst_datF]; exact hr⟩

/-- `liftFueled` (the level comparison's fuel) is operation-free. -/
theorem liftFueledS_sim {α : Type} {what : String} {o : Option α} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (liftFueled (m := CheckCM) what o) (liftFueled (m := FueledM) what o) := by
  cases o with
  | none => exact SimC.throw
  | some a => exact SimC.pure hs rfl

/-! ### The class match (`targetClassMatch`) and its three uses -/

theorem targetParamsDefEqS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat}
    {absM : Expr → Expr} (habs : ∀ e, WScoped d e → WScoped d (absM e)) {pfvs : List Expr}
    (hp : ∀ x ∈ pfvs, WScoped d x) :
    ∀ (as bs : List Expr) {s₀ : CState}, (∀ a ∈ as, WScoped d a) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (targetParamsDefEq (sharedOpsC mode (mkFEnv env)) env d absM pfvs as bs)
        (targetParamsDefEq (fueledOpsM mode) env d absM pfvs as bs)
  | [], [], _, _, hs => SimC.pure hs rfl
  | [], _ :: _, _, _, hs => SimC.pure hs rfl
  | _ :: _, [], _, _, hs => SimC.pure hs rfl
  | a :: as, b :: bs, _, ha, hs => by
    unfold targetParamsDefEq
    split
    · rename_i hg
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
      dsimp only [sharedOpsC]
      have hwa := habs _ (targetCanonParams_WScoped hp a (fvarB_le hg.1.2))
      have hwb := habs _ (targetCanonParams_WScoped hp b (fvarB_le hg.2))
      split
      · exact targetParamsDefEqS_sim hμ henv habs hp as bs
          (fun a' ha' => ha a' (List.mem_cons_of_mem _ ha')) hs
      refine SimC.bind (opE_infer_sim hμ henv hs hwa) (fun s₁ _ _ hs₁ _ => ?_)
      refine SimC.bind (opE_infer_sim hμ henv hs₁ hwb) (fun s₂ _ _ hs₂ _ => ?_)
      refine SimC.bind (opB_sim hμ henv hs₂ hwa hwb) (fun s₃ c c' hs₃ hC => ?_)
      obtain rfl : c = c' := hC
      cases c
      · exact SimC.pure hs₃ rfl
      · exact targetParamsDefEqS_sim hμ henv habs hp as bs
          (fun a' ha' => ha a' (List.mem_cons_of_mem _ ha')) hs₃
    · exact SimC.pure hs rfl

/-- The class match, simulated: the class's openers and parameters
scoped by the block's parameters, the formers closed. -/
theorem targetClassMatchS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {pfvs ds eds : List Expr} {us lvls : List Level}
    (hp : ∀ x ∈ pfvs, WScoped pfvs.length x) (hds : ∀ x ∈ ds, WScoped pfvs.length x)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (targetClassMatch (sharedOpsC mode (mkFEnv env)) env p formerTys pfvs us ds lvls eds)
      (targetClassMatch (fueledOpsM mode) env p formerTys pfvs us ds lvls eds) := by
  unfold targetClassMatch
  split
  · exact targetParamsDefEqS_sim hμ henv
      (targetAbs_WScoped (targetHoles_WScoped hformer pfvs.length))
      (fun x hx => (hp x hx).mono (by omega)) ds eds (fun x hx => (hds x hx).mono (by omega)) hs
  · exact SimC.pure hs rfl

theorem targetMajorNfsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {pfvs ds : List Expr} {us : List Level} {ctors : List (ConstantVal × Nat)}
    (hp : ∀ x ∈ pfvs, WScoped pfvs.length x) (hds : ∀ x ∈ ds, WScoped pfvs.length x) :
    ∀ (es : List NestCtorNf) {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (targetMajorNfs (sharedOpsC mode (mkFEnv env)) env p formerTys pfvs us ds ctors es)
        (targetMajorNfs (fueledOpsM mode) env p formerTys pfvs us ds ctors es)
  | [], _, hs => SimC.pure hs rfl
  | e :: es, _, hs => by
    unfold targetMajorNfs
    refine SimC.bind (targetMajorNfsS_sim hμ henv hformer hp hds es hs)
      (fun s₁ r r' hs₁ hR => ?_)
    obtain rfl : r = r' := hR
    split
    · refine SimC.bind (targetClassMatchS_sim hμ henv hformer hp hds hs₁)
        (fun s₂ c c' hs₂ hC => ?_)
      obtain rfl : c = c' := hC
      cases c <;> exact SimC.pure hs₂ rfl
    · exact SimC.pure hs₁ rfl

theorem targetMajorOfS_sim {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs fvs : List Expr} {mty : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (targetMajorOf (m := CheckCM) (mkFEnv env) p ctorsAs pfvs fvs mty)
      (targetMajorOf (m := FueledM) (mkFEnv env) p ctorsAs pfvs fvs mty) := by
  unfold targetMajorOf
  dsimp only
  split
  · split
    · refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ ms ms' hs₁ hP => ?_)
      obtain ⟨rfl, -⟩ := hP
      refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ c c' hs₂ hQ => ?_)
      obtain ⟨rfl, -⟩ := hQ
      split
      · exact SimC.pure hs₂ rfl
      · exact SimC.throw_bind
    · repeat' (first
        | exact SimC.throw
        | exact SimC.throw_bind
        | exact SimC.pure hs rfl
        | split)
      all_goals
        refine SimC.bind (targetOutsideInstS_sim hs) (fun s₂ r r' hs₂ hR => ?_)
        cases hR
        refine SimC.bind (liftFueledS_sim hs₂) (fun s₃ q q' hs₃ hQ => ?_)
        cases hQ
        split
        · exact SimC.pure hs₃ rfl
        · exact SimC.throw_bind
  · exact SimC.throw

/-- The pin typing at the cached driver. -/
theorem targetPinTysS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} :
    ∀ {xs : List Expr}, (∀ x ∈ xs, WScoped d x) → ∀ {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ (fun (_ _ : Unit) => True)
        (targetPinTys (sharedOpsC mode (mkFEnv env)) env d xs)
        (targetPinTys (fueledOpsM mode) env d xs)
  | [], _, _, hs => SimC.pure hs trivial
  | x :: xs, hx, _, hs => by
    unfold targetPinTys
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_infer_sim hμ henv hs (hx x List.mem_cons_self))
      (fun s₁ _ _ hs₁ _ => ?_)
    exact targetPinTysS_sim hμ henv (fun y hy => hx y (List.mem_cons_of_mem _ hy)) hs₁

/-- `targetMajorPins` at the cached driver: nothing at a member, the
pins and the instantiation typed at an outside major. -/
theorem targetMajorPinsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {rP : Nat}
    {M : TargetMajor} (hds : M.member = none → ∀ x ∈ M.ds, WScoped rP x) {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun (_ _ : Unit) => True)
      (targetMajorPins (sharedOpsC mode (mkFEnv env)) env rP M)
      (targetMajorPins (fueledOpsM mode) env rP M) := by
  unfold targetMajorPins
  cases hM : M.member with
  | some t =>
    simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    exact SimC.pure hs trivial
  | none =>
    simp only [Option.isNone_none, ↓reduceIte]
    have hw := hds hM
    refine SimC.bind (targetPinTysS_sim hμ henv hw hs) (fun s₁ _ _ hs₁ _ => ?_)
    dsimp only [sharedOpsC]
    refine SimC.bind (opE_infer_sim hμ henv hs₁
      (Expr.WScoped.mkAppN (by simp [WScoped]) hw)) (fun s₂ _ _ hs₂ _ => ?_)
    exact SimC.pure hs₂ trivial

theorem targetRecPinsS_sim {p : BlockShape} {block : List ConstantInfo} {s₀ : CState}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (targetRecPins (m := CheckCM) p block)
      (targetRecPins (m := FueledM) p block) := by
  unfold targetRecPins
  dsimp only
  by_cases h1 : blockRecLpsOk p = true
  case neg => simp only [h1]; exact SimC.throw_bind
  simp only [h1, if_true]
  by_cases h2 : blockRecNamesUnreserved p = true
  case neg => simp only [h2]; exact SimC.throw_bind
  simp only [h2, if_true]
  split
  case isFalse => exact SimC.throw_bind
  split
  case isFalse => exact SimC.throw_bind
  split
  case isFalse => exact SimC.throw_bind
  split
  · split
    · exact SimC.pure hs rfl
    · exact SimC.throw
  · exact SimC.throw

/-- A resolved major's class, scoped by the block's parameters: its
openers and its parameters (what the class match needs). -/
@[expose] def TargetMajScoped (M : TargetMajor) : Prop :=
  (∀ x ∈ M.pfvs, WScoped M.pfvs.length x) ∧ ∀ x ∈ M.ds, WScoped M.pfvs.length x

theorem TargetMajScoped.getD {l : List TargetMajor}
    (h : ∀ M ∈ l, TargetMajScoped M) (i : Nat) : TargetMajScoped (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD]
  cases hx : l[i]? with
  | none =>
    refine ⟨fun x hx' => ?_, fun x hx' => ?_⟩ <;> exact nomatch hx'
  | some M => exact h M (List.mem_of_getElem? hx)

theorem targetK53S_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t) {Mc : TargetMajor}
    (hMc : TargetMajScoped Mc) {tele : List (Expr × BinderMeta)} {majDom f : Expr}
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (targetK53 (sharedOpsC mode (mkFEnv env)) env p formerTys Mc tele majDom f)
      (targetK53 (fueledOpsM mode) env p formerTys Mc tele majDom f) := by
  unfold targetK53
  repeat' split
  all_goals first
    | exact SimC.pure hs rfl
    | exact targetClassMatchS_sim hμ henv hformer hMc.1 hMc.2 hs

end Sims

/-! ### The rule stage: two environments, one state (`SimG`, `BlockRunC.lean`) -/

/-! ## 3. The assembly -/

/-- `SimG.bind` that remembers the first component's fueled run. -/
theorem SimG.bindR {A B C : CState → Prop} {β β' α α' : Type} {P : β → α → Prop}
    {Q : β' → α' → Prop} {c : CheckCM β} {k : β → CheckCM β'} {p : FueledM α}
    {q : α → FueledM α'} (hx : SimG A B P c p)
    (hf : ∀ b a, P b a → (∃ F, p.val F = .ok a) → SimG B C Q (k b) (q a)) :
    SimG A C Q (c >>= k) (p >>= q) := by
  intro s₀ hs v' s' hr
  simp only [Bind.bind, StateT.bind] at hr
  cases hc : c s₀ with
  | error e => rw [hc] at hr; exact nomatch hr
  | ok pr =>
    obtain ⟨b, s₁⟩ := pr
    rw [hc] at hr
    dsimp only [Except.bind] at hr
    obtain ⟨hs₁, a, hP, F₁, hp₁⟩ := hx s₀ hs b s₁ hc
    obtain ⟨hs', a', hQ, F₂, hp₂⟩ := hf b a hP ⟨F₁, hp₁⟩ s₁ hs₁ v' s' hr
    refine ⟨hs', a', hQ, max F₁ F₂, ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_max_left F₁ F₂) hp₁]
    dsimp only [Except.bind]
    exact (q a).property (Nat.le_max_right F₁ F₂) hp₂

/-- The stage's closing flush: the pure side's is no operation. -/
theorem flushC_simG : SimG CSOKF CSOKF RelVC flushC (Pure.pure () : FueledM Unit) := by
  intro s₀ hs v' s' hr
  rw [flushC_run] at hr
  injection hr with hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hs.flushed, (), rfl, 0, rfl⟩

/-- A flush into any environment's invariant. -/
theorem flushC_simG_to {A : CState → Prop} (hA : ∀ s, A s → CSOKF s) (env' : Env) :
    SimG A (CSOK mode env') RelVC flushC (Pure.pure () : FueledM Unit) := by
  intro s₀ hs v' s' hr
  rw [flushC_run] at hr
  injection hr with hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨flushC_csok (hA s₀ hs), (), rfl, 0, rfl⟩

/-- The shared operations read the index only through `find?`
(`coreKnotI_congr`). -/
theorem sharedOpsC_congr {fe₁ fe₂ : FEnv} (hfe : fe₁.find? = fe₂.find?) :
    sharedOpsC mode fe₁ = sharedOpsC mode fe₂ := by
  unfold sharedOpsC opE opB opS
  simp only [coreKnotI_congr hfe]

/-! ### The cons at the majors

The install conses the checked family with each recursor's rules
at ITS major (`consBlockRecsT`): at an outside major every rule fires
`.nested` as the recursor type's major domain reads (`auxRuleFireR`),
and `EnvWF`'s `.nested` clause is exactly that reading's inversion
(`nestedRuleSyn_inv`). -/

theorem consBlockRecsTF_mkFEnv (find? : Name → Option ConstantInfo) (res : Expr → Bool)
    (p : BlockShape) :
    ∀ (m : Nat) (out : List (ConstantVal × TargetMajor × List Expr)) (env : Env),
      consBlockRecsTF find? res p m out (mkFEnv env) = mkFEnv (consBlockRecsT find? res p m out env)
  | _, [], _ => rfl
  | m, (cv, M, rhss) :: rest, env => by
    simp only [consBlockRecsTF, consBlockRecsT, push_mkFEnv]
    exact consBlockRecsTF_mkFEnv find? res p (m + 1) rest _

theorem find?_consBlockRecsT_le {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {env : Env} (n : Name),
      (env.find? n).isSome = true →
      ((consBlockRecsT find? res q m out env).find? n).isSome = true
  | _, [], _, _, h => h
  | _, _ :: _, env, n, h => by
    simp only [consBlockRecsT]
    refine find?_consBlockRecsT_le n ?_
    rw [Env.find?_cons]
    split <;> simp_all

theorem find?_consBlockRecsT_of_bare {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {envA envB : Env},
      (∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true) →
      ∀ n, ((consBlockRecsBare q m (out.map fun t => (t.1, t.2.1.nIdx)) envA).find? n).isSome
          = true →
        ((consBlockRecsT find? res q m out envB).find? n).isSome = true
  | _, [], _, _, hf, n, h => hf n h
  | m, (cv, M, rhss) :: rest, envA, envB, hf, n, h => by
    simp only [List.map_cons, consBlockRecsBare] at h
    simp only [consBlockRecsT]
    refine find?_consBlockRecsT_of_bare
      (envA := ⟨.recInfo cv (q.majorIdxAt m) (q.rulePrefixAt m) [] :: envA.consts⟩) ?_ n h
    exact find?_cons_mono rfl hf

theorem mem_consBlockRecsT {find? : Name → Option ConstantInfo} {res : Expr → Bool}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {env : Env}
      {c : ConstantInfo},
      c ∈ (consBlockRecsT find? res q m out env).consts →
      c ∈ env.consts ∨ ∃ t ∈ out, ∃ j,
        c = .recInfo t.1 (q.majorIdxAt j) (q.rulePrefixAt j)
          (tgtStoredRules find? res t.1 (q.majorIdxAt j) (q.rulePrefixAt j) t.2.1 t.2.2)
  | _, [], _, _, h => Or.inl h
  | m, t0 :: rest, env, c, h => by
    simp only [consBlockRecsT] at h
    rcases mem_consBlockRecsT h with h' | ⟨t, ht, j, hj⟩
    · rcases List.mem_cons.mp h' with rfl | h'
      · exact Or.inr ⟨t0, List.mem_cons_self, m, rfl⟩
      · exact Or.inl h'
    · exact Or.inr ⟨t, List.mem_cons_of_mem _ ht, j, hj⟩

/-- **The family consed at its majors keeps well-formedness**
(`envWF_consBlockRecs` at the majors): the rules' right-hand
sides as there, and an outside major's `.nested` fire off
`nestedRuleSyn_inv`. -/
theorem envWF_consBlockRecsT {find? : Name → Option ConstantInfo} {q : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} {env : Env}
    (henv : EnvWF env)
    (hall : ∀ t ∈ out, t.1.type.hasFvar = false ∧
      t.1.type.allLevelParamsDefined t.1.levelParams = true ∧
      t.1.type.constsResolve env = true ∧
      t.1.type.looseBVarsBounded 0 = true ∧
      ∀ rhs ∈ t.2.2, rhs.hasFvar = false ∧
        rhs.allLevelParamsDefined t.1.levelParams = true ∧
        rhs.constsResolve (consBlockRecsBare q 0 (out.map fun t => (t.1, t.2.1.nIdx)) env)
          = true ∧
        rhs.looseBVarsBounded 0 = true) :
    EnvWF (consBlockRecsT find? (·.constsResolve env) q 0 out env) := by
  have hdomEnv : ∀ n, (env.find? n).isSome = true →
      ((consBlockRecsT find? (·.constsResolve env) q 0 out env).find? n).isSome = true :=
    fun n hn => find?_consBlockRecsT_le n hn
  have hdomBare : ∀ n,
      ((consBlockRecsBare q 0 (out.map fun t => (t.1, t.2.1.nIdx)) env).find? n).isSome
        = true →
      ((consBlockRecsT find? (·.constsResolve env) q 0 out env).find? n).isSome = true :=
    find?_consBlockRecsT_of_bare (fun _ hn => hn)
  intro c hc
  rcases mem_consBlockRecsT hc with hc' | ⟨t, ht, j, rfl⟩
  · exact ConstWF.mono hdomEnv (henv c hc')
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hall t ht
    refine structConstWF h1 h2 (Expr.constsResolve_of_find hdomEnv h3) h4
      (fun _ _ _ heq => nomatch heq) ?_
    intro cvR' mI' rP' rules' heq rl hrl
    injection heq with e1 e2 e3 e4
    subst e1 e2 e3 e4
    unfold tgtStoredRules at hrl
    dsimp only at hrl
    cases hM : t.2.1.member with
    | some _ =>
      rw [hM] at hrl
      obtain ⟨hmem, hfire⟩ := sumRules_mem hrl
      obtain ⟨g1, g2, g3, g4⟩ := h5 rl.rhs hmem
      refine ⟨g1, g2, Expr.constsResolve_of_find hdomBare g3, g4, ?_⟩
      intro lvls pins hf
      exact absurd hf (hfire lvls pins)
    | none =>
      rw [hM] at hrl
      obtain ⟨rl₀, hrl₀, rfl⟩ := List.mem_map.mp hrl
      obtain ⟨hmem, -⟩ := sumRules_mem hrl₀
      obtain ⟨g1, g2, g3, g4⟩ := h5 rl₀.rhs hmem
      refine ⟨g1, g2, Expr.constsResolve_of_find hdomBare g3, g4, ?_⟩
      intro lvls pins hf
      simp only [auxRuleFireR] at hf
      split at hf
      · next lvls' pins' hsyn =>
        obtain ⟨rfl, rfl⟩ : lvls' = lvls ∧ pins' = pins := by
          injection hf with a b; exact ⟨a, b⟩
        obtain ⟨k1, k2, k3, k4⟩ := nestedRuleSyn_inv hsyn
        refine ⟨k1, k2, fun pin hpin => ?_, ?_⟩
        · obtain ⟨p1, p2, p3, p4⟩ := k3 pin hpin
          exact ⟨p1, p2, Expr.constsResolve_of_find hdomEnv p3, p4⟩
        · obtain ⟨pre, dom, body, bm, D, e1, e2, e3, -⟩ := k4
          exact ⟨pre, dom, body, bm, D, e1, e2, e3⟩
      · exact nomatch hf

end ConLeche.Cached
