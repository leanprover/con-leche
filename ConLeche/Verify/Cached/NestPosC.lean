module

public import ConLeche.Cached.CheckerC
public import ConLeche.Verify.BridgeDecl
public import ConLeche.Verify.Cached.SimC
import ConLeche.Verify.Cached.BridgeCS2
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.SimCS
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.InstLevels
import ConLeche.Verify.InferLemmas
public import ConLeche.Verify.Inductives.NestScope
public section

/-!
# The positivity function at the cached driver

`nestPos` (`Kernel/Inductives/Positivity.lean`) and the install's
positivity stage (`checkBlockPositivity`, `BlockInstall.lean`) are
written once, over `CheckerOps`; the cached driver runs them at the
shared operations (`sharedOpsC`), the model at the fueled ones.  This
file is the simulation: a successful cached run is reproduced by the
fueled one, with the same result (`SimC`, `Verify/Cached/SimC.lean`).

The only operations the function calls are `whnf` (every step), and at
the install stage `inferType`/`ensureSort` (U2); their simulations need
the input WELL SCOPED at its depth, which the walk keeps: a member
constructor's type is closed, its members abstracted to holes below the
walk's depth; opening a field instantiates at a fresh variable; a
container frame instantiates a closed stored constructor type at the
frame's holes and at parameters without local variables.
-/

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## The run's state: container lookups of closed constructor types -/

/-- The container lookups the state records read closed constructor
types. -/
@[expose] def NestStOk (st : NestState) : Prop :=
  ∀ C r, (C, r) ∈ st.ctorsOf → ∀ q, r = some q → ∀ x ∈ q.2, x.1.type.hasFvar = false

theorem nestContainer_closed {ctx : NestCtx} (hc : NestCtxOk ctx) {C : Name}
    {q : Nat × List (ConstantVal × Nat)} (h : nestContainer ctx C = some q) :
    ∀ x ∈ q.2, x.1.type.hasFvar = false := by
  unfold nestContainer at h
  split at h
  · dsimp only at h
    generalize hcs : List.filterMap _ ctx.consts = cs at h
    have hall : ∀ y ∈ cs, y.1.type.hasFvar = false := by
      intro y hy
      rw [← hcs] at hy
      obtain ⟨ci, hci, hmap⟩ := List.mem_filterMap.mp hy
      split at hmap
      · split at hmap
        · split at hmap
          · split at hmap
            · simp only [Option.some.injEq] at hmap
              subst hmap
              exact hc.1 _ hci
            · exact nomatch hmap
          · exact nomatch hmap
        · exact nomatch hmap
      · exact nomatch hmap
    cases cs with
    | nil => simp only [Option.some.injEq] at h; subst h; intro x hx; exact nomatch hx
    | cons y0 rest =>
      simp only [Option.some.injEq] at h
      subst h
      intro x hx
      simp only [List.mem_reverse, List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hall y hy
  · exact nomatch h

theorem lookup_mem {β : Type} :
    ∀ {l : List (Name × β)} {a : Name} {b : β}, l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => nomatch h
  | (x, y) :: l, a, b, h => by
    simp only [List.lookup] at h
    split at h
    · next hxa =>
      simp only [Option.some.injEq] at h
      subst h
      have : a = x := by simpa using hxa
      subst this
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

theorem nestContainerC_ok {ctx : NestCtx} (hc : NestCtxOk ctx) {st : NestState}
    (hst : NestStOk st) (C : Name) :
    NestStOk (nestContainerC ctx st C).2 ∧
      ∀ q, (nestContainerC ctx st C).1 = some q → ∀ x ∈ q.2, x.1.type.hasFvar = false := by
  unfold nestContainerC
  split
  · next r hr =>
    refine ⟨hst, fun q hq x hx => ?_⟩
    exact hst C r (lookup_mem hr) q hq x hx
  · refine ⟨fun C' r hm q hq x hx => ?_, fun q hq x hx => nestContainer_closed hc hq x hx⟩
    rcases List.mem_cons.mp hm with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact nestContainer_closed hc hq x hx
    · exact hst C' r h q hq x hx

/-! ## The environment-reading steps (no operation) -/

section Pure

variable {env : Env} {s₀ : CState}

theorem nestInstTypeS_sim {ctx : NestCtx} (hc : NestCtxOk ctx) (hs : CSOK mode env s₀)
    (hi : Nat) (key : NestKey) :
    SimC mode env s₀ (fun v w => v = w ∧ v.2.hasFvar = false)
      (nestInstType (m := CheckCM) ctx hi key) (nestInstType (m := FueledM) ctx hi key) := by
  unfold nestInstType
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ cv cv' hs₁ hP => ?_)
  obtain ⟨rfl, hcv⟩ := hP
  have hcl : cv.type.hasFvar = false := by
    split at hcv
    · next cv₀ caps hf =>
      simp only [Option.some.injEq] at hcv
      subst hcv
      exact hc.2 _ _ hf
    · exact nomatch hcv
  dsimp only
  split
  case isFalse => exact SimC.throw_bind
  split
  case isFalse => exact SimC.throw_bind
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ ty ty' hs₂ hP => ?_)
  obtain ⟨rfl, -⟩ := hP
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ sv sv' hs₃ hP => ?_)
  obtain ⟨rfl, -⟩ := hP
  split
  · exact SimC.throw_bind
  refine SimC.bind (SimC.liftFueled _ _ hs₃) (fun s₄ b b' hs₄ hb => ?_)
  obtain rfl : b = b' := hb
  split
  · exact SimC.pure hs₄ ⟨rfl, by rw [Expr.hasFvar_instantiateLevelParams]; exact hcl⟩
  · exact SimC.throw_bind

theorem nestGrowGroupS_sim {ctx : NestCtx} (hc : NestCtxOk ctx) (hi : Nat) (us : List Level)
    (ds : List Expr) :
    ∀ (cs : List Name) (grp : List (Name × Expr)) {s₀ : CState}, CSOK mode env s₀ →
      (∀ x ∈ grp, x.2.hasFvar = false) →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ x ∈ v, x.2.hasFvar = false)
        (nestGrowGroup (m := CheckCM) ctx hi us ds cs grp)
        (nestGrowGroup (m := FueledM) ctx hi us ds cs grp)
  | [], grp, _, hs, hg => SimC.pure hs ⟨rfl, hg⟩
  | c :: cs, grp, _, hs, hg => by
    unfold nestGrowGroup
    refine SimC.bind (nestInstTypeS_sim hc hs hi _) (fun s₁ q q' hs₁ hP => ?_)
    obtain ⟨rfl, hq⟩ := hP
    exact nestGrowGroupS_sim hc hi us ds cs _ hs₁ (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hg x hx
      · simp only [List.mem_singleton] at hx; subst hx; exact hq)

theorem nestGroupCtorsS_sim {ctx : NestCtx} (hc : NestCtxOk ctx) (nPc : Nat) :
    ∀ (cs : List Name) (st : NestState) {s₀ : CState}, CSOK mode env s₀ → NestStOk st →
      SimC mode env s₀
        (fun v w => v = w ∧ (∀ x ∈ v.1, x.1.type.hasFvar = false) ∧ NestStOk v.2)
        (nestGroupCtors (m := CheckCM) ctx nPc cs st)
        (nestGroupCtors (m := FueledM) ctx nPc cs st)
  | [], st, _, hs, hst => SimC.pure hs ⟨rfl, ⟨(fun _ h => nomatch h), hst⟩⟩
  | c :: cs, st, _, hs, hst => by
    unfold nestGroupCtors
    obtain ⟨hst', hq⟩ := nestContainerC_ok hc hst c
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ q q' hs₁ hP => ?_)
    obtain ⟨rfl, hqe⟩ := hP
    dsimp only
    split
    · refine SimC.bind (nestGroupCtorsS_sim hc nPc cs _ hs₁ hst') (fun s₂ r r' hs₂ hR => ?_)
      obtain ⟨rfl, hr, hstr⟩ := hR
      exact SimC.pure hs₂ ⟨rfl, ⟨(fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · exact hq q hqe x hx
        · exact hr x hx), hstr⟩⟩
    · exact SimC.throw_bind

end Pure

/-! ## The walk -/

section Walk

variable {env : Env}

/-- **The simulation a walk's recursive call provides**: at a
well-scoped input and a state of closed container lookups. -/
@[expose] def RecSimC (mode : CheckMode) (env : Env)
    (rec : List NestHole → Nat → Nat → Expr → NestState →
      CheckCM (NestFieldKind × Expr × NestState))
    (rec' : List NestHole → Nat → Nat → Expr → NestState →
      FueledM (NestFieldKind × Expr × NestState)) : Prop :=
  ∀ (prog : List NestHole) (dep kb : Nat) (e : Expr) (st : NestState) {s₀ : CState},
    CSOK mode env s₀ → WScoped dep e → NestStOk st →
    SimC mode env s₀ (fun v w => v = w ∧ NestStOk v.2.2 ∧ WScoped dep v.2.1) (rec prog dep kb e st)
      (rec' prog dep kb e st)

variable {rec : List NestHole → Nat → Nat → Expr → NestState →
    CheckCM (NestFieldKind × Expr × NestState)}
  {rec' : List NestHole → Nat → Nat → Expr → NestState →
    FueledM (NestFieldKind × Expr × NestState)}

theorem nestFieldsS_sim (hrec : RecSimC mode env rec rec')
    (prog : List NestHole) (base : Nat) (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) {s₀ : CState}, CSOK mode env s₀ →
      WScoped (base + j) cur → NestStOk st →
      SimC mode env s₀ (fun v w => v = w ∧ NestStOk v.2.2.2 ∧
          (∀ (i : Nat) (nd : Expr × BinderMeta), v.2.1[i]? = some nd →
            WScoped (base + j + i) nd.1) ∧ WScoped (base + j + v.2.1.length) v.2.2.1)
        (nestFields rec prog base err nF j cur st)
        (nestFields rec' prog base err nF j cur st)
  | 0, _, _, st, _, hs, hw, hst =>
    SimC.pure hs ⟨rfl, hst, fun _ _ h => by simp at h, by simpa using hw⟩
  | nF + 1, j, cur, st, _, hs, hw, hst => by
    unfold nestFields
    split
    · next a b bm =>
      simp only [WScoped] at hw
      refine SimC.bind (hrec prog (base + j) 0 a st hs hw.1 hst) (fun s₁ r r' hs₁ hR => ?_)
      obtain ⟨rfl, hst₁, hnd⟩ := hR
      rcases r with ⟨k, nd, st₁⟩
      dsimp only
      have hw' : WScoped (base + (j + 1)) (b.instantiate1 (.fvar (base + j) a)) := by
        rw [show base + (j + 1) = base + j + 1 by omega]
        exact WScoped.instantiate1 hw.1 0 hw.2
      refine SimC.bind (nestFieldsS_sim hrec prog base err nF (j + 1) _ st₁ hs₁ hw' hst₁)
        (fun s₂ q q' hs₂ hQ => ?_)
      obtain ⟨rfl, hst₂, hnds, hres⟩ := hQ
      rcases q with ⟨ks, nds, res, st₂⟩
      refine SimC.pure hs₂ ⟨rfl, hst₂, fun i x hx => ?_, by
        simp only [List.length_cons]
        rw [show base + j + (nds.length + 1) = base + (j + 1) + nds.length by omega]; exact hres⟩
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx; simpa using hnd
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        have := hnds i x hx
        rwa [show base + (j + 1) + i = base + j + (i + 1) by omega] at this
    · exact SimC.throw

theorem nestCtorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    (hrec : RecSimC mode env rec rec') (ctx : NestCtx)
    (prog : List NestHole)
    (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (sub : Name → List Level → Option Expr)
    (hds : ∀ d ∈ ds, WScoped hi d) (hsub : ∀ c us e, sub c us = some e → WScoped hi e) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState) {s₀ : CState}, CSOK mode env s₀ →
      (∀ c ∈ cs, c.1.type.hasFvar = false) → NestStOk st →
      SimC mode env s₀ (fun v w => v = w ∧ NestStOk v)
        (nestCtors ctx (sharedOpsC mode (mkFEnv env)) env rec prog hi us ds nPc sub cs st)
        (nestCtors ctx (fueledOpsM mode) env rec' prog hi us ds nPc sub cs st)
  | [], st, _, hs, _, hst => SimC.pure hs ⟨rfl, hst⟩
  | (cv, nF) :: cs, st, _, hs₀, hcs, hst => by
    unfold nestCtors
    dsimp only [sharedOpsC]
    split
    case isFalse => exact SimC.throw_bind
    refine SimC.bind (SimC.unwrapOr' hs₀) (fun s₁ crest crest' hs₁ hP => ?_)
    obtain ⟨rfl, hcr⟩ := hP
    have hwc : WScoped (hi + 0) crest := by
      rw [Nat.add_zero]
      exact wscoped_instPisWith hds (WScoped.replaceConsts_closed hsub _
        (by rw [Expr.hasFvar_instantiateLevelParams]; exact hcs _ List.mem_cons_self)) hcr
    refine SimC.bind (opE_infer_sim hμ henv hs₁ (by simpa using hwc))
      (fun s₁' ty ty' hs₁' hR => ?_)
    obtain ⟨rfl, hty⟩ := hR
    refine SimC.bind (opS_sim hμ henv hs₁' hty) (fun s₁'' u u' hs₁'' hU => ?_)
    obtain rfl : u = u' := hU
    refine SimC.bind (nestFieldsS_sim hrec prog hi _ nF 0 crest st hs₁'' hwc hst)
      (fun s₂ r r' hs₂ hR => ?_)
    obtain ⟨rfl, hst₂, -⟩ := hR
    rcases r with ⟨ks, nds, cur, st₂⟩
    dsimp only
    have htl : ∀ c ∈ cs, c.1.type.hasFvar = false := fun c hc => hcs c (List.mem_cons_of_mem _ hc)
    repeat' split
    all_goals first
      | exact SimC.pure hs₂ ⟨rfl, hst₂⟩
      | exact SimC.throw_bind
      | exact nestCtorsS_sim hμ henv hrec ctx prog hi us ds nPc sub hds hsub cs _ hs₂ htl
          hst₂
      | exact SimC.bind_pure_left (nestCtorsS_sim hμ henv hrec ctx prog hi us ds nPc sub hds
          hsub cs _ hs₂ htl hst₂)


/-- A frame's holes are well scoped above the frame. -/
theorem frameHoles_wscoped {grp : List (Name × Expr)} (hg : ∀ x ∈ grp, x.2.hasFvar = false)
    (hi : Nat) {c : Name} {e : Expr}
    (h : (grp.mapIdx fun i (x : Name × Expr) => (x.1, Expr.fvar (hi + i) x.2)).lookup c = some e) :
    WScoped (hi + grp.length) e := by
  have hm := lookup_mem h
  obtain ⟨i, hi', heq⟩ := List.mem_mapIdx.mp hm
  simp only [Prod.mk.injEq] at heq
  obtain ⟨-, rfl⟩ := heq
  simp only [WScoped]
  exact ⟨by omega, WScoped.of_not_hasFvar (hg _ (List.getElem_mem hi'))⟩

theorem nestFrameS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) (hrec : RecSimC mode env rec rec')
    (prog : List NestHole) (hi : Nat) (us : List Level) (ds : List Expr) (nPc : Nat)
    (hds : ∀ d ∈ ds, WScoped hi d) (grp : List (Name × Expr)) (st : NestState) {s₀ : CState}
    (hs : CSOK mode env s₀) (hg : ∀ x ∈ grp, x.2.hasFvar = false) (hst : NestStOk st) :
    SimC mode env s₀ (fun v w => v = w ∧ NestStOk v)
      (nestFrame ctx (sharedOpsC mode (mkFEnv env)) env rec prog hi us ds nPc grp st)
      (nestFrame ctx (fueledOpsM mode) env rec' prog hi us ds nPc grp st) := by
  unfold nestFrame
  dsimp only [sharedOpsC]
  -- K.52: the instantiation typed at the frame's depth
  have hwk : WScoped hi (Expr.mkAppN (.const (grp.headD default).1 us) ds) :=
    Expr.WScoped.mkAppN (by simp [WScoped]) hds
  refine SimC.bind (opE_infer_sim hμ henv hs hwk) (fun s₀' ty ty' hs₀' hR => ?_)
  obtain ⟨rfl, -⟩ := hR
  refine SimC.bind (nestGroupCtorsS_sim hc nPc _ st hs₀' hst) (fun s₁ q q' hs₁ hQ => ?_)
  obtain ⟨rfl, hcl, hst₁⟩ := hQ
  rcases q with ⟨ctors, st₁⟩
  dsimp only
  exact nestCtorsS_sim hμ henv hrec ctx _ (hi + grp.length) us ds nPc _
    (fun d hd => WScoped.mono (Nat.le_add_right _ _) (hds d hd))
    (fun c us' e he => by
      split at he
      · exact frameHoles_wscoped hg hi he
      · exact nomatch he) ctors st₁ hs₁ hcl hst₁

theorem nestContNewS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) (hrec : RecSimC mode env rec rec')
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (hds : ∀ d ∈ ds, WScoped (ctx.hiAt prog.length) d) (cty : Expr) (hni : cty.hasFvar = false)
    (st : NestState) {s₀ : CState} (hs : CSOK mode env s₀) (hst : NestStOk st) :
    SimC mode env s₀ (fun v w => v = w ∧ NestStOk v.2)
      (nestContNew ctx (sharedOpsC mode (mkFEnv env)) env rec prog kb n us ds nPc cty st)
      (nestContNew ctx (fueledOpsM mode) env rec' prog kb n us ds nPc cty st) := by
  have hdsw : ∀ d ∈ ds, WScoped (ctx.hiAt (nestWalkStack ctx prog ds).length) d := by
    unfold nestWalkStack; split
    · rename_i hfree
      intro x hx
      exact WScoped.of_fvarsBelow (hds x hx)
        (fvarB_le (by simpa using List.all_eq_true.mp hfree x hx))
    · exact hds
  unfold nestContNew
  refine SimC.bind (nestGrowGroupS_sim hc _ us ds _ _ hs
    (fun x hx => by simp only [List.mem_singleton] at hx; subst hx; exact hni))
    (fun s₁' g g' hs₁' hG => ?_)
  obtain ⟨rfl, hg⟩ := hG
  refine SimC.bind (nestFrameS_sim hμ henv hc hrec _ _ us ds nPc hdsw g _ hs₁' hg
    (fun C r' hm q hq x hx => hst C r' hm q hq x hx))
    (fun s₂ st₂ st₂' hs₂ hG => ?_)
  obtain ⟨rfl, hst₂⟩ := hG
  exact SimC.pure hs₂ ⟨rfl, fun C r' hm q hq x hx => hst₂ C r' hm q hq x hx⟩

theorem nestContKeyS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) (hrec : RecSimC mode env rec rec')
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (ds : List Expr) (nPc : Nat)
    (hds : ∀ d ∈ ds, WScoped (ctx.hiAt prog.length) d) (cty : Expr) (hni : cty.hasFvar = false)
    (st : NestState) {s₀ : CState} (hs : CSOK mode env s₀) (hst : NestStOk st) :
    SimC mode env s₀ (fun v w => v = w ∧ NestStOk v.2)
      (nestContKey ctx (sharedOpsC mode (mkFEnv env)) env rec prog kb n us ds nPc cty st)
      (nestContKey ctx (fueledOpsM mode) env rec' prog kb n us ds nPc cty st) := by
  unfold nestContKey
  split
  · exact SimC.throw
  · split
    · exact SimC.pure hs ⟨rfl, hst⟩
    · exact nestContNewS_sim hμ henv hc hrec prog kb n us ds nPc hds cty hni st hs hst

theorem nestContS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) (hrec : RecSimC mode env rec rec')
    (prog : List NestHole) (kb : Nat) (n : Name) (us : List Level) (args : List Expr)
    {dep : Nat} (hargs : ∀ a ∈ args, WScoped dep a) (st : NestState) {s₀ : CState}
    (hs : CSOK mode env s₀) (hst : NestStOk st) :
    SimC mode env s₀ (fun v w => v = w ∧ NestStOk v.2)
      (nestCont ctx (sharedOpsC mode (mkFEnv env)) env rec prog kb n us args st)
      (nestCont ctx (fueledOpsM mode) env rec' prog kb n us args st) := by
  unfold nestCont
  obtain ⟨hst', -⟩ := nestContainerC_ok hc hst n
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ q q' hs₁ hP => ?_)
  obtain ⟨rfl, -⟩ := hP
  dsimp only
  have hkey : ∀ {s₂ : CState}, CSOK mode env s₂ → ∀ (hck : (List.take q.1 args).all
      (fun x => x.bvarB == 0 && decide (x.fvarB ≤ ctx.hiAt prog.length)) = true)
      (cty : Expr), cty.hasFvar = false →
      SimC mode env s₂ (fun v w => v = w ∧ NestStOk v.snd)
        (nestContKey ctx (sharedOpsC mode (mkFEnv env)) env rec prog kb n us
          (List.take q.fst args) q.fst cty (nestContainerC ctx st n).snd)
        (nestContKey ctx (fueledOpsM mode) env rec' prog kb n us (List.take q.fst args) q.fst
          cty (nestContainerC ctx st n).snd) := by
    intro s₂ hs₂ hck cty hni
    refine nestContKeyS_sim hμ henv hc hrec prog kb n us _ q.1 (fun d hd => ?_) cty hni _ hs₂
      hst'
    have h1 := List.all_eq_true.mp hck d hd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    exact WScoped.of_fvarsBelow (hargs d (List.mem_of_mem_take hd)) (fvarB_le h1.2)
  repeat' split
  all_goals first
    | exact SimC.throw_bind
    | (rename_i hck
       refine SimC.bind (nestInstTypeS_sim hc hs₁ _ _) (fun s₂ r r' hs₂ hP => ?_)
       obtain ⟨rfl, hr⟩ := hP
       split
       · exact hkey hs₂ hck _ hr
       · exact SimC.throw_bind)

end Walk

/-! ## The function itself, and the install stage -/

section Top

variable {env : Env}

/-- **`nestPos` at the shared operations**: every successful cached run
is a fueled one, with the same result. -/
theorem nestPosS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) :
    ∀ fuel, RecSimC mode env (nestPos (sharedOpsC mode (mkFEnv env)) env ctx fuel)
      (nestPos (fueledOpsM mode) env ctx fuel) := by
  intro fuel
  induction fuel with
  | zero => exact fun prog dep kb e st _ _ _ _ => SimC.throw
  | succ fuel ih =>
    intro prog dep kb e st s₀ hs hw hst
    · unfold nestPos
      dsimp only [sharedOpsC]
      refine SimC.bind (opE_whnf_sim hμ henv hs hw) (fun s₁ w w' hs₁ hR => ?_)
      obtain ⟨rfl, hww⟩ := hR
      split
      · exact SimC.pure hs₁ ⟨rfl, hst, by dsimp only; split <;> assumption⟩
      · split
        · next a b bm =>
          simp only [WScoped] at hww
          split
          · exact SimC.throw
          · refine SimC.bind (ih prog (dep + 1) (kb + 1) _ st hs₁
              (WScoped.instantiate1 hww.1 0 hww.2) hst) (fun s₂ r r' hs₂ hR => ?_)
            obtain ⟨rfl, hst₂, hwb⟩ := hR
            rcases r with ⟨k, nb, st₂⟩
            exact SimC.pure hs₂ ⟨rfl, hst₂, by
              simp only [WScoped]; exact ⟨hww.1, WScoped.abstract1 0 hwb⟩⟩
        · split
          · repeat' split
            all_goals first
              | exact SimC.throw
              | exact SimC.pure hs₁ ⟨rfl, hst, hww⟩
          · split
            · exact SimC.throw
            · refine SimC.bind (nestContS_sim hμ henv hc ih prog kb _ _ _
                (Expr.WScoped.getAppArgs hww) st hs₁ hst) (fun s₂ r r' hs₂ hR => ?_)
              obtain ⟨rfl, hst₂⟩ := hR
              rcases r with ⟨k, st₂⟩
              exact SimC.pure hs₂ ⟨rfl, hst₂, hww⟩
          · exact SimC.throw


/-- A telescope closed over well-scoped pieces is well scoped. -/
theorem closeTelescope_wscoped :
    ∀ (nds : List (Expr × BinderMeta)) (i : Nat) (body : Expr),
      (∀ (k : Nat) (nd : Expr × BinderMeta), nds[k]? = some nd → WScoped (i + k) nd.1) →
      WScoped (i + nds.length) body → WScoped i (closeTelescope nds i body)
  | [], i, body, _, hb => by simpa [closeTelescope] using hb
  | (dom, bm) :: bs, i, body, h, hb => by
    simp only [closeTelescope, WScoped]
    refine ⟨by simpa using h 0 _ rfl, WScoped.abstract1 0 (closeTelescope_wscoped bs (i + 1) body
      (fun k nd hk => ?_) ?_)⟩
    · have := h (k + 1) nd (by simpa using hk)
      rwa [show i + (k + 1) = i + 1 + k by omega] at this
    · rw [show i + 1 + bs.length = i + (List.length ((dom, bm) :: bs)) by simp; omega]
      exact hb

theorem nestMemberCtorS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) (nF : Nat) {crest : Expr} (hw : WScoped (ctx.hiAt 0) crest)
    (st : NestState) {s₀ : CState} (hs : CSOK mode env s₀) (hst : NestStOk st) :
    SimC mode env s₀ (fun v w => v = w ∧ NestStOk v.2.2 ∧ WScoped (ctx.hiAt 0) v.2.1)
      (nestMemberCtor (sharedOpsC mode (mkFEnv env)) env ctx nF crest st)
      (nestMemberCtor (fueledOpsM mode) env ctx nF crest st) := by
  unfold nestMemberCtor
  dsimp only
  refine SimC.bind (nestFieldsS_sim (nestPosS_sim hμ henv hc (whnfWalkFuel crest))
    [] _ _ nF 0 crest st hs
    (by simpa using hw) hst) (fun s₁ r r' hs₁ hR => ?_)
  obtain ⟨rfl, hst₁, hnds, hcur⟩ := hR
  rcases r with ⟨ks, nds, cur, st₁⟩
  dsimp only
  have hN : WScoped (ctx.hiAt 0) (closeTelescope nds (ctx.hiAt 0) cur) :=
    closeTelescope_wscoped nds _ cur (fun k nd hk => by simpa using hnds k nd hk)
      (by simpa using hcur)
  repeat' split
  all_goals first
    | exact SimC.throw_bind
    | exact SimC.throw
    | exact SimC.pure hs₁ ⟨rfl, hst₁, hN⟩

theorem nestNoMemberConstS_sim {ctx : NestCtx} {s₀ : CState} (hs : CSOK mode env s₀) (e : Expr) :
    SimC mode env s₀ (fun v w => v = w ∧ True)
      (nestNoMemberConst (m := CheckCM) ctx e) (nestNoMemberConst (m := FueledM) ctx e) := by
  unfold nestNoMemberConst
  split
  · exact SimC.throw
  · exact SimC.pure hs ⟨rfl, trivial⟩

theorem nestMemberCtorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState) {s₀ : CState}, CSOK mode env s₀ →
      (∀ c ∈ cs, c.1.type.hasFvar = false) → NestStOk st →
      SimC mode env s₀ (fun v w => v = w ∧ NestStOk v.2.2 ∧ ∀ n ∈ v.2.1, WScoped (ctx.hiAt 0) n)
        (nestMemberCtors (sharedOpsC mode (mkFEnv env)) env ctx holes cs st)
        (nestMemberCtors (fueledOpsM mode) env ctx holes cs st)
  | [], st, _, hs, _, hst => SimC.pure hs ⟨rfl, hst, fun _ h => nomatch h⟩
  | c :: cs, st, _, hs, hcs, hst => by
    unfold nestMemberCtors
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ crest crest' hs₁ hP => ?_)
    obtain ⟨rfl, hcr⟩ := hP
    refine SimC.bind (nestMemberCtorS_sim hμ henv hc c.2
      (memberCrest_wscoped hholes hpar (hcs c List.mem_cons_self) hcr) st hs₁ hst)
      (fun s₃' r r' hs₃' hR => ?_)
    obtain ⟨rfl, hst₃, hwN⟩ := hR
    rcases r with ⟨ks, tyN, st₃⟩
    dsimp only
    refine SimC.bind (nestNoMemberConstS_sim hs₃' _) (fun s₃ u u' hs₃ hU => ?_)
    obtain ⟨rfl, -⟩ := hU
    refine SimC.bind (nestMemberCtorsS_sim hμ henv hc hholes hpar cs st₃ hs₃
      (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc')) hst₃) (fun s₄ q q' hs₄ hQ => ?_)
    obtain ⟨rfl, hst₄, hwq⟩ := hQ
    rcases q with ⟨kss, nss, st₄⟩
    refine SimC.pure hs₄ ⟨rfl, hst₄, fun n hn => ?_⟩
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hwN
    · exact hwq n hn

theorem nestBlockCtorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : NestState) {s₀ : CState},
      CSOK mode env s₀ → (∀ cs ∈ css, ∀ c ∈ cs, c.1.type.hasFvar = false) → NestStOk st →
      SimC mode env s₀ (fun v w => v = w ∧ NestStOk v.2.2 ∧
          ∀ ns ∈ v.2.1, ∀ n ∈ ns, WScoped (ctx.hiAt 0) n)
        (nestBlockCtors (sharedOpsC mode (mkFEnv env)) env ctx holes css st)
        (nestBlockCtors (fueledOpsM mode) env ctx holes css st)
  | [], st, _, hs, _, hst => SimC.pure hs ⟨rfl, hst, fun _ h => nomatch h⟩
  | cs :: css, st, _, hs, hcs, hst => by
    unfold nestBlockCtors
    refine SimC.bind (nestMemberCtorsS_sim hμ henv hc hholes hpar cs st hs
      (hcs cs List.mem_cons_self) hst) (fun s₁ r r' hs₁ hR => ?_)
    obtain ⟨rfl, hst₁, hw₁⟩ := hR
    rcases r with ⟨kss, nss, st₁⟩
    dsimp only
    refine SimC.bind (nestBlockCtorsS_sim hμ henv hc hholes hpar css st₁ hs₁
      (fun cs' hc' => hcs cs' (List.mem_cons_of_mem _ hc')) hst₁) (fun s₂ q q' hs₂ hQ => ?_)
    obtain ⟨rfl, hst₂, hw₂⟩ := hQ
    rcases q with ⟨ksss, nsss, st₂⟩
    refine SimC.pure hs₂ ⟨rfl, hst₂, fun ns hns => ?_⟩
    rcases List.mem_cons.mp hns with rfl | hns
    · exact hw₁
    · exact hw₂ ns hns

/-- The per-field sort walk at the shared operations
(#175: the large-eliminator escape admits a field that is
one of the residual's index expressions). -/
theorem checkStructFieldSortsIS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {isProp large : Bool}
    {s : Level} {nP : Nat} {fvs idxArgs : List Expr}
    (hfvs : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      WScoped (nP + i) (Expr.fvarTypeD x)) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkStructFieldSortsI (sharedOpsC mode (mkFEnv env)) env isProp large
          s nP fvs idxArgs j)
        (checkStructFieldSortsI (fueledOpsM mode) env isProp large s nP fvs idxArgs j)
  | 0, s₀, hs => SimC.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkStructFieldSortsI
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ fv fv' hs₁ hP => ?_)
    obtain ⟨rfl, hfe⟩ := hP
    refine SimC.bind (opE_infer_sim hμ henv hs₁ (hfvs j fv hfe))
      (fun s₂ ty ty' hs₂ hP₂ => ?_)
    obtain ⟨rfl, htyW⟩ := hP₂
    refine SimC.bind (opS_sim hμ henv hs₂ htyW)
      (fun s₃ u u' hs₃ hP₃ => ?_)
    obtain rfl : u = u' := hP₃
    by_cases hnp : (!isProp) = true
    · simp only [if_pos hnp]
      refine SimC.bind (SimC.liftFueled _ _ hs₃)
        (fun s₃ c c' hs₃ hC => ?_)
      obtain rfl : c = c' := hC
      cases c with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.throw_bind
      | true =>
        simp only [↓reduceIte]
        refine SimC.bind (checkStructFieldSortsIS_sim hμ henv hfvs hs₃)
          (fun s₄ rest rest' hs₄ hR => ?_)
        obtain rfl : rest = rest' := hR
        exact SimC.pure hs₄ rfl
    · simp only [if_neg hnp]
      by_cases hl : large = true
      · simp only [if_pos hl]
        by_cases hz : (Level.isEquiv u .zero == some true || idxArgs.contains fv) = true
        · simp only [if_pos hz]
          refine SimC.bind (checkStructFieldSortsIS_sim hμ henv hfvs hs₃)
            (fun s₄ rest rest' hs₄ hR => ?_)
          obtain rfl : rest = rest' := hR
          exact SimC.pure hs₄ rfl
        · simp only [if_neg hz]
          exact SimC.throw_bind
      · simp only [if_neg hl]
        refine SimC.bind (checkStructFieldSortsIS_sim hμ henv hfvs hs₃)
          (fun s₄ rest rest' hs₄ hR => ?_)
        obtain rfl : rest = rest' := hR
        exact SimC.pure hs₄ rfl

/-- U2 at the shared operations. -/
theorem checkAbsCtorTysS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    {holes : List Expr} (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) :
    ∀ (cs : List (ConstantVal × Nat)) (ns : List Expr) {s₀ : CState}, CSOK mode env s₀ →
      (∀ c ∈ cs, c.1.type.hasFvar = false) → (∀ n ∈ ns, WScoped (ctx.hiAt 0) n) →
      SimC mode env s₀ RelVC
        (checkAbsCtorTys (sharedOpsC mode (mkFEnv env)) env ctx holes cs ns)
        (checkAbsCtorTys (fueledOpsM mode) env ctx holes cs ns)
  | [], _, _, hs, _, _ => SimC.pure hs rfl
  | _ :: _, [], _, hs, _, _ => SimC.pure hs rfl
  | c :: cs, n :: ns, _, hs, hcs, hns => by
    unfold checkAbsCtorTys
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ crest crest' hs₁ hP => ?_)
    obtain ⟨rfl, hcr⟩ := hP
    refine SimC.bind (opE_infer_sim hμ henv hs₁
      (memberCrest_wscoped hholes hpar (hcs c List.mem_cons_self) hcr)) (fun s₂ ty ty' hs₂ hR => ?_)
    obtain ⟨rfl, hty⟩ := hR
    refine SimC.bind (opS_sim hμ henv hs₂ hty) (fun s₃ u u' hs₃ hU => ?_)
    obtain rfl : u = u' := hU
    have hW : WScoped (ctx.hiAt 0) n := hns n List.mem_cons_self
    split
    case isFalse => exact SimC.throw
    refine SimC.bind (SimC.unwrapOr' hs₃) (fun s₄ xq xq' hs₄ hP => ?_)
    obtain ⟨rfl, hxq⟩ := hP
    have hxPos : ∀ (i : Nat) (x : Expr), xq.1[i]? = some x →
        WScoped (ctx.hiAt 0 + i) (Expr.fvarTypeD x) := by
      intro i x hx
      obtain ⟨ty, rfl⟩ := openPisAtFvars_index _ _ _ hxq i x hx
      have hw := (openPisAtFvars_WScoped _ _ _ hxq hW).1 _ (List.mem_of_getElem? hx)
      simp only [WScoped] at hw
      exact hw.2
    refine SimC.bind (checkStructFieldSortsIS_sim hμ henv hxPos hs₄)
      (fun s₅ r r' hs₅ hR => ?_)
    obtain rfl : r = r' := hR
    exact checkAbsCtorTysS_sim hμ henv hholes hpar cs ns hs₅
      (fun c' hc' => hcs c' (List.mem_cons_of_mem _ hc'))
      (fun n' hn' => hns n' (List.mem_cons_of_mem _ hn'))

theorem checkAbsCtorTysAllS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {ctx : NestCtx} {holes : List Expr}
    (hholes : ∀ x ∈ holes, WScoped (ctx.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty)
    (hpar : ∀ x ∈ ctx.params, WScoped (ctx.hiAt 0) x) :
    ∀ (css : List (List (ConstantVal × Nat))) (nss : List (List Expr)) {s₀ : CState},
      CSOK mode env s₀ →
      (∀ cs ∈ css, ∀ c ∈ cs, c.1.type.hasFvar = false) →
      (∀ ns ∈ nss, ∀ n ∈ ns, WScoped (ctx.hiAt 0) n) →
      SimC mode env s₀ RelVC
        (checkAbsCtorTysAll (sharedOpsC mode (mkFEnv env)) env ctx holes css nss)
        (checkAbsCtorTysAll (fueledOpsM mode) env ctx holes css nss)
  | [], _, _, hs, _, _ => SimC.pure hs rfl
  | _ :: _, [], _, hs, _, _ => SimC.pure hs rfl
  | cs :: css, ns :: nss, _, hs, hcs, hns => by
    unfold checkAbsCtorTysAll
    refine SimC.bind (checkAbsCtorTysS_sim hμ henv hholes hpar cs ns hs (hcs cs List.mem_cons_self)
      (hns ns List.mem_cons_self)) (fun s₁ u u' hs₁ hU => ?_)
    obtain rfl : u = u' := hU
    exact checkAbsCtorTysAllS_sim hμ henv hholes hpar css nss hs₁
      (fun cs' hc' => hcs cs' (List.mem_cons_of_mem _ hc'))
      (fun ns' hn' => hns ns' (List.mem_cons_of_mem _ hn'))

theorem nestSeedsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {ctx : NestCtx}
    (hc : NestCtxOk ctx) :
    ∀ (ks : List (NestKey × Nat)) (st : NestState) {s₀ : CState}, CSOK mode env s₀ →
      (∀ k ∈ ks, ∀ x ∈ k.1.ds, WScoped (ctx.hiAt 0) x) → NestStOk st →
      SimC mode env s₀ (fun v w => v = w ∧ NestStOk v)
        (nestSeeds (sharedOpsC mode (mkFEnv env)) env ctx ks st)
        (nestSeeds (fueledOpsM mode) env ctx ks st)
  | [], st, _, hs, _, hst => SimC.pure hs ⟨rfl, hst⟩
  | (key, nPc) :: ks, st, _, hs, hw, hst => by
    unfold nestSeeds
    split
    case isFalse => exact SimC.throw_bind
    refine SimC.bind (nestInstTypeS_sim hc hs _ _) (fun s₀' ni ni' hs₀' hN => ?_)
    obtain ⟨rfl, hni⟩ := hN
    refine SimC.bind (nestContKeyS_sim hμ henv hc (nestPosS_sim hμ henv hc _) [] 0 key.cname
      key.lvls key.ds nPc (fun x hx => hw _ List.mem_cons_self x hx) ni.2 hni st hs₀' hst)
      (fun s₁ r r' hs₁ hR => ?_)
    obtain ⟨rfl, hst₁⟩ := hR
    exact nestSeedsS_sim hμ henv hc ks _ hs₁ (fun k hk => hw k (List.mem_cons_of_mem _ hk)) hst₁

/-- **The walk's context at the shared operations** (`blockNestCtx`, no
operation run): the same value, a context whose stored constants are
closed, its holes and canonical variables well scoped at its depth, one
canonical variable per parameter. -/
theorem blockNestCtxS_sim (henv : EnvWF env) (p : BlockShape) (cvTas : List ConstantVal)
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type) {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀
      (fun v w => v = w ∧ NestCtxOk v.1 ∧
        (∀ x ∈ v.2, WScoped (v.1.hiAt 0) x ∧ ∃ i ty, x = .fvar i ty) ∧
        (∀ x ∈ v.1.params, WScoped (v.1.hiAt 0) x) ∧ v.1.params.length = v.1.nP ∧
        nestHoles v.1 = some v.2 ∧ v.1.nP = p.nP)
      (blockNestCtx (m := CheckCM) p cvTas env.find? env.consts)
      (blockNestCtx (m := FueledM) p cvTas env.find? env.consts) := by
  unfold blockNestCtx
  refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ cvTa0 cvTa0' hs₁ hP => ?_)
  obtain ⟨rfl, h0⟩ := hP
  have hw0 : WScoped 0 cvTa0.type := hT _ (List.mem_of_mem_head? h0)
  refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ pq pq' hs₂ hP => ?_)
  obtain ⟨rfl, hpq⟩ := hP
  have hctx : NestCtxOk (p.nestCtx pq.1 env.find? env.consts) :=
    ⟨fun ci hci => (henv ci hci).1,
      fun n ci hf => (henv ci (List.mem_of_find?_eq_some hf)).1⟩
  have hpar : ∀ x ∈ pq.1, WScoped ((p.nestCtx pq.1 env.find? env.consts).hiAt 0) x := by
    intro x hx
    have := (openPisAtFvars_WScoped p.nP cvTa0.type 0 hpq hw0).1 x hx
    rw [Nat.zero_add] at this
    exact WScoped.mono (by simp [NestCtx.hiAt, BlockShape.nestCtx]) this
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ holes holes' hs₃ hP => ?_)
  obtain ⟨rfl, hh⟩ := hP
  exact SimC.pure hs₃ ⟨rfl, hctx, nestHoles_ok hctx hh, hpar,
    ConLeche.Verify.openPisAtFvars_length _ hpq, hh, rfl⟩

/-- **The install's positivity stage at the shared operations**: every
successful cached run is a fueled one, its final state's container
lookups closed (the seeds continue from it). -/
theorem checkBlockPositivityS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    (p : BlockParts) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (hct : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type)
    {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ NestStOk v.2.2)
      (checkBlockPositivity (sharedOpsC mode (mkFEnv env)) env env.find? env.consts p cvTas
        ctorsAs)
      (checkBlockPositivity (fueledOpsM mode) env env.find? env.consts p cvTas ctorsAs) := by
  have hcl : ∀ cs ∈ ctorsAs, ∀ c ∈ cs, c.1.type.hasFvar = false :=
    fun cs hcs c hc => not_hasFvar_of_fvarsBelow_zero (hct cs hcs c hc).fvarsBelow
  unfold checkBlockPositivity
  refine SimC.bind (blockNestCtxS_sim henv p.toBlockShape cvTas hT hs)
    (fun s₃ r r' hs₃ hR => ?_)
  obtain ⟨rfl, hctx, hholes, hpar, -, -, -⟩ := hR
  rcases r with ⟨ctx, holes⟩
  dsimp only
  refine SimC.bind (nestBlockCtorsS_sim hμ henv hctx hholes hpar ctorsAs {} hs₃
    hcl (fun _ _ hm => nomatch hm)) (fun s₄ r r' hs₄ hR => ?_)
  obtain ⟨rfl, hstN, hwN⟩ := hR
  rcases r with ⟨kinds, normals, st⟩
  dsimp only
  refine SimC.bind (checkAbsCtorTysAllS_sim hμ henv hholes hpar ctorsAs normals
    hs₄ hcl hwN) (fun s₅ u u' hs₅ _ => ?_)
  exact SimC.pure hs₅ ⟨rfl, hstN⟩

/-- **The recursor check's seeds at the shared operations**
(`checkBlockSeeds`): every successful cached run is a fueled one, at a
state whose container lookups are closed and outside classes whose
parameters mention only the parameters. -/
theorem checkBlockSeedsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    (p : BlockShape) (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (nfs : List (List Expr)) (st : NestState) (tys : List (ConstantVal × TargetMajor × Level))
    (hT : ∀ cv ∈ cvTas, WScoped 0 cv.type)
    (htys : ∀ t ∈ tys, t.2.1.member = none → ∀ x ∈ t.2.1.ds, x.fvarB ≤ p.nP)
    (hst : NestStOk st) {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkBlockSeeds (sharedOpsC mode (mkFEnv env)) env env.find? env.consts p cvTas ctorsAs
        nfs st tys)
      (checkBlockSeeds (fueledOpsM mode) env env.find? env.consts p cvTas ctorsAs nfs st tys) := by
  unfold checkBlockSeeds
  refine SimC.bind (blockNestCtxS_sim henv p cvTas hT hs) (fun s₁ r r' hs₁ hR => ?_)
  obtain ⟨rfl, hctx, hholes, hpar, hlen, hh, hnP⟩ := hR
  rcases r with ⟨ctx, holes⟩
  dsimp only at hctx hholes hpar hlen hh hnP ⊢
  refine SimC.bind (nestSeedsS_sim hμ henv hctx _ st hs₁ (fun k hk x hx => ?_) hst)
    (fun s₂ st' st'' hs₂ hS => ?_)
  · obtain ⟨t, ht, hM, rfl⟩ := mem_targetSeeds hk
    exact (nestSeedOf_ds hh hlen (fun y hy => Expr.fvarB_le (by
      rw [hnP]; exact htys t ht hM y hy)) x hx).2 (fun y hy => (hholes y hy).1) hpar
  obtain ⟨rfl, -⟩ := hS
  exact SimC.pure hs₂ rfl

end Top

end ConLeche.Cached
