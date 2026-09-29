module

public import ConLeche.Verify.Cached.BridgeCSDecl
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.DirectInv
public import ConLeche.Verify.Cached.NestPosC
import ConLeche.Verify.Extend.Inversions

public section

/-!
# The cached uniform install at k members, bridged

`checkBlockKS` (`ConLeche/Cached/CheckerC.lean`), the cached mirror of
the uniform installer at any number of members, is reproduced by the
pure fueled `checkBlock`.  This file holds the pass (`checkBlockPassS_run`),
the stages' simulations and the `SimG` kit; the recursor stage — the
target check — its install and the `.indDecl` dispatch
(`checkBlockTailS_run`, `checkBlockKS_run`, `checkModeledOrNativeSF_run`)
are in `ConLeche/Verify/Cached/TargetRecC.lean`.

The file follows `BridgeCSDecl.lean`'s layout:

1. the index mirrors at `mkFEnv` ARE the pure stages (`*_eqC`);
2. the scoping facts every cached operation's simulation needs
   (`SimC`, `ConLeche/Verify/Cached/SimC.lean`, is stated at well-scoped
   inputs);
3. the single-environment stages as `SimC`s;
4. the rule stage, whose one rule alternates between the rule-less
   recursors' environment and the constructors' (`sharedOpsRuleR`'s
   flushes are what make that a chain of `SimC`s);
5. the assembly, and the dispatch.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche.Cached

open ConLeche
open Expr

variable {mode : CheckMode}

/-! ## 1. The index mirrors at `mkFEnv` are the pure stages -/

section Mirrors

variable (ops : CheckerOps CheckCM)

theorem checkBlockTeleF_eqC (env : Env) (nP : Nat) (ms : MemberShape) :
    checkBlockTeleF ops (mkFEnv env) nP ms = checkBlockTele ops env nP ms := by
  unfold checkBlockTeleF checkBlockTele
  simp only [checkConstantValF_eq, checkSumTeleF_pushC]

theorem checkBlockTelesF_eqC (env : Env) (nP : Nat) :
    ∀ mss : List MemberShape,
      checkBlockTelesF ops (mkFEnv env) nP mss = checkBlockTeles ops env nP mss
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockTelesF, checkBlockTeles, checkBlockTeleF_eqC,
      checkBlockTelesF_eqC env nP rest]

theorem checkBlockDomsAtF_eqC (env : Env) (off : Nat) (fvs doms : List Expr) :
    ∀ j : Nat, checkBlockDomsAtF ops (mkFEnv env) off fvs doms j
      = checkBlockDomsAt ops env off fvs doms j
  | 0 => rfl
  | j + 1 => by
    simp only [checkBlockDomsAtF, checkBlockDomsAt, mkFEnv_env,
      checkBlockDomsAtF_eqC env off fvs doms j]

theorem checkBlockAgreeF_eqC (env : Env) (nP : Nat) (cvTa0 : ConstantVal) (s0 : Level) :
    ∀ cvs : List (ConstantVal × Level),
      checkBlockAgreeF ops (mkFEnv env) nP cvTa0 s0 cvs
        = checkBlockAgree ops env nP cvTa0 s0 cvs
  | [] => rfl
  | (cvTa, s) :: rest => by
    simp only [checkBlockAgreeF, checkBlockAgree, checkBlockDomsAtF_eqC,
      checkBlockAgreeF_eqC env nP cvTa0 s0 rest]

theorem consBlockIndsF_mkFEnv (p₁ : BlockShape) (isRec : Bool) :
    ∀ (cvTas : List ConstantVal) (i : Nat) (env : Env),
      consBlockIndsF p₁ isRec cvTas i (mkFEnv env) = mkFEnv (consBlockInds p₁ isRec cvTas i env)
  | [], _, _ => rfl
  | cvTa :: rest, i, env => by
    simp only [consBlockIndsF, consBlockInds, push_mkFEnv]
    exact consBlockIndsF_mkFEnv p₁ isRec rest (i + 1) _

theorem checkBlockIndsF_eqC (env : Env) (p : BlockParts) (isRec : Bool) :
    checkBlockIndsF ops (mkFEnv env) p isRec
      = checkBlockInds ops env p isRec >>= fun r => pure (mkFEnv r.1, r.2) := by
  unfold checkBlockIndsF checkBlockInds
  rcases hm : p.members with _ | ⟨ms0, rest⟩
  · rfl
  · simp only [checkBlockTeleF_eqC, checkBlockTelesF_eqC, checkBlockAgreeF_eqC, bind_assoc,
      pure_bind, consBlockIndsF_mkFEnv]

theorem checkBlockCtorsF_eqC (env₀ env : Env) (p : BlockShape) :
    ∀ l : List (MemberShape × ConstantVal),
      checkBlockCtorsF ops (mkFEnv env₀) (mkFEnv env) p l = checkBlockCtors ops env₀ env p l
  | [] => rfl
  | (ms, cvTa) :: rest => by
    simp only [checkBlockCtorsF, checkBlockCtors, checkSumCtorsF_eq,
      checkBlockCtorsF_eqC env₀ env p rest]

theorem checkBlockIdxSortsF_eqC (env : Env) (p : BlockShape) :
    ∀ l : List (MemberShape × ConstantVal),
      checkBlockIdxSortsF ops (mkFEnv env) p l = checkBlockIdxSorts ops env p l
  | [] => rfl
  | (ms, cvTa) :: rest => by
    simp only [checkBlockIdxSortsF, checkBlockIdxSorts, checkStructFieldSortsIF_eq,
      checkBlockIdxSortsF_eqC env p rest]

end Mirrors

theorem consBlockCtorsF_mkFEnv (nP : Nat) :
    ∀ (ctorsAs : List (List (ConstantVal × Nat))) (env : Env),
      consBlockCtorsF nP ctorsAs (mkFEnv env) = mkFEnv (consBlockCtors nP ctorsAs env)
  | [], _ => rfl
  | ctorsA :: rest, env => by
    simp only [consBlockCtorsF, consBlockCtors, consSumCtorsF_mkFEnv]
    exact consBlockCtorsF_mkFEnv nP rest _

/-! ## 2. Scoping

Every cached operation's simulation is stated at a well-scoped input
(`WScoped`).  Most of the stages' inputs are OPENED telescopes of
checked (fvar-free) constants, and the Verify tier's opening lemmas
cover them; the lemmas here fill the gaps.  "fvar-free" is stated as
`WScoped 0` (`ws0_hasFvar`), which composes with the opening lemmas. -/

theorem ws0_hasFvar {e : Expr} (h : WScoped 0 e) : e.hasFvar = false :=
  not_hasFvar_of_fvarsBelow_zero (WScoped.fvarsBelow h)

theorem ws_of_ws0 {d : Nat} {e : Expr} (h : WScoped 0 e) : WScoped d e :=
  WScoped.of_not_hasFvar (ws0_hasFvar h)

/-- An opened telescope's variables carry types scoped at their own
frame. -/
theorem openers_typeD_WScoped {n off : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e off = some (fvs, body)) (he : WScoped off e) :
    ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (off + i) x.fvarTypeD := by
  intro i x hx
  obtain ⟨ty, rfl⟩ := openPisAtFvars_index n e off h i x hx
  have hw := (openPisAtFvars_WScoped n e off h he).1 _ (List.mem_of_getElem? hx)
  simp only [WScoped] at hw
  exact hw.2

/-! ## 3. The single-environment stages, simulated -/

section Sims

variable {env : Env}

theorem checkBlockTeleS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {nP : Nat}
    {ms : MemberShape} {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ WScoped 0 (Prod.fst v).type)
      (checkBlockTele (sharedOpsC mode (mkFEnv env)) env nP ms)
      (checkBlockTele (fueledOpsM mode) env nP ms) := by
  unfold checkBlockTele
  refine SimC.bind (checkConstantValS_sim hμ henv hs) (fun s₁ c c' hs₁ hP => ?_)
  obtain ⟨rfl, hw⟩ := hP
  refine SimC.bind (checkSumTeleS_sim hμ henv hs₁ hw) (fun s₂ r r' hs₂ hR => ?_)
  obtain ⟨rfl, hw'⟩ := hR
  obtain ⟨cvTa, sx⟩ := r
  dsimp only
  refine SimC.bind (SimC.unwrapOr' hs₂) (fun s₃ q q' hs₃ hQ => ?_)
  obtain ⟨rfl, -⟩ := hQ
  obtain ⟨tbs, tbody⟩ := q
  dsimp only
  by_cases h1 : (tbody == Expr.sort sx) = true
  case neg => simp only [h1]; exact SimC.throw_bind
  simp only [h1, if_true]
  exact SimC.pure hs₃ ⟨rfl, hw'⟩

theorem checkBlockTelesS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {nP : Nat} :
    ∀ {mss : List MemberShape} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ (fun v w => v = w ∧ ∀ r ∈ v, WScoped 0 (Prod.fst r).type)
        (checkBlockTeles (sharedOpsC mode (mkFEnv env)) env nP mss)
        (checkBlockTeles (fueledOpsM mode) env nP mss)
  | [], s₀, hs => SimC.pure hs ⟨rfl, fun _ h => nomatch h⟩
  | ms :: rest, s₀, hs => by
    unfold checkBlockTeles
    refine SimC.bind (checkBlockTeleS_sim hμ henv hs) (fun s₁ r r' hs₁ hP => ?_)
    obtain ⟨rfl, hw⟩ := hP
    refine SimC.bind (checkBlockTelesS_sim hμ henv hs₁) (fun s₂ rs rs' hs₂ hR => ?_)
    obtain ⟨rfl, hws⟩ := hR
    refine SimC.pure hs₂ ⟨rfl, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hw
    · exact hws x hx

theorem checkBlockDomsAtS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {off : Nat}
    {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockDomsAt (sharedOpsC mode (mkFEnv env)) env off fvs doms j)
        (checkBlockDomsAt (fueledOpsM mode) env off fvs doms j)
  | 0, s₀, hs => SimC.pure hs rfl
  | j + 1, s₀, hs => by
    unfold checkBlockDomsAt
    dsimp only [sharedOpsC]
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ a a' hs₁ hP => ?_)
    obtain ⟨rfl, hae⟩ := hP
    refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ b b' hs₂ hQ => ?_)
    obtain ⟨rfl, hbe⟩ := hQ
    refine SimC.bind (opB_sim hμ henv hs₂ (hc j a hae) (ht j b hbe))
      (fun s₃ c c' hs₃ hC => ?_)
    obtain rfl : c = c' := hC
    cases c with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw_bind
    | true =>
      simp only [↓reduceIte]
      exact checkBlockDomsAtS_sim hμ henv hc ht hs₃

theorem checkBlockAgreeS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {nP : Nat}
    {cvTa0 : ConstantVal} {s0 : Level} (h0 : WScoped 0 cvTa0.type) :
    ∀ {cvs : List (ConstantVal × Level)} {s₀ : CState},
      (∀ r ∈ cvs, WScoped 0 r.1.type) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockAgree (sharedOpsC mode (mkFEnv env)) env nP cvTa0 s0 cvs)
        (checkBlockAgree (fueledOpsM mode) env nP cvTa0 s0 cvs)
  | [], s₀, _, hs => SimC.pure hs rfl
  | (cvTa, s) :: rest, s₀, hcvs, hs => by
    unfold checkBlockAgree
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ tq0 tq0' hs₁ hP => ?_)
    obtain ⟨rfl, htq0⟩ := hP
    refine SimC.bind (SimC.unwrapOr' hs₁) (fun s₂ tq tq' hs₂ hQ => ?_)
    obtain ⟨rfl, htq⟩ := hQ
    have hw : WScoped 0 cvTa.type := hcvs _ List.mem_cons_self
    by_cases hl : (tq.1.length == tq0.1.length) = true
    case neg => simp only [hl]; exact SimC.throw_bind
    simp only [hl, if_true]
    refine SimC.bind (checkBlockDomsAtS_sim hμ henv ?_ ?_ hs₂) (fun s₄ _ _ hs₄ _ => ?_)
    · intro i x hx
      exact openers_typeD_WScoped htq hw i x hx
    · intro i x hx
      rw [List.getElem?_map] at hx
      obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
      exact openers_typeD_WScoped htq0 h0 i y hy
    refine SimC.bind (SimC.liftFueled _ _ hs₄) (fun s₅ b b' hs₅ hb => ?_)
    obtain rfl : b = b' := hb
    cases b
    · exact SimC.throw_bind
    · exact checkBlockAgreeS_sim hμ henv h0 (fun r hr => hcvs r (List.mem_cons_of_mem _ hr)) hs₅

theorem checkBlockIndsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockParts}
    {isRec : Bool} {s₀ : CState} (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ cv ∈ v.2.1, WScoped 0 cv.type)
      (checkBlockInds (sharedOpsC mode (mkFEnv env)) env p isRec)
      (checkBlockInds (fueledOpsM mode) env p isRec) := by
  unfold checkBlockInds
  split
  · exact SimC.throw
  · refine SimC.bind (checkBlockTeleS_sim hμ henv hs) (fun s₁ r r' hs₁ hP => ?_)
    obtain ⟨rfl, hw0⟩ := hP
    obtain ⟨cvTa0, s0⟩ := r
    dsimp only
    refine SimC.bind (checkBlockTelesS_sim hμ henv hs₁) (fun s₂ cvs cvs' hs₂ hQ => ?_)
    obtain ⟨rfl, hws⟩ := hQ
    refine SimC.bind (checkBlockAgreeS_sim hμ henv hw0 hws hs₂) (fun s₃ _ _ hs₃ _ => ?_)
    refine SimC.pure hs₃ ⟨rfl, ?_⟩
    intro cv hcv
    rcases List.mem_cons.mp hcv with rfl | hcv
    · exact hw0
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hcv
      exact hws r hr

theorem checkBlockCtorsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {env₀ : Env}
    {p : BlockShape} :
    ∀ {l : List (MemberShape × ConstantVal)} {s₀ : CState},
      (∀ x ∈ l, x.2.type.hasFvar = false) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockCtors (sharedOpsC mode (mkFEnv env)) env₀ env p l)
        (checkBlockCtors (fueledOpsM mode) env₀ env p l)
  | [], s₀, _, hs => SimC.pure hs rfl
  | (ms, cvTa) :: rest, s₀, hl, hs => by
    unfold checkBlockCtors
    refine SimC.bind (checkSumCtorsS_sim hμ henv (hl _ List.mem_cons_self) hs)
      (fun s₁ q q' hs₁ hP => ?_)
    obtain rfl : q = q' := hP
    obtain ⟨ctorsA, sortss⟩ := q
    dsimp only
    refine SimC.bind (checkBlockCtorsS_sim hμ henv
      (fun x hx => hl x (List.mem_cons_of_mem _ hx)) hs₁) (fun s₂ r r' hs₂ hR => ?_)
    obtain rfl : r = r' := hR
    exact SimC.pure hs₂ rfl

theorem checkBlockIdxSortsS_sim (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} :
    ∀ {l : List (MemberShape × ConstantVal)} {s₀ : CState},
      (∀ x ∈ l, WScoped 0 x.2.type) → CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkBlockIdxSorts (sharedOpsC mode (mkFEnv env)) env p l)
        (checkBlockIdxSorts (fueledOpsM mode) env p l)
  | [], s₀, _, hs => SimC.pure hs rfl
  | (ms, cvTa) :: rest, s₀, hl, hs => by
    unfold checkBlockIdxSorts
    refine SimC.bind (SimC.unwrapOr' hs) (fun s₁ tq tq' hs₁ hP => ?_)
    obtain ⟨rfl, htq⟩ := hP
    have hw : WScoped 0 cvTa.type := hl _ List.mem_cons_self
    have hxPos : ∀ (i : Nat) (x : Expr), (tq.1.drop p.nP)[i]? = some x →
        WScoped (p.nP + i) (Expr.fvarTypeD x) := by
      intro i x hx
      rw [List.getElem?_drop] at hx
      have := openers_typeD_WScoped htq hw (p.nP + i) x hx
      simpa using this
    refine SimC.bind (checkStructFieldSortsIS_sim hμ henv hxPos hs₁) (fun s₂ is is' hs₂ hI => ?_)
    obtain rfl : is = is' := hI
    refine SimC.bind (checkBlockIdxSortsS_sim hμ henv (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      hs₂) (fun s₃ r r' hs₃ hR => ?_)
    obtain rfl : r = r' := hR
    exact SimC.pure hs₃ rfl

end Sims


/-! ## 4. The rule stage: two environments, one state

One rule runs its first two operations at the rule-less recursors'
environment and the rest at the constructors'; `sharedOpsRuleR`
flushes entering the first and leaving the second.  `SimG` is `SimC`
with the state invariant at entry and at exit left free, so that a
chain of operations can change environment where a flush lets it. -/

/-- `SimC` across environment transitions: `Pre` of the entry state,
`Post` of the exit state. -/
@[expose] def SimG (Pre Post : CState → Prop) {β α : Type} (P : β → α → Prop) (c : CheckCM β)
    (p : FueledM α) : Prop :=
  ∀ s₀, Pre s₀ → ∀ v' s', c s₀ = .ok (v', s') → Post s' ∧ ∃ v, P v' v ∧ ∃ F, p.val F = .ok v

namespace SimG

variable {A B C : CState → Prop}

theorem ofC {env : Env} {β α : Type} {P : β → α → Prop} {c : CheckCM β} {p : FueledM α}
    (h : ∀ s₀, CSOK mode env s₀ → SimC mode env s₀ P c p) :
    SimG (CSOK mode env) (CSOK mode env) P c p :=
  fun s₀ hs v' s' hr => h s₀ hs v' s' hr

theorem pure {β α : Type} {P : β → α → Prop} {b : β} {a : α} (hAB : ∀ s, A s → B s)
    (h : P b a) : SimG A B P (Pure.pure b) (Pure.pure a) := by
  intro s₀ hs v' s' hr
  simp only [Pure.pure, StateT.pure, Except.pure, Except.ok.injEq] at hr
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hr
  exact ⟨hAB _ hs, a, h, 0, rfl⟩

theorem throw_bind {β β' α : Type} {P : β' → α → Prop} {er : CheckError}
    {k : β → CheckCM β'} {p : FueledM α} :
    SimG A B P ((throw er : CheckCM β) >>= k) p := by
  intro s₀ _ v' s' hr
  exact nomatch hr

theorem throw {β α : Type} {P : β → α → Prop} {er : CheckError} {p : FueledM α} :
    SimG A B P (throw er : CheckCM β) p := by
  intro s₀ _ v' s' hr
  exact nomatch hr

theorem bind {β β' α α' : Type} {P : β → α → Prop} {Q : β' → α' → Prop}
    {c : CheckCM β} {k : β → CheckCM β'} {p : FueledM α} {q : α → FueledM α'}
    (hx : SimG A B P c p) (hf : ∀ b a, P b a → SimG B C Q (k b) (q a)) :
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
    obtain ⟨hs', a', hQ, F₂, hp₂⟩ := hf b a hP s₁ hs₁ v' s' hr
    refine ⟨hs', a', hQ, max F₁ F₂, ?_⟩
    rw [FueledM.atF_bind]
    simp only [Bind.bind]
    rw [p.property (Nat.le_max_left F₁ F₂) hp₁]
    dsimp only [Except.bind]
    exact (q a).property (Nat.le_max_right F₁ F₂) hp₂

theorem unwrapOr {α : Type} {o : Option α} {err : CheckError} (hAB : ∀ s, A s → B s) :
    SimG A B (fun v w => v = w ∧ o = some v)
      (ConLeche.unwrapOr o err : CheckCM α) (ConLeche.unwrapOr o err : FueledM α) := by
  cases o with
  | none => exact SimG.throw
  | some a => exact SimG.pure hAB ⟨rfl, rfl⟩

theorem mono {β α : Type} {P : β → α → Prop} {c : CheckCM β} {p : FueledM α}
    {A' B' : CState → Prop} (h : SimG A B P c p) (hA : ∀ s, A' s → A s)
    (hB : ∀ s, B s → B' s) : SimG A' B' P c p :=
  fun s₀ hs v' s' hr =>
    let ⟨h1, h2⟩ := h s₀ (hA s₀ hs) v' s' hr
    ⟨hB s' h1, h2⟩

end SimG

/-- The rule stage's `inferType` at the rule-less recursors'
environment: it flushes last, so it hands on a state that is an
invariant state of ANY environment. -/
theorem ruleR_infer_simG (hμ : mode.verifiedChecks = true) {envR : Env} (henvR : EnvWF envR)
    (envT : Env) {d : Nat} {e : Expr} (hw : WScoped d e) :
    SimG (CSOK mode envR) (CSOK mode envT) (RelW d)
      ((sharedOpsRuleR mode (mkFEnv envR)).inferType envR d e)
      ((fueledOpsM mode).inferType envR d e) := by
  intro s₀ hs v' s' hr
  simp only [sharedOpsRuleR] at hr
  obtain ⟨t, s₁, hinf, hr⟩ := bindC_ok hr
  obtain ⟨hs₁, w, hrel, F, hF⟩ := opE_infer_sim hμ henvR hs hw t s₁ hinf
  obtain ⟨u, s₂, hfl, hr⟩ := bindC_ok hr
  rw [flushC_run] at hfl
  injection hfl with hfl
  obtain rfl : s₁.flushed = s₂ := congrArg Prod.snd hfl
  obtain ⟨rfl, rfl⟩ := pureC_ok hr
  exact ⟨flushC_csok hs₁.residue, w, hrel, F, hF⟩

/-! ## 5. The assembly -/

/-- The rule-less recursors' cons is a `consBlockRecs` with no rules. -/
theorem consBlockRecsBare_eq_consBlockRecs (find? : Name → Option ConstantInfo) (q : BlockShape)
    (nP : Nat) :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (env : Env),
      consBlockRecsBare q m cvRas env
        = consBlockRecs find? q nP m
            (cvRas.map fun c => (c.1, ([] : List Expr), c.2, ([] : List (ConstantVal × Nat))))
            env
  | _, [], _ => rfl
  | m, (cv, n) :: rest, env => by
    simp only [consBlockRecsBare, consBlockRecs, List.map_cons, sumRules]
    exact consBlockRecsBare_eq_consBlockRecs find? q nP (m + 1) rest _

/-- **The rule-less recursors' environment is well-formed** when their
checked types are. -/
theorem envWF_consBlockRecsBare {q : BlockShape} {cvRas : List (ConstantVal × Nat)} {env : Env}
    (henv : EnvWF env)
    (hall : ∀ c ∈ cvRas, c.1.type.hasFvar = false ∧
      c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
      c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true) :
    EnvWF (consBlockRecsBare q 0 cvRas env) := by
  rw [consBlockRecsBare_eq_consBlockRecs env.find? q 0]
  refine envWF_consBlockRecs henv ?_
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  obtain ⟨h1, h2, h3, h4⟩ := hall c hc
  exact ⟨h1, h2, h3, h4, fun _ h => nomatch h⟩

/-- The projection tables at the cached driver: operation-free, the
state unchanged, the environment the pure stage's. -/
theorem checkBlockTablesS_run (p : BlockShape) :
    ∀ (l : List (MemberShape × List (ConstantVal × Nat) × List (List Level))) (env : Env)
      {s₀ : CState} {fe' : FEnv} {s' : CState}, EnvWF env → CSOKF s₀ →
      checkBlockTablesF (m := CheckCM) .plain p l (mkFEnv env) s₀ = .ok (fe', s') →
      CSOKF s' ∧ fe' = mkFEnv fe'.env ∧ EnvWF fe'.env ∧
        checkBlockTables (m := CheckM) p l env = .ok fe'.env
  | [], env, s₀, fe', s', henv, hwf, h => by
    simp only [checkBlockTablesF] at h
    obtain ⟨rfl, rfl⟩ := pureC_ok h
    exact ⟨hwf, rfl, henv, rfl⟩
  | (ms, ctorsA, sortss) :: rest, env, s₀, fe', s', henv, hwf, h => by
    match ctorsA, sortss with
    | [cA], [sorts] =>
      simp only [checkBlockTablesF] at h
      by_cases hi : (ms.nIdx == 0) = true
      · rw [if_pos hi] at h
        obtain ⟨fe₁, s₁, h1, h⟩ := bindC_ok h
        obtain ⟨hwf₁, hfe₁, henv₁, F₁, hF₁⟩ := checkStructProjTableS_run env henv hwf h1
        rw [hfe₁] at h
        obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest fe₁.env henv₁ hwf₁ h
        refine ⟨hwf', hfe', henv', ?_⟩
        rw [checkStructProjTable_datF] at hF₁
        simp only [checkBlockTables, if_pos hi, Bind.bind, Except.bind]
        rw [hF₁]
        exact hrest
      · rw [if_neg hi] at h
        simp only [pure_bind] at h
        obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
        refine ⟨hwf', hfe', henv', ?_⟩
        simp only [checkBlockTables, if_neg hi, pure_bind]
        exact hrest
    | [], _ =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩
    | _ :: _ :: _, _ =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩
    | [_], [] =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩
    | [_], _ :: _ :: _ =>
      simp only [checkBlockTablesF, pure_bind] at h
      obtain ⟨hwf', hfe', henv', hrest⟩ := checkBlockTablesS_run p rest env henv hwf h
      exact ⟨hwf', hfe', henv', by simpa [checkBlockTables] using hrest⟩

/-- The constructors' stage stores fvar-free constructor types. -/
theorem checkBlockCtors_types {env₀ env : Env} {q : BlockShape} {F : Nat}
    {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
    {sortsss : List (List (List Level))}
    (h : checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss)) :
    ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, WScoped 0 c.1.type := by
  obtain ⟨hlen, -, hall⟩ := checkBlockCtors_inv h
  intro ctorsA hcA c hc
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hcA
  have hil : i < l.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨ctorsA', sortss, hcA', -, hcs⟩ := hall i l[i] (List.getElem?_eq_getElem hil)
  obtain rfl := Option.some.inj (hi.symm.trans hcA')
  obtain ⟨hlenC, -, hallc⟩ := checkSumCtors_inv hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hjl : j < l[i].1.ctors.length := by
    rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨-, sorts, -, hrun⟩ := hallc j (l[i].1.ctors[j]) c (List.getElem?_eq_getElem hjl) hj
  exact WScoped.of_not_hasFvar (direct_sum_ctor_typeWF hrun).1

/-- The constructors' stage stores constructors fresh in the
environment they are checked at (`checkConstantVal` rejects a name
already there). -/
theorem checkBlockCtors_fresh {env₀ env : Env} {q : BlockShape} {F : Nat}
    {l : List (MemberShape × ConstantVal)} {ctorsAs : List (List (ConstantVal × Nat))}
    {sortsss : List (List (List Level))}
    (h : checkBlockCtors (fueledOps mode F) env₀ env q l = .ok (ctorsAs, sortsss)) :
    ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, env.find? c.1.name = none := by
  obtain ⟨hlen, -, hall⟩ := checkBlockCtors_inv h
  intro ctorsA hcA c hc
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hcA
  have hil : i < l.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨ctorsA', sortss, hcA', -, hcs⟩ := hall i l[i] (List.getElem?_eq_getElem hil)
  obtain rfl := Option.some.inj (hi.symm.trans hcA')
  obtain ⟨hlenC, -, hallc⟩ := checkSumCtors_inv hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  have hjl : j < l[i].1.ctors.length := by
    rw [← hlenC]; exact (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨-, sorts, -, hrun⟩ := hallc j (l[i].1.ctors[j]) c (List.getElem?_eq_getElem hjl) hj
  obtain ⟨⟨ty', hccv⟩, -, -⟩ := checkSumCtor_shape hrun
  rw [(checkConstantVal_lps hccv).1]
  exact (checkConstantVal_inv hccv).1

/-! ### The formers' view of the constructors' index

The tail runs the positivity walk at the formers' environment through the
prefix view of the constructors' index (`FEnv.restrictTo`, `checkBlockTailS`):
every constructor pushed above the view is fresh below it, so the view
looks names up as the formers' index does. -/

/-- A push of a name fresh at `fe₀` keeps the view at `fe₀`'s bound
looking up as `fe₀`. -/
theorem restrictTo_push_find? {fe₀ fe : FEnv} {ci : ConstantInfo}
    (hle : fe₀.visibleBelow ≤ fe.visibleBelow)
    (hv : (fe.restrictTo fe₀.visibleBelow).find? = fe₀.find?)
    (hfresh : fe₀.find? ci.name = none) :
    ((fe.push ci).restrictTo fe₀.visibleBelow).find? = fe₀.find? := by
  funext n
  by_cases hn : ci.name = n
  · subst hn
    rw [hfresh]
    simp only [FEnv.find?, FEnv.push, FEnv.restrictTo, Std.HashMap.getElem?_insert_self]
    exact if_neg (Nat.not_lt.mpr hle)
  · rw [← congrFun hv n]
    simp only [FEnv.find?, FEnv.push, FEnv.restrictTo]
    rw [Std.HashMap.getElem?_insert, if_neg (by simpa using hn)]
    rfl

theorem restrictTo_consSumCtorsF_find? {fe₀ : FEnv} {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {fe : FEnv},
      fe₀.visibleBelow ≤ fe.visibleBelow →
      (fe.restrictTo fe₀.visibleBelow).find? = fe₀.find? →
      (∀ c ∈ ctorsA, fe₀.find? c.1.name = none) →
      fe₀.visibleBelow ≤ (consSumCtorsF nP ctorsA fe).visibleBelow ∧
        ((consSumCtorsF nP ctorsA fe).restrictTo fe₀.visibleBelow).find? = fe₀.find?
  | [], _, hle, hv, _ => ⟨hle, hv⟩
  | c :: cs, fe, hle, hv, hfr => by
    simp only [consSumCtorsF]
    refine restrictTo_consSumCtorsF_find? (by simp only [FEnv.push]; omega)
      (restrictTo_push_find? hle hv (hfr c List.mem_cons_self))
      (fun c' hc' => hfr c' (List.mem_cons_of_mem _ hc'))

theorem restrictTo_consBlockCtorsF_find? {fe₀ : FEnv} {nP : Nat} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {fe : FEnv},
      fe₀.visibleBelow ≤ fe.visibleBelow →
      (fe.restrictTo fe₀.visibleBelow).find? = fe₀.find? →
      (∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, fe₀.find? c.1.name = none) →
      ((consBlockCtorsF nP ctorsAs fe).restrictTo fe₀.visibleBelow).find? = fe₀.find?
  | [], _, _, hv, _ => hv
  | cs :: css, fe, hle, hv, hfr => by
    simp only [consBlockCtorsF]
    obtain ⟨hle', hv'⟩ := restrictTo_consSumCtorsF_find? (nP := nP) hle hv
      (hfr cs List.mem_cons_self)
    exact restrictTo_consBlockCtorsF_find? hle' hv'
      (fun cs' hc' => hfr cs' (List.mem_cons_of_mem _ hc'))

/-- **The formers' view of the constructors' index looks up as the
formers' environment.** -/
theorem restrictTo_consBlockCtors_mkFEnv {env₁ : Env} {nP : Nat}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hfr : ∀ ctorsA ∈ ctorsAs, ∀ c ∈ ctorsA, env₁.find? c.1.name = none) :
    ((consBlockCtorsF nP ctorsAs (mkFEnv env₁)).restrictTo (mkFEnv env₁).visibleBelow).find?
      = (mkFEnv env₁).find? :=
  restrictTo_consBlockCtorsF_find? (Nat.le_refl _) rfl
    (fun cs hc c hc' => by rw [mkFEnv_find?]; exact hfr cs hc c hc')

end ConLeche.Cached
