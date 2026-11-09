module

public import ConLeche.Verify.Cached.BridgeCSDecl
import ConLeche.Verify.Cached.NestPosC
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockRecRun
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Inductives.DirectInv

public section

/-!
# The cached uniform install at k members, bridged

`checkBlockKS` (`ConLeche/Cached/CheckerC.lean`), the cached mirror of
the uniform installer at any number of members, is reproduced by the
pure fueled `checkBlock`.  This file holds the stages' simulations and
the rule stage's `SimG`; the pass (`checkBlockPassS_run`, which checks the
classes), the recursor stage, its install and the `.indDecl` dispatch
(`checkBlockTailS_run`, `checkBlockKS_run`, `checkModeledOrNativeSF_run`)
are in `ConLeche/Verify/Cached/GenRecC.lean`.

The file follows `BridgeCSDecl.lean`'s layout:

1. the index mirrors at `mkFEnv` ARE the pure stages (`*_eqC`);
2. the scoping facts every cached operation's triple needs (they are
   stated at well-scoped inputs);
3. the single-environment stages as `Std.WP` triples, proved by `vcgen`
   and `grind`;
4. the rule stage, whose one rule alternates between the rule-less
   recursors' environment and the constructors' (`SimG`, a run-level
   simulation whose invariant may change at `sharedOpsRuleR`'s
   flushes);
5. the assembly, and the dispatch.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open Expr
open Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## 1. The index mirrors at `mkFEnv` are the pure stages -/

section Mirrors

variable (ops : CheckerOps CheckCM)

theorem checkBlockTeleF_eqC (env : Env) (nP : Nat) (ms : MemberShape) :
    checkBlockTeleF ops (mkFEnv env) nP ms = checkBlockTele ops env nP ms := by
  unfold checkBlockTeleF checkBlockTele
  simp only [checkConstantValF_eq]

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
    ∀ (formers : List ConstantVal) (i : Nat) (env : Env),
      consBlockIndsF p₁ isRec formers i (mkFEnv env) = mkFEnv (consBlockInds p₁ isRec formers i env)
  | [], _, _ => rfl
  | cvTa :: rest, i, env => by
    simp only [consBlockIndsF, consBlockInds, push_mkFEnv]
    exact consBlockIndsF_mkFEnv p₁ isRec rest (i + 1) _

theorem checkBlockIndsF_eqC (env : Env) (p : BlockShape) (isRec : Bool) :
    checkBlockIndsF ops (mkFEnv env) p isRec
      = checkBlockInds ops env p isRec >>= fun r => pure (mkFEnv r.1, r.2) := by
  unfold checkBlockIndsF checkBlockInds
  rcases hm : p.members with _ | ⟨ms0, rest⟩
  · rfl
  · simp only [checkBlockTeleF_eqC, checkBlockTelesF_eqC, checkBlockAgreeF_eqC, bind_assoc,
      pure_bind, consBlockIndsF_mkFEnv]

theorem checkBlockCtorsF_eqC (env₀ env : Env) (p : BlockShape) :
    ∀ l : List MemberShape,
      checkBlockCtorsF ops (mkFEnv env₀) (mkFEnv env) p l = checkBlockCtors ops env₀ env p l
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockCtorsF, checkBlockCtors, checkSumCtorsF_eq,
      checkBlockCtorsF_eqC env₀ env p rest]

theorem checkBlockIdxSortsF_eqC (env : Env) (p : BlockShape) :
    ∀ l : List MemberShape,
      checkBlockIdxSortsF ops (mkFEnv env) p l = checkBlockIdxSorts ops env p l
  | [] => rfl
  | ms :: rest => by
    simp only [checkBlockIdxSortsF, checkBlockIdxSorts, checkStructFieldSortsIF_eq,
      checkBlockIdxSortsF_eqC env p rest]

end Mirrors

theorem consBlockCtorsF_mkFEnv (nP : Nat) :
    ∀ (memberCtors : List (List (ConstantVal × Nat))) (env : Env),
      consBlockCtorsF nP memberCtors (mkFEnv env) = mkFEnv (consBlockCtors nP memberCtors env)
  | [], _ => rfl
  | ctorList :: rest, env => by
    simp only [consBlockCtorsF, consBlockCtors, consSumCtorsF_mkFEnv]
    exact consBlockCtorsF_mkFEnv nP rest _

/-! ## 2. Scoping

Every cached operation's simulation is stated at a well-scoped input
(`WScoped`).  Most of the stages' inputs are OPENED telescopes of
checked (fvar-free) constants, and the opening lemmas
(`BridgeCS3.lean`'s vocabulary) cover them.  "fvar-free" is stated as
`WScoped 0` (`ws_of_ws0`), which composes with the opening lemmas; a
list of checked constants as the named predicate `CvsWS`. -/

theorem ws0_hasFvar {e : Expr} (h : WScoped 0 e) : e.hasFvar = false :=
  not_hasFvar_of_fvarsBelow_zero (WScoped.fvarsBelow h)

theorem ws_of_ws0 {d : Nat} {e : Expr} (h : WScoped 0 e) : WScoped d e :=
  WScoped.of_not_hasFvar (ws0_hasFvar h)

/-- Every constant of the list has an fvar-free type. -/
@[expose] def CvsWS (l : List ConstantVal) : Prop := ∀ cv ∈ l, WScoped 0 cv.type

@[conleche_grind =] theorem CvsWS.nil_eq : CvsWS [] = True := by
  simp [CvsWS]

@[conleche_grind =] theorem CvsWS.cons_eq (cv : ConstantVal) (l : List ConstantVal) :
    CvsWS (cv :: l) = (WScoped 0 cv.type ∧ CvsWS l) := by
  simp [CvsWS]

/-- The level comparison's fuel at the cached driver (operation-free). -/
theorem liftFueledS_spec {env : Env} {α : Type} {what : String} {o : Option α} {s₀ : CState}
    (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄ (liftFueled what o : CheckCM α)
    ⦃fun v s' => CSOK mode false env s' ∧ Runs (liftFueled what o : FueledM α) v; ⊤⦄ := by
  sym only [conleche_grind, liftFueled.eq_1, liftFueled.eq_2] =>
    vcgen [liftFueled] <;> finish

/-! ## 3. The single-environment stages, simulated -/

section Sims

variable {env : Env}

theorem checkBlockTeleS_spec (henv : EnvWF env) {nP : Nat}
    {ms : MemberShape} {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ checkBlockTele (sharedOpsC .verified (mkFEnv env)) env nP ms
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs (checkBlockTele (fueledOpsM .verified) env nP ms) v ∧
      WScoped 0 v.1.type; ⊤⦄ := by
  sym only [conleche_grind, checkBlockTele.eq_1, unwrapOr] =>
    vcgen [checkBlockTele, unwrapOr, checkConstantValS_spec henv hs,
      checkSumTeleS_spec (env := env)] <;> finish

theorem checkBlockTelesS_spec (henv : EnvWF env) {nP : Nat} :
    ∀ {mss : List MemberShape} {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄ checkBlockTeles (sharedOpsC .verified (mkFEnv env)) env nP mss
      ⦃fun v s' => CSOK .verified false env s' ∧ Runs (checkBlockTeles (fueledOpsM .verified) env nP mss) v ∧
        CvsWS (v.map Prod.fst); ⊤⦄ := by
  intro mss
  induction mss with
  | nil =>
    intro _ _
    sym only [conleche_grind, checkBlockTeles.eq_1, List.map_nil] =>
      vcgen [checkBlockTeles] <;> finish
  | cons _ rest ih =>
    intro _ _
    sym only [conleche_grind, checkBlockTeles.eq_2, List.map_cons] =>
      vcgen [checkBlockTeles, checkBlockTeleS_spec henv, ih] <;> finish

theorem checkBlockDomsAtS_spec (henv : EnvWF env) {off : Nat}
    {fvs doms : List Expr}
    (hc : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → WScoped (off + i) (Expr.fvarTypeD x))
    (ht : ∀ (i : Nat) (x : Expr), doms[i]? = some x → WScoped (off + i) x) :
    ∀ {j : Nat} {s₀ : CState}, CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄ checkBlockDomsAt (sharedOpsC .verified (mkFEnv env)) env off fvs doms j
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (checkBlockDomsAt (fueledOpsM .verified) env off fvs doms j) v; ⊤⦄ := by
  intro j
  induction j with
  | zero =>
    intro _ _
    sym only [conleche_grind, checkBlockDomsAt.eq_1] => vcgen [checkBlockDomsAt] <;> finish
  | succ j ih =>
    intro _ _
    sym only [conleche_grind, checkBlockDomsAt.eq_2, unwrapOr] =>
      vcgen [checkBlockDomsAt, unwrapOr, defeqS_spec henv, ih] <;> finish

theorem checkBlockAgreeS_spec (henv : EnvWF env) {nP : Nat}
    {cvTa0 : ConstantVal} {s0 : Level} (h0 : WScoped 0 cvTa0.type) :
    ∀ {cvs : List (ConstantVal × Level)} {s₀ : CState},
      CvsWS (cvs.map Prod.fst) → CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄ checkBlockAgree (sharedOpsC .verified (mkFEnv env)) env nP cvTa0 s0 cvs
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (checkBlockAgree (fueledOpsM .verified) env nP cvTa0 s0 cvs) v; ⊤⦄ := by
  intro cvs
  induction cvs with
  | nil =>
    intro _ _ _
    sym only [conleche_grind, checkBlockAgree.eq_1] => vcgen [checkBlockAgree] <;> finish
  | cons x rest ih =>
    obtain ⟨cvTa, s⟩ := x
    intro _ _ _
    sym only [conleche_grind, checkBlockAgree.eq_2, unwrapOr, List.map_cons] =>
      vcgen [checkBlockAgree, unwrapOr, checkBlockDomsAtS_spec henv,
        liftFueledS_spec (mode := .verified) (env := env), ih] <;> finish

theorem checkBlockIndsS_spec (henv : EnvWF env)
    {p : BlockShape} {isRec : Bool} {s₀ : CState} (hs : CSOK .verified false env s₀) :
    ⦃fun s => s = s₀⦄ checkBlockInds (sharedOpsC .verified (mkFEnv env)) env p isRec
    ⦃fun v s' => CSOK .verified false env s' ∧ Runs (checkBlockInds (fueledOpsM .verified) env p isRec) v; ⊤⦄ := by
  sym only [conleche_grind, checkBlockInds.eq_1] =>
    vcgen [checkBlockInds, checkBlockTeleS_spec henv hs, checkBlockTelesS_spec henv,
      checkBlockAgreeS_spec henv] <;> finish

theorem checkBlockCtorsS_spec (henv : EnvWF env)
    {env₀ : Env} {p : BlockShape} :
    ∀ {l : List MemberShape} {s₀ : CState},
      (∀ x ∈ l, x.cvT.type.hasFvar = false) → CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄ checkBlockCtors (sharedOpsC .verified (mkFEnv env)) env₀ env p l
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (checkBlockCtors (fueledOpsM .verified) env₀ env p l) v; ⊤⦄ := by
  intro l
  induction l with
  | nil =>
    intro _ _ _
    sym only [conleche_grind, checkBlockCtors.eq_1] => vcgen [checkBlockCtors] <;> finish
  | cons ms rest ih =>
    intro _ hl _
    sym only [conleche_grind, checkBlockCtors.eq_2] =>
      vcgen [checkBlockCtors, checkSumCtorsS_spec henv
          (show ms.cvT.type.hasFvar = false from hl ms List.mem_cons_self),
        ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))] <;> finish

/-- An opened telescope's variables past a prefix carry types scoped at
their own frame. -/
theorem openers_drop_fvarTypeD_WScoped {n k : Nat} {e : Expr} {fvs : List Expr} {body : Expr}
    (h : openPisAtFvars n e 0 = some (fvs, body)) (he : WScoped 0 e) {i : Nat} {x : Expr}
    (hx : (fvs.drop k)[i]? = some x) : WScoped (k + i) x.fvarTypeD := by
  rw [List.getElem?_drop] at hx
  simpa using openers_fvarTypeD_WScoped h he hx
grind_pattern [conleche_grind] openers_drop_fvarTypeD_WScoped =>
  openPisAtFvars n e 0, some (fvs, body), (fvs.drop k)[i]?, x.fvarTypeD where
  guard openPisAtFvars n e 0 = some (fvs, body)
  guard (fvs.drop k)[i]? = some x

theorem checkBlockIdxSortsS_spec (henv : EnvWF env)
    {p : BlockShape} :
    ∀ {l : List MemberShape} {s₀ : CState},
      (∀ x ∈ l, WScoped 0 x.cvT.type) → CSOK .verified false env s₀ →
      ⦃fun s => s = s₀⦄ checkBlockIdxSorts (sharedOpsC .verified (mkFEnv env)) env p l
      ⦃fun v s' => CSOK .verified false env s' ∧
        Runs (checkBlockIdxSorts (fueledOpsM .verified) env p l) v; ⊤⦄ := by
  intro l
  induction l with
  | nil =>
    intro _ _ _
    sym only [conleche_grind, checkBlockIdxSorts.eq_1] => vcgen [checkBlockIdxSorts] <;> finish
  | cons ms rest ih =>
    intro _ hl _
    sym only [conleche_grind, checkBlockIdxSorts.eq_2, unwrapOr, FvsWS,
        show WScoped 0 ms.cvT.type from hl ms List.mem_cons_self] =>
      vcgen [checkBlockIdxSorts, unwrapOr, checkStructFieldSortsIS_spec henv,
        ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))] <;> finish

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

/-- The rule stage's `inferType` at the rule-less recursors'
environment: it flushes first and last, so it hands on a state that is
an invariant state of ANY environment. -/
theorem ruleR_infer_simG {envR : Env} (henvR : EnvWF envR)
    (envT : Env) {d : Nat} {e : Expr} (hw : WScoped d e) :
    SimG (CSOK .verified false envR) (CSOK .verified false envT) (RelEC d)
      ((sharedOpsRuleR .verified (mkFEnv envR)).inferType envR d e)
      ((fueledOpsM .verified).inferType envR d e) := by
  intro s₀ hs v' s' hr
  simp only [sharedOpsRuleR] at hr
  obtain ⟨u₀, s₀', hfl₀, hr⟩ := bindC_ok hr
  rw [flushC_run] at hfl₀
  injection hfl₀ with hfl₀
  obtain rfl : s₀.flushed = s₀' := congrArg Prod.snd hfl₀
  have hs₀' : CSOK .verified false envR s₀.flushed := flushC_csok hs.residue
  obtain ⟨t, s₁, hinf, hr⟩ := bindC_ok hr
  obtain ⟨hs₁, ⟨F, hF⟩, hwt⟩ := triple_iff_run.mp (opE_infer_spec henvR hs₀' hw) t s₁ hinf
  obtain ⟨u, s₂, hfl, hr⟩ := bindC_ok hr
  rw [flushC_run] at hfl
  injection hfl with hfl
  obtain rfl : s₁.flushed = s₂ := congrArg Prod.snd hfl
  obtain ⟨rfl, rfl⟩ := pureC_ok hr
  exact ⟨flushC_csok hs₁.residue, t, relEC_diag t hwt, F, hF⟩

/-! ## 5. The assembly -/

/-- The rule-less recursors' cons is a `consBlockRecs` with no rules. -/
theorem consBlockRecsBare_eq_consBlockRecs (q : BlockShape) :
    ∀ (m : Nat) (cvRas : List (ConstantVal × Nat)) (env : Env),
      consBlockRecsBare q m cvRas env
        = consBlockRecs q m
            (cvRas.map fun c => (c.1, ([] : List Expr), c.2, ([] : List (ConstantVal × Nat))))
            env
  | _, [], _ => rfl
  | m, (cv, n) :: rest, env => by
    simp only [consBlockRecsBare, consBlockRecs, List.map_cons, sumRules]
    exact consBlockRecsBare_eq_consBlockRecs q (m + 1) rest _

/-- **The rule-less recursors' environment is well-formed** when their
checked types are. -/
theorem envWF_consBlockRecsBare {q : BlockShape} {cvRas : List (ConstantVal × Nat)} {env : Env}
    (henv : EnvWF env)
    (hall : ∀ c ∈ cvRas, c.1.type.hasFvar = false ∧
      c.1.type.allLevelParamsDefined c.1.levelParams = true ∧
      c.1.type.constsResolve env = true ∧ c.1.type.looseBVarsBounded 0 = true)
    (hlit : ∀ c ∈ cvRas, LitShapeAt c.1) :
    EnvWF (consBlockRecsBare q 0 cvRas env) := by
  rw [consBlockRecsBare_eq_consBlockRecs q]
  refine envWF_consBlockRecs henv ?_ ?_
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    obtain ⟨h1, h2, h3, h4⟩ := hall c hc
    exact ⟨h1, h2, h3, h4, fun _ h => nomatch h⟩
  · intro r hr
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
    exact hlit c hc

/-- The projection tables' checks at the cached driver: operation-free, the state unchanged, the
verdict the pure stage's. -/
theorem checkBlockTablesS_run (env : Env) :
    ∀ (Q : List ProjTable) {s₀ : CState} {u : Unit} {s' : CState},
      checkBlockTablesF (m := CheckCM) .plain (mkFEnv env) Q s₀ = .ok (u, s') →
      s' = s₀ ∧ checkBlockTables (m := CheckM) env Q = .ok ()
  | [], s₀, u, s', h => by
    simp only [checkBlockTablesF] at h
    obtain ⟨-, rfl⟩ := pureC_ok h
    exact ⟨rfl, rfl⟩
  | t :: rest, s₀, u, s', h => by
    unfold checkBlockTablesF at h
    unfold checkBlockTables
    obtain ⟨u₁, s₁, h₁, h⟩ := bindC_ok h
    obtain ⟨rfl, hrest⟩ := checkBlockTablesS_run env rest h
    obtain ⟨rfl, hT⟩ := checkStructProjTableS_run env h₁
    refine ⟨rfl, ?_⟩
    simp only [hT, bind, Except.bind, hrest]

/-- The constructors' stage stores fvar-free constructor types. -/
theorem checkBlockCtors_types {env₀ env : Env} {q : BlockShape} {F : Nat}
    {l : List MemberShape}
    (h : checkBlockCtors (fueledOps mode F) env₀ env q l = .ok ()) :
    ∀ ctorList ∈ l.map (·.ctors), ∀ c ∈ ctorList, WScoped 0 c.1.type := by
  obtain ⟨_, -, hall⟩ := checkBlockCtors_inv h
  intro ctorList hctor c hc
  obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hctor
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hms
  obtain ⟨sortss, -, hcs⟩ := hall i ms hi
  obtain ⟨hlenC, -, hallc⟩ := hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  obtain ⟨-, sorts, -, hrun⟩ := hallc j c c hj hj
  exact WScoped.of_not_hasFvar (direct_sum_ctor_typeWF hrun).1

end ConLeche.Cached
