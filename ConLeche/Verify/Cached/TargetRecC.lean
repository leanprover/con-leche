module

public import ConLeche.Verify.Cached.BlockRunC
import ConLeche.Verify.Cached.NestPosC
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.RecCheckScope
public import ConLeche.Verify.Inductives.NestedRead
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.Cached.KnotCongr

public section

/-!
# The cached recursor stage, bridged: the TARGET check

The recursor stage's class kit (`ConLeche/Kernel/Inductives/RecCheck.lean`:
the class match, a class resolved and its pins, node agreement) at the
cached driver: each operation's simulation by the pure fueled one, the
scoping facts they need, and the cons at the majors
(`pushAll_blockRecInfosTF_mkFEnv`, `envWF_consBlockRecsT`).  The generated stage itself and the cached
uniform install are simulated in `GenRecC.lean`.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche
open Expr
open Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## 1. Scoping -/

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

section Sims

variable {env : Env}

/-! ### The operation-free outside instantiation -/

/-- `targetOutsideInst` is operation-free: at the cached driver it
leaves the state alone and computes the pure value. -/
theorem targetOutsideInstS_spec {fe : FEnv} {I : Name} {us : List Level} {ds : List Expr}
    {s₀ : CState} (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄ targetOutsideInst (m := CheckCM) fe I us ds
    ⦃fun v s' => CSOK mode false env s' ∧ Runs (targetOutsideInst (m := FueledM) fe I us ds) v; ⊤⦄
        := by
  sym only [conleche_grind, targetOutsideInst.eq_1] =>
    vcgen [targetOutsideInst] <;> finish

/-! ### The class match (`targetClassMatch`) and its three uses -/

theorem targetParamsDefEqS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat}
    {absM : Expr → Expr} (habs : ∀ e, WScoped d e → WScoped d (absM e)) {pfvs : List Expr}
    (hp : ∀ x ∈ pfvs, WScoped d x) :
    ∀ (as bs : List Expr) {s₀ : CState}, CSOK mode false env s₀ →
      ⦃fun s => s = s₀⦄
        targetParamsDefEq (sharedOpsC mode (mkFEnv env)) env d absM pfvs as bs
      ⦃fun v s' => CSOK mode false env s' ∧
        Runs (targetParamsDefEq (fueledOpsM mode) env d absM pfvs as bs) v; ⊤⦄ := by
  intro as
  induction as with
  | nil =>
    intro bs
    cases bs with
    | nil =>
      intro _ _
      sym only [conleche_grind, targetParamsDefEq.eq_1] =>
        vcgen [targetParamsDefEq] <;> finish
    | cons _ _ =>
      intro _ _
      -- the catch-all arm's equation is conditional (`vcgen` finds no spec)
      simp only [targetParamsDefEq]
      sym only [conleche_grind] => vcgen <;> finish
  | cons a as ih =>
    intro bs
    cases bs with
    | nil =>
      intro _ _
      -- the catch-all arm's equation is conditional (`vcgen` finds no spec)
      simp only [targetParamsDefEq]
      sym only [conleche_grind] => vcgen <;> finish
    | cons b bs =>
      intro _ _
      sym only [conleche_grind, targetParamsDefEq.eq_2,
          fun a (h : a.fvarB ≤ pfvs.length) =>
            habs _ (targetCanonParams_WScoped hp a (fvarB_le h))] =>
        vcgen [targetParamsDefEq, inferS_spec hμ henv, defeqS_spec hμ henv, ih bs] <;> finish

/-- The class match: the class's openers and parameters scoped by the
block's parameters, the formers closed. -/
theorem targetClassMatchS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {pfvs ds eds : List Expr} {us lvls : List Level}
    (hp : ∀ x ∈ pfvs, WScoped pfvs.length x) {s₀ : CState} (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄
      targetClassMatch (sharedOpsC mode (mkFEnv env)) env p formerTys pfvs us ds lvls eds
    ⦃fun v s' => CSOK mode false env s' ∧
      Runs (targetClassMatch (fueledOpsM mode) env p formerTys pfvs us ds lvls eds) v; ⊤⦄ := by
  sym only [conleche_grind, targetClassMatch.eq_1] =>
    vcgen [targetClassMatch, targetParamsDefEqS_spec hμ henv
      (targetAbs_WScoped (targetHoles_WScoped hformer pfvs.length))
      (fun x hx => (hp x hx).mono (by omega)) ds eds hs] <;> finish

theorem targetMajorNfsS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env)
    {p : BlockShape} {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t)
    {pfvs ds : List Expr} {us : List Level} {ctors : List (ConstantVal × Nat)}
    (hp : ∀ x ∈ pfvs, WScoped pfvs.length x) :
    ∀ (es : List NestCtorNf) {s₀ : CState}, CSOK mode false env s₀ →
      ⦃fun s => s = s₀⦄
        targetMajorNfs (sharedOpsC mode (mkFEnv env)) env p formerTys pfvs us ds ctors es
      ⦃fun v s' => CSOK mode false env s' ∧
        Runs (targetMajorNfs (fueledOpsM mode) env p formerTys pfvs us ds ctors es) v; ⊤⦄ := by
  intro es
  induction es with
  | nil =>
    intro _ _
    sym only [conleche_grind, targetMajorNfs.eq_1] => vcgen [targetMajorNfs] <;> finish
  | cons _ es ih =>
    intro _ hs
    sym only [conleche_grind, targetMajorNfs.eq_2] =>
      vcgen [targetMajorNfs, ih hs, targetClassMatchS_spec hμ henv hformer hp] <;> finish

theorem targetMajorOfS_spec {p : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {pfvs fvs : List Expr} {mty : Expr}
    {s₀ : CState} (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄ targetMajorOf (m := CheckCM) (mkFEnv env) p ctorsAs pfvs fvs mty
    ⦃fun v s' => CSOK mode false env s' ∧
      Runs (targetMajorOf (m := FueledM) (mkFEnv env) p ctorsAs pfvs fvs mty) v; ⊤⦄ := by
  sym only [conleche_grind, targetMajorOf.eq_1, unwrapOr] =>
    vcgen [targetMajorOf, unwrapOr, targetOutsideInstS_spec hs,
      liftFueledS_spec (mode := mode) (env := env)] <;> finish

/-- The pin typing at the cached driver. -/
theorem targetPinTysS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {d : Nat} :
    ∀ {xs : List Expr}, AllWS d xs → ∀ {s₀ : CState}, CSOK mode false env s₀ →
      ⦃fun s => s = s₀⦄ targetPinTys (sharedOpsC mode (mkFEnv env)) env d xs
      ⦃fun v s' => CSOK mode false env s' ∧ Runs (targetPinTys (fueledOpsM mode) env d xs) v; ⊤⦄ :=
          by
  intro xs
  induction xs with
  | nil =>
    intro _ _ _
    sym only [conleche_grind, targetPinTys.eq_1] => vcgen [targetPinTys] <;> finish
  | cons _ xs ih =>
    intro _ _ _
    sym only [conleche_grind, targetPinTys.eq_2] =>
      vcgen [targetPinTys, inferS_spec hμ henv, ih] <;>
        finish

/-- `targetMajorPins` at the cached driver: nothing at a member, the
pins and the instantiation typed at an outside major. -/
theorem targetMajorPinsS_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {rP : Nat}
    {M : TargetMajor} (hds : M.member = none → AllWS rP M.ds) {s₀ : CState}
    (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄ targetMajorPins (sharedOpsC mode (mkFEnv env)) env rP M
    ⦃fun v s' => CSOK mode false env s' ∧ Runs (targetMajorPins (fueledOpsM mode) env rP M) v; ⊤⦄
        := by
  sym only [conleche_grind, targetMajorPins.eq_1, Option.isNone_iff_eq_none] =>
    vcgen [targetMajorPins, targetPinTysS_spec hμ henv, inferS_spec hμ henv] <;> finish

theorem targetRecPinsS_spec {p : BlockShape} {block : List ConstantInfo} {s₀ : CState}
    (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄ targetRecPins (m := CheckCM) p block
    ⦃fun v s' => CSOK mode false env s' ∧ Runs (targetRecPins (m := FueledM) p block) v; ⊤⦄ := by
  sym only [conleche_grind, targetRecPins.eq_1] => vcgen [targetRecPins] <;> finish

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

theorem targetK53S_spec (hμ : mode.verifiedChecks = true) (henv : EnvWF env) {p : BlockShape}
    {formerTys : List Expr} (hformer : ∀ t ∈ formerTys, WScoped 0 t) {Mc : TargetMajor}
    (hMc : TargetMajScoped Mc) {tele : List Expr} {majDom f : Expr}
    {s₀ : CState} (hs : CSOK mode false env s₀) :
    ⦃fun s => s = s₀⦄ targetK53 (sharedOpsC mode (mkFEnv env)) env p formerTys Mc tele majDom f
    ⦃fun v s' => CSOK mode false env s' ∧
      Runs (targetK53 (fueledOpsM mode) env p formerTys Mc tele majDom f) v; ⊤⦄ := by
  sym only [conleche_grind, targetK53.eq_1] =>
    vcgen [targetK53, targetClassMatchS_spec hμ henv hformer hMc.1 hs] <;> finish

end Sims

/-! ### The rule stage: two environments, one state (`SimG`, `BlockRunC.lean`) -/

/-! ## 3. The assembly -/

/-- The recursors' conses at their majors leave the tables alone. -/
theorem consBlockRecsT_tables (find? : Name → Option ConstantInfo) (q : BlockShape) :
    ∀ (m : Nat) (out : List (ConstantVal × TargetMajor × List Expr)) (env : Env),
      (consBlockRecsT find? q m out env).tables = env.tables
  | _, [], _ => rfl
  | m, _ :: rest, _ => consBlockRecsT_tables find? q (m + 1) rest _

/-! ### The cons at the majors

The install conses the checked family with each recursor's rules
at ITS major (`consBlockRecsT`): at an outside major every rule fires
`.nested` at the class's levels and parameters (`auxRuleFire`), and
`EnvWF`'s `.nested` clause is what that datum reads off the generated
type (`NestedRead`, `genStage_nestedRead`). -/

/-- The cached install's pushes of the family's records
(`blockRecInfosTF`) onto a canonical index are the canonical index of
the pure cons. -/
theorem pushAll_blockRecInfosTF_mkFEnv (find? : Name → Option ConstantInfo)
    (p : BlockShape) :
    ∀ (m : Nat) (out : List (ConstantVal × TargetMajor × List Expr)) (env : Env),
      FEnv.pushAll (blockRecInfosTF find? p m out) (mkFEnv env)
        = mkFEnv (consBlockRecsT find? p m out env)
  | _, [], _ => rfl
  | m, (cv, M, rhss) :: rest, env => by
    simp only [blockRecInfosTF, FEnv.pushAll, consBlockRecsT, push_mkFEnv]
    exact pushAll_blockRecInfosTF_mkFEnv find? p (m + 1) rest _

theorem find?_consBlockRecsT_le {find? : Name → Option ConstantInfo}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {env : Env} (n : Name),
      (env.find? n).isSome = true →
      ((consBlockRecsT find? q m out env).find? n).isSome = true
  | _, [], _, _, h => h
  | _, _ :: _, env, n, h => by
    simp only [consBlockRecsT]
    refine find?_consBlockRecsT_le n ?_
    rw [Env.find?_cons]
    split <;> simp_all

theorem find?_consBlockRecsT_of_bare {find? : Name → Option ConstantInfo}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {envA envB : Env},
      (∀ n, (envA.find? n).isSome = true → (envB.find? n).isSome = true) →
      ∀ n, ((consBlockRecsBare q m (out.map fun t => (t.1, t.2.1.nIdx)) envA).find? n).isSome
          = true →
        ((consBlockRecsT find? q m out envB).find? n).isSome = true
  | _, [], _, _, hf, n, h => hf n h
  | m, (cv, M, rhss) :: rest, envA, envB, hf, n, h => by
    simp only [List.map_cons, consBlockRecsBare] at h
    simp only [consBlockRecsT]
    refine find?_consBlockRecsT_of_bare
      (envA := ⟨.recInfo cv (q.majorIdxAt m) (q.rulePrefixAt m) [] :: envA.consts, envA.tables⟩) ?_ n h
    exact find?_cons_mono rfl hf

theorem mem_consBlockRecsT {find? : Name → Option ConstantInfo}
    {q : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {env : Env}
      {c : ConstantInfo},
      c ∈ (consBlockRecsT find? q m out env).consts →
      c ∈ env.consts ∨ ∃ i t, out[i]? = some t ∧
        c = .recInfo t.1 (q.majorIdxAt (m + i)) (q.rulePrefixAt (m + i))
          (tgtStoredRules find? t.1 (q.rulePrefixAt (m + i)) t.2.1 t.2.2)
  | _, [], _, _, h => Or.inl h
  | m, t0 :: rest, env, c, h => by
    simp only [consBlockRecsT] at h
    rcases mem_consBlockRecsT h with h' | ⟨i, t, ht, hj⟩
    · rcases List.mem_cons.mp h' with rfl | h'
      · exact Or.inr ⟨0, t0, rfl, rfl⟩
      · exact Or.inl h'
    · refine Or.inr ⟨i + 1, t, by simpa using ht, ?_⟩
      rw [show m + (i + 1) = m + 1 + i by omega]
      exact hj

/-- **The family consed at its majors keeps well-formedness**
(`envWF_consBlockRecs` at the majors): the rules' right-hand
sides as there, and an outside major's `.nested` fire is `auxRuleFire`'s
datum, which reads off the stored type (`hread`, `genStage_nestedRead`). -/
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
        rhs.looseBVarsBounded 0 = true)
    (hread : ∀ i t, out[i]? = some t → t.2.1.member = none →
      NestedRead (·.constsResolve env) t.1.levelParams t.1.type (q.majorIdxAt i)
        (q.rulePrefixAt i) t.2.1.nPc t.2.1.lvls
        (t.2.1.ds.map (Expr.abstractPrefix (q.rulePrefixAt i) 0))) :
    EnvWF (consBlockRecsT find? q 0 out env) := by
  have hdomEnv : ∀ n, (env.find? n).isSome = true →
      ((consBlockRecsT find? q 0 out env).find? n).isSome = true :=
    fun n hn => find?_consBlockRecsT_le n hn
  have hdomBare : ∀ n,
      ((consBlockRecsBare q 0 (out.map fun t => (t.1, t.2.1.nIdx)) env).find? n).isSome
        = true →
      ((consBlockRecsT find? q 0 out env).find? n).isSome = true :=
    find?_consBlockRecsT_of_bare (fun _ hn => hn)
  refine ⟨fun c hc => ?_, fun t ht => TableWF.mono hdomEnv
    (henv.tables t (by rw [consBlockRecsT_tables] at ht; exact ht))⟩
  rcases mem_consBlockRecsT hc with hc' | ⟨i, t, hti, rfl⟩
  · exact ConstWF.mono hdomEnv (henv.consts c hc')
  · rw [Nat.zero_add]
    obtain ⟨h1, h2, h3, h4, h5⟩ := hall t (List.mem_of_getElem? hti)
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
      simp only [auxRuleFire, RecRuleFire.nested.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      obtain ⟨k1, k2, k3, pre, dom, body, D, e1, e2, e3, -⟩ := hread i t hti hM
      refine ⟨k1, k2, fun pin hpin => ?_, pre, dom, body, D, e1, e2, e3, rfl⟩
      obtain ⟨p1, p2, p3, p4⟩ := k3 pin hpin
      exact ⟨p1, p2, Expr.constsResolve_of_find hdomEnv p3, p4⟩

end ConLeche.Cached
