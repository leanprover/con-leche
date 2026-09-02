import Setlec.Verify.Cached.SimCS
import Setlec.Verify.BridgeWfImp

/-!
# Cached shared-state walks, part 1: the single-environment checker
functions

Port of `Setlec/Verify/BridgeS1.lean` for the cached tier.  Each lemma
relates a generic declaration-checker function instantiated at the
cached shared operations (`sharedOpsC mode (mkFEnv env)`, state shared
across all operation calls) to the same function at the fueled families
(`(fueledOpsM mode)`), as a `SimC` — the invariant `CSOK mode env` is
threaded through every call, so cache entries created by one call are
consumed by later ones soundly.  The per-site well-scopedness facts
mirror the `_wfimp` walks (`Setlec/Verify/BridgeWfImp.lean`).

The *subjects* are the very same `Expr`-level checker functions as in
the interned original — only the operations record differs, so the
walks transpose by the recipe's substitutions alone (`SimAt → SimC`,
`ISOK → CSOK`, no `Ext` binder, state-free value relations).  The pure
comparand side of every statement is byte-identical to the interned
original's.
-/

namespace Setlec.Cached

open Setlec
open Setlec.Cached.ExprC

variable {mode : CheckMode}

section Walks1

variable {env : Env} {s₀ : CState}

/-- `checkConstantVal` at the cached shared operations simulates the
fueled instantiation; the returned constant's type is well-scoped. -/
theorem checkConstantValS_sim (henv : EnvWF env) {cv : ConstantVal}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ Expr.WScoped 0 v.type)
      (checkConstantVal (sharedOpsC mode (mkFEnv env)) env cv)
      (checkConstantVal (fueledOpsM mode) env cv) := by
  unfold checkConstantVal
  dsimp only [sharedOpsC]
  by_cases h1 : (env.find? cv.name).isSome = true
  · simp only [if_pos h1]
    exact SimC.throw_bind
  simp only [if_neg h1]
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · simp only [if_pos h2]
    exact SimC.throw_bind
  simp only [if_neg h2]
  by_cases h3 : cv.name.isProjFnShape = true
  · simp only [if_pos h3]
    exact SimC.throw_bind
  simp only [if_neg h3]
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg =>
    simp only [if_neg h4]
    exact SimC.throw_bind
  simp only [if_pos h4]
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg =>
    simp only [if_neg h5]
    exact SimC.throw_bind
  simp only [if_pos h5]
  by_cases h6 : cv.type.hasFvar = true
  · simp only [if_pos h6]
    exact SimC.throw_bind
  simp only [if_neg h6]
  refine SimC.bind (opE_annotate_sim henv hs
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6)))
    (fun s₁ ty ty' hs₁ hP => ?_)
  obtain ⟨rfl, hwty⟩ := hP
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams ty = true
  case neg =>
    simp only [if_neg h7]
    exact SimC.throw_bind
  simp only [if_pos h7]
  by_cases h8 : Expr.constsResolve env ty = true
  case neg =>
    simp only [if_neg h8]
    exact SimC.throw_bind
  simp only [if_pos h8]
  refine SimC.bind (opE_infer_sim henv hs₁ hwty)
    (fun s₂ sty sty' hs₂ hP₂ => ?_)
  obtain ⟨rfl, hwsty⟩ := hP₂
  refine SimC.bind (opS_sim henv hs₂ hwsty)
    (fun s₃ u u' hs₃ hP₃ => ?_)
  exact SimC.pure hs₃ ⟨rfl, hwty⟩

/-- `checkDefnVal` at the cached shared operations; the returned
environment stores the annotated (fvar-free) value under `cv.name`. -/
theorem checkDefnValS_sim (henv : EnvWF env) {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint} (htf : Expr.WScoped 0 cv.type)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ ∀ cv' v' h',
        v.find? cv.name = some (.defnInfo cv' v' h') → v'.hasFvar = false)
      (checkDefnVal (sharedOpsC mode (mkFEnv env)) env cv value hint)
      (checkDefnVal (fueledOpsM mode) env cv value hint) := by
  unfold checkDefnVal
  dsimp only [sharedOpsC]
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  by_cases h2 : value.hasFvar = true
  · simp only [if_pos h2]; exact SimC.throw_bind
  simp only [if_neg h2]
  refine SimC.bind (opE_annotate_sim henv hs
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₁ val val' hs₁ hP => ?_)
  obtain ⟨rfl, hwval⟩ := hP
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams val = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  by_cases h4 : Expr.constsResolve env val = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  refine SimC.bind (opE_infer_sim henv hs₁ hwval)
    (fun s₂ vt vt' hs₂ hP₂ => ?_)
  obtain ⟨rfl, hwvt⟩ := hP₂
  refine SimC.bind (opB_sim henv hs₂ hwvt htf)
    (fun s₃ b b' hs₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
    simp only [↓reduceIte]
    refine SimC.pure hs₃ ⟨rfl, ?_⟩
    intro cv' v' h' hf
    rw [Env.find?_cons, if_pos (show (ConstantInfo.defnInfo cv val
      hint).name = cv.name from rfl)] at hf
    simp only [Option.some.injEq, ConstantInfo.defnInfo.injEq] at hf
    obtain ⟨-, rfl, -⟩ := hf
    exact Expr.not_hasFvar_of_fvarsBelow_zero hwval.fvarsBelow

/-- `checkThmVal` at the cached shared operations. -/
theorem checkThmValS_sim (henv : EnvWF env) {cv : ConstantVal}
    {value : Expr} (htf : Expr.WScoped 0 cv.type) (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkThmVal (sharedOpsC mode (mkFEnv env)) env cv value)
      (checkThmVal (fueledOpsM mode) env cv value) := by
  unfold checkThmVal
  dsimp only [sharedOpsC]
  refine SimC.bind (opE_infer_sim henv hs htf)
    (fun s₁ sty sty' hs₁ hP => ?_)
  obtain ⟨rfl, hwsty⟩ := hP
  refine SimC.bind (opS_sim henv hs₁ hwsty)
    (fun s₂ u u' hs₂ hP₂ => ?_)
  obtain rfl : u = u' := hP₂
  refine SimC.bind (SimC.liftFueled _ _ hs₂)
    (fun s₃ b b' hs₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
  simp only [↓reduceIte]
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  by_cases h2 : value.hasFvar = true
  · simp only [if_pos h2]; exact SimC.throw_bind
  simp only [if_neg h2]
  refine SimC.bind (opE_annotate_sim henv hs₃
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₄ val val' hs₄ hP₄ => ?_)
  obtain ⟨rfl, hwval⟩ := hP₄
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams val = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  by_cases h4 : Expr.constsResolve env val = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  refine SimC.bind (opE_infer_sim henv hs₄ hwval)
    (fun s₅ vt vt' hs₅ hP₅ => ?_)
  obtain ⟨rfl, hwvt⟩ := hP₅
  refine SimC.bind (opB_sim henv hs₅ hwvt htf)
    (fun s₆ b b' hs₆ hP₆ => ?_)
  obtain rfl : b = b' := hP₆
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₆ rfl

/-- `checkOpaqueVal` at the cached shared operations (the postcondition
carries the raw value's `hasFvar` fact for the compiler-trust install
gate's re-annotation). -/
theorem checkOpaqueValS_sim (henv : EnvWF env) {cv : ConstantVal}
    {value : Expr} (htf : Expr.WScoped 0 cv.type) (hs : CSOK mode env s₀) :
    SimC mode env s₀ (fun v w => v = w ∧ value.hasFvar = false)
      (checkOpaqueVal (sharedOpsC mode (mkFEnv env)) env cv value)
      (checkOpaqueVal (fueledOpsM mode) env cv value) := by
  unfold checkOpaqueVal
  dsimp only [sharedOpsC]
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => simp only [if_neg h1]; exact SimC.throw_bind
  simp only [if_pos h1]
  by_cases h2 : value.hasFvar = true
  · simp only [if_pos h2]; exact SimC.throw_bind
  simp only [if_neg h2]
  refine SimC.bind (opE_annotate_sim henv hs
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)))
    (fun s₁ val val' hs₁ hP => ?_)
  obtain ⟨rfl, hwval⟩ := hP
  by_cases h3 : Expr.allLevelParamsDefined cv.levelParams val = true
  case neg => simp only [if_neg h3]; exact SimC.throw_bind
  simp only [if_pos h3]
  by_cases h4 : Expr.constsResolve env val = true
  case neg => simp only [if_neg h4]; exact SimC.throw_bind
  simp only [if_pos h4]
  refine SimC.bind (opE_infer_sim henv hs₁ hwval)
    (fun s₂ vt vt' hs₂ hP₂ => ?_)
  obtain ⟨rfl, hwvt⟩ := hP₂
  refine SimC.bind (opB_sim henv hs₂ hwvt htf)
    (fun s₃ b b' hs₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw_bind
  | true =>
    simp only [↓reduceIte]
    exact SimC.pure hs₃ ⟨rfl, Bool.not_eq_true _ ▸ h2⟩

/-- `checkReducePin` at the cached shared operations. -/
theorem checkReducePinS_sim (henv : EnvWF env) {env2 : Env} {c : Name}
    {value : Expr} (hvf : value.hasFvar = false)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkReducePin (sharedOpsC mode (mkFEnv env)) env env2 c value)
      (checkReducePin (fueledOpsM mode) env env2 c value) := by
  unfold checkReducePin
  dsimp only [sharedOpsC]
  by_cases h1 : (reduceStoredOk env2 c && reduceElemOk env c) = true
  case neg => simp only [if_neg h1]; exact SimC.throw
  simp only [if_pos h1]
  by_cases h2 : reducePinGuard env c = true
  case neg => simp only [if_neg h2]; exact SimC.throw
  simp only [if_pos h2]
  refine SimC.bind (opE_annotate_sim henv hs
      (Expr.WScoped.of_not_hasFvar hvf))
    (fun s₁ valA valA' hs₁ hP => ?_)
  obtain ⟨rfl, hwval⟩ := hP
  have h2' := h2
  unfold reducePinGuard at h2'
  simp only [Bool.and_eq_true] at h2'
  have hpinF : (reduceDeclPin c).hasFvar = false := by
    simpa using h2'.1.1.2
  refine SimC.bind (opE_annotate_sim henv hs₁
      (Expr.WScoped.of_not_hasFvar hpinF))
    (fun s₂ pinA pinA' hs₂ hP₂ => ?_)
  obtain ⟨rfl, hwpin⟩ := hP₂
  refine SimC.bind (opB_sim henv hs₂ hwval hwpin)
    (fun s₃ b b' hs₃ hP₃ => ?_)
  obtain rfl : b = b' := hP₃
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact SimC.throw
  | true =>
    simp only [↓reduceIte]
    have hxW : Expr.WScoped 1 (reduceCertVar c) := by
      unfold reduceCertVar
      simp only [Expr.WScoped]
      refine ⟨Nat.zero_lt_one, ?_⟩
      unfold reduceElemTy
      split <;> simp only [Expr.WScoped]
    have happW : Expr.WScoped 1 (Expr.app valA (reduceCertVar c)) := by
      simp only [Expr.WScoped]
      exact ⟨Expr.WScoped.mono (Nat.zero_le 1) hwval, hxW⟩
    refine SimC.bind (opB_sim henv hs₃ happW hxW)
      (fun s₄ b2 b2' hs₄ hP₄ => ?_)
    obtain rfl : b2 = b2' := hP₄
    cases b2 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.throw
    | true =>
      simp only [↓reduceIte]
      exact SimC.pure hs₄ rfl

/-- `certifyNatEqs` at the cached shared operations. -/
theorem certifyNatEqsS_sim (henv : EnvWF env) :
    ∀ {eqs : List (Expr × Expr)},
      (∀ eq ∈ eqs, (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true)) →
      ∀ {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (certifyNatEqs (sharedOpsC mode (mkFEnv env)) env eqs)
        (certifyNatEqs (fueledOpsM mode) env eqs)
  | [], _, s₀, hs => SimC.pure hs rfl
  | eq :: rest, hsc, s₀, hs => by
    unfold certifyNatEqs
    dsimp only [sharedOpsC]
    have hh := hsc eq (List.mem_cons_self ..)
    refine SimC.bind (opB_sim henv hs (Expr.WScoped.of_wscopedB hh.1)
        (Expr.WScoped.of_wscopedB hh.2))
      (fun s₁ b b' hs₁ hP => ?_)
    obtain rfl : b = b' := hP
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact certifyNatEqsS_sim henv
        (fun e he => hsc e (List.mem_cons_of_mem _ he)) hs₁
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.pure hs₁ rfl

/-- `checkDivModCerts` at the cached shared operations. -/
theorem checkDivModCertsS_sim (henv : EnvWF env) {c : Name}
    {annVal : Expr} (hvf : annVal.hasFvar = false) :
    ∀ {stmts : List (List Expr × Expr)} {proofs : List Expr},
      (∀ st ∈ stmts, (∀ hyp ∈ st.1, hyp.wscopedB 2 = true) ∧
        st.2.wscopedB 4 = true) →
      ∀ {s₀ : CState}, CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (checkDivModCerts (sharedOpsC mode (mkFEnv env)) env c annVal
          stmts proofs)
        (checkDivModCerts (fueledOpsM mode) env c annVal stmts proofs)
  | [], [], _, s₀, hs => SimC.pure hs rfl
  | [], _ :: _, _, s₀, hs => SimC.pure hs rfl
  | _ :: _, [], _, s₀, hs => SimC.pure hs rfl
  | (hyps, eqE) :: srest, proof :: prest, hsc, s₀, hs => by
    unfold checkDivModCerts
    dsimp only [sharedOpsC]
    obtain ⟨hhyps, heqw⟩ := hsc (hyps, eqE) (List.mem_cons_self ..)
    have hhypsS : ∀ hyp ∈ hyps.map (Expr.substConst0 c annVal),
        hyp.wscopedB 2 = true := by
      intro hyp hh
      obtain ⟨h₀, hh₀, rfl⟩ := List.mem_map.mp hh
      exact wscopedB_substConst0 hvf _ (hhyps h₀ hh₀)
    have heqS : (Expr.substConst0 c annVal eqE).wscopedB 4 = true :=
      wscopedB_substConst0 hvf _ heqw
    by_cases hguards : divModCertGuard env c annVal hyps eqE proof = true
    case neg =>
      simp only [if_neg hguards]
      exact SimC.pure hs rfl
    simp only [if_pos hguards]
    have hguards' := hguards
    unfold divModCertGuard at hguards'
    simp only [Bool.and_eq_true] at hguards'
    have hpf : (Expr.substConstAll c annVal proof).hasFvar = false := by
      simpa using hguards'.1.1.1.1.2
    have happW : (divModCertApplied (Expr.substConstAll c annVal proof)
        (hyps.map (Expr.substConst0 c annVal))).wscopedB 4 = true :=
      divModCertApplied_wscopedB hpf hhypsS
    refine SimC.bind (opE_annotate_sim henv hs
        (Expr.WScoped.of_wscopedB happW))
      (fun s₁ appliedA appliedA' hs₁ hP => ?_)
    obtain ⟨rfl, hwapp⟩ := hP
    refine SimC.bind (opE_infer_sim henv hs₁ hwapp)
      (fun s₂ tp tp' hs₂ hP₂ => ?_)
    obtain ⟨rfl, hwtp⟩ := hP₂
    refine SimC.bind (opB_sim henv hs₂ hwtp (Expr.WScoped.of_wscopedB heqS))
      (fun s₃ b b' hs₃ hP₃ => ?_)
    obtain rfl : b = b' := hP₃
    cases b with
    | true =>
      simp only [↓reduceIte]
      exact checkDivModCertsS_sim henv hvf
        (fun st hst => hsc st (List.mem_cons_of_mem _ hst)) hs₃
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact SimC.pure hs₃ rfl

/-- `checkDivModPin` at the cached shared operations. -/
theorem checkDivModPinS_sim (henv : EnvWF env) {env2 : Env} {c : Name}
    (hc : c ∈ natDivModNames)
    (hv'f : ∀ cv' v' h', env2.find? c = some (.defnInfo cv' v' h') →
      v'.hasFvar = false)
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC
      (checkDivModPin (sharedOpsC mode (mkFEnv env)) env env2 c)
      (checkDivModPin (fueledOpsM mode) env env2 c) := by
  unfold checkDivModPin
  dsimp only [sharedOpsC]
  by_cases h1 : divModEnvGuard env2 c = true
  case neg => simp only [if_neg h1]; exact SimC.throw
  simp only [if_pos h1]
  cases hfind : env2.find? c with
  | none => exact SimC.throw
  | some ci =>
    cases ci with
    | axiomInfo cv' => exact SimC.throw
    | thmInfo cv' v' => exact SimC.throw
    | indInfo cv' caps => exact SimC.throw
    | ctorInfo cv' nP nF => exact SimC.throw
    | recInfo cv' mI rP rules => exact SimC.throw
    | projInfo _ => exact SimC.throw
    | defnInfo cv' value' hint' =>
      dsimp only
      by_cases hping : (divModPinGuard env c &&
          divModCertsGuard env c value') = true
      case neg => simp only [if_neg hping]; exact SimC.throw
      simp only [if_pos hping]
      have hping' := hping
      simp only [Bool.and_eq_true] at hping'
      have hping'' := hping'.1
      unfold divModPinGuard at hping''
      simp only [Bool.and_eq_true] at hping''
      have hpinF : (divModDeclPin c).hasFvar = false := by
        simpa using hping''.1.1.2
      refine SimC.bind (opE_annotate_sim henv hs
          (Expr.WScoped.of_not_hasFvar hpinF))
        (fun s₁ pinA pinA' hs₁ hP => ?_)
      obtain ⟨rfl, hwpin⟩ := hP
      have hvf : value'.hasFvar = false := hv'f _ _ _ hfind
      refine SimC.bind (opB_sim henv hs₁
          (Expr.WScoped.of_not_hasFvar hvf) hwpin)
        (fun s₂ b b' hs₂ hP₂ => ?_)
      obtain rfl : b = b' := hP₂
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact SimC.throw
      | true =>
        simp only [↓reduceIte]
        refine SimC.bind (checkDivModCertsS_sim henv hvf
            (divModCertStmts_wscopedB hc) hs₂)
          (fun s₃ ok ok' hs₃ hP₃ => ?_)
        obtain rfl : ok = ok' := hP₃
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw
        | true =>
          simp only [↓reduceIte]
          exact SimC.pure hs₃ rfl

/-- `installBasisDecl` (operation-free) as a `SimC`. -/
theorem installBasisDeclS_sim {env' : Env} {ci : ConstantInfo}
    (hs : CSOK mode env s₀) :
    SimC mode env s₀ RelVC (installBasisDecl env' ci : CheckCM Env)
      (installBasisDecl env' ci : FueledM Env) := by
  unfold installBasisDecl
  by_cases h1 : (env'.find? ci.name).isNone = true
  · simp only [if_pos h1]
    exact SimC.pure hs rfl
  · simp only [if_neg h1]
    exact SimC.throw_bind

/-- The basis-install fold as a `SimC`. -/
theorem installBasisFoldS_sim :
    ∀ (cis : List ConstantInfo) (env' : Env) {s₀ : CState},
      CSOK mode env s₀ →
      SimC mode env s₀ RelVC
        (cis.foldlM installBasisDecl env' : CheckCM Env)
        (cis.foldlM installBasisDecl env' : FueledM Env)
  | [], env', s₀, hs => SimC.pure hs rfl
  | ci :: cis, env', s₀, hs => by
    simp only [List.foldlM]
    refine SimC.bind (installBasisDeclS_sim hs)
      (fun s₁ e e' hs₁ hP => ?_)
    obtain rfl : e = e' := hP
    exact installBasisFoldS_sim cis e hs₁

/-- The non-inductive branches of `checkDecl` at the cached shared
operations: the whole declaration runs at the input environment, all
operation calls sharing one state. -/
theorem checkDeclS_nonind_sim (henv : EnvWF env) (hs : CSOK mode env s₀)
    {d : Declaration} (hnotind : ∀ block, d ≠ .indDecl block) :
    SimC mode env s₀ RelVC
      (checkDecl mode (sharedOpsC mode (mkFEnv env)) env d)
      (checkDecl mode (fueledOpsM mode) env d) := by
  cases d with
  | indDecl block => exact absurd rfl (hnotind block)
  | defnDecl cv value hint =>
    unfold checkDecl
    dsimp only
    refine SimC.bind (checkConstantValS_sim henv hs)
      (fun s₁ cvA cvA' hs₁ hP => ?_)
    obtain ⟨rfl, hwty⟩ := hP
    refine SimC.bind (checkDefnValS_sim henv hwty hs₁)
      (fun s₂ env2 env2' hs₂ hP₂ => ?_)
    obtain ⟨rfl, hv'fD⟩ := hP₂
    by_cases h1 : natOpNames.contains cvA.name = true
    case neg =>
      simp only [if_neg h1]
      by_cases h4 : natDivModNames.contains cvA.name = true
      case neg =>
        simp only [if_neg h4]
        exact SimC.pure hs₂ rfl
      simp only [if_pos h4]
      refine SimC.bind (checkDivModPinS_sim henv
          (List.contains_iff_mem.mp h4) hv'fD hs₂)
        (fun s₃ u u' hs₃ hP₃ => ?_)
      exact SimC.pure hs₃ rfl
    simp only [if_pos h1]
    by_cases h2 : (natOpGuard env2 cvA.name &&
        (natOpDeps cvA.name).all (natOpStoredOk env2)) = true
    case neg => simp only [if_neg h2]; exact SimC.throw_bind
    simp only [if_pos h2]
    cases hfind : env2.find? cvA.name with
    | none => exact SimC.throw_bind
    | some ci =>
      cases ci with
      | defnInfo cvS value' hintS =>
        dsimp only
        have hvf : value'.hasFvar = false := hv'fD _ _ _ hfind
        have hsc : ∀ eq ∈ (natOpEquations 0 cvA.name).map
            (fun eq => (Expr.substConst0 cvA.name value' eq.1,
              Expr.substConst0 cvA.name value' eq.2)),
            (eq.1.wscopedB 2 = true) ∧ (eq.2.wscopedB 2 = true) := by
          intro eq heq
          obtain ⟨eq₀, heq₀, rfl⟩ := List.mem_map.mp heq
          obtain ⟨hs1, hs2⟩ := natOpEquations_wscopedB
            (by simpa using h1) eq₀ heq₀
          exact ⟨wscopedB_substConst0 hvf _ hs1,
            wscopedB_substConst0 hvf _ hs2⟩
        refine SimC.bind (certifyNatEqsS_sim henv hsc hs₂)
          (fun s₃ ok ok' hs₃ hP₃ => ?_)
        obtain rfl : ok = ok' := hP₃
        cases ok with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact SimC.throw_bind
        | true =>
          simp only [↓reduceIte]
          by_cases h4 : natDivModNames.contains cvA.name = true
          case neg =>
            simp only [if_neg h4]
            exact SimC.pure hs₃ rfl
          simp only [if_pos h4]
          refine SimC.bind (checkDivModPinS_sim henv
              (List.contains_iff_mem.mp h4) hv'fD hs₃)
            (fun s₄ u u' hs₄ hP₄ => ?_)
          exact SimC.pure hs₄ rfl
      | axiomInfo cv' => exact SimC.throw_bind
      | thmInfo cv' v' => exact SimC.throw_bind
      | indInfo cv' caps => exact SimC.throw_bind
      | ctorInfo cv' nP nF => exact SimC.throw_bind
      | recInfo cv' mI rP rules => exact SimC.throw_bind
      | projInfo _ => exact SimC.throw_bind
  | thmDecl cv value =>
    unfold checkDecl
    dsimp only
    refine SimC.bind (checkConstantValS_sim henv hs)
      (fun s₁ cvA cvA' hs₁ hP => ?_)
    obtain ⟨rfl, hwty⟩ := hP
    exact checkThmValS_sim henv hwty hs₁
  | opaqueDecl cv value =>
    unfold checkDecl
    dsimp only
    refine SimC.bind (checkConstantValS_sim henv hs)
      (fun s₁ cvA cvA' hs₁ hP => ?_)
    obtain ⟨rfl, hwty⟩ := hP
    refine SimC.bind (checkOpaqueValS_sim henv hwty hs₁)
      (fun s₂ env2 env2' hs₂ hP₂ => ?_)
    obtain ⟨rfl, hvf⟩ := hP₂
    by_cases h1 : reduceOpNames.contains cvA.name = true
    case neg =>
      simp only [if_neg h1]
      exact SimC.pure hs₂ rfl
    simp only [if_pos h1]
    refine SimC.bind (checkReducePinS_sim henv hvf hs₂)
      (fun s₃ u u' hs₃ hP₃ => ?_)
    exact SimC.pure hs₃ rfl
  | axiomDecl cv =>
    unfold checkDecl
    dsimp only
    refine SimC.bind (checkConstantValS_sim henv hs)
      (fun s₁ cvA cvA' hs₁ hP => ?_)
    obtain ⟨rfl, hwty⟩ := hP
    by_cases h1 : stdAxiomOk env cvA = true
    · simp only [if_pos h1]
      exact SimC.pure hs₁ rfl
    · simp only [if_neg h1]
      by_cases htc : cvA.name = trustCompilerName
      · simp only [if_pos htc]
        by_cases htc2 : trustCompilerOk env cvA = true
        · simp only [if_pos htc2]
          exact SimC.pure hs₁ rfl
        · simp only [if_neg htc2]
          exact SimC.throw
      · simp only [if_neg htc]
        by_cases hor : cvA.name = ofReduceNatName ∨
            cvA.name = ofReduceBoolName
        · simp only [if_pos hor]
          by_cases hor2 : ofReduceAxOk env cvA = true
          · simp only [if_pos hor2]
            exact SimC.pure hs₁ rfl
          · simp only [if_neg hor2]
            exact SimC.throw
        · simp only [if_neg hor]
          by_cases h2 : cvA.name = propextName ∨ cvA.name = choiceName
          · simp only [if_pos h2]
            exact SimC.throw
          · simp only [if_neg h2]
            by_cases h3 : toleratedAxiomNames.contains cvA.name = true
            · simp only [if_pos h3]
              exact SimC.pure hs₁ rfl
            · simp only [if_neg h3]
              exact SimC.throw
  | basisDecl kind =>
    unfold checkDecl
    dsimp only
    by_cases hq : kind = .quotK
    · simp only [if_pos hq]
      by_cases he : env.find? eqName = some eqA
      · simp only [if_pos he]
        exact installBasisFoldS_sim _ env hs
      · simp only [if_neg he]
        exact SimC.throw_bind
    · simp only [if_neg hq]
      exact installBasisFoldS_sim _ env hs

end Walks1

end Setlec.Cached
