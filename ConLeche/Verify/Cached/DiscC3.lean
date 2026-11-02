module

public import ConLeche.Verify.Cached.DiscC2

public section

/-!
# Cached body walks, part 3: the stuck-major rescue and iota

Simulation walks for the cached `majorToCtorI`/`pinArgsI`/`iotaRecI`
(`ConLeche/Cached/CoreC.lean`) against `majorToCtor`/`iotaRec`
(`ConLeche/Kernel/Core.lean`).

Every walk here is a `Std.WP` triple proved by `vcgen` and `grind`
(`ConLeche/Verify/Cached/Grind.lean`).  The pure side of a nested
dispatch is never unfolded into its `match` tree: grind splits such a
tree on every discriminant and compares the alternatives' lambdas (the
cached and the pure restatements share their matchers).  Each arm the
cached walk can reach is instead one equation whose hypotheses are the
cached match's own arm hypotheses (`iotaRec_rec`, `iotaRecK_ctor`,
`mtc_body`, …, registered with guarded patterns), and the pieces between
the arms are named functions (`iotaRecK`, `iotaCertGate`, `iotaCertP`,
`iotaRecFire`, `mtcBodyP`; the cached blocks `iotaCertI`, `mtcBodyI`), so
that no `fun` holding a `match` reaches grind.  The environment reads
are named (`ctorVal?`; the caches' `findRule`, `constTyOf`, `ruleRhsOf`
in `SimCEff.lean`), with one guarded equation each at the arm that reads
them.
-/

set_option experimental.vcgen true

namespace ConLeche.Cached

open ConLeche.Expr Std.WP
open scoped Lean.Order

variable {mode : CheckMode}

/-! ## The residual and constructor-head readers -/

section Vocabulary

variable {env : Env}

theorem wscoped_piResidual {d : Nat} {t : Expr} {ys : List Expr} (ht : Expr.WScoped d t)
    (hys : AllWS d ys) : OptWS d (piResidual t ys) := by
  cases h : piResidual t ys with
  | none => trivial
  | some r => exact piResidual_WScoped h ht hys
grind_pattern [conleche_grind] wscoped_piResidual => Expr.WScoped d t, piResidual t ys

@[conleche_grind =] theorem isCtorAppC_eq (env : Env) (e : Expr) :
    isCtorAppC (mkFEnv env) e = isCtorApp env e :=
  isCtorAppC_spec

end Vocabulary

section Walks

variable {env : Env} {f : Nat}

/-! ### The stuck-major rescue's named pieces

The cached rescue's three blocks (`mtcKI`, `mtcEtaI`, `mtcAndI`) and the
pure ones' continuations past the major's type (`mtcKCont`, `mtcEtaCont`,
`mtcAndCont`) are the bodies' own code, named so that each block is one
triple.  A continuation's single one-level `match` reaches grind as is
(its discriminant is known in every arm); the four-deep dispatch of
`majorToCtor` reaches it only as one equation per arm (`mtc_body`, …). -/

/-- The leaf guard of a fabrication (the pure side's `fun` named). -/
@[expose] def leafGuardP (fab major : Expr) : Bool :=
  fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l)

@[conleche_grind =] theorem leafGuard_eq (fab major : Expr) :
    Expr.leafGuard fab major = leafGuardP fab major :=
  leafGuard_spec' rfl rfl

@[conleche_grind =] theorem wscopedBC_eq (d : Nat) (e : Expr) :
    Expr.wscopedBC d e = e.wscopedB d :=
  wscopedB_spec' rfl

theorem wscoped_of_wscopedB {d : Nat} {e : Expr} (h : e.wscopedB d = true) :
    Expr.WScoped d e :=
  WScoped.of_wscopedB h
grind_pattern [conleche_grind] wscoped_of_wscopedB => e.wscopedB d

@[conleche_grind =] theorem towerSlotsAllF_eq (env : Env) (T : Name) (n : Nat) :
    (mkFEnv env).towerSlotsAllF T n = towerSlotsAll env T n :=
  towerSlotsAllF_mkFEnv env T n

@[conleche_grind =] theorem andRescueSlotsF_eq (env : Env) (ctor : Name) (nP : Nat)
    (ust : List Level) :
    (mkFEnv env).andRescueSlotsF ctor nP ust = andRescueSlots env ctor nP ust :=
  andRescueSlotsF_spec

/-- The proof-irrelevance certificate behind its mode gate. -/
@[expose] def proofIrrelGate {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (mode : CheckMode) (r : CoreFns m) (depth : Nat) (a b : Expr) : m Bool :=
  if mode.verifiedChecks then proofIrrel r depth a b else pure true

theorem proofIrrelGate_of {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (hμ : mode.verifiedChecks = true) (r : CoreFns m) (depth : Nat) (a b : Expr) :
    proofIrrelGate mode r depth a b = proofIrrel r depth a b := by
  simp [proofIrrelGate, hμ]

/-- The cached K rescue. -/
@[expose] def mtcKI (mode : CheckMode) (r : CoreFnsI) (depth : Nat) (major : Expr) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : Name) : CheckCM Expr := do
  let tmaj₀ ← r.inferIO depth major
  let tmaj ← r.whnf depth tmaj₀
  match Expr.getAppFn tmaj with
  | .const T' ust =>
    if (← pure (T' == T)) ∧ cvj.levelParams.length = ust.length then do
      let margs ← pure (Expr.getAppArgsC tmaj)
      if cnP ≤ margs.length then do
        let ctorI ← pure rl.ctor
        let h ← pure (Expr.const ctorI ust)
        let fab ← mkAppNM h (margs.take cnP)
        if ← pure (Expr.wscopedBC depth fab &&
            Expr.looseBVarsBounded 0 fab &&
            Expr.leafGuard fab major) then do
          let tfab ← r.inferIO depth fab
          if ← r.defeq depth tmaj tfab then
            if ← certAtI mode (proofIrrelI r depth fab major) then
              pure fab
            else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- The cached η rescue. -/
@[expose] def mtcEtaI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (major : Expr) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : CheckCM Expr := do
  let tmaj₀ ← r.inferIO depth major
  let tmaj ← r.whnf depth tmaj₀
  match Expr.getAppFn tmaj with
  | .const T' ust => do
    let margs ← pure (Expr.getAppArgsC tmaj)
    let ustL ← pure ust
    if (← pure (T' == T)) ∧ margs.length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        capsNeverZero cvT.levelParams ustL caps = true ∧
        reservedBasisNames.contains T = false ∧
        reservedBasisNames.contains caps.etaCtor = false ∧
        fe.towerSlotsAllF T caps.etaFields = true then do
      let TI ← pure T
      let projs ← projNodesI TI major (List.range caps.etaFields)
      let ctorI ← pure caps.etaCtor
      let h ← pure (Expr.const ctorI ust)
      let fab ← mkAppNM h (margs ++ projs)
      if ← pure (Expr.wscopedBC depth fab &&
          Expr.looseBVarsBounded 0 fab &&
          Expr.leafGuard fab major) then
        pure fab
      else pure major
    else pure major
  | _ => pure major

/-- The cached `And` rescue. -/
@[expose] def mtcAndI (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat) (major : Expr) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : Name) : CheckCM Expr := do
  let tmaj₀ ← r.inferIO depth major
  let tmaj ← r.whnf depth tmaj₀
  match Expr.getAppFn tmaj with
  | .const T' ust => do
    let margs ← pure (Expr.getAppArgsC tmaj)
    if (← pure (T' == T)) ∧ margs.length = cnP ∧
        cvj.levelParams.length = ust.length ∧
        fe.andRescueSlotsF rl.ctor cnP ust = true then do
      let TI ← pure T
      let projs ← projNodesI TI major [0, 1]
      let ctorI ← pure rl.ctor
      let h ← pure (Expr.const ctorI ust)
      let fab ← mkAppNM h (margs ++ projs)
      if ← pure (Expr.wscopedBC depth fab &&
          Expr.looseBVarsBounded 0 fab &&
          Expr.leafGuard fab major) then do
        let tfab ← r.inferIO depth fab
        if ← r.defeq depth tmaj tfab then
          if ← certAtI mode (proofIrrelI r depth fab major) then
            pure fab
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- The cached rescue past its syntactic gates. -/
@[expose] def mtcBodyI (mode : CheckMode) (r : CoreFnsI) (fe : FEnv) (depth : Nat) (major : Expr) (rl : RecRule)
    (cvj : ConstantVal) (cnP : Nat) (T : Name) (cvT : ConstantVal) (caps : IndCaps) :
    CheckCM Expr :=
  if rl.k = true then mtcKI mode r depth major rl cvj cnP T
  else if rl.eta = true then mtcEtaI r fe depth major T cvT caps
  else if T = andName then mtcAndI mode r fe depth major rl cvj cnP T
  else pure major

/-- `majorToCtorI` with its blocks named. -/
theorem majorToCtorI_eq (r : CoreFnsI) (fe : FEnv) (depth : Nat) (recName : Name)
    (rules : List RecRule) (major : Expr) :
    majorToCtorI mode r fe depth recName rules major =
    (do
      if ← pure (isCtorAppC fe major) then pure major else
      match rules with
      | [rl] =>
        match fe.find? rl.ctor with
        | some (.ctorInfo cvj cnP _cnF) =>
          match (cvj.type.piResult).getAppFn with
          | .const T _ =>
            match fe.find? T with
            | some (.indInfo cvT caps) => mtcBodyI mode r fe depth major rl cvj cnP T cvT caps
            | _ => pure major
          | _ => pure major
        | _ => pure major
      | _ => pure major) := rfl

section PureMtc

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m] {r : CoreFns m} {d : Nat}

/-- The pure K rescue past the major's type. -/
@[expose] def mtcKCont (mode : CheckMode) (r : CoreFns m) (depth : Nat) (major : Expr)
    (rl : RecRule) (cvj : ConstantVal) (cnP : Nat) (T : Name) (tmaj : Expr) : m Expr :=
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ cvj.levelParams.length = ust.length then
      if cnP ≤ tmaj.getAppArgs.length then
        if (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).wscopedB depth &&
            (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)).looseBVarsBounded 0 &&
            leafGuardP (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) major then
          r.inferIO depth (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) >>=
            fun tfab => r.defeq depth tmaj tfab >>= fun rd =>
            if rd then
              proofIrrelGate mode r depth
                  (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP)) major >>=
                fun ok =>
                if ok then pure (Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP))
                else pure major
            else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- The pure η rescue past the major's type. -/
@[expose] def mtcEtaCont (env : Env) (depth : Nat) (major : Expr) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) (tmaj : Expr) : m Expr :=
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        capsNeverZero cvT.levelParams ust caps = true ∧
        reservedBasisNames.contains T = false ∧
        reservedBasisNames.contains caps.etaCtor = false ∧
        towerSlotsAll env T caps.etaFields = true then
      if (Expr.mkAppN (.const caps.etaCtor ust)
            (etaFabArgsE T tmaj.getAppArgs major caps.etaFields)).wscopedB depth &&
          (Expr.mkAppN (.const caps.etaCtor ust)
            (etaFabArgsE T tmaj.getAppArgs major caps.etaFields)).looseBVarsBounded 0 &&
          leafGuardP (Expr.mkAppN (.const caps.etaCtor ust)
            (etaFabArgsE T tmaj.getAppArgs major caps.etaFields)) major then
        pure (Expr.mkAppN (.const caps.etaCtor ust)
          (etaFabArgsE T tmaj.getAppArgs major caps.etaFields))
      else pure major
    else pure major
  | _ => pure major

/-- The pure `And` rescue past the major's type. -/
@[expose] def mtcAndCont (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (major : Expr) (rl : RecRule) (cvj : ConstantVal) (cnP : Nat) (T : Name) (tmaj : Expr) :
    m Expr :=
  match tmaj.getAppFn with
  | .const T' ust =>
    if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
        cvj.levelParams.length = ust.length ∧
        andRescueSlots env rl.ctor cnP ust = true then
      if (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])).wscopedB depth &&
          (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])).looseBVarsBounded 0 &&
          leafGuardP (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])) major then
        r.inferIO depth (Expr.mkAppN (.const rl.ctor ust)
            (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])) >>=
          fun tfab => r.defeq depth tmaj tfab >>= fun rd =>
          if rd then
            proofIrrelGate mode r depth (Expr.mkAppN (.const rl.ctor ust)
                (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])) major >>=
              fun ok =>
              if ok then
                pure (Expr.mkAppN (.const rl.ctor ust)
                  (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major]))
              else pure major
          else pure major
      else pure major
    else pure major
  | _ => pure major

/-- The pure rescue past its syntactic gates. -/
@[expose] def mtcBodyP (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat)
    (major : Expr) (rl : RecRule) (cvj : ConstantVal) (cnP : Nat) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : m Expr :=
  if rl.k = true then
    r.inferIO depth major >>= fun tm => r.whnf depth tm >>=
      mtcKCont mode r depth major rl cvj cnP T
  else if rl.eta = true then
    r.inferIO depth major >>= fun tm => r.whnf depth tm >>=
      mtcEtaCont env depth major T cvT caps
  else if T = andName then
    r.inferIO depth major >>= fun tm => r.whnf depth tm >>=
      mtcAndCont mode r env depth major rl cvj cnP T
  else pure major

/-- `majorToCtor` with its blocks named. -/
theorem majorToCtor_eq (recName : Name) (rules : List RecRule) (major : Expr) :
    majorToCtor mode r env d recName rules major =
    (if isCtorApp env major then pure major else
    match rules with
    | [rl] =>
      match env.find? rl.ctor with
      | some (.ctorInfo cvj cnP _cnF) =>
        match (cvj.type.piResult).getAppFn with
        | .const T _ =>
          match env.find? T with
          | some (.indInfo cvT caps) => mtcBodyP mode r env d major rl cvj cnP T cvT caps
          | _ => pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major) := rfl

/-! The pure rescue's arms, one equation each. -/

theorem mtc_isCtor {recName : Name} {rules : List RecRule} {major : Expr}
    (h : isCtorApp env major = true) :
    majorToCtor mode r env d recName rules major = pure major := by
  rw [majorToCtor_eq]; simp only [h, ↓reduceIte]
grind_pattern [conleche_grind] mtc_isCtor => majorToCtor mode r env d recName rules major where
  guard isCtorApp env major = true

theorem mtc_body {recName : Name} {rules : List RecRule} {major : Expr} {rl : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {T : Name} {lus : List Level} {cvT : ConstantVal}
    {caps : IndCaps} (h0 : isCtorApp env major = false) (h1 : rules = [rl])
    (h2 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (h3 : (cvj.type.piResult).getAppFn = .const T lus)
    (h4 : env.find? T = some (.indInfo cvT caps)) :
    majorToCtor mode r env d recName rules major =
      mtcBodyP mode r env d major rl cvj cnP T cvT caps := by
  rw [majorToCtor_eq]; subst h1; simp only [h0, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
grind_pattern [conleche_grind] mtc_body =>
    majorToCtor mode r env d recName rules major, [rl], ConstantInfo.ctorInfo cvj cnP cnF,
      Expr.const T lus, ConstantInfo.indInfo cvT caps where
  guard isCtorApp env major = false
  guard rules = [rl]
  guard env.find? rl.ctor = some (.ctorInfo cvj cnP cnF)
  guard (cvj.type.piResult).getAppFn = .const T lus
  guard env.find? T = some (.indInfo cvT caps)

theorem mtc_notSingle {recName : Name} {rules : List RecRule} {major : Expr}
    (h0 : isCtorApp env major = false) (h1 : ∀ rl, rules = [rl] → False) :
    majorToCtor mode r env d recName rules major = pure major := by
  rw [majorToCtor_eq]; simp only [h0, Bool.false_eq_true, ↓reduceIte]

theorem mtc_notCtor {recName : Name} {rules : List RecRule} {major : Expr} {rl : RecRule}
    (h0 : isCtorApp env major = false) (h1 : rules = [rl])
    (h2 : ∀ cvj cnP cnF, env.find? rl.ctor = some (.ctorInfo cvj cnP cnF) → False) :
    majorToCtor mode r env d recName rules major = pure major := by
  rw [majorToCtor_eq]; subst h1; simp only [h0, Bool.false_eq_true, ↓reduceIte]
grind_pattern [conleche_grind] mtc_notCtor => majorToCtor mode r env d recName rules major, [rl] where
  guard rules = [rl]

theorem mtc_notConst {recName : Name} {rules : List RecRule} {major : Expr} {rl : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} (h0 : isCtorApp env major = false)
    (h1 : rules = [rl]) (h2 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (h3 : ∀ T lus, (cvj.type.piResult).getAppFn = .const T lus → False) :
    majorToCtor mode r env d recName rules major = pure major := by
  rw [majorToCtor_eq]; subst h1; simp only [h0, h2, Bool.false_eq_true, ↓reduceIte]
grind_pattern [conleche_grind] mtc_notConst =>
    majorToCtor mode r env d recName rules major, [rl], ConstantInfo.ctorInfo cvj cnP cnF where
  guard rules = [rl]
  guard env.find? rl.ctor = some (.ctorInfo cvj cnP cnF)

theorem mtc_notInd {recName : Name} {rules : List RecRule} {major : Expr} {rl : RecRule}
    {cvj : ConstantVal} {cnP cnF : Nat} {T : Name} {lus : List Level}
    (h0 : isCtorApp env major = false) (h1 : rules = [rl])
    (h2 : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (h3 : (cvj.type.piResult).getAppFn = .const T lus)
    (h4 : ∀ cvT caps, env.find? T = some (.indInfo cvT caps) → False) :
    majorToCtor mode r env d recName rules major = pure major := by
  rw [majorToCtor_eq]; subst h1; simp only [h0, h2, h3, Bool.false_eq_true, ↓reduceIte]
grind_pattern [conleche_grind] mtc_notInd =>
    majorToCtor mode r env d recName rules major, [rl], ConstantInfo.ctorInfo cvj cnP cnF,
      Expr.const T lus where
  guard rules = [rl]
  guard env.find? rl.ctor = some (.ctorInfo cvj cnP cnF)
  guard (cvj.type.piResult).getAppFn = .const T lus

end PureMtc

/-! ### The rescue's walks -/

theorem mtcKC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) {d : Nat}
    {major : Expr} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat} {T : Name} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d major) :
    ⦃fun s => s = s₀⦄ mtcKI mode (coreKnotI mode (mkFEnv env) f) d major rl cvj cnP T
    ⦃fun v s' => CSOK mode env s' ∧
      Runs ((fueledFns mode env).inferIO d major >>= fun tm => (fueledFns mode env).whnf d tm >>=
        mtcKCont mode (fueledFns mode env) d major rl cvj cnP T) v ∧
      Expr.WScoped d v; ⊤⦄ := by
  sym only [conleche_grind, mtcKCont, proofIrrelGate_of hμ] =>
    vcgen [mtcKI, certAtI, mkAppNM, ih.inferIO_spec, ih.whnf_spec,
      ih.defeq_spec, proofIrrelC_spec ih] <;> finish

theorem mtcEtaC_spec (ih : SSimC mode env f) {d : Nat} {major : Expr} {T : Name}
    {cvT : ConstantVal} {caps : IndCaps} {s₀ : CState} (hs : CSOK mode env s₀)
    (hw : Expr.WScoped d major) :
    ⦃fun s => s = s₀⦄ mtcEtaI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d major T cvT caps
    ⦃fun v s' => CSOK mode env s' ∧
      Runs ((fueledFns mode env).inferIO d major >>= fun tm => (fueledFns mode env).whnf d tm >>=
        mtcEtaCont env d major T cvT caps) v ∧
      Expr.WScoped d v; ⊤⦄ := by
  sym only [conleche_grind, mtcEtaCont, etaFabArgsE] =>
    vcgen [mtcEtaI, mkAppNM, ih.inferIO_spec, ih.whnf_spec,
      projNodesC_spec (mode := mode) (env := env)] <;> finish

theorem mtcAndC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) {d : Nat}
    {major : Expr} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat} {T : Name} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d major) :
    ⦃fun s => s = s₀⦄ mtcAndI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d major rl cvj cnP T
    ⦃fun v s' => CSOK mode env s' ∧
      Runs ((fueledFns mode env).inferIO d major >>= fun tm => (fueledFns mode env).whnf d tm >>=
        mtcAndCont mode (fueledFns mode env) env d major rl cvj cnP T) v ∧
      Expr.WScoped d v; ⊤⦄ := by
  sym only [conleche_grind, mtcAndCont, proofIrrelGate_of hμ] =>
    vcgen [mtcAndI, certAtI, mkAppNM, ih.inferIO_spec, ih.whnf_spec,
      ih.defeq_spec, proofIrrelC_spec ih, projNodesC_spec (mode := mode) (env := env)] <;>
      finish

theorem mtcBodyC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f) {d : Nat}
    {major : Expr} {rl : RecRule} {cvj : ConstantVal} {cnP : Nat} {T : Name} {cvT : ConstantVal}
    {caps : IndCaps} {s₀ : CState} (hs : CSOK mode env s₀) (hw : Expr.WScoped d major) :
    ⦃fun s => s = s₀⦄
      mtcBodyI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d major rl cvj cnP T cvT caps
    ⦃fun v s' => CSOK mode env s' ∧
      Runs (mtcBodyP mode (fueledFns mode env) env d major rl cvj cnP T cvT caps) v ∧
      Expr.WScoped d v; ⊤⦄ := by
  sym only [conleche_grind, mtcBodyP] =>
    vcgen [mtcBodyI, mtcKC_spec hμ ih hs hw, mtcEtaC_spec ih hs hw,
      mtcAndC_spec hμ ih hs hw] <;> finish

/-- `majorToCtorI` simulates its fueled original. -/
theorem majorToCtorC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    {d : Nat} {recName : Name} {rules : List RecRule} {i : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      majorToCtorI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d recName rules i
    ⦃fun m s' => CSOK mode env s' ∧
      Runs (majorToCtor mode (fueledFns mode env) env d recName rules i) m ∧
      Expr.WScoped d m; ⊤⦄ := by
  sym only [conleche_grind, mtc_notSingle] =>
    vcgen [majorToCtorI_eq, mtcBodyC_spec hμ ih hs hw] <;> finish

/-- The major's preparation, in either order (the K flag is the single
rule's stored bit, read identically on both sides; off K, the rescue on
the raw major, then, failing a constructor, the whnf chain). -/
theorem prepareMajorC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    {d : Nat} {recName : Name} {rules : List RecRule} {i : Expr} {s₀ : CState}
    (hs : CSOK mode env s₀) (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄
      prepareMajorI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d recName rules i
    ⦃fun m s' => CSOK mode env s' ∧
      Runs (prepareMajor mode (fueledFns mode env) env d recName rules i) m ∧
      Expr.WScoped d m; ⊤⦄ := by
  sym only [conleche_grind, prepareMajor] =>
    vcgen [prepareMajorI, majorToCtorC_spec (mode := mode) (env := env) hμ ih,
      litMajorToCtorC_spec (mode := mode) (env := env) ih, ih.whnf_spec] <;> finish

/-! ### The ι step's named pieces -/

/-- A nested rule's pin at the recursor's levels and leading arguments. -/
@[expose] def pinInst (lps : List Name) (us : List Level) (args : List Expr) (t : Nat)
    (p : Expr) : Expr :=
  Expr.instSpine args t (p.instantiateLevelParams lps us)

/-- `recFireComparands` with the firing mode as an argument. -/
@[expose] def fireCmp (fire : RecRuleFire) (ctorParams : Nat) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    List Level × List Expr :=
  match fire with
  | .nested lvls pins =>
    (lvls.map (Level.subst lps us), pins.map (pinInst lps us (args.take rP) (rP - 1)))
  | .plain => ((cvjLps.map Level.param).map (Level.subst lps us), args.take ctorParams)

@[conleche_grind =] theorem recFireComparands_eq (rl : RecRule) (lps : List Name)
    (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    recFireComparands rl lps us cvjLps args rP =
      fireCmp rl.fire rl.ctorParams lps us cvjLps args rP := by
  unfold recFireComparands fireCmp pinInst
  cases rl.fire <;> simp

@[conleche_grind =] theorem fireCmp_nested (lvls : List Level) (pins : List Expr) (n : Nat)
    (lps : List Name) (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    fireCmp (.nested lvls pins) n lps us cvjLps args rP =
      (lvls.map (Level.subst lps us), pins.map (pinInst lps us (args.take rP) (rP - 1))) := rfl

@[conleche_grind =] theorem fireCmp_plain (n : Nat)
    (lps : List Name) (us : List Level) (cvjLps : List Name) (args : List Expr) (rP : Nat) :
    fireCmp .plain n lps us cvjLps args rP =
      ((cvjLps.map Level.param).map (Level.subst lps us), args.take n) := rfl

/-- Every element of the list is free of free variables. -/
@[expose] def AllClosed (xs : List Expr) : Prop := ∀ x ∈ xs, x.hasFvar = false

theorem allWS_pinInst {d : Nat} {pins args : List Expr} (lps : List Name) (us : List Level)
    (t : Nat) (hp : AllClosed pins) (ha : AllWS d args) :
    AllWS d (pins.map (pinInst lps us args t)) := by
  intro x hx
  obtain ⟨p, hp', rfl⟩ := List.mem_map.mp hx
  exact instSpine_WScoped t (WScoped.of_not_hasFvar (by
    rw [hasFvar_instantiateLevelParams]; exact hp p hp')) ha
grind_pattern [conleche_grind] allWS_pinInst => AllWS d (pins.map (pinInst lps us args t))

/-- A nested rule's stored pins are closed. -/
@[expose] def FireClosed : RecRuleFire → Prop
  | .plain => True
  | .nested _ pins => AllClosed pins

@[conleche_grind =] theorem FireClosed.nested_eq (lvls : List Level) (pins : List Expr) :
    FireClosed (.nested lvls pins) = AllClosed pins := rfl

/-- A found rule's stored data is closed. -/
@[expose] def OptRuleOK : Option RecRule → Prop
  | none => True
  | some rl => rl.rhs.hasFvar = false ∧ FireClosed rl.fire

@[conleche_grind =] theorem OptRuleOK.some_eq (rl : RecRule) :
    OptRuleOK (some rl) = (rl.rhs.hasFvar = false ∧ FireClosed rl.fire) := rfl

/-- Every rule's stored data is closed. -/
@[expose] def AllRulesOK (rules : List RecRule) : Prop := ∀ rl ∈ rules, OptRuleOK (some rl)

theorem allRulesOK_find {rules : List RecRule} (h : AllRulesOK rules) (cj : Name) :
    OptRuleOK (findRule rules cj) := by
  cases hf : findRule rules cj with
  | none => trivial
  | some rl => exact h rl (List.mem_of_find?_eq_some hf)
grind_pattern [conleche_grind] allRulesOK_find => AllRulesOK rules, findRule rules cj

theorem EnvWF.ctorTy_closed (henv : EnvWF env) {cj : Name} {cvj : ConstantVal} {nP nF : Nat}
    (hfj : env.find? cj = some (.ctorInfo cvj nP nF)) : cvj.type.hasFvar = false :=
  (henv.consts _ (Env.find?_mem hfj)).1

theorem EnvWF.rules_ok (henv : EnvWF env) {c : Name} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (hfc : env.find? c = some (.recInfo cv mI rP rules)) :
    AllRulesOK rules := by
  obtain ⟨-, -, -, -, -, hrules, -⟩ := henv.consts _ (Env.find?_mem hfc)
  intro rl hrl
  obtain ⟨hrf, -, -, -, g5⟩ := hrules cv mI rP rules rfl rl hrl
  refine ⟨hrf, ?_⟩
  cases hf : rl.fire with
  | plain => trivial
  | nested lvls pins => exact fun pin hpin => ((g5 lvls pins hf).2.2.1 pin hpin).1

/-- The constructor record stored under `n`. -/
@[expose] def ctorVal? (env : Env) (n : Name) : Option ConstantVal :=
  match env.find? n with
  | some (.ctorInfo cv _ _) => some cv
  | _ => none

theorem ctorVal?_some {n : Name} {cv : ConstantVal} (h : ctorVal? env n = some cv) :
    ∃ nP nF, env.find? n = some (.ctorInfo cv nP nF) := by
  unfold ctorVal? at h
  split at h
  · cases h; exact ⟨_, _, by assumption⟩
  · cases h

theorem ctorVal?_of {n : Name} {cv : ConstantVal} {nP nF : Nat}
    (h : env.find? n = some (.ctorInfo cv nP nF)) : ctorVal? env n = some cv := by
  simp only [ctorVal?, h]
grind_pattern [conleche_grind] ctorVal?_of => ctorVal? env n, ConstantInfo.ctorInfo cv nP nF where
  guard env.find? n = some (.ctorInfo cv nP nF)

theorem ruleRhsOf_some {c j : Name} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {rl : RecRule} (h2 : env.find? c = some (.recInfo cv mI rP rules))
    (h3 : findRule rules j = some rl) (us : List Level) :
    ruleRhsOf env c j us = some (rl.rhs.instantiateLevelParams cv.levelParams us) := by
  simp only [ruleRhsOf, h2, h3]
grind_pattern [conleche_grind] ruleRhsOf_some =>
    ruleRhsOf env c j us, ConstantInfo.recInfo cv mI rP rules, some rl where
  guard env.find? c = some (.recInfo cv mI rP rules)
  guard findRule rules j = some rl

/-- The cached ι certificate block (the argument of `certAtI` in
`iotaRecI`). -/
@[expose] def iotaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (cv : ConstantVal)
    (mI rP : Nat) (us : List Level) (args : List Expr) (cj cjn : Name) (usj : List Level)
    (cvj : ConstantVal) (rl : RecRule) (margs : List Expr) : CheckCM Bool := do
  let cmpLvls : List Level ←
    match rl.fire with
    | .nested lvls _ => substLevelTreesM cv.levelParams us lvls
    | .plain =>
      substLevelTreesM cv.levelParams us
        (cvj.levelParams.map Level.param)
  if iotaCase3 fe.find? rl cvj cmpLvls then do
    let oL ← isEquivListLM usj cmpLvls
    if ← liftFueled "level comparison" oL then do
      let cmpArgs : List Expr ←
        match rl.fire with
        | .nested _ pins =>
          pinArgsI cv.levelParams us (args.take rP) (rP - 1) pins
        | .plain => pure (args.take rl.ctorParams)
      if ← defEqListI r fe depth (margs.take rl.ctorParams) cmpArgs then do
        let tyCtor ← constTyAtM fe cj cjn usj
        if ← iotaCertsFullI r fe depth tyCtor margs then
          iotaIndexOkI r fe depth mI rP rl.ctorParams tyCtor
            margs ((args.take mI).drop rP)
        else pure false
      else pure false
    else pure false
  else pure true

/-- The pure ι certificate block (case 3 of the ι case split). -/
@[expose] def iotaCertP {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) (env : Env) (depth : Nat) (cv : ConstantVal) (mI rP : Nat)
    (us : List Level) (args : List Expr) (usj : List Level) (cvj : ConstantVal)
    (rl : RecRule) (margs : List Expr) : m Bool := do
  let cmp := recFireComparands rl cv.levelParams us cvj.levelParams args rP
  if iotaCase3 env.find? rl cvj cmp.1 then do
    if ← liftFueled "level comparison" (Level.isEquivList usj cmp.1) then
      if ← defEqList r env depth (margs.take rl.ctorParams) cmp.2 then
        if ← iotaCertsFull r env depth
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            margs then
          iotaIndexOk r env depth mI rP rl.ctorParams
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            margs ((args.take mI).drop rP)
        else pure false
      else pure false
    else pure false
  else pure true

/-- The pure ι certificate block behind its mode gate. -/
@[expose] def iotaCertGate {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (mode : CheckMode) (r : CoreFns m) (env : Env) (depth : Nat) (cv : ConstantVal)
    (mI rP : Nat) (us : List Level) (args : List Expr) (usj : List Level) (cvj : ConstantVal)
    (rl : RecRule) (margs : List Expr) : m Bool :=
  if mode.verifiedChecks then iotaCertP r env depth cv mI rP us args usj cvj rl margs
  else pure true

/-- The firing tail of the pure ι step. -/
@[expose] def iotaRecFire {m : Type → Type} [Monad m] (cv : ConstantVal) (us : List Level)
    (args : List Expr) (rP : Nat) (rl : RecRule) (margs : List Expr) (ok : Bool) :
    m (Option Expr) :=
  if ok then
    pure (some (Expr.mkAppN
      (rl.rhs.instantiateLevelParams cv.levelParams us)
      (args.take rP ++ margs.drop rl.ctorParams)))
  else pure none

/-- The pure ι step past the major's preparation. -/
@[expose] def iotaRecK {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) (env : Env) (depth : Nat) (args : List Expr) (us : List Level)
    (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule) (major : Expr) :
    m (Option Expr) :=
  match major.getAppFn with
  | .const cj usj =>
    match env.find? cj with
    | some (.ctorInfo cvj _ _) =>
      match findRule rules cj with
      | some rl =>
        if major.getAppArgs.length = rl.ctorParams + rl.nfields then
          iotaCertGate mode r env depth cv mI rP us args usj cvj rl major.getAppArgs >>=
            iotaRecFire cv us args rP rl major.getAppArgs
        else pure none
      | none => pure none
    | _ => pure none
  | _ => pure none

/-- `iotaRecI` with its certificate block named. -/
theorem iotaRecI_eq (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    iotaRecI mode r fe depth e =
    (match Expr.getAppFn e with
    | .const c us => do
      let cn ← pure c
      match fe.find? cn with
      | some (.recInfo cv mI rP rules) => do
        let args ← pure (Expr.getAppArgsC e)
        if args.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
            (Expr.peelPis (mI + 1) cv.type).isSome = true then do
          let bvar0 ← pure (Expr.mkBvar 0)
          let major ← prepareMajorI mode r fe depth cn rules (args.getD mI bvar0)
          match Expr.getAppFn major with
          | .const cj usj => do
            let cjn ← pure cj
            match fe.find? cjn with
            | some (.ctorInfo cvj _ _) =>
              match findRule rules cjn with
              | some rl => do
                let margs ← pure (Expr.getAppArgsC major)
                if margs.length = rl.ctorParams + rl.nfields then do
                  if ← certAtI mode
                      (iotaCertI r fe depth cv mI rP us args cj cjn usj cvj rl margs) then do
                    let rhs ← ruleRhsAtM fe c cj cn cjn us
                    let red ← mkAppNM rhs
                      (args.take rP ++ margs.drop rl.ctorParams)
                    pure (some red)
                  else pure none
                else pure none
              | none => pure none
            | _ => pure none
          | _ => pure none
        else pure none
      | _ => pure none
    | _ => pure none) := rfl

/-- `iotaRec` with its continuation past the major named. -/
theorem iotaRec_eq {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    iotaRec mode r env depth e =
    (match e.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.recInfo cv mI rP rules) =>
        if e.getAppArgs.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
            (Expr.peelPis (mI + 1) cv.type).isSome = true then
          prepareMajor mode r env depth c rules (e.getAppArgs.getD mI (.bvar 0)) >>=
            iotaRecK (mode := mode) r env depth e.getAppArgs us cv mI rP rules
        else pure none
      | _ => pure none
    | _ => pure none) := rfl

/-! ### The pure ι step's arms, one equation each -/

section PureArms

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m] {r : CoreFns m} {d : Nat}

theorem iotaRec_rec {e : Expr} {c : Name} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} (h1 : e.getAppFn = .const c us)
    (h2 : env.find? c = some (.recInfo cv mI rP rules)) :
    iotaRec mode r env d e =
      if e.getAppArgs.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
          (Expr.peelPis (mI + 1) cv.type).isSome = true then
        prepareMajor mode r env d c rules (e.getAppArgs.getD mI (.bvar 0)) >>=
          iotaRecK (mode := mode) r env d e.getAppArgs us cv mI rP rules
      else pure none := by
  rw [iotaRec_eq]; simp only [h1, h2]
grind_pattern [conleche_grind] iotaRec_rec =>
    iotaRec mode r env d e, Expr.const c us, ConstantInfo.recInfo cv mI rP rules where
  guard e.getAppFn = .const c us
  guard env.find? c = some (.recInfo cv mI rP rules)

theorem iotaRec_notconst {e : Expr} (h : ∀ c us, e.getAppFn = .const c us → False) :
    iotaRec mode r env d e = pure none := by
  rw [iotaRec_eq]; split
  · next h' => exact (h _ _ h').elim
  · rfl

theorem iotaRec_notrec {e : Expr} {c : Name} {us : List Level} (h1 : e.getAppFn = .const c us)
    (h2 : ∀ cv mI rP rules, env.find? c = some (.recInfo cv mI rP rules) → False) :
    iotaRec mode r env d e = pure none := by
  rw [iotaRec_eq]; simp only [h1]
grind_pattern [conleche_grind] iotaRec_notrec => iotaRec mode r env d e, Expr.const c us where
  guard e.getAppFn = .const c us

theorem iotaRecK_ctor {args : List Expr} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {major : Expr} {cj : Name} {usj : List Level} {cvj : ConstantVal}
    {nP nF : Nat} {rl : RecRule} (h1 : major.getAppFn = .const cj usj)
    (h2 : env.find? cj = some (.ctorInfo cvj nP nF)) (h3 : findRule rules cj = some rl) :
    iotaRecK (mode := mode) r env d args us cv mI rP rules major =
      if major.getAppArgs.length = rl.ctorParams + rl.nfields then
        iotaCertGate mode r env d cv mI rP us args usj cvj rl major.getAppArgs >>=
          iotaRecFire cv us args rP rl major.getAppArgs
      else pure none := by
  rw [iotaRecK]; simp only [h1, h2, h3]
grind_pattern [conleche_grind] iotaRecK_ctor =>
    iotaRecK (mode := mode) r env d args us cv mI rP rules major, Expr.const cj usj,
      ConstantInfo.ctorInfo cvj nP nF, some rl where
  guard major.getAppFn = .const cj usj
  guard env.find? cj = some (.ctorInfo cvj nP nF)
  guard findRule rules cj = some rl

theorem iotaRecK_notconst {args : List Expr} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {major : Expr} (h : ∀ c us, major.getAppFn = .const c us → False) :
    iotaRecK (mode := mode) r env d args us cv mI rP rules major = pure none := by
  rw [iotaRecK]; split
  · next h' => exact (h _ _ h').elim
  · rfl

theorem iotaRecK_notctor {args : List Expr} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {major : Expr} {cj : Name} {usj : List Level}
    (h1 : major.getAppFn = .const cj usj)
    (h2 : ∀ cvj nP nF, env.find? cj = some (.ctorInfo cvj nP nF) → False) :
    iotaRecK (mode := mode) r env d args us cv mI rP rules major = pure none := by
  rw [iotaRecK]; simp only [h1]
grind_pattern [conleche_grind] iotaRecK_notctor =>
    iotaRecK (mode := mode) r env d args us cv mI rP rules major, Expr.const cj usj where
  guard major.getAppFn = .const cj usj

theorem iotaRecK_norule {args : List Expr} {us : List Level} {cv : ConstantVal} {mI rP : Nat}
    {rules : List RecRule} {major : Expr} {cj : Name} {usj : List Level} {cvj : ConstantVal}
    {nP nF : Nat} (h1 : major.getAppFn = .const cj usj)
    (h2 : env.find? cj = some (.ctorInfo cvj nP nF)) (h3 : findRule rules cj = none) :
    iotaRecK (mode := mode) r env d args us cv mI rP rules major = pure none := by
  rw [iotaRecK]; simp only [h1, h2, h3]
grind_pattern [conleche_grind] iotaRecK_norule =>
    iotaRecK (mode := mode) r env d args us cv mI rP rules major, Expr.const cj usj,
      ConstantInfo.ctorInfo cvj nP nF where
  guard major.getAppFn = .const cj usj
  guard env.find? cj = some (.ctorInfo cvj nP nF)
  guard findRule rules cj = none

theorem iotaCertGate_of (hμ : mode.verifiedChecks = true) (r : CoreFns m) (env : Env)
    (depth : Nat) (cv : ConstantVal) (mI rP : Nat) (us : List Level) (args : List Expr)
    (usj : List Level) (cvj : ConstantVal) (rl : RecRule) (margs : List Expr) :
    iotaCertGate mode r env depth cv mI rP us args usj cvj rl margs =
      iotaCertP r env depth cv mI rP us args usj cvj rl margs := by
  simp [iotaCertGate, hμ]

omit [MonadExceptOf CheckError m] in
@[conleche_grind =] theorem iotaRecFire_true (cv : ConstantVal) (us : List Level)
    (args : List Expr) (rP : Nat) (rl : RecRule) (margs : List Expr) :
    (iotaRecFire cv us args rP rl margs true : m (Option Expr)) =
      pure (some (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
        (args.take rP ++ margs.drop rl.ctorParams))) := rfl

omit [MonadExceptOf CheckError m] in
@[conleche_grind =] theorem iotaRecFire_false (cv : ConstantVal) (us : List Level)
    (args : List Expr) (rP : Nat) (rl : RecRule) (margs : List Expr) :
    (iotaRecFire cv us args rP rl margs false : m (Option Expr)) = pure none := rfl

end PureArms

/-! ### The ι walks -/

/-- The cached pin instantiations are the nested comparand's mapped
list. -/
theorem pinArgsC_spec (lps : List Name) (us : List Level) :
    ∀ (ps : List Expr) {s₀ : CState}, CSOK mode env s₀ → ∀ (args : List Expr) (t : Nat),
      ⦃fun s => s = s₀⦄ pinArgsI lps us args t ps
      ⦃fun rs s' => CSOK mode env s' ∧ rs = ps.map (pinInst lps us args t); ⊤⦄ := by
  intro ps
  induction ps with
  | nil =>
    intro _ _ _ _
    sym only [conleche_grind, List.map_nil] => vcgen [pinArgsI] <;> finish
  | cons _ ps ih =>
    intro _ _ _ _
    sym only [conleche_grind, List.map_cons, pinInst] =>
      vcgen [pinArgsI, instLevelParamsM, instSpineM, ih] <;> finish

/-- The canonical-index comparison (the ι batch) simulates its fueled
original. -/
theorem iotaIndexOkC_spec (ih : SSimC mode env f) {d : Nat} {mI rP cnP : Nat}
    {ty : Expr} {margs idx : List Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hwty : Expr.WScoped d ty) (hwm : AllWS d margs) (hwi : AllWS d idx) :
    ⦃fun s => s = s₀⦄
      iotaIndexOkI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d mI rP cnP ty margs idx
    ⦃fun b s' => CSOK mode env s' ∧
      Runs (iotaIndexOk (fueledFns mode env) env d mI rP cnP ty margs idx) b; ⊤⦄ := by
  sym only [conleche_grind, iotaIndexOk] =>
    vcgen [iotaIndexOkI, piResidualM_spec hs, defEqListC_spec ih] <;> finish

/-- The case-3 certificate block simulates its fueled original. -/
theorem iotaCertC_spec (ih : SSimC mode env f) (henv : EnvWF env) {d : Nat} {s₀ : CState}
    (hs : CSOK mode env s₀) (cv : ConstantVal) (mI rP : Nat) (us : List Level)
    {args : List Expr} (hargs : AllWS d args) (cj cjn : Name) (usj : List Level)
    {cvj : ConstantVal} (hfj : ctorVal? env cjn = some cvj) {rl : RecRule}
    (hrl : OptRuleOK (some rl)) {margs : List Expr} (hm : AllWS d margs) :
    ⦃fun s => s = s₀⦄
      iotaCertI (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d cv mI rP us args cj cjn usj cvj
        rl margs
    ⦃fun b s' => CSOK mode env s' ∧
      Runs (iotaCertP (fueledFns mode env) env d cv mI rP us args usj cvj rl margs) b; ⊤⦄ := by
  obtain ⟨nP, nF, hfj⟩ := ctorVal?_some hfj
  sym only [conleche_grind, iotaCertP, constTyOf, ConstantInfo.toConstantVal,
      Option.isSome_some, EnvWF.ctorTy_closed henv hfj] =>
    vcgen [iotaCertI, liftFueled, substLevelTreesM, isEquivListLM_spec hs,
      pinArgsC_spec (mode := mode) (env := env),
      defEqListC_spec ih, constTyAtM_spec (mode := mode) (env := env),
      iotaCertsFullC_spec ih, iotaIndexOkC_spec ih] <;> finish

/-- The ι step simulates its fueled original. -/
theorem iotaRecC_spec (hμ : mode.verifiedChecks = true) (ih : SSimC mode env f)
    (henv : EnvWF env) {d : Nat} {i : Expr} {s₀ : CState} (hs : CSOK mode env s₀)
    (hw : Expr.WScoped d i) :
    ⦃fun s => s = s₀⦄ iotaRecI mode (coreKnotI mode (mkFEnv env) f) (mkFEnv env) d i
    ⦃fun o s' => CSOK mode env s' ∧ Runs (iotaRec mode (fueledFns mode env) env d i) o ∧
      OptWS d o; ⊤⦄ := by
  sym only [conleche_grind, iotaRec_notconst, iotaRecK_notconst, Option.isSome_some,
      iotaCertGate_of hμ, → EnvWF.rules_ok henv] =>
    vcgen [iotaRecI_eq, certAtI, mkAppNM, prepareMajorC_spec hμ ih,
      iotaCertC_spec ih henv (mode := mode) (env := env),
      ruleRhsAtM_spec (mode := mode) (env := env)] <;> finish [Expr.WScoped.of_not_hasFvar]

end Walks

end ConLeche.Cached
