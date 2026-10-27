module

public import ConLeche.Cached.StateC

@[expose] public section

/-!
# The cached checker core

The core over the computed-field representation: `whnfCore`, `whnf`,
`infer`, `inferIO` and `defeq`, each memoized in `CState`; a
syntactic read is the operation itself (task #198).

See DESIGN.md, "The cached checker".

**One body, two modes.**  Every body below is a template
over `mode : CheckMode`, and the knot at the end (`coreKnotI mode`)
ties them at a mode.  The verified core is this knot at `.verified`;
the trusted core is this same knot at `.trusted` — there is no second
implementation: what
the trusted mode omits is exactly what `mode.verifiedChecks` gates
here: group A (the η body-type comparison, the λ/λ body-type
comparison, the projection certificate) and the
certificate families (every `certAtI` site), and
nothing else (DESIGN.md, "CORET
RETIRED").  Every read is a `match` on the two-constructor enum
(`ConLeche/Kernel/Env.lean`), so at either literal mode it reduces by
`rfl` and the branch is gone, not collapsed.
-/

namespace ConLeche.Cached

open ConLeche

variable {m : Type → Type}

/-! ## The core record and its helper twins -/

/-- The record of mutually recursive cached entry points. -/
structure CoreFnsI where
  whnfCore : Bool → Nat → Expr → CheckCM Expr
  whnf : Nat → Expr → CheckCM Expr
  infer : Nat → Expr → CheckCM Expr
  defeq : Nat → Expr → Expr → CheckCM Bool
  /-- Definitional equality in the **eager tower** (task #353) — the
  twin of `CoreFns.defeqE`. -/
  defeqE : Nat → Expr → Expr → CheckCM Bool
  /-- Type inference at the **infer-only grade** (task #170 / #172 B4)
  — the twin of `CoreFns.inferIO` (`ConLeche/Kernel/Core.lean`): what
  every internal inference call site runs: the io body under its own
  memo (`CState.inferIOC`), at both modes (task #346: official's
  `infer_only`). -/
  inferIO : Nat → Expr → CheckCM Expr

/-- The io-grade view (twin of `CoreFns.ioView`): the record whose
full-grade `infer` slot is the io slot, so a body written against
`r.infer` recurses at the io grade when handed `r.ioView`. -/
def CoreFnsI.ioView (r : CoreFnsI) : CoreFnsI :=
  { r with infer := r.inferIO }

/-- Twin of `unfoldDefinition` (monadic: the unfolded value is read
through the `(name, levels)` cache).  Like the spec, a theorem never
unfolds. -/
def unfoldDefinitionI (fe : FEnv) (e : Expr) : CheckCM (Option Expr) := do
  match Expr.getAppFn e with
  | .const n us => do
    let nm ← pure n
    match fe.find? nm with
    | some (.defnInfo cv _ _) =>
      if us.length = cv.levelParams.length then do
        let v ← constValAtM fe n nm us
        let args ← pure (Expr.getAppArgsC e)
        let r ← mkAppNM v args
        pure (some r)
      else pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `litToCtorIfNat`. -/
def litToCtorIfNatI (fe : FEnv) (e : Expr) : CheckCM Expr := do
  match e with
  | .lit (.natVal n) =>
    if natLitSupportedF fe then pure (natLitToConstructor n)
    else pure e
  | _ => pure e

/-- Twin of `reduceNat`. -/
def reduceNatI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) := do
  match e with
  | .app f₁ b =>
    match f₁ with
    | .const c us =>
      match us with
      | _ :: _ => pure none
      | [] => do
        let cn ← pure c
        if cn = natSuccName ∧ natLitSupportedF fe then do
          let w ← r.whnf depth b
          match ← pure (rawNatLitC? w) with
          | some n => do
            let r ← pure (Expr.lit (.natVal (n + 1)))
            pure (some r)
          | none => pure none
        else pure none
    | .app f₂ a =>
      match f₂ with
      | .const c us =>
        match us with
        | _ :: _ => pure none
        | [] => do
          let cn ← pure c
          if (cn = natAddName ∨ cn = natSubName ∨ cn = natMulName ∨
              cn = natPowName ∨ cn = natBeqName ∨ cn = natBleName ∨
              cn = natDivName ∨ cn = natModName ∨ cn = natGcdName ∨
              cn = natLandName ∨ cn = natLorName ∨ cn = natXorName ∨
              cn = natShiftLeftName ∨ cn = natShiftRightName) ∧
              natOpStoredF fe cn = true then do
            -- first argument first; the second only behind a literal
            -- (official `reduce_bin_nat_op`; the spec's D15 note)
            let w₁ ← r.whnf depth a
            match ← pure (rawNatLitC? w₁) with
            | some n₁ => do
              let w₂ ← r.whnf depth b
              match ← pure (rawNatLitC? w₂) with
              | some n₂ =>
                match natOpResult cn n₁ n₂ with
                | some x => do
                  let r ← pure x
                  pure (some r)
                | none => pure none
              | none => pure none
            | none => pure none
          else if natOpWfNames.contains cn ∧ natLitSupportedF fe then do
            let w₁ ← r.whnf depth a
            match ← pure (rawNatLitC? w₁) with
            | some _ => do
              let w₂ ← r.whnf depth b
              match ← pure (rawNatLitC? w₂) with
              | some _ => throw (.notImplemented
                  s!"native Nat computation on literals ({cn})")
              | none => pure none
            | none => pure none
          else pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none

/-- Twin of `iotaCertsFull` (task #342 L10, ι's case 3), in bulk form:
the consumed arguments are kept in an accumulator and substituted into
each binder's *domain* (small) instead of instantiating the whole
residual telescope per argument; a raw `bvar` body substitutes the
accumulator and re-enters.  Every slot is certified, its argument
inferred at the FULL grade. -/
def iotaCertsFullIAux (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Expr → List Expr → List Expr → CheckCM Bool
  | _, _, [] => pure true
  | ty, acc, arg :: rest => do
    match ty with
    | .forallE dom body => do
        let dom' ← instListM dom acc
        let ta ← r.infer depth arg
        if ← r.defeq depth ta dom' then
          iotaCertsFullIAux r fe depth body (arg :: acc) rest
        else pure false
    | .bvar _ =>
      match acc with
      | [] => pure false
      | _ :: _ => do
        let ty' ← instListM ty acc
        iotaCertsFullIAux r fe depth ty' [] (arg :: rest)
    | _ => pure false
termination_by _ acc args => (args.length, acc.length)
decreasing_by
  · apply Prod.Lex.left; simp
  · apply Prod.Lex.right' <;> simp

/-- Twin of `iotaCertsFull`, at the empty accumulator. -/
def iotaCertsFullI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (ty : Expr) (args : List Expr) : CheckCM Bool :=
  iotaCertsFullIAux r fe depth ty [] args

/-- Twin of `defEqList`. -/
def defEqListI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    List Expr → List Expr → CheckCM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then
      defEqListI r fe depth as bs
    else pure false
  | _, _ => pure false

/-- Twin of `iotaIndexOk` (the canonical-index comparison, only where
the recursor has indices). -/
def iotaIndexOkI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (mI rP cnP : Nat)
    (tyCtor : Expr) (margs idx : List Expr) : CheckCM Bool :=
  if mI = rP then pure true
  else do
    match ← piResidualM tyCtor margs with
    | some residual => do
      let resArgs ← pure (Expr.getAppArgsC residual)
      defEqListI r fe depth (resArgs.drop cnP) idx
    | none => pure false

/-- Twin of `defeqSpine`. -/
def defeqSpineI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  match Expr.getAppFn a with
  | .const n us =>
    match Expr.getAppFn b with
    | .const n' us' => do
      let aargs ← pure (Expr.getAppArgsC a)
      let bargs ← pure (Expr.getAppArgsC b)
      if n = n' ∧ aargs.length = bargs.length then
        match ← isEquivListLM us us' with
        -- last to first, as the spec (official `is_def_eq_args`)
        | some true => defEqListI r fe depth aargs.reverse bargs.reverse
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `proofIrrel`. -/
def proofIrrelI (r : CoreFnsI) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  let ta ← r.inferIO depth a
  let tta ← r.inferIO depth ta
  let wtta ← r.whnf depth tta
  match wtta with
  | .sort uT => do
    let z ← pure .zero
    let okA ← liftFueled "level comparison" (← isEquivLM uT z)
    let tb ← r.inferIO depth b
    let ttb ← r.inferIO depth tb
    let wttb ← r.whnf depth ttb
    match wttb with
    | .sort vT => do
      let z ← pure .zero
      let okB ← liftFueled "level comparison" (← isEquivLM vT z)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/- Task #172 batch B2 — **THE BODY TEMPLATE'S PARAMETER** (the mode
itself since task #185).  Every configured body below takes
`mode : CheckMode` and is instantiated at the two named concrete cores
at the end of this module (`…PC` at `.verified`, `…TC` at `.trusted`;
the `…RC` half retired with the R core, 2026-09-05).  Every read below
is one of the `CheckMode` functions of `ConLeche/Kernel/Env.lean`, each
a `match` on the enum.  The ι cone (`majorToCtorI` → `prepareMajorI`
→ `iotaRecI`) reads the mode through `certAtI`. -/
variable (mode : CheckMode)

/-! ### The certificate-family switch (the twin's retirement, 2026-09-06)

The certificate families — the task-#76 skip list: work the
reference kernel does not run and only the soundness proof consumes —
are gated by `CheckMode.verifiedChecks` (`ConLeche/Kernel/Env.lean`).
Every such certificate below is spelled through the wrapper here, so
the list of `certAtI` sites **is** the
list of what the trusted core omits beyond group A.  At `.verified`
the mode function is `true`, so `certAtI .verified c` is `c` by `rfl`
(`certAtI_verified`); the simulation tower
(`ConLeche/Verify/Cached/*`), stated under `hμ : mode.verifiedChecks =
true`, sees through the wrapper by `certAtI_verified` — the
spec bodies (`ConLeche/Kernel/Core.lean`) gate the same sites directly
(`if mode.verifiedChecks then … else pure true`, `majorToCtor`'s
K/`And` proof-irrelevance checks and `iotaRec`'s case-3 decision), not
through this named wrapper, since `Kernel/*` cannot import `Cached/*`
(the layering fence). -/

/-- Run the certificate `c` when the mode runs the certificate
families; otherwise it is `true` without running. -/
@[inline] def certAtI (mode : CheckMode) (c : CheckCM Bool) : CheckCM Bool :=
  if mode.verifiedChecks then c else pure true

/-- … and at the two modes the wrapper is the certificate or the
constant `true`, by `rfl`. -/
@[simp] theorem certAtI_verified (c : CheckCM Bool) :
    certAtI .verified c = c := rfl

/-- Twin of `propIrrel` (task #168): the hoisted `Prop`-branch test
with both head-symbol arms.  Ungated since 2026-09-06 — the readers
run in both modes, so this body takes no `CheckMode` at all. -/
def propIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  if notProofFast fe.find? fe.findTable? a || notProofFast fe.find? fe.findTable? b then
    pure false
  else if isProofFast fe.find? fe.findTable? a && isProofFast fe.find? fe.findTable? b then
    pure true
  else
  let ta ← r.inferIO depth a
  let tta ← r.inferIO depth ta
  let wtta ← r.whnf depth tta
  match wtta with
  | .sort uT => do
    let z ← pure .zero
    let okA ← liftFueled "level comparison" (← isEquivLM uT z)
    let tb ← r.inferIO depth b
    let ttb ← r.inferIO depth tb
    let wttb ← r.whnf depth ttb
    match wttb with
    | .sort vT => do
      let z ← pure .zero
      let okB ← liftFueled "level comparison" (← isEquivLM vT z)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/-- The `.proj T i b` spine (the tower spelling, task #175
W4c). -/
def projNodesI (T : Name) (b : Expr) : List Nat → CheckCM (List Expr)
  | [] => pure []
  | i :: rest => do
    let r ← pure (Expr.proj T i b)
    let rs ← projNodesI T b rest
    pure (r :: rs)

/-- Twin of `structEtaCertWith`. -/
def structEtaCertWithI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b wtb : Expr) : CheckCM Bool := do
  match Expr.getAppFn a with
  | .const c us => do
    let cn ← pure c
    match fe.find? cn with
    | some (.ctorInfo cvc cnP cnF) => do
      let aargs ← pure (Expr.getAppArgsC a)
      if aargs.length = cnP + cnF then
        match Expr.getAppFn wtb with
        | .const T us' => do
          let Tn ← pure T
          match fe.find? Tn with
          | some (.indInfo cvT caps) => do
            let targs ← pure (Expr.getAppArgsC wtb)
            if caps.eta = true ∧ caps.etaCtor = cn ∧
                reservedBasisNames.contains Tn = false ∧
                reservedBasisNames.contains cn = false ∧
                targs.length = caps.etaParams ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                fe.towerSlotsAllF Tn caps.etaFields = true then do
              if ← liftFueled "level comparison"
                  (← isEquivListLM us us') then do
                -- no type-application certificate (task #342 L11b)
                if ← defEqListI r fe depth
                    (aargs.take caps.etaParams) targs then do
                  let projs ← projNodesI T b (List.range caps.etaFields)
                  defEqListI r fe depth (aargs.drop caps.etaParams) projs
                else pure false
              else pure false
            else pure false
          | _ => pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `structEtaCert`. -/
def structEtaCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  -- the constructor-shape gate first (D13), as in the spec
  let sh ← pure (etaCtorShapeC fe a)
  if sh then
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    structEtaCertWithI r fe depth a b wtb
  else pure false

/-- Twin of `structUnitCert`. -/
def structUnitCertI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  match Expr.getAppFn wta with
  | .const T us' => do
    let Tn ← pure T
    match fe.find? Tn with
    | some (.indInfo cvT caps) => do
      let targs ← pure (Expr.getAppArgsC wta)
      if caps.unitlike = true ∧
          reservedBasisNames.contains Tn = false ∧
          targs.length = caps.unitParams ∧
          us'.length = cvT.levelParams.length then do
        let tb ← r.inferIO depth b
        let wtb ← r.whnf depth tb
        -- no type-application certificate (task #342 L11b), as
        -- official's `is_def_eq_unit_like`; no ∀ (task #342 L18)
        if wtb.isForallE then pure false else
        r.defeq depth wta wtb
      else pure false
    | _ => pure false
  | _ => pure false

/-- Twin of `etaCert` (the λ's pieces come pre-destructured, as in the
spec). -/
def etaCertI (r : CoreFnsI) (_fe : FEnv) (depth : Nat)
    (ty₁ body₁ : Expr) (b : Expr) :
    CheckCM Bool := do
  if !b.ioNeutral then pure false else
  let tb ← r.inferIO depth b
  let wtb ← r.whnf depth tb
  match wtb with
  | .forallE ty₂ cod₂ => do
    if ← r.defeq depth ty₂ ty₁ then do
      let fv ← pure (Expr.fvar depth ty₁)
      let b₁ ← inst1M body₁ fv
      let ba ← pure (Expr.app b fv)
      unless ← r.defeq (depth + 1) b₁ ba do return false
      -- the η check (task #342, T2; see `etaCert`): the λ body's
      -- full-grade type is the ∀'s codomain at the variable
      if mode.verifiedChecks then do
        let t₁ ← r.infer (depth + 1) b₁
        let t₂ ← inst1M cod₂ fv
        unless ← r.defeq (depth + 1) t₁ t₂ do return false
      pure true
    else pure false
  | _ => pure false

/-- Twin of `stuckIrrel`. -/
def stuckIrrelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  if ← structEtaCertI r fe depth a b then pure true
  else if ← structEtaCertI r fe depth b a then pure true
  else if ← structUnitCertI r fe depth a b then pure true
  else proofIrrelI r depth a b

/-- Twin of `majorToCtor`. -/
def majorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (_recName : Name) (rules : List RecRule) (major : Expr) :
    CheckCM Expr := do
  if ← pure (isCtorAppC fe major) then pure major else
  match rules with
  | [rl] =>
    match fe.find? rl.ctor with
    | some (.ctorInfo cvj cnP _cnF) =>
      match (cvj.type.piResult).getAppFn with
      | .const T _ =>
        match fe.find? T with
        | some (.indInfo cvT caps) =>
          if rl.k = true then do
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
                    -- official `to_cnstr_when_K` fabrication type
                    -- check (arena bad/098_ruleKbad) — runs in both
                    -- modes; `proofIrrelI`, a certificate family
                    -- (official stops at the type check), is off at
                    -- `.trusted`
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
          else if rl.eta = true then do
            let tmaj₀ ← r.inferIO depth major
            let tmaj ← r.whnf depth tmaj₀
            match Expr.getAppFn tmaj with
            | .const T' ust => do
              let margs ← pure (Expr.getAppArgsC tmaj)
              let ustL ← pure ust
              -- instantiated non-Prop guard, as in the spec body
              -- `majorToCtor` (task #61)
              -- and the η law's keys, as in the spec body
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
                -- no certificate on the fabricated spine (task #342 L11b)
                if ← pure (Expr.wscopedBC depth fab &&
                    Expr.looseBVarsBounded 0 fab &&
                    Expr.leafGuard fab major) then
                  pure fab
                else pure major
              else pure major
            | _ => pure major
          else if T = andName then do
            -- the `And`-only rescue, as in the spec body
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
          else pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major
  | _ => pure major

/-- Twin of `litMajorToCtor`. -/
def litMajorToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    CheckCM Expr := do
  match e with
  | .lit (.strVal s) =>
    if strLitSupportedF fe then do
      let x ← pure (strLitToConstructor s)
      r.whnf depth x
    else pure e
  | _ => litToCtorIfNatI fe e

/-- Twin of `projLitToCtor`. -/
def projLitToCtorI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    CheckCM Expr := do
  match e with
  | .lit (.strVal s) =>
    if strLitSupportedF fe then do
      let x ← pure (strLitToConstructor s)
      r.whnf depth x
    else pure e
  | _ => pure e

/-- Twin of `prepareMajor`: the major's preparation (K rescue on the
raw major; task #334 — no `whnf` either way after it: if it produced a
constructor, only the literal conversion follows; if it failed, the
major is left exactly as it is; elsewhere the structure rescues on the
raw major first (lean4#15351, task #342 R2), and only if they produce
no constructor whnf, literal, rescue).  The K flag is the single rule's
stored bit, as in the spec (`recRuleK`). -/
def prepareMajorI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : Expr) :
    CheckCM Expr := do
  if recRuleK rules then do
    let majorK ← majorToCtorI mode r fe depth recName rules major
    if isCtorAppC fe majorK then
      litMajorToCtorI r fe depth majorK
    else pure majorK
  else do
    let majorE ← if major.isStrLit then pure major
      else majorToCtorI mode r fe depth recName rules major
    if isCtorAppC fe majorE then pure majorE
    else do
      let major₀ ← r.whnf depth majorE
      let major₁ ← litMajorToCtorI r fe depth major₀
      majorToCtorI mode r fe depth recName rules major₁

/-- The nested-rule pin instantiations (structural recursion;
the spec side is `(recFireComparands …).2`'s `List.map`). -/
def pinArgsI (lps : List Name) (us : List Level) (args : List Expr)
    (t : Nat) : List Expr → CheckCM (List Expr)
  | [] => pure []
  | p :: ps => do
    let praw ← pure p
    let pi ← instLevelParamsM lps us praw
    let r ← instSpineM args t pi
    let rs ← pinArgsI lps us args t ps
    pure (r :: rs)

/-- The length of an application spine, without building its argument
list. -/
def iotaNumArgs : Expr → Nat → Nat
  | .app f _, n => iotaNumArgs f (n + 1)
  | _, n => n

/-- The arity pre-check of the ι step: `iotaRecI` returns `none`
unless the head is a stored recursor applied to exactly `majorIdx + 1`
arguments with the recursor's own number of levels
(`iotaRecI_of_arityOk_false`).  The whnf spine loop asks this before
every ι attempt, which is allocation-free where the ι step's own guard
would first materialise the argument list. -/
def iotaArityOk (fe : FEnv) (e : Expr) : Bool :=
  match Expr.getAppFn e with
  | .const c us =>
    match fe.find? c with
    | some (.recInfo cv mI _ _) =>
      iotaNumArgs e 0 == mI + 1 && us.length == cv.levelParams.length
    | _ => false
  | _ => false

/-- Twin of `iotaRec`. -/
def iotaRecI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) := do
  match Expr.getAppFn e with
  | .const c us => do
    let cn ← pure c
    match fe.find? cn with
    | some (.recInfo cv mI rP rules) => do
      let args ← pure (Expr.getAppArgsC e)
      -- checker change #9 (twin of `Core.lean`'s `iotaRec`): guard the
      -- recursor's level arity before the rule's RHS is instantiated.
      if args.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
          (Expr.peelPis (mI + 1) cv.type).isSome = true then do
        let bvar0 ← pure (Expr.mkBvar 0)
        let major ← prepareMajorI mode r fe depth cn rules (args.getD mI bvar0)
        match Expr.getAppFn major with
        | .const cj usj => do
          let cjn ← pure cj
          match fe.find? cjn with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cjn) with
            | some rl => do
              let margs ← pure (Expr.getAppArgsC major)
              if margs.length = rl.ctorParams + rl.nfields then do
                -- (the ι batch: the two `stripPis` pins are gone — see
                -- the spec's `iotaRec`)
                --
                -- ONE certificate family (task #342 L10, S5c; official's
                -- `inductive_reduce_rec` checks nothing of the major's
                -- constructor), so the whole block is what `.trusted`
                -- omits: at a case-3 redex — not K, the constructor's
                -- family may be `Prop` at the comparand levels (plain: the
                -- recursor's levels; nested: the stored major-domain
                -- instantiation) — the constructor's levels and parameters
                -- against the comparands (the parameter comparands, plain:
                -- the recursor's leading arguments; nested: the stored
                -- pins at them), the constructor telescope at the FULL
                -- grade and the canonical-index comparison (which exists
                -- only where indices do — the spec's `iotaRec`).  The
                -- recursor's spine is never certified (task #349); the
                -- types are looked up only where a certificate consumes
                -- them (DESIGN.md, "CORET RETIRED", inversion 22).
                if ← certAtI mode (do
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
                    else pure true) then do
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
  | _ => pure none

/-- Twin of `projCert`, through the index. -/
def projCertF (fe : FEnv) (c : Name) (args : List Expr) : Bool :=
  match fe.find? c with
  | some (.ctorInfo cvC _ _) => teleArityOk cvC.type args
  | _ => false

/-- Twin of `projCertAt`. -/
def projCertAtF (fe : FEnv) (verified : Bool) (c : Name) (args : List Expr) :
    Bool :=
  if verified then projCertF fe c args else true

/-- Twin of `reduceProjCore`. -/
def reduceProjCoreI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (sn : Name)
    (i : Nat) (c : Expr) : CheckCM (Option Expr) := do
  let e' ← projLitToCtorI r fe depth c
  let snn ← pure sn
  match fe.findProj? snn i with
  | some entry =>
    match Expr.getAppFn e' with
    | .const k us => do
      let args ← pure (Expr.getAppArgsC e')
      if (← pure (k == entry.ctor)) ∧ i < entry.numFields ∧
          args.length = entry.numParams + entry.numFields ∧
          us.length = entry.levelParams.length ∧
          entry.fireOk us = true then do
        let bvar0 ← pure (Expr.mkBvar 0)
        let arg := args.getD (entry.numParams + i) bvar0
        -- task #100 de-gating / task #175 W6 / `projCertAt`: see the
        -- spec `reduceProjCore`
        if projCertAtF fe mode.verifiedChecks k args then
          pure (some arg)
        else pure none
      else pure none
    | _ => pure none
  | none => pure none

/-- Peel loop of `whnfAppI`: `t` is the raw (unsubstituted) lambda body
after the binders consumed so far, `acc` their arguments (innermost
first).  The body is substituted once, when peeling stops, and handed
to the loop together with the arguments left over. -/
def betaPeelI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Expr → List Expr → List Expr → CheckCM WhnfStep
  | t, acc, [] => do
    let e' ← instListM t acc
    pure (.cont e')
  | t, acc, a :: rest => do
    match t with
    | .lam _ body =>
        -- Task #342 S0: uniform β (see `whnfAppI`)
        betaPeelI r fe depth body (a :: acc) rest
    | _ => do
      let e' ← instListM t acc
      let e'' ← mkAppNM e' (a :: rest)
      pure (.cont e'')

/-- Bulk-beta argument loop (task #50): consume the whole application
spine against the whnf'd head `v`.  A lambda head enters the peel loop
(first binder inline, which keeps the argument count decreasing);
other heads try iota with one more argument and otherwise accumulate a
stuck application — the per-level `whnfCoreBody` app clauses, with the
chained per-argument `instantiate1` of the beta path replaced by one
bulk substitution per peeled group (`ConLeche/Verify/BetaSpine.lean`
proves the identification).  A fired ι hands the loop its reduct
applied to the rest of the spine (`WhnfStep.cont`, task #342 R2): the
loop, not a nested call, continues with it. -/
def whnfAppI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Expr → List Expr → CheckCM WhnfStep
  | v, [] => pure (.done v)
  | v, a :: rest => do
    match v with
    | .lam _ body =>
        -- Task #342 S0: uniform β, no certificate, at every λ
        betaPeelI r fe depth body [a] rest
    | _ => do
      let fa ← pure (Expr.app v a)
      -- the ι step is tried only where it could fire; every other
      -- prefix of the spine returns `none` by `iotaRecI`'s own guard
      match ← (if iotaArityOk fe fa then iotaRecI mode r fe depth fa
               else pure none) with
      | some e'' => do
        let e' ← mkAppNM e'' rest
        pure (.cont e')
      | none => whnfAppI r fe depth fa rest

/-- One head-normalization step of `whnfCoreBody` (beta, iota,
projection), returning the head normal form or the term to continue
with; `cheap` is the official `cheap_proj` flag (see `whnfCoreBody`).
Only the spine head's normalization stays a knot call (genuine
nesting, bounded by the term's depth); every *reduction* step is
iteration, so a chain no longer charges the shared recursion-depth
budget one unit per step (task #106 — that is what made the
`Nat.brecOn` grind of `Std.Time…toDays._proof_1` exhaust
`checkFuel`).  `@[inline]` (a compiler attribute): inlined into
`whnfCoreLoopI`, whose continuation is then its own tail call. -/
@[inline] def whnfCoreStepI (r : CoreFnsI) (fe : FEnv) (cheap : Bool) (depth : Nat)
    (e : Expr) : CheckCM WhnfStep := do
    match e with
    | .sort _ | .fvar .. | .forallE ..
    | .lam .. | .const .. | .lit _ => pure (.done e)
    | .app _ _ => do
      -- Bulk beta (task #50): normalize the spine head once and run the
      -- argument loop over the whole spine, batching consecutive
      -- lambda binders into one substitution.
      let h ← pure (Expr.getAppFn e)
      let args ← pure (Expr.getAppArgsC e)
      let v ← r.whnfCore cheap depth h
      whnfAppI mode r fe depth v args
    | .proj sn i pe => do
      -- the scrutinee by `whnf`, or by the cheap `whnfCore` in the
      -- cheap mode; stuck: the input itself, scrutinee as it was (see
      -- `whnfCoreBody`)
      let c ← if cheap then r.whnfCore true depth pe else r.whnf depth pe
      match ← reduceProjCoreI mode r fe depth sn i c with
      | some m' => pure (.cont m')
      | none => pure (.done e)
    | .letE _ v b => do
      -- Task #342 S0: ζ, Lean's way (lets are stored as Lean stores them)
      let e' ← inst1M b v
      pure (.cont e')
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")

/-- Iterate `whnfCoreStepI` on its own step budget (pure mirror:
`whnfCoreLoopM`, `ConLeche/Verify/BetaSpine.lean`).  The continuation
is a self tail call, compiled to a jump (task #342 R2): a reduction
chain of any length runs in constant native stack, and a
non-terminating one runs until the external timeout. -/
def whnfCoreLoopI (r : CoreFnsI) (fe : FEnv) (cheap : Bool) (depth : Nat) :
    Nat → Expr → CheckCM Expr
  | 0, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e => do
    match ← whnfCoreStepI mode r fe cheap depth e with
    | .done v => pure v
    | .cont e' => whnfCoreLoopI r fe cheap depth n e'

/-- Twin of `whnfCoreBody`: the head-normalization loop at its own step
budget. -/
def whnfCoreBodyI (r : CoreFnsI) (fe : FEnv) : Bool → Nat → Expr → CheckCM Expr :=
  fun cheap depth e => whnfCoreLoopI mode r fe cheap depth whnfCoreLoopFuel e

/-- Twin of `defeqArg`: an `eagerReduce _ _` argument's type is
compared in the eager tower. -/
@[inline] def defeqArgI (r : CoreFnsI) (depth : Nat) (a ta ty : Expr) : CheckCM Bool :=
  if Expr.isEagerReduce a then r.defeqE depth ta ty else r.defeq depth ta ty

/-- Application-inference spine loop (task #50): walk the raw
Π-telescope against the arguments with deferred substitution — each
argument's certificate substitutes only its *domain*; the codomain is
substituted once per peeled group.  A non-syntactic telescope step
substitutes and normalizes, exactly like the chained `inferBody`
recursion (`ConLeche/Verify/BetaSpine.lean` proves the
identification). -/
def inferSpineI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ty with
    | .forallE dom body => do
      -- the per-argument check, unconditional at the full grade, as
      -- in the spec body `inferBody`
      let dom' ← instListRevM dom acc
      let ta ← r.infer depth a
      unless ← defeqArgI r depth a ta dom' do
        throw (.invalid "application type mismatch")
      inferSpineI r fe depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match w with
      | .forallE dom body => do
        let ta ← r.infer depth a
        unless ← defeqArgI r depth a ta dom do
          throw (.invalid "application type mismatch")
        inferSpineI r fe depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- **The io-grade spine walk**: `inferBodyIO`'s app clause
(`ConLeche/Kernel/Core.lean`) in the bulk telescope form — official's
`infer_only`: the function's type is walked through the arguments with
no argument inference and no domain comparison (task #342).  A
syntactic `.forallE` is its own whnf; anything else is instantiated and
whnf'd before the next step. -/
def inferSpineIOI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ty with
    | .forallE _ body => do
      inferSpineIOI r fe depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match w with
      | .forallE _ body => do
        inferSpineIOI r fe depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- Twin of `whnfStep`.  `@[inline]` (a compiler attribute; the term
is unchanged): inlined into `whnfLoopI`, the continuation call becomes
the loop's own tail call, which the compiler turns into a jump, so a
δ chain of any length runs in constant native stack (task #342 R2: a
non-terminating δ chain — Coquand's paradox — runs until the external
timeout instead of overflowing the stack). -/
@[inline] def whnfStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Expr → CheckCM Expr) (e : Expr) : CheckCM Expr := do
  let e₁ ← r.whnfCore false depth e
  match ← reduceNatI r fe depth e₁ with
  | some e₂ => k e₂
  | none =>
    match ← unfoldDefinitionI fe e₁ with
    | some e₂ => k e₂
    | none => pure e₁

/-- Twin of `whnfLoop`. -/
def whnfLoopI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → Expr → CheckCM Expr
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStepI r fe depth (whnfLoopI r fe depth n) e

/-- Twin of `whnfBody`. -/
def whnfBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => whnfLoopI r fe depth whnfLoopFuel e

/-- Twin of `ensureSort` (returns the level; no readback needed). -/
def ensureSortI (r : CoreFnsI) (depth : Nat) (e : Expr) : CheckCM Level := do
  let w ← r.whnf depth e
  match w with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-! ### Binder-telescope loops (task #72)

The official-kernel discipline (lean4lean's `inferLambda`/`inferForall`
loops): peel a whole binder telescope accumulating opened free
variables, substituting only each binder's *domain* on the way in
(domains are small; `instListM` against the accumulator), infer the
leaf once on the bulk-opened body, then rebuild with one
`abstractRange` per domain and one over the leaf.  Each loop replays
exactly the per-binder checks of the chained recursion, in order; the
value-level identification with the chained spec bodies is
`ConLeche/Verify/BinderLoop.lean` (`Verify/Cached/BinderLoopC.lean` relates the loops to
their pure mirrors, and `_sound` theorems reproduce a mirror run
in the original one-binder-at-a-time body at some fuel).
The peel fuel is semantically transparent: on exhaustion the leaf phase hands
the residual binder chain back to the knot, which is exactly the
chained spec's next step. -/

/-- Rebuild loop of `inferLamsI`: fold the stack (innermost binder
first, `j` its binder level relative to the ambient depth `d`).  The
intermediate `∀`-node inferences of the chained body are
value-determined by the peel phase's domain sorts and the leaf phase's
body-type sort and cannot fail. -/
def inferLamsOutI (d : Nat) :
    List Expr → Nat → Expr → CheckCM Expr
  | [], _j, cur => pure cur
  | tyo :: rest, j, cur => do
    let tyAbs ← abstractRangeM tyo d j
    let node ← pure (Expr.forallE tyAbs cur)
    inferLamsOutI d rest (j - 1) node

/-- Leaf phase of `inferLamsI`: bulk-open the residual body, infer it,
then rebuild outward.

Task #152: at the verified modes the chain's body type is
sort-checked here — the spec's codomain check (`inferBody`'s `.lam`
clause), which fires at the innermost binder of a λ-chain, i.e.
exactly when the peel stops on a non-λ residual.  The guard is the
same one the spec uses, on the same term. -/
def inferLamsLeafI (r : CoreFnsI) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Expr) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  let cur ← abstractRangeM bt d k
  inferLamsOutI d stk (k - 1) cur

/-- λ-telescope inference loop (task #72; used by `inferBodyI`'s and
`inferBodyIOI`'s lam cases): peel the raw λ-chain, checking each opened
domain to be a type on the way in.  `k` counts the opened binders
(`≥ 1`: the caller peels the first binder inline), `fvs` their free
variables innermost-first. -/
def inferLamsI (r : CoreFnsI) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List Expr → CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match t with
    | .lam ty body => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      let wtty ← r.whnf (d + k) tty
      match wtty with
      | .sort _ => do
        let fv ← pure (Expr.fvar (d + k) tyo)
        inferLamsI r d fuel body (k + 1) (fvs.push fv)
          (tyo :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferLamsLeafI r d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeafI r d t k fvs stk

/-- Rebuild loop of `inferPisI`: fold the accumulated domain sorts by
`imax`, innermost binder first — exactly the chained `∀`-rule's result
value.  The fold reads no per-node datum: a `Level`-keyed lookup here
would miss at every step (a node's key `.imax u v` is new each time),
and a walk down the growing right spine is `O(k²)` in the telescope
depth `k` (task #272, GitHub issue #9: it was 90 % of the check phase
on a ∀ chain of 40 000 binders). -/
def inferPisOutI : List Level → Level → CheckCM Level
  | [], v => pure v
  | u :: rest, v => do
    let v' ← pure (.imax u v)
    inferPisOutI rest v'

/-- Leaf phase of `inferPisI`: bulk-open the residual body, infer its
sort, then fold the domain sorts outward. -/
def inferPisLeafI (r : CoreFnsI) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Level) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← r.infer (d + k) ob
  let wbt ← r.whnf (d + k) bt
  match wbt with
  | .sort v => do
    let iv ← inferPisOutI stk v
    pure (Expr.sort iv)
  | _ => throw (.invalid "expected a sort")

/-- ∀-telescope inference loop (task #100 stage 6: the `∀`-rule infers
its codomain sort): peel the raw
∀-chain, checking each opened domain to be a type on the way in and
accumulating its sort, infer the bulk-opened leaf's sort once, and
fold `imax` outward. -/
def inferPisI (r : CoreFnsI) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List Level →
      CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match t with
    | .forallE ty body => do
      let tyo ← instListRevM ty fvs
      let tty ← r.infer (d + k) tyo
      let wtty ← r.whnf (d + k) tty
      match wtty with
      | .sort u => do
        let fv ← pure (Expr.fvar (d + k) tyo)
        inferPisI r d fuel body (k + 1) (fvs.push fv)
          (u :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferPisLeafI r d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeafI r d t k fvs stk

/-- Twin of `inferBody`. -/
def inferBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => do
    match e with
    | .sort u => do
      let su ← pure (.succ u)
      pure (Expr.sort su)
    | .fvar idx ty =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | .const n us => do
      let nm ← pure n
      match fe.find? nm with
      | none => throw (unknownConstError nm)
      | some ci =>
        -- Task #368: `inferBody`'s twin
        if bvNativeStub ci then throw (.notImplemented (bvNativeUseMsg nm))
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {nm}")
        constTyAtM fe n nm us
    | .lit (.natVal _) => do
      if natLitSupportedF fe then do
        let ni ← pure natName
        pure (Expr.const ni [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if strLitSupportedF fe then do
        let si ← pure stringName
        pure (Expr.const si [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body => do
      -- Binder-telescope loop (task #72 discipline; the codomain sort
      -- is inferred).
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match wtty with
      | .sort u => do
        let fv ← pure (Expr.fvar depth ty)
        let fuel ← peelFuelM
        inferPisI r depth fuel body 1 #[fv] [u]
      | _ => throw (.invalid "expected a sort")
    | .lam ty body => do
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match wtty with
      | .sort _ => do
        -- Binder-telescope loop (task #72): peel the whole λ-chain,
        -- open in bulk, rebuild with `abstractRange`.
        let fv ← pure (Expr.fvar depth ty)
        let fuel ← peelFuelM
        inferLamsI r depth fuel body 1 #[fv] [ty]
      | _ => throw (.invalid "expected a sort")
    | .app _ _ => do
      -- Bulk telescope consumption (task #50): infer the spine head
      -- once and walk its Π-telescope against the whole spine.
      let h ← pure (Expr.getAppFn e)
      let args ← pure (Expr.getAppArgsC e)
      -- Task #368: `inferBody`'s `U E C a` case
      let tf ← r.infer depth h
      match bvUnsatSpine h args with
      | some (E, C, a, rest) => do
        -- `U E C`'s type as the spec infers it, then `a`'s check skipped
        -- where the gate accepts (the spec's `bvUnsatSkip`)
        let t1 ← inferSpineI r fe depth tf #[] [E, C]
        let w ← r.whnf depth t1
        match w with
        | .forallE _ body =>
          if bvUnsatSkip fe.find? fe.findProj? (.app (.app h E) C) a body then
            inferSpineI r fe depth (body.instantiate1 a) #[] rest
          else inferSpineI r fe depth tf #[] args
        | _ => inferSpineI r fe depth tf #[] args
      | none =>
      inferSpineI r fe depth tf #[] args
    | .proj sn i pe => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match Expr.getAppFn te with
      | .const T us => do
        let Tn ← pure T
        match fe.findProj? Tn i with
        | some entry => do
          let targs ← pure (Expr.getAppArgsC te)
          -- the node names the subject type's head, at its arity
          -- (official `infer_proj`)
          unless T = sn do
            throw (.invalid "invalid projection: the node names another structure")
          unless targs.length = entry.numParams do
            throw (.invalid "projection parameter mismatch")
          if us.length = entry.levelParams.length then do
            -- the official `infer_proj` restriction (task #175
            -- W4c/O4), as in the spec body
            if Level.isEquiv entry.structSort .zero == some true then
              unless Level.isEquiv
                  (Level.subst entry.levelParams us entry.fieldSort) .zero
                  == some true do
                throw (.invalid
                  "projection from a propositional structure must be a proposition")
            -- the body at the arguments and the subject, as in the
            -- spec body (task #175 S1) — through the memoized,
            -- sharing-preserving `Expr` instantiations
            -- (`ProjEntry.typeAtI`; the spec's `typeAt` is a tree walk
            -- that copied the subject and the parameters — the affine
            -- frontier's out-of-memory, DESIGN.md "The affine frontier")
            pure (entry.typeAtI us targs pe)
          else throw (.notImplemented "projection without a native entry")
        | none =>
          throw (projMissError fe.find? (fe.findTable? Tn).isSome Tn sn i
            (Expr.getAppArgsC te).length)
      | _ => throw (.invalid "invalid projection: not a structure-like type, or no such field")
    | .letE ty v b => do
      -- official `infer_let`: the `let`'s type is a type, the value's
      -- type matches it, then the body with the value substituted —
      -- the ζ reduct, as Lean's kernel infers it
      let tty ← r.infer depth ty
      let _ ← ensureSortI r depth tty
      let tv ← r.infer depth v
      unless ← r.defeq depth tv ty do
        throw (.invalid "let value type mismatch")
      let ob ← inst1M b v
      r.infer depth ob
    | .bvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- **The io-grade inference body** (task #172 B4): `inferBodyI` with
the application, ∀, λ and `let` clauses changed — the spine walk is
`inferSpineIOI` (no argument check), the binder clauses are chained
(the λ's runs no domain-sort check) and the `let` clause checks
neither the type nor the value, as `inferBodyIO` does.  Every other
view dispatches to `inferBodyI`'s own clause.
Recursion grade is the record's: the knot ties this body to
`CoreFnsI.ioView`, so `r.infer` here is the io slot one level down —
the grade propagates exactly as official's `infer_only` does. -/
def inferBodyIOI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → CheckCM Expr :=
  fun depth e => do
    match e with
    | .app _ _ => do
      let h ← pure (Expr.getAppFn e)
      let args ← pure (Expr.getAppArgsC e)
      let tf ← r.infer depth h
      inferSpineIOI r fe depth tf #[] args
    | .forallE ty body => do
      -- the pure io ∀ clause, **chained** (deliberately not the
      -- task-#72 telescope loop: the loops are the front door's
      -- optimization, and looping the io lane would owe the whole
      -- loop-identification walk family a second, io-graded instance
      -- for a lane whose subjects are internal re-inferences —
      -- recorded in the B4 seal as a measured-need follow-up)
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match wtty with
      | .sort u => do
        let fv ← pure (Expr.fvar depth ty)
        let ob ← inst1M body fv
        let bt ← r.infer (depth + 1) ob
        let v ← ensureSortI r (depth + 1) bt
        let iu ← pure (.imax u v)
        pure (Expr.sort iu)
      | _ => throw (.invalid "expected a sort")
    | .lam ty body => do
      -- the pure io λ clause, chained; no domain-sort run (task #168
      -- stage 2, as in the spec)
      let fv ← pure (Expr.fvar depth ty)
      let ob ← inst1M body fv
      let bt ← r.infer (depth + 1) ob
      let bAbs ← abstract1M bt depth
      pure (Expr.forallE ty bAbs)
    | .letE _ v b => do
      -- official `infer_let` at `infer_only`: the body at its value,
      -- no check of the type or the value (task #342 R-C)
      let ob ← inst1M b v
      r.infer depth ob
    | _ => inferBodyI r fe depth e

/-- Twin of `boolTrueShortcut`. -/
def boolTrueShortcutI (r : CoreFnsI) (depth : Nat) (a : Expr) : CheckCM Bool := do
  let w ← r.whnf depth a
  pure (Expr.isBoolTrue w)

/-- Twin of `defeqLamsInner`. -/
def defeqLamsInnerI (r : CoreFnsI) (depth : Nat) (b₁ b₂ : Expr) : CheckCM Bool := do
  unless ← r.defeq (depth + 1) b₁ b₂ do return false
  if mode.verifiedChecks then do
    let t₁ ← r.infer (depth + 1) b₁
    let t₂ ← r.infer (depth + 1) b₂
    unless ← r.defeq (depth + 1) t₁ t₂ do return false
  pure true

/-- Twin of `defeqLams`. -/
def defeqLamsI (r : CoreFnsI) :
    Nat → Nat → Expr → Expr → Expr → Expr → CheckCM Bool
  | fuel, depth, ty₁, body₁, ty₂, body₂ => do
    unless ← r.defeq depth ty₁ ty₂ do return false
    let fv ← pure (Expr.fvar depth ty₂)
    let b₁ ← inst1M body₁ fv
    let b₂ ← inst1M body₂ fv
    match fuel, Expr.lamPair? b₁ b₂ with
    | fuel + 1, some (ty₁', body₁', ty₂', body₂') =>
      if b₁ == b₂ then pure true
      else defeqLamsI r fuel (depth + 1) ty₁' body₁' ty₂' body₂'
    | _, _ => defeqLamsInnerI mode r depth b₁ b₂

/-- Twin of `quickDefEq`. -/
def quickDefEqI (r : CoreFnsI) (depth : Nat) (a b : Expr) :
    CheckCM (Option Bool) :=
  if a == b then pure (some true) else
  match a, b with
  | .sort u, .sort v => do
    let ok ← liftFueled "level comparison" (← isEquivLM u v)
    pure (some ok)
  | .lit l₁, .lit l₂ => pure (some (l₁ == l₂))
  | .forallE ty₁ body₁, .forallE ty₂ body₂ => do
    unless ← r.defeq depth ty₁ ty₂ do return some false
    let fv ← pure (Expr.fvar depth ty₂)
    let b₁ ← inst1M body₁ fv
    let b₂ ← inst1M body₂ fv
    unless ← r.defeq (depth + 1) b₁ b₂ do return some false
    pure (some true)
  | .lam ty₁ body₁, .lam ty₂ body₂ => do
    let ok ← defeqLamsI mode r lamsFuel depth ty₁ body₁ ty₂ body₂
    pure (some ok)
  | _, _ => pure none

/-- Twin of `defeqOffset`. -/
def defeqOffsetI (r : CoreFnsI) (depth : Nat) (a b : Expr) :
    CheckCM (Option Bool) :=
  if a.isNatZero && b.isNatZero then pure (some true) else
  if a.isLit && b.isLit then pure none else
  match a.natPred?, b.natPred? with
  | some x, some y => do
    let ok ← r.defeq depth x y
    pure (some ok)
  | _, _ => pure none

/-- Twin of `tryUnfoldProjApp`. -/
def tryUnfoldProjAppI (r : CoreFnsI) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) :=
  if Expr.headIsProj e then do
    let e' ← r.whnfCore false depth e
    if e' == e then pure none else pure (some e')
  else pure none

/-- Twin of `deltaQuick`. -/
def deltaQuickI (r : CoreFnsI) (depth : Nat) (a b : Expr) : CheckCM DeltaStep := do
  match ← quickDefEqI mode r depth a b with
  | some true => pure .eq
  | some false => pure .diff
  | none => pure (.cont a b)

/-- Twin of `lazyDeltaStep`. -/
def lazyDeltaStepI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM DeltaStep := do
  match ← pure (unfoldableHeadC fe a), ← pure (unfoldableHeadC fe b) with
  | false, false => pure .unknown
  | true, false =>
    match ← tryUnfoldProjAppI r depth b with
    | some b₂ => deltaQuickI mode r depth a b₂
    | none =>
      match ← unfoldDefinitionI fe a with
      | some a₂ => do
        let a₃ ← r.whnfCore true depth a₂
        deltaQuickI mode r depth a₃ b
      | none => pure .unknown
  | false, true =>
    match ← tryUnfoldProjAppI r depth a with
    | some a₂ => deltaQuickI mode r depth a₂ b
    | none =>
      match ← unfoldDefinitionI fe b with
      | some b₂ => do
        let b₃ ← r.whnfCore true depth b₂
        deltaQuickI mode r depth a b₃
      | none => pure .unknown
  | true, true => do
    let ha ← pure (headHintC fe a)
    let hb ← pure (headHintC fe b)
    if ReducibilityHint.lt hb ha then
      match ← unfoldDefinitionI fe a with
      | some a₂ => do
        let a₃ ← r.whnfCore true depth a₂
        deltaQuickI mode r depth a₃ b
      | none => pure .unknown
    else if ReducibilityHint.lt ha hb then
      match ← unfoldDefinitionI fe b with
      | some b₂ => do
        let b₃ ← r.whnfCore true depth b₂
        deltaQuickI mode r depth a b₃
      | none => pure .unknown
    else if ← (if ReducibilityHint.sameRegular ha hb &&
        (← pure (sameConstHeadsC a b)) then
        defeqSpineI r fe depth a b else pure false) then pure .eq
    else
      match ← unfoldDefinitionI fe a, ← unfoldDefinitionI fe b with
      | some a₂, some b₂ => do
        let a₃ ← r.whnfCore true depth a₂
        let b₃ ← r.whnfCore true depth b₂
        deltaQuickI mode r depth a₃ b₃
      | _, _ => pure .unknown

/-- Twin of `lazyDeltaReduction`. -/
def lazyDeltaReductionI (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → Expr → Expr → CheckCM LazyRes
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | n + 1, a, b => do
    match ← defeqOffsetI r depth a b with
    | some v => pure (.verdict v)
    | none =>
    -- the eager flag (task #353) folds with free variables present
    let fold ← pure (mode.eager || (!Expr.hasFvar a && !Expr.hasFvar b))
    match ← (if fold then reduceNatI r fe depth a else pure none) with
    | some a₂ => do
      let v ← r.defeq depth a₂ b
      pure (.verdict v)
    | none =>
    match ← (if fold then reduceNatI r fe depth b else pure none) with
    | some b₂ => do
      let v ← r.defeq depth a b₂
      pure (.verdict v)
    | none =>
    match ← lazyDeltaStepI mode r fe depth a b with
    | .cont a' b' => lazyDeltaReductionI r fe depth n a' b'
    | .eq => pure (.verdict true)
    | .diff => pure (.verdict false)
    | .unknown => pure (.unknown a b)

/-- Twin of `lazyDeltaProjReduction`. -/
def lazyDeltaProjReductionI (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (sn : Name) (i : Nat) : Nat → Expr → Expr → CheckCM Bool
  | 0, _, _ => throw (.internal "fuel exhausted: lazy delta projection loop")
  | n + 1, a, b => do
    match ← lazyDeltaStepI mode r fe depth a b with
    | .cont a' b' => lazyDeltaProjReductionI r fe depth sn i n a' b'
    | .eq => pure true
    | .diff | .unknown =>
      match ← reduceProjCoreI mode r fe depth sn i a with
      | some x =>
        match ← reduceProjCoreI mode r fe depth sn i b with
        | some y => r.defeq depth x y
        | none => r.defeq depth a b
      | none => r.defeq depth a b

/-- Twin of `defeqProjPair`. -/
def defeqProjPairI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool :=
  match a, b with
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ =>
    if s₁ == s₂ && i₁ == i₂ then
      lazyDeltaProjReductionI mode r fe depth s₁ i₁ defeqLoopFuel e₁ e₂
    else pure false
  | _, _ => pure false

/-- Twin of `defeqStuck`. -/
def defeqStuckI (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : Expr) :
    CheckCM Bool :=
  match a, b with
  | .lit l, .app fO _x => do
    match l, fO with
    | .strVal s, .const cO usO =>
      if (← pure (cO == stringOfListName)) ∧ usO = [] ∧ strLitSupportedF fe then do
        let sc ← pure (strLitToConstructor s)
        r.defeq depth sc b
      else stuckIrrelI r fe depth a b
    | _, _ => stuckIrrelI r fe depth a b
  | .app fO _x, .lit l => do
    match l, fO with
    | .strVal s, .const cO usO =>
      if (← pure (cO == stringOfListName)) ∧ usO = [] ∧ strLitSupportedF fe then do
        let sc ← pure (strLitToConstructor s)
        r.defeq depth a sc
      else stuckIrrelI r fe depth a b
    | _, _ => stuckIrrelI r fe depth a b
  | .fvar i _, .fvar j _ =>
    if i == j then pure true
    else stuckIrrelI r fe depth a b
  | .const n us, .const n' us' =>
    if n = n' then do
      if ← liftFueled "level comparison" (← isEquivListLM us us') then
        pure true
      else stuckIrrelI r fe depth a b
    else stuckIrrelI r fe depth a b
  | .app _f₁ _a₁, .app _f₂ _a₂ => do
    -- spine-wise congruence, as in the spec (official `is_def_eq_app`)
    let as₁ ← pure (Expr.getAppArgsC a)
    let as₂ ← pure (Expr.getAppArgsC b)
    if as₁.length = as₂.length then do
      let h₁ ← pure (Expr.getAppFn a)
      let h₂ ← pure (Expr.getAppFn b)
      if ← r.defeq depth h₁ h₂ then do
        if ← defEqListI r fe depth as₁ as₂ then pure true
        else stuckIrrelI r fe depth a b
      else stuckIrrelI r fe depth a b
    else stuckIrrelI r fe depth a b
  | .lam ty₁ body₁, _ => do
    if ← etaCertI mode r fe depth ty₁ body₁ b then pure true
    else stuckIrrelI r fe depth a b
  | _, .lam ty₂ body₂ => do
    if ← etaCertI mode r fe depth ty₂ body₂ a then pure true
    else stuckIrrelI r fe depth a b
  | _, _ => stuckIrrelI r fe depth a b

/-- Twin of `defeqBody`. -/
def defeqBodyI (r : CoreFnsI) (fe : FEnv) : Nat → Expr → Expr → CheckCM Bool :=
  fun depth a b => do
    if a == b then pure true else
    -- the eq-true shortcut (E2), as in the spec
    let bt ← pure (Expr.isBoolTrue b)
    let af ← pure (Expr.hasFvar a)
    if ← (if bt && (mode.eager || !af) then boolTrueShortcutI r depth a
        else pure false) then pure true else
    match ← quickDefEqI mode r depth a b with
    | some v => pure v
    | none =>
    -- task #333: proof irrelevance before any head normalization
    if ← propIrrelI r fe depth a b then pure true else
    let a' ← r.whnfCore true depth a
    let b' ← r.whnfCore true depth b
    match ← quickDefEqI mode r depth a' b' with
    | some v => pure v
    | none =>
    match ← lazyDeltaReductionI mode r fe depth defeqLoopFuel a' b' with
    | .verdict v => pure v
    | .unknown a₁ b₁ =>
    if ← defeqProjPairI mode r fe depth a₁ b₁ then pure true else
    if !(Expr.headIsProj a₁) && !(Expr.headIsProj b₁) then
      defeqStuckI mode r fe depth a₁ b₁ else
    let a₂ ← r.whnfCore false depth a₁
    let b₂ ← r.whnfCore false depth b₁
    if a₂ == a₁ && b₂ == b₁ then defeqStuckI mode r fe depth a₁ b₁
    else r.defeq depth a₂ b₂

/-! ## The memoized knot -/

/-- Memoize a unary entry point under its node (`O(1)` key).

`@[inline]` (the retired twin's perf-eng E2, now the one knot's): after
inlining the getter/setter lambdas beta-reduce away and the memo probe
compiles into the record field's own closure.  A compiler attribute
only — the term the proofs unfold is unchanged. -/
@[inline] def memoEI (get' : CState → Std.HashMap Expr Expr)
    (set' : CState → Std.HashMap Expr Expr → CState)
    (f : Nat → Expr → CheckCM Expr) : Nat → Expr → CheckCM Expr :=
  fun d e => do
    match (get' (← get))[e]? with
    | some r => pure r
    | none =>
      let r ← f d e
      modify fun st =>
          let mp := get' st
        let st := set' st ∅
        set' st (mp.insert e r)
      pure r

/-- Memoize the definitional-equality entry point under the
index pair (`@[inline]` as `memoEI`). -/
@[inline] def memoBI (f : Nat → Expr → Expr → CheckCM Bool) :
    Nat → Expr → Expr → CheckCM Bool :=
  fun d a b => do
    match (← get).defeqC[(a, b)]? with
    | some r => pure r
    | none =>
      let r ← f d a b
      modify fun st =>
        let mp := st.defeqC
        let st := { st with defeqC := ∅ }
        { st with defeqC := mp.insert (a, b) r }
      pure r

/-- Tie the bodies at the memoizing state monad (fuel only
here, as in `coreKnot`; levels built lazily).

**The knot takes the mode** (task #185; from 2026-09-06 to then it
took a configuration record standing in for it).  `coreKnotI .verified`
is the verified core the capstones are stated about, and
`coreKnotI .trusted` is the trusted core `--trusted` runs — the same
function at the other mode.  The mode-parametric simulation tower
(`ConLeche/Verify/Cached/*`) is stated at `coreKnotI mode` under
`hμ : mode.verifiedChecks = true`. -/
def coreKnotI (mode : CheckMode) (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      defeqE := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    -- **NOT a `Thunk`** (task #179).  The previous fuel level used to be
    -- `Thunk`-cached (perf-eng E1: built once per record rather than once
    -- per cache-missing call), and that single word cost 13.8 % of
    -- `init-full`.  `lean_thunk_get_core` calls `mark_mt` on the forced
    -- **value** — the runtime's invariant is that a single-threaded object
    -- may not be reachable from a multi-threaded one, and a thunk may be
    -- forced from another thread — so forcing this thunk marked the whole
    -- reachable graph of its value multi-threaded, and the value's six
    -- closures capture `fe`.  Two consequences, both `O(|env|)` per
    -- *declaration*: (i) the mark itself walks the index's whole bucket
    -- array, and (ii) an MT object is never `lean_is_exclusive`, so
    -- `FEnv.push`'s `idx.insert` stopped updating in place and copied the
    -- bucket array (with an atomic `lean_inc` per slot) at every accepted
    -- constant — the two symbols task #177 left unattributed,
    -- `lean_mark_mt` (7.6 %) and `lean_copy_expand_array` (6.2 %).  The
    -- copy re-created the array as single-threaded, the next force marked
    -- it again, and the loop sustained itself.  A plain `Unit`-closure
    -- forces nothing and marks nothing; it pays E1 back (one record per
    -- cache-missing call) and that is the smaller number by 5×.
    -- `Thunk.get ⟨f⟩` is `f ()` by structure eta, so this is the same
    -- term: no proof in `ConLeche/Verify/Cached/*` moved.
    let prev : Unit → CoreFnsI := fun _ => coreKnotI mode fe fuel
    -- task #172 B2 / #185: the template's parameter is the mode, an
    -- enum passed down once per *driver* — nothing is built per knot
    -- level or per call (at B2 a record allocation at every
    -- head-normalization entry cost +0.155 % on `init-prelude`).
    -- The two modes of `whnfCore` (official `cheap_proj`) under two
    -- memos: their results differ on a stuck projection.
    { whnfCore := fun c => if c then
          memoEI (·.whnfCoreCheapC)
            (fun st mp => { st with whnfCoreCheapC := mp })
            (fun d e => whnfCoreBodyI mode (prev ()) fe true d e)
        else memoEI (·.whnfCoreC)
          (fun st mp => { st with whnfCoreC := mp })
          (fun d e => whnfCoreBodyI mode (prev ()) fe false d e)
      whnf := memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI (prev ()) fe d e)
      infer := memoEI (·.inferC) (fun st mp => { st with inferC := mp })
        (fun d e => inferBodyI (prev ()) fe d e)
      defeq := memoBI
        (fun d a b => defeqBodyI mode (prev ()) fe d a b)
      -- **The eager slot** (task #353): the eager tower — the knot at
      -- `mode.toEager` one level down — on its own memos, kept in the
      -- state between eager comparisons (`withEagerMemos`, task #361:
      -- an eager entry never serves a plain query)
      defeqE := fun d a b => withEagerMemos mode
        (memoBI (fun d a b =>
          defeqBodyI mode.toEager (coreKnotI mode.toEager fe fuel) fe d a b) d a b)
      -- **The io slot** (task #170 / #172 B4, task #346): the io body
      -- under its OWN memo (`CState.inferIOC` — the task-#170 memo
      -- ruling: a hit in the io memo never serves a full-infer query),
      -- tied to the io-grade view of the previous level (the grade
      -- propagates)
      inferIO := memoEI (·.inferIOC) (fun st mp => { st with inferIOC := mp })
        (fun d e => inferBodyIOI (prev ()).ioView fe d e) }

end ConLeche.Cached
