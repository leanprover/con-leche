import Setlec.Cached.CoreC

/-!
# The cert-skipping cached core (the `--no-model` cached parity lane)

A twin of the kernel's cert-skipping interned core
(`Setlec/Kernel/CoreNC.lean`) over `ExprC`: **every function below
mirrors its interned NC original clause by clause** — same order of
record calls, same short-circuits, same caches, same loops — with the
arena replaced by the computed-field representation, exactly the way
`Setlec/Cached/CoreC.lean` clones `Setlec/Kernel/CoreI.lean` (the
store wrappers survive as `CStore` no-ops, the interning wrappers as
smart constructors, the name/level interning as identities).  Where an
NC body references a certified helper (`projCertI`, `reduceNatI`,
`unfoldDefinitionI`, `whnfBodyI`, `annotateBodyI`, `ensureSortI`, …)
it uses the `CoreC` twin under the same name.

The task-#76 skip list — which infer/defeq calls are proof-only and
why — is documented once, in `Setlec/Kernel/CoreNC.lean`'s module
docstring; this clone adds no new judgement.  Measurement-only:
nothing in `Setlec/Verify/*` or `Setlec/SetR/*` may import this
module, and none of the consistency statements cover these knots.
Main reaches these bodies only through the `--no-model
--core=cached-parsed` driver (`Setlec/Cached/ParsedNC.lean`).

Representational deltas (each is a `CoreC`-convention substitution,
not a behavioral one): `CheckIM`→`CheckCM`, `EIdx`→`ExprC`,
`LIdx`→`Level`, `IState`→`CState`, and the binder-loop fuel
`withStore (·.nodes.size)`→`peelFuelM` (there is no arena node count;
the fuel is semantically transparent, see `Setlec/Cached/StateC.lean`).
-/

namespace Setlec.Cached

open Setlec

/-- Cert-skipping twin of `inferSpineI` (port of
`Setlec/Kernel/CoreNC.lean`'s `inferSpineNC`): the telescope walk
without the possibly-Prop argument re-checks (references are
infer-only here). -/
def inferSpineNC (r : CoreFnsI) (depth : Nat) :
    ExprC → Array ExprC → List ExprC → CheckCM ExprC
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ← viewI ty with
    | some (.forallE _ _dom body _) =>
      inferSpineNC r depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match ← viewI w with
      | some (.forallE _ _dom body _) =>
        inferSpineNC r depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- Cert-skipping twin of `structEtaCertWithI` (port of
`Setlec/Kernel/CoreNC.lean`'s `structEtaCertWithNC`): keeps the guard,
the level comparison, the parameter comparison and the per-field defeq
against the projections (what lean4lean's `tryEtaStructCore` checks);
skips the type-former and per-projection telescope certifications. -/
def structEtaCertWithNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b wtb : ExprC) : CheckCM Bool := do
  match ← withStore (fun st => st.getNode (st.getAppFnI a)) with
  | some (.const c us) => do
    let cn ← readbackNM c
    match fe.find? cn with
    | some (.ctorInfo cvc cnP cnF) => do
      let aargs ← withStore (·.getAppArgsI a)
      if aargs.length = cnP + cnF then
        match ← withStore (fun st => st.getNode (st.getAppFnI wtb)) with
        | some (.const T us') => do
          let Tn ← readbackNM T
          match fe.find? Tn with
          | some (.indInfo cvT caps) => do
            let targs ← withStore (·.getAppArgsI wtb)
            if caps.eta = true ∧ caps.etaCtor = cn ∧
                caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                reservedBasisNames.contains Tn = false ∧
                reservedBasisNames.contains cn = false ∧
                targs.length = cnP ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                (cvT.type.stripPis cnP).isSome = true then do
              if ← liftFueled "level comparison"
                  (← isEquivListLM us us') then do
                if ← defEqListI r fe depth (aargs.take cnP) targs then do
                  let projs ← projAppsI T us' targs b (List.range cnF)
                  defEqListI r fe depth (aargs.drop cnP) projs
                else pure false
              else pure false
            else pure false
          | _ => pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Cert-skipping twin of `structEtaCertI` (port of
`Setlec/Kernel/CoreNC.lean`'s `structEtaCertNC`). -/
def structEtaCertNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  let tb ← r.infer depth b
  let wtb ← r.whnf depth tb
  structEtaCertWithNC r fe depth a b wtb

/-- Cert-skipping twin of `structUnitCertI` (port of
`Setlec/Kernel/CoreNC.lean`'s `structUnitCertNC`): keeps the unit-like
shape guard and the defeq of the two whnf'd types (what lean4lean's
`isDefEqUnitLike` checks); skips the type-former telescope
certification. -/
def structUnitCertNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  let ta ← r.infer depth a
  let wta ← r.whnf depth ta
  match ← withStore (fun st => st.getNode (st.getAppFnI wta)) with
  | some (.const T us') => do
    let Tn ← readbackNM T
    match fe.find? Tn with
    | some (.indInfo cvT caps) => do
      let targs ← withStore (·.getAppArgsI wta)
      if caps.unitlike = true ∧
          reservedBasisNames.contains Tn = false ∧
          targs.length = caps.unitParams ∧
          us'.length = cvT.levelParams.length ∧
          (cvT.type.stripPis caps.unitParams).isSome = true then do
        let tb ← r.infer depth b
        let wtb ← r.whnf depth tb
        r.defeq depth wta wtb
      else pure false
    | _ => pure false
  | _ => pure false

/-- Cert-skipping twin of `pairEtaCertI` (port of
`Setlec/Kernel/CoreNC.lean`'s `pairEtaCertNC`): keeps the constructor
and type-head guards, the level comparison, the two parameter
comparisons and the two field defeqs against the projections (all of
which the references' `tryEtaStructCore` performs, the parameter
comparisons as part of its `isDefEq (inferType t) (inferType s)`);
skips the projection-entry parameter telescope certification
`projParamCertI` (task #130). -/
def pairEtaCertNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  match ← viewI a with
  | some (.app f₄ s₂) =>
    match ← viewI f₄ with
    | some (.app f₃ s₁) =>
      match ← viewI f₃ with
      | some (.app f₂ pβ) =>
        match ← viewI f₂ with
        | some (.app f₁ pα) =>
          match ← viewI f₁ with
          | some (.const c us) => do
            let cn ← readbackNM c
            match fe.find? cn with
            | some (.ctorInfo _cvm 2 2) => do
              let tb ← r.infer depth b
              let wtb ← r.whnf depth tb
              match ← viewI wtb with
              | some (.app g₂ B) =>
                match ← viewI g₂ with
                | some (.app g₁ A) =>
                  match ← viewI g₁ with
                  | some (.const c' us') => do
                    let c'n ← readbackNM c'
                    match fe.find? c'n with
                    | some (.indInfo _ _) =>
                      match fe.find? (c'n.str "rec") with
                      | some (.recInfo _ mI rP [rr]) =>
                        if rr.ctor = cn ∧ rr.nfields = 2 ∧ mI = rP ∧
                            reservedBasisNames.contains (c'n.str "rec")
                              = true then do
                          if ← liftFueled "level comparison"
                              (← isEquivListLM us us') then do
                            if ← r.defeq depth pα A then do
                              if ← r.defeq depth pβ B then do
                                let p₀ ← internI (.proj c' 0 b)
                                if ← r.defeq depth s₁ p₀ then do
                                  let p₁ ← internI (.proj c' 1 b)
                                  r.defeq depth s₂ p₁
                                else pure false
                              else pure false
                            else pure false
                          else pure false
                        else pure false
                      | _ => pure false
                    | _ => pure false
                  | _ => pure false
                | _ => pure false
              | _ => pure false
            | _ => pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- Cert-skipping twin of `stuckIrrelI` (port of
`Setlec/Kernel/CoreNC.lean`'s `stuckIrrelNC`; `proofIrrelI` does no
proof-only work and is reused). -/
def stuckIrrelNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  if ← pairEtaCertNC r fe depth a b then pure true
  else if ← pairEtaCertNC r fe depth b a then pure true
  else if ← structEtaCertNC r fe depth a b then pure true
  else if ← structEtaCertNC r fe depth b a then pure true
  else if ← structUnitCertNC r fe depth a b then pure true
  else proofIrrelI r fe depth a b

/-- Cert-skipping twin of `majorToCtorI` (port of
`Setlec/Kernel/CoreNC.lean`'s `majorToCtorNC`).  The K-rescue
fabrication check is the official kernel's `toCtorWhenK` test — defeq
of the (whnf'd) major's type against the fabricated constructor
application's inferred type; NC differs from the certified twin only
in dropping the `proofIrrelI` soundness certificate that follows it.
The eta fabrication runs `structEtaCertWithNC`. -/
def majorToCtorNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : ExprC) :
    CheckCM ExprC := do
  if ← withStore (fun st => isCtorAppI fe st major) then pure major else
  match rules with
  | [rl] =>
    match fe.find? rl.ctor with
    | some (.ctorInfo cvj cnP cnF) =>
      match (cvj.type.piResult).getAppFn with
      | .const T _ =>
        match fe.find? T with
        | some (.indInfo cvT caps) =>
          if caps.ruleK = true ∧ cnF = 0 then do
            let tmaj₀ ← r.infer depth major
            let tmaj ← r.whnf depth tmaj₀
            match ← withStore (fun st => st.getNode (st.getAppFnI tmaj)) with
            | some (.const T' ust) =>
              if (← beqNameM T' T) ∧ cvj.levelParams.length = ust.length then do
                let margs ← withStore (·.getAppArgsI tmaj)
                let ctorI ← internNameM rl.ctor
                let h ← internI (.const ctorI ust)
                let fab ← mkAppNM h (margs.take cnP)
                if ← withStore (fun st => st.wscopedBI depth fab &&
                    st.looseBVarsBoundedI 0 fab &&
                    st.leafGuardI fab major) then do
                  -- official `toCtorWhenK`: the fabricated constructor's
                  -- type must be defeq to the major's (indices match)
                  let tfab ← r.infer depth fab
                  if ← r.defeq depth tmaj tfab then pure fab
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
              Name.isProjFnShape recName = false then do
            let tmaj₀ ← r.infer depth major
            let tmaj ← r.whnf depth tmaj₀
            match ← withStore (fun st => st.getNode (st.getAppFnI tmaj)) with
            | some (.const T' ust) => do
              let margs ← withStore (·.getAppArgsI tmaj)
              let ustL ← readbackLevelsM ust
              -- instantiated non-Prop guard, as in `majorToCtor`
              if (← beqNameM T' T) ∧ margs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length ∧
                  piResultNeverZero cvT.levelParams ustL cvT.type = true then do
                let TI ← internNameM T
                let projs ← projAppsI TI ust margs major
                  (List.range caps.etaFields)
                let ctorI ← internNameM caps.etaCtor
                let h ← internI (.const ctorI ust)
                let fab ← mkAppNM h (margs ++ projs)
                if ← withStore (fun st => st.wscopedBI depth fab &&
                    st.looseBVarsBoundedI 0 fab &&
                    st.leafGuardI fab major) then do
                  if ← structEtaCertWithNC r fe depth fab major tmaj then
                    pure fab
                  else if caps.etaFields = 0 ∧
                      cvj.levelParams.length = ust.length then
                    if ← proofIrrelI r fe depth fab major then pure fab
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

/-- Cert-skipping twin of `iotaRecI` (port of
`Setlec/Kernel/CoreNC.lean`'s `iotaRecNC`): keeps every check
lean4lean's `inductiveReduceRec` performs plus the verdict-relevant
level linkage, the nested-rule comparand values and the
projection-rule parameter comparison; skips the two telescope
certifications, the ordinary plain-rule parameter re-comparison and
the canonical-index comparison. -/
def iotaRecNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : ExprC) :
    CheckCM (Option ExprC) := do
  match ← withStore (fun st => st.getNode (st.getAppFnI e)) with
  | some (.const c us) => do
    let cn ← readbackNM c
    match fe.find? cn with
    | some (.recInfo cv mI rP rules) => do
      let args ← withStore (·.getAppArgsI e)
      -- checker change #9 (twin of `Core.lean`'s `iotaRec`): guard the
      -- recursor's level arity before the rule's RHS is instantiated.
      if args.length = mI + 1 ∧ us.length = cv.levelParams.length then do
        let bvar0 ← internI (.bvar 0)
        let major₀ ← r.whnf depth (args.getD mI bvar0)
        let major₁ ← litMajorToCtorI r fe depth major₀
        let major ← majorToCtorNC r fe depth cn rules major₁
        match ← withStore (fun st => st.getNode (st.getAppFnI major)) with
        | some (.const cj usj) => do
          let cjn ← readbackNM cj
          match fe.find? cjn with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cjn) with
            | some rl => do
              let margs ← withStore (·.getAppArgsI major)
              if margs.length = rl.ctorParams + rl.nfields then
               if rl.fire = .inert then
                 throw (.notImplemented
                   "iota reduction over a nested auxiliary recursor rule")
               else
               if (cv.type.stripPis (mI + 1)).isSome ∧
                  (cvj.type.stripPis (rl.ctorParams + rl.nfields)).isSome
                  then do
                let cmpLvls : List Level ←
                  match rl.fire with
                  | .nested lvls _ => substLevelTreesM cv.levelParams us lvls
                  | _ =>
                    substLevelTreesM cv.levelParams us
                      (cvj.levelParams.map Level.param)
                if ← liftFueled "level comparison"
                    (← isEquivListLM usj cmpLvls) then do
                 let cmpOk ← match rl.fire with
                   | .nested _ pins => do
                     let cmpArgs ← pinArgsI cv.levelParams us
                       (args.take rP) (rP - 1) pins
                     defEqListI r fe depth (margs.take rl.ctorParams) cmpArgs
                   | _ =>
                     if Name.isProjFnShape cn then
                       defEqListI r fe depth (margs.take rl.ctorParams)
                         (args.take rl.ctorParams)
                     else pure true
                 if cmpOk then do
                  let rhs ← ruleRhsAtM fe c cj cn cjn us
                  let red ← mkAppNM rhs
                    (args.take rP ++ margs.drop rl.ctorParams)
                  pure (some red)
                 else pure none
                else pure none
               else pure none
              else pure none
            | none => pure none
          | _ => pure none
        | _ => pure none
      else pure none
    | _ => pure none
  | _ => pure none

mutual

/-- Cert-skipping twin of `whnfAppI` (port of
`Setlec/Kernel/CoreNC.lean`'s `whnfAppNC`): a λ-binder always
beta-reduces (no per-redex argument re-check).  The head-normalization
loop's continuation `k` is threaded through (task #172 batch B1b, E1). -/
def whnfAppNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) :
    ExprC → List ExprC → CheckCM ExprC
  | v, [] => pure v
  | v, a :: rest => do
    match ← viewI v with
    | some (.lam _ _ty body _mb) => betaPeelNC r fe depth k body [a] rest
    | _ => do
      let fa ← internI (.app v a)
      match ← iotaRecNC r fe depth fa with
      | some e'' => do
        let v' ← k e''
        whnfAppNC r fe depth k v' rest
      | none => whnfAppNC r fe depth k fa rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Cert-skipping twin of `betaPeelI` (port of
`Setlec/Kernel/CoreNC.lean`'s `betaPeelNC`). -/
def betaPeelNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) :
    ExprC → List ExprC → List ExprC → CheckCM ExprC
  | t, acc, [] => do
    let e' ← instListM t acc
    k e'
  | t, acc, a :: rest => do
    match ← viewI t with
    | some (.lam _ _ty body _mb) => betaPeelNC r fe depth k body (a :: acc) rest
    | _ => do
      let e' ← instListM t acc
      let v ← k e'
      whnfAppNC r fe depth k v (a :: rest)
termination_by _ _acc args => (args.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- Cert-skipping twin of `whnfCoreStepI` (port of
`Setlec/Kernel/CoreNC.lean`'s `whnfCoreStepNC`): one head-normalization
step with the loop's continuation `k` abstracted.  The app clause
differs through `whnfAppNC`, and the proj clause drops the
constructor-telescope certification `projTeleCertI` (task #126).  The
possibly-Prop projection certificate `projCertI` is outside the
task-#76 site list and kept. -/
def whnfCoreStepNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) (e : ExprC) : CheckCM ExprC := do
    match ← viewI e with
    | some (.sort _) | some (.fvar ..) | some (.forallE ..)
    | some (.lam ..) | some (.const ..) | some (.lit _) => pure e
    | some (.app _ _) => do
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let v ← r.whnfCore depth h
      whnfAppNC r fe depth k v args
    | some (.proj sn i pe) => do
      let e' ← r.whnf depth pe
      let e' ← projLitToCtorI r fe depth e'
      let snn ← readbackNM sn
      match fe.findProj? snn i with
      | some entry =>
        match ← withStore (fun st => st.getNode (st.getAppFnI e')) with
        | some (.const c us) => do
          let args ← withStore (·.getAppArgsI e')
          if entry.native ∧ (← beqNameM c entry.ctor) ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length then do
            let bvar0 ← internI (.bvar 0)
            let arg := args.getD (entry.numParams + i) bvar0
            -- task #100 de-gating: ungated, as in `whnfCoreStepI`
            -- (`projCertI` stays — outside the task-#76 skip list;
            -- task #161 item B1 shrank it to its two `infer` runs)
            if ← projCertI r fe depth e' i entry.numParams then
              k arg
            else internI (.proj sn i e')
          else internI (.proj sn i e')
        | _ => internI (.proj sn i e')
      | none => internI (.proj sn i e')
    | some (.letE _ _ v b) => do
      let e' ← inst1M b v
      k e'
    | some (.bvar _) =>
      throw (.notImplemented "whnf beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Cert-skipping twin of `whnfCoreLoopI`: iterate `whnfCoreStepNC` on
its own step budget. -/
def whnfCoreLoopNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → ExprC → CheckCM ExprC
  | 0, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e =>
    whnfCoreStepNC r fe depth (whnfCoreLoopNC r fe depth n) e

/-- Cert-skipping twin of `whnfCoreBodyI`: the head-normalization loop
at its own step budget. -/
def whnfCoreBodyNC (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  fun depth e => whnfCoreLoopNC r fe depth whnfCoreLoopFuel e

/-- Cert-skipping twin of `inferBodyI` (port of
`Setlec/Kernel/CoreNC.lean`'s `inferBodyNC`; the app clause differs,
through `inferSpineNC`; the proj clause drops `projParamCertI`, task
#129).  The binder-loop fuel is `peelFuelM` (the `CoreC` convention —
there is no arena node count here). -/
def inferBodyNC (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  fun depth e => do
    match ← viewI e with
    | some (.sort u) => do
      let su ← internLM (.succ u)
      internI (.sort su)
    | some (.fvar idx _ ty) =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | some (.const n us) => do
      let nm ← readbackNM n
      match fe.find? nm with
      | none => throw (.invalid s!"unknown constant {nm}")
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {nm}")
        constTyAtM fe n nm us
    | some (.lit (.natVal _)) => do
      if natLitSupportedF fe then do
        let ni ← internNameM natName
        internI (.const ni [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | some (.lit (.strVal _)) => do
      if strLitSupportedF fe then do
        let si ← internNameM stringName
        internI (.const si [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | some (.forallE n ty body mb) => do
      -- Binder-telescope loop (task #72), shared with `inferBodyI`
      -- (task #100 stage 6: the codomain sort is inferred).
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort u) => do
        let fv ← internI (.fvar depth n ty)
        let fuel ← peelFuelM
        -- At `.noModel` the ∀-annotation validation is off (task
        -- #161), matching the spec's parity lane.
        inferPisI cfgNC r depth fuel body 1 #[fv] [(u, mb.pw)]
      | _ => throw (.invalid "expected a sort")
    | some (.lam n ty body mb) => do
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort _) => do
        -- Binder-telescope loop (task #72), shared with `inferBodyI`.
        -- At `.noModel` the λ-codomain sort check is off (task #152:
        -- official-kernel parity is this lane's whole point).
        let fv ← internI (.fvar depth n ty)
        let fuel ← peelFuelM
        inferLamsI cfgNC r depth fuel body 1 #[fv] [(n, ty, mb)]
      | _ => throw (.invalid "expected a sort")
    | some (.app _ _) => do
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let tf ← r.infer depth h
      inferSpineNC r depth tf #[] args
    | some (.proj _sn i pe) => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.getNode (st.getAppFnI te)) with
      | some (.const T us) => do
        let Tn ← readbackNM T
        match fe.findProj? Tn i with
        | some entry => do
          let targs ← withStore (·.getAppArgsI te)
          if entry.native ∧ targs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            -- Task #172 batch B1b (E2): the same clause as
            -- `inferBodyI`'s — the residual is computed from the
            -- pinned two-parameter basis shape, not walked out of the
            -- stored entry type.  `NativeProjPinned.spineShape`
            -- (`Verify/ProjPinInv.lean`) makes the fall-through branch
            -- unreachable on every environment the checker builds, and
            -- `piResidual_of_invariant` (`SetBase/ProjPins.lean`)
            -- proves the computed value is what the walk would have
            -- returned — both with no environment predicate as a
            -- premise, so this lane stays licence-free.
            match targs, i with
            | [A, _], 0 => pure A
            | [_, B], 1 => do
              let p₀ ← internI (.proj T 0 pe)
              internI (.app B p₀)
            | _, _ => throw (.internal "malformed projection entry")
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | some (.letE _ ty v b) => do
      -- the official kernel's `infer_let` checks, as in `inferBodyI`
      -- (task #100 stage 6: moved here from the deleted annotation pass)
      let _ ← ensureSortI r depth (← r.infer depth ty)
      let tv ← r.infer depth v
      unless ← r.defeq depth tv ty do
        throw (.invalid "let value type mismatch")
      let e' ← inst1M b v
      r.infer depth e'
    | some (.bvar _) =>
      throw (.notImplemented "inferType beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Cert-skipping twin of `defeqStepI` (port of
`Setlec/Kernel/CoreNC.lean`'s `defeqStepNC`; only the stuck-term
fallback differs, through `stuckIrrelNC`). -/
def defeqStepNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → ExprC → CheckCM Bool) (a b : ExprC) : CheckCM Bool := do
    if a == b then pure true else
    let a' ← r.whnfCore depth a
    let b' ← r.whnfCore depth b
    if a' == b' then pure true else
    if ← proofIrrelI r fe depth a' b' then pure true else
    -- fvar-free guard on defeq-side literal folding, as in
    -- `defeqBodyI` (official kernel `lazy_delta_reduction`; lean4lean
    -- `TypeChecker.lean:782`)
    let fold ← withStore fun st => !st.hasFvarI a' && !st.hasFvarI b'
    match ← (if fold then reduceNatI r fe depth a' else pure none) with
    | some a₂ => k a₂ b'
    | none =>
    match ← (if fold then reduceNatI r fe depth b' else pure none) with
    | some b₂ => k a' b₂
    | none =>
    -- lazy delta, decision before materialization; see `defeqBody`
    match ← withStore (fun st => unfoldableHeadI fe st a'),
        ← withStore (fun st => unfoldableHeadI fe st b') with
    | true, false =>
      match ← unfoldDefinitionI fe a' with
      | some a₂ => k a₂ b'
      | none => pure false
    | false, true =>
      match ← unfoldDefinitionI fe b' with
      | some b₂ => k a' b₂
      | none => pure false
    | true, true => do
      let ha ← withStore (fun st => headHintI fe st a')
      let hb ← withStore (fun st => headHintI fe st b')
      if ReducibilityHint.lt hb ha then
        match ← unfoldDefinitionI fe a' with
        | some a₂ => k a₂ b'
        | none => pure false
      else if ReducibilityHint.lt ha hb then
        match ← unfoldDefinitionI fe b' with
        | some b₂ => k a' b₂
        | none => pure false
      else if ReducibilityHint.sameRegular ha hb &&
          (← withStore (sameConstHeadsI · a' b')) then do
        if ← defeqSpineI r fe depth a' b' then pure true
        else
          match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
          | some a₂, some b₂ => k a₂ b₂
          | _, _ => pure false
      else
        match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
        | some a₂, some b₂ => k a₂ b₂
        | _, _ => pure false
    | false, false =>
    match ← viewI a', ← viewI b' with
    | some (.sort u), some (.sort v) => do
      liftFueled "level comparison" (← isEquivLM u v)
    | some (.lit l₁), some (.lit l₂) => pure (l₁ == l₂)
    | some (.lit (.natVal n)), some (.const c us) =>
      if (← beqNameM c natZeroName) ∧ us = [] then pure (n == 0)
      else stuckIrrelNC r fe depth a' b'
    | some (.const c us), some (.lit (.natVal n)) =>
      if (← beqNameM c natZeroName) ∧ us = [] then pure (n == 0)
      else stuckIrrelNC r fe depth a' b'
    | some (.lit (.natVal nn)), some (.app f x) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if ← beqNameM c natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth kl x
        else stuckIrrelNC r fe depth a' b'
      | _, _ => stuckIrrelNC r fe depth a' b'
    | some (.app f x), some (.lit (.natVal nn)) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if ← beqNameM c natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth x kl
        else stuckIrrelNC r fe depth a' b'
      | _, _ => stuckIrrelNC r fe depth a' b'
    | some (.lit (.strVal s)), some (.app fO _x) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if (← beqNameM cO stringOfListName) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth sc b'
        else stuckIrrelNC r fe depth a' b'
      | _ => stuckIrrelNC r fe depth a' b'
    | some (.app fO _x), some (.lit (.strVal s)) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if (← beqNameM cO stringOfListName) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth a' sc
        else stuckIrrelNC r fe depth a' b'
      | _ => stuckIrrelNC r fe depth a' b'
    | some (.fvar i _ _), some (.fvar j _ _) =>
      if i == j then pure true
      else stuckIrrelNC r fe depth a' b'
    | some (.const n us), some (.const n' us') =>
      if n = n' then do
        if ← liftFueled "level comparison" (← isEquivListLM us us') then
          pure true
        else stuckIrrelNC r fe depth a' b'
      else stuckIrrelNC r fe depth a' b'
    | some (.forallE n₁ ty₁ body₁ _m₁), some (.forallE n₂ ty₂ body₂ _m₂) => do
      -- no binder-annotation comparison; see `defeqBody`
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      r.defeq (depth + 1) b₁ b₂
    | some (.lam n₁ ty₁ body₁ _m₁), some (.lam n₂ ty₂ body₂ _m₂) => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      r.defeq (depth + 1) b₁ b₂
    | some (.app _f₁ _a₁), some (.app _f₂ _a₂) => do
      -- spine-wise congruence, as in the spec body `defeqBody`
      let as₁ ← withStore (·.getAppArgsI a')
      let as₂ ← withStore (·.getAppArgsI b')
      if as₁.length = as₂.length then do
        let h₁ ← withStore (fun st => st.getAppFnI a')
        let h₂ ← withStore (fun st => st.getAppFnI b')
        if ← r.defeq depth h₁ h₂ then do
          if ← defEqListI r fe depth as₁ as₂ then pure true
          else stuckIrrelNC r fe depth a' b'
        else stuckIrrelNC r fe depth a' b'
      else stuckIrrelNC r fe depth a' b'
    | some (.proj _s₁ i₁ e₁), some (.proj _s₂ i₂ e₂) => do
      if i₁ == i₂ then do
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrelNC r fe depth a' b'
      else stuckIrrelNC r fe depth a' b'
    | some (.lam n₁ ty₁ body₁ m₁), _ => do
      if ← etaCertI cfgNC r fe depth n₁ ty₁ body₁ m₁ b' then pure true
      else stuckIrrelNC r fe depth a' b'
    | _, some (.lam n₂ ty₂ body₂ m₂) => do
      if ← etaCertI cfgNC r fe depth n₂ ty₂ body₂ m₂ a' then pure true
      else stuckIrrelNC r fe depth a' b'
    | some _, some _ => stuckIrrelNC r fe depth a' b'
    | _, _ => throw (.internal "interned node missing")

/-- Cert-skipping twin of `defeqLoopI` (port of
`Setlec/Kernel/CoreNC.lean`'s `defeqLoopNC`). -/
def defeqLoopNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → ExprC → ExprC → CheckCM Bool
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | fl + 1, a, b => defeqStepNC r fe depth (defeqLoopNC r fe depth fl) a b

/-- Cert-skipping twin of `defeqBodyI` (port of
`Setlec/Kernel/CoreNC.lean`'s `defeqBodyNC`). -/
def defeqBodyNC (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → ExprC → CheckCM Bool :=
  fun depth a b => defeqLoopNC r fe depth defeqLoopFuel a b

/-- perf-eng E2 (port of `Setlec/Kernel/CoreNC.lean`'s `memoEINC`):
`@[inline]` twin of `memoEI`, scoped to the measurement-only NC knot —
after inlining, the getter/setter lambdas beta-reduce away and the
memo probe compiles into the record field's own closure. -/
@[inline] private def memoEINC (get' : CState → Std.HashMap ExprC ExprC)
    (set' : CState → Std.HashMap ExprC ExprC → CState)
    (f : Nat → ExprC → CheckCM ExprC) : Nat → ExprC → CheckCM ExprC :=
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

/-- The infer-only inference memo with the **one-directional share**
from the checking-mode front-door memo (port of
`Setlec/Kernel/CoreNC.lean`'s `memoEIO`, task #134/#161).

Reads `inferFC` first, then `inferC`; writes **only** `inferC`.  The
direction is the sound one: a checking-mode inference and an
infer-only inference of the same node compute the same type, but the
former also *validated* the arguments, so serving it to an infer-only
query loses nothing.  The converse share would serve an unvalidated
type to a checking-mode query and must never be added — the front
door (`coreKnotFNC.infer`) stays a plain `memoEINC (·.inferFC)`.

Lifetimes coincide: `checkDeclSPStepCNC` clears `inferC` (via
`flushC`) and `inferFC` (via `flushInferFC`) back to back at every
declaration boundary. -/
def memoEIO (f : Nat → ExprC → CheckCM ExprC) : Nat → ExprC → CheckCM ExprC :=
  fun d e => do
    let st ← get
    match st.inferFC[e]? with
    | some r => pure r
    | none =>
      match st.inferC[e]? with
      | some r => pure r
      | none =>
        let r ← f d e
        modify fun st =>
          let mp := st.inferC
          let st := { st with inferC := ∅ }
          { st with inferC := mp.insert e r }
        pure r

/-- perf-eng E2: `@[inline]` twin of `memoBI` (port of
`Setlec/Kernel/CoreNC.lean`'s `memoBINC`; see `memoEINC`). -/
@[inline] private def memoBINC (f : Nat → ExprC → ExprC → CheckCM Bool) :
    Nat → ExprC → ExprC → CheckCM Bool :=
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

/-- Tie the cert-skipping bodies at the memoizing state monad (port of
`Setlec/Kernel/CoreNC.lean`'s `coreKnotNC`, E1 Thunk-caching shape
kept; the `whnf` and `annotate` bodies are the certified ones — their
behavior differences come entirely through the record).  The
consistency proofs are pinned to `coreKnotI`; this knot is
measurement-only. -/
def coreKnotNC (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    -- perf-eng E1: the previous fuel level is built at most once per
    -- record (Thunk-cached) instead of once per cache-missing call.
    let prev : Thunk CoreFnsI := ⟨fun _ => coreKnotNC fe fuel⟩
    { whnfCore := memoEINC (·.whnfCoreC)
        (fun st mp => { st with whnfCoreC := mp })
        (fun d e => whnfCoreBodyNC prev.get fe d e)
      whnf := memoEINC (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI prev.get fe d e)
      infer := memoEIO (fun d e => inferBodyNC prev.get fe d e)
      defeq := memoBINC
        (fun d a b => defeqBodyNC prev.get fe d a b)
      annotate := memoEINC (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI cfgNC prev.get fe d e) }

/-- The `--no-model` cached **checking-mode front-door knot** (port of
`Setlec/Kernel/CoreNC.lean`'s `coreKnotFNC`; the task-#134 `coreKnotF`
pattern over the cert-skipping internals).  `infer` is the certified
`inferBodyI` at `.noModel` — the official kernel's checking-mode
`infer_type_core(e, infer_only := false)`; `annotate` is tied to
itself for the same reason.  `whnfCore`/`whnf`/`defeq` are
`coreKnotNC`'s, so every inference *reduction* performs internally is
infer-only and certificate-free.  The checking-mode inference memo is
`inferFC`, kept apart from the infer-only `inferC`. -/
def coreKnotFNC (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    -- perf-eng E1: share one `coreKnotNC` build across the three
    -- reduction fields, and Thunk-cache the recursive front-door level.
    let nc := coreKnotNC fe (fuel + 1)
    let prev : Thunk CoreFnsI := ⟨fun _ => coreKnotFNC fe fuel⟩
    { whnfCore := nc.whnfCore
      whnf := nc.whnf
      defeq := nc.defeq
      infer := memoEINC (·.inferFC) (fun st mp => { st with inferFC := mp })
        (fun d e => inferBodyI cfgNC prev.get fe d e)
      annotate := memoEINC (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI cfgNC prev.get fe d e) }

/-- Drop the checking-mode inference memo (port of
`Setlec/Kernel/CoreNC.lean`'s `flushInferFC`); called back to back
with `flushC` at every declaration boundary. -/
def flushInferFC : CheckCM Unit :=
  modify fun s => { s with inferFC := {} }

end Setlec.Cached
