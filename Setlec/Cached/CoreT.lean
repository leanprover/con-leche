import Setlec.Cached.CoreC

/-!
# The cert-skipping cached core (the `--trusted` cached trusted lane)

A twin of the kernel's cert-skipping interned core
(`Setlec/Kernel/CoreNC.lean`) over `ExprC`: **every function below
mirrors its interned NC original clause by clause** — same order of
record calls, same short-circuits, same caches, same loops — with the
arena replaced by the computed-field representation, exactly the way
`Setlec/Cached/CoreC.lean` clones `Setlec/Kernel/CoreI.lean` (the
store wrappers survive as `CStore` no-ops, the interning wrappers as
smart constructors, the name/level interning as identities).  Where an
NC body references a certified helper (`reduceNatI`,
`unfoldDefinitionI`, `whnfBodyI`, `annotateBodyI`, `ensureSortI`, …)
it uses the `CoreC` twin under the same name.

The task-#76 skip list — which infer/defeq calls are proof-only and
why — is documented once, in `Setlec/Kernel/CoreNC.lean`'s module
docstring; this clone adds no new judgement.  Measurement-only:
nothing in `Setlec/Verify/*` or `Setlec/SetR/*` may import this
module, and none of the consistency statements cover these knots.
Main reaches these bodies only through the `--trusted
--core=cached-parsed` driver (`Setlec/Cached/ParsedT.lean`).

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
def inferSpineT (r : CoreFnsI) (depth : Nat) :
    ExprC → Array ExprC → List ExprC → CheckCM ExprC
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ← viewI ty with
    | some (.forallE _ _dom body _) =>
      inferSpineT r depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← r.whnf depth ty'
      match ← viewI w with
      | some (.forallE _ _dom body _) =>
        inferSpineT r depth body #[a] rest
      | _ => throw (.invalid "function expected")

/-- Cert-skipping twin of `structEtaCertWithI` (port of
`Setlec/Kernel/CoreNC.lean`'s `structEtaCertWithNC`): keeps the guard,
the level comparison, the parameter comparison and the per-field defeq
against the projections (what lean4lean's `tryEtaStructCore` checks);
skips the type-former and per-projection telescope certifications. -/
def structEtaCertWithT (r : CoreFnsI) (fe : FEnv) (depth : Nat)
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
                (cvT.type.stripPis cnP).isSome = true ∧
                (fe.towerSlotsAllF Tn cnF || fe.recSlotsAllF Tn cnF) = true then do
              if ← liftFueled "level comparison"
                  (← isEquivListLM us us') then do
                if ← defEqListI r fe depth (aargs.take cnP) targs then do
                  let projs ← projAppsI fe Tn T us' targs b cnF
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
def structEtaCertT (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  -- the constructor-shape gate first (D13), as in the spec
  let sh ← withStore (fun st => etaCtorShapeI fe st a)
  if sh then
    let tb ← r.infer depth b
    let wtb ← r.whnf depth tb
    structEtaCertWithT r fe depth a b wtb
  else pure false

/-- Cert-skipping twin of `structUnitCertI` (port of
`Setlec/Kernel/CoreNC.lean`'s `structUnitCertNC`): keeps the unit-like
shape guard and the defeq of the two whnf'd types (what lean4lean's
`isDefEqUnitLike` checks); skips the type-former telescope
certification. -/
def structUnitCertT (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
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

/-- Cert-skipping twin of `stuckIrrelI` (port of
`Setlec/Kernel/CoreNC.lean`'s `stuckIrrelNC`; `proofIrrelI` does no
proof-only work and is reused). -/
def stuckIrrelT (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : ExprC) :
    CheckCM Bool := do
  if ← structEtaCertT r fe depth a b then pure true
  else if ← structEtaCertT r fe depth b a then pure true
  else if ← structUnitCertT r fe depth a b then pure true
  else proofIrrelI r fe depth a b

/-- Cert-skipping twin of `majorToCtorI` (port of
`Setlec/Kernel/CoreNC.lean`'s `majorToCtorNC`).  The K-rescue
fabrication check is the official kernel's `toCtorWhenK` test — defeq
of the (whnf'd) major's type against the fabricated constructor
application's inferred type; NC differs from the certified twin only
in dropping the `proofIrrelI` soundness certificate that follows it.
The eta fabrication runs `structEtaCertWithT`. -/
def majorToCtorT (r : CoreFnsI) (fe : FEnv) (depth : Nat)
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
                let projs ← projAppsI fe T TI ust margs major caps.etaFields
                let ctorI ← internNameM caps.etaCtor
                let h ← internI (.const ctorI ust)
                let fab ← mkAppNM h (margs ++ projs)
                if ← withStore (fun st => st.wscopedBI depth fab &&
                    st.looseBVarsBoundedI 0 fab &&
                    st.leafGuardI fab major) then do
                  if ← structEtaCertWithT r fe depth fab major tmaj then
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

/-- Cert-skipping twin of `prepareMajorI`: the same official order
(`prepareMajor`'s docstring) over `majorToCtorT`. -/
def prepareMajorT (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : ExprC) :
    CheckCM ExprC := do
  if recRuleKOf fe.find? rules then do
    let majorK ← majorToCtorT r fe depth recName rules major
    let major₀ ← r.whnf depth majorK
    litMajorToCtorI r fe depth major₀
  else do
    let major₀ ← r.whnf depth major
    let major₁ ← litMajorToCtorI r fe depth major₀
    majorToCtorT r fe depth recName rules major₁

/-- Cert-skipping twin of `iotaRecI` (port of
`Setlec/Kernel/CoreNC.lean`'s `iotaRecNC`): keeps every check
lean4lean's `inductiveReduceRec` performs plus the verdict-relevant
level linkage, the nested-rule comparand values and the
projection-rule parameter comparison; skips the two telescope
certifications, the ordinary plain-rule parameter re-comparison and
the canonical-index comparison. -/
def iotaRecT (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : ExprC) :
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
        let major ← prepareMajorT r fe depth cn rules (args.getD mI bvar0)
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
               else do
                -- (the ι batch: the two `stripPis` pins are gone — see
                -- the spec's `iotaRec`)
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
def whnfAppT (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) :
    ExprC → List ExprC → CheckCM ExprC
  | v, [] => pure v
  | v, a :: rest => do
    match ← viewI v with
    | some (.lam _ _ty body _mb) => betaPeelT r fe depth k body [a] rest
    | _ => do
      let fa ← internI (.app v a)
      match ← iotaRecT r fe depth fa with
      | some e'' => do
        let v' ← k e''
        whnfAppT r fe depth k v' rest
      | none => whnfAppT r fe depth k fa rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Cert-skipping twin of `betaPeelI` (port of
`Setlec/Kernel/CoreNC.lean`'s `betaPeelNC`). -/
def betaPeelT (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) :
    ExprC → List ExprC → List ExprC → CheckCM ExprC
  | t, acc, [] => do
    let e' ← instListM t acc
    k e'
  | t, acc, a :: rest => do
    match ← viewI t with
    | some (.lam _ _ty body _mb) => betaPeelT r fe depth k body (a :: acc) rest
    | _ => do
      let e' ← instListM t acc
      let v ← k e'
      whnfAppT r fe depth k v (a :: rest)
termination_by _ _acc args => (args.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- Cert-skipping twin of `whnfCoreStepI` (port of
`Setlec/Kernel/CoreNC.lean`'s `whnfCoreStepNC`): one head-normalization
step with the loop's continuation `k` abstracted.  The app clause
differs through `whnfAppT`, and the proj clause drops the
constructor-telescope certification `projTeleCertI` (task #126) and,
since 2026-09-06 (parity mirrors official), the spine certificate
`projCertI` too: official's `reduce_proj` runs none. -/
def whnfCoreStepT (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : ExprC → CheckCM ExprC) (e : ExprC) : CheckCM ExprC := do
    match ← viewI e with
    | some (.sort _) | some (.fvar ..) | some (.forallE ..)
    | some (.lam ..) | some (.const ..) | some (.lit _) => pure e
    | some (.app _ _) => do
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let v ← r.whnfCore depth h
      whnfAppT r fe depth k v args
    | some (.proj sn i pe) => do
      let e' ← r.whnf depth pe
      let e' ← projLitToCtorI r fe depth e'
      let snn ← readbackNM sn
      match fe.findProj? snn i with
      | some entry =>
        match ← withStore (fun st => st.getNode (st.getAppFnI e')) with
        | some (.const c us) => do
          let args ← withStore (·.getAppArgsI e')
          if entry.tower ∧ (← beqNameM c entry.ctor) ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length ∧
              entry.fireOk us = true then do
            let bvar0 ← internI (.bvar 0)
            let arg := args.getD (entry.numParams + i) bvar0
            -- parity mirrors official (2026-09-06): `reduce_proj`
            -- reduces every constructor redex with no certificate, so
            -- the trusted core runs none — `projCertAt` at
            -- `verified = false` in the shared body
            k arg
          else internI (.proj sn i e')
        | _ => internI (.proj sn i e')
      | none => internI (.proj sn i e')
    | some (.letE _ _ v b) => do
      let e' ← inst1M b v
      k e'
    | some (.bvar _) =>
      throw (.notImplemented "whnf beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Cert-skipping twin of `whnfCoreLoopI`: iterate `whnfCoreStepT` on
its own step budget. -/
def whnfCoreLoopT (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → ExprC → CheckCM ExprC
  | 0, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, e =>
    whnfCoreStepT r fe depth (whnfCoreLoopT r fe depth n) e

/-- Cert-skipping twin of `whnfCoreBodyI`: the head-normalization loop
at its own step budget. -/
def whnfCoreBodyT (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
  fun depth e => whnfCoreLoopT r fe depth whnfCoreLoopFuel e

/-- Cert-skipping twin of `inferBodyI` (port of
`Setlec/Kernel/CoreNC.lean`'s `inferBodyNC`; the app clause differs,
through `inferSpineT`; the proj clause drops `projParamCertI`, task
#129).  The binder-loop fuel is `peelFuelM` (the `CoreC` convention —
there is no arena node count here). -/
def inferBodyT (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → CheckCM ExprC :=
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
        -- At `.trusted` the ∀-annotation validation is off (task
        -- #161), matching the spec's trusted lane.
        inferPisI cfgT r depth fuel body 1 #[fv] [(u, mb.pw)]
      | _ => throw (.invalid "expected a sort")
    | some (.lam n ty body mb) => do
      let tty ← r.infer depth ty
      let wtty ← r.whnf depth tty
      match ← viewI wtty with
      | some (.sort _) => do
        -- Binder-telescope loop (task #72), shared with `inferBodyI`.
        -- At `.trusted` the λ-codomain sort check is off (task #152:
        -- dropping certification-only work is this lane's point).
        let fv ← internI (.fvar depth n ty)
        let fuel ← peelFuelM
        inferLamsI cfgT r depth fuel body 1 #[fv] [(n, ty, mb)]
      | _ => throw (.invalid "expected a sort")
    | some (.app _ _) => do
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let tf ← r.infer depth h
      inferSpineT r depth tf #[] args
    | some (.proj sn i pe) => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.getNode (st.getAppFnI te)) with
      | some (.const T us) => do
        let Tn ← readbackNM T
        match fe.findProj? Tn i with
        | some entry => do
          let targs ← withStore (·.getAppArgsI te)
          if entry.tower ∧ T = sn ∧ targs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            -- the official `infer_proj` restriction (task #175
            -- W4c/O4), as in the spec body
            if Level.isEquiv entry.structSort .zero == some true then
              unless Level.isEquiv
                  (Level.subst entry.levelParams us entry.fieldSort) .zero
                  == some true do
                throw (.invalid
                  "projection from a propositional structure must be a proposition")
            -- the body at the arguments and the subject, as in the
            -- spec body (task #175 S1) — since B3a `ExprC = Expr` and
            -- the store is a unit, so the instantiation runs directly
            -- on the stored body and the interned spine.
            internExprM (entry.typeAt us targs pe)
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
fallback differs, through `stuckIrrelT`). -/
def defeqStepT (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : Bool → ExprC → ExprC → CheckCM Bool) (pi : Bool) (a b : ExprC) :
    CheckCM Bool := do
    if a == b then pure true else
    -- the eq-true shortcut (E2), as in the spec
    let bt ← withStore (isBoolTrueI · b)
    let af ← withStore (fun st => st.hasFvarI a)
    if ← (if pi && bt && !af then boolTrueShortcutI r depth a
        else pure false) then pure true else
    let a' ← r.whnfCore depth a
    let b' ← r.whnfCore depth b
    if a' == b' then pure true else
    -- proof irrelevance once per entry (`pi`; the spec's D3 note)
    let qp ← withStore (fun st => quickPairI st a' b')
    if ← (if pi && !qp then propIrrelI cfgT r fe depth a' b' else pure false) then
      pure true else
    -- fvar-free guard on defeq-side literal folding, as in
    -- `defeqBodyI` (official kernel `lazy_delta_reduction`; lean4lean
    -- `TypeChecker.lean:782`)
    let fold ← withStore fun st => !st.hasFvarI a' && !st.hasFvarI b'
    match ← (if fold then reduceNatI r fe depth a' else pure none) with
    | some a₂ => k true a₂ b'
    | none =>
    match ← (if fold then reduceNatI r fe depth b' else pure none) with
    | some b₂ => k true a' b₂
    | none =>
    -- lazy delta, decision before materialization; see `defeqBody`
    match ← withStore (fun st => unfoldableHeadI fe st a'),
        ← withStore (fun st => unfoldableHeadI fe st b') with
    | true, false =>
      match ← unfoldDefinitionI fe a' with
      | some a₂ => k false a₂ b'
      | none => pure false
    | false, true =>
      match ← unfoldDefinitionI fe b' with
      | some b₂ => k false a' b₂
      | none => pure false
    | true, true => do
      let ha ← withStore (fun st => headHintI fe st a')
      let hb ← withStore (fun st => headHintI fe st b')
      if ReducibilityHint.lt hb ha then
        match ← unfoldDefinitionI fe a' with
        | some a₂ => k false a₂ b'
        | none => pure false
      else if ReducibilityHint.lt ha hb then
        match ← unfoldDefinitionI fe b' with
        | some b₂ => k false a' b₂
        | none => pure false
      else if ReducibilityHint.sameRegular ha hb &&
          (← withStore (sameConstHeadsI · a' b')) then do
        if ← defeqSpineI r fe depth a' b' then pure true
        else
          match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
          | some a₂, some b₂ => k false a₂ b₂
          | _, _ => pure false
      else
        match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
        | some a₂, some b₂ => k false a₂ b₂
        | _, _ => pure false
    | false, false =>
    match ← viewI a', ← viewI b' with
    | some (.sort u), some (.sort v) => do
      liftFueled "level comparison" (← isEquivLM u v)
    | some (.lit l₁), some (.lit l₂) => pure (l₁ == l₂)
    | some (.lit (.natVal n)), some (.const c us) =>
      if (← beqNameM c natZeroName) ∧ us = [] then pure (n == 0)
      else stuckIrrelT r fe depth a' b'
    | some (.const c us), some (.lit (.natVal n)) =>
      if (← beqNameM c natZeroName) ∧ us = [] then pure (n == 0)
      else stuckIrrelT r fe depth a' b'
    | some (.lit (.natVal nn)), some (.app f x) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if ← beqNameM c natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth kl x
        else stuckIrrelT r fe depth a' b'
      | _, _ => stuckIrrelT r fe depth a' b'
    | some (.app f x), some (.lit (.natVal nn)) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if ← beqNameM c natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth x kl
        else stuckIrrelT r fe depth a' b'
      | _, _ => stuckIrrelT r fe depth a' b'
    | some (.lit (.strVal s)), some (.app fO _x) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if (← beqNameM cO stringOfListName) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth sc b'
        else stuckIrrelT r fe depth a' b'
      | _ => stuckIrrelT r fe depth a' b'
    | some (.app fO _x), some (.lit (.strVal s)) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if (← beqNameM cO stringOfListName) ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth a' sc
        else stuckIrrelT r fe depth a' b'
      | _ => stuckIrrelT r fe depth a' b'
    | some (.fvar i _ _), some (.fvar j _ _) =>
      if i == j then pure true
      else stuckIrrelT r fe depth a' b'
    | some (.const n us), some (.const n' us') =>
      if n = n' then do
        if ← liftFueled "level comparison" (← isEquivListLM us us') then
          pure true
        else stuckIrrelT r fe depth a' b'
      else stuckIrrelT r fe depth a' b'
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
          else stuckIrrelT r fe depth a' b'
        else stuckIrrelT r fe depth a' b'
      else stuckIrrelT r fe depth a' b'
    | some (.proj s₁ i₁ e₁), some (.proj s₂ i₂ e₂) => do
      if s₁ == s₂ && i₁ == i₂ then do
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrelT r fe depth a' b'
      else stuckIrrelT r fe depth a' b'
    | some (.lam n₁ ty₁ body₁ m₁), _ => do
      if ← etaCertI cfgT r fe depth n₁ ty₁ body₁ m₁ b' then pure true
      else stuckIrrelT r fe depth a' b'
    | _, some (.lam n₂ ty₂ body₂ m₂) => do
      if ← etaCertI cfgT r fe depth n₂ ty₂ body₂ m₂ a' then pure true
      else stuckIrrelT r fe depth a' b'
    | some _, some _ => stuckIrrelT r fe depth a' b'
    | _, _ => throw (.internal "interned node missing")

/-- Cert-skipping twin of `defeqLoopI` (port of
`Setlec/Kernel/CoreNC.lean`'s `defeqLoopNC`). -/
def defeqLoopT (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → Bool → ExprC → ExprC → CheckCM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | fl + 1, pi, a, b =>
    defeqStepT r fe depth (defeqLoopT r fe depth fl) pi a b

/-- Cert-skipping twin of `defeqBodyI` (port of
`Setlec/Kernel/CoreNC.lean`'s `defeqBodyNC`). -/
def defeqBodyT (r : CoreFnsI) (fe : FEnv) : Nat → ExprC → ExprC → CheckCM Bool :=
  fun depth a b => defeqLoopT r fe depth defeqLoopFuel true a b

/-- perf-eng E2 (port of `Setlec/Kernel/CoreNC.lean`'s `memoEINC`):
`@[inline]` twin of `memoEI`, scoped to the measurement-only NC knot —
after inlining, the getter/setter lambdas beta-reduce away and the
memo probe compiles into the record field's own closure. -/
@[inline] private def memoEIT (get' : CState → Std.HashMap ExprC ExprC)
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
door (`coreKnotFT.infer`) stays a plain `memoEIT (·.inferFC)`.

Lifetimes coincide: `checkDeclSPStepCT` clears `inferC` (via
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
`Setlec/Kernel/CoreNC.lean`'s `memoBINC`; see `memoEIT`). -/
@[inline] private def memoBIT (f : Nat → ExprC → ExprC → CheckCM Bool) :
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
def coreKnotT (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    -- perf-eng E1: the previous fuel level is built at most once per
    -- record (Thunk-cached) instead of once per cache-missing call.
    let prev : Thunk CoreFnsI := ⟨fun _ => coreKnotT fe fuel⟩
    { whnfCore := memoEIT (·.whnfCoreC)
        (fun st mp => { st with whnfCoreC := mp })
        (fun d e => whnfCoreBodyT prev.get fe d e)
      whnf := memoEIT (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI prev.get fe d e)
      infer := memoEIO (fun d e => inferBodyT prev.get fe d e)
      -- task #172 B4 (field added to the shared record): the internal
      -- knot's inference IS the io grade in the trusted mode — bind the io slot to
      -- the same memoized closure (nothing in the NC bodies reads it).
      inferIO := memoEIO (fun d e => inferBodyT prev.get fe d e)
      defeq := memoBIT
        (fun d a b => defeqBodyT prev.get fe d a b)
      annotate := memoEIT (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI cfgT prev.get fe d e) }

/-- The `--trusted` cached **checking-mode front-door knot** (port of
`Setlec/Kernel/CoreNC.lean`'s `coreKnotFNC`; the task-#134 `coreKnotF`
pattern over the cert-skipping internals).  `infer` is the certified
`inferBodyI` at `.trusted` — the official kernel's checking-mode
`infer_type_core(e, infer_only := false)`; `annotate` is tied to
itself for the same reason.  `whnfCore`/`whnf`/`defeq` are
`coreKnotT`'s, so every inference *reduction* performs internally is
infer-only and certificate-free.  The checking-mode inference memo is
`inferFC`, kept apart from the infer-only `inferC`. -/
def coreKnotFT (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    -- perf-eng E1: share one `coreKnotT` build across the three
    -- reduction fields, and Thunk-cache the recursive front-door level.
    let nc := coreKnotT fe (fuel + 1)
    let prev : Thunk CoreFnsI := ⟨fun _ => coreKnotFT fe fuel⟩
    { whnfCore := nc.whnfCore
      whnf := nc.whnf
      defeq := nc.defeq
      infer := memoEIT (·.inferFC) (fun st mp => { st with inferFC := mp })
        (fun d e => inferBodyI cfgT prev.get fe d e)
      -- task #172 B4: the front-door knot never serves internal calls;
      -- its io slot is the internal (cert-skipping) knot's inference,
      -- which is what an internal caller would mean in the trusted mode.
      inferIO := nc.infer
      annotate := memoEIT (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI cfgT prev.get fe d e) }

/-- Drop the checking-mode inference memo (port of
`Setlec/Kernel/CoreNC.lean`'s `flushInferFC`); called back to back
with `flushC` at every declaration boundary. -/
def flushInferFC : CheckCM Unit :=
  modify fun s => { s with inferFC := {} }

end Setlec.Cached
