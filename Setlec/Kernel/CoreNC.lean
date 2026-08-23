import Setlec.Kernel.CoreI

/-!
# The cert-skipping interned core (task #76, `SETLEC_NO_PROOF_CERTS`)

**Unverified measurement mode.**  Twins of the interned core bodies
(`Setlec/Kernel/CoreI.lean`) with the infer/defeq calls removed that
exist *only* to feed the soundness proofs — the reference kernels
(official C++ kernel, lean4lean) do not perform them, so skipping them
cannot change the verdict on valid input.  The point of this mode is a
fair performance comparison: the instruction delta between the default
(certified) knot and this knot is the *verification tax*; the residual
gap to the reference kernels is engineering quality.

None of the consistency proofs cover this knot.  The default path
(`coreKnotI` → `sharedOps` → `checkDeclsShared`) is byte-identical to
before this file existed; Main selects this knot only when the
`SETLEC_NO_PROOF_CERTS=1` environment variable is set.

Skipped here (each site cites why it is proof-only):

* `iotaRecNC` (vs `iotaRecI`): the per-fire recursor-telescope and
  constructor-telescope certifications (since task #71 the certified
  pipeline runs them possibly-Prop-*gated*, `iotaCertsGI`; NC skips
  even the residue), the *ordinary* plain-rule parameter
  re-comparison, and
  the canonical-index `defEqListI` — lean4lean's `inductiveReduceRec`
  (`Lean4Lean/Inductive/Reduce.lean`) checks only: rule lookup by
  constructor name, `rule.nfields ≤ majorArgs.size`, and
  `ls.length = info.levelParams.length`, then builds the reduct.
  Kept unconditionally: all arity/ctor-identity checks, the inert-rule
  decline, the `stripPis` arity pins, the constructor↔recursor
  level-linkage comparison, the nested-rule comparand
  (`recFireComparands`) value checks, and — a task-#76 finding — the
  parameter comparison for *projection-function* rules: projection
  functions are a setlec-specific recursor encoding (the references
  reduce `.proj` nodes by direct field selection, never splicing the
  outer application's parameters into a reduct), so their parameter
  comparison is part of matching reference behavior, and skipping it
  rejects five good arena/e2e tests (`118/119_reduceCtorParamRefl`,
  `120/121_rTreeRec*`, `080_RBTree`, `nested_rec`, `let_rec_rhs`).
* `majorToCtorNC` (vs `majorToCtorI`): the K-rescue fabrication is
  checked exactly as the official kernel's `toCtorWhenK` does — defeq
  of the major's type against the fabricated constructor's inferred
  type.  Since task #71 the certified `majorToCtorI` runs the same
  reference check too (with the major-slot certificate gated at
  nonzero motives it is load-bearing there as well — the original
  task-#76 finding on arena `bad/098_ruleKbad`); NC differs only in
  dropping the `proofIrrelI` soundness certificate that follows it.
  The eta fabrication runs `structEtaCertWithNC`.
* `whnfAppNC`/`betaPeelNC` (vs `whnfAppI`/`betaPeelI`): the
  possibly-Prop per-binder argument re-check before beta — the
  references beta-reduce unconditionally (lean4lean `whnfCore`).
* `inferSpineNC` (vs `inferSpineI`): the possibly-Prop-gated
  per-argument infer+defeq residue — the references never re-check
  application arguments during inference (lean4lean `inferType` with
  `inferOnly := true`).
* `structEtaCertWithNC` (vs `structEtaCertWithI`): the type-former
  telescope certification (`iotaCertsI` on `tyT`) and the
  per-projection telescope certifications (`structEtaProjCertsI`) —
  lean4lean's `tryEtaStructCore` checks only that the types are defeq
  (which our head/level/parameter comparison mirrors) and the
  per-field `isDefEq` against the projections (kept).
* `structUnitCertNC` (vs `structUnitCertI`): the type-former telescope
  certification — lean4lean's `isDefEqUnitLike` checks exactly the
  unit-like shape and the defeq of the two types (kept).

Not skipped (also proof-only, but outside the task-#76 site list —
reported as residue): `projCertI`, the possibly-Prop projection
reduction certificate in the `whnfCoreBody` proj clause; `pairEtaCertI`
performs no work the references' `tryEtaStructCore` would not.
-/

namespace Setlec

/-- Cert-skipping twin of `inferSpineI`: the telescope walk without the
possibly-Prop argument re-checks (references are infer-only here). -/
def inferSpineNC (r : CoreFnsI) (depth : Nat) :
    EIdx → List EIdx → List EIdx → CheckIM EIdx
  | ty, acc, [] => instListM ty acc
  | ty, acc, a :: rest => do
    match ← viewI ty with
    | some (.forallE _ _dom body _) =>
      inferSpineNC r depth body (a :: acc) rest
    | _ => do
      let ty' ← instListM ty acc
      let w ← r.whnf depth ty'
      match ← viewI w with
      | some (.forallE _ _dom body _) =>
        inferSpineNC r depth body [a] rest
      | _ => throw (.invalid "function expected")

/-- Cert-skipping twin of `structEtaCertWithI`: keeps the guard, the
level comparison, the parameter comparison and the per-field defeq
against the projections (what lean4lean's `tryEtaStructCore` checks);
skips the type-former and per-projection telescope certifications. -/
def structEtaCertWithNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b wtb : EIdx) : CheckIM Bool := do
  match ← withStore (fun st => st.nodes[st.getAppFnI a]?) with
  | some (.const c us) =>
    match fe.find? c with
    | some (.ctorInfo cvc cnP cnF) => do
      let aargs ← withStore (·.getAppArgsI a)
      if aargs.length = cnP + cnF then
        match ← withStore (fun st => st.nodes[st.getAppFnI wtb]?) with
        | some (.const T us') =>
          match fe.find? T with
          | some (.indInfo cvT caps) => do
            let targs ← withStore (·.getAppArgsI wtb)
            if caps.eta = true ∧ caps.etaCtor = c ∧
                caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                reservedBasisNames.contains T = false ∧
                reservedBasisNames.contains c = false ∧
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

/-- Cert-skipping twin of `structEtaCertI`. -/
def structEtaCertNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  let tb ← r.infer depth b
  let wtb ← r.whnf depth tb
  structEtaCertWithNC r fe depth a b wtb

/-- Cert-skipping twin of `structUnitCertI`: keeps the unit-like shape
guard and the defeq of the two whnf'd types (what lean4lean's
`isDefEqUnitLike` checks); skips the type-former telescope
certification. -/
def structUnitCertNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  let ta ← r.infer depth a
  let wta ← r.whnf depth ta
  match ← withStore (fun st => st.nodes[st.getAppFnI wta]?) with
  | some (.const T us') =>
    match fe.find? T with
    | some (.indInfo cvT caps) => do
      let targs ← withStore (·.getAppArgsI wta)
      if caps.unitlike = true ∧
          reservedBasisNames.contains T = false ∧
          targs.length = caps.unitParams ∧
          us'.length = cvT.levelParams.length ∧
          (cvT.type.stripPis caps.unitParams).isSome = true then do
        let tb ← r.infer depth b
        let wtb ← r.whnf depth tb
        r.defeq depth wta wtb
      else pure false
    | _ => pure false
  | _ => pure false

/-- Cert-skipping twin of `stuckIrrelI` (`pairEtaCertI` and
`proofIrrelI` do no proof-only work and are reused). -/
def stuckIrrelNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  if ← pairEtaCertI r fe depth a b then pure true
  else if ← pairEtaCertI r fe depth b a then pure true
  else if ← structEtaCertNC r fe depth a b then pure true
  else if ← structEtaCertNC r fe depth b a then pure true
  else if ← structUnitCertNC r fe depth a b then pure true
  else proofIrrelI r fe depth a b

/-- Twin of `majorToCtorI` for the cert-skipping mode.  The K-rescue
fabrication check is the official kernel's `toCtorWhenK` test — defeq
of the (whnf'd) major's type against the fabricated constructor
application's inferred type, which compares the indices.  Since task
#71 the certified `majorToCtorI` runs the same reference check
(load-bearing with the major-slot telescope certificate gated at
nonzero motives; arena `bad/098_ruleKbad`); NC differs only in
dropping the `proofIrrelI` soundness certificate that follows it.
The eta fabrication runs `structEtaCertWithNC` (the reference's
`toCtorWhenStruct` checks only type shape; the NC cert keeps the
parameter/field defeqs and drops the telescope certifications). -/
def majorToCtorNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : EIdx) :
    CheckIM EIdx := do
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
            match ← withStore (fun st => st.nodes[st.getAppFnI tmaj]?) with
            | some (.const T' ust) =>
              if T' = T ∧ cvj.levelParams.length = ust.length then do
                let margs ← withStore (·.getAppArgsI tmaj)
                let h ← internI (.const rl.ctor ust)
                let fab ← mkAppNM h (margs.take cnP)
                if ← withStore (fun st => st.wscopedBI depth fab &&
                    st.looseBVarsBoundedI 0 fab &&
                    (st.fvarLeavesI fab).all
                      (fun l => (st.fvarLeavesI major).contains l)) then do
                  -- official `toCtorWhenK`: the fabricated constructor's
                  -- type must be defeq to the major's (indices match)
                  let tfab ← r.infer depth fab
                  if ← r.defeq depth tmaj tfab then pure fab
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
              Name.isProjFnShape recName = false ∧
              piResultIsProp cvT.type = false then do
            let tmaj₀ ← r.infer depth major
            let tmaj ← r.whnf depth tmaj₀
            match ← withStore (fun st => st.nodes[st.getAppFnI tmaj]?) with
            | some (.const T' ust) => do
              let margs ← withStore (·.getAppArgsI tmaj)
              let ustL ← readbackLevelsM ust
              if T' = T ∧ margs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length then do
                let projs ← projAppsI T ust margs major
                  (List.range caps.etaFields)
                let h ← internI (.const caps.etaCtor ust)
                let fab ← mkAppNM h (margs ++ projs)
                if ← withStore (fun st => st.wscopedBI depth fab &&
                    st.looseBVarsBoundedI 0 fab &&
                    (st.fvarLeavesI fab).all
                      (fun l => (st.fvarLeavesI major).contains l)) then do
                  if ← structEtaCertWithNC r fe depth fab major tmaj then
                    pure fab
                  else if caps.etaFields = 0 ∧
                      cvj.levelParams.length = ust.length ∧
                      piResultNeverZero cvT.levelParams ustL cvT.type
                        = true then
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

/-- Cert-skipping twin of `iotaRecI`: keeps every check lean4lean's
`inductiveReduceRec` performs (rule lookup, arities, level count via
the linkage below) plus the verdict-relevant level linkage, the
nested-rule comparand values and the projection-rule parameter
comparison (projection functions are a setlec-specific recursor
encoding — the references reduce `.proj` nodes by direct field
selection and never splice the outer application's parameters into
the reduct, so the comparison is part of matching their behavior;
empirically, skipping it rejects five good arena/e2e tests); skips
the two telescope certifications, the ordinary plain-rule parameter
re-comparison and the canonical-index comparison. -/
def iotaRecNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (e : EIdx) :
    CheckIM (Option EIdx) := do
  match ← withStore (fun st => st.nodes[st.getAppFnI e]?) with
  | some (.const c us) =>
    match fe.find? c with
    | some (.recInfo cv mI rP rules) => do
      let args ← withStore (·.getAppArgsI e)
      if args.length = mI + 1 then do
        let bvar0 ← internI (.bvar 0)
        let major₀ ← r.whnf depth (args.getD mI bvar0)
        let major₁ ← litMajorToCtorI r fe depth major₀
        let major ← majorToCtorNC r fe depth c rules major₁
        match ← withStore (fun st => st.nodes[st.getAppFnI major]?) with
        | some (.const cj usj) =>
          match fe.find? cj with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cj) with
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
                let cmpLvls : List LIdx ←
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
                       (args.take mI) (mI - 1) pins
                     defEqListI r fe depth (margs.take rl.ctorParams) cmpArgs
                   | _ =>
                     if Name.isProjFnShape c then
                       defEqListI r fe depth (margs.take rl.ctorParams)
                         (args.take rl.ctorParams)
                     else pure true
                 if cmpOk then do
                  let rhs ← ruleRhsAtM fe c cj us
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

/-- Cert-skipping twin of `whnfAppI`: an annotated λ-binder always
beta-reduces (no possibly-Prop argument re-check). -/
def whnfAppNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    EIdx → List EIdx → CheckIM EIdx
  | v, [] => pure v
  | v, a :: rest => do
    match ← viewI v with
    | some (.lam _ _ty body mb) =>
      match mb.cod with
      | some _ => betaPeelNC r fe depth body [a] rest
      | none => do
        let fa ← internI (.app v a)
        mkAppNM fa rest
    | _ => do
      let fa ← internI (.app v a)
      match ← iotaRecNC r fe depth fa with
      | some e'' => do
        let v' ← r.whnfCore depth e''
        whnfAppNC r fe depth v' rest
      | none => whnfAppNC r fe depth fa rest
termination_by _ args => (args.length, 0)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

/-- Cert-skipping twin of `betaPeelI`. -/
def betaPeelNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    EIdx → List EIdx → List EIdx → CheckIM EIdx
  | t, acc, [] => do
    let e' ← instListM t acc
    r.whnfCore depth e'
  | t, acc, a :: rest => do
    match ← viewI t with
    | some (.lam _ _ty body mb) =>
      match mb.cod with
      | some _ => betaPeelNC r fe depth body (a :: acc) rest
      | none => do
        let f' ← instListM t acc
        let fa ← internI (.app f' a)
        mkAppNM fa rest
    | _ => do
      let e' ← instListM t acc
      let v ← r.whnfCore depth e'
      whnfAppNC r fe depth v (a :: rest)
termination_by _ _acc args => (args.length, 1)
decreasing_by
  all_goals first
    | (apply Prod.Lex.left; simp; done)
    | (apply Prod.Lex.right' <;> simp)

end

/-- Cert-skipping twin of `whnfCoreBodyI` (only the app clause differs,
through `whnfAppNC`; the possibly-Prop projection certificate
`projCertI` is outside the task-#76 site list and kept). -/
def whnfCoreBodyNC (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => do
    match ← viewI e with
    | some (.sort _) | some (.fvar ..) | some (.forallE ..)
    | some (.lam ..) | some (.const ..) | some (.lit _) => pure e
    | some (.app _ _) => do
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let v ← r.whnfCore depth h
      whnfAppNC r fe depth v args
    | some (.proj sn i pe) => do
      let e' ← r.whnf depth pe
      let e' ← projLitToCtorI r fe depth e'
      match fe.findProj? sn i with
      | some entry =>
        match ← withStore (fun st => st.nodes[st.getAppFnI e']?) with
        | some (.const c us) => do
          let args ← withStore (·.getAppArgsI e')
          if entry.native ∧ c = entry.ctor ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length then do
            let mx ← substLevelTreeM entry.levelParams us
              entry.structSort
            let bvar0 ← internI (.bvar 0)
            let arg := args.getD (entry.numParams + i) bvar0
            if ← isNonZeroLM mx then r.whnfCore depth arg
            else do
              let fl ← substLevelTreeM entry.levelParams us entry.fieldSort
              if ← projCertI r fe depth e' i fl
                  mx entry.numParams then
                r.whnfCore depth arg
              else internI (.proj sn i e')
          else internI (.proj sn i e')
        | _ => internI (.proj sn i e')
      | none => internI (.proj sn i e')
    | some (.letE _ _ v b) => do
      let e' ← inst1M b v
      r.whnfCore depth e'
    | some (.bvar _) =>
      throw (.notImplemented "whnf beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Cert-skipping twin of `inferBodyI` (only the app clause differs,
through `inferSpineNC`). -/
def inferBodyNC (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → CheckIM EIdx :=
  fun depth e => do
    match ← viewI e with
    | some (.sort u) => do
      let su ← internLM (.succ u)
      internI (.sort su)
    | some (.fvar idx _ ty) =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | some (.const n us) => do
      match fe.find? n with
      | none => throw (.invalid s!"unknown constant {n}")
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        constTyAtM fe n us
    | some (.lit (.natVal _)) => do
      if natLitSupportedF fe then internI (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | some (.lit (.strVal _)) => do
      if strLitSupportedF fe then internI (.const stringName [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | some (.forallE _ ty _ mb) => do
      match mb.cod with
      | some v => do
        let tty ← r.infer depth ty
        let wtty ← r.whnf depth tty
        match ← viewI wtty with
        | some (.sort u) => do
          let iv ← internLM (.imax u v)
          internI (.sort iv)
        | _ => throw (.invalid "expected a sort")
      | none => throw (.internal "unannotated ∀-binder reached inferType")
    | some (.lam n ty body mb) => do
      match mb.cod with
      | some v => do
        let tty ← r.infer depth ty
        let wtty ← r.whnf depth tty
        match ← viewI wtty with
        | some (.sort u) => do
          -- Binder-telescope loop (task #72), shared with `inferBodyI`.
          let fv ← internI (.fvar depth n ty)
          let fuel ← withStore (·.nodes.size)
          inferLamsI r depth fuel body 1 [fv] [(n, ty, mb, v, u)]
        | _ => throw (.invalid "expected a sort")
      | none => throw (.internal "unannotated λ-binder reached inferType")
    | some (.app _ _) => do
      let h ← withStore (fun st => st.getAppFnI e)
      let args ← withStore (·.getAppArgsI e)
      let tf ← r.infer depth h
      inferSpineNC r depth tf [] args
    | some (.proj _sn i pe) => do
      let tpe ← r.infer depth pe
      let te ← r.whnf depth tpe
      match ← withStore (fun st => st.nodes[st.getAppFnI te]?) with
      | some (.const T us) =>
        match fe.findProj? T i with
        | some entry => do
          let targs ← withStore (·.getAppArgsI te)
          if entry.native ∧ targs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            let pty ← constTyAtM fe (projFnName T i) us
            match ← piResidualM pty (targs ++ [pe]) with
            | some resTy => pure resTy
            | none => throw (.internal "malformed projection entry")
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | some (.letE _ _ v b) => do
      let e' ← inst1M b v
      r.infer depth e'
    | some (.bvar _) =>
      throw (.notImplemented "inferType beyond the supported fragment")
    | none => throw (.internal "interned node missing")

/-- Cert-skipping twin of `defeqBodyI` (only the stuck-term fallback
differs, through `stuckIrrelNC`). -/
def defeqBodyNC (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → EIdx → CheckIM Bool :=
  fun depth a b => do
    if a == b then pure true else
    let a' ← r.whnfCore depth a
    let b' ← r.whnfCore depth b
    if a' == b' then pure true else
    if ← proofIrrelI r fe depth a' b' then pure true else
    match ← reduceNatI r fe depth a' with
    | some a₂ => r.defeq depth a₂ b'
    | none =>
    match ← reduceNatI r fe depth b' with
    | some b₂ => r.defeq depth a' b₂
    | none =>
    match ← unfoldDefinitionI fe a', ← unfoldDefinitionI fe b' with
    | some a₂, none => r.defeq depth a₂ b'
    | none, some b₂ => r.defeq depth a' b₂
    | some a₂, some b₂ => do
      let ha ← withStore (fun st => headHintI fe st a')
      let hb ← withStore (fun st => headHintI fe st b')
      if ReducibilityHint.lt hb ha then r.defeq depth a₂ b'
      else if ReducibilityHint.lt ha hb then r.defeq depth a' b₂
      else if ReducibilityHint.sameRegular ha hb &&
          (← withStore (sameConstHeadsI · a' b')) then do
        if ← defeqSpineI r fe depth a' b' then pure true
        else r.defeq depth a₂ b₂
      else r.defeq depth a₂ b₂
    | none, none =>
    match ← viewI a', ← viewI b' with
    | some (.sort u), some (.sort v) => do
      liftFueled "level comparison" (← isEquivLM u v)
    | some (.lit l₁), some (.lit l₂) => pure (l₁ == l₂)
    | some (.lit (.natVal n)), some (.const c us) =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrelNC r fe depth a' b'
    | some (.const c us), some (.lit (.natVal n)) =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrelNC r fe depth a' b'
    | some (.lit (.natVal nn)), some (.app f x) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if c = natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth kl x
        else stuckIrrelNC r fe depth a' b'
      | _, _ => stuckIrrelNC r fe depth a' b'
    | some (.app f x), some (.lit (.natVal nn)) => do
      match nn, ← viewI f with
      | k + 1, some (.const c []) =>
        if c = natSuccName then do
          let kl ← internI (.lit (.natVal k))
          r.defeq depth x kl
        else stuckIrrelNC r fe depth a' b'
      | _, _ => stuckIrrelNC r fe depth a' b'
    | some (.lit (.strVal s)), some (.app fO _x) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if cO = stringOfListName ∧ usO = [] ∧ strLitSupportedF fe then do
          let sc ← internExprM (strLitToConstructor s)
          r.defeq depth sc b'
        else stuckIrrelNC r fe depth a' b'
      | _ => stuckIrrelNC r fe depth a' b'
    | some (.app fO _x), some (.lit (.strVal s)) => do
      match ← viewI fO with
      | some (.const cO usO) =>
        if cO = stringOfListName ∧ usO = [] ∧ strLitSupportedF fe then do
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
    | some (.forallE n₁ ty₁ body₁ m₁), some (.forallE n₂ ty₂ body₂ m₂) => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ => do
        liftFueled "level comparison" (← isEquivLM v₁ v₂)
      | _, _ => throw (.internal "unannotated ∀-binder reached isDefEq")
    | some (.lam n₁ ty₁ body₁ m₁), some (.lam n₂ ty₂ body₂ m₂) => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let fv₁ ← internI (.fvar depth n₁ ty₁)
      let b₁ ← inst1M body₁ fv₁
      let fv₂ ← internI (.fvar depth n₂ ty₂)
      let b₂ ← inst1M body₂ fv₂
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ => do
        liftFueled "level comparison" (← isEquivLM v₁ v₂)
      | _, _ => throw (.internal "unannotated λ-binder reached isDefEq")
    | some (.app f₁ a₁), some (.app f₂ a₂) => do
      if ← r.defeq depth f₁ f₂ then do
        if ← r.defeq depth a₁ a₂ then
          pure true
        else stuckIrrelNC r fe depth a' b'
      else stuckIrrelNC r fe depth a' b'
    | some (.proj _s₁ i₁ e₁), some (.proj _s₂ i₂ e₂) => do
      if i₁ == i₂ then do
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrelNC r fe depth a' b'
      else stuckIrrelNC r fe depth a' b'
    | some (.lam n₁ ty₁ body₁ m₁), _ => do
      if ← etaCertI r fe depth n₁ ty₁ body₁ m₁ b' then pure true
      else stuckIrrelNC r fe depth a' b'
    | _, some (.lam n₂ ty₂ body₂ m₂) => do
      if ← etaCertI r fe depth n₂ ty₂ body₂ m₂ a' then pure true
      else stuckIrrelNC r fe depth a' b'
    | some _, some _ => stuckIrrelNC r fe depth a' b'
    | _, _ => throw (.internal "interned node missing")

/-- Tie the cert-skipping bodies at the memoizing state monad (the
`whnf` and `annotate` bodies are the certified ones — their behavior
differences come entirely through the record).  The consistency proofs
are pinned to `coreKnotI`; this knot is measurement-only. -/
def coreKnotNC (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    { whnfCore := memoEI (·.whnfCoreC)
        (fun st mp => { st with whnfCoreC := mp })
        (fun d e => whnfCoreBodyNC (coreKnotNC fe fuel) fe d e)
      whnf := memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
        (fun d e => whnfBodyI (coreKnotNC fe fuel) fe d e)
      infer := memoEI (·.inferC) (fun st mp => { st with inferC := mp })
        (fun d e => inferBodyNC (coreKnotNC fe fuel) fe d e)
      defeq := memoBI
        (fun d a b => defeqBodyNC (coreKnotNC fe fuel) fe d a b)
      annotate := memoEI (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI (coreKnotNC fe fuel) fe d e) }

end Setlec
