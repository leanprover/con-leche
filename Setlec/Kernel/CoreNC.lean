import Setlec.Kernel.CoreI

/-!
# The cert-skipping interned core (task #76; task #147: `--no-model`)

**The unverified lane.**  Originally the `SETLEC_NO_PROOF_CERTS=1`
measurement mode (task #76); since task #147 it is the engine of the
`--no-model` mode — the cert-skipping internal knot (`coreKnotNC`,
infer-only inside reduction exactly as the reference kernels are) under
a checking-mode front-door knot (`coreKnotFNC`, the task-#134 pattern:
the declaration's own term is checked in full, per-argument application
checks included).  Twins of the interned core bodies
(`Setlec/Kernel/CoreI.lean`) with the infer/defeq calls removed that
exist *only* to feed the soundness proofs — the reference kernels
(official C++ kernel, lean4lean) do not perform them, so skipping them
cannot change the verdict on valid input.  The point of this mode is a
fair performance comparison: the instruction delta between the default
(certified) knot and this knot is the *verification tax*; the residual
gap to the reference kernels is engineering quality.

None of the consistency proofs cover this knot.  The default path
(`coreKnotI` → `sharedOps` → `checkDeclsSP`) is untouched by this
file; Main reaches these bodies only through the `--no-model` driver
(`Setlec/Kernel/CheckerNC.lean`, task #147).

Skipped here (each site cites why it is proof-only):

* `iotaRecNC` (vs `iotaRecI`): the per-fire recursor-telescope and
  constructor-telescope certifications (`iotaCertsI`; since task #100
  de-gating the certified pipeline runs them ungated on every slot —
  NC skips them entirely), the *ordinary* plain-rule parameter
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
* `whnfAppNC`/`betaPeelNC` (vs `whnfAppI`/`betaPeelI`): the per-binder
  argument re-check before beta (unconditional in the certified core
  since the task-#100 de-gating) — the references beta-reduce
  unconditionally (lean4lean `whnfCore`).
* `inferSpineNC` (vs `inferSpineI`): the per-argument infer+defeq
  (likewise unconditional since task #100) — the references never
  re-check application arguments during inference (lean4lean
  `inferType` with `inferOnly := true`).
* `structEtaCertWithNC` (vs `structEtaCertWithI`): the type-former
  telescope certification (`iotaCertsI` on `tyT`) and the
  per-projection telescope certifications (`structEtaProjCertsI`) —
  lean4lean's `tryEtaStructCore` checks only that the types are defeq
  (which our head/level/parameter comparison mirrors) and the
  per-field `isDefEq` against the projections (kept).
* `structUnitCertNC` (vs `structUnitCertI`): the type-former telescope
  certification — lean4lean's `isDefEqUnitLike` checks exactly the
  unit-like shape and the defeq of the two types (kept).
* `whnfCoreBodyNC`'s proj clause (vs `whnfCoreStepI`'s): the
  constructor-telescope certification `projTeleCertI` (task #126) — the
  same `iotaCertsI` family skipped at every other site above.  It was
  added so that a *typing derivation* for `proj_i (C p⃗ x⃗) ↦ x_i` can be
  rebuilt from what the checker records (the projection rules' four
  premises are that telescope's domains); the references reduce a
  `.proj` node by direct field selection and certify nothing
  (lean4lean `projectCore`, official kernel `whnf_core`'s proj case),
  so it is proof-only in exactly the task-#76 sense.
* `inferBodyNC`'s proj clause (vs `inferBodyI`'s): the
  parameter-telescope certification `projParamCertI` (task #129) — the
  inference-path sibling of the entry above, and the same `iotaCertsI`
  family.  The judgement was made deliberately, not by analogy: the
  call exists so that `projFst`/`projSnd`'s first two premises
  (`⊢ A : Sort u`, `⊢ B : A → Sort v`) can be read off what the checker
  recorded, and *neither reference infers anything about those
  parameters* — lean4lean's `inferProj` and the official kernel's
  `infer_proj` both peel the telescope with
  `r := binding_body(r).instantiate1 args[i]` for each parameter, with
  no `infer` and no `isDefEq` on `args[i]`; the parameters are
  substituted, never typed.  Keeping the call would put a telescope
  certification in the one mode whose whole purpose is to price them
  out — and, as at `projTeleCertI`, a mode that skips every other
  member of the family and keeps this one reports a meaningless
  number.
* `pairEtaCertNC` (vs `pairEtaCertI`): the projection-entry parameter
  telescope certification `projParamCertI` (task #130) — the third
  member of the same `iotaCertsI` family, added so that `psigmaEta`'s
  first two premises (`⊢ A : Sort u`, `⊢ B : arrow A (Sort v)`) can be
  read off what the checker recorded.  Evidence, read rather than
  inherited: both references' struct-η
  (lean4lean `tryEtaStructCore`, official kernel
  `type_checker::try_eta_struct_core`) run *one* `isDefEq (inferType t)
  (inferType s)` plus a per-field `isDefEq` against the projections;
  neither ever infers or compares the structure type's **parameters**
  on their own, let alone against a telescope.  Our parameter
  comparisons `defeq pα A`/`defeq pβ B` stay — they are the interned
  spelling of that single type-level `isDefEq` and are kept — but the
  telescope walk is proof-only in exactly the task-#76 sense.  Until
  task #130 this mode reused `pairEtaCertI` outright.

Not skipped (also proof-only, but outside the task-#76 site list —
reported as residue): `projCertI`, the possibly-Prop projection
reduction certificate in the `whnfCoreBody` proj clause.
-/

namespace Setlec

/-- Cert-skipping twin of `inferSpineI`: the telescope walk without the
possibly-Prop argument re-checks (references are infer-only here). -/
def inferSpineNC (r : CoreFnsI) (depth : Nat) :
    EIdx → Array EIdx → List EIdx → CheckIM EIdx
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

/-- Cert-skipping twin of `structEtaCertWithI`: keeps the guard, the
level comparison, the parameter comparison and the per-field defeq
against the projections (what lean4lean's `tryEtaStructCore` checks);
skips the type-former and per-projection telescope certifications. -/
def structEtaCertWithNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (a b wtb : EIdx) : CheckIM Bool := do
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

/-- Cert-skipping twin of `pairEtaCertI`: keeps the constructor and
type-head guards, the level comparison, the two parameter comparisons
and the two field defeqs against the projections (all of which the
references' `tryEtaStructCore` performs, the parameter comparisons as
part of its `isDefEq (inferType t) (inferType s)`); skips the
projection-entry parameter telescope certification `projParamCertI`
(task #130). -/
def pairEtaCertNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
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

/-- Cert-skipping twin of `stuckIrrelI` (`proofIrrelI` does no
proof-only work and is reused). -/
def stuckIrrelNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) (a b : EIdx) :
    CheckIM Bool := do
  if ← pairEtaCertNC r fe depth a b then pure true
  else if ← pairEtaCertNC r fe depth b a then pure true
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

/-- Cert-skipping twin of `whnfAppI`: a λ-binder always beta-reduces
(no per-redex argument re-check; since task #100 de-gating the
certified twin re-checks every redex). -/
def whnfAppNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    EIdx → List EIdx → CheckIM EIdx
  | v, [] => pure v
  | v, a :: rest => do
    match ← viewI v with
    | some (.lam _ _ty body _mb) => betaPeelNC r fe depth body [a] rest
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
    | some (.lam _ _ty body _mb) => betaPeelNC r fe depth body (a :: acc) rest
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

/-- Cert-skipping twin of `whnfCoreBodyI`: the app clause differs
through `whnfAppNC`, and the proj clause drops the
constructor-telescope certification `projTeleCertI` (task #126, an
`iotaCertsI` site like every other one this mode skips).  The
possibly-Prop projection certificate `projCertI` is outside the
task-#76 site list and kept. -/
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
      let snn ← readbackNM sn
      match fe.findProj? snn i with
      | some entry =>
        match ← withStore (fun st => st.getNode (st.getAppFnI e')) with
        | some (.const c us) => do
          let args ← withStore (·.getAppArgsI e')
          if entry.native ∧ (← beqNameM c entry.ctor) ∧ i < entry.numFields ∧
              args.length = entry.numParams + entry.numFields ∧
              us.length = entry.levelParams.length then do
            let mx ← substLevelTreeM entry.levelParams us
              entry.structSort
            let bvar0 ← internI (.bvar 0)
            let arg := args.getD (entry.numParams + i) bvar0
            -- task #100 de-gating: ungated, as in `whnfCoreBodyI`
            -- (`projCertI` stays — outside the task-#76 skip list)
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

/-- Cert-skipping twin of `inferBodyI` (the app clause differs, through
`inferSpineNC`; the proj clause drops `projParamCertI`, task #129). -/
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
        let fuel ← withStore (·.nodes.size)
        -- At `.noModel` the ∀-annotation validation is off (task
        -- #161), matching the spec's parity lane.
        inferPisI .noModel r depth fuel body 1 #[fv] [(u, mb.pw)]
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
        let fuel ← withStore (·.nodes.size)
        inferLamsI .noModel r depth fuel body 1 #[fv] [(n, ty, mb)]
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
            let pf ← projFnIdxM T i
            let pty ← constTyAtM fe pf (projFnName Tn i) us
            match ← piResidualM pty (targs ++ [pe]) with
            | some resTy => pure resTy
            | none => throw (.internal "malformed projection entry")
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

/-- Cert-skipping twin of `defeqBodyI` (only the stuck-term fallback
differs, through `stuckIrrelNC`). -/
def defeqStepNC (r : CoreFnsI) (fe : FEnv) (depth : Nat)
    (k : EIdx → EIdx → CheckIM Bool) (a b : EIdx) : CheckIM Bool := do
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
      if ← etaCertI .noModel r fe depth n₁ ty₁ body₁ m₁ b' then pure true
      else stuckIrrelNC r fe depth a' b'
    | _, some (.lam n₂ ty₂ body₂ m₂) => do
      if ← etaCertI .noModel r fe depth n₂ ty₂ body₂ m₂ a' then pure true
      else stuckIrrelNC r fe depth a' b'
    | some _, some _ => stuckIrrelNC r fe depth a' b'
    | _, _ => throw (.internal "interned node missing")

/-- Cert-skipping twin of `defeqLoopI`. -/
def defeqLoopNC (r : CoreFnsI) (fe : FEnv) (depth : Nat) :
    Nat → EIdx → EIdx → CheckIM Bool
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | fl + 1, a, b => defeqStepNC r fe depth (defeqLoopNC r fe depth fl) a b

/-- Cert-skipping twin of `defeqBodyI`. -/
def defeqBodyNC (r : CoreFnsI) (fe : FEnv) : Nat → EIdx → EIdx → CheckIM Bool :=
  fun depth a b => defeqLoopNC r fe depth defeqLoopFuel a b

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

/-- The `--no-model` **checking-mode front-door knot** (task #147; the
task-#134 `coreKnotF` pattern over the cert-skipping internals).
`infer` is the certified `inferBodyI` at `.noModel` — the official
kernel's checking-mode `infer_type_core(e, infer_only := false)`: the
per-argument application re-check runs on the declaration's own term
and propagates down it, while the projection-parameter certification
(task #129, a TT-lane check) is off at `.noModel`.  `annotate` is tied
to itself for the same reason.  `whnfCore`/`whnf`/`defeq` are
`coreKnotNC`'s, so every inference *reduction* performs internally is
infer-only and certificate-free.  The checking-mode inference memo is
`inferFC`, kept apart from the infer-only `inferC` (a type derived
infer-only is never served to a checking-mode query). -/
def coreKnotFNC (fe : FEnv) : Nat → CoreFnsI
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    { whnfCore := (coreKnotNC fe (fuel + 1)).whnfCore
      whnf := (coreKnotNC fe (fuel + 1)).whnf
      defeq := (coreKnotNC fe (fuel + 1)).defeq
      infer := memoEI (·.inferFC) (fun st mp => { st with inferFC := mp })
        (fun d e => inferBodyI .noModel (coreKnotFNC fe fuel) fe d e)
      annotate := memoEI (·.annotC) (fun st mp => { st with annotC := mp })
        (fun d e => annotateBodyI (coreKnotFNC fe fuel) fe d e) }

/-- Drop the checking-mode inference memo.  Its keys are arena
indices, so it must go wherever the index-carrying memos go: at a
declaration boundary and at every snapshot close that truncates tier
two. -/
def flushInferFC : CheckIM Unit :=
  modify fun s => { s with inferFC := {} }

end Setlec
