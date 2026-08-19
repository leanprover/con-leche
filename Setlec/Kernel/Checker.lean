import Setlec.Kernel.Env
import Setlec.Kernel.TypeChecker

/-!
# The checker

`checkDecl` checks one declaration against the current environment and, on
success, returns the extended environment.  `checkDecls` folds it over a list
of declarations, starting from the empty environment.

Currently supported: `def` declarations in the sort fragment.  Axioms and
theorems are declined.  Verification: `Setlec.Verify.Checker` and
`Setlec.Model.Consistency`.
-/

namespace Setlec

/-- Checks common to all declarations: fresh name, well-formed universe
parameters, and a type that is a type and mentions only declared
parameters.  Returns the constant with its type **annotated**
(`annotate`); the guards run on the annotated type. -/
def checkConstantVal (env : Env) (cv : ConstantVal) : CheckM ConstantVal := do
  if (env.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let type ← annotate env 0 cv.type
  unless type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless type.constsResolve env do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let stype ← inferType env 0 type
  let _u ← ensureSort env 0 stype
  pure { cv with type := type }

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (env : Env) (d : Declaration) : CheckM Env := do
  match d with
  | .defnDecl cv value =>
    let cv ← checkConstantVal env cv
    unless value.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in value of {cv.name}")
    if value.hasFvar then
      throw (.invalid s!"unexpected free variable in value of {cv.name}")
    let value ← annotate env 0 value
    unless value.allLevelParamsDefined cv.levelParams do
      throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
    unless value.constsResolve env do
      throw (.invalid s!"unknown constant in value of {cv.name}")
    let vtype ← inferType env 0 value
    unless ← isDefEq env 0 vtype cv.type do
      throw (.invalid s!"type mismatch in definition {cv.name}")
    pure ⟨.defnInfo cv value :: env.consts⟩
  | .thmDecl cv value =>
    let cv ← checkConstantVal env cv
    -- the type of a theorem must be a proposition
    let stype ← inferType env 0 cv.type
    let u ← ensureSort env 0 stype
    unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
      throw (.invalid s!"type of theorem {cv.name} is not a proposition")
    unless value.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in value of {cv.name}")
    if value.hasFvar then
      throw (.invalid s!"unexpected free variable in value of {cv.name}")
    let value ← annotate env 0 value
    unless value.allLevelParamsDefined cv.levelParams do
      throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
    unless value.constsResolve env do
      throw (.invalid s!"unknown constant in value of {cv.name}")
    let vtype ← inferType env 0 value
    unless ← isDefEq env 0 vtype cv.type do
      throw (.invalid s!"type mismatch in theorem {cv.name}")
    pure ⟨.thmInfo cv value :: env.consts⟩
  | .axiomDecl cv => throw (.notImplemented s!"axiom declaration ({cv.name})")
  | .basisDecl kind =>
    -- Install the pinned (pre-annotated) basis block; the frontend has
    -- already matched the incoming record against the pinned shapes.
    kind.declsA.foldlM (fun env ci => do
      unless (env.find? ci.name).isNone do
        throw (.invalid s!"duplicate declaration {ci.name}")
      pure (⟨ci :: env.consts⟩ : Env)) env
  | .indDecl _block =>
    -- Modeled inductive blocks: installation lands with the
    -- model-checking machinery; decline until then.
    throw (.notImplemented "modeled inductive declaration")

/-- Build the expected statement of the model's `iota_j` theorem for one
recursor rule (non-indexed, single motive): the rule's λ-telescope,
domains renamed to the `_model` family, closing over
`R._model p⃗ M m⃗ (C._model p⃗ x⃗) = rhs-body`. -/
def buildIotaStmt (f : Name → Name) (recName ctorName : Name)
    (recLPs ctorLPs : List Name) (nP nM nm nF : Nat)
    (recTy ctorTy : Expr) (ruleRhs : Expr) : Option Expr := do
  let (binders, body) ← ruleRhs.stripLams (nP + nM + nm + nF)
  -- binder infos follow the recursor's telescope (then the
  -- constructor's fields), not the rule's λs
  let bisR ← recTy.piBinderInfos (nP + nM + nm)
  let bisC ← ctorTy.piBinderInfos (nP + nF)
  let bis := bisR ++ bisC.drop nP
  let binders := (binders.zip bis).map fun (b, bi) => (b.1, b.2.1, bi)
  let (_, mdom, _) ← binders[nP]?
  let ℓ ← mdom.resultSort
  let depth := nP + nM + nm + nF
  let pArgs := (List.range nP).map fun k => Expr.bvar (depth - 1 - k)
  let mmArgs := (List.range (nM + nm)).map fun k =>
    Expr.bvar (depth - 1 - nP - k)
  let xArgs := (List.range nF).map fun k => Expr.bvar (nF - 1 - k)
  let ctorApp := Expr.mkAppN (.const (f ctorName) (ctorLPs.map .param))
    (pArgs ++ xArgs)
  let lhs := Expr.mkAppN (.const (f recName) (recLPs.map .param))
    (pArgs ++ mmArgs ++ [ctorApp])
  let motiveBVar := Expr.bvar (nF + nm + (nM - 1))
  let α := Expr.app motiveBVar ctorApp
  let rhs := body.renameConsts f
  let eqApp := Expr.mkAppN (.const eqName [ℓ]) [α, lhs, rhs]
  pure (binders.foldr
    (fun (b : Name × Expr × BinderInfo) acc =>
      .forallE b.1 (b.2.1.renameConsts f) acc ⟨b.2.2, none⟩) eqApp)

/-- Check and install a modeled inductive block: every member is
checked against its `_model` counterpart (type up to the public↔model
renaming, iota rules against the model's `iota_j` theorems), then
stored as a real inductive-kind constant.  Not yet wired into
`checkDecl` — the soundness proof accompanies the wiring. -/
def checkIndDecl (env : Env) (block : List ConstantInfo) : CheckM Env := do
  let blockNames := block.map (·.name)
  let f : Name → Name := fun n =>
    if blockNames.contains n then n.str "_model" else n
  block.foldlM (fun env' ci => do
    let cv := ci.toConstantVal
    unless (env'.find? cv.name).isNone do
      throw (.invalid s!"duplicate declaration {cv.name}")
    if reservedBasisNames.contains cv.name then
      throw (.invalid s!"reserved basis name {cv.name}")
    unless Name.nodup cv.levelParams do
      throw (.invalid s!"duplicate universe parameters in {cv.name}")
    unless cv.type.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in type of {cv.name}")
    if cv.type.hasFvar then
      throw (.invalid s!"unexpected free variable in type of {cv.name}")
    unless cv.type.allLevelParamsDefined cv.levelParams do
      throw (.invalid s!"undeclared universe parameter in {cv.name}")
    unless cv.type.constsResolve env' do
      throw (.invalid s!"unknown constant in type of {cv.name}")
    let tyA ← annotate env' 0 cv.type
    -- the model counterpart
    let some (.defnInfo cvm _mval) := env'.find? (cv.name.str "_model")
      | throw (.notImplemented s!"missing model for {cv.name}")
    unless cvm.levelParams = cv.levelParams do
      throw (.notImplemented s!"model level parameters mismatch for {cv.name}")
    unless (tyA.renameConsts f) == cvm.type do
      throw (.notImplemented s!"model type mismatch for {cv.name}")
    let cvA : ConstantVal := ⟨cv.name, cv.levelParams, tyA⟩
    match ci with
    | .indInfo _ => pure (⟨.indInfo cvA :: env'.consts⟩ : Env)
    | .ctorInfo _ nP nF => pure ⟨.ctorInfo cvA nP nF :: env'.consts⟩
    | .recInfo _ nP nM nm ni rules => do
      unless ni = 0 do throw (.notImplemented "indexed recursor")
      unless nM = 1 do throw (.notImplemented "multiple motives")
      -- the model's value must be a λ-telescope matching the rule
      -- domains (its interpretation determines argument domains)
      -- provisional self with *no* rules: rule right-hand sides may
      -- mention the recursor, but nothing during their annotation may
      -- depend on its (yet unchecked) rules
      let envSelf : Env := ⟨.recInfo cvA nP nM nm ni [] :: env'.consts⟩
      let rec goRules : Nat → List RecRule → CheckM (List RecRule)
        | _, [] => pure []
        | j, r :: rest => do
          let some (.ctorInfo cvj cnP cnF) := env'.find? r.ctor
            | throw (.invalid s!"iota rule constructor {r.ctor} not stored")
          unless cnP = nP do
            throw (.notImplemented "constructor/recursor parameter mismatch")
          unless r.nfields = cnF do
            throw (.invalid "rule field count mismatch")
          unless r.rhs.looseBVarsBounded 0 do
            throw (.invalid s!"loose bound variable in rule of {cv.name}")
          if r.rhs.hasFvar then
            throw (.invalid s!"free variable in rule of {cv.name}")
          unless r.rhs.allLevelParamsDefined cv.levelParams do
            throw (.invalid s!"undeclared universe parameter in rule of {cv.name}")
          unless r.rhs.constsResolve envSelf do
            throw (.invalid s!"unknown constant in rule of {cv.name}")
          let rhsA ← annotate envSelf 0 r.rhs
          -- the rule's λ-domains pin down what the model's iota
          -- theorem quantifies over; they must match the recursor
          -- type's domains (prefix) and the constructor type's field
          -- domains (lifted past motive and minors) — the same
          -- telescopes the iota certificates certify the spines
          -- against
          let some (rbinders, _) := rhsA.stripLams (nP + nM + nm + cnF)
            | throw (.notImplemented s!"rule of {cv.name} is not a lambda telescope")
          let some (tbinders, _) := tyA.stripPis (nP + nM + nm)
            | throw (.notImplemented s!"type of {cv.name} is not a pi telescope")
          let some (cbinders, _) := cvj.type.stripPis (cnP + cnF)
            | throw (.notImplemented s!"type of {r.ctor} is not a pi telescope")
          unless (List.range (nP + nM + nm)).all (fun i =>
              match rbinders[i]?, tbinders[i]? with
              | some rb, some tb => rb.2.1 == tb.2.1
              | _, _ => false) do
            throw (.notImplemented s!"rule domain mismatch with recursor type for {cv.name}")
          unless (List.range cnF).all (fun i =>
              match rbinders[nP + nM + nm + i]?, cbinders[cnP + i]? with
              | some rb, some cb =>
                rb.2.1 == cb.2.1.liftLooseBVars (nM + nm) i
              | _, _ => false) do
            throw (.notImplemented s!"rule field domain mismatch with constructor type for {cv.name}")
          -- infer the rule's type: soundness interprets the (λ-tower)
          -- right-hand side through this inference
          let _rhsTy ← inferType envSelf 0 rhsA
          let some stmtRaw := buildIotaStmt f cv.name r.ctor
              cv.levelParams cvj.levelParams nP nM nm cnF
              tyA cvj.type r.rhs
            | throw (.notImplemented "iota statement construction")
          let stmtA ← annotate env' 0 stmtRaw
          let thmName := (cv.name.str "_model").str s!"iota_{j}"
          let some (.thmInfo cvt _) := env'.find? thmName
            | throw (.notImplemented s!"missing iota theorem {thmName}")
          unless cvt.levelParams = cv.levelParams do
            throw (.notImplemented s!"iota theorem level mismatch {thmName}")
          unless cvt.type == stmtA do
            throw (.notImplemented s!"iota statement mismatch for {thmName}")
          let rest' ← goRules (j + 1) rest
          pure ({ r with rhs := rhsA } :: rest')
      let rules' ← goRules 0 rules
      pure ⟨.recInfo cvA nP nM nm ni rules' :: env'.consts⟩
    | _ => throw (.invalid s!"non-inductive member {cv.name} in block")
    ) env

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDecls (ds : List Declaration) : CheckM Env :=
  ds.foldlM checkDecl Env.empty

end Setlec
