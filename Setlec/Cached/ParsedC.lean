import Setlec.Cached.CheckerC

/-!
# The cached clone's parsed-declaration driver

The `Expr`-typed shared-state driver (`Setlec/Cached/CheckerC.lean`) is
the *controlled* comparand — it isolates the core.  It is not, however,
the shipped architecture: the production driver
(`Setlec.checkDeclsSP`, task #78) parses **directly into the arena**,
keeps declarations as indices, and runs the per-declaration syntactic
guards as DAG-memoized walks.  On declarations whose term is an
exponentially shared DAG that difference is not a constant factor —
the `Expr`-typed driver cannot check `good/perf/app-lam` at all, with
either core, because `Expr.constsResolveF` and friends are tree walks.

This module gives the clone the same shape, so the architecture
question ("could a computed-field checker replace the arena?") can be
asked against the configuration that actually ships:

* the parse arena is converted **once**, under an index-keyed memo, to
  an `ExprC` DAG (`ofStore`) — the conversion is the clone's
  counterpart of the parse arena itself, and it preserves sharing
  exactly;
* declarations become `DeclC` (`ExprC` in place of `EIdx`);
* `checkDeclSPPlainC` mirrors `checkDeclSPPlain` clause by clause, with
  the guards as the memoized `ExprC` walks and the entry points on
  `ExprC` values — no per-call conversion at the `CheckerOps` seam at
  all for the def/thm/opaque/axiom pipeline.

What is **not** cloned: the task-#64 tier-two snapshot bracket.  It is
an arena mechanism (fork the node table, truncate, promote the stored
output) with no counterpart in a representation that has no node
table; the clone's equivalent is simply that unreferenced intermediate
nodes are collected.  The clone therefore mirrors `checkDeclSPPlain`,
the unbracketed path, which is also the path production takes for the
install-only kinds.  Inductive and basis blocks reuse the `Expr`-level
drivers, exactly as production does.
-/

namespace Setlec.Cached

open Setlec

/-! ## Parsed declarations over `ExprC` -/

/-- `ConstantVal` with the type as an `ExprC`. -/
structure ConstantValC where
  name : Name
  levelParams : List Name
  type : ExprC

/-- A parsed declaration over `ExprC` (the counterpart of `DeclP`). -/
inductive DeclC where
  | axiomDecl (val : ConstantValC)
  | defnDecl (val : ConstantValC) (value : ExprC) (hint : ReducibilityHint)
  | thmDecl (val : ConstantValC) (value : ExprC)
  | opaqueDecl (val : ConstantValC) (value : ExprC)
  | basisDecl (kind : BasisKind)
  | indDecl (block : List ConstantInfo)

/-! ## Converting the parse arena

One index-keyed memo for the whole stream: every shared sub-DAG of the
parse store becomes one `ExprC` object, so the sharing the parser
established survives into the clone's representation.  This is the
clone's counterpart of "the parse arena seeds the run's `IState`". -/

/-- Core of `ofStore` (memoized on the arena index; the level memo is
shared across the traversal).

Non-`partial`: termination is the arena readback's own, copied verbatim
from `EStore.readbackGo` (`Setlec/Kernel/IExpr.lean`) — the traversal
order `(etier e, epos e)` with an `emlt` guard on every child index.
The guards are exactly the ones the interned readback performs, so on a
well-formed parse arena (children are `emlt`-below their parent) no
guard ever fires and the conversion is unchanged; on an ill-formed one
the clause returns `none`, which is what `readbackGo` does too. -/
def ofStoreGo (st : EStore) (memo : Std.HashMap EIdx ExprC)
    (lmemo : Std.HashMap LIdx Level) (e : EIdx) :
    Option ExprC × Std.HashMap EIdx ExprC × Std.HashMap LIdx Level :=
  match memo[e]? with
  | some x => (some x, memo, lmemo)
  | none =>
    match st.getNode e with
    | none => (none, memo, lmemo)
    | some n =>
      let (r, memo, lmemo) :
          Option ExprC × Std.HashMap EIdx ExprC × Std.HashMap LIdx Level :=
        match n with
        | .bvar i => (some (ExprC.mkBVar i), memo, lmemo)
        | .fvar idx nm ty =>
          if _h : emlt ty e then
            match ofStoreGo st memo lmemo ty with
            | (some t, memo, lmemo) =>
              match st.readbackN nm with
              | some n' => (some (ExprC.mkFVar idx n' t), memo, lmemo)
              | none => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .sort u =>
          match EStore.readbackLGo st lmemo u with
          | (some l, lmemo) => (some (ExprC.mkSort l), memo, lmemo)
          | (none, lmemo) => (none, memo, lmemo)
        | .const nm us =>
          match EStore.readbackLList st lmemo us with
          | (some ls, lmemo) =>
            match st.readbackN nm with
            | some n' => (some (ExprC.mkConst n' ls), memo, lmemo)
            | none => (none, memo, lmemo)
          | (none, lmemo) => (none, memo, lmemo)
        | .app f a =>
          if _h : emlt f e ∧ emlt a e then
            match ofStoreGo st memo lmemo f with
            | (some xf, memo, lmemo) =>
              match ofStoreGo st memo lmemo a with
              | (some xa, memo, lmemo) =>
                (some (ExprC.mkApp xf xa), memo, lmemo)
              | (none, memo, lmemo) => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .lam nm ty body mb =>
          if _h : emlt ty e ∧ emlt body e then
            match ofStoreGo st memo lmemo ty with
            | (some xt, memo, lmemo) =>
              match ofStoreGo st memo lmemo body with
              | (some xb, memo, lmemo) =>
                match st.readbackN nm with
                | some n' =>
                  (some (ExprC.mkLam n' xt xb ⟨mb.bi, mb.pw⟩), memo, lmemo)
                | none => (none, memo, lmemo)
              | (none, memo, lmemo) => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .forallE nm ty body mb =>
          if _h : emlt ty e ∧ emlt body e then
            match ofStoreGo st memo lmemo ty with
            | (some xt, memo, lmemo) =>
              match ofStoreGo st memo lmemo body with
              | (some xb, memo, lmemo) =>
                match st.readbackN nm with
                | some n' =>
                  (some (ExprC.mkForallE n' xt xb ⟨mb.bi, mb.pw⟩), memo, lmemo)
                | none => (none, memo, lmemo)
              | (none, memo, lmemo) => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .letE nm ty val body =>
          if _h : emlt ty e ∧ emlt val e ∧ emlt body e then
            match ofStoreGo st memo lmemo ty with
            | (some xt, memo, lmemo) =>
              match ofStoreGo st memo lmemo val with
              | (some xv, memo, lmemo) =>
                match ofStoreGo st memo lmemo body with
                | (some xb, memo, lmemo) =>
                  match st.readbackN nm with
                  | some n' =>
                    (some (ExprC.mkLetE n' xt xv xb), memo, lmemo)
                  | none => (none, memo, lmemo)
                | (none, memo, lmemo) => (none, memo, lmemo)
              | (none, memo, lmemo) => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
        | .lit l => (some (ExprC.mkLit l), memo, lmemo)
        | .proj s i sub =>
          if _h : emlt sub e then
            match ofStoreGo st memo lmemo sub with
            | (some xs, memo, lmemo) =>
              match st.readbackN s with
              | some sn => (some (ExprC.mkProj sn i xs), memo, lmemo)
              | none => (none, memo, lmemo)
            | (none, memo, lmemo) => (none, memo, lmemo)
          else (none, memo, lmemo)
      match r with
      | some x => (some x, memo.insert e x, lmemo)
      | none => (none, memo, lmemo)
termination_by (etier e, epos e)
decreasing_by all_goals first | exact emlt_lex _h.1 | exact emlt_lex _h.2.1 | exact emlt_lex _h.2.2 | exact emlt_lex _h.2 | exact emlt_lex _h

/-- The conversion state threaded across the whole declaration list. -/
structure OfStoreS where
  memo : Std.HashMap EIdx ExprC := {}
  lmemo : Std.HashMap LIdx Level := {}

/-- Convert one index, threading the shared memos. -/
def ofStore (st : EStore) (s : OfStoreS) (e : EIdx) :
    Option ExprC × OfStoreS :=
  let (r, memo, lmemo) := ofStoreGo st s.memo s.lmemo e
  (r, ⟨memo, lmemo⟩)

/-- Convert a parsed constant value. -/
def cvCOfP (st : EStore) (s : OfStoreS) (cv : ConstantValP) :
    Option ConstantValC × OfStoreS :=
  match ofStore st s cv.type with
  | (some t, s) => (some ⟨cv.name, cv.levelParams, t⟩, s)
  | (none, s) => (none, s)

/-- Convert a parsed declaration. -/
def declCOfP (st : EStore) (s : OfStoreS) : DeclP → Option DeclC × OfStoreS
  | .axiomDecl v =>
    match cvCOfP st s v with
    | (some cv, s) => (some (.axiomDecl cv), s)
    | (none, s) => (none, s)
  | .defnDecl v value hint =>
    match cvCOfP st s v with
    | (some cv, s) =>
      match ofStore st s value with
      | (some x, s) => (some (.defnDecl cv x hint), s)
      | (none, s) => (none, s)
    | (none, s) => (none, s)
  | .thmDecl v value =>
    match cvCOfP st s v with
    | (some cv, s) =>
      match ofStore st s value with
      | (some x, s) => (some (.thmDecl cv x), s)
      | (none, s) => (none, s)
    | (none, s) => (none, s)
  | .opaqueDecl v value =>
    match cvCOfP st s v with
    | (some cv, s) =>
      match ofStore st s value with
      | (some x, s) => (some (.opaqueDecl cv x), s)
      | (none, s) => (none, s)
    | (none, s) => (none, s)
  | .basisDecl kind => (some (.basisDecl kind), s)
  | .indDecl block => (some (.indDecl block), s)

/-- Convert the whole declaration list under one shared memo. -/
def declsCOfP (st : EStore) : OfStoreS → List DeclP →
    CheckM (List DeclC)
  | _, [] => pure []
  | s, pd :: rest =>
    match declCOfP st s pd with
    | (some d, s) => do
      let ds ← declsCOfP st s rest
      pure (d :: ds)
    | (none, _) => throw (.internal "parse-arena conversion failed")

/-! ## The parsed-declaration checker -/

variable (mode : CheckMode)

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : ExprC) : CheckCM Level :=
  ensureSortI (coreKnotI mode fe checkFuel) d i

/-- `checkConstantVal` on a converted declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `ExprC`
DAG and the operations on `ExprC` values. -/
def checkConstantValC (fe : FEnv) (cv : ConstantValC) :
    CheckCM (ConstantVal × ExprC) := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless ExprC.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let jty ← (coreKnotI mode fe checkFuel).annotate 0 cv.type
  unless ExprC.allLevelParamsDefined cv.levelParams jty do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe jty do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let _u ← opSIxC mode fe 0 jsty
  let tyE := ExprC.toExpr jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `checkDefnValP` over `ExprC`. -/
def checkDefnValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) (hint : ReducibilityHint) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := ExprC.toExpr jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValP` over `ExprC`. -/
def checkThmValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv := do
  let jsty ← (coreKnotI mode fe checkFuel).infer 0 jty
  let ul ← opSIxC mode fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let vE := ExprC.toExpr jv
  recordCConst cvA.name cvA.type jty (some (vE, jv))
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValP` over `ExprC`. -/
def checkOpaqueValC (fe : FEnv) (cvA : ConstantVal) (jty : ExprC)
    (value : ExprC) : CheckCM FEnv := do
  unless ExprC.looseBVarsBounded 0 value do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI mode fe checkFuel).annotate 0 value
  unless ExprC.allLevelParamsDefined cvA.levelParams jv do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless constsResolveFC fe jv do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  recordCConst cvA.name cvA.type jty none
  let jvt ← (coreKnotI mode fe checkFuel).infer 0 jv
  unless ← (coreKnotI mode fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  pure (fe.push (.axiomInfo cvA))

/-- One converted declaration (mirrors `checkDeclSPPlain` branch by
branch; inductive and basis blocks reuse the `Expr`-level drivers). -/
def checkDeclSPC (fe : FEnv) (pd : DeclC) : CheckCM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let fe2 ← checkDefnValC mode fe cvA jty value hint
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOpsC mode fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOpsC mode fe) fe fe2 cvA.name
      pure fe2
    else
      checkDefnValC mode fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    checkThmValC mode fe cvA jty value
  | .opaqueDecl cv value => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    let fe2 ← checkOpaqueValC mode fe cvA jty value
    if reduceOpNames.contains cvA.name then do
      let vE := ExprC.toExpr value
      checkReducePinF (sharedOpsC mode fe) fe fe2 cvA.name vE
    pure fe2
  | .axiomDecl cv => do
    let (cvA, jty) ← checkConstantValC mode fe cv
    if stdAxiomOkF fe cvA then do
      recordCConst cvA.name cvA.type jty none
      pure (fe.push (.axiomInfo cvA))
    else if cvA.name = trustCompilerName then
      if trustCompilerOkF fe cvA then do
        recordCConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported Lean.trustCompiler shape ({cv.name})")
    else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
      if ofReduceAxOkF fe cvA then do
        recordCConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported compiler-trust axiom environment ({cv.name})")
    else if cvA.name = propextName ∨ cvA.name = choiceName then
      throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
    else if toleratedAxiomNames.contains cvA.name then
      pure fe
    else
      throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => do
    if kind = .quotK then
      unless fe.find? eqName = some eqA do
        throw (.notImplemented "quotient basis requires the pinned Eq basis")
    kind.declsA.foldlM installBasisDeclF fe
  | .indDecl block =>
    match directPartsF? fe block with
    | some p => checkDirectStructS mode fe p
    | none => checkIndDeclSF mode fe block

/-- One step of the converted-declaration fold: flush, then check. -/
def checkDeclSPStepC (fe : FEnv) (pd : DeclC) : CheckCM FEnv := do
  flushC
  checkDeclSPC mode fe pd

/-- The per-slot field invariant of a directly parsed declaration
(task #171): every `ExprC` the record carries is `WFc`.  The basis and
inductive kinds carry no `ExprC` slots. -/
def DeclCWFc : DeclC → Prop
  | .axiomDecl cv => ExprC.WFc cv.type
  | .defnDecl cv v _ => ExprC.WFc cv.type ∧ ExprC.WFc v
  | .thmDecl cv v => ExprC.WFc cv.type ∧ ExprC.WFc v
  | .opaqueDecl cv v => ExprC.WFc cv.type ∧ ExprC.WFc v
  | .basisDecl _ => True
  | .indDecl _ => True

/-- A parsed declaration carrying its invariant (the `WFStore`
pattern: the type is the receipt; the wrapper erases at runtime). -/
abbrev WDeclC := { pc : DeclC // DeclCWFc pc }

/-- Task #171: the direct-parse driver.  `DeclC` records come straight
from the frontend (`Setlec/Frontend/ExportC.lean`) — no arena, no
conversion pass; the capstone's entry premise is the parser's
`WFc`-by-construction theorem (`Setlec/Verify/Cached/ParseC.lean`). -/
def checkDeclsSPCachedD (mode : CheckMode) (ds : List WDeclC) : CheckM Env := do
  let fe ← (ds.foldlM (fun fe pc => checkDeclSPStepC mode fe pc.1)
    (mkFEnv Env.empty)).run' {}
  pure fe.env

/-- The converted-declaration checker: the parse arena is converted
once (sharing preserved), then the whole fold runs in one `CState`
with the environment-dependent caches flushed per declaration. -/
def checkDeclsSPCached (mode : CheckMode) (st : WFStore)
    (pds : List DeclP) : CheckM Env := do
  let ds ← declsCOfP st.raw {} pds
  let fe ← (ds.foldlM (checkDeclSPStepC mode) (mkFEnv Env.empty)).run' {}
  pure fe.env

end Setlec.Cached
