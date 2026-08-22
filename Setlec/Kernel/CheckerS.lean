import Setlec.Kernel.Checker

/-!
# The shared-state declaration checker (task #51)

One interned state (`IState`, `Setlec/Kernel/CoreI.lean`) per
*declaration*: all checker operations within one `checkDecl` — the
annotate/infer/defeq/whnf calls of every phase — run in a single
`CheckIM` state, so the arena and the memo caches are shared across
entry calls instead of being rebuilt per call (`cachedOps`).

The environment is not constant within an inductive block
(`checkIndDecl`'s provisional environments), and cache entries are only
valid for the environment they were created under.  The discipline is
**driver-directed**: the thin drivers below mirror `checkDecl`'s
phase structure and call `flushS` at every environment transition —
the memo and lazy-constant caches are dropped, the *arena* (which is
environment-independent: denotations mention no environment) and the
name index survive.  There is no runtime environment comparison; the
adequacy of the flush points is what the bridge proves
(`Setlec/Verify/SimS.lean`, `Setlec/Verify/BridgeS*.lean`,
`Setlec/Model/ConsistencyS.lean`).

The environment *index* (`FEnv`) is built once per declaration and
maintained across the provisional environments by `FEnv.push` — the
index of a cons-extended environment is one `HashMap.insert`
(`mkFEnv_push`), so the per-entry-call `mkFEnv` fold disappears.  The
recursor group keeps the `env₂` snapshot of the index and rebuilds the
final environments from it by pushes (the ruled recursors are installed
on `env₂`, not on the provisional `envSelf`).

Everything here is additive: `Setlec/Kernel/Checker.lean` (the generic
checker and its `cachedOps` instantiation) is untouched, and the
single-environment pieces are the *generic* checker functions
instantiated at `sharedOps` — only the phase structure is mirrored.
-/

namespace Setlec

/-- The index of the cons-extended environment (`mkFEnv_push`:
`FEnv.push (mkFEnv env) ci = mkFEnv ⟨ci :: env.consts⟩`). -/
def FEnv.push (fe : FEnv) (ci : ConstantInfo) : FEnv :=
  ⟨⟨ci :: fe.env.consts⟩, fe.idx.insert ci.name ci⟩

/-- Drop the memo and lazy stored-constant caches (an environment
transition); the arena is environment-independent and survives. -/
def flushS : CheckIM Unit :=
  modify fun s => { store := s.store }

/-- Shared-state unary entry point: intern into the ambient arena, run
the interned knot, read back.  Unlike `runEntryE` the state is the
ambient per-declaration state, not a fresh one. -/
def opE (fe : FEnv) (pick : CoreFnsI → Nat → EIdx → CheckIM EIdx)
    (d : Nat) (e : Expr) : CheckIM Expr := do
  let i ← internExprM e
  let j ← pick (coreKnotI fe checkFuel) d i
  match ← withStore (fun st => st.readbackI j) with
  | some v => pure v
  | none => throw (.internal "interned readback failed")

/-- Shared-state definitional-equality entry point. -/
def opB (fe : FEnv) (d : Nat) (a b : Expr) : CheckIM Bool := do
  let i ← internExprM a
  let j ← internExprM b
  (coreKnotI fe checkFuel).defeq d i j

/-- Shared-state sort-ensuring entry point. -/
def opS (fe : FEnv) (d : Nat) (e : Expr) : CheckIM Level := do
  let i ← internExprM e
  let u ← ensureSortI (coreKnotI fe checkFuel) d i
  readbackLevelM u

/-- The per-declaration shared operations at a fixed environment index.
The methods ignore the per-call environment argument: the drivers
instantiate the record only at `fe.env`, which is what the bridge
walks relate (there is no runtime check — the flush discipline is
proven adequate, not tested). -/
def sharedOps (fe : FEnv) : CheckerOps CheckIM where
  annotate _ d e := opE fe (·.annotate) d e
  inferType _ d e := opE fe (·.infer) d e
  isDefEq _ d a b := opB fe d a b
  ensureSort _ d e := opS fe d e
  whnf _ d e := opE fe (·.whnf) d e

/-! ## Thin phase drivers for the inductive-block install

Each mirrors its `Setlec/Kernel/Checker.lean` counterpart clause by
clause; the differences are exactly: `flushS` at environment
transitions, `FEnv.push` maintaining the index, and the install path's
direct linear `Env.find?` lookups routed through the index. -/

/-- One non-recursor member (mirrors `checkIndMember`). -/
def checkIndMemberS (blockNames : List Name) (caps : IndCaps)
    (fe : FEnv) (ci : ConstantInfo) : CheckIM FEnv := do
  flushS
  let cvA ← checkMemberVal (sharedOps fe) blockNames fe.env ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (fe.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe.push (.ctorInfo cvA nP nF))
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Phase 0 of the recursor group (mirrors `provisionRecs`). -/
def provisionRecsS (blockNames : List Name) :
    FEnv → List ConstantInfo →
    CheckIM (FEnv × List (ConstantVal × Nat × Nat × List RecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      flushS
      let cvA ← checkMemberVal (sharedOps feAcc) blockNames feAcc.env
        ci.toConstantVal
      let (feSelf, others) ← provisionRecsS blockNames
        (feAcc.push (.recInfo cvA mI rP [])) rest
      pure (feSelf, (cvA, mI, rP, rules) :: others)
    | _ => throw (.notImplemented "recursor before other block members")

/-- The recursor group (mirrors `checkIndRecs`).  All iota-rule checks
run at `envSelf` — one flush entering the phase, none inside the fold
(the fold's accumulator environments are never passed to the
operations).  The ruled recursors are installed on the `env₂` snapshot
of the index. -/
def checkIndRecsS (blockNames : List Name) (fe₂ : FEnv)
    (recs : List ConstantInfo) : CheckIM FEnv := do
  if recs.isEmpty then
    pure fe₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    unless fe₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (feSelf, checked) ← provisionRecsS blockNames fe₂ recs
    flushS
    checked.foldlM (fun (acc : FEnv) c => do
        let rules' ← checkIotaRules (sharedOps feSelf) fe₂.env feSelf.env
          f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
      fe₂

/-- The public projection function for field `i` (mirrors
`checkProjFn`; the single-environment stages are the generic ones). -/
def checkProjFnS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckIM FEnv := do
  let (cvj, mcv) ← checkProjLookups (m := CheckIM) fe.env T ctorName lps
    nP nF i
  let pty ← checkProjTy (m := CheckIM) fe.env T ctorName lps mcv.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRule (sharedOps fe) fe.env cvj lps nP nF i
  checkProjIota (m := CheckIM) fe.env T ctorName lps cvj nP nF i
  pure (fe.push (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [⟨ctorName, nF, nP,
      if Expr.recRulePlain pty nP nP nP then .plain else .inert, rhsA⟩]))

/-- One projection-function install step (mirrors `installProjFnStep`;
the artifact lookup goes through the index). -/
def installProjFnStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckIM FEnv := do
  if (fe.find? (projModelName T i)).isSome then do
    flushS
    checkProjFnS fe T ctorName lps nP nF i
  else pure fe

/-- The Prop-fallback elimination-template entry (mirrors
`installProjTemplate`; operation-free, lookups through the index). -/
def installProjTemplateS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckIM FEnv := do
  match fe.find? (T.str "rec") with
  | some (.recInfo cvR mI rP [rule]) =>
    if (fe.find? (projFnName T i)).isNone ∧
        mI = rP ∧ rP = nP + 2 ∧ rule.ctor = ctorName ∧ i < nF then
      pure (fe.push (.projInfo ⟨T, i, lps, nP, ctorName, nF, .sort .zero,
        .zero, .zero, false,
        cvR.levelParams.length = lps.length + 1⟩))
    else pure fe
  | _ => pure fe

/-- One elimination-template install step (mirrors
`installProjTemplateStep`). -/
def installProjTemplateStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckIM FEnv :=
  if (fe.find? (projFnName T i)).isNone then
    installProjTemplateS fe T ctorName lps nP nF i
  else pure fe

/-- The modeled inductive block (mirrors `checkIndDecl`). -/
def checkIndDeclS (fe : FEnv) (block : List ConstantInfo) :
    CheckIM Env := do
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  unless block = nonrecs ++ recs do
    throw (.notImplemented "recursor before other block members")
  let blockNames := block.map (·.name)
  match block.filter (fun ci => match ci with
      | .indInfo _ _ => true | _ => false),
    block.filter (fun ci => match ci with
      | .ctorInfo _ _ _ => true | _ => false) with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    let caps ← pure (indBlockCaps fe.env cvT cvC nP nF)
    let fe₂ ← nonrecs.foldlM (checkIndMemberS blockNames caps) fe
    let fe₃ ← checkIndRecsS blockNames fe₂ recs
    unless (List.range nF).all
        (fun j => (fe₃.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    let fe₄ ← (List.range nF).foldlM
      (installProjFnStepS cvT.name cvC.name cvT.levelParams nP nF) fe₃
    let fe₅ ← (List.range nF).foldlM
      (installProjTemplateStepS cvT.name cvC.name cvT.levelParams nP nF) fe₄
    pure fe₅.env
  | _, _ => do
    let fe₂ ← nonrecs.foldlM (checkIndMemberS blockNames {}) fe
    let fe₃ ← checkIndRecsS blockNames fe₂ recs
    pure fe₃.env

/-- One declaration in the shared state.  Non-inductive declarations
run entirely at the input environment: they are the *generic*
`checkDecl` at the shared operations (state shared across every
operation call, no flushes needed). -/
def checkDeclS (fe : FEnv) (d : Declaration) : CheckIM Env :=
  match d with
  | .indDecl block => checkIndDeclS fe block
  | _ => checkDecl (sharedOps fe) fe.env d

/-- The shared-state checker step the binary runs: index built once,
state lives for exactly this declaration. -/
def checkDeclShared (env : Env) (d : Declaration) : CheckM Env :=
  (checkDeclS (mkFEnv env) d).run' {}

/-- The declaration fold of the shared-state checker. -/
def checkDeclsShared (ds : List Declaration) : CheckM Env :=
  ds.foldlM checkDeclShared Env.empty

end Setlec
