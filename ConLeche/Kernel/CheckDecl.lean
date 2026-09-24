module

public import ConLeche.Kernel.Inductives.BlockTail

@[expose] public section

/-!
# The checker's fold step

`checkDecl` checks one declaration against the current environment and,
on success, returns the extended environment.  `checkDeclsPure` folds it
over a list of declarations, starting from the empty environment.  The
stages it dispatches to live in `ConLeche/Kernel/Checker.lean` (values,
basis, `Nat` operations), `ConLeche/Kernel/Inductives/BlockTail.lean`
(the uniform inductive route) and `ConLeche/Kernel/Inductives/Modeled.lean`
(the modeled route).  Its own module because the uniform route's
recursor check is written over the index (`FEnv`).
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]
variable (mode : CheckMode)

/-- Check a single declaration, extending the environment on success. -/
def checkDecl (ops : CheckerOps m) (pins : List NatOpPinSet) (env : Env)
    (d : Declaration) : m Env := do
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkDefnVal ops env cv value hint
    -- Structural-Nat pins: the fast-path ops must be the standard
    -- structural recursions — their recurrence equations are checked
    -- by definitional equality here, once, so the literal fast path's
    -- reduction-time certification never fails on an accepted
    -- environment.  A nonstandard definition under one of these names
    -- is positively unsupported.  The equations are certified in the
    -- *pre-insertion* environment with the operation's self-references
    -- replaced by its stored value (see `ConLeche/Kernel/Core.lean`:
    -- certifying after insertion would let the operation's own fast
    -- path discharge its all-literal equations vacuously), and the
    -- operation's and its dependencies' stored types are pinned.
    if natOpNames.contains cv.name then
      unless natOpGuard env2 cv.name &&
          (natOpDeps cv.name).all (natOpStoredOk env2) do
        throw (.notImplemented
          s!"nonstandard structural Nat operation environment ({cv.name})")
      match env2.find? cv.name with
      | some (.defnInfo _ value' _) =>
        let ok ← certifyNatEqs ops env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2))
        unless ok do
          throw (.notImplemented
            s!"nonstandard structural Nat operation ({cv.name})")
      | _ => throw (.internal s!"structural Nat operation not stored ({cv.name})")
    -- WF-recursive Nat pins (`Nat.div`/`Nat.mod`): the stored value must
    -- be definitionally equal to some committed pin variant of a
    -- toolchain's own (helper-unfolded) definition, and that variant's
    -- pinned `Nat.ble`-guarded characterization certificates must
    -- check (in the pre-insertion environment, self-references
    -- substituted; see `checkDivModCerts`) — they are not installed;
    -- their success is what the model side consumes for the literal
    -- fast path.  No variant matching is a decline (exit 2) naming
    -- what each variant failed on — elaborator drift surfaces
    -- visibly, never silently (task #273).
    if natDivModNames.contains cv.name then
      checkDivModPin ops pins env env2 cv.name
    pure env2
  | .thmDecl cv value =>
    let cv ← checkConstantVal ops env cv
    checkThmVal ops env cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantVal ops env cv
    let env2 ← checkOpaqueVal ops env cv value
    -- Compiler-trust opaques (`Lean.reduceNat`/`Lean.reduceBool`,
    -- task #95): the stored value must be definitionally equal to the
    -- build-time pin of the toolchain's own defining expression — the
    -- gate that lets the `ofReduce*` axioms' identity certificates
    -- never fail on an accepted environment.
    if reduceOpNames.contains cv.name then
      checkReducePin ops env env2 cv.name value
    pure env2
  | .axiomDecl cv =>
    -- Pinned axioms are *installed*: the two standard axioms
    -- (`propext` via the stored `Iff` recursor and extensionality of
    -- propositions, `Classical.choice` via the stored `Nonempty`
    -- recursor and global choice) and the `Init` compiler-trust
    -- family (task #95: `Lean.trustCompiler` as an opaque with value
    -- `True.intro`; `Lean.ofReduceNat`/`Lean.ofReduceBool` over the
    -- pinned identity opaques, trivially true).  All types and the
    -- shapes of the inductives they quantify over are pinned (up to
    -- the exporter's unstable hygienic binder names).  `sorryAx` — the
    -- one axiom the checker tolerates as a DECLARATION (user ruling) —
    -- is well-formedness-checked but installs NOTHING: an export
    -- declares it whenever its module mentions `sorry`, whether or not
    -- anything uses it, so the record is skipped and the run continues,
    -- and because there is no set model for it any USE of the name
    -- declines at the record that uses it (`unknownConstError`,
    -- `ConLeche/Kernel/Core.lean`, and `unresolvedConstsError`,
    -- `ConLeche/Kernel/CheckerBase.lean`).  Any other axiom
    -- is a positive decline at its own record; a *pinned name* with a
    -- non-pinned shape likewise (the pin would otherwise shadow).
    -- **`Quot.sound` is the pinned quotient BLOCK's own record**
    -- (task #293): the export writes it as an ordinary axiom record
    -- beside the four `#QUOT` ones, so it arrives here — compared with
    -- the pin and installing NOTHING of its own (the pinned block
    -- installs the axiom together with its three other constants, at
    -- the first quotient record that matches), and DECLINING when it
    -- does not match.  The comparison precedes the common checks
    -- because the name is a reserved basis name: this record IS the
    -- pinned block's, not a redeclaration of it.  What stood here was
    -- a parser check (`ConLeche/Frontend/ExportC.lean`), which
    -- swallowed the record before the fold ever saw it.
    if cv.name = quotSoundName then
      (if ConstantInfo.canonEq (.axiomInfo cv) (quotBasis.getD 4 (.axiomInfo default)) then
        pure env
      else
        throw (.notImplemented "quotient soundness axiom mismatch"))
    else do
      let cvA ← checkConstantVal ops env cv
      if stdAxiomOk env cvA then
        pure ⟨.axiomInfo cvA :: env.consts⟩
      else if cvA.name = trustCompilerName then
        -- `Lean.trustCompiler : True` is trivially realizable (task
        -- #95): installed exactly like a checked `opaque` with witness
        -- value `True.intro` over the pinned `True` family — the pin
        -- guarantees everything the ordinary opaque check would have
        -- checked for that value, and the model interprets the constant
        -- by `True.intro`'s interpretation.
        if trustCompilerOk env cvA then
          pure ⟨.axiomInfo cvA :: env.consts⟩
        else throw (.notImplemented
          s!"unsupported Lean.trustCompiler shape ({cv.name})")
      else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
        -- The pinned `ofReduce*` axioms (task #95): over the pinned
        -- `Eq` basis, the element inductive and the identity-certified
        -- reduce opaque, `∀ a b, reduce a = b → a = b` interprets to an
        -- inhabited proposition (the hypothesis *is* the conclusion).
        if ofReduceAxOk env cvA then
          pure ⟨.axiomInfo cvA :: env.consts⟩
        else throw (.notImplemented
          s!"unsupported compiler-trust axiom environment ({cv.name})")
      else if cvA.name = propextName ∨ cvA.name = choiceName then
        throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
      else if cvA.name = sorryAxName then
        pure env
      else
        throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => checkBasisDecl env kind
  | .indDecl block nP =>
    -- **THE PINNED BASIS BLOCKS** (task #293).  A stream's `Nat` block
    -- arrives as an ordinary `indDecl` — the decoder emits the file's
    -- records and nothing else — and it is recognised HERE: a block
    -- whose members are named as one of the five pins' and which
    -- matches it up to `ConstantInfo.canon` installs the PIN (the
    -- annotated, model-proved literals `installBasisDecl` puts in the
    -- environment verbatim).  A block under a pinned name that does not
    -- match falls through to the ordinary route, where
    -- `checkConstantVal`'s reserved-name check REJECTS it: a basis
    -- redefinition is invalid input (task #181's ruling).
    match basisPinHit block with
    | some kind => checkBasisDecl env kind
    | none =>
    -- TASK #228 — THE DECLARED PARAMETER COUNT, first and for both
    -- routes.  Official reads `nparams` off the declaration and checks
    -- the block against it (`check_inductive_types`' telescope loop,
    -- and the replay's structural comparison of every constructor
    -- record with the generated one); `indParamsOk` is that check,
    -- one-sided, so a `false` is official's own reject.  It runs
    -- BEFORE the dispatch because it is a property of the DECLARATION
    -- and not of a route: the modeled path reaches it too, which is
    -- where a block with no constructor and no recursor record — the
    -- shape neither route recognises — is rejected rather than
    -- declined (arena 047).
    if indParamsOk nP block then
      -- ONE ROUTE (task #210): the fixpoint route takes every block it
      -- RECOGNISES — one type former, one recursor, ordinary,
      -- finitary-recursive or reflexive fields (the structure and sum
      -- routes it replaced were deleted at Part C).  Everything else is
      -- the modeled path's, and its model is the in-process modeller's
      -- (`ConLeche/Frontend/InModel.lean`), whose records precede the
      -- block in the very same parse; `checkModeled` DECLINES, naming the
      -- block, when there is none.  The dispatch is the RECOGNISER alone
      -- (task #219): a mutual or nested block carries several type
      -- formers, resp. several recursors, so `sumSplit` refuses it
      -- outright and no model lookup is needed to route it — which is why
      -- a stream record that happens to be named `T._model` has no effect
      -- on any block.  The module split (`CheckerBase ← Modeled ←
      -- Checker`) is why the dispatch lives here and not inside
      -- `checkModeled`.
      match blockParts? nP block with
      | some p => checkBlock ops env block p uniformNested
      | none => checkModeled mode ops env nP block
    else throw (.invalid "number of parameters mismatch")
  | .quotDecl k cv =>
    -- **THE QUOTIENT PACKAGE** (task #293).  The export writes it as
    -- four records; each one is compared with the pinned block's
    -- constant at its own kind, and the FIRST that matches installs the
    -- pinned block whole (the other three then find it installed and
    -- add nothing — they are the same declaration).  A record that does
    -- not match is a quotient this checker positively does not support:
    -- the decline the parser used to issue, now at the record, in the
    -- fold.
    if quotPinHit k cv then
      (match k with
       | .type => checkBasisDecl env .quotK
       | _ => pure env)
    else throw (.notImplemented (match k with
      | .sound => "quotient soundness axiom mismatch"
      | _ => "quotient declaration mismatch"))

/-- Check a list of declarations in order, starting from the empty
environment. -/
def checkDeclsPure (ops : CheckerOps m) (pins : List NatOpPinSet)
    (ds : List Declaration) : m Env :=
  ds.foldlM (checkDecl mode ops pins) Env.empty

end ConLeche
