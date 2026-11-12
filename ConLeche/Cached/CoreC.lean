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
over `mode : CheckMode`, and the knot (the mutual block of the bodies
and the entry points `whnfCoreI`, `whnfI`, `inferI`, `defeqI`, `defeqEI`)
runs them at a mode.  The verified core is this knot at `.verified`;
the trusted core is this same knot at `.trusted` — there is no second
implementation: what
the trusted mode omits is exactly what `mode.verifiedChecks` gates
here: group A (the η body-type comparison, the λ/λ body-type
comparison, the projection certificate) and the
certificate families (every `certAtI` site), and
nothing else (DESIGN.md, "CORET
RETIRED").  Every read is a `match` on the two-constructor enum
(`ConLeche/Kernel/Env.lean`), so at either literal mode it reduces by
`rfl`, with no branch left.
-/

namespace ConLeche.Cached

open ConLeche

variable {m : Type → Type}

/-! ## The helper twins outside the knot -/

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
    if natLitStoredF fe then pure (natLitToConstructor n)
    else pure e
  | _ => pure e

/-! ### The certificate-family switch (the twin's retirement, 2026-09-06)

The certificate families — the task-#76 skip list: work the
reference kernel does not run and only the soundness proof consumes —
are gated by `CheckMode.verifiedChecks` (`ConLeche/Kernel/Env.lean`).
Every such certificate below is spelled through the wrapper here, so
the list of `certAtI` sites **is** the
list of what the trusted core omits beyond group A.  At `.verified`
the mode function is `true`, so `certAtI .verified c` is `c` by `rfl`
(`certAtI_verified`); the simulation tower
(`ConLeche/Verify/Cached/*`), stated at `.verified`, sees through the
wrapper by `certAtI_verified` — the
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

/-- The `.proj T i b` spine (the tower spelling, task #175
W4c). -/
def projNodesI (T : Name) (b : Expr) : List Nat → CheckCM (List Expr)
  | [] => pure []
  | i :: rest => do
    let r ← pure (Expr.proj T i b)
    let rs ← projNodesI T b rest
    pure (r :: rs)

/-- Twin of `unitLikeShape` (pure: the index's reads and the cached
operation-free instantiations). -/
def unitLikeShapeF (fe : FEnv) (w : Expr) : Option (Expr × Nat) :=
  match Expr.getAppFn w with
  | .const S us =>
    match fe.find? S with
    | some (.indInfo cvS caps) =>
      if caps.eta = true ∧ us.length = cvS.levelParams.length then
        match fe.findTable? S with
        | some tbl =>
          if (Expr.getAppArgsC w).length = tbl.numParams then
            match fe.find? tbl.ctor with
            | some (.ctorInfo cvC _ _) =>
              (Expr.peelPis tbl.numParams (Expr.instLevelParams cvC.levelParams us cvC.type)).map
                fun body =>
                  (Expr.instantiateListC body (Expr.getAppArgsC w).reverse 0, tbl.numFields)
            | _ => none
          else none
        | none => none
      else none
    | _ => none
  | _ => none

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
    | some (.recInfo cv mI _ _ _) =>
      iotaNumArgs e 0 == mI + 1 && us.length == cv.levelParams.length
    | _ => false
  | _ => false

/-- A spine head that is its own head normal form and not a lambda: the
heads `whnfCoreEasy` answers with themselves, but a lambda. -/
def isStuckHeadC : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .const .. | .lit _ => true
  | _ => false

/-- The ι target of a spine head: the spine length `mI + 1` at which
`iotaRecI` can fire, where the head is a stored recursor at its own
number of levels (the arity test of `iotaArityOk`, read off the head
once). -/
def iotaTargetF (fe : FEnv) (h : Expr) : Option Nat :=
  match h with
  | .const c us =>
    match fe.find? c with
    | some (.recInfo cv mI _ _ _) =>
      if us.length = cv.levelParams.length then some (mI + 1) else none
    | _ => none
  | _ => none

/-- Twin of `projCert`, through the index. -/
def projCertF (fe : FEnv) (c : Name) (args : List Expr) : Bool :=
  match fe.find? c with
  | some (.ctorInfo cvC _ _) => teleArityOk cvC.type args
  | _ => false

/-- Twin of `projCertAt`. -/
def projCertAtF (fe : FEnv) (verified : Bool) (c : Name) (args : List Expr) :
    Bool :=
  if verified then projCertF fe c args else true

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

/-- **`whnfCore`'s easy cases** (official `whnf_core`, "handle easy
cases"): the kinds that are their own head normal form
(`whnfCoreStepI`'s `.done e` arm).  The loop returns them before the
memo, at every step: no lookup, no insert.  A free variable is never a
let-variable here (lets are ζ-reduced by instantiation), so it is easy,
as official's non-let `FVar`. -/
@[inline] def whnfCoreEasy : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .lam .. | .const .. | .lit _ => true
  | _ => false

/-- **A `whnfCore` memo key**: a term of an arm official `whnf_core`
stores (`src/kernel/type_checker.cpp`, `whnf_core`: the `Proj`, `Let`
and `App` cases, the insert after the `switch`) — a projection, a
let-expression, or an application whose head is not its own head normal
form.  An application with a stuck head (`isStuckHeadC`) is official's
`f == f0` arm, the ι step or the stuck answer, which `return`s before
the insert: it is never stored, so the loop does not look it up.  `h`
is the term's spine head (`Expr.getAppFn`), computed once per step. -/
@[inline] def whnfCoreKeyC (h : Expr) : Expr → Bool
  | .app _ _ => !isStuckHeadC h
  | .proj .. | .letE .. => true
  | _ => false

/-- A key whose step ended the chain with `v` is stored, but for an
application answered by itself: its head normalized to itself (a stuck
projection), official's `f == f0` arm again.  A stuck
projection is stored (official's `Proj` case stores `r = e`).  `key` is
`whnfCoreKeyC` of `e`. -/
@[inline] def whnfCoreStoresDone (key : Bool) (e v : Expr) : Bool :=
  match e with
  | .app .. => key && !(v == e)
  | _ => key

/-- **A step the two modes take alike**: a let-expression, or an
application whose head is a lambda or stuck; neither normalizes a
projection or a head that could contain one.  A chain of such steps
answers the same in the cheap mode as in the full one
(`whnfCoreStepW_cheap`), so the full mode's loop also stores its keys
in the cheap mode's memo.  `h` is the term's spine head. -/
@[inline] def whnfCoreCheapSafeC (h : Expr) : Expr → Bool
  | .app _ _ =>
    match h with
    | .lam .. => true
    | h => isStuckHeadC h
  | .letE .. => true
  | _ => false

/-- The cached state after a finished chain: its keys `pend` map to the
answer `v` in the full mode's memo, and those of them whose chain the
cheap mode takes alike (`pendC`) in the cheap mode's memo.  Each map is
taken out of the state before the inserts (`memoEI`'s linearity). -/
@[inline] def storeChain (st : CState) (pend pendC : List Expr) (v : Expr) : CState :=
  let mp := st.whnfCoreC
  let st := { st with whnfCoreC := ∅ }
  let st := { st with whnfCoreC := pend.foldl (fun m k => m.insert k v) mp }
  let mc := st.whnfCoreCheapC
  let st := { st with whnfCoreCheapC := ∅ }
  { st with whnfCoreCheapC := pendC.foldl (fun m k => m.insert k v) mc }

/-- The pending keys past a step on `e`: `e` joins them where it is
stored (`b`). -/
@[inline] def pushKey (b : Bool) (e : Expr) (pend : List Expr) : List Expr :=
  if b then e :: pend else pend

/-- The cheap mode's pending keys past a step on `e`: kept, and joined by
`e` where it is stored (`b`), past a step the two modes take alike
(`safe`, `whnfCoreCheapSafeC`); dropped past any other. -/
@[inline] def pushCheapKey (safe b : Bool) (e : Expr) (pendC : List Expr) : List Expr :=
  if safe then pushKey b e pendC else []

/-- Store a finished chain (`storeChain`): the cheap mode stores nothing
(official stores only when not cheap), and a chain without keys has
nothing to store. -/
@[inline] def storeChainI (cheap : Bool) (pend pendC : List Expr) (v : Expr) : CheckCM Unit :=
  if cheap || pend.isEmpty then pure () else modify fun st => storeChain st pend pendC v

/-- The `whnfCore` memo of a mode: the full mode reads `whnfCoreC`, the
cheap mode `whnfCoreCheapC` (see `whnfCoreLoopI`). -/
@[inline] def whnfCoreLookupI (cheap : Bool) (e : Expr) : CheckCM (Option Expr) := do
  let st ← get
  if cheap then pure st.whnfCoreCheapC[e]? else pure st.whnfCoreC[e]?

/-- **`whnf`'s easy cases** (official `whnf`, "Do not cache easy
cases"): sorts, free variables, Π-types and literals, which neither
head-normalize, reduce as literals nor unfold.  A constant or a
lambda-expression still goes through the memo, as in official `whnf`. -/
@[inline] def whnfEasy : Expr → Bool
  | .sort _ | .fvar .. | .forallE .. | .lit _ => true
  | _ => false

/-- Memoize a unary entry point under its node (`O(1)` key).

`@[inline]`: after
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

/-! ## The knot

The cached core is one block of mutually recursive functions: the five
entry points (`whnfCoreI`, `whnfI`, `inferI`, `defeqI`, `defeqEI`, at
the end of the block), each memoized in `CState`, and the bodies and
helpers they run.  Every function of the block takes the knot's
address: the mode and the environment index (the section's variables),
the tower flag `eager` and the knot level `lv`.  An entry point at
`lv + 1` runs its body at `lv`; a helper calls the entry points at its
own level; at level `0` every entry point is out of fuel.  The checker
enters at `checkFuel`.  Nothing is built per call: no record, no
closure (task #558; until then the level below was a record of six
closures, built at every memo miss).

Termination is lexicographic: the knot level, then the helper's place
in the block (an entry point is `0`; a helper calls only helpers above
it and the entry points), then the helper's own loop measure.  The
compiled code is the plain recursion.

**The knot takes the mode** (task #185).  `.verified` is the verified
core the capstones are stated about, and `.trusted` is the trusted core
`--trusted` runs — the same functions at the other mode.  The
mode-parametric simulation tower (`ConLeche/Verify/Cached/*`) is
general in the mode where it holds at both, and stated at `.verified`
where it needs the certificate families. -/

/- Every read of the mode below is one of the `CheckMode` functions of
`ConLeche/Kernel/Env.lean`, each a `match` on the enum.  The ι cone
(`majorToCtorI` → `prepareMajorI` → `iotaRecI`) reads the mode through
`certAtI`. -/
section Knot

variable (mode : CheckMode) (fe : FEnv)

-- Both limits count per command, and the block is one command of 68
-- definitions (each alone is far below the defaults): the heartbeats for
-- their elaboration, the recursion depth for the termination proofs over
-- the 68-way packed argument of the well-founded fixpoint.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 8000 in
mutual

/-- Twin of `reduceNat`. -/
def reduceNatI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) := do
  match e with
  | .app f₁ b =>
    match f₁ with
    | .const c us =>
      match us with
      | _ :: _ => pure none
      | [] => do
        let cn ← pure c
        if cn = natSuccName ∧ natLitStoredF fe then do
          let w ← whnfI eager lv depth b
          match ← pure (rawNatLitC? w) with
          | some n => do
            let maxNatSize ← maxNatSizeM
            if natSizeBytes (n + 1) > maxNatSize then throw natNumeralTooBig
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
          -- the operation found once (`NatBinOp.ofName?`)
          match NatBinOp.ofName? c with
          | some op => do
            -- first argument first; the second only behind a literal
            -- (official `reduce_bin_nat_op`; the spec's D15 note)
            let w₁ ← whnfI eager lv depth a
            match ← pure (rawNatLitC? w₁) with
            | some n₁ => do
              let w₂ ← whnfI eager lv depth b
              match ← pure (rawNatLitC? w₂) with
              | some n₂ => do
                -- the maximum `Nat` size (official `reduce_pow`,
                -- `reduce_shiftLeft`, `reduce_bin_nat_op`): refused
                -- before computing, or by the computed result's size
                let maxNatSize ← maxNatSizeM
                match natOpRefusal maxNatSize op n₁ n₂ with
                | some err => throw err
                | none =>
                  let x ← pure (op.result n₁ n₂)
                  if natResultRefused maxNatSize op x then throw natNumeralTooBig
                  pure (some x)
              | none => pure none
            | none => pure none
          | none => pure none
      | _ => pure none
    | _ => pure none
  | _ => pure none
termination_by (lv, 1, 0, 0)

/-- Twin of `iotaCertsFull` (task #342 L10, ι's case 3), in bulk form:
the consumed arguments are kept in an accumulator and substituted into
each binder's *domain* (small) instead of instantiating the whole
residual telescope per argument; a raw `bvar` body substitutes the
accumulator and re-enters.  Every slot is certified, its argument
inferred at the FULL grade. -/
def iotaCertsFullIAux (eager : Bool) (lv : Nat) (depth : Nat) :
    Expr → List Expr → List Expr → CheckCM Bool
  | _, _, [] => pure true
  | ty, acc, arg :: rest => do
    match ty with
    | .forallE dom body => do
        let dom' ← instListM dom acc
        let ta ← inferI eager lv false depth arg
        if ← defeqI eager lv depth ta dom' then
          iotaCertsFullIAux eager lv depth body (arg :: acc) rest
        else pure false
    | .bvar _ =>
      match acc with
      | [] => pure false
      | _ :: _ => do
        let ty' ← instListM ty acc
        iotaCertsFullIAux eager lv depth ty' [] (arg :: rest)
    | _ => pure false
termination_by _ acc args => (lv, 2, 2 * args.length + acc.length, 0)

/-- Twin of `iotaCertsFull`, at the empty accumulator. -/
def iotaCertsFullI (eager : Bool) (lv : Nat) (depth : Nat)
    (ty : Expr) (args : List Expr) : CheckCM Bool :=
  iotaCertsFullIAux eager lv depth ty [] args
termination_by (lv, 3, 0, 0)

/-- Twin of `defEqList`. -/
def defEqListI (eager : Bool) (lv : Nat) (depth : Nat) :
    List Expr → List Expr → CheckCM Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← defeqI eager lv depth a b then
      defEqListI eager lv depth as bs
    else pure false
  | _, _ => pure false
termination_by as _ => (lv, 4, as.length, 0)

/-- Twin of `iotaIndexOk` (the canonical-index comparison, only where
the recursor has indices). -/
def iotaIndexOkI (eager : Bool) (lv : Nat) (depth : Nat) (mI rP cnP : Nat)
    (tyCtor : Expr) (margs idx : List Expr) : CheckCM Bool :=
  if mI = rP then pure true
  else do
    match ← piResidualM tyCtor margs with
    | some residual => do
      let resArgs ← pure (Expr.getAppArgsC residual)
      defEqListI eager lv depth (resArgs.drop cnP) idx
    | none => pure false
termination_by (lv, 5, 0, 0)

/-- Twin of `defeqSpine`. -/
def defeqSpineI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
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
        | some true => defEqListI eager lv depth aargs.reverse bargs.reverse
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false
termination_by (lv, 6, 0, 0)

/-- Twin of `proofIrrel`. -/
def proofIrrelI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  let ta ← inferI eager lv true depth a
  let tta ← inferI eager lv true depth ta
  let wtta ← whnfI eager lv depth tta
  match wtta with
  | .sort uT => do
    let z ← pure .zero
    let okA ← liftFueled "level comparison" (← isEquivLM uT z)
    let tb ← inferI eager lv true depth b
    let ttb ← inferI eager lv true depth tb
    let wttb ← whnfI eager lv depth ttb
    match wttb with
    | .sort vT => do
      let z ← pure .zero
      let okB ← liftFueled "level comparison" (← isEquivLM vT z)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false
termination_by (lv, 7, 0, 0)

/-- Twin of `propIrrel` (task #168): the hoisted `Prop`-branch test
with both head-symbol arms.  Ungated since 2026-09-06 — the readers
run in both modes, so this body takes no `CheckMode` at all. -/
def propIrrelI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  if notProofFast fe.find? fe.findTable? a || notProofFast fe.find? fe.findTable? b then
    pure false
  else if isProofFast fe.find? fe.findTable? a && isProofFast fe.find? fe.findTable? b then
    pure true
  else
  let ta ← inferI eager lv true depth a
  let tta ← inferI eager lv true depth ta
  let wtta ← whnfI eager lv depth tta
  match wtta with
  | .sort uT => do
    let z ← pure .zero
    let okA ← liftFueled "level comparison" (← isEquivLM uT z)
    let tb ← inferI eager lv true depth b
    let ttb ← inferI eager lv true depth tb
    let wttb ← whnfI eager lv depth ttb
    match wttb with
    | .sort vT => do
      let z ← pure .zero
      let okB ← liftFueled "level comparison" (← isEquivLM vT z)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false
termination_by (lv, 8, 0, 0)

/-- Twin of `structEtaCertWith`. -/
def structEtaCertWithI (eager : Bool) (lv : Nat) (depth : Nat)
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
            match fe.findTable? Tn with
            | some tbl => do
              let targs ← pure (Expr.getAppArgsC wtb)
              if caps.eta = true ∧ tbl.ctor = cn ∧
                  targs.length = tbl.numParams ∧
                  us'.length = cvT.levelParams.length ∧
                  cvc.levelParams = cvT.levelParams then do
                if ← liftFueled "level comparison"
                    (← isEquivListLM us us') then do
                  -- no type-application certificate (task #342 L11b)
                  if ← defEqListI eager lv depth
                      (aargs.take tbl.numParams) targs then do
                    let projs ← projNodesI T b (List.range tbl.numFields)
                    defEqListI eager lv depth (aargs.drop tbl.numParams) projs
                  else pure false
                else pure false
              else pure false
            | none => pure false
          | _ => pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false
termination_by (lv, 9, 0, 0)

/-- Twin of `structEtaFull`. -/
def structEtaFullI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  -- the constructor-shape gate first (D13), as in the spec
  let sh ← pure (etaCtorShapeC fe a)
  if sh then
    let tb ← inferI eager lv true depth b
    let wtb ← whnfI eager lv depth tb
    structEtaCertWithI eager lv depth a b wtb
  else pure false
termination_by (lv, 10, 0, 0)

/-- Twin of `structEtaExpand`. -/
def structEtaExpandI (eager : Bool) (lv : Nat) :
    Nat → Nat → Expr → Expr → Expr → CheckCM Bool
  | 0, depth, a, b, _ => structEtaFullI eager lv depth a b
  | k + 1, depth, a, b, .forallE dom body => do
    let fv ← pure (Expr.fvar depth dom)
    let body' ← inst1M body fv
    structEtaExpandI eager lv k (depth + 1) (.app a fv) (.app b fv) body'
  | _ + 1, _, _, _, _ => pure false
termination_by k _ _ _ _ => (lv, 11, k, 0)

/-- Twin of `structEtaCert`. -/
def structEtaCertI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  let sh ← pure (etaCtorShapeC fe a)
  if sh then structEtaFullI eager lv depth a b else
  match etaCtorPartialC fe a with
  | some k =>
    if !b.ioNeutral then pure false else
    let ta ← inferI eager lv true depth a
    let tb ← inferI eager lv true depth b
    if ← defeqI eager lv depth tb ta then structEtaExpandI eager lv k depth a b ta
    else pure false
  | none => pure false
termination_by (lv, 12, 0, 0)

/-- Twin of `isPropType`. -/
def isPropTypeI (eager : Bool) (lv : Nat) (depth : Nat) (T : Expr) : CheckCM Bool := do
  let tt ← inferI eager lv true depth T
  let w ← whnfI eager lv depth tt
  match w with
  | .sort u => do
    let z ← pure .zero
    liftFueled "level comparison" (← isEquivLM u z)
  | _ => pure false
termination_by (lv, 13, 0, 0)

/-- Twin of `unitLikeFields`, the field test `unitLikeLoopI` at the
loop's remaining fuel `ulf`. -/
def unitLikeFieldsI (eager : Bool) (lv : Nat) (ulf : Nat) :
    Nat → Nat → Expr → CheckCM Bool
  | 0, _, _ => pure true
  | n + 1, depth, .forallE dom body => do
    if ← isPropTypeI eager lv depth dom then do
      let body' ← inst1M body (.fvar depth dom)
      unitLikeFieldsI eager lv ulf n (depth + 1) body'
    else if ← unitLikeLoopI eager lv ulf depth dom then do
      let body' ← inst1M body (.fvar depth dom)
      unitLikeFieldsI eager lv ulf n (depth + 1) body'
    else pure false
  | _ + 1, _, _ => pure false
termination_by n _ _ => (lv, 16, 2 * ulf, n + 1)

/-- Twin of `unitLikeStruct`. -/
def unitLikeStructI (eager : Bool) (lv : Nat) (ulf : Nat)
    (depth : Nat) (w : Expr) : CheckCM Bool :=
  match unitLikeShapeF fe w with
  | some (tele, n) => unitLikeFieldsI eager lv ulf n depth tele
  | none => pure false
termination_by (lv, 16, 2 * ulf + 1, 0)

/-- Twin of `unitLikeLoop`. -/
def unitLikeLoopI (eager : Bool) (lv : Nat) : Nat → Nat → Expr → CheckCM Bool
  | 0, _, _ => pure false
  | fuel + 1, depth, T => do
    let w ← whnfI eager lv depth T
    match w with
    | .forallE dom body => do
      let body' ← inst1M body (.fvar depth dom)
      unitLikeLoopI eager lv fuel (depth + 1) body'
    | _ => unitLikeStructI eager lv fuel depth w
termination_by f _ _ => (lv, 16, 2 * f, 0)

/-- Twin of `structUnitCert`. -/
def structUnitCertI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  let ta ← inferI eager lv true depth a
  let wta ← whnfI eager lv depth ta
  if wta.isForallE && !a.ioNeutral then pure false else
  if ← unitLikeLoopI eager lv unitLikeFuel depth wta then
    let tb ← inferI eager lv true depth b
    let wtb ← whnfI eager lv depth tb
    if wtb.isForallE && !b.ioNeutral then pure false else
    defeqI eager lv depth wta wtb
  else pure false
termination_by (lv, 17, 0, 0)

/-- Twin of `etaCert` (the λ's pieces come pre-destructured, as in the
spec). -/
def etaCertI (eager : Bool) (lv : Nat) (depth : Nat)
    (ty₁ body₁ : Expr) (b : Expr) :
    CheckCM Bool := do
  if !b.ioNeutral then pure false else
  let tb ← inferI eager lv true depth b
  let wtb ← whnfI eager lv depth tb
  match wtb with
  | .forallE ty₂ cod₂ => do
    if ← defeqI eager lv depth ty₂ ty₁ then do
      let fv ← pure (Expr.fvar depth ty₁)
      let b₁ ← inst1M body₁ fv
      let ba ← pure (Expr.app b fv)
      unless ← defeqI eager lv (depth + 1) b₁ ba do return false
      -- the η check (task #342, T2; see `etaCert`): the λ body's
      -- full-grade type is the ∀'s codomain at the variable
      if mode.verifiedChecks then do
        let t₁ ← inferI eager lv false (depth + 1) b₁
        let t₂ ← inst1M cod₂ fv
        unless ← defeqI eager lv (depth + 1) t₁ t₂ do return false
      pure true
    else pure false
  | _ => pure false
termination_by (lv, 18, 0, 0)

/-- Twin of `stuckIrrel`. -/
def stuckIrrelI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM Bool := do
  if ← structEtaCertI eager lv depth a b then pure true
  else if ← structEtaCertI eager lv depth b a then pure true
  else if ← structUnitCertI eager lv depth a b then pure true
  else proofIrrelI eager lv depth a b
termination_by (lv, 19, 0, 0)

/-- Twin of `formerSortLoop`, through the shared instantiation. -/
def formerSortLoopI (eager : Bool) (lv : Nat) : Nat → Nat → Expr → CheckCM (Option Level)
  | d, 0, e => do
    let w ← whnfI eager lv d e
    match w with
    | .sort s => pure (some s)
    | _ => pure none
  | d, n + 1, e => do
    let w ← whnfI eager lv d e
    match w with
    | .forallE dom b => do
      let b' ← inst1M b (.fvar d dom)
      formerSortLoopI eager lv (d + 1) n b'
    | _ => pure none
termination_by _ n _ => (lv, 20, n, 0)

/-- Twin of `formerNeverZeroAt`. -/
def formerNeverZeroI (eager : Bool) (lv : Nat) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) : CheckCM Bool :=
  match formerResSort cvT.type with
  | some _ => pure (formerNeverZero cvT us)
  | none => do
    let ty ← instLevelParamsM cvT.levelParams us cvT.type
    let o ← formerSortLoopI eager lv 0 (caps.nparams + caps.nIdx) ty
    match o with
    | some s => pure (Level.zeronessOf s).isNever
    | none => pure false
termination_by (lv, 21, 0, 0)

/-- Twin of `iotaCase3At`. -/
def iotaCase3I (eager : Bool) (lv : Nat) (find? : Name → Option ConstantInfo) (isK : Bool)
    (cvj : ConstantVal) (us : List Level) : CheckCM Bool :=
  if isK then pure false else
  match ctorFamily find? cvj with
  | some (cvT, caps) =>
    if cvT.levelParams.length == us.length then do
      let nz ← formerNeverZeroI eager lv cvT caps us
      pure !nz
    else pure true
  | none => pure true
termination_by (lv, 22, 0, 0)

/-- Twin of `majorToCtor`. -/
def majorToCtorI (eager : Bool) (lv : Nat) (depth : Nat)
    (_recName : Name) (isK : Bool) (rules : List RecRule) (major : Expr) :
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
          if isK = true then do
            let tmaj₀ ← inferI eager lv true depth major
            let tmaj ← whnfI eager lv depth tmaj₀
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
                    let tfab ← inferI eager lv true depth fab
                    if ← defeqI eager lv depth tmaj tfab then
                      if ← certAtI mode (proofIrrelI eager lv depth fab major) then
                        pure fab
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else match etaRescueTable? (fe.findTable? T) rl.ctor cvj cvT caps with
          | some tbl => do
            let tmaj₀ ← inferI eager lv true depth major
            let tmaj ← whnfI eager lv depth tmaj₀
            match Expr.getAppFn tmaj with
            | .const T' ust => do
              let margs ← pure (Expr.getAppArgsC tmaj)
              let ustL ← pure ust
              -- instantiated non-Prop guard, as in the spec body
              -- `majorToCtor` (task #61); the counts are the table's
              if (← pure (T' == T)) ∧ margs.length = tbl.numParams ∧
                  ust.length = cvT.levelParams.length then do
                if ← formerNeverZeroI eager lv cvT caps ustL then do
                  let TI ← pure T
                  let projs ← projNodesI TI major (List.range tbl.numFields)
                  let ctorI ← pure tbl.ctor
                  let h ← pure (Expr.const ctorI ust)
                  let fab ← mkAppNM h (margs ++ projs)
                  -- no certificate on the fabricated spine (task #342 L11b)
                  if ← pure (Expr.wscopedBC depth fab &&
                      Expr.looseBVarsBounded 0 fab &&
                      Expr.leafGuard fab major) then
                    pure fab
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          | none =>
            if T = andName then do
              -- the `And`-only rescue, as in the spec body
              let tmaj₀ ← inferI eager lv true depth major
              let tmaj ← whnfI eager lv depth tmaj₀
              match Expr.getAppFn tmaj with
              | .const T' ust => do
                let margs ← pure (Expr.getAppArgsC tmaj)
                if (← pure (T' == T)) ∧ margs.length = cnP ∧
                    cvj.levelParams.length = ust.length ∧
                    fe.andRescueSlotsF rl.ctor cnP = true then do
                  let TI ← pure T
                  let projs ← projNodesI TI major [0, 1]
                  let ctorI ← pure rl.ctor
                  let h ← pure (Expr.const ctorI ust)
                  let fab ← mkAppNM h (margs ++ projs)
                  if ← pure (Expr.wscopedBC depth fab &&
                      Expr.looseBVarsBounded 0 fab &&
                      Expr.leafGuard fab major) then do
                    let tfab ← inferI eager lv true depth fab
                    if ← defeqI eager lv depth tmaj tfab then
                      if ← certAtI mode (proofIrrelI eager lv depth fab major) then
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
termination_by (lv, 23, 0, 0)

/-- Twin of `litMajorToCtor`. -/
def litMajorToCtorI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) :
    CheckCM Expr := do
  match e with
  | .lit (.strVal s) =>
    if strLitStoredF fe then do
      let x ← pure (strLitToConstructor s)
      whnfI eager lv depth x
    else pure e
  | _ => litToCtorIfNatI fe e
termination_by (lv, 24, 0, 0)

/-- Twin of `projLitToCtor`. -/
def projLitToCtorI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) :
    CheckCM Expr := do
  match e with
  | .lit (.strVal s) =>
    if strLitStoredF fe then do
      let x ← pure (strLitToConstructor s)
      whnfI eager lv depth x
    else pure e
  | _ => pure e
termination_by (lv, 25, 0, 0)

/-- Twin of `prepareMajor`: the major's preparation (K rescue on the
raw major; task #334 — no `whnf` either way after it: if it produced a
constructor, only the literal conversion follows; if it failed, the
major is left exactly as it is; elsewhere the structure rescues on the
raw major first (lean4#15351, task #342 R2), and only if they produce
no constructor whnf, literal, rescue).  The K flag is the single rule's
record's flag, as in the spec. -/
def prepareMajorI (eager : Bool) (lv : Nat) (depth : Nat)
    (recName : Name) (isK : Bool) (rules : List RecRule) (major : Expr) :
    CheckCM Expr := do
  if isK then do
    let majorK ← majorToCtorI eager lv depth recName isK rules major
    if isCtorAppC fe majorK then
      litMajorToCtorI eager lv depth majorK
    else pure majorK
  else do
    let majorE ← if major.isStrLit then pure major
      else majorToCtorI eager lv depth recName isK rules major
    if isCtorAppC fe majorE then pure majorE
    else do
      let major₀ ← whnfI eager lv depth majorE
      let major₁ ← litMajorToCtorI eager lv depth major₀
      majorToCtorI eager lv depth recName isK rules major₁
termination_by (lv, 26, 0, 0)

/-- Twin of `iotaRec`. -/
def iotaRecI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) := do
  match Expr.getAppFn e with
  | .const c us => do
    let cn ← pure c
    match fe.find? cn with
    | some (.recInfo cv mI rP isK rules) => do
      let args ← pure (Expr.getAppArgsC e)
      -- checker change #9 (twin of `Core.lean`'s `iotaRec`): guard the
      -- recursor's level arity before the rule's RHS is instantiated.
      if args.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
          (Expr.peelPis (mI + 1) cv.type).isSome = true then do
        let bvar0 ← pure (Expr.mkBvar 0)
        let major ← prepareMajorI eager lv depth cn isK rules (args.getD mI bvar0)
        match Expr.getAppFn major with
        | .const cj usj => do
          let cjn ← pure cj
          match fe.find? cjn with
          | some (.ctorInfo cvj cnP _) =>
            match rules.find? (fun r' => r'.ctor == cjn) with
            | some rl => do
              let margs ← pure (Expr.getAppArgsC major)
              if margs.length = cnP + rl.nfields then do
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
                      | .levels lvls => substLevelTreesM cv.levelParams us lvls
                    if ← iotaCase3I eager lv fe.find? isK cvj cmpLvls then do
                      let oL ← isEquivListLM usj cmpLvls
                      if ← liftFueled "level comparison" oL then do
                        let cmpArgs : List Expr ←
                          match rl.fire with
                          | .nested _ pins =>
                            pinArgsI cv.levelParams us (args.take rP) (rP - 1) pins
                          | .plain => pure (args.take cnP)
                          | .levels _ => pure (args.take cnP)
                        if ← defEqListI eager lv depth (margs.take cnP) cmpArgs then do
                          let tyCtor ← constTyAtM fe cj cjn usj
                          if ← iotaCertsFullI eager lv depth tyCtor margs then
                            iotaIndexOkI eager lv depth mI rP cnP tyCtor
                              margs ((args.take mI).drop rP)
                          else pure false
                        else pure false
                      else pure false
                    else pure true) then do
                  let rhs ← ruleRhsAtM fe c cj cn cjn us
                  let red ← mkAppNM rhs
                    (args.take rP ++ margs.drop cnP)
                  pure (some red)
                else pure none
              else pure none
            | none => pure none
          | _ => pure none
        | _ => pure none
      else pure none
    | _ => pure none
  | _ => pure none
termination_by (lv, 27, 0, 0)

/-- Twin of `reduceProjCore`. -/
def reduceProjCoreI (eager : Bool) (lv : Nat) (depth : Nat) (sn : Name)
    (i : Nat) (c : Expr) : CheckCM (Option Expr) := do
  let e' ← projLitToCtorI eager lv depth c
  let snn ← pure sn
  match fe.findProj? snn i with
  | some entry =>
    match Expr.getAppFn e' with
    | .const k us => do
      let args ← pure (Expr.getAppArgsC e')
      if (← pure (k == entry.ctor)) ∧ i < entry.numFields ∧
          args.length = entry.numParams + entry.numFields ∧
          us.length = entry.levelParams.length then do
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
termination_by (lv, 28, 0, 0)

/-- Peel loop of `whnfAppI`: `t` is the raw (unsubstituted) lambda body
after the binders consumed so far, `acc` their arguments (innermost
first).  The body is substituted once, when peeling stops, and handed
to the loop together with the arguments left over.  The substitution is
not memoised (`instantiateListC`, not `instListM`), as official's
`instantiate` keeps no cache across calls: a β redex's arguments, an ι
reduct's above all, rarely repeat, so a memo entry is a miss and an
insert nearly every time (task #572). -/
def betaPeelI (eager : Bool) (lv : Nat) (depth : Nat) :
    Expr → List Expr → List Expr → CheckCM WhnfStep
  | t, acc, [] => do
    let e' ← pure (Expr.instantiateListC t acc)
    pure (.cont e')
  | t, acc, a :: rest => do
    match t with
    | .lam _ body =>
        -- Task #342 S0: uniform β (see `whnfAppI`)
        betaPeelI eager lv depth body (a :: acc) rest
    | _ => do
      let e' ← pure (Expr.instantiateListC t acc)
      let e'' ← mkAppNM e' (a :: rest)
      pure (.cont e'')
termination_by _ _ args => (lv, 29, args.length, 0)

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
def whnfAppI (eager : Bool) (lv : Nat) (depth : Nat) :
    Expr → List Expr → CheckCM WhnfStep
  | v, [] => pure (.done v)
  | v, a :: rest => do
    match v with
    | .lam _ body =>
        -- Task #342 S0: uniform β, no certificate, at every λ
        betaPeelI eager lv depth body [a] rest
    | _ => do
      let fa ← pure (Expr.app v a)
      -- the ι step is tried only where it could fire; every other
      -- prefix of the spine returns `none` by `iotaRecI`'s own guard
      match ← (if iotaArityOk fe fa then iotaRecI eager lv depth fa
               else pure none) with
      | some e'' => do
        let e' ← mkAppNM e'' rest
        pure (.cont e')
      | none => whnfAppI eager lv depth fa rest
termination_by _ args => (lv, 30, args.length, 0)

/-- A spine `e` whose head `h` is its own head normal form and not a
lambda (official `whnf_core`'s `f == f0` arm,
`src/kernel/type_checker.cpp:525-536`): the ι step, tried once, at the
one prefix where it can fire (`iotaTargetF`), and otherwise the input
itself, with nothing rebuilt. -/
def whnfStuckI (eager : Bool) (lv : Nat) (depth : Nat) (h e : Expr) :
    CheckCM WhnfStep := do
  match iotaTargetF fe h with
  | some k =>
    if k ≤ iotaNumArgs e 0 then do
      let args ← pure (Expr.getAppArgsC e)
      match ← iotaRecI eager lv depth (Expr.mkAppN h (args.take k)) with
      | some e'' => do
        let e' ← mkAppNM e'' (args.drop k)
        pure (.cont e')
      | none => pure (.done e)
    else pure (.done e)
  | none => pure (.done e)
termination_by (lv, 30, 0, 0)

/-- One head-normalization step of `whnfCoreBody` (beta, iota,
projection), returning the head normal form or the term to continue
with; `cheap` is the official `cheap_proj` flag (see `whnfCoreBody`).
Only the spine head's normalization stays a knot call (genuine
nesting, bounded by the term's depth); every *reduction* step is
iteration, so a chain does not charge the shared recursion-depth
budget per step (task #106: a `Nat.brecOn` grind would exhaust `checkFuel`).
`whnfCoreLoopI` continues with the step's result by a tail call; it
passes the term's spine head `h` (`Expr.getAppFn e`), which it computes
once per step for its memo policy as well. -/
def whnfCoreStepI (eager : Bool) (lv : Nat) (cheap : Bool) (depth : Nat)
    (h e : Expr) : CheckCM WhnfStep := do
    match e with
    | .sort _ | .fvar .. | .forallE ..
    | .lam .. | .const .. | .lit _ => pure (.done e)
    | .app _ _ => do
      -- `h` is the spine head, computed by the loop
      -- a head that is its own head normal form: the spine is stuck but
      -- for ι, and is answered by itself
      if isStuckHeadC h then whnfStuckI eager lv depth h e
      else do
        -- Bulk beta (task #50): normalize the spine head once and run
        -- the argument loop over the whole spine, batching consecutive
        -- lambda binders into one substitution.
        let args ← pure (Expr.getAppArgsC e)
        let v ← whnfCoreI eager lv cheap depth h
        whnfAppI eager lv depth v args
    | .proj sn i pe => do
      -- the scrutinee by `whnf`, or by the cheap `whnfCore` in the
      -- cheap mode; stuck: the input itself, scrutinee as it was (see
      -- `whnfCoreBody`)
      let c ← if cheap then whnfCoreI eager lv true depth pe else whnfI eager lv depth pe
      match ← reduceProjCoreI eager lv depth sn i c with
      | some m' => pure (.cont m')
      | none => pure (.done e)
    | .letE _ v b => do
      -- Task #342 S0: ζ, Lean's way (lets are stored as Lean stores them)
      let e' ← inst1M b v
      pure (.cont e')
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")
termination_by (lv, 31, 0, 0)

/-- Iterate `whnfCoreStepI` on its own step budget, with official
`whnf_core`'s memo policy (`src/kernel/type_checker.cpp`, `whnf_core`).
Official recurses: every call on a term that is not easy looks the term
up, and after the recursive call on its reduct returns, stores the
answer for the β, projection, ζ and head-reduced arms, but not for the
ι and stuck arms (`f == f0`), and only when not in a cheap mode.  The
loop follows it iteratively: every step looks its term up
(`whnfCoreKeyC`: a term no arm stores is not looked up), a hit ends the
chain, and the keys of the steps taken so far (`pend`) wait for the
chain's answer, stored at its end (`storeChainI`).  The continuation
is a self tail call, compiled to a jump (task #342 R2): a reduction
chain of any length runs in constant native stack, and a
non-terminating one runs until the external timeout.

**The cheap mode.**  Official has one memo, read in both modes and
written only by the full one; a cheap query can so be answered by a
full answer, which the cheap specification need not compute (a
projection whose scrutinee needs δ).  Here the cheap mode reads its
own memo, `whnfCoreCheapC`, and stores nothing, as official; the full
mode writes there the keys whose chain from the key on takes no step
the two modes take differently (`whnfCoreCheapSafeC`; `pendC`, emptied
at any other step and at a hit). -/
def whnfCoreLoopI (eager : Bool) (lv : Nat) (cheap : Bool) (depth : Nat) :
    Nat → List Expr → List Expr → Expr → CheckCM Expr
  | 0, _, _, _ => throw (.internal "fuel exhausted: whnfCore loop")
  | n + 1, pend, pendC, e => do
    if whnfCoreEasy e then
      storeChainI cheap pend pendC e
      pure e
    else
      let h := Expr.getAppFn e
      let key := whnfCoreKeyC h e
      match ← (if key then whnfCoreLookupI cheap e else pure none) with
      | some r =>
        storeChainI cheap pend [] r
        pure r
      | none =>
        let safe := whnfCoreCheapSafeC h e
        match ← whnfCoreStepI eager lv cheap depth h e with
        | .done v =>
          let st := !cheap && whnfCoreStoresDone key e v
          storeChainI cheap (pushKey st e pend) (pushCheapKey safe st e pendC) v
          pure v
        | .cont e' =>
          let st := !cheap && key
          whnfCoreLoopI eager lv cheap depth n (pushKey st e pend) (pushCheapKey safe st e pendC) e'
termination_by n _ _ _ => (lv, 32, n, 0)

/-- Twin of `whnfCoreBody`: the head-normalization loop at its own step
budget, with no key pending. -/
def whnfCoreBodyI (eager : Bool) (lv : Nat) : Bool → Nat → Expr → CheckCM Expr :=
  fun cheap depth e => whnfCoreLoopI eager lv cheap depth whnfCoreLoopFuel [] [] e
termination_by (lv, 33, 0, 0)

/-- Twin of `defeqArg`: an `eagerReduce _ _` argument's type is
compared in the eager tower. -/
def defeqArgI (eager : Bool) (lv : Nat) (depth : Nat) (a ta ty : Expr) : CheckCM Bool :=
  if Expr.isEagerReduce a then defeqEI eager lv depth ta ty else defeqI eager lv depth ta ty
termination_by (lv, 34, 0, 0)

/-- Application-inference spine loop (task #50): walk the raw
Π-telescope against the arguments with deferred substitution — each
argument's certificate substitutes only its *domain*; the codomain is
substituted once per peeled group.  A non-syntactic telescope step
substitutes and normalizes, exactly like the chained `inferBody`
recursion (`ConLeche/Verify/BetaSpine.lean` proves the
identification). -/
def inferSpineI (eager : Bool) (lv : Nat) (io : Bool) (depth : Nat) :
    Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ty with
    | .forallE dom body => do
      -- the per-argument check, unconditional at the full grade, as
      -- in the spec body `inferBody`
      let dom' ← instListRevM dom acc
      let ta ← inferI eager lv io depth a
      unless ← defeqArgI eager lv depth a ta dom' do
        throw (.invalid "application type mismatch")
      inferSpineI eager lv io depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← whnfI eager lv depth ty'
      match w with
      | .forallE dom body => do
        let ta ← inferI eager lv io depth a
        unless ← defeqArgI eager lv depth a ta dom do
          throw (.invalid "application type mismatch")
        inferSpineI eager lv io depth body #[a] rest
      | _ => throw (.invalid "function expected")
termination_by _ _ args => (lv, 35, args.length, 0)

/-- **The io-grade spine walk**: `inferBodyIO`'s app clause
(`ConLeche/Kernel/Core.lean`) in the bulk telescope form — official's
`infer_only`: the function's type is walked through the arguments with
no argument inference and no domain comparison (task #342).  A
syntactic `.forallE` is its own whnf; anything else is instantiated and
whnf'd before the next step. -/
def inferSpineIOI (eager : Bool) (lv : Nat) (depth : Nat) :
    Expr → Array Expr → List Expr → CheckCM Expr
  | ty, acc, [] => instListRevM ty acc
  | ty, acc, a :: rest => do
    match ty with
    | .forallE _ body => do
      inferSpineIOI eager lv depth body (acc.push a) rest
    | _ => do
      let ty' ← instListRevM ty acc
      let w ← whnfI eager lv depth ty'
      match w with
      | .forallE _ body => do
        inferSpineIOI eager lv depth body #[a] rest
      | _ => throw (.invalid "function expected")
termination_by _ _ args => (lv, 36, args.length, 0)

/-- Twin of `whnfLoop`, each step `whnfStep`'s: the continuation of a
step is the loop's own tail call, which the compiler turns into a jump,
so a δ chain of any length runs in constant native stack (task #342 R2:
a non-terminating δ chain — Coquand's paradox — runs until the external
timeout instead of overflowing the stack). -/
def whnfLoopI (eager : Bool) (lv : Nat) (depth : Nat) :
    Nat → Expr → CheckCM Expr
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => do
    let e₁ ← whnfCoreI eager lv false depth e
    match ← reduceNatI eager lv depth e₁ with
    -- a computed literal is the answer (official `whnf`: `if (auto v =
    -- reduce_nat(t)) return *v;`); a `Bool` constructor goes on (see
    -- `whnfStep`)
    | some e₂ => if e₂.isLit then pure e₂ else whnfLoopI eager lv depth n e₂
    | none =>
      match ← unfoldDefinitionI fe e₁ with
      | some e₂ => whnfLoopI eager lv depth n e₂
      | none => pure e₁
termination_by n _ => (lv, 37, n, 0)

/-- Twin of `whnfBody`. -/
def whnfBodyI (eager : Bool) (lv : Nat) : Nat → Expr → CheckCM Expr :=
  fun depth e => whnfLoopI eager lv depth whnfLoopFuel e
termination_by (lv, 38, 0, 0)

/-- Twin of `ensureSort` (returns the level; no readback needed). -/
def ensureSortI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) : CheckCM Level := do
  let w ← whnfI eager lv depth e
  match w with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")
termination_by (lv, 39, 0, 0)

/-- Twin of `checkGuardRows`. -/
def checkGuardRowsI (eager : Bool) (lv : Nat) (guardSort : Level) :
    List (Nat × Expr) → CheckCM Unit
  | [] => pure ()
  | (d, dom) :: rest => do
    let t ← inferI eager lv true d dom
    let w ← whnfI eager lv d t
    match w with
    | .sort u =>
      unless Level.zeroWhereZero guardSort u do
        throw (.invalid "projection from a propositional structure must be a proposition")
      checkGuardRowsI eager lv guardSort rest
    | _ => throw (.invalid "expected a sort")
termination_by rows => (lv, 40, rows.length, 0)

/-- Twin of `projGuardSort`. -/
def projGuardSortI (eager : Bool) (lv : Nat) (cvT : ConstantVal) (caps : IndCaps)
    (us : List Level) : CheckCM (Option Level) :=
  match formerResSort cvT.type with
  | some s => pure (if s.isAlwaysZero then some .zero else none)
  | none => do
    let ty ← instLevelParamsM cvT.levelParams us cvT.type
    let o ← formerSortLoopI eager lv 0 (caps.nparams + caps.nIdx) ty
    match o with
    | some s => pure (if (Level.zeronessOf s).isNever then none else some s)
    | none => throw (.invalid "projection from a structure whose type reaches no sort")
termination_by (lv, 41, 0, 0)

/-- The rows of a projection's guard, against the sort they answer to. -/
def checkProjRowsI (eager : Bool) (lv : Nat) (entry : ProjEntry)
    (us : List Level) (guardSort : Level) : CheckCM Unit :=
  match fe.find? entry.ctor with
  | some _ => do
    let cty ← constTyAtM fe entry.ctor entry.ctor us
    match projGuardRowsC entry.numParams entry.idx cty with
    | some rows => checkGuardRowsI eager lv guardSort rows
    | none =>
      throw (.invalid "projection from a propositional structure must be a proposition")
  | none =>
    throw (.invalid "projection from a propositional structure must be a proposition")
termination_by (lv, 42, 0, 0)

/-- Twin of `checkProjGuard`: the constructor's type at the use's levels
through the per-declaration memo (`constTyAtM`), then its rows
(`projGuardRowsC`: the parameters opened in one pass, the field
telescope read before it is rebuilt). -/
def checkProjGuardI (eager : Bool) (lv : Nat) (entry : ProjEntry)
    (us : List Level) : CheckCM Unit := do
  match fe.find? entry.structName with
  | some (.indInfo cvT caps) => do
    let b? ← projGuardSortI eager lv cvT caps us
    match b? with
    | none => pure ()
    | some guardSort => checkProjRowsI eager lv entry us guardSort
  | _ => throw (.invalid "projection from a propositional structure must be a proposition")

/- ### Binder-telescope loops (task #72)

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
termination_by (lv, 43, 0, 0)

/-- Leaf phase of `inferLamsI`: bulk-open the residual body, infer it,
then rebuild outward.

Task #152: at the verified modes the chain's body type is
sort-checked here — the spec's codomain check (`inferBody`'s `.lam`
clause), which fires at the innermost binder of a λ-chain, i.e.
exactly when the peel stops on a non-λ residual.  The guard is the
same one the spec uses, on the same term. -/
def inferLamsLeafI (eager : Bool) (lv : Nat) (io : Bool) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Expr) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← inferI eager lv io (d + k) ob
  let cur ← abstractRangeM bt d k
  inferLamsOutI d stk (k - 1) cur
termination_by (lv, 44, 0, 0)

/-- λ-telescope inference loop (task #72; used by `inferBodyI`'s and
`inferBodyIOI`'s lam cases): peel the raw λ-chain, checking each opened
domain to be a type on the way in.  `k` counts the opened binders
(`≥ 1`: the caller peels the first binder inline), `fvs` their free
variables innermost-first. -/
def inferLamsI (eager : Bool) (lv : Nat) (io : Bool) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List Expr → CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match t with
    | .lam ty body => do
      let tyo ← instListRevM ty fvs
      let tty ← inferI eager lv io (d + k) tyo
      let wtty ← whnfI eager lv (d + k) tty
      match wtty with
      | .sort _ => do
        let fv ← pure (Expr.fvar (d + k) tyo)
        inferLamsI eager lv io d fuel body (k + 1) (fvs.push fv)
          (tyo :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferLamsLeafI eager lv io d t k fvs stk
  | 0, t, k, fvs, stk => inferLamsLeafI eager lv io d t k fvs stk
termination_by f _ _ _ _ => (lv, 45, f, 0)

/-- Leaf phase of `inferPisI`: bulk-open the residual body, infer its
sort, then fold the domain sorts outward. -/
def inferPisLeafI (eager : Bool) (lv : Nat) (io : Bool) (d : Nat) (t : Expr) (k : Nat)
    (fvs : Array Expr) (stk : List Level) : CheckCM Expr := do
  let ob ← instListRevM t fvs
  let bt ← inferI eager lv io (d + k) ob
  let wbt ← whnfI eager lv (d + k) bt
  match wbt with
  | .sort v => do
    let iv ← inferPisOutI stk v
    pure (Expr.sort iv)
  | _ => throw (.invalid "expected a sort")
termination_by (lv, 46, 0, 0)

/-- ∀-telescope inference loop (task #100 stage 6: the `∀`-rule infers
its codomain sort): peel the raw
∀-chain, checking each opened domain to be a type on the way in and
accumulating its sort, infer the bulk-opened leaf's sort once, and
fold `imax` outward. -/
def inferPisI (eager : Bool) (lv : Nat) (io : Bool) (d : Nat) :
    Nat → Expr → Nat → Array Expr → List Level →
      CheckCM Expr
  | fuel + 1, t, k, fvs, stk => do
    match t with
    | .forallE ty body => do
      let tyo ← instListRevM ty fvs
      let tty ← inferI eager lv io (d + k) tyo
      let wtty ← whnfI eager lv (d + k) tty
      match wtty with
      | .sort u => do
        let fv ← pure (Expr.fvar (d + k) tyo)
        inferPisI eager lv io d fuel body (k + 1) (fvs.push fv)
          (u :: stk)
      | _ => throw (.invalid "expected a sort")
    | _ => inferPisLeafI eager lv io d t k fvs stk
  | 0, t, k, fvs, stk => inferPisLeafI eager lv io d t k fvs stk
termination_by f _ _ _ _ => (lv, 47, f, 0)

/-- Twin of `inferBody`. -/
def inferBodyI (eager : Bool) (lv : Nat) (io : Bool) : Nat → Expr → CheckCM Expr :=
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
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {nm}")
        constTyAtM fe n nm us
    | .lit (.natVal n) => do
      if natLitStoredF fe then do
        -- a numeral entering the checker is bounded by `maxNatSize` too
        -- (official `infer_lit`)
        let maxNatSize ← maxNatSizeM
        if natSizeBytes n > maxNatSize then throw natNumeralTooBig
        let ni ← pure natName
        pure (Expr.const ni [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if strLitStoredF fe then do
        let si ← pure stringName
        pure (Expr.const si [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body => do
      -- Binder-telescope loop (task #72 discipline; the codomain sort
      -- is inferred).
      let tty ← inferI eager lv io depth ty
      let wtty ← whnfI eager lv depth tty
      match wtty with
      | .sort u => do
        let fv ← pure (Expr.fvar depth ty)
        let fuel ← peelFuelM
        inferPisI eager lv io depth fuel body 1 #[fv] [u]
      | _ => throw (.invalid "expected a sort")
    | .lam ty body => do
      let tty ← inferI eager lv io depth ty
      let wtty ← whnfI eager lv depth tty
      match wtty with
      | .sort _ => do
        -- Binder-telescope loop (task #72): peel the whole λ-chain,
        -- open in bulk, rebuild with `abstractRange`.
        let fv ← pure (Expr.fvar depth ty)
        let fuel ← peelFuelM
        inferLamsI eager lv io depth fuel body 1 #[fv] [ty]
      | _ => throw (.invalid "expected a sort")
    | .app _ _ => do
      -- Bulk telescope consumption (task #50): infer the spine head
      -- once and walk its Π-telescope against the whole spine.
      let h ← pure (Expr.getAppFn e)
      let args ← pure (Expr.getAppArgsC e)
      let tf ← inferI eager lv io depth h
      inferSpineI eager lv io depth tf #[] args
    | .proj sn i pe => do
      let tpe ← inferI eager lv io depth pe
      let te ← whnfI eager lv depth tpe
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
            -- the official `infer_proj` restriction, as in the spec body
            checkProjGuardI eager lv entry us
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
      let tty ← inferI eager lv io depth ty
      let _ ← ensureSortI eager lv depth tty
      let tv ← inferI eager lv io depth v
      unless ← defeqI eager lv depth tv ty do
        throw (.invalid "let value type mismatch")
      let ob ← inst1M b v
      inferI eager lv io depth ob
    | .bvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")
termination_by (lv, 48, 0, 0)

/-- **The io-grade inference body** (task #172 B4): `inferBodyI` with
the application, ∀, λ and `let` clauses changed — the spine walk is
`inferSpineIOI` (no argument check), the binder clauses are chained
(the λ's runs no domain-sort check) and the `let` clause checks
neither the type nor the value, as `inferBodyIO` does.  Every other
view dispatches to `inferBodyI`'s own clause.
Recursion grade: every inference here is the io entry point one level
down (`inferI … true`), and the clauses it shares with `inferBodyI` run
there at `io := true` — the grade propagates exactly as official's
`infer_only` does. -/
def inferBodyIOI (eager : Bool) (lv : Nat) : Nat → Expr → CheckCM Expr :=
  fun depth e => do
    match e with
    | .app _ _ => do
      let h ← pure (Expr.getAppFn e)
      let args ← pure (Expr.getAppArgsC e)
      let tf ← inferI eager lv true depth h
      inferSpineIOI eager lv depth tf #[] args
    | .forallE ty body => do
      -- the pure io ∀ clause, **chained** (deliberately not the
      -- task-#72 telescope loop: the loops are the front door's
      -- optimization, and looping the io lane would owe the whole
      -- loop-identification walk family a second, io-graded instance
      -- for a lane whose subjects are internal re-inferences —
      -- recorded in the B4 seal as a measured-need follow-up)
      let tty ← inferI eager lv true depth ty
      let wtty ← whnfI eager lv depth tty
      match wtty with
      | .sort u => do
        let fv ← pure (Expr.fvar depth ty)
        let ob ← inst1M body fv
        let bt ← inferI eager lv true (depth + 1) ob
        let v ← ensureSortI eager lv (depth + 1) bt
        let iu ← pure (.imax u v)
        pure (Expr.sort iu)
      | _ => throw (.invalid "expected a sort")
    | .lam ty body => do
      -- the pure io λ clause, chained; no domain-sort run (task #168
      -- stage 2, as in the spec)
      let fv ← pure (Expr.fvar depth ty)
      let ob ← inst1M body fv
      let bt ← inferI eager lv true (depth + 1) ob
      let bAbs ← abstract1M bt depth
      pure (Expr.forallE ty bAbs)
    | .letE _ v b => do
      -- official `infer_let` at `infer_only`: the body at its value,
      -- no check of the type or the value (task #342 R-C)
      let ob ← inst1M b v
      inferI eager lv true depth ob
    | _ => inferBodyI eager lv true depth e
termination_by (lv, 49, 0, 0)

/-- Twin of `boolTrueShortcut`. -/
def boolTrueShortcutI (eager : Bool) (lv : Nat) (depth : Nat) (a : Expr) : CheckCM Bool := do
  let w ← whnfI eager lv depth a
  pure (Expr.isBoolTrue w)
termination_by (lv, 50, 0, 0)

/-- Twin of `defeqBindersInner`. -/
def defeqBindersInnerI (eager : Bool) (lv : Nat) (lam : Bool) (depth : Nat) (b₁ b₂ : Expr) :
    CheckCM Bool := do
  unless ← defeqI eager lv (depth + 1) b₁ b₂ do return false
  if lam && mode.verifiedChecks then do
    let t₁ ← inferI eager lv false (depth + 1) b₁
    let t₂ ← inferI eager lv false (depth + 1) b₂
    unless ← defeqI eager lv (depth + 1) t₁ t₂ do return false
  pure true
termination_by (lv, 51, 0, 0)

/-- Twin of `defeqDomain`. -/
def defeqDomainI (eager : Bool) (lv : Nat) (depth : Nat) (fvs : Array Expr) (ty₁ ty₂ dom₂ : Expr) :
    CheckCM Bool :=
  if ty₁ == ty₂ then pure true else do
    let dom₁ ← instListRevM ty₁ fvs
    defeqI eager lv depth dom₁ dom₂
termination_by (lv, 52, 0, 0)

/-- Twin of `defeqBinders`: the variables so far are an `Array`,
outermost first (the spec's list reversed), so that each opening is
one `instantiateRev` walk over it. -/
def defeqBindersI (eager : Bool) (lv : Nat) (lam : Bool) :
    Nat → Nat → Array Expr → Expr → Expr → Expr → Expr → CheckCM Bool
  | fuel, depth, fvs, ty₁, body₁, ty₂, body₂ => do
    let dom₂ ← instListRevM ty₂ fvs
    unless ← defeqDomainI eager lv depth fvs ty₁ ty₂ dom₂ do return false
    let fvs' ← pure (fvs.push (Expr.fvar depth dom₂))
    match fuel, Expr.binderPair? lam body₁ body₂ with
    | fuel + 1, some (ty₁', body₁', ty₂', body₂') =>
      defeqBindersI eager lv lam fuel (depth + 1) fvs' ty₁' body₁' ty₂' body₂'
    | _, _ => do
      let b₁ ← instListRevM body₁ fvs'
      let b₂ ← instListRevM body₂ fvs'
      defeqBindersInnerI eager lv lam depth b₁ b₂
termination_by f _ _ _ _ _ _ => (lv, 53, f, 0)

/-- Twin of `quickDefEq`. -/
def quickDefEqI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM (Option Bool) :=
  if a == b then pure (some true) else
  match a, b with
  | .sort u, .sort v => do
    let ok ← liftFueled "level comparison" (← isEquivLM u v)
    pure (some ok)
  | .lit l₁, .lit l₂ => pure (some (l₁ == l₂))
  | .forallE ty₁ body₁, .forallE ty₂ body₂ => do
    let ok ← defeqBindersI eager lv false bindersFuel depth #[] ty₁ body₁ ty₂ body₂
    pure (some ok)
  | .lam ty₁ body₁, .lam ty₂ body₂ => do
    let ok ← defeqBindersI eager lv true bindersFuel depth #[] ty₁ body₁ ty₂ body₂
    pure (some ok)
  | _, _ => pure none
termination_by (lv, 54, 0, 0)

/-- Twin of `defeqOffset`. -/
def defeqOffsetI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM (Option Bool) :=
  if a.isNatZero && b.isNatZero then pure (some true) else
  if a.isLit && b.isLit then pure none else
  match a.natPred?, b.natPred? with
  | some x, some y => do
    let ok ← defeqI eager lv depth x y
    pure (some ok)
  | _, _ => pure none
termination_by (lv, 55, 0, 0)

/-- Twin of `tryUnfoldProjApp`. -/
def tryUnfoldProjAppI (eager : Bool) (lv : Nat) (depth : Nat) (e : Expr) :
    CheckCM (Option Expr) :=
  if Expr.headIsProj e then do
    let e' ← whnfCoreI eager lv false depth e
    if e' == e then pure none else pure (some e')
  else pure none
termination_by (lv, 56, 0, 0)

/-- Twin of `deltaQuick`. -/
def deltaQuickI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) : CheckCM DeltaStep := do
  match ← quickDefEqI eager lv depth a b with
  | some true => pure .eq
  | some false => pure .diff
  | none => pure (.cont a b)
termination_by (lv, 57, 0, 0)

/-- Twin of `lazyDeltaStep`. -/
def lazyDeltaStepI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM DeltaStep := do
  match ← pure (unfoldableHeadC fe a), ← pure (unfoldableHeadC fe b) with
  | false, false => pure .unknown
  | true, false =>
    match ← tryUnfoldProjAppI eager lv depth b with
    | some b₂ => deltaQuickI eager lv depth a b₂
    | none =>
      match ← unfoldDefinitionI fe a with
      | some a₂ => do
        let a₃ ← whnfCoreI eager lv true depth a₂
        deltaQuickI eager lv depth a₃ b
      | none => pure .unknown
  | false, true =>
    match ← tryUnfoldProjAppI eager lv depth a with
    | some a₂ => deltaQuickI eager lv depth a₂ b
    | none =>
      match ← unfoldDefinitionI fe b with
      | some b₂ => do
        let b₃ ← whnfCoreI eager lv true depth b₂
        deltaQuickI eager lv depth a b₃
      | none => pure .unknown
  | true, true => do
    let ha ← pure (headHintC fe a)
    let hb ← pure (headHintC fe b)
    if ReducibilityHint.lt hb ha then
      match ← unfoldDefinitionI fe a with
      | some a₂ => do
        let a₃ ← whnfCoreI eager lv true depth a₂
        deltaQuickI eager lv depth a₃ b
      | none => pure .unknown
    else if ReducibilityHint.lt ha hb then
      match ← unfoldDefinitionI fe b with
      | some b₂ => do
        let b₃ ← whnfCoreI eager lv true depth b₂
        deltaQuickI eager lv depth a b₃
      | none => pure .unknown
    else if ← (if ReducibilityHint.sameRegular ha hb &&
        (← pure (sameConstHeadsC a b)) then
        defeqSpineI eager lv depth a b else pure false) then pure .eq
    else
      match ← unfoldDefinitionI fe a, ← unfoldDefinitionI fe b with
      | some a₂, some b₂ => do
        let a₃ ← whnfCoreI eager lv true depth a₂
        let b₃ ← whnfCoreI eager lv true depth b₂
        deltaQuickI eager lv depth a₃ b₃
      | _, _ => pure .unknown
termination_by (lv, 58, 0, 0)

/-- Twin of `lazyDeltaReduction`. -/
def lazyDeltaReductionI (eager : Bool) (lv : Nat) (depth : Nat) :
    Nat → Expr → Expr → CheckCM LazyRes
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | n + 1, a, b => do
    match ← defeqOffsetI eager lv depth a b with
    | some v => pure (.verdict v)
    | none =>
    -- the eager flag (task #353) folds with free variables present
    let fold ← pure (eager || (!Expr.hasFvar a && !Expr.hasFvar b))
    match ← (if fold then reduceNatI eager lv depth a else pure none) with
    | some a₂ => do
      let v ← defeqI eager lv depth a₂ b
      pure (.verdict v)
    | none =>
    match ← (if fold then reduceNatI eager lv depth b else pure none) with
    | some b₂ => do
      let v ← defeqI eager lv depth a b₂
      pure (.verdict v)
    | none =>
    match ← lazyDeltaStepI eager lv depth a b with
    | .cont a' b' => lazyDeltaReductionI eager lv depth n a' b'
    | .eq => pure (.verdict true)
    | .diff => pure (.verdict false)
    | .unknown => pure (.unknown a b)
termination_by n _ _ => (lv, 59, n, 0)

/-- Twin of `lazyDeltaProjReduction`. -/
def lazyDeltaProjReductionI (eager : Bool) (lv : Nat) (depth : Nat)
    (sn : Name) (i : Nat) : Nat → Expr → Expr → CheckCM Bool
  | 0, _, _ => throw (.internal "fuel exhausted: lazy delta projection loop")
  | n + 1, a, b => do
    match ← lazyDeltaStepI eager lv depth a b with
    | .cont a' b' => lazyDeltaProjReductionI eager lv depth sn i n a' b'
    | .eq => pure true
    | .diff | .unknown =>
      match ← reduceProjCoreI eager lv depth sn i a with
      | some x =>
        match ← reduceProjCoreI eager lv depth sn i b with
        | some y => defeqI eager lv depth x y
        | none => defeqI eager lv depth a b
      | none => defeqI eager lv depth a b
termination_by n _ _ => (lv, 60, n, 0)

/-- Twin of `defeqProjPair`. -/
def defeqProjPairI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM Bool :=
  match a, b with
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ =>
    if s₁ == s₂ && i₁ == i₂ then
      lazyDeltaProjReductionI eager lv depth s₁ i₁ defeqLoopFuel e₁ e₂
    else pure false
  | _, _ => pure false
termination_by (lv, 61, 0, 0)

/-- Twin of `defeqStuck`. -/
def defeqStuckI (eager : Bool) (lv : Nat) (depth : Nat) (a b : Expr) :
    CheckCM Bool :=
  match a, b with
  | .lit l, .app fO _x => do
    match l, fO with
    | .strVal s, .const cO usO =>
      if (← pure (cO == stringOfListName)) ∧ usO = [] ∧ strLitStoredF fe then do
        let sc ← pure (strLitToConstructor s)
        defeqI eager lv depth sc b
      else stuckIrrelI eager lv depth a b
    | _, _ => stuckIrrelI eager lv depth a b
  | .app fO _x, .lit l => do
    match l, fO with
    | .strVal s, .const cO usO =>
      if (← pure (cO == stringOfListName)) ∧ usO = [] ∧ strLitStoredF fe then do
        let sc ← pure (strLitToConstructor s)
        defeqI eager lv depth a sc
      else stuckIrrelI eager lv depth a b
    | _, _ => stuckIrrelI eager lv depth a b
  | .fvar i _, .fvar j _ =>
    if i == j then pure true
    else stuckIrrelI eager lv depth a b
  | .const n us, .const n' us' =>
    if n = n' then do
      if ← liftFueled "level comparison" (← isEquivListLM us us') then
        pure true
      else stuckIrrelI eager lv depth a b
    else stuckIrrelI eager lv depth a b
  | .app _f₁ _a₁, .app _f₂ _a₂ => do
    -- spine-wise congruence, as in the spec (official `is_def_eq_app`)
    let as₁ ← pure (Expr.getAppArgsC a)
    let as₂ ← pure (Expr.getAppArgsC b)
    if as₁.length = as₂.length then do
      let h₁ ← pure (Expr.getAppFn a)
      let h₂ ← pure (Expr.getAppFn b)
      if ← defeqI eager lv depth h₁ h₂ then do
        if ← defEqListI eager lv depth as₁ as₂ then pure true
        else stuckIrrelI eager lv depth a b
      else stuckIrrelI eager lv depth a b
    else stuckIrrelI eager lv depth a b
  | .lam ty₁ body₁, _ => do
    if ← etaCertI eager lv depth ty₁ body₁ b then pure true
    else stuckIrrelI eager lv depth a b
  | _, .lam ty₂ body₂ => do
    if ← etaCertI eager lv depth ty₂ body₂ a then pure true
    else stuckIrrelI eager lv depth a b
  | _, _ => stuckIrrelI eager lv depth a b
termination_by (lv, 62, 0, 0)

/-- Twin of `defeqBody`. -/
def defeqBodyI (eager : Bool) (lv : Nat) : Nat → Expr → Expr → CheckCM Bool :=
  fun depth a b => do
    if a == b then pure true else
    -- the eq-true shortcut (E2), as in the spec
    let bt ← pure (Expr.isBoolTrue b)
    let af ← pure (Expr.hasFvar a)
    if ← (if bt && (eager || !af) then boolTrueShortcutI eager lv depth a
        else pure false) then pure true else
    match ← quickDefEqI eager lv depth a b with
    | some v => pure v
    | none =>
    -- task #333: proof irrelevance before any head normalization
    if ← propIrrelI eager lv depth a b then pure true else
    let a' ← whnfCoreI eager lv true depth a
    let b' ← whnfCoreI eager lv true depth b
    match ← quickDefEqI eager lv depth a' b' with
    | some v => pure v
    | none =>
    match ← lazyDeltaReductionI eager lv depth defeqLoopFuel a' b' with
    | .verdict v => pure v
    | .unknown a₁ b₁ =>
    if ← defeqProjPairI eager lv depth a₁ b₁ then pure true else
    if !(Expr.headIsProj a₁) && !(Expr.headIsProj b₁) then
      defeqStuckI eager lv depth a₁ b₁ else
    let a₂ ← whnfCoreI eager lv false depth a₁
    let b₂ ← whnfCoreI eager lv false depth b₁
    if a₂ == a₁ && b₂ == b₁ then defeqStuckI eager lv depth a₁ b₁
    else defeqI eager lv depth a₂ b₂
termination_by (lv, 63, 0, 0)

/-- **The whnfCore entry point** at knot level `lv`: the loop, which
looks its terms up in the mode's memo (`whnfCoreLoopI`). -/
def whnfCoreI (eager : Bool) : Nat → Bool → Nat → Expr → CheckCM Expr
  | 0, _, _, _ => throw (.internal "fuel exhausted: whnfCore")
  | lv + 1, c, d, e => whnfCoreBodyI eager lv c d e
termination_by lv _ _ _ => (lv, 0, 0, 0)

/-- **The whnf entry point**; its easy cases (`whnfEasy`) return before
the memo, as official: each computed literal would otherwise become a
`lit ↦ lit` entry (task #549: 14.5 GB of keys on CFSG's C20). -/
def whnfI (eager : Bool) : Nat → Nat → Expr → CheckCM Expr
  | 0, _, _ => throw (.internal "fuel exhausted: whnf")
  | lv + 1, d, e =>
    if whnfEasy e then pure e
    else memoEI (·.whnfC) (fun st mp => { st with whnfC := mp })
      (fun d e => whnfBodyI eager lv d e) d e
termination_by lv _ _ => (lv, 0, 0, 0)

/-- **The inference entry point**, at the full grade (`io := false`) or
at the io grade (`io := true`, task #170 / #172 B4, task #346:
official's `infer_only`).  The io body runs under its OWN memo
(`CState.inferIOC` — the task-#170 memo ruling: a hit in the io memo
never serves a full-infer query). -/
def inferI (eager : Bool) : Nat → Bool → Nat → Expr → CheckCM Expr
  | 0, _, _, _ => throw (.internal "fuel exhausted: infer")
  | lv + 1, io, d, e =>
    if io then
      memoEI (·.inferIOC) (fun st mp => { st with inferIOC := mp })
        (fun d e => inferBodyIOI eager lv d e) d e
    else memoEI (·.inferC) (fun st mp => { st with inferC := mp })
      (fun d e => inferBodyI eager lv false d e) d e
termination_by lv _ _ _ => (lv, 0, 0, 0)

/-- **The definitional-equality entry point**, in the tower `eager`. -/
def defeqI (eager : Bool) : Nat → Nat → Expr → Expr → CheckCM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: defeq")
  | lv + 1, d, a, b => memoBI (fun d a b => defeqBodyI eager lv d a b) d a b
termination_by lv _ _ _ => (lv, 0, 0, 0)

/-- **The eager entry point** (task #353): the comparison in the eager
tower — the bodies at `eager := true` one level down — on its own memos,
kept in the state between eager comparisons (`withEagerMemos`, task #361:
an eager entry never serves a plain query). -/
def defeqEI (eager : Bool) : Nat → Nat → Expr → Expr → CheckCM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: defeq")
  | lv + 1, d, a, b =>
    withEagerMemos eager (memoBI (fun d a b => defeqBodyI true lv d a b) d a b)
termination_by lv _ _ _ => (lv, 0, 0, 0)
end

end Knot

end ConLeche.Cached
