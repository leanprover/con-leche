module

import ConLeche.Kernel.Level
import ConLeche.Kernel.ExprOps
public import ConLeche.Kernel.BVUnsat

@[expose] public section

/-!
# The checker core, in open-recursion style

Every core function is written **once**, as a non-recursive *body*
parameterized over a record of the mutually recursive entry points
(`CoreFns`) and polymorphic in the monad.  All recursion is routed
through the record — bodies never call themselves, and the few helpers
that do recurse (`iotaCertsFull`, `defEqList`) do so
structurally on a list.  Fuel lives only in the *knots* that tie the
record: the pure knot (`ConLeche.Kernel.TypeChecker`) instantiates the
bodies at `CheckM` and is the verification's subject; the cached knot
(`ConLeche.Cached.CoreC`) instantiates them over the cached
representation with the memo caches and is what the checker executes.
A refinement bridge relates the two (see DESIGN.md).

The reduction loop follows the official kernel (`whnfCore` never
delta-unfolds; `whnf` iterates `whnfCore → reduceNat → unfold one
definition`), and definitional equality starts with the syntactic fast
path and tries proof irrelevance before structural congruence.
Inference comes at two grades, as in the official kernel: the full
grade (`inferBody`) checks application arguments, λ domains and `let`
values; the infer-only grade (`inferBodyIO`, the knot's `inferIO`
slot) re-derives a type without those checks and is what reduction and
definitional equality call on their own intermediate terms.

Verification: `ConLeche.Model.*` and `ConLeche.Verify.*` (claims),
`ConLeche.Verify.*` (inversions), both stated against the bodies with
hypotheses about the record and discharged by one induction at the
knot.

The core's **fuel-free helpers** — everything a body reads that
mentions no monad, no record and no fuel (`unfoldDefinition`, the
literal guards, the certified `Nat` operations' tables, the η
fabrications, the install-time rule bits, …) — live
in `ConLeche/Kernel/CoreDefs.lean` since task #305 (prep) and are
re-exported here, so that a relational description of the core's
moves can name them without importing the bodies.
-/

namespace ConLeche

/-- **The verdict of a failure, everywhere in the binary** — the one
error type the whole accept path reports (task #295): the kernel's
steps, the fold, and the frontend's parse and prelude alike.  The
three cases are the three verdicts the driver exits with
(`CheckError.exitCode`, `ConLeche/Driver/Run.lean`): 2 declined, 1 rejected, 3 an
error of unclear cause or a malformed input.

Where a failure has a POSITION the type is `CheckError × Nat`, and the
`Nat` is read in the step's own unit: the input's LINE number in the
frontend (`ConLeche/Frontend/Export.lean`; 0 where no line is meant,
as in the size guard, which refuses the input before reading it) and
the record's position in the list the fold folds
(`ConLeche.Cached.checkDecls`).  The two are in the same type because
the driver chains the steps, and the main corollary states that chain
(`ConLeche/MainTheorem.lean`). -/
inductive CheckError where
  | notImplemented (what : String)
  | invalid (msg : String)
  | internal (msg : String)
  deriving Repr

instance : ToString CheckError where
  toString
    | .notImplemented what => s!"not implemented yet: {what}"
    | .invalid msg => s!"invalid: {msg}"
    | .internal msg => s!"internal error: {msg}"

abbrev CheckM := Except CheckError

/-- **The verdict at a constant the environment does not know.**

`sorryAx` is the one axiom the checker tolerates as a *declaration*
and installs nothing for (`sorryAxName`,
`ConLeche/Kernel/Basis/Names.lean`): an export declares it whenever
its module mentions `sorry`, so the record is skipped and the stream
goes on — but there is no set model for it, so a *use* is a
positively detected unsupported feature and the run DECLINES, at the
record that uses it.  Every other unresolved name is a malformed
stream: a REJECT, with the message unchanged.

This decides the question wherever inference meets the constant
first.  Its companion `unresolvedConstsError`
(`ConLeche/Kernel/CheckerBase.lean`) decides the same question at the
guard that keeps unresolved constants out of stored terms
(`Expr.constsResolve`). -/
def unknownConstError (n : Name) : CheckError :=
  if n = sorryAxName then .notImplemented "use of the sorryAx axiom"
  else .invalid s!"unknown constant {n}"

/-- **Could official's `infer_proj` type `.proj sn i _` at a subject
of type `T a⃗` where we store no projection table for `T`?**  Only at a
single-constructor inductive `T` named by the node, applied to MORE
arguments than its parameters (official's premise is `#ctors = 1` and
`#args = nparams + nindices`, so indices are allowed), at a field index
below the constructor's field count: an INDEXED structure-like type,
where official projects and we store no table (the installer stores
one at every index-free single-constructor member and only there,
`checkBlockTables`).  Every other shape official rejects
(`invalid_proj_exception`): a head that is no inductive (an axiom, an
opaque, `Quot`), a constructor count other than one, a node naming
another type, a field index beyond the fields (`PUnit`, `Eq`: no
fields; an index-free one-constructor type always has a table). -/
def projIndexedStructLike (find? : Name → Option ConstantInfo) (T sn : Name)
    (i nArgs : Nat) : Bool :=
  T == sn &&
    match find? T with
    | some (.indInfo _ caps) =>
      match caps.ctors with
      | [c] =>
        caps.nparams < nArgs &&
          match find? c with
          | some (.ctorInfo _ _ nF) => decide (i < nF)
          | _ => false
      | _ => false
    | _ => false

/-- **The verdict at a `.proj sn i _` whose subject type is headed by
the constant `T` (applied to `nArgs` arguments) and has no
projection-table entry at field `i`** (`hasTable`: whether `T` has a
table at all).  A table without field `i` is an out-of-range index; a
positively detected indexed structure-like type (`projIndexedStructLike`)
is the one shape official accepts and we do not support (DECLINE, on
purpose: https://github.com/leanprover/lean4/issues/14977 removes
projections from indexed inductives); everything else rejects. -/
def projMissError (find? : Name → Option ConstantInfo) (hasTable : Bool)
    (T sn : Name) (i nArgs : Nat) : CheckError :=
  if hasTable then .invalid "projection index out of range"
  else if projIndexedStructLike find? T sn i nArgs then
    .notImplemented "projection on an indexed structure-like type"
  else .invalid "invalid projection: not a structure-like type, or no such field"

/-- The record of mutually recursive core entry points.  `whnfCore`
computes a head normal form without delta — its first argument is the
official kernel's `cheap_proj` flag (`whnfCoreBody`); `whnf` is the full reduction
loop; `infer` is type inference;
`defeq` is definitional equality; `inferIO` is inference at the
infer-only grade. -/
structure CoreFns (m : Type → Type u) where
  whnfCore : Bool → Nat → Expr → m Expr
  whnf : Nat → Expr → m Expr
  infer : Nat → Expr → m Expr
  defeq : Nat → Expr → Expr → m Bool
  /-- Definitional equality in the **eager tower** (task #353): the
  official kernel's `is_def_eq` with `m_eager_reduce` set, which
  `infer_app` sets for the comparison of an `eagerReduce _ _`
  argument's type with its domain (`defeqArg`).  The knot ties it to
  the bodies at `mode.toEager` one level down, so the flag holds for
  the whole comparison and everything it calls, as official's
  `flet` scope does. -/
  defeqE : Nat → Expr → Expr → m Bool
  /-- Type inference at the **infer-only grade** (task #170): the
  official kernel's `infer_type_core(e, infer_only = true)`, the entry
  every *internal* inference call site uses: the io body
  (`inferBodyIO`), which checks no application argument and no λ
  domain (task #346: its claim is hereditary on the type's syntax). -/
  inferIO : Nat → Expr → m Expr

/-- The **io-grade view** of a core record: the record whose full-grade
`infer` slot is the io slot, so that a body written against `r.infer`
recurses at the io grade when handed `r.ioView`.  This is how the io
inference body propagates its own grade (official: `infer_type_core`
passes `infer_only` down) without a textual twin. -/
def CoreFns.ioView {m : Type → Type u} (r : CoreFns m) : CoreFns m :=
  { r with infer := r.inferIO }

section Bodies

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/- The mode setting (`CheckMode`, `ConLeche/Kernel/Env.lean`):
definitions below that mention `mode` take it as their first explicit
argument (after the monad instances). -/
variable (mode : CheckMode)

/-- Lift a fuel-style partial result.  Its only client is the level
comparison (`Level.leq`/`isEquiv`), whose `none` is its fuel running out
(`Level.defaultFuel`) — OUR resource limit, so a DECLINE (exit 2), never
a verdict (charter item 9).  Every check that REQUIRES a comparison between two
levels neither of which is `zero` goes through here, so an exhausted
comparison cannot read as "not equivalent".  (A comparison against
`zero` cannot misread: `simplify` sends every always-zero level to
`zero`, and `isEquiv` answers `true` on that fast path, so its `none`
only ever stands for a true "no".) -/
def liftFueled (what : String) : Option α → m α
  | some a => pure a
  | none => throw (.notImplemented s!"resource limit: fuel exhausted: {what}")

/-- Literal acceleration (the official kernel's `reduceNat`, run in the
`whnf` loop *before* delta-unfolding): pack `Nat.succ` applied to a
literal back into a literal.  Binary operations on literal arguments
are added with the verified fast-path capabilities (see DESIGN.md);
until then only the constructor packing reduces. -/
def reduceNat (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    m (Option Expr) := do
  match e with
  | .app (.const c []) a =>
    if c = natSuccName ∧ natLitSupported env then
      -- the argument is reduced first (as for the operations below):
      -- literals reach `succ` wrapped in `OfNat`/instance towers, and a
      -- missed packing here defeats the binary fast paths downstream,
      -- which then delta-grind the `brecOn` below-tower unarily
      match rawNatLit? (← r.whnf depth a) with
      | some n => pure (some (.lit (.natVal (n + 1))))
      | none => pure none
    -- (the audit's S1: the `Nat.pred` and `Nat.log2` literal fast paths
    -- are gone — official `reduce_nat` (`type_checker.cpp:639-668`) has
    -- `Nat.succ` and the fourteen binary operations, nothing else.
    -- `Nat.pred` stays a certified structural operation because
    -- `Nat.sub`'s recurrence names it; `Nat.log2` is gone entirely)
    else pure none
  | .app (.app (.const c []) a) b =>
    if (c = natAddName ∨ c = natSubName ∨ c = natMulName ∨
        c = natPowName ∨ c = natBeqName ∨ c = natBleName ∨
        c = natDivName ∨ c = natModName ∨ c = natGcdName ∨
        c = natLandName ∨ c = natLorName ∨ c = natXorName ∨
        c = natShiftLeftName ∨ c = natShiftRightName) ∧
        natOpStored env c = true then
      -- Official `reduce_bin_nat_op` (`type_checker.cpp:606-614`):
      -- the FIRST argument is head-normalised and, unless it is a
      -- literal, the step fails WITHOUT touching the second.  The
      -- former two-scrutinee `match` whnf'd both up front — a cost
      -- divergence (DESIGN.md "THE DIVERGENCE AUDIT", D15): on
      -- `Nat.add o (slow n)` with `o` opaque it evaluated `slow n`
      -- where official never does (fuel death at `n = 80000`; the fixture).
      match rawNatLit? (← r.whnf depth a) with
      | some n₁ =>
        match rawNatLit? (← r.whnf depth b) with
        | some n₂ => pure (natOpResult c n₁ n₂)
        | none => pure none
      | none => pure none
    else if natOpWfNames.contains c ∧ natLitSupported env then
      match rawNatLit? (← r.whnf depth a) with
      | some _ =>
        match rawNatLit? (← r.whnf depth b) with
        | some _ => throw (.notImplemented
            s!"native Nat computation on literals ({c})")
        | none => pure none
      | none => pure none
    else pure none
  | _ => pure none


/-- **The full-grade telescope certificate** (task #342 L10, ι's case
3): every argument is inferred at the FULL grade, which establishes
its invariant, and its type is compared with its domain; no slot is
skipped.  The constructor spine of a case-3 redex is not a subterm of
the redex: at a valuation where the family is `Prop` the reduced major
is the point, its reduction says nothing, and only this run grades
its fields and puts them in their domains. -/
def iotaCertsFull (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → List Expr → m Bool
  | _, [] => pure true
  | .forallE ty body, arg :: rest => do
    let ta ← r.infer depth arg
    if ← r.defeq depth ta ty then
      iotaCertsFull r env depth (body.instantiate1 arg) rest
    else pure false
  | _, _ :: _ => pure false

/-- Pairwise definitional equality of two spines (used to check a
major's constructor parameters against the recursor's). -/
def defEqList (r : CoreFns m) (env : Env) (depth : Nat) :
    List Expr → List Expr → m Bool
  | [], [] => pure true
  | a :: as, b :: bs => do
    if ← r.defeq depth a b then
      defEqList r env depth as bs
    else pure false
  | _, _ => pure false

/-- The canonical-index comparison of a firing ι redex (the ι batch,
2026-09-05).  Where the recursor has indices (`rP < mI`) the residual of
the constructor's telescope `tyCtor` along the major's spine `margs`
must agree, past the `cnP` parameters, with the recursor's index
arguments `idx` — the model's iota equation only speaks about the
canonical indices.  At `mI = rP` there is nothing to compare (the law's
`IotaIndexPin` is discharged by `Or.inl rfl`) and the block is
skipped.  The residual-head test that once stood beside the comparison
(`stripPis` + "the body's head is a constant") was consumed by nothing
in the P lane and is gone. -/
def iotaIndexOk (r : CoreFns m) (env : Env) (depth : Nat) (mI rP cnP : Nat)
    (tyCtor : Expr) (margs idx : List Expr) : m Bool :=
  if mI = rP then pure true
  else
    match piResidual tyCtor margs with
    | some residual => defEqList r env depth (residual.getAppArgs.drop cnP) idx
    | none => pure false

/-- Proof irrelevance certification: both sides' types' *sorts* are
`Prop`.  In the model everything inhabiting a proposition is the proof
point, so any two such terms are equal — no common-type check is needed: soundness holds
without it, and the check-first discipline (every subterm is
checked before definitional equality compares it; congruence compares
argument pairs only after the earlier arguments matched) makes a
heterogeneous comparison unreachable, so the official kernel's check is
implied (see DESIGN.md, design-review triage). -/
def proofIrrel (r : CoreFns m) (depth : Nat) (a b : Expr) :
    m Bool := do
  -- task #172 B4: every inference here is at the io grade (official's
  -- is_def_eq_proof_irrel runs infer_type — always infer_only)
  let ta ← r.inferIO depth a
  match ← r.whnf depth (← r.inferIO depth ta) with
  | .sort uT =>
    let okA ← liftFueled "level comparison" (Level.isEquiv uT .zero)
    let tb ← r.inferIO depth b
    match ← r.whnf depth (← r.inferIO depth tb) with
    | .sort vT =>
      let okB ← liftFueled "level comparison" (Level.isEquiv vT .zero)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/-- **The hoisted proof-irrelevance test** (task #168, Option U):
`proofIrrel` behind the head-symbol fast arms — official's
`is_def_eq_proof_irrel`; the unit-like test is `stuckIrrel`'s
`structUnitCert` (official's `is_def_eq_unit_like`, the last test of
`is_def_eq_core`).

Before the io inferences, the head-symbol readers decide both fast
arms, **in both modes** (user ruling, 2026-09-06: the fast readers are
part of the real checker, and the trusted mode is the real checker
with certification-only work omitted — a reader that replaces
inference is not certification-only work).  The **"not a proof" arm**:
a side whose head-symbol datum says "not a proposition" refuses the
shortcut outright (`notProofFast`, `ConLeche/Kernel/PropRead.lean`).
Refusing is always sound — the P row is stated at `.ok true` — and the
arm's obligation is *agreement* with the slow path, recorded by the
landing census (DESIGN.md, task #168: 0 disagreements in 7.5 M calls).
The **"yes" arm** (`isProofFast` on both sides → `true`) is
justified by the squash regime, stage 3 of the same design
(`prf_of_isProofFast`, `ConLeche/Model/Rules/ProofFastSound.lean`), which the
verified mode's `DefEq.proofFast` rule consumes; the trusted mode is unverified and
inherits the arm without a row, as it inherits every other body. -/
def propIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  if notProofFast env.find? env.findTable? a || notProofFast env.find? env.findTable? b then
    pure false
  else if isProofFast env.find? env.findTable? a && isProofFast env.find? env.findTable? b then
    -- the yes arm (task #168 stage 3): both heads' data say
    -- "a proposition at every valuation" — justified by the squash
    -- regime (`prf_of_isProofFast`, `ConLeche/Model/Rules/ProofFastSound.lean`)
    pure true
  else
  -- task #172 B4: every inference here is at the io grade
  let ta ← r.inferIO depth a
  match ← r.whnf depth (← r.inferIO depth ta) with
  | .sort uT =>
    let okA ← liftFueled "level comparison" (Level.isEquiv uT .zero)
    let tb ← r.inferIO depth b
    match ← r.whnf depth (← r.inferIO depth tb) with
    | .sort vT =>
      let okB ← liftFueled "level comparison" (Level.isEquiv vT .zero)
      pure (okA && okB)
    | _ => pure false
  | _ => pure false

/-- The structure-eta certificate against the weak-head-normal type
`wtb` of the stuck side `b` (`structEtaCert` below reduces it). -/
def structEtaCertWith (r : CoreFns m) (env : Env) (depth : Nat)
    (a b wtb : Expr) : m Bool := do
  match a.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.ctorInfo cvc cnP cnF) =>
      if a.getAppArgs.length = cnP + cnF then
        match wtb.getAppFn with
        | .const T us' =>
          match env.find? T with
          | some (.indInfo cvT caps) =>
            if caps.eta = true ∧ caps.etaCtor = c ∧
                reservedBasisNames.contains T = false ∧
                reservedBasisNames.contains c = false ∧
                wtb.getAppArgs.length = caps.etaParams ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                -- the former's telescope arity
                -- `(cvT.type.stripPis caps.etaParams).isSome` is
                -- `EnvWF`'s `IndCapsWF` clause: established at the
                -- block's install, read by the η row from the
                -- invariant
                -- the slot discipline: every field slot has a
                -- projection-table entry (a fieldless family trivially)
                towerSlotsAll env T caps.etaFields = true then
              if ← liftFueled "level comparison"
                  (Level.isEquivList us us') then
                -- no certificate on the type application: `wtb` is the
                -- reduced type of `b`, a type, so its spine fits the
                -- former's telescope (task #342 L11b)
                if ← defEqList r env depth
                    (a.getAppArgs.take caps.etaParams) wtb.getAppArgs then
                  defEqList r env depth
                    (a.getAppArgs.drop caps.etaParams)
                    (etaProjs T b caps.etaFields)
                else pure false
              else pure false
            else pure false
          | _ => pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Structural eta certification for a stored eta-capable structure:
`a` is a fully applied constructor of a structure whose recorded
capabilities include eta, `b` inhabits that structure type, the
constructor's parameters are the type's arguments, and every field is
the corresponding projection (`.proj T j b`) of `b`.  The
parameter and field counts the certificate works at are the
capability RECORD's, which is what the stored law speaks; the
constructor's own counts gate the redex's shape and nothing else
(`etaCtorShape`). -/
def structEtaCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  -- The constructor-shape test FIRST (the divergence audit's D13):
  -- official `try_eta_struct_core` (`type_checker.cpp:824-829`) reads
  -- `s`'s head and arity syntactically and infers nothing unless they
  -- fit; ours inferred and whnf'd `b`'s type on every stuck pair, both
  -- directions, before `structEtaCertWith` looked at `a`'s head.
  if etaCtorShape env a then
    -- task #172 B4: io grade
    let tb ← r.inferIO depth b
    let wtb ← r.whnf depth tb
    structEtaCertWith r env depth a b wtb
  else pure false

/-- Unit-likeness certification: `a` and `b` inhabit the same stored
unit-like family (the types are definitionally equal and the type
application is certified against the family's telescope), so their
values coincide by the stored unit law. -/
def structUnitCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  -- task #172 B4: io grade
  let ta ← r.inferIO depth a
  let wta ← r.whnf depth ta
  match wta.getAppFn with
  | .const T us' =>
    match env.find? T with
    | some (.indInfo cvT caps) =>
      if caps.unitlike = true ∧
          reservedBasisNames.contains T = false ∧
          wta.getAppArgs.length = caps.unitParams ∧
          -- `(cvT.type.stripPis caps.unitParams).isSome` is `EnvWF`'s
          -- `IndCapsWF` clause, established at the block's install
          us'.length = cvT.levelParams.length then
        let tb ← r.inferIO depth b
        let wtb ← r.whnf depth tb
        -- no certificate on the type application (task #342 L11b); a ∀
        -- is never a family's application (task #342 L18: `b`'s io
        -- claim is then a membership)
        if wtb.isForallE then pure false else
        r.defeq depth wta wtb
      else pure false
    | _ => pure false
  | _ => pure false

/-- Eta certification for a one-sided λ against a stuck term `b`: `b`'s
type whnfs to a `∀` whose domain is defeq to the λ's, and the λ's body
is pointwise the application of `b`.  The λ is then `b`'s eta-expansion
(soundness: `SetTheory.lam_eta`). -/
def etaCert (mode : CheckMode) (r : CoreFns m) (_env : Env) (depth : Nat)
    (ty₁ body₁ : Expr) (b : Expr) :
    m Bool := do
  -- `b`'s head is no λ and no `let` (task #342 L18: its io claim is then
  -- a membership; `b` is in weak-head normal form and not a λ here)
  if !b.ioNeutral then pure false else
  -- task #172 B4: io grade
  let tb ← r.inferIO depth b
  match ← r.whnf depth tb with
  | .forallE ty₂ cod₂ =>
    if ← r.defeq depth ty₂ ty₁ then
      unless ← r.defeq (depth + 1)
          (body₁.instantiate1 (.fvar depth ty₁))
          (.app b (.fvar depth ty₁)) do return false
      -- Task #342 S0: the λ/η tax (T2)
      if mode.verifiedChecks then
        unless ← r.defeq (depth + 1)
            (← r.infer (depth + 1)
              (body₁.instantiate1 (.fvar depth ty₁)))
            (cod₂.instantiate1 (.fvar depth ty₁)) do return false
      pure true
    else pure false
  | _ => pure false

/-- The fallback for structurally distinct stuck terms: structural eta
in either direction, unit-likeness, else proof irrelevance. -/
def stuckIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  if ← structEtaCert r env depth a b then pure true
  else if ← structEtaCert r env depth b a then pure true
  else if ← structUnitCert r env depth a b then pure true
  else proofIrrel r depth a b

/-- Stuck-major rescue (`to_cnstr_when_K` and `to_cnstr_when_structure`
in the official kernel): a recursor's major premise that does not whnf
to a constructor application may still be *replaced* by one.  For a
K-flagged inductive proposition the parameters-only application of the
single constructor is fabricated from the major's type; its io type is
compared with the major's (official's check, unconditional) and, at the
verified mode, proof irrelevance compares it with the major (in the
model both are the proof point) — a certificate family, off at the
trusted mode (`mode.verifiedChecks`), as its cached twin gates it
through `certAtI` (`ConLeche/Cached/CoreC.lean`).
For an eta-capable structure the constructor applied to the major's
projections is fabricated with no check: the major is that application
by the family's η law (in the model both are the tuple of the major's
components).  For `And` — a proposition, which official never
η-rescues — the constructor applied to the major's projections is
fabricated and checked as in the K branch (the `And` branch below),
proof irrelevance likewise off at the trusted mode.  A
major that fails a check stays put — sound, the reduction simply stays
stuck. -/
def majorToCtor (r : CoreFns m) (env : Env) (depth : Nat)
    (_recName : Name) (rules : List RecRule) (major : Expr) : m Expr := do
  -- cheap syntactic gates before any inference: a rescue needs a
  -- single-rule recursor whose rule carries the matching install-time
  -- rescue bit (`RecRule.k`/`RecRule.eta`)
  if isCtorApp env major then pure major else
  match rules with
  | [rl] =>
    match env.find? rl.ctor with
    | some (.ctorInfo cvj cnP _cnF) =>
      match (cvj.type.piResult).getAppFn with
      | .const T _ =>
        match env.find? T with
        | some (.indInfo cvT caps) =>
          if rl.k = true then
            -- task #172 B4: io grade (lean4lean toCtorWhenK inferType)
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              if T' = T ∧ cvj.levelParams.length = ust.length then
                -- no constructor-telescope arity pin: the model proof
                -- consumes no such fact
                if cnP ≤ tmaj.getAppArgs.length then
                  let fab := Expr.mkAppN (.const rl.ctor ust)
                    (tmaj.getAppArgs.take cnP)
                  -- scope guard: scoping of
                  -- the fabricated major is checked syntactically,
                  -- keeping its verification local
                  if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    -- The official `to_cnstr_when_K` type check on the
                    -- fabrication: the constructor application's type
                    -- must be defeq to the major's (for `Eq` this is
                    -- the endpoint condition — `Eq.refl a : Eq a a`
                    -- against the major's `Eq a b` forces `a ≡ b`;
                    -- arena bad/098_ruleKbad fires at `Eq.rec.{3,3}`
                    -- without it).  `proofIrrel` makes the major a
                    -- proof (in the model both sides are the point).
                    if ← r.defeq depth tmaj (← r.inferIO depth fab) then
                      -- Task #342 (r1): the K check's proof-irrelevance half
                      -- is a certificate family (official stops at the type
                      -- check above) — gated off at the trusted mode, as
                      -- `certAtI mode (proofIrrelI ...)` gates its cached twin
                      -- (`ConLeche/Cached/CoreC.lean`).
                      if ← (if mode.verifiedChecks then proofIrrel r depth fab major
                          else pure true) then
                        pure fab
                      else pure major
                    else pure major
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if rl.eta = true then
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              -- The official kernel does not eta-rescue propositional
              -- structures (`to_cnstr_when_structure` requires the
              -- structure's result sort to be provably nonzero).  The
              -- test is the *instantiated* one (task #61): a static
              -- test of the declared type's result sort passes a
              -- parametric `Sort u` that a `Prop` instantiation
              -- collapses, which is exactly the case the guard exists
              -- for.
              -- the last three conjuncts are the keys of the η law:
              -- neither the family nor its constructor a reserved basis
              -- name, every field slot a projection-table entry
              if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length ∧
                  capsNeverZero cvT.levelParams ust caps = true ∧
                  reservedBasisNames.contains T = false ∧
                  reservedBasisNames.contains caps.etaCtor = false ∧
                  towerSlotsAll env T caps.etaFields = true then
                -- no constructor-telescope arity pin, as in the K
                -- branch, and no level-count pin: the η bit is set
                -- only at a constructor stored with the former's own
                -- level parameters (`RecCtorsStored`), which the
                -- fabrication's levels are those of
                let fab := Expr.mkAppN (.const caps.etaCtor ust)
                    (etaFabArgsE T tmaj.getAppArgs major caps.etaFields)
                -- scope guard, as in the K branch.  No certificate on
                -- the fabricated spine: the major is the fabrication by
                -- the family's η law, and the fabrication fits the η
                -- constructor's telescope by the coherence law (task
                -- #342 L11b).
                if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                    fab.fvarLeaves.all
                      (fun l => major.fvarLeaves.contains l) then
                  pure fab
                else pure major
              else pure major
            | _ => pure major
          else if T = andName then
            -- THE `And`-ONLY η RESCUE (user ruling: `And` and nothing
            -- else — "this is a hack and we want its blast radius
            -- limited").  `And.rec F h` at a stuck PROOF `h` (a theorem
            -- is opaque to reduction) fires through the fabrication
            -- `And.intro a b (.proj And 0 h) (.proj And 1 h)`,
            -- certified the K branch's way: the fabrication's type
            -- against the major's, and proof irrelevance — sound
            -- because in the model every proof is the point.  Official does not η-rescue a proposition
            -- (`to_cnstr_when_structure` requires a never-zero sort),
            -- so this is an accept-superset there, reported per the
            -- `proofIrrel` ruling; it WORKS AROUND the absence of
            -- https://github.com/leanprover/lean4/pull/14925 (upstream
            -- builds `casesOn`/`recOn` of such a proposition from
            -- projections, so no `And.rec` on a proof is emitted), on
            -- top of opaque theorems, which ANTICIPATE
            -- https://github.com/leanprover/lean4/pull/14896.
            let tmaj ← r.whnf depth (← r.inferIO depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              if T' = T ∧ tmaj.getAppArgs.length = cnP ∧
                  cvj.levelParams.length = ust.length ∧
                  andRescueSlots env rl.ctor cnP ust = true then
                let fab := Expr.mkAppN (.const rl.ctor ust)
                  (tmaj.getAppArgs ++ [.proj T 0 major, .proj T 1 major])
                -- scope guard, as in the K branch
                if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                    fab.fvarLeaves.all
                      (fun l => major.fvarLeaves.contains l) then
                  -- the fabrication's type against the major's, then
                  -- proof irrelevance, as in the K branch
                  if ← r.defeq depth tmaj (← r.inferIO depth fab) then
                    -- Task #342 (r1): proof irrelevance here, as in the K
                    -- branch, is a certificate family — gated off at the
                    -- trusted mode (`certAtI mode (proofIrrelI ...)` in the
                    -- cached twin).
                    if ← (if mode.verifiedChecks then proofIrrel r depth fab major
                        else pure true) then
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

/-- Convert a literal major premise to constructor form: a `Nat`
literal one layer (`litToCtorIfNat`); a `String` literal to its
*reduced* constructor form — the reference kernels re-reduce after
`strLitToConstructor` (lean4lean `Inductive/Reduce.lean`, nanoda
`str_lit_to_ctor_reducing`) since `String.ofList` is a definition, not
a constructor.  An unsupported literal passes through (stuck; sound,
and unreachable for input inference accepted, which declines it). -/
def litMajorToCtor (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → m Expr
  | .lit (.strVal s) =>
    if strLitSupported env then r.whnf depth (strLitToConstructor s)
    else pure (.lit (.strVal s))
  | e => pure (litToCtorIfNat env e)

/-- Convert a string-literal projection scrutinee to its *reduced*
constructor form — the references' proj expansion site (official
`reduce_proj_core`, `type_checker.cpp:383-384`; lean4lean
`TypeChecker.lean` proj clause; nanoda `tc.rs` `reduce_proj`): the
expansion's head `String.ofList` is a definition, so the whnf grinds it
to the real `String.ofByteArray` constructor form.  Only `String`
literals — no reference touches other scrutinees here.  An unsupported
literal passes through (stuck; sound, and unreachable for input
inference accepted, which declines it). -/
def projLitToCtor (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → m Expr
  | .lit (.strVal s) =>
    if strLitSupported env then r.whnf depth (strLitToConstructor s)
    else pure (.lit (.strVal s))
  | e => pure e

/-- Is `e` a `String` literal?  (The structure rescue leaves one to the
literal conversion, as lean4#15351's `to_cnstr_when_structure` does.) -/
def Expr.isStrLit : Expr → Bool
  | .lit (.strVal _) => true
  | _ => false

/-- The major premise's preparation before a rule fires.  Elsewhere
(the non-K case), the order of lean4#15351 (the kernel's
`inductive_reduce_rec` after Lean's kernel logic renovation,
lean4#14977): the structure rescues (`to_cnstr_when_structure`; here
also the `And` rescue) run on the major **as found**, before any head
normalization; only if they do not produce a constructor is the major
head-normalized, its literal converted, and the rescue tried once more
on the reduct.  A `String` literal skips the first attempt (lean4#15351
leaves it to the literal conversion).

Why the rescue comes first (task #342 R2, the arena's
`corner-cases/eta-struct-major-no-whnf` and
`eta-struct-major-and-no-whnf`): a structure major whose head
normalization does not terminate — `Prod.rec f loopPair`, `loopPair`
an `Acc.rec` over a proof built from Coquand's paradox; `And.rec f h`
for such a proof `h` — is rescued by reading only its *type*, and the
rule fires without the major ever being reduced.  Reducing first let
the proof's non-termination leak into the conversion of data.  The
rescues are `Red` steps on any major (`Red.rescueEta`,
`Red.rescueAnd`), so the order changes no claim; the reduct `minor
(S.p₀ x) … (S.pₖ x)` is convertible with the one plain ι gives after
the major reduces to `S.mk ps fs`.

At a K-flagged recursor the K rescue (`to_ctor_when_K`) runs on the
**raw** major — it reads only the major's *type* and fabricates the
constructor from it.  **Task #334 (maintainer ruling, 2026-10-09,
proposal P1 of the task #333 audit): if the rescue fails, the major is
left exactly as it is — no head normalization, no literal conversion.**
This deviates from the official kernel, which head-normalizes the
major unconditionally even after a failed K rescue
(`inductive_reduce_rec`'s `major = whnf(major)` runs regardless of
`to_cnstr_when_K`'s outcome).  The rescue reads only the major's
*type*: if `whnf` of a failed-rescue major ever produced `Eq.refl x`,
its type `x = x` would be definitionally equal to the recursor's
expected `a = b` by type preservation, so `a ≡ b` and the rescue would
already have succeeded.  The only loss is in incompleteness corners of
the checker's own defeq (a true `a ≡ b` that only a more complete
decision procedure — such as one that first normalizes the major —
would find); on mathlib-full the `whnf` after a failed K rescue ran
15 651 times (all `Eq.rec`) and reached a constructor 0 times (see the
TASK #333 record's audit). A K-like recursor application whose rescue
fails is now simply stuck, sound either way.

The rescues (K, structure-eta, `And`) live in one function
(`majorToCtor`); the K branch is reachable exactly at `recRuleK`, the
eta and `And` branches never are there (an inductive proposition fails
the eta branch's provably-nonzero guard, and `And` is not K), so the
split below dispatches each to its site.

Why the K order matters (2026-09-06, the Mathlib `decide`-over-`Rat`
frontier): with the whnf *first*, an `Eq.rec` whose major is a
theorem application — `Eq.ndrec … (Int.decEq._proof_1 a b h)` with
`h := Nat.eq_of_beq_eq_true …`, the shape `instDecidableEqRat`'s
`h ▸` produces — delta-unfolds the proofs and iota-grinds
`Nat.eq_of_beq_eq_true`'s `Nat.brecOn` tower unarily down the
`604800` literal: one knot level per `succ`, fuel exhaustion.  The
official order fabricates `Eq.refl` from the type (`a ≡ b` by the
`Nat` literal fast paths) and never opens either proof. -/
def prepareMajor (r : CoreFns m) (env : Env) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : Expr) : m Expr := do
  if recRuleK rules then
    let majorK ← majorToCtor mode r env depth recName rules major
    if isCtorApp env majorK then
      litMajorToCtor r env depth majorK
    else
      pure majorK
  else
    let majorE ← if major.isStrLit then pure major
      else majorToCtor mode r env depth recName rules major
    if isCtorApp env majorE then
      pure majorE
    else
      let major₀ ← r.whnf depth majorE
      let major₁ ← litMajorToCtor r env depth major₀
      majorToCtor mode r env depth recName rules major₁

/-- One iota step: the expression is a stored recursor applied to
exactly its telescope (params, motives, minors, indices, major), the
major premise whnfs to a fully applied constructor with a matching
rule (a literal major converts to constructor form — see
`litMajorToCtor` —, a
stuck major may be rescued — see `majorToCtor`), and the recursor's
stored type has the redex's arity.  The constructor side follows **the
ι case split** (task #342 L10, S5c), decided at the rule's comparand levels (`recFireComparands`):
a K rule, and a rule whose constructor's family is never `Prop` there
(`iotaCtorNeverProp`), fire with no check of the constructor application
— official's `inductive_reduce_rec` checks nothing of it either; every
other rule (case 3, `iotaCase3`) compares the constructor's levels and
parameters with the rule's comparands, certifies the constructor
telescope at the full grade (`iotaCertsFull`) and compares the indices
(`iotaIndexOk`).  The result is the rule's rhs applied to the non-index prefix and the
constructor's fields; over-application is handled by the outer app
recursion. -/
def iotaRec (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    m (Option Expr) := do
  match e.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.recInfo cv mI rP rules) =>
      let args := e.getAppArgs
      -- checker change #9: the recursor's level arity, guarded as
      -- `unfoldDefinition` guards it (`Core.lean:174`).  The official
      -- kernel tests this immediately before instantiating the rule's
      -- RHS (`src/kernel/inductive.h:105`, present since v4.0.0);
      -- lean4lean does the same (`Inductive/Reduce.lean:98`) and
      -- nanoda's `subst_expr_levels` asserts it.  Without it
      -- `rl.rhs.instantiateLevelParams cv.levelParams us` can leak a
      -- level parameter the subject never had.  Ungated: the reference has it
      -- unconditionally, so a mode gate would break parity.
      -- task #342 L18: the stored type's syntactic arity, which the
      -- uncertified recursor spine is read against
      if args.length = mI + 1 ∧ us.length = cv.levelParams.length ∧
          (Expr.peelPis (mI + 1) cv.type).isSome = true then
        -- the major's preparation (K rescue / whnf / literal / eta) in
        -- the official order — `prepareMajor`'s docstring
        let major ← prepareMajor mode r env depth c rules
          (args.getD mI (.bvar 0))
        match major.getAppFn with
        | .const cj usj =>
          match env.find? cj with
          | some (.ctorInfo cvj _ _) =>
            match rules.find? (fun r' => r'.ctor == cj) with
            | some rl =>
              let margs := major.getAppArgs
              -- the constructor's counts are read off the stored rule
              -- (install-computed); the defensive spine-length check
              -- stays
              if margs.length = rl.ctorParams + rl.nfields then
                -- The ι batch (2026-09-05): the two `stripPis` arity
                -- pins that stood here were an environment invariant
                -- re-checked per fire (every install route establishes
                -- them; the P lane bound and never used them) — deleted
                -- per the "invariants over runtime gates" ruling.
                --
                -- the rule's comparands (plain: the recursor's own level
                -- instantiation and leading arguments; nested: the stored
                -- major-domain instantiations), from the firing mode
                -- computed once at install (`sumRules` / `auxRuleFire`)
                let cmp := recFireComparands rl cv.levelParams us cvj.levelParams args rP
                -- **the ι case split** (task #342 L10, #349, S5c), decided at
                -- the comparand levels: a K rule, or a family never `Prop`
                -- there (`iotaCtorNeverProp`), fires with no check, as
                -- official's `inductive_reduce_rec` (it compares nothing
                -- of the major's constructor); case 3 compares the
                -- constructor's levels and parameters with the comparands,
                -- certifies the constructor telescope at the full grade and
                -- compares the indices (`iotaIndexOk`) — a certificate
                -- family (task #342 (r1)), off at the trusted mode as its
                -- cached twin gates the whole case-3 decision through
                -- `certAtI mode (do ...)` (`ConLeche/Cached/CoreC.lean`)
                if ← (if mode.verifiedChecks then
                    (if iotaCase3 env.find? rl cvj cmp.1 then do
                      if ← liftFueled "level comparison" (Level.isEquivList usj cmp.1) then
                        if ← defEqList r env depth (margs.take rl.ctorParams) cmp.2 then
                          if ← iotaCertsFull r env depth
                              (cvj.type.instantiateLevelParams cvj.levelParams usj)
                              margs then
                            iotaIndexOk r env depth mI rP rl.ctorParams
                              (cvj.type.instantiateLevelParams cvj.levelParams usj)
                              margs ((args.take mI).drop rP)
                          else pure false
                        else pure false
                      else pure false
                    else pure true)
                  else pure true) then
                  pure (some (Expr.mkAppN
                    (rl.rhs.instantiateLevelParams cv.levelParams us)
                    (args.take rP ++ margs.drop rl.ctorParams)))
                else pure none
              else pure none
            | none => pure none
          | _ => pure none
        | _ => pure none
      else pure none
    | _ => pure none
  | _ => pure none

/-- **The structural projection's check** (task #175 W6): the redex
`proj_i (C p⃗ x⃗)` fires only where `C`'s stored type has the spine's
arity.  The check is the constructor telescope's syntactic arity
(`teleArityOk`, task #342 L18): the spine is a subterm of the subject,
so where the redex is not the point it fits the telescope by the
application slots of its own invariant, and a reduction claims nothing
of a redex that is the point.  The official kernel's `reduce_proj`
checks nothing.  (Level instantiation keeps the arity, so the stored
type is read uninstantiated.) -/
def projCert (env : Env) (c : Name) (args : List Expr) : Bool :=
  match env.find? c with
  | some (.ctorInfo cvC _ _) => teleArityOk cvC.type args
  | _ => false

/-- **The fire check as the mode runs it** (parity mirrors official,
2026-09-06): the verified core checks the constructor telescope's
arity (`projCert`); the trusted core is the official kernel's, which
reduces every constructor redex with no check.  The trusted lane stays
an accept-superset of the verified lane, which is all the agreement
floor (`Verify/Cached/AgreeFloor.lean`) asks of it. -/
def projCertAt (env : Env) (verified : Bool) (c : Name) (args : List Expr) :
    Bool :=
  if verified then projCert env c args else true

/-- **The projection rule on a reduced scrutinee** (the official
kernel's `reduce_proj_core`): `proj_i (ctor p⃗ x⃗) ↦ x_i`, driven by the
projection table (never by basis names) — the table entry for
(structName, i) supplies the constructor, the counts and the
possibly-Prop level guard.  A string-literal scrutinee first expands to
its reduced constructor form (`projLitToCtor`, official: `whnf
(string_lit_to_constructor c)`).  At the verified mode the fire is
certified (`projCertAt`: the constructor spine against the
constructor's stored type, task #175 W6; official certifies nothing).
`none` when the rule does not fire.  Callers: `whnfCoreBody`'s `.proj`
clause and `lazyDeltaProjReduction`. -/
def reduceProjCore (r : CoreFns m) (env : Env) (depth : Nat) (sn : Name)
    (i : Nat) (c : Expr) : m (Option Expr) := do
  let c ← projLitToCtor r env depth c
  match env.findProj? sn i with
  | some entry =>
    match c.getAppFn with
    | .const k us =>
      let args := c.getAppArgs
      if k = entry.ctor ∧ i < entry.numFields ∧
          args.length = entry.numParams + entry.numFields ∧
          us.length = entry.levelParams.length ∧
          entry.fireOk us = true then
        -- the certificate runs unconditionally at the verified mode;
        -- the trusted mode runs none (`projCertAt`).
        if projCertAt env mode.verifiedChecks k args then
          pure (some (args.getD (entry.numParams + i) (.bvar 0)))
        else pure none
      else pure none
    | _ => pure none
  | none => pure none

/-- The head-normalization body: beta (with the per-redex argument
certificate, unconditional since the task-#100 de-gating), iota (with
the stuck-major machinery) and the native basis pair projection — but
**no delta**; unfolding happens in the `whnf` loop.  Values (sorts,
binders, constants, literals) return themselves.

`cheap` is the official kernel's `cheap_proj` (`whnf_core(e,
cheap_rec = false, cheap_proj)`): a projection's scrutinee is reduced
with `whnfCore` itself instead of `whnf`, and the flag propagates to
every recursive head normalization.  `whnf` runs the full mode;
definitional equality runs the cheap mode on its entry and after every
lazy-delta unfolding, so that `a.i =?= b.i` compares `a =?= b` before
reducing either scrutinee (`tests/e2e/src/proj_cheap_struct.lean`). -/
def whnfCoreBody (r : CoreFns m) (env : Env) : Bool → Nat → Expr → m Expr :=
  fun cheap depth e =>
    match e with
    | .sort u => pure (.sort u)
    | .fvar idx ty => pure (.fvar idx ty)
    | .forallE ty body => pure (.forallE ty body)
    | .lam ty body => pure (.lam ty body)
    | .const n us => pure (.const n us)
    | .lit l => pure (.lit l)
    | .app f a => do
      match ← r.whnfCore cheap depth f with
      | .lam _ body => do
        -- Task #342 S0: uniform β, no certificate
        r.whnfCore cheap depth (body.instantiate1 a)
      | f' => do
        match ← iotaRec mode r env depth (.app f' a) with
        | some e'' => r.whnfCore cheap depth e''
        | none => pure (.app f' a)
    | .proj sn i pe => do
      -- official `reduce_proj`: the scrutinee by `whnf`, or by the
      -- cheap `whnf_core` in the cheap mode; then `reduce_proj_core`.
      -- When it does not fire, the INPUT is returned — its scrutinee as
      -- it was, not the WHNF computed here (official `whnf_core`:
      -- `reduce_proj` fails, `r = e`).  The WHNF has lost the
      -- scrutinee's head constant, and with it the defeq check's
      -- arguments-first comparison of `a.i =?= b.i` (lane KEEPPROJ:
      -- exponential on the self-check's `nestRoot_datF._f`,
      -- `tests/e2e/src/proj_stuck_struct.lean`).
      let c ← if cheap then r.whnfCore true depth pe else r.whnf depth pe
      match ← reduceProjCore mode r env depth sn i c with
      | some m' => r.whnfCore cheap depth m'
      | none => pure (.proj sn i pe)
    | .letE _ v b =>
      -- Task #342 S0: ζ
      r.whnfCore cheap depth (b.instantiate1 v)
    | .bvar _ =>
      throw (.notImplemented "whnf beyond the supported fragment")

/-- Step budget of the `whnfCore` head-normalization loop (task #106).
Beta, iota and projection steps are *iteration*: the interned
`whnfCoreLoopI` runs them on this budget instead of charging each step
to the shared recursion-depth budget (and to the native stack).  The
`Expr`-level specification below stays chained — the refinement bridge
reproduces a loop run by the chained recursion *at some knot fuel*
(`ConLeche/Verify/BetaSpine.lean`), so the specification and everything
above it are unchanged.

Task #330: a real 104.7 GB export (a `decide +kernel` proof,
`CKLaneD.Structural.structural_paths._proof_1_1`) exhausted this budget
on master, an internal error (exit 3) on a legitimate input, never an
accept — raising it can't weaken the check, so the budget is now
effectively unbounded: `2^62`, the largest literal that still keeps the
decrementing counter an unboxed scalar (`2^63` is a bignum on a 64-bit
`Nat`/`LEAN_MAX_SMALL_NAT`).  A runaway input is left to an external
timeout.  See
<https://github.com/dpwoodru/general-courtade-kumar-lean/tree/main/verification/con-leche/results/2026-10-08>. -/
@[irreducible, noinline] def whnfCoreLoopFuel : Nat := 4611686018427387904  -- 2^62

/-- The outcome of one step of the cached head-normalization loop
(`whnfCoreStepI`, `ConLeche/Cached/CoreC.lean`) and of its pure mirror
(`ConLeche/Verify/BetaSpine.lean`): the head normal form, or the term
the loop continues with.  Task #342 R2: a step *returns* its
continuation instead of calling it, so every reduction step is the
loop's own tail call and a chain of any length — a non-terminating one
included — runs in constant native stack. -/
inductive WhnfStep where
  | done (e : Expr)
  | cont (e : Expr)

/-- Step budget of the `whnf` reduction loop (lean4lean's
`FuelConfig.whnf`, same value).  Literal-acceleration and delta steps
are *iteration*, not recursion: the official kernel's loop is a
`while (true)` and lean4lean's is a fixed-fuel local loop.  Task #106:
routing them through the knot instead charged every unfolding step to
the shared *recursion depth* budget (and to the native stack), so a
long-but-perfectly-ordinary unfolding chain exhausted `checkFuel`.

Task #330: effectively unbounded for the same reason as
`whnfCoreLoopFuel` above (the same real export exhausted this budget on
master before the fuel patch). -/
@[irreducible, noinline] def whnfLoopFuel : Nat := 4611686018427387904  -- 2^62

/-- One iteration of the reduction loop (the official kernel's `whnf`
body, lean4lean's `whnf'` loop body): head-normalize, try literal
acceleration, unfold one definition — and hand the reduct to the
loop's continuation `k`.  As everywhere in this module, the body never
calls itself: the continuation is abstracted exactly like the record
`r`, so every lemma about the body is proven once, with a hypothesis
about `k`, and the loop lemma is one induction on the budget. -/
def whnfStep (r : CoreFns m) (env : Env) (depth : Nat)
    (k : Expr → m Expr) (e : Expr) : m Expr := do
  let e₁ ← r.whnfCore false depth e
  match ← reduceNat r env depth e₁ with
  | some e₂ => k e₂
  | none =>
    match unfoldDefinition env e₁ with
    | some e₂ => k e₂
    | none => pure e₁

/-- The reduction loop: iterate `whnfStep` on its own step budget, so
the whole chain costs one knot level however many steps it takes. -/
def whnfLoop (r : CoreFns m) (env : Env) (depth : Nat) :
    Nat → Expr → m Expr
  | 0, _ => throw (.internal "fuel exhausted: whnf loop")
  | n + 1, e => whnfStep r env depth (whnfLoop r env depth n) e

/-- The reduction loop's body: run `whnfLoop` at its own step budget. -/
def whnfBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => whnfLoop r env depth whnfLoopFuel e

/-- Ensure `e` (the type of some expression) is a sort, returning its
level. -/
def ensureSort (r : CoreFns m) (_env : Env) (depth : Nat) (e : Expr) :
    m Level := do
  match ← r.whnf depth e with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-- **The argument check of a full-grade application** (task #353,
official `infer_app`): the type of an `eagerReduce _ _` argument
(`Expr.isEagerReduce`) is compared with the domain in the eager tower
(`CoreFns.defeqE`: the official kernel sets `m_eager_reduce` for this
one comparison), every other argument's in the knot's own. -/
def defeqArg (r : CoreFns m) (depth : Nat) (a ta ty : Expr) : m Bool :=
  if a.isEagerReduce then r.defeqE depth ta ty else r.defeq depth ta ty

/-- The inference body at the full grade — official's
`infer_type_core` with `infer_only = false`: every binder domain is
checked to be a type, every application argument against its domain,
and a `let`'s value against its type.  Speculative inference inside
reduction runs at the io grade instead (`inferBodyIO`). -/
def inferBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => do
    match e with
    | .sort u => pure (.sort (.succ u))
    | .fvar idx ty =>
      -- Scope check at the leaf of a traversal that happens anyway
      -- (O(1); never a fresh walk): a free variable must refer to an
      -- enclosing opened binder.  On raw (closed) input at depth 0 this
      -- rejects any `fvar` outright; internally the checker only opens
      -- variables below the ambient depth, so for disciplined calls the
      -- check always passes (and inference success implies
      -- well-scopedness, the base case of the cache discipline).
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | .const n us => do
      match env.find? n with
      | none => throw (unknownConstError n)
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        pure (cv.type.instantiateLevelParams cv.levelParams us)
    | .lit (.natVal _) => do
      if natLitSupported env then pure (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      -- a string literal types as `String` (the reference kernels'
      -- `Literal.typeName`); without the pinned support declarations
      -- this is a positively detected unsupported feature: decline
      if strLitSupported env then pure (.const stringName [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body => do
      -- The ∀-formation rule, official-kernel style (task #100 stage 6):
      -- the codomain sort is *inferred* from the opened body.
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort u => do
        let v ← ensureSort r env (depth + 1)
          (← r.infer (depth + 1) (body.instantiate1 (.fvar depth ty)))
        pure (.sort (.imax u v))
      | _ => throw (.invalid "expected a sort")
    | .lam ty body => do
      -- The domain must be a type (and the model needs its
      -- interpretation defined), exactly as in the ∀ rule.
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort _ => do
        let bt ← r.infer (depth + 1)
          (body.instantiate1 (.fvar depth ty))
        pure (.forallE ty (bt.abstract1 depth))
      | _ => throw (.invalid "expected a sort")
    | .app f a => do
      let tf ← r.infer depth f
      match ← r.whnf depth tf with
      | .forallE ty body => do
        -- Task #368: `U E C a` with a natively
        -- accepted certificate, typed `Unsat E` without inferring `a`
        -- (`Rules.Infer.bvUnsat`)
        if bvUnsatSkip env.find? env.findProj? f a body then pure (body.instantiate1 a) else
        -- The per-argument check, unconditional at this grade (the
        -- soundness proof needs `⟦a⟧ ∈ ⟦ty⟧`).
        let ta ← r.infer depth a
        unless ← defeqArg r depth a ta ty do
          throw (.invalid "application type mismatch")
        pure (body.instantiate1 a)
      | _ => throw (.invalid "function expected")
    | .proj sn i pe => do
      -- A `.proj` node is typed by its projection-table entry: the
      -- stored body, level-instantiated at the subject type's levels
      -- and instantiated at its arguments and the subject (task #175
      -- S1).  Only stored table entries type bare nodes (task #175
      -- W6: the pinned pair entries and their computed two-member
      -- fast path are retired; tower-flag: every stored table is a
      -- real one).
      let te ← r.whnf depth (← r.infer depth pe)
      match te.getAppFn with
      | .const T us =>
        match env.findProj? T i with
        | some entry =>
          -- task #175 wiring W5: the node's struct name must be the
          -- subject type's head (official `infer_proj`'s
          -- `const_name(I) == proj_sname(e)`); the readings key the
          -- table on the node's name, the checker on the head's
          if T = sn ∧ te.getAppArgs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            -- the official `infer_proj` restriction (task #175
            -- W4c/O4): at a `Prop`-declared structure the field —
            -- and every earlier field a later field uses — must be
            -- a proposition at this instantiation; the entry's
            -- guard level joins exactly those sorts
            if Level.isEquiv entry.structSort .zero == some true then
              unless Level.isEquiv
                  (Level.subst entry.levelParams us entry.fieldSort) .zero
                  == some true do
                throw (.invalid
                  "projection from a propositional structure must be a proposition")
            -- the body at the subject type's arguments and the
            -- subject, one `instantiateList` (task #175 S1)
            pure (entry.typeAt us te.getAppArgs pe)
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | .letE ty v b => do
      -- Task #342 S0: official `infer_let`
      let _ ← ensureSort r env depth (← r.infer depth ty)
      unless ← r.defeq depth (← r.infer depth v) ty do
        throw (.invalid "let value type mismatch")
      r.infer depth (b.instantiate1 v)
    | .bvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- **The io inference body** (tasks #161, #170, #346): official's
`infer_type_core` with `infer_only = true`.  It differs from
`inferBody` at three clauses: an application's argument is not
checked against the domain, a λ's domain is not checked to be a type,
and a `let`'s type and value are not checked (the body is inferred at
the value).  The computed types and the "function expected" rejection
are `inferBody`'s.  Recursion is through `r.infer`: the io knot ties
this body to an io-grade record (`CoreFns.ioView` at the knot's io
slot, or `coreKnotIO`'s leaf lane), which is how the grade propagates
— official's `infer_type_core(e, infer_only)` passing `infer_only` to
every recursive call.

Moved here from `ConLeche/Kernel/CoreIO.lean` (task #172 B4) so the knot
can tie the io slot. -/
def inferBodyIO (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => do
    match e with
    | .sort u => pure (.sort (.succ u))
    | .fvar idx ty =>
      if idx < depth then pure ty
      else throw (.invalid "free variable out of scope")
    | .const n us => do
      match env.find? n with
      | none => throw (unknownConstError n)
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        pure (cv.type.instantiateLevelParams cv.levelParams us)
    | .lit (.natVal _) => do
      if natLitSupported env then pure (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => do
      if strLitSupported env then pure (.const stringName [])
      else throw (.notImplemented
        "string literals before the String support declarations")
    | .forallE ty body => do
      match ← r.whnf depth (← r.infer depth ty) with
      | .sort u => do
        let v ← ensureSort r env (depth + 1)
          (← r.infer (depth + 1) (body.instantiate1 (.fvar depth ty)))
        pure (.sort (.imax u v))
      | _ => throw (.invalid "expected a sort")
    | .lam ty body => do
      -- Task #168: no domain-sort run at the io grade —
      -- official's `infer_lambda` skips it at `infer_only`
      -- (`type_checker.cpp:131`), and the model proof
      -- never consumes it: the domain's grading comes from the
      -- λ node's own `WellDenoted` premise.
      let bt ← r.infer (depth + 1)
        (body.instantiate1 (.fvar depth ty))
      pure (.forallE ty (bt.abstract1 depth))
    | .app f a => do
      let tf ← r.infer depth f
      match ← r.whnf depth tf with
      | .forallE _ body => do
        -- **THE io SITE** (task #346): official's `infer_only` — the
        -- argument is not checked against the domain; the io claim is
        -- hereditary on the type's syntax (`IORel`)
        pure (body.instantiate1 a)
      | _ => throw (.invalid "function expected")
    | .proj sn i pe => do
      let te ← r.whnf depth (← r.infer depth pe)
      match te.getAppFn with
      | .const T us =>
        match env.findProj? T i with
        | some entry =>
          -- task #175 wiring W5: the node's struct name must be the
          -- subject type's head (official `infer_proj`'s
          -- `const_name(I) == proj_sname(e)`); the readings key the
          -- table on the node's name, the checker on the head's
          if T = sn ∧ te.getAppArgs.length = entry.numParams ∧
              us.length = entry.levelParams.length then do
            -- the official `infer_proj` restriction (task #175
            -- W4c/O4), as in `inferBody`
            if Level.isEquiv entry.structSort .zero == some true then
              unless Level.isEquiv
                  (Level.subst entry.levelParams us entry.fieldSort) .zero
                  == some true do
                throw (.invalid
                  "projection from a propositional structure must be a proposition")
            -- the body at the arguments and the subject, as in
            -- `inferBody` (task #175 S1)
            pure (entry.typeAt us te.getAppArgs pe)
          else throw (.notImplemented "projection without a native entry")
        | none => throw (.notImplemented "projection without a native entry")
      | _ => throw (.notImplemented "projection without a native entry")
    | .letE _ v b =>
      -- official `infer_let` at `infer_only`: the body at its value,
      -- no check of the type or the value (task #342 R-C)
      r.infer depth (b.instantiate1 v)
    | .bvar _ =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- **The eq-true shortcut** (the divergence audit's E2): official
`is_def_eq_core`'s second clause (`type_checker.cpp:1093-1101`) — when
the right side is the constant `Bool.true` and the left side has no
free variables (or the eager flag is set, task #353), the left side is
fully head-normalised (`whnf`, the
cached loop) and the verdict is `true` iff the reduct is `Bool.true`; on
failure the comparison continues.  Only the reduction is here; the
guard is `defeqBody`'s.
Verdict-neutral against lazy delta (a `whnf` reduct is what the
unfolding loop reaches, one step at a time), one memoised `whnf`
instead of one loop iteration per unfolding. -/
def boolTrueShortcut (r : CoreFns m) (depth : Nat) (a : Expr) : m Bool := do
  let w ← r.whnf depth a
  pure w.isBoolTrue

/-- Levels-and-spine congruence for two applications of the same
stored constant — the lazy delta *same-head short-circuit* (the
official kernel's `try_eq_const_app`): before unfolding both sides of
`f as ≡ f bs`, try pairwise definitional equality of the levels and
the spine arguments.  A `false` verdict is never final — the caller
falls back to unfolding — so an inconclusive level comparison simply
answers `false` here.

The arguments are compared **last to first** (task #353), as official
`is_def_eq_args` walks `app_arg`/`app_fn` from the outermost
application inwards: on `Nat.add (M+1) 1 =?= Nat.add M 2` the literals
`1 =?= 2` fail at once and both sides unfold, where a first-to-first
walk decides `M+1 =?= M` by unary successor descent first
(`tests/e2e/src/spine_arg_order.lean`).  The stuck spine congruence
(`defeqStuck`, official `is_def_eq_app`) stays first to last, as
official's does. -/
def defeqSpine (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  match a.getAppFn with
  | .const n us =>
    match b.getAppFn with
    | .const n' us' =>
      if n = n' ∧ a.getAppArgs.length = b.getAppArgs.length then
        match Level.isEquivList us us' with
        | some true =>
          defEqList r env depth a.getAppArgs.reverse b.getAppArgs.reverse
        | _ => pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Descent budget of the λ-telescope comparison (`defeqLams`).
Exhaustion is not an error: the level reached is compared as the
innermost one, which is always sound. -/
@[irreducible, noinline] def lamsFuel : Nat := 4611686018427387904  -- 2^62

/-- The innermost level of `defeqLams`: the opened bodies, and at the
verified mode their FULL-grade types. -/
def defeqLamsInner (r : CoreFns m) (depth : Nat) (b₁ b₂ : Expr) : m Bool := do
  unless ← r.defeq (depth + 1) b₁ b₂ do return false
  if mode.verifiedChecks then
    unless ← r.defeq (depth + 1) (← r.infer (depth + 1) b₁)
        (← r.infer (depth + 1) b₂) do return false
  pure true

/-- **λ-telescope congruence** (task #342, #349; the rules tier's
`DefEqLams`): two λs compare their domains; while both opened bodies
are λs (and not syntactically equal) the comparison descends into them
directly, comparing domains only; at the innermost level the opened
bodies are compared and, at the verified mode, so are their FULL-grade
types (the λ check).  The descent is the λ arm's own, not a recursive
`defeq` call: a recursive call could answer two λs by proof
irrelevance or the memo, which skips the type comparison that the
outer levels rely on. -/
def defeqLams (r : CoreFns m) :
    Nat → Nat → Expr → Expr → Expr → Expr → m Bool
  | fuel, depth, ty₁, body₁, ty₂, body₂ => do
    unless ← r.defeq depth ty₁ ty₂ do return false
    let b₁ := body₁.instantiate1 (.fvar depth ty₂)
    let b₂ := body₂.instantiate1 (.fvar depth ty₂)
    match fuel, Expr.lamPair? b₁ b₂ with
    | fuel + 1, some (ty₁', body₁', ty₂', body₂') =>
      if b₁ == b₂ then pure true
      else defeqLams r fuel (depth + 1) ty₁' body₁' ty₂' body₂'
    | _, _ => defeqLamsInner mode r depth b₁ b₂

/-- **The easy cases** (the official kernel's `quick_is_def_eq`): the
syntactic fast path, and the pairs whose verdict is decided on the spot
— two sorts (level equivalence), two literals, two `∀`s and two `λ`s
(binder congruence: domains, then bodies opened at the RIGHT domain;
two λs by `defeqLams`).
`none` is "not an easy case".  `defeqBody` runs it on the unreduced
pair and again after the cheap head normalization, and
`lazyDeltaStep` after every unfolding.  (The
positive `is_def_eq` cache of official's version is the cached core's
`defeq` memo.) -/
def quickDefEq (r : CoreFns m) (depth : Nat) (a b : Expr) : m (Option Bool) :=
  if a == b then pure (some true) else
  match a, b with
  | .sort u, .sort v => do
    let ok ← liftFueled "level comparison" (Level.isEquiv u v)
    pure (some ok)
  | .lit l₁, .lit l₂ => pure (some (l₁ == l₂))
  | .forallE ty₁ body₁, .forallE ty₂ body₂ => do
    unless ← r.defeq depth ty₁ ty₂ do return some false
    unless ← r.defeq (depth + 1)
        (body₁.instantiate1 (.fvar depth ty₂))
        (body₂.instantiate1 (.fvar depth ty₂)) do return some false
    pure (some true)
  | .lam ty₁ body₁, .lam ty₂ body₂ => do
    let ok ← defeqLams mode r lamsFuel depth ty₁ body₁ ty₂ body₂
    pure (some ok)
  | _, _ => pure none

/-- `Nat.zero` or the literal `0` (official `is_nat_zero`). -/
def Expr.isNatZero : Expr → Bool
  | .lit (.natVal 0) => true
  | .const c [] => c == natZeroName
  | _ => false

/-- Is `e` a literal? -/
def Expr.isLit : Expr → Bool
  | .lit _ => true
  | _ => false

/-- The predecessor of a successor form (official `is_nat_succ`): a
nonzero literal, or `Nat.succ x`. -/
def Expr.natPred? : Expr → Option Expr
  | .lit (.natVal (n + 1)) => some (.lit (.natVal n))
  | .app (.const c []) x => if c = natSuccName then some x else none
  | _ => none

/-- **Offsets** (the official kernel's `is_def_eq_offset`, the first
check of each lazy-delta iteration): two zeros are equal, two
successor forms compare their predecessors.  Two literals never reach
it (`quickDefEq` decides them first), and are left out so that the
predecessor comparison only ever pairs a literal with a `Nat.succ`. -/
def defeqOffset (r : CoreFns m) (depth : Nat) (a b : Expr) : m (Option Bool) :=
  if a.isNatZero && b.isNatZero then pure (some true) else
  if a.isLit && b.isLit then pure none else
  match a.natPred?, b.natPred? with
  | some x, some y => do
    let ok ← r.defeq depth x y
    pure (some ok)
  | _, _ => pure none

/-- Is the head of the application spine a projection? -/
def Expr.headIsProj (e : Expr) : Bool :=
  match e.getAppFn with
  | .proj _ _ _ => true
  | _ => false

/-- Official `try_unfold_proj_app`: a term whose head is a projection
is put through the FULL `whnfCore` (the scrutinee reduced with
`whnf`); `some` whenever that changed it — also when only the
scrutinee moved and the projection did not fire. -/
def tryUnfoldProjApp (r : CoreFns m) (depth : Nat) (e : Expr) : m (Option Expr) :=
  if e.headIsProj then do
    let e' ← r.whnfCore false depth e
    if e' == e then pure none else pure (some e')
  else pure none

/-- The outcome of one lazy-delta step (official `reduction_status`):
continue with the reduced pair, or a verdict, or "neither side
unfolds". -/
inductive DeltaStep where
  | cont (a b : Expr)
  | eq
  | diff
  | unknown

/-- The end of a lazy-delta step: `quick_is_def_eq` on the new pair. -/
def deltaQuick (r : CoreFns m) (depth : Nat) (a b : Expr) : m DeltaStep := do
  match ← quickDefEq mode r depth a b with
  | some true => pure .eq
  | some false => pure .diff
  | none => pure (.cont a b)

/-- **One lazy-delta step** (the official kernel's
`lazy_delta_reduction_step`): read the two heads' unfoldability and
hints, unfold the side with the greater height (both at equal hints,
after the same-head argument shortcut at equal *regular* hints), put
the unfolded side through the cheap `whnfCore`, and finish with
`quickDefEq`.  With one side unfoldable, a projection application on
the other side is reduced instead (`tryUnfoldProjApp`): `expensive =?=
inst.1 a` must not unfold `expensive` lazily to the bottom.

The same-head shortcut's `sameRegular` guard mirrors the reference
kernels and is deliberate: at equal `abbrev` (or `opaque`) hints both
sides unfold eagerly instead (abbrevs are meant to unfold; a spine
attempt on abbrev-headed applications risks reduction bombs).  Do not
generalize it.  The `.unknown` exits under a successful
`unfoldableHead` are unreachable (`unfoldableHead env e` is
`(unfoldDefinition env e).isSome`). -/
def lazyDeltaStep (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m DeltaStep := do
  match unfoldableHead env a, unfoldableHead env b with
  | false, false => pure .unknown
  | true, false =>
    match ← tryUnfoldProjApp r depth b with
    | some b₂ => deltaQuick mode r depth a b₂
    | none =>
      match unfoldDefinition env a with
      | some a₂ => do
        let a₃ ← r.whnfCore true depth a₂
        deltaQuick mode r depth a₃ b
      | none => pure .unknown
  | false, true =>
    match ← tryUnfoldProjApp r depth a with
    | some a₂ => deltaQuick mode r depth a₂ b
    | none =>
      match unfoldDefinition env b with
      | some b₂ => do
        let b₃ ← r.whnfCore true depth b₂
        deltaQuick mode r depth a b₃
      | none => pure .unknown
  | true, true =>
    let ha := headHint env a
    let hb := headHint env b
    if ReducibilityHint.lt hb ha then
      match unfoldDefinition env a with
      | some a₂ => do
        let a₃ ← r.whnfCore true depth a₂
        deltaQuick mode r depth a₃ b
      | none => pure .unknown
    else if ReducibilityHint.lt ha hb then
      match unfoldDefinition env b with
      | some b₂ => do
        let b₃ ← r.whnfCore true depth b₂
        deltaQuick mode r depth a b₃
      | none => pure .unknown
    else if ← (if ReducibilityHint.sameRegular ha hb && sameConstHeads a b then
        defeqSpine r env depth a b else pure false) then pure .eq
    else
      match unfoldDefinition env a, unfoldDefinition env b with
      | some a₂, some b₂ => do
        let a₃ ← r.whnfCore true depth a₂
        let b₃ ← r.whnfCore true depth b₂
        deltaQuick mode r depth a₃ b₃
      | _, _ => pure .unknown

/-- The outcome of the lazy-delta loop: a verdict, or the pair it got
stuck on (official `lazy_delta_reduction` returns `l_undef` and updates
`t_n`, `s_n`). -/
inductive LazyRes where
  | verdict (v : Bool)
  | unknown (a b : Expr)

/-- Step budget of the two lazy-delta loops (lean4lean's
`FuelConfig.lazyDelta`, generously sized).  Exhaustion is an internal
error, never a verdict.

Task #330: effectively unbounded for the same reason as
`whnfCoreLoopFuel`/`whnfLoopFuel` above. -/
@[irreducible, noinline] def defeqLoopFuel : Nat := 4611686018427387904  -- 2^62

/-- **The lazy-delta loop** (the official kernel's
`lazy_delta_reduction`): per iteration the offset check, the literal
acceleration — guarded on both sides being free of free variables, as
in the official kernel and lean4lean (an open `Int32`/`Int64` pair
would otherwise delta-grind the `Nat.brecOn` tower; the whnf-loop
`reduceNat` stays unguarded, as the official whnf loop is), unless the
eager flag is set (`mode.eager`, task #353: official's
`(!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce`) — whose
reduct restarts the comparison (`defeq`, official `is_def_eq_core`),
then one `lazyDeltaStep`.  Each unfolding is one iteration of this
loop on its own step budget (task #106: not one unit of the knot's
recursion depth). -/
def lazyDeltaReduction (r : CoreFns m) (env : Env) (depth : Nat) :
    Nat → Expr → Expr → m LazyRes
  | 0, _, _ => throw (.internal "fuel exhausted: defeq loop")
  | n + 1, a, b => do
    match ← defeqOffset r depth a b with
    | some v => pure (.verdict v)
    | none =>
    match ← (if mode.eager || (!a.hasFvar && !b.hasFvar) then
        reduceNat r env depth a else pure none) with
    | some a₂ => do
      let v ← r.defeq depth a₂ b
      pure (.verdict v)
    | none =>
    match ← (if mode.eager || (!a.hasFvar && !b.hasFvar) then
        reduceNat r env depth b else pure none) with
    | some b₂ => do
      let v ← r.defeq depth a b₂
      pure (.verdict v)
    | none =>
    match ← lazyDeltaStep mode r env depth a b with
    | .cont a' b' => lazyDeltaReduction r env depth n a' b'
    | .eq => pure (.verdict true)
    | .diff => pure (.verdict false)
    | .unknown => pure (.unknown a b)

/-- **`a.i =?= b.i` by its scrutinees** (the official kernel's
`lazy_delta_proj_reduction`): lazy-delta steps on the two scrutinees;
when neither unfolds any more (or the step found them different), the
projection is tried on both (`reduceProjCore`) and only the projected
fields are compared; failing that, the scrutinees themselves. -/
def lazyDeltaProjReduction (r : CoreFns m) (env : Env) (depth : Nat)
    (sn : Name) (i : Nat) : Nat → Expr → Expr → m Bool
  | 0, _, _ => throw (.internal "fuel exhausted: lazy delta projection loop")
  | n + 1, a, b => do
    match ← lazyDeltaStep mode r env depth a b with
    | .cont a' b' => lazyDeltaProjReduction r env depth sn i n a' b'
    | .eq => pure true
    | .diff | .unknown =>
      match ← reduceProjCore mode r env depth sn i a with
      | some x =>
        match ← reduceProjCore mode r env depth sn i b with
        | some y => r.defeq depth x y
        | none => r.defeq depth a b
      | none => r.defeq depth a b

/-- The proj/proj check of `is_def_eq_core`: two projections at the
same slot go through `lazyDeltaProjReduction` on their scrutinees. -/
def defeqProjPair (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool :=
  match a, b with
  | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ =>
    if s₁ == s₂ && i₁ == i₂ then
      lazyDeltaProjReduction mode r env depth s₁ i₁ defeqLoopFuel e₁ e₂
    else pure false
  | _, _ => pure false

/-- **The stuck comparison** (the tail of the official kernel's
`is_def_eq_core`, after lazy delta, the proj/proj check and the full
`whnf_core` restart): the same constant at equivalent levels, the same
free variable, a string literal against `String.ofList`
(`try_string_lit_expansion`), the application spine
(`is_def_eq_app`), η on a one-sided λ; every failing arm ends in
`stuckIrrel` (proof irrelevance, structure η, unit-likeness).  Two
constants or two free variables are inert under `whnfCore`, so checking
them here, after the restart, instead of before it is the same
verdict. -/
def defeqStuck (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool :=
  match a, b with
  -- a string literal against a unary `String.ofList` application:
  -- expand the literal to its constructor form and compare — the
  -- reference kernels' `tryStringLitExpansion` (lean4lean
  -- `TypeChecker.lean`, nanoda `try_string_lit_expansion`), which
  -- fires exactly when the other side's function part is the bare
  -- `String.ofList` constant
  | .lit l, .app f x =>
    match l, f with
    | .strVal st, .const cO usO =>
      if cO = stringOfListName ∧ usO = [] ∧ strLitSupported env then
        r.defeq depth (strLitToConstructor st) (.app (.const cO usO) x)
      else stuckIrrel r env depth (.lit (.strVal st)) (.app (.const cO usO) x)
    | _, _ => stuckIrrel r env depth (.lit l) (.app f x)
  | .app f x, .lit l =>
    match l, f with
    | .strVal st, .const cO usO =>
      if cO = stringOfListName ∧ usO = [] ∧ strLitSupported env then
        r.defeq depth (.app (.const cO usO) x) (strLitToConstructor st)
      else stuckIrrel r env depth (.app (.const cO usO) x) (.lit (.strVal st))
    | _, _ => stuckIrrel r env depth (.app f x) (.lit l)
  | .fvar i ty₁, .fvar j ty₂ =>
    if i == j then pure true
    else stuckIrrel r env depth (.fvar i ty₁) (.fvar j ty₂)
  | .const n us, .const n' us' =>
    if n = n' then do
      if ← liftFueled "level comparison" (Level.isEquivList us us') then
        pure true
      else stuckIrrel r env depth (.const n us) (.const n' us')
    else stuckIrrel r env depth (.const n us) (.const n' us')
  | .app f₁ a₁, .app f₂ a₂ => do
    -- Stuck applications: **spine-wise** congruence (the official
    -- kernel's `is_def_eq_app`, lean4lean's `isDefEqApp`, nanoda's
    -- `def_eq_app`): equal spine lengths, one head comparison, then
    -- the argument lists pairwise (task #106: never the partial
    -- applications one by one).
    if (Expr.app f₁ a₁).getAppArgs.length =
        (Expr.app f₂ a₂).getAppArgs.length then
      if ← r.defeq depth (Expr.app f₁ a₁).getAppFn
          (Expr.app f₂ a₂).getAppFn then
        if ← defEqList r env depth (Expr.app f₁ a₁).getAppArgs
            (Expr.app f₂ a₂).getAppArgs then pure true
        else stuckIrrel r env depth (.app f₁ a₁) (.app f₂ a₂)
      else stuckIrrel r env depth (.app f₁ a₁) (.app f₂ a₂)
    else stuckIrrel r env depth (.app f₁ a₁) (.app f₂ a₂)
  -- One-sided λ: eta, else the stuck fallbacks.  (Two λs never get
  -- here: `quickDefEq` decides them.)
  | .lam ty₁ body₁, b₂ => do
    if ← etaCert mode r env depth ty₁ body₁ b₂ then pure true
    else stuckIrrel r env depth (.lam ty₁ body₁) b₂
  | a₁, .lam ty₂ body₂ => do
    if ← etaCert mode r env depth ty₂ body₂ a₁ then pure true
    else stuckIrrel r env depth a₁ (.lam ty₂ body₂)
  -- Distinct whnf-stuck head symbols: only the stuck fallbacks can
  -- equate them; `false` is always sound.
  | e₁, e₂ => stuckIrrel r env depth e₁ e₂

/-- **The definitional-equality body** (the official kernel's
`is_def_eq_core`, clause for clause except one deliberate reordering):
the syntactic fast path; the `Bool.true` shortcut (E2,
`boolTrueShortcut`: right side `Bool.true`, left side fvar-free or the
eager flag set — official's `(!has_fvar(t) || m_eager_reduce) &&
is_constant(s, Bool.true)`, the flag being `mode.eager`, task #353);
`quickDefEq` and proof
irrelevance (`is_def_eq_proof_irrel`) on the UNREDUCED sides; the cheap
head normalization of both sides (`whnfCore` with `cheap_proj`);
`quickDefEq` again; the lazy-delta loop (`lazyDeltaReduction`); the
proj/proj check (`defeqProjPair`); the FULL `whnfCore` of both sides
and, if either changed, a restart; and the stuck comparison
(`defeqStuck`).

**The deviation (task #333).**  The official kernel runs proof
irrelevance after the cheap `whnfCore`; here it runs before it, so two
proofs are never head-normalized to be compared.  Proof irrelevance
reads only the two sides' types, which reduction preserves, so the
verdict is the same on any pair whose reduction terminates; the
difference is a proof with no normal form (impredicative `Prop` +
`propext` + K-like `Eq.rec`, `tests/e2e/src/omega_kloop.lean`), which
the official order head-normalizes forever.  `quickDefEq` stays first
because it only fires on sorts, literals and binders, which `whnfCore`
leaves unchanged: on those pairs the old order's verdict is kept.

The restarts — after a literal acceleration in the loop and after the
full `whnfCore` — are `defeq` calls, as official's are `is_def_eq_core`
calls, so every entry runs the prefix (proof irrelevance included)
exactly once (the divergence audit's D3 holds by construction); the
long chains — the unfoldings — are iterations of the lazy loops. -/
def defeqBody (r : CoreFns m) (env : Env) : Nat → Expr → Expr → m Bool :=
  fun depth a b => do
    if a == b then pure true else
    if ← (if b.isBoolTrue && (mode.eager || !a.hasFvar) then
        boolTrueShortcut r depth a else pure false) then pure true else
    match ← quickDefEq mode r depth a b with
    | some v => pure v
    | none =>
    -- task #333: proof irrelevance on the UNREDUCED sides, before any
    -- head normalization (a proof is never reduced to be compared)
    if ← propIrrel r env depth a b then pure true else
    let a' ← r.whnfCore true depth a
    let b' ← r.whnfCore true depth b
    match ← quickDefEq mode r depth a' b' with
    | some v => pure v
    | none =>
    match ← lazyDeltaReduction mode r env depth defeqLoopFuel a' b' with
    | .verdict v => pure v
    | .unknown a₁ b₁ =>
    if ← defeqProjPair mode r env depth a₁ b₁ then pure true else
    -- the full `whnfCore` can only differ from the cheap one where the
    -- cheap mode left a projection stuck, which is then the spine head
    -- (`whnfCore` stops there); without one, the restart's test
    -- would find both sides unchanged, so it is skipped (cost only)
    if !a₁.headIsProj && !b₁.headIsProj then defeqStuck mode r env depth a₁ b₁ else
    let a₂ ← r.whnfCore false depth a₁
    let b₂ ← r.whnfCore false depth b₁
    if a₂ == a₁ && b₂ == b₁ then defeqStuck mode r env depth a₁ b₁
    else r.defeq depth a₂ b₂

end Bodies

/-- Tie the bodies together at a monad: the record whose entry points
are the bodies applied to the record one fuel level down.  Fuel is
*only* here — exhaustion is an internal error, never a verdict.  The
next level is constructed lazily, inside each entry point's closure
(constant work per call; an eager tower would cost `fuel` allocations
per instantiation). -/
def coreKnot {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (mode : CheckMode) (env : Env)
    (wrap : CoreFns m → CoreFns m) : Nat → CoreFns m
  | 0 =>
    { whnfCore := fun _ _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      defeqE := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      inferIO := fun _ _ => throw (.internal "fuel exhausted: infer") }
  | fuel + 1 =>
    wrap
      { whnfCore := fun c d e =>
          whnfCoreBody mode (coreKnot mode env wrap fuel) env c d e
        whnf := fun d e => whnfBody (coreKnot mode env wrap fuel) env d e
        infer := fun d e =>
          inferBody (coreKnot mode env wrap fuel) env d e
        defeq := fun d a b =>
          defeqBody mode (coreKnot mode env wrap fuel) env d a b
        -- **The eager slot** (task #353): the eager tower, the knot at
        -- `mode.toEager` one level down (the flag propagates to
        -- everything the comparison calls, as official's does)
        defeqE := fun d a b =>
          defeqBody mode.toEager (coreKnot mode.toEager env wrap fuel) env d a b
        -- **The io slot** (task #170 / #172 B4, task #346): official's
        -- `infer_only`, tied to the io-grade view of the knot one level
        -- down (the grade propagates, as official's does)
        inferIO := fun d e =>
          inferBodyIO
            (CoreFns.ioView (coreKnot mode env wrap fuel)) env d e }

/-- The shared fuel for the checker core: bounds the recursion depth of
reduction, inference and definitional equality.  Exhaustion is an
internal error, never a verdict.

**Effectively unbounded** (task #354).  The fuel exists so that the
knot is a structural recursion the proofs can induct over; as a limit
it is not needed: running out of it is an internal error (exit 3),
never an accept, so raising it cannot weaken the check.  It is `2^62`,
as `whnfCoreLoopFuel`.  Fuel is counted in knot levels, and each knot
level is native recursion, as in the official kernel (a `whnf` of
`W*200033` is a 200033-deep first-argument recursion in both).  What
bounds the depth is therefore the native stack: every checker thread
has the Lean runtime's default 1 GiB stack, a level costs 0.8–1.2 KB
of it, and a recursion deeper than about a million levels aborts
(`Stack overflow detected`, exit 134;
`tests/e2e/src/stack_fuel_offset.lean`) — an error like exit 3 for
the arena, and never an accept.  Task #353 had sized the fuel to the
stack (500000) so that the error was a clean exit 3; the openai/math
ContinuumCoulombHardness challenge needs more than that and is
accepted on the default stack.  See DESIGN.md, tasks #353 and #354. -/
@[irreducible, noinline] def checkFuel : Nat := 4611686018427387904  -- 2^62

end ConLeche
