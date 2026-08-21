import Setlec.Kernel.Env
import Setlec.Kernel.Level
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Basis

/-!
# The checker core, in open-recursion style

Every core function is written **once**, as a non-recursive *body*
parameterized over a record of the mutually recursive entry points
(`CoreFns`) and polymorphic in the monad.  All recursion is routed
through the record — bodies never call themselves, and the few helpers
that do recurse (`iotaCerts`, `defEqList`, `structEtaProjCerts`) do so
structurally on a list.  Fuel lives only in the *knots* that tie the
record: the pure knot (`Setlec.Kernel.TypeChecker`) instantiates the
bodies at `CheckM` and is the verification's subject; the memoized knot
(`Setlec.Kernel.TypeCheckerC`) instantiates them at a state monad
carrying the caches and is what the checker executes.  A refinement
bridge relates the two (see DESIGN.md).

The reduction loop follows the official kernel (`whnfCore` never
delta-unfolds; `whnf` iterates `whnfCore → reduceNat → unfold one
definition`), and definitional equality starts with the syntactic fast
path and tries proof irrelevance before structural congruence.
Inference re-checks the application argument and the λ-annotation: the
soundness claims re-derive their membership slots from those checks at
their own fuel.  The official kernel's *infer-only* mode is deferred
until the refinement bridge's fuel-determinism machinery lands
(DESIGN.md).

Verification: `Setlec.Model.TypeChecker` (claims), `Setlec.Verify.*`
(inversions), both stated against the bodies with hypotheses about the
record and discharged by one induction at the knot.
-/

namespace Setlec

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

/-- The record of mutually recursive core entry points.  `whnfCore`
computes a head normal form without delta; `whnf` is the full reduction
loop; `infer` is type inference;
`defeq` is definitional equality; `annotate` computes binder
annotations (and is the one place typing is checked). -/
structure CoreFns (m : Type → Type u) where
  whnfCore : Nat → Expr → m Expr
  whnf : Nat → Expr → m Expr
  infer : Nat → Expr → m Expr
  defeq : Nat → Expr → Expr → m Bool
  annotate : Nat → Expr → m Expr

section Bodies

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- Lift a fuel-style partial result; `none` is an internal error. -/
def liftFueled (what : String) : Option α → m α
  | some a => pure a
  | none => throw (.internal s!"fuel exhausted: {what}")

/-- The public projection-function constant installed for field `i` of
a modeled structure `T` (a `Nat` component keeps it out of the way of
exported identifiers; installs are duplicate-checked regardless). -/
def projFnName (T : Name) (i : Nat) : Name := (T.str "proj").num i

/-- The model-side name of field `i`'s projection for `T`
(the documented public interface of the preprocessor's models). -/
def projModelName (T : Name) (i : Nat) : Name :=
  (T.str "_model").str ("proj_" ++ toString i)

/-- Is the expression headed by a stored constructor? -/
def isCtorApp (env : Env) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ =>
    match env.find? c with
    | some (.ctorInfo _ _ _) => true
    | _ => false
  | _ => false

/-- Does the syntactic pi telescope end in a (normalized) `Prop`?
Used for the K capability (an inductive *proposition*) and to guard the
structure-eta rescue (the official kernel does not eta-rescue
propositional structures). -/
def piResultIsProp (e : Expr) : Bool :=
  match e.piResult with
  | .sort u => Level.isEquiv u .zero == some true
  | _ => false

/-- Is this (whnf'd) type expression a unit-like inductive type — a
stored inductive whose recursor (under the `<ind>.rec` naming
convention) has no indices and a single zero-field rule?  All of its
inhabitants are then equal (in the model: the proof point; the
environment invariant supplies the fact for the stored constant). -/
def isUnitLikeTy (env : Env) : Expr → Bool
  | .const c _ =>
    (match env.find? c with
      | some (.indInfo _ _) => true
      | _ => false) &&
    (match env.find? (c.str "rec") with
      | some (.recInfo _ _ _ _ 0 [r]) => r.nfields == 0
      | _ => false) &&
    -- native unit semantics: pinned basis blocks only (env-stored
    -- capability flags will replace this)
    reservedBasisNames.contains (c.str "rec")
  | _ => false

/-- Unfold the (application of a) definition at the head, one step.
`none` when the head is not an unfoldable definition. -/
def unfoldDefinition (env : Env) (e : Expr) : Option Expr :=
  match e.getAppFn with
  | .const n us =>
    match env.find? n with
    | some (.defnInfo cv value) =>
      if us.length = cv.levelParams.length then
        some (Expr.mkAppN (value.instantiateLevelParams cv.levelParams us)
          e.getAppArgs)
      else none
    | _ => none
  | _ => none

/-- The constructor form of a `Nat` literal, one layer:
`n + 1` becomes `Nat.succ (lit n)`, `0` becomes `Nat.zero` (the
official kernel's `natLitToConstructor`, used on recursor majors). -/
def natLitToConstructor (n : Nat) : Expr :=
  match n with
  | 0 => .const natZeroName []
  | k + 1 => .app (.const natSuccName []) (.lit (.natVal k))

/-- The stored `Nat` declaration has the expected shape. -/
def natIndOk : Option ConstantInfo → Bool
  | some (.indInfo cv _) =>
    cv.levelParams.isEmpty && cv.type == .sort (.succ .zero)
  | _ => false

/-- The stored `Nat.zero` declaration has the expected shape. -/
def natZeroOk : Option ConstantInfo → Bool
  | some (.ctorInfo cv _ _) =>
    cv.levelParams.isEmpty && cv.type == .const natName []
  | _ => false

/-- The stored `Nat.succ` declaration has the expected (annotated)
shape. -/
def natSuccOk : Option ConstantInfo → Bool
  | some (.ctorInfo cv _ _) =>
    cv.levelParams.isEmpty &&
    (match cv.type with
     | .forallE _ (.const c1 []) (.const c2 []) mb =>
       c1 == natName && c2 == natName && mb.cod == some (.succ .zero)
     | _ => false)
  | _ => false

/-- Whether the environment supports `Nat` literals: `Nat`, `Nat.zero`
and `Nat.succ` are stored with exactly the expected kinds, level
parameters and (annotated) types.  Every literal code path is guarded
on this — the model interprets a literal by iterating the `Nat.succ`
value on the `Nat.zero` value, and the soundness proofs read the
declaration shapes off this guard. -/
def natLitSupported (env : Env) : Bool :=
  natIndOk (env.find? natName) && natZeroOk (env.find? natZeroName) &&
    natSuccOk (env.find? natSuccName)

/-- Do all constants referenced in `e` (including inside `fvar` type
annotations) resolve in `env`?  A `Nat` literal implicitly references
the `Nat` basis constants.  Checked once per declaration; keeps the
environment well-formedness invariant syntactic. -/
def Expr.constsResolve (env : Env) : Expr → Bool
  | .bvar _ | .sort _ | .lit (.strVal _) => true
  | .lit (.natVal _) =>
    (env.find? natName).isSome && (env.find? natZeroName).isSome &&
      (env.find? natSuccName).isSome
  | .const n _ => (env.find? n).isSome
  | .fvar _ _ ty => ty.constsResolve env
  | .app f a => f.constsResolve env && a.constsResolve env
  | .lam _ ty body _ | .forallE _ ty body _ =>
    ty.constsResolve env && body.constsResolve env
  | .letE _ ty val body =>
    ty.constsResolve env && val.constsResolve env && body.constsResolve env
  | .proj s _ e => (env.find? s).isSome && e.constsResolve env

/-- Convert a `Nat`-literal major premise to constructor form, one
layer; anything else passes through. -/
def litToCtorIfNat (env : Env) : Expr → Expr
  | .lit (.natVal n) =>
    if natLitSupported env then natLitToConstructor n else .lit (.natVal n)
  | e => e

/-- A `Nat` literal reading of a whnf'd expression: literals and the
`Nat.zero` constant (the official kernel's `rawNatLitExt?`). -/
def rawNatLit? : Expr → Option Nat
  | .lit (.natVal n) => some n
  | .const c [] => if c = natZeroName then some 0 else none
  | _ => none

/-- Literal acceleration (the official kernel's `reduceNat`, run in the
`whnf` loop *before* delta-unfolding): pack `Nat.succ` applied to a
literal back into a literal.  Binary operations on literal arguments
are added with the verified fast-path capabilities (see DESIGN.md);
until then only the constructor packing reduces. -/
def reduceNat (_r : CoreFns m) (env : Env) (_depth : Nat) (e : Expr) :
    m (Option Expr) := do
  match e with
  | .app (.const c []) a =>
    if c = natSuccName ∧ natLitSupported env then
      match rawNatLit? a with
      | some n => pure (some (.lit (.natVal (n + 1))))
      | none => pure none
    else pure none
  | _ => pure none

/-- Certify a spine against a recursor telescope: each argument's
inferred type is defeq to the corresponding (instantiated) domain.
This is what hands the soundness proof the memberships the iota
equations need, at every level assignment. -/
def iotaCerts (r : CoreFns m) (env : Env) (depth : Nat) :
    Expr → List Expr → m Bool
  | _, [] => pure true
  | .forallE _ ty body _, arg :: rest => do
    let ta ← r.infer depth arg
    if ← r.defeq depth ta ty then
      iotaCerts r env depth (body.instantiate1 arg) rest
    else pure false
  | _, _ :: _ => pure false

/-- Peel a `∀`-telescope along an argument list (the residual type of
a fully applied telescope). -/
def piResidual : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: as => piResidual (b.instantiate1 a) as
  | _, _ :: _ => none

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

/-- Proof irrelevance certification: both sides' types whnf to the
basis unit type (all of whose inhabitants are the proof point in the
model), or both sides' types' *sorts* are `Prop`.  In the model
everything inhabiting a proposition is the proof point, so any two such
terms are equal — no common-type check is needed: soundness holds
without it, and the annotation-first discipline (every subterm is
checked before definitional equality compares it; congruence compares
argument pairs only after the earlier arguments matched) makes a
heterogeneous comparison unreachable, so the official kernel's check is
implied (see DESIGN.md, design-review triage). -/
def proofIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  let ta ← r.infer depth a
  if isUnitLikeTy env (← r.whnf depth ta) then
    let tb ← r.infer depth b
    if isUnitLikeTy env (← r.whnf depth tb) then
      pure true
    else
      pure false
  else
    match ← r.whnf depth (← r.infer depth ta) with
    | .sort uT =>
      let okA ← liftFueled "level comparison" (Level.isEquiv uT .zero)
      let tb ← r.infer depth b
      match ← r.whnf depth (← r.infer depth tb) with
      | .sort vT =>
        let okB ← liftFueled "level comparison" (Level.isEquiv vT .zero)
        pure (okA && okB)
      | _ => pure false
    | _ => pure false

/-- Pair eta certification: `a` is a fully applied structure
constructor (a stored constructor that is the single rule of an
index-free recursor, under the `<ind>.rec` naming convention), `b`
inhabits the matching structure type at the same levels, and `a`'s
two fields are defeq to `b`'s projections.  In the model both sides
are then the pair of `b`'s components (or the proof point at the Prop
collapse); the environment invariant supplies the facts for the stored
constants. -/
def pairEtaCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  match a with
  | .app (.app (.app (.app (.const c us) _pα) _pβ) s₁) s₂ =>
    match env.find? c with
    | some (.ctorInfo _cvm 2 2) => do
      let tb ← r.infer depth b
      match ← r.whnf depth tb with
      | .app (.app (.const c' us') _A) _B =>
        match env.find? c' with
        | some (.indInfo _ _) =>
          match env.find? (c'.str "rec") with
          | some (.recInfo _ _ _ _ 0 [rr]) =>
            if rr.ctor = c ∧ rr.nfields = 2 ∧
                reservedBasisNames.contains (c'.str "rec") = true then
              if ← liftFueled "level comparison"
                  (Level.isEquivList us us') then
                if ← r.defeq depth s₁ (.proj c' 0 b) then
                  r.defeq depth s₂ (.proj c' 1 b)
                else pure false
              else pure false
            else pure false
          | _ => pure false
        | _ => pure false
      | _ => pure false
    | _ => pure false
  | _ => pure false

/-- The per-projection telescope certificates of a structural eta
certification: for every field index, the installed projection
function's telescope is certified against the type's arguments and the
stuck side. -/
def structEtaProjCerts (r : CoreFns m) (env : Env) (depth : Nat)
    (T : Name) (us' : List Level) (targs : List Expr) (b : Expr)
    (lpsT : List Name) : List Nat → m Bool
  | [] => pure true
  | i :: rest => do
    match env.find? (projFnName T i) with
    | some (.recInfo cvp _ _ _ _ _) =>
      if cvp.levelParams = lpsT ∧
          (cvp.type.stripPis (targs.length + 1)).isSome = true then
        if ← iotaCerts r env depth
            (cvp.type.instantiateLevelParams cvp.levelParams us')
            (targs ++ [b]) then
          structEtaProjCerts r env depth T us' targs b lpsT rest
        else pure false
      else pure false
    | _ => pure false

/-- The structure-eta certificate against a *given* weak-head-normal
type of the stuck side (callers that already reduced it — the
stuck-major rescue — pass their own copy, so the certificate's facts
are in terms of that expression). -/
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
                caps.etaParams = cnP ∧ caps.etaFields = cnF ∧
                reservedBasisNames.contains T = false ∧
                reservedBasisNames.contains c = false ∧
                wtb.getAppArgs.length = cnP ∧
                us'.length = cvT.levelParams.length ∧
                cvc.levelParams = cvT.levelParams ∧
                (cvT.type.stripPis cnP).isSome = true then
              if ← liftFueled "level comparison"
                  (Level.isEquivList us us') then
                if ← iotaCerts r env depth
                    (cvT.type.instantiateLevelParams cvT.levelParams
                      us') wtb.getAppArgs then
                  if ← structEtaProjCerts r env depth T us'
                      wtb.getAppArgs b cvT.levelParams
                      (List.range cnF) then
                    if ← defEqList r env depth
                        (a.getAppArgs.take cnP) wtb.getAppArgs then
                      defEqList r env depth (a.getAppArgs.drop cnP)
                        ((List.range cnF).map fun i =>
                          Expr.mkAppN (.const (projFnName T i) us')
                            (wtb.getAppArgs ++ [b]))
                    else pure false
                  else pure false
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
the corresponding installed projection function applied to `b`.  The
type application is additionally certified against the type former's
telescope (the memberships the stored eta law consumes). -/
def structEtaCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  let tb ← r.infer depth b
  let wtb ← r.whnf depth tb
  structEtaCertWith r env depth a b wtb

/-- Unit-likeness certification: `a` and `b` inhabit the same stored
unit-like family (the types are definitionally equal and the type
application is certified against the family's telescope), so their
values coincide by the stored unit law. -/
def structUnitCert (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  let ta ← r.infer depth a
  let wta ← r.whnf depth ta
  match wta.getAppFn with
  | .const T us' =>
    match env.find? T with
    | some (.indInfo cvT caps) =>
      if caps.unitlike = true ∧
          reservedBasisNames.contains T = false ∧
          wta.getAppArgs.length = caps.unitParams ∧
          us'.length = cvT.levelParams.length ∧
          (cvT.type.stripPis caps.unitParams).isSome = true then
        let tb ← r.infer depth b
        let wtb ← r.whnf depth tb
        if ← r.defeq depth wta wtb then
          iotaCerts r env depth
            (cvT.type.instantiateLevelParams cvT.levelParams us')
            wta.getAppArgs
        else pure false
      else pure false
    | _ => pure false
  | _ => pure false

/-- Eta certification for a one-sided λ against a stuck term `b`: `b`'s
type whnfs to a `∀` whose domain is defeq to the λ's and whose codomain
annotation agrees, and the λ's body is pointwise the application of `b`.
The λ is then `b`'s eta-expansion (soundness: `SetTheory.lam_eta`). -/
def etaCert (r : CoreFns m) (_env : Env) (depth : Nat)
    (n₁ : Name) (ty₁ body₁ : Expr) (m₁ : BinderMeta) (b : Expr) :
    m Bool := do
  let tb ← r.infer depth b
  match ← r.whnf depth tb with
  | .forallE _ ty₂ _ m₂ =>
    match m₁.cod, m₂.cod with
    | some v₁, some v₂ =>
      if ← liftFueled "level comparison" (Level.isEquiv v₁ v₂) then
        if ← r.defeq depth ty₂ ty₁ then
          r.defeq (depth + 1)
            (body₁.instantiate1 (.fvar depth n₁ ty₁))
            (.app b (.fvar depth n₁ ty₁))
        else pure false
      else pure false
    | _, _ => pure false
  | _ => pure false

/-- The fallback for structurally distinct stuck terms: pair eta in
either direction, structural eta in either direction, unit-likeness,
else proof irrelevance. -/
def stuckIrrel (r : CoreFns m) (env : Env) (depth : Nat) (a b : Expr) :
    m Bool := do
  if ← pairEtaCert r env depth a b then pure true
  else if ← pairEtaCert r env depth b a then pure true
  else if ← structEtaCert r env depth a b then pure true
  else if ← structEtaCert r env depth b a then pure true
  else if ← structUnitCert r env depth a b then pure true
  else proofIrrel r env depth a b

/-- Stuck-major rescue (`to_cnstr_when_K` and `to_cnstr_when_structure`
in the official kernel): a recursor's major premise that does not whnf
to a constructor application may still be *replaced* by one.  For a
K-flagged inductive proposition the parameters-only application of the
single constructor is fabricated from the major's type and certified by
proof irrelevance (in the model both are the proof point); for an
eta-capable structure the constructor of the major's projections is
fabricated and certified by the structure-eta certificate (in the model
both are the tuple of the major's components).  An uncertified major
stays put — sound, the reduction simply stays stuck. -/
def majorToCtor (r : CoreFns m) (env : Env) (depth : Nat)
    (recName : Name) (rules : List RecRule) (major : Expr) : m Expr := do
  -- cheap syntactic gates before any inference: a rescue needs a
  -- single-rule recursor whose constructor's inductive is stored with
  -- the matching capability
  if isCtorApp env major then pure major else
  match rules with
  | [rl] =>
    match env.find? rl.ctor with
    | some (.ctorInfo cvj cnP cnF) =>
      match (cvj.type.piResult).getAppFn with
      | .const T _ =>
        match env.find? T with
        | some (.indInfo cvT caps) =>
          if caps.ruleK = true ∧ cnF = 0 then
            let tmaj ← r.whnf depth (← r.infer depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              if T' = T ∧ cvj.levelParams.length = ust.length then
                let fab := Expr.mkAppN (.const rl.ctor ust)
                  (tmaj.getAppArgs.take cnP)
                -- scope guard (cf. `annotateProjElim`): scoping of the
                -- fabricated major is checked syntactically, keeping
                -- its verification local
                if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                    fab.fvarLeaves.all
                      (fun l => major.fvarLeaves.contains l) then
                  -- no explicit type check on the fabrication: the
                  -- endpoint condition (`Eq`: defeq endpoints) is
                  -- enforced by the iota certificates on the major
                  -- slot, which the soundness proof makes
                  -- load-bearing — a machine-checked invariant (see
                  -- DESIGN.md, design-review triage)
                  if ← proofIrrel r env depth fab major then pure fab
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else if caps.eta = true ∧ rl.ctor = caps.etaCtor ∧
              -- a projection function's rescue would reduce to a
              -- no-op (its own reduct), looping the reduction: a
              -- stuck projection stays stuck; and the official
              -- kernel does not eta-rescue propositional structures
              Name.isProjFnShape recName = false ∧
              piResultIsProp cvT.type = false then
            let tmaj ← r.whnf depth (← r.infer depth major)
            match tmaj.getAppFn with
            | .const T' ust =>
              if T' = T ∧ tmaj.getAppArgs.length = caps.etaParams ∧
                  ust.length = cvT.levelParams.length then
                let fab := Expr.mkAppN (.const caps.etaCtor ust)
                  (tmaj.getAppArgs ++
                    (List.range caps.etaFields).map fun j =>
                      Expr.mkAppN (.const (projFnName T j) ust)
                        (tmaj.getAppArgs ++ [major]))
                -- scope guard, as in the K branch
                if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                    fab.fvarLeaves.all
                      (fun l => major.fvarLeaves.contains l) then
                  if ← structEtaCertWith r env depth fab major tmaj then
                    pure fab
                  else pure major
                else pure major
              else pure major
            | _ => pure major
          else pure major
        | _ => pure major
      | _ => pure major
    | _ => pure major
  | _ => pure major

/-- One iota step: the expression is a stored recursor applied to
exactly its telescope (params, motives, minors, indices, major), the
major premise whnfs to a fully applied constructor with a matching
rule (a `Nat`-literal major converts to constructor form one layer, a
stuck major may be rescued — see `majorToCtor`), and the spine is
certified against the recursor's own (pinned, annotated) type.  The
result is the rule's rhs applied to the non-index prefix and the
constructor's fields; over-application is handled by the outer app
recursion. -/
def iotaRec (r : CoreFns m) (env : Env) (depth : Nat) (e : Expr) :
    m (Option Expr) := do
  match e.getAppFn with
  | .const c us =>
    match env.find? c with
    | some (.recInfo cv nP nM nm ni rules) =>
      let args := e.getAppArgs
      if args.length = nP + nM + nm + ni + 1 then
        let major₀ ← r.whnf depth
          (args.getD (nP + nM + nm + ni) (.bvar 0))
        let major ← majorToCtor r env depth c rules (litToCtorIfNat env major₀)
        match major.getAppFn with
        | .const cj usj =>
          match env.find? cj with
          | some (.ctorInfo cvj cnP cnF) =>
            match rules.find? (fun r' => r'.ctor == cj) with
            | some rl =>
              let margs := major.getAppArgs
              if margs.length = cnP + cnF ∧ rl.nfields = cnF then
               if (cv.type.stripPis (nP + nM + nm + ni + 1)).isSome ∧
                  (cvj.type.stripPis (cnP + cnF)).isSome then
                -- the constructor's levels must agree with the
                -- recursor's instantiation (the rule links their
                -- level parameters by name)
                if ← liftFueled "level comparison" (Level.isEquivList usj
                    (cvj.levelParams.map fun p =>
                      Level.subst cv.levelParams us (.param p))) then
                 if ← defEqList r env depth (margs.take cnP)
                    (args.take cnP) then
                  if ← iotaCerts r env depth
                     (cv.type.instantiateLevelParams cv.levelParams us)
                     (args.take (nP + nM + nm + ni) ++ [major]) then
                   if ← iotaCerts r env depth
                      (cvj.type.instantiateLevelParams cvj.levelParams usj)
                      margs then
                    -- the recursor's index arguments must match the
                    -- constructor's canonical index tuple (the residual
                    -- of its telescope, whose head must be the stored
                    -- family): the model's iota equation only speaks
                    -- about the canonical indices
                    match (cvj.type.instantiateLevelParams cvj.levelParams
                          usj).stripPis (cnP + cnF),
                        piResidual (cvj.type.instantiateLevelParams
                          cvj.levelParams usj) margs with
                    | some (_, cbody), some residual =>
                      match cbody.getAppFn with
                      | .const _ _ =>
                        if ← defEqList r env depth
                            (residual.getAppArgs.drop cnP)
                            ((args.take (nP + nM + nm + ni)).drop
                              (nP + nM + nm)) then
                          pure (some (Expr.mkAppN
                            (rl.rhs.instantiateLevelParams cv.levelParams us)
                            (args.take (nP + nM + nm) ++ margs.drop cnP)))
                        else pure none
                      | _ => pure none
                    | _, _ => pure none
                   else pure none
                  else pure none
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

/-- Certification for projecting a possibly-Prop pair `e₂ =
PSigma'.mk α β a b` (levels `us`): the projected argument's *type's
sort* matches the corresponding level, and the pair's type's sort
matches `max` of the levels.  At Prop instances this collapses both the
argument and the pair to the proof point, which is exactly what the
reduction's soundness needs there. -/
def projCert (r : CoreFns m) (_env : Env) (depth : Nat)
    (e₂ : Expr) (i : Nat) (us : List Level) (nP : Nat) : m Bool := do
  let arg := e₂.getAppArgs.getD (nP + i) (.bvar 0)
  let ta ← r.infer depth arg
  match ← r.whnf depth (← r.infer depth ta) with
  | .sort uT =>
    let okT ← liftFueled "level comparison" (Level.isEquiv uT (us.getD i .zero))
    let te ← r.infer depth e₂
    match ← r.whnf depth (← r.infer depth te) with
    | .sort wT =>
      let okW ← liftFueled "level comparison"
        (Level.isEquiv wT (.max (us.getD 0 .zero) (us.getD 1 .zero)))
      pure (okT && okW)
    | _ => pure false
  | _ => pure false

/-- The head-normalization body: beta (with the possibly-Prop
certificate), iota (with the stuck-major machinery) and the native
basis pair projection — but **no delta**; unfolding happens in the
`whnf` loop.  Values (sorts, binders, constants, literals) return
themselves. -/
def whnfCoreBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e =>
    match e with
    | .sort u => pure (.sort u)
    | .fvar idx n ty => pure (.fvar idx n ty)
    | .forallE n ty body bi => pure (.forallE n ty body bi)
    | .lam n ty body mb => pure (.lam n ty body mb)
    | .const n us => pure (.const n us)
    | .lit l => pure (.lit l)
    | .app f a => do
      match ← r.whnfCore depth f with
      | .lam n ty body mb =>
        match mb.cod with
        | some v =>
          if v.isNonZero then r.whnfCore depth (body.instantiate1 a)
          else do
            -- Possibly-Prop redex: certify the argument against the
            -- domain before reducing (the soundness proof needs
            -- `⟦a⟧ ∈ ⟦ty⟧` at every level assignment).  An uncertified
            -- redex stays stuck — sound, and unreachable for
            -- well-typed input.
            let ta ← r.infer depth a
            if ← r.defeq depth ta ty then
              r.whnfCore depth (body.instantiate1 a)
            else pure (.app (.lam n ty body mb) a)
        | none => pure (.app (.lam n ty body mb) a)
      | f' => do
        match ← iotaRec r env depth (.app f' a) with
        | some e'' => r.whnfCore depth e''
        | none => pure (.app f' a)
    | .proj sn i pe => do
      let e' ← r.whnf depth pe
      match e'.getAppFn with
      | .const c us =>
        -- Only the basis pair constructor is projected (`PSigma'.mk α β a b`).
        match env.find? c with
        | some (.ctorInfo _ nP nF) =>
          let args := e'.getAppArgs
          if c = psigmaMkName ∧ i < nF ∧ args.length = nP + nF ∧ us.length = 2 then
            let mx : Level := .max (us.getD 0 .zero) (us.getD 1 .zero)
            let arg := args.getD (nP + i) (.bvar 0)
            if mx.isNonZero then r.whnfCore depth arg
            else do
              -- Possibly-Prop pair: certify that at Prop instances both
              -- the projected argument and the pair collapse to the
              -- proof point (see DESIGN.md on beta certification).
              if ← projCert r env depth e' i us nP then
                r.whnfCore depth arg
              else pure (.proj sn i e')
          else pure (.proj sn i e')
        | _ => pure (.proj sn i e')
      | _ => pure (.proj sn i e')
    | .bvar _ | .letE .. =>
      throw (.notImplemented "whnf beyond the supported fragment")

/-- The reduction loop (the official kernel's `whnf`): head-normalize,
try literal acceleration, unfold one definition, repeat. -/
def whnfBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e => do
    let e₁ ← r.whnfCore depth e
    match ← reduceNat r env depth e₁ with
    | some e₂ => r.whnf depth e₂
    | none =>
      match unfoldDefinition env e₁ with
      | some e₂ => r.whnf depth e₂
      | none => pure e₁

/-- Ensure `e` (the type of some expression) is a sort, returning its
level. -/
def ensureSort (r : CoreFns m) (_env : Env) (depth : Nat) (e : Expr) :
    m Level := do
  match ← r.whnf depth e with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-- The inference body — **infer-only**: the application rule's
argument check ran once, in the annotation pass, and is trusted here
(so speculative inference inside reduction cannot reject). -/
def inferBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e =>
    match e with
    | .sort u => pure (.sort (.succ u))
    | .fvar _ _ ty => pure ty
    | .const n us => do
      match env.find? n with
      | none => throw (.invalid s!"unknown constant {n}")
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        pure (cv.type.instantiateLevelParams cv.levelParams us)
    | .lit (.natVal _) => do
      if natLitSupported env then pure (.const natName [])
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => throw (.notImplemented "string literals")
    | .forallE _ ty _ mb => do
      -- The codomain-sort annotation is trusted: the body was checked once,
      -- by real inference, when the annotation was created (`annotate`).
      match mb.cod with
      | some v => do
        match ← r.whnf depth (← r.infer depth ty) with
        | .sort u => pure (.sort (.imax u v))
        | _ => throw (.invalid "expected a sort")
      | none => throw (.internal "unannotated ∀-binder reached inferType")
    | .lam n ty body mb => do
      match mb.cod with
      | some v => do
        -- The domain must be a type (and the model needs its
        -- interpretation defined), exactly as in the ∀ rule.
        match ← r.whnf depth (← r.infer depth ty) with
        | .sort _ => do
          let bt ← r.infer (depth + 1)
            (body.instantiate1 (.fvar depth n ty))
          -- Re-check the stored annotation: it must be the sort of the
          -- body's type (the λ-annotation is *trusted* by the ∀ it
          -- builds, so it is *checked* here, where the body's type is
          -- at hand).
          match ← r.whnf (depth + 1) (← r.infer (depth + 1) bt) with
          | .sort v' => do
            unless ← liftFueled "level comparison" (Level.isEquiv v v') do
              throw (.invalid "λ-annotation does not match the body's sort")
            pure (.forallE n ty (bt.abstract1 depth) mb)
          | _ => throw (.invalid "expected a sort")
        | _ => throw (.invalid "expected a sort")
      | none => throw (.internal "unannotated λ-binder reached inferType")
    | .app f a => do
      let tf ← r.infer depth f
      match ← r.whnf depth tf with
      | .forallE _ ty body _ => do
        -- The argument check stays in inference for now: the soundness
        -- claim's `⟦a⟧ ∈ ⟦domain⟧` slot is re-derived here, at the
        -- claims' own fuel.  A later infer-only mode needs the fuel
        -- determinism machinery of the refinement bridge (DESIGN.md).
        let ta ← r.infer depth a
        unless ← r.defeq depth ta ty do
          throw (.invalid "application type mismatch")
        pure (body.instantiate1 a)
      | _ => throw (.invalid "function expected")
    | .proj sn i pe => do
      -- Only the basis pair type is projected natively; every other
      -- structure's type delta-unfolds (via its `_model` alias) to a
      -- `PSigma'` nest, which is what `whnf` produces here.
      match ← r.whnf depth (← r.infer depth pe) with
      | .app (.app (.const c _us) A) B =>
        match env.find? c with
        | some (.indInfo _ _) =>
          if c = psigmaName then
            match i with
            | 0 => pure A
            | 1 => pure (.app B (.proj sn 0 pe))
            | _ => throw (.invalid "projection index out of range")
          else throw (.notImplemented "projection on a non-pair type")
        | _ => throw (.notImplemented "projection on a non-pair type")
      | _ => throw (.notImplemented "projection on a non-pair type")
    | .bvar _ | .letE .. =>
      throw (.notImplemented "inferType beyond the supported fragment")

/-- The definitional-equality body: syntactic fast path, full
reduction of both sides, an early proof-irrelevance attempt, then
structural congruence with the stuck fallbacks. -/
def defeqBody (r : CoreFns m) (env : Env) : Nat → Expr → Expr → m Bool :=
  fun depth a b => do
    -- syntactic fast path (the references' most-hit branch)
    if a == b then pure true else
    let a' ← r.whnf depth a
    let b' ← r.whnf depth b
    if a' == b' then pure true else
    match a', b' with
    | .sort u, .sort v => liftFueled "level comparison" (Level.isEquiv u v)
    | .lit l₁, .lit l₂ => pure (l₁ == l₂)
    -- a packed literal against a constructor form: compare
    -- shape-directed (an unpack-and-retry would immediately repack in
    -- `reduceNat` and loop)
    | .lit (.natVal n), .const c us =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrel r env depth (.lit (.natVal n)) (.const c us)
    | .const c us, .lit (.natVal n) =>
      if c = natZeroName ∧ us = [] then pure (n == 0)
      else stuckIrrel r env depth (.const c us) (.lit (.natVal n))
    | .lit (.natVal nn), .app f x =>
      match nn, f with
      | k + 1, .const c [] =>
        if c = natSuccName then r.defeq depth (.lit (.natVal k)) x
        else stuckIrrel r env depth (.lit (.natVal nn)) (.app f x)
      | _, _ => stuckIrrel r env depth (.lit (.natVal nn)) (.app f x)
    | .app f x, .lit (.natVal nn) =>
      match nn, f with
      | k + 1, .const c [] =>
        if c = natSuccName then r.defeq depth x (.lit (.natVal k))
        else stuckIrrel r env depth (.app f x) (.lit (.natVal nn))
      | _, _ => stuckIrrel r env depth (.app f x) (.lit (.natVal nn))
    | .fvar i n₁ ty₁, .fvar j n₂ ty₂ =>
      if i == j then pure true
      else stuckIrrel r env depth (.fvar i n₁ ty₁) (.fvar j n₂ ty₂)
    | .const n us, .const n' us' =>
      if n = n' then
        if ← liftFueled "level comparison" (Level.isEquivList us us') then
          pure true
        else stuckIrrel r env depth (.const n us) (.const n' us')
      else stuckIrrel r env depth (.const n us) (.const n' us')
    | .forallE n₁ ty₁ body₁ m₁, .forallE n₂ ty₂ body₂ m₂ => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let b₁ := body₁.instantiate1 (.fvar depth n₁ ty₁)
      let b₂ := body₂.instantiate1 (.fvar depth n₂ ty₂)
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      -- Deviation (see module docstring): codomain sorts must agree —
      -- with annotations this is a cheap level comparison.
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ => liftFueled "level comparison" (Level.isEquiv v₁ v₂)
      | _, _ => throw (.internal "unannotated ∀-binder reached isDefEq")
    | .lam n₁ ty₁ body₁ m₁, .lam n₂ ty₂ body₂ m₂ => do
      unless ← r.defeq depth ty₁ ty₂ do return false
      let b₁ := body₁.instantiate1 (.fvar depth n₁ ty₁)
      let b₂ := body₂.instantiate1 (.fvar depth n₂ ty₂)
      unless ← r.defeq (depth + 1) b₁ b₂ do return false
      -- Deviation, as for ∀ (see module docstring).
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ => liftFueled "level comparison" (Level.isEquiv v₁ v₂)
      | _, _ => throw (.internal "unannotated λ-binder reached isDefEq")
    | .app f₁ a₁, .app f₂ a₂ => do
      -- Stuck applications: congruence, then the stuck fallbacks (the
      -- official kernel hoists proof irrelevance before congruence;
      -- with a shared depth fuel the hoist multiplies the depth cost
      -- of every comparison, so it stays in the fallback — same
      -- verdicts, different cost profile).
      if ← r.defeq depth f₁ f₂ then
        if ← r.defeq depth a₁ a₂ then
          pure true
        else stuckIrrel r env depth (.app f₁ a₁) (.app f₂ a₂)
      else stuckIrrel r env depth (.app f₁ a₁) (.app f₂ a₂)
    | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
      -- Stuck projections: congruence, else the stuck fallbacks.
      if i₁ == i₂ then
        if ← r.defeq depth e₁ e₂ then pure true
        else stuckIrrel r env depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
      else stuckIrrel r env depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
    -- One-sided λ: eta, else the stuck fallbacks.
    | .lam n₁ ty₁ body₁ m₁, b₂ => do
      if ← etaCert r env depth n₁ ty₁ body₁ m₁ b₂ then pure true
      else stuckIrrel r env depth (.lam n₁ ty₁ body₁ m₁) b₂
    | a₁, .lam n₂ ty₂ body₂ m₂ => do
      if ← etaCert r env depth n₂ ty₂ body₂ m₂ a₁ then pure true
      else stuckIrrel r env depth a₁ (.lam n₂ ty₂ body₂ m₂)
    -- Distinct whnf-stuck head symbols: only the stuck fallbacks can
    -- equate them; `false` is always sound, and `whnf` has already
    -- thrown on unsupported heads, so no unimplemented case can hide
    -- here.
    | e₁, e₂ => stuckIrrel r env depth e₁ e₂

/-- Check that a (raw) type is a `Prop` by annotating it and inferring
its sort. -/
def isPropType (r : CoreFns m) (env : Env) (depth : Nat) (ty : Expr) :
    m Bool := do
  let ty' ← r.annotate depth ty
  let s ← ensureSort r env depth (← r.infer depth ty')
  liftFueled "level comparison" (Level.isEquiv s Level.zero)

/-- Walk a field telescope to the `i`-th binder and return its domain,
earlier binders instantiated with projections of `e'`, mirroring the
official kernel's projection rule: for a `Prop` structure every
*depended-on* skipped field must itself be a `Prop`. -/
def projFieldDom (r : CoreFns m) (env : Env) (depth : Nat)
    (structProp : Bool) (sn : Name) (e' : Expr) :
    Nat → Nat → Expr → m Expr
  | _, 0, .forallE _ dom _ _ => pure dom
  | j, k + 1, .forallE _ dom rest _ => do
    if rest.looseBVarsBounded 0 then
      projFieldDom r env depth structProp sn e' (j + 1) k rest
    else
      if structProp then
        unless ← isPropType r env depth dom do
          throw (.invalid
            "projection through a non-Prop field of a Prop structure")
      projFieldDom r env depth structProp sn e' (j + 1) k
        (rest.instantiate1 (.proj sn j e'))
  | _, _, _ => throw (.invalid "projection index out of range")

/-- Fallback for structures without an installed projection function
(Prop-valued structures: the preprocessor emits no `_model.proj_i`
artifacts for them): inline the recursor elimination
`S.rec params motive minor e'`, with a constant motive — the projected
field's type, earlier fields replaced by projections of `e'` — and the
minor the constructor's field telescope as `λ`s returning field `i`.
The rewrite is annotated, so the ordinary rules re-check it; in
particular the kernel's Prop restriction (projections from a `Prop`
structure must land in `Prop`) surfaces as a type error when the
stored recursor's fixed motive sort cannot reach the field's. -/
def annotateProjRec (r : CoreFns m) (env : Env) (depth : Nat) (sn : Name)
    (i : Nat) (te e' : Expr) (us : List Level) : m Expr := do
  match env.find? (sn.str "rec"), env.find? sn with
  | some (.recInfo cvR nP 1 1 0 [rule]), some (.indInfo _ _) =>
    match env.find? (RecRule.ctor rule) with
    | some (.ctorInfo cvC _ cnF) =>
      let params := te.getAppArgs
      if params.length = nP then
        let ctorTy := cvC.type.instantiateLevelParams cvC.levelParams us
        match ctorTy.instPis params with
        | some tel =>
          let structProp ← isPropType r env depth te
          let fi ← projFieldDom r env depth structProp sn e' 0 i tel
          match Expr.pisToLams cnF tel (.bvar (cnF - 1 - i)) with
          | some minor =>
            -- the projected field's sort: the official Prop
            -- restriction, and the motive level for subsingleton
            -- eliminators
            let fi' ← r.annotate depth fi
            let sfi ← ensureSort r env depth (← r.infer depth fi')
            if structProp then
              unless ← liftFueled "level comparison"
                  (Level.isEquiv sfi Level.zero) do
                throw (.invalid "non-Prop projection from a Prop structure")
            let uf :=
              if cvR.levelParams.length = us.length + 1 then [sfi] else []
            let raw := Expr.mkAppN (.const (sn.str "rec") (uf ++ us))
              (params ++ [.lam (.str .anonymous "t") te fi ⟨.default, none⟩,
                minor, e'])
            if raw.wscopedB depth && raw.looseBVarsBounded 0 &&
                raw.fvarLeaves.all (fun l => e'.fvarLeaves.contains l) then
              r.annotate depth raw
            else throw (.notImplemented "projection elimination scoping")
          | none => throw (.invalid "projection index out of range")
        | none => throw (.invalid "projection index out of range")
      else throw (.notImplemented "projection parameter mismatch")
    | _ => throw (.notImplemented
        "projection constructor not stored")
  | _, _ => throw (.notImplemented
      "projection on a non-structure-like type")

/-- Rewrite a projection on a stored non-basis structure into its
installed projection function (a rules-carrying constant checked
against the structure's `_model.proj_i` at install) and annotate the
rewrite: the recursive annotation re-checks every node with the
ordinary rules, and the scope guard keeps the scaffolding inside the
annotated struct's free-variable leaves.  Structures without an
installed projection function fall back to `annotateProjRec`. -/
def annotateProjElim (r : CoreFns m) (env : Env) (depth : Nat) (sn : Name)
    (i : Nat) (te e' : Expr) : m Expr := do
  match te.getAppFn with
  | .const T us =>
    if T = sn then
      match env.find? (projFnName T i) with
      | some (.recInfo _ nP _ _ _ _) =>
        if te.getAppArgs.length = nP then
          let raw := Expr.mkAppN (.const (projFnName T i) us)
            (te.getAppArgs ++ [e'])
          if raw.wscopedB depth && raw.looseBVarsBounded 0 &&
              raw.fvarLeaves.all (fun l => e'.fvarLeaves.contains l) then
            r.annotate depth raw
          else throw (.notImplemented "projection elimination scoping")
        else throw (.notImplemented "projection parameter mismatch")
      | _ => annotateProjRec r env depth sn i te e' us
    else throw (.invalid "projection structure mismatch")
  | _ => throw (.notImplemented "projection on a non-structure type")

/-- The annotation body: compute the codomain-sort annotations of every
binder, bottom-up, by real inference on the opened (already annotated)
body.  This is the one place binder bodies — and the application rule —
are type-checked; `infer` afterwards trusts the annotations.  For a
`forallE` the annotation is the body's sort (so this also checks that
the body *is* a type — the ∀-formation rule); for a `lam` it is the
sort of the body's type. -/
def annotateBody (r : CoreFns m) (env : Env) : Nat → Expr → m Expr :=
  fun depth e =>
    match e with
    | .bvar i => pure (.bvar i)
    | .fvar idx n ty => pure (.fvar idx n ty)
    | .sort u => pure (.sort u)
    | .const n us => pure (.const n us)
    | .lit (.natVal n) => do
      -- a literal is well-formed exactly when its type's declarations
      -- are stored in the expected shape
      if natLitSupported env then pure (.lit (.natVal n))
      else throw (.invalid "Nat literal without the Nat basis declarations")
    | .lit (.strVal _) => throw (.notImplemented "string literals")
    | .app f a => do
      let f' ← r.annotate depth f
      let a' ← r.annotate depth a
      -- Run the application rule here (the one place typing is checked):
      -- this establishes the semantic well-typedness clause for `app`
      -- nodes that beta-reduction soundness relies on (see DESIGN.md).
      let tf ← r.infer depth f'
      match ← r.whnf depth tf with
      | .forallE _ ty _ _ =>
        let ta ← r.infer depth a'
        unless ← r.defeq depth ta ty do
          throw (.invalid "application argument type mismatch")
        pure (.app f' a')
      | _ => throw (.invalid "function expected")
    | .forallE n ty body mb => do
      let ty' ← r.annotate depth ty
      let body' ← r.annotate (depth + 1) (body.instantiate1 (.fvar depth n ty'))
      let v ← ensureSort r env (depth + 1) (← r.infer (depth + 1) body')
      pure (.forallE n ty' (body'.abstract1 depth) ⟨mb.bi, some v⟩)
    | .lam n ty body mb => do
      let ty' ← r.annotate depth ty
      let body' ← r.annotate (depth + 1) (body.instantiate1 (.fvar depth n ty'))
      let bt ← r.infer (depth + 1) body'
      let v ← ensureSort r env (depth + 1) (← r.infer (depth + 1) bt)
      pure (.lam n ty' (body'.abstract1 depth) ⟨mb.bi, some v⟩)
    | .letE _ _ _ _ => throw (.notImplemented "annotate: let-expressions")
    | .proj sn i pe => do
      let e' ← r.annotate depth pe
      -- Run the projection rule (the one place it is checked; this
      -- establishes the semantic proj clause of `AnnotOk`).
      let te ← r.whnf depth (← r.infer depth e')
      match te with
      | .app (.app (.const c _) _) _ =>
        -- the basis pair projects natively
        if c = psigmaName then
          match env.find? c with
          | some (.indInfo _ _) => do
            unless i < 2 do
              throw (.invalid "projection index out of range")
            pure (.proj sn i e')
          | _ => annotateProjElim r env depth sn i te e'
        else annotateProjElim r env depth sn i te e'
      | _ => annotateProjElim r env depth sn i te e'

end Bodies

/-- Tie the bodies together at a monad: the record whose entry points
are the bodies applied to the record one fuel level down.  Fuel is
*only* here — exhaustion is an internal error, never a verdict.  The
next level is constructed lazily, inside each entry point's closure
(constant work per call; an eager tower would cost `fuel` allocations
per instantiation). -/
def coreKnot {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]
    (env : Env)
    (wrap : CoreFns m → CoreFns m) : Nat → CoreFns m
  | 0 =>
    { whnfCore := fun _ _ => throw (.internal "fuel exhausted: whnfCore")
      whnf := fun _ _ => throw (.internal "fuel exhausted: whnf")
      infer := fun _ _ => throw (.internal "fuel exhausted: infer")
      defeq := fun _ _ _ => throw (.internal "fuel exhausted: defeq")
      annotate := fun _ _ => throw (.internal "fuel exhausted: annotate") }
  | fuel + 1 =>
    wrap
      { whnfCore := fun d e => whnfCoreBody (coreKnot env wrap fuel) env d e
        whnf := fun d e => whnfBody (coreKnot env wrap fuel) env d e
        infer := fun d e => inferBody (coreKnot env wrap fuel) env d e
        defeq := fun d a b => defeqBody (coreKnot env wrap fuel) env d a b
        annotate := fun d e =>
          annotateBody (coreKnot env wrap fuel) env d e }

/-- The shared fuel for the checker core: bounds the recursion depth of
reduction, inference and definitional equality.  Exhaustion is an
internal error, never a verdict. -/
def checkFuel : Nat := 100000

end Setlec
