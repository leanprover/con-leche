import Setlec.Kernel.TypeChecker
import Std.Data.HashMap

/-!
# The cached checker core

The executable twin of `Setlec.Kernel.TypeChecker`: the same mutually
recursive reduction/inference/definitional-equality core, threading a
memoization cache (`KCache`) for the three expensive functions.  The
pure module remains the *specification* — all semantic verification
(`Setlec/Model/*`, `Setlec/Verify/*`) reasons about it; a syntactic
bridge (`Setlec/Verify/CacheBridge`) shows that a successful cached run
is reproduced by the pure core at some fuel, so every claim proven
about the pure core applies to what this module computed.

Body texts are kept line-for-line identical to the specification
(modulo the `C` name suffix and the memo shims at the top of the three
cached functions) — the bridge proof depends on it.
-/

namespace Setlec

/-- Memoization state: results of the three expensive core functions,
keyed by binder depth and expression (the environment is fixed for the
lifetime of a cache — each top-level entry point starts fresh). -/
structure KCache where
  whnf : Std.HashMap (Nat × Expr) Expr := {}
  infer : Std.HashMap (Nat × Expr) Expr := {}
  defeq : Std.HashMap (Nat × Expr × Expr) Bool := {}
  annot : Std.HashMap (Nat × Expr) Expr := {}

instance : Inhabited KCache := ⟨{}⟩

/-- The cached checker monad. -/
abbrev CheckSM := StateT KCache CheckM

mutual

/-- Reduce an expression to weak head normal form.  Definitions are
delta-unfolded (eagerly for now; the lazy strategy of real kernels comes
with performance work); beta redexes reduce when certainly non-Prop or
when the argument certifies against the domain. -/
def whnfCoreC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → CheckSM Expr
  | 0, _, _ => throw (.internal "fuel exhausted: whnf")
  | fuel + 1, depth, e => do
    match (← get).whnf[(depth, e)]? with
    | some r => pure r
    | none =>
      let r ← show CheckSM Expr from
        match e with
        | .sort u => pure (.sort u)
        | .fvar idx n ty => pure (.fvar idx n ty)
        | .forallE n ty body bi => pure (.forallE n ty body bi)
        | .lam n ty body m => pure (.lam n ty body m)
        | .const n us =>
          match env.find? n with
          | some (.defnInfo cv value) =>
            if us.length = cv.levelParams.length then
              whnfCoreC env fuel depth (value.instantiateLevelParams cv.levelParams us)
            else pure (.const n us)
          | _ => pure (.const n us)
        | .app f a => do
          match ← whnfCoreC env fuel depth f with
          | .lam n ty body m =>
            match m.cod with
            | some v =>
              if v.isNonZero then whnfCoreC env fuel depth (body.instantiate1 a)
              else do
                -- Possibly-Prop redex: certify the argument against the
                -- domain before reducing (the soundness proof needs
                -- `⟦a⟧ ∈ ⟦ty⟧` at every level assignment).  An uncertified
                -- redex stays stuck — sound, and unreachable for
                -- well-typed input.
                let ta ← inferTypeCoreC env fuel depth a
                if ← isDefEqCoreC env fuel depth ta ty then
                  whnfCoreC env fuel depth (body.instantiate1 a)
                else pure (.app (.lam n ty body m) a)
            | none => pure (.app (.lam n ty body m) a)
          | f' => do
            match ← iotaRecC env fuel depth (.app f' a) with
            | some e'' => whnfCoreC env fuel depth e''
            | none => pure (.app f' a)
        | .proj sn i e => do
          let e' ← whnfCoreC env fuel depth e
          match e'.getAppFn with
          | .const c us =>
            -- Only the basis pair constructor is projected (`PSigma'.mk α β a b`).
            match env.find? c with
            | some (.ctorInfo _ nP nF) =>
              let args := e'.getAppArgs
              if c = psigmaMkName ∧ i < nF ∧ args.length = nP + nF ∧ us.length = 2 then
                let mx : Level := .max (us.getD 0 .zero) (us.getD 1 .zero)
                let arg := args.getD (nP + i) (.bvar 0)
                if mx.isNonZero then whnfCoreC env fuel depth arg
                else do
                  -- Possibly-Prop pair: certify that at Prop instances both
                  -- the projected argument and the pair collapse to the
                  -- proof point (see DESIGN.md on beta certification).
                  if ← projCertC env fuel depth e' i us nP then
                    whnfCoreC env fuel depth arg
                  else pure (.proj sn i e')
              else pure (.proj sn i e')
            | _ => pure (.proj sn i e')
          | _ => pure (.proj sn i e')
        | _ => throw (.notImplemented "whnf beyond the supported fragment")
      modify fun st => { st with whnf := st.whnf.insert (depth, e) r }
      pure r
  termination_by structural fuel _ _ => fuel

/-- Infer the type of an expression whose free variables are `fvar`s below
`depth` (no loose `bvar`s). -/
def inferTypeCoreC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → CheckSM Expr
  | 0, _, _ => throw (.internal "fuel exhausted: inferType")
  | fuel + 1, depth, e => do
    match (← get).infer[(depth, e)]? with
    | some r => pure r
    | none =>
      let r ← show CheckSM Expr from
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
        | .forallE _ ty _ m => do
          -- The codomain-sort annotation is trusted: the body was checked once,
          -- by real inference, when the annotation was created (`annotate`).
          match m.cod with
          | some v => do
            match ← whnfCoreC env fuel depth (← inferTypeCoreC env fuel depth ty) with
            | .sort u => pure (.sort (.imax u v))
            | _ => throw (.invalid "expected a sort")
          | none => throw (.internal "unannotated ∀-binder reached inferType")
        | .lam n ty body m => do
          match m.cod with
          | some v => do
            -- The domain must be a type (and the model needs its
            -- interpretation defined), exactly as in the ∀ rule.
            match ← whnfCoreC env fuel depth (← inferTypeCoreC env fuel depth ty) with
            | .sort _ => do
              let bt ← inferTypeCoreC env fuel (depth + 1)
                (body.instantiate1 (.fvar depth n ty))
              -- Re-check the stored annotation: it must be the sort of the
              -- body's type (the λ-annotation is *trusted* by the ∀ it builds,
              -- so it is *checked* here, where the body's type is at hand).
              match ← whnfCoreC env fuel (depth + 1) (← inferTypeCoreC env fuel (depth + 1) bt) with
              | .sort v' => do
                unless ← liftFueled "level comparison" (Level.isEquiv v v') do
                  throw (.invalid "λ-annotation does not match the body's sort")
                pure (.forallE n ty (bt.abstract1 depth) ⟨m.bi, some v⟩)
              | _ => throw (.invalid "expected a sort")
            | _ => throw (.invalid "expected a sort")
          | none => throw (.internal "unannotated λ-binder reached inferType")
        | .app f a => do
          let tf ← inferTypeCoreC env fuel depth f
          match ← whnfCoreC env fuel depth tf with
          | .forallE _ ty body _ =>
            let ta ← inferTypeCoreC env fuel depth a
            unless ← isDefEqCoreC env fuel depth ta ty do
              throw (.invalid "application argument type mismatch")
            pure (body.instantiate1 a)
          | _ => throw (.invalid "function expected")
        | .proj sn i e => do
          -- Only the basis pair type is projected natively; every other
          -- structure's type delta-unfolds (via its `_model` alias) to a
          -- `PSigma'` nest, which is what `whnfCoreC` produces here.
          match ← whnfCoreC env fuel depth (← inferTypeCoreC env fuel depth e) with
          | .app (.app (.const c _us) A) B =>
            match env.find? c with
            | some (.indInfo _ _) =>
              if c = psigmaName then
                match i with
                | 0 => pure A
                | 1 => pure (.app B (.proj sn 0 e))
                | _ => throw (.invalid "projection index out of range")
              else throw (.notImplemented "projection on a non-basis structure")
            | _ => throw (.notImplemented "projection on a non-basis structure")
          | _ => throw (.notImplemented "projection on a non-basis structure")
        | _ => throw (.notImplemented "inferType beyond the supported fragment")
      modify fun st => { st with infer := st.infer.insert (depth, e) r }
      pure r
  termination_by structural fuel _ _ => fuel

/-- Certification for projecting a possibly-Prop pair `e₂ =
PSigma'.mk α β a b` (levels `us`): the projected argument's *type's
sort* matches the corresponding level, and the pair's type's sort
matches `max` of the levels.  At Prop instances this collapses both the
argument and the pair to the proof point, which is exactly what the
reduction's soundness needs there. -/
def projCertC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Nat → List Level →
    Nat → CheckSM Bool
  | 0, _, _, _, _, _ => throw (.internal "fuel exhausted: projCertC")
  | fuel + 1, depth, e₂, i, us, nP => do
    let arg := e₂.getAppArgs.getD (nP + i) (.bvar 0)
    let ta ← inferTypeCoreC env fuel depth arg
    match ← whnfCoreC env fuel depth (← inferTypeCoreC env fuel depth ta) with
    | .sort uT =>
      let okT ← liftFueled "level comparison" (Level.isEquiv uT (us.getD i .zero))
      let te ← inferTypeCoreC env fuel depth e₂
      match ← whnfCoreC env fuel depth (← inferTypeCoreC env fuel depth te) with
      | .sort wT =>
        let okW ← liftFueled "level comparison"
          (Level.isEquiv wT (.max (us.getD 0 .zero) (us.getD 1 .zero)))
        pure (okT && okW)
      | _ => pure false
    | _ => pure false
  termination_by structural fuel _ _ _ => fuel

/-- Definitional-equality core. -/
def isDefEqCoreC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr → CheckSM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: isDefEq")
  | fuel + 1, depth, a, b => do
    match (← get).defeq[(depth, a, b)]? with
    | some r => pure r
    | none =>
      let r ← show CheckSM Bool from do
        match ← whnfCoreC env fuel depth a, ← whnfCoreC env fuel depth b with
        | .sort u, .sort v => liftFueled "level comparison" (Level.isEquiv u v)
        | .fvar i n₁ ty₁, .fvar j n₂ ty₂ =>
          if i == j then pure true
          else stuckIrrelC env fuel depth (.fvar i n₁ ty₁) (.fvar j n₂ ty₂)
        | .const n us, .const n' us' =>
          if n = n' then
            if ← liftFueled "level comparison" (Level.isEquivList us us') then
              pure true
            else stuckIrrelC env fuel depth (.const n us) (.const n' us')
          else stuckIrrelC env fuel depth (.const n us) (.const n' us')
        | .forallE n₁ ty₁ body₁ m₁, .forallE n₂ ty₂ body₂ m₂ => do
          unless ← isDefEqCoreC env fuel depth ty₁ ty₂ do return false
          let b₁ := body₁.instantiate1 (.fvar depth n₁ ty₁)
          let b₂ := body₂.instantiate1 (.fvar depth n₂ ty₂)
          unless ← isDefEqCoreC env fuel (depth + 1) b₁ b₂ do return false
          -- Deviation (see module docstring): codomain sorts must agree —
          -- with annotations this is a cheap level comparison.
          match m₁.cod, m₂.cod with
          | some v₁, some v₂ => liftFueled "level comparison" (Level.isEquiv v₁ v₂)
          | _, _ => throw (.internal "unannotated ∀-binder reached isDefEq")
        | .lam n₁ ty₁ body₁ m₁, .lam n₂ ty₂ body₂ m₂ => do
          unless ← isDefEqCoreC env fuel depth ty₁ ty₂ do return false
          let b₁ := body₁.instantiate1 (.fvar depth n₁ ty₁)
          let b₂ := body₂.instantiate1 (.fvar depth n₂ ty₂)
          unless ← isDefEqCoreC env fuel (depth + 1) b₁ b₂ do return false
          -- Deviation, as for ∀ (see module docstring).
          match m₁.cod, m₂.cod with
          | some v₁, some v₂ => liftFueled "level comparison" (Level.isEquiv v₁ v₂)
          | _, _ => throw (.internal "unannotated λ-binder reached isDefEq")
        | .app f₁ a₁, .app f₂ a₂ => do
          -- Stuck applications: congruence, else proof irrelevance.
          -- (Eta is not yet handled; a `false` answer is always sound.)
          if ← isDefEqCoreC env fuel depth f₁ f₂ then
            if ← isDefEqCoreC env fuel depth a₁ a₂ then
              pure true
            else stuckIrrelC env fuel depth (.app f₁ a₁) (.app f₂ a₂)
          else stuckIrrelC env fuel depth (.app f₁ a₁) (.app f₂ a₂)
        | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
          -- Stuck projections: congruence, else proof irrelevance.
          if i₁ == i₂ then
            if ← isDefEqCoreC env fuel depth e₁ e₂ then pure true
            else stuckIrrelC env fuel depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
          else stuckIrrelC env fuel depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
        -- One-sided λ: eta, else proof irrelevance.
        | .lam n₁ ty₁ body₁ m₁, b₂ => do
          if ← etaCertC env fuel depth n₁ ty₁ body₁ m₁ b₂ then pure true
          else stuckIrrelC env fuel depth (.lam n₁ ty₁ body₁ m₁) b₂
        | a₁, .lam n₂ ty₂ body₂ m₂ => do
          if ← etaCertC env fuel depth n₂ ty₂ body₂ m₂ a₁ then pure true
          else stuckIrrelC env fuel depth a₁ (.lam n₂ ty₂ body₂ m₂)
        -- Distinct whnf-stuck head symbols: only proof irrelevance can
        -- equate them; `false` is always sound, and `whnf` has already
        -- thrown on unsupported heads, so no unimplemented case can hide
        -- here.
        | e₁, e₂ => stuckIrrelC env fuel depth e₁ e₂
      modify fun st => { st with defeq := st.defeq.insert (depth, a, b) r }
      pure r
  termination_by structural fuel _ _ _ => fuel

/-- One iota step: the expression is a stored recursor applied to
exactly its telescope (params, motives, minors, indices, major), the
major premise whnfs to a fully applied constructor with a matching
rule, and the spine is certified against the recursor's own (pinned,
annotated) type.  The result is the rule's rhs applied to the
non-index prefix and the constructor's fields; over-application is
handled by the outer `whnf` app recursion. -/
def iotaRecC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr →
    CheckSM (Option Expr)
  | 0, _, _ => throw (.internal "fuel exhausted: iotaRecC")
  | fuel + 1, depth, e => do
    match e.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.recInfo cv nP nM nm ni rules) =>
        let args := e.getAppArgs
        if args.length = nP + nM + nm + ni + 1 then
          let major₀ ← whnfCoreC env fuel depth
            (args.getD (nP + nM + nm + ni) (.bvar 0))
          let major ← majorToCtorC env fuel depth c rules major₀
          match major.getAppFn with
          | .const cj usj =>
            match env.find? cj with
            | some (.ctorInfo cvj cnP cnF) =>
              match rules.find? (fun r => r.ctor == cj) with
              | some r =>
                let margs := major.getAppArgs
                if margs.length = cnP + cnF ∧ r.nfields = cnF then
                 if (cv.type.stripPis (nP + nM + nm + ni + 1)).isSome ∧
                    (cvj.type.stripPis (cnP + cnF)).isSome then
                  -- the constructor's levels must agree with the
                  -- recursor's instantiation (the rule links their
                  -- level parameters by name)
                  if ← liftFueled "level comparison" (Level.isEquivList usj
                      (cvj.levelParams.map fun p =>
                        Level.subst cv.levelParams us (.param p))) then
                   if ← defEqListC env fuel depth (margs.take cnP)
                      (args.take cnP) then
                    if ← iotaCertsC env fuel depth
                       (cv.type.instantiateLevelParams cv.levelParams us)
                       (args.take (nP + nM + nm + ni) ++ [major]) then
                     if ← iotaCertsC env fuel depth
                        (cvj.type.instantiateLevelParams cvj.levelParams usj)
                        margs then
                      pure (some (Expr.mkAppN
                        (r.rhs.instantiateLevelParams cv.levelParams us)
                        (args.take (nP + nM + nm) ++ margs.drop cnP)))
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
  termination_by structural fuel _ _ => fuel

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
def majorToCtorC (env : Env) : (fuel : Nat) → (depth : Nat) → Name →
    List RecRule → Expr → CheckSM Expr
  | 0, _, _, _, _ => throw (.internal "fuel exhausted: majorToCtorC")
  | fuel + 1, depth, recName, rules, major => do
    -- cheap syntactic gates before any inference: a rescue needs a
    -- single-rule recursor whose constructor's inductive is stored with
    -- the matching capability
    if isCtorApp env major then pure major else
    match rules with
    | [r] =>
      match env.find? r.ctor with
      | some (.ctorInfo cvj cnP cnF) =>
        match (cvj.type.piResult).getAppFn with
        | .const T _ =>
          match env.find? T with
          | some (.indInfo cvT caps) =>
            if caps.ruleK = true ∧ cnF = 0 then
              let tmaj ← whnfCoreC env fuel depth
                (← inferTypeCoreC env fuel depth major)
              match tmaj.getAppFn with
              | .const T' ust =>
                if T' = T ∧ cvj.levelParams.length = ust.length then
                  let fab := Expr.mkAppN (.const r.ctor ust)
                    (tmaj.getAppArgs.take cnP)
                  -- scope guard (cf. `annotateProjElimC`): scoping of the
                  -- fabricated major is checked syntactically, keeping
                  -- its verification local
                  if fab.wscopedB depth && fab.looseBVarsBounded 0 &&
                      fab.fvarLeaves.all
                        (fun l => major.fvarLeaves.contains l) then
                    if ← proofIrrelC env fuel depth fab major then pure fab
                    else pure major
                  else pure major
                else pure major
              | _ => pure major
            else if caps.eta = true ∧ r.ctor = caps.etaCtor ∧
                -- a projection function's rescue would reduce to a
                -- no-op (its own reduct), looping the reduction: a
                -- stuck projection stays stuck
                Name.isProjFnShape recName = false then
              let tmaj ← whnfCoreC env fuel depth
                (← inferTypeCoreC env fuel depth major)
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
                    if ← structEtaCertWithC env fuel depth fab major tmaj then
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
  termination_by structural fuel _ _ _ _ => fuel

/-- Certify a spine against a recursor telescope: each argument's
inferred type is defeq to the corresponding (instantiated) domain.
This is what hands the soundness proof the memberships the iota
equations need, at every level assignment. -/
def iotaCertsC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr →
    List Expr → CheckSM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: iotaCertsC")
  | _ + 1, _, _, [] => pure true
  | fuel + 1, depth, .forallE _ ty body _, arg :: rest => do
    let ta ← inferTypeCoreC env fuel depth arg
    if ← isDefEqCoreC env fuel depth ta ty then
      iotaCertsC env fuel depth (body.instantiate1 arg) rest
    else pure false
  | _ + 1, _, _, _ :: _ => pure false
  termination_by structural fuel _ _ _ => fuel

/-- Pairwise definitional equality of two spines (used to check a
major's constructor parameters against the recursor's). -/
def defEqListC (env : Env) : (fuel : Nat) → (depth : Nat) → List Expr →
    List Expr → CheckSM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: defEqListC")
  | _ + 1, _, [], [] => pure true
  | fuel + 1, depth, a :: as, b :: bs => do
    if ← isDefEqCoreC env fuel depth a b then
      defEqListC env fuel depth as bs
    else pure false
  | _ + 1, _, _, _ => pure false
  termination_by structural fuel _ _ _ => fuel

/-- The fallback for structurally distinct stuck terms: pair eta in
either direction, else proof irrelevance. -/
def stuckIrrelC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr →
    CheckSM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: stuckIrrelC")
  | fuel + 1, depth, a, b => do
    if ← pairEtaCertC env fuel depth a b then pure true
    else if ← pairEtaCertC env fuel depth b a then pure true
    else if ← structEtaCertC env fuel depth a b then pure true
    else if ← structEtaCertC env fuel depth b a then pure true
    else if ← structUnitCertC env fuel depth a b then pure true
    else proofIrrelC env fuel depth a b
  termination_by structural fuel _ _ _ => fuel

/-- Pair eta certification: `a` is a fully applied structure
constructor (a stored constructor that is the single rule of an
index-free recursor, under the `<ind>.rec` naming convention), `b`
inhabits the matching structure type at the same levels, and `a`'s
two fields are defeq to `b`'s projections.  In the model both sides
are then the pair of `b`'s components (or the proof point at the Prop
collapse); the environment invariant supplies the facts for the stored
constants. -/
def pairEtaCertC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr →
    CheckSM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: pairEtaCertC")
  | fuel + 1, depth, .app (.app (.app (.app (.const c us) _pα) _pβ) s₁) s₂,
      b => do
    match env.find? c with
    | some (.ctorInfo _ nP nF) =>
      if nP = 2 ∧ nF = 2 then
        let tb ← inferTypeCoreC env fuel depth b
        match ← whnfCoreC env fuel depth tb with
        | .app (.app (.const c' us') _A) _B =>
          match env.find? c' with
          | some (.indInfo _ _) =>
            match env.find? (c'.str "rec") with
            | some (.recInfo _ _ _ _ ni rules) =>
              match rules with
              | [r] =>
                if ni = 0 ∧ r.ctor = c ∧ r.nfields = 2 ∧
                    reservedBasisNames.contains (c'.str "rec") = true then
                  if ← liftFueled "level comparison"
                      (Level.isEquivList us us') then
                    if ← isDefEqCoreC env fuel depth s₁ (.proj c' 0 b) then
                      isDefEqCoreC env fuel depth s₂ (.proj c' 1 b)
                    else pure false
                  else pure false
                else pure false
              | _ => pure false
            | _ => pure false
          | _ => pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | _ + 1, _, _, _ => pure false
  termination_by structural fuel _ _ _ => fuel

/-- Certify each installed projection function's application to the
stuck side against its own telescope (the typing slots the reduct's
annotation chain needs), at the structure type's level arguments. -/
def structEtaProjCertsC (env : Env) : (fuel : Nat) → (depth : Nat) →
    Name → List Level → List Expr → Expr → List Name → List Nat →
    CheckSM Bool
  | 0, _, _, _, _, _, _, _ =>
    throw (.internal "fuel exhausted: structEtaProjCertsC")
  | _ + 1, _, _, _, _, _, _, [] => pure true
  | fuel + 1, depth, T, us', targs, b, lpsT, i :: rest => do
    match env.find? (projFnName T i) with
    | some (.recInfo cvp _ _ _ _ _) =>
      if cvp.levelParams = lpsT ∧
          (cvp.type.stripPis (targs.length + 1)).isSome = true then
        if ← iotaCertsC env fuel depth
            (cvp.type.instantiateLevelParams cvp.levelParams us')
            (targs ++ [b]) then
          structEtaProjCertsC env fuel depth T us' targs b lpsT rest
        else pure false
      else pure false
    | _ => pure false
  termination_by structural fuel _ _ _ _ _ _ _ => fuel

/-- Structural eta certification for a stored eta-capable structure:
`a` is a fully applied constructor of a structure whose recorded
capabilities include eta, `b` inhabits that structure type, the
constructor's parameters are the type's arguments, and every field is
the corresponding installed projection function applied to `b`.  The
type application is additionally certified against the type former's
telescope (the memberships the stored eta law consumes). -/
def structEtaCertC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr →
    Expr → CheckSM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: structEtaCertC")
  | fuel + 1, depth, a, b => do
    let tb ← inferTypeCoreC env fuel depth b
    let wtb ← whnfCoreC env fuel depth tb
    structEtaCertWithC env fuel depth a b wtb
  termination_by structural fuel _ _ _ => fuel

/-- The structure-eta certificate against a *given* weak-head-normal
type of the stuck side (see the specification twin). -/
def structEtaCertWithC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr →
    Expr → Expr → CheckSM Bool
  | 0, _, _, _, _ => throw (.internal "fuel exhausted: structEtaCertWithC")
  | fuel + 1, depth, a, b, wtb => do
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
                  if ← iotaCertsC env fuel depth
                      (cvT.type.instantiateLevelParams cvT.levelParams
                        us') wtb.getAppArgs then
                    if ← structEtaProjCertsC env fuel depth T us'
                        wtb.getAppArgs b cvT.levelParams
                        (List.range cnF) then
                      if ← defEqListC env fuel depth
                          (a.getAppArgs.take cnP) wtb.getAppArgs then
                        defEqListC env fuel depth (a.getAppArgs.drop cnP)
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
  termination_by structural fuel _ _ _ _ => fuel

/-- Unit-likeness certification: `a` and `b` inhabit the same stored
unit-like family (the types are definitionally equal and the type
application is certified against the family's telescope), so their
values coincide by the stored unit law. -/
def structUnitCertC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr →
    Expr → CheckSM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: structUnitCertC")
  | fuel + 1, depth, a, b => do
    let ta ← inferTypeCoreC env fuel depth a
    let wta ← whnfCoreC env fuel depth ta
    match wta.getAppFn with
    | .const T us' =>
      match env.find? T with
      | some (.indInfo cvT caps) =>
        if caps.unitlike = true ∧
            reservedBasisNames.contains T = false ∧
            wta.getAppArgs.length = caps.unitParams ∧
            us'.length = cvT.levelParams.length ∧
            (cvT.type.stripPis caps.unitParams).isSome = true then
          let tb ← inferTypeCoreC env fuel depth b
          let wtb ← whnfCoreC env fuel depth tb
          if ← isDefEqCoreC env fuel depth wta wtb then
            iotaCertsC env fuel depth
              (cvT.type.instantiateLevelParams cvT.levelParams us')
              wta.getAppArgs
          else pure false
        else pure false
      | _ => pure false
    | _ => pure false
  termination_by structural fuel _ _ _ => fuel

/-- Eta certification for a one-sided λ against a stuck term `b`: `b`'s
type whnfs to a `∀` whose domain is defeq to the λ's and whose codomain
annotation agrees, and the λ's body is pointwise the application of `b`.
The λ is then `b`'s eta-expansion (soundness: `SetTheory.lam_eta`). -/
def etaCertC (env : Env) : (fuel : Nat) → (depth : Nat) →
    Name → Expr → Expr → BinderMeta → Expr → CheckSM Bool
  | 0, _, _, _, _, _, _ => throw (.internal "fuel exhausted: etaCertC")
  | fuel + 1, depth, n₁, ty₁, body₁, m₁, b => do
    let tb ← inferTypeCoreC env fuel depth b
    match ← whnfCoreC env fuel depth tb with
    | .forallE _ ty₂ _ m₂ =>
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ =>
        if ← liftFueled "level comparison" (Level.isEquiv v₁ v₂) then
          if ← isDefEqCoreC env fuel depth ty₂ ty₁ then
            isDefEqCoreC env fuel (depth + 1)
              (body₁.instantiate1 (.fvar depth n₁ ty₁))
              (.app b (.fvar depth n₁ ty₁))
          else pure false
        else pure false
      | _, _ => pure false
    | _ => pure false
  termination_by structural fuel _ => fuel

/-- Proof irrelevance certification: both sides' types whnf to the
basis unit type (all of whose inhabitants are the proof point in the
model), or both sides' types' *sorts* are `Prop`.  In the model
everything inhabiting a proposition is the proof point, so any two such
terms are equal — no common-type check is needed for soundness. -/
def proofIrrelC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr →
    CheckSM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: proofIrrelC")
  | fuel + 1, depth, a, b => do
    let ta ← inferTypeCoreC env fuel depth a
    if isUnitLikeTy env (← whnfCoreC env fuel depth ta) then
      let tb ← inferTypeCoreC env fuel depth b
      if isUnitLikeTy env (← whnfCoreC env fuel depth tb) then
        pure true
      else
        pure false
    else
      match ← whnfCoreC env fuel depth (← inferTypeCoreC env fuel depth ta) with
      | .sort uT =>
        let okA ← liftFueled "level comparison" (Level.isEquiv uT .zero)
        let tb ← inferTypeCoreC env fuel depth b
        match ← whnfCoreC env fuel depth (← inferTypeCoreC env fuel depth tb) with
        | .sort vT =>
          let okB ← liftFueled "level comparison" (Level.isEquiv vT .zero)
          pure (okA && okB)
        | _ => pure false
      | _ => pure false
  termination_by structural fuel _ _ _ => fuel

end

/-- Ensure `e` (the type of some expression) is a sort, returning its
level. -/
def ensureSortCoreC (env : Env) (fuel depth : Nat) (e : Expr) : CheckSM Level := do
  match ← whnfCoreC env fuel depth e with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

mutual

/-- Compute the codomain-sort annotations of every binder in `e`, bottom-up,
by real inference on the opened (already annotated) body.  This is the one
place binder bodies are type-checked; `inferType` afterwards trusts the
annotations.  For a `forallE` the annotation is the body's sort (so this
also checks that the body *is* a type — the ∀-formation rule); for a `lam`
it is the sort of the body's type. -/
def annotateCoreC (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → CheckSM Expr
  | 0, _, _ => throw (.internal "fuel exhausted: annotate")
  | fuel + 1, depth, e => do
    match (← get).annot[(depth, e)]? with
    | some r => pure r
    | none =>
      let r ← show CheckSM Expr from
        match e with
        | .bvar i => pure (.bvar i)
        | .fvar idx n ty => pure (.fvar idx n ty)
        | .sort u => pure (.sort u)
        | .const n us => pure (.const n us)
        | .app f a => do
          let f' ← annotateCoreC env fuel depth f
          let a' ← annotateCoreC env fuel depth a
          -- Run the application rule here (the one place typing is checked):
          -- this establishes the semantic well-typedness clause for `app`
          -- nodes that beta-reduction soundness relies on (see DESIGN.md).
          let tf ← inferTypeCoreC env fuel depth f'
          match ← whnfCoreC env fuel depth tf with
          | .forallE _ ty _ _ =>
            let ta ← inferTypeCoreC env fuel depth a'
            unless ← isDefEqCoreC env fuel depth ta ty do
              throw (.invalid "application argument type mismatch")
            pure (.app f' a')
          | _ => throw (.invalid "function expected")
        | .forallE n ty body m => do
          let ty' ← annotateCoreC env fuel depth ty
          let body' ← annotateCoreC env fuel (depth + 1) (body.instantiate1 (.fvar depth n ty'))
          let v ← ensureSortCoreC env fuel (depth + 1)
            (← inferTypeCoreC env fuel (depth + 1) body')
          pure (.forallE n ty' (body'.abstract1 depth) ⟨m.bi, some v⟩)
        | .lam n ty body m => do
          let ty' ← annotateCoreC env fuel depth ty
          let body' ← annotateCoreC env fuel (depth + 1) (body.instantiate1 (.fvar depth n ty'))
          let bt ← inferTypeCoreC env fuel (depth + 1) body'
          let v ← ensureSortCoreC env fuel (depth + 1)
            (← inferTypeCoreC env fuel (depth + 1) bt)
          pure (.lam n ty' (body'.abstract1 depth) ⟨m.bi, some v⟩)
        | .letE _ _ _ _ => throw (.notImplemented "annotate: let-expressions")
        | .proj sn i e => do
          let e' ← annotateCoreC env fuel depth e
          -- Run the projection rule (the one place it is checked; this
          -- establishes the semantic proj clause of `AnnotOk`).
          let te ← whnfCoreC env fuel depth (← inferTypeCoreC env fuel depth e')
          match te with
          | .app (.app (.const c _) _) _ =>
            -- the basis pair projects natively
            if c = psigmaName then
              match env.find? c with
              | some (.indInfo _ _) => do
                unless i < 2 do
                  throw (.invalid "projection index out of range")
                pure (.proj sn i e')
              | _ => annotateProjElimC env fuel depth sn i te e'
            else annotateProjElimC env fuel depth sn i te e'
          | _ => annotateProjElimC env fuel depth sn i te e'
        | .lit _ => throw (.notImplemented "annotate: literals")
      modify fun st => { st with annot := st.annot.insert (depth, e) r }
      pure r
termination_by fuel _ _ => (fuel, 0)

/-- Rewrite a projection on a stored non-basis structure into its
installed projection function (a rules-carrying constant checked
against the structure's `_model.proj_i` at install) and annotate the
rewrite: the recursive annotation re-checks every node with the
ordinary rules, and the scope guard keeps the scaffolding inside the
annotated struct's free-variable leaves. -/
def annotateProjElimC (env : Env) (fuel depth : Nat) (sn : Name) (i : Nat)
    (te e' : Expr) : CheckSM Expr := do
  let .const T us := te.getAppFn
    | throw (.notImplemented "projection on a non-structure type")
  unless T = sn do
    throw (.invalid "projection structure mismatch")
  let some (.recInfo _ nP _ _ _ _) := env.find? (projFnName T i)
    | throw (.notImplemented
        "projection without an installed projection function")
  let args := te.getAppArgs
  unless args.length = nP do
    throw (.notImplemented "projection parameter mismatch")
  let raw := Expr.mkAppN (.const (projFnName T i) us) (args ++ [e'])
  unless raw.wscopedB depth && raw.looseBVarsBounded 0 &&
      raw.fvarLeaves.all (fun l => e'.fvarLeaves.contains l) do
    throw (.notImplemented "projection elimination scoping")
  annotateCoreC env fuel depth raw
termination_by (fuel, 1)

end

/-- `whnfCoreC` with the standard fuel and a fresh cache. -/
def whnf (env : Env) (depth : Nat) (e : Expr) : CheckM Expr :=
  (whnfCoreC env checkFuel depth e).run' {}

/-- `inferTypeCoreC` with the standard fuel and a fresh cache. -/
def inferType (env : Env) (depth : Nat) (e : Expr) : CheckM Expr :=
  (inferTypeCoreC env checkFuel depth e).run' {}

/-- `isDefEqCoreC` with the standard fuel and a fresh cache. -/
def isDefEq (env : Env) (depth : Nat) (a b : Expr) : CheckM Bool :=
  (isDefEqCoreC env checkFuel depth a b).run' {}

/-- `ensureSortCoreC` with the standard fuel and a fresh cache. -/
def ensureSort (env : Env) (depth : Nat) (e : Expr) : CheckM Level :=
  (ensureSortCoreC env checkFuel depth e).run' {}

/-- `annotateCoreC` with the standard fuel and a fresh cache. -/
def annotate (env : Env) (depth : Nat) (e : Expr) : CheckM Expr :=
  (annotateCoreC env checkFuel depth e).run' {}

end Setlec
