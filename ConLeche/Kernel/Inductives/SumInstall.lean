module

public import ConLeche.Kernel.Inductives.StructInstall

@[expose] public section

/-!
# The shared install stages (pure fueled checker)

The former, constructor and rule-shape stages the block install runs
(`checkBlock`, `ConLeche/Kernel/Inductives/BlockTail.lean`): the
type former's telescope, one constructor stage per constructor, the
constructors consed, the stored rules.

The per-constructor stage (`checkSumCtor`) reads the residual as the
family at the parameters followed by `nIdx` index expressions; the
field-sort walk (`checkStructFieldSortsI`) carries official's
subsingleton-elimination criterion for a large eliminator at a `Prop` family with one
constructor (a field that is not a proposition must be one of the
index expressions); the domain pins are shared (`checkStructDomsAt`).
Every constructor's type is checked at the environment holding the
type former alone and the constructors are consed afterwards: they
never mention each other, and this order keeps the install soundness
one-pass (each constructor's reading is taken at the one environment,
and crossed).  The index-threaded twins are
`ConLeche/Kernel/Inductives/SumInstallF.lean`.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- **Official's telescope loop** (`check_inductive_types`,
`inductive.cpp`; task #195): peel `n` Π binders off `e`, reducing the
residual to weak head normal form before each binder and at the end,
where it must be a sort.  Binder `i` is opened at the free variable
`i` (its domain instantiated at the earlier ones, as `openPisAtFvars`
does), so the returned binder domains and the sort are scoped at the
free variables `0 ..< n`.  A residual that does not reduce to a Π, or
finally to a sort, is INVALID input — official fails there too. -/
def whnfTelescope (ops : CheckerOps m) (env : Env) :
    Nat → Nat → Expr → m (List Expr × Level)
  | i, 0, e => do
    let e' ← ops.whnf env i e
    match e' with
    | .sort s => pure ([], s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a sort \
        after its parameters and indices")
  | i, n + 1, e => do
    let e' ← ops.whnf env i e
    match e' with
    | .forallE dom body =>
      let (bs, s) ← whnfTelescope ops env (i + 1) n (body.instantiate1 (.fvar i dom))
      pure (dom :: bs, s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a telescope \
        of its parameters and indices")

/-- The type former's TELESCOPE: `n` Π binders ending in a sort, as it stands.  A block whose
formers do not show theirs is checked at its reducts (`checkBlock`'s second path).  Returns the
former and its sort. -/
def checkSumTele (n : Nat) (cvTa₀ : ConstantVal) : m (ConstantVal × Level) :=
  match cvTa₀.type.stripPis n with
  | some (_, .sort s) => pure (cvTa₀, s)
  | _ => throw (.invalid "direct sum: type former does not reduce to a sort after its parameters and indices")

/-- The fields' sorts over the opened constructor telescope, with the
official per-field universe bound unless the family is
propositional: at a
`Prop` family with a large eliminator every field must be a
proposition OR one of the residual's index expressions — official's
`elim_only_at_universe_zero` for one constructor (the subsingleton-
elimination criterion, `Eq`'s rule; `inductive.cpp`).  A block with
two or more constructors has its large eliminator rejected by
the recursor stage's elimination guard (`blockLargeElimAllowed`).  Walks the fields from
the last to the first and returns the sorts in field order. -/
def checkStructFieldSortsI (ops : CheckerOps m) (env : Env) (isProp large : Bool)
    (s : Level) (nP : Nat) (fvs idxArgs : List Expr) : Nat → m (List Level)
  | 0 => pure []
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct sum: field index")
    let ty ← ops.inferType env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort env (nP + j) ty
    if !isProp then
      unless ← liftFueled "level comparison" (Level.leq u s) do
        throw (.invalid "direct sum: field universe too large")
    else if large then
      unless Level.isEquiv u .zero == some true || idxArgs.contains fv do
        throw (.invalid "direct sum: large eliminator with a non-propositional \
          field outside the indices")
    let rest ← checkStructFieldSortsI ops env isProp large s nP fvs idxArgs j
    pure (rest ++ [u])

/-- Stage 2, one constructor's type: the ordinary constant check (the
constructor is stored AS DECLARED), the result
shape (the family at the parameters followed by
`nIdx` index expressions), the parameter pins against the type
former's opened telescope, the pre-block resolution of the field
domains, and the per-field universe bound (`env₀` is the pre-block environment,
`env` the one holding the type former).  Every constructor is checked
at the environment holding the type former alone — the constructors do
not mention each other — and the block conses them afterwards
(`consBlockCtors`).  Returns the checked constructor and its fields'
sorts (the projection table's guard levels at a structure-like member
are computed from them). -/
def checkSumCtor (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m (ConstantVal × List Level) := do
  checkConstantVal ops env cvC
  let cvCa := cvC
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (nP + nF))
    (.notImplemented "direct sum: constructor telescope")
  -- official's `is_valid_ind_app` on the constructor's result
  -- ("invalid return type for 'C'", `check_constructors`): a REJECT,
  -- not a decline (task #220) — the head must be the block at its own
  -- level parameters, applied to exactly the parameters and `nIdx`
  -- further arguments
  unless structCtorResidOk T lps nP nF nIdx cbody do
    throw (.invalid "direct sum: invalid constructor return type")
  let cq ← unwrapOr (openPisAtFvars nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (openPisAtFvars nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkStructDomsAt ops env 0 cq.1 (tq.1.map Expr.fvarTypeD) nP
  let xq ← unwrapOr (openPisAtFvars nF cq.2 nP)
    (.notImplemented "direct sum: constructor field telescope")
  -- the opened residual is the family at the opened parameter
  -- variables followed by the index expressions
  unless xq.2.getAppFn == Expr.const T (lps.map .param) &&
      xq.2.getAppArgs.take nP == cq.1 && xq.2.getAppArgs.length == nP + nIdx do
    throw (.notImplemented "direct sum: opened constructor residual")
  unless xq.1.all fun x => x.fvarTypeD.constsResolve env₀ do
    throw (.notImplemented "direct sum: field domain after the block")
  -- the index expressions never mention the block (official
  -- `is_valid_ind_app`: no inductive occurrence in an index argument)
  unless (xq.2.getAppArgs.drop nP).all fun e => e.constsResolve env₀ do
    throw (.invalid "direct sum: index expression mentions the block")
  let sorts ← checkStructFieldSortsI ops env isProp large resSort nP xq.1
    (xq.2.getAppArgs.drop nP) nF
  pure (cvCa, sorts)

/-- Stage 2, all constructors' types, at the environment holding the
type former; returns the checked constructors with their field
counts, and beside them the constructors' field sorts. -/
def checkSumCtors (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    List (ConstantVal × Nat) → m (List (ConstantVal × Nat) × List (List Level))
  | [] => pure ([], [])
  | c :: cs => do
    let (cvCa, sorts) ← checkSumCtor ops env₀ env T lps nP nIdx resSort isProp large c.1 c.2
      cvTa
    let (rest, srest) ← checkSumCtors ops env₀ env T lps nP nIdx resSort isProp large cvTa
      cs
    pure ((cvCa, c.2) :: rest, sorts :: srest)

/-- The constructors' conses, in order (the first constructor deepest). -/
def consSumCtors (nP : Nat) : List (ConstantVal × Nat) → Env → Env
  | [], env => env
  | c :: cs, env => consSumCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts, env.tables⟩

/-- The stored rules: constructor `j`'s with the generated right-hand
side `j`, `.plain` (the major is the family at the recursor's
parameters). -/
def sumRules : List (ConstantVal × Nat) → List Expr → List RecRule
  | c :: cs, rhs :: rhss =>
    { ctor := c.1.name, nfields := c.2, fire := .plain, rhs := rhs } :: sumRules cs rhss
  | _, _ => []

end ConLeche
