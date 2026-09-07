import ConLeche.Kernel.Direct.Install
import ConLeche.Kernel.Direct.SumParts

/-!
# The direct sum install (pure fueled checker; task #175 sum-types, indexed)

The install stages of a block recognised by `directSumParts?`
(`ConLeche/Kernel/Direct/SumParts.lean`): the type former, one
constructor stage per constructor, the recursor generated and compared
with one minor premise and one rule per constructor.  No projection
table, no eta, no unit-likeness — a sum has no structure-like
capability (the official kernel's `is_structure_like` needs one
constructor and no index); the former is stored with the capability
record `directSumCaps` (only `ruleK`, official's `is_K_target`: a
`Prop` family with one constructor taking only the parameters — `Eq`'s
shape) and the recursor's rules are the block's only definitional
content.

The per-constructor stage is `checkDirectCtor` with the constructor
made explicit (the direct structure route's stage reads it off its
`DirectParts`) and the residual widened to the family at the
parameters followed by `nIdx` index expressions; the field-sort walk
(`checkDirectFieldSortsI`) carries official's subsingleton-elimination
criterion for a large eliminator at a `Prop` family with one
constructor (a field that is not a proposition must be one of the
index expressions); the domain pins are shared (`checkDirectDomsAt`).
Every constructor's type is checked at the environment holding the
type former alone and the constructors are consed afterwards: they
never mention each other, and this order keeps the install soundness
one-pass (each constructor's reading is taken at the one environment,
and crossed).  The index-threaded twins are
`ConLeche/Kernel/Direct/SumInstallF.lean`.
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
    Nat → Nat → Expr → m (List (Expr × BinderMeta) × Level)
  | i, 0, e => do
    let e' ← ops.whnf env i e
    match e' with
    | .sort s => pure ([], s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a sort \
        after its parameters and indices")
  | i, n + 1, e => do
    let e' ← ops.whnf env i e
    match e' with
    | .forallE dom body bm =>
      let (bs, s) ← whnfTelescope ops env (i + 1) n (body.instantiate1 (.fvar i dom))
      pure ((dom, bm) :: bs, s)
    | _ => throw (.invalid "direct sum: type former does not reduce to a telescope \
        of its parameters and indices")

/-- Close a telescope opened at the free variables `i ..< i + bs.length`
back into a syntactic Π-telescope over `body`: innermost binder first,
each abstraction turning the binder's own free variable into the bound
one (`abstract1`; the domains of the inner binders are closed by the
outer abstractions, which descend into binder domains). -/
def closeTelescope : List (Expr × BinderMeta) → Nat → Expr → Expr
  | [], _, body => body
  | (dom, bm) :: bs, i, body =>
    .forallE dom ((closeTelescope bs (i + 1) body).abstract1 i 0) bm

/-- The type former's TELESCOPE (task #195): the checked declared type
when it is already a syntactic telescope of `n` Π binders ending in a
sort, else the declared type's whnf'd telescope (`whnfTelescope`),
closed and checked as the former's type in its place —
`checkConstantVal` from scratch, so nothing about the reduction is
trusted: the stored type is the one this run annotated, inferred and
sorted.  Returns the checked constant and the result sort. -/
def checkDirectSumTele (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (n : Nat)
    (cvTa₀ : ConstantVal) : m (ConstantVal × Level) :=
  match cvTa₀.type.stripPis n with
  | some (_, .sort s) => pure (cvTa₀, s)
  | _ => do
    let (bs, s) ← whnfTelescope ops env 0 n cvTa₀.type
    let cvTa ← checkConstantVal ops env { cv with type := closeTelescope bs 0 (.sort s) }
    pure (cvTa, s)

/-- Stage 1: the type former, stored with the block's capability
record — `capsOf` at the completed record: `directSumCaps` on the sum
route, `directFixCaps` on the fixpoint route (task #210 Part A) — at
its telescope (`checkDirectSumTele`); returns the record completed
with the result sort (`DirectSumParts.withSort`), which every later
stage runs on. -/
def checkDirectSumInd (ops : CheckerOps m) (env : Env) (p : DirectSumParts)
    (capsOf : DirectSumParts → IndCaps) :
    m (Env × ConstantVal × DirectSumParts) := do
  let cvTa₀ ← checkConstantVal ops env p.cvT
  let (cvTa, s) ← checkDirectSumTele ops env p.cvT (p.nP + p.nIdx) cvTa₀
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis (p.nP + p.nIdx))
    (.internal "direct sum: type former telescope")
  unless tbody == Expr.sort s do
    throw (.internal "direct sum: type former result sort")
  let p' := p.withSort s
  pure (⟨.indInfo cvTa (capsOf p') :: env.consts⟩, cvTa, p')

/-- The fields' sorts over the opened constructor telescope, with the
official per-field universe bound unless the family is
propositional (`checkDirectFieldSorts` at an indexed family): at a
`Prop` family with a large eliminator every field must be a
proposition OR one of the residual's index expressions — official's
`elim_only_at_universe_zero` for one constructor (the subsingleton-
elimination criterion, `Eq`'s rule; `inductive.cpp`).  A block with
two or more constructors never reaches this walk with a large
eliminator (`checkDirectSum`'s front guard).  Walks the fields from
the last to the first and returns the sorts in field order. -/
def checkDirectFieldSortsI (ops : CheckerOps m) (env : Env) (isProp large : Bool)
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
    let rest ← checkDirectFieldSortsI ops env isProp large s nP fvs idxArgs j
    pure (rest ++ [u])

/-- Stage 2, one constructor's type: the ordinary constant check, the
annotated result shape (the family at the parameters followed by
`nIdx` index expressions), the parameter pins against the type
former's opened telescope, the pre-block resolution of the field
domains, and the per-field universe bound (`checkDirectCtor`, the
constructor made explicit; `env₀` is the pre-block environment, `env`
the one holding the type former).  Every constructor is checked at
the environment holding the type former alone — the constructors do
not mention each other — and the block conses them afterwards
(`checkDirectSum`).  Returns the annotated constructor and its fields'
sorts (task #210 Part A: the projection table's guard levels at a
structure-like block on the fixpoint route are computed from them). -/
def checkDirectSumCtor (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m (ConstantVal × List Level) := do
  let cvCa ← checkConstantVal ops env cvC
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (nP + nF))
    (.notImplemented "direct sum: constructor telescope")
  unless directCtorResidOk T lps nP nF nIdx cbody do
    throw (.notImplemented "direct sum: constructor result")
  let cq ← unwrapOr (openPisAtFvars nP cvCa.type 0)
    (.notImplemented "direct sum: constructor telescope")
  let tq ← unwrapOr (openPisAtFvars nP cvTa.type 0)
    (.notImplemented "direct sum: type former telescope")
  checkDirectDomsAt ops env 0 cq.1 (tq.1.map Expr.fvarTypeD) nP
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
  let sorts ← checkDirectFieldSortsI ops env isProp large resSort nP xq.1
    (xq.2.getAppArgs.drop nP) nF
  pure (cvCa, sorts)

/-- Stage 2, all constructors' types, at the environment holding the
type former; returns the annotated constructors with their field
counts, and beside them the constructors' field sorts. -/
def checkDirectSumCtors (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal) :
    List (ConstantVal × Nat) → m (List (ConstantVal × Nat) × List (List Level))
  | [] => pure ([], [])
  | c :: cs => do
    let (cvCa, sorts) ← checkDirectSumCtor ops env₀ env T lps nP nIdx resSort isProp large c.1 c.2
      cvTa
    let (rest, srest) ← checkDirectSumCtors ops env₀ env T lps nP nIdx resSort isProp large cvTa cs
    pure ((cvCa, c.2) :: rest, sorts :: srest)

/-- The constructors' conses, in order (the first constructor deepest). -/
def consSumCtors (nP : Nat) : List (ConstantVal × Nat) → Env → Env
  | [], env => env
  | c :: cs, env => consSumCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩

/-- The stored rules: constructor `j`'s with the generated right-hand
side `j`, plain when the generated type's major is the family at the
parameters (always, by construction). -/
def directSumRules (nP mI rP : Nat) (recTy : Expr) :
    List (ConstantVal × Nat) → List Expr → List RecRule
  | c :: cs, rhs :: rhss =>
    ⟨c.1.name, c.2, nP,
      if Expr.recRulePlain recTy mI rP nP then .plain else .inert, rhs⟩
      :: directSumRules nP mI rP recTy cs rhss
  | _, _ => []

/-- The recursor's rule prefix (parameters, motive, minors) and its
major index (the rule prefix, then the indices). -/
def DirectSumParts.rulePrefix (p : DirectSumParts) : Nat := p.nP + 1 + p.ctors.length
def DirectSumParts.majorIdx (p : DirectSumParts) : Nat := p.rulePrefix + p.nIdx

@[simp] theorem DirectSumParts.withSort_rulePrefix (p : DirectSumParts) (s : Level) :
    (p.withSort s).rulePrefix = p.rulePrefix := rfl
@[simp] theorem DirectSumParts.withSort_majorIdx (p : DirectSumParts) (s : Level) :
    (p.withSort s).majorIdx = p.majorIdx := rfl

end ConLeche
