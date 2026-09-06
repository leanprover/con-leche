import Setlec.Kernel.Direct.Install
import Setlec.Kernel.Direct.SumParts

/-!
# The direct sum install (pure fueled checker; task #175 sum-types, indexed)

The install stages of a block recognised by `directSumParts?`
(`Setlec/Kernel/Direct/SumParts.lean`): the type former, one
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
`Setlec/Kernel/Direct/SumInstallF.lean`.
-/

namespace Setlec

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- The capabilities a direct sum block earns: `ruleK` exactly at
official's `is_K_target` — a `Prop` result, one constructor, no
fields (task #175 indexed; at a plain sum the constructor count is
never one, so the record is empty). -/
def directSumCaps (p : DirectSumParts) : IndCaps where
  ruleK := p.ctors.length == 1 && p.ctors.all (fun c => c.2 == 0) && p.isProp

/-- Stage 1: the type former, stored with the block's capability
record (`directSumCaps`). -/
def checkDirectSumInd (ops : CheckerOps m) (env : Env) (p : DirectSumParts) :
    m (Env × ConstantVal) := do
  let cvTa ← checkConstantVal ops env p.cvT
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis (p.nP + p.nIdx))
    (.notImplemented "direct sum: type former telescope")
  unless tbody == Expr.sort p.resSort do
    throw (.notImplemented "direct sum: type former result sort")
  pure (⟨.indInfo cvTa (directSumCaps p) :: env.consts⟩, cvTa)

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
(`checkDirectSum`). -/
def checkDirectSumCtor (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) : m ConstantVal := do
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
  let _sorts ← checkDirectFieldSortsI ops env isProp large resSort nP xq.1
    (xq.2.getAppArgs.drop nP) nF
  pure cvCa

/-- Stage 2, all constructors' types, at the environment holding the
type former; returns the annotated constructors with their field
counts. -/
def checkDirectSumCtors (ops : CheckerOps m) (env₀ env : Env) (T : Name)
    (lps : List Name) (nP nIdx : Nat) (resSort : Level) (isProp large : Bool)
    (cvTa : ConstantVal) : List (ConstantVal × Nat) → m (List (ConstantVal × Nat))
  | [] => pure []
  | c :: cs => do
    let cvCa ← checkDirectSumCtor ops env₀ env T lps nP nIdx resSort isProp large c.1 c.2 cvTa
    let rest ← checkDirectSumCtors ops env₀ env T lps nP nIdx resSort isProp large cvTa cs
    pure ((cvCa, c.2) :: rest)

/-- The constructors' conses, in order (the first constructor deepest). -/
def consSumCtors (nP : Nat) : List (ConstantVal × Nat) → Env → Env
  | [], env => env
  | c :: cs, env => consSumCtors nP cs ⟨.ctorInfo c.1 nP c.2 :: env.consts⟩

/-- The generated rules for constructors `j, j+1, …` (`k` of them):
each is scoped-checked and inferred (task #175 S2's discipline for the
single rule). -/
def checkDirectSumRules (ops : CheckerOps m) (env : Env) (rlps : List Name)
    (T : Name) (lps : List Name) (elim : Name) (large : Bool) (nP nIdx : Nat)
    (tty : Expr) (ctors : List (Name × Nat × Expr)) : Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (directRecRhsI T lps elim large nP nIdx tty ctors j)
      (.internal "direct sum: recursor rule")
    unless rhs.allLevelParamsDefined rlps && rhs.constsResolve env &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct sum: recursor rule scoping")
    let _rhsTy ← ops.inferType env 0 rhs
    let rest ← checkDirectSumRules ops env rlps T lps elim large nP nIdx tty ctors k (j + 1)
    pure (rhs :: rest)

/-- Stage 3: the recursor, generated and compared (task #175 S2) — the
generated type has one minor premise per constructor and the index
binders after the minors (`directRecTyI`), the generated rules are
one per constructor. -/
def checkDirectSumRec (ops : CheckerOps m) (env : Env) (p : DirectSumParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  let cvRi ← checkConstantVal ops env p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := ctorsA.map fun c => (c.1.name, c.2, c.1.type)
  let recTy ← unwrapOr (directRecTyI T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct sum: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && recTy.constsResolve env &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct sum: recursor type scoping")
  let sty ← ops.inferType env 0 recTy
  let _u ← ops.ensureSort env 0 sty
  -- the stream's recursor is the generated one
  unless ← ops.isDefEq env 0 cvRi.type recTy do
    -- a recognised block's recursor is derived, so a different type is
    -- INVALID input (task #181), not an unsupported shape
    throw (.invalid "direct sum: recursor type is not the generated one")
  let rhss ← checkDirectSumRules ops env p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors ctors.length 0
  pure (⟨p.cvR.name, p.cvR.levelParams, recTy⟩, rhss)

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

/-- Check and install a **direct sum**: the type former, the
constructors, the recursor with its rules.  The elimination
restriction (official `elim_only_at_universe_zero`) is enforced up
front: with two or more constructors and a result sort that is not
provably nonzero, only the small eliminator is admissible (the
one-constructor case is the per-field test in
`checkDirectFieldSortsI`). -/
def checkDirectSum (ops : CheckerOps m) (env : Env) (p : DirectSumParts) : m Env := do
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length) then
    throw (.invalid "direct sum: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  -- the constructors are checked at one environment and consed
  -- afterwards, so their names must be pairwise distinct here
  unless (p.ctors.map (·.1.name)).Nodup do
    throw (.invalid "direct sum: duplicate constructor")
  let (env₁, cvTa) ← checkDirectSumInd ops env p
  let ctorsA ← checkDirectSumCtors ops env env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx
    p.resSort p.isProp p.large cvTa p.ctors
  let env₂ := consSumCtors p.nP ctorsA env₁
  let (cvRa, rhss) ← checkDirectSumRec ops env₂ p cvTa ctorsA
  pure ⟨.recInfo cvRa p.majorIdx p.rulePrefix
    (directSumRules p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss) :: env₂.consts⟩

end Setlec
