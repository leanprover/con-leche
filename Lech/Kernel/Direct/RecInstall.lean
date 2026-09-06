import Lech.Kernel.Direct.SumInstall
import Lech.Kernel.Direct.RecParts

/-!
# The direct recursive install (pure fueled checker; task #188)

The install stages of a block recognised by `directFixParts?`
(`Lech/Kernel/Direct/RecParts.lean`).  The former's and the
constructors' stages are the sum route's, verbatim
(`checkDirectSumInd`, `checkDirectSumCtors`): the constructors are
checked at the environment holding the former, with the pre-block
resolution guard pointed at THAT environment so that the recursive
fields `T p⃗` pass it; what the sum route's guard bought — no field
domain mentions the block — is replaced by the positivity
classification, re-checked on the annotated types after the stage
(`directFixFieldsOk`: every field is ordinary, resolving in the
pre-block environment, or exactly the family at the parameters).
The recursor stage generates the type with the inductive-hypothesis
binders (`directRecTyR`), compares it with the stream's by one closed
`isDefEq` (task #175 S2), and generates the rules (`directRecRhsR`);
the rules mention the recursor itself, so they are scope-checked at
the environment holding its constant and NOT inferred — the official
kernel infers no rule either; the P tier grades the generated form
from the leaf's own laws.

Front guards, in the official kernel's order: positivity (a
non-positive occurrence is `.invalid`, an unsupported positive one
`.notImplemented`), the elimination restriction
(`elim_only_at_universe_zero`: a large eliminator on a block whose
sort may be `Prop` is `.invalid` at two or more constructors; at one
constructor it is positively DECLINED here — the recursive squash
regime's large eliminator is the fixed-point equation on the proof
point, not modeled yet — see DESIGN.md, task #188), the constructors'
distinct names.  The index-threaded twins are
`Lech/Kernel/Direct/RecInstallF.lean`.
-/

namespace Lech

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- Does the variable `q` occur as a leaf of `e` (annotations
included, as `fvarLeaves` walks them)? -/
def Expr.mentionsFvar (q : Nat) (e : Expr) : Bool := e.fvarLeaves.any fun l => l.1 == q

/-- The kinds the recogniser computed, re-checked on the annotated
constructor type OPENED at variables (`openPisAtFvars`, as the stage
read it): an ordinary field's domain resolves in the pre-block
environment `env₀`; a recursive field's domain is the family at the
opened parameter variables followed by `nIdx` index expressions
resolving in `env₀`, and the variable occurs in no later field's
domain nor in the residual (the model reads those at a frame whose
recursive slots hold an arbitrary member of the family being defined);
the residual's index expressions resolve in `env₀`. -/
def directFixOpenedOk (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (cty : Expr) (nF : Nat) (ks : List RecFieldKind) : Bool :=
  match openPisAtFvars nP cty 0 with
  | some (fvsP, crest) =>
    match openPisAtFvars nF crest nP with
    | some (xFvs, xrest) =>
      (xrest.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
      (List.range nF).all fun i =>
        match xFvs[i]?, ks.getD i .ordinary with
        | some x, .ordinary => x.fvarTypeD.constsResolve env₀
        | some x, .recursive =>
          x.fvarTypeD.getAppFn == Expr.const T (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdx &&
          (x.fvarTypeD.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | _, _ => false
    | none => false
  | none => false

/-- The kinds, re-checked on every annotated constructor
(`directFixOpenedOk`), one kind list per constructor, one kind per
field. -/
def directFixFieldsOk (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) : Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 && directFixOpenedOk env₀ T lps nP nIdx cA.1.type cA.2 ks
    | _, _ => false

/-- The generated rules for constructors `j, j+1, …` (`k` of them),
each scoped at the environment holding the recursor's constant
(`envR`): a rule mentions the recursor and is not inferred. -/
def checkDirectFixRules (envR : Env) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (directRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless rhs.allLevelParamsDefined rlps && rhs.constsResolve envR &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct rec: recursor rule scoping")
    let rest ← checkDirectFixRules envR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- Stage 3: the recursor, generated and compared — the generated
type has the inductive-hypothesis binders in each minor
(`directRecTyR`); the generated rules are scoped at the environment
holding the recursor's constant. -/
def checkDirectFixRec (ops : CheckerOps m) (env : Env) (p : DirectFixParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  let cvRi ← checkConstantVal ops env p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := directFixCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (directRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && recTy.constsResolve env &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct rec: recursor type scoping")
  let sty ← ops.inferType env 0 recTy
  let _u ← ops.ensureSort env 0 sty
  -- the stream's recursor is the generated one
  unless ← ops.isDefEq env 0 cvRi.type recTy do
    throw (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : ConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let envR : Env := ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: env.consts⟩
  let rhss ← checkDirectFixRules envR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name (p.cvR.levelParams.map .param) ctors.length 0
  pure (cvRa, rhss)

/-- Check and install a **direct recursive block**: positivity, the
elimination restriction, the distinct names, the former, the
constructors (at the former's environment), the kinds re-checked, the
recursor with its rules. -/
def checkDirectFix (ops : CheckerOps m) (env : Env) (p : DirectFixParts) : m Env := do
  if p.kinds.any (fun ks => ks.any (· == .negative)) then
    throw (.invalid "direct rec: non positive occurrence of the inductive type")
  if p.large && !p.resSort.isNeverZero then
    if decide (2 ≤ p.ctors.length) then
      throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
        whose sort may be Prop")
    else
      throw (.notImplemented "direct rec: large eliminator on a recursive inductive \
        whose sort may be Prop")
  unless (p.ctors.map (·.1.name)).Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  let (env₁, cvTa) ← checkDirectSumInd ops env p.toDirectSumParts
  -- the index binders' universes, exposed for the model's index-tuple
  -- universe: the former's telescope opened at variables, each index
  -- domain's sort inferred (no bound is checked — `isProp` set,
  -- `large` unset — the sorts are read, not compared)
  let tq ← unwrapOr (openPisAtFvars (p.nP + p.nIdx) cvTa.type 0)
    (.internal "direct rec: type former telescope")
  let _isorts ← checkDirectFieldSortsI ops env₁ true false p.resSort p.nP (tq.1.drop p.nP) []
    p.nIdx
  -- the constructors' field domains may mention the block: the
  -- resolution guard is pointed at the former's environment, and the
  -- kinds are re-checked afterwards
  let ctorsA ← checkDirectSumCtors ops env₁ env₁ p.cvT.name p.cvT.levelParams p.nP p.nIdx
    p.resSort p.isProp p.large cvTa p.ctors
  unless directFixFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds do
    throw (.internal "direct rec: field kinds")
  let env₂ := consSumCtors p.nP ctorsA env₁
  let (cvRa, rhss) ← checkDirectFixRec ops env₂ p cvTa ctorsA
  pure ⟨.recInfo cvRa p.majorIdx p.rulePrefix
    (directSumRules p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss) :: env₂.consts⟩

end Lech
