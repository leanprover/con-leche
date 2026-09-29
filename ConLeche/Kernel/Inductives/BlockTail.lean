module

public import ConLeche.Kernel.Inductives.GenRec

@[expose] public section

/-!
# The uniform install's tail: the recursor stage and the install after the pass

`checkBlock` (the uniform route's entry, dispatched from `checkDecl`)
and the stages after the pass over the formers and the constructors
(`BlockInstall.lean`): the elimination restriction, the index sorts,
the constructors consed, the recursor stage —
the generated recursors (`genRecCheck`, `GenRec.lean`, charter item 5)
— the recursors consed and the projection tables.  Its own module because the check is
written over the index (`FEnv`), whose operations sit above the pure
checker's stages.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- **The recursor stage on the uniform route** (charter item 5): the
GENERATED recursor stage `genRecCheck` (`GenRec.lean`) at the
constructors' environment `env`, on the stream's own recursor family
(the raw `block`: the pins read it), its classes' seeds walked by the
positivity check at the formers' environment `env₁` (its state `pos`
after the root frame), and the elimination guard's container bit
`nested` (`blockNestedBit`).  Returns every generated recursor with its
class and its generated rules (`tgtRs` is the install's recursor-list
format of it).  The pure operations run it at every index
(`ShadowOps.ofOps`); the cached driver runs the SAME function at its own
shadow operations (`checkBlockTailS`, `ConLeche/Cached/CheckerC.lean`). -/
def checkBlockRec (ops : CheckerOps m) (env₁ env : Env) (p : BlockParts) (nested : Bool)
    (pos : NestState)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × TargetMajor × List Expr)) :=
  genRecCheck (ShadowOps.ofOps ops) (mkFEnv env₁) env₁ (mkFEnv env) p.toBlockShape nested
    pos cvTas block ctorsAs

/-- **The checked family consed, at its majors**: each
recursor with its rules at ITS major (`tgtStoredRules`: the major's
parameter count and constructors; `.nested` at an outside major).  At
member majors it is `consBlockRecs`.
`resolves` is the constructors' environment's resolution test (the
`.nested` pins' guard). -/
def consBlockRecsT (find? : Name → Option ConstantInfo) (resolves : Expr → Bool)
    (p : BlockShape) : Nat → List (ConstantVal × TargetMajor × List Expr) → Env → Env
  | _, [], env => env
  | m, (cv, M, rhss) :: rest, env =>
    consBlockRecsT find? resolves p (m + 1) rest
      ⟨.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m)
        (tgtStoredRules find? resolves cv (p.majorIdxAt m) (p.rulePrefixAt m) M rhss)
        :: env.consts⟩

/-- **The projection table at every STRUCTURE-LIKE member** (one
constructor, no index): the member's table at the tagged tower's
projection offset `1`; nothing at any other member. -/
def checkBlockTables (p : BlockShape) :
    List (MemberShape × List (ConstantVal × Nat) × List (List Level)) → Env → m Env
  | [], env => pure env
  | (ms, ctorsA, sortss) :: rest, env => do
    let env' ←
      (match ctorsA, sortss with
       | [cA], [sorts] =>
         if ms.nIdx == 0 then
           checkStructProjTable ms.cvT.name cA.1.name p.lps p.nP cA.2 p.resSort
             (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 env
         else pure env
       | _, _ => pure env)
    checkBlockTables p rest env'

/-- **The install after the pass**: the elimination restriction, the
index binders' sorts, the constructors consed,
the recursor stage, the recursors consed at their majors, and the
projection tables. -/
def checkBlockTail (ops : CheckerOps m) (block : List ConstantInfo)
    (q : BlockPass Env) : m Env := do
  let p := q.p
  -- **the elimination restriction** (official `elim_only_at_universe_zero`,
  -- `inductive.cpp`): a large eliminator on a block whose sort may be
  -- `Prop` needs ONE member with at most one constructor — official
  -- returns `true` (eliminate into `Prop` only) as soon as
  -- `m_ind_types.size() > 1` or `num_intros > 1`; the one-constructor
  -- case is the subsingleton criterion, taken per field at
  -- `checkStructFieldSortsI`
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.k ∨ 2 ≤ p.numCtors) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  let _isorts ← checkBlockIdxSorts ops q.env₁ p.toBlockShape (p.members.zip q.cvTas)
  let env₂ := consBlockCtors p.nP q.ctorsAs q.env₁
  let out ← checkBlockRec ops q.env₁ env₂ p (blockNestedBit p.toBlockShape q.kinds) q.pos
    block q.cvTas q.ctorsAs
  let env₃ := consBlockRecsT env₂.find? (·.constsResolve env₂) p.toBlockShape 0 out env₂
  checkBlockTables p.toBlockShape
    (p.members.zip (q.ctorsAs.zip q.sortsss)) env₃

/-- Check and install a block on the uniform route: the distinct
names, the pass over the formers and the constructors at official's
`is_rec` (`blockRawRec`), and the install after it. -/
def checkBlock (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) (p₀ : BlockParts) :
    m Env := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  let q ← checkBlockPass ops env p₀ (blockRawRec p₀)
  checkBlockTail ops block q


end ConLeche
