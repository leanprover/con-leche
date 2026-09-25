module

public import ConLeche.Kernel.Inductives.RecCheck

@[expose] public section

/-!
# The uniform install's tail: the recursor CHECK and the install after the pass

`checkBlock` (the uniform route's entry, dispatched from `checkDecl`)
and the stages after the pass over the formers and the constructors
(`BlockInstall.lean`): the elimination restriction, the index sorts,
the constructors consed, the recursor stage —
the classification-free `targetRecCheck` (`RecCheck.lean`, charter
item 5) followed by the reject-only conformance check — the recursors
consed and the projection tables.  Its own module because the check is
written over the index (`FEnv`), whose operations sit above the pure
checker's stages.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- **The recursor CHECK on the uniform route** (charter item 5):
`targetRecCheck` — primitive recursion, classification-free — at the
constructors' environment, on the stream's own recursor family (the
raw `block`: the pins read it), with outside majors admitted exactly
when the route switch is on (`nst`; the dispatch passes `true`) and the
elimination guard's container bit `nested` (`blockNestedBit`, off with
the switch).  Returns the check's output: every recursor with its
resolved major and its annotated rules (`tgtRs` is the install's
recursor-list format of it).  The pure operations run it at every
index (`ShadowOps.ofOps`); the cached driver runs the SAME function at
its own shadow operations (`checkBlockRecS`,
`ConLeche/Cached/CheckerC.lean`). -/
def checkBlockRecT (ops : CheckerOps m) (env : Env) (p : BlockParts) (nst nested : Bool)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × TargetMajor × List Expr)) :=
  targetRecCheck (ShadowOps.ofOps ops) (mkFEnv env) p.toBlockShape nst nested block
    cvTas ctorsAs

/-- **The recursor stage**: the CHECK (`checkBlockRecT`, primitive
recursion) at every `k`, on the constructors as declared (`ctorsAs`),
then — where every field kind is flat (`conf`: the generator has no
container arm, NESTPLAN Q-F) — the reject-only conformance check
(`checkBlockRecConform`) on the constructors at their positivity normal
forms (`ctorsN`, `blockNormalCtors`), returning the check's result
unchanged (`thenConform`). -/
def checkBlockRec (ops : CheckerOps m) (env : Env) (p : BlockParts) (nst nested conf : Bool)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs ctorsN : List (List (ConstantVal × Nat))) :
    m (List (ConstantVal × TargetMajor × List Expr)) :=
  thenConform (checkBlockRecT ops env p nst nested block cvTas ctorsAs)
    (if conf then checkBlockRecConform ops env p cvTas ctorsN else pure ())

/-- **The checked family consed, at its majors** (lane NESTKERN): each
recursor with its rules at ITS major (`tgtStoredRules`: the major's
parameter count and constructors; `.nested` at an outside major).  At
member majors it is `consBlockRecs` (`consBlockRecsT_member`).
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
projection tables.  `nst` is the route switch (`true` at the dispatch). -/
def checkBlockTail (ops : CheckerOps m) (block : List ConstantInfo)
    (q : BlockPass Env) (nst : Bool := false) : m Env := do
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
  let out ← checkBlockRec ops env₂ p nst (nst && blockNestedBit p.toBlockShape q.kinds)
    (nestKindsFlat q.kinds) block q.cvTas q.ctorsAs
    (blockNormalCtors p.toBlockShape q.ctorsAs q.nfs)
  let env₃ := consBlockRecsT env₂.find? (·.constsResolve env₂) p.toBlockShape 0 out env₂
  checkBlockTables p.toBlockShape
    (p.members.zip (q.ctorsAs.zip q.sortsss)) env₃

/-- Check and install a block on the uniform route: the distinct
names, the pass over the formers and the constructors — again where
the capability record's syntactic reading overshot (task #268) — and
the install after it.  `nst` is the route switch: the dispatch hands it
`true` (`checkDecl`); `false` survives in the switch-off statements of
the proofs only. -/
def checkBlock (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) (p₀ : BlockParts)
    (nst : Bool := false) : m Env := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  let (q, settled) ← checkBlockPass ops env p₀ (blockRawRec p₀) nst
  if settled then checkBlockTail ops block q nst
  else do
    let (q', settled') ← checkBlockPass ops env p₀ (nestIsRec q.kinds) nst
    unless settled' do
      throw (.internal "direct rec: the capability record did not settle")
    checkBlockTail ops block q' nst


end ConLeche
