module

public import ConLeche.Kernel.Inductives.GenRec

@[expose] public section

/-!
# The inductive installer's pass and tail

`checkBlock` (the installer's entry, dispatched from `checkDecl`):
the pass (the formers and the constructors, `BlockInstall.lean`; the
classes the stream's recursor family eliminates, `checkBlockClasses`;
the positivity check walking every class), and the stages after it: the index sorts,
the constructors consed, the recursor stage —
the generated recursors (`genRecCheck`, `GenRec.lean`, charter item 5)
— the recursors consed and the projection tables.  Its own module because the check is
written over the index (`FEnv`), whose operations sit above the pure
checker's stages.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- **What one pass over the formers, the constructors and the classes
yields**. -/
structure BlockPass (E : Type) where
  /-- the environment holding all k formers, at the record the pass ran at -/
  env₁ : E
  /-- the annotated formers, in block order -/
  cvTas : List ConstantVal
  /-- the completed record: the sort read -/
  p : BlockParts
  /-- the annotated constructors, per member, AS DECLARED -/
  ctorsAs : List (List (ConstantVal × Nat))
  /-- the fields' sorts, per member, per constructor -/
  sortsss : List (List (List Level))
  /-- the positivity function's field kinds, per member, per constructor -/
  kinds : List (List (List NestFieldKind))
  /-- the positivity function's normal forms, per member, per constructor
  (member-abstracted at the walk's context) -/
  nfs : List (List Expr)
  /-- the block's canonical parameter variables (the walk's, the classes') -/
  params : List Expr
  /-- [UNVERIFIED] the pre-pass's reading of the stream's recursor types -/
  rd : ClassRead
  /-- the classes the stream's recursor family eliminates, each checked as a
  major -/
  cls : List TargetMajor
  /-- the positivity check's TABLE: every walked node's constructors,
  normalised and read back (`NestCtorNf`); installer-local, never stored -/
  tbl : Array NestCtorNf

/-- **One pass over the formers, the constructors and the classes** at
the block's `is_rec` verdict (`blockRawRec`, known before any constructor
is looked at, as official's `declare_inductive_types` stores it): the
formers, the constructors, the classes (`checkBlockClasses`: read off the
stream's raw recursor types, each checked as a major), and the positivity
check as ONE walk: every class from the empty frame stack, the members
first (the ROOT frame, `checkBlockPositivity`, with its own lines), then
every outside class (`nestSeeds`: a cache hit, or its frame walked). -/
def checkBlockPass (ops : CheckerOps m) (env : Env) (p₀ : BlockParts) (isRec : Bool) :
    m (BlockPass Env) := do
  let (env₁, cvTas, p₁) ← checkBlockInds ops env p₀ isRec
  let pC := p₀.complete p₁
  let (ctorsAs, sortsss) ← checkBlockCtors ops env₁ env₁ pC.toBlockShape
    (pC.members.zip cvTas)
  let (ctx, holes) ← blockNestCtx pC.toBlockShape cvTas env₁.find?
  -- the classes
  let (rd, Ms) ← checkBlockClasses ops (mkFEnv env₁) env₁ pC.toBlockShape ctx.params ctorsAs
  -- positivity: every class from the empty stack, the members (the root frame) first
  let (kinds, nfs, pos) ← checkBlockPositivity ops env₁ env₁.find? pC cvTas ctorsAs
  let st ← nestSeeds ops env₁ ctx (classSeeds ctx holes Ms) pos
  pure ⟨env₁, cvTas, pC, ctorsAs, sortsss, kinds, nfs, ctx.params, rd, Ms, st.ctorNfs⟩

/-- **The installer's recursor stage** (charter item 5): the
GENERATED recursor stage `genRecCheck` (`GenRec.lean`) at the
constructors' environment `env`, on the stream's own recursor family
(the raw `block`: the pins read it), the pass's classes and table, and
the elimination guard's container bit `nested` (`blockNestedBit`).
Returns every generated recursor with its class and its generated rules
(`tgtRs` is the install's recursor-list format of it).  The pure
operations run it at every index (`ShadowOps.ofOps`); the cached driver
runs the SAME function at its own shadow operations (`checkBlockTailS`,
`ConLeche/Cached/CheckerC.lean`). -/
def checkBlockRec (ops : CheckerOps m) (env : Env) (p : BlockParts) (nested : Bool)
    (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor)
    (block : List ConstantInfo) (cvTas : List ConstantVal) :
    m (List (ConstantVal × TargetMajor × List Expr)) :=
  genRecCheck (ShadowOps.ofOps ops) (mkFEnv env) p.toBlockShape nested params tbl rd Ms
    cvTas block

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

/-- **The install after the pass**: the
index binders' sorts, the constructors consed,
the recursor stage, the recursors consed at their majors, and the
projection tables. -/
def checkBlockTail (ops : CheckerOps m) (block : List ConstantInfo)
    (q : BlockPass Env) : m Env := do
  let p := q.p
  let _isorts ← checkBlockIdxSorts ops q.env₁ p.toBlockShape (p.members.zip q.cvTas)
  let env₂ := consBlockCtors p.nP q.ctorsAs q.env₁
  let out ← checkBlockRec ops env₂ p (blockNestedBit p.toBlockShape q.kinds) q.params
    q.tbl.toList q.rd q.cls block q.cvTas
  let env₃ := consBlockRecsT env₂.find? (·.constsResolve env₂) p.toBlockShape 0 out env₂
  checkBlockTables p.toBlockShape
    (p.members.zip (q.ctorsAs.zip q.sortsss)) env₃

/-- Check and install an inductive block: the distinct
names, the pass over the formers, the constructors and the classes at official's
`is_rec` (`blockRawRec`), and the install after it. -/
def checkBlock (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) (p₀ : BlockParts) :
    m Env := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  let q ← checkBlockPass ops env p₀ (blockRawRec p₀)
  checkBlockTail ops block q


end ConLeche
