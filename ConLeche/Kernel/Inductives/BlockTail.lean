module

public import ConLeche.Kernel.Inductives.GenRec
public import ConLeche.Kernel.Inductives.StreamRecs
public import ConLeche.Kernel.Install

@[expose] public section

/-!
# The inductive block's check

`checkBlock` (dispatched from `checkDecl`): the pass (the formers and the constructors,
`BlockInstall.lean`; the classes the stream's recursor family eliminates, `checkBlockClasses`; the
positivity check walking every class), the stages after it (the index sorts, the generated recursors
of `GenRec.lean`, the stream's recursors against them, the projection tables), and finally the
block's install, which is read off the block (`Kernel/Install.lean`).  Its own module because the
check is written over the index (`FEnv`), whose operations sit above the pure checker's stages.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- **What one pass over the formers, the constructors and the classes
yields**. -/
structure BlockPass (E : Type) where
  /-- the environment holding all k formers, at the record the pass ran at -/
  env₁ : E
  /-- the completed record: the sort read -/
  p : BlockShape
  /-- the positivity function's field kinds, per member, per constructor -/
  kinds : List (List (List NestFieldKind))
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
the block's `is_rec` verdict (`blockIsRec`, known before any constructor
is looked at, as official's `declare_inductive_types` stores it): the
formers, the constructors, the classes (`checkBlockClasses`: read off the
stream's raw recursor types, each checked as a major), and the positivity
check as ONE walk: every class from the empty frame stack, the members
first (the ROOT frame, `checkBlockPositivity`, with its own lines), then
every outside class (`nestSeeds`: a cache hit, or its frame walked). -/
def checkBlockPass (ops : CheckerOps m) (env : Env) (p₀ : BlockShape) (isRec : Bool) :
    m (BlockPass Env) := do
  let (env₁, p₁) ← checkBlockInds ops env p₀ isRec
  checkBlockCtors ops env₁ env₁ p₁ p₁.members
  let (ctx, holes) ← blockNestCtx p₁ env₁.find?
  -- the classes
  let (rd, Ms) ← checkBlockClasses ops (mkFEnv env₁) p₁ ctx.params
  -- positivity: every class from the empty stack, the members (the root frame) first
  let (outs, pos) ← checkBlockPositivity ops env₁ env₁.find? p₁
  let st ← nestSeeds ops env₁ ctx (classSeeds ctx holes Ms) pos
  pure ⟨env₁, p₁, nestOutKinds outs, ctx.params, rd, Ms, st.ctorNfs⟩

/-- **The installer's recursor stage** (charter item 5): the
GENERATED recursor stage `genRecCheck` (`GenRec.lean`) at the
constructors' environment `env`, on the stream's own recursor family
(the raw `block`: the pins read it), the pass's classes and table, and
the elimination guard's container bit `nested` (`blockNestedBit`).
Returns every generated recursor with its class and its generated rules
(`tgtRs` is the check's recursor-list format of it).  The pure
operations run it at every index (`ShadowOps.ofOps`); the cached driver
runs the SAME function at its own shadow operations (`checkBlockTailS`,
`ConLeche/Cached/CheckerC.lean`). -/
def checkBlockRec (ops : CheckerOps m) (env : Env) (p : BlockShape) (nested : Bool)
    (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead) (Ms : List TargetMajor)
    (block : List ConstantInfo) :
    m (List (ConstantVal × TargetMajor × List Expr)) :=
  genRecCheck (ShadowOps.ofOps ops) (mkFEnv env) p nested params tbl rd Ms block

/-- **The checked family consed, at its majors**: each
recursor with its rules at ITS major (`generatedRules`: the major's
parameter count and constructors; `.nested` at an outside major).  At
member majors it is `consBlockRecs`. -/
def consBlockRecsT
    (p : BlockShape) : Nat → List (ConstantVal × TargetMajor × List Expr) → Env → Env
  | _, [], env => env
  | m, (cv, M, rhss) :: rest, env =>
    consBlockRecsT p (m + 1) rest
      ⟨.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m)
        (recKExpected p M) (generatedRules (p.rulePrefixAt m) M rhss)
        :: env.consts, env.tables⟩

/-- **The checks of the block's projection tables** (`blockTables`), at the environment holding
the formers and the constructors. -/
def checkBlockTables (env : Env) : List ProjTable → m Unit
  | [] => pure ()
  | t :: rest => do
    checkStructProjTable t env
    checkBlockTables env rest

/-- **The checks after the pass**: the index binders' sorts, the generated recursors (at the
environment holding the constructors), the stream's recursors against them (at the environment
holding the generated ones) and the block's projection tables `Q`. -/
def checkBlockTail (ops : CheckerOps m) (block : List ConstantInfo) (q : BlockPass Env)
    (Q : List ProjTable) : m Unit := do
  let p := q.p
  checkBlockIdxSorts ops q.env₁ p p.members
  let env₂ := consBlockCtors p.nP p.memberCtors q.env₁
  let out ← checkBlockRec ops env₂ p (blockNestedBit p q.kinds) q.params
    q.tbl.toList q.rd q.cls block
  streamKCheck p p.recs out
  streamRecsCheck ops (mkFEnv (consBlockRecsT p 0 out env₂)) p.recs out
  checkBlockTables env₂ Q

/-! ## The block's check -/

/-- **The families declined at a definition.**  The names a literal's constructor form applies: a
former declared at one of them at a type that is not a telescope could pass `litShapeOk`
(`String.ofList : List Char → String`, `String` a definition reducing to a sort), and a literal's
constructor form would then apply a family.  And `Bool`: the frontend puts a stream's `Bool` at the
front of the fold, ahead of the definition it would be declared at. -/
def declinedAtDefinition : List Name :=
  [stringOfListName, listNilName, listConsName, charOfNatName, boolName]

/-- **A member's former at its telescope**, official's `whnf` loop where the declared type does
not show it: the declared type checked, reduced, and the two compared. -/
def reduceMember (ops : CheckerOps m) (env : Env) (ms : MemberShape) (nP : Nat) : m MemberShape :=
  if formerDefHeaded ms.cvT then do
    if declinedAtDefinition.contains ms.cvT.name then
      throw (.notImplemented s!"this family stored at a definition ({ms.cvT.name})")
    else do
      checkConstantVal ops env ms.cvT
      let cvR ← reducedFormer ops env ms.cvT (nP + ms.nIdx)
      unless ← ops.isDefEq env 0 ms.cvT.type cvR.type do
        throw (.invalid "direct sum: a type former's declared type and its reduct differ")
      pure { ms with cvT := cvR }
  else pure ms

/-- The members, each at its telescope. -/
def reduceMembers (ops : CheckerOps m) (env : Env) (nP : Nat) :
    List MemberShape → m (List MemberShape)
  | [] => pure []
  | ms :: rest => do
    let ms' ← reduceMember ops env ms nP
    let rest' ← reduceMembers ops env nP rest
    pure (ms' :: rest')

/-- Check an inductive block and install it (`blockConstants`, `blockTables`): the distinct names,
each former reduced to its telescope once (official's `check_inductive_types`), the pass over the
formers, the constructors and the classes at official's `is_rec` (`blockIsRec`), the projection
tables read off the block (once the constructors' telescopes have passed, every structure-like
member has its table), and the checks after it, the tables' among them.  The tables checked are
the tables installed. -/
def checkBlock (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) (p₀ : BlockShape) :
    m Env := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  unless boolTrueName ∉ p₀.memberNames ∧ boolFalseName ∉ p₀.memberNames do
    throw (.invalid "direct rec: a family at a `Bool` constructor's name")
  let ms ← reduceMembers ops env p₀.nP p₀.members
  let q ← checkBlockPass ops env { p₀ with members := ms } (blockIsRec p₀)
  let Q ← unwrapOr (blockTables p₀ p₀.members) (.internal "direct structure: projection bodies")
  checkBlockTail ops block q Q
  pure (env.pushDelta (blockConstants p₀) Q)

end ConLeche
