module

public import ConLeche.Kernel.Inductives.GenRec
public import ConLeche.Kernel.Inductives.StoredRecs

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
  /-- the checked formers, in block order -/
  cvTas : List ConstantVal
  /-- the completed record: the sort read -/
  p : BlockParts
  /-- the checked constructors, per member, AS DECLARED -/
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
  let (rd, Ms) ← checkBlockClasses ops (mkFEnv env₁) pC.toBlockShape ctx.params ctorsAs
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
member majors it is `consBlockRecs`. -/
def consBlockRecsT
    (p : BlockShape) : Nat → List (ConstantVal × TargetMajor × List Expr) → Env → Env
  | _, [], env => env
  | m, (cv, M, rhss) :: rest, env =>
    consBlockRecsT p (m + 1) rest
      ⟨.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m)
        (recKExpected p M) (tgtStoredRules (p.rulePrefixAt m) M rhss)
        :: env.consts, env.tables⟩

/-- **The projection table at every STRUCTURE-LIKE member** (one
constructor, no index): the member's table; nothing at any other
member. -/
def checkBlockTables (p : BlockShape) :
    List (MemberShape × List (ConstantVal × Nat) × List (List Level)) → Env → m Env
  | [], env => pure env
  | (ms, ctorsA, sortss) :: rest, env => do
    let env' ←
      (match ctorsA, sortss with
       | [cA], [_] =>
         if ms.nIdx == 0 then
           checkStructProjTable ms.cvT.name cA.1.name p.lps p.nP cA.2 cA.1 env
         else pure env
       | _, _ => pure env)
    checkBlockTables p rest env'

/-- **The install after the pass**: the
index binders' sorts, the constructors consed,
the recursor stage, the STORED recursors against the generated ones
(`storedRecsCheck`, at the generated install), the stored recursors
consed at their majors, and the projection tables. -/
def checkBlockTail (ops : CheckerOps m) (block : List ConstantInfo)
    (q : BlockPass Env) : m Env := do
  let p := q.p
  let _isorts ← checkBlockIdxSorts ops q.env₁ p.toBlockShape (p.members.zip q.cvTas)
  let env₂ := consBlockCtors p.nP q.ctorsAs q.env₁
  let out ← checkBlockRec ops env₂ p (blockNestedBit p.toBlockShape q.kinds) q.params
    q.tbl.toList q.rd q.cls block q.cvTas
  -- the stored recursors, against the generated ones at the generated
  -- install (task #431): what is installed
  storedKCheck p.toBlockShape p.recs out
  storedRecsCheck ops .plain
    (mkFEnv (consBlockRecsT p.toBlockShape 0 out env₂)) p.recs out
  let env₃ := consBlockRecsT p.toBlockShape 0 (storedOut p.recs out) env₂
  checkBlockTables p.toBlockShape
    (p.members.zip (q.ctorsAs.zip q.sortsss)) env₃

/-! ## A def-headed former

A former whose stored type reaches its telescope only by reduction (task #480).  The
install pushes it as stored; the block's job reduces it, as official's `whnf` of the type
does, and checks the block at the reduced form, which needs nothing new of the check.  A
block nesting through such a family reads it reduced as well. -/

/-- The families the literal guards read by name, whose stored type they compare. -/
def litGuardFamilies : List Name :=
  [natName, natZeroName, natSuccName, stringName, stringOfListName, listName, listNilName,
   listConsName, charName, charOfNatName, boolName, boolTrueName, boolFalseName] ++
    reservedBasisNames

/-- A former at its reduced telescope (official's `whnf` loop), closed. -/
def reducedFormer (ops : CheckerOps m) (env : Env) (cv : ConstantVal) (n : Nat) :
    m ConstantVal := do
  let (bs, s) ← whnfTelescope ops env 0 n cv.type
  pure { cv with type := closeTelescope bs 0 (.sort s) }

/-- **A member of the block, reduced where it is def-headed**: the declared type checked,
reduced, and the two compared. -/
def reduceMember (ops : CheckerOps m) (env : Env) (nP : Nat) (ms : MemberShape) :
    m MemberShape :=
  if formerDefHeaded ms.cvT then do
    if litGuardFamilies.contains ms.cvT.name then
      throw (.notImplemented s!"a literal's family stored at a definition ({ms.cvT.name})")
    else do
      checkConstantVal ops env ms.cvT
      let cvR ← reducedFormer ops env ms.cvT (nP + ms.nIdx)
      checkConstantVal ops env cvR
      unless ← ops.isDefEq env 0 ms.cvT.type cvR.type do
        throw (.invalid "direct sum: a type former's declared type and its reduct differ")
      pure { ms with cvT := cvR }
  else pure ms

/-- The members, reduced. -/
def reduceMembers (ops : CheckerOps m) (env : Env) (nP : Nat) :
    List MemberShape → m (List MemberShape)
  | [] => pure []
  | ms :: rest => do
    let ms' ← reduceMember ops env nP ms
    let rest' ← reduceMembers ops env nP rest
    pure (ms' :: rest')

/-- A reduced former is closed, over its level parameters and what is stored. -/
def viewScoped (resolve : Expr → Bool) (cv : ConstantVal) : Bool :=
  !cv.type.hasFvar && cv.type.allLevelParamsDefined cv.levelParams &&
    resolve cv.type && cv.type.looseBVarsBounded 0

/-- The heads of the applications in `e` with an argument mentioning `names`, and whether
`e` mentions them; memoized on the shared term. -/
def Expr.nestedHeadsGo (names : List Name) :
    Expr → Std.HashMap Expr Bool × List Name → Bool × (Std.HashMap Expr Bool × List Name)
  | e, st =>
    match st.1[e]? with
    | some b => (b, st)
    | none =>
      let (b, st') : Bool × (Std.HashMap Expr Bool × List Name) :=
        match e with
        | .bvar _ | .sort _ | .lit _ => (false, st)
        | .const n _ => (names.contains n, st)
        | .fvar _ ty => Expr.nestedHeadsGo names ty st
        | .app f a =>
          let (bf, st₁) := Expr.nestedHeadsGo names f st
          let (ba, st₂) := Expr.nestedHeadsGo names a st₁
          let st₃ := match ba, (Expr.app f a).getAppFn with
            | true, .const I _ => (st₂.1, I :: st₂.2)
            | _, _ => st₂
          (bf || ba, st₃)
        | .lam ty b | .forallE ty b =>
          let (b₁, st₁) := Expr.nestedHeadsGo names ty st
          let (b₂, st₂) := Expr.nestedHeadsGo names b st₁
          (b₁ || b₂, st₂)
        | .letE ty v b =>
          let (b₁, st₁) := Expr.nestedHeadsGo names ty st
          let (b₂, st₂) := Expr.nestedHeadsGo names v st₁
          let (b₃, st₃) := Expr.nestedHeadsGo names b st₂
          (b₁ || b₂ || b₃, st₃)
        | .proj s _ x =>
          let (b₁, st₁) := Expr.nestedHeadsGo names x st
          (names.contains s || b₁, st₁)
      (b, (st'.1.insert e b, st'.2))

/-- The constants of `e`, memoized on the shared term. -/
def Expr.constsGo : Expr → Std.HashSet Expr × List Name → Std.HashSet Expr × List Name
  | e, st =>
    if st.1.contains e then st else
    let st := (st.1.insert e, st.2)
    match e with
    | .bvar _ | .sort _ | .lit _ => st
    | .const n _ => (st.1, n :: st.2)
    | .fvar _ ty => Expr.constsGo ty st
    | .app f a => Expr.constsGo a (Expr.constsGo f st)
    | .lam ty b | .forallE ty b => Expr.constsGo b (Expr.constsGo ty st)
    | .letE ty v b => Expr.constsGo b (Expr.constsGo v (Expr.constsGo ty st))
    | .proj _ _ x => Expr.constsGo x st

/-- **The families a nested block reads**, as a worklist: from the heads of the applications
that take the group as an argument, the inductives in those families' constructor types,
each once. -/
def containerClosure (find? : Name → Option ConstantInfo) :
    Nat → List Name → List Name → List Name
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, c :: work, seen =>
    if seen.contains c then containerClosure find? n work seen else
    match find? c with
    | some (.indInfo _ caps) =>
      let st := caps.ctors.foldl (fun st k =>
        match find? k with
        | some ci => Expr.constsGo ci.toConstantVal.type st
        | none => st) (({} : Std.HashSet Expr), [])
      containerClosure find? n (st.2 ++ caps.all ++ work) (c :: seen)
    | _ => containerClosure find? n work seen

/-- The stored families a block reads as containers, by name.  The fuel is for termination
only, as `checkFuel`: the worklist takes one step per name it holds, and no run takes 2^62. -/
def blockContainers (find? : Name → Option ConstantInfo) (p : BlockParts) : List Name :=
  let st := p.allCtors.foldl (fun st c => (Expr.nestedHeadsGo p.memberNames c.1.type st).2)
    (({} : Std.HashMap Expr Bool), [])
  containerClosure find? (2 ^ 62) st.2 []

/-- **The block's def-headed containers at their reduced telescopes**, at this environment:
a run does not see an extension (`Verify/EnvExt.lean`), so this is what the family's own job
read. -/
def blockViews (ops : CheckerOps m) (env : Env) :
    List Name → m (List ConstantInfo)
  | [] => pure []
  | c :: cs => do
    let rest ← blockViews ops env cs
    match env.find? c with
    | some (.indInfo cv caps) =>
      if formerDefHeaded cv then do
        if litGuardFamilies.contains c then
          throw (.notImplemented s!"a literal's family stored at a definition ({c})")
        else do
          let cvR ← reducedFormer ops env cv (caps.nparams + caps.nIdx)
          unless viewScoped (·.constsResolve env) cvR do
            throw (.internal "a family's reduced telescope is not closed")
          pure (.indInfo cvR caps :: rest)
      else pure rest
    | _ => pure rest

/-- A member at its stored type again. -/
def storedFormerOf (p₀ : BlockParts) : ConstantInfo → ConstantInfo
  | .indInfo cv caps =>
    match p₀.members.find? (·.cvT.name == cv.name) with
    | some ms => .indInfo ms.cvT caps
    | none => .indInfo cv caps
  | c => c

/-- **The job's environment back at what the group stores**: the block's pushes at the
input environment, each member at its stored type, the containers' views gone. -/
def restoreBlock (p₀ : BlockParts) (nViews : Nat) (env env₃ : Env) : Env :=
  ⟨(env₃.consts.take (env₃.consts.length - (nViews + env.consts.length))).map (storedFormerOf p₀)
      ++ env.consts, env₃.tables⟩

/-- The block's check at an environment and a group that show every telescope it reads. -/
def checkBlockAt (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) (p₀ : BlockParts) :
    m Env := do
  let q ← checkBlockPass ops env p₀ (blockRawRec p₀)
  checkBlockTail ops block q

/-- A former in a block's raw records at its reduced form. -/
def reducedRecord (members : List MemberShape) : ConstantInfo → ConstantInfo
  | .indInfo cv caps =>
    match members.find? (·.cvT.name == cv.name) with
    | some ms => .indInfo ms.cvT caps
    | none => .indInfo cv caps
  | c => c

/-- Does the block's check need its second path: a member def-headed, or a container? -/
def blockViewed (find? : Name → Option ConstantInfo) (cs : List Name) (p₀ : BlockParts) : Bool :=
  p₀.members.any (formerDefHeaded ·.cvT) || cs.any fun c =>
    match find? c with
    | some (.indInfo cv _) => formerDefHeaded cv
    | _ => false

/-- Check and install an inductive block: the distinct names, the pass over the formers, the
constructors and the classes at official's `is_rec` (`blockRawRec`), and the install after
it.  A block that shows every telescope it reads is checked as it stands; otherwise at its
reduced form and its containers' views, and restored (`restoreBlock`). -/
def checkBlock (ops : CheckerOps m) (env : Env) (block : List ConstantInfo) (p₀ : BlockParts) :
    m Env := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  unless boolTrueName ∉ p₀.memberNames ∧ boolFalseName ∉ p₀.memberNames do
    throw (.invalid "direct rec: a family at a `Bool` constructor's name")
  let cs := blockContainers env.find? p₀
  if blockViewed env.find? cs p₀ then do
    let ms ← reduceMembers ops env p₀.nP p₀.members
    let vs ← blockViews ops env cs
    let pR : BlockParts := { p₀ with members := ms }
    let env₃ ← checkBlockAt ops ⟨vs ++ env.consts, env.tables⟩
      (block.map (reducedRecord ms)) pR
    pure (restoreBlock p₀ vs.length env env₃)
  else
    checkBlockAt ops env block p₀

end ConLeche
