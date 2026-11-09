module

public import ConLeche.Kernel.Inductives.BlockTail
public import ConLeche.Cached.CoreC
public import ConLeche.Cached.IndPositivity

@[expose] public section

/-!
# The cached declaration driver

The declaration checker *above* `CheckerOps` is shared verbatim with
the generic one: only the core is replaced.  What lives here is the
thin per-declaration phase-driver layer at `CheckCM`, plus the
entry-point record over the cached core.

What the layer is *for*: the per-declaration phase driver that the
parsed-declaration driver (`ConLeche/Cached/ParsedC.lean`) and its bridges
consume — at a `CheckMode` (see `ParsedC.lean`'s header).
-/

namespace ConLeche.Cached

open ConLeche

/-! ### The direct installers' walker (task #214) -/

/-- `structProjBodiesGo` at the memoised substitution
(`structProjBodiesGoC_eq`). -/
def structProjBodiesGoC (T : Name) (vs : List Expr) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body =>
    (structProjBodiesGoC T (structProjArgP T i :: vs) k (i + 1) body).map
      (Expr.instantiateLiftC fdom vs :: ·)
  | _ + 1, _, _ => none

/-- `structProjBodies` at the memoised substitution: each field's raw
domain substituted once by `instantiateLiftC` (`structProjBodiesC_eq`). -/
def structProjBodiesC (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  match cty.stripPis nP with
  | some (_, r) => (structProjBodiesGoC T (structProjPs nP).reverse nF 0 r).map List.toArray
  | none => none

/-- `blockTables` over the memoised projection bodies (task #497;
`blockTablesC_eq`, `ConLeche/Verify/Cached/WalkersC.lean`): the tables
the index records (`declTablesC`, `StreamIndex.add`) and the tables the
block's install checks and pushes (`checkBlockKS`). -/
def blockTablesC (p : BlockShape) : List MemberShape → Option (List ProjTable)
  | [] => some []
  | ms :: rest =>
    match ms.structCtor? with
    | some c =>
      (structProjBodiesC ms.declared.name p.nP c.2 c.1.type).bind fun bodies =>
        (blockTablesC p rest).map (⟨ms.declared.name, p.lps, p.nP, c.1.name, c.2, bodies⟩ :: ·)
    | none => blockTablesC p rest

/-- `declTables` over `blockTablesC`. -/
def declTablesC : Declaration → List ProjTable
  | .indDecl block nP =>
    match readBlock nP block with
    | .ok p => (blockTablesC p p.members).getD []
    | .error _ => []
  | _ => []

/-- The cached `blockIsRec` (official's `is_rec`): the declared
constructors' syntactic domains scanned by `mentionsAnyConstC`
(`blockIsRecC_eq`). -/
def blockIsRecC (p : BlockShape) : Bool :=
  p.members.any fun ms => ms.ctors.any fun c => Expr.piDomsMentionAnyC p.memberNames c.1.type

/-- `blockConstants` at `blockIsRecC`: the constants the index records
(`declConstantsC`) and the block's install pushes (`checkBlockKS`). -/
def blockConstantsC (p : BlockShape) : List ConstantInfo :=
  blockFormers p (blockIsRecC p) ++ blockCtors p ++ blockRecs p p.recs

/-- `declConstants` over `blockConstantsC`. -/
def declConstantsC : Declaration → List ConstantInfo
  | .defnDecl cv value hint => [.defnInfo cv value hint]
  | .thmDecl cv _ => [.thmInfo cv]
  | .opaqueDecl cv _ => [.axiomInfo cv]
  | .axiomDecl cv =>
    if cv.name = quotSoundName then [quotAt .sound cv]
    else if cv.name = sorryAxName then []
    else [.axiomInfo cv]
  | .quotDecl k cv => [quotAt k cv]
  | .indDecl block nP =>
    match readBlock nP block with
    | .ok p => blockConstantsC p
    | .error _ => []

/-- **The cached driver's walker**: the memoised constant-resolution
gate (`constsResolveFC`, verified at `constsResolveFC_spec`); equal to
`StructWalkers.plain` (`structWalkersC_eq_plain`). -/
def structWalkersC : StructWalkers := ⟨constsResolveFC⟩

variable (mode : CheckMode)

/-! ## The entry-point record over the cached core

`opE`/`opB`/`opS` pass their `Expr` arguments through: there is one
expression type (task #172 B3a). -/

/-- Shared-state unary entry point: run the cached knot. -/
def opE (fe : FEnv) (pick : CoreFnsI → Nat → Expr → CheckCM Expr)
    (d : Nat) (e : Expr) : CheckCM Expr := do
  pick (coreKnotI mode false fe checkFuel) d e

/-- Shared-state definitional-equality entry point. -/
def opB (fe : FEnv) (d : Nat) (a b : Expr) : CheckCM Bool :=
  (coreKnotI mode false fe checkFuel).defeq d a b

/-- Shared-state sort-ensuring entry point. -/
def opS (fe : FEnv) (d : Nat) (e : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode false fe checkFuel) d e

/-- The per-declaration shared operations at a fixed environment
index. -/
def sharedOpsC (fe : FEnv) : CheckerOps CheckCM where
  inferType _ d e := opE mode fe (·.infer) d e
  isDefEq _ d a b := opB mode fe d a b
  ensureSort _ d e := opS mode fe d e
  whnf _ d e := opE mode fe (·.whnf) d e


/-! ## Thin phase drivers (one `CState` per declaration)

Each mirrors its `ConLeche/Kernel/Checker.lean` counterpart clause by
clause; the differences are exactly: `flushC` at environment
transitions, `FEnv.push` maintaining the index, and *every*
environment lookup routed through the index (task #63). -/

/-- **The rule stage's operations at the rule-less recursors'
environment**: `sharedOpsC` at `feR`, with a `flushC` ENTERING and
LEAVING its `inferType`.

One rule runs operations at TWO environments, interleaved: its
right-hand side is typed at `feR` (the `k` rule-less
recursors consed), and everything after — the λ-domains' defeq, the
residue's inference, the conclusion's defeq — at the constructors'
index.  The memo caches are keyed by the term alone, and their
invariant (`CSOK`, `ConLeche/Verify/Cached/SimC.lean`) is a claim at
ONE environment, so a state threaded unflushed across the two is not
a state of either: an entry the `feR` half wrote (a term naming a
recursor, typed where the recursor is stored) is not a claim at the
constructors' environment, where the recursor is absent.  The flushes
are the drivers' own discipline (`flushC` at every environment
transition), placed where the transitions are: the stage's `feR` half
is exactly one operation, the `inferType` (`classRuleOk`,
`ConLeche/Kernel/Inductives/GenRec.lean`, infers only).  Every other
operation is `sharedOpsC`'s. -/
def sharedOpsRuleR (fe : FEnv) : CheckerOps CheckCM :=
  { sharedOpsC mode fe with
    inferType := fun _ d e => do
      -- the flush entering the `feR` half
      flushC
      let t ← opE mode fe (·.infer) d e
      flushC
      pure t }

/-- **The shadow operations of the cached driver**: the index-bound
operations `sharedOpsC`, the rule variant `sharedOpsRuleR` (a flush at
each of a rule's two environment transitions), `flushC` at every
environment change, the memoised walkers, and the rule-less recursors
as an overlay sharing the constructors' index (`classFeROvl`).  The
recursor stage (`checkBlockTailS`) runs `genRecCheck` at them. -/
def shadowOpsC : ShadowOps CheckCM :=
  ⟨sharedOpsC mode, sharedOpsRuleR mode, flushC, structWalkersC, classFeROvl⟩

/-- **`checkBlockPass` through the index**: the k
formers checked and consed — one flush entering the environment that
holds them all — then the constructors per member at that
environment, the classes, and the positivity check walking every class
(the members' root frame first). -/
def checkBlockPassS (fe : FEnv) (p₀ : BlockShape) (isRec : Bool) :
    CheckCM (BlockPass FEnv) := do
  let (fe₁, p₁) ← checkBlockIndsF (sharedOpsC mode fe) fe p₀ isRec
  flushC
  checkBlockCtorsF (sharedOpsC mode fe₁) fe₁ fe₁ p₁ p₁.members
  let (ctx, holes) ← blockNestCtx p₁ fe₁.find?
  let (rd, Ms) ← checkBlockClasses (sharedOpsC mode fe₁) fe₁ p₁ ctx.params
  let (outs, pos) ← checkBlockPositivity (sharedOpsC mode fe₁) fe₁.env fe₁.find? p₁
  let st ← nestSeeds (sharedOpsC mode fe₁) fe₁.env ctx (classSeeds ctx holes Ms) pos
  pure ⟨fe₁, p₁, nestOutKinds outs, ctx.params, rd, Ms, st.ctorNfs⟩

/-- **`checkBlockTail` through the index**: one flush entering the recursors' environment.  The
constructors' index `fe₂` is read at once by the rule-less recursors (the rule stage reads `fe₂` and
them) and by the generated recursors, so both are overlays sharing it (`shadowOpsC`'s `ruleEnv`,
`classFeROvl`; `blockRecInfosTF`): a push onto `fe₂` while it is alive would copy the whole bucket
array, once per inductive block. -/
def checkBlockTailS (block : List ConstantInfo) (q : BlockPass FEnv) (Q : List ProjTable) :
    CheckCM Unit :=
  match q with
  | ⟨env₁, p, kinds, params, rd, cls, tbl⟩ => do
  checkBlockIdxSortsF (sharedOpsC mode env₁) env₁ p p.members
  let fe₂ := consBlockCtorsF p.nP p.memberCtors env₁
  flushC
  let out ← genRecCheck (shadowOpsC mode) fe₂ p
    (blockNestedBit p kinds) params tbl.toList rd cls block
  -- the stream's recursors against the generated ones, at the generated recursors as an OVERLAY on
  -- the constructors' index (read-only, sharing it), a flush entering and leaving that environment
  streamKCheck p p.recs out
  let feG := fe₂.overlay (blockRecInfosTF p 0 out).reverse
  flushC
  streamRecsCheck (sharedOpsC mode feG) structWalkersC feG p.recs out
  flushC
  checkBlockTablesF (m := CheckCM) structWalkersC fe₂ Q

/-- The cached `unresolvedConstsErrorL`: the `sorryAx` test by the
memoized `mentionsAnyConstC` (`unresolvedConstsErrorLC_eq`). -/
def unresolvedConstsErrorLC (strOk : Bool) (where_ : String) (e : Expr) : CheckError :=
  if !strOk && (Expr.hasStrLitGo {} e).1 then
    .notImplemented "string literals before the String support declarations"
  else if Expr.mentionsAnyConstC [sorryAxName] e then
    .notImplemented s!"use of the sorryAx axiom in {where_}"
  else .invalid s!"unknown constant in {where_}"

/-- Parsed `ensureSort` (no per-call conversion). -/
def opSIxC (fe : FEnv) (d : Nat) (i : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode false fe checkFuel) d i

/-- `checkConstantVal` on a parsed declaration: the checks of
`checkConstantValF` with the syntactic passes memoized on the `Expr`
DAG and the cached operations on its nodes. -/
def checkConstantValC (fe : FEnv) (cv : ConstantVal) (allowOp : Bool := false) :
    CheckCM Unit := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if natOpName cv.name && !allowOp then
    throw (.invalid s!"a certified Nat operation's name, not a definition: {cv.name}")
  unless litShapeOk (.axiomInfo cv) do
    throw (.notImplemented s!"a declaration at a literal's name with another shape ({cv.name})")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless Expr.looseBVarsBounded 0 cv.type do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if Expr.hasFvar cv.type then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  unless Expr.allLevelParamsDefinedC cv.levelParams cv.type do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless constsResolveFC fe cv.type do
    throw (unresolvedConstsErrorLC (strLitStoredF fe) s!"type of {cv.name}" cv.type)
  let jsty ← (coreKnotI mode false fe checkFuel).infer 0 cv.type
  let _u ← opSIxC mode fe 0 jsty

/-- Twin of `reduceMember`. -/
def reduceMemberS (fe : FEnv) (ms : MemberShape) (nP : Nat) : CheckCM MemberShape :=
  if formerDefHeaded ms.cvT then do
    if declinedAtDefinition.contains ms.cvT.name then
      throw (.notImplemented s!"this family stored at a definition ({ms.cvT.name})")
    else do
      checkConstantValC mode fe ms.cvT
      let cvR ← reducedFormerC mode fe ms.cvT (nP + ms.nIdx)
      unless ← (coreKnotI mode false fe checkFuel).defeq 0 ms.cvT.type cvR.type do
        throw (.invalid "direct sum: a type former's declared type and its reduct differ")
      pure { ms with cvT := cvR }
  else pure ms

/-- Twin of `reduceMembers`. -/
def reduceMembersS (fe : FEnv) (nP : Nat) : List MemberShape → CheckCM (List MemberShape)
  | [] => pure []
  | ms :: rest => do
    flushC
    let ms' ← reduceMemberS mode fe ms nP
    let rest' ← reduceMembersS fe nP rest
    pure (ms' :: rest')

/-- **`checkBlock` through the index.** -/
def checkBlockKS (fe : FEnv) (block : List ConstantInfo) (p₀ : BlockShape) :
    CheckCM FEnv := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  unless boolTrueName ∉ p₀.memberNames ∧ boolFalseName ∉ p₀.memberNames do
    throw (.invalid "direct rec: a family at a `Bool` constructor's name")
  let ms ← reduceMembersS mode fe p₀.nP p₀.members
  flushC
  let q ← checkBlockPassS mode fe { p₀ with members := ms } (blockIsRecC p₀)
  let Q ← unwrapOr (blockTablesC p₀ p₀.members) (.internal "direct structure: projection bodies")
  checkBlockTailS mode block q Q
  pure (FEnv.pushDelta (blockConstantsC p₀) Q fe)

end ConLeche.Cached
