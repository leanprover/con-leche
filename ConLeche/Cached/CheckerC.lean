module

public import ConLeche.Kernel.Inductives.BlockTail
public import ConLeche.Cached.CoreC

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

/-! ### The direct installers' walkers (task #214) -/

/-- `Expr.instPisAtLift` at the memoised substitution. -/
def instPisAtLiftC : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ body => instPisAtLiftC as (Expr.instantiate1LiftC body a)
  | _ :: _, _ => none

/-- `structProjBodiesGo` at the memoised substitution. -/
def structProjBodiesGoC (T : Name) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body =>
    (structProjBodiesGoC T k (i + 1) (Expr.instantiate1LiftC body (structProjArgP T i))).map
      (fdom :: ·)
  | _ + 1, _, _ => none

/-- `structProjBodies` at the memoised substitution
(`structProjBodiesC_eq`). -/
def structProjBodiesC (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  match instPisAtLiftC (structProjPs nP) cty with
  | some r => (structProjBodiesGoC T nF 0 r).map List.toArray
  | none => none

/-- `blockTables` over the memoised projection bodies (task #497;
`blockTablesC_eq`, `ConLeche/Verify/Cached/WalkersC.lean`): the tables
the index records (`StreamIndex.add`) and the block's install pushes
(`checkBlockKS`). -/
def blockTablesC (p : BlockShape) : List MemberShape → List ProjTable
  | [] => []
  | ms :: rest =>
    match ms.structCtor? with
    | some c =>
      match structProjBodiesC ms.declared.name p.nP c.2 c.1.type with
      | some bodies =>
        ⟨ms.declared.name, p.lps, p.nP, c.1.name, c.2, bodies⟩ :: blockTablesC p rest
      | none => blockTablesC p rest
    | none => blockTablesC p rest

/-- `declTables` over `blockTablesC`. -/
def declTablesC : Declaration → List ProjTable
  | .indDecl block nP =>
    match readBlock nP block with
    | .ok p => blockTablesC p p.members
    | .error _ => []
  | _ => []

/-- **The cached driver's walkers**: the memoised constant-resolution
gate (`constsResolveFC`, verified at `constsResolveFC_spec`) and the
memoised projection-body builder; equal to `StructWalkers.plain`
(`structWalkersC_eq_plain`). -/
def structWalkersC : StructWalkers := ⟨constsResolveFC, structProjBodiesC⟩

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
def checkBlockTailS (block : List ConstantInfo) (q : BlockPass FEnv) : CheckCM Unit :=
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
  checkBlockTablesF (m := CheckCM) structWalkersC p fe₂ p.members

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
    throw (unresolvedConstsErrorL (strLitStoredF fe) s!"type of {cv.name}" cv.type)
  let jsty ← (coreKnotI mode false fe checkFuel).infer 0 cv.type
  let _u ← opSIxC mode fe 0 jsty

/-- Twin of `reduceMember`. -/
def reduceMemberS (fe : FEnv) (ms : MemberShape) (nP : Nat) : CheckCM MemberShape :=
  if formerDefHeaded ms.cvT then do
    if declinedAtDefinition.contains ms.cvT.name then
      throw (.notImplemented s!"this family stored at a definition ({ms.cvT.name})")
    else do
      checkConstantValC mode fe ms.cvT
      let cvR ← reducedFormer (sharedOpsC mode fe) fe.env ms.cvT (nP + ms.nIdx)
      unless ← (sharedOpsC mode fe).isDefEq fe.env 0 ms.cvT.type cvR.type do
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
  let q ← checkBlockPassS mode fe { p₀ with members := ms } (blockIsRec p₀)
  checkBlockTailS mode block q
  pure (FEnv.pushDelta (blockConstants p₀) (blockTablesC p₀ p₀.members) fe)

end ConLeche.Cached
