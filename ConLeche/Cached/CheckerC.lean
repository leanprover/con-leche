module

public import ConLeche.Kernel.Inductives.BlockTail
public import ConLeche.Cached.IndBlock
public import ConLeche.Cached.IndTail

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

/-- The cached `Expr.dropVars`: each variable dropped by `instantiate1C`
(`dropVarsC_eq`). -/
def Expr.dropVarsC : Nat → Expr → Expr
  | 0, e => e
  | n + 1, e => Expr.dropVarsC n (Expr.instantiate1C e (.sort .zero))

/-- The cached `recFire`: a nested recursor's container parameters
moved by `dropVarsC` (`recFireC_eq`). -/
def recFireC (p : BlockShape) (rc : RecShape) : RecRuleFire :=
  if rc.tgt < p.k then .plain
  else
    match rc.cvR.type.stripPis rc.mI with
    | some (_, .forallE dom _) =>
      match dom.getAppFn with
      | .const _ us =>
        let nI := rc.mI - rc.rP
        let args := dom.getAppArgs
        .nested us ((args.take (args.length - nI)).map (Expr.dropVarsC nI))
      | _ => .plain
    | _ => .plain

/-- The cached `blockRecs`, over `recFireC` (`blockRecsC_eq`). -/
def blockRecsC (p : BlockShape) : List RecShape → List ConstantInfo
  | [] => []
  | rc :: rest =>
    .recInfo rc.cvR rc.mI rc.rP rc.isK (rc.rules.map ({ · with fire := recFireC p rc })) ::
      blockRecsC p rest

/-- `blockConstants` at `blockIsRecC` and `blockRecsC`: the constants the index records
(`declConstantsC`) and the block's install pushes (`checkBlockKS`). -/
def blockConstantsC (p : BlockShape) : List ConstantInfo :=
  blockFormers p (blockIsRecC p) ++ blockCtors p ++ blockRecsC p p.recs

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

/-- **`checkBlockPass` through the index**: the k
formers checked and consed — one flush entering the environment that
holds them all — then the constructors per member at that
environment, the classes, and the positivity check walking every class
(the members' root frame first). -/
def checkBlockPassS (fe : FEnv) (p₀ : BlockShape) (isRec : Bool) :
    CheckCM (BlockPass FEnv) := do
  let (fe₁, p₁) ← checkBlockIndsC mode fe p₀ isRec
  flushC
  checkBlockCtorsC mode fe₁ fe₁ p₁ p₁.members
  let (ctx, holes) ← blockNestCtxC p₁ fe₁.find?
  let (rd, Ms) ← checkBlockClassesC mode fe₁ p₁ ctx.params
  let (outs, pos) ← checkBlockPositivityC mode fe₁ fe₁.find? p₁
  let st ← nestSeedsC mode fe₁ ctx (classSeedsC ctx holes Ms) pos
  pure ⟨fe₁, p₁, nestOutKinds outs, ctx.params, rd, Ms, st.ctorNfs⟩

/-- **`checkBlockTail` through the index**: one flush entering the recursors' environment.  The
constructors' index `fe₂` is read at once by the rule-less recursors (the rule stage reads `fe₂` and
them) and by the generated recursors, so both are overlays sharing it (`classFeROvl`,
`genRecCheckC`; `blockRecInfosTC`): a push onto `fe₂` while it is alive would copy the whole bucket
array, once per inductive block. -/
def checkBlockTailS (block : List ConstantInfo) (q : BlockPass FEnv) (Q : List ProjTable) :
    CheckCM Unit :=
  match q with
  | ⟨env₁, p, kinds, params, rd, cls, tbl⟩ => do
  checkBlockIdxSortsC mode env₁ p p.members
  let fe₂ := consBlockCtorsF p.nP p.memberCtors env₁
  flushC
  let out ← genRecCheckC mode fe₂ p (blockNestedBit p kinds) params tbl.toList rd cls block
  -- the stream's recursors against the generated ones, at the generated recursors as an OVERLAY on
  -- the constructors' index (read-only, sharing it), a flush entering and leaving that environment
  streamKCheck p p.recs out
  let feG := fe₂.overlay (blockRecInfosTC p 0 out).reverse
  flushC
  streamRecsCheckC mode feG p.recs out
  flushC
  checkBlockTablesC fe₂ Q

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
