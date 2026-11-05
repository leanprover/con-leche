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
def checkBlockPassS (fe : FEnv) (p₀ : BlockParts) (isRec : Bool) :
    CheckCM (BlockPass FEnv) := do
  let (fe₁, cvTas, p₁) ← checkBlockIndsF (sharedOpsC mode fe) fe p₀ isRec
  let pC := p₀.complete p₁
  flushC
  let (ctorsAs, sortsss) ← checkBlockCtorsF (sharedOpsC mode fe₁) fe₁ fe₁
    pC.toBlockShape
    (pC.members.zip cvTas)
  let (ctx, holes) ← blockNestCtx pC.toBlockShape cvTas fe₁.find?
  let (rd, Ms) ← checkBlockClasses (sharedOpsC mode fe₁) fe₁ pC.toBlockShape
    ctx.params ctorsAs
  let (kinds, nfs, pos) ← checkBlockPositivity (sharedOpsC mode fe₁) fe₁.env fe₁.find?
    pC cvTas ctorsAs
  let st ← nestSeeds (sharedOpsC mode fe₁) fe₁.env ctx (classSeeds ctx holes Ms) pos
  pure ⟨fe₁, cvTas, pC, ctorsAs, sortsss, kinds, nfs, ctx.params, rd, Ms, st.ctorNfs⟩

/-- **`checkBlockTail` through the index**: one flush entering the
recursors' environment, every push in place.  The constructors' index
`fe₂` is needed across two conses: the rule-less recursors (the rule
stage reads `fe₂` and them at once) and the stored recursors (whose
records read `fe₂`).  A push onto `fe₂` while it is alive would copy the
whole bucket array, once per inductive block, so the rule-less
recursors are an overlay sharing the index (`shadowOpsC`'s `ruleEnv`,
`classFeROvl`), the stored recursors' records are built before the
first push (`blockRecInfosTF`), and the pass record is taken apart up
front, so the index is unique at every push. -/
def checkBlockTailS (block : List ConstantInfo) (q : BlockPass FEnv) :
    CheckCM FEnv :=
  match q with
  | ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, _nfs, params, rd, cls, tbl⟩ => do
  let _isorts ← checkBlockIdxSortsF (sharedOpsC mode env₁) env₁ p.toBlockShape
    (p.members.zip cvTas)
  let fe₂ := consBlockCtorsF p.nP ctorsAs env₁
  flushC
  let out ← genRecCheck (shadowOpsC mode) fe₂ p.toBlockShape
    (blockNestedBit p.toBlockShape kinds) params tbl.toList rd cls cvTas block
  -- the stored recursors against the generated ones (task #431): the
  -- checks run at the generated recursors as an OVERLAY on the
  -- constructors' index (read-only, sharing it), a flush entering and
  -- leaving that environment; the overlay is dead once the comparison
  -- returns, before the stored recursors are pushed
  storedKCheck p.toBlockShape p.recs out
  let feG := fe₂.overlay (blockRecInfosTF p.toBlockShape 0 out).reverse
  flushC
  storedRecsCheck (sharedOpsC mode feG) structWalkersC feG p.recs out
  flushC
  let recs := blockRecInfosTF p.toBlockShape 0 (storedOut p.recs out)
  checkBlockTablesF (m := CheckCM) structWalkersC p.toBlockShape
    (p.members.zip (ctorsAs.zip sortsss)) (FEnv.pushAll recs fe₂)

/-- The check at a group that shows every telescope it reads. -/
def checkBlockAtS (fe : FEnv) (block : List ConstantInfo) (p₀ : BlockParts) : CheckCM FEnv := do
  flushC
  let q ← checkBlockPassS mode fe p₀ (blockRawRec p₀)
  checkBlockTailS mode block q

/-- Twin of `reduceMember`. -/
def reduceMemberS (fe : FEnv) (nP : Nat) (ms : MemberShape) : CheckCM MemberShape :=
  if formerDefHeaded ms.cvT then do
    if litGuardFamilies.contains ms.cvT.name then
      throw (.notImplemented s!"a literal's family stored at a definition ({ms.cvT.name})")
    else do
      checkConstantValF (sharedOpsC mode fe) fe ms.cvT
      let cvR ← reducedFormer (sharedOpsC mode fe) fe.env ms.cvT (nP + ms.nIdx)
      checkConstantValF (sharedOpsC mode fe) fe cvR
      unless ← (sharedOpsC mode fe).isDefEq fe.env 0 ms.cvT.type cvR.type do
        throw (.invalid "direct sum: a type former's declared type and its reduct differ")
      pure { ms with cvT := cvR }
  else pure ms

/-- The members reduced, with the memos of the view. -/
def reduceMembersS (fe : FEnv) (nP : Nat) : List MemberShape → CheckCM (List MemberShape)
  | [] => pure []
  | ms :: rest => do
    flushC
    let ms' ← reduceMemberS mode fe nP ms
    let rest' ← reduceMembersS fe nP rest
    pure (ms' :: rest')

/-- Twin of `blockViews`. -/
def blockViewsS (fe : FEnv) : List Name → CheckCM (List ConstantInfo)
  | [] => pure []
  | c :: cs => do
    let rest ← blockViewsS fe cs
    match fe.find? c with
    | some (.indInfo cv caps) =>
      if formerDefHeaded cv then do
        if litGuardFamilies.contains c then
          throw (.notImplemented s!"a literal's family stored at a definition ({c})")
        else do
          flushC
          let cvR ← reducedFormer (sharedOpsC mode fe) fe.env cv (caps.nparams + caps.nIdx)
          flushC
          unless viewScoped (Expr.constsResolveF fe) cvR do
            throw (.internal "a family's reduced telescope is not closed")
          pure (.indInfo cvR caps :: rest)
      else pure rest
    | _ => pure rest

/-- The second path of `checkBlock`: the group reduced, the containers' views pushed on top,
the ordinary check, and the block's pushes replayed at `fe` as stored. -/
def checkBlockViewedS (fe : FEnv) (block : List ConstantInfo) (p₀ : BlockParts) (cs : List Name) :
    CheckCM FEnv := do
  let ms ← reduceMembersS mode fe p₀.nP p₀.members
  let vs ← blockViewsS mode fe cs
  let pR : BlockParts := { p₀ with members := ms }
  let fe₃ ← checkBlockAtS mode (FEnv.pushAll vs.reverse fe) (block.map (reducedRecord ms)) pR
  let cs₃ := fe₃.env.consts
  let ts₃ := fe₃.env.tables
  pure (FEnv.pushTables
      (ts₃.take (ts₃.length - fe.env.tables.length)).reverse
      (FEnv.pushAll
        ((cs₃.take (cs₃.length - (vs.length + fe.env.consts.length))).map
          (storedFormerOf p₀)).reverse fe))

/-- **`checkBlock` through the index**: the k-ary
mirror, at any number of members. -/
def checkBlockKS (fe : FEnv) (block : List ConstantInfo) (p₀ : BlockParts) :
    CheckCM FEnv := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  unless boolTrueName ∉ p₀.memberNames ∧ boolFalseName ∉ p₀.memberNames do
    throw (.invalid "direct rec: a family at a `Bool` constructor's name")
  let cs := blockContainers fe.find? p₀
  -- decided before the check, so that the ordinary path consumes `fe`
  if blockViewed fe.find? cs p₀ then
    checkBlockViewedS mode fe block p₀ cs
  else
    checkBlockAtS mode fe block p₀

end ConLeche.Cached
