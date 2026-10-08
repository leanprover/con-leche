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
  | a :: as, .forallE _ body _ => instPisAtLiftC as (Expr.instantiate1LiftC body a)
  | _ :: _, _ => none

/-- `structProjBodiesGo` at the memoised substitution. -/
def structProjBodiesGoC (T : Name) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body _ =>
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
  pick (coreKnotI mode fe checkFuel) d e

/-- Shared-state definitional-equality entry point. -/
def opB (fe : FEnv) (d : Nat) (a b : Expr) : CheckCM Bool :=
  (coreKnotI mode fe checkFuel).defeq d a b

/-- Shared-state sort-ensuring entry point. -/
def opS (fe : FEnv) (d : Nat) (e : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode fe checkFuel) d e

/-- The per-declaration shared operations at a fixed environment
index. -/
def sharedOpsC (fe : FEnv) : CheckerOps CheckCM where
  annotate _ d e := opE mode fe (·.annotate) d e
  inferType _ d e := opE mode fe (·.infer) d e
  isDefEq _ d a b := opB mode fe d a b
  ensureSort _ d e := opS mode fe d e
  whnf _ d e := opE mode fe (·.whnf) d e
  -- the executable's instantiation delivers the attempt's outcome to
  -- the continuation (the decline message names what each pin variant
  -- failed on); after an error the state is the PRE-attempt one — the
  -- memo entries the failed attempt wrote are discarded with it
  orElse x k := fun s => match x s with
    | .ok (true, s') => .ok ((), s')
    | .ok (false, s') => k none s'
    | .error e => k (some e) s

/-! ## Thin phase drivers (one `CState` per declaration)

Each mirrors its `ConLeche/Kernel/Checker.lean` counterpart clause by
clause; the differences are exactly: `flushC` at environment
transitions, `FEnv.push` maintaining the index, and *every*
environment lookup routed through the index (task #63). -/

/-- **The rule stage's operations at the rule-less recursors'
environment**: `sharedOpsC` at `feR`, with a `flushC`
ENTERING its `annotate` and LEAVING its `inferType`.

One rule runs operations at TWO environments, interleaved: its
right-hand side is annotated and typed at `feR` (the `k` rule-less
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
is exactly those two operations, the `annotate` first and the
`inferType` last (`classRuleOk`,
`ConLeche/Kernel/Inductives/GenRec.lean`, infers only).  Every other
operation is `sharedOpsC`'s. -/
def sharedOpsRuleR (fe : FEnv) : CheckerOps CheckCM :=
  { sharedOpsC mode fe with
    annotate := fun _ d e => do
      flushC
      opE mode fe (·.annotate) d e
    inferType := fun _ d e => do
      let t ← opE mode fe (·.infer) d e
      flushC
      pure t }

/-- **The shadow operations of the cached driver**: the index-bound
operations `sharedOpsC`, the rule variant `sharedOpsRuleR` (a flush at
each of a rule's two environment transitions), `flushC` at every
environment change, and the memoised walkers.  The recursor stage
(`checkBlockTailS`) runs `genRecCheck` at them. -/
def shadowOpsC : ShadowOps CheckCM :=
  ⟨sharedOpsC mode, sharedOpsRuleR mode, flushC, structWalkersC⟩

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
  let (ctorsAs, sortsss) ← checkBlockCtorsF (sharedOpsC mode fe₁) fe₁ fe₁ pC.toBlockShape
    (pC.members.zip cvTas)
  let (ctx, holes) ← blockNestCtx pC.toBlockShape cvTas fe₁.find?
  let (rd, Ms) ← checkBlockClasses (sharedOpsC mode fe₁) fe₁ fe₁.env pC.toBlockShape
    ctx.params ctorsAs
  let (kinds, nfs, pos) ← checkBlockPositivity (sharedOpsC mode fe₁) fe₁.env fe₁.find?
    pC cvTas ctorsAs
  let st ← nestSeeds (sharedOpsC mode fe₁) fe₁.env ctx (classSeeds ctx holes Ms) pos
  pure ⟨fe₁, cvTas, pC, ctorsAs, sortsss, kinds, nfs, ctx.params, rd, Ms, st.ctorNfs⟩

/-- **`checkBlockTail` through the index**: one flush
entering the recursors' environment.  The reference form, which the
proofs read; the driver runs `checkBlockTailS`, equal to it
(`checkBlockTailS_eq_ref`, `ConLeche/Cached/BlockOverlay.lean`). -/
def checkBlockTailSRef (block : List ConstantInfo) (q : BlockPass FEnv) :
    CheckCM FEnv := do
  let p := q.p
  let _isorts ← checkBlockIdxSortsF (sharedOpsC mode q.env₁) q.env₁ p.toBlockShape
    (p.members.zip q.cvTas)
  let fe₂ := consBlockCtorsF p.nP q.ctorsAs q.env₁
  flushC
  let out ← genRecCheck (shadowOpsC mode) fe₂ p.toBlockShape
    (blockNestedBit p.toBlockShape q.kinds) q.params q.tbl.toList q.rd q.cls q.cvTas block
  let fe₃ := consBlockRecsTF fe₂.find? (·.constsResolveF fe₂) p.toBlockShape 0 out fe₂
  checkBlockTablesF (m := CheckCM) structWalkersC p.toBlockShape
    (p.members.zip (q.ctorsAs.zip q.sortsss)) fe₃

/-- **`checkBlockTailSRef` with every push in place** (task #329).  The
reference holds the constructors' index `fe₂` live across two pushes:
`genRecCheck`'s rule-less recursors (`classFeR`, while the rule stage
still reads `fe₂`) and the stored recursors (`consBlockRecsTF`, whose
lookup closures read `fe₂`).  Each copied the whole bucket array, once
per inductive block, a cost that grew with the environment.  Here the
rule-less recursors are an overlay sharing the index
(`genRecCheckOvl`), the stored recursors' records are built before the
first push (`blockRecInfosTF`), and the pass record is taken apart up
front, so the index is unique at every push.  An `fe₂` that already
carries an overlay (never on the install path) runs the reference's
code. -/
def checkBlockTailS (block : List ConstantInfo) (q : BlockPass FEnv) :
    CheckCM FEnv :=
  match q with
  | ⟨env₁, cvTas, p, ctorsAs, sortsss, kinds, _nfs, params, rd, cls, tbl⟩ => do
  let _isorts ← checkBlockIdxSortsF (sharedOpsC mode env₁) env₁ p.toBlockShape
    (p.members.zip cvTas)
  let fe₂ := consBlockCtorsF p.nP ctorsAs env₁
  flushC
  if fe₂.ovl.isEmpty then
    let out ← genRecCheckOvl (shadowOpsC mode) fe₂ p.toBlockShape
      (blockNestedBit p.toBlockShape kinds) params tbl.toList rd cls cvTas block
    let recs := blockRecInfosTF fe₂.find? (·.constsResolveF fe₂) p.toBlockShape 0 out
    checkBlockTablesF (m := CheckCM) structWalkersC p.toBlockShape
      (p.members.zip (ctorsAs.zip sortsss)) (FEnv.pushAll recs fe₂)
  else
    let out ← genRecCheck (shadowOpsC mode) fe₂ p.toBlockShape
      (blockNestedBit p.toBlockShape kinds) params tbl.toList rd cls cvTas block
    let fe₃ := consBlockRecsTF fe₂.find? (·.constsResolveF fe₂) p.toBlockShape 0 out fe₂
    checkBlockTablesF (m := CheckCM) structWalkersC p.toBlockShape
      (p.members.zip (ctorsAs.zip sortsss)) fe₃

/-- **`checkBlock` through the index**: the k-ary
mirror, at any number of members. -/
def checkBlockKS (fe : FEnv) (block : List ConstantInfo) (p₀ : BlockParts) :
    CheckCM FEnv := do
  unless (p₀.allCtors.map (·.1.name)).Nodup ∧ p₀.memberNames.Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  flushC
  let q ← checkBlockPassS mode fe p₀ (blockRawRec p₀)
  checkBlockTailS mode block q

end ConLeche.Cached
