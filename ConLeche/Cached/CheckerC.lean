module

public import ConLeche.Kernel.Inductives.GenRec
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
environment, and the positivity function on the stored constructors. -/
def checkBlockPassS (fe : FEnv) (p₀ : BlockParts) (isRec : Bool) :
    CheckCM (BlockPass FEnv) := do
  let (fe₁, cvTas, p₁) ← checkBlockIndsF (sharedOpsC mode fe) fe p₀ isRec
  let pC := p₀.complete p₁
  flushC
  let (ctorsAs, sortsss) ← checkBlockCtorsF (sharedOpsC mode fe₁) fe₁ fe₁ pC.toBlockShape
    (pC.members.zip cvTas)
  let (kinds, nfs, pos) ← checkBlockPositivity (sharedOpsC mode fe₁) fe₁.env fe₁.find?
    fe₁.env.consts pC cvTas ctorsAs
  pure ⟨fe₁, cvTas, pC, ctorsAs, sortsss, kinds, nfs, pos⟩

/-- **`checkBlockTail` through the index**: one flush
entering the recursors' environment.  The recursor stage's seeds walk at
the formers' environment through the O(1) prefix view of the
constructors' index (`FEnv.restrictTo`: the formers' index is not held
past the constructors' pushes, which would copy it). -/
def checkBlockTailS (block : List ConstantInfo) (q : BlockPass FEnv) :
    CheckCM FEnv := do
  let p := q.p
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.k ∨ 2 ≤ p.numCtors) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  let _isorts ← checkBlockIdxSortsF (sharedOpsC mode q.env₁) q.env₁ p.toBlockShape
    (p.members.zip q.cvTas)
  let vis₁ := q.env₁.visibleBelow
  let env₁ := q.env₁.env
  let fe₂ := consBlockCtorsF p.nP q.ctorsAs q.env₁
  flushC
  let out ← genRecCheck (shadowOpsC mode) (fe₂.restrictTo vis₁) env₁ fe₂ p.toBlockShape
    (blockNestedBit p.toBlockShape q.kinds) q.pos q.cvTas block q.ctorsAs
  let fe₃ := consBlockRecsTF fe₂.find? (·.constsResolveF fe₂) p.toBlockShape 0 out fe₂
  checkBlockTablesF (m := CheckCM) structWalkersC p.toBlockShape
    (p.members.zip (q.ctorsAs.zip q.sortsss)) fe₃

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
