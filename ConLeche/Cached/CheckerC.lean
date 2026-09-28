module

public import ConLeche.Conformance.RecConformF
public import ConLeche.Kernel.Inductives.RecCheck
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
`inferType` last (`targetRule`,
`ConLeche/Kernel/Inductives/RecCheck.lean`).  Every other
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
(`checkBlockRecS`) runs `targetRecCheck` at them. -/
def shadowOpsC : ShadowOps CheckCM :=
  ⟨sharedOpsC mode, sharedOpsRuleR mode, flushC, structWalkersC⟩

/-- `checkBlockRec` through the index: the CHECK — `targetRecCheck`, the
function the pure install runs (`checkBlockRecT`), at the cached shadow
operations — then, where every kind is flat (`conf`), the reject-only
conformance check at the constructors' index (`checkBlockRecConformF`).
The `flushC` is there because the check finishes with its
caches at the recursors' index. -/
def checkBlockRecS (fe : FEnv) (p : BlockParts) (nested conf : Bool) (aux : NestNodes)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (nfs : List (List Expr)) :
    CheckCM (List (ConstantVal × TargetMajor × List Expr)) :=
  thenConform
    (targetRecCheck (shadowOpsC mode) fe p.toBlockShape nested aux block cvTas ctorsAs)
    (if conf then
      flushC *> checkBlockRecConformF (sharedOpsC mode fe) structWalkersC fe none p block cvTas
        ctorsAs nfs
    else pure ())

/-- The rule-less recursor environment the recursor stage built, offered
to the conformance check (`FEnv.pushRecBare`): at ONE recursor, its
record and the environment holding it; `none` otherwise. -/
def recBareHint (p : BlockShape) (cvRas : List (ConstantVal × Nat)) (feR : FEnv) :
    Option (ConstantVal × Nat × Nat × FEnv) :=
  match cvRas with
  | [(cv, _)] => some (cv, p.majorIdxAt 0, p.rulePrefixAt 0, feR)
  | _ => none

/-- **`checkBlockRecS` as it runs** (`@[csimp]`
`checkBlockRecS_eq_fast`): the check's stages inline, so that the
rule-less recursor environment `feR` it builds is still in hand when the
conformance check runs, which then reuses it (`recBareHint`) where it
would push the same record onto `fe` again.  That push is onto the
constructors' index while the caller (`checkBlockTailS`) still holds it
for the install that follows, so it copied the whole index — once per
one-member block.  When the generated recursor type differs from the
stream's, the conformance check pushes as before. -/
def checkBlockRecSFast (fe : FEnv) (p : BlockParts) (nested conf : Bool)
    (aux : NestNodes)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (nfs : List (List Expr)) :
    CheckCM (List (ConstantVal × TargetMajor × List Expr)) := do
  targetRecPins (m := CheckCM) p.toBlockShape block
  let tys ← targetRecTys ((shadowOpsC mode).opsAt fe) fe p.toBlockShape nested aux cvTas
    ctorsAs p.recs
  let us := tys.map (·.2.2)
  checkBlockRecSmallElim (m := CheckCM) p.toBlockShape
    (nested || tys.any (fun t => t.2.1.member.isNone)) us
  checkBlockRecElimPin (m := CheckCM) p.toBlockShape us
  checkBlockRecPrefixAgree ((shadowOpsC mode).opsAt fe) fe.env p.toBlockShape (tys.map (·.1))
  targetRulePinsAll (m := CheckCM) tys (targetRecRules block)
  let cvRas := tys.map fun t => (t.1, t.2.1.nIdx)
  let feR := consBlockRecsBareF p.toBlockShape 0 cvRas fe
  let out ← targetRecsRules ((shadowOpsC mode).opsRuleR feR) (shadowOpsC mode).walkers feR
    ((shadowOpsC mode).opsAt fe) fe p.toBlockShape (cvTas.map (·.type))
    (targetFamilyOf p.toBlockShape tys) p.recs tys
  (shadowOpsC mode).flush
  if conf then
    flushC
    checkBlockRecConformF (sharedOpsC mode fe) structWalkersC fe
      (recBareHint p.toBlockShape cvRas feR) p block cvTas ctorsAs nfs
  pure out

/-- The hint `checkBlockRecSFast` offers is the environment the push
would build, so the conformance check reads the same environment. -/
theorem checkBlockRecConformF_recBareHint {m : Type → Type} [Monad m]
    [MonadExceptOf CheckError m] (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv)
    (q : BlockShape) (cvRas : List (ConstantVal × Nat)) (p : BlockParts)
    (block : List ConstantInfo) (cvTas : List ConstantVal)
    (ctorsAs : List (List (ConstantVal × Nat))) (nfs : List (List Expr)) :
    checkBlockRecConformF ops w fe (recBareHint q cvRas (consBlockRecsBareF q 0 cvRas fe)) p
      block cvTas ctorsAs nfs = checkBlockRecConformF ops w fe none p block cvTas ctorsAs nfs := by
  have hv : ∀ cv' mI' rP' feH,
      recBareHint q cvRas (consBlockRecsBareF q 0 cvRas fe) = some (cv', mI', rP', feH) →
      feH = fe.push (.recInfo cv' mI' rP' []) := by
    intro cv' mI' rP' feH h
    unfold recBareHint at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      rfl
    · exact nomatch h
  unfold checkBlockRecConformF
  split
  · simp only [checkNativeRecF_hint ops w fe hv]
  · rfl

@[csimp] theorem checkBlockRecS_eq_fast : @checkBlockRecS = @checkBlockRecSFast := by
  funext mode fe p nested conf aux block cvTas ctorsAs nfs
  unfold checkBlockRecS checkBlockRecSFast thenConform targetRecCheck
  cases conf <;>
    simp only [bind_assoc, seqRight_eq_bind, pure_bind, checkBlockRecConformF_recBareHint,
      Bool.false_eq_true, ↓reduceIte]

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
  let (kinds, nfs, nodes) ← checkBlockPositivity (sharedOpsC mode fe₁) fe₁.env fe₁.find?
    fe₁.env.consts pC cvTas ctorsAs
  pure ⟨fe₁, cvTas, pC, ctorsAs, sortsss, kinds, nfs, nodes⟩

/-- **`checkBlockTail` through the index**: one flush
entering the recursors' environment. -/
def checkBlockTailS (block : List ConstantInfo) (q : BlockPass FEnv) :
    CheckCM FEnv := do
  let p := q.p
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.k ∨ 2 ≤ p.numCtors) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  let _isorts ← checkBlockIdxSortsF (sharedOpsC mode q.env₁) q.env₁ p.toBlockShape
    (p.members.zip q.cvTas)
  let fe₂ := consBlockCtorsF p.nP q.ctorsAs q.env₁
  flushC
  let out ← checkBlockRecS mode fe₂ p (blockNestedBit p.toBlockShape q.kinds)
    (nestKindsFlat q.kinds) q.nodes block q.cvTas q.ctorsAs q.nfs
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
