module

public import ConLeche.Kernel.Inductives.SumInstall
public import ConLeche.Kernel.Inductives.NativeParts

@[expose] public section

/-!
# The direct recursive install (pure fueled checker; task #188)

The install stages of a block recognised by `nativeParts?`
(`ConLeche/Kernel/Inductives/NativeParts.lean`).  The former's and the
constructors' stages are the sum route's, verbatim
(`checkSumInd`, `checkSumCtors`): the constructors are
checked at the environment holding the former, with the pre-block
resolution guard pointed at THAT environment so that the recursive
fields `T p⃗` pass it; what the sum route's guard bought — no field
domain mentions the block — is replaced by the positivity
classification, re-checked on the annotated types after the stage
(`nativeFieldsOk`: every field is ordinary, resolving in the
pre-block environment, or exactly the family at the parameters).
The recursor stage generates the type with the inductive-hypothesis
binders (`structRecTyR`), compares it with the stream's by one closed
`isDefEq` (task #175 S2), and generates the rules (`structRecRhsR`);
the rules mention the recursor itself, so they are scope-checked at
the environment holding its constant and NOT inferred — the official
kernel infers no rule either; the P tier grades the generated form
from the leaf's own laws.

Front guards, in the official kernel's order: positivity (a
non-positive occurrence is `.invalid`, an unsupported positive one
`.notImplemented`), the elimination restriction
(`elim_only_at_universe_zero`: a large eliminator on a block whose
sort may be `Prop` is `.invalid` at two or more constructors; at one
constructor it is the subsingleton case, taken with the per-field
criterion at `checkStructFieldSortsI` — the recursive squash regime's
large eliminator, task #202 Stage A2), the constructors' distinct
names.

**The recursor pin is the LAST of the block's checks** (task #220):
everything the stream's recursor RECORD claims — its name, its level
parameters, its argument sums, its rules — is compared at
`checkNativeRec`/`nativeRulesOk`, where a mismatch is `.invalid`,
and none of it is a condition of recognition.  Official never reads the
exported recursor as an input either: `add_inductive` generates one and
the replay compares the record with it structurally
(`checkPostponedRecursors`, `Lean4Checker/Replay.lean` — "Invalid
recursor", "No such recursor").  So a block whose recursor record is a
stub is rejected by its own type and constructors, with official's
message, instead of being declined for a recursor this route was going
to generate anyway.  The index-threaded twins are
`ConLeche/Kernel/Inductives/NativeInstallF.lean`.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- The capabilities a block on the fixpoint route earns (task #210
Part A): at a STRUCTURE-LIKE block — one constructor, no index, and NO
recursive or reflexive field: official's `is_structure_like` is
`ncnstrs == 1 && nindices == 0 && !is_rec` (kernel/inductive.cpp), and
its `try_eta_struct` / `is_def_eq_unit_like` fire nowhere else —
structure eta at a non-`Prop` sort (the tagged tower's own elimination
law: a member is the constructor at its projections) and
unit-likeness when the constructor has no field (the fibre is then the
one tagged empty tuple); rule K exactly at official's `is_K_target` (a
`Prop` result, one constructor taking only the parameters — at any
index count, as at the sum route's `Eq`); nothing at any other block.
The projection TABLE (`checkNativeTable`) does not depend on this
record: official's `infer_proj` types `.proj` on any one-constructor
index-free family, recursive or not.  At a FIELDLESS constructor the
record claims BOTH unit-likeness and η, as official's `is_structure_like`
does: the recursor's major-premise rescue (`Core.lean`, the
`etaFields = 0` arm — arena `073_typeSingletonRecReduction`) keys on η,
and the η law owed there is the constructor at the parameters
(`FixZeroFieldP.fixFibreEtaLaw0`).  (Granting η at a recursive
structure-like was tried and is UNSOUND IN PRACTICE though sound in
the model: on `ind_nest_via_refl` the tool's nested model over a
reflexive `W1 α = sup (a : α) (f : Nat → W1 α)` made `isDefEq` spin
through η-expansion — official's `!is_rec` is load-bearing.)  On the
sum route's domain (never one constructor without an index) this is
`sumCaps`. -/
def nativeCaps (p : NativeParts) : IndCaps :=
  match p.ctors with
  | [c] =>
    { eta := p.nIdx == 0 && !p.isProp &&
        !(p.kinds.any fun ks => ks.any fun k => k == .recursive || k == .reflexive)
      etaCtor := c.1.name
      etaParams := p.nP
      etaFields := c.2
      unitlike := p.nIdx == 0 && c.2 == 0
      unitParams := p.nP
      ruleK := c.2 == 0 && p.isProp
      sortZ := Level.zeronessOf p.resSort }
  | _ => {}

/-- The fixpoint route stores the family's own result-sort datum: the
former's telescope ends in `Sort p.resSort`, so the record's `sortZ`
is `piResultZ` of the type the install stores (`capsNeverZero_eq`). -/
theorem nativeCaps_sortZ {p : NativeParts} {c : ConstantVal × Nat}
    {e : Expr} (hc : p.ctors = [c]) (he : e.piResult = .sort p.resSort) :
    (nativeCaps p).sortZ = piResultZ e := by
  unfold nativeCaps piResultZ
  rw [hc, he]

/-- Does the variable `q` occur as a leaf of `e` (annotations
included, as `fvarLeaves` walks them)? -/
def Expr.mentionsFvar (q : Nat) (e : Expr) : Bool := e.fvarLeaves.any fun l => l.1 == q

/-- The kinds the recogniser computed, re-checked on the annotated
constructor type OPENED at variables (`openPisAtFvars`, as the stage
read it): an ordinary field's domain resolves in the pre-block
environment `env₀`; a recursive field's domain is the family at the
opened parameter variables followed by `nIdx` index expressions
resolving in `env₀`, and the variable occurs in no later field's
domain nor in the residual (the model reads those at a frame whose
recursive slots hold an arbitrary member of the family being defined);
the residual's index expressions resolve in `env₀`. -/
def nativeOpenedOk (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (cty : Expr) (nF : Nat) (ks : List RecFieldKind) : Bool :=
  match openPisAtFvars nP cty 0 with
  | some (fvsP, crest) =>
    match openPisAtFvars nF crest nP with
    | some (xFvs, xrest) =>
      (xrest.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
      (List.range nF).all fun i =>
        match xFvs[i]?, ks.getD i .ordinary with
        | some x, .ordinary => x.fvarTypeD.constsResolve env₀
        | some x, .recursive =>
          x.fvarTypeD.getAppFn == Expr.const T (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdx &&
          (x.fvarTypeD.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | some x, .reflexive =>
          -- the field's own telescope, OPENED at variables at the field's
          -- depth (as the constructor's was): its domains resolve in
          -- `env₀` (so they are free of the block), its body is the family
          -- at the parameter variables and `nIdx` index expressions
          -- resolving in `env₀` (task #202)
          match openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | some (afvs, body) =>
            afvs.length != 0 &&
            afvs.all (fun a => a.fvarTypeD.constsResolve env₀) &&
            body.getAppFn == Expr.const T (lps.map .param) &&
            body.getAppArgs.take nP == fvsP &&
            body.getAppArgs.length == nP + nIdx &&
            (body.getAppArgs.drop nP).all (fun e => e.constsResolve env₀) &&
            !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
            !xrest.mentionsFvar (nP + i)
          | none => false
        | _, _ => false
    | none => false
  | none => false

/-- The kinds, re-checked on every annotated constructor
(`nativeOpenedOk`), one kind list per constructor, one kind per
field. -/
def nativeFieldsOk (env₀ : Env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) : Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 && nativeOpenedOk env₀ T lps nP nIdx cA.1.type cA.2 ks
    | _, _ => false

/-- The generated rules for constructors `j, j+1, …` (`k` of them),
each scoped at the environment holding the recursor's constant
(`envR`): a rule mentions the recursor and is not inferred. -/
def checkNativeRules (envR : Env) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (structRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless rhs.allLevelParamsDefined rlps && rhs.constsResolve envR &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct rec: recursor rule scoping")
    let rest ← checkNativeRules envR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- Stage 3: the recursor, generated and compared — the generated
type has the inductive-hypothesis binders in each minor
(`structRecTyR`); the generated rules are scoped at the environment
holding the recursor's constant. -/
def checkNativeRec (ops : CheckerOps m) (env : Env) (p : NativeParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  -- THE RECURSOR PIN (task #220), split off the type-and-constructor
  -- gate above and thrown here: official generates the recursor and its
  -- replay compares the exported record with the generated one
  -- structurally, so a record naming something other than the generated
  -- `T.rec` ("No such recursor") or contradicting it in its argument
  -- sums or its rules ("Invalid recursor") is INVALID INPUT
  unless p.cvR.name == p.cvT.name.str "rec" do
    throw (.invalid "direct rec: the block's recursor is not the generated T.rec")
  unless nativeRecLpsOk p.toInductiveShape do
    throw (.invalid "direct rec: the recursor's level parameters are not the generated ones")
  unless p.recPinned do
    throw (.invalid "direct rec: the recursor record is not the generated recursor")
  let cvRi ← checkConstantVal ops env p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := nativeCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (structRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && recTy.constsResolve env &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct rec: recursor type scoping")
  let sty ← ops.inferType env 0 recTy
  let _u ← ops.ensureSort env 0 sty
  -- the stream's recursor is the generated one
  unless ← ops.isDefEq env 0 cvRi.type recTy do
    throw (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : ConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let envR : Env := ⟨.recInfo cvRa p.majorIdx p.rulePrefix [] :: env.consts⟩
  let rhss ← checkNativeRules envR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name (p.cvR.levelParams.map .param) ctors.length 0
  pure (cvRa, rhss)

/-- Stage 4 (task #210 Part A): **the projection table** at a
STRUCTURE-LIKE block — one constructor, no index — the direct
structure route's table (`checkStructProjTable`: the fields' bodies
off the annotated constructor type, the guard levels from the
constructors' stage's field sorts) at the TAGGED tower's projection
offset `1` (`ProjTable.off`: the carrier's first pair component is
the constructor tag); nothing at any other block. -/
def checkNativeTable (p : NativeParts) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (env : Env) : m Env :=
  match ctorsA, sortss with
  | [cA], [sorts] =>
    if p.nIdx == 0 then
      checkStructProjTable p.cvT.name cA.1.name p.cvT.levelParams p.nP cA.2 p.resSort
        (structProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 env
    else pure env
  | _, _ => pure env

/-- **The fields' kinds, classified at install** (task #210 Part D) on
the stored constructors — their field domains normalised by official's
positivity walk (`normCtorVal`), so the syntactic classification
(`recCtorKinds`) is official's: a non-positive or non-valid occurrence
is INVALID (official's "non positive occurrence", "non valid
occurrence", "invalid return type"), a nested occurrence — the one
positive occurrence the route does not model — a positive decline. -/
def classifyFixKinds (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) : m (List (List RecFieldKind)) := do
  let kinds ← unwrapOr (ctorsA.mapM (recCtorKinds T lps nP nIdx))
    (.notImplemented "direct rec: constructor telescope")
  if kinds.any (fun ks => ks.any (· == .negative)) then
    throw (.invalid "direct rec: non positive or non valid occurrence of the inductive type")
  if kinds.any (fun ks => ks.any (· == .unsupported)) then
    throw (.notImplemented "direct rec: a nested occurrence of the block (not modeled here)")
  pure kinds

/-- Check and install a **direct recursive block**: positivity, the
elimination restriction, the distinct names, the former (with the
block's capability record, `nativeCaps`), the constructors (at the
former's environment), the kinds re-checked, the recursor with its
rules, and — at a structure-like block — the projection table
(`checkNativeTable`, task #210 Part A). -/
def checkNative (ops : CheckerOps m) (env : Env) (p₀ : NativeParts) : m Env := do
  unless (p₀.ctors.map (·.1.name)).Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  -- THE PROVISIONAL PASS (task #210 Part D): the block's capability
  -- record (`nativeCaps`) needs the fields' kinds — official's
  -- `is_rec` — and the kinds need the constructors normalised at an
  -- environment where the former resolves.  So the former is first
  -- installed with an EMPTY record in a throwaway environment, the
  -- constructors normalised and checked there, and the kinds
  -- classified from those; the real former then carries the record
  -- at the kinds, and every later stage runs on the completed record
  -- `p`.  (Official adds the whole block in one step; this is the
  -- same information in two.)
  let (envP, cvTaP, p₁P) ← checkSumInd ops env p₀.toInductiveShape (fun _ => {})
  let p₂P := p₀.complete p₁P
  let (ctorsP, _) ← checkSumCtors ops envP envP p₂P.cvT.name p₂P.cvT.levelParams p₂P.nP
    p₂P.nIdx p₂P.resSort p₂P.isProp p₂P.large cvTaP p₂P.ctors
  let kinds ← classifyFixKinds p₂P.cvT.name p₂P.cvT.levelParams p₂P.nP p₂P.nIdx ctorsP
  -- the former's run completes the record with the sort it read
  -- (task #195: a former declared at a definition that only unfolds
  -- to its telescope); every later stage runs on the completed record
  -- `p`, whose capability record the former already carries
  let (env₁, cvTa, p₁) ← checkSumInd ops env p₀.toInductiveShape
    (fun p₁ => nativeCaps ((p₀.complete p₁).withKinds kinds))
  let p := (p₀.complete p₁).withKinds kinds
  -- a large eliminator on a block whose sort may be `Prop`: two or more
  -- constructors is `.invalid` (official's `elim_only_at_universe_zero`);
  -- one constructor is the subsingleton case, taken (task #202 Stage
  -- A2) with the per-field criterion at `checkStructFieldSortsI`
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  -- the index binders' universes, exposed for the model's index-tuple
  -- universe: the former's telescope opened at variables, each index
  -- domain's sort inferred (no bound is checked — `isProp` set,
  -- `large` unset — the sorts are read, not compared)
  let tq ← unwrapOr (openPisAtFvars (p.nP + p.nIdx) cvTa.type 0)
    (.internal "direct rec: type former telescope")
  let _isorts ← checkStructFieldSortsI ops env₁ true false p.resSort p.nP (tq.1.drop p.nP) []
    p.nIdx
  -- the constructors' field domains may mention the block: the
  -- resolution guard is pointed at the former's environment; the kinds
  -- classified at the provisional pass are re-checked on the stored
  -- (normalised) constructors
  let (ctorsA, sortss) ← checkSumCtors ops env₁ env₁ p.cvT.name p.cvT.levelParams p.nP
    p.nIdx p.resSort p.isProp p.large cvTa p.ctors
  unless nativeFieldsOk env p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA p.kinds do
    throw (.internal "direct rec: field kinds")
  -- the stream's rules are the generated ones (official's replay
  -- compares the exported recursor structurally with its own)
  unless nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP p.ctors.length
      ctorsA p.kinds p.rhss do
    throw (.invalid "direct rec: recursor rules are not the generated ones")
  let env₂ := consSumCtors p.nP ctorsA env₁
  let (cvRa, rhss) ← checkNativeRec ops env₂ p cvTa ctorsA
  checkNativeTable p ctorsA sortss ⟨.recInfo cvRa p.majorIdx p.rulePrefix
    (sumRules env₂.find? cvRa.name p.nP p.majorIdx p.rulePrefix cvRa.type
      ctorsA rhss) :: env₂.consts⟩

end ConLeche
