module

public import ConLeche.Kernel.Inductives.NestedElim
public import ConLeche.Kernel.Inductives.MutualInstall

@[expose] public section

/-!
# `restore_nested` and the nested install (task #279)

The second half of the nested route.  The auxiliary mutual declaration
produced by `elimNested` is checked by task #278's mutual installer
(`checkMutualCore`) in a SCRATCH environment — the block's own types
with their nesting eliminated, plus the mimics, are an ordinary mutual
block, and everything official checks of a nested block it checks
there: the same-universe condition (a `Type` block through a `Prop`
container rejects), positivity with `whnf` on the copied fields
(official's dynamic nesting), the universe bounds, the index
occurrences, `elim_only_at_universe_zero` at two or more types (so a
nested `Prop` block gets the small eliminator), the constructors'
return types.

Then the nesting is RESTORED (official's `restore_nested`): in the
constructor types, the recursor types and the rule right-hand sides
every `auxJ p⃗ is` becomes `J Ds is` and every `auxJ.c p⃗` becomes
`J.c Ds`, the mimics' recursors are renamed to `<first member>.rec_k`,
and the mimics' rules get their constructor names back.  Only the
restored constants are stored; the scratch environment is dropped, and
since a stream may not name a `_nested` constant the declarations that
follow see exactly official's environment.

Three post-checks close the holes the copies would leave (official's,
in official's order):

* **(o)** the copies' REFERENCE RELATION is computed and topologically
  sorted (`nestedTopoOrder`, DESIGN §M.22): the order the model's
  forward fold recurses along, with a cyclic block a positive DECLINE;
* **(a′′)** every pin, abstracted over the block's parameters, is FREE
  OF free variables and has its loose bound variables within the
  parameter telescope (`pinsClosed`) — the pair `ConstWF` demands of a
  nested RULE's stored pins, and the only certificate these have;
* **(a)** every pin `I Ds` is type-checked at the block's parameter
  context in the RESTORED environment (leanprover/lean4#14577 — the
  parametric arguments do not appear in the auxiliary declaration, so
  they would otherwise escape type checking; the arena's
  `nested-unused-param`), and — `pinsOkAux`, for the model tier — at the
  SCRATCH environment as well, where the two fold spellings need the
  pins to fit the container's parameter telescope;
* **(b)** the restored constructor types, recursor types and rule
  right-hand sides are re-checked (leanprover/lean4#14621 — "not
  necessary … added to catch bugs"; here it is also where the stored
  terms earn their `EnvWF` facts);
* **(a′)** every name the elimination MINTS — each copy's type, its
  constructors and its recursor — is free in the PRE-BLOCK environment
  (`copiesFresh`; official's `check_name` at `declare_inductive_types`),
  so that the scratch environment's cons shadows nothing;
* **(c)** the stream's `k + numNested` recursor records are compared
  with the restored generated ones — the types by one `isDefEq` each,
  the rules structurally — as the fixpoint and mutual routes compare
  theirs, and as official's replay does (`checkPostponedRecursors`).  A
  missing, extra or different record REJECTS.

**This route is not on the fold's dispatch yet.**  Until the model
tier's `declNested` exists a nested block still reaches the modelled
route; `checkNested` runs in SHADOW beside it (`Main.lean`,
`--shadow-nested`), and its verdict is compared with the modelled
route's on the fixtures, on init-full and on the Mathlib nested cone.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- Lift a pure elimination result into the checker monad. -/
def nestedLift {α : Type} (r : Except CheckError α) : m α :=
  match r with
  | .ok a => pure a
  | .error err => throw err

/-! ## The restore -/

/-- Everything `restore_nested` needs: the block's parameter count, the
mimic types' pins (in the `Π p⃗` context), the mimic constructors' pins
with their restored names, and the mimic recursors' new names. -/
structure RestoreTbl where
  nP : Nat
  /-- `auxJ ↦ J Ds`, the pin in the block's parameter context -/
  pins : List (Name × Expr)
  /-- `auxJ.c ↦ (J Ds, J.c)` -/
  ctorPins : List (Name × Expr × Name)
  /-- `auxJ.rec ↦ T₁.rec_k` -/
  recMap : List (Name × Name)
  /-- every name the replace can fire on: the three maps' keys.  A
  subterm mentioning none of them is its own restoration, which is what
  lets the walk dismiss a DAG-shared subterm in one memoized
  `mentionsConst` pass (the task #215 discipline). -/
  auxNames : List Name
  deriving Repr, Inhabited

/-- The node step of official's `restore_nested` replace: `some e'` —
the node is replaced and its children are NOT visited (official's
`replace` returns the value as is); `none` — descend.  `d` is the
number of binders below the parameter prefix, by which a pin is
lifted. -/
def restoreNode (R : RestoreTbl) (d : Nat) (e : Expr) :
    Except CheckError (Option Expr) :=
  let head : Except CheckError (Option Expr) :=
    match e.getAppFn with
    | .const n _ =>
      let args := e.getAppArgs
      match R.pins.lookup n with
      | some pin =>
        if args.length < R.nP then
          .error (.invalid "failed to restore nested inductive types, auxiliary type is \
            not applied to all parameters")
        else .ok (some (Expr.mkAppN (pin.liftLooseBVars d 0) (args.drop R.nP)))
      | none =>
        match R.ctorPins.find? (fun q => q.1 == n) with
        | some (_, pin, newName) =>
          if args.length < R.nP then
            .error (.invalid "failed to restore nested inductive types, auxiliary \
              constructor is not applied to all parameters")
          else
            let nested := pin.liftLooseBVars d 0
            match nested.getAppFn with
            | .const _ ilvls =>
              .ok (some (Expr.mkAppN (Expr.mkAppN (.const newName ilvls) nested.getAppArgs)
                (args.drop R.nP)))
            | _ =>
              .error (.invalid "failed to restore nested inductive types, nested \
                occurrence is not an inductive type application")
        | none => .ok none
    | _ => .ok none
  match e with
  | .const n us =>
    match R.recMap.lookup n with
    | some n' => .ok (some (.const n' us))
    | none => head
  | _ => head

/-- The replace itself: top-down, children only where the node step
declines. -/
def restoreWalk (R : RestoreTbl) : Nat → Expr → Except CheckError Expr
  | d, e =>
    -- the prune (see `RestoreTbl.auxNames`)
    if !R.auxNames.any (fun n => e.mentionsConst n) then .ok e else
    match restoreNode R d e with
    | .error err => .error err
    | .ok (some e') => .ok e'
    | .ok none =>
      match e with
      | .app f a =>
        match restoreWalk R d f with
        | .error err => .error err
        | .ok f' =>
          match restoreWalk R d a with
          | .error err => .error err
          | .ok a' => .ok (.app f' a')
      | .lam ty b bm =>
        match restoreWalk R d ty with
        | .error err => .error err
        | .ok ty' =>
          match restoreWalk R (d + 1) b with
          | .error err => .error err
          | .ok b' => .ok (.lam ty' b' bm)
      | .forallE ty b bm =>
        match restoreWalk R d ty with
        | .error err => .error err
        | .ok ty' =>
          match restoreWalk R (d + 1) b with
          | .error err => .error err
          | .ok b' => .ok (.forallE ty' b' bm)
      | .letE ty v b =>
        match restoreWalk R d ty with
        | .error err => .error err
        | .ok ty' =>
          match restoreWalk R d v with
          | .error err => .error err
          | .ok v' =>
            match restoreWalk R (d + 1) b with
            | .error err => .error err
            | .ok b' => .ok (.letE ty' v' b')
      | .proj s i x =>
        match restoreWalk R d x with
        | .error err => .error err
        | .ok x' => .ok (.proj s i x')
      | _ => .ok e

/-- Strip the leading `nP` binders, each a `∀` or a `λ` (official's
`restore_nested` prologue: "fewer binders than parameters" otherwise),
keeping their domains and binder data. -/
def stripPisOrLams : Nat → Expr → Option (List (Expr × BinderMeta) × Expr)
  | 0, e => some ([], e)
  | k + 1, .forallE ty b bm => (stripPisOrLams k b).map fun q => ((ty, bm) :: q.1, q.2)
  | k + 1, .lam ty b bm => (stripPisOrLams k b).map fun q => ((ty, bm) :: q.1, q.2)
  | _ + 1, _ => none

/-- **`restore_nested`**: the leading `nP` binders are consumed, the
body replaced, and the telescope rebuilt as `∀`s when the term started
with one and as `λ`s otherwise (official's `pi` flag). -/
def restoreNested (R : RestoreTbl) (e : Expr) : Except CheckError Expr :=
  let isPi := match e with | .forallE .. => true | _ => false
  match stripPisOrLams R.nP e with
  | none =>
    .error (.invalid "failed to restore nested inductive types, fewer binders than \
      parameters")
  | some (bs, body) =>
    match restoreWalk R 0 body with
    | .error err => .error err
    | .ok body' =>
      .ok (bs.foldr (fun (b : Expr × BinderMeta) acc =>
        if isPi then .forallE b.1 acc b.2 else .lam b.1 acc b.2) body')

/-! ## The mimic rules' fire -/

/-- **The nested-shape data of a mimic rule** — `nestedRuleShape`
(`Kernel/Inductives/Modeled.lean`) MINUS its `_model.iota_j` lookup,
which is the modelled route's licence and has no counterpart here: the
constructor's level and parameter instantiations, read off the restored
recursor type's major-premise domain `∀ …prefix… …indices…, ∀ (t :
D.{lvls} p₁ … p_cnP i₁ … i_k), …`.  The instantiations are stored
LOWERED into the rule-prefix context; the lift-back roundtrip certifies
that no index variable occurs in them, and the syntactic guards are the
facts `EnvWF`'s stored-rule clause records. -/
def nestedFireShape (envSelf : Env) (lps : List Name) (tyA : Expr) (mI rP cnP : Nat) :
    Option (List Level × List Expr) :=
  if rP ≤ mI then
    match tyA.stripPis mI with
    | some (_, .forallE dom _ _) =>
      match dom.getAppFn with
      | .const _D lvls =>
        let args := dom.getAppArgs
        let k := mI - rP
        let pins := (args.take cnP).map (Expr.lowerBVars k 0)
        if args.length = cnP + k ∧
            args.take cnP == pins.map (Expr.liftLooseBVars k 0) ∧
            args.drop cnP ==
              (List.range k).map (fun i => Expr.bvar (k - 1 - i)) ∧
            pins.all (fun q => !q.hasFvar && q.looseBVarsBounded rP &&
              q.constsResolve envSelf && q.allLevelParamsDefined lps) ∧
            lvls.all (Level.allParamsDefined lps) then
          some (lvls, pins)
        else none
      | _ => none
    | _ => none
  else none

/-! ## The block record of the auxiliary declaration -/

/-- The index count of an auxiliary type: what is left of its declared
telescope once the block's parameters are peeled.  A copy's type is
`Π p⃗, J's type at the pins`, a syntactic telescope ending in a sort by
construction. -/
def auxIdxCount (nP : Nat) (ty : Expr) : Option Nat :=
  match ty.piBinders with
  | (bs, .sort _) => if nP ≤ bs.length then some (bs.length - nP) else none
  | _ => none

/-- The auxiliary mutual block, as `checkMutualCore` takes it. -/
def auxBlock (p : NestedParts) (st : ElimState) : Option MutualBlock := do
  let formers ← st.types.mapM fun t => do
    let nIdx ← auxIdxCount p.nP t.type
    pure ((⟨t.name, p.lps, t.type⟩ : ConstantVal), nIdx)
  let ctors := (st.types.zipIdx.map fun (t, mIdx) =>
    t.ctors.map fun c =>
      (⟨⟨c.1, p.lps, c.2.1⟩, c.2.2, mIdx⟩ : MutualCtor)).flatten
  pure ⟨formers, ctors, p.nP, p.lps, p.large, p.elim⟩

/-- The restore table of an elimination: the mimics' pins in the `Π p⃗`
context, their constructors' pins and restored names, and the mimic
recursors' stored names (`mk_aux_rec_name_map`: `<first member>.rec_k`
in creation order). -/
def restoreTbl (p : NestedParts) (st : ElimState) : RestoreTbl :=
  { nP := p.nP
    pins := st.pins.map fun q => (q.aux, Expr.abstractRange q.pin 0 p.nP 0)
    ctorPins := (st.types.drop p.k).zipIdx.map (fun (t, j) =>
        match st.pins[j]? with
        | some q =>
          t.ctors.map fun c =>
            (c.1, Expr.abstractRange q.pin 0 p.nP 0,
              Name.replacePrefix q.aux q.container c.1)
        | none => []) |>.flatten
    recMap := (st.pins.zipIdx.map fun (q, j) => (q.aux.str "rec", p.mimicRecName j))
    auxNames := st.pins.map (fun q => q.aux)
      ++ (st.types.drop p.k).flatMap (fun t => t.ctors.map (·.1))
      ++ st.pins.map (fun q => q.aux.str "rec") }

/-! ## The install -/

/-- The stored members of the auxiliary block, read back out of the
scratch environment: the annotated former, its capability record, its
constructors and its recursor with its rules. -/
structure AuxStored where
  cvTa : ConstantVal
  caps : IndCaps
  nIdx : Nat
  ctors : List (ConstantVal × Nat × Nat)
  cvRa : ConstantVal
  mI : Nat
  rP : Nat
  rules : List RecRule
  tbl : Option ProjTable
  deriving Repr, Inhabited

/-- Read one auxiliary member back out of the scratch environment. -/
def auxStored? (envAux : Env) (b : MutualBlock) (mIdx : Nat) : Option AuxStored := do
  let (cv, nIdx) ← b.formers[mIdx]?
  let .indInfo cvTa caps := (← envAux.find? cv.name) | none
  let .recInfo cvRa mI rP rules := (← envAux.find? (cv.name.str "rec")) | none
  let ctors ← (b.ownCtors mIdx).mapM fun (_, c) => do
    let .ctorInfo cvCa nP nF := (← envAux.find? c.cv.name) | none
    pure (cvCa, nP, nF)
  let tbl : Option ProjTable :=
    match envAux.find? (projTableName cv.name) with
    | some (.projInfo t) => some t
    | _ => none
  pure ⟨cvTa, caps, nIdx, ctors, cvRa, mI, rP, rules, tbl⟩

/-- **The copies' types, re-minted at ANNOTATED pin components**
(DESIGN §M.21 (A), task #279 K.8 steps (1) and (2)).

`elimNested` mints a copy from the container's STORED (annotated) type
instantiated at the pin's components, and those components are RAW
sub-terms of the stream's constructor types — the export carries no
binder datum at all, so every binder of a stream term arrives with the
parse placeholder.  The aux install's annotation pass then REWRITES the
data inside them, and the stored copy type is not the minted one.

So the components are annotated FIRST, here, by the same pass at the
smaller environment — the pre-block constants plus the block's formers,
which is all a component can mention (`checkMutualCtor` resolves a
field domain there and a pin is a sub-term of one) — and the copy's type
is re-minted from the container's stored annotated type at the
ANNOTATED components, with the block's first former's ANNOTATED
parameter binders (premise B).  The copy's type is then annotated
throughout, so the aux install's own pass keeps every written datum and
recomputes the `.never` ones to `.never`.

The components' TYPING still happens after the install — but on THESE
components: the annotated open pin is RETURNED beside the types, and
both pin passes (`pinsOkAux` at `envAux`, post-check (a) at the restored
environment) infer that very term instead of annotating the raw pin
again (the `checkConstantValPre` discipline: a datum we built ourselves
is VALIDATED, by inference, not recomputed).  So the components are one
syntactic object everywhere, and the recorded equation has one form —
this one. -/
def remintCopyTypes (ops : CheckerOps m) (envF : Env) (nP : Nat)
    (fvsA : List Expr) (pbsA : List (Expr × BinderMeta)) (env : Env) :
    List NestedPin → List AuxType → m (List AuxType × List (NestedPin × Expr))
  | [], ts => pure (ts, [])
  | q :: qs, ts => do
    let pinB := Expr.abstractRange q.pin 0 nP 0
    let pinA ← ops.annotate envF nP (Expr.instantiateList pinB fvsA.reverse)
    let ts' ←
      match pinA.getAppFn, containerInfo? env q.container with
      | .const _ lvls, some ci =>
        match ci.members.find? (fun J => J.name == q.container) with
        | some J =>
          if lvls.length == J.lps.length then
            match Expr.instPis (Expr.instantiateLevelParams J.lps lvls J.type)
                (pinA.getAppArgs) with
            | some tyI =>
              pure (ts.map fun t =>
                if t.name == q.aux then { t with type := closeTelescope pbsA 0 tyI } else t)
            | none => pure ts
          else pure ts
        | none => pure ts
      | _, _ => pure ts
    let (ts'', qs') ← remintCopyTypes ops envF nP fvsA pbsA env qs ts'
    pure (ts'', (q, pinA) :: qs')

/-- **The elimination's state with the copies' types re-minted at
ANNOTATED pin components** (K.8 steps (1) and (2)): the first former's
type is annotated, its parameter binders `pbsA` and openers `fvsA₀` are
taken from it, and every copy's type is rebuilt by `remintCopyTypes`.
The pins, their order and the copies' constructors are untouched, so
every guard downstream sees the state the elimination produced; the
ANNOTATED open pins come back beside the state, paired with the pins
they belong to, and they are what the two pin passes type-check. -/
def nestedRemint (ops : CheckerOps m) (env : Env) (p : NestedParts) (st : ElimState) :
    m (ElimState × List (NestedPin × Expr)) := do
  let cv₀ ← unwrapOr (p.formers.head?.map (·.1)) (.internal "nested: no former")
  let t₀A ← ops.annotate env 0 cv₀.type
  let (fvsA₀, _) ← unwrapOr (openPisAtFvars p.nP t₀A 0)
    (.invalid "invalid inductive datatype declaration, incorrect number of parameters")
  let (pbsA, _) ← unwrapOr (t₀A.stripPis p.nP)
    (.invalid "invalid inductive datatype declaration, incorrect number of parameters")
  let envF : Env :=
    ⟨(p.formers.map fun f => ConstantInfo.indInfo f.1 {}).reverse ++ env.consts⟩
  let (typesA, pinsA) ← remintCopyTypes ops envF p.nP fvsA₀ pbsA env st.pins st.types
  pure ({ st with types := typesA }, pinsA)

/-- The block's own members' stored records, in member order, then the
mimics' (whose only stored part the restore keeps is the recursor). -/
def auxStoredAll (envAux : Env) (b : MutualBlock) : Nat → Option (List AuxStored)
  | 0 => some []
  | k + 1 => do
    let earlier ← auxStoredAll envAux b k
    let a ← auxStored? envAux b k
    pure (earlier ++ [a])

/-- The restored constructors of one member, re-checked at the
environment holding the block's formers (post-check (b)). -/
def restoreCtors (ops : CheckerOps m) (env : Env) (R : RestoreTbl) (lps : List Name) :
    List (ConstantVal × Nat × Nat) → m (List (ConstantVal × Nat × Nat))
  | [] => pure []
  | (cvCa, nP, nF) :: rest => do
    let ty ← nestedLift (restoreNested R cvCa.type)
    let cvA ← checkConstantVal ops env { cvCa with levelParams := lps, type := ty }
    let rest' ← restoreCtors ops env R lps rest
    pure ((cvA, nP, nF) :: rest')

/-- The formers' conses (`consMutualFormers`' shape at the restored
block): the type and the capability record the AUXILIARY install
stored, official's unchanged re-add (our inductive records carry no
`all`, which is the only field official fixes). -/
def consNestedFormers : List AuxStored → Env → Env
  | [], env => env
  | a :: rest, env => consNestedFormers rest ⟨.indInfo a.cvTa a.caps :: env.consts⟩

/-- The constructors' conses (`consMutualCtors`' shape). -/
def consNestedCtors : List (ConstantVal × Nat × Nat) → Env → Env
  | [], env => env
  | (cv, nP, nF) :: cs, env => consNestedCtors cs ⟨.ctorInfo cv nP nF :: env.consts⟩

/-- The rules of one restored recursor: the right-hand sides restored
and re-checked (post-check (b)), the constructor names restored at a
MIMIC recursor (official's `restore_constructor_name`), the firing mode
computed — `.plain` for a member's own canonical rule, the certified
`.nested` shape for a mimic's. -/
def restoreRules (ops : CheckerOps m) (envR : Env) (R : RestoreTbl) (lps : List Name)
    (recName : Name) (isMimic : Bool) (recTy : Expr) (mI rP : Nat) :
    List RecRule → m (List RecRule)
  | [] => pure []
  | rl :: rest => do
    let rhs ← nestedLift (restoreNested R rl.rhs)
    let rhsA ← ops.annotate envR 0 rhs
    unless rhsA.allLevelParamsDefined lps && rhsA.constsResolve envR &&
        rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
      throw (.invalid s!"nested: the restored rule of {recName} does not scope")
    let _ty ← ops.inferType envR 0 rhsA
    let ctor : Name :=
      if isMimic then
        match R.ctorPins.find? (fun q => q.1 == rl.ctor) with
        | some (_, _, nm) => nm
        | none => rl.ctor
      else rl.ctor
    unless !isMimic || (R.ctorPins.any fun q => q.1 == rl.ctor) do
      throw (.invalid s!"failed to restore nested inductive types, '{rl.ctor}' is not a         constructor of an auxiliary type")
    let cnP : Nat :=
      match envR.find? ctor with
      | some (.ctorInfo _ n _) => n
      | _ => rl.ctorParams
    let fire : RecRuleFire :=
      if isMimic then
        match nestedFireShape envR lps recTy mI rP cnP with
        | some (lvls, pins) => .nested lvls pins
        | none => .inert
      else if Expr.recRulePlain recTy mI rP cnP then .plain else .inert
    let rest' ← restoreRules ops envR R lps recName isMimic recTy mI rP rest
    pure (recRuleBits envR.find? recName
      { rl with ctor := ctor, ctorParams := cnP, fire := fire, rhs := rhsA,
                paramsBlind := !isMimic } :: rest')

/-- The restored recursor types, re-checked at the environment holding
the block's formers and constructors (post-check (b)); the stream's
records are compared afterwards, against the stored result. -/
def restoreRecTys (ops : CheckerOps m) (env : Env) (R : RestoreTbl) (lps : List Name)
    (names : List Name) : List AuxStored → m (List ConstantVal)
  | [] => pure []
  | a :: rest => do
    let nm := names.headD a.cvRa.name
    let ty ← nestedLift (restoreNested R a.cvRa.type)
    let cvA ← checkConstantVal ops env ⟨nm, a.cvRa.levelParams, ty⟩
    let rest' ← restoreRecTys ops env R lps (names.drop 1) rest
    pure (cvA :: rest')

/-- The recursors provisioned rule-less, so that every rule is scoped
at the environment holding all of them (`provisionMutualRecs`). -/
def provisionNestedRecs : List (ConstantVal × Nat × Nat) → Env → Env
  | [], env => env
  | (cvRa, mI, rP) :: rest, env =>
    provisionNestedRecs rest ⟨.recInfo cvRa mI rP [] :: env.consts⟩

/-- The recursors stored with their restored rules. -/
def storeNestedRecs : List (ConstantVal × Nat × Nat × List RecRule) → Env → Env
  | [], env => env
  | (cvRa, mI, rP, rules) :: rest, env =>
    storeNestedRecs rest ⟨.recInfo cvRa mI rP rules :: env.consts⟩

/-- **Post-check (c)**: one stream recursor record against the restored
generated one — the name and the level parameters, the type by one
`isDefEq`, the rules structurally (official's replay,
`checkPostponedRecursors`). -/
def nestedRulesOk (nP k n : Nat) (recTy : Expr) (own : List (Nat × Nat))
    (srules grules : List RecRule) : Bool :=
  srules.length == grules.length && srules.length == own.length &&
  (List.range own.length).all fun j =>
    match srules[j]?, grules[j]?, own[j]? with
    | some a, some g, some (J, nF) =>
      a.ctor == g.ctor && a.nfields == g.nfields && a.nfields == nF &&
        mutualRulePrefixOk recTy nP k n J nF a.rhs &&
        (match a.rhs.stripLams (nP + k + n + nF), g.rhs.stripLams (nP + k + n + nF) with
         | some (_, ab), some (_, gb) => Expr.resetMeta ab == Expr.resetMeta gb
         | _, _ => false)
    | _, _, _ => false

/-- **Post-check (c)**: one stream recursor record against the restored
generated one — the name and the level parameters, the type by one
`isDefEq`, the rules structurally (official's replay,
`checkPostponedRecursors`).  As at the mutual route, the rule bodies
are compared under the `λ` prefix and the PREFIX is checked against the
stream's OWN recursor type (`mutualRulePrefixOk`): the copies' field
domains are stored NORMALISED (official's positivity walk `whnf`s them
too, but official keeps the declared spelling in the rule's binders), so
a redex pin — `DMap α (fun _ => PT α)`, whose copied field is
`(fun _ => PT α) k` — differs there and nowhere else. -/
def nestedRecOk (ops : CheckerOps m) (env : Env) (nP k n : Nat)
    (streamRec : ConstantVal × List RecRule) (own : List (Nat × Nat))
    (cvRa : ConstantVal) (rules : List RecRule) : m Unit := do
  let (cvR, srules) := streamRec
  unless cvR.name == cvRa.name && cvR.levelParams == cvRa.levelParams do
    throw (.invalid s!"nested: {cvR.name} is not the generated recursor")
  let cvRi ← checkConstantVal ops env cvR
  unless ← ops.isDefEq env 0 cvRi.type cvRa.type do
    throw (.invalid s!"nested: the type of {cvR.name} is not the generated one")
  unless nestedRulesOk nP k n cvRi.type own srules rules do
    throw (.invalid s!"nested: the rules of {cvR.name} are not the generated ones")

/-- Post-check (c) over a list of records. -/
def nestedRecsOk (ops : CheckerOps m) (env : Env) (nP k n : Nat) :
    List ((ConstantVal × List RecRule) × List (Nat × Nat) × ConstantVal × List RecRule) →
      m Unit
  | [] => pure ()
  | (sr, own, cvRa, rules) :: rest => do
    nestedRecOk ops env nP k n sr own cvRa rules
    nestedRecsOk ops env nP k n rest

/-- **Post-check (a)** (leanprover/lean4#14577): every pin `I Ds` is
type-checked at the block's parameter context in the RESTORED
environment.  The parametric arguments `Ds` do not appear in the
auxiliary declaration, so they escape every other check; the arena's
`nested-unused-param` is an ill-typed one. -/
def nestedPinsOk (ops : CheckerOps m) (env : Env) (nP : Nat) :
    List (NestedPin × Expr) → m Unit
  | [] => pure ()
  | (q, pinA) :: rest => do
    let pinB := Expr.abstractRange q.pin 0 nP 0
    -- **THE PIN'S SCOPE** (`pinsClosed`, the model lane's DESIGN §M.20
    -- finding 1): no free variable, and every loose bound variable
    -- within the block's parameter telescope.  Nothing else certifies
    -- it — `annotateBody` certifies only that each `.fvar` it REACHES
    -- carries an index below the depth, it never descends into an
    -- fvar's type annotation and never compares it with the opener's,
    -- and it passes `.bvar` through; and a pin's components appear in
    -- no other term the route checks.  The precedent is `ConstWF`,
    -- which demands exactly this pair of a nested RULE's stored pins.
    unless !pinB.hasFvar && pinB.looseBVarsBounded nP do
      throw (.invalid "nested: a pin is not closed at the block's parameter telescope")
    -- official's `tc.check(nested, lparams)`: the pin is TYPE-CHECKED,
    -- not required to be a sort — a pin of an indexed container
    -- (`Vec (T α)`) is a function into one.  The term is the ANNOTATED
    -- component `nestedRemint` minted the copy's type from, opened at
    -- the same parameter variables; inference VALIDATES every datum in
    -- it, so nothing is re-annotated here and the components the model
    -- tier reads are the components the copies' types were built from
    -- (task #279 K.10).
    let _ty ← ops.inferType env nP pinA
    nestedPinsOk ops env nP rest

/-- **The pins' scope, as one Bool over the list** — the same pair of
tests `nestedPinsOk` throws on, so that the run relation records the
fact for EVERY pin without inverting that loop.

**It narrows only where official rejects too.**  A pin is
`J Ds` with `Ds` the container's parameter arguments read out of a
constructor body that was opened at the block's parameters and at
NOTHING else (`Expr.instPis cty params`, `params = openPisAtFvars nP
…`), and the stream's own terms carry no free variable at all
(`checkConstantVal`).  So the only free variables a pin can hold are
`0 … nP-1`, which `abstractRange … 0 nP 0` removes — and a pin that
held a FIELD variable was already rejected by `nestedOccOk`, official's
"nested inductive datatypes parameters cannot contain local variables".
Loose bound variables likewise: a pin has none in the opened context
(`nestedOccOk`'s `looseBVarsBounded 0`), and `abstractRange` introduces
one only at an abstracted parameter, at a depth-bumped index below
`nP`.  A pin failing either test is therefore a term no kernel run
produces, and official — whose own `type_checker` would meet the same
term — refuses it as well. -/
def pinsClosed (nP : Nat) (pins : List NestedPin) : Bool :=
  pins.all fun q =>
    let pinB := Expr.abstractRange q.pin 0 nP 0
    !pinB.hasFvar && pinB.looseBVarsBounded nP

/-- The projection table of a restored structure-like member: the
scratch block's table with its bodies recomputed from the RESTORED
constructor type (the guards and the result sort are levels, which the
restore does not touch). -/
def nestedMemberTable (T : Name) (tbl? : Option ProjTable)
    (ctors : List (ConstantVal × Nat × Nat)) (env : Env) : m Env :=
  match tbl?, ctors with
  | some tbl, [(cvCa, nP, nF)] =>
    checkStructProjTable T tbl.ctor tbl.levelParams nP nF tbl.structSort tbl.guards
      tbl.off cvCa env
  | _, _ => pure env

/-- The tables over the block's members. -/
def nestedTables : List (Name × Option ProjTable × List (ConstantVal × Nat × Nat)) →
    Env → m Env
  | [], env => pure env
  | (T, tbl?, cs) :: rest, env => do
    let env' ← nestedMemberTable (m := m) T tbl? cs env
    nestedTables rest env'

/-! ## The install -/

/-- **Check and install a recognised NESTED block** (see the module
docstring): official's two syntactic front guards, the elimination, the
auxiliary mutual block checked in a scratch environment, the restore,
and the three post-checks.  Only the restored constants are stored. -/
def checkNested (ops : CheckerOps m) (env : Env) (p : NestedParts) : m Env := do
  -- 0. official's `check_no_nested_aux` and `check_uniform_ind_occs`
  let ctorTypes := p.ctors.map (fun c => c.cv.type)
  unless p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      ctorTypes.all (fun t => !t.mentionsNestedAux) do
    throw (.invalid "invalid declaration, it uses the reserved prefix '_nested'")
  unless uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP ctorTypes do
    throw (.invalid "invalid occurrence of datatype being declared: it must be applied \
      to the parameters and universe levels of the mutual declaration")
  -- 1. the elimination, and the mimic count against the stream's records
  let types0 : List AuxType := p.formers.zipIdx.map fun ((cv, _), mIdx) =>
    ⟨cv.name, cv.type,
      (p.ctors.filter (fun c => c.member == mIdx)).map fun c => (c.cv.name, c.cv.type, c.nF)⟩
  let st ← nestedLift (m := m) (elimNested env p.nP p.lps types0)
  -- §M.21 (A) (K.8 steps (1) and (2)): the pin components are ANNOTATED
  -- and the copies' types re-minted at them, with the block's first
  -- former's ANNOTATED parameter binders — so a copy's type is
  -- annotated throughout and the aux install rewrites nothing in it
  let (st, pinsA) ← nestedRemint ops env p st
  unless st.pins.length == p.numNested do
    throw (.invalid s!"the block carries {p.numNested} recursor records past its \
      {p.k} type formers; the elimination finds {st.pins.length} nested occurrences")
  -- the minted names are free in the PRE-BLOCK environment
  -- (`copiesFresh`; official's `check_name` at
  -- `declare_inductive_types`), so that the scratch environment's cons
  -- shadows nothing a later declaration could reach
  unless copiesFresh env p.k st do
    throw (.invalid "nested: an auxiliary type generated by the elimination names a \
      constant the environment already carries")
  -- THE COPIES' ORDER (DESIGN §M.22, the maintainer's decision: the
  -- KERNEL computes it).  The model's forward fold is one term per
  -- copy, built from the terms of the copies it REFERS to, and that
  -- relation has no syntactic well-founded measure — on the raw terms
  -- it is not even acyclic.  So the relation is computed here from the
  -- elimination's own result and a topological order is emitted; a
  -- CYCLE is a positive DECLINE.  It cannot fire on a stream official
  -- accepts: §M.22 records that KINDING excludes the cycles, and the
  -- copies are type-checked (the scratch install, below) — but the
  -- kernel does not read kinding, so the order is computed rather than
  -- argued.
  let _order ← nestedLift (m := m)
    ((nestedTopoOrder (ElimState.grp st) p.k st).mapError fun (j, j') =>
      CheckError.notImplemented s!"nested: the copies' reference relation has a cycle \
        ({(st.pins.getD j default).aux} at {(st.pins.getD j default).container} refers to \
        {(st.pins.getD j' default).aux} at {(st.pins.getD j' default).container} and back)")
  -- 2. the auxiliary mutual block, checked in a SCRATCH environment
  let b ← unwrapOr (auxBlock p st)
    (.invalid "invalid nested inductive datatype, ill-formed declaration")
  -- `auxRoute := true` (K.10): the `_nested`-named members of this block
  -- are the copies the kernel minted itself, out of the container's
  -- stored annotated type at annotated pins, so their types are
  -- PRE-ANNOTATED and the install's front door skips the annotation walk
  -- for them — the stored copy type is then the minted one,
  -- syntactically.  Every check still runs, `inferType` included, which
  -- is what validates each binder datum.
  let envAux ← checkMutualCore ops env b none true
  let stored ← unwrapOr (auxStoredAll envAux b b.k)
    (.internal "nested: the auxiliary block's stored records")
  let R := restoreTbl p st
  let members := stored.take p.k
  let mimics := stored.drop p.k
  let a₀ ← unwrapOr members.head? (.internal "nested: no member")
  let (_fvsA, _) ← unwrapOr (openPisAtFvars p.nP a₀.cvTa.type 0)
    (.internal "nested: the block's parameter telescope")
  -- POST-CHECK (a) AT THE SCRATCH ENVIRONMENT (`pinsOkAux`, the model
  -- lane's request): the same pins, type-checked where the AUXILIARY
  -- block is installed.  It is ADDED, never substituted for the run at
  -- the restored environment, so the accept set can only narrow.  The
  -- two runs agree on everything a pin can MENTION: a pin is a
  -- sub-term of a constructor's field domain, and `checkMutualCtor`
  -- resolves those at the environment holding the pre-block constants
  -- and the block's FORMERS (never its constructors), which `envAux`
  -- and the restored environment hold identically — the formers are
  -- the very `indInfo`s the auxiliary install stored, and the restore
  -- re-adds them unchanged.  The one thing the restore respells that a
  -- pin could reach is a projection TABLE's bodies, through a
  -- `.proj T i` node; running BOTH is what makes that case checked
  -- rather than assumed.
  -- the pins' SCOPE, once for the whole list (`pinsClosed`); the same
  -- pair of tests guards each pin inside `nestedPinsOk`, and this pass
  -- is what the run relation records
  unless pinsClosed p.nP st.pins do
    throw (.invalid "nested: a pin is not closed at the block's parameter telescope")
  nestedPinsOk ops envAux p.nP pinsA
  -- 3. the formers, re-stored with the block's own `all` (our records
  -- carry no `all`, so the stored type and capabilities are official's
  -- unchanged re-add)
  let env₁ := consNestedFormers members env
  -- 4. the constructors, restored and re-checked (post-check (b))
  let ctorsR ← members.mapM fun a => restoreCtors ops env₁ R p.lps a.ctors
  let env₂ := consNestedCtors ctorsR.flatten env₁
  -- 5. the recursor types, restored and re-checked (post-check (b))
  let memberNames := (List.range p.k).map fun mIdx =>
    ((p.formers.getD mIdx default).1.name.str "rec")
  let mimicNames := (List.range p.numNested).map p.mimicRecName
  let cvRms ← restoreRecTys ops env₂ R p.lps memberNames members
  let cvRns ← restoreRecTys ops env₂ R p.lps mimicNames mimics
  let provisions := (cvRms.zip (members.map fun a => (a.mI, a.rP)))
    ++ (cvRns.zip (mimics.map fun a => (a.mI, a.rP)))
  let envR := provisionNestedRecs provisions env₂
  -- 6. the rules, restored and re-checked (post-check (b))
  let rulesM ← (cvRms.zip members).mapM fun (cvRa, a) =>
    restoreRules ops envR R cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules
  let rulesN ← (cvRns.zip mimics).mapM fun (cvRa, a) =>
    restoreRules ops envR R cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules
  let env₃ := storeNestedRecs
    ((cvRms.zip (members.zip rulesM)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
      ++ (cvRns.zip (mimics.zip rulesN)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))) env₂
  -- 7. the projection tables of the structure-like members
  let env₄ ← nestedTables (m := m)
    ((members.zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
      ((p.formers.getD mIdx default).1.name, a.tbl, cs)) env₃
  -- 8. POST-CHECK (a): the pins, typed at the parameter context of the
  -- RESTORED environment (the variables and the telescope are the ones
  -- `pinsOkAux` already used, above — the SAME annotated components,
  -- from the re-mint)
  nestedPinsOk ops env₄ p.nP pinsA
  -- 9. POST-CHECK (c): the stream's records against the generated ones
  unless p.memberRecs.length == cvRms.length && p.mimicRecs.length == cvRns.length do
    throw (.invalid "nested: the block's recursor records are not the generated ones")
  -- the stream's records are checked at the environment BEFORE the
  -- recursors are stored, as the mutual route checks its own
  -- (`checkMutualRecTy`): the record is compared, never added
  let ownOf : Nat → List (Nat × Nat) := fun mIdx =>
    (b.ownCtors mIdx).map fun (J, c) => (J, c.nF)
  let mRows := ((p.memberRecs.zip cvRms).zip rulesM).zipIdx.map
    (fun (((sr, cv), rs), mIdx) => (sr, ownOf mIdx, cv, rs))
  let nRows := ((p.mimicRecs.zip cvRns).zip rulesN).zipIdx.map
    (fun (((sr, cv), rs), j) => (sr, ownOf (p.k + j), cv, rs))
  nestedRecsOk ops env₂ p.nP b.k b.n (mRows ++ nRows)
  pure env₄

end ConLeche
