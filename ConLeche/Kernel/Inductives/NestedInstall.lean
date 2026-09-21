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

/-- **THE PINS ARE STRUCTURALLY DISTINCT** (task #279 K.15 (2), named
for task #315 K.31).

The elimination DEDUPES: `replaceIfNested` mints only on a pin MISS, and
when it misses it mints the container's whole `all`-group, so two pins
can never carry the same term — and `containerGroupOk` makes a
group-mate's group coincide with the group already minted, so a
group-mate cannot be minted twice either.

It is what makes `replaceAllNested`'s rewrite of a container-recursive
field correct: the field is rewritten to the pin `find?` FINDS, which is
the group's own copy only if the pins are pairwise distinct.  Recorded
since K.15 (2) as the first conjunct of `nestedContainersOk`; K.31 gives
it a NAME so the model can consume it without decomposing that `&&`
chain, and adds it to the run relation as its own conjunct — read off
the same Bool, so there is no second evaluation and no second check. -/
def pinsDistinct (pins : List NestedPin) : Bool :=
  decide ((pins.map (·.pin)).Nodup)

/-- **The containers' facts at every pin** (task #279 K.14): the three
syntactic facts about a container the model tier's ψ needs and no stored
record exposes (`containerFactsOk`).  `none` from `containerInfo?` is
impossible here for the reason K.11 (a) records: the pin exists only
because `replaceIfNested` recovered its container at this same
environment. -/
def nestedContainersOk (env : Env) (pins : List NestedPin) : Bool :=
  -- the pins are STRUCTURALLY DISTINCT (K.15 (2), named `pinsDistinct`
  -- at K.31): the elimination dedupes — `replaceIfNested` mints only on
  -- a pin MISS — so this is a fact of the mint, recorded for the model
  pinsDistinct pins &&
  pins.all fun q =>
    match containerInfo? env q.container with
    -- **THE CONTAINER'S CONSTRUCTOR NAMES ROUND-TRIP** (task #315,
    -- lane M7-2's request, DESIGN `#### K.53`): the mint renames a
    -- container constructor by `replacePrefix J.name q.aux` and the
    -- restore renames it back by `replacePrefix q.aux q.container`, so
    -- the model's copy-constructor reading needs the two to compose to
    -- the identity ON THE CONTAINER'S OWN NAMES.  It is a fact of the
    -- container's namespace, not of the mint, and no stored record
    -- exposes it — so it is recorded here, at the pin whose
    -- `containerInfo?` is already in hand and whose `q.aux` is already
    -- minted.  It adds NO environment lookup: the work is name
    -- comparisons on records this clause already read.
    | some ci => containerFactsOk env ci &&
        ci.members.all fun J => !(J.name == q.container) ||
          J.ctors.all fun cc =>
            Name.replacePrefix q.aux q.container
              (Name.replacePrefix J.name q.aux cc.name) == cc.name
    | none => false

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

/-- **The block's FORMERS, checked as the install will store them**
(task #279 K.12).

The elimination mints every copy out of the pieces it is given, so the
pieces are ANNOTATED FIRST — the maintainer's principle: a term we build
ourselves is built from annotated parts and validated afterwards, never
re-annotated.  This is `mutualFormerChecks`' own pair of steps at the
pre-block environment: the front door (`checkConstantVal` — the walk, the
scope and resolution checks, `inferType` and `ensureSort`) and
`checkSumTele`, which keeps a type that is already a syntactic `nP +
nIdx` telescope ending in a sort and otherwise stores the checked close
of its `whnfTelescope` (task #195; official's `check_inductive_types`
reduces before each binder, so `T : id Type` is a correct stream).  The
result is the constant the scratch install will store for that member,
so the elimination's parameter openers and binders — read off the FIRST
former — are the stored former's, by construction. -/
def nestedAnnotFormers (ops : CheckerOps m) (env : Env) (nP : Nat) :
    List (ConstantVal × Nat) → m (List ConstantVal)
  | [] => pure []
  | (cv, nIdx) :: rest => do
    let cvTa₀ ← checkConstantVal ops env cv
    let (cvTa, _s) ← checkSumTele ops env cv (nP + nIdx) cvTa₀
    let restA ← nestedAnnotFormers ops env nP rest
    pure (cvTa :: restA)

/-- **The block's CONSTRUCTORS, annotated at the formers' environment**
(K.12): `checkMutualCtor`'s front door, at the environment
`checkMutualCtor` uses — the pre-block constants plus the block's
formers.  A constructor's type mentions the block's own members and
constants the environment already carries (a nested occurrence is an
application of a STORED container), so this environment is all it
needs; the copies do not exist yet and no constructor of the STREAM
mentions one (the reserved-prefix guard). -/
def nestedAnnotCtors (ops : CheckerOps m) (envF : Env) :
    List MutualCtor → m (List ConstantVal)
  | [] => pure []
  | c :: rest => do
    let cvCa ← checkConstantVal ops envF c.cv
    let restA ← nestedAnnotCtors ops envF rest
    pure (cvCa :: restA)

/-- The environment the constructors are annotated at: the pre-block
constants plus the block's formers at their CHECKED types, which is
`consMutualFormers` at the very records the scratch install will cons. -/
def nestedFormerEnv (fmsA : List ConstantVal) (env : Env) : Env :=
  ⟨(fmsA.map fun cv => ConstantInfo.indInfo cv {}).reverse ++ env.consts⟩

/-- **The elimination's input**, built from the annotated formers and
constructors (K.12): one `AuxType` per member, with its constructors in
block order. -/
def nestedTypes0 (p : NestedParts) (fmsA ctorsA : List ConstantVal) : List AuxType :=
  fmsA.zipIdx.map fun (cvT, mIdx) =>
    ⟨cvT.name, cvT.type,
      (p.ctors.zip ctorsA).filterMap fun (c, cvCa) =>
        if c.member == mIdx then some (cvCa.name, cvCa.type, c.nF) else none,
      -- the block's own members are NOT minted: no source (K.28)
      none⟩

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
    -- **PRE-ANNOTATED** (K.19): the restore is a constant replacement on
    -- a term the scratch install already stored annotated, so the
    -- restored type needs no annotation inferred — every check of
    -- `checkConstantVal` still runs, `inferType` included, and the
    -- stored constant is `restoreNested R` of the auxiliary one,
    -- SYNTACTICALLY
    let cvA ← checkConstantValPre ops env { cvCa with levelParams := lps, type := ty }
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
    let rhsA ← nestedLift (restoreNested R rl.rhs)
    -- **PRE-ANNOTATED** (K.19): the generated rule's right-hand side is
    -- the scratch install's own annotated term with the auxiliary
    -- constants replaced, so no annotation is inferred here.  Every
    -- check the walk's caller made still runs — the scope and
    -- resolution tests below, the `.proj` structure-name slot the walk
    -- itself checked (K.13's `projTablesOk`), and `inferType`, which
    -- VALIDATES every binder datum — and the stored right-hand side is
    -- `restoreNested R` of the auxiliary one, SYNTACTICALLY.
    unless rhsA.allLevelParamsDefined lps && rhsA.constsResolve envR &&
        rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
      throw (.invalid s!"nested: the restored rule of {recName} does not scope")
    unless rhsA.projTablesOk envR do
      throw (.invalid "invalid projection: the node names another structure")
    let _ty ← ops.inferType envR 0 rhsA
    let ctor : Name :=
      if isMimic then
        match R.ctorPins.find? (fun q => q.1 == rl.ctor) with
        | some (_, _, nm) => nm
        | none => rl.ctor
      else rl.ctor
    unless !isMimic || (R.ctorPins.any fun q => q.1 == rl.ctor) do
      throw (.invalid s!"failed to restore nested inductive types, '{rl.ctor}' is not a \
        constructor of an auxiliary type")
    -- **THE CONSTRUCTOR IS STORED** (task #279 K.24): official reads the
    -- rule's constructor with `env.get`, which THROWS on an unknown
    -- constant; this read used to fall back on the stream's own
    -- `ctorParams`, which is a fallback where official has a verdict.
    -- It is now the verdict: a restored rule whose constructor is not a
    -- stored constructor at this environment is INVALID.  On a
    -- well-formed stream it cannot fire — the constructors were stored
    -- two stages earlier (`consNestedCtors`) and the mimics' names come
    -- from the restore table — so the accept set does not move; what it
    -- buys is the model tier's premise, that every restored rule's
    -- constructor is a stored `ctorInfo`.
    let cnP : Nat ←
      match envR.find? ctor with
      | some (.ctorInfo _ n _) => pure n
      | _ => throw (.invalid s!"failed to restore nested inductive types, '{ctor}' is not \
          a constructor")
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
    -- pre-annotated, as at the constructors (K.19)
    let cvA ← checkConstantValPre ops env ⟨nm, a.cvRa.levelParams, ty⟩
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
    List NestedPin → m Unit
  | [] => pure ()
  | q :: rest => do
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
    -- (`Vec (T α)`) is a function into one.  The pin is the
    -- elimination's own term, ANNOTATED (K.12: the elimination ran on
    -- annotated inputs) and already opened at the block's parameter
    -- variables, so nothing is annotated or instantiated here:
    -- inference VALIDATES every datum in it, which is the
    -- `checkConstantValPre` discipline applied to a term the kernel
    -- built itself.
    let _ty ← ops.inferType env nP q.pin
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

/-- **THE PINS' LEVELS ARE THE BLOCK'S** (task #315 K.48, lane M7-3's
DESIGN §U.69 (e)).

`pinsClosed`'s twin, one line below it: every level parameter a pin's
term mentions — in the head's level arguments and in its components
alike — is one of the block's own `lps`.

**Why it is recorded and not derived.**  `ContainerModeled.pinParams`
(lane L-E's clause, landed as a field) asks that a pin's `u`, `Ds` and
`Ids` depend on the container's level parameters ALONE.  `pinOf` builds
`u` and `Ids` from the container's block model at
`Level.substFn ψ M.lps lvls` and `Ds` as the components' `denoteMeta`
readings at `ψ`, so at the nested site BOTH halves reduce to exactly
this Bool — and nothing records it: `nestedPinsOk` type-checks a pin and
`pinsClosed`/`pinsScoped` constrain its VARIABLES, and no test of the
three looks at a level.

**It cannot fire**, and a failure is `.internal`: a pin is a sub-term of
a constructor type that `checkConstantVal` checked at `p.lps`, and a
level parameter outside that list would have been refused there.
CERTIFICATION-ONLY: gated. -/
def pinsLevelsOk (lps : List Name) (pins : List NestedPin) : Bool :=
  pins.all fun q => q.pin.allLevelParamsDefined lps

/-- **THE PINS' CONSTANTS RESOLVE** (task #315 K.64, lane LE's
DESIGN "route 1, priced at the proof").

`pinsClosed`'s and `pinsLevelsOk`'s third twin, at the environment
holding the RESTORED formers: every constant a pin's term names — the
container at its head, the block's own members inside its components,
and everything the components inherit from the constructor type they
were read out of — is stored there, and every `.proj` node in it names
a stored structure.

**Why it is recorded and not derived**, which is the whole of its
justification and is four dead ends, each checked:

* `nestedPinsOk` runs three walks on a pin — `hasFvar`,
  `looseBVarsBounded` and `inferType` — and `Expr.projTablesOk`, the
  syntactic projection-slot walk, is NOT one of them: that one belongs
  to `checkConstantVal`/`checkConstantValPre`, which no pin passes
  through;
* the pin's READING does not give it either.  `denoteMeta` ignores an
  `.fvar`'s type ANNOTATION, which `Expr.constsResolve` descends into;
  and at a `.proj sn i` node it is satisfied either by a table — which
  is `find? (projTableName sn)`, not `find? sn` — or by the
  `projPair?` fallback, which asks the environment nothing;
* `ConstWF`'s projection clause constrains a stored table's BODIES,
  not its structure's storage, so the table route does not reach
  `find? sn`;
* and a pin's components reach stored types only through the MINT
  CHAIN — a pin minted inside one of the container's own copies has
  its components off the COPY's type — so recovering them from
  `EnvWF` would be an invariant over `elimNested`'s loop rather than a
  lookup.

**TWO CONJUNCTS, FOR TWO CROSSINGS.**  `constsResolve` is the guard at
a LATER install: there the newly tabled names are FRESH at this
environment, so `ProjFree.of_constsResolve` turns the resolution into
the guard.  `projTablesOk` is the guard at the block's OWN install,
which conses projection TABLES for its structure-like members: a
member is STORED here — that is why the check runs at the formers'
environment and not at the pre-block one — so resolution says nothing
about it, while the table walk does, because a member's TABLE is not
here.  A `.proj` node at a member is exactly what this conjunct
refuses.

The consumer is the wide identification's `ContainerModeled` clause
carrying a container's pins' components' READINGS: that clause is a
`denoteMeta` conclusion, it crosses a later install through the
GUARDED `hde` (a `.proj` node whose table appears only afterwards
reads one way before and another after), and every other subject of
that crossing takes its guard from exactly this fact — a front door's
resolution plus the tabled names' freshness.

**It cannot fire.**  `pinsScoped`'s own argument applies verbatim: a
pin is `J Ds` with `Ds` the container's parameter arguments read out of
a constructor body the front door RESOLVED, `mkCopy` substitutes
resolving terms into a stored container's resolving type, and the
members the components mention are the formers this very environment
holds.  The table conjunct is the same argument at the other walk: a
`.proj` node of the material a pin is read out of names a table stored
at the FORMERS' environment (`restoreCtors_door`'s
`FrontDoorFacts.slots`, which `NestedTailIn.storeNoProj`'s docstring
states for the restored constructors — and a pin is a domain of one),
and a member's own table is consed only at the very end of the
install.  A failure is `.internal`.  Category (B), by-construction-only,
and NOT gated: the consumer reads it in every mode. -/
def pinsResolve (env : Env) (pins : List NestedPin) : Bool :=
  pins.all fun q => q.pin.constsResolve env && q.pin.projTablesOk env

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

/-- **THE COPIES' SOURCES, RECORDED AND RE-CHECKED** (task #315 K.28,
the model lane's DESIGN §U.17 (g) 3).

Every auxiliary type past the block's own `k` members was MINTED by
`mkCopies`, out of a container member `J`, a level instantiation `lvls`
and the pin's components `Ds`; `AuxType.src` now carries that triple.
This Bool says the record is the truth: at every pin `q`, the pin is
`J.{lvls} Ds` and the aux type `st.types[k + q]` is what
`mkCopy pbs lvls Ds aux J` minted — its name, its telescope-closed
TYPE, and its constructors' NAMES and field counts — where `pbs` is the
block's first former's parameter binders (premise B, K.8: every copy is
minted with those, not the minting constructor's) and `J` is the member
of `containerInfo? env (src.1)`'s group with that name.

**Not the constructors' BODIES, and that is a finding.**  A minted body
is `mkCopy`'s only until `replaceAllNested` runs over it, and that pass
rewrites every nested occurrence INSIDE it into an aux name — including
the container's own recursive occurrences (`List α`'s `cons` tail
becomes the copy's own name), so the bodies differ at essentially every
copy of the corpus, not in a corner case.  Demanding `c.ctors ==
t.ctors` here fires at 23 of the 26 shadow fixtures.  What the record
gives the model is therefore the PRE-IMAGE: the source, certified, from
which `mkCopy`'s output is a computation; the step from that output to
the stored constructors is `replaceAllNested`'s action, which is the
model's own item and not a fact any Bool here can state.

**Why it is recorded and not inferred.**  The model's discharge of the
copy-instantiation identities (`CopyCtorInst` and the index-telescope
and group identities beside it) needs to know which container member,
at which levels and components, a copy came from — true by construction
in the kernel and a theorem nowhere: recovering it is an inversion of
`elimNested`/`mkCopies` through the replacement loop, which
`Verify/Inductives/` does not have (`nestedCopyFormerType_eq` and
`nestedCopyCtorType_eq` start at `st.types`, i.e. after the mint).  One
field and one Bool turn that inversion into a field read.

**It cannot fire.**  `mkCopies` writes the field and the type in the
same breath, from the same `mkCopy` call; the former's type and the
constructors' names and arities are what no later pass touches
(`replaceAllNested` rewrites bodies, and `elimLoop` sets `ctors` only
through it).  A failure is therefore `.internal`. -/
def nestedCopySrcOk (env : Env) (p : NestedParts) (st : ElimState) : Bool :=
  match st.types.head?.bind (fun t₀ => t₀.type.stripPis p.nP) with
  | some (pbs, _) =>
    (List.range st.pins.length).all fun q =>
      match st.types[p.k + q]?, st.pins[q]? with
      | some t, some qn =>
        match t.src with
        | some (Jn, lvls, Ds) =>
          Jn == qn.container &&
            qn.pin == Expr.mkAppN (.const Jn lvls) Ds &&
            (match containerInfo? env Jn with
             | some ci =>
               match ci.members.find? (fun J => J.name == Jn) with
               | some J =>
                 match mkCopy pbs lvls Ds t.name J with
                 | .ok c =>
                   c.name == t.name && c.type == t.type &&
                     -- the constructors' NAMES and arities, not their
                     -- bodies: `replaceAllNested` rewrites a minted
                     -- body's own nested occurrences into pins
                     -- afterwards (see the docstring)
                     c.ctors.map (fun x => (x.1, x.2.2)) ==
                       t.ctors.map (fun x => (x.1, x.2.2))
                 | .error _ => false
               | none => false
             | none => false)
        | none => false
      | _, _ => false
  | none => false

/-- **A PIN'S COMPONENTS MENTION A MEMBER OF THE BLOCK** (task #315
K.44, lane M7-3's DESIGN §U.68 (b)).

Lane L-E's `ContainerModeled.nestMention` — `ordFree`'s nested twin —
asks, at a field the classification calls NESTED at pin `q`, for a
member of the block's own group among the first `nPJ` arguments of the
field's spine.  At the nested route's own read-back that is the pin's
components, and **it has no source in the tree**.  The two gaps M7-3
found:

* the moment is right but the WITNESS is not.  `nestedOccOk` — the
  elimination's own first test — compares `args.take nPI` against
  `ElimState.newNames`, which is `st.types.map (·.name)`: the block's
  members AND every copy minted so far.  So the fact the elimination
  records (`CopyHead`'s mention conjunct, exported at
  `elimNested_copyCtors`) permits a `_nested`-prefixed COPY as the
  witness, at which point a clause asking for a MEMBER does not follow.
  The clause is nonetheless true — every term the walk sees is copy-free,
  since the block's own annotated constructors are guarded by
  `mentionsNestedAux` and `mkCopy`'s output is the container's stored
  constructors with the original components substituted — but that is an
  argument, not a theorem here;
* `CopyInv` is stated at the positions BEHIND the block's `k` members,
  so the members' own rewrites, which is where the clause lives, have no
  provenance theorem at all.

Proving it (M7-3's A2) strengthens `NestedCopyProv`'s invariant to a
member witness across eleven of its seventeen lemmas, adds a
copy-freeness induction through six functions and extends `CopyInv`:
4–6 sessions.  Recording it is this Bool.  CERTIFICATION-ONLY, gated;
`.internal` on failure, and it cannot fire for the reason above. -/
def nestedPinMentionOk (p : NestedParts) (st : ElimState) : Bool :=
  st.pins.all fun q => q.pin.getAppArgs.any fun a => mentionsMember p.memberNames a

/-- **THE PINS' SCOPE, EXACTLY** (task #315 K.30, the model lane's
DESIGN §U.21 (d) 2).

`pinsClosed` says a pin abstracted over the parameters has no free
variable and no loose bound variable below `nP`.  This says the sharper
thing the model's `CtxOk`/`WScoped` need of a pin AT the block's
parameter context: every free variable of a pin — annotation included —
IS one of the FIRST FORMER's openers, at that opener's index and with
that opener's annotation, and the pin has no loose bound variable at
all.

**It cannot fire.**  `replaceIfNested` reads a nested occurrence's
arguments off a term opened at exactly these openers; `mkCopy`'s output
is closed over them and re-opened at them by `elimCtors`; and
`nestedOccOk` — official's "nested inductive datatypes parameters cannot
contain local variables" — refuses a parameter with a loose bound
variable.  A failure is `.internal`. -/
def pinsScoped (nP : Nat) (st : ElimState) : Bool :=
  match st.types.head?.bind (fun t₀ => openPisAtFvars nP t₀.type 0) with
  | some (params, _) =>
    st.pins.all fun q =>
      q.pin.looseBVarsBounded 0 &&
        q.pin.fvarLeaves.all fun l => params[l.1]? == some (.fvar l.1 l.2)
  | none => false

/-- **THE PINS' MINT GROUPS, CERTIFIED** (task #315 K.29, the model
lane's DESIGN §U.19 (d)).

`NestedPin.grpBase`/`grpSize` (K.15 (2)) are written by `mkCopies` and,
until this conjunct, read by nothing: no fact of the run said that pin
`q` lies in its own group, that the group is a contiguous block of the
pin list of the container's `all`-group's size, that the group's `i`-th
pin copies the container's `i`-th member, that the group's copies share
the level instantiation and the components, or that the components'
count is the container's parameter count.  K.28 certifies ONE pin's
source; the group's SHAPE is this one.

Per pin `q`, with `ci = containerInfo? env q.container` and
`(_, lvls, Ds) = st.types[k + q].src` (K.28's record): `q` lies in
`[grpBase, grpBase + grpSize)`, the group ends inside the pin list,
`grpSize` is the container's group size, `Ds.length` is the container's
parameter count, and at every `i < grpSize` the pin `grpBase + i` names
the container's `i`-th member, carries the same group fields, and its
type records the same `lvls` and `Ds`.

**It cannot fire**: `mkCopies` mints a container's whole `all`-group in
one pass, appending one pin per member in block order with the same
`base`/`size` and the same `lvls`/`Ds` it was called with, and
`replaceIfNested` calls it with the group of `containerInfo? env I`.  A
failure is `.internal`.

The consumers are the model lane's `NestedPinGroup.seg`/`kEq`/`rep`/
`pinDsLen` — and through `pinDsLen` the copy's sort `w`, which strips at
`Ds.length + nIdx`. -/
def nestedGroupsOk (env : Env) (p : NestedParts) (st : ElimState) : Bool :=
  (List.range st.pins.length).all fun q =>
    match st.pins[q]?, st.types[p.k + q]? with
    | some qn, some t =>
      match containerInfo? env qn.container, t.src with
      | some ci, some (_, lvls, Ds) =>
        qn.grpBase ≤ q && q < qn.grpBase + qn.grpSize &&
        qn.grpBase + qn.grpSize ≤ st.pins.length &&
        qn.grpSize == ci.members.length && Ds.length == ci.nP &&
        (List.range qn.grpSize).all fun i =>
          match st.pins[qn.grpBase + i]?, ci.members[i]?,
              st.types[p.k + qn.grpBase + i]? with
          | some qi, some Ji, some ti =>
            qi.container == Ji.name && qi.grpBase == qn.grpBase &&
              qi.grpSize == qn.grpSize &&
              (match ti.src with
               | some (Jn', lvls', Ds') => Jn' == Ji.name && lvls' == lvls && Ds' == Ds
               | none => false)
          | _, _, _ => false
      | _, _ => false
    | _, _ => false

/-- **THE FIELD KINDS AT THE PINS** (task #315 §U.1 (c) fact 6; task
#279 K.26 variant C, re-keyed from the copies to the PINS).

`checkMutualCore` classifies every field of every constructor of the
auxiliary block by `mutualCtorKinds` and installs the block only if no
field is `.negative` (official's "non positive or non valid
occurrence") or `.unsupported` (a nested occurrence inside the
auxiliary block).  For a COPY — the container's constructors with the
block's components substituted — that classification is the fact the
model tier needs about the container at the pin: a field is `.ordinary`
(it mentions no member of the auxiliary block), or `.recursive`/
`.reflexive` INTO a named target, and the target index is an index into
`members ++ pins`: a real member of the block (a container-parameter
position, `head : α` at `α := Tree`) or another pin one container level
down (`toList : List α` in `Array.mk`).

Keyed by PIN: `nestedPinKinds p b stored` drops the block's own members
and lists, per pin in pin order, per container constructor, one kind per
field.  The classification is recomputed on the constructors the scratch
install STORED — which are the container's constructors INSTANTIATED at
the pin's components, since that is what the elimination minted.

**Why it is recorded and not derived.**  The alternative is a syntactic
positivity walk over the container's stored constructors with the
parameter FREE, and such a walk can DECLINE a stream official accepts:
official's positivity runs on the substituted field, where a field that
inspects a parameter reduces, and the free-parameter walk is whnf-stuck
on it.  A check that can fire on a correct stream is out; recording what
the install already decided cannot fire at all.

**It cannot fire.**  `nestedPinKinds` answers `none` only if a stored
constructor's type does not strip its own `nP + nF` binders, which is
the telescope `checkMutualCtors` opened to check it; a `.negative` or
`.unsupported` kind is exactly what `classifyMutualKinds` threw on, at
this block, on these types; and a target outside `members ++ pins` is
outside the aux block `mutualCtorKinds` classified against.  A failure
is `.internal`. -/
def nestedPinKinds (p : NestedParts) (b : MutualBlock) (stored : List AuxStored) :
    Option (List (List (List (RecFieldKind × Nat)))) :=
  (stored.drop p.k).mapM fun a =>
    a.ctors.mapM fun (cvCa, _nP, nF) => mutualCtorKinds b.members3 b.lps b.nP (cvCa, nF)

/-- The kinds exist at every pin, every field is `.ordinary`,
`.recursive` or `.reflexive`, and every target is a position of
`members ++ pins` (§U.1 (c) fact 6). -/
def nestedPinKindsAt (p : NestedParts) (st : ElimState)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool :=
  match kinds? with
  | some kinds =>
    kinds.length == st.pins.length &&
      kinds.all fun ks => ks.all fun k => k.all fun (r, t) =>
        (r == .ordinary || r == .recursive || r == .reflexive) &&
          decide (t < p.k + st.pins.length)
  | none => false

@[inline] def nestedPinKindsOk (p : NestedParts) (b : MutualBlock) (st : ElimState)
    (stored : List AuxStored) : Bool :=
  nestedPinKindsAt p st (nestedPinKinds p b stored)

/-- **THE COPIES' RECURSIVE TARGETS COME FROM THE CONTAINER'S OWN
RECURSION** (task #315 K.32, the model lane's DESIGN §U.23 (e)).

At a copy of a container group, a field the auxiliary block classified
`.recursive`/`.reflexive` INTO the same group must come from a field the
CONTAINER's own stored constructor already had as a group occurrence:
per copy `k + q` of the group `[gb, gb + gs)`, constructor `j` and field
`l`, if the kind at `(j, l)` targets an aux member in
`[k + gb, k + gb + gs)`, then the container member's stored constructor
`j`, at field `l`, with its own `Π`-prefix (as many binders as the
COPY's field carries) peeled, is headed by the container group's member
that target names, applied to the container's parameter spine.

**Why it is recorded and not derived.**  The model's `ordF` arm needs
to know that a container-ORDINARY field cannot instantiate to the
group's own pin.  It could only do so through a parameter-headed shape
`β …` whose component is `J_m (Ds.take r)` with `r < nPJ` — a parameter
whose type contains itself, excluded by TYPING and by no syntactic fact
the run records.  This Bool says it at the elimination's output instead,
where it is a property of `mkCopy` + `replaceAllNested`: the rewrite
turns a group occurrence into the group's copy and touches nothing else,
so a copy field classified recursive into the group comes from a
container field that WAS that occurrence.

**It cannot fire**, and a failure is `.internal`. -/
def nestedCopyTargetsAt (env : Env) (p : NestedParts) (st : ElimState)
    (stored : List AuxStored)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool :=
  match kinds? with
  | none => false
  | some kinds =>
    (List.range st.pins.length).all fun q =>
      match st.pins[q]?, kinds[q]?, stored[p.k + q]? with
      | some qn, some ks, some a =>
        match containerInfo? env qn.container with
        | none => false
        | some ci =>
          match ci.members[q - qn.grpBase]? with
          | none => false
          | some J =>
            (List.range ks.length).all fun j =>
              match ks[j]?, a.ctors[j]?, J.ctors[j]? with
              | some kf, some (cvCa, _, nF), some cJ =>
                (List.range kf.length).all fun l =>
                  match kf[l]? with
                  | none => true
                  | some (r, t) =>
                    -- only a field the aux block classified recursive
                    -- into this copy's OWN group is constrained
                    if (r == .recursive || r == .reflexive) &&
                        p.k + qn.grpBase ≤ t &&
                        t < p.k + qn.grpBase + qn.grpSize then
                      match cvCa.type.stripPis (p.nP + nF),
                          cJ.type.stripPis (ci.nP + cJ.nFields) with
                      | some (cbs, _), some (jbs, _) =>
                        match cbs[p.nP + l]?, jbs[ci.nP + l]? with
                        | some domC, some domJ =>
                          let d := (Expr.piBinders domC.1).1.length
                          match domJ.1.stripPis d,
                              ci.members[t - p.k - qn.grpBase]? with
                          | some (_, jres), some Jt =>
                            (match jres.getAppFn with
                             | .const nm _ => nm == Jt.name
                             | _ => false) &&
                              jres.getAppArgs.take ci.nP == structPsAt (l + d) ci.nP
                          | _, _ => false
                        | _, _ => false
                      | _, _ => false
                    else true
              | _, _, _ => false
      | _, _, _ => false

@[inline] def nestedCopyTargetsOk (env : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedCopyTargetsAt env p st stored (nestedPinKinds p b stored)

/-! ### THE COPY FIELDS' TWO RECORDS, ON ONE WALK (task #315 K.60 and K.63)

K.60 and K.63 ask the same question of the same field at the two shapes
a container field can have: K.60 when the stored domain is headed by a
constant, K.63 when it is a `Π` whose BODY is.  The two guards are
disjoint by construction — a `Π`'s `getAppFn` is never a `.const` — and
their per-field environment lookups are disjoint with them, so folding
them shares the constructor telescopes and one `containerInfo?` per
pin, which is what the ablation in DESIGN "#### K.61" (d) says the
route pays for.

`nestedCopyFieldsAt` is that fold: it runs BOTH arms in one pass and
returns the pair, so each route's throw site can name the right record.
The two Bools below are the SPEC — what the run relation records and
what the model inverts — and each IS one component of the fold
(`.1` and `.2`, definitionally), so the two inversions in
`ConLeche/Verify/Inductives/NestedCopyKinds.lean` unfold straight
through it and read the pair with `allPair_fst_mem`/`allPair_snd_mem`
where an `all`-shaped walk would use `List.all_eq_true`. -/

/-- `List.all` of BOTH components of a pair-valued predicate, in ONE
pass over the list (`allPair_fst`/`allPair_snd`). -/
def allPair {α : Type} : List α → (α → Bool × Bool) → Bool × Bool
  | [], _ => (true, true)
  | a :: as, f =>
    let x := f a
    let y := allPair as f
    (x.1 && y.1, x.2 && y.2)

/-- **K.60's ARM at one field**: a container field headed by `.const K`
with `K` not a member of the container's own group, `K` itself a stored
container, and one of its first `ciK.nP` arguments mentioning a member
of the group, forces the copy's field to be `.recursive` into a PIN. -/
def copyPinFieldOk (env : Env) (p : NestedParts) (mems : List Name)
    (r : RecFieldKind) (t : Nat) (dom : Expr) : Bool :=
  match dom.getAppFn with
  | .const K _ =>
    if mems.contains K then true
    else
      match containerInfo? env K with
      | none => true
      | some ciK =>
        if (dom.getAppArgs.take ciK.nP).any (mentionsMember mems) then
          r == .recursive && decide (p.k ≤ t)
        else true
  | _ => true

/-- The container's stored field domain, stripped of its own binders. -/
def stripDomPis : Expr → Expr
  | .forallE _ b _ => stripDomPis b
  | e => e

/-- **How many binders `stripDomPis` removed** — `0` on a domain that
is not a `Π`, so a finitary field's cut is unmoved.  A reflexive
field's spine stands under its own telescope, so the parameters it
mentions are that many `bvar`s further out, and any comparison against
the container's own-pin table has to instantiate at the deeper cut. -/
def domPiDepth : Expr → Nat
  | .forallE _ b _ => domPiDepth b + 1
  | _ => 0

/-- **K.63's ARM at one field**: the same guard one `Π`-tower down —
the domain is a non-empty `Π` telescope whose BODY is headed by
`.const K` with `K` not a member of the container's own group, `K`
itself a stored container, and one of its first `ciK.nP` arguments
mentioning a member of the group.  Then the copy's field is
`.reflexive` into a PIN.

The two arms cannot both fire at one field: the `.forallE` test is what
separates them, and `stripDomPis` is the identity on a domain that is
not a `Π`. -/
def copyReflFieldOk (env : Env) (p : NestedParts) (mems : List Name)
    (r : RecFieldKind) (t : Nat) (dom : Expr) : Bool :=
  match dom with
  | .forallE _ _ _ =>
    match (stripDomPis dom).getAppFn with
    | .const K _ =>
      if mems.contains K then true
      else
        match containerInfo? env K with
        | none => true
        | some ciK =>
          if ((stripDomPis dom).getAppArgs.take ciK.nP).any (mentionsMember mems) then
            r == .reflexive && decide (p.k ≤ t)
          else true
    | _ => true
  | _ => true

/-- **THE TWO ARMS ON ONE WALK** (task #315 K.60 + K.63): the pair
`(K.60's verdict, K.63's verdict)`, computed in a single pass over the
containers' stored constructors.  The two records ARE its components —
`nestedCopyPinFieldsAt` is `.1` and `nestedCopyReflFieldsAt` is `.2`,
definitionally — so the route calls this one and reads the components
for the two messages. -/
def nestedCopyFieldsAt (env : Env) (p : NestedParts) (st : ElimState)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool × Bool :=
  match kinds? with
  | none => (false, false)
  | some kinds =>
    allPair (List.range st.pins.length) fun q =>
      match st.pins[q]?, kinds[q]? with
      | some qn, some ks =>
        match containerInfo? env qn.container with
        | none => (false, false)
        | some ci =>
          match ci.members[q - qn.grpBase]? with
          | none => (false, false)
          | some J =>
            let mems := ci.members.map (·.name)
            allPair (List.range ks.length) fun j =>
              match ks[j]?, J.ctors[j]? with
              | some kf, some cJ =>
                match cJ.type.stripPis (ci.nP + cJ.nFields) with
                | none => (false, false)
                | some (jbs, _) =>
                  allPair (List.range kf.length) fun l =>
                    match kf[l]?, jbs[ci.nP + l]? with
                    | some (r, t), some domJ =>
                      (copyPinFieldOk env p mems r t domJ.1,
                        copyReflFieldOk env p mems r t domJ.1)
                    | _, _ => (false, false)
              | _, _ => (false, false)
      | _, _ => (false, false)

/-- **A CONTAINER'S NESTED FIELD LANDS ON A BLOCK PIN** (task #315
K.60): K.32's twin, running the other way.

K.32 goes from the COPY's classification to the container's field.  The
model's `pinF` arm needs the converse, and its guard is the CONTAINER
field's own shape — every part of which is a fact the model already
holds:

* the field's domain is headed by `.const K …` with `K` NOT a member of
  the container's own group (`BlockOpened.nestF`'s head equation and
  `ContainerModeled.pinsNotMembers`);
* `K` is itself a stored container (`ContainerModeled.pinNP`/`pinConts`);
* one of the first `ciK.nP` arguments mentions a member of the
  container's group (`ContainerModeled.nestArgsMention`).

The third conjunct is what keeps the check off an ORDINARY
container-headed field — `mk : List Nat → Tree` has head `List`, a
container, and no member in its parameter part, so no pin is minted and
nothing is claimed.  Reflexive nested fields fall outside THIS guard by
construction — their domain is a `Π`, so `getAppFn` is not a `.const` —
and they are K.63's, on the same walk.

Under the guard, the auxiliary block classified the copy's
corresponding field `.recursive` into a PIN: `kf[l] = (.recursive, t)`
with `p.k ≤ t`.  That is the model's conjunct 1 and `copyPinFCorr`'s
`hkA` together.

**Why it is recorded and not derived**, which is K.32's reason in the
other direction: it is a property of `mkCopy` + `replaceAllNested`.
`mkCopy` substitutes the pin's components for the container's
parameters and leaves the container's OWN group occurrences standing;
`replaceAllNested` turns those into the group's copies, so `K …` now
carries an auxiliary member inside its parameter spine — a nested
occurrence, rewritten to a mimic, which is an auxiliary member at an
index at or past `p.k`.  The model derives none of it: the opened form
of a nested field keeps the head and the argument count and drops the
parameter part, and the elimination's own records (K.32, K.44) run the
other way.

UNCONDITIONAL in both routes, and `.internal`: the consumer needs the
fact in every mode, and a `certOnly` check is `true` in the trusted
one.

**IF THIS EVER FIRES** the elimination's classification of a copy field
disagrees with its container's — a defect in the ROUTE, not in the
stream, and the answer is never to relax the check.  See DESIGN
"#### K.60". -/
def nestedCopyPinFieldsAt (env : Env) (p : NestedParts) (st : ElimState)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool :=
  (nestedCopyFieldsAt env p st kinds?).1

/-- The Bool the route records (task #315 K.60), on the same field kinds
`nestedPinKinds` computes for K.26 and K.32. -/
@[inline] def nestedCopyPinFieldsOk (env : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedCopyPinFieldsAt env p st (nestedPinKinds p b stored)

/-- **A CONTAINER'S REFLEXIVE NESTED FIELD LANDS ON A BLOCK PIN**
(task #315 K.63, lane PINF's request).

K.60's twin one `Π`-tower down, and it exists because K.60 claims
nothing there BY CONSTRUCTION: K.60's guard reads the stored domain's
head and a reflexive field's domain is a `Π`, so `getAppFn` is not a
`.const` and the walk falls into its catch-all.  The model cannot
supply the kind in its place, and the reason is the circle K.60 exists
to break: the copy's stored domain is mimic-headed only if the rewrite
FIRED, the fire needs the MENTION, and at a pin target the mention is
read off the kind.  Nor can the model exclude `.ordinary` instead —
`mutualOpenedOk`'s ordinary clause says the stored domain resolves in
the pre-block environment, which an UNFIRED container-headed domain
satisfies, so that arm closes nothing.

Each part of the guard is available to the model, which is the
criterion K.60 was designed against: `BlockOpened.nestReflF` gives the
reflexive nested field's OPENED form as exactly a non-empty `Π`
telescope whose body is headed by the pin's container at the pin's
level arguments, the non-membership is
`ContainerModeled.pinsNotMembers`, the further container is `pinNP` +
`NestedPinGroupSyn.contsEnv`, and the mention is the reflexive twin of
`ContainerModeled.nestArgsMentionAbs`.

Under the guard, `kf[l] = (.reflexive, t)` with `p.k ≤ t`.

Gating, carrier and category are K.60's, and so is the WALK: the two
are folded into `nestedCopyFieldsAt`, which runs both arms in one pass.

**IF THIS EVER FIRES** the elimination's classification of a copy's
reflexive field disagrees with its container's — a defect in the ROUTE,
not in the stream, and the answer is never to relax the check.  See
DESIGN "#### K.63". -/
def nestedCopyReflFieldsAt (env : Env) (p : NestedParts) (st : ElimState)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool :=
  (nestedCopyFieldsAt env p st kinds?).2

/-- The Bool the route records (task #315 K.63). -/
@[inline] def nestedCopyReflFieldsOk (env : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedCopyReflFieldsAt env p st (nestedPinKinds p b stored)

/-- Every argument of an application spine is a proper subterm: the
measure that lets `auxAppsOk` recurse into `getAppArgs`. -/
theorem sizeOf_mem_getAppArgs : ∀ {e a : Expr}, a ∈ e.getAppArgs → sizeOf a < sizeOf e
  | .app f b, a, h => by
    -- `getAppArgs` is unfolded by DEFEQ, never by its equation lemma:
    -- asking for that lemma here would mint `Expr.getAppFn.match_1`'s
    -- splitter equations as constants PRIVATE TO THIS MODULE, and every
    -- later module that unfolds `getAppArgs` would then reach the nested
    -- route through them (`tests/proofdeps.sh` catches exactly that).
    have h' : a ∈ f.getAppArgs ++ [b] := h
    rcases List.mem_append.mp h' with h'' | h''
    · have := sizeOf_mem_getAppArgs h''
      simp only [Expr.app.sizeOf_spec]; omega
    · obtain rfl : a = b := by simpa using h''
      simp only [Expr.app.sizeOf_spec]; omega
  | .bvar _, _, h | .fvar _ _, _, h | .sort _, _, h | .const _ _, _, h
  | .lam _ _ _, _, h | .forallE _ _ _, _, h | .letE _ _ _, _, h
  | .proj _ _ _, _, h | .lit _, _, h =>
    absurd (show _ ∈ ([] : List Expr) from h) (by simp)

/-! ## THE AUXILIARY APPLICATIONS SIT AT THE PARAMETERS (task #315 K.35)

`restoreNode` REPLACES a key-headed application `aux_q args` by the pin
lifted to the depth and applied to `args.drop nP` — it DROPS the first
`nP` arguments, exactly as official's `restore_nested` does, and the
components it substitutes refer to the BLOCK's parameters.  Both rely on
the elimination's invariant that an auxiliary type or constructor is
only ever applied to the block's own parameter variables: at a pin
occurrence the restored reading says "the container at `Ds[p⃗]`" and the
auxiliary reading says "the copy at whatever the first `nP` arguments
are", and the two agree only when those arguments are `p⃗`.

The invariant is IN THE TREE for the constructors' FIELDS
(`MutualOpened.recF`/`.reflF`, recorded by `mutualOpenedOk`), and it is
true by construction for the recursor TYPES (`mutualRecTy`'s `structFamI`
and `structCtorSpineAt` are generated at the parameters) and for the
RULES (`mutualIhApp`'s `mutualRecPrefixAt`) — but nothing recorded it.
This is the record.

**The walk is well-founded, not fuelled.**  `auxAppsOk` has to look at a
spine as a whole (`getAppFn`/`getAppArgs`), which Lean cannot see as
structural subterms, and the first attempt used `fuel := e.sizeF` — a
TREE walk, so computing the fuel was itself exponential on a DAG-shared
read-back rule (`tests/e2e/tower_nested.ndjson` went from 0.046 s to
over 600 s).  The measure here is `sizeOf`, Lean's own auto-generated
one, used only in `termination_by`/`decreasing_by` and therefore erased
at runtime; the executed walk is the memoized twin below, swapped in by
`@[csimp]` as `projTablesOk`'s is (the task #215 discipline). -/

/-- A key of the restore's REPLACE whose ARGUMENT SHAPE the restore
relies on: an auxiliary type (a `pins` key) or an auxiliary constructor
(a `ctorPins` key).  A `recMap` key is NOT one — `restoreNode` renames a
bare constant there and the walk descends into its arguments. -/
def isAuxAppKey (R : RestoreTbl) (n : Name) : Bool :=
  (R.pins.lookup n).isSome || R.ctorPins.any (fun q => q.1 == n)

/-- The structural children of an application node: its two halves.
Walking `f` and `a` visits the head and every argument, and no key
constraint fires anywhere along a spine whose head is not a key. -/
def auxAppsKids : Expr → List Expr
  | .app f a => [f, a]
  | _ => []

/-- Is this node's spine headed by a key the shape test applies to? -/
def auxAppsHeadIsKey (R : RestoreTbl) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => isAuxAppKey R n
  | _ => false

/-- **The node's own test**: at a spine headed by a `pins` or `ctorPins`
key the shape is exactly `nP + arity` arguments (the copy's index count
for a type, the constructor's field count for a constructor) whose first
`nP` are the parameter variables `structPsAt d nP`; at any other head
there is nothing to test. -/
def auxAppsNodeOk (R : RestoreTbl) (lps : List Name) (arityOf : Name → Option Nat)
    (d : Nat) (e : Expr) : Bool :=
  match e.getAppFn with
  | .const n us =>
    if isAuxAppKey R n then
      -- **THE KEY HEAD'S LEVEL ARGUMENTS** (task #315 K.38): a copy is
      -- minted at the BLOCK's own level parameters, and the model's
      -- reading law at a key head rewrites by `denoteMeta_const` to the
      -- leaf `acvalA n φ` — the only leaf `RestoreAgree.pin`/`.ctor`
      -- speak about.  At any other `us` the leaf is
      -- `acvalA n (Level.substFn φ lps us)` and the identity does not
      -- apply, so this conjunct is load-bearing and derivable from
      -- nothing else the run records.
      (us == lps.map Level.param) &&
        (match arityOf n with
         | some ar =>
           (e.getAppArgs.length == R.nP + ar) && (e.getAppArgs.take R.nP == structPsAt d R.nP)
         | none => false)
    else true
  | _ => true


/-- **The children the walk continues into**, at the SAME binder depth:
past a key-headed spine's parameter prefix, or — at any other head — the
application's two halves. -/
def auxAppsNodeKids (R : RestoreTbl) (e : Expr) : List Expr :=
  if auxAppsHeadIsKey R e then e.getAppArgs.drop R.nP else auxAppsKids e

theorem sizeOf_mem_auxAppsKids : ∀ {e x : Expr}, x ∈ auxAppsKids e → sizeOf x < sizeOf e
  | .app f a, x, h => by
    -- by DEFEQ, for the reason `sizeOf_mem_getAppArgs` records
    have h' : x ∈ [f, a] := h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
    rcases h' with rfl | rfl <;> (simp only [Expr.app.sizeOf_spec]; omega)
  | .bvar _, _, h | .fvar _ _, _, h | .sort _, _, h | .const _ _, _, h
  | .lam _ _ _, _, h | .forallE _ _ _, _, h | .letE _ _ _, _, h
  | .proj _ _ _, _, h | .lit _, _, h =>
    absurd (show _ ∈ ([] : List Expr) from h) (by simp)

/-- Every child of the node step is a PROPER subterm: the measure the
walk recurses on.  It holds of every node, shape test or not, so the
walk needs no equation to descend. -/
theorem sizeOf_mem_auxAppsNodeKids {R : RestoreTbl} {e x : Expr}
    (h : x ∈ auxAppsNodeKids R e) : sizeOf x < sizeOf e := by
  -- `auxAppsNodeKids` is an `if`, so `unfold` needs no matcher equation
  unfold auxAppsNodeKids at h
  split at h
  · exact sizeOf_mem_getAppArgs (List.mem_of_mem_drop h)
  · exact sizeOf_mem_auxAppsKids h

/-- **Every auxiliary application is at the parameters** — `d` binders
below the block's parameter prefix.  Outside an application the walk is
structural, counting binders in `d`; an `.fvar`'s annotation is not
visited, which is `restoreWalk`'s own convention. -/
def auxAppsOk (R : RestoreTbl) (lps : List Name) (arityOf : Name → Option Nat)
    (d : Nat) (e : Expr) : Bool :=
  match e with
  | .bvar _ => true
  | .sort _ => true
  | .lit _ => true
  | .fvar _ _ => true
  | .const n us =>
    -- the zero-argument instance of the spine rule (`[].length == nP + ar`),
    -- with K.38's level conjunct
    if isAuxAppKey R n then
      (us == lps.map Level.param) &&
        (match arityOf n with
         | some ar => R.nP + ar == 0
         | none => false)
    else true
  | .lam ty b _ => auxAppsOk R lps arityOf d ty && auxAppsOk R lps arityOf (d + 1) b
  | .forallE ty b _ => auxAppsOk R lps arityOf d ty && auxAppsOk R lps arityOf (d + 1) b
  | .letE ty v b =>
    auxAppsOk R lps arityOf d ty && auxAppsOk R lps arityOf d v && auxAppsOk R lps arityOf (d + 1) b
  | .proj _ _ x => auxAppsOk R lps arityOf d x
  | .app f a =>
    auxAppsNodeOk R lps arityOf d (.app f a) &&
      (auxAppsNodeKids R (.app f a)).attach.all fun x => auxAppsOk R lps arityOf d x.1
termination_by sizeOf e
decreasing_by
  all_goals
    first
      | exact sizeOf_mem_auxAppsNodeKids x.2
      | (simp only [Expr.lam.sizeOf_spec, Expr.forallE.sizeOf_spec,
            Expr.letE.sizeOf_spec, Expr.proj.sizeOf_spec]; omega)

/-- The walk's `attach` is bookkeeping for the termination argument. -/
theorem auxAppsOk_attach_all (R : RestoreTbl) (lps : List Name)
    (arityOf : Name → Option Nat) (d : Nat) (cs : List Expr) :
    (cs.attach.all fun x => auxAppsOk R lps arityOf d x.1) = cs.all (auxAppsOk R lps arityOf d) := by
  simp

/-! ### `auxAppsOk`, memoized (the task #215 discipline)

A read-back recursor type or rule rhs is a DAG: the nested tower fixture
`tests/e2e/tower_nested.ndjson` shares one subterm across sixty levels,
so a TREE walk over it does not terminate in any practical time.  The
memo is keyed by the pair `(node, binder depth)` — the walk's answer
depends on both, since the parameter variables it compares against are
`structPsAt d nP` — and the memoized twin is swapped in by `@[csimp]`,
kernel-checked, exactly as `projTablesOk`'s is. -/

/-- The memo's invariant: every recorded answer is the real one, at the
depth it was recorded at. -/
def AuxAppsMemoInv (R : RestoreTbl) (lps : List Name) (arityOf : Name → Option Nat)
    (memo : Std.HashMap (Expr × Nat) Bool) : Prop :=
  ∀ (k : Expr × Nat) (r : Bool), memo[k]? = some r → r = auxAppsOk R lps arityOf k.2 k.1

theorem AuxAppsMemoInv.empty {R : RestoreTbl} {lps : List Name} {arityOf : Name → Option Nat} :
    AuxAppsMemoInv R lps arityOf {} := by
  intro k r h; simp at h

theorem AuxAppsMemoInv.insert {R : RestoreTbl} {arityOf : Name → Option Nat}
    {memo : Std.HashMap (Expr × Nat) Bool} (hm : AuxAppsMemoInv R lps arityOf memo)
    {e : Expr} {d : Nat} {r : Bool} (heq : r = auxAppsOk R lps arityOf d e) :
    AuxAppsMemoInv R lps arityOf (memo.insert (e, d) r) := by
  intro k r' hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i hbeq
    cases hk
    rw [← eq_of_beq hbeq]
    exact heq
  · exact hm k r' hk

/-- Memoized `auxAppsOk`: one walk per `(node, binder depth)`. -/
def auxAppsGoM (R : RestoreTbl) (lps : List Name) (arityOf : Name → Option Nat) (d : Nat)
    (memo : Std.HashMap (Expr × Nat) Bool) (e : Expr) :
    Bool × Std.HashMap (Expr × Nat) Bool :=
  match e with
  | .bvar _ => (true, memo)
  | .sort _ => (true, memo)
  | .lit _ => (true, memo)
  | .fvar _ _ => (true, memo)
  | .const n us => (auxAppsOk R lps arityOf d (.const n us), memo)
  | .lam ty b bm =>
    match memo[(Expr.lam ty b bm, d)]? with
    | some r => (r, memo)
    | none =>
      let (r₁, memo) := auxAppsGoM R lps arityOf d memo ty
      let (r₂, memo) := auxAppsGoM R lps arityOf (d + 1) memo b
      (r₁ && r₂, memo.insert (Expr.lam ty b bm, d) (r₁ && r₂))
  | .forallE ty b bm =>
    match memo[(Expr.forallE ty b bm, d)]? with
    | some r => (r, memo)
    | none =>
      let (r₁, memo) := auxAppsGoM R lps arityOf d memo ty
      let (r₂, memo) := auxAppsGoM R lps arityOf (d + 1) memo b
      (r₁ && r₂, memo.insert (Expr.forallE ty b bm, d) (r₁ && r₂))
  | .letE ty v b =>
    match memo[(Expr.letE ty v b, d)]? with
    | some r => (r, memo)
    | none =>
      let (r₁, memo) := auxAppsGoM R lps arityOf d memo ty
      let (r₂, memo) := auxAppsGoM R lps arityOf d memo v
      let (r₃, memo) := auxAppsGoM R lps arityOf (d + 1) memo b
      (r₁ && r₂ && r₃, memo.insert (Expr.letE ty v b, d) (r₁ && r₂ && r₃))
  | .proj s i x =>
    match memo[(Expr.proj s i x, d)]? with
    | some r => (r, memo)
    | none =>
      let (r, memo) := auxAppsGoM R lps arityOf d memo x
      (r, memo.insert (Expr.proj s i x, d) r)
  | .app f a =>
    match memo[(Expr.app f a, d)]? with
    | some r => (r, memo)
    | none =>
      let res : Bool × Std.HashMap (Expr × Nat) Bool :=
        if auxAppsNodeOk R lps arityOf d (Expr.app f a) then
          (auxAppsNodeKids R (Expr.app f a)).attach.foldl
            (fun p x =>
              let q := auxAppsGoM R lps arityOf d p.2 x.1
              (p.1 && q.1, q.2))
            (true, memo)
        else (false, memo)
      (res.1, res.2.insert (Expr.app f a, d) res.1)
termination_by sizeOf e
decreasing_by
  all_goals
    first
      | exact sizeOf_mem_auxAppsNodeKids x.2
      | (simp only [Expr.lam.sizeOf_spec, Expr.forallE.sizeOf_spec,
            Expr.letE.sizeOf_spec, Expr.proj.sizeOf_spec]; omega)

/-- The argument fold, given the walk's specification at every element. -/
theorem auxAppsGoM_fold_spec {R : RestoreTbl} {lps : List Name}
    {arityOf : Name → Option Nat} {d : Nat}
    (l : List Expr)
    (ih : ∀ x ∈ l, ∀ memo : Std.HashMap (Expr × Nat) Bool, AuxAppsMemoInv R lps arityOf memo →
      ((auxAppsGoM R lps arityOf d memo x).1 = auxAppsOk R lps arityOf d x ∧
        AuxAppsMemoInv R lps arityOf (auxAppsGoM R lps arityOf d memo x).2)) :
    ∀ (acc : Bool) (memo : Std.HashMap (Expr × Nat) Bool), AuxAppsMemoInv R lps arityOf memo →
      ((l.foldl (fun p x =>
            ((p.1 && (auxAppsGoM R lps arityOf d p.2 x).1), (auxAppsGoM R lps arityOf d p.2 x).2))
          (acc, memo)).1 = (acc && l.all (auxAppsOk R lps arityOf d)) ∧
        AuxAppsMemoInv R lps arityOf (l.foldl (fun p x =>
            ((p.1 && (auxAppsGoM R lps arityOf d p.2 x).1), (auxAppsGoM R lps arityOf d p.2 x).2))
          (acc, memo)).2) := by
  induction l with
  | nil => intro acc memo hm; simpa using hm
  | cons x xs ihl =>
    intro acc memo hm
    obtain ⟨h1, h2⟩ := ih x (by simp) memo hm
    obtain ⟨h3, h4⟩ := ihl (fun y hy => ih y (by simp [hy]))
      (acc && (auxAppsGoM R lps arityOf d memo x).1) (auxAppsGoM R lps arityOf d memo x).2 h2
    refine ⟨?_, ?_⟩
    · simp only [List.foldl_cons, List.all_cons]
      rw [h3, h1, Bool.and_assoc]
    · simpa only [List.foldl_cons] using h4

/-- **The memoized walk is `auxAppsOk`.** -/
theorem auxAppsGoM_spec (R : RestoreTbl) (lps : List Name) (arityOf : Name → Option Nat) :
    ∀ (e : Expr) (d : Nat) (memo : Std.HashMap (Expr × Nat) Bool),
      AuxAppsMemoInv R lps arityOf memo →
      ((auxAppsGoM R lps arityOf d memo e).1 = auxAppsOk R lps arityOf d e ∧
        AuxAppsMemoInv R lps arityOf (auxAppsGoM R lps arityOf d memo e).2)
  | .bvar _, _, _, hm => by simp only [auxAppsGoM, auxAppsOk]; exact ⟨trivial, hm⟩
  | .sort _, _, _, hm => by simp only [auxAppsGoM, auxAppsOk]; exact ⟨trivial, hm⟩
  | .lit _, _, _, hm => by simp only [auxAppsGoM, auxAppsOk]; exact ⟨trivial, hm⟩
  | .fvar _ _, _, _, hm => by simp only [auxAppsGoM, auxAppsOk]; exact ⟨trivial, hm⟩
  | .const _ _, _, _, hm => by simp only [auxAppsGoM]; exact ⟨trivial, hm⟩
  | .lam ty b bm, d, memo, hm => by
    rw [auxAppsGoM]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := auxAppsGoM_spec R lps arityOf ty d memo hm
      obtain ⟨h3, h4⟩ := auxAppsGoM_spec R lps arityOf b (d + 1) _ h2
      refine ⟨by simp [auxAppsOk, h1, h3], ?_⟩
      exact h4.insert (by simp [auxAppsOk, h1, h3])
  | .forallE ty b bm, d, memo, hm => by
    rw [auxAppsGoM]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := auxAppsGoM_spec R lps arityOf ty d memo hm
      obtain ⟨h3, h4⟩ := auxAppsGoM_spec R lps arityOf b (d + 1) _ h2
      refine ⟨by simp [auxAppsOk, h1, h3], ?_⟩
      exact h4.insert (by simp [auxAppsOk, h1, h3])
  | .letE ty v b, d, memo, hm => by
    rw [auxAppsGoM]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := auxAppsGoM_spec R lps arityOf ty d memo hm
      obtain ⟨h3, h4⟩ := auxAppsGoM_spec R lps arityOf v d _ h2
      obtain ⟨h5, h6⟩ := auxAppsGoM_spec R lps arityOf b (d + 1) _ h4
      refine ⟨by simp [auxAppsOk, h1, h3, h5], ?_⟩
      exact h6.insert (by simp [auxAppsOk, h1, h3, h5])
  | .proj s i x, d, memo, hm => by
    rw [auxAppsGoM]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨h1, h2⟩ := auxAppsGoM_spec R lps arityOf x d memo hm
      refine ⟨by simp [auxAppsOk, h1], ?_⟩
      exact h2.insert (by simp [auxAppsOk, h1])
  | .app f a, d, memo, hm => by
    have hkey : ∀ (memo' : Std.HashMap (Expr × Nat) Bool), AuxAppsMemoInv R lps arityOf memo' →
        (((auxAppsNodeKids R (Expr.app f a)).foldl (fun p x =>
              ((p.1 && (auxAppsGoM R lps arityOf d p.2 x).1), (auxAppsGoM R lps arityOf d p.2 x).2))
            (true, memo')).1
              = (true && (auxAppsNodeKids R (Expr.app f a)).all (auxAppsOk R lps arityOf d)) ∧
          AuxAppsMemoInv R lps arityOf ((auxAppsNodeKids R (Expr.app f a)).foldl (fun p x =>
              ((p.1 && (auxAppsGoM R lps arityOf d p.2 x).1), (auxAppsGoM R lps arityOf d p.2 x).2))
            (true, memo')).2) := by
      intro memo' hm'
      exact auxAppsGoM_fold_spec (auxAppsNodeKids R (Expr.app f a))
        (fun x hx memo'' hm'' => auxAppsGoM_spec R lps arityOf x d memo'' hm'') true memo' hm'
    rw [auxAppsGoM]
    split
    · rename_i r hhit
      exact ⟨(hm _ _ hhit).symm ▸ rfl, hm⟩
    · obtain ⟨hf1, hf2⟩ := hkey memo hm
      rw [List.foldl_attach (l := auxAppsNodeKids R (Expr.app f a))
        (f := fun (p : Bool × Std.HashMap (Expr × Nat) Bool) (x : Expr) =>
          ((p.1 && (auxAppsGoM R lps arityOf d p.2 x).1), (auxAppsGoM R lps arityOf d p.2 x).2))
        (b := (true, memo))]
      by_cases hok : auxAppsNodeOk R lps arityOf d (Expr.app f a) = true
      · have hval : ((auxAppsNodeKids R (Expr.app f a)).foldl (fun p x =>
              ((p.1 && (auxAppsGoM R lps arityOf d p.2 x).1), (auxAppsGoM R lps arityOf d p.2 x).2))
            (true, memo)).1 = auxAppsOk R lps arityOf d (Expr.app f a) := by
          rw [hf1, auxAppsOk, auxAppsOk_attach_all, hok, Bool.true_and]
        rw [if_pos hok]
        exact ⟨hval, hf2.insert hval⟩
      · simp only [Bool.not_eq_true] at hok
        have hval : (false : Bool) = auxAppsOk R lps arityOf d (Expr.app f a) := by
          rw [auxAppsOk, hok, Bool.false_and]
        rw [if_neg (by simp [hok])]
        exact ⟨hval, hm.insert hval⟩
termination_by e => sizeOf e
decreasing_by
  all_goals
    first
      | exact sizeOf_mem_auxAppsNodeKids hx
      | (simp only [Expr.lam.sizeOf_spec, Expr.forallE.sizeOf_spec,
            Expr.letE.sizeOf_spec, Expr.proj.sizeOf_spec]; omega)

/-- The executed `auxAppsOk` (one memoized DAG walk). -/
def auxAppsOkFast (R : RestoreTbl) (lps : List Name) (arityOf : Name → Option Nat)
    (d : Nat) (e : Expr) : Bool :=
  (auxAppsGoM R lps arityOf d {} e).1

@[csimp] theorem auxAppsOk_eq_auxAppsOkFast : @auxAppsOk = @auxAppsOkFast := by
  funext R lps arityOf d e
  exact (auxAppsGoM_spec R lps arityOf e d {} AuxAppsMemoInv.empty).1.symm


/-- **THE AUXILIARY APPLICATIONS SIT AT THE PARAMETERS** (task #315
K.35, the model lane's spec §1a): in every read-back RECURSOR TYPE and
every read-back RULE right-hand side of the scratch block, every
application headed by an auxiliary type (a `pins` key) or an auxiliary
constructor (a `ctorPins` key) has exactly `nP + arity` arguments — the
copy's index count for a type, the constructor's field count for a
constructor — whose first `nP` are the block's parameter variables at
that binder depth.

The recursor's own `Π p⃗` prefix and a rule's own `λ p⃗` are stripped
first, which is what `restoreNested` does before it walks, so the walk
starts at depth `0` below the parameters exactly as `restoreWalk` does.

**Why it is recorded.**  `restoreNode` DROPS those first `nP` arguments
and puts the pin — whose components mention the block's parameters — in
their place.  If a copy were ever applied to something else, the
restored term would silently claim the container at `Ds[p⃗]` where the
auxiliary term said the copy at other arguments, and the two readings
the model identifies would not be the same object.  Official's
`restore_nested` drops them unchecked for the same reason: its
elimination only ever mints applications at the parameters.

**It cannot fire**: every auxiliary occurrence in the scratch block's
generated recursor types and rules comes from `structFamI` (the
parameters `structPsAt (o + e + nIdx) nP`, then the copy's own index
variables), `structCtorSpineAt` (the parameters, then the fields), a
constructor's own field domain lifted by `o` (`mutualOpenedOk` already
certifies `take nP = fvsP` and the arity at the OPENED form, and the
lift keeps the parameters the parameters), or `mutualIhApp`'s
`mutualRecPrefixAt`.  A failure is `.internal`. -/
def nestedAuxAppsOk (p : NestedParts) (st : ElimState) (stored : List AuxStored) : Bool :=
  let R := restoreTbl p st
  -- a key's argument count PAST the parameters: a copy's index count,
  -- a copy constructor's field count
  let arityOf : Name → Option Nat := fun n =>
    match st.pins.zipIdx.find? (fun q => q.1.aux == n) with
    | some (_, j) => (st.types[p.k + j]?).bind fun t => auxIdxCount p.nP t.type
    | none =>
      match ((st.types.drop p.k).flatMap (·.ctors)).find? (fun c => c.1 == n) with
      | some c => some c.2.2
      | none => none
  stored.all fun a =>
    (match a.cvRa.type.stripPis p.nP with
     | some (_, body) => auxAppsOk R p.lps arityOf 0 body
     | none => false) &&
      a.rules.all fun rl =>
        match rl.rhs.stripLams p.nP with
        | some (_, body) => auxAppsOk R p.lps arityOf 0 body
        | none => false

/-! ## THE PINS' CONTAINER INSTANCES AND THEIR RANK (task #315 K.37)

A **container instance** is one container's whole instantiation at a set
of components, as it is embedded in the block's scratch mutual group:
the copies of the container's members at those components PLUS the
copies of the container's OWN auxiliary types — its own pins — at them.
It is the unit the model's step (iii) reasons about: inside an instance
the block's pin system IS the container's own system at `Ds` (up to the
duplication a relational meet absorbs), and the externals — the pins an
instance refers to that are not its own — are held fixed.

The model needs those externals' references to be WELL FOUNDED.  Its
lane proved that componentwise leastness gives joint leastness only over
a well-founded external-reference graph — over `{0,1}`, `Θ (x, y) :=
(y, x)` has `(1,1)` with each component least at its own section while
the joint least fixed point is `(0,0)` — so there is no order-free
route, and the induction measure has to come from somewhere.  Here it
is: a RANK per instance, computed by the checker and CHECKED, so the
model's step (iii) is strong induction on it.

`nestedPinInstOf` is the connected-component label of the OWN-reference
graph (with a mint group one component by construction), and
`nestedPinRankOf` the longest external chain out of an instance.  Both
are computed by bounded relaxation over the edge list, `nPins + 1`
passes, no term traversal of their own. -/

/-- **The reference edges between the elimination's pins**: per copy
`p.k + q`, per constructor and per field the auxiliary block classified
`.recursive` or `.reflexive` INTO another copy, the edge `(q, t, own)`
— `t` the target PIN (a target inside the block's own members is not an
edge) and `own` saying whether the CONTAINER's stored field at that
position already mentioned a member of the container's own group.

`own` is what separates the two kinds of reference the model treats
differently: an own-group field (the container's own recursion, and the
container's own nesting, which its own elimination pinned) stays INSIDE
the instance; anything else — the container's ordinary field through
another container, or a component — leaves it, and must go to a
strictly smaller rank. -/
def nestedPinEdgesAt (env : Env) (p : NestedParts) (st : ElimState)
    (stored : List AuxStored)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) :
    Option (List (Nat × Nat × Bool)) := do
  let kinds ← kinds?
  let rows ← (List.range st.pins.length).mapM fun q => do
    let qn ← st.pins[q]?
    let ks ← kinds[q]?
    let a ← stored[p.k + q]?
    let ci ← containerInfo? env qn.container
    let J ← ci.members[q - qn.grpBase]?
    let names := ci.members.map (·.name)
    let perCtor ← (List.range ks.length).mapM fun j => do
      let kf ← ks[j]?
      let _c ← a.ctors[j]?
      let cJ ← J.ctors[j]?
      let (jbs, _) ← cJ.type.stripPis (ci.nP + cJ.nFields)
      let perField ← (List.range kf.length).mapM fun l => do
        let (r, t) ← kf[l]?
        if (r == .recursive || r == .reflexive) && p.k ≤ t then
          let domJ ← jbs[ci.nP + l]?
          pure [(q, t - p.k, mentionsMember names domJ.1)]
        else pure ([] : List (Nat × Nat × Bool))
      pure perField.flatten
    pure perCtor.flatten
  pure rows.flatten

/-- **THE CONTAINERS' DECLARATION ORDER** (task #315 K.57): a name's
position in the environment's own list, whose HEAD is the most recent
cons — so a LARGER index is an EARLIER declaration.  `none` at a name
the environment does not hold, which `containerInfo?` has already
excluded for every container this walk visits. -/
def declPos (env : Env) (n : Name) : Option Nat :=
  env.consts.findIdx? (fun ci => ci.name == n)

@[inline] def nestedPinEdges (env : Env) (p : NestedParts) (b : MutualBlock) (st : ElimState)
    (stored : List AuxStored) : Option (List (Nat × Nat × Bool)) :=
  nestedPinEdgesAt env p st stored (nestedPinKinds p b stored)

/-- **A NOT-OWN, CONSTANT-HEADED REFERENCE GOES TO AN EARLIER-DECLARED
CONTAINER** (task #315 K.57): the ordering the entry theorem's step
(iii) inducts on.

Three shapes of reference, and only the third carries an obligation.
An OWN reference stays inside the instance — the ownership bit is
`mentionsMember` against the container's OWN GROUP's names, and
`containerInfo?` puts the container among them, so a not-own reference
can never point back at the source's own group, which is the one shape
no ordering could make decrease.  A not-own reference whose stripped
field domain is headed by a PARAMETER carries no obligation either: the
step reads the parameter's own value and never descends.  What is left
is a not-own reference whose domain is headed by a CONSTANT — another
container — and there the record is that its declaration is strictly
earlier.

Same addressing as `nestedPinEdgesAt`, same `domJ`; the positions are
computed per visit rather than per environment. -/
def nestedPinOrderAt (env : Env) (p : NestedParts) (st : ElimState)
    (stored : List AuxStored)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool :=
  match kinds? with
  | none => false
  | some kinds =>
    (List.range st.pins.length).all fun q =>
      match st.pins[q]?, kinds[q]?, stored[p.k + q]? with
      | some qn, some ks, some a =>
        match containerInfo? env qn.container, declPos env qn.container with
        | some ci, some posQ =>
          match ci.members[q - qn.grpBase]? with
          | some J =>
            (List.range ks.length).all fun j =>
              match ks[j]?, a.ctors[j]?, J.ctors[j]? with
              | some kf, some _, some cJ =>
                match cJ.type.stripPis (ci.nP + cJ.nFields) with
                | some (jbs, _) =>
                  (List.range kf.length).all fun l =>
                    match kf[l]? with
                    | some (r, t) =>
                      if (r == .recursive || r == .reflexive) && p.k ≤ t then
                        match jbs[ci.nP + l]? with
                        | some domJ =>
                          if mentionsMember (ci.members.map (·.name)) domJ.1 then true
                          else
                            match (stripDomPis domJ.1).getAppFn with
                            | .const n _ =>
                              match declPos env n with
                              | some posT => decide (posQ < posT)
                              | none => false
                            | _ => true
                        | none => false
                      else true
                    | none => false
                | none => false
              | _, _, _ => false
          | none => false
        | _, _ => false
      | _, _, _ => false

@[inline] def nestedPinOrderOk (env : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedPinOrderAt env p st stored (nestedPinKinds p b stored)

/-- **The augmented reference digraph**: every edge as an arc, an OWN
edge additionally as its reverse, and every pin joined to its mint
group's base in both directions.  Its strongly connected components are
the container instances: symmetrising the own edges is what makes an
instance closed under the container's own nesting, and joining the group
is what keeps a mint group in one instance — so those two clauses hold
of the computation, and its condensation is acyclic. -/
def nestedPinArcs (st : ElimState) (edges : List (Nat × Nat × Bool)) : List (Nat × Nat) :=
  edges.flatMap (fun e => if e.2.2 then [(e.1, e.2.1), (e.2.1, e.1)] else [(e.1, e.2.1)])
    ++ (List.range st.pins.length).flatMap fun q =>
        let g := (st.pins.getD q default).grpBase
        [(q, g), (g, q)]

/-- The reachable set, grown one arc-relaxation at a time and stopped
when it stops growing (at most `nPins + 1` rounds). -/
def nestedReachGo (arcs : List (Nat × Nat)) : Nat → List Nat → List Nat
  | 0, acc => acc
  | k + 1, acc =>
    let acc' := (acc ++ arcs.filterMap fun a =>
      if acc.contains a.1 then some a.2 else none).eraseDups
    if acc'.length == acc.length then acc else nestedReachGo arcs k acc'

def nestedReach (n : Nat) (arcs : List (Nat × Nat)) (q : Nat) : List Nat :=
  nestedReachGo arcs (n + 1) [q]

/-- One relaxation pass of the rank along the EXTERNAL references — the
ones that leave the instance. -/
def nestedRankPass (inst : List Nat) (edges : List (Nat × Nat × Bool)) (rank : List Nat) :
    List Nat :=
  edges.foldl (fun cur e =>
    if inst.getD e.1 0 == inst.getD e.2.1 0 then cur else
      match cur[e.1]?, cur[e.2.1]? with
      | some rq, some rt => if rq ≤ rt then cur.set e.1 (rt + 1) else cur
      | _, _ => cur) rank

/-- The rank is a function of the INSTANCE: every pin takes its
instance's maximum. -/
def nestedRankHomog (inst rank : List Nat) : List Nat :=
  (List.range rank.length).map fun q =>
    ((List.range rank.length).filter fun q' => inst.getD q' 0 == inst.getD q 0).foldl
      (fun m q' => Nat.max m (rank.getD q' 0)) 0

def nestedRankIter (inst : List Nat) :
    Nat → List (Nat × Nat × Bool) → List Nat → List Nat
  | 0, _, rank => rank
  | n + 1, edges, rank =>
    nestedRankIter inst n edges (nestedRankHomog inst (nestedRankPass inst edges rank))

/-- **The pins' container instances, off the edge list**: the strongly
connected components of `nestedPinArcs` — mutual reachability, computed
by `nPins + 1` relaxation rounds and represented by each class's
smallest member. -/
def nestedPinInstFrom (st : ElimState) (edges : List (Nat × Nat × Bool)) : List Nat :=
  let n := st.pins.length
  let arcs := nestedPinArcs st edges
  let reach := (List.range n).map (nestedReach n arcs)
  (List.range n).map fun q =>
    ((List.range n).filter fun m =>
      (reach.getD q []).contains m && (reach.getD m []).contains q).headD q

/-- **The instances' rank, off the edge list**: the longest chain of
references LEAVING the instance, by `nPins + 1` relaxation passes.  The
condensation is acyclic by construction, so the passes converge. -/
def nestedPinRankFrom (st : ElimState) (edges : List (Nat × Nat × Bool))
    (inst : List Nat) : List Nat :=
  nestedRankIter inst (st.pins.length + 1) edges
    ((List.range st.pins.length).map fun _ => 0)

/-- The instances, at a computed edge list. -/
def nestedPinInstAt (st : ElimState) (edges? : Option (List (Nat × Nat × Bool))) : List Nat :=
  match edges? with
  | none => (List.range st.pins.length).map fun _ => 0
  | some edges => nestedPinInstFrom st edges

/-- The rank, at a computed edge list. -/
def nestedPinRankListAt (st : ElimState) (edges? : Option (List (Nat × Nat × Bool))) :
    List Nat :=
  match edges? with
  | none => (List.range st.pins.length).map fun _ => 0
  | some edges => nestedPinRankFrom st edges (nestedPinInstFrom st edges)

/-- The instances, as the model reads them off the run. -/
@[inline] def nestedPinInstOf (env : Env) (p : NestedParts) (b : MutualBlock) (st : ElimState)
    (stored : List AuxStored) : List Nat :=
  nestedPinInstAt st (nestedPinEdges env p b st stored)

/-- The rank, as the model reads it off the run. -/
@[inline] def nestedPinRankOf (env : Env) (p : NestedParts) (b : MutualBlock) (st : ElimState)
    (stored : List AuxStored) : List Nat :=
  nestedPinRankListAt st (nestedPinEdges env p b st stored)

/-! ## A stored container's OWN pins (task #315 K.41)

A container installed by the nested route carries its own elimination's
pins in the environment after all: the restore re-spells each MIMIC
recursor `C₁.rec_j`'s major premise at the pin, so `C₁.rec_j`'s type,
with its `mI` binders stripped, has as its next domain the container's
own pin `K lvls Ds` applied to that copy's indices — which is exactly
what `nestedFireShape` already reads on the fire path.  A container
whose own declaration was NOT nested has no mimic and so no own pin,
which is the honest answer for e.g. `Array` (a structure over
`List α`). -/

/-- **A stored container's own pins, AT A GIVEN INSTANTIATION**: read
off its mimic recursors and already instantiated at `lvls`/`Ds` — the
level arguments and components of the pin that names this container in
the block.

**There is no index arithmetic here, and that is deliberate.**  The
naive reading — take the major premise's component arguments,
`lowerBVars` them out of the recursor's motives, minors and indices,
then re-instantiate at `Ds` — is exactly the arithmetic a
twelve-instance corpus cannot validate.  It is avoided instead: a pin's
components mention only the container's own PARAMETERS
(`nestedFireShape`'s `looseBVarsBounded rP`; `pinsClosed` says the same
of the block's), so instantiating ALL `mI` binders — the parameters at
`Ds`, the motives, minors and indices at PADDING — leaves the
components exactly `Ds`-substituted, with nothing lifted and nothing to
lower.  `Expr.instPis` is a plain substitution, so the padding needs no
type; and the level arguments come from `instantiateLevelParams` at the
container FORMER's level parameters, which is where a pin's levels are
scoped. -/
def containerOwnPinsAtGo (env : Env) (base : Name) (lps : List Name)
    (lvls : List Level) (Ds : List Expr) (nPr : Nat) : Nat → Nat → List Expr
  | 0, _ => []
  | fuel + 1, j =>
    match env.find? (Name.appendIndexAfter base (j + 1)) with
    | some (.recInfo cvR mI _rP _rules) =>
      let here : List Expr :=
        if nPr ≤ mI && Ds.length == nPr then
          let ty := cvR.type.instantiateLevelParams lps lvls
          let pad := (List.range (mI - nPr)).map fun _ => Expr.sort Level.zero
          match Expr.instPis ty (Ds ++ pad) with
          | some (.forallE dom _ _) =>
            match dom.getAppFn with
            | .const K _ =>
              match containerInfo? env K with
              | some ciK => [Expr.mkAppN dom.getAppFn (dom.getAppArgs.take ciK.nP)]
              | none => []
            | _ => []
          | _ => []
        else []
      here ++ containerOwnPinsAtGo env base lps lvls Ds nPr fuel (j + 1)
    | _ => []

/-- The container's own pins at the instantiation the block's pin
records: `none` if the container is not a recorded group. -/
def containerOwnPinsAt (env : Env) (C : Name) (lvls : List Level) (Ds : List Expr) :
    Option (List Expr) := do
  let .indInfo cvT _ := (← env.find? C) | none
  let ci ← containerInfo? env C
  let first ← ci.members.head?
  pure (containerOwnPinsAtGo env (first.name.str "rec") cvT.levelParams lvls Ds ci.nP 64 0)

/-- A recorded pin's own level arguments and components, off the pin
term the mint wrote (`replaceIfNested`: `pin = I lvls (args.take nP)`). -/
def nestedPinLvlsDs (env : Env) (q : NestedPin) : Option (List Level × List Expr) := do
  let .const _ lvls := q.pin.getAppFn | none
  let ci ← containerInfo? env q.container
  pure (lvls, q.pin.getAppArgs.take ci.nP)

/-- **THE RESTORED RULES' RESCUE BITS ARE THE PROVISION'S OWN VERDICT**
(task #315 K.50, lane M7-2's DESIGN §U.29 (gggg)).

`nestedRecsStore`'s `hctorStored` has three conjuncts; the first is
`restoreRules_at`'s verbatim and the other two are NOT available, for a
structural reason.  `restoreRules` builds the restored rule as
`{ rl with ctor := ctor, … }`, so `r.k` and `r.eta` are the SCRATCH
rule's, unchanged, while `r.ctor` at a mimic is the RESTORED
constructor.  What the scratch bits mean is `mutualRules_bits` at
`envAux`; what `ConstWF` asks is
`r.k = true → recRuleKOf (provision).find? r.ctor = true` and its η
twin.  The two differ in BOTH arguments — a different constructor name
AND a different environment — so the obligation is a transport across
`consNestedCtors`' capability records, which no lemma in the tree
relates.

This is those two conjuncts, recorded at the provisioned environment
where `ConstWF` asks them.

**IT IS NOT THE `false` THE REQUEST PREDICTED, and the measurement is
the reason** (DESIGN `#### K.50`).  §U.29 (gggg) proposed recording both
bits as `false`, on the argument that a mimic's constructors have
fields.  That argument is right about **K** — the K bit is `false` at
every rule of every fixture and every Mathlib cone block — and wrong
about **η**, whose condition is about a STRUCTURE's single constructor
and not about field counts: a copy of a structure-like container is
structure-like, so its restored rule legitimately carries η, and 7 of
the 27 shadow fixtures have one.  Recording `false` there would have
DECLINED them, which the standing rule forbids.

The implication form costs nothing at a rule with no bit set (`!r.k ||`
short-circuits) and two `find?`s at one that has, so only the η-carrying
rules pay — but MEASURED, those two were +0.053 % on the Mathlib cone,
all of it the lookups (a stub with the list work kept and the lookups
removed is free).  So the Bool takes the LOOKUP FUNCTION rather than an
environment, and the cached mirror hands it the driver's index while the
pure route — which the run relation records — hands it `envR.find?`.
`.internal` on failure, CERTIFICATION-ONLY: gated. -/
def nestedRuleBitsOk (find? : Name → Option ConstantInfo)
    (rows : List (ConstantVal × List RecRule)) : Bool :=
  rows.all fun (cvRa, rs) => rs.all fun r =>
    (!r.k || recRuleKOf find? r.ctor) &&
      (!r.eta || recRuleEtaOf find? cvRa.name r.ctor)

/-- **THE MIMICS' STORED TYPES ARE THE RECORDED PINS** (task #315 K.47,
lane M7-3's DESIGN §U.69 (c) 1 and (d)).

`ContainerModeled.ownPins` — lane L-E's clause, and the substantive half
of it — needs the mimic recursors' STORED TYPES tied to the pins the
elimination recorded: that instantiating `T₁.rec_j`'s `mI` binders
leaves the `j`-th pin as its major premise's domain.  M7-3 judged that a
KERNEL record rather than a model proof, and the reason is the one
`containerOwnPinsAt`'s own docstring gives: it is index arithmetic over
`restoreRecTys`/`mutualRecTy`, "the arithmetic a twelve-instance corpus
cannot validate".  The route, on the other hand, has both tables in hand
and can simply compare them.

**The comparison is at the route's OWN instantiation**, which is the
identity one: the container is this block's first member, the level
arguments are its own `lps` as parameters, and the components are the
block's parameter OPENERS — the very fvars `pinsScoped` (K.30) proves a
pin's free variables to be.  At that instantiation
`containerOwnPinsAt`'s output is the recorded pin list VERBATIM, in pin
order (`containerOwnPinsAtGo` walks `T₁.rec_1, T₁.rec_2, …` and
`p.mimicRecName j` is `T₁.rec_(j+1)`).  A consumer that wants the table
at some OTHER `lvls`/`Ds` gets it from this identity by substitution —
which is the law §U.69 (c) already asks lane L-B for, shared with
`NestedPinsShapePinF`; recording the identity is what keeps the kernel
out of the arithmetic.

**It cannot fire**, and a failure is `.internal`: the restore writes
each mimic recursor's major premise FROM the recorded pin
(`restoreNode`'s key rewrite), so the two tables are two readings of one
list.  CERTIFICATION-ONLY: gated. -/
def nestedOwnPinsOk (env : Env) (p : NestedParts) (st : ElimState) : Bool :=
  match st.types.head?.bind (fun t₀ => openPisAtFvars p.nP t₀.type 0) with
  | some (params, _) =>
    match containerOwnPinsAt env (p.formers.headD default).1.name
        (p.lps.map Level.param) params with
    | some ps => ps == st.pins.map (·.pin)
    | none => false
  | none => false

/-- **THE MINT PARENTS ARE WELL FOUNDED** (task #315 K.40, lane L-E's
DESIGN §U.55): every recorded parent is an EARLIER pin.

The model's transfer needs each container instance to be ONE container's
system, with a ROOT it can walk the instance from — and the covering
walk is not reconstructible from the block's edges alone.  `nested_p04`
is the case: from `Array`'s copy the walk reaches the block's `List` pin
through a field (`List α`) that mentions no member of `Array`'s group,
so there is nothing on the edge to relate them; from `P4C` the same
field is the container's own nesting and `List` IS one of `P4C`'s own
pins.  The missing fact is SYNTACTIC — the container's own pin list —
and the checker cannot read it, because a nested declaration RESTORES
and the environment keeps no copy.

The elimination knows it at mint time, so it records it
(`NestedPin.parent`), and this is the clause that makes it usable: a
parent is always an earlier pin, so the parent chain terminates, the
instance's ROOT is its parent-minimal member, and the covering is the
chain.  It holds by construction — the worklist mints at
`types[qhead]` and the new pins take indices at or past the current pin
count, which is greater than `qhead - k`.  CERTIFICATION-ONLY, gated; a
failure is `.internal`. -/
def nestedPinParent (p : NestedParts) (st : ElimState) : List (Option Nat) :=
  st.pins.map fun q => if q.mintedAt < p.k then none else some (q.mintedAt - p.k)

/-- The Bool: the derived parent of every pin is an EARLIER pin. -/
def nestedPinParentOk (p : NestedParts) (st : ElimState) : Bool :=
  st.pins.zipIdx.all fun (q, i) =>
    if q.mintedAt < p.k then true else decide (q.mintedAt - p.k < i)

/-- **THE PINS' INSTANCES AND RANK, CERTIFIED** (task #315 K.37, the
model lane's DESIGN §U.48 (e″)): every OWN reference stays inside the
instance, every OTHER reference goes to a STRICTLY SMALLER rank, the
rank is a function of the instance, and a mint group is one instance.

The first, third and fourth hold of `nestedPinInstOf`/`nestedPinRankOf`
by construction — they are what the propagation computes.  **The second
is the real content**: it says the external-reference graph between
container instances is ACYCLIC, which is the model's induction measure
and the one thing a relaxation cannot arrange for itself.

**It cannot fire**, and a failure is `.internal`: an external reference
either descends into a pin's own components or goes to a container
declared EARLIER than this one, and the path multiset of the block's
own elimination decreases along both.  CERTIFICATION-ONLY: gated. -/
def nestedPinRankAt (st : ElimState) (edges? : Option (List (Nat × Nat × Bool))) : Bool :=
  match edges? with
  | none => false
  | some edges =>
    let n := st.pins.length
    -- the edge list is walked ONCE, and computed once: `nestedPinChecks`
    -- binds it, and `nestedPinKinds` under it, for all four checks (K.46)
    let inst := nestedPinInstFrom st edges
    let rank := nestedPinRankFrom st edges inst
    inst.length == n && rank.length == n &&
      -- (3) the rank is a function of the instance
      (List.range n).all (fun q => (List.range n).all fun t =>
        !(inst.getD q 0 == inst.getD t 0) || rank.getD q 0 == rank.getD t 0) &&
      -- (4) a mint group is one instance
      (List.range n).all (fun q =>
        inst.getD q 0 == inst.getD (st.pins.getD q default).grpBase 0) &&
      -- (1) an OWN reference stays inside the instance, and
      -- (2) a reference that LEAVES the instance goes to a strictly
      -- smaller rank
      edges.all (fun e =>
        if e.2.2 then inst.getD e.1 0 == inst.getD e.2.1 0
        else inst.getD e.1 0 == inst.getD e.2.1 0 ||
          decide (rank.getD e.2.1 0 < rank.getD e.1 0))

@[inline] def nestedPinRankOk (env : Env) (p : NestedParts) (b : MutualBlock) (st : ElimState)
    (stored : List AuxStored) : Bool :=
  nestedPinRankAt st (nestedPinEdges env p b st stored)

/-! ## THE PIN PAIRING AT A NOT-OWN EDGE (task #315 K.41)

Lane L-E's transfer compares a container instance with the block's pins
through ONE container — the instance's ROOT — and needs, at every pin of
the instance, the four data of its `ClassPin`: one container (`name`),
one level assignment on that container's own level parameters (`psi`),
one frame on its parameters (`frame`) and one index set (`idx`).  At an
OWN edge both sides name the same own pin of one container and
`targetPin_corr` gives the pair; at a NOT-OWN edge there is nothing on
the shape to relate them — and the syntactic route is REFUTED at an
accepted fixture (`nested_lam_pin_prop`, where the positivity `whnf`
turns `(fun _ => T) trivial` into a member, so the component's head is a
λ).

**What the checker can compare instead.**  A container installed by the
nested route carries its own elimination's pins in the ENVIRONMENT after
all: the restore re-spells each MIMIC recursor `C₁.rec_j`'s major
premise at the pin, so that type with its `mI` binders stripped has as
its next domain the container's own pin `K lvls Ds` applied to the
copy's indices — which is what `nestedFireShape` already reads on the
fire path.  So the pairing is a comparison of TWO RECORDED TABLES, with
no head reading anywhere.

**THE CORRECTION the measurement forced** (DESIGN `#### K.41`): the
pairing is against the INSTANCE'S ROOT container, NOT the immediate mint
parent.  In `nested_p04` the pins are `P4C`, `Array`, `List` in ONE
instance with `P4C` the root, and the parent chain is
`P4C → Array → List`; `containerOwnPinsAt` of the PARENT of the third
pin — `Array`, a structure over `List α` — is `some []`, because
`Array`'s own declaration is not nested and mints nothing.  It is
`P4C`'s own pin list that is `[Array, List]`.  A pairing stated at the
parent is therefore false at an accepted block; stated at the root it
holds. -/

/-- Each pin's instance ENTRY GROUP: the mint-group base of the unique
group of its container instance whose parent lies OUTSIDE the instance.
`none` at a pin whose instance has no unique entry group, which K.41's
first clause refuses.  K.40's measurement found no such instance in
either corpus — but that corpus was the 27 shadow rows and the 41-block
Mathlib cone, and `tests/e2e/inmodel_groups.ndjson` was in NEITHER: at
its `InModelGroups.H` there are two entry groups, because the `mintedAt`
stamp two of the three pins carry is wrong (DESIGN "THE `mintedAt`
STAMP IS RESET BY ITS OWN MINT"). -/
def nestedPinRootGroupAt (p : NestedParts) (st : ElimState) (inst : List Nat) :
    List (Option Nat) :=
  let par := nestedPinParent p st
  (List.range st.pins.length).map fun q =>
    let cls := (List.range st.pins.length).filter fun i =>
      inst.getD i 0 == inst.getD q 0
    let entries := (cls.filterMap fun i =>
      match par.getD i none with
      | none => some (st.pins.getD i default).grpBase
      | some r => if inst.getD r 0 == inst.getD i 0 then none
                  else some (st.pins.getD i default).grpBase).eraseDups
    match entries with
    | [g] => some g
    | _ => none

@[inline] def nestedPinRootGroup (env : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : List (Option Nat) :=
  nestedPinRootGroupAt p st (nestedPinInstOf env p b st stored)

/-- **THE PIN PAIRING AT A NOT-OWN EDGE** (task #315 K.41, lane L-E's
DESIGN §U.61 finding 4): every pin of a container instance that is not
one of the ROOT group's own members IS a pin the root container's own
elimination minted, at the root pin's own level arguments and
components.

ONE equality of pin TERMS gives all four data of L-E's `ClassPin` at the
pair — `name` (the head), `psi` (the level arguments), `frame` (the
components) and `idx` (the index set, a function of the other three) —
off the two RECORDED tables, with no term head read anywhere.  That is
what the refutation requires: the syntactic route is false at the
accepted fixture `nested_lam_pin_prop`, where the positivity `whnf`
turns `(fun _ => T) trivial` into a member and the component's head is
a λ.

**IT CAN FIRE, and it HAS** (task #315 M8 session 2; DESIGN "THE
`mintedAt` STAMP IS RESET BY ITS OWN MINT").  The argument that stood
here — the block's elimination mints a pin only while rewriting a copy,
and that copy is the root container's — is sound about the MINT and says
nothing about the RECORD the pairing is computed from.  At
`tests/e2e/inmodel_groups.ndjson`'s `InModelGroups.H` this Bool is
`false`, on a stream official accepts, because `mkCopies` resets
`mintedAt` and two pins of one instance then both claim to be
parentless.  A failure stays `.internal` and the ledger category stays
(S) — a fire IS a defect in our own generator, and this one was.
CERTIFICATION-ONLY: gated. -/
def nestedPinRootPairAt (env : Env) (st : ElimState) (roots : List (Option Nat)) : Bool :=
  (List.range st.pins.length).all fun q =>
    match roots.getD q none with
    | none => false
    | some g =>
      let qn := st.pins.getD q default
      if qn.grpBase == g then true
      else
        -- the root GROUP's own pins, pooled: a mutual group is minted at
        -- once and its members' eliminations share the occurrence list
        let pool := ((List.range st.pins.length).filterMap fun i =>
          let rn := st.pins.getD i default
          if rn.grpBase == g then
            (nestedPinLvlsDs env rn).bind fun ld =>
              containerOwnPinsAt env rn.container ld.1 ld.2
          else none).flatten
        pool.contains qn.pin

/-! ## THE CONTAINER INSTANCE MAP (task #315 K.61 and K.62)

A nested block's expansion mints one mimic per distinct pin EXPRESSION
(`replaceIfNested`: `st.pins.find? (fun q => q.pin == pin)`).  When a
pin's container `J` is ITSELF nested, `J`'s own pin table is part of
`J`'s stored block model, and the block's worklist re-mints `J`'s own
pins under the substitution at which `J` was instantiated.  The
**instance map** of a block pin `q` is the resulting map

    J's own pin index  qK   ↦   the block pin index  σ q qK

and it is what identifies a container INSTANCE's copies with the
container's own wide fixpoint (`docs/NESTED.md` §5).  K.41 records the
CONVERSE direction — every pin of a container instance is one the root
container's own elimination minted — which is a covering and not a map:
it says each block pin is SOME own pin's image, and says nothing about
which, nor that every own pin has an image, nor where a field's target
sits.

**THE MAP IS A FUNCTION AND MAY COLLAPSE.**  Two own pins instantiated
alike arrive at ONE mimic — `tests/e2e/src/nested_pin_collide.lean`
exhibits it — and the set theory allows that (`FibreConst`,
`lfpTuple_set` without `InjOn`).  Injectivity is NOT checked; what is
checked is that a value exists at every own pin.  -/

/-- **PIN `q`'s INSTANCE MAP** (task #315 K.61): the block-pin index of
each of `q`'s container's own pins, instantiated at `q`'s own level
arguments and components.  `none` as soon as one of them is not a pin of
the block.

`containerOwnPinsAt` hands back the container's recorded pin list
VERBATIM, in pin order, instantiated at the pin's components — K.41's
own reader, reused unchanged — and pin order is what the model indexes
by. -/
def nestedInstMapAt (env : Env) (st : ElimState) (q : Nat) : Option (List Nat) := do
  let qn ← st.pins[q]?
  let (lvls, Ds) ← nestedPinLvlsDs env qn
  let own ← containerOwnPinsAt env qn.container lvls Ds
  own.mapM fun e => st.pins.findIdx? (fun r => r.pin == e)

/-- Every pin's instance map, in pin order; `none` as soon as one pin's
is undefined.  This is K.61's TOTALITY clause: the `mapM` succeeding
says `σ q` is defined at every own pin of every pin's container. -/
def nestedInstMaps (env : Env) (st : ElimState) : Option (List (List Nat)) :=
  (List.range st.pins.length).mapM (nestedInstMapAt env st)

/-- **THE CONTAINER'S PARAMETERS AS OPAQUE OPENERS**: `nP` free
variables at the levels `0 … nP-1`.

They stand for the container's own parameters wherever the own-pin table
and a stored constructor's telescope have to be compared, and they are
SYNTHETIC on purpose: a stored constant's type carries no free variable
at all, so any `fvar` is a marker that cannot collide, and the two sides
of the comparison are two substitutions by the SAME list — which is all
the comparison needs.  The type an opener carries is never read.

A bound variable would NOT do: `containerOwnPinsAt` instantiates the
mimic recursor's whole telescope with `Expr.instPis`, whose
`instantiate1` lowers the binders above each substitution, so a loose
`bvar` handed to it is re-captured by the next binder and comes back as
the padding. -/
def containerParamOpeners (nP : Nat) : List Expr :=
  (List.range nP).map fun i => Expr.fvar i (Expr.sort Level.zero)

/-- A stored container's own pins **at its OWN parameters**: the same
reader (`containerOwnPinsAt`) at the identity level instantiation and
the parameter openers.

This, and not the table at a pin's components, is where an own-pin INDEX
is determined: the instance map MAY COLLAPSE, so two distinct own pins
can become one block pin, and only the container's own scope tells them
apart. -/
def containerOwnPinsSelf (env : Env) (C : Name) : Option (List Expr) := do
  let ci ← containerInfo? env C
  let m ← ci.members.head?
  containerOwnPinsAt env C (m.lps.map Level.param) (containerParamOpeners ci.nP)

/-- **THE OWN-PIN FIELDS' TARGETS ARE THE INSTANCE MAP'S VALUES**
(task #315 K.61).

The walk is `nestedCopyPinFieldsAt`'s (K.60) with the SAME GUARD — the
field's domain headed by `.const K` with `K` not a member of the
container's own group, `K` itself a stored container, and one of its
first `ciK.nP` arguments mentioning a member of the group — so the two
records constrain exactly the same fields and compose: K.60 says the
copy's field is classified `.recursive` into a PIN, and this says WHICH
pin — the instance map's value at the own-pin position the container's
field sits at.  The guard is K.60's on the very same
binder list, character for character.

The own-pin position is `containerOwnPinsSelf`'s, and the field's domain
is cut to the shape that table holds (`replaceIfNested`'s
`pin = I lvls (args.take nP)`) and only THEN instantiated at the
openers — the CUT is a pin, a small term, where the constructor's whole
telescope is not.  (Instantiating the whole telescope instead,
`Expr.instPisAtF` at the openers, was the first form built and costs
the SAME to three digits — the record's Mathlib price is the
per-pin ENVIRONMENT lookups, not the term walk; see DESIGN
"#### K.61".)  Both sides carry the same openers, so the comparison is exact:
the cut sits under `ci.nP + l` binders whose outer `ci.nP` are the
parameters, so `instantiateList … opens l` with the openers REVERSED
maps `bvar (l + i)` to parameter `ci.nP - 1 - i`'s opener and leaves the
earlier fields' variables alone.

**REFLEXIVE nested fields are INSIDE the guard** (task #315 K.65),
folded in the way K.63 was folded into K.60's walk: the dispatch reads
`stripDomPis domJ.1`, which is the identity on a domain that is not a
`Π`, so a finitary field's verdict is unchanged character for
character, and a reflexive field — whose domain IS a `Π` and which
used to fall into the catch-all — is classified by the same arm.  Its
spine stands under its own telescope, so the cut moves out by
`domPiDepth domJ.1` (which is `0` in the finitary case); `| _ => true`
now keeps only a domain that is neither, i.e. one whose `Π`-stripped
body is not headed by a constant. -/
def nestedInstMapOkAt (env : Env) (p : NestedParts) (st : ElimState)
    (maps? : Option (List (List Nat)))
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool :=
  match maps?, kinds? with
  | some maps, some kinds =>
    (List.range st.pins.length).all fun q =>
      match st.pins[q]?, kinds[q]? with
      | some qn, some ks =>
        match containerInfo? env qn.container with
        | none => false
        | some ci =>
          let opens := (containerParamOpeners ci.nP).reverse
          match ci.members[q - qn.grpBase]? with
          | none => false
          | some J =>
            let mems := ci.members.map (·.name)
            (List.range ks.length).all fun j =>
              match ks[j]?, J.ctors[j]? with
              | some kf, some cJ =>
                match cJ.type.stripPis (ci.nP + cJ.nFields) with
                | none => false
                | some (jbs, _) =>
                  (List.range kf.length).all fun l =>
                    match kf[l]?, jbs[ci.nP + l]? with
                    | some (_, t), some domJ =>
                      let dm := stripDomPis domJ.1
                      let cut := l + domPiDepth domJ.1
                      match dm.getAppFn with
                      | .const K _ =>
                        if mems.contains K then true
                        else
                          match containerInfo? env K with
                          | none => true
                          | some ciK =>
                            if (dm.getAppArgs.take ciK.nP).any (mentionsMember mems) then
                              -- the own-pin table is read HERE and not above:
                              -- `containerOwnPinsSelf` costs two whole-environment
                              -- scans (`Env.find?` is a list walk) and a guarded
                              -- field is rare — 8 blocks over three corpora —
                              -- while a pin is not
                              match containerOwnPinsSelf env qn.container with
                              | none => false
                              | some own0 =>
                              match own0.findIdx? (fun e => e ==
                                  Expr.instantiateList (Expr.mkAppN dm.getAppFn
                                    (dm.getAppArgs.take ciK.nP)) opens cut) with
                              | some qK =>
                                (maps.getD q []).getD qK st.pins.length == t - p.k
                              | none => false
                            else true
                      | _ => true
                    | _, _ => false
              | _, _ => false
      | _, _ => false
  | _, _ => false

/-- The Bool the route records (task #315 K.61), on the same field kinds
`nestedPinKinds` computes for K.26, K.32 and K.60. -/
@[inline] def nestedInstMapOk (env : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedInstMapOkAt env p st (nestedInstMaps env st) (nestedPinKinds p b stored)

/-- **A REWRITTEN ORDINARY FIELD LEAVES THE INSTANCE** (task #315 K.62).

A SECOND record, and separate from K.61 on purpose: it needs no walk of
its own (it is a predicate on `nestedPinEdges`' existing rows against
K.61's table), its clause is a NEGATIVE one, and a fire in it means
something different.  K.61 firing says the instance map is not what the
mint produced; K.62 firing says a rewritten ORDINARY field re-entered
the instance, which would refute the argument that such a target's
container is not one of the container's own classes.

`nestedPinEdgesAt`'s rows are `(q, t - p.k, mentions)`, and `mentions` —
"the CONTAINER's stored field at that position already mentioned a
member of the container's own group" — is exactly the `pinF`/`ordF`-right
split.  At an `ordF`-right row the recorded target must be OUTSIDE
`σ q`'s image.

**AND OUTSIDE THE MINT GROUP** (task #315 K.66).  `σ q`'s image is the
container's OWN PINS' classes; the container's MEMBERS' classes are the
mint group `[grpBase, grpBase + grpSize)`, which the map does not
mention, so the first conjunct alone leaves half the instance
uncovered.  The consumer (`houtσ`) quantifies over BOTH halves, so the
row carries both.  No walk of its own either: the group's bounds are
the pin's own record. -/
def nestedOrdOutsideAt (st : ElimState) (maps? : Option (List (List Nat)))
    (edges? : Option (List (Nat × Nat × Bool))) : Bool :=
  match maps?, edges? with
  | some maps, some rows =>
    rows.all fun (q, t, mentions) =>
      mentions ||
        (!((maps.getD q []).contains t) &&
          (match st.pins[q]? with
           | some qn => decide (t < qn.grpBase) || decide (qn.grpBase + qn.grpSize ≤ t)
           | none => false))
  | _, _ => false

/-- The Bool the route records (task #315 K.62), on the same edge list
`nestedPinEdges` computes for K.37 and K.41. -/
@[inline] def nestedOrdOutsideOk (env : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedOrdOutsideAt st (nestedInstMaps env st) (nestedPinEdges env p b st stored)

/-! ## THE ROOT GROUP'S COVERING, AT THE INDEX LEVEL (task #315 K.75)

K.41 covers every pin of an instance by the root GROUP's pooled own-pin
TERMS, and K.62/K.66 say where a rewritten ordinary field's target is
NOT — at the source PIN.  The label half of the wide route's step needs
the two read against ONE arbitrary member of the root group, and
neither record is in that shape:

* K.41's pool is a union over the root group's members, so its
  membership hands over a member and a TERM, not an index; and
* K.62's negative clause speaks at the source pin's own map alone,
  while the member K.41 hands over is any member of the group.

K.75 is the pair of clauses that closes exactly that gap, and neither
walks: both are predicates on tables `nestedPinChecks` already binds
(`nestedInstMaps`, `nestedPinEdgesAt`, `nestedPinRootGroupAt`).

**MEASURED BEFORE IT LANDED** (DESIGN "WIDE (f4)"): zero fires on the
shadow suite, `init-full` and Mathlib in BOTH modes.  The control says
clause (1) is exercised — 18 pins over eleven blocks are NOT members of
their instance's root group and are covered by the image — and that
clause (2) is VACUOUS on both corpora (`grpgt1 = 0`: no `ordF`-right
edge in either has its source in a mint group of more than one member,
so `nestedOrdOutsideGrpAt` is pointwise `nestedOrdOutsideAt` there).
Clause (2) is therefore carried on its DESIGN argument — a mutual
container's members are minted together and their eliminations share
the occurrence list — and not on a measurement.  The cheaper reading
(K.62 at the pin plus K.29's contiguity) does NOT close the label
chain: see DESIGN's WIDE (f5) §(b).

CERTIFICATION-ONLY: gated, with K.41, whose `roots` table it takes. -/

/-- **K.75 CLAUSE (1): THE POOL IS THE INSTANCE MAP'S IMAGE.**  K.41's
clause with the expr-level `pool.contains qn.pin` replaced by the
INDEX-level image — every pin of an instance is a member of its root
group, or lies in the instance map of one of that group's members. -/
def nestedPinPoolImageAt (st : ElimState) (maps? : Option (List (List Nat)))
    (roots : List (Option Nat)) : Bool :=
  match maps? with
  | some maps =>
    (List.range st.pins.length).all fun q =>
      match roots.getD q none with
      | none => false
      | some g =>
        ((st.pins.getD q default).grpBase == g) ||
          (List.range st.pins.length).any fun i =>
            ((st.pins.getD i default).grpBase == g) && (maps.getD i []).contains q
  | none => false

/-- **K.75 CLAUSE (2): K.62 AT THE MINT GROUP.**  At an `ordF`-right row
`(q, t, false)` the target is outside the instance map's image of EVERY
member of `q`'s mint group `[grpBase, grpBase + grpSize)`, and not only
of `q` itself.  VACUOUS on both corpora (`grpgt1 = 0`); see the section
comment. -/
def nestedOrdOutsideGrpAt (st : ElimState) (maps? : Option (List (List Nat)))
    (edges? : Option (List (Nat × Nat × Bool))) : Bool :=
  match maps?, edges? with
  | some maps, some rows =>
    rows.all fun (q, t, mentions) =>
      mentions ||
        (match st.pins[q]? with
         | some qn =>
           (List.range qn.grpSize).all fun d =>
             !((maps.getD (qn.grpBase + d) []).contains t)
         | none => false)
  | _, _ => false

/-- The two clauses as one Bool, gated with K.41 (task #315 K.75). -/
def nestedPinPoolGrpAt (st : ElimState) (maps? : Option (List (List Nat)))
    (edges? : Option (List (Nat × Nat × Bool))) (roots : List (Option Nat)) : Bool :=
  nestedPinPoolImageAt st maps? roots && nestedOrdOutsideGrpAt st maps? edges?

/-- The Bool the route records (task #315 K.41, extended by K.75): the
pairing at a not-own edge AND the two INDEX-level clauses it has to be
read with — K.41's pool as the instance map's image, and K.62 at the
whole mint group.  One `roots` table, one recorded conjunct; the three
`…At` Bools stay separate, and `nestedPinChecks` throws a different
message at each. -/
@[inline] def nestedPinRootPairOk (env : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedPinRootPairAt env st (nestedPinRootGroup env p b st stored)
    && nestedPinPoolGrpAt st (nestedInstMaps env st)
        (nestedPinEdges env p b st stored) (nestedPinRootGroup env p b st stored)

/-- **THE OWNER'S OWN READING OF A CONTAINER FIELD** (task #315 K.67):
the container `K`'s stored constructor field domain, cut the way K.63
and K.65 cut it (`stripDomPis`, the cut moving with the tower by
`domPiDepth`) and instantiated at `K`'s PARAMETERS AS THE OWNER GAVE
THEM — the own-pin term's argument spine, reversed because the binder
order inside a stripped telescope is the parameters' reverse (K.61
instantiates the same positions with `(containerParamOpeners ci.nP).reverse`).

This is what makes the record a RECOMPUTATION rather than a reading:
the owner's own elimination left no constant behind to ask. -/
def ordTargetLvls (ownSelf : List Expr) (qK : Nat) : List Level :=
  match (ownSelf.getD qK default).getAppFn with
  | .const _ us => us
  | _ => []

/-- The stored domain at the copy's LEVEL instantiation — `mkCopy`'s own
substitution, performed before the cut so that the recomputed term is
syntactically the minted pin (task #315 WIDE (3): without it the
`findIdx?` into the own-pin table misses at five accepted blocks). -/
def ordTargetDomL (lps : List Name) (ownSelf : List Expr) (qK : Nat) (dom : Expr) : Expr :=
  dom.instantiateLevelParams lps (ordTargetLvls ownSelf qK)

def ordTargetDom (lps : List Name) (nP : Nat) (ownSelf : List Expr) (qK l : Nat)
    (dom : Expr) : Expr :=
  Expr.instantiateList (stripDomPis (ordTargetDomL lps ownSelf qK dom))
    (((ownSelf.getD qK default).getAppArgs.take nP).reverse)
    (l + domPiDepth (ordTargetDomL lps ownSelf qK dom))


/-- The worker of `ordHeadRed`: the application spine is peeled into
`args` and a `.lam` meets its argument (β) or a `.letE` its value (ζ).
`args` is in spine order (outermost last is `mkAppN`'s order), and the
invariant every peeling step keeps is `Expr.mkAppN e args = <the term>`
— which is what makes the fuel harmless: running out returns the term
itself, never a wrong one.

`instantiate1Lift` and not `instantiate1`: the recomputed mint leaves
the binders BELOW the cut loose (`ordTargetDom`), so the argument of a
β-redex is an OPEN term and the capture-avoiding substitution is the
one that may be used. -/
def ordHeadRedGo : Nat → Expr → List Expr → Expr
  | 0, e, args => Expr.mkAppN e args
  | n + 1, e, args =>
    match e with
    | .app f a => ordHeadRedGo n f (a :: args)
    | .letE _ v bd => ordHeadRedGo n (Expr.instantiate1Lift bd v) args
    | .lam _ bd _ =>
      match args with
      | a :: rest => ordHeadRedGo n (Expr.instantiate1Lift bd a) rest
      | [] => Expr.mkAppN e args
    | _ => Expr.mkAppN e args

/-- The fuel of `ordHeadRed`, which bounds the number of head β/ζ steps
and spine peelings together.  It is a constant and not the route's `F`
for `ordHeadRed`'s whole reason for being: the function must be the
SAME one at the block's install and at its owner's, and the two routes
have different fuels to hand. -/
def ordHeadRedFuel : Nat := 1024

/-- **THE MINT AT ITS ENVIRONMENT-FREE HEAD NORMAL FORM** (task #315
K.69's REDUCTION SLIVER, at the spelling WIDE (f3) step 1 chose).

`ordRootFired` tests the head of a recomputed mint, and a mint that is
a REDEX at the owner — `(fun _ : True => J β) True.intro`, the shape
`tests/e2e/nested_redex_owner.ndjson` exhibits — has no constant head
until something reduces it.  The model's consumer needs K.67's and
K.68's rows whenever the OWNER fired, reduction or not, and a proof's
case split is over the SYNTAX and not over a corpus, so "measured zero"
does not retire that arm.

**IT REDUCES β AND ζ AT THE HEAD, AND READS NO ENVIRONMENT.**  That is
the whole point, and it is what a `whnf`-based normalisation could not
give: K.68's row is CARRIED to a later block's install through
`PinShapes`, so the function the owner ran and the function the block
runs must be literally the same one — and a function that reads an
environment is not, unless a `whnf`-stability-under-extension theorem
is proved first.  There is no such theorem in the tree.  β and ζ need
no environment, so the two walks run ONE pure function on ONE term and
the identification is free.

**THE RESIDUE, NAMED.**  A mint whose head becomes a constant only
after DELTA, IOTA or a projection is NOT reduced here, and at such a
mint K.67's guard fails and K.68's lookup concedes — an arm with a
conceding producer, exactly as before this spelling.  No fixture in the
tree exhibits one and neither corpus measures one (the non-constant
head population at this arm is ZERO at `init-full` and at Mathlib in
both modes).

**THE COST IS THE SLIVER'S.**  Nothing is run where the mint's head is
already a constant (`ordHeadRed_const`), which is every field of both
real corpora; where it is not, the work is bounded by
`ordHeadRedFuel` head steps on ONE field domain of ONE constructor of
ONE pin.  The "no unmemoized traversals" rule is met by rarity and by
size, not by a memo. -/
def ordHeadRed (W : Expr) : Expr := ordHeadRedGo ordHeadRedFuel W []

/-- Peeling the spine keeps `Expr.mkAppN e args`, so at a head that no
rule applies to the worker returns its input. -/
theorem ordHeadRedGo_of_const {c : Name} {us : List Level} :
    ∀ (n : Nat) (e : Expr) (args : List Expr), e.getAppFn = .const c us →
      ordHeadRedGo n e args = Expr.mkAppN e args := by
  -- **NO FOREIGN DEFINITION IS UNFOLDED BY NAME HERE** (the proof-term
  -- gate's documented door, `tests/proofdeps.sh`): `Expr.mkAppN`'s and
  -- `Expr.getAppFn`'s equations would be GENERATED in this module and
  -- every later proof that reused them would name it.  Everything
  -- below goes through defeq — `show`, a type ascription, `rfl`.
  intro n
  induction n with
  | zero => intro e args _; rfl
  | succ n ih =>
    intro e args h
    match e with
    | .app f a =>
      have hf : f.getAppFn = .const c us := h
      show ordHeadRedGo n f (a :: args) = Expr.mkAppN (.app f a) args
      rw [ih f (a :: args) hf]
      rfl
    | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .forallE _ _ _
    | .lit _ | .proj _ _ _ => rfl
    | .lam _ _ _ => exact nomatch (h : Expr.lam _ _ _ = Expr.const c us)
    | .letE _ _ _ => exact nomatch (h : Expr.letE _ _ _ = Expr.const c us)

/-- **AT A CONSTANT HEAD THE REDUCTION IS THE IDENTITY**, and nothing
is run.  This is the cost argument, and it is also what makes every
proof that already knows its term's head transfer unchanged: the
`ordHeadRed` disappears. -/
theorem ordHeadRed_const {W : Expr} {c : Name} {us : List Level}
    (h : W.getAppFn = .const c us) : ordHeadRed W = W :=
  ordHeadRedGo_of_const ordHeadRedFuel W [] h

/-- **IDEMPOTENT WHERE IT LANDS ON A CONSTANT HEAD** — which is exactly
where the rows speak.  (Off that head the fuel is what it is, and the
rows are silent there anyway.) -/
theorem ordHeadRed_idem_of_const {W : Expr} {c : Name} {us : List Level}
    (h : (ordHeadRed W).getAppFn = .const c us) :
    ordHeadRed (ordHeadRed W) = ordHeadRed W :=
  ordHeadRed_const h

/-- **THE SUBJECT OF THE ORDINARY-FIELD RECORDS' HEAD READ** (task #315
K.74): the recomputed mint at its environment-free head normal form,
read BELOW its own `Π`-tower.

`ordRootFired` and the two target lookups read `getAppFn`, and a `Π`
has none — so without the strip K.67, K.68 and K.69 are SILENT at
exactly the fields whose copies carry a telescope, which is the
population the reading rows have to speak at.  The fields it reaches
are the ones whose tower the MINT PLANTS — `nested_comp_tower`, where
the component is a `Π`, and `nested_redex_tower`, where the `Π`
appears only after the reduction; a tower that is the CONTAINER's own
(`nested_pi_field`) is stripped by `ordTargetDom` before the
components are substituted, so the strip is the identity there and
K.76's first summand is what covers it.  `stripDomPis` is the cut
K.63's guard already uses one
tower down (`copyReflFieldOk`), and it is the IDENTITY wherever the
reduced mint is not a `Π` (`ordHeadCut_const`), so every field the
three rows speak at today they speak at unchanged. -/
def ordHeadCut (W : Expr) : Expr := stripDomPis (ordHeadRed W)

/-- `stripDomPis` is the identity at a constant head: a `Π`'s
`getAppFn` is the `Π` itself and never a `.const`. -/
theorem stripDomPis_of_const {W : Expr} {c : Name} {us : List Level}
    (h : W.getAppFn = .const c us) : stripDomPis W = W := by
  cases W with
  | forallE ty bo bm =>
    have hc : Expr.forallE ty bo bm = Expr.const c us := h
    exact nomatch hc
  | _ => rfl

/-- **THE CUT DISAPPEARS AT A CONSTANT HEAD**, which is every field of
both real corpora — `ordHeadRed_const` and `stripDomPis_of_const`
together. -/
theorem ordHeadCut_const {W : Expr} {c : Name} {us : List Level}
    (h : W.getAppFn = .const c us) : ordHeadCut W = W := by
  unfold ordHeadCut
  rw [ordHeadRed_const h]
  exact stripDomPis_of_const h

/-! ## THE RECOMPUTED FIELD TELESCOPE (task #315 K.76) -/

/-- The worker of `ordTargetTele`: each leading `∀` binder's TYPE with
the pin's components substituted at that binder's own cut.  The cut
rises by one per binder, which is what makes binder `i` speak at
`l + i` — the same arithmetic `ordTargetDom` performs once, for the
body, with `domPiDepth`. -/
def ordTeleGo (Ds : List Expr) : Nat → Expr → List Expr
  | cut, .forallE ty b _ => Expr.instantiateList ty Ds cut :: ordTeleGo Ds (cut + 1) b
  | _, _ => []

/-- **THE COPY'S FIELD TELESCOPE, RECOMPUTED** (task #315 K.76) — K.73's
SUM with the two numbers replaced by the terms they count.

The first summand is the CONTAINER's own tower: binder `i` is the
container's `i`-th stored binder type with the pin's components
substituted at that binder's own cut `l + i`.  The second is the tower
the MINT plants into the stripped body, read straight off the reduced
recomputation `ordHeadRed (ordTargetDom …)` — the same term K.69's own
equation compares, and the same one K.73 measures the depth of.  So

    (ordTargetTele … dom).length
      = domPiDepth (ordTargetDomL … dom)
          + domPiDepth (ordHeadRed (ordTargetDom … dom))

which is K.73's right-hand side verbatim (the level instantiation
moves no binder — `domPiDepth_instantiateLevelParams`).

**IT IS A RECOMPUTATION AND NOT A READING.**  Nothing here looks at the
copy's STORED constructor: the mint (`replaceAllNested`) rewrites
nested occurrences INSIDE binder types and `ordTargetDom` does not, so
the stored binders and a recomputation differ as TERMS at any container
whose field tower mentions its own group, and a comparison between them
would fire on an input official accepts.  K.73's LENGTH comparison is
the only stored-against-recomputed reading this arm may make, and it is
not moved. -/
def ordTargetTele (lps : List Name) (nP : Nat) (ownSelf : List Expr) (qK l : Nat)
    (dom : Expr) : List Expr :=
  ordTeleGo (((ownSelf.getD qK default).getAppArgs.take nP).reverse) l
      (ordTargetDomL lps ownSelf qK dom)
    ++ ((ordHeadRed (ordTargetDom lps nP ownSelf qK l dom)).piBinders).1.map (·.1)

/-- `ordTeleGo` records one entry per leading `∀`, so its length is the
tower's depth and does not depend on the components. -/
theorem ordTeleGo_length (Ds : List Expr) :
    ∀ (cut : Nat) (e : Expr), (ordTeleGo Ds cut e).length = domPiDepth e := by
  intro cut e
  induction e generalizing cut with
  | forallE ty b m ih₁ ih₂ => simp [ordTeleGo, domPiDepth, ih₂]
  | _ => simp [ordTeleGo, domPiDepth]

/-- `Expr.piBinders` records one entry per leading `∀` too. -/
theorem piBinders_length : ∀ (e : Expr), (e.piBinders).1.length = domPiDepth e := by
  intro e
  induction e with
  | forallE ty b m ih₁ ih₂ => simp [Expr.piBinders, domPiDepth, ih₂]
  | _ => simp [Expr.piBinders, domPiDepth]

/-- **K.76's LENGTH IS K.73's SUM** — the bridge that lets the model
spend the two rows together. -/
theorem ordTargetTele_length (lps : List Name) (nP : Nat) (ownSelf : List Expr)
    (qK l : Nat) (dom : Expr) :
    (ordTargetTele lps nP ownSelf qK l dom).length
      = domPiDepth (ordTargetDomL lps ownSelf qK dom)
        + domPiDepth (ordHeadRed (ordTargetDom lps nP ownSelf qK l dom)) := by
  simp [ordTargetTele, ordTeleGo_length, piBinders_length]

/-- **THE ROOT'S COPY FIRED AT THIS FIELD** (task #315 K.69, and K.70's
own dichotomy): its own
recomputation of the field (`ordTargetDom` at the owner's own
components) is headed by a CONSTANT that is one of the owner's group
MEMBERS or the container of one of the owner's own PINS — K.67's head
test, read as a Bool instead of as a case split.

That is the guard under which the normalisation may be pushed across
the block's instantiation, and it is a guard about the ROOT alone: a
term already at a constant inductive head is its own `whnf`
(`whnf_indApp_eq`, `normPosDomM_indApp`), a constant head survives any
substitution, and so the block's copy of the same field is head-normal
too.  The converse fails — a root STUCK at a variable head is unblocked
by the block's substitution — which is why the guard is the root's
firing and not the block's.

It is applied to the mint's POSITIVITY NORMAL FORM (`ordRootNorm`) and
not to the mint, so that a root that fires only AFTER a reduction step
— its mint a redex, `(fun _ => T α) trivial` — is inside the guard and
not in the silent set.  At a mint already at a constant head the normal
form is the mint and no walk is run.

**K.70 READS IT AT THE NORMAL FORM TOO**, and the argument that it need
not is REFUTED.  K.70's two arms — the owner's copy names a class of
the owner (the positive row), or it names none (the negative one) — are
complementary as BOOLS at whatever term the test is asked of, but the
negative arm's CLAIM is about the owner's instance and not about the
term: a mint that is a REDEX whose reduct names one of the owner's own
classes reads as NOT firing and so lands in the negative arm, whose
claim is then FALSE.  `tests/e2e/nested_redex_owner.lean` is that shape
and is an OFFICIAL ACCEPT the unnormalised split errors on.  So K.67's
split is taken at `ordRootNorm` exactly as K.69's guard is, which
costs no acceptance anywhere measured (init-full and Mathlib
byte-identical) and keeps the walk inside `ordRootNorm`'s own
measured-empty regime. -/
def ordRootFired (env : Env) (memsJ : List Name) (ownSelf : List Expr) (W : Expr) : Bool :=
  match W.getAppFn with
  | .const M _ =>
    memsJ.contains M ||
      (match containerInfo? env M with
       | none => false
       | some ciM =>
         (ownSelf.findIdx? (fun e => e ==
           Expr.mkAppN W.getAppFn (W.getAppArgs.take ciM.nP))).isSome)
  | _ => false

/-- **A REWRITTEN ORDINARY FIELD'S TARGET IS THE OWNER'S OWN CLASS**
(task #315 K.67).

K.62 says where such a target is NOT — outside the instance.  The wide
identification's PIN half needs where it IS: at a field the container
`K` calls ORDINARY and the block's rewrite made recursive, the block's
recorded target must be the image of the class the OWNING container
`J` — the container whose own pin this copy is — gave the same field.
Without it the two copies of one `K` constructor, `J`'s own and the
block's, have no relation at that field, and the `ordF`-right arm of
`CopyCtorShape` relates them no longer: its `TargetHead` conjunct was
refuted at an accepted block (`tests/e2e/nested_lam_pin_prop.ndjson`),
so the shape carries the reading and nothing about the target.

**THE CLASSIFICATION IS RECOMPUTED, NOT READ, AND IT HAS TO BE.**  The
obvious form — read `J`'s own record of its pin of `K` — has nothing to
read: the nested install RESTORES, the scratch environment is dropped,
and what survives of a container's own pins is the pin TERM alone,
recovered from the mimic recursor's first domain
(`containerOwnPinsAtGo` keeps `K lvlsK DsK`).  There are no stored
fields, constructors or kinds.  So `J`'s classification is recomputed
from `K`'s STORED constructor at `J`'s own components — which is
exactly K.61's inner block with the lookup table changed from `K`'s own
pins to `J`'s members and own pins, and both cuts (`stripDomPis` /
`domPiDepth`, K.63 and K.65's pattern) come with it.

**THE OWNER IS READ OFF THE MAP, NOT OFF THE PARENT.**  Iterating pins
`g` and their own-pin tables is K.61's own addressing, and it is the
addressing the consumer uses (`dJ.pinCtors qK` at the group).  K.40's
`nestedPinParent` would be VACUOUS where the consumer needs content: in
`tests/e2e/nested_p04` the chain is `P4C → Array → List` and `Array`
mints nothing, so the parent of the `List` copy has an empty own-pin
table while `P4C`'s is `[Array, List]` — K.41's own correction, one arm
over.  A collapsed map is handled for free: every own-pin position
whose image is this pin is checked, not just the first.

**THE THREE ARMS ARE ALL ASSERTED NOW** (task #315 K.70).  The walk
used to SKIP a field the container calls RECURSIVE and to CONCEDE a
field whose owner-side recomputation is not constant-headed; those are
exactly the two arms of the wide identification's pin half with no
producer in the tree.  What it asserts instead:

* the instance map's image of a MINTED GROUP is contiguous in member
  order — arm (A) at a MEMBER target, where both copies' targets are
  already exact (`CopyCtorShape.recF`) and only the map ties them.  It
  is hoisted OUT of the field walk because it is a statement about the
  MAP and reads no field at all;
* the positive row at every field under the guard, the
  `mentionsMember` skip gone — arm (A) at a PIN target, whose consumer
  needs K.71 beside it;
* where the owner's recomputation did NOT fire and the field is
  container-ordinary, the target is in neither the image of the
  owner's instance map nor the owner's own mint group — arm (C),
  K.62/K.66's content ONE NESTING LEVEL UP.  The remaining corner (not
  fired, container-RECURSIVE) is a `false`: a strictly positive
  recursive occurrence is constant-headed after the `Π`-strip.

**It cannot fire by construction**: the block's rewrite of the copy is
ONE substitution applied to the very constructor `J` copied, so the
block's target is `J`'s target instantiated; the mint plants a mimic
of a class only where the rewrite found an occurrence of it, so a
field whose owner-side reading names no class of the owner has none to
find; and the map's contiguity is `mkCopies`' own order.  CERTIFICATION-ONLY in
spirit but UNCONDITIONAL and `.internal` for K.61's reason — the wide
identification reads it in every mode, and a gated check is `true` in
the trusted one.  Cost is K.30's: one stored-constructor read per pin
field, plus `containerOwnPinsSelf` HOISTED PER PIN rather than per
field, which is the order `nestedInstMaps` already runs at. -/
def nestedOrdTargetAt (env : Env) (p : NestedParts) (st : ElimState)
    (maps? : Option (List (List Nat)))
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool :=
  match maps?, kinds? with
  | some maps, some kinds =>
    (List.range st.pins.length).all fun g =>
      match st.pins[g]? with
      | none => false
      | some gn =>
        match containerInfo? env gn.container with
        | none => false
        | some ciJ =>
          match containerOwnPinsSelf env gn.container with
          | none => false
          | some ownSelf =>
            let memsJ := ciJ.members.map (·.name)
            let mapR := maps.getD g []
            (List.range ownSelf.length).all fun qK =>
              let q := mapR.getD qK st.pins.length
              match st.pins[q]?, kinds[q]? with
              | some qn, some ks =>
                -- **K.70's ARM (A), THE MEMBER HALF**: the image of a
                -- MINTED GROUP is contiguous in member order.  The
                -- copy at `q` is the owner's own pin `qK` and sits at
                -- offset `q - qn.grpBase` in the block's group, so the
                -- owner's own pin for the container's member `mm` is
                -- `qK - (q - qn.grpBase) + mm` and its image is the
                -- block's `qn.grpBase + mm`.  That is all a
                -- container-RECURSIVE field at a MEMBER target needs:
                -- both copies' targets are already exact
                -- (`CopyCtorShape.recF`), and only the map's
                -- contiguity ties them.
                ((List.range qn.grpSize).all fun mm =>
                  mapR.getD (qK - (q - qn.grpBase) + mm) st.pins.length
                    == qn.grpBase + mm) &&
                match containerInfo? env qn.container with
                | none => false
                | some ci =>
                  match ci.members[q - qn.grpBase]? with
                  | none => false
                  | some Jm =>
                    let memsK := ci.members.map (·.name)
                    (List.range ks.length).all fun j =>
                      match ks[j]?, Jm.ctors[j]? with
                      | some kf, some cJ =>
                        match cJ.type.stripPis (ci.nP + cJ.nFields) with
                        | none => false
                        | some (jbs, _) =>
                          (List.range kf.length).all fun l =>
                            match kf[l]?, jbs[ci.nP + l]? with
                            | some (r, t), some domJ =>
                              if !((r == .recursive || r == .reflexive) && p.k ≤ t) then true
                              else
                                -- **THE HEAD IS READ BELOW THE
                                -- REDUCED TOWER** (task #315 K.74):
                                -- the subject is `stripDomPis` of the
                                -- reduced mint, not the reduced mint.
                                -- `ordRootFired` reads `getAppFn` and
                                -- a `Π` has none, so without the strip
                                -- this row is SILENT at exactly the
                                -- fields whose copies carry a
                                -- telescope — the population the
                                -- reading rows have to speak at.  The
                                -- strip is the identity wherever the
                                -- mint is not a `Π`
                                -- (`stripDomPis`), so every field the
                                -- row speaks at today it speaks at
                                -- unchanged.
                                let dmJ := ordHeadCut
                                  (ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1)
                                if ordRootFired env memsJ ownSelf dmJ then
                                  match dmJ.getAppFn with
                                  | .const M _ =>
                                    match memsJ.findIdx? (· == M) with
                                    | some mm => t == p.k + gn.grpBase + mm
                                    | none =>
                                      match containerInfo? env M with
                                      | none => false
                                      | some ciM =>
                                        match ownSelf.findIdx? (fun e => e ==
                                            Expr.mkAppN dmJ.getAppFn
                                              (dmJ.getAppArgs.take ciM.nP)) with
                                        | some qJ => t == p.k + mapR.getD qJ st.pins.length
                                        | none => false
                                  | _ => false
                                else if mentionsMember memsK domJ.1 then false
                                else
                                  !mapR.contains (t - p.k)
                                    && (decide (t < p.k + gn.grpBase)
                                        || decide (p.k + gn.grpBase + gn.grpSize ≤ t))
                            | _, _ => false
                      | _, _ => false
              | _, _ => true
  | _, _ => false

/-- The Bool the route records (task #315 K.67), on the same instance-map
table K.61 and K.62 read and the same field kinds `nestedPinKinds`
computes. -/
@[inline] def nestedOrdTargetOk (env : Env) (p : NestedParts)
    (b : MutualBlock) (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedOrdTargetAt env p st (nestedInstMaps env st) (nestedPinKinds p b stored)

/-- **THE BLOCK'S OWN PINS AS THE MODEL SPELLS THEM** (task #315 K.68):
each recorded pin term with the block's PARAMETERS abstracted and
re-opened at the parameter openers.

This is `PinSyn.ownAt` at the identity level instantiation, and the
tree already proves the two equal — `hownAtSelf` (the nested route's own
bridge in `DeclNestedCore.lean`) composed with
`instantiateList_openers_eq_instSeq` at cut `0`, the Verify-tier
identity of the two substitution idioms.  The KERNEL spelling has to be
`instantiateList` and not `instSeq`: `instSeq` lives in `Verify`, which
the implementation may not import. -/
def nestedPinTermsSelf (p : NestedParts) (st : ElimState) : List Expr :=
  st.pins.map fun s =>
    Expr.instantiateList (Expr.abstractRange s.pin 0 p.nP 0)
      (containerParamOpeners p.nP).reverse 0

/-- **A REWRITTEN ORDINARY FIELD'S TARGET IS THE BLOCK'S OWN CLASS**
(task #315 K.68) — K.67's SELF-RELATIVE twin, and the half the
CONTAINER's side of the correspondence needs.

K.67 answers about a copy that is some OTHER container's own pin,
keyed by the instance map, and that is the block's own side of the
transfer.  The other side is what a LATER block must know of THIS
block's pins: which of THIS block's classes its own elimination gave a
field its pin's container calls ordinary.  At this block's install that
pin was minted from this block's own nesting and has no owner at all,
so K.67's guard is vacuous there and says nothing.  Hence a second
record — cheaper than K.67, since no owner, no parent and no instance
map appear.

**The two compose with nothing in between.**  K.67 recomputes at the
`qK`-th entry of `containerOwnPinsSelf env J`; K.68, at `J`'s own
install, recomputes at `J`'s pin `qK`'s components through
`nestedPinTermsSelf` — and `ContainerOwnPinsSyn`'s second clause says
the table's entry at a recorded pin's own index IS that pin at the
instantiation, so the two are the SAME term and the head `M` agrees.
Nothing has to be pushed across a substitution.

The guard is K.67's minus the `p.k ≤ t` bound: the block's own
recomputation may name a MEMBER of the block as easily as one of its
pins — `Tree α := node (List (Tree α))` names the member — so both
halves are recorded, the member by its name among `p.memberNames` and
the pin by its term among the same table the head is recomputed in.

**AND THE CONTAINER-RECURSIVE FIELDS ARE IN IT** (task #315 K.71),
which is K.70's change on this block's own side: the
`mentionsMember memsK` skip is gone.  At a field the container calls
RECURSIVE the block's recomputation names a class just as it does at
one it calls ordinary, and the wide identification's pin half needs it
CARRIED — the OWNER's install is restored and dropped, so the pin TERM
is all that survives of it, and identifying the owner's model index
with a position in its own-pin table asks for TERM equality
(`pinsDistinctAt`), which no DATA row carries.

**It cannot fire by construction**, category (B): the elimination's
rewrite of the copy IS the substitution this row recomputes, followed
by the replacement of the occurrence it finds, so the recorded target
is the class the recomputation names — at a recursive field as much as
at an ordinary one.  UNCONDITIONAL and `.internal` for K.61's
reason. -/
def nestedOrdSelfTargetAt (env : Env) (p : NestedParts) (st : ElimState)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool :=
  match kinds? with
  | some kinds =>
    let terms := nestedPinTermsSelf p st
    (List.range st.pins.length).all fun q =>
      match st.pins[q]?, kinds[q]? with
      | some qn, some ks =>
        match containerInfo? env qn.container with
        | none => false
        | some ci =>
          match ci.members[q - qn.grpBase]? with
          | none => false
          | some Jm =>
            (List.range ks.length).all fun j =>
              match ks[j]?, Jm.ctors[j]? with
              | some kf, some cJ =>
                match cJ.type.stripPis (ci.nP + cJ.nFields) with
                | none => false
                | some (jbs, _) =>
                  (List.range kf.length).all fun l =>
                    match kf[l]?, jbs[ci.nP + l]? with
                    | some (r, t), some domJ =>
                      if !(r == .recursive || r == .reflexive) then true
                      else
                        -- **K.71**: the `mentionsMember memsK` skip is
                        -- gone, K.70's twin at this block's own side.
                        -- At a field the container calls RECURSIVE the
                        -- block's recomputation names a class just as
                        -- it does at an ordinary one — the block's
                        -- mimic of the container's member, or the
                        -- block's copy of one of the container's own
                        -- pins — and the wide identification's pin
                        -- half needs it there too (arm (A)).
                        -- **THE HEAD IS READ THROUGH THE ENVIRONMENT-FREE
                        -- REDUCTION** (task #315 WIDE (f3) step 1,
                        -- spelling (B)): K.67's walk reads the OWNER's
                        -- recomputation the same way, at the same
                        -- place and with the same pure function, so a
                        -- REDEX mint (`nested_redex_owner`) is inside
                        -- both rows instead of conceding on this side.
                        -- `| _ => true` survives as the NARROWER
                        -- residue it now is: a head that becomes a
                        -- constant only after δ, ι or a projection.
                        -- **AND BELOW THE REDUCED TOWER** (task
                        -- #315 K.74), K.67's own move on this side:
                        -- the block's recomputation is a `Π` wherever
                        -- the container's field tower is its own or
                        -- the mint plants one, and a `Π`'s `getAppFn`
                        -- is no `.const`.
                        let dmJ := ordHeadCut (ordTargetDom Jm.lps ci.nP terms q l domJ.1)
                        match dmJ.getAppFn with
                        | .const M _ =>
                          match p.memberNames.findIdx? (· == M) with
                          | some mm => t == mm
                          | none =>
                            match containerInfo? env M with
                            | none => false
                            | some ciM =>
                              match terms.findIdx? (fun e => e ==
                                  Expr.mkAppN dmJ.getAppFn
                                    (dmJ.getAppArgs.take ciM.nP)) with
                              | some z => t == p.k + z
                              | none => false
                        | _ => true
                    | _, _ => false
              | _, _ => false
      | _, _ => false
  | _ => false

/-- The Bool the route records (task #315 K.68), on the same field kinds
`nestedPinKinds` computes for K.26, K.32, K.60, K.61 and K.67. -/
@[inline] def nestedOrdSelfTargetOk (env : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedOrdSelfTargetAt env p st (nestedPinKinds p b stored)

/-! ## THE ROOT'S NORMALISED DOMAIN, INSTANTIATED (task #315 K.69) -/

/-- **THE ROOT-ERA TERM AT THE BLOCK'S INSTANTIATION** (task #315 K.69):
a term in the OWNER's parameter-opener scope, carried to the BLOCK's by
the one substitution that relates the two — the owner's level parameters
at the block pin's levels, the owner's openers at the block pin's
components.

`cut` is the recomputation's own (`l + domPiDepth`), and it is what the
abstraction has to start above: `ordTargetDom` leaves the binders BELOW
the cut loose, so abstracting the openers at `0` would collide with
them.  Above the cut there is nothing to lower — the container's
parameters are exactly the `nP` the recomputation already consumed.

`none` where the block pin's head is not a constant: nothing is asserted
there, and a mint always writes one (`replaceIfNested`). -/
def ordRootInst (lpsJ : List Name) (nPJ cut : Nat) (pinG W : Expr) : Option Expr :=
  match pinG.getAppFn with
  | .const _ lvlsJ =>
    some (Expr.instantiateList
      (Expr.abstractRange (W.instantiateLevelParams lpsJ lvlsJ) 0 nPJ cut)
      ((pinG.getAppArgs.take nPJ).reverse) cut)
  | _ => none

/-- **THE NORMALISATION COMMUTES WITH THE INSTANTIATION AT THIS FIELD**
(task #315 K.69) — K.67's and K.68's twin at the same walk, with the
TERMS compared instead of the targets.

K.67 says which class the owner `J` gave a field its container `K`
calls ordinary; K.68 says which class the block gave it.  Neither says
that the two field DOMAINS are one substitution apart, and the wide
identification's pin half needs exactly that: the block's copy's domain
at the field IS the owner's, instantiated at the block pin's levels and
components.

**WHY IT IS A RECORD AND NOT A THEOREM.**  What the two installs
compare is not the mint but the mint after the POSITIVITY
NORMALISATION, and a normalisation is not a substitution: substitution
creates redexes, so `whnf (e[s]) = (whnf e)[s]` is false in general and
no such theorem exists in the tree.  Under this row's GUARD it holds,
in TWO shapes.  Where the owner's own recomputation is already at a
constant inductive head it needs no commutation at all: such a term is
its own normalisation (`normPosDomM_indApp`), the head survives the
substitution, the block's is its own normalisation too, and the
equation this Bool records — about the MINTS — carries the normalised
domains with it, with NO walk run.  Where it is not — the REDUCTION
SLIVER — both sides are put through `ordRootNorm`, the very walk the
install uses, and the equation is recorded between the two NORMAL
FORMS; what is owed there is that the owner's reduction survives the
substitution (`t →* W` gives `t[s] →* W[s]`, the direction that IS
closed under substitution) and that `whnf` is the function that finds
it, `W[s]` being constant-headed and so its own `whnf`.  The guard is
the ROOT's firing, and it is the root's alone because the mixed corner
— the block's copy fires where the owner's did not — is REAL (a root
stuck at a VARIABLE head is unblocked by the block's substitution, and
no reduction at the owner can unstick it) and is the arm the model
closes with an entry.

**It cannot fire by construction**: the block's copy of the owner's pin
is ONE substitution applied to the very constructor the owner copied,
and both sides instantiate the SAME stored domain — the owner's at its
own components, the block's at those components substituted.
UNCONDITIONAL and `.internal`, for K.61's reason.

**THE OWNER'S FIRING FORCES THE BLOCK'S** (task #315 WIDE (f3), the row
STRENGTHENED).  The field kind test is BELOW the guard and not above
it: where the owner fired, a block copy that left the field ORDINARY is
a `false` and not a silence.  The argument is the guard's own — the
owner's normalised domain is constant-headed at an inductive head
(`ordRootFired`), a constant head survives the block's substitution,
and such an application is its own `whnf` (`whnf_indApp_eq`,
`normPosDomM_indApp`), so the block's positivity walk classifies the
field recursive or reflexive.  It cannot fire for that reason on the
constant-head path; on the SLIVER path it rests on the same owed lemma
the row's WHAT IS OWED already names (the owner's reduction under the
substitution, and `whnf` finding it).  This is what produces
`hfireOrd` — `rs₂ → rs₁` at the model — which no `blkRss`-guarded row
can.

**The arms that assert nothing.**  Where the root did NOT fire — after
the normalisation, so the mixed corner and nothing else — the row is
silent, and that corner has no claim to make (and with it the block's
kind, which is why the kind test may not be hoisted above the guard);
where the OWNER's walk threw (fuel, or a non-positive occurrence) it is
silent too, since the owner's own side is then not in hand; where the
block pin's head is not a constant it is silent for `ordRootInst`'s
reason; and where the container's own stored domain already mentions a
member of the container's group the field is not this row's.  The
BLOCK's walk throwing is NOT silent: under the guard the owner's normal
form is constant-headed, so the block's reduces to its substitution and
cannot throw, and the arm asserts that.  The LOOKUP arms are K.67's,
character for character. -/
def nestedOrdNormAt (env : Env) (p : NestedParts) (st : ElimState)
    (stored : List AuxStored)
    (maps? : Option (List (List Nat)))
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) : Bool :=
  match maps?, kinds? with
  | some maps, some kinds =>
    let terms := nestedPinTermsSelf p st
    (List.range st.pins.length).all fun g =>
      match st.pins[g]? with
      | none => false
      | some gn =>
        match containerInfo? env gn.container with
        | none => false
        | some ciJ =>
          match containerOwnPinsSelf env gn.container with
          | none => false
          | some ownSelf =>
            match ciJ.members.head? with
            | none => false
            | some m₀ =>
              let memsJ := ciJ.members.map (·.name)
              let mapR := maps.getD g []
              let pinG := terms.getD g default
              (List.range ownSelf.length).all fun qK =>
                let q := mapR.getD qK st.pins.length
                match st.pins[q]?, kinds[q]? with
                | some qn, some ks =>
                  match containerInfo? env qn.container with
                  | none => false
                  | some ci =>
                    match ci.members[q - qn.grpBase]? with
                    | none => false
                    | some Jm =>
                      let memsK := ci.members.map (·.name)
                      (List.range ks.length).all fun j =>
                        match ks[j]?, Jm.ctors[j]? with
                        | some kf, some cJ =>
                          match cJ.type.stripPis (ci.nP + cJ.nFields) with
                          | none => false
                          | some (jbs, _) =>
                            (List.range kf.length).all fun l =>
                              match kf[l]?, jbs[ci.nP + l]? with
                              | some (r, _), some domJ =>
                                if mentionsMember memsK domJ.1 then true
                                else
                                  let W := ordTargetDom Jm.lps ci.nP ownSelf qK l domJ.1
                                  let Wn := ordHeadRed W
                                  -- **THE GUARD READS THE HEAD BELOW
                                  -- THE REDUCED TOWER** (task #315
                                  -- K.74), K.67's guard character for
                                  -- character, so the three rows still
                                  -- speak at exactly the same fields.
                                  -- `Wn` ITSELF is not stripped: the
                                  -- term equation below compares the
                                  -- two reduced mints towers and all,
                                  -- and that is the only place the
                                  -- PLANTED tower is compared.
                                  if !ordRootFired env memsJ ownSelf
                                      (ordHeadCut W) then true
                                  else if !(r == .recursive || r == .reflexive) then false
                                  -- **THE BLOCK'S OWN RECOMPUTATION IS
                                  -- CONSTANT-HEADED WHERE THE OWNER'S
                                  -- RAW ONE IS** (task #315 WIDE (f3)
                                  -- step 2).  One `getAppFn` match at
                                  -- a term this arm already computes;
                                  -- it is what the model spends where
                                  -- it used to ask the STORED
                                  -- domain's head, which is not the
                                  -- recomputation's and is refuted at
                                  -- three accepted blocks.
                                  --
                                  -- **AND BOTH SIDES ARE READ THROUGH
                                  -- THE ENVIRONMENT-FREE REDUCTION**
                                  -- (task #315 WIDE (f3) step 1,
                                  -- spelling (B)).  The guard is the
                                  -- owner's firing at `ordHeadRed`,
                                  -- which is K.67's own guard
                                  -- character for character, so the
                                  -- three rows speak at exactly the
                                  -- same fields; and the block's head
                                  -- is asserted at `ordHeadRed` of the
                                  -- block's recomputation, which is
                                  -- the owner's under the mint's
                                  -- substitution and therefore
                                  -- constant-headed wherever the
                                  -- owner's reduced mint is.  At a
                                  -- REDEX mint
                                  -- (`tests/e2e/nested_redex_owner.ndjson`)
                                  -- that is now TRUE on both sides,
                                  -- where the raw reading had to
                                  -- concede.
                                  else
                                    -- the RAW block head, unchanged and
                                    -- under its own RAW guard: the
                                    -- positivity walk's identity on the
                                    -- minted domain is read off it, and
                                    -- that consumer is not the head
                                    -- lookups' (see `#### K.69`).
                                    (match (ordTargetDom Jm.lps ci.nP terms q l
                                        domJ.1).getAppFn with
                                     | .const _ _ => true
                                     | _ => !ordRootFired env memsJ ownSelf W)
                                    &&
                                    (match ordRootInst m₀.lps ciJ.nP
                                        (l + domPiDepth
                                          (ordTargetDomL Jm.lps ownSelf qK domJ.1))
                                        pinG Wn with
                                    | none => true
                                    | some Wb =>
                                      ordHeadRed
                                        (ordTargetDom Jm.lps ci.nP terms q l domJ.1) == Wb)
                                    &&
                                    -- **THE COPY'S OWN TOWER IS THE
                                    -- CONTAINER'S PLUS THE ONE THE
                                    -- MINT PLANTS** (task #315 K.72),
                                    -- **AND THE MINT'S HALF IS
                                    -- MEASURED AT ITS HEAD NORMAL
                                    -- FORM** (task #315 K.73).
                                    -- The block's copy of this field
                                    -- carries a `Π`-prefix, and it has
                                    -- TWO sources: the container's own
                                    -- stored domain (`domPiDepth
                                    -- domJ.1`, which `ordTargetDom`
                                    -- strips before it substitutes)
                                    -- and the components the mint
                                    -- plants into the stripped BODY.
                                    -- Their SUM is the copy's, and the
                                    -- addressing is K.32's own —
                                    -- `stored`, the copy's stored
                                    -- constructor, its field `l`.
                                    --
                                    -- The second summand is
                                    -- `domPiDepth` of `ordHeadRed` of
                                    -- the recomputation and not of the
                                    -- recomputation itself, because
                                    -- the STORED copy is what the
                                    -- comparison's left-hand side
                                    -- measures and the install ran
                                    -- `normPosDomM` — a `whnf`-based
                                    -- walk — over the minted domain
                                    -- before it stored it.  So a mint
                                    -- that is a β/ζ-REDEX whose head
                                    -- normal form is a `Π` is stored
                                    -- WITH that binder
                                    -- (`tests/e2e/nested_redex_tower.ndjson`
                                    -- is the shape), and the raw
                                    -- reading under-counts it.
                                    --
                                    -- **IT SUBSUMES THE RAW
                                    -- COMPARISON AND IS NOT A SECOND
                                    -- ONE.**  Wherever the block's
                                    -- recomputation is constant-headed
                                    -- — which the arm above asserts at
                                    -- every field whose OWNER's raw
                                    -- mint fires, and which both
                                    -- corpora measure at every field —
                                    -- `ordHeadRed` is the identity
                                    -- (`ordHeadRed_const`) and the two
                                    -- comparisons are the same `Bool`.
                                    -- Off it the raw one can be FALSE
                                    -- at a stored copy that is
                                    -- perfectly well-formed, which
                                    -- would be a reject on an input
                                    -- official accepts.
                                    -- **AND THE TWO RECOMPUTED
                                    -- TOWERS AGREE, BINDER BY BINDER,
                                    -- AT EACH BINDER'S OWN CUT**
                                    -- (task #315 K.76).  This is the
                                    -- row above one level out: K.69
                                    -- carries the OWNER's reduced mint
                                    -- to the block's instantiation and
                                    -- compares it with the BLOCK's;
                                    -- K.76 does the same at each
                                    -- binder of the tower that mint
                                    -- stands under, at `l + i`.
                                    --
                                    -- Both sides are the SAME function
                                    -- at the SAME stored domain
                                    -- `domJ.1`, differing only in the
                                    -- component table — recomputation
                                    -- against recomputation, never the
                                    -- stored binders against a
                                    -- recomputation (see
                                    -- `ordTargetTele`).  `none` is
                                    -- K.69's own silence, the block
                                    -- pin's head not being a constant.
                                    --
                                    -- **IT DOES NOT SUBSUME K.73**:
                                    -- K.76 never reads `stored`, and
                                    -- K.73 is the only comparison the
                                    -- arm may make between the STORED
                                    -- copy's tower and the
                                    -- recomputation's.
                                    --
                                    -- **THE LENGTH HALF IS
                                    -- UNGUARDED**, and that is the one
                                    -- place this row speaks where K.69
                                    -- is silent — a block pin whose
                                    -- head is not a `.const`, which
                                    -- `replaceIfNested` never writes.
                                    -- It may be: the first summand is
                                    -- the same stored domain's tower
                                    -- on both sides (the level
                                    -- instantiation moves no binder)
                                    -- and the second is the same
                                    -- stripped body under two
                                    -- component tables, and neither
                                    -- `Expr.instantiateList` nor the
                                    -- β/ζ reduction turns a `Π` into a
                                    -- non-`Π` at the head.  The model
                                    -- needs it unconditionally: a
                                    -- `teleOfFields` congruence cannot
                                    -- start without the two lengths.
                                    (let tlO := ordTargetTele Jm.lps ci.nP ownSelf qK l domJ.1
                                     let tlB := ordTargetTele Jm.lps ci.nP terms q l domJ.1
                                     (tlO.length == tlB.length) &&
                                       (List.range tlO.length).all fun i =>
                                         match ordRootInst m₀.lps ciJ.nP (l + i) pinG
                                             (tlO.getD i default) with
                                         | none => true
                                         | some Tb => tlB.getD i default == Tb)
                                    &&
                                    match stored[p.k + q]? with
                                    | none => false
                                    | some a =>
                                      match a.ctors[j]? with
                                      | none => false
                                      | some (cvCa, _, nF) =>
                                        match cvCa.type.stripPis (p.nP + nF) with
                                        | none => false
                                        | some (cbs, _) =>
                                          match cbs[p.nP + l]? with
                                          | none => false
                                          | some domC =>
                                            (Expr.piBinders domC.1).1.length ==
                                              domPiDepth domJ.1
                                                + domPiDepth (ordHeadRed
                                                    (ordTargetDom Jm.lps ci.nP
                                                      terms q l domJ.1))
                              | _, _ => false
                        | _, _ => false
                | _, _ => true
  | _, _ => false

/-- The Bool the route records (task #315 K.69), on the same instance-map
table K.61, K.62 and K.67 read and the same field kinds
`nestedPinKinds` computes. -/
@[inline] def nestedOrdNormOk (env : Env) (p : NestedParts)
    (b : MutualBlock) (st : ElimState) (stored : List AuxStored) : Bool :=
  nestedOrdNormAt env p st stored (nestedInstMaps env st) (nestedPinKinds p b stored)

/-! ## THE POSITIVITY NORMALISATION ON THE MINTED COPY (task #315 K.42)

Lane L-B's `ordF`-LEFT arm (DESIGN §U.62) needs, at an ORDINARY field of
a copy's constructor, that the stored domain and the MINTED one — the
container's field instantiated at the pin's components, `mkCopy`'s
output BEFORE `replaceAllNested` — have the same reading.  The
model-side law for that is provably unavailable: the induction over the
rewrite closes every node but the firing occurrence, and the firing
occurrence needs `pinLeaf`, which is downstream of the very shape being
proved (at a self-nested container the circle is real).

The cheap route is a SECOND RUN of the walk the kernel already has.
`normPosDomM` is official's positivity normalisation; the install ran it
on the REWRITTEN domain and stored the result.  Run it on the MINTED
domain too and compare: at an ordinary field the two differ only at
replaced occurrences, neither a mimic nor a container application heads
a redex, and an ordinary field's stored domain mentions no member at all
— so the surviving term is the same on both sides, and the model gets
`interp (reading minted) = interp (reading w) = interp (reading stored)`
out of `normPosDomM_read_of` with the rewrite's own leg GONE.

The decline-shaped alternative — "a domain that mentions a member is
never classified ordinary" — is REFUSED: §U.62 (d) measures it
non-vacuous (`tests/e2e/nested_p20.ndjson`, accepted today), so it would
narrow the accept set on a shape official takes, which the maintainer's
standing rule forbids.  This form costs no accept set at all.

**The addressing is PURE and the run is ONE FLAT `mapM`.**
`nestedOrdDomPairs` is an `Option` walk that returns, per pin, per
constructor, per ordinary field, the triple (the field's depth, the
MINTED domain, the STORED domain) — all of it off the run's own records,
in exactly `nestedPinEdges`' three-layer shape, so the model addresses a
field with the established `mapM_option_inv` idiom.  `nestedOrdNorms` is
then a single `List.mapM` whose positional inversion is
`mapM_except_inv`. -/

/-- The ordinary fields' two domains, per pin, per constructor, per
field: `(p.nP + l, the MINTED domain, the STORED domain)`.

The minted constructor is recomputed the way K.28 certifies it —
`Expr.instPis` of the container's stored constructor at the pin's own
`lvls`/`Ds` — and opened at its FIELD binders from `p.nP`, which is the
spelling the model's `mintFieldRead` reads (`openPisAtFvars nF cI nP`,
`x.fvarTypeD` at depth `nP + l`).  The stored constructor is opened
twice, the parameters then the fields, as `normCtorValM` itself does. -/
def nestedOrdDomPairs (env : Env) (p : NestedParts) (st : ElimState)
    (stored : List AuxStored)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) :
    Option (List (Nat × Expr × Expr)) := do
  let kinds ← kinds?
  let rows ← (List.range st.pins.length).mapM fun q => do
    let t ← st.types[p.k + q]?
    let (Jn, lvls, Ds) ← t.src
    let a ← stored[p.k + q]?
    let ks ← kinds[q]?
    let ci ← containerInfo? env Jn
    let J ← ci.members.find? (fun J => J.name == Jn)
    if lvls.length != J.lps.length then none else
    let perCtor ← (List.range ks.length).mapM fun j => do
      let kf ← ks[j]?
      let cJ ← J.ctors[j]?
      let (cvS, _, nF) ← a.ctors[j]?
      let cI ← Expr.instPis (Expr.instantiateLevelParams J.lps lvls cJ.type) Ds
      let (xsM, _) ← openPisAtFvars nF cI p.nP
      let (_, crestS) ← openPisAtFvars p.nP cvS.type 0
      let (xsS, _) ← openPisAtFvars nF crestS p.nP
      let perField ← (List.range kf.length).mapM fun l => do
        -- **ORDINARY, OR A MEMBER TARGET** (lane L-B's request, task
        -- #315 M8 session 3): a field classified recursive or reflexive
        -- at a target BELOW `p.k` points at a MEMBER of the block being
        -- installed, not at a mimic, and there the stored domain is
        -- mimic-free — positivity admits a member head only with
        -- member-free telescope domains and index arguments — so the
        -- minted and the rewritten walk end at the SAME term and the
        -- comparison is the one this record already makes.  It is the
        -- PIN targets (`p.k ≤ t`) that would need the heavier rewritten
        -- form, and they are NOT widened here.
        let (r, t) ← kf[l]?
        if r == RecFieldKind.ordinary || t < p.k then
          let xM ← xsM[l]?
          let xS ← xsS[l]?
          pure [(p.nP + l, xM.fvarTypeD, xS.fvarTypeD)]
        else pure ([] : List (Nat × Expr × Expr))
      pure perField.flatten
    pure perCtor.flatten
  pure rows.flatten

/-- **THE PIN-TARGET FIELDS' TWO DOMAINS** (task #315 K.51, lane L-B's
request): the jobs `nestedOrdDomPairs` deliberately leaves out — a copy
field classified recursive or reflexive at a target AT OR ABOVE `p.k`,
which points at a MIMIC rather than at a member of the block being
installed.  Same addressing, same triple `(depth, MINTED, STORED)`, so
the model reaches a field with the same `mapM_option_inv` idiom.

The two lists together cover every constructor field of every copy: a
field is ordinary, or a member target, or one of these. -/
def nestedPinDomPairs (env : Env) (p : NestedParts) (st : ElimState)
    (stored : List AuxStored)
    (kinds? : Option (List (List (List (RecFieldKind × Nat))))) :
    Option (List (Nat × Expr × Expr)) := do
  let kinds ← kinds?
  let rows ← (List.range st.pins.length).mapM fun q => do
    let t ← st.types[p.k + q]?
    let (Jn, lvls, Ds) ← t.src
    let a ← stored[p.k + q]?
    let ks ← kinds[q]?
    let ci ← containerInfo? env Jn
    let J ← ci.members.find? (fun J => J.name == Jn)
    if lvls.length != J.lps.length then none else
    let perCtor ← (List.range ks.length).mapM fun j => do
      let kf ← ks[j]?
      let cJ ← J.ctors[j]?
      let (cvS, _, nF) ← a.ctors[j]?
      let cI ← Expr.instPis (Expr.instantiateLevelParams J.lps lvls cJ.type) Ds
      let (xsM, _) ← openPisAtFvars nF cI p.nP
      let (_, crestS) ← openPisAtFvars p.nP cvS.type 0
      let (xsS, _) ← openPisAtFvars nF crestS p.nP
      let perField ← (List.range kf.length).mapM fun l => do
        let (r, t) ← kf[l]?
        if r == RecFieldKind.ordinary || t < p.k then pure ([] : List (Nat × Expr × Expr))
        else do
          let xM ← xsM[l]?
          let xS ← xsS[l]?
          pure [(p.nP + l, xM.fvarTypeD, xS.fvarTypeD)]
      pure perField.flatten
    pure perCtor.flatten
  pure rows.flatten

/-- **THE ELIMINATION'S OWN REWRITE DATA, recovered from the FINAL
state** (task #315 K.51): `elimNested` starts its loop at the block's
FIRST former's parameter openers and binders (premise B, K.8), and the
loop rewrites CONSTRUCTORS only — a type's own `type` field is never
touched — so the final state carries them still. -/
def nestedRewriteData (p : NestedParts) (st : ElimState) :
    Option (List Expr × List (Expr × BinderMeta)) := do
  let t₀ ← st.types.head?
  let (params, _) ← openPisAtFvars p.nP t₀.type 0
  let (pbs₀, _) ← t₀.type.stripPis p.nP
  pure (params, pbs₀)

/-- **THE REWRITE AFTER THE NORMALISATION** (task #315 K.51): each
normalised MINTED domain, rewritten by the elimination's own
`replaceAllNested` at the FINAL state, IS the stored one — and the
state does not grow, which says the re-run minted nothing.

This is the clause the pin targets need and the ordinary fields do not:
there the stored domain mentions no member at all, so the minted and
the rewritten walk end at the same term (K.42).  At a pin target the
stored domain is headed by the MIMIC while the minted one is headed by
the CONTAINER, so the two legs differ by exactly this rewrite — and the
model reads the target off the minted domain, where the container
application still stands, instead of off the stored one, which is what
`pinLeaf` would need and is circular. -/
def nestedPinRewrites (env : Env) (p : NestedParts) (st : ElimState)
    (params : List Expr) (pbs₀ : List (Expr × BinderMeta))
    (jobs : List (Nat × Expr × Expr)) (ws : List Expr) : Bool :=
  (jobs.zip ws).all fun (je, w) =>
    match replaceAllNested env (p.lps.map Level.param) params pbs₀ st w with
    | .ok (w', st') =>
      w' == je.2.2 && st'.types.length == st.types.length &&
        st'.pins.length == st.pins.length
    | .error _ => false

/-- **THE PINS' COMPONENTS, REWRITTEN** (task #315 K.59, lane L-E's
request):
every component of a pin's argument spine, rewritten by the
elimination's own `replaceAllNested` at the FINAL state — and the state
does not grow, which says the re-run minted nothing.  This is K.51's
clause at the spine's COMPONENTS instead of at the copies' field
domains, and it is what three of the model's arms (`recF`, `es`,
`ordF`-left) read: without it they hold terms mentioning constants they
cannot interpret.

The carrier is the walk itself, RECOMPUTED, exactly as K.51's
(`nestedPinRewrites`): no field is added to `NestedPin` and no
parameter to the elimination.  A field would mean touching `mkCopies`
and every `ElimState` literal, which is where the `mintedAt` trap bit
(`NestedElim.lean`: a literal naming three fields reset the fourth on
every mint, silently, on two Mathlib blocks).

The COPY-NAME correspondence the consumers also need — which copy name
belongs to which auxiliary index — costs nothing here: `nestedCopyNames
k st` is `(st.types.drop k).flatMap …`, so the `j`-th copy's block IS
`st.types[k + j]` positionally, and that ships as a lemma rather than
as a Bool. -/
def nestedPinCompRewrites (env : Env) (p : NestedParts) (st : ElimState)
    (params : List Expr) (pbs₀ : List (Expr × BinderMeta)) :
    Option (List (List Expr)) :=
  st.pins.mapM fun q =>
    q.pin.getAppArgs.mapM fun c =>
      match replaceAllNested env (p.lps.map Level.param) params pbs₀ st c with
      | .ok (c', st') =>
        if st'.types.length == st.types.length && st'.pins.length == st.pins.length then
          some c'
        else none
      | .error _ => none

/-- The Bool the route records: the rewrite runs at every component of
every pin.  **Unconditional** — not one of `nestedPinChecks`' clauses,
which are entered only at `mode.verifiedChecks`: the consumers need this
in every mode, and a gated check is `true` in the trusted one. -/
def nestedPinCompsOk (env : Env) (p : NestedParts) (st : ElimState) : Bool :=
  match nestedRewriteData p st with
  | some (params, pbs₀) => (nestedPinCompRewrites env p st params pbs₀).isSome
  | none => false

/-- The second run: the positivity normalisation of every minted
ordinary domain, at the environment holding the block's own FORMERS —
the one the model's readings are taken in.

**Any error of the inner walk becomes `.internal`.**  `normPosDomM`
throws `.invalid` at a non-positive occurrence and `.notImplemented` on
fuel; a certification-only record must never turn an accepted stream
into a REJECT or a DECLINE, so the handler reclassifies.  (It cannot
fire either way: the rewrite replaces a group occurrence by a mimic,
which is a member of the auxiliary block too, so the minted and the
rewritten walk see a member at exactly the same nodes.) -/
def nestedOrdNorms (ops : CheckerOps m) (env : Env) (memberNames : List Name)
    (jobs : List (Nat × Expr × Expr)) : m (List Expr) :=
  jobs.mapM fun je =>
    tryCatchThe CheckError (normPosDomM ops env memberNames je.1 1024 je.2.1)
      (fun _ => throw (.internal "nested: the positivity normalisation of a minted copy \
        field does not run"))

/-- The pin-target jobs' second run, `nestedOrdNorms` verbatim at the
other job list (task #315 K.51): any error of the inner walk becomes
`.internal`, for the same reason. -/
def nestedPinNorms (ops : CheckerOps m) (env : Env) (memberNames : List Name)
    (jobs : List (Nat × Expr × Expr)) : m (List Expr) :=
  jobs.mapM fun je =>
    tryCatchThe CheckError (normPosDomM ops env memberNames je.1 1024 je.2.1)
      (fun _ => throw (.internal "nested: the positivity normalisation of a minted copy \
        field at a pin target does not run"))

/-- **THE PINS' CHECKS, ON ONE WALK** (task #315 K.46; all
certification-only until K.60, which is not).  K.26, K.32, K.37 and
K.41 each ask a question about the copies.
field kinds, and each used to recompute them: `nestedPinKinds` ran FOUR
times per nested block (twice directly, and twice more under
`nestedPinEdges`, which K.37 calls and K.41 reaches through
`nestedPinRootGroup`), and the edge list TWICE.  Here the kinds and the
edges are computed ONCE and threaded, and each check keeps its own
clause, its own message and its own conjunct of the run relation:
`nestedPinKindsAt p st kinds? = nestedPinKindsOk p b st stored` and its
three twins hold by definition, so nothing the model consumes moves.

The certification-only group is skipped at `.trusted` — these are the
model tier's evidence, not the kernel's (`certOnly`'s docstring).  It
used to be the WHOLE body, and the shared `kinds?` sat inside the mode
test for exactly that reason (a `let` is strict, so a `let` above the
test would have run the walk in trusted mode for nothing).  **K.60
changed that**: it is unconditional — its consumer reads it in every
mode — so the classification is needed in every mode too, and the `let`
is hoisted and SHARED with it rather than recomputed beside the group.

Measured, and the measurement is worth keeping: the shared and the
unshared arrangements cost the SAME (+0.128 % and +0.129 % of a Mathlib
shadow run), so the second classification walk was never K.60's price —
its own traversal of the containers' stored constructors is.  The
shared form is kept because it is one walk rather than two and because
it needs no call-site change in either route. -/
def nestedPinChecks (ops : CheckerOps m) (env envN : Env) (p : NestedParts) (b : MutualBlock)
    (st : ElimState) (stored : List AuxStored) : m Unit :=
  -- ONE classification of the copies' fields (K.46), HOISTED out of the
  -- mode test by K.60, which reads it in EVERY mode.  The reference
  -- graph stays inside the gate — nothing unconditional reads it.
  let kinds? := nestedPinKinds p b stored
  -- ONE reference graph (K.46), HOISTED out of the mode test too, by
  -- K.62 — which reads it in EVERY mode, for the same reason K.60 reads
  -- the classification in every mode
  let edges? := nestedPinEdgesAt env p st stored kinds?
  -- ONE instance-map table (K.61), shared by K.61 and K.62
  let maps? := nestedInstMaps env st
  -- ONE walk of the containers' stored constructors for K.60 AND K.63
  -- (their guards are disjoint — a `Π`'s `getAppFn` is never a
  -- `.const` — and so are their per-field environment lookups, so the
  -- fold shares the constructor telescopes and one `containerInfo?`
  -- per pin); the pair's components carry the two records' verdicts so
  -- each throw site names the right one
  let copyF := nestedCopyFieldsAt env p st kinds?
  -- **A CONTAINER'S NESTED FIELD LANDS ON A BLOCK PIN** (task #315
  -- K.60): at a container field headed by another stored container
  -- whose parameter part carries one of the container's own members,
  -- the copy's corresponding field is classified `.recursive` into a
  -- PIN.  K.32's twin, running the other way — the direction the
  -- model's `pinF` arm needs.  UNCONDITIONAL, and `.internal`: the
  -- consumer reads it in every mode, and a `certOnly` check is `true`
  -- in the trusted one.  It is the one check in this group that is not
  -- certification-only, which is why it stands before the mode test.
  --
  -- **IF THIS EVER FIRES** the elimination's classification of a copy
  -- field disagrees with its container's: that is a defect in the
  -- ROUTE, not in the stream, and the answer is never to relax the
  -- check.  See DESIGN "#### K.60".
  if !copyF.1 then
    throw (.internal "nested: a container's nested field is not classified recursive \
      into a pin of the block")
  -- **A CONTAINER'S REFLEXIVE NESTED FIELD LANDS ON A BLOCK PIN**
  -- (task #315 K.63, lane PINF's request): K.60's guard one `Π`-tower
  -- down, where K.60 claims nothing by construction.  Same walk, same
  -- gating (none), same category; the model's `pinF` arm at a
  -- REFLEXIVE nested field has no other producer for its `hkA`.
  --
  -- **IF THIS EVER FIRES** the elimination's classification of a
  -- copy's reflexive field disagrees with its container's: a defect in
  -- the ROUTE, not in the stream, and the answer is never to relax the
  -- check.  See DESIGN "#### K.63".
  else if !copyF.2 then
    throw (.internal "nested: a container's reflexive nested field is not classified \
      reflexive into a pin of the block")
  -- **THE CONTAINER INSTANCE MAP** (task #315 K.61): every own pin of
  -- every pin's container, instantiated at that pin's own levels and
  -- components, IS a pin of the block (totality), and a copy's field at
  -- one of those own pins carries the map's value as its recorded
  -- target.  K.41's converse, and a FUNCTION where K.41 has only a
  -- covering — the map may COLLAPSE, and injectivity is not checked.
  -- UNCONDITIONAL, and `.internal`: the wide identification reads it in
  -- every mode, and a `certOnly` check is `true` in the trusted one.
  --
  -- **IF THIS EVER FIRES** the elimination's instance map disagrees
  -- with its own pin table — a defect in the ROUTE, not in the stream,
  -- and the answer is never to relax the check.  See DESIGN "#### K.61".
  else if !nestedInstMapOkAt env p st maps? kinds? then
    throw (.internal "nested: a container's own pin is not the block pin the copy's \
      field records")
  -- **A REWRITTEN ORDINARY FIELD LEAVES THE INSTANCE** (task #315
  -- K.62, extended by K.66): at an `ordF`-right edge — a reference
  -- whose container-side field mentions no member of the container's
  -- own group — the recorded target is OUTSIDE the instance map's
  -- image (K.62, the container's own pins' half) AND outside the mint
  -- GROUP (K.66, the container's members' half).  A negative clause on
  -- K.61's table and on the pin's own record, with no walk of its own.
  -- UNCONDITIONAL and `.internal`, for K.61's reason.
  --
  -- **IF THIS EVER FIRES** a rewritten ordinary field re-entered the
  -- instance, which refutes the argument that such a target's container
  -- is not one of the container's own classes — again a defect in the
  -- ROUTE.  See DESIGN "#### K.62".
  else if !nestedOrdOutsideAt st maps? edges? then
    throw (.internal "nested: a rewritten ordinary field's target is inside the \
      container instance")
  -- **A REWRITTEN ORDINARY FIELD'S TARGET IS THE OWNER'S OWN CLASS**
  -- (task #315 K.67): K.62's positive twin at the same guard.  K.62
  -- says where the target is NOT; the wide identification's PIN half
  -- needs where it IS — the image of the class the OWNING container
  -- gave the same field, recomputed from the container's STORED
  -- constructor at the owner's own components, because no `_nested`
  -- constant survives the restore.  UNCONDITIONAL and `.internal`, for
  -- K.61's reason, on K.61's own table and K.46's field kinds.
  --
  -- **AND ITS THREE ARMS** (task #315 K.70): the instance map's image
  -- of a minted group is contiguous in member order; the positive row
  -- holds at a field the container calls RECURSIVE too; and where the
  -- OWNER's own recomputation did not fire the target leaves the
  -- owner's instance altogether — K.62/K.66's content one nesting
  -- level up.
  --
  -- **IF THIS EVER FIRES** the block's rewrite of a copy disagrees with
  -- the container it copied — a defect in the ROUTE, not in the
  -- stream, and the answer is never to relax the check.  See DESIGN
  -- "#### K.67" and "#### K.70".
  else if !nestedOrdTargetAt env p st maps? kinds? then
    throw (.internal "nested: a rewritten ordinary field's target is not the owning \
      container's own class")
  -- **AND IT IS THIS BLOCK'S OWN CLASS, BY ITS OWN RECOMPUTATION**
  -- (task #315 K.68): K.67's SELF-RELATIVE twin, the half a LATER
  -- block reads of this one.  No owner, no parent, no instance map;
  -- the same walk and the same guard, minus K.67's `p.k ≤ t` bound,
  -- because this block's own recomputation may name a MEMBER as
  -- easily as a pin.  UNCONDITIONAL and `.internal`, for K.61's
  -- reason.
  --
  -- The container-RECURSIVE fields are in it too (task #315 K.71),
  -- because arm (A)'s pin half needs this row CARRIED.
  --
  -- **IF THIS EVER FIRES** the elimination's rewrite of a copy names a
  -- class its own substitution does not — a defect in the ROUTE, not
  -- in the stream.  See DESIGN "#### K.68" and "#### K.71".
  else if !nestedOrdSelfTargetAt env p st kinds? then
    throw (.internal "nested: a rewritten ordinary field's target is not the block's own \
      class")
  -- **AND ITS DOMAIN IS THE OWNER'S, ONE SUBSTITUTION APART** (task
  -- #315 K.69): K.67 and K.68 compare the two copies' TARGETS; this
  -- compares their field DOMAINS, at the one guard under which the
  -- positivity normalisation may be pushed across the block's
  -- instantiation — the OWNER's own recomputation already at a
  -- constant inductive head, hence its own normalisation
  -- (`normPosDomM_indApp`), hence head-normal after the substitution
  -- too.  Where the root did NOT fire the row is silent: that is the
  -- mixed corner the model closes with an entry.  UNCONDITIONAL and
  -- `.internal`, for K.61's reason.
  --
  -- **IF THIS EVER FIRES** the block's copy of a container field is
  -- not the owner's copy substituted — a defect in the ROUTE, not in
  -- the stream, and the answer is never to relax the check.  See
  -- DESIGN "#### K.69".
  else if !nestedOrdNormAt env p st stored maps? kinds? then
    throw (.internal "nested: a rewritten ordinary field's domain is not the owning \
      container's domain instantiated")
  else if !ops.mode.verifiedChecks then pure () else
  let roots := nestedPinRootGroupAt p st (nestedPinInstAt st edges?)
  -- **THE COPIES' RECURSIVE TARGETS** (K.32): a copy field the aux
  -- block classified recursive into its own group comes from a
  -- container field that was a group occurrence at the parameter spine
  if !nestedCopyTargetsAt env p st stored kinds? then
    throw (.internal "nested: a copy's group-recursive field does not come from the \
      container's own recursion")
  -- **THE FIELD KINDS AT THE PINS** (K.26, §U.1 (c) fact 6): the
  -- classification the scratch install decided, recomputed on the
  -- constructors it stored — the container's, at the pin's components —
  -- so that the model tier reads a pin's field kinds off the run instead
  -- of re-deciding positivity at the container
  else if !nestedPinKindsAt p st kinds? then
    throw (.internal "nested: a stored field at a pin is not classified ordinary, \
      recursive or reflexive into the block")
  -- **THE PINS' CONTAINER INSTANCES AND RANK** (K.37): every own
  -- reference stays in the instance, every other one goes to a strictly
  -- smaller rank — the model's induction measure for step (iii)
  else if !nestedPinRankAt st edges? then
    throw (.internal "nested: the pins' container instances are not well-founded")
  -- **THE PIN PAIRING AT A NOT-OWN EDGE** (K.41): every pin of a
  -- container instance that is not one of the root group's own members
  -- IS a pin the ROOT CONTAINER's own elimination minted, at the root
  -- pin's own levels and components — all four of `ClassPin`'s data in
  -- ONE equality, off the two recorded tables
  else if !nestedPinRootPairAt env st roots then
    throw (.internal "nested: a pin is not one the instance's root container pinned")
  -- **THE POOL AS THE INSTANCE MAP'S IMAGE, AND K.62 AT THE MINT GROUP**
  -- (K.75): the two clauses the label half of the WIDE route's step
  -- reads K.41 and K.62 with — K.41's membership hands over an
  -- ARBITRARY member of the root group and a pin TERM, and the
  -- contradiction that puts a rewritten ordinary field's target in
  -- another instance needs both at the INDEX level, at that member.
  -- Neither clause walks: both are predicates on the tables already
  -- bound above.  Measured at zero fires on the shadow suite,
  -- `init-full` and Mathlib in both modes; see DESIGN "#### K.75".
  --
  -- **IF THIS EVER FIRES** either a pin of an instance is not in the
  -- root group's own-pin image (clause 1), or a rewritten ordinary
  -- field re-entered a SIBLING member's instance (clause 2) — a defect
  -- in the ROUTE, not in the stream, and the answer is never to relax
  -- the check.
  else if !nestedPinPoolGrpAt st maps? edges? roots then
    throw (.internal "nested: a pin of an instance is not in the root group's own-pin \
      image, or a rewritten ordinary field re-enters the mint group's instance")
  -- **THE NOT-OWN REFERENCES' ORDER** (K.57): a reference that LEAVES
  -- the instance goes to a container declared strictly earlier — the
  -- well-founded order the model's step (iii) inducts on at a
  -- constant-headed field.  Same-container references cannot appear
  -- here at all: the ownership bit is `mentionsMember` against the
  -- container's own group, which contains the container.
  else if !nestedPinOrderAt env p st stored kinds? then
    throw (.internal "nested: a not-own reference does not go to an earlier-declared container")
  -- **THE POSITIVITY NORMALISATION ON THE MINTED COPY** (K.42): at every
  -- ORDINARY field of every copy's constructor, the stored domain IS the
  -- normalisation of the MINTED one, so the model's `ordF`-left arm gets
  -- its reading identity with the rewrite's own leg gone.  The walk is
  -- the install's, run a second time, on the shared field kinds.
  else do
    let jobs ← unwrapOr (nestedOrdDomPairs env p st stored kinds?)
      (.internal "nested: the minted copies' ordinary field domains are not readable")
    let ws ← nestedOrdNorms ops envN b.memberNames jobs
    unless ws == jobs.map (·.2.2) do
      throw (.internal "nested: an ordinary copy field's stored domain is not the         positivity normalisation of the minted one")
    -- **THE SAME WALK AT A PIN TARGET, REWRITTEN** (K.51): there the
    -- stored domain is headed by the mimic and the minted one by the
    -- container, so the normalisation's output has to be rewritten
    -- before the comparison — by the elimination's own
    -- `replaceAllNested`, at the FINAL state, which therefore mints
    -- nothing
    let (params, pbs₀) ← unwrapOr (nestedRewriteData p st)
      (.internal "nested: the elimination's rewrite data is not readable")
    let jobsP ← unwrapOr (nestedPinDomPairs env p st stored kinds?)
      (.internal "nested: the minted copies' pin-target field domains are not readable")
    let wsP ← nestedPinNorms ops envN b.memberNames jobsP
    unless nestedPinRewrites env p st params pbs₀ jobsP wsP do
      throw (.internal "nested: a pin-target copy field's stored domain is not the \
        rewrite of the positivity normalisation of the minted one")

/-- **The nested install's SECOND STAGE**: everything after the auxiliary
block has been checked in its scratch environment — the read-back of what
it stored, the pins' certification checks, the restore of constructors,
recursor types and rules, the projection tables, and the three
post-checks.

A stage of `checkNested`, called from nowhere else, and split out so that
the route's INVERSION can be split too: `checkNested_inv`
(`ConLeche/Verify/Inductives/NestedInv.lean`) recovers a sixty-conjunct
run relation from one `.ok`, and as a single declaration it sat at the
elaborator's heartbeat budget — the next recorded check on this route
would have pushed it over, and `maxHeartbeats` is not available.  With
the cut here the inversion is two declarations, `checkNested_inv_front`
and `checkNested_inv_rest`, each with room, composed into the same
statement.

`env` is the pre-block environment, `envAux` the scratch one the
auxiliary install produced, `st` the elimination's state and `b` the
auxiliary block. -/
def checkNestedRest (ops : CheckerOps m) (env : Env) (p : NestedParts)
    (st : ElimState) (b : MutualBlock) (envAux : Env) : m Env := do
  let stored ← unwrapOr (auxStoredAll envAux b b.k)
    (.internal "nested: the auxiliary block's stored records")
  let R := restoreTbl p st
  let members := stored.take p.k
  let mimics := stored.drop p.k
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
  nestedPinsOk ops envAux p.nP st.pins
  -- 3. the formers, re-stored with the block's own `all` (our records
  -- carry no `all`, so the stored type and capabilities are official's
  -- unchanged re-add)
  -- **THE RESTORED FORMERS: FRESH, AND WITHOUT THE η BIT** (K.20).  Every
  -- member is re-stored with the record the AUXILIARY install stored for
  -- it, and that install's formers stage conses `{}`
  -- (`consMutualFormers`), so no restored former carries the η bit; and
  -- its name is free in the pre-block environment, which the same
  -- install's front door checked at this very environment.  Both are
  -- facts of an environment we built, and the model tier needs them to
  -- keep the η families closed across the install
  -- (`declNestedRun_etaClosed`); they are RECORDED here rather than
  -- re-derived through the scratch install's four cons stages, which is
  -- a `find?`-shadowing argument about our own environment.  A failure
  -- is `.internal`.
  unless members.all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) do
    throw (.internal "nested: a restored former is not a fresh non-eta family")
  -- **THE COPIES' SOURCES** (K.28): every minted type is `mkCopy`'s
  -- output at the source it records, so the model reads the
  -- copy-instantiation identities off the record instead of inverting
  -- the elimination.  A failure is `.internal`.
  unless certOnly ops.mode (nestedCopySrcOk env p st) do
    throw (.internal "nested: a minted auxiliary type is not the copy of the container \
      it records")
  -- **THE PINS' MINT GROUPS** (K.29): the group fields the mint wrote,
  -- certified — the segment, its size, the member order, the shared
  -- level instantiation and components.  A failure is `.internal`.
  unless certOnly ops.mode (nestedGroupsOk env p st) do
    throw (.internal "nested: a pin's mint group is not the container's group as minted")
  -- **A PIN'S COMPONENTS MENTION A MEMBER** (K.44): the parameter part
  -- of every pin's spine carries a member of the block's own group —
  -- lane L-E's `nestMention`, whose witness the elimination's own record
  -- does not pin down (it permits a COPY).  A failure is `.internal`.
  unless certOnly ops.mode (nestedPinMentionOk p st) do
    throw (.internal "nested: a pin's components mention no member of the block")
  -- **THE PINS' SCOPE** (K.30): every pin's free variables are the
  -- first former's openers, annotation included, and no loose bvar.
  unless certOnly ops.mode (pinsScoped p.nP st) do
    throw (.internal "nested: a pin's free variables are not the block's parameter openers")
  -- **THE PINS' LEVELS** (K.48): every level parameter a pin mentions is
  -- one of the block's own — `ContainerModeled.pinParams`' whole content
  -- at this site.  A failure is `.internal`.
  unless certOnly ops.mode (pinsLevelsOk p.lps st.pins) do
    throw (.internal "nested: a pin mentions a level parameter that is not the block's")
  -- **THE AUXILIARY APPLICATIONS** (K.35): every copy and copy
  -- constructor in the scratch block's read-back recursor types and
  -- rules is applied to `nP + arity` arguments whose first `nP` are the
  -- block's parameter variables — the precondition the restore's
  -- `args.drop nP` relies on.  A failure is `.internal`.
  unless certOnly ops.mode (nestedAuxAppsOk p st stored) do
    throw (.internal "nested: an auxiliary application in the block's read-back is not \
      at the block's parameters")
  -- **THE MINT PARENTS** (K.40): every recorded parent is an EARLIER
  -- pin, so an instance's root is its parent-minimal member and the
  -- covering walk the model needs is the parent chain.
  -- CERTIFICATION-ONLY, gated.  A failure is `.internal`.
  unless certOnly ops.mode (nestedPinParentOk p st) do
    throw (.internal "nested: a pin's mint parent is not an earlier pin")
  -- **THE PINS' FOUR CERTIFICATION-ONLY CHECKS** (K.26, K.32, K.37 and
  -- K.41), on ONE computation of the field kinds and the reference edge
  -- list (K.46).  Gated as a group; each check keeps its own clause, its
  -- own message and its own conjunct of the run relation.
  let env₁ := consNestedFormers members env
  nestedPinChecks ops env env₁ p b st stored
  -- **POST-CHECK (a), A THIRD TIME** (K.30): the pins typed at the
  -- environment holding the RESTORED FORMERS — the one `restoreCtors`
  -- runs at, and the one the model tier reads the block's own prefix
  -- model over.  ADDED, never substituted, so the accept set can only
  -- narrow; and it cannot narrow, because a pin mentions the pre-block
  -- constants and the block's members, which this environment holds
  -- exactly as the scratch one does.
  nestedPinsOk ops env₁ p.nP st.pins
  -- **THE PINS' CONSTANTS RESOLVE** (K.64): at that same environment,
  -- every constant a pin names is stored and every `.proj` node in it
  -- names a stored structure — what lets a container's pins' READINGS
  -- cross a later install's projection table.  UNCONDITIONAL, like
  -- K.59-K.63 and for the same reason: the consumer reads it in every
  -- mode.  A failure is `.internal`.
  unless pinsResolve env₁ st.pins do
    throw (.internal "nested: a pin names a constant the block's environment does not store")
  -- 4. the constructors, restored and re-checked (post-check (b))
  let ctorsR ← members.mapM fun a => restoreCtors ops env₁ R p.lps a.ctors
  let env₂ := consNestedCtors ctorsR.flatten env₁
  -- 5. the recursor types, restored and re-checked (post-check (b))
  let memberNames := (List.range p.k).map fun mIdx =>
    ((p.formers.getD mIdx default).1.name.str "rec")
  let mimicNames := (List.range p.numNested).map p.mimicRecName
  let cvRms ← restoreRecTys ops env₂ R p.lps memberNames members
  let cvRns ← restoreRecTys ops env₂ R p.lps mimicNames mimics
  -- **THE RESTORED RECURSORS' NAMES ARE PAIRWISE DISTINCT** (task #315
  -- K.39, lane M7-2's DESIGN §U.29 (s)).  The provision loop needs each
  -- name FRESH at the environment its cons runs at, and nothing else
  -- supplies it: `restoreRecTys_door` gives freshness at ONE
  -- environment, the same for every entry, so it separates none of
  -- them; and `b.blockNames.Nodup` covers the members' `T_m.rec` but
  -- not a mimic's `T₁.rec_j`, which is no scratch block name at all.
  -- Deriving it syntactically needs `Nat.repr` injectivity, which core
  -- does not carry.  It is the nested twin of the mutual route's own
  -- `blockNames.Nodup` check.  CERTIFICATION-ONLY, gated; a failure is
  -- `.internal` and cannot happen — the members' names are the block's,
  -- already `Nodup`, and the mimics' are `T₁.rec_1, T₁.rec_2, …`.
  unless certOnly ops.mode
      (decide ((cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)) do
    throw (.internal "nested: two restored recursors carry one name")
  -- **THE AUXILIARY NAMES AND THE RESTORED RECURSORS' ARE DISJOINT**
  -- (task #315 K.45, lane M7-2's DESIGN §U.29 (ll)).
  -- `RestoreAgree.auxFresh` at the restored PROVISIONED environment
  -- needs every auxiliary name absent there, and the provision below
  -- adds exactly these `k + nPins` recursor names — so it needs the two
  -- lists disjoint, and that is NOT derivable.  The mint is
  -- `mkUniqueName env (Name.appendName nestedPrefixName J.name) …`, so a
  -- copy's name is `.str X (s ++ "_" ++ toString idx)`, while
  -- `p.mimicRecName j` is `.str T₁ ("rec" ++ "_" ++ toString (j + 1))` —
  -- the SAME shape, so separating them syntactically needs
  -- `toString`/`Nat.repr` injectivity, which core does not have.  That
  -- is exactly why K.39 above is a recorded check and not a proof.
  -- CERTIFICATION-ONLY, gated; a failure is `.internal` and cannot
  -- happen — `mkUniqueName` skips every name the PRE-BLOCK environment
  -- holds and the restored recursors are named after the block's own
  -- formers, which `copiesFresh` keeps out of the minted set.
  unless certOnly ops.mode
      (R.auxNames.all fun n =>
        !((cvRms.map (·.name) ++ cvRns.map (·.name)).contains n)) do
    throw (.internal "nested: an auxiliary name collides with a restored recursor")
  let provisions := (cvRms.zip (members.map fun a => (a.mI, a.rP)))
    ++ (cvRns.zip (mimics.map fun a => (a.mI, a.rP)))
  let envR := provisionNestedRecs provisions env₂
  -- 6. the rules, restored and re-checked (post-check (b))
  let rulesM ← (cvRms.zip members).mapM fun (cvRa, a) =>
    restoreRules ops envR R cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules
  let rulesN ← (cvRns.zip mimics).mapM fun (cvRa, a) =>
    restoreRules ops envR R cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules
  -- **THE RESTORED RULES' RESCUE BITS** (K.50): a set bit IS the
  -- provisioned environment's own verdict — `hctorStored`'s other two
  -- conjuncts, recorded where `ConstWF` asks them.  `restoreRules`
  -- copies the SCRATCH rule's bits while replacing its constructor, so
  -- the obligation is a transport across two environments AND two
  -- constructor names that no lemma relates.  A failure is `.internal`.
  unless certOnly ops.mode
      (nestedRuleBitsOk envR.find? (cvRms.zip rulesM ++ cvRns.zip rulesN)) do
    throw (.internal "nested: a restored rule carries a K or eta rescue bit")
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
  nestedPinsOk ops env₄ p.nP st.pins
  -- 9. POST-CHECK (c): the stream's records against the generated ones
  -- **THE RECORDS' ARGUMENT SUMS ARE THE INSTALL'S** (task #315 K.54):
  -- the stream's `(mI, rP)` per recursor against the read-back's.  The
  -- CACHED mirror's skeleton needs the stored numbers to be a function
  -- of the record rather than of the elimination, and the pure route
  -- carries the same check so that the two routes' accept sets stay
  -- identical.
  unless p.memberRecNums == (members.map fun a => (a.mI, a.rP)) &&
      p.mimicRecNums == (mimics.map fun a => (a.mI, a.rP)) do
    throw (.invalid "nested: a recursor record's argument sums are not the ones the \
      auxiliary install computed")
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
  -- **THE READ-BACK** (task #315 K.34): `containerInfo?` of the
  -- environment this route produced, at every member of the block it
  -- installed, is the block's own data — the reading the model's
  -- environment field is quantified over.  The mimics are NOT members:
  -- the motive walk stops at the first motive that is not a real
  -- member's, which is the first mimic's.  It cannot fire.
  unless certOnly ops.mode (blockReadBackOk env₄ p.nP ((members.zip ctorsR).map fun (a, cs) =>
      (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))) do
    throw (.internal "nested: the installed block does not read back as its own")
  -- **THE MIMICS' STORED TYPES ARE THE RECORDED PINS** (K.47): the
  -- own-pin reader, run on the block this route just installed at the
  -- block's own levels and parameter openers, returns the recorded pin
  -- list verbatim — the substantive half of
  -- `ContainerModeled.ownPins`.  A failure is `.internal`.
  unless certOnly ops.mode (nestedOwnPinsOk env₄ p st) do
    throw (.internal "nested: the mimics' stored types are not the recorded pins")
  -- **THE OWN-PIN TABLE IS THE ROUTE'S OWN** (K.43): the mimic recursors
  -- this route stored are exactly `T₁.rec_1 … T₁.rec_numNested`, so the
  -- own-pin reader's walk visits exactly that many entries at EVERY
  -- instantiation.  CERTIFICATION-ONLY, gated; a failure is `.internal`.
  unless certOnly ops.mode
      (blockOwnMimicsOk env₄ (p.formers.headD default).1.name p.numNested) do
    throw (.internal "nested: the installed block's mimic recursors are not the route's")
  pure env₄

/-- **Check and install a recognised NESTED block** (see the module
docstring): official's two syntactic front guards, the elimination, the
auxiliary mutual block checked in a scratch environment, the restore,
and the three post-checks.  Only the restored constants are stored.

Everything from the auxiliary block's read-back onwards is
`checkNestedRest`, for the reason its docstring gives. -/
def checkNested (ops : CheckerOps m) (env : Env) (p : NestedParts) : m Env := do
  -- 0. official's `check_no_nested_aux` and `check_uniform_ind_occs`
  let ctorTypes := p.ctors.map (fun c => c.cv.type)
  unless p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      ctorTypes.all (fun t => !t.mentionsNestedAux) do
    throw (.invalid "invalid declaration, it uses the reserved prefix '_nested'")
  unless uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP ctorTypes do
    throw (.invalid "invalid occurrence of datatype being declared: it must be applied \
      to the parameters and universe levels of the mutual declaration")
  -- 1. THE ELIMINATION'S INPUTS, ANNOTATED (K.12): the formers as the
  -- install will store them and the constructors at the environment
  -- holding those formers — so every piece the elimination instantiates,
  -- closes over or pins is annotated, and every copy it mints is
  -- annotated BY CONSTRUCTION, with no annotation pass left to run on it
  let fmsA ← nestedAnnotFormers ops env p.nP p.formers
  let ctorsA ← nestedAnnotCtors ops (nestedFormerEnv fmsA env) p.ctors
  -- 2. the elimination, and the mimic count against the stream's records
  let st ← nestedLift (m := m) (elimNested env p.nP p.lps (nestedTypes0 p fmsA ctorsA))
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
  -- THE CONTAINERS' FACTS (K.14, the model lane's DESIGN §M.28): every
  -- container the elimination pinned has uniform occurrences of its own
  -- group in its stored constructors, and every member's stored
  -- recursor keeps its elimination universe out of the block's level
  -- parameters (large) or eliminates into `Prop` (small).  All three
  -- hold of any container this checker installed — a failure is a
  -- broken environment, not a stream's fault.
  unless certOnly ops.mode (nestedContainersOk env st.pins) do
    throw (.internal "nested: a container the elimination pinned fails a fact its own \
      install established")
  -- **THE PINS' COMPONENTS REWRITE** (task #315 K.59, lane L-E's request):
  -- every component of every pin's argument spine goes through the
  -- elimination's own `replaceAllNested` at the FINAL state, and the
  -- state does not grow.  UNCONDITIONAL, and `.internal`: three of the
  -- model's arms read the rewritten components, and a `certOnly` check
  -- is `true` in trusted mode.  Measured before it landed: 87 shadow
  -- blocks over e2e+arena and Mathlib, zero fires, firing control 43/43
  -- where the check is reached, and +0.025 % of a Mathlib shadow run
  -- (nothing today — the route is not dispatched).
  --
  -- **IF THIS EVER FIRES** the elimination's rewrite is not reproducible
  -- at the final state: that is a defect in the ROUTE, not in the
  -- stream, and the answer is never to relax the check.  See DESIGN
  -- "#### K.59 — the pins' components, rewritten".
  unless nestedPinCompsOk env p st do
    throw (.internal "nested: a pin's components do not rewrite at the final state")
  -- 2. the auxiliary mutual block, checked in a SCRATCH environment
  let b ← unwrapOr (auxBlock p st)
    (.invalid "invalid nested inductive datatype, ill-formed declaration")
  -- **THE BLOCK'S MEMBER INDEX COUNTS ARE THE RECORD'S** (task #315
  -- K.58): the auxiliary block reads each member's index count off the
  -- ANNOTATED former's telescope (`auxIdxCount`), while the recogniser
  -- read it off the stream's; the two decide structure-likeness (and so
  -- the projection tables) and nothing until now checked that they
  -- agree.  Not `certOnly`: the cached mirror's SKELETON is a function
  -- of the record in EVERY mode, and a gated check is `true` in the
  -- trusted one.  Measured before it landed — 85 blocks, 102 counts,
  -- zero differences over e2e+arena, `init-full` and Mathlib, with a
  -- firing control and a reachability control.
  --
  -- **IF THIS EVER FIRES, WIDEN THE SKELETON** — carry the auxiliary
  -- count in it and prove the two drivers agree on that — rather than
  -- keep rejecting.  See DESIGN "#### K.58 — the auxiliary block's
  -- member index counts, pinned".
  unless p.formers.map (·.2) == (b.formers.take p.k).map (·.2) do
    throw (.invalid "nested: a member's index count is not the one its declaration carries")
  -- `auxRoute := true` (K.10, widened by K.12): EVERY member of this
  -- block is pre-annotated — the real members are the constants the
  -- input-annotation stage checked, and the copies are minted out of
  -- them and out of the containers' stored types at annotated pins — so
  -- the install's front doors (the formers' and the constructors')
  -- skip the annotation walk throughout and the stored types are the
  -- minted ones.  Every check still runs, `inferType` included, which
  -- is what validates each binder datum.  The grade is the CALLER's
  -- single explicit opt-in for the whole block: no name is
  -- interpreted.
  let envAux ← checkMutualCore ops env b none true
  checkNestedRest ops env p st b envAux

end ConLeche
