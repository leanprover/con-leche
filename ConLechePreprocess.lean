import InductiveModels.Main

/-!
# `con-leche-preprocess` — the preprocessor, told what con-leche handles itself (#178)

`lean-inductive-models` reduces an export's inductive declarations to a
five-member basis (`Eq`, `Nat`, `PUnit`, `PSigma'`, `Quot`) plus ordinary
definitions and theorems.  Since its `45d1346` it is a *library*
(`InductiveModels.main args (native := …)`), and the consumer says which
inductive blocks it handles itself: an accepted block is left unmodelled and
reported on a `native` line (`Dep: native — left to the consumer`), outside the
decline count.

con-leche is such a consumer.  Its **direct simple-structure path**
(`ConLeche/Kernel/Direct/Parts.lean`, task #175 W4c) installs a non-recursive,
single-constructor, index-free inductive block *from the reference checks
alone* — no `_model` artifact is read, and since the W4c priority gate the
artifacts of such a block are dead weight in the stream: recognition wins
whether or not a model is present.  This executable is the checker's own
`main` for the preprocessor, telling it not to generate that dead weight.

## THE PREDICATE AND THE RECOGNISER

`conlecheNative` below must accept **only** blocks `ConLeche.directPartsCore?`
accepts: a block accepted here gets no model, so a block the recogniser then
rejects would reach the checker as a bare inductive it cannot install — a
decline where the stream used to be accepted.  The predicate is therefore
written as a mirror of `directPartsCore?`, conjunct for conjunct, and where a
conjunct cannot be mirrored it is *dropped in the strict direction* (the
predicate rejects) or argued below.

`directPartsCore?` matches `[.indInfo cvT _, .ctorInfo cvC nP nF,
.recInfo cvR mI rP [rule]]` and demands, in order:

| `directPartsCore?` | mirrored here as |
| --- | --- |
| exactly one type, one constructor, one recursor, one rule | `.induct [type] [ctor] [rec]`, `rec.rules = [rule]` |
| `cvR.name == T.str "rec"` | `rec.name == type.name.str "rec"` |
| `cvC.levelParams == lps` | `ctor.levelParams == type.levelParams` |
| `reservedBasisNames.contains {T, C, T.rec} == false` | `conlecheReservedBasisNames` (copied from `ConLeche/Kernel/Basis/Names.lean`) |
| `mI == nP + 2 ∧ rP == nP + 2` (with `mI = rnP+rnM+rnm+rnI`, `rP = rnP+rnM+rnm`, from `ConLeche/Frontend/ExportC.lean`) | `rec.numIndices == 0 ∧ rec.numMotives == 1 ∧ rec.numMinors == 1 ∧ rec.numParams == ctor.numParams` |
| `rule.ctor == C ∧ rule.nfields == nF` | the same, on `ERecRule` |
| `rule.rhs.stripLams (nP+2+nF)` is `directRuleBody nF` | *not mirrored* — see below |
| `cvT.type.stripPis nP` ends in `.sort` | `conlecheFormerTelescope` — `numParams + numIndices` Π binders then a `Sort`, on the DECLARED type (task #193: `numIndices` alone is NOT this conjunct — a former declared at a definition that unfolds to a telescope, `inductive … : Presieve X`, has indices and no syntactic telescope; the structure recogniser rejects it, and since task #195 the SUM recogniser reads it through `whnf` — so the pin is the structure arm's only) |
| large: `cvR.levelParams = elim :: lps`, `elim ∉ lps`; else small: `cvR.levelParams == lps` | the same, on `rec.levelParams` |
| `directShape` (constructor result `T p⃗`; recursor motive/minor/major domains and `motive t` result) | *not mirrored* — see below |
| `directNonRec env` (every constructor binder domain resolves in the pre-block environment) | `!type.isRec ∧ type.numNested == 0` |

**The two conjuncts that are not mirrored** are `directShape` and the rule's
right-hand side: both pin the block against *the shape Lean's kernel generates*
for a single-member, index-free, one-constructor inductive
(`Lean4Lean/Inductive/Add.lean:477-483` and `mkRecRules`, `Add.lean:441-447`).
Every record the predicate sees — the input's blocks and the blocks a model
splices alike — was produced by Lean's own `addDecl`/export path, so those
shapes hold by construction; they are in the recogniser because the *checker*
reads an untrusted stream, which this predicate does not.  Mirroring them would
mean a second, drifting implementation of a syntactic pin over a second `Expr`
type (`Lean.Expr` here, `ConLeche.Expr` there), so they are gated empirically
instead: `tests/native-audit.sh` (task #193) runs every fixture stream through
this binary and, reading the checker's own route trace, fails on any block left
`native` that the checker then declines — the predicate ⊆ recogniser direction.
(It used to be named `tests/native-agree.sh` here, a name that never existed on
disk; task #187's Mathlib row found the very gap the check is for.)

`directNonRec` is the one genuinely environment-dependent conjunct.
`!isRec ∧ numNested == 0` is what makes a constructor's binder domains free of
the block's own names; a domain naming some *other* constant that failed to
enter the environment would fail the modelled route just as hard (the model is
built from the same field types), so the direction is safe.
-/

open InductiveModels

/-- The reserved basis names of `ConLeche/Kernel/Basis/Names.lean`
(`ConLeche.reservedBasisNames`).  `directPartsCore?` rejects a block using one of
them — those are con-leche's pinned basis blocks, installed by the basis path, not
the direct one.  (`PSigma'` is deliberately *not* here: it is the
preprocessor's basis and con-leche installs it through the direct path, task
#175 W6.  `Quot` never reaches the predicate as an `induct` record.) -/
def conlecheReservedBasisNames : List Lean.Name :=
  [`Eq, `Eq.refl, `Eq.rec,
   `Nat, `Nat.zero, `Nat.succ, `Nat.rec,
   `PUnit, `PUnit.unit, `PUnit.rec,
   `Empty, `Empty.rec,
   `Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound]

/-! **`False` is reserved by the checker but deliberately NOT listed above**
(task #181).  `False`/`False.rec` joined `ConLeche.reservedBasisNames` when
the block was pinned (`ConLeche/Kernel/Basis/False.lean`), so the direct sum
recogniser rejects the name — but the frontend matches an incoming block
against the pinned basis blocks *before* any recogniser runs
(`ConLeche/Frontend/ExportC.lean`), and the raw `False` block IS the pin.  A
native `False` therefore never reaches the recogniser: the pin installs
it, and leaving it native keeps the preprocessor's `False._model` artifacts
— dead weight the pin would ignore, exactly as `Empty._model`'s are —
out of the stream.  (`Empty` stays listed for the historical reason that
it was reserved before the direct routes existed; its artifacts are
inert.)  The mirror doctrine of the module header is unaffected: the
predicate must be no looser than *the checker*, and the checker's first
route for this block is the pin. -/

/-- **The type former's DECLARED type is a syntactic telescope**
(task #193): `numParams + numIndices` Π binders ending in a `Sort`.
This mirrors the STRUCTURE recogniser's `cvT.type.stripPis nP` ending
in `.sort` — a conjunct the predicate used to read off `numIndices`
alone, which is wrong for a former declared AT A DEFINITION that only
*unfolds* to a telescope: `inductive Presieve.ofArrows … : Presieve X`
(Mathlib; `Presieve X := ∀ ⦃Y⦄, Set (Y ⟶ X)`) has `numIndices = 2` from
the kernel's `whnf`, but its stored type ends in `Presieve C inst X`.
Since task #195 the SUM route reads such a type through the whnf loop
and takes it, so this pin applies to the structure arm only (no
structure of init-full or Mathlib is declared that way — the task #195
census — but the arm's recogniser is syntactic, so the mirror stays
exact).  Read with `Lean.Expr`'s binder structure only; no environment,
no unfolding. -/
def conlecheFormerTelescope (type : EIndType) : Bool :=
  go (type.numParams + type.numIndices) type.type
where
  go : Nat → Lean.Expr → Bool
    | 0, .sort _ => true
    | 0, _ => false
    | n + 1, .forallE _ _ body _ => go n body
    | _ + 1, _ => false

/-- THE DIRECT SUM CLASS (task #175 sum-types, indexed): any number of
constructors other than one, or an indexed family with any number of
constructors — `ConLeche.directSumPartsCore?`
(`ConLeche/Kernel/Direct/SumParts.lean`), mirrored conjunct for
conjunct; the one-constructor index-free class is the structure route
(`conlecheNative`'s first arm).  The recogniser's residual shape
(`directCtorResidOk`: the family at the parameters followed by
`numIndices` index expressions) and the rules' right-hand sides are the
two conjuncts argued rather than mirrored, as at the structure class. -/
def conlecheNativeSum (type : EIndType) (ctors : List ECtor) (rec : ERec) : Bool :=
  -- any number of constructors other than one, or an indexed family
  (ctors.length != 1 || type.numIndices != 0) &&
  -- the former's type: NOT pinned here (task #195).  The sum route's
  -- install reads the telescope through official's own whnf loop
  -- (`whnfTelescope`, `ConLeche/Kernel/Direct/SumInstall.lean`), so a former
  -- declared at a definition (`inductive … : Presieve X`) is in the
  -- class; that every Lean-produced record's type DOES whnf to
  -- `numParams + numIndices` binders and a sort is how Lean computed
  -- `numIndices` in the first place — an argued conjunct, like the
  -- shape pins below, gated by `tests/native-audit.sh` (which holds on
  -- all 23 such blocks of Mathlib, the task #195 census).  Task #193's
  -- `conlecheFormerTelescope` stays on the STRUCTURE arm, whose recogniser
  -- still reads the declared type syntactically.
  -- the member: non-recursive, non-nested, safe
  !type.isRec && type.numNested == 0 &&
    !type.isUnsafe && type.all == [type.name] &&
    type.ctors == ctors.map (·.name) &&
  -- every constructor: this member's, at its level parameters
  ctors.all (fun ctor => ctor.induct == type.name &&
    ctor.levelParams == type.levelParams &&
    ctor.numParams == type.numParams && !ctor.isUnsafe &&
    !conlecheReservedBasisNames.contains ctor.name) &&
  -- the recursor: `T.rec`, the family's indices, one motive, one
  -- minor and one rule per constructor in constructor order
  rec.name == type.name.str "rec" && rec.numIndices == type.numIndices &&
    rec.numMotives == 1 && rec.numMinors == ctors.length &&
    rec.numParams == type.numParams && !rec.isUnsafe &&
    rec.rules.length == ctors.length &&
    (List.range ctors.length).all (fun j =>
      match rec.rules[j]?, ctors[j]? with
      | some rule, some ctor => rule.ctor == ctor.name && rule.nfields == ctor.numFields
      | _, _ => false) &&
  -- the eliminator shape: LARGE (a fresh elimination level parameter in
  -- front of the block's own) or, failing that, SMALL (the block's own
  -- level parameters) — `directSumPartsCore?`'s `large?`/`else` order
  ((match rec.levelParams with
    | elim :: rest => rest == type.levelParams && !type.levelParams.contains elim
    | [] => false) ||
   rec.levelParams == type.levelParams) &&
  -- not one of con-leche's pinned basis blocks
  !conlecheReservedBasisNames.contains type.name &&
    !conlecheReservedBasisNames.contains rec.name

/-- The field kinds of a recursive block's constructor, mirroring
`ConLeche.recCtorKinds` (`ConLeche/Kernel/Direct/RecParts.lean`) on the
export's `Lean.Expr`: peel the parameters, then every field's domain is
ordinary (it does not mention the block) or the family at the
parameter variables followed by `nIdx` index expressions free of the
block, the field mentioned by nothing after it (`directUsedLater`:
no later domain, no index expression, not the residual); the
constructor's residual index expressions are free of the block.
Anything else — a non-positive occurrence, a nested
occurrence, an index expression through the block or an earlier
recursive field — is NOT native (the recogniser admits it only to
reject or to fall through to the modeled path, and leaving such a block
modeled changes no verdict the route could accept). -/
def conlecheFixFieldsOk (T : Lean.Name) (lps : List Lean.Name) (nP nIdx : Nat) :
    Lean.Expr → Nat → Nat → Bool
  | .forallE _ dom body _, k, i =>
    if k < nP then conlecheFixFieldsOk T lps nP nIdx body (k + 1) i
    else
      let noT := fun (e : Lean.Expr) => (e.find? fun e => e.isConstOf T).isNone
      -- the domain's own `∀`-telescope (empty at a finitary field, the
      -- `a⃗ : A⃗` of a reflexive one — task #202) and its body
      let rec peel : Lean.Expr → Nat → Nat × Lean.Expr
        | .forallE _ d b _, m => if noT d then peel b (m + 1) else (m, .forallE .anonymous d b .default)
        | e, m => (m, e)
      let (m, fam) := peel dom 0
      (noT dom ||
        (fam.getAppFn == Lean.mkConst T (lps.map .param) &&
          fam.getAppNumArgs == nP + nIdx &&
          fam.getAppArgs.toList.take nP ==
            ((List.range nP).map fun j => Lean.mkBVar (m + i + nP - 1 - j)) &&
          (fam.getAppArgs.toList.drop nP).all noT &&
          !body.hasLooseBVar 0)) &&
      conlecheFixFieldsOk T lps nP nIdx body (k + 1) (i + 1)
  | e, _, _ => (e.getAppArgs.toList.drop nP).all fun a => (a.find? fun e => e.isConstOf T).isNone

/-- THE DIRECT FIXED-POINT CLASS (task #188, reflexive fields at every
sort since task #202 Stage B): a RECURSIVE, non-nested block (indexed
or not) with any number of constructors whose recursive fields are
finitary or reflexive — `ConLeche.directFixParts?`
(`ConLeche/Kernel/Direct/RecParts.lean`), mirrored conjunct for conjunct;
the rule bodies (with the inductive hypotheses) are the conjunct
argued rather than mirrored, as at the other two classes. -/
def conlecheNativeFix (type : EIndType) (ctors : List ECtor) (rec : ERec) : Bool :=
  -- the member: recursive, non-nested, safe, its declared
  -- type `∀ p⃗ ı⃗, Sort u` syntactically (`directFixShape?` reads the
  -- telescope by `stripPis` as the structure arm does — task #193's
  -- conjunct, not task #195's whnf reading of the sum arm)
  type.isRec && type.numNested == 0 && conlecheFormerTelescope type &&
    !type.isUnsafe && type.all == [type.name] &&
    type.ctors == ctors.map (·.name) &&
  -- every constructor: this member's, at its level parameters, its
  -- fields ordinary or finitary recursive
  ctors.all (fun ctor => ctor.induct == type.name &&
    ctor.levelParams == type.levelParams &&
    ctor.numParams == type.numParams && !ctor.isUnsafe &&
    !conlecheReservedBasisNames.contains ctor.name &&
    -- a reflexive field at every sort (task #202, Stage B)
    conlecheFixFieldsOk type.name type.levelParams type.numParams type.numIndices ctor.type 0 0) &&
  -- the recursor: `T.rec`, the family's indices, one motive, one minor
  -- and one rule per constructor in constructor order
  rec.name == type.name.str "rec" && rec.numIndices == type.numIndices &&
    rec.numMotives == 1 && rec.numMinors == ctors.length &&
    rec.numParams == type.numParams && !rec.isUnsafe &&
    rec.rules.length == ctors.length &&
    (List.range ctors.length).all (fun j =>
      match rec.rules[j]?, ctors[j]? with
      | some rule, some ctor => rule.ctor == ctor.name && rule.nfields == ctor.numFields
      | _, _ => false) &&
  -- the eliminator shape: LARGE or SMALL, as at the sum class
  ((match rec.levelParams with
    | elim :: rest => rest == type.levelParams && !type.levelParams.contains elim
    | [] => false) ||
   rec.levelParams == type.levelParams) &&
  -- not one of con-leche's pinned basis blocks
  !conlecheReservedBasisNames.contains type.name &&
    !conlecheReservedBasisNames.contains rec.name
/-- Does the block name occur in the expression? -/
def conlecheMentions (ns : List Lean.Name) (e : Lean.Expr) : Bool :=
  (e.find? fun x => match x with
    | .const n _ => ns.contains n
    | _ => false).isSome

/-- THE IN-PROCESS CLASS (task #200): a mutual or nested block that
con-leche models in-process (`ConLeche/Frontend/InModel/*`): every member
non-reflexive, safe, at one parameter count and level-parameter list;
every constructor field either free of the block or a whole
member/container occurrence (no occurrence under a binder); the
recursor family with the block's motive/minor counts and one
eliminator shape.  The members' telescope agreement and the recursor
shapes are argued (Lean's own elaboration produces them); the
container shapes are not visible here (see `conlecheFieldsWhole`). -/
def conlecheNativeInModel (types : List EIndType) (ctors : List ECtor) (recs : List ERec) : Bool :=
  match types with
  | [] => false
  | t0 :: _ =>
    let names := types.map (·.name)
    let lps := t0.levelParams
    let nP := t0.numParams
    let nested := types.any (·.numNested > 0)
    (types.length > 1 || nested) &&
    types.all (fun t => !t.isReflexive &&
      !t.isUnsafe && t.levelParams == lps && t.numParams == nP &&
      t.all == names && conlecheFormerTelescope t) &&
    ctors.all (fun c => c.levelParams == lps && c.numParams == nP && !c.isUnsafe &&
      names.contains c.induct && !conlecheReservedBasisNames.contains c.name &&
      conlecheFieldsWhole names c.type 0 0) &&
    types.all (fun t => recs.any fun r => r.name == t.name.str "rec") &&
    recs.all (fun r => r.numMotives == recs.length &&
      r.numMinors == recs.foldl (fun acc r' => acc + r'.rules.length) 0 &&
      r.numParams == nP && !r.isUnsafe &&
      r.levelParams == (recs.headD default).levelParams &&
      ((match r.levelParams with
        | elim :: rest => rest == lps && !lps.contains elim
        | [] => false) || r.levelParams == lps)) &&
    !names.any conlecheReservedBasisNames.contains
where
  /-- every field domain is free of the block, or an application headed
  by a constant (not a `∀`: a reflexive/infinitary field) — a whole
  member or container occurrence, what the in-process rungs read as a
  member's or a mimic's carrier (`InModel.matchCarrier`; a dependent pin
  `I α (fun _ => T α)` is such a whole occurrence).  The container's own
  shape (plain, acyclic, its fields finitary) is not visible to the
  predicate: a block it leaves native and the generator then declines
  is the run's decline, naming the reason — the residual list. -/
  conlecheFieldsWhole (names : List Lean.Name) : Lean.Expr → Nat → Nat → Bool
    | .forallE _ dom body _, k, i =>
      (!conlecheMentions names dom ||
        (match dom.getAppFn with
         | .const _ _ => true
         | _ => false)) &&
      conlecheFieldsWhole names body (k + 1) (i + 1)
    | _, _, _ => true

/-- The blocks con-leche installs natively: the **direct simple-structure class**
of `ConLeche.directPartsCore?` (`ConLeche/Kernel/Direct/Parts.lean`) and the
**direct sum class** of `ConLeche.directSumPartsCore?` (`conlecheNativeSum`).
See this module's header for the conjunct-by-conjunct correspondence and for
the two conjuncts that are argued rather than mirrored.

Propositional structures are *in*: `directPartsCore?` recognises both
eliminator shapes — the large one (a fresh elimination level parameter in
front) and the small one Lean generates for a `Prop`-valued structure with a
non-`Prop` field (`motive : T p⃗ → Prop`, the block's own level parameters) —
and the install's squash regime handles the `Prop` case (task #175 W4c/O4). -/
def conlecheNative : NativeSupport := fun block =>
  match block with
  | .induct [type] [ctor] [rec] =>
    -- an indexed one-constructor family is the sum route's (task #175
    -- indexed: not a structure — official's `is_structure_like` needs
    -- no index); a recursive one is the fixed-point route's (task #188)
    (type.numIndices != 0 && conlecheNativeSum type [ctor] rec) ||
    conlecheNativeFix type [ctor] rec ||
    -- the member: index-free, non-recursive, non-nested, safe, one
    -- constructor, its declared type `∀ p⃗, Sort u` syntactically (#193)
    (type.numIndices == 0 && conlecheFormerTelescope type &&
      !type.isRec && type.numNested == 0 &&
      !type.isUnsafe && type.all == [type.name] && type.ctors == [ctor.name] &&
    -- the constructor: this member's, at its level parameters
    ctor.induct == type.name && ctor.levelParams == type.levelParams &&
      ctor.numParams == type.numParams && !ctor.isUnsafe &&
    -- the recursor: `T.rec`, no indices, one motive, one minor, one rule
    rec.name == type.name.str "rec" && rec.numIndices == 0 &&
      rec.numMotives == 1 && rec.numMinors == 1 &&
      rec.numParams == ctor.numParams && !rec.isUnsafe &&
      (match rec.rules with
       | [rule] => rule.ctor == ctor.name && rule.nfields == ctor.numFields
       | _ => false) &&
    -- the eliminator shape: LARGE (a fresh elimination level parameter in
    -- front of the block's own) or, failing that, SMALL (the block's own
    -- level parameters) — `directPartsCore?`'s `large?`/`else` order
    ((match rec.levelParams with
      | elim :: rest => rest == type.levelParams && !type.levelParams.contains elim
      | [] => false) ||
     rec.levelParams == type.levelParams) &&
    -- not one of con-leche's pinned basis blocks
    !conlecheReservedBasisNames.contains type.name &&
      !conlecheReservedBasisNames.contains ctor.name &&
      !conlecheReservedBasisNames.contains rec.name)
  | .induct [type] ctors [rec] => conlecheNativeSum type ctors rec || conlecheNativeFix type ctors rec
  -- the in-process class (task #200): mutual and nested blocks con-leche
  -- models itself (`ConLeche/Frontend/InModel/*`), their auxiliary families
  -- installed by the fixed-point route (task #188).  Since the flip
  -- (2026-09-07) this is the default: a block left native here that the
  -- generator then declines is the run's decline naming the reason —
  -- the exact residual class (DESIGN, task #200 closing section).
  | .induct types ctors recs => conlecheNativeInModel types ctors recs
  | _ => false

/-- `con-leche-preprocess [OPTIONS] IN.ndjson` — `lean-inductive-models` with
con-leche's native-support predicate.  Every option and exit code is the tool's
own (see its README); the only difference is that the blocks con-leche installs
directly (`ConLeche.directPartsCore?`/`directSumPartsCore?`/`directFixParts?`)
or models in-process (mutual and nested blocks) come out unmodelled. -/
def main (args : List String) : IO UInt32 :=
  InductiveModels.main args (native := conlecheNative)
