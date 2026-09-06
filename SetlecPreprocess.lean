import InductiveModels.Main

/-!
# `setlec-preprocess` — the preprocessor, told what setlec handles itself (#178)

`lean-inductive-models` reduces an export's inductive declarations to a
five-member basis (`Eq`, `Nat`, `PUnit`, `PSigma'`, `Quot`) plus ordinary
definitions and theorems.  Since its `45d1346` it is a *library*
(`InductiveModels.main args (native := …)`), and the consumer says which
inductive blocks it handles itself: an accepted block is left unmodelled and
reported on a `native` line (`Dep: native — left to the consumer`), outside the
decline count.

setlec is such a consumer.  Its **direct simple-structure path**
(`Setlec/Kernel/Direct/Parts.lean`, task #175 W4c) installs a non-recursive,
single-constructor, index-free inductive block *from the reference checks
alone* — no `_model` artifact is read, and since the W4c priority gate the
artifacts of such a block are dead weight in the stream: recognition wins
whether or not a model is present.  This executable is the checker's own
`main` for the preprocessor, telling it not to generate that dead weight.

## THE PREDICATE AND THE RECOGNISER

`setlecNative` below must accept **only** blocks `Setlec.directPartsCore?`
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
| `reservedBasisNames.contains {T, C, T.rec} == false` | `setlecReservedBasisNames` (copied from `Setlec/Kernel/Basis/Names.lean`) |
| `mI == nP + 2 ∧ rP == nP + 2` (with `mI = rnP+rnM+rnm+rnI`, `rP = rnP+rnM+rnm`, from `Setlec/Frontend/ExportC.lean`) | `rec.numIndices == 0 ∧ rec.numMotives == 1 ∧ rec.numMinors == 1 ∧ rec.numParams == ctor.numParams` |
| `rule.ctor == C ∧ rule.nfields == nF` | the same, on `ERecRule` |
| `rule.rhs.stripLams (nP+2+nF)` is `directRuleBody nF` | *not mirrored* — see below |
| `cvT.type.stripPis nP` ends in `.sort` | `type.numIndices == 0` (an index-free member's type former *is* `∀ p⃗, Sort u`) |
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
type (`Lean.Expr` here, `Setlec.Expr` there), so they are gated empirically
instead: `tests/native-agree.sh` runs every fixture stream through this binary
and fails on any block left `native` that the checker then declines.

`directNonRec` is the one genuinely environment-dependent conjunct.
`!isRec ∧ numNested == 0` is what makes a constructor's binder domains free of
the block's own names; a domain naming some *other* constant that failed to
enter the environment would fail the modelled route just as hard (the model is
built from the same field types), so the direction is safe.
-/

open InductiveModels

/-- The reserved basis names of `Setlec/Kernel/Basis/Names.lean`
(`Setlec.reservedBasisNames`).  `directPartsCore?` rejects a block using one of
them — those are setlec's pinned basis blocks, installed by the basis path, not
the direct one.  (`PSigma'` is deliberately *not* here: it is the
preprocessor's basis and setlec installs it through the direct path, task
#175 W6.  `Quot` never reaches the predicate as an `induct` record.) -/
def setlecReservedBasisNames : List Lean.Name :=
  [`Eq, `Eq.refl, `Eq.rec,
   `Nat, `Nat.zero, `Nat.succ, `Nat.rec,
   `PUnit, `PUnit.unit, `PUnit.rec,
   `Empty, `Empty.rec,
   `Quot, `Quot.mk, `Quot.lift, `Quot.ind, `Quot.sound]

/-- THE DIRECT SUM CLASS (task #175 sum-types, indexed): any number of
constructors other than one, or an indexed family with any number of
constructors — `Setlec.directSumPartsCore?`
(`Setlec/Kernel/Direct/SumParts.lean`), mirrored conjunct for
conjunct; the one-constructor index-free class is the structure route
(`setlecNative`'s first arm).  The recogniser's residual shape
(`directCtorResidOk`: the family at the parameters followed by
`numIndices` index expressions) and the rules' right-hand sides are the
two conjuncts argued rather than mirrored, as at the structure class. -/
def setlecNativeSum (type : EIndType) (ctors : List ECtor) (rec : ERec) : Bool :=
  -- any number of constructors other than one, or an indexed family
  (ctors.length != 1 || type.numIndices != 0) &&
  -- the member: non-recursive, non-nested, safe
  !type.isRec && type.numNested == 0 &&
    !type.isUnsafe && type.all == [type.name] &&
    type.ctors == ctors.map (·.name) &&
  -- every constructor: this member's, at its level parameters
  ctors.all (fun ctor => ctor.induct == type.name &&
    ctor.levelParams == type.levelParams &&
    ctor.numParams == type.numParams && !ctor.isUnsafe &&
    !setlecReservedBasisNames.contains ctor.name) &&
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
  -- not one of setlec's pinned basis blocks
  !setlecReservedBasisNames.contains type.name &&
    !setlecReservedBasisNames.contains rec.name

/-- The blocks setlec installs natively: the **direct simple-structure class**
of `Setlec.directPartsCore?` (`Setlec/Kernel/Direct/Parts.lean`) and the
**direct sum class** of `Setlec.directSumPartsCore?` (`setlecNativeSum`).
See this module's header for the conjunct-by-conjunct correspondence and for
the two conjuncts that are argued rather than mirrored.

Propositional structures are *in*: `directPartsCore?` recognises both
eliminator shapes — the large one (a fresh elimination level parameter in
front) and the small one Lean generates for a `Prop`-valued structure with a
non-`Prop` field (`motive : T p⃗ → Prop`, the block's own level parameters) —
and the install's squash regime handles the `Prop` case (task #175 W4c/O4). -/
def setlecNative : NativeSupport := fun block =>
  match block with
  | .induct [type] [ctor] [rec] =>
    -- an indexed one-constructor family is the sum route's (task #175
    -- indexed: not a structure — official's `is_structure_like` needs
    -- no index)
    (type.numIndices != 0 && setlecNativeSum type [ctor] rec) ||
    -- the member: index-free, non-recursive, non-nested, safe, one constructor
    (type.numIndices == 0 && !type.isRec && type.numNested == 0 &&
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
    -- not one of setlec's pinned basis blocks
    !setlecReservedBasisNames.contains type.name &&
      !setlecReservedBasisNames.contains ctor.name &&
      !setlecReservedBasisNames.contains rec.name)
  | .induct [type] ctors [rec] => setlecNativeSum type ctors rec
  | _ => false

/-- `setlec-preprocess [OPTIONS] IN.ndjson` — `lean-inductive-models` with
setlec's native-support predicate.  Every option and exit code is the tool's
own (see its README); the only difference is that the blocks
`Setlec.directPartsCore?`/`Setlec.directSumPartsCore?` install directly come
out unmodelled. -/
def main (args : List String) : IO UInt32 :=
  InductiveModels.main args (native := setlecNative)
