module

public import ConLeche.Frontend.Export
public import ConLeche.Cached.ExprNodes
/- The line reader the driver calls is the SPECIFICATION, `scanLineSpec`
(the naive recogniser); the compiler substitutes `scanLineFwd` on the
strength of `scanLineSpec_eq_scanLineFwd` (`@[csimp]`).  `Scan.Fast`
comes with it. -/
public import ConLeche.Frontend.Scan.Equiv

@[expose] public section

/-!
# Direct-to-`Expr` export parsing (task #171)

The cached pipeline parses the ndjson export
**directly into `Expr`** — no parse arena, no conversion.  The
export's `ie`-indices *are* the sharing: the format already
externalizes the DAG structure, so the parse keeps a stream-index-keyed table of
`Expr` values and a table hit is a shared node by reference.
Sharing is preserved structurally; the derived fields are computed
once per node by the smart constructors, which is also what makes
every parsed term well-formed **by construction** — the entry obligation
the capstone consumes (`ConLeche/Verify/Cached/ParseC.lean`).

**The stream is read as bytes** (task #256): the driver asks the
handle for 4 MiB at a time, carries the incomplete tail into the next
chunk, and hands every complete line to the byte recogniser of
`ConLeche/Frontend/Scan/Fast.lean`, which decodes it into a syntax
record (`LineRec`) still in stream indices.  `applyLine` below is the
semantic half: it resolves the indices against the tables, builds the
nodes through the smart constructors, and builds the declaration records.  There is one grammar in the tree and no
`Lean.Json` on the checking path.

**THE DECODER EMITS THE FILE'S RECORDS AND NOTHING ELSE** (task
#293).  Every inductive block parses to an `indDecl` — `Nat` and `Eq`
like any other — and every `#QUOT` record to a `quotDecl` carrying the
constant the file declares at the kind it declares it at.  No basis
recognition, no reserved-name logic, no prelude, no dedupe and no
reordering happen here: the checker's own prelude is prepended, the
pinned shapes are recognised and the pinned `Nat` operations' ground is
hoisted by `preparePrelude` (`ConLeche/Frontend/Prepare.lean`), between
this parse and the fold, and every VERDICT — a basis redefinition, a
quotient mismatch, a stream copy of a prelude record that differs — is
the fold's.
-/

namespace ConLeche.Frontend

open ConLeche


/-! ## The direct parse state -/

/-- The direct parse state: stream-index-keyed tables of *values*
(names and levels as trees, expressions as `Expr` — a table hit is a
shared node by reference) and the parsed declarations as
`Declaration`. -/
structure StateD where
  names : IdTable Name := IdTable.singleton .anonymous
  levels : IdTable Level := IdTable.singleton .zero
  exprs : IdTable Expr := {}
  decls : Array Declaration := #[]

/-- **One parsed record, appended** (task #293): the decoder keeps the
file's records in the file's order.  What used to sit here was the
prelude dedupe — a basis block the prelude held dropped by kind, a
record under a prelude name dropped when identical and DECLINING the
stream when different — and it is `preparePrelude`'s and the fold's
now (`ConLeche/Frontend/Prepare.lean`). -/
def pushDecl (st : StateD) (d : Declaration) : StateD :=
  { st with decls := st.decls.push d }

@[inline] def StateD.name (st : StateD) (i : Nat) : M Name :=
  match st.names.get? i with
  | some n => pure n
  | none => throw s!"undefined name index {i}"

@[inline] def StateD.level (st : StateD) (i : Nat) : M Level :=
  match st.levels.get? i with
  | some l => pure l
  | none => throw s!"undefined level index {i}"

@[inline] def StateD.expr (st : StateD) (i : Nat) : M Expr :=
  match st.exprs.get? i with
  | some e => pure e
  | none => throw s!"undefined expr index {i}"

/-! ## The lookup interface (task #329)

Every builder below reads the tables through three lookups and
nothing else: the entry builders `nameOf`/`levelOf`/`exprOf` and the
declaration builder `declOf`.  The serial parse hands them its own
tables (`StateD.lk`); the rounds parse (`ConLeche/Frontend/Rounds.lean`)
hands them a window's partly built tables, where a lookup may also
answer "not yet" — which is why the error type is a parameter.  A
builder's result depends on its lookups' answers alone, and that is
what the proofs of the rounds parse use
(`ConLeche/Verify/Frontend/Dense.lean`).

The frontend tree-size budget that used to sit on the declaration-level
expression lookup was **retired at task #215**: every consumer it
bounded is now either name-selected (the basis-pin match) or a
memoized DAG walk (`Expr.renameConsts`, `Expr.instantiate1`;
`@[csimp]` in `ConLeche/Kernel/ExprOps.lean`), and the adversarial
DAG-tower fixtures in `tests/e2e` are the standing gate in its place —
a limit told a user "no", a fixture tells *us* which walker
regressed. -/

/-- The three table lookups a builder reads through. -/
structure Lk (ε : Type) where
  name : Nat → Except ε Name
  level : Nat → Except ε Level
  expr : Nat → Except ε Expr

/-- The serial parse's lookups: the state's own tables. -/
@[inline] def StateD.lk (st : StateD) : Lk String := ⟨st.name, st.level, st.expr⟩

/-- The `pw` datum, over the name lookup. -/
@[inline] def pwOfF (nm : Nat → Except ε Name) (_lv : Nat → Except ε Level) (_ex : Nat → Except ε Expr) : PwRec → Except ε PropWhen
  | .never => pure .never
  | .ifAllZero ns => do pure (.ifAllZero (← ns.mapM nm))

/-- A name-table entry's value. -/
@[inline] def nameOfF (nm : Nat → Except ε Name) (_lv : Nat → Except ε Level) (_ex : Nat → Except ε Expr) (r : NameRec) : Except ε Name :=
  match r with
  | .str pre s => do pure (Name.str (← nm pre) s)
  | .num pre n => do pure (Name.num (← nm pre) n)

/-- A level-table entry's value. -/
@[inline] def levelOfF (nm : Nat → Except ε Name) (lv : Nat → Except ε Level) (_ex : Nat → Except ε Expr) (r : LevelRec) : Except ε Level :=
  match r with
  | .succ u => do pure (Level.succ (← lv u))
  | .max a b => do pure (Level.max (← lv a) (← lv b))
  | .imax a b => do pure (Level.imax (← lv a) (← lv b))
  | .param n => do pure (Level.param (← nm n))

/-- An expression-table entry's value: the `Expr` node built from the
children's values (the derived fields are the compiler's, task #172
B3a).

Binder names are display data the official kernel's equality and hash
ignore; ours are `.anonymous` on every parsed binder (task #203,
beside the `.default` annotation of task #142), so `==` is
α-equivalence downstream.  The `name` field is still required to be
present and well-formed (the recogniser reads it), it is just not
resolved. -/
@[inline] def exprOfF (nm : Nat → Except ε Name) (lv : Nat → Except ε Level) (ex : Nat → Except ε Expr) (r : ExprRec) : Except ε Expr :=
  match r with
  | .bvar k => pure (Expr.mkBvar k)
  | .sort u => do pure (Expr.mkSort (← lv u))
  | .const n us => do
    let nm ← nm n
    let ls ← us.mapM lv
    pure (Expr.mkConst nm ls)
  | .app f a => do pure (Expr.mkApp (← ex f) (← ex a))
  | .lam ty bd pw => do
    pure (Expr.mkLam (← ex ty) (← ex bd) ⟨← pwOfF nm lv ex pw⟩)
  | .forallE ty bd pw => do
    pure (Expr.mkForallE (← ex ty) (← ex bd) ⟨← pwOfF nm lv ex pw⟩)
  | .letE ty vl bd => do
    pure (Expr.mkLetE (← ex ty) (← ex vl) (← ex bd))
  | .proj tn ix s => do
    pure (Expr.mkProj (← nm tn) ix (← ex s))
  | .natVal n => pure (Expr.mkLit (.natVal n))
  | .strVal s => pure (Expr.mkLit (.strVal s))

/-- The builders over an `Lk` record. -/
@[inline] def pwOf (L : Lk ε) (r : PwRec) : Except ε PropWhen := pwOfF L.name L.level L.expr r
@[inline] def nameOf (L : Lk ε) (r : NameRec) : Except ε Name := nameOfF L.name L.level L.expr r
@[inline] def levelOf (L : Lk ε) (r : LevelRec) : Except ε Level := levelOfF L.name L.level L.expr r
@[inline] def exprOf (L : Lk ε) (r : ExprRec) : Except ε Expr := exprOfF L.name L.level L.expr r

/-! ## The rebinding test (task #290)

Every table entry is bound once: a line that binds an index a
previous line already bound is a parse error.  Before this the tables
let a later line overwrite an entry all the same (the entries are
resolved eagerly, so nothing already built could change).  What the
rule buys is the one property a theorem about the FILE needs of the
tables: the entry a line bound is the entry every later line reads,
whatever else the file holds
(`ConLeche/Verify/Frontend/ApplyLine.lean`). -/

/-- The rebinding error, named once. -/
def reboundError (what : String) (i : Nat) : String :=
  s!"{what} index {i} is already bound"

/-- The three tests, on a BORROWED state.  Written as separate
functions rather than inline so that the state is not deconstructed
before the test: an owned `st.exprs.bound i` at the top of a `do`
block made the compiler project and `inc` every field of the state
first (the reset/reuse pass moved the deconstruction ahead of the
test), which was a 17 % instruction increase on the parse phase;
against a borrowed parameter the state stays whole until the update
that consumes it, exactly as before. -/
@[noinline] def StateD.freshName (st : @& StateD) (i : Nat) : M Unit :=
  if st.names.bound i then throw (reboundError "name" i) else pure ()
@[noinline] def StateD.freshLevel (st : @& StateD) (i : Nat) : M Unit :=
  if st.levels.bound i then throw (reboundError "level" i) else pure ()
@[noinline] def StateD.freshExpr (st : @& StateD) (i : Nat) : M Unit :=
  if st.exprs.bound i then throw (reboundError "expression" i) else pure ()

/-! ## Table entries -/

/-- A name-table entry: the name value is built directly. -/
@[inline] def parseNameEntryD (st : StateD) (i : Nat) (r : @& NameRec) : M StateD := do
  let n ← nameOf st.lk r
  st.freshName i
  pure { st with names := st.names.insert i n }

/-- A level-table entry. -/
@[inline] def parseLevelEntryD (st : StateD) (i : Nat) (r : @& LevelRec) : M StateD := do
  st.freshLevel i
  let l ← levelOf st.lk r
  pure { st with levels := st.levels.insert i l }

/-- An expression-table entry (`exprOf`). -/
@[inline] def parseExprEntryD (st : StateD) (i : Nat) (r : @& ExprRec) : M StateD := do
  st.freshExpr i
  let e ← exprOf st.lk r
  pure { st with exprs := st.exprs.insert i e }

/-! ## Declaration records -/

/-- A declaration's common data; the type stays `Expr`. -/
@[specialize] def cvOfF (nm : Nat → M Name) (_lv : Nat → M Level) (ex : Nat → M Expr) (cv : CVRec) : M ConstantVal := do
  let name ← nm cv.name
  let ty ← ex cv.type
  pure { name := name
         levelParams := ← cv.levelParams.mapM nm
         type := ty }

/-- **The syntactic Π-telescope length of a declared type** (task
#271): official counts a constructor's binders by walking `is_pi`
without reducing (`check_constructors`), and the count past the
parameters is the `numFields` of the constructor it generates. -/
def indPiTeleLen : Expr → Nat
  | .forallE _ b _ => indPiTeleLen b + 1
  | _ => 0

/-- One recursor rule of an inductive record, resolved. -/
@[specialize] def ruleOfF (nm : Nat → M Name) (_lv : Nat → M Level) (ex : Nat → M Expr) (ru : RuleRec) : M RecRule := do
  pure (RecRule.mk (← nm ru.ctor) ru.nfields 0 .inert
    (← ex ru.rhs) false false false)

/-- **An inductive record, validated** (tasks #217, #228, #271): the
half of the record's processing that reads the state and changes
nothing — the verdict, or the block's constructors in the block's own
order with the declared parameter count.  Split from `indBlockOf`
below at task #290 so that a proof about what the parse does to its
state need not look here at all. -/
@[specialize] def validateIndF (nm : Nat → M Name) (_lv : Nat → M Level) (ex : Nat → M Expr) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) : M (RecordVerdict ⊕ (List IndCtorRec × Nat)) := do
  -- TASK #217 (audit follow-up 6): an `unsafe inductive` is DECLINED,
  -- not an error.  The official kernel admits unsafe blocks (it skips
  -- positivity for them); we support no unsafe declaration at all, and
  -- unsafe axioms/opaques/definitions already decline positively.
  if tys.any (·.isUnsafe) then
    return .inl (.declined "unsafe inductive declaration")
  -- TASK #228 — THE DECLARED PARAMETER COUNT.  Official's replay
  -- hands `add_inductive` the `numParams` of ONE inductive record of
  -- the block (`Declaration.inductDecl lparams nparams types`,
  -- `Lean4Checker/Replay.lean`) and checks every former and every
  -- constructor against it; which record that is, is the name order
  -- of the replay's walk.  So the count is well defined for the
  -- block exactly when its type records AGREE on it — as every
  -- record a real export writes does, `add_inductive` storing one
  -- `m_nparams` in every member's `InductiveVal`.  A block whose
  -- records disagree has no declared count this checker could hold
  -- official to, and is positively declined here rather than checked
  -- against a count official might not have chosen.
  let nPs := tys.map (·.numParams)
  let nPd := nPs.head?.getD 0
  unless nPs.all (· == nPd) do
    return .inl (.declined "inductive block whose type records disagree on numParams")
  -- TASK #271 (issues #5 and #7) — THE BLOCK'S REDUNDANT FIELDS.
  -- Official's replay hands `add_inductive` the type formers, the
  -- constructors and the parameter count; the kernel then GENERATES
  -- the constructors and the recursors, and the replay compares each
  -- exported CONSTRUCTOR and RECURSOR record with the generated one
  -- structurally (`checkPostponedConstructors`,
  -- `checkPostponedRecursors`, `Lean4Checker/Replay.lean`) — a
  -- mismatch is "Invalid constructor" / "Invalid recursor", a
  -- REJECT.  An exported INDUCTIVE record is never compared with the
  -- generated `InductiveVal`, so its `numIndices`, `numNested`,
  -- `isRec`, `isReflexive` and `all` are not input official reads and
  -- are not checked here either (the `numParams` half official DOES
  -- read is task #228's, just above).  What is read of a type record
  -- is its `ctors` list: it groups the constructor records into the
  -- block, and it IS the block's constructor order (issue #5 — the
  -- `cidx` field is the redundant copy, not the other way round).
  -- These are consistency checks between the stream's own fields, so
  -- they live here, in the parse, and their verdict is `.invalid`:
  -- the fold never sees such a block.
  let tyNames ← tys.mapM fun t => nm t.cv.name
  let tyTypes ← tys.mapM fun t => ex t.cv.type
  let listed ← tys.mapM fun t => t.ctors.mapM nm
  let ctorNames ← cts.mapM fun c => nm c.cv.name
  let flat := listed.flatten
  unless flat.Nodup do
    return .inl (.invalid "duplicate constructor name in an inductive type's ctors")
  unless flat.length == cts.length do
    return .inl (.invalid s!"the inductive block lists {flat.length} constructors \
      and carries {cts.length} constructor records")
  let ctorIx : Std.HashMap Name Nat :=
    (ctorNames.foldl (fun (mi : Std.HashMap Name Nat × Nat) n =>
      (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1
  let ctsA := cts.toArray
  -- the constructors IN THE BLOCK'S OWN ORDER, `types[].ctors` in
  -- type order (issue #5): a record array in another order is the
  -- same block, and the recursor generated from it is the same one
  let mut ordered : Array IndCtorRec := #[]
  for tn in tyNames.zip listed do
    let (T, ns) := tn
    let mut j := 0
    for n in ns do
      let some k := ctorIx[n]? | return .inl (.invalid s!"No such constructor {n}")
      let some c := ctsA[k]? | return .inl (.invalid s!"No such constructor {n}")
      if let some ci := c.cidx then
        unless ci == j do
          return .inl (.invalid s!"constructor {n} declares cidx {ci}; it is \
            constructor {j} of {T}")
      if let some iw := c.induct then
        let iwn ← nm iw
        unless iwn == T do
          return .inl (.invalid s!"constructor {n} declares induct {iwn}; it is \
            a constructor of {T}")
      -- `numFields`: official counts the constructor's own Π binders
      -- without reducing (`check_constructors` walks `is_pi`) and
      -- stores the count past the parameters, so a record that
      -- declares another number is not the generated constructor.
      -- Before this, a count too LARGE declined at the field
      -- telescope (arena `ctor-num-fields`) and a count too small was
      -- caught later, by the constructor's result type, if at all.
      let cty ← ex c.cv.type
      unless nPd + c.numFields == indPiTeleLen cty do
        return .inl (.invalid s!"constructor {n} declares {c.numFields} fields at \
          {nPd} parameters; its type has {indPiTeleLen cty} binders")
      ordered := ordered.push c
      j := j + 1
  let cts := ordered.toList
  -- The recursor records: the counts and the K flag the GENERATED
  -- recursor carries.  `numParams + numMotives + numMinors` and the
  -- major-premise index are compared with the block at the install
  -- (the recursor stage), which leaves a compensating pair of lies
  -- open; the individual counts are here.
  --
  -- NOT at a NESTED block.  The kernel specialises a nested block
  -- into a mutual one with a mimic type per nested occurrence, and
  -- the recursors it generates — `T.rec`, `T.rec_1`, … — are the
  -- SPECIALISED block's: their motives and minor premises count the
  -- mimics too, so the declared block's own type and constructor
  -- counts are not what they carry (measured: `ind_nest_inf`'s
  -- `InfNest.rec` declares two motives at one declared type).
  -- `numNested` is a field of the type record, which official never
  -- compares; reading it here only ever WEAKENS these checks, never
  -- rejects on it.
  let nested := tys.any (·.numNested != 0)
  let nTypes := tys.length
  let nCtors := cts.length
  -- official's `is_K_target`: the block is a `Prop`, has ONE type
  -- with ONE constructor, and that constructor takes only the
  -- parameters.  At a former whose declared type is not a syntactic
  -- Π-telescope ending in a sort (task #195) the sort cannot be read
  -- here and the flag is left to the install.
  let kExpected? : Option Bool :=
    match tyTypes, listed, cts with
    | [ty], [[_]], [c] =>
      match ty.piResult with
      | .sort s => some (c.numFields == 0 && Level.isEquiv s .zero == some true)
      | _ => none
    | _, _, _ => some false
  for r in (if nested then [] else rcs) do
    let rn ← nm r.cv.name
    unless r.numParams == nPd do
      return .inl (.invalid s!"recursor {rn} declares {r.numParams} parameters; \
        the block declares {nPd}")
    unless r.numMotives == nTypes do
      return .inl (.invalid s!"recursor {rn} declares {r.numMotives} motives; \
        the block has {nTypes} inductive types")
    unless r.numMinors == nCtors do
      return .inl (.invalid s!"recursor {rn} declares {r.numMinors} minor premises; \
        the block has {nCtors} constructors")
    if let some kE := kExpected? then
      unless r.k == kE do
        return .inl (.invalid s!"recursor {rn} declares k := {r.k}; the generated \
          recursor of this block is{if kE then "" else " not"} K-like")
    -- `numIndices` of `T.rec` is what is left of `T`'s own telescope
    -- once the parameters are peeled; unreadable at a former declared
    -- at a definition, and then not checked
    if let .str T "rec" := rn then
      for tt in tyNames.zip tyTypes do
        if tt.1 == T then
          if let some n := tt.2.piSortTeleLen? then
            unless nPd + r.numIndices == n do
              return .inl (.invalid s!"recursor {rn} declares {r.numIndices} indices; \
                {T} has {n - nPd} at {nPd} parameters")
  return .inr (cts, nPd)

/-- **An inductive record, assembled**: the block's constants, as one
`indDecl`. -/
@[specialize] def indBlockOfF (nm : Nat → M Name) (lv : Nat → M Level) (ex : Nat → M Expr) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (nPd : Nat) : M Declaration := do
  let types ← tys.mapM fun t => do
    pure (ConstantInfo.indInfo (← cvOfF nm lv ex t.cv) {})
  let ctors ← cts.mapM fun c => do
    pure (ConstantInfo.ctorInfo (← cvOfF nm lv ex c.cv) c.numParams c.numFields)
  let recs ← rcs.mapM fun r => do
    let rules ← r.rules.mapM (ruleOfF nm lv ex)
    pure (ConstantInfo.recInfo (← cvOfF nm lv ex r.cv)
      (r.numParams + r.numMotives + r.numMinors + r.numIndices)
      (r.numParams + r.numMotives + r.numMinors) rules)
  let block := types ++ ctors ++ recs
  -- **EVERY BLOCK IS AN `indDecl`** (task #293): the basis-pin match
  -- that used to stand here — a name pre-filter (task #215) and then
  -- `canonEqList` against the five pinned blocks — is
  -- `preparePrelude`'s (`ConLeche/Frontend/Prepare.lean`), which
  -- retags a matching block to its `basisDecl` kind before the fold
  -- sees it.  A block under a pinned name that does NOT match keeps
  -- its `indDecl` form and is rejected by the fold's reserved-name
  -- check, exactly as before.
  return .indDecl block nPd

/-- The record's own semantics: the declaration kinds, producing
`Declaration` records (the state is `processLineCoreD`'s, below).
Every branch, guard and error string is the one the `Lean.Json` reader this replaced had (task #256); only the reads
changed, from key lookups in a DOM to fields of a syntax record. -/
@[specialize] def declOfF (nm : Nat → M Name) (lv : Nat → M Level) (ex : Nat → M Expr) (d : @& DeclRec) : M (Declaration ⊕ RecordVerdict) := do
  match d with
  | .ax cvr isUnsafe =>
    let cvp ← cvOfF nm lv ex cvr
    if isUnsafe then
      return .inr (.declined "unsafe axiom")
    -- **`Quot.sound` is the FOLD's** (task #293): the axiom record is
    -- forwarded like any other, and the fold compares it with the
    -- pinned soundness axiom (`checkDecl`'s `.axiomDecl` arm) — the
    -- decline on a mismatch was the parser's and is not any more.
    return .inl (.axiomDecl cvp)
  | .defn cvr value hints safety =>
    let cvp ← cvOfF nm lv ex cvr
    match safety with
    | "safe" =>
      let vl ← ex value
      let h : ReducibilityHint := match hints with
        | .«abbrev» => .«abbrev»
        | .«opaque» => .«opaque»
        | .regular n => .regular n
      return .inl (.defnDecl cvp vl h)
    | s => return .inr (.declined s!"definition with safety '{s}'")
  | .thm cvr value =>
    let cvp ← cvOfF nm lv ex cvr
    let vl ← ex value
    return .inl (.thmDecl cvp vl)
  | .opaq cvr value isUnsafe =>
    let cvp ← cvOfF nm lv ex cvr
    if isUnsafe then
      return .inr (.declined "unsafe opaque declaration")
    let vl ← ex value
    return .inl (.opaqueDecl cvp vl)
  | .quot cvr kind =>
    -- **ONE RECORD PER `#QUOT` LINE** (task #293): the file declares
    -- the quotient package as four records, and the decoder emits four
    -- — the constant as the file declares it, at the kind the file
    -- declares it at.  The comparison with the pinned block
    -- (`preparePrelude`, which retags a matching record to
    -- `basisDecl .quotK`) and the decline on a mismatch (the fold's
    -- `.quotDecl` arm) are not the parser's any more.
    let cv ← cvOfF nm lv ex cvr
    let qk ← match kind with
      | "type" => pure QuotKind.type
      | "ctor" => pure QuotKind.ctor
      | "lift" => pure QuotKind.lift
      | "ind" => pure QuotKind.ind
      | k => throw s!"unknown quotient kind '{k}'"
    return .inl (.quotDecl qk cv)
  | .ind tys cts rcs =>
    match ← validateIndF nm lv ex tys cts rcs with
    | .inl v => pure (.inr v)
    | .inr (cts, nPd) => return .inl (← indBlockOfF nm lv ex tys cts rcs nPd)

/-- The declaration builder over an `Lk` record. -/
@[inline] def declOf (L : Lk String) (d : DeclRec) : M (Declaration ⊕ RecordVerdict) :=
  declOfF L.name L.level L.expr d

/-- A declaration record applied to the state: its record pushed, or its
verdict. -/
def processLineCoreD (st : StateD) (d : @& DeclRec) : M (StateD ⊕ RecordVerdict) := do
  match ← declOf st.lk d with
  | .inl x => pure (.inl (pushDecl st x))
  | .inr v => pure (.inr v)

/-- A declaration record.  **`sorryAx` is the FOLD's** (user ruling):
the parse forwards every declaration record, the `sorryAx` axiom record
included — the fold checks its type, installs nothing for it, and
declines at the first record that USES the name
(`ConLeche/Kernel/Checker.lean`'s `.axiomDecl` arm, `unknownConstError`
and `unresolvedConstsError`); the parser owns no semantic decision. -/
def applyDeclD (st : StateD) (d : @& DeclRec) : M (StateD ⊕ RecordVerdict) :=
  processLineCoreD st d

/-- **The semantic layer**: one scanned line applied to the parse
state, reading the fields of the syntax record the byte recogniser
produced (`ConLeche/Frontend/Scan/Fast.lean`, task #256). -/
@[inline] def applyLine (st : StateD) (r : @& LineRec) : M (StateD ⊕ RecordVerdict) :=
  match r with
  | .expr i e => do pure (.inl (← parseExprEntryD st i e))
  | .name i n => do pure (.inl (← parseNameEntryD st i n))
  | .level i l => do pure (.inl (← parseLevelEntryD st i l))
  | .decl d => applyDeclD st d
  | .header => pure (.inl st)
  | .blank => pure (.inl st)

/-! ## The line feed and the drivers -/

/-- The direct parse result: the declarations over `Expr`.  No arena. -/
structure ParseResultD where
  /-- the FILE's declaration records, in the file's order (task #293:
  the prelude, the dedupe and the ground hoist are `preparePrelude`'s) -/
  decls : Array Declaration

/-- The initial parse state (task #293: there is no prelude here any
more — the parse starts from the file's first record). -/
def StateD.init : StateD := {}

/-- The result: the file's records, in the file's order. -/
def ParseResultD.ofState (st : StateD) : ParseResultD :=
  ⟨st.decls⟩

/-- Scan and apply the LAST line of a stream — the one no newline
ends.  A syntactic failure is reported at its offset in the line. -/
def applyFinalLine (st : StateD) (b : @& ByteArray) (i : USize)
    (lineNo : Nat) : Except (CheckError × Nat) StateD :=
  match scanLineSpec b i with
  | .err e => .error (.internal (ScanErr.render ⟨e.offset - i.toNat, e.what⟩), lineNo)
  | .ok r _ =>
    match applyLine st r with
    | .error msg => .error (.internal msg, lineNo)
    | .ok (.inr v) => .error (v.toError, lineNo)
    | .ok (.inl st) => .ok st

/-- Every COMPLETE line of the chunk from `i`, applied in order: the
state, the line count, and where the incomplete tail begins (the
caller carries it into the next chunk).  A line the chunk cut in half
is told from a malformed one by whether the rest of the chunk holds a
newline at all — which is why a scan failure is not immediately an
error.  The loop's advance is the line, and the line reader never
returns a position at or before its own start, so the remaining byte
count is the termination measure.  The reader is `scanLineSpec`, the
naive reference; what runs is `scanLineFwd`, by the kernel-checked
equality the compiler substitutes (`ConLeche/Frontend/Scan/Equiv.lean`). -/
def feedChunk (st : StateD) (b : @& ByteArray) (i : USize) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × Nat × USize) :=
  if _h : i < b.usize then
    match scanLineSpec b i with
    | .err e =>
      if newlineFrom b i then
        .error (.internal (ScanErr.render ⟨e.offset - i.toNat, e.what⟩), lineNo + 1)
      else .ok (st, lineNo, i)
    | .ok r j =>
      -- `0` is the recogniser's "the buffer ended before a newline
      -- did": these bytes are an incomplete tail, not a line.  (A
      -- `USize` numeral must be COMPARED, not matched: a literal
      -- pattern of a machine-word type does not fire.)
      if j == 0 then .ok (st, lineNo, i)
      else
        match applyLine st r with
        | .error msg => .error (.internal msg, lineNo + 1)
        | .ok (.inr v) => .error (v.toError, lineNo + 1)
        | .ok (.inl st) =>
          if _hj : i < j then feedChunk st b j (lineNo + 1)
          else .error (.internal "the line scanner made no progress", lineNo + 1)
  else .ok (st, lineNo, i)
termination_by b.size - i.toNat
decreasing_by
  exact Nat.sub_lt_sub_left (usizeInBounds b i _h) (USize.lt_iff_toNat_lt.mp _hj)

/-- How many bytes the streaming driver asks for at a time. -/
def chunkSize : USize := 4 * 1024 * 1024

/-- **The size guard** (task #290).  The byte reader addresses its
buffer by machine word, so an input of `USize.size` bytes or more is
refused before any of it is read — the wholesale parse at its length,
the streaming parse when the bytes read so far would reach it.  No
real input comes near, and the guard discharges the size hypothesis
of the file theorem (`ConLeche/Verify/Frontend/Lines.lean`,
`parseBytes_eq_parseLines`) at every parse that returns a result. -/
def sizeError : CheckError × Nat :=
  (.notImplemented s!"an input of {USize.size} bytes or more", 0)

/-- **Wholesale direct parse of a byte buffer**: the whole input fed
at once, then the last line.  The specification the streaming parse is
proved equal to (`parseChunks_ok_parseBytes`,
`ConLeche/Verify/Frontend/Chunks.lean`). -/
def parseBytes (b : ByteArray) :
    Except (CheckError × Nat) ParseResultD := do
  if b.size ≥ USize.size then throw sizeError
  let (st, lineNo, tail) ← feedChunk .init b 0 0
  if tail < b.usize then
    let st ← applyFinalLine st b tail (lineNo + 1)
    return .ofState st
  else
    return .ofState st

/-- Wholesale direct parse of a string (the built-in prelude, tests
and small inputs): `parseBytes` of its UTF-8. -/
def parseExportD (contents : String) :
    Except (CheckError × Nat) ParseResultD :=
  parseBytes contents.toUTF8

/-- **One chunk of the stream, applied** (task #290): the carried
incomplete tail is put in front of the new bytes, every complete line
of the buffer is fed, and the new incomplete tail is cut off for the
next chunk; `total` counts the bytes read before this chunk, for the
size guard.  This is the step the streaming reader takes
(`parseExportHandleP`, `ConLeche/Frontend/Pipeline.lean`, as
`chunkStepS` with the chunk's scan handed in), pure, so that
`parseChunks` below — the same step folded over a list of chunks — is
exactly what the binary
computes and can be compared with the wholesale parse
(`parseChunks_eq_parseBytes`, `ConLeche/Verify/Frontend/Chunks.lean`). -/
def chunkStep (st : StateD) (carry : ByteArray) (lineNo total : Nat) (buf0 : ByteArray) :
    Except (CheckError × Nat) (StateD × ByteArray × Nat × Nat) :=
  if total + buf0.size ≥ USize.size then .error sizeError
  else
    let buf := if carry.isEmpty then buf0 else carry ++ buf0
    match feedChunk st buf 0 lineNo with
    | .error e => .error e
    | .ok (st, lineNo, tail) =>
      .ok (st, buf.extract tail.toNat buf.size, lineNo, total + buf0.size)

/-- The end of the stream: the carried tail, if any, is its last line. -/
def chunkFinish (st : StateD) (carry : ByteArray) (lineNo : Nat) :
    Except (CheckError × Nat) ParseResultD :=
  if carry.isEmpty then .ok (.ofState st)
  else
    match applyFinalLine st carry 0 (lineNo + 1) with
    | .error e => .error e
    | .ok st => .ok (.ofState st)

/-- The bytes of a list of chunks, in order: what the chunks a handle
hands out add up to (task #290). -/
def concatBytes : List ByteArray → ByteArray
  | [] => .empty
  | c :: cs => c ++ concatBytes cs

/-- **The streaming parse, purely** (task #290): `chunkStep` folded
over a list of chunks, `chunkFinish` at its end — what
`parseExportHandleP` does with the chunks it cuts from its reads, minus
the reads.  The list is folded whole (task #294): an empty chunk
contributes nothing and the fold goes on, so the parse of a list of
chunks is the parse of their concatenation, however it was cut
(`parseChunks_ok_parseBytes`, `ConLeche/Verify/Frontend/Chunks.lean`).
The loop's end-of-input decision — an empty READ is the end of the
file — is the loop's own, not the step's. -/
def parseChunks (chunks : List ByteArray) :
    Except (CheckError × Nat) ParseResultD :=
  go .init .empty 0 0 chunks
where
  go (st : StateD) (carry : ByteArray) (lineNo total : Nat) :
      List ByteArray → Except (CheckError × Nat) ParseResultD
    | [] => chunkFinish st carry lineNo
    | c :: cs =>
      match chunkStep st carry lineNo total c with
      | .error e => .error e
      | .ok (st, carry, lineNo, total) => go st carry lineNo total cs

end ConLeche.Frontend
