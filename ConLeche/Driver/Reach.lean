module

public import ConLeche.Frontend.Olean
public import ConLeche.Modular
import ConLeche.Cached.Needs
import ConLeche.Cached.ParsedC
import ConLeche.Verify.Cached.DeclNames

@[expose] public section

/-!
# A worker's context: the reach of a module, its completion, the capture check

Phase 4 and 6 of a worker at module `M` (DESIGN #460 §3): the context `M`'s own records are
checked against, as a list of records, and its validation.

* **The reach** (`reachGo`): a plain worklist over names, from the names `M`'s own records
  read (`roots`).  A name the name index holds is read at its first copy, in the loaded
  part its module is loaded at, and becomes its **presented record** (`readRecord`): a
  definition the part holds with its value (exposed, or under `import all`) with it, every
  other definition, theorem and opaque constant as the axiom of its statement (the
  **opaque cut**: an imported theorem's value and a hidden definition's are never read),
  an axiom and a quotient constant as they are, an inductive group whole (`groupAt`,
  `groupRecord`), always read from its home's private part, so that it is its home's own
  record: an exported part lists a group's recursors sorted by name and need not hold them
  all.  A compiler-trust name is presented as its statement only where its home declares an
  opaque constant or an axiom there (`stmtRecord`).  What the record reads (`recordReads`)
  is pushed.
* **The completion of the exports, on demand.**  A record of home `h` means by a name `y` it
  reads the copy `h`'s export holds: `h`'s own, or the copy of a module of `h`'s public-import
  closure whose exported part holds `y`.  A name neither holds is **dangling** in `h`'s export,
  and is completed where the export was made: located in `h`'s view (`viewOf`: `h`'s own private
  part first, then the parts `h`'s header fixpoint loads, the first copy found; never by a name's
  `_private` spelling) and read from its module's private part as its statement (a group
  whole); its reads are dangling or not relative to the module it was read from, in turn.  A
  name located nowhere is malformed input (exit 1).  Completion is done for the names the
  context's records read and for every copy of every clashing name the context stores, and no
  other: a completed copy joins the loaded ones, and where two copies meet they must agree.
* **The capture check** (`captureOne`), for every record of home `h` and every name `y` it
  reads: the read passes when the context's copy of `y` is `h`'s own, or comes from a module
  of `h`'s public-import closure that exports it: the copy `h`'s export holds.  Otherwise `y`
  is located in `h`'s view, which on Lean's output means a completed name or a clashing copy,
  and the two copies must agree (`agreeCheck`, the specification's `Agree`): one module, or
  both proofs of one statement whose names agree.  Else the module is rejected ("name
  capture").  A context record reading one of `M`'s own names is rejected so too.
* **The names a record stores** (`storedNamesOk`): a group read with one of its names stores
  all of them; each must have no importer copy or one of the group's home, and none located
  elsewhere, else the module is rejected; one with no copy is located at the home's private
  part, so that a later read compares with it.
* **A copy's statement** at a proof pair, and every copy of a clashing name the context stores
  (`clashPartners`): every name the statement reads is capture-checked as a read of the copy's
  module (`ReachCache.partners`, after the worklist has read every record, so that each such
  name is the context's: the context's copy of the name has that statement), so that every
  copy reads its statement as the context does.
* **Proofs by inference** (`proofStatus`, ruling 3 of #460; axioms by #444's): a copy
  is a proof if it is a theorem, or (an exported axiom) its home's private part declares a
  theorem there, or it is a definition, opaque constant or axiom (exported or not, at its
  home) whose type the kernel infers to be a proposition over the part of the context below
  its name (`typeIsPropC`, `inferFlags`, after the context is built and validated).  The inference accepts every well-typed type
  Lean's `isPropCheap` accepts, so every pair Lean's merge identifies agrees.  The copies of
  every name two loaded modules hold (`WorkerReads.clashes`) must be proofs of one statement
  (`clashAgree`, Lean's merge).  Copies of one statement of which one is a theorem need no
  inference (task #506): a theorem's type is a proposition, and the copies' statement is one,
  its names read alike.  Only where no copy is a theorem is the statement inferred.  Every
  clashing name is reached, so that its statement's names are in the context and every copy's
  statement is capture-checked (task #618): Lean's merge compares the copies' statements as
  expressions, which a stale or hand-made build can make mean two things.
* **What a record reads** (`recordReads`): the names its constants' laws and its tables
  ask stored, `RecordScoped`'s (`ConLeche/Modular.lean`): every constant of a type, of a
  definition's value, of a recursor's rules and nested pins, a literal's and a
  projection's names, a type former's block members and η constructor, a table's
  structure, constructor and bodies, and `pinFootprint` at a pinned name; one memoized
  walk of each expression's DAG (`needsGo`).
* **The read order** (`readOrder`): the context's records sorted so that every record's reads
  are stored by itself or by an earlier record (a post-order walk of the reads, each record after
  the records storing what it reads; `ImportOk.ordered`, `readOrder_ordered`).  Records that read
  each other are malformed input (exit 1): Lean's output has none, every copy's statement reading
  only names its home declared or loaded before it.
* **The validation** (`validateCtx`): every context record validated as untrusted input
  (`recordOk`: closed, every loose bound variable bound, every level parameter declared, a
  nested rule's datum read off its recursor's type, a literal's name's shape, a table's
  bodies likewise); with the reach's closure, the context is `EnvWF`
  (`ConLeche/Verify/Driver/Reach.lean`, `reach_ok`).

**Termination** is by a fuel: every pushed name is new, out of the index plus the located
names, and each step pops one or checks the partners' reads recorded so far.
-/

namespace ConLeche.Cached

/-- **What a record reads**: its constants' laws' names and its tables', each expression's
DAG walked once (`RecordScoped`'s names, `recordReads_scoped`).  Compiled here, where the record's
constants and tables run as their cached twins (`Verify/Cached/DeclNames.lean`'s `csimp`). -/
def recordReads (d : Declaration) : Array Name :=
  ((declTables d).foldl NeedsSt.table ((declConstants d).foldl NeedsSt.const ({}, #[]))).2

end ConLeche.Cached

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

/-! ## The validation of a record -/

/-- **An expression's syntactic clauses**: no free variable, no loose bound variable at or
past `k`, every level parameter among `lps`. -/
def exprOk (lps : List Name) (k : Nat) (e : Expr) : Bool :=
  !e.hasFvar && e.looseBVarsBounded k && Expr.allLevelParamsDefinedC lps e

/-- **A nested rule's datum reads off its recursor's type** (`NestedRead`'s clauses, the
pins' resolution aside): the major's domain is the class's inductive at the rule's levels,
applied to the pins lifted past the index binders and then to the index variables. -/
def nestedOk (lps : List Name) (ty : Expr) (mI rP : Nat) (lvls : List Level)
    (pins : List Expr) : Bool :=
  decide (rP ≤ mI) && lvls.all (·.allParamsDefined lps) && pins.all (exprOk lps rP) &&
    match ty.stripPis mI with
    | some (_, .forallE dom _) =>
      match dom.getAppFn with
      | .const _ ls =>
        ls == lvls && dom.getAppArgs == pins.map (fun e => Expr.liftLooseBVarsC (mI - rP) e 0) ++
          (List.range (mI - rP)).map fun i => Expr.bvar (mI - rP - 1 - i)
      | _ => false
    | _ => false

/-- A recursor rule's clauses: its right-hand side, what it binds (`RuleWF`: the rule prefix
within the major's telescope, a λ per prefix argument and field), and its datum if nested. -/
def ruleOk (lps : List Name) (ty : Expr) (mI rP : Nat) (r : RecRule) : Bool :=
  exprOk lps 0 r.rhs && decide (rP ≤ mI) && (r.rhs.stripLams (rP + r.nfields)).isSome &&
    match r.fire with
    | .nested lvls pins => nestedOk lps ty mI rP lvls pins
    | _ => true

/-- **A constructor's stored family is the one its type concludes in** (`CtorWF`): its type's
result is headed by `induct`. -/
def ctorHeadOk (cv : ConstantVal) (induct : Name) : Bool :=
  match cv.type.piResult.getAppFn with
  | .const T _ => T == induct
  | _ => false

/-- **A constant's syntactic clauses** (`ConstWF`'s, the names' resolution aside, `CtorWF`'s
and `RuleWF`'s): its type; a definition's value; a recursor's rules; a constructor's
family. -/
def constOk : ConstantInfo → Bool
  | .defnInfo cv v _ => exprOk cv.levelParams 0 cv.type && exprOk cv.levelParams 0 v
  | .recInfo cv mI rP _ rules =>
    exprOk cv.levelParams 0 cv.type && rules.all (ruleOk cv.levelParams cv.type mI rP)
  | .ctorInfo cv _ _ induct => exprOk cv.levelParams 0 cv.type && ctorHeadOk cv induct
  | c => exprOk c.toConstantVal.levelParams 0 c.toConstantVal.type

/-- **A table's syntactic clauses** (`TableWF`'s, its structure's presence aside): one body
per field, each scoped at the parameters and the subject. -/
def tableOk (t : ProjTable) : Bool :=
  t.bodies.size == t.numFields && t.bodies.all (exprOk t.levelParams (t.numParams + 1))

/-- **A record validated**: every constant it installs and every table, with the shape a
literal's name asks. -/
def recordOk (d : Declaration) : Bool :=
  (declConstants d).all (fun c => constOk c && litShapeOk c) && (declTables d).all tableOk

/-! ## The reach's reads -/

deriving instance Hashable for OLeanLevel

/-- **A part of a view**: a module and a level. -/
structure PartKey where
  mod : Name
  level : OLeanLevel
  deriving BEq, Hashable, Inhabited

/-- **A copy of a name**: the part holding it and its name position there. -/
structure Spot where
  part : PartKey
  pos : NamePosition

/-- What the reach reads its records with, fixed for the run. -/
structure ReachEnv (μ : Type → Type) where
  /-- its reads of the files -/
  rd : OleanReads μ
  /-- the module whose context it is -/
  mod : Name
  wr : WorkerReads
  /-- the module's own names -/
  own : Std.HashSet Name
  /-- every copy of each name two loaded modules hold: the copy's module and its statement
  (`clashCopiesOf`) -/
  copies : Std.HashMap Name (Array (Name × ConstantVal)) := {}

/-- **The reach's caches**: what it has read of the files.  A part's memo is taken out of
`parts` while it is extended, so that it is changed at reference count 1. -/
structure ReachCache where
  /-- name tables of parts read so far (beside the index's) -/
  tables : Std.HashMap PartKey NamePositions := {}
  /-- name lookups of parts read from -/
  looks : Std.HashMap PartKey (Std.HashMap Name NamePosition) := {}
  /-- regions and memos of parts read from -/
  parts : Std.HashMap PartKey (Region × SM) := {}
  /-- per part, its recursors' locations by their block's first member -/
  recBlocks : Std.HashMap PartKey (Std.HashMap Name (Array Nat)) := {}
  /-- a home's view, for the searches -/
  views : Std.HashMap Name (Std.HashMap Name Spot) := {}
  /-- the completions: each name's located copy, at its module's private part -/
  located : Std.HashMap Name Spot := {}
  /-- the completed names, each with the home whose view located it -/
  completed : Array (Name × Name) := #[]
  /-- statements whose being a proposition decides an agreement, inferred over the part of the
  context below their name -/
  pending : Array (String × Name × ConstantVal) := #[]
  /-- the names of a proof pair's statement, each with the home that reads it as the pair's
  other copy (`agreeCheck`), to be capture-checked once the worklist is done -/
  partners : Array (Name × Name) := #[]
  /-- how many reads were looked for in their reader's view -/
  searches : Nat := 0

/-- **The parts of module `h`'s view**, in order: `h`'s own private part, then the parts its
header fixpoint `ld` loads, in its order. -/
def viewKeys (h : Name) (ld : HeaderLoads) : List PartKey :=
  ⟨h, .private⟩ :: (ld.order.zip ld.flags).toList.map fun (m, fl) => ⟨m, fl.level⟩

/-- **One part's names into a view**, the first copy of each name kept. -/
def viewStep (v : Std.HashMap Name Spot) (k : PartKey) (t : NamePositions) :
    Std.HashMap Name Spot :=
  t.consts.foldl (fun (v : Std.HashMap Name Spot) q =>
    if v.contains q.name then v else v.insert q.name ⟨k, q⟩) v

section
variable {μ : Type → Type} [CheckerIO μ]

/-! ## The parts -/

/-- **A part's name table**: the index's where the module is loaded at that level, else
read once. -/
def tableOf (env : ReachEnv μ) (c : ReachCache) (k : PartKey) :
    μ (ReachCache × Except CheckError NamePositions) := do
  match c.tables[k]? with
  | some t => pure (c, .ok t)
  | none =>
    let ld := env.wr.loads
    match ld.index[k.mod]? with
    | some i =>
      if ((ld.flags[i]?).getD default).level == k.level then
        match env.wr.index.parts[i]? with
        | some t => return (c, .ok t)
        | none => pure ()
      else pure ()
    | none => pure ()
    match ← env.rd.names (k.mod, k.level) with
    | .error e => pure (c, .error e)
    | .ok t => pure ({ c with tables := c.tables.insert k t }, .ok t)

/-- **A part's name lookup**, built once. -/
def lookOf (env : ReachEnv μ) (c : ReachCache) (k : PartKey) :
    μ (ReachCache × Except CheckError (Std.HashMap Name NamePosition)) := do
  match c.looks[k]? with
  | some l => pure (c, .ok l)
  | none =>
    match ← tableOf env c k with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok t) =>
      let l := t.consts.foldl (fun (l : Std.HashMap Name NamePosition) q => l.insert q.name q)
        (Std.HashMap.emptyWithCapacity t.consts.size)
      pure ({ c with looks := c.looks.insert k l }, .ok l)

/-- **A pure read of a part with its memo** (`entryWith`, `stmtWith`): the part's files read
once, its memo taken out while it is extended.  A read that fails leaves an empty memo: the
memo is consumed by `f`, no reference to it is kept for the failure branch (task #565). -/
def withPart {α : Type} (env : ReachEnv μ) (c : ReachCache) (k : PartKey)
    (f : Region → SM → Option (SM × α)) : μ (ReachCache × Except CheckError (α)) := do
  let got : Except CheckError (Region × SM) ← match c.parts[k]? with
    | some p => pure (.ok p)
    | none =>
      match ← env.rd.files k.mod k.level with
      | .error e => pure (.error e)
      | .ok fs =>
        match fs.viewRegion k.level with
        | some (r, _) => pure (.ok (r, ({} : SM)))
        | none => pure (.error (viewError k.mod fs k.level))
  match got with
  | .error e => pure (c, .error e)
  | .ok (r, st) =>
    let c := { c with parts := c.parts.erase k }
    match f r st with
    | some (st, a) => pure ({ c with parts := c.parts.insert k (r, st) }, .ok a)
    | none => pure ({ c with parts := c.parts.insert k (r, {}) }, .error (undecodable k.mod))

/-- **A part's region and name table off one read of its files** (task #508): for `groupAt`,
which reads both.  The region is kept with an empty memo; the table is the region's
(`namePositionsAt`, what `readNamePositions` reads), kept where none is yet.  Nothing is read
where the region is kept already. -/
def loadPart (env : ReachEnv μ) (c : ReachCache) (k : PartKey) :
    μ (ReachCache × Except CheckError Unit) := do
  if c.parts.contains k then return (c, .ok ())
  match ← env.rd.files k.mod k.level with
  | .error e => pure (c, .error e)
  | .ok fs =>
    match fs.viewRegion k.level with
    | none => pure (c, .error (viewError k.mod fs k.level))
    | some (r, a) =>
      let c := { c with parts := c.parts.insert k (r, {}) }
      if c.tables.contains k then return (c, .ok ())
      match namePositionsAt r a with
      | some t => pure ({ c with tables := c.tables.insert k t }, .ok ())
      | none => pure (c, .error (viewError k.mod fs k.level))

/-- Several constants with one memo (`entryWith`, in order). -/
def entriesWith (r : Region) (st : SM) : List Nat → Option (SM × List (CEntryF Name Expr))
  | [] => some (st, [])
  | l :: ls => do
    let (st, e) ← entryWith r st l
    let (st, es) ← entriesWith r st ls
    pure (st, e :: es)

/-- **A copy's statement and kind** (the kind's expressions left out). -/
def stmtAt (env : ReachEnv μ) (c : ReachCache) (s : Spot) :
    μ (ReachCache × Except CheckError (ConstantVal × CKindF Name Unit)) :=
  withPart env c s.part fun r st => stmtWith r st s.pos.loc

/-- **A copy in a module's private part**: itself, or the private part's constant of its
name. -/
def privSpot (env : ReachEnv μ) (c : ReachCache) (s : Spot) :
    μ (ReachCache × Except CheckError Spot) := do
  if s.part.level == .private then return (c, .ok s)
  let k : PartKey := ⟨s.part.mod, .private⟩
  match ← lookOf env c k with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok l) =>
    match l[s.pos.name]? with
    | some q => pure (c, .ok ⟨k, q⟩)
    | none => pure (c, .error (.invalid s!"module {s.part.mod}: its exported part holds \
        {s.pos.name}, its private part does not"))

/-! ## A home's view, and a search in it -/

/-- The names of some parts into a view, the first copy kept. -/
def viewAdd (env : ReachEnv μ) :
    ReachCache → Std.HashMap Name Spot → List PartKey →
      μ (ReachCache × Except CheckError (Std.HashMap Name Spot))
  | c, v, [] => pure (c, .ok v)
  | c, v, k :: ks => do
    match ← tableOf env c k with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok t) => viewAdd env c (viewStep v k t) ks

/-- **Module `h`'s view, by name**: `h`'s own private part, then the parts `h`'s header
fixpoint loads, in its order, the first copy of each name.  Built once per home. -/
def viewOf (env : ReachEnv μ) (c : ReachCache) (h : Name) :
    μ (ReachCache × Except CheckError (Std.HashMap Name Spot)) := do
  match c.views[h]? with
  | some v => pure (c, .ok v)
  | none =>
    match ← tableOf env c ⟨h, .private⟩ with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok own) =>
      match ← headerFixpoint env.rd.imports own.header.isModule own.header.imports with
      | .error e => pure (c, .error e)
      | .ok ld =>
        match ← viewAdd env c {} (viewKeys h ld) with
        | (c, .error e) => pure (c, .error e)
        | (c, .ok v) => pure ({ c with views := c.views.insert h v }, .ok v)

/-- **`y` located in `h`'s view.** -/
def locate (env : ReachEnv μ) (c : ReachCache) (h y : Name) :
    μ (ReachCache × Except CheckError (Option Spot)) := do
  match ← viewOf env c h with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok v) => pure ({ c with searches := c.searches + 1 }, .ok v[y]?)

/-- **The importer's copy of a loaded name**: its module's position in the load order and
the copy. -/
def importerSpot (env : ReachEnv μ) (y : Name) : Option (Nat × Spot) := do
  let cp ← env.wr.index.first[y]?
  let q ← env.wr.index.at cp
  let ld := env.wr.loads
  pure (cp.mod, ⟨⟨ld.nameAt cp.mod, ((ld.flags[cp.mod]?).getD default).level⟩, q⟩)

/-! ## Agreement -/

/-- **Is a copy a proof**: `yes`, `no`, or decided by inferring that its statement is a
proposition. -/
inductive ProofStatus where
  | yes
  | no
  | infer
  deriving BEq, Inhabited

/-- **A copy's proof flag** (ruling 3 of #460, and #444's: axioms as Lean merges them): a
theorem is a proof; a definition, opaque constant or axiom is one if its type is a proposition;
an exported axiom is what its home's private part declares there (a theorem a proof, a
definition, opaque constant or axiom by its type). -/
def proofStatus (env : ReachEnv μ) (c : ReachCache) (s : Spot) (k : CKindF Name Unit) :
    μ (ReachCache × Except CheckError ProofStatus) := do
  match k with
  | .thm .. => pure (c, .ok .yes)
  | .defn .. | .opaq .. => pure (c, .ok .infer)
  | .ax _ =>
    if s.part.level == .private then return (c, .ok .infer)
    match ← privSpot env c s with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok p) =>
      pure (c, .ok (match p.pos.tag with
        | 2 => .yes
        | 0 | 1 | 3 => .infer
        | _ => .no))
  | _ => pure (c, .ok .no)

/-- The names a statement reads, each paired with a home. -/
def partnerReads (h : Name) (ty : Expr) : Array (Name × Name) :=
  (needsGo {} #[] ty).2.map (h, ·)

/-- **Two copies of `y` agree**, the context's `s₁` and `s₂` of home `h`'s view: one module, or
both proofs of one statement (one of them a theorem, or else an inference recorded with the
statement), whose names `s₂`'s module reads as the context does (recorded in `partners`, each name as a read of that module).
The copy `h` reads is not unsafe or partial: `s₂`'s module holds it as a constant of its own
(a safe constant never reads an unsafe or partial one, in Lean's kernel as in the worker). -/
def agreeCheck (env : ReachEnv μ) (c : ReachCache) (h y : Name) (s₁ s₂ : Spot) :
    μ (ReachCache × Except CheckError Unit) := do
  if s₁.part.mod == s₂.part.mod then return (c, .ok ())
  let what := s!"name capture at {y}, read by module {h}"
  if s₂.pos.skipped then
    return (c, .error (.invalid s!"{what}: its copy of {y}, of module {s₂.part.mod}, is unsafe \
      or partial"))
  let bad : CheckError := .invalid s!"{what}: the copies of {y} of modules {s₁.part.mod} and \
    {s₂.part.mod} are not one constant (not two proofs of one statement)"
  match ← stmtAt env c s₁ with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok (cv₁, k₁)) =>
    match ← stmtAt env c s₂ with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok (cv₂, k₂)) =>
      if !(cv₁.levelParams == cv₂.levelParams && cv₁.type == cv₂.type) then
        return (c, .error bad)
      match ← proofStatus env c s₁ k₁ with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok p₁) =>
        match ← proofStatus env c s₂ k₂ with
        | (c, .error e) => pure (c, .error e)
        | (c, .ok p₂) =>
          if p₁ == .no || p₂ == .no then pure (c, .error bad)
          else
            let c := { c with partners := c.partners ++ partnerReads s₂.part.mod cv₂.type }
            if p₁ == .yes || p₂ == .yes then pure (c, .ok ())
            else pure ({ c with pending := c.pending.push (what, y, cv₁) }, .ok ())

/-- **The clash rule** (ruling 3 of #460, Lean's merge): the copies of every name two loaded
modules hold must be proofs of one statement, one of them a theorem or the statement inferred to
be a proposition.  Every clashing name is returned, to be reached (task #618): each copy's
statement is then capture-checked as its module reads it (`clashPartners`), so that the
statement means one thing at every copy, and a name two loaded modules hold has one meaning. -/
def clashAgree (env : ReachEnv μ) :
    ReachCache → List Clash → Array Name → μ (ReachCache × Except CheckError (Array Name))
  | c, [], acc => pure (c, .ok acc)
  | c, cl :: cls, acc => do
    let ld := env.wr.loads
    let spots := cl.copies.toList.filterMap fun (cp, cv, k) =>
      (env.wr.index.at cp).map fun q =>
        ((⟨⟨ld.nameAt cp.mod, ((ld.flags[cp.mod]?).getD default).level⟩, q⟩ : Spot), cv, k)
    match ← statuses c spots [] with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok ps) =>
      if ps.contains .no then
        pure (c, .error (.invalid s!"the loaded modules {spots.map (·.1.part.mod)} store \
          {cl.name}, not as one constant (not proofs of one statement)"))
      else if ps.contains .yes then clashAgree env c cls (acc.push cl.name)
      else
        match spots with
        | (_, cv, _) :: _ =>
          let why := s!"two loaded modules store {cl.name}"
          clashAgree env { c with pending := c.pending.push (why, cl.name, cv) }
            cls (acc.push cl.name)
        | [] => clashAgree env c cls acc
where
  statuses (c : ReachCache) : List (Spot × ConstantVal × CKindF Name Unit) → List ProofStatus →
      μ (ReachCache × Except CheckError (List ProofStatus))
    | [], acc => pure (c, .ok acc)
    | (s, _, k) :: rest, acc => do
      match ← proofStatus env c s k with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok p) => statuses c rest (p :: acc)

/-! ## The capture check -/

/-- **Is `y` in module `m`'s exported part** (`m` loaded at `level`). -/
def inExported (env : ReachEnv μ) (c : ReachCache) (m : Name) (level : OLeanLevel) (y : Name) :
    μ (ReachCache × Except CheckError Bool) := do
  if level == .exported then return (c, .ok true)
  match ← lookOf env c ⟨m, .exported⟩ with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok l) => pure (c, .ok (l.contains y))

/-- **The capture check of one read** `y` of a record of home `h`, and the completion of a
name the index lacks (see the module docstring). -/
def captureOne (env : ReachEnv μ) (c : ReachCache) (h y : Name) :
    μ (ReachCache × Except CheckError Unit) := do
  if env.own.contains y then
    return (c, .error (.invalid s!"name capture: module {h} reads {y}, which {env.mod} declares"))
  match importerSpot env y with
  | some (i, s₁) =>
    if s₁.part.mod == h then return (c, .ok ())
    let ld := env.wr.loads
    let pubHas : Bool := match ld.index[h]? with
      | some hi => ((env.wr.pub[hi]?).map (·.has i)).getD false
      | none => false
    let short ← if pubHas then inExported env c s₁.part.mod s₁.part.level y
      else pure (c, .ok false)
    match short with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok true) => pure (c, .ok ())
    | (c, .ok false) =>
      match ← locate env c h y with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok none) => pure (c, .error (.invalid s!"module {h} reads {y}, which its view \
          does not hold"))
      | (c, .ok (some s₂)) => agreeCheck env c h y s₁ s₂
  | none =>
    match c.located[y]? with
    | some s₁ =>
      if s₁.part.mod == h then return (c, .ok ())
      match ← locate env c h y with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok none) => pure (c, .error (.invalid s!"module {h} reads {y}, which its view \
          does not hold"))
      | (c, .ok (some s₂)) => agreeCheck env c h y s₁ s₂
    | none =>
      match ← locate env c h y with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok none) => pure (c, .error (.invalid s!"module {h} reads {y}, which no module \
          of its view holds"))
      | (c, .ok (some s)) =>
        match ← privSpot env c s with
        | (c, .error e) => pure (c, .error e)
        | (c, .ok p) =>
          pure ({ c with located := c.located.insert y p,
                         completed := c.completed.push (y, h) }, .ok ())

/-- **The names a record stores, against the importer's copies** (a group's members,
constructors and recursors, read with it from its home `h`'s private part): each has no importer
copy or one of `h`, and no located copy or one of `h`; one with neither is located at `h`'s private
part, so that a later read of it is compared with the context's copy like any read.  A copy of
another module is never one constant with a group's (no group member is a proof): a reject. -/
def storedNamesOk (env : ReachEnv μ) (c : ReachCache) (h : Name) :
    List Name → μ (ReachCache × Except CheckError Unit)
  | [] => pure (c, .ok ())
  | n :: ns => do
    let bad (k : Name) : CheckError := .invalid s!"a record read from module {h} stores {n}, \
      which the context reads from module {k}"
    match importerSpot env n with
    | some (_, s) =>
      if s.part.mod == h then storedNamesOk env c h ns else pure (c, .error (bad s.part.mod))
    | none =>
      match c.located[n]? with
      | some s =>
        if s.part.mod == h then storedNamesOk env c h ns else pure (c, .error (bad s.part.mod))
      | none =>
        match ← lookOf env c ⟨h, .private⟩ with
        | (c, .error e) => pure (c, .error e)
        | (c, .ok l) =>
          match l[n]? with
          | some q => storedNamesOk env { c with located := c.located.insert n ⟨⟨h, .private⟩, q⟩ } h ns
          | none => pure (c, .error (.invalid s!"module {h}: a record of its private part stores \
              {n}, which its private part does not hold"))

/-- **Every copy of a clashing name the context stores**, its statement's names each as a read of
the copy's module (`copies`): every copy a home might have chosen reads its statement as the
context does. -/
def clashPartners (env : ReachEnv μ) (ns : List Name) : Array (Name × Name) :=
  ns.foldl (fun acc n => match env.copies[n]? with
    | some cs => cs.foldl (fun acc (k, cv) => acc ++ partnerReads k cv.type) acc
    | none => acc) #[]

/-- The capture check of every read of a record. -/
def captureAll (env : ReachEnv μ) (h : Name) :
    ReachCache → List Name → μ (ReachCache × Except CheckError Unit)
  | c, [] => pure (c, .ok ())
  | c, y :: ys => do
    match ← captureOne env c h y with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok ()) => captureAll env h c ys

/-- **The partners' reads checked**: each name capture-checked as a read of its home. -/
def capturePairs (env : ReachEnv μ) :
    ReachCache → List (Name × Name) → μ (ReachCache × Except CheckError Unit)
  | c, [] => pure (c, .ok ())
  | c, (h, y) :: ps => do
    match ← captureOne env c h y with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok ()) => capturePairs env c ps

/-! ## A record read -/

/-- **A part's recursors' locations by their block's first member**, in the part's order:
`t` its name table, `r` its region. -/
def recBlocksAt (r : Region) (t : NamePositions) : Option (Std.HashMap Name (Array Nat)) :=
  let locs := (t.consts.filter (·.tag == 7)).toList.map (·.loc)
  (locs.mapM fun l => (kindNamesAt r l).map (l, ·)).map fun ks =>
    ks.foldl (fun (m : Std.HashMap Name (Array Nat)) (l, k) => match k with
      | .recur (a :: _) .. => m.alter a fun | none => some #[l] | some xs => some (xs.push l)
      | _ => m) {}

/-- A part's recursors' locations by their block's first member, read once. -/
def recBlocksOf (env : ReachEnv μ) (c : ReachCache) (k : PartKey) :
    μ (ReachCache × Except CheckError (Std.HashMap Name (Array Nat))) := do
  match c.recBlocks[k]? with
  | some m => pure (c, .ok m)
  | none =>
    match ← tableOf env c k with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok t) =>
      match ← withPart env c k (fun r st => (recBlocksAt r t).map (st, ·)) with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok m) => pure ({ c with recBlocks := c.recBlocks.insert k m }, .ok m)

/-- The constructors a group's types list. -/
def groupCtorNames (tys : List (CEntryF Name Expr)) : List Name :=
  tys.flatMap fun t => match t.kind with
    | .induct _ _ _ cs .. => cs
    | _ => []

/-- The locations of a group's recursors in a part, by its first member. -/
def groupRecLocs (rb : Std.HashMap Name (Array Nat)) (all : List Name) : List Nat :=
  ((all.head?.bind (rb[·]?)).getD #[]).toList

/-- A group's constants as a merge: `n`'s type, the types, the constructors and the
recursors of the block `all` among `rest`. -/
def groupMerged (t : CEntryF Name Expr) (tys rest : List (CEntryF Name Expr)) (all : List Name) :
    Merged :=
  let recs := rest.filter fun e => match e.kind with
    | .recur all' .. => all' == all
    | _ => true
  mergedOfList ((t :: tys ++ recs).map CEntry.ofF)

/-- **Type `n`'s group, read from one part**: `none` where the part lacks one of its
members or constructors.  The part's files are read once, for its table and its region
(`loadPart`). -/
def groupAt (env : ReachEnv μ) (c : ReachCache) (k : PartKey) (n : Name) :
    μ (ReachCache × Except CheckError (Option Declaration)) := do
  match ← loadPart env c k with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok ()) =>
  match ← lookOf env c k with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok look) =>
    match look[n]? with
    | none => pure (c, .ok none)
    | some q =>
      match ← withPart env c k fun r st => entryWith r st q.loc with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok t) =>
        match t.kind with
        | .induct _ _ all .. =>
          match all.mapM (look[·]?) with
          | none => pure (c, .ok none)
          | some mqs =>
            match ← withPart env c k fun r st => entriesWith r st (mqs.map (·.loc)) with
            | (c, .error e) => pure (c, .error e)
            | (c, .ok tys) =>
              match (groupCtorNames tys).mapM (look[·]?) with
              | none => pure (c, .ok none)
              | some cqs =>
                match ← recBlocksOf env c k with
                | (c, .error e) => pure (c, .error e)
                | (c, .ok rb) =>
                  match ← withPart env c k fun r st =>
                      entriesWith r st (cqs.map (·.loc) ++ groupRecLocs rb all) with
                  | (c, .error e) => pure (c, .error e)
                  | (c, .ok rest) =>
                    match groupRecord (groupMerged t tys rest all) n with
                    | .ok d => pure (c, .ok (some d))
                    | .error e => pure (c, .error e)
        | _ => pure (c, .error (.invalid s!"module {k.mod}: {n} is not an inductive type"))

/-- The type whose group presents a copy of `x` of kind `k`: `x` itself, a constructor's type, a
recursor's block's first member (`x` itself for a recursor of no block, which `groupAt` then
refuses); none for any other kind. -/
def groupOfKind (x : Name) : CKindF Name Unit → Option Name
  | .induct .. => some x
  | .ctor ind .. => some ind
  | .recur all .. => some (all.headD x)
  | _ => none

/-- **A copy presented as its statement** (`.axiomDecl cv`).  At a compiler-trust name
(`reduceOpNames`) only where its home's private part declares an opaque constant or an axiom
there: the statement of a theorem or definition at such a name presents nothing its home
declares (`Presents`), since a record at that name is presented as itself. -/
def stmtRecord (env : ReachEnv μ) (c : ReachCache) (s : Spot) (cv : ConstantVal) :
    μ (ReachCache × Except CheckError (Declaration × Name)) := do
  let h := s.part.mod
  if !reduceOpNames.contains cv.name then return (c, .ok (.axiomDecl cv, h))
  match ← privSpot env c s with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok p) =>
    if p.pos.tag == 0 || p.pos.tag == 3 then pure (c, .ok (.axiomDecl cv, h))
    else pure (c, .error (.invalid s!"module {h} declares {cv.name}, a compiler-trust name, \
      as neither an opaque constant nor an axiom"))

/-- **The record presenting `x`, and its home** (see the module docstring): read at the
importer's copy, or at a completion's located copy as a statement. -/
def readRecord (env : ReachEnv μ) (c : ReachCache) (x : Name) :
    μ (ReachCache × Except CheckError (Declaration × Name)) := do
  let some (s, completed) := (match importerSpot env x with
      | some (_, s) => some (s, false)
      | none => (c.located[x]?).map (·, true))
    | pure (c, .error (.internal s!"the reach pushed {x}, which nothing locates"))
  let h := s.part.mod
  if s.pos.skipped then
    return (c, .error (.invalid s!"a context record reads {x} of {h}, which is unsafe or partial"))
  match ← stmtAt env c s with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok (cv, k)) =>
    match groupOfKind x k with
    | some n =>
      match ← groupAt env c ⟨h, .private⟩ n with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok (some d)) => pure (c, .ok (d, h))
      | (c, .ok none) =>
        pure (c, .error (.invalid s!"module {h}: the group of {n} lacks a member or a \
          constructor"))
    | none =>
      match k with
      | .defn .. =>
        if completed then return ← stmtRecord env c s cv
        match ← withPart env c s.part fun r st => entryWith r st s.pos.loc with
        | (c, .error e) => pure (c, .error e)
        | (c, .ok e) =>
          match recordOfEntry e with
          | .ok d => pure (c, .ok (d, h))
          | .error e => pure (c, .error e)
      | .quot q =>
        match recordOfEntry ⟨cv.name, cv.levelParams, cv.type, .quot q⟩ with
        | .ok d => pure (c, .ok (d, h))
        | .error e => pure (c, .error e)
      | _ => stmtRecord env c s cv

end

/-! ## The worklist -/

/-- **The reach's logical state**: the names pushed so far, the names the context's records
install, the records, their homes and what each reads, the names still to read. -/
structure ReachLog where
  seen : Std.HashSet Name
  stored : Std.HashSet Name
  ctx : Array Declaration
  homes : Array Name
  /-- what each record reads -/
  reads : Array (List Name)
  stack : List Name

/-- Push the names not seen yet. -/
def pushNames (seen : Std.HashSet Name) (stack : List Name) :
    List Name → Std.HashSet Name × List Name
  | [] => (seen, stack)
  | y :: ys =>
    if seen.contains y then pushNames seen stack ys
    else pushNames (seen.insert y) (y :: stack) ys

/-- **A record added**: its names stored, what it reads (`rd`) pushed. -/
def ReachLog.add (L : ReachLog) (d : Declaration) (h : Name) (rd rest : List Name) : ReachLog :=
  let (seen, stack) := pushNames L.seen rest rd
  { seen, stored := (declNames d).foldl (fun s n => s.insert n) L.stored,
    ctx := L.ctx.push d, homes := L.homes.push h, reads := L.reads.push rd, stack }

/-- **The worklist's start**: the roots pushed, nothing read. -/
def ReachLog.init (rs : List Name) : ReachLog :=
  let p := pushNames {} [] rs
  { seen := p.1, stored := {}, ctx := #[], homes := #[], reads := #[], stack := p.2 }

/-- Why the record read for `x` does not store it. -/
def missingError (d : Declaration) (x h : Name) : CheckError :=
  match d with
  | .indDecl .. =>
    if (declConstants d).isEmpty then
      .notImplemented s!"the inductive group of {x}, read from {h}: a group the recogniser \
        does not read"
    else .invalid s!"the group read for {x} from {h} does not declare it"
  | .axiomDecl cv =>
    if cv.name = sorryAxName then .notImplemented s!"a context record reads {x} (sorryAx)"
    else .invalid s!"the record read for {x} from {h} does not declare it"
  | _ => .invalid s!"the record read for {x} from {h} does not declare it"

/-- **The copies of every name two loaded modules hold**, by name: each copy's module and
statement. -/
def clashCopiesOf (wr : WorkerReads) : Std.HashMap Name (Array (Name × ConstantVal)) :=
  wr.clashes.foldl (fun m cl =>
    m.insert cl.name (cl.copies.map fun (cp, cv, _) => (wr.loads.nameAt cp.mod, cv))) {}

/-- A failed read of the record of `x`, read from `h`, names the record. -/
def inRecord (x h : Name) : CheckError → CheckError
  | .invalid m => .invalid s!"the record of {x}, read from {h}: {m}"
  | e => e

/-- **The reach's worklist** (see the module docstring). -/
def reachGo {μ : Type → Type} [CheckerIO μ] (env : ReachEnv μ) :
    Nat → ReachLog → ReachCache → μ (Except CheckError (ReachLog × ReachCache))
  | fuel, L, c =>
    match L.stack with
    | [] =>
      if c.partners.isEmpty then pure (.ok (L, c)) else
      match fuel with
      | 0 => pure (.error (.internal "the reach ran out of steps"))
      | fuel + 1 => do
        let ps := c.partners.toList
        match ← capturePairs env { c with partners := #[] } ps with
        | (_, .error e) => pure (.error e)
        | (c, .ok ()) =>
          let (seen, stack) := pushNames L.seen [] (ps.map (·.2))
          reachGo env fuel { L with seen, stack } c
    | x :: rest =>
      match fuel with
      | 0 => pure (.error (.internal "the reach ran out of steps"))
      | fuel + 1 =>
        if L.stored.contains x then reachGo env fuel { L with stack := rest } c else do
        match ← readRecord env c x with
        | (_, .error e) => pure (.error e)
        | (c, .ok (d, h)) =>
          let ns := declNames d
          if !ns.contains x then pure (.error (missingError d x h))
          else if ns.any L.stored.contains then
            pure (.error (.invalid s!"two context records store a name of {x}'s record (of {h})"))
          else
            let rd := (recordReads d).toList
            match ← captureAll env h c rd with
            | (_, .error e) => pure (.error (inRecord x h e))
            | (c, .ok ()) =>
              match ← storedNamesOk env c h ns with
              | (_, .error e) => pure (.error e)
              | (c, .ok ()) =>
                reachGo env fuel (L.add d h rd rest)
                  { c with partners := c.partners ++ clashPartners env ns }

/-! ## The validation and the flags -/

/-- **Every context record validated** (`recordOk`), the first failure named. -/
def validateCtx (ds : Array Declaration) (hs : Array Name) : Except CheckError Unit :=
  if ds.all recordOk then .ok () else
    match (ds.zip hs).find? (fun (d, _) => !recordOk d) with
    | some (d, h) => .error (.invalid s!"the record {declCLabel d} of module {h} is malformed \
        (a free or loose bound variable, an undeclared universe parameter, a nested rule's \
        datum, a table's bodies or a literal's shape)")
    | none => .error (.internal "a malformed context record not found")

/-- **Is a statement's type a proposition**, by the kernel's inference at `fe`. -/
def typeIsPropC (fe : FEnv) (cv : ConstantVal) : CheckCM Bool := do
  let jsty ← inferI .verified fe false checkFuel false 0 cv.type
  let u ← opSIxC .verified fe 0 jsty
  liftFueled "level comparison" (Level.isEquiv u .zero)

/-- **The part of the context below a name**: the records before the first one storing it (the
specification's `Module.part`). -/
def ctxPart (ctx : List Declaration) (y : Name) : List Declaration :=
  ctx.take (ctx.findIdx fun d => (declNames d).contains y)

/-- **The inferred flags**: every recorded statement a proposition over the part of the context
below its name (`ctxPart`), as the specification's proof route asks and as Lean's merge infers it
over the constants loaded before.  The context is in read order, so a statement's names are
stored before its record, unless it reads its own name, which no home accepts. -/
def inferFlags (ctx : List Declaration) : List (String × Name × ConstantVal) → Except CheckError Unit
  | [] => .ok ()
  | (what, y, cv) :: rest =>
    let fe := mkFEnv (streamEnv (ctxPart ctx y))
    if !(exprOk cv.levelParams 0 cv.type && constsResolveFC fe cv.type) then
      .error (.invalid s!"the statement of {y} reads a name the context does not store before it")
    else
      match (typeIsPropC fe cv).run' {} with
      | .error e => .error e
      | .ok true => inferFlags ctx rest
      | .ok false => .error (.invalid s!"{what}: the copies of {y} of two modules are not one \
          constant (its type is not a proposition)")

/-! ## The read order -/

/-- **Each context name's record**, by its position. -/
def ownerMap (ds : Array Declaration) : Std.HashMap Name Nat :=
  (List.range ds.size).foldl
    (fun m j => (declNames (ds.getD j default)).foldl (fun m y => m.insert y j) m) {}

/-- **The read order's state**: the positions placed so far, in order, and as a set. -/
structure SortSt where
  order : Array Nat := #[]
  placed : Std.HashSet Nat := {}

/-- **The record at position `i` placed after its reads** `ys` still to place (a post-order
walk): a read stored by `i` itself or by a placed record is placed; any other read's record is
placed first, unless it is on the walk's path (`path`, the records being placed), which is a cycle
among the records' reads, malformed input.  `fuel` bounds the walk's depth. -/
def sortVisit (ds : Array Declaration) (rds : Array (List Name)) (owner : Std.HashMap Name Nat)
    (fuel i : Nat)
    (path : Std.HashSet Nat) (ys : List Name) (st : SortSt) : Except CheckError SortSt :=
  match fuel, ys with
  | 0, _ => .error (.internal "the read order ran out of steps")
  | _ + 1, [] => .ok { order := st.order.push i, placed := st.placed.insert i }
  | fuel + 1, y :: ys =>
    match owner[y]? with
    | none => .error (.internal s!"a context record reads {y}, which no context record stores")
    | some j =>
      if j == i || st.placed.contains j then sortVisit ds rds owner (fuel + 1) i path ys st
      else if path.contains j then
        .error (.invalid s!"the context records {declCLabel (ds.getD i default)} and \
          {declCLabel (ds.getD j default)} read each other (through {y})")
      else
        match sortVisit ds rds owner fuel j (path.insert j) (rds.getD j []) st with
        | .error e => .error e
        | .ok st => sortVisit ds rds owner (fuel + 1) i path ys st
termination_by (fuel, ys.length)

/-- Every record of `is` placed, each after its reads. -/
def sortFrom (ds : Array Declaration) (rds : Array (List Name)) (owner : Std.HashMap Name Nat)
    (fuel : Nat) :
    List Nat → SortSt → Except CheckError SortSt
  | [], st => .ok st
  | i :: is, st =>
    if st.placed.contains i then sortFrom ds rds owner fuel is st else
    match sortVisit ds rds owner fuel i (({} : Std.HashSet Nat).insert i) (rds.getD i []) st with
    | .error e => .error e
    | .ok st => sortFrom ds rds owner fuel is st

/-- **The context's records in read order**: their positions, each record after the records
storing what it reads (`rds`, each record's `recordReads`; `readOrder_spec`); a cycle among their
reads is malformed input. -/
def readOrder (ds : Array Declaration) (rds : Array (List Name)) : Except CheckError (Array Nat) :=
  (sortFrom ds rds (ownerMap ds) (ds.size + 1) (List.range ds.size) {}).map (·.order)

/-! ## The reach -/

/-- **What the reach gives**: the context's records with their homes, the completed names
with the homes that located them, and its counts. -/
structure Reach where
  ctx : Array Declaration
  homes : Array Name
  completed : Array (Name × Name)
  searches : Nat
  inferred : Nat

/-- **The reach of module `m`** from the names its own records read (`roots`): the clash
rule's keys, the worklist, the context's validation, the inferred flags. -/
def reach {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (m : Name) (wr : WorkerReads)
    (own : Std.HashSet Name) (roots : Array Name) : μ (Except CheckError Reach) := do
  let env : ReachEnv μ := { rd, mod := m, wr, own, copies := clashCopiesOf wr }
  match ← clashAgree env {} wr.clashes.toList #[] with
  | (_, .error e) => pure (.error e)
  | (c, .ok extra) =>
    let rs := (roots ++ extra).toList.filter (!own.contains ·)
    match rs.find? (!wr.index.first.contains ·) with
    | some x => pure (.error (.invalid s!"module {m} reads {x}, which no module it loads holds"))
    | none =>
      let L := ReachLog.init rs
      let fuel := wr.index.first.size + wr.index.more.size + (1 <<< 24)
      match ← reachGo env fuel L c with
      | .error e => pure (.error e)
      | .ok (L, c) =>
        match readOrder L.ctx L.reads with
        | .error e => pure (.error e)
        | .ok o =>
        let ctx := o.map (L.ctx.getD · default)
        let homes := o.map (L.homes.getD · default)
        match validateCtx ctx homes with
        | .error e => pure (.error e)
        | .ok () =>
          match inferFlags ctx.toList c.pending.toList with
          | .error e => pure (.error e)
          | .ok () =>
            pure (.ok { ctx, homes, completed := c.completed,
                        searches := c.searches, inferred := c.pending.size })

end ConLeche.Driver
