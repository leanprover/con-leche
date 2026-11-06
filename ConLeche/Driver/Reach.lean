module

public import ConLeche.Frontend.Olean
public import ConLeche.Modular
import ConLeche.Cached.ParsedC

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
  `groupRecord`; read from the home's private part where the loaded part lacks a member or
  a constructor).  What the record reads (`recordReads`) is pushed.
* **The completion**: a name the index lacks, read by a record of home `h`, is located in
  `h`'s view (`viewOf`: `h`'s own private part first, then the parts `h`'s header fixpoint
  loads, the first copy found; never by a name's `_private` spelling) and read from its
  module's private part as its statement (a group whole); its reads are resolved or
  completed in turn, each in its own home's view.  A name located nowhere is malformed
  input (exit 1).
* **The capture check** (`captureOne`), for every record of home `h` and every name `y` it
  reads: the context's copy of `y` stands for `h`'s if it is `h`'s own, or `h`'s
  public-import closure holds its module and `y` is in that module's exported part (`h`'s
  view then holds that copy, and `h`'s clash rule made every copy it might choose one
  key); otherwise `y` is located in `h`'s view and the two copies must have one key
  (`keyCheck`): one module, or both proofs of one statement.  Else the module is rejected
  ("name capture").  A context record reading one of `M`'s own names is rejected so too.
* **Proof flags by inference** (`proofStatus`, ruling 3 of #460; axioms by #444's): a copy
  is a proof if it is a theorem, or (an exported axiom) its home's private part declares a
  theorem there, or it is a definition, opaque constant or axiom (exported or not, at its
  home) whose type the kernel infers to be a proposition at the context (`typeIsPropC`,
  after the context is built and validated).  The inference accepts every well-typed type
  Lean's `isPropCheap` accepts, so every pair Lean's merge identifies has one key.  Every
  name two loaded modules hold (`WorkerReads.clashes`) must have one key so (`clashKeys`);
  a clash whose flag is inferred has its name reached, so that its statement's names are in
  the context.
* **What a record reads** (`recordReads`): the names its constants' laws and its tables
  ask stored, `RecordScoped`'s (`ConLeche/Modular.lean`): every constant of a type, of a
  definition's value, of a recursor's rules and nested pins, a literal's and a
  projection's names, a type former's block members and η constructor, a table's
  structure, constructor and bodies, and `pinFootprint` at a pinned name; one memoized
  walk of each expression's DAG (`needsGo`).
* **The validation** (`validateCtx`): every context record validated as untrusted input
  (`recordOk`: closed, every loose bound variable bound, every level parameter declared, a
  nested rule's datum read off its recursor's type, a literal's name's shape, a table's
  bodies likewise); with the reach's closure, the context is `EnvWF`
  (`ConLeche/Verify/Driver/Reach.lean`, `reach_ok`).

**Termination** is by a fuel: every pushed name is new, out of the index plus the located
names, and each step pops one.
-/

namespace ConLeche.Driver

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

/-! ## What a record reads -/

/-- The names a literal reads (`Expr.constsResolve`'s): the `Nat` basis, and for a string
the string-support constants. -/
def litNeeds : Literal → List Name
  | .natVal _ => [natName, natZeroName, natSuccName]
  | .strVal _ => [natName, natZeroName, natSuccName, stringName, stringOfListName, listName,
      listNilName, listConsName, charName, charOfNatName]

/-- **The names `Expr.constsResolve` asks stored**: the specification of `needsGo`. -/
def _root_.ConLeche.Expr.needs : Expr → List Name
  | .bvar _ | .sort _ => []
  | .lit l => litNeeds l
  | .const n _ => [n]
  | .fvar _ ty => ty.needs
  | .app f a => f.needs ++ a.needs
  | .lam ty b | .forallE ty b => ty.needs ++ b.needs
  | .letE ty v b => ty.needs ++ v.needs ++ b.needs
  | .proj s _ e => s :: e.needs

/-- **`Expr.needs`, one memoized walk of the DAG**: `seen` the compound subterms walked,
`acc` the names so far.  A subterm is recorded after its children. -/
def needsGo (seen : Std.HashSet Expr) (acc : Array Name) : Expr → Std.HashSet Expr × Array Name
  | .bvar _ => (seen, acc)
  | .sort _ => (seen, acc)
  | .lit l => (seen, acc ++ litNeeds l)
  | .const n _ => (seen, acc.push n)
  | e =>
    if seen.contains e then (seen, acc) else
      let (seen, acc) : Std.HashSet Expr × Array Name :=
        match e with
        | .fvar _ ty => needsGo seen acc ty
        | .app f a =>
          let (seen, acc) := needsGo seen acc f
          needsGo seen acc a
        | .lam ty b =>
          let (seen, acc) := needsGo seen acc ty
          needsGo seen acc b
        | .forallE ty b =>
          let (seen, acc) := needsGo seen acc ty
          needsGo seen acc b
        | .letE ty v b =>
          let (seen, acc) := needsGo seen acc ty
          let (seen, acc) := needsGo seen acc v
          needsGo seen acc b
        | .proj s _ x => needsGo seen (acc.push s) x
        | _ => (seen, acc)
      (seen.insert e, acc)

/-- The walk's state through several expressions. -/
abbrev NeedsSt := Std.HashSet Expr × Array Name

/-- One more expression's names. -/
def NeedsSt.expr (x : NeedsSt) (e : Expr) : NeedsSt := needsGo x.1 x.2 e

/-- Some names. -/
def NeedsSt.names (x : NeedsSt) (ns : List Name) : NeedsSt := (x.1, x.2 ++ ns)

/-- What a recursor rule reads: its right-hand side, its constructor, a nested datum's pins. -/
def NeedsSt.rule (x : NeedsSt) (r : RecRule) : NeedsSt :=
  let x := (x.expr r.rhs).names [r.ctor]
  match r.fire with
  | .nested _ pins => pins.foldl NeedsSt.expr x
  | _ => x

/-- **What a constant's laws read** (`EntryScoped`'s names). -/
def NeedsSt.const (x : NeedsSt) (ci : ConstantInfo) : NeedsSt :=
  let x := x.expr ci.toConstantVal.type
  let x := match ci with
    | .defnInfo _ v _ => x.expr v
    | .recInfo _ _ _ _ rules => rules.foldl NeedsSt.rule x
    | .indInfo _ caps => x.names (caps.all ++ if caps.eta then [caps.etaCtor] else [])
    | _ => x
  x.names (pinFootprint ci.toConstantVal.name)

/-- What a table reads: its structure, its constructor, its bodies. -/
def NeedsSt.table (x : NeedsSt) (t : ProjTable) : NeedsSt :=
  t.bodies.toList.foldl NeedsSt.expr (x.names [t.structName, t.ctor])

/-- **What a record reads**: its constants' laws' names and its tables', each expression's
DAG walked once (`RecordScoped`'s names, `recordReads_scoped`). -/
def recordReads (d : Declaration) : Array Name :=
  ((declTables d).foldl NeedsSt.table ((declConstants d).foldl NeedsSt.const ({}, #[]))).2

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
        ls == lvls && dom.getAppArgs == pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map fun i => Expr.bvar (mI - rP - 1 - i)
      | _ => false
    | _ => false

/-- A recursor rule's clauses: its right-hand side, and its datum if nested. -/
def ruleOk (lps : List Name) (ty : Expr) (mI rP : Nat) (r : RecRule) : Bool :=
  exprOk lps 0 r.rhs &&
    match r.fire with
    | .nested lvls pins => nestedOk lps ty mI rP lvls pins
    | _ => true

/-- **A constant's syntactic clauses** (`ConstWF`'s, the names' resolution aside): its type;
a definition's value; a recursor's rules. -/
def constOk : ConstantInfo → Bool
  | .defnInfo cv v _ => exprOk cv.levelParams 0 cv.type && exprOk cv.levelParams 0 v
  | .recInfo cv mI rP _ rules =>
    exprOk cv.levelParams 0 cv.type && rules.all (ruleOk cv.levelParams cv.type mI rP)
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
structure ReachEnv where
  sp : SearchPath
  /-- the module whose context it is -/
  mod : Name
  wr : WorkerReads
  /-- the module's own names -/
  own : Std.HashSet Name

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
  /-- statements whose being a proposition decides a key, inferred at the context -/
  pending : Array (String × Name × ConstantVal) := #[]
  /-- how many reads were looked for in their reader's view -/
  searches : Nat := 0

section
variable {μ : Type → Type} [CheckerIO μ]

/-! ## The parts -/

/-- **A part's name table**: the index's where the module is loaded at that level, else
read once. -/
def tableOf (env : ReachEnv) (c : ReachCache) (k : PartKey) :
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
    match ← readPartNames env.sp (k.mod, k.level) with
    | .error e => pure (c, .error e)
    | .ok t => pure ({ c with tables := c.tables.insert k t }, .ok t)

/-- **A part's name lookup**, built once. -/
def lookOf (env : ReachEnv) (c : ReachCache) (k : PartKey) :
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
once, its memo taken out while it is extended. -/
def withPart {α : Type} (env : ReachEnv) (c : ReachCache) (k : PartKey)
    (f : Region → SM → Option (SM × α)) : μ (ReachCache × Except CheckError (α)) := do
  let got : Except CheckError (Region × SM) ← match c.parts[k]? with
    | some p => pure (.ok p)
    | none =>
      match ← readFiles env.sp k.mod k.level with
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
    | none => pure ({ c with parts := c.parts.insert k (r, st) }, .error (undecodable k.mod))

/-- Several constants with one memo (`entryWith`, in order). -/
def entriesWith (r : Region) (st : SM) : List Nat → Option (SM × List (CEntryF Name Expr))
  | [] => some (st, [])
  | l :: ls => do
    let (st, e) ← entryWith r st l
    let (st, es) ← entriesWith r st ls
    pure (st, e :: es)

/-- **A copy's statement and kind** (the kind's expressions left out). -/
def stmtAt (env : ReachEnv) (c : ReachCache) (s : Spot) :
    μ (ReachCache × Except CheckError (ConstantVal × CKindF Name Unit)) :=
  withPart env c s.part fun r st => stmtWith r st s.pos.loc

/-- **A copy in a module's private part**: itself, or the private part's constant of its
name. -/
def privSpot (env : ReachEnv) (c : ReachCache) (s : Spot) :
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
def viewAdd (env : ReachEnv) :
    ReachCache → Std.HashMap Name Spot → List PartKey →
      μ (ReachCache × Except CheckError (Std.HashMap Name Spot))
  | c, v, [] => pure (c, .ok v)
  | c, v, k :: ks => do
    match ← tableOf env c k with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok t) =>
      let v := t.consts.foldl (fun (v : Std.HashMap Name Spot) q =>
        if v.contains q.name then v else v.insert q.name ⟨k, q⟩) v
      viewAdd env c v ks

/-- **Module `h`'s view, by name**: `h`'s own private part, then the parts `h`'s header
fixpoint loads, in its order, the first copy of each name.  Built once per home. -/
def viewOf (env : ReachEnv) (c : ReachCache) (h : Name) :
    μ (ReachCache × Except CheckError (Std.HashMap Name Spot)) := do
  match c.views[h]? with
  | some v => pure (c, .ok v)
  | none =>
    match ← tableOf env c ⟨h, .private⟩ with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok own) =>
      match ← headerFixpoint env.sp own.header.isModule own.header.imports with
      | .error e => pure (c, .error e)
      | .ok ld =>
        let ks : List PartKey := ⟨h, .private⟩ ::
          (ld.order.zip ld.flags).toList.map fun (m, fl) => ⟨m, fl.level⟩
        match ← viewAdd env c {} ks with
        | (c, .error e) => pure (c, .error e)
        | (c, .ok v) => pure ({ c with views := c.views.insert h v }, .ok v)

/-- **`y` located in `h`'s view.** -/
def locate (env : ReachEnv) (c : ReachCache) (h y : Name) :
    μ (ReachCache × Except CheckError (Option Spot)) := do
  match ← viewOf env c h with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok v) => pure ({ c with searches := c.searches + 1 }, .ok v[y]?)

/-- **The importer's copy of a loaded name**: its module's position in the load order and
the copy. -/
def importerSpot (env : ReachEnv) (y : Name) : Option (Nat × Spot) := do
  let cp ← env.wr.index.first[y]?
  let q ← env.wr.index.at cp
  let ld := env.wr.loads
  pure (cp.mod, ⟨⟨ld.nameAt cp.mod, ((ld.flags[cp.mod]?).getD default).level⟩, q⟩)

/-! ## Keys -/

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
def proofStatus (env : ReachEnv) (c : ReachCache) (s : Spot) (k : CKindF Name Unit) :
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

/-- **Two copies of `y` have one key**: one module, or both proofs of one statement (a
flag to be inferred is recorded with its statement). -/
def keyCheck (env : ReachEnv) (c : ReachCache) (h y : Name) (s₁ s₂ : Spot) :
    μ (ReachCache × Except CheckError Unit) := do
  if s₁.part.mod == s₂.part.mod then return (c, .ok ())
  let what := s!"name capture at {y}, read by module {h}"
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
          else if p₁ == .infer || p₂ == .infer then
            pure ({ c with pending := c.pending.push (what, y, cv₁) }, .ok ())
          else pure (c, .ok ())

/-- **The clash rule's keys** (ruling 3 of #460): every name two loaded modules hold must
have one key; the names whose flags are inferred, to be reached. -/
def clashKeys (env : ReachEnv) :
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
      else if ps.contains .infer then
        match spots with
        | (_, cv, _) :: _ =>
          let why := s!"two loaded modules store {cl.name}"
          clashKeys env { c with pending := c.pending.push (why, cl.name, cv) }
            cls (acc.push cl.name)
        | [] => clashKeys env c cls acc
      else clashKeys env c cls acc
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
def inExported (env : ReachEnv) (c : ReachCache) (m : Name) (level : OLeanLevel) (y : Name) :
    μ (ReachCache × Except CheckError Bool) := do
  if level == .exported then return (c, .ok true)
  match ← lookOf env c ⟨m, .exported⟩ with
  | (c, .error e) => pure (c, .error e)
  | (c, .ok l) => pure (c, .ok (l.contains y))

/-- **The capture check of one read** `y` of a record of home `h`, and the completion of a
name the index lacks (see the module docstring). -/
def captureOne (env : ReachEnv) (c : ReachCache) (h y : Name) :
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
      | (c, .ok (some s₂)) => keyCheck env c h y s₁ s₂
  | none =>
    match c.located[y]? with
    | some s₁ =>
      if s₁.part.mod == h then return (c, .ok ())
      match ← locate env c h y with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok none) => pure (c, .error (.invalid s!"module {h} reads {y}, which its view \
          does not hold"))
      | (c, .ok (some s₂)) => keyCheck env c h y s₁ s₂
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

/-- The capture check of every read of a record. -/
def captureAll (env : ReachEnv) (h : Name) :
    ReachCache → List Name → μ (ReachCache × Except CheckError Unit)
  | c, [] => pure (c, .ok ())
  | c, y :: ys => do
    match ← captureOne env c h y with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok ()) => captureAll env h c ys

/-! ## A record read -/

/-- A part's recursors' locations by their block's first member, read once. -/
def recBlocksOf (env : ReachEnv) (c : ReachCache) (k : PartKey) :
    μ (ReachCache × Except CheckError (Std.HashMap Name (Array Nat))) := do
  match c.recBlocks[k]? with
  | some m => pure (c, .ok m)
  | none =>
    match ← tableOf env c k with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok t) =>
      let locs := (t.consts.filter (·.tag == 7)).toList.map (·.loc)
      match ← withPart env c k (fun r st =>
          (locs.mapM fun l => (kindNamesAt r l).map (l, ·)).map (st, ·)) with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok ks) =>
        let m := ks.foldl (fun (m : Std.HashMap Name (Array Nat)) (l, k) => match k with
          | .recur (a :: _) .. => m.alter a fun | none => some #[l] | some xs => some (xs.push l)
          | _ => m) {}
        pure ({ c with recBlocks := c.recBlocks.insert k m }, .ok m)

/-- **Type `n`'s group, read from one part**: `none` where the part lacks one of its
members or constructors. -/
def groupAt (env : ReachEnv) (c : ReachCache) (k : PartKey) (n : Name) :
    μ (ReachCache × Except CheckError (Option Declaration)) := do
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
              let ctorNames := tys.flatMap fun t => match t.kind with
                | .induct _ _ _ cs .. => cs
                | _ => []
              match ctorNames.mapM (look[·]?) with
              | none => pure (c, .ok none)
              | some cqs =>
                match ← recBlocksOf env c k with
                | (c, .error e) => pure (c, .error e)
                | (c, .ok rb) =>
                  let rls := ((all.head?.bind (rb[·]?)).getD #[]).toList
                  match ← withPart env c k fun r st =>
                      entriesWith r st (cqs.map (·.loc) ++ rls) with
                  | (c, .error e) => pure (c, .error e)
                  | (c, .ok rest) =>
                    let recs := rest.filter fun e => match e.kind with
                      | .recur all' .. => all' == all
                      | _ => true
                    let mg := mergedOfList ((t :: tys ++ recs).map CEntry.ofF)
                    match groupRecord mg n with
                    | .ok d => pure (c, .ok (some d))
                    | .error e => pure (c, .error e)
        | _ => pure (c, .error (.invalid s!"module {k.mod}: {n} is not an inductive type"))

/-- **The record presenting `x`, and its home** (see the module docstring): read at the
importer's copy, or at a completion's located copy as a statement. -/
def readRecord (env : ReachEnv) (c : ReachCache) (x : Name) :
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
    let grp : Option Name := match k with
      | .induct .. => some x
      | .ctor ind .. => some ind
      | .recur (a :: _) .. => some a
      | _ => none
    match grp with
    | some n =>
      match ← groupAt env c s.part n with
      | (c, .error e) => pure (c, .error e)
      | (c, .ok (some d)) => pure (c, .ok (d, h))
      | (c, .ok none) =>
        let pk : PartKey := ⟨h, .private⟩
        if s.part.level == .private then
          return (c, .error (.invalid s!"module {h}: the group of {n} lacks a member or a \
            constructor"))
        match ← groupAt env c pk n with
        | (c, .error e) => pure (c, .error e)
        | (c, .ok (some d)) => pure (c, .ok (d, h))
        | (c, .ok none) =>
          pure (c, .error (.invalid s!"module {h}: the group of {n} lacks a member or a \
            constructor"))
    | none =>
      match k with
      | .defn .. =>
        if completed then return (c, .ok (.axiomDecl cv, h))
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
      | _ => pure (c, .ok (.axiomDecl cv, h))

end

/-! ## The worklist -/

/-- **The reach's logical state**: the names pushed so far, the names the context's records
install, the records and their homes, the names still to read. -/
structure ReachLog where
  seen : Std.HashSet Name
  stored : Std.HashSet Name
  ctx : Array Declaration
  homes : Array Name
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
    ctx := L.ctx.push d, homes := L.homes.push h, stack }

/-- **The worklist's start**: the roots pushed, nothing read. -/
def ReachLog.init (rs : List Name) : ReachLog :=
  let p := pushNames {} [] rs
  { seen := p.1, stored := {}, ctx := #[], homes := #[], stack := p.2 }

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

/-- **The reach's worklist** (see the module docstring). -/
def reachGo {μ : Type → Type} [CheckerIO μ] (env : ReachEnv) :
    Nat → ReachLog → ReachCache → μ (Except CheckError (ReachLog × ReachCache))
  | fuel, L, c =>
    match L.stack with
    | [] => pure (.ok (L, c))
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
            | (_, .error e) => pure (.error e)
            | (c, .ok ()) => reachGo env fuel (L.add d h rd rest) c

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
  let jsty ← (coreKnotI .verified false fe checkFuel).infer 0 cv.type
  let u ← opSIxC .verified fe 0 jsty
  liftFueled "level comparison" (Level.isEquiv u .zero)

/-- **The inferred flags**: every recorded statement a proposition at the context. -/
def inferFlags (fe : FEnv) : List (String × Name × ConstantVal) → Except CheckError Unit
  | [] => .ok ()
  | (what, y, cv) :: rest =>
    if !(exprOk cv.levelParams 0 cv.type && cv.type.constsResolveF fe) then
      .error (.internal s!"the statement of {y} does not resolve in the context")
    else
      match (typeIsPropC fe cv).run' {} with
      | .error e => .error e
      | .ok true => inferFlags fe rest
      | .ok false => .error (.invalid s!"{what}: the copies of {y} of two modules are not one \
          constant (its type is not a proposition)")

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
def reach {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) (wr : WorkerReads)
    (own : Std.HashSet Name) (roots : Array Name) : μ (Except CheckError Reach) := do
  let env : ReachEnv := { sp, mod := m, wr, own }
  match ← clashKeys env {} wr.clashes.toList #[] with
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
        match validateCtx L.ctx L.homes with
        | .error e => pure (.error e)
        | .ok () =>
          let fe := mkFEnv (streamEnv L.ctx.toList)
          match inferFlags fe c.pending.toList with
          | .error e => pure (.error e)
          | .ok () =>
            pure (.ok { ctx := L.ctx, homes := L.homes, completed := c.completed,
                        searches := c.searches, inferred := c.pending.size })

end ConLeche.Driver
