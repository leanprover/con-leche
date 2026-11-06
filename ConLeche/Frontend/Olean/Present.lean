module

public import ConLeche.Frontend.Olean.Group
public import ConLeche.Modular

@[expose] public section

/-!
# Reading `.olean` files: an imported constant as a context record

What the reach of a module (`ConLeche/Frontend/Olean/Reach.lean`) needs of one record of
its context, beside the files:

* **what a record reads** (`recordReads`): the names its constants' laws and its tables
  ask stored, `RecordScoped`'s (`ConLeche/Modular.lean`): every constant of a type, of a
  definition's value, of a recursor's rules and nested pins, a literal's and a
  projection's names, a type former's block members and η constructor, a table's
  structure, constructor and bodies, and `pinFootprint` at a pinned name.  One memoized
  walk of each expression's DAG (`needsGo`); `recordReads_scoped`
  (`ConLeche/Verify/Frontend/Olean/Reach.lean`): where every name it lists is stored, the
  record is `RecordScoped`;
* **its validation as untrusted input** (`recordOk`): every constant it installs
  closed, every loose bound variable bound, every level parameter declared, a nested
  rule's datum read off its recursor's type, the shape a literal's name asks
  (`litShapeOk`), every table's bodies likewise: the clauses of `EnvWF` other than the
  names' resolution, which the reach's closure gives (`ctx_envWF`);
* **its read from a part of a view, with one memo per part** (`entryWith`, `stmtWith`):
  a constant whole, or its statement and its kind without expressions (a theorem's value,
  an opaque's and a hidden definition's are never read: the opaque cut).  Each is the
  full parse's constant at its position (`entryWith_of_view`, `stmtWith_of_view`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche ConLeche.Modular

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

/-! ## Reads with one memo per part -/

/-- **The constant at location `c`, read with the part's memo**, which it extends. -/
def entryWith (r : Region) (st : SM) (c : Nat) : Option (SM × CEntryF Name Expr) := do
  let sk ← constSkel r c
  let st := memoRoots r st sk
  let e ← sk.mapM (memoName r st) (memoExpr r st)
  pure (st, e)

/-- **The statement and the kind of the constant at location `c`**, its kind's expressions
left out, read with the part's memo: a theorem's value is never read. -/
def stmtWith (r : Region) (st : SM) (c : Nat) :
    Option (SM × ConstantVal × CKindF Name Unit) := do
  let sk ← constSkel r c
  let st := memoAdd r kExpr ((sk.name :: sk.levelParams).foldl (memoAdd r kName) st) sk.type
  let n ← memoName r st sk.name
  let lps ← sk.levelParams.mapM (memoName r st)
  let ty ← memoExpr r st sk.type
  let k ← sk.kind.mapM (memoName r st) (fun _ => some ())
  pure (st, ⟨n, lps, ty⟩, k)

/-! ## A constant as a record -/

/-- **One constant's record**, through the stream reader's builder (`Emit.one`, `declsOf`). -/
def recordOfEntry (c : CEntryF Name Expr) : Except CheckError Declaration :=
  match declsOf (({} : Emit).one (CEntry.ofF c)) with
  | .error (e, _) => .error e
  | .ok ds =>
    match ds.toList with
    | [d] => .ok d
    | _ => .error (.internal s!"the constant {c.name}: {ds.size} records")

end ConLeche.Frontend.Olean
