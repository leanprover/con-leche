module

public import ConLeche.Kernel.Install

@[expose] public section

/-!
# What a record reads

The names a term, a constant's laws and a record read, as `Expr.constsResolve` and
`Modular.RecordScoped` ask them stored (`Expr.needs`, the specification), and the walk that
computes them, one memoized walk of each expression's DAG (`needsGo`).  Shared by the
sidecar's justification (`ConLeche/Cached/Justify.lean`) and the modular worker's reach
(`ConLeche/Driver/Reach.lean`).
-/

namespace ConLeche.Cached

open ConLeche


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
    | .indInfo _ caps => x.names caps.all
    | _ => x
  x.names (pinFootprint ci.toConstantVal.name)

/-- What a table reads: its structure, its constructor, its bodies. -/
def NeedsSt.table (x : NeedsSt) (t : ProjTable) : NeedsSt :=
  t.bodies.toList.foldl NeedsSt.expr (x.names [t.structName, t.ctor])



end ConLeche.Cached
