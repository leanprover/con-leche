module

public import ConLeche.Frontend.Olean.Group

@[expose] public section

/-!
# Reading `.olean` files: an imported constant as a context record

What the reach of a module (`ConLeche/Driver/Reach.lean`) reads of one constant of its
context: **its read from a part of a view, with one memo per part** (`entryWith`,
`stmtWith`): a constant whole, or its statement and its kind without expressions (a
theorem's value, an opaque's and a hidden definition's are never read: the opaque cut),
each the full parse's constant at its position (`entryWith_of_view`, `stmtWith_of_view`,
`ConLeche/Verify/Frontend/Olean/Present.lean`); and **a constant as its record**, through
the stream reader's builder (`recordOfEntry`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

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
