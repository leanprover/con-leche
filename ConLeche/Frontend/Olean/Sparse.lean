module

public import ConLeche.Frontend.Olean.Fast

@[expose] public section

/-!
# Reading `.olean` files: the sparse decoder

The fast decoder (`ConLeche/Frontend/Olean/Fast.lean`) sweeps the whole
region, its memo dense (a mark byte and four value slots per slot of the
file): the right shape for a whole module, the wrong one for a few
constants of a large file.  This decoder reads a constant at a time, each
with **a memo of its own**: from one root, exactly the objects the root
leads to, each once (`sGo`: a recursion on the location, every object's kids
first, then the object by the specification's own node function with
its kids' values taken from the memo, a map by location).  Nothing is
shared between two calls.

Beside its own memo, a read may be handed **a frontier** (`Frontier`): values
of the region's objects read earlier, read-only and shared by every read of
the module.  An object the frontier holds is taken from it, so the value
shares it with whatever else holds it, and what lies below it is not visited.
This is how a theorem's value is read when its check needs it
(`frontierExpr`, task #481).

`sparseNameP`/`sparseExprP` are `nameP`/`exprP`
(`ConLeche/Verify/Frontend/Olean/Sparse.lean`: `sparseExprP_eq`,
`sparseNameP_eq`), so a constant read by them is the specification's
(`sparseEntry_eq`); `frontierExpr` is `exprAt` if the frontier holds only
the specification's values (`frontierExpr_eq`).  The recursion's depth is the
value's nesting depth, as the checker's own walks.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## The kid table

Per kind and shape, the pointer fields a node function follows to
objects of a recursive type: the field, the kind it is read as, and
whether that kind's nullary constructor is the scalar `0`
(`ConLeche/Verify/Frontend/Olean/Kids.lean` proves the fast decoder's
marking functions are this table read four ways). -/

def nameKids : Nat → Nat → Option (List (Nat × UInt8 × Bool))
  | 1, 2 => some [(0, kName, true)]
  | 2, 2 => some [(0, kName, true)]
  | _, _ => none

def levelKids : Nat → Nat → Option (List (Nat × UInt8 × Bool))
  | 0, 0 => some []
  | 1, 1 => some [(0, kLevel, true)]
  | 2, 2 => some [(0, kLevel, true), (1, kLevel, true)]
  | 3, 2 => some [(0, kLevel, true), (1, kLevel, true)]
  | 4, 1 => some [(0, kName, true)]
  | _, _ => none

def levelsKids : Nat → Nat → Option (List (Nat × UInt8 × Bool))
  | 1, 2 => some [(0, kLevel, true), (1, kLevels, true)]
  | _, _ => none

def exprKids : Nat → Nat → Option (List (Nat × UInt8 × Bool))
  | 0, 1 => some []
  | 3, 1 => some [(0, kLevel, true)]
  | 4, 2 => some [(0, kName, true), (1, kLevels, true)]
  | 5, 2 => some [(0, kExpr, false), (1, kExpr, false)]
  | 6, 3 => some [(1, kExpr, false), (2, kExpr, false)]
  | 7, 3 => some [(1, kExpr, false), (2, kExpr, false)]
  | 8, 4 => some [(1, kExpr, false), (2, kExpr, false), (3, kExpr, false)]
  | 9, 1 => some []
  | 10, 2 => some [(1, kExpr, false)]
  | 11, 3 => some [(0, kName, true), (2, kExpr, false)]
  | _, _ => none

/-- **The objects an object leads to**: for an object read as kind `k`
with tag `t` and `n` pointer fields, the pointer fields its node
function follows to objects of a recursive type — the field, the kind
it is read as, and whether that kind's nullary constructor is the
scalar `0` — or `none` when the node function reads no object of that
shape. -/
def kidTable (k : UInt8) (t n : Nat) : Option (List (Nat × UInt8 × Bool)) :=
  if k = kName then nameKids t n
  else if k = kLevel then levelKids t n
  else if k = kLevels then levelsKids t n
  else exprKids t n


/-! ## The memo -/

/-- A sparse decoder's memo: the values read so far, by location, one
map per kind. -/
structure SM where
  names : Std.HashMap Nat Name := {}
  levels : Std.HashMap Nat Level := {}
  lists : Std.HashMap Nat (List Level) := {}
  exprs : Std.HashMap Nat Expr := {}

/-- Does the memo hold the object at `g` as kind `k`. -/
def SM.has (st : SM) (k : UInt8) (g : Nat) : Bool :=
  if k = kName then st.names.contains g
  else if k = kLevel then st.levels.contains g
  else if k = kLevels then st.lists.contains g
  else st.exprs.contains g

/-! ## The frontier -/

/-- A read-only table by location: `keys` ascending, `vals[i]` the value at
`keys[i]`. -/
structure Table (α : Type) where
  keys : Array Nat := #[]
  vals : Array α := #[]

/-- The binary search of `Table.get`, between `lo` and `hi`. -/
def Table.search {α : Type} (t : Table α) (c lo hi : Nat) : Option α :=
  if lo < hi then
    let mid := (lo + hi) / 2
    match t.keys[mid]? with
    | none => none
    | some k =>
      if k = c then t.vals[mid]?
      else if k < c then t.search c (mid + 1) hi
      else t.search c lo mid
  else none
termination_by hi - lo
decreasing_by all_goals omega

/-- The value at location `c`. -/
def Table.get {α : Type} (t : Table α) (c : Nat) : Option α := t.search c 0 t.keys.size

/-- **Values read earlier, by kind and location**, read-only: which objects it
holds is a matter of speed alone. -/
structure Frontier where
  names : Table Name := {}
  levels : Table Level := {}
  lists : Table (List Level) := {}
  exprs : Table Expr := {}

instance : Inhabited Frontier := ⟨{}⟩

/-- Does the frontier hold the object at `g` as kind `k`. -/
def Frontier.has (b : Frontier) (k : UInt8) (g : Nat) : Bool :=
  if k = kName then (b.names.get g).isSome
  else if k = kLevel then (b.levels.get g).isSome
  else if k = kLevels then (b.lists.get g).isSome
  else (b.exprs.get g).isSome

/-- Does the read hold the object at `g` as kind `k`: its memo or the frontier. -/
@[inline] def SM.holds (st : SM) (b : Frontier) (k : UInt8) (g : Nat) : Bool :=
  st.has k g || b.has k g

/-- The value of a kid: the memo's, or the frontier's. -/
@[inline] def lookup {α : Type} (m : Std.HashMap Nat α) (t : Table α) (c : Nat) : Option α :=
  match m[c]? with
  | some v => some v
  | none => t.get c

/-- **The object at `g`, read as kind `k`**, by the specification's node
function, its kids' values from the memo or the frontier, and added to the
memo. -/
def SM.buildIn (r : Region) (b : Frontier) (k : UInt8) (g : Nat) (st : SM) : Option SM :=
  if k = kName then
    (nameNode r g fun c _ => lookup st.names b.names c).map fun v =>
      { st with names := st.names.insert g v }
  else if k = kLevel then
    (levelNode r g (fun c _ => lookup st.levels b.levels c)
      (fun c _ => lookup st.names b.names c)).map fun v =>
      { st with levels := st.levels.insert g v }
  else if k = kLevels then
    (levelsNode r g (fun c _ => lookup st.lists b.lists c)
      (fun c _ => lookup st.levels b.levels c)).map fun v =>
      { st with lists := st.lists.insert g v }
  else
    (exprNode r g (fun c _ => lookup st.exprs b.exprs c) (fun c _ => lookup st.names b.names c)
      (fun c _ => lookup st.levels b.levels c) (fun c _ => lookup st.lists b.lists c)).map fun v =>
      { st with exprs := st.exprs.insert g v }

/-! ## The recursion -/

-- (`hd` is read by `decreasing_by`, which the linter does not see)
set_option linter.unusedVariables false in
mutual
/-- **The object at `g` read as kind `k`, into the memo**: nothing to do
if the memo or the frontier holds it; else its kids (`kidsGo`), then the
object itself. -/
def sGo (r : Region) (b : Frontier) (k : UInt8) (g : Nat) (st : SM) : Option SM :=
  if st.holds b k g then some st
  else if r.fits g then
    match kidTable k (r.tag g) (r.nobjs g) with
    | none => none
    | some fs =>
      match kidsGo r b g fs st with
      | some st => SM.buildIn r b k g st
      | none => none
  else none
termination_by (g, 1, 0)

/-- The kids the fields `fs` of the object at `g` lead to, into the memo. -/
def kidsGo (r : Region) (b : Frontier) (g : Nat) : List (Nat × UInt8 × Bool) → SM → Option SM
  | [], st => some st
  | (i, k', nil) :: fs, st =>
    if nil && r.fld g i == 1 then kidsGo r b g fs st
    else match hd : r.down g (r.fld g i) with
      | some c =>
        match sGo r b k' c st with
        | some st => kidsGo r b g fs st
        | none => none
      | none => none
termination_by fs => (g, 0, fs.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; apply Prod.Lex.right; simp)
    | (apply Prod.Lex.left; exact Region.down_lt hd)
end

/-! ## Roots -/

/-- **The `Expr` at location `c`**, read with a memo of its own over a frontier. -/
def frontierExpr (r : Region) (b : Frontier) (c : Nat) : Option Expr :=
  (sGo r b kExpr c {}).bind fun st => lookup st.exprs b.exprs c

/-- **The `Name` a pointer stands for**, read sparsely (`nameP`). -/
def sparseNameP (r : Region) (v : UInt64) : Option Name :=
  if v == 1 then some .anonymous
  else match r.loc v with
    | some c => (sGo r {} kName c {}).bind fun st => lookup st.names ({} : Frontier).names c
    | none => none

/-- **The `Expr` a pointer stands for**, read sparsely (`exprP`). -/
def sparseExprP (r : Region) (v : UInt64) : Option Expr :=
  match r.loc v with
  | some c => frontierExpr r {} c
  | none => none

/-- **A constant's names and expressions, read sparsely**: each root with
a memo of its own (`CEntryF.mapM (nameP r) (exprP r)`). -/
def sparseEntry (r : Region) (sk : CEntryF UInt64 UInt64) : Option (CEntryF Name Expr) :=
  sk.mapM (sparseNameP r) (sparseExprP r)

end ConLeche.Frontend.Olean
