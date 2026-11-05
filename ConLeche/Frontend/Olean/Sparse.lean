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

`sparseNameP`/`sparseExprP` are `nameP`/`exprP`
(`ConLeche/Verify/Frontend/Olean/Sparse.lean`: `sparseExprP_eq`,
`sparseNameP_eq`), so a constant read by them is the specification's
(`sparseEntry_eq`).  The recursion's depth is the value's nesting depth,
as the checker's own walks.
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

/-- **The object at `g`, read as kind `k`**, by the specification's node
function, its kids' values from the memo, and added to it. -/
def SM.build (r : Region) (k : UInt8) (g : Nat) (st : SM) : Option SM :=
  if k = kName then
    (nameNode r g fun c _ => st.names[c]?).map fun v => { st with names := st.names.insert g v }
  else if k = kLevel then
    (levelNode r g (fun c _ => st.levels[c]?) (fun c _ => st.names[c]?)).map fun v =>
      { st with levels := st.levels.insert g v }
  else if k = kLevels then
    (levelsNode r g (fun c _ => st.lists[c]?) (fun c _ => st.levels[c]?)).map fun v =>
      { st with lists := st.lists.insert g v }
  else
    (exprNode r g (fun c _ => st.exprs[c]?) (fun c _ => st.names[c]?) (fun c _ => st.levels[c]?)
      (fun c _ => st.lists[c]?)).map fun v => { st with exprs := st.exprs.insert g v }

/-! ## The recursion -/

-- (`hd` is read by `decreasing_by`, which the linter does not see)
set_option linter.unusedVariables false in
mutual
/-- **The object at `g` read as kind `k`, into the memo**: nothing to do
if it is there; else its kids (`kidsGo`), then the object itself. -/
def sGo (r : Region) (k : UInt8) (g : Nat) (st : SM) : Option SM :=
  if st.has k g then some st
  else if r.fits g then
    match kidTable k (r.tag g) (r.nobjs g) with
    | none => none
    | some fs =>
      match kidsGo r g fs st with
      | some st => st.build r k g
      | none => none
  else none
termination_by (g, 1, 0)

/-- The kids the fields `fs` of the object at `g` lead to, into the memo. -/
def kidsGo (r : Region) (g : Nat) : List (Nat × UInt8 × Bool) → SM → Option SM
  | [], st => some st
  | (i, k', nil) :: fs, st =>
    if nil && r.fld g i == 1 then kidsGo r g fs st
    else match hd : r.down g (r.fld g i) with
      | some c =>
        match sGo r k' c st with
        | some st => kidsGo r g fs st
        | none => none
      | none => none
termination_by fs => (g, 0, fs.length)
decreasing_by
  all_goals first
    | (apply Prod.Lex.right; apply Prod.Lex.right; simp)
    | (apply Prod.Lex.left; exact Region.down_lt hd)
end

/-! ## Roots -/

/-- **The `Name` a pointer stands for**, read sparsely (`nameP`). -/
def sparseNameP (r : Region) (v : UInt64) : Option Name :=
  if v == 1 then some .anonymous
  else match r.loc v with
    | some c => (sGo r kName c {}).bind (·.names[c]?)
    | none => none

/-- **The `Expr` a pointer stands for**, read sparsely (`exprP`). -/
def sparseExprP (r : Region) (v : UInt64) : Option Expr :=
  match r.loc v with
  | some c => (sGo r kExpr c {}).bind (·.exprs[c]?)
  | none => none

/-- **A constant's names and expressions, read sparsely**: each root with
a memo of its own (`CEntryF.mapM (nameP r) (exprP r)`). -/
def sparseEntry (r : Region) (sk : CEntryF UInt64 UInt64) : Option (CEntryF Name Expr) :=
  sk.mapM (sparseNameP r) (sparseExprP r)

end ConLeche.Frontend.Olean
