module

public import ConLeche.Cached.Installed
public import ConLeche.Modular
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# The module store and the local checks of a modular run (task #370)

A modular run (`ConLeche/Driver/Modular.lean`) installs every module at
a **view** of one store partitioned by home module (`MBase`,
`ConLeche/Kernel/FEnv.lean`): module `h`'s **unit** (`ModSlot`) holds the
constants its install pushed, their exported presentation, its tables,
its gates and its proofs.  This file holds the pure part of the run that
the proofs are about:

* `Store`, `Store.view` — the store and a module's view of it;
* `unitOf` — a module's unit, computed from its installed view (an
  oracle: everything the proofs need of it is re-established by
  `unitOk`), with what its importers must check (`Unit'`: `fp1`, the
  modules its exported presentation reads that every importer at that
  level loads);
* `unitOk` — the check of a unit against its module's view: the
  presentations refine the installed constants, and every name their
  laws read (`lawsOf`, verified with the checker's own resolution walk
  `constsResolveFC` against the claimed set) resolves in the module, and
  its module and level are in `fp1` or the constant's gate;
* `localOk` — module `m`'s local checks against the units of its
  context: every module of it is earlier, a module loaded privately
  brings its whole context, one loaded at the exported level brings
  `fp1`, and the copies of a name that meet in `m`'s context have one
  qualified name.

Nothing here type-checks: the declarations' checks are the fold's own
(`installDeclStep`, `checkPending`), run at the views.
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-! ## The store -/

/-- The store's name index: every name, with the modules storing it and
its position among each one's installed constants, sharded by name
hash. -/
abbrev Shards := Array (Std.HashMap Name (List (Nat × Nat)))

/-- **The store**: the name index, the names with more than one
alternate, the units (deferred: a thunk over the promise the module's
install resolves) and every module's levels. -/
structure Store where
  idx : Shards
  dups : Array Name
  slots : Array (Thunk ModSlot)
  lvls : Array ByteArray

/-- Module `i`'s levels. -/
def Store.lvl (S : Store) (i : Nat) : ByteArray := (S.lvls[i]?).getD .empty

/-- The store as module `i` sees it. -/
def Store.mb (S : Store) (i : Nat) : MBase := ⟨S.idx, S.slots, S.lvl i⟩

/-- **A view**: no constants of its own yet, the store below. -/
def viewOf (mb : MBase) : FEnv := ⟨⟨[], []⟩, {}, 0, { mb := some mb }, [], {}⟩

/-- **Module `i`'s view.** -/
def Store.view (S : Store) (i : Nat) : FEnv := viewOf (S.mb i)

/-- Module `h`'s unit. -/
def Store.slot (S : Store) (h : Nat) : ModSlot := ((S.slots[h]?).map Thunk.get).getD {}

/-! ## Presentations -/

/-- Is `n` a pinned name (`Modular.pinnedNames`). -/
def isPinned (n : Name) : Bool := ConLeche.Modular.pinnedNames.contains n

/-- The assumption of a constant's statement. -/
def asAxiom (ci : ConstantInfo) : ConstantInfo := .axiomInfo ci.toConstantVal

/-- Can `ci` be presented as the assumption of its statement
(`Modular.Refines`): a definition, theorem or assumption at a name that
is not pinned. -/
def hideable (ci : ConstantInfo) : Bool :=
  !isPinned ci.name && match ci with
    | .defnInfo .. | .thmInfo _ | .axiomInfo _ => true
    | _ => false

/-- **The exported presentation of a constant**: nothing, the constant
with its value hidden (`some false`), or the constant (`some true`). -/
def at1Of (pres : Option Bool) (ci : ConstantInfo) : Option ConstantInfo :=
  match pres with
  | none => none
  | some full => if full then some ci else some (asAxiom ci)

/-! ## What a constant's laws read -/

/-- The names a literal's checks read. -/
def natLitDeps : List Name := [natName, natZeroName, natSuccName]
def strLitDeps : List Name :=
  natLitDeps ++ [stringName, stringOfListName, listName, listNilName, listConsName, charName,
    charOfNatName]

/-- The constants of a list of expressions (and the literal
dependencies `Expr.constsResolve` reads), each node visited once.  An
oracle: what it returns is verified (`lawsOk`). -/
partial def collectGo (stack : List Expr) (seen : Std.HashSet Expr) (out : Std.HashSet Name) :
    Std.HashSet Name :=
  match stack with
  | [] => out
  | e :: rest =>
    match e with
    | .const n _ => collectGo rest seen (out.insert n)
    | .lit (.natVal _) => collectGo rest seen (natLitDeps.foldl (·.insert ·) out)
    | .lit (.strVal _) => collectGo rest seen (strLitDeps.foldl (·.insert ·) out)
    | .bvar _ | .sort _ => collectGo rest seen out
    | _ =>
      if seen.contains e then collectGo rest seen out
      else
        let seen := seen.insert e
        match e with
        | .app f a => collectGo (f :: a :: rest) seen out
        | .lam t b | .forallE t b => collectGo (t :: b :: rest) seen out
        | .letE t v b => collectGo (t :: v :: b :: rest) seen out
        | .proj sn _ x => collectGo (x :: rest) seen (out.insert sn)
        | .fvar _ t => collectGo (t :: rest) seen out
        | _ => collectGo rest seen out

/-- **What a presented constant's laws read** (`Modular.EntryScoped`):
its expressions and its names — its type, a definition's value, a
recursor's rules (right-hand sides, nested pins, constructors), an
inductive type's members, constructors, η constructor and projection
table (`tbl`), the names a pinned constant's fast path reads. -/
def lawsOf (tbl : Option ProjTable) (ci : ConstantInfo) : List Expr × List Name :=
  let pinN := ConLeche.Modular.pinFootprint ci.name
  let tblPart : List Expr × List Name := match ci with
    | .indInfo .. => match tbl with
      | some t => (t.bodies.toList, [t.ctor])
      | none => ([], [])
    | _ => ([], [])
  let (es, ns) : List Expr × List Name := match ci with
    | .defnInfo cv v _ => ([cv.type, v], [])
    | .recInfo cv _ _ rules =>
      (cv.type :: rules.flatMap (fun r => r.rhs :: match r.fire with
        | .nested _ pins => pins
        | .plain => []), rules.map (·.ctor))
    | .indInfo cv caps =>
      ([cv.type], caps.all ++ caps.ctors ++ (if caps.eta then [caps.etaCtor] else []))
    | ci => ([ci.toConstantVal.type], [])
  (es ++ tblPart.1, ns ++ tblPart.2 ++ pinN)

/-- The names of a list, as a lookup index (a constant of no meaning
under each): `(dvOf D).find? n` is some exactly at the names of `D`. -/
def dvOf (D : Array Name) : FEnv :=
  ⟨⟨[], []⟩, D.foldl (fun m n => m.insert n (0, .axiomInfo ⟨n, [], .sort .zero⟩)) {}, 1, {}, [],
    {}⟩

/-- **Every name the laws read is in `D`**: the checker's own resolution
walk over each expression, a lookup for each name. -/
def lawsOk (D : Array Name) (l : List Expr × List Name) : Bool :=
  let dv := dvOf D
  l.1.all (constsResolveFC dv) && l.2.all fun n => (dv.find? n).isSome

/-! ## Qualified names -/

/-- The alternates of a name in the store. -/
def Store.alts (S : Store) (n : Name) : List (Nat × Nat) := (S.mb 0).alts n

/-- The qualified name a unit's constant `j` of module `h` has. -/
def keyOfSlot (s : ModSlot) (h j : Nat) (n : Name) : ConLeche.Modular.Key :=
  match s.prf[j]?, s.priv[j]? with
  | some true, some ci => .proof n ci.toConstantVal.levelParams ci.toConstantVal.type
  | _, _ => .qual h n

/-- **The qualified name of module `h`'s constant `j`**, stored under `n`:
its statement for a proof, its home and name otherwise. -/
def Store.keyAt (S : Store) (h j : Nat) (n : Name) : ConLeche.Modular.Key :=
  keyOfSlot (S.slot h) h j n

/-- The qualified name module `i` resolves `n` to through its context. -/
def Store.keyIn (S : Store) (i : Nat) (n : Name) : Option ConLeche.Modular.Key :=
  match (S.mb i).pick? n with
  | some (h, j, _) => some (S.keyAt h j n)
  | none => none

/-! ## A module's unit -/

/-- **A module's unit, with what its importers must check**: `fp1`, the
modules, with levels, that the constants presented at the exported level
read and every importer at that level loads (Lean's rules guarantee
them, the importer checks them). -/
structure Unit' where
  slot : ModSlot := {}
  fp1 : Array (Nat × UInt8) := #[]
  deriving Inhabited

/-- The names a unit's presentations read, claimed (an oracle that
`unitOk` verifies): all names the installed constants read (`all2`),
the names the ungated exported constants read (`all1`), and for each
gated constant its type-level and its value reads. -/
structure Reads where
  all2 : Array Name := #[]
  all1 : Array Name := #[]
  gated : Array (Nat × Array Name × Array Name) := #[]
  deriving Inhabited

/-- A read's target as module `h` resolves it: its own constant at its
counter, or the context's alternate. -/
def target (h : Nat) (fe : FEnv) (d : Name) : Option (Nat × Nat) :=
  match fe.idx[d]? with
  | some (c, _) => if c < fe.visibleBelow then some (h, c) else none
  | none => match fe.base.mb with
    | some mb => (mb.pick? d).map fun (h', j', _) => (h', j')
    | none => none

/-- The level an importer needs at module `h` to see its constant `j`. -/
def Store.needAt (S : Store) (h j : Nat) : UInt8 :=
  match (S.slot h).at1[j]? with
  | some (some _) => 1
  | _ => 2

/-- The gate of module `h`'s exported constant `j`. -/
def Store.gateAt (S : Store) (h j : Nat) : Array (Nat × UInt8) :=
  ((S.slot h).g1[j]?).getD #[]

/-- **The unit's shape**: the arrays aligned with the installed constants;
each exported presentation the constant, or its assumption where that
refines it; a value gate only on a presented definition; the proofs the
module's; a structure's table its own. -/
def shapeOk (fe : FEnv) (flagged : Name → Bool) (s : ModSlot) : Bool :=
  s.priv.size == s.at1.size && s.priv.size == s.tbls.size && s.priv.size == s.g1.size &&
  s.priv.size == s.v1.size && s.priv.size == s.prf.size &&
  (List.range s.priv.size).all fun j =>
    match s.priv[j]?, s.at1[j]?, s.v1[j]?, s.prf[j]?, s.tbls[j]? with
    | some ci, some a, some v, some p, some t =>
      (match a with
        | none => true
        | some a => a == ci || (a == asAxiom ci && hideable ci)) &&
      (v.isEmpty || (a == some ci && hideable ci && (match ci with
        | .defnInfo .. => true
        | _ => false))) &&
      p == flagged ci.name &&
      t == fe.env.tables.find? (·.structName == ci.name)
    | _, _, _, _, _ => false

/-- A read at the private level: it resolves in the module, and the
module's own constant is the store's alternate there. -/
def read2Ok (S : Store) (h : Nat) (fe : FEnv) (d : Name) : Bool :=
  match target h fe d with
  | some (h', j') => h' != h || (S.alts d).contains (h', j')
  | none => false

/-- A read at the exported level of a constant whose gate is `G`: it
resolves in the module, and its target is presented at the exported
level to every viewer that loads `fp1` and `G` — its module and level are
in them, and so is its gate; an own target is the store's alternate,
itself presented. -/
def read1Ok (S : Store) (h : Nat) (fe : FEnv) (u : Unit') (G : Array (Nat × UInt8))
    (d : Name) : Bool :=
  let inG (p : Nat × UInt8) : Bool := u.fp1.contains p || G.contains p
  match target h fe d with
  | some (h', j') =>
    if h' == h then
      (S.alts d).contains (h', j') && ((u.slot.at1[j']?).join).isSome &&
        ((u.slot.g1[j']?).getD #[]).all inG
    else
      inG (h', S.needAt h' j') && (S.needAt h' j' != 1 || (S.gateAt h' j').all inG)
  | none => false

/-- **The check of a unit** against its module's final view `fe`: its
shape, and every name its presentations' laws read, as `Reads` claims
them (verified: `lawsOk`), read as `read2Ok`/`read1Ok` require. -/
def unitOk (S : Store) (h : Nat) (fe : FEnv) (flagged : Name → Bool) (u : Unit') (r : Reads) :
    Bool :=
  let s := u.slot
  shapeOk fe flagged s &&
  -- the private level
  (List.range s.priv.size).all (fun j => match s.priv[j]?, s.tbls[j]? with
    | some ci, some t => lawsOk r.all2 (lawsOf t ci)
    | _, _ => false) &&
  r.all2.all (read2Ok S h fe) &&
  -- the exported level, ungated
  (List.range s.priv.size).all (fun j => match s.at1[j]?, s.g1[j]?, s.v1[j]?, s.tbls[j]? with
    | some (some ci), some g, some v, some t =>
      !(g.isEmpty && v.isEmpty) || lawsOk r.all1 (lawsOf t ci)
    | _, _, _, _ => true) &&
  r.all1.all (read1Ok S h fe u #[]) &&
  -- the exported level, gated: every gated constant listed, with its reads
  (List.range s.priv.size).all (fun j => match s.at1[j]?, s.g1[j]?, s.v1[j]?, s.tbls[j]? with
    | some (some ci), some g, some v, some t =>
      (g.isEmpty && v.isEmpty) || r.gated.any fun (j', dt, dv) =>
        j' == j &&
        lawsOk dt (lawsOf t (if v.isEmpty then ci else asAxiom ci)) &&
        dt.all (read1Ok S h fe u g) &&
        (v.isEmpty || (lawsOk (dt ++ dv) (lawsOf t ci) &&
          dv.all (read1Ok S h fe u (g ++ v))))
    | _, _, _, _ => true)

/-! ## The local checks -/

/-- The level at `h` of a level array. -/
@[inline] def lvlAt (l : ByteArray) (h : Nat) : UInt8 := if hh : h < l.size then l[h] else 0

/-- **The copies of a name that meet in module `m`'s context have one
qualified name**: every alternate `m` sees has the qualified name of the
first.  (Lean merges such copies only when they are proofs of one
statement, whose qualified name is the statement.) -/
def oneKey (S : Store) (m : Nat) (n : Name) : Bool :=
  let mb := S.mb m
  let vis := (mb.alts n).filter fun (h, j) => match mb.at? h j with
    | some ci => ci.name == n
    | none => false
  match vis with
  | [] => true
  | (h₀, j₀) :: rest => rest.all fun (h, j) => S.keyAt h j n == S.keyAt h₀ j₀ n

/-- **The names with several alternates are listed** (`Store.dups`): a
name the store's index gives two alternates is in the list. -/
def dupsOk (S : Store) : Bool :=
  S.idx.all fun m => m.toList.all fun (n, l) => l.length < 2 || S.dups.contains n

/-- **Module `m`'s local checks** against the units of its context: every
module it loads is earlier and loaded at level 1 or 2; a module loaded
at its private level brings its whole context (`m` loads every module of
that context at least as high); one loaded at its exported level brings
the modules its presentation reads (`fp1`); and the copies of a name that
meet in `m`'s context have one qualified name (`oneKey`). -/
def localOk (S : Store) (units : Array Unit') (m : Nat) : Bool :=
  let lv := S.lvl m
  ((List.range lv.size).all fun h =>
    let l := lvlAt lv h
    l == 0 || (h < m && l ≤ 2 &&
      match units[h]? with
      | some u =>
        if l == 2 then
          let lh := S.lvl h
          (List.range lh.size).all (fun x => lvlAt lh x ≤ lvlAt lv x)
        else
          u.fp1.all (fun (x, need) => lvlAt lv x ≥ need)
      | none => false)) &&
  S.dups.all (oneKey S m)

end ConLeche.Cached.Mod
