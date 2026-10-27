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
(`Modular.Refines`): any constant at a name that is not pinned. -/
def hideable (ci : ConstantInfo) : Bool := !isPinned ci.name

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

/-- **What a presented constant's laws read** (`Modular.EntryScoped`,
`EntryProjs`, `BlockIn`): expressions whose constants must be present and
whose projections' structures stored type formers (`es`), names that
must be present (`ns`), stored as type formers (`fi`) or as constructors
(`fc`). -/
structure Laws where
  es : List Expr := []
  ns : List Name := []
  fi : List Name := []
  fc : List Name := []
  deriving Inhabited

/-- **The laws of a presented constant**: its type; a definition's value;
a recursor's rules (right-hand sides, nested pins, constructors); an
inductive type's members, constructors, η constructor and projection
table (`tbl`); a constructor's result family; and the names a pinned
constant's fast path reads. -/
def lawsOf (tbl : Option ProjTable) (ci : ConstantInfo) : Laws :=
  let pinN := ConLeche.Modular.pinFootprint ci.name
  match ci with
  | .defnInfo cv v _ => { es := [cv.type, v], ns := pinN }
  | .recInfo cv _ _ rules =>
    { es := cv.type :: rules.flatMap (fun r => r.rhs :: match r.fire with
        | .nested _ pins => pins
        | .plain => []),
      ns := rules.map (·.ctor) ++ pinN, fc := rules.map (·.ctor) }
  | .indInfo cv caps =>
    let cs := caps.ctors ++ (if caps.eta then [caps.etaCtor] else [])
    match tbl with
    | some t => { es := cv.type :: t.bodies.toList, ns := caps.all ++ cs ++ [t.ctor] ++ pinN,
                  fi := caps.all, fc := cs ++ [t.ctor] }
    | none => { es := [cv.type], ns := caps.all ++ cs ++ pinN, fi := caps.all, fc := cs }
  | .ctorInfo cv _ _ =>
    { es := [cv.type], ns := pinN,
      fi := match cv.type.piResult.getAppFn with
        | .const T _ => [T]
        | _ => [] }
  | ci => { es := [ci.toConstantVal.type], ns := pinN }

/-- **Every projection an expression reads is of a structure `P`
admits** (the specification; `projsInC` is its memoized walk). -/
def Expr.projsIn (P : Name → Bool) : Expr → Bool
  | .proj s _ e => P s && Expr.projsIn P e
  | .app f a => Expr.projsIn P f && Expr.projsIn P a
  | .lam ty b | .forallE ty b => Expr.projsIn P ty && Expr.projsIn P b
  | .letE ty v b => Expr.projsIn P ty && Expr.projsIn P v && Expr.projsIn P b
  | .fvar _ ty => Expr.projsIn P ty
  | _ => true

/-- The child step of `projsInXP`: the compound test, then the
exclusivity read (as `enterCRF`). -/
@[inline] def enterPI (P : Name → Bool) (e : @& Expr) (memo : Expr.MemoB0 (Expr.projsIn P))
    (rec : Unit → Squash (Expr.ResB0 (Expr.projsIn P) e)) :
    Squash (Expr.ResB0 (Expr.projsIn P) e) :=
  if !Expr.isCompoundF e then rec () else
  withExcl e fun excl =>
    if excl then rec () else memo.shared e fun _ => rec ()

/-- The walk of `projsInC`: one memoized DAG walk. -/
def projsInXP (P : Name → Bool) (memo : Expr.MemoB0 (Expr.projsIn P)) (e : @& Expr) :
    Squash (Expr.ResB0 (Expr.projsIn P) e) :=
  match e with
  | .bvar .. => Squash.mk (⟨true, by simp [Expr.projsIn]⟩, memo)
  | .sort .. => Squash.mk (⟨true, by simp [Expr.projsIn]⟩, memo)
  | .const .. => Squash.mk (⟨true, by simp [Expr.projsIn]⟩, memo)
  | .lit .. => Squash.mk (⟨true, by simp [Expr.projsIn]⟩, memo)
  | .fvar _ ty =>
    enterPI P ty memo (fun _ => projsInXP P memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    Squash.mk (⟨rt, by rw [Expr.projsIn, ← ht]⟩, memo)
  | .app f a =>
    enterPI P f memo (fun _ => projsInXP P memo f) |>.lift fun (⟨rf, hf⟩, memo) =>
    match rf, hf with
    | true, hf =>
      enterPI P a memo (fun _ => projsInXP P memo a) |>.lift fun (⟨ra, ha⟩, memo) =>
      Squash.mk (⟨ra, by rw [Expr.projsIn, ← hf, ← ha, Bool.true_and]⟩, memo)
    | false, hf => Squash.mk (⟨false, by rw [Expr.projsIn, ← hf, Bool.false_and]⟩, memo)
  | .lam ty body | .forallE ty body =>
    enterPI P ty memo (fun _ => projsInXP P memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterPI P body memo (fun _ => projsInXP P memo body) |>.lift fun (⟨rb, hb⟩, memo) =>
      Squash.mk (⟨rb, by rw [Expr.projsIn, ← ht, ← hb, Bool.true_and]⟩, memo)
    | false, ht => Squash.mk (⟨false, by rw [Expr.projsIn, ← ht, Bool.false_and]⟩, memo)
  | .letE ty val body =>
    enterPI P ty memo (fun _ => projsInXP P memo ty) |>.lift fun (⟨rt, ht⟩, memo) =>
    match rt, ht with
    | true, ht =>
      enterPI P val memo (fun _ => projsInXP P memo val) |>.lift fun (⟨rv, hv⟩, memo) =>
      match rv, hv with
      | true, hv =>
        enterPI P body memo (fun _ => projsInXP P memo body) |>.lift fun (⟨rb, hb⟩, memo) =>
        Squash.mk (⟨rb, by rw [Expr.projsIn, ← ht, ← hv, ← hb]; simp⟩, memo)
      | false, hv => Squash.mk (⟨false, by rw [Expr.projsIn, ← ht, ← hv]; simp⟩, memo)
    | false, ht => Squash.mk (⟨false, by rw [Expr.projsIn, ← ht]; simp⟩, memo)
  | .proj sn _ sub =>
    if hP : P sn = true then
      enterPI P sub memo (fun _ => projsInXP P memo sub) |>.lift fun (⟨rs, hs⟩, memo) =>
      Squash.mk (⟨rs, by rw [Expr.projsIn, ← hs, hP, Bool.true_and]⟩, memo)
    else Squash.mk (⟨false, by rw [Expr.projsIn]; simp [hP]⟩, memo)

/-- The memoized `Expr.projsIn P`. -/
def projsInC (P : Name → Bool) (e : Expr) : Bool := Expr.resBool (projsInXP P none e)

theorem projsInC_eq (P : Name → Bool) (e : Expr) : projsInC P e = Expr.projsIn P e :=
  Expr.resBool_eq _

/-- The structure names of a list of expressions' projections (an
oracle, verified by `projsInC`). -/
partial def collectProjs (stack : List Expr) (seen : Std.HashSet Expr) (out : Std.HashSet Name) :
    Std.HashSet Name :=
  match stack with
  | [] => out
  | e :: rest =>
    if !Expr.isCompoundF e then collectProjs rest seen out
    else if seen.contains e then collectProjs rest seen out
    else
      let seen := seen.insert e
      match e with
      | .app f a => collectProjs (f :: a :: rest) seen out
      | .lam t b | .forallE t b => collectProjs (t :: b :: rest) seen out
      | .letE t v b => collectProjs (t :: v :: b :: rest) seen out
      | .proj sn _ x => collectProjs (x :: rest) seen (out.insert sn)
      | .fvar _ t => collectProjs (t :: rest) seen out
      | _ => collectProjs rest seen out

/-- **A claimed set of reads** (an oracle's answer, verified by
`lawsOk` and the read checks): the names that must be present, as a
lookup index (`dvOf`: a name maps to a constant of no meaning at counter
`0`), and the names that must be stored type formers (`fi`) and stored
constructors (`fc`). -/
structure ReadSet where
  d : Std.HashMap Name (Nat × ConstantInfo) := {}
  fi : Std.HashSet Name := {}
  fc : Std.HashSet Name := {}
  deriving Inhabited

/-- The present names of a read set as an index: `(dvOf r).find? n` is
some only at its names. -/
def dvOf (r : ReadSet) : FEnv := ⟨⟨[], []⟩, r.d, 1, {}, [], {}⟩

/-- **Every name the laws read is in the read set**: the checker's own
resolution walk and the projection walk over each expression, a lookup
for each name. -/
def lawsOk (r : ReadSet) (l : Laws) : Bool :=
  let dv := dvOf r
  l.es.all (constsResolveFC dv) && l.es.all (projsInC r.fi.contains) &&
  l.ns.all (fun n => (dv.find? n).isSome) && l.fi.all r.fi.contains && l.fc.all r.fc.contains

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

/-- The reads a unit's presentations claim (verified by `unitOk`): of the
installed constants (`all2`), of the ungated exported presentations
(`all1`), and for each gated constant, of its presentation when its full
gate is closed and when it is open. -/
structure Reads where
  all2 : ReadSet := {}
  all1 : ReadSet := {}
  gated : Array (Nat × ReadSet × ReadSet) := #[]
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
      (v.isEmpty || (a == some ci && hideable ci)) &&
      p == flagged ci.name && (!p || (match ci with
        | .defnInfo .. | .thmInfo _ | .axiomInfo _ => true
        | _ => false)) &&
      t == fe.env.tables.find? (·.structName == ci.name)
    | _, _, _, _, _ => false

/-- The kind a full read requires. -/
inductive Want where
  | ind | ctor

def Want.ok : Want → ConstantInfo → Bool
  | .ind, .indInfo .. => true
  | .ctor, .ctorInfo .. => true
  | _, _ => false

/-- A read at the private level: it resolves in the module, and the
module's own constant is the store's alternate there. -/
def read2Ok (S : Store) (h : Nat) (fe : FEnv) (d : Name) : Bool :=
  match target h fe d with
  | some (h', j') => h' != h || (S.alts d).contains (h', j')
  | none => false

/-- A full read at the private level: as `read2Ok`, and the target is
presented as stored, of the wanted kind. -/
def full2Ok (S : Store) (h : Nat) (fe : FEnv) (u : Unit') (w : Want) (d : Name) : Bool :=
  match target h fe d with
  | some (h', j') =>
    if h' == h then (S.alts d).contains (h', j') && ((u.slot.priv[j']?).map w.ok).getD false
    else match fe.base.mb with
      | some mb => match mb.pick? d with
        | some (_, _, ci) => some ci == (S.slot h').priv[j']? && w.ok ci
        | none => false
      | none => false
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

/-- The full gate of module `h`'s exported constant `j`. -/
def Store.fullGateAt (S : Store) (h j : Nat) : Array (Nat × UInt8) :=
  ((S.slot h).g1[j]?).getD #[] ++ ((S.slot h).v1[j]?).getD #[]

/-- A full read at the exported level: the target is presented as stored,
of the wanted kind, to every viewer that loads `fp1` and `G`. -/
def full1Ok (S : Store) (h : Nat) (fe : FEnv) (u : Unit') (G : Array (Nat × UInt8)) (w : Want)
    (d : Name) : Bool :=
  let inG (p : Nat × UInt8) : Bool := u.fp1.contains p || G.contains p
  match target h fe d with
  | some (h', j') =>
    if h' == h then
      (S.alts d).contains (h', j') &&
        (match u.slot.priv[j']? with
          | some ci => (u.slot.at1[j']?) == some (some ci) && w.ok ci
          | none => false) &&
        (((u.slot.g1[j']?).getD #[]) ++ ((u.slot.v1[j']?).getD #[])).all inG
    else
      match (S.slot h').priv[j']? with
      | some ci =>
        w.ok ci &&
        (if (S.slot h').at1[j']? == some (some ci) then
          inG (h', 1) && (S.fullGateAt h' j').all inG
        else inG (h', 2))
      | none => false
  | none => false

/-- The read checks of a read set, with gate `G` at the exported level
(`lvl2`: at the private level). -/
def readsOk (S : Store) (h : Nat) (fe : FEnv) (u : Unit') (lvl2 : Bool) (G : Array (Nat × UInt8))
    (r : ReadSet) : Bool :=
  r.d.toList.all (fun (d, _) => if lvl2 then read2Ok S h fe d else read1Ok S h fe u G d) &&
  r.fi.toList.all (fun d => if lvl2 then full2Ok S h fe u .ind d else full1Ok S h fe u G .ind d) &&
  r.fc.toList.all (fun d => if lvl2 then full2Ok S h fe u .ctor d else full1Ok S h fe u G .ctor d)

/-- **A recursor's rules are of constructors of stored type formers**, in
the module's own environment (`Modular.LocalOk.recFam`). -/
def recFamOk (fe : FEnv) (ci : ConstantInfo) : Bool :=
  match ci with
  | .recInfo _ _ _ rules => rules.all fun r => match fe.find? r.ctor with
    | some (.ctorInfo cvj _ _) => match cvj.type.piResult.getAppFn with
      | .const T _ => match fe.find? T with
        | some (.indInfo ..) => true
        | _ => false
      | _ => true
    | _ => true
  | _ => true

/-- **The check of a unit** against its module's final view `fe`: its
shape; its recursors' families; every name its presentations' laws read,
as `Reads` claims them (verified: `lawsOk`), read as the read checks
require. -/
def unitOk (S : Store) (h : Nat) (fe : FEnv) (flagged : Name → Bool) (u : Unit') (r : Reads) :
    Bool :=
  let s := u.slot
  shapeOk fe flagged s &&
  s.priv.all (recFamOk fe) &&
  -- the private level
  (List.range s.priv.size).all (fun j => match s.priv[j]?, s.tbls[j]? with
    | some ci, some t => lawsOk r.all2 (lawsOf t ci)
    | _, _ => false) &&
  readsOk S h fe u true #[] r.all2 &&
  -- the exported level, ungated
  (List.range s.priv.size).all (fun j => match s.at1[j]?, s.g1[j]?, s.v1[j]?, s.tbls[j]? with
    | some (some ci), some g, some v, some t =>
      !(g.isEmpty && v.isEmpty) || lawsOk r.all1 (lawsOf t ci)
    | _, _, _, _ => true) &&
  readsOk S h fe u false #[] r.all1 &&
  -- the exported level, gated: every gated constant listed, with its reads
  (List.range s.priv.size).all (fun j => match s.at1[j]?, s.g1[j]?, s.v1[j]?, s.tbls[j]? with
    | some (some ci), some g, some v, some t =>
      (g.isEmpty && v.isEmpty) || r.gated.any fun (j', rt, rf) =>
        j' == j &&
        lawsOk rt (lawsOf t (if v.isEmpty then ci else asAxiom ci)) &&
        readsOk S h fe u false g rt &&
        (v.isEmpty || (lawsOk rf (lawsOf t ci) && readsOk S h fe u false (g ++ v) rf))
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
