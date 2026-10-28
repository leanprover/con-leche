module

import ConLeche.Cached.Installed
public import ConLeche.Modular
public import Std.Data.HashSet.Basic

@[expose] public section

/-!
# The module store and the bookkeeping of a modular run (tasks #370, #374)

A modular run (`ConLeche/Driver/Modular.lean`) checks every module on its
own.  Module `h`'s **unit** (`ModSlot`, `ConLeche/Kernel/FEnv.lean`) is
what it publishes for its importers, the counterpart of Lean's interface
files: its interface `exp` (each installed constant as an importer at the
exported level sees it — the constant, the assumption of its statement,
or nothing — with the **gates**: the modules, with levels, an importer
must load for that presentation; and `fp1`, what every importer loads by
Lean's rules) and its private record `prv` (the installed constants, for
`import all` importers, and the module's own levels).  This file holds
the pure part of the run that the proofs are about:

* `Store`, `Store.view` — the store mode's one store of all units with a
  name index, and a module's view of it;
* `UView` — what a module's bookkeeping reads of its context: the
  interfaces of the modules it loads and its context's lookup (from the
  store, `Store.uview`; from the units alone, `isoUView`,
  `ConLeche/Cached/ModIso.lean`);
* `unitOk` — the check of a unit against its module's own constants and
  its context: the presentations refine the installed constants, and
  every name their laws read (`lawsOf`, verified with the checker's own
  resolution walk `constsResolveFC` against the claimed set) resolves in
  the module, and its module and level are in `fp1` or the constant's
  gate;
* `levelsOk`, `localOk` — module `m`'s local checks against the units of
  what it loads: every module it loads is earlier, a module loaded
  privately brings its whole context, one loaded at the exported level
  brings `fp1`; in the store mode with the store's duplicates' check
  (`oneKey`; the isolated mode's is `keysOk`).

Nothing here type-checks: the declarations' checks are the fold's own
(`installDeclStep`, `checkPending`).
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

/-! ## Keys -/

/-- The alternates of a name in the store. -/
def Store.alts (S : Store) (n : Name) : List (Nat × Nat) := (S.mb 0).alts n

/-! ## The name index lists every unit constant -/

/-- Pairs in strictly increasing lexicographic order. -/
def sortedLex : List (Nat × Nat) → Bool
  | a :: b :: rest => (a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) && sortedLex (b :: rest)
  | _ => true

/-- **The store's name index lists every unit constant under its name,
in module order**: every alternate list strictly increasing, and every
constant of every unit — of its private record, and every exported
presentation — an alternate of its name. -/
def idxOk (S : Store) : Bool :=
  S.idx.all (fun m => m.toList.all fun (_, l) => sortedLex l) &&
  (List.range S.slots.size).all fun h =>
    (List.range (S.slot h).prv.priv.size).all (fun j => match (S.slot h).prv.priv[j]? with
      | some c => (S.alts c.name).contains (h, j)
      | none => true) &&
    (List.range (S.slot h).exp.at1.size).all (fun j => match ((S.slot h).exp.at1[j]?).join with
      | some c => (S.alts c.name).contains (h, j)
      | none => true)

/-- **The key a unit's constant `j` of module `h` has**: a
proof's is its statement, read off its exported presentation (the
constant or the assumption of its statement: the same statement); only
a proof the exported part does not present — which only a viewer
loading `h` with `import all` sees — reads the private record. -/
def keyOfSlot (s : ModSlot) (h j : Nat) : ConLeche.Modular.Key ConLeche.Modular.Stmt :=
  match s.exp.prf[j]? with
  | some true =>
    match (s.exp.at1[j]?).join with
    | some ci => .proof (ci.toConstantVal.levelParams, ci.toConstantVal.type)
    | none =>
      match s.prv.priv[j]? with
      | some ci => .proof (ci.toConstantVal.levelParams, ci.toConstantVal.type)
      | none => .home h
  | _ => .home h

/-- **The key of module `h`'s constant `j`**: its statement for a
proof, its home otherwise. -/
def Store.keyAt (S : Store) (h j : Nat) : ConLeche.Modular.Key ConLeche.Modular.Stmt :=
  keyOfSlot (S.slot h) h j

/-! ## What a module's bookkeeping reads of its context -/

/-- **What a module's bookkeeping reads of its context** (task #374): the
interfaces of the modules it loads (`iface`; what it holds for a module
it does not load is never read) and its context's lookup (`look`: a
name's constant in the context, with the module it is presented from and
its position in that module's unit).  A store run reads both off the
store (`Store.uview`); an isolated run builds them from the loaded units
alone (`isoUView`, `ConLeche/Cached/ModIso.lean`). -/
structure UView where
  iface : Nat → ModIface
  look : Name → Option (Nat × Nat × ConstantInfo)

/-- **Module `h`'s view of the store**, for its bookkeeping. -/
def Store.uview (S : Store) (h : Nat) : UView := ⟨fun h' => (S.slot h').exp, (S.mb h).pick?⟩

/-- A name's constant in a module's environment: its own (`fe`), else its
context's. -/
def findIn (fe : FEnv) (U : UView) (n : Name) : Option ConstantInfo :=
  match fe.find? n with
  | some c => some c
  | none => (U.look n).map (·.2.2)

/-! ## A module's unit -/

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
counter, or the context's presentation. -/
def target (h : Nat) (fe : FEnv) (U : UView) (d : Name) : Option (Nat × Nat) :=
  match fe.idx[d]? with
  | some (c, _) => if c < fe.visibleBelow then some (h, c) else none
  | none => (U.look d).map fun (h', j', _) => (h', j')

/-- The level an importer needs at module `h` to see its constant `j`. -/
def UView.needAt (U : UView) (h j : Nat) : UInt8 :=
  match (U.iface h).at1[j]? with
  | some (some _) => 1
  | _ => 2

/-- The gate of module `h`'s exported constant `j`. -/
def UView.gateAt (U : UView) (h j : Nat) : Array (Nat × UInt8) :=
  ((U.iface h).g1[j]?).getD #[]

/-- The full gate of module `h`'s exported constant `j`. -/
def UView.fullGateAt (U : UView) (h j : Nat) : Array (Nat × UInt8) :=
  ((U.iface h).g1[j]?).getD #[] ++ ((U.iface h).v1[j]?).getD #[]

/-- Is module `h`'s constant `j` presented as stored at the exported
level. -/
def UView.storedAt (U : UView) (h j : Nat) : Bool := ((U.iface h).stored[j]?).getD false

/-- Is a constant of a kind that can be a proof (a theorem, a definition,
an assumption). -/
def proofKind : ConstantInfo → Bool
  | .defnInfo .. | .thmInfo _ | .axiomInfo _ => true
  | _ => false

/-- **The unit's shape**: the arrays aligned with the installed constants;
each exported presentation the constant, or its assumption where that
refines it; a value gate only on a presented definition; the proofs the
module's; a structure's table its own. -/
def shapeOk (fe : FEnv) (flagged : Name → Bool) (s : ModSlot) : Bool :=
  let e := s.exp
  let p := s.prv
  p.priv.size == e.at1.size && p.priv.size == p.tbls.size && p.priv.size == e.g1.size &&
  p.priv.size == e.v1.size && p.priv.size == e.prf.size && p.priv.size == e.stored.size &&
  p.priv.size == e.tbls.size &&
  (List.range p.priv.size).all fun j =>
    match p.priv[j]?, e.at1[j]?, e.v1[j]?, e.prf[j]?, p.tbls[j]?, e.stored[j]?, e.tbls[j]? with
    | some ci, some a, some v, some pf, some t, some st, some et =>
      (match a with
        | none => true
        | some a => a == ci || (a == asAxiom ci && hideable ci)) &&
      st == (a == some ci) &&
      (v.isEmpty || (st && hideable ci)) &&
      pf == flagged ci.name && (!pf || proofKind ci) &&
      t == fe.env.tables.find? (·.structName == ci.name) &&
      et == (if st then t else none)
    | _, _, _, _, _, _, _ => false

/-- The kind a full read requires. -/
inductive Want where
  | ind | ctor

def Want.ok : Want → ConstantInfo → Bool
  | .ind, .indInfo .. => true
  | .ctor, .ctorInfo .. => true
  | _, _ => false

/-- A read at the private level: it resolves in the module. -/
def read2Ok (U : UView) (h : Nat) (fe : FEnv) (d : Name) : Bool :=
  (target h fe U d).isSome

/-- A full read at the private level: it resolves in the module, and the
target is presented as stored, of the wanted kind. -/
def full2Ok (U : UView) (h : Nat) (fe : FEnv) (s : ModSlot) (w : Want) (d : Name) : Bool :=
  match target h fe U d with
  | some (h', j') =>
    if h' == h then ((s.prv.priv[j']?).map w.ok).getD false
    else match U.look d with
      | some (_, _, ci) => w.ok ci
      | none => false
  | none => false

/-- A read at the exported level of a constant whose gate is `G`: it
resolves in the module, and its target is presented at the exported
level to every viewer that loads `fp1` and `G` — its module and level are
in them, and so is its gate; an own target is itself presented. -/
def read1Ok (U : UView) (h : Nat) (fe : FEnv) (s : ModSlot) (G : Array (Nat × UInt8))
    (d : Name) : Bool :=
  let inG (p : Nat × UInt8) : Bool := s.exp.fp1.contains p || G.contains p
  match target h fe U d with
  | some (h', j') =>
    if h' == h then
      ((s.exp.at1[j']?).join).isSome && ((s.exp.g1[j']?).getD #[]).all inG
    else
      inG (h', U.needAt h' j') && (U.needAt h' j' != 1 || (U.gateAt h' j').all inG)
  | none => false

/-- A full read at the exported level: the target is presented as stored,
of the wanted kind, to every viewer that loads `fp1` and `G`. -/
def full1Ok (U : UView) (h : Nat) (fe : FEnv) (s : ModSlot) (G : Array (Nat × UInt8)) (w : Want)
    (d : Name) : Bool :=
  let inG (p : Nat × UInt8) : Bool := s.exp.fp1.contains p || G.contains p
  match target h fe U d with
  | some (h', j') =>
    if h' == h then
      ((s.exp.stored[j']?).getD false) && ((s.prv.priv[j']?).map w.ok).getD false &&
        (((s.exp.g1[j']?).getD #[]) ++ ((s.exp.v1[j']?).getD #[])).all inG
    else
      match U.look d with
      | some (_, _, ci) =>
        w.ok ci &&
        (if U.storedAt h' j' then inG (h', 1) && (U.fullGateAt h' j').all inG
         else inG (h', 2))
      | none => false
  | none => false

/-- The read checks of a read set, with gate `G` at the exported level
(`lvl2`: at the private level). -/
def readsOk (U : UView) (h : Nat) (fe : FEnv) (s : ModSlot) (lvl2 : Bool) (G : Array (Nat × UInt8))
    (r : ReadSet) : Bool :=
  r.d.toList.all (fun (d, _) => if lvl2 then read2Ok U h fe d else read1Ok U h fe s G d) &&
  r.fi.toList.all (fun d => if lvl2 then full2Ok U h fe s .ind d else full1Ok U h fe s G .ind d) &&
  r.fc.toList.all (fun d => if lvl2 then full2Ok U h fe s .ctor d else full1Ok U h fe s G .ctor d)

/-- **A recursor's rules are of constructors of stored type formers**, in
the module's own environment (`Modular.LocalOk.recFam`; `find` its
lookup). -/
def recFamOk (find : Name → Option ConstantInfo) (ci : ConstantInfo) : Bool :=
  match ci with
  | .recInfo _ _ _ rules => rules.all fun r => match find r.ctor with
    | some (.ctorInfo cvj _ _) => match cvj.type.piResult.getAppFn with
      | .const T _ => match find T with
        | some (.indInfo ..) => true
        | _ => false
      | _ => true
    | _ => true
  | _ => true

/-- **The check of a unit** (`s`) against its module's own constants
(`fe`) and its context (`U`): its shape; its recursors' families; every
name its presentations' laws read, as `Reads` claims them (verified:
`lawsOk`), read as the read checks require. -/
def unitOk (U : UView) (h : Nat) (fe : FEnv) (flagged : Name → Bool) (s : ModSlot) (r : Reads) :
    Bool :=
  shapeOk fe flagged s &&
  s.prv.priv.all (recFamOk (findIn fe U)) &&
  -- the private level
  (List.range s.prv.priv.size).all (fun j => match s.prv.priv[j]?, s.prv.tbls[j]? with
    | some ci, some t => lawsOk r.all2 (lawsOf t ci)
    | _, _ => false) &&
  readsOk U h fe s true #[] r.all2 &&
  -- the exported level, ungated
  (List.range s.prv.priv.size).all (fun j =>
    match s.exp.at1[j]?, s.exp.g1[j]?, s.exp.v1[j]?, s.exp.tbls[j]? with
    | some (some ci), some g, some v, some t =>
      !(g.isEmpty && v.isEmpty) || lawsOk r.all1 (lawsOf t ci)
    | _, _, _, _ => true) &&
  readsOk U h fe s false #[] r.all1 &&
  -- the exported level, gated: every gated constant listed, with its reads
  (List.range s.prv.priv.size).all (fun j =>
    match s.exp.at1[j]?, s.exp.g1[j]?, s.exp.v1[j]?, s.exp.tbls[j]? with
    | some (some ci), some g, some v, some t =>
      (g.isEmpty && v.isEmpty) || r.gated.any fun (j', rt, rf) =>
        j' == j &&
        lawsOk rt (lawsOf t (if v.isEmpty then ci else asAxiom ci)) &&
        readsOk U h fe s false g rt &&
        (v.isEmpty || (lawsOk rf (lawsOf t ci) && readsOk U h fe s false (g ++ v) rf))
    | _, _, _, _ => true)

/-! ## The local checks -/

/-- The level at `h` of a level array. -/
@[inline] def lvlAt (l : ByteArray) (h : Nat) : UInt8 := if hh : h < l.size then l[h] else 0

/-- **Module `m`'s levels against the units of what it loads**: every
module it loads is earlier and loaded at level 1 or 2; a module loaded
at its private level brings its whole context (`m` loads every module of
that context at least as high, by that module's own levels `prv.lvl`);
one loaded at its exported level brings the modules its presentation
reads (`fp1`).  `unit h` is read only for a module `m` loads, its
private record only for one it loads privately. -/
def levelsOk (m : Nat) (lv : ByteArray) (unit : Nat → ModSlot) : Bool :=
  (List.range lv.size).all fun h =>
    let l := lvlAt lv h
    l == 0 || (h < m && l ≤ 2 &&
      if l == 2 then
        let lh := (unit h).prv.lvl
        (List.range lh.size).all (fun x => lvlAt lh x ≤ lvlAt lv x)
      else
        (unit h).exp.fp1.all (fun (x, need) => lvlAt lv x ≥ need))

/-- **The copies of a name that meet in module `m`'s context have one
key**: every alternate `m` sees has the key of the
first.  (Lean merges such copies only when they are proofs of one
statement, whose key is the statement.) -/
def oneKey (S : Store) (m : Nat) (n : Name) : Bool :=
  let mb := S.mb m
  let vis := (mb.alts n).filter fun (h, j) => match mb.at? h j with
    | some ci => ci.name == n
    | none => false
  match vis with
  | [] => true
  | (h₀, j₀) :: rest => rest.all fun (h, j) => S.keyAt h j == S.keyAt h₀ j₀

/-- **The names with several alternates are listed** (`Store.dups`): a
name the store's index gives two alternates is in the list. -/
def dupsOk (S : Store) : Bool :=
  S.idx.all fun m => m.toList.all fun (n, l) => l.length < 2 || S.dups.contains n

/-- **Module `m`'s local checks in a store run**: its levels against the
units of what it loads (`levelsOk`, every module's own levels the
store's), and the copies of a name that meet in `m`'s context have one
key (`oneKey`, over the store's names stored twice). -/
def localOk (S : Store) (m : Nat) : Bool :=
  levelsOk m (S.lvl m) S.slot && S.dups.all (oneKey S m)

/-! ## A module, checked -/

/-- **What a modular run keeps of a module**: its imports, its records,
its own constants' index at the end of its install with the records'
checks, its unit and proofs, and the reads its unit was checked
against. -/
structure ModData where
  imports : List Nat := []
  ds : Array Declaration := #[]
  fe : FEnv := mkFEnv Env.empty
  pend : Array PendingCheck := #[]
  unit : ModSlot := {}
  flags : Std.HashSet Name := {}
  reads : Reads := {}

end ConLeche.Cached.Mod
