module

public import ConLeche.Frontend.Olean.Levels
public import ConLeche.Frontend.Olean.Merge

@[expose] public section

/-!
# Reading `.olean` files: the names a module's environment holds

What a worker reads of the modules its header loads (`headerFixpoint`) before its own
records: every loaded part's name table (`readNamePositions f level`: names, kinds,
positions, no expression), indexed by name, and the two checks Lean's import and
kernel make over the whole loaded environment:

* **the clash rule** (`finalizeImport`): two modules' copies of one name are merged
  by `subsumesInfo` (`subsumesF`), the later replacing the earlier when it subsumes it;
  otherwise the module is rejected (exit 1).  Only the doubly held names' statements
  and kinds are read (`readStmts`, `readKinds`), and kept: the key check of the reach
  compares them (DESIGN #460 §2).
* **freshness**: no constant of the module's own private part bears a loaded name (Lean's
  kernel refuses to declare one twice; exit 1).

One departure from `finalizeImport`, never a reject Lean does not make: `isPropCheap`
(the axiom/axiom arm) looks the head constant up in the whole index, where Lean
looks in the constants loaded so far, so a pair whose head comes later in the order
is merged here and refused by Lean.  Both copies are then propositions, so the
merge is still sound.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- **A copy of a loaded name**: the module (its position in the load order) and the
constant's position among that module's name positions. -/
structure Copy where
  mod : Nat
  pos : Nat
  deriving Inhabited, BEq, Hashable, Repr

/-- **The name index** of the loaded parts. -/
structure NameIndex where
  /-- by position in the load order: the loaded part's name positions -/
  parts : Array NamePositions
  /-- each loaded name's first copy in the load order -/
  first : Std.HashMap Name Copy
  /-- every later copy, in the load order -/
  more : Array (Name × Copy)

/-- The name position of a copy. -/
def NameIndex.at (ix : NameIndex) (c : Copy) : Option NamePosition :=
  (ix.parts[c.mod]?).bind (·.consts[c.pos]?)

/-- **The index of some modules' name positions**, in their order. -/
def nameIndexOf (parts : Array NamePositions) : NameIndex :=
  let total := parts.foldl (fun n p => n + p.consts.size) 0
  let (first, more, _) := parts.foldl (fun (acc : Std.HashMap Name Copy × Array (Name × Copy) × Nat) p =>
    let (first, more, i) := acc
    let (first, more, _) := p.consts.foldl (fun (acc : Std.HashMap Name Copy × Array (Name × Copy) × Nat) q =>
      let (first, more, k) := acc
      match first[q.name]? with
      | none => (first.insert q.name ⟨i, k⟩, more, k + 1)
      | some _ => (first, more.push (q.name, ⟨i, k⟩), k + 1)) (first, more, 0)
    (first, more, i + 1)) (Std.HashMap.emptyWithCapacity total, #[], 0)
  { parts, first, more }

/-- **A name two loaded modules hold**: its copies in the load order, each with its
statement and its kind (expressions left out). -/
structure Clash where
  name : Name
  copies : Array (Copy × ConstantVal × CKindF Name Unit)

/-! ## Reading -/

/-- **The statements and kinds of some copies** of one module, read together. -/
def readInfosOf {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (ld : HeaderLoads) (ix : NameIndex)
    (x : Nat × Array Copy) : μ (Except CheckError (Array (Copy × ConstantVal × CKindF Name Unit))) := do
  let (i, cs) := x
  let m := (ld.order[i]?).getD .anonymous
  let level := ((ld.flags[i]?).getD default).level
  let locs := cs.toList.filterMap fun c => (ix.at c).map (·.loc)
  match ← rd.files m level with
  | .error e => pure (.error e)
  | .ok f =>
    match readStmts f level locs, readKinds f level locs with
    | some ss, some ks =>
      if ss.length == cs.size && ks.length == cs.size then
        pure (.ok ((cs.zip (ss.zip ks).toArray)))
      else pure (.error (undecodable m))
    | _, _ => pure (.error (undecodable m))

/-- Copies grouped by module, the modules ascending. -/
def byModule (cs : Array Copy) : Array (Nat × Array Copy) :=
  let m : Std.HashMap Nat (Array Copy) := cs.foldl (fun m c =>
    m.alter c.mod fun | none => some #[c] | some a => some (a.push c)) {}
  (m.toArray.qsort (·.1 < ·.1))

/-- **The statements and kinds of some copies**, module by module, in parallel. -/
def readInfos {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (ld : HeaderLoads) (ix : NameIndex)
    (jobs : Nat) (cs : Array Copy) :
    μ (Except CheckError (Std.HashMap Copy (ConstantVal × CKindF Name Unit))) := do
  match ← CheckerIO.parMapExcept jobs (readInfosOf rd ld ix) (byModule cs).toList with
  | .error e => pure (.error e)
  | .ok rs =>
    pure (.ok (rs.foldl (fun m r => r.foldl (fun m (c, s, k) => m.insert c (s, k)) m) {}))

/-! ## The checks -/

/-- A module's name for messages. -/
def HeaderLoads.nameAt (ld : HeaderLoads) (i : Nat) : Name := (ld.order[i]?).getD .anonymous

/-- **Lean's clash rule over one name's copies**, in the load order: the copy kept so far
and the next one, the next kept where it subsumes the kept one, the kept one staying where
it subsumes the next, a reject otherwise. -/
def clashOk (ld : HeaderLoads) (headTy : Name → Option Expr) (c : Clash) : Except CheckError Unit :=
  match c.copies.toList with
  | [] => pure ()
  | k :: rest =>
    let r : Except CheckError (Copy × ConstantVal × CKindF Name Unit) := rest.foldlM (fun (kept : Copy × ConstantVal × CKindF Name Unit) next =>
      let (_, cv₁, k₁) := next
      let (_, cv₂, k₂) := kept
      if subsumesF headTy cv₁ k₁ cv₂ k₂ then .ok next
      else if subsumesF headTy cv₂ k₂ cv₁ k₁ then .ok kept
      else .error (.invalid s!"modules {ld.nameAt kept.1.mod} and {ld.nameAt next.1.mod} \
        store different constants named {c.name}, and both are loaded")) k
    r.map fun _ => ()

/-- **Freshness**: no constant of the module's own part bears a loaded name. -/
def freshOk (m : Name) (ld : HeaderLoads) (ix : NameIndex) (own : NamePositions) : Except CheckError Unit :=
  match own.consts.find? (ix.first.contains ·.name) with
  | none => pure ()
  | some q =>
    let src := ((ix.first[q.name]?).map fun c => ld.nameAt c.mod).getD .anonymous
    .error (.invalid s!"module {m} declares {q.name}, which the module {src} it loads stores")

/-- **Lean's refusal of a classic import from a module** (`importModulesCore`): every import
of a root of the module system is of the module system. -/
def importsModulesOk (m : Name) (isModule : Bool) (ld : HeaderLoads) (ix : NameIndex)
    (imports : Array ImportRec) : Except CheckError Unit :=
  if !isModule then pure () else
  match imports.find? fun i => match ld.index[i.module]? with
    | some k => !((ix.parts[k]?).any (·.header.isModule))
    | none => false with
  | some i => .error (.invalid s!"module {m} of the module system imports {i.module}, which is not")
  | none => pure ()

/-! ## The worker's reads -/

/-- **What a worker reads before its own records.** -/
structure WorkerReads where
  /-- the module's own private part's name positions and header -/
  own : NamePositions
  /-- what Lean loads for it -/
  loads : HeaderLoads
  /-- each loaded module's public-import closure -/
  pub : Array ModSet
  /-- the loaded parts' names -/
  index : NameIndex
  /-- every name two loaded modules hold, its copies merged by Lean's rule -/
  clashes : Array Clash

/-- The doubly held names, each with all its copies, in the load order. -/
def clashCopies (ix : NameIndex) : Array (Name × Array Copy) :=
  let m : Std.HashMap Name (Array Copy) := ix.more.foldl (fun m (n, c) =>
    m.alter n fun
      | none => some #[(ix.first[n]?).getD c, c]
      | some a => some (a.push c)) {}
  m.toArray

/-- **A worker's own part with imports added** (a compared challenge's, task #608): the
header's imports followed by `x`, and no constant of its own, so that none of its names is
checked fresh.  Without imports to add, the part itself. -/
def NamePositions.withImports (own : NamePositions) (x : Array ImportRec) : NamePositions :=
  if x.isEmpty then own
  else { header := { own.header with imports := own.header.imports ++ x }, consts := #[] }

/-- **Phases 1 and 2 of a worker at module `m`** (DESIGN #460 §3): its own part's header
and names; the header fixpoint; each loaded module's public-import closure; the name
index of the loaded parts (read in parallel, at most `jobs` modules at once); Lean's
refusal of a classic import from a module, the clash rule over every loaded name and
freshness, each a reject (exit 1) naming what it found.  `x`: imports added to the header
(`NamePositions.withImports`; a compared challenge's solution, task #608). -/
def workerReads {μ : Type → Type} [CheckerIO μ] (rd : OleanReads μ) (m : Name) (jobs : Nat := 1)
    (x : Array ImportRec := #[]) : μ (Except CheckError WorkerReads) := do
  match ← rd.names (m, .private) with
  | .error e => pure (.error e)
  | .ok own =>
    let own := own.withImports x
    match ← headerFixpoint rd.imports own.header.isModule own.header.imports with
    | .error e => pure (.error e)
    | .ok ld =>
      let xs := (ld.order.zip ld.flags).toList.map fun (n, fl) => (n, fl.level)
      match ← CheckerIO.parMapExcept jobs rd.names xs with
      | .error e => pure (.error e)
      | .ok parts =>
        let ix := nameIndexOf parts.toArray
        match importsModulesOk m own.header.isModule ld ix own.header.imports with
        | .error e => pure (.error e)
        | .ok () =>
        let cc := clashCopies ix
        match ← readInfos rd ld ix jobs (cc.flatMap (·.2)) with
        | .error e => pure (.error e)
        | .ok infos =>
          let clashes : Array Clash := cc.map fun (n, cs) =>
            { name := n, copies := cs.filterMap fun c => (infos[c]?).map fun (s, k) => (c, s, k) }
          -- the heads `isPropCheap` asks the type of, at the axiom/axiom pairs
          let heads := clashes.foldl (fun (acc : Array Copy) cl =>
            match cl.copies[0]? with
            | some (_, cv, .ax _) =>
              match (isPropCheap.headOf cv.type).bind (ix.first[·]?) with
              | some c => acc.push c
              | none => acc
            | _ => acc) #[]
          match ← readInfos rd ld ix jobs heads with
          | .error e => pure (.error e)
          | .ok hinfos =>
            let headTy (n : Name) : Option Expr :=
              (ix.first[n]?).bind fun c => (hinfos[c]?).map (·.1.type)
            match clashes.toList.forM (clashOk ld headTy) with
            | .error e => pure (.error e)
            | .ok () =>
              match freshOk m ld ix own with
              | .error e => pure (.error e)
              | .ok () =>
                pure (.ok { own, loads := ld, pub := pubClosures ld, index := ix, clashes })

end ConLeche.Frontend.Olean
