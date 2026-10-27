import ConLeche.Frontend.Olean.Load
/- NOT a `module`, like `OleanCompare.lean`: a development tool. -/

/-!
# `olean-modular` — compatibility and summary sizes (task #370, measurement)

    lake exe olean-modular JOBS SEARCHPATH MODULE...

Loads the import closure of `MODULE...` at the private level (theorem
proofs are not decoded: the fragment stores a theorem as its statement)
and, for the names stored by several modules, at the exported level, and
reports (1) the duplicated names against the fragment's `Compatible`
and Lean's `subsumesInfo`, (2) the modules whose local check (own
declarations and the direct imports' summaries pairwise compatible)
fails, (3) the summary sizes and what each exported view hides.
A development tool, not a default target.
-/

open ConLeche ConLeche.Frontend ConLeche.Frontend.Olean

instance : Inhabited CEntry := ⟨{ name := .anonymous, levelParams := [], type := .bvar 0, kind := .ax false }⟩
instance : Inhabited Loaded := ⟨{ name := .anonymous, imports := #[], constants := #[] }⟩

/-! ## Loading -/

def loadPriv (sp : SearchPath) (m : Name) (ds : DS) :
    IO (Except CheckError (Loaded × DS)) := do
  let some dir ← findModule sp m
    | return .error (.internal s!"module {m}: no .olean on the search path")
  let ex ← match ← readPart (modFile dir m "olean") with
    | .ok p => pure p
    | .error e => return .error e
  let r0 := Region.single ex
  let isModule ← match (do
      let x ← r0.obj ex.root
      x.expect 0 5 "ModuleData"
      boolAt x 0 : Except String Bool) with
    | .ok b => pure b
    | .error e => return .error (.internal s!"module {m}: {e}")
  let (r, root) ← if isModule then do
      let sv ← readPart (modFile dir m "olean.server")
      let pv ← readPart (modFile dir m "olean.private")
      match sv, pv with
      | .ok s, .ok p =>
        match Region.ofParts #[ex, s, p] with
        | .ok r => pure (r, p.root)
        | .error e => return .error e
      | .error e, _ | _, .error e => return .error e
    else pure (r0, ex.root)
  let ds := ds.fresh r.words
  let act : DM Loaded := do
    let info ← moduleAt r root
    let cs ← info.constants.mapM fun v => constAt r v (skipThm := true)
    pure ⟨m, info.imports, cs⟩
  match act.run ds with
  | .ok (l, ds) => pure (.ok (l, ds))
  | .error e => pure (.error (.internal s!"module {m}: {e}"))

/-- The exported part alone (`.olean`). -/
def loadExp (sp : SearchPath) (m : Name) (ds : DS) :
    IO (Except CheckError (Array CEntry × DS)) := do
  let some dir ← findModule sp m
    | return .error (.internal s!"module {m}: no .olean on the search path")
  let ex ← match ← readPart (modFile dir m "olean") with
    | .ok p => pure p
    | .error e => return .error e
  let r := Region.single ex
  let ds := ds.fresh r.words
  let act : DM (Array CEntry) := do
    let info ← moduleAt r ex.root
    info.constants.mapM fun v => constAt r v (skipThm := true)
  match act.run ds with
  | .ok (l, ds) => pure (.ok (l, ds))
  | .error e => pure (.error (.internal s!"module {m}: {e}"))

/-- Run `f 0 … f (n-1)` on `jobs` workers (round-robin), results in order. -/
def parRun {α} (jobs n : Nat) (f : Nat → DS → IO (Except CheckError (α × DS))) :
    IO (Except CheckError (Array α)) := do
  let w := max 1 (min jobs n)
  let serial (ids : List Nat) : IO (Except CheckError (Array α)) := do
    let mut ds : DS := {}
    let mut out : Array α := #[]
    for i in ids do
      match ← f i ds with
      | .error e => return .error e
      | .ok (a, d) => ds := d; out := out.push a
    return .ok out
  let shares := (List.range w).map fun k => (List.range n).filter (· % w == k)
  let tasks ← shares.toArray.mapM fun ids => IO.asTask (prio := .dedicated) (serial ids)
  let mut parts : Array (Array α) := #[]
  for t in tasks do
    match ← IO.wait t with
    | .ok (.ok ls) => parts := parts.push ls
    | .ok (.error e) => return .error e
    | .error ioe => return .error (.internal s!"worker: {ioe}")
  let out := (List.range n).filterMap fun i => (parts[i % w]?).bind (·[i / w]?)
  pure (.ok out.toArray)

/-! ## Entries -/

def kn : CKind → String
  | .ax _ => "ax" | .defn .. => "defn" | .thm .. => "thm" | .opaq .. => "opaq"
  | .quot _ => "quot" | .induct .. => "induct" | .ctor .. => "ctor" | .recur .. => "recur"

def ruleEq : (Name × Nat × Expr) → (Name × Nat × Expr) → Bool
  | (a, b, c), (a', b', c') => a == a' && b == b' && c == c'

def listEq {α} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listEq f as bs
  | _, _ => false

/-- The fragment's equality of stored entries: a theorem is stored as its
statement, so equal to an axiom of the same statement. -/
def fragEq (a b : CEntry) : Bool :=
  a.name == b.name && a.levelParams == b.levelParams && a.type == b.type &&
  match a.kind, b.kind with
  | .ax _, .ax _ => true
  | .ax _, .thm .. => true
  | .thm .., .ax _ => true
  | .thm .., .thm .. => true
  | .defn v _ s, .defn w _ s' => v == w && s == s'
  | .opaq v u, .opaq w u' => v == w && u == u'
  | .quot k, .quot k' => k == k'
  | .induct p i al cs n r u rf, .induct p' i' al' cs' n' r' u' rf' =>
    p == p' && i == i' && al == al' && cs == cs' && n == n' && r == r' && u == u' && rf == rf'
  | .ctor ind c p f u, .ctor ind' c' p' f' u' =>
    ind == ind' && c == c' && p == p' && f == f' && u == u'
  | .recur al p i m mi rs k u, .recur al' p' i' m' mi' rs' k' u' =>
    al == al' && p == p' && i == i' && m == m' && mi == mi' && listEq ruleEq rs rs'
      && k == k' && u == u'
  | _, _ => false

/-- Why two entries differ. -/
def whyDiffer (a b : CEntry) : String :=
  if kn a.kind != kn b.kind then s!"kind {kn a.kind} vs {kn b.kind}"
  else if a.levelParams != b.levelParams then "level parameters"
  else if !(a.type == b.type) then "type"
  else match a.kind, b.kind with
    | .defn .., .defn .. => "value"
    | .opaq .., .opaq .. => "value"
    | _, _ => "other fields"

/-- Lean's merge (`mergeEntry`) over a name's entries, in module order. -/
def leanAccepts (pm : Std.HashMap Name CEntry) (es : Array CEntry) : Bool := Id.run do
  let some e0 := es[0]? | return true
  let mut cur := e0
  for c in es[1:] do
    if subsumes pm c cur then cur := c
    else if subsumes pm cur c then pure ()
    else return false
  return true

/-! ## Helpers -/

def hasBit (b : ByteArray) (j : Nat) : Bool := (b.get! (j / 8) >>> (j % 8).toUInt8) &&& 1 == 1

def pct (a : Array Nat) (p : Nat) : Nat :=
  if a.isEmpty then 0 else a[(a.size - 1) * p / 100]!

def sortNat (a : Array Nat) : Array Nat := a.qsort (· < ·)

structure ModStat where
  nExp : Nat := 0
  hiddenThm : Nat := 0
  hiddenDef : Nat := 0
  hiddenOpq : Nat := 0
  otherDiff : Nat := 0
  privOnly : Nat := 0
  diffs : Array (String × Nat) := #[]
  dupExp : Array CEntry := #[]

def bump (m : Std.HashMap String Nat) (k : String) (d : Nat := 1) : Std.HashMap String Nat :=
  m.insert k (m.getD k 0 + d)

def nameStr (n : Name) : String := toString n

def run (jobs : Nat) (sp : SearchPath) (roots : Array Name) : IO UInt32 := do
  let t0 ← IO.monoMsNow
  let .ok order ← closureOrder sp roots | IO.eprintln "closure failed"; return 3
  let n := order.size
  IO.println s!"modules in the closure: {n}"
  let ls ← match ← parRun jobs n (fun i ds => loadPriv sp order[i]! ds) with
    | .ok ls => pure ls
    | .error e => IO.eprintln s!"load: {e}"; return 3
  IO.println s!"loaded (private level) in {(← IO.monoMsNow) - t0} ms"
  let idx : Std.HashMap Name Nat := order.size.fold (fun i _ m => m.insert order[i]! i) {}
  -- occurrences
  let mut occ : Std.HashMap Name (Array Nat) := {}
  let mut total := 0
  let mut kinds : Std.HashMap String Nat := {}
  let mut pm : Std.HashMap Name CEntry := {}
  for i in [0:n] do
    for c in ls[i]!.constants do
      total := total + 1
      kinds := bump kinds (kn c.kind)
      occ := occ.insert c.name ((occ.getD c.name #[]).push i)
      unless pm.contains c.name do pm := pm.insert c.name c
  let distinct := occ.size
  let dupNames := occ.fold (fun acc k v => if v.size ≥ 2 then acc.push k else acc) #[]
  let dupSet : Std.HashSet Name := dupNames.foldl (·.insert ·) {}
  IO.println s!"constants stored: {total}, distinct names: {distinct}, names stored by >1 module: {dupNames.size}"
  IO.println s!"by kind (private level): {kinds.toList}"
  -- exported level
  let t1 ← IO.monoMsNow
  let sts ← match ← parRun jobs n (fun i ds => do
      match ← loadExp sp order[i]! ds with
      | .error e => return .error e
      | .ok (es, ds) =>
        let priv : Std.HashMap Name CEntry :=
          ls[i]!.constants.foldl (fun m c => m.insert c.name c) {}
        let mut st : ModStat := { nExp := es.size }
        let mut diffs : Std.HashMap String Nat := {}
        let mut seen : Std.HashSet Name := {}
        for e in es do
          seen := seen.insert e.name
          if dupSet.contains e.name then st := { st with dupExp := st.dupExp.push e }
          match priv[e.name]? with
          | none => st := { st with otherDiff := st.otherDiff + 1 }
          | some p =>
            if kn p.kind != kn e.kind then
              diffs := bump diffs s!"{kn p.kind}->{kn e.kind}"
              match p.kind, e.kind with
              | .thm .., .ax _ => st := { st with hiddenThm := st.hiddenThm + 1 }
              | .defn .., .ax _ => st := { st with hiddenDef := st.hiddenDef + 1 }
              | .opaq .., .ax _ => st := { st with hiddenOpq := st.hiddenOpq + 1 }
              | _, _ => st := { st with otherDiff := st.otherDiff + 1 }
        for c in ls[i]!.constants do
          unless seen.contains c.name do st := { st with privOnly := st.privOnly + 1 }
        return .ok ({ st with diffs := diffs.toArray }, ds)) with
    | .ok s => pure s
    | .error e => IO.eprintln s!"load exported: {e}"; return 3
  IO.println s!"loaded (exported level) in {(← IO.monoMsNow) - t1} ms"
  let mut diffTot : Std.HashMap String Nat := {}
  for st in sts do for (k, v) in st.diffs do diffTot := bump diffTot k v
  IO.println s!"exported vs private kind changes (summed over modules): {diffTot.toList}"
  let expOf : Array (Std.HashMap Name CEntry) :=
    sts.map fun st => st.dupExp.foldl (fun m e => m.insert e.name e) {}

  let selftest := (← IO.getEnv "OLEAN_MODULAR_SELFTEST").isSome
  -- ## 1. duplicated names
  IO.println "\n== 1. names stored by more than one module =="
  -- key -> (names, fragOK, leanOK, both, neither)
  let mut tab : Std.HashMap String (Array Nat) := {}   -- [names, fragOK, leanOK, bothOK, fragOnly, leanOnly, neither]
  let mut ex : Std.HashMap String (Array String) := {}
  let mut conflicts : Array (Name × Array Nat × Array Nat) := #[]  -- name, modules, classes
  let mut multiplicity : Std.HashMap Nat Nat := {}
  for d in dupNames do
    let L := occ[d]!
    multiplicity := multiplicity.insert L.size (multiplicity.getD L.size 0 + 1)
    let es : Array CEntry := L.map fun i => (ls[i]!.constants.find? (fun (c : CEntry) => c.name == d)).get!
    -- self-test of the failing path: `OLEAN_MODULAR_SELFTEST=1` perturbs the
    -- last copy of the first duplicated name (its level parameters)
    let es := if selftest && d == dupNames[0]! then
        es.modify (es.size - 1) fun e => { e with levelParams := [.str .anonymous "bogus"] }
      else es
    -- classes
    let mut reps : Array CEntry := #[]
    let mut cls : Array Nat := #[]
    for e in es do
      match reps.findIdx? (fragEq · e) with
      | some k => cls := cls.push k
      | none => cls := cls.push reps.size; reps := reps.push e
    let fragOK := reps.size == 1
    let ees := (L.map fun i => (expOf[i]!)[d]?).filterMap id
    let leanOK := leanAccepts pm (if ees.size == L.size then ees else es)
    let ks := (es.map (kn ·.kind)).toList.eraseDups.mergeSort (· ≤ ·)
    let key := "/".intercalate ks
    let row := tab.getD key (Array.replicate 7 0)
    let row := row.modify 0 (· + 1)
    let row := if fragOK then row.modify 1 (· + 1) else row
    let row := if leanOK then row.modify 2 (· + 1) else row
    let row := if fragOK && leanOK then row.modify 3 (· + 1)
      else if fragOK then row.modify 4 (· + 1)  -- fragOK, lean rejects
      else if leanOK then row.modify 5 (· + 1)  -- frag incompatible, lean accepts
      else row.modify 6 (· + 1)
    tab := tab.insert key row
    let cat := if fragOK && leanOK then "compat+lean"
      else if fragOK then "compat, lean rejects"
      else if leanOK then "INCOMPATIBLE, lean accepts" else "INCOMPATIBLE, lean rejects"
    let why := if fragOK then "" else
      let r0 := reps[0]!
      " [" ++ ", ".intercalate ((reps.toList.drop 1).map (whyDiffer r0 ·)) ++ "]"
    let lst := ex.getD (key ++ " | " ++ cat) #[]
    if lst.size < 4 then
      ex := ex.insert (key ++ " | " ++ cat)
        (lst.push s!"{d} in {(L.map (order[·]!)).toList.take 3}{why}")
    unless fragOK do conflicts := conflicts.push (d, L, cls)
  IO.println s!"multiplicity (modules per duplicated name): {(multiplicity.toList.toArray.qsort (·.1 < ·.1)).toList}"
  IO.println "kinds | names | fragment-compatible | lean-accepts | both | compat only | lean only | neither"
  for (k, r) in tab.toList.toArray.qsort (fun a b => a.2[0]! > b.2[0]!) do
    IO.println s!"{k} | {r[0]!} | {r[1]!} | {r[2]!} | {r[3]!} | {r[4]!} | {r[5]!} | {r[6]!}"
  let sum (j : Nat) := tab.fold (fun a _ r => a + r[j]!) 0
  IO.println s!"TOTAL | {sum 0} | {sum 1} | {sum 2} | {sum 3} | {sum 4} | {sum 5} | {sum 6}"
  IO.println "examples:"
  for (k, v) in ex.toList.toArray.qsort (fun a b => a.1 < b.1) do
    IO.println s!"  {k}"
    for s in v do IO.println s!"    {s}"

  -- closure bitsets
  let nb := (n + 7) / 8
  let impIdx : Array (Array Nat) := ls.map fun l => l.imports.filterMap (idx[·]?)
  let mut clo : Array ByteArray := Array.mkEmpty n
  for i in [0:n] do
    let mut b : ByteArray := ⟨Array.replicate nb 0⟩
    for j in impIdx[i]! do
      let cj := clo[j]!
      for k in [0:nb] do b := b.set! k (b.get! k ||| cj.get! k)
    b := b.set! (i / 8) (b.get! (i / 8) ||| ((1 : UInt8) <<< (i % 8).toUInt8))
    clo := clo.push b

  -- ## 2. local check per module
  IO.println "\n== 2. the local compatibility check per module =="
  IO.println s!"incompatible names (fragment): {conflicts.size}"
  let mut failCnt := Array.replicate n 0
  let mut rootCnt := Array.replicate n 0
  let mut failNames : Array (Array String) := Array.replicate n #[]
  for (d, L, cls) in conflicts do
    let lo := L.foldl min n
    -- sc[M]: class of S_M's entry for d, `none` if absent
    let mut sc : Array (Option Nat) := Array.replicate n none
    let mut failed : Array Bool := Array.replicate n false
    for m in [lo:n] do
      let own := (L.findIdx? (· == m)).map (cls[·]!)
      let mut fam : Array Nat := #[]   -- classes present in the families
      let mut firstSc : Option Nat := none
      for b in impIdx[m]! do
        if let some c := sc[b]! then
          fam := fam.push c
          if firstSc.isNone then firstSc := some c
      if let some c := own then fam := fam.push c
      let bad := fam.any (· != fam[0]!)
      if bad then
        failed := failed.set! m true
        failCnt := failCnt.modify m (· + 1)
        let inherited := (impIdx[m]!).any (failed[·]!)
        unless inherited do
          rootCnt := rootCnt.modify m (· + 1)
          if failNames[m]!.size < 3 then
            failNames := failNames.modify m (·.push s!"{d} (in {(L.map (order[·]!)).toList.take 3})")
      sc := sc.set! m (match firstSc with | some c => some c | none => own)
  let nFail := failCnt.foldl (fun a c => if c > 0 then a + 1 else a) 0
  let nRoot := rootCnt.foldl (fun a c => if c > 0 then a + 1 else a) 0
  IO.println s!"modules whose local check fails: {nFail} of {n}; of these first failing there (some name not already failing at a direct import): {nRoot}"
  IO.println "(Lean accepts every one of them: the oleans exist, built by Lean.)"
  IO.println "modules where the check first fails, with clashing names:"
  let mut shown := 0
  for m in [0:n] do
    if rootCnt[m]! > 0 && shown < 200 then
      shown := shown + 1
      IO.println s!"  {order[m]!}: {rootCnt[m]!} name(s) e.g. {failNames[m]!.toList}"

  -- ## 3. summaries
  IO.println "\n== 3. summary sizes =="
  let own := ls.map (·.constants.size)
  let mut sizes : Array Nat := Array.replicate n 0
  for m in [0:n] do
    let mut s := 0
    for j in [0:m+1] do
      if hasBit clo[m]! j then s := s + own[j]!
    sizes := sizes.set! m s
  -- duplicates counted once
  for d in dupNames do
    let L := occ[d]!
    let lo := L.foldl min n
    for m in [lo:n] do
      let k := L.foldl (fun a j => if hasBit clo[m]! j then a + 1 else a) 0
      if k ≥ 2 then sizes := sizes.modify m (· - (k - 1))
  let sorted := sortNat sizes
  let sumS := sizes.foldl (· + ·) 0
  IO.println s!"summary size (names per module summary): min {pct sorted 0}, median {pct sorted 50}, p90 {pct sorted 90}, p99 {pct sorted 99}, max {pct sorted 100}"
  IO.println s!"sum over modules of |S_M|: {sumS}; distinct names overall: {distinct}; sum / distinct = {sumS / distinct} (each name is in that many summaries on average)"
  let edges := impIdx.foldl (fun a v => a + v.size) 0
  let edgeSum := (List.range n).foldl (fun a m => impIdx[m]!.foldl (fun a b => a + sizes[b]!) a) 0
  IO.println s!"import edges: {edges}; sum over edges of |S_B| (work if each summary is copied along each edge): {edgeSum}"
  let ownSorted := sortNat own
  IO.println s!"own declarations per module: min {pct ownSorted 0}, median {pct ownSorted 50}, p90 {pct ownSorted 90}, max {pct ownSorted 100}"
  let cloSizes := sortNat ((List.range n).toArray.map fun m => (List.range (m+1)).foldl (fun a j => if hasBit clo[m]! j then a + 1 else a) 0)
  IO.println s!"modules in closure (incl. itself): median {pct cloSizes 50}, p90 {pct cloSizes 90}, max {pct cloSizes 100}"
  -- hidden
  let hid := sts.map fun s => s.hiddenThm + s.hiddenDef + s.hiddenOpq
  let hidSorted := sortNat hid
  let hT := sts.foldl (fun a s => a + s.hiddenThm) 0
  let hD := sts.foldl (fun a s => a + s.hiddenDef) 0
  let hO := sts.foldl (fun a s => a + s.hiddenOpq) 0
  let pO := sts.foldl (fun a s => a + s.privOnly) 0
  let oD := sts.foldl (fun a s => a + s.otherDiff) 0
  let nE := sts.foldl (fun a s => a + s.nExp) 0
  IO.println s!"exported view: {nE} constants of {total} private-level ones; hidden into assumptions: theorems {hT}, definitions {hD}, opaque {hO}; private-only names (absent from the exported view): {pO}; other differences: {oD}"
  IO.println s!"names turned into assumptions per module: min {pct hidSorted 0}, median {pct hidSorted 50}, p90 {pct hidSorted 90}, max {pct hidSorted 100}"
  IO.println s!"total time {(← IO.monoMsNow) - t0} ms"
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | jobs :: sp :: mods@(_ :: _) =>
    let roots := mods.toArray.map fun m => (m.splitOn ".").foldl Name.str Name.anonymous
    run jobs.toNat! ((sp.splitOn ":").map System.FilePath.mk) roots
  | _ => IO.eprintln "usage: olean-modular JOBS SEARCHPATH MODULE..."; return 2
