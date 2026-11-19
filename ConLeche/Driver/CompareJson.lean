module

public import ConLeche.Driver.Compare
import ConLeche.Verify.Cached.DeclNames

@[expose] public section

/-!
# A challenge and its solution, as two lean4export files (task #612)

`con-leche --compare [--] CHALLENGE.ndjson SOLUTION.ndjson` says whether the export
`SOLUTION.ndjson` solves the export `CHALLENGE.ndjson`: every hole of the challenge is met by
the solution's constant of the same name and type, every other challenge declaration is the
solution's, and the solution's file is accepted.  This is leanprover/comparator's setting: it
compares two lean4export files of the same targets.

**No modules, no homes.**  An export has no modules, so every record of the challenge file is
the challenge's own, and is compared by its content alone: a solution that declares a challenge
constant itself, with the same content, meets it (in the merged `--olean` mode a name the
challenge imports must be its home's constant, `Driver.cmpRecord`; that rule is needed only
where a view lacks bodies).  The comparison is `compareRecords`, the `--olean --compare` one, with
every challenge record of the challenge's own (`jsonHomes`) but the standard axioms'.

* **The holes** (`jsonHole`): the challenge file's axioms other than the standard ones
  (`propext`, `Classical.choice`, `Quot.sound`, `isStdAxiom`) and the placeholder `sorryAx`, and its definitions, theorems
  and opaque constants whose value uses `sorryAx` (`isHole`).  A hole is filled by the
  solution's constant of its name and type up to the names of its level parameters, of any kind
  `cmpRecord` admits (its declines stand: a hole at a compiler-trust name filled by a definition
  or theorem, a hole filled by an inductive type's constant).
* **A standard axiom** is compared as it is, exactly (`cmpRecord` with no home on either side).
* **Every other record** is the solution's up to the names of its level parameters
  (`sameRecordUpToLevels`).

**What is compared** (`jsonRecs`): the holes, and what the challenge's environment needs: the
records no other record of the file mentions (the exporter's selection) and what they read, the
holes as their statements.  A record only a hole's value or a theorem's proof mentions is not
compared: an export of a challenge holds `sorryAx` and the cone of the `sorry`'s tag, and a lemma
a challenge's proof uses, none of which the solution need hold.

The solution's file is checked in full, as a plain run checks a stream (`checkMainG`); the
challenge's is compared, not checked: every challenge record stands for a checked solution
record, or for a hole the statement of one, and those read only what the records before them
install (`ctxScoped`).  A challenge record the solution's file lacks is a missing constant,
exit 1.  There is no `--constant`: the exporter's selection is the file.
-/

namespace ConLeche.Driver

open ConLeche

/-- **A compared run of two lean4export files**: the challenge's and the solution's. -/
structure JCmpReq where
  challenge : String
  solution : String

/-- The standard axioms: compared as they are, never holes. -/
def stdAxiomNames : Array Name := #[propextName, choiceName, quotSoundName]

/-- A standard axiom's record. -/
def isStdAxiom : Declaration → Bool
  | .axiomDecl cv => stdAxiomNames.contains cv.name
  | _ => false

/-- The placeholder axiom's record (`sorryAx`): it installs nothing (`declConstants`), and is no
hole. -/
def isPlaceholder : Declaration → Bool
  | .axiomDecl cv => cv.name == sorryAxName
  | _ => false

/-- **A hole of a challenge file**: an axiom other than a standard one and the placeholder, or
a definition, theorem or opaque constant whose value uses `sorryAx`. -/
def jsonHole (d : Declaration) : Bool :=
  !isStdAxiom d && !isPlaceholder d && isHole Declaration.usedConsts d

/-- The name the comparison takes as the challenge's own "module": an export has none, and
every record of the challenge file is the challenge's own. -/
def jsonOwn : Name := .anonymous

/-- **What a record of the file mentions**: what it reads (`recordReads`, literals' support
constants included), and a theorem's or opaque constant's value, which `recordReads` does not
read. -/
def jsonMentions (d : Declaration) : Array Name :=
  match d with
  | .thmDecl _ v | .opaqueDecl _ v => (needsGo {} (recordReads d) v).2
  | _ => recordReads d

/-- **The names other records of the file mention** (`jsonMentions`, values included).  A
record none of whose names is among them is top-level: the exporter's selection, as a name the
exporter was asked for is mentioned by no other record, unless one of them needs it. -/
def jsonMentioned (recs : Array Declaration) : Std.HashSet Name :=
  recs.foldl (init := {}) fun s d =>
    let own := recKey d :: Modular.declNames d
    s.insertMany ((jsonMentions d).filter (!own.contains ·))

/-- The worklist of `jsonNeeded`: record positions, each pushed once (`seen` marks it), so that
`fuel = recs.size + 1` steps empty it. -/
def jsonReachGo (recs : Array Declaration) (idx : Std.HashMap Name Nat) :
    Nat → List Nat → Array Bool → Array Bool
  | 0, _, seen => seen
  | _, [], seen => seen
  | fuel + 1, i :: rest, seen =>
    match recs[i]? with
    | none => jsonReachGo recs idx fuel rest seen
    | some d =>
      let form := if jsonHole d then Modular.stmtOf d else d
      let (stack, seen) := (recordReads form).foldl (init := (rest, seen)) fun (st, seen) y =>
        match idx[y]? with
        | some j => if seen[j]?.getD true then (st, seen) else (j :: st, seen.set! j true)
        | none => (st, seen)
      jsonReachGo recs idx fuel stack seen

/-- **What the challenge's environment needs**: the positions reached from the top-level records
(`jsonMentioned`) and the holes, through what each reads with the holes as their statements
(`recordReads`, which never reads a theorem's value).  A record only a hole's value or a
theorem's proof mentions is not needed: the `sorryAx` an export holds for a `sorry` and what its
tag mentions, a lemma one proof uses. -/
def jsonNeeded (recs : Array Declaration) : Array Bool :=
  let mentioned := jsonMentioned recs
  let roots := (List.range recs.size).filter fun i => match recs[i]? with
    | some d => jsonHole d || (recKey d :: Modular.declNames d).all (!mentioned.contains ·)
    | none => false
  let seen := roots.foldl (fun seen i => seen.set! i true) (Array.replicate recs.size false)
  jsonReachGo recs (recIndex recs) (recs.size + 1) roots seen

/-- **The challenge's records**: the file's records prepared with the built-in prelude, as a
plain run prepares them, those the challenge's environment needs (`jsonNeeded`), in their
order; every hole is one of them. -/
def jsonRecs (pre : Frontend.PreludeIx) (ds : Array Declaration) : Array Declaration :=
  let recs := (Frontend.prepareD pre ds).decls
  let need := jsonNeeded recs
  (recs.zipIdx.filter fun (d, i) => jsonHole d || need[i]?.getD false).map (·.1)

/-- **Every challenge record is the challenge's own**, but a standard axiom's. -/
def jsonHomes (recs : Array Declaration) : Std.HashMap Name Name :=
  recs.foldl (init := {}) fun m d => if isStdAxiom d then m else m.insert (recKey d) jsonOwn

/-- **The compared run of two lean4export files** (see the module docstring). -/
def compareJsonG {μ : Type → Type} [CheckerIO μ] (r : JCmpReq) (mode : CheckMode)
    (maxNatSize : Nat) (pace : Pace) (jobs : Nat) : μ UInt8 := do
  let t0 ← clockMs
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let prelude ← match Frontend.builtinPreludeE with
    | .ok p => pure p
    | .error (_, line) =>
      diagLine s!"con-leche: the built-in prelude does not parse (line {line}); regenerate it \
        with `lake exe natop-pins-export` ({modeTag})"
      return 3
  CheckerIO.liftIO (readStarts pace r.challenge)
  match ← parseStreamG r.challenge jobs with
  | .error e => readFailed modeTag r.challenge e
  | .ok rC =>
  CheckerIO.liftIO (readStarts pace r.solution)
  match ← parseStreamG r.solution jobs with
  | .error e => readFailed modeTag r.solution e
  | .ok rS =>
  let recsC := jsonRecs prelude rC.decls
  let ⟨recsS, _, hoisted⟩ := Frontend.prepareD prelude rS.decls
  match compareRecords jsonOwn Declaration.usedConsts (jsonHomes recsC) {} recsS
      (recIndex recsS) recsC with
  | .error why =>
    if declined.isPrefixOf why then
      diagLine s!"con-leche: {why} ({modeTag})"
      return 2
    diagLine s!"con-leche: {r.solution} does not solve {r.challenge}: {why} ({modeTag})"
    return 1
  | .ok (ctx, filled) =>
  if let some why := ctxScoped ctx then
    diagLine s!"con-leche: {r.solution} does not solve {r.challenge}: {why} ({modeTag})"
    return 1
  hoistedNote hoisted
  -- the solution's file, checked in full
  let tIndex ← clockMs
  let J ← CheckerIO.liftIO (Jobs.build recsS)
  let tParse ← clockMs
  let verdict ← CheckerIO.liftIO do
    checkDeclsIO mode maxNatSize (← IO.getStderr) pace t0 tIndex tParse jobs J
  match verdict with
  | .error e =>
    verdictG modeTag rS.decls.size t0 recsS (.error e) s!"the solution {r.solution}: "
  | .ok _ =>
    outLine s!"con-leche: accepted: {r.solution} solves {r.challenge}: {recsC.size} \
      challenge declarations compared, {filled.size} holes filled, {rS.decls.size} solution \
      declarations checked ({modeTag})"
    for f in filled do
      outLine s!"con-leche: hole {f.name} ({f.hole}) filled by the solution's {f.filler}"
    return 0

end ConLeche.Driver
