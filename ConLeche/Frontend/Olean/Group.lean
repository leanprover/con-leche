module

public import ConLeche.Frontend.Olean.Records

@[expose] public section

/-!
# Reading `.olean` files: one inductive group's record

An importer presents an imported inductive group as its record, whole: its types,
constructors and recursors, as its home's emission builds it (DESIGN #460 §2).
`groupRecord mg n` builds the record of `n`'s group from the constants `mg` holds,
exactly as the emission does (`Emit.block` over `blockTys`, `blockCtors`,
`blockRecs`, then the stream reader's builder), after validating, for that group
only, what `blocksOk` validates of a merged closure: every member a stored inductive
type of the same block, every listed constructor stored and naming its type, every
recursor's block a member's (`blockStep` of each of the group's names).
`groupRecord_from` (`ConLeche/Verify/Frontend/Olean/Group.lean`): the record is made
of stored constants of those kinds, as `declsOf_from` says of the emission.

`readGroup` gathers a group's constants from one part of a module (a group is
declared by one module): its members and constructors by name, its recursors among
the part's recursor constants, by their block (`readKinds`), read with one memo
(`readEntries`).
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- Some constants as a merge, in their order (each name once: the first copy kept). -/
def mergedOfList (cs : List CEntry) : Merged :=
  cs.foldl (fun mg c =>
    if mg.map.contains c.name then mg
    else { map := mg.map.insert c.name c, order := mg.order.push c.name }) {}

/-- The constants of `n`'s group the emission takes, if `n` is a stored inductive type:
its block's members, their constructors, the recursors under `n`. -/
def groupParts (mg : Merged) (n : Name) : Option (List CEntry × List CEntry × List CEntry) :=
  match mg.map[n]? with
  | some c =>
    match c.kind with
    | .induct _ _ all .. =>
      let tys := blockTys mg all
      let ctors := blockCtors mg tys
      some (tys, ctors, blockRecs mg (recMapOf mg) n)
    | _ => none
  | none => none

/-- The emission of `n`'s group alone. -/
def groupEmit (tys ctors recs : List CEntry) : Emit := ({} : Emit).block tys ctors recs

/-- **One inductive group's record, validated**: `n`'s group as the emission builds it,
after `blockStep` of `n` and of each of the group's constants.  Malformed input as in the
merged read (`blocksOk`); a decline as the stream reader's builder declines a block. -/
def groupRecord (mg : Merged) (n : Name) : Except CheckError Declaration :=
  match groupParts mg n with
  | none => .error (.internal s!"the inductive group of {n}: {n} is not a stored inductive type")
  | some (tys, ctors, recs) =>
    match (n :: (tys ++ ctors ++ recs).map (·.name)).forM (blockStep mg) with
    | .error e => .error e
    | .ok () =>
      match declsOf (groupEmit tys ctors recs) with
      | .error (e, _) => .error e
      | .ok ds =>
        match ds[0]? with
        | some d => if ds.size == 1 then .ok d
          else .error (.internal s!"the inductive group of {n}: {ds.size} records")
        | none => .error (.internal s!"the inductive group of {n}: no record")

/-- `CEntry` of a constant read. -/
def CEntry.ofF (c : CEntryF Name Expr) : CEntry := { toCEntryF := c }

/-- **`n`'s group's constants, from one part of a view**: `look` gives a name's location in
the part, `recs` are the part's recursor constants' locations.  `n` first, then the
block's members, their constructors and the recursors whose block is `n`'s, read with one
memo.  A name the part does not hold is left out, for `groupRecord` to refuse. -/
def readGroup (f : ModFiles) (level : OLeanLevel) (look : Name → Option Nat) (recs : List Nat)
    (n : Name) : Option Merged := do
  let ln ← look n
  let c ← (readEntries f level [ln]).bind (·.head?)
  let .induct _ _ all .. := c.kind | some (mergedOfList [CEntry.ofF c])
  let tyLocs := all.filterMap look
  let tys ← readEntries f level tyLocs
  let ctorLocs := tys.flatMap fun t => match t.kind with
    | .induct _ _ _ cs .. => cs.filterMap look
    | _ => []
  let ks ← readKinds f level recs
  let recLocs := (recs.zip ks).filterMap fun (l, k) => match k with
    | .recur all' .. => if all' == all then some l else none
    | _ => none
  let rest ← readEntries f level (ctorLocs ++ recLocs)
  pure (mergedOfList ((c :: tys ++ rest).map CEntry.ofF))

end ConLeche.Frontend.Olean
