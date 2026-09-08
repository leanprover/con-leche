import ConLeche.SetModel
import ConLeche.Semantics
import ConLeche.Model
import ConLeche.Verify.Cached
import ConLeche.MainTheorem

/-!
# The proof-term dependency gate's instrument (task #161 S10; redefined
at the SetR removal's Stage C, 2026-09-05)

`tests/layering.sh` measures where code **sits**; this file measures
what a theorem **uses**.  S9's payoff check found the difference the
hard way: the layering gate read

    base 260 / R 106 / P 117 / neutral 3 modules; 0 P->R edges

— true, and simultaneously silent about `Red.beta` being live on the
shipped P capstone's proof path, because S7/S8 moved the modules that
*define* `Red`/`Infer`/`DefEq` into the shared base, where a
directory-classifying gate counts them as `base`.  The campaign's rule,
from that finding, is unchanged and is why this file still exists:

> An import gate measures where code *sits*; only the proof term
> measures what a theorem *uses*.  A separation criterion stated over
> imports cannot certify a proof-path property.

## WHAT THE GATE MEASURED, AND WHY IT HAD TO CHANGE

Until 2026-09-05 it measured **P-vs-R disjointness**: eleven named R
targets (`Red`, `Red.beta`, `Infer`, `Infer.app`, `DefEq`,
`DefEq.trans`, `EnvS`, `checkDeclR_ofEnvRE`, `DeclR`, `declIndRR`,
`DeclIndRun`), each checked absent from every capstone's constant
closure.  Every row read `absent`, and that was the separation
campaign's deliverable, mechanized.

The SetR removal deleted the collapsed model (Stage A), the R core
(Stage B) and finally the relation family and the whole derivation
bridge above it (Stage C).  **Every one of the eleven targets is
gone.**  A gate whose targets do not exist measures nothing: it would
report eleven `MISSING-TARGET` rows, or — worse, if the names were
merely dropped — forty-four vacuous `absent`s.  *The separation is not
weaker; there is no second lane to be separated from.*

## WHAT IT MEASURES NOW

A **frozen module-level dependency pin**: for each of the six
pinned roots (the two main theorems and the four capstone letters and
assembly lemmas under them), the exact set of `ConLeche.*` modules its type and
proof term reach, transitively, at the constant level.  The expectation
is `tests/proofdeps-expected.txt` and the gate is a diff, so any drift
shows up as a named module appearing or disappearing — which is the
property the old gate had (a target entering a closure is rot; a target
leaving is progress that must be recorded) generalised from eleven
names to every module.

It is a **weaker** claim than the old one — a pin is not a theorem, and
"module X is on the path" is not "declaration Y is used".  It is also
the strongest thing left to say once the tree has one lane, and it
catches the class of regression the old gate was built for: a capstone
silently acquiring a dependency on machinery it should not need.  The
first line of defence against *that* is now the ratchet on this file's
expectations, and the second is the axiom audit, which is unchanged.

TWO IMPLEMENTATION NOTES, both learned by getting them wrong (S9 §1):

* a theorem's proof term must be reached by matching `.thmInfo`
  **directly**.  `ConstantInfo.value?` returns `none` for theorems at
  Lean 4.33, which silently makes the walk report *nothing* — a green
  gate that measures the empty set;
* every root is checked to **exist** before it is measured
  (`MISSING-ROOT` rows, which the expectations never contain).  A
  misspelled or renamed name would otherwise measure the empty closure
  forever: the config audit's vacuity-protection discipline, at this
  gate.  The vacuity sentinel is now structural — a root whose closure
  is empty prints no rows at all, and the diff fails on 351 missing
  lines.

Run through `tests/proofdeps.sh`; it runs inside `tests/arena.sh`
beside the layering gate.
-/

open Lean

/-- Transitive constant dependencies of a root's type **and proof
term**. -/
partial def conlecheDeps (env : Environment) (todo : List Name)
    (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then conlecheDeps env rest seen
    else
      let seen := seen.insert n
      match env.find? n with
      | none => conlecheDeps env rest seen
      | some ci =>
        -- `.thmInfo` matched directly: `value?` is `none` for
        -- theorems, which would make this walk vacuous.
        let vcs : Array Name := match ci with
          | .thmInfo v => v.value.getUsedConstants
          | .defnInfo v => v.value.getUsedConstants
          | .opaqueInfo v => v.value.getUsedConstants
          | _ => #[]
        conlecheDeps env ((ci.type.getUsedConstants ++ vcs).toList ++ rest)
          seen

/-- The seven pinned roots: the MAIN THEOREM first, then the letters it
is a corollary of and the assembly under those.

* `main_False` — **the statement the project exists to make**
  (`ConLeche/MainTheorem.lean`): an accepted stream, at the shipped
  `--verified` configuration named outright, yields no constant of type
  `False`.  It is pinned as a root because it is what a reader checks
  first; it should reach exactly what the letter it wraps reaches, plus
  `ConLeche.MainTheorem` itself.  (The `Empty` main theorem and the
  `IO`-loop one were dropped from that file on 2026-09-07 — one main
  theorem, and one loop that the theorem is about: the printing lane
  runs an openly unverified twin fold in `Main.lean`.)
* `False_SPCD_P` / `SPCD_P` — **the shipped driver's letters**: the
  checker, running the verified mode over the direct-parse cached core
  it ships with, never accepts a stream in which some stored constant
  has type `False` (resp. `Empty`).
* `sound_P` / `fold_preserves` — the acceptance corollary and the fold
  under it, pinned separately so a change in the assembly is visible
  even when the letter's own closure is unmoved.
* `False_P` / `P` — the pure fueled checker the graded tower is stated
  about. -/
private def roots : List (String × Name) :=
  [("main_False", `ConLeche.no_proof_of_False),
   ("False_SPCD_P", `ConLeche.Cached.no_proof_of_False_cached),
   ("False_P", `ConLeche.Model.no_proof_of_False_pure),
   ("SPCD_P", `ConLeche.Cached.no_proof_of_Empty_cached),
   ("sound_P", `ConLeche.Cached.checkDecls_sound),
   ("fold_preserves", `ConLeche.Cached.fold_preserves),
   ("P", `ConLeche.Model.no_proof_of_Empty_pure)]

/-- The measured rows, in a fixed order: one `<label> :: <module>` per
`ConLeche.*` module the root's proof term reaches, sorted.  The pinned
expectations are in `tests/proofdeps-expected.txt`. -/
def conlecheProofDeps : CoreM Unit := do
  let env ← getEnv
  let names := env.header.moduleNames
  for (lbl, r) in roots do
    if (env.find? r).isNone then
      IO.println s!"MISSING-ROOT {lbl} :: {r}"
    else
      let s := conlecheDeps env [r] {}
      let mut mods : NameSet := {}
      for n in s.toList do
        match env.getModuleIdxFor? n with
        | some i =>
          let m := names[i.toNat]!
          if (`ConLeche).isPrefixOf m then mods := mods.insert m
        | none => pure ()
      for m in (mods.toList.map toString).toArray.qsort (· < ·) do
        IO.println s!"{lbl} :: {m}"

#eval conlecheProofDeps
