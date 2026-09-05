import Setlec.SetBase
import Setlec.SetP
import Setlec.Verify.Cached

/-!
# The proof-term dependency gate's instrument (task #161, S10)

`tests/layering.sh` measures where code **sits**; this file measures
what a theorem **uses**.  S9's payoff check found the difference the
hard way: the layering gate read

    base 260 / R 106 / P 117 / neutral 3 modules; 0 P->R edges

— true, and simultaneously silent about `Red.beta` being live on the
shipped P capstone's proof path, because S7/S8 moved the modules that
*define* `Red`/`Infer`/`DefEq` into the shared base, where a
directory-classifying gate counts them as `base`.  The campaign's rule,
from that finding:

> An import gate measures where code *sits*; only the proof term
> measures what a theorem *uses*.  A separation criterion stated over
> imports cannot certify a proof-path property.

This instrument walks the transitive **constant** closure of a
declaration's type and proof term, optionally with *cut points* whose
own dependencies are not followed, and prints one `PRESENT`/`absent`
row per (root, target) pair.  `tests/proofdeps.sh` holds the pinned
expectations and fails on any divergence **in either direction** (a
target that re-enters a closure is rot; a target that leaves is
progress that must be recorded — the layering gate's shrink-only
ratchet, at the proof-term criterion).

TWO IMPLEMENTATION NOTES, both learned by getting them wrong (S9 §1):

* a theorem's proof term must be reached by matching `.thmInfo`
  **directly**.  `ConstantInfo.value?` returns `none` for theorems at
  Lean 4.33, which silently makes the walk report *nothing* — a green
  gate that measures the empty set;
* every root and every target is checked to **exist** before it is
  measured (`MISSING` rows, which the expectations never contain).
  A misspelled or renamed name would otherwise read `absent` forever:
  the config audit's vacuity-protection discipline, at this gate.

Run through `tests/proofdeps.sh`; it runs inside `tests/arena.sh`
beside the layering gate.
-/

open Lean

/-- Transitive constant dependencies of the roots' types **and proof
terms**, with a set of cut points whose own dependencies are not
followed (they are still recorded as reached). -/
partial def setlecDepsCut (env : Environment) (cut : NameSet)
    (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then setlecDepsCut env cut rest seen
    else
      let seen := seen.insert n
      if cut.contains n then setlecDepsCut env cut rest seen
      else match env.find? n with
        | none => setlecDepsCut env cut rest seen
        | some ci =>
          -- `.thmInfo` matched directly: `value?` is `none` for
          -- theorems, which would make this walk vacuous.
          let vcs : Array Name := match ci with
            | .thmInfo v => v.value.getUsedConstants
            | .defnInfo v => v.value.getUsedConstants
            | .opaqueInfo v => v.value.getUsedConstants
            | _ => #[]
          setlecDepsCut env cut
            ((ci.type.getUsedConstants ++ vcs).toList ++ rest) seen

private def mkNameSet (ns : List Name) : NameSet :=
  ns.foldl (·.insert ·) {}

/-- The four R relations the separation is measured against, each at
**two** granularities, plus the one door S9 found.

The two granularities are not redundant and S9's table conflated them:
the *type* name (`Setlec.SetR.Infer`) enters a P theorem's closure as
soon as the theorem's **statement** mentions an R record — `DeclIndR`
carries `∀ φ, … Infer … ∧ DefEq …`, so every ind-tier P signature
drags the names in without any P proof ever deriving anything — while
a *constructor* (`Infer.app`, `Red.beta`) enters only when a proof
term actually builds a derivation.  The record split targets the
first; the β-certificate gate targets the second.

S11a added the ninth target, `DeclR` itself: the per-declaration
*record* the graded lane consumed until S11a re-pointed its fold at
`DeclRunR`.  It is the record-level reading of the same separation —
`Red.beta` is about derivations built, `DeclR` about the record
carried — and it left the P capstones' closures outright when the run
route landed.

S11b added the tenth and eleventh, and they close the campaign's
question: `declIndRR` — the `ind` kind's derivation bridge, which was
the single remaining door — and `DeclIndR`, the ind kind's *record*.
Both left the P capstones' closures when the ind run bridge landed, and
with them the six relation names went `absent` at BOTH granularities.
There is no cut point left to measure: block (B)'s cut was retired in
the batch that emptied it, exactly as this file's own rule says (a
cut-point row measures a route; when the route is gone the row goes
with it, and the uncut reading is the honest one).

**THE SetR REMOVAL (2026-09-05) RETIRES THE TWELFTH TARGET,
`Setlec.SetR.EnvS`** — the collapsed model's environment invariant,
which was the campaign's very first target.  It is gone with the tier
it lived in (`Setlec/SetR/EnvS.lean`), so its rows go with their
subject; the file's own vacuity protection would otherwise have read
`MISSING-TARGET` forever.  The ten survivors all live in
`Setlec/SetBase/*` under the unchanged namespace `Setlec.SetR`, which
is why the removal moved no row but this one: what the gate measures is
the SHARED relation tier the graded proof must not touch, and that tier
was never in the deleted directory. -/
private def targets : List Name :=
  [`Setlec.SetR.Red, `Setlec.SetR.Red.beta,
   `Setlec.SetR.Infer, `Setlec.SetR.Infer.app,
   `Setlec.SetR.DefEq, `Setlec.SetR.DefEq.trans,
   `Setlec.SetR.checkDeclR_ofEnvRE,
   `Setlec.SetR.DeclR, `Setlec.SetR.declIndRR,
   `Setlec.SetR.DeclIndR]

/-- The vacuity sentinel: a constant that MUST be in every closure
measured here.  If a root is misspelled the walk collapses and every
row reads `absent`; this row reads `absent` too, and the gate fails. -/
private def sentinel : Name := `Setlec.Expr

private def emit (env : Environment) (label : String) (root : Name)
    (cut : List Name) : IO Unit := do
  if (env.find? root).isNone then
    IO.println s!"MISSING-ROOT {label} :: {root}"
    return
  let s := setlecDepsCut env (mkNameSet cut) [root] {}
  for t in sentinel :: targets do
    if (env.find? t).isNone then
      IO.println s!"MISSING-TARGET {label} :: {t}"
    else
      let mark := if s.contains t then "PRESENT" else "absent "
      IO.println s!"{mark} {label} :: {t}"

/-- The measured rows, in a fixed order.  The pinned expectations are
in `tests/proofdeps.sh`. -/
def setlecProofDeps : CoreM Unit := do
  let env ← getEnv
  -- (A) the shipped P capstone family: what the user's question is
  -- about.  Task #172 retired the three interned drivers and their
  -- letters with them; `SPCD_P` is the letter over the driver the
  -- binary now runs (`checkDeclsSPCachedD`), and `P` is the pure
  -- fueled checker the whole tower is stated about.
  emit env "SPCD_P" `Setlec.Cached.no_proof_of_Empty_SPCD_P []
  emit env "P" `Setlec.SetR.Interp2.no_proof_of_Empty_P []
  -- (B) THE DOOR IS GONE (task #161 S11b).  S9 found one door at
  -- `checkDeclR_ofEnvRE`; S11a moved it to `declIndRR`; S11b's ind run
  -- bridge removed it.  There is nothing left to cut — `declIndRR` is
  -- not in the closure, so a cut at it would measure the uncut reading
  -- and the row would be inert (S11a finding 1).  The cut root is
  -- therefore **retired** and the door is pinned directly, as target
  -- `declIndRR` in block (A): absent from all four capstones.
  -- (C) the P tier's own mathematics: the claims tower, the inductive
  -- tier's step, the value kinds' harvest.  All relation-free, and
  -- that is the separation's real deliverable.
  emit env "claims" `Setlec.SetR.Interp2.checkSound2P []
  emit env "declIndP" `Setlec.SetR.Interp2.declIndP []
  emit env "harvestDefnP" `Setlec.SetR.Interp2.harvestDefnP []
  -- (D) THE RUN ROUTE ITSELF (task #161 S11a): the five non-`ind`
  -- kinds' producer, measured at its own root.  Every target absent is
  -- the batch's deliverable stated positively — the dispatch derives
  -- nothing, carries no `DeclR`, and its only route into the relation
  -- tier is the `Ind` parameter its callers fill.
  emit env "runroute" `Setlec.SetR.checkDeclRun_of []
  -- (E) THE IND RUN BRIDGE AND THE WHOLE RUN DISPATCH (task #161
  -- S11b), each at its own root.  `declIndRunRR` is the `ind` kind's
  -- checker inversion feeding `DeclIndRunR`; `checkDeclRun_ofEnvRE` is
  -- the theorem the graded fold actually calls, all six kinds
  -- discharged.  Every target absent at both roots is the campaign's
  -- criterion stated positively: the declaration bridge the P lane runs
  -- on builds no derivation, carries no record of one, and has no
  -- premise slot left through which one could arrive.
  emit env "indrunroute" `Setlec.SetR.declIndRunRR []
  emit env "declrun" `Setlec.SetR.checkDeclRun_ofEnvRE []

#eval setlecProofDeps
