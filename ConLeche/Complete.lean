module

public import ConLeche.Complete.OfficialNested
public import ConLeche.Complete.PosDerivComplete
public import ConLeche.Complete.ProgActive

/-!
# Parked completeness work (lib `ConLecheComplete`)

The root of the checker's COMPLETENESS results against the official
kernel: results, not lemmas — no soundness proof, capstone or checker
module consumes anything here, and nothing outside `ConLeche/Complete/`
may import it (`tests/layering.sh`, the parked clause).

* `OfficialNested` — official's nested elimination and positivity check
  (`inductive.cpp`) transcribed as a Lean spec over our `Expr`;
* `PosDerivComplete` — the nested positivity walk's completeness against
  a run-complete derivation (`posDR_run`).
* `ProgActive` — the walk's in-progress test reads only `active`: the
  older walk that also tested the frame stack is the same function
  (`nestPosP_eq_nil`).

Built by `lake build` (a default target), so it cannot rot.
-/
