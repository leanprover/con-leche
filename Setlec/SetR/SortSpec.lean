import Setlec.SetR.SortSpec.Defs
import Setlec.SetR.SortSpec.Blind
import Setlec.SetR.SortSpec.Examples
import Setlec.SetR.SortSpec.Subst
import Setlec.SetR.SortSpec.Agree

/-!
# `Setlec.SetR.SortSpec` — the reduction-free structural sort pilot

See `Setlec/SetR/SortSpec/DESIGN.md` for the pilot's ledger (seal 0 =
pre-registration, seal 1 = the definition and wall #1, seal 2 = the
agreement question).

* `SortSpec/Defs.lean` — `levelOf`, `piCod`, `ctxCod`, `sortApp`, the
  abstract oracle `SortEnv` and its canonical instance `constCod`;
* `SortSpec/Blind.lean` — argument-blindness, discharged;
* `SortSpec/Examples.lean` — worked instances against `inferBody`;
* `SortSpec/Subst.lean` — substitution stability (monotone form) and
  the mechanized refutation of its equational form;
* `SortSpec/Agree.lean` — agreement with the checker's `sortOfE`.
-/
