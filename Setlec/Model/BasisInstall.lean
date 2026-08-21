import Setlec.Model.Basis.PUnit.Install
import Setlec.Model.Basis.Eq.Install
import Setlec.Model.Basis.PSigma.Install
import Setlec.Model.Basis.Nat.Install
import Setlec.Model.Basis.Empty.Install
import Setlec.Model.Basis.Quot.Install

/-!
# Interpretation computations for the pinned basis declarations

Each pinned (annotated) basis type's interpretation is computed
concretely (one module per basis type under `Setlec/Model/Basis/`), and
the hand-written value is shown to inhabit it — the `hkey` obligations
of basis installation (`Setlec.Model.Consistency`).
-/
