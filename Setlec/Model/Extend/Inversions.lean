import Setlec.Verify.Extend.Inversions
import Setlec.Model.TypeChecker
import Setlec.Model.BasisInstall
import Setlec.Model.IndInstall
import Setlec.Model.ProjInstall
import Setlec.Model.EtaInstall

/-!
# Inversions — relocated to `Setlec/Verify/Extend/Inversions.lean`

The whole content of this module was `V`-free checker inversion and
moved to `Setlec.Verify.Extend.Inversions` (task #123,
`Setlec/TTVerify/DESIGN.md` §14.1).  The module survives as the
install-side import point its `Setlec.Model.Extend.*` siblings depend
on: they inherit the `Model.*Install` modules through it.
-/
