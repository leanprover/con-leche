import Setlec.Verify.Extend.Iota
import Setlec.Model.Extend.Inversions
import Setlec.Model.IotaWalk

/-!
# Iota — relocated to `Setlec/Verify/Extend/Iota.lean`

The whole content of this module was `V`-free checker inversion and
moved to `Setlec.Verify.Extend.Iota` (task #123,
`Setlec/TTVerify/DESIGN.md` §14.1).  The module survives as the
install-side import point its `Setlec.Model.Extend.*` siblings depend
on: they inherit `Setlec.Model.IotaWalk` through it.
-/
