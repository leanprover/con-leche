--#export t_pow1 t_pow0
/- End-to-end fixture (task #423 completeness): `Nat.pow` with an exponent
   above 2^24 (`33554432 = 2^25`) on literals, at the ground site.  The
   cached core's bound is official's maximum numeral size (`reduce_pow`,
   `maxNatSize`, task #519): a base `≤ 1` gives `0` or `1` at any
   exponent up to 2^32 - 1, so both are computed.

   Accepted.  The v4.29.1 kernel rejects this source without
   `debug.skipKernelTC` ("deep recursion": its bound was an exponent of
   2^24, beyond which it unfolds `Nat.pow`); the maximum-size bound is
   lean4#14849's, which con-leche follows (task #519).  With the ground engine on, the engine mirrors
   that bound; before, it aborted above an exponent of 2^24 ("nat pow
   bound") and the incumbent computed.

   The theorems are added with `addDecl` under `debug.skipKernelTC`: the
   elaborator does not evaluate the power. -/
import Lean
open Lean Elab Command

def tPowDecl (nm : String) (base res : Nat) : Declaration :=
  let lhs := mkApp2 (mkConst ``Nat.beq)
    (mkApp2 (mkConst ``Nat.pow) (mkRawNatLit base) (mkRawNatLit 33554432)) (mkRawNatLit res)
  .thmDecl {
    name := Name.mkSimple nm
    levelParams := []
    type := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) lhs (mkConst ``Bool.true)
    value := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true) }

elab "pow_thms%" : command => liftCoreM do
  addDecl (tPowDecl "t_pow1" 1 1)
  addDecl (tPowDecl "t_pow0" 0 0)

set_option debug.skipKernelTC true
pow_thms%
