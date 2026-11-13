--#export t_bad
/- End-to-end fixture (task #423 K): a K major whose indices differ.  The
   theorem `bad : Quot.mk r 1 = Quot.mk r 2` (by `Quot.sound`, `r` the
   full relation) is the major of `Eq.rec`; official's `to_cnstr_when_K`
   checks `Quot.mk r 1 ≡ Quot.mk r 2`, fails, so the redex is stuck and
   `kBad = true` is not definitionally equal: the declaration is
   rejected (official too: this source without `debug.skipKernelTC`
   fails with the kernel's type mismatch).

   **ACCEPTED, beyond official**: the ground engine's K step (task #423)
   reduces `Eq.rec` to its minor premise without the index check
   (`Red.iotaK`, task #552), so `kBad` evaluates to `true`.  The claim holds in the
   model (the major is a proof of an equation between equal values of the
   quotient); it is not a definitional equality official accepts.

   `t_bad` is added with `addDecl` under `debug.skipKernelTC`; the stream
   is checked by the checkers that read it. -/
import Lean
open Lean Elab Command

def r : Nat → Nat → Prop := fun _ _ => True

theorem bad : Quot.mk r 1 = Quot.mk r 2 := Quot.sound trivial

noncomputable def kBad : Bool :=
  @Eq.rec (Quot r) (Quot.mk r 1) (fun _ _ => Bool) true (Quot.mk r 2) bad

def tBadDecl : Declaration :=
  .thmDecl {
    name := Name.mkSimple "t_bad"
    levelParams := []
    type := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) (mkConst ``kBad) (mkConst ``Bool.true)
    value := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true) }

elab "k_bad_thm%" : command => liftCoreM (addDecl tBadDecl)

set_option debug.skipKernelTC true
k_bad_thm%
