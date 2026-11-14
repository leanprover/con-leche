--#export t
/- End-to-end fixture (task #582, found by task #580 on CFSG's
   `Certificates.Kernel.Sporadic.Fi24Br.Seed`): a strict counter of two
   hundred thousand steps, in the shape of CFSG's `strictB`/`runF`.

   `count len n i` runs `n` steps of a `Nat.rec`; step number `i` tests
   `Nat.blt i len` and goes on with `strictB (Nat.succ i) ih`, whose
   `Nat.rec` forces the index `Nat.succ i` before the next step.  The
   official kernel takes the whnf of every major premise, and its whnf folds
   `Nat.succ x` to a literal (`reduce_nat`), so the index is always
   `Nat.succ` over a literal.  A checker that takes a `Nat.succ` major as it
   stands (con-leche before task #582: the constructor shortcut of
   `prepareMajor`) carries the index as a unary tower `Nat.succ (… (Nat.succ
   0))` that grows by one level per step.  The 32-bit hash of an application
   depends on the argument's hash alone, so the towers' hashes run into a
   cycle (DESIGN #580): past the cycle's start, memo keys that hold the
   index share a bucket with the key of a step one period earlier, and every
   probe compares two towers as deep as the step number.  Quadratic.

   The steps must pass the cycle's start (step 116 393 for a tower over the
   literal `0`), so the counter runs 200 000 of them.  A performance fixture:
   accepted in 1.8 s (18.8 G instructions) by con-leche with the whnf of a
   `Nat.succ` major (2026-11-14), in 348 s (2 554 G) without it; the official
   kernel (`leanchecker` v4.35.0) takes 3.3 s.  `tests/arena.sh` runs it
   under a timeout of 10 s, so the old order fails it.

   The theorem is added with `addDecl` under `debug.skipKernelTC`: the
   elaborator would check `rfl` by its own unfolding.  The stream is checked
   by the checkers that read it. -/
import Lean
open Lean Elab Command

/-- CFSG's strictness combinator: the `Nat.rec` forces `y` before `k`. -/
noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

/-- One step: `i < len`, then the next step at `Nat.succ i`, forced. -/
noncomputable def step (len : Nat) (ih : Nat → Bool) (i : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (strictB (Nat.succ i) ih) (Nat.blt i len)

/-- `n` steps from the index `i`, then `i = len`. -/
noncomputable def count (len n : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i len)
    (fun _ ih => step len ih) n

/-- `count n n 0 = true`, by `Eq.refl true`. -/
def tDecl (n : Nat) : Declaration :=
  let ty := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool)
    (mkApp3 (mkConst ``count) (mkRawNatLit n) (mkRawNatLit n) (mkRawNatLit 0))
    (mkConst ``Bool.true)
  .thmDecl {
    name := Name.mkSimple "t"
    levelParams := []
    type := ty
    value := mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true) }

elab "strict_succ_thm% " n:num : command => liftCoreM (addDecl (tDecl n.getNat))

set_option debug.skipKernelTC true
strict_succ_thm% 200000
