import Setlec.TT.Const
import Setlec.SetTheory.Basic

/-!
# Set-theoretic values of the built-in constants

Each `BConst` gets a value in the target set theory, as a function of
its (concrete) level instantiation.  The values are the hand-written
basis models of `Setlec/Model/BasisVal.lean`, restated here against the
`SetTheory` interface alone: this module imports **only**
`Setlec/SetTheory/*`, never the checker or its model layer.

Note the two places where the domain-relative collapse (task #100) is
visible:

* `psigmaMkV` is the proof point when the joint level is `0` — at
  `Prop` the pair set is a truth value, so a Kuratowski pair could not
  inhabit it;
* `quotIndV`, `quotSoundV`, `propextV` and `emptyRecV` are *just* the
  proof point, because their whole λ-tower ends in a `Prop` and
  therefore collapses.
-/

namespace Setlec.TT

open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-- The space of relations on `A`: `A → A → Prop`. -/
noncomputable def relSpace (A : V) : V := piC A fun _ => piC A fun _ => univ 0

/-- The minor-premise space of `Nat.rec` at motive `M`. -/
noncomputable def natStepSpace (M : V) : V :=
  piC omega fun n => piC (app M n) fun _ => app M (natsucc n)

/-- `Nat.succ`. -/
noncomputable def natSuccV : V := lamC omega natsucc

theorem natSuccV_app {n : V} (hn : n ∈ˢ (omega : V)) :
    app (natSuccV V) n = natsucc n := app_lamC hn

theorem natSuccV_mem : natSuccV V ∈ˢ piC (omega : V) fun _ => omega :=
  lamC_mem fun _ hx => natsucc_mem hx

/-- `Nat.rec.{u}`. -/
noncomputable def natRecV (u : Nat) : V :=
  lamC (piC omega fun _ => univ u) fun M =>
    lamC (app M natzero) fun z =>
      lamC (natStepSpace V M) fun s =>
        lamC omega fun n => natrec z s n

/-- `PUnit.rec.{u,v}`. -/
noncomputable def punitRecV (v : Nat) : V :=
  lamC (piC unitSet fun _ => univ v) fun M =>
    lamC (app M pt) fun m =>
      lamC unitSet fun _ => m

/-- `PSigma'.{u,v}`. -/
noncomputable def psigmaV (u v : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (piC A fun _ => univ v) fun B =>
      sigmaSet (Nat.max u v) A fun x => app B x

/-- `PSigma'.mk.{u,v}`. -/
noncomputable def psigmaMkV (u v : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (piC A fun _ => univ v) fun B =>
      lamC A fun a =>
        lamC (app B a) fun b =>
          if Nat.max u v = 0 then pt else spair a b

/-- `PSigma'.fst.{u,v}`. -/
noncomputable def psigmaFstV (u v : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (piC A fun _ => univ v) fun B =>
      lamC (sigmaSet (Nat.max u v) A fun x => app B x) sfst

/-- `PSigma'.snd.{u,v}`. -/
noncomputable def psigmaSndV (u v : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (piC A fun _ => univ v) fun B =>
      lamC (sigmaSet (Nat.max u v) A fun x => app B x) ssnd

/-- `Quot.{u}`. -/
noncomputable def quotV (u : Nat) : V :=
  lamC (univ u) fun A => lamC (relSpace V A) fun R => quotSet u A R

/-- `Quot.mk.{u}`. -/
noncomputable def quotMkV (u : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (relSpace V A) fun R => lamC A fun a => quotClass u A R a

/-- The invariance space of `Quot.lift`: `∀ a b, r a b → f a = f b`. -/
noncomputable def quotInvSpace (A R f : V) : V :=
  piC A fun a => piC A fun b =>
    piC (app (app R a) b) fun _ => eqv (app f a) (app f b)

/-- `Quot.lift.{u,v}`. -/
noncomputable def quotLiftV (u v : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (relSpace V A) fun R =>
      lamC (univ v) fun B =>
        lamC (piC A fun _ => B) fun f =>
          lamC (quotInvSpace V A R f) fun _ => SetTheory.quotLift u v A R f

/-- `Classical.choice.{u}`, in the primitive double-negation form. -/
noncomputable def choiceV (u : Nat) : V :=
  lamC (univ u) fun A =>
    lamC (piC (piC A fun _ => empty) fun _ => empty) fun _ => schoice A

/-- The value of each built-in constant at a concrete level
instantiation. -/
noncomputable def bval : BConst → List Nat → V
  | .nat, _ => omega
  | .natZero, _ => natzero
  | .natSucc, _ => natSuccV V
  | .natRec, us => natRecV V (lv us 0)
  | .punit, _ => unitSet
  | .punitUnit, _ => pt
  | .punitRec, us => punitRecV V (lv us 1)
  | .psigma, us => psigmaV V (lv us 0) (lv us 1)
  | .psigmaMk, us => psigmaMkV V (lv us 0) (lv us 1)
  | .psigmaFst, us => psigmaFstV V (lv us 0) (lv us 1)
  | .psigmaSnd, us => psigmaSndV V (lv us 0) (lv us 1)
  | .empty, _ => empty
  | .emptyRec, _ => pt
  | .quot, us => quotV V (lv us 0)
  | .quotMk, us => quotMkV V (lv us 0)
  | .quotLift, us => quotLiftV V (lv us 0) (lv us 1)
  | .quotInd, _ => pt
  | .quotSound, _ => pt
  | .propext, _ => pt
  | .choice, us => choiceV V (lv us 0)

end Setlec.TT
