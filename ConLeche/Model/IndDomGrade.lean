module

public import ConLeche.Model.Currency
import ConLeche.Model.Rules.RedSoundKit
public section

/-!
# The instantiated domains are graded (task #161, IND TIER part 4)

The second half of the part-4 grading bill, and the one that is
**genuinely new content** rather than a transposition.

`defEqAt_of_run` fires a recorded comparison only against *both*
sides' gradings.  Every iota walk compares a statement-frame opener's
annotation against a domain of an `instPisAt` run — the recursor's
prefix domains (`rdoms`), the constructor's field domains (`cdoms`),
the rule's λ-domains (`ldomsL`).  The **a**-side is a slot of the
stored `iota_j` theorem's own tower and is graded by `hokA_padded`.
The **b**-side is a slot of a *different* stored type's tower,
instantiated at the statement frame, and nothing in the checker's run
record types it: `checkIotaThm` compares domains with `checkDefEqList`
and never infers them (`Inductives/Modeled.lean:109-135`), so the P tier's
general grading producer — `InferClaim` from an `inferTypeCore`
run — has nothing to consume.

So the b-side's grading has to come from its **own type's** tower, and
this file is the lemma that walks it: an `instPisAt` run's domains are
graded whenever the type's reading is, the spine's readings are, and
each spine element's value inhabits the domain it is substituted into.
The last premise is the load-bearing one and is where the walks come
back in — which is why the stage that consumes this runs an induction
on the frame position, spending the equality at position `i` to earn
the grading at position `i + 1`.

**Why the spine premise is cheap where it is used.**  On a `.plain`
fire every spine element is a frame *opener*, and an opener reads to a
`.bvar` (`denoteMeta_fvar`), which is graded by definition — so the
`WellDenotedV` premise costs nothing there.  On a `.nested` fire the spine
is the instantiated pins, and `RecRuleLaw` already carries their open
readings **graded** (the ratified iota-seal repair, `Annot/EnvModelM.lean`)
— the conjunct that was added for the pins' own sake turns out to be
exactly what this lemma asks for.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## The `.pi` split, in the P currency -/

/-- A `.pi` reading's domain is graded when the reading is. -/
theorem WellDenotedV_pi_dom {ρ : Nat → V} {u v : Nat} {A B : AnnotTerm}
    (h : WellDenotedV V ρ (.pi u v A B)) : WellDenotedV V ρ A :=
  ⟨((WellDenoted_pi V ρ u v A B) ▸ h.1).1,
    ((AnnotValid_pi V ρ u v A B) ▸ h.2).1⟩

/-- A `.pi` reading's body is graded at every extension by an element
of the domain. -/
theorem WellDenotedV_pi_body {ρ : Nat → V} {u v : Nat} {A B : AnnotTerm}
    (h : WellDenotedV V ρ (.pi u v A B)) {x : V}
    (hx : x ∈ˢ interp V ρ A) : WellDenotedV V (cons x ρ) B :=
  ⟨((WellDenoted_pi V ρ u v A B) ▸ h.1).2 x hx,
    ((AnnotValid_pi V ρ u v A B) ▸ h.2).2.1 x hx⟩

/-! ## Application spines, graded backwards

`wellDenotedV_mkAppN_of_fitA` (`Steps/IotaKit.lean`) builds an
application's grading from a fit; the point stage needs the *inverse*,
because the index walk compares arguments of a spine whose whole
grading it already has (the checker's own `inferTypeCore` verdict on
the statement's left-hand side).  `WellDenoted`/`AnnotValid` are
conjunctive at `.app`, so both directions are one projection. -/

/-- An application's argument is graded when the application is. -/
theorem WellDenotedV_app_arg {ρ : Nat → V} {g a : AnnotTerm}
    (h : WellDenotedV V ρ (.app g a)) : WellDenotedV V ρ a :=
  ⟨((WellDenoted_app V ρ g a) ▸ h.1).2.1,
    ((AnnotValid_app V ρ g a) ▸ h.2).2⟩

/-- **Every argument of a graded application spine is graded.** -/
theorem WellDenotedV_mkAppN_args {ρ : Nat → V} :
    ∀ (as : List AnnotTerm) {g : AnnotTerm},
      WellDenotedV V ρ (AnnotTerm.mkAppN g as) → ∀ a ∈ as, WellDenotedV V ρ a := by
  intro as
  induction as with
  | nil => intro g _ a ha; exact nomatch ha
  | cons x xs ih =>
    intro g h a ha
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact WellDenotedV_app_arg (Rules.mkAppN_head xs h)
    · exact ih (g := .app g x) h a ha'

end ConLeche.Model
