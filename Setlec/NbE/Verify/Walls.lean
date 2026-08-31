import Setlec.NbE.Verify.Conv

/-!
# NbE pilot: the walls, named precisely

The proved artifacts of this pilot (`Verify/Eval.lean`,
`Verify/Conv.lean`) are all *conditional on ledgers*: `EvalOk`
(one membership per β event), `ConvOk` (fresh-variable coherence and
δ-coherence per conversion event), `EnvOk` (constants denote their
bodies).  This module names, as precise `Prop`s, what remains between
those artifacts and an unconditional consistency statement — and
proves the *assembly*: the walls below are jointly **sufficient**
(given `FrontDoorAdequacy`, a consistency-style corollary follows,
`no_universal_inhabitant_of_adequacy`), so they are the exact frontier,
not an underestimate.

## Wall 1 — front-door adequacy (the typed logical relation)

`FrontDoorAdequacy`/`InferAdequacyStmt`: acceptance implies semantic
typing and implies the ledgers.  The naive induction on `infer` fails
at exactly one clause: **the λ case**.  `infer` visits the body once,
under the single fresh variable `freshV k`; but the conclusion
(membership of the λ's denotation in the Π's) and the ledger of any
*later* β event both quantify over **every** `x ∈ˢ ⟦dom⟧`.  The fix is
the standard one — strengthen the induction to a Kripke-style logical
relation over semantic environments (`ρ`-entries related to
`Γ`-entries at all extensions of `σ`) — and that is the same *kind* of
proof the main campaign's typing-premise tier is; NbE does not remove
it.  What NbE removes is the need for that relation to be stable under
*syntactic substitution* — there is none — which in the main campaign
is the multiplicative factor (every transport lemma × every rewrite
site).  Here the relation composes with `eval`'s environment extension
definitionally.

## Wall 2 — readback coherence

`QuoteCoherenceStmt`: `quote` inverts denotation up to the fresh-frame
environment.  Needed because `infer`'s λ case *re-closes* the body's
inferred type value through `quote` (the one place NbE forces readback
into the checking path).  Statable crisply thanks to gluing (readback
never unfolds); provable by the same fuel-induction pattern as
`conv_sound` with `EvalOk` premises at closure applications; not
attempted in this slice.

## Wall 3 — ledger transport along forcing

`forceV`/`toPi`/`toSort` return *unfolded* views; adequacy must carry
`EvalOk`/`ArgsOk` facts across `unfoldNeu` chains (the premises of
`unfoldNeu_sound`, iterated).  Mechanical given walls 1–2 (each step
is `unfoldNeu_sound` plus `EnvOk`), but it is a real induction and
its statement must be fuel-monotone (the machine consumes fuel while
the ledger is stated at the entry fuel) — the pilot's fueled mirrors
are aligned per-call today, and a production proof wants
fuel-monotonicity lemmas for the mirrors (the standard
`lean-fuel-induction` suffix pattern).

## What is *not* a wall here

* **Cross-run sort agreement (main campaign hard class 2).**  In this
  regime conversion's fresh variables carry no types and no sorts;
  sorts are compared only as carried `Level` syntax at `sort`/`sort`
  leaves, and the model is consulted only forward (`univ ∘ eval φ`) —
  never asked to recover a level from a set.  The two sides of a defeq
  never manufacture types independently: `infer` runs once, before
  values exist.  Nothing in walls 1–3 requires arbitrating two runs'
  levels against each other.
* **Substitution transport (hard class 1).**  No term substitution
  exists in the implementation; the only transport lemma is the level
  one (`dTerm_instL`), unconditional, 20 lines.

## Where proof irrelevance would enter (second-slice, hard class 3)

`conv` compares values untyped.  Kernel-grade proof irrelevance
identifies `v ≡ w` whenever their common *type* is a `Prop` — a fact
about types of values the machine deliberately does not carry.  The
official kernel and nanoda solve it by *inferring the types of both
sides inside `is_def_eq`*; in this regime that means `quote` + `infer`
from within `conv` (readback of the compared values, then a typing
run) — a type-computation channel into the untyped comparison, paid
per proof-irrelevance probe.  Model-side the collapse makes the rule
sound nearly for free (`mem_univ_zero`: members of a `univ 0` set are
all `pt`), *given* exactly the two memberships
`⟦v⟧ ∈ˢ P`, `⟦w⟧ ∈ˢ P`, `P ∈ˢ univ 0` — one more ledger clause, of
the same species as `ApplyOk`.  So the cost is implementation-side
(the typing channel), not model-side; the "kernel is safe only on what
it has typed" boundary reappears as: the ledger for a proof-irrelevance
event can only be discharged for values the front door typed.
-/

namespace Setlec.NbE

open Setlec.SetTheory

universe u

variable (V : Type u) [SetTheory V]

/-- **Wall 1 (declaration form).**  Acceptance implies semantic typing
of the declaration.  This is the pilot's exact analogue of the main
campaign's checker-soundness statement; everything else in this
development is proved, conditional on ledgers this statement's proof
would discharge. -/
def FrontDoorAdequacy : Prop :=
  ∀ (E : Env) (κ : Name → List Nat → V) (φ : Name → Nat),
    EnvOk κ E →
    ∀ (fuel : Nat) (ci : ConstInfo), checkDecl E ci fuel = true →
      dTerm κ φ [] ci.value ∈ˢ dTerm κ φ [] ci.type

/-- **Wall 1 (induction form).**  The statement the logical relation
must establish for `infer`; the λ clause is where the naive structural
induction fails (see the module docstring).  The context premise
relates `ρ`-values to `Γ`-types pointwise — the Kripke strengthening
quantifies this over all `σ`-extensions. -/
def InferAdequacyStmt : Prop :=
  ∀ (E : Env) (κ : Name → List Nat → V) (φ : Name → Nat) (σ : Nat → V),
    EnvOk κ E →
    ∀ (fuel k : Nat) (Γ ρ : List Value) (t : Term) (T : Value),
      infer E fuel k Γ ρ t = some T →
      (∀ (i : Nat) (v Tv : Value), ρ[i]? = some v → Γ[i]? = some Tv →
        dVal κ φ σ v ∈ˢ dVal κ φ σ Tv) →
      EvalOk κ φ σ E fuel ρ t ∧
      ∀ v, eval E fuel ρ t = some v → dVal κ φ σ v ∈ˢ dVal κ φ σ T

/-- **Wall 2.**  Readback coherence: quoting at frontier `k` inverts
denotation against the fresh-frame environment
`[σ (k-1), …, σ 0]`. -/
def QuoteCoherenceStmt : Prop :=
  ∀ (E : Env) (κ : Name → List Nat → V) (φ : Name → Nat) (σ : Nat → V)
    (fuel k : Nat) (v : Value) (t : Term),
    quote E fuel k v = some t → ScopedV k v →
    dTerm κ φ ((List.range k).reverse.map σ) t = dVal κ φ σ v

/-- **The assembly**: wall 1 alone already yields a consistency-style
corollary for this slice — no accepted definition can inhabit
`∀ (A : Sort 1), A` over a sound environment.  (The slice has no
`Empty`; the universal type is its stand-in: its denotation would
have a member in every member of `univ 1`, in particular in `∅`.)
This shows the walls are jointly sufficient, i.e. the frontier is
exactly as named, and the pilot's conditional artifacts compose. -/
theorem no_universal_inhabitant_of_adequacy
    (hFDA : FrontDoorAdequacy V)
    {E : Env} {κ : Name → List Nat → V} (hE : EnvOk κ E)
    {fuel : Nat} {ci : ConstInfo}
    (hty : ci.type = .pi (.sort (.succ .zero)) (.bvar 0))
    (hcd : checkDecl E ci fuel = true) : False := by
  have h := hFDA E κ (fun _ => 0) hE fuel ci hcd
  rw [hty] at h
  have h2 : dTerm κ (fun _ => 0) ([] : List V) ci.value ∈ˢ
      piC (univ 1 : V) (fun x => x) := by
    simpa [dTerm, Level.eval] using h
  have h3 := app_mem_piC h2 (empty_mem_univ 1)
  exact not_mem_empty _ h3

/-- Vacuity probe for the assembly: the premise pair
(`EnvOk` for the empty environment, an accepted declaration) is
satisfiable — `EnvOk` holds vacuously for `⟨[]⟩`, and `NbETests`
exhibits accepted declarations — so the corollary's contradiction has
real reach: it genuinely constrains `FrontDoorAdequacy`'s content
rather than following from an unsatisfiable antecedent. -/
theorem envOk_empty (κ : Name → List Nat → V) : EnvOk κ ⟨[]⟩ := by
  intro ci hci
  simp at hci

end Setlec.NbE
