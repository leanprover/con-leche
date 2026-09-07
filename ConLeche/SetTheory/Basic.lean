import Lech.SetTheory.Core
import Lech.SetTheory.Derive.Sigma
import Lech.SetTheory.Derive.Natrec
import Lech.SetTheory.Derive.Quot
import Lech.SetTheory.Derive.Choice
import Lech.SetTheory.Derive.PtFresh
import Lech.SetTheory.Derive.Lfp
import Lech.SetTheory.Derive.LfpFam

/-!
# The target set theory: the derived operator interface

The set theory in which the checker's soundness model lives.  All
consistency proofs are parametric in a type `V` carrying a `SetTheory`
instance, so the final result reads:

> Assuming Tarski–Grothendieck set theory has a model, every environment
> accepted by the checker has a model; in particular no proof of `Empty`
> is ever accepted.

The axiomatic content is exactly the `SetTheory` class of
`Lech/SetTheory/Core.lean`: membership, extensionality, pairing,
union, power set, regularity, Lean-level replacement, and Tarski's
Axiom A with a transitivity clause.  The instance existence is the
"extra assumption for cardinality reasons" mentioned in the design:
inside Lean one can construct such a `V` from `ZFSet`-style
constructions plus universe assumptions (cf. lean4lean-model), but the
checker's verification does not depend on how `V` is obtained.

Every operator and law the model construction consumes — `pi`, `lam`,
`app`, the universe tower `univ`, the proof point `pt`, `eqv`,
`unitSet`, `omega` with `natrec`, `sigmaSet` with its projections,
quotients, `prop_ext`, the global selector `schoice` — is a
`noncomputable def`/`theorem` in the `SetTheory` namespace, *derived*
from the class in `Lech/SetTheory/Derive/*` (which see for each
operator's realization and its documentation).  Importing this module
provides the whole surface.

Most interface names coincide with the derivation's own names and are
re-exported by the imports above; this file supplies the remaining
interface-shaped statements (naturals under their `nat*` names, laws
phrased against `univ 0` rather than its value `univZero`, and the
elimination/beta laws with the unconditional fibre-universe premise).
-/

namespace Lech.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- Members of `univ 0` (propositions) have at most the proof point as
element. -/
theorem mem_univ_zero {T x : V} (hT : T ∈ˢ (univ 0 : V)) (hx : x ∈ˢ T) :
    x = pt :=
  eq_pt_of_mem_univZero (univ_zero (V := V) ▸ hT) hx

/-- Elimination: application stays in the fibre.  The fibre-universe
premise makes the `v = 0` case realizable (fibres are then truth
values, so the inhabited fibre is the singleton of `•`). -/
theorem app_mem {v : Nat} {A f a : V} {B : V → V}
    (hf : f ∈ˢ pi v A B) (ha : a ∈ˢ A)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V)) : app f a ∈ˢ B a :=
  app_mem' hf ha (fun hv x hx => by subst hv; exact univ_zero (V := V) ▸ hB x hx)

/-- Beta: conditional on membership, as set-theoretic functions have set
domains. -/
theorem app_lam {v : Nat} {A a : V} {F B : V → V}
    (ha : a ∈ˢ A) (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x)
    (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V)) : app (lam v A F) a = F a :=
  app_lam' ha hF (fun hv x hx => by subst hv; exact univ_zero (V := V) ▸ hB x hx)

/-- Truth values for equality: `eqv x y` is `{pt}` if `x = y` and `∅`
otherwise. -/
theorem eqv_mem_univ (x y : V) : eqv x y ∈ˢ (univ 0 : V) :=
  (univ_zero (V := V)).symm ▸ eqv_mem_univZero x y

theorem mem_eqv {a x y : V} (h : a ∈ˢ eqv x y) : x = y :=
  eq_of_mem_eqv h

/-- The canonical singleton `{pt}` has only the proof point as member. -/
theorem mem_unitSet {x : V} (h : x ∈ˢ (unitSet : V)) : x = pt :=
  mem_unitSet_iff.mp h

theorem omega_mem_univ : (omega : V) ∈ˢ univ 1 :=
  omega_mem_univ_succ 0

/-- The model of `Nat.zero`: the empty set, i.e. the ordinal `0`. -/
noncomputable def natzero : V := empty

/-- The model of `Nat.succ`: the von Neumann successor. -/
noncomputable def natsucc : V → V := vsucc

theorem natzero_mem : (natzero : V) ∈ˢ omega := empty_mem_omega

theorem natsucc_mem {n : V} (hn : n ∈ˢ (omega : V)) : natsucc n ∈ˢ omega :=
  vsucc_mem_omega hn

theorem natrec_zero (z s : V) : natrec z s natzero = z :=
  natrec_empty z s

theorem natrec_succ (z s : V) {n : V} (hn : n ∈ˢ (omega : V)) :
    natrec z s (natsucc n) = app (app s n) (natrec z s n) :=
  natrec_vsucc z s hn

/-- The recursion theorem plus induction: `natrec`'s value inhabits the
motive's fibre, with the motive `M` applied as a set-theoretic
function. -/
theorem natrec_mem {M z s n : V}
    (hz : z ∈ˢ app M natzero)
    (hs : ∀ k, k ∈ˢ (omega : V) → ∀ ih, ih ∈ˢ app M k →
      app (app s k) ih ∈ˢ app M (natsucc k))
    (hn : n ∈ˢ (omega : V)) : natrec z s n ∈ˢ app M n :=
  natrec_mem_vsucc hz hs hn

/-- Extensionality of propositions: members of `univ 0` with the same
proof-point membership are equal (propositions are subsets of `{pt}`). -/
theorem prop_ext {A B : V} (hA : A ∈ˢ (univ 0 : V)) (hB : B ∈ˢ (univ 0 : V))
    (hab : (pt : V) ∈ˢ A → pt ∈ˢ B) (hba : (pt : V) ∈ˢ B → pt ∈ˢ A) : A = B :=
  univZero_ext (univ_zero (V := V) ▸ hA) (univ_zero (V := V) ▸ hB) hab hba

/- Opaque interface operators (see `Derive/Empty.lean`). -/
attribute [irreducible] natzero natsucc

end Lech.SetTheory
