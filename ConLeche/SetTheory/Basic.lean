module

public import ConLeche.SetTheory.Derive.Natrec
public import ConLeche.SetTheory.Derive.Univ

@[expose] public section

/-!
# The target set theory: the derived operator interface

The set theory in which the checker's soundness model lives.  All
consistency proofs are parametric in a type `V` carrying a `SetTheory`
instance, so the final result reads:

> Assuming ZFC + countably many Grothendieck universes has a model, every
> environment accepted by the checker has a model; in particular no proof
> of `Empty` is ever accepted.

The axiomatic content is strictly first-order in the `SetTheory` class
of `ConLeche/SetTheory/Core.lean`: membership, extensionality, pairing,
union, power set, regularity, the first-order replacement schema over
`Formula`, Jech's internal Axiom of Choice, and an ω-indexed Grothendieck
universe tower (`IsGrothendieck`).  The instance existence is the
"extra assumption for cardinality reasons" mentioned in the design:
inside Lean one can construct such a `V` from `ZFSet`-style
constructions plus universe assumptions (cf. lean4lean-model), but the
checker's verification does not depend on how `V` is obtained.

Every operator and law the model construction consumes — `pi`, `lam`,
`app`, the universe tower `univ`, the proof point `pt`, `eqv`,
`unitSet`, `omega` with `natrec`, `sigmaSet` with its projections,
quotients, `prop_ext`, the universe choice functions `univChoiceFn` /
`piSet_choose` — is a `noncomputable def`/`theorem` in the `SetTheory`
namespace, *derived* from the class in `ConLeche/SetTheory/Derive/*`
(which see for each operator's realization and its documentation).
Importing this module provides the whole surface.

Most interface names coincide with the derivation's own names and are
re-exported by the imports above; this file supplies the remaining
interface-shaped statements (naturals under their `nat*` names, laws
phrased against `univ 0` rather than its value `univZero`, and the
elimination/beta laws with the unconditional fibre-universe premise).
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- Members of `univ 0` (propositions) have at most the proof point as
element. -/
theorem mem_univ_zero {T x : V} (hT : T ∈ˢ (univ 0 : V)) (hx : x ∈ˢ T) :
    x = pt :=
  eq_pt_of_mem_univZero (univ_zero (V := V) ▸ hT) hx

/-- Truth values for equality: `eqv x y` is `{pt}` if `x = y` and `∅`
otherwise. -/
theorem eqv_mem_univ (x y : V) : eqv x y ∈ˢ (univ 0 : V) :=
  (univ_zero (V := V)).symm ▸ eqv_mem_univZero x y

/-- The model of `Nat.zero`: the empty set, i.e. the ordinal `0`. -/
noncomputable def natzero : V := empty

/-- The model of `Nat.succ`: the von Neumann successor. -/
noncomputable def natsucc : V → V := vsucc

theorem DefFun.natzero {k : Nat} : DefFun k fun _ => (natzero : V) :=
  DefFun.empty

theorem DefFun.natsucc_apply {k : Nat} {A : (Fin k → V) → V} (hA : DefFun k A) :
    DefFun k fun env => natsucc (A env) :=
  DefFun.vsucc_apply hA

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

end ConLeche.SetTheory
