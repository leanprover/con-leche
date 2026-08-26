import Setlec.TT.Semantics.Consistency
import Setlec.TT.Deq

/-!
# REFUTATION: level-guarded Π-domain-injectivity (Q1)

The F2/#125 record refuted derivable Π-injectivity **at `Prop`** via
`propext` and noted that "a level-guarded variant is not refuted by
this argument".  With typing premises now permitted on admissibility
statements, the guarded variant can be stated:

> `Deq Γ (pi A B) (pi A' B')`, with both `pi` types typed at
> `sort (u+1)` (so not `Prop`) — then `Deq Γ A A'`.

**It is refuted too.**  The generator the F2 argument did not have to
consider is the *context*: in a layer with equality reflection, a
hypothesis `h : L = R` derives `Deq Γ L R` in one `bvar`, so an
admissible injectivity must survive every equation a binder can
introduce — and binder types are arbitrary (`eqE _ L R : Sort 0`
unconditionally), so the context below arises from a perfectly typable
closed term, e.g. `fun (h : (Nat → Empty.{1}) = (PUnit.{1} → Empty.{1})) => h`.

Semantically, `Π` at `sort (u+1)` is still non-injective on **empty
function spaces**: `Nat → Empty.{1}` and `PUnit.{1} → Empty.{1}` are
both typed at `sort 1` and both denote `∅` (`piC_prop_eq` with empty
fibres), so the context is **satisfiable** — the equation is true — yet
`⟦Nat⟧ = ω ≠ {pt} = ⟦PUnit⟧`, so soundness at the satisfying valuation
refutes the conclusion `Deq Γ Nat PUnit.{1}`.

The satisfiability is the load-bearing part: in an *unsatisfiable*
context nothing is semantically refutable, so this witness is the only
kind that can exist — and it does.

What the witness does **not** kill, recorded for the design's sake:
the variant with an *inhabitation* premise (`Γ ⊢ f : pi A B` for some
`f`).  Here no `f` exists (the type is empty, the context satisfiable,
soundness forbids it).  That variant is semantically valid in the
model — but it is not *derivable-as-admissible* by any induction the
layer offers (a `conv`-retyped `prf` reaches the equation's `Prop`
from any inhabited `Prop`, so derivations of equations do not
decompose), leaving it a conjecture per the §3.1 house rule.
-/

namespace Setlec.TT
namespace Spike

open VExpr SetTheory

/-- `Nat → Empty.{1}` — a `sort 1` type denoting `∅`. -/
def L : VExpr := .pi natT (emptyT 1)

/-- `PUnit.{1} → Empty.{1}` — a `sort 1` type denoting `∅`. -/
def R : VExpr := .pi (punitT 1) (emptyT 1)

/-- The context: one hypothesis, `h : L = R`.  It is the binder context
of the closed, typable term `fun (h : eqE (sort 1) L R) => h`. -/
def GammaLR : List VExpr := [.eqE (.sort 1) L R]

/-- The binder type is well-formed: the term producing the context is
closed and typable. -/
theorem context_from_typable_term :
    HasType [] (.lam (.eqE (.sort 1) L R) (.bvar 0))
      (.pi (.eqE (.sort 1) L R) ((VExpr.eqE (.sort 1) L R).liftN 1)) :=
  .lam (.bvar (A := .eqE (.sort 1) L R) rfl)

/-- The hypothesis reflects: `Deq GammaLR L R` in one `bvar`. -/
theorem deq_L_R : Deq GammaLR L R :=
  Deq.intro (T := .sort 1) (p := .bvar 0)
    (HasType.bvar (Γ := GammaLR) (i := 0) (A := .eqE (.sort 1) L R) rfl)

/-- The guard, left side: `L : sort 1` — not a `Prop`. -/
theorem L_sort1 : HasType GammaLR L (.sort 1) :=
  .pi (u := 1) (v := 1) .const .const

/-- The guard, right side: `R : sort 1` — not a `Prop`. -/
theorem R_sort1 : HasType GammaLR R (.sort 1) :=
  .pi (u := 1) (v := 1) .const .const

section Model

universe w
variable (V : Type w) [SetTheory V]

/-- The satisfying valuation: the hypothesis is a *true* equation, so
`pt` witnesses it. -/
noncomputable def rhoLR : Nat → V := fun _ => SetTheory.pt

/-- A function space with inhabited domain and empty fibres is empty. -/
theorem piC_into_empty_eq_empty {A : V} {x : V} (hx : x ∈ˢ A) :
    piC A (fun _ => (SetTheory.empty : V)) = SetTheory.empty := by
  rw [piC_prop_eq (fun _ _ => univ_zero (V := V) ▸ empty_mem_univ 0)]
  exact truthVal_eq_empty fun h => not_mem_empty _ (h x hx).choose_spec

/-- `⟦L⟧ = ∅`. -/
theorem interp_L_empty (ρ : Nat → V) :
    interp V ρ L = SetTheory.empty := by
  show piC (omega : V) (fun _ => SetTheory.empty) = SetTheory.empty
  exact piC_into_empty_eq_empty V natzero_mem

/-- `⟦R⟧ = ∅`. -/
theorem interp_R_empty (ρ : Nat → V) :
    interp V ρ R = SetTheory.empty := by
  show piC (unitSet : V) (fun _ => SetTheory.empty) = SetTheory.empty
  exact piC_into_empty_eq_empty V pt_mem_unitSet

/-- **The context is satisfiable** — the refutation is not vacuous. -/
theorem sat_GammaLR : Sat V GammaLR (rhoLR V) := by
  intro i A hi
  match i, hi with
  | 0, hi =>
    cases hi
    show (pt : V) ∈ˢ interp V _ (.eqE (.sort 1) L R)
    rw [interp_eqE, interp_L_empty, interp_R_empty]
    exact pt_mem_eqv_self _

/-- `natzero` is the empty set (the ordinal `0`). -/
theorem natzero_eq_empty : (natzero : V) = SetTheory.empty := by
  unfold natzero
  rfl

/-- `ω ≠ {pt}`: the model separates `Nat` from `PUnit`. -/
theorem omega_ne_unitSet : (omega : V) ≠ unitSet := by
  intro h
  have h0 : (natzero : V) = pt := mem_unitSet (h ▸ natzero_mem)
  exact pt_ne_empty (h0 ▸ natzero_eq_empty V)

end Model

/-- **The refutation.**  Level-guarded Π-domain-injectivity — even with
typing premises putting both `pi` types at successor sorts — is
inadmissible: this instance's premises are derivable (in a satisfiable
context arising from a closed typable term) and its conclusion is
refuted by soundness at the satisfying valuation. -/
theorem guarded_pi_domain_injectivity_refuted
    (V : Type w) [SetTheory V] :
    ¬ ∀ (Γ : List VExpr) (A B A' B' : VExpr) (u u' : Nat),
        Deq Γ (.pi A B) (.pi A' B') →
        HasType Γ (.pi A B) (.sort (u + 1)) →
        HasType Γ (.pi A' B') (.sort (u' + 1)) →
        Deq Γ A A' := by
  intro hinj
  have hd : Deq GammaLR natT (punitT 1) :=
    hinj GammaLR natT (emptyT 1) (punitT 1) (emptyT 1) 0 0
      deq_L_R L_sort1 R_sort1
  have hs := (hd.toHasType (.sort 1)).sound V (rhoLR V) (sat_GammaLR V)
  rw [interp_eqE] at hs
  exact omega_ne_unitSet V (mem_eqv hs)

end Spike
end Setlec.TT
