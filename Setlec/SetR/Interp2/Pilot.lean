import Setlec.SetR.Interp2.Ops

/-!
# The second soundness — feasibility pilots (task #151 tier C)

Before any T4 motive is re-signed over `interp2`, the two lemmas the
whole removal campaign stands on are proved here in isolation — the
B5-style discipline: a feasibility check is a theorem or a
countermodel, never a plan.

**Pilot 1 — graded beta** (`graded_beta_pos`): at a λ whose codomain
kind is provably nonzero, the application slot's *kinded* package plus
the λ's own fibre package give β **with no argument re-check** — the
slot pins the domain through graph rigidity (`piR_dom_unique`, no side
condition), which is the #49 domain-determination argument made sound
by the collapse's removal.  This is the fact whose runtime twin is the
per-redex beta certificate (family 2, 25–48 % of the tax).

**Pilot 2 — slot pinning at a telescope step** (`slot_pins_domain`):
at a positive-kind product, an application slot's membership pins the
domain *even when the slot's own type is a proposition* — what matters
is the kind of the remaining telescope.  Iterated along a stored
recursor type (whose slot kinds are static and install-sort-checked),
this is the fact whose runtime twin is the per-fire telescope
certification (families 0/1, 7–15 % of the tax); the walk survives
only at `Prop`-motive fires.

**The residue, on the record**: at a `Prop`-kind product (`v' = 0`)
the slot cannot pin the domain — `piR 0 A B` is a truth value and
forgets `A` (impredicativity, the same analysis as tasks #49/#73) —
and the reduct-side value is only the canonical proof *on* the domain.
So the removals land as O(1) kind gates with a `Prop`-codomain
residue, not as unconditional deletions.  The residue's necessity is
task #73's finding, unchanged by the regime split; it is not
re-mechanized here.
-/

namespace Setlec.SetR.Interp2

open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- The kinded application-slot package — `AnnotOkV`'s app slot with
the product kind carried (the second soundness's `AnnotOk2` upgrade). -/
def AppSlot2 (f a : V) : Prop :=
  ∃ (v : Nat) (A : V) (B : V → V), f ∈ˢ piR v A B ∧ a ∈ˢ A

/-- The λ fibre package at the node's own annotation — what
`Annotates.lam`'s cached codomain sort is worth semantically: fibres
exist, and at kind `0` they are truth values (the codomain is a
proposition). -/
def LamPkg2 (v : Nat) (A : V) (F : V → V) : Prop :=
  ∃ B : V → V, (∀ x, x ∈ˢ A → F x ∈ˢ B x) ∧
    (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))

/-- **Pilot 1 — graded beta at a positive codomain kind.**  β with no
argument re-check: the slot's membership is at *some* product, the λ's
own package puts it at *its* product, positivity makes both graphs,
and graphs determine their domains. -/
theorem graded_beta_pos {v : Nat} (hv : v ≠ 0) {A a : V} {F : V → V}
    (hslot : AppSlot2 (lamR v A F) a)
    (hpkg : LamPkg2 v A F) :
    app (lamR v A F) a = F a := by
  obtain ⟨v', A', B', hf, ha⟩ := hslot
  obtain ⟨B, hB, -⟩ := hpkg
  -- the slot's product is in the graph regime too: the λ is not `pt`
  have hv' : v' ≠ 0 := by
    intro h0
    subst h0
    exact lamR_ne_pt hv (eq_pt_of_mem_piR_zero hf)
  -- rigidity pins the slot's domain to the λ's own
  have hAA : A = A' :=
    piR_dom_unique hv hv' (lamR_mem hB) hf
  exact app_lamR_pos hv (hAA ▸ ha)

/-- **Pilot 2 — the telescope pinning step.**  At a positive-kind
product the slot's membership recovers the *stored* domain membership
and the walk's next membership — even when the slot's own type is a
proposition.  This is one step of the iota telescope walk with the
runtime certificate replaced by graph rigidity. -/
theorem slot_pins_domain {v v' : Nat} (hv : v ≠ 0) (hv' : v' ≠ 0)
    {A A' f a : V} {B B' : V → V}
    (hstored : f ∈ˢ piR v A B)
    (hslot : f ∈ˢ piR v' A' B')
    (ha : a ∈ˢ A') :
    a ∈ˢ A ∧ app f a ∈ˢ B a := by
  have hAA : A' = A := piR_dom_unique hv' hv hslot hstored
  subst hAA
  exact ⟨ha, app_mem_piR_pos hv hstored ha⟩

end Setlec.SetR.Interp2
