import ConLeche.SetBase.Ops

/-!
# ROUND D PART 1 — ARCHIVE (route RETIRED before completion)

**Status: retired.**  Round D (the pw-gated application-argument
re-check, harvest sites 9/10/11/12) was withdrawn from the de-gating
harvest by user ruling while this probe was in flight:

> "a front door check where the official kernel also does a defeq,
>  and rightly so."

The `inferSpineI` domain `defeq` (sites 11/12) **is the application
typing rule's own premise**, not certificate tax; masking it weakens
the checker below official kernel semantics.  Neither the totalized
function space nor a domain-nonemptiness `BinderMeta` datum is
pursued.  Everything below is kept as the *record* of what was
established before the retirement, and as a permanent set of
no-go theorems so the routes are not re-opened.

This file is **not** in any `lake` library root: nothing imports it,
`lake build` never compiles it.  Check it with

    lake env lean _probe/TotalizeD1.lean

## What is proved here

1. `app_lamT` / `app_lamT_off_carrier` — the totalized encoding's β.
   Totalization makes β hold for every argument **in the carrier**,
   with no reference to the binder's domain `A`.  It does **not**
   make β unconditional: off the carrier the value is canonical junk,
   exactly as it is off the domain today.  Totalization *relocates*
   the side condition (`a ∈ˢ A` ↦ `a ∈ˢ U`); it does not remove it.
   This is the coordinator's kill-note, mechanized.

2. `no_membership_free_elim` — **the encoding-independent no-go.**
   For *any* triple of operators `piX / lamX / appX` on any
   `SetTheory V` satisfying the ordinary introduction rule, the
   membership-free elimination rule
   `f ∈ˢ piX A B → ∀ a, appX f a ∈ˢ B a` is **false**.  The witness is
   the empty domain with empty fibres.  So the goal the site-11/12
   mask leaves open (`⟦f a⟧ ∈ˢ ⟦B[a]⟧` with nothing known about
   `⟦a⟧`) is unreachable by *any* model swap whatsoever — not by
   totalization, not by a nonemptiness datum, not by an encoding
   nobody has thought of yet.  The route was dead on arrival for
   this site.

3. `graph_not_mem_of_isTGUniverse` / `lamT_not_mem_univ` — **the
   universe-placement no-go for totalization.**  A function graph
   whose domain is a Grothendieck universe `U` is never a member of
   `U`: `⋃⋃` of the graph contains its domain, and `U` is closed
   under `⋃` and under subsets of members, so `graph F U ∈ˢ U` would
   give `U ∈ˢ U`.  Hence a λ totalized over the level-`ℓ` carrier
   `univ ℓ` cannot be placed at level `ℓ`; every abstraction would
   jump a universe, and the whole placement battery
   (`piC_mem_univ` and the 75 `piR_zero_mem_univZero` consumers)
   would have to be restated at `ℓ+1`.  Independent of (1): even if
   a carrier bound *were* available at the `.lam` node — it is not,
   see the DESIGN record — the placement is refuted.

## What is *not* here, and why

No totalized `interp2`, no law-battery re-proofs, no swap.  The
carrier bound the encoding needs does not exist at the interpretation
site: `AVExpr.lam` carries **one** numeral, the *codomain* sort `v`
(`ConLeche/SetR/Annot/Syntax.lean`), and `interp2`'s `.lam` clause reads
only that.  The domain's sort was deliberately dropped from the
annotation ("no consumer reads it"), and `Red.beta`'s subject
`.app (.lam A b) a` has a λ whose domain sort **no premise supplies**
(`ConLeche/SetR/Annot/Pass.lean`, the existence-theorem docstring).
`pw` is a zero-ness bit, not a level.  Supplying the bound is an
`AVExpr`/`Annotates`/tier-A-B-C change; it was never started.
-/

namespace ConLeche.SetR.Interp2.ProbeD1

open ConLeche ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## 1. The totalized encoding, and what its β actually says -/

/-- Totalized abstraction: the graph over the **carrier** `U`, not over
the binder's domain `A`.  (`lamR`'s graph regime is `graph F A`; this
is the same operator at a different, larger, index.) -/
noncomputable def lamT (U : V) (F : V → V) : V := graph F U

/-- Totalized product: the total single-valued graphs on the carrier
whose values land in the fibres.  Stated for completeness; only its
domain slot matters below. -/
noncomputable def piT (U : V) (B : V → V) : V := piSet U B

/-- **β on the carrier, with no reference to the binder's domain.**
This is the totalization prize, in full: the argument's membership in
`A` is gone from the statement. -/
theorem app_lamT {U a : V} {F : V → V} (ha : a ∈ˢ U) :
    app (lamT U F) a = F a :=
  app_graph ha

/-- **…and this is the whole of the kill-note.**  Off the carrier the
totalized abstraction applies to canonical junk, exactly as today's
`lamR` does off its domain (`app_lamR_of_not_mem`).  Totalization
*moves* the side condition from `a ∈ˢ A` to `a ∈ˢ U`; it never
discharges one.  Since the masked checker learns nothing at all about
the argument, `a ∈ˢ U` is no more available to it than `a ∈ˢ A` was. -/
theorem app_lamT_off_carrier {U a : V} {F : V → V} (ha : ¬ a ∈ˢ U) :
    app (lamT U F) a = (empty : V) :=
  app_graph_of_not_mem ha

/-! ## 2. The encoding-independent no-go

The site-11/12 mask deletes the argument's `defeq` against the
domain, so the P-tier goal at that site — `⟦f a⟧ ∈ˢ ⟦B[a]⟧`, i.e.
`app_mem_piR` with its `ha : a ∈ˢ A` premise removed — must be
discharged with *nothing* known about the argument.  The following
says no set-theoretic function-space encoding can do that. -/

/-- **No function-space encoding admits membership-free elimination.**
Any `piX`/`lamX`/`appX` with the ordinary introduction rule refutes
the elimination rule stated without a domain-membership premise.

Witness: the empty domain with everywhere-empty fibres.  Introduction
is vacuous there (`∀ x ∈ˢ ∅, …`), so *some* value inhabits
`piX ∅ (fun _ => ∅)`; membership-free elimination then puts a value
in `∅`.

Note what is *not* assumed: nothing about `appX`, nothing about `piX`
beyond the introduction rule, no extensionality, no graph structure.
In particular the hypothesis is satisfied by `lamR`/`piR`/`app`
(`lamR_mem`), by `lamT`/`piT`/`app` (`graph_mem_piSet`), and by any
successor encoding. -/
theorem no_membership_free_elim
    (piX : V → (V → V) → V) (lamX : V → (V → V) → V) (appX : V → V → V)
    (intro : ∀ (A : V) (F B : V → V),
      (∀ x, x ∈ˢ A → F x ∈ˢ B x) → lamX A F ∈ˢ piX A B)
    (elim : ∀ (A f a : V) (B : V → V),
      f ∈ˢ piX A B → appX f a ∈ˢ B a) :
    False := by
  have hmem : lamX (empty : V) (fun x => x) ∈ˢ piX (empty : V) (fun _ => empty) :=
    intro empty (fun x => x) (fun _ => empty)
      (fun x hx => absurd hx (not_mem_empty x))
  exact not_mem_empty _
    (elim empty (lamX (empty : V) (fun x => x)) empty (fun _ => empty) hmem)

/-- The same refutation, spelled out against the *actual* operators the
sealed P tier uses: `app_mem_piR_pos` cannot have its `ha` premise
dropped. -/
theorem app_mem_piR_pos_needs_ha
    (bad : ∀ {v : Nat} {A f a : V} {B : V → V}, v ≠ 0 →
      f ∈ˢ piR v A B → app f a ∈ˢ B a) :
    False :=
  no_membership_free_elim (V := V) (piR 1) (lamR 1) app
    (fun _A _F _B hF => lamR_mem hF)
    (fun _A _f _a _B hf => bad Nat.one_ne_zero hf)

/-! ## 3. The universe-placement no-go for totalization -/

/-- `⋃⋃` of a function graph contains the graph's domain: from
`x ∈ˢ A` we get `⟨x, F x⟩ = {{x},{x,F x}} ∈ˢ graph F A`, hence
`{x} ∈ˢ ⋃ (graph F A)`, hence `x ∈ˢ ⋃⋃ (graph F A)`. -/
theorem dom_subset_sUnion_sUnion_graph {A : V} (F : V → V) :
    A ⊆ˢ sUnion (sUnion (graph F A)) := by
  intro x hx
  refine mem_sUnion.mpr ⟨sing x, ?_, mem_sing.mpr rfl⟩
  refine mem_sUnion.mpr ⟨kpair x (F x), mem_graph.mpr ⟨x, hx, rfl⟩, ?_⟩
  exact mem_upair_left _ _

/-- **A totalized abstraction over a universe is never in that
universe.**  Grothendieck universes are closed under `⋃` and under
subsets of members, so `graph F U ∈ˢ U` would put `U` inside itself. -/
theorem graph_not_mem_of_isTGUniverse {U : V}
    (hU : IsTGUniverse (Mem (V := V)) U) (F : V → V) :
    ¬ graph F U ∈ˢ U := by
  intro hg
  exact not_mem_self U
    (hU.mem_of_subset_mem (hU.sUnion_mem (hU.sUnion_mem hg))
      (dom_subset_sUnion_sUnion_graph F))

/-- The placement statement in the tower's own terms: a λ totalized
over the level-`n+1` carrier does not live at level `n+1`.  (Level `0`
is `univZero`, the truth values, and is not a Grothendieck universe —
but the squash regime has no graphs at all, so nothing is totalized
there.) -/
theorem lamT_not_mem_univ (n : Nat) (F : V → V) :
    ¬ lamT (univ (n + 1)) F ∈ˢ (univ (n + 1) : V) :=
  graph_not_mem_of_isTGUniverse (univ_isTGUniverse (Nat.succ_ne_zero n)) F

/-- Contrast — the *current* encoding places fine, because the domain
is a member of the level, not the level itself.  This is the clause
totalization would have to give up. -/
theorem lamR_mem_piR_of {A : V} {F B : V → V}
    (hF : ∀ x, x ∈ˢ A → F x ∈ˢ B x) : lamR 1 A F ∈ˢ piR 1 A B :=
  lamR_mem hF

/-! ## Axiom audit -/

#print axioms app_lamT
#print axioms app_lamT_off_carrier
#print axioms no_membership_free_elim
#print axioms app_mem_piR_pos_needs_ha
#print axioms dom_subset_sUnion_sUnion_graph
#print axioms graph_not_mem_of_isTGUniverse
#print axioms lamT_not_mem_univ
#print axioms lamR_mem_piR_of

end ConLeche.SetR.Interp2.ProbeD1
