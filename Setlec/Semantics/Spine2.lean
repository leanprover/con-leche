import Setlec.Semantics.Ok2

/-!
# The spine chain and the pinning fold (task #151 tier C, seal 2)

(Task #172 B4: moved from `SetR/Annot/` — the module is lane-neutral,
`V`-generic over `SetTheory` and imports only `SetBase/Ok2`, and the
io skip's semantic license consumes it from the P lane too.  The
namespace is unchanged.)

The family-0/1 (iota telescope) core theorem set: what replaces the
per-fire `iotaCertsI` walk at a positive-kind telescope.

* `SlotChain` — the subject side: each partial application of a spine
  carries its kinded package.  `AnnotOk2_spine_slots` reads it off the
  redex's own invariant — this is all the *subject* ever contributes.
* `PosShape` — the stored-type side: the telescope value peels `n`
  binders, every one in the graph regime.  For a stored recursor type
  this is install-time data: the telescope is sort-checked at the
  front door, and the peeled kinds are the (instantiated) binder
  sorts, positive exactly when the motive's instantiated sort is —
  the O(1) runtime gate of the removal design.
* `slotChain_fits` — **the pinning fold**: walking the slots down a
  positive-kind telescope pins every domain (`piR_dom_unique` — even
  `Prop`-typed slots, since what matters is the *product's* kind) and
  yields the telescope fit plus the residual membership, with no
  runtime walk.  `TeleFit2` is the fit the iota consumer reads
  (`TeleFitV`'s value-level, kinded analogue).
-/

namespace Setlec.SetR.Interp2

open SetTheory
open Setlec.SetR (AVExpr)

universe w

variable {V : Type w} [SetTheory V]

/-- The subject-side slot chain: each partial application carries a
kinded package for the next argument. -/
def SlotChain : V → List V → Prop
  | _, [] => True
  | f, a :: rest =>
    (∃ (v : Nat) (A : V) (B : V → V), f ∈ˢ piR v A B ∧ a ∈ˢ A ∧
      (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))) ∧
    SlotChain (app f a) rest

/-- The stored-type side: the value peels `n` binders, every product
in the graph regime, fibre-uniformly (the walk descends at whatever
value the slot pins). -/
inductive PosShape : V → Nat → Prop
  | zero {T : V} : PosShape T 0
  | succ {v : Nat} {A : V} {B : V → V} {n : Nat} :
      v ≠ 0 → (∀ x, x ∈ˢ A → PosShape (B x) n) →
      PosShape (piR v A B) (n + 1)

/-- The value-level, kinded telescope fit (`TeleFitV`'s analogue):
each argument inhabits its progressively-peeled domain, every product
in the graph regime. -/
inductive TeleFit2 : V → List V → V → Prop
  | nil {T : V} : TeleFit2 T [] T
  | cons {v : Nat} {A T' : V} {B : V → V} {a : V} {as : List V} :
      v ≠ 0 → a ∈ˢ A → TeleFit2 (B a) as T' →
      TeleFit2 (piR v A B) (a :: as) T'

/-- The residual membership a fit carries along a member of the
telescope. -/
theorem TeleFit2.fold_mem {T T' f : V} {as : List V}
    (hfit : TeleFit2 T as T') (hf : f ∈ˢ T) :
    as.foldl app f ∈ˢ T' := by
  induction hfit generalizing f with
  | nil => exact hf
  | @cons v A _ B a as hv ha _ ih =>
    exact ih (app_mem_piR_pos hv hf ha)

/-- **The pinning fold** — the family-0/1 core theorem: a member of a
positive-kind telescope, applied along a spine whose partial
applications carry kinded packages, *fits* the telescope — every
domain membership recovered by graph rigidity, no runtime walk. -/
theorem slotChain_fits :
    ∀ (as : List V) {T f : V}, f ∈ˢ T → SlotChain f as →
      PosShape T as.length →
      ∃ T', TeleFit2 T as T' ∧ as.foldl app f ∈ˢ T' := by
  intro as
  induction as with
  | nil =>
    intro T f hf _ _
    exact ⟨T, .nil, hf⟩
  | cons a as ih =>
    intro T f hf hchain hshape
    obtain ⟨⟨v', A', B', hslot, ha', -⟩, hchain'⟩ := hchain
    cases hshape with
    | @succ v A B _ hv hfib =>
      -- the slot's product is in the graph regime: `f` is not `pt`
      have hv' : v' ≠ 0 := by
        intro h0
        subst h0
        exact not_pt_mem_piR_pos hv (eq_pt_of_mem_piR_zero hslot ▸ hf)
      -- rigidity pins the slot's domain to the telescope's
      have hAA : A' = A := piR_dom_unique hv' hv hslot hf
      have ha : a ∈ˢ A := hAA ▸ ha'
      obtain ⟨T', hfit, hmem⟩ :=
        ih (app_mem_piR_pos hv hf ha) hchain' (hfib a ha)
      exact ⟨T', .cons hv ha hfit, hmem⟩

/-- The subject supplies its own slot chain: `AnnotOk2` of an
application spine, read along the spine.  The heads of a truthful
spine are truthful (first conjunct), so the extraction is one
induction. -/
theorem AnnotOk2_spine_slots {ρ : Nat → V} :
    ∀ (as : List AVExpr) (f : AVExpr),
      AnnotOk2 V ρ (AVExpr.mkAppN f as) →
      SlotChain (interp2 V ρ f) (as.map (interp2 V ρ)) := by
  intro as
  induction as with
  | nil => intro f _; trivial
  | cons a as ih =>
    intro f h
    have h' := ih (.app f a) h
    -- the head's own package: `AnnotOk2 (.app f a)` sits at the spine's
    -- base, reachable through the first conjuncts
    have hhead : AnnotOk2 V ρ (.app f a) := by
      clear h' ih
      induction as generalizing a f with
      | nil => exact h
      | cons b bs ih2 =>
        have := ih2 (f := .app f a) (a := b) h
        rw [AnnotOk2_app] at this
        exact this.1
    rw [AnnotOk2_app] at hhead
    refine ⟨?_, ?_⟩
    · exact hhead.2.2
    · rw [show SetTheory.app (interp2 V ρ f) (interp2 V ρ a)
        = interp2 V ρ (.app f a) from (interp2_app V ρ f a).symm]
      exact h'

/-- **The redex interface** (what seal 3's iota case consumes): a
truthful application spine whose head inhabits a positive-kind
telescope fits it — subject invariant in, telescope fit and residual
membership out, no runtime walk anywhere. -/
theorem AnnotOk2_redex_fits {ρ : Nat → V} {f : AVExpr}
    {as : List AVExpr} {T : V}
    (h : AnnotOk2 V ρ (AVExpr.mkAppN f as))
    (hf : interp2 V ρ f ∈ˢ T)
    (hshape : PosShape T as.length) :
    ∃ T', TeleFit2 T (as.map (interp2 V ρ)) T' ∧
      interp2 V ρ (AVExpr.mkAppN f as) ∈ˢ T' := by
  obtain ⟨T', hfit, hmem⟩ := slotChain_fits (as.map (interp2 V ρ)) hf
    (AnnotOk2_spine_slots as f h)
    (by rw [List.length_map]; exact hshape)
  refine ⟨T', hfit, ?_⟩
  rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V ρ)
    (g := fun r a => app r a)]
  exact hmem

end Setlec.SetR.Interp2
