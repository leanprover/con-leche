module

public import ConLeche.Semantics.Inductives.HoleMono

@[expose] public section

/-!
# Accessibility in the holes, case by case (lane ACCMODEL)

The twin of `HoleMono.lean` for the closure witness (W) (maintainer
ruling "(W) by ACCESSIBILITY", 2026-09-24): a reading is ACCESSIBLE
along a frame relation `R` when every element has a SUPPORT — a family,
indexed by a subset of a BOUND `A ρ`, of items `(h, vs, y)` held by the
frame (`Holds`: `y` lies in the value at position `h` applied to the
spine `vs`) — such that the element lies in the reading at every related
frame holding the items (`AccOn`).  At the top the relation relates the
hole frames of any two tuples of the space, and the support items at the
member holes are the tuple's occurrences: `SetModel/Access.lean`'s
`AccTuple`, which `closed_of_acc` turns into (W).

`R` is a relation of COMPARABLE frames (holes vary freely), not an
order: the support, not an inclusion of holes, carries the element to
the target frame.  Under a binder whose domain may read the holes the
relation is `FrameRel.underBoth` (the bound value in the domain at both
frames): a field telescope puts an earlier field's value into the target
frame by that value's own support.

| case | lemma | bound |
|---|---|---|
| a hole-free reading | `ConstOn.accOn` | `∅` |
| the `whnf` step | `AccOn.of_eqOn` | the reduct's |
| Π over a hole-free domain | `AccOn.pi` | `Σ_{d ∈ ⟦D⟧ρ} Bb (d :: ρ)` |
| a member hole at hole-free arguments | `AccOn.holeApp` | `{pt}` |
| a frame's hole at its key's parameters | `AccOn.holeAppArgs` (`FrameBlind`) | `{pt}` |

The bound is a FUNCTION of the frame: a Π's domain may read earlier
fields and binders.  Its uniformity across the tuples of the space is a
separate, all-frames fact (`InvOn`: the bound reads only given
positions), which the run inversion states off the walk's output and U4
makes uniform along a field telescope.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Support items and the predicate -/

/-- A support item: a frame position, an argument spine, a value. -/
abbrev Occ (V : Type uv) := Nat × List V × V

/-- **The frame holds the item**: the value lies in the position's value
applied to the spine. -/
def Holds (ρ : Nat → V) (o : Occ V) : Prop := o.2.2 ∈ˢ o.2.1.foldl app (ρ o.1)

/-- **Accessible along `R` with bound `A`** (see the module docstring). -/
def AccOn (R : FrameRel V) (A : (Nat → V) → V) (a : AnnotTerm) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ x, x ∈ˢ interp V ρ a →
    ∃ (B : V) (g : V → Occ V), B ⊆ˢ A ρ ∧ (∀ b, b ∈ˢ B → Holds ρ (g b)) ∧
      ∀ ρ', R ρ ρ' → (∀ b, b ∈ˢ B → Holds ρ' (g b)) → x ∈ˢ interp V ρ' a

/-- **The bound reads only the positions `M`.** -/
def InvOn (M : Nat → Prop) (A : (Nat → V) → V) : Prop :=
  ∀ ρ ρ' : Nat → V, (∀ i, M i → ρ i = ρ' i) → A ρ = A ρ'

namespace FrameRel

/-- **Under a binder of domain `A`, the value in the domain at both
frames.** -/
def underBoth (R : FrameRel V) (A : AnnotTerm) : FrameRel V :=
  fun σ σ' => ∃ x ρ ρ', σ = cons x ρ ∧ σ' = cons x ρ' ∧ R ρ ρ' ∧
    x ∈ˢ interp V ρ A ∧ x ∈ˢ interp V ρ' A

theorem AgreesOff.underBoth {R : FrameRel V} {P : Nat → Prop} (h : R.AgreesOff P)
    (A : AnnotTerm) : (R.underBoth A).AgreesOff (shiftP P) := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -, -⟩
  exact agreeOff_cons (h ρ ρ' hR) x

/-- A hole-free domain: `underBoth` is `under`. -/
theorem underBoth_of_constOn {R : FrameRel V} {A : AnnotTerm} (hA : ConstOn R A) {σ σ' : Nat → V}
    (h : R.under A σ σ') : R.underBoth A σ σ' := by
  obtain ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩ := h
  exact ⟨x, ρ, ρ', rfl, rfl, hR, hx, hA ρ ρ' hR ▸ hx⟩

end FrameRel

/-! ## Generic facts -/

theorem AccOn.mono_bound {R : FrameRel V} {A A' : (Nat → V) → V} {a : AnnotTerm}
    (h : AccOn R A a) (hA : ∀ ρ ρ₀, R ρ ρ₀ → A ρ ⊆ˢ A' ρ) : AccOn R A' a := by
  intro ρ ρ₀ hR x hx
  obtain ⟨B, g, hB, hg, hs⟩ := h ρ ρ₀ hR x hx
  exact ⟨B, g, Subset.trans hB (hA ρ ρ₀ hR), hg, hs⟩

/-- A smaller relation keeps accessibility. -/
theorem AccOn.of_le {R R' : FrameRel V} {A : (Nat → V) → V} {a : AnnotTerm}
    (h : AccOn R A a) (hRR : ∀ ρ ρ', R' ρ ρ' → R ρ ρ') : AccOn R' A a := by
  intro ρ ρ₀ hR x hx
  obtain ⟨B, g, hB, hg, hs⟩ := h ρ ρ₀ (hRR _ _ hR) x hx
  exact ⟨B, g, hB, hg, fun ρ' hR' h' => hs ρ' (hRR _ _ hR') h'⟩

/-- **Accessible ⇒ positive** along any relation that carries the items. -/
theorem AccOn.monoOn {R R' : FrameRel V} {A : (Nat → V) → V} {a : AnnotTerm}
    (h : AccOn R A a) (hRR : ∀ ρ ρ', R' ρ ρ' → R ρ ρ')
    (hold : ∀ ρ ρ', R' ρ ρ' → ∀ o, Holds ρ o → Holds ρ' o) : MonoOn R' a := by
  intro ρ ρ' hR x hx
  obtain ⟨B, g, -, hg, hs⟩ := h ρ ρ' (hRR _ _ hR) x hx
  exact hs ρ' (hRR _ _ hR) fun b hb => hold ρ ρ' hR _ (hg b hb)

/-! ## The cases -/

/-- **A hole-free reading** is accessible with the empty bound. -/
theorem ConstOn.accOn {R : FrameRel V} {a : AnnotTerm} (h : ConstOn R a) :
    AccOn R (fun _ => empty) a := by
  intro ρ ρ₀ _ x hx
  refine ⟨empty, fun _ => (0, [], empty), Subset.refl _,
    fun b hb => absurd hb (not_mem_empty b), fun ρ' hR' _ => ?_⟩
  rw [← h ρ ρ' hR']
  exact hx

/-- **The `whnf` step.** -/
theorem AccOn.of_eqOn {R : FrameRel V} {Q : (Nat → V) → Prop}
    (hdom : ∀ ρ ρ', R ρ ρ' → Q ρ ∧ Q ρ') {A : (Nat → V) → V} {a b : AnnotTerm}
    (heq : ∀ ρ, Q ρ → interp V ρ a = interp V ρ b) (hb : AccOn R A b) : AccOn R A a := by
  intro ρ ρ₀ hR x hx
  rw [heq ρ (hdom ρ ρ₀ hR).1] at hx
  obtain ⟨B, g, hB, hg, hs⟩ := hb ρ ρ₀ hR x hx
  exact ⟨B, g, hB, hg, fun ρ' hR' h' => by rw [heq ρ' (hdom ρ ρ' hR').2]; exact hs ρ' hR' h'⟩

/-- Skolemisation of supports over a set of positions. -/
theorem skolem_occ {S : V} {Q : V → V → (V → Occ V) → Prop}
    (h : ∀ a, a ∈ˢ S → ∃ B g, Q a B g) :
    ∃ (Bf : V → V) (gf : V → V → Occ V), ∀ a, a ∈ˢ S → Q a (Bf a) (gf a) := by
  classical
  refine ⟨fun a => if h' : a ∈ˢ S then Classical.choose (h a h') else empty,
    fun a => if h' : a ∈ˢ S then Classical.choose (Classical.choose_spec (h a h'))
      else fun _ => (0, [], empty), fun a ha => ?_⟩
  simp only [dif_pos ha]
  exact Classical.choose_spec (Classical.choose_spec (h a ha))

/-- An item one binder down, seen above it. -/
def Occ.down (o : Occ V) : Occ V := (o.1 - 1, o.2)

theorem holds_cons_down {x : V} {ρ : Nat → V} {o : Occ V} (h0 : o.1 ≠ 0) :
    Holds (cons x ρ) o ↔ Holds ρ o.down := by
  obtain ⟨i, vs, y⟩ := o
  cases i with
  | zero => exact absurd rfl h0
  | succ i => rfl

/-- **Π over a hole-free domain**: the support of a function (or, at a
`Prop` codomain, of the truth of `∀ d`) is the glued supports of its
values, the body's items one binder down (the bound variable's own items
dropped: it is the same at both frames). -/
theorem AccOn.pi {R : FrameRel V} {D B : AnnotTerm} (u v : Nat) (hD : ConstOn R D)
    {Bb : (Nat → V) → V} (hB : AccOn (R.underBoth D) Bb B) :
    AccOn R (fun ρ => sigmaPairs (interp V ρ D) fun d => Bb (cons d ρ)) (.pi u v D B) := by
  intro ρ ρ₀ hR f hf
  rw [interp_pi] at hf
  -- the elements of the fibres a support is needed for
  have hwit : ∀ d, d ∈ˢ interp V ρ D → ∃ y, y ∈ˢ interp V (cons d ρ) B ∧
      (v ≠ 0 → y = app f d) := by
    intro d hd
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · rw [piR_zero] at hf
      obtain ⟨y, hy⟩ := (of_mem_truthVal hf) d hd
      exact ⟨y, hy, fun h => absurd rfl h⟩
    · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
      rw [piR_pos hv'] at hf
      exact ⟨app f d, app_mem_of_mem_piSet hf hd, fun _ => rfl⟩
  classical
  let yv : V → V := fun d => if h : d ∈ˢ interp V ρ D then Classical.choose (hwit d h) else empty
  have hyv : ∀ d (hd : d ∈ˢ interp V ρ D), yv d ∈ˢ interp V (cons d ρ) B ∧
      (v ≠ 0 → yv d = app f d) := by
    intro d hd
    have := Classical.choose_spec (hwit d hd)
    simp only [yv, dif_pos hd]
    exact this
  obtain ⟨Bf, gf, hsk⟩ := skolem_occ (S := interp V ρ D)
    (Q := fun d B' g => B' ⊆ˢ Bb (cons d ρ) ∧ (∀ b, b ∈ˢ B' → Holds (cons d ρ) (g b)) ∧
      ∀ σ', R.underBoth D (cons d ρ) σ' → (∀ b, b ∈ˢ B' → Holds σ' (g b)) →
        yv d ∈ˢ interp V σ' B)
    fun d hd => hB (cons d ρ) (cons d ρ₀) ⟨d, ρ, ρ₀, rfl, rfl, hR, hd, hD ρ ρ₀ hR ▸ hd⟩ _
      (hyv d hd).1
  -- the glued support, the bound variable's items dropped
  refine ⟨sigmaPairs (interp V ρ D) fun d => sep (Bf d) fun b => (gf d b).1 ≠ 0,
    fun p => (gf (sfst p) (ssnd p)).down, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨d, hd, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
    exact mem_sigmaPairs.mpr ⟨d, hd, b, (hsk d hd).1 b (mem_sep.mp hb).1, rfl⟩
  · intro p hp
    obtain ⟨d, hd, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
    simp only [sfst_kpair, ssnd_kpair]
    exact (holds_cons_down (mem_sep.mp hb).2).mp ((hsk d hd).2.1 b (mem_sep.mp hb).1)
  · intro ρ' hR' h'
    rw [interp_pi, ← hD ρ ρ' hR']
    -- every chosen value lies in the body at the target frame
    have hval : ∀ d, d ∈ˢ interp V ρ D → yv d ∈ˢ interp V (cons d ρ') B := by
      intro d hd
      refine (hsk d hd).2.2 (cons d ρ') ⟨d, ρ, ρ', rfl, rfl, hR', hd, hD ρ ρ' hR' ▸ hd⟩
        fun b hb => ?_
      by_cases h0 : (gf d b).1 = 0
      · -- the bound variable's item: the same at both frames
        have := (hsk d hd).2.1 b hb
        unfold Holds at this ⊢
        rw [h0] at this ⊢
        exact this
      · have := h' (kpair d b) (mem_sigmaPairs.mpr ⟨d, hd, b, mem_sep.mpr ⟨hb, h0⟩, rfl⟩)
        simp only [sfst_kpair, ssnd_kpair] at this
        exact (holds_cons_down h0).mpr this
    rcases Nat.eq_zero_or_pos v with rfl | hv
    · rw [piR_zero] at hf ⊢
      rw [eq_pt_of_mem_truthVal hf]
      exact pt_mem_truthVal fun d hd => ⟨yv d, hval d hd⟩
    · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
      rw [piR_pos hv'] at hf ⊢
      rw [← eq_graph_app_of_mem_piSet hf]
      refine graph_mem_piSet fun d hd => ?_
      rw [← (hyv d hd).2 hv']
      exact hval d hd

/-- **A member hole at its full arity, at hole-free arguments.** -/
theorem AccOn.holeApp {R : FrameRel V} {h : Nat} {es : List AnnotTerm}
    (hes : ∀ e ∈ es, ConstOn R e) :
    AccOn R (fun _ => unitSet) (AnnotTerm.mkAppN (.bvar h) es) := by
  intro ρ ρ₀ _ x hx
  rw [interp_mkAppN_map, interp_bvar] at hx
  refine ⟨unitSet, fun _ => (h, es.map (interp V ρ), x), Subset.refl _, fun _ _ => hx,
    fun ρ' hR' h' => ?_⟩
  rw [interp_mkAppN_map, interp_bvar]
  have hmap : es.map (interp V ρ) = es.map (interp V ρ') :=
    List.map_congr_left fun e he => hes e he ρ ρ' hR'
  rw [← hmap]
  exact h' pt pt_mem_unitSet

/-- **A frame's hole is blind in its key's parameters** across related
frames: at the target frame its value applied to the parameters' readings
at either frame (then anything) is the same. -/
def FrameBlind (R : FrameRel V) (h : Nat) (ds : List AnnotTerm) : Prop :=
  ∀ ρ ρ', R ρ ρ' → ∀ is : List V,
    (ds.map (interp V ρ) ++ is).foldl app (ρ' h) = (ds.map (interp V ρ') ++ is).foldl app (ρ' h)

/-- **An in-progress hole** at its key's parameters and hole-free
indices. -/
theorem AccOn.holeAppArgs {R : FrameRel V} {h : Nat} {ds is : List AnnotTerm}
    (hbl : FrameBlind R h ds) (his : ∀ e ∈ is, ConstOn R e) :
    AccOn R (fun _ => unitSet) (AnnotTerm.mkAppN (.bvar h) (ds ++ is)) := by
  intro ρ ρ₀ _ x hx
  rw [interp_mkAppN_map, interp_bvar, List.map_append] at hx
  refine ⟨unitSet, fun _ => (h, ds.map (interp V ρ) ++ is.map (interp V ρ), x), Subset.refl _,
    fun _ _ => hx, fun ρ' hR' h' => ?_⟩
  rw [interp_mkAppN_map, interp_bvar, List.map_append]
  have hmap : is.map (interp V ρ) = is.map (interp V ρ') :=
    List.map_congr_left fun e he => his e he ρ ρ' hR'
  rw [← hmap, ← hbl ρ ρ' hR']
  exact h' pt pt_mem_unitSet

/-! ## Bounds reading given positions -/

/-- The positions `M` seen one binder down, the bound variable read. -/
def liftM (M : Nat → Prop) : Nat → Prop
  | 0 => True
  | i + 1 => M i

omit [SetTheory V] in
theorem InvOn.const (M : Nat → Prop) (c : V) : InvOn M (fun _ : Nat → V => c) :=
  fun _ _ _ => rfl

/-- **The Π bound reads what its domain and its body's bound read.** -/
theorem InvOn.pi {M : Nat → Prop} {D : AnnotTerm} (hD : NoBVar (fun i => ¬ M i) D)
    {Bb : (Nat → V) → V} (hB : InvOn (liftM M) Bb) :
    InvOn M (fun ρ => sigmaPairs (interp V ρ D) fun d => Bb (cons d ρ)) := by
  intro ρ ρ' hag
  have hD' : interp V ρ D = interp V ρ' D :=
    interp_congr_noBVar D hD fun i hi => hag i (Classical.byContradiction hi)
  simp only
  rw [hD']
  congr 1
  funext d
  refine hB _ _ fun i hi => ?_
  cases i with
  | zero => rfl
  | succ i => exact hag i hi

end ConLeche.Semantics
