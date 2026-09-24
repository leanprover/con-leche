module

public import ConLeche.Semantics.Inductives.HoleMono

@[expose] public section

/-!
# Accessibility in the holes, case by case (lane ACCMODEL)

The twin of `HoleMono.lean` for the closure witness (W) (maintainer
ruling "(W) by ACCESSIBILITY", 2026-09-24): a reading is ACCESSIBLE
along a frame relation `R` when every SMALL element (`x ∈ univ w`) has a
SUPPORT — a family, indexed by a subset of a BOUND `A ρ`, of ADMISSIBLE
items `(h, vs, y)` held by the frame (`Holds`: `y` lies in the value at
position `h` applied to the spine `vs`; admissible: `Q h vs.length`, a
hole at its full arity) — such that the element lies in the reading at
every related frame holding the items (`AccOn`).  At the top the
relation relates the hole frames of any two tuples of the space, and the
items are the tuple's occurrences: `SetModel/Access.lean`'s `AccTuple`,
which `closed_of_acc` turns into (W).

`R` is a relation of COMPARABLE frames (holes vary freely), not an
order: the support, not an inclusion of holes, carries the element to
the target frame.  Under a binder whose domain may read the holes the
relation is `FrameRel.underBoth` (the bound value in the domain at both
frames): a field telescope puts an earlier field's value into the target
frame by that value's own support.

**Sizes.**  The bound must be a set of the level (`SizeOn`), uniformly:
only small elements need a support (the element guard), so a Π's bound
glues its values' supports over its domain only where that domain is
small — which it is as soon as one small function inhabits it.  A Π at a
`Prop` codomain may have a big domain; there the body is truth-valued
(the grading), and a truth-valued reading of an accepted walk reads no
hole (`TypeReg`): a hole at its full arity is RICH (`RichOn`, a fact of
the relation: a frame holding `pt` at the hole has a related, larger
frame holding a non-`pt` element there), so it is never truth-valued at
every related frame.  The Π is then hole-free, its bound `∅`.

| case | accessibility | bound | type regime |
|---|---|---|---|
| a hole-free reading | `ConstOn.accOn` | `∅` | `ConstOn.typeReg` |
| the `whnf` step | `AccOn.of_eqOn` | the reduct's | `TypeReg.of_eqOn` |
| Π, hole-free domain, `v ≠ 0` | `AccOn.pi` | `piBound` | `TypeReg.pi` |
| Π, hole-free domain, `v = 0` | `ConstOn.pi` (via the body's `TypeReg`) | `∅` | `TypeReg.pi` |
| a member hole at hole-free arguments | `AccOn.holeApp` | `{pt}` | `TypeReg.holeApp` |
| a frame's hole at its key's parameters | `AccOn.holeAppArgs` (`FrameBlind`) | `{pt}` | `TypeReg.holeAppArgs` |

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

/-- The admissible items: at the positions and spine lengths `Q`. -/
def Adm (Q : Nat → Nat → Prop) (o : Occ V) : Prop := Q o.1 o.2.1.length

/-- **Accessible along `R` with bound `A`, admissible items `Q`, at the
level `w`** (see the module docstring). -/
def AccOn (w : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V) (A : (Nat → V) → V)
    (a : AnnotTerm) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ x, x ∈ˢ (univ w : V) → x ∈ˢ interp V ρ a →
    ∃ (B : V) (g : V → Occ V), B ⊆ˢ A ρ ∧ (∀ b, b ∈ˢ B → Adm Q (g b) ∧ Holds ρ (g b)) ∧
      ∀ ρ', R ρ ρ' → (∀ b, b ∈ˢ B → Holds ρ' (g b)) → x ∈ˢ interp V ρ' a

/-- **The bound is a set of the level** at every frame of the relation. -/
def SizeOn (w : Nat) (R : FrameRel V) (A : (Nat → V) → V) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → A ρ ∈ˢ (univ w : V)

/-- **The bound reads only the positions `M`.** -/
def InvOn (M : Nat → Prop) (A : (Nat → V) → V) : Prop :=
  ∀ ρ ρ' : Nat → V, (∀ i, M i → ρ i = ρ' i) → A ρ = A ρ'

/-- **The type regime**: a reading truth-valued at every frame of the
relation reads no hole (see the module docstring). -/
def TypeReg (R : FrameRel V) (a : AnnotTerm) : Prop :=
  (∀ ρ ρ', R ρ ρ' → interp V ρ a ∈ˢ (univZero : V) ∧ interp V ρ' a ∈ˢ (univZero : V)) →
    ConstOn R a

/-- The larger frame holds every admissible item the smaller one does. -/
def HoldsLe (Q : Nat → Nat → Prop) (ρ ρ' : Nat → V) : Prop :=
  ∀ o, Adm Q o → Holds ρ o → Holds ρ' o

/-- **Rich holes**: an admissible position holding `pt` at a frame of the
relation has a related frame, holding every admissible item the first
one does, where it holds a non-`pt` element. -/
def RichOn (Q : Nat → Nat → Prop) (R : FrameRel V) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ (i : Nat) (vs : List V), Q i vs.length → (pt : V) ∈ˢ vs.foldl app (ρ i) →
    ∃ ρ'', R ρ ρ'' ∧ HoldsLe Q ρ ρ'' ∧ ∃ z, z ∈ˢ vs.foldl app (ρ'' i) ∧ z ≠ pt

/-- The admissible items one binder down: never the bound variable. -/
def shiftQ (Q : Nat → Nat → Prop) : Nat → Nat → Prop
  | 0, _ => False
  | i + 1, n => Q i n

namespace FrameRel

/-- **Under a binder of domain `A`, the value in the domain at both
frames.** -/
def underBoth (R : FrameRel V) (A : AnnotTerm) : FrameRel V :=
  fun σ σ' => ∃ x ρ ρ', σ = cons x ρ ∧ σ' = cons x ρ' ∧ R ρ ρ' ∧
    x ∈ˢ interp V ρ A ∧ x ∈ˢ interp V ρ' A

/-- A symmetric relation. -/
def Symm (R : FrameRel V) : Prop := ∀ ρ ρ', R ρ ρ' → R ρ' ρ

theorem AgreesOff.underBoth {R : FrameRel V} {P : Nat → Prop} (h : R.AgreesOff P)
    (A : AnnotTerm) : (R.underBoth A).AgreesOff (shiftP P) := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -, -⟩
  exact agreeOff_cons (h ρ ρ' hR) x

theorem Symm.underBoth {R : FrameRel V} (h : R.Symm) (A : AnnotTerm) : (R.underBoth A).Symm := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
  exact ⟨x, ρ', ρ, rfl, rfl, h ρ ρ' hR, hx', hx⟩

/-- A hole-free domain: `underBoth` is `under`. -/
theorem underBoth_of_constOn {R : FrameRel V} {A : AnnotTerm} (hA : ConstOn R A) {σ σ' : Nat → V}
    (h : R.under A σ σ') : R.underBoth A σ σ' := by
  obtain ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩ := h
  exact ⟨x, ρ, ρ', rfl, rfl, hR, hx, hA ρ ρ' hR ▸ hx⟩

end FrameRel

/-! ## Generic facts -/

theorem AccOn.mono_bound {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {A A' : (Nat → V) → V}
    {a : AnnotTerm} (h : AccOn w Q R A a) (hA : ∀ ρ ρ₀, R ρ ρ₀ → A ρ ⊆ˢ A' ρ) :
    AccOn w Q R A' a := by
  intro ρ ρ₀ hR x hxw hx
  obtain ⟨B, g, hB, hg, hs⟩ := h ρ ρ₀ hR x hxw hx
  exact ⟨B, g, Subset.trans hB (hA ρ ρ₀ hR), hg, hs⟩

/-- A smaller relation keeps accessibility. -/
theorem AccOn.of_le {w : Nat} {Q : Nat → Nat → Prop} {R R' : FrameRel V} {A : (Nat → V) → V}
    {a : AnnotTerm} (h : AccOn w Q R A a) (hRR : ∀ ρ ρ', R' ρ ρ' → R ρ ρ') : AccOn w Q R' A a := by
  intro ρ ρ₀ hR x hxw hx
  obtain ⟨B, g, hB, hg, hs⟩ := h ρ ρ₀ (hRR _ _ hR) x hxw hx
  exact ⟨B, g, hB, hg, fun ρ' hR' h' => hs ρ' (hRR _ _ hR') h'⟩

/-- **Accessible ⇒ positive** (at the small elements) along any relation
that carries the admissible items. -/
theorem AccOn.monoOn {w : Nat} {Q : Nat → Nat → Prop} {R R' : FrameRel V} {A : (Nat → V) → V}
    {a : AnnotTerm} (h : AccOn w Q R A a) (hRR : ∀ ρ ρ', R' ρ ρ' → R ρ ρ')
    (hold : ∀ ρ ρ', R' ρ ρ' → HoldsLe Q ρ ρ') :
    ∀ ρ ρ', R' ρ ρ' → ∀ x, x ∈ˢ (univ w : V) → x ∈ˢ interp V ρ a → x ∈ˢ interp V ρ' a := by
  intro ρ ρ' hR x hxw hx
  obtain ⟨B, g, -, hg, hs⟩ := h ρ ρ' (hRR _ _ hR) x hxw hx
  exact hs ρ' (hRR _ _ hR) fun b hb => hold ρ ρ' hR _ (hg b hb).1 (hg b hb).2

/-- **The domain transfer**: a small value of an accessible domain at a
frame stays in it at every related frame holding the frame's admissible
items. -/
theorem AccOn.transfer {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {A : (Nat → V) → V}
    {a : AnnotTerm} (h : AccOn w Q R A a) {ρ ρ₀ ρ'' : Nat → V} (hR₀ : R ρ ρ₀) (hR'' : R ρ ρ'')
    (hle : HoldsLe Q ρ ρ'') {x : V} (hxw : x ∈ˢ (univ w : V)) (hx : x ∈ˢ interp V ρ a) :
    x ∈ˢ interp V ρ'' a := by
  obtain ⟨B, g, -, hg, hs⟩ := h ρ ρ₀ hR₀ x hxw hx
  exact hs ρ'' hR'' fun b hb => hle _ (hg b hb).1 (hg b hb).2

/-- **Richness survives a binder** whose domain carries its values to
every larger related frame (a hole-free domain, or an accessible one at
small values). -/
theorem RichOn.underBoth {Q : Nat → Nat → Prop} {R : FrameRel V} (h : RichOn Q R) {A : AnnotTerm}
    (htr : ∀ ρ ρ₀ ρ'', R ρ ρ₀ → R ρ ρ'' → HoldsLe Q ρ ρ'' → ∀ x, x ∈ˢ interp V ρ A →
      x ∈ˢ interp V ρ₀ A → x ∈ˢ interp V ρ'' A) :
    RichOn (shiftQ Q) (R.underBoth A) := by
  rintro _ _ ⟨x, ρ, ρ₀, rfl, rfl, hR, hx, hx₀⟩ i vs hQ hpt
  cases i with
  | zero => exact hQ.elim
  | succ i =>
    obtain ⟨ρ'', hR'', hle, z, hz, hzp⟩ := h ρ ρ₀ hR i vs hQ hpt
    refine ⟨cons x ρ'', ⟨x, ρ, ρ'', rfl, rfl, hR'', hx, htr ρ ρ₀ ρ'' hR hR'' hle x hx hx₀⟩,
      ?_, z, hz, hzp⟩
    rintro ⟨j, us, y⟩ hQ' hy
    cases j with
    | zero => exact hQ'.elim
    | succ j => exact hle (j, us, y) hQ' hy

/-! ## The cases: accessibility -/

theorem SizeOn.const {w : Nat} {R : FrameRel V} {c : V} (hc : c ∈ˢ (univ w : V)) :
    SizeOn w R (fun _ => c) := fun _ _ _ => hc

/-- **A hole-free reading** is accessible with the empty bound. -/
theorem ConstOn.accOn {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {a : AnnotTerm}
    (h : ConstOn R a) : AccOn w Q R (fun _ => empty) a := by
  intro ρ ρ₀ _ x _ hx
  refine ⟨empty, fun _ => (0, [], empty), Subset.refl _,
    fun b hb => absurd hb (not_mem_empty b), fun ρ' hR' _ => ?_⟩
  rw [← h ρ ρ' hR']
  exact hx

/-- **The `whnf` step.** -/
theorem AccOn.of_eqOn {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {P : (Nat → V) → Prop}
    (hdom : ∀ ρ ρ', R ρ ρ' → P ρ ∧ P ρ') {A : (Nat → V) → V} {a b : AnnotTerm}
    (heq : ∀ ρ, P ρ → interp V ρ a = interp V ρ b) (hb : AccOn w Q R A b) : AccOn w Q R A a := by
  intro ρ ρ₀ hR x hxw hx
  rw [heq ρ (hdom ρ ρ₀ hR).1] at hx
  obtain ⟨B, g, hB, hg, hs⟩ := hb ρ ρ₀ hR x hxw hx
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

/-- A small function's domain and values are small. -/
theorem small_of_mem_piSet {w : Nat} (hw : w ≠ 0) {D f : V} {F : V → V} (hf : f ∈ˢ piSet D F)
    (hfw : f ∈ˢ (univ w : V)) : D ∈ˢ (univ w : V) ∧ ∀ d, d ∈ˢ D → app f d ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  have hpair : ∀ d, d ∈ˢ D → kpair d (app f d) ∈ˢ f := by
    intro d hd
    rw [← eq_graph_app_of_mem_piSet hf]
    exact mem_graph.mpr ⟨d, hd, by rw [eq_graph_app_of_mem_piSet hf]⟩
  have hkp : ∀ d, d ∈ˢ D → kpair d (app f d) ∈ˢ (univ w : V) :=
    fun d hd => hU.transitive hfw (hpair d hd)
  refine ⟨?_, fun d hd => ?_⟩
  · refine hU.mem_of_subset_mem (hU.sUnion_mem (hU.sUnion_mem hfw)) fun d hd => ?_
    exact mem_sUnion.mpr ⟨sing d, mem_sUnion.mpr ⟨kpair d (app f d), hpair d hd,
      mem_upair_left _ _⟩, mem_sing.mpr rfl⟩
  · exact hU.transitive (hU.transitive (hkp d hd) (mem_upair_right _ _)) (mem_upair_right _ _)

/-- **The bound of a Π**: the glued bounds of the body over the domain,
where the domain is small. -/
noncomputable def piBound (w : Nat) (D : AnnotTerm) (Bb : (Nat → V) → V) (ρ : Nat → V) : V :=
  open Classical in
  if interp V ρ D ∈ˢ (univ w : V) then sigmaPairs (interp V ρ D) fun d => Bb (cons d ρ) else empty

/-- **Π over a hole-free domain at a positive codomain sort**: the
support of a small function is the glued supports of its values, the
body's items one binder down (the bound variable is no admissible
position). -/
theorem AccOn.pi {w : Nat} (hw : w ≠ 0) {Q : Nat → Nat → Prop} {R : FrameRel V} {D B : AnnotTerm}
    (u : Nat) {v : Nat} (hv : v ≠ 0) (hD : ConstOn R D)
    {Bb : (Nat → V) → V} (hB : AccOn w (shiftQ Q) (R.underBoth D) Bb B) :
    AccOn w Q R (piBound w D Bb) (.pi u v D B) := by
  intro ρ ρ₀ hR f hfw hf
  rw [interp_pi, piR_pos hv] at hf
  obtain ⟨hDw, happw⟩ := small_of_mem_piSet hw hf hfw
  obtain ⟨Bf, gf, hsk⟩ := skolem_occ (S := interp V ρ D)
    (Q := fun d B' g => B' ⊆ˢ Bb (cons d ρ) ∧
      (∀ b, b ∈ˢ B' → Adm (shiftQ Q) (g b) ∧ Holds (cons d ρ) (g b)) ∧
      ∀ σ', R.underBoth D (cons d ρ) σ' → (∀ b, b ∈ˢ B' → Holds σ' (g b)) →
        app f d ∈ˢ interp V σ' B)
    fun d hd => hB (cons d ρ) (cons d ρ₀) ⟨d, ρ, ρ₀, rfl, rfl, hR, hd, hD ρ ρ₀ hR ▸ hd⟩ _
      (happw d hd) (app_mem_of_mem_piSet hf hd)
  -- an admissible item of the body is never the bound variable
  have hne : ∀ d, d ∈ˢ interp V ρ D → ∀ b, b ∈ˢ Bf d → (gf d b).1 ≠ 0 := by
    intro d hd b hb h0
    have := ((hsk d hd).2.1 b hb).1
    unfold Adm at this
    rw [h0] at this
    exact this
  refine ⟨sigmaPairs (interp V ρ D) Bf, fun p => (gf (sfst p) (ssnd p)).down, ?_, ?_, ?_⟩
  · intro p hp
    obtain ⟨d, hd, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
    unfold piBound
    rw [if_pos hDw]
    exact mem_sigmaPairs.mpr ⟨d, hd, b, (hsk d hd).1 b hb, rfl⟩
  · intro p hp
    obtain ⟨d, hd, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
    simp only [sfst_kpair, ssnd_kpair]
    obtain ⟨hQ, hH⟩ := (hsk d hd).2.1 b hb
    refine ⟨?_, (holds_cons_down (hne d hd b hb)).mp hH⟩
    have h0 := hne d hd b hb
    unfold Adm at hQ ⊢
    generalize gf d b = o at hQ h0
    obtain ⟨i, vs, y⟩ := o
    cases i with
    | zero => exact absurd rfl h0
    | succ i => exact hQ
  · intro ρ' hR' h'
    rw [interp_pi, ← hD ρ ρ' hR', piR_pos hv]
    rw [← eq_graph_app_of_mem_piSet hf]
    refine graph_mem_piSet fun d hd => ?_
    refine (hsk d hd).2.2 (cons d ρ') ⟨d, ρ, ρ', rfl, rfl, hR', hd, hD ρ ρ' hR' ▸ hd⟩
      fun b hb => ?_
    have := h' (kpair d b) (mem_sigmaPairs.mpr ⟨d, hd, b, hb, rfl⟩)
    simp only [sfst_kpair, ssnd_kpair] at this
    exact (holds_cons_down (hne d hd b hb)).mpr this

/-- The Π bound is a set of the level. -/
theorem SizeOn.pi {w : Nat} (hw : w ≠ 0) {R : FrameRel V} {D : AnnotTerm} (hD : ConstOn R D)
    {Bb : (Nat → V) → V} (hB : SizeOn w (R.underBoth D) Bb) : SizeOn w R (piBound w D Bb) := by
  intro ρ ρ₀ hR
  unfold piBound
  split
  · rename_i hDw
    exact (univ_isTGUniverse hw).sigmaPairs_mem hDw fun d hd =>
      hB (cons d ρ) (cons d ρ₀) ⟨d, ρ, ρ₀, rfl, rfl, hR, hd, hD ρ ρ₀ hR ▸ hd⟩
  · exact empty_mem_univ w

/-- **A member hole at its full arity, at hole-free arguments.** -/
theorem AccOn.holeApp {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {h : Nat}
    {es : List AnnotTerm} (hQ : Q h es.length) (hes : ∀ e ∈ es, ConstOn R e) :
    AccOn w Q R (fun _ => unitSet) (AnnotTerm.mkAppN (.bvar h) es) := by
  intro ρ ρ₀ _ x _ hx
  rw [interp_mkAppN_map, interp_bvar] at hx
  refine ⟨unitSet, fun _ => (h, es.map (interp V ρ), x), Subset.refl _,
    fun _ _ => ⟨by unfold Adm; simpa using hQ, hx⟩, fun ρ' hR' h' => ?_⟩
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
indices, at its full arity. -/
theorem AccOn.holeAppArgs {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {h : Nat}
    {ds is : List AnnotTerm} (hQ : Q h (ds.length + is.length)) (hbl : FrameBlind R h ds)
    (his : ∀ e ∈ is, ConstOn R e) :
    AccOn w Q R (fun _ => unitSet) (AnnotTerm.mkAppN (.bvar h) (ds ++ is)) := by
  intro ρ ρ₀ _ x _ hx
  rw [interp_mkAppN_map, interp_bvar, List.map_append] at hx
  refine ⟨unitSet, fun _ => (h, ds.map (interp V ρ) ++ is.map (interp V ρ), x), Subset.refl _,
    fun _ _ => ⟨by unfold Adm; simpa using hQ, hx⟩, fun ρ' hR' h' => ?_⟩
  rw [interp_mkAppN_map, interp_bvar, List.map_append]
  have hmap : is.map (interp V ρ) = is.map (interp V ρ') :=
    List.map_congr_left fun e he => his e he ρ ρ' hR'
  rw [← hmap, ← hbl ρ ρ' hR']
  exact h' pt pt_mem_unitSet

/-! ## The cases: the type regime -/

theorem ConstOn.typeReg {R : FrameRel V} {a : AnnotTerm} (h : ConstOn R a) : TypeReg R a :=
  fun _ => h

theorem TypeReg.of_eqOn {R : FrameRel V} {P : (Nat → V) → Prop}
    (hdom : ∀ ρ ρ', R ρ ρ' → P ρ ∧ P ρ') {a b : AnnotTerm}
    (heq : ∀ ρ, P ρ → interp V ρ a = interp V ρ b) (hb : TypeReg R b) : TypeReg R a := by
  intro htv
  refine ConstOn.of_eqOn hdom heq (hb fun ρ ρ' hR => ?_)
  rw [← heq ρ (hdom ρ ρ' hR).1, ← heq ρ' (hdom ρ ρ' hR).2]
  exact htv ρ ρ' hR

/-- **A Π over a hole-free domain and a hole-free body** is hole-free. -/
theorem ConstOn.pi {R : FrameRel V} {D B : AnnotTerm} (u v : Nat) (hD : ConstOn R D)
    (hB : ConstOn (R.underBoth D) B) : ConstOn R (.pi u v D B) := by
  intro ρ ρ' hR
  rw [interp_pi, interp_pi, ← hD ρ ρ' hR]
  unfold piR
  split
  · refine truthVal_congr (forall_congr' fun d => imp_congr_right fun hd => ?_)
    show (∃ y, y ∈ˢ interp V (cons d ρ) B) ↔ ∃ y, y ∈ˢ interp V (cons d ρ') B
    rw [hB _ _ ⟨d, ρ, ρ', rfl, rfl, hR, hd, hD ρ ρ' hR ▸ hd⟩]
  · exact piSet_congr fun d hd => hB _ _ ⟨d, ρ, ρ', rfl, rfl, hR, hd, hD ρ ρ' hR ▸ hd⟩

/-- A truth-valued product at a positive codomain sort is its domain's
emptiness: `{∅}` over the empty domain, `∅` otherwise. -/
theorem piSet_of_mem_univZero {D : V} {F : V → V} (h : piSet D F ∈ˢ (univZero : V)) :
    piSet D F = (open Classical in if ∃ d, d ∈ˢ D then empty else unitSet) := by
  classical
  split
  · rename_i hne
    obtain ⟨d, hd⟩ := hne
    refine ext fun f => ⟨fun hf => ?_, fun hf => absurd hf (not_mem_empty f)⟩
    have hf' := eq_pt_of_mem_univZero h hf
    exact absurd hf' (ne_pt_of_mem_piSet hf)
  · rename_i hne
    have hD : D = empty := ext fun d => ⟨fun hd => absurd ⟨d, hd⟩ hne,
      fun hd => absurd hd (not_mem_empty d)⟩
    subst hD
    refine ext fun f => ⟨fun hf => ?_, fun hf => ?_⟩
    · exact mem_unitSet_iff.mpr (eq_pt_of_mem_univZero h hf)
    · -- the empty graph
      have hg : graph (fun _ => (empty : V)) empty ∈ˢ piSet empty F :=
        graph_mem_piSet fun d hd => absurd hd (not_mem_empty d)
      have := eq_pt_of_mem_univZero h hg
      rw [mem_unitSet_iff.mp hf, ← this]
      exact hg

/-- **The type regime of a Π over a hole-free domain**: at a positive
codomain sort a truth-valued product only depends on its (hole-free)
domain; at `v = 0` the body is truth-valued (the grading) and in the type
regime, so it is hole-free, and so is the product. -/
theorem TypeReg.pi {R : FrameRel V} {D B : AnnotTerm} (u v : Nat) (hD : ConstOn R D)
    (hB : TypeReg (R.underBoth D) B)
    (hB0 : v = 0 → ∀ σ σ', R.underBoth D σ σ' →
      interp V σ B ∈ˢ (univZero : V) ∧ interp V σ' B ∈ˢ (univZero : V)) :
    TypeReg R (.pi u v D B) := by
  intro htv
  by_cases hv : v = 0
  · exact ConstOn.pi u v hD (hB (hB0 hv))
  · intro ρ ρ' hR
    have h1 := (htv ρ ρ' hR).1
    have h2 := (htv ρ ρ' hR).2
    simp only [interp_pi, piR_pos hv] at h1 h2 ⊢
    rw [piSet_of_mem_univZero h1, piSet_of_mem_univZero h2, hD ρ ρ' hR]

/-- **A hole at its full arity is never truth-valued at every related
frame unless it is empty at all of them** (richness), so a member hole
applied to hole-free arguments is in the type regime. -/
theorem TypeReg.holeApp {Q : Nat → Nat → Prop} {R : FrameRel V} (hrich : RichOn Q R)
    (hsymm : R.Symm) {h : Nat} {es : List AnnotTerm} (hQ : Q h es.length)
    (hes : ∀ e ∈ es, ConstOn R e) : TypeReg R (AnnotTerm.mkAppN (.bvar h) es) := by
  intro htv
  -- at every frame of the relation the value is empty
  have hemp : ∀ ρ ρ', R ρ ρ' → interp V ρ (AnnotTerm.mkAppN (.bvar h) es) = empty := by
    intro ρ ρ' hR
    have hsub := mem_univZero.mp (htv ρ ρ' hR).1
    refine ext fun y => ⟨fun hy => ?_, fun hy => absurd hy (not_mem_empty y)⟩
    exfalso
    have hy' := hy
    rw [mem_unitSet_iff.mp (hsub y hy)] at hy'
    rw [interp_mkAppN_map, interp_bvar] at hy'
    obtain ⟨ρ'', hR'', -, z, hz, hzp⟩ := hrich ρ ρ' hR h (es.map (interp V ρ)) (by simpa using hQ) hy'
    have hsub'' := mem_univZero.mp (htv ρ ρ'' hR'').2
    have hmap : es.map (interp V ρ) = es.map (interp V ρ'') :=
      List.map_congr_left fun e he => hes e he ρ ρ'' hR''
    rw [hmap] at hz
    rw [interp_mkAppN_map, interp_bvar] at hsub''
    exact hzp (mem_unitSet_iff.mp (hsub'' z hz))
  intro ρ ρ' hR
  rw [hemp ρ ρ' hR, hemp ρ' ρ (hsymm ρ ρ' hR)]

/-- **A frame's hole at its key's parameters and hole-free indices, at
its full arity** is in the type regime. -/
theorem TypeReg.holeAppArgs {Q : Nat → Nat → Prop} {R : FrameRel V} (hrich : RichOn Q R)
    (hsymm : R.Symm) {h : Nat} {ds is : List AnnotTerm} (hQ : Q h (ds.length + is.length))
    (hbl : FrameBlind R h ds) (his : ∀ e ∈ is, ConstOn R e) :
    TypeReg R (AnnotTerm.mkAppN (.bvar h) (ds ++ is)) := by
  intro htv
  have hemp : ∀ ρ ρ', R ρ ρ' → interp V ρ (AnnotTerm.mkAppN (.bvar h) (ds ++ is)) = empty := by
    intro ρ ρ' hR
    have hsub := mem_univZero.mp (htv ρ ρ' hR).1
    refine ext fun y => ⟨fun hy => ?_, fun hy => absurd hy (not_mem_empty y)⟩
    exfalso
    have hy' := hy
    rw [mem_unitSet_iff.mp (hsub y hy)] at hy'
    rw [interp_mkAppN_map, interp_bvar, List.map_append] at hy'
    obtain ⟨ρ'', hR'', -, z, hz, hzp⟩ := hrich ρ ρ' hR h _ (by simpa using hQ) hy'
    have hsub'' := mem_univZero.mp (htv ρ ρ'' hR'').2
    have hmap : is.map (interp V ρ) = is.map (interp V ρ'') :=
      List.map_congr_left fun e he => his e he ρ ρ'' hR''
    rw [hmap, hbl ρ ρ'' hR''] at hz
    rw [interp_mkAppN_map, interp_bvar, List.map_append] at hsub''
    exact hzp (mem_unitSet_iff.mp (hsub'' z hz))
  intro ρ ρ' hR
  rw [hemp ρ ρ' hR, hemp ρ' ρ (hsymm ρ ρ' hR)]

/-! ## Bounds reading given positions -/

/-- The positions `M` seen one binder down, the bound variable read. -/
def liftM (M : Nat → Prop) : Nat → Prop
  | 0 => True
  | i + 1 => M i

omit [SetTheory V] in
theorem InvOn.const (M : Nat → Prop) (c : V) : InvOn M (fun _ : Nat → V => c) :=
  fun _ _ _ => rfl

/-- **The Π bound reads what its domain and its body's bound read.** -/
theorem InvOn.pi {w : Nat} {M : Nat → Prop} {D : AnnotTerm} (hD : NoBVar (fun i => ¬ M i) D)
    {Bb : (Nat → V) → V} (hB : InvOn (liftM M) Bb) : InvOn M (piBound w D Bb) := by
  intro ρ ρ' hag
  have hD' : interp V ρ D = interp V ρ' D :=
    interp_congr_noBVar D hD fun i hi => hag i (Classical.byContradiction hi)
  have hb : ∀ d, Bb (cons d ρ) = Bb (cons d ρ') := by
    intro d
    refine hB _ _ fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact hag i hi
  unfold piBound
  rw [hD']
  simp only [hb]

end ConLeche.Semantics
