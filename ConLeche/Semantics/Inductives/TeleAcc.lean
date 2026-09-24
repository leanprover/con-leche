module

public import ConLeche.Semantics.Inductives.HoleAcc
public import ConLeche.Semantics.Sat

@[expose] public section

/-!
# A constructor's field telescope, accessible with ONE bound (lane ACCMODEL)

The run inversion (`Model/Inductives/NestPosAcc.lean`) makes every field
of a member constructor accessible under the earlier fields, each with a
bound that is a FUNCTION of the frame (`TeleAccP`).  (W) needs one bound
for all the tuples of the space.  A fitting spine's support is the glued
supports of its fields (`teleBound_support`); its index set lies in the
TELESCOPE'S BOUND `teleBound`, computed along the fields:

* the field's own bound, guarded to the level;
* for the later fields: at an ORDINARY field (its reading hole-free and
  reading no non-ordinary field) the union over the field's values of the
  later fields' bound; at a non-ordinary (recursive, reflexive, nested)
  field the later fields' bound at a junk value — no later field and no
  later bound reads that slot (U4).

The telescope's bound is then the same at any two frames agreeing off the
holes and at the ordinary slots (`teleBound_agr`, `TAgr`): at the hole
frames of any two tuples of the space.  It is a set of the level by
construction (`teleBound_mem`, the guards).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Guards and tags -/

/-- A set of the level, else `∅`. -/
noncomputable def guardU (w : Nat) (S : V) : V :=
  open Classical in if S ∈ˢ (univ w : V) then S else empty

theorem guardU_mem (w : Nat) (S : V) : guardU w S ∈ˢ (univ w : V) := by
  unfold guardU
  split
  · assumption
  · exact empty_mem_univ w

theorem guardU_eq {w : Nat} {S : V} (h : S ∈ˢ (univ w : V)) : guardU w S = S := by
  unfold guardU
  rw [if_pos h]

/-- The tagged union: `X` under the tag `∅`, `Y` under `{pt}`. -/
noncomputable def tagU (X Y : V) : V :=
  binUnion (image (kpair empty) X) (image (kpair unitSet) Y)

theorem tagU_mem {w : Nat} (hw : w ≠ 0) {X Y : V} (hX : X ∈ˢ (univ w : V))
    (hY : Y ∈ˢ (univ w : V)) : tagU X Y ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  have he : (empty : V) ∈ˢ (univ w : V) := empty_mem_univ w
  have hu : (unitSet : V) ∈ˢ (univ w : V) := unitSet_mem_univ w
  exact hU.binUnion_mem he
    (hU.image_mem hX fun x hx => hU.kpair_mem he he (hU.transitive hX hx))
    (hU.image_mem hY fun y hy => hU.kpair_mem he hu (hU.transitive hY hy))

theorem kpair_empty_mem_tagU {X Y b : V} (hb : b ∈ˢ X) : kpair empty b ∈ˢ tagU X Y :=
  mem_binUnion.mpr (Or.inl (mem_image.mpr ⟨b, hb, rfl⟩))

theorem kpair_unit_mem_tagU {X Y b : V} (hb : b ∈ˢ Y) : kpair unitSet b ∈ˢ tagU X Y :=
  mem_binUnion.mpr (Or.inr (mem_image.mpr ⟨b, hb, rfl⟩))

/-! ## The telescope's bound -/

/-- **The telescope's bound** at field `l` (see the module docstring):
`ord l` tells an ordinary field, `Af l` is field `l`'s own bound. -/
noncomputable def teleBound (w : Nat) (ord : Nat → Bool) (Af : Nat → (Nat → V) → V) :
    Nat → List AnnotTerm → (Nat → V) → V
  | _, [], _ => empty
  | l, F :: Fs, τ => tagU (guardU w (Af l τ))
      (if ord l = true then
        sUnion (image (fun a => teleBound w ord Af (l + 1) Fs (cons a τ)) (guardU w (interp V τ F)))
      else teleBound w ord Af (l + 1) Fs (cons empty τ))

theorem teleBound_mem {w : Nat} (hw : w ≠ 0) (ord : Nat → Bool) (Af : Nat → (Nat → V) → V) :
    ∀ (Fs : List AnnotTerm) (l : Nat) (τ : Nat → V), teleBound w ord Af l Fs τ ∈ˢ (univ w : V)
  | [], _, _ => empty_mem_univ w
  | F :: Fs, l, τ => by
    unfold teleBound
    refine tagU_mem hw (guardU_mem w _) ?_
    split
    · exact (univ_isTGUniverse hw).famUnion_mem (guardU_mem w _) fun a _ =>
        teleBound_mem hw ord Af Fs (l + 1) (cons a τ)
    · exact teleBound_mem hw ord Af Fs (l + 1) (cons empty τ)

/-- **Frames agreeing at the ordinary slots** below field `l` (the
positions `< l`, slot `l - 1 - i` at position `i`) and at the positions
`l + k` on (the parameters, above `k` holes). -/
def TAgr (k : Nat) (ord : Nat → Bool) (l : Nat) (τ τ' : Nat → V) : Prop :=
  ∀ i, (i < l → ord (l - 1 - i) = true → τ i = τ' i) ∧ (l + k ≤ i → τ i = τ' i)

omit [SetTheory V] in
theorem TAgr.cons_same {k : Nat} {ord : Nat → Bool} {l : Nat} {τ τ' : Nat → V}
    (h : TAgr k ord l τ τ') (a : V) :
    TAgr k ord (l + 1) (ConLeche.Semantics.cons a τ) (ConLeche.Semantics.cons a τ') := by
  intro i
  cases i with
  | zero => exact ⟨fun _ _ => rfl, fun _ => rfl⟩
  | succ i =>
    refine ⟨fun hi ho => (h i).1 (by omega) ?_, fun hi => (h i).2 (by omega)⟩
    rwa [show l + 1 - 1 - (i + 1) = l - 1 - i by omega] at ho

omit [SetTheory V] in
theorem TAgr.cons_nonord {k : Nat} {ord : Nat → Bool} {l : Nat} {τ τ' : Nat → V}
    (h : TAgr k ord l τ τ') (ho : ord l = false) (a b : V) :
    TAgr k ord (l + 1) (ConLeche.Semantics.cons a τ) (ConLeche.Semantics.cons b τ') := by
  intro i
  cases i with
  | zero =>
    refine ⟨fun _ ho' => ?_, fun hi => by omega⟩
    rw [show l + 1 - 1 - 0 = l by omega, ho] at ho'
    exact absurd ho' (by decide)
  | succ i =>
    refine ⟨fun hi ho => (h i).1 (by omega) ?_, fun hi => (h i).2 (by omega)⟩
    rwa [show l + 1 - 1 - (i + 1) = l - 1 - i by omega] at ho

/-- **The telescope's bound reads only the agreeing positions**, when every
field's own bound does and every ordinary field's reading does. -/
theorem teleBound_agr {w k : Nat} {ord : Nat → Bool} {Af : Nat → (Nat → V) → V}
    (hAf : ∀ l τ τ', TAgr k ord l τ τ' → Af l τ = Af l τ') :
    ∀ (Fs : List AnnotTerm) (l : Nat),
      (∀ (i : Nat) (F : AnnotTerm), Fs[i]? = some F → ord (l + i) = true →
        ∀ τ τ', TAgr k ord (l + i) τ τ' → interp V τ F = interp V τ' F) →
      ∀ τ τ', TAgr k ord l τ τ' → teleBound w ord Af l Fs τ = teleBound w ord Af l Fs τ'
  | [], _, _, _, _, _ => rfl
  | F :: Fs, l, hF, τ, τ', h => by
    have hrest : ∀ (i : Nat) (F' : AnnotTerm), Fs[i]? = some F' → ord (l + 1 + i) = true →
        ∀ σ σ', TAgr k ord (l + 1 + i) σ σ' → interp V σ F' = interp V σ' F' := by
      intro i F' hi ho σ σ' hs
      have := hF (i + 1) F' (by simpa using hi)
      rw [show l + (i + 1) = l + 1 + i by omega] at this
      exact this ho σ σ' hs
    unfold teleBound
    rw [hAf l τ τ' h]
    congr 1
    split
    · rename_i ho
      rw [hF 0 F rfl (by simpa using ho) τ τ' (by simpa using h)]
      congr 1
      refine image_congr fun a _ => ?_
      exact teleBound_agr hAf Fs (l + 1) hrest _ _ (h.cons_same a)
    · rename_i ho
      exact teleBound_agr hAf Fs (l + 1) hrest _ _
        (h.cons_nonord (by simpa using ho) empty empty)

/-! ## The support of a fitting spine -/

/-- **Every field accessible under the earlier ones**, with its own bound
`Af l` of the level, its reading a set of the level. -/
def TeleAccP (w : Nat) (Af : Nat → (Nat → V) → V) :
    Nat → (Nat → Nat → Prop) → FrameRel V → List AnnotTerm → Prop
  | _, _, _, [] => True
  | l, Q, R, F :: Fs => AccOn w Q R (Af l) F ∧ SizeOn w R (Af l) ∧
      (∀ ρ ρ₀, R ρ ρ₀ → interp V ρ F ∈ˢ (univ w : V)) ∧
      TeleAccP w Af (l + 1) (shiftQ Q) (R.underBoth F) Fs

/-- **A fitting spine's support** (see the module docstring): its index
set lies in the telescope's bound, its items are admissible and held,
and it carries the spine to every related frame.  The frame must be
related to itself (the top relation relates any two hole frames). -/
theorem teleBound_support {w k : Nat} (hw : w ≠ 0) {ord : Nat → Bool}
    {Af : Nat → (Nat → V) → V}
    (hAf : ∀ l τ τ', TAgr k ord l τ τ' → Af l τ = Af l τ') :
    ∀ (Fs : List AnnotTerm) (l : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V),
      (∀ (i : Nat) (F : AnnotTerm), Fs[i]? = some F → ord (l + i) = true →
        ∀ τ τ', TAgr k ord (l + i) τ τ' → interp V τ F = interp V τ' F) →
      TeleAccP w Af l Q R Fs → ∀ τ, R τ τ → ∀ fs, SpineFit τ Fs fs →
      ∃ (B : V) (g : V → Occ V), B ⊆ˢ teleBound w ord Af l Fs τ ∧
        (∀ b, b ∈ˢ B → Adm Q (g b) ∧ Holds τ (g b)) ∧
        ∀ τ', R τ τ' → (∀ b, b ∈ˢ B → Holds τ' (g b)) → SpineFit τ' Fs fs
  | [], _, _, _, _, _, τ, _, fs, hfit => by
    refine ⟨empty, fun _ => (0, [], empty), fun b hb => absurd hb (not_mem_empty b),
      fun b hb => absurd hb (not_mem_empty b), fun _ _ _ => ?_⟩
    cases fs with
    | nil => trivial
    | cons _ _ => exact hfit.elim
  | F :: Fs, l, Q, R, hF, hP, τ, hRτ, fs, hfit => by
    obtain ⟨hacc, hsz, hdom, hrest⟩ := hP
    cases fs with
    | nil => exact hfit.elim
    | cons a fs =>
    obtain ⟨ha, hfit'⟩ := hfit
    have haw : a ∈ˢ (univ w : V) := (univ_isTGUniverse hw).transitive (hdom τ τ hRτ) ha
    -- the field's own support
    obtain ⟨B0, g0, hB0, hg0, hs0⟩ := hacc τ τ hRτ a haw ha
    -- the later fields' support, under the field
    have hF' : ∀ (i : Nat) (F' : AnnotTerm), Fs[i]? = some F' → ord (l + 1 + i) = true →
        ∀ σ σ', TAgr k ord (l + 1 + i) σ σ' → interp V σ F' = interp V σ' F' := by
      intro i F' hi ho σ σ' hs
      have := hF (i + 1) F' (by simpa using hi)
      rw [show l + (i + 1) = l + 1 + i by omega] at this
      exact this ho σ σ' hs
    have hRa : R.underBoth F (cons a τ) (cons a τ) := ⟨a, τ, τ, rfl, rfl, hRτ, ha, ha⟩
    obtain ⟨B1, g1, hB1, hg1, hs1⟩ :=
      teleBound_support hw hAf Fs (l + 1) (shiftQ Q) (R.underBoth F) hF' hrest (cons a τ) hRa
        fs hfit'
    -- an item of the later fields is never the field's own variable
    have hne : ∀ b, b ∈ˢ B1 → (g1 b).1 ≠ 0 := by
      intro b hb h0
      have := (hg1 b hb).1
      unfold Adm at this
      rw [h0] at this
      exact this
    classical
    refine ⟨tagU B0 B1, fun p => if sfst p = empty then g0 (ssnd p) else (g1 (ssnd p)).down,
      ?_, ?_, ?_⟩
    · -- the index set
      intro p hp
      unfold teleBound
      rcases mem_binUnion.mp hp with hp | hp
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        refine kpair_empty_mem_tagU ?_
        rw [guardU_eq (hsz τ τ hRτ)]
        exact hB0 b hb
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        refine kpair_unit_mem_tagU ?_
        split
        · refine mem_sUnion.mpr ⟨_, mem_image.mpr ⟨a, ?_, rfl⟩, hB1 b hb⟩
          rw [guardU_eq (hdom τ τ hRτ)]
          exact ha
        · rename_i ho
          have hagr : TAgr k ord (l + 1) (cons a τ) (cons empty τ) :=
            TAgr.cons_nonord (fun _ => ⟨fun _ _ => rfl, fun _ => rfl⟩) (by simpa using ho) a empty
          rw [← teleBound_agr hAf Fs (l + 1) hF' _ _ hagr]
          exact hB1 b hb
    · -- the items
      intro p hp
      rcases mem_binUnion.mp hp with hp | hp
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        simp only [sfst_kpair, ssnd_kpair, if_true]
        exact hg0 b hb
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        simp only [sfst_kpair, ssnd_kpair, if_neg (unitSet_ne_empty (V := V))]
        obtain ⟨hQ, hH⟩ := hg1 b hb
        refine ⟨?_, (holds_cons_down (hne b hb)).mp hH⟩
        have h0 := hne b hb
        unfold Adm at hQ ⊢
        generalize g1 b = o at hQ h0
        obtain ⟨i, vs, y⟩ := o
        cases i with
        | zero => exact absurd rfl h0
        | succ i => exact hQ
    · -- at a related frame holding the items
      intro τ' hR' hheld
      have ha' : a ∈ˢ interp V τ' F := hs0 τ' hR' fun b hb => by
        have := hheld (kpair empty b) (kpair_empty_mem_tagU hb)
        simpa only [sfst_kpair, ssnd_kpair, if_true] using this
      refine ⟨ha', hs1 (cons a τ') ⟨a, τ, τ', rfl, rfl, hR', ha, ha'⟩ fun b hb => ?_⟩
      have := hheld (kpair unitSet b) (kpair_unit_mem_tagU hb)
      simp only [sfst_kpair, ssnd_kpair, if_neg (unitSet_ne_empty (V := V))] at this
      exact (holds_cons_down (hne b hb)).mpr this

/-! ## The relation under a telescope -/

namespace FrameRel

/-- **Under a field telescope**: each field's value in its domain at both
frames. -/
def underBothTele : FrameRel V → List AnnotTerm → FrameRel V
  | R, [] => R
  | R, F :: Fs => underBothTele (R.underBoth F) Fs

/-- The frames a spine fitting at both frames reaches are related along
the telescope. -/
theorem underBothTele_consList :
    ∀ {R : FrameRel V} {ρ ρ' : Nat → V} (Fs : List AnnotTerm) (as : List V),
      R ρ ρ' → SpineFit ρ Fs as → SpineFit ρ' Fs as →
      R.underBothTele Fs (consList as ρ) (consList as ρ')
  | _, _, _, [], [], hR, _, _ => hR
  | _, _, _, [], _ :: _, _, h, _ => h.elim
  | _, _, _, _ :: _, [], _, h, _ => h.elim
  | _, ρ, ρ', _ :: Fs, a :: as, hR, h, h' =>
    underBothTele_consList (R := _) Fs as ⟨a, ρ, ρ', rfl, rfl, hR, h.1, h'.1⟩ h.2 h'.2

end FrameRel

/-- **Domains reading alike give the same relation under them** (on a
relation whose frames satisfy the context). -/
theorem underBoth_eq_of_eqOn {R : FrameRel V} {Δ : List AnnotTerm} {A B : AnnotTerm}
    (h : ∀ ρ, Sat V Δ ρ → interp V ρ A = interp V ρ B)
    (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δ ρ ∧ Sat V Δ ρ') : R.underBoth A = R.underBoth B := by
  funext σ σ'
  apply propext
  constructor
  · rintro ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
    exact ⟨x, ρ, ρ', rfl, rfl, hR, h ρ (hdom ρ ρ' hR).1 ▸ hx, h ρ' (hdom ρ ρ' hR).2 ▸ hx'⟩
  · rintro ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
    exact ⟨x, ρ, ρ', rfl, rfl, hR, (h ρ (hdom ρ ρ' hR).1).symm ▸ hx,
      (h ρ' (hdom ρ ρ' hR).2).symm ▸ hx'⟩

/-- Under a domain, the frames satisfy the extended context. -/
theorem underBoth_dom {R : FrameRel V} {Δ : List AnnotTerm} {A : AnnotTerm}
    (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δ ρ ∧ Sat V Δ ρ') :
    ∀ σ σ', R.underBoth A σ σ' → Sat V (A :: Δ) σ ∧ Sat V (A :: Δ) σ' := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
  exact ⟨Sat_cons V (hdom ρ ρ' hR).1 hx, Sat_cons V (hdom ρ ρ' hR).2 hx'⟩

end ConLeche.Semantics
