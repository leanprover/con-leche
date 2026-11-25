module

public import ConLeche.Semantics.Inductives.HoleAcc
public import ConLeche.Semantics.Sat

@[expose] public section

/-!
# A constructor's field telescope, accessible with ONE bound (strictly first-order)

The run inversion (`Model/Inductives/NestPosAcc.lean`) makes every field
of a member constructor accessible under the earlier fields, each with a
bound that is a FUNCTION of the frame (`TeleAccP`).  (W) needs one bound
for all the tuples of the space.  A fitting spine's support is the glued
set-level support graph of its fields (`teleBound_support`); its index set
lies in the TELESCOPE'S BOUND `teleBound`, computed along the fields using
proof-carrying `image` (guarded by `HasImage`/`HasGraph`, discharged from
`DefBound`) and `tg_isGrothendieck`.
-/

namespace ConLeche.Semantics
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Guards and tags -/

/-- A set of the level, else `∅` (at `w = 0`, the set). -/
noncomputable def guardU (w : Nat) (S : V) : V :=
  open Classical in if SmallAt w S then S else empty

theorem guardU_mem {w : Nat} (hw : w ≠ 0) (S : V) : guardU w S ∈ˢ (tg w : V) := by
  unfold guardU
  split
  · rename_i h; exact h hw
  · exact empty_mem_tg w

theorem guardU_eq {w : Nat} {S : V} (h : SmallAt w S) : guardU w S = S := by
  unfold guardU
  rw [ite_eq_left h]

theorem DefFun.guardU_apply {k : Nat} (w : Nat) {S : (Fin k → V) → V} (hS : DefFun k S) :
    DefFun k fun env => guardU w (S env) := by
  unfold guardU
  by_cases hw : w = 0
  · subst hw
    exact (DefFun.ite DefRel.true hS DefFun.empty).congr fun env => by
      have h0 : SmallAt 0 (S env) := SmallAt.zero _
      simp [h0]
  · refine (DefFun.ite (DefRel.mem_apply hS (DefFun.tg_const w)) hS DefFun.empty).congr fun env => ?_
    by_cases hmem : S env ∈ˢ (tg w : V)
    · have hs : SmallAt w (S env) := fun _ => hmem
      simp [hs, hmem]
    · have hns : ¬ SmallAt w (S env) := fun hs => hmem (hs hw)
      simp [hns, hmem]

/-- The tagged union: `X` under the tag `∅`, `Y` under `{pt}`. -/
noncomputable def tagU (X Y : V) : V :=
  binUnion
    (image (kpair empty) X
      (hasImage_of_defFun1 (DefFun.kpair_apply DefFun.empty (DefFun.proj 0)) X))
    (image (kpair unitSet) Y
      (hasImage_of_defFun1 (DefFun.kpair_apply DefFun.unitSet (DefFun.proj 0)) Y))

theorem tagU_mem {w : Nat} (hw : w ≠ 0) {X Y : V} (hX : X ∈ˢ (tg w : V))
    (hY : Y ∈ˢ (tg w : V)) : tagU X Y ∈ˢ (tg w : V) := by
  have hU := tg_isGrothendieck (V := V) hw
  have he : (empty : V) ∈ˢ (tg w : V) := empty_mem_tg w
  have hu : (unitSet : V) ∈ˢ (tg w : V) := unitSet_mem_tg w
  have hGrX : HasImage (fun x => kpair x (kpair empty x)) X :=
    hasImage_of_defFun1 (f := fun x => kpair x (kpair empty x))
      (DefFun.kpair_apply (DefFun.proj 0) (DefFun.kpair_apply DefFun.empty (DefFun.proj 0))) X
  have hGrY : HasImage (fun y => kpair y (kpair unitSet y)) Y :=
    hasImage_of_defFun1 (f := fun y => kpair y (kpair unitSet y))
      (DefFun.kpair_apply (DefFun.proj 0) (DefFun.kpair_apply DefFun.unitSet (DefFun.proj 0))) Y
  exact hU.binUnion_mem
    (hU.image_mem hX (fun x hx => hU.kpair_mem he (hU.transitive hX hx)) _ hGrX)
    (hU.image_mem hY (fun y hy => hU.kpair_mem hu (hU.transitive hY hy)) _ hGrY)

theorem DefFun.tagU_apply {k : Nat} {X Y : (Fin k → V) → V}
    (hX : DefFun k X) (hY : DefFun k Y) : DefFun k fun env => tagU (X env) (Y env) := by
  unfold tagU
  exact DefFun.binUnion_apply
    (DefFun.image_apply_curry (DefFun.kpair_apply DefFun.empty (DefFun.proj 0)) hX)
    (DefFun.image_apply_curry (DefFun.kpair_apply DefFun.unitSet (DefFun.proj 0)) hY)

theorem kpair_empty_mem_tagU {X Y b : V} (hb : b ∈ˢ X) : kpair empty b ∈ˢ tagU X Y :=
  mem_binUnion.mpr (Or.inl (mem_image.mpr ⟨b, hb, rfl⟩))

theorem kpair_unit_mem_tagU {X Y b : V} (hb : b ∈ˢ Y) : kpair unitSet b ∈ˢ tagU X Y :=
  mem_binUnion.mpr (Or.inr (mem_image.mpr ⟨b, hb, rfl⟩))

/-! ## The telescope's bound -/

/-- **The telescope's bound** at field `l` (see the module docstring):
`ord l` tells an ordinary field, `Af l` is field `l`'s own bound. -/
noncomputable def teleBound (w : Nat) (ord : Nat → Bool) (Af : Nat → (Nat → V) → V) :
    Nat → List Term → (Nat → V) → V
  | _, [], _ => empty
  | l, F :: Fs, τ =>
      open Classical in
      tagU (guardU w (Af l τ))
        (if ord l = true then
          let S := guardU w (interp V τ F)
          let G := fun a => teleBound w ord Af (l + 1) Fs (cons a τ)
          if hImg : HasImage G S then
            if _hGr : HasGraph S G then sUnion (image G S hImg) else empty
          else empty
        else teleBound w ord Af (l + 1) Fs (cons empty τ))

theorem teleBound_mem {w : Nat} (hw : w ≠ 0) (ord : Nat → Bool) (Af : Nat → (Nat → V) → V) :
    ∀ (Fs : List Term) (l : Nat) (τ : Nat → V), teleBound w ord Af l Fs τ ∈ˢ (tg w : V)
  | [], _, _ => empty_mem_tg w
  | F :: Fs, l, τ => by
    unfold teleBound
    refine tagU_mem hw (guardU_mem hw _) ?_
    split
    · dsimp only
      split
      · rename_i hImg
        split
        · rename_i hGr
          exact (tg_isGrothendieck hw).famUnion_mem (guardU_mem hw _)
            (fun a _ => teleBound_mem hw ord Af Fs (l + 1) (cons a τ)) hImg hGr
        · exact empty_mem_tg w
      · exact empty_mem_tg w
    · exact teleBound_mem hw ord Af Fs (l + 1) (cons empty τ)

omit [SetTheory V] in
private theorem fcons_ftail_eq {k : Nat} (v : Fin (k + 1) → V) : fcons (v 0) (ftail v) = v := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i => rfl

open Classical in
/-- `teleBound` is definable (`DefBound (d0 + l)`) whenever each `Af l'`
for `l ≤ l' < l + Fs.length` is `DefBound (d0 + l')`. -/
theorem DefBound.teleBound (w : Nat) (ord : Nat → Bool) {Af : Nat → (Nat → V) → V} (d0 : Nat) :
    ∀ (Fs : List Term) (l : Nat),
      (∀ l', l ≤ l' → l' < l + Fs.length → DefBound (d0 + l') (Af l')) →
      DefBound (d0 + l) (Semantics.teleBound w ord Af l Fs)
  | [], l, _ => DefBound.const (d0 + l) empty
  | F :: Fs, l, hAf => fun tail => by
    have hAfl : DefFun (d0 + l) fun xs => Af l (prepend xs tail) :=
      hAf l (Nat.le_refl l) (by simp) tail
    have hRec : DefBound (d0 + l + 1) (Semantics.teleBound w ord Af (l + 1) Fs) :=
      DefBound.teleBound w ord d0 Fs (l + 1) fun l' h1 h2 =>
        hAf l' (by omega) (by simp at h2 ⊢; omega)
    have hF_def : DefFun (d0 + l) fun xs => interp V (prepend xs tail) F :=
      interp_defFun_prepend tail (d0 + l) F
    have hG_def : DefFun (d0 + l + 1) fun v =>
        Semantics.teleBound w ord Af (l + 1) Fs (cons (v 0) (prepend (ftail v) tail)) :=
      (hRec tail).congr fun v => by rw [← prepend_fcons, fcons_ftail_eq]
    by_cases ho : ord l = true
    · have hS_def : DefFun (d0 + l) fun xs => guardU w (interp V (prepend xs tail) F) :=
        DefFun.guardU_apply w hF_def
      have hImgAll : ∀ xs : Fin (d0 + l) → V,
          HasImage (fun a => Semantics.teleBound w ord Af (l + 1) Fs (cons a (prepend xs tail)))
            (guardU w (interp V (prepend xs tail) F)) := fun xs =>
        hasImage_of_defFun1
          ((hRec.defFun1_cons (prepend xs tail)).congr fun _ => rfl) _
      have hGrAll : ∀ xs : Fin (d0 + l) → V,
          HasGraph (guardU w (interp V (prepend xs tail) F))
            (fun a => Semantics.teleBound w ord Af (l + 1) Fs (cons a (prepend xs tail))) := fun xs =>
        hasGraph_of_defFun1
          ((hRec.defFun1_cons (prepend xs tail)).congr fun _ => rfl)
      have hU_def : DefFun (d0 + l) fun xs =>
          sUnion (image (fun a => Semantics.teleBound w ord Af (l + 1) Fs (cons a (prepend xs tail)))
            (guardU w (interp V (prepend xs tail) F)) (hImgAll xs)) :=
        DefFun.sUnion_apply (DefFun.image_apply_curry hG_def hS_def)
      refine (DefFun.tagU_apply (DefFun.guardU_apply w hAfl) hU_def).congr fun xs => ?_
      change tagU (guardU w (Af l (prepend xs tail)))
        (sUnion (image (fun a => Semantics.teleBound w ord Af (l + 1) Fs (cons a (prepend xs tail)))
          (guardU w (interp V (prepend xs tail) F)) (hImgAll xs))) =
        tagU (guardU w (Af l (prepend xs tail)))
          (if ord l = true then
            let S := guardU w (interp V (prepend xs tail) F)
            let G := fun a => Semantics.teleBound w ord Af (l + 1) Fs (cons a (prepend xs tail))
            if hImg : HasImage G S then
              if _hGr : HasGraph S G then sUnion (image G S hImg) else empty
            else empty
          else Semantics.teleBound w ord Af (l + 1) Fs (cons empty (prepend xs tail)))
      simp only [ho, ↓reduceIte, dite_eq_left (hImgAll xs), dite_eq_left (hGrAll xs)]
    · have hE_def : DefFun (d0 + l) fun xs =>
          Semantics.teleBound w ord Af (l + 1) Fs (cons empty (prepend xs tail)) := by
        let Gs : Fin (d0 + l + 1) → (Fin (d0 + l) → V) → V := fun j xs =>
          if hj : j.val = 0 then empty else xs ⟨j.val - 1, by omega⟩
        have hGs : ∀ j : Fin (d0 + l + 1), DefFun (d0 + l) (Gs j) := fun j => by
          dsimp only [Gs]
          by_cases hj : j.val = 0
          · simp only [hj, ↓reduceDIte]; exact DefFun.empty
          · simp only [hj, ↓reduceDIte]; exact DefFun.proj ⟨j.val - 1, by omega⟩
        refine ((hRec tail).comp hGs).congr fun xs => ?_
        congr 1
        funext j
        cases j with
        | zero => rfl
        | succ j =>
          by_cases hj : j < d0 + l
          · simp [Gs, prepend, cons, hj]
          · simp only [prepend, cons, hj, show ¬ (j + 1 < d0 + l + 1) by omega, ↓reduceDIte]
            congr 1; omega
      refine (DefFun.tagU_apply (DefFun.guardU_apply w hAfl) hE_def).congr fun xs => ?_
      change tagU (guardU w (Af l (prepend xs tail)))
        (Semantics.teleBound w ord Af (l + 1) Fs (cons empty (prepend xs tail))) =
        tagU (guardU w (Af l (prepend xs tail)))
          (if ord l = true then _ else Semantics.teleBound w ord Af (l + 1) Fs (cons empty (prepend xs tail)))
      simp [ho]

/-- **Frames agreeing at the ordinary slots** below field `l` and at the positions `l + k` on. -/
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

private theorem teleBound_dite_congr {S₁ S₂ : V} {G₁ G₂ : V → V}
    (hS : S₁ = S₂) (hG : ∀ a, G₁ a = G₂ a) :
    (open Classical in
      if hImg : HasImage G₁ S₁ then
        if _hGr : HasGraph S₁ G₁ then sUnion (image G₁ S₁ hImg) else empty
      else empty) =
    (open Classical in
      if hImg : HasImage G₂ S₂ then
        if _hGr : HasGraph S₂ G₂ then sUnion (image G₂ S₂ hImg) else empty
      else empty) := by
  subst hS
  have hImg_iff : HasImage G₁ S₁ ↔ HasImage G₂ S₁ :=
    ⟨fun h => h.congr fun a _ => hG a, fun h => h.congr fun a _ => (hG a).symm⟩
  have hGr_iff : HasGraph S₁ G₁ ↔ HasGraph S₁ G₂ :=
    ⟨fun h => HasImage.congr (fun a _ => congrArg (kpair a) (hG a)) h,
     fun h => HasImage.congr (fun a _ => congrArg (kpair a) (hG a).symm) h⟩
  by_cases hI₁ : HasImage G₁ S₁
  · have hI₂ : HasImage G₂ S₁ := hImg_iff.mp hI₁
    rw [dite_eq_left hI₁, dite_eq_left hI₂]
    by_cases hG₁ : HasGraph S₁ G₁
    · have hG₂ : HasGraph S₁ G₂ := hGr_iff.mp hG₁
      rw [dite_eq_left hG₁, dite_eq_left hG₂]
      exact congrArg sUnion (image_congr hI₁ hI₂ fun a _ => hG a)
    · have hG₂ : ¬ HasGraph S₁ G₂ := fun h => hG₁ (hGr_iff.mpr h)
      rw [dite_eq_right hG₁, dite_eq_right hG₂]
  · have hI₂ : ¬ HasImage G₂ S₁ := fun h => hI₁ (hImg_iff.mpr h)
    rw [dite_eq_right hI₁, dite_eq_right hI₂]

/-- **The telescope's bound reads only the agreeing positions**, when every
field's own bound does and every ordinary field's reading does. -/
theorem teleBound_agr {w k : Nat} {ord : Nat → Bool} {Af : Nat → (Nat → V) → V}
    (hAf : ∀ l τ τ', TAgr k ord l τ τ' → Af l τ = Af l τ') :
    ∀ (Fs : List Term) (l : Nat),
      (∀ (i : Nat) (F : Term), Fs[i]? = some F → ord (l + i) = true →
        ∀ τ τ', TAgr k ord (l + i) τ τ' → interp V τ F = interp V τ' F) →
      ∀ τ τ', TAgr k ord l τ τ' → teleBound w ord Af l Fs τ = teleBound w ord Af l Fs τ'
  | [], _, _, _, _, _ => rfl
  | F :: Fs, l, hF, τ, τ', h => by
    have hrest : ∀ (i : Nat) (F' : Term), Fs[i]? = some F' → ord (l + 1 + i) = true →
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
      refine teleBound_dite_congr
        (by rw [hF 0 F rfl (by simpa using ho) τ τ' (by simpa using h)])
        (fun a => teleBound_agr hAf Fs (l + 1) hrest _ _ (h.cons_same a))
    · rename_i ho
      exact teleBound_agr hAf Fs (l + 1) hrest _ _
        (h.cons_nonord (by simpa using ho) empty empty)

/-- **Frames agreeing at the ordinary slots and at the base positions `M0`**. -/
def TAgrM (k : Nat) (M0 : Nat → Prop) (ord : Nat → Bool) (l : Nat) (τ τ' : Nat → V) : Prop :=
  ∀ i, (i < l → ord (l - 1 - i) = true → τ i = τ' i) ∧ (l + k ≤ i → M0 (i - l) → τ i = τ' i)

omit [SetTheory V] in
theorem TAgr.toM {k : Nat} {ord : Nat → Bool} {l : Nat} {τ τ' : Nat → V}
    (h : TAgr k ord l τ τ') (M0 : Nat → Prop) : TAgrM k M0 ord l τ τ' :=
  fun i => ⟨(h i).1, fun hi _ => (h i).2 hi⟩

omit [SetTheory V] in
theorem TAgrM.cons_same {k : Nat} {M0 : Nat → Prop} {ord : Nat → Bool} {l : Nat}
    {τ τ' : Nat → V} (h : TAgrM k M0 ord l τ τ') (a : V) :
    TAgrM k M0 ord (l + 1) (ConLeche.Semantics.cons a τ) (ConLeche.Semantics.cons a τ') := by
  intro i
  cases i with
  | zero => exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  | succ i =>
    refine ⟨fun hi ho => (h i).1 (by omega) ?_, fun hi hm => (h i).2 (by omega) ?_⟩
    · rwa [show l + 1 - 1 - (i + 1) = l - 1 - i by omega] at ho
    · rwa [show i + 1 - (l + 1) = i - l by omega] at hm

omit [SetTheory V] in
theorem TAgrM.cons_nonord {k : Nat} {M0 : Nat → Prop} {ord : Nat → Bool} {l : Nat}
    {τ τ' : Nat → V} (h : TAgrM k M0 ord l τ τ') (ho : ord l = false) (a b : V) :
    TAgrM k M0 ord (l + 1) (ConLeche.Semantics.cons a τ) (ConLeche.Semantics.cons b τ') := by
  intro i
  cases i with
  | zero =>
    refine ⟨fun _ ho' => ?_, fun hi => by omega⟩
    rw [show l + 1 - 1 - 0 = l by omega, ho] at ho'
    exact absurd ho' (by decide)
  | succ i =>
    refine ⟨fun hi ho => (h i).1 (by omega) ?_, fun hi hm => (h i).2 (by omega) ?_⟩
    · rwa [show l + 1 - 1 - (i + 1) = l - 1 - i by omega] at ho
    · rwa [show i + 1 - (l + 1) = i - l by omega] at hm

/-- **`teleBound_agr` at the base positions `M0`.** -/
theorem teleBound_agrM {w k : Nat} {M0 : Nat → Prop} {ord : Nat → Bool}
    {Af : Nat → (Nat → V) → V}
    (hAf : ∀ l τ τ', TAgrM k M0 ord l τ τ' → Af l τ = Af l τ') :
    ∀ (Fs : List Term) (l : Nat),
      (∀ (i : Nat) (F : Term), Fs[i]? = some F → ord (l + i) = true →
        ∀ τ τ', TAgrM k M0 ord (l + i) τ τ' → interp V τ F = interp V τ' F) →
      ∀ τ τ', TAgrM k M0 ord l τ τ' → teleBound w ord Af l Fs τ = teleBound w ord Af l Fs τ'
  | [], _, _, _, _, _ => rfl
  | F :: Fs, l, hF, τ, τ', h => by
    have hrest : ∀ (i : Nat) (F' : Term), Fs[i]? = some F' → ord (l + 1 + i) = true →
        ∀ σ σ', TAgrM k M0 ord (l + 1 + i) σ σ' → interp V σ F' = interp V σ' F' := by
      intro i F' hi ho σ σ' hs
      have := hF (i + 1) F' (by simpa using hi)
      rw [show l + (i + 1) = l + 1 + i by omega] at this
      exact this ho σ σ' hs
    unfold teleBound
    rw [hAf l τ τ' h]
    congr 1
    split
    · rename_i ho
      refine teleBound_dite_congr
        (by rw [hF 0 F rfl (by simpa using ho) τ τ' (by simpa using h)])
        (fun a => teleBound_agrM hAf Fs (l + 1) hrest _ _ (h.cons_same a))
    · rename_i ho
      exact teleBound_agrM hAf Fs (l + 1) hrest _ _
        (h.cons_nonord (by simpa using ho) empty empty)

/-! ## The support of a fitting spine -/

/-- **Every field accessible under the earlier ones**, with its own bound
`Af l` of the level, its reading a set of the level. -/
def TeleAccP (w : Nat) (Af : Nat → (Nat → V) → V) :
    Nat → (Nat → Nat → Prop) → FrameRel V → List Term → Prop
  | _, _, _, [] => True
  | l, Q, R, F :: Fs => AccOn w Q R (Af l) F ∧ SizeOn w R (Af l) ∧
      (∀ ρ ρ₀, R ρ ρ₀ → SmallAt w (interp V ρ F)) ∧
      TeleAccP w Af (l + 1) (shiftQ Q) (R.underBoth F) Fs

open Classical in
/-- **A fitting spine's support** (strictly first-order): returns a set-level
support graph `g ∈ˢ piSet B (fun _ => U) _` indexed by `B ⊆ˢ teleBound w ord Af l Fs τ`. -/
theorem teleBound_support {w k d0 : Nat} {ord : Nat → Bool}
    {Af : Nat → (Nat → V) → V}
    (hAf : ∀ l τ τ', TAgr k ord l τ τ' → Af l τ = Af l τ')
    (hAf_def : ∀ l', 0 ≤ l' → DefBound (d0 + l') (Af l')) :
    ∀ (Fs : List Term) (l : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V),
      (∀ (i : Nat) (F : Term), Fs[i]? = some F → ord (l + i) = true →
        ∀ τ τ', TAgr k ord (l + i) τ τ' → interp V τ F = interp V τ' F) →
      TeleAccP w Af l Q R Fs → ∀ τ, R τ τ → ∀ fs, SpineFit τ Fs fs →
      ∃ (B g : V), B ⊆ˢ teleBound w ord Af l Fs τ ∧
        (∃ U : V, g ∈ˢ piSet B (fun _ => U) (hasSigmaPairs_const _ _)) ∧
        (∀ b, b ∈ˢ B → AdmItem Q (app g b) ∧ HoldsNonPt τ (app g b)) ∧
        ∀ τ', R τ τ' → (∀ b, b ∈ˢ B → HoldsItem τ' (app g b)) → SpineFit τ' Fs fs
  | [], _, _, _, _, _, τ, _, fs, hfit => by
    refine ⟨empty, graph (fun _ => empty) empty (hasGraph_empty (V := V) fun _ => empty),
      fun b hb => absurd hb (not_mem_empty b),
      ⟨empty, graph_mem_piSet fun _ hb => absurd hb (not_mem_empty _)⟩,
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
    have haw : SmallAt w a := fun hw => (tg_isGrothendieck hw).transitive (hdom τ τ hRτ hw) ha
    obtain ⟨B0, g0, hB0, ⟨U0, hg0⟩, hitems0, hs0⟩ := hacc τ τ hRτ a haw ha
    have hF' : ∀ (i : Nat) (F' : Term), Fs[i]? = some F' → ord (l + 1 + i) = true →
        ∀ σ σ', TAgr k ord (l + 1 + i) σ σ' → interp V σ F' = interp V σ' F' := by
      intro i F' hi ho σ σ' hs
      have := hF (i + 1) F' (by simpa using hi)
      rw [show l + (i + 1) = l + 1 + i by omega] at this
      exact this ho σ σ' hs
    have hRa : R.underBoth F (cons a τ) (cons a τ) := ⟨a, τ, τ, rfl, rfl, hRτ, ha, ha⟩
    obtain ⟨B1, g1, hB1, ⟨U1, hg1⟩, hitems1, hs1⟩ :=
      teleBound_support hAf hAf_def Fs (l + 1) (shiftQ Q) (R.underBoth F) hF' hrest
        (cons a τ) hRa fs hfit'
    have hg_def : DefFun 1 fun v =>
        if sfst (v 0) = empty then app g0 (ssnd (v 0)) else downOcc (app g1 (ssnd (v 0))) :=
      DefFun.ite (DefRel.eq_apply (DefFun.sfst_apply (DefFun.proj 0)) DefFun.empty)
        (DefFun.app_apply (DefFun.const g0) (DefFun.ssnd_apply (DefFun.proj 0)))
        (DefFun.downOcc_apply
          (DefFun.app_apply (DefFun.const g1) (DefFun.ssnd_apply (DefFun.proj 0))))
    let g := graph (fun p => if sfst p = empty then app g0 (ssnd p) else downOcc (app g1 (ssnd p)))
      (tagU B0 B1) (hasGraph_of_defFun1 hg_def)
    let U := binUnion U0
      (image downOcc U1 (hasImage_of_defFun1 (DefFun.downOcc_apply (DefFun.proj 0)) U1))
    refine ⟨tagU B0 B1, g, ?_, ⟨U, graph_mem_piSet fun p hp => ?_⟩, ?_, ?_⟩
    · intro p hp
      unfold teleBound
      rcases mem_binUnion.mp hp with hp | hp
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        refine kpair_empty_mem_tagU ?_
        rw [guardU_eq (hsz τ τ hRτ)]
        exact hB0 b hb
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        refine kpair_unit_mem_tagU ?_
        split
        · have hDefRec : DefBound (d0 + (l + 1)) (teleBound w ord Af (l + 1) Fs) :=
            DefBound.teleBound w ord d0 Fs (l + 1) fun l' _ _ => hAf_def l' (Nat.zero_le _)
          have hImg : HasImage (fun x => teleBound w ord Af (l + 1) Fs (cons x τ))
              (guardU w (interp V τ F)) :=
            hasImage_of_defFun1 ((hDefRec.defFun1_cons τ).congr fun _ => rfl) _
          have hGr : HasGraph (guardU w (interp V τ F))
              (fun x => teleBound w ord Af (l + 1) Fs (cons x τ)) :=
            hasGraph_of_defFun1 ((hDefRec.defFun1_cons τ).congr fun _ => rfl)
          rw [dite_eq_left hImg, dite_eq_left hGr]
          refine mem_sUnion.mpr ⟨_, mem_image.mpr ⟨a, ?_, rfl⟩, hB1 b hb⟩
          rw [guardU_eq (hdom τ τ hRτ)]
          exact ha
        · rename_i ho
          have hagr : TAgr k ord (l + 1) (cons a τ) (cons empty τ) :=
            TAgr.cons_nonord (fun _ => ⟨fun _ _ => rfl, fun _ => rfl⟩) (by simpa using ho) a empty
          rw [← teleBound_agr hAf Fs (l + 1) hF' _ _ hagr]
          exact hB1 b hb
    · rcases mem_binUnion.mp hp with hp | hp
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        rw [sfst_kpair, ssnd_kpair, ite_eq_left rfl]
        exact mem_binUnion.mpr (Or.inl (app_mem_of_mem_piSet hg0 hb))
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        rw [sfst_kpair, ssnd_kpair, ite_eq_right (unitSet_ne_empty (V := V))]
        exact mem_binUnion.mpr (Or.inr (mem_image.mpr ⟨_, app_mem_of_mem_piSet hg1 hb, rfl⟩))
    · intro p hp
      dsimp only [g]
      rw [app_graph hp]
      rcases mem_binUnion.mp hp with hp | hp
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        rw [sfst_kpair, ssnd_kpair, ite_eq_left rfl]
        exact hitems0 b hb
      · obtain ⟨b, hb, rfl⟩ := mem_image.mp hp
        rw [sfst_kpair, ssnd_kpair, ite_eq_right (unitSet_ne_empty (V := V))]
        obtain ⟨hQ1, hH1⟩ := hitems1 b hb
        obtain ⟨i, vs, y, heq1, hq1⟩ := hQ1
        obtain ⟨i', vs', y', heq2, hnp, hy⟩ := hH1
        obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj (heq1.symm.trans heq2)
        cases i with
        | zero => exact hq1.elim
        | succ i =>
          rw [heq1, downOcc_occEncItem]
          exact ⟨⟨i, vs, y, rfl, hq1⟩, ⟨i, vs, y, rfl, hnp, hy⟩⟩
    · intro τ' hR' hheld
      have ha' : a ∈ˢ interp V τ' F := hs0 τ' hR' fun b hb => by
        have hi := hheld (kpair empty b) (kpair_empty_mem_tagU hb)
        dsimp only [g] at hi
        rwa [app_graph (kpair_empty_mem_tagU hb), sfst_kpair, ssnd_kpair, ite_eq_left rfl] at hi
      refine ⟨ha', hs1 (cons a τ') ⟨a, τ, τ', rfl, rfl, hR', ha, ha'⟩ fun b hb => ?_⟩
      have hi := hheld (kpair unitSet b) (kpair_unit_mem_tagU hb)
      dsimp only [g] at hi
      rw [app_graph (kpair_unit_mem_tagU hb), sfst_kpair, ssnd_kpair,
        ite_eq_right (unitSet_ne_empty (V := V))] at hi
      obtain ⟨i, vs, y, heq1, hq1⟩ := (hitems1 b hb).1
      cases i with
      | zero => exact hq1.elim
      | succ i =>
        rw [heq1, downOcc_occEncItem] at hi
        obtain ⟨i', vs', y', heq', hy'⟩ := hi
        obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj heq'
        exact ⟨i + 1, vs, y, heq1, hy'⟩

/-! ## The relation under a telescope -/

namespace FrameRel

/-- **Under a field telescope**: each field's value in its domain at both
frames. -/
def underBothTele : FrameRel V → List Term → FrameRel V
  | R, [] => R
  | R, F :: Fs => underBothTele (R.underBoth F) Fs

/-- The frames a spine fitting at both frames reaches are related along
the telescope. -/
theorem underBothTele_consList :
    ∀ {R : FrameRel V} {ρ ρ' : Nat → V} (Fs : List Term) (as : List V),
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
theorem underBoth_eq_of_eqOn {R : FrameRel V} {Δ : List Term} {A B : Term}
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
theorem underBoth_dom {R : FrameRel V} {Δ : List Term} {A : Term}
    (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δ ρ ∧ Sat V Δ ρ') :
    ∀ σ σ', R.underBoth A σ σ' → Sat V (A :: Δ) σ ∧ Sat V (A :: Δ) σ' := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
  exact ⟨Sat_cons V (hdom ρ ρ' hR).1 hx, Sat_cons V (hdom ρ ρ' hR).2 hx'⟩

end ConLeche.Semantics
