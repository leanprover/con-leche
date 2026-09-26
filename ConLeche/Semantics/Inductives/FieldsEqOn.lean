module

public import ConLeche.Semantics.Inductives.HoleMono
public import ConLeche.Semantics.Sat

@[expose] public section

/-!
# Field lists that read alike (lane ALPHA1)

`FieldsEqOn V Δ As Bs`: two field lists read alike along every prefix
satisfying the context `Δ` (innermost first) extended by the earlier
fields.  The positivity walk's normal form of a constructor type reads
like the declared type in exactly this sense (`memberCtorD_red`,
`Model/Inductives/NestPosRed.lean`); what that is used for follows from
the definition alone: fitting spines agree, field-wise positivity moves
across, and so does the relation under the fields.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory

universe w

variable {V : Type w} [SetTheory V]


/-- **Two field lists read alike along every satisfying prefix**: the
first fields at every frame satisfying `Δ`, the rest under the first
field (either one: they read alike there). -/
def FieldsEqOn (V : Type w) [SetTheory V] :
    List AnnotTerm → List AnnotTerm → List AnnotTerm → Prop
  | _, [], [] => True
  | Δ, A :: As, B :: Bs =>
    (∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ A = interp V ρ B) ∧ FieldsEqOn V (A :: Δ) As Bs
  | _, _, _ => False

theorem FieldsEqOn.refl : ∀ (Δ As : List AnnotTerm), FieldsEqOn V Δ As As
  | _, [] => trivial
  | Δ, A :: As => ⟨fun _ _ => rfl, FieldsEqOn.refl (A :: Δ) As⟩

theorem FieldsEqOn.length_eq :
    ∀ {Δ As Bs : List AnnotTerm}, FieldsEqOn V Δ As Bs → As.length = Bs.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, h => by simp [FieldsEqOn.length_eq h.2]
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim

/-- A context whose head reads alike is satisfied alike. -/
theorem sat_cons_congr {Δ : List AnnotTerm} {A B : AnnotTerm}
    (h : ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ A = interp V ρ B) {ρ : Nat → V}
    (hs : Sat V (A :: Δ) ρ) : Sat V (B :: Δ) ρ := by
  intro i Aa hi
  cases i with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
    subst hi
    have := hs 0 A rfl
    rw [h _ (Sat_tail hs)] at this
    simpa using this
  | succ i => exact hs (i + 1) Aa (by simpa using hi)

/-- Fitting spines agree along field lists that read alike. -/
theorem FieldsEqOn.spineFit_iff :
    ∀ {Δ As Bs : List AnnotTerm}, FieldsEqOn V Δ As Bs → ∀ {ρ : Nat → V}, Sat V Δ ρ →
      ∀ fs : List V, SpineFit ρ As fs ↔ SpineFit ρ Bs fs
  | _, [], [], _, _, _, fs => Iff.rfl
  | _, A :: As, B :: Bs, h, ρ, hρ, [] => by simp [SpineFit]
  | Δ, A :: As, B :: Bs, h, ρ, hρ, x :: fs => by
    simp only [SpineFit]
    constructor
    · rintro ⟨hx, hfs⟩
      exact ⟨h.1 ρ hρ ▸ hx, (FieldsEqOn.spineFit_iff h.2 (Sat_cons V hρ hx) fs).mp hfs⟩
    · rintro ⟨hx, hfs⟩
      have hx' : x ∈ˢ interp V ρ A := (h.1 ρ hρ).symm ▸ hx
      exact ⟨hx', (FieldsEqOn.spineFit_iff h.2 (Sat_cons V hρ hx') fs).mpr hfs⟩
  | _, [], _ :: _, h, _, _, _ => h.elim
  | _, _ :: _, [], h, _, _, _ => h.elim


/-- Spines fit two field lists alike when the fields read alike at every
prefix. -/
theorem spineFit_congr_all {σ ρ : Nat → V} :
    ∀ {Fs Gs : List AnnotTerm}, Fs.length = Gs.length →
      (∀ (i : Nat) (as : List V), i < Fs.length → as.length = i →
        interp V (consList as σ) (Fs.getD i default)
          = interp V (consList as ρ) (Gs.getD i default)) →
      ∀ fs : List V, SpineFit σ Fs fs ↔ SpineFit ρ Gs fs
  | [], [], _, _, fs => by cases fs <;> simp [SpineFit]
  | F :: Fs, G :: Gs, hl, h, [] => by simp [SpineFit]
  | F :: Fs, G :: Gs, hl, h, x :: fs => by
    simp only [SpineFit]
    have h0 : interp V σ F = interp V ρ G := h 0 [] (by simp) rfl
    rw [h0]
    refine and_congr_right fun _ => spineFit_congr_all (σ := cons x σ) (ρ := cons x ρ)
      (by simpa using hl) (fun i as hi has => ?_) fs
    have := h (i + 1) (x :: as) (by simp; omega) (by simp [has])
    simpa using this
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- Spines fit two field lists alike when the fields read alike along
every prefix fitting the second list. -/
theorem spineFit_congr_fit {σ ρ : Nat → V} :
    ∀ {Fs Gs : List AnnotTerm}, Fs.length = Gs.length →
      (∀ (i : Nat) (as : List V), i < Fs.length → as.length = i → SpineFit ρ (Gs.take i) as →
        interp V (consList as σ) (Fs.getD i default)
          = interp V (consList as ρ) (Gs.getD i default)) →
      ∀ fs : List V, SpineFit σ Fs fs ↔ SpineFit ρ Gs fs
  | [], [], _, _, fs => by cases fs <;> simp [SpineFit]
  | F :: Fs, G :: Gs, hl, h, [] => by simp [SpineFit]
  | F :: Fs, G :: Gs, hl, h, x :: fs => by
    simp only [SpineFit]
    have h0 : interp V σ F = interp V ρ G := h 0 [] (by simp) rfl (by simp [SpineFit])
    rw [h0]
    refine and_congr_right fun hx => spineFit_congr_fit (σ := cons x σ) (ρ := cons x ρ)
      (by simpa using hl) (fun i as hi has hfit => ?_) fs
    have := h (i + 1) (x :: as) (by simp; omega) (by simp [has])
      (by simp only [List.take_succ_cons, SpineFit]; exact ⟨hx, hfit⟩)
    simpa using this
  | [], _ :: _, hl, _, _ => by simp at hl
  | _ :: _, [], hl, _, _ => by simp at hl

/-- Along a prefix fitting the first list, the next fields read alike. -/
theorem FieldsEqOn.getD_eq :
    ∀ {Δ As Bs : List AnnotTerm}, FieldsEqOn V Δ As Bs → ∀ {ρ : Nat → V}, Sat V Δ ρ →
      ∀ (l : Nat) (as : List V), l < As.length → SpineFit ρ (As.take l) as →
        interp V (consList as ρ) (As.getD l default) = interp V (consList as ρ) (Bs.getD l default)
  | _, A :: _, B :: _, h, ρ, hρ, 0, as, _, hfit => by
    cases as with
    | nil => exact h.1 ρ hρ
    | cons _ _ => simp [SpineFit] at hfit
  | _, A :: As, B :: Bs, h, ρ, hρ, l + 1, as, hl, hfit => by
    cases as with
    | nil => simp [SpineFit] at hfit
    | cons a as =>
      simp only [List.take_succ_cons, SpineFit] at hfit
      simp only [consList_cons, List.getD_cons_succ]
      exact FieldsEqOn.getD_eq h.2 (Sat_cons V hρ hfit.1) l as (by simpa using hl) hfit.2
  | _, [], _, _, _, _, _, _, hl, _ => by simp at hl
  | _, _ :: _, [], h, _, _, _, _, _, _ => h.elim

/-- Two Π-towers over field lists that read alike, with the same binder
data and the same body, read alike. -/
theorem interp_mkPisAV_congr :
    ∀ {Δ : List AnnotTerm} (abD abN : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      abD.map (fun x => (x.1, x.2.1)) = abN.map (fun x => (x.1, x.2.1)) →
      FieldsEqOn V Δ (abD.map (·.2.2)) (abN.map (·.2.2)) →
      ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ (mkPisAV abD B) = interp V ρ (mkPisAV abN B)
  | _, [], [], _, _, _, _, _ => rfl
  | Δ, d :: abD, e :: abN, B, hb, h, ρ, hρ => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hb
    obtain ⟨⟨h1, h2⟩, hb⟩ := hb
    simp only [mkPisAV, interp_pi, h2]
    rw [h.1 ρ hρ]
    refine piR_congr fun x hx => ?_
    have hx' : x ∈ˢ interp V ρ d.2.2 := (h.1 ρ hρ).symm ▸ hx
    exact interp_mkPisAV_congr abD abN B hb h.2 _ (Sat_cons V hρ hx')
  | _, [], _ :: _, _, hb, _, _, _ => by simp at hb
  | _, _ :: _, [], _, hb, _, _, _ => by simp at hb

/-- The relation under a binder depends only on the binder's reading at
the relation's frames. -/
theorem under_eq_of_eqOn {Δ : List AnnotTerm} {A B : AnnotTerm} {R : FrameRel V}
    (h : ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ A = interp V ρ B)
    (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δ ρ ∧ Sat V Δ ρ') : R.under A = R.under B := by
  funext σ σ'
  apply propext
  constructor
  · rintro ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
    exact ⟨x, ρ, ρ', rfl, rfl, hR, by rwa [← h ρ (hdom ρ ρ' hR).1]⟩
  · rintro ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
    exact ⟨x, ρ, ρ', rfl, rfl, hR, by rwa [h ρ (hdom ρ ρ' hR).1]⟩

/-- Field-wise positivity moves along field lists that read alike, and
so does the relation under all the fields. -/
theorem FieldsEqOn.teleMonoOn :
    ∀ {Δ As Bs : List AnnotTerm} {R : FrameRel V}, FieldsEqOn V Δ As Bs →
      (∀ ρ ρ', R ρ ρ' → Sat V Δ ρ ∧ Sat V Δ ρ') → TeleMonoOn R As →
      TeleMonoOn R Bs ∧ R.underTele As = R.underTele Bs
  | _, [], [], _, _, _, _ => ⟨trivial, rfl⟩
  | Δ, A :: As, B :: Bs, R, h, hdom, hm => by
    obtain ⟨hA, hAs⟩ := hm
    have hdom' : ∀ σ σ', R.under A σ σ' → Sat V (A :: Δ) σ ∧ Sat V (A :: Δ) σ' := by
      rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx⟩
      exact ⟨Sat_cons V (hdom ρ ρ' hR).1 hx, Sat_cons V (hdom ρ ρ' hR).2 (hA ρ ρ' hR x hx)⟩
    obtain ⟨hBs, hU⟩ := FieldsEqOn.teleMonoOn h.2 hdom' hAs
    have hUE := under_eq_of_eqOn h.1 hdom
    refine ⟨⟨MonoOn.of_eqOn (Q := Sat V Δ) hdom (fun ρ hρ => (h.1 ρ hρ).symm) hA, ?_⟩, ?_⟩
    · rw [← hUE]; exact hBs
    · show (R.under A).underTele As = (R.under B).underTele Bs
      rw [hU, hUE]
  | _, [], _ :: _, _, h, _, _ => h.elim
  | _, _ :: _, [], _, h, _, _ => h.elim


end ConLeche.Semantics
