module

public import ConLeche.Semantics.Tower.TowerLeaf

@[expose] public section

/-!
# Π-towers that read alike at every fitting prefix (task #315 U-18, lane D)

`mkPisAV` folds `(domain sort, codomain sort, domain)` data into a
Π-tower.  Two such towers over the SAME body have the same
interpretation as soon as their data agree *where the interpretation
can see them*:

* the **codomain bits** (`d.2.1` — `interp_pi` reads the domain bit
  `d.1` nowhere, so it is unconstrained), pointwise; and
* the **domains**, but only at the environments a fit of the earlier
  domains produces: `interp_mkPisAV_congr_fit`'s third premise is
  quantified over the prefix length `l` and a value spine `as` fitting
  BOTH prefixes, so a caller never has to know what the two towers do
  at a frame no value reaches.

That prefix quantification is the whole point: the two data lists in
the consumers differ by a per-field rewriting whose agreement is
itself only available under the earlier fields' membership.  A
congruence over raw syntactic equality of the domains would not apply;
this one does, because `piR`'s congruence (`piR_congr`) hands back
exactly the membership hypothesis the premise asks for.

`interp_mkPisAV_congr_fit'` is the same statement with the second
tower's fit dropped from the premise — the shape a caller with a
single-sided fit already has.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory

universe uv

variable {V : Type uv} [SetTheory V]

/-- **The Π-tower congruence at fitting prefixes**: two towers over
the same body, of the same length, with pointwise equal codomain bits
and domains that read alike at every frame a fitting value spine
produces, have the same interpretation. -/
theorem interp_mkPisAV_congr_fit {R : AnnotTerm} :
    ∀ {ds₁ ds₂ : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      ds₁.length = ds₂.length →
      (∀ i, i < ds₁.length → (ds₁.getD i default).2.1 = (ds₂.getD i default).2.1) →
      (∀ l, l < ds₁.length → ∀ as : List V, as.length = l →
        SpineFit σ ((ds₁.take l).map (·.2.2)) as → SpineFit σ ((ds₂.take l).map (·.2.2)) as →
        interp V (consList as σ) (ds₁.getD l default).2.2
          = interp V (consList as σ) (ds₂.getD l default).2.2) →
      interp V σ (mkPisAV ds₁ R) = interp V σ (mkPisAV ds₂ R) := by
  intro ds₁
  induction ds₁ with
  | nil =>
    intro ds₂ σ hlen _ _
    cases ds₂ with
    | nil => rfl
    | cons _ _ => exact nomatch hlen
  | cons d₁ ds₁ ih =>
    intro ds₂ σ hlen hbits hpref
    cases ds₂ with
    | nil => exact nomatch hlen
    | cons d₂ ds₂ =>
      have hnil₁ : SpineFit σ ((((d₁ :: ds₁).take 0).map (·.2.2))) ([] : List V) := by
        simp only [List.take_zero, List.map_nil]
        trivial
      have hnil₂ : SpineFit σ ((((d₂ :: ds₂).take 0).map (·.2.2))) ([] : List V) := by
        simp only [List.take_zero, List.map_nil]
        trivial
      have hdom : interp V σ d₁.2.2 = interp V σ d₂.2.2 := by
        have h := hpref 0 (by simp) [] rfl hnil₁ hnil₂
        simpa using h
      have hv : d₁.2.1 = d₂.2.1 := by
        have h := hbits 0 (by simp)
        simpa using h
      simp only [mkPisAV, interp_pi]
      rw [← hv, ← hdom]
      refine piR_congr ?_
      intro x hx
      have hx₂ : x ∈ˢ interp V σ d₂.2.2 := hdom ▸ hx
      refine ih (σ := cons x σ) (by simpa using hlen) (fun i hi => ?_) (fun l hl as hlas h₁ h₂ => ?_)
      · have h := hbits (i + 1) (by simpa using Nat.succ_lt_succ hi)
        simpa using h
      · have hstep₁ : SpineFit σ ((((d₁ :: ds₁).take (l + 1)).map (·.2.2))) (x :: as) := by
          simp only [List.take_succ_cons, List.map_cons]
          exact ⟨hx, h₁⟩
        have hstep₂ : SpineFit σ ((((d₂ :: ds₂).take (l + 1)).map (·.2.2))) (x :: as) := by
          simp only [List.take_succ_cons, List.map_cons]
          exact ⟨hx₂, h₂⟩
        have h := hpref (l + 1) (by simpa using Nat.succ_lt_succ hl) (x :: as)
          (by simp [hlas]) hstep₁ hstep₂
        simpa using h

/-- The one-sided form: the caller carries a fit of the FIRST tower's
prefix only.  The premise is stronger, so the congruence follows. -/
theorem interp_mkPisAV_congr_fit' {R : AnnotTerm}
    {ds₁ ds₂ : List (Nat × Nat × AnnotTerm)} {σ : Nat → V}
    (hlen : ds₁.length = ds₂.length)
    (hbits : ∀ i, i < ds₁.length → (ds₁.getD i default).2.1 = (ds₂.getD i default).2.1)
    (hpref : ∀ l (fs₁ : List V), fs₁.length = l → l < ds₁.length →
      SpineFit σ ((ds₁.take l).map (·.2.2)) fs₁ →
      interp V (consList fs₁ σ) (ds₁.getD l default).2.2
        = interp V (consList fs₁ σ) (ds₂.getD l default).2.2) :
    interp V σ (mkPisAV ds₁ R) = interp V σ (mkPisAV ds₂ R) :=
  interp_mkPisAV_congr_fit hlen hbits
    (fun l hl as hlas h₁ _ => hpref l as hlas hl h₁)

end ConLeche.Semantics
