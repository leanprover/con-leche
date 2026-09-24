module

public import ConLeche.Semantics.Inductives.HoleApp

@[expose] public section

/-!
# Grading across frames related at the holes (lane HOLE2)

`interp_congr_holeApp` (`HoleApp.lean`, lane CONTSEM) reads a term whose
holes occur only applied to the parameters the same at two frames whose
hole values agree APPLIED TO THE PARAMETERS.  This module is the grading
twin: `WellDenoted` crosses the same relation, once the two frames' hole
values also accept the same arguments at every PARTIAL application to a
prefix of the parameters (`HoleAgreeW`) — beyond the parameters the
values agree, so they accept the same arguments anyway.

The block operator's hole chains (`Semantics/Tower/BlockHoleChain.lean`)
substitute each hole by a term that is graded at every family tuple and
agrees with the model's hole value applied to the parameters; this
lemma is how the chains inherit the fields' grading at the model's hole
frame.
-/

namespace ConLeche.Semantics

open SetTheory ConLeche.SetModel

universe uv

variable {V : Type uv} [SetTheory V]

/-- **`f` applies to `a`** in the grading's sense: `WellDenoted`'s
application clause at the values. -/
def AppOk (f a : V) : Prop :=
  ∃ (v : Nat) (A : V) (B : V → V), f ∈ˢ piR v A B ∧ a ∈ˢ A ∧
    (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V))

/-- **A spine of arguments applies**, argument by argument. -/
def SpineOk (g : V) : List V → Prop
  | [] => True
  | a :: as => AppOk g a ∧ SpineOk (app g a) as

theorem wellDenoted_mkAppN_iff (ρ : Nat → V) :
    ∀ (f : AnnotTerm) (args : List AnnotTerm),
      WellDenoted V ρ (AnnotTerm.mkAppN f args) ↔
        WellDenoted V ρ f ∧ (∀ a ∈ args, WellDenoted V ρ a) ∧
          SpineOk (interp V ρ f) (args.map (interp V ρ))
  | f, [] => by simp [AnnotTerm.mkAppN, SpineOk]
  | f, a :: args => by
    rw [AnnotTerm.mkAppN_cons, wellDenoted_mkAppN_iff ρ (.app f a) args, WellDenoted_app,
      interp_app]
    simp only [List.mem_cons, forall_eq_or_imp, List.map_cons, SpineOk, AppOk]
    constructor
    · rintro ⟨⟨hf, ha, hap⟩, hargs, hsp⟩; exact ⟨hf, ⟨ha, hargs⟩, hap, hsp⟩
    · rintro ⟨hf, ⟨ha, hargs⟩, hap, hsp⟩; exact ⟨⟨hf, ha, hap⟩, hargs, hsp⟩

theorem spineOk_iff (g : V) :
    ∀ ws : List V, SpineOk g ws ↔
      ∀ i (hi : i < ws.length), AppOk ((ws.take i).foldl app g) ws[i]
  | [] => by simp [SpineOk]
  | a :: ws => by
    rw [SpineOk, spineOk_iff (app g a) ws]
    constructor
    · rintro ⟨h0, hs⟩ i hi
      cases i with
      | zero => simpa using h0
      | succ i => simpa using hs i (by simpa using hi)
    · intro h
      refine ⟨?_, fun i hi => ?_⟩
      · have := h 0 (by simp)
        simpa using this
      · have := h (i + 1) (by simpa using hi)
        rw [List.getElem_cons_succ] at this
        simpa using this

/-- **Frames related at the holes, for grading**: `HoleAgree`, and at
every PARTIAL application of a hole to a prefix of the parameters the
second frame's hole accepts every argument the first's does. -/
def HoleAgreeW (k nP lo : Nat) (σ σ' : Nat → V) : Prop :=
  HoleAgree k nP lo σ σ' ∧
  ∀ h, lo ≤ h → h < lo + k → ∀ j, j < nP → ∀ a,
    AppOk (((holeParamVals k nP lo σ).take j).foldl app (σ h)) a →
      AppOk (((holeParamVals k nP lo σ).take j).foldl app (σ' h)) a

theorem HoleAgreeW.cons {k nP lo : Nat} {σ σ' : Nat → V} (h : HoleAgreeW k nP lo σ σ') (x : V) :
    HoleAgreeW k nP (lo + 1) (cons x σ) (cons x σ') := by
  refine ⟨h.1.cons x, fun hh h1 h2 j hj a => ?_⟩
  obtain ⟨hh, rfl⟩ : ∃ h', hh = h' + 1 := ⟨hh - 1, by omega⟩
  rw [holeParamVals_cons]
  exact h.2 hh (by omega) (by omega) j hj a

theorem HoleAgreeW.consList {k nP lo : Nat} :
    ∀ (fs : List V) {σ σ' : Nat → V}, HoleAgreeW k nP lo σ σ' →
      HoleAgreeW k nP (lo + fs.length) (consList fs σ) (consList fs σ')
  | [], _, _, h => h
  | a :: fs, _, _, h => by
    have := HoleAgreeW.consList (lo := lo + 1) fs (h.cons a)
    rwa [show lo + 1 + fs.length = lo + (a :: fs).length by simp; omega] at this

omit [SetTheory V] in
theorem holeParamVals_length (k nP lo : Nat) (σ : Nat → V) :
    (holeParamVals k nP lo σ).length = nP := by simp [holeParamVals]

/-- **A hole's spine applies at the second frame** when it does at the
first. -/
theorem spineOk_hole {k nP lo : Nat} {σ σ' : Nat → V} (h : HoleAgreeW k nP lo σ σ')
    {hh : Nat} (h1 : lo ≤ hh) (h2 : hh < lo + k) (is : List V)
    (hs : SpineOk (σ hh) (holeParamVals k nP lo σ ++ is)) :
    SpineOk (σ' hh) (holeParamVals k nP lo σ ++ is) := by
  rw [spineOk_iff] at hs ⊢
  intro i hi
  have hlen := holeParamVals_length k nP lo σ
  by_cases hin : i < nP
  · have htake : (holeParamVals k nP lo σ ++ is).take i = (holeParamVals k nP lo σ).take i := by
      rw [List.take_append_of_le_length (by omega)]
    have := hs i hi
    rw [htake] at this ⊢
    exact h.2 hh h1 h2 i hin _ this
  · have htake : (holeParamVals k nP lo σ ++ is).take i
        = holeParamVals k nP lo σ ++ is.take (i - nP) := by
      rw [List.take_append, List.take_of_length_le (by omega), hlen]
    have := hs i hi
    rw [htake] at this ⊢
    rw [← h.1.2 hh h1 h2 (is.take (i - nP))]
    exact this

/-- **The grading crosses frames related at the holes** (see the module
docstring). -/
theorem wellDenoted_congr_holeApp {k nP : Nat} :
    ∀ {lo : Nat} {e : AnnotTerm}, HoleApp k nP lo e →
      ∀ {σ σ' : Nat → V}, HoleAgreeW k nP lo σ σ' → WellDenoted V σ e → WellDenoted V σ' e := by
  intro lo e he
  induction he with
  | bvar => intros; simp
  | sort => intros; simp
  | const => intros; simp
  | prf => intros; simp
  | app hf ha ihf iha =>
    intro σ σ' h hw
    rw [WellDenoted_app] at hw ⊢
    obtain ⟨hwf, hwa, v, A, B, h1, h2, h3⟩ := hw
    refine ⟨ihf h hwf, iha h hwa, v, A, B, ?_, ?_, h3⟩
    · rwa [← interp_congr_holeApp hf h.1]
    · rwa [← interp_congr_holeApp ha h.1]
  | lam hA hb ihA ihb =>
    intro σ σ' h hw
    rw [WellDenoted_lam] at hw ⊢
    obtain ⟨hwA, hwb, B, hB, hB0⟩ := hw
    have hAe := interp_congr_holeApp hA h.1
    refine ⟨ihA h hwA, fun x hx => ihb (h.cons x) (hwb x (by rwa [hAe])), B,
      fun x hx => ?_, fun hv x hx => hB0 hv x (by rwa [hAe])⟩
    rw [← interp_congr_holeApp hb (h.1.cons x)]
    exact hB x (by rwa [hAe])
  | pi hA hB ihA ihB =>
    intro σ σ' h hw
    rw [WellDenoted_pi] at hw ⊢
    obtain ⟨hwA, hwB⟩ := hw
    have hAe := interp_congr_holeApp hA h.1
    exact ⟨ihA h hwA, fun x hx => ihB (h.cons x) (hwB x (by rwa [hAe]))⟩
  | eqE ha hb iha ihb =>
    intro σ σ' h hw
    rw [WellDenoted_eqE] at hw ⊢
    exact ⟨iha h hw.1, ihb h hw.2⟩
  | fst he ih =>
    intro σ σ' h hw
    rw [WellDenoted_fst] at hw ⊢
    obtain ⟨hwe, u, v, A, Bf, h1, h2, h3⟩ := hw
    exact ⟨ih h hwe, u, v, A, Bf, by rwa [← interp_congr_holeApp he h.1], h2, h3⟩
  | snd he ih =>
    intro σ σ' h hw
    rw [WellDenoted_snd] at hw ⊢
    obtain ⟨hwe, u, v, A, Bf, h1, h2, h3⟩ := hw
    exact ⟨ih h hwe, u, v, A, Bf, by rwa [← interp_congr_holeApp he h.1], h2, h3⟩
  | @hole lo hh rest h1 h2 hrest ih =>
    intro σ σ' h hw
    rw [wellDenoted_mkAppN_iff] at hw ⊢
    obtain ⟨-, hargs, hsp⟩ := hw
    refine ⟨by simp, fun a ha => ?_, ?_⟩
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨p, -, rfl⟩ := List.mem_map.mp ha; simp
      · exact ih a ha h (hargs a (List.mem_append_right _ ha))
    · have hrestE : rest.map (interp V σ') = rest.map (interp V σ) :=
        List.map_congr_left fun r hr => (interp_congr_holeApp (hrest r hr) h.1).symm
      rw [List.map_append, map_interp_holeParams, hrestE, interp_bvar,
        ← holeParamVals_congr h.1]
      rw [List.map_append, map_interp_holeParams, interp_bvar] at hsp
      exact spineOk_hole h h1 h2 _ hsp

end ConLeche.Semantics
