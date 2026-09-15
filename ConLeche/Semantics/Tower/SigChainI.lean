module

public import ConLeche.Semantics.Tower.TowerMk
public import ConLeche.Semantics.Kit
@[expose] public section

/-!
# The ι-specified chosen tuple: the Σ'-chain kit (task #315, M3)

The uniform route's recursors are ONE chosen tuple pinned by its ι
equations (DESIGN §U.4): a Σ'-chain of the `k` recursor types followed
by the conjunction of the rules' equations, chosen by `choice`, the
members' leaves its projections.  This file is that kit, generic in
the component types and the proposition:

    sigChainAV s [T₀, …, T_{k-1}] Q  =  Σ' (r₀ : T₀) … (r_{k-1} : T_{k-1}), Q
    selChainAV s Ts Q                 =  choice (sigChainAV s Ts Q) prf
    projChainAV i e                   =  fst (snd^i e)

`Ts[i]` sits under `i` binders (the earlier components); the recursor
types are lifted there (`blockTsAV`).  The semantic chain `sigChainV`
is the nested `sigmaSet`; `ChainOk` is its formation premise (each
component's reading in `univ s` and graded at every earlier fit, the
proposition a truth value, graded).  **The kit's theorem**
(`sigChain_choice`): under `ChainOk`, if the chain is inhabited then
the chosen element's projections are a fitting spine whose components
satisfy `Q`, each graded.  `blockRecAVI_facts` is the block shape:
`k` closed types, the equations a conjunction (`andChainAV`), a
candidate tuple in hand.

Everything the falsifier `BlockRecPair.lean` proved by hand at `k = 2`,
`n = 3`, once for all `k` and `n`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## `Nat.max` at the pinned pair's levels -/

omit [SetTheory V] in
theorem natMax_self (n : Nat) : Nat.max n n = n := Nat.max_self n

omit [SetTheory V] in
theorem natMax_zero (n : Nat) : Nat.max n 0 = n := Nat.max_zero n

/-! ## `PSigma'`, `choice` -/

/-- `PSigma'.{u,v}` is a graph. -/
theorem psigmaV_mem (u v : Nat) :
    psigmaV V u v ∈ˢ piR (Nat.max u v + 1) (univ u : V)
      (fun A => piR (Nat.max u v + 1) (psigmaFibreSpace V v A) fun _ => (univ (Nat.max u v) : V)) :=
  lamR_mem fun _ hA => lamR_mem fun _ hB =>
    sigma_mem_univ hA (fun _ hx => psigmaFibre_apply V hB hx)

/-- `PSigma'.{s,s}` is a graph, at the chain's levels. -/
theorem psigmaV_ss_mem (s : Nat) :
    psigmaV V s s ∈ˢ piR (s + 1) (univ s : V)
      (fun A => piR (s + 1) (psigmaFibreSpace V s A) fun _ => (univ s : V)) := by
  have := psigmaV_mem (V := V) s s
  rwa [natMax_self] at this

/-- `pt` witnesses the double negation of an inhabited set. -/
theorem pt_mem_dnegSpace_of {A x : V} (hx : x ∈ˢ A) : (pt : V) ∈ˢ dnegSpace V A := by
  unfold dnegSpace
  have h1 : piR 0 A (fun _ => (empty : V)) = empty := by
    rw [piR_zero]
    exact truthVal_eq_empty fun hf => not_mem_empty _ (hf x hx).choose_spec
  rw [h1, piR_zero_empty]
  exact pt_mem_unitSet

/-- `Classical.choice.{s}` is a graph. -/
theorem choiceV_mem (s : Nat) :
    choiceV V s ∈ˢ piR s (univ s : V) (fun A => piR s (dnegSpace V A) fun _ => A) :=
  lamR_mem fun _ _ => lamR_mem fun _ hh => schoice_mem (exists_mem_of_dneg V hh).choose_spec

/-- Elimination at a `Prop`-valued product. -/
theorem piR_zero_elim {A f x : V} {B : V → V} (hf : f ∈ˢ piR 0 A B) (hx : x ∈ˢ A) :
    ∃ y, y ∈ˢ B x := by
  rw [piR_zero] at hf
  exact of_mem_truthVal hf x hx

/-! ## Conjunction of propositions -/

/-- `Σ' (_ : P), Q` at `Prop` (`Q` at the same depth as `P`). -/
def andAV (P Q : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .psigma [0, 0]) [P, .lam 1 P (Q.liftN 1 0)]

/-- The conjunction of a list of propositions (`PUnit` at `[]`). -/
def andChainAV : List AnnotTerm → AnnotTerm
  | [] => .const .punit [0]
  | e :: es => andAV e (andChainAV es)

theorem interp_andAV {P Q : AnnotTerm} {ρ : Nat → V}
    (hP : interp V ρ P ∈ˢ (univZero : V)) (hQ : interp V ρ Q ∈ˢ (univZero : V)) :
    interp V ρ (andAV P Q) = sigmaSet 0 (interp V ρ P) fun _ => interp V ρ Q := by
  have hP' : interp V ρ P ∈ˢ (univ 0 : V) := by rw [univ_zero]; exact hP
  have hlam : interp V ρ (.lam 1 P (Q.liftN 1 0)) = lamR 1 (interp V ρ P) fun _ => interp V ρ Q := by
    rw [interp_lam]
    exact lamR_congr fun x _ => by rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]
  have hfib : (lamR 1 (interp V ρ P) fun _ => interp V ρ Q) ∈ˢ psigmaFibreSpace V 0 (interp V ρ P) :=
    lamR_mem fun _ _ => by rw [univ_zero]; exact hQ
  show SetTheory.app (SetTheory.app (psigmaV V 0 0) (interp V ρ P))
    (interp V ρ (.lam 1 P (Q.liftN 1 0))) = _
  rw [hlam, psigmaV_app V hP' hfib]
  exact sigma_congr fun x hx => app_lamR_pos Nat.one_ne_zero hx

theorem andAV_univZero {P Q : AnnotTerm} {ρ : Nat → V}
    (hP : interp V ρ P ∈ˢ (univZero : V)) (hQ : interp V ρ Q ∈ˢ (univZero : V)) :
    interp V ρ (andAV P Q) ∈ˢ (univZero : V) := by
  rw [interp_andAV hP hQ, sigmaSet_zero]
  exact truthVal_mem_univZero _

theorem pt_mem_andAV_iff {P Q : AnnotTerm} {ρ : Nat → V}
    (hP : interp V ρ P ∈ˢ (univZero : V)) (hQ : interp V ρ Q ∈ˢ (univZero : V)) :
    (pt : V) ∈ˢ interp V ρ (andAV P Q) ↔
      (pt : V) ∈ˢ interp V ρ P ∧ (pt : V) ∈ˢ interp V ρ Q := by
  rw [interp_andAV hP hQ]
  constructor
  · intro hz
    obtain ⟨a, b, ha, hb, -, -⟩ := mem_sigma_elim hz
    exact ⟨eq_pt_of_mem_univZero hP ha ▸ ha, eq_pt_of_mem_univZero hQ hb ▸ hb⟩
  · rintro ⟨hp, hq⟩
    exact pt_mem_sigma hp hq

/-- The `Prop`-level pair is graded. -/
theorem wd_andAV {P Q : AnnotTerm} {ρ : Nat → V} (hP : WellDenoted V ρ P) (hQ : WellDenoted V ρ Q)
    (hPu : interp V ρ P ∈ˢ (univZero : V)) (hQu : interp V ρ Q ∈ˢ (univZero : V)) :
    WellDenoted V ρ (andAV P Q) := by
  have hP' : interp V ρ P ∈ˢ (univ 0 : V) := by rw [univ_zero]; exact hPu
  have hQ' : interp V ρ Q ∈ˢ (univ 0 : V) := by rw [univ_zero]; exact hQu
  have hps := psigmaV_ss_mem (V := V) 0
  have hlam : interp V ρ (.lam 1 P (Q.liftN 1 0)) = lamR 1 (interp V ρ P) fun _ => interp V ρ Q := by
    rw [interp_lam]
    exact lamR_congr fun x _ => by rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]
  show WellDenoted V ρ (.app (.app (.const .psigma [0, 0]) P) (.lam 1 P (Q.liftN 1 0)))
  rw [WellDenoted_app]
  refine ⟨?_, ?_, 1, psigmaFibreSpace V 0 (interp V ρ P), fun _ => (univ 0 : V), ?_, ?_,
    fun h0 => absurd h0 Nat.one_ne_zero⟩
  · rw [WellDenoted_app]
    exact ⟨trivial, hP, 1, univ 0, fun A => piR 1 (psigmaFibreSpace V 0 A) fun _ => (univ 0 : V),
      hps, hP', fun h0 => absurd h0 Nat.one_ne_zero⟩
  · rw [WellDenoted_lam]
    refine ⟨hP, fun x _ => ?_, fun _ => (univ 0 : V), fun x _ => ?_,
      fun h0 => absurd h0 Nat.one_ne_zero⟩
    · rw [WellDenoted_liftN, shiftE_succ_cons, shiftE_zero_zero]; exact hQ
    · rw [interp_liftN, shiftE_succ_cons, shiftE_zero_zero]; exact hQ'
  · show SetTheory.app (psigmaV V 0 0) (interp V ρ P) ∈ˢ _
    exact app_mem_piR_pos Nat.one_ne_zero hps hP'
  · rw [hlam]
    exact lamR_mem fun _ _ => hQ'

/-- The conjunction's formation and grading, from its conjuncts'. -/
theorem andChainAV_facts {ρ : Nat → V} :
    ∀ {es : List AnnotTerm},
      (∀ e ∈ es, interp V ρ e ∈ˢ (univZero : V) ∧ WellDenoted V ρ e) →
      interp V ρ (andChainAV es) ∈ˢ (univZero : V) ∧ WellDenoted V ρ (andChainAV es)
  | [], _ => ⟨by show (unitSet : V) ∈ˢ _; rw [← univ_zero]; exact unitSet_mem_univ 0, trivial⟩
  | e :: es, h => by
    have ih := andChainAV_facts (es := es) fun e' he' => h e' (.tail _ he')
    have he := h e (.head _)
    exact ⟨andAV_univZero he.1 ih.1, wd_andAV he.2 ih.2 he.1 ih.1⟩

/-- `pt` inhabits the conjunction iff it inhabits every conjunct. -/
theorem pt_mem_andChainAV_iff {ρ : Nat → V} :
    ∀ {es : List AnnotTerm},
      (∀ e ∈ es, interp V ρ e ∈ˢ (univZero : V) ∧ WellDenoted V ρ e) →
      ((pt : V) ∈ˢ interp V ρ (andChainAV es) ↔ ∀ e ∈ es, (pt : V) ∈ˢ interp V ρ e)
  | [], _ => by
    show (pt : V) ∈ˢ unitSet ↔ _
    exact ⟨fun _ e he => (nomatch he), fun _ => pt_mem_unitSet⟩
  | e :: es, h => by
    have ih := pt_mem_andChainAV_iff (es := es) fun e' he' => h e' (.tail _ he')
    have hall := andChainAV_facts (es := es) fun e' he' => h e' (.tail _ he')
    show (pt : V) ∈ˢ interp V ρ (andAV e (andChainAV es)) ↔ _
    rw [pt_mem_andAV_iff (h e (.head _)).1 hall.1, ih]
    constructor
    · rintro ⟨h1, h2⟩ e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact h1
      · exact h2 e' he'
    · intro h'
      exact ⟨h' e (.head _), fun e' he' => h' e' (.tail _ he')⟩

/-! ## The Σ'-chain -/

/-- `Σ' (r : T), rest` at sort `s` (the rest at sort `s` too). -/
def sigAV (s : Nat) (T rest : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .psigma [s, s]) [T, .lam (s + 1) T rest]

/-- **The chain** `Σ' (r₀ : T₀) … (r_{k-1} : T_{k-1}), Q`; `Ts[i]` sits
under the `i` earlier binders. -/
def sigChainAV (s : Nat) : List AnnotTerm → AnnotTerm → AnnotTerm
  | [], Q => Q
  | T :: Ts, Q => sigAV s T (sigChainAV s Ts Q)

/-- The `i`-th component of a chain element: `fst (snd^i e)`. -/
def projChainAV : Nat → AnnotTerm → AnnotTerm
  | 0, e => .fst e
  | i + 1, e => projChainAV i (.snd e)

/-- **The chosen chain element** `choice (sigChainAV s Ts Q) prf`. -/
def selChainAV (s : Nat) (Ts : List AnnotTerm) (Q : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .choice [s]) [sigChainAV s Ts Q, .prf]

/-- The semantic chain: the nested pair set. -/
noncomputable def sigChainV (s : Nat) : (Nat → V) → List AnnotTerm → AnnotTerm → V
  | ρ, [], Q => interp V ρ Q
  | ρ, T :: Ts, Q => sigmaSet s (interp V ρ T) fun r => sigChainV s (cons r ρ) Ts Q

/-- The iterated second projection. -/
noncomputable def ssndN : Nat → V → V
  | 0, x => x
  | i + 1, x => ssndN i (ssnd x)

/-- **The chain's formation premise**: each component's reading is in
`univ s` and graded at every fit of the earlier ones; the proposition
is a truth value and graded at every full fit. -/
def ChainOk (s : Nat) : (Nat → V) → List AnnotTerm → AnnotTerm → Prop
  | ρ, [], Q => interp V ρ Q ∈ˢ (univZero : V) ∧ WellDenoted V ρ Q
  | ρ, T :: Ts, Q => interp V ρ T ∈ˢ (univ s : V) ∧ WellDenoted V ρ T ∧
      ∀ r, r ∈ˢ interp V ρ T → ChainOk s (cons r ρ) Ts Q

theorem interp_projChainAV (ρ : Nat → V) :
    ∀ (i : Nat) (e : AnnotTerm), interp V ρ (projChainAV i e) = sfst (ssndN i (interp V ρ e))
  | 0, _ => rfl
  | i + 1, e => by
    show interp V ρ (projChainAV i (.snd e)) = _
    rw [interp_projChainAV ρ i (.snd e)]
    rfl

section Chain

variable {s : Nat}

/-- The chain lives in `univ s`. -/
theorem sigChainV_univ :
    ∀ {ρ : Nat → V} {Ts : List AnnotTerm} {Q : AnnotTerm}, ChainOk s ρ Ts Q →
      sigChainV s ρ Ts Q ∈ˢ (univ s : V)
  | _, [], _, h => by
    show interp V _ _ ∈ˢ _
    exact univ_mono (Nat.zero_le s) _ (by rw [univ_zero]; exact h.1)
  | ρ, T :: Ts, Q, h => by
    show sigmaSet s _ _ ∈ˢ _
    have := sigma_mem_univ h.1 (fun r hr => sigChainV_univ (h.2.2 r hr))
    rwa [natMax_self] at this

/-- The chain's fibre λ. -/
theorem sigChain_lam_mem {ρ : Nat → V} {T : AnnotTerm} {Ts : List AnnotTerm} {Q : AnnotTerm}
    (h : ChainOk s ρ (T :: Ts) Q) :
    (lamR (s + 1) (interp V ρ T) fun r => sigChainV s (cons r ρ) Ts Q)
      ∈ˢ psigmaFibreSpace V s (interp V ρ T) :=
  lamR_mem fun r hr => sigChainV_univ (h.2.2 r hr)

/-- **The chain reads as the nested pair set.** -/
theorem interp_sigChainAV :
    ∀ {ρ : Nat → V} {Ts : List AnnotTerm} {Q : AnnotTerm}, ChainOk s ρ Ts Q →
      interp V ρ (sigChainAV s Ts Q) = sigChainV s ρ Ts Q
  | _, [], _, _ => rfl
  | ρ, T :: Ts, Q, h => by
    have hlam : interp V ρ (.lam (s + 1) T (sigChainAV s Ts Q))
        = lamR (s + 1) (interp V ρ T) fun r => sigChainV s (cons r ρ) Ts Q := by
      rw [interp_lam]
      exact lamR_congr fun r hr => interp_sigChainAV (h.2.2 r hr)
    show SetTheory.app (SetTheory.app (psigmaV V s s) (interp V ρ T))
      (interp V ρ (.lam (s + 1) T (sigChainAV s Ts Q))) = _
    rw [hlam, psigmaV_app V h.1 (sigChain_lam_mem h), natMax_self]
    exact sigma_congr fun r hr => app_lamR_pos (Nat.succ_ne_zero s) hr

/-- **The chain is graded.** -/
theorem wd_sigChainAV :
    ∀ {ρ : Nat → V} {Ts : List AnnotTerm} {Q : AnnotTerm}, ChainOk s ρ Ts Q →
      WellDenoted V ρ (sigChainAV s Ts Q)
  | _, [], _, h => h.2
  | ρ, T :: Ts, Q, h => by
    have hps := psigmaV_ss_mem (V := V) s
    show WellDenoted V ρ (.app (.app (.const .psigma [s, s]) T) (.lam (s + 1) T (sigChainAV s Ts Q)))
    rw [WellDenoted_app]
    refine ⟨?_, ?_, s + 1, psigmaFibreSpace V s (interp V ρ T), fun _ => (univ s : V), ?_, ?_,
      fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
    · rw [WellDenoted_app]
      exact ⟨trivial, h.2.1, s + 1, univ s,
        fun A => piR (s + 1) (psigmaFibreSpace V s A) fun _ => (univ s : V), hps, h.1,
        fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
    · rw [WellDenoted_lam]
      refine ⟨h.2.1, fun r hr => wd_sigChainAV (h.2.2 r hr), fun _ => (univ s : V), fun r hr => ?_,
        fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
      rw [interp_sigChainAV (h.2.2 r hr)]
      exact sigChainV_univ (h.2.2 r hr)
    · show SetTheory.app (psigmaV V s s) (interp V ρ T) ∈ˢ _
      exact app_mem_piR_pos (Nat.succ_ne_zero _) hps h.1
    · rw [interp_lam]
      exact lamR_mem fun r hr => by
        rw [interp_sigChainAV (h.2.2 r hr)]
        exact sigChainV_univ (h.2.2 r hr)

/-- A fitting spine satisfying `Q` inhabits the chain. -/
theorem sigChainV_inhabited :
    ∀ {ρ : Nat → V} {Ts : List AnnotTerm} {Q : AnnotTerm} {rs : List V}, ChainOk s ρ Ts Q →
      SpineFit ρ Ts rs → (pt : V) ∈ˢ interp V (consList rs ρ) Q →
      ∃ x, x ∈ˢ sigChainV s ρ Ts Q
  | _, [], _, [], _, _, hq => ⟨pt, hq⟩
  | _, [], _, _ :: _, _, hsp, _ => hsp.elim
  | _, _ :: _, _, [], _, hsp, _ => hsp.elim
  | ρ, T :: Ts, Q, r :: rs, h, hsp, hq => by
    obtain ⟨x, hx⟩ := sigChainV_inhabited (h.2.2 r hsp.1) hsp.2 hq
    show ∃ y, y ∈ˢ sigmaSet s (interp V ρ T) fun r => sigChainV s (cons r ρ) Ts Q
    by_cases hs : s = 0
    · subst hs
      have hr : r = pt := mem_univ_zero h.1 hsp.1
      have hx' : x ∈ˢ sigChainV 0 (cons r ρ) Ts Q := hx
      exact ⟨pt, pt_mem_sigma hsp.1 hx'⟩
    · exact ⟨spair r x, spair_mem hs hsp.1 hx⟩

/-- **A chain element's components**: a fitting spine satisfying `Q`,
its `i`-th component the `i`-th projection, the `i`-th tail in the
chain of the remaining types. -/
theorem mem_sigChainV :
    ∀ {ρ : Nat → V} {Ts : List AnnotTerm} {Q : AnnotTerm} {x : V}, ChainOk s ρ Ts Q →
      x ∈ˢ sigChainV s ρ Ts Q →
      ∃ rs : List V, SpineFit ρ Ts rs ∧ (pt : V) ∈ˢ interp V (consList rs ρ) Q ∧
        ∀ i, i < Ts.length → sfst (ssndN i x) = rs.getD i pt ∧
          ssndN i x ∈ˢ sigChainV s (consList (rs.take i) ρ) (Ts.drop i) Q
  | _, [], _, x, h, hx => by
    refine ⟨[], trivial, ?_, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    have : x = pt := eq_pt_of_mem_univZero h.1 hx
    rw [this] at hx; exact hx
  | ρ, T :: Ts, Q, x, h, hx => by
    obtain ⟨a, e, ha, he, hz, hpos⟩ := mem_sigma_elim hx
    obtain ⟨rs, hsp, hq, hproj⟩ := mem_sigChainV (h.2.2 a ha) he
    -- the second projection is the tail in both regimes
    have hsnd : ssnd x = e := by
      by_cases hs : s = 0
      · subst hs
        rw [hz rfl, ssnd_pt]
        exact (mem_univ_zero (sigChainV_univ (h.2.2 a ha)) he).symm
      · rw [hpos hs, ssnd_spair]
    have hfst : sfst x = a := by
      by_cases hs : s = 0
      · subst hs
        rw [hz rfl, sfst_pt]
        exact (mem_univ_zero h.1 ha).symm
      · rw [hpos hs, sfst_spair]
    refine ⟨a :: rs, ⟨ha, hsp⟩, hq, fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨hfst, hx⟩
    | succ i =>
      obtain ⟨h1, h2⟩ := hproj i (by simpa using hi)
      refine ⟨?_, ?_⟩
      · show sfst (ssndN i (ssnd x)) = _
        rw [hsnd, h1]; rfl
      · show ssndN i (ssnd x) ∈ˢ _
        rw [hsnd]
        simpa using h2

/-- **The projections are graded**, at a graded chain element. -/
theorem wd_projChainAV :
    ∀ (i : Nat) {e : AnnotTerm} {ρ ρ' : Nat → V} {Ts : List AnnotTerm} {Q : AnnotTerm},
      ChainOk s ρ' Ts Q → interp V ρ e ∈ˢ sigChainV s ρ' Ts Q → WellDenoted V ρ e →
      i < Ts.length → WellDenoted V ρ (projChainAV i e)
  | _, _, _, _, [], _, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | 0, e, ρ, ρ', T :: Ts, Q, h, hx, hwe, _ => by
    show WellDenoted V ρ (.fst e)
    rw [WellDenoted_fst]
    refine ⟨hwe, s, s, interp V ρ' T, fun r => sigChainV s (cons r ρ') Ts Q, ?_, h.1,
      fun r hr => sigChainV_univ (h.2.2 r hr)⟩
    rw [natMax_self]; exact hx
  | i + 1, e, ρ, ρ', T :: Ts, Q, h, hx, hwe, hi => by
    show WellDenoted V ρ (projChainAV i (.snd e))
    obtain ⟨a, e', ha, he', hz, hpos⟩ := mem_sigma_elim hx
    have hsnd : ssnd (interp V ρ e) = e' := by
      by_cases hs : s = 0
      · subst hs
        rw [hz rfl, ssnd_pt]
        exact (mem_univ_zero (sigChainV_univ (h.2.2 a ha)) he').symm
      · rw [hpos hs, ssnd_spair]
    refine wd_projChainAV i (ρ' := cons a ρ') (h.2.2 a ha) ?_ ?_ (by simpa using hi)
    · show ssnd (interp V ρ e) ∈ˢ _
      rw [hsnd]; exact he'
    · show WellDenoted V ρ (.snd e)
      rw [WellDenoted_snd]
      refine ⟨hwe, s, s, interp V ρ' T, fun r => sigChainV s (cons r ρ') Ts Q, ?_, h.1,
        fun r hr => sigChainV_univ (h.2.2 r hr)⟩
      rw [natMax_self]; exact hx

/-- **The chosen element**: its value and grading, at an inhabited chain. -/
theorem selChainAV_facts {ρ : Nat → V} {Ts : List AnnotTerm} {Q : AnnotTerm}
    (h : ChainOk s ρ Ts Q) (hne : ∃ x, x ∈ˢ sigChainV s ρ Ts Q) :
    interp V ρ (selChainAV s Ts Q) = schoice (sigChainV s ρ Ts Q) ∧
      WellDenoted V ρ (selChainAV s Ts Q) := by
  have hu := sigChainV_univ h
  have hchoice := choiceV_mem (V := V) s
  refine ⟨?_, ?_⟩
  · show SetTheory.app (SetTheory.app (choiceV V s) (interp V ρ (sigChainAV s Ts Q))) pt = _
    rw [interp_sigChainAV h]
    exact choiceV_app V hu (pt_mem_dnegSpace_of hne.choose_spec)
  · show WellDenoted V ρ (.app (.app (.const .choice [s]) (sigChainAV s Ts Q)) .prf)
    rw [WellDenoted_app]
    refine ⟨?_, trivial, s, dnegSpace V (sigChainV s ρ Ts Q), fun _ => sigChainV s ρ Ts Q,
      ?_, ?_, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨trivial, wd_sigChainAV h, s, univ s,
        fun A => piR s (dnegSpace V A) fun _ => A, hchoice, ?_, fun h0 A _ => ?_⟩
      · rw [interp_sigChainAV h]; exact hu
      · show piR s _ _ ∈ˢ _
        rw [h0]; exact piR_zero_mem_univZero
    · show SetTheory.app (choiceV V s) (interp V ρ (sigChainAV s Ts Q)) ∈ˢ _
      rw [interp_sigChainAV h]
      refine app_mem_piR hchoice hu (fun h0 A _ => ?_)
      show piR s _ _ ∈ˢ _
      rw [h0]; exact piR_zero_mem_univZero
    · exact pt_mem_dnegSpace_of hne.choose_spec
    · intro h0 _ _
      show sigChainV s ρ Ts Q ∈ˢ univZero
      rw [h0]
      have := hu
      rwa [h0, univ_zero] at this

/-- **THE KIT'S THEOREM**: at a formed, inhabited chain, the chosen
element's projections are a fitting spine whose components satisfy
`Q`, each projection graded. -/
theorem sigChain_choice {ρ : Nat → V} {Ts : List AnnotTerm} {Q : AnnotTerm}
    (h : ChainOk s ρ Ts Q) (hne : ∃ x, x ∈ˢ sigChainV s ρ Ts Q) :
    ∃ rs : List V, SpineFit ρ Ts rs ∧ (pt : V) ∈ˢ interp V (consList rs ρ) Q ∧
      ∀ i, i < Ts.length →
        interp V ρ (projChainAV i (selChainAV s Ts Q)) = rs.getD i pt ∧
        WellDenoted V ρ (projChainAV i (selChainAV s Ts Q)) := by
  obtain ⟨hv, hwd⟩ := selChainAV_facts h hne
  have hsel : schoice (sigChainV s ρ Ts Q) ∈ˢ sigChainV s ρ Ts Q := schoice_mem hne.choose_spec
  obtain ⟨rs, hsp, hq, hproj⟩ := mem_sigChainV h hsel
  refine ⟨rs, hsp, hq, fun i hi => ⟨?_, ?_⟩⟩
  · rw [interp_projChainAV, hv]
    exact (hproj i hi).1
  · exact wd_projChainAV i h (by rw [hv]; exact hsel) hwd hi

end Chain

/-! ## The block shape: `k` closed types, the equations' conjunction -/

/-- The `k` component types, each lifted under the earlier binders. -/
def blockTsAV (k : Nat) (T : Nat → AnnotTerm) : List AnnotTerm :=
  (List.range k).map fun mm => (T mm).liftN mm 0

/-- **The block's recursor leaf** of member `mm`: the `mm`-th
projection of the chosen tuple of the `k` types with the equations. -/
def blockRecAVI (s k : Nat) (T : Nat → AnnotTerm) (eqs : List AnnotTerm) (mm : Nat) : AnnotTerm :=
  projChainAV mm (selChainAV s (blockTsAV k T) (andChainAV eqs))

omit [SetTheory V] in
theorem blockTsAV_length (k : Nat) (T : Nat → AnnotTerm) : (blockTsAV k T).length = k := by
  simp [blockTsAV]

/-- A lifted closed type reads at the base frame. -/
theorem interp_liftN_consList (e : AnnotTerm) (rs : List V) (ρ : Nat → V) :
    interp V (consList rs ρ) (e.liftN rs.length 0) = interp V ρ e := by
  rw [interp_liftN, shiftE_consList]

theorem wd_liftN_consList (e : AnnotTerm) (rs : List V) (ρ : Nat → V) :
    WellDenoted V (consList rs ρ) (e.liftN rs.length 0) ↔ WellDenoted V ρ e := by
  rw [WellDenoted_liftN, shiftE_consList]

/-- The lifted types' list, at a prefix's length. -/
theorem blockTs_drop_cons {k : Nat} (T : Nat → AnnotTerm) {p : Nat} (hpl : p < k) :
    ((List.range k).drop p).map (fun mm => (T mm).liftN mm 0)
      = (T p).liftN p 0 :: ((List.range k).drop (p + 1)).map (fun mm => (T mm).liftN mm 0) := by
  rw [List.drop_eq_getElem_cons (by rw [List.length_range]; exact hpl), List.getElem_range,
    List.map_cons]

theorem blockTs_drop_nil {k : Nat} (T : Nat → AnnotTerm) {p : Nat} (hpl : k ≤ p) :
    ((List.range k).drop p).map (fun mm => (T mm).liftN mm 0) = [] := by
  rw [List.drop_eq_nil_of_le (by rw [List.length_range]; exact hpl)]
  rfl

theorem getD_append_snoc (pre : List V) (r : V) (i : Nat) :
    (pre ++ [r]).getD (pre.length + i) pt = [r].getD i pt := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem getD_append_lt (pre : List V) (r : V) {i : Nat} (hi : i < pre.length) :
    (pre ++ [r]).getD i pt = pre.getD i pt := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- A fit of the lifted types, from the components' memberships. -/
theorem spineFit_blockTs_go {ρ : Nat → V} {k : Nat} (T : Nat → AnnotTerm) :
    ∀ (n : Nat) (pre rs : List V), pre.length + n = k → rs.length = n →
      (∀ i, i < n → rs.getD i pt ∈ˢ interp V ρ (T (pre.length + i))) →
      SpineFit (consList pre ρ)
        (((List.range k).drop pre.length).map fun mm => (T mm).liftN mm 0) rs
  | 0, pre, [], hlen, _, _ => by
    rw [blockTs_drop_nil T (p := pre.length) (by omega)]; trivial
  | 0, _, _ :: _, _, hrs, _ => nomatch hrs
  | _ + 1, _, [], _, hrs, _ => nomatch hrs
  | n + 1, pre, r :: rs, hlen, hrs, hmem => by
    rw [blockTs_drop_cons T (p := pre.length) (by omega)]
    refine ⟨?_, ?_⟩
    · rw [interp_liftN_consList]
      have := hmem 0 (Nat.succ_pos n)
      simpa using this
    · have ih := spineFit_blockTs_go (k := k) T n (pre ++ [r]) rs (by simp; omega) (by simpa using hrs)
        fun i hi => by
          have := hmem (i + 1) (by omega)
          simp only [List.length_append, List.length_singleton, List.getD_cons_succ] at this ⊢
          rw [show pre.length + 1 + i = pre.length + (i + 1) from by omega]
          exact this
      rw [consList_append] at ih
      simpa using ih

theorem spineFit_blockTs {ρ : Nat → V} {k : Nat} {T : Nat → AnnotTerm} {rs : List V}
    (hlen : rs.length = k) (hmem : ∀ mm, mm < k → rs.getD mm pt ∈ˢ interp V ρ (T mm)) :
    SpineFit ρ (blockTsAV k T) rs := by
  have := spineFit_blockTs_go (ρ := ρ) (k := k) T k [] rs (by simp) hlen
    (fun i hi => by simpa using hmem i hi)
  simpa [blockTsAV] using this

/-- The components of a fit of the lifted types. -/
theorem spineFit_blockTs_inv_go {ρ : Nat → V} {k : Nat} (T : Nat → AnnotTerm) :
    ∀ (n : Nat) (pre rs : List V), pre.length + n = k →
      SpineFit (consList pre ρ)
        (((List.range k).drop pre.length).map fun mm => (T mm).liftN mm 0) rs →
      rs.length = n ∧ ∀ i, i < n → rs.getD i pt ∈ˢ interp V ρ (T (pre.length + i))
  | 0, pre, rs, hlen, hsp => by
    rw [blockTs_drop_nil T (p := pre.length) (by omega)] at hsp
    cases rs with
    | nil => exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | cons r rs => exact hsp.elim
  | n + 1, pre, rs, hlen, hsp => by
    rw [blockTs_drop_cons T (p := pre.length) (by omega)] at hsp
    cases rs with
    | nil => exact hsp.elim
    | cons r rs =>
      obtain ⟨hr, hrest⟩ := hsp
      rw [interp_liftN_consList] at hr
      have ih := spineFit_blockTs_inv_go (k := k) T n (pre ++ [r]) rs (by simp; omega) (by
        rw [consList_append]
        simpa using hrest)
      simp only [List.length_append, List.length_singleton] at ih
      refine ⟨by simp [ih.1], fun i hi => ?_⟩
      cases i with
      | zero => simpa using hr
      | succ i =>
        have := ih.2 i (by omega)
        simp only [List.getD_cons_succ]
        rw [show pre.length + (i + 1) = pre.length + 1 + i from by omega]
        exact this

theorem spineFit_blockTs_inv {ρ : Nat → V} {k : Nat} {T : Nat → AnnotTerm} {rs : List V}
    (hsp : SpineFit ρ (blockTsAV k T) rs) :
    rs.length = k ∧ ∀ mm, mm < k → rs.getD mm pt ∈ˢ interp V ρ (T mm) := by
  have := spineFit_blockTs_inv_go (ρ := ρ) (k := k) T k [] rs (by simp)
    (by simpa [blockTsAV] using hsp)
  simpa using this

/-- The block chain's formation premise from the types' and the
equations'. -/
theorem chainOk_block_go {s : Nat} {ρ : Nat → V} {k : Nat} (T : Nat → AnnotTerm)
    (eqs : List AnnotTerm)
    (hT : ∀ mm, mm < k → interp V ρ (T mm) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (T mm))
    (heq : ∀ rs : List V, rs.length = k → (∀ mm, mm < k → rs.getD mm pt ∈ˢ interp V ρ (T mm)) →
      ∀ e ∈ eqs, interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e) :
    ∀ (n : Nat) (pre : List V), pre.length + n = k →
      (∀ mm, mm < pre.length → pre.getD mm pt ∈ˢ interp V ρ (T mm)) →
      ChainOk s (consList pre ρ)
        (((List.range k).drop pre.length).map fun mm => (T mm).liftN mm 0) (andChainAV eqs)
  | 0, pre, hlen, hpre => by
    rw [blockTs_drop_nil T (p := pre.length) (by omega)]
    show ChainOk s (consList pre ρ) [] (andChainAV eqs)
    exact andChainAV_facts (heq pre (by omega) (fun mm hmm => hpre mm (by omega)))
  | n + 1, pre, hlen, hpre => by
    rw [blockTs_drop_cons T (p := pre.length) (by omega)]
    have hTp := hT pre.length (by omega)
    refine ⟨by rw [interp_liftN_consList]; exact hTp.1,
      by rw [wd_liftN_consList]; exact hTp.2, fun r hr => ?_⟩
    rw [interp_liftN_consList] at hr
    have ih := chainOk_block_go (k := k) T eqs hT heq n (pre ++ [r]) (by simp; omega) fun mm hmm => by
      simp only [List.length_append, List.length_singleton] at hmm
      rcases Nat.lt_or_ge mm pre.length with h | h
      · rw [getD_append_lt pre r h]; exact hpre mm h
      · have : mm = pre.length + 0 := by omega
        rw [this, getD_append_snoc]
        simpa using hr
    rw [consList_append] at ih
    simpa using ih

theorem chainOk_block {s k : Nat} {ρ : Nat → V} {T : Nat → AnnotTerm} {eqs : List AnnotTerm}
    (hT : ∀ mm, mm < k → interp V ρ (T mm) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (T mm))
    (heq : ∀ rs : List V, rs.length = k → (∀ mm, mm < k → rs.getD mm pt ∈ˢ interp V ρ (T mm)) →
      ∀ e ∈ eqs, interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e) :
    ChainOk s ρ (blockTsAV k T) (andChainAV eqs) := by
  have := chainOk_block_go (ρ := ρ) T eqs hT heq k [] (by simp) (fun mm hmm => absurd hmm (by simp))
  simpa [blockTsAV] using this

/-- A tuple of length `k` is the map of its components. -/
theorem range_map_getD {rs : List V} {k : Nat} (hlen : rs.length = k) :
    (List.range k).map (fun mm => rs.getD mm pt) = rs := by
  apply List.ext_getElem
  · simp [hlen]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]

/-- **The block's chosen tuple**: its components are typed at their
recursor types, satisfy every equation, and ARE the members' leaves,
each graded — given the types' formation, the equations' grading at
every fitting tuple, and a candidate tuple. -/
theorem blockRecAVI_facts (s k : Nat) (T : Nat → AnnotTerm) (eqs : List AnnotTerm) (ρ : Nat → V)
    (hT : ∀ mm, mm < k → interp V ρ (T mm) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (T mm))
    (heq : ∀ rs : List V, rs.length = k → (∀ mm, mm < k → rs.getD mm pt ∈ˢ interp V ρ (T mm)) →
      ∀ e ∈ eqs, interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e)
    (cand : Nat → V) (hcand : ∀ mm, mm < k → cand mm ∈ˢ interp V ρ (T mm))
    (hceq : ∀ e ∈ eqs, (pt : V) ∈ˢ interp V (consList ((List.range k).map cand) ρ) e) :
    ∃ a : Nat → V,
      (∀ mm, mm < k → a mm ∈ˢ interp V ρ (T mm) ∧
        interp V ρ (blockRecAVI s k T eqs mm) = a mm ∧
        WellDenoted V ρ (blockRecAVI s k T eqs mm)) ∧
      ∀ e ∈ eqs, (pt : V) ∈ˢ interp V (consList ((List.range k).map a) ρ) e := by
  have hok := chainOk_block (s := s) hT heq
  have hcsp : SpineFit ρ (blockTsAV k T) ((List.range k).map cand) :=
    spineFit_blockTs (by simp) fun mm hmm => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hmm]
      exact hcand mm hmm
  have hcmem : ∀ mm, mm < k → ((List.range k).map cand).getD mm pt ∈ˢ interp V ρ (T mm) :=
    fun mm hmm => (spineFit_blockTs_inv hcsp).2 mm hmm
  have hne := sigChainV_inhabited hok hcsp
    ((pt_mem_andChainAV_iff (heq _ (by simp) hcmem)).mpr hceq)
  obtain ⟨rs, hsp, hq, hproj⟩ := sigChain_choice hok hne
  obtain ⟨hlen, hmem⟩ := spineFit_blockTs_inv hsp
  refine ⟨fun mm => rs.getD mm pt, fun mm hmm => ⟨hmem mm hmm, ?_, ?_⟩, ?_⟩
  · exact (hproj mm (by rw [blockTsAV_length]; exact hmm)).1
  · exact (hproj mm (by rw [blockTsAV_length]; exact hmm)).2
  · rw [range_map_getD hlen]
    exact (pt_mem_andChainAV_iff (heq rs hlen hmem)).mp hq

end ConLeche.Semantics
