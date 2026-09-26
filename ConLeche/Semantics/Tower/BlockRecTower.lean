module

public import ConLeche.Semantics.Tower.TowerKit
public import ConLeche.SetModel.GraphRec
public import ConLeche.SetModel.UnionRec
import ConLeche.Semantics.Kit
import ConLeche.Semantics.Tower.FixTower

@[expose] public section

/-!
# The recursor family of a `k`-member block

The ι-specified chosen tuple (the Σ'-chain kit); the recursor family's
leaf and its ι laws; its candidate from the graph kit.
-/

/-!
## The ι-specified chosen tuple: the Σ'-chain kit

A block's recursors are ONE chosen tuple pinned by its ι
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


/-! ## `PSigma'`, `choice` -/

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
  have hps := psigmaV_rr_mem (V := V) 0
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

/-! ## An equation under a `Prop`-valued Π-tower -/

/-- A `Prop`-valued Π-tower over an equation is inhabited by `pt` iff
the equation holds at every fitting spine. -/
theorem pt_mem_mkPisAV_eqE_iff :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {l r : AnnotTerm} {ρ : Nat → V},
      (∀ d ∈ ds, d.2.1 = 0) →
      ((pt : V) ∈ˢ interp V ρ (mkPisAV ds (.eqE l r)) ↔
        ∀ xs : List V, SpineFit ρ (ds.map (·.2.2)) xs →
          interp V (consList xs ρ) l = interp V (consList xs ρ) r)
  | [], l, r, ρ, _ => by
    show (pt : V) ∈ˢ eqv (interp V ρ l) (interp V ρ r) ↔ _
    constructor
    · intro h xs hsp
      cases xs with
      | nil => exact eq_of_mem_eqv h
      | cons x xs => exact hsp.elim
    · intro h
      have := h [] trivial
      simp only [consList_nil] at this
      rw [this]; exact pt_mem_eqv_self _
  | d :: ds, l, r, ρ, hz => by
    have hd : d.2.1 = 0 := hz d (.head _)
    have hrest : ∀ x, interp V (cons x ρ) (mkPisAV ds (.eqE l r)) ∈ˢ (univZero : V) := by
      intro x
      cases ds with
      | nil => exact eqv_mem_univZero _ _
      | cons d' ds' =>
        show piR d'.2.1 _ _ ∈ˢ _
        rw [hz d' (.tail _ (.head _))]
        exact piR_zero_mem_univZero
    show (pt : V) ∈ˢ piR d.2.1 (interp V ρ d.2.2) (fun x => interp V (cons x ρ) (mkPisAV ds (.eqE l r))) ↔ _
    rw [hd]
    constructor
    · intro h xs hsp
      cases xs with
      | nil => exact hsp.elim
      | cons x xs =>
        obtain ⟨y, hy⟩ := piR_zero_elim h hsp.1
        have hy' : (pt : V) ∈ˢ interp V (cons x ρ) (mkPisAV ds (.eqE l r)) :=
          eq_pt_of_mem_univZero (hrest x) hy ▸ hy
        exact (pt_mem_mkPisAV_eqE_iff (fun d' hd' => hz d' (.tail _ hd'))).mp hy' xs hsp.2
    · intro h
      refine pt_mem_piR_zero_of fun x hx => ?_
      exact (pt_mem_mkPisAV_eqE_iff (fun d' hd' => hz d' (.tail _ hd'))).mpr
        fun xs hsp => h (x :: xs) ⟨hx, hsp⟩

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
    have hps := psigmaV_rr_mem (V := V) s
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

theorem getD_snoc_at (pre : List V) (r : V) (i : Nat) :
    (pre ++ [r]).getD (pre.length + i) pt = [r].getD i pt := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem getD_snoc_lt (pre : List V) (r : V) {i : Nat} (hi : i < pre.length) :
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
      · rw [getD_snoc_lt pre r h]; exact hpre mm h
      · have : mm = pre.length + 0 := by omega
        rw [this, getD_snoc_at]
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


/-!
## The recursor family of a k-member block: the leaf and its ι laws

The recursor stage CHECKS the stream's recursors (`targetRecCheck`,
`Kernel/Inductives/RecCheck.lean`) instead of generating them.  What
the model needs in exchange is a VALUE for each
of the `K` recursors of the block that satisfies exactly the equations
the check certified — one chosen tuple, pinned by its ι equations
(DESIGN v2 §3.2, the leaf):

    blockRecAV c  :=  projAV c (fst (choice.{s} (Σ' rs : ⟨RecTy_0, …, RecTy_{K-1}⟩, IotaAll rs) prf))

with `RecTy_c` the READING of the stream's recursor type of class `c`
(a `mkPisAV` over its binder data: the parameters, the arbitrary
`nP…rP-1` stretch, the indices and the major, then the conclusion) and

    IotaAll rs  =  ⋀_{c,j} ∀ x⃗ f⃗, eqE (app^ (projAV c rs) [x⃗, e⃗_j, C_j p⃗ f⃗]) (Rb_{c,j}[rec ↦ rs])

the conjunction over every class `c` and constructor `j` of the rule's
equation at the rule's own prefix `x⃗` (`rP` binders, read off the
recursor's record) and the constructor's fields `f⃗`.

**Where the recursor occurrences went.**  The stored right-hand side's
recursor occurrences are the GUARDED SPINES `rec_{c'} x⃗ e⃗(a⃗) (f_i a⃗)`
the check abstracted to `ih` openers (`targetRule`,
`Kernel/Inductives/RecCheck.lean`), so the substitution
`[rec ↦ rs]` is performed AT THE SPINE LEVEL, once per ih opener:
`Rb = Rb''[ih_i ↦ ihFun_i]` with `Rb''` the RESIDUE — recursor-free by
construction, which is why the residue may be typed at the
CONSTRUCTORS' environment (G1).  `instsAV` below is that substitution,
and `interp_instsAV` is the substitution lemma: reading the
substituted body at a frame is reading the residue at the frame
extended by the ih VALUES.  Nothing here has to descend through the
right-hand side's syntax — the check already did.

**What is input and what is generated.**  Everything the equation
mentions is INPUT data, read at the CHAIN frame (under the `K` Σ'
binders, where class `c`'s component is `bvar (K-1-c)`): the rule's
prefix domains `pdoms`, the constructor's field domains `fdoms`, its
index expressions `es`, the constructed major `mk`, the ih terms `ihs`
and the residue `Rb`.  The Model tier supplies them as the readings of
the stored forms, lifted by `K`; the ih terms' canonical shape is the
curried λ-tower over the field's telescope of the guarded call.
-/


/-! ## Substituting a block of innermost binders

`instsAV d vs e` replaces the `vs.length` innermost binders of `e` by
`vs` — `vs[0]` the OUTERMOST of the replaced block, every `v` written
at the frame BELOW the block (so `vs[t]` is lifted past the `t`
binders still standing when its turn comes).  This is the ih
substitution `[ih_i ↦ ihFun_i]` of the design. -/

def instsAV : Nat → List AnnotTerm → AnnotTerm → AnnotTerm
  | _, [], e => e
  | d, v :: vs, e => (instsAV (d + 1) vs e).inst (v.liftN d 0)

omit [SetTheory V] in
@[simp] theorem instsAV_nil (d : Nat) (e : AnnotTerm) : instsAV d [] e = e := rfl

theorem interp_instsAV_go : ∀ (vs : List AnnotTerm) (pre : List V) (e : AnnotTerm) (ρ : Nat → V),
    interp V (consList pre ρ) (instsAV pre.length vs e)
      = interp V (consList (pre ++ vs.map (interp V ρ)) ρ) e
  | [], pre, e, ρ => by simp
  | v :: vs, pre, e, ρ => by
    show interp V (consList pre ρ)
      ((instsAV (pre.length + 1) vs e).inst ((v.liftN pre.length 0))) = _
    rw [interp_inst0, interp_liftN_consList, consList_snoc']
    have h := interp_instsAV_go vs (pre ++ [interp V ρ v]) e ρ
    rw [List.length_append, List.length_singleton] at h
    rw [h]
    simp

/-- **THE SUBSTITUTION LEMMA** (spine-structural): the
body with the ih openers substituted, read at a frame, is the RESIDUE
read at that frame extended by the ih VALUES.  The recursion through
the right-hand side's syntax is the check's, not the model's. -/
theorem interp_instsAV (vs : List AnnotTerm) (e : AnnotTerm) (ρ : Nat → V) :
    interp V ρ (instsAV 0 vs e) = interp V (consList (vs.map (interp V ρ)) ρ) e := by
  have h := interp_instsAV_go (V := V) vs [] e ρ
  simpa using h

theorem wd_instsAV_go : ∀ (vs : List AnnotTerm) (pre : List V) (e : AnnotTerm) (ρ : Nat → V),
    (∀ v ∈ vs, WellDenoted V ρ v) →
    (WellDenoted V (consList pre ρ) (instsAV pre.length vs e)
      ↔ WellDenoted V (consList (pre ++ vs.map (interp V ρ)) ρ) e)
  | [], pre, e, ρ, _ => by simp
  | v :: vs, pre, e, ρ, hv => by
    show WellDenoted V (consList pre ρ)
      ((instsAV (pre.length + 1) vs e).inst ((v.liftN pre.length 0))) ↔ _
    rw [WellDenoted_inst0 V ((wd_liftN_consList v pre ρ).mpr (hv v (.head _))),
      interp_liftN_consList, consList_snoc']
    have h := wd_instsAV_go vs (pre ++ [interp V ρ v]) e ρ fun v' hv' => hv v' (.tail _ hv')
    rw [List.length_append, List.length_singleton] at h
    rw [h]
    simp

theorem wd_instsAV {vs : List AnnotTerm} {e : AnnotTerm} {ρ : Nat → V}
    (hv : ∀ v ∈ vs, WellDenoted V ρ v) :
    WellDenoted V ρ (instsAV 0 vs e) ↔ WellDenoted V (consList (vs.map (interp V ρ)) ρ) e := by
  have h := wd_instsAV_go (V := V) vs [] e ρ hv
  simpa using h

theorem foldl_app_map (f : AnnotTerm → V) (b : V) :
    ∀ as : List AnnotTerm,
      as.foldl (fun r a => SetTheory.app r (f a)) b = (as.map f).foldl SetTheory.app b
  | [] => rfl
  | a :: as => by
    show (as.foldl (fun r a => SetTheory.app r (f a)) (SetTheory.app b (f a))) = _
    rw [foldl_app_map f _ as]
    rfl

/-! ## The rule's own prefix variables

A rule binds `rP + nF` λs: the recursor's own prefix (the parameters
and the arbitrary stretch), then the constructor's fields.  A guarded
call's prefix arguments are the rule's OWN prefix variables (the kernel
requires `rP_{c'} = rP`), and so is the ι equation's left-hand side's prefix. -/

/-- The `rP` prefix variables as bvars, at the frame
`prefix ++ (nF further binders)`. -/
def prefVarsAV (rP nF : Nat) : List AnnotTerm :=
  (List.range rP).map fun l => .bvar (nF + rP - 1 - l)

/-- **The prefix variables read back the prefix spine.** -/
theorem interp_prefVarsAV {rP : Nat} {xs bs : List V} {ρ : Nat → V} (hx : xs.length = rP) :
    (prefVarsAV rP bs.length).map (interp V (consList (xs ++ bs) ρ)) = xs := by
  have hlen : (xs ++ bs).length = bs.length + rP := by
    rw [List.length_append, hx]; omega
  have hval : ∀ l, l < rP →
      interp V (consList (xs ++ bs) ρ) (.bvar (bs.length + rP - 1 - l)) = xs.getD l pt := by
    intro l hl
    show consList (xs ++ bs) ρ (bs.length + rP - 1 - l) = _
    rw [consList_getD_of_lt _ _ _ (by omega), hlen,
      show bs.length + rP - 1 - (bs.length + rP - 1 - l) = l from by omega,
      List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
      ← List.getD_eq_getElem?_getD]
  calc (prefVarsAV rP bs.length).map (interp V (consList (xs ++ bs) ρ))
      = (List.range rP).map (fun l => xs.getD l pt) := by
        rw [prefVarsAV, List.map_map]
        exact List.map_congr_left fun l hl => hval l (List.mem_range.mp hl)
    _ = xs := range_map_getD hx

/-! ## The ι equation of one rule -/

/-- The binder data of a `Prop`-valued Π-tower over the given domains
(both numerals `0`: the tower is a proposition and so is its body). -/
def propBinders (doms : List AnnotTerm) : List (Nat × Nat × AnnotTerm) :=
  doms.map fun D => (0, 0, D)

omit [SetTheory V] in
@[simp] theorem propBinders_doms (doms : List AnnotTerm) :
    (propBinders doms).map (·.2.2) = doms := by
  simp [propBinders, Function.comp_def]

omit [SetTheory V] in
theorem propBinders_cod {doms : List AnnotTerm} : ∀ d ∈ propBinders doms, d.2.1 = 0 := by
  intro d hd
  obtain ⟨D, -, rfl⟩ := List.mem_map.mp hd
  rfl

/-- A `Prop`-valued Π-tower over an equation is a truth value. -/
theorem mkPisAV_eqE_univZero {l r : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      (∀ d ∈ ds, d.2.1 = 0) → interp V σ (mkPisAV ds (.eqE l r)) ∈ˢ (univZero : V)
  | [], _, _ => eqv_mem_univZero _ _
  | d :: ds, σ, hz => by
    show piR d.2.1 _ _ ∈ˢ _
    rw [hz d (.head _)]
    exact piR_zero_mem_univZero

/-- **One rule's ι equation**, at the CHAIN frame (under the `K` Σ'
binders, class `c`'s component `bvar (K-1-c)`).  Quantified over the
rule's prefix `x⃗` (domains `pdoms`) and the constructor's fields `f⃗`
(domains `fdoms`); the left-hand side is the class's component applied
along `(x⃗, e⃗_j, mk_j)`, the right-hand side the residue `Rb` with its
ih openers substituted by `ihs`. -/
def iotaEqAV (K c : Nat) (pdoms fdoms es : List AnnotTerm) (mk : AnnotTerm)
    (ihs : List AnnotTerm) (Rb : AnnotTerm) : AnnotTerm :=
  mkPisAV (propBinders (pdoms ++ fdoms))
    (.eqE
      (AnnotTerm.mkAppN (.bvar (pdoms.length + fdoms.length + (K - 1 - c)))
        (prefVarsAV pdoms.length fdoms.length ++ es ++ [mk]))
      (instsAV 0 ihs Rb))

/-- The ι equation is a truth value. -/
theorem iotaEqAV_univZero {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V} :
    interp V σ (iotaEqAV K c pdoms fdoms es mk ihs Rb) ∈ˢ (univZero : V) :=
  mkPisAV_eqE_univZero propBinders_cod

/-- **The ι equation is graded** when the domains are graded along the
telescope and both sides are graded at every fitting spine. -/
theorem wd_iotaEqAV {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V}
    (hdoms : FieldsOkB 0 σ (pdoms ++ fdoms))
    (hbody : ∀ ys, SpineFit σ (pdoms ++ fdoms) ys →
      WellDenoted V (consList ys σ)
          (AnnotTerm.mkAppN (.bvar (pdoms.length + fdoms.length + (K - 1 - c)))
            (prefVarsAV pdoms.length fdoms.length ++ es ++ [mk])) ∧
        WellDenoted V (consList ys σ) (instsAV 0 ihs Rb)) :
    WellDenoted V σ (iotaEqAV K c pdoms fdoms es mk ihs Rb) := by
  refine WellDenoted_mkPisAV_of (by simpa using hdoms) fun ys hsp => ?_
  rw [propBinders_doms] at hsp
  rw [WellDenoted_eqE]
  exact hbody ys hsp

/-- **The two sides of one rule's ι equation**, read at a fitting
spine `xs ++ fs` of the rule's prefix and the constructor's fields:
the left is the class's component folded along `(x⃗, e⃗_j, mk_j)`, the
right is the RESIDUE at the ih values. -/
theorem iotaEqAV_sides {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V} {R : V}
    (hR : σ (K - 1 - c) = R) {xs fs : List V}
    (hxl : xs.length = pdoms.length) (hfl : fs.length = fdoms.length) :
    interp V (consList (xs ++ fs) σ)
        (AnnotTerm.mkAppN (.bvar (pdoms.length + fdoms.length + (K - 1 - c)))
          (prefVarsAV pdoms.length fdoms.length ++ es ++ [mk]))
        = (xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) σ))).foldl SetTheory.app R ∧
      interp V (consList (xs ++ fs) σ) (instsAV 0 ihs Rb)
        = interp V (consList (ihs.map (interp V (consList (xs ++ fs) σ)))
            (consList (xs ++ fs) σ)) Rb := by
  refine ⟨?_, interp_instsAV _ _ _⟩
  have hhead : interp V (consList (xs ++ fs) σ)
      (.bvar (pdoms.length + fdoms.length + (K - 1 - c))) = R := by
    show consList (xs ++ fs) σ (pdoms.length + fdoms.length + (K - 1 - c)) = R
    rw [show pdoms.length + fdoms.length + (K - 1 - c)
          = (K - 1 - c) + (xs ++ fs).length from by
        rw [List.length_append, hxl, hfl]; omega,
      consList_apply_add, hR]
  have hpre : (prefVarsAV pdoms.length fdoms.length).map (interp V (consList (xs ++ fs) σ))
      = xs := by
    have h := interp_prefVarsAV (V := V) (rP := pdoms.length) (xs := xs) (bs := fs) (ρ := σ) hxl
    rw [hfl] at h
    exact h
  have hargs : (prefVarsAV pdoms.length fdoms.length ++ es ++ [mk]).map
      (interp V (consList (xs ++ fs) σ))
      = xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) σ)) := by
    simp only [List.map_append, hpre, List.append_assoc]
  rw [interp_mkAppN, foldl_app_map, hhead, hargs]

/-- The length of a fit of the rule's binder data. -/
theorem iotaEqAV_fs_length {pdoms fdoms : List AnnotTerm} {σ : Nat → V} {xs fs : List V}
    (hxl : xs.length = pdoms.length) (hsp : SpineFit σ (pdoms ++ fdoms) (xs ++ fs)) :
    fs.length = fdoms.length := by
  have h := hsp.length_eq
  rw [List.length_append, List.length_append, hxl] at h
  omega

/-- **THE ι LAW, extracted**: at a fitting spine `xs ++ fs` of the
rule's prefix and the constructor's fields, the class's component
applied along the rule's left-hand side equals the residue read at the
frame extended by the ih values.  `hR` names the component: the
consumer instantiates `σ` with the chain frame `consList rs ρ`, where
`σ (K-1-c) = rs.getD c pt` is the class's leaf. -/
theorem iotaEqAV_law {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V} {R : V}
    (hR : σ (K - 1 - c) = R)
    (h : (pt : V) ∈ˢ interp V σ (iotaEqAV K c pdoms fdoms es mk ihs Rb))
    {xs fs : List V} (hxl : xs.length = pdoms.length)
    (hsp : SpineFit σ (pdoms ++ fdoms) (xs ++ fs)) :
    ((xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) σ))).foldl SetTheory.app R)
      = interp V (consList ((ihs.map (interp V (consList (xs ++ fs) σ)))) (consList (xs ++ fs) σ))
          Rb := by
  have heq := (pt_mem_mkPisAV_eqE_iff (V := V) (propBinders_cod (doms := pdoms ++ fdoms))).mp h
    (xs ++ fs) (by rw [propBinders_doms]; exact hsp)
  obtain ⟨hl, hr⟩ := iotaEqAV_sides hR hxl (iotaEqAV_fs_length hxl hsp)
  rw [hl, hr] at heq
  exact heq

/-- **The ι equation is INHABITED** by the laws at every fitting spine —
the direction the graph kit's candidate (`famCandG_hCand`) is fed
through. -/
theorem pt_mem_iotaEqAV_of {K c : Nat} {pdoms fdoms es : List AnnotTerm} {mk : AnnotTerm}
    {ihs : List AnnotTerm} {Rb : AnnotTerm} {σ : Nat → V} {R : V}
    (hR : σ (K - 1 - c) = R)
    (h : ∀ xs fs : List V, xs.length = pdoms.length →
      SpineFit σ (pdoms ++ fdoms) (xs ++ fs) →
      ((xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) σ))).foldl SetTheory.app R)
        = interp V (consList ((ihs.map (interp V (consList (xs ++ fs) σ))))
            (consList (xs ++ fs) σ)) Rb) :
    (pt : V) ∈ˢ interp V σ (iotaEqAV K c pdoms fdoms es mk ihs Rb) := by
  refine (pt_mem_mkPisAV_eqE_iff (V := V) (propBinders_cod (doms := pdoms ++ fdoms))).mpr
    fun ys hsp => ?_
  rw [propBinders_doms] at hsp
  have hlen : ys.length = pdoms.length + fdoms.length := by
    rw [hsp.length_eq, List.length_append]
  have hys : ys = ys.take pdoms.length ++ ys.drop pdoms.length := (List.take_append_drop _ _).symm
  have hxl : (ys.take pdoms.length).length = pdoms.length := by
    rw [List.length_take]; omega
  rw [hys] at hsp ⊢
  obtain ⟨hl, hr⟩ := iotaEqAV_sides hR hxl (iotaEqAV_fs_length hxl hsp)
  rw [hl, hr]
  exact h _ _ hxl hsp

/-! ## The λ-tower whose body sees the spine

The candidate the graph kit supplies (`famCandG`) is a λ-tower over the
recursor's whole binder data whose body needs the PREFIX values (the
parameters and the arbitrary stretch: the kit is built per prefix
frame), the INDEX values and the MAJOR — i.e. the accumulated spine,
not just the leaf frame.  `lamTowerA` is the semantic λ-tower with
that accumulator. -/

/-- The semantic λ-tower over binder data, with the body a function of
the ACCUMULATED spine and the leaf frame. -/
noncomputable def lamTowerA (m : Nat) :
    (Nat → V) → List V → List (Nat × Nat × AnnotTerm) → (List V → (Nat → V) → V) → V
  | ρ, acc, [], g => g acc ρ
  | ρ, acc, d :: ds, g => lamR m (interp V ρ d.2.2) fun a => lamTowerA m (cons a ρ) (acc ++ [a]) ds g

/-- `lamTowerA`'s walk premise: at every leaf frame reached the body is
in the conclusion's reading (a truth value at a zero bit). -/
def TowerWalkA (m : Nat) (C : AnnotTerm) (g : List V → (Nat → V) → V) :
    (Nat → V) → List V → List (Nat × Nat × AnnotTerm) → Prop
  | ρ, acc, [] => g acc ρ ∈ˢ interp V ρ C ∧ (m = 0 → interp V ρ C ∈ˢ (univZero : V))
  | ρ, acc, d :: ds => ∀ a, a ∈ˢ interp V ρ d.2.2 → TowerWalkA m C g (cons a ρ) (acc ++ [a]) ds

/-- **The tower inhabits the Π-tower's reading** — `mem_type` of the
candidate. -/
theorem lamTowerA_mem {m : Nat} {C : AnnotTerm} {g : List V → (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → TowerWalkA m C g ρ acc ds →
      lamTowerA m ρ acc ds g ∈ˢ interp V ρ (mkPisAV ds C)
  | [], _, _, _, h => h.1
  | d :: ds, ρ, acc, hz, h => by
    show lamR m (interp V ρ d.2.2) (fun a => lamTowerA m (cons a ρ) (acc ++ [a]) ds g)
      ∈ˢ piR d.2.1 (interp V ρ d.2.2) fun a => interp V (cons a ρ) (mkPisAV ds C)
    exact lamR_mem_zero_agree (hz d (.head _))
      fun a ha => lamTowerA_mem (fun d' hd' => hz d' (.tail _ hd')) (h a ha)

/-- **The tower's fold along a fitting spine** (nonzero bit) — the ι
law's left-hand side. -/
theorem lamTowerA_fold {m : Nat} (hm : m ≠ 0) {g : List V → (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc bs : List V},
      SpineFit ρ (ds.map (·.2.2)) bs →
      bs.foldl SetTheory.app (lamTowerA m ρ acc ds g) = g (acc ++ bs) (consList bs ρ)
  | [], _, acc, [], _ => by simp [lamTowerA]
  | [], _, _, _ :: _, hsp => hsp.elim
  | _ :: _, _, _, [], hsp => hsp.elim
  | d :: ds, ρ, acc, b :: bs, hsp => by
    show bs.foldl SetTheory.app (SetTheory.app (lamR m (interp V ρ d.2.2)
      fun a => lamTowerA m (cons a ρ) (acc ++ [a]) ds g) b) = _
    rw [app_lamR_pos hm hsp.1, consList_cons, lamTowerA_fold hm hsp.2]
    simp

/-! ## The family: its ι equations, its leaf, and its facts -/

/-- The family's ι equations: one per class `c < K` and constructor
`j < nCt c`, in class-major order.  `IotaAll` of the design. -/
def iotaEqsAV (K : Nat) (nCt : Nat → Nat) (pdoms : Nat → List AnnotTerm)
    (fdoms es : Nat → Nat → List AnnotTerm) (mk : Nat → Nat → AnnotTerm)
    (ihs : Nat → Nat → List AnnotTerm) (Rb : Nat → Nat → AnnotTerm) : List AnnotTerm :=
  (List.range K).flatMap fun c =>
    (List.range (nCt c)).map fun j =>
      iotaEqAV K c (pdoms c) (fdoms c j) (es c j) (mk c j) (ihs c j) (Rb c j)

omit [SetTheory V] in
theorem mem_iotaEqsAV {K : Nat} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
    {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
    {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {c j : Nat}
    (hc : c < K) (hj : j < nCt c) :
    iotaEqAV K c (pdoms c) (fdoms c j) (es c j) (mk c j) (ihs c j) (Rb c j)
      ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb :=
  List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc,
    List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩

omit [SetTheory V] in
/-- Every member of the family's equation list IS one rule's equation —
the form every per-equation premise is discharged in. -/
theorem forall_iotaEqsAV {K : Nat} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
    {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
    {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {P : AnnotTerm → Prop}
    (h : ∀ c, c < K → ∀ j, j < nCt c →
      P (iotaEqAV K c (pdoms c) (fdoms c j) (es c j) (mk c j) (ihs c j) (Rb c j))) :
    ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb, P e := by
  intro e he
  obtain ⟨c, hc, he⟩ := List.mem_flatMap.mp he
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp he
  exact h c (List.mem_range.mp hc) j (List.mem_range.mp hj)

/-- **THE LEAF**: the recursor of class `c` is the `c`-th projection of
the ONE chosen tuple of the `K` recursor types pinned by every rule's ι
equation. -/
def blockRecAV (s K : Nat) (RecTy : Nat → AnnotTerm) (eqs : List AnnotTerm) (c : Nat) :
    AnnotTerm :=
  blockRecAVI s K RecTy eqs c

/-- The chain frame of a tuple: the base frame under the `K` Σ'
binders, class `c`'s component at `bvar (K-1-c)`. -/
noncomputable def chainFrame (K : Nat) (a ρ : Nat → V) : Nat → V :=
  consList ((List.range K).map a) ρ

theorem chainFrame_apply {K c : Nat} (hc : c < K) (a ρ : Nat → V) :
    chainFrame K a ρ (K - 1 - c) = a c := by
  have hlen : ((List.range K).map a).length = K := by simp
  rw [chainFrame, consList_getD_of_lt _ _ _ (by omega), hlen,
    show K - 1 - (K - 1 - c) = c from by omega, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range hc]
  rfl

/-- **The premise of the recursor family's leaf** at a base frame `ρ`:
the `K` recursor types are formed at level `s`, the ι equations are
truth values and graded at every fitting tuple, and a CANDIDATE tuple
satisfies them.  The candidate is what the recursor model supplies
(the graph kit, `famCandG_hCand`);
everything else is read off the check's certificates. -/
structure BlockRecPre (V : Type uv) [SetTheory V] (s K : Nat) (RecTy : Nat → AnnotTerm)
    (eqs : List AnnotTerm) (ρ : Nat → V) : Prop where
  /-- The recursor types are sets of the chain's level, and graded. -/
  hTy : ∀ c, c < K → interp V ρ (RecTy c) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (RecTy c)
  /-- The ι equations are truth values and graded at every tuple typed
  at the recursor types. -/
  hEq : ∀ rs : List V, rs.length = K →
    (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
    ∀ e ∈ eqs, interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e
  /-- **The recursion theorem**: a tuple typed at the recursor types
  satisfying every ι equation. -/
  hCand : ∃ cand : Nat → V, (∀ c, c < K → cand c ∈ˢ interp V ρ (RecTy c)) ∧
    ∀ e ∈ eqs, (pt : V) ∈ˢ interp V (chainFrame K cand ρ) e

/-- **The leaf's facts**: there is ONE tuple `a` whose components are
the classes' leaves — typed at the recursor types (`mem_type`) and
graded — and which satisfies every ι equation. -/
theorem blockRecAV_facts {s K : Nat} {RecTy : Nat → AnnotTerm} {eqs : List AnnotTerm}
    {ρ : Nat → V} (h : BlockRecPre V s K RecTy eqs ρ) :
    ∃ a : Nat → V,
      (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c) ∧
        interp V ρ (blockRecAV s K RecTy eqs c) = a c ∧
        WellDenoted V ρ (blockRecAV s K RecTy eqs c)) ∧
      ∀ e ∈ eqs, (pt : V) ∈ˢ interp V (chainFrame K a ρ) e := by
  obtain ⟨cand, hcand, hcandEq⟩ := h.hCand
  exact blockRecAVI_facts s K RecTy eqs ρ h.hTy h.hEq cand hcand hcandEq

/-- **THE ι LAWS OF THE FAMILY**, extracted at the leaf: one tuple `a`,
its components the classes' leaves, and for every class `c` and
constructor `j` the equation
`rec_c x⃗ e⃗_j (C_j p⃗ f⃗) = Rb_{c,j}` at the ih values — the
`RecRuleLaw`-shaped statement the Model tier converts. -/
theorem blockRecAV_iota {s K : Nat} {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat}
    {pdoms : Nat → List AnnotTerm} {fdoms es : Nat → Nat → List AnnotTerm}
    {mk : Nat → Nat → AnnotTerm} {ihs : Nat → Nat → List AnnotTerm}
    {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}
    (h : BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ) :
    ∃ a : Nat → V,
      (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c) ∧
        interp V ρ (blockRecAV s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) c) = a c ∧
        WellDenoted V ρ
          (blockRecAV s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) c)) ∧
      ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
        xs.length = (pdoms c).length →
        SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
        (xs ++ (es c j ++ [mk c j]).map
            (interp V (consList (xs ++ fs) (chainFrame K a ρ)))).foldl SetTheory.app (a c)
          = interp V
              (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ))))
                (consList (xs ++ fs) (chainFrame K a ρ))) (Rb c j) := by
  obtain ⟨a, ha, haEq⟩ := blockRecAV_facts h
  refine ⟨a, ha, fun c hc j hj xs fs hxl hsp => ?_⟩
  exact iotaEqAV_law (chainFrame_apply hc a ρ) (haEq _ (mem_iotaEqsAV hc hj)) hxl hsp

/-! ## The guarded call's ih term: the curried λ-tower

A rule's `ih` opener for a recursive/reflexive/nested field `f_i` is
valued, in the design, at the CURRIED λ-tower over the field's
TELESCOPE (the ih's domain is the telescope, not the predecessor set)
of the guarded call `rec_{c'} x⃗ e⃗(a⃗) (f_i a⃗)` — the
very spine the check abstracted.  At the chain frame that call's head
is class `c'`'s component, so the tower is spellable here, and its
FOLD along a fitting telescope spine is the call's value. -/

/-! ## Two named obligations: one elimination level (D-d) and the residue (G1) -/

/-- **D-d, stated** (DESIGN v2 §3.2): the family eliminates at ONE
level.  The leaf is a Σ'-chain at a single `s` and the candidate is a
λ-tower at a single bit, so every class's binder data must carry the
SAME zeroness — which is what a common elimination level gives (the
kernel's elimination-level pin, `checkBlockRecElimPin`). -/
def OneElimLevel (ℓ K : Nat) (rds : Nat → List (Nat × Nat × AnnotTerm)) : Prop :=
  ∀ c, c < K → ∀ d ∈ rds c, (ℓ = 0 ↔ d.2.1 = 0)

/-- **G1's shape, stated**: what the Model tier proves about ONE rule's
RESIDUE at ONE frame — it is graded, and its value lands in the
target, at the frame `(x⃗, f⃗)` extended by the ih openers' VALUES.
The residue is recursor-free by construction, which is why
this is a statement about the CONSTRUCTORS' environment and not about
one holding the recursors.

The graph kit consumes exactly this: the target is the kit's bound
`B (tagged c ⟨ı⃗⟩ (C_j p⃗ f⃗))` and the fact IS `GraphRecKit.hst`.  The grading half is `hEq_iotaEqsAV_of`'s right
conjunct. -/
def ResidueOk (V : Type uv) [SetTheory V] (Rb : AnnotTerm) (ihvals : List V) (ρ' : Nat → V)
    (B : V) : Prop :=
  WellDenoted V (consList ihvals ρ') Rb ∧ interp V (consList ihvals ρ') Rb ∈ˢ B

/-! ## The premise's two halves, in the form their owners prove them -/

section Assemble

variable {s K : Nat} {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **The ι equations are graded** when every rule's binder data is
graded along the telescope and both its sides are graded at every
fitting spine — the Model tier's half (G1's `WellDenotedV` under
`CtxOk`, and the leaf's own grading for the left-hand side). -/
theorem hEq_iotaEqsAV_of
    (hwd : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j))) :
    ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e := by
  intro rs hlen hmem
  refine forall_iotaEqsAV fun c hc j hj => ⟨iotaEqAV_univZero, ?_⟩
  obtain ⟨hd, hb⟩ := hwd rs hlen hmem c hc j hj
  exact wd_iotaEqAV hd hb

/-- **The candidate's obligations, in the form the graph kit proves
them** (`famCandG_hCand`): a tuple typed at the
recursor types whose components satisfy every rule's ι law at every
fitting spine of the rule's prefix and the constructor's fields. -/
theorem hCand_iotaEqsAV_of (cand : Nat → V)
    (hty : ∀ c, c < K → cand c ∈ˢ interp V ρ (RecTy c))
    (hiota : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K cand ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (xs ++ (es c j ++ [mk c j]).map
          (interp V (consList (xs ++ fs) (chainFrame K cand ρ)))).foldl SetTheory.app (cand c)
        = interp V
            (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K cand ρ))))
              (consList (xs ++ fs) (chainFrame K cand ρ))) (Rb c j)) :
    ∃ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        (pt : V) ∈ˢ interp V (chainFrame K a ρ) e :=
  ⟨cand, hty, forall_iotaEqsAV fun c hc j hj =>
    pt_mem_iotaEqAV_of (chainFrame_apply hc cand ρ) (hiota c hc j hj)⟩

end Assemble

/-- `TowerWalkA` from the facts at every fitting spine. -/
theorem towerWalkA_of_spines_body {m : Nat} {C : AnnotTerm} {g : List V → (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V},
      (∀ ys, SpineFit ρ (ds.map (·.2.2)) ys →
        g (acc ++ ys) (consList ys ρ) ∈ˢ interp V (consList ys ρ) C ∧
          (m = 0 → interp V (consList ys ρ) C ∈ˢ (univZero : V))) →
      TowerWalkA m C g ρ acc ds
  | [], ρ, acc, h => by
    have h0 := h [] trivial
    rw [List.append_nil, consList_nil] at h0
    exact h0
  | d :: ds, ρ, acc, h => by
    intro a ha
    refine towerWalkA_of_spines_body fun ys hsp => ?_
    have := h (a :: ys) ⟨ha, hsp⟩
    rw [consList_cons] at this
    simpa using this


/-!
## The recursor family's candidate from the GRAPH kit

The recursor model is the graph route.  A checked recursor family is the selector of its GRAPH — the least
relation closed under its rules read as closure conditions over
DECODINGS of the majors (`GraphRecKit`, `SetModel/GraphRec.lean`) —
and the graph is functional by ONE induction over the majors plus
`huniq` (decodings equal, or the bound a subsingleton).  The family's
candidate is ONE λ-tower whose body is the kit's recursor, at EVERY
level — no regime split.

**Classes are the stream's recursors**: the
majors are tagged by the recursor class `c`, with the class's own
index sets and ORDINARY carriers per prefix spine (`GraphFamData`).

**At `ℓ = 0`** the tower is the point and so is every value of the
graph (its bound is a truth value), which is why `famCandG_fold` needs
no level split at its consumers: both sides are the point.

**What the Model tier proves** (`famCandG_hCand`): that a rule's spine
FITS the recursor's type (`hrule`); that the rule's own fields are a
DECODING of the constructed major (`hdec` — the rule reads the
constructor it is keyed by, at any sort); and that the kit's step at
that decoding, with the `ih`s read off the recursor over its
predecessors, IS the residue at the `ih` terms' values (`hst`).  The ι
law is then `GraphRecKit.rec_eq` at THAT decoding: no decoding is
ever chosen.
-/


open ConLeche.SetTheory


/-! ## The recursor's spine, decomposed

A fitting spine of `rec_c`'s type is `x⃗ ++ ı⃗ ++ [t]`: the rule prefix
(`rP c` binders — record-read, PER RECURSOR), the class's indices, the
major. -/

/-- The rule prefix of a spine. -/
def prefOf (rP : Nat) (ys : List V) : List V := ys.take rP

/-- The index values of a spine. -/
def idxOf (rP : Nat) (ys : List V) : List V := (ys.drop rP).dropLast

/-- The major of a spine. -/
noncomputable def majOf (ys : List V) : V := ys.reverse.headD pt

omit [SetTheory V] in
@[simp] theorem prefOf_split {rP : Nat} {xs is : List V} {t : V} (hx : xs.length = rP) :
    prefOf rP (xs ++ (is ++ [t])) = xs := by
  rw [prefOf, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

omit [SetTheory V] in
@[simp] theorem idxOf_split {rP : Nat} {xs is : List V} {t : V} (hx : xs.length = rP) :
    idxOf rP (xs ++ (is ++ [t])) = is := by
  rw [idxOf, List.drop_append_of_le_length (by omega),
    List.drop_of_length_le (by omega), List.nil_append, List.dropLast_concat]

@[simp] theorem majOf_split {xs is : List V} {t : V} :
    majOf (xs ++ (is ++ [t])) = t := by
  simp [majOf]

/-- **The recursion data of a recursor family over the graph kit**, at
the base frame `ρ`: per PREFIX SPINE a `GraphRecKit` over the tagged
union of the classes' ORDINARY carriers, with decodings in `R`, and the
two readings the recursors' TYPES fix. -/
structure GraphFamData (V : Type uv) [SetTheory V] (ℓ K : Nat) (rP : Nat → Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (concl : Nat → AnnotTerm) (ρ : Nat → V)
    (R : Type uv) where
  /-- The classes' index sets, at a prefix frame. -/
  Is : List V → Nat → V
  /-- The classes' ORDINARY carriers. -/
  Cr : List V → Nat → V
  /-- The index TUPLE of a class's index spine. -/
  tupOf : Nat → List V → V
  /-- The kit, one per prefix spine. -/
  kit : ∀ xs : List V, GraphRecKit ℓ (unionSet K (Is xs) (Cr xs)) R
  /-- A fitting spine of `rec_c`'s type is `x⃗ ++ ı⃗ ++ [t]`, a major of
  class `c`. -/
  hsplit : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (prefOf (rP c) ys).length = rP c ∧
    ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
    tupOf c (idxOf (rP c) ys) ∈ˢ Is (prefOf (rP c) ys) c ∧
    majOf ys ∈ˢ app (Cr (prefOf (rP c) ys) c) (tupOf c (idxOf (rP c) ys))
  /-- The conclusion reads to the kit's bound at the tagged major. -/
  hconcl : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (kit (prefOf (rP c) ys)).B (tagged c (tupOf c (idxOf (rP c) ys)) (majOf ys))
      = interp V (consList ys ρ) (concl c)

section Cand

variable {ℓ K : Nat} {rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {concl : Nat → AnnotTerm} {ρ : Nat → V} {R : Type uv}

/-- **The candidate at class `c`**: the λ-tower over the recursor
type's binder data whose body is the kit's recursor at the tagged
major the spine names. -/
noncomputable def famCandG (D : GraphFamData V ℓ K rP rds concl ρ R) (c : Nat) : V :=
  lamTowerA ℓ ρ [] (rds c) fun ys _ =>
    (D.kit (prefOf (rP c) ys)).recAt (tagged c (D.tupOf c (idxOf (rP c) ys)) (majOf ys))

/-- A fitting spine's tagged major is a major of the kit. -/
theorem GraphFamData.mem_union (D : GraphFamData V ℓ K rP rds concl ρ R) {c : Nat}
    (hc : c < K) {ys : List V} (hsp : SpineFit ρ ((rds c).map (·.2.2)) ys) :
    tagged c (D.tupOf c (idxOf (rP c) ys)) (majOf ys)
      ∈ˢ unionSet K (D.Is (prefOf (rP c) ys)) (D.Cr (prefOf (rP c) ys)) := by
  obtain ⟨-, -, hi, hx⟩ := D.hsplit c hc ys hsp
  exact tagged_mem_unionSet hc hi hx

/-- **`mem_type` of the candidate**, at every level: the kit's
recursor lies in its bound, which is the conclusion's reading; at
`ℓ = 0` that reading is a truth value because the bound is a set of
level `0`. -/
theorem famCandG_mem (D : GraphFamData V ℓ K rP rds concl ρ R) {c : Nat} (hc : c < K)
    (hbits : ∀ d ∈ rds c, (ℓ = 0 ↔ d.2.1 = 0)) :
    famCandG D c ∈ˢ interp V ρ (mkPisAV (rds c) (concl c)) := by
  refine lamTowerA_mem hbits (towerWalkA_of_spines_body fun ys hsp => ?_)
  have hu := D.mem_union hc hsp
  have hB := (D.kit (prefOf (rP c) ys)).hB _ hu
  rw [D.hconcl c hc ys hsp] at hB
  refine ⟨?_, fun h0 => ?_⟩
  · have hmem := (D.kit (prefOf (rP c) ys)).rec_mem_B hu
    rw [D.hconcl c hc ys hsp] at hmem
    simpa using hmem
  · subst h0
    rwa [univ_zero] at hB

/-- **The candidate folds to the kit's recursor** along a fitting spine
`x⃗ ++ ı⃗ ++ [t]` — at EVERY level.  Above `Prop` it is the tower's
fold; at `ℓ = 0` both sides are the point (the tower is `lamR 0 …`,
the recursor lies in a truth value). -/
theorem famCandG_fold (D : GraphFamData V ℓ K rP rds concl ρ R) {c : Nat} (hc : c < K)
    {xs is : List V} {t : V} (hx : xs.length = rP c)
    (hsp : SpineFit ρ ((rds c).map (·.2.2)) (xs ++ (is ++ [t]))) :
    (xs ++ (is ++ [t])).foldl SetTheory.app (famCandG D c)
      = (D.kit xs).recAt (tagged c (D.tupOf c is) t) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    have hu := D.mem_union hc hsp
    rw [prefOf_split hx, idxOf_split hx, majOf_split] at hu
    have hB := (D.kit xs).hB _ hu
    rw [univ_zero] at hB
    rw [eq_pt_of_mem_univZero hB ((D.kit xs).rec_mem_B hu)]
    obtain ⟨dd, ds, hrds⟩ : ∃ dd ds, rds c = dd :: ds := by
      cases h : rds c with
      | nil =>
        have hl := hsp.length_eq
        rw [h] at hl
        simp at hl
      | cons dd ds => exact ⟨dd, ds, rfl⟩
    rw [famCandG, hrds]
    show (xs ++ (is ++ [t])).foldl SetTheory.app (lamR 0 _ _) = _
    rw [lamR_zero]
    exact foldl_app_pt' _
  · rw [famCandG, lamTowerA_fold hℓ hsp]
    simp only [List.nil_append]
    rw [prefOf_split hx, idxOf_split hx, majOf_split]

variable {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm}

/-- **THE CANDIDATE, from the graph kit** — the ONE producer of
`BlockRecPre.hCand`, at every level.

* `hrule`: a rule's own spine (the prefix, the constructor's index
  expressions, the constructed major) FITS the recursor's type;
* `hdec`: the rule's fields, keyed by the rule, are a DECODING
  (`dOf`) of that major;
* `hst`: the kit's step at that decoding, the `ih`s read off the
  recursor over the decoding's predecessors, IS the residue at the
  `ih` terms' values.

The ι law is `GraphRecKit.rec_eq` at the rule's own decoding. -/
theorem famCandG_hCand (D : GraphFamData V ℓ K rP rds concl ρ R)
    (dOf : List V → Nat → Nat → List V → R)
    (hTy : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ K rds)
    (hpl : ∀ c, c < K → (pdoms c).length = rP c)
    (hrule : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCandG D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)) (mk c j)])))
    (hdec : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCandG D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (D.kit xs).Dec
        (tagged c
          (D.tupOf c ((es c j).map
            (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)))))
          (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)) (mk c j)))
        (dOf xs c j fs))
    (hst : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCandG D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (D.kit xs).st (dOf xs c j fs)
          (graph (fun v => (D.kit xs).recAt v) ((D.kit xs).pred (dOf xs c j fs)))
        = interp V
            (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ))))
              (consList (xs ++ fs) (chainFrame K (famCandG D) ρ))) (Rb c j)) :
    ∃ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        (pt : V) ∈ˢ interp V (chainFrame K a ρ) e := by
  refine hCand_iotaEqsAV_of (famCandG D) (fun c hc => ?_) fun c hc j hj xs fs hxl hsp => ?_
  · rw [hTy c hc]
    exact famCandG_mem D hc (hbits c hc)
  · have hxr : xs.length = rP c := by rw [hxl, hpl c hc]
    have hfit := hrule c hc j hj xs fs hxl hsp
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [famCandG_fold D hc hxr hfit]
    have hu := D.mem_union hc hfit
    rw [prefOf_split hxr, idxOf_split hxr, majOf_split] at hu
    rw [(D.kit xs).rec_eq hu (hdec c hc j hj xs fs hxl hsp)]
    exact hst c hc j hj xs fs hxl hsp

end Cand

end ConLeche.Semantics
