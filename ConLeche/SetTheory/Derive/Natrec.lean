module

public import ConLeche.SetTheory.Derive.Omega
public import ConLeche.SetTheory.Derive.Graphs

@[expose] public section

/-!
# Internal Dedekind recursion on `ω`

Replaces meta-level `Nat` iteration (`natIter`) with internal
first-order Dedekind recursion via finite attempt graphs `IsAttempt`
over `ω`, using `omega_ind` and the ordinal laws from `Derive/Omega.lean`.

* `omegaRec z step hstep n hn` is proof-carrying and zero-junk on
  `n ∈ˢ ω`, valid for any `DefFun 2` step function `step`.
* `natrec z s n` specializes `omegaRec` to `step k ih := app (app s k) ih`
  via `uniqueChoice` (returning `empty` off `ω`, matching total `app`).
  Both `omegaRec_apply` and `DefFun.natrec_apply` provide full `DefFun`
  closure.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- A Dedekind attempt graph `g` for recursion from `z` along `step`
up to `n ∈ˢ ω` (domain `vsucc n`). -/
def IsAttempt (z : V) (step : V → V → V) (n g : V) : Prop :=
  (∀ p, p ∈ˢ g → ∃ k y, k ∈ˢ vsucc n ∧ p = kpair k y) ∧
  (∀ k, k ∈ˢ vsucc n → ExistsUnique fun y => kpair k y ∈ˢ g) ∧
  kpair empty z ∈ˢ g ∧
  ∀ k y, vsucc k ∈ˢ vsucc n → kpair k y ∈ˢ g → kpair (vsucc k) (step k y) ∈ˢ g

theorem defRel_isAttempt_param {k : Nat}
    {Z N G : (Fin k → V) → V} {S : (Fin (k + 2) → V) → V}
    (hZ : DefFun k Z) (hS : DefFun (k + 2) S) (hN : DefFun k N) (hG : DefFun k G) :
    DefRel k fun env =>
      IsAttempt (Z env) (fun a b => S (fcons a (fcons b env))) (N env) (G env) := by
  unfold IsAttempt
  refine DefRel.and ?_ (DefRel.and ?_ (DefRel.and ?_ ?_))
  · refine DefRel.forall_curry (DefRel.imp
      (DefRel.mem_apply (DefFun.proj 0) hG.weaken)
      (DefRel.exists_curry (DefRel.exists_curry (DefRel.and ?_ ?_))))
    · exact DefRel.mem_apply (DefFun.proj 1) (DefFun.vsucc_apply hN.weaken.weaken.weaken)
    · exact DefRel.eq_apply (DefFun.proj 2) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))
  · refine DefRel.forall_curry (DefRel.imp
      (DefRel.mem_apply (DefFun.proj 0) (DefFun.vsucc_apply hN.weaken))
      (DefRel.existsUnique_curry ?_))
    exact DefRel.mem_apply (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)) hG.weaken.weaken
  · exact DefRel.mem_apply (DefFun.kpair_apply DefFun.empty hZ) hG
  · refine DefRel.forall_curry (DefRel.forall_curry (DefRel.imp ?_ (DefRel.imp ?_ ?_)))
    · exact DefRel.mem_apply (DefFun.vsucc_apply (DefFun.proj 1))
        (DefFun.vsucc_apply hN.weaken.weaken)
    · exact DefRel.mem_apply (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)) hG.weaken.weaken
    · have hS' : DefFun (k + 2) fun w => S (fcons (w 1) (fcons (w 0) (ftail (ftail w)))) := by
        let re : Fin (k + 2) → Fin (k + 2)
          | ⟨0, _⟩ => 1
          | ⟨1, _⟩ => 0
          | ⟨i + 2, hi⟩ => ⟨i + 2, hi⟩
        exact (hS.reIndex re).congr fun w => by
          congr 1
          funext ⟨j, hj⟩
          match j with
          | 0 => rfl
          | 1 => rfl
          | _ + 2 => rfl
      exact DefRel.mem_apply (DefFun.kpair_apply (DefFun.vsucc_apply (DefFun.proj 1)) hS')
        hG.weaken.weaken

theorem defRel_isAttempt {step : V → V → V}
    (hstep : DefFun 2 fun v => step (v 0) (v 1)) (z : V) :
    DefRel 2 fun v => IsAttempt z step (v 0) (v 1) := by
  have hS : DefFun 4 fun w => step (w 0) (w 1) :=
    hstep.reIndex (fun i => match i with | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1)
  exact (defRel_isAttempt_param (Z := fun _ => z) (N := fun v => v 0) (G := fun v => v 1)
    (DefFun.const z) hS (DefFun.proj 0) (DefFun.proj 1)).congr fun _ => Iff.rfl

private theorem attempt_empty (z : V) (step : V → V → V) :
    ExistsUnique fun g => IsAttempt z step empty g := by
  let g₀ := sing (kpair empty z)
  have h0 : IsAttempt z step empty g₀ := by
    refine ⟨?_, ?_, mem_sing.mpr rfl, ?_⟩
    · intro p hp
      rw [mem_sing.mp hp]
      exact ⟨empty, z, self_mem_vsucc empty, rfl⟩
    · intro k hk
      rcases mem_vsucc.mp hk with hk0 | rfl
      · exact absurd hk0 (not_mem_empty k)
      · refine ⟨z, mem_sing.mpr rfl, ?_⟩
        intro y hy
        exact (kpair_inj (mem_sing.mp hy)).2
    · intro k _ hk _
      rcases mem_vsucc.mp hk with hk0 | hk0
      · exact absurd hk0 (not_mem_empty _)
      · exact absurd hk0 (vsucc_ne_empty k)
  refine ⟨g₀, h0, fun g hg => ext fun p => ?_⟩
  rw [mem_sing]
  constructor
  · intro hp
    obtain ⟨k, y, hk, rfl⟩ := hg.1 p hp
    rcases mem_vsucc.mp hk with hk0 | rfl
    · exact absurd hk0 (not_mem_empty k)
    · have hy : y = z := (hg.2.1 empty (self_mem_vsucc empty)).unique hp hg.2.2.1
      rw [hy]
  · rintro rfl
    exact hg.2.2.1

private theorem attempt_succ (z : V) (step : V → V → V) {n : V}
    (hn : n ∈ˢ (omega : V)) (ih : ExistsUnique fun g => IsAttempt z step n g) :
    ExistsUnique fun g => IsAttempt z step (vsucc n) g := by
  obtain ⟨gₙ, hgₙ, huniqₙ⟩ := ih
  obtain ⟨yₙ, hyₙ, hyₙ_uniq⟩ := hgₙ.2.1 n (self_mem_vsucc n)
  let g' := binUnion gₙ (sing (kpair (vsucc n) (step n yₙ)))
  have hnot : ¬ (vsucc n : V) ∈ˢ vsucc n := not_mem_self _
  have hg'_attempt : IsAttempt z step (vsucc n) g' := by
    refine ⟨?_, ?_, mem_binUnion.mpr (Or.inl hgₙ.2.2.1), ?_⟩
    · intro p hp
      rcases mem_binUnion.mp hp with hp | hp
      · obtain ⟨k, y, hk, rfl⟩ := hgₙ.1 p hp
        exact ⟨k, y, mem_vsucc.mpr (Or.inl hk), rfl⟩
      · rw [mem_sing.mp hp]
        exact ⟨vsucc n, step n yₙ, self_mem_vsucc (vsucc n), rfl⟩
    · intro k hk
      rcases mem_vsucc.mp hk with hkn | rfl
      · obtain ⟨y, hy, hyu⟩ := hgₙ.2.1 k hkn
        refine ⟨y, mem_binUnion.mpr (Or.inl hy), ?_⟩
        intro y' hy'
        rcases mem_binUnion.mp hy' with hy' | hy'
        · exact hyu y' hy'
        · obtain ⟨hkn', _⟩ := kpair_inj (mem_sing.mp hy')
          exact absurd (hkn' ▸ hkn) hnot
      · refine ⟨step n yₙ, mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl)), ?_⟩
        intro y' hy'
        rcases mem_binUnion.mp hy' with hy' | hy'
        · obtain ⟨k, y, hk, hkp⟩ := hgₙ.1 _ hy'
          obtain ⟨hkn', _⟩ := kpair_inj hkp
          exact absurd (hkn' ▸ hk) hnot
        · exact (kpair_inj (mem_sing.mp hy')).2
    · intro k y hk hky
      rcases mem_vsucc.mp hk with hk' | hkeq
      · have hkn : k ∈ˢ n := (vsucc_mem_iff_of_mem_omega hn).mp hk'
        have hkv : k ∈ˢ vsucc n := mem_vsucc.mpr (Or.inl hkn)
        rcases mem_binUnion.mp hky with hky' | hky'
        · exact mem_binUnion.mpr (Or.inl (hgₙ.2.2.2 k y hk' hky'))
        · obtain ⟨hkeq, _⟩ := kpair_inj (mem_sing.mp hky')
          exact absurd (hkeq ▸ hkv) hnot
      · obtain rfl : k = n := vsucc_inj hkeq
        have hnv : k ∈ˢ vsucc k := self_mem_vsucc k
        have hkyₙ : kpair k y ∈ˢ gₙ := by
          rcases mem_binUnion.mp hky with hky' | hky'
          · exact hky'
          · obtain ⟨hkeq', _⟩ := kpair_inj (mem_sing.mp hky')
            exact absurd (hkeq' ▸ hnv) hnot
        obtain rfl : y = yₙ := hyₙ_uniq y hkyₙ
        exact mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl))
  refine ⟨g', hg'_attempt, fun h' hh' => ?_⟩
  have hsep : HasSep h' (fun p => ∃ k y, k ∈ˢ vsucc n ∧ p = kpair k y) :=
    hasSep_of_def (by fo_def [DefFun.kpair_apply])
  let h := sep h' (fun p => ∃ k y, k ∈ˢ vsucc n ∧ p = kpair k y) hsep
  have hh_attempt : IsAttempt z step n h := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro p hp
      exact (mem_sep.mp hp).2
    · intro k hk
      obtain ⟨y, hy, hyu⟩ := hh'.2.1 k (mem_vsucc.mpr (Or.inl hk))
      refine ⟨y, mem_sep.mpr ⟨hy, k, y, hk, rfl⟩, ?_⟩
      intro y' hy'
      exact hyu y' (mem_sep.mp hy').1
    · exact mem_sep.mpr ⟨hh'.2.2.1, empty, z, empty_mem_vsucc_of_mem_omega hn, rfl⟩
    · intro k y hk hky
      have hk_in : k ∈ˢ vsucc n := by
        have hkn := (vsucc_mem_iff_of_mem_omega hn).mp hk
        exact mem_vsucc.mpr (Or.inl hkn)
      have hstep' := hh'.2.2.2 k y (mem_vsucc.mpr (Or.inl hk)) (mem_sep.mp hky).1
      exact mem_sep.mpr ⟨hstep', vsucc k, step k y, hk, rfl⟩
  have heq_n : h = gₙ := huniqₙ h hh_attempt
  apply ext fun p => ?_
  constructor
  · intro hp
    obtain ⟨k, y, hk, rfl⟩ := hh'.1 p hp
    rcases mem_vsucc.mp hk with hk' | rfl
    · have hph : kpair k y ∈ˢ h := mem_sep.mpr ⟨hp, k, y, hk', rfl⟩
      rw [heq_n] at hph
      exact mem_binUnion.mpr (Or.inl hph)
    · have hyₙ_h' : kpair n yₙ ∈ˢ h' := by
        have : kpair n yₙ ∈ˢ h := heq_n ▸ hyₙ
        exact (mem_sep.mp this).1
      have hstep_h' : kpair (vsucc n) (step n yₙ) ∈ˢ h' :=
        hh'.2.2.2 n yₙ (self_mem_vsucc (vsucc n)) hyₙ_h'
      have hy_eq : y = step n yₙ :=
        (hh'.2.1 (vsucc n) (self_mem_vsucc (vsucc n))).unique hp hstep_h'
      rw [hy_eq]
      exact mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl))
  · intro hp
    rcases mem_binUnion.mp hp with hp | hp
    · rw [← heq_n] at hp
      exact (mem_sep.mp hp).1
    · rw [mem_sing.mp hp]
      have hyₙ_h' : kpair n yₙ ∈ˢ h' := by
        have : kpair n yₙ ∈ˢ h := heq_n ▸ hyₙ
        exact (mem_sep.mp this).1
      exact hh'.2.2.2 n yₙ (self_mem_vsucc (vsucc n)) hyₙ_h'

/-- Every `n ∈ˢ ω` admits a unique Dedekind attempt graph for any
`DefFun 2` step function. -/
theorem existsUnique_attempt (z : V) (step : V → V → V)
    (hstep : DefFun 2 fun v => step (v 0) (v 1))
    {n : V} (hn : n ∈ˢ (omega : V)) :
    ExistsUnique fun g => IsAttempt z step n g := by
  have hdef : DefPred (fun n => ExistsUnique fun g => IsAttempt z step n g) :=
    DefRel.existsUnique_curry
      ((defRel_isAttempt hstep z).reIndex (fun i => match i with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0))
  exact omega_ind_of_def (DefPredOn.of_defPred hdef)
    (attempt_empty z step) (fun _ hm ih => attempt_succ z step hm ih) n hn

private theorem existsUnique_attempt_val (z : V) (step : V → V → V)
    (hstep : DefFun 2 fun v => step (v 0) (v 1))
    {n : V} (hn : n ∈ˢ (omega : V)) :
    ExistsUnique fun y => ∃ g, IsAttempt z step n g ∧ kpair n y ∈ˢ g := by
  obtain ⟨g, hg, hg_uniq⟩ := existsUnique_attempt z step hstep hn
  obtain ⟨y, hy, hy_uniq⟩ := hg.2.1 n (self_mem_vsucc n)
  refine ⟨y, ⟨g, hg, hy⟩, ?_⟩
  rintro y' ⟨g', hg', hy'⟩
  obtain rfl : g' = g := hg_uniq g' hg'
  exact hy_uniq y' hy'

open Classical in
/-- Proof-carrying, zero-junk internal recursion on `ω` for any
first-order definable step function `step : V → V → V`. -/
noncomputable def omegaRec (z : V) (step : V → V → V)
    (_hstep : DefFun 2 fun v => step (v 0) (v 1))
    (n : V) (_hn : n ∈ˢ (omega : V)) : V :=
  if h : ExistsUnique fun y => ∃ g, IsAttempt z step n g ∧ kpair n y ∈ˢ g
  then Classical.choose h else empty

private theorem omegaRec_spec {z : V} {step : V → V → V}
    (hstep : DefFun 2 fun v => step (v 0) (v 1))
    {n : V} (hn : n ∈ˢ (omega : V)) :
    ∃ g, IsAttempt z step n g ∧ kpair n (omegaRec z step hstep n hn) ∈ˢ g := by
  unfold omegaRec
  have hex := existsUnique_attempt_val z step hstep hn
  rw [dite_eq_left hex]
  exact (Classical.choose_spec hex).1

theorem omegaRec_eq_of_attempt {z : V} {step : V → V → V}
    (hstep : DefFun 2 fun v => step (v 0) (v 1))
    {n g y : V} (hn : n ∈ˢ (omega : V))
    (hg : IsAttempt z step n g) (hy : kpair n y ∈ˢ g) :
    omegaRec z step hstep n hn = y := by
  obtain ⟨g', hg', hy'⟩ := omegaRec_spec hstep hn
  have heq := (existsUnique_attempt z step hstep hn).unique hg' hg
  subst heq
  exact (hg'.2.1 n (self_mem_vsucc n)).unique hy' hy

theorem omegaRec_congr {z : V} {step : V → V → V}
    (hstep : DefFun 2 fun v => step (v 0) (v 1))
    {n : V} (hn₁ hn₂ : n ∈ˢ (omega : V)) :
    omegaRec z step hstep n hn₁ = omegaRec z step hstep n hn₂ := rfl

theorem omegaRec_empty (z : V) (step : V → V → V)
    (hstep : DefFun 2 fun v => step (v 0) (v 1)) :
    omegaRec z step hstep empty empty_mem_omega = z := by
  obtain ⟨g, hg, hy⟩ := omegaRec_spec hstep empty_mem_omega
  exact (hg.2.1 empty (self_mem_vsucc empty)).unique hy hg.2.2.1

theorem omegaRec_vsucc (z : V) (step : V → V → V)
    (hstep : DefFun 2 fun v => step (v 0) (v 1))
    {n : V} (hn : n ∈ˢ (omega : V)) :
    omegaRec z step hstep (vsucc n) (vsucc_mem_omega hn) =
      step n (omegaRec z step hstep n hn) := by
  obtain ⟨g, hg, hy⟩ := omegaRec_spec hstep (vsucc_mem_omega hn)
  have hsep : HasSep g (fun p => ∃ k y, k ∈ˢ vsucc n ∧ p = kpair k y) :=
    hasSep_of_defPred
      (DefRel.exists_curry (DefRel.exists_curry (DefRel.and
        (DefRel.mem_apply (DefFun.proj 1) (DefFun.const (vsucc n)))
        (DefRel.eq_apply (DefFun.proj 2) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))))))
  let gₙ := sep g (fun p => ∃ k y, k ∈ˢ vsucc n ∧ p = kpair k y) hsep
  have hgₙ : IsAttempt z step n gₙ := by
    refine ⟨fun _ hp => (mem_sep.mp hp).2, ?_, ?_, ?_⟩
    · intro k hk
      obtain ⟨y', hy', hyu'⟩ := hg.2.1 k (mem_vsucc.mpr (Or.inl hk))
      refine ⟨y', mem_sep.mpr ⟨hy', k, y', hk, rfl⟩, ?_⟩
      intro y'' hy''
      exact hyu' y'' (mem_sep.mp hy'').1
    · exact mem_sep.mpr ⟨hg.2.2.1, empty, z, empty_mem_vsucc_of_mem_omega hn, rfl⟩
    · intro k y' hk hky'
      have hstep' := hg.2.2.2 k y' (mem_vsucc.mpr (Or.inl hk)) (mem_sep.mp hky').1
      exact mem_sep.mpr ⟨hstep', vsucc k, step k y', hk, rfl⟩
  let yₙ := omegaRec z step hstep n hn
  obtain ⟨gₙ', hgₙ', hyₙ'⟩ := omegaRec_spec hstep hn
  have heq : gₙ = gₙ' := (existsUnique_attempt z step hstep hn).unique hgₙ hgₙ'
  have hmem_n : kpair n yₙ ∈ˢ g := by
    have : kpair n yₙ ∈ˢ gₙ := heq ▸ hyₙ'
    exact (mem_sep.mp this).1
  have hmem_succ : kpair (vsucc n) (step n yₙ) ∈ˢ g :=
    hg.2.2.2 n yₙ (self_mem_vsucc (vsucc n)) hmem_n
  exact (hg.2.1 (vsucc n) (self_mem_vsucc (vsucc n))).unique hy hmem_succ

/-- Internal induction principle for `omegaRec`. -/
theorem omegaRec_ind {z : V} {step : V → V → V}
    (hstep : DefFun 2 fun v => step (v 0) (v 1))
    {P : V → V → Prop}
    (hSep : HasSep (omega : V) fun n =>
      ∃ y, (∃ g, IsAttempt z step n g ∧ kpair n y ∈ˢ g) ∧ P n y)
    (hz : P empty z)
    (hs : ∀ k, k ∈ˢ (omega : V) → ∀ ih, P k ih → P (vsucc k) (step k ih))
    {n : V} (hn : n ∈ˢ (omega : V)) :
    P n (omegaRec z step hstep n hn) := by
  have hall : ∀ n, n ∈ˢ (omega : V) →
      ∃ y, (∃ g, IsAttempt z step n g ∧ kpair n y ∈ˢ g) ∧ P n y := by
    refine omega_ind hSep ?_ ?_
    · obtain ⟨g₀, hg₀, hy₀⟩ := omegaRec_spec (z := z) hstep empty_mem_omega
      rw [omegaRec_empty z step hstep] at hy₀
      exact ⟨z, ⟨g₀, hg₀, hy₀⟩, hz⟩
    · intro k hk ⟨y, ⟨gk, hgk, hyk⟩, hPk⟩
      have hy_eq : omegaRec z step hstep k hk = y :=
        omegaRec_eq_of_attempt hstep hk hgk hyk
      obtain ⟨g₁, hg₁, hy₁⟩ := omegaRec_spec (z := z) hstep (vsucc_mem_omega hk)
      rw [omegaRec_vsucc z step hstep hk, hy_eq] at hy₁
      exact ⟨step k y, ⟨g₁, hg₁, hy₁⟩, hs k hk y hPk⟩
  obtain ⟨y, ⟨g, hg, hy⟩, hP⟩ := hall n hn
  rwa [omegaRec_eq_of_attempt hstep hn hg hy]

theorem omegaRec_ind_of_def {z : V} {step : V → V → V}
    (hstep : DefFun 2 fun v => step (v 0) (v 1))
    {P : V → V → Prop} (hP : DefRel 2 fun v => P (v 0) (v 1))
    (hz : P empty z)
    (hs : ∀ k, k ∈ˢ (omega : V) → ∀ ih, P k ih → P (vsucc k) (step k ih))
    {n : V} (hn : n ∈ˢ (omega : V)) :
    P n (omegaRec z step hstep n hn) := by
  have hSep : HasSep (omega : V) fun n =>
      ∃ y, (∃ g, IsAttempt z step n g ∧ kpair n y ∈ˢ g) ∧ P n y := by
    apply hasSep_of_defPred
    refine DefRel.exists_curry (DefRel.and (DefRel.exists_curry (DefRel.and ?_ ?_)) ?_)
    · exact (defRel_isAttempt hstep z).reIndex
        (fun i => match i with | ⟨0, _⟩ => 2 | ⟨1, _⟩ => 0)
    · exact DefRel.mem_apply
        (DefFun.kpair_apply (DefFun.proj 2) (DefFun.proj 1)) (DefFun.proj 0)
    · exact hP.reIndex (fun i => match i with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0)
  exact omegaRec_ind hstep hSep hz hs hn

/-- `DefFun` closure for `omegaRec` (with varying `Z` and `N`, and
fixed `DefFun 2` step function `step`). -/
theorem DefFun.omegaRec_apply {k : Nat}
    {Z N : (Fin k → V) → V}
    {step : V → V → V} (hstep : DefFun 2 fun v => step (v 0) (v 1))
    (hZ : DefFun k Z) (hN : DefFun k N)
    (hmem : ∀ env, N env ∈ˢ (omega : V)) :
    DefFun k fun env => omegaRec (Z env) step hstep (N env) (hmem env) := by
  have hS : DefFun ((k + 2) + 2) fun w => step (w 0) (w 1) :=
    hstep.reIndex (fun i => match i with | ⟨0, _⟩ => 0 | ⟨1, _⟩ => 1)
  have hAtt := defRel_isAttempt_param
    (Z := fun w => Z (ftail (ftail w)))
    (S := fun w => step (w 0) (w 1))
    (N := fun w => N (ftail (ftail w)))
    (G := fun w => w 0)
    hZ.weaken.weaken hS hN.weaken.weaken (DefFun.proj 0)
  have hR : DefRel (k + 1) fun v =>
      ∃ g, IsAttempt (Z (ftail v)) step (N (ftail v)) g ∧ kpair (N (ftail v)) (v 0) ∈ˢ g :=
    DefRel.exists_curry (DefRel.and hAtt
      (DefRel.mem_apply (DefFun.kpair_apply hN.weaken.weaken (DefFun.proj 1)) (DefFun.proj 0)))
  exact (DefFun.uniqueChoice_curry hR).congr fun env => by
    open Classical in
    unfold omegaRec
    rfl

attribute [irreducible] omegaRec

/-! ### Interface `natrec` specialized to curried `app` -/

open Classical in
/-- Set-theoretic recursion on `ω` via Dedekind attempt graphs,
specialized to the curried set-level step `k ↦ ih ↦ app (app s k) ih`.
Returns `empty` off `ω` (matching total `app`). -/
noncomputable def natrec (z s n : V) : V :=
  if h : ExistsUnique fun y => ∃ g, IsAttempt z (fun k ih => app (app s k) ih) n g ∧ kpair n y ∈ˢ g
  then Classical.choose h else empty

theorem step_app_defFun (s : V) :
    DefFun 2 fun v => app (app s (v 0)) (v 1) :=
  DefFun.app_apply (DefFun.app_apply (DefFun.const s) (DefFun.proj 0)) (DefFun.proj 1)

open Classical in
theorem natrec_eq_omegaRec (z s : V) {n : V} (hn : n ∈ˢ (omega : V)) :
    natrec z s n = omegaRec z (fun k ih => app (app s k) ih) (step_app_defFun s) n hn := by
  unfold natrec omegaRec
  rfl

theorem natrec_empty (z s : V) : natrec z s empty = z := by
  rw [natrec_eq_omegaRec z s empty_mem_omega, omegaRec_empty]

theorem natrec_vsucc (z s : V) {n : V} (hn : n ∈ˢ (omega : V)) :
    natrec z s (vsucc n) = app (app s n) (natrec z s n) := by
  rw [natrec_eq_omegaRec z s (vsucc_mem_omega hn),
      natrec_eq_omegaRec z s hn,
      omegaRec_vsucc]

/-- The recursion theorem with typing: the motive `M` is applied as a
set-theoretic function. -/
theorem natrec_mem_vsucc {M z s n : V}
    (hz : z ∈ˢ app M empty)
    (hs : ∀ k, k ∈ˢ (omega : V) → ∀ ih, ih ∈ˢ app M k →
      app (app s k) ih ∈ˢ app M (vsucc k))
    (hn : n ∈ˢ (omega : V)) : natrec z s n ∈ˢ app M n := by
  rw [natrec_eq_omegaRec z s hn]
  refine omegaRec_ind_of_def (step_app_defFun s)
    (P := fun k y => y ∈ˢ app M k)
    (DefRel.mem_apply (DefFun.proj 1) (DefFun.app_apply (DefFun.const M) (DefFun.proj 0)))
    hz hs hn

theorem DefFun.natrec_apply {k : Nat} {Z S N : (Fin k → V) → V}
    (hZ : DefFun k Z) (hS : DefFun k S) (hN : DefFun k N) :
    DefFun k fun env => natrec (Z env) (S env) (N env) := by
  unfold natrec
  have hS_step : DefFun ((k + 2) + 2) fun u =>
      app (app (S (ftail (ftail (ftail (ftail u))))) (u 0)) (u 1) :=
    DefFun.app_apply
      (DefFun.app_apply hS.weaken.weaken.weaken.weaken (DefFun.proj 0))
      (DefFun.proj 1)
  have hAtt := defRel_isAttempt_param
    (Z := fun w => Z (ftail (ftail w)))
    (S := fun u => app (app (S (ftail (ftail (ftail (ftail u))))) (u 0)) (u 1))
    (N := fun w => N (ftail (ftail w)))
    (G := fun w => w 0)
    hZ.weaken.weaken hS_step hN.weaken.weaken (DefFun.proj 0)
  have hR : DefRel (k + 1) fun v =>
      ∃ g, IsAttempt (Z (ftail v)) (fun a b => app (app (S (ftail v)) a) b) (N (ftail v)) g ∧
        kpair (N (ftail v)) (v 0) ∈ˢ g :=
    DefRel.exists_curry (DefRel.and hAtt
      (DefRel.mem_apply (DefFun.kpair_apply hN.weaken.weaken (DefFun.proj 1)) (DefFun.proj 0)))
  exact DefFun.uniqueChoice_curry hR

/- Opaque interface operator (see `Derive/Empty.lean`). -/
attribute [irreducible] natrec

end ConLeche.SetTheory
