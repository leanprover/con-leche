module

public import ConLeche.Model.Inductives.BlockRecLaw
public import ConLeche.Model.Inductives.BlockRecAssembly
import ConLeche.Model.Inductives.FixLeafOk
import ConLeche.Model.Annot.BitLevels
import ConLeche.Verify.Inductives.BlockRecInv

public section

/-!
# The recursor family's LEAF: its structural facts, and the rule data
(task #315, M5, model half — lane RM8)

Two things live here, and they are entangled through the equation
list `eqs`:

* **item C** — the five facts `blockRecStaged_of`
  (`Model/Inductives/BlockStageRec.lean`) asks of the stage's
  VALUATION, at the block route's leaf
  `blockRecAV s K RecTy eqs c` (`Semantics/Tower/BlockRecI.lean`):
  the erasure is closed, lifting is a no-op, the leaf depends on `ψ`
  only through its inputs, it is `WellDenoted` and it is
  `AnnotValid`.  Four of the five are a battery over the leaf's own
  spelling — `projChainAV c (choice (Σ' r⃗ : ⟨RecTy⃗⟩, ⋀ eqs) prf)` —
  and `SigChainI`'s laws; the fifth (`WellDenoted`) is
  `blockRecAV_facts` at the family premise, one line.

  Each of the two syntactic facts (closed, valid) reduces to the SAME
  two obligations about the family's inputs: the `K` recursor types,
  and every ι equation AT THE CHAIN FRAME (under the `K` Σ'
  binders).  The equations' half is then discharged, once, at the
  shape the design uses — `iotaEqAV`.

* **item A** — `BlockRuleDataAt` (`Model/Inductives/BlockRecLaw.lean`)
  at a stored rule.
-/

namespace ConLeche.Model

open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo RecRule BlockShape
  consBlockRecs)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-! ## C.1 The leaf's ERASURE is closed

`blockRecAV s K RecTy eqs c` is `projChainAV c` of
`choice.{s} (sigChainAV s (blockTsAV K RecTy) (andChainAV eqs)) prf`,
so its bound is the chain's: the `K` types are closed (each sits under
the `mm` earlier Σ' binders, and a closed type's lift is itself) and
the conjunction of the equations is bounded by `K`. -/

omit [SetTheory V] in
theorem bvarsBelow_projChainAV : ∀ (i : Nat) {e : AnnotTerm} {n : Nat},
    Term.bvarsBelow n e.erase → Term.bvarsBelow n (projChainAV i e).erase
  | 0, _, _, h => h
  | i + 1, e, _, h => bvarsBelow_projChainAV i (e := .snd e) h

omit [SetTheory V] in
theorem bvarsBelow_andAV {P Q : AnnotTerm} {n : Nat}
    (hP : Term.bvarsBelow n P.erase) (hQ : Term.bvarsBelow n Q.erase) :
    Term.bvarsBelow n (andAV P Q).erase := by
  refine ⟨⟨trivial, hP⟩, hP, ?_⟩
  rw [AnnotTerm.erase_liftN]
  exact VExprAux.bvarsBelow_liftN 1 Q.erase n 0 hQ

omit [SetTheory V] in
theorem bvarsBelow_andChainAV : ∀ {eqs : List AnnotTerm} {n : Nat},
    (∀ e ∈ eqs, Term.bvarsBelow n e.erase) → Term.bvarsBelow n (andChainAV eqs).erase
  | [], _, _ => trivial
  | e :: _, _, h => bvarsBelow_andAV (h e (.head _))
      (bvarsBelow_andChainAV fun e' he' => h e' (.tail _ he'))

omit [SetTheory V] in
theorem bvarsBelow_sigAV {s : Nat} {T rest : AnnotTerm} {n : Nat}
    (hT : Term.bvarsBelow n T.erase) (hr : Term.bvarsBelow (n + 1) rest.erase) :
    Term.bvarsBelow n (sigAV s T rest).erase := ⟨⟨trivial, hT⟩, hT, hr⟩

omit [SetTheory V] in
/-- A Σ'-chain over CLOSED component types is bounded wherever its
body is, `Ts.length` binders down. -/
theorem bvarsBelow_sigChainAV {s : Nat} {Q : AnnotTerm} :
    ∀ {Ts : List AnnotTerm} {n : Nat}, (∀ T ∈ Ts, Term.Closed T.erase) →
      Term.bvarsBelow (n + Ts.length) Q.erase →
      Term.bvarsBelow n (sigChainAV s Ts Q).erase
  | [], n, _, hQ => by
    show Term.bvarsBelow n Q.erase
    rw [List.length_nil] at hQ
    exact Term.bvarsBelow.mono (by omega) hQ
  | T :: Ts, n, hT, hQ =>
    bvarsBelow_sigAV (Term.bvarsBelow.mono (Nat.zero_le n) (hT T (.head _)))
      (bvarsBelow_sigChainAV (fun T' hT' => hT T' (.tail _ hT'))
        (by
          have h : n + 1 + Ts.length = n + (T :: Ts).length := by
            rw [List.length_cons]; omega
          rw [h]; exact hQ))

omit [SetTheory V] in
/-- The `K` lifted component types are closed when the types are. -/
theorem closed_blockTsAV {K : Nat} {RecTy : Nat → AnnotTerm}
    (hT : ∀ c, c < K → Term.Closed (RecTy c).erase) :
    ∀ T ∈ blockTsAV K RecTy, Term.Closed T.erase := by
  intro T hT'
  simp only [blockTsAV] at hT'
  obtain ⟨mm, hmm, rfl⟩ := List.mem_map.mp hT'
  rw [AnnotTerm.erase_liftN, Term.liftN_eq_self (hT mm (List.mem_range.mp hmm)) mm]
  exact hT mm (List.mem_range.mp hmm)

omit [SetTheory V] in
/-- **C-1: the leaf's erasure is closed** — from the `K` recursor
types' closedness and the ι equations' bound at the chain frame. -/
theorem closed_blockRecAV {s K : Nat} {RecTy : Nat → AnnotTerm} {eqs : List AnnotTerm} {c : Nat}
    (hT : ∀ c', c' < K → Term.Closed (RecTy c').erase)
    (heq : ∀ e ∈ eqs, Term.bvarsBelow K e.erase) :
    Term.Closed (blockRecAV s K RecTy eqs c).erase := by
  show Term.bvarsBelow 0
    (projChainAV c (selChainAV s (blockTsAV K RecTy) (andChainAV eqs))).erase
  refine bvarsBelow_projChainAV c
    (e := selChainAV s (blockTsAV K RecTy) (andChainAV eqs)) ?_
  show Term.bvarsBelow 0 (AnnotTerm.erase
    (.app (.app (.const .choice [s]) (sigChainAV s (blockTsAV K RecTy) (andChainAV eqs)))
      .prf))
  refine ⟨⟨trivial, ?_⟩, trivial⟩
  refine bvarsBelow_sigChainAV (n := 0) (closed_blockTsAV hT) ?_
  rw [Nat.zero_add, blockTsAV_length]
  exact bvarsBelow_andChainAV heq

omit [SetTheory V] in
/-- **C-2: lifting the leaf at any cut is a no-op** — a corollary of
C-1 (`liftN_eq_self_of_closed`). -/
theorem liftN_blockRecAV {s K : Nat} {RecTy : Nat → AnnotTerm} {eqs : List AnnotTerm} {c : Nat}
    (hT : ∀ c', c' < K → Term.Closed (RecTy c').erase)
    (heq : ∀ e ∈ eqs, Term.bvarsBelow K e.erase) (n k : Nat) :
    (blockRecAV s K RecTy eqs c).liftN n k = blockRecAV s K RecTy eqs c :=
  liftN_eq_self_of_closed (closed_blockRecAV hT heq) k n

omit [SetTheory V] in
/-- **C-3: the leaf reads only the `K` types and the equations** — so a
level valuation reaches it only through those.  Only the components
`c' < K` matter: the leaf is the chain of `blockTsAV K RecTy`. -/
theorem blockRecAV_congr {s₁ s₂ K : Nat} {RecTy₁ RecTy₂ : Nat → AnnotTerm}
    {eqs₁ eqs₂ : List AnnotTerm} {c : Nat} (hs : s₁ = s₂)
    (hT : ∀ c', c' < K → RecTy₁ c' = RecTy₂ c') (heq : eqs₁ = eqs₂) :
    blockRecAV s₁ K RecTy₁ eqs₁ c = blockRecAV s₂ K RecTy₂ eqs₂ c := by
  subst heq
  subst hs
  have hTs : blockTsAV K RecTy₁ = blockTsAV K RecTy₂ := by
    simp only [blockTsAV]
    refine List.map_congr_left fun mm hmm => ?_
    rw [hT mm (List.mem_range.mp hmm)]
  show projChainAV c (selChainAV s₁ (blockTsAV K RecTy₁) (andChainAV eqs₁)) = _
  rw [hTs]
  rfl

/-! ## C.5 The leaf is `AnnotValid`

The same walk as `chainOk_block_go` (`Semantics/Tower/SigChainI.lean`),
in the bit-validity currency: a Σ'-binder's obligation is its
domain's validity plus the rest's under an arbitrary element of the
domain, and the domain at depth `mm` reads at the base frame
(`annotValid_liftN_consList`), so the accumulated hypotheses are
exactly "a tuple typed at the recursor types". -/

theorem annotValid_liftN_consList (e : AnnotTerm) (rs : List V) (ρ : Nat → V) :
    AnnotValid V (consList rs ρ) (e.liftN rs.length 0) ↔ AnnotValid V ρ e := by
  rw [AnnotValid_liftN, shiftE_consList]

theorem annotValid_andAV {P Q : AnnotTerm} {ρ : Nat → V}
    (hP : AnnotValid V ρ P) (hQ : AnnotValid V ρ Q) :
    AnnotValid V ρ (andAV P Q) := by
  show AnnotValid V ρ (AnnotTerm.app (.app (.const .psigma [0, 0]) P) (.lam 1 P (Q.liftN 1 0)))
  rw [AnnotValid_app, AnnotValid_app, AnnotValid_lam]
  refine ⟨⟨trivial, hP⟩, hP, fun x _ => ?_⟩
  have h := annotValid_liftN_consList (V := V) Q [x] ρ
  rw [List.length_singleton, consList_cons, consList_nil] at h
  exact h.mpr hQ

theorem annotValid_andChainAV {ρ : Nat → V} :
    ∀ {eqs : List AnnotTerm}, (∀ e ∈ eqs, AnnotValid V ρ e) →
      AnnotValid V ρ (andChainAV eqs)
  | [], _ => trivial
  | e :: _, h => annotValid_andAV (h e (.head _))
      (annotValid_andChainAV fun e' he' => h e' (.tail _ he'))

theorem annotValid_sigChainAV_go {s : Nat} {ρ : Nat → V} {K : Nat} (RecTy : Nat → AnnotTerm)
    (Q : AnnotTerm)
    (hT : ∀ mm, mm < K → AnnotValid V ρ (RecTy mm))
    (hQ : ∀ rs : List V, rs.length = K →
      (∀ mm, mm < K → rs.getD mm pt ∈ˢ interp V ρ (RecTy mm)) →
      AnnotValid V (consList rs ρ) Q) :
    ∀ (n : Nat) (pre : List V), pre.length + n = K →
      (∀ mm, mm < pre.length → pre.getD mm pt ∈ˢ interp V ρ (RecTy mm)) →
      AnnotValid V (consList pre ρ)
        (sigChainAV s (((List.range K).drop pre.length).map fun mm => (RecTy mm).liftN mm 0) Q)
  | 0, pre, hlen, hpre => by
    rw [blockTs_drop_nil RecTy (p := pre.length) (by omega)]
    show AnnotValid V (consList pre ρ) Q
    exact hQ pre (by omega) fun mm hmm => hpre mm (by omega)
  | n + 1, pre, hlen, hpre => by
    rw [blockTs_drop_cons RecTy (p := pre.length) (by omega)]
    have hTp : AnnotValid V (consList pre ρ) ((RecTy pre.length).liftN pre.length 0) :=
      (annotValid_liftN_consList (RecTy pre.length) pre ρ).mpr (hT pre.length (by omega))
    show AnnotValid V (consList pre ρ)
      (sigAV s ((RecTy pre.length).liftN pre.length 0) _)
    show AnnotValid V (consList pre ρ) (AnnotTerm.app (.app (.const .psigma [s, s]) _)
      (.lam (s + 1) _ _))
    rw [AnnotValid_app, AnnotValid_app, AnnotValid_lam]
    refine ⟨⟨trivial, hTp⟩, hTp, fun r hr => ?_⟩
    rw [interp_liftN_consList] at hr
    have ih := annotValid_sigChainAV_go (s := s) (ρ := ρ) (K := K) RecTy Q hT hQ n (pre ++ [r])
      (by simp; omega) fun mm hmm => by
        simp only [List.length_append, List.length_singleton] at hmm
        rcases Nat.lt_or_ge mm pre.length with h | h
        · rw [getD_snoc_lt pre r h]; exact hpre mm h
        · have hmm' : mm = pre.length + 0 := by omega
          rw [hmm', getD_snoc_at]
          simpa using hr
    rw [consList_append] at ih
    simpa using ih

/-- **C-5: the leaf is `AnnotValid`** — from the `K` recursor types'
validity and every ι equation's validity at every tuple typed at
them. -/
theorem annotValid_blockRecAV {s K : Nat} {RecTy : Nat → AnnotTerm} {eqs : List AnnotTerm}
    {c : Nat} {ρ : Nat → V}
    (hT : ∀ c', c' < K → AnnotValid V ρ (RecTy c'))
    (heq : ∀ rs : List V, rs.length = K →
      (∀ mm, mm < K → rs.getD mm pt ∈ˢ interp V ρ (RecTy mm)) →
      ∀ e ∈ eqs, AnnotValid V (consList rs ρ) e) :
    AnnotValid V ρ (blockRecAV s K RecTy eqs c) := by
  show AnnotValid V ρ (projChainAV c (selChainAV s (blockTsAV K RecTy) (andChainAV eqs)))
  have hchain : AnnotValid V ρ (sigChainAV s (blockTsAV K RecTy) (andChainAV eqs)) := by
    have h := annotValid_sigChainAV_go (s := s) (ρ := ρ) (K := K) RecTy (andChainAV eqs) hT
      (fun rs hlen hmem => annotValid_andChainAV (heq rs hlen hmem)) K []
      (by simp) (fun mm hmm => absurd hmm (by simp))
    simpa [blockTsAV] using h
  have hgo : ∀ (i : Nat) (e : AnnotTerm), AnnotValid V ρ e →
      AnnotValid V ρ (projChainAV i e) := by
    intro i
    induction i with
    | zero => intro e he; rw [projChainAV, AnnotValid_fst]; exact he
    | succ i ih =>
      intro e he
      rw [projChainAV]
      exact ih (.snd e) (by rw [AnnotValid_snd]; exact he)
  refine hgo c (selChainAV s (blockTsAV K RecTy) (andChainAV eqs)) ?_
  show AnnotValid V ρ (AnnotTerm.app (.app (.const .choice [s]) _) .prf)
  rw [AnnotValid_app, AnnotValid_app]
  exact ⟨⟨trivial, hchain⟩, trivial⟩

/-! ## C.6 The two obligations, DISCHARGED at the design's equation

C-1 and C-5 each reduce to the same pair of facts about the family's
inputs — the `K` recursor types, and every ι equation AT THE CHAIN
FRAME.  At `eqs = iotaEqsAV K nCt pdoms fdoms es mk ihs Rb` the
second is a fact about ONE rule's data, and this section proves it:
the bound at `K + rP + nF`, and the validity at every fitting spine.

The validity half is the exact twin of `blockRecPre_of`'s `hwd` (the
grading of the same two sides); the bound half needs `inst`'s and
`instsAV`'s own metatheory, which is written here because no consumer
had wanted it before. -/

omit [SetTheory V] in
/-- `inst`'s bound: substituting a term bounded at `m` into a body
bounded one deeper, at the cut `k`, lands at `m + k`. -/
theorem bvarsBelow_inst {m : Nat} {a : Term} (ha : Term.bvarsBelow m a) :
    ∀ (v : Term) (k : Nat), Term.bvarsBelow (m + k + 1) v →
      Term.bvarsBelow (m + k) (Term.inst v a k) := by
  intro v
  induction v with
  | bvar i =>
    intro k h
    show Term.bvarsBelow (m + k)
      (if i < k then .bvar i else if i = k then Term.liftN k a else .bvar (i - 1))
    by_cases hik : i < k
    · rw [if_pos hik]; exact show i < m + k by omega
    · rw [if_neg hik]
      by_cases hik2 : i = k
      · rw [if_pos hik2]
        exact VExprAux.bvarsBelow_liftN k a m 0 ha
      · rw [if_neg hik2]
        have : i < m + k + 1 := h
        exact show i - 1 < m + k by omega
  | sort u => intro _ _; trivial
  | const c us => intro _ _; trivial
  | prf => intro _ _; trivial
  | app f b ihf ihb => intro k h; exact ⟨ihf k h.1, ihb k h.2⟩
  | eqE x y ihx ihy => intro k h; exact ⟨ihx k h.1, ihy k h.2⟩
  | fst e ihe => intro k h; exact ihe k h
  | snd e ihe => intro k h; exact ihe k h
  | lam A b ihA ihb =>
    intro k h
    refine ⟨ihA k h.1, ?_⟩
    have hb := ihb (k + 1) (by rw [show m + (k + 1) + 1 = m + k + 1 + 1 from by omega]; exact h.2)
    rwa [show m + (k + 1) = m + k + 1 from by omega] at hb
  | pi A B ihA ihB =>
    intro k h
    refine ⟨ihA k h.1, ?_⟩
    have hB := ihB (k + 1) (by rw [show m + (k + 1) + 1 = m + k + 1 + 1 from by omega]; exact h.2)
    rwa [show m + (k + 1) = m + k + 1 from by omega] at hB

omit [SetTheory V] in
/-- The ih substitution's bound: the residue bounded `nR` binders down
and the ih terms bounded at the frame give a bounded substitution. -/
theorem bvarsBelow_instsAV {m : Nat} :
    ∀ (vs : List AnnotTerm) (d : Nat) (e : AnnotTerm),
      Term.bvarsBelow (m + d + vs.length) e.erase →
      (∀ v ∈ vs, Term.bvarsBelow m v.erase) →
      Term.bvarsBelow (m + d) (instsAV d vs e).erase
  | [], d, e, he, _ => by simpa using he
  | v :: vs, d, e, he, hv => by
    show Term.bvarsBelow (m + d) (AnnotTerm.inst (instsAV (d + 1) vs e) (v.liftN d 0)).erase
    rw [AnnotTerm.erase_inst]
    refine bvarsBelow_inst (a := (v.liftN d 0).erase) ?_ _ 0 ?_
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN d v.erase m 0 (hv v (.head _))
    · rw [Nat.add_zero]
      have h2 := bvarsBelow_instsAV (m := m) vs (d + 1) e
        (by rw [List.length_cons] at he; rw [show m + (d + 1) + vs.length = m + d + (vs.length + 1) from by omega]; exact he)
        (fun v' hv' => hv v' (.tail _ hv'))
      rw [show m + (d + 1) = m + d + 1 from by omega] at h2
      exact h2

omit [SetTheory V] in
theorem bvarsBelow_prefVarsAV {rP nF n : Nat} (h : rP + nF ≤ n) :
    ∀ e ∈ prefVarsAV rP nF, Term.bvarsBelow n e.erase := by
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  have hlr : l < rP := List.mem_range.mp hl
  exact show nF + rP - 1 - l < n by omega

omit [SetTheory V] in
/-- **One rule's ι equation is bounded at the chain frame.** -/
theorem bvarsBelow_iotaEqAV {K c rP nF : Nat} {pdoms fdoms es ihs : List AnnotTerm}
    {mk Rb : AnnotTerm} (hc : c < K)
    (hpl : pdoms.length = rP) (hfl : fdoms.length = nF)
    (hp : ∀ D ∈ pdoms, Term.bvarsBelow K D.erase)
    (hf : ∀ D ∈ fdoms, Term.bvarsBelow (K + rP) D.erase)
    (hes : ∀ e ∈ es, Term.bvarsBelow (K + rP + nF) e.erase)
    (hmk : Term.bvarsBelow (K + rP + nF) mk.erase)
    (hih : ∀ v ∈ ihs, Term.bvarsBelow (K + rP + nF) v.erase)
    (hRb : Term.bvarsBelow (K + rP + nF + ihs.length) Rb.erase) :
    Term.bvarsBelow K (iotaEqAV K c pdoms fdoms es mk ihs Rb).erase := by
  have hdoms : DomsBelow K (propBinders (pdoms ++ fdoms)) := by
    have hgo : ∀ (Ds : List AnnotTerm) (k : Nat),
        (∀ j, ∀ hj : j < Ds.length, Term.bvarsBelow (k + j) (Ds[j]).erase) →
        DomsBelow k (propBinders Ds) := by
      intro Ds
      induction Ds with
      | nil => intro k _; trivial
      | cons D Ds ih =>
        intro k h
        refine ⟨?_, ih (k + 1) fun j hj => ?_⟩
        · have h0 := h 0 (by simp)
          rw [List.getElem_cons_zero] at h0
          exact h0
        · have hj' := h (j + 1) (by simp only [List.length_cons]; omega)
          rw [List.getElem_cons_succ] at hj'
          rw [show k + 1 + j = k + (j + 1) from by omega]
          exact hj'
    refine hgo _ K fun j hj => ?_
    rcases Nat.lt_or_ge j pdoms.length with h | h
    · rw [List.getElem_append_left h]
      exact Term.bvarsBelow.mono (Nat.le_add_right _ _) (hp _ (List.getElem_mem h))
    · rw [List.getElem_append_right h]
      have hj' : j - pdoms.length < fdoms.length := by
        rw [List.length_append] at hj; omega
      exact Term.bvarsBelow.mono (by omega) (hf _ (List.getElem_mem hj'))
  refine mkPisAV_below_of hdoms ?_
  have hlen : (propBinders (pdoms ++ fdoms)).length = rP + nF := by
    simp [propBinders]; omega
  rw [hlen]
  refine ⟨?_, ?_⟩
  · rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN
      (show Term.bvarsBelow (K + (rP + nF))
        (AnnotTerm.erase (.bvar (pdoms.length + fdoms.length + (K - 1 - c)))) from
        show pdoms.length + fdoms.length + (K - 1 - c) < K + (rP + nF) by omega) ?_
    intro a' ha'
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ha'
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · exact bvarsBelow_prefVarsAV (rP := pdoms.length) (nF := fdoms.length)
          (by omega) a ha
      · exact Term.bvarsBelow.mono (by omega) (hes a ha)
    · rw [List.mem_singleton.mp ha]
      exact Term.bvarsBelow.mono (by omega) hmk
  · have h := bvarsBelow_instsAV (m := K + rP + nF) ihs 0 Rb
      (by rw [Nat.add_zero]; exact hRb) hih
    rw [Nat.add_zero] at h
    exact Term.bvarsBelow.mono (by omega) h

/-! ### The validity half -/

theorem annotValid_mkAppN {ρ : Nat → V} :
    ∀ {args : List AnnotTerm} {f : AnnotTerm}, AnnotValid V ρ f →
      (∀ a ∈ args, AnnotValid V ρ a) → AnnotValid V ρ (AnnotTerm.mkAppN f args)
  | [], _, hf, _ => hf
  | a :: args, f, hf, ha => by
    rw [AnnotTerm.mkAppN_cons]
    exact annotValid_mkAppN (by rw [AnnotValid_app]; exact ⟨hf, ha a (.head _)⟩)
      fun a' ha' => ha a' (.tail _ ha')

theorem annotValid_instsAV_go : ∀ (vs : List AnnotTerm) (pre : List V) (e : AnnotTerm)
    (ρ : Nat → V), (∀ v ∈ vs, AnnotValid V ρ v) →
    (AnnotValid V (consList pre ρ) (instsAV pre.length vs e)
      ↔ AnnotValid V (consList (pre ++ vs.map (interp V ρ)) ρ) e)
  | [], pre, e, ρ, _ => by simp
  | v :: vs, pre, e, ρ, hv => by
    show AnnotValid V (consList pre ρ)
      ((instsAV (pre.length + 1) vs e).inst ((v.liftN pre.length 0))) ↔ _
    rw [AnnotValid_inst0 V ((annotValid_liftN_consList v pre ρ).mpr (hv v (.head _))),
      interp_liftN_consList, consList_snoc']
    have h := annotValid_instsAV_go vs (pre ++ [interp V ρ v]) e ρ
      fun v' hv' => hv v' (.tail _ hv')
    rw [List.length_append, List.length_singleton] at h
    rw [h]
    simp

theorem annotValid_instsAV {vs : List AnnotTerm} {e : AnnotTerm} {ρ : Nat → V}
    (hv : ∀ v ∈ vs, AnnotValid V ρ v) :
    AnnotValid V ρ (instsAV 0 vs e) ↔
      AnnotValid V (consList (vs.map (interp V ρ)) ρ) e := by
  have h := annotValid_instsAV_go (V := V) vs [] e ρ hv
  simpa using h

/-- **One rule's ι equation is `AnnotValid`** at the chain frame — the
exact twin of `blockRecPre_of`'s `hwd`, in the bit currency. -/
theorem annotValid_iotaEqAV {K c : Nat} {pdoms fdoms es ihs : List AnnotTerm}
    {mk Rb : AnnotTerm} {σ : Nat → V}
    (hdoms : FieldsValid σ (pdoms ++ fdoms))
    (hbody : ∀ ys, SpineFit σ (pdoms ++ fdoms) ys →
      (∀ e ∈ es, AnnotValid V (consList ys σ) e) ∧
        AnnotValid V (consList ys σ) mk ∧
        (∀ v ∈ ihs, AnnotValid V (consList ys σ) v) ∧
        AnnotValid V (consList (ihs.map (interp V (consList ys σ))) (consList ys σ)) Rb) :
    AnnotValid V σ (iotaEqAV K c pdoms fdoms es mk ihs Rb) := by
  refine AnnotValid_mkPisAV_of (w := 0) (fun d hd => by rw [propBinders_cod d hd]) ?_ ?_ ?_
  · rw [propBinders_doms]; exact hdoms
  · intro ys hsp
    rw [propBinders_doms] at hsp
    obtain ⟨hes, hmk, hih, hRb⟩ := hbody ys hsp
    rw [AnnotValid_eqE]
    refine ⟨annotValid_mkAppN trivial ?_, (annotValid_instsAV hih).mpr hRb⟩
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha; trivial
      · exact hes a ha
    · rw [List.mem_singleton.mp ha]; exact hmk
  · intro _ ys hsp
    rw [propBinders_doms] at hsp
    exact eqv_mem_univZero _ _

/-! ## C.7 The five facts AT THE RUN

`blockRecStaged_run` (`BlockRecAssembly.lean`) states them at
`blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i`, which is
`blockRecAV s rs.length (blockRecTyAV …) (eqs ψ) i` — so each is the
battery above at the run's own two inputs: the recursor types'
readings (`checkBlockRecK_tyPis`, whose closedness is one
`bvarsBelow_of_reading`) and the equation list `eqs`, which is
RM9's choice and is left as the named premise here. -/

/-- The `i`-th stored recursor type's READING is closed — the stored
type has no free variable and no loose bvar, and `denoteMeta` at depth
`0` preserves that. -/
theorem closed_blockRecTyAV {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) :
    Term.Closed ((blockRecTyAV mpC.base2.acval envC rs ψ i).erase) := by
  obtain ⟨hfv, -, -, hb, -⟩ := ConLeche.checkBlockRecK_facts h r (List.mem_of_getElem? hr)
  obtain ⟨-, -, -, hread, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  exact bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hfv) hb hread

section RunLeaf

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}

/-- **C-1 at the run**: the stage's leaf is closed. -/
theorem blockRecLeafAV_closed (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (heqB : ∀ ψ : Name → Nat, ∀ e ∈ eqs ψ, Term.bvarsBelow rs.length e.erase)
    (ψ : Name → Nat) (i : Nat) :
    Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).erase) :=
  closed_blockRecAV
    (fun _c' hc' => closed_blockRecTyAV hμ mpC h (List.getElem?_eq_getElem hc') ψ)
    (heqB ψ)

/-- **C-2 at the run**: lifting the stage's leaf is a no-op. -/
theorem blockRecLeafAV_liftN (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (heqB : ∀ ψ : Name → Nat, ∀ e ∈ eqs ψ, Term.bvarsBelow rs.length e.erase)
    (ψ : Name → Nat) (i k : Nat) :
    (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).liftN 1 k
      = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i :=
  liftN_eq_self_of_closed (blockRecLeafAV_closed hμ mpC h heqB ψ i) k 1

/-- **C-3 at the run**: the stage's leaf reads a level valuation only
through the recursor types' readings and the equations. -/
theorem blockRecLeafAV_par {mpC : EnvModelM V μ envC}
    (hpar : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        s ψ₁ = s ψ₂ ∧
        (∀ c', c' < rs.length → blockRecTyAV mpC.base2.acval envC rs ψ₁ c'
            = blockRecTyAV mpC.base2.acval envC rs ψ₂ c') ∧ eqs ψ₁ = eqs ψ₂)
    (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (hr : rs[i]? = some r) (ψ₁ ψ₂ : Name → Nat)
    (hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) :
    blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₁ i
      = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₂ i :=
  blockRecAV_congr (hpar i r hr ψ₁ ψ₂ hq).1 (hpar i r hr ψ₁ ψ₂ hq).2.1
    (hpar i r hr ψ₁ ψ₂ hq).2.2

/-- **C-4 at the run**: the stage's leaf is graded — `blockRecAV_facts`
at the family premise, one line.  **The block position is needed**:
out of range `projChainAV` walks past the chain's last binder and the
grading is not available (and not true in general). -/
theorem blockRecLeafAV_wd {mpC : EnvModelM V μ envC}
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) ρ)
    (ψ : Name → Nat) {i : Nat} (hi : i < rs.length) (ρ : Nat → V) :
    WellDenoted V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i) :=
  ((blockRecAV_facts (hpre ψ ρ)).choose_spec.1 i hi).2.2

/-- **C-5 at the run**: the stage's leaf is bit-valid. -/
theorem blockRecLeafAV_valid (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (heqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ e ∈ eqs ψ, AnnotValid V (consList tup ρ) e)
    (ψ : Name → Nat) (i : Nat) (ρ : Nat → V) :
    AnnotValid V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i) :=
  annotValid_blockRecAV
    (fun c' hc' => by
      obtain ⟨-, -, -, -, -, -, -, -, -, hwd⟩ :=
        checkBlockRecK_tyPis hμ mpC h (List.getElem?_eq_getElem hc') ψ
      exact (hwd ρ).2)
    (heqV ψ ρ)

/-! ## C.8 `hpar`'s recursor-type half, DISCHARGED

`hleafPar` asks the recursor types' READINGS to agree at two level
valuations agreeing on the `i`-th recursor's own `levelParams` — which
for the OTHER `k − 1` types is a claim about the block's recursors
SHARING their level parameters.  They do, and it is a run fact: stage
(a)'s pin `blockRecLpsOk` (`checkBlockRecPins`) says every recursor's
`levelParams` IS the generated list (`elim :: lps`, or `lps` at a
small block), and `checkConstantVal` stores the record's
`levelParams` unchanged. -/

/-- **A block's recursors share their level parameters.** -/
theorem checkBlockRecK_lps {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i j : Nat} {r r' : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (hr' : rs[j]? = some r') :
    r.1.levelParams = r'.1.levelParams := by
  obtain ⟨hpins, hlenR, hall⟩ := checkBlockRecK_recNames h
  have hone : ∀ (n : Nat) (q : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[n]? = some q → ∃ rc ∈ p.recs, q.1.levelParams = rc.cvR.levelParams := by
    intro n q hq
    have hnl : n < p.recs.length := by
      have hql := (List.getElem?_eq_some_iff.mp hq).1
      omega
    obtain ⟨rc, q', hrc, hq', -, hcv⟩ := hall n hnl
    obtain rfl := Option.some.inj (hq.symm.trans hq')
    obtain ⟨-, -, -, -, -, -, type, -, -, -, -, -, -, -, hcv'⟩ :=
      ConLeche.checkConstantVal_inv hcv
    exact ⟨rc, List.mem_of_getElem? hrc, by rw [hcv']⟩
  obtain ⟨rc, hrcm, hlv⟩ := hone i r hr
  obtain ⟨rc', hrcm', hlv'⟩ := hone j r' hr'
  have hlps := List.all_eq_true.mp (checkBlockRecPins_inv hpins).1 rc hrcm
  have hlps' := List.all_eq_true.mp (checkBlockRecPins_inv hpins).1 rc' hrcm'
  rw [hlv, hlv']
  by_cases hb : p.toBlockShape.large = true
  · rw [if_pos hb] at hlps hlps'
    rw [eq_of_beq hlps, eq_of_beq hlps']
  · rw [if_neg hb] at hlps hlps'
    rw [eq_of_beq hlps, eq_of_beq hlps']

/-- **The recursor types' readings are φ-congruent at ANY recursor's
level parameters** — `hleafPar`'s first half, so that what is left of
it is the equation list's own ψ-dependence. -/
theorem blockRecTyAV_params_ext {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) {c' : Nat} (hc' : c' < rs.length) :
    blockRecTyAV mpC.base2.acval envC rs ψ₁ c'
      = blockRecTyAV mpC.base2.acval envC rs ψ₂ c' := by
  have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
  have hlps : rs[c'].1.levelParams = r.1.levelParams := checkBlockRecK_lps h hr' hr
  have hlpd := (ConLeche.checkBlockRecK_facts h rs[c'] (List.mem_of_getElem? hr')).2.1
  obtain ⟨-, -, -, hread₁, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ₁
  obtain ⟨-, -, -, hread₂, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ₂
  have hext := denoteMeta_params_ext (V := V) mpC.base2
    (ps := rs[c'].1.levelParams) (by rw [hlps]; exact hq) 0 rs[c'].1.type hlpd
  rw [hread₁, hread₂] at hext
  exact Option.some.inj hext

/-- **C-3 at the run, with the types' half discharged**: what is left
of `hleafPar` is the EQUATION LIST's own ψ-dependence. -/
theorem blockRecLeafAV_par_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (heqP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧ eqs ψ₁ = eqs ψ₂)
    (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (hr : rs[i]? = some r) (ψ₁ ψ₂ : Name → Nat)
    (hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) :
    blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₁ i
      = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₂ i :=
  blockRecAV_congr (heqP i r hr ψ₁ ψ₂ hq).1
    (fun _ hc' => blockRecTyAV_params_ext hμ mpC h hr hq hc') (heqP i r hr ψ₁ ψ₂ hq).2

end RunLeaf

/-! ## A.1 The CHAIN-FRAME LIFTING

`BlockRuleDataAt` (`BlockRecLaw.lean`) states the rule data at the
CHAIN frame — under the `K` Σ' binders the family's tuple introduces —
while every reading the check produces lives at the BASE frame.  That
gap is O-2's bookkeeping (`M5m-REPORT` §7), and it is ONE move: a form
standing under `k` of the rule's own binders is the base-frame form
lifted by `K` at the cutoff `k`, because the chain frame is
`consList ((List.range K).map a) ρ` and `shiftE K k` of the extended
frame drops exactly that block (`shiftE_consList_ih`).

`liftDomsK` is the same move on a BINDER LIST, each domain at its own
depth; `blockRuleDataAt_of_base` is the whole of
`BlockRuleDataAt` reduced to its five base-frame identifications. -/

/-- A binder list moved under the `K` chain binders: domain `i` is
lifted at the cutoff `k + i`. -/
def liftDomsK (K : Nat) : Nat → List AnnotTerm → List AnnotTerm
  | _, [] => []
  | k, D :: Ds => D.liftN K k :: liftDomsK K (k + 1) Ds

omit [SetTheory V] in
@[simp] theorem liftDomsK_length (K : Nat) :
    ∀ (k : Nat) (Ds : List AnnotTerm), (liftDomsK K k Ds).length = Ds.length
  | _, [] => rfl
  | k, _ :: Ds => by
    show (liftDomsK K (k + 1) Ds).length + 1 = Ds.length + 1
    rw [liftDomsK_length K (k + 1) Ds]

omit [SetTheory V] in
theorem liftDomsK_append (K : Nat) :
    ∀ (k : Nat) (Ds Es : List AnnotTerm),
      liftDomsK K k (Ds ++ Es) = liftDomsK K k Ds ++ liftDomsK K (k + Ds.length) Es
  | k, [], Es => by simp [liftDomsK]
  | k, D :: Ds, Es => by
    show D.liftN K k :: liftDomsK K (k + 1) (Ds ++ Es) = _
    rw [liftDomsK_append K (k + 1) Ds Es,
      show k + 1 + Ds.length = k + (D :: Ds).length from by rw [List.length_cons]; omega]
    rfl

/-- **The lifting, at a reading**: a form read at the base frame under
`ws` binders reads the same at the CHAIN frame under the same `ws`. -/
theorem interp_liftN_chainFrame {K : Nat} {a ρ : Nat → V} (ws : List V) (e : AnnotTerm) :
    interp V (consList ws (chainFrame K a ρ)) (e.liftN K ws.length)
      = interp V (consList ws ρ) e := by
  rw [interp_liftN, chainFrame,
    shiftE_consList_ih (locals := ws) (ihvals := (List.range K).map a) rfl (by simp)]

/-- **The lifting, at a fit**: a spine fitting the base-frame binder
data fits the lifted data at the chain frame. -/
theorem spineFit_liftDomsK {K : Nat} {a ρ : Nat → V} :
    ∀ (Ds : List AnnotTerm) (ws vs : List V),
      SpineFit (consList ws ρ) Ds vs →
      SpineFit (consList ws (chainFrame K a ρ)) (liftDomsK K ws.length Ds) vs
  | [], _, [], _ => trivial
  | [], _, _ :: _, hsp => hsp.elim
  | _ :: _, _, [], hsp => hsp.elim
  | D :: Ds, ws, v :: vs, hsp => by
    refine ⟨?_, ?_⟩
    · rw [interp_liftN_chainFrame ws D]; exact hsp.1
    · have ih := spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) Ds (ws ++ [v]) vs
        (by rw [consList_append, consList_cons, consList_nil]; exact hsp.2)
      rw [List.length_append, List.length_singleton] at ih
      rw [consList_append, consList_cons, consList_nil] at ih
      exact ih

/-- **`BlockRuleDataAt`, reduced to its base-frame identifications.**
The five conjuncts at the chain frame follow from the same five at
the RULE's own frame, once the data are the base-frame forms lifted
past the `K` chain binders at their own depths.  Nothing here is about
the check: it is the whole of O-2's move, once. -/
theorem blockRuleDataAt_of_base {K rP nP : Nat} {a ρ : Nat → V}
    {pdoms0 fdoms0 es0 ihs0 : List AnnotTerm} {mk0 Rb0 : AnnotTerm}
    {xs ys : List AnnotTerm} {Ca Ra : AnnotTerm}
    (hpl : pdoms0.length = rP)
    (hsp : SpineFit ρ (pdoms0 ++ fdoms0) ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)))
    (hes : es0.map (interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)) = (xs.drop rP).map (interp V ρ))
    (hmk : interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ) mk0 = interp V ρ (AnnotTerm.mkAppN Ca ys))
    (hRa : interp V ρ (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop nP))
      = interp V (consList (ihs0.map (interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)))
          (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb0) :
    BlockRuleDataAt V K a (liftDomsK K 0 pdoms0) (liftDomsK K rP fdoms0)
      (es0.map (fun e => e.liftN K (pdoms0.length + fdoms0.length)))
      (mk0.liftN K (pdoms0.length + fdoms0.length))
      (ihs0.map (fun e => e.liftN K (pdoms0.length + fdoms0.length)))
      (Rb0.liftN K (pdoms0.length + fdoms0.length + ihs0.length))
      ρ rP nP xs ys Ca Ra := by
  have hlen : (((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) : List V).length = pdoms0.length + fdoms0.length := by
    have hq := hsp.length_eq
    simp only [List.length_append] at hq ⊢
    exact hq
  have hstep : ∀ e : AnnotTerm,
      interp V (blockRuleFrame K a ρ rP nP xs ys)
          (e.liftN K (pdoms0.length + fdoms0.length))
        = interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ) e := by
    intro e
    show interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) (chainFrame K a ρ)) _ = _
    rw [← hlen, interp_liftN_chainFrame]
  have hfun : (interp V (blockRuleFrame K a ρ rP nP xs ys) ∘
      fun e : AnnotTerm => e.liftN K (pdoms0.length + fdoms0.length))
      = interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ) := funext hstep
  refine ⟨by rw [liftDomsK_length]; exact hpl, ?_, ?_, ?_, ?_⟩
  · have happ : liftDomsK K 0 (pdoms0 ++ fdoms0)
        = liftDomsK K 0 pdoms0 ++ liftDomsK K rP fdoms0 := by
      rw [liftDomsK_append, Nat.zero_add, hpl]
    rw [← happ]
    have hq := spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) (pdoms0 ++ fdoms0) [] ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ))
      (by rw [consList_nil]; exact hsp)
    rw [consList_nil, List.length_nil] at hq
    exact hq
  · rw [List.map_map, hfun]; exact hes
  · rw [hstep]; exact hmk
  · have hRHS : interp V (consList (ihs0.map (interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)))
          (blockRuleFrame K a ρ rP nP xs ys))
          (Rb0.liftN K (pdoms0.length + fdoms0.length + ihs0.length))
        = interp V (consList (ihs0.map (interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)))
            (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb0 := by
      show interp V (consList (ihs0.map (interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)))
        (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) (chainFrame K a ρ))) _ = _
      rw [← consList_append,
        show pdoms0.length + fdoms0.length + ihs0.length
            = ((((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) : List V) ++ ihs0.map (interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ))).length from by
          rw [List.length_append, List.length_map, hlen],
        interp_liftN_chainFrame, consList_append]
    rw [List.map_map, hfun, hRHS]
    exact hRa

/-! ## A.2 The residue conjunct's β-reduction

`BlockRuleDataAt`'s fifth conjunct compares the stored right-hand
side APPLIED to the rule's spine with the residue read at the ih
values.  The right-hand side's reading is the rule's λ-tower
(`rP + nF` binders), so the left side β-reduces along the spine, and
what is left is exactly `interp_blockResidue`'s conclusion
(`BlockRecLaw.lean` §9) — O-1 at the rule's own frame.  The two
lemmas below are that split: the β-reduction is generic, and the
composition is one rewrite. -/

/-- **A λ-tower applied along a fitting spine reads as its body.** -/
theorem interp_mkAppN_mkLamsAV {lds : List (Nat × AnnotTerm)} {b Ra : AnnotTerm}
    {ρ : Nat → V} {args : List AnnotTerm}
    (hlam : Ra = mkLamsAV lds b) (hok : WellDenoted V ρ Ra)
    (hsp : SpineFit ρ (lds.map (·.2)) (args.map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN Ra args)
      = interp V (consList (args.map (interp V ρ)) ρ) b := by
  subst hlam
  rw [interp_mkAppN, foldl_app_map]
  exact mkLamsAV_fold_graded hok hsp

/-- **`blockRuleDataAt_of_base`'s `hRa`, from O-1.**  Give the stored
right-hand side's reading as the rule's λ-tower, its grading, the
spine's fit and `interp_blockResidue`'s equation at the rule's frame,
and the conjunct follows by β-reduction. -/
theorem blockRuleHRa_of {ρ : Nat → V} {Ra Rb0 A : AnnotTerm}
    {lds : List (Nat × AnnotTerm)} {xs ys : List AnnotTerm} {rP nP : Nat}
    {ihs0 : List AnnotTerm}
    (hlam : Ra = mkLamsAV lds A) (hok : WellDenoted V ρ Ra)
    (hsp : SpineFit ρ (lds.map (·.2))
      ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)))
    (hres : interp V (consList ((xs.take rP).map (interp V ρ)
          ++ (ys.drop nP).map (interp V ρ)) ρ) A
      = interp V (consList (ihs0.map (interp V (consList ((xs.take rP).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ)))
          (consList ((xs.take rP).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb0) :
    interp V ρ (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop nP))
      = interp V (consList (ihs0.map (interp V (consList ((xs.take rP).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ)))
          (consList ((xs.take rP).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb0 := by
  rw [← hres, interp_mkAppN_mkLamsAV hlam hok (by rw [List.map_append]; exact hsp),
    List.map_append]

end ConLeche.Model
