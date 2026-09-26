module

public import ConLeche.Model.Inductives.BlockRecLaw
public import ConLeche.Model.Inductives.BlockRecAssembly
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitLevels
import ConLeche.Model.Swap

public section

/-!
# The recursor family's LEAF: its structural facts, and the rule data

Two things live here, entangled through the equation list `eqs`:

* **C** — the five facts `blockRecStaged_of`
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

* **A** — `BlockRuleDataAt` (`Model/Inductives/BlockRecLaw.lean`)
  at a stored rule, narrowed to the seam's one-environment form
  `BlockRuleDataB` (§A.19b), and the endpoint `declBlock_data` (§A.18).
-/

namespace ConLeche.Model

open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche.Term
open ConLeche.Verify (openRev)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo RecRule BlockShape
  consBlockRecs)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}
  {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}

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

The validity half is the exact twin of `BlockRecPre.hEq`'s grading (the
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
theorem domsBelow_propBinders : ∀ {Ds : List AnnotTerm} {k : Nat},
    FieldsBelow k Ds → DomsBelow k (propBinders Ds)
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, domsBelow_propBinders h.2⟩

omit [SetTheory V] in
/-- A lifted form's bound, at any slack. -/
theorem bvarsBelow_liftN_add {K m n : Nat} {e : AnnotTerm} (h : Term.bvarsBelow m e.erase)
    (hn : m + K ≤ n) (k : Nat) : Term.bvarsBelow n (e.liftN K k).erase := by
  rw [AnnotTerm.erase_liftN]
  exact Term.bvarsBelow.mono hn (VExprAux.bvarsBelow_liftN K e.erase m k h)

omit [SetTheory V] in
/-- **One rule's ι equation is bounded at the chain frame.** -/
theorem bvarsBelow_iotaEqAV {K c rP nF : Nat} {pdoms fdoms es ihs : List AnnotTerm}
    {mk Rb : AnnotTerm} (hc : c < K)
    (hpl : pdoms.length = rP) (hfl : fdoms.length = nF)
    (hp : FieldsBelow K pdoms)
    (hf : FieldsBelow (K + rP) fdoms)
    (hes : ∀ e ∈ es, Term.bvarsBelow (K + rP + nF) e.erase)
    (hmk : Term.bvarsBelow (K + rP + nF) mk.erase)
    (hih : ∀ v ∈ ihs, Term.bvarsBelow (K + rP + nF) v.erase)
    (hRb : Term.bvarsBelow (K + rP + nF + ihs.length) Rb.erase) :
    Term.bvarsBelow K (iotaEqAV K c pdoms fdoms es mk ihs Rb).erase := by
  have hdoms : DomsBelow K (propBinders (pdoms ++ fdoms)) :=
    domsBelow_propBinders (fieldsBelow_append hp (by rw [hpl]; exact hf))
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
exact twin of `BlockRecPre.hEq`'s grading, in the bit currency. -/
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
readings (`recStage_tyPis`, whose closedness is one
`bvarsBelow_of_reading`) and the equation list `eqs`, which is left as
a named premise here. -/

/-- The `i`-th stored recursor type's READING is closed — the stored
type has no free variable and no loose bvar, and `denoteMeta` at depth
`0` preserves that. -/
theorem closed_blockRecTyAV {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (ψ : Name → Nat) :
    Term.Closed ((blockRecTyAV mpC.base2.acval envC rs ψ i).erase) := by
  obtain ⟨hfv, -, -, hb, -⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  obtain ⟨-, -, -, hread, -⟩ := recStage_tyPis hμ mpC h hr ψ
  exact bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hfv) hb hread

section RunLeaf

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}

/-- **C-1 at the run**: the stage's leaf is closed. -/
theorem blockRecLeafAV_closed (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (heqB : ∀ ψ : Name → Nat, ∀ e ∈ eqs ψ, Term.bvarsBelow rs.length e.erase)
    (ψ : Name → Nat) (i : Nat) :
    Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).erase) :=
  closed_blockRecAV
    (fun _c' hc' => closed_blockRecTyAV hμ mpC h (List.getElem?_eq_getElem hc') ψ)
    (heqB ψ)

/-- **C-2 at the run**: lifting the stage's leaf is a no-op. -/
theorem blockRecLeafAV_liftN (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (heqB : ∀ ψ : Name → Nat, ∀ e ∈ eqs ψ, Term.bvarsBelow rs.length e.erase)
    (ψ : Name → Nat) (i k : Nat) :
    (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).liftN 1 k
      = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i :=
  liftN_eq_self_of_closed (blockRecLeafAV_closed hμ mpC h heqB ψ i) k 1

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
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (heqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ e ∈ eqs ψ, AnnotValid V (consList tup ρ) e)
    (ψ : Name → Nat) (i : Nat) (ρ : Nat → V) :
    AnnotValid V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i) :=
  annotValid_blockRecAV
    (fun c' hc' => by
      obtain ⟨-, -, -, -, -, -, -, -, -, hwd⟩ :=
        recStage_tyPis hμ mpC h (List.getElem?_eq_getElem hc') ψ
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
theorem recStage_lps {envC : Env} {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i j : Nat} {r r' : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) (hr' : rs[j]? = some r') :
    r.1.levelParams = r'.1.levelParams := by
  obtain ⟨hpins, hlenR, hall⟩ := recStageG_recNames h
  have hone : ∀ (n : Nat) (q : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[n]? = some q → ∃ rc ∈ p.recs, q.1.levelParams = rc.cvR.levelParams := by
    intro n q hq
    have hnl : n < p.recs.length := by
      have hql := (List.getElem?_eq_some_iff.mp hq).1
      omega
    obtain ⟨rc, q', hrc, hq', -, hcv, -, -⟩ := hall n hnl
    obtain rfl := Option.some.inj (hq.symm.trans hq')
    obtain ⟨-, -, -, -, -, -, type, -, -, -, -, -, -, -, hcv'⟩ :=
      ConLeche.checkConstantVal_inv hcv
    exact ⟨rc, List.mem_of_getElem? hrc, by rw [hcv']⟩
  obtain ⟨rc, hrcm, hlv⟩ := hone i r hr
  obtain ⟨rc', hrcm', hlv'⟩ := hone j r' hr'
  have hlps := List.all_eq_true.mp hpins.1 rc hrcm
  have hlps' := List.all_eq_true.mp hpins.1 rc' hrcm'
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
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {i : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[i]? = some r) {ψ₁ ψ₂ : Name → Nat}
    (hq : ∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) {c' : Nat} (hc' : c' < rs.length) :
    blockRecTyAV mpC.base2.acval envC rs ψ₁ c'
      = blockRecTyAV mpC.base2.acval envC rs ψ₂ c' := by
  have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
  have hlps : rs[c'].1.levelParams = r.1.levelParams := recStage_lps h hr' hr
  have hlpd := (ConLeche.recStage_facts h rs[c'] (List.mem_of_getElem? hr')).2.1
  obtain ⟨-, -, -, hread₁, -⟩ := recStage_tyPis hμ mpC h hr' ψ₁
  obtain ⟨-, -, -, hread₂, -⟩ := recStage_tyPis hμ mpC h hr' ψ₂
  have hext := denoteMeta_params_ext (V := V) mpC.base2
    (ps := rs[c'].1.levelParams) (by rw [hlps]; exact hq) 0 rs[c'].1.type hlpd
  rw [hread₁, hread₂] at hext
  exact Option.some.inj hext

/-- **C-3 at the run, with the types' half discharged**: what is left
of `hleafPar` is the EQUATION LIST's own ψ-dependence. -/
theorem blockRecLeafAV_par_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
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
while every reading the check produces lives at the BASE frame.  The
gap is ONE move: a form standing under `k` of the rule's own binders
is the base-frame form lifted by `K` at the cutoff `k`, because the
chain frame is `consList ((List.range K).map a) ρ` and `shiftE K k` of
the extended frame drops exactly that block (`shiftE_consList_ih`).

`liftDomsK` is the same move on a BINDER LIST, each domain at its own
depth; `blockRuleDataAt_of_base` is the whole of
`BlockRuleDataAt` reduced to its five base-frame identifications. -/

/-- A binder list moved under the `K` chain binders: domain `i` is
lifted at the cutoff `k + i`.

`@[expose]`: a downstream fit transport is a structural recursion ON
this definition, so its body must unfold outside this module. -/
@[expose] def liftDomsK (K : Nat) : Nat → List AnnotTerm → List AnnotTerm
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
      SpineFit (consList ws (chainFrame K a ρ)) (liftDomsK K ws.length Ds) vs
        ↔ SpineFit (consList ws ρ) Ds vs
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | D :: Ds, ws, v :: vs => by
    have ih := spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) Ds (ws ++ [v]) vs
    rw [List.length_append, List.length_singleton] at ih
    simp only [consList_append, consList_cons, consList_nil] at ih
    show (v ∈ˢ interp V (consList ws (chainFrame K a ρ)) (D.liftN K ws.length) ∧ _) ↔ _
    rw [interp_liftN_chainFrame ws D]
    exact and_congr Iff.rfl ih

/-- **`BlockRuleDataAt`, reduced to its base-frame identifications.**
The five conjuncts at the chain frame follow from the same five at
the RULE's own frame, once the data are the base-frame forms lifted
past the `K` chain binders at their own depths.  Nothing here is about
the check: it is the whole chain-frame move, once. -/
theorem blockRuleDataAt_of_base {K rP nP : Nat} {a ρ : Nat → V}
    {pdoms0 fdoms0 es0 ihs : List AnnotTerm} {mk0 Rb0 : AnnotTerm}
    {xs ys : List AnnotTerm} {Ca Ra : AnnotTerm}
    (hpl : pdoms0.length = rP)
    (hsp : SpineFit ρ (pdoms0 ++ fdoms0) ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)))
    (hes : es0.map (interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)) = (xs.drop rP).map (interp V ρ))
    (hmk : interp V (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ) mk0 = interp V ρ (AnnotTerm.mkAppN Ca ys))
    (hRa : interp V ρ (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop nP))
      = interp V (consList (ihs.map (interp V (blockRuleFrame K a ρ rP nP xs ys)))
          (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb0) :
    BlockRuleDataAt V K a (liftDomsK K 0 pdoms0) (liftDomsK K rP fdoms0)
      (es0.map (fun e => e.liftN K (pdoms0.length + fdoms0.length)))
      (mk0.liftN K (pdoms0.length + fdoms0.length))
      ihs (Rb0.liftN K (pdoms0.length + fdoms0.length + ihs.length))
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
    have hq := (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) (pdoms0 ++ fdoms0) []
      ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ))).mpr
      (by rw [consList_nil]; exact hsp)
    rw [consList_nil, List.length_nil] at hq
    exact hq
  · rw [List.map_map, hfun]; exact hes
  · rw [hstep]; exact hmk
  · have hRHS : interp V (consList (ihs.map (interp V (blockRuleFrame K a ρ rP nP xs ys)))
          (blockRuleFrame K a ρ rP nP xs ys))
          (Rb0.liftN K (pdoms0.length + fdoms0.length + ihs.length))
        = interp V (consList (ihs.map (interp V (blockRuleFrame K a ρ rP nP xs ys)))
            (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb0 := by
      show interp V (consList (ihs.map (interp V (blockRuleFrame K a ρ rP nP xs ys)))
        (consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) (chainFrame K a ρ))) _ = _
      rw [← consList_append,
        show pdoms0.length + fdoms0.length + ihs.length
            = ((((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) : List V)
                ++ ihs.map (interp V (blockRuleFrame K a ρ rP nP xs ys))).length from by
          rw [List.length_append, List.length_map, hlen],
        interp_liftN_chainFrame, consList_append]
    rw [hRHS]
    exact hRa

/-! ## A.2 The residue conjunct's β-reduction

`BlockRuleDataAt`'s fifth conjunct compares the stored right-hand
side APPLIED to the rule's spine with the residue read at the ih
values.  The right-hand side's reading is the rule's λ-tower
(`rP + nF` binders), so the left side β-reduces along the spine, and
what is left is exactly `interp_blockResidue`'s conclusion
(`BlockRecLaw.lean` §9) at the rule's own frame.  The two lemmas below
are that split: the β-reduction is generic, and the composition is one
rewrite. -/

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

/-- **The residue conjunct at the ih VALUES.**  The conjunct
`blockRuleDataAt_of_base` asks reads the ih TERMS at the CHAIN frame
(their heads are the chain's components) while the fold delivers them
at the rule's own, so the two spellings meet at the VALUES and not at
a list of terms — which is where `interp_blockResidue` states it. -/
theorem blockRuleHRa_val {ρ : Nat → V} {Ra Rb0 A : AnnotTerm}
    {lds : List (Nat × AnnotTerm)} {xs ys : List AnnotTerm} {rP nP : Nat}
    {ihvals : List V}
    (hlam : Ra = mkLamsAV lds A) (hok : WellDenoted V ρ Ra)
    (hsp : SpineFit ρ (lds.map (·.2))
      ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)))
    (hres : interp V (consList ((xs.take rP).map (interp V ρ)
          ++ (ys.drop nP).map (interp V ρ)) ρ) A
      = interp V (consList ihvals (consList ((xs.take rP).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb0) :
    interp V ρ (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop nP))
      = interp V (consList ihvals (consList ((xs.take rP).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb0 := by
  rw [← hres, interp_mkAppN_mkLamsAV hlam hok (by rw [List.map_append]; exact hsp),
    List.map_append]

/-! ## A.3 The family's EQUATION LIST, spelled — and C's two
obligations at it

`blockIotaEqsAV` is the `eqs` of `blockRecStaged_run` at the block's
own data: the six components are given at the BASE frame, one per
(class, rule) pair, and lifted past the `K` chain binders exactly as
`blockRuleDataAt_of_base` requires.  The regime `hpre` is stated at
THIS list; C's `heqB`/`heqV` are then §C.6's two theorems under the
lifting, and that is what the rest of this section proves. -/

omit [SetTheory V] in
/-- The chain binders inserted: a base-frame binder list, each domain
at its own depth, stays so `K` deeper. -/
theorem fieldsBelow_liftDomsK (K : Nat) : ∀ {Ds : List AnnotTerm} {k : Nat},
    FieldsBelow k Ds → FieldsBelow (K + k) (liftDomsK K k Ds)
  | [], _, _ => trivial
  | D :: Ds, k, h => by
    refine ⟨?_, ?_⟩
    · show Term.bvarsBelow (K + k) (AnnotTerm.liftN K D k).erase
      rw [AnnotTerm.erase_liftN, Nat.add_comm K k]
      exact VExprAux.bvarsBelow_liftN K D.erase k k h.1
    · have ih := fieldsBelow_liftDomsK K (Ds := Ds) (k := k + 1) h.2
      rwa [show K + (k + 1) = K + k + 1 from by omega] at ih

/-- The bit-validity twin of `spineFit_liftDomsK`. -/
theorem annotValid_liftN_chainFrame {K : Nat} {a ρ : Nat → V} (ws : List V) (e : AnnotTerm) :
    AnnotValid V (consList ws (chainFrame K a ρ)) (e.liftN K ws.length)
      ↔ AnnotValid V (consList ws ρ) e := by
  rw [AnnotValid_liftN, chainFrame,
    shiftE_consList_ih (locals := ws) (ihvals := (List.range K).map a) rfl (by simp)]

theorem fieldsValid_liftDomsK {K : Nat} {a ρ : Nat → V} :
    ∀ (Ds : List AnnotTerm) (ws : List V),
      FieldsValid (consList ws ρ) Ds →
      FieldsValid (consList ws (chainFrame K a ρ)) (liftDomsK K ws.length Ds)
  | [], _, _ => trivial
  | D :: Ds, ws, h => by
    refine ⟨(annotValid_liftN_chainFrame ws D).mpr h.1, fun x hx => ?_⟩
    rw [interp_liftN_chainFrame ws D] at hx
    have ih := fieldsValid_liftDomsK (K := K) (a := a) (ρ := ρ) Ds (ws ++ [x]) (by
      rw [consList_append, consList_cons, consList_nil]; exact h.2 x hx)
    rw [List.length_append, List.length_singleton] at ih
    simp only [consList_append, consList_cons, consList_nil] at ih
    exact ih

/-- **The family's ι equations at the block's own data.**

`@[expose]`: the recursor model's `hpre` is stated at this term, so the body
must unfold outside this module — `blockRecEqs` is exposed but reduces
to this. -/
@[expose] def blockIotaEqsAV (K : Nat) (nCt : Nat → Nat) (pdoms0 : Nat → List AnnotTerm)
    (fdoms0 es0 ihs : Nat → Nat → List AnnotTerm) (mk0 Rb0 : Nat → Nat → AnnotTerm) :
    List AnnotTerm :=
  iotaEqsAV K nCt
    (fun c => liftDomsK K 0 (pdoms0 c))
    (fun c j => liftDomsK K (pdoms0 c).length (fdoms0 c j))
    (fun c j => (es0 c j).map (fun e => e.liftN K ((pdoms0 c).length + (fdoms0 c j).length)))
    (fun c j => (mk0 c j).liftN K ((pdoms0 c).length + (fdoms0 c j).length))
    ihs
    (fun c j => (Rb0 c j).liftN K
      ((pdoms0 c).length + (fdoms0 c j).length + (ihs c j).length))

omit [SetTheory V] in
/-- **`heqB` at the design's equation list** — every base-frame
component bounded at its own depth. -/
theorem bvarsBelow_blockIotaEqsAV {K : Nat} {nCt : Nat → Nat}
    {pdoms0 : Nat → List AnnotTerm} {fdoms0 es0 ihs : Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : Nat → Nat → AnnotTerm}
    (hp : ∀ c, c < K → FieldsBelow 0 (pdoms0 c))
    (hf : ∀ c, c < K → ∀ j, j < nCt c → FieldsBelow (pdoms0 c).length (fdoms0 c j))
    (hes : ∀ c, c < K → ∀ j, j < nCt c → ∀ e ∈ es0 c j,
      Term.bvarsBelow ((pdoms0 c).length + (fdoms0 c j).length) e.erase)
    (hmk : ∀ c, c < K → ∀ j, j < nCt c →
      Term.bvarsBelow ((pdoms0 c).length + (fdoms0 c j).length) (mk0 c j).erase)
    (hih : ∀ c, c < K → ∀ j, j < nCt c → ∀ v ∈ ihs c j,
      Term.bvarsBelow (K + (pdoms0 c).length + (fdoms0 c j).length) v.erase)
    (hRb : ∀ c, c < K → ∀ j, j < nCt c →
      Term.bvarsBelow
        ((pdoms0 c).length + (fdoms0 c j).length + (ihs c j).length) (Rb0 c j).erase) :
    ∀ e ∈ blockIotaEqsAV K nCt pdoms0 fdoms0 es0 ihs mk0 Rb0,
      Term.bvarsBelow K e.erase := by
  refine forall_iotaEqsAV fun c hc j hj => ?_
  refine bvarsBelow_iotaEqAV (rP := (pdoms0 c).length) (nF := (fdoms0 c j).length) hc
    (liftDomsK_length K 0 (pdoms0 c)) (liftDomsK_length K (pdoms0 c).length (fdoms0 c j))
    ?_ ?_ ?_ ?_ ?_ ?_
  · have hq := fieldsBelow_liftDomsK K (Ds := pdoms0 c) (k := 0) (hp c hc)
    rw [Nat.add_zero] at hq
    exact hq
  · exact fieldsBelow_liftDomsK K (Ds := fdoms0 c j) (k := (pdoms0 c).length) (hf c hc j hj)
  · intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact bvarsBelow_liftN_add (hes c hc j hj e' he') (by omega) _
  · exact bvarsBelow_liftN_add (hmk c hc j hj) (by omega) _
  · intro v hv
    exact Term.bvarsBelow.mono (by omega) (hih c hc j hj v hv)
  · exact bvarsBelow_liftN_add (hRb c hc j hj) (by omega) _

/-- **`heqV` at the design's equation list** — the base-frame twin of
`BlockRecPre.hEq`'s grading. -/
theorem annotValid_blockIotaEqsAV {K : Nat} {nCt : Nat → Nat}
    {pdoms0 : Nat → List AnnotTerm} {fdoms0 es0 ihs : Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : Nat → Nat → AnnotTerm} {a ρ : Nat → V}
    (hdoms : ∀ c, c < K → ∀ j, j < nCt c → FieldsValid ρ (pdoms0 c ++ fdoms0 c j))
    (hbody : ∀ c, c < K → ∀ j, j < nCt c → ∀ ys : List V,
      SpineFit ρ (pdoms0 c ++ fdoms0 c j) ys →
      (∀ e ∈ es0 c j, AnnotValid V (consList ys ρ) e) ∧
        AnnotValid V (consList ys ρ) (mk0 c j) ∧
        (∀ v ∈ ihs c j, AnnotValid V (consList ys (chainFrame K a ρ)) v) ∧
        AnnotValid V
          (consList ((ihs c j).map (interp V (consList ys (chainFrame K a ρ))))
            (consList ys ρ)) (Rb0 c j)) :
    ∀ e ∈ blockIotaEqsAV K nCt pdoms0 fdoms0 es0 ihs mk0 Rb0,
      AnnotValid V (chainFrame K a ρ) e := by
  refine forall_iotaEqsAV fun c hc j hj => ?_
  have happ : liftDomsK K 0 (pdoms0 c ++ fdoms0 c j)
      = liftDomsK K 0 (pdoms0 c) ++ liftDomsK K (pdoms0 c).length (fdoms0 c j) := by
    rw [liftDomsK_append, Nat.zero_add]
  have hlen : (liftDomsK K 0 (pdoms0 c)).length = (pdoms0 c).length := by
    rw [liftDomsK_length]
  have hfit : ∀ ys : List V,
      SpineFit (chainFrame K a ρ)
          (liftDomsK K 0 (pdoms0 c) ++ liftDomsK K (pdoms0 c).length (fdoms0 c j)) ys →
        SpineFit ρ (pdoms0 c ++ fdoms0 c j) ys := by
    intro ys hys
    have hq := (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) (pdoms0 c ++ fdoms0 c j) [] ys)
    rw [consList_nil, List.length_nil] at hq
    exact hq.mp (by rw [happ]; exact hys)
  refine annotValid_iotaEqAV ?_ fun ys hys => ?_
  · rw [← happ]
    have hq := fieldsValid_liftDomsK (K := K) (a := a) (ρ := ρ) (pdoms0 c ++ fdoms0 c j) []
      (by rw [consList_nil]; exact hdoms c hc j hj)
    rw [consList_nil, List.length_nil] at hq
    exact hq
  · obtain ⟨hes, hmk, hih, hRb⟩ := hbody c hc j hj ys (hfit ys hys)
    have hlys : ys.length = (pdoms0 c).length + (fdoms0 c j).length := by
      have hq := (hfit ys hys).length_eq
      rw [List.length_append] at hq
      exact hq
    have hstep : ∀ e : AnnotTerm,
        AnnotValid V (consList ys (chainFrame K a ρ))
            (e.liftN K ((pdoms0 c).length + (fdoms0 c j).length))
          ↔ AnnotValid V (consList ys ρ) e := by
      intro e; rw [← hlys]; exact annotValid_liftN_chainFrame ys e
    have hinterp : ∀ e : AnnotTerm,
        interp V (consList ys (chainFrame K a ρ))
            (e.liftN K ((pdoms0 c).length + (fdoms0 c j).length))
          = interp V (consList ys ρ) e := by
      intro e; rw [← hlys]; exact interp_liftN_chainFrame ys e
    refine ⟨?_, (hstep _).mpr hmk, hih, ?_⟩
    · intro e he
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      exact (hstep e').mpr (hes e' he')
    · have hq := annotValid_liftN_chainFrame (K := K) (a := a) (ρ := ρ)
        (ys ++ (ihs c j).map (interp V (consList ys (chainFrame K a ρ)))) (Rb0 c j)
      rw [List.length_append, List.length_map, hlys] at hq
      simp only [consList_append] at hq
      exact hq.mpr hRb

/-! ## A.4 `hnew`'s three FREE premises, discharged

`hnew` (`blockRecStaged_run`) is `blockRecRuleLaw_of`
(`BlockRecLaw.lean`) at one (recursor, constructor) pair, and four of
its six premises are free once `eqs` is fixed to `blockIotaEqsAV`: the
firing (`recRuleBits_fire`), the recursor's argument sums
(`recStage_recNames`: the stage pins them), the valuation's
reading at the block position, and the family's ι law.  What is left
is the right-hand side's, and it enters `blockRuleDataAt_of_base`
(§3.1). -/

section Hnew

variable {envC : Env} {p : ConLeche.BlockParts}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
  {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
  {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
  {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
  {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}

/-- The family's `eqs`: the family's ι equations at the block's own
base-frame data (§A.3). -/
@[expose] def blockRecEqs (nCt : Nat → Nat)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (pdoms0 : (Name → Nat) → Nat → List AnnotTerm)
    (fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm) (ψ : Name → Nat) : List AnnotTerm :=
  blockIotaEqsAV rs.length nCt (pdoms0 ψ) (fdoms0 ψ) (es0 ψ) (ihs ψ) (mk0 ψ) (Rb0 ψ)

/-- **`hleaf`**: the consed model's valuation at the `j`-th stored
recursor IS the `j`-th leaf. -/
theorem blockRecHleaf {mpC : EnvModelM V μ envC}
    {m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC rs s
      (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
    (hnd : (rs.map (·.1.name)).Nodup) {j : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[j]? = some r)
    (ψ : Name → Nat) :
    m₃.acval r.1.name ψ
      = blockRecLeafAV mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ j := by
  have hi : (rs.map (·.1.name))[j]? = some r.1.name := by
    rw [List.getElem?_map, hr]; rfl
  rw [hac, blockRecAcv, blockRecAcvOf_at hnd hi]

/-- **`hiota`**: the family's ι law at the `j`-th class and the `i`-th
rule, in `blockRecRuleLaw_of`'s spelling — `blockIotaAt_of_pre` at the
regimes' `hpre`, at `blockRecEqs`. -/
theorem blockRecHiota {mpC : EnvModelM V μ envC}
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ)
    {j i : Nat} (hj : j < rs.length) (hi : i < nCt j) (ψ : Name → Nat) (ρ : Nat → V) :
    BlockIotaAt V rs.length j
      (blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ)
      (liftDomsK rs.length 0 (pdoms0 ψ j))
      (liftDomsK rs.length (pdoms0 ψ j).length (fdoms0 ψ j i))
      ((es0 ψ j i).map
        (fun e => e.liftN rs.length ((pdoms0 ψ j).length + (fdoms0 ψ j i).length)))
      ((mk0 ψ j i).liftN rs.length ((pdoms0 ψ j).length + (fdoms0 ψ j i).length))
      (ihs ψ j i)
      ((Rb0 ψ j i).liftN rs.length
        ((pdoms0 ψ j).length + (fdoms0 ψ j i).length + (ihs ψ j i).length))
      ρ :=
  blockIotaAt_of_pre (hpre ψ ρ) hj hi

/-- **`hrPle`**: the recursor's rule prefix does not reach past its
major premise — the stage's own equation `mI = rP + nIdx`. -/
theorem blockRecHrPle {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {j : Nat} (hj : j < rs.length) :
    p.toBlockShape.rulePrefixAt j ≤ p.toBlockShape.majorIdxAt j := by
  obtain ⟨-, hlenR, hall⟩ := recStageG_recNames h
  obtain ⟨-, -, -, -, -, -, -, nIdx, hsum⟩ := hall j (by omega)
  omega

/-- **The stored right-hand side's own law**, at one (recursor,
constructor) pair: `blockRecRuleLaw_of`'s `hrhs`, named.  Naming it is
what makes A-5 (`blockRecHnew_of`) three lines — the obligation is
stated once here, consumed by `blockRecRuleLaw_run`, and discharged by
the rule-data chapter (`blockRuleDataAt_of_base` for its fourth
conjunct's rule datum, `blockRuleHRa_val` and `interp_blockResidue`
for the residue inside it).

The family's leaf enters only through `leaf`, so the obligation does
not mention the equation list it was built from.

`@[expose]`: it is stated here and discharged elsewhere, so its body
must unfold outside this module. -/
@[expose] def BlockRuleRhsOk (leaf : (Name → Nat) → Nat → AnnotTerm)
    (m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC))
    (φ : Name → Nat) (j i : Nat)
    (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (rl : ConLeche.RecRule) : Prop :=
  ∀ us : List Level, us.length = r.1.levelParams.length →
      ∃ Ra : AnnotTerm,
        denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
            ((ConLeche.RecRule.rhs rl).instantiateLevelParams r.1.levelParams us) = some Ra ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ Ra) ∧
        ∀ (cvj : ConstantVal) (cnP cnF : Nat),
          (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC).find?
              (ConLeche.RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
        ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm)
          (TVa TVja restR restC : AnnotTerm),
          xs.length = p.toBlockShape.majorIdxAt j →
          ys.length = ConLeche.RecRule.ctorParams rl + ConLeche.RecRule.nfields rl →
          usj.length = cvj.levelParams.length →
          Level.substFn φ cvj.levelParams usj
            = Level.substFn φ cvj.levelParams
                (ConLeche.recFireComparands rl r.1.levelParams us cvj.levelParams []
                  (p.toBlockShape.rulePrefixAt j)).1 →
          -- the `.nested` firing's parameter comparison (vacuous at `.plain`)
          (∀ lvls pins, ConLeche.RecRule.fire rl = .nested lvls pins →
            ∀ q, q < ConLeche.RecRule.ctorParams rl →
            ∀ vpa : AnnotTerm,
              denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ
                  (p.toBlockShape.rulePrefixAt j)
                (openRev 0 (p.toBlockShape.rulePrefixAt j)
                  ((pins.getD q default).instantiateLevelParams r.1.levelParams us))
                = some vpa →
              interp V ρ (ys.getD q default)
                = interp V ρ (AnnotTerm.instRevChain
                    (xs.take (p.toBlockShape.rulePrefixAt j)) vpa)) →
          IotaIndexPin (V := V) ρ restC (ConLeche.RecRule.ctorParams rl)
            (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
          denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
              (r.1.type.instantiateLevelParams r.1.levelParams us) = some TVa →
          denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
              (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
          TeleFitPA V ρ TVa
            (xs ++ [AnnotTerm.mkAppN
              (m₃.acval (ConLeche.RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys]) restR →
          TeleFitPA V ρ TVja ys restC →
          ((∀ a : Nat → V,
            (∀ c', c' < rs.length →
              interp V ρ (leaf (Level.substFn φ r.1.levelParams us) c') = a c') →
            BlockRuleDataAt V rs.length a
              (liftDomsK rs.length 0 (pdoms0 (Level.substFn φ r.1.levelParams us) j))
              (liftDomsK rs.length (pdoms0 (Level.substFn φ r.1.levelParams us) j).length
                (fdoms0 (Level.substFn φ r.1.levelParams us) j i))
              ((es0 (Level.substFn φ r.1.levelParams us) j i).map (fun e =>
                e.liftN rs.length
                  ((pdoms0 (Level.substFn φ r.1.levelParams us) j).length
                    + (fdoms0 (Level.substFn φ r.1.levelParams us) j i).length)))
              ((mk0 (Level.substFn φ r.1.levelParams us) j i).liftN rs.length
                ((pdoms0 (Level.substFn φ r.1.levelParams us) j).length
                  + (fdoms0 (Level.substFn φ r.1.levelParams us) j i).length))
              (ihs (Level.substFn φ r.1.levelParams us) j i)
              ((Rb0 (Level.substFn φ r.1.levelParams us) j i).liftN rs.length
                ((pdoms0 (Level.substFn φ r.1.levelParams us) j).length
                  + (fdoms0 (Level.substFn φ r.1.levelParams us) j i).length
                  + (ihs (Level.substFn φ r.1.levelParams us) j i).length))
              ρ (p.toBlockShape.rulePrefixAt j) (ConLeche.RecRule.ctorParams rl) xs ys
              (m₃.acval (ConLeche.RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) Ra) ∨
            -- the `ℓ = 0` arm: both sides are the point
            (interp V ρ (AnnotTerm.mkAppN (leaf (Level.substFn φ r.1.levelParams us) j)
                (xs ++ [AnnotTerm.mkAppN (m₃.acval (ConLeche.RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys])) = pt ∧
              interp V ρ (AnnotTerm.mkAppN Ra
                (xs.take (p.toBlockShape.rulePrefixAt j)
                  ++ ys.drop (ConLeche.RecRule.ctorParams rl))) = pt)) ∧
          ((∀ a ∈ xs, WellDenotedV V ρ a) → (∀ b ∈ ys, WellDenotedV V ρ b) →
            WellDenotedV V ρ (AnnotTerm.mkAppN Ra
              (xs.take (p.toBlockShape.rulePrefixAt j)
                ++ ys.drop (ConLeche.RecRule.ctorParams rl))))

/-- **One stored rule's `RecRuleLaw`, at the run** — `blockRecRuleLaw_gen`
with four of its premises discharged (§A.4).  What is left is the
`.nested` pins' law (`RecRulePinsOk`, vacuous at `.plain`) and the
RIGHT-HAND SIDE's (`BlockRuleRhsOk`), whose rule-data conjunct enters
`blockRuleDataAt_of_base` (§3.1). -/
theorem blockRecRuleLaw_run {mpC : EnvModelM V μ envC} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hnd : (rs.map (·.1.name)).Nodup)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ) (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ)
    {m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)}
    (hac : m₃.acval
      = blockRecAcv mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
    (φ : Name → Nat) {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[j]? = some r)
    (hj : j < rs.length) (hi : i < nCt j) {rl : ConLeche.RecRule}
    (hpins : RecRulePinsOk m₃ φ r.1 (p.toBlockShape.rulePrefixAt j) rl)
    (hrhs : BlockRuleRhsOk (V := V) (pdoms0 := pdoms0) (fdoms0 := fdoms0) (es0 := es0)
      (ihs := ihs) (mk0 := mk0) (Rb0 := Rb0)
      (blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)) m₃ φ j i r rl) :
    RecRuleLaw m₃ φ r.1.name r.1 (p.toBlockShape.majorIdxAt j)
      (p.toBlockShape.rulePrefixAt j) rl :=
  blockRecRuleLaw_gen (blockRecHrPle h hj) hj
    (blockRecHleaf hac hnd hr) (blockRecHiota hpre hj hi) hpins fun us hus => by
      obtain ⟨Ra, hRa, hok, hsp⟩ := hrhs us hus
      exact ⟨Ra, hRa, hok, fun cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl hujl
        hψ _ hN hidx hTVa hTVja hfitR hfitC => hsp cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR
          restC hxl hyl hujl hψ hN hidx hTVa hTVja hfitR hfitC⟩

/-- **A-5: `hnew`, in `blockRecStaged_runR`'s exact spelling.**

The stage's rule seam is `blockRecRuleLaw_run` at every (recursor,
constructor) pair of the SHAPE; the pair's index bound is the stored
constructor list's own.  **What is left of `hnew` is `RecRulePinsOk`
and `BlockRuleRhsOk` at each pair, and nothing else.** -/
theorem blockRecHnew_of {mpC : EnvModelM V μ envC} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hnd : (rs.map (·.1.name)).Nodup)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ)
    (hnCt : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → r.2.2.2.length ≤ nCt j)
    {nPc : Nat → Nat}
    {fireOf : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) →
      ConLeche.RecRuleFire}
    (hpins : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) →
      ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
        List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        RecRulePinsOk m₃ φ r.1 (p.toBlockShape.rulePrefixAt j)
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
              fire := fireOf j r, rhs := rhs, paramsBlind := true }))
    (hrhs : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) →
      ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
        List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        fireOf j r ≠ .inert →
        BlockRuleRhsOk (V := V) (pdoms0 := pdoms0) (fdoms0 := fdoms0) (es0 := es0)
          (ihs := ihs) (mk0 := mk0) (Rb0 := Rb0)
          (blockRecLeafAV mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)) m₃ φ j i r
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
              fire := fireOf j r, rhs := rhs, paramsBlind := true })) :
    ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) →
      ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
        List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        fireOf j r ≠ .inert →
        RecRuleLaw m₃ φ r.1.name r.1 (p.toBlockShape.majorIdxAt j)
          (p.toBlockShape.rulePrefixAt j)
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
              fire := fireOf j r, rhs := rhs, paramsBlind := true }) := by
  intro m₃ hac φ j r hr i cA rhs hcA hrh hfire
  have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  have hi : i < nCt j := by
    have h₁ := (List.getElem?_eq_some_iff.mp hcA).1
    have h₂ := hnCt j r hr
    omega
  exact blockRecRuleLaw_run h hnd hpre hac φ hr hj hi
    (hpins m₃ hac φ j r hr i cA rhs hcA hrh) (hrhs m₃ hac φ j r hr i cA rhs hcA hrh hfire)

/-! ## A.5b The stage, with `hnew` applied

`blockRecStaged_run` (`BlockRecAssembly.lean`) takes the rule seam as
`hnew`; §A.5 reduces that to the per-pair right-hand-side obligation,
and §C.7/§C.8 reduce the LEAF's five facts to three statements about
the equation list alone.  Composing them leaves the stage's premises
at exactly: the run, the recogniser's `Nodup`, the constructors'
storage, the equation list's three (`heqB`/`heqV`/`heqP` — §A.3's two
lemmas cut the first two down to the six components), the family's
regime `hpre` and the per-pair `BlockRuleRhsOk`. -/

/-- **The recursor stage, with `hnew` applied** — `eqs` fixed to
`blockRecEqs` and the leaf's five facts discharged, at any rules of the
shape (`blockRecStaged_runR`). -/
theorem blockRecStaged_rhs (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hnd : (rs.map (·.1.name)).Nodup)
    {nPc : Nat → Nat}
    {fireOf : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) →
      ConLeche.RecRuleFire}
    (hshape : ConLeche.RecRulesShape envC.find? R rs nPc fireOf)
    (hnest : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ lvls pins, fireOf j r = .nested lvls pins →
        p.toBlockShape.rulePrefixAt j ≤ p.toBlockShape.majorIdxAt j ∧
        (∀ l ∈ lvls, l.allParamsDefined r.1.levelParams = true) ∧
        (∀ pin ∈ pins, pin.hasFvar = false ∧
          pin.allLevelParamsDefined r.1.levelParams = true ∧
          pin.constsResolve envC = true ∧
          pin.looseBVarsBounded (p.toBlockShape.rulePrefixAt j) = true ∧
          ∀ (T : Name) (i : Nat), envC.findProj? T i = none → Expr.NoProjAt T i pin) ∧
        ∃ pre dom body bm D,
          r.1.type.stripPis (p.toBlockShape.majorIdxAt j) = some (pre, .forallE dom body bm) ∧
          dom.getAppFn = .const D lvls ∧
          dom.getAppArgs =
            pins.map (Expr.liftLooseBVars
              (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j) 0) ++
              (List.range (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j)).map
                (fun i => Expr.bvar
                  (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j - 1 - i)))
    (hctorsIn : ∀ r ∈ rs, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF))
    (heqB : ∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
        Term.bvarsBelow rs.length e.erase)
    (heqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ e ∈ blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
        AnnotValid V (consList tup ρ) e)
    (heqP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧
          blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ₁
            = blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ₂)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ)
    (hnCt : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → r.2.2.2.length ≤ nCt j)
    (hpins : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) →
      ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
        List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        RecRulePinsOk m₃ φ r.1 (p.toBlockShape.rulePrefixAt j)
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
              fire := fireOf j r, rhs := rhs, paramsBlind := true }))
    (hrhs : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) →
      ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
        List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        fireOf j r ≠ .inert →
        BlockRuleRhsOk (V := V) (pdoms0 := pdoms0) (fdoms0 := fdoms0) (es0 := es0)
          (ihs := ihs) (mk0 := mk0) (Rb0 := Rb0)
          (blockRecLeafAV mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)) m₃ φ j i r
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
              fire := fireOf j r, rhs := rhs, paramsBlind := true })) :
    BlockRecStagedAt (V := V) μ envC (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) mpC :=
  blockRecStaged_runR hμ mpC h hnd hshape hnest hctorsIn
    (blockRecLeafAV_closed hμ mpC h heqB)
    (blockRecLeafAV_liftN hμ mpC h heqB)
    (blockRecLeafAV_par_run hμ mpC h heqP)
    (fun ψ _ hi ρ => blockRecLeafAV_wd hpre ψ hi ρ)
    (blockRecLeafAV_valid hμ mpC h heqV)
    hpre
    (blockRecHnew_of h hnd hpre hnCt hpins hrhs)

/-! ## A.5c `BlockRuleRhsOk` at the BASE frame

The obligation §A.5 leaves is stated at the CHAIN frame and with the
right-hand side's reading existential; `blockRuleDataAt_of_base` (§A.1)
undoes the first and naming the reading undoes the second.  What is
left is five statements at the rule's OWN frame, per level
instantiation and per fired spine:

1. the prefix and the fields FIT (two halves: §A.10's prefix
   truncation and the representation's fibre);
2. the index expressions read to the recursor's index arguments
   (`blockRuleEsAV_eq` at the constructors' stage);
3. the fired spine's reading is the constructor at its own parameters
   (`blockRuleMkAV_eq`; the value is parameter-blind, `BlockModelAt.ctor`);
4. the residue, at the ih VALUES (`blockRuleHRa_val` below, at
   `ihSpineFold_blockRec` — whose G3 premise is §A.16's
   `blockRuleHfit_run`);
5. the applied right-hand side is graded
   (`mkAppN_wellDenotedV_of_lam` at the rule's λ-tower).

`RaOf` is the reading as a FUNCTION of the level valuation, which is
how the definition uses it (`Level.substFn φ r.1.levelParams us`
appears in every one of its clauses). -/

/-- **`BlockRuleRhsOk` from the base-frame identifications.** -/
theorem blockRuleRhsOk_of
    {m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)}
    {φ : Name → Nat} {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} {rl : ConLeche.RecRule}
    {leaf : (Name → Nat) → Nat → AnnotTerm} {RaOf : (Name → Nat) → AnnotTerm}
    (hread : ∀ us : List Level, us.length = r.1.levelParams.length →
      denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
          ((ConLeche.RecRule.rhs rl).instantiateLevelParams r.1.levelParams us)
        = some (RaOf (Level.substFn φ r.1.levelParams us)))
    (hok : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (RaOf ψ))
    (hpl : ∀ ψ : Name → Nat, (pdoms0 ψ j).length = p.toBlockShape.rulePrefixAt j)
    (hdata : ∀ us : List Level, us.length = r.1.levelParams.length →
          ∀ (cvj : ConstantVal) (cnP cnF : Nat),
            (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC).find?
                (ConLeche.RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
          ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm)
            (TVa TVja restR restC : AnnotTerm),
            xs.length = p.toBlockShape.majorIdxAt j →
            ys.length = ConLeche.RecRule.ctorParams rl + ConLeche.RecRule.nfields rl →
            usj.length = cvj.levelParams.length →
            Level.substFn φ cvj.levelParams usj
              = Level.substFn φ cvj.levelParams
                  (ConLeche.recFireComparands rl r.1.levelParams us cvj.levelParams []
                    (p.toBlockShape.rulePrefixAt j)).1 →
            (∀ lvls pins, ConLeche.RecRule.fire rl = .nested lvls pins →
              ∀ q, q < ConLeche.RecRule.ctorParams rl →
              ∀ vpa : AnnotTerm,
                denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ
                    (p.toBlockShape.rulePrefixAt j)
                  (openRev 0 (p.toBlockShape.rulePrefixAt j)
                    ((pins.getD q default).instantiateLevelParams r.1.levelParams us))
                  = some vpa →
                interp V ρ (ys.getD q default)
                  = interp V ρ (AnnotTerm.instRevChain
                      (xs.take (p.toBlockShape.rulePrefixAt j)) vpa)) →
            IotaIndexPin (V := V) ρ restC (ConLeche.RecRule.ctorParams rl)
              (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
            denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
                (r.1.type.instantiateLevelParams r.1.levelParams us) = some TVa →
            denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
                (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
            TeleFitPA V ρ TVa
              (xs ++ [AnnotTerm.mkAppN
                (m₃.acval (ConLeche.RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]) restR →
            TeleFitPA V ρ TVja ys restC →
        ((SpineFit ρ (pdoms0 (Level.substFn φ r.1.levelParams us) j
              ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i)
            ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
              ++ (ys.drop (ConLeche.RecRule.ctorParams rl)).map (interp V ρ)) ∧
          (es0 (Level.substFn φ r.1.levelParams us) j i).map
              (interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
                ++ (ys.drop (ConLeche.RecRule.ctorParams rl)).map (interp V ρ)) ρ))
            = (xs.drop (p.toBlockShape.rulePrefixAt j)).map (interp V ρ) ∧
          interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
              ++ (ys.drop (ConLeche.RecRule.ctorParams rl)).map (interp V ρ)) ρ)
              (mk0 (Level.substFn φ r.1.levelParams us) j i)
            = interp V ρ (AnnotTerm.mkAppN (m₃.acval (ConLeche.RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys) ∧
          (∀ a : Nat → V,
            (∀ c', c' < rs.length →
              interp V ρ (leaf (Level.substFn φ r.1.levelParams us) c') = a c') →
            interp V ρ (AnnotTerm.mkAppN (RaOf (Level.substFn φ r.1.levelParams us))
                (xs.take (p.toBlockShape.rulePrefixAt j)
                  ++ ys.drop (ConLeche.RecRule.ctorParams rl)))
              = interp V (consList
                  ((ihs (Level.substFn φ r.1.levelParams us) j i).map
                    (interp V (blockRuleFrame rs.length a ρ (p.toBlockShape.rulePrefixAt j)
                      (ConLeche.RecRule.ctorParams rl) xs ys)))
                  (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
                    ++ (ys.drop (ConLeche.RecRule.ctorParams rl)).map (interp V ρ)) ρ))
                (Rb0 (Level.substFn φ r.1.levelParams us) j i))) ∨
          -- the `ℓ = 0` arm: both sides are the point
          (interp V ρ (AnnotTerm.mkAppN (leaf (Level.substFn φ r.1.levelParams us) j)
              (xs ++ [AnnotTerm.mkAppN (m₃.acval (ConLeche.RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys])) = pt ∧
            interp V ρ (AnnotTerm.mkAppN (RaOf (Level.substFn φ r.1.levelParams us))
              (xs.take (p.toBlockShape.rulePrefixAt j)
                ++ ys.drop (ConLeche.RecRule.ctorParams rl))) = pt)) ∧
          ((∀ a ∈ xs, WellDenotedV V ρ a) → (∀ b ∈ ys, WellDenotedV V ρ b) →
            WellDenotedV V ρ (AnnotTerm.mkAppN (RaOf (Level.substFn φ r.1.levelParams us))
              (xs.take (p.toBlockShape.rulePrefixAt j)
                ++ ys.drop (ConLeche.RecRule.ctorParams rl))))) :
    BlockRuleRhsOk (V := V) (pdoms0 := pdoms0) (fdoms0 := fdoms0) (es0 := es0)
      (ihs := ihs) (mk0 := mk0) (Rb0 := Rb0) leaf m₃ φ j i r rl := by
  intro us hus
  refine ⟨RaOf (Level.substFn φ r.1.levelParams us), hread us hus, fun ρ => hok _ ρ, ?_⟩
  intro cvj cnP cnF hfind usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ hN hidx hTVa
    hTVja hfitR hfitC
  obtain ⟨hdat, happ⟩ := hdata us hus cvj cnP cnF hfind usj ρ xs ys TVa TVja
    restR restC hxl hyl husjl hψ hN hidx hTVa hTVja hfitR hfitC
  refine ⟨?_, happ⟩
  rcases hdat with ⟨hsp, hes, hmk, hRa⟩ | hpt
  case inr => exact Or.inr hpt
  refine Or.inl fun a ha => ?_
  have h := blockRuleDataAt_of_base (V := V) (K := rs.length) (a := a) (ρ := ρ)
    (rP := p.toBlockShape.rulePrefixAt j) (nP := ConLeche.RecRule.ctorParams rl)
    (hpl (Level.substFn φ r.1.levelParams us)) hsp hes hmk (hRa a ha)
  simp only [hpl] at h ⊢
  exact h

/-! ## A.6 The rule data's FIRST component, at the run

`pdoms0` — the rule's prefix domains at the base frame — needs no new
reading: it is the `rP` first entries of the recursor type's own
binder data (`blockRecRdsAV`), which `recStage_tyPis`
identifies.  Its length conjunct (the first of `BlockRuleDataAt`'s
five) is then the stage's two pins together: `rds.length = mI + 1` and
`mI = rP + nIdx`. -/

/-- **The `c`-th rule's prefix domains, at the BASE frame.** -/
@[expose] def blockRulePdomsAV (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : ConLeche.BlockShape)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ψ : Name → Nat) (c : Nat) : List AnnotTerm :=
  ((blockRecRdsAV acval envC p rs ψ c).take (p.rulePrefixAt c)).map (·.2.2)

/-- **`BlockRuleDataAt`'s first conjunct, at the run.** -/
theorem blockRulePdomsAV_length {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) :
    (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := by
  obtain ⟨-, -, -, -, -, hlen, -⟩ := recStage_tyPis hμ mpC h hr ψ
  have hle := blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  rw [blockRulePdomsAV, List.length_map, List.length_take, hlen]
  omega

end Hnew

/-! ## A.5 Stage (c)'s record

The rule's own data — the two typing runs, the three openings, the
λ-tower's body, the constructor's instantiated telescope, the
abstraction's residue and the `ih` telescope, each with its DEFINING
equation — is the stage's rule record `ConLeche.RuleRun`
(`Verify/Inductives/BlockRecRun.lean`), handed out at a stored rule by
`RecKRun.ruleAt`; the components below are functions of the run
through it. -/

/-! ## A.7 The constructors' reading record, in scope

The per-field readings the rule data needs are in scope where `hnew`
is proved: `hrec` hands the recursor stage the block's whole
representation, including

```
BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k
```

whose third clause carries, per (member `c`, constructor `j`), the
constructors' reading record `BlockCtorDataI` — the block route's
counterpart of the native route's `CtorReadR`.  `blockCtorData_of_core`
is the one-line projection that names the entry point. -/

/-- The constructors' reading record for one (member, constructor),
off the stage's core invariant. -/
theorem blockCtorData_of_core {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    {c j : Nat} {cA : ConstantVal × Nat} (hcA : (d.ctorsM c)[j]? = some cA) :
    BlockCtorDataI mpC.base2 (d.memberName c) lps cA.1 d.nP cA.2 (d.nIdxAt c) d.resSort d.isProp
      d.large (d.idxF c j) (d.dsF c j) (d.esF c j) (d.srcsF c j) (d.fvsPF c j)
      (d.xFvsF c j) (d.xrestF c j) :=
  (hcore.2.2.1 c j cA hcA).2.2.1

/-! ## A.8 The remaining components, SPELLED

`pdoms0` needed no new reading (§A.6).  The other four syntactic
components are the readings of the check's own opened frame, and they
are functions of the run: the recursor's stored type and the
constructor's stored type determine every Expr
`checkBlockRule` opens (§A.5's equations), so recomputing the same
`openPisAtFvars` / `instPisAt` here and reading the result is the
definition.  The identification — that the run's witnesses ARE these —
is `Option` determinism against the rule record (`RecKRun.ruleAt`), at the one-rule
peel of §A.9 (`blockRuleData_run`). -/

/-- The readings of an opened telescope's fvar types, each at its own
depth. -/
@[expose] def readOpenedDoms (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (ψ : Name → Nat) :
    Nat → List Expr → List AnnotTerm
  | _, [] => []
  | d, x :: xs =>
    (denoteMeta acval env ψ d x.fvarTypeD).getD default :: readOpenedDoms acval env ψ (d + 1) xs

omit [SetTheory V] in
/-- A reading of an opened telescope has one entry per opener. -/
@[simp] theorem readOpenedDoms_length_eq (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
    (ψ : Name → Nat) : ∀ (d : Nat) (fvs : List Expr),
      (readOpenedDoms acval env ψ d fvs).length = fvs.length
  | _, [] => rfl
  | d, _ :: xs => by
    simp only [readOpenedDoms, List.length_cons, readOpenedDoms_length_eq acval env ψ (d + 1) xs]

section Components

variable (p : ConLeche.BlockShape)
  (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))

/-- The `c`-th stored recursor's type. -/
@[expose] def blockRuleRecTy (c : Nat) : Expr := (rs.getD c default).1.type

/-- The `i`-th constructor the `c`-th recursor's rules run over. -/
@[expose] def blockRuleCtorOf (c i : Nat) : ConstantVal × Nat :=
  ((rs.getD c default).2.2.2).getD i default

/-- The rule's PREFIX openers: the recursor type's first `rP` binders. -/
@[expose] def blockRulePrefFvs (c : Nat) : List Expr :=
  ((ConLeche.openPisAtFvars (p.rulePrefixAt c) (blockRuleRecTy rs c) 0).map (·.1)).getD []

/-- The constructor's telescope at the rule's parameters. -/
@[expose] def blockRuleCrest (c i : Nat) : Expr :=
  ((ConLeche.Expr.instPisAt ((blockRulePrefFvs p rs c).take p.nP)
    (blockRuleCtorOf rs c i).1.type).map (·.2)).getD default

/-- The rule's FIELD openers, at the depth `rP`. -/
@[expose] def blockRuleFieldFvs (c i : Nat) : List Expr :=
  ((ConLeche.openPisAtFvars (blockRuleCtorOf rs c i).2 (blockRuleCrest p rs c i)
    (p.rulePrefixAt c)).map (·.1)).getD []

/-- The constructor's conclusion at those openers — its INDEX
expressions are `getAppArgs.drop nP`. -/
@[expose] def blockRuleCbody (c i : Nat) : Expr :=
  ((ConLeche.openPisAtFvars (blockRuleCtorOf rs c i).2 (blockRuleCrest p rs c i)
    (p.rulePrefixAt c)).map (·.2)).getD default

variable (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env) (ψ : Name → Nat)

/-- **`fdoms0`** — the constructor's field domains at the rule's frame. -/
@[expose] def blockRuleFdomsAV (c i : Nat) : List AnnotTerm :=
  readOpenedDoms acval envC ψ (p.rulePrefixAt c) (blockRuleFieldFvs p rs c i)

/-- **`es0`** — the constructor's index expressions, read at the rule's
frame. -/
@[expose] def blockRuleEsAV (c i : Nat) : List AnnotTerm :=
  ((blockRuleCbody p rs c i).getAppArgs.drop p.nP).map fun e =>
    (denoteMeta acval envC ψ (p.rulePrefixAt c + (blockRuleCtorOf rs c i).2) e).getD default

/-- **`mk0`** — the FIRED SPINE `C_J p⃗ f⃗`, read at the rule's frame. -/
@[expose] def blockRuleMkAV (c i : Nat) : AnnotTerm :=
  (denoteMeta acval envC ψ (p.rulePrefixAt c + (blockRuleCtorOf rs c i).2)
    (ConLeche.Expr.mkAppN (.const (blockRuleCtorOf rs c i).1.name (p.lps.map .param))
      ((blockRulePrefFvs p rs c).take p.nP ++ blockRuleFieldFvs p rs c i))).getD default

end Components

/-! ## A.9 The peel to ONE rule

`RecKRun.ruleAt` (`Verify/Inductives/BlockRecRun.lean`) is the peel:
from `checkBlockRecK … = .ok rs` to the `checkBlockRule` run of the
`(c, i)`-th rule, with the inputs it was called at pinned to the stored
data. -/

section Peel

open ConLeche (BlockShape BlockParts RecShape)

/-- **The `c`-th recursor's constructor list, off `checkBlockRecK`** —
it is the constructors' stage's list AT THE RECURSOR'S MEMBER
(`recTgtAt c`), and as long as that member's declared constructors.
`recStage_ctorsIdx` gives only SOME index. -/
theorem recStage_ctorsAt {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) :
    ∃ ms : ConLeche.MemberShape,
      p.members[p.toBlockShape.recTgtAt c]? = some ms ∧
      ctorsAs[p.toBlockShape.recTgtAt c]? = some r.2.2.2 ∧ r.2.2.2.length = ms.ctors.length := by
  obtain ⟨R⟩ := id h
  exact R.ctorsAt c r hm hr

/-! ### A.9b The rule's FRAME and RESIDUE, as functions of the run

`RecKRun.ruleAt` pins the rule stage's recursor-type list to the stored
recursors' types, so every frame field built from them (`ks`,
`ihKeys`) and everything downstream of the frame (the residue, the `ih`
tower, its openers) is a function of the run.  The
definitions below are the frame and everything the stage computes from
it, RECOMPUTED — the §A.8 pattern (`blockRulePrefFvs` & co.). -/

/-- **Every constructor has its rule**: the check stores one rule per
constructor of the recursor's major. -/
theorem recStage_rulesLen {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) : r.2.1.length = r.2.2.2.length := by
  obtain ⟨R⟩ := id h
  exact R.rulesLen hr


/-! ### A-1's identification: the components ARE the run's witnesses -/

/-- **The `(c, i)`-th rule's syntactic data, identified.**  Every Expr
`checkBlockRule` opened is the one §A.8's definitions recompute:
`Option` determinism against the rule record (`RecKRun.ruleAt`).

The last two rows are **G2**, the step that compares the rule's own
λ-domains with the openers' stored types binder by binder
(`checkBlockDefEqList` at the rule's typing environment, which
`RecKRun.ruleAt` shows is `envC` itself).  It is the only
input the TOWER FIT (`BlockRuleDataB`'s fifth conjunct) can have — the
fit compares `lds.map (·.2)`, the reading of `ldoms`, with
`blockRulePdomsAV ++ blockRuleFdomsAV`, the reading of exactly those
stored types. -/
theorem blockRuleData_run {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    ∃ (o₁ : Expr) (cpref : List Expr) (rbs : List (Expr × ConLeche.BinderMeta)) (body : Expr)
      (ldoms : List Expr) (lrest : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.rulePrefixAt c) r.1.type 0
          = some (blockRulePrefFvs p.toBlockShape rs c, o₁) ∧
      ConLeche.Expr.instPisAt ((blockRulePrefFvs p.toBlockShape rs c).take p.nP) cA.1.type
          = some (cpref, blockRuleCrest p.toBlockShape rs c i) ∧
      ConLeche.openPisAtFvars cA.2 (blockRuleCrest p.toBlockShape rs c i)
            (p.toBlockShape.rulePrefixAt c)
          = some (blockRuleFieldFvs p.toBlockShape rs c i,
              blockRuleCbody p.toBlockShape rs c i) ∧
      ConLeche.Expr.stripLams (p.toBlockShape.rulePrefixAt c + cA.2) rhs = some (rbs, body) ∧
      ConLeche.Expr.instLamsAt
          (blockRulePrefFvs p.toBlockShape rs c ++ blockRuleFieldFvs p.toBlockShape rs c i)
          rhs = some (ldoms, lrest) ∧
      (∀ l, l < p.toBlockShape.rulePrefixAt c + cA.2 →
        ConstsBound envC (ldoms.getD l default)) ∧
      ((blockRulePrefFvs p.toBlockShape rs c
          ++ blockRuleFieldFvs p.toBlockShape rs c i).map ConLeche.Expr.fvarTypeD).length
        = ldoms.length ∧
      (∀ l, l < ((blockRulePrefFvs p.toBlockShape rs c
            ++ blockRuleFieldFvs p.toBlockShape rs c i).map ConLeche.Expr.fvarTypeD).length →
        ConLeche.isDefEqCore μ envC F (p.toBlockShape.rulePrefixAt c + cA.2)
          (((blockRulePrefFvs p.toBlockShape rs c
              ++ blockRuleFieldFvs p.toBlockShape rs c i).map
              ConLeche.Expr.fvarTypeD).getD l default)
          (ldoms.getD l default) = .ok true) := by
  have hrd : rs.getD c default = r := by
    rw [List.getD_eq_getElem?_getD, hr]; rfl
  have hcd : r.2.2.2.getD i default = cA := by
    rw [List.getD_eq_getElem?_getD, hcA]; rfl
  have hty : blockRuleRecTy rs c = r.1.type := by rw [blockRuleRecTy, hrd]
  have hct : blockRuleCtorOf rs c i = cA := by rw [blockRuleCtorOf, hrd, hcd]
  obtain ⟨R⟩ := id h
  obtain ⟨rc, rhs0, -, -, ⟨Q⟩⟩ := R.ruleAtG hm hr hcA hrhs
  have hrecTy : Q.recTy = r.1.type := by
    have h' := Q.hrecTy
    rw [List.getElem?_map, hr] at h'
    exact (Option.some.inj h').symm
  have hop1 := Q.hpref
  rw [hrecTy] at hop1
  -- the prefix openers
  have hpref : blockRulePrefFvs p.toBlockShape rs c = Q.fvsPref := by
    rw [blockRulePrefFvs, hty, hop1]; rfl
  -- the constructor's telescope
  have hcrest : blockRuleCrest p.toBlockShape rs c i = Q.crest := by
    rw [blockRuleCrest, hpref, hct, Q.hcpar]; rfl
  -- the field openers and the body
  have hffvs : blockRuleFieldFvs p.toBlockShape rs c i = Q.fvsF := by
    rw [blockRuleFieldFvs, hcrest, hct, Q.hfld]; rfl
  have hcbody : blockRuleCbody p.toBlockShape rs c i = Q.cbody := by
    rw [blockRuleCbody, hcrest, hct, Q.hfld]; rfl
  -- the domains' count: G2's list lengths, through the two openings
  have hldlen : Q.ldoms.length = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [← Q.hG2len, List.length_map, List.length_append,
      ConLeche.Verify.openPisAtFvars_length _ hop1,
      ConLeche.Verify.openPisAtFvars_length _ Q.hfld]
  -- the domains' own resolution guard, at the constructors' environment
  have hcb : ∀ l, l < Q.ldoms.length → ConstsBound envC (Q.ldoms.getD l default) := by
    intro l hl
    refine constsBound_of_constsResolve _ ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
    exact Q.hldomsRes _ (List.getElem_mem hl)
  exact ⟨Q.oPref, Q.cpref, Q.rbs, Q.body, Q.ldoms, Q.lrest,
    by rw [hpref]; exact hop1,
    by rw [hpref, hcrest]; exact Q.hcpar,
    by rw [hcrest, hffvs, hcbody]; exact Q.hfld,
    Q.hstrip, by rw [hpref, hffvs]; exact Q.hlams,
    fun l hl => hcb l (by rw [hldlen]; exact hl),
    by rw [hpref, hffvs]; exact Q.hG2len,
    by rw [hpref, hffvs]; exact Q.hG2⟩

/-- **The stored rule's λ binder DATA, at the run** — the kernel guard
that `checkBlockRule` requires every λ binder of the stored right-hand
side's `rP + nF` telescope to carry
`Level.zeronessOf (structElimLevel p.elim p.large)`, read off the one
rule record's `hpw` (`RuleRun`). -/
theorem blockRuleBinderData_run {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    ∃ (rbs : List (Expr × ConLeche.BinderMeta)) (body : Expr),
      ConLeche.Expr.stripLams (p.toBlockShape.rulePrefixAt c + cA.2) rhs = some (rbs, body) ∧
      ∀ b ∈ rbs, b.2.pw
        = Level.zeronessOf (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) := by
  obtain ⟨R⟩ := id h
  obtain ⟨rc, rhs0, -, -, ⟨Q⟩⟩ := R.ruleAtG hm hr hcA hrhs
  exact ⟨Q.rbs, Q.body, Q.hstrip, Q.hpw⟩

/-- A spine on a head reading as the point reads as the point. -/
theorem interp_mkAppN_of_pt {ρ : Nat → V} :
    ∀ {f : AnnotTerm} (_ : interp V ρ f = pt) (as : List AnnotTerm),
      interp V ρ (AnnotTerm.mkAppN f as) = pt
  | _, hf, [] => hf
  | f, hf, a :: as => by
    rw [AnnotTerm.mkAppN_cons]
    exact interp_mkAppN_of_pt (f := .app f a) (by rw [interp_app, hf, app_pt]) as

/-- **THE `ℓ = 0` ARM'S RIGHT SIDE**: at a valuation where the family's
elimination level is zero, the stored rule reads as the POINT.

The rule's outermost λ binder carries the elimination datum (the
binder-data guard, `blockRuleBinderData_run`), `denoteMeta` turns a
binder datum into its bit at the valuation (`pwBit`), and that bit is
zero exactly when the level evaluates to zero (`pwBit_zeronessOf`) —
so the reading is `lamR 0 … = pt`.

`hpos` is the telescope's NON-EMPTINESS: a rule binding no variables
has no binder to carry the datum.  Nothing in the check forces it —
stage (b) asks only `nP ≤ rP` — and a rule binding none is read as the
point by the family's ι law instead (`blockRuleRaZ_empty`,
`BlockDeclRun.lean`); `blockRuleRaZ_seam` dispatches the two. -/
theorem blockRuleRaZ_run {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hpos : 0 < p.toBlockShape.rulePrefixAt c + cA.2)
    {acv : Name → (Name → Nat) → AnnotTerm} {env₃ : Env} {ψ : Name → Nat} {Ra : AnnotTerm}
    (hread : denoteMeta acv env₃ ψ 0 rhs = some Ra)
    (hℓ : Level.eval ψ
      (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0)
    (ρ : Nat → V) : interp V ρ Ra = pt := by
  obtain ⟨rbs, body, hstrip, hpw⟩ := blockRuleBinderData_run (hm := hm) h hr hcA hrhs
  obtain ⟨k, hk⟩ : ∃ k, p.toBlockShape.rulePrefixAt c + cA.2 = k + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hk] at hstrip
  match rhs, hstrip with
  | .lam dom bd mb, hstrip =>
    simp only [ConLeche.Expr.stripLams] at hstrip
    cases hs : bd.stripLams k with
    | none => rw [hs] at hstrip; exact nomatch hstrip
    | some q =>
      rw [hs] at hstrip
      simp only [Option.map_some, Option.some.injEq] at hstrip
      have hmb : mb.pw = Level.zeronessOf
          (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) :=
        hpw (dom, mb) (by rw [← (Prod.mk.inj hstrip).1]; exact List.mem_cons_self)
      obtain ⟨ta, ba, -, -, rfl⟩ := denoteMeta_lam_inv hread
      have hb : pwBit ψ mb.pw = 0 := by rw [hmb]; exact (pwBit_zeronessOf ψ _).mpr hℓ
      rw [interp_lam, hb, ConLeche.SetModel.lamR_zero]

/-- The recomputed constructor and right-hand side ARE the run's. -/
theorem blockRuleCtorOf_eq {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA) :
    blockRuleCtorOf rs c i = cA := by
  simp only [blockRuleCtorOf, List.getD_eq_getElem?_getD, hr, Option.getD_some, hcA]

/-- **The rule's conclusion row** — the recursor's conclusion at the
rule's prefix, the constructor's result indices and the constructed
element (the rule tower's `hconcl`), at §A.8's pinned openers. -/
theorem blockRuleConcl_run {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs) :
    ∃ concl : Expr,
      ConLeche.Expr.instPisAtLift
          (blockRulePrefFvs p.toBlockShape rs c
            ++ (blockRuleCbody p.toBlockShape rs c i).getAppArgs.drop p.nP
            ++ [ConLeche.Expr.mkAppN (.const cA.1.name (p.toBlockShape.lps.map .param))
                ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
                  ++ blockRuleFieldFvs p.toBlockShape rs c i)])
          r.1.type = some concl := by
  have hrd : rs.getD c default = r := by
    rw [List.getD_eq_getElem?_getD, hr]; rfl
  have hty : blockRuleRecTy rs c = r.1.type := by rw [blockRuleRecTy, hrd]
  have hct : blockRuleCtorOf rs c i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨R⟩ := id h
  obtain ⟨rc, rhs0, -, -, ⟨Q⟩⟩ := R.ruleAtG hm hr hcA hrhs
  have hrecTy : Q.recTy = r.1.type := by
    have h' := Q.hrecTy
    rw [List.getElem?_map, hr] at h'
    exact (Option.some.inj h').symm
  have hop1 := Q.hpref
  have hconcl := Q.hconcl
  rw [hrecTy] at hop1 hconcl
  have hpref : blockRulePrefFvs p.toBlockShape rs c = Q.fvsPref := by
    rw [blockRulePrefFvs, hty, hop1]; rfl
  have hcrest : blockRuleCrest p.toBlockShape rs c i = Q.crest := by
    rw [blockRuleCrest, hpref, hct, Q.hcpar]; rfl
  have hffvs : blockRuleFieldFvs p.toBlockShape rs c i = Q.fvsF := by
    rw [blockRuleFieldFvs, hcrest, hct, Q.hfld]; rfl
  have hcbody : blockRuleCbody p.toBlockShape rs c i = Q.cbody := by
    rw [blockRuleCbody, hcrest, hct, Q.hfld]; rfl
  exact ⟨Q.concl, by rw [hpref, hffvs, hcbody]; exact hconcl⟩

/-! ### The two peels' BODIES are one term

`blockRuleData_run` returns the `instLamsAt` run — the rule's λ-domains
and its residual `lrest` — and `blockRuleResidueData_runP` the
`stripLams` run — the binder list and the bvar-form `body` that
`abstractIh` is applied to.  The two are the SAME peel at two
spellings, and the residue's consumers need them identified: the body
equation reads `body.instantiateList as1 0` (`interp_blockResidue`'s
`hA`), while the tower's reading is stated at `lrest`
(`blockRuleTower_run`).  The identification is generic and costs one
induction: `instLamsAt` instantiates each binder as it peels, which is
`instantiateList` at the reversed opener list
(`instantiateList_append_one` is the step). -/

omit [SetTheory V] in
/-- **`instLamsAt`'s residual IS the stripped body, opened.**  A term
that λ-peels `as.length` binders both ways: `instLamsAt` returns the
body with every binder instantiated, which is `instantiateList` at
`as.reverse` — the head of the reversed list is the INNERMOST binder,
which is the one `instantiate1` applies first. -/
theorem instLamsAt_rest_eq :
    ∀ (as : List ConLeche.Expr) {e : ConLeche.Expr} {ds : List ConLeche.Expr}
      {rest : ConLeche.Expr} {bs : List (ConLeche.Expr × ConLeche.BinderMeta)}
      {body : ConLeche.Expr},
      ConLeche.Expr.instLamsAt as e = some (ds, rest) →
      ConLeche.Expr.stripLams as.length e = some (bs, body) →
      rest = body.instantiateList as.reverse 0 := by
  intro as
  induction as with
  | nil =>
    intro e ds rest bs body h1 h2
    simp only [ConLeche.Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h1
    simp only [List.length_nil, ConLeche.Expr.stripLams, Option.some.injEq,
      Prod.mk.injEq] at h2
    obtain ⟨-, rfl⟩ := h1
    obtain ⟨-, rfl⟩ := h2
    rw [List.reverse_nil, ConLeche.Expr.instantiateList_nil]
  | cons a as ih =>
    intro e ds rest bs body h1 h2
    match e with
    | .lam d b m =>
      simp only [ConLeche.Expr.instLamsAt, Option.map_eq_some_iff] at h1
      obtain ⟨⟨ds₀, rest₀⟩, hin, heq⟩ := h1
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      simp only [List.length_cons, ConLeche.Expr.stripLams, Option.map_eq_some_iff] at h2
      obtain ⟨⟨bs₀, body₀⟩, hst, heq2⟩ := h2
      simp only [Prod.mk.injEq] at heq2
      obtain ⟨-, rfl⟩ := heq2
      -- the instantiated tower still peels, and its body is the body instantiated
      have hsome : ((b.instantiate1 a 0).stripLams as.length).isSome :=
        ConLeche.Expr.stripLams_instantiate1_isSome as.length 0 (by rw [hst]; rfl)
      obtain ⟨⟨bs', body'⟩, hst'⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hbody', -⟩ := ConLeche.Expr.stripLams_instantiate1_eq as.length 0 hst hst'
      have hres := ih hin hst'
      rw [hres, hbody', List.reverse_cons,
        ConLeche.Expr.instantiateList_append_one as.reverse body₀ a 0,
        List.length_reverse]
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _
    | .forallE _ _ _ | .letE _ _ _ | .proj _ _ _ =>
      exact absurd h1 (by simp [ConLeche.Expr.instLamsAt])

end Peel

/-! ## A.10 A-2, split — the PREFIX half at the run, and what the
FIELD half is

`BlockRuleDataAt`'s second conjunct is a fit of `pdoms0 ++ fdoms0`
against `(xs.take rP) ++ (ys.drop nP)`, so `SpineFit.append` splits it
at `rP`:

* the **prefix half** — `SpineFit ρ pdoms0 ((xs.take rP).map ⟦·⟧)` —
  is `spineFit_blockRecTy` truncated: the contract's `hfitR` fits the
  stored recursor type's reading, `pdoms0` is that reading's binder
  data cut at `rP`, and a fit truncates.  That is this section;
* the **field half** — `SpineFit (consList ((xs.take rP).map ⟦·⟧) ρ)
  fdoms0 ((ys.drop nP).map ⟦·⟧)` — is NOT a truncation of the
  contract's `hfitC`.  `hfitC` fits the constructor's fields at the
  CONSTRUCTOR's own parameters (`ys.take nP`); the conjunct asks them
  to fit at the RECURSOR's (`xs.take nP`), and the rule is
  `paramsBlind`, so no run fact compares the two spines.  What
  supplies it is the block's REPRESENTATION: the major premise's
  membership (`hfitR`'s last step, at the member's carrier at `xs`'
  parameters and indices) inverts through `BlockModelAt.fibre` into
  "the value is `d.inj ψ c j fs` with `fs` fitting component `c`'s
  constructor `j` AT THOSE PARAMETERS", and `BlockModelAt.mkInj`
  identifies that `fs` with `(ys.drop nP)`'s values.  That inversion
  is the kits' `hspF`; what it leaves is the SHIFT — the rule's field
  domains are the block's `d.Fss` read `rP − nP` deeper, because the
  rule's prefix carries the recursor's `nP … rP-1` stretch:

  ```
  blockRuleFdomsAV acval envC p rs ψ c i
    = liftDomsK (p.rulePrefixAt c - p.nP) 0 ((d.Fss c ψ).getD i [])
  ```

  (the same `o = rP − nP` shift the `ih` spine fold carries).  That
  identity (§A.13) and its twins for `es0`/`mk0` are reading
  identifications between the CHECK's opened frame (parameters at
  fvars `0 … nP-1`, fields at `rP … rP+nF-1`) and the CONSTRUCTORS'
  stage's (`d.fvsPF`/`d.xFvsF`, at `0 … nP+nF-1`) — the same Exprs
  opened at different fvar bases and read at different depths. -/

section HspRun

open ConLeche (BlockParts)

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **A-2's PREFIX half, generically**: whatever fits the `c`-th
stored recursor type's reading fits its first `rP` binder domains —
`spineFit_blockRecTy` truncated at the rule's prefix. -/
theorem spineFit_blockRulePdomsAV (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat)
    {ρ : Nat → V} {ws : List AnnotTerm} {rest TVa : AnnotTerm}
    (hTVa : denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some TVa)
    (hlen : ws.length = p.toBlockShape.majorIdxAt c + 1)
    (hfit : TeleFitPA V ρ TVa ws rest) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      ((ws.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)) := by
  have hsp := spineFit_blockRecTy hμ mpC h hr ψ hTVa hlen hfit
  obtain ⟨-, -, -, -, -, hrdsLen, -⟩ := recStage_tyPis hμ mpC h hr ψ
  have hle := blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  have hpre := spineFit_take hsp (i := p.toBlockShape.rulePrefixAt c)
    (by rw [List.length_map, hrdsLen]; omega)
  rw [blockRulePdomsAV, List.map_take, List.map_take]
  exact hpre

/-- **A-2's prefix half at the contract's own spine**: the fit
`RecRuleLaw` hands (`hfitR`, at `xs ++ [C ys]`) restricted to the
rule's prefix. -/
theorem spineFit_blockRulePdomsAV_app (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat)
    {ρ : Nat → V} {xs : List AnnotTerm} {maj rest TVa : AnnotTerm}
    (hTVa : denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some TVa)
    (hxl : xs.length = p.toBlockShape.majorIdxAt c)
    (hfit : TeleFitPA V ρ TVa (xs ++ [maj]) rest) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)) := by
  have hle : p.toBlockShape.rulePrefixAt c ≤ xs.length := by
    rw [hxl]
    exact blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  have hq := spineFit_blockRulePdomsAV hμ mpC h hr ψ hTVa
    (by rw [List.length_append, List.length_singleton, hxl]) hfit
  rwa [List.take_append_of_le_length hle] at hq

end HspRun

/-! ## A.13 The `rP − nP` SHIFT — the rule's field domains ARE the
block's, read deeper

The rule opens the constructor's telescope with the parameters at
fvars `0 … nP-1` (the RECURSOR's prefix openers) and the fields at
`rP … rP+nF-1`; the constructors' stage opens the SAME telescope at
`0 … nP+nF-1`.  Reading an opened fvar `i` at depth `d` gives
`.bvar (d-1-i)`, so the two readings differ exactly by a lift of
`rP − nP` at each entry's own cutoff — the `o = rP − nP` shift the
`ih` spine fold carries.

The move is not to compare two openings but to read ONE instantiated
telescope (`crest`, whose free variables are the `nP` parameter
openers) at the DEEPER depth: that is `ctorResidual_read_lift`
(`StructRecRead.lean`), `denoteMeta_lift` through `liftN_mkPisAV`.
`denoteMeta_openPis` then hands the shifted tower's binder data back as
the opened fvars' readings, and the two frames' `crest`s are `ErasedEq`
because the reading is blind to an opener's annotation. -/

section Shift

variable {acval : Name → (Name → Nat) → AnnotTerm} {envC : Env} {ψ : Name → Nat}

omit [SetTheory V] in
/-- A binder list's domains survive the lifting: `liftDoms` on the
triples is `liftDomsK` on their domains. -/
theorem map_liftDoms (m : Nat) :
    ∀ (k : Nat) (ds : List (Nat × Nat × AnnotTerm)),
      (liftDoms m k ds).map (·.2.2) = liftDomsK m k (ds.map (·.2.2))
  | _, [] => rfl
  | k, _ :: ds => by
    show _ :: (liftDoms m (k + 1) ds).map (·.2.2) = _ :: liftDomsK m (k + 1) (ds.map (·.2.2))
    rw [map_liftDoms m (k + 1) ds]

omit [SetTheory V] in
/-- `readOpenedDoms` is the binder data, whenever every opener reads to
its own entry. -/
theorem readOpenedDoms_eq :
    ∀ (fvs : List Expr) (pps : List (Nat × Nat × AnnotTerm)) (dpt : Nat),
      fvs.length = pps.length →
      (∀ (i : Nat) (x : Expr), fvs[i]? = some x →
        ∃ pd, pps[i]? = some pd ∧ denoteMeta acval envC ψ (dpt + i) x.fvarTypeD = some pd.2.2) →
      readOpenedDoms acval envC ψ dpt fvs = pps.map (·.2.2)
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, hl, _ => nomatch hl
  | _ :: _, [], _, hl, _ => nomatch hl
  | x :: fvs, pd :: pps, dpt, hl, hb => by
    obtain ⟨pd', hpd', hx⟩ := hb 0 x rfl
    obtain rfl : pd' = pd := Option.some.inj hpd'.symm
    rw [Nat.add_zero] at hx
    show (denoteMeta acval envC ψ dpt x.fvarTypeD).getD default
        :: readOpenedDoms acval envC ψ (dpt + 1) fvs = _
    rw [hx, Option.getD_some,
      readOpenedDoms_eq fvs pps (dpt + 1) (by simpa using hl)
        (fun i y hy => by
          obtain ⟨q, hq, hd⟩ := hb (i + 1) y (by simpa using hy)
          exact ⟨q, by simpa using hq, by rw [show dpt + 1 + i = dpt + (i + 1) from by omega]; exact hd⟩)]
    rfl

/-- **The shift, generically.**  Reading the constructor's
parameter-instantiated telescope at the RULE's depth `nP + o` gives the
constructors' stage's binder data lifted by `o`, and its body lifted at
the fields' cutoff. -/
theorem readOpenedDoms_shift {m : EnvModel V envC}
    {crest crest' : Expr} {ds : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm}
    {nP nF o : Nat}
    (hread : denoteMeta m.acval envC ψ nP crest = some (mkPisAV (ds.drop nP) bodyC))
    (hw : Expr.WScoped nP crest) (hlenD : ds.length = nP + nF)
    (heq : Expr.ErasedEq crest crest')
    {fvsF : List Expr} {cbody : Expr}
    (hop : ConLeche.openPisAtFvars nF crest' (nP + o) = some (fvsF, cbody)) :
    readOpenedDoms m.acval envC ψ (nP + o) fvsF
        = liftDomsK o 0 ((ds.drop nP).map (·.2.2)) ∧
      denoteMeta m.acval envC ψ (nP + o + nF) cbody = some (bodyC.liftN o nF) ∧
      (∀ (l : Nat) (x : Expr), fvsF[l]? = some x →
        denoteMeta m.acval envC ψ (nP + o + l) x.fvarTypeD
          = some ((liftDomsK o 0 ((ds.drop nP).map (·.2.2))).getD l default)) := by
  have hlenDrop : (ds.drop nP).length = nF := by
    rw [List.length_drop, hlenD]; omega
  have hread' : denoteMeta m.acval envC ψ (nP + o) crest'
      = some (mkPisAV (liftDoms o 0 (ds.drop nP)) (bodyC.liftN o nF)) := by
    rw [← denoteMeta_erasedEq heq]
    exact ctorResidual_read_lift hread hw hlenD o
  obtain ⟨pps, b, hst, hb, hlen, hbind⟩ := denoteMeta_openPis nF hop hread'
  have hstEq := stripPisAV_mkPisAV (liftDoms o 0 (ds.drop nP)) (bodyC.liftN o nF)
  rw [liftDoms_length, hlenDrop] at hstEq
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst.symm.trans hstEq))
  refine ⟨?_, hb, fun l x hx => ?_⟩
  · rw [readOpenedDoms_eq (acval := m.acval) (envC := envC) (ψ := ψ) fvsF
        (liftDoms o 0 (ds.drop nP)) (nP + o)
        (by rw [openPisAtFvars_length _ hop, liftDoms_length, hlenDrop])
        (fun i x hx => by
          obtain ⟨q, hq, -, hd⟩ := hbind i x hx
          exact ⟨q, hq, hd⟩)]
    exact map_liftDoms o 0 (ds.drop nP)
  · obtain ⟨q, hq, -, hd⟩ := hbind l x hx
    rw [hd, ← map_liftDoms o 0 (ds.drop nP), List.getD_eq_getElem?_getD,
      List.getElem?_map, hq]
    rfl

omit [SetTheory V] in
/-- Renaming by the identity is the identity — the bridge from
`instPisAt_renEq` (stated at `RenEqT`) to `ErasedEq`. -/
theorem renameConsts_id : ∀ e : Expr, e.renameConsts (fun n => n) = e
  | .bvar _ | .sort _ | .const _ _ | .lit _ => rfl
  | .fvar _ ty => by rw [ConLeche.Expr.renameConsts, renameConsts_id ty]
  | .app f a => by rw [ConLeche.Expr.renameConsts, renameConsts_id f, renameConsts_id a]
  | .lam ty b m => by rw [ConLeche.Expr.renameConsts, renameConsts_id ty, renameConsts_id b]
  | .forallE ty b m => by rw [ConLeche.Expr.renameConsts, renameConsts_id ty, renameConsts_id b]
  | .letE ty v b => by
    rw [ConLeche.Expr.renameConsts, renameConsts_id ty, renameConsts_id v, renameConsts_id b]
  | .proj sn i e => by rw [ConLeche.Expr.renameConsts, renameConsts_id e]

/-- **A-2's FIELD DOMAINS, at the run.**  The rule's field domains ARE
the constructors' stage's, read `rP − nP` deeper — the identity the
kits' `hspF` needs, and the last reading fact between
`BlockRuleDataAt`'s second conjunct and the block's representation.

**Two conjuncts**: the equation, and the per-opener READINGS (`hdF`,
the tower fit's second input, §6c of `BlockRuleFit.lean`), which
`readOpenedDoms_shift` computes on the way to it —
`readOpenedDoms_eq`'s hypothesis is exactly `hdF`, so the statement is
free at this frame and nowhere else. -/
theorem blockRuleFdomsAV_eq {envC : Env} {mpC : EnvModelM V μ envC}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {T : Name} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr}
    (hcd : BlockCtorDataI mpC.base2 T lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs fvsP xFvs xrest)
    (hCf : cA.1.type.hasFvar = false)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) :
    blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
        = liftDomsK (p.toBlockShape.rulePrefixAt c - p.nP) 0
            (((ds ψ).drop p.nP).map (·.2.2)) ∧
      (∀ (l : Nat) (x : Expr), (blockRuleFieldFvs p.toBlockShape rs c i)[l]? = some x →
        denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + l)
            (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD
              l default)) := by
  obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, hopPref, hinst, hopF, -, -, -, -, -⟩ :=
    blockRuleData_run (hm := hm) h hr hcA hrhs
  obtain ⟨crest, hopP, hopX⟩ := hcd.opens
  -- the stage's reading of the parameter-instantiated telescope
  obtain ⟨pps₀, b₀, hst₀, hb₀, -, -⟩ := denoteMeta_openPis p.nP hopP (hcd.read ψ)
  have hstTake := stripPisAV_mkPisAV_take p.nP (ds ψ)
    (ctorBodyAVI mpC.base2 T p.nP cA.2 ψ (Es ψ)) (by rw [hcd.len ψ]; omega)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst₀.symm.trans hstTake))
  rw [Nat.zero_add] at hb₀
  -- the telescope is scoped at the parameters
  have hwT : Expr.WScoped 0 cA.1.type := Expr.WScoped.of_not_hasFvar hCf
  have hwC : Expr.WScoped p.nP crest := by
    have := (ConLeche.openPisAtFvars_WScoped p.nP cA.1.type 0 hopP hwT).2
    rwa [Nat.zero_add] at this
  -- the two frames' telescopes are erasure-equal
  have hlenPref : (blockRulePrefFvs p.toBlockShape rs c).length
      = p.toBlockShape.rulePrefixAt c := openPisAtFvars_length _ hopPref
  have hidxPref := ConLeche.openPisAtFvars_index _ _ _ hopPref
  have hargs : ∀ (k : Nat) (a a' : Expr), fvsP[k]? = some a →
      ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)[k]? = some a' →
      ConLeche.Verify.RenEqT (fun n => n) a a' := by
    intro k a a' ha ha'
    obtain ⟨ty, rfl⟩ := hcd.pIdx k a ha
    have hk : k < p.nP := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha'
      rw [List.length_take] at hlt
      omega
    have ha'' : (blockRulePrefFvs p.toBlockShape rs c)[k]? = some a' := by
      have ht : (List.take p.nP (blockRulePrefFvs p.toBlockShape rs c))[k]?
          = (blockRulePrefFvs p.toBlockShape rs c)[k]? := by
        rw [List.getElem?_take, if_pos hk]
      rw [← ht]; exact ha'
    obtain ⟨ty', rfl⟩ := hidxPref k a' ha''
    rw [Nat.zero_add]
    exact ConLeche.Verify.RenEqT.fvar
  have hinstP : ConLeche.Expr.instPisAt fvsP cA.1.type
      = some (fvsP.map ConLeche.Expr.fvarTypeD, crest) :=
    ConLeche.Verify.openPisAtFvars_instPisAt _ hopP
  obtain ⟨-, hrenC⟩ := ConLeche.Verify.instPisAt_renEq (f := fun n => n) fvsP
    ((blockRulePrefFvs p.toBlockShape rs c).take p.nP) hinstP hinst
    (by show Expr.ErasedEq _ _; rw [renameConsts_id]; exact Expr.ErasedEq.rfl _)
    hargs
    (by rw [hcd.pLen, List.length_take, hlenPref]; omega)
  have heq : Expr.ErasedEq crest (blockRuleCrest p.toBlockShape rs c i) := by
    have := hrenC
    rwa [ConLeche.Verify.RenEqT, renameConsts_id] at this
  -- the shift
  have hsh := readOpenedDoms_shift (m := mpC.base2) (ψ := ψ)
    (o := p.toBlockShape.rulePrefixAt c - p.nP) hb₀ hwC (hcd.len ψ) heq
    (by rw [show p.nP + (p.toBlockShape.rulePrefixAt c - p.nP)
          = p.toBlockShape.rulePrefixAt c from by omega]
        exact hopF)
  have hq := hsh.1
  have hrd := hsh.2.2
  rw [show p.nP + (p.toBlockShape.rulePrefixAt c - p.nP)
      = p.toBlockShape.rulePrefixAt c from by omega] at hq hrd
  have heqF : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - p.nP) 0
          (((ds ψ).drop p.nP).map (·.2.2)) := by
    rw [blockRuleFdomsAV]; exact hq
  exact ⟨heqF, fun l x hx => by rw [heqF]; exact hrd l x hx⟩

/-- **A-2's FIELD DOMAINS in the CERTIFICATES' spelling** — the
same identity as `blockRuleFdomsAV_eq` with the lifting on the
TRIPLES instead of on their domains.

`blockRuleFseg_of_run` (`BlockRecPreRun.lean`) states the field
segment's grading at `(liftDoms o 0 (ds.drop nP)).map (·.2.2)` — it
lifts the binder data and reads the domains off — while the
certificate bundle's `fdoms` is `blockRuleFdomsAV`, a
`readOpenedDoms`.  The two spellings are the two sides of
`map_liftDoms`, so this is that theorem composed with the identity and
nothing else; it is stated because the consumer plugs `ds` and `o` in
as parameters and cannot rewrite a premise it does not own. -/
theorem blockRuleFdomsAV_eq_liftDoms {envC : Env} {mpC : EnvModelM V μ envC}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {T : Name} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr}
    (hcd : BlockCtorDataI mpC.base2 T lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs fvsP xFvs xrest)
    (hCf : cA.1.type.hasFvar = false)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) {o : Nat}
    (ho : p.toBlockShape.rulePrefixAt c = p.nP + o) (ψ : Name → Nat) :
    blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = (liftDoms o 0 ((ds ψ).drop p.nP)).map (·.2.2) := by
  have hoq : p.toBlockShape.rulePrefixAt c - p.nP = o := by omega
  rw [(blockRuleFdomsAV_eq (hm := hm) h hr hcA hrhs hcd hCf hnP ψ).1, hoq, map_liftDoms]

/-- **A-3's `mk0`, at the run**: the FIRED SPINE's reading is the
constructor's leaf applied to the rule frame's parameter and field
slots.  No stage comparison is needed — the term the check builds is a
constant applied to openers, and the reading of an opener is its de
Bruijn slot. -/
theorem blockRuleMkAV_eq {envC : Env} {mpC : EnvModelM V μ envC}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {ci : ConstantInfo}
    (hfind : envC.find? cA.1.name = some ci)
    (hlps : ci.toConstantVal.levelParams = p.lps)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) :
    blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = AnnotTerm.mkAppN
          (mpC.base2.acval cA.1.name (Level.substFn ψ p.lps (p.lps.map Level.param)))
          (paramBvarsAt p.nP (p.toBlockShape.rulePrefixAt c + cA.2)
            ++ (List.range cA.2).map fun k =>
                  AnnotTerm.bvar (p.toBlockShape.rulePrefixAt c + cA.2 - 1
                    - (p.toBlockShape.rulePrefixAt c + k))) := by
  obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, hopPref, hinst, hopF, -, -, -, -, -⟩ :=
    blockRuleData_run (hm := hm) h hr hcA hrhs
  have hrd : rs.getD c default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
  have hcdd : r.2.2.2.getD i default = cA := by rw [List.getD_eq_getElem?_getD, hcA]; rfl
  have hct : blockRuleCtorOf rs c i = cA := by rw [blockRuleCtorOf, hrd, hcdd]
  have hlenPref : (blockRulePrefFvs p.toBlockShape rs c).length
      = p.toBlockShape.rulePrefixAt c := openPisAtFvars_length _ hopPref
  have hidxPref := ConLeche.openPisAtFvars_index _ _ _ hopPref
  have hlenF : (blockRuleFieldFvs p.toBlockShape rs c i).length = cA.2 :=
    openPisAtFvars_length _ hopF
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hopF
  -- the head
  have hconst : denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2)
      (.const cA.1.name (p.lps.map Level.param))
      = some (mpC.base2.acval cA.1.name (Level.substFn ψ p.lps (p.lps.map Level.param))) := by
    rw [denoteMeta]
    simp only [hfind, hlps]
    rw [if_pos (by rw [List.length_map])]
  -- the parameter openers
  have hlenTake : ((blockRulePrefFvs p.toBlockShape rs c).take p.nP).length = p.nP := by
    rw [List.length_take, hlenPref]; omega
  have hidxTake : ∀ (k : Nat) (x : Expr),
      ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by
    intro k x hx
    have hk : k < p.nP := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hx
      rw [hlenTake] at hlt
      exact hlt
    have hx' : (blockRulePrefFvs p.toBlockShape rs c)[k]? = some x := by
      have ht : ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)[k]?
          = (blockRulePrefFvs p.toBlockShape rs c)[k]? := by
        rw [List.getElem?_take, if_pos hk]
      rw [← ht]; exact hx
    obtain ⟨ty, hty⟩ := hidxPref k x hx'
    exact ⟨ty, by rw [hty, Nat.zero_add]⟩
  have hspP := denoteMetaSpine_params (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (p.toBlockShape.rulePrefixAt c + cA.2) hlenTake hidxTake
  -- the field openers
  have hspF := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (p.toBlockShape.rulePrefixAt c + cA.2) (blockRuleFieldFvs p.toBlockShape rs c i)
    (p.toBlockShape.rulePrefixAt c) hidxF
  rw [hlenF] at hspF
  rw [blockRuleMkAV, hct,
    denoteMeta_mkAppN_of _ hconst (DenoteMetaSpine.append hspP hspF), Option.getD_some]

omit [SetTheory V] in
/-- A frame substitution does not touch a constant. -/
theorem instSeq_const : ∀ (as : List Expr) (t : Nat) (n : Name) (us : List Level),
    Expr.instSeq as t (Expr.const n us) = Expr.const n us
  | [], _, _, _ => rfl
  | a :: as, t, n, us => by
    show Expr.instSeq as (t - 1) ((Expr.const n us).instantiate1 a t) = _
    rw [show (Expr.const n us).instantiate1 a t = Expr.const n us from rfl,
      instSeq_const as (t - 1) n us]

omit [SetTheory V] in
/-- A read spine's `getD` map IS the spine. -/
theorem denoteMetaSpine_map_getD {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      as.map (fun e => (denoteMeta acval env φ d e).getD default) = vs
  | _, _, .nil => rfl
  | _, _, .cons hx hsp => by
    rw [List.map_cons, hx, Option.getD_some, denoteMetaSpine_map_getD hsp]

/-- **A-3's `es0`, at the run**: the constructor's INDEX expressions,
read at the rule's frame, are the constructors' stage's index readings
lifted by `rP − nP` at the fields' cutoff.

The body's reading is `readOpenedDoms_shift`'s second component; what
this adds is the SPINE inversion — the opened residual is the member's
constant applied to the parameter slots and the index expressions
(`CtorDataI.resid`), so `denoteMeta_mkAppN_inv` against the lifted
`ctorBodyAVI` identifies the arguments one by one. -/
theorem blockRuleEsAV_eq {envC : Env} {mpC : EnvModelM V μ envC}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {T : Name} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)}
    {fvsP xFvs : List Expr} {xrest : Expr}
    (hcd : BlockCtorDataI mpC.base2 T lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs fvsP xFvs xrest)
    (hCf : cA.1.type.hasFvar = false)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) :
    blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = (Es ψ).map (·.liftN (p.toBlockShape.rulePrefixAt c - p.nP) cA.2) := by
  obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, hopPref, hinst, hopF, -, -, -, -, -⟩ :=
    blockRuleData_run (hm := hm) h hr hcA hrhs
  obtain ⟨crest, hopP, hopX⟩ := hcd.opens
  -- the shift's body half (`readOpenedDoms_shift`)
  obtain ⟨pps₀, b₀, hst₀, hb₀, -, -⟩ := denoteMeta_openPis p.nP hopP (hcd.read ψ)
  have hstTake := stripPisAV_mkPisAV_take p.nP (ds ψ)
    (ctorBodyAVI mpC.base2 T p.nP cA.2 ψ (Es ψ)) (by rw [hcd.len ψ]; omega)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst₀.symm.trans hstTake))
  rw [Nat.zero_add] at hb₀
  have hwC : Expr.WScoped p.nP crest := by
    have := (ConLeche.openPisAtFvars_WScoped p.nP cA.1.type 0 hopP
      (Expr.WScoped.of_not_hasFvar hCf)).2
    rwa [Nat.zero_add] at this
  have hlenPref : (blockRulePrefFvs p.toBlockShape rs c).length
      = p.toBlockShape.rulePrefixAt c := openPisAtFvars_length _ hopPref
  have hidxPref := ConLeche.openPisAtFvars_index _ _ _ hopPref
  have hargs : ∀ (k : Nat) (a a' : Expr), fvsP[k]? = some a →
      ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)[k]? = some a' →
      ConLeche.Verify.RenEqT (fun n => n) a a' := by
    intro k a a' ha ha'
    obtain ⟨ty, rfl⟩ := hcd.pIdx k a ha
    have hk : k < p.nP := by
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp ha'
      rw [List.length_take] at hlt
      omega
    have ha'' : (blockRulePrefFvs p.toBlockShape rs c)[k]? = some a' := by
      have ht : ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)[k]?
          = (blockRulePrefFvs p.toBlockShape rs c)[k]? := by
        rw [List.getElem?_take, if_pos hk]
      rw [← ht]; exact ha'
    obtain ⟨ty', rfl⟩ := hidxPref k a' ha''
    rw [Nat.zero_add]
    exact ConLeche.Verify.RenEqT.fvar
  obtain ⟨-, hrenC⟩ := ConLeche.Verify.instPisAt_renEq (f := fun n => n) fvsP
    ((blockRulePrefFvs p.toBlockShape rs c).take p.nP)
    (ConLeche.Verify.openPisAtFvars_instPisAt _ hopP) hinst
    (by show Expr.ErasedEq _ _; rw [renameConsts_id]; exact Expr.ErasedEq.rfl _)
    hargs
    (by rw [hcd.pLen, List.length_take, hlenPref]; omega)
  have heq : Expr.ErasedEq crest (blockRuleCrest p.toBlockShape rs c i) := by
    have := hrenC
    rwa [ConLeche.Verify.RenEqT, renameConsts_id] at this
  have hsh := readOpenedDoms_shift (m := mpC.base2) (ψ := ψ)
    (o := p.toBlockShape.rulePrefixAt c - p.nP) hb₀ hwC (hcd.len ψ) heq
    (by rw [show p.nP + (p.toBlockShape.rulePrefixAt c - p.nP)
          = p.toBlockShape.rulePrefixAt c from by omega]
        exact hopF)
  have hcb : denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2)
      (blockRuleCbody p.toBlockShape rs c i)
      = some ((ctorBodyAVI mpC.base2 T p.nP cA.2 ψ (Es ψ)).liftN
          (p.toBlockShape.rulePrefixAt c - p.nP) cA.2) := by
    have := hsh.2.1
    rwa [show p.nP + (p.toBlockShape.rulePrefixAt c - p.nP)
        = p.toBlockShape.rulePrefixAt c from by omega] at this
  -- the residual's SYNTACTIC spine
  obtain ⟨cbs, es, hresid, hlenes⟩ := hcd.resid
  have hlenSp : ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
      ++ blockRuleFieldFvs p.toBlockShape rs c i).length = p.nP + cA.2 := by
    rw [List.length_append, List.length_take, hlenPref, openPisAtFvars_length _ hopF]
    omega
  obtain ⟨ds', hcomb'⟩ := ConLeche.instPisAt_of_stripPis
    ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
      ++ blockRuleFieldFvs p.toBlockShape rs c i) (by rw [hlenSp]; exact hresid)
  have hcbEq : blockRuleCbody p.toBlockShape rs c i
      = Expr.mkAppN (.const T (lps.map Level.param))
          ((ConLeche.structPsAt cA.2 p.nP ++ es).map
            (Expr.instSeq ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
              ++ blockRuleFieldFvs p.toBlockShape rs c i)
              (((blockRulePrefFvs p.toBlockShape rs c).take p.nP
                ++ blockRuleFieldFvs p.toBlockShape rs c i).length - 1) ·)) := by
    have h1 : blockRuleCbody p.toBlockShape rs c i
        = Expr.instSeq ((blockRulePrefFvs p.toBlockShape rs c).take p.nP
            ++ blockRuleFieldFvs p.toBlockShape rs c i)
          (((blockRulePrefFvs p.toBlockShape rs c).take p.nP
            ++ blockRuleFieldFvs p.toBlockShape rs c i).length - 1)
          (Expr.mkAppN (.const T (lps.map Level.param))
            (ConLeche.structPsAt cA.2 p.nP ++ es)) :=
      congrArg Prod.snd (Option.some.inj
        ((ConLeche.Verify.Expr.instPisAt_append _ hinst
          (ConLeche.Verify.openPisAtFvars_instPisAt _ hopF)).symm.trans hcomb'))
    rw [h1, Expr.instSeq_mkAppN, instSeq_const]
  have hlenArgs : (ConLeche.structPsAt cA.2 p.nP ++ es).length = p.nP + nIdx := by
    rw [List.length_append, ConLeche.structPsAt, List.length_map, List.length_range, hlenes]
  -- the reading, inverted
  obtain ⟨fa, vs, -, hspine, hbeq⟩ := denoteMeta_mkAppN_inv (hcbEq ▸ hcb)
  have hlift : (ctorBodyAVI mpC.base2 T p.nP cA.2 ψ (Es ψ)).liftN
      (p.toBlockShape.rulePrefixAt c - p.nP) cA.2
      = AnnotTerm.mkAppN
          ((mpC.base2.acval T ψ).liftN (p.toBlockShape.rulePrefixAt c - p.nP) cA.2)
          ((paramBvars p.nP cA.2 ++ Es ψ).map
            (·.liftN (p.toBlockShape.rulePrefixAt c - p.nP) cA.2)) := by
    rw [ctorBodyAVI, liftN_mkAppN]
  have hlenVs : vs.length = ((paramBvars p.nP cA.2 ++ Es ψ).map
      (·.liftN (p.toBlockShape.rulePrefixAt c - p.nP) cA.2)).length := by
    rw [← hspine.length, List.length_map, List.length_map, List.length_append,
      List.length_append, paramBvars, List.length_map, List.length_range,
      ConLeche.structPsAt, List.length_map, List.length_range, hlenes, hcd.lenE ψ]
  obtain ⟨-, rfl⟩ := mkAppN_inj_args (hlift ▸ hbeq) hlenVs.symm
  -- the index arguments
  have hmap := denoteMetaSpine_map_getD hspine
  have hrd : rs.getD c default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
  have hcdd : r.2.2.2.getD i default = cA := by rw [List.getD_eq_getElem?_getD, hcA]; rfl
  have hct : blockRuleCtorOf rs c i = cA := by rw [blockRuleCtorOf, hrd, hcdd]
  rw [blockRuleEsAV, hct, hcbEq, Expr.getAppArgs_mkAppN,
    show (Expr.const T (lps.map Level.param)).getAppArgs = [] from rfl, List.nil_append]
  rw [List.map_drop, hmap, List.map_append, List.drop_left' (by
    rw [List.length_map, paramBvars, List.length_map, List.length_range])]

end Shift

/-! ## A.14 A-4's ENVIRONMENT premises

`ihSpineFold_blockRec` opens with three facts about the leaf valuation
— it is closed at every lift, fixed by every instantiation, and its
reading does not depend on the environment.  All three are `EnvModel`
fields, or one lemma away from one; naming them here is what lets the
A-4 assembly pass them by `exact` instead of re-deriving them at each
of the ~15 premise slots. -/


/-! ## A.15 A-4's CALLEE premise, at the run

`ihSpineFold_blockRec`'s `hcallee` is the one premise no amount of
substitution algebra produces: a guarded call's head is the CONSTANT
`rec_{c'}`, while the design's ih tower reads its head off the chain
frame, and what ties the two is the LEAF's value.  Its three conjuncts
are

* the callee is stored — the recursors' cons finds it
  (`find?_consBlockRecsR_at` below);
* the call's level arguments have the callee's arity — the block's
  recursors share their `levelParams` (`recStage_lps`), and the
  frame's `rlvls` is that very list, as `.param`s;
* the callee's leaf IS the chain's `c'`-th component — the valuation's
  definition (`blockRecAcvOf_at`) against the tuple `blockRecAV_facts`
  chooses, which is the hypothesis `blockRecRuleLaw_run`'s `hrhs`
  carries (`∀ a, (∀ c' < K, ⟦leaf c'⟧ = a c') → …`).

Nothing here is about the rule body; the premise is about the BLOCK. -/

section Callee

open ConLeche (BlockParts nameIdxOf? sumRules)

/-- **The recursors' cons FINDS its own members.**  The inversion
(`find?_consBlockRecs_inv`) says a name found above the `k` records is
one of them; this is the converse, and it is what `hcallee`'s first
conjunct is.  `Nodup` is what makes the position `j` the one the
lookup reaches, and `hfr` is what keeps a member from being shadowed
by the environment below. -/
theorem find?_consBlockRecsR_at {q : BlockShape} :
    ∀ {m : Nat} {rs : List RecDatum} {env : Env},
      (rs.map (·.1.name)).Nodup →
      (∀ r ∈ rs, env.find? r.1.name = none) →
      ∀ {j : Nat} {r : RecDatum}, rs[j]? = some r →
        (ConLeche.consBlockRecsR R q m rs env).find? r.1.name
          = some (.recInfo r.1 (q.majorIdxAt (m + j)) (q.rulePrefixAt (m + j)) (R (m + j) r))
  | _, [], _, _, _, j, r, hj => nomatch hj
  | m, r0 :: rest, env, hnd, hfr, j, r, hj => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    cases j with
    | zero =>
      obtain rfl := Option.some.inj hj
      rw [ConLeche.consBlockRecsR,
        ConLeche.find?_consBlockRecsR_of_ne (fun x hx hh => hnd.1 (by
          rw [hh]; exact List.mem_map_of_mem hx)),
        ConLeche.Env.find?_cons]
      split
      · rw [Nat.add_zero]
      · next hh => exact absurd rfl hh
    | succ j =>
      have hrest : ∀ x ∈ rest, (Env.mk (ConstantInfo.recInfo r0.1 (q.majorIdxAt m)
          (q.rulePrefixAt m) (R m r0) :: env.consts)).find? x.1.name = none := by
        intro x hx
        rw [ConLeche.Env.find?_cons]
        split
        · next hh =>
          exact absurd (show r0.1.name ∈ rest.map (·.1.name) from by
            rw [show r0.1.name = x.1.name from hh]; exact List.mem_map_of_mem hx) hnd.1
        · exact hfr x (List.mem_cons_of_mem _ hx)
      rw [ConLeche.consBlockRecsR]
      have hq := find?_consBlockRecsR_at (q := q)
        (m := m + 1) hnd.2 hrest (j := j) (r := r) (by simpa using hj)
      rw [show m + 1 + j = m + (j + 1) from by omega] at hq
      exact hq

variable {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {rs : List RecDatum} {F : Nat}

/-- **The frame's recursor names ARE the stored data's.**  The rule
stage is called at `p.recs.map (·.cvR.name)`
(`RecKRun.ruleAt`) and `checkConstantVal` stores the record's
name unchanged, so the two spellings agree list-wise. -/
theorem recStage_recNamesEq
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR) :
    p.recs.map (·.cvR.name) = rs.map (·.1.name) := by
  obtain ⟨-, hlenR, hall⟩ := recStageG_recNames h
  refine List.ext_getElem? (fun n => ?_)
  rw [List.getElem?_map, List.getElem?_map]
  rcases Nat.lt_or_ge n p.recs.length with hn | hn
  · obtain ⟨rc, r, hrc, hr, hnm, -⟩ := hall n hn
    rw [hrc, hr]
    exact congrArg some hnm.symm
  · rw [List.getElem?_eq_none hn, List.getElem?_eq_none (by omega)]
    rfl

end Callee

/-! ## A.16 `hfit`'s discharge, steps 1 and 2

The fold carries the OCCURRENCE (`IhTyped`), and
`certs_of_infer_mkAppN` turns a `.full` spine derivation into a
`Certs` walk.  The two meet here, and what the composition needs of
the run is one number: the `ih` opener's stored type has at least as
many leading `∀`s as the call has arguments — which is `blockIhPis`'
own shape (`Expr.mkPisOf (structTeleAt …) concl`, whose tower is the
field's telescope) read off `checkBlockRule`'s third opening.

The `Certs` walk's SEMANTICS — `certs_sound` at the frame's
`CtxOk`/`Sat`, the reading of the opener type as a `mkPisAV` tower, and
the two transports (the residue frame's argument readings to the body
frame's, and the `d`-shift of the ih telescope) — is §A.18; none of it
is a fact about the check. -/


/-! ## A.17b `hfld` at BOTH environments

The composition needs the field's readings TWICE: the OPENER's tower
is read at `envC`, where the check ran and where the opener's stored
type lives, and the generated CALL's tower at the CONSED environment,
because its conclusion mentions the recursor constant.  The
constructors' stage gives the `envC` one (`blockFieldReadAt_of`), and
the transport is the mono lemma's own direction — its
`ConstsBound envC` premise comes off the constructor's stored type by
four structural steps. -/


/-! ## A.18 `hfit`, CLOSED

The pieces: the `Certs` walk off the residue's own typing
(`certs_of_ihCall`), the context it is sound at (`WalkCtx`), the
opener's stored type (`blockIhOpener_stored`) and its reading
(`denoteMeta_blockIhOpenerTy_deep_exists`).  The composition is three
moves:

1. `certs_sound` at the walk's context — `Frame`/`CtxOk`/`Graded` for
   the head's stored type is `WalkCtx.annotOk`, for the arguments
   `WalkCtx.subjOk`;
2. `spineFit_of_teleFitPA` at the opener's reading, then the DOUBLE
   shift: the telescope's `ihTeleAtR_shiftAt` down to the design's
   level `0` and the frame's `shiftE_consList_two` down to the rule's
   own — the two cancel;
3. the values: the residue spine read at `envT` is the same spine read
   at the consed environment (`denoteMetaSpine_mono` at
   `blockIhCall?_args_constsBound`'s bound), and
   `denoteMetaSpine_of_lift` turns it into the fold's own `vs`.

The `SpineFit`s of `pdoms ++ fdoms` and of `ihdoms` are not
hypotheses of `ihSpineFold_blockRec`: they build `WalkCtx`'s `Sat` at
the walk's ENTRY (`sat_blockFrame`), so they are consumed by the
per-pair assembly that constructs the context, not by the fold that
travels with it. -/


/-! ## A.17 The call's arguments live BELOW the recursors

`hfit`'s spine premise reads the call's arguments at the CONSED
environment while the certificates are at `envT` — the constructors'
one, where the check ran.  The bridge is
`denoteMeta_consBlockRecsR_mono`, whose one hypothesis is
`ConstsBound envT`; and that IS true of a guarded call's arguments,
because `blockIhCall?` rejects a block recursor anywhere in them
(`IhCallRun.hfree`). -/


/-! ## A.17c The BARE-`k` model, and the rule's own reading

The rule stage ANNOTATES the right-hand side at the environment
holding the `k` RULE-LESS recursors and TYPES it there too, so the
accepted-reads recipe applies at that environment and nowhere below it
(the rule mentions the recursors).  What is needed to run the recipe
is a MODEL of that environment, and it is `envModelM_consBlockRecsBare`
at exactly the facts `blockRecStaged_run` already assembles. -/

theorem blockRecBareModel_run {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hnd : (rs.map (·.1.name)).Nodup)
    (hleafCl : ∀ (ψ : Name → Nat) (i : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).erase))
    (hleafLift : ∀ (ψ : Name → Nat) (i k : Nat),
      (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).liftN 1 k
        = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i)
    (hleafPar : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₁ i
          = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₂ i)
    (hleafOk : ∀ (ψ : Name → Nat) (i : Nat), i < rs.length → ∀ ρ : Nat → V,
      WellDenoted V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i))
    (hleafVal : ∀ (ψ : Name → Nat) (i : Nat) (ρ : Nat → V),
      AnnotValid V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i))
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) ρ)
    :
    ∃ mpR : EnvModelM V μ (consBlockRecsBare p.toBlockShape 0 (bareOf rs) envC),
      mpR.base2.acval = blockRecAcv mpC.base2.acval envC rs s eqs := by
  have hfacts := ConLeche.recStage_facts h
  have hcv := recStage_cvFacts h
  have hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) →
      blockRecAcv mpC.base2.acval envC rs s eqs n = mpC.base2.acval n := by
    intro n hne
    refine blockRecAcvOf_of_ne (fun m hm => ?_)
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
    exact hne r hr
  have hacv : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        blockRecAcv mpC.base2.acval envC rs s eqs r.1.name ψ
          = ConLeche.Semantics.blockRecAV (s ψ) rs.length
              (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) i := by
    intro i r hr ψ
    have hi : (rs.map (·.1.name))[i]? = some r.1.name := by
      rw [List.getElem?_map, hr]; rfl
    rw [blockRecAcv, blockRecAcvOf_at hnd hi]
    rfl
  have hty : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ : Name → Nat,
        denoteMeta mpC.base2.acval envC ψ 0 r.1.type
          = some (blockRecTyAV mpC.base2.acval envC rs ψ i) := by
    intro i r hr ψ
    obtain ⟨-, -, -, hread, -⟩ := recStage_tyPis hμ mpC h hr ψ
    exact hread
  have hidx : ∀ r ∈ rs, ∃ i : Nat, rs[i]? = some r := fun r hr => List.getElem?_of_mem hr
  have hrd := hrd_of_pre hμ mpC h rfl hty hacv hpre
  exact envModelM_consBlockRecsBare (q := p.toBlockShape) (m := 0) mpC
    (by rw [bareOf_map_name]; exact hnd)
    (fun x hx => by obtain ⟨r, hr, he⟩ := mem_bareOf hx; rw [he]; exact (hcv r hr).1)
    (fun x hx => by obtain ⟨r, hr, he⟩ := mem_bareOf hx; rw [he]; exact (hcv r hr).2.1)
    (fun x hx => by obtain ⟨r, hr, he⟩ := mem_bareOf hx; rw [he]; exact (hcv r hr).2.2.1)
    (fun x hx => by
      obtain ⟨r, hr, he⟩ := mem_bareOf hx
      rw [he]
      exact ⟨(hfacts r hr).1, (hfacts r hr).2.1, (hfacts r hr).2.2.1, (hfacts r hr).2.2.2.1⟩)
    (fun n hne => hag n (fun r hr => hne (r.1, r.2.2.1)
      (List.mem_map.mpr ⟨r, hr, rfl⟩)))
    (fun x hx ψ => by
      obtain ⟨r, hr, he⟩ := mem_bareOf hx
      obtain ⟨i, hi⟩ := hidx r hr
      rw [he, hacv i r hi ψ]; exact hleafCl ψ i)
    (fun x hx ψ k => by
      obtain ⟨r, hr, he⟩ := mem_bareOf hx
      obtain ⟨i, hi⟩ := hidx r hr
      rw [he, hacv i r hi ψ]; exact hleafLift ψ i k)
    (fun x hx ψ₁ ψ₂ hq => by
      obtain ⟨r, hr, he⟩ := mem_bareOf hx
      obtain ⟨i, hi⟩ := hidx r hr
      rw [he] at hq ⊢
      rw [hacv i r hi ψ₁, hacv i r hi ψ₂]
      exact hleafPar i r hi ψ₁ ψ₂ hq)
    (fun x hx ψ ρ => by
      obtain ⟨r, hr, he⟩ := mem_bareOf hx
      obtain ⟨i, hi⟩ := hidx r hr
      rw [he, hacv i r hi ψ]
      exact hleafOk ψ i (List.getElem?_eq_some_iff.mp hi).1 ρ)
    (fun x hx ψ ρ => by
      obtain ⟨r, hr, he⟩ := mem_bareOf hx
      obtain ⟨i, hi⟩ := hidx r hr
      rw [he, hacv i r hi ψ]; exact hleafVal ψ i ρ)
    (fun x hx ψ => by
      obtain ⟨r, hr, he⟩ := mem_bareOf hx
      rw [he]; exact hrd r hr ψ)

/-- **A checked right-hand side READS, and its reading is graded.**
The accepted-reads recipe (`checkConstantVal_reads`) at the stage's
OWN inference run — `checkBlockRule`'s `inferType` on the annotated
rule at the rule-less recursor environment.  The subject is not a
type, so the grading is the INFER claim's first component rather than
the sort's. -/
theorem blockRuleRhs_reads {envR : Env} (hμ : μ.verifiedChecks = true)
    (mpR : EnvModelM V μ envR) {F : Nat} {out tyR : Expr}
    (hfv : out.hasFvar = false) (hb : out.looseBVarsBounded 0 = true)
    (hinf : ConLeche.inferTypeCore μ envR F 0 out = .ok tyR) (ψ : Name → Nat) :
    ∃ Ra : AnnotTerm, denoteMeta mpR.base2.acval envR ψ 0 out = some Ra ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ Ra := by
  have hw : Expr.WScoped 0 out := Expr.WScoped.of_not_hasFvar hfv
  have hnl : out.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hfv
  have hL : Expr.LeavesBounded out := fun l hl => by
    rw [hnl] at hl
    exact absurd hl (List.not_mem_nil)
  obtain ⟨Ra, hRa⟩ := acceptedReads_of mpR.base2 ψ hinf hw hb hL
  obtain ⟨-, -, -, ihi⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mpR ψ) F
  obtain ⟨tya, htya⟩ := inferReads_of hμ (Rules.RulesInputs.ofSem mpR ψ) hinf hw hb hL
    (CtxOk.nil hnl) hRa
  obtain ⟨hok, -, -⟩ := ihi hinf hw hb hL (CtxOk.nil hnl) hRa htya
  exact ⟨Ra, hRa, fun ρ => hok ρ (ConLeche.Semantics.Sat_nil V ρ)⟩

/-- **The rule's reading, named.**  `blockRuleRhsOk_of` takes the
right-hand side's reading as a FUNCTION of the level valuation; this
is that function, in the shape `Model/Harvest.lean` names a checked
value's reading in. -/
@[expose] noncomputable def blockRuleRaOf (acv : Name → (Name → Nat) → AnnotTerm) (envR : Env)
    (rhsA : Expr) (ψ : Name → Nat) : AnnotTerm :=
  (denoteMeta acv envR ψ 0 rhsA).getD default

/-- **`blockRuleRhsOk_of`'s `hread` and `hok`, at the run.**  The
reading lives at the BARE-`k` environment — the rule mentions the
block's recursors, so it reads nowhere below it — and crosses to the
consed one by the RULE-LIST SWAP (`denoteMeta_swap` at
`swapShList_consBlockRecs`: `denoteMeta` reads the environment only
through the stored level parameters, and the two conses differ in the
`rules` field alone).  The level instantiation is
`denoteMeta_instLevels`, which is why the reading is a FUNCTION of the
valuation. -/
theorem blockRuleRhs_read_run {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hnd : (rs.map (·.1.name)).Nodup)
    (hleafCl : ∀ (ψ : Name → Nat) (i : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).erase))
    (hleafLift : ∀ (ψ : Name → Nat) (i k : Nat),
      (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i).liftN 1 k
        = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i)
    (hleafPar : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₁ i
          = blockRecLeafAV mpC.base2.acval envC rs s eqs ψ₂ i)
    (hleafOk : ∀ (ψ : Name → Nat) (i : Nat), i < rs.length → ∀ ρ : Nat → V,
      WellDenoted V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i))
    (hleafVal : ∀ (ψ : Name → Nat) (i : Nat) (ρ : Nat → V),
      AnnotValid V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ i))
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ) (eqs ψ) ρ) :
    ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s eqs →
      ∀ r ∈ rs, ∀ rhsA ∈ r.2.1,
        (∀ (φ : Name → Nat) (us : List Level),
            denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
                (rhsA.instantiateLevelParams r.1.levelParams us)
              = some (blockRuleRaOf m₃.acval
                  (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) rhsA
                  (Level.substFn φ r.1.levelParams us))) ∧
          ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ
            (blockRuleRaOf m₃.acval
              (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) rhsA ψ) := by
  intro m₃ hac r hr rhsA hrhsA
  obtain ⟨mpR, hacR⟩ :=
    blockRecBareModel_run hμ mpC h hnd hleafCl hleafLift hleafPar hleafOk hleafVal hpre
  have hfacts := ConLeche.recStage_facts h
  obtain ⟨hfv, -, -, hb⟩ := (hfacts r hr).2.2.2.2 rhsA hrhsA
  obtain ⟨tyR, hinf⟩ := recStage_rhsInfer h r hr rhsA hrhsA
  -- the two conses differ in the rules alone
  have hsw : ConLeche.SwapShList
      (consBlockRecsBare p.toBlockShape 0 (bareOf rs) envC).consts
      (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC).consts :=
    swapShList_consBlockRecsR (ConLeche.SwapShList.of_eq envC.consts)
  have hcross : ∀ (ψ : Name → Nat) (e : Expr),
      denoteMeta m₃.acval (consBlockRecsBare p.toBlockShape 0 (bareOf rs) envC) ψ 0 e
        = denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) ψ 0 e :=
    fun ψ e => denoteMeta_swap (ConLeche.SwapShList.congr hsw) ψ 0 e
  have hone : ∀ ψ : Name → Nat, ∃ Ra : AnnotTerm,
      denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) ψ 0 rhsA
          = some Ra ∧ ∀ ρ : Nat → V, WellDenotedV V ρ Ra := by
    intro ψ
    obtain ⟨Ra, hRa, hok⟩ := blockRuleRhs_reads hμ mpR hfv hb hinf ψ
    rw [hacR, ← hac] at hRa
    exact ⟨Ra, by rw [← hcross]; exact hRa, hok⟩
  refine ⟨fun φ us => ?_, fun ψ ρ => ?_⟩
  · rw [denoteMeta_instLevels (acvalParamsAt_of_core m₃) φ]
    obtain ⟨Ra, hRa, -⟩ := hone (Level.substFn φ r.1.levelParams us)
    rw [hRa, blockRuleRaOf, hRa]
    rfl
  · obtain ⟨Ra, hRa, hok⟩ := hone ψ
    rw [blockRuleRaOf, hRa]
    exact hok ρ

/-- **`BlockRuleRhsOk` at the run, with the reading discharged.**
`blockRuleRhsOk_of` at `blockRuleRhs_read_run`: what is left of the
per-pair obligation is `hpl` (the prefix length, a run fact at
`pdoms0`) and the five BASE-FRAME statements — the fit, the index
expressions, the fired spine, the residue at the ih values and the
applied grading. -/
theorem blockRuleRhsOk_run {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hnd : (rs.map (·.1.name)).Nodup)
    (hleafCl : ∀ (ψ : Name → Nat) (i : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i).erase))
    (hleafLift : ∀ (ψ : Name → Nat) (i k : Nat),
      (blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i).liftN 1 k
        = blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i)
    (hleafPar : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ₁ i
          = blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ₂ i)
    (hleafOk : ∀ (ψ : Name → Nat) (i : Nat), i < rs.length → ∀ ρ : Nat → V,
      WellDenoted V ρ (blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i))
    (hleafVal : ∀ (ψ : Name → Nat) (i : Nat) (ρ : Nat → V),
      AnnotValid V ρ (blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i))
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ) ((blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ) ρ)
    {m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC rs s
      (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
    {φ : Name → Nat} {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : r ∈ rs)
    {rhs : Expr} (hrhs : rhs ∈ r.2.1)
    {rl : ConLeche.RecRule} (hrl : ConLeche.RecRule.rhs rl = rhs)
    (hpl : ∀ ψ : Name → Nat, (pdoms0 ψ j).length = p.toBlockShape.rulePrefixAt j)
    (hdata : ∀ us : List Level, us.length = r.1.levelParams.length →
          ∀ (cvj : ConstantVal) (cnP cnF : Nat),
            (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC).find?
                (ConLeche.RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
          ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm)
            (TVa TVja restR restC : AnnotTerm),
            xs.length = p.toBlockShape.majorIdxAt j →
            ys.length = ConLeche.RecRule.ctorParams rl + ConLeche.RecRule.nfields rl →
            usj.length = cvj.levelParams.length →
            Level.substFn φ cvj.levelParams usj
              = Level.substFn φ cvj.levelParams
                  (ConLeche.recFireComparands rl r.1.levelParams us cvj.levelParams []
                    (p.toBlockShape.rulePrefixAt j)).1 →
            (∀ lvls pins, ConLeche.RecRule.fire rl = .nested lvls pins →
              ∀ q, q < ConLeche.RecRule.ctorParams rl →
              ∀ vpa : AnnotTerm,
                denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ
                    (p.toBlockShape.rulePrefixAt j)
                  (openRev 0 (p.toBlockShape.rulePrefixAt j)
                    ((pins.getD q default).instantiateLevelParams r.1.levelParams us))
                  = some vpa →
                interp V ρ (ys.getD q default)
                  = interp V ρ (AnnotTerm.instRevChain
                      (xs.take (p.toBlockShape.rulePrefixAt j)) vpa)) →
            IotaIndexPin (V := V) ρ restC (ConLeche.RecRule.ctorParams rl)
              (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
            denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
                (r.1.type.instantiateLevelParams r.1.levelParams us) = some TVa →
            denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
                (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
            TeleFitPA V ρ TVa
              (xs ++ [AnnotTerm.mkAppN
                (m₃.acval (ConLeche.RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]) restR →
            TeleFitPA V ρ TVja ys restC →
        ((SpineFit ρ (pdoms0 (Level.substFn φ r.1.levelParams us) j
              ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i)
            ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
              ++ (ys.drop (ConLeche.RecRule.ctorParams rl)).map (interp V ρ)) ∧
          (es0 (Level.substFn φ r.1.levelParams us) j i).map
              (interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
                ++ (ys.drop (ConLeche.RecRule.ctorParams rl)).map (interp V ρ)) ρ))
            = (xs.drop (p.toBlockShape.rulePrefixAt j)).map (interp V ρ) ∧
          interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
              ++ (ys.drop (ConLeche.RecRule.ctorParams rl)).map (interp V ρ)) ρ)
              (mk0 (Level.substFn φ r.1.levelParams us) j i)
            = interp V ρ (AnnotTerm.mkAppN (m₃.acval (ConLeche.RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys) ∧
          (∀ a : Nat → V,
            (∀ c', c' < rs.length →
              interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s
                (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)
                (Level.substFn φ r.1.levelParams us) c') = a c') →
            interp V ρ (AnnotTerm.mkAppN (blockRuleRaOf m₃.acval
                (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) rhs
                (Level.substFn φ r.1.levelParams us))
                (xs.take (p.toBlockShape.rulePrefixAt j)
                  ++ ys.drop (ConLeche.RecRule.ctorParams rl)))
              = interp V (consList
                  ((ihs (Level.substFn φ r.1.levelParams us) j i).map
                    (interp V (blockRuleFrame rs.length a ρ (p.toBlockShape.rulePrefixAt j)
                      (ConLeche.RecRule.ctorParams rl) xs ys)))
                  (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
                    ++ (ys.drop (ConLeche.RecRule.ctorParams rl)).map (interp V ρ)) ρ))
                (Rb0 (Level.substFn φ r.1.levelParams us) j i))) ∨
          -- the `ℓ = 0` arm: both sides are the point
          (interp V ρ (AnnotTerm.mkAppN (blockRecLeafAV mpC.base2.acval envC rs s
                (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)
                (Level.substFn φ r.1.levelParams us) j)
              (xs ++ [AnnotTerm.mkAppN (m₃.acval (ConLeche.RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys])) = pt ∧
            interp V ρ (AnnotTerm.mkAppN (blockRuleRaOf m₃.acval
                (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) rhs
                (Level.substFn φ r.1.levelParams us))
              (xs.take (p.toBlockShape.rulePrefixAt j)
                ++ ys.drop (ConLeche.RecRule.ctorParams rl))) = pt)) ∧
          ((∀ a ∈ xs, WellDenotedV V ρ a) → (∀ b ∈ ys, WellDenotedV V ρ b) →
            WellDenotedV V ρ (AnnotTerm.mkAppN (blockRuleRaOf m₃.acval
                (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) rhs
                (Level.substFn φ r.1.levelParams us))
              (xs.take (p.toBlockShape.rulePrefixAt j)
                ++ ys.drop (ConLeche.RecRule.ctorParams rl))))) :
    BlockRuleRhsOk (V := V) (pdoms0 := pdoms0) (fdoms0 := fdoms0) (es0 := es0)
      (ihs := ihs) (mk0 := mk0) (Rb0 := Rb0)
      (blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)) m₃ φ j i r rl := by
  obtain ⟨hread, hok⟩ :=
    blockRuleRhs_read_run hμ mpC h hnd hleafCl hleafLift hleafPar hleafOk hleafVal hpre
      m₃ hac r hr rhs hrhs
  exact blockRuleRhsOk_of
    (RaOf := blockRuleRaOf m₃.acval
      (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) rhs)
    (fun us _ => by rw [hrl]; exact hread φ us) (fun ψ ρ => hok ψ ρ) hpl hdata

/-! ## A.19 The rule's λ-TOWER — the shape the last two conjuncts read

Two of §A.5c's five base-frame statements read the right-hand side's
reading AS A λ-TOWER `mkLamsAV lds A`: the residue conjunct
β-reduces along it (`blockRuleHRa_val`) and the applied form is
graded along it (`mkAppN_wellDenotedV_of_lam`).  The shape is a
COROLLARY of the reading, through the stage's OWN `instLamsAt` run —
`checkBlockRule`'s G2 witness, which `blockRuleData_run` names — and
`instLamsAt_denotePTele` (`Model/IndTowerRead.lean`).

**The tower's domains are the RULE's**, each read at its own depth;
the rule data's `pdoms0 ++ fdoms0` are the RECURSOR's prefix domains
and the CONSTRUCTOR's field domains.  `checkBlockRule` compares the two
(`checkBlockDefEqList` at `envT`, the G2 step), so they are DEFEQ and
not equal, and all either consumer asks of them is that a spine
fitting the second fits the first — which is how the bridge is
stated below (`hG2`). -/

section RuleTower

/-- A reversed list's slot, at an index the list has. -/
theorem getD_reverse_lt {l : List AnnotTerm} {i : Nat} (hi : i < l.length) :
    l.reverse.getD i default = l.getD (l.length - 1 - i) default := by
  rw [List.getD, List.getElem?_reverse (by omega), List.getD]

/-- **A λ-telescope IS a `mkLamsAV` tower.**  `LamTele` appends the
OUTERMOST domain last, so the tower's data is the reversed context —
which is also the order the two consumers index it in (slot `i0` is
the `i0`-th binder from the outside). -/
theorem lamTele_mkLamsAV :
    ∀ {k : Nat} {T : AnnotTerm} {Γ : List AnnotTerm} {R : AnnotTerm},
      LamTele k T Γ R →
      ∃ lds : List (Nat × AnnotTerm), lds.map (·.2) = Γ.reverse ∧ T = mkLamsAV lds R := by
  intro k T Γ R h
  induction h with
  | nil => exact ⟨[], rfl, rfl⟩
  | @cons k v A B R Γ _ ih =>
    obtain ⟨lds, hmap, hT⟩ := ih
    exact ⟨(v, A) :: lds, by simp [hmap], by rw [mkLamsAV, hT]⟩

/-- **The rule's opener spine is indexed**: `fvsPref ++ fvsF` is
`.fvar 0, …, .fvar (rP + nF − 1)`, which is `instLamsAt_denotePTele`'s
shape premise at depth `0`. -/
theorem blockRuleOpeners_index {rP nF : Nat} {e₁ e₂ o₁ o₂ : Expr}
    {fvsPref fvsF : List Expr}
    (h1 : ConLeche.openPisAtFvars rP e₁ 0 = some (fvsPref, o₁))
    (h2 : ConLeche.openPisAtFvars nF e₂ rP = some (fvsF, o₂)) :
    ∀ (i : Nat) (x : Expr), (fvsPref ++ fvsF)[i]? = some x →
      ∃ ty, x = Expr.fvar (0 + i) ty := by
  intro i x hx
  have hlen : fvsPref.length = rP := openPisAtFvars_length _ h1
  rcases Nat.lt_or_ge i fvsPref.length with hi | hi
  · rw [List.getElem?_append_left hi] at hx
    obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ h1 i x hx
    exact ⟨ty, hty⟩
  · rw [List.getElem?_append_right hi] at hx
    obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ h2 (i - fvsPref.length) x hx
    refine ⟨ty, ?_⟩
    rw [hty, hlen]
    congr 1
    omega

/-- **The rule's reading IS a λ-tower over the run's own domains.**

The tower has one layer per rule-prefix and field binder, its core is
the reading of the `instLamsAt` run's residual, and its `i0`-th
domain is the reading of the run's `i0`-th λ-domain AT DEPTH `i0` —
the same per-depth convention `readOpenedDoms` (and with it
`blockRulePdomsAV`/`blockRuleFdomsAV`) uses, so the G2 bridge
compares two readings at one depth and not two frames. -/
theorem blockRuleTower_run {envC env₃ : Env} {acv : Name → (Name → Nat) → AnnotTerm}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {ψ : Name → Nat} {Ra : AnnotTerm} (hread : denoteMeta acv env₃ ψ 0 rhs = some Ra) :
    ∃ (ldoms : List Expr) (lrest : Expr) (lds : List (Nat × AnnotTerm)) (A : AnnotTerm),
      ConLeche.Expr.instLamsAt
          (blockRulePrefFvs p.toBlockShape rs c ++ blockRuleFieldFvs p.toBlockShape rs c i)
          rhs = some (ldoms, lrest) ∧
      Ra = mkLamsAV lds A ∧
      lds.length = p.toBlockShape.rulePrefixAt c + cA.2 ∧
      denoteMeta acv env₃ ψ (p.toBlockShape.rulePrefixAt c + cA.2) lrest = some A ∧
      ∀ (i0 : Nat) (x : Expr), ldoms[i0]? = some x →
        denoteMeta acv env₃ ψ i0 x = some ((lds.map (·.2)).getD i0 default) := by
  obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, hopPref, hinst, hopF, -, hlams, -, -, -⟩ :=
    blockRuleData_run (hm := hm) h hr hcA hrhs
  have hlenP : (blockRulePrefFvs p.toBlockShape rs c).length
      = p.toBlockShape.rulePrefixAt c := openPisAtFvars_length _ hopPref
  have hlenF : (blockRuleFieldFvs p.toBlockShape rs c i).length = cA.2 :=
    openPisAtFvars_length _ hopF
  have hsplen : (blockRulePrefFvs p.toBlockShape rs c
      ++ blockRuleFieldFvs p.toBlockShape rs c i).length
      = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [List.length_append, hlenP, hlenF]
  obtain ⟨Γ, C, htele, hΓlen, hrest, hdoms⟩ :=
    instLamsAt_denotePTele (acval := acv) (env := env₃) (φ := ψ) _ hlams
      (blockRuleOpeners_index hopPref hopF) hread
  obtain ⟨lds, hmap, hT⟩ := lamTele_mkLamsAV htele
  have hldslen : lds.length = p.toBlockShape.rulePrefixAt c + cA.2 := by
    have hq : (lds.map (·.2)).length = Γ.reverse.length := by rw [hmap]
    simp only [List.length_map, List.length_reverse] at hq
    rw [hq, hΓlen, hsplen]
  have hdomslen : ldoms.length = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [ConLeche.Verify.instLamsAt_length _ hlams, hsplen]
  refine ⟨ldoms, lrest, lds, C, hlams, hT, hldslen, ?_, ?_⟩
  · rw [Nat.zero_add, hsplen] at hrest
    exact hrest
  · intro i0 x hx
    have hi0 : i0 < p.toBlockShape.rulePrefixAt c + cA.2 := by
      have hq := (List.getElem?_eq_some_iff.mp hx).1
      omega
    have hd := hdoms i0 x hx
    rw [Nat.zero_add] at hd
    rw [hd, hmap, getD_reverse_lt (by rw [hΓlen, hsplen]; exact hi0), hΓlen]

end RuleTower

/-! ## A.19b The SEAM's shape — ONE environment, ONE valuation

§A.5c's five statements are posed at the CONSED environment's
readings (`m₃.acval`; the recursor's and the constructor's types
instantiated at the rule's level arguments), while every landed
producer speaks the CONSTRUCTORS' environment's (`mpC.base2.acval
envC`, at one valuation).  Two lemmas cross the gap, and only one
direction of each exists:

* `denoteMeta_instLevels` turns the level instantiation into a CHANGE
  OF VALUATION — which is why the rule data is indexed by `ψ` at
  all;
* `denoteMeta_consBlockRecsR_mono` moves a reading UP across the `k`
  recursors' cons, at the one hypothesis `ConstsBound envC`.  The run
  supplies it for the recursor's type (`recStage_facts`'
  `constsResolve`); nothing supplies it for the RULE, which mentions
  the recursors — and that is why the rule's own reading (§A.17c)
  goes the other way, through the bare-`k` model.

`denoteMeta` is a function, so the crossing does not merely relate the
two readings: it ELIMINATES the contract's binder.  `TVa` IS
`blockRecTyAV` at the substituted valuation, and the constructor's
leaf IS the constructors' environment's.

Two more things fall out.  The contract's FIFTH statement — the
applied right-hand side is graded — is not an obligation: the
rule's reading is a λ-tower (§A.19) and a graded tower applied along a
FITTING spine is graded (`mkAppN_wellDenotedV_of_lam`), so what is
owed in its place is the tower's FIT, which the residue statement
(§A.4) needs anyway.  Five statements become four plus one shared fit.
And the premise loses its `∀ m₃` binder: with `hac` used to spell the
valuation, everything the seam is asked for mentions
`blockRecAcv mpC.base2.acval envC rs s eqs` and the two environments,
and no model of the consed environment at all. -/

section SeamShape

variable {envC : Env} {p : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}

/-- **A reading at the constructors' environment is a reading at the
recursors'** — `denoteMeta_consBlockRecsR_mono` at the run's own
freshness (`recStage_cvFacts`) and at the consed valuation's
agreement off the `k` recursor names. -/
theorem blockRecDenote_cross {mpC : EnvModelM V μ envC}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC rs s eqs)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : ConstsBound envC e) {ea : AnnotTerm}
    (hread : denoteMeta mpC.base2.acval envC ψ d e = some ea) :
    denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) ψ d e
      = some ea := by
  have hcv := recStage_cvFacts h
  rw [hac]
  refine denoteMeta_consBlockRecsR_mono (fun r hr => (hcv r hr).1)
    (fun r hr => (hcv r hr).2.2.1) (fun n hne => ?_) ψ d e hcb hread
  refine blockRecAcvOf_of_ne (fun m hm => ?_)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  exact hne r hr

/-- **A constant stored in the constructors' environment keeps its
leaf across the recursors' cons** — the `k` new names are fresh, so
the consed valuation's `findIdx?` misses. -/
theorem blockRecAcv_stored {mpC : EnvModelM V μ envC}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC rs s eqs)
    {n : Name} (hn : (envC.find? n).isSome = true) :
    m₃.acval n = mpC.base2.acval n := by
  have hcv := recStage_cvFacts h
  rw [hac]
  refine blockRecAcvOf_of_ne (fun m hm => ?_)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  intro hh
  rw [hh, (hcv r hr).1] at hn
  exact nomatch hn

/-- **THE ENVIRONMENT CROSSING, as an EQUATION** — the two readings of
one `ConstsBound envC` subject, at the constructors' environment and
at the recursors', are the SAME `Option`.

`blockRecDenote_cross` is its monotone half and is all a consumer that
already HAS the `envC` reading needs.  A consumer that has only the
CONSED reading — the rule's λ-tower is read there, because the
right-hand side mentions the recursors by design — needs the other
direction too, and it is free: `denoteMeta_envExtend` is an equation
under `ConstsBound env₀`, and the run supplies both of its remaining
premises (`recStage_cvFacts` for the freshness and the
projection shape, `recStage_reserved` for the two literal
guards, which is exactly the NAME check `blockRecStaged_of` names for
the same reason).

So the crossing itself is **not** an obligation: what is owed at a
λ-tower's binder domains is the SYNTACTIC premise `ConstsBound envC`,
and that premise has no producer in the tree (§A.19c). -/
theorem blockRecDenote_cross_eq {mpC : EnvModelM V μ envC}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (ψ : Name → Nat) (d : Nat) (e : Expr) (hcb : ConstsBound envC e) :
    denoteMeta mpC.base2.acval envC ψ d e
      = denoteMeta (blockRecAcv mpC.base2.acval envC rs s eqs)
          (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) ψ d e := by
  have hcv := recStage_cvFacts h
  have hres := ConLeche.recStage_reserved h
  have hkeep := find?_consBlockRecsR_keep (R := R) (q := p.toBlockShape)
    (fun r hr => (hcv r hr).1)
  rw [← denoteMeta_envExtend (acval := blockRecAcv mpC.base2.acval envC rs s eqs) (φ := ψ)
      (fun {n} {ci} hf => hkeep n ci hf)
      ⟨(ConLeche.natLitSupported_consBlockRecsR hres).symm,
        (ConLeche.strLitSupported_consBlockRecsR hres).symm⟩
      (fun sn i hs => by
        rw [findProj?_consBlockRecsR (fun r hr => (hcv r hr).2.2.1)]; exact hs) d e hcb]
  refine denoteMeta_acval_congr (fun n hn => ?_) d e
  refine (blockRecAcvOf_of_ne (fun m hm => ?_)).symm
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hm
  intro hh
  rw [hh, (hcv r hr).1] at hn
  exact nomatch hn

/-- **The contract's `TVa` binder, ELIMINATED**: the recursor type's
reading at the consed environment, at the rule's level arguments, IS
`blockRecTyAV` at the substituted valuation. -/
theorem blockRuleTVa_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC rs s eqs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) (φ : Name → Nat) (us : List Level) {TVa : AnnotTerm}
    (hTVa : denoteMeta m₃.acval (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) φ 0
        (r.1.type.instantiateLevelParams r.1.levelParams us) = some TVa) :
    TVa = blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j := by
  obtain ⟨-, -, hres, -, -⟩ := ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  obtain ⟨-, -, -, hread, -⟩ :=
    recStage_tyPis hμ mpC h hr (Level.substFn φ r.1.levelParams us)
  rw [denoteMeta_instLevels (acvalParamsAt_of_core m₃) φ,
    blockRecDenote_cross h hac _ 0 _ (constsBound_of_constsResolve _ hres) hread] at hTVa
  exact (Option.some.inj hTVa).symm

/-- **§A.5c's FIFTH statement is not an obligation.**  The rule's
reading is a λ-tower over the run's own domains (§A.19), and a graded
tower applied along a FITTING spine is graded — so the grading follows
from the TOWER'S FIT, which the residue statement (§A.4's `hsp`) asks
for anyway.

`htow` is stated at the tower the reading determines: `mkLamsAV` at a
fixed length pins `lds` and `A`, so the quantifier is TIED, not
free. -/
theorem blockRuleHapp_run {c : Nat} {cA : ConstantVal × Nat} {Ra : AnnotTerm}
    (htw : ∃ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A ∧
      lds.length = p.toBlockShape.rulePrefixAt c + cA.2)
    {ρ : Nat → V} (hok : WellDenotedV V ρ Ra) {xs ys : List AnnotTerm} {nP : Nat}
    (htow : ∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A →
      lds.length = p.toBlockShape.rulePrefixAt c + cA.2 →
      SpineFit ρ (lds.map (·.2))
        ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)
          ++ (ys.drop nP).map (interp V ρ)))
    (hxs : ∀ a ∈ xs, WellDenotedV V ρ a) (hys : ∀ b ∈ ys, WellDenotedV V ρ b) :
    WellDenotedV V ρ (AnnotTerm.mkAppN Ra
      (xs.take (p.toBlockShape.rulePrefixAt c) ++ ys.drop nP)) := by
  obtain ⟨lds, A, hlam, hlen⟩ := htw
  refine mkAppN_wellDenotedV_of_lam (σ := ρ) (lds := lds) (b := A) hok ?_ ?_ ?_ ?_
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hxs a (List.mem_of_mem_take ha)
    · exact hys a (List.mem_of_mem_drop ha)
  · rw [← hlam]; exact hok.1
  · exact Or.inr (by rw [hlam])
  · rw [List.map_append]; exact htow lds A hlam hlen

/-- **The residue conjunct, from the TOWER FIT and the WALK's
equation.**  §A.5c's FOURTH statement β-reduces along the rule's
λ-tower (`blockRuleHRa_val`), and the tower is the reading's own
(§A.19, `blockRuleTower_run`), so what is left of the conjunct once
the fit is available is ONE equation: the tower's CORE reads, at the
fired frame, to the residue read at the ih values.

The two premises are stated in the `∀ lds A` shape the contract's
FIFTH statement already has — `mkLamsAV` at a fixed length pins `lds`
and `A`, so neither quantifier is free — which is what makes the
composition's fifth conjunct discharge the fourth's fit premise
verbatim, with no transport.  What the residue then costs is the body
equation: `interp_blockResidue`'s conclusion, whose premises include
the rule's walk (`hspine`/`hW`/`hB`). -/
theorem blockRuleHRa_tower_run {env₃ : Env} {acv : Name → (Name → Nat) → AnnotTerm}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hm : memR c) (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {ψ : Name → Nat} {Ra : AnnotTerm} (hread : denoteMeta acv env₃ ψ 0 rhs = some Ra)
    {ρ : Nat → V} (hok : WellDenotedV V ρ Ra)
    {xs ys : List AnnotTerm} {nP : Nat} {ihvals : List V} {Rb : AnnotTerm}
    (hsp : ∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A →
      lds.length = p.toBlockShape.rulePrefixAt c + cA.2 →
      SpineFit ρ (lds.map (·.2))
        ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)
          ++ (ys.drop nP).map (interp V ρ)))
    (hbody : ∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A →
      lds.length = p.toBlockShape.rulePrefixAt c + cA.2 →
      interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)
          ++ (ys.drop nP).map (interp V ρ)) ρ) A
        = interp V (consList ihvals
            (consList ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)
              ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb) :
    interp V ρ (AnnotTerm.mkAppN Ra (xs.take (p.toBlockShape.rulePrefixAt c) ++ ys.drop nP))
      = interp V (consList ihvals
          (consList ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ)) Rb := by
  obtain ⟨-, -, lds, A, -, hlam, hlen, -, -⟩ := blockRuleTower_run (hm := hm) h hr hcA hrhs hread
  exact blockRuleHRa_val hlam hok.1 (hsp lds A hlam hlen) (hbody lds A hlam hlen)

/-- **The fit's PREFIX half is a RUN fact.**  §A.10's truncation
takes the recursor type's reading as a premise (`hTVa`); with the
contract's `TVa` eliminated (`blockRuleTVa_run`) the fit the contract
hands IS a fit of that reading, so the premise is discharged by
`recStage_tyPis` and nothing is left of this half. -/
theorem blockRuleHspPref_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat)
    {ρ : Nat → V} {xs : List AnnotTerm} {maj rest : AnnotTerm}
    (hxl : xs.length = p.toBlockShape.majorIdxAt c)
    (hfit : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) (xs ++ [maj]) rest) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)) := by
  obtain ⟨-, -, -, hread, -⟩ := recStage_tyPis hμ mpC h hr ψ
  exact spineFit_blockRulePdomsAV_app hμ mpC h hr ψ hread hxl hfit

/-- **The rule obligation's RESIDUE half, as ONE premise** — the
FOURTH conjunct of `BlockRuleDataB` at the tower's CORE, at the
contract's own ∀-telescope and under the same premises.

`BlockRuleDataB`'s statements split in two by WHAT they are about.
Three are about the DATA the rule fires with — the prefix-and-fields
fit, the index expressions, the fired spine — and are discharged from
the block's representation (`BlockRuleFit.lean`).  Two are about the
right-hand side's λ-TOWER — the residue at the ih values, and the
tower's own fit — and are discharged from the rule's walk
(`interp_blockResidue`) and the G2 defeq bridge.  Bundling the second
pair under the telescope they are discharged at is what lets the
composition (`blockRuleDataB_of_residue`) take them as ONE hypothesis
instead of restating thirty lines of conjunct, and it bounds them
exactly: the producer sees every premise the contract hands — the two
lengths, `hψ`, `hidx` and both `TeleFitPA`s — and nothing is
quantified past them.

The residue is asked for **at the tower's CORE**, not at the applied
form: `blockRuleHRa_tower_run` pays the β-reduction on this side, so
what the rule side owes is `interp_blockResidue`'s own conclusion —
the body's reading against the residue's at the ih values — and the
`∀ lds A` binders are the ones `mkLamsAV` at a fixed length already
pins (`mkLamsAV_length_inj`).

**It is ONE statement**: the TOWER's FIT is derived at the run from
`BlockRuleDataB`'s FIRST conjunct through G2 (`blockRuleTowerFit_run`,
`BlockRuleFit.lean`), so the rule side owes the body equation and
nothing else.

`@[expose]`: the composition unfolds it. -/
@[expose] def BlockRuleResidueB {envC : Env} (mpC : EnvModelM V μ envC) (p : BlockParts)
    (nP : Nat) (env₃ : Env)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (nCt : Nat → Nat)
    (pdoms0 : (Name → Nat) → Nat → List AnnotTerm)
    (fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm)
    (ctorTy : (Name → Nat) → AnnotTerm) (φ : Name → Nat) (j i : Nat)
    (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (cA : ConstantVal × Nat) (rl : ConLeche.RecRule) (rhs : Expr) : Prop :=
∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
        xs.length = p.toBlockShape.majorIdxAt j →
        ys.length = nP + cA.2 →
        usj.length = cA.1.levelParams.length →
        Level.substFn φ cA.1.levelParams usj
          = Level.substFn φ cA.1.levelParams
              (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
                (p.toBlockShape.rulePrefixAt j)).1 →
        IotaIndexPin (V := V) ρ restC nP
          (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
        TeleFitPA V ρ
          (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
          (xs ++ [AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
        TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
    (∀ a : Nat → V,
        (∀ c', c' < rs.length →
          interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)
            (Level.substFn φ r.1.levelParams us) c') = a c') →
        ∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm),
          blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
              (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
              env₃ rhs
              (Level.substFn φ r.1.levelParams us) = mkLamsAV lds A →
          lds.length = p.toBlockShape.rulePrefixAt j + cA.2 →
          interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
              ++ (ys.drop nP).map (interp V ρ)) ρ) A
            = interp V (consList
                ((ihs (Level.substFn φ r.1.levelParams us) j i).map
                  (interp V (blockRuleFrame rs.length a ρ (p.toBlockShape.rulePrefixAt j)
                    nP xs ys)))
                (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
                  ++ (ys.drop nP).map (interp V ρ)) ρ))
              (Rb0 (Level.substFn φ r.1.levelParams us) j i))

/-- **The seam's rule-side obligation at one (recursor, constructor)
pair** — §A.5c's contract with both reading binders eliminated, its
grading statement replaced by the rule tower's FIT, and no `∀ m₃`.

Five conjuncts, all at `mpC.base2.acval envC` and at the valuation
`Level.substFn φ …`: the prefix-and-fields fit, the index
expressions, the fired spine, the residue at the ih values, and the
λ-tower's fit (§A.4's `hsp`, of which §A.5c's fifth statement is a
corollary).

`@[expose]`: the seam discharges it and the stage consumes it, so the
body must unfold outside this module. -/
@[expose] def BlockRuleDataB {envC : Env} (mpC : EnvModelM V μ envC) (p : BlockParts)
    (nP : Nat) (env₃ : Env)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (s : (Name → Nat) → Nat) (nCt : Nat → Nat)
    (pdoms0 : (Name → Nat) → Nat → List AnnotTerm)
    (fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm)
    (ctorTy : (Name → Nat) → AnnotTerm) (φ : Name → Nat) (j i : Nat)
    (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (cA : ConstantVal × Nat) (rl : ConLeche.RecRule) (rhs : Expr) : Prop :=
∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
        xs.length = p.toBlockShape.majorIdxAt j →
        ys.length = nP + cA.2 →
        usj.length = cA.1.levelParams.length →
        Level.substFn φ cA.1.levelParams usj
          = Level.substFn φ cA.1.levelParams
              (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
                (p.toBlockShape.rulePrefixAt j)).1 →
        -- the `.nested` firing's parameter comparison (vacuous at `.plain`)
        (∀ lvls pins, ConLeche.RecRule.fire rl = .nested lvls pins →
          ∀ q, q < nP → ∀ vpa : AnnotTerm,
            denoteMeta mpC.base2.acval envC φ (p.toBlockShape.rulePrefixAt j)
              (openRev 0 (p.toBlockShape.rulePrefixAt j)
                ((pins.getD q default).instantiateLevelParams r.1.levelParams us))
              = some vpa →
            interp V ρ (ys.getD q default)
              = interp V ρ (AnnotTerm.instRevChain
                  (xs.take (p.toBlockShape.rulePrefixAt j)) vpa)) →
        IotaIndexPin (V := V) ρ restC nP
          (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
        TeleFitPA V ρ
          (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
          (xs ++ [AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
        TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
    SpineFit ρ (pdoms0 (Level.substFn φ r.1.levelParams us) j
          ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i)
        ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ (ys.drop nP).map (interp V ρ)) ∧
      (es0 (Level.substFn φ r.1.levelParams us) j i).map
          (interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)) ρ))
        = (xs.drop (p.toBlockShape.rulePrefixAt j)).map (interp V ρ) ∧
      interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ (ys.drop nP).map (interp V ρ)) ρ)
          (mk0 (Level.substFn φ r.1.levelParams us) j i)
        = interp V ρ (AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys) ∧
      (∀ a : Nat → V,
        (∀ c', c' < rs.length →
          interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)
            (Level.substFn φ r.1.levelParams us) c') = a c') →
        interp V ρ (AnnotTerm.mkAppN (blockRuleRaOf
            (blockRecAcv mpC.base2.acval envC rs s
              (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
            env₃ rhs
            (Level.substFn φ r.1.levelParams us))
            (xs.take (p.toBlockShape.rulePrefixAt j) ++ ys.drop nP))
          = interp V (consList
              ((ihs (Level.substFn φ r.1.levelParams us) j i).map
                (interp V (blockRuleFrame rs.length a ρ (p.toBlockShape.rulePrefixAt j)
                  nP xs ys)))
              (consList ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
                ++ (ys.drop nP).map (interp V ρ)) ρ))
            (Rb0 (Level.substFn φ r.1.levelParams us) j i)) ∧
      (∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm),
        blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
            env₃ rhs
            (Level.substFn φ r.1.levelParams us) = mkLamsAV lds A →
        lds.length = p.toBlockShape.rulePrefixAt j + cA.2 →
        SpineFit ρ (lds.map (·.2))
          ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop nP).map (interp V ρ)))

/-- **`BlockRuleRhsOk` at ONE environment and ONE valuation** —
§A.5c's contract with both reading binders eliminated and the fifth
statement discharged.

What the premise `hdataB` says, and nothing more: at every level
instantiation and every fired spine, the recursor's PREFIX and the
constructor's FIELDS fit the rule data's domains, the index
expressions read to the recursor's index arguments, the fired spine
reads to the constructor at its own parameters, the residue holds at
the ih values — and the rule's λ-tower is FITTED by the same spine
(the shared premise §A.4's `hsp` and the grading both live on).

Three binders are eliminated.  `TVa` and `TVja` name readings the
contract cannot compute; `denoteMeta` is a function, so the run's own
reading (`blockRecTyAV`) and the constructors' stage's (`ctorTy`) ARE
them.  And `hdataB` has no `∀ m₃`: with `hac` used to spell the
valuation, it mentions `blockRecAcv mpC.base2.acval envC rs s eqs` and
the two environments and no model of the consed environment at all. -/
theorem blockRuleRhsOk_base {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hnd : (rs.map (·.1.name)).Nodup)
    (hleafCl : ∀ (ψ : Name → Nat) (i : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i).erase))
    (hleafLift : ∀ (ψ : Name → Nat) (i k : Nat),
      (blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i).liftN 1 k
        = blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i)
    (hleafPar : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) →
        blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ₁ i
          = blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ₂ i)
    (hleafOk : ∀ (ψ : Name → Nat) (i : Nat), i < rs.length → ∀ ρ : Nat → V,
      WellDenoted V ρ (blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i))
    (hleafVal : ∀ (ψ : Name → Nat) (i : Nat) (ρ : Nat → V),
      AnnotValid V ρ (blockRecLeafAV mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ i))
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ) ((blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ) ρ)
    {m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC rs s
      (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
    {φ : Name → Nat} {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hrj : rs[j]? = some r)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {cA : ConstantVal × Nat}
    {rl : ConLeche.RecRule}
    (hrl : ConLeche.RecRule.rhs rl = rhs)
    (hct : ConLeche.RecRule.ctor rl = cA.1.name)
    {nP : Nat} (hnp : ConLeche.RecRule.ctorParams rl = nP)
    (hnf : ConLeche.RecRule.nfields rl = cA.2)
    (hcfind : envC.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2))
    (hpinsCB : ∀ lvls pins, ConLeche.RecRule.fire rl = .nested lvls pins →
      ∀ pin ∈ pins, pin.constsResolve envC = true)
    (hctorCB : ConstsBound envC cA.1.type)
    {ctorTy : (Name → Nat) → AnnotTerm}
    (hctorRead : ∀ ψ : Name → Nat,
      denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some (ctorTy ψ))
    (hpl : ∀ ψ : Name → Nat, (pdoms0 ψ j).length = p.toBlockShape.rulePrefixAt j)
    -- the stored rule reads as a λ-tower over the prefix and the fields
    -- (`blockRuleTower_run` at a member major)
    (htower : ∀ (acv : Name → (Name → Nat) → AnnotTerm) (ψ : Name → Nat) (Ra : AnnotTerm),
      denoteMeta acv (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) ψ 0 rhs = some Ra →
      ∃ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A ∧
        lds.length = p.toBlockShape.rulePrefixAt j + cA.2)
    (hdataB : BlockRuleDataB (V := V) mpC p nP (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs)
    -- the `ℓ = 0` arm: the recursor's type is a truth value, and the
    -- stored rule reads as the point there (`blockRuleRaZ_seam`: by its
    -- head binder's elimination datum, or by the ι law when it binds
    -- no variable)
    (hTyZ : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ j) ∈ˢ (univZero : V))
    (hRaZ : ∀ (ψ : Name → Nat) (Ra : AnnotTerm),
      denoteMeta (blockRecAcv mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
        (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) ψ 0 rhs = some Ra →
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
      ∀ ρ : Nat → V, interp V ρ Ra = pt) :
    BlockRuleRhsOk (V := V) (pdoms0 := pdoms0) (fdoms0 := fdoms0) (es0 := es0)
      (ihs := ihs) (mk0 := mk0) (Rb0 := Rb0)
      (blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)) m₃ φ j i r rl := by
  have hrmem : r ∈ rs := List.mem_of_getElem? hrj
  have hrhsmem : rhs ∈ r.2.1 := List.mem_of_getElem? hrhs
  obtain ⟨hreadR, hokR⟩ :=
    blockRuleRhs_read_run hμ mpC h hnd hleafCl hleafLift hleafPar hleafOk hleafVal hpre
      m₃ hac r hrmem rhs hrhsmem
  have hstored : m₃.acval (ConLeche.RecRule.ctor rl) = mpC.base2.acval cA.1.name := by
    rw [hct]
    exact blockRecAcv_stored h hac (by rw [hcfind]; rfl)
  refine blockRuleRhsOk_run hμ mpC h hnd hleafCl hleafLift hleafPar hleafOk hleafVal hpre
    hac hrmem hrhsmem hrl hpl ?_
  intro us hus cvj cnP cnF hfind usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ hN hidx
    hTVa hTVja hfitR hfitC
  -- the `.nested` comparison, read at the constructors' environment
  have hN' : ∀ lvls pins, ConLeche.RecRule.fire rl = .nested lvls pins →
      ∀ q, q < nP → ∀ vpa : AnnotTerm,
        denoteMeta mpC.base2.acval envC φ (p.toBlockShape.rulePrefixAt j)
          (openRev 0 (p.toBlockShape.rulePrefixAt j)
            ((pins.getD q default).instantiateLevelParams r.1.levelParams us)) = some vpa →
        interp V ρ (ys.getD q default)
          = interp V ρ (AnnotTerm.instRevChain
              (xs.take (p.toBlockShape.rulePrefixAt j)) vpa) := by
    intro lvls pins hf q hq vpa hvpa
    refine hN lvls pins hf q (by rw [hnp]; exact hq) vpa ?_
    refine blockRecDenote_cross h hac φ _ _ ?_ hvpa
    refine constsBound_openRev (constsBound_of_constsResolve _ ?_) 0 _
    rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
    by_cases hilt : q < pins.length
    · exact hpinsCB lvls pins hf _ (ConLeche.getD_mem hilt)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  -- the rule's constructor is `cA`, stored below the recursors
  have hkeep := find?_consBlockRecsR_keep
    (R := R) (q := p.toBlockShape)
    (fun r' hr' => (recStage_cvFacts h r' hr').1) cA.1.name _ hcfind
  have hfind' : (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC).find?
      (ConLeche.RecRule.ctor rl) = some (.ctorInfo cA.1 nP cA.2) := by
    rw [hct]; exact hkeep
  obtain ⟨rfl, rfl, rfl⟩ : cvj = cA.1 ∧ cnP = nP ∧ cnF = cA.2 := by
    have he := hfind'.symm.trans hfind
    injection he with he'
    injection he' with h1 h2 h3
    exact ⟨h1.symm, h2.symm, h3.symm⟩
  -- the two reading binders, eliminated
  obtain rfl := blockRuleTVa_run hμ mpC h hac hrj φ us hTVa
  have hcross := blockRecDenote_cross h hac (Level.substFn φ cA.1.levelParams usj) 0
    cA.1.type hctorCB (hctorRead (Level.substFn φ cA.1.levelParams usj))
  rw [denoteMeta_instLevels (acvalParamsAt_of_core m₃) φ, hcross] at hTVja
  obtain rfl : ctorTy (Level.substFn φ cA.1.levelParams usj) = TVja := Option.some.inj hTVja
  -- the rule's own reading, as a function of the valuation
  have hreadRa : denoteMeta m₃.acval
      (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC)
      (Level.substFn φ r.1.levelParams us) 0 rhs
      = some (blockRuleRaOf m₃.acval
          (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) rhs
          (Level.substFn φ r.1.levelParams us)) := by
    rw [← denoteMeta_instLevels (acvalParamsAt_of_core m₃) (ks := r.1.levelParams) (us := us) φ]
    exact hreadR φ us
  rw [hstored] at hfitR ⊢
  rw [hnp] at hyl hidx ⊢
  rw [hnf] at hyl
  rw [hac] at hreadRa hokR ⊢
  by_cases hℓ : Level.eval (Level.substFn φ r.1.levelParams us)
      (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0
  · -- THE `ℓ = 0` ARM: both sides are the point
    have hRa := hRaZ _ _ hreadRa hℓ ρ
    have hL : interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)
        (Level.substFn φ r.1.levelParams us) j) = pt := by
      obtain ⟨a, ha, -⟩ := blockRecAV_facts (hpre (Level.substFn φ r.1.levelParams us) ρ)
      have hj : j < rs.length := (List.getElem?_eq_some_iff.mp hrj).1
      obtain ⟨hmem, heq, -⟩ := ha j hj
      show interp V ρ (ConLeche.Semantics.blockRecAV _ _ _ _ j) = pt
      rw [heq]
      exact eq_pt_of_mem_univZero (hTyZ (Level.substFn φ r.1.levelParams us) ρ hℓ) hmem
    refine ⟨Or.inr ⟨interp_mkAppN_of_pt hL _, interp_mkAppN_of_pt hRa _⟩, fun hxsW hysW => ?_⟩
    refine mkAppN_wellDenotedV_of_pt (hokR (Level.substFn φ r.1.levelParams us) ρ) hRa ?_
    intro x hx
    rcases List.mem_append.mp hx with h' | h'
    · exact hxsW x (List.mem_of_mem_take h')
    · exact hysW x (List.mem_of_mem_drop h')
  obtain ⟨h1, h2, h3, h4, htow⟩ := hdataB us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ
    hN' hidx hfitR hfitC
  refine ⟨Or.inl ⟨h1, h2, h3, h4⟩, fun hxsW hysW => ?_⟩
  exact blockRuleHapp_run (htower _ _ _ hreadRa)
    (hokR (Level.substFn φ r.1.levelParams us) ρ) htow hxsW hysW

/-- **The recursor stage at the seam's shape** — `blockRecStaged_rhs`
with the rule-side premise replaced by `BlockRuleDataB`.

The premise loses the two reading binders (`TVa`, `TVja` — eliminated
by the crossing), the grading statement (a corollary of the tower's
fit) and the `∀ m₃` quantifier, and gains the CONSTRUCTORS' side of
the pair — the stored `ctorInfo`, the type's `ConstsBound` and its
reading `ctorTy` — which is what the eliminations are paid for with,
and which the constructors' stage owns (`BlockCtorFacts`'s first field
and `CtorDataI.read`). -/
theorem blockRecStaged_dataR {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hnd : (rs.map (·.1.name)).Nodup)
    {nPc : Nat → Nat}
    {fireOf : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) →
      ConLeche.RecRuleFire}
    (hshape : ConLeche.RecRulesShape envC.find? R rs nPc fireOf)
    (hnest : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ lvls pins, fireOf j r = .nested lvls pins →
        p.toBlockShape.rulePrefixAt j ≤ p.toBlockShape.majorIdxAt j ∧
        (∀ l ∈ lvls, l.allParamsDefined r.1.levelParams = true) ∧
        (∀ pin ∈ pins, pin.hasFvar = false ∧
          pin.allLevelParamsDefined r.1.levelParams = true ∧
          pin.constsResolve envC = true ∧
          pin.looseBVarsBounded (p.toBlockShape.rulePrefixAt j) = true ∧
          ∀ (T : Name) (i : Nat), envC.findProj? T i = none → Expr.NoProjAt T i pin) ∧
        ∃ pre dom body bm D,
          r.1.type.stripPis (p.toBlockShape.majorIdxAt j) = some (pre, .forallE dom body bm) ∧
          dom.getAppFn = .const D lvls ∧
          dom.getAppArgs =
            pins.map (Expr.liftLooseBVars
              (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j) 0) ++
              (List.range (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j)).map
                (fun i => Expr.bvar
                  (p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j - 1 - i)))
    (hctorsIn : ∀ r ∈ rs, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF))
    (heqB : ∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
        Term.bvarsBelow rs.length e.erase)
    (heqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ e ∈ blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
        AnnotValid V (consList tup ρ) e)
    (heqP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧
          blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ₁
            = blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ₂)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ)
    (hnCt : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → r.2.2.2.length ≤ nCt j)
    (hpl : ∀ (ψ : Name → Nat) (j : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      (pdoms0 ψ j).length = p.toBlockShape.rulePrefixAt j)
    {ctorTy : Nat → Nat → (Name → Nat) → AnnotTerm}
    (hctor : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (nPc j) cA.2) ∧
        ConstsBound envC cA.1.type ∧
        ∀ ψ : Name → Nat,
          denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some (ctorTy j i ψ))
    -- every fired stored rule reads as a λ-tower over the prefix and the
    -- fields (`blockRuleTower_run` at a member major)
    (htower : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → fireOf j r ≠ .inert →
      ∀ (acv : Name → (Name → Nat) → AnnotTerm) (ψ : Name → Nat) (Ra : AnnotTerm),
        denoteMeta acv (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) ψ 0 rhs = some Ra →
        ∃ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A ∧
          lds.length = p.toBlockShape.rulePrefixAt j + cA.2)
    -- L6: the `.nested` pins' law (vacuous at `.plain`)
    (hpins : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) →
      ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
        List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        RecRulePinsOk m₃ φ r.1 (p.toBlockShape.rulePrefixAt j)
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
              fire := fireOf j r, rhs := rhs, paramsBlind := true }))
    (hdataS : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) →
      ∀ (φ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → fireOf j r ≠ .inert →
        BlockRuleDataB (V := V) mpC p (nPc j)
          (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) rs s nCt pdoms0 fdoms0 es0
          ihs mk0 Rb0 (ctorTy j i) φ j i r cA
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := nPc j,
              fire := fireOf j r, rhs := rhs, paramsBlind := true }) rhs)
    -- the `ℓ = 0` arm: every recursor's type is a truth value there, and
    -- every fired stored rule reads as the point there
    (hTyZ : ∀ j, j < rs.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ j) ∈ˢ (univZero : V))
    (hRaZ : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → fireOf j r ≠ .inert →
      ∀ (ψ : Name → Nat) (Ra : AnnotTerm),
        denoteMeta (blockRecAcv mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) ψ 0 rhs = some Ra →
        Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
        ∀ ρ : Nat → V, interp V ρ Ra = pt) :
    BlockRecStagedAt (V := V) μ envC (ConLeche.consBlockRecsR R p.toBlockShape 0 rs envC) mpC := by
  refine blockRecStaged_rhs hμ mpC h hnd hshape hnest hctorsIn heqB heqV heqP hpre hnCt hpins ?_
  intro m₃ hac φ j r hr i cA rhs hcA hrhs hfire
  obtain ⟨hcfind, hcb, hread⟩ := hctor j r hr i cA hcA
  exact blockRuleRhsOk_base hμ mpC h hnd
    (blockRecLeafAV_closed hμ mpC h heqB)
    (blockRecLeafAV_liftN hμ mpC h heqB)
    (blockRecLeafAV_par_run hμ mpC h heqP)
    (fun ψ _ hi ρ => blockRecLeafAV_wd hpre ψ hi ρ)
    (blockRecLeafAV_valid hμ mpC h heqV)
    hpre hac hr hrhs rfl rfl rfl rfl hcfind
    (fun lvls pins hf pin hpin => by
      rw [ConLeche.recRuleBits_fire] at hf
      exact ((hnest j r hr lvls pins hf).2.2.1 pin hpin).2.2.1)
    hcb hread (fun ψ => hpl ψ j r hr)
    (htower j r hr i cA rhs hcA hrhs hfire)
    (hdataS m₃ hac φ j r hr i cA rhs hcA hrhs hfire)
    (hTyZ j (List.getElem?_eq_some_iff.mp hr).1) (hRaZ j r hr i cA rhs hcA hrhs hfire)

/-- **The recursor stage at the seam's shape, switch off**:
`blockRecStaged_dataR` at `sumRulesR` — the rules fire `.plain` or
`.inert` (the `.nested` premises vacuous), every major is a member (the
rule's λ-tower is the stage's own, `blockRuleTower_run`), and the names
are distinct by the NAME-SET check (`recStage_nodup`). -/
theorem blockRecStaged_data {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hndM : p.toBlockShape.memberNames.Nodup)
    (hctorsIn : ∀ r ∈ rs, ∀ cA ∈ r.2.2.2,
      ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF))
    (heqB : ∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
        Term.bvarsBelow rs.length e.erase)
    (heqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ e ∈ blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
        AnnotValid V (consList tup ρ) e)
    (heqP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧
          blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ₁
            = blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ₂)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ)
    (hnCt : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → r.2.2.2.length ≤ nCt j)
    (hpl : ∀ (ψ : Name → Nat) (j : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      (pdoms0 ψ j).length = p.toBlockShape.rulePrefixAt j)
    {ctorTy : Nat → Nat → (Name → Nat) → AnnotTerm}
    (hctor : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 p.nP cA.2) ∧
        ConstsBound envC cA.1.type ∧
        ∀ ψ : Name → Nat,
          denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some (ctorTy j i ψ))
    (hdataS : ∀ m₃ : EnvModel V (ConLeche.consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC),
      m₃.acval = blockRecAcv mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) →
      ∀ (φ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        BlockRuleDataB (V := V) mpC p p.nP
          (ConLeche.consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) rs s nCt pdoms0
          fdoms0 es0 ihs mk0 Rb0 (ctorTy j i) φ j i r cA
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := p.nP,
              fire := .plain, rhs := rhs, paramsBlind := true }) rhs)
    (hTyZ : ∀ j, j < rs.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ j) ∈ˢ (univZero : V))
    (hRaZ : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      ∀ (ψ : Name → Nat) (Ra : AnnotTerm),
        denoteMeta (blockRecAcv mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (ConLeche.consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) ψ 0 rhs = some Ra →
        Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
        ∀ ρ : Nat → V, interp V ρ Ra = pt) :
    BlockRecStaged (V := V) μ envC p.toBlockShape p.nP rs mpC := by
  unfold BlockRecStaged
  rw [ConLeche.consBlockRecs_eq_R] at hdataS hRaZ ⊢
  -- the switch-off firing is `.plain` wherever it is not `.inert`
  have hpl' : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (if Expr.recRulePlain r.1.type (p.toBlockShape.majorIdxAt j)
          (p.toBlockShape.rulePrefixAt j) p.nP then ConLeche.RecRuleFire.plain else .inert)
        ≠ .inert →
      (if Expr.recRulePlain r.1.type (p.toBlockShape.majorIdxAt j)
          (p.toBlockShape.rulePrefixAt j) p.nP then ConLeche.RecRuleFire.plain else .inert)
        = .plain := by
    intro j r hf
    split
    · rfl
    · next hh => simp [hh] at hf
  refine blockRecStaged_dataR hμ mpC h (recStage_nodup h hndM)
    (ConLeche.recRulesShape_sum envC.find? p.toBlockShape p.nP rs)
    (fun j r _ lvls pins hf => by split at hf <;> exact nomatch hf)
    hctorsIn heqB heqV heqP hpre hnCt hpl hctor
    (fun j r hr i cA rhs hcA hrhs _ acv ψ Ra hRa => by
      obtain ⟨-, -, lds, A, -, hlam, hlen, -, -⟩ :=
        blockRuleTower_run (hm := trivial) h hr hcA hrhs hRa
      exact ⟨lds, A, hlam, hlen⟩)
    (fun m₃ _ φ j r _ i cA rhs _ _ us _ lvls pins hf => by
      rw [ConLeche.recRuleBits_fire] at hf
      split at hf <;> exact nomatch hf)
    (fun m₃ hac φ j r hr i cA rhs hcA hrhs hf => by
      rw [hpl' j r hf]; exact hdataS m₃ hac φ j r hr i cA rhs hcA hrhs)
    hTyZ (fun j r hr i cA rhs hcA hrhs _ => hRaZ j r hr i cA rhs hcA hrhs)

end SeamShape

/-! ## A.18 The ENDPOINT — `declBlock` at what is left

`declBlock` (`DeclBlock.lean`) takes the recursor stage as a
hypothesis `hrec` and hands it everything the constructors'
environment knows; §A.5b turns that hypothesis into the stage's
REMAINING obligations and §A.19b narrows them to ONE environment and
ONE valuation.  The composition says: the P carrier survives the
uniform install at `k` members as soon as, for every block the run
accepts, there is a choice of the family's level, of the rule data
(`pdoms0`/`fdoms0`/`es0`/`ihs`/`mk0`/`Rb0`, `nCt`) and of the
constructors' type readings (`ctorTy`) for which

* the equation list is bounded, valid and level-parametric
  (`heqB`/`heqV`/`heqP` — §A.3's two lemmas reduce the first two to
  the six components' own facts),
* the family's recursor model holds (`hpre`, `blockRecPre_graph`),
* the rule prefix has the length the stage pins (`hpl` —
  `blockRulePdomsAV_length` at `pdoms0`),
* every constructor the recursors carry is STORED with the block's
  arity and its type READS (`hctor` — `BlockCtorFacts`'s first field
  and `CtorDataI.read`), and
* every (recursor, constructor) pair satisfies `BlockRuleDataB`
  (§A.19b: the fit, the index expressions, the fired spine, the
  residue and the rule tower's fit — five statements at the
  constructors' environment and one valuation). -/

theorem declBlock_data (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : ConLeche.BlockParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env block p₀ env₂)
    (hseam : ∀ (envC envI : Env) (pp : ConLeche.BlockParts) (cvTasR : List ConstantVal)
        (ctorsAsR : List (List (ConstantVal × Nat)))
        (rsR : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
        (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
        (A : Nat → (Name → Nat) → AnnotTerm)
       ,
        (∃ out, rsR = ConLeche.tgtRs out ∧ Nonempty (ConLeche.TargetRecRun μ F
          (ConLeche.mkFEnv envC) pp.toBlockShape false false block cvTasR ctorsAsR out)) →
        ConLeche.RecStageOk μ F envC pp cvTasR ctorsAsR rsR →
        pp.toBlockShape.memberNames.Nodup →
        BlockNamesOk (V := V) dR cvTasR →
        BlockCtorsStage (V := V) μ F dR pp.lps cvTasR pp.toBlockShape isRecR A envI
          pp.ctorNamesAt →
        BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k →
        (∀ c, c < ctorsAsR.length → ctorsAsR[c]? = some (dR.ctorsM c)) →
        (∀ r ∈ rsR, ∀ cA ∈ r.2.2.2,
          ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF)) →
        (∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
            (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
          dR = blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf) →
        dR.toLfp ∈ mpC.lfpBlocks →
        ∃ (s : (Name → Nat) → Nat) (nCt : Nat → Nat)
          (pdoms0 : (Name → Nat) → Nat → List AnnotTerm)
          (fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
          (mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm)
          (ctorTy : Nat → Nat → (Name → Nat) → AnnotTerm),
      (∀ ψ : Name → Nat,
      ∀ e ∈ blockRecEqs nCt rsR pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
        Term.bvarsBelow rsR.length e.erase) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rsR.length →
      (∀ mm, mm < rsR.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rsR ψ mm)) →
      ∀ e ∈ blockRecEqs nCt rsR pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
        AnnotValid V (consList tup ρ) e) ∧
      (∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rsR[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
        (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧
          blockRecEqs nCt rsR pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ₁
            = blockRecEqs nCt rsR pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rsR.length
        (blockRecTyAV mpC.base2.acval envC rsR ψ)
        (blockRecEqs nCt rsR pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ) ∧
      (∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rsR[j]? = some r → r.2.2.2.length ≤ nCt j) ∧
      (∀ (ψ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rsR[j]? = some r →
        (pdoms0 ψ j).length = pp.toBlockShape.rulePrefixAt j) ∧
      (∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rsR[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 pp.nP cA.2) ∧
        ConstsBound envC cA.1.type ∧
        ∀ ψ : Name → Nat,
          denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some (ctorTy j i ψ)) ∧
      (∀ m₃ : EnvModel V (consBlockRecs envC.find? pp.toBlockShape pp.nP 0 rsR envC),
        m₃.acval = blockRecAcv mpC.base2.acval envC rsR s
          (blockRecEqs nCt rsR pdoms0 fdoms0 es0 ihs mk0 Rb0) →
      ∀ (φ : Name → Nat) (j : Nat)
          (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rsR[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        BlockRuleDataB (V := V) mpC pp pp.nP
          (consBlockRecs envC.find? pp.toBlockShape pp.nP 0 rsR envC) rsR s nCt pdoms0 fdoms0
          es0 ihs mk0 Rb0 (ctorTy j i) φ j i r cA
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := pp.nP,
              fire := .plain, rhs := rhs, paramsBlind := true }) rhs) ∧
      (∀ j, j < rsR.length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0 →
        interp V ρ (blockRecTyAV mpC.base2.acval envC rsR ψ j) ∈ˢ (univZero : V)) ∧
      (∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
        rsR[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        ∀ (ψ : Name → Nat) (Ra : AnnotTerm),
          denoteMeta (blockRecAcv mpC.base2.acval envC rsR s
              (blockRecEqs nCt rsR pdoms0 fdoms0 es0 ihs mk0 Rb0))
            (consBlockRecs envC.find? pp.toBlockShape pp.nP 0 rsR envC) ψ 0 rhs = some Ra →
          Level.eval ψ
            (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0 →
          ∀ ρ : Nat → V, interp V ρ Ra = pt)) :
    CoverStep mp env₂ :=
  declBlock hμ mp hE hdp hrun
    fun envC envI pp cvTasR ctorsAsR rsR mpC dR isRecR A htgtR hrec hnd hnames hstage hcore
        hctorsAs hctorsIn hdR hlfp => by
      obtain ⟨s, nCt, pdoms0, fdoms0, es0, ihs, mk0, Rb0, ctorTy, heqB, heqV, heqP, hpre,
          hnCt, hpl, hctor, hdataS, hTyZ, hRaZ⟩ :=
        hseam envC envI pp cvTasR ctorsAsR rsR mpC dR isRecR A htgtR hrec hnd hnames hstage
          hcore hctorsAs hctorsIn hdR hlfp
      exact blockRecStaged_data hμ mpC hrec hnd hctorsIn heqB heqV heqP hpre hnCt hpl
        hctor hdataS hTyZ hRaZ

end ConLeche.Model
