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
theorem domsBelow_propBinders : ∀ {Ds : List AnnotTerm} {k : Nat},
    FieldsBelow k Ds → DomsBelow k (propBinders Ds)
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, domsBelow_propBinders h.2⟩

omit [SetTheory V] in
theorem fieldsBelow_append : ∀ {Ds Es : List AnnotTerm} {k : Nat},
    FieldsBelow k Ds → FieldsBelow (k + Ds.length) Es → FieldsBelow k (Ds ++ Es)
  | [], _, k, _, hE => by simpa using hE
  | D :: Ds, Es, k, hD, hE =>
    ⟨hD.1, fieldsBelow_append hD.2
      (by rw [show k + 1 + Ds.length = k + (D :: Ds).length from by
            rw [List.length_cons]; omega]; exact hE)⟩

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
    obtain ⟨rc, q', hrc, hq', -, hcv, -, -⟩ := hall n hnl
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
the check: it is the whole of O-2's move, once. -/
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

/-! ## A.3 The family's EQUATION LIST, spelled — and item C's two
obligations at it

`blockIotaEqsAV` is the `eqs` of `blockRecStaged_run` at the block's
own data: the six components are given at the BASE frame, one per
(class, rule) pair, and lifted past the `K` chain binders exactly as
`blockRuleDataAt_of_base` requires.  RM9 states `hpre` at THIS list;
item C's `heqB`/`heqV` are then §2's two theorems under the lifting,
and that is what the rest of this section proves. -/

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

/-- **The family's ι equations at the block's own data.** -/
def blockIotaEqsAV (K : Nat) (nCt : Nat → Nat) (pdoms0 : Nat → List AnnotTerm)
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
`blockRecPre_of`'s `hwd`. -/
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
its six premises are free once the lane's `eqs` is fixed to
`blockIotaEqsAV`: the firing (`recRuleBits_fire`), the recursor's
argument sums (`checkBlockRecK_recNames`, now that the stage pins them
— §4a of session 1), the valuation's reading at the block position,
and the family's ι law.  What is left is the right-hand side's, and it
enters `blockRuleDataAt_of_base` (§3.1). -/

section Hnew

variable {envC : Env} {p : ConLeche.BlockParts}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
  {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
  {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
  {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
  {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}

/-- The lane's `eqs`: the family's ι equations at the block's own
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
    {m₃ : EnvModel V (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)}
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
regimes' `hpre`, with the lane's `eqs`. -/
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
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {j : Nat} (hj : j < rs.length) :
    p.toBlockShape.rulePrefixAt j ≤ p.toBlockShape.majorIdxAt j := by
  obtain ⟨-, hlenR, hall⟩ := checkBlockRecK_recNames h
  obtain ⟨-, -, -, -, -, -, -, nIdx, hsum⟩ := hall j (by omega)
  omega

/-- **One stored rule's `RecRuleLaw`, at the run** — `blockRecRuleLaw_of`
with four of its six premises discharged (§A.4).  What is left is the
RIGHT-HAND SIDE's, verbatim as `blockRecRuleLaw_of` states it, and its
rule-data conjunct enters `blockRuleDataAt_of_base` (§3.1): so `hnew`
is this theorem at every (recursor, constructor) pair, and A-5 is the
`hrhs` below and nothing else. -/
theorem blockRecRuleLaw_run {mpC : EnvModelM V μ envC} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hnd : (rs.map (·.1.name)).Nodup)
    (hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ) (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ)
    {m₃ : EnvModel V (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)}
    (hac : m₃.acval
      = blockRecAcv mpC.base2.acval envC rs s (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
    (φ : Name → Nat) {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[j]? = some r)
    (hj : j < rs.length) (hi : i < nCt j) {rl : ConLeche.RecRule}
    (hplain : ConLeche.RecRule.fire rl = .plain)
    (hrhs : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∃ Ra : AnnotTerm,
        denoteMeta m₃.acval (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) φ 0
            ((ConLeche.RecRule.rhs rl).instantiateLevelParams r.1.levelParams us) = some Ra ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ Ra) ∧
        ∀ (cvj : ConstantVal) (cnP cnF : Nat),
          (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC).find?
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
          IotaIndexPin (V := V) ρ restC (ConLeche.RecRule.ctorParams rl)
            (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
          denoteMeta m₃.acval (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) φ 0
              (r.1.type.instantiateLevelParams r.1.levelParams us) = some TVa →
          denoteMeta m₃.acval (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) φ 0
              (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
          TeleFitPA V ρ TVa
            (xs ++ [AnnotTerm.mkAppN
              (m₃.acval (ConLeche.RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys]) restR →
          TeleFitPA V ρ TVja ys restC →
          (∀ a : Nat → V,
            (∀ c', c' < rs.length →
              interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s
                (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)
                (Level.substFn φ r.1.levelParams us) c') = a c') →
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
                (Level.substFn φ cvj.levelParams usj)) Ra) ∧
          ((∀ a ∈ xs, WellDenotedV V ρ a) → (∀ b ∈ ys, WellDenotedV V ρ b) →
            WellDenotedV V ρ (AnnotTerm.mkAppN Ra
              (xs.take (p.toBlockShape.rulePrefixAt j)
                ++ ys.drop (ConLeche.RecRule.ctorParams rl))))) :
    RecRuleLaw m₃ φ r.1.name r.1 (p.toBlockShape.majorIdxAt j)
      (p.toBlockShape.rulePrefixAt j) rl :=
  blockRecRuleLaw_of (blockRecHrPle h hj) hj hplain
    (blockRecHleaf hac hnd hr) (blockRecHiota hpre hj hi) hrhs

/-! ## A.6 The rule data's FIRST component, at the run

`pdoms0` — the rule's prefix domains at the base frame — needs no new
reading: it is the `rP` first entries of the recursor type's own
binder data, which RM4 already named (`blockRecRdsAV`) and
`checkBlockRecK_tyPis` already identifies.  Its length conjunct (the
first of `BlockRuleDataAt`'s five) is then the stage's two pins
together: `rds.length = mI + 1` and `mI = rP + nIdx`. -/

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
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) :
    (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := by
  obtain ⟨-, -, -, -, -, hlen, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  have hle := blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  rw [blockRulePdomsAV, List.length_map, List.length_take, hlen]
  omega

end Hnew

/-! ## A.5 Stage (c)'s peel, WIDENED — the rule's own data, named

`checkBlockRule_typing` (`BlockRecTyping.lean`) keeps the two typing
runs and the three openings; the rule DATA needs four more witnesses
the same bind chain produces and that peel discards — the λ-tower's
body, the constructor's instantiated telescope, the abstraction's
residue and the `ih` telescope — each with its DEFINING equation, so
that the components below are functions of the run and not
existentials.  (Fifth peel of stage (c) in the tree; V2's open item 3
stands.) -/

section RuleData

open ConLeche (checkBlockRule BlockShape BlockFieldKind BlockRuleFrame)

local macro "close_throw " h:term : tactic =>
  `(tactic| first
      | exact nomatch $h
      | exact absurd $h (by
          simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
          exact fun hh => nomatch hh)
      | exact absurd $h
          (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-- **Stage (c)'s peel with the rule's DATA kept.** -/
theorem checkBlockRule_data {envR envT : Env} {p : BlockShape} {recNames : List Name}
    {rlvls : List Level} {recTys : List Expr} {mIs rPs recTgts : List Nat} {ri : Nat}
    {cvR : ConstantVal} {cA : ConstantVal × Nat} {ks : List BlockFieldKind}
    {rhs out : Expr} {F : Nat}
    (h : checkBlockRule (ConLeche.fueledOps μ F) envR (ConLeche.fueledOps μ F) envT p
      recNames rlvls recTys mIs rPs recTgts ri cvR cA ks rhs = .ok out) :
    ∃ (recTy : Expr) (rbs : List (Expr × ConLeche.BinderMeta)) (body : Expr)
      (cpref : List Expr) (crest : Expr) (fvsPref : List Expr) (o₁ : Expr)
      (fvsF : List Expr) (cbody : Expr) (ldoms : List Expr) (lrest : Expr)
      (resid ihTele : Expr) (fvsIh : List Expr) (bodyO ty concl : Expr),
      recTys[ri]? = some recTy ∧
      ConLeche.Expr.stripLams (p.rulePrefixAt ri + cA.2) out = some (rbs, body) ∧
      ConLeche.openPisAtFvars (p.rulePrefixAt ri) recTy 0 = some (fvsPref, o₁) ∧
      ConLeche.Expr.instPisAt (fvsPref.take p.nP) cA.1.type = some (cpref, crest) ∧
      ConLeche.openPisAtFvars cA.2 crest (p.rulePrefixAt ri) = some (fvsF, cbody) ∧
      ConLeche.Expr.instLamsAt (fvsPref ++ fvsF) out = some (ldoms, lrest) ∧
      ConLeche.abstractIh
          { recNames := recNames, rlvls := rlvls, mIs := mIs, rPs := rPs,
            recTgts := recTgts, nP := p.nP, rP := p.rulePrefixAt ri, nF := cA.2, ks := ks,
            teleOf := ConLeche.structFieldTeleOf cA.1.type p.nP cA.2,
            idxOf := ConLeche.structFieldIdxOf cA.1.type p.nP cA.2,
            ihKeys := ConLeche.blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks,
            pw := Level.zeronessOf (ConLeche.structElimLevel p.elim p.large) }
          0 body = some resid ∧
      ConLeche.blockIhPis p.nP (p.rulePrefixAt ri) cA.2
          (Level.zeronessOf (ConLeche.structElimLevel p.elim p.large))
          (fun c => recTys.getD c (.sort .zero))
          (ConLeche.structFieldTeleOf cA.1.type p.nP cA.2)
          (ConLeche.structFieldIdxOf cA.1.type p.nP cA.2)
          (ConLeche.blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks) 0 resid = some ihTele ∧
      ConLeche.openPisAtFvars
          (ConLeche.blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length
          (ihTele.instantiateList (fvsPref ++ fvsF).reverse)
          (p.rulePrefixAt ri + cA.2) = some (fvsIh, bodyO) ∧
      ConLeche.inferTypeCore μ envT F
          (p.rulePrefixAt ri + cA.2 +
            (ConLeche.blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length)
          bodyO = .ok ty ∧
      ConLeche.Expr.instPisAtLift
          (fvsPref ++ cbody.getAppArgs.drop p.nP ++
            [ConLeche.Expr.mkAppN (.const cA.1.name (p.lps.map .param))
              (fvsPref.take p.nP ++ fvsF)])
          recTy = some concl ∧
      ConLeche.isDefEqCore μ envT F
          (p.rulePrefixAt ri + cA.2 +
            (ConLeche.blockIhKeys (p.rulePrefixAt ri) rPs recTgts ks).length)
          ty concl = .ok true := by
  unfold checkBlockRule at h
  obtain ⟨recTy, hrecTy, h⟩ := ConLeche.exceptBind_ok h
  by_cases hbv : ConLeche.Expr.looseBVarsBounded 0 rhs = true
  case neg => rw [if_neg hbv] at h; close_throw h
  rw [if_pos hbv] at h
  by_cases hfv : rhs.hasFvar = true
  case pos => rw [if_pos hfv] at h; close_throw h
  rw [if_neg hfv] at h
  obtain ⟨rhsA, _, h⟩ := ConLeche.exceptBind_ok h
  by_cases hlp : ConLeche.Expr.allLevelParamsDefined cvR.levelParams rhsA = true
  case neg => rw [if_neg hlp] at h; close_throw h
  rw [if_pos hlp] at h
  by_cases hres : ConLeche.Expr.constsResolve envR rhsA = true
  case neg => rw [if_neg hres] at h; close_throw h
  rw [if_pos hres] at h
  obtain ⟨x1, hx1, h⟩ := ConLeche.exceptBind_ok h; obtain ⟨rbs, body⟩ := x1
  obtain ⟨x2, hx2, h⟩ := ConLeche.exceptBind_ok h; obtain ⟨fvsPref, o₁⟩ := x2
  obtain ⟨x3, hx3, h⟩ := ConLeche.exceptBind_ok h; obtain ⟨cpref, crest⟩ := x3
  obtain ⟨x4, hx4, h⟩ := ConLeche.exceptBind_ok h; obtain ⟨fvsF, cbody⟩ := x4
  obtain ⟨x5, hx5, h⟩ := ConLeche.exceptBind_ok h; obtain ⟨ldoms, lrest⟩ := x5
  obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨resid, hresid, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨ihTele, hihTele, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨x9, hx9, h⟩ := ConLeche.exceptBind_ok h; obtain ⟨fvsIh, bodyO⟩ := x9
  obtain ⟨ty, hty, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨concl, hconcl, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨b, hb, h⟩ := ConLeche.exceptBind_ok h
  by_cases hd : b = true
  case neg => rw [if_neg hd] at h; close_throw h
  subst hd
  have hout : out = rhsA := by
    simpa [pure, Except.pure] using h.symm
  subst hout
  exact ⟨recTy, rbs, body, cpref, crest, fvsPref, o₁, fvsF, cbody, ldoms, lrest,
    resid, ihTele, fvsIh, bodyO, ty, concl,
    ConLeche.unwrapOr_ok hrecTy, ConLeche.unwrapOr_ok hx1, ConLeche.unwrapOr_ok hx2,
    ConLeche.unwrapOr_ok hx3, ConLeche.unwrapOr_ok hx4, ConLeche.unwrapOr_ok hx5,
    ConLeche.unwrapOr_ok hresid, ConLeche.unwrapOr_ok hihTele, ConLeche.unwrapOr_ok hx9,
    hty, ConLeche.unwrapOr_ok hconcl, hb⟩

end RuleData

/-! ## A.7 The ruling of session 4, resolved: NO interface change

The coordinator's option (i) — "thread the per-field `FieldReadAt`
package into `declBlock`'s `hrec` and `blockRecStaged_run`" — turns
out to need NO threading at all.  RM7's session-2 `hrec` already hands
the recursor lane the block's whole representation, including

```
BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k
```

whose third clause carries, per (member `c`, constructor `j`), the
constructors' reading record `BlockCtorDataI` — the block route's
counterpart of the native route's `CtorReadR`.  So the data IS in
scope where `hnew` is proved; `blockCtorData_of_core` is the one-line
projection that names the entry point.

**What the ruling actually reduces to is ONE owed theorem**, the block
analogue of `fieldReadAt_of` (`FixRecRead.lean:965`, which builds
`FieldReadAt` out of `CtorReadR`):

```lean
theorem blockFieldReadAt_of (hcd : BlockCtorDataI mpC.base2 … (d.eissF c j) (d.tssF c j))
    {fvs : List Expr} {o : Expr}
    (hop : ConLeche.openPisAtFvars (d.nP + cA.2) cA.1.type 0 = some (fvs, o))
    {i : Nat} (hi : i < cA.2) :
    FieldReadAt mpC.base2 ψ d.nP cA.2 i cA.1.type fvs
      ((d.tssF c j ψ).getD i []) ((d.eissF c j ψ).getD i [])
```

`BlockCtorDataI.reflOpen` is its content — the field's telescope
OPENED at the field's depth, its domains reading to the telescope's
entries and its body's index expressions to the field's readings —
and the gap to `FieldReadAt` is the same `instSeq`/`openFvars` algebra
`fieldReadAt_of` performs against `CtorReadR`'s
`fieldRead`/`recEntry`/`fieldArity`/`teleLen`.  It belongs in M3's
tier (beside `BlockCtorDataI`), not here. -/

/-- The constructors' reading record for one (member, constructor),
off the stage's core invariant — `blockFieldReadAt_of`'s entry. -/
theorem blockCtorData_of_core {envC : Env} {mpC : EnvModelM V μ envC} {d : BlockData V}
    {lps : List Name} {cvTas : List ConstantVal} {p₁ : ConLeche.BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hcore : BlockCtorsCore mpC.base2 d lps cvTas p₁ isRec A nc)
    {c j : Nat} {cA : ConstantVal × Nat} (hcA : (d.ctorsM c)[j]? = some cA) :
    BlockCtorDataI mpC.base2 d.env₀ (d.memberName c) (fun i => d.memberName (d.tgts c j i))
      (fun i => d.nIdxAt (d.tgts c j i)) lps cA.1 d.nP cA.2 (d.nIdxAt c) d.resSort d.isProp
      d.large (d.idxF c j) (d.dsF c j) (d.esF c j) (d.srcsF c j) (d.ksF c j) (d.fvsPF c j)
      (d.xFvsF c j) (d.xrestF c j) (d.eissF c j) (d.tssF c j) :=
  (hcore.2.2.1 c j cA hcA).2.2

/-! ## A.8 The remaining components, SPELLED

`pdoms0` needed no new reading (§A.6).  The other four syntactic
components are the readings of the check's own opened frame, and they
are functions of the run: the recursor's stored type and the
constructor's stored type determine every Expr
`checkBlockRule` opens (§A.5's equations), so recomputing the same
`openPisAtFvars` / `instPisAt` here and reading the result is the
definition.  The identification — that the run's witnesses ARE these —
is `Option` determinism against `checkBlockRule_data`, once
`checkBlockRecsRules` is peeled to reach one rule; that peel, and
A-2/A-3's uses of these, are not in the tree. -/

/-- The readings of an opened telescope's fvar types, each at its own
depth. -/
def readOpenedDoms (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (ψ : Name → Nat) :
    Nat → List Expr → List AnnotTerm
  | _, [] => []
  | d, x :: xs =>
    (denoteMeta acval env ψ d x.fvarTypeD).getD default :: readOpenedDoms acval env ψ (d + 1) xs

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

end ConLeche.Model
