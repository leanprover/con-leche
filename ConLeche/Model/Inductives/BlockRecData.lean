module

public import ConLeche.Model.Inductives.BlockRecMem
public import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Model.Inductives.FixLeafOk

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

variable {V : Type w} [SetTheory V]

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
theorem blockRecAV_congr {s K : Nat} {RecTy₁ RecTy₂ : Nat → AnnotTerm}
    {eqs₁ eqs₂ : List AnnotTerm} {c : Nat}
    (hT : ∀ c', c' < K → RecTy₁ c' = RecTy₂ c') (heq : eqs₁ = eqs₂) :
    blockRecAV s K RecTy₁ eqs₁ c = blockRecAV s K RecTy₂ eqs₂ c := by
  subst heq
  have hTs : blockTsAV K RecTy₁ = blockTsAV K RecTy₂ := by
    simp only [blockTsAV]
    refine List.map_congr_left fun mm hmm => ?_
    rw [hT mm (List.mem_range.mp hmm)]
  show projChainAV c (selChainAV s (blockTsAV K RecTy₁) (andChainAV eqs₁)) = _
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

end ConLeche.Model
