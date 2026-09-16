module

public import ConLeche.Model.Inductives.BlockRecWD
public import ConLeche.Model.Annot.Valid
import ConLeche.Semantics.Tower.FixWire
import ConLeche.Semantics.Tower.SumWire
import ConLeche.Model.Inductives.MutualLeafBelow
import ConLeche.Model.Inductives.BlockRecEq
public section

/-!
# The block's recursor leaf: closed, and bit-valid (task #315, U-8)

Two syntactic currencies of the chosen tuple (`blockRecAVI`,
`Semantics/Tower/SigChainI.lean`), the ones the install site asks for
beyond `blockRecs`'s semantic package:

* **closedness** — the leaf is bounded wherever the `k` recursor types
  are, the rules' equations being bounded under the `k` tuple binders
  (`Semantics/Tower/SigChainWire.lean`); here the two block-shaped
  inputs, the conclusion `mutualConcAV` and the recursor type
  `mkPisAV rds (mutualConcAV …)`, and **the rules' equations
  themselves** (`BlockReps.specEqs_below`): the Π-tower's domains are
  the readings' prefix (closed by `BlockReadings.below`) and the
  constructor's fields lifted under the motives and minors (closed by
  the constructor's `CtorDataI.below`), and the body's two application
  chains mention the tuple's variables, the block's variables, the
  constructor's leaf (closed, `cval_closedL`) and the recursive
  fields' moved telescopes and index expressions only;
* **bit validity** — `AnnotValid` of the leaf (`blockRecAVI_validV`):
  the Σ'-chain's hereditary λ clauses quantify over the earlier
  components, so the equations' validity is consumed at fitting
  tuples, exactly as `chainOk_block` consumes their grading.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule PropWhen)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The block's conclusion and recursor type, bounded -/

omit [SetTheory V] in
/-- **The recursor's conclusion is bounded**: motive `mm` sits `nIdx +
n + k` above the major, the index variables below it. -/
theorem mutualConcAV_below {k n nIdx mm K : Nat} (h : nIdx + n + k < K) :
    Term.bvarsBelow K (mutualConcAV k n nIdx mm).erase := by
  unfold mutualConcAV
  refine ⟨?_, show (0 : Nat) < K by omega⟩
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (show 1 + nIdx + n + k - 1 - mm < K by omega) ?_
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  exact Term.bvarsBelow.mono (show nIdx + 1 ≤ K by omega)
    (idxVarsAV_below (K := nIdx) (Nat.le_refl _) e he)

omit [SetTheory V] in
/-- **Member `mm`'s recursor type is bounded** where its binder data
are: the conclusion sits under the whole telescope. -/
theorem blockRecTy_below {rds : List (Nat × Nat × AnnotTerm)} {nP k n nIdx mm K : Nat}
    (hd : DomsBelow K rds) (hlen : rds.length = nP + k + n + nIdx + 1) :
    Term.bvarsBelow K (mkPisAV rds (mutualConcAV k n nIdx mm)).erase :=
  mkPisAV_below_of hd (mutualConcAV_below (by omega))

/-! ## Bit validity of the chosen tuple -/

theorem AnnotValid_liftN_consList (e : AnnotTerm) (rs : List V) (ρ : Nat → V) :
    AnnotValid V (consList rs ρ) (e.liftN rs.length 0) ↔ AnnotValid V ρ e := by
  rw [AnnotValid_liftN V, shiftE_consList]

/-- The `Prop`-level pair is valid when its components are. -/
theorem andAV_valid {ρ : Nat → V} {P Q : AnnotTerm} (hP : AnnotValid V ρ P)
    (hQ : AnnotValid V ρ Q) : AnnotValid V ρ (andAV P Q) := by
  unfold andAV
  show AnnotValid V ρ (.app (.app (.const .psigma [0, 0]) P) (.lam 1 P (Q.liftN 1 0)))
  rw [AnnotValid_app, AnnotValid_app, AnnotValid_lam]
  refine ⟨⟨trivial, hP⟩, hP, fun x _ => ?_⟩
  have h : AnnotValid V (cons x ρ) (Q.liftN 1 0) ↔ AnnotValid V ρ Q := by
    rw [AnnotValid_liftN V, shiftE_succ_cons, shiftE_zero_zero]
  exact h.mpr hQ

/-- The conjunction of valid propositions is valid. -/
theorem andChainAV_valid {ρ : Nat → V} :
    ∀ {es : List AnnotTerm}, (∀ e ∈ es, AnnotValid V ρ e) → AnnotValid V ρ (andChainAV es)
  | [], _ => trivial
  | e :: es, h => by
    show AnnotValid V ρ (andAV e (andChainAV es))
    exact andAV_valid (h e (.head _))
      (andChainAV_valid (es := es) fun e' he' => h e' (.tail _ he'))

/-- A chain link is valid when its head is and its tail is at every
value of the head. -/
theorem sigAV_valid {s : Nat} {ρ : Nat → V} {A rest : AnnotTerm} (hA : AnnotValid V ρ A)
    (hrest : ∀ x, x ∈ˢ interp V ρ A → AnnotValid V (cons x ρ) rest) :
    AnnotValid V ρ (sigAV s A rest) := by
  unfold sigAV
  show AnnotValid V ρ (.app (.app (.const .psigma [s, s]) A) (.lam (s + 1) A rest))
  rw [AnnotValid_app, AnnotValid_app, AnnotValid_lam]
  exact ⟨⟨trivial, hA⟩, hA, hrest⟩

/-- **The block chain is valid**, prefix by prefix (`chainOk_block_go`'s
twin for the bit currency). -/
theorem sigChainAV_valid_go {s : Nat} {ρ : Nat → V} {k : Nat} (T : Nat → AnnotTerm)
    (eqs : List AnnotTerm) (hT : ∀ mm, mm < k → AnnotValid V ρ (T mm))
    (heq : ∀ rs : List V, rs.length = k → (∀ mm, mm < k → rs.getD mm pt ∈ˢ interp V ρ (T mm)) →
      ∀ e ∈ eqs, AnnotValid V (consList rs ρ) e) :
    ∀ (n : Nat) (pre : List V), pre.length + n = k →
      (∀ mm, mm < pre.length → pre.getD mm pt ∈ˢ interp V ρ (T mm)) →
      AnnotValid V (consList pre ρ)
        (sigChainAV s (((List.range k).drop pre.length).map fun mm => (T mm).liftN mm 0)
          (andChainAV eqs))
  | 0, pre, hlen, hpre => by
    rw [blockTs_drop_nil T (p := pre.length) (by omega)]
    show AnnotValid V (consList pre ρ) (andChainAV eqs)
    exact andChainAV_valid (heq pre (by omega) (fun mm hmm => hpre mm (by omega)))
  | n + 1, pre, hlen, hpre => by
    rw [blockTs_drop_cons T (p := pre.length) (by omega)]
    refine sigAV_valid ((AnnotValid_liftN_consList (T pre.length) pre ρ).mpr
      (hT pre.length (by omega))) fun r hr => ?_
    rw [interp_liftN_consList] at hr
    have ih := sigChainAV_valid_go (s := s) (k := k) T eqs hT heq n (pre ++ [r]) (by simp; omega)
      fun mm hmm => by
        simp only [List.length_append, List.length_singleton] at hmm
        rcases Nat.lt_or_ge mm pre.length with hm | hm
        · rw [getD_snoc_lt pre r hm]; exact hpre mm hm
        · have hmm' : mm = pre.length + 0 := by omega
          rw [hmm', getD_snoc_at]
          simpa using hr
    rw [consList_append] at ih
    simpa using ih

theorem sigChainAV_valid {s k : Nat} {ρ : Nat → V} {T : Nat → AnnotTerm} {eqs : List AnnotTerm}
    (hT : ∀ mm, mm < k → AnnotValid V ρ (T mm))
    (heq : ∀ rs : List V, rs.length = k → (∀ mm, mm < k → rs.getD mm pt ∈ˢ interp V ρ (T mm)) →
      ∀ e ∈ eqs, AnnotValid V (consList rs ρ) e) :
    AnnotValid V ρ (sigChainAV s (blockTsAV k T) (andChainAV eqs)) := by
  have := sigChainAV_valid_go (s := s) (ρ := ρ) T eqs hT heq k [] (by simp)
    (fun mm hmm => absurd hmm (by simp))
  simpa [blockTsAV] using this

theorem projChainAV_valid {ρ : Nat → V} :
    ∀ (i : Nat) {e : AnnotTerm}, AnnotValid V ρ e → AnnotValid V ρ (projChainAV i e)
  | 0, e, h => by
    show AnnotValid V ρ (.fst e)
    rw [AnnotValid_fst]; exact h
  | i + 1, e, h => by
    show AnnotValid V ρ (projChainAV i (.snd e))
    exact projChainAV_valid i (by rw [AnnotValid_snd]; exact h)

theorem selChainAV_valid {s : Nat} {ρ : Nat → V} {Ts : List AnnotTerm} {Q : AnnotTerm}
    (h : AnnotValid V ρ (sigChainAV s Ts Q)) : AnnotValid V ρ (selChainAV s Ts Q) := by
  unfold selChainAV
  show AnnotValid V ρ (.app (.app (.const .choice [s]) (sigChainAV s Ts Q)) .prf)
  rw [AnnotValid_app, AnnotValid_app]
  exact ⟨⟨trivial, h⟩, trivial⟩

/-- The chosen tuple's projections are bit-valid: the types are valid
and graded at the sort, the equations valid and truth-valued at every
fitting tuple. -/
theorem blockRecAVI_validV {s k : Nat} {T : Nat → AnnotTerm} {eqs : List AnnotTerm} {ρ : Nat → V}
    (hT : ∀ mm, mm < k → interp V ρ (T mm) ∈ˢ (univ s : V) ∧ WellDenoted V ρ (T mm) ∧
      AnnotValid V ρ (T mm))
    (heq : ∀ rs : List V, rs.length = k → (∀ mm, mm < k → rs.getD mm pt ∈ˢ interp V ρ (T mm)) →
      ∀ e ∈ eqs, interp V (consList rs ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList rs ρ) e ∧
        AnnotValid V (consList rs ρ) e)
    (mm : Nat) : AnnotValid V ρ (blockRecAVI s k T eqs mm) :=
  projChainAV_valid mm
    (selChainAV_valid (sigChainAV_valid (fun t ht => (hT t ht).2.2)
      fun rs hlen hmem e he => (heq rs hlen hmem e he).2.2))

/-! ## The binder-data kit -/

omit [SetTheory V] in
theorem domsBelow_rebit {b : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {K : Nat}, DomsBelow K ds → DomsBelow K (rebit b ds)
  | [], _, _ => trivial
  | _ :: ds, _, h => ⟨h.1, domsBelow_rebit (ds := ds) h.2⟩

omit [SetTheory V] in
theorem domsBelow_liftDoms {n : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {a kk : Nat}, DomsBelow a ds →
      DomsBelow (a + n) (liftDoms n kk ds)
  | [], _, _, _ => trivial
  | d :: ds, a, kk, h => by
    refine ⟨?_, ?_⟩
    · rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN n _ a kk h.1
    · have := domsBelow_liftDoms (n := n) (ds := ds) (a := a + 1) (kk := kk + 1) h.2
      rwa [show a + 1 + n = a + n + 1 from by omega] at this

omit [SetTheory V] in
theorem domsBelow_mapSnd {K : Nat} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)}, DomsBelow K ds →
      LamDomsBelow K (ds.map fun d => (d.2.1, d.2.2))
  | [], _ => trivial
  | _ :: ds, h => ⟨h.1, domsBelow_mapSnd (ds := ds) h.2⟩

omit [SetTheory V] in
/-- The rule's Π-frame, whose bits are reset to `0`, is bounded exactly
where its domains are. -/
theorem domsBelow_reset_of_fields {K : Nat} :
    ∀ {L : List (Nat × AnnotTerm)}, FieldsBelow K (L.map (·.2)) →
      DomsBelow K (L.map fun q => ((0 : Nat), (0 : Nat), q.2))
  | [], _ => trivial
  | _ :: L, h => ⟨h.1, domsBelow_reset_of_fields (L := L) h.2⟩

/-! ## The variable spines -/

omit [SetTheory V] in
theorem tupleVarAV_below {k dp t K : Nat} (hk : 0 < k) (h : dp + k ≤ K) :
    Term.bvarsBelow K (tupleVarAV k dp t).erase := by
  show dp + (k - 1 - t) < K
  omega

omit [SetTheory V] in
theorem paramBvarsAt_below {nP D K : Nat} (hD : nP ≤ D) (h : D ≤ K) :
    ∀ a ∈ paramBvarsAt nP D, Term.bvarsBelow K a.erase := by
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hq
  show D - 1 - q < K
  omega

omit [SetTheory V] in
theorem fieldBvars_below {nF K : Nat} (h : nF ≤ K) :
    ∀ a ∈ fieldBvars nF, Term.bvarsBelow K a.erase := by
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hq
  show nF - 1 - q < K
  omega

omit [SetTheory V] in
theorem teleVarsAV_below {mb K : Nat} (h : mb ≤ K) :
    ∀ a ∈ teleVarsAV mb, Term.bvarsBelow K a.erase := by
  intro a ha
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
  have := List.mem_range.mp hq
  show mb - 1 - q < K
  omega

omit [SetTheory V] in
theorem recPrefixBvarsMK_below {nP k n nF mb K : Nat} (h : nP + nF + n + k + mb ≤ K) :
    ∀ a ∈ recPrefixBvarsMK nP k n nF mb, Term.bvarsBelow K a.erase := by
  intro a ha
  unfold recPrefixBvarsMK at ha
  rcases List.mem_append.mp ha with ha | ha
  · rcases List.mem_append.mp ha with ha | ha
    · exact paramBvarsAt_below (by omega) (by omega) a ha
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      have := List.mem_range.mp ht
      show nF + n + k - 1 - t + mb < K
      omega
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp ha
    have := List.mem_range.mp hl
    show nF + n - 1 - l + mb < K
    omega

/-! ## The rule's two sides -/

omit [SetTheory V] in
/-- **An inductive-hypothesis application is bounded**: a λ-tower over
the field's moved telescope whose body applies the target's tuple
variable to the block's variables, the moved index expressions and the
field at its telescope. -/
theorem ihAppAVK_below {R : AnnotTerm} {nP k n nF i K L : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm} (hlen : tl.length = L)
    (hR : Term.bvarsBelow (K + L) R.erase)
    (htl : DomsBelow K (ihTeleAtR nF (n + k) i 0 tl))
    (hE : ∀ E ∈ Eis, Term.bvarsBelow (K + L) (ihIdxAtM nF (n + k) i 0 L E).erase)
    (hi : i < nF) (hK : nP + nF + n + k ≤ K) :
    Term.bvarsBelow K (ihAppAVK R nP k n nF i tl Eis).erase := by
  subst hlen
  unfold ihAppAVK
  refine mkLamsAV_below (domsBelow_mapSnd htl) ?_
  rw [List.length_map, ihTeleAtR_length, AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN hR ?_
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · exact recPrefixBvarsMK_below (by omega) e he
    · obtain ⟨E, hE', rfl⟩ := List.mem_map.mp he
      exact hE E hE'
  · rw [List.mem_singleton] at he
    subst he
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN
      (show nF - 1 - i + tl.length < K + tl.length by omega) ?_
    intro a' ha'
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp ha'
    exact teleVarsAV_below (K := K + tl.length) (by omega) e' he'

omit [SetTheory V] in
/-- **The rule's left-hand side is bounded**: the member's tuple
variable at the block's variables, the constructor's index readings
(moved under the `k + n` extras) and its leaf at the parameters and
the fields. -/
theorem specLhsAV_below {k nP n nF mJ K : Nat} {Es : List AnnotTerm} {C : AnnotTerm}
    (hk : 0 < k) (hC : Term.bvarsBelow 0 C.erase)
    (hEs : ∀ E ∈ Es, Term.bvarsBelow (nP + nF) E.erase)
    (hK : nP + k + n + nF + k ≤ K) :
    Term.bvarsBelow K (specLhsAV k nP n nF mJ Es C).erase := by
  unfold specLhsAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (tupleVarAV_below hk (by omega)) ?_
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp he with he | he
  · rcases List.mem_append.mp he with he | he
    · exact recPrefixBvarsMK_below (by omega) e he
    · obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he
      rw [AnnotTerm.erase_liftN]
      exact Term.bvarsBelow.mono (show nP + nF + (k + n) ≤ K by omega)
        (VExprAux.bvarsBelow_liftN (k + n) E.erase (nP + nF) nF (hEs E hE))
  · rw [List.mem_singleton] at he
    subst he
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (Term.bvarsBelow.mono (Nat.zero_le K) hC) ?_
    intro a' ha'
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp ha'
    rcases List.mem_append.mp he' with he' | he'
    · exact paramBvarsAt_below (by omega) (by omega) e' he'
    · exact fieldBvars_below (by omega) e' he'

omit [SetTheory V] in
/-- **The rule's right-hand side is bounded**: the minor at the field
variables and the inductive hypotheses. -/
theorem specRuleCoreAV_below {b k nP n nF J K : Nat} {tgtsJ : Nat → Nat} {recIdx : List Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eiss : List (List AnnotTerm)}
    (hk : 0 < k) (hrec : ∀ i ∈ recIdx, i < nF)
    (htl : ∀ i, DomsBelow (nP + i) (tls.getD i []))
    (hE : ∀ i, ∀ E ∈ Eiss.getD i [],
      Term.bvarsBelow (nP + i + (tls.getD i []).length) E.erase)
    (hK : nP + k + n + nF + k ≤ K) :
    Term.bvarsBelow K (specRuleCoreAV b k tgtsJ nP n nF J recIdx tls Eiss).erase := by
  unfold specRuleCoreAV
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (show nF + n - 1 - J < K by omega) ?_
  intro a ha
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  rcases List.mem_append.mp he with he | he
  · exact fieldBvars_below (by omega) e he
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    have hiF : i < nF := hrec i hi
    refine ihAppAVK_below (L := (tls.getD i []).length) (rebit_length b _)
      (tupleVarAV_below hk (by omega)) ?_ ?_ hiF (by omega)
    · have := ihTeleAtGo_below (nF := nF) (o := n + k) (i := i) (l := 0) (K := nP + i)
        (tl := rebit b (tls.getD i [])) (k := 0) (domsBelow_rebit (htl i))
      exact domsBelow_mono (by omega) this
    · intro E hE'
      have := ihIdxAtM_below (nF := nF) (o := n + k) (i := i) (l := 0)
        (m := (tls.getD i []).length) (hE i E hE')
      exact Term.bvarsBelow.mono (by omega) this

omit [SetTheory V] in
/-- **A rule's equation is bounded**: the `Prop`-valued Π-tower over
the rule's binder data of the two sides. -/
theorem specEqAV_below {ruleData : List (Nat × AnnotTerm)} {lhs rhs : AnnotTerm} {K : Nat}
    (hd : DomsBelow K (ruleData.map fun q => ((0 : Nat), (0 : Nat), q.2)))
    (hl : Term.bvarsBelow (K + ruleData.length) lhs.erase)
    (hr : Term.bvarsBelow (K + ruleData.length) rhs.erase) :
    Term.bvarsBelow K (specEqAV ruleData lhs rhs).erase := by
  unfold specEqAV
  refine mkPisAV_below_of hd ?_
  rw [List.length_map]
  exact ⟨hl, hr⟩

/-! ## The block's equations -/

/-- **The block's rule equations are closed under the tuple binders.** -/
theorem BlockReps.specEqs_below {m : EnvModel V env} {d : BlockRepData V} (hreps : BlockReps m d)
    {ψ : Name → Nat} {elimL : Level} {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mots : Nat → Nat} {tgts : Nat → Nat → Nat}
    (hR : BlockReadings m d ψ elimL Ls nIdxs pps ipss cds mots tgts) :
    ∀ e ∈ d.specEqs m ψ elimL Ls nIdxs pps ipss cds mots tgts, Term.bvarsBelow d.k e.erase := by
  intro e he
  obtain ⟨c, j, cA, hc, hj, rfl⟩ := d.mem_specEqs he
  obtain ⟨cvT, cvR, mI, rP, rules, h⟩ := hreps c hc
  have hcd := h.ctorData hj
  have hk : 0 < d.k := Nat.lt_of_le_of_lt (Nat.zero_le c) hc
  have hppsLen : pps.length = d.nP := by
    have hl := congrArg List.length hR.ppsDom
    rw [List.length_map, hreps.params_length hk ψ] at hl
    exact hl
  have hdsLen : (d.dsF c j ψ).length = d.nP + cA.2 := hcd.len ψ
  -- the rule's binder data: length, and closedness at the tuple frame
  have hrdLen : (mutualRuleDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts
      (d.dsF c j ψ)).length = d.nP + d.k + d.nCtors + cA.2 := by
    rw [mutualRuleDataAV_length hppsLen hdsLen, hR.lsLen, hR.cdsLen]
  have hpre : DomsBelow 0 (recPrefixAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts) := by
    have hb := hR.below c hc
    rw [mutualRecDataAV_eq_prefix] at hb
    exact DomsBelow.append_left hb
  have hpreLen : (recPrefixAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts).length
      = d.nP + d.k + d.nCtors := by
    unfold recPrefixAV
    rw [List.length_append, List.length_append, rebit_length, motivesDataGo_length,
      fixMinorsDataM_length, hppsLen, hR.lsLen, hR.cdsLen]
  have hdrop : DomsBelow d.nP ((d.dsF c j ψ).drop d.nP) := by
    have hdr := DomsBelow.drop (k := 0) d.nP (hcd.below ψ)
    simpa using hdr
  have hfields : DomsBelow (d.k + (d.nP + d.k + d.nCtors))
      (rebit (pwBit ψ (Level.zeronessOf elimL))
        (liftDoms (Ls.length + cds.length) 0 ((d.dsF c j ψ).drop d.nP))) :=
    domsBelow_rebit (domsBelow_mono (by rw [hR.lsLen, hR.cdsLen]; omega)
      (domsBelow_liftDoms (n := Ls.length + cds.length) (kk := 0) hdrop))
  have hdata : DomsBelow d.k
      ((mutualRuleDataAV m ψ Ls d.nP nIdxs elimL pps ipss cds mots tgts (d.dsF c j ψ)).map
        fun q => ((0 : Nat), (0 : Nat), q.2)) := by
    refine domsBelow_reset_of_fields ?_
    rw [mutualRuleDataAV_eq_prefix]
    refine DomsBelow.fields (domsBelow_append (domsBelow_mono (Nat.zero_le _) hpre) ?_)
    rw [hpreLen]
    exact hfields
  refine specEqAV_below hdata ?_ ?_
  · rw [hrdLen]
    exact specLhsAV_below hk (m.cval_closedL _ ψ) (hcd.belowE ψ) (by omega)
  · rw [hrdLen]
    refine specRuleCoreAV_below hk (fun i hi => ?_) (hcd.tssBelow ψ) (hcd.eissBelow ψ) (by omega)
    rw [← hcd.ksLen]
    exact (mem_recIdxOf.mp hi).1

end ConLeche.Model
