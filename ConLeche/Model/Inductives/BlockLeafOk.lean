module

public import ConLeche.Model.Inductives.FixLeafOk
import ConLeche.Model.Inductives.BlockChains
public section

/-!
# The block leaf's P currency (task #315 M3)

`FixLeafOk.lean` at `k` members.  The validity machinery of that file
is REUSED, not restated — `ChainValidFacts` never mentions the family
slot (its clauses are about a field's telescope and index expressions
at the SHADOW frame, which is target-blind), and so are
`AnnotValid_congr_noBVar`, `AnnotValid_mkPisAV_of/_inv`,
`fieldsValid_liftTele2`, `fieldsValid_congr_exclP`, `tuplerAV_validV`
and `underTowerValid_of_fields`.  What is ported is the WALK, whose
recursive branch now reads the TARGET member's component of the family
tuple (`recSlotB_facts`, `Semantics/Tower/BlockFamI.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## The validity walk at k -/

section Valid

variable {k w nP nF m : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {ks : List RecFieldKind} {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
  {Fs : List AnnotTerm} {Eis : List (List AnnotTerm)} {Es : List AnnotTerm}

/-- **The validity walk at k** along the X-chain, beside a shadow
spine. -/
theorem blockChainWalkValid (hIall : BlockIdxOk (V := V) k uf ρp Idss)
    (hIV : ∀ c, c < k → FieldsValid ρp (Idss c)) {Y : V}
    (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {t : V}
    (hC : ChainFactsB k w nP nF ρp uf Idss m ks tgts tls Fs Eis Es)
    (hCV : ChainValidFacts nP nF ρp ks tls Fs Eis Es) :
    ∀ (n : Nat) (as as' : List V), nF - as.length = n → as.length ≤ nF →
      ShadowRel nP ks as as' → SpineFit ρp ((shadowFs nP ks nF Fs).take as.length) as' →
      FieldsValid (consList as (cons t (cons Y ρp)))
        (chainXBIGo uf Idss (rsOf ks) tgts tls Eis (Fs.drop as.length) as.length ++
          [idxEqAV (eqsXI (Idss m).length nF Es)]) := by
  intro n
  induction n with
  | zero =>
    intro as as' hn hle hrel hsp
    have hlen : as.length = nF := by omega
    have hdrop : Fs.drop as.length = [] := by rw [List.drop_eq_nil_iff, hC.hFs]; omega
    rw [hdrop]
    simp only [chainXBIGo, List.nil_append, FieldsValid]
    have hspF : SpineFit ρp (shadowFs nP ks nF Fs) as' := by
      rwa [hlen, List.take_of_length_le (by rw [shadowFs_length]; exact Nat.le_refl _)] at hsp
    have hag := agreeOff_shadow hrel ρp
    rw [hlen] at hag
    refine ⟨idxEqAV_validV fun e he => ?_, fun _ _ => trivial⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    have hl' : l < (Idss m).length := List.mem_range.mp hl
    have hEmem : Es.getD l default ∈ Es := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hC.hEs]; exact hl')]
      exact List.getElem_mem _
    constructor
    · show AnnotValid V _ ((Es.getD l default).liftN 2 nF)
      rw [← hlen, AnnotValid_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl,
        shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
      exact (AnnotValid_congr_noBVar _ (hC.nbEs _ hEmem) hag).mpr (hCV.grEV as' hspF _ hEmem)
    · show AnnotValid V _ (projAV l (.bvar nF))
      exact projAV_validV (by simp)
  | succ n ih =>
    intro as as' hn hle hrel hsp
    have hi : as.length < nF := by omega
    have hdrop : Fs.drop as.length = Fs.getD as.length default :: Fs.drop (as.length + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hC.hFs]; exact hi), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hC.hFs]; exact hi)]
      rfl
    rw [hdrop, chainXBIGo_cons, List.cons_append]
    have hag := agreeOff_shadow hrel ρp
    obtain ⟨hok', hbnd', hrec'⟩ := hC.gr as.length hi as' hsp
    obtain ⟨hv', hrecV'⟩ := hCV.grV as.length hi as' hsp
    have hFnb := hC.nb as.length hi
    have hvF : interp V (consList as ρp) (Fs.getD as.length default)
        = interp V (consList as' ρp) (Fs.getD as.length default) :=
      interp_congr_noBVar _ hFnb hag
    have hnext : ∀ (a a' : V), (¬ recAt nP ks (nP + as.length) → a' = a) →
        a' ∈ˢ interp V (consList as' ρp)
          (if recAt nP ks (nP + as.length) then AnnotTerm.sort 0 else Fs.getD as.length default) →
        FieldsValid (consList (as ++ [a]) (cons t (cons Y ρp)))
          (chainXBIGo uf Idss (rsOf ks) tgts tls Eis (Fs.drop (as.length + 1)) (as.length + 1) ++
            [idxEqAV (eqsXI (Idss m).length nF Es)]) := by
      intro a a' ha ha'
      have h := ih (as ++ [a]) (as' ++ [a']) (by simp; omega) (by simp; omega)
        (ShadowRel.snoc hrel ha) (by
          rw [List.length_append, List.length_singleton, shadowFs_take_succ hi]
          exact SpineFit.append hsp ⟨ha', trivial⟩)
      simpa only [List.length_append, List.length_singleton] using h
    by_cases hr : recAt nP ks (nP + as.length)
    · obtain ⟨htlt, hfitS⟩ := hrec' hr
      have hrs : (rsOf ks).getD as.length false = true := by
        have h2 := hr.2
        rw [Nat.add_sub_cancel_left] at h2
        exact (rsOf_getD_iff (by rw [hC.hks]; exact hi)).mpr h2
      have hQ : ∀ q, (recAt nP ks q ∧ q < nP + as.length) → q < nP + as.length := fun _ h => h.2
      have hfit : SlotFit (uf (tgts.getD as.length 0)) w ρp (Idss (tgts.getD as.length 0))
          (tls.getD as.length []) (Eis.getD as.length []) as :=
        slotFit_congr_shadow hrel (hC.nbT as.length hi hr) (hC.nbE as.length hi hr) hfitS
      obtain ⟨hTv', hEv'⟩ := hrecV' hr
      have hT' : ∀ q F, ((tls.getD as.length []).map (·.2.2))[q]? = some F →
          NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + as.length) (nP + as.length + q)) F := by
        intro q F hq
        rw [List.getElem?_map] at hq
        obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp hq
        exact hC.nbT as.length hi hr q d hd
      have hTv : FieldsValid (consList as ρp) ((tls.getD as.length []).map (·.2.2)) :=
        fieldsValid_congr_exclP _ hQ hag hT' hTv'
      have hEv : ∀ bs : List V, SpineFit (consList as ρp) ((tls.getD as.length []).map (·.2.2)) bs →
          ∀ E ∈ Eis.getD as.length [], AnnotValid V (consList (as ++ bs) ρp) E := by
        intro bs hsp E hE
        have hsp' := (spineFit_congr_exclP _ bs hQ hag hT').mp hsp
        have hlen : bs.length = (tls.getD as.length []).length := by
          rw [hsp.length_eq, List.length_map]
        have hag' : AgreeOff (exclP (fun q => recAt nP ks q ∧ q < nP + as.length)
            (nP + as.length + (tls.getD as.length []).length))
            (consList (as ++ bs) ρp) (consList (as' ++ bs) ρp) := by
          rw [consList_append, consList_append, ← hlen]
          exact agreeOff_exclP_consList bs hQ hag
        exact (AnnotValid_congr_noBVar E (hC.nbE as.length hi hr E hE) hag').mpr
          (hEv' bs hsp' E hE)
      have hx : xEntryB uf Idss (rsOf ks) tgts tls Eis (Fs.getD as.length default) as.length
          = slotXBI (uf (tgts.getD as.length 0)) (Idss (tgts.getD as.length 0))
              (tgts.getD as.length 0) (tls.getD as.length []) (Eis.getD as.length [])
              as.length := by
        unfold xEntryB; rw [if_pos hrs]
      rw [hx]
      refine ⟨?_, fun a ha => ?_⟩
      · unfold slotXBI
        refine AnnotValid_mkPisAV_of (w := w) (fun d hd => ?_)
          (fieldsValid_liftTele2 t Y _ as hTv) (fun bs hsp => ?_) (fun hw bs hsp => ?_)
        · obtain ⟨d', hd', he⟩ := mem_liftTele2 hd
          rw [he]; exact hfit.2.1 d' hd'
        · have hsp' := (spineFit_liftTele2 t Y _ as bs).mp hsp
          have hlen : bs.length = (tls.getD as.length []).length := by
            rw [hsp'.length_eq, List.length_map]
          rw [← consList_append,
            show as.length + 1 + (tls.getD as.length []).length = (as ++ bs).length + 1 from by
              rw [List.length_append, hlen]; omega,
            show as.length + 2 + (tls.getD as.length []).length = (as ++ bs).length + 2 from by
              rw [List.length_append, hlen]; omega,
            show as.length + (tls.getD as.length []).length = (as ++ bs).length from by
              rw [List.length_append, hlen]]
          rw [AnnotValid_app]
          refine ⟨projAV_validV (by simp), mkAppN_validV ?_ ?_⟩
          · rw [AnnotValid_liftN, shiftE_Xframe]
            exact tuplerAV_validV (hIall _ htlt) (hIV _ htlt)
          · intro E' hE'
            obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hE'
            rw [AnnotValid_chainXI_ord]
            exact hEv bs hsp' E hE
        · have hsp' := (spineFit_liftTele2 t Y _ as bs).mp hsp
          have hlen : bs.length = (tls.getD as.length []).length := by
            rw [hsp'.length_eq, List.length_map]
          obtain ⟨hEok, hspE⟩ := hfit.2.2 bs hsp'
          have h := recSlotB_facts hIall htlt hY (as ++ bs) t hEok hspE
          rw [← consList_append,
            show as.length + 1 + (tls.getD as.length []).length = (as ++ bs).length + 1 from by
              rw [List.length_append, hlen]; omega,
            show as.length + 2 + (tls.getD as.length []).length = (as ++ bs).length + 2 from by
              rw [List.length_append, hlen]; omega,
            show as.length + (tls.getD as.length []).length = (as ++ bs).length from by
              rw [List.length_append, hlen], h.1]
          rw [hw, univ_zero] at h
          exact h.2.2
      · rw [consList_snoc']
        exact hnext a shadowVal (fun h => absurd hr h) (by rw [if_pos hr]; exact shadowVal_mem)
    · have hrs : (rsOf ks).getD as.length false = false := by
        have := rsOf_getD_iff (ks := ks) (i := as.length) (by rw [hC.hks]; exact hi)
        cases h : (rsOf ks).getD as.length false with
        | false => rfl
        | true =>
          exfalso
          apply hr
          refine ⟨Nat.le_add_right _ _, ?_⟩
          rw [Nat.add_sub_cancel_left]
          exact this.mp h
      have hx : xEntryB uf Idss (rsOf ks) tgts tls Eis (Fs.getD as.length default) as.length
          = (Fs.getD as.length default).liftN 2 as.length := by
        unfold xEntryB; rw [if_neg (by rw [hrs]; exact Bool.false_ne_true)]
      rw [hx]
      refine ⟨?_, fun a ha => ?_⟩
      · rw [AnnotValid_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl,
          shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
        exact (AnnotValid_congr_noBVar _ hFnb hag).mpr hv'
      · rw [consList_snoc']
        rw [interp_chainXI_ord, hvF] at ha
        exact hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)

/-- **The block member's X-chain, valid**, from the walk at the empty
spine. -/
theorem blockChainValid_of (hIall : BlockIdxOk (V := V) k uf ρp Idss)
    (hIV : ∀ c, c < k → FieldsValid ρp (Idss c)) {Y : V}
    (hY : Y ∈ˢ famsSpaceB k w ρp uf Idss) {t : V}
    (hC : ChainFactsB k w nP nF ρp uf Idss m ks tgts tls Fs Eis Es)
    (hCV : ChainValidFacts nP nF ρp ks tls Fs Eis Es) :
    FieldsValid (cons t (cons Y ρp))
      (chainXBI uf Idss (Idss m).length (rsOf ks) tgts tls Eis Fs Es) := by
  have h := blockChainWalkValid hIall hIV hY (t := t) hC hCV nF [] [] (by simp) (by simp)
    (ShadowRel.nil nP ks) trivial
  simp only [List.length_nil, List.drop_zero, consList_nil] at h
  rw [chainXBI, hC.hFs]
  exact h

end Valid

/-! ## Closedness -/

section Below

omit [SetTheory V] in
/-- The non-dependent tower is closed at its components' bound plus
its own depth. -/
theorem ndTowerAV_below {r b : Nat} {G : Nat → AnnotTerm} :
    ∀ (n s d : Nat), (∀ i, i < s + n → Term.bvarsBelow b (G i).erase) →
      Term.bvarsBelow (b + d) (ndTowerAV r G s d n).erase
  | 0, _, _, _ => by simp [ndTowerAV, Term.bvarsBelow]
  | n + 1, s, d, hG => by
    show Term.bvarsBelow (b + d) (AnnotTerm.erase
      (.app (.app (.const .psigma [r, r]) ((G s).liftN d 0))
        (.lam (r + 1) ((G s).liftN d 0) (ndTowerAV r G (s + 1) (d + 1) n))))
    have hC : Term.bvarsBelow (b + d) ((G s).liftN d 0).erase := by
      rw [AnnotTerm.erase_liftN]
      exact VExprAux.bvarsBelow_liftN d (G s).erase b 0 (hG s (by omega))
    have htail : Term.bvarsBelow (b + d + 1) (ndTowerAV r G (s + 1) (d + 1) n).erase := by
      have := ndTowerAV_below (r := r) (G := G) (b := b) n (s + 1) (d + 1)
        (fun i hi => hG i (by omega))
      rwa [show b + (d + 1) = b + d + 1 from by omega] at this
    simp only [AnnotTerm.erase_app, AnnotTerm.erase_lam, Term.bvarsBelow]
    exact ⟨⟨trivial, hC⟩, hC, htail⟩

omit [SetTheory V] in
/-- The non-dependent tuple VALUE is closed at its components' bound. -/
theorem ndMkTowerAV_below {r b : Nat} {Gty G : Nat → AnnotTerm} :
    ∀ (n s : Nat), (∀ i, i < s + n → Term.bvarsBelow b (Gty i).erase) →
      (∀ i, i < s + n → Term.bvarsBelow b (G i).erase) →
      Term.bvarsBelow b (ndMkTowerAV r Gty G s n).erase
  | 0, _, _, _ => by simp [ndMkTowerAV, Term.bvarsBelow]
  | n + 1, s, hGty, hG => by
    show Term.bvarsBelow b (AnnotTerm.erase (AnnotTerm.mkAppN (.const .psigmaMk [r, r])
      [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
       G s, ndMkTowerAV r Gty G (s + 1) n]))
    rw [AnnotTerm.erase_mkAppN]
    refine VExprAux.bvarsBelow_mkAppN (by simp [Term.bvarsBelow]) ?_
    intro a ha
    simp only [List.map_cons, List.map_nil, List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | rfl | h
    · exact hGty s (by omega)
    · simp only [AnnotTerm.erase_lam, Term.bvarsBelow]
      refine ⟨hGty s (by omega), ?_⟩
      have := ndTowerAV_below (r := r) (G := Gty) (b := b) n (s + 1) 1
        (fun i hi => hGty i (by omega))
      rwa [show b + 1 = b + 1 from rfl] at this
    · exact hG s (by omega)
    · exact ndMkTowerAV_below (r := r) (Gty := Gty) (G := G) n (s + 1)
        (fun i hi => hGty i (by omega)) (fun i hi => hG i (by omega))
    · exact nomatch h

/-! ### The chains and the leaf -/

section ChainBelow

variable {k w u nP nIdx : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rs : List Bool} {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
  {Eis : List (List AnnotTerm)} {Fs Es : List AnnotTerm}

omit [SetTheory V] in
/-- The block X-chain's entries from position `i` on, below the
X-frame.  `Idss` is bounded UNBOUNDEDLY in the component: the stage
builds it so that a component past the block has the empty index
telescope, and a recursive position's target bound is not a syntactic
fact here. -/
theorem chainXBIGo_below (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hTls : ∀ i, DomsBelow (nP + i) (tls.getD i []))
    (hEis : ∀ i, ∀ E ∈ Eis.getD i [],
      Term.bvarsBelow (nP + i + (tls.getD i []).length) E.erase) :
    ∀ (Fs : List AnnotTerm) (i : Nat), FieldsBelow (nP + i) Fs →
      FieldsBelow (nP + 2 + i) (chainXBIGo uf Idss rs tgts tls Eis Fs i)
  | [], _, _ => trivial
  | F :: Fs, i, hF => by
    rw [chainXBIGo_cons]
    refine ⟨?_, ?_⟩
    · unfold xEntryB
      split
      · unfold slotXBI
        refine mkPisAV_below_of (domsBelow_liftTele2 _ i (hTls i)) ?_
        rw [liftTele2_length]
        simp only [AnnotTerm.erase_app, Term.bvarsBelow]
        refine ⟨projAV_below (by simp only [AnnotTerm.erase_bvar, Term.bvarsBelow]; omega), ?_⟩
        rw [AnnotTerm.erase_mkAppN]
        refine VExprAux.bvarsBelow_mkAppN ?_ ?_
        · rw [AnnotTerm.erase_liftN]
          have := VExprAux.bvarsBelow_liftN (i + 2 + (tls.getD i []).length)
            (tuplerAV (uf (tgts.getD i 0)) (Idss (tgts.getD i 0))).erase nP 0
            (tuplerAV_below (u := uf (tgts.getD i 0)) (hIds (tgts.getD i 0)))
          rwa [show nP + (i + 2 + (tls.getD i []).length) = nP + 2 + i + (tls.getD i []).length
            from by omega] at this
        · intro a ha
          rw [List.map_map] at ha
          obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
          simp only [Function.comp, AnnotTerm.erase_liftN]
          have := VExprAux.bvarsBelow_liftN 2 E.erase (nP + i + (tls.getD i []).length)
            (i + (tls.getD i []).length) (hEis i E hE)
          rwa [show nP + i + (tls.getD i []).length + 2 = nP + 2 + i + (tls.getD i []).length
            from by omega] at this
      · rw [AnnotTerm.erase_liftN]
        have := VExprAux.bvarsBelow_liftN 2 F.erase (nP + i) i hF.1
        rwa [show nP + i + 2 = nP + 2 + i from by omega] at this
    · have := chainXBIGo_below hIds hTls hEis Fs (i + 1)
        (by rw [show nP + (i + 1) = nP + i + 1 from by omega]; exact hF.2)
      rwa [show nP + 2 + (i + 1) = nP + 2 + i + 1 from by omega] at this

omit [SetTheory V] in
/-- One block constructor's X-chain, below the X-frame. -/
theorem chainXBI_below (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hTls : ∀ i, DomsBelow (nP + i) (tls.getD i []))
    (hEis : ∀ i, ∀ E ∈ Eis.getD i [],
      Term.bvarsBelow (nP + i + (tls.getD i []).length) E.erase)
    (hFs : FieldsBelow nP Fs) (hEsLen : Es.length = nIdx)
    (hEs : ∀ E ∈ Es, Term.bvarsBelow (nP + Fs.length) E.erase) :
    FieldsBelow (nP + 2) (chainXBI uf Idss nIdx rs tgts tls Eis Fs Es) := by
  unfold chainXBI
  refine FieldsBelow_append_idxEq
    (by simpa using chainXBIGo_below hIds hTls hEis Fs 0 (by simpa using hFs)) ?_
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  have hl' : l < nIdx := List.mem_range.mp hl
  rw [chainXBIGo_length]
  have hmem : Es.getD l default ∈ Es := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hEsLen]; exact hl')]
    exact List.getElem_mem _
  constructor
  · show Term.bvarsBelow _ ((Es.getD l default).liftN 2 Fs.length).erase
    rw [AnnotTerm.erase_liftN]
    have := VExprAux.bvarsBelow_liftN 2 (Es.getD l default).erase (nP + Fs.length) Fs.length
      (hEs _ hmem)
    rwa [show nP + Fs.length + 2 = nP + 2 + Fs.length from by omega] at this
  · show Term.bvarsBelow _ (projAV l (.bvar Fs.length)).erase
    exact projAV_below (by simp [Term.bvarsBelow])

end ChainBelow

/-! ### The operator tower -/

section LeafBelow

variable {k w nP nIdx : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

omit [SetTheory V] in
theorem famTyAV_below {u w : Nat} {Ids : List AnnotTerm} (h : FieldsBelow nP Ids) :
    Term.bvarsBelow nP (famTyAV u w Ids).erase := by
  unfold famTyAV
  simp only [AnnotTerm.erase_pi, AnnotTerm.erase_sort, Term.bvarsBelow]
  exact ⟨towerBodyAV_below h, trivial⟩

omit [SetTheory V] in
/-- Member `m`'s arm of the operator, below the operator's λ. -/
theorem blockArmAV_below {m : Nat} (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hchains : ∀ chain ∈ Chs m, FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow (nP + 1)
      (blockArmG w uf Idss Chs m).erase := by
  unfold blockArmG
  simp only [AnnotTerm.erase_lam, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN 1 (idxTyAV (uf m) (Idss m)).erase nP 0
      (towerBodyAV_below (hIds m))
  · exact sumBodyAV_below hchains

omit [SetTheory V] in
/-- The block's operator, below the parameter frame. -/
theorem blockFunAV_below (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hchains : ∀ m, m < k → ∀ chain ∈ Chs m, FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow nP (blockFunG k w uf Idss Chs).erase := by
  unfold blockFunG
  simp only [AnnotTerm.erase_lam, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · unfold famsTyBAV
    have := ndTowerAV_below (r := blockR k w uf)
      (G := fun m => famTyAV (uf m) w (Idss m)) (b := nP) k 0 0
      (fun i _ => famTyAV_below (hIds i))
    rwa [Nat.add_zero] at this
  · exact ndMkTowerAV_below (r := blockR k w uf) (b := nP + 1) k 0
      (fun i _ => by
        rw [AnnotTerm.erase_liftN]
        exact VExprAux.bvarsBelow_liftN 1 (famTyAV (uf i) w (Idss i)).erase nP 0
          (famTyAV_below (hIds i)))
      (fun i hi => blockArmAV_below hIds (hchains i (by omega)))

omit [SetTheory V] in
/-- The index-set tuple, below the parameter frame. -/
theorem idxTupAV_below (hIds : ∀ c, FieldsBelow nP (Idss c)) :
    Term.bvarsBelow nP (idxTupAV k w uf Idss).erase := by
  unfold idxTupAV
  exact ndMkTowerAV_below (r := blockS k w uf) (b := nP) k 0
    (fun _ _ => by simp only [AnnotTerm.erase_sort]; trivial)
    (fun i _ => towerBodyAV_below (hIds i))

omit [SetTheory V] in
/-- The block's carrier tuple, below the parameter frame. -/
theorem blockBodyAV_below (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hchains : ∀ m, m < k → ∀ chain ∈ Chs m, FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow nP (blockBodyG k w uf Idss Chs).erase := by
  unfold blockBodyG
  rw [AnnotTerm.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (by simp [Term.bvarsBelow]) ?_
  intro a ha
  simp only [List.map_cons, List.map_nil, List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · exact idxTupAV_below hIds
  · exact blockFunAV_below hIds hchains
  · exact nomatch h

omit [SetTheory V] in
/-- **A member's former leaf is closed.** -/
theorem blockTyAV_below {m : Nat} {pps : List (Nat × Nat × AnnotTerm)}
    (hp : DomsBelow 0 pps) (hlen : pps.length = nP + nIdx)
    (hIdsLen : (Idss m).length = nIdx)
    (hIds : ∀ c, FieldsBelow nP (Idss c))
    (hchains : ∀ m, m < k → ∀ chain ∈ Chs m, FieldsBelow (nP + 2) chain) :
    Term.bvarsBelow 0
      (blockTyG k w uf Idss Chs pps m).erase := by
  refine mkLamsAV_below hp.mapC ?_
  rw [List.length_map, hlen, Nat.zero_add, ← hIdsLen]
  simp only [AnnotTerm.erase_app, Term.bvarsBelow]
  refine ⟨?_, ?_⟩
  · refine projAV_below ?_
    rw [AnnotTerm.erase_liftN]
    exact VExprAux.bvarsBelow_liftN (Idss m).length
      (blockBodyG k w uf Idss Chs).erase nP 0
      (blockBodyAV_below hIds hchains)
  · exact mkTowerGo_below (w := uf m) (hIds m)

end LeafBelow

end Below

/-! ## The leaf's currency -/

section Currency

variable {k w nP : Nat} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {Chs : Nat → List (List AnnotTerm)}

/-- The non-dependent tuple VALUE is bit-valid, hereditarily from its
components'. -/
theorem ndMkTowerAV_validV {r : Nat} {Gty G : Nat → AnnotTerm} {ρ : Nat → V} :
    ∀ (n s : Nat), (∀ i, i < s + n → AnnotValid V ρ (Gty i)) →
      (∀ i, i < s + n → AnnotValid V ρ (G i)) →
      AnnotValid V ρ (ndMkTowerAV r Gty G s n)
  | 0, _, _, _ => by simp [ndMkTowerAV]
  | n + 1, s, hGty, hG => by
    show AnnotValid V ρ (AnnotTerm.mkAppN (.const .psigmaMk [r, r])
      [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
       G s, ndMkTowerAV r Gty G (s + 1) n])
    refine mkAppN_validV (by simp) ?_
    intro a ha
    simp only [List.mem_cons] at ha
    rcases ha with rfl | rfl | rfl | rfl | h
    · exact hGty s (by omega)
    · rw [AnnotValid_lam]
      exact ⟨hGty s (by omega), fun x _ =>
        ndTowerAV_annotValid V n (s + 1) 1 (cons x ρ)
          (by rw [shiftE_succ_cons, shiftE_zero_zero]) (fun i hi => hGty i (by omega))⟩
    · exact hG s (by omega)
    · exact ndMkTowerAV_validV n (s + 1) (fun i hi => hGty i (by omega))
        (fun i hi => hG i (by omega))
    · exact nomatch h

/-- **The block's carrier tuple is bit-valid** at the parameter
frame. -/
theorem blockBodyAV_validV {ρp : Nat → V} (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hIV : ∀ c, c < k → FieldsValid ρp (Idss c))
    (hchains : ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ c, c < k →
      ∀ t, t ∈ˢ idxSet (uf c) ρp (Idss c) →
      SumFieldsValid (cons t (cons Y ρp))
        (Chs c)) :
    AnnotValid V ρp (blockBodyG k w uf Idss Chs) := by
  unfold blockBodyG
  refine mkAppN_validV (by simp) ?_
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · -- the index-set tuple
    unfold idxTupAV
    exact ndMkTowerAV_validV k 0 (fun _ _ => trivial)
      (fun i hi => towerBodyAV_validV (hIV i (by omega)))
  · -- the operator
    unfold blockFunG
    rw [AnnotValid_lam]
    have hfam : ∀ i, i < k → AnnotValid V ρp (famTyAV (uf i) w (Idss i)) := by
      intro i hi
      unfold famTyAV
      rw [AnnotValid_pi]
      exact ⟨towerBodyAV_validV (hIV i hi), fun _ _ => trivial,
        fun h0 => absurd h0 (Nat.succ_ne_zero _)⟩
    refine ⟨?_, fun Y hY => ?_⟩
    · unfold famsTyBAV
      exact ndTowerAV_annotValid V k 0 0 ρp (shiftE_zero_zero ρp)
        (fun i hi => hfam i (by omega))
    · rw [(famsTyBAV_facts (w := w) hI).1] at hY
      have hsh1 : shiftE 1 0 (cons Y ρp) = ρp := by
        rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      refine ndMkTowerAV_validV k 0 (fun i hi => ?_) (fun i hi => ?_)
      · rw [AnnotValid_liftN, hsh1]; exact hfam i (by omega)
      · unfold blockArmG
        rw [AnnotValid_lam]
        refine ⟨by rw [AnnotValid_liftN, hsh1]; exact towerBodyAV_validV (hIV i (by omega)),
          fun t ht => ?_⟩
        rw [interp_liftN, hsh1, (idxTyAV_facts (hI i (by omega))).1] at ht
        exact sumBodyAV_validV (hchains Y hY i (by omega) t ht)
  · exact nomatch h

/-- The leaf's body is bit-valid at the frame below the parameters and
the member's index variables. -/
theorem blockLeafBody_validV {ρp : Nat → V} (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hIV : ∀ c, c < k → FieldsValid ρp (Idss c))
    (hchains : ∀ Y, Y ∈ˢ famsSpaceB k w ρp uf Idss → ∀ c, c < k →
      ∀ t, t ∈ˢ idxSet (uf c) ρp (Idss c) →
      SumFieldsValid (cons t (cons Y ρp))
        (Chs c))
    {m : Nat} (hm : m < k) {is : List V} (hsp : SpineFit ρp (Idss m) is) :
    AnnotValid V (consList is ρp)
      (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0))
        (mkTowerGo (uf m) (Idss m))) := by
  have hsh : shiftE (Idss m).length 0 (consList is ρp) = ρp := by
    rw [← hsp.length_eq]; exact shiftE_consList is ρp
  rw [AnnotValid_app]
  refine ⟨?_, mkTowerGo_validV (hIV m hm) (fun _ => (hI m hm).2) hsp⟩
  refine projAV_validV ?_
  rw [AnnotValid_liftN, hsh]
  exact blockBodyAV_validV hI hIV hchains

/-- **The block former leaf's P currency**: graded at the hereditary
premise, valid under the tower. -/
theorem blockTyAV_wellDenotedV {m : Nat} (hm : m < k)
    {pps : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V}
    (hok : ParamsOkG k w ρ uf Idss Chs m pps)
    (hval : UnderTowerValid ρ
      (.app (projAV m ((blockBodyG k w uf Idss Chs).liftN
          (Idss m).length 0))
        (mkTowerGo (uf m) (Idss m))) pps) :
    WellDenotedV V ρ (blockTyG k w uf Idss Chs pps m) :=
  ⟨blockTyG_wellDenoted hm hok, mkLamsC_validV (m := w + 1) hval⟩

end Currency

end ConLeche.Model
