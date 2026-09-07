import Lech.SetP.DirectFix.FixRealChainsP
import Lech.SetP.DirectSum.SumIntroP

/-!
# The fixed-point leaf's P currency (task #188)

The former's leaf `directFixTyAVI` at the P carrier: closed
(`directFixTyAVI_below`), graded and inhabiting its type's reading
(`FixLeafI.lean`'s `directFixTyAVI_ok2/_mem` at the hereditary premise
`ParamsOkXI`, walked from the former's data — `fixLeafWalks`), and
bit-valid (`AnnotValidV`, the annotation's second currency): the
functor's λ's are valid over the X-chains, which are valid at every
family (`fixChainWalkValid`, the walk of `FixChainsP.lean` for the
validity predicate — the entries' validity carries off the recursive
slots exactly as their grading, `AnnotValidV_congr_noBVar`).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Validity ignores the variables a term does not mention -/

theorem AnnotValidV_congr_noBVar :
    ∀ (e : AVExpr) {P : Nat → Prop} {σ σ' : Nat → V},
      NoBVar P e → AgreeOff P σ σ' → (AnnotValidV V σ e ↔ AnnotValidV V σ' e) := by
  intro e
  induction e with
  | bvar i => intros; simp
  | sort u => intros; simp
  | const c us => intros; simp
  | app f a ihf iha =>
    intro P σ σ' h hag
    rw [AnnotValidV_app, AnnotValidV_app, ihf h.1 hag, iha h.2 hag]
  | lam v A b ihA ihb =>
    intro P σ σ' h hag
    rw [AnnotValidV_lam, AnnotValidV_lam, ihA h.1 hag, interp2_congr_noBVar A h.1 hag]
    exact and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihb h.2 (agreeOff_cons hag x)))
  | pi u v A B ihA ihB =>
    intro P σ σ' h hag
    rw [AnnotValidV_pi, AnnotValidV_pi, ihA h.1 hag, interp2_congr_noBVar A h.1 hag]
    refine and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl (ihB h.2 (agreeOff_cons hag x)))
      (imp_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    rw [interp2_congr_noBVar B h.2 (agreeOff_cons hag x)]
  | letE T v b ihT ihv ihb =>
    intro P σ σ' h hag
    rw [AnnotValidV_letE, AnnotValidV_letE, ihT h.1 hag, ihv h.2.1 hag,
      ihb h.2.2 (agreeOff_cons_of hag (interp2_congr_noBVar v h.2.1 hag))]
  | eqE T a b ihT iha ihb =>
    intro P σ σ' h hag
    rw [AnnotValidV, AnnotValidV, iha h.2.1 hag, ihb h.2.2 hag]
  | proj i e ihe =>
    intro P σ σ' h hag
    rw [AnnotValidV_proj, AnnotValidV_proj, ihe h hag]
  | prf => intros; simp

/-! ## The X-chains, valid at every family -/

section Valid

variable {u w : Nat} {ρp : Nat → V} {Ids : List AVExpr} {nP nF : Nat} {ks : List RecFieldKind}
  {Fs : List AVExpr} {Eis : List (List AVExpr)} {Es : List AVExpr}

/-- The validity facts beside `ChainFacts`. -/
structure ChainValidFacts (nP nF : Nat) (ρp : Nat → V) (ks : List RecFieldKind)
    (Fs : List AVExpr) (Eis : List (List AVExpr)) (Es : List AVExpr) : Prop where
  grV : ∀ i, i < nF → ∀ as' : List V, SpineFit ρp ((shadowFs nP ks nF Fs).take i) as' →
    AnnotValidV V (consList as' ρp) (Fs.getD i default) ∧
    (recAt nP ks (nP + i) → ∀ E ∈ Eis.getD i [], AnnotValidV V (consList as' ρp) E)
  grEV : ∀ as' : List V, SpineFit ρp (shadowFs nP ks nF Fs) as' →
    ∀ E ∈ Es, AnnotValidV V (consList as' ρp) E

/-- The λ-tower over valid fields ending in a body valid at every
fitting spine is valid under the fields. -/
theorem underTowerValid_of_fields {b : AVExpr} {u : Nat} :
    ∀ {Fs : List AVExpr} {ρ : Nat → V}, FieldsValid ρ Fs →
      (∀ bs : List V, SpineFit ρ Fs bs → AnnotValidV V (consList bs ρ) b) →
      UnderTowerValid ρ b (Fs.map fun F => (u, u, F))
  | [], ρ, _, hb => hb [] trivial
  | F :: Fs, ρ, hv, hb => by
    refine ⟨hv.1, fun a ha => ?_⟩
    exact underTowerValid_of_fields (hv.2 a ha) fun bs hsp => by
      have := hb (a :: bs) ⟨ha, hsp⟩
      simpa [consList_cons] using this

/-- The tupler is valid at a frame whose index telescope is valid. -/
theorem tuplerAV_validV (hI : IdxOk u ρp Ids) (hV : FieldsValid ρp Ids) :
    AnnotValidV V ρp (tuplerAV u Ids) := by
  unfold tuplerAV
  apply mkLamsC_validV
  exact underTowerValid_of_fields hV fun bs hsp => mkTowerGo_validV hV (fun _ => hI.2) hsp

/-- **The validity walk** along the X-chain, beside a shadow spine. -/
theorem fixChainWalkValid (hI : IdxOk u ρp Ids) (hIV : FieldsValid ρp Ids) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V}
    (hC : ChainFacts u w nP nF ρp Ids ks Fs Eis Es) (hCV : ChainValidFacts nP nF ρp ks Fs Eis Es) :
    ∀ (m : Nat) (as as' : List V), nF - as.length = m → as.length ≤ nF →
      ShadowRel nP ks as as' → SpineFit ρp ((shadowFs nP ks nF Fs).take as.length) as' →
      FieldsValid (consList as (cons t (cons X ρp)))
        (chainXIGo u Ids (rsOf ks) Eis (Fs.drop as.length) as.length ++
          [idxEqAV (eqsXI Ids.length nF Es)]) := by
  intro m
  induction m with
  | zero =>
    intro as as' hm hle hrel hsp
    have hlen : as.length = nF := by omega
    have hdrop : Fs.drop as.length = [] := by rw [List.drop_eq_nil_iff, hC.hFs]; omega
    rw [hdrop]
    simp only [chainXIGo, List.nil_append, FieldsValid]
    have hspF : SpineFit ρp (shadowFs nP ks nF Fs) as' := by
      rwa [hlen, List.take_of_length_le (by rw [shadowFs_length]; exact Nat.le_refl _)] at hsp
    have hag := agreeOff_shadow hrel ρp
    rw [hlen] at hag
    refine ⟨idxEqAV_validV fun e he => ?_, fun _ _ => trivial⟩
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
    have hl' : l < Ids.length := List.mem_range.mp hl
    have hEmem : Es.getD l default ∈ Es := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hC.hEs]; exact hl')]
      exact List.getElem_mem _
    constructor
    · show AnnotValidV V _ ((Es.getD l default).liftN 2 nF)
      rw [← hlen, AnnotValidV_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl,
        shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
      exact (AnnotValidV_congr_noBVar _ (hC.nbEs _ hEmem) hag).mpr (hCV.grEV as' hspF _ hEmem)
    · show AnnotValidV V _ (projAV l (.bvar nF))
      exact projAV_validV (by simp)
  | succ m ih =>
    intro as as' hm hle hrel hsp
    have hi : as.length < nF := by omega
    have hdrop : Fs.drop as.length = Fs.getD as.length default :: Fs.drop (as.length + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hC.hFs]; exact hi), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hC.hFs]; exact hi)]
      rfl
    rw [hdrop, chainXIGo_cons, List.cons_append]
    have hag := agreeOff_shadow hrel ρp
    obtain ⟨hok', hbnd', hrec'⟩ := hC.gr as.length hi as' hsp
    obtain ⟨hv', hrecV'⟩ := hCV.grV as.length hi as' hsp
    have hFnb := hC.nb as.length hi
    have hvF : interp2 V (consList as ρp) (Fs.getD as.length default)
        = interp2 V (consList as' ρp) (Fs.getD as.length default) :=
      interp2_congr_noBVar _ hFnb hag
    have hnext : ∀ (a a' : V), (¬ recAt nP ks (nP + as.length) → a' = a) →
        a' ∈ˢ interp2 V (consList as' ρp)
          (if recAt nP ks (nP + as.length) then AVExpr.sort 0 else Fs.getD as.length default) →
        FieldsValid (consList (as ++ [a]) (cons t (cons X ρp)))
          (chainXIGo u Ids (rsOf ks) Eis (Fs.drop (as.length + 1)) (as.length + 1) ++
            [idxEqAV (eqsXI Ids.length nF Es)]) := by
      intro a a' ha ha'
      have h := ih (as ++ [a]) (as' ++ [a']) (by simp; omega) (by simp; omega)
        (ShadowRel.snoc hrel ha) (by
          rw [List.length_append, List.length_singleton, shadowFs_take_succ hi]
          exact SpineFit.append hsp ⟨ha', trivial⟩)
      simpa only [List.length_append, List.length_singleton] using h
    by_cases hr : recAt nP ks (nP + as.length)
    · have hrs : (rsOf ks).getD as.length false = true := by
        have h2 := hr.2
        rw [Nat.add_sub_cancel_left] at h2
        exact (rsOf_getD_iff (by rw [hC.hks]; exact hi)).mpr h2
      obtain ⟨hEok', hspE'⟩ := hrec' hr
      have hEok : ∀ E ∈ Eis.getD as.length [], AnnotOk2 V (consList as ρp) E := fun E hE =>
        (AnnotOk2_congr_noBVar E (hC.nbE as.length hi hr E hE) hag).mpr (hEok' E hE)
      have hEv : ∀ E ∈ Eis.getD as.length [], AnnotValidV V (consList as ρp) E := fun E hE =>
        (AnnotValidV_congr_noBVar E (hC.nbE as.length hi hr E hE) hag).mpr (hrecV' hr E hE)
      have hmap : (Eis.getD as.length []).map (interp2 V (consList as ρp))
          = (Eis.getD as.length []).map (interp2 V (consList as' ρp)) := by
        apply List.map_congr_left
        intro E hE
        exact interp2_congr_noBVar E (hC.nbE as.length hi hr E hE) hag
      have hspE : SpineFit ρp Ids ((Eis.getD as.length []).map (interp2 V (consList as ρp))) := by
        rw [hmap]; exact hspE'
      obtain ⟨hval, -, -⟩ := recSlot_facts hI hX as t hEok hspE
      have hx : xEntry u Ids (rsOf ks) Eis (Fs.getD as.length default) as.length
          = .app (.bvar (as.length + 1))
            (AVExpr.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0)
              ((Eis.getD as.length []).map (·.liftN 2 as.length))) := by
        unfold xEntry; rw [if_pos hrs]
      rw [hx]
      refine ⟨?_, fun a ha => ?_⟩
      · rw [AnnotValidV_app]
        refine ⟨by simp, mkAppN_validV ?_ ?_⟩
        · rw [AnnotValidV_liftN, shiftE_Xframe]
          exact tuplerAV_validV hI hIV
        · intro E' hE'
          obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hE'
          rw [AnnotValidV_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl,
            shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
          exact hEv E hE
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
      have hx : xEntry u Ids (rsOf ks) Eis (Fs.getD as.length default) as.length
          = (Fs.getD as.length default).liftN 2 as.length := by
        unfold xEntry; rw [if_neg (by rw [hrs]; exact Bool.false_ne_true)]
      rw [hx]
      refine ⟨?_, fun a ha => ?_⟩
      · rw [AnnotValidV_liftN, shiftE_consList_len, show (2 : Nat) = 1 + 1 from rfl,
          shiftE_succ_cons, shiftE_succ_cons, shiftE_zero_zero]
        exact (AnnotValidV_congr_noBVar _ hFnb hag).mpr hv'
      · rw [consList_snoc']
        rw [interp2_chainXI_ord, hvF] at ha
        exact hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)

/-- **The X-chain, valid**, from the walk at the empty spine. -/
theorem fixChainValid_of (hI : IdxOk u ρp Ids) (hIV : FieldsValid ρp Ids) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V}
    (hC : ChainFacts u w nP nF ρp Ids ks Fs Eis Es) (hCV : ChainValidFacts nP nF ρp ks Fs Eis Es) :
    FieldsValid (cons t (cons X ρp)) (chainXI u Ids Ids.length (rsOf ks) Eis Fs Es) := by
  have h := fixChainWalkValid hI hIV hX (t := t) hC hCV nF [] [] (by simp) (by simp)
    (ShadowRel.nil nP ks) trivial
  simp only [List.length_nil, List.drop_zero, consList_nil] at h
  rw [chainXI, hC.hFs]
  exact h

end Valid

/-! ## Closedness -/

section Below

variable {u w nP nIdx nF : Nat} {Ids Fs Es : List AVExpr} {rs : List Bool}
  {tls : List (List (Nat × Nat × AVExpr))} {Eis : List (List AVExpr)}

omit [SetTheory V] in
theorem domsBelow_tuplerData {k : Nat} :
    ∀ {Ids : List AVExpr}, FieldsBelow k Ids → DomsBelow k (Ids.map fun F => (u, u, F))
  | [], _ => trivial
  | _ :: _, h => ⟨h.1, domsBelow_tuplerData h.2⟩

omit [SetTheory V] in
theorem tuplerAV_below (hIds : FieldsBelow nP Ids) :
    VExpr.bvarsBelow nP (tuplerAV u Ids).erase := by
  unfold tuplerAV
  refine mkLamsC_below (domsBelow_tuplerData hIds) ?_
  rw [List.length_map]
  exact mkTowerGo_below hIds

omit [SetTheory V] in
/-- The X-chain's entries from position `i` on, below the X-frame. -/
theorem chainXIGo_below (hIds : FieldsBelow nP Ids)
    (hEis : ∀ i, ∀ E ∈ Eis.getD i [], VExpr.bvarsBelow (nP + i) E.erase) :
    ∀ (Fs : List AVExpr) (i : Nat), FieldsBelow (nP + i) Fs →
      FieldsBelow (nP + 2 + i) (chainXIGo u Ids rs tls Eis Fs i)
  | [], _, _ => trivial
  | F :: Fs, i, hF => by
    rw [chainXIGo_cons]
    refine ⟨?_, ?_⟩
    · unfold xEntry
      split
      · simp only [AVExpr.erase_app, AVExpr.erase_bvar, VExpr.bvarsBelow]
        refine ⟨by omega, ?_⟩
        rw [AVExpr.erase_mkAppN]
        refine VExprAux.bvarsBelow_mkAppN ?_ ?_
        · rw [AVExpr.erase_liftN]
          have := VExprAux.bvarsBelow_liftN (i + 2) (tuplerAV u Ids).erase nP 0
            (tuplerAV_below (u := u) hIds)
          rwa [show nP + (i + 2) = nP + 2 + i from by omega] at this
        · intro a ha
          rw [List.map_map] at ha
          obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
          simp only [Function.comp, AVExpr.erase_liftN]
          have := VExprAux.bvarsBelow_liftN 2 E.erase (nP + i) i (hEis i E hE)
          rwa [show nP + i + 2 = nP + 2 + i from by omega] at this
      · rw [AVExpr.erase_liftN]
        have := VExprAux.bvarsBelow_liftN 2 F.erase (nP + i) i hF.1
        rwa [show nP + i + 2 = nP + 2 + i from by omega] at this
    · have := chainXIGo_below hIds hEis Fs (i + 1)
        (by rw [show nP + (i + 1) = nP + i + 1 from by omega]; exact hF.2)
      rwa [show nP + 2 + (i + 1) = nP + 2 + i + 1 from by omega] at this

omit [SetTheory V] in
/-- A constructor's X-chain, below the X-frame. -/
theorem chainXI_below (hIds : FieldsBelow nP Ids)
    (hEis : ∀ i, ∀ E ∈ Eis.getD i [], VExpr.bvarsBelow (nP + i) E.erase)
    (hFs : FieldsBelow nP Fs) (hEsLen : Es.length = nIdx)
    (hEs : ∀ E ∈ Es, VExpr.bvarsBelow (nP + Fs.length) E.erase) :
    FieldsBelow (nP + 2) (chainXI u Ids nIdx rs tls Eis Fs Es) := by
  unfold chainXI
  refine FieldsBelow_append_idxEq (by simpa using chainXIGo_below hIds hEis Fs 0 (by simpa using hFs))
    ?_
  intro e he
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
  have hl' : l < nIdx := List.mem_range.mp hl
  rw [chainXIGo_length]
  have hmem : Es.getD l default ∈ Es := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hEsLen]; exact hl')]
    exact List.getElem_mem _
  constructor
  · show VExpr.bvarsBelow _ ((Es.getD l default).liftN 2 Fs.length).erase
    rw [AVExpr.erase_liftN]
    have := VExprAux.bvarsBelow_liftN 2 (Es.getD l default).erase (nP + Fs.length) Fs.length
      (hEs _ hmem)
    rwa [show nP + Fs.length + 2 = nP + 2 + Fs.length from by omega] at this
  · show VExpr.bvarsBelow _ (projAV l (.bvar Fs.length)).erase
    exact projAV_below (by simp [VExpr.bvarsBelow])

omit [SetTheory V] in
/-- The functor's λ, below the parameter frame. -/
theorem fixBodyAVI_below {rss : List (List Bool)} {tlss : List (List (List (Nat × Nat × AVExpr)))} {Eiss : List (List (List AVExpr))}
    {Fss Ess : List (List AVExpr)} (hIds : FieldsBelow nP Ids)
    (hchains : ∀ chain ∈ chainsXI u Ids nIdx rss tlss Eiss Fss Ess, FieldsBelow (nP + 2) chain) :
    VExpr.bvarsBelow nP (fixBodyAVI u w Ids nIdx rss tlss Eiss Fss Ess).erase := by
  unfold fixBodyAVI
  rw [AVExpr.erase_mkAppN]
  refine VExprAux.bvarsBelow_mkAppN (by simp [VExpr.bvarsBelow]) ?_
  intro a ha
  simp only [List.map_cons, List.map_nil, List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · exact towerBodyAV_below hIds
  · unfold fixFunAVI famTyAV
    simp only [AVExpr.erase_lam, AVExpr.erase_pi, AVExpr.erase_sort, VExpr.bvarsBelow]
    refine ⟨⟨towerBodyAV_below hIds, trivial⟩, ?_, ?_⟩
    · rw [AVExpr.erase_liftN]
      exact VExprAux.bvarsBelow_liftN 1 (towerBodyAV u Ids).erase nP 0 (towerBodyAV_below hIds)
    · exact sumBodyAV_below hchains
  · exact nomatch h

omit [SetTheory V] in
/-- **The former's leaf is closed.** -/
theorem directFixTyAVI_below {pps : List (Nat × Nat × AVExpr)} {rss : List (List Bool)}
    {tlss : List (List (List (Nat × Nat × AVExpr)))} {Eiss : List (List (List AVExpr))} {Fss Ess : List (List AVExpr)}
    (hp : DomsBelow 0 pps) (hlen : pps.length = nP + nIdx)
    (hIdsLen : (((pps.drop nP).map (·.2.2))).length = nIdx)
    (hchains : ∀ chain ∈ chainsXI u Ids nIdx rss tlss Eiss Fss Ess, FieldsBelow (nP + 2) chain)
    (hIds : Ids = (pps.drop nP).map (·.2.2)) :
    VExpr.bvarsBelow 0 (directFixTyAVI u w pps Ids rss tlss Eiss Fss Ess).erase := by
  have hIdsB : FieldsBelow nP Ids := by
    rw [hIds]
    have := (DomsBelow.drop nP hp).fields
    rwa [Nat.zero_add] at this
  have hIL : Ids.length = nIdx := by rw [hIds]; exact hIdsLen
  refine mkLamsAV_below hp.mapC ?_
  rw [List.length_map, hlen, Nat.zero_add]
  simp only [AVExpr.erase_app, VExpr.bvarsBelow]
  refine ⟨?_, ?_⟩
  · rw [AVExpr.erase_liftN]
    have := VExprAux.bvarsBelow_liftN Ids.length
      (fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).erase nP 0
      (fixBodyAVI_below (w := w) (nIdx := Ids.length) hIdsB (by rw [hIL]; exact hchains))
    rw [hIL] at this ⊢
    exact this
  · have := mkTowerGo_below (w := u) hIdsB
    rwa [hIL] at this

end Below

/-! ## The leaf's currency -/

section Currency

variable {u w nP : Nat} {Ids : List AVExpr} {rss : List (List Bool)}
  {tlss : List (List (List (Nat × Nat × AVExpr)))} {Eiss : List (List (List AVExpr))} {Fss Ess : List (List AVExpr)}

/-- The body's validity at the frame below the parameters and the
index variables. -/
theorem fixBody_validV {ρp : Nat → V} (hI : IdxOk u ρp Ids) (hIV : FieldsValid ρp Ids)
    (hchains : ∀ X, X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids) → ∀ t, t ∈ˢ idxSet u ρp Ids →
      SumFieldsValid (cons t (cons X ρp)) (chainsXI u Ids Ids.length rss tlss Eiss Fss Ess))
    {is : List V} (hsp : SpineFit ρp Ids is) :
    AnnotValidV V (consList is ρp)
      (.app ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0)
        (mkTowerGo u Ids)) := by
  have hsh : shiftE Ids.length 0 (consList is ρp) = ρp := by
    rw [← hsp.length_eq]; exact shiftE_consList is ρp
  rw [AnnotValidV_app]
  refine ⟨?_, mkTowerGo_validV hIV (fun _ => hI.2) hsp⟩
  rw [AnnotValidV_liftN, hsh]
  unfold fixBodyAVI
  refine mkAppN_validV (by simp) ?_
  intro a ha
  simp only [List.mem_cons] at ha
  rcases ha with rfl | rfl | h
  · exact towerBodyAV_validV hIV
  · unfold fixFunAVI
    rw [AnnotValidV_lam]
    refine ⟨?_, fun X hX => ?_⟩
    · unfold famTyAV
      rw [AnnotValidV_pi]
      exact ⟨towerBodyAV_validV hIV, fun _ _ => trivial, fun h => absurd h (Nat.succ_ne_zero _)⟩
    · rw [(famTyAV_facts hI).1] at hX
      rw [AnnotValidV_lam]
      have hsh1 : shiftE 1 0 (cons X ρp) = ρp := by
        rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      refine ⟨?_, fun t ht => ?_⟩
      · rw [AnnotValidV_liftN, hsh1]; exact towerBodyAV_validV hIV
      · rw [interp2_liftN, hsh1, (idxTyAV_facts hI).1] at ht
        exact sumBodyAV_validV (hchains X hX t ht)
  · exact nomatch h

/-- **The former leaf's P currency**: graded at the hereditary premise,
valid under the tower. -/
theorem directFixTyAVI_okP {pps : List (Nat × Nat × AVExpr)} {ρ : Nat → V}
    (hok : ParamsOkXI u w ρ Ids rss tlss Eiss Fss Ess pps)
    (hval : UnderTowerValid ρ
      (.app ((fixBodyAVI u w Ids Ids.length rss tlss Eiss Fss Ess).liftN Ids.length 0)
        (mkTowerGo u Ids)) pps) :
    AnnotOkP V ρ (directFixTyAVI u w pps Ids rss tlss Eiss Fss Ess) :=
  ⟨directFixTyAVI_ok2 hok, mkLamsC_validV (m := w + 1) hval⟩

end Currency

end Lech.SetP
