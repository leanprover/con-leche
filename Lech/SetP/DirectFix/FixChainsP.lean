import Lech.SetP.DirectFix.FixShadowP
import Lech.Semantics.Tower.FixFamI

/-!
# The X-chains, graded at every family (task #188)

The functor's premise (`XChainsOk`): at every family `X` over the index
tuples and every tuple `t`, a constructor's X-chain — its ordinary
domains lifted past `X` and `t`, its recursive slots reading `X ⟨e⃗⟩`,
the index-equation terminator — is graded (`FieldsOkB`) and its
recursive slots fit (`SlotsFitX`).  The walk along the chain keeps a
**shadow spine** beside the X-chain's values: the same values at the
ordinary slots and a truth value at the recursive ones, which fits the
shadow fields (`shadowFs`: the ordinary domains, `Sort 0` at the
recursive positions) and hence satisfies the shadow context of
`FixShadowP.lean`, where every entry is graded; the entries, the index
expressions and the terminator mention no recursive slot, so their
grading and value carry from the shadow frame to the X-frame
(`interp2_congr_noBVar`, `AnnotOk2_congr_noBVar`).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## Kit -/

/-- The recursive positions as the functor's Bool list. -/
def rsOf (ks : List RecFieldKind) : List Bool := ks.map fun k => decide (k = .recursive)

omit [SetTheory V] in
theorem rsOf_getD {ks : List RecFieldKind} {i : Nat} (hi : i < ks.length) :
    (rsOf ks).getD i false = decide (ks.getD i .ordinary = .recursive) := by
  simp only [rsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

omit [SetTheory V] in
theorem rsOf_getD_iff {ks : List RecFieldKind} {i : Nat} (hi : i < ks.length) :
    (rsOf ks).getD i false = true ↔ ks.getD i .ordinary = .recursive := by
  rw [rsOf_getD hi, decide_eq_true_eq]

omit [SetTheory V] in
theorem rsOf_length (ks : List RecFieldKind) : (rsOf ks).length = ks.length := by simp [rsOf]

/-- The shadow fields: the ordinary domains, `Sort 0` at the recursive
positions. -/
def shadowFs (nP : Nat) (ks : List RecFieldKind) (nF : Nat) (Fs : List AVExpr) : List AVExpr :=
  (List.range nF).map fun i => if recAt nP ks (nP + i) then .sort 0 else Fs.getD i default

omit [SetTheory V] in
theorem shadowFs_length {nP nF : Nat} {ks : List RecFieldKind} {Fs : List AVExpr} :
    (shadowFs nP ks nF Fs).length = nF := by simp [shadowFs]

omit [SetTheory V] in
theorem shadowFs_getElem? {nP nF : Nat} {ks : List RecFieldKind} {Fs : List AVExpr} {i : Nat}
    (hi : i < nF) :
    (shadowFs nP ks nF Fs)[i]?
      = some (if recAt nP ks (nP + i) then .sort 0 else Fs.getD i default) := by
  simp [shadowFs, List.getElem?_map, List.getElem?_range hi]

omit [SetTheory V] in
theorem shadowFs_take_succ {nP nF : Nat} {ks : List RecFieldKind} {Fs : List AVExpr} {i : Nat}
    (hi : i < nF) :
    (shadowFs nP ks nF Fs).take (i + 1)
      = (shadowFs nP ks nF Fs).take i ++
          [if recAt nP ks (nP + i) then .sort 0 else Fs.getD i default] := by
  rw [List.take_add_one, shadowFs_getElem? hi]
  rfl

omit [SetTheory V] in
/-- The shadow context below field `i` is the shadow fields below `i`
over the parameters. -/
theorem shadowCtx_drop_fields {nP nF : Nat} {ks : List RecFieldKind}
    {ds : List (Nat × Nat × AVExpr)} (hlen : ds.length = nP + nF) {i : Nat} (hi : i ≤ nF) :
    (shadowCtx nP ks (nP + nF) ((ds.map (·.2.2)).reverse)).drop (nP + nF - (nP + i))
      = ((shadowFs nP ks nF ((ds.drop nP).map (·.2.2))).take i).reverse ++
          ((ds.take nP).map (·.2.2)).reverse := by
  have hlenS : ((shadowFs nP ks nF ((ds.drop nP).map (·.2.2))).take i).length = i := by
    rw [List.length_take, shadowFs_length]; omega
  have hlenP : (((ds.take nP).map (·.2.2)).reverse).length = nP := by
    simp [List.length_take, hlen]
  apply List.ext_getElem?
  intro q
  rw [List.getElem?_drop]
  by_cases hq : q < i + nP
  · rw [shadowCtx_getElem? (by omega)]
    by_cases hqi : q < i
    · -- a shadow field entry
      rw [List.getElem?_append_left (by rw [List.length_reverse, hlenS]; exact hqi),
        List.getElem?_reverse (by rw [hlenS]; exact hqi), hlenS,
        List.getElem?_take_of_lt (by omega), shadowFs_getElem? (by omega)]
      congr 1
      have e1 : nP + nF - 1 - (nP + nF - (nP + i) + q) = nP + (i - 1 - q) := by omega
      rw [e1]
      split
      · rfl
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse
          (by simp [hlen]; omega), List.getElem?_map, List.getElem?_map, List.getElem?_drop]
        simp only [List.length_map, hlen]
        rw [show nP + nF - 1 - (nP + nF - (nP + i) + q) = nP + (i - 1 - q) from by omega]
    · -- a parameter entry
      have hq' : q - i < nP := by omega
      have hidx : nP - 1 - (q - i) < ds.length := by omega
      have hlenP' : (((ds.take nP).map (·.2.2))).length = nP := by
        simp [List.length_take, hlen]
      have hR : (((ds.take nP).map (·.2.2)).reverse)[q - i]?
          = some (ds.getD (nP - 1 - (q - i)) default).2.2 := by
        rw [List.getElem?_reverse (by rw [hlenP']; exact hq'), hlenP', List.getElem?_map,
          List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hidx,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
        rfl
      have hL : (if recAt nP ks (nP + nF - 1 - (nP + nF - (nP + i) + q)) then AVExpr.sort 0
            else ((ds.map (·.2.2)).reverse).getD (nP + nF - (nP + i) + q) default)
          = (ds.getD (nP - 1 - (q - i)) default).2.2 := by
        rw [if_neg, List.getD_eq_getElem?_getD, List.getElem?_reverse (by simp [hlen]; omega)]
        · simp only [List.length_map, hlen, List.getElem?_map]
          rw [show nP + nF - 1 - (nP + nF - (nP + i) + q) = nP - 1 - (q - i) from by omega,
            List.getElem?_eq_getElem hidx, List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hidx]
          rfl
        · intro h
          have := h.1
          omega
      rw [hL, List.getElem?_append_right (by rw [List.length_reverse, hlenS]; omega),
        List.length_reverse, hlenS, hR]
  · rw [List.getElem?_eq_none (by rw [shadowCtx_length]; omega),
      List.getElem?_eq_none (by rw [List.length_append, List.length_reverse, hlenS, hlenP]; omega)]

/-- A truth value: the shadow value at the recursive slots. -/
noncomputable def shadowVal : V := truthVal False

theorem shadowVal_mem : (shadowVal : V) ∈ˢ (univ 0 : V) := truthVal_mem_univ False 0

/-- The shadow spine tracks the X-chain's spine off the recursive
slots. -/
def ShadowRel (nP : Nat) (ks : List RecFieldKind) (as as' : List V) : Prop :=
  as'.length = as.length ∧
  ∀ l, l < as.length → ¬ recAt nP ks (nP + l) → as'.getD l pt = as.getD l pt

theorem consList_apply_lt' (as : List V) (σ : Nat → V) {k : Nat} (hk : k < as.length) :
    consList as σ k = as.getD (as.length - 1 - k) pt := by
  rw [consList_apply_lt as σ k hk, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by omega)]
  rfl

/-- The two frames agree off the recursive slots. -/
theorem agreeOff_shadow {nP : Nat} {ks : List RecFieldKind} {as as' : List V}
    (h : ShadowRel nP ks as as') (ρp : Nat → V) :
    AgreeOff (exclP (fun q => recAt nP ks q ∧ q < nP + as.length) (nP + as.length))
      (consList as ρp) (consList as' ρp) := by
  intro j hj
  by_cases hji : j < as.length
  · rw [consList_apply_lt' as ρp hji, consList_apply_lt' as' ρp (by rw [h.1]; exact hji), h.1]
    have hnr : ¬ recAt nP ks (nP + (as.length - 1 - j)) := by
      intro hr
      apply hj
      exact ⟨nP + (as.length - 1 - j), ⟨hr, by omega⟩, by omega, by omega⟩
    exact (h.2 (as.length - 1 - j) (by omega) hnr).symm
  · have h1 := consList_apply_add as ρp (j - as.length)
    have h2 := consList_apply_add as' ρp (j - as.length)
    rw [show j - as.length + as.length = j from by omega] at h1
    rw [h.1, show j - as.length + as.length = j from by omega] at h2
    rw [h1, h2]

theorem ShadowRel.nil (nP : Nat) (ks : List RecFieldKind) : ShadowRel (V := V) nP ks [] [] :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem ShadowRel.snoc {nP : Nat} {ks : List RecFieldKind} {as as' : List V}
    (h : ShadowRel nP ks as as') {a a' : V}
    (ha : ¬ recAt nP ks (nP + as.length) → a' = a) :
    ShadowRel nP ks (as ++ [a]) (as' ++ [a']) := by
  refine ⟨by simp [h.1], fun l hl hr => ?_⟩
  simp only [List.length_append, List.length_singleton] at hl
  by_cases hla : l < as.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hla,
      List.getElem?_append_left (by rw [h.1]; exact hla), ← List.getD_eq_getElem?_getD,
      ← List.getD_eq_getElem?_getD]
    exact h.2 l hla hr
  · have hl' : l = as.length := by omega
    subst hl'
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (Nat.le_refl _),
      List.getElem?_append_right (by rw [h.1]; exact Nat.le_refl _),
      h.1, Nat.sub_self]
    simp only [List.getElem?_cons_zero, Option.getD_some]
    exact ha hr

omit [SetTheory V] in
theorem mem_fvarLeaves_of_getAppArgs : ∀ (e a : Expr), a ∈ e.getAppArgs →
    ∀ l ∈ a.fvarLeaves, l ∈ e.fvarLeaves
  | .app f a', a, ha, l, hl => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    simp only [Expr.fvarLeaves, List.mem_append]
    rcases ha with ha | rfl
    · exact Or.inl (mem_fvarLeaves_of_getAppArgs f a ha l hl)
    · exact Or.inr hl
  | .bvar _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .fvar _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .sort _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .const _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .lam _ _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .forallE _ _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .letE _ _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .proj _ _ _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])
  | .lit _, _, ha, _, _ => absurd ha (by simp [Expr.getAppArgs])

/-! ## The walk -/

section Walk

variable {u w : Nat} {ρp : Nat → V} {Ids : List AVExpr} {nP nF : Nat} {ks : List RecFieldKind}
  {Fs : List AVExpr} {Eis : List (List AVExpr)} {Es : List AVExpr}

/-- The per-position facts the walk consumes: the entries, index
expressions and residual index readings mention no recursive slot
below them; at every shadow-fitting spine the entry is graded (in the
family's universe when ordinary and the family is not `Prop`), a
recursive entry's index expressions are graded and fit the index
telescope; the residual's index readings are graded at every
shadow-fitting field spine. -/
structure ChainFacts (u w nP nF : Nat) (ρp : Nat → V) (Ids : List AVExpr)
    (ks : List RecFieldKind) (Fs : List AVExpr) (Eis : List (List AVExpr)) (Es : List AVExpr) :
    Prop where
  hks : ks.length = nF
  hFs : Fs.length = nF
  hEs : Es.length = Ids.length
  nb : ∀ i, i < nF →
    NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i)) (Fs.getD i default)
  nbE : ∀ i, i < nF → recAt nP ks (nP + i) → ∀ E ∈ Eis.getD i [],
    NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i)) E
  nbEs : ∀ E ∈ Es, NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + nF) (nP + nF)) E
  gr : ∀ i, i < nF → ∀ as' : List V, SpineFit ρp ((shadowFs nP ks nF Fs).take i) as' →
    AnnotOk2 V (consList as' ρp) (Fs.getD i default) ∧
    (¬ recAt nP ks (nP + i) → w ≠ 0 →
      interp2 V (consList as' ρp) (Fs.getD i default) ∈ˢ (univ w : V)) ∧
    (recAt nP ks (nP + i) →
      (∀ E ∈ Eis.getD i [], AnnotOk2 V (consList as' ρp) E) ∧
      SpineFit ρp Ids ((Eis.getD i []).map (interp2 V (consList as' ρp))))
  grE : ∀ as' : List V, SpineFit ρp (shadowFs nP ks nF Fs) as' →
    ∀ E ∈ Es, AnnotOk2 V (consList as' ρp) E

/-- **The walk**: along the X-chain, beside a shadow spine. -/
theorem fixChainWalk (hI : IdxOk u ρp Ids) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V} (ht : t ∈ˢ idxSet u ρp Ids)
    (hC : ChainFacts u w nP nF ρp Ids ks Fs Eis Es) :
    ∀ (m : Nat) (as as' : List V), nF - as.length = m → as.length ≤ nF →
      ShadowRel nP ks as as' → SpineFit ρp ((shadowFs nP ks nF Fs).take as.length) as' →
      FieldsOkB w (consList as (cons t (cons X ρp)))
        (chainXIGo u Ids (rsOf ks) Eis (Fs.drop as.length) as.length ++
          [idxEqAV (eqsXI Ids.length nF Es)]) ∧
      SlotsFitX u ρp Ids (rsOf ks) Eis X t as.length as (Fs.drop as.length) := by
  intro m
  induction m with
  | zero =>
    intro as as' hm hle hrel hsp
    have hlen : as.length = nF := by omega
    have hdrop : Fs.drop as.length = [] := by
      rw [List.drop_eq_nil_iff, hC.hFs]; omega
    rw [hdrop]
    simp only [chainXIGo, List.nil_append, SlotsFitX, and_true]
    -- the terminator: the residual's index readings, carried from the
    -- shadow frame
    have hspF : SpineFit ρp (shadowFs nP ks nF Fs) as' := by
      rwa [hlen, List.take_of_length_le (by rw [shadowFs_length]; exact Nat.le_refl _)] at hsp
    have hag := agreeOff_shadow hrel ρp
    rw [hlen] at hag
    have hEok : ∀ E ∈ Es, AnnotOk2 V (consList as ρp) E := fun E hE =>
      (AnnotOk2_congr_noBVar E (hC.nbEs E hE) hag).mpr (hC.grE as' hspF E hE)
    refine ⟨idxEqAV_ok2 (eqsXI_ok2 hI ht hlen hEok hC.hEs), fun _ => idxEqAV_mem_univ _ _ _,
      fun _ _ => trivial⟩
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
    have hFnb := hC.nb as.length hi
    -- the entry's grading and value, carried from the shadow frame
    have hokF : AnnotOk2 V (consList as ρp) (Fs.getD as.length default) :=
      (AnnotOk2_congr_noBVar _ hFnb hag).mpr hok'
    have hvF : interp2 V (consList as ρp) (Fs.getD as.length default)
        = interp2 V (consList as' ρp) (Fs.getD as.length default) :=
      interp2_congr_noBVar _ hFnb hag
    -- the recursion at an extended spine
    have hnext : ∀ (a a' : V), (¬ recAt nP ks (nP + as.length) → a' = a) →
        a' ∈ˢ interp2 V (consList as' ρp)
          (if recAt nP ks (nP + as.length) then AVExpr.sort 0 else Fs.getD as.length default) →
        FieldsOkB w (consList (as ++ [a]) (cons t (cons X ρp)))
          (chainXIGo u Ids (rsOf ks) Eis (Fs.drop (as.length + 1)) (as.length + 1) ++
            [idxEqAV (eqsXI Ids.length nF Es)]) ∧
        SlotsFitX u ρp Ids (rsOf ks) Eis X t (as.length + 1) (as ++ [a])
          (Fs.drop (as.length + 1)) := by
      intro a a' ha ha'
      have h := ih (as ++ [a]) (as' ++ [a']) (by simp; omega) (by simp; omega)
        (ShadowRel.snoc hrel ha) (by
          rw [List.length_append, List.length_singleton, shadowFs_take_succ hi]
          exact SpineFit.append hsp ⟨ha', trivial⟩)
      simpa only [List.length_append, List.length_singleton] using h
    by_cases hr : recAt nP ks (nP + as.length)
    · -- a recursive slot
      have hrs : (rsOf ks).getD as.length false = true := by
        have h2 := hr.2
        rw [Nat.add_sub_cancel_left] at h2
        exact (rsOf_getD_iff (by rw [hC.hks]; exact hi)).mpr h2
      obtain ⟨hEok', hspE'⟩ := hrec' hr
      have hEok : ∀ E ∈ Eis.getD as.length [], AnnotOk2 V (consList as ρp) E := fun E hE =>
        (AnnotOk2_congr_noBVar E (hC.nbE as.length hi hr E hE) hag).mpr (hEok' E hE)
      have hmap : (Eis.getD as.length []).map (interp2 V (consList as ρp))
          = (Eis.getD as.length []).map (interp2 V (consList as' ρp)) := by
        apply List.map_congr_left
        intro E hE
        exact interp2_congr_noBVar E (hC.nbE as.length hi hr E hE) hag
      have hspE : SpineFit ρp Ids ((Eis.getD as.length []).map (interp2 V (consList as ρp))) := by
        rw [hmap]; exact hspE'
      obtain ⟨hval, hokX, huniv⟩ := recSlot_facts hI hX as t hEok hspE
      have hx : xEntry u Ids (rsOf ks) Eis (Fs.getD as.length default) as.length
          = .app (.bvar (as.length + 1))
            (AVExpr.mkAppN ((tuplerAV u Ids).liftN (as.length + 2) 0)
              ((Eis.getD as.length []).map (·.liftN 2 as.length))) := by
        unfold xEntry; rw [if_pos hrs]
      rw [hx]
      refine ⟨⟨hokX, fun _ => by rw [hval]; exact huniv, fun a ha => ?_⟩,
        fun _ => ⟨hEok, hspE⟩, fun a ha => ?_⟩
      · rw [consList_snoc']
        exact (hnext a shadowVal (fun h => absurd hr h) (by rw [if_pos hr]; exact shadowVal_mem)).1
      · rw [hx] at ha
        exact (hnext a shadowVal (fun h => absurd hr h) (by rw [if_pos hr]; exact shadowVal_mem)).2
    · -- an ordinary entry
      have hrs : (rsOf ks).getD as.length false = false := by
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
      have hokL : AnnotOk2 V (consList as (cons t (cons X ρp)))
          ((Fs.getD as.length default).liftN 2 as.length) :=
        (AnnotOk2_chainXI_ord _ as t X).mpr hokF
      have hvL : interp2 V (consList as (cons t (cons X ρp)))
          ((Fs.getD as.length default).liftN 2 as.length)
          = interp2 V (consList as' ρp) (Fs.getD as.length default) := by
        rw [interp2_chainXI_ord, hvF]
      refine ⟨⟨hokL, fun hw => by rw [hvL]; exact hbnd' hr hw, fun a ha => ?_⟩,
        fun h => absurd h (by rw [hrs]; exact Bool.false_ne_true), fun a ha => ?_⟩
      · rw [consList_snoc']
        rw [hvL] at ha
        exact (hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)).1
      · rw [hx, hvL] at ha
        exact (hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)).2

/-- **The X-chain, graded and fitting**, from the walk at the empty
spine. -/
theorem fixChain_of (hI : IdxOk u ρp Ids) {X : V}
    (hX : X ∈ˢ lfpFamSpace V w (idxSet u ρp Ids)) {t : V} (ht : t ∈ˢ idxSet u ρp Ids)
    (hC : ChainFacts u w nP nF ρp Ids ks Fs Eis Es) :
    FieldsOkB w (cons t (cons X ρp)) (chainXI u Ids Ids.length (rsOf ks) Eis Fs Es) ∧
    SlotsFitX u ρp Ids (rsOf ks) Eis X t 0 [] Fs := by
  have h := fixChainWalk hI hX ht hC nF [] [] (by simp) (by simp) (ShadowRel.nil nP ks) trivial
  simp only [List.length_nil, List.drop_zero, consList_nil] at h
  rw [chainXI, hC.hFs]
  exact h

end Walk

end Lech.SetP
