module

public import ConLeche.Model.Inductives.BlockChains
public section

/-!
# The real chains against the X-chains, at k members (task #315 M3)

`FixRealChains.lean` at `k`.  At the environment holding all the
block's formers as their fixed-point leaves (`blockTyAV`), a
recursive field's domain reads to the TARGET member's leaf at the
parameter variables and the field's index expressions; along a
fitting spine that is the target's component of the least tuple at the
tuple of the expressions' values (`blockLeafApp`, through
`blockTyAV_fold`).  So the constructor's REAL chain is the X-chain the
operator was spelled from with the least tuple substituted for the
tuple variable (`ChainRealBI`), hereditarily along the real chain —
the walk keeps the shadow spine beside the real one exactly as along
the X-chain.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V]

/-! ## The leaf at a spine -/

/-- **A member's fixed-point leaf at the parameter variables and index
expressions** reads, under `as` field values at the parameter frame
`ρp`, to that member's component of the least tuple at the tuple of
the expressions' values. -/
theorem blockLeafApp {k w nP c : Nat} (hc : c < k) {pps : List (Nat × Nat × AnnotTerm)}
    {uf : Nat → Nat} {Idss : Nat → List AnnotTerm} {rsss : Nat → List (List Bool)}
    {tgtsss : Nat → List (List Nat)}
    {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
    {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}
    {ρp : Nat → V}
    (hlen : pps.length = nP + (Idss c).length)
    (hIds : Idss c = (pps.drop nP).map (·.2.2))
    (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hok : BlockChainsOkI k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    (hρp : Sat V ((pps.take nP).map (·.2.2)).reverse ρp)
    {A : AnnotTerm} (hA : ∀ σ : Nat → V, interp V σ A
      = interp V (fun j => ρp (j + nP))
          (blockTyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss pps c))
    {as : List V} {Eis : List AnnotTerm}
    (hsp : SpineFit ρp (Idss c) (Eis.map (interp V (consList as ρp)))) :
    interp V (consList as ρp) (AnnotTerm.mkAppN A (paramBvarsAt nP (nP + as.length) ++ Eis))
      = SetTheory.app
          (blockFam k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss c)
          (tupW (uf c) (Eis.map (interp V (consList as ρp)))) := by
  have hlenI : (Eis.map (interp V (consList as ρp))).length = (Idss c).length := hsp.length_eq
  have hps : (paramBvarsAt nP (nP + as.length)).map (interp V (consList as ρp))
      = (List.range nP).reverse.map ρp :=
    map_paramBvarsAt_interp fun j => consList_apply_add as ρp j
  rw [interp_mkAppN, ← List.foldl_map (f := interp V (consList as ρp)) (g := SetTheory.app),
    List.map_append, hps, hA]
  have hlenP : ((pps.take nP).map (·.2.2)).length = nP := by
    rw [List.length_map, List.length_take]; omega
  have hspP := spineFit_of_sat (Δ₀ := []) (Ds := (pps.take nP).map (·.2.2))
    (by rw [List.append_nil]; exact hρp)
  rw [hlenP] at hspP
  have hρ0 : consList ((List.range nP).reverse.map ρp) (fun j => ρp (j + nP)) = ρp :=
    consList_range_reverse nP ρp
  have hspAll : SpineFit (fun j => ρp (j + nP)) (pps.map (·.2.2))
      ((List.range nP).reverse.map ρp ++ Eis.map (interp V (consList as ρp))) := by
    rw [← List.take_append_drop nP pps, List.map_append]
    refine hspP.append ?_
    rw [hρ0, ← hIds]
    exact hsp
  have hframe : consList ((List.range nP).reverse.map ρp ++ Eis.map (interp V (consList as ρp)))
      (fun j => ρp (j + nP)) = consList (Eis.map (interp V (consList as ρp))) ρp := by
    rw [consList_append, hρ0]
  have hsh : shiftE (Idss c).length 0 (consList (Eis.map (interp V (consList as ρp))) ρp) = ρp := by
    rw [← hlenI]; exact shiftE_consList _ ρp
  have hfr : frameIdx (Idss c).length (consList (Eis.map (interp V (consList as ρp))) ρp)
      = Eis.map (interp V (consList as ρp)) := by
    rw [← hlenI]; exact frameIdx_consList' _ ρp
  have hbase : BlockBaseI k w (consList ((List.range nP).reverse.map ρp ++
      Eis.map (interp V (consList as ρp))) (fun j => ρp (j + nP)))
      uf Idss rsss tgtsss tlsss Eisss Fsss Esss c := by
    rw [hframe]
    refine ⟨?_, ?_, ?_⟩
    · rw [hsh]; exact hI
    · rw [hsh]; exact hok
    · rw [hsh, hfr]; exact hsp
  rw [blockTyAV_fold hc hspAll hbase, hframe, hsh, hfr]

/-! ## The real chain -/

section RealWalk

variable {k w nP nF m : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {ks : List RecFieldKind} {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
  {Fs₀ Fs : List AnnotTerm} {Eis : List (List AnnotTerm)} {Es : List AnnotTerm}

/-- **The real walk at k**: along the real chain `Fs`, beside a shadow
spine, against the X-source chain `Fs₀`. -/
theorem blockRealWalk {μ : Nat → V}
    (hC : ChainFactsB k w nP nF ρp uf Idss m ks tgts tls Fs₀ Eis Es)
    (hFs : Fs.length = nF)
    (hnb : ∀ i, i < nF →
      NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i)) (Fs.getD i default))
    (hord : ∀ i, i < nF → ¬ recAt nP ks (nP + i) → Fs.getD i default = Fs₀.getD i default)
    (hrec : ∀ i, i < nF → recAt nP ks (nP + i) → ∀ as as' : List V, as.length = i →
      ShadowRel nP ks as as' → SpineFit ρp ((shadowFs nP ks nF Fs₀).take i) as' →
      interp V (consList as ρp) (Fs.getD i default)
        = slotSet w (uf (tgts.getD i 0)) (consList as ρp) (tls.getD i []) (Eis.getD i [])
            (μ (tgts.getD i 0))) :
    ∀ (n : Nat) (as as' : List V), nF - as.length = n → as.length ≤ nF →
      ShadowRel nP ks as as' → SpineFit ρp ((shadowFs nP ks nF Fs₀).take as.length) as' →
      ChainRealBI μ k w ρp uf Idss (rsOf ks) tgts tls Eis as.length as
        (Fs₀.drop as.length) (Fs.drop as.length) := by
  intro n
  induction n with
  | zero =>
    intro as as' hn hle hrel hsp
    have h0 : Fs₀.drop as.length = [] := by rw [List.drop_eq_nil_iff, hC.hFs]; omega
    have h1 : Fs.drop as.length = [] := by rw [List.drop_eq_nil_iff, hFs]; omega
    rw [h0, h1]
    trivial
  | succ n ih =>
    intro as as' hn hle hrel hsp
    have hi : as.length < nF := by omega
    have hd0 : Fs₀.drop as.length = Fs₀.getD as.length default :: Fs₀.drop (as.length + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hC.hFs]; exact hi), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hC.hFs]; exact hi)]
      rfl
    have hd1 : Fs.drop as.length = Fs.getD as.length default :: Fs.drop (as.length + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [hFs]; exact hi), List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hFs]; exact hi)]
      rfl
    rw [hd0, hd1]
    have hag := agreeOff_shadow hrel ρp
    have hvF : interp V (consList as ρp) (Fs.getD as.length default)
        = interp V (consList as' ρp) (Fs.getD as.length default) :=
      interp_congr_noBVar _ (hnb as.length hi) hag
    have hnext : ∀ (a a' : V), (¬ recAt nP ks (nP + as.length) → a' = a) →
        a' ∈ˢ interp V (consList as' ρp)
          (if recAt nP ks (nP + as.length) then AnnotTerm.sort 0 else Fs₀.getD as.length default) →
        ChainRealBI μ k w ρp uf Idss (rsOf ks) tgts tls Eis (as.length + 1) (as ++ [a])
          (Fs₀.drop (as.length + 1)) (Fs.drop (as.length + 1)) := by
      intro a a' ha ha'
      have h := ih (as ++ [a]) (as' ++ [a']) (by simp; omega) (by simp; omega)
        (ShadowRel.snoc hrel ha) (by
          rw [List.length_append, List.length_singleton, shadowFs_take_succ hi]
          exact SpineFit.append hsp ⟨ha', trivial⟩)
      simpa only [List.length_append, List.length_singleton] using h
    show (if (rsOf ks).getD as.length false then _ else _) ∧ _
    by_cases hr : recAt nP ks (nP + as.length)
    · have hrs : (rsOf ks).getD as.length false = true := by
        have h2 := hr.2
        rw [Nat.add_sub_cancel_left] at h2
        exact (rsOf_getD_iff (by rw [hC.hks]; exact hi)).mpr h2
      rw [if_pos hrs]
      obtain ⟨-, -, hrec'⟩ := hC.gr as.length hi as' hsp
      obtain ⟨htlt, hfit'⟩ := hrec' hr
      have hfit : SlotFit (uf (tgts.getD as.length 0)) w ρp (Idss (tgts.getD as.length 0))
          (tls.getD as.length []) (Eis.getD as.length []) as :=
        slotFit_congr_shadow hrel (hC.nbT as.length hi hr) (hC.nbE as.length hi hr) hfit'
      refine ⟨⟨htlt, hfit, hrec as.length hi hr as as' rfl hrel hsp⟩, fun a ha => ?_⟩
      exact (hnext a shadowVal (fun h => absurd hr h) (by rw [if_pos hr]; exact shadowVal_mem))
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
      rw [if_neg (by rw [hrs]; exact Bool.false_ne_true)]
      refine ⟨hord as.length hi hr, fun a ha => ?_⟩
      rw [hvF, hord as.length hi hr] at ha
      exact hnext a a (fun _ => rfl) (by rw [if_neg hr]; exact ha)

/-- **The real chain against the X-source chain at k**, from the walk
at the empty spine. -/
theorem chainRealBI_of {μ : Nat → V}
    (hC : ChainFactsB k w nP nF ρp uf Idss m ks tgts tls Fs₀ Eis Es) (hFs : Fs.length = nF)
    (hnb : ∀ i, i < nF →
      NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i)) (Fs.getD i default))
    (hord : ∀ i, i < nF → ¬ recAt nP ks (nP + i) → Fs.getD i default = Fs₀.getD i default)
    (hrec : ∀ i, i < nF → recAt nP ks (nP + i) → ∀ as as' : List V, as.length = i →
      ShadowRel nP ks as as' → SpineFit ρp ((shadowFs nP ks nF Fs₀).take i) as' →
      interp V (consList as ρp) (Fs.getD i default)
        = slotSet w (uf (tgts.getD i 0)) (consList as ρp) (tls.getD i []) (Eis.getD i [])
            (μ (tgts.getD i 0))) :
    ChainRealBI μ k w ρp uf Idss (rsOf ks) tgts tls Eis 0 [] Fs₀ Fs := by
  have h := blockRealWalk hC hFs hnb hord hrec nF [] [] (by simp) (by simp)
    (ShadowRel.nil nP ks) trivial
  simpa using h

end RealWalk

end ConLeche.Model
