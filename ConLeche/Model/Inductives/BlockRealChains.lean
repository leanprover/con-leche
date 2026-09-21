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

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
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


/-! ## The real chain from the constructor's syntactic entries -/

section RealOf

variable {k w nP nF m : Nat} {ρp : Nat → V} {uf : Nat → Nat} {Idss : Nat → List AnnotTerm}
  {rsss : Nat → List (List Bool)} {tgtsss : Nat → List (List Nat)}
  {tlsss : Nat → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eisss : Nat → List (List (List AnnotTerm))} {Fsss Esss : Nat → List (List AnnotTerm)}
  {ks : List RecFieldKind} {tgts : List Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
  {Fs₀ Fs Es : List AnnotTerm} {Eis : List (List AnnotTerm)}
  {ppsOf : Nat → List (Nat × Nat × AnnotTerm)} {AOf : Nat → AnnotTerm}

/-- **One block constructor's REAL chain, from its syntactic entries**
(`declNative`'s `hreal` at `k` members).  The recursive and reflexive
entries are the TARGET member's leaf at the parameter variables and the
field's index readings (`BlockCtorDataI.recEntry`/`.reflEntry`, whose
`m.acval (Tof i) ψ` is `AOf i` here); `blockLeafApp` folds each to the
target's component of the least tuple, which is exactly the slot's
value.

The target indirection costs ONE base fact the one-member route never
needed: `blockLeafApp` wants the frame to satisfy the TARGET's
parameter telescope, while the constructor's frame satisfies its OWN
member's.  `hρpOf` is that fact at every member, and its producer is
`blockParamsIff` — official's `checkBlockAgree` read semantically. -/
theorem blockChainReal_of
    (hI : BlockIdxOk (V := V) k uf ρp Idss)
    (hokI : BlockChainsOkI k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    (hC₀ : ChainFactsB k w nP nF ρp uf Idss m ks tgts tls Fs₀ Eis Es)
    (hlenPpsOf : ∀ c, c < k → (ppsOf c).length = nP + (Idss c).length)
    (hIdsOf : ∀ c, c < k → Idss c = ((ppsOf c).drop nP).map (·.2.2))
    (hρpOf : ∀ c, c < k → Sat V (((ppsOf c).take nP).map (·.2.2)).reverse ρp)
    (hA : ∀ i, i < nF → recAt nP ks (nP + i) → ∀ σ : Nat → V, interp V σ (AOf i)
      = interp V (fun j => ρp (j + nP))
          (blockTyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss
            (ppsOf (tgts.getD i 0)) (tgts.getD i 0)))
    (hFs : Fs.length = nF)
    (hnb : ∀ i, i < nF →
      NoBVar (exclP (fun q => recAt nP ks q ∧ q < nP + i) (nP + i)) (Fs.getD i default))
    (hord : ∀ i, i < nF → ¬ recAt nP ks (nP + i) → Fs.getD i default = Fs₀.getD i default)
    (hrecE : ∀ i, i < nF → ks.getD i .ordinary = .recursive →
      Fs.getD i default
        = AnnotTerm.mkAppN (AOf i) (paramBvarsAt nP (nP + i) ++ Eis.getD i []))
    (hreflE : ∀ i, i < nF → ks.getD i .ordinary = .reflexive →
      Fs.getD i default
        = mkPisAV (tls.getD i [])
            (AnnotTerm.mkAppN (AOf i)
              (paramBvarsAt nP (nP + i + (tls.getD i []).length) ++ Eis.getD i [])))
    (hnoneT : ∀ i, ks.getD i .ordinary ≠ .reflexive → tls.getD i [] = [])
    (hbitsT : ∀ i, ∀ d ∈ tls.getD i [], (d.2.1 = 0 ↔ w = 0)) :
    ChainRealBI (blockFam k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
      k w ρp uf Idss (rsOf ks) tgts tls Eis 0 [] Fs₀ Fs := by
  refine chainRealBI_of hC₀ hFs hnb hord ?_
  intro i hi hr as as' hlenA hrel hsp'
  obtain ⟨-, -, hrec'⟩ := hC₀.gr i hi as' hsp'
  obtain ⟨htlt, hfit'⟩ := hrec' hr
  have hfitS : SlotFit (uf (tgts.getD i 0)) w ρp (Idss (tgts.getD i 0)) (tls.getD i [])
      (Eis.getD i []) as := by
    refine slotFit_congr_shadow hrel ?_ ?_ hfit'
    · rw [hlenA]; exact hC₀.nbT i hi hr
    · rw [hlenA]; exact hC₀.nbE i hi hr
  have hk := hr.2
  rw [Nat.add_sub_cancel_left] at hk
  rcases hk with hk | hk
  · -- a finitary field: the TARGET member's family at the readings' values
    have hnone := hnoneT i (by rw [hk]; intro h; cases h)
    rw [hrecE i hi hk, hnone, slotSet_nil]
    rw [hnone] at hfitS
    obtain ⟨-, hspE⟩ := SlotFit.fin hfitS
    have := blockLeafApp (c := tgts.getD i 0) htlt (hlenPpsOf _ htlt) (hIdsOf _ htlt) hI hokI
      (hρpOf _ htlt) (hA i hi hr) (as := as) (Eis := Eis.getD i []) hspE
    rw [hlenA] at this
    exact this
  · -- a reflexive field: the nested product of the target's family
    rw [hreflE i hi hk]
    unfold slotSet
    refine ConLeche.Semantics.interp_mkPisAV_piTele (v := w) (acc := [])
      (fun d hd => hbitsT i d hd) ?_
    intro bs hsp
    rw [List.nil_append, ← consList_append]
    obtain ⟨-, hspE⟩ := hfitS.2.2 bs hsp
    have hlenAB : (as ++ bs).length = i + (tls.getD i []).length := by
      rw [List.length_append, hlenA, hsp.length_eq, List.length_map]
    have := blockLeafApp (c := tgts.getD i 0) htlt (hlenPpsOf _ htlt) (hIdsOf _ htlt) hI hokI
      (hρpOf _ htlt) (hA i hi hr) (as := as ++ bs) (Eis := Eis.getD i []) hspE
    rw [hlenAB, ← Nat.add_assoc] at this
    exact this

/-- **The fixpoint leaf's fibre law at block member `m`** —
`blockCtorsLoop`'s `hfold`.  The member's leaf at the parameter
variables and a constructor's index readings folds to the MEMBER-LOCAL
tagged union of that member's own constructors' real chains: the leaf
is the least tuple's `m`-th component (`blockLeafApp`), and the
component's fibre is the indexed sum route's union
(`blockFam_app_eq_sum`). -/
theorem blockFold_of {A : AnnotTerm} {ppsAll : List (Nat × Nat × AnnotTerm)}
    {Fss' : List (List AnnotTerm)} {Eis : List AnnotTerm} {bs : List V}
    (hm : m < k)
    (hok : BlockChainsOk k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
    (hlenPps : ppsAll.length = nP + (Idss m).length)
    (hIdsm : Idss m = ((ppsAll.drop nP).map (·.2.2)))
    (hρp : Sat V ((ppsAll.take nP).map (·.2.2)).reverse ρp)
    (hA : ∀ σ : Nat → V, interp V σ A
      = interp V (fun j => ρp (j + nP))
          (blockTyAV k w uf Idss rsss tgtsss tlsss Eisss Fsss Esss ppsAll m))
    (hreal : ChainsRealBI (blockFam k w ρp uf Idss rsss tgtsss tlsss Eisss Fsss Esss)
      k w ρp uf Idss m (rsss m) (tgtsss m) (tlsss m) (Eisss m) (Fsss m) Fss' (Esss m))
    (hspE : SpineFit ρp (Idss m) (Eis.map (interp V (consList bs ρp)))) :
    interp V (consList bs ρp) (AnnotTerm.mkAppN A (paramBvarsAt nP (nP + bs.length) ++ Eis))
      = sumSet w (sumFibre w (consList (Eis.map (interp V (consList bs ρp))) ρp)
          (rChains (Idss m).length (Idss m).length Fss' (Esss m))) := by
  rw [blockLeafApp hm hlenPps hIdsm hok.hI hok.hok hρp hA hspE,
    blockFam_app_eq_sum hok hm hreal hspE]

end RealOf

end ConLeche.Model
