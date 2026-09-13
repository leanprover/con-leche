module

public import ConLeche.Model.Inductives.RoundTrip
public section

/-!
# R2 — the container-side round trip, per GROUP (task #279 M-C′, DESIGN §M.34)

`RoundTrip.lean` states the round trips per pin and proves the
container-side induction principle (`IndRep.carrier_induction`).  This
module runs R2's induction:

* **`R2Grp`** — R2 for every member of a container's group at once
  (`R2At` at the group's data, member by member): the induction is over
  the block's ONE least fixed point, so a recursive field into a
  sibling member gets its hypothesis in the same induction, at the
  sibling's pin;
* **`R2Pred`** — the induction predicate over the container's index
  tuples: at every member whose tuple this is, the round trip;
  **`r2Fam`** the carrier restricted to it;
* **`r2Grp_of_step`** — `R2Grp` from the STEP (`carrier_induction` at
  every member of the group);
* **`slot_finitary`** — a finitary recursive slot at the restricted
  family: the field's value is in the target member's carrier at its
  own readings (`slotRecover` + `leaf`) and satisfies the predicate at
  the target's tuple (`mem_restrictedFam`);
* **`fieldsFit_of_chainFit`** — a chain-fitting spine fits the REAL
  domains, position by position (an ordinary domain verbatim, a
  finitary recursive one through `slot_finitary`), with the induction
  hypothesis at every recursive position;
* **`r2_step`** — THE STEP at the datum level: ψ's ι at values sends
  the container constructor to the copy constructor at ψ's values,
  ψ⁻¹'s ι at values sends that to the container constructor at the
  MIXED values, and the mixed values ARE the fields — an ordinary
  position verbatim, a finitary container-recursive position by the
  induction hypothesis at the target member (the "round trip inside"),
  the remaining shapes (a TRANSPORT, whose round trip is R2 at the
  EARLIER pin; a REFLEXIVE position, η) by the named per-position
  hypothesis `hrest`.

The step's ι laws are taken in the shape `PsiSetup.fold_iota_vals` and
`InvSetup.fold_iota_vals` deliver them (`FoldValues.lean`), with the
fold terms abstracted to `Ψ`/`Φ'`; the bookkeeping facts of the copy's
constructor (its index readings at ψ's values are the container's at
the fields, its head reads as the container constructor at the pin's
readings, ψ's values fit its telescope) are the record's consequences
(`CopyCtorAsRead`, `psiVals_fit_copy`) and are hypotheses here.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The statement per group, and the induction predicate -/

/-- **R2 per GROUP**: the container-side round trip at every member `t`
of the group's container block, at the group's data (`c.dJ`, `c.ψ'`,
`c.DsA`, `c.base`), with ψ's term `Ψ t` (the table's entry at pin
`c.base + t`) and ψ⁻¹'s term `Φ t` (at the copy `k₀ + c.base + t`). -/
@[expose] def R2Grp (m : EnvModel V env) (ρ : Nat → V) (ps : List AnnotTerm) (c : CopyData V)
    (Ψ Φ : Nat → AnnotTerm) : Prop :=
  ∀ t, t < c.dJ.k → IndRepData.R2At m ρ ps ⟨c.dJ, t, c.ψ', c.DsA, c.base⟩ (Ψ t) (Φ t)

/-- **The induction predicate** over the container's index tuples: for
every member `t'` and fitting index spine `is'` whose tuple this is,
ψ⁻¹ after ψ at `is'` is the identity on the element.  `σ₀` is the
scratch block's parameter frame (ψ's terms read there), `σ` the
container's parameter frame on top of it (the pin's readings), `ρ` the
frame ψ⁻¹'s terms read at. -/
@[expose] def R2Pred (dJ : IndRepData V) (ψ' : Name → Nat) (ρ σ₀ σ : Nat → V)
    (Ψ Φ : Nat → AnnotTerm) (tup x : V) : Prop :=
  ∀ t', t' < dJ.k → ∀ is' : List V, SpineFit σ (dJ.IdsM t' ψ') is' → tup = dJ.tup ψ' t' is' →
    foldApp ρ (Φ t') is' (foldApp σ₀ (Ψ t') is' x) = x

/-- The container's carrier restricted to the predicate (the family
`carrier_induction` chain-fits at). -/
@[expose] noncomputable def r2Fam (dJ : IndRepData V) (ψ' : Name → Nat) (ρ σ₀ σ : Nat → V)
    (Ψ Φ : Nat → AnnotTerm) : V :=
  graph (fun i => sep (SetTheory.app (lfpFamSet (dJ.w ψ') (dJ.idx ψ' σ) (dJ.Φ ψ' σ)) i)
    (R2Pred dJ ψ' ρ σ₀ σ Ψ Φ i)) (dJ.idx ψ' σ)

/-- **R2 per group from the step**: every member's `R2At` is the
predicate at its own tuple, by `carrier_induction` at that member. -/
theorem r2Grp_of_step (m : EnvModel V env) {c : CopyData V} {ρ : Nat → V} {ps : List AnnotTerm}
    {Ψ Φ : Nat → AnnotTerm}
    (hrepT : ∀ t, t < c.dJ.k → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IndRep m (c.dJ.memberName t) cvT cvR mI rP rules c.dJ t)
    (hDsFit : SpineFit (consList (ps.map (interp V ρ)) ρ) (c.dJ.params c.ψ')
      (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ))))
    (hstep : ∀ tup, tup ∈ˢ c.dJ.idx c.ψ' (consList (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)))
        (consList (ps.map (interp V ρ)) ρ)) →
      ∀ (J : Nat) (fs : List V), J < c.dJ.ctorsA.length →
      c.dJ.ChainFit c.ψ' (consList (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)))
          (consList (ps.map (interp V ρ)) ρ))
        (r2Fam c.dJ c.ψ' ρ (consList (ps.map (interp V ρ)) ρ)
          (consList (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)))
            (consList (ps.map (interp V ρ)) ρ)) Ψ Φ) tup J fs →
      R2Pred c.dJ c.ψ' ρ (consList (ps.map (interp V ρ)) ρ)
        (consList (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)))
          (consList (ps.map (interp V ρ)) ρ)) Ψ Φ tup (c.dJ.inj c.ψ' J fs)) :
    R2Grp m ρ ps c Ψ Φ := by
  intro t ht is x his hx
  obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := hrepT t ht
  have h := hrep.carrier_induction c.ψ' hDsFit his
    (R2Pred c.dJ c.ψ' ρ (consList (ps.map (interp V ρ)) ρ)
      (consList (c.DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)))
        (consList (ps.map (interp V ρ)) ρ)) Ψ Φ) hstep x hx
  exact h t ht is his rfl

/-! ## The datum's chain lists, entry by entry -/

namespace IndRepData

variable (d : IndRepData V)

omit [SetTheory V] in
theorem Fss_getD (ψ : Name → Nat) {J : Nat} {cA : ConstantVal × Nat} (hJ : d.ctorsA[J]? = some cA) :
    (d.Fss ψ).getD J [] = ((d.dsF J ψ).drop d.nP).map (·.2.2) := by
  unfold IndRepData.Fss IndRepData.cdsC
  rw [List.getD_eq_getElem?_getD, fssOfR, List.getElem?_map, fixCtorDataList_getElem?, Nat.zero_add,
    hJ]
  rfl

omit [SetTheory V] in
theorem Ess_getD (ψ : Name → Nat) {J : Nat} {cA : ConstantVal × Nat} (hJ : d.ctorsA[J]? = some cA) :
    (d.Ess ψ).getD J [] = d.essC J ψ := by
  unfold IndRepData.Ess IndRepData.cdsC
  rw [List.getD_eq_getElem?_getD, essOfR, List.getElem?_map, fixCtorDataList_getElem?, Nat.zero_add,
    hJ]
  rfl

omit [SetTheory V] in
theorem Eiss_getD (ψ : Name → Nat) {J : Nat} {cA : ConstantVal × Nat} (hJ : d.ctorsA[J]? = some cA) :
    (d.Eiss ψ).getD J [] = d.eissC J ψ := by
  unfold IndRepData.Eiss IndRepData.cdsC
  rw [List.getD_eq_getElem?_getD, eissOfR, List.getElem?_map, fixCtorDataList_getElem?, Nat.zero_add,
    hJ]
  rfl

omit [SetTheory V] in
theorem tlss_getD (ψ : Name → Nat) {J : Nat} {cA : ConstantVal × Nat} (hJ : d.ctorsA[J]? = some cA) :
    (d.tlss ψ).getD J [] = d.tssF J ψ := by
  unfold IndRepData.tlss IndRepData.cdsC
  rw [List.getD_eq_getElem?_getD, tlssOfR, List.getElem?_map, fixCtorDataList_getElem?, Nat.zero_add,
    hJ]
  rfl

omit [SetTheory V] in
theorem rss_getD {J : Nat} (hJ : J < d.ctorsA.length) : d.rss.getD J [] = rsOf (d.ksF J) := by
  unfold IndRepData.rss rssOfK
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hJ]
  rfl

omit [SetTheory V] in
/-- The recursive flag at a position is membership in the recursive
positions. -/
theorem rss_getD_iff {J i : Nat} (hJ : J < d.ctorsA.length) (hi : i < (d.ksF J).length) :
    (d.rss.getD J []).getD i false = true ↔ i ∈ ConLeche.recIdxOf (d.ksF J) := by
  rw [d.rss_getD hJ, rsOf_getD_iff hi, mem_recIdxOf]
  exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩

end IndRepData

/-! ## Small list facts -/

theorem list_ext_getD {as bs : List V} (hlen : as.length = bs.length)
    (h : ∀ i, i < as.length → as.getD i pt = bs.getD i pt) : as = bs := by
  apply List.ext_getElem hlen
  intro i h1 h2
  have := h i h1
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem h2] at this

theorem getD_map_idxOf {l : List Nat} {i : Nat} (h : i ∈ l) (f : Nat → V) :
    (l.map f).getD (l.idxOf i) pt = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, getElem?_idxOf_of_mem h]
  rfl

/-- A spine fits a telescope when each value lies in its domain at the
prefix's frame, given the prefix fits (the fit built position by
position). -/
theorem spineFit_of_prefix_pointwise {Fs : List AnnotTerm} {fs : List V} {σ : Nat → V}
    (hlen : fs.length = Fs.length)
    (h : ∀ (n : Nat) (F : AnnotTerm) (f : V), Fs[n]? = some F → fs[n]? = some f →
      SpineFit σ (Fs.take n) (fs.take n) → f ∈ˢ interp V (consList (fs.take n) σ) F) :
    SpineFit σ Fs fs := by
  have hpre : ∀ n, n ≤ Fs.length → SpineFit σ (Fs.take n) (fs.take n) := by
    intro n
    induction n with
    | zero => intro _; simp only [List.take_zero]; trivial
    | succ n ih =>
      intro hn
      have hn' : n < Fs.length := by omega
      have hnf : n < fs.length := by rw [hlen]; exact hn'
      rw [List.take_succ_eq_append_getElem hn', List.take_succ_eq_append_getElem hnf]
      refine SpineFit.append (ih (Nat.le_of_lt hn')) ⟨?_, trivial⟩
      exact h n Fs[n] fs[n] (List.getElem?_eq_getElem hn') (List.getElem?_eq_getElem hnf)
        (ih (Nat.le_of_lt hn'))
  have := hpre Fs.length (Nat.le_refl _)
  rwa [List.take_length, ← hlen, List.take_length] at this

/-! ## A finitary recursive slot at the restricted family -/

/-- **A finitary recursive slot at the restricted family** (task #279
M-C′): at a finitary recursive position `i` of constructor `J`
targeting member `tgt`, with the field's readings graded and fitting
the target's telescope at the prefix frame, a value in the X-chain's
slot at the restricted family lies in the TARGET's carrier at the pin's
readings and the field's own readings (the slot's tuple is the target's
tuple, `slotRecover`; the fibre of the least fixed point is the leaf,
`leaf`) and satisfies the predicate at that tuple
(`mem_restrictedFam`). -/
theorem slot_finitary {m : EnvModel V env} {dJ : IndRepData V} {ψ' : Name → Nat}
    {ρ σ₀ σ : Nat → V} {Ψ Φ : Nat → AnnotTerm}
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {tgt : Nat}
    (hrep : IndRep m T cvT cvR mI rP rules dJ tgt)
    (hsat : Sat V (dJ.params ψ').reverse σ)
    {DsAv : List V} (hσ : σ = consList DsAv σ₀) (hDsFit : SpineFit σ₀ (dJ.params ψ') DsAv)
    {J i : Nat} {cA : ConstantVal × Nat} (hJ : dJ.ctorsA[J]? = some cA)
    (htgt : dJ.tgts J i = tgt) (hrec : (dJ.rss.getD J []).getD i false = true)
    (htl : (dJ.tssF J ψ').getD i [] = [])
    {ws : List V} (hws : ws.length = i)
    (hEok : ∀ E ∈ (dJ.eissF J ψ').getD i [], WellDenoted V (consList ws σ) E)
    (hEfit : SpineFit σ (dJ.IdsM tgt ψ')
      (((dJ.eissF J ψ').getD i []).map (interp V (consList ws σ))))
    {f : V}
    (hf : f ∈ˢ slotSet (dJ.w ψ') (dJ.u ψ') (consList ws σ) (((dJ.tlss ψ').getD J []).getD i [])
      (((dJ.Eiss ψ').getD J []).getD i []) (r2Fam dJ ψ' ρ σ₀ σ Ψ Φ)) :
    f ∈ˢ (DsAv ++ ((dJ.eissF J ψ').getD i []).map (interp V (consList ws σ))).foldl SetTheory.app
        (interp V σ₀ (m.acval T ψ')) ∧
      R2Pred dJ ψ' ρ σ₀ σ Ψ Φ
        (dJ.tup ψ' tgt (((dJ.eissF J ψ').getD i []).map (interp V (consList ws σ)))) f := by
  have hJlt : J < dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have htlD : ((dJ.tlss ψ').getD J []).getD i [] = [] := by rw [dJ.tlss_getD ψ' hJ, htl]
  rw [htlD, slotSet_nil] at hf
  have hshift : shiftE (i + ((dJ.tssF J ψ').getD i []).length) 0 (consList ws σ) = σ := by
    rw [htl, List.length_nil, Nat.add_zero, ← hws]
    exact shiftE_consList _ _
  have hslot := hrep.slotRecover ψ' σ hsat J i hJlt hrec (consList ws σ) hshift hEok
    (by rw [htgt]; exact hEfit)
  rw [htgt] at hslot
  rw [hslot] at hf
  have htup := hrep.tupMem ψ' σ hsat _ hEfit
  unfold r2Fam at hf
  rw [mem_restrictedFam htup] at hf
  obtain ⟨hf1, hf2⟩ := hf
  refine ⟨?_, hf2⟩
  rw [hrep.leaf ψ' σ₀ DsAv _ hDsFit (by rw [← hσ]; exact hEfit), ← hσ]
  exact hf1

/-- **A recursive entry's reading** at the field's frame: the target
member's leaf at the pin's readings and the field's readings
(`recEntry`, the parameter variables reading the frame's parameters,
the leaf closed). -/
theorem interp_recEntry {m : EnvModel V env} {env₀ : Env} {T : Name} {lps : List Name}
    {cvC : ConstantVal} {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool}
    {idxArgs : List Expr} {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {srcs : List (Option Nat)} {ks : List RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {tgtOf : Nat → Name}
    {nIdxOf : Nat → Nat}
    (hD : FixCtorDataI m env₀ T lps cvC nP nF nIdx resSort isProp large idxArgs ds Es srcs ks fvsP
      xFvs xrest Eiss tss tgtOf nIdxOf)
    (ψ : Name → Nat) {i : Nat} (hrec : ks.getD i .ordinary = .recursive) (hi : i < nF)
    {ws : List V} (hws : ws.length = i) {DsAv : List V} (hDsLen : DsAv.length = nP) (σ₀ : Nat → V) :
    interp V (consList ws (consList DsAv σ₀)) ((ds ψ).getD (nP + i) default).2.2
      = (DsAv ++ ((Eiss ψ).getD i []).map (interp V (consList ws (consList DsAv σ₀)))).foldl
          SetTheory.app (interp V σ₀ (m.acval (tgtOf i) ψ)) := by
  rw [hD.recEntry ψ i hrec hi, interp_mkAppN_map, List.map_append,
    map_paramBvarsAt_interp (e := i) (ρp := consList DsAv σ₀)
      (fun j => by rw [← hws]; exact consList_apply_add ws _ j),
    range_reverse_map_consList' hDsLen, interp_closed (V := V) (m.cval_closedL _ ψ) _ σ₀]

/-! ## The fields fit the real domains -/

set_option maxHeartbeats 800000 in
/-- **A chain-fitting spine fits the REAL domains** (task #279 M-C′), at
a container whose recursive fields are FINITARY (`hfin`): an ordinary
position's value is in its domain (`chainFit_fields`), a recursive
position's in the target member's carrier at its readings
(`slot_finitary`) — which is the recursive entry's reading
(`interp_recEntry`); and at every recursive position the induction
hypothesis at the target's tuple.  The recursive entries' readings are
graded and fit the target's telescope at any fitting prefix
(`hEntry`; from the constructor's grading, `idxFit_of_entry`). -/
theorem fieldsFit_of_chainFit {m : EnvModel V env} {dJ : IndRepData V} {ψ' : Name → Nat}
    {ρ σ₀ σ : Nat → V} {Ψ Φ : Nat → AnnotTerm}
    (hrepT : ∀ t, t < dJ.k → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IndRep m (dJ.memberName t) cvT cvR mI rP rules dJ t)
    (hsat : Sat V (dJ.params ψ').reverse σ)
    {DsAv : List V} (hσ : σ = consList DsAv σ₀) (hDsFit : SpineFit σ₀ (dJ.params ψ') DsAv)
    (hDsLen : DsAv.length = dJ.nP)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : dJ.ctorsA[J]? = some cA) {lpsT : List Name}
    (hC : FixCtorFactsAt m dJ.env₀ (dJ.memberName (dJ.mems J)) lpsT dJ.nP (dJ.nIdxAt (dJ.mems J))
      dJ.resSort dJ.isProp dJ.large dJ.idxF dJ.dsF dJ.esF dJ.srcsF dJ.ksF dJ.fvsPF dJ.xFvsF dJ.xrestF
      dJ.eissF dJ.tssF J cA (fun i => dJ.memberName (dJ.tgts J i)) (fun i => dJ.nIdxAt (dJ.tgts J i)))
    (htgts : ∀ i, dJ.tgts J i < dJ.k)
    (hfin : ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF J) → (dJ.ksF J).getD i .ordinary = .recursive ∧
      (dJ.tssF J ψ').getD i [] = [])
    (hEntry : ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF J) → ∀ ws : List V, ws.length = i →
      SpineFit σ ((((dJ.dsF J ψ').drop dJ.nP).map (·.2.2)).take i) ws →
      (∀ E ∈ (dJ.eissF J ψ').getD i [], WellDenoted V (consList ws σ) E) ∧
      SpineFit σ (dJ.IdsM (dJ.tgts J i) ψ')
        (((dJ.eissF J ψ').getD i []).map (interp V (consList ws σ))))
    {fs : List V} (hlen : fs.length = ((dJ.Fss ψ').getD J []).length)
    (hfields : ∀ (i : Nat) (F : AnnotTerm), ((dJ.Fss ψ').getD J [])[i]? = some F → ∀ f, fs[i]? = some f →
      ((dJ.rss.getD J []).getD i false = true →
        f ∈ˢ slotSet (dJ.w ψ') (dJ.u ψ') (consList (fs.take i) σ) (((dJ.tlss ψ').getD J []).getD i [])
          (((dJ.Eiss ψ').getD J []).getD i []) (r2Fam dJ ψ' ρ σ₀ σ Ψ Φ)) ∧
      ((dJ.rss.getD J []).getD i false = false → f ∈ˢ interp V (consList (fs.take i) σ) F)) :
    SpineFit σ ((dJ.Fss ψ').getD J []) fs ∧
    ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF J) →
      R2Pred dJ ψ' ρ σ₀ σ Ψ Φ
        (dJ.tup ψ' (dJ.tgts J i) (((dJ.eissF J ψ').getD i []).map (interp V (consList (fs.take i) σ))))
        (fs.getD i pt) := by
  have hJlt : J < dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  obtain ⟨-, -, hD⟩ := hC
  have hFs := dJ.Fss_getD ψ' hJ
  have hksLen : (dJ.ksF J).length = cA.2 := hD.ksLen
  have hnF : ((dJ.Fss ψ').getD J []).length = cA.2 := by
    rw [hFs, List.length_map, List.length_drop, hD.len ψ']
    omega
  -- one position, given the prefix fits
  have hpos : ∀ (n : Nat) (F : AnnotTerm) (f : V), ((dJ.Fss ψ').getD J [])[n]? = some F →
      fs[n]? = some f → SpineFit σ (((dJ.Fss ψ').getD J []).take n) (fs.take n) →
      f ∈ˢ interp V (consList (fs.take n) σ) F ∧
      (n ∈ ConLeche.recIdxOf (dJ.ksF J) →
        R2Pred dJ ψ' ρ σ₀ σ Ψ Φ
          (dJ.tup ψ' (dJ.tgts J n)
            (((dJ.eissF J ψ').getD n []).map (interp V (consList (fs.take n) σ))))
          f) := by
    intro n F f hF hf hpre
    have hnlt : n < cA.2 := by
      have := (List.getElem?_eq_some_iff.mp hF).1
      rwa [hnF] at this
    have hnfs : n < fs.length := (List.getElem?_eq_some_iff.mp hf).1
    have hFeq : F = ((dJ.dsF J ψ').getD (dJ.nP + n) default).2.2 := by
      have h := hF
      rw [hFs, List.getElem?_map, List.getElem?_drop] at h
      obtain ⟨dd, hdd, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [List.getD_eq_getElem?_getD, hdd]
      rfl
    have htake : (fs.take n).length = n := by rw [List.length_take]; omega
    by_cases hr : n ∈ ConLeche.recIdxOf (dJ.ksF J)
    · -- a (finitary) recursive position
      obtain ⟨hkind, htl⟩ := hfin n hr
      have hrec : (dJ.rss.getD J []).getD n false = true :=
        (dJ.rss_getD_iff hJlt (by rw [hksLen]; exact hnlt)).mpr hr
      have hslot := (hfields n F hF f hf).1 hrec
      rw [hFs] at hpre
      obtain ⟨hEok, hEfit⟩ := hEntry n hr (fs.take n) htake hpre
      obtain ⟨cvT', cvR', mI', rP', rules', hrep'⟩ := hrepT _ (htgts n)
      have h := slot_finitary hrep' hsat hσ hDsFit hJ rfl hrec htl htake hEok hEfit hslot
      refine ⟨?_, fun _ => h.2⟩
      rw [hFeq, hσ, interp_recEntry hD ψ' hkind hnlt htake hDsLen σ₀, ← hσ]
      exact h.1
    · -- an ordinary position
      have hord : (dJ.rss.getD J []).getD n false = false := by
        have := (dJ.rss_getD_iff hJlt (by rw [hksLen]; exact hnlt))
        cases hb : (dJ.rss.getD J []).getD n false
        · rfl
        · exact absurd (this.mp hb) hr
      exact ⟨(hfields n F hF f hf).2 hord, fun h => absurd h hr⟩
  have hfit : SpineFit σ ((dJ.Fss ψ').getD J []) fs :=
    spineFit_of_prefix_pointwise hlen fun n F f hF hf hpre => (hpos n F f hF hf hpre).1
  refine ⟨hfit, fun i hi => ?_⟩
  have hilt : i < cA.2 := by rw [← hksLen]; exact (mem_recIdxOf.mp hi).1
  have hifs : i < fs.length := by rw [hlen, hnF]; exact hilt
  have hiF : i < ((dJ.Fss ψ').getD J []).length := by rw [hnF]; exact hilt
  have hpre : SpineFit σ (((dJ.Fss ψ').getD J []).take i) (fs.take i) := spineFit_take' hfit (Nat.le_of_lt hiF)
  have h := (hpos i _ (fs.getD i pt) (List.getElem?_eq_getElem hiF)
    (by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hifs]; rfl) hpre).2 hi
  exact h

/-! ## The step -/

set_option maxHeartbeats 1600000 in
/-- **THE STEP** (task #279 M-C′, DESIGN §M.34): at a container constructor
`J` (its copy `J'`) and a spine `fs` fitting the real domains with the
induction hypotheses at the recursive positions, the predicate holds of
`inj J fs`: the terminator recovers the member and the readings
(`idxRecover`); the injection is the constructor's value (`ctor`); ψ's
ι at values sends it to the copy constructor at ψ's VALUES (`hιΨ`); the
copy constructor's index readings there are the container's (`hEs`),
so ψ⁻¹'s ι at values sends that to the container constructor at the
MIXED values (`hιΦ`, the head reading as the container constructor at
the pin's readings, `hheadφ`); and the mixed values are the fields —
an ordinary position verbatim, a finitary container-recursive position
by the induction hypothesis at the target member (`hIH`, the "round
trip inside"), the remaining positions (a TRANSPORT: R2 at the earlier
pin; a REFLEXIVE position: η) by the named hypothesis `hpos`'s third
arm.  The ι laws are in the shape `PsiSetup.fold_iota_vals`/
`InvSetup.fold_iota_vals` deliver them, the fold terms abstracted to
`Ψ` (at the container's members) and `Φ'` (at the scratch block's,
`Φ t = Φ' (k₀ + base + t)`); `VSψ`/`MIXED` name ψ's and ψ⁻¹'s value
spines. -/
theorem r2_step (m : EnvModel V env) {dJ d : IndRepData V} {ψ' ψ : Name → Nat} {ρ σ₀ σ : Nat → V}
    {Ψ Φ Φ' : Nat → AnnotTerm} {k₀ base : Nat}
    -- the container's representations, at every member
    (hrepT : ∀ t, t < dJ.k → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IndRep m (dJ.memberName t) cvT cvR mI rP rules dJ t)
    (hsat : Sat V (dJ.params ψ').reverse σ)
    {DsAv : List V} (hσ : σ = consList DsAv σ₀) (hDsFit : SpineFit σ₀ (dJ.params ψ') DsAv)
    (hDsLen : DsAv.length = dJ.nP)
    -- the constructor and its copy
    {J J' : Nat} {cA cA' : ConstantVal × Nat} (hJ : dJ.ctorsA[J]? = some cA)
    (hlenD : (dJ.dsF J ψ').length = dJ.nP + cA.2)
    (hpIff : ∀ ρ' : Nat → V, Sat V (dJ.params ψ').reverse ρ' ↔
      Sat V (((dJ.dsF J ψ').take dJ.nP).map (·.2.2)).reverse ρ')
    (hmemJ : dJ.mems J < dJ.k) (htgts : ∀ i, dJ.tgts J i < dJ.k)
    (hview : dJ.ksR J = dJ.ksF J ∧ dJ.tgtsR J = dJ.tgts J ∧ dJ.eissR J = dJ.eissF J ∧
      dJ.tssR J = dJ.tssF J)
    (hmemA : d.mems J' = k₀ + base + dJ.mems J)
    (hΦ : ∀ t, t < dJ.k → Φ t = Φ' (k₀ + base + t))
    -- the spine: it fits the real domains, the induction hypotheses at
    -- the recursive positions, the readings' facts, the terminator
    {fs : List V} (hfit : SpineFit σ ((dJ.Fss ψ').getD J []) fs)
    (hIH : ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF J) →
      R2Pred dJ ψ' ρ σ₀ σ Ψ Φ
        (dJ.tup ψ' (dJ.tgts J i)
          (((dJ.eissF J ψ').getD i []).map (interp V (consList (fs.take i) σ))))
        (fs.getD i pt))
    (hEsOk : ∀ E ∈ dJ.esF J ψ', WellDenoted V (consList fs σ) E)
    (hEsFit : SpineFit σ (dJ.IdsM (dJ.mems J) ψ') ((dJ.esF J ψ').map (interp V (consList fs σ))))
    (hEntryFit : ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF J) →
      SpineFit σ (dJ.IdsM (dJ.tgts J i) ψ')
        (((dJ.eissF J ψ').getD i []).map (interp V (consList (fs.take i) σ))))
    {X tup : V}
    (hall : EqAll (consList fs (cons tup (cons X σ)))
      (eqsXI (dJ.IdsC ψ').length ((dJ.Fss ψ').getD J []).length ((dJ.Ess ψ').getD J [])))
    -- ψ's ι at values (`PsiSetup.fold_iota_vals`), the fold terms abstracted
    {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {via : Nat → Nat → Option ViaSpec}
    (hιΨ : ∀ vs : List V, SpineFit σ₀ ((dJ.dsF J ψ').map (·.2.2)) (DsAv ++ vs) →
      ((dJ.esF J ψ').map (interp V (consList vs σ)) ++
          [(DsAv ++ vs).foldl SetTheory.app (interp V σ₀ (m.acval cA.1.name ψ'))]).foldl
          SetTheory.app (interp V σ₀ (Ψ (dJ.mems J)))
        = (psiVals (dJ.bb ψ') σ (ConLeche.recIdxOf (dJ.ksR J)) (useIh J) (via J) vs
            ((ConLeche.recIdxOf (dJ.ksR J)).map fun i =>
              lamTower (dJ.bb ψ') (consList (vs.take i) σ) ((dJ.tssR J ψ').getD i []) fun σ'' =>
                (((dJ.eissR J ψ').getD i []).map (interp V σ'') ++
                  [(Semantics.frameIdx (((dJ.tssR J ψ').getD i []).length) σ'').foldl SetTheory.app
                    (vs.getD i pt)]).foldl SetTheory.app (interp V σ₀ (Ψ (dJ.tgtsR J i))))).foldl
            SetTheory.app (interp V σ (head J)))
    -- ψ⁻¹'s ι at values (`InvSetup.fold_iota_vals`), the fold terms abstracted
    {head' : Nat → AnnotTerm} {useIhA : Nat → Nat → Bool}
    (hιΦ : ∀ vs' : List V, SpineFit ρ ((d.dsF J' ψ).map (·.2.2)) (paramVals d.nP ρ ++ vs') →
      ((d.esF J' ψ).map (interp V (consList (paramVals d.nP ρ ++ vs') ρ)) ++
          [(paramVals d.nP ρ ++ vs').foldl SetTheory.app (interp V ρ (m.acval cA'.1.name ψ))]).foldl
          SetTheory.app (interp V ρ (Φ' (d.mems J')))
        = (mixedVals (ConLeche.recIdxOf (d.ksR J')) (useIhA J') vs'
            ((ConLeche.recIdxOf (d.ksR J')).map fun i =>
              lamTower (d.bb ψ) (consList (vs'.take i) ρ) ((d.tssR J' ψ).getD i []) fun σ'' =>
                (((d.eissR J' ψ).getD i []).map (interp V σ'') ++
                  [(Semantics.frameIdx (((d.tssR J' ψ).getD i []).length) σ'').foldl SetTheory.app
                    (vs'.getD i pt)]).foldl SetTheory.app (interp V ρ (Φ' (d.tgtsR J' i))))).foldl
            SetTheory.app (interp V ρ (head' J')))
    -- ψ's values and ψ⁻¹'s mixed values, named
    {VSψ MIXED : List V}
    (hVS : VSψ = psiVals (dJ.bb ψ') σ (ConLeche.recIdxOf (dJ.ksR J)) (useIh J) (via J) fs
      ((ConLeche.recIdxOf (dJ.ksR J)).map fun i =>
        lamTower (dJ.bb ψ') (consList (fs.take i) σ) ((dJ.tssR J ψ').getD i []) fun σ'' =>
          (((dJ.eissR J ψ').getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((dJ.tssR J ψ').getD i []).length) σ'').foldl SetTheory.app
              (fs.getD i pt)]).foldl SetTheory.app (interp V σ₀ (Ψ (dJ.tgtsR J i)))))
    (hMIX : MIXED = mixedVals (ConLeche.recIdxOf (d.ksR J')) (useIhA J') VSψ
      ((ConLeche.recIdxOf (d.ksR J')).map fun i =>
        lamTower (d.bb ψ) (consList (VSψ.take i) ρ) ((d.tssR J' ψ).getD i []) fun σ'' =>
          (((d.eissR J' ψ).getD i []).map (interp V σ'') ++
            [(Semantics.frameIdx (((d.tssR J' ψ).getD i []).length) σ'').foldl SetTheory.app
              (VSψ.getD i pt)]).foldl SetTheory.app (interp V ρ (Φ' (d.tgtsR J' i)))))
    -- the copy constructor at ψ's values: its head (`psiHead`), ψ⁻¹'s head
    -- at the copy (the container constructor at the pin's readings),
    -- ψ's values fit its telescope (`psiVals_fit_copy`), its index
    -- readings there are the container's at the fields (the record's
    -- `es` off the replaced positions)
    (hheadψ : interp V σ (head J)
      = (paramVals d.nP ρ).foldl SetTheory.app (interp V ρ (m.acval cA'.1.name ψ)))
    (hheadφ : interp V ρ (head' J') = DsAv.foldl SetTheory.app (interp V σ₀ (m.acval cA.1.name ψ')))
    (hfitCopy : SpineFit ρ ((d.dsF J' ψ).map (·.2.2)) (paramVals d.nP ρ ++ VSψ))
    (hEs : (d.esF J' ψ).map (interp V (consList (paramVals d.nP ρ ++ VSψ) ρ))
      = (dJ.esF J ψ').map (interp V (consList fs σ)))
    -- per position: ordinary on both sides; container-recursive and
    -- FINITARY (the copy's field recursive into the group-mate's copy,
    -- its readings the container's); or the REST (a transport, a
    -- reflexive position) with its round trip given
    (hpos : ∀ i, i < cA.2 →
      (¬ replaced (useIh J) (via J) i ∧ useIhA J' i = false) ∨
      (useIh J i = true ∧ via J i = none ∧ useIhA J' i = true ∧
        i ∈ ConLeche.recIdxOf (dJ.ksF J) ∧ i ∈ ConLeche.recIdxOf (d.ksR J') ∧
        (dJ.tssF J ψ').getD i [] = [] ∧ (d.tssR J' ψ).getD i [] = [] ∧
        d.tgtsR J' i = k₀ + base + dJ.tgts J i ∧
        ((d.eissR J' ψ).getD i []).map (interp V (consList (VSψ.take i) ρ))
          = ((dJ.eissF J ψ').getD i []).map (interp V (consList (fs.take i) σ))) ∨
      MIXED.getD i pt = fs.getD i pt) :
    R2Pred dJ ψ' ρ σ₀ σ Ψ Φ tup (dJ.inj ψ' J fs) := by
  intro t' ht' is' his' htup
  have hJlt : J < dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hlenFs : fs.length = ((dJ.Fss ψ').getD J []).length := hfit.length_eq
  have hfsN : fs.length = cA.2 := by
    rw [hlenFs, dJ.Fss_getD ψ' hJ, List.length_map, List.length_drop, hlenD]
    omega
  -- the terminator: the constructor's member and its readings
  obtain ⟨cvT', cvR', mI', rP', rules', hrep'⟩ := hrepT t' ht'
  rw [htup] at hall
  obtain ⟨hmem, hisE⟩ := hrep'.idxRecover ψ' σ hsat is' his' X J fs hJlt hlenFs hEsOk hEsFit hall
  subst hisE
  subst hmem
  -- the injection is the constructor's value
  obtain ⟨cvT, cvR, mI, rP, rules, hrep⟩ := hrepT _ hmemJ
  have hctor : dJ.inj ψ' J fs = (DsAv ++ fs).foldl SetTheory.app (interp V σ₀ (m.acval cA.1.name ψ')) :=
    (hrep.ctor J cA hJ ψ' σ₀ DsAv fs hDsFit (by rw [← hσ]; exact hfit)).symm
  -- the whole spine fits the constructor's telescope
  have hfitP : SpineFit σ₀ (((dJ.dsF J ψ').take dJ.nP).map (·.2.2)) DsAv :=
    spineFit_of_paramsIff hDsLen (by rw [List.length_map, List.length_take, hlenD]; omega) hDsFit hpIff
  have hfitAll : SpineFit σ₀ ((dJ.dsF J ψ').map (·.2.2)) (DsAv ++ fs) := by
    rw [← List.take_append_drop dJ.nP (dJ.dsF J ψ'), List.map_append]
    refine hfitP.append ?_
    rw [← hσ, ← dJ.Fss_getD ψ' hJ]
    exact hfit
  -- the mixed values are the fields
  have hVSlen : VSψ.length = fs.length := by rw [hVS, psiVals_length]
  have hMIXlen : MIXED.length = fs.length := by rw [hMIX, mixedVals_length, hVSlen]
  have hmixed : MIXED = fs := by
    refine list_ext_getD hMIXlen fun i hi => ?_
    have hiN : i < cA.2 := by rw [← hfsN, ← hMIXlen]; exact hi
    have hifs : i < fs.length := by rw [hfsN]; exact hiN
    have hiVS : i < VSψ.length := by rw [hVSlen]; exact hifs
    rcases hpos i hiN with ⟨hnr, huseA⟩ | ⟨huse, hvia, huseA, hrJ, hrA, htlJ, htlA, htgtA, hread⟩ | hrest
    · -- ordinary on both sides
      have hnu : useIh J i = false := by
        cases h : useIh J i
        · rfl
        · exact absurd (Or.inl h) hnr
      have hnv : via J i = none := by
        cases h : via J i with
        | none => rfl
        | some v => exact absurd (Or.inr (by rw [h]; rfl)) hnr
      rw [hMIX, mixedVals_getD _ _ _ _ hiVS, huseA, hVS, psiVals_getD _ _ _ _ _ _ _ hifs, hnv]
      simp only [hnu, Bool.false_eq_true, if_false]
    · -- container-recursive, finitary: the round trip inside
      have hrJR : i ∈ ConLeche.recIdxOf (dJ.ksR J) := by rw [hview.1]; exact hrJ
      have htlJR : (dJ.tssR J ψ').getD i [] = [] := by rw [hview.2.2.2]; exact htlJ
      have hVSi : VSψ.getD i pt
          = (((dJ.eissF J ψ').getD i []).map (interp V (consList (fs.take i) σ)) ++ [fs.getD i pt]).foldl
              SetTheory.app (interp V σ₀ (Ψ (dJ.tgts J i))) := by
        rw [hVS, psiVals_getD _ _ _ _ _ _ _ hifs, hvia]
        simp only [huse, if_true]
        rw [getD_map_idxOf hrJR, htlJR, hview.2.1, hview.2.2.1]
        simp only [lamTower, List.length_nil, Semantics.frameIdx, List.range_zero, List.map_nil,
          List.foldl_nil]
      have hMIXi : MIXED.getD i pt
          = (((dJ.eissF J ψ').getD i []).map (interp V (consList (fs.take i) σ)) ++ [VSψ.getD i pt]).foldl
              SetTheory.app (interp V ρ (Φ (dJ.tgts J i))) := by
        rw [hMIX, mixedVals_getD _ _ _ _ hiVS, huseA]
        simp only [if_true]
        rw [getD_map_idxOf hrA, htlA, htgtA, ← hΦ _ (htgts i), ← hread]
        simp only [lamTower, List.length_nil, Semantics.frameIdx, List.range_zero, List.map_nil,
          List.foldl_nil]
      rw [hMIXi, hVSi]
      have h := hIH i hrJ (dJ.tgts J i) (htgts i) _ (hEntryFit i hrJ) rfl
      unfold foldApp at h
      exact h
    · exact hrest
  -- assemble
  unfold foldApp
  rw [hctor, hιΨ fs hfitAll, hheadψ, ← List.foldl_append, ← hVS, hΦ _ hmemJ, ← hmemA, ← hEs,
    hιΦ VSψ hfitCopy, hheadφ, ← List.foldl_append, ← hMIX, hmixed]

end ConLeche.Model
