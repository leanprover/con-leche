module

public import ConLeche.Model.Inductives.InvFold
public import ConLeche.Model.Inductives.MutualRep
public import ConLeche.Verify.Inductives.NestedFacts
public section

/-!
# The copies' side of `ψ⁻¹` (task #279 M-B′ step 3c, continued)

`InvFold` closes the ψ⁻¹ instance under two hypotheses the COPIES owe:
`TargetOk` at a copy member (the container's leaf at the pin, graded
and in the elimination universe at every fitting index spine) and
`CtorAtPins` at a copy's constructor (the container constructor's
reading at the pin, in the aux datum's target-form vocabulary).  This
module discharges them from the CONTAINER's own representation — its
`IndRep` at the scratch environment, read at the level instantiation
the pin names — and from the semantic content of the run's facts,
packaged as three records:

* `PinRead` — the pin `J Ds`'s annotated components `DsA` at the aux
  block's parameter frame, graded there (what `pinsOkAux` says of the
  pin through the certified annotation: DESIGN §K.2/§M.17 finding 2);
* `CopyIdxRead` — the copy's index telescope is the container's at
  the pin (the copy's former is the container's type instantiated at
  the pin, `mkCopy`, read through `denoteMeta_instPisAt_peel`), and
  the copy's sort is the container's;
* `CopyCtorRead` — the copy's constructor is the container's at the
  pin, field by field: an aux-recursive field's target form is the
  container's field domain at the pin, an aux-ordinary field's domain
  IS the container's (the elimination rewrites a nested occurrence and
  nothing else, `replaceAllNested`).

The records are the SEMANTIC layer; deriving them from the run
relation is the syntactic layer (the next step), and is why they are
records rather than inlined hypotheses: every consumer below is stated
once, over the aux datum, and the syntactic layer only has to hit the
record.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Application spines, graded -/

/-- The arguments of a graded application spine are graded. -/
theorem WellDenotedV.mkAppN_args {ρ : Nat → V} :
    ∀ {args : List AnnotTerm} {f : AnnotTerm}, WellDenotedV V ρ (AnnotTerm.mkAppN f args) →
      WellDenotedV V ρ f ∧ ∀ a ∈ args, WellDenotedV V ρ a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: args, f, h => by
    rw [AnnotTerm.mkAppN_cons] at h
    obtain ⟨hfa, hall⟩ := WellDenotedV.mkAppN_args h
    exact ⟨WellDenotedV_app_fn hfa, fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact WellDenotedV_app_arg hfa
      · exact hall b hb⟩

namespace IndRepData

variable (d : IndRepData V)

/-! ## The records -/

/-- **The pin, read**: the container's leaf `L` at the pin's annotated
components `DsA` (readings at the aux block's parameter frame) is
graded at every frame satisfying the aux block's parameter context —
the semantic content of `pinsOkAux` for one pin (`nestedPinsOk` at the
scratch environment: the pin annotated at the parameter variables of
the stored former and type-checked there). -/
structure PinRead (ψ : Name → Nat) (L : AnnotTerm) (DsA : List AnnotTerm) (nPJ : Nat) : Prop where
  len : DsA.length = nPJ
  wd : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ → WellDenotedV V σ (AnnotTerm.mkAppN L DsA)

/-- **The copy's index telescope is the container's at the pin**, and
its sort is the container's — the copy's former is the container's
type at the level instantiation, instantiated at the pin (`mkCopy`),
so its reading below the aux block's parameters is the container's
index telescope at the pin's readings. -/
structure CopyIdxRead (ψ : Name → Nat) (t : Nat) (dJ : IndRepData V) (ψ' : Name → Nat) (mmJ : Nat)
    (DsA : List AnnotTerm) : Prop where
  sort : dJ.w ψ' = d.w ψ
  idxIff : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ → ∀ is : List V,
    SpineFit σ (d.IdsM t ψ) is ↔ SpineFit (consList (DsA.map (interp V σ)) σ) (dJ.IdsM mmJ ψ') is

/-! ## The pin fits the container's parameters -/

/-- **The pin's components fit the container's parameter telescope**:
the leaf is a λ-tower (`LeafShape`), so a graded application along
the components forces them into the tower's first binders
(`spineFit_of_wellDenoted_lams`). -/
theorem pinFit_of_leafShape {m : EnvModel V env} {ψ ψ' : Name → Nat} {L : AnnotTerm}
    {DsA : List AnnotTerm} {dJ : IndRepData V} {mmJ : Nat}
    (hL : L = m.acval (dJ.memberName mmJ) ψ')
    (hFFJ : dJ.FormerFacts m ψ' mmJ) (hLSJ : dJ.LeafShape m ψ' mmJ)
    (hpin : d.PinRead ψ L DsA dJ.nP) {σ : Nat → V} (hσ : Sat V (d.params ψ).reverse σ) :
    SpineFit σ (((dJ.ppsM mmJ ψ').take dJ.nP).map (·.2.2)) (DsA.map (interp V σ)) := by
  obtain ⟨hlen, -, -, -⟩ := hFFJ
  obtain ⟨B, hB⟩ := hLSJ
  have hfit := spineFit_of_wellDenoted_lams (u := dJ.w ψ' + 1) (Nat.succ_ne_zero _) (b := B)
    (args := DsA) (ds := dJ.ppsM mmJ ψ') (σ := σ) (ρ := σ) (f := L)
    (by rw [hpin.len, hlen]; exact Nat.le_add_right _ _) (hpin.wd σ hσ).1 (by rw [hL, hB])
  rw [hpin.len] at hfit
  exact hfit

/-! ## The copy's target -/

set_option maxHeartbeats 800000 in
/-- **A copy member's target fact, from the container's former at the
pin**: the copy's index telescope is graded as a real member of the
aux datum (`targetOk_real`'s first half — the copy IS a real member of
the scratch block); at every index spine fitting it, the container's
leaf at the pin's readings and the indices is graded (the container's
tower lifted to the index frame, `wellDenotedV_mkAppN_of_spineFit`)
and lies in the container's sort — the copy's, the elimination
universe — by the leaf in its tower (`mkPisAV_fold_mem` at the pin's
fit and the indices' fit through `CopyIdxRead`). -/
theorem targetOk_copy {μ : CheckMode} (mp : EnvModelM V μ env) {ψ : Name → Nat} {ρ : Nat → V}
    {ps : List AnnotTerm} (hps : ps.length = d.nP) {t : Nat} (ht : t < d.k)
    (hFF : d.FormerFacts mp.base2 ψ t)
    (hpIffM : ∀ ρ' : Nat → V, Sat V (d.params ψ).reverse ρ' ↔
      Sat V (((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse ρ')
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    (hlev : d.elimL.eval ψ = d.w ψ)
    -- the container, at the level instantiation the pin names
    {dJ : IndRepData V} {ψ' : Name → Nat} {mmJ : Nat}
    (hFFJ : dJ.FormerFacts mp.base2 ψ' mmJ) (hLSJ : dJ.LeafShape mp.base2 ψ' mmJ)
    -- the choice at `t`: the container's leaf at the pin
    {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
    (hL : L t = mp.base2.acval (dJ.memberName mmJ) ψ') {DsA : List AnnotTerm} (hpinsT : pinsT t = DsA)
    (hpin : d.PinRead ψ (L t) DsA dJ.nP) (hidx : d.CopyIdxRead ψ t dJ ψ' mmJ DsA) :
    d.TargetOk ψ ρ ps L pinsT t := by
  obtain ⟨hlen, hbits, -, hokF⟩ := hFF
  have hFFJ' := hFFJ
  obtain ⟨hlenJ, hbitsJ, hmemJ, hokJ⟩ := hFFJ'
  have hb : pwBit ψ ConLeche.PropWhen.never ≠ 0 := by rw [pwBit_never_eq]; exact Nat.one_ne_zero
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [hps]
  have hclosedJ : Term.bvarsBelow 0 (mp.base2.acval (dJ.memberName mmJ) ψ').erase :=
    mp.base2.cval_closedL _ ψ'
  have hfitP : SpineFit ρ (((d.ppsM t ψ).take d.nP).map (·.2.2)) (ps.map (interp V ρ)) :=
    spineFit_of_paramsIff hpsLen (by rw [List.length_map, List.length_take, hlen]; omega) hparams
      hpIffM
  have hsplitT : mkPisAV (d.ppsM t ψ) (.sort (d.w ψ))
      = mkPisAV ((d.ppsM t ψ).take d.nP) (mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.w ψ))) := by
    rw [← mkPisAV_append, List.take_append_drop]
  have hWD : WellDenotedV V (consList (ps.map (interp V ρ)) ρ)
      (mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.w ψ))) := by
    have h := hokF ρ
    rw [hsplitT] at h
    exact ⟨wellDenoted_mkPisAV_body h.1 _ hfitP, annotValid_mkPisAV_body h.2 _ hfitP⟩
  -- the parameter frame satisfies the aux block's parameter context
  have hσ : Sat V (d.params ψ).reverse (consList (ps.map (interp V ρ)) ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hparams
    simpa using this
  -- the pin's components fit the container's parameters
  have hfitDs := d.pinFit_of_leafShape hL hFFJ hLSJ hpin hσ
  have hsplitJ : (dJ.ppsM mmJ ψ').map (·.2.2)
      = ((dJ.ppsM mmJ ψ').take dJ.nP).map (·.2.2) ++ ((dJ.ppsM mmJ ψ').drop dJ.nP).map (·.2.2) := by
    rw [← List.map_append, List.take_append_drop]
  refine ⟨?_, ?_⟩
  · rw [d.ipss_getD ψ ht, hlev]
    exact ⟨wellDenoted_mkPisAV_rebit _ hWD.1, annotValid_mkPisAV_rebit_sort hb hWD.2⟩
  · intro is hsp
    rw [d.ipss_getD ψ ht, rebit_map_dom] at hsp
    have hisLen : is.length = d.nIdxAt t := by
      rw [hsp.length_eq, List.length_map, List.length_drop, hlen]; omega
    have hnI : d.nIdxs.getD t 0 = d.nIdxAt t := rfl
    -- the indices fit the container's index telescope at the pin
    have hspJ : SpineFit
        (consList (DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)))
          (consList (ps.map (interp V ρ)) ρ))
        (dJ.IdsM mmJ ψ') is :=
      (hidx.idxIff _ hσ is).mp hsp
    have hfitAll : SpineFit (consList (ps.map (interp V ρ)) ρ) ((dJ.ppsM mmJ ψ').map (·.2.2))
        (DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)) ++ is) := by
      rw [hsplitJ]; exact SpineFit.append hfitDs hspJ
    have hshift : shiftE (d.nIdxAt t) 0 (consList is (consList (ps.map (interp V ρ)) ρ))
        = consList (ps.map (interp V ρ)) ρ := by
      rw [← hisLen]; exact shiftE_consList _ _
    have hDsLen : DsA.length = dJ.nP := hpin.len
    -- the family's reading: the leaf at the pin's values and the indices
    have hfam : interp V (consList is (consList (ps.map (interp V ρ)) ρ))
          (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0))
        = (DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)) ++ is).foldl SetTheory.app
            (interp V (consList (ps.map (interp V ρ)) ρ) (L t)) := by
      have h := interp_famAppAV_at (V := V) (L := L t)
        (fun σ₁ σ₂ => by rw [hL]; exact interp_closed (V := V) hclosedJ _ _)
        (pinsT t) d.nP (extra := []) (is := is) (σ := consList (ps.map (interp V ρ)) ρ)
      rw [hpinsT] at h ⊢
      rw [hnI, ← hisLen]
      simpa using h
    refine ⟨?_, ?_⟩
    · -- graded: the container's tower lifted to the index frame,
      -- applied along the pin's lifted components and the index variables
      have hT : WellDenotedV V (consList is (consList (ps.map (interp V ρ)) ρ))
          (mkPisAV (liftDoms (d.nIdxAt t) 0 (dJ.ppsM mmJ ψ'))
            ((AnnotTerm.sort (dJ.w ψ')).liftN (d.nIdxAt t) (0 + (dJ.ppsM mmJ ψ').length))) := by
        rw [← liftN_mkPisAV, WellDenotedV_liftN, hshift]
        exact hokJ _
      have hmem : interp V (consList is (consList (ps.map (interp V ρ)) ρ)) (L t)
          ∈ˢ interp V (consList is (consList (ps.map (interp V ρ)) ρ))
            (mkPisAV (liftDoms (d.nIdxAt t) 0 (dJ.ppsM mmJ ψ'))
              ((AnnotTerm.sort (dJ.w ψ')).liftN (d.nIdxAt t) (0 + (dJ.ppsM mmJ ψ').length))) := by
        rw [← liftN_mkPisAV, interp_liftN, hshift, hL,
          interp_closed (V := V) hclosedJ _ (consList (ps.map (interp V ρ)) ρ)]
        exact hmemJ _
      have hargs : ∀ a ∈ (pinsT t).map (·.liftN (d.nIdxAt t) 0) ++ fieldBvars (d.nIdxAt t),
          WellDenotedV V (consList is (consList (ps.map (interp V ρ)) ρ)) a := by
        intro a ha
        rcases List.mem_append.mp ha with h | h
        · obtain ⟨D, hD, rfl⟩ := List.mem_map.mp h
          rw [WellDenotedV_liftN, hshift]
          rw [hpinsT] at hD
          exact (WellDenotedV.mkAppN_args (hpin.wd _ hσ)).2 D hD
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp h
          exact ⟨by simp, by simp⟩
      have hfit : SpineFit (consList is (consList (ps.map (interp V ρ)) ρ))
          ((liftDoms (d.nIdxAt t) 0 (dJ.ppsM mmJ ψ')).map (·.2.2))
          (((pinsT t).map (·.liftN (d.nIdxAt t) 0) ++ fieldBvars (d.nIdxAt t)).map
            (interp V (consList is (consList (ps.map (interp V ρ)) ρ)))) := by
        rw [spineFit_liftDoms, hshift, List.map_append, List.map_map, hpinsT,
          show fieldBvars (d.nIdxAt t)
            = (List.range (d.nIdxAt t)).map (fun k => AnnotTerm.bvar (d.nIdxAt t - 1 - k)) from rfl,
          map_fieldBvars_interp hisLen]
        have hmapDs : DsA.map (interp V (consList is (consList (ps.map (interp V ρ)) ρ)) ∘
            (·.liftN (d.nIdxAt t) 0)) = DsA.map (interp V (consList (ps.map (interp V ρ)) ρ)) := by
          apply List.map_congr_left
          intro D _
          simp only [Function.comp_def]
          rw [interp_liftN, hshift]
        rw [hmapDs]
        exact hfitAll
      have hfam' : famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)
          = AnnotTerm.mkAppN (L t) ((pinsT t).map (·.liftN (d.nIdxAt t) 0) ++ fieldBvars (d.nIdxAt t)) := by
        unfold famAppAV
        rw [hnI, Nat.add_sub_cancel_left]
      rw [hfam']
      exact (wellDenotedV_mkAppN_of_spineFit hT
        (by rw [hL]; exact ⟨mp.base2.acval_wellDenoted _ ψ' _, mp.acval_validV _ ψ' _⟩)
        hargs hmem hfit).1
    · rw [hfam, hlev, ← hidx.sort]
      have := mkPisAV_fold_mem (m := 1)
        (fun dd hd => ⟨fun h => absurd h Nat.one_ne_zero, fun h => absurd h (hbitsJ dd hd)⟩)
        (fun h => absurd h Nat.one_ne_zero) (hmemJ (consList (ps.map (interp V ρ)) ρ)) hfitAll
      rw [interp_sort] at this
      rw [hL]
      exact this

end IndRepData

/-! ## Spines against pointwise-equal telescopes -/

/-- **`SpineFit` is pointwise**: two telescopes of the same length whose
entries read alike under every prefix fitting the target telescope
accept the same spines. -/
theorem spineFit_congr_pointwise :
    ∀ {Ds Ds' : List AnnotTerm} {vs : List V} {σ : Nat → V}, Ds.length = Ds'.length →
      (∀ i, i < Ds'.length → ∀ ws : List V, ws.length = i → SpineFit σ (Ds'.take i) ws →
        interp V (consList ws σ) (Ds.getD i default) = interp V (consList ws σ) (Ds'.getD i default)) →
      SpineFit σ Ds vs → SpineFit σ Ds' vs
  | [], [], [], _, _, _, _ => trivial
  | [], [], _ :: _, _, _, _, h => h.elim
  | [], _ :: _, _, _, hlen, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _ => by simp at hlen
  | _ :: _, _ :: _, [], _, _, _, h => h.elim
  | D :: Ds, D' :: Ds', v :: vs, σ, hlen, h, hfit => by
    obtain ⟨hv, hrest⟩ := hfit
    have h0 := h 0 (by simp) [] rfl trivial
    simp only [List.getD_cons_zero] at h0
    have hv' : v ∈ˢ interp V σ D' := by
      have : consList ([] : List V) σ = σ := rfl
      rw [this] at h0
      rw [← h0]; exact hv
    refine ⟨hv', ?_⟩
    refine spineFit_congr_pointwise (σ := cons v σ) (by simpa using hlen) ?_ hrest
    intro i hi ws hws hws'
    have := h (i + 1) (by simp; omega) (v :: ws) (by simp [hws]) ⟨hv', hws'⟩
    simpa [List.getD_cons_succ] using this

namespace IndRepData

variable (d : IndRepData V)

/-! ## The copy's constructor -/

/-- **The copy's constructor, read through the container's at the
pin**: at the aux block's parameter frame, `head` (the container's
constructor at the pin's readings) inhabits a graded tower `mkPisAV
dsC bodyC` over `nF` binders (the container constructor's residual
tower instantiated at the pin — the reading of `instPis` through
`denoteMeta_instPisAt_peel`); each binder reads as the copy
constructor's field in TARGET form under every fitting prefix (an
aux-recursive field's target form is the container's field domain at
the pin, by the elimination ledger; an aux-ordinary field's domain IS
the container's, since `replaceAllNested` rewrites nested occurrences
and nothing else); and the body at fitting fields is the copy's
target at the constructor's index readings (the container
constructor's result `J Ds ı⃗` read as the copy's target at ı⃗, the
`invTgAV` β).  The syntactic layer derives this from the run; the
semantic layer consumes it. -/
structure CopyCtorRead (ψ : Name → Nat) (ρ : Nat → V) (ps : List AnnotTerm) (L : Nat → AnnotTerm)
    (pinsT : Nat → List AnnotTerm) (useIh : Nat → Bool) (Ja : Nat) (head : AnnotTerm) (nF : Nat)
    (dsC : List (Nat × Nat × AnnotTerm)) (bodyC : AnnotTerm) : Prop where
  len : dsC.length = nF
  towerWD : WellDenotedV V (consList (ps.map (interp V ρ)) ρ) (mkPisAV dsC bodyC)
  headWD : WellDenotedV V (consList (ps.map (interp V ρ)) ρ) head
  headMem : interp V (consList (ps.map (interp V ρ)) ρ) head
    ∈ˢ interp V (consList (ps.map (interp V ρ)) ρ) (mkPisAV dsC bodyC)
  fields : ∀ i, i < nF → ∀ ws : List V, ws.length = i →
    SpineFit (consList (ps.map (interp V ρ)) ρ) ((dsC.take i).map (·.2.2)) ws →
    interp V (consList ws (consList (ps.map (interp V ρ)) ρ))
        (tgFieldAV (d.invTgAV ψ ps L pinsT) useIh d.nP (d.bb ψ) (d.tgtsR Ja) (d.dsF Ja ψ)
          (d.eissR Ja ψ) (d.tssR Ja ψ) i)
      = interp V (consList ws (consList (ps.map (interp V ρ)) ρ)) (dsC.getD i default).2.2
  body : ∀ vs : List V, SpineFit (consList (ps.map (interp V ρ)) ρ) (dsC.map (·.2.2)) vs →
    interp V (consList vs (consList (ps.map (interp V ρ)) ρ)) bodyC
      = ((d.esF Ja ψ).map (interp V (consList vs (consList (ps.map (interp V ρ)) ρ)))).foldl
          SetTheory.app (interp V ρ (d.invTgAV ψ ps L pinsT (d.mems Ja)))

/-- **A copy's constructor at the pins**: `CtorAtPins` from
`CopyCtorRead` — the tower is the record's, and a spine fitting the
target-form field domains fits it by the pointwise reading
(`spineFit_congr_pointwise`). -/
theorem ctorAtPins_copy {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm}
    {pinsT : Nat → List AnnotTerm} {useIh : Nat → Bool} {Ja : Nat} {head : AnnotTerm} {nF : Nat}
    {dsC : List (Nat × Nat × AnnotTerm)} {bodyC : AnnotTerm}
    (h : d.CopyCtorRead ψ ρ ps L pinsT useIh Ja head nF dsC bodyC) :
    d.CtorAtPins ψ ρ ps (d.invTgAV ψ ps L pinsT) useIh Ja head nF (d.dsF Ja ψ) (d.esF Ja ψ)
      (d.eissR Ja ψ) (d.tssR Ja ψ) := by
  refine ⟨dsC, bodyC, h.len, h.towerWD, h.headWD, h.headMem, fun vs hvs => ?_⟩
  have hfit : SpineFit (consList (ps.map (interp V ρ)) ρ) (dsC.map (·.2.2)) vs := by
    refine spineFit_congr_pointwise (by simp [tgFieldsAV, h.len]) ?_ hvs
    intro i hi ws hws hws'
    have hi' : i < nF := by simpa [h.len] using hi
    rw [← List.map_take] at hws'
    have := h.fields i hi' ws hws hws'
    have hidx : i < dsC.length := by rw [h.len]; exact hi'
    have hR : (dsC.map (·.2.2)).getD i default = (dsC.getD i default).2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hidx,
        Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hidx, Option.getD_some]
    have hL : (tgFieldsAV (d.invTgAV ψ ps L pinsT) useIh d.nP (d.bb ψ) (d.tgtsR Ja) (d.dsF Ja ψ)
          (d.eissR Ja ψ) (d.tssR Ja ψ) nF).getD i default
        = tgFieldAV (d.invTgAV ψ ps L pinsT) useIh d.nP (d.bb ψ) (d.tgtsR Ja) (d.dsF Ja ψ)
          (d.eissR Ja ψ) (d.tssR Ja ψ) i := by
      rw [tgFieldsAV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi',
        Option.map_some, Option.getD_some]
    rw [hL, hR]
    exact this
  exact ⟨hfit, h.body vs hfit⟩

end IndRepData

/-! ## The choice, member by member

`TargetOk` and (at a constructor whose fields all use their own
domains) `CtorAtPins` read the choice POINTWISE — at the member's own
target alone — so the identity discharges of `InvFold`
(`targetOk_real`, `ctorAtPins_real`) apply verbatim at a real member
of a block whose OTHER members are pinned elsewhere.
-/

/-- The target-form field domains do not mention the choice when no
field uses its hypothesis. -/
theorem tgFieldsAV_congr_noIh {Tg Tg' : Nat → AnnotTerm} {useIh : Nat → Bool}
    (hu : ∀ i, useIh i = false) (nP b : Nat) (tgt : Nat → Nat)
    (ds : List (Nat × Nat × AnnotTerm)) (Eiss : List (List AnnotTerm))
    (tls : List (List (Nat × Nat × AnnotTerm))) (nF : Nat) :
    tgFieldsAV Tg useIh nP b tgt ds Eiss tls nF = tgFieldsAV Tg' useIh nP b tgt ds Eiss tls nF := by
  refine List.map_congr_left fun i _ => ?_
  unfold tgFieldAV
  rw [hu i]
  rfl

namespace IndRepData

variable (d : IndRepData V)

/-- **`TargetOk` is pointwise in the choice**: member `t`'s fact
mentions `L t` and `pinsT t` and nothing else. -/
theorem TargetOk.congr {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm}
    {L L' : Nat → AnnotTerm} {pinsT pinsT' : Nat → List AnnotTerm} {t : Nat}
    (hL : L t = L' t) (hp : pinsT t = pinsT' t) (h : d.TargetOk ψ ρ ps L pinsT t) :
    d.TargetOk ψ ρ ps L' pinsT' t := by
  unfold IndRepData.TargetOk at h ⊢
  rw [← hL, ← hp]
  exact h

omit [SetTheory V] in
/-- **A member's target is pointwise in the choice**. -/
theorem invTgAV_congr {ψ : Name → Nat} {ps : List AnnotTerm} {L L' : Nat → AnnotTerm}
    {pinsT pinsT' : Nat → List AnnotTerm} {t : Nat} (hL : L t = L' t) (hp : pinsT t = pinsT' t) :
    d.invTgAV ψ ps L pinsT t = d.invTgAV ψ ps L' pinsT' t := by
  unfold IndRepData.invTgAV
  rw [hL, hp]

/-- **`CtorAtPins` is pointwise in the choice at a constructor that
uses no hypothesis**: the field domains are the constructor's own
(`tgFieldsAV_congr_noIh`) and the body's target is the constructor's
OWN member's. -/
theorem CtorAtPins.congr_tg {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm}
    {Tg Tg' : Nat → AnnotTerm} {useIh : Nat → Bool} {J : Nat} {head : AnnotTerm} {nF : Nat}
    {ds : List (Nat × Nat × AnnotTerm)} {Es : List AnnotTerm} {Eiss : List (List AnnotTerm)}
    {tls : List (List (Nat × Nat × AnnotTerm))} (hu : ∀ i, useIh i = false)
    (hTg : Tg (d.mems J) = Tg' (d.mems J))
    (h : d.CtorAtPins ψ ρ ps Tg useIh J head nF ds Es Eiss tls) :
    d.CtorAtPins ψ ρ ps Tg' useIh J head nF ds Es Eiss tls := by
  obtain ⟨dsC, bodyC, hlen, htw, hhd, hmem, hall⟩ := h
  refine ⟨dsC, bodyC, hlen, htw, hhd, hmem, fun vs hvs => ?_⟩
  rw [← hTg]
  refine hall vs ?_
  rwa [tgFieldsAV_congr_noIh hu d.nP (d.bb ψ) (d.tgtsR J) ds Eiss tls nF (Tg := Tg) (Tg' := Tg')]

end IndRepData

/-! ## The pin, read off the check (the syntactic layer)

`pinsOkAux` (DESIGN §K.2) annotates each pin at the aux block's
parameter depth in the SCRATCH environment and infers a type for it.
What the model needs of it — the pin's components read at the
parameter frame, graded there (`PinRead`) — is that run through
`acceptedReads_of` and `ClaimsAt.inferRow`, at the parameter context
the block's first member's former opens (`Opened`).

**The pin's scope** (DESIGN §M.20's kernel request, landed as K.3
`pinsClosed`): `acceptedReads_of` and `Opened.ctx` need the annotated
pin to be `WScoped nP` HEREDITARILY, `looseBVarsBounded 0`, and to have
its fvar leaves among the openers.  `annotateBody` certifies only that
each `.fvar` its traversal REACHES has index `< depth` — it does not
descend into an fvar's type annotation, it does not compare the
annotation with the opener's, and it passes a `.bvar` through
unchecked — and the pin's components appear in NO other checked term.
The run records instead that the pin ABSTRACTED over the parameters is
fvar-free with its loose bvars inside the telescope (`pinsClosed`), and
`instantiateList_openers_scoped` (`Verify/Inductives/NestedFacts.lean`)
turns that into the three facts at the openers.
-/

namespace IndRepData

variable (d : IndRepData V)

/-- **The block's parameter context, opened**: the first member's
former opened at the block's parameter count yields exactly the
datum's parameter telescope (`PiTeleAV.unique` against the reading's
own peel). -/
theorem opened_params {μ : CheckMode} {mp : EnvModelM V μ env} (ψ : Name → Nat)
    {cvT : ConstantVal} {caps : IndCaps}
    (hf : env.find? (d.memberName 0) = some (.indInfo cvT caps))
    (hFD : FormerData mp.base2 cvT (d.nP + d.nIdxAt 0) d.resSort (d.ppsM 0) (d.lvlsM 0))
    {fvsA : List ConLeche.Expr} {oA : ConLeche.Expr}
    (hop : ConLeche.openPisAtFvars d.nP cvT.type 0 = some (fvsA, oA)) :
    ∃ R : AnnotTerm, Opened mp.base2 ψ d.nP cvT.type fvsA oA (d.params ψ).reverse R := by
  have hwf := mp.base2.wf _ (Env.find?_mem hf)
  obtain ⟨Γ, R, htele, hopened⟩ :=
    opened_of (V := V) hop hwf.1 hwf.2.2.2.1 (hFD.read ψ) (fun ρ => hFD.okTy ψ ρ)
  have hle : d.nP ≤ (d.ppsM 0 ψ).length := by rw [hFD.len ψ]; omega
  have htele' : PiTeleAV d.nP (mkPisAV (d.ppsM 0 ψ) (.sort (d.resSort.eval ψ)))
      ((((d.ppsM 0 ψ).take d.nP).map (·.2.2)).reverse)
      (mkPisAV ((d.ppsM 0 ψ).drop d.nP) (.sort (d.resSort.eval ψ))) :=
    piTeleAV_of_stripPisAV (stripPisAV_mkPisAV_take d.nP (d.ppsM 0 ψ) _ hle)
  obtain ⟨rfl, -⟩ := PiTeleAV.unique htele htele'
  exact ⟨R, hopened⟩

/-- **The pin, read** (the syntactic layer): from the pin's check at the
scratch environment — the annotation and the inference of
`nestedPinsOk` — and the pin's syntactic guards (see the section
docstring), the container's leaf at the pin's annotated components is
graded at every frame satisfying the block's parameter context, and
there is one component per pin argument. -/
theorem pinRead_of {μ : CheckMode} (hμ : μ.verifiedChecks = true) {mp : EnvModelM V μ env}
    {F : Nat} {ψ : Name → Nat}
    {cvT : ConstantVal} {fvsA : List ConLeche.Expr} {oA : ConLeche.Expr} {R : AnnotTerm}
    (hopened : Opened mp.base2 ψ d.nP cvT.type fvsA oA (d.params ψ).reverse R)
    {Jn : Name} {lvls : List ConLeche.Level} {Ds : List ConLeche.Expr} {ci : ConstantInfo}
    (hfJ : env.find? Jn = some ci)
    (hlvls : lvls.length = ci.toConstantVal.levelParams.length)
    {pinA e ty : ConLeche.Expr}
    (hpinA : pinA = Expr.instantiateList
      (Expr.abstractRange (Expr.mkAppN (.const Jn lvls) Ds) 0 d.nP 0) fvsA.reverse)
    (hann : ConLeche.annotateCore μ env F d.nP pinA = .ok e)
    (hinf : ConLeche.inferTypeCore μ env F d.nP e = .ok ty)
    -- the pin's scope (`pinsClosed`, K.3): abstracted over the parameters
    -- it is fvar-free with its loose bvars inside the telescope
    (hclosed : (Expr.abstractRange (Expr.mkAppN (.const Jn lvls) Ds) 0 d.nP 0).hasFvar = false ∧
      (Expr.abstractRange (Expr.mkAppN (.const Jn lvls) Ds) 0 d.nP 0).looseBVarsBounded d.nP
        = true)
    (hlenF : fvsA.length = d.nP) :
    ∃ (argsA : List ConLeche.Expr) (DsA : List AnnotTerm),
      ConLeche.annotateCore μ env F d.nP pinA = .ok (Expr.mkAppN (.const Jn lvls) argsA) ∧
      argsA.length = Ds.length ∧
      (∀ a ∈ argsA, Expr.WScoped d.nP a ∧ a.looseBVarsBounded 0 = true) ∧
      DenoteMetaSpine mp.base2.acval env ψ d.nP argsA DsA ∧
      DsA.length = Ds.length ∧
      d.PinRead ψ (mp.base2.acval Jn
        (ConLeche.Level.substFn ψ ci.toConstantVal.levelParams lvls)) DsA Ds.length := by
  -- the pin's three syntactic guards, from its scope at the openers
  obtain ⟨hws, hb, hleaf⟩ : Expr.WScoped d.nP pinA ∧ pinA.looseBVarsBounded 0 = true ∧
      ∀ l ∈ pinA.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsA := by
    rw [hpinA]
    exact ConLeche.instantiateList_openers_scoped hlenF hclosed.1 hclosed.2 fun i x hx =>
      let h := hopened.var i x hx
      ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩
  -- the annotated pin is a spine at the same constant
  have hconst : Expr.instantiateList ((Expr.const Jn lvls).abstractRange 0 d.nP 0) fvsA.reverse
      = .const Jn lvls := by
    rw [show (Expr.const Jn lvls).abstractRange 0 d.nP 0 = .const Jn lvls from rfl,
      Expr.instantiateList]
  have hspine : pinA = Expr.mkAppN (.const Jn lvls)
      (Ds.map fun D => Expr.instantiateList (D.abstractRange 0 d.nP 0) fvsA.reverse) := by
    rw [hpinA, ConLeche.abstractRange_mkAppN, ConLeche.instantiateList_mkAppN, List.map_map,
      hconst]
    rfl
  rw [hspine] at hann hws hb hleaf
  obtain ⟨f', args', hlenA, rfl, F', hf'⟩ := ConLeche.annotateCore_mkAppN_inv hann
  obtain rfl := ConLeche.annotateCore_const_inv hf'
  -- the annotated pin's guards, and its reading
  have hwsE : Expr.WScoped d.nP (Expr.mkAppN (.const Jn lvls) args') :=
    ConLeche.annotateCore_WScoped F _ hann hws
  have hbE : (Expr.mkAppN (.const Jn lvls) args').looseBVarsBounded 0 = true :=
    ConLeche.annotateCore_looseBVars F _ hann hb
  have hleafE : ∀ l ∈ (Expr.mkAppN (.const Jn lvls) args').fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsA := by
    intro l hl
    exact hleaf l (ConLeche.annotateCore_leaves_sub F _ hann hws hb l hl)
  have hLE : Expr.LeavesBounded (Expr.mkAppN (.const Jn lvls) args') := by
    intro l hl
    exact (hopened.var _ _ (List.getElem?_of_mem (hleafE l hl)).choose_spec).2.2.1
  obtain ⟨eA, heA⟩ := acceptedReads_of (V := V) mp.base2 ψ hinf hwsE hbE hLE
  -- the reading is the leaf at the components' readings
  obtain ⟨fa, DsA, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv heA
  have hlenD : DsA.length = args'.length := (DenoteMetaSpine.length hsp).symm
  rw [denoteMeta_const hfJ hlvls] at hfa
  obtain rfl := Option.some.inj hfa
  -- graded at the parameter frame
  have hC : CtxOk mp.base2 ψ d.nP (d.params ψ).reverse (Expr.mkAppN (.const Jn lvls) args') := by
    have h := hopened.ctx (Nat.le_refl d.nP) hwsE hleafE
    rwa [Nat.sub_self, List.drop_zero] at h
  obtain ⟨-, -, hok, -, -⟩ := (claimsAt_of hμ mp ψ F).inferRow hinf hwsE hbE hLE hC heA
  have hargsA : ∀ a ∈ args', Expr.WScoped d.nP a ∧ a.looseBVarsBounded 0 = true := fun a ha =>
    ⟨(ConLeche.WScoped_mkAppN_args hwsE).2 a ha, (ConLeche.looseBVarsBounded_mkAppN_args hbE).2 a ha⟩
  exact ⟨args', DsA, by rw [hspine]; exact hann, by rw [hlenA, List.length_map], hargsA, hsp,
    by rw [hlenD, hlenA, List.length_map], ⟨by rw [hlenD, hlenA, List.length_map], hok⟩⟩

end IndRepData

/-! ## The scratch block's `InvSetup`

The block's representations (`MutualBlockReps`, the widened conclusion
of `declMutualCore`) supply every datum-side field of the ψ⁻¹ setup:
ONE member with constructors carries, through `rulesRead`, the whole
family's `RecReadAt`, and its `formersRead`/`leafShape`/`ctors`/
`paramsIff` clauses are already quantified over the block.  The datum
the setup is stated at is the block's datum re-sorted to that member's
own spelling of the sort (`MutualBlockReps`' existential; every field
the fold reads is unchanged by the re-sorting, so the consumer's
hypotheses are stated at `d` itself).
-/

namespace IndRepData

variable (d : IndRepData V)

/-- **The block's formers, as the fold reads them**: length, bits, the
tower graded (`FormerData`) and the leaf in it (`mem_type`). -/
theorem formerFacts_of_indRep {μ : CheckMode} {mp : EnvModelM V μ env} {T : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {t₀ : Nat}
    (hrep : IndRep mp.base2 T cvT cvR mI rP rules d t₀) (hkR : d.kReal = d.k)
    (ψ : Name → Nat) {t : Nat} (ht : t < d.k) : d.FormerFacts mp.base2 ψ t := by
  obtain ⟨cv, capsT, hf⟩ := hrep.membersFound t ht
  have hFD := hrep.formersRead t (by rw [hkR]; exact ht) cv capsT hf
  refine ⟨hFD.len ψ, fun dd hd => hFD.bits ψ dd hd, fun ρ => ?_, fun ρ => hFD.okTy ψ ρ⟩
  have hname : cv.name = d.memberName t := Env.find?_name hf
  have h := mp.mem_type _ (Env.find?_mem hf) ψ _ (hFD.read ψ) ρ
  rw [show (ConstantInfo.indInfo cv capsT).name = cv.name from rfl, hname] at h
  exact h

/-- **The ψ⁻¹ setup from ONE member's representation**: a member whose
recursor is stored with rules carries, through `rulesRead`, every
member's `RecReadAt`, and its `formersRead`/`leafShape`/`ctors`/
`paramsIff` clauses are already quantified over the block; the rest of
`InvSetup`'s datum-side fields are the block's shape conjuncts.  The
premise is the one the datum's `rulesRead` carries: this member's
recursor has rules. -/
theorem invSetup_of_member {μ : CheckMode} {mp : EnvModelM V μ env}
    (hctorsC : d.ctorsC = []) (hkR : d.kReal = d.k)
    (hpinsAV : ∀ (t : Nat) (ψ : Name → Nat), d.pinsAV t ψ = paramBvarsAt d.nP d.nP)
    (hview : ∀ J, d.ksR J = d.ksF J ∧ d.tgtsR J = d.tgts J ∧ d.eissR J = d.eissF J ∧
      d.tssR J = d.tssF J)
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {t₀ : Nat}
    (ht₀ : t₀ < d.k) (hrules : rules ≠ [])
    (hfR : env.find? cvR.name = some (.recInfo cvR mI rP rules))
    (hrep : IndRep mp.base2 T cvT cvR mI rP rules d t₀)
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm}
    {pinsT : Nat → List AnnotTerm} {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool}
    (hps : ps.length = d.nP) (hpsWD : ∀ p ∈ ps, WellDenotedV V ρ p)
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    (hTg : ∀ t, t < d.k → d.TargetOk ψ ρ ps L pinsT t)
    (hCAP : ∀ J cA, d.ctorsA[J]? = some cA →
      d.CtorAtPins ψ ρ ps (d.invTgAV ψ ps L pinsT) (useIh J) J (head J) cA.2 (d.dsF J ψ)
        (d.esF J ψ) (d.eissR J ψ) (d.tssR J ψ))
    (huse : ∀ J i, useIh J i = true → i ∈ ConLeche.recIdxOf (d.ksR J)) :
    d.InvSetup mp cvT.levelParams cvT.levelParams ψ ρ ps L pinsT head useIh := by
  have hk : 0 < d.k := Nat.lt_of_le_of_lt (Nat.zero_le _) ht₀
  have hFF : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t :=
    fun t ht => d.formerFacts_of_indRep hrep hkR ψ ht
  have hnAll : d.nAll = d.ctorsA.length := by
    show d.ctorsA.length + d.ctorsC.length = _
    rw [hctorsC]
    rfl
  refine
    { hR := fun t ht => hrep.rulesRead hrules hfR t ht, hps := hps, hpsWD := hpsWD,
      hparams := hparams, hpps := ?_, hipsLen := ?_, hk := hk, hctorsC := hctorsC,
      hpins := fun t => hpinsAV t ψ, hview := hview,
      hLS := fun t ht => hrep.leafShape t (by rw [hkR]; exact ht) ψ, hFF := hFF,
      hctors := fun J cA hJ => hrep.ctors J cA hJ, hpIff := fun J cA hJ => hrep.paramsIff J cA hJ ψ,
      hmems := ?_, htgts := ?_, hTg := hTg, hCAP := hCAP, huse := huse }
  · rw [List.length_take, (hFF 0 hk).1]
    omega
  · intro t ht
    have hg : (d.ipss ψ).getD t [] = (d.ppsM t ψ).drop d.nP := by
      show ((List.range d.k).map (fun t => (d.ppsM t ψ).drop d.nP)).getD t [] = _
      exact getD_range_map _ _ _ ht _
    rw [hg, List.length_drop, (hFF t ht).1]
    show d.nP + d.nIdxAt t - d.nP = d.nIdxAt t
    omega
  · intro J hJ
    have h := (hrep.memsReal J (by rw [hnAll]; exact hJ)).mpr hJ
    rw [hkR] at h
    exact h
  · intro J i
    have h := hrep.tgtsRLt J i
    rw [show d.tgtsR J = d.tgts J from (hview J).2.1] at h
    exact h

/-! ### The real members' half of the choice

A member of the scratch block that is NOT a copy keeps its own leaf at
the parameter variables (ψ⁻¹ is the identity there), so its target and
its constructors' facts are `InvFold`'s identity discharges read
through the pointwise congruences. -/

/-- **A real member's target at the mixed choice** (`targetOk_real`
through `TargetOk.congr`). -/
theorem targetOk_choice_real {μ : CheckMode} {mp : EnvModelM V μ env} {T : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {t₀ : Nat}
    (hrep : IndRep mp.base2 T cvT cvR mI rP rules d t₀) (hkR : d.kReal = d.k)
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} (hps : ps.length = d.nP)
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    (hlev : d.elimL.eval ψ = d.w ψ) {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
    {t : Nat} (ht : t < d.k) (hL : L t = mp.base2.acval (d.memberName t) ψ)
    (hp : pinsT t = paramBvarsAt d.nP d.nP) : d.TargetOk ψ ρ ps L pinsT t :=
  IndRepData.TargetOk.congr d hL.symm hp.symm
    (d.targetOk_real mp hps ht (d.formerFacts_of_indRep hrep hkR ψ ht)
      (hrep.paramsIffM t (by rw [hkR]; exact ht) ψ) hparams hlev)

/-- **A real constructor's `CtorAtPins` at the mixed choice**: its
minor uses the FIELDS (no hypothesis), so the target-form domains are
its own and the only target it mentions is its own member's
(`ctorAtPins_real` through `CtorAtPins.congr_tg`). -/
theorem ctorAtPins_choice_real {μ : CheckMode} {mp : EnvModelM V μ env} {T : Name}
    {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {t₀ : Nat}
    (hrep : IndRep mp.base2 T cvT cvR mI rP rules d t₀) (hkR : d.kReal = d.k)
    (hctorsC : d.ctorsC = [])
    (hpinsAV : ∀ (t : Nat) (ψ : Name → Nat), d.pinsAV t ψ = paramBvarsAt d.nP d.nP)
    (hview : ∀ J, d.ksR J = d.ksF J ∧ d.tgtsR J = d.tgts J ∧ d.eissR J = d.eissF J ∧
      d.tssR J = d.tssF J)
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} (hps : ps.length = d.nP)
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm} {head : Nat → AnnotTerm}
    {useIh : Nat → Nat → Bool} {J : Nat} {cA : ConstantVal × Nat}
    (hJ : d.ctorsA[J]? = some cA)
    (hhead : head J = AnnotTerm.mkAppN (mp.base2.acval cA.1.name ψ) (paramBvarsAt d.nP d.nP))
    (hu : ∀ i, useIh J i = false)
    (hL : L (d.mems J) = mp.base2.acval (d.memberName (d.mems J)) ψ)
    (hp : pinsT (d.mems J) = paramBvarsAt d.nP d.nP) :
    d.CtorAtPins ψ ρ ps (d.invTgAV ψ ps L pinsT) (useIh J) J (head J) cA.2 (d.dsF J ψ)
      (d.esF J ψ) (d.eissR J ψ) (d.tssR J ψ) := by
  have hJA : J < d.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hnAll : d.nAll = d.ctorsA.length := by
    show d.ctorsA.length + d.ctorsC.length = _
    rw [hctorsC]
    rfl
  have hmemJ : d.mems J < d.k := by
    have h := (hrep.memsReal J (by rw [hnAll]; exact hJA)).mpr hJA
    rw [hkR] at h
    exact h
  have htgtR : ∀ i, d.tgtsR J i = d.tgts J i := fun i => by rw [(hview J).2.1]
  have hC := hrep.ctors J cA hJ
  have hpIff := hrep.paramsIff J cA hJ ψ
  have cff := d.ctorFieldFacts_of mp hps (fun t => hpinsAV t ψ)
    (fun t ht => hrep.leafShape t (by rw [hkR]; exact ht) ψ)
    (fun t ht => d.formerFacts_of_indRep hrep hkR ψ ht) hparams hC hpIff hmemJ
    (fun i => by have := hrep.tgtsRLt J i; rw [htgtR i] at this; exact this) htgtR
  have h := d.ctorAtPins_real mp hps hparams hC hpIff (fun fs hfs => (cff.2 fs hfs).1)
    (Eiss := d.eissR J ψ) (tls := d.tssR J ψ)
  rw [hhead, show useIh J = fun _ => false from funext hu]
  exact IndRepData.CtorAtPins.congr_tg d (fun _ => rfl) (d.invTgAV_congr hL.symm hp.symm) h

/-- **The ψ⁻¹ setup of a NESTED scratch block**, from one member's
representation: the members below `kR` are the block's own (ψ⁻¹ is the
identity there and their facts are discharged here); the members from
`kR` on are the copies, whose target and constructors the caller
supplies — `targetOk_copy`/`ctorAtPins_copy` at the three records. -/
theorem invSetup_of_member_nested {μ : CheckMode} {mp : EnvModelM V μ env}
    (hctorsC : d.ctorsC = []) (hkR : d.kReal = d.k)
    (hpinsAV : ∀ (t : Nat) (ψ : Name → Nat), d.pinsAV t ψ = paramBvarsAt d.nP d.nP)
    (hview : ∀ J, d.ksR J = d.ksF J ∧ d.tgtsR J = d.tgts J ∧ d.eissR J = d.eissF J ∧
      d.tssR J = d.tssF J)
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {t₀ : Nat}
    (ht₀ : t₀ < d.k) (hrules : rules ≠ [])
    (hfR : env.find? cvR.name = some (.recInfo cvR mI rP rules))
    (hrep : IndRep mp.base2 T cvT cvR mI rP rules d t₀)
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm}
    {pinsT : Nat → List AnnotTerm} {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {kR : Nat}
    (hps : ps.length = d.nP) (hpsWD : ∀ p ∈ ps, WellDenotedV V ρ p)
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    (hlev : d.elimL.eval ψ = d.w ψ)
    (hreal : ∀ t, t < kR → t < d.k →
      L t = mp.base2.acval (d.memberName t) ψ ∧ pinsT t = paramBvarsAt d.nP d.nP)
    (hrealC : ∀ J cA, d.ctorsA[J]? = some cA → d.mems J < kR →
      head J = AnnotTerm.mkAppN (mp.base2.acval cA.1.name ψ) (paramBvarsAt d.nP d.nP) ∧
        ∀ i, useIh J i = false)
    (hTgC : ∀ t, kR ≤ t → t < d.k → d.TargetOk ψ ρ ps L pinsT t)
    (hCAPC : ∀ J cA, d.ctorsA[J]? = some cA → kR ≤ d.mems J →
      d.CtorAtPins ψ ρ ps (d.invTgAV ψ ps L pinsT) (useIh J) J (head J) cA.2 (d.dsF J ψ)
        (d.esF J ψ) (d.eissR J ψ) (d.tssR J ψ))
    (huse : ∀ J i, useIh J i = true → i ∈ ConLeche.recIdxOf (d.ksR J)) :
    d.InvSetup mp cvT.levelParams cvT.levelParams ψ ρ ps L pinsT head useIh := by
  refine d.invSetup_of_member hctorsC hkR hpinsAV hview ht₀ hrules hfR hrep hps hpsWD hparams
    ?_ ?_ huse
  · intro t ht
    rcases Nat.lt_or_ge t kR with hlt | hge
    · obtain ⟨hL, hp⟩ := hreal t hlt ht
      exact d.targetOk_choice_real hrep hkR hps hparams hlev ht hL hp
    · exact hTgC t hge ht
  · intro J cA hJ
    rcases Nat.lt_or_ge (d.mems J) kR with hlt | hge
    · obtain ⟨hhead, hu⟩ := hrealC J cA hJ hlt
      obtain ⟨hL, hp⟩ := hreal (d.mems J) hlt (by
        have hJA : J < d.ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
        have hnAll : d.nAll = d.ctorsA.length := by
          show d.ctorsA.length + d.ctorsC.length = _
          rw [hctorsC]
          rfl
        have h := (hrep.memsReal J (by rw [hnAll]; exact hJA)).mpr hJA
        rw [hkR] at h
        exact h)
      exact d.ctorAtPins_choice_real hrep hkR hctorsC hpinsAV hview hps hparams hJ hhead hu hL hp
    · exact hCAPC J cA hJ hge

end IndRepData

/-- **The ψ⁻¹ setup of a mutual block**, from its representations
(`invSetup_of_member` at the member the block's existential supplies):
the datum is the block's re-sorted to that member's own spelling of the
sort, and every field the fold reads is unchanged by the re-sorting, so
the consumer's hypotheses are stated at `d` itself. -/
theorem invSetup_of_blockReps {μ : CheckMode} {mp : EnvModelM V μ env} {b : ConLeche.MutualBlock}
    {d : IndRepData V} (hreps : MutualBlockReps mp.base2 b d)
    {t₀ : Nat} (ht₀ : t₀ < b.k) (hct₀ : d.memberCtors t₀ ≠ [])
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm}
    {pinsT : Nat → List AnnotTerm} {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool}
    (hps : ps.length = d.nP) (hpsWD : ∀ p ∈ ps, WellDenotedV V ρ p)
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    (hTg : ∀ t, t < d.k → d.TargetOk ψ ρ ps L pinsT t)
    (hCAP : ∀ J cA, d.ctorsA[J]? = some cA →
      d.CtorAtPins ψ ρ ps (d.invTgAV ψ ps L pinsT) (useIh J) J (head J) cA.2 (d.dsF J ψ)
        (d.esF J ψ) (d.eissR J ψ) (d.tssR J ψ))
    (huse : ∀ J i, useIh J i = true → i ∈ ConLeche.recIdxOf (d.ksR J)) :
    ∃ (s : Level) (lps lpsT : List Name),
      (∀ ψ' : Name → Nat, s.eval ψ' = d.resSort.eval ψ') ∧
      ({d with resSort := s} : IndRepData V).InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh := by
  obtain ⟨hctorsC, hkb, hkRb, -, hpinsAV, hview, -, hall⟩ := hreps
  obtain ⟨s, cvT, cvR, capsT, mI, rP, rules, -, hfR, hrul, hsv, hrep⟩ := hall t₀ ht₀
  have hkR : ({d with resSort := s} : IndRepData V).kReal
      = ({d with resSort := s} : IndRepData V).k := by
    show d.kReal = d.k
    rw [hkb, hkRb]
  refine ⟨s, cvT.levelParams, cvT.levelParams, hsv, ?_⟩
  exact IndRepData.invSetup_of_member ({d with resSort := s} : IndRepData V) hctorsC hkR
    (fun t ψ' => hpinsAV t ψ') hview
    (show t₀ < d.k by rw [hkb]; exact ht₀) (hrul hct₀) hfR hrep hps hpsWD hparams hTg hCAP huse


/-- **The ψ⁻¹ setup of a nested block's SCRATCH block**, from its
representations: the block's own members (below `kR`) at the identity,
the copies (from `kR` on) at their containers' leaves — the caller's
`targetOk_copy`/`ctorAtPins_copy` at the three records of this module.
The elimination universe is read at the block's own sort spelling; the
member's is the same value (`MutualBlockReps`). -/
theorem invSetup_of_blockReps_nested {μ : CheckMode} {mp : EnvModelM V μ env}
    {b : ConLeche.MutualBlock} {d : IndRepData V} (hreps : MutualBlockReps mp.base2 b d)
    {t₀ : Nat} (ht₀ : t₀ < b.k) (hct₀ : d.memberCtors t₀ ≠ [])
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm}
    {pinsT : Nat → List AnnotTerm} {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {kR : Nat}
    (hps : ps.length = d.nP) (hpsWD : ∀ p ∈ ps, WellDenotedV V ρ p)
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    (hlev : d.elimL.eval ψ = d.w ψ)
    (hreal : ∀ t, t < kR → t < d.k →
      L t = mp.base2.acval (d.memberName t) ψ ∧ pinsT t = paramBvarsAt d.nP d.nP)
    (hrealC : ∀ J cA, d.ctorsA[J]? = some cA → d.mems J < kR →
      head J = AnnotTerm.mkAppN (mp.base2.acval cA.1.name ψ) (paramBvarsAt d.nP d.nP) ∧
        ∀ i, useIh J i = false)
    (hTgC : ∀ t, kR ≤ t → t < d.k → d.TargetOk ψ ρ ps L pinsT t)
    (hCAPC : ∀ J cA, d.ctorsA[J]? = some cA → kR ≤ d.mems J →
      d.CtorAtPins ψ ρ ps (d.invTgAV ψ ps L pinsT) (useIh J) J (head J) cA.2 (d.dsF J ψ)
        (d.esF J ψ) (d.eissR J ψ) (d.tssR J ψ))
    (huse : ∀ J i, useIh J i = true → i ∈ ConLeche.recIdxOf (d.ksR J)) :
    ∃ (s : Level) (lps lpsT : List Name),
      (∀ ψ' : Name → Nat, s.eval ψ' = d.resSort.eval ψ') ∧
      ({d with resSort := s} : IndRepData V).InvSetup mp lps lpsT ψ ρ ps L pinsT head useIh := by
  obtain ⟨hctorsC, hkb, hkRb, -, hpinsAV, hview, -, hall⟩ := hreps
  obtain ⟨s, cvT, cvR, capsT, mI, rP, rules, -, hfR, hrul, hsv, hrep⟩ := hall t₀ ht₀
  have hkR : ({d with resSort := s} : IndRepData V).kReal
      = ({d with resSort := s} : IndRepData V).k := by
    show d.kReal = d.k
    rw [hkb, hkRb]
  have hlev' : ({d with resSort := s} : IndRepData V).elimL.eval ψ
      = ({d with resSort := s} : IndRepData V).w ψ := by
    show d.elimL.eval ψ = s.eval ψ
    rw [hsv ψ]
    exact hlev
  refine ⟨s, cvT.levelParams, cvT.levelParams, hsv, ?_⟩
  exact IndRepData.invSetup_of_member_nested ({d with resSort := s} : IndRepData V) hctorsC hkR
    (fun t ψ' => hpinsAV t ψ') hview (show t₀ < d.k by rw [hkb]; exact ht₀) (hrul hct₀) hfR hrep
    hps hpsWD hparams hlev' hreal hrealC hTgC hCAPC huse

/-! ## The copies' index telescopes: the container's at the pin (session 9)

`CopyIdxRead` from the ALIGNMENT of the copy's stored former with the
container's: opened at the aux block's parameter openers, the copy's
former is `instPis` of the container's stored former (at the level
instantiation the pin names) at the pin's ANNOTATED components.  That
equation is what the run must certify (DESIGN §M.21's finding: the aux
install re-annotates the copy's types, recomputing every `.never` bit,
and the model cannot pin those bits semantically); under it the copy's
index telescope reads as the container's peeled at the components
(`denoteMeta_instPisAt_peel`), and an index spine fits the one iff it
fits the other at the components' values (`spineFit_instSeqDoms_iff`:
`instSeq` through a Π-tower is entrywise, and its interpretation under
`i` binders is the interpretation at the substituted frame).
-/

omit [SetTheory V] in
/-- `instE` at the bottom is `cons`. -/
theorem instE_zero_eq_cons (x : V) (ρ : Nat → V) : instE 0 x ρ = cons x ρ := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [instE, cons]

/-- **An instantiation sequence under binders**: substituting `ws` for
the variables just below `xs` reads at the frame with `ws`'s values
pushed under `xs`. -/
theorem interp_instSeq_under (σ : Nat → V) :
    ∀ (ws : List AnnotTerm) (xs : List V) (t : Nat) (e : AnnotTerm),
      (ws ≠ [] → ws.length + xs.length = t + 1) →
      interp V (consList xs σ) (ConLeche.Model.AnnotTerm.instSeq ws t e)
        = interp V (consList xs (consList (ws.map (interp V σ)) σ)) e
  | [], xs, t, e, _ => rfl
  | w :: ws, xs, t, e, hlen => by
    have ht : t = ws.length + xs.length := by
      have := hlen (List.cons_ne_nil w ws)
      simp only [List.length_cons] at this
      omega
    rw [AnnotTerm.instSeq_cons, interp_instSeq_under σ ws xs (t - 1) (e.inst w t)
      (fun hne => by
        have hpos : ws.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
        omega)]
    rw [interp_inst]
    have hfr : consList xs (consList (ws.map (interp V σ)) σ)
        = consList (ws.map (interp V σ) ++ xs) σ := (consList_append _ _ _).symm
    have hlenF : (ws.map (interp V σ) ++ xs).length = t := by
      rw [List.length_append, List.length_map, ht]
    rw [hfr, ← hlenF, shiftE_consList, ← Nat.add_zero (ws.map (interp V σ) ++ xs).length,
      instE_consList, instE_zero_eq_cons, List.map_cons, consList_cons, consList_append]

/-- The domains of a Π-tower under an instantiation sequence, entry
`i` at index `t + i`. -/
@[expose] def instSeqDoms (ws : List AnnotTerm) : Nat → List (Nat × Nat × AnnotTerm) →
    List (Nat × Nat × AnnotTerm)
  | _, [] => []
  | t, (u, v, A) :: Γ => (u, v, ConLeche.Model.AnnotTerm.instSeq ws t A) :: instSeqDoms ws (t + 1) Γ

omit [SetTheory V] in
theorem instSeqDoms_length (ws : List AnnotTerm) :
    ∀ (t : Nat) (Γ : List (Nat × Nat × AnnotTerm)), (instSeqDoms ws t Γ).length = Γ.length
  | _, [] => rfl
  | t, (_, _, _) :: Γ => by simp [instSeqDoms, instSeqDoms_length ws (t + 1) Γ]

omit [SetTheory V] in
/-- `instSeq` through a Π-tower is entrywise, the body at the deepest
index. -/
theorem instSeq_mkPisAV (ws : List AnnotTerm) :
    ∀ (t : Nat) (Γ : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm), ws.length ≤ t + 1 →
      ConLeche.Model.AnnotTerm.instSeq ws t (mkPisAV Γ B)
        = mkPisAV (instSeqDoms ws t Γ) (ConLeche.Model.AnnotTerm.instSeq ws (t + Γ.length) B)
  | _, [], _, _ => rfl
  | t, (u, v, A) :: Γ, B, hle => by
    simp only [mkPisAV, instSeqDoms]
    rw [instSeqAV_pi ws t u v A (mkPisAV Γ B) hle,
      instSeq_mkPisAV ws (t + 1) Γ B (Nat.le_succ_of_le hle)]
    simp only [List.length_cons]
    rw [show t + (Γ.length + 1) = t + 1 + Γ.length from by omega]

omit [SetTheory V] in
/-- An instantiation sequence leaves a sort alone. -/
theorem instSeq_sort :
    ∀ (ws : List AnnotTerm) (t u : Nat), ConLeche.Model.AnnotTerm.instSeq ws t (.sort u) = .sort u
  | [], _, _ => rfl
  | _ :: ws, t, u => by rw [AnnotTerm.instSeq_cons]; exact instSeq_sort ws (t - 1) u

/-- **The fit transfer**: a spine fits the instantiated telescope
under `xs` iff it fits the telescope at the frame with the
substituted values pushed under `xs`. -/
theorem spineFit_instSeqDoms_iff {ws : List AnnotTerm} {σ : Nat → V} :
    ∀ (xs : List V) (t : Nat) (Γ : List (Nat × Nat × AnnotTerm)) (is : List V),
      (ws ≠ [] → ws.length + xs.length = t + 1) →
      (SpineFit (consList xs σ) ((instSeqDoms ws t Γ).map (·.2.2)) is ↔
        SpineFit (consList xs (consList (ws.map (interp V σ)) σ)) (Γ.map (·.2.2)) is)
  | _, _, [], [], _ => Iff.rfl
  | _, _, [], _ :: _, _ => Iff.rfl
  | _, _, (_, _, _) :: _, [], _ => Iff.rfl
  | xs, t, (u, v, A) :: Γ, a :: is, hlen => by
    simp only [instSeqDoms, List.map_cons, SpineFit]
    rw [interp_instSeq_under σ ws xs t A hlen]
    have hc : ∀ ρ : Nat → V, cons a (consList xs ρ) = consList (xs ++ [a]) ρ := by
      intro ρ; rw [consList_append]; rfl
    rw [hc, hc, spineFit_instSeqDoms_iff (xs ++ [a]) (t + 1) Γ is
      (fun hne => by have := hlen hne; simp only [List.length_append, List.length_singleton]; omega)]

omit [SetTheory V] in
/-- Two sort-ended Π-towers are equal only entrywise (a sort is not a
Π, so the lengths agree). -/
theorem mkPisAV_sort_inj :
    ∀ {Γ₁ Γ₂ : List (Nat × Nat × AnnotTerm)} {w₁ w₂ : Nat},
      mkPisAV Γ₁ (.sort w₁) = mkPisAV Γ₂ (.sort w₂) → Γ₁ = Γ₂ ∧ w₁ = w₂
  | [], [], _, _, h => ⟨rfl, AnnotTerm.sort.inj h⟩
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | (u, v, A) :: Γ₁, (u', v', A') :: Γ₂, w₁, w₂, h => by
    simp only [mkPisAV, AnnotTerm.pi.injEq] at h
    obtain ⟨rfl, rfl, rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := mkPisAV_sort_inj h
    exact ⟨rfl, rfl⟩

omit [SetTheory V] in
/-- `instPis` is the residual of `instPisAt`. -/
theorem instPisAt_of_instPis :
    ∀ (args : List ConLeche.Expr) {e rest : ConLeche.Expr}, Expr.instPis e args = some rest →
      ∃ ds, Expr.instPisAt args e = some (ds, rest)
  | [], e, rest, h => ⟨[], by simp only [Expr.instPis, Option.some.injEq] at h; rw [h]; rfl⟩
  | a :: args, e, rest, h => by
    match e, h with
    | .forallE dom body bm, h =>
      simp only [Expr.instPis] at h
      obtain ⟨ds, hds⟩ := instPisAt_of_instPis args h
      exact ⟨dom :: ds, by simp [Expr.instPisAt, hds]⟩
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => simp [Expr.instPis] at h

/-- **The container's former, peeled at the pin**: at the level
instantiation the pin names, `instPis` of the stored former at the
pin's annotated components reads (at the aux parameter depth) as the
container's index telescope instantiated at the components' readings
(`denoteMeta_instPisAt_peel`, `peelPis_of_piTeleAV`). -/
theorem former_peel {μ : CheckMode} (mp : EnvModelM V μ env) {ψ ψ' : Name → Nat}
    {J : Name} {cvTJ : ConstantVal} {capsJ : IndCaps} (hfJ : env.find? J = some (.indInfo cvTJ capsJ))
    {dJ : IndRepData V} {mmJ : Nat}
    (hFDJ : FormerData mp.base2 cvTJ (dJ.nP + dJ.nIdxAt mmJ) dJ.resSort (dJ.ppsM mmJ) (dJ.lvlsM mmJ))
    {lvls : List Level} (hψ' : ψ' = Level.substFn ψ cvTJ.levelParams lvls)
    {nP : Nat} {argsA : List ConLeche.Expr} {DsA : List AnnotTerm} (hlenA : argsA.length = dJ.nP)
    (hargs : ∀ a ∈ argsA, Expr.WScoped nP a ∧ a.looseBVarsBounded 0 = true)
    (hsp : DenoteMetaSpine mp.base2.acval env ψ nP argsA DsA)
    {rest : ConLeche.Expr}
    (hrest : Expr.instPis (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) argsA
      = some rest) :
    denoteMeta mp.base2.acval env ψ nP rest
      = some (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1)
          (mkPisAV ((dJ.ppsM mmJ ψ').drop dJ.nP) (.sort (dJ.w ψ')))) := by
  have hwf := mp.base2.wf _ (Env.find?_mem hfJ)
  have hnf : (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls).hasFvar = false := by
    rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwf.1
  have hb : (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls).looseBVarsBounded 0 = true := by
    rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
  -- the reading at depth 0, then at the aux depth
  have hread0 : denoteMeta mp.base2.acval env ψ 0
      (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls)
      = some (mkPisAV (dJ.ppsM mmJ ψ') (.sort (dJ.w ψ'))) := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core mp.base2) ψ, ← hψ']
    exact hFDJ.read ψ'
  have hreadN : denoteMeta mp.base2.acval env ψ nP
      (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls)
      = some (mkPisAV (dJ.ppsM mmJ ψ') (.sort (dJ.w ψ'))) :=
    denoteMeta_depth_of_closed mp.base2.acval_closed hnf
      (fun k => denoteMeta_closed mp.base2.acval_erase mp.base2.cval_closed hnf hb hread0 1 k)
      hread0 nP
  -- the peel
  obtain ⟨ds, hpr⟩ := instPisAt_of_instPis argsA hrest
  obtain ⟨restA, hrestA, hpeel⟩ := denoteMeta_instPisAt_peel mp.base2.acval_closed
    (acval_inst_self mp.base2) argsA hpr (Expr.WScoped.of_not_hasFvar hnf) hargs hreadN hsp
  have hlenD : DsA.length = dJ.nP := by rw [← DenoteMetaSpine.length hsp, hlenA]
  have hle : dJ.nP ≤ (dJ.ppsM mmJ ψ').length := by rw [hFDJ.len ψ']; omega
  have htele : PiTeleAV dJ.nP (mkPisAV (dJ.ppsM mmJ ψ') (.sort (dJ.w ψ')))
      ((((dJ.ppsM mmJ ψ').take dJ.nP).map (·.2.2)).reverse)
      (mkPisAV ((dJ.ppsM mmJ ψ').drop dJ.nP) (.sort (dJ.w ψ'))) :=
    piTeleAV_of_stripPisAV (stripPisAV_mkPisAV_take dJ.nP (dJ.ppsM mmJ ψ') _ hle)
  rw [peelPis_of_piTeleAV dJ.nP htele hlenD] at hpeel
  rw [hrestA, Option.some.inj hpeel]

namespace IndRepData

variable (d : IndRepData V)

/-- **`CopyIdxRead` from the alignment**: the copy's stored former,
opened at the aux openers, is the container's stored former (at the
level instantiation) `instPis`'d at the pin's annotated components.
Then the copy's index telescope reading IS the container's peeled at
the components (`former_peel` against the copy's own `FormerData`
through the opening, `mkPisAV_sort_inj`), so the sorts agree and the
fits transfer (`spineFit_instSeqDoms_iff`).  The alignment is the
syntactic fact the run must certify (DESIGN §M.21). -/
theorem copyIdxRead_of_align {μ : CheckMode} (mp : EnvModelM V μ env) {ψ : Name → Nat} {t : Nat}
    {cvT : ConstantVal}
    (hFD : FormerData mp.base2 cvT (d.nP + d.nIdxAt t) d.resSort (d.ppsM t) (d.lvlsM t))
    -- the container's stored former and its data at the level instantiation
    {J : Name} {cvTJ : ConstantVal} {capsJ : IndCaps} (hfJ : env.find? J = some (.indInfo cvTJ capsJ))
    {dJ : IndRepData V} {mmJ : Nat}
    (hFDJ : FormerData mp.base2 cvTJ (dJ.nP + dJ.nIdxAt mmJ) dJ.resSort (dJ.ppsM mmJ) (dJ.lvlsM mmJ))
    {lvls : List Level} {ψ' : Name → Nat} (hψ' : ψ' = Level.substFn ψ cvTJ.levelParams lvls)
    -- the pin's annotated components at the aux parameter depth
    {argsA : List ConLeche.Expr} {DsA : List AnnotTerm} (hlenA : argsA.length = dJ.nP)
    (hargs : ∀ a ∈ argsA, Expr.WScoped d.nP a ∧ a.looseBVarsBounded 0 = true)
    (hsp : DenoteMetaSpine mp.base2.acval env ψ d.nP argsA DsA)
    -- THE ALIGNMENT
    {fvsA : List ConLeche.Expr} {rest : ConLeche.Expr}
    (hopen : ConLeche.openPisAtFvars d.nP cvT.type 0 = some (fvsA, rest))
    (hrest : Expr.instPis (cvTJ.type.instantiateLevelParams cvTJ.levelParams lvls) argsA
      = some rest) :
    d.CopyIdxRead ψ t dJ ψ' mmJ DsA := by
  -- the copy's former, opened: its body reads as its own index telescope
  obtain ⟨Γ, R, htele, hbody, -⟩ := openPisAtFvars_denotePTele d.nP hopen (hFD.read ψ)
  have hle : d.nP ≤ (d.ppsM t ψ).length := by rw [hFD.len ψ]; omega
  have htele' : PiTeleAV d.nP (mkPisAV (d.ppsM t ψ) (.sort (d.w ψ)))
      ((((d.ppsM t ψ).take d.nP).map (·.2.2)).reverse)
      (mkPisAV ((d.ppsM t ψ).drop d.nP) (.sort (d.w ψ))) :=
    piTeleAV_of_stripPisAV (stripPisAV_mkPisAV_take d.nP (d.ppsM t ψ) _ hle)
  obtain ⟨-, rfl⟩ := PiTeleAV.unique htele htele'
  rw [Nat.zero_add] at hbody
  -- … and as the container's peeled at the components
  have hpeel := former_peel mp hfJ hFDJ hψ' hlenA hargs hsp hrest
  rw [hbody] at hpeel
  have hlenD : DsA.length = dJ.nP := by rw [← DenoteMetaSpine.length hsp, hlenA]
  rw [instSeq_mkPisAV DsA (dJ.nP - 1) _ _ (by omega), instSeq_sort] at hpeel
  obtain ⟨hΓ, hw⟩ := mkPisAV_sort_inj (Option.some.inj hpeel)
  refine ⟨hw.symm, fun σ _ is => ?_⟩
  show SpineFit σ (((d.ppsM t ψ).drop d.nP).map (·.2.2)) is ↔
    SpineFit (consList (DsA.map (interp V σ)) σ) (((dJ.ppsM mmJ ψ').drop dJ.nP).map (·.2.2)) is
  rw [hΓ]
  have h := spineFit_instSeqDoms_iff (ws := DsA) (σ := σ) [] (dJ.nP - 1)
    ((dJ.ppsM mmJ ψ').drop dJ.nP) is
    (fun hne => by
      have hpos : DsA.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
      rw [hlenD] at hpos ⊢
      simp only [List.length_nil, Nat.add_zero]
      omega)
  simpa using h

end IndRepData

end ConLeche.Model
