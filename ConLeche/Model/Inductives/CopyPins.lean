module

public import ConLeche.Model.Inductives.InvFold
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

end ConLeche.Model
