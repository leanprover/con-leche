module

public import ConLeche.Model.Inductives.NestedPinLaws
public import ConLeche.Model.Inductives.NestedPins
import ConLeche.Model.Inductives.NestedAux
public section

/-!
# The block's pins as a stored block's pins, and the global entry theorem (task #315, L-E)

Two things live here, both stated at the nested run's block model
`nestedBlockModel` with its pins' constructors `nestedPc`
(`NestedPinLaws.lean`):

* **the pins' SHAPES of the block being installed** — `PinShapes`
  (`NestedPremise.lean`) at an assignment `B` whose value at every pin
  group's container is the group's block model (`nestedPinShapes_of`),
  from the groups carrying the per-group shapes (`NestedPinGroup.shape`,
  lane L-B's `NestedPinsShape`); with M7-1's `PinRecLaws`
  (`nestedPinRecLaws_of`) and the block's own `ContainerModeled` (K.34's
  read-back, the tail's) this is the block's `BlockAt` at the output
  model (`nestedBlockAt_of`) — what `EnvModelB.blocks` asks of the
  nested route (DESIGN §U.36);
* **the global entry theorem** `nestedPinLeaf_all` (DESIGN §U.36): the
  entries `CopyEntryA` at the auxiliary carrier for EVERY group at once,
  from the shapes of the block's pins and the containers' `BlockAt` —
  the residual `NestedPinsEntry` names.  Its plan: `P q` := pin `q`'s
  container's least tuple at the pin's frame; (i) `P` is a fixed point
  of the pins' section of the auxiliary operator at the carrier's
  members, from the shapes with the entries read at `P`
  (`copyEntryAt_of_read` at the containers' `leaf`); (ii) `L⁺`'s pin
  segment lies below `P` (`lfpTuple_le` at the section); (iii) `P` lies
  below the segment by induction on the pin's expression, a self-nested
  container's cycle closed by its own `PinRecLaws.ind` at the segment;
  (iv) `P q = L⁺ (k + q)` is every `pinLeaf` and every entry.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock ElimState NestedPin IndCaps ContainerInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## Kit: the slot's value reads its family at the fitting tuples only -/

/-- The nested product is a congruence in its body over the fitting
spines (`piTele_mono`'s equality twin). -/
theorem piTele_congr {v : Nat} {B B' : List V → V} :
    ∀ {k : Nat} {T : TeleS V k} {acc : List V},
      (∀ as, FitsS T as → B (acc ++ as) = B' (acc ++ as)) →
      piTele v T B acc = piTele v T B' acc
  | _, .nil, acc, h => by
    simp only [piTele]
    have := h [] trivial
    simpa using this
  | _, .cons A T, acc, h => by
    simp only [piTele]
    refine piR_congr fun a ha => ?_
    refine piTele_congr fun as has => ?_
    have := h (a :: as) ⟨ha, has⟩
    simpa [List.append_assoc] using this

/-- **The slot's value is a congruence in the family at the fitting
tuples**: two families agreeing at every index tuple the telescope's
fitting spines produce give one slot. -/
theorem slotSet_congr_app {w u : Nat} {ρ : Nat → V} {tl : List (Nat × Nat × AnnotTerm)}
    {Eis : List AnnotTerm} {X Y : V}
    (h : ∀ bs : List V, SpineFit ρ (tl.map (·.2.2)) bs →
      SetTheory.app X (tupW u (Eis.map (interp V (consList bs ρ))))
        = SetTheory.app Y (tupW u (Eis.map (interp V (consList bs ρ))))) :
    slotSet w u ρ tl Eis X = slotSet w u ρ tl Eis Y := by
  unfold slotSet
  refine piTele_congr fun bs hbs => ?_
  rw [List.nil_append]
  exact h bs (fitsS_teleOfFields.mp hbs)

/-! ## Kit: the readings' frames — a congruence below a depth -/

/-- **The telescope of a field chain reads only the frame below the
chain's bound** (task #315 L-E, DESIGN §U.51): the container instance
transfer reads ONE container's constructor at TWO frames — the
container's own pin frame and the block's — which agree exactly on the
components' values. -/
theorem teleOfFields_congr_below : ∀ {Fs : List AnnotTerm} {k : Nat} {ρ ρ' : Nat → V},
    FieldsBelow k Fs → (∀ v, v < k → ρ v = ρ' v) →
    teleOfFields ρ Fs = teleOfFields ρ' Fs
  | [], _, _, _, _, _ => rfl
  | F :: Fs, k, ρ, ρ', hb, hρ => by
    simp only [teleOfFields_cons]
    rw [interp_congr_below V F k ρ ρ' hb.1 hρ]
    refine congrArg _ (funext fun a => ?_)
    refine teleOfFields_congr_below (k := k + 1) hb.2 fun v hv => ?_
    match v with
    | 0 => rfl
    | v + 1 => exact hρ v (by omega)

/-- **Two frames agreeing below a depth agree below that depth under a
common prefix** (task #315 L-E: `consList_agree_below` at a bound
BEYOND the prefix — the parameters are what the two frames share). -/
theorem consList_agree_above {k : Nat} {ρ ρ' : Nat → V} (hρ : ∀ v, v < k → ρ v = ρ' v)
    (as : List V) : ∀ v, v < as.length + k → consList as ρ v = consList as ρ' v := by
  intro v hv
  rcases Nat.lt_or_ge v as.length with hv' | hv'
  · rw [consList_getD_lt as ρ v hv', consList_getD_lt as ρ' v hv']
  · rw [show v = (v - as.length) + as.length from by omega,
      consList_apply_add as ρ, consList_apply_add as ρ']
    exact hρ _ (by omega)

/-- **A recursive slot reads only the frame below its telescope's
bound** (task #315 L-E, DESIGN §U.48 (i)'s `slotSet_congr_below`): the
telescope's domains are bounded at their own depths and the index
expressions under the telescope, so two frames agreeing below the bound
give one slot. -/
theorem slotSet_congr_below {w u k : Nat} {ρ ρ' : Nat → V}
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm} {X : V}
    (htl : DomsBelow k tl)
    (hEis : ∀ e ∈ Eis, ConLeche.Term.Term.bvarsBelow (k + tl.length) e.erase)
    (hρ : ∀ v, v < k → ρ v = ρ' v) :
    slotSet w u ρ tl Eis X = slotSet w u ρ' tl Eis X := by
  unfold slotSet
  rw [teleOfFields_congr_below (k := k) htl.fields hρ]
  refine piTele_congr fun bs hbs => ?_
  have hlen : bs.length = tl.length := by
    have := FitsS.length_eq hbs
    rw [List.length_map] at this
    exact this
  rw [List.nil_append]
  refine congrArg _ (congrArg _ (List.map_congr_left fun e he => ?_))
  refine interp_congr_below V e (k + tl.length) _ _ (hEis e he) fun v hv => ?_
  exact consList_agree_above hρ bs v (by omega)

/-- **A container's constructor fit at TWO level assignments and TWO
frames** (task #315 L-E, DESIGN §U.51: the gap between the container
instance transfer's two halves): the container instance transfer reads
one container `dK`'s member `i`, constructor `j` twice — once as the
outer container's own copy of a pin, at its pin frame and level
assignment, once as the BLOCK's copy of the image pin, at the block's —
and the two agree because the level assignments agree on the
constructor's level parameters (`targetHead_corr`, `ContainerModeled.pinψ`)
and the frames on the components' values (`PinCorr`'s `Ds`,
`interp_instAll`).  The class data are then one datum
(`IsBlockModel.ctor_params`) and every reading is below the parameter
depth (`CtorDataI.below`/`belowE`, `tssBelow`/`eissBelow`), so
`slotSet_congr_below` and `interp_congr_below` carry the fit across. -/
theorem BlockModel.chainFitT_congr_mem {m : EnvModel V env} {dK : BlockModel V}
    {pc : Nat → PinCtors V} {ψ₁ ψ₂ : Name → Nat} {ρ₁ ρ₂ : Nat → V} {Y : Nat → V} {t : V}
    {i j : Nat} {fs : List V}
    (hreps : IsBlockModels m dK) (hi : i < dK.k)
    {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hψ : ∀ p ∈ cA.1.levelParams, ψ₁ p = ψ₂ p)
    (hw : dK.w ψ₁ = dK.w ψ₂)
    (hu : ∀ l, dK.uT (dK.tgts i j l) ψ₁ = dK.uT (dK.tgts i j l) ψ₂)
    (hIds : (dK.IdsM i ψ₁).length = (dK.IdsM i ψ₂).length)
    (hρ : ∀ v, v < dK.nP → ρ₁ v = ρ₂ v)
    (h : dK.ChainFitT pc ψ₁ ρ₁ Y t i j fs) : dK.ChainFitT pc ψ₂ ρ₂ Y t i j fs := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  obtain ⟨hF, hE, htl, hEs⟩ := hI.ctor_params hj hψ
  have hcd := hI.ctorData hj
  have hlenF := hI.Fss_length hj ψ₁
  unfold BlockModel.ChainFitT at h ⊢
  rw [BlockModel.rssT_of_mem hi, BlockModel.FssT_of_mem hi, BlockModel.IdsT_of_mem hi,
    BlockModel.EssT_of_mem hi] at h ⊢
  obtain ⟨hfit, hidx⟩ := h
  constructor
  · refine (fitsFrom_iff_frames (by rw [hF]) fun l hl fs₁ hl₁ _ _ => ?_).mp hfit
    subst hl₁
    have hlt : fs₁.length < cA.2 := by rw [← hlenF]; exact hl
    have hidx : dK.nP + fs₁.length < (dK.dsF i j ψ₂).length := by rw [hcd.len]; omega
    simp only [Nat.zero_add]
    by_cases hr : ((dK.rss i).getD j []).getD fs₁.length false = true
    · rw [if_pos hr, if_pos hr]
      simp only [BlockModel.slotAtT, BlockModel.tgtsT_of_mem hi, BlockModel.teleAtT_of_mem hi,
        BlockModel.eisAtT_of_mem hi, BlockModel.teleAt, BlockModel.eisAt]
      rw [hw, hu, htl, hE]
      refine slotSet_congr_below (k := dK.nP + fs₁.length) ?_ (fun e he => ?_)
        (fun v hv => consList_agree_above hρ fs₁ v (by omega))
      · rw [IsBlockModel.tlss_getD hj]
        exact hcd.tssBelow ψ₂ fs₁.length
      · have hmem : e ∈ (dK.eissF i j ψ₂).getD fs₁.length [] := by
          rwa [IsBlockModel.Eiss_getD hj] at he
        rw [IsBlockModel.tlss_getD hj]
        exact hcd.eissBelow ψ₂ fs₁.length e hmem
    · have hr' : ((dK.rss i).getD j []).getD fs₁.length false = false := by simpa using hr
      rw [if_neg (by rw [hr']; exact Bool.false_ne_true),
        if_neg (by rw [hr']; exact Bool.false_ne_true), hF]
      refine interp_congr_below V _ (dK.nP + fs₁.length) _ _ ?_
        (fun v hv => consList_agree_above hρ fs₁ v (by omega))
      have hbelow := (hcd.below ψ₂).getD_below (dK.nP + fs₁.length) hidx
      rw [Nat.zero_add, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx] at hbelow
      rw [IsBlockModel.Fss_getD hj, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_drop, List.getElem?_eq_getElem hidx]
      simpa using hbelow
  · intro l hl
    have hlenE : ((dK.Ess i ψ₁).getD j []).length = (dK.IdsM i ψ₁).length := by
      rw [IsBlockModel.Ess_getD hj, hcd.lenE, hI.IdsM_length ψ₁]
    have hlt' : l < ((dK.Ess i ψ₁).getD j []).length := by
      rw [hlenE, ← hIds] at *
      exact hl
    have hgetD_mem : ∀ (L : List AnnotTerm), l < L.length → L.getD l default ∈ L := by
      intro L hL
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hL]
      simp
    have hmemE := hgetD_mem ((dK.Ess i ψ₁).getD j []) hlt'
    have hlen : fs.length = cA.2 := by rw [hfit.length_eq, hlenF]
    rw [← hEs, ← hidx l (by rw [hIds]; exact hl)]
    refine interp_congr_below V _ (dK.nP + fs.length) _ _ ?_
      (fun v hv => (consList_agree_above hρ fs v (by omega)).symm)
    have hbE := hcd.belowE ψ₁ _ (by rwa [IsBlockModel.Ess_getD hj] at hmemE)
    rw [hlen, IsBlockModel.Ess_getD hj]
    exact hbE

/-! ## The extended carrier is least among the tuples closed under the classes' constructors -/

/-- **A tuple over the classes closed under the classes' constructors**
(task #315 L-E, DESIGN §U.48 (h)): in the extended space, and every
constructor fit at it (`ChainFitT`: the members' constructors and the
pins' `pc`, all reading the tuple) injects into it. -/
@[expose] def BlockModel.TClosed (d : BlockModel V) (pc : Nat → PinCtors V) (ψ : Name → Nat)
    (ρp : Nat → V) (T : Nat → V) : Prop :=
  InTupleSpace (d.w ψ) d.kT (d.idxT ψ ρp) T ∧
  ∀ c, c < d.kT → ∀ t, t ∈ˢ d.idxT ψ ρp c → ∀ j fs, j < (d.ctorsT pc c).length →
    d.ChainFitT pc ψ ρp T t c j fs → d.injT pc ψ c j fs ∈ˢ SetTheory.app (T c) t

/-- The separated pins lie under the property at every point. -/
theorem BlockModel.app_sepPins_subset_P (d : BlockModel V) {ψ : Name → Nat} {ρp : Nat → V}
    {X : Nat → V} (P : Nat → V → V → Prop) {q : Nat} (t : V) :
    ∀ x, x ∈ˢ SetTheory.app (d.sepPins ψ ρp X P q) t → P q t x := by
  intro x hx
  by_cases ht : t ∈ˢ d.pinIdx q ψ ρp
  · unfold BlockModel.sepPins at hx
    rw [app_graph ht] at hx
    exact (mem_sep.mp hx).2
  · unfold BlockModel.sepPins at hx
    rw [app_graph_of_not_mem ht] at hx
    exact absurd hx (not_mem_empty x)

/-- **The extended carrier lies below every closed tuple** (task #315
L-E, DESIGN §U.48 (h)): the members' least tuple with the pins'
carriers at it (`famAt LJ`) is below any `TClosed` tuple `T` — the pins'
carriers at `T`'s members are below `T`'s pins (`PinRecLaws.ind` at
the property "in `T`", the separated pins being under it), so `T`'s
members are closed under the members' operator (its fits read the
pins' carriers, `chainFitT_of_chainFit` + `ChainFitT_mono`), so the
least tuple is below them (`lfpTuple_le`), and the pins follow by
`pinMono`.  No set operator over the classes is needed. -/
theorem BlockModel.famAt_le_of_TClosed {env : Env} {m : EnvModel V env} {d : BlockModel V}
    {pc : Nat → PinCtors V} (hreps : IsBlockModels m d) (hp : PinRecLaws m d pc) (hk : 0 < d.k)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) {T : Nat → V}
    (hT : d.TClosed pc ψ ρp T) :
    TupleLe d.kT (d.idxT ψ ρp)
      (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) T := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI0⟩ := hreps 0 hk
  have hTm : InTupleSpace (d.w ψ) d.k (d.idx ψ ρp) T := by
    intro mm hmm
    have := hT.1 mm (by show mm < d.k + d.nPins; omega)
    rwa [BlockModel.idxT_of_mem hmm] at this
  -- (1) the pins' carriers at `T`'s members are below `T`'s pins
  have h1 : ∀ q, q < d.nPins → ∀ t, t ∈ˢ d.pinIdx q ψ ρp → ∀ x,
      x ∈ˢ SetTheory.app (d.pinCar ψ ρp T q) t → x ∈ˢ SetTheory.app (T (d.k + q)) t := by
    intro q hq t ht x hx
    refine hp.ind ψ ρp hρp T hTm (fun q' t' x' => x' ∈ˢ SetTheory.app (T (d.k + q')) t')
      (fun q' hq' t' ht' j fs hj hfit => ?_) q hq t ht x hx
    have hnk : ¬ d.k + q' < d.k := by omega
    have hfit' : d.ChainFitT pc ψ ρp T t' (d.k + q') j fs := by
      refine d.ChainFitT_mono pc (fun c' hc' t'' => ?_) (fun i hi hr => ?_) hfit
      · have hc'k : c' < d.k + d.nPins := hc'
        by_cases hc'' : c' < d.k
        · rw [segJoin_lt _ _ hc'', d.famAt_of_mem hc'']
          exact Subset.refl _
        · rw [show c' = d.k + (c' - d.k) by omega, segJoin_add _ _ (by omega : c' - d.k < d.nPins)]
          intro x' hx'
          exact d.app_sepPins_subset_P _ t'' x' hx'
      · rw [BlockModel.FssT_of_pin hnk, Nat.add_sub_cancel_left] at hi
        rw [BlockModel.rssT_of_pin hnk] at hr
        rw [BlockModel.tgtsT_of_pin hnk, Nat.add_sub_cancel_left]
        exact hp.tgtsLt ψ q' j i hq' hj hi
    have := hT.2 (d.k + q') (by show d.k + q' < d.k + d.nPins; omega) t'
      (by rw [BlockModel.idxT_of_pin hnk, Nat.add_sub_cancel_left]; exact ht') j fs
      (by rw [BlockModel.ctorsT_of_pin hnk, Nat.add_sub_cancel_left]; exact hj) hfit'
    rw [BlockModel.injT_of_pin hnk, Nat.add_sub_cancel_left] at this
    exact this
  -- (2) `T`'s members are closed under the members' operator
  have h2 : IsClosedTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp) T := by
    refine ⟨hTm, fun i hi t ht x hx => ?_⟩
    obtain ⟨cvT', cvR', mI', rP', rules', hI'⟩ := hreps i hi
    obtain ⟨j, fs, hj, hC, rfl⟩ := (hI'.fibre ψ ρp hρp T hTm i hi t ht x).mp hx
    have hCT := d.chainFitT_of_chainFit pc hi hC
    have hCT' : d.ChainFitT pc ψ ρp T t i j fs := by
      refine d.ChainFitT_mono pc (fun c' hc' t'' => ?_) (fun i' hi' hr => ?_) hCT
      · have hc'k : c' < d.k + d.nPins := hc'
        by_cases hc'' : c' < d.k
        · rw [d.famAt_of_mem hc'']
          exact Subset.refl _
        · rw [d.famAt_of_pin hc'']
          have hq' : c' - d.k < d.nPins := by omega
          refine app_subset_of_famLe (hI0.pinMem ψ ρp hρp T hTm _ hq') (fun t₀ ht₀ x' hx' => ?_) t''
          have := h1 _ hq' t₀ ht₀ x' hx'
          rwa [show d.k + (c' - d.k) = c' by omega] at this
      · rw [BlockModel.FssT_of_mem hi] at hi'
        rw [BlockModel.rssT_of_mem hi] at hr
        rw [BlockModel.tgtsT_of_mem hi]
        have hks : (d.ksF i j).length = ((d.Fss i ψ).getD j []).length := by
          rw [(hI'.ctorData (List.getElem?_eq_getElem hj)).ksLen,
            hI'.Fss_length (List.getElem?_eq_getElem hj) ψ]
        exact hI'.tgtsLt i j i' hi hj (by rw [hks]; exact hi')
    have := hT.2 i (by show i < d.k + d.nPins; omega) t
      (by rw [BlockModel.idxT_of_mem hi]; exact ht) j fs
      (by rw [BlockModel.ctorsT_of_mem hi]; exact hj) hCT'
    rw [BlockModel.injT_of_mem hi] at this
    exact this
  -- assemble
  intro c hc
  by_cases hcm : c < d.k
  · rw [d.famAt_of_mem hcm, BlockModel.idxT_of_mem hcm]
    exact lfpTuple_le h2 c hcm
  · rw [d.famAt_of_pin hcm, BlockModel.idxT_of_pin hcm]
    have hq : c - d.k < d.nPins := by
      have : c < d.k + d.nPins := hc
      omega
    have hmono := hI0.pinMono ψ ρp hρp _ T (lfpTuple_mem _ _ _ _) hTm (lfpTuple_le h2) _ hq
    refine hmono.trans fun t ht x hx => ?_
    have := h1 _ hq t ht x hx
    rwa [show d.k + (c - d.k) = c by omega] at this

/-! ## The entry at a container's OWN pin, from the pin correspondence -/

/-- **The `pinF` entry at a tuple whose target family reads the stored
reading** (task #315 L-E, step (i)): at a container-recursive field at
one of the container's OWN pins `qK`, the container's domain read at the
pin's frame is (`real_dom_eq`) the container's slot at its carrier —
its pin's carrier at `LJ` — which `pinLeaf` reads as the container `K`
at the pin's components applied to the index spine; the copy's slot at
`Z` at the corresponding block pin reads (`hZ`) the SAME stored reading
(`PinCorr`), so the two slots agree at every fitting tuple
(`slotSet_congr_app`, `slotSet_instTele`).  `hfr` transports a fit at
the container's pin frame to the block pin's frame (the two differ in
their base only, below the components). -/
theorem copyEntryAt_of_pinCorr {env : Env} {m : EnvModel V env} {TV : TargetView V}
    {dJ : BlockModel V} {ψJ : Name → Nat} {Ds : List AnnotTerm} {DsE : List Expr}
    {tg : Nat → Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {ρp : Nat → V}
    {i j l : Nat}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hi : i < dJ.k) {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (hρJ : Sat V (dJ.params ψJ).reverse (consList (Ds.map (interp V ρp)) ρp))
    (hw : dJ.w ψJ = TV.w) (hl : l < ((dJ.Fss i ψJ).getD j []).length)
    (hr : ((dJ.rss i).getD j []).getD l false = true) (hnt : ¬ dJ.tgts i j l < dJ.k)
    {lpsJ : List Name} {lvlsJ : List Level}
    (hcorr : PinCorr TV m.acval dJ ψJ Ds DsE lpsJ lvlsJ (tg l) (dJ.tgts i j l - dJ.k))
    (htl : (tls.getD l []).map (·.2.2)
      = instTele Ds l ((((dJ.tlss i ψJ).getD j []).getD l []).map (·.2.2)))
    (hEis : Eis.getD l [] = (((dJ.Eiss i ψJ).getD j []).getD l []).map
      (AnnotTerm.instAll Ds (l + (((dJ.tlss i ψJ).getD j []).getD l []).length)))
    (hfr : ∀ is : List V,
      SpineFit (dJ.pinFrame (dJ.tgts i j l - dJ.k) ψJ (consList (Ds.map (interp V ρp)) ρp))
        ((dJ.pinAt (dJ.tgts i j l - dJ.k)).Ids ψJ) is →
      SpineFit (TV.frame ρp (tg l)) (TV.Ids (tg l)) is)
    {Z : Nat → V}
    (hZ : ∀ is : List V, SpineFit (TV.frame ρp (tg l)) (TV.Ids (tg l)) is →
      SetTheory.app (Z (tg l)) (tupW (TV.u (tg l)) is)
        = is.foldl SetTheory.app (interp V ρp (TV.EA (tg l)))) :
    CopyEntryAt dJ ψJ Ds tg tls Eis ρp i j TV.w TV.u Z l := by
  intro fs₁ hl₁ hsp
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hjl : j < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hlenF := hI.Fss_length hj ψJ
  have hlt : l < cA.2 := by rw [← hlenF]; exact hl
  have hks : (dJ.ksF i j).length = ((dJ.Fss i ψJ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hlenF]
  have hr' : (rsOf (dJ.ksF i j)).getD l false = true := by
    rwa [IsBlockModel.rss_getD hjl] at hr
  subst hl₁
  obtain ⟨qK, hqK⟩ : ∃ qK, qK = dJ.tgts i j fs₁.length - dJ.k := ⟨_, rfl⟩
  have hqlt : qK < dJ.nPins := hqK ▸ hreps.tgt_pin_lt hi hj _ hl hnt
  rw [← hqK] at hcorr hfr
  obtain ⟨hEA, hDs, hu, hIds, -, -⟩ := hcorr
  -- the container's domain is its slot at the carrier: its own pin's carrier
  rw [hreps.real_dom_eq hfT hPT hi hj hρJ hlt hr' hsp, dJ.slotAt_of_pin hnt, ← hqK]
  have hρ : (fun n => consList fs₁ (consList (Ds.map (interp V ρp)) ρp) (n + fs₁.length))
      = consList (Ds.map (interp V ρp)) ρp :=
    funext fun n => consList_apply_add fs₁ _ n
  rw [hρ]
  -- the copy's slot, at the container's frame
  rw [← hu, ← hw, hEis]
  rw [slotSet_instTele (w := dJ.w ψJ) (w' := dJ.w ψJ) (u := TV.u (tg fs₁.length))
    (u' := TV.u (tg fs₁.length)) Iff.rfl Iff.rfl Ds ρp fs₁ htl
    (((dJ.Eiss i ψJ).getD j []).getD fs₁.length []) (Z (tg fs₁.length))]
  -- the two families agree at every fitting tuple
  refine slotSet_congr_app fun bs hbs => ?_
  -- the index readings fit the container's pin
  have hfit : SpineFit (dJ.pinFrame qK ψJ (consList (Ds.map (interp V ρp)) ρp))
      ((dJ.pinAt qK).Ids ψJ)
      ((((dJ.Eiss i ψJ).getD j []).getD fs₁.length []).map
        (interp V (consList bs (consList fs₁ (consList (Ds.map (interp V ρp)) ρp))))) := by
    have hcd := hI.ctorData hj
    have hiK : fs₁.length < (dJ.ksF i j).length := by rw [hks]; exact hl
    have hk : (dJ.ksF i j).getD fs₁.length .ordinary = .recursive ∨
        (dJ.ksF i j).getD fs₁.length .ordinary = .reflexive := by
      unfold rsOf at hr'
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hiK,
        Option.map_some, Option.getD_some, decide_eq_true_iff] at hr'
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hiK]
      exact hr'
    have hnest : dJ.nestOf i j fs₁.length = some qK := hqK ▸ dJ.nestOf_some hnt
    rw [IsBlockModel.Eiss_getD hj]
    rw [IsBlockModel.tlss_getD hj] at hbs
    rcases hk with hk | hk
    · rw [hcd.tssNone ψJ _ (by rw [hk]; decide)] at hbs
      cases bs with
      | nil =>
        simpa using hreps.nest_eis_fit hPT hi hj hρJ hlt hnest hqlt hk hsp
      | cons _ _ => exact hbs.elim
    · exact hreps.nest_refl_eis_fit hPT hi hj hρJ hlt hnest hqlt hk hsp hbs
  -- the container's pin at the carrier: `pinLeaf`
  obtain ⟨ρ, as, hρJas, hspJ⟩ := spineOfSat_params dJ hρJ
  rw [hρJas] at hfit ⊢
  have hleaf := hI.pinLeaf qK hqlt ψJ ρ as _ hspJ hfit
  rw [← hρJas] at hfit
  -- the block's pin at `Z`: the same stored reading
  have hZ' := hZ _ (hfr _ hfit)
  rw [hρJas] at hZ'
  rw [hZ', hEA, hu, ← hleaf, interp_mkAppN_foldl, List.map_map, ← List.foldl_append,
    interp_closed (V := V) (m.cval_closedL _ _) ρp ρ]
  congr 2
  refine List.map_congr_left fun D _ => ?_
  show interp V (consList as ρ) D = interp V ρp (AnnotTerm.instAll Ds 0 D)
  have := interp_instAll Ds [] ρp D
  rw [hρJas] at this
  simpa using this.symm

section Assembly

variable {F : Nat} {g : Bool} {mp : EnvModelM V μ env} {p : NestedParts} {b : MutualBlock}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn} {env₂ : Env}

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "PC" => (nestedPc (V := V) b ctorsA kinds p.k f₀.s dsF esF eissF tssF)

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

local notation "PGS" => NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

/-- **The block model's target view IS the auxiliary lists'**: every
field by construction except the index universes, which agree by
`ofNested_uT`. -/
theorem nestedBlockModel_targetView (m : EnvModel V env₂) (ψ : Name → Nat) :
    (D).targetView m.acval ψ
      = nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS m.acval (D).memberNames ψ := by
  unfold BlockModel.targetView nestedTV
  congr 1
  funext t
  exact ofNested_uT t ψ

/-- **The pins' shapes of the block being installed**, at an assignment
`B` whose value at every pin's container's group is the group's block
model (`hgroupsB`: the groups, with their model NAMED by `B`): pin `q`'s
constructors `nestedPc` have `CopyCtorShape` against `B ci` — the
group's `shape` field (lane L-B's `NestedPinsShape`) read at the
group's base pin through `same`, the auxiliary lists' positions
against the dropped ones (`getD_drop`), and the target view's
identity. -/
theorem nestedPinShapes_of (m : EnvModel V env₂) {B : ContainerInfo → BlockModel V}
    (hgroupsB : ∀ q, q < pinsS.length → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? env₂ ((D).pinAt q).J = some ci →
      ∃ (q₀ kJ i : Nat), q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ (B ci) ∧
        ∀ i', i' < kJ → ((D).pinAt (q₀ + i')).DsE = ((D).pinAt q₀).DsE)
    (hcont : ∀ q, q < pinsS.length →
      ∃ ci : ContainerInfo, ConLeche.containerInfo? env₂ ((D).pinAt q).J = some ci) :
    PinShapes m B (D) PC := by
  intro q hq
  obtain ⟨ci, hci⟩ := hcont q hq
  obtain ⟨q₀, kJ, i, hqe, hi, G, hDsE⟩ := hgroupsB q hq ci hci
  refine ⟨q₀, kJ, i, ci, hqe, hi, hci, ?_, ?_⟩
  · -- the group, viewed
    have h0 : q₀ + 0 = q₀ := Nat.add_zero q₀
    refine ⟨G.seg, G.kpos, G.kEq, fun i' hi' => ?_, G.same, hDsE, G.lvls, fun i' hi' ψ => ?_,
      G.pinNP, G.pinNIdx, G.pinPps, fun ψ => ?_, fun ψ => ?_, fun ψ ρ as hsp => ?_⟩
    · obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i' hi'
      exact hI.member.symm
    · have := G.pinU 0 G.kpos ψ i' hi'
      rwa [h0] at this
    · have := G.pinDsLen 0 G.kpos ψ
      rwa [h0] at this
    · have := G.w 0 G.kpos ψ
      rwa [h0] at this
    · have := G.DsFit 0 G.kpos ψ ρ as hsp
      rwa [h0] at this
  · -- the shape, at the base pin's record and the dropped lists
    intro ψ ρp hρp i' j hi' hj cvT caps hf
    have hsh := G.shape i' hi' cvT caps hf ψ ρp hρp i' hi' j hj
    rw [(G.same i' hi' ψ).1, (G.same i' hi' ψ).2, hDsE i' hi', G.lvls i' hi'] at hsh
    unfold CopyShapeA at hsh
    rw [nestedBlockModel_targetView m ψ]
    simp only [nestedPc, getD_drop, ← Nat.add_assoc]
    exact hsh

/-- **The block's obligation at the output model**: its own
`ContainerModeled` (K.34's read-back, the tail's), M7-1's `PinRecLaws`
and the shapes above, at an assignment carrying the block at its
group. -/
theorem nestedBlockAt_of (m : EnvModel V env₂) {B : ContainerInfo → BlockModel V}
    {ci : ContainerInfo} (hB : B ci = D) (C : ContainerModeled m ci (D))
    (hL : PinRecLaws m (D) PC) (hS : PinShapes m B (D) PC) : BlockAt m B ci := by
  rw [BlockAt, hB]
  exact ⟨C, PC, hL, hS⟩

/-! ## The targets read as the stored readings — step (i)'s two leaf laws -/

/-- **A MEMBER target reads as the block's carrier**: at a spine fitting
the member's index telescope at the parameter frame, the block's
carrier at the member, at the spine's tuple (the block's index
universe), is the member's stored reading — the auxiliary leaf
(`hleafM`) at the parameters (`tupleLfpAV_fold`, Bekić's nested form
`ofNested_lfp`) — applied to the spine.  The `hZ` of
`copyEntryAt_of_read` at a member target. -/
theorem memberTarget_reads
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    (hOk : NestedLfpOk (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
      (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
      (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
      (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
      (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
      (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) ψ ρp)
    {t : Nat} (ht : t < p.k) {is : List V} (his : SpineFit ρp (blockIds b.nP ppsF ψ t) is) :
    SetTheory.app (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp) t) (tupW (W ψ) is)
      = is.foldl SetTheory.app
          (interp V ρp (targetRead m.acval ((fms.take p.k).map (·.cvTa.name)) pinsS b.nP p.k ψ t)) := by
  have hkT : b.k = fms.length := h.lenFms.symm
  have hplen : ((D).params ψ).length = b.nP := by
    show (((ppsF 0 ψ).take b.nP).map (·.2.2)).length = b.nP
    rw [List.length_map, List.length_take, (h.FD 0 f₀ h.first).len ψ]
    omega
  have htl : t < fms.length := by rw [← hkT, hbk]; omega
  have hft := fms_get htl
  obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
  have hlenAs : as.length = b.nP := by rw [hsp.length_eq, hplen]
  have hOk' := hOk
  -- the stored reading is the auxiliary leaf at the parameters
  have hName : ((fms.take p.k).map (·.cvTa.name)).getD t .anonymous = (fms.getD t default).cvTa.name := by
    show ((fms.take p.k).map (·.cvTa.name)).getD t .anonymous = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt ht, hft]
    rfl
  have hpar : (paramBvarsAt b.nP b.nP).map (interp V (consList as ρ))
      = (List.range b.nP).reverse.map (consList as ρ) :=
    map_paramBvarsAt_interp (nP := b.nP) (e := 0) (ρp := consList as ρ) (σ := consList as ρ)
      (fun _ => rfl)
  have hrng : (List.range b.nP).reverse.map (consList as ρ) = as := by
    rw [← hlenAs]; exact range_reverse_map_consList as ρ
  rw [targetRead_of_mem ht, interp_mkAppN_foldl, hpar, hrng, hName, hleafM t _ ht hft,
    ← List.foldl_append]
  unfold mutMemberLeaf
  rw [interp_closed (V := V) (tupleLfpAV_below h.blockOk b.ownOffset
      ((h.FD _ _ hft).below ψ) ((h.FD _ _ hft).len ψ) ψ) _ ρ]
  -- the leaf law at the member, then Bekić
  have hsp_t : SpineFit ρ (((ppsF t ψ).take b.nP).map (·.2.2)) as :=
    spineFit_of_frames (by
        show (((ppsF 0 ψ).take b.nP).map (·.2.2)).length = _
        simp only [List.length_map, List.length_take, (h.FD 0 f₀ h.first).len ψ,
          (h.FD _ _ hft).len ψ]
        omega)
      (fun ρ' => (h.frame t _ hft ψ ρ').symm) hsp
  have hnI : ((ppsF t ψ).drop b.nP).length = (fms.getD t default).nIdx := by
    rw [List.length_drop, (h.FD _ _ hft).len ψ]
    exact Nat.add_sub_cancel_left _ _
  have htk : t < p.k + pinsS.length := by omega
  rw [← hnI,
    show mutRss ctorsA.length (mutKsOf kinds) = blkRss ctorsA kinds from rfl,
    show mutFss0 b.nP ctorsA.length dsF (mutKsOf kinds) (mutNFOf ctorsA) ψ
      = blkFss0 b ctorsA kinds dsF ψ from rfl, hbk]
  rw [tupleLfpAV_fold htk hOk' rfl hsp_t his, nestedU_mem ht]
  exact congrArg (fun X => SetTheory.app X (tupW (W ψ) is)) (ofNested_lfp hOk' ht)

/-- The pin's index telescope is the container member's at the pin's
level assignment (`NestedPinGroup.pinIds` at the syntactic group). -/
theorem NestedPinGroupSyn.pinIds {st : ElimState} {m : EnvModel V env₂} {q₀ kJ : Nat}
    {dJ : BlockModel V} (S : PGS st m q₀ kJ dJ) {i : Nat} (hi : i < kJ) (ψ : Name → Nat) :
    ((D).pinAt (q₀ + i)).Ids ψ = dJ.IdsM i (((D).pinAt (q₀ + i)).ψJ ψ) := by
  unfold PinSyn.Ids
  rw [S.pinPps i hi, S.pinNP i hi]
  rfl

/-- **A PIN target reads as its container's least tuple**: at a spine
fitting the pin's index telescope at the pin's frame, the container's
least tuple at the pin's frame (at the block's sort, the container's —
`w`), at the group's member, at the spine's tuple (the pin's index
universe, the container's — `pinU`), is the pin's stored reading (the
container at the components, `dJ.leaf` at the components' fit `DsFit`)
applied to the spine.  The `hZ` of `copyEntryAt_of_read` at a pin
target, with `P q` the container's least tuple. -/
theorem pinTarget_reads {st : ElimState} (m : EnvModel V env₂) {q₀ kJ i : Nat} {dJ : BlockModel V}
    (S : PGS st m q₀ kJ dJ) (hi : i < kJ)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {is : List V}
    (his : SpineFit (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)
      (((D).pinAt (q₀ + i)).Ids ψ) is) :
    SetTheory.app
        (lfpTuple (f₀.s.eval ψ) dJ.k
          (dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
          (dJ.Φ (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
        (tupW (nestedU p.k W pinsS ψ (p.k + (q₀ + i))) is)
      = is.foldl SetTheory.app
          (interp V ρp (targetRead m.acval (D).memberNames pinsS b.nP p.k ψ (p.k + (q₀ + i)))) := by
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i hi
  obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
  have hnlt : ¬ p.k + (q₀ + i) < p.k := by omega
  have hpin : pinsS.getD (q₀ + i) default = (D).pinAt (q₀ + i) := rfl
  rw [targetRead_of_pin hnlt, Nat.add_sub_cancel_left, hpin, interp_mkAppN_foldl,
    ← List.foldl_append]
  rw [S.pinIds hi ψ] at his
  have hleaf := hI.leaf (((D).pinAt (q₀ + i)).ψJ ψ) (consList as ρ) _ is
    (S.DsFit i hi ψ ρ as hsp) his
  rw [← S.w i hi ψ, hleaf]
  unfold BlockModel.tup
  rw [nestedU_pin]
  exact congrArg _ (congrArg (fun u => tupW u is) (S.pinU i hi ψ i hi))

/-! ## The global entry theorem: (i) the containers' least tuples are a fixed point of the pins' section, (ii) the auxiliary carrier's pins lie below them -/

/-- **A pin group with its identities and shapes** (task #315 L-E): the
syntactic group (`NestedPinGroupSyn`), the index-telescope identity
(`nestedPinsIdx`) and the copies' shapes (lane L-B's `NestedPinsShape`)
— what the global entry theorem reads of a group; the model is NAMED
by the consumer (`dJf` at the group's base pin). -/
structure GroupFacts (st : ElimState) (m : EnvModel V env₂) (q₀ kJ : Nat) (dJ : BlockModel V) :
    Prop where
  syn : PGS st m q₀ kJ dJ
  idx : ∀ i, i < kJ → ∀ (ψ : Name → Nat) (i' : Nat), i' < kJ →
    blockIds b.nP ppsF ψ (p.k + q₀ + i')
      = instTele (((D).pinAt (q₀ + i)).Ds ψ) 0 (dJ.IdsM i' (((D).pinAt (q₀ + i)).ψJ ψ))
  shape : ∀ i, i < kJ → ∀ (cvT : ConstantVal) (caps : IndCaps),
    env₂.find? ((D).pinAt (q₀ + i)).J = some (.indInfo cvT caps) →
    ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
    ∀ i' j, i' < kJ → j < (dJ.ctorsM i').length →
    CopyShapeA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
      (pins := pinsS) (offs := b.ownOffset) (memberNames := (fms.take p.k).map (·.cvTa.name))
      (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
      (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
      (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
      m.acval dJ (((D).pinAt (q₀ + i)).ψJ ψ) (((D).pinAt (q₀ + i)).Ds ψ)
      ((D).pinAt (q₀ + i)).DsE cvT.levelParams ((D).pinAt (q₀ + i)).lvls q₀ kJ i' j

/-- **The containers' least tuples at the pins**, `P` (task #315 L-E,
DESIGN §U.36 (c)): pin `q`'s container's least tuple at the pin's
frame — at the block model `dJf` of the pin's mint group's BASE pin,
at the member `q - grpBase` — at the block's sort. -/
noncomputable def pinLfp (st : ElimState) (pinsS : List PinSyn) (dJf : Nat → BlockModel V)
    (w : Nat) (ψ : Name → Nat) (ρp : Nat → V) (q : Nat) : V :=
  lfpTuple w (dJf (st.pins.getD q default).grpBase).k
    ((dJf (st.pins.getD q default).grpBase).idx ((pinsS.getD q default).ψJ ψ)
      (consList (((pinsS.getD q default).Ds ψ).map (interp V ρp)) ρp))
    ((dJf (st.pins.getD q default).grpBase).Φ ((pinsS.getD q default).ψJ ψ)
      (consList (((pinsS.getD q default).Ds ψ).map (interp V ρp)) ρp))
    (q - (st.pins.getD q default).grpBase)

local notation "GF" => GroupFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

local notation "ΨA" => nestedΨ (V := V) b.nP p.k f₀.s ppsF W pinsS b.ownOffset
  (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
  (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
  (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
  (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)

local notation "TVA" => nestedTV (V := V) b.nP p.k f₀.s ppsF W pinsS

/-- **A fit at a container's own pin's frame is a fit at the
corresponding block pin's frame** (task #315 L-E, step (i)): the two
frames carry the SAME components' values — the container's pin's
components read at the pin's frame, the block pin's at the block's
frame (`PinCorr`'s `Ds`, `interp_instAll`) — over different bases
(`ρJ` vs `ρp`), and the index telescope (the block pin's container
member's, `pinIds`) has its variables below the parameters
(`FormerData.below`), so the base is invisible (`spineFit_congr_below`). -/
theorem nestedPinFrame_transport (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} {q₀ i qK TG : Nat}
    (hkle : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).k ≤ TG)
    (hklt : TG < (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).k
      + (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).n)
    (hDs : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ds TG
      = (((dJf q₀).pinAt qK).Ds (((D).pinAt (q₀ + i)).ψJ ψ)).map
          (AnnotTerm.instAll (((D).pinAt (q₀ + i)).Ds ψ) 0))
    (hIds : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids TG
      = ((dJf q₀).pinAt qK).Ids (((D).pinAt (q₀ + i)).ψJ ψ)) :
    ∀ is : List V,
      SpineFit ((dJf q₀).pinFrame qK (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        (((dJf q₀).pinAt qK).Ids (((D).pinAt (q₀ + i)).ψJ ψ)) is →
      SpineFit ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).frame ρp TG)
        ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids TG) is := by
  intro is hfit
  have hklt' : TG < p.k + pinsS.length := hklt
  have hkle' : p.k ≤ TG := hkle
  have hk : ¬ TG < p.k := by omega
  · have hq' : TG - p.k < pinsS.length := by omega
    obtain ⟨q₀', kJ', i', hq'e, hi', G'⟩ := hgroups _ hq'
    obtain ⟨cvT', caps', cvR', mI', rP', rules', -, hI', -⟩ := G'.syn.stored i' hi'
    -- the block pin's components read as the container's pin's at the pin's frame
    have hDsT : ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ds TG).map (interp V ρp)
        = (((dJf q₀).pinAt qK).Ds (((D).pinAt (q₀ + i)).ψJ ψ)).map
            (interp V (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) := by
      rw [hDs, List.map_map]
      refine List.map_congr_left fun Dc _ => ?_
      show interp V ρp (AnnotTerm.instAll _ 0 Dc) = _
      have := interp_instAll (((D).pinAt (q₀ + i)).Ds ψ) [] ρp Dc
      simpa using this
    -- the block pin's index telescope is its container member's
    have hIdsT : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids TG
        = (((dJf q₀').ppsM i' (((D).pinAt (q₀' + i')).ψJ ψ)).drop (dJf q₀').nP).map (·.2.2) := by
      rw [show (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids TG
        = ((D).pinAt (TG - p.k)).Ids ψ from if_neg hk, hq'e, G'.syn.pinIds hi' ψ]
      rfl
    have hlenT : (((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ds TG).map (interp V ρp)).length
        = (dJf q₀').nP := by
      show ((((D).pinAt (TG - p.k)).Ds ψ).map (interp V ρp)).length = _
      rw [List.length_map, hq'e, G'.syn.pinDsLen i' hi' ψ]
    have hXlen : ((((dJf q₀).pinAt qK).Ds (((D).pinAt (q₀ + i)).ψJ ψ)).map
        (interp V (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))).length
        = (dJf q₀').nP := by rw [← hDsT]; exact hlenT
    have hbelow : DomsBelow (dJf q₀').nP
        (((dJf q₀').ppsM i' (((D).pinAt (q₀' + i')).ψJ ψ)).drop (dJf q₀').nP) := by
      have := DomsBelow.drop (dJf q₀').nP (hI'.former.below (((D).pinAt (q₀' + i')).ψJ ψ))
      simpa using this
    rw [TargetView.frame_of_pin _ _ hk, hIdsT, hDsT]
    rw [← hIds, hIdsT] at hfit
    refine spineFit_congr_below hbelow (fun n hn => ?_) hfit
    show consList _ (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) n = consList _ ρp n
    rw [consList_getD_lt _ _ n (by rw [hXlen]; exact hn), consList_getD_lt _ _ n (by rw [hXlen]; exact hn)]

/-- **Steps (i) and (ii) of the global entry theorem** (task #315 L-E,
DESIGN §U.36 (c)): at every parameter frame, with `P` the containers'
least tuples at the pins (`pinLfp`) and `L` the block's carrier,

* (i) `P` is a fixed point of the pins' section of the auxiliary
  operator at `L`: the auxiliary fibre at a copy is the container's
  fibre at its least tuple (`CopyCtorShape.fit_iff_at` at the tuple
  `segJoin k n L P`, whose entries are the targets' stored readings —
  `memberTarget_reads`, `pinTarget_reads` — through
  `copyEntryAt_of_read`/`copyEntryAt_of_pinCorr`), and the container's
  fibre at its least tuple is the least tuple (`app_lfpTuple_eq`);
* (ii) the auxiliary carrier's pin segment lies below `P`
  (`lfp_pins_le_of_section_closed`).

The groups carry their shapes (`GroupFacts`) at the model `dJf` of
each group's base pin — one model per group, so `P` at a group IS that
model's least tuple at every member. -/
theorem nestedPinsFixed (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp) :
    (∀ q, q < pinsS.length → ∀ t, t ∈ˢ (D).idx ψ ρp (p.k + q) →
      SetTheory.app
          (ΨA ψ ρp (segJoin p.k pinsS.length
              (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp))
              (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp)) (p.k + q)) t
        = SetTheory.app (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q) t) ∧
    (∀ q, q < pinsS.length →
      FamLe ((D).idx ψ ρp (p.k + q))
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q))
        (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q)) := by
  have hlenA : ctorsA.length = b.ctors.length := h.lenA
  -- the pins' index telescopes at the squash regime are bounded
  have hbound : ∀ q, q < pinsS.length → ((D).pinAt q).u ψ = 0 →
      FieldsBound 0 ρp (blockIds b.nP ppsF ψ (p.k + q)) := by
    intro q hq hz
    obtain ⟨q₀, kJ, i, rfl, hi, G⟩ := hgroups q hq
    obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := G.syn.stored i hi
    obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
    have hDsFit := G.syn.DsFit i hi ψ ρ as hsp
    have hJ := (hI.idxOk _ _ ((dJf q₀).satOfSpine hDsFit) i (G.syn.kEq ▸ hi)).2
    rw [← G.syn.pinU i hi ψ i hi, hz] at hJ
    rw [← Nat.add_assoc, G.idx i hi ψ i hi]
    have := (fieldsBound_instTele 0 (((D).pinAt (q₀ + i)).Ds ψ) (consList as ρ)
      ((dJf q₀).IdsM i (((D).pinAt (q₀ + i)).ψJ ψ)) []).mpr (by simpa only [consList_nil] using hJ)
    simpa only [consList_nil, List.length_nil] using this
  have hOk := nestedLfpOk_of_formers h hμ hbk ψ ρp hρp hbound
  have hS := nestedShape_of_formers h hbk ψ
  have hΨ := nestedΨ_functor hOk
  -- the per-group readers
  have hw : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      (dJf q₀).w (((D).pinAt (q₀ + i)).ψJ ψ) = f₀.s.eval ψ :=
    fun q₀ kJ G i hi => G.syn.w i hi ψ
  have hρJ : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Sat V ((dJf q₀).params (((D).pinAt (q₀ + i)).ψJ ψ)).reverse
        (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) := by
    intro q₀ kJ G i hi
    obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
    exact (dJf q₀).satOfSpine (G.syn.DsFit i hi ψ ρ as hsp)
  have hPinIdx : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      (D).idx ψ ρp (p.k + q₀ + i)
        = (dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) i := by
    intro q₀ kJ G i hi
    show idxSet (nestedU p.k W pinsS ψ (p.k + q₀ + i)) ρp (blockIds b.nP ppsF ψ (p.k + q₀ + i)) = _
    rw [Nat.add_assoc, nestedU_pin]
    change idxSet (((D).pinAt (q₀ + i)).u ψ) ρp (blockIds b.nP ppsF ψ (p.k + (q₀ + i))) = _
    rw [G.syn.pinU i hi ψ i hi, ← Nat.add_assoc, G.idx i hi ψ i hi, idxSet_instTele Iff.rfl]
    rfl
  have hP_group : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp (q₀ + i)
        = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
            ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
              (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
            ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
              (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i := by
    intro q₀ kJ G i hi
    unfold pinLfp
    rw [(G.syn.grp i hi).1, Nat.add_sub_cancel_left]
    rfl
  -- `P` is in the pins' space
  have hPmem : InTupleSpace (f₀.s.eval ψ) pinsS.length (fun q => (D).idx ψ ρp (p.k + q))
      (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp) := by
    intro q hq
    obtain ⟨q₀, kJ, i, rfl, hi, G⟩ := hgroups q hq
    show pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp (q₀ + i) ∈ˢ famSpace (f₀.s.eval ψ) ((D).idx ψ ρp (p.k + (q₀ + i)))
    rw [hP_group q₀ kJ G i hi, ← Nat.add_assoc, hPinIdx q₀ kJ G i hi]
    exact lfpTuple_mem _ _ _ _ i (G.syn.kEq ▸ hi)
  have hLmem : InTupleSpace (f₀.s.eval ψ) p.k ((D).idx ψ ρp)
      (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp)) := lfpTuple_mem _ _ _ _
  have hL'mem : InTupleSpace (f₀.s.eval ψ) (p.k + pinsS.length) ((D).idx ψ ρp)
      (segJoin p.k pinsS.length (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp))
        (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp)) :=
    inTupleSpace_join hLmem hPmem
  -- the targets of the joined tuple read as the stored readings
  have hZmem : ∀ t, t < p.k → ∀ is : List V, SpineFit ρp (blockIds b.nP ppsF ψ t) is →
      SetTheory.app (segJoin p.k pinsS.length (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp))
          (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp) t) (tupW (W ψ) is)
        = is.foldl SetTheory.app (interp V ρp (targetRead m.acval ((fms.take p.k).map (·.cvTa.name)) pinsS b.nP p.k ψ t)) := by
    intro t ht is his
    rw [segJoin_lt _ _ ht]
    exact memberTarget_reads h hbk m hleafM hρp hOk ht his
  have hZpin : ∀ q', q' < pinsS.length → ∀ is : List V,
      SpineFit (consList ((((D).pinAt q').Ds ψ).map (interp V ρp)) ρp) (((D).pinAt q').Ids ψ) is →
      SetTheory.app (segJoin p.k pinsS.length (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp))
          (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp) (p.k + q')) (tupW (nestedU p.k W pinsS ψ (p.k + q')) is)
        = is.foldl SetTheory.app
            (interp V ρp (targetRead m.acval ((fms.take p.k).map (·.cvTa.name)) pinsS b.nP p.k ψ (p.k + q'))) := by
    intro q' hq' is his
    rw [segJoin_add _ _ hq']
    obtain ⟨q₀, kJ, i, rfl, hi, G⟩ := hgroups q' hq'
    rw [hP_group q₀ kJ G i hi]
    exact pinTarget_reads m G.syn hi hρp his
  -- the readings at the block's targets, as the target view spells them
  have hZ : ∀ t, t < p.k + pinsS.length → ∀ is : List V,
      SpineFit ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).frame ρp t) ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids t) is →
      SetTheory.app (segJoin p.k pinsS.length (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp))
          (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp) t)
          (tupW ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).u t) is)
        = is.foldl SetTheory.app (interp V ρp ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).EA t)) := by
    intro t ht is his
    by_cases hk : t < p.k
    · rw [TargetView.frame_of_mem _ _ hk] at his
      have hIds : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids t = blockIds b.nP ppsF ψ t := if_pos hk
      rw [hIds] at his
      have hu : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).u t = W ψ := nestedU_mem hk
      rw [hu]
      exact hZmem t hk is his
    · have ht' : t = p.k + (t - p.k) := by omega
      have his' : SpineFit (consList ((((D).pinAt (t - p.k)).Ds ψ).map (interp V ρp)) ρp)
          (((D).pinAt (t - p.k)).Ids ψ) is := by
        rw [TargetView.frame_of_pin _ _ hk] at his
        have hIds : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids t
            = ((D).pinAt (t - p.k)).Ids ψ := if_neg hk
        rw [hIds] at his
        exact his
      rw [ht']
      exact hZpin (t - p.k) (by omega) is his'
  -- the entries at the joined tuple, for every copy
  have hent : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ → ∀ j, j < ((dJf q₀).ctorsM i).length →
      CopyEntryOut (dJf q₀) (((D).pinAt (q₀ + i)).ψJ ψ) (((D).pinAt (q₀ + i)).Ds ψ)
        (fun l => ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0)
        ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) [])
        ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []) ρp i j
        (p.k + q₀) kJ ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) [])
        ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i) + j) []) (f₀.s.eval ψ)
        (nestedU p.k W pinsS ψ)
        (segJoin p.k pinsS.length (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp))
          (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp)) := by
    intro q₀ kJ G i hi j hj l hl hrs hout
    obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, -⟩ := G.syn.stored i hi
    have hsh := G.shape i hi cvT caps hfind ψ ρp hρp i j hi hj
    unfold CopyShapeA at hsh
    have hjl : (((dJf q₀).ctorsM i))[j]? = some (((dJf q₀).ctorsM i).getD j default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have hlenF := hI.Fss_length hjl (((D).pinAt (q₀ + i)).ψJ ψ)
    have hks : ((dJf q₀).ksF i j).length = (((dJf q₀).Fss i (((D).pinAt (q₀ + i)).ψJ ψ)).getD j []).length := by
      rw [(hI.ctorData hjl).ksLen, hlenF]
    have hlF : l < (((dJf q₀).Fss i (((D).pinAt (q₀ + i)).ψJ ψ)).getD j []).length := by
      rw [← hsh.len]; exact hl
    by_cases hr : (((dJf q₀).rss i).getD j []).getD l false = true
    · rcases hI.tgt_cases hj (hks ▸ hlF) with htgt | ⟨hnt, -⟩
      · obtain ⟨-, htg, -, -⟩ := hsh.recF l hlF hr htgt
        have hk := G.syn.kEq
        have hin : p.k + q₀ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0 ∧
            ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0 < p.k + q₀ + kJ :=
          ⟨by rw [htg]; omega, by rw [htg]; omega⟩
        exact absurd hin hout
      · obtain ⟨-, -, hkle, hklt, hcorr, htl, hEis⟩ := hsh.pinF l hlF hr hnt
        refine copyEntryAt_of_pinCorr (TV := TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ) G.syn.reps
          (G.syn.typed _) (G.syn.pinsTyped _) (G.syn.kEq ▸ hi) hjl (hρJ q₀ kJ G i hi)
          (hw q₀ kJ G i hi) hlF hr hnt hcorr htl hEis ?_ (hZ _ hklt)
        -- the fit at the container's pin frame is a fit at the block pin's
        exact nestedPinFrame_transport dJf hgroups hkle hklt hcorr.2.1 hcorr.2.2.2.1
    · have hr' : (((dJf q₀).rss i).getD j []).getD l false = false := by simpa using hr
      rcases hsh.ordF l hlF hr' with ⟨hrC, -⟩ | ⟨-, -, hklt, hread⟩
      · rw [hrC] at hrs; exact absurd hrs Bool.false_ne_true
      · exact copyEntryAt_of_read hread (hZ _ hklt)
  -- (i): the fibres agree at every pin
  have hfix : ∀ q, q < pinsS.length → ∀ t, t ∈ˢ (D).idx ψ ρp (p.k + q) →
      SetTheory.app
          (ΨA ψ ρp (segJoin p.k pinsS.length
              (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp))
              (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp)) (p.k + q)) t
        = SetTheory.app (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q) t := by
    intro q hq t ht
    obtain ⟨q₀, kJ, i, rfl, hi, G⟩ := hgroups q hq
    obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, -⟩ := G.syn.stored i hi
    have hi' : i < (dJf q₀).k := G.syn.kEq ▸ hi
    rw [← Nat.add_assoc] at ht ⊢
    rw [hP_group q₀ kJ G i hi]
    have ht' : t ∈ˢ (dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
        (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) i := by
      rw [← hPinIdx q₀ kJ G i hi]; exact ht
    have hρJ' := hρJ q₀ kJ G i hi
    have hw' := hw q₀ kJ G i hi
    -- the container's fibre at its least tuple is the least tuple
    have hF := hI.functor _ _ hρJ'
    rw [hw'] at hF
    rw [← app_lfpTuple_eq hF.2.2 hF.1 hF.2.1 hi' ht']
    have hLJmem : InTupleSpace ((dJf q₀).w (((D).pinAt (q₀ + i)).ψJ ψ)) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        (lfpTuple (f₀.s.eval ψ) (dJf q₀).k
          ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
          ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))) := by
      rw [hw']; exact lfpTuple_mem _ _ _ _
    have hfibR := fun x => hI.fibre _ _ hρJ' _ hLJmem i hi' t ht' x
    -- the joined tuple's group segment is the container's least tuple
    have hseg : ∀ i', i' < kJ →
        segJoin p.k pinsS.length (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp))
            (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp) (p.k + q₀ + i')
          = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
              ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
                (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
              ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
                (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i' := by
      intro i' hi'
      have hseg0 := G.syn.seg
      rw [Nat.add_assoc, segJoin_add _ _ (by omega : q₀ + i' < pinsS.length),
        hP_group q₀ kJ G i' hi', G.syn.ψJEq i' i hi' hi ψ, G.syn.sameDs i' hi' ψ,
        ← G.syn.sameDs i hi ψ]
    have hnI : (blockIds b.nP ppsF ψ (p.k + q₀ + i)).length
        = ((dJf q₀).IdsM i (((D).pinAt (q₀ + i)).ψJ ψ)).length := by
      rw [G.idx i hi ψ i hi, instTele_length]
    have hu : ∀ i', i' < kJ →
        (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).u (p.k + q₀ + i')
          = (dJf q₀).uM i' (((D).pinAt (q₀ + i)).ψJ ψ) := by
      intro i' hi'
      show nestedU p.k W pinsS ψ (p.k + q₀ + i') = _
      rw [Nat.add_assoc, nestedU_pin]
      exact G.syn.pinU i hi ψ i' hi'
    have hgrp := fun j => ownCtors_grp (kinds := kinds) (dsF := dsF) h3 hlenA ψ (G.syn.ctorCount i hi) j
    -- the fits at the joined tuple against the container's
    have hbridge : ∀ j, j < ((dJf q₀).ctorsM i).length → ∀ fs : List V,
        (FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i) + j) [])
            (fun i' ρ => slotSet (f₀.s.eval ψ)
              (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (p.k + q₀ + i) + j) []).getD i' 0)) ρ
              (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD i' [])
              (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD i' [])
              (segJoin p.k pinsS.length (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp))
                (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp)
                (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                  (b.ownOffset (p.k + q₀ + i) + j) []).getD i' 0)))
            0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []) fs ∧
          (∀ l, l < (blockIds b.nP ppsF ψ (p.k + q₀ + i)).length →
            interp V (consList fs ρp)
                (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD l default)
              = projS l t))
        ↔ (dJf q₀).ChainFit (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)
            (lfpTuple (f₀.s.eval ψ) (dJf q₀).k
              ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
                (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
              ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
                (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))) t i j fs := by
      intro j hj fs
      have hj' : ((dJf q₀).ctorsM i)[j]? = some (((dJf q₀).ctorsM i).getD j default) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      have hsh := G.shape i hi cvT caps hfind ψ ρp hρp i j hi hj
      unfold CopyShapeA at hsh
      have hfit := CopyCtorShape.fit_iff_at (TV := TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ)
        G.syn.reps (G.syn.typed _) (G.syn.pinsTyped _) hi' G.syn.kEq hw' hu hρJ' hnI hj'
        hsh (hent q₀ kJ G i hi j hj) t fs
      refine Iff.trans (and_congr ?_ Iff.rfl) hfit
      refine (FitsFrom.congr_slot fun l hl => ?_).symm
      simp only [Nat.zero_add]
      by_cases hin : p.k + q₀ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0 ∧
          ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0 < p.k + q₀ + kJ
      · rw [segJoin_in _ _ hin]
        have := hseg (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0 - (p.k + q₀)) (by omega)
        rw [Nat.add_sub_cancel' hin.1] at this
        rw [this]
        rfl
      · rw [segJoin_out _ _ hin]
        rfl
    refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨j, fs, h1, h2, h3, h4, rfl⟩ := (tupleLfpΦ_fibre hOk hS hL'mem (by omega) ht _).mp hx
      have hj := (hgrp j).mp ⟨h1, h2⟩
      exact (hfibR _).mpr ⟨j, fs, hj, (hbridge j hj fs).mp ⟨h3, h4⟩, by rw [G.syn.inj, hw']⟩
    · obtain ⟨j, fs, hj, hC, rfl⟩ := (hfibR x).mp hx
      obtain ⟨h1, h2⟩ := (hgrp j).mpr hj
      obtain ⟨h3, h4⟩ := (hbridge j hj fs).mpr hC
      rw [G.syn.inj, hw']
      exact (tupleLfpΦ_fibre hOk hS hL'mem (by omega) ht _).mpr ⟨j, fs, h1, h2, h3, h4, rfl⟩
  refine ⟨hfix, fun q hq => ?_⟩
  -- (ii): leastness of the pins' section at the carrier
  refine lfp_pins_le_of_section_closed hΨ.1 hΨ.2.2 hPmem (fun q' hq' t ht x hx => ?_) q hq
  show x ∈ˢ SetTheory.app (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q') t
  rw [← hfix q' hq' t ht]
  exact hx

/-! ## Step (iii), per group: the container's least tuple lies below the auxiliary carrier's segment, given the entries as inclusions -/

/-- **A group's least tuple lies below the auxiliary carrier's segment,
given the outside entries as INCLUSIONS** (task #315 L-E, step (iii)'s
per-group closure, DESIGN §U.39 (c)): with `X` the auxiliary carrier's
group segment — in the container's tuple space, below its least tuple
by (ii) — `X` is CLOSED under the container's operator when every
container fit at `X` is a copy fit at the auxiliary carrier
(`CopyCtorShape.fit_imp_le`: member targets read the segment, the
`ordF`-right entries `hentR` and the `pinF` entries at the container's
own pins' carriers AT `X` `hentP` are the callers' — the induction
hypothesis at a smaller pin, the container's own `PinRecLaws.ind` at
the cycle), so the least tuple lies below it (`lfpTuple_le`). -/
theorem nestedGroupLe_of_entries (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀)) {i : Nat} (hi : i < kJ)
    (hentR : ∀ i', i' < kJ → ∀ j, j < ((dJf q₀).ctorsM i').length →
      ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l false = true →
      (((dJf q₀).rss i').getD j []).getD l false = false →
      ¬ (p.k + q₀ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 ∧
          ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k + q₀ + kJ) →
      ∀ fs₁ : List V, fs₁.length = l →
        SpineFit (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)
          ((((dJf q₀).Fss i' (((D).pinAt (q₀ + i)).ψJ ψ)).getD j []).take l) fs₁ →
        interp V (consList fs₁ (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
            ((((dJf q₀).Fss i' (((D).pinAt (q₀ + i)).ψJ ψ)).getD j []).getD l default)
          ⊆ˢ slotSet (f₀.s.eval ψ)
              (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0))
              (consList fs₁ ρp)
              (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
              (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
              (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
                (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                  (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0)))
    (hentP : ∀ i', i' < kJ → ∀ j, j < ((dJf q₀).ctorsM i').length →
      ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).length →
      (((dJf q₀).rss i').getD j []).getD l false = true →
      ¬ (dJf q₀).tgts i' j l < (dJf q₀).k →
      ¬ (p.k + q₀ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 ∧
          ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k + q₀ + kJ) →
      ∀ fs₁ : List V, fs₁.length = l →
        SpineFit (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)
          ((((dJf q₀).Fss i' (((D).pinAt (q₀ + i)).ψJ ψ)).getD j []).take l) fs₁ →
        (dJf q₀).slotAt (((D).pinAt (q₀ + i)).ψJ ψ)
            (fun i'' => lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
              (p.k + q₀ + i''))
            i' j l (consList fs₁ (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
          ⊆ˢ slotSet (f₀.s.eval ψ)
              (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0))
              (consList fs₁ ρp)
              (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
              (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD l [])
              (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
                (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                  (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0))) :
    FamLe ((D).idx ψ ρp (p.k + q₀ + i)) (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp (q₀ + i))
      (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q₀ + i)) := by
  have hlenA : ctorsA.length = b.ctors.length := h.lenA
  -- (ii), the segment below the least tuples
  have hfix := (nestedPinsFixed hμ h h3 hbk m hleafM dJf hgroups hρp).2
  -- the block's fixed point
  have hbound : ∀ q, q < pinsS.length → ((D).pinAt q).u ψ = 0 →
      FieldsBound 0 ρp (blockIds b.nP ppsF ψ (p.k + q)) := by
    intro q hq hz
    obtain ⟨q₀', kJ', i', rfl, hi', G'⟩ := hgroups q hq
    obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := G'.syn.stored i' hi'
    obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
    have hDsFit := G'.syn.DsFit i' hi' ψ ρ as hsp
    have hJ := (hI.idxOk _ _ ((dJf q₀').satOfSpine hDsFit) i' (G'.syn.kEq ▸ hi')).2
    rw [← G'.syn.pinU i' hi' ψ i' hi', hz] at hJ
    rw [← Nat.add_assoc, G'.idx i' hi' ψ i' hi']
    have := (fieldsBound_instTele 0 (((D).pinAt (q₀' + i')).Ds ψ) (consList as ρ)
      ((dJf q₀').IdsM i' (((D).pinAt (q₀' + i')).ψJ ψ)) []).mpr (by simpa only [consList_nil] using hJ)
    simpa only [consList_nil, List.length_nil] using this
  have hOk := nestedLfpOk_of_formers h hμ hbk ψ ρp hρp hbound
  have hS := nestedShape_of_formers h hbk ψ
  have hΨ := nestedΨ_functor hOk
  have hLmem : InTupleSpace (f₀.s.eval ψ) (p.k + pinsS.length) ((D).idx ψ ρp)
      (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) := lfpTuple_mem _ _ _ _
  -- the group's data at pin `q₀ + i`
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, -⟩ := G.syn.stored i hi
  have hw' : (dJf q₀).w (((D).pinAt (q₀ + i)).ψJ ψ) = f₀.s.eval ψ := G.syn.w i hi ψ
  have hρJ' : Sat V ((dJf q₀).params (((D).pinAt (q₀ + i)).ψJ ψ)).reverse
      (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) := by
    obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
    exact (dJf q₀).satOfSpine (G.syn.DsFit i hi ψ ρ as hsp)
  have hPinIdx : ∀ i', i' < kJ →
      (D).idx ψ ρp (p.k + q₀ + i')
        = (dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) i' := by
    intro i' hi'
    show idxSet (nestedU p.k W pinsS ψ (p.k + q₀ + i')) ρp (blockIds b.nP ppsF ψ (p.k + q₀ + i')) = _
    rw [Nat.add_assoc, nestedU_pin]
    change idxSet (((D).pinAt (q₀ + i')).u ψ) ρp (blockIds b.nP ppsF ψ (p.k + (q₀ + i'))) = _
    rw [G.syn.pinU i hi ψ i' hi', ← Nat.add_assoc, G.idx i hi ψ i' hi', idxSet_instTele Iff.rfl]
    rfl
  have hP_group : ∀ i', i' < kJ →
      pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp (q₀ + i')
        = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
            ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
              (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
            ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
              (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i' := by
    intro i' hi'
    unfold pinLfp
    rw [(G.syn.grp i' hi').1, Nat.add_sub_cancel_left]
    change lfpTuple (f₀.s.eval ψ) (dJf q₀).k
      ((dJf q₀).idx (((D).pinAt (q₀ + i')).ψJ ψ)
        (consList ((((D).pinAt (q₀ + i')).Ds ψ).map (interp V ρp)) ρp))
      ((dJf q₀).Φ (((D).pinAt (q₀ + i')).ψJ ψ)
        (consList ((((D).pinAt (q₀ + i')).Ds ψ).map (interp V ρp)) ρp)) i' = _
    rw [G.syn.ψJEq i' i hi' hi ψ, G.syn.sameDs i' hi' ψ, ← G.syn.sameDs i hi ψ]
  have hseg0 := G.syn.seg
  have hk := G.syn.kEq
  -- the segment, in the container's tuple space and below its least tuple
  have hXs : InTupleSpace (f₀.s.eval ψ) (dJf q₀).k
      ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
        (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
      (fun i'' => lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
        (p.k + q₀ + i'')) := by
    intro i' hi'
    rw [← hPinIdx i' (G.syn.kEq ▸ hi')]
    exact hLmem _ (by omega)
  have hXle : TupleLe (dJf q₀).k
      ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
        (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
      (fun i'' => lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
        (p.k + q₀ + i''))
      (lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))) := by
    intro i' hi'
    have := hfix (q₀ + i') (by omega)
    rw [hP_group i' (G.syn.kEq ▸ hi'), ← Nat.add_assoc, hPinIdx i' (G.syn.kEq ▸ hi')] at this
    exact this
  have hnI : ∀ i', i' < kJ → (blockIds b.nP ppsF ψ (p.k + q₀ + i')).length
      = ((dJf q₀).IdsM i' (((D).pinAt (q₀ + i)).ψJ ψ)).length := by
    intro i' hi'
    rw [G.idx i hi ψ i' hi', instTele_length]
  have hu : ∀ i', i' < kJ →
      (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).u (p.k + q₀ + i')
        = (dJf q₀).uM i' (((D).pinAt (q₀ + i)).ψJ ψ) := by
    intro i' hi'
    show nestedU p.k W pinsS ψ (p.k + q₀ + i') = _
    rw [Nat.add_assoc, nestedU_pin]
    exact G.syn.pinU i hi ψ i' hi'
  -- the segment is closed under the container's operator
  have hclosed : IsClosedTuple (f₀.s.eval ψ) (dJf q₀).k
      ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
        (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
      ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
        (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
      (fun i'' => lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
        (p.k + q₀ + i'')) := by
    refine ⟨hXs, fun i' hi' t ht x hx => ?_⟩
    have hi'' : i' < kJ := G.syn.kEq ▸ hi'
    obtain ⟨cvT', caps', cvR', mI', rP', rules', -, hI', -⟩ := G.syn.stored i' hi''
    have hXs' : InTupleSpace ((dJf q₀).w (((D).pinAt (q₀ + i)).ψJ ψ)) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        (fun i'' => lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
          (p.k + q₀ + i'')) := by rw [hw']; exact hXs
    have ht' : t ∈ˢ (D).idx ψ ρp (p.k + q₀ + i') := by rw [hPinIdx i' hi'']; exact ht
    obtain ⟨j, fs, hj, hC, rfl⟩ := (hI'.fibre _ _ hρJ' _ hXs' i' hi' t ht x).mp hx
    have hj' : ((dJf q₀).ctorsM i')[j]? = some (((dJf q₀).ctorsM i').getD j default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have hsh := G.shape i hi cvT caps hfind ψ ρp hρp i' j hi'' hj
    unfold CopyShapeA at hsh
    obtain ⟨hf, heq⟩ := CopyCtorShape.fit_imp_le
      (TV := TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ) G.syn.reps (G.syn.typed _)
      (G.syn.pinsTyped _) hi' G.syn.kEq hw' hu hρJ' (hnI i' hi'') hXs hXle hj' hsh
      (hentR i' hi'' j hj) (hentP i' hi'' j hj) t fs hC
    -- the slots at the joined tuple are the auxiliary carrier's
    have hslot := (FitsFrom.congr_slot (rs := (blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i') + j) [])
      (slot' := fun i'' ρ => slotSet (f₀.s.eval ψ)
        (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i') + j) []).getD i'' 0)) ρ
        (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD i'' [])
        (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i') + j) []).getD i'' [])
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
          (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD i'' 0)))
      (fun l hl => ?_)).mp hf
    · have hgrp := (ownCtors_grp (kinds := kinds) (dsF := dsF) h3 hlenA ψ (G.syn.ctorCount i' hi'') j).mpr hj
      have hmem := (tupleLfpΦ_fibre hOk hS hLmem (by omega) ht'
          ((dJf q₀).inj (((D).pinAt (q₀ + i)).ψJ ψ) i' j fs)).mpr
        ⟨j, fs, hgrp.1, hgrp.2, hslot, heq, by rw [G.syn.inj, hw']⟩
      exact lfpTuple_closed hΨ.2.2 hΨ.1 _ (by omega) t ht' _ hmem
    · simp only [Nat.zero_add]
      by_cases hin : p.k + q₀ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 ∧
          ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i') + j) []).getD l 0 < p.k + q₀ + kJ
      · rw [segJoin_in _ _ hin, Nat.add_sub_cancel' hin.1]
        rfl
      · rw [segJoin_out _ _ hin]
        rfl
  -- leastness
  have hle := lfpTuple_le hclosed i (G.syn.kEq ▸ hi)
  rw [hP_group i hi, hPinIdx i hi]
  exact hle

end Assembly

end ConLeche.Model
