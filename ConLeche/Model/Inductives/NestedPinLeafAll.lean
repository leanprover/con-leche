module

public import ConLeche.Model.Inductives.NestedPinLaws
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
    {dJ : BlockModel V} {ψJ : Name → Nat} {Ds : List AnnotTerm} {tg : Nat → Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {ρp : Nat → V}
    {i j l : Nat}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hi : i < dJ.k) {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (hρJ : Sat V (dJ.params ψJ).reverse (consList (Ds.map (interp V ρp)) ρp))
    (hw : dJ.w ψJ = TV.w) (hl : l < ((dJ.Fss i ψJ).getD j []).length)
    (hr : ((dJ.rss i).getD j []).getD l false = true) (hnt : ¬ dJ.tgts i j l < dJ.k)
    (hcorr : PinCorr TV m.acval dJ ψJ Ds (tg l) (dJ.tgts i j l - dJ.k))
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
  obtain ⟨hEA, hDs, hu, hIds⟩ := hcorr
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
      ∃ (q₀ kJ i : Nat), q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ (B ci))
    (hcont : ∀ q, q < pinsS.length →
      ∃ ci : ContainerInfo, ConLeche.containerInfo? env₂ ((D).pinAt q).J = some ci) :
    PinShapes m B (D) PC := by
  intro q hq
  obtain ⟨ci, hci⟩ := hcont q hq
  obtain ⟨q₀, kJ, i, hqe, hi, G⟩ := hgroupsB q hq ci hci
  refine ⟨q₀, kJ, i, ci, hqe, hi, hci, ?_, ?_⟩
  · -- the group, viewed
    have h0 : q₀ + 0 = q₀ := Nat.add_zero q₀
    refine ⟨G.seg, G.kpos, G.kEq, fun i' hi' => ?_, G.same, fun i' hi' ψ => ?_, G.pinNP,
      G.pinNIdx, G.pinPps, fun ψ => ?_, fun ψ => ?_, fun ψ ρ as hsp => ?_⟩
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
    intro ψ ρp hρp i' j hi' hj
    have hsh := G.shape 0 G.kpos ψ ρp hρp i' hi' j hj
    rw [Nat.add_zero] at hsh
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
theorem memberTarget_reads (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PG m q₀ kJ dJ)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {t : Nat} (ht : t < p.k) {is : List V} (his : SpineFit ρp (blockIds b.nP ppsF ψ t) is) :
    SetTheory.app (lfpTuple ((D).w ψ) p.k ((D).idx ψ ρp) ((D).Φ ψ ρp) t) (tupW (W ψ) is)
      = is.foldl SetTheory.app
          (interp V ρp (targetRead m.acval (D).memberNames pinsS b.nP p.k ψ t)) := by
  have hkT : b.k = fms.length := h.lenFms.symm
  have hplen : ((D).params ψ).length = b.nP := by
    show (((ppsF 0 ψ).take b.nP).map (·.2.2)).length = b.nP
    rw [List.length_map, List.length_take, (h.FD 0 f₀ h.first).len ψ]
    omega
  have htl : t < fms.length := by rw [← hkT, hbk]; omega
  have hft := fms_get htl
  obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
  have hlenAs : as.length = b.nP := by rw [hsp.length_eq, hplen]
  have hOk' := nestedLfpOk_of_formers h hμ hbk ψ (consList as ρ) hρp
    (nestedPinBound_of m hgroups ψ _ hρp)
  -- the stored reading is the auxiliary leaf at the parameters
  have hName : (D).memberNames.getD t .anonymous = (fms.getD t default).cvTa.name := by
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

/-- **A PIN target reads as its container's least tuple**: at a spine
fitting the pin's index telescope at the pin's frame, the container's
least tuple at the pin's frame, at the group's member, at the spine's
tuple (the pin's index universe, the container's — `pinU`), is the
pin's stored reading (the container at the components, `dJ.leaf` at
the components' fit `DsFit`) applied to the spine.  The `hZ` of
`copyEntryAt_of_read` at a pin target, with `P q` the container's least
tuple. -/
theorem pinTarget_reads (m : EnvModel V env₂) {q₀ kJ i : Nat} {dJ : BlockModel V}
    (G : PG m q₀ kJ dJ) (hi : i < kJ)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {is : List V}
    (his : SpineFit (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)
      (((D).pinAt (q₀ + i)).Ids ψ) is) :
    SetTheory.app
        (lfpTuple (dJ.w (((D).pinAt (q₀ + i)).ψJ ψ)) dJ.k
          (dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
          (dJ.Φ (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
        (tupW (nestedU p.k W pinsS ψ (p.k + (q₀ + i))) is)
      = is.foldl SetTheory.app
          (interp V ρp (targetRead m.acval (D).memberNames pinsS b.nP p.k ψ (p.k + (q₀ + i)))) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := G.rep i hi
  obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
  have hnlt : ¬ p.k + (q₀ + i) < p.k := by omega
  have hpin : pinsS.getD (q₀ + i) default = (D).pinAt (q₀ + i) := rfl
  rw [targetRead_of_pin hnlt, Nat.add_sub_cancel_left, hpin, interp_mkAppN_foldl,
    ← List.foldl_append]
  rw [G.pinIds hi ψ] at his
  have hleaf := hI.leaf (((D).pinAt (q₀ + i)).ψJ ψ) (consList as ρ) _ is
    (G.DsFit i hi ψ ρ as hsp) his
  rw [hleaf]
  unfold BlockModel.tup
  rw [← Nat.add_assoc, nestedU_pin_group m G hi ψ i hi]

end Assembly

end ConLeche.Model
