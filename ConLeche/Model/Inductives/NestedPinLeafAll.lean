module

import ConLeche.Model.Inductives.NestedPinLaws
import ConLeche.Model.Inductives.NestedAux
import ConLeche.Model.Inductives.ContainerCross
public import ConLeche.Model.Inductives.NestedCopyIdx
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

/-- **A spine fits at two frames agreeing below the chain's bound**
(task #315 L-E, DESIGN §U.61): `teleOfFields_congr_below`'s `SpineFit`
twin — a field chain whose domains are bounded at their own depths
reads only the frame below the chain's bound, so a prefix fitting it at
one of the container instance transfer's two frames fits it at the
other. -/
theorem spineFit_congr_fields :
    ∀ {Fs : List AnnotTerm} {k : Nat} {ρ ρ' : Nat → V} {fs : List V},
      FieldsBelow k Fs → (∀ v, v < k → ρ v = ρ' v) → SpineFit ρ Fs fs → SpineFit ρ' Fs fs
  | [], _, _, _, [], _, _, h => h
  | [], _, _, _, _ :: _, _, _, h => h.elim
  | _ :: _, _, _, _, [], _, _, h => h.elim
  | F :: Fs, k, ρ, ρ', a :: fs, hb, hρ, h => by
    simp only [SpineFit] at h ⊢
    refine ⟨?_, ?_⟩
    · rw [← interp_congr_below V F k ρ ρ' hb.1 hρ]
      exact h.1
    · refine spineFit_congr_fields (k := k + 1) hb.2 (fun v hv => ?_) h.2
      match v with
      | 0 => rfl
      | v + 1 => exact hρ v (by omega)

/-- A field chain's entries are bounded at their own depths (the
`FieldsBelow` reader; `MutualFormersKit`'s twin is not re-exported to
this file). -/
theorem fieldsBelow_getD : ∀ {Fs : List AnnotTerm} {k : Nat} (l : Nat),
    FieldsBelow k Fs → l < Fs.length →
    ConLeche.Term.Term.bvarsBelow (k + l) (Fs.getD l default).erase
  | [], _, _, _, hl => by simp at hl
  | F :: Fs, k, 0, hb, _ => by simpa using hb.1
  | F :: Fs, k, l + 1, hb, hl => by
    have := fieldsBelow_getD (Fs := Fs) (k := k + 1) l hb.2 (by simp at hl ⊢; omega)
    simpa [show k + 1 + l = k + (l + 1) from by omega] using this

/-- A field chain's PREFIX is bounded where the chain is. -/
theorem fieldsBelow_take : ∀ {Fs : List AnnotTerm} {k : Nat} (l : Nat),
    FieldsBelow k Fs → FieldsBelow k (Fs.take l)
  | [], _, l, _ => by rw [List.take_nil]; trivial
  | _ :: _, _, 0, _ => by rw [List.take_zero]; trivial
  | F :: Fs, k, l + 1, hb => by
    rw [List.take_succ_cons]
    exact ⟨hb.1, fieldsBelow_take l hb.2⟩

/-- **A container's constructor's field domains are bounded at their own
depths over the parameters** (`CtorDataI.below` at the dropped
telescope). -/
theorem IsBlockModel.Fss_below {m : EnvModel V env} {d : BlockModel V}
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {mm : Nat}
    (h : IsBlockModel m T cvT cvR mI rP rules d mm) {j : Nat} {cA : ConstantVal × Nat}
    (hj : (d.ctorsM mm)[j]? = some cA) (ψ : Name → Nat) :
    FieldsBelow d.nP ((d.Fss mm ψ).getD j []) := by
  rw [IsBlockModel.Fss_getD hj]
  have := (DomsBelow.drop (k := 0) d.nP ((h.ctorData hj).below ψ)).fields
  simpa using this

/-- **A container's constructor fit at TWO level assignments and TWO
frames** (task #315 L-E, DESIGN §U.51: the gap between the container
instance transfer's two halves): the container instance transfer reads
one container `dK`'s member `i`, constructor `j` twice — once as the
outer container's own copy of a pin, at its pin frame and level
assignment, once as the BLOCK's copy of the image pin, at the block's —
and the two agree because the level assignments agree on the
constructor's level parameters (`targetPin_corr`, `ContainerModeled.pinψ`)
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

/-- **A container's recursive SLOT at one field, at TWO level
assignments and TWO frames** (task #315 L-E, DESIGN §U.61):
`chainFitT_congr_mem`'s recursive branch, extracted — the constructor's
data are one datum (`IsBlockModel.ctor_params`), the telescope's
domains and the index expressions read only below the field's depth
(`CtorDataI.tssBelow`/`eissBelow`), so `slotSet_congr_below` carries
the slot across. -/
theorem BlockModel.slotAtT_congr_mem {m : EnvModel V env} {dK : BlockModel V}
    {pc : Nat → PinCtors V} {ψ₁ ψ₂ : Name → Nat} {ρ₁ ρ₂ : Nat → V} {Y : Nat → V} {i j : Nat}
    (hreps : IsBlockModels m dK) (hi : i < dK.k)
    {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hψ : ∀ p ∈ cA.1.levelParams, ψ₁ p = ψ₂ p)
    (hw : dK.w ψ₁ = dK.w ψ₂)
    (hu : ∀ l, dK.uT (dK.tgts i j l) ψ₁ = dK.uT (dK.tgts i j l) ψ₂)
    (hρ : ∀ v, v < dK.nP → ρ₁ v = ρ₂ v) (fs₁ : List V) :
    dK.slotAtT pc ψ₁ Y i j fs₁.length (consList fs₁ ρ₁)
      = dK.slotAtT pc ψ₂ Y i j fs₁.length (consList fs₁ ρ₂) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  obtain ⟨-, hE, htl, -⟩ := hI.ctor_params hj hψ
  have hcd := hI.ctorData hj
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

/-- **A container's field DOMAIN at TWO level assignments and TWO
frames** (task #315 L-E, DESIGN §U.61): the domain lists are one
(`ctor_params`) and each domain reads only below its own depth
(`Fss_below`). -/
theorem IsBlockModel.dom_congr_mem {m : EnvModel V env} {dK : BlockModel V}
    {ψ₁ ψ₂ : Name → Nat} {ρ₁ ρ₂ : Nat → V} {i j : Nat}
    (hreps : IsBlockModels m dK) (hi : i < dK.k)
    {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hψ : ∀ p ∈ cA.1.levelParams, ψ₁ p = ψ₂ p)
    (hρ : ∀ v, v < dK.nP → ρ₁ v = ρ₂ v) (fs₁ : List V)
    (hl : fs₁.length < ((dK.Fss i ψ₂).getD j []).length) :
    interp V (consList fs₁ ρ₁) (((dK.Fss i ψ₁).getD j []).getD fs₁.length default)
      = interp V (consList fs₁ ρ₂) (((dK.Fss i ψ₂).getD j []).getD fs₁.length default) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  obtain ⟨hF, -, -, -⟩ := hI.ctor_params hj hψ
  rw [hF]
  exact interp_congr_below V _ (dK.nP + fs₁.length) _ _
    (fieldsBelow_getD _ (hI.Fss_below hj ψ₂) hl)
    (fun v hv => consList_agree_above hρ fs₁ v (by omega))

/-- **The container's slots' BOUND travels between the frames** (task
#315 L-E, DESIGN §U.54 (b), §U.61): the `_dom` premise of
`fit_iff_at_T_dom`/`fit_imp_T_le_dom` — the container's recursive slot
at a field is within the field's real domain — at one level assignment
and frame gives it at the other, over the SAME tuple `Y`.  This is what
makes the container instance transfer's two halves composable: the
container's tuple space and extended carrier do NOT travel (they are
stated at one frame), its slots' bound does. -/
theorem BlockModel.slotDom_congr_mem {m : EnvModel V env} {dK : BlockModel V}
    {pc : Nat → PinCtors V} {ψ₁ ψ₂ : Name → Nat} {ρ₁ ρ₂ : Nat → V} {Y : Nat → V} {i j : Nat}
    (hreps : IsBlockModels m dK) (hi : i < dK.k)
    {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hψ : ∀ p ∈ cA.1.levelParams, ψ₁ p = ψ₂ p)
    (hw : dK.w ψ₁ = dK.w ψ₂)
    (hu : ∀ l, dK.uT (dK.tgts i j l) ψ₁ = dK.uT (dK.tgts i j l) ψ₂)
    (hρ : ∀ v, v < dK.nP → ρ₁ v = ρ₂ v)
    (hdom : ∀ l, l < ((dK.Fss i ψ₁).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρ₁ (((dK.Fss i ψ₁).getD j []).take l) fs₁ →
      dK.slotAtT pc ψ₁ Y i j l (consList fs₁ ρ₁)
        ⊆ˢ interp V (consList fs₁ ρ₁) (((dK.Fss i ψ₁).getD j []).getD l default)) :
    ∀ l, l < ((dK.Fss i ψ₂).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρ₂ (((dK.Fss i ψ₂).getD j []).take l) fs₁ →
      dK.slotAtT pc ψ₂ Y i j l (consList fs₁ ρ₂)
        ⊆ˢ interp V (consList fs₁ ρ₂) (((dK.Fss i ψ₂).getD j []).getD l default) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  obtain ⟨hF, -, -, -⟩ := hI.ctor_params hj hψ
  intro l hl hr fs₁ hlen hsp
  subst hlen
  have hsp₁ : SpineFit ρ₁ (((dK.Fss i ψ₁).getD j []).take fs₁.length) fs₁ := by
    rw [hF]
    exact spineFit_congr_fields (fieldsBelow_take _ (hI.Fss_below hj ψ₂))
      (fun v hv => (hρ v hv).symm) hsp
  have hkey := hdom fs₁.length (by rw [hF]; exact hl) hr fs₁ rfl hsp₁
  rw [BlockModel.slotAtT_congr_mem hreps hi hj hψ hw hu hρ fs₁,
    IsBlockModel.dom_congr_mem hreps hi hj hψ hρ fs₁ hl] at hkey
  exact hkey

/-! ## A family is determined by its LEAF -/

/-- **Two families with ONE leaf are one family** (task #315 L-E, DESIGN
§U.58): over one index set, if each family's fibre at every fitting
index spine is one stored reading applied to that spine, the families
are equal.  Every index tuple IS such a spine's (`mem_idxSet_elim`),
so the leaf laws determine the family.

This is what identifies a container instance's ROOT class with the
block pin it corresponds to (`ClassPin`): the root's member class has
`IsBlockModel.leaf`, its pin class has `IsBlockModel.pinLeaf`, the
block's pin has the leaf of ITS container's model, and all three are
the SAME stored reading at the same values — `acval` at agreeing level
assignments (`EnvModel.acval_params`), applied to the components'
values, which `ClassPin.frame` makes one.  No congruence of the
abstract `Φ` or `pinCar` in the frame is needed. -/
theorem fam_eq_of_leaf {w' u : Nat} {ρ₁ ρ₂ : Nat → V} {Ids : List AnnotTerm} {A F₁ F₂ : V}
    (hsp : ∀ is : List V, SpineFit ρ₁ Ids is → SpineFit ρ₂ Ids is)
    (hidx : idxSet u ρ₁ Ids = idxSet u ρ₂ Ids)
    (h₁ : F₁ ∈ˢ famSpace w' (idxSet u ρ₁ Ids)) (h₂ : F₂ ∈ˢ famSpace w' (idxSet u ρ₂ Ids))
    (hl₁ : ∀ is : List V, SpineFit ρ₁ Ids is →
      SetTheory.app F₁ (tupW u is) = is.foldl SetTheory.app A)
    (hl₂ : ∀ is : List V, SpineFit ρ₂ Ids is →
      SetTheory.app F₂ (tupW u is) = is.foldl SetTheory.app A) :
    F₁ = F₂ := by
  refine famSpace_ext h₁ (hidx ▸ h₂) fun t ht => ?_
  obtain ⟨is, hfit, rfl⟩ := mem_idxSet_elim ht
  rw [hl₁ is hfit, hl₂ is (hsp is hfit)]

/-- **The container's slots at a tuple BELOW its extended carrier are
within its real domains** (task #315 L-E, DESIGN §U.65): the `_dom`
premise of `fit_iff_at_T_dom`/`fit_imp_T_le_dom`, from the tuple's
place in the container's tuple space — `slotAtT_mono` up to the
extended carrier, at which the container's slot IS the field's real
domain (`IsBlockModels.real_dom_eq`, DESIGN §U.18 (e)'s `pinFix`).
`fit_imp_T_le` had this inline; the container instance transfer needs
it on its own, because `copyTransfer_mem`/`copyTransfer_via` take the
bound as a premise (the tuple space does not travel between the two
readings, §U.54 (b)). -/
theorem BlockModel.slotDomT_of_le {env : Env} {m : EnvModel V env} {dK : BlockModel V}
    {pc : Nat → PinCtors V} {ψ : Name → Nat} {ρ : Nat → V} {T : Nat → V} {i j : Nat}
    (hreps : IsBlockModels m dK) (hfT : FormersTyped m dK ψ) (hPT : PinsTyped m dK ψ)
    (hi : i < dK.k) {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hρ : Sat V (dK.params ψ).reverse ρ)
    (hTs : InTupleSpace (dK.w ψ) dK.kT (dK.idxT ψ ρ) T)
    (hTle : TupleLe dK.kT (dK.idxT ψ ρ) T
      (dK.famAt ψ ρ (lfpTuple (dK.w ψ) dK.k (dK.idx ψ ρ) (dK.Φ ψ ρ)))) :
    ∀ l, l < ((dK.Fss i ψ).getD j []).length → ((dK.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρ (((dK.Fss i ψ).getD j []).take l) fs₁ →
      dK.slotAtT pc ψ T i j l (consList fs₁ ρ)
        ⊆ˢ interp V (consList fs₁ ρ) (((dK.Fss i ψ).getD j []).getD l default) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hjl : j < (dK.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hks : (dK.ksF i j).length = ((dK.Fss i ψ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hI.Fss_length hj]
  have hTle' : ∀ c, c < dK.kT → ∀ t',
      SetTheory.app (T c) t'
        ⊆ˢ SetTheory.app (dK.famAt ψ ρ (lfpTuple (dK.w ψ) dK.k (dK.idx ψ ρ) (dK.Φ ψ ρ)) c) t' :=
    fun c hc t' => app_subset_of_famLe (hTs c hc) (hTle c hc) t'
  intro l hl hr fs₁ hl₁ hsp
  subst hl₁
  have hlt : fs₁.length < cA.2 := by rw [← hI.Fss_length hj ψ]; exact hl
  have hkl : fs₁.length < (dK.ksF i j).length := by rw [hks]; exact hl
  have hr' : (rsOf (dK.ksF i j)).getD fs₁.length false = true := by
    rwa [IsBlockModel.rss_getD hjl] at hr
  have hreal := hreps.real_dom_eq hfT hPT hi hj hρ hlt hr' hsp
  have htgtLt : dK.tgts i j fs₁.length < dK.kT := by
    rcases hI.tgt_cases hjl hkl with h1 | ⟨-, h2⟩
    · show _ < dK.k + dK.nPins; omega
    · show _ < dK.k + dK.nPins; omega
  refine Subset.trans (dK.slotAtT_mono pc
    (Y' := dK.famAt ψ ρ (lfpTuple (dK.w ψ) dK.k (dK.idx ψ ρ) (dK.Φ ψ ρ))) ?_) ?_
  · rw [BlockModel.tgtsT_of_mem hi]
    exact hTle' _ htgtLt
  · rw [BlockModel.slotAtT_of_mem hi ψ ρ _ j fs₁.length rfl, hreal]
    exact Subset.refl _

/-- **`hdom₁` at a MEMBER class of the root** (task #315 L-E, DESIGN
§U.65 — §U.64 (c)'s first row): the relational meet is in the
container's tuple space and below its extended carrier
(`relMeet_mem`/`relMeet_le_base`), so `slotDomT_of_le` applies.  This
is `copyTransfer_mem`'s `_dom` premise at the root's own reading, where
the transfer's member half starts. -/
theorem BlockModel.slotDomT_relMeet {env : Env} {m : EnvModel V env} {dK : BlockModel V}
    {pc : Nat → PinCtors V} {ψ : Name → Nat} {ρ : Nat → V} {i j : Nat}
    {R : Nat → Nat → Prop} {kB : Nat} {LB : Nat → V}
    (hreps : IsBlockModels m dK) (hfT : FormersTyped m dK ψ) (hPT : PinsTyped m dK ψ)
    (hi : i < dK.k) {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hρ : Sat V (dK.params ψ).reverse ρ) (hk : 0 < dK.k) :
    ∀ l, l < ((dK.Fss i ψ).getD j []).length → ((dK.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρ (((dK.Fss i ψ).getD j []).take l) fs₁ →
      dK.slotAtT pc ψ
          (relMeet (dK.idxT ψ ρ)
            (dK.famAt ψ ρ (lfpTuple (dK.w ψ) dK.k (dK.idx ψ ρ) (dK.Φ ψ ρ))) R kB LB)
          i j l (consList fs₁ ρ)
        ⊆ˢ interp V (consList fs₁ ρ) (((dK.Fss i ψ).getD j []).getD l default) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI0⟩ := hreps 0 hk
  refine dK.slotDomT_of_le hreps hfT hPT hi hj hρ
    (fun c hc => relMeet_mem (hI0.famAt_mem hρ (lfpTuple_mem _ _ _ _) hc))
    (fun c _ => relMeet_le_base _ _ _ _ _ _)

/-- **A block pin that is the image of one of the ROOT's OWN pins is
its partner** (task #315 L-E, DESIGN §U.65 — `InstanceCovered`'s
second case): `PinCorr` at the block's target `D.k + q` and the root
container's own pin `qK` — the target's recorded container, level
arguments, components, index universe and index telescope are that own
pin's, instantiated at the root pin's components — gives `ClassPin` at
the PIN class `dR.k + qK`.

This is the MODEL FACE of K.41's record: the kernel's
`nestedPinRootPairOk` certifies ONE equality of recorded pin TERMS
(`containerOwnPinsAt` instantiates the mimic recursor's binders at the
root pin's components, so an own pin comes out `Ds`-substituted), and
an equality of pin terms is exactly a `PinCorr` at the data the term
spells — the container (`J`), the level arguments (`lvls`) and the
components (`Ds`/`DsE`), with `u` and `Ids` following from the
container.  The same datum is what the copies' `pinF` arm already
produces at an OWN edge, so the two cases of the covering speak one
language.

The auxiliary premises are all available where the covering is used:
`hψR` is the root pin's own `pinψ` (its level assignment IS the
substitution of its level arguments), `hψD`/`hψK` are the two sides'
`pinψ`, and `hIdsBelow` is the container member's index telescope over
its parameters (`FormerData.below`).  Note that the `allParamsDefined`
scope `targetPin_corr` needs is NOT needed here: both sides' level
assignments come from `pinψ`, so the algebra is
`Level.substFn_map_subst` alone.

**The level half is unexercised by the corpus** (K.41's own caveat:
blanking the levels fires on no cone block), so `psi` below leans on a
conjunct nothing measures; `frame` and `idx` lean on the components,
which are load-bearing at every instance. -/
theorem classPin_of_pinCorr {env : Env} {m : EnvModel V env} {D dR : BlockModel V}
    {ψ ψR : Name → Nat} {ρp ρR : Nat → V} {Ds₀ : List AnnotTerm}
    {lpsK : List Name} {lvlsK : List Level} {q qK : Nat}
    (hq : q < D.nPins) (hqK : qK < dR.nPins)
    (hcorr : PinCorr (D.targetView m.acval ψ) m.acval dR ψR Ds₀ lpsK lvlsK (D.k + q) qK)
    (hρR : ρR = consList (Ds₀.map (interp V ρp)) ρp)
    (hψR : ψR = Level.substFn ψ lpsK lvlsK)
    (hψD : ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? (D.pinAt q).J = some (.indInfo cvT caps) →
      ∀ ψ' : Name → Nat, (D.pinAt q).ψJ ψ' = Level.substFn ψ' cvT.levelParams (D.pinAt q).lvls)
    (hψK : ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? (dR.pinAt qK).J = some (.indInfo cvT caps) →
      (dR.pinAt qK).lvls.length = cvT.levelParams.length ∧
      ∀ ψ' : Name → Nat,
        (dR.pinAt qK).ψJ ψ' = Level.substFn ψ' cvT.levelParams (dR.pinAt qK).lvls)
    (hDsLen : (D.pinAt q).nPJ ≤ ((D.pinAt q).Ds ψ).length)
    (hIdsBelow : FieldsBelow (((dR.pinAt qK).Ds ψR).map (interp V ρR)).length
      ((dR.pinAt qK).Ids ψR)) :
    ClassPin env D dR ψ ψR ρp ρR (dR.k + qK) q := by
  obtain ⟨hEA, hDs, hu, hIds, hJ, hlvls⟩ := hcorr
  have hnk : ¬ D.k + q < D.k := by omega
  have hsub : D.k + q - D.k = q := by omega
  -- the target view's data at the pin
  have hJ' : (D.pinAt q).J = (dR.pinAt qK).J := by
    have : (D.targetView m.acval ψ).J (D.k + q) = (D.pinAt q).J := by
      show (if D.k + q < D.k then _ else (D.pinAt (D.k + q - D.k)).J) = _
      rw [if_neg hnk, hsub]
    rw [← this]; exact hJ
  have hlvls' : (D.pinAt q).lvls = ((dR.pinAt qK).lvls).map (Level.subst lpsK lvlsK) := by
    have : (D.targetView m.acval ψ).lvls (D.k + q) = (D.pinAt q).lvls := by
      show (if D.k + q < D.k then _ else (D.pinAt (D.k + q - D.k)).lvls) = _
      rw [if_neg hnk, hsub]
    rw [← this]; exact hlvls
  have hu' : (D.pinAt q).u ψ = (dR.pinAt qK).u ψR := by
    have : (D.targetView m.acval ψ).u (D.k + q) = (D.pinAt q).u ψ := by
      show D.uT (D.k + q) ψ = _
      rw [BlockModel.uT_of_pin hnk ψ, hsub]
    rw [← this]; exact hu
  have hIds' : (D.pinAt q).Ids ψ = (dR.pinAt qK).Ids ψR := by
    have : (D.targetView m.acval ψ).Ids (D.k + q) = (D.pinAt q).Ids ψ := by
      show D.IdsT (D.k + q) ψ = _
      rw [BlockModel.IdsT_of_pin hnk ψ, hsub]
    rw [← this]; exact hIds
  have hDs' : (D.pinAt q).Ds ψ = ((dR.pinAt qK).Ds ψR).map (AnnotTerm.instAll Ds₀ 0) := by
    have : (D.targetView m.acval ψ).Ds (D.k + q) = (D.pinAt q).Ds ψ := by
      show (D.pinAt (D.k + q - D.k)).Ds ψ = _
      rw [hsub]
    rw [← this]; exact hDs
  -- the components' VALUES are one list
  have hvals : ((D.pinAt q).Ds ψ).map (interp V ρp)
      = ((dR.pinAt qK).Ds ψR).map (interp V ρR) := by
    rw [hDs', List.map_map, hρR]
    refine List.map_congr_left fun Dc _ => ?_
    show interp V ρp (AnnotTerm.instAll Ds₀ 0 Dc) = _
    have := interp_instAll Ds₀ [] ρp Dc
    simpa using this
  refine ⟨(by show dR.k + qK < dR.k + dR.nPins; omega), hq, ?_, ?_, ?_, ?_⟩
  · rw [dR.nameT_of_pin (by omega), Nat.add_sub_cancel_left]
    exact hJ'.symm
  · intro cvT caps hfind r hr
    rw [dR.psiT_of_pin ψR (by omega), Nat.add_sub_cancel_left]
    rw [hJ'] at hfind
    obtain ⟨hvlen, hlaw⟩ := hψK cvT caps hfind
    rw [hψD cvT caps (by rw [hJ']; exact hfind) ψ, hlvls',
      Level.substFn_map_subst hvlen hr, hψR, hlaw]
  · intro v hv
    rw [dR.frameT_of_pin (show ¬ dR.k + qK < dR.k by omega) ψR ρR, Nat.add_sub_cancel_left]
    unfold BlockModel.pinFrame
    rw [← hvals]
    have hvl : v < (((D.pinAt q).Ds ψ).map (interp V ρp)).length := by
      rw [List.length_map]; omega
    rw [consList_getD_lt _ _ v hvl, consList_getD_lt _ _ v hvl]
  · rw [dR.idxT_of_pin (show ¬ dR.k + qK < dR.k by omega) ψR ρR, Nat.add_sub_cancel_left]
    unfold BlockModel.pinIdx BlockModel.pinFrame
    rw [hu', hIds', ← hvals]
    unfold idxSet
    refine congrArg _ (teleOfFields_congr_below (k := (((D.pinAt q).Ds ψ).map (interp V ρp)).length)
      ?_ (fun v hv => ?_))
    · rw [hvals]; exact hIdsBelow
    · rw [consList_getD_lt _ _ v hv, consList_getD_lt _ _ v hv]

/-- **Two group views of ONE container relate their members** (task
#315 L-E, DESIGN §U.71 — the WALK at a container-recursive field with a
MEMBER target): the root's pin group `[q₀', q₀' + kK)` and the block's
pin group `[q₀, q₀ + kK)` have the same container `dK`, so the root's
PIN class at member `i` of its group and the block's pin at member `i`
of its group are `ClassPin`-related as soon as the two groups' BASE
pins agree — one level assignment on the container's level parameters
(`hparK`, which is where they are spent) and one frame on its
parameters (`hfr0`).

Both agreements travel from the pair the walk starts at: a group's
pins share their level assignment and their components
(`PinGroupView.same`), so the base pins' data ARE the pair's.  This is
`classPin_of_rootMember`'s sibling at a PIN class of the root, and it
is what §U.64 (c) listed as "the two group views". -/
theorem classPin_of_views {env : Env} {D dR dK : BlockModel V}
    {ψ ψR : Name → Nat} {ρp ρR : Nat → V} {q₀ q₀' kK i : Nat}
    (S₁ : PinGroupView D dK q₀ kK) (S₂ : PinGroupView dR dK q₀' kK)
    (hψ0 : ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? (dK.memberName i) = some (.indInfo cvT caps) →
      ∀ p ∈ cvT.levelParams, (dR.pinAt q₀').ψJ ψR p = (D.pinAt q₀).ψJ ψ p)
    (hfr0 : ∀ v, v < dK.nP → dR.pinFrame q₀' ψR ρR v = D.pinFrame q₀ ψ ρp v)
    (hparK : dK.uM i ((dR.pinAt q₀').ψJ ψR) = dK.uM i ((D.pinAt q₀).ψJ ψ) ∧
      dK.IdsM i ((dR.pinAt q₀').ψJ ψR) = dK.IdsM i ((D.pinAt q₀).ψJ ψ))
    (hIdsBelow : FieldsBelow dK.nP (dK.IdsM i ((D.pinAt q₀).ψJ ψ)))
    (hi : i < kK) :
    ClassPin env D dR ψ ψR ρp ρR (dR.k + (q₀' + i)) (q₀ + i) := by
  have hnlt : ¬ dR.k + (q₀' + i) < dR.k := by omega
  have hsub : dR.k + (q₀' + i) - dR.k = q₀' + i := by omega
  have hψ₂ := (S₂.same i hi ψR).1
  have hDs₂ := (S₂.same i hi ψR).2
  have hψ₁ := (S₁.same i hi ψ).1
  have hDs₁ := (S₁.same i hi ψ).2
  have hfr₂ : dR.pinFrame (q₀' + i) ψR ρR = dR.pinFrame q₀' ψR ρR := by
    unfold BlockModel.pinFrame; rw [hDs₂]
  have hfr₁ : D.pinFrame (q₀ + i) ψ ρp = D.pinFrame q₀ ψ ρp := by
    unfold BlockModel.pinFrame; rw [hDs₁]
  have hIds₂ : (dR.pinAt (q₀' + i)).Ids ψR = dK.IdsM i ((dR.pinAt q₀').ψJ ψR) := by
    unfold PinSyn.Ids
    rw [S₂.pinPps i hi, S₂.pinNP i hi, hψ₂]
    rfl
  have hIds₁ : (D.pinAt (q₀ + i)).Ids ψ = dK.IdsM i ((D.pinAt q₀).ψJ ψ) := by
    unfold PinSyn.Ids
    rw [S₁.pinPps i hi, S₁.pinNP i hi, hψ₁]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · show dR.k + (q₀' + i) < dR.k + dR.nPins
    have := S₂.seg; omega
  · have := S₁.seg; omega
  · rw [dR.nameT_of_pin hnlt, hsub, S₂.name i hi, ← S₁.name i hi]
  · intro cvT caps hfind p hp
    rw [dR.psiT_of_pin ψR hnlt, hsub, hψ₂, hψ₁]
    exact hψ0 cvT caps (by rw [← S₁.name i hi]; exact hfind) p hp
  · intro v hv
    rw [dR.frameT_of_pin hnlt ψR ρR, hsub, hfr₂, hfr₁]
    exact hfr0 v (by rw [← S₁.pinNP i hi]; exact hv)
  · rw [dR.idxT_of_pin hnlt ψR ρR, hsub]
    unfold BlockModel.pinIdx
    rw [hfr₂, hfr₁, hIds₂, hIds₁, S₂.pinU i hi ψR, S₁.pinU i hi ψ, hparK.1, hparK.2]
    unfold idxSet
    exact congrArg _ (teleOfFields_congr_below hIdsBelow hfr0)

/-- **The WALK's `recF` step, packaged** (task #315 L-E, DESIGN §U.77):
`classPin_of_views` with its three auxiliary premises discharged from
the container's own record — the level agreement moved from the PAIR's
member to the FIELD's target member (`memberLpsI`), the index universe
and telescope by `params_congr`, and the telescope's bound by
`memberIds_below`.  Only the pair's own two agreements are left to the
caller. -/
theorem classPinAt_of_pairViews {env : Env} {m : EnvModel V env} {D dR dK : BlockModel V}
    {ci : ContainerInfo} (CK : ContainerModeled m ci dK) {I : Name}
    (hci : ConLeche.containerInfo? env I = some ci)
    {cvI : ConstantVal} {capsI : IndCaps} (hfI : env.find? I = some (.indInfo cvI capsI))
    {q₀ q₀' kK : Nat} (S₁ : PinGroupView D dK q₀ kK) (S₂ : PinGroupView dR dK q₀' kK)
    {ψ ψR : Name → Nat} {ρp ρR : Nat → V} {r : Nat}
    (hψ0 : ∀ pp ∈ cvI.levelParams, (dR.pinAt q₀').ψJ ψR pp = (D.pinAt q₀).ψJ ψ pp)
    (hfr0 : ∀ v, v < dK.nP → dR.pinFrame q₀' ψR ρR v = D.pinFrame q₀ ψ ρp v)
    {i : Nat} (hi : i < kK) :
    ClassPinAt env D dR ψ ψR ρp ρR r (dR.k + (q₀' + i)) (q₀ + i) := by
  have hik : i < dK.k := S₁.kEq ▸ hi
  have hpar := CK.params_congr hci hfI hψ0 hik
  refine ⟨classPin_of_views S₁ S₂ (fun cvTi capsi hfi pp hp => ?_) hfr0
    ⟨hpar.1, ?_⟩ (memberIds_below CK.reps hik _) hi, fun hlt => absurd hlt (by omega)⟩
  · exact hψ0 pp (by rw [← CK.memberLpsI hci hfI hik hfi]; exact hp)
  · unfold BlockModel.IdsM
    rw [hpar.2.1]

/-- **The WALK's `pinF` step** (task #315 L-E, DESIGN §U.86): at a
container-recursive field whose target is one of the CONTAINER's own
pins, the two sides' copies carry a `PinCorr` at the SAME own pin
`qK'`, so the field's two targets are `ClassPin`-related and the
relation's root-group conjunct is vacuous (both are PIN classes).

Each clause comes off the two `PinCorr`s and one part of
`ContainerPinParams`:

* `name` — the two targets' recorded containers are that own pin's
  (`PinCorr`'s `J`), and nothing else is needed;
* `psi` — each side's pin law spells its target's assignment as the
  substitution of its recorded level arguments, which `PinCorr`'s
  `lvls` clause makes the own pin's substituted at the OUTER pin's
  (`Level.substFn_map_subst` twice); what is left is the own pin's
  level arguments read at the two outer assignments, which agree by
  `Level.substFn_ext` at the scope conjunct;
* `frame` — each side's target frame is the own pin's components read
  at that side's container frame (`PinCorr`'s `Ds`, `interp_instAll`);
  the components are ONE list by the congruence and bounded at the
  container's parameters by the boundedness conjunct, so the two
  frames' agreement below `dK.nP` carries them;
* `idx` — the index universe and telescope are the own pin's by
  `PinCorr`'s `u`/`Ids`, ONE by the congruences, and the telescope
  reads only the components' prefix. -/
theorem classPinAt_of_pinCorrs {env : Env} {m : EnvModel V env} {D dR dK : BlockModel V}
    {ψ ψR : Name → Nat} {ρp ρR : Nat → V} {r : Nat}
    {ψ₁ ψ₂ : Name → Nat} {Ds₁ Ds₂ : List AnnotTerm}
    {lpsK : List Name} {lvls₁ lvls₂ : List Level} {t₁ t₂ qK' : Nat}
    {cvK : ConstantVal} (hpp : ContainerPinParams (V := V) cvK dK) (hqK' : qK' < dK.nPins)
    (hIdsBelow : FieldsBelow (((dK.pinAt qK').Ds ψ₂).map (interp V ρp)).length
      ((dK.pinAt qK').Ids ψ₂))
    (hc₁ : PinCorr (dR.targetView m.acval ψR) m.acval dK ψ₁ Ds₁ lpsK lvls₁ t₁ qK')
    (hc₂ : PinCorr (D.targetView m.acval ψ) m.acval dK ψ₂ Ds₂ lpsK lvls₂ t₂ qK')
    (ht₁ : dR.k ≤ t₁) (ht₁' : t₁ < dR.k + dR.nPins)
    (ht₂ : D.k ≤ t₂) (ht₂' : t₂ < D.k + D.nPins)
    (hψ₁ : ψ₁ = Level.substFn ψR lpsK lvls₁) (hψ₂ : ψ₂ = Level.substFn ψ lpsK lvls₂)
    (hpinψR : ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? (dR.pinAt (t₁ - dR.k)).J = some (.indInfo cvT caps) →
      (dR.pinAt (t₁ - dR.k)).lvls.length = cvT.levelParams.length ∧
      ∀ φ : Name → Nat, (dR.pinAt (t₁ - dR.k)).ψJ φ
        = Level.substFn φ cvT.levelParams (dR.pinAt (t₁ - dR.k)).lvls)
    (hpinψD : ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? (D.pinAt (t₂ - D.k)).J = some (.indInfo cvT caps) →
      ∀ φ : Name → Nat, (D.pinAt (t₂ - D.k)).ψJ φ
        = Level.substFn φ cvT.levelParams (D.pinAt (t₂ - D.k)).lvls)
    (hnPJ : (D.pinAt (t₂ - D.k)).nPJ ≤ ((dK.pinAt qK').Ds ψ₂).length)
    (hψ : ∀ pp ∈ cvK.levelParams, ψ₁ pp = ψ₂ pp)
    (hfr : ∀ v, v < dK.nP →
      consList (Ds₁.map (interp V ρR)) ρR v = consList (Ds₂.map (interp V ρp)) ρp v) :
    ClassPinAt env D dR ψ ψR ρp ρR r t₁ (t₂ - D.k) := by
  obtain ⟨hEA₁, hDs₁, hu₁, hIds₁, hJ₁, hl₁⟩ := hc₁
  obtain ⟨hEA₂, hDs₂, hu₂, hIds₂, hJ₂, hl₂⟩ := hc₂
  obtain ⟨hscope, hbelow, hcong⟩ := hpp qK' hqK'
  have hnR : ¬ t₁ < dR.k := by omega
  have hnD : ¬ t₂ < D.k := by omega
  -- the own pin's components are ONE list, read at the two container frames
  have hDsEq : (dK.pinAt qK').Ds ψ₁ = (dK.pinAt qK').Ds ψ₂ := (hcong ψ₁ ψ₂ hψ).2.1
  have hvals : (((dR.pinAt (t₁ - dR.k)).Ds ψR).map (interp V ρR))
      = (((D.pinAt (t₂ - D.k)).Ds ψ).map (interp V ρp)) := by
    have e₁ : ((dR.pinAt (t₁ - dR.k)).Ds ψR) = ((dK.pinAt qK').Ds ψ₁).map
        (AnnotTerm.instAll Ds₁ 0) := hDs₁
    have e₂ : ((D.pinAt (t₂ - D.k)).Ds ψ) = ((dK.pinAt qK').Ds ψ₂).map
        (AnnotTerm.instAll Ds₂ 0) := hDs₂
    rw [e₁, e₂, List.map_map, List.map_map, hDsEq]
    refine List.map_congr_left fun e he => ?_
    show interp V ρR (AnnotTerm.instAll Ds₁ 0 e) = interp V ρp (AnnotTerm.instAll Ds₂ 0 e)
    have i₁ : interp V ρR (AnnotTerm.instAll Ds₁ 0 e)
        = interp V (consList (Ds₁.map (interp V ρR)) ρR) e := by
      have := interp_instAll Ds₁ [] ρR e; simpa using this
    have i₂ : interp V ρp (AnnotTerm.instAll Ds₂ 0 e)
        = interp V (consList (Ds₂.map (interp V ρp)) ρp) e := by
      have := interp_instAll Ds₂ [] ρp e; simpa using this
    rw [i₁, i₂]
    exact interp_congr_below V e dK.nP _ _ (hbelow ψ₂ e he) hfr
  refine ⟨⟨(by show t₁ < dR.k + dR.nPins; omega), by omega, ?_, ?_, ?_, ?_⟩,
    fun hlt => absurd hlt (by omega)⟩
  · -- ONE container
    rw [dR.nameT_of_pin hnR]
    have j₁ : (dR.targetView m.acval ψR).J t₁ = (dR.pinAt (t₁ - dR.k)).J := if_neg hnR
    have j₂ : (D.targetView m.acval ψ).J t₂ = (D.pinAt (t₂ - D.k)).J := if_neg hnD
    rw [← j₁, ← j₂, hJ₁, hJ₂]
  · -- ONE level assignment at the target container's level parameters
    intro cvT caps hfind pp hpp'
    have hfind₁ : env.find? (dR.pinAt (t₁ - dR.k)).J = some (.indInfo cvT caps) := by
      have j₁ : (dR.targetView m.acval ψR).J t₁ = (dR.pinAt (t₁ - dR.k)).J := if_neg hnR
      have j₂ : (D.targetView m.acval ψ).J t₂ = (D.pinAt (t₂ - D.k)).J := if_neg hnD
      rw [show (dR.pinAt (t₁ - dR.k)).J = (D.pinAt (t₂ - D.k)).J from by
        rw [← j₁, ← j₂, hJ₁, hJ₂]]
      exact hfind
    obtain ⟨hlenR, hlawR⟩ := hpinψR cvT caps hfind₁
    have hlvlsR : (dR.pinAt (t₁ - dR.k)).lvls
        = ((dK.pinAt qK').lvls).map (Level.subst lpsK lvls₁) := by
      have j : (dR.targetView m.acval ψR).lvls t₁ = (dR.pinAt (t₁ - dR.k)).lvls := if_neg hnR
      rw [← j, hl₁]
    have hlvlsD : (D.pinAt (t₂ - D.k)).lvls
        = ((dK.pinAt qK').lvls).map (Level.subst lpsK lvls₂) := by
      have j : (D.targetView m.acval ψ).lvls t₂ = (D.pinAt (t₂ - D.k)).lvls := if_neg hnD
      rw [← j, hl₂]
    have hvlen : ((dK.pinAt qK').lvls).length = cvT.levelParams.length := by
      rw [← hlenR, hlvlsR, List.length_map]
    rw [dR.psiT_of_pin ψR hnR, hlawR, hpinψD cvT caps hfind, hlvlsR, hlvlsD,
      Level.substFn_map_subst hvlen hpp', Level.substFn_map_subst hvlen hpp', ← hψ₁, ← hψ₂]
    exact Level.substFn_ext hψ hscope hvlen pp hpp'
  · -- ONE frame at the target container's parameters
    intro v hv
    rw [dR.frameT_of_pin hnR ψR ρR]
    unfold BlockModel.pinFrame
    rw [hvals]
    have hvl : v < (((D.pinAt (t₂ - D.k)).Ds ψ).map (interp V ρp)).length := by
      rw [List.length_map,
        show ((D.pinAt (t₂ - D.k)).Ds ψ) = (D.targetView m.acval ψ).Ds t₂ from rfl,
        hDs₂, List.length_map]
      omega
    rw [consList_getD_lt _ _ v hvl, consList_getD_lt _ _ v hvl]
  · -- ONE index set
    rw [dR.idxT_of_pin hnR ψR ρR]
    unfold BlockModel.pinIdx BlockModel.pinFrame
    have hu : (dR.pinAt (t₁ - dR.k)).u ψR = (D.pinAt (t₂ - D.k)).u ψ := by
      have j₁ : (dR.targetView m.acval ψR).u t₁ = dR.uT t₁ ψR := rfl
      have j₂ : (D.targetView m.acval ψ).u t₂ = D.uT t₂ ψ := rfl
      rw [← BlockModel.uT_of_pin hnR ψR, ← BlockModel.uT_of_pin hnD ψ, ← j₁, ← j₂,
        hu₁, hu₂, (hcong ψ₁ ψ₂ hψ).1]
    have hIds : (dR.pinAt (t₁ - dR.k)).Ids ψR = (D.pinAt (t₂ - D.k)).Ids ψ := by
      rw [show (dR.pinAt (t₁ - dR.k)).Ids ψR = (dR.targetView m.acval ψR).Ids t₁ from
          (BlockModel.IdsT_of_pin hnR ψR).symm,
        show (D.pinAt (t₂ - D.k)).Ids ψ = (D.targetView m.acval ψ).Ids t₂ from
          (BlockModel.IdsT_of_pin hnD ψ).symm,
        hIds₁, hIds₂, (hcong ψ₁ ψ₂ hψ).2.2]
    have hIdsB' : FieldsBelow (((D.pinAt (t₂ - D.k)).Ds ψ).map (interp V ρp)).length
        ((D.pinAt (t₂ - D.k)).Ids ψ) := by
      rw [show ((D.pinAt (t₂ - D.k)).Ids ψ) = (dK.pinAt qK').Ids ψ₂ from
            (BlockModel.IdsT_of_pin hnD ψ).symm.trans hIds₂,
        List.length_map,
        show ((D.pinAt (t₂ - D.k)).Ds ψ) = ((dK.pinAt qK').Ds ψ₂).map (AnnotTerm.instAll Ds₂ 0)
          from hDs₂, List.length_map, ← List.length_map (f := interp V ρp)]
      exact hIdsBelow
    rw [hu, hIds, hvals]
    unfold idxSet
    refine congrArg _ (teleOfFields_congr_below hIdsB' (fun v hv => ?_))
    rw [consList_getD_lt _ _ v hv, consList_getD_lt _ _ v hv]

/-- **THE WALK at a PIN class of the root** (task #315 L-E, DESIGN
§U.86): at a container-recursive field of the container's constructor,
the root's copy's target class and the block's copy's target are
`ClassPinAt`-related — a MEMBER target of the container by
`classPinAt_of_pairViews` at the two groups' views, one of the
container's OWN pins by `classPinAt_of_pinCorrs` at the two copies'
`PinCorr`.  Both targets are PIN classes of the root, so the
relation's root-group conjunct is vacuous throughout.

The premises are the pair's own two agreements (`hψ`, `hfr`), the
container's record (`CK`, `hpp`, and `hOwn` for ITS pins' groups), and
each side's pin laws — the root's `ContainerModeled.pinψ` and the
block's own, which the run supplies. -/
theorem classPinAt_of_walk {env : Env} {m : EnvModel V env} {D dR dK : BlockModel V}
    {ciK : ContainerInfo} (CK : ContainerModeled m ciK dK) {IK : Name}
    (hciK : ConLeche.containerInfo? env IK = some ciK)
    {cvK : ConstantVal} {capsK : IndCaps} (hfK : env.find? IK = some (.indInfo cvK capsK))
    (hpp : ContainerPinParams (V := V) cvK dK)
    (hOwn : ∀ qq, qq < dK.nPins → ∃ (q₀'' kk'' i'' : Nat) (dJ'' : BlockModel V),
      qq = q₀'' + i'' ∧ i'' < kk'' ∧ PinGroupView dK dJ'' q₀'' kk'' ∧ IsBlockModels m dJ'')
    {q₀ q₀' kK : Nat} (S₁ : PinGroupView D dK q₀ kK) (S₂ : PinGroupView dR dK q₀' kK)
    {ψ ψR : Name → Nat} {ρp ρR : Nat → V} {r iq j : Nat}
    {lvls₁ lvls₂ : List Level} {tg₁ tg₂ : Nat → Nat}
    {tls₁ tls₂ : List (List (Nat × Nat × AnnotTerm))} {Eis₁ Eis₂ : List (List AnnotTerm)}
    {Fs₁ Fs₂ Es₁ Es₂ : List AnnotTerm} {rs₁ rs₂ : List Bool}
    (h₁ : CopyCtorShape (dR.targetView m.acval ψR) m.acval dK ((dR.pinAt q₀').ψJ ψR)
      ((dR.pinAt q₀').Ds ψR) cvK.levelParams lvls₁ tg₁ tls₁ Eis₁ ρR iq j
      (dR.k + q₀') kK Fs₁ rs₁ Es₁)
    (h₂ : CopyCtorShape (D.targetView m.acval ψ) m.acval dK ((D.pinAt q₀).ψJ ψ)
      ((D.pinAt q₀).Ds ψ) cvK.levelParams lvls₂ tg₂ tls₂ Eis₂ ρp iq j
      (D.k + q₀) kK Fs₂ rs₂ Es₂)
    (hψ₁ : (dR.pinAt q₀').ψJ ψR = Level.substFn ψR cvK.levelParams lvls₁)
    (hψ₂ : (D.pinAt q₀).ψJ ψ = Level.substFn ψ cvK.levelParams lvls₂)
    (hpinψR : ∀ qq, qq < dR.nPins → ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? (dR.pinAt qq).J = some (.indInfo cvT caps) →
      (dR.pinAt qq).lvls.length = cvT.levelParams.length ∧
      ∀ φ : Name → Nat, (dR.pinAt qq).ψJ φ
        = Level.substFn φ cvT.levelParams (dR.pinAt qq).lvls)
    (hpinψD : ∀ qq, qq < D.nPins → ∀ (cvT : ConstantVal) (caps : IndCaps),
      env.find? (D.pinAt qq).J = some (.indInfo cvT caps) →
      ∀ φ : Name → Nat, (D.pinAt qq).ψJ φ
        = Level.substFn φ cvT.levelParams (D.pinAt qq).lvls)
    (hDsLenD : ∀ qq, qq < D.nPins → (D.pinAt qq).nPJ ≤ ((D.pinAt qq).Ds ψ).length)
    (hψ : ∀ pp ∈ cvK.levelParams,
      (dR.pinAt q₀').ψJ ψR pp = (D.pinAt q₀).ψJ ψ pp)
    (hfr : ∀ v, v < dK.nP → dR.pinFrame q₀' ψR ρR v = D.pinFrame q₀ ψ ρp v)
    (hiq : iq < kK) {l : Nat}
    (hl₁ : l < ((dK.Fss iq ((dR.pinAt q₀').ψJ ψR)).getD j []).length)
    (hl₂ : l < ((dK.Fss iq ((D.pinAt q₀).ψJ ψ)).getD j []).length)
    {cA : ConstantVal × Nat} (hj : (dK.ctorsM iq)[j]? = some cA)
    (hr : ((dK.rss iq).getD j []).getD l false = true) :
    tg₂ l = D.k + (tg₂ l - D.k) ∧ ClassPinAt env D dR ψ ψR ρp ρR r (tg₁ l) (tg₂ l - D.k) := by
  have hiqK : iq < dK.k := S₁.kEq ▸ hiq
  by_cases hnt : dK.tgts iq j l < dK.k
  · -- a MEMBER target of the container
    obtain ⟨-, htg₁, -, -⟩ := h₁.recF l hl₁ hr hnt
    obtain ⟨-, htg₂, -, -⟩ := h₂.recF l hl₂ hr hnt
    refine ⟨by rw [htg₂]; omega, ?_⟩
    rw [htg₁, htg₂,
      show dR.k + q₀' + dK.tgts iq j l = dR.k + (q₀' + dK.tgts iq j l) from by omega,
      show D.k + q₀ + dK.tgts iq j l - D.k = q₀ + dK.tgts iq j l from by omega]
    exact classPinAt_of_pairViews CK hciK hfK S₁ S₂ hψ hfr (S₁.kEq ▸ hnt)
  · -- one of the container's OWN pins
    obtain ⟨-, -, hkle₁, hklt₁, hcorr₁, -, -⟩ := h₁.pinF l hl₁ hr hnt
    obtain ⟨-, -, hkle₂, hklt₂, hcorr₂, -, -⟩ := h₂.pinF l hl₂ hr hnt
    have hkle₁' : dR.k ≤ tg₁ l := hkle₁
    have hklt₁' : tg₁ l < dR.k + dR.nPins := hklt₁
    have hkle₂' : D.k ≤ tg₂ l := hkle₂
    have hklt₂' : tg₂ l < D.k + D.nPins := hklt₂
    have hqK' : dK.tgts iq j l - dK.k < dK.nPins :=
      CK.reps.tgt_pin_lt hiqK hj l hl₂ hnt
    obtain ⟨q₀'', kk'', i'', dJ'', hqe'', hi'', S'', hreps''⟩ := hOwn _ hqK'
    refine ⟨by omega, ?_⟩
    refine classPinAt_of_pinCorrs hpp hqK' ?_ hcorr₁ hcorr₂ hkle₁' hklt₁' hkle₂' hklt₂'
      hψ₁ hψ₂ (hpinψR _ (by omega)) (hpinψD _ (by omega)) ?_ hψ hfr
    · rw [hqe'']
      exact pinIds_below S'' hreps'' hi'' ((D.pinAt q₀).ψJ ψ) ρp
    · refine Nat.le_trans (hDsLenD _ (by omega)) (Nat.le_of_eq ?_)
      rw [show ((D.pinAt (tg₂ l - D.k)).Ds ψ) = (D.targetView m.acval ψ).Ds (tg₂ l) from rfl,
        hcorr₂.2.1, List.length_map]

/-- **The covering, split at the root GROUP** (task #315 L-E, DESIGN
§U.65): `InstanceCovered` at the root pin `r` from its two cases — a
pin of the ROOT group is its own container member's partner
(`classPin_of_rootMember`, no record), and every OTHER pin of the
instance is the record's (`hothers`, which K.41's
`nestedPinRootPairOk` discharges through `classPin_of_pinCorr`).

`hgrp` — a pin whose mint group is the root's is one of `[r, r + kR)`
— is the pin table's own bookkeeping (`NestedPinGroupSyn.grp` gives
the other direction) and is cheap wherever the groups are in hand; the
group base is a PARAMETER here, since the model's `PinSyn` does not
carry it (it is `NestedPin.grpBase`, off the run). -/
theorem instanceCovered_of_others {env : Env} {D dR : BlockModel V}
    {ψ : Name → Nat} {ρp : Nat → V} {r kR : Nat} {inst grp : Nat → Nat}
    (S : PinGroupView D dR r kR)
    (hgrp : ∀ q, q < D.nPins → grp q = r → ∃ i, i < kR ∧ q = r + i)
    (hothers : ∀ q, q < D.nPins → inst q = inst r → grp q ≠ r →
      ∃ qK, ClassPin env D dR ψ ((D.pinAt r).ψJ ψ) ρp (D.pinFrame r ψ ρp) (dR.k + qK) q) :
    InstanceCovered env D dR ψ ((D.pinAt r).ψJ ψ) ρp (D.pinFrame r ψ ρp) inst r := by
  intro q hq hinst
  by_cases hb : grp q = r
  · obtain ⟨i, hi, rfl⟩ := hgrp q hq hb
    exact ⟨i, classPin_of_rootMember S hi, fun _ => rfl⟩
  · obtain ⟨qK, hcp⟩ := hothers q hq hinst hb
    exact ⟨dR.k + qK, hcp, fun hlt => absurd hlt (by omega)⟩

/-- The parameter spine read back off its own frame. -/
theorem map_range_reverse_consList (as : List V) (ρ : Nat → V) :
    (List.range as.length).reverse.map (consList as ρ) = as := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  have hi : i < as.length := h2
  rw [List.getElem_map, List.getElem_reverse]
  simp only [List.length_range, List.getElem_range]
  rw [consList_getD_lt as ρ _ (by omega),
    show as.length - 1 - (as.length - 1 - i) = i by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- **The extended carrier reads as the target view's stored
readings** (task #315 L-E, DESIGN §U.70 (b)): at a class of a stored
block model — a member or one of its own pins — the extended carrier
at a fitting index spine IS the stored reading applied to the spine:
`IsBlockModel.leaf` at a member (the former at the parameter bvars,
which read back as the parameter spine, `map_paramBvarsAt_interp`) and
`IsBlockModel.pinLeaf` at a pin (the container at the pin's
components).  Both readings are of stored constants, hence closed, so
the parameter frame does not enter (`EnvModel.cval_closedL`).

This is the `hZ` of `copyEntryAt_of_read`/`copyEntryAt_of_pinCorr` at
the ROOT's own carrier — what the container instance transfer needs to
bound the root's copy's slots by the container's real domains. -/
theorem BlockModel.famAt_reads {env : Env} {m : EnvModel V env} {d : BlockModel V}
    (hreps : IsBlockModels m d) {ψ : Name → Nat} {ρ : Nat → V}
    (hρ : Sat V (d.params ψ).reverse ρ) (hk : 0 < d.k) {t : Nat} (ht : t < d.k + d.nPins)
    (is : List V)
    (his : SpineFit ((d.targetView m.acval ψ).frame ρ t) ((d.targetView m.acval ψ).Ids t) is) :
    SetTheory.app (d.famAt ψ ρ (lfpTuple (d.w ψ) d.k (d.idx ψ ρ) (d.Φ ψ ρ)) t)
        (tupW ((d.targetView m.acval ψ).u t) is)
      = is.foldl SetTheory.app (interp V ρ ((d.targetView m.acval ψ).EA t)) := by
  obtain ⟨ρ₀, as, rfl, hsp⟩ := spineOfSat_params d hρ
  have hlenAs : as.length = d.nP := by
    have := hsp.length_eq
    rwa [hreps.params_length hk ψ] at this
  by_cases hm : t < d.k
  · -- a MEMBER: the former at the parameter bvars
    obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps t hm
    have hIds : (d.targetView m.acval ψ).Ids t = d.IdsM t ψ := by
      show d.IdsT t ψ = _
      rw [BlockModel.IdsT_of_mem hm ψ]
    have hu : (d.targetView m.acval ψ).u t = d.uM t ψ := by
      show d.uT t ψ = _
      rw [BlockModel.uT_of_mem hm ψ]
    have hfr : (d.targetView m.acval ψ).frame (consList as ρ₀) t = consList as ρ₀ :=
      TargetView.frame_of_mem _ _ hm
    rw [hfr, hIds] at his
    have hleaf := hI.leaf ψ ρ₀ as is hsp his
    unfold BlockModel.tup at hleaf
    have hEA : (d.targetView m.acval ψ).EA t
        = AnnotTerm.mkAppN (m.acval (d.memberName t) ψ) (paramBvarsAt d.nP d.nP) :=
      targetRead_of_mem hm
    have hpar : (paramBvarsAt d.nP d.nP).map (interp V (consList as ρ₀)) = as := by
      have := map_paramBvarsAt_interp (V := V) (nP := d.nP) (e := 0)
        (ρp := consList as ρ₀) (σ := consList as ρ₀) (fun j => by rw [Nat.add_zero])
      rw [Nat.add_zero] at this
      rw [this, ← hlenAs]
      exact map_range_reverse_consList as ρ₀
    rw [d.famAt_of_mem hm, hu, hEA, interp_mkAppN_foldl, hpar,
      interp_closed (V := V) (m.cval_closedL _ _) (consList as ρ₀) ρ₀, ← List.foldl_append,
      ← hleaf]
  · -- a PIN: the container at the pin's components
    obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps 0 hk
    have hq : t - d.k < d.nPins := by omega
    have hIds : (d.targetView m.acval ψ).Ids t = (d.pinAt (t - d.k)).Ids ψ := by
      show d.IdsT t ψ = _
      rw [BlockModel.IdsT_of_pin hm ψ]
    have hu : (d.targetView m.acval ψ).u t = (d.pinAt (t - d.k)).u ψ := by
      show d.uT t ψ = _
      rw [BlockModel.uT_of_pin hm ψ]
    have hfr : (d.targetView m.acval ψ).frame (consList as ρ₀) t
        = d.pinFrame (t - d.k) ψ (consList as ρ₀) := by
      rw [TargetView.frame_of_pin _ _ hm]
      rfl
    rw [hfr, hIds] at his
    have hleaf := hI.pinLeaf (t - d.k) hq ψ ρ₀ as is hsp his
    have hEA : (d.targetView m.acval ψ).EA t
        = AnnotTerm.mkAppN (m.acval (d.pinAt (t - d.k)).J ((d.pinAt (t - d.k)).ψJ ψ))
            (((d.pinAt (t - d.k)).Ds ψ)) :=
      targetRead_of_pin hm
    rw [d.famAt_of_pin hm, hu, hEA, interp_mkAppN_foldl,
      interp_closed (V := V) (m.cval_closedL _ _) (consList as ρ₀) ρ₀, ← List.foldl_append,
      ← hleaf]

/-- **A pin group's carrier IS its container's least tuple** (task #315
L-E, DESIGN §U.70 (b) — the family identity (‡)): at a pin group
`[q₀, q₀ + kK)` of a stored block model `d` whose container is `dJ`,
the block's own pin carrier at member `i` of the group and `dJ`'s least
tuple at member `i`, read at the pin's frame, are ONE family.

Both are determined by their leaves and the leaves are one reading —
`IsBlockModel.pinLeaf` at `d` gives the container at the pin's
components, `IsBlockModel.leaf` at `dJ` gives the same container
member at the same components (`PinGroupView.name`/`same`), and a
stored constant's reading is closed, so the base frame does not
separate them (`EnvModel.cval_closedL`).  `fam_eq_of_leaf` (DESIGN
§U.58) is the principle; here its two frames are literally equal, so
its index-set and spine hypotheses are `rfl`.

This is what the container instance transfer needs at a `recF` field
of the root's copy: the root's class at the copy's target IS the
container's class at the corresponding member, so `real_dom_eq`'s
carrier and the copy's slot's family are the same object. -/
theorem BlockModel.pinGroupFam_mem {env : Env} {m : EnvModel V env} {d dJ : BlockModel V}
    {q₀ kK : Nat} (hreps : IsBlockModels m d) (hrepsJ : IsBlockModels m dJ) (hk : 0 < d.k)
    (S : PinGroupView d dJ q₀ kK) {ψ : Name → Nat} {ρ : Nat → V}
    (hρ : Sat V (d.params ψ).reverse ρ) {i : Nat} (hi : i < kK) :
    d.pinCar ψ ρ (lfpTuple (d.w ψ) d.k (d.idx ψ ρ) (d.Φ ψ ρ)) (q₀ + i)
      = lfpTuple (d.w ψ) dJ.k
          (dJ.idx ((d.pinAt q₀).ψJ ψ) (d.pinFrame q₀ ψ ρ))
          (dJ.Φ ((d.pinAt q₀).ψJ ψ) (d.pinFrame q₀ ψ ρ)) i := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI0⟩ := hreps 0 hk
  obtain ⟨cvTJ, cvRJ, mIJ, rPJ, rulesJ, hIJ⟩ := hrepsJ i (S.kEq ▸ hi)
  have hqlt : q₀ + i < d.nPins := by have := S.seg; omega
  have hψJ : (d.pinAt (q₀ + i)).ψJ ψ = (d.pinAt q₀).ψJ ψ := (S.same i hi ψ).1
  have hDs : (d.pinAt (q₀ + i)).Ds ψ = (d.pinAt q₀).Ds ψ := (S.same i hi ψ).2
  have hfrm : d.pinFrame (q₀ + i) ψ ρ = d.pinFrame q₀ ψ ρ := by
    unfold BlockModel.pinFrame; rw [hDs]
  have hIds : (d.pinAt (q₀ + i)).Ids ψ = dJ.IdsM i ((d.pinAt q₀).ψJ ψ) := by
    unfold PinSyn.Ids
    rw [S.pinPps i hi, S.pinNP i hi, hψJ]
    rfl
  have hu : (d.pinAt (q₀ + i)).u ψ = dJ.uM i ((d.pinAt q₀).ψJ ψ) := S.pinU i hi ψ
  have hidxEq : d.pinIdx (q₀ + i) ψ ρ
      = dJ.idx ((d.pinAt q₀).ψJ ψ) (d.pinFrame q₀ ψ ρ) i := by
    unfold BlockModel.pinIdx
    rw [hu, hIds, hfrm]
    rfl
  obtain ⟨ρ₀, as, rfl, hsp⟩ := spineOfSat_params d hρ
  have hDsFit := S.DsFit ψ ρ₀ as hsp
  have hwJ : dJ.w ((d.pinAt q₀).ψJ ψ) = d.w ψ := S.w ψ
  refine fam_eq_of_leaf (w' := d.w ψ) (ρ₁ := d.pinFrame q₀ ψ (consList as ρ₀))
    (ρ₂ := d.pinFrame q₀ ψ (consList as ρ₀))
    (u := dJ.uM i ((d.pinAt q₀).ψJ ψ)) (Ids := dJ.IdsM i ((d.pinAt q₀).ψJ ψ))
    (A := ((((d.pinAt q₀).Ds ψ).map (interp V (consList as ρ₀)))).foldl SetTheory.app
      (interp V ρ₀ (m.acval (dJ.memberName i) ((d.pinAt q₀).ψJ ψ))))
    (fun _ h => h) rfl ?_ ?_ ?_ ?_
  · have hmem := hI0.pinMem ψ (consList as ρ₀) hρ
      (lfpTuple (d.w ψ) d.k (d.idx ψ (consList as ρ₀)) (d.Φ ψ (consList as ρ₀)))
      (lfpTuple_mem _ _ _ _) (q₀ + i) hqlt
    unfold BlockModel.pinIdx at hmem
    rw [hu, hIds, hfrm] at hmem
    exact hmem
  · exact lfpTuple_mem (d.w ψ) dJ.k
      (dJ.idx ((d.pinAt q₀).ψJ ψ) (d.pinFrame q₀ ψ (consList as ρ₀)))
      (dJ.Φ ((d.pinAt q₀).ψJ ψ) (d.pinFrame q₀ ψ (consList as ρ₀))) i (S.kEq ▸ hi)
  · intro is his
    have his' : SpineFit (d.pinFrame (q₀ + i) ψ (consList as ρ₀))
        ((d.pinAt (q₀ + i)).Ids ψ) is := by rw [hfrm, hIds]; exact his
    have hleaf := hI0.pinLeaf (q₀ + i) hqlt ψ ρ₀ as is hsp his'
    rw [hu] at hleaf
    rw [← hleaf, hDs, List.foldl_append]
    congr 2
    rw [← S.name i hi, hψJ]
  · intro is his
    have hleaf := hIJ.leaf ((d.pinAt q₀).ψJ ψ) (consList as ρ₀)
      (((d.pinAt q₀).Ds ψ).map (interp V (consList as ρ₀))) is hDsFit his
    unfold BlockModel.tup at hleaf
    rw [hwJ] at hleaf
    unfold BlockModel.pinFrame
    rw [← hleaf, List.foldl_append,
      interp_closed (V := V) (m.cval_closedL _ _) (consList as ρ₀) ρ₀]

/-- **A fit at a container's own pin's frame is a fit at the block
pin's frame, GENERICALLY** (task #315 L-E, DESIGN §U.70 (c)):
`nestedPinFrame_transport`'s form over a `PinGroupView`, which is what
a STORED block's own pins carry (`PinShapes`) — the concrete one is
stated at the block being installed and at the run's `GroupFacts`, so
the container instance transfer at a PIN class of the ROOT cannot use
it.

The two frames carry the SAME components' values — the container's
pin's components read at the pin's frame, the class's at the block's
frame (`PinCorr`'s `Ds` clause, `interp_instAll`) — over different
bases, and the index telescope (the class's container member's,
`pinPps`/`pinNP`) has its variables below the parameters
(`FormerData.below`), so the base is invisible
(`spineFit_congr_below`). -/
theorem BlockModel.pinFrame_transport {env : Env} {m : EnvModel V env}
    {d dJ dK : BlockModel V} {q₀ kK : Nat}
    (S : PinGroupView d dJ q₀ kK) (hreps : IsBlockModels m dJ)
    {ψ ψK : Name → Nat} {ρ : Nat → V} {DsK : List AnnotTerm} {i qK TG : Nat}
    (hi : i < kK) (hTG : TG = d.k + (q₀ + i))
    (hDs : (d.targetView m.acval ψ).Ds TG
      = ((dK.pinAt qK).Ds ψK).map (AnnotTerm.instAll DsK 0))
    (hIds : (d.targetView m.acval ψ).Ids TG = (dK.pinAt qK).Ids ψK) :
    ∀ is : List V,
      SpineFit (dK.pinFrame qK ψK (consList (DsK.map (interp V ρ)) ρ))
          ((dK.pinAt qK).Ids ψK) is →
      SpineFit ((d.targetView m.acval ψ).frame ρ TG)
        ((d.targetView m.acval ψ).Ids TG) is := by
  intro is hfit
  have hk : ¬ TG < d.k := by omega
  have hsub : TG - d.k = q₀ + i := by omega
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i (S.kEq ▸ hi)
  -- the components read the same values, over the two bases
  have hDsT : ((d.targetView m.acval ψ).Ds TG).map (interp V ρ)
      = ((dK.pinAt qK).Ds ψK).map (interp V (consList (DsK.map (interp V ρ)) ρ)) := by
    rw [hDs, List.map_map]
    refine List.map_congr_left fun Dc _ => ?_
    show interp V ρ (AnnotTerm.instAll _ 0 Dc) = _
    have := interp_instAll DsK [] ρ Dc
    simpa using this
  -- the class's index telescope is its container member's
  have hIdsT : (d.targetView m.acval ψ).Ids TG
      = ((dJ.ppsM i ((d.pinAt (q₀ + i)).ψJ ψ)).drop dJ.nP).map (·.2.2) := by
    show d.IdsT TG ψ = _
    rw [BlockModel.IdsT_of_pin hk ψ, hsub]
    unfold PinSyn.Ids
    rw [S.pinPps i hi, S.pinNP i hi]
  have hlenT : (((d.targetView m.acval ψ).Ds TG).map (interp V ρ)).length = dJ.nP := by
    show (((d.pinAt (TG - d.k)).Ds ψ).map (interp V ρ)).length = _
    rw [List.length_map, hsub, (S.same i hi ψ).2, S.pinDsLen ψ]
  have hXlen : (((dK.pinAt qK).Ds ψK).map
      (interp V (consList (DsK.map (interp V ρ)) ρ))).length = dJ.nP := by
    rw [← hDsT]; exact hlenT
  have hbelow : DomsBelow dJ.nP ((dJ.ppsM i ((d.pinAt (q₀ + i)).ψJ ψ)).drop dJ.nP) := by
    have := DomsBelow.drop dJ.nP (hI.former.below ((d.pinAt (q₀ + i)).ψJ ψ))
    simpa using this
  rw [TargetView.frame_of_pin _ _ hk, hIdsT, hDsT]
  rw [← hIds, hIdsT] at hfit
  unfold BlockModel.pinFrame at hfit
  refine spineFit_congr_below hbelow (fun n hn => ?_) hfit
  rw [consList_getD_lt _ _ n (by rw [hXlen]; exact hn),
    consList_getD_lt _ _ n (by rw [hXlen]; exact hn)]

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

/-- **The extended carrier is itself closed under the classes'
constructors** (task #315 L-E, DESIGN §U.57): a member class by the
container's own fibre law at its least tuple (which is a fixed point),
a pin class by `PinRecLaws.fibre` at it.  The first half of the
relational meet's closure — the other half is the transfer. -/
theorem BlockModel.famAt_TClosed {env : Env} {m : EnvModel V env} {d : BlockModel V}
    {pc : Nat → PinCtors V} (hreps : IsBlockModels m d) (hp : PinRecLaws m d pc) (hk : 0 < d.k)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp) :
    d.TClosed pc ψ ρp (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp))) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI0⟩ := hreps 0 hk
  refine ⟨fun c hc => hI0.famAt_mem hρp (lfpTuple_mem _ _ _ _) hc, fun c hc t ht j fs hj hfit => ?_⟩
  by_cases hcm : c < d.k
  · rw [BlockModel.injT_of_mem hcm]
    rw [BlockModel.idxT_of_mem hcm] at ht
    rw [d.famAt_of_mem hcm]
    obtain ⟨cvT', cvR', mI', rP', rules', hI'⟩ := hreps c hcm
    have hC := d.chainFit_of_chainFitT pc hcm hfit
    have := (hI'.fibre ψ ρp hρp _ (lfpTuple_mem _ _ _ _) c hcm t ht (d.inj ψ c j fs)).mpr
      ⟨j, fs, by rw [BlockModel.ctorsT_of_mem hcm] at hj; exact hj, hC, rfl⟩
    rwa [lfpTuple_eq (hI0.functor ψ ρp hρp).2.2 (hI0.functor ψ ρp hρp).1
      (hI0.functor ψ ρp hρp).2.1 hcm] at this
  · have hq : c - d.k < d.nPins := by have : c < d.k + d.nPins := hc; omega
    rw [BlockModel.injT_of_pin hcm]
    rw [BlockModel.idxT_of_pin hcm] at ht
    rw [d.famAt_of_pin hcm]
    refine (hp.fibre ψ ρp hρp _ (lfpTuple_mem _ _ _ _) (TupleLe.refl _ _ _) _ hq t ht _).mpr
      ⟨j, fs, by rw [BlockModel.ctorsT_of_pin hcm] at hj; exact hj, ?_, rfl⟩
    rwa [show d.k + (c - d.k) = c by omega]

/-- **`instanceLe`, modulo the TRANSFER** (task #315 L-E, DESIGN §U.48
(h), §U.57): the relational meet of the container's extended carrier
with the block's carrier at the `R`-related pins is `TClosed` — its
`famAt` half by `famAt_TClosed`, its `L⁺` half by `htrans`, the
transfer of a fit at the meet to the block's copy — so the extended
carrier lies below the meet (`famAt_le_of_TClosed`), hence below the
block's carrier at every related pair.  This is the whole of
`instanceLe` that does not depend on WHAT the classes are: a member
class of the container instance's root gives `P (r₀ + i) ≤ L⁺ (k + r₀ +
i)` and a pin class gives the same at the image pin, through the
container's own `pinLeaf`. -/
theorem instanceLe_of_transfer {env : Env} {m : EnvModel V env} {d : BlockModel V}
    {pc : Nat → PinCtors V} (hreps : IsBlockModels m d) (hp : PinRecLaws m d pc) (hk : 0 < d.k)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V (d.params ψ).reverse ρp)
    {R : Nat → Nat → Prop} {kB : Nat} {LB : Nat → V}
    (htrans : ∀ c, c < d.kT → ∀ t, t ∈ˢ d.idxT ψ ρp c → ∀ j fs, j < (d.ctorsT pc c).length →
      d.ChainFitT pc ψ ρp
        (relMeet (d.idxT ψ ρp) (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)))
          R kB LB) t c j fs →
      ∀ b, b < kB → R c b → d.injT pc ψ c j fs ∈ˢ SetTheory.app (LB b) t) :
    ∀ c b, c < d.kT → b < kB → R c b →
      FamLe (d.idxT ψ ρp c)
        (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)) c) (LB b) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI0⟩ := hreps 0 hk
  have hTcl : d.TClosed pc ψ ρp
      (relMeet (d.idxT ψ ρp) (d.famAt ψ ρp (lfpTuple (d.w ψ) d.k (d.idx ψ ρp) (d.Φ ψ ρp)))
        R kB LB) := by
    refine ⟨fun c hc => relMeet_mem (hI0.famAt_mem hρp (lfpTuple_mem _ _ _ _) hc), ?_⟩
    intro c hc t ht j fs hj hfit
    rw [app_relMeet ht]
    refine mem_sep.mpr ⟨?_, fun b hb hR => htrans c hc t ht j fs hj hfit b hb hR⟩
    refine (BlockModel.famAt_TClosed hreps hp hk hρp).2 c hc t ht j fs hj ?_
    refine d.ChainFitT_mono pc (fun c' _ t' => app_relMeet_subset _ _ _ _ _ _ _) ?_ hfit
    intro i hi hr
    by_cases hcm : c < d.k
    · obtain ⟨cvT', cvR', mI', rP', rules', hI'⟩ := hreps c hcm
      rw [BlockModel.FssT_of_mem hcm] at hi
      rw [BlockModel.rssT_of_mem hcm] at hr
      rw [BlockModel.tgtsT_of_mem hcm]
      have hjl : j < (d.ctorsM c).length := by rw [BlockModel.ctorsT_of_mem hcm] at hj; exact hj
      have hks : (d.ksF c j).length = ((d.Fss c ψ).getD j []).length := by
        rw [(hI'.ctorData (List.getElem?_eq_getElem hjl)).ksLen,
          hI'.Fss_length (List.getElem?_eq_getElem hjl) ψ]
      exact hI'.tgtsLt c j i hcm hjl (by rw [hks]; exact hi)
    · have hq : c - d.k < d.nPins := by have : c < d.k + d.nPins := hc; omega
      rw [BlockModel.FssT_of_pin hcm] at hi
      rw [BlockModel.rssT_of_pin hcm] at hr
      rw [BlockModel.tgtsT_of_pin hcm]
      have hjl : j < (pc (c - d.k)).ctors.length := by
        rw [BlockModel.ctorsT_of_pin hcm] at hj; exact hj
      exact hp.tgtsLt ψ (c - d.k) j i hq hjl hi
  have hle := d.famAt_le_of_TClosed hreps hp hk hρp hTcl
  intro c b hc hb hR
  exact (hle c hc).trans (relMeet_le_rel hb hR)

/-- **`instanceLe` at the correspondence** (task #315 L-E, DESIGN
§U.57): `instanceLe_of_transfer` with `R` the `ClassPin` relation at
the block's pins, its conclusion read at the PIN's index set (`ClassPin.idx`)
— which is the form the run consumes: at a member class of the root the
left-hand side is the root's container's least tuple at that member,
i.e. `P` at the root's group, and at a pin class it is the root's pin's
carrier at its carrier, which the root's own `pinLeaf` reads as `P` at
the image pin. -/
theorem instanceLe_of_rel {env : Env} {m : EnvModel V env} {D dR : BlockModel V}
    {pc : Nat → PinCtors V} (hreps : IsBlockModels m dR) (hp : PinRecLaws m dR pc) (hk : 0 < dR.k)
    {ψ ψR : Name → Nat} {ρp ρR : Nat → V} (hρR : Sat V (dR.params ψR).reverse ρR)
    {k kB : Nat} {LB : Nat → V} {Rel : Nat → Nat → Prop}
    (hsub : ∀ c q, Rel c q → ClassPin env D dR ψ ψR ρp ρR c q)
    (htrans : ∀ c, c < dR.kT → ∀ t, t ∈ˢ dR.idxT ψR ρR c → ∀ j fs, j < (dR.ctorsT pc c).length →
      dR.ChainFitT pc ψR ρR
        (relMeet (dR.idxT ψR ρR)
          (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR)))
          (fun c' b => ∃ q, b = k + q ∧ Rel c' q) kB LB) t c j fs →
      ∀ q, k + q < kB → Rel c q →
        dR.injT pc ψR c j fs ∈ˢ SetTheory.app (LB (k + q)) t) :
    ∀ c q, k + q < kB → Rel c q →
      FamLe (D.pinIdx q ψ ρp)
        (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR)) c) (LB (k + q)) := by
  intro c q hqk hcp
  rw [← (hsub c q hcp).idx]
  refine instanceLe_of_transfer hreps hp hk hρR
    (R := fun c' b => ∃ q', b = k + q' ∧ Rel c' q') ?_ c (k + q) (hsub c q hcp).cLt hqk
    ⟨q, rfl, hcp⟩
  intro c' hc' t ht j fs hj hfit b hb hR
  obtain ⟨q', rfl, hcp'⟩ := hR
  exact htrans c' hc' t ht j fs hj hfit q' hb hcp'

/-- `instanceLe_of_rel` at the full `ClassPin` relation. -/
theorem instanceLe_of_classPin {env : Env} {m : EnvModel V env} {D dR : BlockModel V}
    {pc : Nat → PinCtors V} (hreps : IsBlockModels m dR) (hp : PinRecLaws m dR pc) (hk : 0 < dR.k)
    {ψ ψR : Name → Nat} {ρp ρR : Nat → V} (hρR : Sat V (dR.params ψR).reverse ρR)
    {k kB : Nat} {LB : Nat → V}
    (htrans : ∀ c, c < dR.kT → ∀ t, t ∈ˢ dR.idxT ψR ρR c → ∀ j fs, j < (dR.ctorsT pc c).length →
      dR.ChainFitT pc ψR ρR
        (relMeet (dR.idxT ψR ρR)
          (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR)))
          (fun c' b => ∃ q, b = k + q ∧ ClassPin env D dR ψ ψR ρp ρR c' q) kB LB) t c j fs →
      ∀ q, k + q < kB → ClassPin env D dR ψ ψR ρp ρR c q →
        dR.injT pc ψR c j fs ∈ˢ SetTheory.app (LB (k + q)) t) :
    ∀ c q, k + q < kB → ClassPin env D dR ψ ψR ρp ρR c q →
      FamLe (D.pinIdx q ψ ρp)
        (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR)) c) (LB (k + q)) :=
  instanceLe_of_rel hreps hp hk hρR (fun _ _ h => h) htrans

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
    {dJ : BlockModel V} {ψJ : Name → Nat} {Ds : List AnnotTerm}
    {tg : Nat → Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {ρp : Nat → V}
    {i j l : Nat}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hi : i < dJ.k) {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (hρJ : Sat V (dJ.params ψJ).reverse (consList (Ds.map (interp V ρp)) ρp))
    (hw : dJ.w ψJ = TV.w) (hl : l < ((dJ.Fss i ψJ).getD j []).length)
    (hr : ((dJ.rss i).getD j []).getD l false = true) (hnt : ¬ dJ.tgts i j l < dJ.k)
    {lpsJ : List Name} {lvlsJ : List Level}
    (hcorr : PinCorr TV m.acval dJ ψJ Ds lpsJ lvlsJ (tg l) (dJ.tgts i j l - dJ.k))
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

/-- **A pin group of the run, VIEWED** (task #315 L-E, DESIGN §U.72 (a)):
`NestedPinGroup`'s facts as the abstract `PinGroupView` the container
instance transfer speaks — the group's segment, its container's
members by name, its pins' shared level assignment, level arguments and
components, and the container's arities and parameter fit, all read at
the group's BASE pin. -/
theorem pinGroupView_of_group {m : EnvModel V env₂} {q₀ kJ : Nat} {dJ : BlockModel V}
    (G : PG m q₀ kJ dJ)
    (hDsE : ∀ i', i' < kJ → ((D).pinAt (q₀ + i')).DsE = ((D).pinAt q₀).DsE) :
    PinGroupView (D) dJ q₀ kJ := by
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
  refine ⟨q₀, kJ, i, ci, hqe, hi, hci, pinGroupView_of_group G hDsE, fun i' hi' => ?_, ?_⟩
  · -- the count: the copies of a member are its constructors
    simp only [nestedPc, List.length_map, ← Nat.add_assoc]
    exact (G.ctorCount i' hi').symm
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

/-- **A stored block's pins' groups, with their containers' models** —
`PinShapes` read for the VIEWS alone, at an assignment every stored
container's `ContainerModeled` backs (task #315 L-E, DESIGN §U.70
(c)): what the container instance transfer needs at a target pin of
the ROOT, where only the frames matter. -/
theorem PinShapes.views {env : Env} {m : EnvModel V env} {B : ContainerInfo → BlockModel V}
    {d : BlockModel V} {pc : Nat → PinCtors V}
    (hB : EnvBlocksOf m B) (hSh : PinShapes m B d pc) :
    ∀ q, q < d.nPins → ∃ (q₀ kJ i : Nat) (dJ : BlockModel V),
      q = q₀ + i ∧ i < kJ ∧ PinGroupView d dJ q₀ kJ ∧ IsBlockModels m dJ := by
  intro q hq
  obtain ⟨q₀, kJ, i, ci, rfl, hi, hci, S, -⟩ := hSh q hq
  exact ⟨q₀, kJ, i, B ci, rfl, hi, S, (hB _ ci hci).1.reps⟩

/-- **The entry at a PIN class of a stored block, at its own extended
carrier** (task #315 L-E, DESIGN §U.70 (c) — `hdom₁`'s content at a
PIN class): at a pin group `[q₀, q₀ + kK)` of `dR` whose container is
`dK`, the group's copy of `dK`'s constructor `(i, j)` has, at EVERY
copy-recursive field, the container's field domain read at the pin's
frame EQUAL to the copy's slot at `dR`'s own extended carrier.  One
case per field kind:

* `pinF` — `copyEntryAt_of_pinCorr`, with `famAt_reads` for the
  target's stored reading and `pinFrame_transport` for the frames;
* `recF` — the copy's slot IS the container's at the pin's frame
  (`slot_container`), the container's domain IS its slot at its own
  least tuple (`real_dom_eq`), and the two families are ONE
  (`pinGroupFam_mem`: the root's class at the copy's target is the
  container's class at the corresponding member);
* `ordF`-right — `copyEntryAt_of_read`, again with `famAt_reads`.

With `slotSet_mono_app`/`app_relMeet_subset` this is `copyTransfer_via`'s
`hdom₁` at a pin class: the relational meet is below the extended
carrier, at which the entry is an equality. -/
theorem BlockModel.copyEntryAt_pin {env : Env} {m : EnvModel V env}
    {dR dK : BlockModel V} {q₀ kK : Nat}
    (hrepsR : IsBlockModels m dR) (hrepsK : IsBlockModels m dK) (hkR : 0 < dR.k)
    (S : PinGroupView dR dK q₀ kK)
    (hviews : ∀ q, q < dR.nPins → ∃ (q₀' kJ' i' : Nat) (dJ' : BlockModel V),
      q = q₀' + i' ∧ i' < kJ' ∧ PinGroupView dR dJ' q₀' kJ' ∧ IsBlockModels m dJ')
    {ψR : Name → Nat} {ρR : Nat → V} (hρR : Sat V (dR.params ψR).reverse ρR)
    (hfT : FormersTyped m dK ((dR.pinAt q₀).ψJ ψR))
    (hPT : PinsTyped m dK ((dR.pinAt q₀).ψJ ψR))
    {i j : Nat} (hi : i < kK) {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    {lpsK : List Name} {lvlsK : List Level} {tg : Nat → Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    {Fs Es : List AnnotTerm} {rs : List Bool}
    (hsh : CopyCtorShape (dR.targetView m.acval ψR) m.acval dK ((dR.pinAt q₀).ψJ ψR)
      ((dR.pinAt q₀).Ds ψR) lpsK lvlsK tg tls Eis ρR i j (dR.k + q₀) kK Fs rs Es)
    {l : Nat} (hl : l < ((dK.Fss i ((dR.pinAt q₀).ψJ ψR)).getD j []).length)
    (hrs : rs.getD l false = true) :
    CopyEntryAt dK ((dR.pinAt q₀).ψJ ψR) ((dR.pinAt q₀).Ds ψR) tg tls Eis ρR i j
      (dR.targetView m.acval ψR).w (dR.targetView m.acval ψR).u
      (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR))) l := by
  have hi' : i < dK.k := S.kEq ▸ hi
  have hjl : j < (dK.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hrepsK i hi'
  -- the container's parameter frame at the pin
  have hρJ : Sat V (dK.params ((dR.pinAt q₀).ψJ ψR)).reverse
      (consList (((dR.pinAt q₀).Ds ψR).map (interp V ρR)) ρR) := by
    obtain ⟨ρ, as, hρeq, hsp⟩ := spineOfSat_params dR hρR
    subst hρeq
    exact dK.satOfSpine (S.DsFit ψR ρ as hsp)
  have hw : dK.w ((dR.pinAt q₀).ψJ ψR) = (dR.targetView m.acval ψR).w := S.w ψR
  -- the root's extended carrier reads as the target view's stored readings
  have hZ : ∀ t, t < dR.k + dR.nPins → ∀ is : List V,
      SpineFit ((dR.targetView m.acval ψR).frame ρR t)
        ((dR.targetView m.acval ψR).Ids t) is →
      SetTheory.app (dR.famAt ψR ρR
          (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR)) t)
          (tupW ((dR.targetView m.acval ψR).u t) is)
        = is.foldl SetTheory.app (interp V ρR ((dR.targetView m.acval ψR).EA t)) :=
    fun t ht is his => BlockModel.famAt_reads hrepsR hρR hkR ht is his
  by_cases hr : ((dK.rss i).getD j []).getD l false = true
  · by_cases hnt : dK.tgts i j l < dK.k
    · -- a container-RECURSIVE field at a MEMBER of the container
      obtain ⟨-, htg, -, -⟩ := hsh.recF l hl hr hnt
      have hntK : dK.tgts i j l < kK := S.kEq ▸ hnt
      have hlt : l < cA.2 := by rw [← hI.Fss_length hj ((dR.pinAt q₀).ψJ ψR)]; exact hl
      have hr' : (rsOf (dK.ksF i j)).getD l false = true := by
        rwa [IsBlockModel.rss_getD hjl] at hr
      intro fs₁ hl₁ hsp
      rw [hsh.slot_container hl hr fs₁ hl₁, hrepsK.real_dom_eq hfT hPT hi' hj hρJ hlt hr' hsp,
        dK.slotAt_of_mem hnt, hw]
      -- the two targets' index universes
      have hu : (dR.targetView m.acval ψR).u (tg l)
          = dK.uM (dK.tgts i j l) ((dR.pinAt q₀).ψJ ψR) := by
        rw [htg]
        show dR.uT (dR.k + q₀ + dK.tgts i j l) ψR = _
        rw [Nat.add_assoc, BlockModel.uT_of_pin (by omega) ψR, Nat.add_sub_cancel_left]
        exact S.pinU _ hntK ψR
      -- the two families are ONE
      have hfam : dR.famAt ψR ρR
            (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR)) (tg l)
          = lfpTuple (dK.w ((dR.pinAt q₀).ψJ ψR)) dK.k
              (dK.idx ((dR.pinAt q₀).ψJ ψR)
                (consList (((dR.pinAt q₀).Ds ψR).map (interp V ρR)) ρR))
              (dK.Φ ((dR.pinAt q₀).ψJ ψR)
                (consList (((dR.pinAt q₀).Ds ψR).map (interp V ρR)) ρR))
              (dK.tgts i j l) := by
        rw [htg, Nat.add_assoc, dR.famAt_of_pin (by omega), Nat.add_sub_cancel_left,
          BlockModel.pinGroupFam_mem hrepsR hrepsK hkR S hρR hntK, hw]
        rfl
      rw [hu, hfam, hw]
    · -- a container-RECURSIVE field at one of the container's OWN pins
      obtain ⟨-, -, hkle, hklt, hcorr, htl, hEis⟩ := hsh.pinF l hl hr hnt
      have hkle' : dR.k ≤ tg l := hkle
      have hklt' : tg l < dR.k + dR.nPins := hklt
      obtain ⟨q₀', kJ', i', dJ', hqe, hi'', S', hrepsJ'⟩ := hviews _ (by omega : tg l - dR.k < dR.nPins)
      refine copyEntryAt_of_pinCorr (TV := dR.targetView m.acval ψR) hrepsK hfT hPT hi' hj hρJ
        hw hl hr hnt hcorr htl hEis ?_ (hZ _ hklt')
      exact BlockModel.pinFrame_transport S' hrepsJ' hi'' (by omega) hcorr.2.1 hcorr.2.2.2.1
  · -- a container-ORDINARY field the elimination rewrote
    have hr' : ((dK.rss i).getD j []).getD l false = false := by simpa using hr
    rcases hsh.ordF l hl hr' with ⟨hrC, -⟩ | ⟨-, -, hklt, hread⟩
    · rw [hrC] at hrs; exact absurd hrs Bool.false_ne_true
    · exact copyEntryAt_of_read hread (hZ _ hklt)

/-! ## The targets read as the stored readings — step (i)'s two leaf laws -/

/-- **THE TARGET'S READING AT THE AUXILIARY BLOCK, FOR EVERY TARGET**
(task #315 L-E, the collapse): the auxiliary block's own leaf reading at
target `t`, applied to the parameter variables.

`targetRead`'s MEMBER branch is this term — that is exactly what
`hleafM` says, `m.acval` at a member IS `mutMemberLeaf` — and unlike
`targetRead` it is defined at a COPY too, because `mutMemberLeaf` is
`tupleLfpAV` over all `b.k` members and nothing in it restricts the
index.  The copies have readings; only their NAMES are missing. -/
@[expose] noncomputable def auxTargetRead (nP t : Nat) (ψ : Name → Nat) : AnnotTerm :=
  AnnotTerm.mkAppN (mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t ψ)
    (paramBvarsAt nP nP)

/-- **THE COLLAPSE LEMMA: EVERY TARGET READS AS THE AUXILIARY CARRIER**
(task #315 L-E).  At a spine fitting target `t`'s index telescope, the
auxiliary carrier at `t` — the FULL `(k + n)`-tuple — applied to the
spine's tuple, is the auxiliary block's own leaf reading at `t` applied
to the spine.  **For every `t < b.k`: members and copies alike, no case
on the target.**

**This is what the three-way split collapses to.**  `memberTarget_reads`
is this lemma at `t < p.k` composed with Bekić (`ofNested_lfp`, which
converts the full tuple to the block's own `p.k`-tuple) and with
`hleafM` (which supplies a NAME for the reading).  `pinTarget_reads` is
the corresponding statement at a pin, and it lands on the CONTAINER's
least tuple instead — which is the difference that made an arm reach for
a hypothesis at another pin.  Drop the Bekić step and the name, and the
two become one statement at one carrier, dispatching on nothing.

Its proof is `memberTarget_reads`'s with the last line and the `hleafM`
rewrite removed; the index-genericity is `tupleLfpAV_fold`'s, which is
already stated at an arbitrary `m < k`. -/
theorem auxTarget_reads
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    (hOk : NestedLfpOk (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
      (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
      (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
      (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
      (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
      (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) ψ ρp)
    {t : Nat} (ht : t < b.k) {is : List V}
    (his : SpineFit ρp (blockIds b.nP ppsF ψ t) is) :
    SetTheory.app
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp)
          (nestedΨ (V := V) b.nP p.k f₀.s ppsF W pinsS b.ownOffset
            (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
            (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
            (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
            (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)
            ψ ρp) t)
        (tupW (nestedU p.k W pinsS ψ t) is)
      = is.foldl SetTheory.app (interp V ρp
          (auxTargetRead (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
            (kinds := kinds) (ppsF := ppsF) (W := W) (dsF := dsF) (esF := esF)
            (eissF := eissF) (tssF := tssF) b.nP t ψ)) := by
  have hkT : b.k = fms.length := h.lenFms.symm
  have hplen : ((D).params ψ).length = b.nP := by
    show (((ppsF 0 ψ).take b.nP).map (·.2.2)).length = b.nP
    rw [List.length_map, List.length_take, (h.FD 0 f₀ h.first).len ψ]
    omega
  have htl : t < fms.length := by rw [← hkT]; exact ht
  have hft := fms_get htl
  obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
  have hlenAs : as.length = b.nP := by rw [hsp.length_eq, hplen]
  have hOk' := hOk
  have hpar : (paramBvarsAt b.nP b.nP).map (interp V (consList as ρ))
      = (List.range b.nP).reverse.map (consList as ρ) :=
    map_paramBvarsAt_interp (nP := b.nP) (e := 0) (ρp := consList as ρ) (σ := consList as ρ)
      (fun _ => rfl)
  have hrng : (List.range b.nP).reverse.map (consList as ρ) = as := by
    rw [← hlenAs]; exact range_reverse_map_consList as ρ
  unfold auxTargetRead
  rw [interp_mkAppN_foldl, hpar, hrng, ← List.foldl_append]
  unfold mutMemberLeaf
  rw [interp_closed (V := V) (tupleLfpAV_below h.blockOk b.ownOffset
      ((h.FD _ _ hft).below ψ) ((h.FD _ _ hft).len ψ) ψ) _ ρ]
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
  rw [tupleLfpAV_fold htk hOk' rfl hsp_t his]
  rfl

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
  have htl : t < fms.length := by rw [← hkT, hbk]; omega
  have hft := fms_get htl
  have hName : ((fms.take p.k).map (·.cvTa.name)).getD t .anonymous
      = (fms.getD t default).cvTa.name := by
    show ((fms.take p.k).map (·.cvTa.name)).getD t .anonymous = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt ht, hft]
    rfl
  have hEA : targetRead m.acval ((fms.take p.k).map (·.cvTa.name)) pinsS b.nP p.k ψ t
      = auxTargetRead (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA) (kinds := kinds)
          (ppsF := ppsF) (W := W) (dsF := dsF) (esF := esF) (eissF := eissF) (tssF := tssF)
          b.nP t ψ := by
    rw [targetRead_of_mem ht, hName, hleafM t _ ht hft]
    rfl
  have haux := auxTarget_reads h hbk hρp hOk (by omega) his
  rw [nestedU_mem ht] at haux
  rw [hEA, ← haux]
  exact congrArg (fun X => SetTheory.app X (tupW (W ψ) is)) (ofNested_lfp hOk ht)

/-- The pin's index telescope is the container member's at the pin's
level assignment (`NestedPinGroup.pinIds` at the syntactic group). -/
theorem NestedPinGroupSyn.pinIds {st : ElimState} {m : EnvModel V env₂} {q₀ kJ : Nat}
    {dJ : BlockModel V} (S : PGS st m q₀ kJ dJ) {i : Nat} (hi : i < kJ) (ψ : Name → Nat) :
    ((D).pinAt (q₀ + i)).Ids ψ = dJ.IdsM i (((D).pinAt (q₀ + i)).ψJ ψ) := by
  unfold PinSyn.Ids
  rw [S.pinPps i hi, S.pinNP i hi]
  rfl

/-- **A PIN target reads as its container's least tuple, AT ANY FITTING
FRAME** (task #315 L-E, the restatement's row two — the reading lemma
identified as frame-generic except through `DsFit`).

This is `pinTarget_reads` with the pin's component values taken as an
ARGUMENT and their fit as a HYPOTHESIS, instead of read off the
recorded pin and supplied by `NestedPinGroupSyn.DsFit`.  Everything else
the proof uses — `stored`, `pinIds`, `IsBlockModel.leaf`, `w`, `pinU` —
is already generic in the frame, which is what the restatement claimed
and this is the check of it: the body below is the recorded-frame
proof with the `spineOfSat_params` destructuring and the `DsFit`
appeal removed, and nothing else changed.

`DsFit` was the ONLY place the recorded frame entered, so this is
exactly side condition one of the restatement made explicit at the one
lemma that needed it. -/
theorem pinTarget_reads_at {st : ElimState} (m : EnvModel V env₂) {q₀ kJ i : Nat}
    {dJ : BlockModel V} (S : PGS st m q₀ kJ dJ) (hi : i < kJ)
    {ψ : Name → Nat} {ρp : Nat → V} {aas is : List V}
    (hfit : SpineFit ρp (dJ.params (((D).pinAt (q₀ + i)).ψJ ψ)) aas)
    (his : SpineFit (consList aas ρp) (((D).pinAt (q₀ + i)).Ids ψ) is) :
    SetTheory.app
        (lfpTuple (f₀.s.eval ψ) dJ.k
          (dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ) (consList aas ρp))
          (dJ.Φ (((D).pinAt (q₀ + i)).ψJ ψ) (consList aas ρp)) i)
        (tupW (nestedU p.k W pinsS ψ (p.k + (q₀ + i))) is)
      = (aas ++ is).foldl SetTheory.app
          (interp V ρp (m.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ))) := by
  obtain ⟨cvT, caps, cvR, mI, rP, rules, -, hI, -⟩ := S.stored i hi
  rw [S.pinIds hi ψ] at his
  have hleaf := hI.leaf (((D).pinAt (q₀ + i)).ψJ ψ) ρp aas is hfit his
  rw [← S.w i hi ψ, hleaf]
  unfold BlockModel.tup
  rw [nestedU_pin]
  exact congrArg _ (congrArg (fun u => tupW u is) (S.pinU i hi ψ i hi))

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
  obtain ⟨ρ, as, rfl, hsp⟩ := spineOfSat_params (D) hρp
  have hnlt : ¬ p.k + (q₀ + i) < p.k := by omega
  have hpin : pinsS.getD (q₀ + i) default = (D).pinAt (q₀ + i) := rfl
  rw [targetRead_of_pin hnlt, Nat.add_sub_cancel_left, hpin, interp_mkAppN_foldl,
    ← List.foldl_append]
  exact pinTarget_reads_at m S hi (S.DsFit i hi ψ ρ as hsp) his

/-- **TODAY'S TARGET READING IS THE GENERAL ONE AT THE RECORDED
COMPONENTS** (task #315 L-E, the collapse's conservativity): the value
`targetValAt` gives at the recorded component values is exactly the
denotation of `targetRead`.

Both branches, in one proof of two `rw`s — which is the point.  The
member branch is an identity of the SAME term; the pin branch is
`interp_mkAppN_foldl`, the commutation of `interp` with an application
spine, and it is head-free.  Nothing here inspects the container's field
domain, because at this level there is no field domain to inspect: the
target is an index into `memberNames ++ pins`. -/
theorem targetValAt_recorded (acval : Name → (Name → Nat) → AnnotTerm)
    (memberNames : List Name) (pins : List PinSyn) (nP k : Nat) (ψ : Name → Nat)
    (ρp : Nat → V) (t : Nat) :
    targetValAt (V := V) acval memberNames pins (recordedAs (V := V) pins ψ ρp) nP k ψ ρp t
      = interp V ρp (targetRead acval memberNames pins nP k ψ t) := by
  by_cases ht : t < k
  · rw [targetValAt_of_mem ht, targetRead_of_mem ht]
  · rw [targetValAt_of_pin ht, targetRead_of_pin ht, interp_mkAppN_foldl]
    rfl

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

/-- **A pin group's SYNTACTIC facts, VIEWED** — `pinGroupView_of_group`
at `NestedPinGroupSyn`, which is what `GroupFacts` carries (task #315
L-E, DESIGN §U.72 (a)): the container instance transfer needs the view
at the ROOT group and at the block's group of the pin, and both arrive
as `GroupFacts`. -/
theorem pinGroupView_of_syn {st : ElimState} {m : EnvModel V env₂} {q₀ kJ : Nat}
    {dJ : BlockModel V} (G : PGS st m q₀ kJ dJ) : PinGroupView (D) dJ q₀ kJ := by
  have h0 : q₀ + 0 = q₀ := Nat.add_zero q₀
  refine ⟨G.seg, G.kpos, G.kEq, fun i' hi' => ?_, fun i' hi' ψ => ⟨?_, G.sameDs i' hi' ψ⟩,
    fun i' hi' => (G.same i' hi').2, fun i' hi' => (G.same i' hi').1, fun i' hi' ψ => ?_,
    G.pinNP, G.pinNIdx, G.pinPps, fun ψ => ?_, fun ψ => ?_, fun ψ ρ as hsp => ?_⟩
  · obtain ⟨cvT, cvR, mI, rP, rules, hI, -⟩ := G.rep i' hi'
    exact hI.member.symm
  · have := G.ψJEq i' 0 hi' G.kpos ψ
    rwa [h0] at this
  · have := G.pinU 0 G.kpos ψ i' hi'
    rwa [h0] at this
  · have := G.pinDsLen 0 G.kpos ψ
    rwa [h0] at this
  · have := G.w 0 G.kpos ψ
    rwa [h0] at this
  · have := G.DsFit 0 G.kpos ψ ρ as hsp
    rwa [h0] at this

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

/-- **The components a pin's frame is taken at**, as a function of the
pin — today's, read off the recorded pin syntax (task #315 L-E, the
restatement's row one).  `pinLfp` is `pinLfpAt` at exactly this
argument, definitionally. -/
noncomputable def pinAs (pinsS : List PinSyn) (ψ : Name → Nat) (ρp : Nat → V)
    (q : Nat) : List V :=
  ((pinsS.getD q default).Ds ψ).map (interp V ρp)

/-- **The containers' least tuples at the pins, AT A GIVEN FRAME** (task
#315 L-E, the restatement's row one): `pinLfp` with the pin's component
values supplied as an argument rather than read off the recorded pin.

This is the object the restated step (iii) is about.  The whole point of
the re-basing is that the frame is no longer forced to be the recorded
one: the candidate frame differs from it at the pin-valued component
positions, and every consumer of `pinLfp` that used the frame ONLY
through a fit and the index identities re-bases to `pinLfpAt` by adding
this argument and changing nothing else. -/
noncomputable def pinLfpAt (st : ElimState) (pinsS : List PinSyn) (dJf : Nat → BlockModel V)
    (w : Nat) (ψ : Name → Nat) (ρp : Nat → V) (as : List V) (q : Nat) : V :=
  lfpTuple w (dJf (st.pins.getD q default).grpBase).k
    ((dJf (st.pins.getD q default).grpBase).idx ((pinsS.getD q default).ψJ ψ)
      (consList as ρp))
    ((dJf (st.pins.getD q default).grpBase).Φ ((pinsS.getD q default).ψJ ψ)
      (consList as ρp))
    (q - (st.pins.getD q default).grpBase)

/-- **Today's `pinLfp` IS the frame-generic one at the recorded
components** (task #315 L-E).  Definitional, so a re-based theorem
specialises back to its current statement with no rewriting at all —
which is what makes the ten theorems of the restatement's list
re-basings rather than rebuilds. -/
theorem pinLfp_eq_pinLfpAt (st : ElimState) (pinsS : List PinSyn)
    (dJf : Nat → BlockModel V) (w : Nat) (ψ : Name → Nat) (ρp : Nat → V) (q : Nat) :
    pinLfp (V := V) st pinsS dJf w ψ ρp q
      = pinLfpAt (V := V) st pinsS dJf w ψ ρp (pinAs (V := V) pinsS ψ ρp q) q := by rfl

/-- **SIDE CONDITION ONE, stated** (task #315 L-E, the restatement's
(c)): the candidate components fit the container's parameter telescope,
at every pin.

It is NOT `PinGroupView.DsFit`, and the difference is the whole content
of the side condition: `DsFit` is the recorded fit of the TRUE
components and has no candidate analogue, while `PinsTyped` gives
membership in a sort rather than satisfaction of the parameter domains.
At a non-dependent telescope the two coincide and this follows from the
auxiliary block's own tuple-space membership; at a dependent telescope
`SpineFit` interprets each later domain at the EARLIER values, so a
frame mixing candidate and true entries changes those domains and the
fit has to be established at the candidate values rather than
transported.  Hence a hypothesis. -/
def CandParamFit (st : ElimState) (pinsS : List PinSyn) (dJf : Nat → BlockModel V)
    (ψ : Name → Nat) (ρp : Nat → V) (as : Nat → List V) : Prop :=
  ∀ q, q < pinsS.length →
    SpineFit ρp ((dJf (st.pins.getD q default).grpBase).params ((pinsS.getD q default).ψJ ψ))
      (as q)

/-- **SIDE CONDITION TWO, stated** (task #315 L-E, the restatement's
(d)): the container's index-tuple sets do not move when the frame does.

The restated inclusion's conclusion is a `FamLe` at ONE index family —
the auxiliary block's, tied to the container's by `nestedIdx_of_group`
at the TRUE frame — while its subject is the container's least tuple at
the CANDIDATE frame.  `BlockModel.idx` reads the frame
(`idx ψ ρ mm = idxSet (uM mm ψ) ρ (IdsM mm ψ)`), so the two agree only
when no index telescope reads a component the candidate substitution
replaces.  Measured VACUOUS on every corpus (Mathlib nests 121
instances, none indexed; init nests arrays and lists only; the one
parameter-reaching fixture reaches the parameter the rewriting leaves
alone) — which is exactly why it is written into the statement now, as
nothing downstream would ever discover it. -/
def CandIdxAgree (st : ElimState) (pinsS : List PinSyn) (dJf : Nat → BlockModel V)
    (ψ : Name → Nat) (ρp : Nat → V) (as : Nat → List V) : Prop :=
  ∀ q, q < pinsS.length → ∀ i, i < (dJf (st.pins.getD q default).grpBase).k →
    (dJf (st.pins.getD q default).grpBase).idx ((pinsS.getD q default).ψJ ψ)
        (consList (as q) ρp) i
      = (dJf (st.pins.getD q default).grpBase).idx ((pinsS.getD q default).ψJ ψ)
          (consList (pinAs (V := V) pinsS ψ ρp q) ρp) i

/-- **Both side conditions hold of the TRUE components** (task #315
L-E): the fit is `DsFit`'s conclusion and the index agreement is
reflexivity.  So the restated statement, instantiated at today's frame,
asks for nothing today's does not already have — the re-basing is
conservative by construction. -/
theorem candIdxAgree_pinAs (st : ElimState) (pinsS : List PinSyn)
    (dJf : Nat → BlockModel V) (ψ : Name → Nat) (ρp : Nat → V) :
    CandIdxAgree (V := V) st pinsS dJf ψ ρp (pinAs (V := V) pinsS ψ ρp) :=
  fun _ _ _ _ => rfl

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

/-- **A pin's class index set is its container member's** (task #315
L-E, DESIGN §U.72 (a)): the block's own `idx` at the class `p.k + q₀ + i`
IS the container's `idx` at member `i` at the pin's frame — the sort by
`nestedU_pin`/`pinU`, the telescope by the group's index identity
(`GroupFacts.idx`, `idxSet_instTele`).  `nestedPinsFixed` had this
inline; the container instance transfer needs it to read a `ClassPin`'s
index clause back as the block's own membership. -/
theorem nestedIdx_of_group {st : ElimState} {m : EnvModel V env₂} {dJ : BlockModel V}
    {q₀ kJ : Nat} (G : GF st m q₀ kJ dJ) {ψ : Name → Nat} {ρp : Nat → V} {i : Nat} (hi : i < kJ) :
    (D).idx ψ ρp (p.k + q₀ + i)
      = dJ.idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) i := by
  show idxSet (nestedU p.k W pinsS ψ (p.k + q₀ + i)) ρp (blockIds b.nP ppsF ψ (p.k + q₀ + i)) = _
  rw [Nat.add_assoc, nestedU_pin]
  change idxSet (((D).pinAt (q₀ + i)).u ψ) ρp (blockIds b.nP ppsF ψ (p.k + (q₀ + i))) = _
  rw [G.syn.pinU i hi ψ i hi, ← Nat.add_assoc, G.idx i hi ψ i hi, idxSet_instTele Iff.rfl]
  rfl

/-- The same, read as the block's own pin index set (`pinIdx_of_view`). -/
theorem nestedIdx_eq_pinIdx {st : ElimState} {m : EnvModel V env₂} {dJ : BlockModel V}
    {q₀ kJ : Nat} (G : GF st m q₀ kJ dJ) {ψ : Name → Nat} {ρp : Nat → V} {i : Nat} (hi : i < kJ) :
    (D).idx ψ ρp (p.k + q₀ + i) = (D).pinIdx (q₀ + i) ψ ρp := by
  rw [nestedIdx_of_group G hi,
    BlockModel.pinIdx_of_view (pinGroupView_of_syn G.syn) ψ ρp hi,
    (G.syn.ψJEq i 0 hi G.syn.kpos ψ).trans (by rw [Nat.add_zero])]
  unfold BlockModel.pinFrame
  rw [G.syn.sameDs i hi ψ]


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

/-- **The pins' index telescopes are bounded at the squash regime**
(task #315 L-E, DESIGN §U.64): the side condition
`nestedLfpOk_of_formers` asks of the block's pins — a pin whose index
universe is `0` has truth-valued index domains, by its container's
`idxOk` at the pin's frame (`fieldsBound_instTele`).  Shared by every
consumer of the auxiliary block's `TupleLfpOk`. -/
theorem nestedPinsBound (m : EnvModel V env₂) (dJf : Nat → BlockModel V)
    {st : ElimState}
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp) :
    ∀ q, q < pinsS.length → ((D).pinAt q).u ψ = 0 →
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
  have hOk := nestedLfpOk_of_formers h hμ hbk ψ ρp hρp (nestedPinsBound m dJf hgroups hρp)
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

/-- **A group's `pinLfp` IS the container's least tuple at the pin's
frame** (task #315 L-E): what every consumer of `pinLfp` actually needs
of it, factored out so the consumers can take it as a HYPOTHESIS and
stop mentioning `pinLfp` at all.

That factoring is the re-basing: with this equation as a premise the
chain is generic in the family, and `pinLfp` is one witness among the
`pinLfpAt`s. -/
theorem pinLfp_group {st : ElimState} {m : EnvModel V env₂} {dJf : Nat → BlockModel V}
    {ψ : Name → Nat} {ρp : Nat → V} {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀))
    {i : Nat} (hi : i < kJ) :
    pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp (q₀ + i)
      = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
          ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
          ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
            (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i := by
  unfold pinLfp
  rw [(G.syn.grp i hi).1, Nat.add_sub_cancel_left]
  rfl

/-- **The block's targets read as the stored readings AT THE AUXILIARY
CARRIER** (task #315 L-E, DESIGN §U.72 — the correction to §U.64 (c)'s
`hent₂` row): `nestedPinsFixed`'s `hZ` is at `P`, the containers' least
tuples, where the entry is an EQUALITY; the container instance
transfer needs it at `L⁺`, and step (ii) gives only `L⁺ ≤ P`, the wrong
direction.  Both halves are available all the same, but only under a
hypothesis:

* at a MEMBER target the carrier's member segment IS the block's own
  least tuple (`ofNested_lfp`, Bekić), so `memberTarget_reads` applies
  unconditionally;
* at a PIN target `P q' = L⁺ (p.k + q')` is needed, and that is the
  RANK INDUCTION's hypothesis, which holds only at a target OUTSIDE
  the source's instance.  The predicate `S` is where that scope
  enters.

**Do not read `S` as "the target leaves the instance"** (this
docstring did, until 2026-09-18, and so did three DESIGN sections):
`nestedPinRankOk`'s not-own branch is

    inst.getD e.1 0 == inst.getD e.2.1 0 ||
      decide (rank.getD e.2.1 0 < rank.getD e.1 0)

— a DISJUNCTION — and it is the clause the rank MEANS, not a weakening
of one: `nestedRankPass` never relaxes along an edge whose endpoints
share a label, so a strict decrease there is something the computation
deliberately never establishes.  Fourteen such edges occur across
eight ACCEPTED blocks.  At an in-instance target `S` is supplied by
neither this lane nor the induction (DESIGN §U.92 (b)). -/
theorem nestedTargetReads_L (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {S : Nat → Prop}
    {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length → S q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Pf (q₀ + i) = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i) :
    ∀ t, t < p.k + pinsS.length → (¬ t < p.k → S (t - p.k)) → ∀ is : List V,
      SpineFit ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).frame ρp t) ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids t) is →
      SetTheory.app ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) t) (tupW ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).u t) is)
        = is.foldl SetTheory.app (interp V ρp ((TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).EA t)) := by
  have hOk := nestedLfpOk_of_formers h hμ hbk ψ ρp hρp (nestedPinsBound m dJf hgroups hρp)
  intro t ht hS is his
  by_cases hk : t < p.k
  · rw [TargetView.frame_of_mem _ _ hk] at his
    have hIds : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids t = blockIds b.nP ppsF ψ t := if_pos hk
    rw [hIds] at his
    have hu : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).u t = W ψ := nestedU_mem hk
    rw [hu, ← ofNested_lfp hOk hk]
    exact memberTarget_reads h hbk m hleafM hρp hOk hk his
  · have ht' : t = p.k + (t - p.k) := by omega
    have his' : SpineFit (consList ((((D).pinAt (t - p.k)).Ds ψ).map (interp V ρp)) ρp)
        (((D).pinAt (t - p.k)).Ids ψ) is := by
      rw [TargetView.frame_of_pin _ _ hk] at his
      have hIds : (TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ).Ids t = ((D).pinAt (t - p.k)).Ids ψ := if_neg hk
      rw [hIds] at his
      exact his
    obtain ⟨q₀, kJ, i, hqe, hi, G⟩ := hgroups (t - p.k) (by omega)
    rw [ht', ← hIH (t - p.k) (by omega) (hS hk), ← ht']
    rw [ht'] at his' ⊢
    rw [show p.k + (t - p.k) - p.k = t - p.k from by omega] at his'
    rw [hqe] at his' ⊢
    have hP := hPfGroup q₀ kJ G i hi
    rw [show p.k + (q₀ + i) - p.k = q₀ + i from by omega, hP]
    exact pinTarget_reads m G.syn hi hρp his'

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
  have hOk := nestedLfpOk_of_formers h hμ hbk ψ ρp hρp (nestedPinsBound m dJf hgroups hρp)
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

/-- **A copy's injection lands in the auxiliary carrier** (task #315
L-E, DESIGN §U.64 — step (3) of the container instance transfer,
DESIGN §U.58 (b)): the block's copy of pin `q₀ + i`'s constructor `j`,
fitting the auxiliary carrier at a spine `fs` whose result index
readings are `t`, injects into the carrier's fibre there —
`tupleLfpΦ_fibre` at the grouped constructor position
(`ownCtors_grp`), then the fixed point's closure (`lfpTuple_closed`).

This is what turns `copyTransfer_via`'s conclusion (a fit of the
BLOCK's copy at `L⁺`, with the index equations) into the `htrans`
premise of `instanceLe_of_classPin`: nothing about the root enters, so
the whole of step (3) is discharged once and for all. -/
theorem nestedPinInj_mem (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀)) {i : Nat} (hi : i < kJ)
    {j : Nat} (hj : j < ((dJf q₀).ctorsM i).length)
    {t : V} (ht : t ∈ˢ (D).idx ψ ρp (p.k + q₀ + i)) {fs : List V}
    (hslot : FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i) + j) [])
      (fun l ρ => slotSet (f₀.s.eval ψ)
        (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0)) ρ
        (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD l [])
        (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD l [])
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
          (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0)))
      0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []) fs)
    (heq : ∀ l, l < (blockIds b.nP ppsF ψ (p.k + q₀ + i)).length →
      interp V (consList fs ρp)
          (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []).getD l default)
        = projS l t) :
    (dJf q₀).inj (((D).pinAt (q₀ + i)).ψJ ψ) i j fs
      ∈ˢ SetTheory.app (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
          (p.k + q₀ + i)) t := by
  have hlenA : ctorsA.length = b.ctors.length := h.lenA
  have hOk := nestedLfpOk_of_formers h hμ hbk ψ ρp hρp (nestedPinsBound m dJf hgroups hρp)
  have hS := nestedShape_of_formers h hbk ψ
  have hΨ := nestedΨ_functor hOk
  have hLmem : InTupleSpace (f₀.s.eval ψ) (p.k + pinsS.length) ((D).idx ψ ρp)
      (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) := lfpTuple_mem _ _ _ _
  have hseg0 := G.syn.seg
  have hw' : (dJf q₀).w (((D).pinAt (q₀ + i)).ψJ ψ) = f₀.s.eval ψ := G.syn.w i hi ψ
  have hgrp := (ownCtors_grp (kinds := kinds) (dsF := dsF) h3 hlenA ψ
    (G.syn.ctorCount i hi) j).mpr hj
  have hmem := (tupleLfpΦ_fibre hOk hS hLmem (by omega) ht
      ((dJf q₀).inj (((D).pinAt (q₀ + i)).ψJ ψ) i j fs)).mpr
    ⟨j, fs, hgrp.1, hgrp.2, hslot, heq, by rw [G.syn.inj, hw']⟩
  exact lfpTuple_closed hΨ.2.2 hΨ.1 _ (by omega) t ht _ hmem

/-! ## The container instance transfer at a PIN class: one constructor, two copies -/

/-- **The container instance transfer's PIN half** (task #315 L-E,
DESIGN §U.51 (c), §U.54 (b)): the container `J`'s own copy of one of its
pins' constructors and the BLOCK's copy of the image pin are copies of
ONE constructor of ONE container `dK`, at two level assignments that
agree on the constructor's level parameters (`targetPin_corr`,
`ContainerModeled.pinψ`) and two frames that agree on the components'
values (`PinCorr`'s `Ds`, `interp_instAll`).  So a spine fitting the
container-side copy — its slots reading the outer tuple `T` outside the
group and the pullback `Y` inside — fits the block's copy at `Z`,
whenever `Y`'s classes lie under `Z`'s targets (`hrel`, the relation's
premise) and the block-side externals' domains lie under their slots
(`hentR`).

It is a COMPOSITION, not a new field-by-field argument: the
container-side fit IS `dK.ChainFitT` at `Y` (`fit_iff_at_T_dom`), the
congruence carries that across the two readings
(`chainFitT_congr_mem`), and the block side reads it off
(`fit_imp_T_le_dom`).  The `_dom` forms are what make the middle step
possible — the container's tuple space and extended carrier do not
travel, its slots' bound does. -/
theorem copyTransfer_pin {env : Env} {m : EnvModel V env} {dK : BlockModel V}
    {pcK : Nat → PinCtors V} {acval : Name → (Name → Nat) → AnnotTerm}
    {TV₁ TV₂ : TargetView V} {ψ₁ ψ₂ : Name → Nat} {Ds₁ Ds₂ : List AnnotTerm}
    {lpsK : List Name} {lvls₁ lvls₂ : List Level}
    {tg₁ tg₂ : Nat → Nat} {tls₁ tls₂ : List (List (Nat × Nat × AnnotTerm))}
    {Eis₁ Eis₂ : List (List AnnotTerm)} {ρ₁ ρ₂ : Nat → V} {base₁ base₂ kK i j : Nat}
    {Fs₁ Fs₂ Es₁ Es₂ : List AnnotTerm} {rs₁ rs₂ : List Bool} {Y T Z : Nat → V}
    (hreps : IsBlockModels m dK) (hi : i < dK.k) (hkK : dK.k = kK)
    {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hψ : ∀ p ∈ cA.1.levelParams, ψ₁ p = ψ₂ p)
    (hρ : ∀ v, v < dK.nP →
      consList (Ds₁.map (interp V ρ₁)) ρ₁ v = consList (Ds₂.map (interp V ρ₂)) ρ₂ v)
    (hwK : dK.w ψ₁ = dK.w ψ₂)
    (huT : ∀ l, dK.uT (dK.tgts i j l) ψ₁ = dK.uT (dK.tgts i j l) ψ₂)
    (hIdsLen : (dK.IdsM i ψ₁).length = (dK.IdsM i ψ₂).length)
    (hw₁ : dK.w ψ₁ = TV₁.w) (hw₂ : dK.w ψ₂ = TV₂.w)
    (hu₁ : ∀ i', i' < kK → TV₁.u (base₁ + i') = dK.uM i' ψ₁)
    (hu₂ : ∀ i', i' < kK → TV₂.u (base₂ + i') = dK.uM i' ψ₂)
    {nI₁ nI₂ : Nat} (hnI₁ : nI₁ = (dK.IdsM i ψ₁).length) (hnI₂ : nI₂ = (dK.IdsM i ψ₂).length)
    (hdom₁ : ∀ l, l < ((dK.Fss i ψ₁).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (Ds₁.map (interp V ρ₁)) ρ₁) (((dK.Fss i ψ₁).getD j []).take l) fs₁ →
      dK.slotAtT pcK ψ₁ Y i j l (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁))
        ⊆ˢ interp V (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁))
            (((dK.Fss i ψ₁).getD j []).getD l default))
    (hdom₂ : ∀ l, l < ((dK.Fss i ψ₂).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (Ds₂.map (interp V ρ₂)) ρ₂) (((dK.Fss i ψ₂).getD j []).take l) fs₁ →
      dK.slotAtT pcK ψ₂ Y i j l (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
        ⊆ˢ interp V (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
            (((dK.Fss i ψ₂).getD j []).getD l default))
    (h₁ : CopyCtorShape TV₁ acval dK ψ₁ Ds₁ lpsK lvls₁ tg₁ tls₁ Eis₁ ρ₁ i j base₁ kK Fs₁ rs₁ Es₁)
    (h₂ : CopyCtorShape TV₂ acval dK ψ₂ Ds₂ lpsK lvls₂ tg₂ tls₂ Eis₂ ρ₂ i j base₂ kK Fs₂ rs₂ Es₂)
    (hent₁ : CopyEntryOut dK ψ₁ Ds₁ tg₁ tls₁ Eis₁ ρ₁ i j base₁ kK Fs₁ rs₁ TV₁.w TV₁.u T)
    (hL₁ : ∀ l, l < Fs₁.length → ((dK.rss i).getD j []).getD l false = true →
      ¬ dK.tgts i j l < dK.k → T (tg₁ l) = Y (dK.tgts i j l))
    (hrel : ∀ l, l < Fs₂.length → ((dK.rss i).getD j []).getD l false = true →
      ∀ t', SetTheory.app (Y (dK.tgts i j l)) t' ⊆ˢ SetTheory.app (Z (tg₂ l)) t')
    (hentR : ∀ l, l < Fs₂.length → rs₂.getD l false = true →
      ((dK.rss i).getD j []).getD l false = false → ¬ (base₂ ≤ tg₂ l ∧ tg₂ l < base₂ + kK) →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (Ds₂.map (interp V ρ₂)) ρ₂) (((dK.Fss i ψ₂).getD j []).take l) fs₁ →
        interp V (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
            (((dK.Fss i ψ₂).getD j []).getD l default)
          ⊆ˢ slotSet TV₂.w (TV₂.u (tg₂ l)) (consList fs₁ ρ₂) (tls₂.getD l []) (Eis₂.getD l [])
              (Z (tg₂ l)))
    (t : V) (fs : List V)
    (hfit : FitsFrom rs₁ (fun i' ρ => slotSet TV₁.w (TV₁.u (tg₁ i')) ρ (tls₁.getD i' [])
        (Eis₁.getD i' []) (segJoin base₁ kK T Y (tg₁ i'))) 0 ρ₁ Fs₁ fs)
    (hidx : ∀ l, l < nI₁ → interp V (consList fs ρ₁) (Es₁.getD l default) = projS l t) :
    FitsFrom rs₂ (fun i' ρ => slotSet TV₂.w (TV₂.u (tg₂ i')) ρ (tls₂.getD i' []) (Eis₂.getD i' [])
        (Z (tg₂ i'))) 0 ρ₂ Fs₂ fs ∧
    (∀ l, l < nI₂ → interp V (consList fs ρ₂) (Es₂.getD l default) = projS l t) :=
  h₂.fit_imp_T_le_dom hreps hi hkK hw₂ hu₂ hnI₂ hj hdom₂ hrel hentR t fs
    (BlockModel.chainFitT_congr_mem hreps hi hj hψ hwK huT hIdsLen hρ
      ((h₁.fit_iff_at_T_dom hreps hi hkK hw₁ hu₁ hnI₁ hj hdom₁ hent₁ hL₁ t fs).mp ⟨hfit, hidx⟩))

/-- **The container instance transfer, COPY TO COPY** (task #315 L-E,
DESIGN §U.64): two copies of ONE constructor of ONE container `dK`, at
level assignments agreeing on the constructor's own level parameters
and at frames agreeing on the components' values, carry a fit from the
first to the second — the first copy's fit at a tuple `X₁` over its
block's targets to the second's at `X₂` — under three premises, one per
field kind:

* `hdom₁`: the FIRST copy's entries sit inside the container's real
  domains.  At a container-RECURSIVE field this is the `_dom` bound of
  §U.54 (b); at an `ordF`-right field it is that side's entry law read
  as an INCLUSION, which is all the transfer needs (DESIGN §U.61
  (d) 1) — the root's tuple is below its extended carrier, at which
  the entry is an equality;
* `hent₂`: at the SECOND copy's `ordF`-right fields, the container's
  domain sits inside that copy's slot — its own entry law, again as an
  inclusion;
* `hrel`: at every container-recursive field, the first copy's target
  family is below the second's — THE WALK, and the only place a
  correspondence of targets is needed (`recF` by the two group views,
  `pinF` by `targetPin_corr`).

No `ordF`-right correspondence appears: each side's entry is its own
reading law, and the two are glued through the container's domain
chain, which `IsBlockModel.ctor_params` makes ONE list
(`fitsFrom_imp_frames_via`). -/
theorem copyTransfer_via {env : Env} {m : EnvModel V env} {dK : BlockModel V}
    {acval : Name → (Name → Nat) → AnnotTerm}
    {TV₁ TV₂ : TargetView V} {ψ₁ ψ₂ : Name → Nat} {Ds₁ Ds₂ : List AnnotTerm}
    {lpsK : List Name} {lvls₁ lvls₂ : List Level}
    {tg₁ tg₂ : Nat → Nat} {tls₁ tls₂ : List (List (Nat × Nat × AnnotTerm))}
    {Eis₁ Eis₂ : List (List AnnotTerm)} {ρ₁ ρ₂ : Nat → V} {base₁ base₂ kK i j : Nat}
    {Fs₁ Fs₂ Es₁ Es₂ : List AnnotTerm} {rs₁ rs₂ : List Bool} {X₁ X₂ : Nat → V}
    (hreps : IsBlockModels m dK) (hi : i < dK.k) (hkK : dK.k = kK)
    {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hψ : ∀ p ∈ cA.1.levelParams, ψ₁ p = ψ₂ p)
    (hρ : ∀ v, v < dK.nP →
      consList (Ds₁.map (interp V ρ₁)) ρ₁ v = consList (Ds₂.map (interp V ρ₂)) ρ₂ v)
    (hwK : dK.w ψ₁ = dK.w ψ₂)
    (huT : ∀ l, dK.uT (dK.tgts i j l) ψ₁ = dK.uT (dK.tgts i j l) ψ₂)
    (hIdsLen : (dK.IdsM i ψ₁).length = (dK.IdsM i ψ₂).length)
    (hw₁ : dK.w ψ₁ = TV₁.w) (hw₂ : dK.w ψ₂ = TV₂.w)
    (hu₁ : ∀ i', i' < kK → TV₁.u (base₁ + i') = dK.uM i' ψ₁)
    (hu₂ : ∀ i', i' < kK → TV₂.u (base₂ + i') = dK.uM i' ψ₂)
    {nI₁ nI₂ : Nat} (hnI₁ : nI₁ = (dK.IdsM i ψ₁).length) (hnI₂ : nI₂ = (dK.IdsM i ψ₂).length)
    (h₁ : CopyCtorShape TV₁ acval dK ψ₁ Ds₁ lpsK lvls₁ tg₁ tls₁ Eis₁ ρ₁ i j base₁ kK Fs₁ rs₁ Es₁)
    (h₂ : CopyCtorShape TV₂ acval dK ψ₂ Ds₂ lpsK lvls₂ tg₂ tls₂ Eis₂ ρ₂ i j base₂ kK Fs₂ rs₂ Es₂)
    (hdom₁ : ∀ l, l < ((dK.Fss i ψ₁).getD j []).length → rs₁.getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (Ds₁.map (interp V ρ₁)) ρ₁) (((dK.Fss i ψ₁).getD j []).take l) fs₁ →
      slotSet TV₁.w (TV₁.u (tg₁ l)) (consList fs₁ ρ₁) (tls₁.getD l []) (Eis₁.getD l [])
          (X₁ (tg₁ l))
        ⊆ˢ interp V (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁))
            (((dK.Fss i ψ₁).getD j []).getD l default))
    (hent₂ : ∀ l, l < ((dK.Fss i ψ₂).getD j []).length →
      ((dK.rss i).getD j []).getD l false = false → rs₂.getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (Ds₂.map (interp V ρ₂)) ρ₂) (((dK.Fss i ψ₂).getD j []).take l) fs₁ →
      interp V (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
          (((dK.Fss i ψ₂).getD j []).getD l default)
        ⊆ˢ slotSet TV₂.w (TV₂.u (tg₂ l)) (consList fs₁ ρ₂) (tls₂.getD l []) (Eis₂.getD l [])
            (X₂ (tg₂ l)))
    (hrel : ∀ l, l < ((dK.Fss i ψ₁).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true →
      ∀ t', SetTheory.app (X₁ (tg₁ l)) t' ⊆ˢ SetTheory.app (X₂ (tg₂ l)) t')
    (t : V) (fs : List V)
    (hfit : FitsFrom rs₁ (fun i' ρ => slotSet TV₁.w (TV₁.u (tg₁ i')) ρ (tls₁.getD i' [])
        (Eis₁.getD i' []) (X₁ (tg₁ i'))) 0 ρ₁ Fs₁ fs)
    (hidx : ∀ l, l < nI₁ → interp V (consList fs ρ₁) (Es₁.getD l default) = projS l t) :
    FitsFrom rs₂ (fun i' ρ => slotSet TV₂.w (TV₂.u (tg₂ i')) ρ (tls₂.getD i' []) (Eis₂.getD i' [])
        (X₂ (tg₂ i'))) 0 ρ₂ Fs₂ fs ∧
    (∀ l, l < nI₂ → interp V (consList fs ρ₂) (Es₂.getD l default) = projS l t) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  obtain ⟨hF, hE, htl, hEs⟩ := hI.ctor_params hj hψ
  have hcd := hI.ctorData hj
  have hjl : j < (dK.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hwT : TV₁.w = TV₂.w := by rw [← hw₁, ← hw₂, hwK]
  -- the two frames agree below the parameter depth, under any prefix
  have hfrm : ∀ (as : List V) v, v < dK.nP + as.length →
      consList as (consList (Ds₁.map (interp V ρ₁)) ρ₁) v
        = consList as (consList (Ds₂.map (interp V ρ₂)) ρ₂) v :=
    fun as v hv => consList_agree_above hρ as v (by omega)
  -- a container-recursive field is copy-recursive on both sides
  have hrs₁ : ∀ l, l < ((dK.Fss i ψ₁).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true → rs₁.getD l false = true := by
    intro l hl hr
    by_cases hnt : dK.tgts i j l < dK.k
    · exact (h₁.recF l hl hr hnt).1
    · exact (h₁.pinF l hl hr hnt).1
  have hrs₂ : ∀ l, l < ((dK.Fss i ψ₂).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true → rs₂.getD l false = true := by
    intro l hl hr
    by_cases hnt : dK.tgts i j l < dK.k
    · exact (h₂.recF l hl hr hnt).1
    · exact (h₂.pinF l hl hr hnt).1
  refine ⟨fitsFrom_imp_frames_via ((dK.Fss i ψ₁).getD j [])
    (ρV := consList (Ds₁.map (interp V ρ₁)) ρ₁) h₁.len
    (by rw [h₂.len, hF]) (fun l hl fs₁ hl₁ hsp => ?_) hfit, ?_⟩
  · subst hl₁
    have hl₂ : fs₁.length < ((dK.Fss i ψ₂).getD j []).length := by rw [← hF]; exact hl
    -- the container's prefix fit at the SECOND frame
    have hsp₂ : SpineFit (consList (Ds₂.map (interp V ρ₂)) ρ₂)
        (((dK.Fss i ψ₂).getD j []).take fs₁.length) fs₁ := by
      rw [← hF]
      exact spineFit_congr_fields (fieldsBelow_take _ (hI.Fss_below hj ψ₁)) hρ hsp
    -- the container's domain at the two frames
    have hcdom : interp V (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁))
          (((dK.Fss i ψ₁).getD j []).getD fs₁.length default)
        = interp V (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
          (((dK.Fss i ψ₂).getD j []).getD fs₁.length default) := by
      rw [hF]
      exact interp_congr_below V _ (dK.nP + fs₁.length) _ _
        (fieldsBelow_getD _ (hI.Fss_below hj ψ₂) hl₂) (hfrm fs₁)
    simp only [Nat.zero_add]
    by_cases hr : ((dK.rss i).getD j []).getD fs₁.length false = true
    · -- container-RECURSIVE: both sides recursive, the walk closes it
      rw [if_pos (hrs₁ _ hl hr), if_pos (hrs₂ _ hl₂ hr)]
      refine ⟨hdom₁ _ hl (hrs₁ _ hl hr) fs₁ rfl hsp, ?_⟩
      rw [h₁.slot_container hl hr fs₁ rfl, h₂.slot_container hl₂ hr fs₁ rfl,
        hwT, copyTarget_u h₁ h₂ hkK hu₁ hu₂ hl hl₂ hr (huT fs₁.length), htl, hE]
      have hcongr : slotSet TV₂.w (TV₂.u (tg₂ fs₁.length))
            (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁))
            (((dK.tlss i ψ₂).getD j []).getD fs₁.length [])
            (((dK.Eiss i ψ₂).getD j []).getD fs₁.length []) (X₁ (tg₁ fs₁.length))
          = slotSet TV₂.w (TV₂.u (tg₂ fs₁.length))
            (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
            (((dK.tlss i ψ₂).getD j []).getD fs₁.length [])
            (((dK.Eiss i ψ₂).getD j []).getD fs₁.length []) (X₁ (tg₁ fs₁.length)) := by
        refine slotSet_congr_below (k := dK.nP + fs₁.length) ?_ (fun e he => ?_) (hfrm fs₁)
        · rw [IsBlockModel.tlss_getD hj]
          exact hcd.tssBelow ψ₂ fs₁.length
        · have hmem : e ∈ (dK.eissF i j ψ₂).getD fs₁.length [] := by
            rwa [IsBlockModel.Eiss_getD hj] at he
          rw [IsBlockModel.tlss_getD hj]
          exact hcd.eissBelow ψ₂ fs₁.length e hmem
      rw [hcongr]
      exact slotSet_mono_app (hrel _ hl hr)
    · -- container-ORDINARY: the two entries are glued through its domain
      have hr' : ((dK.rss i).getD j []).getD fs₁.length false = false := by simpa using hr
      have hto₂ : interp V (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁))
            (((dK.Fss i ψ₁).getD j []).getD fs₁.length default)
          ⊆ˢ (if rs₂.getD fs₁.length false then
                slotSet TV₂.w (TV₂.u (tg₂ fs₁.length)) (consList fs₁ ρ₂)
                  (tls₂.getD fs₁.length []) (Eis₂.getD fs₁.length []) (X₂ (tg₂ fs₁.length))
              else interp V (consList fs₁ ρ₂) (Fs₂.getD fs₁.length default)) := by
        rcases h₂.ordF _ hl₂ hr' with ⟨hrC₂, hFeq₂⟩ | ⟨hrC₂, -, -, -⟩
        · rw [if_neg (by rw [hrC₂]; exact Bool.false_ne_true), hFeq₂ fs₁ rfl hsp₂,
            interp_instAll, ← hcdom]
          exact Subset.refl _
        · rw [if_pos hrC₂, hcdom]
          exact hent₂ _ hl₂ hr' hrC₂ fs₁ rfl hsp₂
      rcases h₁.ordF _ hl hr' with ⟨hrC₁, hFeq₁⟩ | ⟨hrC₁, -, -, -⟩
      · rw [if_neg (by rw [hrC₁]; exact Bool.false_ne_true), hFeq₁ fs₁ rfl hsp,
          interp_instAll]
        exact ⟨Subset.refl _, hto₂⟩
      · rw [if_pos hrC₁]
        exact ⟨hdom₁ _ hl hrC₁ fs₁ rfl hsp, Subset.trans (hdom₁ _ hl hrC₁ fs₁ rfl hsp) hto₂⟩
  · -- the index equations
    intro l hl
    rw [hnI₂] at hl
    have hlenFs : fs.length = ((dK.Fss i ψ₁).getD j []).length := hfit.length_eq.trans h₁.len
    have hlenE : ((dK.Ess i ψ₁).getD j []).length = (dK.IdsM i ψ₁).length := by
      rw [IsBlockModel.Ess_getD hj, hcd.lenE, hI.IdsM_length ψ₁]
    have hltE : l < ((dK.Ess i ψ₁).getD j []).length := by rw [hlenE, hIdsLen]; exact hl
    have hgetD_mem : ∀ (L : List AnnotTerm), l < L.length → L.getD l default ∈ L := by
      intro L hL
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hL]
      simp
    have hmemE := hgetD_mem ((dK.Ess i ψ₁).getD j []) hltE
    rw [h₂.es l hl, ← hF, ← hlenFs, interp_instAll]
    rw [← hidx l (by rw [hnI₁, hIdsLen]; exact hl), h₁.es l (by rw [hIdsLen]; exact hl),
      ← hlenFs, interp_instAll]
    have hbE := hcd.belowE ψ₁ _ (by rwa [IsBlockModel.Ess_getD hj] at hmemE)
    have hlencA : fs.length = cA.2 := by rw [hlenFs, hI.Fss_length hj ψ₁]
    rw [← hEs]
    refine (interp_congr_below V _ (dK.nP + fs.length) _ _ ?_ (hfrm fs)).symm
    rw [hlencA, IsBlockModel.Ess_getD hj]
    exact hbE

/-- **The container instance transfer's MEMBER half** (task #315 L-E,
DESIGN §U.61): at a MEMBER class of the root, the container-side fit is
ALREADY the container's `ChainFitT` — the root's container IS `dK` and
the class is one of its members — so the transfer is
`copyTransfer_pin`'s composition without its first step: the
congruence across the two readings (`chainFitT_congr_mem`, with the
slots' bound carried by `slotDom_congr_mem`) and then the block's copy
reading the fit off (`fit_imp_T_le_dom`).

The hypotheses are what the two sides' group views supply: the level
agreement on the constructor's own level parameters, the frames'
agreement on the components' values, the sort and index universes, the
`_dom` bound at the ROOT's reading (where the tuple's place in the
container's tuple space is stated), the block's copy's shape, the
relation's premise at the recursive fields (`hrel` — the WALK) and the
externals at the `ordF`-right fields (`hentR`). -/
theorem copyTransfer_mem {env : Env} {m : EnvModel V env} {dK : BlockModel V}
    {pcK : Nat → PinCtors V} {acval : Name → (Name → Nat) → AnnotTerm}
    {TV₂ : TargetView V} {ψ₁ ψ₂ : Name → Nat} {Ds₂ : List AnnotTerm}
    {lpsK : List Name} {lvls₂ : List Level}
    {tg₂ : Nat → Nat} {tls₂ : List (List (Nat × Nat × AnnotTerm))}
    {Eis₂ : List (List AnnotTerm)} {ρ₁ ρ₂ : Nat → V} {base₂ kK i j : Nat}
    {Fs₂ Es₂ : List AnnotTerm} {rs₂ : List Bool} {Y Z : Nat → V}
    (hreps : IsBlockModels m dK) (hi : i < dK.k) (hkK : dK.k = kK)
    {cA : ConstantVal × Nat} (hj : (dK.ctorsM i)[j]? = some cA)
    (hψ : ∀ p ∈ cA.1.levelParams, ψ₁ p = ψ₂ p)
    (hρ : ∀ v, v < dK.nP → ρ₁ v = consList (Ds₂.map (interp V ρ₂)) ρ₂ v)
    (hwK : dK.w ψ₁ = dK.w ψ₂)
    (huT : ∀ l, dK.uT (dK.tgts i j l) ψ₁ = dK.uT (dK.tgts i j l) ψ₂)
    (hIdsLen : (dK.IdsM i ψ₁).length = (dK.IdsM i ψ₂).length)
    (hw₂ : dK.w ψ₂ = TV₂.w) (hu₂ : ∀ i', i' < kK → TV₂.u (base₂ + i') = dK.uM i' ψ₂)
    {nI₂ : Nat} (hnI₂ : nI₂ = (dK.IdsM i ψ₂).length)
    (hdom₁ : ∀ l, l < ((dK.Fss i ψ₁).getD j []).length →
      ((dK.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρ₁ (((dK.Fss i ψ₁).getD j []).take l) fs₁ →
      dK.slotAtT pcK ψ₁ Y i j l (consList fs₁ ρ₁)
        ⊆ˢ interp V (consList fs₁ ρ₁) (((dK.Fss i ψ₁).getD j []).getD l default))
    (h₂ : CopyCtorShape TV₂ acval dK ψ₂ Ds₂ lpsK lvls₂ tg₂ tls₂ Eis₂ ρ₂ i j base₂ kK Fs₂ rs₂ Es₂)
    (hrel : ∀ l, l < Fs₂.length → ((dK.rss i).getD j []).getD l false = true →
      ∀ t', SetTheory.app (Y (dK.tgts i j l)) t' ⊆ˢ SetTheory.app (Z (tg₂ l)) t')
    (hentR : ∀ l, l < Fs₂.length → rs₂.getD l false = true →
      ((dK.rss i).getD j []).getD l false = false → ¬ (base₂ ≤ tg₂ l ∧ tg₂ l < base₂ + kK) →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (Ds₂.map (interp V ρ₂)) ρ₂) (((dK.Fss i ψ₂).getD j []).take l) fs₁ →
        interp V (consList fs₁ (consList (Ds₂.map (interp V ρ₂)) ρ₂))
            (((dK.Fss i ψ₂).getD j []).getD l default)
          ⊆ˢ slotSet TV₂.w (TV₂.u (tg₂ l)) (consList fs₁ ρ₂) (tls₂.getD l []) (Eis₂.getD l [])
              (Z (tg₂ l)))
    (t : V) (fs : List V) (hfit : dK.ChainFitT pcK ψ₁ ρ₁ Y t i j fs) :
    FitsFrom rs₂ (fun i' ρ => slotSet TV₂.w (TV₂.u (tg₂ i')) ρ (tls₂.getD i' []) (Eis₂.getD i' [])
        (Z (tg₂ i'))) 0 ρ₂ Fs₂ fs ∧
    (∀ l, l < nI₂ → interp V (consList fs ρ₂) (Es₂.getD l default) = projS l t) :=
  h₂.fit_imp_T_le_dom hreps hi hkK hw₂ hu₂ hnI₂ hj
    (BlockModel.slotDom_congr_mem hreps hi hj hψ hwK huT hρ hdom₁) hrel hentR t fs
    (BlockModel.chainFitT_congr_mem hreps hi hj hψ hwK huT hIdsLen hρ hfit)

/-- **`classPin_of_pinCorr` at the BLOCK's pin table** (task #315 L-E,
DESIGN §U.72): the premises read off the pin groups and the root
container's own record — `hψD` is the image pin's group's `stored`,
`hDsLen` is `pinNP`/`pinDsLen` at that group, `hψK` is the root's
`ContainerModeled.pinψ`, and `hIdsBelow` is `pinIds_below` at the
root's own pin group.  What the WALK produces at a `pinF` field of a
MEMBER class. -/
theorem classPin_of_blockPinCorr (m : EnvModel V env₂) {st : ElimState}
    {dJf : Nat → BlockModel V}
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {dR dK : BlockModel V} {ciR : ContainerInfo} (CR : ContainerModeled m ciR dR)
    {q₀' kK' i'' : Nat} (S' : PinGroupView dR dK q₀' kK') (hrepsK : IsBlockModels m dK)
    (hi'' : i'' < kK')
    {ψ ψR : Name → Nat} {ρp ρR : Nat → V} {Ds₀ : List AnnotTerm}
    {lpsK : List Name} {lvlsK : List Level} {q : Nat}
    (hq : q < pinsS.length) (hqK : q₀' + i'' < dR.nPins)
    (hcorr : PinCorr ((D).targetView m.acval ψ) m.acval dR ψR Ds₀ lpsK lvlsK
      (p.k + q) (q₀' + i''))
    (hρR : ρR = consList (Ds₀.map (interp V ρp)) ρp)
    (hψR : ψR = Level.substFn ψ lpsK lvlsK) :
    ClassPin env₂ (D) dR ψ ψR ρp ρR (dR.k + (q₀' + i'')) q := by
  obtain ⟨q₀, kJ, i, rfl, hi, G⟩ := hgroups q hq
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, hψJ⟩ := G.syn.stored i hi
  refine classPin_of_pinCorr hq hqK hcorr hρR hψR (fun cvT' caps' hf' ψ' => ?_)
    (fun cvT' caps' hf' => CR.pinψ (q₀' + i'') hqK cvT' caps' hf') ?_
    (pinIds_below S' hrepsK hi'' ψR ρR)
  · obtain rfl : cvT' = cvT :=
      (ConstantInfo.indInfo.inj (Option.some.inj (hf'.symm.trans hfind))).1
    exact hψJ ψ'
  · rw [G.syn.pinNP i hi, ← G.syn.pinDsLen i hi ψ]
    exact Nat.le_refl _

/-- **The per-pair transfer at a MEMBER class of the root** (task #315
L-E, DESIGN §U.72): the root container's own constructor `(c, j)` and
the BLOCK's copy of it at the root GROUP's member `c` are the two sides
of `copyTransfer_mem`, and every numeric agreement comes off the root
group's own facts — the level assignments are literally EQUAL
(`NestedPinGroupSyn.ψJEq` at the base pin), and so are the frames
(`sameDs`), so the sort, the index universes and the telescope lengths
are `rfl`; the block's sort is the group's (`w`) and the copy's index
universes are the container's (`nestedU_pin`/`pinU`).

The three genuine premises stay premises: `hdom₁` (the root's slots
inside the container's real domains — `slotDomT_relMeet` at the
relational meet), `hrel` (THE WALK) and `hentR` (the externals, at an
`ordF`-right field whose target leaves the group). -/
theorem nestedPinPair_mem (m : EnvModel V env₂) {st : ElimState} {dJf : Nat → BlockModel V}
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {pcR : Nat → PinCtors V} {M Z : Nat → V} {c j : Nat}
    (hc : c < kR) {cA : ConstantVal × Nat} (hj : ((dJf r).ctorsM c)[j]? = some cA)
    (hdom₁ : ∀ l, l < (((dJf r).Fss c (((D).pinAt r).ψJ ψ)).getD j []).length →
      (((dJf r).rss c).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit ((D).pinFrame r ψ ρp)
        ((((dJf r).Fss c (((D).pinAt r).ψJ ψ)).getD j []).take l) fs₁ →
      (dJf r).slotAtT pcR (((D).pinAt r).ψJ ψ) M c j l (consList fs₁ ((D).pinFrame r ψ ρp))
        ⊆ˢ interp V (consList fs₁ ((D).pinFrame r ψ ρp))
            ((((dJf r).Fss c (((D).pinAt r).ψJ ψ)).getD j []).getD l default))
    (hrel : ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + r + c) + j) []).length →
      (((dJf r).rss c).getD j []).getD l false = true →
      ∀ t', SetTheory.app (M ((dJf r).tgts c j l)) t'
        ⊆ˢ SetTheory.app (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + r + c) + j) []).getD l 0)) t')
    (hentR : ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + r + c) + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + r + c) + j) []).getD l false = true →
      (((dJf r).rss c).getD j []).getD l false = false →
      ¬ (p.k + r ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + r + c) + j) []).getD l 0 ∧
         ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
            (b.ownOffset (p.k + r + c) + j) []).getD l 0 < p.k + r + kR) →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit ((D).pinFrame r ψ ρp)
        ((((dJf r).Fss c (((D).pinAt r).ψJ ψ)).getD j []).take l) fs₁ →
      interp V (consList fs₁ ((D).pinFrame r ψ ρp))
          ((((dJf r).Fss c (((D).pinAt r).ψJ ψ)).getD j []).getD l default)
        ⊆ˢ slotSet (f₀.s.eval ψ)
            (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + r + c) + j) []).getD l 0)) (consList fs₁ ρp)
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l [])
            (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + r + c) + j) []).getD l 0)))
    (t : V) (fs : List V)
    (hfit : (dJf r).ChainFitT pcR (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) M t c j fs) :
    FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + r + c) + j) [])
      (fun l ρ => slotSet (f₀.s.eval ψ)
        (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + r + c) + j) []).getD l 0)) ρ
        (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l [])
        (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l [])
        (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
          (b.ownOffset (p.k + r + c) + j) []).getD l 0)))
      0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + r + c) + j) []) fs ∧
    (∀ l, l < (blockIds b.nP ppsF ψ (p.k + r + c)).length →
      interp V (consList fs ρp)
          (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l default)
        = projS l t) := by
  have hck : c < (dJf r).k := GR.syn.kEq ▸ hc
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, hψJ⟩ := GR.syn.stored c hc
  -- the two sides' level assignments and frames are LITERALLY the same
  have hψeq : ((D).pinAt (r + c)).ψJ ψ = ((D).pinAt r).ψJ ψ :=
    (GR.syn.ψJEq c 0 hc GR.syn.kpos ψ).trans (by rw [Nat.add_zero])
  have hDseq : ((D).pinAt (r + c)).Ds ψ = ((D).pinAt r).Ds ψ := GR.syn.sameDs c hc ψ
  have hsh := GR.shape c hc cvT caps hfind ψ ρp hρp c j hc (List.getElem?_eq_some_iff.mp hj).1
  unfold CopyShapeA at hsh
  rw [hψeq, hDseq] at hsh
  have hwb : (dJf r).w (((D).pinAt r).ψJ ψ) = f₀.s.eval ψ := by
    have := GR.syn.w c hc ψ; rwa [hψeq] at this
  have hnI : (blockIds b.nP ppsF ψ (p.k + r + c)).length
      = ((dJf r).IdsM c (((D).pinAt r).ψJ ψ)).length := by
    rw [GR.idx c hc ψ c hc, instTele_length, hψeq]
  exact copyTransfer_mem GR.syn.reps hck GR.syn.kEq hj (fun _ _ => rfl) (fun _ _ => rfl)
    rfl (fun _ => rfl) rfl hwb
    (fun i' hi' => by
      show nestedU p.k W pinsS ψ (p.k + r + i') = _
      rw [Nat.add_assoc, nestedU_pin]
      have := GR.syn.pinU c hc ψ i' hi'
      rwa [hψeq] at this)
    hnI hdom₁ hsh hrel hentR t fs hfit

/-- **THE EXTERNALS** (task #315 L-E, DESIGN §U.72): the `hentR`/`hent₂`
the transfer takes at EITHER class kind — at a container-ORDINARY field the
elimination rewrote, the container's domain read at the pin's frame is
the copy's slot at the AUXILIARY CARRIER (`copyEntryAt_of_read` at
`nestedTargetReads_L`, an equality, read as an inclusion).

`hout` is the induction's scope made explicit: at such a field whose
target is a PIN, that pin must satisfy the induction's predicate.  At
a MEMBER target nothing is needed, the carrier's member segment being
the block's own least tuple.

**`hout` is NOT `nestedPinRankOk`'s clause (2)** (this docstring said
it was, until 2026-09-18): that clause's not-own branch is a
DISJUNCTION — equal instance labels OR a strictly smaller rank — and
the rank induction discharges only the second alternative.  At an
`ordF`-right target inside the source's own instance, which fourteen
edges across eight ACCEPTED blocks have, `hout` needs the route DESIGN
§U.92 (c) sizes and not this one. -/
theorem nestedPinEntryOut (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {r kR : Nat} (GR : GF st m r kR (dJf r)) {S : Nat → Prop}
    {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length → S q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Pf (q₀ + i) = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
    {c j : Nat} (hc : c < kR) {cA : ConstantVal × Nat} (hj : ((dJf r).ctorsM c)[j]? = some cA)
    (hout : ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + r + c) + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + r + c) + j) []).getD l false = true →
      (((dJf r).rss c).getD j []).getD l false = false → ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) < p.k → S ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) - p.k)) :
    ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + r + c) + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + r + c) + j) []).getD l false = true →
      (((dJf r).rss c).getD j []).getD l false = false →
      ¬ (p.k + r ≤ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) ∧ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) < p.k + r + kR) →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit ((D).pinFrame r ψ ρp) ((((dJf r).Fss c (((D).pinAt r).ψJ ψ)).getD j []).take l) fs₁ →
      interp V (consList fs₁ ((D).pinFrame r ψ ρp)) ((((dJf r).Fss c (((D).pinAt r).ψJ ψ)).getD j []).getD l default)
        ⊆ˢ slotSet (f₀.s.eval ψ) (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0)) (consList fs₁ ρp)
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l []) ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0)) := by
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, hψJ⟩ := GR.syn.stored c hc
  have hψeq : ((D).pinAt (r + c)).ψJ ψ = ((D).pinAt r).ψJ ψ :=
    (GR.syn.ψJEq c 0 hc GR.syn.kpos ψ).trans (by rw [Nat.add_zero])
  have hDseq : ((D).pinAt (r + c)).Ds ψ = ((D).pinAt r).Ds ψ := GR.syn.sameDs c hc ψ
  have hsh := GR.shape c hc cvT caps hfind ψ ρp hρp c j hc (List.getElem?_eq_some_iff.mp hj).1
  unfold CopyShapeA at hsh
  rw [hψeq, hDseq] at hsh
  intro l hl hrs hr' _
  have hlF : l < (((dJf r).Fss c (((D).pinAt r).ψJ ψ)).getD j []).length := by rw [← hsh.len]; exact hl
  rcases hsh.ordF l hlF hr' with ⟨hrC, -⟩ | ⟨-, -, hklt, hread⟩
  · rw [hrC] at hrs; exact absurd hrs Bool.false_ne_true
  · have hZ := nestedTargetReads_L hμ h hbk m hleafM dJf hgroups hρp hIH hPfGroup (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) hklt
      (fun hnk => hout l hl hrs hr' hnk)
    have heq := copyEntryAt_of_read hread hZ
    intro fs₁ hl₁ hsp
    have hE := heq fs₁ hl₁ hsp
    exact fun x hx => hE ▸ hx

/-- **THE WALK at a MEMBER class of the root** (task #315 L-E, DESIGN
§U.72): at every container-recursive field of the root container's own
constructor, the field's target class and the block's copy's target pin
are `ClassPinAt`-related — a MEMBER target by `classPin_of_rootMember`
at the root GROUP's view (the copy's target is `p.k + r + tgt`, so the
relation's root-group conjunct holds by `rfl`), one of the container's
OWN pins by `classPin_of_blockPinCorr` at the copy's `PinCorr` (a PIN
class, where the conjunct is vacuous).

This is `nestedPinPair_mem`'s `hrel` modulo `app_relMeet_le_rel`. -/
theorem nestedPinWalk_mem (m : EnvModel V env₂) {st : ElimState} {dJf : Nat → BlockModel V}
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {ciR : ContainerInfo} (CR : ContainerModeled m ciR (dJf r))
    {B : ContainerInfo → BlockModel V} (hB : EnvBlocksOf m B)
    {pcR : Nat → PinCtors V} (hshR : PinShapes m B (dJf r) pcR)
    {c j : Nat} (hc : c < kR) {cA : ConstantVal × Nat} (hj : ((dJf r).ctorsM c)[j]? = some cA) :
    ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + r + c) + j) []).length →
      (((dJf r).rss c).getD j []).getD l false = true →
      ∃ q', (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) = p.k + q' ∧
        ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r
          ((dJf r).tgts c j l) q' := by
  intro l hl hr
  have hck : c < (dJf r).k := GR.syn.kEq ▸ hc
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, hψJ⟩ := GR.syn.stored c hc
  have hψeq : ((D).pinAt (r + c)).ψJ ψ = ((D).pinAt r).ψJ ψ :=
    (GR.syn.ψJEq c 0 hc GR.syn.kpos ψ).trans (by rw [Nat.add_zero])
  have hDseq : ((D).pinAt (r + c)).Ds ψ = ((D).pinAt r).Ds ψ := GR.syn.sameDs c hc ψ
  have hlveq : ((D).pinAt (r + c)).lvls = ((D).pinAt r).lvls := (GR.syn.same c hc).1
  have hsh := GR.shape c hc cvT caps hfind ψ ρp hρp c j hc (List.getElem?_eq_some_iff.mp hj).1
  unfold CopyShapeA at hsh
  rw [hψeq, hDseq, hlveq] at hsh
  have hlF : l < (((dJf r).Fss c (((D).pinAt r).ψJ ψ)).getD j []).length := by
    rw [← hsh.len]; exact hl
  by_cases hnt : (dJf r).tgts c j l < (dJf r).k
  · -- a MEMBER target: the root group's own partner
    obtain ⟨-, htg, -, -⟩ := hsh.recF l hlF hr hnt
    refine ⟨r + (dJf r).tgts c j l, by rw [htg, Nat.add_assoc], ?_,
      fun _ => rfl⟩
    exact classPin_of_rootMember (pinGroupView_of_syn GR.syn) (GR.syn.kEq ▸ hnt)
  · -- one of the container's OWN pins: the copy's `PinCorr`
    obtain ⟨-, -, hkle, hklt, hcorr, -, -⟩ := hsh.pinF l hlF hr hnt
    have hkle' : p.k ≤ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) := hkle
    have hklt' : (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) < p.k + pinsS.length := hklt
    have hqK : (dJf r).tgts c j l - (dJf r).k < (dJf r).nPins :=
      GR.syn.reps.tgt_pin_lt hck hj l hlF hnt
    obtain ⟨q₀', kK', i'', ci', hqKe, hi'', hci', S', -⟩ := hshR _ hqK
    refine ⟨(((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) - p.k, by omega, ?_, fun hlt => absurd hlt (by omega)⟩
    have hcp := classPin_of_blockPinCorr m hgroups CR S'
      ((hB _ ci' hci').1.reps) hi'' (q := (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) - p.k) (by omega) (hqKe ▸ hqK)
      (ρp := ρp) (ρR := (D).pinFrame r ψ ρp)
      (Ds₀ := ((D).pinAt r).Ds ψ) (lpsK := cvT.levelParams) (lvlsK := ((D).pinAt r).lvls)
      (by rw [nestedBlockModel_targetView m ψ, ← hqKe, show p.k + ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) - p.k) = (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) from by omega]
          exact hcorr)
      rfl (by rw [← hψeq, ← hlveq]; exact hψJ ψ)
    rw [← hqKe] at hcp
    rw [show (dJf r).k + ((dJf r).tgts c j l - (dJf r).k) = (dJf r).tgts c j l from by omega] at hcp
    exact hcp


/-- **The per-pair transfer at a PIN class of the root** (task #315
L-E, DESIGN §U.72): the root's own copy of its pin's container's
constructor and the BLOCK's copy of the image pin are two copies of ONE
constructor of ONE container, which is `copyTransfer_via`.  The BLOCK
side is read off the group's own facts — the sort (`w`), the copies'
index universes (`nestedU_pin`/`pinU`), the index-telescope length
(`GroupFacts.idx`) and the shape (`GroupFacts.shape`); the ROOT side
and the four cross agreements stay premises, because they are what the
`ClassPin` pair supplies. -/
theorem nestedPinPair_pin (m : EnvModel V env₂) {st : ElimState} {dJf : Nat → BlockModel V}
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {q₀ kJ iq j : Nat} (G : GF st m q₀ kJ (dJf q₀)) (hiq : iq < kJ)
    {cvT : ConstantVal} {caps : IndCaps}
    (hfind : env₂.find? ((D).pinAt (q₀ + iq)).J = some (.indInfo cvT caps))
    {TV₁ : TargetView V} {ψ₁ : Name → Nat} {Ds₁ : List AnnotTerm} {lvls₁ : List Level}
    {tg₁ : Nat → Nat} {tls₁ : List (List (Nat × Nat × AnnotTerm))} {Eis₁ : List (List AnnotTerm)}
    {Fs₁ Es₁ : List AnnotTerm} {rs₁ : List Bool} {ρ₁ : Nat → V} {base₁ : Nat}
    {M Z : Nat → V}
    {cA : ConstantVal × Nat} (hj : ((dJf q₀).ctorsM iq)[j]? = some cA)
    (hψ : ∀ pp ∈ cA.1.levelParams, ψ₁ pp = (((D).pinAt (q₀ + iq)).ψJ ψ) pp)
    (hρ : ∀ v, v < (dJf q₀).nP → consList (Ds₁.map (interp V ρ₁)) ρ₁ v = ((D).pinFrame (q₀ + iq) ψ ρp) v)
    (hwK : (dJf q₀).w ψ₁ = (dJf q₀).w (((D).pinAt (q₀ + iq)).ψJ ψ))
    (huT : ∀ l, (dJf q₀).uT ((dJf q₀).tgts iq j l) ψ₁
      = (dJf q₀).uT ((dJf q₀).tgts iq j l) (((D).pinAt (q₀ + iq)).ψJ ψ))
    (hIdsLen : ((dJf q₀).IdsM iq ψ₁).length = ((dJf q₀).IdsM iq (((D).pinAt (q₀ + iq)).ψJ ψ)).length)
    (hw₁ : (dJf q₀).w ψ₁ = TV₁.w)
    (hu₁ : ∀ i', i' < kJ → TV₁.u (base₁ + i') = (dJf q₀).uM i' ψ₁)
    (h₁ : CopyCtorShape TV₁ m.acval (dJf q₀) ψ₁ Ds₁ cvT.levelParams lvls₁ tg₁ tls₁ Eis₁ ρ₁
      iq j base₁ kJ Fs₁ rs₁ Es₁)
    (hdom₁ : ∀ l, l < (((dJf q₀).Fss iq ψ₁).getD j []).length → rs₁.getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (Ds₁.map (interp V ρ₁)) ρ₁) ((((dJf q₀).Fss iq ψ₁).getD j []).take l) fs₁ →
      slotSet TV₁.w (TV₁.u (tg₁ l)) (consList fs₁ ρ₁) (tls₁.getD l []) (Eis₁.getD l [])
          (M (tg₁ l))
        ⊆ˢ interp V (consList fs₁ (consList (Ds₁.map (interp V ρ₁)) ρ₁)) ((((dJf q₀).Fss iq ψ₁).getD j []).getD l default))
    (hent₂ : ∀ l, l < (((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).length →
      (((dJf q₀).rss iq).getD j []).getD l false = false →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit ((D).pinFrame (q₀ + iq) ψ ρp) ((((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).take l) fs₁ →
      interp V (consList fs₁ ((D).pinFrame (q₀ + iq) ψ ρp)) ((((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).getD l default)
        ⊆ˢ slotSet (f₀.s.eval ψ) (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) (consList fs₁ ρp)
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l []) (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)))
    (hrel : ∀ l, l < (((dJf q₀).Fss iq ψ₁).getD j []).length → (((dJf q₀).rss iq).getD j []).getD l false = true →
      ∀ t', SetTheory.app (M (tg₁ l)) t' ⊆ˢ SetTheory.app (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) t')
    (t : V) (fs : List V)
    (hfit : FitsFrom rs₁ (fun i' ρ => slotSet TV₁.w (TV₁.u (tg₁ i')) ρ (tls₁.getD i' [])
        (Eis₁.getD i' []) (M (tg₁ i'))) 0 ρ₁ Fs₁ fs)
    (hidx : ∀ l, l < ((dJf q₀).IdsM iq ψ₁).length →
      interp V (consList fs ρ₁) (Es₁.getD l default) = projS l t) :
    FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) [])
      (fun l ρ => slotSet (f₀.s.eval ψ) (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) ρ
        (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
        (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l []) (Z (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)))
      0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []) fs ∧
    (∀ l, l < (blockIds b.nP ppsF ψ (p.k + q₀ + iq)).length →
      interp V (consList fs ρp)
          (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l default) = projS l t) := by
  have hiqk : iq < (dJf q₀).k := G.syn.kEq ▸ hiq
  have hsh := G.shape iq hiq cvT caps hfind ψ ρp hρp iq j hiq (List.getElem?_eq_some_iff.mp hj).1
  unfold CopyShapeA at hsh
  have hwb : (dJf q₀).w (((D).pinAt (q₀ + iq)).ψJ ψ) = f₀.s.eval ψ := G.syn.w iq hiq ψ
  have hnI : (blockIds b.nP ppsF ψ (p.k + q₀ + iq)).length
      = ((dJf q₀).IdsM iq (((D).pinAt (q₀ + iq)).ψJ ψ)).length := by
    rw [G.idx iq hiq ψ iq hiq, instTele_length]
  exact copyTransfer_via G.syn.reps hiqk G.syn.kEq hj hψ hρ hwK huT hIdsLen hw₁ hwb hu₁
    (fun i' hi' => by
      show nestedU p.k W pinsS ψ (p.k + q₀ + i') = _
      rw [Nat.add_assoc, nestedU_pin]
      exact G.syn.pinU iq hiq ψ i' hi')
    rfl hnI h₁ hsh hdom₁ hent₂ hrel t fs hfit hidx


/-- **`hpair` at a MEMBER class of the root** (task #315 L-E, DESIGN
§U.72): `nestedPinPair_mem` with its three premises discharged —
`hdom₁` by `slotDomT_relMeet` (the relational meet is in the
container's tuple space and below its extended carrier), `hrel` by
`nestedPinWalk_mem` through `app_relMeet_le_rel`, and `hentR` by
`nestedPinEntryOut` — together with the pair's other data: the
block's group of the pin IS the root group (`ClassPinAt`'s own
conjunct, spent here), the index membership (`nestedIdx_of_group`) and
the injections' identity (the two sides' level assignments being
literally equal, `ψJEq`).

The remaining premises are the two the induction owns: `hIH` (the rank
induction's hypothesis at the pins it has already closed) and `hout`
(`nestedPinRankOk`'s clause (2): an `ordF`-right target leaves the
instance). -/
theorem nestedPinPairAt_mem (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {ciR : ContainerInfo} (CR : ContainerModeled m ciR (dJf r))
    {B : ContainerInfo → BlockModel V} (hB : EnvBlocksOf m B)
    {pcR : Nat → PinCtors V} (hshR : PinShapes m B (dJf r) pcR)
    {S : Nat → Prop}
    {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length → S q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Pf (q₀ + i) = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
    {c j : Nat} (hc : c < kR) (hjl : j < ((dJf r).ctorsM c).length)
    (hout : ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + r + c) + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + r + c) + j) []).getD l false = true →
      (((dJf r).rss c).getD j []).getD l false = false → ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) < p.k → S ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0) - p.k))
    (t : V) (fs : List V)
    (hfit : (dJf r).ChainFitT pcR (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) (relMeet ((dJf r).idxT (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) ((dJf r).famAt (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) (lfpTuple ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) ((dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))) (fun c' bb => ∃ q', bb = p.k + q' ∧ ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r c' q') (p.k + pinsS.length) (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))) t c j fs)
    (ht : t ∈ˢ (dJf r).idxT (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) c) :
    j < ((dJf r).ctorsM c).length ∧
    t ∈ˢ (D).idx ψ ρp (p.k + r + c) ∧
    (dJf r).injT pcR (((D).pinAt r).ψJ ψ) c j fs = (dJf r).inj (((D).pinAt (r + c)).ψJ ψ) c j fs ∧
    FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + r + c) + j) [])
      (fun l ρ => slotSet (f₀.s.eval ψ) (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0)) ρ
        (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l [])
        (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l []) ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0)))
      0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + r + c) + j) []) fs ∧
    (∀ l, l < (blockIds b.nP ppsF ψ (p.k + r + c)).length →
      interp V (consList fs ρp)
          (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (p.k + r + c) + j) []).getD l default) = projS l t) := by
  have hck : c < (dJf r).k := GR.syn.kEq ▸ hc
  have hkpos : 0 < (dJf r).k := GR.syn.kEq ▸ GR.syn.kpos
  have hj : ((dJf r).ctorsM c)[j]? = some (((dJf r).ctorsM c).getD j default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; rfl
  have hψeq : ((D).pinAt (r + c)).ψJ ψ = (((D).pinAt r).ψJ ψ) :=
    (GR.syn.ψJEq c 0 hc GR.syn.kpos ψ).trans (by rw [Nat.add_zero])
  have hDseq : ((D).pinAt (r + c)).Ds ψ = ((D).pinAt r).Ds ψ := GR.syn.sameDs c hc ψ
  have hρR : Sat V ((dJf r).params (((D).pinAt r).ψJ ψ)).reverse ((D).pinFrame r ψ ρp) := by
    obtain ⟨ρ, as, hρe, hsp⟩ := spineOfSat_params (D) hρp
    subst hρe
    have := (dJf r).satOfSpine (GR.syn.DsFit 0 GR.syn.kpos ψ ρ as hsp)
    rw [Nat.add_zero] at this
    exact this
  -- the walk, as the transfer wants it
  have hwalk := nestedPinWalk_mem m hgroups hρp GR CR hB hshR hc hj
  have hrel : ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + r + c) + j) []).length →
      (((dJf r).rss c).getD j []).getD l false = true →
      ∀ t', SetTheory.app ((relMeet ((dJf r).idxT (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) ((dJf r).famAt (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) (lfpTuple ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) ((dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))) (fun c' bb => ∃ q', bb = p.k + q' ∧ ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r c' q') (p.k + pinsS.length) (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))) ((dJf r).tgts c j l)) t' ⊆ˢ SetTheory.app ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + r + c) + j) []).getD l 0)) t' := by
    intro l hl hr t'
    obtain ⟨q', hq'e, hcp⟩ := hwalk l hl hr
    have hq'lt : q' < pinsS.length := hcp.1.qLt
    rw [hq'e]
    exact app_relMeet_le_rel (by omega) ⟨q', rfl, hcp⟩ t'
  refine ⟨hjl, ?_, ?_, nestedPinPair_mem m hρp GR hc hj
    ((dJf r).slotDomT_relMeet GR.syn.reps (GR.syn.typed _) (GR.syn.pinsTyped _) hck hj hρR hkpos)
    hrel (nestedPinEntryOut hμ h hbk m hleafM dJf hgroups hρp GR hIH hPfGroup hc hj hout) t fs hfit⟩
  · rw [nestedIdx_of_group GR hc, hψeq, hDseq]
    rw [(dJf r).idxT_of_mem hck (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)] at ht
    exact ht
  · rw [(dJf r).injT_of_mem hck (((D).pinAt r).ψJ ψ), hψeq]


/-- **`hpair` at a PIN class of the root** (task #315 L-E, DESIGN
§U.87): the pin-side twin of `nestedPinPairAt_mem`.
`nestedPinPair_pin` with every premise discharged — `hdom₁` by
`copyEntryAt_pin` through `slotSet_mono_app`/`app_relMeet_subset` (the
relational meet is below the extended carrier, at which the entry is
an EQUALITY), `hent₂` by `nestedPinEntryOut` (general in the group
since §U.72), `hrel` by `classPinAt_of_walk` through
`app_relMeet_le_rel`, the sort and the member index universes by
`params_congr`, the pin index universes by `ContainerPinParams`, and
the fit itself by `chainFitT_of_pin` — together with the pair's other
data: the index membership (`nestedIdx_eq_pinIdx` at the pair's own
index clause) and the injections' identity (`PinRecLaws.injW` on the
root's side, `NestedPinGroupSyn.inj` on the block's, at one sort).

What is left are the two premises the rank induction owns, `hIH` and
`hout`, exactly as at a member class. -/
theorem nestedPinPairAt_pin (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {q₀ kJ iq j : Nat} (G : GF st m q₀ kJ (dJf q₀)) (hiq : iq < kJ)
    {dR : BlockModel V}
    {r q₀' : Nat} {ψR : Name → Nat} {ρR : Nat → V}
    (S₂ : PinGroupView dR (dJf q₀) q₀' kJ)
    {ciK : ContainerInfo} (CK : ContainerModeled m ciK (dJf q₀))
    {IK : Name} (hciK : ConLeche.containerInfo? env₂ IK = some ciK)
    {cvK : ConstantVal} {capsK : IndCaps} (hfK : env₂.find? IK = some (.indInfo cvK capsK))
    (hpp : ContainerPinParams (V := V) cvK (dJf q₀))
    (hOwn : ∀ qq, qq < (dJf q₀).nPins → ∃ (q₀'' kk'' i'' : Nat) (dJ'' : BlockModel V),
      qq = q₀'' + i'' ∧ i'' < kk'' ∧ PinGroupView (dJf q₀) dJ'' q₀'' kk'' ∧ IsBlockModels m dJ'')
    (hrepsR : IsBlockModels m dR)
    (hρR : Sat V (dR.params ψR).reverse ρR) (hkR : 0 < dR.k)
    (hviews : ∀ qq, qq < dR.nPins → ∃ (a bb c : Nat) (dJ' : BlockModel V),
      qq = a + c ∧ c < bb ∧ PinGroupView dR dJ' a bb ∧ IsBlockModels m dJ')
    {pcR : Nat → PinCtors V} (hp : PinRecLaws m dR pcR) {lvls₁ : List Level}
    (h₁ : CopyCtorShape (dR.targetView m.acval ψR) m.acval (dJf q₀) ((dR.pinAt q₀').ψJ ψR) ((dR.pinAt q₀').Ds ψR) cvK.levelParams lvls₁
      (fun l => (pcR (q₀' + iq)).tgts j l) (((pcR (q₀' + iq)).tlss ψR).getD j []) (((pcR (q₀' + iq)).Eiss ψR).getD j []) ρR iq j
      (dR.k + q₀') kJ (((pcR (q₀' + iq)).Fss ψR).getD j []) ((pcR (q₀' + iq)).rss.getD j []) (((pcR (q₀' + iq)).Ess ψR).getD j []))
    (hψ₁ : ((dR.pinAt q₀').ψJ ψR) = Level.substFn ψR cvK.levelParams lvls₁)
    (hpinψR : ∀ qq, qq < dR.nPins → ∀ (cvT : ConstantVal) (caps : IndCaps),
      env₂.find? (dR.pinAt qq).J = some (.indInfo cvT caps) →
      (dR.pinAt qq).lvls.length = cvT.levelParams.length ∧
      ∀ φ : Name → Nat, (dR.pinAt qq).ψJ φ
        = Level.substFn φ cvT.levelParams (dR.pinAt qq).lvls)
    (hpinψD : ∀ qq, qq < pinsS.length → ∀ (cvT : ConstantVal) (caps : IndCaps),
      env₂.find? ((D).pinAt qq).J = some (.indInfo cvT caps) →
      ∀ φ : Name → Nat, ((D).pinAt qq).ψJ φ
        = Level.substFn φ cvT.levelParams ((D).pinAt qq).lvls)
    (hDsLenD : ∀ qq, qq < pinsS.length → ((D).pinAt qq).nPJ ≤ (((D).pinAt qq).Ds ψ).length)
    (hψ : ∀ pp ∈ cvK.levelParams, ((dR.pinAt q₀').ψJ ψR) pp = (((D).pinAt (q₀ + iq)).ψJ ψ) pp)
    (hfr : ∀ v, v < (dJf q₀).nP → dR.pinFrame q₀' ψR ρR v = (D).pinFrame (q₀ + iq) ψ ρp v)
    (hidxP : dR.idxT ψR ρR (dR.k + (q₀' + iq)) = (D).pinIdx (q₀ + iq) ψ ρp)
    {S : Nat → Prop}
    {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length → S q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Pf (q₀ + i) = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
    (hout : ∀ l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l false = true →
      (((dJf q₀).rss iq).getD j []).getD l false = false → ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) < p.k → S ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) - p.k))
    (hjl : j < ((dJf q₀).ctorsM iq).length)
    (t : V) (fs : List V) (ht : t ∈ˢ dR.idxT ψR ρR (dR.k + (q₀' + iq)))
    (hfitT : dR.ChainFitT pcR ψR ρR (relMeet (dR.idxT ψR ρR) (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR))) (fun c' bb => ∃ q'', bb = p.k + q'' ∧ ClassPinAt env₂ (D) dR ψ ψR ρp ρR r c' q'') (p.k + pinsS.length) (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))) t (dR.k + (q₀' + iq)) j fs) :
    j < ((dJf q₀).ctorsM iq).length ∧
    t ∈ˢ (D).idx ψ ρp (p.k + q₀ + iq) ∧
    dR.injT pcR ψR (dR.k + (q₀' + iq)) j fs = (dJf q₀).inj (((D).pinAt (q₀ + iq)).ψJ ψ) iq j fs ∧
    FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) [])
      (fun l ρ => slotSet (f₀.s.eval ψ) (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) ρ
        (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
        (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l []) ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)))
      0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []) fs ∧
    (∀ l, l < (blockIds b.nP ppsF ψ (p.k + q₀ + iq)).length →
      interp V (consList fs ρp)
          (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l default) = projS l t) := by
  have hiqK : iq < (dJf q₀).k := S₂.kEq ▸ hiq
  have hqK : q₀' + iq < dR.nPins := by have := S₂.seg; omega
  have hnc : ¬ dR.k + (q₀' + iq) < dR.k := by omega
  have hsub : dR.k + (q₀' + iq) - dR.k = q₀' + iq := by omega
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, hψJ⟩ := G.syn.stored iq hiq
  have hmemName : (dJf q₀).memberName iq = ((D).pinAt (q₀ + iq)).J := hI.member
  have hlps : cvT.levelParams = cvK.levelParams :=
    CK.memberLpsI hciK hfK hiqK (by rw [hmemName]; exact hfind)
  have hpar := CK.params_congr hciK hfK hψ hiqK
  have hS₁ : PinGroupView (D) (dJf q₀) q₀ kJ := pinGroupView_of_syn G.syn
  have hj : ((dJf q₀).ctorsM iq)[j]? = some (((dJf q₀).ctorsM iq).getD j default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; rfl
  have hψ2f : (((D).pinAt (q₀ + iq)).ψJ ψ) = ((D).pinAt q₀).ψJ ψ := (hS₁.same iq hiq ψ).1
  have hDs2f : (((D).pinAt (q₀ + iq)).Ds ψ) = ((D).pinAt q₀).Ds ψ := (hS₁.same iq hiq ψ).2
  have hlvls2 : (((D).pinAt (q₀ + iq)).lvls) = ((D).pinAt q₀).lvls := hS₁.lvls iq hiq
  have hcaLps : ((((dJf q₀).ctorsM iq).getD j default).1).levelParams = cvT.levelParams :=
    (hI.ctors iq j _ hiqK hj).2.1
  have hψcA : ∀ pp ∈ ((((dJf q₀).ctorsM iq).getD j default).1).levelParams,
      ((dR.pinAt q₀').ψJ ψR) pp = (((D).pinAt (q₀ + iq)).ψJ ψ) pp := by
    rw [hcaLps, hlps]; exact hψ
  have hFss : ((dJf q₀).Fss iq ((dR.pinAt q₀').ψJ ψR)).getD j []
      = ((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j [] := (hI.ctor_params hj hψcA).1
  have hfrm2 : (D).pinFrame (q₀ + iq) ψ ρp = (D).pinFrame q₀ ψ ρp := by
    unfold BlockModel.pinFrame; rw [hDs2f]
  -- the block's copy shape, at the base pin's record
  have hsh := G.shape iq hiq cvT caps hfind ψ ρp hρp iq j hiq hjl
  unfold CopyShapeA at hsh
  -- the numeric agreements
  have hwK : (dJf q₀).w ((dR.pinAt q₀').ψJ ψR) = (dJf q₀).w (((D).pinAt (q₀ + iq)).ψJ ψ) := hpar.2.2
  have huT : ∀ l, (dJf q₀).uT ((dJf q₀).tgts iq j l) ((dR.pinAt q₀').ψJ ψR) = (dJf q₀).uT ((dJf q₀).tgts iq j l) (((D).pinAt (q₀ + iq)).ψJ ψ) := by
    intro l
    by_cases hnt : (dJf q₀).tgts iq j l < (dJf q₀).k
    · rw [BlockModel.uT_of_mem hnt, BlockModel.uT_of_mem hnt]
      exact (CK.params_congr hciK hfK hψ hnt).1
    · rw [BlockModel.uT_of_pin hnt, BlockModel.uT_of_pin hnt]
      by_cases hqq : (dJf q₀).tgts iq j l - (dJf q₀).k < (dJf q₀).nPins
      · exact ((hpp _ hqq).2.2 _ _ hψ).1
      · unfold BlockModel.pinAt
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (show (dJf q₀).pins.length ≤ _ from by
            unfold BlockModel.nPins at hqq; omega)]
        rfl
  have hIdsLen : ((dJf q₀).IdsM iq ((dR.pinAt q₀').ψJ ψR)).length = ((dJf q₀).IdsM iq (((D).pinAt (q₀ + iq)).ψJ ψ)).length := by
    unfold BlockModel.IdsM; rw [hpar.2.1]
  have hwR : (dJf q₀).w ((dR.pinAt q₀').ψJ ψR) = (dR.targetView m.acval ψR).w := S₂.w ψR
  have hu₁ : ∀ i', i' < kJ → (dR.targetView m.acval ψR).u (dR.k + q₀' + i') = (dJf q₀).uM i' ((dR.pinAt q₀').ψJ ψR) := by
    intro i' hi'
    show dR.uT (dR.k + q₀' + i') ψR = _
    rw [Nat.add_assoc, BlockModel.uT_of_pin (by omega) ψR, Nat.add_sub_cancel_left]
    exact S₂.pinU i' hi' ψR
  -- the walk
  have hrel : ∀ l, l < (((dJf q₀).Fss iq ((dR.pinAt q₀').ψJ ψR)).getD j []).length →
      (((dJf q₀).rss iq).getD j []).getD l false = true →
      ∀ t', SetTheory.app ((relMeet (dR.idxT ψR ρR) (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR))) (fun c' bb => ∃ q'', bb = p.k + q'' ∧ ClassPinAt env₂ (D) dR ψ ψR ρp ρR r c' q'') (p.k + pinsS.length) (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))) ((pcR (q₀' + iq)).tgts j l)) t' ⊆ˢ SetTheory.app ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) t' := by
    intro l hl hr t'
    have hl₂ : l < (((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).length := by
      rw [← hFss]; exact hl
    obtain ⟨hte, hcp⟩ := classPinAt_of_walk CK hciK hfK hpp hOwn hS₁ S₂ h₁
      (by rw [nestedBlockModel_targetView m ψ, ← hψ2f, ← hDs2f, ← hlps]; exact hsh)
      hψ₁ (by rw [← hψ2f, ← hlps]; exact hψJ ψ)
      hpinψR hpinψD hDsLenD (fun pp hp => by rw [← hψ2f]; exact hψ pp hp)
      (fun v hv => by rw [← hfrm2]; exact hfr v hv) hiq hl (by rw [← hψ2f]; exact hl₂) hj hr
    have hq'lt : (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) - p.k < pinsS.length := hcp.1.qLt
    have hte' : (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) = p.k + ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) - p.k) := hte
    have key := app_relMeet_le_rel (Is := dR.idxT ψR ρR)
      (X := dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR)))
      (R := fun c' bb => ∃ q'', bb = p.k + q'' ∧ ClassPinAt env₂ (D) dR ψ ψR ρp ρR r c' q'')
      (k' := p.k + pinsS.length)
      (Y := lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))
      (a := (pcR (q₀' + iq)).tgts j l) (b := p.k + ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) - p.k))
      (by omega) ⟨(((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) - p.k, rfl, hcp⟩ t'
    rw [← hte'] at key
    exact key
  -- `hdom₁`: the meet is below the extended carrier, at which the entry is an EQUALITY
  have hdom₁ : ∀ l, l < (((dJf q₀).Fss iq ((dR.pinAt q₀').ψJ ψR)).getD j []).length →
      ((pcR (q₀' + iq)).rss.getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit (consList (((dR.pinAt q₀').Ds ψR).map (interp V ρR)) ρR)
        ((((dJf q₀).Fss iq ((dR.pinAt q₀').ψJ ψR)).getD j []).take l) fs₁ →
      slotSet (dR.targetView m.acval ψR).w ((dR.targetView m.acval ψR).u ((pcR (q₀' + iq)).tgts j l)) (consList fs₁ ρR)
          ((((pcR (q₀' + iq)).tlss ψR).getD j []).getD l []) ((((pcR (q₀' + iq)).Eiss ψR).getD j []).getD l [])
          ((relMeet (dR.idxT ψR ρR) (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR))) (fun c' bb => ∃ q'', bb = p.k + q'' ∧ ClassPinAt env₂ (D) dR ψ ψR ρp ρR r c' q'') (p.k + pinsS.length) (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))) ((pcR (q₀' + iq)).tgts j l))
        ⊆ˢ interp V (consList fs₁ (consList (((dR.pinAt q₀').Ds ψR).map (interp V ρR)) ρR))
            ((((dJf q₀).Fss iq ((dR.pinAt q₀').ψJ ψR)).getD j []).getD l default) := by
    intro l hl hrs fs₁ hl₁ hsp
    rw [BlockModel.copyEntryAt_pin hrepsR G.syn.reps hkR S₂ hviews hρR
      (CK.typed ((dR.pinAt q₀').ψJ ψR)).1 (CK.typed ((dR.pinAt q₀').ψJ ψR)).2.2 hiq hj h₁ hl hrs fs₁ hl₁ hsp]
    exact slotSet_mono_app (fun t' => app_relMeet_subset _ _ _ _ _ _ t')
  -- `hent₂`: the externals, at the auxiliary carrier
  have hent₂ : ∀ l, l < (((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).length →
      (((dJf q₀).rss iq).getD j []).getD l false = false →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l →
      SpineFit ((D).pinFrame (q₀ + iq) ψ ρp)
        ((((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).take l) fs₁ →
      interp V (consList fs₁ ((D).pinFrame (q₀ + iq) ψ ρp))
          ((((dJf q₀).Fss iq (((D).pinAt (q₀ + iq)).ψJ ψ)).getD j []).getD l default)
        ⊆ˢ slotSet (f₀.s.eval ψ) (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) (consList fs₁ ρp)
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l []) ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) := by
    intro l hl hr' hrs fs₁ hl₁ hsp
    have hgout : ¬ (p.k + q₀ ≤ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) ∧ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) < p.k + q₀ + kJ) := by
      rcases hsh.ordF l hl hr' with ⟨hrC, -⟩ | ⟨-, hg, -, -⟩
      · rw [hrC] at hrs; exact absurd hrs Bool.false_ne_true
      · exact hg
    rw [hψ2f, hfrm2] at hsp ⊢
    exact nestedPinEntryOut hμ h hbk m hleafM dJf hgroups hρp G hIH hPfGroup hiq hj hout
      l (by rw [hsh.len]; exact hl) hrs hr' hgout fs₁ hl₁ hsp
  -- the root's fit, read off the pin's constructors
  rw [BlockModel.chainFitT_of_pin hnc, hsub] at hfitT
  have hIdsR : (dR.pinAt (q₀' + iq)).Ids ψR = (dJf q₀).IdsM iq ((dR.pinAt q₀').ψJ ψR) := by
    unfold PinSyn.Ids
    rw [S₂.pinPps iq hiq, S₂.pinNP iq hiq, (S₂.same iq hiq ψR).1]
    rfl
  refine ⟨hjl, ?_, ?_, nestedPinPair_pin m hρp G hiq hfind hj
    (by rw [hcaLps, hlps]; exact hψ) (fun v hv => hfr v hv) hwK huT hIdsLen hwR hu₁
    (by rw [hlps]; exact h₁)
    hdom₁ hent₂ hrel t fs hfitT.1 (fun l hl => hfitT.2 l (by rw [hIdsR]; exact hl))⟩
  · -- the index membership
    rw [nestedIdx_eq_pinIdx G hiq, ← hidxP]
    exact ht
  · -- the injections' identity
    rw [dR.injT_of_pin hnc ψR, hsub, hp.injW ψR (q₀' + iq) hqK j fs,
      G.syn.inj (((D).pinAt (q₀ + iq)).ψJ ψ) iq j fs, ← hwK, hwR]
    rfl


/-- **`hpair`, THE CASE SPLIT** (task #315 L-E, DESIGN §U.87 (b)): the
two halves above, joined — at a `ClassPinAt` pair `(c, q)` of the
ROOT GROUP `r`, the block's copy of pin `q`'s constructor `j` fits the
auxiliary carrier at the same spine with the same result indices and
one injection, which is `instanceLe_of_pair`'s `hpair` verbatim.

The split is on the class kind and both arms are bookkeeping:

* a MEMBER class — `ClassPinAt`'s own conjunct gives `q = r + c`, and
  `NestedPinGroupSyn.grp` reads `grpBase`/`grpSize` off the pin table
  on BOTH sides, so the block's group of `q` IS the root group;
  `nestedPinPairAt_mem` applies verbatim;
* a PIN class — the root's `PinShapes` at `q - dR.k` gives its group
  and its container `ci'`; `ClassPin.name` puts `containerInfo?` at
  ONE name, `hdJfB` identifies the block's group's model with `B ci'`,
  `ContainerModeled.memberName_inj` forces the two member indices
  together and `PinGroupView.kEq` the two group sizes; then
  `nestedPinPairAt_pin` applies, with the container's record taken at
  `ci'`.

The pin half's container-side premises are PER-CONTAINER, so they are
carried QUANTIFIED — `hppB` is `ContainerPinParams` at every stored
container, beside `EnvBlocksOf`, which is the form that becomes free
the moment M7-3 makes it a `ContainerModeled` clause. -/
theorem nestedPinPairAt (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {B : ContainerInfo → BlockModel V} (hB : EnvBlocksOf m B)
    (hppB : ∀ (J : Name) (ci : ContainerInfo) (cv : ConstantVal) (caps : IndCaps),
      ConLeche.containerInfo? env₂ J = some ci → env₂.find? J = some (.indInfo cv caps) →
      ContainerPinParams (V := V) cv (B ci))
    (hdJfB : ∀ (q₀ kJ iq : Nat) (ci : ContainerInfo), iq < kJ → GF st m q₀ kJ (dJf q₀) →
      ConLeche.containerInfo? env₂ ((D).pinAt (q₀ + iq)).J = some ci → dJf q₀ = B ci)
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {ciR : ContainerInfo} (CR : ContainerModeled m ciR (dJf r))
    {pcR : Nat → PinCtors V} (hpR : PinRecLaws m (dJf r) pcR)
    (hshR : PinShapes m B (dJf r) pcR)
    {S : Nat → Prop}
    {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length → S q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Pf (q₀ + i) = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
    (hout : ∀ q₀ iq j l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l false = true →
      (((dJf q₀).rss iq).getD j []).getD l false = false → ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) < p.k → S ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) - p.k)) :
    ∀ c q, c < (dJf r).kT →
      ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r c q →
      ∀ t, t ∈ˢ (dJf r).idxT (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) c →
      ∀ j fs, j < ((dJf r).ctorsT pcR c).length →
      (dJf r).ChainFitT pcR (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
        (relMeet ((dJf r).idxT (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
          ((dJf r).famAt (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
            (lfpTuple ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)) ((dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))))
          (fun c' bb => ∃ q', bb = p.k + q' ∧ ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r c' q')
          (p.k + pinsS.length) (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))) t c j fs →
      ∃ q₀ kJ iq, q = q₀ + iq ∧ iq < kJ ∧ GF st m q₀ kJ (dJf q₀) ∧
        j < ((dJf q₀).ctorsM iq).length ∧
        t ∈ˢ (D).idx ψ ρp (p.k + q₀ + iq) ∧
        (dJf r).injT pcR (((D).pinAt r).ψJ ψ) c j fs = (dJf q₀).inj (((D).pinAt (q₀ + iq)).ψJ ψ) iq j fs ∧
        FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) [])
          (fun l ρ => slotSet (f₀.s.eval ψ) (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) ρ
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l []) ((lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)))
          0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []) fs ∧
        (∀ l, l < (blockIds b.nP ppsF ψ (p.k + q₀ + iq)).length →
          interp V (consList fs ρp)
              (((mutEss0 ctorsA.length esF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l default) = projS l t) := by
  intro c q hcT hcp t ht j fs hj hfit
  by_cases hcm : c < (dJf r).k
  · -- a MEMBER class of the root: the block's group IS the root group
    obtain rfl : q = r + c := hcp.2 hcm
    have hc : c < kR := GR.syn.kEq ▸ hcm
    have hjl : j < ((dJf r).ctorsM c).length := by
      rw [BlockModel.ctorsT_of_mem hcm] at hj; exact hj
    obtain ⟨-, htm, hinj, hslot, heq⟩ :=
      nestedPinPairAt_mem hμ h hbk m hleafM dJf hgroups hρp GR CR hB hshR hIH hPfGroup hc hjl
        (hout r c j) t fs hfit ht
    exact ⟨r, kR, c, rfl, hc, GR, hjl, htm, hinj, hslot, heq⟩
  · -- a PIN class of the root: the root's shapes name the container
    have hqK : c - (dJf r).k < (dJf r).nPins := by
      have := hcT; unfold BlockModel.kT at this; omega
    have hcE : c = (dJf r).k + (c - (dJf r).k) := by omega
    obtain ⟨q₀', kK', i'', ci', hqKe, hi'', hci', S₂', hcount', hshape'⟩ := hshR _ hqK
    -- `ClassPin.name`: the two sides' `containerInfo?` is at ONE name
    have hname : ((dJf r).pinAt (c - (dJf r).k)).J = ((D).pinAt q).J := by
      have := hcp.1.name
      rwa [(dJf r).nameT_of_pin hcm] at this
    have hci₂ : ConLeche.containerInfo? env₂ ((D).pinAt q).J = some ci' := by
      rw [← hname]; exact hci'
    -- the block's group of the pin
    have hqLt : q < pinsS.length := hcp.1.qLt
    obtain ⟨q₀, kJ, iq, hqe, hiq, G⟩ := hgroups q hqLt
    have hdJf : dJf q₀ = B ci' := hdJfB q₀ kJ iq ci' hiq G (by rw [← hqe]; exact hci₂)
    have CK : ContainerModeled m ci' (dJf q₀) := by rw [hdJf]; exact (hB _ ci' hci').1
    have S₂'' : PinGroupView (dJf r) (dJf q₀) q₀' kK' := by rw [hdJf]; exact S₂'
    have hkK : kK' = kJ := by
      have h1 := S₂''.kEq
      have h2 := G.syn.kEq
      omega
    subst hkK
    -- the two member indices agree
    have hi''k : i'' < (dJf q₀).k := by rw [S₂''.kEq]; exact hi''
    have hiqk : iq < (dJf q₀).k := by rw [G.syn.kEq]; exact hiq
    have hnm₁ : ((dJf r).pinAt (q₀' + i'')).J = (dJf q₀).memberName i'' := S₂''.name i'' hi''
    have hnm₂ : ((D).pinAt (q₀ + iq)).J = (dJf q₀).memberName iq :=
      (pinGroupView_of_syn G.syn).name iq hiq
    have hii : i'' = iq := by
      refine CK.memberName_inj hci' hi''k hiqk ?_
      rw [← hnm₁, ← hnm₂, ← hqe, hqKe] at *
      exact hname
    subst hii
    -- the block group's stored constant, at the pin's own name
    obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, hψJ⟩ := G.syn.stored i'' hiq
    have hfindq : env₂.find? ((D).pinAt q).J = some (.indInfo cvT caps) := by
      rw [hqe]; exact hfind
    have hfindR : env₂.find? (((dJf r).pinAt (q₀' + i'')).J) = some (.indInfo cvT caps) := by
      rw [← hqKe, hname]; exact hfindq
    -- the root's frame
    have hρR : Sat V ((dJf r).params (((D).pinAt r).ψJ ψ)).reverse ((D).pinFrame r ψ ρp) := by
      obtain ⟨ρ, as, hρe, hsp⟩ := spineOfSat_params (D) hρp
      subst hρe
      have := (dJf r).satOfSpine (GR.syn.DsFit 0 GR.syn.kpos ψ ρ as hsp)
      rw [Nat.add_zero] at this
      exact this
    have hkR : 0 < (dJf r).k := GR.syn.kEq ▸ GR.syn.kpos
    -- the constructor count, off the root's shapes
    have hjl : j < ((dJf q₀).ctorsM i'').length := by
      rw [BlockModel.ctorsT_of_pin hcm, hqKe, hcount' i'' hiq, ← hdJf] at hj
      exact hj
    -- the container's own pins, viewed
    obtain ⟨-, pcK, hpcK, hshK⟩ := hB _ ci' hci'
    have hOwn : ∀ qq, qq < (dJf q₀).nPins → ∃ (q₀'' kk'' i₂ : Nat) (dJ'' : BlockModel V),
        qq = q₀'' + i₂ ∧ i₂ < kk'' ∧ PinGroupView (dJf q₀) dJ'' q₀'' kk'' ∧ IsBlockModels m dJ'' := by
      rw [hdJf]; exact hshK.views hB
    -- the pin data's congruence, at the container's own constant
    have hpp : ContainerPinParams (V := V) cvT (dJf q₀) := by
      rw [hdJf]
      exact hppB _ ci' cvT caps hci₂ hfindq
    -- the root's own copy shape at the pin
    have h₁ := hshape' (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) hρR i'' j hiq
      (by rw [← hdJf]; exact hjl) cvT caps hfindR
    rw [← hdJf] at h₁
    -- the pin's level law, at the base pin's record
    have hψ₁ : (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))
        = Level.substFn (((D).pinAt r).ψJ ψ) cvT.levelParams ((dJf r).pinAt q₀').lvls := by
      have := (CR.pinψ _ hqK cvT caps (by rw [hname]; exact hfindq)).2 (((D).pinAt r).ψJ ψ)
      rw [hqKe] at this
      rw [← (S₂''.same i'' hiq (((D).pinAt r).ψJ ψ)).1, ← S₂''.lvls i'' hiq]
      exact this
    -- the pair's own two agreements
    have hψ : ∀ pp ∈ cvT.levelParams, (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ)) pp
        = (((D).pinAt (q₀ + i'')).ψJ ψ) pp := by
      intro pp hpp'
      have := hcp.1.psi cvT caps hfindq pp hpp'
      rw [(dJf r).psiT_of_pin _ hcm, hqKe,
        (S₂''.same i'' hiq (((D).pinAt r).ψJ ψ)).1, hqe] at this
      exact this
    have hfr : ∀ v, v < (dJf q₀).nP → (dJf r).pinFrame q₀' (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) v
        = (D).pinFrame (q₀ + i'') ψ ρp v := by
      intro v hv
      have hnp : ((D).pinAt q).nPJ = (dJf q₀).nP := by
        rw [hqe]; exact G.syn.pinNP i'' hiq
      have := hcp.1.frame v (by rw [hnp]; exact hv)
      rw [(dJf r).frameT_of_pin hcm, hqKe] at this
      unfold BlockModel.pinFrame at this ⊢
      rw [(S₂''.same i'' hiq (((D).pinAt r).ψJ ψ)).2] at this
      rw [← hqe]
      exact this
    have hidxP : (dJf r).idxT (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) ((dJf r).k + (q₀' + i''))
        = (D).pinIdx (q₀ + i'') ψ ρp := by
      rw [← hqKe, ← hcE, ← hqe]; exact hcp.1.idx
    -- the block's pin table, read off the groups
    have hpinψD : ∀ qq, qq < pinsS.length → ∀ (cvT' : ConstantVal) (caps' : IndCaps),
        env₂.find? ((D).pinAt qq).J = some (.indInfo cvT' caps') →
        ∀ φ : Name → Nat, ((D).pinAt qq).ψJ φ
          = Level.substFn φ cvT'.levelParams ((D).pinAt qq).lvls := by
      intro qq hqq cvT' caps' hf' φ
      obtain ⟨a, kk, ii, rfl, hii, G'⟩ := hgroups qq hqq
      obtain ⟨cv₀, caps₀, -, -, -, -, hf₀, -, hlaw⟩ := G'.syn.stored ii hii
      obtain rfl : cv₀ = cvT' := (ConstantInfo.indInfo.inj (Option.some.inj (hf₀.symm.trans hf'))).1
      exact hlaw φ
    have hDsLenD : ∀ qq, qq < pinsS.length → ((D).pinAt qq).nPJ ≤ (((D).pinAt qq).Ds ψ).length := by
      intro qq hqq
      obtain ⟨a, kk, ii, rfl, hii, G'⟩ := hgroups qq hqq
      rw [G'.syn.pinNP ii hii, G'.syn.pinDsLen ii hii ψ]
      exact Nat.le_refl _
    -- the transfer at the pin class
    obtain ⟨-, htm, hinj, hslot, heq⟩ :=
      nestedPinPairAt_pin (r := r) hμ h hbk m hleafM dJf hgroups hρp G hiq S₂'' CK hci₂ hfindq hpp
        hOwn GR.syn.reps hρR hkR (hshR.views hB) hpR h₁ hψ₁ CR.pinψ hpinψD hDsLenD hψ hfr hidxP
        hIH hPfGroup (hout q₀ i'' j) hjl t fs (by rw [← hqKe, ← hcE]; exact ht)
        (by rw [← hqKe, ← hcE]; exact hfit)
    refine ⟨q₀, kK', i'', hqe, hiq, G, hjl, htm, ?_, hslot, heq⟩
    rw [hcE, hqKe]
    exact hinj


/-- **`htrans`, from the pair's transfer** (task #315 L-E, DESIGN §U.64
— the plumbing §U.58 (b) named): the transfer premise of
`instanceLe_of_classPin`, discharged from ONE per-pair fact — at a
`ClassPin` pair `(c, q)` and a fit of the root's class `c` at any
tuple `M`, the BLOCK's copy of pin `q`'s constructor `j` fits the
auxiliary carrier at the same spine with the same result indices, and
the two sides' injections are one.

Generic in `M`: step (3) does not read the tuple, so the relational
meet enters only through the premise, which is what
`copyTransfer_via` (the `pinF`/`recF` walk and each side's own
`ordF`-right reading law) and `copyTransfer_mem` deliver, and what
K.41's recorded pairing will close at the ROOT.  Instantiating
`M := relMeet …` gives `instanceLe_of_classPin`'s hypothesis
verbatim. -/
theorem htrans_of_walk (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {dR : BlockModel V} {pcR : Nat → PinCtors V} {ψR : Name → Nat} {ρR : Nat → V}
    {M : Nat → V} {Rel : Nat → Nat → Prop}
    (hpair : ∀ c q, c < dR.kT → Rel c q →
      ∀ t, t ∈ˢ dR.idxT ψR ρR c → ∀ j fs, j < (dR.ctorsT pcR c).length →
      dR.ChainFitT pcR ψR ρR M t c j fs →
      ∃ q₀ kJ iq, q = q₀ + iq ∧ iq < kJ ∧ GF st m q₀ kJ (dJf q₀) ∧
        j < ((dJf q₀).ctorsM iq).length ∧
        t ∈ˢ (D).idx ψ ρp (p.k + q₀ + iq) ∧
        dR.injT pcR ψR c j fs = (dJf q₀).inj (((D).pinAt (q₀ + iq)).ψJ ψ) iq j fs ∧
        FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) [])
          (fun l ρ => slotSet (f₀.s.eval ψ)
            (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) ρ
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
            (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
              (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)))
          0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []) fs ∧
        (∀ l, l < (blockIds b.nP ppsF ψ (p.k + q₀ + iq)).length →
          interp V (consList fs ρp)
              (((mutEss0 ctorsA.length esF ψ).getD
                (b.ownOffset (p.k + q₀ + iq) + j) []).getD l default)
            = projS l t)) :
    ∀ c, c < dR.kT → ∀ t, t ∈ˢ dR.idxT ψR ρR c → ∀ j fs, j < (dR.ctorsT pcR c).length →
      dR.ChainFitT pcR ψR ρR M t c j fs →
      ∀ q, p.k + q < p.k + pinsS.length → Rel c q →
        dR.injT pcR ψR c j fs
          ∈ˢ SetTheory.app (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
              (p.k + q)) t := by
  intro c hc t ht j fs hj hfit q _ hcp
  obtain ⟨q₀, kJ, iq, rfl, hiq, G, hjc, ht', hinj, hslot, heq⟩ :=
    hpair c _ hc hcp t ht j fs hj hfit
  rw [hinj, ← Nat.add_assoc]
  exact nestedPinInj_mem hμ h h3 hbk m dJf hgroups hρp G hiq hjc ht' hslot heq

/-- **`instanceLe` at the root, from the pair's transfer alone** (task
#315 L-E, DESIGN §U.64): `instanceLe_of_classPin` composed with
`htrans_of_walk`.  At a root whose container carries its block model
(`IsBlockModels`, `PinRecLaws` — its `BlockAt`), every class of the
root that is `ClassPin`-related to a block pin has its extended
carrier below the auxiliary carrier at that pin, and the ONLY residual
is the per-pair transfer: the two copies' fit (`copyTransfer_via` /
`copyTransfer_mem` under the `recF`/`pinF` walk) with the injections'
identity.

This is the whole of step (iii) above the rank induction
(`pins_le_of_instanceLe`): with `InstanceCovered` at the root — K.41's
recorded pairing — the pins' section of the entry theorem closes. -/
theorem instanceLe_of_pair (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {dR : BlockModel V} {pcR : Nat → PinCtors V} {ψR : Name → Nat} {ρR : Nat → V}
    (hreps : IsBlockModels m dR) (hp : PinRecLaws m dR pcR) (hk : 0 < dR.k)
    (hρR : Sat V (dR.params ψR).reverse ρR)
    {Rel : Nat → Nat → Prop}
    (hsub : ∀ c q, Rel c q → ClassPin env₂ (D) dR ψ ψR ρp ρR c q)
    (hpair : ∀ c q, c < dR.kT → Rel c q →
      ∀ t, t ∈ˢ dR.idxT ψR ρR c → ∀ j fs, j < (dR.ctorsT pcR c).length →
      dR.ChainFitT pcR ψR ρR
        (relMeet (dR.idxT ψR ρR)
          (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR)))
          (fun c' bb => ∃ q', bb = p.k + q' ∧ Rel c' q')
          (p.k + pinsS.length)
          (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp))) t c j fs →
      ∃ q₀ kJ iq, q = q₀ + iq ∧ iq < kJ ∧ GF st m q₀ kJ (dJf q₀) ∧
        j < ((dJf q₀).ctorsM iq).length ∧
        t ∈ˢ (D).idx ψ ρp (p.k + q₀ + iq) ∧
        dR.injT pcR ψR c j fs = (dJf q₀).inj (((D).pinAt (q₀ + iq)).ψJ ψ) iq j fs ∧
        FitsFrom ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) [])
          (fun l ρ => slotSet (f₀.s.eval ψ)
            (nestedU p.k W pinsS ψ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)) ρ
            (((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
            (((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l [])
            (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)
              (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
                (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0)))
          0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []) fs ∧
        (∀ l, l < (blockIds b.nP ppsF ψ (p.k + q₀ + iq)).length →
          interp V (consList fs ρp)
              (((mutEss0 ctorsA.length esF ψ).getD
                (b.ownOffset (p.k + q₀ + iq) + j) []).getD l default)
            = projS l t)) :
    ∀ c q, p.k + q < p.k + pinsS.length → Rel c q →
      FamLe ((D).pinIdx q ψ ρp)
        (dR.famAt ψR ρR (lfpTuple (dR.w ψR) dR.k (dR.idx ψR ρR) (dR.Φ ψR ρR)) c)
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q)) :=
  instanceLe_of_rel hreps hp hk hρR hsub
    (fun c hc t ht j fs hj hfit q hq hcp =>
      htrans_of_walk hμ h h3 hbk m dJf hgroups hρp hpair c hc t ht j fs hj hfit q
        (by omega) hcp)



/-- **The covering class's family IS the block pin's** (task #315 L-E,
DESIGN §U.89): at a `ClassPinAt` pair `(c, q)` of the root group, the
container's least tuple at block pin `q`'s frame — `pinLfp`, the `P`
of the global entry theorem — and the ROOT's extended carrier at its
class `c` are ONE family.  This is what turns `nestedInstanceLe`'s
conclusion (stated at the root's class) into the rank induction's
(stated at the pin).

**The route is the LEAF, and it has to be** (the negative result of
DESIGN §U.89 (b)): at a PIN class the two families are least tuples of
ONE container at two level assignments agreeing only on its level
parameters and two frames agreeing only below its parameter count, and
that is NOT a congruence of `lfpTuple` — `BlockModel.Φ` is an
arbitrary function of `(ψ, ρ)` and no clause of the tier makes it
depend on the restrictions alone.  `fam_eq_of_leaf` is the way
through: both families' leaves are ONE stored reading at ONE list of
values, which is exactly what `ClassPin`'s four clauses say — the
container (`name`), the assignment at its level parameters (`psi`,
through `EnvModel.acval_params`), the components' values (`frame`) and
the index set (`idx`).

At a MEMBER class nothing is needed: `ClassPinAt`'s own conjunct makes
`q` the root group's pin `r + c`, whose `pinLfp` IS the root's least
tuple at `c` (`grp`, `ψJEq`, `sameDs`). -/
theorem nestedPinFam_of_classPin (m : EnvModel V env₂) {st : ElimState}
    (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    {B : ContainerInfo → BlockModel V} (hB : EnvBlocksOf m B)
    (hdJfB : ∀ (q₀ kJ iq : Nat) (ci : ContainerInfo), iq < kJ → GF st m q₀ kJ (dJf q₀) →
      ConLeche.containerInfo? env₂ ((D).pinAt (q₀ + iq)).J = some ci → dJf q₀ = B ci)
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {pcR : Nat → PinCtors V} (hshR : PinShapes m B (dJf r) pcR) :
    ∀ c q, c < (dJf r).kT →
      ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r c q →
      pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
        = (dJf r).famAt (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
            (lfpTuple ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k
              ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
              ((dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) c := by
  intro c q hcT hcp
  have hwR : (dJf r).w (((D).pinAt r).ψJ ψ) = f₀.s.eval ψ := by
    have := GR.syn.w 0 GR.syn.kpos ψ
    rwa [Nat.add_zero] at this
  have hρR : Sat V ((dJf r).params (((D).pinAt r).ψJ ψ)).reverse ((D).pinFrame r ψ ρp) := by
    obtain ⟨ρ, as, hρe, hsp⟩ := spineOfSat_params (D) hρp
    subst hρe
    have := (dJf r).satOfSpine (GR.syn.DsFit 0 GR.syn.kpos ψ ρ as hsp)
    rw [Nat.add_zero] at this
    exact this
  have hkR : 0 < (dJf r).k := GR.syn.kEq ▸ GR.syn.kpos
  by_cases hcm : c < (dJf r).k
  · -- a MEMBER class: the pin IS the root group's, and `pinLfp` is the root's least tuple
    obtain rfl : q = r + c := hcp.2 hcm
    have hc : c < kR := GR.syn.kEq ▸ hcm
    rw [(dJf r).famAt_of_mem hcm, hwR]
    unfold pinLfp
    simp only [show ∀ t : Nat, pinsS.getD t default = (D).pinAt t from fun _ => rfl]
    rw [(GR.syn.grp c hc).1, Nat.add_sub_cancel_left,
      show ((D).pinAt (r + c)).ψJ ψ = ((D).pinAt r).ψJ ψ from
        (GR.syn.ψJEq c 0 hc GR.syn.kpos ψ).trans (by rw [Nat.add_zero]),
      show ((D).pinAt (r + c)).Ds ψ = ((D).pinAt r).Ds ψ from GR.syn.sameDs c hc ψ]
    rfl
  · -- a PIN class: the two least tuples are compared through their LEAVES
    have hqK : c - (dJf r).k < (dJf r).nPins := by
      have := hcT; unfold BlockModel.kT at this; omega
    obtain ⟨q₀', kK', i'', ci', hqKe, hi'', hci', S₂', hcount', hshape'⟩ := hshR _ hqK
    have hname : ((dJf r).pinAt (c - (dJf r).k)).J = ((D).pinAt q).J := by
      have := hcp.1.name
      rwa [(dJf r).nameT_of_pin hcm] at this
    have hci₂ : ConLeche.containerInfo? env₂ ((D).pinAt q).J = some ci' := by
      rw [← hname]; exact hci'
    have hqLt : q < pinsS.length := hcp.1.qLt
    obtain ⟨q₀, kJ, iq, hqe, hiq, G⟩ := hgroups q hqLt
    have hdJf : dJf q₀ = B ci' := hdJfB q₀ kJ iq ci' hiq G (by rw [← hqe]; exact hci₂)
    have CK : ContainerModeled m ci' (dJf q₀) := by rw [hdJf]; exact (hB _ ci' hci').1
    have S₂ : PinGroupView (dJf r) (dJf q₀) q₀' kK' := by rw [hdJf]; exact S₂'
    have hkK : kK' = kJ := by
      have h1 := S₂.kEq
      have h2 := G.syn.kEq
      omega
    subst hkK
    have hi''k : i'' < (dJf q₀).k := by rw [S₂.kEq]; exact hi''
    have hiqk : iq < (dJf q₀).k := by rw [G.syn.kEq]; exact hiq
    have hii : i'' = iq := by
      refine CK.memberName_inj hci' hi''k hiqk ?_
      rw [← S₂.name i'' hi'', ← (pinGroupView_of_syn G.syn).name iq hiq, ← hqe, hqKe] at *
      exact hname
    subst hii
    obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, hψJ⟩ := G.syn.stored i'' hiq
    have hfindq : env₂.find? ((D).pinAt q).J = some (.indInfo cvT caps) := by
      rw [hqe]; exact hfind
    -- the pair's two agreements, at the group's base pins
    have hψag : ∀ pp ∈ cvT.levelParams,
        (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ)) pp = (((D).pinAt (q₀ + i'')).ψJ ψ) pp := by
      intro pp hpp'
      have := hcp.1.psi cvT caps hfindq pp hpp'
      rw [(dJf r).psiT_of_pin _ hcm, hqKe,
        (S₂.same i'' hiq (((D).pinAt r).ψJ ψ)).1, hqe] at this
      exact this
    have hnp : ((D).pinAt q).nPJ = (dJf q₀).nP := by
      rw [hqe]; exact G.syn.pinNP i'' hiq
    have hfr : ∀ v, v < (dJf q₀).nP →
        (dJf r).pinFrame q₀' (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp) v
          = (D).pinFrame (q₀ + i'') ψ ρp v := by
      intro v hv
      have := hcp.1.frame v (by rw [hnp]; exact hv)
      rw [(dJf r).frameT_of_pin hcm, hqKe] at this
      unfold BlockModel.pinFrame at this ⊢
      rw [(S₂.same i'' hiq (((D).pinAt r).ψJ ψ)).2] at this
      rw [← hqe]
      exact this
    have hpar := CK.params_congr hci₂ hfindq hψag hiqk
    -- the two sides, named
    have hLHS : pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
        = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
            ((dJf q₀).idx (((D).pinAt (q₀ + i'')).ψJ ψ) ((D).pinFrame (q₀ + i'') ψ ρp))
            ((dJf q₀).Φ (((D).pinAt (q₀ + i'')).ψJ ψ) ((D).pinFrame (q₀ + i'') ψ ρp)) i'' := by
      unfold pinLfp
      rw [hqe, (G.syn.grp i'' hiq).1, Nat.add_sub_cancel_left]
      rfl
    have hRHS : (dJf r).famAt (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
          (lfpTuple ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k
            ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
            ((dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) c
        = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
            ((dJf q₀).idx (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))
              ((dJf r).pinFrame q₀' (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))
            ((dJf q₀).Φ (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))
              ((dJf r).pinFrame q₀' (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) i'' := by
      rw [(dJf r).famAt_of_pin hcm, hqKe,
        (dJf r).pinGroupFam_mem GR.syn.reps CK.reps hkR S₂ hρR hiq, hwR]
    rw [hLHS, hRHS]
    -- the container's data at the two assignments
    have huE : (dJf q₀).uM i'' (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))
        = (dJf q₀).uM i'' (((D).pinAt (q₀ + i'')).ψJ ψ) := hpar.1
    have hIdsE : (dJf q₀).IdsM i'' (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))
        = (dJf q₀).IdsM i'' (((D).pinAt (q₀ + i'')).ψJ ψ) := by
      unfold BlockModel.IdsM; rw [hpar.2.1]
    have hbelow : FieldsBelow (dJf q₀).nP
        ((dJf q₀).IdsM i'' (((D).pinAt (q₀ + i'')).ψJ ψ)) :=
      memberIds_below CK.reps hiqk _
    -- the two component lists are ONE list of values
    have hL₁len : ((((D).pinAt (q₀ + i'')).Ds ψ).map (interp V ρp)).length = (dJf q₀).nP := by
      rw [List.length_map]; exact G.syn.pinDsLen i'' hiq ψ
    have hL₂len : ((((dJf r).pinAt q₀').Ds (((D).pinAt r).ψJ ψ)).map
        (interp V ((D).pinFrame r ψ ρp))).length = (dJf q₀).nP := by
      rw [List.length_map]; exact S₂.pinDsLen (((D).pinAt r).ψJ ψ)
    have hAs : (((dJf r).pinAt q₀').Ds (((D).pinAt r).ψJ ψ)).map
          (interp V ((D).pinFrame r ψ ρp))
        = (((D).pinAt (q₀ + i'')).Ds ψ).map (interp V ρp) := by
      have h₁ := map_range_reverse_consList
        ((((D).pinAt (q₀ + i'')).Ds ψ).map (interp V ρp)) ρp
      have h₂ := map_range_reverse_consList
        ((((dJf r).pinAt q₀').Ds (((D).pinAt r).ψJ ψ)).map
          (interp V ((D).pinFrame r ψ ρp))) ((D).pinFrame r ψ ρp)
      rw [hL₁len] at h₁
      rw [hL₂len] at h₂
      rw [← h₁, ← h₂]
      refine List.map_congr_left fun v hv => ?_
      exact hfr v (by simpa using List.mem_range.mp (List.mem_reverse.mp hv))
    -- the leaf: ONE stored reading at ONE list of values
    have hacv : m.acval ((dJf q₀).memberName i'')
          (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))
        = m.acval ((dJf q₀).memberName i'') (((D).pinAt (q₀ + i'')).ψJ ψ) := by
      have hfindM : env₂.find? ((dJf q₀).memberName i'') = some (.indInfo cvT caps) := by
        rw [hI.member, ← hqe]; exact hfindq
      exact m.acval_params _ _ hfindM _ _ hψag
    obtain ⟨cvTJ, cvRJ, mIJ, rPJ, rulesJ, hIJ⟩ := CK.reps i'' hiqk
    have hwJ₁ : (dJf q₀).w (((D).pinAt (q₀ + i'')).ψJ ψ) = f₀.s.eval ψ := G.syn.w i'' hiq ψ
    have hwJ₂ : (dJf q₀).w (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ)) = f₀.s.eval ψ := by
      rw [hpar.2.2]; exact hwJ₁
    have hfit₁ : SpineFit ρp ((dJf q₀).params (((D).pinAt (q₀ + i'')).ψJ ψ))
        ((((D).pinAt (q₀ + i'')).Ds ψ).map (interp V ρp)) := by
      obtain ⟨ρ₀, as, hρe, hsp⟩ := spineOfSat_params (D) hρp
      subst hρe
      exact G.syn.DsFit i'' hiq ψ ρ₀ as hsp
    have hfit₂ : SpineFit ((D).pinFrame r ψ ρp)
        ((dJf q₀).params (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ)))
        ((((dJf r).pinAt q₀').Ds (((D).pinAt r).ψJ ψ)).map
          (interp V ((D).pinFrame r ψ ρp))) := by
      obtain ⟨ρ', as', hρ'e, hsp'⟩ := spineOfSat_params (dJf r) hρR
      rw [hρ'e]
      exact S₂.DsFit (((D).pinAt r).ψJ ψ) ρ' as' hsp'
    refine fam_eq_of_leaf (w' := f₀.s.eval ψ)
      (u := (dJf q₀).uM i'' (((D).pinAt (q₀ + i'')).ψJ ψ))
      (Ids := (dJf q₀).IdsM i'' (((D).pinAt (q₀ + i'')).ψJ ψ))
      (ρ₁ := (D).pinFrame (q₀ + i'') ψ ρp)
      (ρ₂ := (dJf r).pinFrame q₀' (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
      (A := ((((D).pinAt (q₀ + i'')).Ds ψ).map (interp V ρp)).foldl SetTheory.app
        (interp V ρp (m.acval ((dJf q₀).memberName i'') (((D).pinAt (q₀ + i'')).ψJ ψ))))
      (fun is his => spineFit_congr_fields hbelow (fun v hv => (hfr v hv).symm) his)
      (congrArg (towerSet _)
        (teleOfFields_congr_below hbelow fun v hv => (hfr v hv).symm))
      (lfpTuple_mem _ _ _ _ i'' hiqk)
      ?_ ?_ ?_
    · -- the ROOT class's family lives in the same space
      have hmem₂ := lfpTuple_mem (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))
          ((dJf r).pinFrame q₀' (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)))
        ((dJf q₀).Φ (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))
          ((dJf r).pinFrame q₀' (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) i'' hiqk
      unfold BlockModel.idx at hmem₂
      rw [huE, hIdsE] at hmem₂
      exact hmem₂
    · -- the BLOCK pin's leaf
      intro is his
      have hleaf := hIJ.leaf (((D).pinAt (q₀ + i'')).ψJ ψ) ρp
        ((((D).pinAt (q₀ + i'')).Ds ψ).map (interp V ρp)) is hfit₁ his
      rw [List.foldl_append, hwJ₁] at hleaf
      exact hleaf.symm
    · -- the ROOT class's leaf: ONE stored reading at ONE list of values
      intro is his
      have hleaf := hIJ.leaf (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))
        ((D).pinFrame r ψ ρp)
        ((((dJf r).pinAt q₀').Ds (((D).pinAt r).ψJ ψ)).map
          (interp V ((D).pinFrame r ψ ρp))) is hfit₂
        (by rw [hIdsE]; exact his)
      have hA : ((((dJf r).pinAt q₀').Ds (((D).pinAt r).ψJ ψ)).map
              (interp V ((D).pinFrame r ψ ρp))).foldl SetTheory.app
            (interp V ((D).pinFrame r ψ ρp)
              (m.acval ((dJf q₀).memberName i'')
                (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ))))
          = ((((D).pinAt (q₀ + i'')).Ds ψ).map (interp V ρp)).foldl SetTheory.app
            (interp V ρp
              (m.acval ((dJf q₀).memberName i'') (((D).pinAt (q₀ + i'')).ψJ ψ))) := by
        rw [hAs, hacv,
          interp_closed (V := V) (m.cval_closedL _ _) ((D).pinFrame r ψ ρp) ρp]
      rw [List.foldl_append, hwJ₂,
        show (dJf q₀).tup (((dJf r).pinAt q₀').ψJ (((D).pinAt r).ψJ ψ)) i'' is
            = tupW ((dJf q₀).uM i'' (((D).pinAt (q₀ + i'')).ψJ ψ)) is from by
          unfold BlockModel.tup; rw [huE],
        hA] at hleaf
      exact hleaf.symm


/-- **`instanceLe` at the ROOT GROUP, from the run** (task #315 L-E,
DESIGN §U.87 (b)): `instanceLe_of_pair` with its per-pair transfer
discharged by `nestedPinPairAt` — at a root group `r` of the block's
pin table whose container carries its block model, every class of the
root that is `ClassPinAt`-related to a block pin `q` has its extended
carrier below the auxiliary carrier at `q`.

The root's parameter frame is its group's own (`DsFit` at the base
pin), so nothing beyond the block's `Sat` is asked of the caller; what
is left are `hIH` and `hout`, the rank induction's two. -/
theorem nestedInstanceLe (hμ : μ.verifiedChecks = true)
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
    {B : ContainerInfo → BlockModel V} (hB : EnvBlocksOf m B)
    (hppB : ∀ (J : Name) (ci : ContainerInfo) (cv : ConstantVal) (caps : IndCaps),
      ConLeche.containerInfo? env₂ J = some ci → env₂.find? J = some (.indInfo cv caps) →
      ContainerPinParams (V := V) cv (B ci))
    (hdJfB : ∀ (q₀ kJ iq : Nat) (ci : ContainerInfo), iq < kJ → GF st m q₀ kJ (dJf q₀) →
      ConLeche.containerInfo? env₂ ((D).pinAt (q₀ + iq)).J = some ci → dJf q₀ = B ci)
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {ciR : ContainerInfo} (CR : ContainerModeled m ciR (dJf r))
    {pcR : Nat → PinCtors V} (hpR : PinRecLaws m (dJf r) pcR)
    (hshR : PinShapes m B (dJf r) pcR)
    {S : Nat → Prop}
    {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length → S q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Pf (q₀ + i) = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
    (hout : ∀ q₀ iq j l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l false = true →
      (((dJf q₀).rss iq).getD j []).getD l false = false → ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) < p.k → S ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) - p.k)) :
    ∀ c q, p.k + q < p.k + pinsS.length →
      ClassPinAt env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp ((D).pinFrame r ψ ρp) r c q →
      FamLe ((D).pinIdx q ψ ρp)
        ((dJf r).famAt (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp)
          (lfpTuple ((dJf r).w (((D).pinAt r).ψJ ψ)) (dJf r).k
            ((dJf r).idx (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))
            ((dJf r).Φ (((D).pinAt r).ψJ ψ) ((D).pinFrame r ψ ρp))) c)
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q)) := by
  have hρR : Sat V ((dJf r).params (((D).pinAt r).ψJ ψ)).reverse ((D).pinFrame r ψ ρp) := by
    obtain ⟨ρ, as, hρe, hsp⟩ := spineOfSat_params (D) hρp
    subst hρe
    have := (dJf r).satOfSpine (GR.syn.DsFit 0 GR.syn.kpos ψ ρ as hsp)
    rw [Nat.add_zero] at this
    exact this
  exact instanceLe_of_pair hμ h h3 hbk m dJf hgroups hρp GR.syn.reps hpR
    (GR.syn.kEq ▸ GR.syn.kpos) hρR (fun _ _ hcp => hcp.1)
    (nestedPinPairAt hμ h hbk m hleafM dJf hgroups hρp hB hppB hdJfB GR CR hpR hshR hIH hPfGroup hout)


/-- **A container instance is closed, at its ROOT** (task #315 L-E,
DESIGN §U.89): `pins_le_of_instanceLe`'s `hinst` at one instance —
every pin of the instance of `r` has its container's least tuple below
the auxiliary carrier there.  The three pieces compose with nothing
left between them: the COVERING (`InstanceCovered`, a premise here —
`instanceCovered_of_others` builds it, and its `hothers` waits on
M7-3's `ownPins` at the nested site) hands a class of the root;
`nestedInstanceLe` bounds the root's carrier at that class; and
`nestedPinFam_of_classPin` says that carrier IS the pin's family.  The
index sets are one by `nestedIdx_eq_pinIdx`.

What remains of the whole of step (iii) is then the RANK — `hedge` and
`hhom`, K.37's clauses (2) and (3), which want the kernel lane's
inversion of `nestedPinRankAt` — and the two premises this carries,
`hIH` and `hout`. -/
theorem nestedPinInstLe (hμ : μ.verifiedChecks = true)
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
    {B : ContainerInfo → BlockModel V} (hB : EnvBlocksOf m B)
    (hppB : ∀ (J : Name) (ci : ContainerInfo) (cv : ConstantVal) (caps : IndCaps),
      ConLeche.containerInfo? env₂ J = some ci → env₂.find? J = some (.indInfo cv caps) →
      ContainerPinParams (V := V) cv (B ci))
    (hdJfB : ∀ (q₀ kJ iq : Nat) (ci : ContainerInfo), iq < kJ → GF st m q₀ kJ (dJf q₀) →
      ConLeche.containerInfo? env₂ ((D).pinAt (q₀ + iq)).J = some ci → dJf q₀ = B ci)
    {r kR : Nat} (GR : GF st m r kR (dJf r))
    {ciR : ContainerInfo} (CR : ContainerModeled m ciR (dJf r))
    {pcR : Nat → PinCtors V} (hpR : PinRecLaws m (dJf r) pcR)
    (hshR : PinShapes m B (dJf r) pcR)
    {S : Nat → Prop}
    {Pf : Nat → V}
    (hIH : ∀ q', q' < pinsS.length → S q' →
      Pf q' = (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) (p.k + q'))
    (hPfGroup : ∀ q₀ kJ, GF st m q₀ kJ (dJf q₀) → ∀ i, i < kJ →
      Pf (q₀ + i) = lfpTuple (f₀.s.eval ψ) (dJf q₀).k
        ((dJf q₀).idx (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp))
        ((dJf q₀).Φ (((D).pinAt (q₀ + i)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp)) i)
    (hout : ∀ q₀ iq j l, l < ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + iq) + j) []).length →
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l false = true →
      (((dJf q₀).rss iq).getD j []).getD l false = false → ¬ (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) < p.k → S ((((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD (b.ownOffset (p.k + q₀ + iq) + j) []).getD l 0) - p.k))
    {inst : Nat → Nat}
    (hcov : InstanceCovered env₂ (D) (dJf r) ψ (((D).pinAt r).ψJ ψ) ρp
      ((D).pinFrame r ψ ρp) inst r) :
    ∀ q, q < pinsS.length → inst q = inst r →
      FamLe ((D).idx ψ ρp (p.k + q)) (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q)
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q)) := by
  intro q hq hinst
  obtain ⟨c, hcp⟩ := hcov q hq hinst
  have hidx : (D).idx ψ ρp (p.k + q) = (D).pinIdx q ψ ρp := by
    obtain ⟨q₀, kJ, iq, rfl, hiq, G⟩ := hgroups q hq
    rw [show p.k + (q₀ + iq) = p.k + q₀ + iq from by omega]
    exact nestedIdx_eq_pinIdx G hiq
  rw [hidx, nestedPinFam_of_classPin m dJf hgroups hρp hB hdJfB GR hshR c q hcp.1.cLt hcp]
  exact nestedInstanceLe hμ h h3 hbk m hleafM dJf hgroups hρp hB hppB hdJfB GR CR hpR hshR
    hIH hPfGroup hout c q (by omega) hcp

/-! ## Step (iii)'s INDUCTION: the rank orders the instances (K.37) -/

/-- **STEP (iii) AT ONE PIN, FROM CLOSURE AT A GIVEN FRAME** (task #315
L-E, the closure step): the container's least tuple at ANY parameter
frame lies below ANY tuple closed under the container's section at that
same frame.

This is `lfpTuple_le` — **leastness, which is unconditional on this
route**, because `lfpTuple` is the INTERSECTION of the closed tuples
(`mem_app_lfpTuple`) rather than a stage limit.  It needs no
monotonicity and no chain.

**WHAT IT SETTLES, AND WHAT IT DOES NOT.**  Step (iii)'s SKELETON at a
pin takes exactly one hypothesis, `hcl`, and that hypothesis is about
pin `q` alone: no induction, no ordering, no conclusion at another pin
appears anywhere in this statement.  So the declaration-order induction
has no consumer HERE.  It does not follow that it has none: the
consumer, if it survives, has moved into the DISCHARGE of `hcl` — the
agreement between the container's section at the candidate frame and the
auxiliary block's own section at the copy — and this lane does not claim
the discharge is cross-pin-free until it is written.

**The frame stays abstract.**  `as` is universally quantified, so every
skeleton above this one can be built before any candidate component
family is constructed; only `hcl`'s discharge needs the family to be the
candidate one. -/
theorem pinLfpAt_le {st : ElimState} {pinsS : List PinSyn} {dJf : Nat → BlockModel V}
    {w : Nat} {ψ : Name → Nat} {ρp : Nat → V} {as : List V} {q : Nat} {L : Nat → V}
    (hcl : IsClosedTuple w (dJf (st.pins.getD q default).grpBase).k
      ((dJf (st.pins.getD q default).grpBase).idx ((pinsS.getD q default).ψJ ψ)
        (consList as ρp))
      ((dJf (st.pins.getD q default).grpBase).Φ ((pinsS.getD q default).ψJ ψ)
        (consList as ρp)) L)
    (hq : q - (st.pins.getD q default).grpBase < (dJf (st.pins.getD q default).grpBase).k) :
    FamLe ((dJf (st.pins.getD q default).grpBase).idx ((pinsS.getD q default).ψJ ψ)
        (consList as ρp) (q - (st.pins.getD q default).grpBase))
      (pinLfpAt (V := V) st pinsS dJf w ψ ρp as q)
      (L (q - (st.pins.getD q default).grpBase)) :=
  lfpTuple_le hcl _ hq

/-- **STRONG INDUCTION OVER A NUMERIC MEASURE ON THE PINS** (task #315
L-E): if each pin's goal follows from the goal at every pin of strictly
smaller measure, it holds at every pin.  `Q` is arbitrary and `ord` is
arbitrary; this lemma knows nothing about either, and it is the ONE
piece of induction machinery the restated step needs.

**Two consumers, deliberately.**  `pins_le_of_declOrder` instantiates it
at the declaration order with `Q q := FamLe …` — the inclusion of step
(iii).  G1's candidate-to-true bridge instantiates it at the pin
expression's TERM SIZE with `Q q :=` the frame equality at pin `q`,
because "pin `q`'s components contain pin `q'`'s expression" strictly
decreases that size.  **The decrease is SYNTACTIC, not measured** (task
#315 L-C): a pin's reading occurring inside `q`'s components is a
proper subterm of them, and `q` cannot be its own predecessor because
its reading `J Ds` cannot occur inside its own `Ds`.  What the corpus
measurement covers is the IDENTIFICATION of those subterms with table
pins — the kernel record lane L-E requested — and not the order's
well-foundedness.

The two instantiations must stay SEPARATE and SEQUENCED — the bridge
runs after the inclusion is established at every pin, consuming its
finished conclusion rather than its hypothesis.  They cannot be merged
into one induction: at `tests/e2e/nested_p22.ndjson` the declaration
order puts pin 0 before pin 1 and the containment order puts pin 1
before pin 0, so the UNION of the two relations is cyclic and no
well-founded induction over it exists. -/
theorem pins_all_of_measure {n : Nat} {Q : Nat → Prop} {ord : Nat → Nat}
    (hstep : ∀ q, q < n → (∀ q', q' < n → ord q' < ord q → Q q') → Q q) :
    ∀ q, q < n → Q q := by
  have key : ∀ r q, ord q < r → q < n → Q q := by
    intro r
    induction r with
    | zero => intro q hr; exact absurd hr (Nat.not_lt_zero _)
    | succ r ih =>
      intro q hr hq
      exact hstep q hq fun q' hq' hlt => ih q' (by omega) hq'
  exact fun q hq => key (ord q + 1) q (Nat.lt_succ_self _) hq

/-- **THE DECLARATION-ORDER INDUCTION** (task #315 L-E, DESIGN "the
restatement written"): the measure the candidate-frame statement
inducts on, stated ABSTRACTLY in the ordering — `ord q` is meant to be
the declaration position of pin `q`'s CONTAINER, but this lemma does
not know that and does not care how the order is certified.  The
run-level assembly supplies `ord`, exactly as it supplies the edge
relation for `pins_le_of_instanceLe`: **this lane produces neither an
edge nor an order.**

What the step is handed is the conclusion at every pin whose container
is declared STRICTLY EARLIER.  **The obligation this serves is the
CONTAINER'S FIELD DOMAIN at a copy-recursive field, `hentR` of
`CopyCtorShape.fit_imp_T_le_dom` — NOT the target's reading.**  Keeping
those two apart is the whole of the correction recorded below; they were
run together once and the error cost lane L-B a blocked session.

By the field domain's head, at a PIN target:

* a MEMBER target needs nothing — the carrier's member segment IS the
  block's own least tuple (`ofNested_lfp`), and this is not an edge;
* a PARAMETER-headed domain consumes no hypothesis AT ANOTHER PIN, but
  it is not free: at the RECORDED frame it evaluates to the component's
  true value, so it needs the CANDIDATE frame, whose component family
  has no producer in the tree yet;
* a CONSTANT-headed domain **consumes this hypothesis, and consumes it
  AT THE CANDIDATE FRAME TOO.**  `Array`'s field `List α` at a candidate
  `α ↦ L⁺` evaluates to `List`'s least tuple at that argument, which is
  the inner pin's `pinLfpAt` — not the inner pin's `L⁺`.  Closing the
  gap is the conclusion at the inner pin, which is this induction.  The
  candidate frame does NOT supersede this arm, and `auxTarget_reads`
  does not either: that lemma is about the TARGET'S READING, a different
  object.

Pins sharing one container never appear in the step's hypothesis, which
is why "strictly earlier" is load-bearing rather than decorative: a
constant-headed target at the SAME container — `K (K X)` — would leave
the step with nothing, and this lane's own probe found such an edge to
be structurally impossible (the own bit makes a domain mentioning its
own container OWN by definition).

(The per-arm edge counts this docstring used to carry are withdrawn: the
coordinator retracted the two-way 35/59 split as a measurement of a
coarser distinction than it was described as.  The three-valued
classification — parameter-bare, parameter-applied, constant-applied —
replaces it, and no count is load-bearing in any proof.) -/
theorem pins_le_of_declOrder {n k : Nat} {Is P L : Nat → V} {ord : Nat → Nat}
    (hstep : ∀ q, q < n →
      (∀ q', q' < n → ord q' < ord q → FamLe (Is (k + q')) (P q') (L (k + q'))) →
      FamLe (Is (k + q)) (P q) (L (k + q))) :
    ∀ q, q < n → FamLe (Is (k + q)) (P q) (L (k + q)) :=
  pins_all_of_measure hstep

/-- **The rank induction, over K.37's four clauses** (task #315 L-E,
DESIGN §U.55): if every reference LEAVING a container instance goes to
a strictly smaller rank (`hedge`), the rank is a function of the
instance (`hhom`), and each instance is closed once the pins it
references OUTSIDE itself are (`hinst` — `instanceLe`, the container
instance transfer), then every pin's family lies below the auxiliary
carrier's.

This is the whole of step (iii) that does not depend on WHAT the pins
are: `hedge`/`hhom` are `nestedPinRankOk`'s clauses (2) and (3) at the
edge relation the kernel lane's inversion supplies — an edge is a
copy's field target, which `CopyCtorShape` names — and `hinst` is the
transfer.  Clause (1) (an own reference stays inside the instance) and
clause (4) (a mint group is one instance) are consumed INSIDE `hinst`,
which is where the container's own pins and the group are. -/
theorem pins_le_of_instanceLe {n k : Nat} {Is P L : Nat → V}
    {Edge : Nat → Nat → Prop} {inst rank : Nat → Nat}
    (hedge : ∀ q q', q < n → q' < n → Edge q q' → inst q' = inst q ∨ rank q' < rank q)
    (hhom : ∀ q q', q < n → q' < n → inst q = inst q' → rank q = rank q')
    (hinst : ∀ q, q < n →
      (∀ q₀ q', q₀ < n → q' < n → inst q₀ = inst q → Edge q₀ q' → inst q' ≠ inst q →
        FamLe (Is (k + q')) (P q') (L (k + q'))) →
      FamLe (Is (k + q)) (P q) (L (k + q))) :
    ∀ q, q < n → FamLe (Is (k + q)) (P q) (L (k + q)) := by
  have key : ∀ r q, rank q < r → q < n → FamLe (Is (k + q)) (P q) (L (k + q)) := by
    intro r
    induction r with
    | zero => intro q hr; exact absurd hr (Nat.not_lt_zero _)
    | succ r ih =>
      intro q hr hq
      refine hinst q hq fun q₀ q' hq₀ hq' hq₀i hE hne => ?_
      refine ih q' ?_ hq'
      rcases hedge q₀ q' hq₀ hq' hE with heq | hlt
      · exact absurd (heq.trans hq₀i) hne
      · have : rank q₀ = rank q := hhom q₀ q hq₀ hq hq₀i
        omega
  exact fun q hq => key (rank q + 1) q (Nat.lt_succ_self _) hq


/-- **The rank induction AT THE RUN** (task #315 L-E, DESIGN §U.90):
`pins_le_of_instanceLe` with `hedge` and `hhom` — K.37's clauses (2)
and (3) — DISCHARGED from the kernel lane's K.52
(`nestedPinRankOk_inv`), at the two lists the model reads
(`nestedPinInstOf`/`nestedPinRankOf`) and the edge relation
`∃ own, (q, q', own) ∈ edges`.

**The ownership bit is never read**, which is what makes the edge
relation existential in it: at an own edge K.37 gives the instance
equality, at a not-own edge the disjunction, and `hedge`'s conclusion
is the disjunction either way, so `mentionsMember` is never computed
on this side.

What is left is `hinst` — a container instance is closed once the pins
it references OUTSIDE itself are — which is `nestedPinInstLe` at the
instance's root, and which is stated here against the edge list the
inversion produces so that the run-level assembly (where
`NestedPinsRun` is in scope) is the only place that ever has to
exhibit an edge.  This lane produces none. -/
theorem nestedPinsLe_of_rank {env : Env} {p : NestedParts} {b : MutualBlock} {st : ElimState}
    {stored : List AuxStored} (hrank : ConLeche.nestedPinRankOk env p b st stored = true)
    {k : Nat} {Is P L : Nat → V}
    (hinst : ∀ edges : List (Nat × Nat × Bool),
      ConLeche.nestedPinEdges env p b st stored = some edges →
      ∀ q, q < st.pins.length →
      (∀ q₀ q', q₀ < st.pins.length → q' < st.pins.length →
        (ConLeche.nestedPinInstOf env p b st stored).getD q₀ 0
          = (ConLeche.nestedPinInstOf env p b st stored).getD q 0 →
        (∃ own : Bool, (q₀, q', own) ∈ edges) →
        (ConLeche.nestedPinInstOf env p b st stored).getD q' 0
          ≠ (ConLeche.nestedPinInstOf env p b st stored).getD q 0 →
        FamLe (Is (k + q')) (P q') (L (k + q'))) →
      FamLe (Is (k + q)) (P q) (L (k + q))) :
    ∀ q, q < st.pins.length → FamLe (Is (k + q)) (P q) (L (k + q)) := by
  obtain ⟨edges, hed, h12, h3, h4⟩ := ConLeche.nestedPinRankOk_inv hrank
  exact pins_le_of_instanceLe
    (Edge := fun q q' => ∃ own : Bool, (q, q', own) ∈ edges)
    (inst := fun q => (ConLeche.nestedPinInstOf env p b st stored).getD q 0)
    (rank := fun q => (ConLeche.nestedPinRankOf env p b st stored).getD q 0)
    (fun _ _ _ _ he => (h12 _ he.choose_spec).imp Eq.symm id)
    (fun q q' hq hq' hqq => h3 q q' hq hq' hqq)
    (hinst edges hed)


/-- **STEP (ii) AT ONE PIN** (task #315 L-C, the declaration-order
step's bridge): the two inclusions are the identity **at a single
pin**, from the inclusion at that pin alone.

Its consumer is the induction step, and it is what the step needs and
`nestedPinsEq_of_le` cannot give: a well-founded induction over the
pins (`pins_all_of_measure`, and `pins_le_of_declOrder` over it) hands
its step the INCLUSION at the pins already settled, while the
`hIH` every entry lemma below takes (`nestedPinEntryOut`,
`nestedInstanceLe`, `nestedPinInstLe`) is an EQUALITY,
`Pf q' = L⁺ (p.k + q')`.  Step (ii) (`nestedPinsFixed`) supplies the
converse inclusion UNCONDITIONALLY and per pin, so the upgrade is
per pin too — it never needs the conclusion anywhere else, which is
exactly the property an induction step may not assume.

`nestedPinsEq_of_le` is now this lemma pointwise, so the generalisation
is conservative by the elaborator's verdict rather than by reading. -/
theorem nestedPinEq_at_of_le (hμ : μ.verifiedChecks = true)
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
    {q : Nat} (hq : q < pinsS.length)
    (hle : FamLe ((D).idx ψ ρp (p.k + q)) (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q)
      (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q))) :
    pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
      = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q) := by
  have hfix := nestedPinsFixed hμ h h3 hbk m hleafM dJf hgroups hρp
  obtain ⟨q₀, kJ, iq, hqe, hiq, G⟩ := hgroups q hq
  have hidx : (D).idx ψ ρp (p.k + q)
      = (dJf q₀).idx (((D).pinAt (q₀ + iq)).ψJ ψ)
          (consList ((((D).pinAt (q₀ + iq)).Ds ψ).map (interp V ρp)) ρp) iq := by
    rw [hqe, show p.k + (q₀ + iq) = p.k + q₀ + iq from by omega]
    exact nestedIdx_of_group G hiq
  have hPmem : pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
      ∈ˢ famSpace ((D).w ψ) ((D).idx ψ ρp (p.k + q)) := by
    rw [hidx]
    unfold pinLfp
    rw [hqe, (G.syn.grp iq hiq).1, Nat.add_sub_cancel_left]
    exact lfpTuple_mem _ _ _ _ iq (G.syn.kEq ▸ hiq)
  refine famSpace_ext hPmem (lfpTuple_mem _ _ _ _ (p.k + q) (by omega)) fun i hi => ?_
  exact Subset.antisymm (hle i hi) (hfix.2 q hq i hi)

/-- **Step (ii) of the global entry theorem** (task #315 L-E, DESIGN
§U.90): the two inclusions ARE the identity.  Step (i)/(ii)
(`nestedPinsFixed`) gives the auxiliary carrier below the containers'
least tuples at every pin; the rank induction
(`nestedPinsLe_of_rank`, over `nestedPinInstLe` at each instance's
root) gives the converse; and both families live in the family space
of the SAME index set — the pin's, which is its container member's
(`nestedIdx_of_group`) — so `famSpace_ext` turns the pair into
`pinLfp q = L⁺ (k + q)`, which is `hIH`'s statement and, at every
group, `nestedPinsEntry_of`'s. -/
theorem nestedPinsEq_of_le (hμ : μ.verifiedChecks = true)
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
    (hle : ∀ q, q < pinsS.length →
      FamLe ((D).idx ψ ρp (p.k + q)) (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q)
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q))) :
    ∀ q, q < pinsS.length →
      pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
        = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q) :=
  fun q hq => nestedPinEq_at_of_le hμ h h3 hbk m hleafM dJf hgroups hρp hq (hle q hq)


/-- **STEP (iv): the copies' ENTRIES at the auxiliary carrier** (task
#315 L-E, DESIGN §U.91) — the residual `NestedPinsEntry` names, at one
group, read off the identity step (ii)/(iii) produced.

`nestedPinsFixed` builds exactly this at `P`, the containers' least
tuples, where the target readings are `pinTarget_reads`/`memberTarget_reads`
directly.  Here the tuple is `L⁺` and the readings come from
`nestedTargetReads_L` — whose pin-target half is the identity
`pinLfp q = L⁺ (k + q)`, now UNCONDITIONAL (`S := fun _ => True`), so
the predicate that carried the rank induction's scope disappears from
the statement.

The three arms are the shape's own: a container-RECURSIVE field at a
MEMBER target lands inside the group and `CopyEntryOut` does not ask
about it; at one of the container's OWN pins it is
`copyEntryAt_of_pinCorr` with `nestedPinFrame_transport` carrying the
fit from the container's pin frame to the block pin's; a
container-ORDINARY field is `copyEntryAt_of_read` at the repaired
`EntryRead`. -/
theorem nestedPinsEntry_at (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    (heq : ∀ q, q < pinsS.length →
      pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
        = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q))
    {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀)) {i : Nat} (hi : i < kJ)
    {j : Nat} (hj : j < ((dJf q₀).ctorsM i).length) :
    CopyEntryOut (dJf q₀) (((D).pinAt (q₀ + i)).ψJ ψ) (((D).pinAt (q₀ + i)).Ds ψ)
      (fun l => ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
        (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0)
      ((mutTlss ctorsA.length tssF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) [])
      ((mutEiss0 ctorsA.length eissF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) []) ρp i j
      (p.k + q₀) kJ ((blkFss0 b ctorsA kinds dsF ψ).getD (b.ownOffset (p.k + q₀ + i) + j) [])
      ((blkRss ctorsA kinds).getD (b.ownOffset (p.k + q₀ + i) + j) []) (f₀.s.eval ψ)
      (nestedU p.k W pinsS ψ)
      (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp)) := by
  have hZ := nestedTargetReads_L (S := fun _ => True) hμ h hbk m hleafM dJf hgroups hρp
    (fun q' hq' _ => heq q' hq') (fun _ _ G' _ hi' => pinLfp_group G' hi')
  have hρJ : Sat V ((dJf q₀).params (((D).pinAt (q₀ + i)).ψJ ψ)).reverse
      (consList ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V ρp)) ρp) := by
    obtain ⟨ρ, as, hρe, hsp⟩ := spineOfSat_params (D) hρp
    subst hρe
    exact (dJf q₀).satOfSpine (G.syn.DsFit i hi ψ ρ as hsp)
  intro l hl hrs hout
  obtain ⟨cvT, caps, cvR, mI, rP, rules, hfind, hI, -⟩ := G.syn.stored i hi
  have hsh := G.shape i hi cvT caps hfind ψ ρp hρp i j hi hj
  unfold CopyShapeA at hsh
  have hjl : (((dJf q₀).ctorsM i))[j]? = some (((dJf q₀).ctorsM i).getD j default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  have hlenF := hI.Fss_length hjl (((D).pinAt (q₀ + i)).ψJ ψ)
  have hks : ((dJf q₀).ksF i j).length
      = (((dJf q₀).Fss i (((D).pinAt (q₀ + i)).ψJ ψ)).getD j []).length := by
    rw [(hI.ctorData hjl).ksLen, hlenF]
  have hlF : l < (((dJf q₀).Fss i (((D).pinAt (q₀ + i)).ψJ ψ)).getD j []).length := by
    rw [← hsh.len]; exact hl
  by_cases hr : (((dJf q₀).rss i).getD j []).getD l false = true
  · rcases hI.tgt_cases hj (hks ▸ hlF) with htgt | ⟨hnt, -⟩
    · -- a MEMBER target: inside the group, which `CopyEntryOut` does not ask about
      obtain ⟨-, htg, -, -⟩ := hsh.recF l hlF hr htgt
      have hk := G.syn.kEq
      exact absurd
        (⟨by rw [htg]; omega, by rw [htg]; omega⟩ :
          p.k + q₀ ≤ ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0 ∧
            ((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD
              (b.ownOffset (p.k + q₀ + i) + j) []).getD l 0 < p.k + q₀ + kJ) hout
    · -- one of the CONTAINER'S OWN pins
      obtain ⟨-, -, hkle, hklt, hcorr, htl, hEis⟩ := hsh.pinF l hlF hr hnt
      refine copyEntryAt_of_pinCorr (TV := TVA m.acval ((fms.take p.k).map (·.cvTa.name)) ψ)
        G.syn.reps (G.syn.typed _) (G.syn.pinsTyped _) (G.syn.kEq ▸ hi) hjl hρJ
        (G.syn.w i hi ψ) hlF hr hnt hcorr htl hEis ?_ (hZ _ hklt (fun _ => trivial))
      exact nestedPinFrame_transport dJf hgroups hkle hklt hcorr.2.1 hcorr.2.2.2.1
  · -- a container-ORDINARY field: the repaired `EntryRead`
    have hr' : (((dJf q₀).rss i).getD j []).getD l false = false := by simpa using hr
    rcases hsh.ordF l hlF hr' with ⟨hrC, -⟩ | ⟨-, -, hklt, hread⟩
    · rw [hrC] at hrs; exact absurd hrs Bool.false_ne_true
    · exact copyEntryAt_of_read hread (hZ _ hklt (fun _ => trivial))


/-- **Step (iv), in the residual's own shape**: `CopyEntryA` exactly as
`NestedPinsEntry` spells it — at the group's pin `i` for the level
assignment and components and at constructor `(i', j)` — from
`nestedPinsEntry_at` at `i'`, the group's own `ψJEq`/`sameDs` moving
the reading data between its members. -/
theorem nestedPinsEntry_of (hμ : μ.verifiedChecks = true)
    (h : MutualFormersFacts V F g mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF)
    (hbk : b.k = p.k + pinsS.length)
    (m : EnvModel V env₂)
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), t < p.k → fms[t]? = some f →
      m.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t)
    {st : ElimState} (dJf : Nat → BlockModel V)
    (hgroups : ∀ q, q < pinsS.length → ∃ (q₀ kJ i : Nat),
      q = q₀ + i ∧ i < kJ ∧ GF st m q₀ kJ (dJf q₀))
    {ψ : Name → Nat} {ρp : Nat → V} (hρp : Sat V ((D).params ψ).reverse ρp)
    (heq : ∀ q, q < pinsS.length →
      pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q
        = lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q))
    {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀)) {i : Nat} (hi : i < kJ)
    {i' j : Nat} (hi' : i' < kJ) (hj : j < ((dJf q₀).ctorsM i').length) :
    CopyEntryA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
      (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
      (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
      (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
      (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
      (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
      (dJf q₀) ((pinsS.getD (q₀ + i) default).ψJ ψ) ((pinsS.getD (q₀ + i) default).Ds ψ)
      q₀ kJ i' j := by
  have hψ : ((D).pinAt (q₀ + i)).ψJ ψ = ((D).pinAt (q₀ + i')).ψJ ψ := G.syn.ψJEq i i' hi hi' ψ
  have hDs : ((D).pinAt (q₀ + i)).Ds ψ = ((D).pinAt (q₀ + i')).Ds ψ := by
    rw [G.syn.sameDs i hi ψ, ← G.syn.sameDs i' hi' ψ]
  simp only [show ∀ t : Nat, pinsS.getD t default = (D).pinAt t from fun _ => rfl]
  rw [hψ, hDs]
  exact nestedPinsEntry_at hμ h hbk m hleafM dJf hgroups hρp heq G hi' hj


/-- **THE TAIL, at ONE premise** (task #315 L-E, DESIGN §U.91): steps
(ii) and (iv) chained — the copies' entries at the auxiliary carrier,
for every group, from the single input `hle`: the containers' least
tuples lie below the auxiliary carrier at every pin.

`hle` is step (iii)'s conclusion, which `nestedPinsLe_of_rank`
produces from K.52's rank clauses and `hinst`, and `hinst` is
`nestedPinInstLe` at each instance's root.  So what the whole global
entry theorem now rests on, beyond this lane, is that one premise and
the two the rank induction carries. -/
theorem nestedPinsEntry_of_le (hμ : μ.verifiedChecks = true)
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
    (hle : ∀ q, q < pinsS.length →
      FamLe ((D).idx ψ ρp (p.k + q)) (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q)
        (lfpTuple ((D).w ψ) (p.k + pinsS.length) ((D).idx ψ ρp) (ΨA ψ ρp) (p.k + q)))
    {q₀ kJ : Nat} (G : GF st m q₀ kJ (dJf q₀)) {i : Nat} (hi : i < kJ)
    {i' j : Nat} (hi' : i' < kJ) (hj : j < ((dJf q₀).ctorsM i').length) :
    CopyEntryA (V := V) (nP := b.nP) (k := p.k) (resSort := f₀.s) (ppsA := ppsF) (W := W)
      (pins := pinsS) (offs := b.ownOffset) (mems := mutMems ctorsA.length (mutMemF b))
      (nFs := mutNFs ctorsA.length (mutNFOf ctorsA))
      (tgtsG := mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (rss := blkRss ctorsA kinds) (tlss := fun ψ => mutTlss ctorsA.length tssF ψ)
      (Eiss₀ := fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (Fss₀ := fun ψ => blkFss0 b ctorsA kinds dsF ψ)
      (Ess₀ := fun ψ => mutEss0 ctorsA.length esF ψ) (ψ := ψ) (ρp := ρp)
      (dJf q₀) ((pinsS.getD (q₀ + i) default).ψJ ψ) ((pinsS.getD (q₀ + i) default).Ds ψ)
      q₀ kJ i' j :=
  nestedPinsEntry_of hμ h hbk m hleafM dJf hgroups hρp
    (nestedPinsEq_of_le hμ h h3 hbk m hleafM dJf hgroups hρp hle) G hi hi' hj

end Assembly

/-! ## The residual, ASSEMBLED -/

/-- **STEP (iii) AT THE RUN, as a named premise** (task #315 L-E,
DESIGN §U.92): the containers' least tuples lie below the auxiliary
carrier at every pin, for any assignment `dJf` of block models to the
groups' base pins that the run's own groups back.

Quantified over `dJf` and its `hgroups` rather than over a chosen one,
because the choice is made by the consumer: `nestedPinsEntry_of_le_all`
builds an assignment out of `NestedPinSynFacts.groups` and the group
it is handed, and applies this at exactly that one. -/
@[expose] def NestedPinsLe (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  NestedPinsIdsAt V μ F fun {env} _ p st b fms f₀ ctorsA kinds ppsF W idxF dsF esF srcsF fvsPF
      xrestF eissF tssF ctorsR dsR xFvsR pinsS mp₁' _ _ _ =>
    ∀ dJf : Nat → BlockModel V,
      (∀ q, q < pinsS.length → ∃ (a kk ii : Nat), q = a + ii ∧ ii < kk ∧
        GroupFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
          (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
          (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
          (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
          st mp₁'.base2 a kk (dJf a)) →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
      Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρp →
      ∀ q, q < pinsS.length →
        FamLe ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF
            fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).idx ψ ρp (p.k + q))
          (pinLfp st pinsS dJf (f₀.s.eval ψ) ψ ρp q)
          (lfpTuple ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
              srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).w ψ)
            (p.k + pinsS.length)
            ((nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF
              fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS).idx ψ ρp)
            (nestedΨ (V := V) b.nP p.k f₀.s ppsF W pinsS b.ownOffset
              (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
              (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
              (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
              (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)
              ψ ρp)
            (p.k + q))



/-- **THE RESIDUAL, DISCHARGED** (task #315 L-E, DESIGN §U.92):
`NestedPinsEntry` — the copies' entries at the auxiliary carrier, for
every group of every accepted nested block — from lane L-B's shape
residual and step (iii) at the run.

The assignment `dJf` the entry theorem quantifies over is BUILT here,
not assumed: the group the residual hands over serves its own base pin
and `NestedPinSynFacts.groups` serves every other, chosen with
`Classical.epsilon` since nothing names a group's block model at its
base.  The two group sizes agree because both are the pin table's own
`grpSize` at the base (`NestedPinGroupSyn.grp`), which is what lets the
handed group and a chosen one meet.

Stated as an application of the residual so that the elaborator, and
not a reading of the two statements, is what certifies that this is a
discharge. -/
theorem nestedPinsEntry_of_le_all {F : Nat} (hSh : NestedPinsShape V μ F)
    (hLe : NestedPinsLe V μ F) : NestedPinsEntry V μ F := by
  classical
  intro env mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF
    dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
  intro i hi ψ ρp hρp i' hi' j hj
  -- a group's syntactic facts, with its identity and shape
  have mkGF : ∀ (a kk : Nat) (d : BlockModel V),
      NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
        st mp₁'.base2 a kk d →
      GroupFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
        st mp₁'.base2 a kk d := by
    intro a kk d S'
    refine ⟨S', ?_, ?_⟩
    · intro i₂ hi₂ ψ₂ i₃ hi₃
      exact nestedPinsIdx mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds
        mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR
        a kk d S' i₂ hi₂ ψ₂ i₃ hi₃
    · intro i₂ hi₂ cvT caps hf ψ₂ ρ₂ hρ₂ i₃ j₂ hi₃ hj₂
      exact hSh mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
        idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR a kk d S'
        i₂ hi₂ cvT caps hf ψ₂ ρ₂ hρ₂ i₃ hi₃ j₂ hj₂
  -- a group's size is the pin table's own `grpSize` at its base
  have hsize : ∀ (a kk' : Nat) (d : BlockModel V),
      NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
        (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
        (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
        (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
        st mp₁'.base2 a kk' d →
      (st.pins.getD a default).grpSize = kk' := by
    intro a kk' d S''
    have := (S''.grp 0 S''.kpos).2
    rwa [Nat.add_zero] at this
  -- the assignment: the handed group at its own base, a chosen one elsewhere
  obtain ⟨dJf, hdJf₀, hgroups⟩ :
      ∃ dJf : Nat → BlockModel V, dJf q₀ = dJ ∧
        ∀ q, q < pinsS.length → ∃ (a kk ii : Nat), q = a + ii ∧ ii < kk ∧
          GroupFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
            (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
            (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
            (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
            st mp₁'.base2 a kk (dJf a) := by
    refine ⟨fun a => if a = q₀ then dJ else Classical.epsilon (fun d => ∃ kk : Nat, Nonempty
        (NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
          (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
          (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
          (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
          st mp₁'.base2 a kk d)), by simp, ?_⟩
    intro q hq
    obtain ⟨a, kk, ii, dJ', hqe, hii, S'⟩ := SF.groups dsR xFvsR q hq
    by_cases ha : a = q₀
    · subst ha
      obtain rfl : kk = kJ := by rw [← hsize a kk dJ' S', hsize a kJ dJ S]
      exact ⟨a, kk, ii, hqe, hii, by simpa using mkGF a kk dJ S⟩
    · obtain ⟨kk₀, ⟨S₀⟩⟩ := Classical.epsilon_spec
        (p := fun d => ∃ kk : Nat, Nonempty
          (NestedPinGroupSyn (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
            (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
            (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
            (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
            st mp₁'.base2 a kk d)) ⟨dJ', kk, ⟨S'⟩⟩
      obtain rfl : kk₀ = kk := by rw [← hsize a kk₀ _ S₀, hsize a kk dJ' S']
      refine ⟨a, kk₀, ii, hqe, hii, ?_⟩
      simpa only [if_neg ha] using mkGF a kk₀ _ S₀
  have hbk : b.k = p.k + pinsS.length := by rw [R.hbk, SF.pinsLen]
  have hle := hLe mp p st b envAux stored ctorsR fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W
    idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF mp₁' R pinsS SF dsR xFvsR q₀ kJ dJ S
    dJf hgroups ψ ρp hρp
  have hGF' : GroupFacts (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
      (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
      (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
      (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
      st mp₁'.base2 q₀ kJ (dJf q₀) := by
    rw [hdJf₀]; exact mkGF q₀ kJ dJ S
  have hj' : j < ((dJf q₀).ctorsM i').length := by rw [hdJf₀]; exact hj
  have hres := nestedPinsEntry_of_le R.hμ R.h R.h3 hbk mp₁'.base2 R.hleafM' dJf hgroups hρp hle
    hGF' hi hi' hj'
  rw [hdJf₀] at hres
  exact hres

end ConLeche.Model
