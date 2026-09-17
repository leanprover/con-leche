module

public import ConLeche.Model.Inductives.BlockComposed
public import ConLeche.Semantics.Tower.InstAll
public section

/-!
# The instantiation law at the pins — `hfit` (task #315, M6 s5; L-C; L-E)

`ofNested_pin_block_of_fit_at` (`BlockComposed.lean`) reduced `pinLeaf`'s
set equality to TWO fit hypotheses: a field spine fits the COPY's
constructor `offs (k + q₀ + i) + j` of the auxiliary block at the
joined tuple `segJoin (k + q₀) kJ L⁺ Y` iff it is the CONTAINER's
`ChainFit` at `Y` for its member `i`'s constructor `j` — AT the
container's least tuple `Y = LJ` — and one direction (container to
copy) at the tuples `Y` below it; both at the pin's frame `ρJ =
consList ⟦Ds⟧ ρp`.  This module proves them from the INSTANTIATION
IDENTITIES of the copy's readings (DESIGN §U.17, §U.24, §U.36):

* `fitsFrom_iff_frames`: `FitsFrom` across TWO frames is a congruence
  of the per-field ENTRY SETS at every fitting prefix;
  `fitsFrom_iff_frames_spine`/`fitsFrom_imp_frames_spine` the twins
  that carry the first chain's REAL-domain fit (`SpineFit`) along —
  what the container's slot laws at its carrier need;
* `TargetView`: the block's targets as a copy sees them — the members'
  and pins' counts, the block's sort, a target's index universe, index
  telescope and (for a pin) components, and every target's STORED
  READING (`targetRead`) at the parameter depth; instantiated at the
  auxiliary lists (`nestedTV`) and at a stored block model
  (`BlockModel.targetView`, `NestedPremise.lean`);
* `CopyCtorShape` (task #315 L-E, the ENTRY-FREE half of what used to be
  `CopyCtorInst`): per constructor, the copy's readings are the
  container's with the pin's components substituted at the field's
  depth (`AnnotTerm.instAll`, `Semantics/Tower/InstAll.lean`): a
  container-recursive field at a MEMBER target is copy-recursive at
  the copy of its target with the telescope and index expressions
  instantiated (`recF`); a container-ordinary field is either
  copy-ordinary whose domain READS as the container's instantiated
  (the stored copy is the elimination's rewrite only up to the
  constructors' positivity normalisation, which `whnf`s), or
  copy-recursive at a target OUTSIDE the group — the elimination's
  rewrite of an occurrence inside the components — whose entry is the
  TARGET'S STORED READING (`EntryRead`: the container's domain read at
  the pin's frame is the Π-tower over the copy's telescope of the
  target's reading at the copy's index expressions, with the index fit
  and the bits) (`ordF`); a container-recursive field at one of the
  CONTAINER'S OWN PINS (a container that is itself nested) is
  copy-recursive at the block's CORRESPONDING pin (`PinCorr`: the same
  stored reading at the instantiated components, the same index
  universe and telescope), outside the group (`pinF`); the result's
  index readings instantiated (`es`);
* `CopyEntryAt`/`CopyEntryOut`: the ENTRY identities at a tuple `Z` —
  at a prefix fitting the container's real domains, the container's
  domain read at the pin's frame IS the copy's slot at `Z`, at every
  copy-recursive field targeting outside the group; the residual the
  fits need beyond the shape, a theorem of the WHOLE block
  (`nestedPinLeaf_all`), since a pin target's entry is another
  group's `pinLeaf` and the pin reference graph is cyclic at a
  self-nested container (DESIGN §U.36); `copyEntryAt_of_read` turns an
  `EntryRead` into the entry at any tuple whose target family reads
  the stored reading;
* `CopyCtorShape.fit_iff_at`/`.fit_imp` = the fits at one constructor,
  from the shape and the entries: at the carrier a container-recursive
  field's slot IS its real domain (`IsBlockModels.real_dom_eq` — the
  container's own `leaf`/`pinLeaf`, what DESIGN §U.18 (e) called
  `pinFix`), below it the slot is within the real domain
  (`IsBlockModels.slotAt_mono` — `pinMono` at a pin target);
  `CopyShapeA`/`CopyEntryA` the shape and the entries at the auxiliary
  lists; `hfit_at_of_inst`/`hfit_le_of_inst` = the two hypotheses
  verbatim; **`ofNested_pin_block_of_inst`** and
  **`ofNested_pinLeaf_of`**: `pinLeaf` for `ofNested` at a pin group,
  the container's pin list FREE, from the shape, the entries, the
  universe facts, the container's block model and its typing
  (`FormersTyped`, `PinsTyped`).

The universe facts: the block's sort EQUALS the container's at the
pin's level assignment (`hw`, `mutualCrossChecks`' `isEquiv` at the
copy's sort); the block's index universe at a group component IS the
container's (`hu`, the pins' recorded universes — `nestedU`, DESIGN
§U.22).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `FitsFrom` across two frames -/

/-- **`FitsFrom` congruence across two frames**: along two domain lists
of one length, whenever at every position and every prefix fitting
BOTH chains the two ENTRY sets agree (the slot at the recursive
positions, the domain's reading otherwise, each at its own frame), the
fits agree. -/
theorem fitsFrom_iff_frames {rs rs' : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ ρ' : Nat → V} {Fs Fs' : List AnnotTerm} {fs : List V},
      Fs.length = Fs'.length →
      (∀ l, l < Fs.length → ∀ fs₁ : List V, fs₁.length = l →
        FitsFrom rs slot i ρ (Fs.take l) fs₁ → FitsFrom rs' slot' i ρ' (Fs'.take l) fs₁ →
        (if rs.getD (i + l) false then slot (i + l) (consList fs₁ ρ)
          else interp V (consList fs₁ ρ) (Fs.getD l default))
        = (if rs'.getD (i + l) false then slot' (i + l) (consList fs₁ ρ')
          else interp V (consList fs₁ ρ') (Fs'.getD l default))) →
      (FitsFrom rs slot i ρ Fs fs ↔ FitsFrom rs' slot' i ρ' Fs' fs)
  | _, _, _, [], [], [], _, _ => Iff.rfl
  | _, _, _, [], [], _ :: _, _, _ => Iff.rfl
  | _, _, _, [], _ :: _, _, hlen, _ => by simp at hlen
  | _, _, _, _ :: _, [], _, hlen, _ => by simp at hlen
  | _, _, _, _ :: _, _ :: _, [], _, _ => Iff.rfl
  | i, ρ, ρ', F :: Fs, F' :: Fs', a :: fs, hlen, hent => by
    show (a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
        FitsFrom rs slot (i + 1) (cons a ρ) Fs fs) ↔
      (a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') ∧
        FitsFrom rs' slot' (i + 1) (cons a ρ') Fs' fs)
    have h0 := hent 0 (by simp) [] rfl trivial trivial
    simp only [Nat.add_zero, consList_nil, List.getD_cons_zero] at h0
    have hmem : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ↔
        a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') := by rw [h0]
    have htail : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) →
        (FitsFrom rs slot (i + 1) (cons a ρ) Fs fs ↔ FitsFrom rs' slot' (i + 1) (cons a ρ') Fs' fs) := by
      intro ha
      refine fitsFrom_iff_frames (by simpa using hlen) fun l hl fs₁ hl₁ hf hf' => ?_
      have := hent (l + 1) (by simp; omega) (a :: fs₁) (by simp [hl₁])
        (by
          show a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
            FitsFrom rs slot (i + 1) (cons a ρ) (Fs.take l) fs₁
          exact ⟨ha, hf⟩)
        (by
          show a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') ∧
            FitsFrom rs' slot' (i + 1) (cons a ρ') (Fs'.take l) fs₁
          exact ⟨hmem.mp ha, hf'⟩)
      simpa only [consList_cons, List.getD_cons_succ, show i + (l + 1) = i + 1 + l from by omega]
        using this
    exact ⟨fun ⟨ha, hf⟩ => ⟨hmem.mp ha, (htail ha).mp hf⟩,
      fun ⟨ha', hf'⟩ => ⟨hmem.mpr ha', (htail (hmem.mpr ha')).mpr hf'⟩⟩

/-! ## `FitsFrom` across two frames, the fitting prefix carried -/

/-- **`FitsFrom` congruence across two frames**: along two domain lists
of one length, whenever at every position and every prefix fitting
BOTH chains — and fitting the first chain's REAL domains (`SpineFit`),
which the entries' inclusion in them extends position by position —
the first ENTRY set is within its real domain and the two entry sets
agree (the slot at a recursive position, the domain's reading
otherwise, each at its own frame), the fits agree.  The carried spine
fit is what a slot's laws at the carrier need
(`IsBlockModels.real_dom_eq`: at a fitting prefix a slot at the
carrier IS the real domain). -/
theorem fitsFrom_iff_frames_spine {rs rs' : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ ρ' : Nat → V} {Fs Fs' : List AnnotTerm} {fs : List V},
      Fs.length = Fs'.length →
      (∀ l, l < Fs.length → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ (Fs.take l) fs₁ →
        FitsFrom rs slot i ρ (Fs.take l) fs₁ → FitsFrom rs' slot' i ρ' (Fs'.take l) fs₁ →
        (if rs.getD (i + l) false then slot (i + l) (consList fs₁ ρ)
            else interp V (consList fs₁ ρ) (Fs.getD l default))
          ⊆ˢ interp V (consList fs₁ ρ) (Fs.getD l default) ∧
        (if rs.getD (i + l) false then slot (i + l) (consList fs₁ ρ)
            else interp V (consList fs₁ ρ) (Fs.getD l default))
          = (if rs'.getD (i + l) false then slot' (i + l) (consList fs₁ ρ')
            else interp V (consList fs₁ ρ') (Fs'.getD l default))) →
      (FitsFrom rs slot i ρ Fs fs ↔ FitsFrom rs' slot' i ρ' Fs' fs)
  | _, _, _, [], [], [], _, _ => Iff.rfl
  | _, _, _, [], [], _ :: _, _, _ => Iff.rfl
  | _, _, _, [], _ :: _, _, hlen, _ => by simp at hlen
  | _, _, _, _ :: _, [], _, hlen, _ => by simp at hlen
  | _, _, _, _ :: _, _ :: _, [], _, _ => Iff.rfl
  | i, ρ, ρ', F :: Fs, F' :: Fs', a :: fs, hlen, hent => by
    show (a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
        FitsFrom rs slot (i + 1) (cons a ρ) Fs fs) ↔
      (a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') ∧
        FitsFrom rs' slot' (i + 1) (cons a ρ') Fs' fs)
    have h0 := hent 0 (by simp) [] rfl trivial trivial trivial
    simp only [Nat.add_zero, consList_nil, List.getD_cons_zero] at h0
    have hmem : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ↔
        a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') := by rw [h0.2]
    have htail : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) →
        (FitsFrom rs slot (i + 1) (cons a ρ) Fs fs ↔ FitsFrom rs' slot' (i + 1) (cons a ρ') Fs' fs) := by
      intro ha
      refine fitsFrom_iff_frames_spine (by simpa using hlen) fun l hl fs₁ hl₁ hsp hf hf' => ?_
      have := hent (l + 1) (by simp; omega) (a :: fs₁) (by simp [hl₁])
        (by
          show a ∈ˢ interp V ρ F ∧ SpineFit (cons a ρ) (Fs.take l) fs₁
          exact ⟨h0.1 a ha, hsp⟩)
        (by
          show a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
            FitsFrom rs slot (i + 1) (cons a ρ) (Fs.take l) fs₁
          exact ⟨ha, hf⟩)
        (by
          show a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') ∧
            FitsFrom rs' slot' (i + 1) (cons a ρ') (Fs'.take l) fs₁
          exact ⟨hmem.mp ha, hf'⟩)
      simpa only [consList_cons, List.getD_cons_succ, show i + (l + 1) = i + 1 + l from by omega]
        using this
    exact ⟨fun ⟨ha, hf⟩ => ⟨hmem.mp ha, (htail ha).mp hf⟩,
      fun ⟨ha', hf'⟩ => ⟨hmem.mpr ha', (htail (hmem.mpr ha')).mpr hf'⟩⟩

/-- **`FitsFrom` implication across two frames** — the one-directional
twin: the first chain's entries within its real domains and within the
second chain's entries, at every prefix fitting both chains and the
first's real domains, carry a fit of the first chain to the second. -/
theorem fitsFrom_imp_frames_spine {rs rs' : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ ρ' : Nat → V} {Fs Fs' : List AnnotTerm} {fs : List V},
      Fs.length = Fs'.length →
      (∀ l, l < Fs.length → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρ (Fs.take l) fs₁ →
        FitsFrom rs slot i ρ (Fs.take l) fs₁ → FitsFrom rs' slot' i ρ' (Fs'.take l) fs₁ →
        (if rs.getD (i + l) false then slot (i + l) (consList fs₁ ρ)
            else interp V (consList fs₁ ρ) (Fs.getD l default))
          ⊆ˢ interp V (consList fs₁ ρ) (Fs.getD l default) ∧
        (if rs.getD (i + l) false then slot (i + l) (consList fs₁ ρ)
            else interp V (consList fs₁ ρ) (Fs.getD l default))
          ⊆ˢ (if rs'.getD (i + l) false then slot' (i + l) (consList fs₁ ρ')
            else interp V (consList fs₁ ρ') (Fs'.getD l default))) →
      FitsFrom rs slot i ρ Fs fs → FitsFrom rs' slot' i ρ' Fs' fs
  | _, _, _, [], [], [], _, _, h => h
  | _, _, _, [], [], _ :: _, _, _, h => h
  | _, _, _, [], _ :: _, _, hlen, _, _ => by simp at hlen
  | _, _, _, _ :: _, [], _, hlen, _, _ => by simp at hlen
  | _, _, _, _ :: _, _ :: _, [], _, _, h => h
  | i, ρ, ρ', F :: Fs, F' :: Fs', a :: fs, hlen, hent, h => by
    have h' : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
        FitsFrom rs slot (i + 1) (cons a ρ) Fs fs := h
    obtain ⟨ha, hf⟩ := h'
    show a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') ∧
      FitsFrom rs' slot' (i + 1) (cons a ρ') Fs' fs
    have h0 := hent 0 (by simp) [] rfl trivial trivial trivial
    simp only [Nat.add_zero, consList_nil, List.getD_cons_zero] at h0
    refine ⟨h0.2 a ha, ?_⟩
    refine fitsFrom_imp_frames_spine (by simpa using hlen) (fun l hl fs₁ hl₁ hsp hf₁ hf' => ?_) hf
    have := hent (l + 1) (by simp; omega) (a :: fs₁) (by simp [hl₁])
      (by
        show a ∈ˢ interp V ρ F ∧ SpineFit (cons a ρ) (Fs.take l) fs₁
        exact ⟨h0.1 a ha, hsp⟩)
      (by
        show a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
          FitsFrom rs slot (i + 1) (cons a ρ) (Fs.take l) fs₁
        exact ⟨ha, hf₁⟩)
      (by
        show a ∈ˢ (if rs'.getD i false then slot' i ρ' else interp V ρ' F') ∧
          FitsFrom rs' slot' (i + 1) (cons a ρ') (Fs'.take l) fs₁
        exact ⟨h0.2 a ha, hf'⟩)
    simpa only [consList_cons, List.getD_cons_succ, show i + (l + 1) = i + 1 + l from by omega]
      using this

/-! ## The slot and the index set under instantiation -/

/-- `tupW` reads its universe only through `= 0`. -/
theorem tupW_zero_agree {u u' : Nat} (hz : u = 0 ↔ u' = 0) (is : List V) :
    tupW u is = tupW u' is := by
  by_cases hu : u = 0
  · rw [hu, hz.mp hu]
  · rw [tupW_pos hu, tupW_pos fun h => hu (hz.mpr h)]

/-- **The slot under instantiation**: a recursive slot whose telescope
and index expressions are the container's instantiated at the fields'
depth, read at the fields' frame over the block's frame, is the
container's slot at the fields' frame over the pin's frame — at the
same family, when the two sorts and the two index universes agree on
`= 0`. -/
theorem slotSet_instTele {w w' u u' : Nat} (hw : w = 0 ↔ w' = 0) (hu : u = 0 ↔ u' = 0)
    (ds : List AnnotTerm) (ρ : Nat → V) (fs : List V) {tlC tlJ : List (Nat × Nat × AnnotTerm)}
    (htl : tlC.map (·.2.2) = instTele ds fs.length (tlJ.map (·.2.2))) (Eis : List AnnotTerm)
    (X : V) :
    slotSet w u (consList fs ρ) tlC (Eis.map (AnnotTerm.instAll ds (fs.length + tlJ.length))) X
      = slotSet w' u' (consList fs (consList (ds.map (interp V ρ)) ρ)) tlJ Eis X := by
  unfold slotSet
  rw [htl]
  refine piTele_instTele hw ds ρ (tlJ.map (·.2.2)) fs [] fun bs hbs => ?_
  simp only [List.nil_append, List.map_map]
  rw [tupW_zero_agree hu]
  congr 2
  refine List.map_congr_left fun E _ => ?_
  show interp V (consList bs (consList fs ρ)) (AnnotTerm.instAll ds (fs.length + tlJ.length) E)
    = interp V (consList bs (consList fs (consList (ds.map (interp V ρ)) ρ))) E
  have hlen : fs.length + tlJ.length = (fs ++ bs).length := by
    rw [List.length_append, hbs.length_eq, List.length_map]
  rw [← consList_append fs bs ρ, ← consList_append fs bs (consList (ds.map (interp V ρ)) ρ), hlen,
    interp_instAll]

/-- The index-tuple set under instantiation. -/
theorem idxSet_instTele {u u' : Nat} (hu : u = 0 ↔ u' = 0) (ds : List AnnotTerm) (ρ : Nat → V)
    (Ids : List AnnotTerm) :
    idxSet u ρ (instTele ds 0 Ids) = idxSet u' (consList (ds.map (interp V ρ)) ρ) Ids := by
  unfold idxSet
  have := towerSet_instTele hu ds ρ Ids []
  simpa only [consList_nil, List.length_nil] using this

/-! ## The block's targets, viewed from a copy -/

/-- **The block's targets, viewed from a copy** (task #315 L-E, DESIGN
§U.36): what a copy's constructor identities read of the block its
copy lives in — the member count `k`, the pin count `n`, the block's
sort value `w`, a target's index universe `u`, its index telescope
`Ids` at its own frame, a pin target's components `Ds` at the block's
parameter depth and every target's STORED READING `EA` at that depth
(`targetRead`: a member's former at the parameter variables, a pin's
container at the pin's components).  The auxiliary lists instantiate
it (`nestedTV`), and so does a stored block model with its pins'
constructors (`BlockModel.targetView`), which is what lets the
identities be stated ONCE for the block being installed and for the
containers already stored (`PinShapes`). -/
structure TargetView (V : Type w) where
  /-- the members -/
  k : Nat
  /-- the pins -/
  n : Nat
  /-- the block's sort value -/
  w : Nat
  /-- a target's index universe -/
  u : Nat → Nat
  /-- a target's index telescope, at its own frame -/
  Ids : Nat → List AnnotTerm
  /-- a pin target's components at the block's parameter depth -/
  Ds : Nat → List AnnotTerm
  /-- a target's stored reading at the block's parameter depth -/
  EA : Nat → AnnotTerm
  /-- a target's NAME: the member's, a pin's container's (task #315 L-E,
  step (iii): the correspondence of pins is structural) -/
  J : Nat → Name
  /-- a pin target's level arguments -/
  lvls : Nat → List Level

namespace TargetView

/-- A target's frame over the block's parameter frame: the parameters
for a member, the pin's frame — the components' values over the
parameters — for a pin. -/
@[expose] noncomputable def frame (TV : TargetView V) (ρp : Nat → V) (t : Nat) : Nat → V :=
  if t < TV.k then ρp else consList ((TV.Ds t).map (interp V ρp)) ρp

theorem frame_of_mem (TV : TargetView V) (ρp : Nat → V) {t : Nat} (ht : t < TV.k) :
    TV.frame ρp t = ρp := by simp only [frame, if_pos ht]

theorem frame_of_pin (TV : TargetView V) (ρp : Nat → V) {t : Nat} (ht : ¬ t < TV.k) :
    TV.frame ρp t = consList ((TV.Ds t).map (interp V ρp)) ρp := by simp only [frame, if_neg ht]

end TargetView

/-- **The targets' stored readings at the parameter depth**: member
`t`'s former at the parameter variables, pin `q`'s container at the
pin's level assignment and components. -/
@[expose] def targetRead (acval : Name → (Name → Nat) → AnnotTerm) (memberNames : List Name)
    (pins : List PinSyn) (nP k : Nat) (ψ : Name → Nat) (t : Nat) : AnnotTerm :=
  if t < k then AnnotTerm.mkAppN (acval (memberNames.getD t .anonymous) ψ) (paramBvarsAt nP nP)
  else AnnotTerm.mkAppN (acval (pins.getD (t - k) default).J ((pins.getD (t - k) default).ψJ ψ))
    ((pins.getD (t - k) default).Ds ψ)

omit [SetTheory V] in
theorem targetRead_of_mem {acval : Name → (Name → Nat) → AnnotTerm} {memberNames : List Name}
    {pins : List PinSyn} {nP k : Nat} {ψ : Name → Nat} {t : Nat} (ht : t < k) :
    targetRead acval memberNames pins nP k ψ t
      = AnnotTerm.mkAppN (acval (memberNames.getD t .anonymous) ψ) (paramBvarsAt nP nP) := by
  simp only [targetRead, if_pos ht]

omit [SetTheory V] in
theorem targetRead_of_pin {acval : Name → (Name → Nat) → AnnotTerm} {memberNames : List Name}
    {pins : List PinSyn} {nP k : Nat} {ψ : Name → Nat} {t : Nat} (ht : ¬ t < k) :
    targetRead acval memberNames pins nP k ψ t
      = AnnotTerm.mkAppN (acval (pins.getD (t - k) default).J ((pins.getD (t - k) default).ψJ ψ))
          ((pins.getD (t - k) default).Ds ψ) := by
  simp only [targetRead, if_neg ht]

/-! ## The identities of one copy's constructor, entry-free -/

section Shape

variable (TV : TargetView V) (acval : Name → (Name → Nat) → AnnotTerm) (dJ : BlockModel V)
  (ψJ : Name → Nat) (Ds : List AnnotTerm) (lpsJ : List Name) (lvlsJ : List Level)

/-- **A block pin CORRESPONDS to a container's own pin** (task #315 L-E):
the block's target `t` is the pin whose stored reading is the
container's pin's container at the container's pin's components
instantiated at the copy's components, with the same index universe
and index telescope — what a container-recursive field at one of the
CONTAINER'S OWN pins becomes in the copy (`CopyCtorShape.pinF`).  The
level assignment is compared at the READING (`acval` at the two
assignments), never as functions — and, SYNTACTICALLY, the block pin's
container NAME is the container's pin's and its LEVEL ARGUMENTS are
the container's pin's instantiated at the outer pin's (`lpsJ`, the
container's level parameters, `:= lvlsJ`, the outer pin's level
arguments): what the entry theorem's step (iii) transfers a spine
through (DESIGN §U.39 — the readings alone do not determine the
constructors' readings at the target). -/
@[expose] def PinCorr (t qK : Nat) : Prop :=
  TV.EA t = AnnotTerm.mkAppN (acval (dJ.pinAt qK).J ((dJ.pinAt qK).ψJ ψJ))
      (((dJ.pinAt qK).Ds ψJ).map (AnnotTerm.instAll Ds 0)) ∧
  TV.Ds t = ((dJ.pinAt qK).Ds ψJ).map (AnnotTerm.instAll Ds 0) ∧
  TV.u t = (dJ.pinAt qK).u ψJ ∧
  TV.Ids t = (dJ.pinAt qK).Ids ψJ ∧
  TV.J t = (dJ.pinAt qK).J ∧
  TV.lvls t = ((dJ.pinAt qK).lvls).map (Level.subst lpsJ lvlsJ)

variable (tg : Nat → Nat) (tls : List (List (Nat × Nat × AnnotTerm))) (Eis : List (List AnnotTerm))
  (ρp : Nat → V) (i j : Nat)

/-- **The entry at the STORED READING** (task #315 L-E, DESIGN §U.36):
the shape of a container-ordinary field the elimination rewrote — the
copy's field is recursive at a target `tg l` outside the group — reads
the container's domain at the pin's frame as the Π-tower over the
copy's telescope of the TARGET's stored reading (`TargetView.EA`,
lifted past the fields and the telescope) at the copy's index
expressions; the telescope's bits are the block's regime; and at a
prefix fitting the container's real domains the index expressions'
readings fit the target's index telescope at the target's frame.  The
three facts are what turns the reading into the copy's SLOT at any
tuple whose target families read as the stored readings
(`copyEntryAt_of_read`) — the entry at the auxiliary carrier is then a
theorem of the WHOLE block, not a per-group obligation. -/
@[expose] def EntryRead (l : Nat) : Prop :=
  (∀ fs₁ : List V, fs₁.length = l →
    interp V (consList fs₁ (consList (Ds.map (interp V ρp)) ρp)) (((dJ.Fss i ψJ).getD j []).getD l default)
      = interp V (consList fs₁ ρp) (mkPisAV (tls.getD l [])
          (AnnotTerm.mkAppN ((TV.EA (tg l)).liftN (l + (tls.getD l []).length) 0) (Eis.getD l [])))) ∧
  (∀ e ∈ tls.getD l [], (e.2.1 = 0 ↔ TV.w = 0)) ∧
  (∀ fs₁ bs : List V, fs₁.length = l →
    SpineFit (consList (Ds.map (interp V ρp)) ρp) (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
    SpineFit (consList fs₁ ρp) ((tls.getD l []).map (·.2.2)) bs →
    SpineFit (TV.frame ρp (tg l)) (TV.Ids (tg l))
      ((Eis.getD l []).map (interp V (consList bs (consList fs₁ ρp)))))

/-- **The entry identity at a tuple `Z`**, at one field: at a prefix
fitting the container's real domains, the CONTAINER's domain read at
the pin's frame IS the copy's slot at `Z`, taken at the field's target
(`CopyEntry` of DESIGN §U.23, re-based on the container's prefix fit
and generic in the tuple, task #315 L-E). -/
@[expose] def CopyEntryAt (w : Nat) (u : Nat → Nat) (Z : Nat → V) (l : Nat) : Prop :=
  ∀ fs₁ : List V, fs₁.length = l →
    SpineFit (consList (Ds.map (interp V ρp)) ρp) (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
    interp V (consList fs₁ (consList (Ds.map (interp V ρp)) ρp)) (((dJ.Fss i ψJ).getD j []).getD l default)
      = slotSet w (u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) (Z (tg l))

variable (base kJ : Nat) (Fs : List AnnotTerm) (rs : List Bool)

/-- **The entry identities at every copy-recursive field OUTSIDE the
group** — the residual the fits need beyond the shape; a theorem of
the whole block (`nestedPinLeaf_all`). -/
@[expose] def CopyEntryOut (w : Nat) (u : Nat → Nat) (Z : Nat → V) : Prop :=
  ∀ l, l < Fs.length → rs.getD l false = true → ¬ (base ≤ tg l ∧ tg l < base + kJ) →
    CopyEntryAt dJ ψJ Ds tg tls Eis ρp i j w u Z l

variable (Es : List AnnotTerm)

/-- **The instantiation identities of one copy's constructor, ENTRY-FREE**
(task #315 L-E, DESIGN §U.36 — `CopyCtorInst` of §U.17/§U.24 with the
entry conjunct of `ordF`'s right arm and of `pinF` split off): the
container `dJ`'s member `i`, constructor `j`, copied at the pin group
whose first copy sits at position `base` of the block's targets, has
`kJ` members, reads its components as `Ds` (at the block's parameter
frame `ρp`) and its level assignment as `ψJ`; the copy's constructor's
data are `Fs`/`rs`/`tg`/`tls`/`Eis`/`Es` (its field domains at the
block's frame, recursive flags, targets, reflexive telescopes, index
expressions and result index readings).  Each container field reads in
the copy as its instantiation at the field's depth
(`AnnotTerm.instAll`), with the container's MEMBER targets moved to the
group's copies (`recF`); a container-ordinary field is copy-ordinary
whose domain READS as the container's instantiated (the stored copy is
the elimination's rewrite only up to the constructors' positivity
normalisation, which `whnf`s), or copy-recursive at a target OUTSIDE
the group whose entry is the target's STORED READING (`EntryRead`); a
container-recursive field at one of the CONTAINER'S OWN pins (a
container that is itself nested, task #315 L-C) is copy-recursive at
the block's pin CORRESPONDING to the container's (`PinCorr`), its
telescope and index expressions instantiated (`pinF`); the result's
index readings are instantiated (`es`).  What the run proves per group
(`NestedPinsShape`, lane L-B), and what a stored container's own pins
carry (`PinShapes`). -/
structure CopyCtorShape : Prop where
  /-- the copy has the container's field count -/
  len : Fs.length = ((dJ.Fss i ψJ).getD j []).length
  /-- a container-recursive field at a MEMBER target: copy-recursive at
  the group's copy of its target, telescope and index expressions
  instantiated -/
  recF : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
    ((dJ.rss i).getD j []).getD l false = true → dJ.tgts i j l < dJ.k →
    rs.getD l false = true ∧ tg l = base + dJ.tgts i j l ∧
    (tls.getD l []).map (·.2.2) = instTele Ds l ((((dJ.tlss i ψJ).getD j []).getD l []).map (·.2.2)) ∧
    Eis.getD l [] = (((dJ.Eiss i ψJ).getD j []).getD l []).map
      (AnnotTerm.instAll Ds (l + (((dJ.tlss i ψJ).getD j []).getD l []).length))
  /-- a container-ordinary field: copy-ordinary whose domain READS as
  the container's instantiated, or copy-recursive outside the group
  with the entry at the target's stored reading -/
  ordF : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
    ((dJ.rss i).getD j []).getD l false = false →
    (rs.getD l false = false ∧
      ∀ fs₁ : List V, fs₁.length = l →
        interp V (consList fs₁ ρp) (Fs.getD l default)
          = interp V (consList fs₁ ρp)
              (AnnotTerm.instAll Ds l (((dJ.Fss i ψJ).getD j []).getD l default))) ∨
    (rs.getD l false = true ∧ ¬ (base ≤ tg l ∧ tg l < base + kJ) ∧ tg l < TV.k + TV.n ∧
      EntryRead TV dJ ψJ Ds tg tls Eis ρp i j l)
  /-- a container-recursive field at one of the container's OWN pins:
  copy-recursive at the block's corresponding pin, outside the group,
  telescope and index expressions instantiated -/
  pinF : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
    ((dJ.rss i).getD j []).getD l false = true → ¬ dJ.tgts i j l < dJ.k →
    rs.getD l false = true ∧ ¬ (base ≤ tg l ∧ tg l < base + kJ) ∧
    TV.k ≤ tg l ∧ tg l < TV.k + TV.n ∧
    PinCorr TV acval dJ ψJ Ds lpsJ lvlsJ (tg l) (dJ.tgts i j l - dJ.k) ∧
    (tls.getD l []).map (·.2.2) = instTele Ds l ((((dJ.tlss i ψJ).getD j []).getD l []).map (·.2.2)) ∧
    Eis.getD l [] = (((dJ.Eiss i ψJ).getD j []).getD l []).map
      (AnnotTerm.instAll Ds (l + (((dJ.tlss i ψJ).getD j []).getD l []).length))
  /-- the result's index readings instantiated under the fields -/
  es : ∀ l, l < (dJ.IdsM i ψJ).length →
    Es.getD l default
      = AnnotTerm.instAll Ds ((dJ.Fss i ψJ).getD j []).length (((dJ.Ess i ψJ).getD j []).getD l default)

end Shape

/-! ## The entry at a tuple, from the reading -/

/-- **The entry at a tuple whose target family reads the stored
reading**: from `EntryRead` at a field and the law "the target's family
at a fitting index tuple is the stored reading applied to the spine",
the container's domain read at the pin's frame IS the copy's slot at
that tuple (`interp_mkPisAV_piTele` over the copy's telescope, the
reading identity, the lift law and the index fit). -/
theorem copyEntryAt_of_read {TV : TargetView V} {dJ : BlockModel V} {ψJ : Name → Nat}
    {Ds : List AnnotTerm} {tg : Nat → Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eis : List (List AnnotTerm)} {ρp : Nat → V} {i j l : Nat}
    (hread : EntryRead TV dJ ψJ Ds tg tls Eis ρp i j l) {Z : Nat → V}
    (hZ : ∀ is : List V, SpineFit (TV.frame ρp (tg l)) (TV.Ids (tg l)) is →
      SetTheory.app (Z (tg l)) (tupW (TV.u (tg l)) is)
        = is.foldl SetTheory.app (interp V ρp (TV.EA (tg l)))) :
    CopyEntryAt dJ ψJ Ds tg tls Eis ρp i j TV.w TV.u Z l := by
  intro fs₁ hl₁ hsp
  rw [(hread.1 fs₁ hl₁)]
  unfold slotSet
  refine ConLeche.Semantics.interp_mkPisAV_piTele (v := TV.w) (acc := [])
    (fun d' hd' => hread.2.1 d' hd') fun bs hbs => ?_
  rw [List.nil_append, interp_mkAppN_foldl, hZ _ (hread.2.2 fs₁ bs hl₁ hsp hbs)]
  congr 1
  have hlen : l + (tls.getD l []).length = (fs₁ ++ bs).length := by
    rw [List.length_append, hl₁, hbs.length_eq, List.length_map]
  rw [← consList_append, hlen, interp_liftN_consList]

/-! ## The fits at one constructor -/

section Fit

variable {TV : TargetView V} {acval : Name → (Name → Nat) → AnnotTerm} {dJ : BlockModel V}
  {ψJ : Name → Nat} {Ds : List AnnotTerm} {base kJ : Nat} {Fs : List AnnotTerm} {rs : List Bool}
  {tg : Nat → Nat} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
  {Es : List AnnotTerm} {ρp : Nat → V} {i j : Nat}

-- The pin's frame and the container's least tuple there, at the
-- BLOCK's sort (`hw` identifies it with the container's).
local notation "ρJ" => consList (Ds.map (interp V ρp)) ρp

local notation "LJ" => lfpTuple TV.w dJ.k
  (dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp)) (dJ.Φ ψJ (consList (Ds.map (interp V ρp)) ρp))

/-- **`hfit` at one constructor, AT the container's carrier**: the copy's
fit at the joined tuple is the container's `ChainFit` at its least
tuple — from the shape and the entries at the least tuple, at a
container of the group's size whose sort is the block's and whose index
universes agree with the block's on `= 0`.  A container-recursive field
at a MEMBER target reads the group's copy of the target (`recF`,
`slotSet_instTele`); at one of the container's OWN pins the
container's slot at its carrier IS its real domain — its own `pinLeaf`
through `IsBlockModels.real_dom_eq`, the fact DESIGN §U.18 (e) called
`pinFix` — and the copy's entry at the outer tuple is that domain
(`hent`).  The container's fitting prefixes are carried
(`fitsFrom_iff_frames_spine`). -/
theorem CopyCtorShape.fit_iff_at {env : Env} {m : EnvModel V env}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hi : i < dJ.k) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = TV.w)
    (hu : ∀ i', i' < kJ → TV.u (base + i') = dJ.uM i' ψJ)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    {nI : Nat} (hnI : nI = (dJ.IdsM i ψJ).length)
    {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es)
    {L : Nat → V} (hent : CopyEntryOut dJ ψJ Ds tg tls Eis ρp i j base kJ Fs rs TV.w TV.u L)
    (t : V) (fs : List V) :
    (FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' []) (Eis.getD i' [])
        (segJoin base kJ L LJ (tg i'))) 0 ρp Fs fs ∧
      (∀ l, l < nI → interp V (consList fs ρp) (Es.getD l default) = projS l t))
    ↔ dJ.ChainFit ψJ ρJ LJ t i j fs := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hjl : j < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hlenF := hI.Fss_length hj ψJ
  have hks : (dJ.ksF i j).length = ((dJ.Fss i ψJ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hlenF]
  have hLJ : LJ = lfpTuple (dJ.w ψJ) dJ.k (dJ.idx ψJ ρJ) (dJ.Φ ψJ ρJ) := by rw [hw]
  -- the fits
  have hfits : FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' []) (Eis.getD i' [])
        (segJoin base kJ L LJ (tg i'))) 0 ρp Fs fs ↔
      FitsFrom ((dJ.rss i).getD j []) (dJ.slotAt ψJ LJ i j) 0 ρJ ((dJ.Fss i ψJ).getD j []) fs := by
    refine (fitsFrom_iff_frames_spine h.len.symm fun l hl fs₁ hl₁ hsp hf hf' => ?_).symm
    subst hl₁
    have hlt : fs₁.length < cA.2 := by rw [← hlenF]; exact hl
    simp only [Nat.zero_add]
    by_cases hr : ((dJ.rss i).getD j []).getD fs₁.length false = true
    · have hr' : (rsOf (dJ.ksF i j)).getD fs₁.length false = true := by
        rwa [IsBlockModel.rss_getD hjl] at hr
      have hreal := hreps.real_dom_eq hfT hPT hi hj hρJ hlt hr' hsp
      rw [hw] at hreal
      rw [if_pos hr]
      refine ⟨by rw [hreal]; exact Subset.refl _, ?_⟩
      rcases hI.tgt_cases hjl (hks ▸ hl) with htgt | ⟨hnt, -⟩
      · obtain ⟨hrC, htg, htl, hEis⟩ := h.recF _ hl hr htgt
        rw [if_pos hrC, htg, segJoin_add _ _ (hkJ ▸ htgt), dJ.slotAt_of_mem htgt, hEis, hw,
          hu _ (hkJ ▸ htgt)]
        exact (slotSet_instTele Iff.rfl Iff.rfl Ds ρp fs₁ htl _ _).symm
      · obtain ⟨hrC, hout, -, -, -, -, -⟩ := h.pinF _ hl hr hnt
        rw [if_pos hrC, segJoin_out _ _ hout, ← hent _ (h.len ▸ hl) hrC hout fs₁ rfl hsp, hreal]
    · have hr' : ((dJ.rss i).getD j []).getD fs₁.length false = false := by simpa using hr
      rw [if_neg (by rw [hr']; exact Bool.false_ne_true)]
      refine ⟨Subset.refl _, ?_⟩
      rcases h.ordF _ hl hr' with ⟨hrC, hF⟩ | ⟨hrC, hout, -, -⟩
      · rw [if_neg (by rw [hrC]; exact Bool.false_ne_true), hF fs₁ rfl, interp_instAll]
      · rw [if_pos hrC, segJoin_out _ _ hout]
        exact hent _ (h.len ▸ hl) hrC hout fs₁ rfl hsp
  -- the index equations
  refine Iff.trans (and_congr hfits (Iff.rfl)) ?_
  unfold BlockModel.ChainFit
  refine and_congr_right fun hf => ?_
  have hlen : fs.length = ((dJ.Fss i ψJ).getD j []).length := hf.length_eq
  rw [hnI]
  refine forall_congr' fun l => imp_congr_right fun hl => ?_
  rw [h.es l hl, ← hlen, interp_instAll]

/-- **`hfit` at one constructor, BELOW the container's carrier, one
direction**: a spine fitting the container's constructor at a tuple
`Y` below its least tuple fits the copy's at the joined tuple — the
container's slots at `Y` are within its slots at the carrier
(`IsBlockModels.slotAt_mono`: `pinMono` at a pin target), which are the
real domains, which are the copy's entries. -/
theorem CopyCtorShape.fit_imp {env : Env} {m : EnvModel V env} {Y : Nat → V}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hi : i < dJ.k) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = TV.w)
    (hu : ∀ i', i' < kJ → TV.u (base + i') = dJ.uM i' ψJ)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    {nI : Nat} (hnI : nI = (dJ.IdsM i ψJ).length)
    (hYs : InTupleSpace TV.w dJ.k (dJ.idx ψJ ρJ) Y)
    (hY : TupleLe dJ.k (dJ.idx ψJ ρJ) Y LJ)
    {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es)
    {L : Nat → V} (hent : CopyEntryOut dJ ψJ Ds tg tls Eis ρp i j base kJ Fs rs TV.w TV.u L)
    (t : V) (fs : List V) (hC : dJ.ChainFit ψJ ρJ Y t i j fs) :
    FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' []) (Eis.getD i' [])
        (segJoin base kJ L Y (tg i'))) 0 ρp Fs fs ∧
    (∀ l, l < nI → interp V (consList fs ρp) (Es.getD l default) = projS l t) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hjl : j < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hlenF := hI.Fss_length hj ψJ
  have hks : (dJ.ksF i j).length = ((dJ.Fss i ψJ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hlenF]
  have hYs' : InTupleSpace (dJ.w ψJ) dJ.k (dJ.idx ψJ ρJ) Y := by rw [hw]; exact hYs
  have hY' : TupleLe dJ.k (dJ.idx ψJ ρJ) Y
      (lfpTuple (dJ.w ψJ) dJ.k (dJ.idx ψJ ρJ) (dJ.Φ ψJ ρJ)) := by rw [hw]; exact hY
  unfold BlockModel.ChainFit at hC
  obtain ⟨hfC, hiC⟩ := hC
  have hlen : fs.length = ((dJ.Fss i ψJ).getD j []).length := hfC.length_eq
  refine ⟨fitsFrom_imp_frames_spine h.len.symm (fun l hl fs₁ hl₁ hsp hf hf' => ?_) hfC, ?_⟩
  · subst hl₁
    have hlt : fs₁.length < cA.2 := by rw [← hlenF]; exact hl
    simp only [Nat.zero_add]
    by_cases hr : ((dJ.rss i).getD j []).getD fs₁.length false = true
    · have hr' : (rsOf (dJ.ksF i j)).getD fs₁.length false = true := by
        rwa [IsBlockModel.rss_getD hjl] at hr
      have hreal := hreps.real_dom_eq hfT hPT hi hj hρJ hlt hr' hsp
      have hmono := hreps.slotAt_mono hfT hPT hi hj hρJ hlt hr' hsp hYs' hY'
      rw [hw] at hreal hmono
      rw [if_pos hr]
      refine ⟨by rw [hreal]; exact hmono, ?_⟩
      rcases hI.tgt_cases hjl (hks ▸ hl) with htgt | ⟨hnt, -⟩
      · obtain ⟨hrC, htg, htl, hEis⟩ := h.recF _ hl hr htgt
        rw [if_pos hrC, htg, segJoin_add _ _ (hkJ ▸ htgt), dJ.slotAt_of_mem htgt, hEis, hw,
          hu _ (hkJ ▸ htgt), slotSet_instTele Iff.rfl Iff.rfl Ds ρp fs₁ htl _ _]
        exact Subset.refl _
      · obtain ⟨hrC, hout, -, -, -, -, -⟩ := h.pinF _ hl hr hnt
        rw [if_pos hrC, segJoin_out _ _ hout, ← hent _ (h.len ▸ hl) hrC hout fs₁ rfl hsp, hreal]
        exact hmono
    · have hr' : ((dJ.rss i).getD j []).getD fs₁.length false = false := by simpa using hr
      rw [if_neg (by rw [hr']; exact Bool.false_ne_true)]
      refine ⟨Subset.refl _, ?_⟩
      rcases h.ordF _ hl hr' with ⟨hrC, hF⟩ | ⟨hrC, hout, -, -⟩
      · rw [if_neg (by rw [hrC]; exact Bool.false_ne_true), hF fs₁ rfl, interp_instAll]
        exact Subset.refl _
      · rw [if_pos hrC, segJoin_out _ _ hout, hent _ (h.len ▸ hl) hrC hout fs₁ rfl hsp]
        exact Subset.refl _
  · intro l hl
    rw [hnI] at hl
    rw [h.es l hl, ← hlen, interp_instAll]
    exact hiC l hl

end Fit


/-! ## The shape reads its carrier at the targets only -/

/-- **The shape at another carrier**: the stored readings enter the
shape only at the targets below `k + n` (`EntryRead`, `PinCorr`) and at
the container's own pins' containers (`PinCorr`); a view with the same
data and agreeing readings there, at a carrier agreeing at the
container's pins, carries the shape. -/
theorem CopyCtorShape.of_EA {TV : TargetView V} {acval acval' : Name → (Name → Nat) → AnnotTerm}
    {dJ : BlockModel V} {ψJ : Name → Nat} {Ds : List AnnotTerm} {lpsJ : List Name}
    {lvlsJ : List Level} {tg : Nat → Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {ρp : Nat → V}
    {i j base kJ : Nat} {Fs : List AnnotTerm} {rs : List Bool} {Es : List AnnotTerm}
    (EA' : Nat → AnnotTerm) (hEA : ∀ t, t < TV.k + TV.n → EA' t = TV.EA t)
    (hac : ∀ qK, qK < dJ.nPins →
      acval' (dJ.pinAt qK).J ((dJ.pinAt qK).ψJ ψJ) = acval (dJ.pinAt qK).J ((dJ.pinAt qK).ψJ ψJ))
    (htgt : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length → ¬ dJ.tgts i j l < dJ.k →
      dJ.tgts i j l - dJ.k < dJ.nPins)
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es) :
    CopyCtorShape { TV with EA := EA' } acval' dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs
      Es where
  len := h.len
  recF := h.recF
  ordF := fun l hl hr => by
    rcases h.ordF l hl hr with hL | ⟨h1, h2, h3, hr1, hr2, hr3⟩
    · exact Or.inl hL
    · refine Or.inr ⟨h1, h2, h3, fun fs₁ hl₁ => ?_, hr2, hr3⟩
      rw [hr1 fs₁ hl₁]
      show _ = interp V _ (mkPisAV _ (AnnotTerm.mkAppN ((EA' (tg l)).liftN _ 0) _))
      rw [hEA _ h3]
  pinF := fun l hl hr hnt => by
    obtain ⟨h1, h2, h3, h4, ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩, h5, h6⟩ := h.pinF l hl hr hnt
    refine ⟨h1, h2, h3, h4, ⟨?_, hp2, hp3, hp4, hp5, hp6⟩, h5, h6⟩
    show EA' (tg l) = _
    rw [hEA _ h4, hp1, hac _ (htgt l hl hnt)]
  es := h.es

/-- **A field's pin target is a pin of the container** (`IsBlockModel.tgtsLt`
at the field). -/
theorem IsBlockModels.tgt_pin_lt {env : Env} {m : EnvModel V env} {dJ : BlockModel V}
    (hreps : IsBlockModels m dJ) {ψJ : Name → Nat} {i j : Nat} (hi : i < dJ.k)
    {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA) :
    ∀ l, l < ((dJ.Fss i ψJ).getD j []).length → ¬ dJ.tgts i j l < dJ.k →
      dJ.tgts i j l - dJ.k < dJ.nPins := by
  intro l hl hnt
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hks : (dJ.ksF i j).length = ((dJ.Fss i ψJ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hI.Fss_length hj]
  rcases hI.tgt_cases (List.getElem?_eq_some_iff.mp hj).1 (hks ▸ hl) with h | ⟨-, h⟩
  · exact absurd h hnt
  · exact h

/-- **The stored readings at two carriers agreeing on the members and
the pins' containers** agree at every target. -/
theorem targetRead_congr {acval acval' : Name → (Name → Nat) → AnnotTerm}
    {memberNames : List Name} {pins : List PinSyn} {nP k : Nat} {ψ : Name → Nat}
    (hmem : ∀ t, t < k → acval' (memberNames.getD t .anonymous) ψ = acval (memberNames.getD t .anonymous) ψ)
    (hpin : ∀ q, q < pins.length →
      acval' (pins.getD q default).J ((pins.getD q default).ψJ ψ)
        = acval (pins.getD q default).J ((pins.getD q default).ψJ ψ)) :
    ∀ t, t < k + pins.length →
      targetRead acval' memberNames pins nP k ψ t = targetRead acval memberNames pins nP k ψ t := by
  intro t ht
  by_cases hk : t < k
  · rw [targetRead_of_mem hk, targetRead_of_mem hk, hmem t hk]
  · rw [targetRead_of_pin hk, targetRead_of_pin hk, hpin (t - k) (by omega)]

/-! ## The auxiliary lists' instantiation -/

section Inst

variable {nP k : Nat} {resSort : Level} {isProp large : Bool} {env₀ : Env} {memberNames : List Name}
  {nIdxs : List Nat} {ppsA : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {W : (Name → Nat) → Nat} {ctorsM : Nat → List (ConstantVal × Nat)} {idxF : Nat → Nat → List Expr}
  {dsF : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → Nat → List (Option Nat)}
  {ksF : Nat → Nat → List RecFieldKind} {tgts : Nat → Nat → Nat → Nat}
  {fvsPF xFvsF : Nat → Nat → List Expr} {xrestF : Nat → Nat → Expr}
  {eissF : Nat → Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {pins : List PinSyn} {offs : Nat → Nat}
  {mems nFs : List Nat} {tgtsG : List (List Nat)} {rss : List (List Bool)}
  {tlss : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm)))}
  {Eiss₀ : (Name → Nat) → List (List (List AnnotTerm))}
  {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)}

local notation "D" => (BlockModel.ofNested (V := V) nP k resSort isProp large env₀ memberNames
  nIdxs ppsA W ctorsM idxF dsF esF srcsF ksF tgts fvsPF xFvsF xrestF eissF tssF pins offs mems nFs
  tgtsG rss tlss Eiss₀ Fss₀ Ess₀)

local notation "ΨA" => nestedΨ (V := V) nP k resSort ppsA W pins offs mems nFs tgtsG rss tlss
  Eiss₀ Fss₀ Ess₀

variable {ψ : Name → Nat} {ρp : Nat → V}

-- The auxiliary least tuple at the frame (the members' carriers and
-- the pins' carriers at once), spelled without the block model so that
-- the identities below mention only the lists (`(D).w ψ`, `(D).idx ψ ρp`
-- are these by `rfl`).
local notation "L⁺" => lfpTuple (resSort.eval ψ) (k + pins.length) (nestedIs nP k ppsA W pins ψ ρp)
  (ΨA ψ ρp)

/-- **The targets' view at the auxiliary lists**: the block's `k`
members and the elimination's pins, the block's sort, the per-component
index universes (`nestedU`), the `k + n` telescopes, the pins' components
and the stored readings at a carrier `acval`. -/
@[expose] def nestedTV (nP k : Nat) (resSort : Level)
    (ppsA : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (pins : List PinSyn) (acval : Name → (Name → Nat) → AnnotTerm) (memberNames : List Name)
    (ψ : Name → Nat) : TargetView V where
  k := k
  n := pins.length
  w := resSort.eval ψ
  u := nestedU k W pins ψ
  Ids := fun t => if t < k then blockIds nP ppsA ψ t else (pins.getD (t - k) default).Ids ψ
  Ds := fun t => (pins.getD (t - k) default).Ds ψ
  EA := targetRead acval memberNames pins nP k ψ
  J := fun t => if t < k then memberNames.getD t .anonymous else (pins.getD (t - k) default).J
  lvls := fun t => (pins.getD (t - k) default).lvls

variable (acval : Name → (Name → Nat) → AnnotTerm)

local notation "TVA" => nestedTV (V := V) nP k resSort ppsA W pins acval memberNames ψ

/-- **`CopyCtorShape` at the auxiliary lists**, at the copy
`offs (k + q₀ + i) + j` of the container `dJ`'s member `i`, constructor
`j`, of the pin group `[q₀, q₀ + kJ)`. -/
@[expose] def CopyShapeA (dJ : BlockModel V) (ψJ : Name → Nat) (Ds : List AnnotTerm)
    (lpsJ : List Name) (lvlsJ : List Level) (q₀ kJ i j : Nat) : Prop :=
  CopyCtorShape (TVA) acval dJ ψJ Ds lpsJ lvlsJ
    (fun l => (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0)
    ((tlss ψ).getD (offs (k + q₀ + i) + j) []) ((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []) ρp i j
    (k + q₀) kJ ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []) (rss.getD (offs (k + q₀ + i) + j) [])
    ((Ess₀ ψ).getD (offs (k + q₀ + i) + j) [])

/-- **The entries at the auxiliary carrier**, at the copy
`offs (k + q₀ + i) + j` — the residual `nestedPinLeaf_all` discharges
(task #315 L-E). -/
@[expose] def CopyEntryA (dJ : BlockModel V) (ψJ : Name → Nat) (Ds : List AnnotTerm)
    (q₀ kJ i j : Nat) : Prop :=
  CopyEntryOut dJ ψJ Ds (fun l => (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0)
    ((tlss ψ).getD (offs (k + q₀ + i) + j) []) ((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []) ρp i j
    (k + q₀) kJ ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []) (rss.getD (offs (k + q₀ + i) + j) [])
    (resSort.eval ψ) (nestedU k W pins ψ) L⁺


/-- **`CopyShapeA` at another carrier** agreeing on the block's members,
the block's pins' containers and the container's own pins' containers. -/
theorem CopyShapeA.of_acval {acval' : Name → (Name → Nat) → AnnotTerm} {dJ : BlockModel V}
    {ψJ : Name → Nat} {Ds : List AnnotTerm} {lpsJ : List Name} {lvlsJ : List Level} {q₀ kJ i j : Nat}
    (hmem : ∀ t, t < k → acval' (memberNames.getD t .anonymous) ψ = acval (memberNames.getD t .anonymous) ψ)
    (hpin : ∀ q, q < pins.length →
      acval' (pins.getD q default).J ((pins.getD q default).ψJ ψ)
        = acval (pins.getD q default).J ((pins.getD q default).ψJ ψ))
    (hac : ∀ qK, qK < dJ.nPins →
      acval' (dJ.pinAt qK).J ((dJ.pinAt qK).ψJ ψJ) = acval (dJ.pinAt qK).J ((dJ.pinAt qK).ψJ ψJ))
    (htgt : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length → ¬ dJ.tgts i j l < dJ.k →
      dJ.tgts i j l - dJ.k < dJ.nPins)
    (h : CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
      acval dJ ψJ Ds lpsJ lvlsJ q₀ kJ i j) :
    CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
      acval' dJ ψJ Ds lpsJ lvlsJ q₀ kJ i j :=
  CopyCtorShape.of_EA (TV := TVA) (targetRead acval' memberNames pins nP k ψ)
    (targetRead_congr hmem hpin) hac htgt h

section Container

variable {dJ : BlockModel V} {ψJ : Name → Nat} {Ds : List AnnotTerm} {lpsJ : List Name}
  {lvlsJ : List Level}

-- The pin's frame and the container's least tuple there, at the
-- BLOCK's sort (`hw` identifies it with the container's).
local notation "ρJ" => consList (Ds.map (interp V ρp)) ρp

local notation "LJ" => lfpTuple (resSort.eval ψ) dJ.k
  (dJ.idx ψJ (consList (Ds.map (interp V ρp)) ρp)) (dJ.Φ ψJ (consList (Ds.map (interp V ρp)) ρp))

/-- **`hfitAt` verbatim** (`ofNested_pin_block_of_fit_at`'s hypothesis at
the carrier) from the shape and the entries at every constructor of the
group, with the grouping of the auxiliary block's constructor list (the
copy's constructors are the container member's, in order). -/
theorem hfit_at_of_inst {env : Env} {m : EnvModel V env} {q₀ kJ : Nat}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = resSort.eval ψ)
    (hu : ∀ i', i' < kJ → nestedU k W pins ψ (k + q₀ + i') = dJ.uM i' ψJ)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    (hidx : ∀ i, i < kJ → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < kJ → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hsh : ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        acval dJ ψJ Ds lpsJ lvlsJ q₀ kJ i j)
    (hent : ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyEntryA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        dJ ψJ Ds q₀ kJ i j) :
    ∀ i, i < kJ → ∀ t, t ∈ˢ dJ.idx ψJ ρJ i → ∀ j fs,
      (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
        mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i ∧
        FitsFrom (rss.getD (offs (k + q₀ + i) + j) []) (fun i' ρ => slotSet (resSort.eval ψ)
            (nestedU k W pins ψ ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD i' 0)) ρ
            (((tlss ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
            (((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
            (segJoin (k + q₀) kJ L⁺ LJ ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD i' 0)))
          0 ρp ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []) fs ∧
        (∀ l, l < (blockIds nP ppsA ψ (k + q₀ + i)).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (k + q₀ + i) + j) []).getD l default)
            = projS l t))
      ↔ (j < (dJ.ctorsM i).length ∧ dJ.ChainFit ψJ ρJ LJ t i j fs) := by
  subst hkJ
  intro i hi t _ j fs
  by_cases hj : j < (dJ.ctorsM i).length
  · have hj' : (dJ.ctorsM i)[j]? = some ((dJ.ctorsM i).getD j default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have hnI : (blockIds nP ppsA ψ (k + q₀ + i)).length = (dJ.IdsM i ψJ).length := by
      rw [hidx i hi, instTele_length]
    have hfit := CopyCtorShape.fit_iff_at (TV := TVA) hreps hfT hPT hi rfl hw
      (fun i' hi' => hu i' hi') hρJ hnI hj' (hsh i hi j hj) (hent i hi j hj) t fs
    obtain ⟨h1, h2⟩ := (hgrp i hi j).mpr hj
    constructor
    · rintro ⟨-, -, h3, h4⟩
      exact ⟨hj, hfit.mp ⟨h3, h4⟩⟩
    · rintro ⟨-, hC⟩
      obtain ⟨h3, h4⟩ := hfit.mpr hC
      exact ⟨h1, h2, h3, h4⟩
  · constructor
    · rintro ⟨h1, h2, -, -⟩
      exact absurd ((hgrp i hi j).mp ⟨h1, h2⟩) hj
    · rintro ⟨h', -⟩
      exact absurd h' hj

/-- **`hfitLe` verbatim** (`ofNested_pin_block_of_fit_at`'s hypothesis
below the carrier) from the shape and the entries at every constructor
of the group. -/
theorem hfit_le_of_inst {env : Env} {m : EnvModel V env} {q₀ kJ : Nat}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = resSort.eval ψ)
    (hu : ∀ i', i' < kJ → nestedU k W pins ψ (k + q₀ + i') = dJ.uM i' ψJ)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    (hidx : ∀ i, i < kJ → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < kJ → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hsh : ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        acval dJ ψJ Ds lpsJ lvlsJ q₀ kJ i j)
    (hent : ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyEntryA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        dJ ψJ Ds q₀ kJ i j) :
    ∀ Y, InTupleSpace (resSort.eval ψ) kJ (dJ.idx ψJ ρJ) Y → TupleLe kJ (dJ.idx ψJ ρJ) Y LJ →
      ∀ i, i < kJ → ∀ t, t ∈ˢ dJ.idx ψJ ρJ i → ∀ j fs, j < (dJ.ctorsM i).length →
      dJ.ChainFit ψJ ρJ Y t i j fs →
      (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
        mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i ∧
        FitsFrom (rss.getD (offs (k + q₀ + i) + j) []) (fun i' ρ => slotSet (resSort.eval ψ)
            (nestedU k W pins ψ ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD i' 0)) ρ
            (((tlss ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
            (((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) []).getD i' [])
            (segJoin (k + q₀) kJ L⁺ Y ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD i' 0)))
          0 ρp ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) []) fs ∧
        (∀ l, l < (blockIds nP ppsA ψ (k + q₀ + i)).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (k + q₀ + i) + j) []).getD l default)
            = projS l t)) := by
  subst hkJ
  intro Y hY hYle i hi t _ j fs hj hC
  have hj' : (dJ.ctorsM i)[j]? = some ((dJ.ctorsM i).getD j default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
  have hnI : (blockIds nP ppsA ψ (k + q₀ + i)).length = (dJ.IdsM i ψJ).length := by
    rw [hidx i hi, instTele_length]
  obtain ⟨h1, h2⟩ := (hgrp i hi j).mpr hj
  obtain ⟨h3, h4⟩ := CopyCtorShape.fit_imp (TV := TVA) hreps hfT hPT hi rfl hw
    (fun i' hi' => hu i' hi') hρJ hnI hY hYle hj' (hsh i hi j hj) (hent i hi j hj) t fs hC
  exact ⟨h1, h2, h3, h4⟩

/-- **A pin's carrier at the block's carrier is its container's least
tuple**, from the shape and the entries — at a container with pins of
its own as well (task #315 L-C; `ofNested_pin_block_of_fit_at` at the
container's block model: the fibre by its `fibre` clause, the tag shape
`EnvBlockModels`', the fits by `hfit_at_of_inst`/`hfit_le_of_inst`,
which read the container's own pins through `real_dom_eq`/`slotAt_mono`
— its `pinLeaf` and `pinMono` — hence the typing `hfT`/`hPT`). -/
theorem ofNested_pin_block_of_inst {env : Env} {m : EnvModel V env} {q₀ kJ : Nat}
    (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ ρp)
    (hS : TupleLfpShape (k + pins.length) (blockIds nP ppsA ψ) mems nFs tgtsG rss (Eiss₀ ψ) (Fss₀ ψ)
      (Ess₀ ψ))
    (hseg : q₀ + kJ ≤ pins.length)
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = resSort.eval ψ)
    (hu : ∀ i', i' < kJ → nestedU k W pins ψ (k + q₀ + i') = dJ.uM i' ψJ)
    (hinj : ∀ (mm' j : Nat) (fs : List V), dJ.inj ψJ mm' j fs = injW (dJ.w ψJ) j (mkTower (fs ++ [pt])))
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    (hidx : ∀ i, i < kJ → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < kJ → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hsh : ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        acval dJ ψJ Ds lpsJ lvlsJ q₀ kJ i j)
    (hent : ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyEntryA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        dJ ψJ Ds q₀ kJ i j)
    {i : Nat} (hi : i < kJ) :
    (D).pinCar ψ ρp (lfpTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp)) (q₀ + i)
      = lfpTuple (dJ.w ψJ) dJ.k (dJ.idx ψJ ρJ) (dJ.Φ ψJ ρJ) i := by
  have hkJ' : kJ = dJ.k := hkJ.symm
  subst hkJ'
  have hw' : (D).w ψ = dJ.w ψJ := hw.symm
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hF := hI.functor ψJ _ hρJ
  refine (ofNested_pin_block_of_fit_at h hS hseg (IsJ := dJ.idx ψJ ρJ) (ΦJ := dJ.Φ ψJ ρJ)
    ?_ ?_ ?_ ?_ (injJ := dJ.inj ψJ) ?_ (nCJ := fun i => (dJ.ctorsM i).length)
    (FitJ := fun Y t i j fs => dJ.ChainFit ψJ ρJ Y t i j fs) ?_ ?_ ?_ hi).trans (by rw [hw'])
  · -- MonoTuple
    rw [hw']; exact hF.1
  · -- MapsTuple
    rw [hw']; exact hF.2.1
  · -- a closed tuple
    rw [hw']; exact hF.2.2
  · -- hIs
    intro i' hi'
    show idxSet (nestedU k W pins ψ (k + q₀ + i')) ρp (blockIds nP ppsA ψ (k + q₀ + i')) = _
    rw [hidx i' hi', hu i' hi']
    exact idxSet_instTele Iff.rfl Ds ρp _
  · -- hinj
    intro i' j fs
    rw [hinj, hw']
  · -- hfibJ
    intro Y hY i' hi' t ht x
    obtain ⟨cvT', cvR', mI', rP', rules', hI'⟩ := hreps i' hi'
    rw [hw'] at hY
    exact hI'.fibre ψJ _ hρJ Y hY i' hi' t ht x
  · -- hfitAt
    intro i' hi' t ht j fs
    exact hfit_at_of_inst acval hreps hfT hPT rfl hw hu hρJ hidx hgrp hsh hent i' hi' t ht j fs
  · -- hfitLe
    intro Y hY hYle i' hi' t ht j fs hj hC
    exact hfit_le_of_inst acval hreps hfT hPT rfl hw hu hρJ hidx hgrp hsh hent Y hY hYle i' hi' t
      ht j fs hj hC

/-- **`pinLeaf` for `ofNested` at a pin group** — at a container with
pins of its own as well (task #315 L-C discharged the pin-free
restriction `hnp : dJ.pins = []`): the container at the pin's
components and fitting indices is the pin's carrier at the block's
carrier — the container's `leaf` at the pin's frame through
`ofNested_pin_block_of_inst`.  The pin's record is the container's
(`hpJ`/`hpψ`/`hpDs`/`hpu`/`hpIds`); the components fit the container's
parameter telescope at the block's frame (`hDsFit`, the post-check
`nestedPinsOk` read through `PinsTyped`); the container's members,
constructors and pins are typed (`hfT`/`hPT`, `ContainerModeled`'s);
the shape is the group's (`hsh`, lane L-B) and the entries the whole
block's (`hent`, `nestedPinLeaf_all`). -/
theorem ofNested_pinLeaf_of {env : Env} {m : EnvModel V env}
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {i : Nat}
    (hI : IsBlockModel m T cvT cvR mI rP rules dJ i)
    {q₀ kJ : Nat} {ρ : Nat → V} {as is : List V}
    (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ (consList as ρ))
    (hS : TupleLfpShape (k + pins.length) (blockIds nP ppsA ψ) mems nFs tgtsG rss (Eiss₀ ψ) (Fss₀ ψ)
      (Ess₀ ψ))
    (hseg : q₀ + kJ ≤ pins.length) (hi : i < kJ)
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = resSort.eval ψ)
    (hu : ∀ i', i' < kJ → nestedU k W pins ψ (k + q₀ + i') = dJ.uM i' ψJ)
    (hinj : ∀ (mm' j : Nat) (fs : List V), dJ.inj ψJ mm' j fs = injW (dJ.w ψJ) j (mkTower (fs ++ [pt])))
    (hidx : ∀ i, i < kJ → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < kJ → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hsh : ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := consList as ρ)
        acval dJ ψJ Ds lpsJ lvlsJ q₀ kJ i j)
    (hent : ∀ i, i < kJ → ∀ j, j < (dJ.ctorsM i).length →
      CopyEntryA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := consList as ρ)
        dJ ψJ Ds q₀ kJ i j)
    (hpJ : ((D).pinAt (q₀ + i)).J = T) (hpψ : ((D).pinAt (q₀ + i)).ψJ ψ = ψJ)
    (hpDs : ((D).pinAt (q₀ + i)).Ds ψ = Ds)
    (hpIds : ((D).pinAt (q₀ + i)).Ids ψ = dJ.IdsM i ψJ)
    (hDsFit : SpineFit (consList as ρ) (dJ.params ψJ) (Ds.map (interp V (consList as ρ))))
    (hisFit : SpineFit ((D).pinFrame (q₀ + i) ψ (consList as ρ)) (((D).pinAt (q₀ + i)).Ids ψ) is) :
    ((((D).pinAt (q₀ + i)).Ds ψ).map (interp V (consList as ρ)) ++ is).foldl SetTheory.app
        (interp V ρ (m.acval ((D).pinAt (q₀ + i)).J (((D).pinAt (q₀ + i)).ψJ ψ)))
      = SetTheory.app ((D).pinCar ψ (consList as ρ)
            (lfpTuple ((D).w ψ) k ((D).idx ψ (consList as ρ)) ((D).Φ ψ (consList as ρ))) (q₀ + i))
          (tupW (((D).pinAt (q₀ + i)).u ψ) is) := by
  unfold BlockModel.pinFrame at hisFit
  rw [hpDs, hpIds] at hisFit
  rw [hpDs, hpJ, hpψ, interp_closed (V := V) (m.cval_closedL T ψJ) ρ (consList as ρ),
    hI.leaf ψJ (consList as ρ) _ is hDsFit hisFit,
    ofNested_pin_block_of_inst acval h hS hseg hreps hfT hPT hkJ hw hu hinj (dJ.satOfSpine hDsFit)
      hidx hgrp hsh hent hi]
  unfold BlockModel.tup
  rw [← hu i hi, Nat.add_assoc, nestedU_pin]
  rfl

end Container

end Inst

end ConLeche.Model
