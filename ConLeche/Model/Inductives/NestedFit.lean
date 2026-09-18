module

public import ConLeche.Model.Inductives.BlockComposed
public import ConLeche.Model.Inductives.NestedRecCand
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

## THE FRAME-GENERIC FORMS, and the one sentence that explains them

`CopyEntryAtF`, `TargetView.frameAt`, `targetValAt` and `pinLfpAt` take
the pin's components — or the frame they induce — as an ARGUMENT rather
than reading them off the recorded pin.  The reason is one asymmetry,
and it is the central idea of this route rather than a technical
convenience:

> **The copy's SLOT reads at the block's own frame `ρp` and does not
> move.  The CONTAINER's side — its spine fit and the interpretation of
> its field domain — reads at the frame that varies.  That asymmetry is
> what a candidate frame IS.**

`CopyCtorShape` keeps the components `Ds` untouched throughout, because
the copy IS the container at `Ds` syntactically whatever frame one reads
it at; the frame and the shape are separable, and only the frame moves.

It is also, in one line, why the original impasse was an artefact:
stating the obligation at the TRUE frame forces both sides to move
together, and the circularity that appeared then was the cost of tying
them.

**THE EFFORT PROFILE IS THE DIAGNOSTIC — the same observation from the
other side.**  When a cut is real, the work at each site is THE SAME
WORK; when it is imposed, each site needs its own argument.  Five of
these frame-generalisations landed first or second try, which is what a
real cut feels like.  The three-way split by a domain's head needed a
different argument at each arm, and that asymmetry in EFFORT was the
signal — visible weeks before K.51 explained it.  And `fit_iff_at`
resisting a frame parameter is the same signal read the other way: the
work stopped being mechanical, and the reason was that the cut was in
the wrong place (the syntactic instantiation DETERMINES the semantic
frame, so a frame parameter has nowhere to go there).

Together with the rule above this is a method, not two anecdotes: read
the position rather than the head, and watch whether the work stays the
same work.

**AND THE FOURTH SHAPE, which explains the other three: A SEARCH FINDS
OCCURRENCES; WHAT BREAKS AN EDIT IS A PROPERTY.**  A hypothesis's shape
travelling into a callee has no textual footprint at all.  Abstracting
`pinLfp` out of the pin-pair chain looked free because the name occurred
once; it was not, because `nestedTargetReads_L`'s proof needs that family
to BE a container's least tuple — it feeds `pinTarget_reads`.  The edit
closed only once the PROPERTY was supplied as a premise (`hPfGroup`,
proved for `pinLfp` by `pinLfp_group`).  **A claim about a dependency
needs the elaborator, not a search, and the cheap falsifier is to make
the edit and build.**

**CHEAP REVERTS, NOT MERELY CHEAP FALSIFIERS.**  That edit succeeded on
the third attempt, and only because the two reverted ones had mapped its
seven sites and shown which were special.  **A failed attempt that leaves
knowledge behind is a measurement**; reverting WHOLESALE is what keeps
attempting cheap enough to do repeatedly, and what stops a half-done
chain from being indistinguishable from an intended one.

**GREP BEFORE FUNDING — the first step of costing any piece of work on
this route, not a heuristic.**  Five times a deadlock on this route was
broken by something the tree already proved: K.51 for the head split,
`tupleLfpAV_fold`'s index-genericity for the copies' readings, §U.61 for
head-reading, `nestedPinsFixed` for the section agreement, and
`CopyCtorShape.fit_imp_T_le_dom` for the family-generic fit.  Cost a
piece of work by first naming what would discharge it and grepping for
that name.

**AND A HIGHER-ORDER TRAP, WITH ITS REMEDY AS A DEFAULT.**  When one of
these generalisations abstracts an INDEX-INDEXED family — `Af : Nat →
List V` replacing a term like `((d.pinAt (q₀ + i)).Ds ψ).map (interp V
ρp)` inside a hypothesis — leaving `Af` implicit makes unification invert
the index expression `q₀ + i` to solve it.  That surfaces not as a type
error but as a **`(deterministic) timeout at whnf, maximum number of
heartbeats (200000)`**, which the error text gives no way to diagnose.
**Pass such a family EXPLICITLY at call sites from the start**
(`(Af := fun q => …)`); doing so removed the timeout outright when this
lane hit it.

**A mechanical trap that recurs at every one of these generalisations.**
When the generic form stops mentioning an object the specific one
mentions (`CopyEntryAtF` does not mention `Ds`), their auto-bound
section variables differ and the two signatures do NOT line up
positionally — so defining the specific one as an application of the
generic one fails with an argument-order mismatch.  State the bridge as
a separate `Iff.rfl`/`rfl` theorem with explicit named arguments
instead (`copyEntryAt_iff_F`).
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

/-- **`FitsFrom` implication across two frames THROUGH a third chain**
(task #315 L-E, DESIGN §U.64): the container instance transfer compares
the ROOT's copy of a constructor with the BLOCK's copy of it, and the
two copies' entry sets are related not to each other directly but each
to the CONTAINER's own field domains — the chain `G`, read at a frame
`ρV`, which both `CopyCtorShape`s describe (`ctor_params` makes it ONE
list).  So the per-field obligation is a pair of inclusions: the first
copy's entry sits inside the container's real domain — which is what
carries the container's fitting prefix along the recursion, and what
the entries and the slot laws are stated at — and inside the second
copy's entry.

This is the shape `fitsFrom_imp_frames_spine` cannot take: there the
carried spine is the FIRST chain's own, so a copy-to-copy transfer
would need the copy's slots inside the COPY's domains, a fact about the
auxiliary block rather than about the container. -/
theorem fitsFrom_imp_frames_via {rs₁ rs₂ : List Bool} {slot₁ slot₂ : Nat → (Nat → V) → V} :
    ∀ (G : List AnnotTerm) {i : Nat} {ρ₁ ρ₂ ρV : Nat → V} {Fs₁ Fs₂ : List AnnotTerm}
      {fs : List V},
      Fs₁.length = G.length → Fs₂.length = G.length →
      (∀ l, l < G.length → ∀ fs₁ : List V, fs₁.length = l →
        SpineFit ρV (G.take l) fs₁ →
        (if rs₁.getD (i + l) false then slot₁ (i + l) (consList fs₁ ρ₁)
            else interp V (consList fs₁ ρ₁) (Fs₁.getD l default))
          ⊆ˢ interp V (consList fs₁ ρV) (G.getD l default) ∧
        (if rs₁.getD (i + l) false then slot₁ (i + l) (consList fs₁ ρ₁)
            else interp V (consList fs₁ ρ₁) (Fs₁.getD l default))
          ⊆ˢ (if rs₂.getD (i + l) false then slot₂ (i + l) (consList fs₁ ρ₂)
            else interp V (consList fs₁ ρ₂) (Fs₂.getD l default))) →
      FitsFrom rs₁ slot₁ i ρ₁ Fs₁ fs → FitsFrom rs₂ slot₂ i ρ₂ Fs₂ fs := by
  intro G
  induction G with
  | nil =>
    intro i ρ₁ ρ₂ ρV Fs₁ Fs₂ fs h1 h2 _ h
    cases Fs₂ with
    | cons F₂ Fs₂ => simp at h2
    | nil =>
      cases Fs₁ with
      | cons F₁ Fs₁ => simp at h1
      | nil =>
        cases fs with
        | nil => trivial
        | cons a fs => exact h.elim
  | cons Gh G ih =>
    intro i ρ₁ ρ₂ ρV Fs₁ Fs₂ fs h1 h2 hent h
    cases Fs₁ with
    | nil => simp at h1
    | cons F₁ Fs₁ =>
      cases Fs₂ with
      | nil => simp at h2
      | cons F₂ Fs₂ =>
        cases fs with
        | nil => exact h.elim
        | cons a fs =>
          obtain ⟨ha, hf⟩ : a ∈ˢ (if rs₁.getD i false then slot₁ i ρ₁ else interp V ρ₁ F₁) ∧
              FitsFrom rs₁ slot₁ (i + 1) (cons a ρ₁) Fs₁ fs := h
          have h0 := hent 0 (by simp) [] rfl trivial
          simp only [Nat.add_zero, consList_nil, List.getD_cons_zero] at h0
          refine ⟨h0.2 a ha, ?_⟩
          refine ih (i := i + 1) (ρ₁ := cons a ρ₁) (ρ₂ := cons a ρ₂) (ρV := cons a ρV)
            (by simpa using h1) (by simpa using h2) (fun l hl fs₁ hl₁ hsp => ?_) hf
          have := hent (l + 1) (by simp; omega) (a :: fs₁) (by simp [hl₁])
            (by
              show a ∈ˢ interp V ρV Gh ∧ SpineFit (cons a ρV) (G.take l) fs₁
              exact ⟨h0.1 a ha, hsp⟩)
          simpa only [consList_cons, List.getD_cons_succ,
            show i + (l + 1) = i + 1 + l from by omega] using this

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
containers already stored (`PinShapes`).

**THE RULE OF THIS ROUTE, and it has cost four refutations to learn:
NEVER READ A TARGET'S IDENTITY, OR A FIELD'S CLASSIFICATION, OFF A
COMPONENT'S OR A DOMAIN'S HEAD.  READ IT OFF THE RECORDED POSITION.**
A component can be a λ that the positivity `whnf` reduces, so its head
is not the container's; a field domain can be a parameter APPLIED, so
its head is not the target's; the auxiliary domain can be a copy
applied, so it is not the copy constant; and a copy has no NAME in the
output environment while having a perfectly good READING.  The four
witnesses, in the order they were paid for:

* §U.61 — the target's container taken from the component's head,
  refuted by lane L-B at `tests/e2e/nested_lam_pin_prop.ndjson`
  (component `fun _ : True => T`), which is why `DsE` below is read by
  nothing and `PinCorr`/`targetPin_corr` read the POSITION instead;
* the restated ordinary-field case split three ways by the container
  domain's head, collapsed by K.51 (`nestedPinRewrites`), which
  certifies that the normalised minted domain rewritten by
  `replaceAllNested` IS the stored one — over exactly the fields that
  carry an edge, with no head analysis anywhere;
* "the auxiliary domain is the copy constant", corrected at
  `tests/e2e/nested_p26.ndjson`, where it is the copy APPLIED; the
  head-free fact is "headed by an auxiliary member";
* "no term denotes a copy", corrected by `mutMemberLeaf` and
  `tupleLfpAV_fold`, which are index-generic: a copy has a reading, and
  only the NAME is missing.

Three fixtures carry a λ component and teach the first form of the rule:
`nested_lam_pin_prop`, `nested_p22`, `nested_p26`. -/
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
  /-- a pin target's components as EXPRESSIONS.  **Read by nothing in
  the shape** since DESIGN §U.61: §U.48 (i) had the target's container
  taken from the pin's component's head, and lane L-B refuted that at
  an accepted block (`tests/e2e/nested_lam_pin_prop.ndjson`, whose
  component is a λ-redex the positivity `whnf` reduces); a target's
  identity is now read off the target's POSITION in the pin table
  (`PinCorr`, `targetPin_corr`).  The field stays so that the views'
  data are the pin table's. -/
  DsE : Nat → List Expr
  /-- a target's stored reading at the block's parameter depth -/
  EA : Nat → AnnotTerm
  /-- a target's NAME: the member's, a pin's container's (task #315 L-E,
  step (iii): the correspondence of pins is structural) -/
  J : Nat → Name
  /-- a pin target's level arguments (read at PIN targets only: a
  member target has none, and both views give `[]` there — DESIGN
  §U.61, where reading pin `0`'s arguments at a member was a latent
  trap) -/
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

/-- **THE FRAME AT A GIVEN COMPONENT FAMILY** (task #315 L-E, the
collapse): `TargetView.frame` with a pin target's component VALUES
supplied instead of interpreted from the recorded components.

This is the candidate frame, and it is where the whole restatement
lives: at a member the frame does not move — the output model's value at
a member already IS the auxiliary leaf — and at a pin it is the
container's parameter frame at the candidate components. -/
@[expose] noncomputable def frameAt (TV : TargetView V) (cAs : Nat → List V)
    (ρp : Nat → V) (t : Nat) : Nat → V :=
  if t < TV.k then ρp else consList (cAs (t - TV.k)) ρp

omit [SetTheory V] in
theorem frameAt_of_mem (TV : TargetView V) (cAs : Nat → List V) (ρp : Nat → V) {t : Nat}
    (ht : t < TV.k) : TV.frameAt cAs ρp t = ρp := by
  simp only [frameAt, if_pos ht]

omit [SetTheory V] in
theorem frameAt_of_pin (TV : TargetView V) (cAs : Nat → List V) (ρp : Nat → V) {t : Nat}
    (ht : ¬ t < TV.k) : TV.frameAt cAs ρp t = consList (cAs (t - TV.k)) ρp := by
  simp only [frameAt, if_neg ht]

/-- **The recorded frame is the general one at the recorded components**
(task #315 L-E): conservativity again, so every consumer of
`TargetView.frame` specialises back. -/
theorem frameAt_recorded (TV : TargetView V) (ρp : Nat → V) (t : Nat) :
    TV.frameAt (fun q => (TV.Ds (TV.k + q)).map (interp V ρp)) ρp t = TV.frame ρp t := by
  by_cases ht : t < TV.k
  · rw [frameAt_of_mem _ _ _ ht, frame_of_mem _ _ ht]
  · rw [frameAt_of_pin _ _ _ ht, frame_of_pin _ _ ht]
    have h : TV.k + (t - TV.k) = t := by omega
    simp only [h]

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

/-- **THE TARGETS' READINGS AT A GIVEN COMPONENT FAMILY, AS VALUES**
(task #315 L-E, the COLLAPSE of the pin-target arms): `targetRead`'s
denotation with the pins' component VALUES supplied as an argument
instead of read off the recorded pin.

**Why this is the collapse and not another re-basing.**  The restated
ordinary-field case was splitting three ways by the head of the
CONTAINER's field domain — parameter-headed bare, parameter-headed
applied, constant-headed at an earlier container.  Each arm was
answering the same question, "what does this field's domain evaluate to
at the candidate frame", by RECOMPUTING it from the container's syntax,
and the recomputation is what branched.  The elimination has already
computed it: `nestedPinRewrites` (K.51,
`ConLeche/Kernel/Inductives/NestedInstall.lean`) certifies that the
normalised MINTED domain, rewritten by `replaceAllNested` at the final
state, IS the domain the auxiliary install stored — over exactly the
fields that carry an edge, and with no head analysis anywhere.  Stated
over that image the answer is read off, the head never appears, and the
target becomes an INDEX rather than a case.

**WHY VALUES AND NOT TERMS.**  The natural-looking generalisation takes
the components as ANNOTTERMS, and it cannot state the candidate frame at
all: a pin's candidate component has to denote the AUXILIARY CARRIER at
another pin, and the copies are minted into a scratch block that the
restore removes, so no term of the output environment denotes one.  The
container's former does have a constant — only its arguments move — so
the candidate reading is the former's value with the candidate component
VALUES folded onto it.  (This is the same shape as `pinLfpAt`, which
takes `as : List V` for the same reason, and it is G2's point about
carriers one level out: the thing being replaced is not a term.)

**IT BUYS THE ORDERING QUESTION NOTHING, and the next reader's first
instinct will be that it should.**  K.51 is a SYNTACTIC identity between
two terms whose interpretations differ by how the copy constants are
read: as the auxiliary carrier it gives the candidate frame, as the
containers' least tuples the true one.  So a certified syntactic chain
settles the collapse and says nothing whatever about which pin must be
settled before which — the candidate-to-true bridge still needs its own
well-founded induction, over a relation whose union with the
declaration order is cyclic on an accepted fixture. -/
@[expose] noncomputable def targetValAt (acval : Name → (Name → Nat) → AnnotTerm)
    (memberNames : List Name) (pins : List PinSyn) (cAs : Nat → List V)
    (nP k : Nat) (ψ : Name → Nat) (ρp : Nat → V) (t : Nat) : V :=
  if t < k then
    interp V ρp (AnnotTerm.mkAppN (acval (memberNames.getD t .anonymous) ψ) (paramBvarsAt nP nP))
  else
    (cAs (t - k)).foldl SetTheory.app
      (interp V ρp (acval (pins.getD (t - k) default).J ((pins.getD (t - k) default).ψJ ψ)))

/-- **The recorded components' VALUES, as a family** — what today's
`targetRead` supplies once interpreted. -/
@[expose] noncomputable def recordedAs (pins : List PinSyn) (ψ : Name → Nat) (ρp : Nat → V)
    (q : Nat) : List V :=
  ((pins.getD q default).Ds ψ).map (interp V ρp)

theorem targetValAt_of_mem {acval : Name → (Name → Nat) → AnnotTerm} {memberNames : List Name}
    {pins : List PinSyn} {cAs : Nat → List V} {nP k : Nat} {ψ : Name → Nat} {ρp : Nat → V}
    {t : Nat} (ht : t < k) :
    targetValAt (V := V) acval memberNames pins cAs nP k ψ ρp t
      = interp V ρp
          (AnnotTerm.mkAppN (acval (memberNames.getD t .anonymous) ψ) (paramBvarsAt nP nP)) := by
  simp only [targetValAt, if_pos ht]

theorem targetValAt_of_pin {acval : Name → (Name → Nat) → AnnotTerm} {memberNames : List Name}
    {pins : List PinSyn} {cAs : Nat → List V} {nP k : Nat} {ψ : Name → Nat} {ρp : Nat → V}
    {t : Nat} (ht : ¬ t < k) :
    targetValAt (V := V) acval memberNames pins cAs nP k ψ ρp t
      = (cAs (t - k)).foldl SetTheory.app
          (interp V ρp (acval (pins.getD (t - k) default).J
            ((pins.getD (t - k) default).ψJ ψ))) := by
  simp only [targetValAt, if_neg ht]

/-! ## The identities of one copy's constructor, entry-free -/

section Shape

variable (TV : TargetView V) (acval : Name → (Name → Nat) → AnnotTerm) (dJ : BlockModel V)
  (ψJ : Name → Nat) (Ds : List AnnotTerm) (DsE : List Expr) (lpsJ : List Name) (lvlsJ : List Level)

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
constructors' readings at the target).

These six clauses are exactly the TARGET's recorded pin data, which is
where a target's identity is read since DESIGN §U.61.  The seventh —
the components as `Expr`s — is gone: a stored container's record gives
its pins' components SEMANTICALLY (`BlockOpened.nestF` records the
head and the count), so the clause had no source, and nothing reads it
now that `targetPin_corr` replaces the refuted `targetHead_corr`. -/
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

/-- **The entry identity at a tuple `Z`**, at one field: at a prefix
fitting the container's real domains, the CONTAINER's domain read at
the pin's frame IS the copy's slot at `Z`, taken at the field's target
(`CopyEntry` of DESIGN §U.23, re-based on the container's prefix fit
and generic in the tuple, task #315 L-E). -/
@[expose] def CopyEntryAtF (fr : Nat → V) (w : Nat) (u : Nat → Nat) (Z : Nat → V) (l : Nat) :
    Prop :=
  ∀ fs₁ : List V, fs₁.length = l →
    SpineFit fr (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
    interp V (consList fs₁ fr) (((dJ.Fss i ψJ).getD j []).getD l default)
      = slotSet w (u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) (Z (tg l))

/-- **THE ENTRY IDENTITY, FRAME-GENERIC** (task #315 L-E, clause two of
the closure step).  `CopyEntryAt` is `CopyEntryAtF` at the RECORDED
frame, definitionally, so every consumer is untouched.

**The asymmetry is the whole point.**  The container's side — the
`SpineFit` and the `interp` of its field domain — is read at the frame
`fr`; the copy's SLOT is read at `ρp`, the block's own frame, and does
not move.  That is what a candidate frame IS: the same syntactic shape
(`CopyCtorShape` keeps `Ds` untouched, because the copy is the container
at `Ds` whatever frame one reads it at) evaluated on the container's
side at different component values.  Separating the two was the finding:
the frame and the shape are separable, and only the frame moves. -/
@[expose] def CopyEntryAt (w : Nat) (u : Nat → Nat) (Z : Nat → V) (l : Nat) : Prop :=
  ∀ fs₁ : List V, fs₁.length = l →
    SpineFit (consList (Ds.map (interp V ρp)) ρp) (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
    interp V (consList fs₁ (consList (Ds.map (interp V ρp)) ρp)) (((dJ.Fss i ψJ).getD j []).getD l default)
      = slotSet w (u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) (Z (tg l))

/-- **Today's entry identity IS the frame-generic one at the recorded
frame** (task #315 L-E).  `Iff.rfl`, so the re-basing is conservative
and no consumer moves. -/
theorem copyEntryAt_iff_F (w : Nat) (u : Nat → Nat) (Z : Nat → V) (l : Nat) :
    CopyEntryAt (V := V) dJ ψJ Ds tg tls Eis ρp i j w u Z l
      ↔ CopyEntryAtF (V := V) dJ ψJ tg tls Eis ρp i j
          (consList (Ds.map (interp V ρp)) ρp) w u Z l := Iff.rfl

/-- **The entry at the STORED READING** (task #315 L-E, DESIGN §U.36):
the shape of a container-ordinary field the elimination rewrote — the
copy's field is recursive at a target `tg l` outside the group — is
the ENTRY IDENTITY at every tuple whose family at the target reads as
the target's stored reading: the container's domain, read at the pin's
frame under a prefix fitting the container's real domains, IS the
copy's SLOT at that tuple.

**Stated as what its consumer produces** (task #315, lane L-B's
refutation of 2026-09-18, DESIGN "the telescope the positivity `whnf`
MAKES"): until that day the arm exhibited the container's domain as a
SYNTACTIC Π-tower `mkPisAV tlsJ body` whose telescope the copy's was
an `instTele` of, and BOTH clauses are FALSE at a block this checker
ACCEPTS (`tests/e2e/nested_lam_pin_refl.ndjson`).  The witness: a
container whose field is an application of a function PARAMETER,
nested at an instantiation whose body is an arrow.  The elimination's
rewrite is the identity on the minted redex, the positivity
normalisation beta-reduces it to that arrow, and the copy's field is
therefore REFLEXIVE with a one-entry telescope where the container's
own field is ORDINARY and an APPLICATION.  The telescope clause forces
`tlsJ.length = 1` (`instTele_length`), and the first clause then asks
an application to equal a `.pi`-headed term: no witness exists.

What was wrong is the SHAPE, not the route — the slot is a Π-set over
a telescope the COPY really has, and only the demand that the
CONTAINER exhibit the same telescope SYNTACTICALLY was false.  So the
predicate now quantifies over the tuple and asks for the identity
directly, and the arm's obligation is the ONE reading identity it can
prove.  Nothing syntactic survives on the container's side: whether a
copy telescope is always an `instTele` of a container-side one is NOT
established — lane L-B could not establish it, and this lane does not
assume it.

Since DESIGN §U.61 the arm carries the reading and NOTHING about the
target's head: the `TargetHead` conjunct — the target's container read
off the container's own field — is refuted at an accepted block (lane
L-B; `tests/e2e/nested_lam_pin_prop.ndjson`), and an `ordF`-right
field's target has no recorded pin on the CONTAINER's side to be keyed
to, so the arm relates the two sides' targets no longer.  Each side's
entry is its own reading law, which is all the transfer's fit needs;
what the WALK loses is the correspondence at such a field (DESIGN
§U.61 (c)). -/
@[expose] def EntryRead (l : Nat) : Prop :=
  ∀ Z : Nat → V,
    (∀ is : List V, SpineFit (TV.frame ρp (tg l)) (TV.Ids (tg l)) is →
      SetTheory.app (Z (tg l)) (tupW (TV.u (tg l)) is)
        = is.foldl SetTheory.app (interp V ρp (TV.EA (tg l)))) →
    CopyEntryAt dJ ψJ Ds tg tls Eis ρp i j TV.w TV.u Z l

/-- **THE READING LAW, FRAME-GENERIC** (task #315 L-E, clause two).
Three things move together, and they are exactly the three places a
frame appears in `EntryRead`:

* `cAs` — the component family, which fixes the TARGET's frame through
  `TargetView.frameAt`;
* `EAv` — the target's reading as a VALUE, because at a candidate frame
  the target reads as the container's former at the candidate components
  (`targetValAt`) and not as `interp` of a recorded term;
* `frSelf` — this copy's OWN frame, which is what `CopyEntryAtF` reads
  the container's side at.

`entryRead_iff_F` is `Iff.rfl`, so no consumer moves.

**WHICH PARAMETER CARRIES THE OBLIGATION — checked after lane L-B
disputed it, and L-B was right.**  `cAs` occurs ONLY in the hypothesis's
spine fit.  The container's field domain is read at `frSelf`, inside
`CopyEntryAtF`, so **`frSelf` is the parameter that must become the
candidate frame**, and the tree holds no candidate value for it:
`CandParamFit` and `CandIdxAgree` are side conditions ON such a family,
not a construction of one.

**AND THIS DOES NOT REACH `hentR`.**  `CopyCtorShape.fit_imp_T_le_dom`'s
`hentR` reads the container's side at the local notation `ρJ`, the
RECORDED frame, and its proof turns on `slotSet_instTele … Ds ρp` and
`interp_instAll` — the two commutations that force the frame.  So
`CopyEntryAtF` at a candidate `frSelf` is not `hentR`, and the step
between them is not a lemma in this tree. -/
@[expose] def EntryReadF (cAs : Nat → List V) (EAv : Nat → V) (frSelf : Nat → V) (l : Nat) :
    Prop :=
  ∀ Z : Nat → V,
    (∀ is : List V, SpineFit (TV.frameAt cAs ρp (tg l)) (TV.Ids (tg l)) is →
      SetTheory.app (Z (tg l)) (tupW (TV.u (tg l)) is)
        = is.foldl SetTheory.app (EAv (tg l))) →
    CopyEntryAtF dJ ψJ tg tls Eis ρp i j frSelf TV.w TV.u Z l

/-- **Today's reading law IS the frame-generic one at the recorded
data** (task #315 L-E).  `Iff.rfl`; the bridge is a theorem and not a
definitional alias for the signature reason recorded in this file's
header. -/
theorem entryRead_iff_F (l : Nat) :
    EntryRead (V := V) TV dJ ψJ Ds tg tls Eis ρp i j l
      ↔ EntryReadF (V := V) TV dJ ψJ tg tls Eis ρp i j
          (fun q => (TV.Ds (TV.k + q)).map (interp V ρp))
          (fun t => interp V ρp (TV.EA t))
          (consList (Ds.map (interp V ρp)) ρp) l := by
  unfold EntryRead EntryReadF
  simp only [TargetView.frameAt_recorded]
  rfl

variable (base kJ : Nat) (Fs : List AnnotTerm) (rs : List Bool)

/-- **The entry identities at every copy-recursive field OUTSIDE the
group** — the residual the fits need beyond the shape; a theorem of
the whole block (`nestedPinLeaf_all`). -/
@[expose] def CopyEntryOut (w : Nat) (u : Nat → Nat) (Z : Nat → V) : Prop :=
  ∀ l, l < Fs.length → rs.getD l false = true → ¬ (base ≤ tg l ∧ tg l < base + kJ) →
    CopyEntryAt dJ ψJ Ds tg tls Eis ρp i j w u Z l

/-- **The entry identities at the container-ORDINARY fields the
elimination rewrote** — `CopyEntryOut` restricted to the `ordF`-right
arm.  At the WIDE width this is all the fit equivalence asks: a
container-recursive field at one of the container's OWN pins reads the
SEGMENT's own variable on both sides (`CopyCtorShape.fit_iff_wide`'s
`hZY`), so the `pinF` arm no longer passes through its target's stored
reading and the entry there is not consumed.  The narrow route needs
both arms, hence `CopyEntryOut` stays. -/
@[expose] def CopyEntryOrd (w : Nat) (u : Nat → Nat) (Z : Nat → V) : Prop :=
  ∀ l, l < Fs.length → ((dJ.rss i).getD j []).getD l false = false →
    rs.getD l false = true → ¬ (base ≤ tg l ∧ tg l < base + kJ) →
    CopyEntryAt dJ ψJ Ds tg tls Eis ρp i j w u Z l

/-- **The outside entries, FRAME-GENERIC** (task #315 L-E, the abstract
carry): `CopyEntryOut` with the container-side frame an argument.

`Ds` does not occur — the whole point of the carry.  These are the
`ordF`-RIGHT and `pinF` arms, the two that reach the container's field
domain THROUGH the entry, and they are the two the carry covers.  The
three that do not (`recF`, `ordF`-left, `es`) reach `instAll Ds`
directly and are not stated here. -/
@[expose] def CopyEntryOutF (fr : Nat → V) (w : Nat) (u : Nat → Nat) (Z : Nat → V) : Prop :=
  ∀ l, l < Fs.length → rs.getD l false = true → ¬ (base ≤ tg l ∧ tg l < base + kJ) →
    CopyEntryAtF dJ ψJ tg tls Eis ρp i j fr w u Z l

/-- **Today's outside entries ARE the frame-generic ones at the recorded
frame** (task #315 L-E).  `Iff.rfl`, stated as a theorem rather than a
definitional alias for the auto-bound-signature reason in this file's
header. -/
theorem copyEntryOut_iff_F (w : Nat) (u : Nat → Nat) (Z : Nat → V) :
    CopyEntryOut (V := V) dJ ψJ Ds tg tls Eis ρp i j base kJ Fs rs w u Z
      ↔ CopyEntryOutF (V := V) dJ ψJ tg tls Eis ρp i j base kJ Fs rs
          (consList (Ds.map (interp V ρp)) ρp) w u Z := Iff.rfl

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
        SpineFit (consList (Ds.map (interp V ρp)) ρp) (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
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

/-- The outside entries give the container-ordinary ones. -/
theorem CopyEntryOut.ord {dJ : BlockModel V} {ψJ : Name → Nat} {Ds : List AnnotTerm}
    {tg : Nat → Nat} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    {ρp : Nat → V} {i j base kJ : Nat} {Fs : List AnnotTerm} {rs : List Bool}
    {w : Nat} {u : Nat → Nat} {Z : Nat → V}
    (h : CopyEntryOut (V := V) dJ ψJ Ds tg tls Eis ρp i j base kJ Fs rs w u Z) :
    CopyEntryOrd (V := V) dJ ψJ Ds tg tls Eis ρp i j base kJ Fs rs w u Z :=
  fun l hl _ hrC hout => h l hl hrC hout


/-! ## The two copies of ONE container field name ONE target container -/

/-- **A copy's recursive slot at a container-RECURSIVE field is the
container's own slot at the pin's frame** (task #315 L-E, DESIGN
§U.64): `recF` and `pinF` instantiate the telescope and the index
expressions by the same two clauses, so ONE reading serves both arms —
`slotSet_instTele` moves the components out of the frame and into the
base.  What the container instance transfer compares on the two sides. -/
theorem CopyCtorShape.slot_container {TV : TargetView V}
    {acval : Name → (Name → Nat) → AnnotTerm} {dJ : BlockModel V}
    {ψJ : Name → Nat} {Ds : List AnnotTerm} {lpsJ : List Name} {lvlsJ : List Level}
    {tg : Nat → Nat} {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)}
    {ρp : Nat → V} {i j base kJ : Nat} {Fs : List AnnotTerm} {rs : List Bool}
    {Es : List AnnotTerm}
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es)
    {l : Nat} (hl : l < ((dJ.Fss i ψJ).getD j []).length)
    (hr : ((dJ.rss i).getD j []).getD l false = true)
    (fs₁ : List V) (hl₁ : fs₁.length = l) (X : V) :
    slotSet TV.w (TV.u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) X
      = slotSet TV.w (TV.u (tg l)) (consList fs₁ (consList (Ds.map (interp V ρp)) ρp))
          (((dJ.tlss i ψJ).getD j []).getD l []) (((dJ.Eiss i ψJ).getD j []).getD l []) X := by
  subst hl₁
  have hdata : (tls.getD fs₁.length []).map (·.2.2)
        = instTele Ds fs₁.length
            ((((dJ.tlss i ψJ).getD j []).getD fs₁.length []).map (·.2.2)) ∧
      Eis.getD fs₁.length []
        = ((((dJ.Eiss i ψJ).getD j []).getD fs₁.length []).map
            (AnnotTerm.instAll Ds
              (fs₁.length + (((dJ.tlss i ψJ).getD j []).getD fs₁.length []).length))) := by
    by_cases hnt : dJ.tgts i j fs₁.length < dJ.k
    · obtain ⟨-, -, ha, hb⟩ := h.recF _ hl hr hnt
      exact ⟨ha, hb⟩
    · obtain ⟨-, -, -, -, -, ha, hb⟩ := h.pinF _ hl hr hnt
      exact ⟨ha, hb⟩
  rw [hdata.2]
  exact slotSet_instTele Iff.rfl Iff.rfl Ds ρp fs₁ hdata.1 _ X

/-- **The two copies' targets have ONE index universe at a
container-recursive field** (task #315 L-E, DESIGN §U.64): a member
target through `recF`'s position and `hu`, a container's own pin
through `PinCorr`'s `u` clause — in both cases the container's own
datum `dJ.uT (dJ.tgts i j l)` at the two level assignments. -/
theorem copyTarget_u {TV₁ TV₂ : TargetView V} {acval : Name → (Name → Nat) → AnnotTerm}
    {dJ : BlockModel V} {ψ₁ ψ₂ : Name → Nat} {Ds₁ Ds₂ : List AnnotTerm} {lpsJ : List Name}
    {lvls₁ lvls₂ : List Level} {tg₁ tg₂ : Nat → Nat}
    {tls₁ tls₂ : List (List (Nat × Nat × AnnotTerm))} {Eis₁ Eis₂ : List (List AnnotTerm)}
    {ρ₁ ρ₂ : Nat → V} {i j base₁ base₂ kJ : Nat} {Fs₁ Fs₂ : List AnnotTerm}
    {rs₁ rs₂ : List Bool} {Es₁ Es₂ : List AnnotTerm}
    (h₁ : CopyCtorShape TV₁ acval dJ ψ₁ Ds₁ lpsJ lvls₁ tg₁ tls₁ Eis₁ ρ₁ i j base₁ kJ Fs₁ rs₁ Es₁)
    (h₂ : CopyCtorShape TV₂ acval dJ ψ₂ Ds₂ lpsJ lvls₂ tg₂ tls₂ Eis₂ ρ₂ i j base₂ kJ Fs₂ rs₂ Es₂)
    (hkJ : dJ.k = kJ)
    (hu₁ : ∀ i', i' < kJ → TV₁.u (base₁ + i') = dJ.uM i' ψ₁)
    (hu₂ : ∀ i', i' < kJ → TV₂.u (base₂ + i') = dJ.uM i' ψ₂)
    {l : Nat} (hl₁ : l < ((dJ.Fss i ψ₁).getD j []).length)
    (hl₂ : l < ((dJ.Fss i ψ₂).getD j []).length)
    (hr : ((dJ.rss i).getD j []).getD l false = true)
    (hu : dJ.uT (dJ.tgts i j l) ψ₁ = dJ.uT (dJ.tgts i j l) ψ₂) :
    TV₁.u (tg₁ l) = TV₂.u (tg₂ l) := by
  by_cases hnt : dJ.tgts i j l < dJ.k
  · obtain ⟨-, htg₁, -, -⟩ := h₁.recF l hl₁ hr hnt
    obtain ⟨-, htg₂, -, -⟩ := h₂.recF l hl₂ hr hnt
    rw [BlockModel.uT_of_mem hnt ψ₁, BlockModel.uT_of_mem hnt ψ₂] at hu
    rw [htg₁, htg₂, hu₁ _ (hkJ ▸ hnt), hu₂ _ (hkJ ▸ hnt)]
    exact hu
  · obtain ⟨-, -, -, -, ⟨-, -, hv₁, -, -, -⟩, -, -⟩ := h₁.pinF l hl₁ hr hnt
    obtain ⟨-, -, -, -, ⟨-, -, hv₂, -, -, -⟩, -, -⟩ := h₂.pinF l hl₂ hr hnt
    rw [BlockModel.uT_of_pin hnt ψ₁, BlockModel.uT_of_pin hnt ψ₂] at hu
    rw [hv₁, hv₂]
    exact hu

omit [SetTheory V] in
/-- **The container instance transfer's PIN correspondence, off the
recorded pin TABLES** (task #315 L-E, DESIGN §U.61; replaces the
refuted `targetHead_corr`): a container's own copy of one of its pins'
constructors and the BLOCK's copy of the image pin are copies of the
same container-recursive field of the same container `dJ`, so
`CopyCtorShape.pinF` gives a `PinCorr` on each side at the SAME own pin
`qK` of `dJ`.  Then the two targets' RECORDED containers are one —
`dJ.pinAt qK`'s — and their recorded level arguments are that pin's,
substituted at each side's outer level arguments, which identifies the
two targets' index universes (`PinCorr`'s `u`) and so their fibres.

Nothing is read off the container's FIELD: the identity is the
target's position in the two pin tables.  The premise `hpd` is the
syntactic scope of a recorded pin's level arguments — they mention only
the container's own level parameters — which is what makes the two
substitutions compose. -/
theorem targetPin_corr {TV₁ TV₂ : TargetView V} {acval : Name → (Name → Nat) → AnnotTerm}
    {dJ : BlockModel V} {ψ₁ ψ₂ : Name → Nat} {Ds₁ Ds₂ : List AnnotTerm}
    {lpsK lpsJ : List Name} {lvlsK lvlsJ : List Level}
    {t₁ t₂ qK : Nat}
    (h₁ : PinCorr TV₁ acval dJ ψ₁ Ds₁ lpsK lvlsK t₁ qK)
    (h₂ : PinCorr TV₂ acval dJ ψ₂ Ds₂ lpsK (lvlsK.map (Level.subst lpsJ lvlsJ)) t₂ qK)
    (hlenK : lvlsK.length = lpsK.length)
    (hpd : ∀ v ∈ (dJ.pinAt qK).lvls, v.allParamsDefined lpsK = true) :
    TV₂.J t₂ = TV₁.J t₁ ∧
    ∀ (lpsC : List Name) (φ : Name → Nat), (TV₁.lvls t₁).length = lpsC.length →
      ∀ p ∈ lpsC, Level.substFn φ lpsC (TV₂.lvls t₂) p
        = Level.substFn (Level.substFn φ lpsJ lvlsJ) lpsC (TV₁.lvls t₁) p := by
  obtain ⟨-, -, -, -, hJ₁, hus₁⟩ := h₁
  obtain ⟨-, -, -, -, hJ₂, hus₂⟩ := h₂
  refine ⟨hJ₂.trans hJ₁.symm, fun lpsC φ hlen p hp => ?_⟩
  have hvlen : (dJ.pinAt qK).lvls.length = lpsC.length := by
    rw [← hlen, hus₁, List.length_map]
  have hφ : ∀ q ∈ lpsK, Level.substFn φ lpsK (lvlsK.map (Level.subst lpsJ lvlsJ)) q
      = Level.substFn (Level.substFn φ lpsJ lvlsJ) lpsK lvlsK q :=
    fun q hq => Level.substFn_map_subst hlenK hq
  rw [hus₂, hus₁, Level.substFn_map_subst hvlen hp, Level.substFn_map_subst hvlen hp]
  exact Level.substFn_ext hφ hpd hvlen p hp

/-- **A container's constructor data at two level assignments** that
agree on the constructor's level parameters is ONE datum (task #315
L-E, DESIGN §U.51): the field domains, the recursive fields' index
expressions, the reflexive telescopes and the result's index readings.
The container instance transfer compares the container's OWN copy of a
pin's constructor with the BLOCK's copy of the image pin — two copies
of one constructor at two assignments, which `targetPin_corr` makes
agree on that constructor's container's level parameters. -/
theorem IsBlockModel.ctor_params {env : Env} {m : EnvModel V env} {d : BlockModel V}
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {mm : Nat}
    (h : IsBlockModel m T cvT cvR mI rP rules d mm) {j : Nat} {cA : ConstantVal × Nat}
    (hj : (d.ctorsM mm)[j]? = some cA) {ψ₁ ψ₂ : Name → Nat}
    (hψ : ∀ p ∈ cA.1.levelParams, ψ₁ p = ψ₂ p) :
    (d.Fss mm ψ₁).getD j [] = (d.Fss mm ψ₂).getD j [] ∧
    (d.Eiss mm ψ₁).getD j [] = (d.Eiss mm ψ₂).getD j [] ∧
    (d.tlss mm ψ₁).getD j [] = (d.tlss mm ψ₂).getD j [] ∧
    (d.Ess mm ψ₁).getD j [] = (d.Ess mm ψ₂).getD j [] := by
  have hcd := h.ctorData hj
  obtain ⟨hds, hes⟩ := hcd.params ψ₁ ψ₂ hψ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [IsBlockModel.Fss_getD hj, IsBlockModel.Fss_getD hj, hds]
  · rw [IsBlockModel.Eiss_getD hj, IsBlockModel.Eiss_getD hj,
      hcd.eissParams ψ₁ ψ₂ hψ]
  · rw [IsBlockModel.tlss_getD hj, IsBlockModel.tlss_getD hj,
      hcd.tssParams ψ₁ ψ₂ hψ]
  · rw [IsBlockModel.Ess_getD hj, IsBlockModel.Ess_getD hj, hes]

/-! ## The entry at a tuple, from the reading -/

/-- **The entry at a tuple whose target family reads the stored
reading**: `EntryRead` IS this statement since lane L-B refuted its
Π-tower clauses (see `EntryRead`), so the lemma is the predicate
applied.  Kept as a named theorem because it, and not the predicate,
is what the shape's three consumers (`NestedPinLeafAll.lean`) read —
the repair moved no signature. -/
theorem copyEntryAt_of_read {TV : TargetView V} {dJ : BlockModel V} {ψJ : Name → Nat}
    {Ds : List AnnotTerm}
    {tg : Nat → Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eis : List (List AnnotTerm)} {ρp : Nat → V} {i j l : Nat}
    (hread : EntryRead TV dJ ψJ Ds tg tls Eis ρp i j l) {Z : Nat → V}
    (hZ : ∀ is : List V, SpineFit (TV.frame ρp (tg l)) (TV.Ids (tg l)) is →
      SetTheory.app (Z (tg l)) (tupW (TV.u (tg l)) is)
        = is.foldl SetTheory.app (interp V ρp (TV.EA (tg l)))) :
    CopyEntryAt dJ ψJ Ds tg tls Eis ρp i j TV.w TV.u Z l :=
  hread Z hZ

/-- **The entry at a tuple whose target family reads the target's value,
FRAME-GENERIC** (task #315 L-E, clause two).  `copyEntryAt_of_read` with
the target's frame, the target's reading VALUE and this copy's own frame
all supplied — the same one-line proof, because `EntryReadF` is already
the implication this states.

At the candidate frame the caller supplies `EAv := targetValAt …` and
`hZ` from `tupleLfpAV_fold` at the field's target, which is
index-generic: members and copies alike, no case on the target and no
hypothesis at another pin. -/
theorem copyEntryAtF_of_read {TV : TargetView V} {dJ : BlockModel V} {ψJ : Name → Nat}
    {tg : Nat → Nat} {tls : List (List (Nat × Nat × AnnotTerm))}
    {Eis : List (List AnnotTerm)} {ρp : Nat → V} {i j l : Nat}
    {cAs : Nat → List V} {EAv : Nat → V} {frSelf : Nat → V}
    (hread : EntryReadF TV dJ ψJ tg tls Eis ρp i j cAs EAv frSelf l) {Z : Nat → V}
    (hZ : ∀ is : List V, SpineFit (TV.frameAt cAs ρp (tg l)) (TV.Ids (tg l)) is →
      SetTheory.app (Z (tg l)) (tupW (TV.u (tg l)) is)
        = is.foldl SetTheory.app (EAv (tg l))) :
    CopyEntryAtF dJ ψJ tg tls Eis ρp i j frSelf TV.w TV.u Z l :=
  hread Z hZ

/-! ## The fits at one constructor -/

section Fit

variable {TV : TargetView V} {acval : Name → (Name → Nat) → AnnotTerm} {dJ : BlockModel V}
  {ψJ : Name → Nat} {Ds : List AnnotTerm} {DsE : List Expr} {base kJ : Nat}
  {Fs : List AnnotTerm} {rs : List Bool}
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
      · rw [if_neg (by rw [hrC]; exact Bool.false_ne_true), hF fs₁ rfl hsp, interp_instAll]
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

/-- **The slot's value is monotone in the family at every point.** -/
theorem slotSet_mono_app {w u : Nat} {ρ : Nat → V} {tl : List (Nat × Nat × AnnotTerm)}
    {Eis : List AnnotTerm} {X Y : V} (h : ∀ t, SetTheory.app X t ⊆ˢ SetTheory.app Y t) :
    slotSet w u ρ tl Eis X ⊆ˢ slotSet w u ρ tl Eis Y := by
  unfold slotSet
  exact piTele_mono fun bs _ => h _

/-- **`hfit` at one constructor, AT THE WIDE WIDTH** (task #315,
Resolution 1): the copy's fit at an arbitrary tuple `Z` over the
block's targets is the container's CLASS fit (`ChainFitT`) at the
corresponding tuple `Y` over the container's classes.

Three things are different from `fit_iff_at`, and they are exactly what
the wide route buys and pays:

* a container-recursive field at one of the container's OWN pins is no
  longer read through its entry: the container's class fit reads its own
  pin as a VARIABLE, the copy reads the block's corresponding pin, and
  `hZY` says the two tuples agree there.  `recF` and `pinF` therefore
  collapse into ONE arm, whose reading identity is `slot_container` for
  both;
* the container's side is at a FREE tuple `Y`, so the spine-carrying
  obligation — the container's slot is inside its field domain — is not
  `real_dom_eq` alone: it is `real_dom_eq` at the container's carrier
  plus the BOUND `hYle`, `Y` below the container's classes' carrier
  (`BlockModel.auxLfp_eq_famAt` puts that carrier in `famAt` form).
  This is the bound `docs/NESTED.md` §0's (B-below) takes;
* what is unchanged is the ordinary arm: `ordF`-left is the reading
  identity under instantiation, `ordF`-right the entry at a target
  OUTSIDE the group, which `hent` supplies at `Z` (at such a target the
  joined tuple is the block's own carrier).  The entries are asked at
  that arm ALONE, so the hypothesis is `CopyEntryOrd` and not
  `CopyEntryOut`: at a `pinF` field the target is INSIDE the instance,
  where the tuple is free and no entry at the block's carrier holds. -/
theorem CopyCtorShape.fit_iff_wide {env : Env} {m : EnvModel V env}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hi : i < dJ.k)
    (hw : dJ.w ψJ = TV.w)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    {nI : Nat} (hnI : nI = (dJ.IdsM i ψJ).length)
    {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es)
    {Y Z : Nat → V}
    (huT : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
      ((dJ.rss i).getD j []).getD l false = true → TV.u (tg l) = dJ.uT (dJ.tgts i j l) ψJ)
    (hZY : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
      ((dJ.rss i).getD j []).getD l false = true → Z (tg l) = Y (dJ.tgts i j l))
    (hYle : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
      ((dJ.rss i).getD j []).getD l false = true → ∀ t',
      SetTheory.app (Y (dJ.tgts i j l)) t' ⊆ˢ SetTheory.app (dJ.famAt ψJ ρJ LJ (dJ.tgts i j l)) t')
    (hent : CopyEntryOrd dJ ψJ Ds tg tls Eis ρp i j base kJ Fs rs TV.w TV.u Z)
    (t : V) (fs : List V) :
    (FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' []) (Eis.getD i' [])
        (Z (tg i'))) 0 ρp Fs fs ∧
      (∀ l, l < nI → interp V (consList fs ρp) (Es.getD l default) = projS l t))
    ↔ dJ.ChainFitT dJ.pinCtors ψJ ρJ Y t i j fs := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hjl : j < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hlenF := hI.Fss_length hj ψJ
  have hLJ : LJ = lfpTuple (dJ.w ψJ) dJ.k (dJ.idx ψJ ρJ) (dJ.Φ ψJ ρJ) := by rw [hw]
  -- the fits
  have hfits : FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' [])
        (Eis.getD i' []) (Z (tg i'))) 0 ρp Fs fs ↔
      FitsFrom ((dJ.rss i).getD j []) (dJ.slotAtT dJ.pinCtors ψJ Y i j) 0 ρJ
        ((dJ.Fss i ψJ).getD j []) fs := by
    refine (fitsFrom_iff_frames_spine h.len.symm fun l hl fs₁ hl₁ hsp hf hf' => ?_).symm
    subst hl₁
    have hlt : fs₁.length < cA.2 := by rw [← hlenF]; exact hl
    simp only [Nat.zero_add]
    by_cases hr : ((dJ.rss i).getD j []).getD fs₁.length false = true
    · have hr' : (rsOf (dJ.ksF i j)).getD fs₁.length false = true := by
        rwa [IsBlockModel.rss_getD hjl] at hr
      have hreal := hreps.real_dom_eq hfT hPT hi hj hρJ hlt hr' hsp
      rw [hw] at hreal
      -- the container's slot at `Y`, at a frame whose parameter part is `ρJ`
      have hslotT : dJ.slotAtT dJ.pinCtors ψJ Y i j fs₁.length (consList fs₁ ρJ)
          = slotSet (dJ.w ψJ) (dJ.uT (dJ.tgts i j fs₁.length) ψJ) (consList fs₁ ρJ)
              (((dJ.tlss i ψJ).getD j []).getD fs₁.length [])
              (((dJ.Eiss i ψJ).getD j []).getD fs₁.length []) (Y (dJ.tgts i j fs₁.length)) := by
        unfold BlockModel.slotAtT BlockModel.teleAtT BlockModel.eisAtT
        rw [BlockModel.tgtsT_of_mem hi, BlockModel.tlssT_of_mem hi, BlockModel.EissT_of_mem hi]
      -- the container's slot at its own carrier, in the same shape
      have hslotL : dJ.slotAt ψJ LJ i j fs₁.length (consList fs₁ ρJ)
          = slotSet (dJ.w ψJ) (dJ.uT (dJ.tgts i j fs₁.length) ψJ) (consList fs₁ ρJ)
              (((dJ.tlss i ψJ).getD j []).getD fs₁.length [])
              (((dJ.Eiss i ψJ).getD j []).getD fs₁.length [])
              (dJ.famAt ψJ ρJ LJ (dJ.tgts i j fs₁.length)) := by
        have hfr : (fun n => consList fs₁ ρJ (n + fs₁.length)) = ρJ :=
          funext fun n => consList_apply_add fs₁ ρJ n
        unfold BlockModel.slotAt
        rw [hfr]
      rw [if_pos hr, hslotT]
      refine ⟨?_, ?_⟩
      · -- the container's slot at `Y` is inside its field domain: the BOUND
        rw [hreal, hslotL]
        exact slotSet_mono_app (hYle _ hl hr)
      · -- the two slots are one reading
        rw [if_pos (by
            rcases hI.tgt_cases hjl (by rw [(hI.ctorData hj).ksLen]; exact hlt) with
              htgt | ⟨hnt, -⟩
            · exact (h.recF _ hl hr htgt).1
            · exact (h.pinF _ hl hr hnt).1),
          h.slot_container hl hr fs₁ rfl (Z (tg fs₁.length)), huT _ hl hr, hw,
          hZY _ hl hr]
    · have hr' : ((dJ.rss i).getD j []).getD fs₁.length false = false := by simpa using hr
      rw [if_neg (by rw [hr']; exact Bool.false_ne_true)]
      refine ⟨Subset.refl _, ?_⟩
      rcases h.ordF _ hl hr' with ⟨hrC, hF⟩ | ⟨hrC, hout, -, -⟩
      · rw [if_neg (by rw [hrC]; exact Bool.false_ne_true), hF fs₁ rfl hsp, interp_instAll]
      · rw [if_pos hrC]
        exact hent _ (h.len ▸ hl) hr' hrC hout fs₁ rfl hsp
  -- the index equations
  refine Iff.trans (and_congr hfits Iff.rfl) ?_
  unfold BlockModel.ChainFitT
  rw [BlockModel.rssT_of_mem hi, BlockModel.FssT_of_mem hi, BlockModel.EssT_of_mem hi,
    BlockModel.IdsT_of_mem hi]
  refine and_congr_right fun hf => ?_
  have hlen : fs.length = ((dJ.Fss i ψJ).getD j []).length := hf.length_eq
  rw [hnI]
  refine forall_congr' fun l => imp_congr_right fun hl => ?_
  rw [h.es l hl, ← hlen, interp_instAll]

/-- **`hentR` AT ONE FIELD, FROM AN ENTRY IDENTITY AT ANOTHER FAMILY**
(task #315 L-C, the constant-headed step's arithmetic): if the
container's field domain, read at whatever frame `fr` the statement
stands at, IS the copy's slot at a family `P`, and `P` lies under `Z` at
the field's target, then the domain lies under the copy's slot at `Z` —
which is exactly the `hentR` of `CopyCtorShape.fit_imp_T_le_dom` at that
field.

**What it is for, named.**  `hentR` is step (iii)'s only cross-pin
obligation (DESIGN, the adjudication of 2026-09-18).  At a copy-recursive
field whose container kind is ordinary and whose target `tg l` is a pin
outside the group, the two inputs decompose as:

* `hent` — the ENTRY IDENTITY at the target's OWN carrier.  At a
  CONSTANT-HEADED container domain (`Array`'s field `List α`, at a
  candidate frame sending `α` to the block's auxiliary carrier) that
  carrier is the target container's least tuple at those arguments —
  the target pin's `pinLfpAt`, which is why the identity is available
  without any fact at another pin;
* `hle` — the INDUCTION HYPOTHESIS at the target pin, `P (tg l)` under
  `Z (tg l)`, which is `pins_le_of_declOrder`'s hypothesis read through
  `app_subset_of_famLe`.

So this lemma is where the declaration-order induction's conclusion at
the INNER pin turns into the outer pin's `hentR`, and it is the only
step of that arm that is arithmetic rather than syntactic.  It says
nothing about the frame: `fr` is universally quantified, so the same
lemma serves the recorded frame and a candidate one. -/
theorem copyEntryAtF_le_of_app {fr : Nat → V} {w : Nat} {u : Nat → Nat} {P Z : Nat → V} {l : Nat}
    (hent : CopyEntryAtF (V := V) dJ ψJ tg tls Eis ρp i j fr w u P l)
    (hle : ∀ t', SetTheory.app (P (tg l)) t' ⊆ˢ SetTheory.app (Z (tg l)) t') :
    ∀ fs₁ : List V, fs₁.length = l →
      SpineFit fr (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
      interp V (consList fs₁ fr) (((dJ.Fss i ψJ).getD j []).getD l default)
        ⊆ˢ slotSet w (u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) (Z (tg l)) := by
  intro fs₁ hl₁ hsp
  rw [hent fs₁ hl₁ hsp]
  exact slotSet_mono_app hle

/-- **The same, with the induction hypothesis in its OWN shape** (task
#315 L-C): `pins_le_of_declOrder` concludes a `FamLe` at the target
pin's index set, and `lfpTuple_mem` puts the target's least tuple in
that index set's family space, so the two hypotheses this takes are
literally what the induction step holds. -/
theorem copyEntryAtF_le_of_famLe {fr : Nat → V} {w wI : Nat} {u : Nat → Nat} {P Z : Nat → V}
    {I : V} {l : Nat}
    (hent : CopyEntryAtF (V := V) dJ ψJ tg tls Eis ρp i j fr w u P l)
    (hmem : P (tg l) ∈ˢ famSpace wI I) (hIH : FamLe I (P (tg l)) (Z (tg l))) :
    ∀ fs₁ : List V, fs₁.length = l →
      SpineFit fr (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
      interp V (consList fs₁ fr) (((dJ.Fss i ψJ).getD j []).getD l default)
        ⊆ˢ slotSet w (u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) (Z (tg l)) :=
  copyEntryAtF_le_of_app hent (app_subset_of_famLe hmem hIH)

theorem CopyCtorShape.fit_imp_T_le_dom {env : Env} {m : EnvModel V env} {pc : Nat → PinCtors V}
    {T : Nat → V}
    (hreps : IsBlockModels m dJ)
    (hi : i < dJ.k) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = TV.w)
    (hu : ∀ i', i' < kJ → TV.u (base + i') = dJ.uM i' ψJ)
    {nI : Nat} (hnI : nI = (dJ.IdsM i ψJ).length)
    {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (hdom : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
      ((dJ.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρJ (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
      dJ.slotAtT pc ψJ T i j l (consList fs₁ ρJ)
        ⊆ˢ interp V (consList fs₁ ρJ) (((dJ.Fss i ψJ).getD j []).getD l default))
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es)
    {Z : Nat → V}
    (hrel : ∀ l, l < Fs.length → ((dJ.rss i).getD j []).getD l false = true →
      ∀ t', SetTheory.app (T (dJ.tgts i j l)) t' ⊆ˢ SetTheory.app (Z (tg l)) t')
    (hentR : ∀ l, l < Fs.length → rs.getD l false = true →
      ((dJ.rss i).getD j []).getD l false = false → ¬ (base ≤ tg l ∧ tg l < base + kJ) →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρJ (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
        interp V (consList fs₁ ρJ) (((dJ.Fss i ψJ).getD j []).getD l default)
          ⊆ˢ slotSet TV.w (TV.u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) (Z (tg l)))
    (t : V) (fs : List V) (hC : dJ.ChainFitT pc ψJ ρJ T t i j fs) :
    FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' []) (Eis.getD i' [])
        (Z (tg i'))) 0 ρp Fs fs ∧
    (∀ l, l < nI → interp V (consList fs ρp) (Es.getD l default) = projS l t) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hjl : j < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hlenF := hI.Fss_length hj ψJ
  have hks : (dJ.ksF i j).length = ((dJ.Fss i ψJ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hlenF]
  unfold BlockModel.ChainFitT at hC
  rw [BlockModel.rssT_of_mem hi, BlockModel.FssT_of_mem hi, BlockModel.IdsT_of_mem hi,
    BlockModel.EssT_of_mem hi] at hC
  obtain ⟨hfC, hiC⟩ := hC
  have hlen : fs.length = ((dJ.Fss i ψJ).getD j []).length := hfC.length_eq
  refine ⟨fitsFrom_imp_frames_spine h.len.symm (fun l hl fs₁ hl₁ hsp hf hf' => ?_) hfC, ?_⟩
  · subst hl₁
    have hlt : fs₁.length < cA.2 := by rw [← hlenF]; exact hl
    have hkl : fs₁.length < (dJ.ksF i j).length := by rw [hks]; exact hl
    simp only [Nat.zero_add]
    by_cases hr : ((dJ.rss i).getD j []).getD fs₁.length false = true
    · have hr' : (rsOf (dJ.ksF i j)).getD fs₁.length false = true := by
        rwa [IsBlockModel.rss_getD hjl] at hr
      rw [if_pos hr]
      refine ⟨hdom _ hl hr fs₁ rfl hsp, ?_⟩
      rcases hI.tgt_cases hjl hkl with htgt | ⟨hnt, -⟩
      · obtain ⟨hrC, htg, htl, hEis⟩ := h.recF _ hl hr htgt
        simp only [BlockModel.slotAtT, BlockModel.teleAtT_of_mem hi, BlockModel.eisAtT_of_mem hi,
          BlockModel.tgtsT_of_mem hi, BlockModel.teleAt, BlockModel.eisAt,
          BlockModel.uT_of_mem htgt]
        rw [if_pos hrC, htg, hEis, hw, hu _ (hkJ ▸ htgt),
          slotSet_instTele Iff.rfl Iff.rfl Ds ρp fs₁ htl _ _]
        refine slotSet_mono_app fun t' => ?_
        have := hrel _ (h.len ▸ hl) hr t'
        rwa [htg] at this
      · obtain ⟨hrC, hout, -, -, ⟨-, -, hu', -, -, -⟩, htl, hEis⟩ := h.pinF _ hl hr hnt
        simp only [BlockModel.slotAtT, BlockModel.teleAtT_of_mem hi, BlockModel.eisAtT_of_mem hi,
          BlockModel.tgtsT_of_mem hi, BlockModel.teleAt, BlockModel.eisAt,
          BlockModel.uT_of_pin hnt]
        rw [if_pos hrC, hEis, hw, hu', slotSet_instTele Iff.rfl Iff.rfl Ds ρp fs₁ htl _ _]
        exact slotSet_mono_app (hrel _ (h.len ▸ hl) hr)
    · have hr' : ((dJ.rss i).getD j []).getD fs₁.length false = false := by simpa using hr
      rw [if_neg (by rw [hr']; exact Bool.false_ne_true)]
      refine ⟨Subset.refl _, ?_⟩
      rcases h.ordF _ hl hr' with ⟨hrC, hF⟩ | ⟨hrC, hout, -, -⟩
      · rw [if_neg (by rw [hrC]; exact Bool.false_ne_true), hF fs₁ rfl hsp, interp_instAll]
        exact Subset.refl _
      · rw [if_pos hrC]
        exact hentR _ (h.len ▸ hl) hrC hr' hout fs₁ rfl hsp
  · intro l hl
    rw [hnI] at hl
    rw [h.es l hl, ← hlen, interp_instAll]
    exact hiC l hl

/-- **`hfit` at one constructor, at a VARIABLE extended tuple, one
direction, the targets RELATED** (task #315 L-E, DESIGN §U.48 (h): the
blob transfer's member half): a spine fitting the container's
constructor at an extended tuple `T` below the extended carrier fits
the copy at a block tuple `Z` whenever, at every recursive field, the
container's target class at `T` lies under the copy's target at `Z`
(`hrel`, the relation's premise) and, at every `ordF`-right field, the
container's domain lies under the copy's slot at `Z` (`hentR`, the
externals).  The container's slots at `T` are within its real domains
(`slotAtT_mono` to the extended carrier), which the frames' kit
carries. -/
theorem CopyCtorShape.fit_imp_T_le {env : Env} {m : EnvModel V env} {pc : Nat → PinCtors V}
    {T : Nat → V}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hi : i < dJ.k) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = TV.w)
    (hu : ∀ i', i' < kJ → TV.u (base + i') = dJ.uM i' ψJ)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    {nI : Nat} (hnI : nI = (dJ.IdsM i ψJ).length)
    {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (hTs : InTupleSpace (dJ.w ψJ) (dJ.kT) (dJ.idxT ψJ ρJ) T)
    (hTle : TupleLe (dJ.kT) (dJ.idxT ψJ ρJ) T (dJ.famAt ψJ ρJ LJ))
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es)
    {Z : Nat → V}
    (hrel : ∀ l, l < Fs.length → ((dJ.rss i).getD j []).getD l false = true →
      ∀ t', SetTheory.app (T (dJ.tgts i j l)) t' ⊆ˢ SetTheory.app (Z (tg l)) t')
    (hentR : ∀ l, l < Fs.length → rs.getD l false = true →
      ((dJ.rss i).getD j []).getD l false = false → ¬ (base ≤ tg l ∧ tg l < base + kJ) →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρJ (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
        interp V (consList fs₁ ρJ) (((dJ.Fss i ψJ).getD j []).getD l default)
          ⊆ˢ slotSet TV.w (TV.u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) (Z (tg l)))
    (t : V) (fs : List V) (hC : dJ.ChainFitT pc ψJ ρJ T t i j fs) :
    FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' []) (Eis.getD i' [])
        (Z (tg i'))) 0 ρp Fs fs ∧
    (∀ l, l < nI → interp V (consList fs ρp) (Es.getD l default) = projS l t) := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hjl : j < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hks : (dJ.ksF i j).length = ((dJ.Fss i ψJ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hI.Fss_length hj]
  have hTle' : ∀ c, c < dJ.kT → ∀ t', SetTheory.app (T c) t' ⊆ˢ SetTheory.app (dJ.famAt ψJ ρJ LJ c) t' :=
    fun c hc t' => app_subset_of_famLe (hTs c hc) (hTle c hc) t'
  refine fit_imp_T_le_dom hreps hi hkJ hw hu hnI hj (fun l hl hr fs₁ hl₁ hsp => ?_)
    h hrel hentR t fs hC
  subst hl₁
  have hlt : fs₁.length < cA.2 := by rw [← hI.Fss_length hj ψJ]; exact hl
  have hkl : fs₁.length < (dJ.ksF i j).length := by rw [hks]; exact hl
  have hr' : (rsOf (dJ.ksF i j)).getD fs₁.length false = true := by
    rwa [IsBlockModel.rss_getD hjl] at hr
  have hreal := hreps.real_dom_eq hfT hPT hi hj hρJ hlt hr' hsp
  rw [hw] at hreal
  have htgtLt : dJ.tgts i j fs₁.length < dJ.kT := by
    rcases hI.tgt_cases hjl hkl with h1 | ⟨-, h2⟩
    · show _ < dJ.k + dJ.nPins; omega
    · show _ < dJ.k + dJ.nPins; omega
  refine Subset.trans (dJ.slotAtT_mono pc (Y' := dJ.famAt ψJ ρJ LJ) ?_) ?_
  · rw [BlockModel.tgtsT_of_mem hi]
    exact hTle' _ htgtLt
  · rw [BlockModel.slotAtT_of_mem hi ψJ ρJ LJ j fs₁.length rfl, hreal]
    exact Subset.refl _

/-- **`hfit` at one constructor, at a VARIABLE extended tuple, the
container's slots BOUNDED by hypothesis** (task #315 L-E, DESIGN §U.54:
`fit_iff_at_T` with `hdom` as a premise — the container instance
transfer carries the bound across a change of level assignment and
frame, where the container's tuple space is not a congruence of any
clause).  (task
#315 L-E, DESIGN §U.48: the blob transfer's member half): a spine fits
the copy at the joined tuple — the group segment read at `Y`'s member
part, a `pinF` target read at `Y`'s pin part through the pullback `hL`,
an `ordF`-right target at the outer tuple `L` (the externals) — iff it
fits the container's constructor at the extended tuple `Y`
(`ChainFitT`: the container's own pins are VARIABLES, not the least
section), for `Y` below the extended carrier (`famAt` at the least
tuple: the container's slots at `Y` are within its real domains,
`slotAtT_mono`, which the frames' kit carries). -/
theorem CopyCtorShape.fit_iff_at_T_dom {env : Env} {m : EnvModel V env} {pc : Nat → PinCtors V}
    {Y : Nat → V}
    (hreps : IsBlockModels m dJ)
    (hi : i < dJ.k) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = TV.w)
    (hu : ∀ i', i' < kJ → TV.u (base + i') = dJ.uM i' ψJ)
    {nI : Nat} (hnI : nI = (dJ.IdsM i ψJ).length)
    {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (hdom : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
      ((dJ.rss i).getD j []).getD l false = true →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρJ (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
      dJ.slotAtT pc ψJ Y i j l (consList fs₁ ρJ)
        ⊆ˢ interp V (consList fs₁ ρJ) (((dJ.Fss i ψJ).getD j []).getD l default))
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es)
    {L : Nat → V} (hent : CopyEntryOut dJ ψJ Ds tg tls Eis ρp i j base kJ Fs rs TV.w TV.u L)
    (hL : ∀ l, l < Fs.length → ((dJ.rss i).getD j []).getD l false = true →
      ¬ dJ.tgts i j l < dJ.k → L (tg l) = Y (dJ.tgts i j l))
    (t : V) (fs : List V) :
    (FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' []) (Eis.getD i' [])
        (segJoin base kJ L Y (tg i'))) 0 ρp Fs fs ∧
      (∀ l, l < nI → interp V (consList fs ρp) (Es.getD l default) = projS l t))
    ↔ dJ.ChainFitT pc ψJ ρJ Y t i j fs := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hjl : j < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hlenF := hI.Fss_length hj ψJ
  have hks : (dJ.ksF i j).length = ((dJ.Fss i ψJ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hlenF]
  unfold BlockModel.ChainFitT
  rw [BlockModel.rssT_of_mem hi, BlockModel.FssT_of_mem hi, BlockModel.IdsT_of_mem hi,
    BlockModel.EssT_of_mem hi]
  -- the fits
  have hfits : FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' []) (Eis.getD i' [])
        (segJoin base kJ L Y (tg i'))) 0 ρp Fs fs ↔
      FitsFrom ((dJ.rss i).getD j []) (dJ.slotAtT pc ψJ Y i j) 0 ρJ ((dJ.Fss i ψJ).getD j []) fs := by
    refine (fitsFrom_iff_frames_spine h.len.symm fun l hl fs₁ hl₁ hsp hf hf' => ?_).symm
    subst hl₁
    have hlt : fs₁.length < cA.2 := by rw [← hlenF]; exact hl
    have hkl : fs₁.length < (dJ.ksF i j).length := by rw [hks]; exact hl
    simp only [Nat.zero_add]
    by_cases hr : ((dJ.rss i).getD j []).getD fs₁.length false = true
    · rw [if_pos hr]
      refine ⟨hdom _ hl hr fs₁ rfl hsp, ?_⟩
      rcases hI.tgt_cases hjl hkl with htgt | ⟨hnt, -⟩
      · obtain ⟨hrC, htg, htl, hEis⟩ := h.recF _ hl hr htgt
        simp only [BlockModel.slotAtT, BlockModel.teleAtT_of_mem hi, BlockModel.eisAtT_of_mem hi,
          BlockModel.tgtsT_of_mem hi, BlockModel.teleAt, BlockModel.eisAt,
          BlockModel.uT_of_mem htgt]
        rw [if_pos hrC, htg, segJoin_add _ _ (hkJ ▸ htgt), hEis, hw, hu _ (hkJ ▸ htgt)]
        exact (slotSet_instTele Iff.rfl Iff.rfl Ds ρp fs₁ htl _ _).symm
      · obtain ⟨hrC, hout, -, -, ⟨-, -, hu', -, -, -⟩, htl, hEis⟩ := h.pinF _ hl hr hnt
        simp only [BlockModel.slotAtT, BlockModel.teleAtT_of_mem hi, BlockModel.eisAtT_of_mem hi,
          BlockModel.tgtsT_of_mem hi, BlockModel.teleAt, BlockModel.eisAt,
          BlockModel.uT_of_pin hnt]
        rw [if_pos hrC, segJoin_out _ _ hout, hL _ (h.len ▸ hl) hr hnt, hEis, hw, hu']
        exact (slotSet_instTele Iff.rfl Iff.rfl Ds ρp fs₁ htl _ _).symm
    · have hr' : ((dJ.rss i).getD j []).getD fs₁.length false = false := by simpa using hr
      rw [if_neg (by rw [hr']; exact Bool.false_ne_true)]
      refine ⟨Subset.refl _, ?_⟩
      rcases h.ordF _ hl hr' with ⟨hrC, hF⟩ | ⟨hrC, hout, -, -⟩
      · rw [if_neg (by rw [hrC]; exact Bool.false_ne_true), hF fs₁ rfl hsp, interp_instAll]
      · rw [if_pos hrC, segJoin_out _ _ hout]
        exact hent _ (h.len ▸ hl) hrC hout fs₁ rfl hsp
  -- the index equations
  refine Iff.trans (and_congr hfits (Iff.rfl)) ?_
  refine and_congr_right fun hf => ?_
  have hlen : fs.length = ((dJ.Fss i ψJ).getD j []).length := hf.length_eq
  rw [hnI]
  refine forall_congr' fun l => imp_congr_right fun hl => ?_
  rw [h.es l hl, ← hlen, interp_instAll]

/-- **`hfit` at one constructor, at a VARIABLE extended tuple** (task
#315 L-E, DESIGN §U.48: the container instance transfer's member half):
`fit_iff_at_T_dom` with the bound taken from `Y`'s place in the
container's tuple space (`slotAtT_mono` to the extended carrier, where
the slot IS the real domain). -/
theorem CopyCtorShape.fit_iff_at_T {env : Env} {m : EnvModel V env} {pc : Nat → PinCtors V}
    {Y : Nat → V}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hi : i < dJ.k) (hkJ : dJ.k = kJ)
    (hw : dJ.w ψJ = TV.w)
    (hu : ∀ i', i' < kJ → TV.u (base + i') = dJ.uM i' ψJ)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    {nI : Nat} (hnI : nI = (dJ.IdsM i ψJ).length)
    {cA : ConstantVal × Nat} (hj : (dJ.ctorsM i)[j]? = some cA)
    (hYs : InTupleSpace (dJ.w ψJ) (dJ.kT) (dJ.idxT ψJ ρJ) Y)
    (hYle : TupleLe (dJ.kT) (dJ.idxT ψJ ρJ) Y (dJ.famAt ψJ ρJ LJ))
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es)
    {L : Nat → V} (hent : CopyEntryOut dJ ψJ Ds tg tls Eis ρp i j base kJ Fs rs TV.w TV.u L)
    (hL : ∀ l, l < Fs.length → ((dJ.rss i).getD j []).getD l false = true →
      ¬ dJ.tgts i j l < dJ.k → L (tg l) = Y (dJ.tgts i j l))
    (t : V) (fs : List V) :
    (FitsFrom rs (fun i' ρ => slotSet TV.w (TV.u (tg i')) ρ (tls.getD i' []) (Eis.getD i' [])
        (segJoin base kJ L Y (tg i'))) 0 ρp Fs fs ∧
      (∀ l, l < nI → interp V (consList fs ρp) (Es.getD l default) = projS l t))
    ↔ dJ.ChainFitT pc ψJ ρJ Y t i j fs := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
  have hjl : j < (dJ.ctorsM i).length := (List.getElem?_eq_some_iff.mp hj).1
  have hks : (dJ.ksF i j).length = ((dJ.Fss i ψJ).getD j []).length := by
    rw [(hI.ctorData hj).ksLen, hI.Fss_length hj]
  have hYle' : ∀ c, c < dJ.kT → ∀ t', app (Y c) t' ⊆ˢ app (dJ.famAt ψJ ρJ LJ c) t' :=
    fun c hc t' => app_subset_of_famLe (hYs c hc) (hYle c hc) t'
  refine fit_iff_at_T_dom hreps hi hkJ hw hu hnI hj (fun l hl hr fs₁ hl₁ hsp => ?_)
    h hent hL t fs
  subst hl₁
  have hlt : fs₁.length < cA.2 := by rw [← hI.Fss_length hj ψJ]; exact hl
  have hkl : fs₁.length < (dJ.ksF i j).length := by rw [hks]; exact hl
  have hr' : (rsOf (dJ.ksF i j)).getD fs₁.length false = true := by
    rwa [IsBlockModel.rss_getD hjl] at hr
  have hreal := hreps.real_dom_eq hfT hPT hi hj hρJ hlt hr' hsp
  rw [hw] at hreal
  have htgtLt : dJ.tgts i j fs₁.length < dJ.kT := by
    rcases hI.tgt_cases hjl hkl with h1 | ⟨-, h2⟩
    · show _ < dJ.k + dJ.nPins; omega
    · show _ < dJ.k + dJ.nPins; omega
  refine Subset.trans (dJ.slotAtT_mono pc (Y' := dJ.famAt ψJ ρJ LJ) ?_) ?_
  · rw [BlockModel.tgtsT_of_mem hi]
    exact hYle' _ htgtLt
  · rw [BlockModel.slotAtT_of_mem hi ψJ ρJ LJ j fs₁.length rfl, hreal]
    exact Subset.refl _

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
      · rw [if_neg (by rw [hrC]; exact Bool.false_ne_true), hF fs₁ rfl hsp, interp_instAll]
        exact Subset.refl _
      · rw [if_pos hrC, segJoin_out _ _ hout, hent _ (h.len ▸ hl) hrC hout fs₁ rfl hsp]
        exact Subset.refl _
  · intro l hl
    rw [hnI] at hl
    rw [h.es l hl, ← hlen, interp_instAll]
    exact hiC l hl

/-- **`fit_imp` with the outside targets' entries as INCLUSIONS** (task
#315 L-E, step (iii)): at an `ordF`-right field the container's domain
reading lies in the copy's slot at the outer tuple (`hentR`); at a
`pinF` field the container's slot at its OWN PIN's carrier at `Y` — not
at the least tuple — lies in the copy's slot at the outer tuple
(`hentP`): the cycle's closure supplies it from the container's own
`PinRecLaws.ind` at `Y`, where the least tuple's reading would beg the
question. -/
theorem CopyCtorShape.fit_imp_le {env : Env} {m : EnvModel V env} {Y : Nat → V}
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
    {L : Nat → V}
    (hentR : ∀ l, l < Fs.length → rs.getD l false = true →
      ((dJ.rss i).getD j []).getD l false = false → ¬ (base ≤ tg l ∧ tg l < base + kJ) →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρJ (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
        interp V (consList fs₁ ρJ) (((dJ.Fss i ψJ).getD j []).getD l default)
          ⊆ˢ slotSet TV.w (TV.u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) (L (tg l)))
    (hentP : ∀ l, l < Fs.length → ((dJ.rss i).getD j []).getD l false = true →
      ¬ dJ.tgts i j l < dJ.k → ¬ (base ≤ tg l ∧ tg l < base + kJ) →
      ∀ fs₁ : List V, fs₁.length = l → SpineFit ρJ (((dJ.Fss i ψJ).getD j []).take l) fs₁ →
        dJ.slotAt ψJ Y i j l (consList fs₁ ρJ)
          ⊆ˢ slotSet TV.w (TV.u (tg l)) (consList fs₁ ρp) (tls.getD l []) (Eis.getD l []) (L (tg l)))
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
        rw [if_pos hrC, segJoin_out _ _ hout]
        exact hentP _ (h.len ▸ hl) hr hnt hout fs₁ rfl hsp
    · have hr' : ((dJ.rss i).getD j []).getD fs₁.length false = false := by simpa using hr
      rw [if_neg (by rw [hr']; exact Bool.false_ne_true)]
      refine ⟨Subset.refl _, ?_⟩
      rcases h.ordF _ hl hr' with ⟨hrC, hF⟩ | ⟨hrC, hout, -, -⟩
      · rw [if_neg (by rw [hrC]; exact Bool.false_ne_true), hF fs₁ rfl hsp, interp_instAll]
        exact Subset.refl _
      · rw [if_pos hrC, segJoin_out _ _ hout]
        exact hentR _ (h.len ▸ hl) hrC hr' hout fs₁ rfl hsp
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
    {dJ : BlockModel V} {ψJ : Name → Nat} {Ds : List AnnotTerm}
    {lpsJ : List Name} {lvlsJ : List Level} {tg : Nat → Nat}
    {tls : List (List (Nat × Nat × AnnotTerm))} {Eis : List (List AnnotTerm)} {ρp : Nat → V}
    {i j base kJ : Nat} {Fs : List AnnotTerm} {rs : List Bool} {Es : List AnnotTerm}
    (EA' : Nat → AnnotTerm) (hEA : ∀ t, t < TV.k + TV.n → EA' t = TV.EA t)
    (hac : ∀ qK, qK < dJ.nPins →
      acval' (dJ.pinAt qK).J ((dJ.pinAt qK).ψJ ψJ) = acval (dJ.pinAt qK).J ((dJ.pinAt qK).ψJ ψJ))
    (htgt : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length → ¬ dJ.tgts i j l < dJ.k →
      dJ.tgts i j l - dJ.k < dJ.nPins)
    (h : CopyCtorShape TV acval dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ Fs rs Es) :
    CopyCtorShape { TV with EA := EA' } acval' dJ ψJ Ds lpsJ lvlsJ tg tls Eis ρp i j base kJ
      Fs rs Es where
  len := h.len
  recF := h.recF
  ordF := fun l hl hr => by
    rcases h.ordF l hl hr with hL | ⟨h1, h2, h3, hr⟩
    · exact Or.inl hL
    · refine Or.inr ⟨h1, h2, h3, fun Z hZ => hr Z fun is his => ?_⟩
      have hz := hZ is his
      show _ = List.foldl _ (interp V ρp (TV.EA (tg l))) _
      rw [← hEA _ h3]
      exact hz
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
  {Fss₀ Ess₀ : (Name → Nat) → List (List AnnotTerm)} {pc : Nat → PinCtors V}

local notation "D" => (BlockModel.ofNested (V := V) nP k resSort isProp large env₀ memberNames
  nIdxs ppsA W ctorsM idxF dsF esF srcsF ksF tgts fvsPF xFvsF xrestF eissF tssF pins offs mems nFs
  tgtsG rss tlss Eiss₀ Fss₀ Ess₀ pc)

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
  DsE := fun t => (pins.getD (t - k) default).DsE
  EA := targetRead acval memberNames pins nP k ψ
  J := fun t => if t < k then memberNames.getD t .anonymous else (pins.getD (t - k) default).J
  lvls := fun t => if t < k then [] else (pins.getD (t - k) default).lvls

variable (acval : Name → (Name → Nat) → AnnotTerm)

local notation "TVA" => nestedTV (V := V) nP k resSort ppsA W pins acval memberNames ψ

/-- **`CopyCtorShape` at the auxiliary lists**, at the copy
`offs (k + q₀ + i) + j` of the container `dJ`'s member `i`, constructor
`j`, of the pin group `[q₀, q₀ + kJ)`. -/
@[expose] def CopyShapeA (dJ : BlockModel V) (ψJ : Name → Nat) (Ds : List AnnotTerm)
    (_DsE : List Expr) (lpsJ : List Name) (lvlsJ : List Level) (q₀ kJ i j : Nat) : Prop :=
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
    {ψJ : Name → Nat} {Ds : List AnnotTerm} {DsE : List Expr} {lpsJ : List Name}
    {lvlsJ : List Level} {q₀ kJ i j : Nat}
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
      acval dJ ψJ Ds DsE lpsJ lvlsJ q₀ kJ i j) :
    CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
      acval' dJ ψJ Ds DsE lpsJ lvlsJ q₀ kJ i j :=
  CopyCtorShape.of_EA (TV := TVA) (targetRead acval' memberNames pins nP k ψ)
    (targetRead_congr hmem hpin) hac htgt h

section Container

variable {dJ : BlockModel V} {ψJ : Name → Nat} {Ds : List AnnotTerm} {DsE : List Expr}
  {lpsJ : List Name} {lvlsJ : List Level}

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
        acval dJ ψJ Ds DsE lpsJ lvlsJ q₀ kJ i j)
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
        acval dJ ψJ Ds DsE lpsJ lvlsJ q₀ kJ i j)
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


/-- **`hfit` at the container's MEMBER classes, AT THE WIDE WIDTH**
(task #315, Resolution 1) — `hfit_at_of_inst`'s sibling and item (1)'s
wrapper: `ofNested_hΦ_of_fit`'s hypothesis at a class `i < dJ.k`, from
the group's shape and the run's entries.

Three inputs are the wide route's own, and they are what the assembly
reads off the instance CLOSURE rather than off the group:

* `hstgt` — at a container-recursive field targeting one of the
  container's OWN pins, the block's target is the instance's image `σ`
  of that class.  This is what replaces the narrow route's entry at
  that arm: `CopyCtorShape.fit_iff_wide` reads the segment's own
  variable on both sides;
* `houtσ` — at a container-ordinary field the elimination rewrote
  (`ordF`-right), the block's target is OUTSIDE the instance, so the
  joined tuple is the block's own carrier there and the run's entry
  residue (`CopyEntryA`, `nestedPinLeaf_all`) applies verbatim;
* the BOUND on the tuple, which `fit_iff_wide` consumes exactly once,
  at the container-side spine obligation.  The container's own wide
  carrier is its EXTENDED narrow one (`BlockModel.auxLfp_eq_famAt`),
  which is the `famAt` form the container's slot reads. -/
theorem hfit_wide_mem_of_inst {env : Env} {m : EnvModel V env} {q₀ : Nat} {σ : Nat → Nat}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hw : dJ.w ψJ = resSort.eval ψ)
    (hroot : ∀ i, i < dJ.k → σ i = k + q₀ + i)
    (hu : ∀ i', i' < dJ.k → nestedU k W pins ψ (k + q₀ + i') = dJ.uM i' ψJ)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    (hidx : ∀ i, i < dJ.k → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < dJ.k → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hsh : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length →
      CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        acval dJ ψJ Ds DsE lpsJ lvlsJ q₀ dJ.k i j)
    (hent : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length →
      CopyEntryA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        dJ ψJ Ds q₀ dJ.k i j)
    (hstgt : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length → ∀ l,
      l < ((dJ.Fss i ψJ).getD j []).length → ((dJ.rss i).getD j []).getD l false = true →
      ¬ dJ.tgts i j l < dJ.k →
      (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0 = σ (dJ.tgts i j l))
    (houtσ : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length → ∀ l,
      l < ((dJ.Fss i ψJ).getD j []).length → ((dJ.rss i).getD j []).getD l false = false →
      (rss.getD (offs (k + q₀ + i) + j) []).getD l false = true →
      ¬ ∃ m, m < dJ.k + dJ.nPins ∧
        σ m = (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0) :
    ∀ Y, InTupleSpace (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) Y →
      FibreConst σ (dJ.k + dJ.nPins) Y →
      TupleLe (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) Y
        (lfpTuple (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ)) →
      ∀ i, i < dJ.k → ∀ t, t ∈ˢ dJ.idx ψJ ρJ i → ∀ j fs,
      (offs (σ i) + j < (Fss₀ ψ).length ∧ mems.getD (offs (σ i) + j) 0 = σ i ∧
        FitsFrom (rss.getD (offs (σ i) + j) []) (fun i' ρ => slotSet (resSort.eval ψ)
            (nestedU k W pins ψ ((tgtsG.getD (offs (σ i) + j) []).getD i' 0)) ρ
            (((tlss ψ).getD (offs (σ i) + j) []).getD i' [])
            (((Eiss₀ ψ).getD (offs (σ i) + j) []).getD i' [])
            (setJoin σ (dJ.k + dJ.nPins) L⁺ Y ((tgtsG.getD (offs (σ i) + j) []).getD i' 0)))
          0 ρp ((Fss₀ ψ).getD (offs (σ i) + j) []) fs ∧
        (∀ l, l < (blockIds nP ppsA ψ (σ i)).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (σ i) + j) []).getD l default)
            = projS l t))
      ↔ (j < (dJ.ctorsT dJ.pinCtors i).length ∧ dJ.ChainFitT dJ.pinCtors ψJ ρJ Y t i j fs) := by
  intro Y hY hYfc hYC i hi t _ j fs
  rw [BlockModel.ctorsT_of_mem hi, hroot i hi]
  by_cases hj : j < (dJ.ctorsM i).length
  · have hj' : (dJ.ctorsM i)[j]? = some ((dJ.ctorsM i).getD j default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    have hnI : (blockIds nP ppsA ψ (k + q₀ + i)).length = (dJ.IdsM i ψJ).length := by
      rw [hidx i hi, instTele_length]
    have hshij := hsh i hi j hj
    -- the container's own wide carrier IS its extended narrow one
    obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps i hi
    have hFa := hI.auxFunctor ψJ ρJ hρJ
    have hCeq : ∀ c, c < dJ.k + dJ.nPins →
        lfpTuple (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ) c
          = dJ.famAt ψJ ρJ (lfpTuple (resSort.eval ψ) dJ.k (dJ.idx ψJ ρJ) (dJ.Φ ψJ ρJ)) c := by
      intro c hc
      rw [← hw]
      exact dJ.auxLfp_eq_famAt hFa.1 hFa.2.2 (hI.auxCompose ψJ ρJ)
        (fun X q hq => hI.auxPinsCar ψJ ρJ X q hq) hc
    -- the three wide inputs, at this constructor
    have htgtlt : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length → ¬ dJ.tgts i j l < dJ.k →
        dJ.tgts i j l - dJ.k < dJ.nPins := hreps.tgt_pin_lt hi hj'
    have huT : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
        ((dJ.rss i).getD j []).getD l false = true →
        nestedU k W pins ψ ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0)
          = dJ.uT (dJ.tgts i j l) ψJ := by
      intro l hl hr
      by_cases hnt : dJ.tgts i j l < dJ.k
      · obtain ⟨-, htg, -, -⟩ := hshij.recF l hl hr hnt
        rw [BlockModel.uT_of_mem hnt ψJ, htg]
        exact hu _ hnt
      · obtain ⟨-, -, -, -, ⟨-, -, hv, -, -, -⟩, -, -⟩ := hshij.pinF l hl hr hnt
        rw [BlockModel.uT_of_pin hnt ψJ]
        exact hv
    have hZY : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
        ((dJ.rss i).getD j []).getD l false = true →
        setJoin σ (dJ.k + dJ.nPins) L⁺ Y ((tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0)
          = Y (dJ.tgts i j l) := by
      intro l hl hr
      have htg : (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0 = σ (dJ.tgts i j l) := by
        by_cases hnt : dJ.tgts i j l < dJ.k
        · obtain ⟨-, htg, -, -⟩ := hshij.recF l hl hr hnt
          rw [hroot _ hnt]
          exact htg
        · exact hstgt i hi j hj l hl hr hnt
      have hlt : dJ.tgts i j l < dJ.k + dJ.nPins := by
        by_cases hnt : dJ.tgts i j l < dJ.k
        · omega
        · have := htgtlt l hl hnt; omega
      rw [htg]
      exact setJoin_at_fc hYfc _ hlt
    have hYle : ∀ l, l < ((dJ.Fss i ψJ).getD j []).length →
        ((dJ.rss i).getD j []).getD l false = true → ∀ t',
        SetTheory.app (Y (dJ.tgts i j l)) t'
          ⊆ˢ SetTheory.app (dJ.famAt ψJ ρJ
              (lfpTuple (resSort.eval ψ) dJ.k (dJ.idx ψJ ρJ) (dJ.Φ ψJ ρJ)) (dJ.tgts i j l)) t' := by
      intro l hl hr t'
      have hlt : dJ.tgts i j l < dJ.k + dJ.nPins := by
        by_cases hnt : dJ.tgts i j l < dJ.k
        · omega
        · have := htgtlt l hl hnt; omega
      rw [← hCeq _ hlt]
      exact app_subset_of_famLe (hY _ hlt) (hYC _ hlt) t'
    -- the entries: at a rewritten container-ORDINARY field the joined
    -- tuple is the block's own carrier
    have hentZ : CopyEntryOrd (V := V) dJ ψJ Ds
        (fun l => (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0)
        ((tlss ψ).getD (offs (k + q₀ + i) + j) []) ((Eiss₀ ψ).getD (offs (k + q₀ + i) + j) [])
        ρp i j (k + q₀) dJ.k ((Fss₀ ψ).getD (offs (k + q₀ + i) + j) [])
        (rss.getD (offs (k + q₀ + i) + j) []) (resSort.eval ψ) (nestedU k W pins ψ)
        (setJoin σ (dJ.k + dJ.nPins) L⁺ Y) := by
      intro l hl hr' hrC hout fs₁ hl₁ hsp
      rw [setJoin_out _ _ (houtσ i hi j hj l (by rwa [hshij.len] at hl) hr' hrC)]
      exact CopyEntryOut.ord (hent i hi j hj) l hl hr' hrC hout fs₁ hl₁ hsp
    have hfit := CopyCtorShape.fit_iff_wide (TV := nestedTV nP k resSort ppsA W pins acval
        memberNames ψ) hreps hfT hPT hi hw hρJ hnI hj' hshij huT hZY hYle hentZ t fs
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

/-- **`hfit` at EVERY class of the container instance, at the wide
width** (task #315, Resolution 1): `ofNested_hΦ_of_fit`'s hypothesis,
assembled from the two halves that are not alike.

At the container's MEMBERS the run states the comparison and
`hfit_wide_mem_of_inst` proves it.  At the copies of the container's
OWN pins it does not: such a copy belongs to a group whose container is
the PIN's container `K`, not `dJ`, and `dJ`'s own record of that pin is
`K`'s constructors at `dJ`'s components — two copies of ONE container
at two instantiations, whose comparison is the two-copies transfer
(`copyTransfer_via`) and not a fact the run states about either.  That
half is `hpin`, and it is discharged where the transfer lives
(`NestedPinLeafAll.lean`), which is strictly downstream of this
module. -/
theorem hfit_wide_of_inst {env : Env} {m : EnvModel V env} {q₀ : Nat} {σ : Nat → Nat}
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hw : dJ.w ψJ = resSort.eval ψ)
    (hroot : ∀ i, i < dJ.k → σ i = k + q₀ + i)
    (hu : ∀ i', i' < dJ.k → nestedU k W pins ψ (k + q₀ + i') = dJ.uM i' ψJ)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    (hidx : ∀ i, i < dJ.k → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < dJ.k → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hsh : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length →
      CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        acval dJ ψJ Ds DsE lpsJ lvlsJ q₀ dJ.k i j)
    (hent : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length →
      CopyEntryA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        dJ ψJ Ds q₀ dJ.k i j)
    (hstgt : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length → ∀ l,
      l < ((dJ.Fss i ψJ).getD j []).length → ((dJ.rss i).getD j []).getD l false = true →
      ¬ dJ.tgts i j l < dJ.k →
      (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0 = σ (dJ.tgts i j l))
    (houtσ : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length → ∀ l,
      l < ((dJ.Fss i ψJ).getD j []).length → ((dJ.rss i).getD j []).getD l false = false →
      (rss.getD (offs (k + q₀ + i) + j) []).getD l false = true →
      ¬ ∃ m, m < dJ.k + dJ.nPins ∧
        σ m = (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0)
    (hpin : ∀ Y, InTupleSpace (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) Y →
      FibreConst σ (dJ.k + dJ.nPins) Y →
      TupleLe (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) Y
        (lfpTuple (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ)) →
      ∀ i, ¬ i < dJ.k → i < dJ.k + dJ.nPins → ∀ t, t ∈ˢ dJ.idx ψJ ρJ i → ∀ j fs,
      (offs (σ i) + j < (Fss₀ ψ).length ∧ mems.getD (offs (σ i) + j) 0 = σ i ∧
        FitsFrom (rss.getD (offs (σ i) + j) []) (fun i' ρ => slotSet (resSort.eval ψ)
            (nestedU k W pins ψ ((tgtsG.getD (offs (σ i) + j) []).getD i' 0)) ρ
            (((tlss ψ).getD (offs (σ i) + j) []).getD i' [])
            (((Eiss₀ ψ).getD (offs (σ i) + j) []).getD i' [])
            (setJoin σ (dJ.k + dJ.nPins) L⁺ Y ((tgtsG.getD (offs (σ i) + j) []).getD i' 0)))
          0 ρp ((Fss₀ ψ).getD (offs (σ i) + j) []) fs ∧
        (∀ l, l < (blockIds nP ppsA ψ (σ i)).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (σ i) + j) []).getD l default)
            = projS l t))
      ↔ (j < (dJ.ctorsT dJ.pinCtors i).length ∧ dJ.ChainFitT dJ.pinCtors ψJ ρJ Y t i j fs)) :
    ∀ Y, InTupleSpace (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) Y →
      FibreConst σ (dJ.k + dJ.nPins) Y →
      TupleLe (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) Y
        (lfpTuple (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ)) →
      ∀ i, i < dJ.k + dJ.nPins → ∀ t, t ∈ˢ dJ.idx ψJ ρJ i → ∀ j fs,
      (offs (σ i) + j < (Fss₀ ψ).length ∧ mems.getD (offs (σ i) + j) 0 = σ i ∧
        FitsFrom (rss.getD (offs (σ i) + j) []) (fun i' ρ => slotSet (resSort.eval ψ)
            (nestedU k W pins ψ ((tgtsG.getD (offs (σ i) + j) []).getD i' 0)) ρ
            (((tlss ψ).getD (offs (σ i) + j) []).getD i' [])
            (((Eiss₀ ψ).getD (offs (σ i) + j) []).getD i' [])
            (setJoin σ (dJ.k + dJ.nPins) L⁺ Y ((tgtsG.getD (offs (σ i) + j) []).getD i' 0)))
          0 ρp ((Fss₀ ψ).getD (offs (σ i) + j) []) fs ∧
        (∀ l, l < (blockIds nP ppsA ψ (σ i)).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (σ i) + j) []).getD l default)
            = projS l t))
      ↔ (j < (dJ.ctorsT dJ.pinCtors i).length ∧ dJ.ChainFitT dJ.pinCtors ψJ ρJ Y t i j fs) := by
  intro Y hY hYfc hYC i hi t ht j fs
  by_cases hm : i < dJ.k
  · exact hfit_wide_mem_of_inst acval hreps hfT hPT hw hroot hu hρJ hidx hgrp hsh hent
      hstgt houtσ Y hY hYfc hYC i hm t ht j fs
  · exact hpin Y hY hYfc hYC i hm hi t ht j fs

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
        acval dJ ψJ Ds DsE lpsJ lvlsJ q₀ kJ i j)
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

/-- **A pin's carrier at the block's carrier is its container's least
tuple, ON THE WIDE IDENTIFICATION** (task #315, Resolution 1) —
`ofNested_pin_block_of_inst`'s sibling, with no domination hypothesis,
no candidate tuple and no ordering among pins.

The container's side is read off its STORED model throughout: its wide
operator's functor laws and composition (`auxFunctor`/`auxCompose`, at
the BLOCK's sort through `hw`), its wide fibre (`auxFibre`) and its
class readers.  What the assembly supplies beyond the narrow route's
list is the instance CLOSURE `σ` — the container's members contiguous
at the group (`hroot`) and the copies of the container's own pins
wherever the worklist minted them — and the two σ-facts of
`hfit_wide_mem_of_inst`.  `hpin` is the own-pin classes' half, which
lives downstream with the two-copies transfer. -/
theorem ofNested_pin_block_of_wide_inst {env : Env} {m : EnvModel V env} {q₀ : Nat}
    {σ : Nat → Nat}
    (h : NestedLfpOk (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
      (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
      (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) ψ ρp)
    (hS : TupleLfpShape (k + pins.length) (blockIds nP ppsA ψ) mems nFs tgtsG rss (Eiss₀ ψ)
      (Fss₀ ψ) (Ess₀ ψ))
    (hseg : q₀ + dJ.k ≤ pins.length)
    (hreps : IsBlockModels m dJ) (hfT : FormersTyped m dJ ψJ) (hPT : PinsTyped m dJ ψJ)
    (hkpos : 0 < dJ.k)
    (hw : dJ.w ψJ = resSort.eval ψ)
    (hrowsσ : ∀ Y, FibreConst σ (dJ.k + dJ.nPins) (dJ.Ψaux ψJ ρJ Y))
    (hσ : ∀ i, i < dJ.k + dJ.nPins → σ i < k + pins.length)
    (hroot : ∀ i, i < dJ.k → σ i = k + q₀ + i)
    (hIsσ : ∀ i, i < dJ.k + dJ.nPins →
      idxSet (nestedU k W pins ψ (σ i)) ρp (blockIds nP ppsA ψ (σ i)) = dJ.idx ψJ ρJ i)
    (hinjJ : ∀ i j fs, dJ.injT dJ.pinCtors ψJ i j fs = injW (resSort.eval ψ) j (mkTower (fs ++ [pt])))
    (hu : ∀ i', i' < dJ.k → nestedU k W pins ψ (k + q₀ + i') = dJ.uM i' ψJ)
    (hρJ : Sat V (dJ.params ψJ).reverse ρJ)
    (hidx : ∀ i, i < dJ.k → blockIds nP ppsA ψ (k + q₀ + i) = instTele Ds 0 (dJ.IdsM i ψJ))
    (hgrp : ∀ i, i < dJ.k → ∀ j, (offs (k + q₀ + i) + j < (Fss₀ ψ).length ∧
      mems.getD (offs (k + q₀ + i) + j) 0 = k + q₀ + i) ↔ j < (dJ.ctorsM i).length)
    (hsh : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length →
      CopyShapeA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (memberNames := memberNames) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        acval dJ ψJ Ds DsE lpsJ lvlsJ q₀ dJ.k i j)
    (hent : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length →
      CopyEntryA (V := V) (nP := nP) (k := k) (resSort := resSort) (ppsA := ppsA) (W := W)
        (pins := pins) (offs := offs) (mems := mems) (nFs := nFs) (tgtsG := tgtsG) (rss := rss)
        (tlss := tlss) (Eiss₀ := Eiss₀) (Fss₀ := Fss₀) (Ess₀ := Ess₀) (ψ := ψ) (ρp := ρp)
        dJ ψJ Ds q₀ dJ.k i j)
    (hstgt : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length → ∀ l,
      l < ((dJ.Fss i ψJ).getD j []).length → ((dJ.rss i).getD j []).getD l false = true →
      ¬ dJ.tgts i j l < dJ.k →
      (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0 = σ (dJ.tgts i j l))
    (houtσ : ∀ i, i < dJ.k → ∀ j, j < (dJ.ctorsM i).length → ∀ l,
      l < ((dJ.Fss i ψJ).getD j []).length → ((dJ.rss i).getD j []).getD l false = false →
      (rss.getD (offs (k + q₀ + i) + j) []).getD l false = true →
      ¬ ∃ mm, mm < dJ.k + dJ.nPins ∧
        σ mm = (tgtsG.getD (offs (k + q₀ + i) + j) []).getD l 0)
    (hpin : ∀ Y, InTupleSpace (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) Y →
      FibreConst σ (dJ.k + dJ.nPins) Y →
      TupleLe (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) Y
        (lfpTuple (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ)) →
      ∀ i, ¬ i < dJ.k → i < dJ.k + dJ.nPins → ∀ t, t ∈ˢ dJ.idx ψJ ρJ i → ∀ j fs,
      (offs (σ i) + j < (Fss₀ ψ).length ∧ mems.getD (offs (σ i) + j) 0 = σ i ∧
        FitsFrom (rss.getD (offs (σ i) + j) []) (fun i' ρ => slotSet (resSort.eval ψ)
            (nestedU k W pins ψ ((tgtsG.getD (offs (σ i) + j) []).getD i' 0)) ρ
            (((tlss ψ).getD (offs (σ i) + j) []).getD i' [])
            (((Eiss₀ ψ).getD (offs (σ i) + j) []).getD i' [])
            (setJoin σ (dJ.k + dJ.nPins) L⁺ Y ((tgtsG.getD (offs (σ i) + j) []).getD i' 0)))
          0 ρp ((Fss₀ ψ).getD (offs (σ i) + j) []) fs ∧
        (∀ l, l < (blockIds nP ppsA ψ (σ i)).length →
          interp V (consList fs ρp) (((Ess₀ ψ).getD (offs (σ i) + j) []).getD l default)
            = projS l t))
      ↔ (j < (dJ.ctorsT dJ.pinCtors i).length ∧ dJ.ChainFitT dJ.pinCtors ψJ ρJ Y t i j fs))
    {i : Nat} (hi : i < dJ.k) :
    (D).pinCar ψ ρp (lfpTuple ((D).w ψ) k ((D).idx ψ ρp) ((D).Φ ψ ρp)) (q₀ + i)
      = lfpTuple (dJ.w ψJ) dJ.k (dJ.idx ψJ ρJ) (dJ.Φ ψJ ρJ) i := by
  obtain ⟨cvT, cvR, mI, rP, rules, hI⟩ := hreps 0 hkpos
  have hw' : (D).w ψ = dJ.w ψJ := hw.symm
  have hFa := hI.auxFunctor ψJ ρJ hρJ
  have hIs : ∀ i, i < dJ.k + dJ.nPins → (D).idx ψ ρp (σ i) = dJ.idx ψJ ρJ i := hIsσ
  refine (ofNested_pin_block_of_wide h hseg ?_ ?_ ?_ ?_ hrowsσ hσ hroot hIs ?_ hi).trans
    (by rw [hw'])
  · rw [hw']; exact hFa.1
  · rw [hw']; exact hFa.2.1
  · rw [hw']; exact hFa.2.2
  · rw [hw']; exact hI.auxCompose ψJ ρJ
  · refine ofNested_hΦ_of_fit h hS hσ hIs ?_
      (nCJ := fun i => (dJ.ctorsT dJ.pinCtors i).length)
      (FitJ := fun Y t i j fs => dJ.ChainFitT dJ.pinCtors ψJ ρJ Y t i j fs) hinjJ
      (C := lfpTuple (resSort.eval ψ) (dJ.k + dJ.nPins) (dJ.idx ψJ ρJ) (dJ.Ψaux ψJ ρJ)) ?_ ?_
    · show MapsTuple (resSort.eval ψ) _ _ _
      rw [← hw]; exact hFa.2.1
    · intro Y hY c hc t ht x
      exact hI.auxFibre ψJ ρJ hρJ Y (by rw [hw]; exact hY) c hc t ht x
    · exact hfit_wide_of_inst acval hreps hfT hPT hw hroot hu hρJ hidx hgrp hsh hent
        hstgt houtσ hpin

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
        acval dJ ψJ Ds DsE lpsJ lvlsJ q₀ kJ i j)
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
