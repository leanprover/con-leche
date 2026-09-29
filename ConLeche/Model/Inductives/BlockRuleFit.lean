module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecOpenerRead
import ConLeche.Model.Annot.BitInst
public import ConLeche.Model.Inductives.BlockRecPreRun

public section

/-!
# The per-pair rule obligation's FIT and FIRED SPINE

`BlockRuleDataB` (`BlockRecData.lean`) is the seam's rule-side
obligation at ONE environment and ONE valuation: five statements about
one (recursor, constructor) pair, all at the BASE frame `ρ`.  This
file discharges three of them — the first conjunct (the prefix and the
fields FIT the rule's domains), the second (the INDEX EXPRESSIONS read
to the recursor's own index arguments) and the third (the FIRED SPINE
reads to the constructor at its own parameters) — and the three are
one piece of work, because all three need the same fact:

> the constructor's field values fit the constructor's field domains
> **at the RECURSOR's parameter frame**, not only at the
> constructor's own.

The iota rule is `paramsBlind`: the kernel fires it on a syntactic
constructor head and takes the parameters from the RECURSOR's spine
and the fields from the CONSTRUCTOR's, comparing the two parameter
spines nowhere (`Model/Annot/Laws.lean`, and `recFireComparands` at a
`.plain` rule copies the level arguments and drops the comparison).
So nothing syntactic ties the two spines, and the model must pay for
the tie.  It pays with the MAJOR PREMISE: `BlockRuleDataB` hands a
`TeleFitPA` of the recursor's own type, whose last entry is the major,
so the major LIES IN the member's former applied to the RECURSOR's
parameters and indices — which is the carrier
(`BlockModelAt.leaf`), and an element of the carrier IS an injection
of a spine fitting one of the component's constructors THERE
(`blockCarrier_case`).  At a `Type`-valued block that decomposition is
unique (`blockCarrier_case_unique`), so the spine it produces is the
constructor's own field spine — read at the recursor's parameters.

The parts:

* **§1 the frame transport.**  The bridge `blockRecSpF`
  (`BlockRecPreRun.lean`) concludes at the CHAIN frame over `K` binders, with `K` free: the chain is there
  because the KIT runs under it.  At `K = 0` the chain frame IS the
  base frame and `liftDomsK 0` is the identity, both unconditionally,
  so the base-frame instances cost two `simp` lemmas and no
  boundedness premise;
* **§2 the major premise's decomposition** — `hps`, the index tuple's
  membership and the field spine's stored fit, all at the recursor's
  parameter frame, out of `BlockRecSplitOne` and the constructor's
  reading;
* **§3 the fit and the fired spine**, and **§3b the index reading**,
  which is the same stored fit's index clause read backwards.

§4 and §5 give the two `d.w ψ = 0` counterexamples: the fit and the
index reading are BOTH false at a `Prop`-valued block with `ℓ = 0`.
The contract is guarded by `ℓ ≠ 0`; the `d.w ψ = 0` case under that
guard is §2b.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}
  {R : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}

/-! ## 1. The frame transport: a ZERO chain is no chain -/

/-! ## 2. The major premise's decomposition

The iota rule compares no parameters, so nothing SYNTACTIC ties the
recursor's parameter spine `xs.take nP` to the constructor's
`ys.take nP`.  What ties them is the MAJOR PREMISE: the contract's
`hfitR` puts `mkAppN Ca ys` in the recursor type's major domain, which
is the eliminated member's former applied to the RECURSOR's parameters
and indices — the carrier (`BlockModelAt.leaf`) — and an element of
the carrier IS an injection of a spine fitting one of the component's
constructors at THAT frame (`blockCarrier_case`).  The constructor's
own reading says the same element is `d.inj ψ mm j fs` at its own
parameters, and at a `Type`-valued block `mkInj` identifies the two
decompositions.

**This is `d.w ψ ≠ 0` content, and the restriction is not an
artefact** — see the counterexample in §4.  §2b is the same fact at
`d.w ψ = 0`, by a different argument, under the contract's `ℓ ≠ 0`
guard. -/

/-- A fit splits at a cutoff: the prefix fits the domains' prefix and
the suffix fits the rest at the prefix's own frame. -/
theorem spineFit_split {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {n : Nat} (hn : n ≤ Fs.length) :
    SpineFit ρ (Fs.take n) (as.take n) ∧
      SpineFit (consList (as.take n) ρ) (Fs.drop n) (as.drop n) := by
  have h' : SpineFit ρ (Fs.take n ++ Fs.drop n) as := by
    rw [List.take_append_drop]; exact h
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_inv h'
  have hl : as₁.length = n := by
    rw [h1.length_eq, List.length_take]; omega
  have ht : as.take n = as₁ := by
    rw [heq, ← hl]; simp
  have hd : as.drop n = as₂ := by
    rw [heq, ← hl]; simp
  rw [ht, hd]
  exact ⟨h1, h2⟩

variable {envC : Env} {mpC : EnvModelM V μ envC} {names lps : List Name} {d : BlockData V}

/-- **The constructor's parameter spine fits the BLOCK's parameter
telescope**, and its field spine fits the field domains at its own
parameter frame — the two halves of the contract's `hfitC`, once the
constructor's reading is `mkPisAV (d.dsF …)`.

`hparamsC` is the constructors' stage's own clause (an argument of
`blockModelAt_of_records`): the block's parameter telescope and the
constructor's first `nP` binders are satisfied by the same frames. -/
theorem blockCtorSpine_split {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA) {ψ : Name → Nat} {ρ : Nat → V}
    {ys : List AnnotTerm}
    (hdsLen : (d.dsF mm j ψ).length = d.nP + cA.2)
    (hfitC : SpineFit ρ ((d.dsF mm j ψ).map (·.2.2)) (ys.map (interp V ρ)))
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF mm j ψ).take d.nP).map (·.2.2)).reverse σ)
    (hlenP : (d.params ψ).length = d.nP) :
    SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)) ∧
      SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
        ((d.Fss mm ψ).getD j []) ((ys.drop d.nP).map (interp V ρ)) := by
  have hle : d.nP ≤ ((d.dsF mm j ψ).map (·.2.2)).length := by
    rw [List.length_map, hdsLen]; omega
  obtain ⟨h1, h2⟩ := spineFit_split hfitC hle
  simp only [← List.map_take, ← List.map_drop] at h1 h2
  have hlenD : (((d.dsF mm j ψ).take d.nP).map (·.2.2)).length = d.nP := by
    rw [List.length_map, List.length_take, hdsLen]; omega
  refine ⟨?_, ?_⟩
  · refine (spineFit_iff_of_sat_iff (by rw [hlenP, hlenD]) hparamsC ρ _ ?_).mpr h1
    rw [h1.length_eq, hlenD, hlenP]
  · have hF : (d.Fss mm ψ).getD j [] = ((d.dsF mm j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hF]
    exact h2

/-- **THE SHARED FACT of the fit's FIELD half and of `mk`**: the
constructor's field values fit its STORED field domains AT THE
RECURSOR's parameter frame, at the index tuple the major names.

Nothing syntactic produces this — the rule is `paramsBlind`.  What
produces it is the MAJOR PREMISE, in four moves:

1. the major is the constructor at ITS OWN parameters, so its value is
   `d.inj ψ mm j fs` (`BlockModelAt.ctor`, at `hqs`/`hfq`);
2. the contract's `hfitR` puts that value in the eliminated member's
   former applied to the RECURSOR's parameters and indices, which is
   the carrier at the recursor's parameter frame
   (`BlockModelAt.leaf`);
3. an element of the carrier IS an injection of a spine fitting one of
   the component's constructors AT THAT FRAME (`blockCarrier_case`);
4. at `d.w ψ ≠ 0` the injections are injective (`BlockModelAt.mkInj`),
   so that spine is `fs` and that constructor is `j`.

`hw` is not a convenience: at a `Prop`-valued block step 4 is FALSE
and so is the conclusion — see §4. -/
theorem blockRuleStoredFit_run (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hfind : envC.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2))
    (hmemk : mm < d.k) {ψ ψj : Name → Nat}
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q) (hw : d.w ψ ≠ 0)
    {ρ : Nat → V} {ps is : List V} {ys : List AnnotTerm}
    (hps : SpineFit ρ (d.params ψ) ps)
    (hidx : SpineFit (consList ps ρ) (d.IdsM mm ψ) is)
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss mm ψ).getD j []) ((ys.drop d.nP).map (interp V ρ)))
    (hmaj : interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys)
      ∈ˢ (ps ++ is).foldl app (interp V ρ (mpC.base2.acval (d.memberName mm) ψ))) :
    d.StoredFit ψ (consList ps ρ) (d.tup ψ mm is) mm j ((ys.drop d.nP).map (interp V ρ)) := by
  have hmN : mm < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : j < (d.ctorsM mm).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hacv : mpC.base2.acval cA.1.name ψj = mpC.base2.acval cA.1.name ψ :=
    mpC.base2.acval_params cA.1.name _ hfind ψj ψ hlv
  have hval : interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys)
      = d.inj ψ mm j ((ys.drop d.nP).map (interp V ρ)) := by
    rw [hacv, interp_mkAppN_foldl,
      show ys.map (interp V ρ)
          = (ys.take d.nP).map (interp V ρ) ++ (ys.drop d.nP).map (interp V ρ) from by
        rw [← List.map_append, List.take_append_drop]]
    exact hM.ctor mm hmN j cA hcj ψ ρ _ _ hqs hfq
  rw [hM.leaf mm hmemk ψ ρ ps is hps hidx, hval] at hmaj
  have ht : d.tup ψ mm is ∈ˢ d.idx ψ (consList ps ρ) mm := tupW_mem hidx
  obtain ⟨j', fs', hfit', heq⟩ :=
    blockCarrier_case hM (d.satOfSpine hps) hmN ht hmaj
  obtain ⟨rfl, rfl⟩ := hM.mkInj ψ hw mm hmN j _ j' fs' hjl hfit'.1
    hfq.length_eq hfit'.length_eq heq
  exact hfit'

/-! ## 3. The two conjuncts -/

variable {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-! ### 2b. THE SQUASH ARM — the same stored fit at `d.w ψ = 0`

At a `Prop`-valued block `mkInj` is FALSE (`BlockModelAt.mkZero`: every
injection is the point), so §2's step 4 has no analogue and the
decomposition `blockCarrier_case` hands back is *some* constructor's
spine, not this one's.  What replaces it is the SUBSINGLETON
criterion, and it is available exactly where the guard that makes the
region non-empty has fired: with `ℓ ≠ 0` and `d.w ψ = 0` the
large-elimination counting guard (`blockLargeElimAllowed`) forces the
block to declare the generated large shape and to have at most one
constructor — so `j' = j` needs no injectivity, and
`CtorDataI.srcProp` (keyed on that same declared shape) says every
field that is not an index source is a proposition.

Then `srcVals_of_fit` at BOTH frames identifies both spines with the
source spine: the recursor's frame reads `fs'` (the stored fit's own
index clause, retracted by `projS_tupW`), the constructor's frame
reads this rule's own fields, and the two index lists are the same by
the rule's INDEX PIN, which the contract's telescope already carries.
`srcProp` is parameter-generic by statement, so ONE instance serves
both frames.

**Three premises come from elsewhere**: the counting guard's two
facts, `hlarge` and `hct1`, are the KERNEL's (in the same
`ℓ ≠ 0 → d.w ψ = 0 → …` spelling as the dispatch's `hK1`, the same
guard's one-member half), and `hpin` is the rule's index pin in the
model's currency. -/

/-- **The subsingleton criterion at one constructor**, from the
constructors' stage's own per-field clause: with the block's declared
large shape and a `Prop` result, a field that no index expression
sources is a truth value — at EVERY frame satisfying the
constructor's parameter domains, which is why one instance serves the
recursor's parameter frame and the constructor's alike. -/
theorem blockCtorFieldProp {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    (hlarge : d.large = true) {ψ : Name → Nat} (hw : d.w ψ = 0)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF mm j ψ).take d.nP).map (·.2.2)).reverse σ)
    {ρp : Nat → V} (hsat : Sat V (d.params ψ).reverse ρp) :
    ∀ q, q < ((d.Fss mm ψ).getD j []).length →
      srcOfEs ((d.Ess mm ψ).getD j []) ((d.Fss mm ψ).getD j []).length q = none →
      ∀ fs : List V, SpineFit ρp (((d.Fss mm ψ).getD j []).take q) fs →
        interp V (consList fs ρp) (((d.Fss mm ψ).getD j []).getD q default)
          ∈ˢ (univZero : V) := by
  obtain ⟨-, -, hCD⟩ := hcf
  have hFssD : (d.Fss mm ψ).getD j [] = ((d.dsF mm j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hEssD : (d.Ess mm ψ).getD j [] = d.esF mm j ψ := essOfR_fixCtorDataList_getD hcj
  intro q hq hsrc fs hfs
  rw [hFssD] at hq hfs ⊢
  rw [hFssD, hEssD] at hsrc
  have hbnd := hCD.srcProp hlarge ψ hw ρp (hparamsC ρp |>.mp hsat)
  have hlenF : (((d.dsF mm j ψ).drop d.nP).map (·.2.2)).length = cA.2 := by
    rw [List.length_map, List.length_drop, hCD.len ψ]; omega
  rw [hlenF] at hq hsrc
  obtain ⟨s', hs⟩ : ∃ s', (d.srcsF mm j)[q]? = some s' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hCD.srcLen]; exact hq)⟩
  have hsn : s' = none := by
    cases s' with
    | none => rfl
    | some l => exact absurd (hCD.srcIdx q l hs ψ) fun hE => srcOfEs_none hsrc hE
  subst hsn
  rw [← univ_zero]
  exact fieldsBoundSrc_at hbnd hs hfs (by rw [hlenF]; exact hq)

/-- **§2's fact at `d.w ψ = 0`** — the same stored fit, by the
subsingleton criterion instead of by injectivity.  See the section
note for the premises. -/
theorem blockRuleStoredFit_sq (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    (hmemk : mm < d.k) {ψ ψj : Name → Nat}
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q) (hw : d.w ψ = 0)
    (hlarge : d.large = true) (hct1 : (d.ctorsM mm).length ≤ 1)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF mm j ψ).take d.nP).map (·.2.2)).reverse σ)
    {ρ : Nat → V} {ps is : List V} {ys : List AnnotTerm}
    (hps : SpineFit ρ (d.params ψ) ps)
    (hidx : SpineFit (consList ps ρ) (d.IdsM mm ψ) is)
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss mm ψ).getD j []) ((ys.drop d.nP).map (interp V ρ)))
    (hpin : ((d.Ess mm ψ).getD j []).map
        (interp V (consList ((ys.drop d.nP).map (interp V ρ))
          (consList ((ys.take d.nP).map (interp V ρ)) ρ))) = is)
    (hmaj : interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys)
      ∈ˢ (ps ++ is).foldl app (interp V ρ (mpC.base2.acval (d.memberName mm) ψ))) :
    d.StoredFit ψ (consList ps ρ) (d.tup ψ mm is) mm j ((ys.drop d.nP).map (interp V ρ)) := by
  have hmN : mm < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : j < (d.ctorsM mm).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hacv : mpC.base2.acval cA.1.name ψj = mpC.base2.acval cA.1.name ψ :=
    mpC.base2.acval_params cA.1.name _ hcf.1 ψj ψ hlv
  have hval : interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys)
      = d.inj ψ mm j ((ys.drop d.nP).map (interp V ρ)) := by
    rw [hacv, interp_mkAppN_foldl,
      show ys.map (interp V ρ)
          = (ys.take d.nP).map (interp V ρ) ++ (ys.drop d.nP).map (interp V ρ) from by
        rw [← List.map_append, List.take_append_drop]]
    exact hM.ctor mm hmN j cA hcj ψ ρ _ _ hqs hfq
  rw [hM.leaf mm hmemk ψ ρ ps is hps hidx, hval] at hmaj
  have ht : d.tup ψ mm is ∈ˢ d.idx ψ (consList ps ρ) mm := tupW_mem hidx
  obtain ⟨j', fs', hfit', -⟩ :=
    blockCarrier_case hM (d.satOfSpine hps) hmN ht hmaj
  rw [show j' = j from by have := hfit'.1; omega] at hfit'
  -- the recursor side: the decomposition's spine
  have hspR := hfit'.2.1
  -- the index values, at the recursor's frame
  have hIdxOk := hM.idxOk ψ _ (d.satOfSpine hps) mm hmN
  have hEsLen : ((d.Ess mm ψ).getD j []).length = (d.IdsM mm ψ).length := by
    have hq := (hM.resIdxFit ψ _ (d.satOfSpine hps) mm hmN j hjl _ hspR).length_eq
    rwa [List.length_map] at hq
  have hidxR : ((d.Ess mm ψ).getD j []).map (interp V (consList fs' (consList ps ρ))) = is := by
    refine List.ext_getElem (by rw [List.length_map, hEsLen, hidx.length_eq])
      fun l h1 h2 => ?_
    rw [List.length_map, hEsLen] at h1
    have hlE : l < ((d.Ess mm ψ).getD j []).length := by rw [hEsLen]; exact h1
    have hstep := hfit'.2.2 l h1
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlE, Option.getD_some] at hstep
    rw [List.getElem_map, hstep, BlockData.tup, projS_tupW hIdxOk hidx h1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  -- the subsingleton criterion, ONE instance per frame
  have hpropR := blockCtorFieldProp hcj hcf hlarge hw hparamsC (d.satOfSpine hps)
  have hpropC := blockCtorFieldProp hcj hcf hlarge hw hparamsC (d.satOfSpine hqs)
  have hfsR := srcVals_of_fit hpropR hspR hidxR
  have hfsC := srcVals_of_fit hpropC hfq hpin
  rw [hfsC, ← hfsR]
  exact hfit'

/-- **THE INDEX PIN, in the model's currency** — `IotaIndexPin`'s
content read through the constructor's own reading.

The pin is a statement about the residual `restC` of the
constructor's telescope at the FIRED spine; the squash arm (§2b)
needs it about the datum's index readings `d.Ess`.  The two are the
same fact once the residual is named: the constructor's type reads as
`mkPisAV (dsF …) (ctorBodyAVI …)`, so the residual at `ys` is the
applied former's `instSeq`, and `mkAppN`'s injectivity splits its
arguments into the `nP` parameter variables and the index readings —
whose instantiation at `ys` is exactly their reading at the
constructor's own frame (`interp_instSeq`).

This is `FixKit.lean`'s `hpin` at the block datum's spellings,
and it needs no new run fact: the length side condition `mI - rP` is
the recursor's own index-argument count, which the contract's
telescope fixes through the major premise's split.

**The `w`-guard does not appear here.**  The pin is available at
every block; it is only the SQUASH arm that reads it. -/
theorem blockRuleIdxPin_run {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    {ψ ψj : Name → Nat} (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    {ρ : Nat → V} {ys xs : List AnnotTerm} {ctorTy restC : AnnotTerm} {mI rP : Nat}
    (hys : ys.length = d.nP + cA.2) (hxl : xs.length = mI) (hrP : rP ≤ mI)
    (hnI : (d.esF mm j ψ).length = mI - rP)
    (hctorRead : denoteMeta mpC.base2.acval envC ψj 0 cA.1.type = some ctorTy)
    (hfitC : TeleFitPA V ρ ctorTy ys restC)
    (hpinC : IotaIndexPin (V := V) ρ restC d.nP mI rP xs) :
    ((d.Ess mm ψ).getD j []).map
        (interp V (consList ((ys.drop d.nP).map (interp V ρ))
          (consList ((ys.take d.nP).map (interp V ρ)) ρ)))
      = (xs.drop rP).map (interp V ρ) := by
  obtain ⟨-, -, hD⟩ := hcf
  obtain rfl := Option.some.inj (hctorRead.symm.trans (hD.read ψj))
  have hes : d.esF mm j ψj = d.esF mm j ψ := (hD.params ψj ψ hlv).2
  have hEssD : (d.Ess mm ψ).getD j [] = d.esF mm j ψ := essOfR_fixCtorDataList_getD hcj
  have hframe : consList ((ys.drop d.nP).map (interp V ρ))
      (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      = consList (ys.map (interp V ρ)) ρ := by
    rw [← consList_append, ← List.map_append, List.take_append_drop]
  rw [hEssD, hframe]
  -- the residual, named
  have hteleC := piTeleAV_mkPisAV (d.dsF mm j ψj)
    (ctorBodyAVI mpC.base2 (d.memberName mm) d.nP cA.2 ψj (d.esF mm j ψj))
  rw [hD.len ψj] at hteleC
  have hrest := teleFitPA_rest_eq (d.nP + cA.2) hteleC (by rw [hys]) hfitC
  obtain ⟨Ha, cargsa, hrestEq, hcarLen, hcarInterp⟩ := hpinC
  -- the residual's arguments are the parameter variables and the index readings
  have hrest2 : AnnotTerm.mkAppN Ha cargsa
      = AnnotTerm.mkAppN
          (ConLeche.Model.AnnotTerm.instSeq ys (d.nP + cA.2 - 1)
            (mpC.base2.acval (d.memberName mm) ψj))
          ((paramBvars d.nP cA.2 ++ d.esF mm j ψj).map
            (ConLeche.Model.AnnotTerm.instSeq ys (d.nP + cA.2 - 1))) := by
    rw [← hrestEq, hrest]
    unfold ctorBodyAVI
    rw [instSeqAV_mkAppN]
  have hlenE : (d.esF mm j ψj).length = mI - rP := by rw [hes]; exact hnI
  refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_drop, hxl,
    ← hes, hlenE]) fun i h1 h2 => ?_
  rw [List.length_map, ← hes, hlenE] at h1
  -- at an index argument the pin's own length clause is the second disjunct
  have hcarLen' : cargsa.length = d.nP + (mI - rP) := by
    rcases hcarLen with hcase | hq
    · omega
    · exact hq
  obtain ⟨-, hcargs⟩ := AnnotTerm.mkAppN_inj hrest2
    (by rw [hcarLen', List.length_map, List.length_append, paramBvars, List.length_map,
      List.length_range, hlenE])
  have hcel : cargsa.getD (d.nP + i) default
      = ConLeche.Model.AnnotTerm.instSeq ys (d.nP + cA.2 - 1) ((d.esF mm j ψj).getD i default) := by
    have hq := congrArg (fun l => l[d.nP + i]?) hcargs
    simp only [List.getElem?_map,
      List.getElem?_append_right
        (show (paramBvars d.nP cA.2).length ≤ d.nP + i by
          rw [paramBvars, List.length_map, List.length_range]; omega),
      show (paramBvars d.nP cA.2).length = d.nP from by
        rw [paramBvars, List.length_map, List.length_range],
      Nat.add_sub_cancel_left] at hq
    rw [List.getD_eq_getElem?_getD, hq, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hlenE]; exact h1), Option.map_some, Option.getD_some,
      Option.getD_some]
  have hcar := hcarInterp i (by omega)
  rw [hcel, show d.nP + cA.2 - 1 = ys.length - 1 from by rw [hys], interp_instSeq] at hcar
  rw [List.getElem_map, List.getElem_map, List.getElem_drop,
    show (d.esF mm j ψ)[i] = (d.esF mm j ψ).getD i default from by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hnI]; exact h1)]; rfl,
    show xs[rP + i] = xs.getD (rP + i) default from by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl,
    ← hes, ← hcar]
  unfold chain
  rw [consN_eq_consList]

/-! ### 2c. THE LIFT — the criterion as a STANDALONE producer

§2b's arm identifies the field spine with the SOURCE spine inside its
own proof.  The graph kit's `huniq` at `w = 0, ℓ ≠ 0` asks for that
identification on its own (`blockGraphUniq_run`, `BlockRecGraph.lean`:
two decodings of one major have the same fields), and this section is
the lift: the subsingleton criterion (`blockCtorFieldProp`) and
`srcVals_of_fit` at an ARBITRARY index tuple and an arbitrary stored-fit
spine instead of at the rule's own. -/

/-- **THE LIFT** — the subsingleton criterion as a standalone
producer: at a `Prop`-valued block with the declared large shape, a
spine fitting the lone constructor as stored IS the source spine of
the index tuple.

`srcs` is `srcList` at the constructor's own index readings, the shape
`srcVals_of_fit` produces. -/
theorem blockStoredFit_srcVals_zero (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    (hlarge : d.large = true) {ψ : Name → Nat} (hw : d.w ψ = 0)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF mm j ψ).take d.nP).map (·.2.2)).reverse σ)
    (hlenIds : (d.IdsM mm ψ).length = d.nIdxAt mm)
    {ρ : Nat → V} {ps : List V} (hps : SpineFit ρ (d.params ψ) ps)
    (hcN : mm < d.N)
    {t : V} (ht : t ∈ˢ d.idx ψ (consList ps ρ) mm)
    {fs : List V} (hfit : d.StoredFit ψ (consList ps ρ) t mm j fs) :
    fs = srcVals (isOfW (d.uM mm ψ) (d.nIdxAt mm) t)
      (srcList ((d.Ess mm ψ).getD j []) ((d.Fss mm ψ).getD j []).length) := by
  have hIdxOk := hM.idxOk ψ _ (d.satOfSpine hps) mm hcN
  have hEsLen : ((d.Ess mm ψ).getD j []).length = (d.IdsM mm ψ).length := by
    obtain ⟨-, -, hCD⟩ := hcf
    have hEssD : (d.Ess mm ψ).getD j [] = d.esF mm j ψ := essOfR_fixCtorDataList_getD hcj
    rw [hEssD, hCD.lenE ψ, hlenIds]
  have ht' : t ∈ˢ idxSet (d.uM mm ψ) (consList ps ρ) (d.IdsM mm ψ) := ht
  obtain ⟨is, hisp, rfl⟩ := mem_idxSet_elim ht'
  have hsp := hfit.2.1
  have hidx : idxValsAt (consList ps ρ) ((d.Ess mm ψ).getD j []) fs = is := by
    show ((d.Ess mm ψ).getD j []).map (interp V (consList fs (consList ps ρ))) = is
    refine List.ext_getElem (by rw [List.length_map, hEsLen, hisp.length_eq])
      fun l h1 h2 => ?_
    rw [List.length_map, hEsLen] at h1
    have hstep := hfit.2.2 l h1
    rw [List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [hEsLen]; exact h1), Option.getD_some] at hstep
    rw [List.getElem_map, hstep, projS_tupW hIdxOk hisp h1,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
  have hprop := blockCtorFieldProp hcj hcf hlarge hw hparamsC (d.satOfSpine hps)
  rw [show isOfW (d.uM mm ψ) (d.nIdxAt mm) (tupW (d.uM mm ψ) is) = is from by
    rw [← hlenIds]; exact isOfW_tupW hIdxOk hisp]
  exact srcVals_of_fit hprop hsp hidx

/-- **§2's fact at EITHER regime** — the guard's one case distinction.
At `d.w ψ ≠ 0` it is §2 (injectivity); at `d.w ψ = 0` it is §2b (the
subsingleton criterion), whose three extra facts are asked for only
there. -/
theorem blockRuleStoredFit_any (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    (hmemk : mm < d.k) {ψ ψj : Name → Nat}
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    (hlarge : d.w ψ = 0 → d.large = true)
    (hct1 : d.w ψ = 0 → (d.ctorsM mm).length ≤ 1)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF mm j ψ).take d.nP).map (·.2.2)).reverse σ)
    {ρ : Nat → V} {ps is : List V} {ys : List AnnotTerm}
    (hps : SpineFit ρ (d.params ψ) ps)
    (hidx : SpineFit (consList ps ρ) (d.IdsM mm ψ) is)
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss mm ψ).getD j []) ((ys.drop d.nP).map (interp V ρ)))
    (hpin : d.w ψ = 0 →
      ((d.Ess mm ψ).getD j []).map
        (interp V (consList ((ys.drop d.nP).map (interp V ρ))
          (consList ((ys.take d.nP).map (interp V ρ)) ρ))) = is)
    (hmaj : interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys)
      ∈ˢ (ps ++ is).foldl app (interp V ρ (mpC.base2.acval (d.memberName mm) ψ))) :
    d.StoredFit ψ (consList ps ρ) (d.tup ψ mm is) mm j ((ys.drop d.nP).map (interp V ρ)) := by
  by_cases hw : d.w ψ = 0
  · exact blockRuleStoredFit_sq hM hcj hcf hmemk hlv hw (hlarge hw) (hct1 hw) hparamsC
      hps hidx hqs hfq (hpin hw) hmaj
  · exact blockRuleStoredFit_run hM hcj hcf.1 hmemk hlv hw hps hidx hqs hfq hmaj

/-- **The major's VALUE**: the constructor applied to its own
parameters and fields is the block's injection.  `BlockModelAt.ctor`
at the constructor's own parameter frame, with the level arguments
crossed by the leaf's own parameter locality (`acval_params`). -/
theorem blockCtorMajor_value (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hfind : envC.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2))
    (hcN : mm < d.N) {ψ ψj : Name → Nat}
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    {ρ : Nat → V} {ys : List AnnotTerm}
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss mm ψ).getD j []) ((ys.drop d.nP).map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys)
      = d.inj ψ mm j ((ys.drop d.nP).map (interp V ρ)) := by
  rw [mpC.base2.acval_params cA.1.name _ hfind ψj ψ hlv, interp_mkAppN_foldl,
    show ys.map (interp V ρ)
        = (ys.take d.nP).map (interp V ρ) ++ (ys.drop d.nP).map (interp V ρ) from by
      rw [← List.map_append, List.take_append_drop]]
  exact hM.ctor mm hcN j cA hcj ψ ρ _ _ hqs hfq

/-! ## 3b. The three DATA conjuncts -/

/-! ## 3c. The three conjuncts' OWN premises, produced

`blockRuleRows_run` takes `hlv` (the constructor's level assignment agrees with the
recursor's on the block's parameters) and `hqs`/`hfq` (the
constructor's parameter and field spines fit).  Both are
consequences of premises `BlockRuleDataB` already hands — `hψ` for the
first, `hfitC` for the other two — and are produced here. -/

/-- **`hlv` at the contract's own `hψ`.**  A block rule is `.plain`,
so `recFireComparands` copies the recursor's level arguments
(`recFireComparands_plain`), and the contract's level premise becomes
`substFn_agree_of_comparand`'s comparand form. -/
theorem blockRuleLevelAgree {φ : Name → Nat} {lps lpsR : List Name} {us usj : List Level}
    {rl : ConLeche.RecRule} {rP : Nat} (hplain : ConLeche.RecRule.fire rl = .plain)
    (hψ : Level.substFn φ lps usj
      = Level.substFn φ lps (ConLeche.recFireComparands rl lpsR us lps [] rP).1) :
    ∀ q ∈ lps, Level.substFn φ lps usj q = Level.substFn φ lpsR us q :=
  substFn_agree_of_comparand (by rw [hψ, recFireComparands_plain hplain])

/-- **`hqs` and `hfq` at the contract's own `hfitC`.**

`CtorDataI.read` says the constructor's type reads as the Π-tower over
`d.dsF`, so the contract's `ctorTy` IS that tower;
`spineFit_of_teleFitPA` turns a fit of a tower into a fit of its
domains; `CtorDataI.params` moves the domains from the constructor's
own level assignment `ψj` to the recursor's `ψ` (which is exactly what
`hlv` says); and §2's `blockCtorSpine_split` splits the result at
`d.nP`. -/
theorem blockRuleCtorFit_run {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    {ψ ψj : Name → Nat} (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    (hlenP : (d.params ψ).length = d.nP)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF mm j ψ).take d.nP).map (·.2.2)).reverse σ)
    {ρ : Nat → V} {ys : List AnnotTerm} {ctorTy restC : AnnotTerm}
    (hys : ys.length = d.nP + cA.2)
    (hctorRead : denoteMeta mpC.base2.acval envC ψj 0 cA.1.type = some ctorTy)
    (hfitC : TeleFitPA V ρ ctorTy ys restC) :
    SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)) ∧
      SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
        ((d.Fss mm ψ).getD j []) ((ys.drop d.nP).map (interp V ρ)) := by
  obtain ⟨-, -, hD⟩ := hcf
  obtain rfl := Option.some.inj (hctorRead.symm.trans (hD.read ψj))
  have hds : d.dsF mm j ψj = d.dsF mm j ψ := (hD.params ψj ψ hlv).1
  have hsp := spineFit_of_teleFitPA (by rw [hys, hD.len ψj]) hfitC
  rw [hds] at hsp
  exact blockCtorSpine_split hcj (hD.len ψ) hsp hparamsC hlenP

/-! ### §6b The bridge at the rule's own TWO-STAGE frame

The rule frame is opened by TWO `openPisAtFvars` calls at the
consecutive offsets `0` and `rP` — the recursor's stored type and the
constructor's parameter-instantiated telescope — and the rule's own
λ-domains come from an `instLamsAt` run at their concatenation.
`twoStageOpeners_spineFit` is `openerDoms_spineFit` with all of that
syntax discharged: `instLamsAt_index_WScoped`, `instLamsAt_leaves` and
`instLamsAt_bounded` on the second side, `openPisAtFvars_leaves` and
`openPisAtFvars_bounded` on the first. -/

section TwoStage

omit [SetTheory V] μ in
/-- A λ-tower at a fixed height determines its data: `mkLamsAV` is
injective on lists of equal length, so the `∀ lds A` binders the
contract's residue and tower statements carry are TIED and not free.
(Two spellings, two names: this is about `mkLamsAV`; `lamTele_mkLamsAV`
is the one about `LamTele`.) -/
theorem mkLamsAV_length_inj :
    ∀ {lds lds' : List (Nat × AnnotTerm)} {A A' : AnnotTerm},
      lds.length = lds'.length → mkLamsAV lds A = mkLamsAV lds' A' → lds = lds' ∧ A = A'
  | [], [], _, _, _, h => ⟨rfl, h⟩
  | [], _ :: _, _, _, hl, _ => nomatch hl
  | _ :: _, [], _, _, hl, _ => nomatch hl
  | ld :: lds, ld' :: lds', A, A', hl, h => by
    have h' : AnnotTerm.lam ld.1 ld.2 (mkLamsAV lds A)
        = AnnotTerm.lam ld'.1 ld'.2 (mkLamsAV lds' A') := h
    obtain ⟨h1, h2, h3⟩ : ld.1 = ld'.1 ∧ ld.2 = ld'.2 ∧ mkLamsAV lds A = mkLamsAV lds' A' := by
      injection h' with a b c
      exact ⟨a, b, c⟩
    obtain ⟨rfl, rfl⟩ := mkLamsAV_length_inj (by simpa using hl) h3
    exact ⟨by rw [show ld = ld' from Prod.ext h1 h2], rfl⟩

end TwoStage

/-! ## 13. The rule domains' bounds

Consumed by `BlockRecPreHpre.lean` (`hspF`'s field half) and
`TargetClasses.lean`. -/

section DomsBounded

variable {envC : Env} {pp : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {mpC : EnvModelM V μ envC} {F : Nat}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}

omit [SetTheory V] in
/-- A bounded field chain's entries, one by one. -/
theorem fieldsBelow_getD :
    ∀ {m : Nat} {Fs : List AnnotTerm}, FieldsBelow m Fs → ∀ q, q < Fs.length →
      Term.bvarsBelow (m + q) (Fs.getD q default).erase
  | _, [], _, _, hq => absurd hq (Nat.not_lt_zero _)
  | m, _ :: _, h, 0, _ => by simpa using h.1
  | m, _ :: Fs, h, q + 1, hq => by
    simp only [List.getD_cons_succ]
    have := fieldsBelow_getD (m := m + 1) (Fs := Fs) h.2 q (by simpa using hq)
    rwa [show m + 1 + q = m + (q + 1) from by omega] at this

end DomsBounded

end ConLeche.Model
