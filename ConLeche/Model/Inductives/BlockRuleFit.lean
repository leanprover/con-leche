module

public import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Annot.BitInst

public section

/-!
# The per-pair rule obligation's FIT and FIRED SPINE (task #315, M5 model half)

`BlockRuleDataB` (`BlockRecData.lean`) is the seam's rule-side
obligation at ONE environment and ONE valuation: five statements about
one (recursor, constructor) pair, all at the BASE frame `ρ`.  This
file discharges two of them — the first conjunct (the prefix and the
fields FIT the rule's domains) and the third (the FIRED SPINE reads to
the constructor at its own parameters) — and the two are one piece of
work, because both need the same fact:

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

* **§1 the frame transport.**  Every §24 bridge (`blockRecSpF_of`,
  `blockRecCtorFitsFrom_of`) concludes at the CHAIN frame over `K`
  binders, and `K` is a FREE variable of those theorems: the chain is
  there because the KIT runs under it, not because the bridge needs
  it.  At `K = 0` the chain frame IS the base frame and `liftDomsK 0`
  is the identity, both unconditionally, so the bridges' base-frame
  instances cost two `simp` lemmas and no boundedness premise (§28's
  `liftDomsK_eq_self_of_bounded` pays for the same collapse at the `K`
  the kit actually runs at, and is the route for the kit's own guard;
  it is not the route here);
* **§2 the major premise's decomposition** — `hps`, the index tuple's
  membership and the field spine's `ChainFit`, all at the recursor's
  parameter frame, out of `BlockRecSplitAt` and the constructor's
  reading;
* **§3 the two conjuncts.**
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

/-! ## 1. The frame transport: a ZERO chain is no chain -/

/-- **A zero lift is no lift**, at a binder list: `liftDomsK 0` is the
identity at every cutoff, with no boundedness side condition. -/
@[simp] theorem liftDomsK_zero :
    ∀ (k : Nat) (Ds : List AnnotTerm), liftDomsK 0 k Ds = Ds
  | _, [] => rfl
  | k, D :: Ds => by
    show AnnotTerm.liftN 0 D k :: liftDomsK 0 (k + 1) Ds = D :: Ds
    rw [AnnotTerm.liftN_zero, liftDomsK_zero (k + 1) Ds]

omit [SetTheory V] in
/-- **A zero chain is no chain**: `chainFrame 0` is the base frame. -/
@[simp] theorem chainFrame_zero (a ρ : Nat → V) : chainFrame 0 a ρ = ρ := rfl

/-- **§24's `hspF`, AT THE BASE FRAME** — `blockRecSpF_of` at `K = 0`.

`blockRecSpF_of` has `K` and the chain tuple `a` free; its conclusion
is a chain-frame statement because the KIT consumes it under the `K`
Σ' binders, not because the bridge needs them.  `BlockRuleDataB`'s
first conjunct is the same statement at `ρ` and at the UNLIFTED rule
domains, which is the `K = 0` instance — no boundedness premise, no
`liftDomsK_eq_self_of_bounded`.

Every other premise is `blockRecSpF_of`'s own; §2 below produces the
three that mention the block (`hps`, `ht`, `hfit`). -/
theorem blockRecSpF_base {envC : Env} {mpC : EnvModelM V μ envC} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mpC.base2 names d) {lps : List Name}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j : Nat} {mem : Nat → Nat} {ψ : Name → Nat}
    {ρ : Nat → V} {xs fs : List V} {t : V} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem c) j cA)
    (hfd : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []))
    (hasLen : (xs.take d.nP).length = d.nP)
    (hps : SpineFit ρ (d.params ψ) (xs.take d.nP))
    (htgt : ∀ l, l < cA.2 → d.tgts (mem c) j l < d.k)
    (hcN : mem c < d.N) (hj : j < (d.ctorsM (mem c)).length)
    (ht : t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (mem c))
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))))
    (hxs : xs.length = p.toBlockShape.rulePrefixAt c)
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs)
    (hfit : d.ChainFit ψ (consList (xs.take d.nP) ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ))) t (mem c) j fs) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i) (xs ++ fs) := by
  have hq := blockRecSpF_of (K := 0) (a := fun _ => (pt : V)) hM hμ h hr hcj hcf hfd hasLen
    hps htgt hcN hj ht hX hxs
    (by simpa only [chainFrame_zero, blockRecPdomsK, liftDomsK_zero] using hpref) hfit
  simpa only [chainFrame_zero, blockRecPdomsK, blockRecFdomsK, liftDomsK_zero] using hq

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
artefact** — see the FINDING recorded with
`blockRuleHsp_refutable_note` below. -/

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
constructor's field values fit its field domains AT THE RECURSOR's
parameter frame, as a `ChainFit` at the block's own carrier.

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
and so is the conclusion — see §3's FINDING. -/
theorem blockRuleChainFit_run (hM : BlockModelAt mpC.base2 names d)
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
    d.ChainFit ψ (consList ps ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ)))
      (d.tup ψ mm is) mm j ((ys.drop d.nP).map (interp V ρ)) := by
  have hmN : mm < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : j < (d.ctorsM mm).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hacv : mpC.base2.acval cA.1.name ψj = mpC.base2.acval cA.1.name ψ :=
    mpC.base2.acval_params cA.1.name _ hfind ψj ψ hlv
  have hval : interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys)
      = d.inj ψ mm j ((ys.drop d.nP).map (interp V ρ)) := by
    rw [hacv, interp_mkAppN_map,
      show ys.map (interp V ρ)
          = (ys.take d.nP).map (interp V ρ) ++ (ys.drop d.nP).map (interp V ρ) from by
        rw [← List.map_append, List.take_append_drop]]
    exact hM.ctor mm hmN j cA hcj ψ ρ _ _ hqs hfq
  rw [hM.leaf mm hmemk ψ ρ ps is hps hidx, hval] at hmaj
  have ht : d.tup ψ mm is ∈ˢ d.idx ψ (consList ps ρ) mm := tupW_mem hidx
  obtain ⟨j', fs', hj', hfit', heq⟩ :=
    blockCarrier_case hM (d.satOfSpine hps) hmN ht hmaj
  obtain ⟨rfl, rfl⟩ := hM.mkInj ψ hw mm hmN j _ j' fs' hjl hj'
    hfq.length_eq hfit'.length_eq heq
  exact hfit'

end ConLeche.Model
