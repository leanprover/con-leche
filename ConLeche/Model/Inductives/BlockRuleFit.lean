module

public import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecOpenerRead
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.BlockModel
import ConLeche.Model.Inductives.BlockLfpHoles

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

* **§1 the frame transport.**  The bridges `blockRecSpF_of` and
  `blockRecCtorFitsFrom_of` (`BlockRecPreRun.lean`) conclude at the
  CHAIN frame over `K` binders, with `K` free: the chain is there
  because the KIT runs under it.  At `K = 0` the chain frame IS the
  base frame and `liftDomsK 0` is the identity, both unconditionally,
  so the base-frame instances cost two `simp` lemmas and no
  boundedness premise;
* **§2 the major premise's decomposition** — `hps`, the index tuple's
  membership and the field spine's `ChainFit`, all at the recursor's
  parameter frame, out of `BlockRecSplitAt` and the constructor's
  reading;
* **§3 the fit and the fired spine**, and **§3b the index reading**,
  which is the same `ChainFit`'s SECOND conjunct read backwards.

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

/-- **`hspF` AT THE BASE FRAME** — `blockRecSpF_of` at `K = 0`.

`blockRecSpF_of` has `K` and the chain tuple `a` free; its conclusion
is a chain-frame statement because the KIT consumes it under the `K`
Σ' binders, not because the bridge needs them.  `BlockRuleDataB`'s
first conjunct is the same statement at `ρ` and at the UNLIFTED rule
domains, which is the `K = 0` instance — no boundedness premise.

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
and so is the conclusion — see §4. -/
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

/-! ## 3. The two conjuncts -/

variable {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **`BlockRecSplitAt` at the CONTRACT's own recursor fit.**  The
contract hands `TeleFitPA` of the recursor type at `xs ++ [maj]`;
`spineFit_blockRecTy` turns it into a fit of the binder data, which is
what the split consumes.  Out come the three facts the field half
needs: the block's PARAMETERS fit at the recursor's own prefix, the
recursor's index arguments fit the eliminated member's index
telescope there, and the MAJOR lies in that member's former applied to
both.  `hsplit` itself is produced by `blockRecSplitAt_of_shape`
(`BlockRecTyping.lean`) from `blockRecTyShape_run`. -/
theorem blockRecSplit_at_rule (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) {ρ : Nat → V}
    {xs : List AnnotTerm} {maj restR : AnnotTerm}
    (hxl : xs.length = p.toBlockShape.majorIdxAt c)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) (xs ++ [maj]) restR)
    {K : Nat} (hcK : c < K) {mem : Nat → Nat}
    (hsplit : BlockRecSplitAt V mpC.base2 d ψ K p.toBlockShape.rulePrefixAt mem
      (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c') ρ) :
    SpineFit ρ (d.params ψ)
        (((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).take d.nP) ∧
      SpineFit (consList
          (((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).take d.nP) ρ)
        (d.IdsM (mem c) ψ) ((xs.drop (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)) ∧
      interp V ρ maj ∈ˢ
        ((((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).take d.nP
            ++ (xs.drop (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).foldl app
          (interp V ρ (mpC.base2.acval (d.memberName (mem c)) ψ))) := by
  obtain ⟨-, -, -, hread, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  have hle : p.toBlockShape.rulePrefixAt c ≤ xs.length := by
    rw [hxl]; exact blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  have hws := spineFit_blockRecTy hμ mpC h hr ψ hread
    (by rw [List.length_append, List.length_singleton, hxl]) hfitR
  obtain ⟨-, -, hpar, hidx, hmaj⟩ := hsplit c hcK _ hws
  have hmap : (xs ++ [maj]).map (interp V ρ)
      = xs.map (interp V ρ) ++ [interp V ρ maj] := by rw [List.map_append]; rfl
  have hpref : prefOf (p.toBlockShape.rulePrefixAt c) ((xs ++ [maj]).map (interp V ρ))
      = (xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ) := by
    rw [prefOf, hmap, List.take_append_of_le_length (by rw [List.length_map]; exact hle),
      List.map_take]
  have hidxE : idxOf (p.toBlockShape.rulePrefixAt c) ((xs ++ [maj]).map (interp V ρ))
      = (xs.drop (p.toBlockShape.rulePrefixAt c)).map (interp V ρ) := by
    rw [idxOf, hmap, List.drop_append_of_le_length (by rw [List.length_map]; exact hle),
      List.dropLast_concat, List.map_drop]
  have hmajE : majOf ((xs ++ [maj]).map (interp V ρ)) = interp V ρ maj := by
    rw [majOf, hmap, List.reverse_append]; rfl
  simp only [hpref, hidxE, hmajE] at hpar hidx hmaj
  exact ⟨hpar, hidx, hmaj⟩

/-- **The field spine as a `SpineFit`** — `ChainFit`'s `FitsFrom` at
the block's slots, read as a fit of the field domains, through the
slot agreement.  `blockRecSpF` does this inside its own proof; `mk`
needs it on its own, because `BlockModelAt.ctor` speaks `SpineFit`. -/
theorem blockRuleFieldSpine_run (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    {ψ : Name → Nat} {ρ : Nat → V} {ps fs : List V} {t : V}
    (hasLen : ps.length = d.nP) (hps : SpineFit ρ (d.params ψ) ps)
    (htgt : ∀ l, l < cA.2 → d.tgts mm j l < d.k)
    (hcN : mm < d.N) (hjl : j < (d.ctorsM mm).length)
    (ht : t ∈ˢ d.idx ψ (consList ps ρ) mm)
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList ps ρ))
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ))))
    (hfit : d.ChainFit ψ (consList ps ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ)))
      t mm j fs) :
    SpineFit (consList ps ρ) ((d.Fss mm ψ).getD j []) fs :=
  spineFit_of_fitsFrom (fun l hl bs hb hrb => by
    rw [Nat.zero_add] at hrb ⊢
    exact blockSlot_agree hM hcj hcf hasLen hps htgt hcN hjl ht hX l hl bs hb hrb) hfit.1

/-! ### 2b. THE SQUASH ARM — the same `ChainFit` at `d.w ψ = 0`

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
source spine: the recursor's frame reads `fs'` (`ChainFit`'s own
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

/-- **§2's fact at `d.w ψ = 0`** — the same `ChainFit`, by the
subsingleton criterion instead of by injectivity.  See the section
note for the premises. -/
theorem blockRuleChainFit_sq (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    (hmemk : mm < d.k) {ψ ψj : Name → Nat}
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q) (hw : d.w ψ = 0)
    (hlarge : d.large = true) (hct1 : (d.ctorsM mm).length ≤ 1)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF mm j ψ).take d.nP).map (·.2.2)).reverse σ)
    (htgt : ∀ l, l < cA.2 → d.tgts mm j l < d.k)
    {ρ : Nat → V} {ps is : List V} {ys : List AnnotTerm}
    (hasLen : ps.length = d.nP)
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
    d.ChainFit ψ (consList ps ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ)))
      (d.tup ψ mm is) mm j ((ys.drop d.nP).map (interp V ρ)) := by
  have hmN : mm < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : j < (d.ctorsM mm).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hacv : mpC.base2.acval cA.1.name ψj = mpC.base2.acval cA.1.name ψ :=
    mpC.base2.acval_params cA.1.name _ hcf.1 ψj ψ hlv
  have hval : interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys)
      = d.inj ψ mm j ((ys.drop d.nP).map (interp V ρ)) := by
    rw [hacv, interp_mkAppN_map,
      show ys.map (interp V ρ)
          = (ys.take d.nP).map (interp V ρ) ++ (ys.drop d.nP).map (interp V ρ) from by
        rw [← List.map_append, List.take_append_drop]]
    exact hM.ctor mm hmN j cA hcj ψ ρ _ _ hqs hfq
  rw [hM.leaf mm hmemk ψ ρ ps is hps hidx, hval] at hmaj
  have ht : d.tup ψ mm is ∈ˢ d.idx ψ (consList ps ρ) mm := tupW_mem hidx
  obtain ⟨j', fs', hj', hfit', -⟩ :=
    blockCarrier_case hM (d.satOfSpine hps) hmN ht hmaj
  rw [show j' = j from by omega] at hfit'
  -- the recursor side: the decomposition's spine, as a `SpineFit`
  have hspR := blockRuleFieldSpine_run hM hcj hcf hasLen hps htgt hmN hjl ht
    (lfpTuple_mem _ _ _ _) hfit'
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
    have hstep := hfit'.2 l h1
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

This is `FixStageRec.lean`'s `hpin` at the block route's spellings,
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
the lift: the same three steps — the `FitsFrom`-to-
`SpineFit` bridge (§3's `blockRuleFieldSpine_run`), the subsingleton
criterion (`blockCtorFieldProp`) and `srcVals_of_fit` — at an
ARBITRARY index tuple and an arbitrary fitting spine instead of at the
rule's own.

**The lift needs ONE extra premise, `TupleLe`, and it is not
cosmetic.**  The regime quantifies over an arbitrary member `X` of the
TUPLE SPACE, while §2b works at the fixpoint: a `ChainFit` at a
general `X` puts a RECURSIVE field's value in the SLOT, and the
criterion is a statement about the field's DOMAIN.  At `w = 0` the
slot is a truth value, so that field's own value collapses to the
point — but the criterion cannot be WALKED past it:
`CtorDataI.srcProp` bounds field `q` only along a spine fitting the
EARLIER DOMAINS (`FieldsBoundSrc`), and a slot member need not be a
member of the domain when the domain is the empty truth value.

A tuple BELOW the fixpoint transports its `ChainFit` INTO the
fixpoint's (`blockChainFit_of_le`, by `slotSet_mono` at every
recursive position), and there the domains are the slots
(`blockSlot_agree`) and the criterion applies unchanged.  The graph
kit's call site is at the fixpoint itself (`TupleLe.refl`). -/

/-- **`FitsFrom` transports along an INCLUSION of the slots** —
`spineFit_of_fitsFrom`'s pattern with `⊆ˢ` in place of `=`.  The
inclusion is asked for only at the positions the walk actually reads,
and along the walk's own prefixes, which is what lets the slot fit
(`BlockModelAt.idxFit`) supply it. -/
theorem fitsFrom_mono {rs : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs : List AnnotTerm} {as : List V},
      (∀ l, l < Fs.length → ∀ bs : List V,
        FitsFrom rs slot i ρ (Fs.take l) bs → rs.getD (i + l) false = true →
        slot (i + l) (consList bs ρ) ⊆ˢ slot' (i + l) (consList bs ρ)) →
      FitsFrom rs slot i ρ Fs as → FitsFrom rs slot' i ρ Fs as
  | _, _, [], [], _, _ => trivial
  | _, _, [], _ :: _, _, h => h.elim
  | _, _, _ :: _, [], _, h => h.elim
  | i, ρ, F :: Fs, a :: as, hag, h => by
    refine ⟨?_, fitsFrom_mono (fun l hl bs hb hr => ?_) h.2⟩
    · have h1 : a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) := h.1
      show a ∈ˢ (if rs.getD i false then slot' i ρ else interp V ρ F)
      by_cases hr : rs.getD i false = true
      · rw [if_pos hr] at h1 ⊢
        have h0 := hag 0 (by simp) [] trivial (by rw [Nat.add_zero]; exact hr)
        rw [Nat.add_zero] at h0
        simp only [consList_nil] at h0
        exact h0 _ h1
      · have hr' : rs.getD i false = false := by simpa using hr
        rw [hr'] at h1 ⊢
        exact h1
    · have hb' : FitsFrom rs slot i ρ ((F :: Fs).take (l + 1)) (a :: bs) := ⟨h.1, hb⟩
      have hag' := hag (l + 1) (by simpa using hl) (a :: bs) hb'
        (by rw [show i + (l + 1) = i + 1 + l from by omega]; exact hr)
      rw [show i + (l + 1) = i + 1 + l from by omega] at hag'
      exact hag'

/-- **A `ChainFit` at a tuple BELOW the fixpoint is a `ChainFit` at
the fixpoint.**  The index clause does not mention the tuple at all;
the entry clause transports at every RECURSIVE position by
`slotSet_mono`, whose slot fit is `BlockModelAt.idxFit` at the SMALLER
tuple — which is where the walk's own prefix is available. -/
theorem blockChainFit_of_le (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List V}
    (hps : SpineFit ρ (d.params ψ) ps)
    (htgt : ∀ l, l < cA.2 → d.tgts mm j l < d.k)
    (hcN : mm < d.N) (hjl : j < (d.ctorsM mm).length)
    {t : V} (ht : t ∈ˢ d.idx ψ (consList ps ρ) mm)
    {X : Nat → V}
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList ps ρ)) X)
    (hle : TupleLe d.N (d.idx ψ (consList ps ρ)) X
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ))))
    {fs : List V} (hfit : d.ChainFit ψ (consList ps ρ) X t mm j fs) :
    d.ChainFit ψ (consList ps ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ)))
      t mm j fs := by
  have hnF : ((d.Fss mm ψ).getD j []).length = cA.2 := by
    obtain ⟨-, -, hCD⟩ := hcf
    have hFssD : (d.Fss mm ψ).getD j [] = ((d.dsF mm j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hCD.len ψ]
    omega
  refine ⟨fitsFrom_mono (fun l hl bs hb hrb => ?_) hfit.1, hfit.2⟩
  rw [Nat.zero_add] at hrb ⊢
  rw [hnF] at hl
  have hSF := hM.idxFit ψ (consList ps ρ) (d.satOfSpine hps) X hX mm hcN t ht j hjl l
    (by rw [hnF]; exact hl) hrb bs hb
  exact slotSet_mono (hle _ (Nat.lt_of_lt_of_le (htgt l hl) (Nat.le_add_right _ _))) hSF

/-- **THE LIFT** — the subsingleton criterion as a producer of regime
SQ's `hsrcAt`: at a `Prop`-valued block with the declared large shape,
a spine fitting the lone constructor at a tuple BELOW the fixpoint IS
the source spine of the index tuple.

`srcs` is `srcList` at the constructor's own index readings, which is
the shape `srcVals_of_fit` produces and the shape the regime's `srcs`
parameter is instantiated at. -/
theorem blockChainFit_srcVals_zero (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    (hlarge : d.large = true) {ψ : Name → Nat} (hw : d.w ψ = 0)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF mm j ψ).take d.nP).map (·.2.2)).reverse σ)
    (hlenIds : (d.IdsM mm ψ).length = d.nIdxAt mm)
    {ρ : Nat → V} {ps : List V}
    (hasLen : ps.length = d.nP) (hps : SpineFit ρ (d.params ψ) ps)
    (htgt : ∀ l, l < cA.2 → d.tgts mm j l < d.k)
    (hcN : mm < d.N) (hjl : j < (d.ctorsM mm).length)
    {X : Nat → V}
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList ps ρ)) X)
    (hle : TupleLe d.N (d.idx ψ (consList ps ρ)) X
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ))))
    {t : V} (ht : t ∈ˢ d.idx ψ (consList ps ρ) mm)
    {fs : List V} (hfit : d.ChainFit ψ (consList ps ρ) X t mm j fs) :
    fs = srcVals (isOfW (d.uM mm ψ) (d.nIdxAt mm) t)
      (srcList ((d.Ess mm ψ).getD j []) ((d.Fss mm ψ).getD j []).length) := by
  have hIdxOk := hM.idxOk ψ _ (d.satOfSpine hps) mm hcN
  have hEsLen : ((d.Ess mm ψ).getD j []).length = (d.IdsM mm ψ).length := by
    obtain ⟨-, -, hCD⟩ := hcf
    have hEssD : (d.Ess mm ψ).getD j [] = d.esF mm j ψ := essOfR_fixCtorDataList_getD hcj
    rw [hEssD, hCD.lenE ψ, hlenIds]
  have ht' : t ∈ˢ idxSet (d.uM mm ψ) (consList ps ρ) (d.IdsM mm ψ) := ht
  obtain ⟨is, hisp, rfl⟩ := mem_idxSet_elim ht'
  have hfitL := blockChainFit_of_le hM hcj hcf hps htgt hcN hjl ht hX hle hfit
  have hsp := blockRuleFieldSpine_run hM hcj hcf hasLen hps htgt hcN hjl ht
    (lfpTuple_mem _ _ _ _) hfitL
  have hidx : idxValsAt (consList ps ρ) ((d.Ess mm ψ).getD j []) fs = is := by
    show ((d.Ess mm ψ).getD j []).map (interp V (consList fs (consList ps ρ))) = is
    refine List.ext_getElem (by rw [List.length_map, hEsLen, hisp.length_eq])
      fun l h1 h2 => ?_
    rw [List.length_map, hEsLen] at h1
    have hstep := hfitL.2 l h1
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
theorem blockRuleChainFit_any (hM : BlockModelAt mpC.base2 names d)
    {mm j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    (hmemk : mm < d.k) {ψ ψj : Name → Nat}
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    (hlarge : d.w ψ = 0 → d.large = true)
    (hct1 : d.w ψ = 0 → (d.ctorsM mm).length ≤ 1)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF mm j ψ).take d.nP).map (·.2.2)).reverse σ)
    (htgt : ∀ l, l < cA.2 → d.tgts mm j l < d.k)
    {ρ : Nat → V} {ps is : List V} {ys : List AnnotTerm}
    (hasLen : ps.length = d.nP)
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
    d.ChainFit ψ (consList ps ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList ps ρ)) (d.Φ ψ (consList ps ρ)))
      (d.tup ψ mm is) mm j ((ys.drop d.nP).map (interp V ρ)) := by
  by_cases hw : d.w ψ = 0
  · exact blockRuleChainFit_sq hM hcj hcf hmemk hlv hw (hlarge hw) (hct1 hw) hparamsC htgt
      hasLen hps hidx hqs hfq (hpin hw) hmaj
  · exact blockRuleChainFit_run hM hcj hcf.1 hmemk hlv hw hps hidx hqs hfq hmaj

/-- **`BlockRuleDataB`'s FIRST conjunct at the run** — the prefix half
(`blockRuleHspPref_run`) and the FIELD half, appended.

The field half is `blockRecSpF_of` at `K = 0` (§1) over the
`ChainFit` at the recursor's parameters (§2), and its three
block-facing premises come from `BlockRecSplitAt` at the contract's
own recursor fit.

**The conjunct is REFUTABLE at `d.w ψ = 0` with `ℓ = 0`** (§4).  §2b
closes the `d.w ψ = 0` case whenever the large-elimination counting
guard has fired, which is exactly the `ℓ ≠ 0` region, so what this
theorem takes is that guard's two facts and the rule's index pin. -/
theorem blockRuleHsp_field_run (hM : BlockModelAt mpC.base2 names d)
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j : Nat} {mem : Nat → Nat} {cA : ConstantVal × Nat}
    {ψ ψj : Name → Nat}
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem c) j cA)
    (hfd : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []))
    (hmemk : mem c < d.k) (hnP : d.nP ≤ p.toBlockShape.rulePrefixAt c)
    (htgt : ∀ l, l < cA.2 → d.tgts (mem c) j l < d.k)
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    -- the COUNTING guard's two facts, the KERNEL's (the dispatch's
    -- `hK1` is the same guard's one-member half, in the same spelling)
    (hlarge : d.w ψ = 0 → d.large = true)
    (hct1 : d.w ψ = 0 → (d.ctorsM (mem c)).length ≤ 1)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF (mem c) j ψ).take d.nP).map (·.2.2)).reverse σ)
    {ρ : Nat → V} {xs ys : List AnnotTerm} {restR : AnnotTerm}
    (hxl : xs.length = p.toBlockShape.majorIdxAt c)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)
      (xs ++ [AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    {K : Nat} (hcK : c < K)
    (hsplit : BlockRecSplitAt V mpC.base2 d ψ K p.toBlockShape.rulePrefixAt mem
      (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c') ρ)
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss (mem c) ψ).getD j []) ((ys.drop d.nP).map (interp V ρ)))
    (hpin : d.w ψ = 0 →
      ((d.Ess (mem c) ψ).getD j []).map
          (interp V (consList ((ys.drop d.nP).map (interp V ρ))
            (consList ((ys.take d.nP).map (interp V ρ)) ρ)))
        = (xs.drop (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
      ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)
        ++ (ys.drop d.nP).map (interp V ρ)) := by
  have hle : p.toBlockShape.rulePrefixAt c ≤ xs.length := by
    rw [hxl]; exact blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨hps, hidx, hmaj⟩ :=
    blockRecSplit_at_rule (d := d) hμ mpC h hr ψ hxl hfitR hcK hsplit
  have hxsLen : ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).length
      = p.toBlockShape.rulePrefixAt c := by
    rw [List.length_map, List.length_take]; omega
  have hasLen : (((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).take d.nP).length
      = d.nP := by rw [List.length_take, hxsLen]; omega
  refine blockRecSpF_base (j := j) (mem := mem) (cA := cA) hM hμ h hr hcj hcf hfd
    hasLen hps htgt
    (Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _))
    (List.getElem?_eq_some_iff.mp hcj).1 (tupW_mem hidx) (lfpTuple_mem _ _ _ _) hxsLen
    (blockRuleHspPref_run hμ mpC h hr ψ hxl hfitR) ?_
  exact blockRuleChainFit_any hM hcj hcf hmemk hlv hlarge hct1 hparamsC htgt hasLen
    hps hidx hqs hfq hpin hmaj

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
  rw [mpC.base2.acval_params cA.1.name _ hfind ψj ψ hlv, interp_mkAppN_map,
    show ys.map (interp V ρ)
        = (ys.take d.nP).map (interp V ρ) ++ (ys.drop d.nP).map (interp V ρ) from by
      rw [← List.map_append, List.take_append_drop]]
  exact hM.ctor mm hcN j cA hcj ψ ρ _ _ hqs hfq

/-- **`BlockRuleDataB`'s THIRD conjunct at the run** — the FIRED SPINE.

The rule fires the constructor at the RECURSOR's parameters and the
rule's field openers; the major is the constructor at its OWN
parameters.  Both read to `d.inj ψ (mem c) j fs` — the block's
injection does not mention the parameters at all — so the conjunct is
`blockRecMkK_value` at `K = 0` against `blockCtorMajor_value`.

The two parameter spines' FITS are what this costs, and both are
produced: the recursor's by `BlockRecSplitAt` at the contract's own
recursor fit, the constructor's by the contract's `hfitC`. -/
theorem blockRuleHmk_run (hM : BlockModelAt mpC.base2 names d)
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j : Nat} {mem : Nat → Nat} {cA : ConstantVal × Nat}
    {rhs : Expr} {ψ ψj : Name → Nat}
    (hcA : r.2.2.2[i]? = some cA) (hrhs : r.2.1[i]? = some rhs)
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem c) j cA)
    (hlps : cA.1.levelParams = p.lps) (hdnP : d.nP = p.nP)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c)
    (hfd : blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0 ((d.Fss (mem c) ψ).getD j []))
    (hmemk : mem c < d.k)
    (htgt : ∀ l, l < cA.2 → d.tgts (mem c) j l < d.k)
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    -- the COUNTING guard's two facts, the KERNEL's (the dispatch's
    -- `hK1` is the same guard's one-member half, in the same spelling)
    (hlarge : d.w ψ = 0 → d.large = true)
    (hct1 : d.w ψ = 0 → (d.ctorsM (mem c)).length ≤ 1)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF (mem c) j ψ).take d.nP).map (·.2.2)).reverse σ)
    {ρ : Nat → V} {xs ys : List AnnotTerm} {restR : AnnotTerm}
    (hxl : xs.length = p.toBlockShape.majorIdxAt c)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)
      (xs ++ [AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    {K : Nat} (hcK : c < K)
    (hsplit : BlockRecSplitAt V mpC.base2 d ψ K p.toBlockShape.rulePrefixAt mem
      (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c') ρ)
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss (mem c) ψ).getD j []) ((ys.drop d.nP).map (interp V ρ)))
    (hpin : d.w ψ = 0 →
      ((d.Ess (mem c) ψ).getD j []).map
          (interp V (consList ((ys.drop d.nP).map (interp V ρ))
            (consList ((ys.take d.nP).map (interp V ρ)) ρ)))
        = (xs.drop (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)) :
    interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)
          ++ (ys.drop d.nP).map (interp V ρ)) ρ)
        (blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
      = interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys) := by
  have hmN : mem c < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : j < (d.ctorsM (mem c)).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hle : p.toBlockShape.rulePrefixAt c ≤ xs.length := by
    rw [hxl]; exact blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨hps, hidx, hmaj⟩ :=
    blockRecSplit_at_rule (d := d) hμ mpC h hr ψ hxl hfitR hcK hsplit
  have hxsLen : ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).length
      = p.toBlockShape.rulePrefixAt c := by
    rw [List.length_map, List.length_take]; omega
  have hasLen : (((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).take d.nP).length
      = d.nP := by rw [List.length_take, hxsLen]; omega
  have hfit := blockRuleChainFit_any hM hcj hcf hmemk hlv hlarge hct1 hparamsC htgt hasLen
    hps hidx hqs hfq hpin hmaj
  have hfp := blockRuleFieldSpine_run hM hcj hcf hasLen hps htgt hmN hjl
    (tupW_mem hidx) (lfpTuple_mem _ _ _ _) hfit
  have hnF : ((d.Fss (mem c) ψ).getD j []).length = cA.2 := by
    obtain ⟨-, -, hD⟩ := hcf
    have hFssD : (d.Fss (mem c) ψ).getD j [] = ((d.dsF (mem c) j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hD.len ψ]
    omega
  have hval := blockRecMkK_value (K := 0) (a := fun _ => (pt : V)) hM h hr hcA hrhs hcf.1
    (by rw [← hlps]; rfl) hnP hmN hcj ψ hxsLen (by rw [hfp.length_eq, hnF])
    (by rw [blockRulePdomsAV_length hμ mpC h hr ψ, hfd, liftDomsK_length, hxsLen,
        hfp.length_eq])
    (by rw [← hdnP]; exact hps) (by rw [← hdnP]; exact hfp)
  rw [chainFrame_zero, blockRecMkK, AnnotTerm.liftN_zero] at hval
  rw [hval, blockCtorMajor_value hM hcj hcf.1 hmN hlv hqs hfq]

/-! ## 3b. The INDEX READING -/

/-- **`BlockRuleDataB`'s SECOND conjunct at the run** — the rule's
INDEX EXPRESSIONS read to the recursor's own index arguments.

This is the block route's `IotaIndexPin` content, and the pin is NOT
what produces it.  The pin ties the CONSTRUCTOR-frame reading of the
conclusion's index arguments to `xs.drop rP`; the conjunct asks for
the RECURSOR-frame reading.  The two frames differ exactly in the
parameter spine, and — the rule being `paramsBlind` — the only thing
that relates those is the MAJOR PREMISE.  So the row rides on §2's
fact, the one the FIT needed: `blockRuleChainFit_run` produces a
`ChainFit` at the RECURSOR's parameter frame, and `ChainFit`'s SECOND
conjunct IS the reading equality — against the components of the
index tuple the carrier membership named, which `projS_tupW` retracts
to `xs.drop rP` itself.

Two transports and no new mathematics: `hes` (`blockRecCtorIdx`'s own
named premise — `blockRuleEsAV_eq` composed with the record's
`Es`/`Ess` identification) moves the syntactic `es0` onto the datum's
`Ess`, and `interp_liftN_rule` at `K = 0` moves the reading from the
rule's frame to the block's.

**The conjunct is REFUTABLE at `d.w ψ = 0` with `ℓ = 0`** — §5, a
DIFFERENT counterexample from §4's.  Like the fit, it is closed at
`d.w ψ = 0` by §2b under the counting guard, so the premise here is
that guard's two facts and the pin, not `d.w ψ ≠ 0`. -/
theorem blockRuleHes_run (hM : BlockModelAt mpC.base2 names d)
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i j : Nat} {mem : Nat → Nat} {cA : ConstantVal × Nat}
    {ψ ψj : Name → Nat}
    (hcj : (d.ctorsM (mem c))[j]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem c) j cA)
    (hes : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i
      = ((d.Ess (mem c) ψ).getD j []).map
          (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2))
    (hmemk : mem c < d.k) (hnP : d.nP ≤ p.toBlockShape.rulePrefixAt c)
    (htgt : ∀ l, l < cA.2 → d.tgts (mem c) j l < d.k)
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    -- the COUNTING guard's two facts, the KERNEL's (the dispatch's
    -- `hK1` is the same guard's one-member half, in the same spelling)
    (hlarge : d.w ψ = 0 → d.large = true)
    (hct1 : d.w ψ = 0 → (d.ctorsM (mem c)).length ≤ 1)
    (hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF (mem c) j ψ).take d.nP).map (·.2.2)).reverse σ)
    {ρ : Nat → V} {xs ys : List AnnotTerm} {restR : AnnotTerm}
    (hxl : xs.length = p.toBlockShape.majorIdxAt c)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)
      (xs ++ [AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    {K : Nat} (hcK : c < K)
    (hsplit : BlockRecSplitAt V mpC.base2 d ψ K p.toBlockShape.rulePrefixAt mem
      (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c') ρ)
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss (mem c) ψ).getD j []) ((ys.drop d.nP).map (interp V ρ)))
    (hpin : d.w ψ = 0 →
      ((d.Ess (mem c) ψ).getD j []).map
          (interp V (consList ((ys.drop d.nP).map (interp V ρ))
            (consList ((ys.take d.nP).map (interp V ρ)) ρ)))
        = (xs.drop (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)) :
    (blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).map
        (interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)
          ++ (ys.drop d.nP).map (interp V ρ)) ρ))
      = (xs.drop (p.toBlockShape.rulePrefixAt c)).map (interp V ρ) := by
  have hmN : mem c < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : j < (d.ctorsM (mem c)).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hle : p.toBlockShape.rulePrefixAt c ≤ xs.length := by
    rw [hxl]; exact blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨hps, hidx, hmaj⟩ :=
    blockRecSplit_at_rule (d := d) hμ mpC h hr ψ hxl hfitR hcK hsplit
  have hXsLen : ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).length
      = p.toBlockShape.rulePrefixAt c := by
    rw [List.length_map, List.length_take]; omega
  have hasLen : (((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).take d.nP).length
      = d.nP := by rw [List.length_take, hXsLen]; omega
  have hfit := blockRuleChainFit_any hM hcj hcf hmemk hlv hlarge hct1 hparamsC htgt hasLen
    hps hidx hqs hfq hpin hmaj
  have hfp := blockRuleFieldSpine_run hM hcj hcf hasLen hps htgt hmN hjl
    (tupW_mem hidx) (lfpTuple_mem _ _ _ _) hfit
  have hnF : ((d.Fss (mem c) ψ).getD j []).length = cA.2 := by
    obtain ⟨-, -, hD⟩ := hcf
    have hFssD : (d.Fss (mem c) ψ).getD j [] = ((d.dsF (mem c) j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hD.len ψ]
    omega
  have hfsLen : ((ys.drop d.nP).map (interp V ρ)).length = cA.2 := by
    rw [hfq.length_eq, hnF]
  have hsat := d.satOfSpine hps
  have hres := hM.resIdxFit ψ _ hsat (mem c) hmN j hjl _ hfp
  have hEsLen : ((d.Ess (mem c) ψ).getD j []).length = (d.IdsM (mem c) ψ).length := by
    have hq := hres.length_eq
    rwa [List.length_map] at hq
  have hIdxOk := hM.idxOk ψ _ hsat (mem c) hmN
  have hmapEq : (blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).map
        (interp V (consList ((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)
          ++ (ys.drop d.nP).map (interp V ρ)) ρ))
      = ((d.Ess (mem c) ψ).getD j []).map
          (interp V (consList ((ys.drop d.nP).map (interp V ρ))
            (consList (((xs.take (p.toBlockShape.rulePrefixAt c)).map (interp V ρ)).take d.nP)
              ρ))) := by
    rw [hes, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    have hq := interp_liftN_rule (V := V) (K := 0) (a := fun _ => (pt : V)) (ρ := ρ)
      (nP := d.nP) hXsLen hfsLen e
    simpa only [chainFrame_zero, AnnotTerm.liftN_zero, Function.comp_apply] using hq
  rw [hmapEq]
  refine List.ext_getElem (by rw [List.length_map, hEsLen, hidx.length_eq]) fun l h1 h2 => ?_
  have hl : l < (d.IdsM (mem c) ψ).length := by
    rw [List.length_map, hEsLen] at h1; exact h1
  have hlE : l < ((d.Ess (mem c) ψ).getD j []).length := by rw [hEsLen]; exact hl
  have hstep := hfit.2 l hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlE, Option.getD_some] at hstep
  rw [List.getElem_map, hstep, BlockData.tup, projS_tupW hIdxOk hidx hl,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-! ## 3c. The three conjuncts' OWN premises, produced

`blockRuleHsp_field_run`, `blockRuleHes_run` and `blockRuleHmk_run`
each take `hlv` (the constructor's level assignment agrees with the
recursor's on the block's parameters) and `hqs`/`hfq` (the
constructor's parameter and field spines fit).  All three are
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

/-! ## §6 THE TOWER FIT — the λ-domain bridge, at an arbitrary second side

`BlockRuleDataB`'s FIFTH conjunct compares two readings of the SAME
binders: the rule's own λ-domains (`lds.map (·.2)`, `blockRuleTower_run`)
and the OPENERS' stored types (`blockRulePdomsAV ++ blockRuleFdomsAV`).
Nothing identifies them syntactically; what the checker does about it
is the `checkBlockDefEqList` that compares the two binder by binder at
the rule frame's depth (`blockRuleData_run`'s last two rows).

The bridge from that comparison to a `SpineFit` transfer is
`prefixDoms_spineFit`'s (`BlockRecPreRun.lean` §35F), written for two
`openPisAtFvars` runs of the SAME length.  Here the second side is not
an opening at all — it is an `instLamsAt` run's domain list — so §35's
theorem does not apply verbatim; `openerDoms_spineFit` below is that
theorem with the second side abstracted to an arbitrary list of
subjects whose leaves are the FIRST side's openers.  Everything else
is §35's: the depth transport (`denoteMeta_lift` + `interp_liftN`),
the soundness hop at the frame's context, and `spineFit_congr_walk`.

Two spellings, two names: `prefixDoms_spineFit` stays the
opening-against-opening version (its `hdeq` is a disjunction, because
the prefix-agreement check supplies only one orientation); this one
takes the comparison in the single orientation `checkBlockDefEqList`
runs it in (openers' stored types on the left, the rule's λ-domains on
the right). -/

section TowerFit

/-- **A graded λ-tower's domains are graded along their own fitting
spines** — `piTeleAV_graded`'s λ-side twin, read off `mkLamsAV`
directly.  Domain `i` (outermost first) is graded at the frame the
spine's first `i` values push on.

It is what makes the tower fit's `hokB` free: the rule's reading is
graded at every valuation (`blockRuleRhs_read_run`'s second
component), and that grading descends to the tower's own domains. -/
theorem mkLamsAV_doms_graded :
    ∀ {lds : List (Nat × AnnotTerm)} {b : AnnotTerm} {ρ : Nat → V} {ys : List V} {i : Nat},
      WellDenotedV V ρ (mkLamsAV lds b) → i < lds.length →
      SpineFit ρ ((lds.map (·.2)).take i) ys →
      WellDenotedV V (consList ys ρ) ((lds.map (·.2)).getD i default)
  | [], _, _, _, _, _, hi, _ => absurd hi (by simp)
  | ld :: lds, b, ρ, ys, 0, hok, _, hys => by
    have hyn : ys = [] := by
      cases ys with
      | nil => rfl
      | cons y ys => exact absurd hys (by simp [SpineFit])
    subst hyn
    show WellDenotedV V (consList [] ρ) _
    rw [consList_nil]
    have h1 : WellDenoted V ρ ld.2 :=
      ((WellDenoted_lam V ρ ld.1 ld.2 (mkLamsAV lds b)) ▸ hok.1).1
    have h2 : AnnotValid V ρ ld.2 :=
      ((AnnotValid_lam V ρ ld.1 ld.2 (mkLamsAV lds b)) ▸ hok.2).1
    exact ⟨h1, h2⟩
  | ld :: lds, b, ρ, ys, i + 1, hok, hi, hys => by
    cases ys with
    | nil => exact absurd hys (by simp [SpineFit])
    | cons y ys =>
      have hmem : y ∈ˢ interp V ρ ld.2 := hys.1
      have htl : SpineFit (cons y ρ) ((lds.map (·.2)).take i) ys := hys.2
      have hokb : WellDenotedV V (cons y ρ) (mkLamsAV lds b) :=
        ⟨((WellDenoted_lam V ρ ld.1 ld.2 (mkLamsAV lds b)) ▸ hok.1).2.1 y hmem,
          ((AnnotValid_lam V ρ ld.1 ld.2 (mkLamsAV lds b)) ▸ hok.2).2 y hmem⟩
      have hq := mkLamsAV_doms_graded (lds := lds) (b := b) hokb (by simpa using hi) htl
      rw [consList_cons]
      exact hq

/-- **THE λ-DOMAIN BRIDGE** — a spine fitting the OPENERS' stored-type
readings fits the readings of any second list of domains the checker
compared them with, binder by binder, at the frame's own depth.

`prefixDoms_spineFit` (`BlockRecPreRun.lean` §35F) with the second
side generalised: there it is a second `openPisAtFvars` run (whose
subjects carry their OWN annotations, which is why that proof needs
`ctxOk_of_openers_congr` with a non-trivial agreement), here it is an
arbitrary list `bs` whose fvar leaves are the FIRST side's openers —
which is what an `instLamsAt` run at those openers produces.  Both
`CtxOk`s are then at one context and the agreement is `rfl`; the
induction on the position survives, because the SECOND side's
gradings are still only available along ITS own fitting spines.

The premises are bounded by the position: `hwsB`, `hleafB`, `hlbB`
and `hdB` speak about slot `i` for `i < n` and about nothing else, and
`hdeq` is the check's own comparison in the one orientation
`checkBlockDefEqList` runs it in. -/
theorem openerDoms_spineFit {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {fuel n : Nat}
    {fvs : List Expr} (hlfvs : fvs.length = n)
    (hshape : ∀ (i : Nat) (x : Expr), fvs[i]? = some x → ∃ ty, x = Expr.fvar i ty)
    (hws : ∀ x ∈ fvs, Expr.WScoped n x)
    (hleafA : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvs)
    (hlbA : ∀ x ∈ fvs, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    {bs : List Expr}
    (hwsB : ∀ i, i < n → Expr.WScoped i (bs.getD i default))
    (hleafB : ∀ i, i < n →
      ∀ lf ∈ (bs.getD i default).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvs)
    (hlbB : ∀ i, i < n → (bs.getD i default).looseBVarsBounded 0 = true)
    {domsA domsB : List AnnotTerm}
    (hlenA : domsA.length = n) (hlenB : domsB.length = n)
    (hdA : ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      denoteMeta mp.base2.acval envT ψ i (Expr.fvarTypeD x) = some (domsA.getD i default))
    (hdB : ∀ i, i < n →
      denoteMeta mp.base2.acval envT ψ i (bs.getD i default) = some (domsB.getD i default))
    (hokA : ∀ i, i < n → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ (domsA.take i) ys → WellDenotedV V (consList ys σ) (domsA.getD i default))
    (hokB : ∀ i, i < n → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ (domsB.take i) ys → WellDenotedV V (consList ys σ) (domsB.getD i default))
    (hdeq : ∀ i, i < n →
      ConLeche.isDefEqCore μ envT fuel n ((fvs.map Expr.fvarTypeD).getD i default)
        (bs.getD i default) = .ok true)
    {ρ₀ : Nat → V} {xs : List V} (hfit : SpineFit ρ₀ domsA xs) :
    SpineFit ρ₀ domsB xs := by
  obtain ⟨-, -, ihd, -⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) fuel
  have hΔlen : domsA.reverse.length = n := by rw [List.length_reverse, hlenA]
  have hentA : ∀ i, i < n → domsA.reverse[n - 1 - i]? = some (domsA.getD i default) :=
    fun i hi => getElem?_reverse_entry hlenA hi
  have key : ∀ l, l < n → ∀ (ρ₁ : Nat → V) (ys : List V), SpineFit ρ₁ domsA ys →
      interp V (consList (ys.take l) ρ₁) (domsA.getD l default)
        = interp V (consList (ys.take l) ρ₁) (domsB.getD l default) := by
    intro l
    induction l using Nat.strongRecOn with
    | _ l IH =>
      intro hl ρ₁ ys hfitY
      have hylen : ys.length = n := by rw [SpineFit.length_eq hfitY, hlenA]
      have hbelow : ∀ i, i < l → ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
          interp V (shiftE (n - i) 0 ρ) (domsA.getD i default)
            = interp V (shiftE (n - i) 0 ρ) (domsB.getD i default) := by
        intro i hi ρ hρ
        obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
        rw [shiftE_consList_take i hzlen]
        exact IH i hi (by omega) ρ₂ zs hfitZ
      have hokAf : ∀ i, i < l → ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
          WellDenotedV V (shiftE (n - i) 0 ρ) (domsA.getD i default) := by
        intro i hi ρ hρ
        obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
        rw [shiftE_consList_take i hzlen]
        exact hokA i (by omega) ρ₂ (zs.take i) (spineFit_take_any hfitZ i)
      -- the FIRST side's subject at this position
      obtain ⟨xA, hxA⟩ : ∃ x, fvs[l]? = some x :=
        ⟨fvs[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
      have hsubA : (fvs.map Expr.fvarTypeD).getD l default = Expr.fvarTypeD xA := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hxA]; rfl
      have hwl : Expr.WScoped n xA := hws _ (List.mem_of_getElem? hxA)
      obtain ⟨tyA, rfl⟩ := hshape l xA hxA
      have hwty : l < n ∧ Expr.WScoped l tyA := by simpa [Expr.WScoped] using hwl
      have hwsAl : Expr.WScoped l (Expr.fvarTypeD (Expr.fvar l tyA)) := hwty.2
      have hltA : ∀ lf ∈ (Expr.fvarTypeD (Expr.fvar l tyA)).fvarLeaves, lf.1 < l :=
        fun lf hlf => Expr.fvarLeaves_lt_of_wscoped hwsAl lf hlf
      -- `CtxOk` for both subjects, at the FIRST side's own context
      have hctxA : CtxOk mp.base2 ψ n domsA.reverse (Expr.fvarTypeD (Expr.fvar l tyA)) :=
        ctxOk_of_openers_congr mp.base2.acval_closed (Aa := fun i => domsA.getD i default)
          (Ba := fun i => domsA.getD i default) hΔlen hshape hws hdA
          (hleafA l _ hxA) hltA (fun i hi => hentA i (by omega))
          (fun _ _ _ _ _ => rfl) (fun i hi _ ρ hρ => hokAf i hi ρ hρ)
      have hctxB : CtxOk mp.base2 ψ n domsA.reverse (bs.getD l default) :=
        ctxOk_of_openers_congr mp.base2.acval_closed (Aa := fun i => domsA.getD i default)
          (Ba := fun i => domsA.getD i default) hΔlen hshape hws hdA
          (hleafB l hl)
          (fun lf hlf => Expr.fvarLeaves_lt_of_wscoped (hwsB l hl) lf hlf)
          (fun i hi => hentA i (by omega))
          (fun _ _ _ _ _ => rfl) (fun i hi _ ρ hρ => hokAf i hi ρ hρ)
      -- the syntactic side conditions
      have hlbAx := hlbA _ (List.mem_of_getElem? hxA)
      have hlbBx := hlbB l hl
      have hLA := leavesBounded_of_openers hlbA (hleafA l _ hxA)
      have hLB := leavesBounded_of_openers hlbA (hleafB l hl)
      have hwsAn : Expr.WScoped n (Expr.fvarTypeD (Expr.fvar l tyA)) :=
        hwsAl.mono (by omega)
      have hwsBn : Expr.WScoped n (bs.getD l default) := (hwsB l hl).mono (by omega)
      -- the two readings, at the frame's own depth
      have hrdA : denoteMeta mp.base2.acval envT ψ n (Expr.fvarTypeD (Expr.fvar l tyA))
          = some ((domsA.getD l default).liftN (n - l) 0) := by
        rw [denoteMeta_lift mp.base2.acval_closed hwsAl n (by omega), hdA l _ hxA]
        rfl
      have hrdB : denoteMeta mp.base2.acval envT ψ n (bs.getD l default)
          = some ((domsB.getD l default).liftN (n - l) 0) := by
        rw [denoteMeta_lift mp.base2.acval_closed (hwsB l hl) n (by omega), hdB l hl]
        rfl
      -- the two gradings, at the frame's own depth
      have hokAl : ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
          WellDenotedV V ρ ((domsA.getD l default).liftN (n - l) 0) := by
        intro ρ hρ
        refine (WellDenotedV_liftN V (n - l) _ 0 ρ).mpr ?_
        obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
        rw [shiftE_consList_take l hzlen]
        exact hokA l hl ρ₂ (zs.take l) (spineFit_take_any hfitZ l)
      have hokBl : ∀ ρ : Nat → V, Sat V domsA.reverse ρ →
          WellDenotedV V ρ ((domsB.getD l default).liftN (n - l) 0) := by
        intro ρ hρ
        refine (WellDenotedV_liftN V (n - l) _ 0 ρ).mpr ?_
        obtain ⟨ρ₂, zs, hzlen, hfitZ, rfl⟩ := sat_reverse_cases hlenA hρ
        rw [shiftE_consList_take l hzlen]
        refine hokB l hl ρ₂ (zs.take l) ?_
        refine spineFit_congr_walk (by rw [List.length_take, List.length_take, hlenA, hlenB]) ?_
          (spineFit_take_any hfitZ l)
        intro j hj
        rw [List.length_take, hlenA] at hj
        have hjl : j < l := by omega
        rw [getD_take_of_lt hjl, getD_take_of_lt hjl, List.take_take,
          show min j l = j from by omega]
        exact IH j hjl (by omega) ρ₂ zs hfitZ
      -- the hop
      have hsat : Sat V domsA.reverse (consList ys ρ₁) := by
        simpa using sat_of_spineFit (Sat_nil V ρ₁) hfitY
      have heq : interp V (consList ys ρ₁) ((domsA.getD l default).liftN (n - l) 0)
          = interp V (consList ys ρ₁) ((domsB.getD l default).liftN (n - l) 0) :=
        ihd (hsubA ▸ hdeq l hl) hwsAn hlbAx hLA hwsBn hlbBx hLB
          hctxA hctxB hrdA hrdB hokAl hokBl (consList ys ρ₁) hsat
      rw [interp_liftN, interp_liftN, shiftE_consList_take l hylen] at heq
      exact heq
  exact spineFit_congr_walk (by rw [hlenA, hlenB]) (fun l hl => key l (by omega) ρ₀ xs hfit) hfit

end TowerFit

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

/-- **The λ-domain bridge at a TWO-STAGE opened frame** — the rule's shape.

The first side is the rule frame's openers (`fvsP ++ fvsF`, opened at
`0` and at `rP`), the second the domains of an `instLamsAt` run at
exactly those openers, and the comparison is the check's own, at the
frame's depth.  Every syntactic premise `openerDoms_spineFit` asks for
is discharged here; what is left for the caller is the two READINGS,
the two GRADINGS and the check. -/
theorem twoStageOpeners_spineFit {envT : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ envT) {ψ : Name → Nat} {fuel rP nF : Nat}
    {tyR crest rhs o₁ o₂ : Expr} {fvsP fvsF : List Expr}
    (hopPref : ConLeche.openPisAtFvars rP tyR 0 = some (fvsP, o₁))
    (hopF : ConLeche.openPisAtFvars nF crest rP = some (fvsF, o₂))
    (hfvR : tyR.hasFvar = false) (hbR : tyR.looseBVarsBounded 0 = true)
    (hwC : Expr.WScoped rP crest) (hbC : crest.looseBVarsBounded 0 = true)
    (hleafC : ∀ lf ∈ crest.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvsP)
    {ldoms : List Expr} {lrest : Expr}
    (hlams : ConLeche.Expr.instLamsAt (fvsP ++ fvsF) rhs = some (ldoms, lrest))
    (hfvRhs : rhs.hasFvar = false) (hbRhs : rhs.looseBVarsBounded 0 = true)
    {domsA domsB : List AnnotTerm}
    (hlenA : domsA.length = rP + nF) (hlenB : domsB.length = rP + nF)
    (hdA : ∀ (l : Nat) (x : Expr), (fvsP ++ fvsF)[l]? = some x →
      denoteMeta mp.base2.acval envT ψ l (Expr.fvarTypeD x) = some (domsA.getD l default))
    (hdB : ∀ l, l < rP + nF →
      denoteMeta mp.base2.acval envT ψ l (ldoms.getD l default)
        = some (domsB.getD l default))
    (hokA : ∀ l, l < rP + nF → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ (domsA.take l) ys → WellDenotedV V (consList ys σ) (domsA.getD l default))
    (hokB : ∀ l, l < rP + nF → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ (domsB.take l) ys → WellDenotedV V (consList ys σ) (domsB.getD l default))
    (hdeq : ∀ l, l < rP + nF →
      ConLeche.isDefEqCore μ envT fuel (rP + nF)
        (((fvsP ++ fvsF).map ConLeche.Expr.fvarTypeD).getD l default)
        (ldoms.getD l default) = .ok true)
    {ρ₀ : Nat → V} {xs : List V} (hfit : SpineFit ρ₀ domsA xs) :
    SpineFit ρ₀ domsB xs := by
  have hwR : Expr.WScoped 0 tyR := Expr.WScoped.of_not_hasFvar hfvR
  have hlenP : fvsP.length = rP := ConLeche.Verify.openPisAtFvars_length _ hopPref
  have hlenF : fvsF.length = nF := ConLeche.Verify.openPisAtFvars_length _ hopF
  have hsplen : (fvsP ++ fvsF).length = rP + nF := by
    rw [List.length_append, hlenP, hlenF]
  have hwPref : ∀ x ∈ fvsP, Expr.WScoped rP x := by
    have hq := (ConLeche.openPisAtFvars_WScoped rP tyR 0 hopPref hwR).1
    rw [Nat.zero_add] at hq
    exact hq
  have hbPref : ∀ x ∈ fvsP, (Expr.fvarTypeD x).looseBVarsBounded 0 = true :=
    (ConLeche.Verify.openPisAtFvars_bounded _ hopPref hbR).2
  have hbField : ∀ x ∈ fvsF, (Expr.fvarTypeD x).looseBVarsBounded 0 = true :=
    (ConLeche.Verify.openPisAtFvars_bounded _ hopF hbC).2
  have hwField : ∀ x ∈ fvsF, Expr.WScoped (rP + nF) x :=
    (ConLeche.openPisAtFvars_WScoped nF crest rP hopF hwC).1
  have hleafPref : ∀ a ∈ fvsP, ∀ lf ∈ a.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvsP := by
    intro a ha lf hlf
    rcases ConLeche.Verify.openPisAtFvars_leaves rP hopPref lf (Or.inr ⟨a, ha, hlf⟩) with hq | hq
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hfvR] at hq; exact nomatch hq
    · exact hq
  have hleafField : ∀ a ∈ fvsF, ∀ lf ∈ a.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvsP ++ fvsF := by
    intro a ha lf hlf
    rcases ConLeche.Verify.openPisAtFvars_leaves nF hopF lf (Or.inr ⟨a, ha, hlf⟩) with hq | hq
    · exact List.mem_append_left _ (hleafC lf hq)
    · exact List.mem_append_right _ hq
  have hshape : ∀ (l : Nat) (x : Expr), (fvsP ++ fvsF)[l]? = some x →
      ∃ ty, x = Expr.fvar l ty := by
    intro l x hx
    obtain ⟨ty, hty⟩ := blockRuleOpeners_index hopPref hopF l x hx
    exact ⟨ty, by rw [hty, Nat.zero_add]⟩
  have hws : ∀ x ∈ fvsP ++ fvsF, Expr.WScoped (rP + nF) x := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hwPref x hx).mono (by omega)
    · exact hwField x hx
  have hlbA : ∀ x ∈ fvsP ++ fvsF, (Expr.fvarTypeD x).looseBVarsBounded 0 = true := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hbPref x hx
    · exact hbField x hx
  have hfvAll : ∀ x ∈ fvsP ++ fvsF, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := hshape k x hk
    have hq := hlbA _ hx
    simp only [ConLeche.Expr.fvarTypeD] at hq
    simp [ConLeche.Expr.looseBVarsBounded]
  have hleafAll : ∀ a ∈ fvsP ++ fvsF,
      ∀ lf ∈ a.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvsP ++ fvsF := by
    intro a ha lf hlf
    rcases List.mem_append.mp ha with h1 | h1
    · exact List.mem_append_left _ (hleafPref a h1 lf hlf)
    · exact hleafField a h1 lf hlf
  have hleafA : ∀ (l : Nat) (x : Expr), (fvsP ++ fvsF)[l]? = some x →
      ∀ lf ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvsP ++ fvsF := by
    intro l x hx lf hlf
    obtain ⟨ty, rfl⟩ := hshape l x hx
    refine hleafAll _ (List.mem_of_getElem? hx) lf ?_
    simp only [ConLeche.Expr.fvarLeaves]
    exact List.mem_cons_of_mem _ hlf
  have hlenLd : ldoms.length = rP + nF := by
    rw [ConLeche.Verify.instLamsAt_length _ hlams, hsplen]
  have hwsB : ∀ l, l < rP + nF → Expr.WScoped l (ldoms.getD l default) := by
    intro l hl
    obtain ⟨x, hx⟩ : ∃ x, ldoms[l]? = some x :=
      ⟨ldoms[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    have hq := ConLeche.Verify.instLamsAt_index_WScoped (d := 0) _ hlams
      (Expr.WScoped.of_not_hasFvar hfvRhs)
      (fun k a hk => by
        obtain ⟨ty, rfl⟩ := hshape k a hk
        have hq : k < rP + nF ∧ Expr.WScoped k ty := by
          simpa [Expr.WScoped] using hws _ (List.mem_of_getElem? hk)
        have hq2 : k < 0 + k + 1 ∧ Expr.WScoped k ty := ⟨by omega, hq.2⟩
        simpa [Expr.WScoped] using hq2) l x hx
    rw [Nat.zero_add] at hq
    rw [List.getD_eq_getElem?_getD, hx]
    exact hq
  have hleafB : ∀ l, l < rP + nF →
      ∀ lf ∈ (ldoms.getD l default).fvarLeaves, Expr.fvar lf.1 lf.2 ∈ fvsP ++ fvsF := by
    intro l hl lf hlf
    obtain ⟨x, hx⟩ : ∃ x, ldoms[l]? = some x :=
      ⟨ldoms[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    rw [List.getD_eq_getElem?_getD, hx] at hlf
    rcases ConLeche.Verify.instLamsAt_leaves _ hlams lf
      (Or.inl ⟨x, List.mem_of_getElem? hx, hlf⟩) with hq | hq
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hfvRhs] at hq; exact nomatch hq
    · obtain ⟨a, ha, hla⟩ := hq
      exact hleafAll a ha lf hla
  have hlbB : ∀ l, l < rP + nF → (ldoms.getD l default).looseBVarsBounded 0 = true := by
    intro l hl
    obtain ⟨x, hx⟩ : ∃ x, ldoms[l]? = some x :=
      ⟨ldoms[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    rw [List.getD_eq_getElem?_getD, hx]
    exact (ConLeche.Verify.instLamsAt_bounded _ hlams hbRhs hfvAll).1 x
      (List.mem_of_getElem? hx)
  exact openerDoms_spineFit (fuel := fuel) hμ mp hsplen hshape hws hleafA hlbA
    hwsB hleafB hlbB hlenA hlenB hdA hdB hokA hokB
    (fun l hl => hdeq l (by omega)) hfit

end TwoStage

/-! ### §6c The tower fit AT THE RUN

Every input `twoStageOpeners_spineFit` asks for is a run fact of the
rule's own frame, except these, each produced in another file:

* **`hdF`** — the FIELD openers' stored types read to
  `blockRuleFdomsAV`'s entries at their own depths:
  `blockRuleFdomsAV_eq`'s SECOND conjunct (`BlockRecData.lean`), which
  is `readOpenedDoms_eq`'s own hypothesis;
* **`hokF`** — the field domains are graded along their own fitting
  spines: `blockRuleHokF_of_run` (below);
* the ENVIRONMENT CROSSING.  The λ-domain comparison runs at `envC`;
  the rule's reading, and with it the tower's domains, is at the
  CONSED environment.  `denoteMeta` is an EQUATION across the
  recursors' cons at a `ConstsBound envC` subject
  (`blockRecDenote_cross_eq`, `BlockRecData.lean`), the two literal
  guards being the recursor stage's own NAME check.  What it leaves is
  the syntactic `ConstsBound envC (ldoms.getD l default)` — NOT
  `checkBlockRecK_facts`' `constsResolve`, which is at
  `consBlockRecsBare` (the right-hand side mentions the recursors by
  design).  The rule stage's own domain guard supplies it (§7).

The PREFIX half needs no premise at all: its readings are
`blockRulePdomsAV_reads` and its gradings `blockRulePdomsAV_graded`,
both already at the run. -/

section TowerFitRun

variable {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **`hokF`, AT THE RUN** — the tower fit's FIELD-grading input, in
the `blockRuleFdomsAV` spelling the fit asks it in.

`blockRuleFseg_of_run` (`BlockRecPreRun.lean` §40.9) concludes exactly
this at the constructors' stage's own binder data lifted to the rule's
frame, and `blockRuleFdomsAV_eq_liftDoms` is the identity between that
spelling and `blockRuleFdomsAV`, so the proof is a rewrite. -/
theorem blockRuleHokF_of_run (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {cvTa : ConstantVal} {caps : ConLeche.IndCaps}
    (hcvTa : cvTas[p.toBlockShape.recTgtAt c]? = some cvTa)
    (hfT : envC.find? cvTa.name = some (.indInfo cvTa caps))
    {nFull : Nat} {resSortT : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mpC.base2 cvTa nFull resSortT pps) (hle : p.nP ≤ nFull)
    {env₀ : Env} {T : Name} {Tof : Nat → Name} {nIdxOf : Nat → Nat} {lps : List Name}
    {nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List ConLeche.RecFieldKind}
    {fvsP xFvs : List Expr} {xrest : Expr}
    {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (hcd : BlockCtorDataI mpC.base2 env₀ T Tof nIdxOf lps cA.1 p.nP cA.2 nIdx resSort
      isProp large idxArgs ds Es srcs ks fvsP xFvs xrest Eiss tss)
    (hCf : cA.1.type.hasFvar = false) (ψ : Name → Nat) {bodyC : AnnotTerm}
    (hwd : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV (ds ψ) bodyC))
    (hframes : ∀ ρ : Nat → V, Sat V (((pps ψ).take p.nP).map (·.2.2)).reverse ρ ↔
      Sat V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    {o : Nat} (ho : p.toBlockShape.rulePrefixAt c = p.nP + o) :
    ∀ q, q < cA.2 → ∀ (σ : Nat → V) (xs ys : List V),
      SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      SpineFit (consList xs σ)
        ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).take q) ys →
      WellDenotedV V (consList ys (consList xs σ))
        ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD q default) := by
  rw [blockRuleFdomsAV_eq_liftDoms h hr hcA hrhs hcd hCf (by omega) ho ψ]
  exact blockRuleFseg_of_run hμ mpC h hr ψ hcvTa hfT hFD hle hwd (hcd.len ψ) hframes ho

/-- **THE TOWER FIT, AT THE RUN** — `BlockRuleDataB`'s FIFTH conjunct
from its FIRST.

The fit the block's representation produces is of the OPENERS' domain
readings (`blockRulePdomsAV ++ blockRuleFdomsAV`); the conjunct asks
for a fit of the RULE's own λ-domains, and nothing identifies the two
syntactically.  The `checkBlockDefEqList` `blockRuleData_run` carries
compares them binder by binder at the rule frame's depth, and
`twoStageOpeners_spineFit` is the transfer.

`hdF` and `hokF` are the inputs other stages produce (§6c); everything
else is this run's own.  The statement is `w`-FREE: the evidence is a
grading against the rule's λ-tower, never a membership in a carrier. -/
theorem blockRuleTowerFit_run {env₃ : Env} {acv : Name → (Name → Nat) → AnnotTerm}
    (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {ψ : Name → Nat} {Ra : AnnotTerm}
    (hread : denoteMeta acv env₃ ψ 0 rhs = some Ra)
    (hokRa : ∀ σ : Nat → V, WellDenotedV V σ Ra)
    {ldoms : List Expr} {lrest : Expr}
    (hlams : ConLeche.Expr.instLamsAt
        (blockRulePrefFvs p.toBlockShape rs c ++ blockRuleFieldFvs p.toBlockShape rs c i)
        rhs = some (ldoms, lrest))
    (hcross : ∀ l, l < p.toBlockShape.rulePrefixAt c + cA.2 →
      denoteMeta mpC.base2.acval envC ψ l (ldoms.getD l default)
        = denoteMeta acv env₃ ψ l (ldoms.getD l default))
    (hdF : ∀ (l : Nat) (x : Expr), (blockRuleFieldFvs p.toBlockShape rs c i)[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + l)
          (Expr.fvarTypeD x)
        = some ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD l default))
    (hokF : ∀ q, q < cA.2 → ∀ (σ : Nat → V) (xs ys : List V),
      SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      SpineFit (consList xs σ)
        ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).take q) ys →
      WellDenotedV V (consList ys (consList xs σ))
        ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD q default))
    {ρ : Nat → V} {as : List V}
    (hfit : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i) as) :
    ∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A →
      lds.length = p.toBlockShape.rulePrefixAt c + cA.2 →
      SpineFit ρ (lds.map (·.2)) as := by
  intro lds A hlam hldslen
  -- the run's own peel, and the tower the reading determines
  obtain ⟨o₁, cpref, rbs, body, ldoms', lrest', hopPref, hinst, hopF, -, hlams', -, hg2len, hg2⟩ :=
    blockRuleData_run h hr hcA hrhs
  have hldEq : ldoms' = ldoms :=
    congrArg Prod.fst (Option.some.inj (hlams'.symm.trans hlams))
  rw [hldEq] at hg2 hg2len
  obtain ⟨ldoms₀, lrest₀, lds₀, A₀, hlams₀, hlam₀, hlen₀, hcore₀, hdoms₀⟩ :=
    blockRuleTower_run h hr hcA hrhs hread
  have hld₀ : ldoms₀ = ldoms :=
    congrArg Prod.fst (Option.some.inj (hlams₀.symm.trans hlams))
  rw [hld₀] at hdoms₀
  obtain ⟨rfl, rfl⟩ : lds = lds₀ ∧ A = A₀ :=
    mkLamsAV_length_inj (by rw [hldslen, hlen₀]) (hlam ▸ hlam₀)
  -- the frame's two openings, and the constructor telescope's syntax
  have hlenP : (blockRulePrefFvs p.toBlockShape rs c).length
      = p.toBlockShape.rulePrefixAt c := ConLeche.Verify.openPisAtFvars_length _ hopPref
  have hlenF : (blockRuleFieldFvs p.toBlockShape rs c i).length = cA.2 :=
    ConLeche.Verify.openPisAtFvars_length _ hopF
  have hlenPd : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hlenFd : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).length
      = cA.2 := by
    rw [blockRuleFdomsAV, readOpenedDoms_length (fun l x hx => ⟨_, hdF l x hx⟩), hlenF]
  obtain ⟨hwR, hbR⟩ := checkBlockRecK_tyClosed h hr
  obtain ⟨hfvR, -, -, -, hallRhs⟩ :=
    ConLeche.checkBlockRecK_facts h r (List.mem_of_getElem? hr)
  obtain ⟨hfvRhs, -, -, hbRhs⟩ := hallRhs rhs (List.mem_of_getElem? hrhs)
  have hwPref : ∀ x ∈ blockRulePrefFvs p.toBlockShape rs c,
      Expr.WScoped (p.toBlockShape.rulePrefixAt c) x := by
    have hq := (ConLeche.openPisAtFvars_WScoped _ r.1.type 0 hopPref hwR).1
    rw [Nat.zero_add] at hq
    exact hq
  have hfvPref : ∀ x ∈ blockRulePrefFvs p.toBlockShape rs c,
      x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨k, hk⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index _ _ _ hopPref k _ hk
    have hq := (ConLeche.Verify.openPisAtFvars_bounded _ hopPref hbR).2 _ hx
    simp only [ConLeche.Expr.fvarTypeD] at hq
    simp [ConLeche.Expr.looseBVarsBounded]
  have hleafPref : ∀ a ∈ blockRulePrefFvs p.toBlockShape rs c,
      ∀ lf ∈ a.fvarLeaves, Expr.fvar lf.1 lf.2 ∈ blockRulePrefFvs p.toBlockShape rs c := by
    intro a ha lf hlf
    rcases ConLeche.Verify.openPisAtFvars_leaves _ hopPref lf (Or.inr ⟨a, ha, hlf⟩) with hq | hq
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hfvR] at hq; exact nomatch hq
    · exact hq
  have hwC : Expr.WScoped (p.toBlockShape.rulePrefixAt c)
      (blockRuleCrest p.toBlockShape rs c i) :=
    (ConLeche.instPisAt_WScoped _ cA.1.type hinst (Expr.WScoped.of_not_hasFvar hCf)
      (fun a ha => hwPref a (List.mem_of_mem_take ha))).2
  have hbC : (blockRuleCrest p.toBlockShape rs c i).looseBVarsBounded 0 = true :=
    (ConLeche.Verify.instPisAt_bounded _ hinst hCb
      (fun a ha => hfvPref a (List.mem_of_mem_take ha))).2
  have hleafC : ∀ lf ∈ (blockRuleCrest p.toBlockShape rs c i).fvarLeaves,
      Expr.fvar lf.1 lf.2 ∈ blockRulePrefFvs p.toBlockShape rs c := by
    intro lf hlf
    rcases ConLeche.Verify.instPisAt_leaves _ hinst lf (Or.inr hlf) with hq | hq
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hCf] at hq; exact nomatch hq
    · obtain ⟨a, ha, hlfa⟩ := hq
      exact hleafPref a (List.mem_of_mem_take ha) lf hlfa
  -- the openers' readings, prefix and field
  have hdA : ∀ (l : Nat) (x : Expr),
      (blockRulePrefFvs p.toBlockShape rs c ++ blockRuleFieldFvs p.toBlockShape rs c i)[l]?
        = some x →
      denoteMeta mpC.base2.acval envC ψ l (Expr.fvarTypeD x)
        = some ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD l default) := by
    intro l x hx
    rcases Nat.lt_or_ge l (blockRulePrefFvs p.toBlockShape rs c).length with hlt | hge
    · rw [List.getElem?_append_left hlt] at hx
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      exact blockRulePdomsAV_reads hμ mpC h hr ψ hopPref l x hx
    · rw [List.getElem?_append_right hge, hlenP] at hx
      rw [hlenP] at hge
      have hq := hdF (l - p.toBlockShape.rulePrefixAt c) x hx
      rw [show p.toBlockShape.rulePrefixAt c + (l - p.toBlockShape.rulePrefixAt c) = l from
        by omega] at hq
      have hgetD : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD l default
          = (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD
              (l - p.toBlockShape.rulePrefixAt c) default := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [hlenPd]; omega), hlenPd]
      rw [hgetD]
      exact hq
  -- the openers' gradings, prefix and field
  have hokA : ∀ l, l < p.toBlockShape.rulePrefixAt c + cA.2 → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).take l) ys →
      WellDenotedV V (consList ys σ)
        ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD l default) := by
    intro l hl σ ys hys
    rcases Nat.lt_or_ge l (p.toBlockShape.rulePrefixAt c) with hlt | hge
    · rw [List.take_append_of_le_length (by omega)] at hys
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
        ← List.getD_eq_getElem?_getD]
      exact blockRulePdomsAV_graded hμ mpC h hr ψ l hlt σ ys hys
    · obtain ⟨q, rfl⟩ : ∃ q, l = p.toBlockShape.rulePrefixAt c + q :=
        ⟨l - p.toBlockShape.rulePrefixAt c, by omega⟩
      have htk : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).take
              (p.toBlockShape.rulePrefixAt c + q)
          = blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).take q := by
        rw [← hlenPd, List.take_append, List.take_of_length_le (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left]
      have hgetD : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD
              (p.toBlockShape.rulePrefixAt c + q) default
          = (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i).getD q default := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [hlenPd]; omega), hlenPd, Nat.add_sub_cancel_left]
      rw [htk] at hys
      obtain ⟨ys₁, ys₂, rfl, hy1, hy2⟩ := spineFit_append_inv hys
      rw [hgetD, consList_append]
      exact hokF q (by omega) σ ys₁ ys₂ hy1 hy2
  -- the tower's domains: readings at `envC` through the crossing, gradings off the tower
  have hlenLd : ldoms.length = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [ConLeche.Verify.instLamsAt_length _ hlams, List.length_append, hlenP, hlenF]
  have hdB : ∀ l, l < p.toBlockShape.rulePrefixAt c + cA.2 →
      denoteMeta mpC.base2.acval envC ψ l (ldoms.getD l default)
        = some ((lds.map (·.2)).getD l default) := by
    intro l hl
    obtain ⟨x, hx⟩ : ∃ x, ldoms[l]? = some x :=
      ⟨ldoms[l]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    rw [hcross l hl, List.getD_eq_getElem?_getD, hx]
    exact hdoms₀ l x hx
  have hokB : ∀ l, l < p.toBlockShape.rulePrefixAt c + cA.2 → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((lds.map (·.2)).take l) ys →
      WellDenotedV V (consList ys σ) ((lds.map (·.2)).getD l default) :=
    fun l hl σ ys hys =>
      mkLamsAV_doms_graded (b := A) (by rw [← hlam]; exact hokRa σ)
        (by rw [hldslen]; exact hl) hys
  exact twoStageOpeners_spineFit (fuel := F) hμ mpC hopPref hopF hfvR hbR hwC hbC hleafC
    hlams hfvRhs hbRhs
    (by rw [List.length_append, hlenPd, hlenFd])
    (by rw [List.length_map, hldslen]) hdA hdB hokA hokB
    (fun l hl => hg2 l (by rw [List.length_map, List.length_append, hlenP, hlenF]; exact hl))
    hfit

end TowerFitRun

/-! ## 3d. THE COMPOSITION — a theorem whose CONCLUSION is
`BlockRuleDataB`

Five of the obligation's six statements have a theorem each (§3, §3b)
and the sixth pair is the rule stage's.  `blockRuleDataB_of_residue`
composes them: it fixes the four syntactic components at the route's
own readings (`blockRulePdomsAV`/`blockRuleFdomsAV`/`blockRuleEsAV`/
`blockRuleMkAV`, which is what `declBlock_data`'s existential is
instantiated at), takes the residue and the tower fit as the SINGLE
premise `BlockRuleResidueB`, and discharges the other three conjuncts
from the run.

Every ψ-indexed premise is bounded by the contract's own telescope —
the level assignment a conjunct is asked at is `Level.substFn φ
r.1.levelParams us` for a `us` of the recursor's own length, never an
arbitrary `ψ`.  **The guard is `ℓ ≠ 0`**: conjuncts ① and ② are
REFUTABLE at `d.w ψ = 0` with `ℓ = 0` (§4, §5) and at `ℓ = 0` the
contract is not used at all, while at `ℓ ≠ 0` the `d.w ψ = 0` case is
closed by §2b — so what the guard brings with it is the
large-elimination counting guard's two facts, `hlarge` and `hct1`,
which are the KERNEL's.  The rule's INDEX PIN, which §2b also needs,
is produced here (`blockRuleIdxPin_run`) out of the contract's own
`IotaIndexPin` premise. -/

/-- **`BlockRuleDataB` from the run and ONE residue premise.**

The three data conjuncts are `blockRuleHsp_field_run`,
`blockRuleHes_run` and `blockRuleHmk_run`; their own premises `hlv`,
`hqs` and `hfq` are `blockRuleLevelAgree` and `blockRuleCtorFit_run`
at the contract's `hψ` and `hfitC` (§3c), so the contract's telescope
supplies them.  The fourth and fifth arrive together as `hres`, and
the fourth's β-reduction is paid here (`blockRuleHRa_tower_run`, at
the reading `hread` and the grading `hokRa` the stage's own
`blockRuleRhs_read_run` produces) — so what `hres` carries is the
TOWER's core equation and the tower's fit, and nothing about the
applied form.

The four syntactic components are fixed by `hpd`/`hfdD`/`hesD`/`hmkD`
rather than written into the statement: `declBlock_data`'s existential
is instantiated at exactly these readings, and the equations keep the
signature readable.

What is left as a hypothesis is what belongs to another stage: the
identifications of the rule's field domains and index expressions with
the datum's (`hfd`, `hes`), the recursor type's split (`hsplit`,
`BlockRecSplitAt`), the constructors' stage's parameter clauses
(`hlenP`, `hparamsC`), the block's own `d.nP = p.nP`, and the
`w`-guard. -/
theorem blockRuleDataB_of_residue (hM : BlockModelAt mpC.base2 names d)
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hpd : pdoms0 = fun ψ c => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
    (hfdD : fdoms0 = fun ψ c i => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
    (hesD : es0 = fun ψ c i => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
    (hmkD : mk0 = fun ψ c i => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
    {ctorTy : (Name → Nat) → AnnotTerm} {φ : Name → Nat} {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[j]? = some r)
    {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {rl : ConLeche.RecRule} (hplain : ConLeche.RecRule.fire rl = .plain)
    {mem : Nat → Nat} {jc : Nat}
    (hcj : (d.ctorsM (mem j))[jc]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem j) jc cA)
    (hlps : cA.1.levelParams = p.lps) (hdnP : d.nP = p.nP)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt j)
    (hmemk : mem j < d.k)
    (htgt : ∀ l, l < cA.2 → d.tgts (mem j) jc l < d.k)
    {K : Nat} (hjK : j < K)
    (hctorRead : ∀ ψ : Name → Nat,
      denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some (ctorTy ψ))
    (hfd : ∀ us : List Level, us.length = r.1.levelParams.length →
      blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
          (Level.substFn φ r.1.levelParams us) j i
        = liftDomsK (p.toBlockShape.rulePrefixAt j - d.nP) 0
            ((d.Fss (mem j) (Level.substFn φ r.1.levelParams us)).getD jc []))
    (hes : ∀ us : List Level, us.length = r.1.levelParams.length →
      blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC
          (Level.substFn φ r.1.levelParams us) j i
        = ((d.Ess (mem j) (Level.substFn φ r.1.levelParams us)).getD jc []).map
            (·.liftN (p.toBlockShape.rulePrefixAt j - d.nP) cA.2))
    (hlenP : ∀ us : List Level, us.length = r.1.levelParams.length →
      (d.params (Level.substFn φ r.1.levelParams us)).length = d.nP)
    (hparamsC : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ σ : Nat → V,
      Sat V (d.params (Level.substFn φ r.1.levelParams us)).reverse σ
        ↔ Sat V (((d.dsF (mem j) jc (Level.substFn φ r.1.levelParams us)).take d.nP).map
            (·.2.2)).reverse σ)
    (hsplit : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ ρ : Nat → V,
      BlockRecSplitAt V mpC.base2 d (Level.substFn φ r.1.levelParams us) K
        p.toBlockShape.rulePrefixAt mem
        (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) c') ρ)
    -- **THE GUARD** is the contract's own (`BlockRuleDataB`'s
    -- per-valuation `ℓ ≠ 0`, at the CHECKED elimination level
    -- `structElimLevel p.elim p.large`), and under it the COUNTING
    -- guard's two facts.  `hlarge`/`hct1` are the KERNEL's, in the
    -- dispatch's own spelling (`hK1 : ℓ ≠ 0 → d.w ψ = 0 →
    -- rs.length = 1` is the same guard's one-member half).
    (hlarge : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w (Level.substFn φ r.1.levelParams us) = 0 → d.large = true)
    (hct1 : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w (Level.substFn φ r.1.levelParams us) = 0 → (d.ctorsM (mem j)).length ≤ 1)
    (hread : ∀ us : List Level, us.length = r.1.levelParams.length →
      denoteMeta (blockRecAcv mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)
          (Level.substFn φ r.1.levelParams us) 0 rhs
        = some (blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
            (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) rhs
            (Level.substFn φ r.1.levelParams us)))
    (hokRa : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ ρ : Nat → V,
      WellDenotedV V ρ (blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) rhs
          (Level.substFn φ r.1.levelParams us)))
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hdF : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ (l : Nat) (x : Expr), (blockRuleFieldFvs p.toBlockShape rs j i)[l]? = some x →
        denoteMeta mpC.base2.acval envC (Level.substFn φ r.1.levelParams us)
            (p.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
              (Level.substFn φ r.1.levelParams us) j i).getD l default))
    (hokF : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ q, q < cA.2 → ∀ (σ : Nat → V) (vs ws : List V),
        SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) j) vs →
        SpineFit (consList vs σ)
          ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).take q) ws →
        WellDenotedV V (consList ws (consList vs σ))
          ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).getD q default))
    (hres : BlockRuleResidueB (V := V) mpC p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs) :
    BlockRuleDataB (V := V) mpC p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs := by
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC
  have hnPd : d.nP ≤ p.toBlockShape.rulePrefixAt j := by rw [hdnP]; exact hnP
  have hlv := blockRuleLevelAgree hplain hψ
  obtain ⟨hqs, hfq⟩ := blockRuleCtorFit_run (d := d) hcj hcf hlv (hlenP us hus)
    (hparamsC us hus) (by rw [hyl, hdnP]) (hctorRead _) hfitC
  have hbody :=
    hres us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC
  -- THE INDEX PIN, in the model's currency (the contract's `hidx`):
  -- the squash arm's tie between the two frames
  have hmN : mem j < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : jc < (d.ctorsM (mem j)).length := (List.getElem?_eq_some_iff.mp hcj).1
  obtain ⟨-, hidxS, -⟩ := blockRecSplit_at_rule (d := d) hμ mpC h hr
    (Level.substFn φ r.1.levelParams us) hxl hfitR hjK (hsplit us hus ρ)
  have hrPle : p.toBlockShape.rulePrefixAt j ≤ p.toBlockShape.majorIdxAt j :=
    blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  have hEssD : (d.Ess (mem j) (Level.substFn φ r.1.levelParams us)).getD jc []
      = d.esF (mem j) jc (Level.substFn φ r.1.levelParams us) :=
    essOfR_fixCtorDataList_getD hcj
  have hnI : (d.esF (mem j) jc (Level.substFn φ r.1.levelParams us)).length
      = p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j := by
    have hq := (hM.resIdxFit (Level.substFn φ r.1.levelParams us) _
      (d.satOfSpine hqs) (mem j) hmN jc hjl _ hfq).length_eq
    rw [List.length_map, hEssD] at hq
    rw [hq, ← hidxS.length_eq, List.length_map, List.length_drop, hxl]
  have hpin := blockRuleIdxPin_run hcj hcf hlv (by rw [hyl, hdnP]) hxl hrPle hnI
    (hctorRead _) hfitC (by rw [hdnP]; exact hidx)
  subst hpd; subst hfdD; subst hesD; subst hmkD
  -- the FIRST conjunct, and the FIFTH from it through the λ-domain comparison
  have hsp1 : SpineFit ρ
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) j
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i)
      ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
        ++ (ys.drop p.nP).map (interp V ρ)) := by
    have hq := blockRuleHsp_field_run (i := i) hM hμ h hr hcj hcf (hfd us hus) hmemk hnPd
      htgt hlv (fun h0 => hlarge us hus hℓ h0) (fun h0 => hct1 us hus hℓ h0)
      (hparamsC us hus) hxl hfitR hjK (hsplit us hus ρ) hqs hfq (fun _ => hpin)
    rwa [hdnP] at hq
  obtain ⟨-, -, -, -, ldoms, lrest, -, -, -, -, hlams, hcbLdR, -, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  have htow := blockRuleTowerFit_run hμ mpC h hr hcA hrhs hCf hCb (hread us hus)
    (hokRa us hus) hlams
    (fun l hl => blockRecDenote_cross_eq h _ l _ (hcbLdR l hl))
    (hdF us hus) (hokF us hus) hsp1
  refine ⟨hsp1, ?_, ?_, ?_, htow⟩
  · have hq := blockRuleHes_run hM hμ h hr hcj hcf (hes us hus) hmemk hnPd htgt hlv
      (fun h0 => hlarge us hus hℓ h0) (fun h0 => hct1 us hus hℓ h0) (hparamsC us hus)
      hxl hfitR hjK (hsplit us hus ρ) hqs hfq (fun _ => hpin)
    rwa [hdnP] at hq
  · have hq := blockRuleHmk_run hM hμ h hr hcA hrhs hcj hcf hlps hdnP hnP (hfd us hus)
      hmemk htgt hlv (fun h0 => hlarge us hus hℓ h0) (fun h0 => hct1 us hus hℓ h0)
      (hparamsC us hus) hxl hfitR hjK (hsplit us hus ρ) hqs hfq (fun _ => hpin)
    rwa [hdnP] at hq
  · intro a hleaf
    exact blockRuleHRa_tower_run h hr hcA hrhs (hread us hus) (hokRa us hus ρ) htow
      (hbody a hleaf)

/-! ## 4. The FIT conjunct is FALSE at a `Prop`-valued block with `ℓ = 0`

`BlockRuleDataB`'s first conjunct — the recursor's prefix and the
constructor's fields fit the rule's domains — is **refutable** at
`d.w ψ = 0`; the `hw` of §2 is not a convenience of the proof.

The rule is `paramsBlind`, so the only thing that ties the
constructor's parameter spine to the recursor's is the MAJOR
PREMISE's membership.  At `d.w ψ ≠ 0` that membership is worth the
whole tie (`mkInj`).  At `d.w ψ = 0` every value in the block is the
point (`BlockModelAt.mkZero`), so the membership is worth NOTHING: a
constructor built at one parameter spine lies in the carrier at
every other.

**The witness is `Exists`**, and it is in every real stream.
`Exists.{u} {α : Sort u} (p : α → Prop) : Prop` has `nP = 2`, no
indices, one constructor `Exists.intro (w : α) (h : p w)`, and
`d.w ψ = 0`.  Take

* `xs = [Bool, q, motive, minor]` — the recursor's rule prefix at
  `α := Bool` (`rP = nP + 1 + 1 = 4 = mI`, no indices);
* `ys = [Nat, r, 5, h]` — the constructor at `α := Nat`.

`hfitC` holds: `5 ∈ ⟦Nat⟧`, `h ∈ ⟦r 5⟧`.  `hfitR` holds too: the
major's domain is `⟦Exists q⟧`, a `Prop`-set, and the major's value is
`d.inj ψ 0 0 [5, pt] = pt` by `mkZero`, which lies in it as soon as
`∃ b : Bool, q b` — pick `q` satisfiable.  `IotaIndexPin` is vacuous
(`mI = rP`).  And `hψ` is about LEVELS, not about values.  But the
conjunct's field half then asks

    5 ∈ˢ interp V (consList [⟦Bool⟧, ⟦q⟧, …] ρ) (the field `w`'s
        domain, which is the parameter `α`)  =  5 ∈ˢ ⟦Bool⟧

which is false.  No premise of `BlockRuleDataB` excludes it.

**Hence the contract's guard `ℓ ≠ 0`.**  At `ℓ = 0` the ι equation is
an equation between proofs and the rule contract is not used at all.
At `ℓ ≠ 0` and `d.w ψ = 0` the large-elimination COUNTING guard
(`blockLargeElimAllowed`, which requires `p.large`) forces the
generated large shape and at most one constructor, and §2b closes the
fit there by the SUBSINGLETON criterion — `j' = j` without
injectivity, both field spines the source spine.
`blockRuleChainFit_any` is the one case distinction. -/

/-! ## 5. The INDEX READING is FALSE at a `Prop`-valued block with `ℓ = 0`
too, and the witness is in Mathlib

`BlockRuleDataB`'s second conjunct — the rule's index expressions read
to the recursor's own index arguments — is **refutable** at
`d.w ψ = 0`, by a DIFFERENT witness from §4's (`Exists` has no
indices, so there the conjunct is `[] = []`).  The row needs a block
with an INDEX whose constructor-side expression is a PARAMETER, and a
SECOND constructor to keep the carrier inhabited at a *different*
index.

**The witness is `Relation.ReflTransGen`.**

```
inductive ReflTransGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflTransGen r a a
  | tail : ReflTransGen r a b → r b c → ReflTransGen r a c
```

`nP = 3` (`α`, `r`, `a`), one index, `d.w ψ = 0`, and `refl`'s
conclusion's index argument IS the parameter `a`.  Fire the `refl`
rule at `α := Bool`, `r := (· ≠ ·)`:

* `xs = [Bool, r, true, motive, m_refl, m_tail, false]` — the
  recursor's prefix at `a := true` (`motive := fun _ _ => True` and
  the two minors trivial), with the INDEX argument `i_R = false`;
* `ys = [Bool, r, false]` — the constructor at `a := false`.

Every premise holds.  `hfitC` is three parameter memberships.
`hfitR`: the major's value is `d.inj ψ 0 0 [] = pt` (`mkZero`), and
the major's domain is the carrier at the RECURSOR's parameters and
index, `⟦ReflTransGen r true false⟧`, which is inhabited — by `tail`,
since `true ≠ false`.  `IotaIndexPin` holds: `refl`'s residual is
`ReflTransGen r false false` and its trailing argument reads to
`false = i_R`.  `hψ` is about levels.  But the conjunct then asks

    interp (consList (x⃗ ++ f⃗) ρ) ⟦a⃗⟧  =  (xs.drop rP).map (interp ρ)

whose left side reads the parameter `a` at the RECURSOR's frame —
`true` — and whose right side is `[false]`.

**It is the same hole as §4's, one conjunct along.**  At `d.w ψ = 0`
the major's membership says only that SOME constructor's `ChainFit`
holds at the recursor's index tuple — here `tail`'s, not `refl`'s;
`blockCarrier_case` delivers a `j'`, and only `mkInj` makes `j' = j`.

Both witnesses are `ℓ = 0` blocks (`Exists`'s field `w` is neither a
proof nor an argument of the conclusion; `ReflTransGen` has two
constructors), so the `ℓ ≠ 0` guard excludes them.  At `ℓ ≠ 0` the row
is closed like the fit (`blockRuleHes_run` through
`blockRuleChainFit_any`): one constructor makes `blockCarrier_case`'s
`j'` this rule's own with no `mkInj`, and the FIELD spine is pinned by
the subsingleton criterion at the two frames (§2b), the index values
on the two sides being the rule's own INDEX PIN
(`blockRuleIdxPin_run`). -/

/-! ## 7. The rule's λ-DOMAINS must be `ConstsBound envC`, and the
checker guards it

The ENVIRONMENT CROSSING (§6c) is an EQUATION across the recursors'
cons at any `ConstsBound envC` subject (`blockRecDenote_cross_eq`),
because `denoteMeta_envExtend` is one and the recursor stage's NAME
check (`ConLeche.checkBlockRecK_reserved`) is exactly what makes the
two literal guards agree.  What the crossing needs is the syntactic
fact

    ∀ l, l < rP + nF → ConstsBound envC (ldoms.getD l default)

**and without a guard of its own that fact is false for some accepted
streams.**  The rule's right-hand side is annotated and
consts-resolved at the RULE-LESS recursor environment
(`checkBlockRecK_facts`: `rhs.constsResolve (consBlockRecsBare …) =
true`), because a rule mentions the recursors by design.  Its BODY is
forced back into `envC`: `abstractIh` fails unless every recursor
occurrence is a call on a recursive field, and the residue is then
typed at `envT = envC`.  Its λ-BINDER DOMAINS would be forced by
nothing but the comparison
`checkBlockDefEqList opsT envT (rP + nF) (openers' types) ldoms` — and
defeq does not preserve syntax.  Take a rule

    fun (x₁ : D₁) … (x_rP : D_rP)
        (f₁ : (fun _ : T_rec => A₁) C_rec) (f₂ : A₂) … => body

where `T_rec` is the recursor's own stored type, `C_rec` the recursor
CONSTANT and `A₁` the constructor's first field type.  `instLamsAt`
returns `(fun _ : T_rec => A₁) C_rec` as `ldoms[rP]`; `isDefEq envC`
β-reduces it to `A₁` and answers `true`, since an unstored constant is
never looked up on that path; `stripLams`/`abstractIh`/the residue's
inference never see it.  Then
`denoteMeta mpC.base2.acval envC ψ (rP) (ldoms.getD rP default) = none`
by `denoteMeta`'s `.const` clause, while the consed reading is `some`
(`blockRuleTower_run`).

**So the kernel checks it** (validate once at insertion, never a
per-call gate): in `checkBlockRule`
(`ConLeche/Kernel/Inductives/BlockInstall.lean`), immediately after
the `instLamsAt` that produces `ldoms` and before the domain
comparison,

    unless ldoms.all (fun t => t.constsResolve envT) do
      throw (unresolvedConstsError s!"the domains of the rule of {cA.1.name}" rhsA)

mirrored in `checkBlockRuleF` (`BlockInstallF.lean`, through
`w.resolve feT`), so the pure and the cached routes accept the same
streams.  It rejects nothing official emits: a generated rule's binder
domains ARE the recursor prefix's stored types and the constructor's
field types, and both are `constsResolve envC` already
(`checkBlockRecK_facts`' first bullet for the recursor type, the
constructors' stage for `cA.1.type`); the forged witness above is
`tests/e2e/corner_rec_dom_recursor.ndjson`.  The peel keeps the guard
(`RuleRun.hldomsRes`), `blockRuleData_run` states it at the
frame's own bound through the two openings' lengths, and
`blockRuleDataB_of_residue` reads it off the run. -/

/-! ## 8. `ihs` PINNED — the ih openers' terms at the rule's frame

`BlockRuleDataB` carries six function variables and four of them are
pinned by equations in `blockRuleDataB_of_residue`'s own signature
(`hpd`/`hfdD`/`hesD`/`hmkD`); `ihs` is pinned the same way.

`blockRecIhsAt` (`BlockRecPreRun.lean` §30) is the `ihs` the recursor
model states its facts at, one `ihFunAV` per key; `blockRuleIhsAV` is its
instantiation at the RULE's per-key data — the field's MOVED
telescope, its index readings moved with it, and the field applied
along the telescope — which is exactly what
`ihSpineFold_blockRec_run`'s `hihv` spells out on its right-hand
side, so `hihv` is `List.getD` of a `map`. -/

section IhsPin

open ConLeche (BlockRuleFrame pairIdxOf? structFieldTeleOf)

/-- **`ihs` at ONE rule's frame** — `blockRecIhsAt` at the rule's own
per-key syntactic data: field `i`'s telescope moved to the frame
(`ihTeleAtR`, at the block's elimination bit), its index readings
moved with it (`ihIdxAtM`) and the field applied along the telescope's
own variables.

The three `fun i => …` are read off `hihv`'s right-hand side
verbatim; `tlF` and `EisF` are the CONSTRUCTORS' stage's field
readings (`FieldReadAt`), which is where the ψ-dependence enters. -/
@[expose] def blockRuleIhsAV (ℓ K o : Nat) (fr : BlockRuleFrame) (cty : Expr)
    (ψ : Name → Nat) (tlF : Nat → List (Nat × Nat × AnnotTerm))
    (EisF : Nat → List AnnotTerm) : List AnnotTerm :=
  blockRecIhsAt ℓ K fr.rP fr.nF fr.ihKeys
    (fun i => ihTeleAtR fr.nF o i 0 (rebit (pwBit ψ fr.pw) (tlF i)))
    (fun i => (EisF i).map (ihIdxAtM fr.nF o i 0 (structFieldTeleOf cty fr.nP fr.nF i).length))
    (fun i => AnnotTerm.mkAppN
      (.bvar (fr.nF - 1 - i + 0 + (structFieldTeleOf cty fr.nP fr.nF i).length))
      (teleVarsAV (structFieldTeleOf cty fr.nP fr.nF i).length))

@[simp] theorem blockRuleIhsAV_length (ℓ K o : Nat) (fr : BlockRuleFrame) (cty : Expr)
    (ψ : Name → Nat) (tlF : Nat → List (Nat × Nat × AnnotTerm))
    (EisF : Nat → List AnnotTerm) :
    (blockRuleIhsAV ℓ K o fr cty ψ tlF EisF).length = fr.nR := by
  rw [blockRuleIhsAV, blockRecIhsAt_length]
  rfl

/-- **`hihv`, from the pinning** — `ihSpineFold_blockRec_run`'s and
`blockRuleBodyEq_run`'s second block fact, at the values the route's
own `ihs` reads to.  No content beyond `List.getD` of a `map`: the key
at position `r` IS `(i, c')` (`pairIdxOf?_getElem?`). -/
theorem blockRuleHihv_of {ℓ K o : Nat} {fr : BlockRuleFrame} {cty : Expr}
    {ψ : Name → Nat} {tlF : Nat → List (Nat × Nat × AnnotTerm)}
    {EisF : Nat → List AnnotTerm} {σ : Nat → V} :
    ∀ (i c' r : Nat), pairIdxOf? fr.ihKeys (i, c') = some r →
      ((blockRuleIhsAV ℓ K o fr cty ψ tlF EisF).map (interp V σ)).getD r pt
        = interp V σ
            (ihFunAV ℓ K c' fr.rP fr.nF
              (ihTeleAtR fr.nF o i 0 (rebit (pwBit ψ fr.pw) (tlF i)))
              ((EisF i).map (ihIdxAtM fr.nF o i 0 (structFieldTeleOf cty fr.nP fr.nF i).length))
              (AnnotTerm.mkAppN
                (.bvar (fr.nF - 1 - i + 0 + (structFieldTeleOf cty fr.nP fr.nF i).length))
                (teleVarsAV (structFieldTeleOf cty fr.nP fr.nF i).length))) := by
  intro i c' r hr
  have hk : fr.ihKeys[r]? = some (i, c') := pairIdxOf?_getElem? hr
  rw [blockRuleIhsAV, blockRecIhsAt, List.map_map, List.getD_eq_getElem?_getD,
    List.getElem?_map, hk]
  rfl

end IhsPin

/-! ## 9. THE BODY EQUATION, WIRED

`blockRuleBodyEq_run` (`BlockRecTyShapeRun.lean`) is the rule
contract's last conjunct — `interp_blockResidue`'s own conclusion at
the rule's frame, with forty-five premises.  This section is its
application at the run.

**What the run pays for.**  The two peels (`blockRuleData_run` for the
rule's own openings and the λ-tower, `blockRuleResidueData_runP` for
the residue's rows) and the two block facts (`blockRuleHcallee_of`,
and `hihv` off §8's pinning) discharge fifteen of the forty-five; the
reading of the right-hand side is `blockRuleRhs_read_run`'s; the
environment crossing is `blockRecDenote_cross` and
`findProj?_consBlockRecs`; and the two residue rows `hbf`/`hbB` are
the checked rule's own scoping through `stripLams`.

**What stays a premise, and whose it is.** The constructor's stored
type and its field readings (`hop0`…`hrecTy`) are the constructors'
stage's; the frame's eight context rows (`hpl`…`hclF`) are the
certificate bundle's (`BlockRuleCerts`, stated here at the run's own
openers so the bundle's producer plugs in unchanged); `hspF` is the
contract's FIRST conjunct (`blockRuleHsp_field_run`, which is why the
`w`-guard reaches this far); `hihFit` is the recursor model's (the
typed tuple's `ih` fit at the chain frame); and the residue's typing certificates (`hcbe`, `hbT`, `hB`,
`hty`) are the check's own inference, which the bundle also carries.

**`ℓ ≠ 0` is not incidental.**  `blockRuleBodyEq_run` needs it
(`ihFunAV_fold` folds a λ-tower at a non-zero level), so THIS
conjunct of the contract is stated above `Prop`: at `ℓ = 0` the ih
values are the point and the recursor's type is a truth value
(`blockRecTyZ_run`), which is how the endpoint reads that case.

**The composition CALLS the composed statement** rather than inlining
its proof: a composed statement that is CALLED is the only thing that
keeps its premise set honest (an inlining proves the PROOF composes
and says nothing about whether the STATEMENT's premises are
satisfiable — cf. `blockRuleBodyEq_run`'s `hop0`/`hop2` note). -/

section BodyEqRun

open ConLeche (checkBlockRecK BlockParts BlockRuleFrame pairIdxOf? structFieldTeleOf
  nameIdxOf? openPisAtFvars)

/-- **The body equation at the run.**  `blockRuleBodyEq_run` with
every premise the RUN determines discharged; the conclusion is
`BlockRuleResidueB`'s own inner statement — the λ-tower's core read
against the residue at the ih values — at the route's pinned `ihs`
(§8).

The `∀ lds A` binders are the contract's: `mkLamsAV` at a fixed length
pins them (`mkLamsAV_length_inj`), and the reading the run gives
(`blockRuleTower_run`) identifies `A` with the reading of the
`instLamsAt` residual, which `instLamsAt_rest_eq` identifies with the
stripped body opened — which is what `interp_blockResidue`'s `hA`
asks for. -/
theorem blockRuleBodyEq_at_run {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hndM : p.toBlockShape.memberNames.Nodup)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    -- the consed environment, its model and the leaf's value
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    {m₃ : EnvModel V (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC rs s eqs)
    (hleafCl : ∀ (ψ : Name → Nat) (q : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s eqs ψ q).erase))
    {ψ : Name → Nat} {Ra : AnnotTerm}
    (hread : denoteMeta m₃.acval
        (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) ψ 0 rhs = some Ra)
    -- the rule's frame, as the residue peel returns it
    {fr : BlockRuleFrame} {lps : List Name} {recTys : List Expr}
    {rbs : List (Expr × ConLeche.BinderMeta)}
    {rbody resid ihTele bodyO : Expr} {fvsIh : List Expr}
    (hfrP : fr.nP = p.nP) (hfrR : fr.rP = p.toBlockShape.rulePrefixAt c)
    (hfrF : fr.nF = cA.2) (hnames : fr.recNames = rs.map (·.1.name))
    (htele : fr.teleOf = structFieldTeleOf cA.1.type p.nP cA.2)
    (hidxF : fr.idxOf = ConLeche.structFieldIdxOf cA.1.type p.nP cA.2)
    (hstrip : ConLeche.Expr.stripLams (p.toBlockShape.rulePrefixAt c + cA.2) rhs
      = some (rbs, rbody))
    (hab : ConLeche.abstractIh fr 0 rbody = some resid)
    (hpis : ConLeche.blockIhPis p.nP (p.toBlockShape.rulePrefixAt c) cA.2 fr.pw
        (fun c' => recTys.getD c' (.sort .zero)) fr.teleOf fr.idxOf fr.ihKeys 0 resid
      = some ihTele)
    (hopen : openPisAtFvars fr.nR
        (ihTele.instantiateList (blockRulePrefFvs p.toBlockShape rs c
          ++ blockRuleFieldFvs p.toBlockShape rs c i).reverse)
        (p.toBlockShape.rulePrefixAt c + cA.2) = some (fvsIh, bodyO))
    -- the block's level arguments, and the chain
    (hrlvls : fr.rlvls = lps.map Level.param)
    (hlps0 : ∀ r₀ : ConstantVal × List Expr × Nat × List (ConstantVal × Nat),
      rs[0]? = some r₀ → r₀.1.levelParams = lps)
    {a ρ : Nat → V}
    (ha : ∀ c', c' < rs.length →
      interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s eqs ψ c') = a c')
    -- the frame's arithmetic and the caller's two spines
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c)
    {ℓ : Nat} (hℓ : ℓ ≠ 0) {xs fs : List V}
    (hxl : xs.length = fr.rP) (hfsl : fs.length = fr.nF)
    -- the constructor's stored type, and the constructors' stage's readings
    {fvs0 : List Expr} {crest0 : Expr}
    {tlF : Nat → List (Nat × Nat × AnnotTerm)} {EisF : Nat → List AnnotTerm}
    (hop0 : openPisAtFvars (fr.nP + fr.nF) cA.1.type 0 = some (fvs0, crest0))
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hstripC : (cA.1.type.stripPis (fr.nP + fr.nF)).isSome = true)
    (hcb : ConstsBound envC cA.1.type)
    (htlen : ∀ q, (tlF q).length = (structFieldTeleOf cA.1.type fr.nP fr.nF q).length)
    (hfld : ∀ q c' k : Nat, pairIdxOf? fr.ihKeys (q, c') = some k →
      q < fr.nF ∧ FieldReadAt mpC.base2 ψ fr.nP fr.nF q cA.1.type fvs0 (tlF q) (EisF q))
    (hrecTy : ∀ q c' k : Nat, pairIdxOf? fr.ihKeys (q, c') = some k →
      (recTys.getD c' (.sort .zero)).hasFvar = false ∧
        (recTys.getD c' (.sort .zero)).looseBVarsBounded 0 = true ∧
        ∃ TVa : AnnotTerm,
          denoteMeta mpC.base2.acval envC ψ 0 (recTys.getD c' (.sort .zero)) = some TVa)
    -- the generated tower's own two scoping facts
    (hihfv : ihTele.hasFvar = false)
    (hLpf : FvarList (fr.rP + fr.nF)
      (blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i).reverse)
    -- the frame's context: the certificate bundle's rows, at the run's openers
    {pdoms fdoms ihdoms : List AnnotTerm}
    (hpl : pdoms.length = fr.rP) (hfl : fdoms.length = fr.nF)
    (hil : ihdoms.length = fr.nR)
    (hdoms : ∀ (q : Nat) (x : Expr),
      (blockRulePrefFvs p.toBlockShape rs c ++ blockRuleFieldFvs p.toBlockShape rs c i
        ++ fvsIh)[q]? = some x →
      denoteMeta mpC.base2.acval envC ψ q (Expr.fvarTypeD x)
        = some ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (fr.rP + fr.nF + fr.nR - 1 - q) default))
    (hokΔ : ∀ q, q < fr.rP + fr.nF + fr.nR →
      ∀ σ : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) σ →
        WellDenotedV V (fun j => σ (j + (fr.rP + fr.nF + fr.nR - 1 - q) + 1))
          ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (fr.rP + fr.nF + fr.nR - 1 - q) default))
    (hlbF : ∀ x ∈ blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i ++ fvsIh,
      (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hcbF : ∀ x ∈ blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i ++ fvsIh, ConstsBound envC x)
    (hclF : ∀ x ∈ blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i ++ fvsIh,
      ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ blockRulePrefFvs p.toBlockShape rs c
          ++ blockRuleFieldFvs p.toBlockShape rs c i ++ fvsIh)
    -- the two fits: the contract's FIRST conjunct, and the regime's ih fit
    (hspF : SpineFit (chainFrame rs.length a ρ) (pdoms ++ fdoms) (xs ++ fs))
    (hihFit : SpineFit (consList (xs ++ fs) (chainFrame rs.length a ρ)) ihdoms
      ((blockRuleIhsAV ℓ rs.length (fr.rP - fr.nP) fr cA.1.type ψ tlF EisF).map
        (interp V (consList (xs ++ fs) (chainFrame rs.length a ρ)))))
    -- the residue's own typing certificates
    (hin : ConLeche.Model.Rules.RulesInputs V mpC.base2 ψ)
    (hcbe : ConstsBound envC resid)
    (h2 : FvarList (p.toBlockShape.rulePrefixAt c + cA.2 + fr.nR)
      (blockRulePrefFvs p.toBlockShape rs c ++ blockRuleFieldFvs p.toBlockShape rs c i
        ++ fvsIh).reverse)
    {B : AnnotTerm}
    (hB : denoteMeta mpC.base2.acval envC ψ
      (p.toBlockShape.rulePrefixAt c + cA.2 + fr.nR)
      (resid.instantiateList (blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i ++ fvsIh).reverse 0) = some B)
    (hty : IhTyped envC (p.toBlockShape.rulePrefixAt c + cA.2 + fr.nR)
      (resid.instantiateList (blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i ++ fvsIh).reverse 0)) :
    ∀ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A →
      lds.length = p.toBlockShape.rulePrefixAt c + cA.2 →
      interp V (consList (xs ++ fs) ρ) A
        = interp V (consList
            ((blockRuleIhsAV ℓ rs.length (fr.rP - fr.nP) fr cA.1.type ψ tlF EisF).map
              (interp V (consList (xs ++ fs) (chainFrame rs.length a ρ))))
            (consList (xs ++ fs) ρ)) B := by
  intro lds A hlam hldslen
  have hcv := checkBlockRecK_cvFacts h
  -- the rule's own openings, and the tower the reading determines
  obtain ⟨o₁, cpref, rbs', rbody', ldoms, lrest, hopPref, hinst, hopF, hstrip', hlams,
    -, -, -⟩ := blockRuleData_run h hr hcA hrhs
  obtain ⟨ldoms₀, lrest₀, lds₀, A₀, hlams₀, hlam₀, hlen₀, hcore₀, -⟩ :=
    blockRuleTower_run h hr hcA hrhs hread
  have hlrEq : lrest₀ = lrest :=
    congrArg Prod.snd (Option.some.inj (hlams₀.symm.trans hlams))
  rw [hlrEq] at hcore₀
  obtain ⟨rfl, rfl⟩ : lds = lds₀ ∧ A = A₀ :=
    mkLamsAV_length_inj (by rw [hldslen, hlen₀]) (hlam ▸ hlam₀)
  -- the openers' lengths, and the residual as the stripped body OPENED
  have hlenP : (blockRulePrefFvs p.toBlockShape rs c).length
      = p.toBlockShape.rulePrefixAt c := ConLeche.Verify.openPisAtFvars_length _ hopPref
  have hlenF : (blockRuleFieldFvs p.toBlockShape rs c i).length = cA.2 :=
    ConLeche.Verify.openPisAtFvars_length _ hopF
  have hpflen : (blockRulePrefFvs p.toBlockShape rs c
      ++ blockRuleFieldFvs p.toBlockShape rs c i).length
      = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [List.length_append, hlenP, hlenF]
  have hrest : lrest = rbody.instantiateList (blockRulePrefFvs p.toBlockShape rs c
      ++ blockRuleFieldFvs p.toBlockShape rs c i).reverse 0 :=
    instLamsAt_rest_eq _ hlams (by rw [hpflen]; exact hstrip)
  -- the frame's own spellings of the three run facts
  have htele' : fr.teleOf = ConLeche.structFieldTeleOf cA.1.type fr.nP fr.nF := by
    rw [htele, hfrP, hfrF]
  have hidxF' : fr.idxOf = ConLeche.structFieldIdxOf cA.1.type fr.nP fr.nF := by
    rw [hidxF, hfrP, hfrF]
  have hLpf' : FvarList (fr.rP + fr.nF)
      (blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i).reverse := hLpf
  -- the checked rule's own scoping, through `stripLams`
  obtain ⟨-, -, -, -, hallRhs⟩ :=
    ConLeche.checkBlockRecK_facts h r (List.mem_of_getElem? hr)
  obtain ⟨hfvRhs, -, -, hbRhs⟩ := hallRhs rhs (List.mem_of_getElem? hrhs)
  have hbf : rbody.hasFvar = false := (stripLams_not_hasFvar _ hstrip hfvRhs).2
  have hbB : rbody.looseBVarsBounded (p.toBlockShape.rulePrefixAt c + cA.2) = true := by
    have hq := stripLams_body_bounded _ hstrip hbRhs
    rwa [Nat.zero_add] at hq
  -- the three openings, at the frame's own arities
  have hop1 : openPisAtFvars fr.rP r.1.type 0
      = some (blockRulePrefFvs p.toBlockShape rs c, o₁) := by rw [hfrR]; exact hopPref
  have hop2 : openPisAtFvars fr.nF (blockRuleCrest p.toBlockShape rs c i) fr.rP
      = some (blockRuleFieldFvs p.toBlockShape rs c i,
          blockRuleCbody p.toBlockShape rs c i) := by rw [hfrF, hfrR]; exact hopF
  have hopIh : openPisAtFvars fr.nR
      (ihTele.instantiateList (blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i).reverse) (fr.rP + fr.nF)
      = some (fvsIh, bodyO) := by rw [hfrR, hfrF]; exact hopen
  -- the residue's own bounds
  have hbT : resid.looseBVarsBounded (fr.rP + fr.nF + fr.nR) = true := by
    have hq := abstractIh_looseBVarsBounded (B := fr.rP + fr.nF) hab
      (by rw [Nat.zero_add, hfrR, hfrF]; exact hbB)
    rwa [Nat.zero_add] at hq
  have hresfv : resid.hasFvar = false := abstractIh_hasFvar hab hbf
  have h2' : FvarList (fr.rP + fr.nF + fr.nR)
      (blockRulePrefFvs p.toBlockShape rs c ++ blockRuleFieldFvs p.toBlockShape rs c i
        ++ fvsIh).reverse := by rw [hfrR, hfrF]; exact h2
  have hcoreA : denoteMeta m₃.acval
      (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) ψ (fr.rP + fr.nF)
      (rbody.instantiateList (blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i).reverse 0) = some A := by
    rw [hfrR, hfrF, ← hrest]; exact hcore₀
  have hB' : denoteMeta mpC.base2.acval envC ψ (fr.rP + fr.nF + fr.nR)
      (resid.instantiateList (blockRulePrefFvs p.toBlockShape rs c
        ++ blockRuleFieldFvs p.toBlockShape rs c i ++ fvsIh).reverse 0) = some B := by
    rw [hfrR, hfrF]; exact hB
  -- the two readings are bvar-bounded by their own frames, so the CHAIN binders
  -- below them are invisible: the contract states the equation at `ρ`
  have hAb : Term.bvarsBelow (fr.rP + fr.nF) A.erase :=
    bvarsBelow_of_reading (wscoped_instantiateList hLpf' rbody hbf 0)
      (looseBVarsBounded_open hLpf' (by rw [hfrR, hfrF]; exact hbB)) hcoreA
  have hBb : Term.bvarsBelow (fr.rP + fr.nF + fr.nR) B.erase :=
    bvarsBelow_of_reading (wscoped_instantiateList h2' resid hresfv 0)
      (looseBVarsBounded_open h2' hbT) hB'
  have hxfl : (xs ++ fs).length = fr.rP + fr.nF := by
    rw [List.length_append, hxl, hfsl]
  have hihvl : ((blockRuleIhsAV ℓ rs.length (fr.rP - fr.nP) fr cA.1.type ψ tlF EisF).map
      (interp V (consList (xs ++ fs) (chainFrame rs.length a ρ)))).length = fr.nR := by
    rw [List.length_map, blockRuleIhsAV_length]
  rw [interp_congr_below (V := V) A (fr.rP + fr.nF) (consList (xs ++ fs) ρ)
      (consList (xs ++ fs) (chainFrame rs.length a ρ)) hAb
      (fun q hq => consList_below_indep _ _ _ q (by rw [hxfl]; exact hq)),
    interp_congr_below (V := V) B (fr.rP + fr.nF + fr.nR)
      (consList _ (consList (xs ++ fs) ρ))
      (consList _ (consList (xs ++ fs) (chainFrame rs.length a ρ))) hBb
      (fun q hq => by
        rw [← consList_append, ← consList_append]
        exact consList_below_indep _ _ _ q
          (by rw [List.length_append, hxfl, hihvl]; omega))]
  exact blockRuleBodyEq_run (mo := m₃) (mT := mpC.base2) (F := fr.rP + fr.nF)
    (o := fr.rP - fr.nP) (ℓ := ℓ) (K := rs.length) (cty := cA.1.type)
    (fvs0 := fvs0) (crest := crest0) (cmid := blockRuleCrest p.toBlockShape rs c i)
    (tlF := tlF) (EisF := EisF) (recTyOf := fun c' => recTys.getD c' (.sort .zero))
    (σchain := chainFrame rs.length a ρ)
    hin
    (fun sn q => (findProj?_consBlockRecs (fun r₀ hr₀ => (hcv r₀ hr₀).2.2.1) sn q).symm)
    (fun D y ya hcby hy => blockRecDenote_cross h hac ψ D y hcby hy)
    (by omega) rfl (by omega) hxl hfsl hℓ
    (by rw [List.length_map, blockRuleIhsAV_length])
    hop0 hCf hCb hstripC hcb htele' hidxF' htlen hfld hrecTy
    hop1 hop2 (by rw [hfrP, hfrR, hfrF]; exact hpis) hihfv hLpf' hopIh
    (blockRuleHcallee_of h hndM (fun r₀ hr₀ => (hcv r₀ hr₀).1) hleafCl hac hnames hrlvls
      hlps0 ha rfl)
    blockRuleHihv_of
    hpl hfl hil hdoms hokΔ hlbF hcbF hclF hspF hihFit
    hab hbf (by rw [hfrR, hfrF]; exact hbB) hcbe hbT hLpf' h2' hcoreA hB'
    (by rw [hfrR, hfrF]; exact hty)

end BodyEqRun

/-! ## 10. THE TELESCOPE WRAPPER — `BlockRuleResidueB` from the run

§9 concludes the contract's inner statement at the WIRING's own data:
the peel's frame `fr`, the prefix and field VALUES as two lists, and
the chain frame written out.  `BlockRuleResidueB` (`BlockRecData.lean`)
arrives with the CONTRACT's telescope instead — a level list `us`, a
base frame `ρ`, the recursor's spine `xs`, the constructor's spine
`ys` and two `TeleFitPA`s — and the gap between the two is four facts
and one quantifier:

* the prefix VALUES' length is the rule prefix, which needs
  `rulePrefixAt j ≤ majorIdxAt j` (`blockRecHrPle`, a run fact),
  because the contract hands `xs` at the MAJOR index and the wiring
  wants `xs.take rP`;
* the field values' length is `cA.2`, off the contract's own `hyl`;
* the rule's FIT crosses from the contract's base frame `ρ` to the
  CHAIN frame the `ih` values live at.  That crossing is FREE — the
  domains are read at their own depths, so the `K` lift is the
  identity (`liftDomsK_eq_self_of_bounded`) and `spineFit_liftDomsK` at
  the empty prefix is the transport;
* the right-hand side's reading is the contract's `blockRuleRaOf`, and
  the wiring's `Ra` is that value (`hread`, in the spelling
  `blockRuleDataB_of_residue` already asks it in);
* and everything the PEEL determines is quantified over the peel's own
  OUTPUTS, because `blockRuleResidueData_runP` returns them
  existentially.  `BlockRuleBodyInputs` names that premise block, so
  the quantifier is written once.

**Nothing here is over-quantified.**  Every hypothesis is bounded by a
fact the contract's telescope already hands — `us` at the recursor's
own level-parameter count, `ρ`/`xs`/`ys` at the contract's two
lengths — and the peel's outputs are bound by the peel's own rows. -/

section ResidueB

open ConLeche (checkBlockRecK BlockParts BlockRuleFrame pairIdxOf? structFieldTeleOf
  structFieldIdxOf nameIdxOf? openPisAtFvars abstractIh blockIhPis)

/-- **A fit crosses INTO the chain frame for free** when the domains
are read at their own depths: the `K` lift is then the identity
(`liftDomsK_eq_self_of_bounded`) and `spineFit_liftDomsK` at the empty
prefix is the whole transport.

This is the `K = 0` collapse of §1 read in the other direction: §1
takes the chain-frame statement down to the base frame at `K = 0`,
this takes the base-frame statement up to any `K`. -/
theorem spineFit_chainFrame_of_bounded {K : Nat} {a ρ : Nat → V} {Ds : List AnnotTerm}
    {vs : List V}
    (hb : ∀ l, l < Ds.length → Term.bvarsBelow l ((Ds.getD l default).erase))
    (hsp : SpineFit ρ Ds vs) : SpineFit (chainFrame K a ρ) Ds vs := by
  have hq : SpineFit (consList ([] : List V) (chainFrame K a ρ))
      (liftDomsK K ([] : List V).length Ds) vs :=
    (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) Ds [] vs).mpr hsp
  rwa [List.length_nil, liftDomsK_eq_self_of_bounded 0 Ds (by simpa using hb)] at hq

/-- **The body equation's inputs at ONE peel's outputs and ONE fired
spine** — everything `blockRuleBodyEq_at_run` (§9) asks that the RESIDUE
PEEL does not determine, bundled so the telescope wrapper can quantify
it over the peel's outputs in one binder.

The five existentials are the CONSTRUCTORS' stage's readings (`fvs0`,
`crest0`, `tlF`, `EisF` — `FieldReadAt`'s own data) and the `ih`
context's domain list; everything else is a parameter, so a producer
is told which frame, which values, which `ih` list and which residue
reading it must deliver at.

**`ihsL` is the contract's own `ihs ψ j i`**, and the equation that
pins it to `blockRuleIhsAV` (§8) is a conjunct here rather than a
separate hypothesis because the pinning mentions `fr`, `tlF` and
`EisF`, all of which are under the peel's quantifier.

**The ih FIT — the conjunct right after the pinning — is the
recursor model's.**  With `ihs` pinned it is the typed tuple's `ih` fit
at this rule's data, at the chain frame of any typed tuple `a`:

```
SpineFit (consList (x⃗ ++ f⃗) (chainFrame K a ρ)) ihdoms
  (ihs.map (interp V (consList (x⃗ ++ f⃗) (chainFrame K a ρ))))
```

and its producer (`blockRuleIhFit_seam`, off `BlockRecPre`: the leaf's
tuple is typed) needs the recursor model.  It is stated here in the
producer's own spelling — same frame, same `ihdoms`, same `map` — so
it plugs in unchanged; the two side conditions it takes, the prefix length and
`SpineFit (chainFrame K a ρ) (pdoms ++ fdoms) (x⃗ ++ f⃗)`, are the
wrapper's `hxl'`/`hpl` and its `hspF`, at the same frame. -/
def BlockRuleBodyInputs (V : Type w) [SetTheory V] {μ : CheckMode} {envC : Env}
    (mpC : EnvModelM V μ envC) (p : BlockParts) (rs : List RecDatum)
    (ψ : Name → Nat) (ℓ : Nat) (j i : Nat) (cA : ConstantVal × Nat) (lps : List Name)
    (fr : BlockRuleFrame) (recTys : List Expr) (resid ihTele : Expr) (fvsIh : List Expr)
    (pdoms fdoms : List AnnotTerm) (σ : Nat → V) (xs fs : List V)
    (ihsL : List AnnotTerm) (B : AnnotTerm) : Prop :=
  ∃ (fvs0 : List Expr) (crest0 : Expr) (tlF : Nat → List (Nat × Nat × AnnotTerm))
    (EisF : Nat → List AnnotTerm) (ihdoms : List AnnotTerm),
    -- the constructor's stored type, and the constructors' stage's field readings
    openPisAtFvars (fr.nP + fr.nF) cA.1.type 0 = some (fvs0, crest0) ∧
    cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true ∧
    (cA.1.type.stripPis (fr.nP + fr.nF)).isSome = true ∧
    ConstsBound envC cA.1.type ∧
    (∀ q, (tlF q).length = (structFieldTeleOf cA.1.type fr.nP fr.nF q).length) ∧
    (∀ q c' k : Nat, pairIdxOf? fr.ihKeys (q, c') = some k →
      q < fr.nF ∧ FieldReadAt mpC.base2 ψ fr.nP fr.nF q cA.1.type fvs0 (tlF q) (EisF q)) ∧
    (∀ q c' k : Nat, pairIdxOf? fr.ihKeys (q, c') = some k →
      (recTys.getD c' (.sort .zero)).hasFvar = false ∧
        (recTys.getD c' (.sort .zero)).looseBVarsBounded 0 = true ∧
        ∃ TVa : AnnotTerm,
          denoteMeta mpC.base2.acval envC ψ 0 (recTys.getD c' (.sort .zero)) = some TVa) ∧
    -- the block's level arguments, and the generated tower's two scoping facts
    fr.rlvls = lps.map Level.param ∧
    ihTele.hasFvar = false ∧
    FvarList (fr.rP + fr.nF)
      (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse ∧
    -- the frame's context: the certificate bundle's eight rows, at the run's openers
    pdoms.length = fr.rP ∧ fdoms.length = fr.nF ∧ ihdoms.length = fr.nR ∧
    (∀ (q : Nat) (x : Expr),
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ fvsIh)[q]? = some x →
      denoteMeta mpC.base2.acval envC ψ q (Expr.fvarTypeD x)
        = some ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (fr.rP + fr.nF + fr.nR - 1 - q) default)) ∧
    (∀ q, q < fr.rP + fr.nF + fr.nR →
      ∀ σ' : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) σ' →
        WellDenotedV V (fun l => σ' (l + (fr.rP + fr.nF + fr.nR - 1 - q) + 1))
          ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (fr.rP + fr.nF + fr.nR - 1 - q) default)) ∧
    (∀ x ∈ blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh,
      (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
    (∀ x ∈ blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh, ConstsBound envC x) ∧
    (∀ x ∈ blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh,
      ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ blockRulePrefFvs p.toBlockShape rs j
          ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh) ∧
    -- the REGIME's ih fit, and the pinning that makes it statable
    ihsL = blockRuleIhsAV ℓ rs.length (fr.rP - fr.nP) fr cA.1.type ψ tlF EisF ∧
    SpineFit (consList (xs ++ fs) σ) ihdoms (ihsL.map (interp V (consList (xs ++ fs) σ))) ∧
    -- the residue's own typing certificates, at the CHECK's own depth
    ConstsBound envC resid ∧
    FvarList (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR)
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ fvsIh).reverse ∧
    denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR)
      (resid.instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh).reverse 0) = some B ∧
    IhTyped envC (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR)
      (resid.instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh).reverse 0)

/-- `BlockRuleBodyInputs` UNFOLDED — its conjunct list, for producers in
other modules (the definition's body is private there). -/
theorem blockRuleBodyInputs_iff (V : Type w) [SetTheory V] {μ : CheckMode} {envC : Env}
    (mpC : EnvModelM V μ envC) (p : BlockParts) (rs : List RecDatum)
    (ψ : Name → Nat) (ℓ : Nat) (j i : Nat) (cA : ConstantVal × Nat) (lps : List Name)
    (fr : BlockRuleFrame) (recTys : List Expr) (resid ihTele : Expr) (fvsIh : List Expr)
    (pdoms fdoms : List AnnotTerm) (σ : Nat → V) (xs fs : List V)
    (ihsL : List AnnotTerm) (B : AnnotTerm) :
    BlockRuleBodyInputs V mpC p rs ψ ℓ j i cA lps fr recTys resid ihTele fvsIh pdoms fdoms σ xs fs ihsL B ↔
  ∃ (fvs0 : List Expr) (crest0 : Expr) (tlF : Nat → List (Nat × Nat × AnnotTerm))
    (EisF : Nat → List AnnotTerm) (ihdoms : List AnnotTerm),
    -- the constructor's stored type, and the constructors' stage's field readings
    openPisAtFvars (fr.nP + fr.nF) cA.1.type 0 = some (fvs0, crest0) ∧
    cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true ∧
    (cA.1.type.stripPis (fr.nP + fr.nF)).isSome = true ∧
    ConstsBound envC cA.1.type ∧
    (∀ q, (tlF q).length = (structFieldTeleOf cA.1.type fr.nP fr.nF q).length) ∧
    (∀ q c' k : Nat, pairIdxOf? fr.ihKeys (q, c') = some k →
      q < fr.nF ∧ FieldReadAt mpC.base2 ψ fr.nP fr.nF q cA.1.type fvs0 (tlF q) (EisF q)) ∧
    (∀ q c' k : Nat, pairIdxOf? fr.ihKeys (q, c') = some k →
      (recTys.getD c' (.sort .zero)).hasFvar = false ∧
        (recTys.getD c' (.sort .zero)).looseBVarsBounded 0 = true ∧
        ∃ TVa : AnnotTerm,
          denoteMeta mpC.base2.acval envC ψ 0 (recTys.getD c' (.sort .zero)) = some TVa) ∧
    -- the block's level arguments, and the generated tower's two scoping facts
    fr.rlvls = lps.map Level.param ∧
    ihTele.hasFvar = false ∧
    FvarList (fr.rP + fr.nF)
      (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse ∧
    -- the frame's context: the certificate bundle's eight rows, at the run's openers
    pdoms.length = fr.rP ∧ fdoms.length = fr.nF ∧ ihdoms.length = fr.nR ∧
    (∀ (q : Nat) (x : Expr),
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ fvsIh)[q]? = some x →
      denoteMeta mpC.base2.acval envC ψ q (Expr.fvarTypeD x)
        = some ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (fr.rP + fr.nF + fr.nR - 1 - q) default)) ∧
    (∀ q, q < fr.rP + fr.nF + fr.nR →
      ∀ σ' : Nat → V, Sat V (ihdoms.reverse ++ (pdoms ++ fdoms).reverse) σ' →
        WellDenotedV V (fun l => σ' (l + (fr.rP + fr.nF + fr.nR - 1 - q) + 1))
          ((ihdoms.reverse ++ (pdoms ++ fdoms).reverse).getD
            (fr.rP + fr.nF + fr.nR - 1 - q) default)) ∧
    (∀ x ∈ blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh,
      (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
    (∀ x ∈ blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh, ConstsBound envC x) ∧
    (∀ x ∈ blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh,
      ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ blockRulePrefFvs p.toBlockShape rs j
          ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh) ∧
    -- the REGIME's ih fit, and the pinning that makes it statable
    ihsL = blockRuleIhsAV ℓ rs.length (fr.rP - fr.nP) fr cA.1.type ψ tlF EisF ∧
    SpineFit (consList (xs ++ fs) σ) ihdoms (ihsL.map (interp V (consList (xs ++ fs) σ))) ∧
    -- the residue's own typing certificates, at the CHECK's own depth
    ConstsBound envC resid ∧
    FvarList (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR)
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i
        ++ fvsIh).reverse ∧
    denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR)
      (resid.instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh).reverse 0) = some B ∧
    IhTyped envC (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR)
      (resid.instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i ++ fvsIh).reverse 0) := Iff.rfl

/-- **What the rule stage's PEEL owes the residue producer** — the
`hbody` premise of `blockRuleResidueB_run`, named: at the contract's
own telescope — with its FIRST conjunct at the base frame, the residue
producer's own `hsp`, which the `ih` fit is read off — and the
leaf-pinned chain tuple, every run of the peel (the frame, the
abstraction, the `ih` telescope, the opening, the residue's typing)
yields `BlockRuleBodyInputs` at the route's `ihs`/`Rb0`.  The peel's
outputs are PINNED to the run's own (§A.9b's definitions,
`BlockRecData.lean`), so a producer is told exactly which frame,
residue and openers it delivers at; `blockRuleBodyOwed_run`
(`BlockRuleRun.lean`) is that producer, at the pinned `ihs`/`Rb0`. -/
def BlockRuleBodyOwed {envC : Env} (mpC : EnvModelM V μ envC) (F : Nat) (p : BlockParts)
    (rs : List RecDatum) (s : (Name → Nat) → Nat) (nCt : Nat → Nat)
    (pdoms0 : (Name → Nat) → Nat → List AnnotTerm)
    (fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm)
    (ctorTy : (Name → Nat) → AnnotTerm) (φ : Name → Nat) (j i : Nat) (r : RecDatum)
    (cA : ConstantVal × Nat) (rl : ConLeche.RecRule) (rhs : Expr) (lps : List Name) : Prop :=
 ∀ us : List Level, us.length = r.1.levelParams.length →
  Level.eval (Level.substFn φ r.1.levelParams us)
    (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
  ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
    xs.length = p.toBlockShape.majorIdxAt j → ys.length = p.nP + cA.2 →
    usj.length = cA.1.levelParams.length →
    Level.substFn φ cA.1.levelParams usj
      = Level.substFn φ cA.1.levelParams
          (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
            (p.toBlockShape.rulePrefixAt j)).1 →
    IotaIndexPin (V := V) ρ restC p.nP
      (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
    TeleFitPA V ρ
      (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
      (xs ++ [AnnotTerm.mkAppN
        (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
    TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
    -- the contract's FIRST conjunct at this telescope (the residue
    -- producer's `hsp`, `blockRuleFit_tele`): the rule's prefix and the
    -- constructor's fields fit the rule's domains at the BASE frame
    SpineFit ρ (pdoms0 (Level.substFn φ r.1.levelParams us) j
        ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i)
      ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
        ++ (ys.drop p.nP).map (interp V ρ)) →
  ∀ a : Nat → V,
    (∀ c', c' < rs.length →
      interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)
        (Level.substFn φ r.1.levelParams us) c') = a c') →
  ∀ (fr : BlockRuleFrame) (recTys : List Expr) (rbody resid ihTele bodyO : Expr)
    (fvsIh : List Expr) (rbs : List (Expr × ConLeche.BinderMeta)) (ty concl : Expr),
    -- the peel's outputs are the run's own (§A.9b's definitions)
    fr = blockRuleFrameAt p rs j i → recTys = rs.map (·.1.type) →
    rbody = blockRuleBodyAt p rs j i → resid = blockRuleResidAt p rs j i →
    ihTele = blockRuleIhTeleAt p rs j i → fvsIh = blockRuleFvsIhAt p rs j i →
    bodyO = blockRuleBodyOAt p rs j i →
    fr.nP = p.nP → fr.rP = p.toBlockShape.rulePrefixAt j → fr.nF = cA.2 →
    fr.recNames = p.recs.map (·.cvR.name) → fr.recTgts = p.recTgts →
    fr.teleOf = structFieldTeleOf cA.1.type p.nP cA.2 →
    fr.idxOf = structFieldIdxOf cA.1.type p.nP cA.2 →
    fr.pw = Level.zeronessOf
      (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) →
    recTys[j]? = some r.1.type →
    ConLeche.Expr.stripLams (p.toBlockShape.rulePrefixAt j + cA.2) rhs
      = some (rbs, rbody) →
    abstractIh fr 0 rbody = some resid →
    blockIhPis p.nP (p.toBlockShape.rulePrefixAt j) cA.2 fr.pw
        (fun c' => recTys.getD c' (.sort .zero)) fr.teleOf fr.idxOf fr.ihKeys 0 resid
      = some ihTele →
    openPisAtFvars fr.nR
        (ihTele.instantiateList (blockRulePrefFvs p.toBlockShape rs j
          ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse)
        (p.toBlockShape.rulePrefixAt j + cA.2) = some (fvsIh, bodyO) →
    ConLeche.inferTypeCore μ envC F
        (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR) bodyO = .ok ty →
    ConLeche.Expr.instPisAtLift
        (blockRulePrefFvs p.toBlockShape rs j
          ++ (blockRuleCbody p.toBlockShape rs j i).getAppArgs.drop p.nP
          ++ [ConLeche.Expr.mkAppN (.const cA.1.name (p.toBlockShape.lps.map .param))
              ((blockRulePrefFvs p.toBlockShape rs j).take p.nP
                ++ blockRuleFieldFvs p.toBlockShape rs j i)])
        r.1.type = some concl →
    ConLeche.isDefEqCore μ envC F
        (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR) ty concl = .ok true →
    BlockRuleBodyInputs V mpC p rs (Level.substFn φ r.1.levelParams us)
      (Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) j i cA lps
      fr recTys resid ihTele fvsIh
      (pdoms0 (Level.substFn φ r.1.levelParams us) j)
      (fdoms0 (Level.substFn φ r.1.levelParams us) j i)
      (chainFrame rs.length a ρ)
      ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ))
      ((ys.drop p.nP).map (interp V ρ))
      (ihs (Level.substFn φ r.1.levelParams us) j i)
      (Rb0 (Level.substFn φ r.1.levelParams us) j i)

/-- `BlockRuleBodyOwed` UNFOLDED, for producers in other modules. -/
theorem blockRuleBodyOwed_iff {envC : Env} (mpC : EnvModelM V μ envC) (F : Nat) (p : BlockParts)
    (rs : List RecDatum) (s : (Name → Nat) → Nat) (nCt : Nat → Nat)
    (pdoms0 : (Name → Nat) → Nat → List AnnotTerm)
    (fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm)
    (ctorTy : (Name → Nat) → AnnotTerm) (φ : Name → Nat) (j i : Nat) (r : RecDatum)
    (cA : ConstantVal × Nat) (rl : ConLeche.RecRule) (rhs : Expr) (lps : List Name) :
    BlockRuleBodyOwed mpC F p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0 ctorTy φ j i r cA rl rhs lps ↔
 ∀ us : List Level, us.length = r.1.levelParams.length →
  Level.eval (Level.substFn φ r.1.levelParams us)
    (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
  ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
    xs.length = p.toBlockShape.majorIdxAt j → ys.length = p.nP + cA.2 →
    usj.length = cA.1.levelParams.length →
    Level.substFn φ cA.1.levelParams usj
      = Level.substFn φ cA.1.levelParams
          (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
            (p.toBlockShape.rulePrefixAt j)).1 →
    IotaIndexPin (V := V) ρ restC p.nP
      (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
    TeleFitPA V ρ
      (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
      (xs ++ [AnnotTerm.mkAppN
        (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
    TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
    -- the contract's FIRST conjunct at this telescope (the residue
    -- producer's `hsp`, `blockRuleFit_tele`): the rule's prefix and the
    -- constructor's fields fit the rule's domains at the BASE frame
    SpineFit ρ (pdoms0 (Level.substFn φ r.1.levelParams us) j
        ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i)
      ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
        ++ (ys.drop p.nP).map (interp V ρ)) →
  ∀ a : Nat → V,
    (∀ c', c' < rs.length →
      interp V ρ (blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0)
        (Level.substFn φ r.1.levelParams us) c') = a c') →
  ∀ (fr : BlockRuleFrame) (recTys : List Expr) (rbody resid ihTele bodyO : Expr)
    (fvsIh : List Expr) (rbs : List (Expr × ConLeche.BinderMeta)) (ty concl : Expr),
    -- the peel's outputs are the run's own (§A.9b's definitions)
    fr = blockRuleFrameAt p rs j i → recTys = rs.map (·.1.type) →
    rbody = blockRuleBodyAt p rs j i → resid = blockRuleResidAt p rs j i →
    ihTele = blockRuleIhTeleAt p rs j i → fvsIh = blockRuleFvsIhAt p rs j i →
    bodyO = blockRuleBodyOAt p rs j i →
    fr.nP = p.nP → fr.rP = p.toBlockShape.rulePrefixAt j → fr.nF = cA.2 →
    fr.recNames = p.recs.map (·.cvR.name) → fr.recTgts = p.recTgts →
    fr.teleOf = structFieldTeleOf cA.1.type p.nP cA.2 →
    fr.idxOf = structFieldIdxOf cA.1.type p.nP cA.2 →
    fr.pw = Level.zeronessOf
      (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) →
    recTys[j]? = some r.1.type →
    ConLeche.Expr.stripLams (p.toBlockShape.rulePrefixAt j + cA.2) rhs
      = some (rbs, rbody) →
    abstractIh fr 0 rbody = some resid →
    blockIhPis p.nP (p.toBlockShape.rulePrefixAt j) cA.2 fr.pw
        (fun c' => recTys.getD c' (.sort .zero)) fr.teleOf fr.idxOf fr.ihKeys 0 resid
      = some ihTele →
    openPisAtFvars fr.nR
        (ihTele.instantiateList (blockRulePrefFvs p.toBlockShape rs j
          ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse)
        (p.toBlockShape.rulePrefixAt j + cA.2) = some (fvsIh, bodyO) →
    ConLeche.inferTypeCore μ envC F
        (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR) bodyO = .ok ty →
    ConLeche.Expr.instPisAtLift
        (blockRulePrefFvs p.toBlockShape rs j
          ++ (blockRuleCbody p.toBlockShape rs j i).getAppArgs.drop p.nP
          ++ [ConLeche.Expr.mkAppN (.const cA.1.name (p.toBlockShape.lps.map .param))
              ((blockRulePrefFvs p.toBlockShape rs j).take p.nP
                ++ blockRuleFieldFvs p.toBlockShape rs j i)])
        r.1.type = some concl →
    ConLeche.isDefEqCore μ envC F
        (p.toBlockShape.rulePrefixAt j + cA.2 + fr.nR) ty concl = .ok true →
    BlockRuleBodyInputs V mpC p rs (Level.substFn φ r.1.levelParams us)
      (Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large)) j i cA lps
      fr recTys resid ihTele fvsIh
      (pdoms0 (Level.substFn φ r.1.levelParams us) j)
      (fdoms0 (Level.substFn φ r.1.levelParams us) j i)
      (chainFrame rs.length a ρ)
      ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ))
      ((ys.drop p.nP).map (interp V ρ))
      (ihs (Level.substFn φ r.1.levelParams us) j i)
      (Rb0 (Level.substFn φ r.1.levelParams us) j i) := Iff.rfl

/-- **`BlockRuleResidueB` from the run** — the rule contract's residue
conjunct, with the RESIDUE PEEL consumed and the telescope's own four
facts paid.

`blockRuleResidueData_runP` (`BlockRecData.lean`) returns the peel's
rows EXISTENTIALLY, so everything else the peel touches has to be
quantified over the same outputs, which is what `hbody` is.  ALL
SIXTEEN rows are passed into `hbody`'s antecedents, not only the ten
the body equation itself reads: a producer that is handed the peel's
`fr` abstractly and is told nothing about `fr.pw`, `fr.recNames` or
the residue's two typing runs is STARVED — a premise nobody can
discharge is the same defect as a premise set with no instance, one
level up.

The four facts the wrapper pays:

* `xs.take rP` is as long as the rule prefix — the contract hands `xs`
  at the MAJOR index, so this is `blockRecHrPle` (`rulePrefixAt j ≤
  majorIdxAt j`, a run fact);
* `ys.drop nP` is as long as the constructor's field count, off `hyl`;
* the FIT crosses to the chain frame (`spineFit_chainFrame_of_bounded`
  at the domains' own bounds `hbdd`) — the contract's first conjunct
  lives at `ρ`, the `ih` values at the chain frame;
* the right-hand side's reading is the contract's `blockRuleRaOf`
  (`hread`, in `blockRuleDataB_of_residue`'s own spelling, moved
  across `hac`).

`hsp` is the contract's FIRST conjunct at this rule — the same
statement `blockRuleDataB_of_residue` derives from
`blockRuleHsp_field_run` — and it is a PREMISE here rather than a
re-derivation, so the `w`-guard stays where that producer put it and
this theorem carries none. -/
theorem blockRuleResidueB_run {mpC : EnvModelM V μ envC}
    (h : checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hndM : p.toBlockShape.memberNames.Nodup)
    {j : Nat} {r : RecDatum} (hr : rs[j]? = some r)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    {ctorTy : (Name → Nat) → AnnotTerm} {φ : Name → Nat} {rl : ConLeche.RecRule}
    -- the consed environment's model, and the leaf's closedness
    {m₃ : EnvModel V (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC rs s
      (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
    (hleafCl : ∀ (ψ : Name → Nat) (q : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ q).erase))
    -- the block's level parameters, and the rule's arithmetic
    {lps : List Name}
    (hlps0 : ∀ r₀ : RecDatum, rs[0]? = some r₀ → r₀.1.levelParams = lps)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt j)
    -- the right-hand side's reading, and the rules' inputs
    (hread : ∀ us : List Level, us.length = r.1.levelParams.length →
      denoteMeta (blockRecAcv mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)
          (Level.substFn φ r.1.levelParams us) 0 rhs
        = some (blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
            (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) rhs
            (Level.substFn φ r.1.levelParams us)))
    (hin : ∀ us : List Level, us.length = r.1.levelParams.length →
      ConLeche.Model.Rules.RulesInputs V mpC.base2 (Level.substFn φ r.1.levelParams us))
    -- the contract's FIRST conjunct at the base frame, and the domains' own bounds
    (hbdd : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ l, l < (pdoms0 (Level.substFn φ r.1.levelParams us) j
          ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i).length →
        Term.bvarsBelow l (((pdoms0 (Level.substFn φ r.1.levelParams us) j
          ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i).getD l default).erase))
    (hsp : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
        xs.length = p.toBlockShape.majorIdxAt j → ys.length = p.nP + cA.2 →
        usj.length = cA.1.levelParams.length →
        Level.substFn φ cA.1.levelParams usj
          = Level.substFn φ cA.1.levelParams
              (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
                (p.toBlockShape.rulePrefixAt j)).1 →
        IotaIndexPin (V := V) ρ restC p.nP
          (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
        TeleFitPA V ρ
          (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
          (xs ++ [AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
        TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
        SpineFit ρ (pdoms0 (Level.substFn φ r.1.levelParams us) j
            ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i)
          ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop p.nP).map (interp V ρ)))
    -- and everything the PEEL determines, at the peel's own outputs
    (hbody : BlockRuleBodyOwed (V := V) mpC F p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs lps) :
    BlockRuleResidueB (V := V) mpC p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs := by
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC a hleaf
    lds A hlam hldslen
  obtain ⟨rbs, ty, concl, hstrip, hab, hpis, hopen, hinf, hconcl, hdeq⟩ :=
    blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨hfrP, hfrR, hfrF, hnames0, htgts, htele, hidxF, hpw⟩ :=
    blockRuleFrameAt_rows (pp := p) (blockRuleCtorOf_eq hr hcA)
  have hrecTysj : (rs.map (·.1.type))[j]? = some r.1.type := by
    rw [List.getElem?_map, hr]; rfl
  obtain ⟨fvs0, crest0, tlF, EisF, ihdoms, hop0, hCf, hCb, hstripC, hcb, htlen, hfld,
    hrecTy, hrlvls, hihfv, hLpf, hpl, hfl, hil, hdoms, hokΔ, hlbF, hcbF, hclF,
    hihsEq, hihFit, hcbe, h2, hB, hty⟩ :=
    hbody us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC
      (hsp us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC) a hleaf
      _ _ _ _ _ _ _ rbs ty concl rfl rfl rfl rfl rfl rfl rfl
      hfrP hfrR hfrF hnames0 htgts htele hidxF hpw hrecTysj hstrip hab hpis hopen
      hinf hconcl hdeq
  have hcl : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  have hmI : p.toBlockShape.rulePrefixAt j ≤ p.toBlockShape.majorIdxAt j :=
    blockRecHrPle h hcl
  have hxl' : ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)).length
      = (blockRuleFrameAt p rs j i).rP := by
    rw [List.length_map, List.length_take, hxl, hfrR]; omega
  have hfsl' : ((ys.drop p.nP).map (interp V ρ)).length = (blockRuleFrameAt p rs j i).nF := by
    rw [List.length_map, List.length_drop, hyl, hfrF]; omega
  have hspF := spineFit_chainFrame_of_bounded (K := rs.length) (a := a)
    (hbdd us hus)
    (hsp us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC)
  have hread' : denoteMeta m₃.acval
      (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)
      (Level.substFn φ r.1.levelParams us) 0 rhs
      = some (blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) rhs
          (Level.substFn φ r.1.levelParams us)) := by
    rw [hac]; exact hread us hus
  rw [hihsEq] at hihFit ⊢
  exact blockRuleBodyEq_at_run h hndM hr hcA hrhs hac hleafCl hread'
    hfrP hfrR hfrF (hnames0.trans (checkBlockRecK_recNamesEq h)) htele hidxF hstrip hab
    hpis hopen hrlvls hlps0 hleaf hnP hℓ hxl' hfsl' hop0 hCf hCb hstripC hcb htlen hfld
    hrecTy hihfv hLpf hpl hfl hil hdoms hokΔ hlbF hcbF hclF hspF hihFit (hin us hus)
    hcbe h2 hB hty lds A hlam hldslen

end ResidueB

/-! ## 10b. THE CONTRACT AT THE RUN — the residue producer fed by the
contract's own first conjunct

`blockRuleResidueB_run`'s `hsp` is the contract's FIRST conjunct at the
contract's own telescope — the statement `blockRuleDataB_of_residue`
derives internally as `hsp1`.  `blockRuleFit_tele` is that derivation
standing alone (the same four steps: the level agreement, the
constructor's fit, the index pin, `blockRuleHsp_field_run`), and
`blockRuleDataB_run` is the contract with the residue producer CALLED
and its `hsp` paid by it — so what is left of the contract at the run
is the two producers' premises minus the one they share. -/

section DataRun

open ConLeche (checkBlockRecK BlockParts BlockRuleFrame abstractIh blockIhPis openPisAtFvars)

/-- **The contract's first conjunct over its own telescope.** -/
theorem blockRuleFit_tele (hM : BlockModelAt mpC.base2 names d)
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {ctorTy : (Name → Nat) → AnnotTerm} {φ : Name → Nat} {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[j]? = some r)
    {cA : ConstantVal × Nat}
    {rl : ConLeche.RecRule} (hplain : ConLeche.RecRule.fire rl = .plain)
    {mem : Nat → Nat} {jc : Nat}
    (hcj : (d.ctorsM (mem j))[jc]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem j) jc cA)
    (hdnP : d.nP = p.nP)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt j)
    (hmemk : mem j < d.k)
    (htgt : ∀ l, l < cA.2 → d.tgts (mem j) jc l < d.k)
    {K : Nat} (hjK : j < K)
    (hctorRead : ∀ ψ : Name → Nat,
      denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some (ctorTy ψ))
    (hfd : ∀ us : List Level, us.length = r.1.levelParams.length →
      blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
          (Level.substFn φ r.1.levelParams us) j i
        = liftDomsK (p.toBlockShape.rulePrefixAt j - d.nP) 0
            ((d.Fss (mem j) (Level.substFn φ r.1.levelParams us)).getD jc []))
    (hlenP : ∀ us : List Level, us.length = r.1.levelParams.length →
      (d.params (Level.substFn φ r.1.levelParams us)).length = d.nP)
    (hparamsC : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ σ : Nat → V,
      Sat V (d.params (Level.substFn φ r.1.levelParams us)).reverse σ
        ↔ Sat V (((d.dsF (mem j) jc (Level.substFn φ r.1.levelParams us)).take d.nP).map
            (·.2.2)).reverse σ)
    (hsplit : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ ρ : Nat → V,
      BlockRecSplitAt V mpC.base2 d (Level.substFn φ r.1.levelParams us) K
        p.toBlockShape.rulePrefixAt mem
        (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) c') ρ)
    (hlarge : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w (Level.substFn φ r.1.levelParams us) = 0 → d.large = true)
    (hct1 : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w (Level.substFn φ r.1.levelParams us) = 0 → (d.ctorsM (mem j)).length ≤ 1) :
    ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
        xs.length = p.toBlockShape.majorIdxAt j → ys.length = p.nP + cA.2 →
        usj.length = cA.1.levelParams.length →
        Level.substFn φ cA.1.levelParams usj
          = Level.substFn φ cA.1.levelParams
              (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
                (p.toBlockShape.rulePrefixAt j)).1 →
        IotaIndexPin (V := V) ρ restC p.nP
          (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
        TeleFitPA V ρ
          (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
          (xs ++ [AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
        TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
        SpineFit ρ
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs
              (Level.substFn φ r.1.levelParams us) j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
                (Level.substFn φ r.1.levelParams us) j i)
          ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop p.nP).map (interp V ρ)) := by
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC
  have hnPd : d.nP ≤ p.toBlockShape.rulePrefixAt j := by rw [hdnP]; exact hnP
  have hlv := blockRuleLevelAgree hplain hψ
  obtain ⟨hqs, hfq⟩ := blockRuleCtorFit_run (d := d) hcj hcf hlv (hlenP us hus)
    (hparamsC us hus) (by rw [hyl, hdnP]) (hctorRead _) hfitC
  have hmN : mem j < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : jc < (d.ctorsM (mem j)).length := (List.getElem?_eq_some_iff.mp hcj).1
  obtain ⟨-, hidxS, -⟩ := blockRecSplit_at_rule (d := d) hμ mpC h hr
    (Level.substFn φ r.1.levelParams us) hxl hfitR hjK (hsplit us hus ρ)
  have hrPle : p.toBlockShape.rulePrefixAt j ≤ p.toBlockShape.majorIdxAt j :=
    blockRecHrPle (p := p) h (List.getElem?_eq_some_iff.mp hr).1
  have hEssD : (d.Ess (mem j) (Level.substFn φ r.1.levelParams us)).getD jc []
      = d.esF (mem j) jc (Level.substFn φ r.1.levelParams us) :=
    essOfR_fixCtorDataList_getD hcj
  have hnI : (d.esF (mem j) jc (Level.substFn φ r.1.levelParams us)).length
      = p.toBlockShape.majorIdxAt j - p.toBlockShape.rulePrefixAt j := by
    have hq := (hM.resIdxFit (Level.substFn φ r.1.levelParams us) _
      (d.satOfSpine hqs) (mem j) hmN jc hjl _ hfq).length_eq
    rw [List.length_map, hEssD] at hq
    rw [hq, ← hidxS.length_eq, List.length_map, List.length_drop, hxl]
  have hpin := blockRuleIdxPin_run hcj hcf hlv (by rw [hyl, hdnP]) hxl hrPle hnI
    (hctorRead _) hfitC (by rw [hdnP]; exact hidx)
  have hq := blockRuleHsp_field_run (i := i) hM hμ h hr hcj hcf (hfd us hus) hmemk hnPd
    htgt hlv (fun h0 => hlarge us hus hℓ h0) (fun h0 => hct1 us hus hℓ h0)
    (hparamsC us hus) hxl hfitR hjK (hsplit us hus ρ) hqs hfq (fun _ => hpin)
  rwa [hdnP] at hq

/-- **THE CONTRACT AT THE RUN**: `blockRuleDataB_of_residue` with its
`hres` produced by `blockRuleResidueB_run`, whose `hsp` is
`blockRuleFit_tele`.  Its premises are the two producers' minus the
one they share; `hbody` (`BlockRuleBodyOwed`) is the rule stage's and
`hbdd` is `blockRuleDoms_bounded_seam`'s (§13). -/
theorem blockRuleDataB_run (hM : BlockModelAt mpC.base2 names d)
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hpd : pdoms0 = fun ψ c => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
    (hfdD : fdoms0 = fun ψ c i => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
    (hesD : es0 = fun ψ c i => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
    (hmkD : mk0 = fun ψ c i => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
    {ctorTy : (Name → Nat) → AnnotTerm} {φ : Name → Nat} {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[j]? = some r)
    {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {rl : ConLeche.RecRule} (hplain : ConLeche.RecRule.fire rl = .plain)
    {mem : Nat → Nat} {jc : Nat}
    (hcj : (d.ctorsM (mem j))[jc]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem j) jc cA)
    (hlps : cA.1.levelParams = p.lps) (hdnP : d.nP = p.nP)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt j)
    (hmemk : mem j < d.k)
    (htgt : ∀ l, l < cA.2 → d.tgts (mem j) jc l < d.k)
    {K : Nat} (hjK : j < K)
    (hctorRead : ∀ ψ : Name → Nat,
      denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some (ctorTy ψ))
    (hfd : ∀ us : List Level, us.length = r.1.levelParams.length →
      blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
          (Level.substFn φ r.1.levelParams us) j i
        = liftDomsK (p.toBlockShape.rulePrefixAt j - d.nP) 0
            ((d.Fss (mem j) (Level.substFn φ r.1.levelParams us)).getD jc []))
    (hes : ∀ us : List Level, us.length = r.1.levelParams.length →
      blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC
          (Level.substFn φ r.1.levelParams us) j i
        = ((d.Ess (mem j) (Level.substFn φ r.1.levelParams us)).getD jc []).map
            (·.liftN (p.toBlockShape.rulePrefixAt j - d.nP) cA.2))
    (hlenP : ∀ us : List Level, us.length = r.1.levelParams.length →
      (d.params (Level.substFn φ r.1.levelParams us)).length = d.nP)
    (hparamsC : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ σ : Nat → V,
      Sat V (d.params (Level.substFn φ r.1.levelParams us)).reverse σ
        ↔ Sat V (((d.dsF (mem j) jc (Level.substFn φ r.1.levelParams us)).take d.nP).map
            (·.2.2)).reverse σ)
    (hsplit : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ ρ : Nat → V,
      BlockRecSplitAt V mpC.base2 d (Level.substFn φ r.1.levelParams us) K
        p.toBlockShape.rulePrefixAt mem
        (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) c') ρ)
    -- **THE GUARD** is the contract's own (`BlockRuleDataB`'s
    -- per-valuation `ℓ ≠ 0`, at the CHECKED elimination level
    -- `structElimLevel p.elim p.large`), and under it the COUNTING
    -- guard's two facts.  `hlarge`/`hct1` are the KERNEL's, in the
    -- dispatch's own spelling (`hK1 : ℓ ≠ 0 → d.w ψ = 0 →
    -- rs.length = 1` is the same guard's one-member half).
    (hlarge : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w (Level.substFn φ r.1.levelParams us) = 0 → d.large = true)
    (hct1 : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w (Level.substFn φ r.1.levelParams us) = 0 → (d.ctorsM (mem j)).length ≤ 1)
    (hread : ∀ us : List Level, us.length = r.1.levelParams.length →
      denoteMeta (blockRecAcv mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)
          (Level.substFn φ r.1.levelParams us) 0 rhs
        = some (blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
            (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) rhs
            (Level.substFn φ r.1.levelParams us)))
    (hokRa : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ ρ : Nat → V,
      WellDenotedV V ρ (blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) rhs
          (Level.substFn φ r.1.levelParams us)))
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hdF : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ (l : Nat) (x : Expr), (blockRuleFieldFvs p.toBlockShape rs j i)[l]? = some x →
        denoteMeta mpC.base2.acval envC (Level.substFn φ r.1.levelParams us)
            (p.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
              (Level.substFn φ r.1.levelParams us) j i).getD l default))
    (hokF : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ q, q < cA.2 → ∀ (σ : Nat → V) (vs ws : List V),
        SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) j) vs →
        SpineFit (consList vs σ)
          ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).take q) ws →
        WellDenotedV V (consList ws (consList vs σ))
          ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).getD q default))
    -- the residue producer's own premises (`blockRuleResidueB_run`), its
    -- `hsp` paid by `blockRuleFit_tele`
    (hndM : p.toBlockShape.memberNames.Nodup)
    {m₃ : EnvModel V (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC rs s
      (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
    (hleafCl : ∀ (ψ : Name → Nat) (q : Nat),
      Term.Closed ((blockRecLeafAV mpC.base2.acval envC rs s
        (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0) ψ q).erase))
    {lpsR : List Name}
    (hlps0 : ∀ r₀ : RecDatum, rs[0]? = some r₀ → r₀.1.levelParams = lpsR)
    (hin : ∀ us : List Level, us.length = r.1.levelParams.length →
      ConLeche.Model.Rules.RulesInputs V mpC.base2 (Level.substFn φ r.1.levelParams us))
    (hbdd : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ l, l < (pdoms0 (Level.substFn φ r.1.levelParams us) j
          ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i).length →
        Term.bvarsBelow l (((pdoms0 (Level.substFn φ r.1.levelParams us) j
          ++ fdoms0 (Level.substFn φ r.1.levelParams us) j i).getD l default).erase))
    (hbody : BlockRuleBodyOwed (V := V) mpC F p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs lpsR) :
    BlockRuleDataB (V := V) mpC p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs := by
  have hsp := blockRuleFit_tele hM hμ h hr hplain hcj hcf hdnP hnP hmemk htgt hjK hctorRead
    hfd hlenP hparamsC hsplit hlarge hct1
  refine blockRuleDataB_of_residue hM hμ h hpd hfdD hesD hmkD hr hcA hrhs hplain hcj hcf hlps
    hdnP hnP hmemk htgt hjK hctorRead hfd hes hlenP hparamsC hsplit hlarge hct1 hread hokRa
    hCf hCb hdF hokF ?_
  subst hpd hfdD hesD hmkD
  exact blockRuleResidueB_run h hndM hr hcA hrhs hac hleafCl hlps0 hnP hread hin hbdd hsp hbody

/-- **The contract at the run, its residue conjunct a premise** (lane
RECLIB): `blockRuleDataB_run` with the residue producer abstracted —
any `ihs`/`Rb0` whose residue conjunct follows from the contract's
first conjunct. -/
theorem blockRuleDataB_run_gen (hM : BlockModelAt mpC.base2 names d)
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {s : (Name → Nat) → Nat} {nCt : Nat → Nat}
    {pdoms0 : (Name → Nat) → Nat → List AnnotTerm}
    {fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    (hpd : pdoms0 = fun ψ c => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
    (hfdD : fdoms0 = fun ψ c i => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
    (hesD : es0 = fun ψ c i => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
    (hmkD : mk0 = fun ψ c i => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
    {ctorTy : (Name → Nat) → AnnotTerm} {φ : Name → Nat} {j i : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : rs[j]? = some r)
    {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[i]? = some rhs)
    {rl : ConLeche.RecRule} (hplain : ConLeche.RecRule.fire rl = .plain)
    {mem : Nat → Nat} {jc : Nat}
    (hcj : (d.ctorsM (mem j))[jc]? = some cA)
    (hcf : BlockCtorFacts mpC.base2 d lps (mem j) jc cA)
    (hlps : cA.1.levelParams = p.lps) (hdnP : d.nP = p.nP)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt j)
    (hmemk : mem j < d.k)
    (htgt : ∀ l, l < cA.2 → d.tgts (mem j) jc l < d.k)
    {K : Nat} (hjK : j < K)
    (hctorRead : ∀ ψ : Name → Nat,
      denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some (ctorTy ψ))
    (hfd : ∀ us : List Level, us.length = r.1.levelParams.length →
      blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
          (Level.substFn φ r.1.levelParams us) j i
        = liftDomsK (p.toBlockShape.rulePrefixAt j - d.nP) 0
            ((d.Fss (mem j) (Level.substFn φ r.1.levelParams us)).getD jc []))
    (hes : ∀ us : List Level, us.length = r.1.levelParams.length →
      blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC
          (Level.substFn φ r.1.levelParams us) j i
        = ((d.Ess (mem j) (Level.substFn φ r.1.levelParams us)).getD jc []).map
            (·.liftN (p.toBlockShape.rulePrefixAt j - d.nP) cA.2))
    (hlenP : ∀ us : List Level, us.length = r.1.levelParams.length →
      (d.params (Level.substFn φ r.1.levelParams us)).length = d.nP)
    (hparamsC : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ σ : Nat → V,
      Sat V (d.params (Level.substFn φ r.1.levelParams us)).reverse σ
        ↔ Sat V (((d.dsF (mem j) jc (Level.substFn φ r.1.levelParams us)).take d.nP).map
            (·.2.2)).reverse σ)
    (hsplit : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ ρ : Nat → V,
      BlockRecSplitAt V mpC.base2 d (Level.substFn φ r.1.levelParams us) K
        p.toBlockShape.rulePrefixAt mem
        (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) c') ρ)
    -- **THE GUARD** is the contract's own (`BlockRuleDataB`'s
    -- per-valuation `ℓ ≠ 0`, at the CHECKED elimination level
    -- `structElimLevel p.elim p.large`), and under it the COUNTING
    -- guard's two facts.  `hlarge`/`hct1` are the KERNEL's, in the
    -- dispatch's own spelling (`hK1 : ℓ ≠ 0 → d.w ψ = 0 →
    -- rs.length = 1` is the same guard's one-member half).
    (hlarge : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w (Level.substFn φ r.1.levelParams us) = 0 → d.large = true)
    (hct1 : ∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w (Level.substFn φ r.1.levelParams us) = 0 → (d.ctorsM (mem j)).length ≤ 1)
    (hread : ∀ us : List Level, us.length = r.1.levelParams.length →
      denoteMeta (blockRecAcv mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC)
          (Level.substFn φ r.1.levelParams us) 0 rhs
        = some (blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
            (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
            (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) rhs
            (Level.substFn φ r.1.levelParams us)))
    (hokRa : ∀ us : List Level, us.length = r.1.levelParams.length → ∀ ρ : Nat → V,
      WellDenotedV V ρ (blockRuleRaOf (blockRecAcv mpC.base2.acval envC rs s
          (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0))
          (consBlockRecs envC.find? p.toBlockShape p.nP 0 rs envC) rhs
          (Level.substFn φ r.1.levelParams us)))
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    (hdF : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ (l : Nat) (x : Expr), (blockRuleFieldFvs p.toBlockShape rs j i)[l]? = some x →
        denoteMeta mpC.base2.acval envC (Level.substFn φ r.1.levelParams us)
            (p.toBlockShape.rulePrefixAt j + l) (Expr.fvarTypeD x)
          = some ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
              (Level.substFn φ r.1.levelParams us) j i).getD l default))
    (hokF : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ q, q < cA.2 → ∀ (σ : Nat → V) (vs ws : List V),
        SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs
          (Level.substFn φ r.1.levelParams us) j) vs →
        SpineFit (consList vs σ)
          ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).take q) ws →
        WellDenotedV V (consList ws (consList vs σ))
          ((blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).getD q default))
    -- the residue conjunct, given the contract's first one (`blockRuleFit_tele`)
    (hres : (∀ us : List Level, us.length = r.1.levelParams.length →
      Level.eval (Level.substFn φ r.1.levelParams us)
        (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm) (restR restC : AnnotTerm),
        xs.length = p.toBlockShape.majorIdxAt j → ys.length = p.nP + cA.2 →
        usj.length = cA.1.levelParams.length →
        Level.substFn φ cA.1.levelParams usj
          = Level.substFn φ cA.1.levelParams
              (ConLeche.recFireComparands rl r.1.levelParams us cA.1.levelParams []
                (p.toBlockShape.rulePrefixAt j)).1 →
        IotaIndexPin (V := V) ρ restC p.nP
          (p.toBlockShape.majorIdxAt j) (p.toBlockShape.rulePrefixAt j) xs →
        TeleFitPA V ρ
          (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j)
          (xs ++ [AnnotTerm.mkAppN
            (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys]) restR →
        TeleFitPA V ρ (ctorTy (Level.substFn φ cA.1.levelParams usj)) ys restC →
        SpineFit ρ
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs
              (Level.substFn φ r.1.levelParams us) j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC
                (Level.substFn φ r.1.levelParams us) j i)
          ((xs.take (p.toBlockShape.rulePrefixAt j)).map (interp V ρ)
            ++ (ys.drop p.nP).map (interp V ρ))) →
      BlockRuleResidueB (V := V) mpC p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
        ctorTy φ j i r cA rl rhs) :
    BlockRuleDataB (V := V) mpC p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs := by
  have hsp := blockRuleFit_tele hM hμ h hr hplain hcj hcf hdnP hnP hmemk htgt hjK hctorRead
    hfd hlenP hparamsC hsplit hlarge hct1
  exact blockRuleDataB_of_residue hM hμ h hpd hfdD hesD hmkD hr hcA hrhs hplain hcj hcf hlps
    hdnP hnP hmemk htgt hjK hctorRead hfd hes hlenP hparamsC hsplit hlarge hct1 hread hokRa
    hCf hCb hdF hokF (hres (by subst hpd hfdD; exact hsp))

end DataRun

/-! ## 11. `hwd` AT THE FAMILY — a fold over the per-rule theorem

`BlockRecPre.hEq`'s grading (`hEq_iotaEqsAV_of`'s `hwd`,
`Semantics/Tower/BlockRecI.lean`) is, at ONE rule, `blockRuleHwd_of`
(`BlockRecPreRun.lean`):

```
FieldsOkB 0 σ (pdoms ++ fdoms) ∧
  ∀ ys, SpineFit σ (pdoms ++ fdoms) ys →
    WellDenoted V (consList ys σ) lhs ∧
      WellDenoted V (consList ys σ) (instsAV 0 ihs Rb)
```

and the family's `hwd` is that CONJUNCT for CONJUNCT at
`σ := consList rs ρ`, `lhs := ` the ι equation's left side and the
per-`(c, j)` data — so the family version is a λ, not a proof.

**What the fold does and does not cost.**  `BlockRuleCerts` is
frame-free by design, so the certificates are supplied ONCE per rule
and serve at every typed tuple; the three premises that DO mention the
frame (`hokA`, `hlhs`, `hihs`) have to be quantified over `rs`, and
that quantifier is the whole remaining content.  It is wider than the
candidate's own: the graph kit reads its `ih` values at the CHOSEN
candidate (`chainFrame K cand ρ`), while `hEq_iotaEqsAV_of` needs the grading at
EVERY tuple typed at the recursor types — `consList rs ρ` for any such
`rs`.  Whoever pays `hihs` pays it there, not at the candidate. -/

section HwdFamily

/-- **`hwd` at the family, from the per-rule certificates.**
`blockRuleHwd_of` at every `(c, j)` and every typed tuple.

The certificates `hcerts` are stated exactly as the graph kit states
them (`blockGraphKit`), so its producer plugs in unchanged; `hokA`, `hlhs` and `hihs` are `blockRuleHwd_of`'s own three
premises with the frame `σ` replaced by `consList rs ρ` and quantified
over the typed tuples, which is where the family's `hEq` reads them.

No new statement: every hypothesis is a `∀`-closure of a premise that
already exists, and the conclusion is `hEq_iotaEqsAV_of`'s `hwd`
character for character. -/
theorem blockRecHwd_of_rules {envT : Env} {mp : EnvModelM V μ envT} {ψ : Name → Nat}
    {Fu K : Nat} {nCt rP : Nat → Nat} {RecTy : Nat → AnnotTerm}
    {pdoms : Nat → List AnnotTerm} {fdoms es ihdoms ihs : Nat → Nat → List AnnotTerm}
    {mk Rb Ca : Nat → Nat → AnnotTerm} {ρ : Nat → V}
    (hμ : μ.verifiedChecks = true)
    (hcerts : ∀ c, c < K → ∀ j, j < nCt c →
      BlockRuleCerts V mp Fu ψ (rP c) (fdoms c j).length (ihdoms c j).length
        (pdoms c) (fdoms c j) (ihdoms c j) (Rb c j) (Ca c j))
    (hokA : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
      ∀ l, l < (pdoms c ++ fdoms c j).length → ∀ ys : List V,
        SpineFit (consList rs ρ) ((pdoms c ++ fdoms c j).take l) ys →
        WellDenoted V (consList ys (consList rs ρ))
          ((pdoms c ++ fdoms c j).getD l default))
    (hlhs : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
      ∀ ys : List V, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
        WellDenoted V (consList ys (consList rs ρ))
          (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
            (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])))
    (hihs : ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
      ∀ ys : List V, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
        (∀ v ∈ ihs c j, WellDenoted V (consList ys (consList rs ρ)) v) ∧
          SpineFit (consList ys (consList rs ρ)) (ihdoms c j)
            ((ihs c j).map (interp V (consList ys (consList rs ρ))))) :
    ∀ rs : List V, rs.length = K →
      (∀ c, c < K → rs.getD c pt ∈ˢ interp V ρ (RecTy c)) →
      ∀ c, c < K → ∀ j, j < nCt c →
        FieldsOkB 0 (consList rs ρ) (pdoms c ++ fdoms c j) ∧
        ∀ ys, SpineFit (consList rs ρ) (pdoms c ++ fdoms c j) ys →
          WellDenoted V (consList ys (consList rs ρ))
              (AnnotTerm.mkAppN (.bvar ((pdoms c).length + (fdoms c j).length + (K - 1 - c)))
                (prefVarsAV (pdoms c).length (fdoms c j).length ++ es c j ++ [mk c j])) ∧
            WellDenoted V (consList ys (consList rs ρ)) (instsAV 0 (ihs c j) (Rb c j)) :=
  fun rs hlen hmem c hc j hj =>
    blockRuleHwd_of hμ (hcerts c hc j hj) (hokA rs hlen hmem c hc j hj)
      (hlhs rs hlen hmem c hc j hj) (hihs rs hlen hmem c hc j hj)

end HwdFamily

/-! ## 13. The rule domains' bounds at the seam

Upstream of the regime's dispatch (`BlockRecPreHpre.lean`), whose
`hspF` needs the field half; the seam (`BlockDeclRun.lean`) consumes it
too. -/

section DomsBounded

variable {envC : Env} {pp : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {mpC : EnvModelM V μ envC} {F : Nat}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {env₀ : Env} {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
  {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}

omit [SetTheory V] in
/-- A bounded field chain stays bounded, `K` higher, under `liftDomsK` at ANY
cutoff (`fieldsBelow_liftDomsK` is the cutoff-equals-bound case). -/
theorem fieldsBelow_liftDomsK_at (K : Nat) :
    ∀ {m k : Nat} {Fs : List AnnotTerm}, FieldsBelow m Fs → FieldsBelow (m + K) (liftDomsK K k Fs)
  | _, _, [], _ => trivial
  | m, k, _ :: Fs, h =>
    ⟨bvarsBelow_liftN_add h.1 (Nat.le_refl _) k, by
      have := fieldsBelow_liftDomsK_at K (m := m + 1) (k := k + 1) (Fs := Fs) h.2
      rwa [show m + 1 + K = m + K + 1 from by omega] at this⟩

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

/-- **The rule domains' own bounds, at every level valuation** — the prefix half is `blockRulePdomsAV_bounded`, the
field half is the constructor's field domains (`CtorDataI.below`,
dropped past the parameters) lifted past the rule prefix's non-parameter
stretch (`blockRuleFdomsAV_eq`). -/
theorem blockRuleDoms_bounded_at (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC pp cvTas ctorsAs = .ok rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k) :
    ∀ (ψ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr), r.2.2.2[i]? = some cA →
      r.2.1[i]? = some rhs →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i).length →
        Term.bvarsBelow l (((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i).getD l default).erase) := by
  intro ψ j r hr i cA rhs hcA hrhs l hl
  -- the member link and the constructor's data
  obtain ⟨ms, hms, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
  have hmemk : pp.toBlockShape.recTgtAt j
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt j))[i]? = some cA := by
    show (ctorsAs.getD _ [])[i]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk i cA hcj
  obtain ⟨-, -, hcd⟩ := hcore.2.2.1 _ i cA hcj
  have hCf : cA.1.type.hasFvar = false := (mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)).1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
  have hnP := TE.nP_le
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  -- the two halves' bounds
  have hfd := (blockRuleFdomsAV_eq h hr hcA hrhs hcd hCf hnP ψ).1
  have hfB : FieldsBelow (pp.toBlockShape.rulePrefixAt j)
      (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i) := by
    rw [hfd]
    have hd := ConLeche.Model.DomsBelow.drop pp.nP (hcd.below ψ)
    rw [Nat.zero_add] at hd
    have := fieldsBelow_liftDomsK_at (pp.toBlockShape.rulePrefixAt j - pp.nP) (k := 0) hd.fields
    rwa [show pp.nP + (pp.toBlockShape.rulePrefixAt j - pp.nP)
      = pp.toBlockShape.rulePrefixAt j from by omega] at this
  rcases Nat.lt_or_ge l (pp.toBlockShape.rulePrefixAt j) with hlt | hge
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hpl]; exact hlt),
      ← List.getD_eq_getElem?_getD]
    exact blockRulePdomsAV_bounded hμ mpC h hr ψ l (by rw [hpl]; exact hlt)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hpl]; exact hge),
      ← List.getD_eq_getElem?_getD, hpl]
    have hq : l - pp.toBlockShape.rulePrefixAt j
        < (blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC ψ j i).length := by
      rw [List.length_append, hpl] at hl; omega
    have := fieldsBelow_getD hfB _ hq
    rwa [show pp.toBlockShape.rulePrefixAt j + (l - pp.toBlockShape.rulePrefixAt j) = l
      from by omega] at this

/-- **The rule domains' own bounds, at the seam** — the residue
producer's `hbdd`: the prefix half is `blockRulePdomsAV_bounded`, the
field half is the constructor's field domains (`CtorDataI.below`,
dropped past the parameters) lifted past the rule prefix's non-parameter
stretch (`blockRuleFdomsAV_eq`). -/
theorem blockRuleDoms_bounded_seam (hμ : μ.verifiedChecks = true)
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC pp cvTas ctorsAs = .ok rs)
    (hcore : BlockCtorsCore mpC.base2
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) pp.lps cvTas
      pp.toBlockShape isRec A
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k) :
    ∀ (φ : Name → Nat) (j : Nat)
        (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr), r.2.2.2[i]? = some cA →
      r.2.1[i]? = some rhs →
      ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs
            (Level.substFn φ r.1.levelParams us) j
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).length →
        Term.bvarsBelow l (((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs
            (Level.substFn φ r.1.levelParams us) j
          ++ blockRuleFdomsAV pp.toBlockShape rs mpC.base2.acval envC
            (Level.substFn φ r.1.levelParams us) j i).getD l default).erase) :=
  fun φ j r hr i cA rhs hcA hrhs us _ =>
    blockRuleDoms_bounded_at hμ h hcore (Level.substFn φ r.1.levelParams us) j r hr i cA rhs hcA hrhs

end DomsBounded

end ConLeche.Model
