module

public import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.BlockModel

public section

/-!
# The per-pair rule obligation's FIT and FIRED SPINE (task #315, M5 model half)

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
* **§3 the fit and the fired spine**, and **§3b the index reading**,
  which is the same `ChainFit`'s SECOND conjunct read backwards.

Both findings below (§4, §5) are `d.w ψ = 0` refutations: the fit and
the index reading are BOTH false at a `Prop`-valued block, with
different witnesses, and both are closed here at `d.w ψ ≠ 0`.
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

/-! ## 3. The two conjuncts -/

variable {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

/-- **`BlockRecSplitAt` at the CONTRACT's own recursor fit.**  The
contract hands `TeleFitPA` of the recursor type at `xs ++ [maj]`;
`spineFit_blockRecTy` turns it into a fit of the binder data, which is
what O-2's split consumes.  Out come the three facts the field half
needs: the block's PARAMETERS fit at the recursor's own prefix, the
recursor's index arguments fit the eliminated member's index
telescope there, and the MAJOR lies in that member's former applied to
both.

`BlockRecSplitAt` has no producer (`AUDIT-premises.md` §2.6); it is the
recursor-type lane's, and this theorem is its first consumer. -/
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

/-- **`BlockRuleDataB`'s FIRST conjunct at the run** — the prefix half
(`blockRuleHspPref_run`, landed) and the FIELD half, appended.

The field half is `blockRecSpF_of` at `K = 0` (§1) over the
`ChainFit` at the recursor's parameters (§2), and its three
block-facing premises come from `BlockRecSplitAt` at the contract's
own recursor fit.

**`hw : d.w ψ ≠ 0` is essential and the conjunct is REFUTABLE without
it** — see §4's FINDING. -/
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
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q) (hw : d.w ψ ≠ 0)
    {ρ : Nat → V} {xs ys : List AnnotTerm} {restR : AnnotTerm}
    (hxl : xs.length = p.toBlockShape.majorIdxAt c)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)
      (xs ++ [AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    {K : Nat} (hcK : c < K)
    (hsplit : BlockRecSplitAt V mpC.base2 d ψ K p.toBlockShape.rulePrefixAt mem
      (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c') ρ)
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss (mem c) ψ).getD j []) ((ys.drop d.nP).map (interp V ρ))) :
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
  refine blockRecSpF_base (j := j) (mem := mem) (cA := cA) hM hμ h hr hcj hcf hfd
    (by rw [List.length_take, hxsLen]; omega) hps htgt
    (Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _))
    (List.getElem?_eq_some_iff.mp hcj).1 (tupW_mem hidx) (lfpTuple_mem _ _ _ _) hxsLen
    (blockRuleHspPref_run hμ mpC h hr ψ hxl hfitR) ?_
  exact blockRuleChainFit_run hM hcj hcf.1 hmemk hlv hw hps hidx hqs hfq hmaj

/-- **The field spine as a `SpineFit`** — `ChainFit`'s `FitsFrom` at
the block's slots, read as a fit of the field domains, through §25's
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
injection does not mention the parameters at all
(`blockCtorFold_params_blind`'s content, used here as its two halves)
— so the conjunct is `blockRecMkK_value` at `K = 0` against
`blockCtorMajor_value`.

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
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q) (hw : d.w ψ ≠ 0)
    {ρ : Nat → V} {xs ys : List AnnotTerm} {restR : AnnotTerm}
    (hxl : xs.length = p.toBlockShape.majorIdxAt c)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)
      (xs ++ [AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    {K : Nat} (hcK : c < K)
    (hsplit : BlockRecSplitAt V mpC.base2 d ψ K p.toBlockShape.rulePrefixAt mem
      (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c') ρ)
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss (mem c) ψ).getD j []) ((ys.drop d.nP).map (interp V ρ))) :
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
  have hfit := blockRuleChainFit_run hM hcj hcf.1 hmemk hlv hw hps hidx hqs hfq hmaj
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

/-- **`mk` at a `Prop`-valued block.**  At `d.w ψ = 0` every value in
the block is the point, so both sides of the conjunct are the point
and NO fit is needed — the `w`-split that §4's finding forces on the
FIT half does not reach the fired spine.

`hzero` is the constructors' stage's own clause at `d.w ψ = 0`: the
constructor's leaf is `sumMkAV 0 …`, whose every application folds to
the point (`blockModelAt_of_records`' `hctorLeaf`, `sumMkAV_zero`,
`foldl_app_pt`).  It is not a `BlockModelAt` field, which is why it
is named here. -/
theorem blockRuleHmk_zero
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {i : Nat} {cA : ConstantVal × Nat}
    {rhs : Expr} {ψ ψj : Name → Nat}
    (hcA : r.2.2.2[i]? = some cA) (hrhs : r.2.1[i]? = some rhs)
    {nPd nF : Nat} (hfind : envC.find? cA.1.name = some (.ctorInfo cA.1 nPd nF))
    (hlps : cA.1.levelParams = p.lps)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c)
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    {ρ : Nat → V} {L : List V} {ys : List AnnotTerm}
    (hzero : ∀ vs : List V, vs.foldl app (interp V ρ (mpC.base2.acval cA.1.name ψ)) = pt) :
    interp V (consList L ρ) (blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ c i)
      = interp V ρ (AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys) := by
  rw [blockRuleMkAV_eq h hr hcA hrhs hfind (by rw [← hlps]; rfl) hnP ψ,
    interp_mkAppN, foldl_app_map,
    acval_interp_closedC mpC.base2 cA.1.name _ (consList L ρ) ρ,
    Level.substFn_param_self ψ p.lps,
    mpC.base2.acval_params cA.1.name _ hfind ψj ψ hlv, interp_mkAppN_map, hzero, hzero]

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
named premise — RM11's `blockRuleEsAV_eq` composed with the record's
`Es`/`Ess` identification) moves the syntactic `es0` onto the datum's
`Ess`, and `interp_liftN_rule` at `K = 0` moves the reading from the
rule's frame to the block's.

**`hw : d.w ψ ≠ 0` is essential and the conjunct is REFUTABLE without
it** — see §5's FINDING, which is a DIFFERENT witness from §4's. -/
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
    (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q) (hw : d.w ψ ≠ 0)
    {ρ : Nat → V} {xs ys : List AnnotTerm} {restR : AnnotTerm}
    (hxl : xs.length = p.toBlockShape.majorIdxAt c)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)
      (xs ++ [AnnotTerm.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    {K : Nat} (hcK : c < K)
    (hsplit : BlockRecSplitAt V mpC.base2 d ψ K p.toBlockShape.rulePrefixAt mem
      (fun c' => blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c') ρ)
    (hqs : SpineFit ρ (d.params ψ) ((ys.take d.nP).map (interp V ρ)))
    (hfq : SpineFit (consList ((ys.take d.nP).map (interp V ρ)) ρ)
      ((d.Fss (mem c) ψ).getD j []) ((ys.drop d.nP).map (interp V ρ))) :
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
  have hfit := blockRuleChainFit_run hM hcj hcf.1 hmemk hlv hw hps hidx hqs hfq hmaj
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
constructor's parameter and field spines fit).  None of the three is
the seam's to supply: all three are consequences of premises
`BlockRuleDataB` already hands — `hψ` for the first, `hfitC` for the
other two — and they are produced here, so that what is left between
the three conjuncts and the contract is the rule lane's two rows and
the `w`-ruling and nothing else. -/

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
`d.nP`.  This is `blockCtorSpine_split`'s first consumer. -/
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

/-! ## 3d. THE COMPOSITION — a theorem whose CONCLUSION is
`BlockRuleDataB`

Five of the obligation's six statements have a theorem each (§3, §3b)
and the sixth pair is the rule lane's; until this section nothing
COMPOSED them, so the obligation itself was the one statement with no
producer.  `blockRuleDataB_of_residue` is that producer: it fixes the
four syntactic components at the lane's own readings
(`blockRulePdomsAV`/`blockRuleFdomsAV`/`blockRuleEsAV`/`blockRuleMkAV`,
which is what `declBlock_data`'s existential is instantiated at),
takes the residue and the tower fit as the SINGLE premise
`BlockRuleResidueB`, and discharges the other three conjuncts from the
run.

Every ψ-indexed premise is bounded by the contract's own telescope —
the level assignment a conjunct is asked at is `Level.substFn φ
r.1.levelParams us` for a `us` of the recursor's own length, never an
arbitrary `ψ` — and **the `w`-guard `hw` is one of them**: the
obligation is closed at `d.w ψ ≠ 0` only, because conjuncts ① and ②
are REFUTABLE below that (§4, §5), and the guard is written at the
telescope's instantiations so that a later ruling can replace it
without touching the rest of the signature. -/

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
the datum's (`hfd`, `hes`), the recursor type's split (`hsplit`, the
recursor-type lane's `BlockRecSplitAt`), the constructors' stage's
parameter clauses (`hlenP`, `hparamsC`), the block's own
`d.nP = p.nP`, and the `w`-guard. -/
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
    (hw : ∀ us : List Level, us.length = r.1.levelParams.length →
      d.w (Level.substFn φ r.1.levelParams us) ≠ 0)
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
    (hres : BlockRuleResidueB (V := V) mpC p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs) :
    BlockRuleDataB (V := V) mpC p rs s nCt pdoms0 fdoms0 es0 ihs mk0 Rb0
      ctorTy φ j i r cA rl rhs := by
  intro us hus usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC
  have hnPd : d.nP ≤ p.toBlockShape.rulePrefixAt j := by rw [hdnP]; exact hnP
  have hlv := blockRuleLevelAgree hplain hψ
  obtain ⟨hqs, hfq⟩ := blockRuleCtorFit_run (d := d) hcj hcf hlv (hlenP us hus)
    (hparamsC us hus) (by rw [hyl, hdnP]) (hctorRead _) hfitC
  obtain ⟨hbody, htow⟩ :=
    hres us hus usj ρ xs ys restR restC hxl hyl husjl hψ hidx hfitR hfitC
  subst hpd; subst hfdD; subst hesD; subst hmkD
  refine ⟨?_, ?_, ?_, ?_, htow⟩
  · have hq := blockRuleHsp_field_run (i := i) hM hμ h hr hcj hcf (hfd us hus) hmemk hnPd
      htgt hlv (hw us hus) hxl hfitR hjK (hsplit us hus ρ) hqs hfq
    rwa [hdnP] at hq
  · have hq := blockRuleHes_run hM hμ h hr hcj hcf (hes us hus) hmemk hnPd htgt hlv
      (hw us hus) hxl hfitR hjK (hsplit us hus ρ) hqs hfq
    rwa [hdnP] at hq
  · have hq := blockRuleHmk_run hM hμ h hr hcA hrhs hcj hcf hlps hdnP hnP (hfd us hus)
      hmemk htgt hlv (hw us hus) hxl hfitR hjK (hsplit us hus ρ) hqs hfq
    rwa [hdnP] at hq
  · intro a hleaf
    exact blockRuleHRa_tower_run h hr hcA hrhs (hread us hus) (hokRa us hus ρ) htow
      (hbody a hleaf)

/-! ## 4. THE FINDING — the FIT conjunct is FALSE at a `Prop`-valued
block

`BlockRuleDataB`'s first conjunct — the recursor's prefix and the
constructor's fields fit the rule's domains — is **refutable** at
`d.w ψ = 0`, and the `hw` above is not a convenience of the proof.

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

**What this costs and where it goes.**  The other conjunct this lane
owns, `mk`, is NOT affected: at `d.w ψ = 0` both sides are the point
(`blockRuleHmk_zero`), with no fit anywhere.  So the repair is local
to the FIT, and the design question — which is the coordinator's, not
this lane's — is what the contract asks for at `d.w ψ = 0`:

* at `ℓ = 0` (a `Prop` motive, the ordinary case for a `Prop`-valued
  block) the ι equation is an equation between PROOFS, both the
  point, so the fit is not needed at all and the conjunct should be
  guarded by `d.w ψ ≠ 0`;
* at `ℓ ≠ 0` (large elimination from a subsingleton) the attack is
  blocked by `IotaIndexPin` wherever the mismatched field is an INDEX
  of the result — `Acc.intro`'s `x` is, and the pin forces the
  recursor's index value to BE the field's value — but that is an
  argument about the SYNTAX of subsingleton-eliminating blocks and
  has to be written; it is not a consequence of anything landed.

Until it is decided, the fit half is proved under `hw`, and the
per-pair obligation is closed at `d.w ψ ≠ 0` only. -/

/-! ## 5. THE SECOND FINDING — the INDEX READING is FALSE at a
`Prop`-valued block too, and the witness is in Mathlib

`BlockRuleDataB`'s second conjunct — the rule's index expressions read
to the recursor's own index arguments — is **refutable** at
`d.w ψ = 0`, by a DIFFERENT witness from §4's.  §4's `Exists` cannot
refute this row at all: it has no indices, so the conjunct is
`[] = []`.  What this row needs is a block with an INDEX whose
constructor-side expression is a PARAMETER, and a SECOND constructor
to keep the carrier inhabited at a *different* index.

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

**It is the same hole as §4's, one conjunct along.**  The rule is
`paramsBlind`, so the only tie between the constructor's parameter
spine and the recursor's is the major premise's membership; at
`d.w ψ = 0` every value is the point and the membership says only
that SOME constructor's `ChainFit` holds at the recursor's index
tuple — here `tail`'s, not `refl`'s.  `blockCarrier_case` delivers a
`j'`, and it is `mkInj` — `d.w ψ ≠ 0` — that makes `j' = j`.

**Where the two witnesses agree, and what that buys the ruling.**
Both `Exists` and `ReflTransGen` are `ℓ = 0` blocks: `Exists` is not
subsingleton-eliminating (its field `w` is neither a proof nor an
argument of the conclusion) and `ReflTransGen` has two constructors.
So BOTH refutations live in the region where the ι equation is an
equation between PROOFS, and the `d.w ψ ≠ 0` guard on both conjuncts
is the repair the coordinator's first bullet already describes.
Neither witness reaches the `ℓ ≠ 0` region, and the argument there is
still unwritten — but it is now narrower for this row than for the
fit: subsingleton elimination needs ONE constructor, and with one
constructor `blockCarrier_case`'s `j'` is `j` with no `mkInj` at all.
What would remain at `ℓ ≠ 0` is the FIELD spine (`fs'` need not be
`fs` without `mkInj`), so the row closes there exactly when the index
expressions' readings do not depend on the fields, or where
`IotaIndexPin` pins the ones that do — `Acc.intro`'s `x` is pinned,
and `inductive P (α) (a : α) : α → Prop | mk : P α a a` needs no pin
because its single constructor forces `i_R = a_R` through `hfitR`.

Until the ruling, the row is closed at `d.w ψ ≠ 0`
(`blockRuleHes_run`), like the fit. -/

end ConLeche.Model
