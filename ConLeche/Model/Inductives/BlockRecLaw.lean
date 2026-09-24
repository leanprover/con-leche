module

public import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockStageRec
public import ConLeche.Model.Inductives.BlockRecMem
public import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.StructTele
import ConLeche.Verify.Inductives.SumRec
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.StructRecLawKit

public section

/-!
# The LAST HOP: every stored rule's `RecRuleLaw`

`blockRecStaged_of` (`Model/Inductives/BlockStageRec.lean`) owes one
premise about the ι content of the recursors' cons:

```
hrecP : ∀ m₃ : EnvModel V (consBlockRecs envC.find? q nP 0 rs envC),
  m₃.acval = acv → ∀ φ : Name → Nat, RecRules m₃ φ
```

`RecRules` is keyed on EVERY stored recursor of the consed
environment, so it splits — by `find?_consBlockRecs_inv` — into two
disjoint halves:

* **the PRE-EXISTING recursors**, whose laws are `mpC.rec_rules`
  transported across the cons.  That is this module's §1
  (`recRuleLaw_consBlockRecs_prefix`), the `consBlockRecs` twin of
  `recRuleLaw_cons_prefix` (`Model/RecRulesCons.lean`): the crossing
  is `denoteMeta_consBlockRecs_mono` in place of `denoteMeta_cons_mono`
  and the valuation's agreement off the new names (`hag`) in place of
  `acvalWith_ne`.  No premise beyond `blockRecStaged_of`'s own;
* **the `k` NEW recursors**, whose rules are `sumRules`' — the last
  hop proper (§2–§4): `blockRecAV_iota`'s extracted ι equation is
  `RecRuleLaw`'s equality once (a) the two `TeleFitPA` fits are
  flipped to the `SpineFit`s the ι law is stated at, (b) the stored
  right-hand side's reading is exhibited as the residue's λ-tower and
  its application β-reduced, and (c) the residue's reading at the ih
  values is identified with the stored body's —
  `interp_abstractIh` (`Model/Inductives/BlockRecRule.lean`).

The rule data (`pdoms`/`fdoms`/`es`/`mk`/`ihs`/`Rb`) is NOT re-derived
here: it is named, in the spelling the family premise `BlockRecPre`
(`Semantics/Tower/BlockRecI.lean`) is stated at, and the run's own identification of
it lives with the rule data.  What this module owns is the
CONVERSION — from the semantic ι law to the syntactic contract — and
the two `TeleFitPA → SpineFit` flips it needs.
-/

namespace ConLeche.Model

open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo RecRule BlockShape
  consBlockRecs)
open ConLeche.Verify (openRev)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The PRE-EXISTING recursors' laws, across the cons

`recRuleLaw_cons_prefix`'s argument, at `consBlockRecs` rather than at
one fresh cons.  Every piece of `RecRuleLaw` that mentions the
environment is either a LOOKUP (preserved, `find?_consBlockRecs_keep`),
a READING of a subject bound by the constructors' environment (moved
forward by `denoteMeta_consBlockRecs_mono`, then identified with the
one in hand because `denoteMeta` is a function), or one of the TWO
LEAVES the law names — the recursor's and its rule's constructor's,
both stored in `envC`, hence not among the `k` new names, hence
`hag`'s.

The `k` conses are crossed in ONE step rather than iterated: the
iterated form would need an `EnvModelM` at each intermediate
environment, and the statement `hrecP` is posed at is about an
arbitrary `EnvModel` of the final one. -/

/-- **A stored recursor's law crosses the recursors' cons.** -/
theorem recRuleLaw_consBlockRecs_prefix {q : BlockShape} {nP : Nat} {rs : List RecDatum}
    {envC : Env} {acv : Name → (Name → Nat) → AnnotTerm} (mpC : EnvModelM V μ envC)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hpsh : ∀ r ∈ rs, r.1.name.isProjFnShape = false)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
    (m₃ : EnvModel V (consBlockRecs envC.find? q nP 0 rs envC))
    (hac : m₃.acval = acv) (φ : Name → Nat)
    {n : Name} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    (hfE : envC.find? n = some (.recInfo cv mI rP rules))
    {rl : RecRule} (hmem : rl ∈ rules) (hfire : RecRule.fire rl ≠ .inert) :
    RecRuleLaw m₃ φ n cv mI rP rl := by
  -- the valuation at a STORED name is the constructors' environment's
  have hacvAt : ∀ x : Name, (envC.find? x).isSome = true →
      m₃.acval x = mpC.base2.acval x := by
    intro x hx
    rw [hac]
    refine hag x fun r hr hh => ?_
    rw [hh, hfr r hr] at hx
    exact nomatch hx
  have hmono : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr), ConstsBound envC e →
      ∀ {ea : AnnotTerm}, denoteMeta mpC.base2.acval envC ψ d e = some ea →
        denoteMeta m₃.acval (consBlockRecs envC.find? q nP 0 rs envC) ψ d e = some ea := by
    intro ψ d e hcb ea h
    rw [hac]
    exact denoteMeta_consBlockRecs_mono hfr hpsh hag ψ d e hcb h
  obtain ⟨hrPle, hlaw0⟩ := mpC.rec_rules φ n cv mI rP rules hfE rl hmem hfire
  refine ⟨hrPle, fun us hlen => ?_⟩
  obtain ⟨Ra, hRa0, hokRa, hpinsOk, hlaw⟩ := hlaw0 us hlen
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    mpC.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfE)
  obtain ⟨-, -, hRres, -, hnest⟩ := hrec' cv mI rP rules rfl rl hmem
  -- a rule pin's subject resolves at the constructors' environment
  have hpinCB : ∀ (lvls : List Level) (pins : List Expr),
      RecRule.fire rl = .nested lvls pins → ∀ i : Nat,
        ConstsBound envC (openRev 0 rP
          ((pins.getD i default).instantiateLevelParams cv.levelParams us)) := by
    intro lvls pins hn i
    obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hn
    refine constsBound_openRev (constsBound_of_constsResolve _ ?_) 0 rP
    rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
    by_cases hilt : i < pins.length
    · exact (hpinsWf _ (ConLeche.getD_mem hilt)).2.2.1
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  refine ⟨Ra, hmono _ 0 _ (constsBound_of_constsResolve _ (by
      rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
      exact hRres)) hRa0, hokRa, ?_, ?_⟩
  · -- the pins' carried readings, moved forward
    intro lvls pins hn i hi
    obtain ⟨vpa, hvpa, hok⟩ := hpinsOk lvls pins hn i hi
    refine ⟨vpa, hmono _ rP _ (hpinCB lvls pins hn i) hvpa, ?_⟩
    intro ρ zs TVa restR hzl hzok hTVa hfit
    obtain ⟨TVa', hTVa', -, -⟩ := mpC.constType 0 n _ us hfE rfl (by exact hlen)
    obtain rfl : TVa' = TVa :=
      Option.some.inj ((hmono _ 0 _ (constsBound_instType mpC.base2.wf
        (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa').symm.trans hTVa)
    exact hok ρ zs TVa' restR hzl hzok hTVa' hfit
  · intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl hujl
      hψ hplain hnested hpin hTVa hTVja hfitR hfitC
    -- the rule's constructor is stored in the constructors' environment
    have hfcjE : envC.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) := by
      obtain ⟨⟨cvj', cnP', cnF', h0⟩, -, -⟩ :=
        mpC.base2.rec_ctors n cv mI rP rules hfE rl hmem
      have heq := Option.some.inj
        ((find?_consBlockRecs_keep (q := q) (nP := nP) hfr _ _ h0).symm.trans hfcj)
      rw [← heq]
      exact h0
    -- the two leaves the law names are the prefix's
    have hacvR : m₃.acval n = mpC.base2.acval n := hacvAt n (by rw [hfE]; rfl)
    have hacvC : m₃.acval (RecRule.ctor rl) = mpC.base2.acval (RecRule.ctor rl) :=
      hacvAt _ (by rw [hfcjE]; rfl)
    -- the two stored types: produced at the prefix, moved forward,
    -- identified with the readings in hand by determinism
    obtain ⟨TVa', hTVa', -, -⟩ := mpC.constType 0 n _ us hfE rfl (by exact hlen)
    obtain rfl : TVa' = TVa :=
      Option.some.inj ((hmono _ 0 _ (constsBound_instType mpC.base2.wf
        (ConLeche.Semantics.Env.find?_mem hfE) us) hTVa').symm.trans hTVa)
    obtain ⟨TVja', hTVja', -, -⟩ :=
      mpC.constType 0 (RecRule.ctor rl) _ usj hfcjE rfl (by exact hujl)
    obtain rfl : TVja' = TVja :=
      Option.some.inj ((hmono _ 0 _ (constsBound_instType mpC.base2.wf
        (ConLeche.Semantics.Env.find?_mem hfcjE) usj) hTVja').symm.trans hTVja)
    -- the `.nested` premise, contravariantly
    have hnested' : ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
        ∀ i, i < RecRule.ctorParams rl →
        ∀ vpa : AnnotTerm,
          denoteMeta mpC.base2.acval envC φ rP
            (openRev 0 rP ((pins.getD i default).instantiateLevelParams
              cv.levelParams us)) = some vpa →
          interp V ρ (ys.getD i default)
            = interp V ρ (AnnotTerm.instRevChain (xs.take rP) vpa) := by
      intro lvls pins hn i hi vpa hvpa
      exact hnested lvls pins hn i hi vpa (hmono _ rP _ (hpinCB lvls pins hn i) hvpa)
    rw [hacvC] at hfitR
    rw [hacvR, hacvC]
    exact hlaw cvj cnP cnF hfcjE usj ρ xs ys _ _ restR restC hxl hyl
      hujl hψ hplain hnested' hpin hTVa' hTVja' hfitR hfitC

/-! ## 2. The split: `RecRules` at the recursors' environment

`find?_consBlockRecs_inv` (`Model/Inductives/BlockStageRec.lean`) is
the only inversion of the cons needed here: a recursor stored at the
consed environment is either one of the constructors' environment's —
§1 — or the `j`-th of the block, with `sumRules`' rules and the shape
`q` dictates.  So `hrecP` is §1 plus ONE premise, per NEW recursor and
per rule. -/

/-- **`hrecP`, split.**  The pre-existing recursors' rows are §1; the
`k` new ones' are the premise `hnew`, stated at the rule list the cons
actually stores. -/
theorem recRules_consBlockRecs_of {q : BlockShape} {nP : Nat} {rs : List RecDatum}
    {envC : Env} {acv : Name → (Name → Nat) → AnnotTerm} (mpC : EnvModelM V μ envC)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hpsh : ∀ r ∈ rs, r.1.name.isProjFnShape = false)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
    (m₃ : EnvModel V (consBlockRecs envC.find? q nP 0 rs envC))
    (hac : m₃.acval = acv) (φ : Name → Nat)
    (hnew : ∀ (j : Nat) (r : RecDatum), rs[j]? = some r →
      ∀ rl ∈ ConLeche.sumRules envC.find? r.1.name nP (q.majorIdxAt j) (q.rulePrefixAt j)
        r.1.type r.2.2.2 r.2.1,
      RecRule.fire rl ≠ .inert →
        RecRuleLaw m₃ φ r.1.name r.1 (q.majorIdxAt j) (q.rulePrefixAt j) rl) :
    RecRules m₃ φ := by
  intro n cv mI rP rules hf rl hmem hfire
  rcases find?_consBlockRecs_inv hf with hE | ⟨j, r, hr, rfl, hci⟩
  · exact recRuleLaw_consBlockRecs_prefix mpC hfr hpsh hag m₃ hac φ hE hmem hfire
  · rw [Nat.zero_add] at hci
    obtain ⟨rfl, rfl, rfl, rfl⟩ :
        cv = r.1 ∧ mI = q.majorIdxAt j ∧ rP = q.rulePrefixAt j ∧
          rules = ConLeche.sumRules envC.find? r.1.name nP (q.majorIdxAt j)
            (q.rulePrefixAt j) r.1.type r.2.2.2 r.2.1 := by
      injection hci with h1 h2 h3 h4
      exact ⟨h1, h2, h3, h4⟩
    exact hnew j r hr rl hmem hfire


/-! ## 3. The `TeleFitPA → SpineFit` flip

`RecRuleLaw` states its two fits as `TeleFitPA`s of the stored types'
READINGS; the family's ι law (`blockRecAV_iota`) is stated at
`SpineFit`s of the binder data.  The flip is the generic kit at
`k = 1` — `teleFitPA_to_chain` through a `PiTeleAV` of the tower, then
`spineFit_of_chain` — and its ENTRY CONDITION is that the fitted
reading BE a `mkPisAV` tower, which for a block recursor is
`recStage_tyPis`' third conjunct (`Model/Inductives/BlockRecMem.lean`:
the stream's type is stored as is, so its reading is identified by the
run's own Π-peel). -/

/-- **A fit of a Π-tower reading is a `SpineFit` of its domains.** -/
theorem spineFit_of_teleFitPA {pds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}
    {ρ : Nat → V} {ws : List AnnotTerm} {rest : AnnotTerm}
    (hlen : ws.length = pds.length)
    (hfit : TeleFitPA V ρ (mkPisAV pds b) ws rest) :
    SpineFit ρ (pds.map (·.2.2)) (ws.map (interp V ρ)) := by
  have htele := piTeleAV_of_stripPisAV (stripPisAV_mkPisAV pds b)
  refine spineFit_of_chain (by simpa using hlen) ?_
  intro n hn
  have := teleFitPA_to_chain pds.length htele hlen hfit n (by simpa using hn)
  simpa using this

/-- **The block recursor's own flip**, at the run: whatever fits the
`i`-th stored recursor type's reading fits its binder data. -/
theorem spineFit_blockRecTy {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List RecDatum} {F : Nat}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {i : Nat} {r : RecDatum} (hr : rs[i]? = some r) (ψ : Name → Nat)
    {ρ : Nat → V} {ws : List AnnotTerm} {rest TVa : AnnotTerm}
    (hTVa : denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some TVa)
    (hlen : ws.length = p.toBlockShape.majorIdxAt i + 1)
    (hfit : TeleFitPA V ρ TVa ws rest) :
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i).map (·.2.2))
      (ws.map (interp V ρ)) := by
  obtain ⟨-, -, -, hread, hpis, hrdsLen, -, -, -⟩ := recStage_tyPis hμ mpC h hr ψ
  obtain rfl : TVa = blockRecTyAV mpC.base2.acval envC rs ψ i :=
    Option.some.inj (hTVa.symm.trans hread)
  rw [hpis] at hfit
  exact spineFit_of_teleFitPA (by rw [hlen, hrdsLen]) hfit

/-! ## 4. The CONVERSION: the ι equation is the rule's equality

`blockRecAV_iota` hands, per class `c` and constructor `j` and per
fitting spine `xs' ++ fs`, the equation

```
(xs' ++ (es ++ [mk]).map (interp V σ')).foldl app (a c)
  = interp V (consList (ihs.map (interp V σ')) σ') Rb
```

at the chain frame `σ' = consList (xs' ++ fs) (chainFrame K a ρ)`, and
`RecRuleLaw` wants

```
interp V ρ (mkAppN L (xs ++ [mkAppN Ca ys]))
  = interp V ρ (mkAppN Ra (xs.take rP ++ ys.drop nP))
```

at the AMBIENT frame.  Four identifications bridge them, and each is a
statement about the rule DATA rather than about the recursion:

* the leaf — `interp V ρ L = a c` (`blockRecAV_facts`' second field at
  the stage's valuation spelling);
* the prefix — `xs'` is `xs.take rP` read at `ρ`;
* the INDEX PIN — `es` read at the chain frame is `xs.drop rP` read at
  `ρ` (`RecRuleLaw`'s `IotaIndexPin` is what pays for this);
* the constructor's residual — `mk` read at the chain frame is the
  fired spine `mkAppN Ca ys` read at `ρ`;
* the residue — the stored right-hand side's reading applied to
  `xs.take rP ++ ys.drop nP` is `Rb` at the ih values (β-reduction
  through the rule's λ-tower, then `interp_abstractIh`).

The conversion itself is then the spine arithmetic
`xs.map f = (xs.take rP).map f ++ (xs.drop rP).map f`, which is why it
is stated with NO mention of the chain frame, of `K` or of the tuple:
whatever `σ'` and `R` are, the four identifications are the whole
content. -/

/-- **The ι equation IS the rule's equality.** -/
theorem blockRecRuleEq_of_iota {ρ σ' : Nat → V} {R : V} {rP nP : Nat}
    {es ihs xs ys : List AnnotTerm} {mk L Ca Ra Rb : AnnotTerm}
    (hL : interp V ρ L = R)
    (hlaw : ((xs.take rP).map (interp V ρ) ++ (es ++ [mk]).map (interp V σ')).foldl
        SetTheory.app R
      = interp V (consList (ihs.map (interp V σ')) σ') Rb)
    (hes : es.map (interp V σ') = (xs.drop rP).map (interp V ρ))
    (hmk : interp V σ' mk = interp V ρ (AnnotTerm.mkAppN Ca ys))
    (hRa : interp V ρ (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop nP))
      = interp V (consList (ihs.map (interp V σ')) σ') Rb) :
    interp V ρ (AnnotTerm.mkAppN L (xs ++ [AnnotTerm.mkAppN Ca ys]))
      = interp V ρ (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop nP)) := by
  have hlist : (xs ++ [AnnotTerm.mkAppN Ca ys]).map (interp V ρ)
      = (xs.take rP).map (interp V ρ) ++ (es ++ [mk]).map (interp V σ') := by
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [hes, hmk, ← List.append_assoc, ← List.map_append, List.take_append_drop]
  rw [hRa, ← hlaw, interp_mkAppN_foldl, hL, hlist]


/-! ## 5. The family's ι law, in the form the last hop consumes

`blockRecAV_iota` hands the tuple existentially and the law at every
class and constructor at once.  The last hop uses it at ONE class and
ONE constructor, and it must name the tuple — the rule data's
identifications are stated at the chain frame the tuple builds.  So
the consumed form exposes the tuple through the LEAF EQUATIONS (which
pin it) rather than existentially, and fixes `c`/`j`. -/

/-- **One class's ι law at one constructor**, with the tuple exposed.
`leaf c'` is class `c'`'s leaf (the valuation's value at the stored
recursor); the law is the family's at the spine that fits the rule's
prefix and the constructor's fields. -/
def BlockIotaAt (V : Type w) [SetTheory V] (K c : Nat) (leaf : Nat → AnnotTerm)
    (pdoms fdoms es : List AnnotTerm) (mk : AnnotTerm) (ihs : List AnnotTerm)
    (Rb : AnnotTerm) (ρ : Nat → V) : Prop :=
  ∃ a : Nat → V,
    (∀ c', c' < K → interp V ρ (leaf c') = a c') ∧
    ∀ xs fs : List V, xs.length = pdoms.length →
      SpineFit (chainFrame K a ρ) (pdoms ++ fdoms) (xs ++ fs) →
      (xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) (chainFrame K a ρ)))).foldl
          SetTheory.app (a c)
        = interp V (consList (ihs.map (interp V (consList (xs ++ fs) (chainFrame K a ρ))))
            (consList (xs ++ fs) (chainFrame K a ρ))) Rb

/-- **The recursor model's seam**: `BlockRecPre` — `blockRecPre_graph`'s
conclusion — gives `BlockIotaAt` at every class and constructor of the
family. -/
theorem blockIotaAt_of_pre {s K c j : Nat} {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat}
    {pdoms : Nat → List AnnotTerm} {fdoms es : Nat → Nat → List AnnotTerm}
    {mk : Nat → Nat → AnnotTerm} {ihs : Nat → Nat → List AnnotTerm}
    {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}
    (h : BlockRecPre V s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb) ρ)
    (hc : c < K) (hj : j < nCt c) :
    BlockIotaAt V K c (blockRecAV s K RecTy (iotaEqsAV K nCt pdoms fdoms es mk ihs Rb))
      (pdoms c) (fdoms c j) (es c j) (mk c j) (ihs c j) (Rb c j) ρ := by
  obtain ⟨a, ha, hlaw⟩ := blockRecAV_iota h
  exact ⟨a, fun c' hc' => (ha c' hc').2.1, fun xs fs hxl hsp => hlaw c hc j hj xs fs hxl hsp⟩


/-! ## 6. The rule data's identifications, bundled

What is left of the last hop once the family's ι law is in hand is a
statement about the rule DATA at one fired spine, and it mentions
neither the recursion nor the check: the rule's prefix domains are as
long as the recursor's rule prefix, the prefix and field values fit
them at the chain frame, the constructor's index expressions read to
the application's index arguments (`IotaIndexPin`'s content), its
residual to the fired spine, and the stored right-hand side applied to
the residue at the `ih` values (the rule's λ-tower β-reduced, then
`interp_abstractIh`).

Both are `@[expose]` because the rule-data modules build them from the
run in another file. -/

/-- The rule's frame: the prefix values and the constructor's field
values, under the `K` chain binders. -/
@[expose] noncomputable def blockRuleFrame (K : Nat) (a ρ : Nat → V) (rP nP : Nat)
    (xs ys : List AnnotTerm) : Nat → V :=
  consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ))
    (chainFrame K a ρ)

/-- **The rule data's identifications at one fired spine.** -/
@[expose] def BlockRuleDataAt (V : Type w) [SetTheory V] (K : Nat) (a : Nat → V)
    (pdoms fdoms es : List AnnotTerm) (mk : AnnotTerm) (ihs : List AnnotTerm)
    (Rb : AnnotTerm) (ρ : Nat → V) (rP nP : Nat) (xs ys : List AnnotTerm)
    (Ca Ra : AnnotTerm) : Prop :=
  pdoms.length = rP ∧
  SpineFit (chainFrame K a ρ) (pdoms ++ fdoms)
      ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ∧
  es.map (interp V (blockRuleFrame K a ρ rP nP xs ys)) = (xs.drop rP).map (interp V ρ) ∧
  interp V (blockRuleFrame K a ρ rP nP xs ys) mk = interp V ρ (AnnotTerm.mkAppN Ca ys) ∧
  interp V ρ (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop nP))
    = interp V (consList (ihs.map (interp V (blockRuleFrame K a ρ rP nP xs ys)))
        (blockRuleFrame K a ρ rP nP xs ys)) Rb

/-- **The fired equality, from the ι law and the data.** -/
theorem blockRecRuleEq_of_data {K c : Nat} {leaf : Nat → AnnotTerm}
    {pdoms fdoms es ihs : List AnnotTerm} {mk Rb : AnnotTerm} {ρ : Nat → V}
    (hiota : BlockIotaAt V K c leaf pdoms fdoms es mk ihs Rb ρ) (hc : c < K)
    {rP nP : Nat} {xs ys : List AnnotTerm} {Ca Ra : AnnotTerm}
    (hxs : rP ≤ xs.length)
    (hdata : ∀ a : Nat → V, (∀ c', c' < K → interp V ρ (leaf c') = a c') →
      BlockRuleDataAt V K a pdoms fdoms es mk ihs Rb ρ rP nP xs ys Ca Ra) :
    interp V ρ (AnnotTerm.mkAppN (leaf c) (xs ++ [AnnotTerm.mkAppN Ca ys]))
      = interp V ρ (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop nP)) := by
  obtain ⟨a, ha, hlaw⟩ := hiota
  obtain ⟨hpl, hsp, hes, hmk, hRa⟩ := hdata a ha
  exact blockRecRuleEq_of_iota (R := a c) (ha c hc)
    (hlaw _ _ (by rw [List.length_map, List.length_take, hpl, Nat.min_eq_left hxs]) hsp)
    hes hmk hRa


/-! ## 7. `RecRuleLaw` for a new block recursor

The assembly.  Everything `RecRuleLaw` says about NAMES and LEVELS is
discharged here — the `.plain` firing makes both nested conjuncts
vacuous, the level instantiation is carried by the reading premise,
and the parameter comparison is unused (`sumRules` sets
`paramsBlind := true`).  What is passed through is the rule data
(`BlockRuleDataAt`) and the grading of the applied right-hand side;
what is consumed is the family's ι law (`BlockIotaAt`, i.e.
`BlockRecPre` through `blockIotaAt_of_pre`).

**The rule data is ONE arm of a disjunction**: at an
elimination level `ℓ = 0` the data's fit is REFUTABLE (`Exists`,
`BlockRuleFit.lean` §4), and the equation holds for a different
reason — both sides read as the point (the recursor's type is a truth
value, the rule's λ-tower carries the zero binder datum).  The second
arm says exactly that, and the ι law is then not consulted at all. -/

/-- **A new block recursor's rule law.** -/
theorem blockRecRuleLaw_of {env : Env} {m₃ : EnvModel V env} {φ : Name → Nat}
    {n : Name} {cv : ConstantVal} {mI rP : Nat} {rl : RecRule}
    {K c : Nat} {leafF : (Name → Nat) → Nat → AnnotTerm}
    {pdomsF fdomsF esF ihsF : (Name → Nat) → List AnnotTerm}
    {mkF RbF : (Name → Nat) → AnnotTerm}
    (hrPle : rP ≤ mI) (hc : c < K) (hplain : RecRule.fire rl = .plain)
    (hleaf : ∀ ψ : Name → Nat, m₃.acval n ψ = leafF ψ c)
    (hiota : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      BlockIotaAt V K c (leafF ψ) (pdomsF ψ) (fdomsF ψ) (esF ψ) (mkF ψ) (ihsF ψ) (RbF ψ) ρ)
    (hrhs : ∀ us : List Level, us.length = cv.levelParams.length →
      ∃ Ra : AnnotTerm,
        denoteMeta m₃.acval env φ 0
            ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us) = some Ra ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ Ra) ∧
        ∀ (cvj : ConstantVal) (cnP cnF : Nat),
          env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
        ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List AnnotTerm)
          (TVa TVja restR restC : AnnotTerm),
          xs.length = mI →
          ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
          usj.length = cvj.levelParams.length →
          Level.substFn φ cvj.levelParams usj
            = Level.substFn φ cvj.levelParams
                (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1 →
          IotaIndexPin (V := V) ρ restC (RecRule.ctorParams rl) mI rP xs →
          denoteMeta m₃.acval env φ 0
              (cv.type.instantiateLevelParams cv.levelParams us) = some TVa →
          denoteMeta m₃.acval env φ 0
              (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
          TeleFitPA V ρ TVa
            (xs ++ [AnnotTerm.mkAppN
              (m₃.acval (RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) ys]) restR →
          TeleFitPA V ρ TVja ys restC →
          ((∀ a : Nat → V,
            (∀ c', c' < K →
              interp V ρ (leafF (Level.substFn φ cv.levelParams us) c') = a c') →
            BlockRuleDataAt V K a
              (pdomsF (Level.substFn φ cv.levelParams us))
              (fdomsF (Level.substFn φ cv.levelParams us))
              (esF (Level.substFn φ cv.levelParams us))
              (mkF (Level.substFn φ cv.levelParams us))
              (ihsF (Level.substFn φ cv.levelParams us))
              (RbF (Level.substFn φ cv.levelParams us))
              ρ rP (RecRule.ctorParams rl) xs ys
              (m₃.acval (RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) Ra) ∨
            -- the `ℓ = 0` arm: both sides of the fired equation are the point
            (interp V ρ (AnnotTerm.mkAppN (leafF (Level.substFn φ cv.levelParams us) c)
                (xs ++ [AnnotTerm.mkAppN (m₃.acval (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys])) = pt ∧
              interp V ρ (AnnotTerm.mkAppN Ra (xs.take rP ++ ys.drop (RecRule.ctorParams rl)))
                = pt)) ∧
          ((∀ a ∈ xs, WellDenotedV V ρ a) → (∀ b ∈ ys, WellDenotedV V ρ b) →
            WellDenotedV V ρ (AnnotTerm.mkAppN Ra
              (xs.take rP ++ ys.drop (RecRule.ctorParams rl))))) :
    RecRuleLaw m₃ φ n cv mI rP rl := by
  refine ⟨hrPle, fun us hus => ?_⟩
  obtain ⟨Ra, hRa, hokRa, hspine⟩ := hrhs us hus
  refine ⟨Ra, hRa, hokRa, fun lvls pins hn => ?_, ?_⟩
  · rw [hplain] at hn; exact nomatch hn
  · intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl hujl hψ
      _ _ hidx hTVa hTVja hfitR hfitC
    obtain ⟨hdata, hok⟩ := hspine cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC
      hxl hyl hujl hψ hidx hTVa hTVja hfitR hfitC
    refine ⟨?_, hok⟩
    rw [hleaf]
    rcases hdata with hdata | ⟨hL, hR⟩
    · exact blockRecRuleEq_of_data (hiota _ ρ) hc (by rw [hxl]; exact hrPle) hdata
    · exact hL.trans hR.symm


/-! ## 8. `hrecP`, as `blockRecStaged_of` consumes it

The composition.  Two things are discharged on the way, and both are
about `sumRules`' construction rather than about the model:

* a stored rule's POSITION — `sumRules_getElem?` names the constructor
  and the right-hand side the rule was built from, so the premise is
  stated per `(recursor, constructor)` pair rather than per anonymous
  rule;
* the rule's FIRING — a block rule fires `.plain` or `.inert`
  according to ONE syntactic test on the recursor's type
  (`Expr.recRulePlain`), and `RecRules` asks nothing of an `.inert`
  rule, so the `.plain` hypothesis `blockRecRuleLaw_of` needs is free:
  it is `hfire` with the `if` resolved. -/

/-- **`hrecP`**, in the exact shape `blockRecStaged_of` consumes. -/
theorem hrecP_of {q : BlockShape} {nP : Nat} {rs : List RecDatum}
    {envC : Env} {acv : Name → (Name → Nat) → AnnotTerm} (mpC : EnvModelM V μ envC)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hpsh : ∀ r ∈ rs, r.1.name.isProjFnShape = false)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
    (hnew : ∀ m₃ : EnvModel V (consBlockRecs envC.find? q nP 0 rs envC), m₃.acval = acv →
      ∀ (φ : Name → Nat) (j : Nat) (r : RecDatum), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        Expr.recRulePlain r.1.type (q.majorIdxAt j) (q.rulePrefixAt j) nP = true →
        RecRuleLaw m₃ φ r.1.name r.1 (q.majorIdxAt j) (q.rulePrefixAt j)
          (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := nP,
              fire := .plain, rhs := rhs, paramsBlind := true })) :
    ∀ m₃ : EnvModel V (consBlockRecs envC.find? q nP 0 rs envC),
      m₃.acval = acv → ∀ φ : Name → Nat, RecRules m₃ φ := by
  intro m₃ hac φ
  refine recRules_consBlockRecs_of mpC hfr hpsh hag m₃ hac φ ?_
  intro j r hr rl hrl hfire
  obtain ⟨i, cA, rhs, hcA, hrhs, rfl⟩ := ConLeche.sumRules_getElem? hrl
  have hpl : Expr.recRulePlain r.1.type (q.majorIdxAt j) (q.rulePrefixAt j) nP = true := by
    cases hh : Expr.recRulePlain r.1.type (q.majorIdxAt j) (q.rulePrefixAt j) nP with
    | true => rfl
    | false =>
      rw [ConLeche.recRuleBits_fire, hh] at hfire
      simp at hfire
  rw [hpl]
  simp only [if_true]
  exact hnew m₃ hac φ j r hr i cA rhs hcA hrhs hpl


/-! ## 9. The residue conjunct: the abstraction's reading

`BlockRuleDataAt`'s last conjunct is where the RIGHT-HAND SIDE meets
the residue, and its content is this: the stored body read at the
rule's frame IS the residue read at the frame extended by the `ih`
openers' values.  `interp_abstractIh`
(`Model/Inductives/BlockRecRule.lean`) proves that by structural
induction over the body with one premise, `IhNodeVal`, and
`ihNodeVal_of_spine` reduces that premise to `IhSpineFold` — a
statement about the GENERATED guarded call alone.  Stated here at the
rule's own depth (`d = 0`, no local binders) it is the equation the
conjunct needs, modulo the β-reduction of the rule's λ-tower and the
chain-frame lifting, both of which are the rule data's. -/

end ConLeche.Model
