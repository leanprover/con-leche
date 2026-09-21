module

public import ConLeche.Model.Inductives.BlockStageRec
import ConLeche.Model.Inductives.BlockRecMem
public import ConLeche.Model.RecRulesCons
public import ConLeche.Semantics.Tower.BlockRecI

public section

/-!
# The LAST HOP: every stored rule's `RecRuleLaw` (task #315, M5, model half)

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
  values is identified with the stored body's — O-1,
  `interp_abstractIh` (`Model/Inductives/BlockRecRule.lean`).

The rule data (`pdoms`/`fdoms`/`es`/`mk`/`ihs`/`Rb`) is NOT re-derived
here: it is named, in the spelling the family premise `BlockRecPre`
(lane RM3's `blockRecPre_of`) is stated at, and the run's own
identification of it is that lane's.  What this module owns is the
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

end ConLeche.Model
