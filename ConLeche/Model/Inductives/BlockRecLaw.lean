module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockStageRec
public import ConLeche.Model.Inductives.BlockRecMem
public import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.FixKit
import ConLeche.Model.Rules.DefEqSoundKit

public section

/-!
# The LAST HOP: every stored rule's `RecRuleLaw`

`blockRecStaged_of` (`Model/Inductives/BlockStageRec.lean`) owes one
premise about the ι content of the recursors' cons:

```
hrecP : ∀ m₃ : EnvModel V (consBlockRecs q nP 0 rs envC),
  m₃.acval = acv → ∀ φ : Name → Nat, RecRules m₃ φ
```

`RecRules` is keyed on EVERY stored recursor of the consed
environment, so it splits — by `find?_consBlockRecsR_inv` — into two
disjoint halves:

* **the PRE-EXISTING recursors**, whose laws are `mpC.rec_rules`
  transported across the cons.  That is this module's §1
  (`recRuleLaw_consBlockRecsR_prefix`), the `consBlockRecsR` twin of
  `recRuleLaw_cons_prefix` (`Model/RecRulesCons.lean`): the crossing
  is `denote_consBlockRecsR_mono` in place of `denote_cons_mono`
  and the valuation's agreement off the new names (`hag`) in place of
  `acvalWith_ne`.  No premise beyond `blockRecStaged_of`'s own;
* **the `k` NEW recursors**, whose rules are `sumRules`' — the last
  hop proper (§2–§4): `blockRecAV_iota`'s extracted ι equation is
  `RecRuleLaw`'s equality once (a) the two `TeleFitPA` fits are
  flipped to the `SpineFit`s the ι law is stated at, (b) the stored
  right-hand side's reading is exhibited as the residue's λ-tower and
  its application β-reduced, and (c) the residue's reading at the ih
  values is identified with the stored body's (the rule data's last
  conjunct).

The rule data (`pdoms`/`fdoms`/`es`/`mk`/`ihs`/`Rb`) is NOT re-derived
here: it is named, in the spelling the family premise `BlockRecPre`
(`Semantics/Tower/BlockRecTower.lean`) is stated at, and the run's own identification of
it lives with the rule data.  What this module owns is the
CONVERSION — from the semantic ι law to the syntactic contract — and
the two `TeleFitPA → SpineFit` flips it needs.
-/

namespace ConLeche.Model
open ConLeche.Term (Term)


open ConLeche.Semantics SetTheory
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo RecRule BlockShape
  consBlockRecs consBlockRecsR)
open ConLeche.Verify

universe w

variable {V : Type w} [SetTheory V]

/-! ## 1. The PRE-EXISTING recursors' laws, across the cons

`recRuleLaw_cons_prefix`'s argument, at `consBlockRecs` rather than at
one fresh cons.  Every piece of `RecRuleLaw` that mentions the
environment is either a LOOKUP (preserved, `find?_consBlockRecsR_keep`),
a READING of a subject bound by the constructors' environment (moved
forward by `denote_consBlockRecsR_mono`, then identified with the
one in hand because `denote` is a function), or one of the TWO
LEAVES the law names — the recursor's and its rule's constructor's,
both stored in `envC`, hence not among the `k` new names, hence
`hag`'s.

The `k` conses are crossed in ONE step rather than iterated: the
iterated form would need an `EnvModelM` at each intermediate
environment, and the statement `hrecP` is posed at is about an
arbitrary `EnvModel` of the final one. -/

/-- **(S)'s `iotaCtorNeverProp` guard, across the `k` recursors' cons**:
mirrors `iotaCtorNeverProp_cons_of_isSome` (`Model/RecRulesCons.lean`) —
it reads `find?` only at the constructor's result family, and that
name is stored below the new recursors (not one of the `k` fresh
names) whenever the constructor's type resolves. -/
theorem iotaCtorNeverProp_consBlockRecsR_of_isSome {R : Nat → RecDatum → Bool × List RecRule}
    {q : BlockShape} {rs : List RecDatum} {envC : Env}
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    {cvj : ConstantVal} {usj : List Level}
    (hT : ∀ T us, cvj.type.piResult.getAppFn = .const T us →
      (envC.find? T).isSome = true) :
    ConLeche.iotaCtorNeverProp (consBlockRecsR R q 0 rs envC).find? cvj usj
      = ConLeche.iotaCtorNeverProp envC.find? cvj usj := by
  unfold ConLeche.iotaCtorNeverProp
  match hh : cvj.type.piResult.getAppFn with
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ => rfl
  | .const T us =>
    dsimp only
    have hiso := hT T us hh
    obtain ⟨ciT, hciT⟩ : ∃ ciT, envC.find? T = some ciT := by
      cases hfind : envC.find? T with
      | none => rw [hfind] at hiso; exact absurd hiso (by decide)
      | some ciT => exact ⟨ciT, rfl⟩
    rw [find?_consBlockRecsR_keep hfr T ciT hciT, hciT]

/-- **`RecRuleExtra` survives the recursors' cons** —
`recRuleLaw_consBlockRecsR_prefix`'s sibling for the `RecRuleExtra`
conjunct, `recRuleExtra_cons_prefix`'s (`Model/RecRulesCons.lean`) twin
at `consBlockRecsR`: the crossing is `hmono` in place of
`denote_cons_mono` and the valuation's agreement off the new names
(`hacvAt`) in place of `acvalWith_ne`.  Clause (S)'s `iotaCtorNeverProp`
guard agrees with the constructors' environment's for the same reason
as there (`iotaCtorNeverProp_consBlockRecsR_of_isSome`). -/
theorem recRuleExtra_consBlockRecsR_prefix {R : Nat → RecDatum → Bool × List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {acv : Name → (Name → Nat) → Term} (mpC : EnvModelM V envC)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
    (m₃ : EnvModel V (consBlockRecsR R q 0 rs envC))
    (hac : m₃.acval = acv) (φ : Name → Nat)
    {n : Name} {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (hfE : envC.find? n = some (.recInfo cv mI rP isK rules))
    {rl : RecRule} (hmem : rl ∈ rules) :
    RecRuleExtra m₃ φ n cv mI rP isK rl := by
  have hacvAt : ∀ x : Name, (envC.find? x).isSome = true →
      m₃.acval x = mpC.base2.acval x := by
    intro x hx
    rw [hac]
    refine hag x fun r hr hh => ?_
    rw [hh, hfr r hr] at hx
    exact nomatch hx
  have hmono : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr), ConstsBound envC e →
      ∀ {ea : Term}, denote mpC.base2.acval envC ψ d e = some ea →
        denote m₃.acval (consBlockRecsR R q 0 rs envC) ψ d e = some ea := by
    intro ψ d e hcb ea h
    rw [hac]
    exact denote_consBlockRecsR_mono hfr hag ψ d e hcb h
  obtain ⟨-, hlaw0, hextra⟩ := mpC.rec_rules φ n cv mI rP isK rules hfE rl hmem
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    mpC.base2.wf.consts _ (ConLeche.Env.find?_mem hfE)
  obtain ⟨-, -, hRres, -, hnest⟩ := hrec' cv mI rP isK rules rfl rl hmem
  intro us hlen TVa hTVa
  obtain ⟨TVa', hTVa', -, -⟩ := mpC.constType 0 n _ us hfE (by exact hlen)
  obtain rfl : TVa' = TVa :=
    Option.some.inj ((hmono _ 0 _ (constsBound_instType mpC.base2.wf
      (ConLeche.Env.find?_mem hfE) us) hTVa').symm.trans hTVa)
  have hpinCB : ∀ lvls pins, RecRule.fire rl = .nested lvls pins → ∀ i : Nat,
      ConstsBound envC (openRev 0 rP
        ((pins.getD i default).instantiateLevelParams cv.levelParams us)) := by
    intro lvls pins hfr' i
    obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hfr'
    refine constsBound_openRev (constsBound_of_constsResolve _ ?_) 0 rP
    rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
    by_cases hilt : i < pins.length
    · exact (hpinsWf _ (ConLeche.getD_mem hilt)).2.2.1
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  obtain ⟨hK, hCtor⟩ := hextra us hlen TVa' hTVa'
  refine ⟨?_, ?_⟩
  · intro hk
    obtain ⟨hnf, hRalaw⟩ := hK hk
    refine ⟨hnf, fun Ra hRa ρ xs a restR hxl hfit => ?_⟩
    obtain ⟨Ra', hRa0', -, -, -⟩ := hlaw0 us hlen
    obtain rfl : Ra' = Ra :=
      Option.some.inj ((hmono _ 0 _ (constsBound_of_constsResolve _ (by
        rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
        exact hRres)) hRa0').symm.trans hRa)
    have hacvR : m₃.acval n = mpC.base2.acval n := hacvAt n (by rw [hfE]; rfl)
    rw [hacvR]
    exact hRalaw Ra' hRa0' ρ xs a restR hxl hfit
  · intro cvj cnP cnF hfcj
    have hfcjE : envC.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) := by
      obtain ⟨cvj', cnP', cnF', h0⟩ :=
        mpC.base2.rec_ctors n cv mI rP isK rules hfE rl hmem
      have heq := Option.some.inj
        ((find?_consBlockRecsR_keep (R := R) (q := q) hfr _ _ h0).symm.trans hfcj)
      rw [← heq]
      exact h0
    have hacvC : m₃.acval (RecRule.ctor rl) = mpC.base2.acval (RecRule.ctor rl) :=
      hacvAt _ (by rw [hfcjE]; rfl)
    obtain ⟨harity, hnk⟩ := hCtor cvj cnP cnF hfcjE
    refine ⟨harity, ?_⟩
    intro hk
    -- a constructor type's reading at the cons is the prefix's
    have hTVjaOf : ∀ usj : List Level, usj.length = cvj.levelParams.length →
        ∀ TVja : Term, denote m₃.acval (consBlockRecsR R q 0 rs envC) φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
        denote mpC.base2.acval envC φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja := by
      intro usj husj TVja hTVja
      obtain ⟨TVja', hTVja', -, -⟩ :=
        mpC.constType 0 (RecRule.ctor rl) _ usj hfcjE (by exact husj)
      obtain rfl : TVja' = TVja :=
        Option.some.inj ((hmono _ 0 _ (constsBound_instType mpC.base2.wf
          (ConLeche.Env.find?_mem hfcjE) usj) hTVja').symm.trans hTVja)
      exact hTVja'
    -- (S)/(T)'s `iotaCtorNeverProp` guard is the prefix's
    have hlicE : ∀ lvs : List Level,
        ConLeche.iotaCtorNeverProp (consBlockRecsR R q 0 rs envC).find? cvj lvs
          = ConLeche.iotaCtorNeverProp envC.find? cvj lvs := by
      intro lvs
      obtain ⟨-, -, hresolve, -, -, -, -⟩ :=
        mpC.base2.wf.consts _ (ConLeche.Env.find?_mem hfcjE)
      dsimp only [ConLeche.ConstantInfo.toConstantVal] at hresolve
      have hTiso : ∀ T us', cvj.type.piResult.getAppFn = .const T us' →
          (envC.find? T).isSome = true :=
        fun T us' heq' =>
          ConLeche.Expr.find?_isSome_of_piResult_getAppFn_const hresolve heq'
      exact iotaCtorNeverProp_consBlockRecsR_of_isSome hfr hTiso
    obtain ⟨hS, hT, hPU⟩ := hnk hk
    refine ⟨fun hlic => hS (by rwa [hlicE] at hlic), ?_, ?_⟩
    · intro hlic usj husj TVja hTVja ρ xs ys restR restC hxl hyl hfitR hfitC hxwd hywd hne
      rw [hlicE] at hlic
      have hTVja0 := hTVjaOf usj husj TVja hTVja
      rw [hacvC] at hfitR hne
      obtain ⟨usj', ys', TVja', restC', h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        hT hlic usj husj TVja hTVja0 ρ xs ys restR restC hxl hyl
          hfitR hfitC hxwd hywd hne
      refine ⟨usj', ys', TVja', restC', h1, h2,
        hmono _ 0 _ (constsBound_instType mpC.base2.wf
          (ConLeche.Env.find?_mem hfcjE) usj') h3, h4, h5, h6, h7, ?_⟩
      rw [hacvC]
      exact h8
    intro usj husj heq TVja hTVja
    have hTVja' := hTVjaOf usj husj TVja hTVja
    obtain ⟨hP, hU⟩ := hPU usj husj heq TVja hTVja'
    refine ⟨?_, ?_⟩
    · intro ρ xs a restR hxl hfit hapt ys restC hfitC
      rw [hacvC]
      exact hP ρ xs a restR hxl hfit hapt ys restC hfitC
    · intro ρ xs ys restR restC hxl hyl hfitR hfitC hxwd hywd hplain0 hnested0 hpin0
      have hnested' : ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
          interp V ρ (Term.mkAppN
            (mpC.base2.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          ∀ i, i < cnP →
          ∀ vpa : Term,
            denote mpC.base2.acval envC φ rP
              (openRev 0 rP ((pins.getD i default).instantiateLevelParams
                cv.levelParams us)) = some vpa →
            interp V ρ (ys.getD i default) ≠ pt →
            interp V ρ (Term.instRevChain (xs.take rP) vpa) ≠ pt →
            interp V ρ (ys.getD i default)
              = interp V ρ (Term.instRevChain (xs.take rP) vpa) := by
        intro lvls pins hfr' hpt i hi vpa hvpa hney hnex
        exact hnested0 lvls pins hfr' (by rw [hacvC]; exact hpt) i hi vpa
          (hmono _ rP _ (hpinCB lvls pins hfr' i) hvpa) hney hnex
      rw [hacvC] at hfitR hplain0 hpin0 ⊢
      exact hU ρ xs ys restR restC hxl hyl hfitR hfitC hxwd hywd hplain0 hnested' hpin0

/-- **A stored recursor's law crosses the recursors' cons.** -/
theorem recRuleLaw_consBlockRecsR_prefix {R : Nat → RecDatum → Bool × List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {acv : Name → (Name → Nat) → Term} (mpC : EnvModelM V envC)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
    (m₃ : EnvModel V (consBlockRecsR R q 0 rs envC))
    (hac : m₃.acval = acv) (φ : Name → Nat)
    {n : Name} {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (hfE : envC.find? n = some (.recInfo cv mI rP isK rules))
    {rl : RecRule} (hmem : rl ∈ rules) :
    RecRuleLaw m₃ φ n cv mI rP isK rl := by
  -- the valuation at a STORED name is the constructors' environment's
  have hacvAt : ∀ x : Name, (envC.find? x).isSome = true →
      m₃.acval x = mpC.base2.acval x := by
    intro x hx
    rw [hac]
    refine hag x fun r hr hh => ?_
    rw [hh, hfr r hr] at hx
    exact nomatch hx
  have hmono : ∀ (ψ : Name → Nat) (d : Nat) (e : Expr), ConstsBound envC e →
      ∀ {ea : Term}, denote mpC.base2.acval envC ψ d e = some ea →
        denote m₃.acval (consBlockRecsR R q 0 rs envC) ψ d e = some ea := by
    intro ψ d e hcb ea h
    rw [hac]
    exact denote_consBlockRecsR_mono hfr hag ψ d e hcb h
  obtain ⟨hrPle, hlaw0, hextra⟩ := mpC.rec_rules φ n cv mI rP isK rules hfE rl hmem
  refine ⟨hrPle, fun us hlen => ?_,
    recRuleExtra_consBlockRecsR_prefix mpC hfr hag m₃ hac φ hfE hmem⟩
  obtain ⟨Ra, hRa0, hokRa, hpinsOk, hlaw⟩ := hlaw0 us hlen
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    mpC.base2.wf.consts _ (ConLeche.Env.find?_mem hfE)
  obtain ⟨-, -, hRres, -, hnest⟩ := hrec' cv mI rP isK rules rfl rl hmem
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
    obtain ⟨TVa', hTVa', -, -⟩ := mpC.constType 0 n _ us hfE (by exact hlen)
    obtain rfl : TVa' = TVa :=
      Option.some.inj ((hmono _ 0 _ (constsBound_instType mpC.base2.wf
        (ConLeche.Env.find?_mem hfE) us) hTVa').symm.trans hTVa)
    exact hok ρ zs TVa' restR hzl hzok hTVa' hfit
  · intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl hujl
      hψ hyWD hpin hTVa hTVja hfitR hfitC
    -- the rule's constructor is stored in the constructors' environment
    have hfcjE : envC.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) := by
      obtain ⟨cvj', cnP', cnF', h0⟩ :=
        mpC.base2.rec_ctors n cv mI rP isK rules hfE rl hmem
      have heq := Option.some.inj
        ((find?_consBlockRecsR_keep (R := R) (q := q) hfr _ _ h0).symm.trans hfcj)
      rw [← heq]
      exact h0
    -- the two leaves the law names are the prefix's
    have hacvR : m₃.acval n = mpC.base2.acval n := hacvAt n (by rw [hfE]; rfl)
    have hacvC : m₃.acval (RecRule.ctor rl) = mpC.base2.acval (RecRule.ctor rl) :=
      hacvAt _ (by rw [hfcjE]; rfl)
    -- the two stored types: produced at the prefix, moved forward,
    -- identified with the readings in hand by determinism
    obtain ⟨TVa', hTVa', -, -⟩ := mpC.constType 0 n _ us hfE (by exact hlen)
    obtain rfl : TVa' = TVa :=
      Option.some.inj ((hmono _ 0 _ (constsBound_instType mpC.base2.wf
        (ConLeche.Env.find?_mem hfE) us) hTVa').symm.trans hTVa)
    obtain ⟨TVja', hTVja', -, -⟩ :=
      mpC.constType 0 (RecRule.ctor rl) _ usj hfcjE (by exact hujl)
    obtain rfl : TVja' = TVja :=
      Option.some.inj ((hmono _ 0 _ (constsBound_instType mpC.base2.wf
        (ConLeche.Env.find?_mem hfcjE) usj) hTVja').symm.trans hTVja)
    rw [hacvC] at hfitR hpin
    rw [hacvR, hacvC]
    exact hlaw cvj cnP cnF hfcjE usj ρ xs ys _ _ restR restC hxl hyl
      hujl hψ hyWD hpin hTVa' hTVja' hfitR hfitC

/-! ## 2. The split: `RecRules` at the recursors' environment

`find?_consBlockRecsR_inv` (`Model/Inductives/BlockStageRec.lean`) is
the only inversion of the cons needed here: a recursor stored at the
consed environment is either one of the constructors' environment's —
§1 — or the `j`-th of the block, with `sumRules`' rules and the shape
`q` dictates.  So `hrecP` is §1 plus ONE premise, per NEW recursor and
per rule. -/

/-- **`hrecP`, split.**  The pre-existing recursors' rows are §1; the
`k` new ones' are the premise `hnew`, stated at the rule list the cons
actually stores. -/
theorem recRules_consBlockRecsR_of {R : Nat → RecDatum → Bool × List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {acv : Name → (Name → Nat) → Term} (mpC : EnvModelM V envC)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
    (m₃ : EnvModel V (consBlockRecsR R q 0 rs envC))
    (hac : m₃.acval = acv) (φ : Name → Nat)
    (hnew : ∀ (j : Nat) (r : RecDatum), rs[j]? = some r →
      ∀ rl ∈ (R j r).2,
        RecRuleLaw m₃ φ r.1.name r.1 (q.majorIdxAt j) (q.rulePrefixAt j) (R j r).1 rl) :
    RecRules m₃ φ := by
  intro n cv mI rP isK rules hf rl hmem
  rcases find?_consBlockRecsR_inv hf with hE | ⟨j, r, hr, rfl, hci⟩
  · exact recRuleLaw_consBlockRecsR_prefix mpC hfr hag m₃ hac φ hE hmem
  · rw [Nat.zero_add] at hci
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ :
        cv = r.1 ∧ mI = q.majorIdxAt j ∧ rP = q.rulePrefixAt j ∧ isK = (R j r).1 ∧
          rules = (R j r).2 := by
      injection hci with h1 h2 h3 h5 h4
      exact ⟨h1, h2, h3, h5, h4⟩
    exact hnew j r hr rl hmem


/-! ## 3. The `TeleFitPA → SpineFit` flip

`RecRuleLaw` states its two fits as `TeleFitPA`s of the stored types'
READINGS; the family's ι law (`blockRecAV_iota`) is stated at
`SpineFit`s of the domains.  The flip is the generic kit at
`k = 1` — `teleFitPA_to_chain` through a `PiTeleAV` of the tower, then
`spineFit_of_chain` — and its ENTRY CONDITION is that the fitted
reading BE a `mkPisAV` tower, which for a block recursor is
`recStage_tyPis`' third conjunct (`Model/Inductives/BlockRecMem.lean`:
the stream's type is stored as is, so its reading is identified by the
run's own Π-peel). -/

/-- **A fit of a Π-tower reading is a `SpineFit` of its domains.** -/
theorem spineFit_of_teleFitPA {pds : List Term} {b : Term}
    {ρ : Nat → V} {ws : List Term} {rest : Term}
    (hlen : ws.length = pds.length)
    (hfit : TeleFitPA V ρ (mkPisAV pds b) ws rest) :
    SpineFit ρ (pds) (ws.map (interp V ρ)) := by
  have htele := piTeleAV_of_stripPisAV (stripPisAV_mkPisAV pds b)
  refine spineFit_of_chain (by simpa using hlen) ?_
  intro n hn
  have := teleFitPA_to_chain pds.length htele hlen hfit n (by simpa using hn)
  simpa using this

/-- **The block recursor's own flip**, at the run: whatever fits the
`i`-th stored recursor type's reading fits its domains. -/
theorem spineFit_blockRecTy {envC : Env}
    (mpC : EnvModelM V envC) {p : ConLeche.BlockParts}
    {cvTas : List ConstantVal}
    {rs : List RecDatum} {F : Nat}
    (h : ConLeche.RecStageG .verified F envC p cvTas rs)
    {i : Nat} {r : RecDatum} (hr : rs[i]? = some r) (ψ : Name → Nat)
    {ρ : Nat → V} {ws : List Term} {rest TVa : Term}
    (hTVa : denote mpC.base2.acval envC ψ 0 r.1.type = some TVa)
    (hlen : ws.length = p.toBlockShape.majorIdxAt i + 1)
    (hfit : TeleFitPA V ρ TVa ws rest) :
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ i))
      (ws.map (interp V ρ)) := by
  obtain ⟨-, -, -, hread, hpis, hrdsLen, -, -⟩ := recStage_tyPis mpC h hr ψ
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
  through the rule's λ-tower).

The conversion itself is then the spine arithmetic
`xs.map f = (xs.take rP).map f ++ (xs.drop rP).map f`, which is why it
is stated with NO mention of the chain frame, of `K` or of the tuple:
whatever `σ'` and `R` are, the four identifications are the whole
content. -/

/-- **The ι equation IS the rule's equality.** -/
theorem blockRecRuleEq_of_iota {ρ σ' : Nat → V} {R : V} {rP nP : Nat}
    {es ihs xs ys : List Term} {mk L Ca Ra Rb : Term}
    (hL : interp V ρ L = R)
    (hlaw : ((xs.take rP).map (interp V ρ) ++ (es ++ [mk]).map (interp V σ')).foldl
        SetTheory.app R
      = interp V (consList (ihs.map (interp V σ')) σ') Rb)
    (hes : es.map (interp V σ') = (xs.drop rP).map (interp V ρ))
    (hmk : interp V σ' mk = interp V ρ (Term.mkAppN Ca ys))
    (hRa : interp V ρ (Term.mkAppN Ra (xs.take rP ++ ys.drop nP))
      = interp V (consList (ihs.map (interp V σ')) σ') Rb) :
    interp V ρ (Term.mkAppN L (xs ++ [Term.mkAppN Ca ys]))
      = interp V ρ (Term.mkAppN Ra (xs.take rP ++ ys.drop nP)) := by
  have hlist : (xs ++ [Term.mkAppN Ca ys]).map (interp V ρ)
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
def BlockIotaAt (V : Type w) [SetTheory V] (K c : Nat) (leaf : Nat → Term)
    (pdoms fdoms es : List Term) (mk : Term) (ihs : List Term)
    (Rb : Term) (ρ : Nat → V) : Prop :=
  ∃ a : Nat → V,
    (∀ c', c' < K → interp V ρ (leaf c') = a c') ∧
    ∀ xs fs : List V, xs.length = pdoms.length →
      SpineFit (chainFrame K a ρ) (pdoms ++ fdoms) (xs ++ fs) →
      (xs ++ (es ++ [mk]).map (interp V (consList (xs ++ fs) (chainFrame K a ρ)))).foldl
          SetTheory.app (a c)
        = interp V (consList (ihs.map (interp V (consList (xs ++ fs) (chainFrame K a ρ))))
            (consList (xs ++ fs) (chainFrame K a ρ))) Rb

/-- **The recursor model's seam**: `BlockRecPre` — `graphRecPre_core`'s
conclusion — gives `BlockIotaAt` at every class and constructor of the
family. -/
theorem blockIotaAt_of_pre {s K c j : Nat} {RecTy : Nat → Term} {nCt : Nat → Nat}
    {pdoms : Nat → List Term} {fdoms es : Nat → Nat → List Term}
    {mk : Nat → Nat → Term} {ihs : Nat → Nat → List Term}
    {Rb : Nat → Nat → Term} {ρ : Nat → V}
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
the residue at the `ih` values (the rule's λ-tower β-reduced).

Both are `@[expose]` because the rule-data modules build them from the
run in another file. -/

/-- The rule's frame: the prefix values and the constructor's field
values, under the `K` chain binders. -/
@[expose] noncomputable def blockRuleFrame (K : Nat) (a ρ : Nat → V) (rP nP : Nat)
    (xs ys : List Term) : Nat → V :=
  consList ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ))
    (chainFrame K a ρ)

/-- **The rule data's identifications at one fired spine.** -/
@[expose] def BlockRuleDataAt (V : Type w) [SetTheory V] (K : Nat) (a : Nat → V)
    (pdoms fdoms es : List Term) (mk : Term) (ihs : List Term)
    (Rb : Term) (ρ : Nat → V) (rP nP : Nat) (xs ys : List Term)
    (Ca Ra : Term) : Prop :=
  pdoms.length = rP ∧
  SpineFit (chainFrame K a ρ) (pdoms ++ fdoms)
      ((xs.take rP).map (interp V ρ) ++ (ys.drop nP).map (interp V ρ)) ∧
  es.map (interp V (blockRuleFrame K a ρ rP nP xs ys)) = (xs.drop rP).map (interp V ρ) ∧
  interp V (blockRuleFrame K a ρ rP nP xs ys) mk = interp V ρ (Term.mkAppN Ca ys) ∧
  interp V ρ (Term.mkAppN Ra (xs.take rP ++ ys.drop nP))
    = interp V (consList (ihs.map (interp V (blockRuleFrame K a ρ rP nP xs ys)))
        (blockRuleFrame K a ρ rP nP xs ys)) Rb

/-- **The fired equality, from the ι law and the data.** -/
theorem blockRecRuleEq_of_data {K c : Nat} {leaf : Nat → Term}
    {pdoms fdoms es ihs : List Term} {mk Rb : Term} {ρ : Nat → V}
    (hiota : BlockIotaAt V K c leaf pdoms fdoms es mk ihs Rb ρ) (hc : c < K)
    {rP nP : Nat} {xs ys : List Term} {Ca Ra : Term}
    (hxs : rP ≤ xs.length)
    (hdata : ∀ a : Nat → V, (∀ c', c' < K → interp V ρ (leaf c') = a c') →
      BlockRuleDataAt V K a pdoms fdoms es mk ihs Rb ρ rP nP xs ys Ca Ra) :
    interp V ρ (Term.mkAppN (leaf c) (xs ++ [Term.mkAppN Ca ys]))
      = interp V ρ (Term.mkAppN Ra (xs.take rP ++ ys.drop nP)) := by
  obtain ⟨a, ha, hlaw⟩ := hiota
  obtain ⟨hpl, hsp, hes, hmk, hRa⟩ := hdata a ha
  exact blockRecRuleEq_of_iota (R := a c) (ha c hc)
    (hlaw _ _ (by rw [List.length_map, List.length_take, hpl, Nat.min_eq_left hxs]) hsp)
    hes hmk hRa


/-! ## 7. `RecRuleLaw` for a new block recursor

The assembly.  Everything `RecRuleLaw` says about NAMES and LEVELS is
discharged here — the `.plain` firing makes both nested conjuncts
vacuous, and the level instantiation is carried by the reading
premise.  What is passed through is the rule data
(`BlockRuleDataAt`) and the grading of the applied right-hand side;
what is consumed is the family's ι law (`BlockIotaAt`, i.e.
`BlockRecPre` through `blockIotaAt_of_pre`).

**The rule data is ONE arm of a disjunction**: at an
elimination level `ℓ = 0` the data's fit is REFUTABLE (`Exists`,
`BlockRuleFit.lean` §4), and the equation holds for a different
reason — both sides read as the point (the recursor's type is a truth
value).  The second
arm says exactly that, and the ι law is then not consulted at all. -/

/-- **`RecRuleLaw`'s outer `.nested` conjunct, named**: the pins' open
readings at the rule prefix and their
context-guarded grading — vacuous at a rule that does not fire
`.nested`. -/
@[expose] def RecRulePinsOk {env : Env} (m₃ : EnvModel V env) (φ : Name → Nat)
    (cv : ConstantVal) (rP : Nat) (rl : RecRule) : Prop :=
  ∀ us : List Level, us.length = cv.levelParams.length →
    ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
      ∀ i, i < pins.length →
      ∃ vpa : Term,
        denote m₃.acval env φ rP
          (openRev 0 rP ((pins.getD i default).instantiateLevelParams
            cv.levelParams us)) = some vpa ∧
        ∀ (ρ : Nat → V) (zs : List Term) (TVa restR : Term),
          zs.length = rP →
          (∀ z ∈ zs, WellDenoted V ρ z) →
          denote m₃.acval env φ 0
            (cv.type.instantiateLevelParams cv.levelParams us) = some TVa →
          TeleFitPA V ρ TVa zs restR →
          WellDenoted V ρ (Term.instRevChain zs vpa)

/-! ### 7a. `RecRuleLaw`'s ι facts (task #342 L10)

`RecRuleExtra` splits in two.  Its K clause (the law at ANY major) is
derived from the main law at a FIRED spine — the K witness
(`RecRuleKWit`): at a K rule every major value in the major's domain is
the value of the fieldless constructor applied to parameters the ι
step would accept (inversion of the family's least fixed point,
discharged at the run).  The rest (`RecRuleExtraNK`: the arity, (S),
(P), (U)) is passed through. -/

/-- **`RecRuleLaw`'s main conjunct, named** (`Model/Env/Laws.lean`,
verbatim). -/
@[expose] def RecRuleMain {env : Env}
    (m : EnvModel V env) (φ : Name → Nat)
    (n : Name) (cv : ConstantVal) (mI rP : Nat) (isK : Bool) (rl : RecRule) :
    Prop :=
  ∀ us : List Level, us.length = cv.levelParams.length →
    ∃ Ra : Term,
      denote m.acval env φ 0
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        = some Ra ∧
      (∀ ρ : Nat → V, WellDenoted V ρ Ra) ∧
      -- The nested pins' open readings are carried with a
      -- CONTEXT-GUARDED chain grading (an unconditional `∀ ρ` form is
      -- refutable: the checker's certificate is about the pins
      -- instantiated at the public frame, and converts only
      -- context-guarded).  The grading is stated of the chained term
      -- at the chain's own environment: `TeleFitPA` is that
      -- environment's `Sat` in closed form.  The consumer reads it to
      -- run the case-3 pin comparison's claim (`RecRuleExtra`'s (U)).
      (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
        ∀ i, i < pins.length →
        ∃ vpa : Term,
          denote m.acval env φ rP
            (ConLeche.Verify.openRev 0 rP
              ((pins.getD i default).instantiateLevelParams
                cv.levelParams us)) = some vpa ∧
          ∀ (ρ : Nat → V) (zs : List Term) (TVa restR : Term),
            zs.length = rP →
            (∀ z ∈ zs, WellDenoted V ρ z) →
            denote m.acval env φ 0
              (cv.type.instantiateLevelParams cv.levelParams us)
              = some TVa →
            TeleFitPA V ρ TVa zs restR →
            WellDenoted V ρ
              (Term.instRevChain zs vpa)) ∧
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List Term)
        (TVa TVja restR restC : Term),
        xs.length = mI →
        ys.length = cnP + RecRule.nfields rl →
        usj.length = cvj.levelParams.length →
        Level.substFn φ cvj.levelParams usj
          = Level.substFn φ cvj.levelParams
              (ConLeche.recFireComparands rl cnP cv.levelParams us
                cvj.levelParams [] rP).1 →
        -- the fired spine is graded (task #342 S5b: the constructor's own
        -- parameters are not compared outside case 3; its application is
        -- read at them, `genOutCtorOwn`)
        (∀ y ∈ ys, WellDenoted V ρ y) →
        -- the index pin, owed only where the fired constructor application
        -- is the point (task #342 L10: a family never `Prop` at the
        -- instance fires with no index comparison; the law reads the pin
        -- only at a `Prop` valuation)
        (interp V ρ (Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          IotaIndexPin (V := V) ρ restC cnP mI rP xs) →
        denote m.acval env φ 0
          (cv.type.instantiateLevelParams cv.levelParams us)
          = some TVa →
        denote m.acval env φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj)
          = some TVja →
        TeleFitPA V ρ TVa
          (xs ++ [Term.mkAppN
            (m.acval (RecRule.ctor rl)
              (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        TeleFitPA V ρ TVja ys restC →
        interp V ρ
            (Term.mkAppN
              (m.acval n (Level.substFn φ cv.levelParams us))
              (xs ++ [Term.mkAppN
                (m.acval (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]))
          = interp V ρ
              (Term.mkAppN Ra
                (xs.take rP ++ ys.drop cnP)) ∧
        ((∀ a ∈ xs, WellDenoted V ρ a) → (∀ b ∈ ys, WellDenoted V ρ b) →
          WellDenoted V ρ
            (Term.mkAppN Ra
              (xs.take rP ++ ys.drop cnP)))

/-- **`RecRuleExtra` past its K clause, named**: the constructor's
arity, and for a rule that is not K the (S), (T), (P), (U) clauses
(`Model/Env/Laws.lean`, verbatim). -/
@[expose] def RecRuleExtraNK {env : Env}
    (m : EnvModel V env) (φ : Name → Nat)
    (_n : Name) (cv : ConstantVal) (mI rP : Nat) (isK : Bool) (rl : RecRule) : Prop :=
  ∀ us : List Level, us.length = cv.levelParams.length →
    ∀ TVa : Term,
      denote m.acval env φ 0
        (cv.type.instantiateLevelParams cv.levelParams us) = some TVa →
    ∀ (cvj : ConstantVal) (cnP cnF : Nat),
      env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
    -- the constructor's arity
    (cvj.type.stripPis (cnP + RecRule.nfields rl)).isSome = true ∧
    (isK = false →
    -- (S)
    (ConLeche.iotaCtorNeverProp env.find? cvj
        (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams [] rP).1 = true →
      ∀ (ρ : Nat → V) (xs : List Term) (a restR : Term),
        xs.length = mI → TeleFitPA V ρ TVa (xs ++ [a]) restR →
        interp V ρ a ≠ pt) ∧
    -- (T)
    (ConLeche.iotaCtorNeverProp env.find? cvj
        (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams [] rP).1 = true →
      ∀ (usj : List Level), usj.length = cvj.levelParams.length →
      ∀ TVja : Term,
        denote m.acval env φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
      ∀ (ρ : Nat → V) (xs ys : List Term) (restR restC : Term),
        xs.length = mI →
        ys.length = cnP + RecRule.nfields rl →
        TeleFitPA V ρ TVa
          (xs ++ [Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        TeleFitPA V ρ TVja ys restC →
        (∀ x ∈ xs, WellDenoted V ρ x) → (∀ y ∈ ys, WellDenoted V ρ y) →
        interp V ρ (Term.mkAppN
          (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) ≠ pt →
        ∃ (usj' : List Level) (ys' : List Term) (TVja' restC' : Term),
          usj'.length = cvj.levelParams.length ∧
          Level.substFn φ cvj.levelParams usj'
            = Level.substFn φ cvj.levelParams
                (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams [] rP).1 ∧
          denote m.acval env φ 0
            (cvj.type.instantiateLevelParams cvj.levelParams usj') = some TVja' ∧
          ys'.length = ys.length ∧
          ys'.drop cnP = ys.drop cnP ∧
          (∀ y ∈ ys', WellDenoted V ρ y) ∧
          TeleFitPA V ρ TVja' ys' restC' ∧
          interp V ρ (Term.mkAppN
              (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj')) ys')
            = interp V ρ (Term.mkAppN
              (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys)) ∧
    ∀ (usj : List Level), usj.length = cvj.levelParams.length →
      Level.substFn φ cvj.levelParams usj
        = Level.substFn φ cvj.levelParams
            (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams [] rP).1 →
    ∀ TVja : Term,
      denote m.acval env φ 0
        (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
    -- (P)
    (∀ (ρ : Nat → V) (xs : List Term) (a restR : Term),
        xs.length = mI → TeleFitPA V ρ TVa (xs ++ [a]) restR →
        interp V ρ a = pt →
      ∀ (ys : List Term) (restC : Term), TeleFitPA V ρ TVja ys restC →
        ys.length = cnP + RecRule.nfields rl →
        (∀ y ∈ ys, WellDenoted V ρ y) →
        interp V ρ (Term.mkAppN
          (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt) ∧
    -- (U)
    (∀ (ρ : Nat → V) (xs ys : List Term) (restR restC : Term),
        xs.length = mI →
        ys.length = cnP + RecRule.nfields rl →
        TeleFitPA V ρ TVa
          (xs ++ [Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        TeleFitPA V ρ TVja ys restC →
        (∀ x ∈ xs, WellDenoted V ρ x) → (∀ y ∈ ys, WellDenoted V ρ y) →
        (RecRule.fire rl = .plain →
          interp V ρ (Term.mkAppN
              (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          ∀ i, i < cnP → i < mI →
            interp V ρ (ys.getD i default) ≠ pt → interp V ρ (xs.getD i default) ≠ pt →
            interp V ρ (ys.getD i default) = interp V ρ (xs.getD i default)) →
        (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
          interp V ρ (Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          ∀ i, i < cnP →
          ∀ vpa : Term,
            denote m.acval env φ rP
              (ConLeche.Verify.openRev 0 rP
                ((pins.getD i default).instantiateLevelParams
                  cv.levelParams us)) = some vpa →
            interp V ρ (ys.getD i default) ≠ pt →
            interp V ρ (Term.instRevChain (xs.take rP) vpa) ≠ pt →
            interp V ρ (ys.getD i default)
              = interp V ρ (Term.instRevChain (xs.take rP) vpa)) →
        (interp V ρ (Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          IotaIndexPinC (V := V) ρ restC cnP mI rP xs) →
        interp V ρ (Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          IotaIndexPin (V := V) ρ restC cnP mI rP xs))


/-- **The K witness**: at a K rule the constructor has no fields, and
every major value in the recursor's major domain is the value of the
constructor applied to a spine the main law accepts — the guarded
index pin, both fits — graded where the recursor's arguments are. -/
@[expose] def RecRuleKWit {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    (n : Name) (cv : ConstantVal) (mI rP : Nat) (isK : Bool) (rl : RecRule) : Prop :=
  isK = true → RecRule.nfields rl = 0 ∧
  ∀ us : List Level, us.length = cv.levelParams.length →
  ∀ TVa : Term,
    denote m.acval env φ 0 (cv.type.instantiateLevelParams cv.levelParams us) = some TVa →
  ∀ (ρ : Nat → V) (xs : List Term) (a restR : Term),
    xs.length = mI → TeleFitPA V ρ TVa (xs ++ [a]) restR →
  -- both sides are the point (a recursor that eliminates only into `Prop` here)
  (interp V ρ (Term.mkAppN (m.acval n (Level.substFn φ cv.levelParams us)) (xs ++ [a]))
      = pt ∧
    ∀ Ra : Term,
      denote m.acval env φ 0
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us) = some Ra →
      interp V ρ Ra = pt) ∨
  ∃ (cvj : ConstantVal) (cnP cnF : Nat) (usj : List Level) (ys : List Term)
    (TVja restR' restC : Term),
    env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) ∧
    ys.length = cnP + RecRule.nfields rl ∧
    usj.length = cvj.levelParams.length ∧
    Level.substFn φ cvj.levelParams usj
      = Level.substFn φ cvj.levelParams
          (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams [] rP).1 ∧
    (interp V ρ (Term.mkAppN
        (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
      IotaIndexPin (V := V) ρ restC cnP mI rP xs) ∧
    denote m.acval env φ 0 (cvj.type.instantiateLevelParams cvj.levelParams usj)
      = some TVja ∧
    TeleFitPA V ρ TVa
      (xs ++ [Term.mkAppN
        (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys]) restR' ∧
    TeleFitPA V ρ TVja ys restC ∧
    interp V ρ a = interp V ρ (Term.mkAppN
      (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) ∧
    ((∀ x ∈ xs, WellDenoted V ρ x) → ∀ y ∈ ys, WellDenoted V ρ y)

/-- **`RecRuleLaw` from its main conjunct, the K witness and the rest**:
the K law is the main law at the witness's fired spine — the major
enters the recursor's application only through its value, and the
fieldless spine's field part is empty. -/
theorem recRuleLaw_of_main {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    {n : Name} {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rl : RecRule}
    (hrPle : rP ≤ mI) (hmain : RecRuleMain m φ n cv mI rP isK rl)
    (hK : RecRuleKWit m φ n cv mI rP isK rl) (hNK : RecRuleExtraNK m φ n cv mI rP isK rl) :
    RecRuleLaw m φ n cv mI rP isK rl := by
  refine ⟨hrPle, hmain, fun us hus TVa hTVa => ⟨fun hk => ?_, hNK us hus TVa hTVa⟩⟩
  obtain ⟨hnf, hwit⟩ := hK hk
  refine ⟨hnf, fun Ra hRa ρ xs a restR hxl hfit hxwd => ?_⟩
  obtain ⟨Ra', hRa', hokRa, -, hsp⟩ := hmain us hus
  have hRR : Ra' = Ra := Option.some.inj (hRa'.symm.trans hRa)
  rw [hRR] at hokRa hsp
  rcases hwit us hus TVa hTVa ρ xs a restR hxl hfit with ⟨hL, hR⟩ | hwit
  · have hRpt := hR Ra hRa
    exact ⟨hL.trans (Rules.interp_mkAppN_pt hRpt _).symm, fun hxs =>
      mkAppN_wellDenoted_of_pt (hokRa ρ) hRpt fun x hx => hxs x (List.mem_of_mem_take hx)⟩
  obtain ⟨cvj, cnP, cnF, usj, ys, TVja, restR', restC, hfj, hyl, husj, hψ, hpin,
    hTVja, hfitR, hfitC, hval, hwd⟩ := hwit
  obtain ⟨heq, hok⟩ := hsp cvj cnP cnF hfj usj ρ xs ys TVa TVja restR' restC hxl hyl husj hψ
    (hwd hxwd) hpin hTVa hTVja hfitR hfitC
  have hdrop : ys.drop cnP = [] := by
    rw [List.drop_eq_nil_iff, hyl, hnf]; omega
  rw [hdrop, List.append_nil] at heq hok
  refine ⟨?_, fun hxs => hok hxs (hwd hxs)⟩
  rw [← heq, interp_mkAppN_foldl, interp_mkAppN_foldl, List.map_append, List.map_append,
    List.map_singleton, List.map_singleton, hval]

/-- **A new block recursor's rule law, at either firing**.  `hpins` is
`RecRuleLaw`'s outer `.nested` conjunct — the pins'
open readings and their context-guarded grading — vacuous at a `.plain`
rule; `hrhs` receives no parameter comparison at either firing: the
major's membership in the family at the comparands identifies the fired
spine with the rule's own (`BlockRuleDataAt`'s `mk` conjunct). -/
theorem blockRecRuleLaw_gen {env : Env} {m₃ : EnvModel V env} {φ : Name → Nat}
    {n : Name} {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rl : RecRule}
    {K c : Nat} {leafF : (Name → Nat) → Nat → Term}
    {pdomsF fdomsF esF ihsF : (Name → Nat) → List Term}
    {mkF RbF : (Name → Nat) → Term}
    (hrPle : rP ≤ mI) (hc : c < K)
    (hleaf : ∀ ψ : Name → Nat, m₃.acval n ψ = leafF ψ c)
    (hiota : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      BlockIotaAt V K c (leafF ψ) (pdomsF ψ) (fdomsF ψ) (esF ψ) (mkF ψ) (ihsF ψ) (RbF ψ) ρ)
    (hpins : RecRulePinsOk m₃ φ cv rP rl)
    (hK : RecRuleKWit m₃ φ n cv mI rP isK rl) (hNK : RecRuleExtraNK m₃ φ n cv mI rP isK rl)
    (hrhs : ∀ us : List Level, us.length = cv.levelParams.length →
      ∃ Ra : Term,
        denote m₃.acval env φ 0
            ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us) = some Ra ∧
        (∀ ρ : Nat → V, WellDenoted V ρ Ra) ∧
        ∀ (cvj : ConstantVal) (cnP cnF : Nat),
          env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
        ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List Term)
          (TVa TVja restR restC : Term),
          xs.length = mI →
          ys.length = cnP + RecRule.nfields rl →
          usj.length = cvj.levelParams.length →
          Level.substFn φ cvj.levelParams usj
            = Level.substFn φ cvj.levelParams
                (ConLeche.recFireComparands rl cnP cv.levelParams us cvj.levelParams [] rP).1 →
          (∀ y ∈ ys, WellDenoted V ρ y) →
          (interp V ρ (Term.mkAppN
              (m₃.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
            IotaIndexPin (V := V) ρ restC cnP mI rP xs) →
          denote m₃.acval env φ 0
              (cv.type.instantiateLevelParams cv.levelParams us) = some TVa →
          denote m₃.acval env φ 0
              (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
          TeleFitPA V ρ TVa
            (xs ++ [Term.mkAppN
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
              ρ rP cnP xs ys
              (m₃.acval (RecRule.ctor rl)
                (Level.substFn φ cvj.levelParams usj)) Ra) ∨
            -- the `ℓ = 0` arm: both sides of the fired equation are the point
            (interp V ρ (Term.mkAppN (leafF (Level.substFn φ cv.levelParams us) c)
                (xs ++ [Term.mkAppN (m₃.acval (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys])) = pt ∧
              interp V ρ (Term.mkAppN Ra (xs.take rP ++ ys.drop cnP))
                = pt)) ∧
          ((∀ a ∈ xs, WellDenoted V ρ a) → (∀ b ∈ ys, WellDenoted V ρ b) →
            WellDenoted V ρ (Term.mkAppN Ra
              (xs.take rP ++ ys.drop cnP)))) :
    RecRuleLaw m₃ φ n cv mI rP isK rl := by
  refine recRuleLaw_of_main hrPle (fun us hus => ?_) hK hNK
  obtain ⟨Ra, hRa, hokRa, hspine⟩ := hrhs us hus
  refine ⟨Ra, hRa, hokRa, hpins us hus, ?_⟩
  intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl hujl hψ
    hyWD hidx hTVa hTVja hfitR hfitC
  obtain ⟨hdata, hok⟩ := hspine cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC
    hxl hyl hujl hψ hyWD hidx hTVa hTVja hfitR hfitC
  refine ⟨?_, hok⟩
  rw [hleaf]
  rcases hdata with hdata | ⟨hL, hR⟩
  · exact blockRecRuleEq_of_data (hiota _ ρ) hc (by rw [hxl]; exact hrPle) hdata
  · exact hL.trans hR.symm


/-! ## 8. `hrecP`, as `blockRecStaged_of` consumes it

The composition: the rules' SHAPE (`RecRulesShape`) names the
constructor and the right-hand side a stored rule was built from, so
the premise is stated per `(recursor, constructor)` pair rather than
per anonymous rule. -/

/-- **`hrecP`, at any rules of the shape**:
per (recursor, constructor) pair, the rule the SHAPE names. -/
theorem hrecP_ofR {R : Nat → RecDatum → Bool × List RecRule} {q : BlockShape} {rs : List RecDatum}
    {envC : Env} {acv : Name → (Name → Nat) → Term} (mpC : EnvModelM V envC)
    {fireOf : Nat → RecDatum → ConLeche.RecRuleFire}
    (hshape : ConLeche.RecRulesShape R rs fireOf)
    (hfr : ∀ r ∈ rs, envC.find? r.1.name = none)
    (hag : ∀ n : Name, (∀ r ∈ rs, n ≠ r.1.name) → acv n = mpC.base2.acval n)
    (hnew : ∀ m₃ : EnvModel V (consBlockRecsR R q 0 rs envC), m₃.acval = acv →
      ∀ (φ : Name → Nat) (j : Nat) (r : RecDatum), rs[j]? = some r →
      ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
        r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
        RecRuleLaw m₃ φ r.1.name r.1 (q.majorIdxAt j) (q.rulePrefixAt j) (R j r).1
          ({ ctor := cA.1.name, nfields := cA.2, fire := fireOf j r, rhs := rhs })) :
    ∀ m₃ : EnvModel V (consBlockRecsR R q 0 rs envC),
      m₃.acval = acv → ∀ φ : Name → Nat, RecRules m₃ φ := by
  intro m₃ hac φ
  refine recRules_consBlockRecsR_of mpC hfr hag m₃ hac φ ?_
  intro j r hr rl hrl
  obtain ⟨i, cA, rhs, hcA, hrhs, rfl⟩ := hshape j r hr rl hrl
  exact hnew m₃ hac φ j r hr i cA rhs hcA hrhs

end ConLeche.Model
