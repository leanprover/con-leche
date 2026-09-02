import Setlec.SetR.Interp2.CapsP

/-!
# The fired modeled-iota contract across a fresh cons (task #161, iota
tier)

`recRulesP_cons_fresh`, the obligation every value-kind harvest
discharges for the new `EnvS2PM` field `rec_rules`.  The statements
live in `Annot/EnvS2P.lean` beside `CapsOkP` (the field must mention
them); this is the preservation half, `capsOkP_cons_fresh`'s sibling.

## FINDING — every crossing is FORWARD; no equality-form transfer

The freeze anticipated that the law's reading *premises* (`TVa`,
`TVja`, and the `.nested` clause's `vpa`) would have to move
**backward** across the cons, through the equality-form
`denoteP_cons_fresh`, and flagged that as legal at value-kind conses
because the `noConfusion` pair supplies `LitGuardsAgree`.

Neither the backward transfer nor that justification is needed, and
the justification would not have held: the literal tier's seal I
already showed `LitGuardsAgree` is **refutable** at a value-kind cons
(a `def` named `String.ofList` completes string support and flips the
`str` half), which is exactly why `LitStabilityP` was deleted.  Only
the `nat` half is free from the `noConfusion` pair.

What makes the backward direction unnecessary is that the readings
sit in *premise* position, so the transfer they need is contravariant:

* `TVa`/`TVja` are ∀-bound premises, so instead of moving the given
  extension reading down, the proof produces the **prefix** reading
  from `EnvS2PM.constTypeP`, moves *that* forward
  (`denoteP_cons_fresh_mono`), and identifies the two by determinism —
  the `type_reads`/`type_okP` idiom `declStepPM_of_cons` already uses
  three times;
* the `.nested` clause is itself a premise, so proving the prefix form
  of it *consumes* the extension form: a prefix pin reading is moved
  **forward** and fed to the hypothesis in hand.

So the whole preservation runs on `denoteP_cons_fresh_mono`, the only
crossing the campaign has ever shown to be honest, and no literal-tier
premise appears — matching what the literal tier's seal established
for the harvests.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env}

/-- The reverse opening introduces no constants, so it preserves
prefix-boundedness (its opener annotations are `.sort .zero`). -/
theorem constsBound_openRev {env₀ : Env} {e : Expr}
    (h : ConstsBound env₀ e) :
    ∀ d n : Nat, ConstsBound env₀ (openRev d n e) := by
  intro d n
  induction n with
  | zero => exact h
  | succ n ih =>
    show ConstsBound env₀ ((openRev d n e).instantiate1
      (.fvar (d + n) Name.anonymous (.sort .zero)) 0)
    exact ConstsBound.instantiate1 (by simp) _ 0 ih

/-- **The fired modeled-iota contract survives a fresh cons that is
not itself a recursor.**

The recursor disequality is the cons's kind.  The *constructor*
disequality was a second premise until ENDGAME D, and it is not
needed: `EnvS.rec_ctors` (`RecCtorsStored`, `Verify/EnvPreds.lean:64`)
says every stored recursor rule's constructor is itself **stored**, and
the cons is fresh — so `RecRule.ctor rl ≠ c₀.name` follows from the
environment invariant rather than from the cons's kind.  Dropping it is
what lets the **basis** tier use this lemma at its `indInfo`/`ctorInfo`
conses, where the kind premise is false (`Interp2/BasisConsP.lean`'s
`rec_rules` row recorded that as a wall; it is not one).

A recursor cons with rules still establishes its *own* rules bespoke —
that is the firing-law work, not a transport.  A recursor cons with
**no** rules (`Empty.rec`) transports here unchanged, which is why the
premise is `rules = []` rather than "not a recursor". -/
theorem recRulesP_cons_fresh (mp : EnvS2PM V μ env)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AVExpr}
    (hfresh : env.find? c₀.name = none)
    (hnotrec : ∀ cv mI rP rules, c₀ = .recInfo cv mI rP rules →
      rules = [])
    (m₂ : EnvS2Core V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval c₀.name A)
    (φ : Name → Nat) : RecRulesP m₂ φ := by
  intro n cv mI rP rules hf rl hmem hfire
  -- the recursor is stored in the prefix: either the cons is not a
  -- recursor at all (the value kinds' `noConfusion`), or it is one
  -- with no rules (a basis recursor whose block installs its ι
  -- content elsewhere), and then `rl ∈ rules` is impossible
  have hnN : n ≠ c₀.name := by
    intro hh
    subst hh
    have hrl := hnotrec cv mI rP rules
      (Option.some.inj ((Setlec.Env.find?_cons_self c₀ env).symm.trans hf))
    rw [hrl] at hmem
    exact nomatch hmem
  have hfE : env.find? n = some (.recInfo cv mI rP rules) := by
    rw [Setlec.Env.find?_cons, if_neg (fun hh => hnN hh.symm)] at hf
    exact hf
  obtain ⟨hrPle, hlaw0⟩ := mp.rec_rules φ n cv mI rP rules hfE rl hmem hfire
  refine ⟨hrPle, fun us hlen => ?_⟩
  obtain ⟨Ra, hRa0, hokRa, hpinsOk, hlaw⟩ := hlaw0 us hlen
  obtain ⟨-, -, -, -, -, hrec', -⟩ :=
    mp.base2.base.wf _ (Setlec.SetR.Env.find?_mem hfE)
  obtain ⟨-, -, hRres, -, hnest⟩ := hrec' cv mI rP rules rfl rl hmem
  refine ⟨Ra, ?_, hokRa, ?_, ?_⟩
  · rw [hac]
    exact denoteP_cons_fresh_mono hfresh _ 0 _
      (constsBound_of_constsResolve _ (by
        rw [Setlec.Expr.constsResolve_instantiateLevelParams]
        exact hRres)) hRa0
  · -- the pins' carried readings, moved forward (the iota seal's
    -- ratified repair: the grading conjunct in the ∃-form crosses
    -- exactly as `Ra`'s does)
    intro lvls pins hn i hi
    obtain ⟨vpa, hvpa, hok⟩ := hpinsOk lvls pins hn i hi
    obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hn
    have hpinCR : Setlec.Expr.constsResolve env (pins.getD i default)
        = true := by
      by_cases hilt : i < pins.length
      · obtain ⟨-, -, hres, -⟩ := hpinsWf _ (Setlec.getD_mem hilt)
        exact hres
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
    refine ⟨vpa, ?_, hok⟩
    rw [hac]
    exact denoteP_cons_fresh_mono hfresh _ rP _
      (constsBound_openRev (constsBound_of_constsResolve _ (by
        rw [Setlec.Expr.constsResolve_instantiateLevelParams]
        exact hpinCR)) 0 rP) hvpa
  · intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl hujl
      hψ hplain hnested hpin hTVa hTVja hfitR hfitC
    -- **the environment invariant, not the cons's kind**: the rule's
    -- constructor is stored, and the cons is fresh
    have hnC : RecRule.ctor rl ≠ c₀.name := by
      obtain ⟨cvj', cnP', cnF', hst⟩ :=
        mp.base2.base.rec_ctors n cv mI rP rules hfE rl hmem
      intro hh
      rw [hh, hfresh] at hst
      exact nomatch hst
    have hfcjE : env.find? (RecRule.ctor rl)
        = some (.ctorInfo cvj cnP cnF) := by
      rw [Setlec.Env.find?_cons, if_neg (fun hh => hnC hh.symm)] at hfcj
      exact hfcj
    -- the two stored types: produced at the prefix, moved forward,
    -- identified with the given extension readings by determinism
    obtain ⟨TVa', hTVa', -, -⟩ :=
      mp.constTypeP 0 n _ us hfE (by exact hlen)
    obtain rfl : TVa' = TVa := by
      refine Option.some.inj (Eq.trans ?_ hTVa)
      rw [hac]
      exact (denoteP_cons_fresh_mono hfresh _ 0 _
        (constsBound_instType mp.base2.base.wf
          (Setlec.SetR.Env.find?_mem hfE) us) hTVa').symm
    obtain ⟨TVja', hTVja', -, -⟩ :=
      mp.constTypeP 0 (RecRule.ctor rl) _ usj hfcjE (by exact hujl)
    obtain rfl : TVja' = TVja := by
      refine Option.some.inj (Eq.trans ?_ hTVja)
      rw [hac]
      exact (denoteP_cons_fresh_mono hfresh _ 0 _
        (constsBound_instType mp.base2.base.wf
          (Setlec.SetR.Env.find?_mem hfcjE) usj) hTVja').symm
    -- the `.nested` premise, contravariantly: a prefix pin reading is
    -- moved FORWARD and fed to the hypothesis in hand
    have hnested' : ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
        ∀ i, i < RecRule.ctorParams rl →
        ∀ vpa : AVExpr,
          denoteP mp.base2.acval env φ rP
            (openRev 0 rP ((pins.getD i default).instantiateLevelParams
              cv.levelParams us)) = some vpa →
          interp2 V ρ (ys.getD i default)
            = interp2 V ρ (AVExpr.instRevChain (xs.take rP) vpa) := by
      intro lvls pins hn i hi vpa hvpa
      refine hnested lvls pins hn i hi vpa ?_
      obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hn
      have hpinCR : Setlec.Expr.constsResolve env (pins.getD i default)
          = true := by
        by_cases hilt : i < pins.length
        · obtain ⟨-, -, hres, -⟩ := hpinsWf _ (Setlec.getD_mem hilt)
          exact hres
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          rfl
      rw [hac]
      exact denoteP_cons_fresh_mono hfresh _ rP _
        (constsBound_openRev (constsBound_of_constsResolve _ (by
          rw [Setlec.Expr.constsResolve_instantiateLevelParams]
          exact hpinCR)) 0 rP) hvpa
    -- the two leaves the conclusion mentions are the prefix's
    rw [hac, acvalWith_ne hnC] at hfitR
    rw [hac, acvalWith_ne hnN, acvalWith_ne hnC]
    exact hlaw cvj cnP cnF hfcjE usj ρ xs ys _ _ restR restC hxl hyl
      hujl hψ hplain hnested' hpin hTVa' hTVja' hfitR hfitC

end Setlec.SetR.Interp2
