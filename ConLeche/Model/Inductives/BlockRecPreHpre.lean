module

import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.BlockIndRegimeRun
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.BlockDatum
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Model.Inductives.BlockRecRead

public section

/-!
# The regime DISPATCH at the run — `hpre` for the endpoint (task #315, M5M-hpre)

`declBlock_data` (`BlockRecData.lean` §A.18) asks the seam for, among
eight conjuncts, the family's **regime**:

```
∀ ψ ρ, BlockRecPre V (s ψ) rs.length (blockRecTyAV …)
         (blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ) ρ
```

Three producers stand behind it — `blockIndRegime_run` at `ℓ = 0`,
`blockKitRegime_wf` at `ℓ ≠ 0 ∧ w ≠ 0`, `blockKitRegime_sq` at
`ℓ ≠ 0 ∧ w = 0` (`BlockRecPreRun.lean` §5, §19, §36) — and
`blockRecPre_hpre` (§15) is the dispatch over them, but stated in the
DISPATCH's own currency and with the two regime bundles as free
hypotheses.  This file is the composition: the currency change, the
level's skolemisation, the `(w, ℓ)` split and the `K = 1` transport,
in one theorem whose conclusion is the endpoint's premise verbatim.

**What the composition turned out to need** — four things nobody had
listed:

1. **The equation list is the rule lane's, the dispatch's is the model
   lane's.**  `blockRecPre_hpre` concludes at `iotaEqsAV` over
   components the caller supplies; the endpoint asks for `blockRecEqs`
   = `blockIotaEqsAV` over the run's BASE components.  §1 is that
   identification, and it is exactly §20's four `…K` definitions fed
   to §31's `iotaEqsAV_eq_blockIotaEqsAV` — which, before this file,
   had no consumer.
2. **The level must be skolemised by the CONSUMER.**  Every regime's
   guard is a statement about a natural number `ℓ`, and the run hands
   the level back existentially (`blockRecElimLevel_run`,
   `blockRecOneElimLevel_run`).  A guard on an existential level is
   not a guard, so `us` is a PARAMETER here and the guard reads
   `(us.headD .zero).eval ψ = 0` — the run's own currency, and the
   spelling `blockIndRegime_of_run` already takes.
3. **`OneElimLevel` leaves both kit regimes' premise sets.**  `hbits`
   is a premise of `blockKitRegime_wf` and of `blockKitRegime_sq`, and
   with the level named it is `blockRecOneElimLevel` — discharged here
   for both arms at once, from the same three witnesses the IND arm's
   guard is stated over.  It is the one premise the three regimes
   genuinely share.
4. **The ι equations' grading is NOT a premise of the dispatch.**
   The rule lane's fold `blockRecHwd_of_rules`
   (`BlockRuleFit.lean`) is the family's `hwd` conjunct for
   conjunct at `σ := consList as ρ`, so the dispatch takes the
   fold's FOUR premises — the per-rule certificates and its three
   frame premises, ψ- and ρ-quantified — and produces `hwd` itself.
   A premise with no discharge route is the dual of a premise set
   with no instance, and neither is visible in a build.
5. **The SQ arm needs `rs.length = 1`, and that is a KERNEL fact.**
   `blockKitRegime_sq` produces `KitRegimeAt … 1 …`; the dispatch
   consumes `KitRegimeAt … rs.length …`.  The two meet only through
   `rs.length = 1`, and no model-tier fact implies it: it is what the
   large-elimination COUNTING guard says.  `blockLargeElimAllowed`'s
   own arm is a RUN (`isDefEq` against `Sort 0`) and the model holds
   only the LEVEL `ensureSort` returned, so the checker says the
   counting half a second time in the level currency
   (`checkBlockRecSmallElim`, lane SEC2), stated as the GUARD's own
   verdict so that the regime lane's `blockLargeElim_counting` reads
   all FOUR of the squash arm's facts off it rather than this file
   deriving one of them a second time.  §2.5's `blockRecCounting_run`
   is the licence and `blockRecK1_run` the dispatch's slice of it, off
   the same three package components the kit arms take.  It is a
   THEOREM here, not a premise.

**The guard lives in ONE place.**  `blockRecPre_dispatch_run`'s proof
contains the only `by_cases` on `d.w ψ`, and the three regime bundles
name their guards once each.  If the rule contract's guard moves from
`d.w ψ ≠ 0` to `ℓ ψ ≠ 0` (the W0 report's recommendation), the change
here is the `hWF`/`hSQ` premises' guards and nothing else; the
dispatch's `ℓ`-split is already the outer one.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. THE CURRENCY — the dispatch's equations ARE the endpoint's

The dispatch parameterises at the ι equations' components AT THE CHAIN
FRAME (§20's `blockRecPdomsK`/`blockRecFdomsK`/`blockRecEsK`/
`blockRecMkK`); the endpoint states its premise at `blockRecEqs`, the
rule lane's `blockIotaEqsAV` over the BASE components.  The two are
one term, and the only thing separating them is the residue's cutoff —
the dispatch writes the LIFTED prefix and field lengths, the rule lane
the unlifted ones, and `liftDomsK_length` is a theorem, not `rfl`.

The identification is §31's; what is new here is that the four `…K`
definitions are its instance, so the two lanes' `eqs` meet at a NAMED
term rather than at a pair of matching parameter choices. -/

section Currency

/-- **The dispatch's equation list IS `blockRecEqs`** at the run's own
components. -/
theorem blockRecEqs_runK {envC : Env} {acval : Name → (Name → Nat) → AnnotTerm}
    {q : ConLeche.BlockShape}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}
    {nCt : Nat → Nat}
    {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm} (ψ : Name → Nat) :
    iotaEqsAV rs.length nCt
        (blockRecPdomsK rs.length acval envC q rs ψ)
        (blockRecFdomsK rs.length acval envC q rs ψ)
        (blockRecEsK rs.length acval envC q rs ψ)
        (blockRecMkK rs.length acval envC q rs ψ)
        (ihs ψ)
        (fun c j => (Rb0 ψ c j).liftN rs.length
          ((blockRecPdomsK rs.length acval envC q rs ψ c).length
            + (blockRecFdomsK rs.length acval envC q rs ψ c j).length + (ihs ψ c j).length))
      = blockRecEqs nCt rs
          (fun ψ' => blockRulePdomsAV acval envC q rs ψ')
          (fun ψ' => blockRuleFdomsAV q rs acval envC ψ')
          (fun ψ' => blockRuleEsAV q rs acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV q rs acval envC ψ')
          Rb0 ψ :=
  iotaEqsAV_eq_blockIotaEqsAV
    (pdoms0 := blockRulePdomsAV acval envC q rs ψ)
    (fdoms0 := blockRuleFdomsAV q rs acval envC ψ)
    (es0 := blockRuleEsAV q rs acval envC ψ)
    (mk0 := blockRuleMkAV q rs acval envC ψ)

end Currency


/-! ## 2. THE DISPATCH — the endpoint's premise, from the three regimes

`blockRecPre_hpre` (§15) splits on `ℓ = 0`; the `w` split lives in
whoever supplies `KitRegimeAt`, which is here.  Everything the three
producers cannot see is paid in this one theorem:

* the family's elimination LEVEL is NAMED (`us`, a parameter), so each
  regime's guard is a statement about a numeral rather than a
  hypothesis under an existential — and it is named in the RUN's
  currency, `(us.headD .zero).eval ψ`, which is the sort stage (b)
  read off the first recursor's conclusion and the spelling
  `blockIndRegime_of_run` already asks for;
* the ι equations are re-spelled from the dispatch's currency to the
  endpoint's (§1, and the `pdoms` collapse below);
* the SQ arm arrives at `K = 1` and is transported to `rs.length` by
  `hK1`;
* the `(w, ℓ)` split itself.

**The guard is in ONE place**: the `by_cases` in the proof, and the
three bundles' own guards.  Moving the contract's guard from
`d.w ψ ≠ 0` to `ℓ ψ ≠ 0` is an edit to `hWF`/`hSQ`'s statements and to
nothing else; the `ℓ`-split is already the outer one.

**The `pdoms` currency, and why it is the BASE form.**  §20 states the
dispatch's components at the CHAIN frame (`blockRecPdomsK` =
`liftDomsK K 0 ∘ blockRulePdomsAV`), and the endpoint's `blockRecEqs`
lifts the base ones the same way — but all THREE producers hand their
regime back at the BASE form: `blockKitRegime_wf`/`_sq` because
`hpdE` pins `pdoms` to the recursor type's own first `rP` binder
domains, and `blockIndRegime_of_run` because it states its conclusion
at `blockRulePdomsAV` outright.  Since `IndRegimeAt` and `KitRegimeAt`
are proof-tier `def`s, opaque outside `BlockRecPreRun.lean`, a
consumer cannot move a regime from one form to the other; so the
dispatch is stated at the BASE form and the collapse is paid ONCE, in
the equation list, where `iotaEqsAV` is exposed and a congruence is
available (§28's `blockRecPdomsK_run` is what makes it true). -/

section Dispatch

omit [SetTheory V] in
/-- A `flatMap` congruence at the members — core has none. -/
theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a (.head _),
      ih fun b hb => h b (.tail _ hb)]

omit [SetTheory V] in
/-- **The equation list depends on `pdoms` and the residue only BELOW
`K`** — the congruence the `pdoms` collapse is paid through. -/
theorem iotaEqsAV_congr {K : Nat} {nCt : Nat → Nat} {pdoms pdoms' : Nat → List AnnotTerm}
    {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
    {ihs : Nat → Nat → List AnnotTerm} {Rb Rb' : Nat → Nat → AnnotTerm}
    (hp : ∀ c, c < K → pdoms c = pdoms' c)
    (hRb : ∀ c, c < K → ∀ j, j < nCt c → Rb c j = Rb' c j) :
    iotaEqsAV K nCt pdoms fdoms es mk ihs Rb
      = iotaEqsAV K nCt pdoms' fdoms es mk ihs Rb' := by
  show (List.range K).flatMap _ = (List.range K).flatMap _
  refine flatMap_congr_mem fun c hc => ?_
  have hcK := List.mem_range.mp hc
  refine List.map_congr_left fun j hj => ?_
  rw [hp c hcK, hRb c hcK j (List.mem_range.mp hj)]

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {d : BlockData V} {s : (Name → Nat) → Nat} {us : List Level}
  {ihs ihdoms : (Name → Nat) → Nat → Nat → List AnnotTerm}
  {Rb0 Ca : (Name → Nat) → Nat → Nat → AnnotTerm} {uOf : Nat → Level}

/-- **The endpoint's equation list, at the BASE prefix domains** — §1
through §28's collapse. -/
theorem blockRecEqs_base (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (ψ : Name → Nat) :
    iotaEqsAV rs.length (blockRecNCt rs)
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (ihs ψ)
        (fun c j => (Rb0 ψ c j).liftN rs.length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
            + (ihs ψ c j).length))
      = blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ')
          Rb0 ψ := by
  rw [← blockRecEqs_runK (acval := mpC.base2.acval) (envC := envC) (q := p.toBlockShape)
    (nCt := blockRecNCt rs) (ihs := ihs) (Rb0 := Rb0) ψ]
  refine iotaEqsAV_congr (fun c hc => ?_) (fun c hc j _ => ?_)
  · exact (blockRecPdomsK_run (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ rs.length).symm
  · rw [blockRecPdomsK_run (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ rs.length]

/-! ## 2.5 THE COUNTING GUARD AT THE RUN — the dispatch's `hK1`

`blockKitRegime_sq` lives at `K = 1` and every run-level discharge is
indexed over the recursor list, so the SQ arm is unstateable at the run
without `rs.length = 1`.  That is not a model fact and no model fact
implies it: it is what the kernel's COUNTING guard says.

`blockLargeElimAllowed`'s own arm is a RUN (`isDefEq` of the
conclusion's inferred type against `Sort 0`), and the model holds of a
conclusion only the LEVEL `ensureSort` returned — so the checker says
the counting half a second time, in the level currency
(`checkBlockRecSmallElim`, `Kernel/Inductives/BlockInstall.lean`, lane
SEC2): a block declares a family, and a block of SEVERAL families whose
result sort may be `0` eliminates only at a level equivalent to zero.

The three premises below (`helim`, `hmemU`, `hruns`) are components
1, 2 and 4 of `blockRecElimLevel_run`'s package VERBATIM, which is
where the dispatch's `us` and `uOf` come from; `hres` is `rfl` at
`blockDataOf` (`resSort := q.resSort`).  The chain is: the pins give
one recursor per member, stage (b) gives `rs.length = p.recs.length`,
the counting guard gives `p.k = 1` — and `0 < p.k`, which is what makes
the FIRST recursor's level nameable at all (`uOf 0`), and hence what
ties the package's abstract `us.headD` to the kernel's own list. -/

section Count

/-- **`checkBlockRecK`'s pins and its two pure level checks**, off the
run.  `checkBlockRecK_elimList` peels the same three binds and drops
all three facts. -/
theorem checkBlockRecK_count
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ConLeche.checkBlockRecPins (m := ConLeche.CheckM) p = .ok () ∧
    ∃ cvRus : List (ConstantVal × Nat × Level),
      ConLeche.checkBlockRecTys (ConLeche.fueledOps μ F) envC p.toBlockShape
          (ConLeche.blockNested p.kinds) cvTas p.recs 0 = .ok cvRus ∧
      ConLeche.checkBlockRecSmallElim (m := ConLeche.CheckM) p.toBlockShape
        (ConLeche.blockNested p.kinds) (cvRus.map (·.2.2)) = .ok () ∧
      ConLeche.checkBlockRecElimPin (m := ConLeche.CheckM) p.toBlockShape
        (cvRus.map (·.2.2)) = .ok () := by
  unfold ConLeche.checkBlockRecK at h
  obtain ⟨u0, hpins, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨uf, hfam, -⟩ := ConLeche.exceptBind_ok h
  rw [ConLeche.checkBlockRecFamilyAgree] at hfam
  obtain ⟨-, -, hfam⟩ := ConLeche.exceptBind_ok hfam
  obtain ⟨u1, hsmall, hfam⟩ := ConLeche.exceptBind_ok hfam
  obtain ⟨u2, hpin, -⟩ := ConLeche.exceptBind_ok hfam
  exact ⟨by cases u0; exact hpins, cvRus, htys,
    by cases u1; exact hsmall, by cases u2; exact hpin⟩

/-- **The package's `uOf c` IS stage (b)'s own level**, for every
recursor of the list.  `blockRecElimLevel_run` hands the level back
existentially, but its fourth component pins the two RUNS that produced
it — and `inferTypeCore`/`ensureSortCore` are functions, so the level
is determined.  This is what lets a fact about the KERNEL's level list
be read at the package's `us`. -/
theorem blockRecUOf_run
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    {cvRus : List (ConstantVal × Nat × Level)}
    (htys : ConLeche.checkBlockRecTys (ConLeche.fueledOps μ F) envC p.toBlockShape
      (ConLeche.blockNested p.kinds) cvTas p.recs 0 = .ok cvRus)
    {c : Nat} (hc : c < rs.length) : uOf c ∈ cvRus.map (·.2.2) := by
  obtain ⟨cvRus', htys', -, hlenR, hbridge⟩ := checkBlockRecK_elimList h
  have hcv : cvRus' = cvRus := Except.ok.inj (htys'.symm.trans htys)
  rw [hcv] at hbridge
  have hcp : c < p.recs.length := by omega
  obtain ⟨cvRi, nIdx, u, fvs, concl, sty, hcu, hop, hsty, hu⟩ :=
    checkBlockRecTys_elim htys c hcp
  rw [Nat.zero_add] at hop hsty hu
  obtain ⟨fvs', conclE', sty', hop', hsty', hu'⟩ := hruns c hc
  obtain ⟨r0, hr0⟩ : ∃ r, rs[c]? = some r := ⟨rs[c]'hc, List.getElem?_eq_getElem hc⟩
  have hr1 : r0.1 = cvRi := by
    have h' := hbridge c r0 hr0
    rw [List.getElem?_map, hcu] at h'
    simp only [Option.map_some, Option.some.injEq] at h'
    exact h'.symm
  have hrd : rs.getD c default = r0 := by rw [List.getD_eq_getElem?_getD, hr0]; rfl
  rw [hrd, hr1] at hop'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop'.symm.trans hop))
  obtain rfl : sty' = sty := Except.ok.inj (hsty'.symm.trans hsty)
  have huu : uOf c = u := Except.ok.inj (hu'.symm.trans hu.1)
  have hg : (cvRus.map (·.2.2))[c]? = some u := by rw [List.getElem?_map, hcu]; rfl
  obtain ⟨hlt, hEq⟩ := List.getElem?_eq_some_iff.mp hg
  rw [huu]
  exact hEq ▸ List.getElem_mem hlt

omit [SetTheory V] in
/-- **THE COUNTING GUARD'S FOUR FACTS, AT THE RUN.**

At a block whose result sort evaluates to zero and whose recursors
eliminate at a non-zero level, the pass's disjunction collapses onto
`blockLargeElimAllowed`'s own verdict — and the regime lane's
`blockLargeElim_counting` reads all four facts off it.  **That is the
whole point of stating the pass as the GUARD rather than as the one
counting fact**: the squash arm wants four facts, and a second
derivation of `k = 1` in the level currency beside the regime lane's
would be one fact under two names.

The pass is what licenses the collapse.  Stage (b)'s own disjunction
(`checkBlockRecTys_elim`, widened by the regime lane) is
`blockLargeElimAllowed … = true ∨ isDefEq sty (Sort 0) = .ok true`, and
its second arm is a RUN about a term, which the model cannot refute;
the pass says the same implication with `every level is zero` in that
slot, which it can. -/
theorem blockRecCounting_run
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (helim : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (hmemU : ∀ c, c < rs.length → uOf c ∈ us)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat) (hℓ : (us.headD .zero).eval ψ ≠ 0)
    (hw : Level.eval ψ p.toBlockShape.resSort = 0) :
    0 < rs.length ∧ rs.length = p.toBlockShape.k ∧
      p.toBlockShape.large = true ∧ p.toBlockShape.k = 1 ∧
      ConLeche.blockNested p.kinds = false ∧ p.toBlockShape.numCtors ≤ 1 := by
  obtain ⟨hpins, cvRus, htys, hsmall, -⟩ := checkBlockRecK_count h
  obtain ⟨-, -, -, hlenR, -⟩ := checkBlockRecK_elimList h
  obtain ⟨hk0, hcase⟩ := ConLeche.checkBlockRecSmallElim_inv hsmall
  have hklen : rs.length = p.toBlockShape.k := by
    rw [hlenR, (ConLeche.checkBlockRecPins_names hpins).1]; rfl
  have hpos : 0 < rs.length := by rw [hklen]; exact hk0
  have humem := blockRecUOf_run h hruns htys hpos
  have hu0 : Level.eval ψ (uOf 0) ≠ 0 := by
    rw [blockRecElimAgree_eval helim ψ (uOf 0) (hmemU 0 hpos)]; exact hℓ
  have hallow : ConLeche.blockLargeElimAllowed p.toBlockShape
      (ConLeche.blockNested p.kinds) = true := by
    rcases hcase with hg | hzero
    · exact hg
    · exact absurd (ConLeche.Level.isEquiv_sound (hzero _ humem) ψ) hu0
  obtain ⟨hl, hk, hn, hc⟩ := blockLargeElim_counting hallow hw
  exact ⟨hpos, hklen, hl, hk, hn, hc⟩

omit [SetTheory V] in
/-- **THE DISPATCH'S `hK1`** — the second of the four facts, at the
dispatch's own `d.w` currency. -/
theorem blockRecK1_run
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (helim : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (hmemU : ∀ c, c < rs.length → uOf c ∈ us)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (hres : d.resSort = p.toBlockShape.resSort) :
    ∀ ψ : Name → Nat, (us.headD .zero).eval ψ ≠ 0 → d.w ψ = 0 → rs.length = 1 := by
  intro ψ hℓ hw
  obtain ⟨-, hklen, -, hk1, -, -⟩ :=
    blockRecCounting_run h helim hmemU hruns ψ hℓ (by rw [← hres]; exact hw)
  rw [hklen]; exact hk1

/-- **The rule frame's level IS the checked one** (SEC1's flagged
residue, closed).  `blockRuleFrame`'s `pw` is `Level.zeronessOf
(structElimLevel p.elim p.large)`; this says that level EVALUATES to
the one the recursors actually eliminate at, at every `ψ`, so the
frame's binder data is a statement about the elimination the stream
declares and not about a shape that may disagree with it. -/
theorem blockRecElimPin_run
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) :
    Level.eval ψ (uOf c)
      = Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) := by
  obtain ⟨-, cvRus, htys, -, hpin⟩ := checkBlockRecK_count h
  exact ConLeche.Level.isEquiv_sound
    (ConLeche.checkBlockRecElimPin_inv hpin _ (blockRecUOf_run h hruns htys hc)) ψ


/-- **A non-zero elimination level forces the DECLARED large shape** —
the antecedent the constructors' stage's subsingleton clause
(`CtorDataI.srcProp`, keyed on `p.large`) wants, and the squash arm
through it.

`blockRecCounting_run`'s FIRST fact is the same flag, and this is not
a second derivation of it: that one is the counting guard's reading and
needs the block's result sort to evaluate to zero, this one is the
elimination-level PIN's and needs nothing.  Keep both, and reach for
this one wherever the `Prop`-valued hypothesis is not in hand — at a
`Type` block the counting route says nothing and this one still does.

Neither goes through the type stage's `isDefEq sty (Sort 0)`: that run
is a verdict about a TERM and inverting it to a statement about a LEVEL
is an induction over the whole lazy-delta loop.  The pin says it
syntactically — `structElimLevel p.elim p.large` is `Level.zero` at
`large = false`, so a recursor that eliminates at a non-zero level
cannot have declared the small shape. -/
theorem blockRecLarge_run
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) (hne : Level.eval ψ (uOf c) ≠ 0) :
    p.toBlockShape.large = true := by
  cases hb : p.toBlockShape.large with
  | true => rfl
  | false =>
    refine absurd ?_ hne
    rw [blockRecElimPin_run h hruns ψ hc]
    simp [ConLeche.structElimLevel, hb, ConLeche.Level.eval]

end Count

/-- **The endpoint's regime premise, from the three regimes.** -/
theorem blockRecPre_dispatch_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    -- the type stage's two facts (`blockRecTy_univ_run`)
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (s ψ) : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c))
    -- the ι equations' GRADING at every typed tuple: NOT a premise of
    -- its own — the rule lane's fold `blockRecHwd_of_rules` produces
    -- it from the per-rule certificates and its three frame premises,
    -- so what the dispatch takes is those four, ψ- and ρ-quantified
    (hcertsW : ∀ (ψ : Name → Nat), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        (ihdoms ψ c j).length
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)
        (ihdoms ψ c j)
        ((Rb0 ψ c j).liftN rs.length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
            + (ihs ψ c j).length))
        (Ca ψ c j))
    (hokA : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length →
      ∀ ys : List V,
        SpineFit (consList as ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).take l)
          ys →
        WellDenoted V (consList ys (consList as ρ))
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).getD l
            default))
    (hlhs : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ ys : List V,
        SpineFit (consList as ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) ys →
        WellDenoted V (consList ys (consList as ρ))
          (AnnotTerm.mkAppN
            (.bvar
              ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
                + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
                + (rs.length - 1 - c)))
            (prefVarsAV (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
                (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
              ++ blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j
              ++ [blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j])))
    (hihsWd : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ ys : List V,
        SpineFit (consList as ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) ys →
        (∀ v ∈ ihs ψ c j, WellDenoted V (consList ys (consList as ρ)) v) ∧
          SpineFit (consList ys (consList as ρ)) (ihdoms ψ c j)
            ((ihs ψ c j).map (interp V (consList ys (consList as ρ)))))
    -- REGIME IND (`ℓ = 0`) — `blockIndRegime_of_run`'s conclusion verbatim
    (hIND : ∀ (ψ : Name → Nat) (ρ : Nat → V), (us.headD .zero).eval ψ = 0 →
      IndRegimeAt V μ rs.length (blockRecNCt rs) p.toBlockShape.rulePrefixAt ψ
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (ihs ψ)
        (fun c j => (Rb0 ψ c j).liftN rs.length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
            + (ihs ψ c j).length)) ρ)
    -- REGIME WF (`ℓ ≠ 0`, `w ≠ 0`) — `blockKitRegime_wf` at the run's components
    (hWF : ∀ (ψ : Name → Nat) (ρ : Nat → V), (us.headD .zero).eval ψ ≠ 0 → d.w ψ ≠ 0 →
      KitRegimeAt V ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
        (blockRecNCt rs) (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
        (ihs ψ) (Rb0 ψ) ρ)
    -- the COUNTING guard's fact — a `Prop` block eliminating at a
    -- non-zero level has ONE member — NOT a premise: `blockRecK1_run`
    -- produces it from the kernel's own guard, and these four are its
    -- inputs (the first three are `blockRecElimLevel_run`'s package
    -- components 1, 2 and 4 verbatim; `hres` is `rfl` at `blockDataOf`)
    (helim : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (hmemU : ∀ c, c < rs.length → uOf c ∈ us)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (hres : d.resSort = p.toBlockShape.resSort)
    -- REGIME SQ (`ℓ ≠ 0`, `w = 0`), at the ONE member the counting guard leaves
    (hSQ : ∀ (ψ : Name → Nat) (ρ : Nat → V), (us.headD .zero).eval ψ ≠ 0 → d.w ψ = 0 →
      KitRegimeAt V ((us.headD .zero).eval ψ) 1 p.toBlockShape.rulePrefixAt
        (blockRecNCt rs) (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ)
        (blockRecMkK 1 mpC.base2.acval envC p.toBlockShape rs ψ)
        (ihs ψ) (Rb0 ψ) ρ) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ')
          Rb0 ψ) ρ := by
  intro ψ ρ
  rw [← blockRecEqs_base (V := V) (ihs := ihs) (Rb0 := Rb0) hμ mpC h ψ]
  refine blockRecPre_run (ℓ := (us.headD .zero).eval ψ)
    (rds := blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
    (concl := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
    (rP := p.toBlockShape.rulePrefixAt) (μ := μ) (ψ := ψ)
    (hTy ψ ρ)
    (blockRecHwd_of_rules (mp := mpC) hμ (hcertsW ψ) (hokA ψ ρ) (hlhs ψ ρ) (hihsWd ψ ρ))
    (hIND ψ ρ) (fun hl => ?_)
  by_cases hw : d.w ψ = 0
  · rw [blockRecK1_run (d := d) h helim hmemU hruns hres ψ hl hw]
    exact hSQ ψ ρ hl hw
  · exact hWF ψ ρ hl hw

end Dispatch


/-! ## 3. THE KIT ARMS, CALLED

§2's `hWF` and `hSQ` are `blockKitRegime_wf`'s and `blockKitRegime_sq`'s
conclusions at the run's components; these two theorems are that
application, so the dispatch's premises are demonstrably inhabited and
what is LEFT of each kit regime is a named list rather than a guess.

**Six premises leave both arms at the run** — `hμ` aside, they are
`hmemK` (`blockRecMajor_run`), `hsplitR` (`blockRecTyShape_run` through
`blockRecSplitAt_of_shape`), `hpdE` (`blockRulePdomsAV`'s definition
and `List.map_take`), `hTyE` (`checkBlockRecK_tyPis`), `hbits`
(`blockRecOneElimLevel` at the NAMED level) and `hpl`
(`blockRulePdomsAV_length`).  `hbits` is the one that could not be paid
before the level was named, and it is paid identically in both arms —
the only premise the three regimes genuinely share.

**The SQ arm additionally needs `rs.length = 1`** and needs it as a
PREMISE (`hK1`): `blockKitRegime_sq` is stated at `K = 1`, and every
run discharge above is indexed by `c < rs.length`, so without the
counting guard's fact the arm cannot even reach its own hypotheses.
That is the composition's sharpest finding: the SQ regime does not
merely happen to be about one-member blocks, it is UNSTATEABLE at the
run without the kernel guard that makes them one-member. -/

section KitArms

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V} {ψ : Name → Nat} {ρ : Nat → V}
  {us : List Level} {uOf : Nat → Level}
  {ihdoms ihs : Nat → Nat → List AnnotTerm} {Rb0 Ca : Nat → Nat → AnnotTerm}
  {ihv : List V → Nat → Nat → List V → V → List V}
  {srcs : Nat → List (Option Nat)}

/-- **REGIME WF at the run** — `blockKitRegime_wf` at §20's components,
with the six run discharges paid. -/
theorem blockKitRegime_wf_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (helim : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (hmemU : ∀ c, c < rs.length → uOf c ∈ us)
    (hbitsE : ∀ c, c < rs.length →
      ∀ b ∈ blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c,
        (b.2.1 = 0 ↔ (uOf c).eval ψ = 0))
    (hM : BlockModelAt mpC.base2 names d)
    (hw : d.w ψ ≠ 0)
    (hnCt : ∀ c, c < rs.length → (d.ctorsM ((p.toBlockShape.recTgtAt) c)).length = (blockRecNCt
      rs) c)
    (hlenIds : ∀ c, c < rs.length → (d.IdsM ((p.toBlockShape.recTgtAt) c) ψ).length = d.nIdxAt
      ((p.toBlockShape.recTgtAt) c))
    (hconclTy : ∀ xs : List V,
        ∀ c, c < rs.length → ∀ i, i ∈ˢ blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC
          p.toBlockShape rs ψ) (p.toBlockShape.recTgtAt) xs c →
        ∀ x, x ∈ˢ app (blockRecCr d ψ ρ (p.toBlockShape.recTgtAt) xs c) i →
        interp V
            (consList (xs ++ (isOfW (d.uM ((p.toBlockShape.recTgtAt) c) ψ) (d.nIdxAt
              ((p.toBlockShape.recTgtAt) c)) i ++ [x])) ρ) ((blockRecConclAV mpC.base2.acval envC
              p.toBlockShape rs ψ) c)
          ∈ˢ (univ ((us.headD .zero).eval ψ) : V))
    (hcerts : ∀ c, c < rs.length → ∀ j, j < (blockRecNCt rs) c →
        BlockRuleCerts V mpC F ψ ((p.toBlockShape.rulePrefixAt) c) ((blockRecFdomsK rs.length
          mpC.base2.acval envC p.toBlockShape rs ψ) c j).length (ihdoms c j).length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) c) ((blockRecFdomsK
            rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j) (ihdoms c j) (Rb0 c j) (Ca c
            j))
    (hspF : ∀ xs : List V, ∀ c, c < rs.length →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs →
        SpineFit ρ ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) c ++
          (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j) (xs ++ fs))
    (hihF : ∀ xs : List V, ∀ c, c < rs.length →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        (∀ v, v ∈ˢ tcPred (unionSet rs.length (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) (p.toBlockShape.recTgtAt) xs)
              (blockRecCr d ψ ρ (p.toBlockShape.recTgtAt) xs))
            (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)) →
          app g v ∈ˢ blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs
            ψ) (fun c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ)
            (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt) c')) ρ xs v) →
        SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < rs.length →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
          = blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (fun
            c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ) (fun c' => d.nIdxAt
            ((p.toBlockShape.recTgtAt) c')) ρ xs
              (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)))
    -- the three rule bridges at the ONE datum the arm builds (RM51)
    (hrule : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2))
          (xs ++ ((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)))
            ++ [interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ))
              (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)])))
    (hctorAt : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
            (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
              (d.Φ ψ (consList (xs.take d.nP) ρ)))
            (d.tup ψ (p.toBlockShape.recTgtAt c)
              ((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)))))
            (p.toBlockShape.recTgtAt c) j fs ∧
          interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ))
              (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)
            = d.inj ψ (p.toBlockShape.recTgtAt c) j fs)
    (hihChain : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        ihv xs c j fs
            (blockWfGraph ((us.headD .zero).eval ψ) rs.length d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
              p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv xs
              (tagged c
                (d.tup ψ (p.toBlockShape.recTgtAt c)
                  ((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                    (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)))))
                (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ))
                  (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j))))
          = (ihs c j).map
              (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)))) :
    KitRegimeAt V ((us.headD .zero).eval ψ) rs.length p.toBlockShape.rulePrefixAt
      (blockRecNCt rs) (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecTyAV mpC.base2.acval envC rs ψ)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ)
      ihs Rb0 ρ := by
  refine blockKitRegime_wf (mo := mpC.base2) (names := names) (d := d) (mp := mpC)
    (ihdoms := ihdoms) (Ca := Ca) (ihv := ihv) (mem := p.toBlockShape.recTgtAt)
    hμ hM hw ?_ hnCt hlenIds ?_ ?_ hconclTy hcerts hspF hihF hCaB ?_ ?_ ?_
    hrule hctorAt hihChain
  · exact fun c hc =>
      (blockRecMajor_run hμ mpC h hmr (List.getElem?_eq_getElem hc) ψ).2.1
  · exact blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ)
  · intro c _
    rw [blockRulePdomsAV, List.map_take]
  · exact fun c hc =>
      (checkBlockRecK_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hc)
        ψ).choose_spec.choose_spec.2.2.1
  · exact blockRecOneElimLevel helim ψ hmemU hbitsE
  · exact fun c hc => blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc) ψ

/-- **REGIME SQ at the run** — `blockKitRegime_sq` at §20's components
at `K = 1`, with the same six discharges, all of them through the
counting guard's `hK1`. -/
theorem blockKitRegime_sq_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hK1 : rs.length = 1)
    (helim : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (hmemU : ∀ c, c < rs.length → uOf c ∈ us)
    (hbitsE : ∀ c, c < rs.length →
      ∀ b ∈ blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c,
        (b.2.1 = 0 ↔ (uOf c).eval ψ = 0))
    (hM : BlockModelAt mpC.base2 names d)
    (hw : d.w ψ = 0)
    (hN : d.N = 1)
    (hmem0 : (p.toBlockShape.recTgtAt) 0 = 0)
    (hnCt1 : ∀ c, c < 1 → (d.ctorsM ((p.toBlockShape.recTgtAt) c)).length ≤ 1)
    (hnCt : ∀ c, c < 1 → (d.ctorsM ((p.toBlockShape.recTgtAt) c)).length = (blockRecNCt rs) c)
    (htgt : ∀ i, d.tgts 0 0 i = 0)
    (hlenIds : ∀ c, c < 1 → (d.IdsM ((p.toBlockShape.recTgtAt) c) ψ).length = d.nIdxAt
      ((p.toBlockShape.recTgtAt) c))
    (hsrcAt : ∀ xs : List V, SpineFit ρ (d.params ψ) (xs.take d.nP) →
        0 < (d.ctorsM 0).length → ∀ X,
        InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ)) X →
        TupleLe d.N (d.idx ψ (consList (xs.take d.nP) ρ)) X
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) →
        ∀ t, t ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) 0 → ∀ fs,
          d.ChainFit ψ (consList (xs.take d.nP) ρ) X t 0 0 fs →
          fs = srcVals (isOfW (d.uM 0 ψ) (d.nIdxAt 0) t) (srcs 0))
    (hconclTy : ∀ xs : List V, ∀ c, c < 1 → ∀ i, i ∈ˢ blockRecIs d ψ ρ (blockRulePdomsAV
      mpC.base2.acval envC p.toBlockShape rs ψ) (p.toBlockShape.recTgtAt) xs c →
        ∀ x, x ∈ˢ app (blockRecCr d ψ ρ (p.toBlockShape.recTgtAt) xs c) i →
        interp V
            (consList (xs ++ (isOfW (d.uM ((p.toBlockShape.recTgtAt) c) ψ) (d.nIdxAt
              ((p.toBlockShape.recTgtAt) c)) i ++ [x])) ρ) ((blockRecConclAV mpC.base2.acval envC
              p.toBlockShape rs ψ) c)
          ∈ˢ (univ ((us.headD .zero).eval ψ) : V))
    (hcerts : ∀ c, c < 1 → ∀ j, j < (blockRecNCt rs) c →
        BlockRuleCerts V mpC F ψ ((p.toBlockShape.rulePrefixAt) c) ((blockRecFdomsK 1
          mpC.base2.acval envC p.toBlockShape rs ψ) c j).length (ihdoms c j).length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) c) ((blockRecFdomsK 1
            mpC.base2.acval envC p.toBlockShape rs ψ) c j) (ihdoms c j) (Rb0 c j) (Ca c j))
    (hspF : ∀ xs : List V, ∀ c, c < 1 →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs →
        SpineFit ρ ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) c ++
          (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ) c j) (xs ++ fs))
    (hihF : ∀ xs : List V, ∀ c, c < 1 →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        (∀ v, v ∈ˢ blockSqPred d ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt) (srcs 0)
              (unionSet 1 (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape
                rs ψ) (p.toBlockShape.recTgtAt) xs) (blockRecCr d ψ ρ (p.toBlockShape.recTgtAt)
                xs))
              (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)) →
          app g v ∈ˢ blockRecMot 1 (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (fun
            c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ)
            (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt) c')) ρ xs v) →
        SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g))
    (hCaB : ∀ xs : List V, ∀ c, c < 1 →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
          = blockRecMot 1 (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (fun c' =>
            d.uM ((p.toBlockShape.recTgtAt) c') ψ) (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt)
            c')) ρ xs
              (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)))
    -- the four rule bridges at the ONE datum the arm builds (RM51)
    (hrule : ∀ c, c < 1 → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame 1 (blockSqCand ((us.headD .zero).eval ψ) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2))
          (xs ++ ((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ((us.headD .zero).eval ψ) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ)))
            ++ [interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ((us.headD .zero).eval ψ) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ))
              (blockRecMkK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)])))
    (hsrcRule : ∀ c, c < 1 → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame 1 (blockSqCand ((us.headD .zero).eval ψ) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        j = 0 ∧
          srcVals
              (isOfW (d.uM (p.toBlockShape.recTgtAt c) ψ) (d.nIdxAt (p.toBlockShape.recTgtAt c))
                (d.tup ψ (p.toBlockShape.recTgtAt c)
                  ((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                    (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ((us.headD .zero).eval ψ) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ))))))
              (srcs c)
            = fs)
    (hihChain : ∀ c, c < 1 → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame 1 (blockSqCand ((us.headD .zero).eval ψ) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        ihv xs c j fs
            (blockSqGraph ((us.headD .zero).eval ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
              p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv xs
              (tagged c
                (d.tup ψ (p.toBlockShape.recTgtAt c)
                  ((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                    (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ((us.headD .zero).eval ψ) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ)))))
                (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ((us.headD .zero).eval ψ) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ))
                  (blockRecMkK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j))))
          = (ihs c j).map
              (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ((us.headD .zero).eval ψ) p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ)))) :
    KitRegimeAt V ((us.headD .zero).eval ψ) 1 p.toBlockShape.rulePrefixAt
      (blockRecNCt rs) (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecTyAV mpC.base2.acval envC rs ψ)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecMkK 1 mpC.base2.acval envC p.toBlockShape rs ψ)
      ihs Rb0 ρ := by
  have hlt : ∀ c, c < 1 → c < rs.length := fun c hc => by rw [hK1]; exact hc
  refine blockKitRegime_sq (mo := mpC.base2) (names := names) (d := d) (mp := mpC)
    (ihdoms := ihdoms) (Ca := Ca) (ihv := ihv) (srcs := srcs)
    (mem := p.toBlockShape.recTgtAt)
    hμ hM hw ?_ hN hmem0 hnCt1 hnCt htgt hlenIds ?_ ?_ hsrcAt hconclTy hcerts hspF hihF hCaB
    ?_ ?_ ?_ hrule hsrcRule hihChain
  · exact fun c hc =>
      (blockRecMajor_run hμ mpC h hmr (List.getElem?_eq_getElem (hlt c hc)) ψ).2.1
  · exact blockRecSplitAt_of_shape (blockRecTyShape_run hμ mpC h hmr hK1 ψ ρ)
  · intro c _
    rw [blockRulePdomsAV, List.map_take]
  · exact fun c hc =>
      (checkBlockRecK_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem (hlt c hc))
        ψ).choose_spec.choose_spec.2.2.1
  · exact blockRecOneElimLevel helim ψ (fun c hc => hmemU c (hlt c hc))
      (fun c hc => hbitsE c (hlt c hc))
  · exact fun c hc =>
      blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem (hlt c hc)) ψ

end KitArms

/-! ## 4. THE SEAM — the regime premise PRODUCED, owing named rows (lane RM51)

`declBlock_run`'s `howed` carried the regime (`hpre`) as a bare
premise, because the dispatch's WF/SQ arms relayed premises quantified
over EVERY family datum (the abstract-field defect, fixed in §19a of
`BlockRecPreRun.lean`) and the SQ arm had no zero-constructor case (it
is stated at `numCtors ≤ 1` now).  With both repaired, `hpre` is
PRODUCED here, from the seam's own facts and four named bundles of
rows, one per regime plus the grading.

**Everything the seam pays is paid here**: the representation and the
members' records (premises: `declBlock_run` produces them), the
elimination-level package (`blockRecElimLevel_run`), the counting
guard's facts (`blockRecCounting_run` — `rs.length = 1`, `d.N = 1`, the
lone member, `numCtors ≤ 1`), the constructor counts
(`checkBlockRecK_ctorsAt`), the members' index arities
(`blockMembers_IdsM_length`), the recursive fields' targets (the
names record) and the parameter telescope's length.

**The level currency is the CHECKED elimination level**
`structElimLevel p.elim p.large`, the one name for the family's level
that exists BEFORE the elimination-level package is unpacked (so the
bundles can be stated in `howed`, which quantifies before any
unpacking).  The dispatch's `(us.headD .zero).eval ψ` is the same number
at every `ψ` (`blockRecHeadLevel_run`: the package's agreement check
and the elimination PIN), and the bundles cross by `subst`.

**What the bundles hold is what the arms still RELAY** — the rows
priced in `RM51-REPORT.md` §2.  Each is stated exactly as its arm
consumes it, with the arm's own auxiliary witnesses (the certificate
family's `ihdoms`/`Ca`, the ih values `ihv`, the source lists `srcs`,
the ih key table) existential at the frame, so a producer chooses them
where they are produced. -/

section Seam

/-- **REGIME WF's owed rows** at one frame, at an elimination level `ℓ`:
`blockKitRegime_wf_run`'s premises that the seam does not pay, with
the arm's own witnesses (`ihdoms`, `Ca`, `ihv`) existential. -/
@[expose] def BlockWfOwed {envC : Env} (mpC : EnvModelM V μ envC) (F : Nat) (p : ConLeche.BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V) (ℓ : Nat)
    (ihs : Nat → Nat → List AnnotTerm) (Rb0 : Nat → Nat → AnnotTerm) : Prop :=
  ∃ (ihdoms : Nat → Nat → List AnnotTerm) (Ca : Nat → Nat → AnnotTerm)
    (ihv : List V → Nat → Nat → List V → V → List V),
    -- `hcerts`
    (∀ c, c < rs.length → ∀ j, j < (blockRecNCt rs) c →
        BlockRuleCerts V mpC F ψ ((p.toBlockShape.rulePrefixAt) c) ((blockRecFdomsK rs.length
          mpC.base2.acval envC p.toBlockShape rs ψ) c j).length (ihdoms c j).length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) c) ((blockRecFdomsK
            rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j) (ihdoms c j) (Rb0 c j) (Ca c
            j)) ∧
    -- `hspF`
    (∀ xs : List V, ∀ c, c < rs.length →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs →
        SpineFit ρ ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) c ++
          (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j) (xs ++ fs)) ∧
    -- `hihF`
    (∀ xs : List V, ∀ c, c < rs.length →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        (∀ v, v ∈ˢ tcPred (unionSet rs.length (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) (p.toBlockShape.recTgtAt) xs)
              (blockRecCr d ψ ρ (p.toBlockShape.recTgtAt) xs))
            (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)) →
          app g v ∈ˢ blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs
            ψ) (fun c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ)
            (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt) c')) ρ xs v) →
        SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g)) ∧
    -- `hCaB`
    (∀ xs : List V, ∀ c, c < rs.length →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
          = blockRecMot rs.length (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (fun
            c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ) (fun c' => d.nIdxAt
            ((p.toBlockShape.recTgtAt) c')) ρ xs
              (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs))) ∧
    -- `hrule`
    (∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2))
          (xs ++ ((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)))
            ++ [interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ))
              (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)]))) ∧
    -- `hihChain`
    (∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        ihv xs c j fs
            (blockWfGraph ℓ rs.length d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
              p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv xs
              (tagged c
                (d.tup ψ (p.toBlockShape.recTgtAt c)
                  ((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                    (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)))))
                (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ))
                  (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j))))
          = (ihs c j).map
              (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ))))

/-- **Regime SQ's source lists** — the subsingleton criterion's, at the
lone constructor's own index readings: the shape `srcVals_of_fit`
produces (`blockChainFit_srcVals_zero`, `blockRuleSrcVals_rule`), so
the seam fixes the arm's `srcs` here and pays `hsrcAt` with it. -/
@[expose] def blockSqSrcs (d : BlockData V) (ψ : Name → Nat) : Nat → List (Option Nat) :=
  fun _ => srcList ((d.Ess 0 ψ).getD 0 []) ((d.Fss 0 ψ).getD 0 []).length

/-- **REGIME SQ's owed rows** at one frame: `blockKitRegime_sq_run`'s
premises the seam does not pay (`hsrcAt` it pays, at `blockSqSrcs`),
witnesses (`ihdoms`, `Ca`, `ihv`) existential. -/
@[expose] def BlockSqOwed {envC : Env} (mpC : EnvModelM V μ envC) (F : Nat) (p : ConLeche.BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V) (ℓ : Nat)
    (ihs : Nat → Nat → List AnnotTerm) (Rb0 : Nat → Nat → AnnotTerm) : Prop :=
  ∃ (ihdoms : Nat → Nat → List AnnotTerm) (Ca : Nat → Nat → AnnotTerm)
    (ihv : List V → Nat → Nat → List V → V → List V),
    -- `hcerts`
    (∀ c, c < 1 → ∀ j, j < (blockRecNCt rs) c →
        BlockRuleCerts V mpC F ψ ((p.toBlockShape.rulePrefixAt) c) ((blockRecFdomsK 1
          mpC.base2.acval envC p.toBlockShape rs ψ) c j).length (ihdoms c j).length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) c) ((blockRecFdomsK 1
            mpC.base2.acval envC p.toBlockShape rs ψ) c j) (ihdoms c j) (Rb0 c j) (Ca c j)) ∧
    -- `hspF`
    (∀ xs : List V, ∀ c, c < 1 →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs →
        SpineFit ρ ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) c ++
          (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ) c j) (xs ++ fs)) ∧
    -- `hihF`
    (∀ xs : List V, ∀ c, c < 1 →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        (∀ v, v ∈ˢ blockSqPred d ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt) ((blockSqSrcs d ψ) 0)
              (unionSet 1 (blockRecIs d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape
                rs ψ) (p.toBlockShape.recTgtAt) xs) (blockRecCr d ψ ρ (p.toBlockShape.recTgtAt)
                xs))
              (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)) →
          app g v ∈ˢ blockRecMot 1 (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (fun
            c' => d.uM ((p.toBlockShape.recTgtAt) c') ψ)
            (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt) c')) ρ xs v) →
        SpineFit (consList (xs ++ fs) ρ) (ihdoms c j) (ihv xs c j fs g)) ∧
    -- `hCaB`
    (∀ xs : List V, ∀ c, c < 1 →
        SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ ((blockRulePdomsAV mpC.base2.acval
          envC p.toBlockShape rs ψ) c) xs →
        ∀ j, j < (blockRecNCt rs) c → ∀ (i : V) (fs : List V),
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
          (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
            (d.Φ ψ (consList (xs.take d.nP) ρ))) i ((p.toBlockShape.recTgtAt) c) j fs → ∀ g : V,
        interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Ca c j)
          = blockRecMot 1 (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (fun c' =>
            d.uM ((p.toBlockShape.recTgtAt) c') ψ) (fun c' => d.nIdxAt ((p.toBlockShape.recTgtAt)
            c')) ρ xs
              (tagged c i (d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs))) ∧
    -- `hrule`
    (∀ c, c < 1 → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2))
          (xs ++ ((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 ihv) ρ)))
            ++ [interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 ihv) ρ))
              (blockRecMkK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)]))) ∧
    -- `hihChain`
    (∀ c, c < 1 → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        ihv xs c j fs
            (blockSqGraph ℓ d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
              p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 ihv xs
              (tagged c
                (d.tup ψ (p.toBlockShape.recTgtAt c)
                  ((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                    (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 ihv) ρ)))))
                (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 ihv) ρ))
                  (blockRecMkK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j))))
          = (ihs c j).map
              (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockSqSrcs d ψ) Rb0 ihv) ρ))))

/-- **REGIME IND's owed rows** at one frame: `blockIndRegime_of_rules`'s
premises the seam does not pay (`hprefU` it pays, `blockRecHpref_run`),
at the dispatch's field domains and lifted residues, with the `ih` key
table existential. -/
@[expose] def BlockIndOwed {envC : Env} (mpC : EnvModelM V μ envC) (F : Nat) (p : ConLeche.BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (ihs : Nat → Nat → List AnnotTerm) (Rb0 : Nat → Nat → AnnotTerm) : Prop :=
  ∃ ihKeys : Nat → Nat → List (Nat × Nat),
    -- `hspF`
    (∀ c, c < rs.length → ∀ as ms is : List V,
      SpineFit ρ (d.params ψ) as →
      SpineFit (consList as ρ)
        ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).drop
          d.nP).take (p.toBlockShape.rulePrefixAt c - d.nP)) ms →
      SpineFit (consList as ρ) (d.IdsM (p.toBlockShape.recTgtAt c) ψ) is →
      ∀ j, j < blockRecNCt rs c → ∀ fs : List V,
      d.ChainFit ψ (consList as ρ)
        (sepTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
          (blockIndP d ψ ρ rs.length p.toBlockShape.rulePrefixAt p.toBlockShape.recTgtAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) as))
        (d.tup ψ (p.toBlockShape.recTgtAt c) is) (p.toBlockShape.recTgtAt c) j fs →
      SpineFit ρ
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j)
        (as ++ ms ++ fs)) ∧
    -- `hrule`
    (∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∃ (ihdoms : List AnnotTerm) (Ca : AnnotTerm),
        BlockIndRuleAt mpC F p rs d ψ ρ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ) ihs
          (fun c j => (Rb0 c j).liftN rs.length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
            + (ihs c j).length)) ihKeys c j ihdoms Ca)

/-- **The ι equations' GRADING inputs** — the dispatch's four
`blockRecHwd_of_rules` premises, with the certificate family's `Ca`
existential and its `ihdoms` PINNED (lane RM53) to the rule's own
openers' domains at the chain frame (`blockRecIhdomsK`).

The fourth premise (`hihsWd`) is owed in two halves: the `ih` terms'
grading, and their FIT — which is stated at the BASE frame, in the
exact spelling of `declBlock_run`'s typed-tuple `ih` fit
(`BlockIhFitTypedOwed`), so the two are ONE fact with one producer
(`blockIhFitTyped_run`); the seam carries it to the chain frame
(`blockRecIhsFit_chain`). -/
@[expose] def BlockGradeOwed {envC : Env} (mpC : EnvModelM V μ envC) (F : Nat)
    (p : ConLeche.BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm) : Prop :=
  ∃ (Ca : (Name → Nat) → Nat → Nat → AnnotTerm),
    -- `hcertsW`
    (∀ (ψ : Name → Nat), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j).length
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)
        (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j)
        ((Rb0 ψ c j).liftN rs.length
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
            + (ihs ψ c j).length))
        (Ca ψ c j)) ∧
    -- `hokA`
    (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length →
      ∀ ys : List V,
        SpineFit (consList as ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).take l)
          ys →
        WellDenoted V (consList ys (consList as ρ))
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).getD l
            default)) ∧
    -- `hlhs`
    (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ ys : List V,
        SpineFit (consList as ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) ys →
        WellDenoted V (consList ys (consList as ρ))
          (AnnotTerm.mkAppN
            (.bvar
              ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
                + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
                + (rs.length - 1 - c)))
            (prefVarsAV (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
                (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
              ++ blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j
              ++ [blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j]))) ∧
    -- `hihsWd`, first half: the `ih` terms are graded
    (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ ys : List V,
        SpineFit (consList as ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) ys →
        ∀ v ∈ ihs ψ c j, WellDenoted V (consList ys (consList as ρ)) v) ∧
    -- `hihsWd`, second half: the typed tuple's `ih` FIT, at the BASE frame
    -- (`BlockIhFitTypedOwed`'s spelling; `blockIhFitTyped_run` produces it)
    (∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c → ∀ ys : List V,
        SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
        SpineFit (consList ys ρ) (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j)
          ((ihs ψ c j).map (interp V (consList ys (consList tup ρ)))))

section SeamFacts

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}

omit [SetTheory V] in
/-- **The family is non-empty and has one recursor per member** — the
pins and the counting pass's first clause. -/
theorem blockRecLen_run
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    0 < rs.length ∧ rs.length = p.toBlockShape.k := by
  obtain ⟨hpins, cvRus, -, hsmall, -⟩ := checkBlockRecK_count h
  obtain ⟨-, -, -, hlenR, -⟩ := checkBlockRecK_elimList h
  obtain ⟨hk0, -⟩ := ConLeche.checkBlockRecSmallElim_inv hsmall
  have hklen : rs.length = p.toBlockShape.k := by
    rw [hlenR, (ConLeche.checkBlockRecPins_names hpins).1]; rfl
  exact ⟨by rw [hklen]; exact hk0, hklen⟩

omit [SetTheory V] in
/-- **The dispatch's level IS the checked elimination level**, at every
valuation: the package's agreement check puts every conclusion sort at
the head's value, and the elimination pin puts each at the checked
level. -/
theorem blockRecHeadLevel_run {us : List Level} {uOf : Nat → Level}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (helim : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (hmemU : ∀ c, c < rs.length → uOf c ∈ us)
    (hruns : ∀ c, c < rs.length → ∃ (fvs : List Expr) (conclE sty : Expr),
      ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          (rs.getD c default).1.type 0 = some (fvs, conclE) ∧
        ConLeche.inferTypeCore μ envC F (p.toBlockShape.majorIdxAt c + 1) conclE = .ok sty ∧
        ConLeche.ensureSortCore μ envC F (p.toBlockShape.majorIdxAt c + 1) sty = .ok (uOf c))
    (ψ : Name → Nat) :
    (us.headD .zero).eval ψ
      = Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) := by
  have hpos := (blockRecLen_run h).1
  rw [← blockRecElimAgree_eval helim ψ (uOf 0) (hmemU 0 hpos), blockRecElimPin_run h hruns ψ hpos]

omit [SetTheory V] in
/-- A member's constructors are among the block's. -/
theorem numCtorsOf_ge_of_mem {ms : ConLeche.MemberShape} :
    ∀ {l : List ConLeche.MemberShape}, ms ∈ l → ms.ctors.length ≤ ConLeche.numCtorsOf l
  | _ :: _, .head _ => by simp only [ConLeche.numCtorsOf]; omega
  | _ :: _, .tail _ h => by
    simp only [ConLeche.numCtorsOf]; have := numCtorsOf_ge_of_mem h; omega

/-- **The constructor counts at the seam**: at the run's own block data
a recursor's member carries exactly the recursor's rules. -/
theorem blockRecNCt_seam {env₀ : Env} {pk : Nat → BlockMemberPick}
    {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∀ c, c < rs.length →
      ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
          (p.toBlockShape.recTgtAt c)).length = blockRecNCt rs c ∧
        ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
          (p.toBlockShape.recTgtAt c)).length ≤ p.toBlockShape.numCtors := by
  intro c hc
  obtain ⟨ms, hms, hctA, hlenms⟩ := checkBlockRecK_ctorsAt h (List.getElem?_eq_getElem hc)
  have hctM : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c) = rs[c].2.2.2 := by
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  refine ⟨?_, ?_⟩
  · rw [hctM, blockRecNCt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]; rfl
  · rw [hctM, hlenms]
    exact numCtorsOf_ge_of_mem (List.mem_of_getElem? hms)

end SeamFacts

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-! ### The rule's own spine, peeled to the constructor's datum (RM53)

The kit arms' rule bridges (`hsrcRule`, `hctorAt`) all start from the
same antecedent: a spine `x⃗ ++ f⃗` fitting the rule's prefix and field
domains at SOME chain frame.  Everything they need from it is here, at
once: the constructor the rule names (the SAME `cA` in the recursor's
rule list and in the member's constructor list), its record, the
prefix fit at the BASE frame (the `K` lift of a closed telescope is the
identity, §28), the parameter fit (`blockRecParams_run`), the field
spine at the chain frame and at the parameter frame (§23's transport),
and the two syntactic identities `hes`/`hfd`.

The rule's right-hand side, which `blockRuleEsAV_eq` and
`blockRuleFdomsAV_datum` both name, exists because the kinds cover the
constructors (`hkLen`, `checkBlockRecK_rulesLen`) — the one fact the
seam did not have before RM53. -/

/-- **The rule's spine at a chain frame, peeled.** -/
theorem blockRuleSpine_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {j : Nat} (hj : j < blockRecNCt rs c)
    {ψ : Name → Nat} {K : Nat} {a ρ : Nat → V} {xs fs : List V}
    (hxs : xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length)
    (hsp : SpineFit (chainFrame K a ρ)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs)) :
    ∃ (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs ∧
      (d.ctorsM (p.toBlockShape.recTgtAt c))[j]? = some cA ∧
      BlockCtorFacts mpC.base2 d p.lps (p.toBlockShape.recTgtAt c) j cA ∧
      p.toBlockShape.recTgtAt c < d.k ∧
      p.nP ≤ p.toBlockShape.rulePrefixAt c ∧
      xs.length = p.toBlockShape.rulePrefixAt c ∧ fs.length = cA.2 ∧
      ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = cA.2 ∧
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs ∧
      SpineFit ρ (d.params ψ) (xs.take d.nP) ∧
      SpineFit (consList xs (chainFrame K a ρ))
        (liftDomsK K (p.toBlockShape.rulePrefixAt c)
          (liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0
            ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []))) fs ∧
      SpineFit (consList (xs.take d.nP) ρ)
        ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []) fs ∧
      blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
        = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
            (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2) ∧
      blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
        = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0
            ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []) := by
  have hcl : c < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  -- the constructor the rule names, and its right-hand side
  have hjr : j < r.2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, r.2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  have hcj : (d.ctorsM (p.toBlockShape.recTgtAt c))[j]? = some cA := by
    rw [hctM c r hr]; exact hcA
  have hmemk : p.toBlockShape.recTgtAt c < d.k :=
    (blockRecMajor_run (V := V) hμ mpC h hmr hr (fun _ => 0)).2.1
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  obtain ⟨-, -, hcd⟩ := hcore.2.2.1 _ j cA hcj
  have hCf : cA.1.type.hasFvar = false :=
    (mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)).1
  obtain ⟨_, _, _, _, _, _, _, -, -, hnP, -⟩ := checkBlockRecK_tyMajor h hr
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hxs' : xs.length = p.toBlockShape.rulePrefixAt c := by rw [hxs, hpl]
  have hfd := blockRuleFdomsAV_datum h hr hcA hrhs hcore hmemk hcj hnP hdnP ψ
  have hcd' := hcd
  rw [hdnP] at hcd'
  have hes : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
          (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2) := by
    rw [blockRuleEsAV_eq h hr hcA hrhs hcd' hCf hnP ψ, hdnP]
    exact congrArg (List.map _) (essOfR_fixCtorDataList_getD hcj).symm
  have hnF : ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = cA.2 := by
    have hFssD : (d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []
        = ((d.dsF (p.toBlockShape.recTgtAt c) j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hcd.len ψ]
    omega
  -- the split
  obtain ⟨xs₁, fs₁, heq, h1, h2⟩ := spineFit_append_split hsp
  have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hxs]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
  -- the prefix, at the base frame
  have hpre : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs := by
    rw [← blockRecPdomsK_run hμ mpC h hr ψ K, blockRecPdomsK] at h1
    exact (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) _ [] xs).mp h1
  -- the parameters
  have hps : SpineFit ρ (d.params ψ) (xs.take d.nP) := by
    have ht := spineFit_take hpre (i := d.nP) (by rw [hpl, hdnP]; exact hnP)
    have hte : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take d.nP
        = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).take d.nP := by
      rw [blockRulePdomsAV, List.map_take, List.take_take,
        Nat.min_eq_left (by rw [hdnP]; exact hnP)]
    rw [hte] at ht
    exact (blockRecParams_run hμ mpC h hmr hr ψ ρ _).mp ht
  -- the fields
  have h2' : SpineFit (consList xs (chainFrame K a ρ))
      (liftDomsK K (p.toBlockShape.rulePrefixAt c)
        (liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0
          ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []))) fs := by
    rw [blockRecFdomsK, hpl, hfd] at h2; exact h2
  have hfb := (spineFit_liftDomsK_rule (nP := d.nP) hxs').mp h2'
  exact ⟨cA, rhs, hcA, hrhs, hcj, ⟨hfindC, hlpsC, hcd⟩, hmemk, hnP, hxs',
    by rw [hfb.length_eq, hnF], hnF, hpre, hps, h2', hfb, hes, hfd⟩

/-- **REGIME WF's `hctorAt`, at the run** — at ANY chain frame (the
arm's is `chainFrame K (blockWfCand …) ρ`, and nothing here reads the
candidate).  The fit half is §25's `blockRecCtorFitsFrom_of`, the index
half §26's `blockRecCtorIdx`, the fired spine §22's
`blockRecMkK_value`; `blockRuleSpine_run` hands all three their
inputs. -/
theorem blockWfCtorAt_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (hN : BlockNamesOk (V := V) d cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) (K : Nat) (a ρ : Nat → V) :
    ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ xs fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame K a ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) →
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
            (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
              (d.Φ ψ (consList (xs.take d.nP) ρ)))
            (d.tup ψ (p.toBlockShape.recTgtAt c)
              ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                (interp V (consList (xs ++ fs) (chainFrame K a ρ)))))
            (p.toBlockShape.recTgtAt c) j fs ∧
          interp V (consList (xs ++ fs) (chainFrame K a ρ))
              (blockRecMkK K mpC.base2.acval envC p.toBlockShape rs ψ c j)
            = d.inj ψ (p.toBlockShape.recTgtAt c) j fs := by
  intro c hc j hj xs fs hxs hsp
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfs, hnF, -, hps, -, hfb, hes, hfd⟩ :=
    blockRuleSpine_run hμ h hkLen hcore hmr hdnP hctM (List.getElem?_eq_getElem hc) hj hxs hsp
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hmN : p.toBlockShape.recTgtAt c < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : j < (d.ctorsM (p.toBlockShape.recTgtAt c)).length :=
    (List.getElem?_eq_some_iff.mp hcj).1
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [hfd, liftDomsK_length, hnF]
  have hasLen : (xs.take d.nP).length = d.nP := by
    rw [List.length_take, hxs']; rw [hdnP]; exact Nat.min_eq_left hnP
  have hsat : Sat V (d.params ψ).reverse (consList (xs.take d.nP) ρ) := d.satOfSpine hps
  have hres := hM.resIdxFit ψ _ hsat _ hmN j hjl fs hfb
  have ht : tupW (d.uM (p.toBlockShape.recTgtAt c) ψ)
        (((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
          (interp V (consList fs (consList (xs.take d.nP) ρ))))
      ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt c) := tupW_mem hres
  have hspK : SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [blockRecPdomsK_run hμ mpC h hr ψ K]; exact hsp
  have hxsK : xs.length = (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c).length := by
    rw [blockRecPdomsK_run hμ mpC h hr ψ K]; exact hxs
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact blockRecCtorFitsFrom_of (mem := p.toBlockShape.recTgtAt) hM hμ h hr hcj hcf hfd hasLen
      hps (fun l _ => by rw [← hN.2.2.2]; exact hN.2.1 _ j l) hmN hjl ht
      (lfpTuple_mem _ _ _ _) hxsK hspK
  · exact blockRecCtorIdx (mem := p.toBlockShape.recTgtAt) hM hes hpl hfl hxs' hfs hmN hjl hps hfb
  · exact blockRecMkK_value (mem := p.toBlockShape.recTgtAt) hM h hr hcA hrhs hcf.1
      (by rw [← hcf.2.1]; rfl) hnP hmN hcj ψ hxs' hfs
      (by rw [hpl, hfl, hxs', hfs]) (by rw [← hdnP]; exact hps) (by rw [← hdnP]; exact hfb)

/-- **REGIME SQ's `hsrcRule`, at the run** — at ANY chain frame.  The
counting guard's `numCtors ≤ 1` names the constructor (`j = 0`), and
§2b's criterion at the rule's own spine (`blockRuleSrcVals_rule`) is
the rest, with `blockRuleSpine_run` handing it the field spine, the
parameter fit and `es`'s spelling. -/
theorem blockSqSrcRule_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (h0 : 0 < rs.length) (hmem0 : p.toBlockShape.recTgtAt 0 = 0)
    (hct1 : (d.ctorsM (p.toBlockShape.recTgtAt 0)).length ≤ 1)
    (hlarge : d.large = true) (ψ : Name → Nat) (hw : d.w ψ = 0) (K : Nat) (a ρ : Nat → V) :
    ∀ c, c < 1 → ∀ j, j < blockRecNCt rs c →
      ∀ xs fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame K a ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) →
        j = 0 ∧
          srcVals
              (isOfW (d.uM (p.toBlockShape.recTgtAt c) ψ) (d.nIdxAt (p.toBlockShape.recTgtAt c))
                (d.tup ψ (p.toBlockShape.recTgtAt c)
                  ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
                    (interp V (consList (xs ++ fs) (chainFrame K a ρ))))))
              (blockSqSrcs d ψ c)
            = fs := by
  intro c hc j hj xs fs hxs hsp
  obtain rfl : c = 0 := by omega
  have hr : rs[0]? = some rs[0] := List.getElem?_eq_getElem h0
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfs, hnF, -, hps, hfit, -, hes, hfd⟩ :=
    blockRuleSpine_run hμ h hkLen hcore hmr hdnP hctM hr hj hxs hsp
  have hjl : j < (d.ctorsM (p.toBlockShape.recTgtAt 0)).length :=
    (List.getElem?_eq_some_iff.mp hcj).1
  obtain rfl : j = 0 := by omega
  refine ⟨rfl, ?_⟩
  have hmN : p.toBlockShape.recTgtAt 0 < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hk0 : 0 < d.k := Nat.lt_of_le_of_lt (Nat.zero_le _) hmemk
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ 0).length
      = p.toBlockShape.rulePrefixAt 0 := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ 0 0).length = cA.2 := by
    rw [hfd, liftDomsK_length, hnF]
  have hsrcs : blockSqSrcs d ψ 0
      = srcList ((d.Ess (p.toBlockShape.recTgtAt 0) ψ).getD 0 [])
          ((d.Fss (p.toBlockShape.recTgtAt 0) ψ).getD 0 []).length := by
    rw [hmem0]; rfl
  rw [hsrcs]
  refine blockRuleSrcVals_rule hM hcj hcf hlarge hw
    (fun σ => ⟨fun hσ => ((hS.frames _ hmemk 0 cA hcj).1 ψ σ).mp
        (hS.paramsOf 0 hk0 ψ σ hσ _ hmemk),
      fun hσ => hS.paramsOf _ hmemk ψ σ (((hS.frames _ hmemk 0 cA hcj).1 ψ σ).mpr hσ) 0 hk0⟩)
    (blockMembers_IdsM_length hmr hmemk ψ) hmN hjl hxs' ?_ hps hfit
  rw [blockRecEsK, hes, List.map_map, hpl, hfl]
  rfl

/-- **The family's level `s`, CHOSEN — with both facts it owes.**
`s` is the max of the check's inferred sorts (`blockRecTy_univ_run`)
read at the level assignment RESTRICTED to the family's level
parameters (zero elsewhere).  So `s`'s parametricity — `heqP`'s `s`
half, owed by whoever fixes `s` — is definitional: two assignments that
agree on the family's parameters restrict to the same one.  The typing
`hTy` survives the restriction because the recursor types' READINGS are
themselves parametric (`blockRecTyAV_params_ext`: every recursor carries
the family's one parameter list).  No level-footprint fact about the
inferred sorts is needed. -/
theorem blockRecLevel_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∃ s : (Name → Nat) → Nat,
      (∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
        rs[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
          (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
        interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (s ψ) : V) ∧
          WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) := by
  obtain ⟨us, hus⟩ := blockRecTy_univ_run (V := V) hμ mpC h
  let lps := (rs.getD 0 default).1.levelParams
  let res : (Name → Nat) → Name → Nat := fun ψ q => if q ∈ lps then ψ q else 0
  refine ⟨fun ψ => maxLevelEval us (res ψ), fun i r hr ψ₁ ψ₂ hq => ?_, fun ψ ρ c hc => ?_⟩
  · have hi : i < rs.length := (List.getElem?_eq_some_iff.mp hr).1
    have hr0 : rs[0]? = some (rs.getD 0 default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hl : lps = r.1.levelParams := checkBlockRecK_lps h hr0 hr
    have hres : res ψ₁ = res ψ₂ := by
      funext q
      by_cases hqm : q ∈ lps
      · show (if q ∈ lps then ψ₁ q else 0) = (if q ∈ lps then ψ₂ q else 0)
        rw [if_pos hqm, if_pos hqm]
        exact hq q (hl ▸ hqm)
      · show (if q ∈ lps then ψ₁ q else 0) = (if q ∈ lps then ψ₂ q else 0)
        rw [if_neg hqm, if_neg hqm]
    show maxLevelEval us (res ψ₁) = maxLevelEval us (res ψ₂)
    rw [hres]
  · have hr0 : rs[0]? = some (rs.getD 0 default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hext := blockRecTyAV_params_ext (V := V) hμ mpC h hr0 (ψ₁ := ψ) (ψ₂ := res ψ)
      (fun q hqm => by show ψ q = if q ∈ lps then ψ q else 0; rw [if_pos hqm]) hc
    refine ⟨?_, (hus ψ c hc ρ).2⟩
    rw [hext]
    exact (hus (res ψ) c hc ρ).1

/-- A tuple of the family's length IS the chain frame's block. -/
theorem consList_eq_chainFrame' {K : Nat} {tup : List V} (hlen : tup.length = K) (ρ : Nat → V) :
    consList tup ρ = chainFrame K (fun c => tup.getD c pt) ρ := by
  have hmap : (List.range K).map (fun c => tup.getD c pt) = tup := by
    refine List.ext_getElem? fun n => ?_
    rw [List.getElem?_map]
    by_cases hn : n < K
    · rw [List.getElem?_range hn, List.getElem?_eq_getElem (by omega : n < tup.length)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : n < tup.length)]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
      rfl
  rw [chainFrame, hmap]

/-- **The typed tuple's `ih` fit, carried to the chain frame** — the
dispatch's `hihsWd` second half from `BlockGradeOwed`'s base-frame
spelling: the prefix domains are closed (§28), the field domains and
the pinned `ihdoms` are the base ones lifted past the `K` chain binders
at the rule frame's depth (`spineFit_liftDomsK`). -/
theorem blockRecIhsFit_chain (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    {ψ : Name → Nat} {ρ : Nat → V} {as : List V} (hlen : as.length = rs.length)
    {c j : Nat} (hc : c < rs.length) {ihs : List AnnotTerm}
    (hF : ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
      SpineFit (consList ys ρ) (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j)
        (ihs.map (interp V (consList ys (consList as ρ))))) :
    ∀ ys : List V,
      SpineFit (consList as ρ)
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) ys →
      SpineFit (consList ys (consList as ρ))
        (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j)
        (ihs.map (interp V (consList ys (consList as ρ)))) := by
  intro ys hys
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hch := consList_eq_chainFrame' (V := V) hlen ρ
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  have hxl : xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length :=
    hxs.length_eq
  -- the prefix: its `K` lift is the identity
  have hxs0 : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs := by
    rw [hch, ← blockRecPdomsK_run hμ mpC h hr ψ rs.length, blockRecPdomsK] at hxs
    exact (spineFit_liftDomsK (K := rs.length) (ρ := ρ) _ [] xs).mp hxs
  -- the fields: the base domains lifted past the chain
  have hfs0 : SpineFit (consList xs ρ)
      (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) fs := by
    rw [hch, blockRecFdomsK, ← hxl] at hfs
    exact (spineFit_liftDomsK (K := rs.length) (ρ := ρ) _ xs fs).mp hfs
  have hq := hF (xs ++ fs) (SpineFit.append hxs0 hfs0)
  have hyl : (xs ++ fs).length
      = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length := by
    rw [List.length_append, hxl, hfs0.length_eq]
  rw [hch, blockRecIhdomsK, ← hyl]
  rw [hch] at hq
  exact (spineFit_liftDomsK (K := rs.length) (ρ := ρ) _ (xs ++ fs) _).mpr hq

/-- **THE REGIME AT THE SEAM** — `blockRecPre_dispatch_run` with its
three arms CALLED (`blockIndRegime_of_rules`, `blockKitRegime_wf_run`,
`blockKitRegime_sq_run`) and every premise the seam can pay paid.  Its
conclusion is `declBlock_data`'s regime conjunct verbatim.

Paid here beyond the counting facts: the IND arm's `hprefU` (the
family's shared prefix, `blockRecHpref_run`) and the SQ arm's `hsrcAt`
(the subsingleton criterion, `blockChainFit_srcVals_zero`, at the
constructors' records — which is why the seam takes `hS`/`hcore`).

What it owes is named: the family level's typing `hTy` at the chosen
`s` (`blockRecTy_univ_run` produces it at `s := maxLevelEval us`), the
grading bundle and one bundle per regime, each at the CHECKED
elimination level. -/
theorem blockRecPre_seam (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    -- the kinds cover the constructors: every rule has its right-hand side
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {s : (Name → Nat) → Nat} {ihs : (Name → Nat) → Nat → Nat → List AnnotTerm}
    {Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm}
    -- OWED: the family level's typing, at the chosen `s`
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < rs.length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) ∈ˢ (univ (s ψ) : V) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c))
    -- OWED: the ι equations' grading inputs
    (hG : BlockGradeOwed mpC F p rs ihs Rb0)
    -- OWED: the three regimes' rows, at the checked elimination level
    (hI : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0 →
      BlockIndOwed mpC F p rs d ψ ρ (ihs ψ) (Rb0 ψ))
    (hW : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w ψ ≠ 0 →
      BlockWfOwed mpC F p rs d ψ ρ
        (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
        (ihs ψ) (Rb0 ψ))
    (hSq : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) ≠ 0 →
      d.w ψ = 0 →
      BlockSqOwed mpC F p rs d ψ ρ
        (Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large))
        (ihs ψ) (Rb0 ψ)) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) rs.length
        (blockRecTyAV mpC.base2.acval envC rs ψ)
        (blockRecEqs (blockRecNCt rs) rs
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ')
          (fun ψ' => blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          (fun ψ' => blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ')
          Rb0 ψ) ρ := by
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  obtain ⟨us, uOf, helim, hmemU, hbitsE, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hℓeq := blockRecHeadLevel_run h helim hmemU hruns
  obtain ⟨hpos, hklen⟩ := blockRecLen_run h
  have hnCtS := blockRecNCt_seam (V := V) (env₀ := env₀) (pk := pk) (uOfD := uOfD)
    (ppsOf := ppsOf) h
  have hmemk : ∀ c, c < rs.length → p.toBlockShape.recTgtAt c
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k := fun c hc =>
    (blockRecMajor_run (V := V) hμ mpC h hmr (List.getElem?_eq_getElem hc) (fun _ => 0)).2.1
  have hk0 : 0 < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) (hmemk 0 hpos)
  have hlenIds : ∀ (ψ : Name → Nat) m,
      m < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k →
      ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).IdsM m ψ).length
        = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nIdxAt m :=
    fun ψ m hm => blockMembers_IdsM_length hmr hm ψ
  have hlenP : ∀ ψ : Name → Nat,
      ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).params ψ).length
        = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP := by
    intro ψ
    have hl := hS.lenPps 0 ψ hk0
    rw [BlockData.params, List.length_map, List.length_take]
    exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hl.symm))
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  obtain ⟨CaG, hcertsW, hokA, hlhs, hihsWd1, hihsFit⟩ := hG
  refine blockRecPre_dispatch_run (us := us) (uOf := uOf)
    (ihdoms := fun ψ => blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ) (Ca := CaG)
    (d := blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    hμ h hTy hcertsW hokA hlhs
    (fun ψ ρ as hl ht c hc j hj ys hys => ⟨hihsWd1 ψ ρ as hl ht c hc j hj ys hys,
      blockRecIhsFit_chain hμ h hl hc (hihsFit ψ ρ as hl ht c hc j hj) ys hys⟩)
    ?_ ?_ helim hmemU hruns rfl ?_
  -- REGIME IND
  · intro ψ ρ hℓ0
    obtain ⟨ihKeys, hspF, hrule⟩ := hI ψ ρ (by rw [← hℓeq ψ]; exact hℓ0)
    exact blockIndRegime_of_rules (ihKeys := ihKeys) hμ h hM hmr (fun c hc => (hnCtS c hc).1)
      (hlenP ψ) helim hmemU (hbitsE ψ) hℓ0 hspF
      (fun c hc c' hc' _ hfit => blockRecHpref_run hμ mpC h ψ (List.getElem?_eq_getElem hc)
        (List.getElem?_eq_getElem hc') hfit)
      hrule
  -- REGIME WF
  · intro ψ ρ hℓ hw
    have hW' := hW ψ ρ (by rw [← hℓeq ψ]; exact hℓ) hw
    rw [← hℓeq ψ] at hW'
    obtain ⟨ihdoms, Ca, ihv, hcerts, hspF, hihF, hCaB, hrule, hihChain⟩ := hW'
    have hconclTy := blockRecConclTy_run hμ mpC h hmr hM helim hmemU hruns ψ ρ
    exact blockKitRegime_wf_run (ihdoms := ihdoms) (Ca := Ca) (ihv := ihv) hμ h hmr helim hmemU
      (hbitsE ψ) hM hw (fun c hc => (hnCtS c hc).1) (fun c hc => hlenIds ψ _ (hmemk c hc))
      hconclTy hcerts hspF hihF hCaB hrule
      (blockWfCtorAt_run hμ h hkLen hcore hmr hM hN rfl hctM ψ _ _ ρ) hihChain
  -- REGIME SQ, at the one member the counting guard leaves
  · intro ψ ρ hℓ hw
    have hSq' := hSq ψ ρ (by rw [← hℓeq ψ]; exact hℓ) hw
    rw [← hℓeq ψ] at hSq'
    have hconclTy := blockRecConclTy_run hμ mpC h hmr hM helim hmemU hruns ψ ρ
    obtain ⟨ihdoms, Ca, ihv, hcerts, hspF, hihF, hCaB, hrule, hihChain⟩ := hSq'
    obtain ⟨-, -, hlarge, hk1, -, hnc⟩ := blockRecCounting_run h helim hmemU hruns ψ hℓ hw
    have hK1 : rs.length = 1 := by rw [hklen, hk1]
    have hlt : ∀ c, c < 1 → c < rs.length := fun c hc => by rw [hK1]; exact hc
    have hk1d : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k = 1 := hk1
    have hmem0 : p.toBlockShape.recTgtAt 0 = 0 := by
      have := hmemk 0 hpos; omega
    refine blockKitRegime_sq_run (ihdoms := ihdoms) (Ca := Ca) (ihv := ihv)
      (srcs := blockSqSrcs _ ψ)
      hμ h hmr hK1 helim hmemU (hbitsE ψ) hM hw ?_ hmem0
      (fun c hc => Nat.le_trans (hnCtS c (hlt c hc)).2 hnc)
      (fun c hc => (hnCtS c (hlt c hc)).1) ?_ (fun c hc => hlenIds ψ _ (hmemk c (hlt c hc)))
      ?_ (fun xs c hc => hconclTy xs c (hlt c hc)) hcerts hspF hihF hCaB hrule
      (blockSqSrcRule_run hμ h hkLen hS hcore hmr hM rfl hctM hpos hmem0
        (Nat.le_trans (hnCtS 0 hpos).2 hnc) hlarge ψ hw 1 _ ρ)
      hihChain
    · show (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k + 0 = 1
      rw [hk1d]
    · intro i
      have := hN.2.1 0 0 i
      rw [hN.2.2.2, hk1d] at this
      omega
    -- `hsrcAt`: the subsingleton criterion, at the lone constructor
    · intro xs hps hct X hX hle t ht fs hfit
      obtain ⟨cA, hcj⟩ : ∃ cA,
          ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM 0)[0]?
            = some cA := ⟨_, List.getElem?_eq_getElem hct⟩
      obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 0 hk0 0 cA hcj
      obtain ⟨-, -, hcd⟩ := hcore.2.2.1 0 0 cA hcj
      refine blockChainFit_srcVals_zero hM hcj ⟨hfindC, hlpsC, hcd⟩ hlarge hw
        (fun σ => ⟨fun hσ => ((hS.frames 0 hk0 0 cA hcj).1 ψ σ).mp
            (hS.paramsOf 0 hk0 ψ σ hσ 0 hk0),
          fun hσ => hS.paramsOf 0 hk0 ψ σ (((hS.frames 0 hk0 0 cA hcj).1 ψ σ).mpr hσ) 0 hk0⟩)
        (hlenIds ψ 0 hk0) (by rw [hps.length_eq, hlenP ψ]) hps
        (fun l _ => by have := hN.2.1 0 0 l; rwa [hN.2.2.2] at this)
        (by show 0 < _ + 0; omega) hct hX hle ht hfit

end Seam

end ConLeche.Model
