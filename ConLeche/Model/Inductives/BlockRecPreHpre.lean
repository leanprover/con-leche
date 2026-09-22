module

public import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
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
    (hrule : ∀ (D : RecFamData V ((us.headD .zero).eval ψ) rs.length (p.toBlockShape.rulePrefixAt)
      (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockRecConclAV mpC.base2.acval
      envC p.toBlockShape rs ψ) ρ), ∀ c, c < rs.length → ∀ j, j < (blockRecNCt rs) c →
        ∀ xs fs : List V, xs.length = ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          c).length →
        SpineFit (chainFrame rs.length (famCand D) ρ) ((blockRulePdomsAV mpC.base2.acval envC
          p.toBlockShape rs ψ) c ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape
          rs ψ) c j) (xs ++ fs) →
        SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) c).map (·.2.2))
          (xs ++ (((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j).map
            (interp V (consList (xs ++ fs) (chainFrame rs.length (famCand D) ρ)))
            ++ [interp V (consList (xs ++ fs) (chainFrame rs.length (famCand D) ρ)) ((blockRecMkK
              rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j)])))
    (hctorAt : ∀ (D : RecFamData V ((us.headD .zero).eval ψ) rs.length
      (p.toBlockShape.rulePrefixAt) (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) ρ), ∀ c, c < rs.length → ∀ j, j <
      (blockRecNCt rs) c →
        ∀ xs fs : List V, xs.length = ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          c).length →
        SpineFit (chainFrame rs.length (famCand D) ρ) ((blockRulePdomsAV mpC.base2.acval envC
          p.toBlockShape rs ψ) c ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape
          rs ψ) c j) (xs ++ fs) →
        d.ChainFit ψ (consList (xs.take d.nP) ρ)
            (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
              (d.Φ ψ (consList (xs.take d.nP) ρ)))
            (d.tup ψ ((p.toBlockShape.recTgtAt) c)
              (((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j).map (interp
                V (consList (xs ++ fs) (chainFrame rs.length (famCand D) ρ)))))
            ((p.toBlockShape.recTgtAt) c) j fs ∧
          interp V (consList (xs ++ fs) (chainFrame rs.length (famCand D) ρ)) ((blockRecMkK
            rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j)
            = d.inj ψ ((p.toBlockShape.recTgtAt) c) j fs)
    (hihChain : ∀ (D : RecFamData V ((us.headD .zero).eval ψ) rs.length
      (p.toBlockShape.rulePrefixAt) (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
      (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) ρ), ∀ c, c < rs.length → ∀ j, j <
      (blockRecNCt rs) c →
        ∀ xs fs : List V, xs.length = ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          c).length →
        SpineFit (chainFrame rs.length (famCand D) ρ) ((blockRulePdomsAV mpC.base2.acval envC
          p.toBlockShape rs ψ) c ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape
          rs ψ) c j) (xs ++ fs) →
        ihv xs c j fs
            (kitGraphAt (D.kit xs)
              (tagged c
                (D.tupOf c
                  (((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j).map
                    (interp V (consList (xs ++ fs) (chainFrame rs.length (famCand D) ρ)))))
                (interp V (consList (xs ++ fs) (chainFrame rs.length (famCand D) ρ)) ((blockRecMkK
                  rs.length mpC.base2.acval envC p.toBlockShape rs ψ) c j))))
          = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame rs.length (famCand D) ρ)))) :
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
    (hnCt1 : ∀ c, c < 1 → (d.ctorsM ((p.toBlockShape.recTgtAt) c)).length = 1)
    (hnCt : ∀ c, c < 1 → (blockRecNCt rs) c = 1)
    (htgt : ∀ i, d.tgts 0 0 i = 0)
    (hlenIds : ∀ c, c < 1 → (d.IdsM ((p.toBlockShape.recTgtAt) c) ψ).length = d.nIdxAt
      ((p.toBlockShape.recTgtAt) c))
    (hsrcAt : ∀ xs : List V, ∀ X,
        InTupleSpace (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ)) X →
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
    (hrule : ∀ (D : RecFamData V ((us.headD .zero).eval ψ) 1 (p.toBlockShape.rulePrefixAt)
      (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockRecConclAV mpC.base2.acval
      envC p.toBlockShape rs ψ) ρ), ∀ c, c < 1 → ∀ j, j < (blockRecNCt rs) c →
        ∀ xs fs : List V, xs.length = ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          c).length →
        SpineFit (chainFrame 1 (famCand D) ρ) ((blockRulePdomsAV mpC.base2.acval envC
          p.toBlockShape rs ψ) c ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ) c
          j) (xs ++ fs) →
        SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) c).map (·.2.2))
          (xs ++ (((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ) c j).map (interp V
            (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)))
            ++ [interp V (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)) ((blockRecMkK 1
              mpC.base2.acval envC p.toBlockShape rs ψ) c j)])))
    (hsrcRule : ∀ (D : RecFamData V ((us.headD .zero).eval ψ) 1 (p.toBlockShape.rulePrefixAt)
      (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockRecConclAV mpC.base2.acval
      envC p.toBlockShape rs ψ) ρ), ∀ c, c < 1 → ∀ j, j < (blockRecNCt rs) c →
        ∀ xs fs : List V, xs.length = ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          c).length →
        SpineFit (chainFrame 1 (famCand D) ρ) ((blockRulePdomsAV mpC.base2.acval envC
          p.toBlockShape rs ψ) c ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ) c
          j) (xs ++ fs) →
        j = 0 ∧
          srcVals
              (isOfW (d.uM ((p.toBlockShape.recTgtAt) c) ψ) (d.nIdxAt ((p.toBlockShape.recTgtAt)
                c))
                (D.tupOf c
                  (((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ) c j).map (interp V
                    (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ))))))
              (srcs c)
            = fs)
    (hihChain : ∀ (D : RecFamData V ((us.headD .zero).eval ψ) 1 (p.toBlockShape.rulePrefixAt)
      (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) (blockRecConclAV mpC.base2.acval
      envC p.toBlockShape rs ψ) ρ), ∀ c, c < 1 → ∀ j, j < (blockRecNCt rs) c →
        ∀ xs fs : List V, xs.length = ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          c).length →
        SpineFit (chainFrame 1 (famCand D) ρ) ((blockRulePdomsAV mpC.base2.acval envC
          p.toBlockShape rs ψ) c ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ) c
          j) (xs ++ fs) →
        ihv xs c j fs
            (kitGraphAt (D.kit xs)
              (tagged c
                (D.tupOf c
                  (((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ) c j).map (interp V
                    (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)))))
                (interp V (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)) ((blockRecMkK 1
                  mpC.base2.acval envC p.toBlockShape rs ψ) c j))))
          = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame 1 (famCand D) ρ)))) :
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

end ConLeche.Model
