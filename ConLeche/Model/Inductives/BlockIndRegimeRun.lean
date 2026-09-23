module

public import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun

public section

/-!
# The IND regime, at the run (task #315, M5M-rule)

`blockIndRegime_run` (`BlockRecPreRun.lean`) is the dispatch's
`ℓ = 0` arm: it turns the block's own induction, the rules'
certificates and the regime's two chain-frame premises into
`IndRegimeAt`.  Until this file it was never APPLIED — and it is the
hinge of the whole arm's `ℓ = 0` half, so twelve landed theorems
across two lanes had no consumer for want of it.

Two pieces:

* **§1 the CROSSING.**  `hihOpen` is stated in the BLOCK datum's
  currency (`d.Fss`, `d.tlss`, `d.Eiss`, `d.IdsM`, `mem c`, `rP c`)
  and the run produces it in the rule FRAME's
  (`fr.nF`, `fr.teleOf`, `fr.idxOf`, `fr.ihKeys`, the callee's stored
  type).  `blockIhOpen_key_of` is that crossing, at one key: half A's
  three block facts (`BlockRecTyShapeRun.lean`) decide what the KEY
  says, and `blockIhOpenerDom_run`'s fused reading supplies the peel,
  the tower and the domain equation.  Every identification it needs is
  a premise, because each one is a different lane's fact;
* **§2 the COMPOSITION.**  `blockIndRegime_of_run` applies
  `blockIndRegime_run` with everything the run already produces
  discharged: the recursor type's shape (`blockRecTyShape_run`), the
  binder bits (`blockRecOneElimLevel`), the Π-tower identification and
  the conclusion's boundedness (`checkBlockRecK_tyPis`,
  `checkBlockRecK_tyBounds`), and `hihOpen` through §1.

**The premises that stay open are the motive facts** (`hCaE`,
`hihTy`, the `ih` fit at every typed tuple — lane RM55: it was `hihReg`, the fit at the POINT tuple, which needs the arm's own induction to know the point tuple is typed, so no producer outside the arm) and the rule lanes'.  `hjoinC` is GONE: the arm states its
induction motive at the SPLIT data now, so nothing here assembles a
recursor spine and the index clause's converse has no consumer left.

The `univZero` family — §40.14's `hT`, `hTStep`, `hTReg` and the `ih`
segment's `h0` — is ONE premise `hCaZ` now, and §2d DISCHARGES it.
The derivation that did not survive the motive's move was the one
through `hCaE`: `blockRecConclUnivZero_run` licenses the truth value
only at a fitting spine of the RECURSOR's own binder data, and the
split data does not carry one (its index values fit the MEMBER's
telescope, and carrying them to the recursor's index binders is
exactly the deleted converse).  **The licence the family actually has
is the RULE's**: `checkBlockRule` types the residue against the
recursor's type Π-instantiated at the rule's own spine, so the
certificates already carry a `peelPis` of that tower and a
`TeleFitPA` of it at the SAME spine — a fit of the recursor's binder
data at the FIRED spine, produced by the rule's typing run and not
assembled from anything.

No `w` hypothesis: every statement below is a READING, a peel or a
key's own filter fact, never a membership in the block's carrier
(the settled criterion, and the `w ≠ 0` ruling's own blast radius).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)
open ConLeche (BlockFieldKind blockIhKeys blockTgtsOf)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. THE CROSSING — `hihOpen` at ONE key

`blockIndRegime_run`'s `hihOpen` quantifies over `(c, j, r)` and
produces eight existential witnesses and thirteen conjuncts.  Eleven
of the thirteen are the KEY's own (half A, `BlockRecTyShapeRun.lean`
§7) or are `rfl` at the witnesses this theorem chooses; the two that
carry content are the callee's peel and the opener's domain, and both
come out of the ONE fused reading `blockIhOpenerDom_run`.

The premises are grouped by who owns them:

* the block datum's tables at this constructor (`hcj`, `hcf`, `hmr`,
  `hksF`, `hksLen`, `hFssLen`, `htgtsF`, `hrecTgtsLen`, `hrecTgts`,
  `hmemK`) — the install's;
* the frame's widths and the callees' prefixes (`hnF`, `hrPs`, `hb`)
  — the recursor stage's;
* the callee recursor types' readings (`hRecTy`) — §21's;
* the openers' slot and their fused reading (`hfvsIh`, `hslot`,
  `hdom`) — this lane's, `readOpenedDoms_reads` and
  `blockIhOpenerDom_run`.

`hb` is the generated tower's binder BIT (`pwBit ψ fr.pw`), which
`hihOpen` asks at `0`: the `ih` binders of a recursor whose motive
lives at level `0` are `Prop` binders.  It is a premise because the
datum is the CHECK's (`BlockRuleFrame.pw`) and the identification
`pwBit ψ fr.pw = 0` at the IND regime is the stage's, not this
module's. -/

/-! ### 1b. `hihOpen` ASSEMBLED — the same crossing at every key

`blockIndRegime_run`'s `hihOpen` quantifies over the rule `c`, the
constructor `j` and the opener position `r`; §1 is its body at one
key.  The per-`(c, j)` data the crossing needs is EXISTENTIAL at the
run — each rule's frame is produced by that rule's own run, and the
field kinds, the constructor, the `ih` openers and the tower's bit
come out of it together — so it is one premise, `hframe`, and not
thirteen indexed families.  `hmr`, `hrecTgts`, `hmemK`, `hrPs` and
`hRecTy` are BLOCK-wide and stay outside it.

The `ihKeys` identification is inside `hframe` too: the regime reads
its keys off a POSITION in its own `ihKeys c j`, and what the check
generates is `blockIhKeys` at the rule's prefix, the block's prefixes
and targets and the constructor's kinds. -/

/-! ## 2. THE COMPOSITION — `blockIndRegime_run` APPLIED

`IndRegimeAt` at the run, in `blockRecPre_hpre`'s own spelling
(`RecTy := blockRecTyAV`, `pdoms := blockRulePdomsAV`,
`nCt := blockRecNCt rs`, `rP := p.toBlockShape.rulePrefixAt`).

**Six of the nineteen premises are discharged here** against the run
and cost nothing else:

| premise | producer |
|---|---|
| `hmemK` | `blockRecMajor_run` (the major's member is in range) |
| `hshape` | `blockRecTyShape_run` |
| `hbits` | `blockRecOneElimLevel`, at the family's shared level |
| `hTyE` | `checkBlockRecK_tyPis` (O-2's Π-tower identification) |
| `hpdE` | `blockRulePdomsAV`'s own definition — `(l.take n).map f` is `(l.map f).take n`, so this is `List.map_take` and nothing else |
| `hconclB` | `checkBlockRecK_tyBounds` |

**The elimination level is the composition's one surprise.**  `hbits`
asks for `OneElimLevel 0`, and the run's producer
(`blockRecOneElimLevel_run`) hands the level back EXISTENTIALLY —
`∃ ℓ, OneElimLevel ℓ …` — while the dispatch's guard (`hIND`'s
`ℓ ψ = 0`) names the caller's OWN `ℓ`.  The two meet only if the
level is named, so this theorem takes `blockRecElimLevel_run`'s three
outputs (`helim`, `hmem`, `hbitsE`) and the guard in the RUN's
currency: `(us.headD .zero).eval ψ = 0`, the sort the type stage read
off the first recursor's conclusion.  That is what the `ℓ = 0` arm
means at the run, and it is not derivable inside the regime.

**What stays a premise, and whose it is.**  `hCaZ` — §40.14's four
`univZero` facts in ONE frame-generic statement — is the certificate
lane's, and §2d produces it from the rule's own peel and tower fit.
`hlenP` — the block's parameter telescope
has `nP` entries — is the block records', carried as a premise all
over this tree rather than stored in `BlockData`.  `hcerts`, `hspF`,
`hihLen` and `hprefU` are the rule lanes', and `hihOpen` is §1b's.
`hcerts` in particular is NOT discharged here even though
`blockRuleCerts_of_run` exists: that theorem is stated at ONE rule and
ONE constructor with the `ih` opening `fvsIh` existential, and
`IndRegimeAt` wants one `ihdoms` family for all of them — the
skolemisation is the rule lane's to pay, at the frame where `fvsIh`
is produced, not here. -/
theorem blockIndRegime_of_run {envC : Env} {mpC : EnvModelM V μ envC}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {names : List Name} {d : BlockData V} {ψ : Name → Nat} {ρ : Nat → V}
    {us : List Level} {uOf : Nat → Level}
    {fdoms ihdoms ihs : Nat → Nat → List AnnotTerm} {Rb Ca : Nat → Nat → AnnotTerm}
    {ihKeys : Nat → Nat → List (Nat × Nat)}
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hM : BlockModelAt mpC.base2 names d)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hnCt : ∀ c, c < rs.length →
      (d.ctorsM (p.toBlockShape.recTgtAt c)).length = blockRecNCt rs c)
    (hlenP : (d.params ψ).length = d.nP)
    -- the family's elimination level, NAMED, and the arm's guard at it
    (helim : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (hmemU : ∀ c, c < rs.length → uOf c ∈ us)
    (hbitsE : ∀ c, c < rs.length →
      ∀ b ∈ blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c,
        (b.2.1 = 0 ↔ (uOf c).eval ψ = 0))
    (hℓ : (us.headD .zero).eval ψ = 0)
    -- the certificate lane's two open premises
    (hCaZ : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ (σ : Nat → V) (xs fs vs : List V),
      SpineFit σ
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c ++ fdoms c j)
        (xs ++ fs) →
      SpineFit (consList (xs ++ fs) σ) (ihdoms c j) vs →
      interp V (consList vs (consList (xs ++ fs) σ)) (Ca c j) ∈ˢ (univZero : V))
    (hCaE : ∀ c, c < rs.length → ∀ (as ms is : List V) (x : V),
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
      x = d.inj ψ (p.toBlockShape.recTgtAt c) j fs →
      interp V
          (consList (List.replicate (ihdoms c j).length (pt : V))
            (consList (as ++ ms ++ fs) ρ)) (Ca c j)
        = interp V (consList (as ++ ms ++ is ++ [x]) ρ)
            (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c))
    (hihTy : ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length → as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c → ∀ ys : List V,
        SpineFit (consList as ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c ++ fdoms c j) ys →
        SpineFit (consList ys (consList as ρ)) (ihdoms c j)
          ((ihs c j).map (interp V (consList ys (consList as ρ)))))
    -- the rule lanes'
    (hcerts : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c) (fdoms c j).length
        (ihdoms c j).length (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (fdoms c j) (ihdoms c j) (Rb c j) (Ca c j))
    (hspF : ∀ c, c < rs.length → ∀ as ms is : List V,
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
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c ++ fdoms c j)
        (as ++ ms ++ fs))
    (hihLen : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      (ihdoms c j).length = (ihKeys c j).length)
    (hprefU : ∀ c, c < rs.length → ∀ c', c' < rs.length → ∀ xs : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c') xs)
    -- §1b's
    (hihOpen : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ r, r < (ihKeys c j).length →
      ∃ (i c' nF nIdx m : Nat) (eisA : List AnnotTerm) (fapA CihR : AnnotTerm),
        ((ihKeys c j).getD r (0, 0)).1 = i ∧
        ((ihKeys c j).getD r (0, 0)).2 = c' ∧
        c' < rs.length ∧
        i < ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length ∧
        ((d.rss (p.toBlockShape.recTgtAt c)).getD j []).getD i false = true ∧
        d.tgts (p.toBlockShape.recTgtAt c) j i = p.toBlockShape.recTgtAt c' ∧
        ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = nF ∧
        (((d.tlss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i []).length = m ∧
        (((d.Eiss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i []).length = nIdx ∧
        (d.IdsM (p.toBlockShape.recTgtAt c') ψ).length = nIdx ∧
        eisA = (((d.Eiss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i []).map
            (ihIdxAtM nF (p.toBlockShape.rulePrefixAt c - d.nP) i 0 m) ∧
        fapA = AnnotTerm.mkAppN (.bvar (nF - 1 - i + m)) (teleVarsAV m) ∧
        BlockRuleConclAt (p.toBlockShape.rulePrefixAt c') nF m
          (blockRecTyAV mpC.base2.acval envC rs ψ c') eisA fapA CihR ∧
        (ihdoms c j).getD r default
          = (mkPisAV (ihTeleAtR nF (p.toBlockShape.rulePrefixAt c - d.nP) i 0
              (rebit 0 (((d.tlss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i [])))
              CihR).liftN r 0) :
    IndRegimeAt V μ rs.length (blockRecNCt rs) p.toBlockShape.rulePrefixAt ψ
      (blockRecTyAV mpC.base2.acval envC rs ψ)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) fdoms ihs Rb ρ := by
  have hbits : OneElimLevel 0 rs.length
      (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) := by
    rw [← hℓ]
    exact blockRecOneElimLevel helim ψ hmemU hbitsE
  refine blockIndRegime_run (mo := mpC.base2) (names := names) (d := d) (mp := mpC)
    (ihdoms := ihdoms) (Ca := Ca) (ihKeys := ihKeys)
    (concl := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ)
    hμ hM ?_ hlenP hnCt (blockRecTyShape_run hμ mpC h hmr rfl ψ ρ) hbits ?_ hcerts hspF
    hihLen ?_ hprefU ?_ hihOpen hCaZ hCaE hihTy
  · intro c hc
    obtain ⟨r, hr⟩ : ∃ r, rs[c]? = some r := ⟨rs[c]'hc, List.getElem?_eq_getElem hc⟩
    exact (blockRecMajor_run (V := V) hμ mpC h hmr hr ψ).2.1
  · intro c hc
    obtain ⟨r, hr⟩ : ∃ r, rs[c]? = some r := ⟨rs[c]'hc, List.getElem?_eq_getElem hc⟩
    exact (checkBlockRecK_tyPis (V := V) hμ mpC h hr ψ).choose_spec.choose_spec.2.2.1
  · intro c _
    rw [blockRulePdomsAV, List.map_take]
  · intro c hc
    obtain ⟨r, hr⟩ : ∃ r, rs[c]? = some r := ⟨rs[c]'hc, List.getElem?_eq_getElem hc⟩
    exact (checkBlockRecK_tyBounds (V := V) hμ mpC h hr ψ).2

/-! ### 2b. The two halves joined

§1b and §2 at ONE instantiation: `hihOpen` is no longer a premise, and
the callee recursor types are the run's own stored ones
(`blockRuleRecTy`), so `hRecTy` and `hmemK` are discharged too.  What
is left is exactly the list §2's docstring names — the certificate
lane's four `univZero` facts, the rule lanes' `hcerts`, `hspF`,
`hihLen`, `hprefU`, the block-wide key tables and the per-rule
frame. -/

/-! ### 2c. `hframe`'s reading conjunct, from the rule's own run

`hframe`'s last conjunct is `blockIhOpenerDom_run`
(`BlockRecTyShapeRun.lean`) at the BLOCK's rows — the field telescopes
and index readings taken as `d.tlss`/`d.Eiss` rather than as free
functions of the field index, which is legitimate because
`blockFieldReadAt_of` (`BlockFieldRead.lean`) proves `FieldReadAt` at
exactly those rows (`(d.tlss mm ψ).getD j [] = d.tssF mm j ψ`).

What this theorem adds is the FRAME IDENTIFICATION list, and that is
its point: the crossing needs the rule frame's four widths and its key
list to be the block's, and the generated tower's bit to be zero.
Each is the recursor/rule stage's own fact and none of them is
derivable here:

* `hnP`/`hrPf`/`hnFf` — the frame's parameter count, rule prefix and
  field count are the block's `d.nP`, the recursor's
  `rulePrefixAt c` and the constructor's `cA.2`;
* `hkeysf` — the frame's `ihKeys` is the regime's;
* `hpw` — `pwBit ψ fr.pw = 0`, the `ih` binders of a recursor whose
  motive lives at level `0`.  This is the ONE place the IND regime's
  guard reaches into the generated tower, and it is the stage's to
  pay: `BlockRuleFrame.pw` is the check's elimination datum. -/

/-! ### 2d. `hCaZ` DISCHARGED — the family's one premise, at the run

`blockIndRegime_of_run`'s `hCaZ` is the whole of what §40.14 called
four premises (`hT`, `hTStep`, `hTReg` and the `ih` segment's `h0`):
one frame-generic statement, at the rule's certificates' own two fits.
This is its producer, block-wide.

**What it costs the rule lane is nothing new.**  The per-rule datum
below — a spine `vs` of the recursor type's own length, the syntactic
peel `peelPis RecTy vs = some (Ca c j)`, and a `TeleFitPA` of the SAME
tower at the SAME `vs` at every frame satisfying the rule's context —
is `blockRuleCerts_of_run`'s `hpeel`/`hfit` pair verbatim, the pair
`hokC` already consumes.  `vs` is existential per rule for the same
reason `ihdoms` and `Ca` are: it comes out of `checkBlockRule_data`
at that rule's own openings.

**And the licence is the RULE's, not the split's** — which is why the
motive's move to the split data costs the arm nothing here: the fit
this reads is a fit of the recursor's binder data at the FIRED spine,
produced by the rule's own typing run, and no index clause is
inverted to get it. -/

/-! ## 3. THE SKOLEMISATION — `ihdoms` and `Ca` per RULE, not per BLOCK

**This is where §2 stops, and the reason is structural.**
`IndRegimeAt` (and `blockIndRegime_run` under it) wants ONE
`ihdoms : Nat → Nat → List AnnotTerm` and ONE `Ca` for the whole
block, and six of its premises are stated at them.  The RUN produces
neither: `blockRuleCerts_of_run` is stated at one rule and one
constructor, its `ihdoms` is `readOpenedDoms` at THAT rule's own `ih`
opening `fvsIh`, and both that opening and the conclusion `Ca` come
out of `checkBlockRule_data` existentially.  So the certificate lane
cannot hand §2 a family without first choosing one, and choosing one
is not its work.

It is this section's.  `BlockIndRuleAt` is the six `ihdoms`/`Ca`-dependent
premises at ONE pair, and they have to travel together: every one of
them mentions the same two witnesses, so splitting the bundle would
mean six independent choices of what must be one pair.

The cost is `Classical.choice`, which the arm already pays inside
`blockIndRegime_run` (`spineFit_ihdoms_zero` wants one conclusion
function for all the keys while the opener reading is existential per
key).  The guard-free total form is the same `by_cases`-then-choose. -/

/-- **One rule's `ℓ = 0` obligation at ONE (recursor, constructor)
pair**, at that rule's own `ih` domains and conclusion: the
certificates, the opener count, the fused opener reading and the four
`univZero`/motive facts.

The three motive facts are at the SPLIT data — the parameters, the
middle stretch and the member's own index values, each with its own
fit, written out in that order — because that is what the run has; a
recursor-spine fit cannot be rebuilt from them and nothing here tries
to. -/
@[expose] def BlockIndRuleAt {envC : Env} (mpC : EnvModelM V μ envC) (F : Nat)
    (p : ConLeche.BlockParts)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (d : BlockData V) (ψ : Name → Nat) (ρ : Nat → V)
    (fdoms ihs : Nat → Nat → List AnnotTerm) (Rb : Nat → Nat → AnnotTerm)
    (ihKeys : Nat → Nat → List (Nat × Nat)) (c j : Nat)
    (ihdoms : List AnnotTerm) (Ca : AnnotTerm) : Prop :=
  BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c) (fdoms c j).length
      ihdoms.length (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
      (fdoms c j) ihdoms (Rb c j) Ca ∧
  ihdoms.length = (ihKeys c j).length ∧
  (∀ r, r < (ihKeys c j).length →
    ∃ (i c' nF nIdx m : Nat) (eisA : List AnnotTerm) (fapA CihR : AnnotTerm),
      ((ihKeys c j).getD r (0, 0)).1 = i ∧
      ((ihKeys c j).getD r (0, 0)).2 = c' ∧
      c' < rs.length ∧
      i < ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length ∧
      ((d.rss (p.toBlockShape.recTgtAt c)).getD j []).getD i false = true ∧
      d.tgts (p.toBlockShape.recTgtAt c) j i = p.toBlockShape.recTgtAt c' ∧
      ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = nF ∧
      (((d.tlss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i []).length = m ∧
      (((d.Eiss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i []).length = nIdx ∧
      (d.IdsM (p.toBlockShape.recTgtAt c') ψ).length = nIdx ∧
      eisA = (((d.Eiss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i []).map
          (ihIdxAtM nF (p.toBlockShape.rulePrefixAt c - d.nP) i 0 m) ∧
      fapA = AnnotTerm.mkAppN (.bvar (nF - 1 - i + m)) (teleVarsAV m) ∧
      BlockRuleConclAt (p.toBlockShape.rulePrefixAt c') nF m
        (blockRecTyAV mpC.base2.acval envC rs ψ c') eisA fapA CihR ∧
      ihdoms.getD r default
        = (mkPisAV (ihTeleAtR nF (p.toBlockShape.rulePrefixAt c - d.nP) i 0
            (rebit 0 (((d.tlss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i [])))
            CihR).liftN r 0) ∧
  (∀ (σ : Nat → V) (xs fs vs : List V),
    SpineFit σ
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c ++ fdoms c j)
      (xs ++ fs) →
    SpineFit (consList (xs ++ fs) σ) ihdoms vs →
    interp V (consList vs (consList (xs ++ fs) σ)) Ca ∈ˢ (univZero : V)) ∧
  (∀ (as ms is : List V) (x : V),
    SpineFit ρ (d.params ψ) as →
    SpineFit (consList as ρ)
      ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).drop
        d.nP).take (p.toBlockShape.rulePrefixAt c - d.nP)) ms →
    SpineFit (consList as ρ) (d.IdsM (p.toBlockShape.recTgtAt c) ψ) is →
    ∀ fs : List V,
    d.ChainFit ψ (consList as ρ)
      (sepTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
        (blockIndP d ψ ρ rs.length p.toBlockShape.rulePrefixAt p.toBlockShape.recTgtAt
          (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
          (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) as))
      (d.tup ψ (p.toBlockShape.recTgtAt c) is) (p.toBlockShape.recTgtAt c) j fs →
    x = d.inj ψ (p.toBlockShape.recTgtAt c) j fs →
    interp V
        (consList (List.replicate ihdoms.length (pt : V))
          (consList (as ++ ms ++ fs) ρ)) Ca
      = interp V (consList (as ++ ms ++ is ++ [x]) ρ)
          (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)) ∧
  (∀ as : List V, as.length = rs.length →
    (∀ c', c' < rs.length →
      as.getD c' pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c')) →
    ∀ ys : List V,
      SpineFit (consList as ρ)
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c ++ fdoms c j) ys →
      SpineFit (consList ys (consList as ρ)) ihdoms
        ((ihs c j).map (interp V (consList ys (consList as ρ)))))

/-- **`IndRegimeAt` from the PER-RULE bundles** — §2 with the `ih`
domains and the rule conclusions chosen, so the certificate lane never
has to build a family. -/
theorem blockIndRegime_of_rules {envC : Env} {mpC : EnvModelM V μ envC}
    {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {names : List Name} {d : BlockData V} {ψ : Name → Nat} {ρ : Nat → V}
    {us : List Level} {uOf : Nat → Level}
    {fdoms ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm}
    {ihKeys : Nat → Nat → List (Nat × Nat)}
    (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hM : BlockModelAt mpC.base2 names d)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hnCt : ∀ c, c < rs.length →
      (d.ctorsM (p.toBlockShape.recTgtAt c)).length = blockRecNCt rs c)
    (hlenP : (d.params ψ).length = d.nP)
    (helim : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (hmemU : ∀ c, c < rs.length → uOf c ∈ us)
    (hbitsE : ∀ c, c < rs.length →
      ∀ b ∈ blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c,
        (b.2.1 = 0 ↔ (uOf c).eval ψ = 0))
    (hℓ : (us.headD .zero).eval ψ = 0)
    (hspF : ∀ c, c < rs.length → ∀ as ms is : List V,
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
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c ++ fdoms c j)
        (as ++ ms ++ fs))
    (hprefU : ∀ c, c < rs.length → ∀ c', c' < rs.length → ∀ xs : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c') xs)
    (hrule : ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∃ (ihdoms : List AnnotTerm) (Ca : AnnotTerm),
        BlockIndRuleAt mpC F p rs d ψ ρ fdoms ihs Rb ihKeys c j ihdoms Ca) :
    IndRegimeAt V μ rs.length (blockRecNCt rs) p.toBlockShape.rulePrefixAt ψ
      (blockRecTyAV mpC.base2.acval envC rs ψ)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ) fdoms ihs Rb ρ := by
  -- the guarded bundle, made TOTAL so that ONE choice covers every pair
  have htot : ∀ c j : Nat, ∃ P : List AnnotTerm × AnnotTerm,
      c < rs.length → j < blockRecNCt rs c →
      BlockIndRuleAt mpC F p rs d ψ ρ fdoms ihs Rb ihKeys c j P.1 P.2 := by
    intro c j
    by_cases hc : c < rs.length
    · by_cases hj : j < blockRecNCt rs c
      · obtain ⟨A, B, hA⟩ := hrule c hc j hj
        exact ⟨(A, B), fun _ _ => hA⟩
      · exact ⟨default, fun _ hj' => absurd hj' hj⟩
    · exact ⟨default, fun hc' _ => absurd hc' hc⟩
  exact blockIndRegime_of_run (ihdoms := fun c j => (htot c j).choose.1)
    (Ca := fun c j => (htot c j).choose.2)
    hμ h hM hmr hnCt hlenP helim hmemU hbitsE hℓ
    (fun c hc j hj σ xs fs vs => ((htot c j).choose_spec hc hj).2.2.2.1 σ xs fs vs)
    (fun c hc as ms is x has hms his j hj fs hf =>
      ((htot c j).choose_spec hc hj).2.2.2.2.1 as ms is x has hms his fs hf)
    (fun as hl ht c hc j hj ys => ((htot c j).choose_spec hc hj).2.2.2.2.2 as hl ht ys)
    (fun c hc j hj => ((htot c j).choose_spec hc hj).1)
    hspF
    (fun c hc j hj => ((htot c j).choose_spec hc hj).2.1)
    hprefU
    (fun c hc j hj => ((htot c j).choose_spec hc hj).2.2.1)
