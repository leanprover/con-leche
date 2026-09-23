module

public import ConLeche.Model.Inductives.BlockRecPreRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun

public section

/-!
# The IND regime, at the run

`blockIndRegime_run` (`BlockRecPreRun.lean`) is the dispatch's
`ℓ = 0` arm: it turns the block's own induction, the rules'
certificates and the regime's two chain-frame premises into
`IndRegimeAt`.  This file applies it at the run:

* **§2 the COMPOSITION.**  `blockIndRegime_of_run` applies
  `blockIndRegime_run` with everything the run already produces
  discharged: the recursor type's shape (`blockRecTyShape_run`), the
  binder bits (`blockRecOneElimLevel`), the Π-tower identification and
  the conclusion's boundedness (`checkBlockRecK_tyPis`,
  `checkBlockRecK_tyBounds`).
* **§3 the SKOLEMISATION.**  `blockIndRegime_of_rules` chooses the `ih`
  domains and rule conclusions per rule, so the certificates never have
  to be built as a block-wide family.

**The premises that stay open are the motive facts** (`hCaE`, `hihTy`,
the `ih` fit at every typed tuple — not only at the POINT tuple, whose
typedness needs the arm's own induction, so has no producer outside the
arm) and the rules'.  The arm states its induction motive at the SPLIT
data (parameters, middle stretch, the member's own index values, each
with its own fit), so nothing here assembles a recursor spine.

`hCaZ` is the `univZero` family in ONE frame-generic statement.  Its
licence is the RULE's, not the split data's: `blockRecConclUnivZero_run`
licenses the truth value only at a fitting spine of the RECURSOR's own
binder data, which the split data does not carry (its index values fit
the MEMBER's telescope); but `checkBlockRule` types the residue against
the recursor's type Π-instantiated at the rule's own spine, so the
certificates carry a `peelPis` of that tower and a `TeleFitPA` of it at
the SAME spine — a fit at the FIRED spine, produced by the rule's typing
run.

No `w` hypothesis: every statement below is a READING, a peel or a
key's own filter fact, never a membership in the block's carrier.
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

/-! ## 2. THE COMPOSITION — `blockIndRegime_run` APPLIED

`IndRegimeAt` at the run, in the run's own spelling
(`RecTy := blockRecTyAV`, `pdoms := blockRulePdomsAV`,
`nCt := blockRecNCt rs`, `rP := p.toBlockShape.rulePrefixAt`).

**Six of the nineteen premises are discharged here** against the run
and cost nothing else:

| premise | producer |
|---|---|
| `hmemK` | `blockRecMajor_run` (the major's member is in range) |
| `hshape` | `blockRecTyShape_run` |
| `hbits` | `blockRecOneElimLevel`, at the family's shared level |
| `hTyE` | `checkBlockRecK_tyPis` (the Π-tower identification) |
| `hpdE` | `blockRulePdomsAV`'s own definition — `(l.take n).map f` is `(l.map f).take n`, so this is `List.map_take` and nothing else |
| `hconclB` | `checkBlockRecK_tyBounds` |

**The elimination level is NAMED.**  `hbits` asks for
`OneElimLevel 0`, and the dispatch's guard (`hIND`'s `ℓ ψ = 0`) names
the caller's OWN `ℓ`; an existentially produced level would not meet
it.  So this theorem takes `blockRecElimLevel_run`'s three
outputs (`helim`, `hmem`, `hbitsE`) and the guard in the RUN's
currency: `(us.headD .zero).eval ψ = 0`, the sort the type stage read
off the first recursor's conclusion.  That is what the `ℓ = 0` arm
means at the run, and it is not derivable inside the regime.

**What stays a premise.**  `hCaZ` — the four `univZero` facts in ONE
frame-generic statement — comes from the rule's own peel and tower fit.
`hlenP` — the block's parameter telescope has `nP` entries — is the
block records', carried as a premise rather than stored in `BlockData`.
`hcerts`, `hspF`, `hihLen` and `hprefU` are the rules', and `hihOpen`
is the `ih` openers' crossing.  `hcerts` is NOT discharged here even
though `blockRuleCerts_of_run` exists: that theorem is stated at ONE
rule and ONE constructor with the `ih` opening `fvsIh` existential,
and `IndRegimeAt` wants one `ihdoms` family for all of them — §3's
skolemisation. -/
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
    (helim : ∀ u ∈ us, Level.isEquiv u (ConLeche.structElimLevel p.elim p.large) = some true)
    (hmemU : ∀ c, c < rs.length → uOf c ∈ us)
    (hbitsE : ∀ c, c < rs.length →
      ∀ b ∈ blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c,
        (b.2.1 = 0 ↔ (uOf c).eval ψ = 0))
    (hℓ : (us.headD .zero).eval ψ = 0)
    -- the certificates' two open premises
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
    -- the rules'
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
    -- the `ih` openers' crossing
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

/-! ## 3. THE SKOLEMISATION — `ihdoms` and `Ca` per RULE, not per BLOCK

`IndRegimeAt` (and `blockIndRegime_run` under it) wants ONE
`ihdoms : Nat → Nat → List AnnotTerm` and ONE `Ca` for the whole
block, and six of its premises are stated at them.  The RUN produces
neither: `blockRuleCerts_of_run` is stated at one rule and one
constructor, its `ihdoms` is `readOpenedDoms` at THAT rule's own `ih`
opening `fvsIh`, and both that opening and the conclusion `Ca` come
out of the rule record (`RuleRun`) existentially.  So a family must be
chosen, and this section chooses it.

`BlockIndRuleAt` is the six `ihdoms`/`Ca`-dependent
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
domains and the rule conclusions chosen, so no certificate family has
to be built. -/
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
    (helim : ∀ u ∈ us, Level.isEquiv u (ConLeche.structElimLevel p.elim p.large) = some true)
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
