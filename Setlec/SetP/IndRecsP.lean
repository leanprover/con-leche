import Setlec.SetP.SwapP
import Setlec.SetP.IndMembersP
import Setlec.SetP.CapstoneP

/-!
# The recursor-group phase, P tier (task #161, IND TIER part 10)

`Install/IndRecsS.lean`'s **environment layer** at the reading.  The
law layer landed in part 9 (`iotaRuleP`/`iotaRulesP`); what remains,
and what this file is, is the `EnvS2PM` construction that carries those
laws to the group's output environment:

* **provision** — `provisionRecsPM` (part 2) already installs the
  group rule-less *at both tiers*, so the self environment carries an
  `EnvS2PM`, which is what the rule certificates' run route needs;
* **fire** — `iotaRulesP` at each provisioned recursor;
* **swap** — `EnvS2PM.swapP`, with the group's `rec_rules` row assembled
  here.

**The fold is much smaller than v1's.**  `indRecsFoldS` threads seven
invariants because it must produce the swap data (`SwapShList`,
`SwapNResS`) and the `EnvWF`/`RecCtorsStored` inputs of `EnvS.swap`.
None of that is V-tier content: the P fold needs only the *rows*, so it
threads exactly one invariant — the per-recursor law at the fold's
accumulator — and takes the swap data from the v1 fold, which the
install runs anyway (`indRecsFoldS`, called here for `hswR` alone).

The `iotaRulesP` call's environment argument is the **base**
environment throughout (`IndRecsFoldR`'s own choice, task #148 T6), so
`FoldUpS envBase envSelf` and the `Eq` lookup are fixed across the
whole induction — the only per-step data are the block membership and
the provisioned entry's lookup.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- **One recursor's fired rows, at a fixed carrier** — the single
invariant the P fold threads.  `RuleFactsS`'s P residue: its syntactic
clauses are V-free and the v1 fold establishes them, so only the law
is here. -/
def RecLawsAtP {env : Env} (m : EnvS2Core V env) (cv : ConstantVal)
    (mI rP : Nat) (rules : List RecRule) : Prop :=
  ∀ rl ∈ rules, RecRule.fire rl ≠ .inert →
    ∀ φ : Name → Nat, RecRuleLawP m φ cv.name cv mI rP rl

set_option maxHeartbeats 1600000 in
/-- **The provisioning and the install fold, run together at the
reading** (`indRecsFoldS`'s P half).  The conclusion is the single row
`EnvS2PM.swapP` consumes: every recursor stored at the fold's output
either sits unchanged in the self environment — where `rec_rules`
already covers it — or carries the rules `iotaRulesP` fired. -/
theorem indRecsFoldP (hμ : μ.verified = true) {F : Nat}
    {blockNames : List Name} {envSelf envBase : Env}
    (mp : EnvS2PM V μ envSelf)
    (hIS : BlockInstalledTT blockNames envSelf mp.base.cval)
    (hroT : RenameOkP mp.base2.acval envSelf (fun n =>
      if blockNames.contains n then n.str "_model" else n))
    (hupB : FoldUpS envBase envSelf)
    (heqfB : envBase.find? eqName = some eqA) :
    ∀ (recs : List ConstantInfo) {envP envF env₃ : Env}
      {cvalF cval₃ : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      (∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
        (rules : List RecRule),
        envF.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsAtP mp.base2 cv mI rP rules) →
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsR μ F blockNames envP cvalF recs envSelf
        mp.base.cval checked →
      IndRecsR.IndRecsFoldR μ F blockNames envBase envSelf
        mp.base.cval envF cvalF checked env₃ cval₃ →
      ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
        (rules : List RecRule),
        env₃.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        RecLawsAtP mp.base2 cv mI rP rules := by
  -- the four claims and the reads, at every assignment (`hμ` + `mp`)
  have hclaims := fun ψ =>
    checkSoundAtP (V := V) hμ (TierInputsAtP.ofSem mp ψ) F
  have hdeq : ∀ ψ : Name → Nat, DefEqClaims2P μ mp.base2 ψ F :=
    fun ψ => (hclaims ψ).2.2.1
  have hinf : ∀ ψ : Name → Nat, InferClaims2P μ mp.base2 ψ F :=
    fun ψ => (hclaims ψ).2.2.2
  have hreadsP : ∀ ψ : Name → Nat, InferReadsP mp.base2 μ ψ F :=
    fun ψ => inferReadsP_of (TierInputsAtP.ofSem mp ψ).reads
  intro recs
  induction recs with
  | nil =>
    intro envP envF env₃ cvalF cval₃ checked hentF hbn hprov hfold
    obtain ⟨rfl, rfl, rfl⟩ := hprov
    obtain ⟨rfl, rfl⟩ := hfold
    exact hentF
  | cons ci₀ rest ih =>
    intro envP envF env₃ cvalF cval₃ checked hentF hbn hprov hfold
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hprov', rfl⟩ := hprov
    obtain ⟨rules', hiot, hfold'⟩ := hfold
    obtain ⟨type', hcv, hcvAdef, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by rw [hcvAdef]
    have hselfA : envSelf.find? cvA.name
        = some (.recInfo cvA mI rP []) :=
      provisionRecsS_mono rest hprov' _ _
        (Env.find?_cons_self (.recInfo cvA mI rP []) envP)
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci₀ List.mem_cons_self
    -- this recursor's rules, fired
    have hfacts : RecLawsAtP mp.base2 cvA mI rP rules' :=
      fun rl hrl hfire φ =>
        iotaRulesP mp hdeq hinf hreadsP rfl hroT hIS hupB hbnA hselfA
          heqfB 0 rules rules' hiot rl hrl hfire φ
    refine ih ?_ (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci))
      hprov' hfold'
    intro n cv mI₀ rP₀ rules₀ hfx
    rw [Env.find?_cons] at hfx
    split at hfx
    · obtain ⟨rfl, rfl, rfl, rfl⟩ :=
        ConstantInfo.recInfo.inj (Option.some.inj hfx)
      exact Or.inr hfacts
    · exact hentF n cv mI₀ rP₀ rules₀ hfx

/-- `BlockAcvalInstalled` crosses the swap: the predicate reads the
environment only through "this name is stored", and a swap changes no
stored name. -/
theorem blockAcvalInstalled_swap {blockNames : List Name}
    {env₀ env₃ : Env} {acval : Name → (Name → Nat) → AVExpr}
    (hcg : Setlec.SwapCongr env₀ env₃)
    (h : BlockAcvalInstalled blockNames env₀ acval) :
    BlockAcvalInstalled blockNames env₃ acval := by
  intro n hbn ci hf ψ
  have hs := hcg.isSomeEq n
  rw [hf] at hs
  rcases hf₀ : env₀.find? n with _ | ci₀
  · rw [hf₀] at hs; exact nomatch hs.symm
  · exact h n hbn ci₀ hf₀ ψ

set_option maxHeartbeats 1600000 in
/-- **The recursor-group phase, P tier**: provision, fire, swap.
The v1 carrier at the group's output is a premise — the install runs
`indRecsS` for it anyway, and taking it here keeps `EnvWF`,
`RecCtorsStored` and `RecRulesV` out of the P lane entirely. -/
theorem indRecsP (hμ : μ.verified = true) (hkey : MemberKeyS V)
    (hetaP : MemberEtaLawP V) (hunitP : MemberUnitLawP V) {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo} {cval₃ : TConstVal}
    (mp : EnvS2PM V μ env₂)
    (hI : BlockInstalledTT blockNames env₂ mp.base.cval)
    (hIA : BlockAcvalInstalled blockNames env₂ mp.base2.acval)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hall : ∀ n, blockNames.contains n = true →
      (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n)
    (hEC : Setlec.EtaFamiliesClosedO blockNames env₂)
    (hBP : Setlec.BlockEtaPinned μ blockNames env₂)
    (hbase₃ : EnvS V env₃) (hb₃cval : hbase₃.cval = cval₃)
    (h : IndRecsR μ F blockNames env₂ mp.base.cval recs env₃
      cval₃) :
    ∃ mp₃ : EnvS2PM V μ env₃,
      mp₃.base.cval = cval₃ ∧
      BlockAcvalInstalled blockNames env₃ mp₃.base2.acval := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨-, heqf, envSelf, cvalSelf, checked,
    hprov, hfold⟩
  · exact ⟨mp, rfl, hIA⟩
  -- the provisioning, at both tiers
  obtain ⟨mS, hmScval, hIS, hIAS, hECS, hBPS⟩ :=
    provisionRecsPM hkey hetaP hunitP recs mp hbn hprov hI hIA hEC hBP
  rw [← hmScval] at hprov hfold hIS
  -- every block member is stored in the provisional environment
  have hnames : ∀ n, blockNames.contains n = true →
      (envSelf.find? n).isSome = true := by
    intro n hn
    rcases hall n hn with hfound | ⟨ci, hci, rfl⟩
    · rcases hf : env₂.find? n with _ | ci
      · rw [hf] at hfound; exact nomatch hfound
      · rw [provisionRecsS_mono recs hprov n ci hf]; rfl
    · exact provisionRecsS_stored recs hprov ci hci
  -- the block renaming, at both tiers
  have hro := blockRenameOkT hIS hnames
  have hroP := blockRenameOkP hIS hIAS hnames
  -- the fold's swap data, model-free (task #161 S6): this call used
  -- to be `indRecsFoldS mS.base` — the v1 install, run for two of its
  -- five conclusions.  `indRecsFoldFacts` (`SetBase/IndBlockR.lean`)
  -- is the same induction with the per-rule conclusion as a
  -- parameter, and `iotaRulesFactsR` supplies the model-free one, so
  -- the P lane no longer round-trips through the collapsed install
  -- here at all.
  obtain ⟨hswR, -, hcvEq, -, -⟩ :=
    indRecsFoldFacts (RuleFactsR envSelf mS.base.cval)
      (fun _cvA _mI _rP rules rules' _hbnA _hselfA hiot =>
        iotaRulesFactsR
          (fun n ci hf =>
            Or.inl (provisionRecsS_mono recs hprov n ci hf))
          0 rules rules' hiot)
      recs (SwapShList.of_eq env₂.consts)
      (SwapNResS.of_eq env₂)
      (fun n ci hf =>
        Or.inl (provisionRecsS_mono recs hprov n ci hf))
      (provisionRecsS_mono recs hprov) heqf
      (fun c hc => Or.inl (provisionRecsS_mem recs hprov c hc))
      (fun n cv mI rP rules hf =>
        Or.inl (provisionRecsS_mono recs hprov n _ hf))
      hbn hprov hfold
  have hcg : Setlec.SwapCongr envSelf env₃ := SwapShList.congr hswR
  -- the P rows at the group's output
  have hentF := indRecsFoldP (V := V) hμ mS hIS hroP
    (fun n ci hf => Or.inl (provisionRecsS_mono recs hprov n ci hf))
    heqf recs
    (fun n cv mI rP rules hf =>
      Or.inl (provisionRecsS_mono recs hprov n _ hf))
    hbn hprov hfold
  -- `rec_rules` at the swapped carrier
  have hrecP : ∀ m₃ : EnvS2Core V env₃, m₃.acval = mS.base2.acval →
      ∀ φ : Name → Nat, RecRulesP m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
    rcases hentF n cv mI rP rules hf with hfS | hlaws
    · exact RecRuleLawP.swapP hcg hac
        (mS.rec_rules φ n cv mI rP rules hfS rl hrl hfire)
    · rw [← Env.find?_name hf]
      exact RecRuleLawP.swapP hcg hac (hlaws rl hrl hfire φ)
  -- the swap
  obtain ⟨mp₃, hacc, hcval₃⟩ :=
    EnvS2PM.swapP mS hswR hbase₃ (by rw [hb₃cval, hcvEq]) hrecP
  exact ⟨mp₃, by rw [hcval₃, hb₃cval],
    by rw [hacc]; exact blockAcvalInstalled_swap hcg hIAS⟩

end Setlec.SetR.Interp2
