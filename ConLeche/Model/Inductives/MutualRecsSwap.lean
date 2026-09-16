module

public import ConLeche.Model.Swap
public import ConLeche.Model.Inductives.MutualFormersKit
public import ConLeche.Verify.Inductives.MutualWF
public import ConLeche.Semantics.IndBlockFacts
public section

/-!
# The recursors' store, as a swap (task #315 U-9, M4 s4b)

The kernel conses the block's `k` recursors twice: RULE-LESS
(`provisionMutualRecs`, the environment every rule is scoped at) and
then, at the SAME names in the SAME order, WITH their generated rules
(`storeMutualRecs`).  The second cons is therefore a *rule-list swap*
of the first, and this file is that reading of it: the two conses'
shape-level agreement (`swapShList_provision_store`), the side
condition that no swapped entry sits at a pinned basis name
(`swapNResS_provision_store`), the two lookup inversions
(`storeMutualRecs_find?_inv`, `provisionMutualRecs_find?_of_ne`), the
transport of the three syntactic environment facts that are not
`EnvWF` (`swapFacts_of_shList`, whose rule premise is the store's own
rule data rather than a `RuleFacts` record), and the stage itself
(`mutualRecsStore`): the carrier at the provisioned environment
crosses to the stored one by `EnvModelM.swapP`, with `EnvWF` from
`mutual_recs_wf` and the block's own rule rows as a premise at the
final carrier.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps RecRule
  MutualBlock MutualFormerA MutualFormer MutualCtor MutualCtor4)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The provision and the store, as a swap -/

section Swap

variable {b : MutualBlock} {fms : List MutualFormerA}
  {rulesOf : List (List (MutualCtor × Expr))} {env₂ : Env}

/-- The head the store conses for entry `(cvRa, mIdx)`. -/
@[expose] def storeHead (env₂ : Env) (b : MutualBlock) (fms : List MutualFormerA)
    (rulesOf : List (List (MutualCtor × Expr))) (x : ConstantVal × Nat) : ConstantInfo :=
  .recInfo x.1 (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix
    (ConLeche.mutualRules env₂.find? x.1.name b.nP
      (b.rulePrefix + (fms.getD x.2 default).nIdx) b.rulePrefix x.1.type (rulesOf.getD x.2 []))

/-- **The provision and the store are a shape-level swap**: the same
`k` names, in the same order, on lookup-comparable environments,
differing only in their rule lists. -/
theorem swapShList_provision_store :
    ∀ (l : List (ConstantVal × Nat)) {env env' : Env},
      ConLeche.SwapShList env.consts env'.consts →
      ConLeche.SwapShList (ConLeche.provisionMutualRecs b fms l env).consts
        (ConLeche.storeMutualRecs env₂ b fms rulesOf l env').consts
  | [], _, _, h => h
  | (cvRa, mIdx) :: rest, env, env', h => by
    simp only [ConLeche.provisionMutualRecs, ConLeche.storeMutualRecs]
    exact swapShList_provision_store rest
      (ConLeche.SwapShList.cons (Or.inr ⟨cvRa, _, _, _, rfl, rfl⟩) h)

/-- **The swap sits at no reserved basis name**: the only entries the
store changes are the block's recursors. -/
theorem swapNResS_provision_store :
    ∀ (l : List (ConstantVal × Nat)) {env env' : Env},
      (∀ x ∈ l, ConLeche.reservedBasisNames.contains x.1.name = false) →
      SwapNResS env env' →
      SwapNResS (ConLeche.provisionMutualRecs b fms l env)
        (ConLeche.storeMutualRecs env₂ b fms rulesOf l env')
  | [], _, _, _, h => h
  | (cvRa, mIdx) :: rest, env, env', hres, h => by
    simp only [ConLeche.provisionMutualRecs, ConLeche.storeMutualRecs]
    refine swapNResS_provision_store rest (fun x hx => hres x (List.mem_cons_of_mem _ hx)) ?_
    intro n cv mI rP rules h₀ h₃
    by_cases hn : cvRa.name = n
    · refine Or.inr ?_
      show ConLeche.reservedBasisNames.contains n = false
      rw [← hn]
      exact hres (cvRa, mIdx) List.mem_cons_self
    · rw [find?_cons_of_name_ne (c := .recInfo cvRa
        (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix []) hn] at h₀
      rw [find?_cons_of_name_ne (c := .recInfo cvRa
        (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix
        (ConLeche.mutualRules env₂.find? cvRa.name b.nP
          (b.rulePrefix + (fms.getD mIdx default).nIdx) b.rulePrefix cvRa.type
          (rulesOf.getD mIdx []))) hn] at h₃
      exact h n cv mI rP rules h₀ h₃

/-- The store's lookups: the base environment's, or one of the `k`
stored recursors. -/
theorem storeMutualRecs_find?_inv :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {n : Name} {c : ConstantInfo},
      (ConLeche.storeMutualRecs env₂ b fms rulesOf l env).find? n = some c →
      env.find? n = some c ∨ ∃ x ∈ l, c = storeHead env₂ b fms rulesOf x ∧ x.1.name = n
  | [], _, _, _, h => Or.inl h
  | (cvRa, mIdx) :: rest, env, n, c, h => by
    simp only [ConLeche.storeMutualRecs] at h
    rcases storeMutualRecs_find?_inv h with h' | ⟨x, hx, hc, hn⟩
    · rw [ConLeche.Env.find?_cons] at h'
      split at h'
      · next hname =>
        exact Or.inr ⟨(cvRa, mIdx), List.mem_cons_self, (Option.some.inj h').symm, hname⟩
      · exact Or.inl h'
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hc, hn⟩

/-- The provision's lookups, at a name none of the `k` recursors
carries: the base environment's. -/
theorem provisionMutualRecs_find?_of_ne :
    ∀ {l : List (ConstantVal × Nat)} {env : Env} {n : Name},
      (∀ x ∈ l, n ≠ x.1.name) →
      (ConLeche.provisionMutualRecs b fms l env).find? n = env.find? n
  | [], _, _, _ => rfl
  | (cvRa, mIdx) :: rest, env, n, hne => by
    simp only [ConLeche.provisionMutualRecs]
    rw [provisionMutualRecs_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      ConLeche.Env.find?_cons,
      if_neg (fun hh => hne (cvRa, mIdx) List.mem_cons_self hh.symm)]

/-- **The provision's stored entries survive the provision's own
conses**: a name the constructors' environment already carries is
found unchanged past the `k` fresh recursors. -/
theorem provisionMutualRecs_findPreserved {l : List (ConstantVal × Nat)} {env : Env}
    (hfresh : ∀ x ∈ l, env.find? x.1.name = none) :
    ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
      (ConLeche.provisionMutualRecs b fms l env).find? n = some ci := by
  intro n ci hf
  rw [provisionMutualRecs_find?_of_ne ?ne]
  · exact hf
  case ne =>
    intro x hx hn
    have := hfresh x hx
    rw [← hn, hf] at this
    exact nomatch this

/-- **The provision and the store are lookup-congruent**: the swap's
environment congruences, at the block's own entry list. -/
theorem swapCongr_provision_store {cvRas : List ConstantVal} :
    ConLeche.SwapCongr (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂)
      (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂) :=
  ConLeche.SwapShList.congr
    (swapShList_provision_store _ (ConLeche.SwapShList.of_eq env₂.consts))

/-- **The three remaining syntactic environment facts survive the
swap** (`swapEnvFacts`'s non-`EnvWF` half, with the `RuleFacts`
premise replaced by the store's own rule data). -/
theorem swapFacts_of_shList {env₀ env₃ : Env} {cval : TConstVal}
    (hsw : ConLeche.SwapShList env₀.consts env₃.consts)
    (hnres : SwapNResS env₀ env₃)
    (hctors₀ : ConLeche.RecCtorsStored env₀)
    (hbp₀ : BasisPinnedTT env₀ cval)
    (hproj₀ : ProjOkT env₀)
    (hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      env₃.find? n = some (.recInfo cv mI rP rules) →
      env₀.find? n = some (.recInfo cv mI rP rules) ∨
      ∀ r ∈ rules,
        (∃ cvj cnP cnF, env₀.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf env₀.find? r.ctor = true) ∧
        (r.eta = true → ConLeche.recRuleEtaOf env₀.find? n r.ctor = true)) :
    ConLeche.RecCtorsStored env₃ ∧ BasisPinnedTT env₃ cval ∧ ProjOkT env₃ := by
  have hcg : ConLeche.SwapCongr env₀ env₃ := ConLeche.SwapShList.congr hsw
  have hcorr := ConLeche.swapSh_find?_corr hsw
  have hsame : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      (env₃.find? n = some ci ↔ env₀.find? n = some ci) :=
    fun n ci hnr => ⟨fun h => hcg.findDown n ci h hnr, fun h => hcg.findUp n ci h hnr⟩
  have hkeep : ∀ (m : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      env₀.find? m = some ci → env₃.find? m = some ci :=
    fun m ci hnr hf => hcg.findUp m ci hf hnr
  refine ⟨?_, ?_, ?_⟩
  · -- `RecCtorsStored`
    intro n cv mI rP rules hf r hr
    rcases hnew n cv mI rP rules hf with hf₀ | hfacts
    · obtain ⟨⟨cvj, cnP, cnF, hfc⟩, hk, he⟩ := hctors₀ n cv mI rP rules hf₀ r hr
      exact ⟨⟨cvj, cnP, cnF, hkeep _ _
          (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩,
        fun hb => recRuleKOf_mono hkeep (hk hb),
        fun hb => recRuleEtaOf_mono hkeep (he hb)⟩
    · obtain ⟨⟨cvj, cnP, cnF, hfc⟩, hk, he⟩ := hfacts r hr
      exact ⟨⟨cvj, cnP, cnF, hkeep _ _
          (fun _ _ _ _ hcon => ConstantInfo.noConfusion hcon) hfc⟩,
        fun hb => recRuleKOf_mono hkeep (hk hb),
        fun hb => recRuleEtaOf_mono hkeep (he hb)⟩
  · -- `BasisPinnedTT`: a genuinely swapped entry is never reserved
    intro n ci hf hres
    have hf₀ : env₀.find? n = some ci := by
      rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
      · rw [← heq]; exact hf
      · rcases hnres n cv mI rP rules h₀ h₃ with rfl | hnr
        · rw [h₃] at hf
          obtain rfl := Option.some.inj hf
          exact h₀
        · rw [hnr] at hres
          exact nomatch hres
    exact hbp₀ n ci hf₀ hres
  · -- `ProjOkT`: projection tables are untouched
    intro n tbl hf i hi
    exact ConLeche.TowerHead.mono (fun n' ci hnr hf' => (hsame n' ci hnr).mpr hf')
      (hproj₀ n tbl ((hsame _ _ (fun _ _ _ _ h => ConstantInfo.noConfusion h)).mp hf) i hi)

end Swap


/-! ## The store: the swap -/

/-- **The recursors' store stage**: the carrier at the provisioned
environment crosses to the environment holding the SAME `k` recursors
WITH their rules (`storeMutualRecs`), by `EnvModelM.swapP`.

`EnvWF` at the store is `mutual_recs_wf`'s (a rule is scoped at the
provision, and the store finds every name the provision finds); the
other three syntactic facts are transported (`swapFacts_of_shList`),
and the rule rows are the prefix's own — transported by
`RecRuleLaw.swapP` — plus the block's, which the caller supplies at
the final carrier. -/
theorem mutualRecsStore {k : Nat}
    {b : MutualBlock} {fms : List MutualFormerA} {cvRas : List ConstantVal}
    {rulesOf : List (List (MutualCtor × Expr))} {env₂ : Env}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {F : Nat}
    (henv₂ : ConLeche.EnvWF env₂)
    (hrectys : ConLeche.checkMutualRecTys (ConLeche.fueledOps μ F) env₂ b formers4 ctors4
      streamRecs b.k = .ok cvRas)
    (hrules : ConLeche.checkMutualAllRules (m := ConLeche.CheckM)
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂) b formers4 ctors4 streamRecs b.k
      = .ok rulesOf)
    (mpP : EnvModelM V μ (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂))
    (hk : cvRas.length = k)
    (hfresh : ∀ t, t < k → env₂.find? (cvRas.getD t default).name = none)
    (hnres : ∀ t, t < k →
      ConLeche.reservedBasisNames.contains (cvRas.getD t default).name = false)
    -- every stored rule's constructor is stored at the constructors'
    -- environment (the block's own constructors, consed there)
    (hctorStored : ∀ t, t < k → ∀ r ∈ ConLeche.mutualRules env₂.find?
        (cvRas.getD t default).name b.nP (b.rulePrefix + (fms.getD t default).nIdx)
        b.rulePrefix (cvRas.getD t default).type (rulesOf.getD t []),
      ∃ cvj cnP cnF, env₂.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    -- the block's own rule rows at the FINAL carrier
    (hlaws : ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      m₃.acval = mpP.base2.acval → ∀ (φ : Name → Nat) (t : Nat), t < k →
      ∀ rl ∈ ConLeche.mutualRules env₂.find? (cvRas.getD t default).name b.nP
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix
          (cvRas.getD t default).type (rulesOf.getD t []),
        RecRule.fire rl ≠ .inert →
        RecRuleLaw m₃ φ (cvRas.getD t default).name (cvRas.getD t default)
          (b.rulePrefix + (fms.getD t default).nIdx) b.rulePrefix rl) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      mp₃.base2.acval = mpP.base2.acval ∧ mp₃.base2.cvalE = mpP.base2.cvalE := by
  -- the block's entries
  have hzip : ∀ x ∈ cvRas.zipIdx, x.2 < k ∧ x.1 = cvRas.getD x.2 default := by
    intro x hx
    have hget : cvRas[x.2]? = some x.1 := List.mk_mem_zipIdx_iff_getElem?.mp (by simpa using hx)
    exact ⟨by rw [← hk]; exact (List.getElem?_eq_some_iff.mp hget).1,
      by rw [List.getD_eq_getElem?_getD, hget]; rfl⟩
  -- the swap
  have hsw : ConLeche.SwapShList (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).consts
      (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂).consts :=
    swapShList_provision_store _ (ConLeche.SwapShList.of_eq env₂.consts)
  have hnresS : SwapNResS (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂)
      (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂) :=
    swapNResS_provision_store _
      (fun x hx => by rw [(hzip x hx).2]; exact hnres x.2 (hzip x hx).1)
      (SwapNResS.of_eq env₂)
  have hcg := ConLeche.SwapShList.congr hsw
  -- the constructors' environment sits inside the provision
  have hmono : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n = some c :=
    provisionMutualRecs_findPreserved
      (fun x hx => by rw [(hzip x hx).2]; exact hfresh x.2 (hzip x hx).1)
  have hkeep₂ : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) → env₂.find? n = some ci →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n = some ci :=
    fun n ci _ h => hmono n ci h
  -- the store's own rules: their constructors and their rescue bits
  have hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂).find? n
        = some (.recInfo cv mI rP rules) →
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n
        = some (.recInfo cv mI rP rules) ∨
      ∀ r ∈ rules,
        (∃ cvj cnP cnF, (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find?
          (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf
          (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? r.ctor = true) ∧
        (r.eta = true → ConLeche.recRuleEtaOf
          (ConLeche.provisionMutualRecs b fms cvRas.zipIdx env₂).find? n r.ctor = true) := by
    intro n cv mI rP rules hf
    rcases storeMutualRecs_find?_inv hf with h₂ | ⟨x, hx, hc, hn⟩
    · exact Or.inl (hmono _ _ h₂)
    right
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
    obtain ⟨hxk, hxv⟩ := hzip x hx
    intro r hr
    rw [hxv] at hr
    obtain ⟨hkb, heb⟩ := ConLeche.mutualRules_bits hr
    obtain ⟨cvj, cnP, cnF, hfc⟩ := hctorStored x.2 hxk r hr
    refine ⟨⟨cvj, cnP, cnF, hmono _ _ hfc⟩, fun hb => ?_, fun hb => ?_⟩
    · exact recRuleKOf_mono hkeep₂ (by rw [← hkb]; exact hb)
    · rw [← hn, hxv]
      exact recRuleEtaOf_mono hkeep₂ (by rw [← heb]; exact hb)
  obtain ⟨hctors₃, hbp₃, hproj₃⟩ :=
    swapFacts_of_shList hsw hnresS mpP.base2.rec_ctors mpP.base2.basis_pinnedL
      mpP.base2.proj_ok hnew
  -- the rule rows at the swapped carrier
  have hrecP : ∀ m₃ : EnvModel V (ConLeche.storeMutualRecs env₂ b fms rulesOf cvRas.zipIdx env₂),
      m₃.acval = mpP.base2.acval → ∀ φ : Name → Nat, RecRules m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
    rcases storeMutualRecs_find?_inv hf with h₂ | ⟨x, hx, hc, hn⟩
    · exact RecRuleLaw.swapP hcg hac
        (mpP.rec_rules φ n cv mI rP rules (hmono _ _ h₂) rl hrl hfire)
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
      obtain ⟨hxk, hxv⟩ := hzip x hx
      rw [← hn, hxv]
      rw [hxv] at hrl
      exact hlaws m₃ hac φ x.2 hxk rl hrl hfire
  exact EnvModelM.swapP mpP hsw (ConLeche.mutual_recs_wf henv₂ hrectys hrules) hctors₃ hbp₃
    hproj₃ hrecP

end ConLeche.Model
