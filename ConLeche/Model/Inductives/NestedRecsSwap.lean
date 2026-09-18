module

public import ConLeche.Verify.Inductives.NestedRecsWF
public import ConLeche.Semantics.IndBlockFacts
public import ConLeche.Model.Annot.EnvModelM
import ConLeche.Verify.Extend.Recs
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Swap
import ConLeche.Model.Inductives.MutualRecsSwap
public section

/-!
# The restored recursors' store, as a swap (task #315, M7-2, item 5 step 3)

`MutualRecsSwap.lean`'s twin at the nested route.  The kernel conses
the `k + nPins` restored recursors twice: RULE-LESS
(`provisionNestedRecs`, the environment every restored rule is scoped
at) and then, at the SAME names in the SAME order, WITH their restored
rules (`storeNestedRecs`).  The second cons is therefore a *rule-list
swap* of the first.

Where the mutual pair takes the block and COMPUTES each entry's
arities and rules, the nested pair takes the entries as data — a list
of quadruples for the store, its projection `nestedProvOf` for the
provision — so everything here is generic in that one list, and the
run's own list is the caller's.  `swapFacts_of_shList` (the transport
of the three syntactic environment facts that are not `EnvWF`) is
generic in the two environments already and is reused verbatim.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The provision and the store, as a swap -/

section Swap

variable {l : List (ConstantVal × Nat × Nat × List RecRule)}

/-- **The provision and the store are a shape-level swap**: the same
names, in the same order, on lookup-comparable environments,
differing only in their rule lists. -/
theorem swapShList_provision_store_nested :
    ∀ (l : List (ConstantVal × Nat × Nat × List RecRule)) {env env' : Env},
      ConLeche.SwapShList env.consts env'.consts →
      ConLeche.SwapShList (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env).consts
        (ConLeche.storeNestedRecs l env').consts
  | [], _, _, h => h
  | (cvRa, mI, rP, rules) :: rest, env, env', h => by
    simp only [ConLeche.nestedProvOf, List.map_cons, ConLeche.provisionNestedRecs,
      ConLeche.storeNestedRecs]
    exact swapShList_provision_store_nested rest
      (ConLeche.SwapShList.cons (Or.inr ⟨cvRa, mI, rP, rules, rfl, rfl⟩) h)

/-- **The swap sits at no reserved basis name**: the only entries the
store changes are the block's restored recursors. -/
theorem swapNResS_provision_store_nested :
    ∀ (l : List (ConstantVal × Nat × Nat × List RecRule)) {env env' : Env},
      (∀ x ∈ l, ConLeche.reservedBasisNames.contains x.1.name = false) →
      SwapNResS env env' →
      SwapNResS (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env)
        (ConLeche.storeNestedRecs l env')
  | [], _, _, _, h => h
  | (cvRa, mI, rP, rules) :: rest, env, env', hres, h => by
    simp only [ConLeche.nestedProvOf, List.map_cons, ConLeche.provisionNestedRecs,
      ConLeche.storeNestedRecs]
    refine swapNResS_provision_store_nested rest
      (fun x hx => hres x (List.mem_cons_of_mem _ hx)) ?_
    intro n cv mI' rP' rules' h₀ h₃
    by_cases hn : cvRa.name = n
    · refine Or.inr ?_
      show ConLeche.reservedBasisNames.contains n = false
      rw [← hn]
      exact hres (cvRa, mI, rP, rules) List.mem_cons_self
    · rw [find?_cons_of_name_ne (c := ConstantInfo.recInfo cvRa mI rP []) hn] at h₀
      rw [find?_cons_of_name_ne (c := ConstantInfo.recInfo cvRa mI rP rules) hn] at h₃
      exact h n cv mI' rP' rules' h₀ h₃

/-- A name free after the store's conses was free before them: the
stage only ADDS recursors (`consNestedFormers_find?_none`'s twin at
`storeNestedRecs`). -/
theorem storeNestedRecs_find?_none :
    ∀ {l : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} {n : Name},
      (ConLeche.storeNestedRecs l env).find? n = none → env.find? n = none
  | [], _, _, h => h
  | (cvRa, mI, rP, rules) :: rest, env, n, h => by
    simp only [ConLeche.storeNestedRecs] at h
    have h' : (Env.mk (.recInfo cvRa mI rP rules :: env.consts)).find? n = none :=
      storeNestedRecs_find?_none h
    rw [ConLeche.Env.find?_cons] at h'
    split at h'
    · exact nomatch h'
    · exact h'

/-- The store's lookups: the base environment's, or one of the stored
recursors. -/
theorem storeNestedRecs_find?_inv :
    ∀ {l : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} {n : Name}
      {c : ConstantInfo},
      (ConLeche.storeNestedRecs l env).find? n = some c →
      env.find? n = some c ∨
        ∃ x ∈ l, c = .recInfo x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ x.1.name = n
  | [], _, _, _, h => Or.inl h
  | (cvRa, mI, rP, rules) :: rest, env, n, c, h => by
    simp only [ConLeche.storeNestedRecs] at h
    rcases storeNestedRecs_find?_inv h with h' | ⟨x, hx, hc, hn⟩
    · rw [ConLeche.Env.find?_cons] at h'
      split at h'
      · next hname =>
        exact Or.inr ⟨(cvRa, mI, rP, rules), List.mem_cons_self, (Option.some.inj h').symm, hname⟩
      · exact Or.inl h'
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, hc, hn⟩

/-- The provision's lookups, at a name none of the restored recursors
carries: the base environment's. -/
theorem provisionNestedRecs_find?_of_ne :
    ∀ {l : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} {n : Name},
      (∀ x ∈ l, n ≠ x.1.name) →
      (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env).find? n = env.find? n
  | [], _, _, _ => rfl
  | (cvRa, mI, rP, rules) :: rest, env, n, hne => by
    simp only [ConLeche.nestedProvOf, List.map_cons, ConLeche.provisionNestedRecs]
    rw [show (rest.map fun x => (x.1, x.2.1, x.2.2.1)) = ConLeche.nestedProvOf rest from rfl,
      provisionNestedRecs_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      ConLeche.Env.find?_cons,
      if_neg (fun hh => hne (cvRa, mI, rP, rules) List.mem_cons_self hh.symm)]

/-- **The provision's stored entries survive the provision's own
conses**: a name the constructors' environment already carries is
found unchanged past the fresh recursors. -/
theorem provisionNestedRecs_findPreserved {env : Env}
    (hfresh : ∀ x ∈ l, env.find? x.1.name = none) :
    ∀ (n : Name) (ci : ConstantInfo), env.find? n = some ci →
      (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env).find? n = some ci := by
  intro n ci hf
  rw [provisionNestedRecs_find?_of_ne ?ne]
  · exact hf
  case ne =>
    intro x hx hn
    have := hfresh x hx
    rw [← hn, hf] at this
    exact nomatch this

end Swap

/-! ## The store: the swap -/

/-- **The restored recursors' store stage**: the carrier at the
provisioned environment crosses to the environment holding the SAME
recursors WITH their restored rules (`storeNestedRecs`), by
`EnvModelM.swapP`.

`EnvWF` at the store is `nested_recs_wf`'s; the other three syntactic
facts are transported (`swapFacts_of_shList`, the mutual file's, which
is generic in the two environments); and the rule rows are the
prefix's own — transported by `RecRuleLaw.swapP` — plus the restored
recursors', which the caller supplies at the final carrier. -/
theorem nestedRecsStore {env₂ : Env} {l : List (ConstantVal × Nat × Nat × List RecRule)}
    (henv₂ : ConLeche.EnvWF env₂)
    (mpP : EnvModelM V μ (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂))
    (hfresh : ∀ x ∈ l, env₂.find? x.1.name = none)
    (hnres : ∀ x ∈ l, ConLeche.reservedBasisNames.contains x.1.name = false)
    (htys : ∀ x ∈ l, x.1.type.hasFvar = false ∧
      x.1.type.allLevelParamsDefined x.1.levelParams = true ∧
      x.1.type.constsResolve env₂ = true ∧ x.1.type.looseBVarsBounded 0 = true)
    (hrulesWF : ∀ x ∈ l, ∀ r ∈ x.2.2.2,
      (RecRule.rhs r).hasFvar = false ∧
      (RecRule.rhs r).allLevelParamsDefined x.1.levelParams = true ∧
      (RecRule.rhs r).constsResolve
        (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂) = true ∧
      (RecRule.rhs r).looseBVarsBounded 0 = true ∧
      ∀ lvls pins, RecRule.fire r = .nested lvls pins →
        x.2.2.1 ≤ x.2.1 ∧
        (∀ u ∈ lvls, u.allParamsDefined x.1.levelParams = true) ∧
        (∀ pin ∈ pins, pin.hasFvar = false ∧
          pin.allLevelParamsDefined x.1.levelParams = true ∧
          pin.constsResolve
            (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂) = true ∧
          pin.looseBVarsBounded x.2.2.1 = true) ∧
        ∃ pre dom body bm D,
          x.1.type.stripPis x.2.1 = some (pre, .forallE dom body bm) ∧
          dom.getAppFn = .const D lvls ∧
          dom.getAppArgs =
            pins.map (Expr.liftLooseBVars (x.2.1 - x.2.2.1) 0) ++
              (List.range (x.2.1 - x.2.2.1)).map
                (fun i => Expr.bvar (x.2.1 - x.2.2.1 - 1 - i)))
    -- every stored rule's constructor, and its rescue bits, at the provision
    (hctorStored : ∀ x ∈ l, ∀ r ∈ x.2.2.2,
      (∃ cvj cnP cnF, (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂).find?
        (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
      (r.k = true → ConLeche.recRuleKOf
        (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂).find? r.ctor = true) ∧
      (r.eta = true → ConLeche.recRuleEtaOf
        (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂).find? x.1.name r.ctor
        = true))
    -- the restored recursors' own rule rows at the FINAL carrier
    (hlaws : ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs l env₂),
      m₃.acval = mpP.base2.acval → ∀ φ : Name → Nat, ∀ x ∈ l, ∀ rl ∈ x.2.2.2,
        RecRule.fire rl ≠ .inert →
        RecRuleLaw m₃ φ x.1.name x.1 x.2.1 x.2.2.1 rl) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.storeNestedRecs l env₂),
      mp₃.base2.acval = mpP.base2.acval ∧ mp₃.base2.cvalE = mpP.base2.cvalE := by
  have hsw : ConLeche.SwapShList
      (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂).consts
      (ConLeche.storeNestedRecs l env₂).consts :=
    swapShList_provision_store_nested _ (ConLeche.SwapShList.of_eq env₂.consts)
  have hnresS : SwapNResS (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂)
      (ConLeche.storeNestedRecs l env₂) :=
    swapNResS_provision_store_nested _ hnres (SwapNResS.of_eq env₂)
  have hcg := ConLeche.SwapShList.congr hsw
  have hmono : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂).find? n = some c :=
    provisionNestedRecs_findPreserved hfresh
  have hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      (ConLeche.storeNestedRecs l env₂).find? n = some (.recInfo cv mI rP rules) →
      (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂).find? n
        = some (.recInfo cv mI rP rules) ∨
      ∀ r ∈ rules,
        (∃ cvj cnP cnF, (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂).find?
          (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf
          (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂).find? r.ctor = true) ∧
        (r.eta = true → ConLeche.recRuleEtaOf
          (ConLeche.provisionNestedRecs (ConLeche.nestedProvOf l) env₂).find? n r.ctor
          = true) := by
    intro n cv mI rP rules hf
    rcases storeNestedRecs_find?_inv hf with h₂ | ⟨x, hx, hc, hn⟩
    · exact Or.inl (hmono _ _ h₂)
    right
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
    intro r hr
    obtain ⟨hct, hk, he⟩ := hctorStored x hx r hr
    exact ⟨hct, hk, by rw [← hn]; exact he⟩
  obtain ⟨hctors₃, hbp₃, hproj₃⟩ :=
    swapFacts_of_shList hsw hnresS mpP.base2.rec_ctors mpP.base2.basis_pinnedL
      mpP.base2.proj_ok hnew
  have hrecP : ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs l env₂),
      m₃.acval = mpP.base2.acval → ∀ φ : Name → Nat, RecRules m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
    rcases storeNestedRecs_find?_inv hf with h₂ | ⟨x, hx, hc, hn⟩
    · exact RecRuleLaw.swapP hcg hac
        (mpP.rec_rules φ n cv mI rP rules (hmono _ _ h₂) rl hrl hfire)
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
      rw [← hn]
      exact hlaws m₃ hac φ x hx rl hrl hfire
  exact EnvModelM.swapP mpP hsw (ConLeche.nested_recs_wf henv₂ htys hrulesWF) hctors₃ hbp₃
    hproj₃ hrecP

end ConLeche.Model
