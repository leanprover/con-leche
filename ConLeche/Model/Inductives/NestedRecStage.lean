module

public import ConLeche.Model.Inductives.NestedCtorStage
public import ConLeche.Model.Inductives.MutualStageRec
import ConLeche.Model.Inductives.StructCaps
import ConLeche.Model.Swap
import ConLeche.Model.IndCons
import ConLeche.Model.RecRulesCons

public section

/-!
# The restored recursors' stage (task #279 M-D′ D4)

The nested install stores its `p.k + n` restored recursors in two
moves, exactly as the mutual route does
(`Kernel/Inductives/NestedInstall.lean`):

* `provisionNestedRecs provs env₂` conses them RULE-LESS onto the
  constructors' environment — a rule mentions the sibling recursors, so
  every rule is scoped at the environment holding all of them.
  `stageNestedRecProvision` is the P step at ONE such cons
  (`declStep_preserves_of_ind_rec_cons` with `rules := []`, whose
  `hrec` is `recRules_cons_fresh`: a rule-less recursor owes no rule
  law), `stageNestedRecsProvisionGo` the loop.
* `storeNestedRecs stores env₂` conses the SAME names, in the same
  order, onto the SAME `env₂`, differing only in their rules
  (`hsp : stores.map (fun r => (r.1, r.2.1, r.2.2.1)) = provs`).  The
  carrier crosses that with `EnvModelM.swapP` (`stageNestedRecsStore`),
  whose `hrecP` is the prefix's own rule rows transported by
  `RecRuleLaw.swapP` plus the block's, which the caller supplies.

Everything here is GENERIC in the leaves: what one restored recursor's
cons asks is the constructors' stage's own record, `NestedCtorLeaf`
(`NestedCtorStage.lean`) — the leaf closed, level-parametric, graded
and bit-valid, the restored type reading at the environment so far,
graded, and the leaf a member of that reading.  The caller (M-D′'s
`declNested`) builds it; this file never looks inside.

**The caller's invariant `Inv`** is `stageMutualRecsProvisionGo`'s
device: the representation clause is owed at every intermediate
carrier of the provisioning loop, and those carriers are anonymous
here, so the loop threads a predicate on carriers the caller chooses,
with one step obligation (`hInv`) per cons.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-! ## One restored recursor's rule-less cons -/

/-- **The P step at ONE provisioned restored recursor's cons**
(`stageMutualRecProvision`'s shape with the leaf ABSTRACT): the
recursor is fresh at the environment, its static front-door facts hold
(`RestoredCtorStatic`), its type resolves there, and the leaf and its
typing are the caller's (`NestedCtorLeaf`).  The environment's
well-formedness is `structConstWF`'s with the rules clause vacuous (the
entry is consed rule-less), the reading is transported by
`denoteMeta_cons_mono`, the capability obligation is vacuous (the cons
stores a RECURSOR at the name it is taken at) and the rule law is
`recRules_cons_fresh`'s nothing. -/
theorem stageNestedRecProvision {μ : CheckMode} {env : Env} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) {cvR : ConstantVal} {mI rP : Nat}
    (hfresh : env.find? cvR.name = none) (hstatic : RestoredCtorStatic cvR)
    (htr : cvR.type.constsResolve env = true)
    {A ta : (Name → Nat) → AnnotTerm} (hL : NestedCtorLeaf mp cvR A ta)
    (hreps : ∀ m₂ : EnvModel V ⟨.recInfo cvR mI rP [] :: env.consts⟩,
      m₂.acval = acvalWith mp.base2.acval cvR.name A → IndRepsHead env (.recInfo cvR mI rP []) m₂) :
    ∃ mp' : EnvModelM V μ ⟨.recInfo cvR mI rP [] :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvR.name A := by
  obtain ⟨hnres, hpshape, htf, hlp, hbt⟩ := hstatic
  have hcb : ConstsBound env cvR.type := constsBound_of_constsResolve _ htr
  have hwf : ConLeche.EnvWF ⟨.recInfo cvR mI rP [] :: env.consts⟩ := by
    refine ConLeche.EnvWF.cons mp.base2.wf (ConLeche.structConstWF htf hlp
      (Expr.constsResolve_mono htr) hbt (fun _ _ _ heq => nomatch heq) ?_)
    intro cv mI' rP' rules heq r hr
    injection heq with _ _ _ hrules
    rw [← hrules] at hr
    exact nomatch hr
  have hread : ∀ ψ : Name → Nat,
      denoteMeta (acvalWith mp.base2.acval cvR.name A) ⟨.recInfo cvR mI rP [] :: env.consts⟩ ψ 0
        cvR.type = some (ta ψ) := fun ψ =>
    denoteMeta_cons_mono (c₀ := .recInfo cvR mI rP []) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hL.read ψ)
  refine declStep_preserves_of_ind_rec_cons mp (c₀ := .recInfo cvR mI rP [])
    (A := A) hfresh hnres ⟨_, _, _, _, rfl⟩
    (ConsHead.ofFresh hwf (fun ψ => hL.below ψ) hnres (fun _ h => nomatch h)
      (fun _ _ _ rules heq r hr => by
        injection heq with _ _ _ hrules
        rw [← hrules] at hr
        exact nomatch hr))
    (fun ψ q => AnnotTerm.liftN_eq_self _
      (Term.bvarsBelow.mono (Nat.zero_le q) (hL.below ψ)) 1)
    hL.params hL.wd hL.valid (fun ψ => ⟨_, hread ψ⟩) ?_ ?_ ?_ ?_ hreps
  · intro ψ ta' hta ρ
    obtain rfl := Option.some.inj ((hread ψ).symm.trans hta)
    exact hL.okTy ψ ρ
  · intro ψ ta' hta ρ
    obtain rfl := Option.some.inj ((hread ψ).symm.trans hta)
    exact hL.mem ψ ρ
  · -- `caps_ok`: the cons stores a RECURSOR at the name the obligation
    -- is taken at, so the block-family branch is vacuous
    intro m₂ hac
    refine capsOk_cons_native mp (c₀ := .recInfo cvR mI rP []) (A := A)
      (T := cvR.name) hfresh (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshape
      (Or.inr fun _ _ h => nomatch h)
      (fun T' cvT' caps' hf _ hres hcape => hE T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT' caps' hf _
    have hself := ConLeche.Env.find?_cons_self (ConstantInfo.recInfo cvR mI rP []) env
    rw [show (ConstantInfo.recInfo cvR mI rP []).name = cvR.name from rfl] at hself
    exact nomatch (hself.symm.trans hf)
  · -- `rec_rules`: the provisioned recursor has no rules
    intro m₂ hac φ
    exact recRules_cons_fresh mp (c₀ := .recInfo cvR mI rP []) (A := A) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h)
      (fun _ _ _ rules heq => by injection heq with _ _ _ hrules; exact hrules.symm) m₂ hac φ

/-! ## The provisioning loop -/

set_option maxHeartbeats 1600000 in
/-- **The restored recursors' rule-less conses, in order** (the
induction over the remaining entries, `stageNestedCtorsGo`'s positional
shape with `stageMutualRecsProvisionGo`'s invariant device).  Every
pending entry is fresh at the environment, statically sound, resolves
there and carries its leaf's content at the environment's model; each
cons keeps the facts of the rest (the reading by `denoteMeta_cons_mono`
at `ConsCrossAt.ofNtc`, the other six clauses of `NestedCtorLeaf` being
carrier-independent) and leaves every other name's leaf untouched. -/
theorem stageNestedRecsProvisionGo {μ : CheckMode} (Aof taOf : Nat → (Name → Nat) → AnnotTerm)
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop) :
    ∀ (rest : List (ConstantVal × Nat × Nat)) (k : Nat) (env : Env) (mp : EnvModelM V μ env),
      ConLeche.EtaFamiliesClosed env → (rest.map (·.1.name)).Nodup →
      (∀ (i : Nat) (x : ConstantVal × Nat × Nat), rest[i]? = some x →
        env.find? x.1.name = none ∧ RestoredCtorStatic x.1 ∧ x.1.type.constsResolve env = true ∧
        NestedCtorLeaf mp x.1 (Aof (k + i)) (taOf (k + i))) →
      Inv mp.base2 →
      (∀ (i : Nat) (x : ConstantVal × Nat × Nat), rest[i]? = some x →
        ∀ {env' : Env} (m' : EnvModel V env'), env'.find? x.1.name = none → Inv m' →
        ∀ m₂ : EnvModel V ⟨.recInfo x.1 x.2.1 x.2.2 [] :: env'.consts⟩,
          m₂.acval = acvalWith m'.acval x.1.name (Aof (k + i)) → Inv m₂) →
      (∀ (i : Nat) (x : ConstantVal × Nat × Nat), rest[i]? = some x →
        ∀ {env' : Env} (mp' : EnvModelM V μ env'), env'.find? x.1.name = none → Inv mp'.base2 →
        ∀ m₂ : EnvModel V ⟨.recInfo x.1 x.2.1 x.2.2 [] :: env'.consts⟩,
          m₂.acval = acvalWith mp'.base2.acval x.1.name (Aof (k + i)) →
          IndRepsHead env' (.recInfo x.1 x.2.1 x.2.2 []) m₂) →
      ∃ mp' : EnvModelM V μ (ConLeche.provisionNestedRecs rest env),
        ConLeche.EtaFamiliesClosed (ConLeche.provisionNestedRecs rest env) ∧
        (∀ (i : Nat) (x : ConstantVal × Nat × Nat), rest[i]? = some x →
          mp'.base2.acval x.1.name = Aof (k + i)) ∧
        (∀ n : Name, (∀ x ∈ rest, n ≠ x.1.name) → mp'.base2.acval n = mp.base2.acval n) ∧
        Inv mp'.base2
  | [], _, _, mp, hE, _, _, hinv, _, _ =>
    ⟨mp, hE, fun _ _ h => by simp at h, fun _ _ => rfl, hinv⟩
  | (cvR, mI, rP) :: rest, k, env, mp, hE, hnd, hfacts, hinv, hInv, hreps => by
    -- the head's facts
    obtain ⟨hfresh, hstatic, htr, hL⟩ := hfacts 0 (cvR, mI, rP) rfl
    simp only [Nat.add_zero] at hL
    -- the head's cons
    obtain ⟨mpR, hacR⟩ := stageNestedRecProvision (mI := mI) (rP := rP) mp hE hfresh hstatic htr hL
      (hreps 0 (cvR, mI, rP) rfl mp hfresh hinv)
    -- the names: the rest is fresh at the cons
    have hndR : (rest.map (·.1.name)).Nodup ∧ ∀ x ∈ rest, x.1.name ≠ cvR.name := by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      exact ⟨hnd.2, fun x hx h => hnd.1 ⟨x, hx, h⟩⟩
    have hE' : ConLeche.EtaFamiliesClosed ⟨.recInfo cvR mI rP [] :: env.consts⟩ :=
      hE.cons_nonind hfresh (fun _ _ heq => nomatch heq)
    -- the rest's facts cross the cons
    have hfacts' : ∀ (i : Nat) (x : ConstantVal × Nat × Nat), rest[i]? = some x →
        (⟨.recInfo cvR mI rP [] :: env.consts⟩ : Env).find? x.1.name = none ∧
        RestoredCtorStatic x.1 ∧
        x.1.type.constsResolve ⟨.recInfo cvR mI rP [] :: env.consts⟩ = true ∧
        NestedCtorLeaf mpR x.1 (Aof (k + 1 + i)) (taOf (k + 1 + i)) := by
      intro i x hx
      obtain ⟨hfreshI, hstaticI, htrI, hLI⟩ := hfacts (i + 1) x (by simpa using hx)
      rw [show k + (i + 1) = k + 1 + i from by omega] at hLI
      refine ⟨?_, hstaticI, Expr.constsResolve_mono htrI, ?_⟩
      · rw [ConLeche.Env.find?_cons]
        have hne : x.1.name ≠ cvR.name := hndR.2 x (List.mem_of_getElem? hx)
        simp only [show (ConstantInfo.recInfo cvR mI rP []).name = cvR.name from rfl]
        rw [if_neg (Ne.symm hne)]
        exact hfreshI
      · exact ⟨hLI.below, hLI.params, hLI.wd, hLI.valid, fun ψ => by
          rw [hacR]
          exact denoteMeta_cons_mono (c₀ := .recInfo cvR mI rP []) hfresh
            (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0
            (constsBound_of_constsResolve _ htrI) (hLI.read ψ), hLI.okTy, hLI.mem⟩
    obtain ⟨mp', hE'', hleaves, hag, hinv''⟩ :=
      stageNestedRecsProvisionGo Aof taOf Inv rest (k + 1) _ mpR hE' hndR.1 hfacts'
        (hInv 0 (cvR, mI, rP) rfl mp.base2 hfresh hinv mpR.base2 hacR)
        (by
          intro i x hx env' m' hfr hiv m₂ hac
          rw [show k + 1 + i = k + (i + 1) from by omega] at hac
          exact hInv (i + 1) x (by simpa using hx) m' hfr hiv m₂ hac)
        (by
          intro i x hx env' mp'' hfr hiv m₂ hac
          rw [show k + 1 + i = k + (i + 1) from by omega] at hac
          exact hreps (i + 1) x (by simpa using hx) mp'' hfr hiv m₂ hac)
    refine ⟨mp', hE'', fun i x hx => ?_, fun n hn => ?_, hinv''⟩
    · cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        rw [hag _ (fun y hy h => hndR.2 y hy h.symm), hacR, Nat.add_zero]
        exact acvalWith_self
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        rw [show k + (i + 1) = k + 1 + i from by omega]
        exact hleaves i x hx
    · rw [hag n (fun x hx => hn x (List.mem_cons_of_mem _ hx)), hacR]
      exact acvalWith_ne (hn (cvR, mI, rP) List.mem_cons_self)

/-! ## The provision and the store, as a swap -/

section Swap

/-- **The provision and the store are a shape-level swap**: the same
names, in the same order, on lookup-comparable environments, differing
only in their rule lists. -/
theorem swapShList_provisionN_storeN :
    ∀ (stores : List (ConstantVal × Nat × Nat × List RecRule)) {env env' : Env},
      ConLeche.SwapShList env.consts env'.consts →
      ConLeche.SwapShList
        (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env).consts
        (ConLeche.storeNestedRecs stores env').consts
  | [], _, _, h => h
  | (cvRa, mI, rP, rules) :: rest, env, env', h => by
    simp only [List.map_cons, ConLeche.provisionNestedRecs, ConLeche.storeNestedRecs]
    exact swapShList_provisionN_storeN rest
      (ConLeche.SwapShList.cons (Or.inr ⟨cvRa, mI, rP, rules, rfl, rfl⟩) h)

/-- **The swap sits at no reserved basis name**: the only entries the
store changes are the block's restored recursors. -/
theorem swapNResS_provisionN_storeN :
    ∀ (stores : List (ConstantVal × Nat × Nat × List RecRule)) {env env' : Env},
      (∀ x ∈ stores, ConLeche.reservedBasisNames.contains x.1.name = false) →
      SwapNResS env env' →
      SwapNResS (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env)
        (ConLeche.storeNestedRecs stores env')
  | [], _, _, _, h => h
  | (cvRa, mI, rP, rules) :: rest, env, env', hres, h => by
    simp only [List.map_cons, ConLeche.provisionNestedRecs, ConLeche.storeNestedRecs]
    refine swapNResS_provisionN_storeN rest (fun x hx => hres x (List.mem_cons_of_mem _ hx)) ?_
    intro n cv mI' rP' rules' h₀ h₃
    by_cases hn : cvRa.name = n
    · refine Or.inr ?_
      show ConLeche.reservedBasisNames.contains n = false
      rw [← hn]
      exact hres (cvRa, mI, rP, rules) List.mem_cons_self
    · rw [find?_cons_of_name_ne (c := .recInfo cvRa mI rP []) hn] at h₀
      rw [find?_cons_of_name_ne (c := .recInfo cvRa mI rP rules) hn] at h₃
      exact h n cv mI' rP' rules' h₀ h₃

/-- The store's lookups: the base environment's, or one of the stored
recursors. -/
theorem storeNestedRecs_find?_inv :
    ∀ {rs : List (ConstantVal × Nat × Nat × List RecRule)} {env : Env} {n : Name}
      {c : ConstantInfo},
      (ConLeche.storeNestedRecs rs env).find? n = some c →
      env.find? n = some c ∨ ∃ r ∈ rs, c = .recInfo r.1 r.2.1 r.2.2.1 r.2.2.2 ∧ r.1.name = n
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
    ∀ {l : List (ConstantVal × Nat × Nat)} {env : Env} {n : Name},
      (∀ x ∈ l, n ≠ x.1.name) →
      (ConLeche.provisionNestedRecs l env).find? n = env.find? n
  | [], _, _, _ => rfl
  | (cvRa, mI, rP) :: rest, env, n, hne => by
    simp only [ConLeche.provisionNestedRecs]
    rw [provisionNestedRecs_find?_of_ne (fun x hx => hne x (List.mem_cons_of_mem _ hx)),
      ConLeche.Env.find?_cons,
      if_neg (fun hh => hne (cvRa, mI, rP) List.mem_cons_self hh.symm)]

end Swap

/-! ## The store: the swap -/

set_option maxHeartbeats 1600000 in
/-- **The restored recursors' store stage**: the carrier at the
provisioned environment crosses to the environment holding the SAME
names WITH their rules (`storeNestedRecs`), by `EnvModelM.swapP`.

`EnvWF` at the store is taken (the Verify lane proves it); the other
three syntactic facts are transported (`swapFacts_of_shList`, whose
`hnew` is the stored rules' own data — their constructors at `env₂`,
lifted into the provision, and their rescue bits, which `hbits` states
at the provision already), the representation clause is the caller's,
and the rule rows are the prefix's own — transported by
`RecRuleLaw.swapP` — plus the block's, which `hlaws` supplies. -/
theorem stageNestedRecsStore {μ : CheckMode} {env₂ : Env}
    {provs : List (ConstantVal × Nat × Nat)} {stores : List (ConstantVal × Nat × Nat × List RecRule)}
    (hsp : stores.map (fun r => (r.1, r.2.1, r.2.2.1)) = provs)
    (mpP : EnvModelM V μ (ConLeche.provisionNestedRecs provs env₂))
    (hwf₃ : ConLeche.EnvWF (ConLeche.storeNestedRecs stores env₂))
    (hfresh : ∀ x ∈ provs, env₂.find? x.1.name = none)
    (hnres : ∀ x ∈ provs, ConLeche.reservedBasisNames.contains x.1.name = false)
    -- every stored rule's constructor is stored at the constructors' environment
    (hctorStored : ∀ r ∈ stores, ∀ rl ∈ r.2.2.2,
      ∃ cvj cnP cnF, env₂.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF))
    -- the rules' rescue bits are the provision's (`recRuleBits` at the provision's lookups)
    (hbits : ∀ r ∈ stores, ∀ rl ∈ r.2.2.2,
      (rl.k = true → ConLeche.recRuleKOf (ConLeche.provisionNestedRecs provs env₂).find? rl.ctor = true) ∧
      (rl.eta = true → ConLeche.recRuleEtaOf (ConLeche.provisionNestedRecs provs env₂).find?
        r.1.name rl.ctor = true))
    (hlaws : ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs stores env₂), m₃.acval = mpP.base2.acval →
      ∀ (φ : Name → Nat) (r : ConstantVal × Nat × Nat × List RecRule), r ∈ stores →
      ∀ rl ∈ r.2.2.2, RecRule.fire rl ≠ .inert → RecRuleLaw m₃ φ r.1.name r.1 r.2.1 r.2.2.1 rl)
    (hreps : ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs stores env₂),
      m₃.acval = mpP.base2.acval → IndReps m₃) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.storeNestedRecs stores env₂),
      mp₃.base2.acval = mpP.base2.acval ∧ mp₃.base2.cvalE = mpP.base2.cvalE := by
  subst hsp
  -- the provision's entries are the stores' own
  have hmemP : ∀ r ∈ stores, ((r.1, r.2.1, r.2.2.1) : ConstantVal × Nat × Nat) ∈
      stores.map (fun r => (r.1, r.2.1, r.2.2.1)) := fun r hr => List.mem_map.mpr ⟨r, hr, rfl⟩
  -- the swap
  have hsw : ConLeche.SwapShList
      (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env₂).consts
      (ConLeche.storeNestedRecs stores env₂).consts :=
    swapShList_provisionN_storeN stores (ConLeche.SwapShList.of_eq env₂.consts)
  have hnresS : SwapNResS
      (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env₂)
      (ConLeche.storeNestedRecs stores env₂) :=
    swapNResS_provisionN_storeN stores (fun x hx => hnres _ (hmemP x hx)) (SwapNResS.of_eq env₂)
  have hcg := ConLeche.SwapShList.congr hsw
  -- the constructors' environment sits inside the provision
  have hmono : ∀ (n : Name) (c : ConstantInfo), env₂.find? n = some c →
      (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env₂).find? n
        = some c := by
    intro n c h
    rw [provisionNestedRecs_find?_of_ne ?ne]
    · exact h
    case ne =>
      intro x hx hn
      have hx₂ := hfresh x hx
      rw [← hn, h] at hx₂
      exact nomatch hx₂
  have hkeep₂ : ∀ (n : Name) (ci : ConstantInfo),
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) → env₂.find? n = some ci →
      (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env₂).find? n
        = some ci :=
    fun n ci _ h => hmono n ci h
  -- the store's own rules: their constructors and their rescue bits
  have hnew : ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      (ConLeche.storeNestedRecs stores env₂).find? n = some (.recInfo cv mI rP rules) →
      (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env₂).find? n
        = some (.recInfo cv mI rP rules) ∨
      ∀ r ∈ rules,
        (∃ cvj cnP cnF,
          (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env₂).find?
            (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF)) ∧
        (r.k = true → ConLeche.recRuleKOf
          (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env₂).find?
          r.ctor = true) ∧
        (r.eta = true → ConLeche.recRuleEtaOf
          (ConLeche.provisionNestedRecs (stores.map (fun r => (r.1, r.2.1, r.2.2.1))) env₂).find?
          n r.ctor = true) := by
    intro n cv mI rP rules hf
    rcases storeNestedRecs_find?_inv hf with h₂ | ⟨x, hx, hc, hn⟩
    · exact Or.inl (hmono _ _ h₂)
    right
    obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
    intro r hr
    obtain ⟨cvj, cnP, cnF, hfc⟩ := hctorStored x hx r hr
    obtain ⟨hkb, heb⟩ := hbits x hx r hr
    exact ⟨⟨cvj, cnP, cnF, hmono _ _ hfc⟩, hkb, by rw [← hn]; exact heb⟩
  obtain ⟨hctors₃, hbp₃, hproj₃⟩ :=
    swapFacts_of_shList hsw hnresS mpP.base2.rec_ctors mpP.base2.basis_pinnedL
      mpP.base2.proj_ok hnew
  -- the rule rows at the swapped carrier
  have hrecP : ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs stores env₂),
      m₃.acval = mpP.base2.acval → ∀ φ : Name → Nat, RecRules m₃ φ := by
    intro m₃ hac φ n cv mI rP rules hf rl hrl hfire
    rcases storeNestedRecs_find?_inv hf with h₂ | ⟨x, hx, hc, hn⟩
    · exact RecRuleLaw.swapP hcg hac
        (mpP.rec_rules φ n cv mI rP rules (hmono _ _ h₂) rl hrl hfire)
    · obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj hc
      rw [← hn]
      exact hlaws m₃ hac φ x hx rl hrl hfire
  exact EnvModelM.swapP mpP hsw hwf₃ hctors₃ hbp₃ hproj₃ hrecP hreps

/-! ## The stage -/

set_option maxHeartbeats 1600000 in
/-- **The restored recursors' stage** (M-D′ D4): the provision
(`stageNestedRecsProvisionGo`) and the store (`stageNestedRecsStore`)
run back to back.  At the end entry `i` carries the leaf `Aof i` and
every other constant keeps the value the constructors' stage gave
it. -/
theorem nestedRecsModel {μ : CheckMode} {env₂ : Env} (mp₂ : EnvModelM V μ env₂)
    (hE₂ : ConLeche.EtaFamiliesClosed env₂)
    {provs : List (ConstantVal × Nat × Nat)} {stores : List (ConstantVal × Nat × Nat × List RecRule)}
    (hsp : stores.map (fun r => (r.1, r.2.1, r.2.2.1)) = provs)
    (hwf₃ : ConLeche.EnvWF (ConLeche.storeNestedRecs stores env₂))
    (hnd : (provs.map (·.1.name)).Nodup)
    (Aof taOf : Nat → (Name → Nat) → AnnotTerm)
    (hfacts : ∀ (i : Nat) (x : ConstantVal × Nat × Nat), provs[i]? = some x →
      env₂.find? x.1.name = none ∧ RestoredCtorStatic x.1 ∧ x.1.type.constsResolve env₂ = true ∧
      NestedCtorLeaf mp₂ x.1 (Aof i) (taOf i))
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop) (hinv₂ : Inv mp₂.base2)
    (hInv : ∀ (i : Nat) (x : ConstantVal × Nat × Nat), provs[i]? = some x →
      ∀ {env' : Env} (m' : EnvModel V env'), env'.find? x.1.name = none → Inv m' →
      ∀ m₂ : EnvModel V ⟨.recInfo x.1 x.2.1 x.2.2 [] :: env'.consts⟩,
        m₂.acval = acvalWith m'.acval x.1.name (Aof i) → Inv m₂)
    (hrepsP : ∀ (i : Nat) (x : ConstantVal × Nat × Nat), provs[i]? = some x →
      ∀ {env' : Env} (mp' : EnvModelM V μ env'), env'.find? x.1.name = none → Inv mp'.base2 →
      ∀ m₂ : EnvModel V ⟨.recInfo x.1 x.2.1 x.2.2 [] :: env'.consts⟩,
        m₂.acval = acvalWith mp'.base2.acval x.1.name (Aof i) →
        IndRepsHead env' (.recInfo x.1 x.2.1 x.2.2 []) m₂)
    (hctorStored : ∀ r ∈ stores, ∀ rl ∈ r.2.2.2,
      ∃ cvj cnP cnF, env₂.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF))
    (hbits : ∀ r ∈ stores, ∀ rl ∈ r.2.2.2,
      (rl.k = true → ConLeche.recRuleKOf (ConLeche.provisionNestedRecs provs env₂).find? rl.ctor = true) ∧
      (rl.eta = true → ConLeche.recRuleEtaOf (ConLeche.provisionNestedRecs provs env₂).find?
        r.1.name rl.ctor = true))
    (hlaws : ∀ (acv : Name → (Name → Nat) → AnnotTerm),
      (∀ (i : Nat) (x : ConstantVal × Nat × Nat), provs[i]? = some x → acv x.1.name = Aof i) →
      (∀ n : Name, (∀ x ∈ provs, n ≠ x.1.name) → acv n = mp₂.base2.acval n) →
      ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs stores env₂), m₃.acval = acv →
      ∀ (φ : Name → Nat) (r : ConstantVal × Nat × Nat × List RecRule), r ∈ stores →
      ∀ rl ∈ r.2.2.2, RecRule.fire rl ≠ .inert → RecRuleLaw m₃ φ r.1.name r.1 r.2.1 r.2.2.1 rl)
    (hrepsS : ∀ mpP : EnvModelM V μ (ConLeche.provisionNestedRecs provs env₂), Inv mpP.base2 →
      (∀ (i : Nat) (x : ConstantVal × Nat × Nat), provs[i]? = some x →
        mpP.base2.acval x.1.name = Aof i) →
      (∀ n : Name, (∀ x ∈ provs, n ≠ x.1.name) → mpP.base2.acval n = mp₂.base2.acval n) →
      ∀ m₃ : EnvModel V (ConLeche.storeNestedRecs stores env₂),
        m₃.acval = mpP.base2.acval → IndReps m₃) :
    ∃ mp₃ : EnvModelM V μ (ConLeche.storeNestedRecs stores env₂),
      (∀ (i : Nat) (x : ConstantVal × Nat × Nat), provs[i]? = some x →
        mp₃.base2.acval x.1.name = Aof i) ∧
      (∀ n : Name, (∀ x ∈ provs, n ≠ x.1.name) → mp₃.base2.acval n = mp₂.base2.acval n) := by
  -- the entries' freshness and names, off the positional facts
  have hfreshAll : ∀ x ∈ provs, env₂.find? x.1.name = none := by
    intro x hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    exact (hfacts i x hi).1
  have hnresAll : ∀ x ∈ provs, ConLeche.reservedBasisNames.contains x.1.name = false := by
    intro x hx
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    exact (hfacts i x hi).2.1.1
  -- the provision
  obtain ⟨mpP, -, hleafP, hagP, hinvP⟩ :=
    stageNestedRecsProvisionGo Aof taOf Inv provs 0 env₂ mp₂ hE₂ hnd
      (by
        intro i x hx
        rw [Nat.zero_add]
        exact hfacts i x hx)
      hinv₂
      (by
        intro i x hx env' m' hfr hiv m₂ hac
        rw [Nat.zero_add] at hac
        exact hInv i x hx m' hfr hiv m₂ hac)
      (by
        intro i x hx env' mp' hfr hiv m₂ hac
        rw [Nat.zero_add] at hac
        exact hrepsP i x hx mp' hfr hiv m₂ hac)
  have hleafP' : ∀ (i : Nat) (x : ConstantVal × Nat × Nat), provs[i]? = some x →
      mpP.base2.acval x.1.name = Aof i := by
    intro i x hx
    have h := hleafP i x hx
    rwa [Nat.zero_add] at h
  -- the store
  obtain ⟨mp₃, hacc, -⟩ :=
    stageNestedRecsStore hsp mpP hwf₃ hfreshAll hnresAll hctorStored hbits
      (hlaws mpP.base2.acval hleafP' hagP) (hrepsS mpP hinvP hleafP' hagP)
  exact ⟨mp₃, fun i x hx => by rw [hacc]; exact hleafP' i x hx,
    fun n hn => by rw [hacc]; exact hagP n hn⟩

end ConLeche.Model
