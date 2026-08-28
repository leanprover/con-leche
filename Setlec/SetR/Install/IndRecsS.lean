import Setlec.SetR.Install.IotaRuleS
import Setlec.SetR.Install.SwapS

/-!
# The recursor-group install, [set] form (task #148, T5, stage 3c)

`indRecsS` turns an `IndRecsR` derivation into the invariant at the
group's installed environment.  The shape is the one stage 3's record
settled and `EnvS.swap` (stage 3a) was built for:

* **provision** the group rule-less (`provisionRecsS`, T5 stage 2) —
  every rule right-hand side is checked against the *whole* group, so
  the self environment must already carry all of it;
* **fire** each checked rule kit through `iotaRuleS` (stage 3b), which
  hands back the `RecRulesV` clause body at that self environment;
* **swap** the checked rule lists onto the provisioned entries
  (`EnvS.swap`).

Everything about the fold that is not about values lives in this
file's first half, as an induction that runs the provisioning and the
install fold *in step*.  That pairing is what makes the accumulators'
correspondence available at each rule kit: `IotaRulesR`'s environment
argument is the install fold's running accumulator, which is the
provisioning's accumulator with some of the group's recursors already
carrying rules — a swap-correspondence, never an inclusion.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-! ## The provisioning's syntactic residue -/

/-- Provisioning only extends: every member's name is checked fresh
(`ConstantValR`'s first conjunct), so earlier lookups survive. -/
theorem provisionRecsS_mono {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ (n : Name) (ci : ConstantInfo),
        envAcc.find? n = some ci → envSelf.find? n = some ci := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h n ci hf
    obtain ⟨rfl, -, -⟩ := h
    exact hf
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h n ci hf
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hrec, -⟩ := h
    obtain ⟨type', ⟨hfresh, -, -, -, -, -, -, -, -, -⟩, rfl, -⟩ := hmv
    exact ih hrec n ci (Env.find?_cons_of_fresh
      (c := .recInfo _ mI rP []) (Option.isNone_iff_eq_none.mp hfresh)
      hf)

/-- Provisioning only extends: stored entries stay stored. -/
theorem provisionRecsS_mem {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ c ∈ envAcc.consts, c ∈ envSelf.consts := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨rfl, -, -⟩ := h
    exact hc
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨cvA, mI, rP, rules, rest', -, -, hprov', -⟩ := h
    exact ih hprov' c (List.mem_cons_of_mem _ hc)

/-- No provisioned member is stored *before* the fold runs. -/
theorem provisionRecsS_fresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ ci ∈ recs, envAcc.find? ci.name = none := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', -⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci₀.name := by rw [hcvA]; rfl
    have hfresh : envAcc.find? cvA.name = none := by
      rw [hnameA]
      exact Option.isNone_iff_eq_none.mp hcv.1
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq, ← hnameA]; exact hfresh
    · rcases hf : envAcc.find? ci.name with _ | ci₂
      · rfl
      · exfalso
        have hnone := ih hprov' ci hci'
        rw [Env.find?_cons_of_fresh (c := .recInfo cvA mI rP [])
          hfresh hf] at hnone
        exact nomatch hnone

/-- Each provisioned member's name passes the two name guards. -/
theorem provisionRecsS_nameGuards {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ ci ∈ recs, ci.name.isProjFnShape = false ∧
        reservedBasisNames.contains ci.name = false := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', -⟩ := h
    obtain ⟨type', hcv, -, -⟩ := id hmv
    rcases List.mem_cons.mp hci with heq | hci'
    · rw [heq]
      exact ⟨hcv.2.2.1, hcv.2.1⟩
    · exact ih hprov' ci hci'

/-- …and so does every group member's. -/
theorem indRecsR_nameGuards {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {cval₂ cval₃ : TConstVal} {recs : List ConstantInfo}
    (h : IndRecsR μ F blockNames env₂ cval₂ recs env₃ cval₃) :
    ∀ ci ∈ recs, ci.name.isProjFnShape = false ∧
      reservedBasisNames.contains ci.name = false := by
  rcases h with ⟨rfl, -, -⟩ | ⟨-, -, envSelf, cvalSelf, checked,
    hprov, -⟩
  · intro ci hci; exact nomatch hci
  · exact provisionRecsS_nameGuards recs hprov

/-- No group member is stored before the group phase runs. -/
theorem indRecsR_fresh {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {cval₂ cval₃ : TConstVal} {recs : List ConstantInfo}
    (h : IndRecsR μ F blockNames env₂ cval₂ recs env₃ cval₃) :
    ∀ ci ∈ recs, env₂.find? ci.name = none := by
  rcases h with ⟨rfl, -, -⟩ | ⟨-, -, envSelf, cvalSelf, checked,
    hprov, -⟩
  · intro ci hci; exact nomatch hci
  · exact provisionRecsS_fresh recs hprov

/-- Every provisioned member is stored. -/
theorem provisionRecsS_stored {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ ci ∈ recs, (envSelf.find? ci.name).isSome = true := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    exact nomatch hci
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h ci hci
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hprov', -⟩ := h
    obtain ⟨type', -, hcvAdef, -⟩ := hmv
    rcases List.mem_cons.mp hci with rfl | hci'
    · have : envSelf.find? cvA.name = some (.recInfo cvA mI rP []) :=
        provisionRecsS_mono rest hprov' _ _
          (Env.find?_cons_self (.recInfo cvA mI rP []) envAcc)
      rw [show ci.name = cvA.name by rw [hcvAdef]; rfl, this]
      rfl
    · exact ih hprov' ci hci'

/-- Each provisioned member is stored rule-less in the self
environment, under a name the member check found unreserved. -/
theorem provisionRecsS_entries {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} {cval : TConstVal}
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      ProvisionRecsR μ F blockNames envAcc cval recs envSelf cvalSelf
        checked →
      ∀ c ∈ checked,
        envSelf.find? c.1.name
          = some (.recInfo c.1 c.2.1 c.2.2.1 []) ∧
        reservedBasisNames.contains c.1.name = false := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨-, -, rfl⟩ := h
    exact nomatch hc
  | cons ci₀ rest ih =>
    intro envAcc cval envSelf cvalSelf checked h c hc
    obtain ⟨cvA, mI, rP, rules, rest', -, hmv, hrec, rfl⟩ := h
    obtain ⟨type', ⟨-, hres, -, -, -, -, -, -, -, -⟩, rfl, -⟩ := hmv
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact ⟨provisionRecsS_mono rest hrec _ _
        (Env.find?_cons_self (.recInfo _ mI rP []) envAcc), hres⟩
    · exact ih hrec c hc'

/-! ## The two folds, run in step

`SwapNResS` is `EnvS.swap`'s last obligation, stated as a relation
between the provisioning's and the install fold's accumulators so the
step-wise induction can maintain it. -/

/-- The reserved-name side condition of the group swap: a genuinely
swapped entry never sits at a pinned basis name. -/
def SwapNResS (env₀ env₃ : Env) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    env₀.find? n = some (.recInfo cv mI rP []) →
    env₃.find? n = some (.recInfo cv mI rP rules) →
    rules = [] ∨ reservedBasisNames.contains n = false

theorem SwapNResS.of_eq (env : Env) : SwapNResS env env := by
  intro n cv mI rP rules h₀ h₃
  rw [h₀] at h₃
  obtain ⟨-, -, -, rfl⟩ := ConstantInfo.recInfo.inj (Option.some.inj h₃)
  exact Or.inl rfl

/-- The install fold's accumulator, read against the self environment:
a lookup either agrees or differs only in a recursor's rule list. -/
def FoldUpS (envAcc envSelf : Env) : Prop :=
  ∀ (n : Name) (ci : ConstantInfo), envAcc.find? n = some ci →
    envSelf.find? n = some ci ∨
    ∃ cv mI' rP' rules rules',
      ci = .recInfo cv mI' rP' rules ∧
      envSelf.find? n = some (.recInfo cv mI' rP' rules')

/-! ## One checked rule's contribution -/

/-- What one checked rule owes the installed environment, stated at
the *self* environment: the `EnvWF` clauses for its right-hand side
and (if nested) its pins, its constructor's storage, and — unless it
is inert — its fired law.  The swap moves all three up unchanged (the
first two modulo `constsResolve`'s `isSome` congruence). -/
def RuleFactsS (V : Type w) [SetTheory V] (envSelf : Env)
    (cvalSelf : TConstVal) (cv : ConstantVal) (mI rP : Nat)
    (rl : RecRule) : Prop :=
  (RecRule.rhs rl).hasFvar = false ∧
  (RecRule.rhs rl).allLevelParamsDefined cv.levelParams = true ∧
  (RecRule.rhs rl).constsResolve envSelf = true ∧
  (RecRule.rhs rl).looseBVarsBounded 0 = true ∧
  (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
    rP ≤ mI ∧
    (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
    (∀ pin ∈ pins, pin.hasFvar = false ∧
      pin.allLevelParamsDefined cv.levelParams = true ∧
      pin.constsResolve envSelf = true ∧
      pin.looseBVarsBounded rP = true) ∧
    ∃ pre nm dom body bm D,
      cv.type.stripPis mI = some (pre, .forallE nm dom body bm) ∧
      dom.getAppFn = .const D lvls ∧
      dom.getAppArgs =
        pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
          (List.range (mI - rP)).map
            (fun i => Expr.bvar (mI - rP - 1 - i))) ∧
  (∃ cvj cnP cnF,
    envSelf.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF)) ∧
  (RecRule.fire rl ≠ .inert → ∀ φ : Name → Nat,
    RecRuleLawV V envSelf cvalSelf φ cv.name cv mI rP rl)

set_option maxHeartbeats 1600000 in
/-- Every rule the per-recursor fold returns carries its facts. -/
theorem iotaRulesS {μ : CheckMode} {F : Nat} {env₂ envSelf : Env}
    (mS : EnvS V envSelf) {blockNames : List Name} {f : Name → Name}
    (hf : f = fun n =>
      if blockNames.contains n then n.str "_model" else n)
    (hro : RenameOkT mS.cval envSelf f)
    (hIS : BlockInstalledTT blockNames envSelf mS.cval)
    (hup : FoldUpS env₂ envSelf)
    {cvA : ConstantVal} {mI rP : Nat}
    (hbnA : blockNames.contains cvA.name = true)
    (hself : envSelf.find? cvA.name = some (.recInfo cvA mI rP []))
    (heqfind : env₂.find? eqName = some eqA) :
    ∀ (j : Nat) (rules rules' : List RecRule),
      IotaRulesR μ F env₂ envSelf mS.cval f cvA.name cvA.levelParams
        cvA.type mI rP j rules rules' →
      ∀ rl ∈ rules', RuleFactsS V envSelf mS.cval cvA mI rP rl := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h rl hrl
    rw [h] at hrl
    exact nomatch hrl
  | cons r rest ih =>
    intro rules' h rl hrl
    obtain ⟨r', rest', hkit, hrec, rfl⟩ := h
    rcases List.mem_cons.mp hrl with heqrl | hrl'
    · -- the head rule
      rw [heqrl]
      obtain ⟨cvjK, cnPK, cnFK, rhsA, hfcK, hnfK, hrb, hrf, hann, hrlp,
        hrres, hstripRhs, hkey, fire, hr'eq, hbranch⟩ := hkit
      have hr'rhs : RecRule.rhs r' = rhsA := by rw [hr'eq]
      have hr'ctor : RecRule.ctor r' = RecRule.ctor r := by rw [hr'eq]
      have hr'fire : RecRule.fire r' = fire := by rw [hr'eq]
      obtain ⟨hrhsAw, hrhsAb⟩ := annotate_syntax hann hrf hrb
      -- the constructor is stored at the self environment
      have hfcS : envSelf.find? (RecRule.ctor r')
          = some (.ctorInfo cvjK cnPK cnFK) := by
        rw [hr'ctor]
        rcases hup _ _ hfcK with h' |
          ⟨cv, mI', rP', rules₀, rules₁, heq, -⟩
        · exact h'
        · exact nomatch heq
      refine ⟨by rw [hr'rhs]; exact hrhsAw, by rw [hr'rhs]; exact hrlp,
        by rw [hr'rhs]; exact hrres, by rw [hr'rhs]; exact hrhsAb, ?_,
        ⟨cvjK, cnPK, cnFK, hfcS⟩, ?_⟩
      · -- the nested shape facts, from `nestedRuleShape`
        intro lvls pins hfireN
        rw [hr'fire] at hfireN
        rcases hbranch with ⟨-, hfireP, -⟩ | ⟨-, hrest⟩
        · rw [hfireP] at hfireN; exact nomatch hfireN
        rcases hrest with ⟨hfireI, -⟩ | ⟨lvls₀, pins₀, hfireN₀, hthmN⟩
        · rw [hfireI] at hfireN; exact nomatch hfireN
        rw [hfireN₀] at hfireN
        obtain ⟨rfl, rfl⟩ := RecRuleFire.nested.inj hfireN
        obtain ⟨hshape, -⟩ := hthmN
        obtain ⟨hrPmI, hlvls, hpins, pre, nm, dom, body, bm, D, hstrip,
          hfn, hargs, -⟩ := nestedRuleShape_inv hshape
        exact ⟨hrPmI, hlvls, hpins, pre, nm, dom, body, bm, D, hstrip,
          hfn, hargs⟩
      · -- the fired law
        intro hfire φ
        exact iotaRuleS mS hf hro hIS hup hbnA hself heqfind
          ⟨cvjK, cnPK, cnFK, rhsA, hfcK, hnfK, hrb, hrf, hann, hrlp,
            hrres, hstripRhs, hkey, fire, hr'eq, hbranch⟩ hfire φ
    · exact ih (j + 1) rest' hrec rl hrl'

/-! ## The two folds, in step -/

set_option maxHeartbeats 1600000 in
/-- **The provisioning and the install fold, run together.**  The
pairing is what makes each rule kit's environment readable: the
install fold's accumulator is the provisioning's accumulator with some
of the group's recursors already ruled, which is a swap
correspondence (`FoldUpS`), never an inclusion. -/
theorem indRecsFoldS {μ : CheckMode} {F : Nat} {blockNames : List Name}
    {envSelf : Env} (mS : EnvS V envSelf)
    (hIS : BlockInstalledTT blockNames envSelf mS.cval)
    (hro : RenameOkT mS.cval envSelf (fun n =>
      if blockNames.contains n then n.str "_model" else n)) :
    ∀ (recs : List ConstantInfo) {envP envF env₃ : Env}
      {cvalF cval₃ : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      SwapShList envP.consts envF.consts →
      SwapNResS envP envF →
      FoldUpS envF envSelf →
      (∀ (n : Name) (ci : ConstantInfo),
        envP.find? n = some ci → envSelf.find? n = some ci) →
      envP.find? eqName = some eqA →
      (∀ c ∈ envF.consts, c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
          c = .recInfo cv mI rP rules ∧
          ∀ rl ∈ rules, RuleFactsS V envSelf mS.cval cv mI rP rl) →
      (∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
        (rules : List RecRule),
        envF.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        ∀ rl ∈ rules, RuleFactsS V envSelf mS.cval cv mI rP rl) →
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsR μ F blockNames envP cvalF recs envSelf mS.cval
        checked →
      IndRecsR.IndRecsFoldR μ F blockNames envSelf mS.cval envF cvalF
        checked env₃ cval₃ →
      SwapShList envSelf.consts env₃.consts ∧
      SwapNResS envSelf env₃ ∧
      mS.cval = cval₃ ∧
      (∀ c ∈ env₃.consts, c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
          c = .recInfo cv mI rP rules ∧
          ∀ rl ∈ rules, RuleFactsS V envSelf mS.cval cv mI rP rl) ∧
      ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
        (rules : List RecRule),
        env₃.find? n = some (.recInfo cv mI rP rules) →
        envSelf.find? n = some (.recInfo cv mI rP rules) ∨
        ∀ rl ∈ rules, RuleFactsS V envSelf mS.cval cv mI rP rl := by
  intro recs
  induction recs with
  | nil =>
    intro envP envF env₃ cvalF cval₃ checked hsw hnres hupF hupP heqP
      hents hentF hbn hprov hfold
    obtain ⟨rfl, rfl, rfl⟩ := hprov
    obtain ⟨rfl, rfl⟩ := hfold
    exact ⟨hsw, hnres, rfl, hents, hentF⟩
  | cons ci₀ rest ih =>
    intro envP envF env₃ cvalF cval₃ checked hsw hnres hupF hupP heqP
      hents hentF hbn hprov hfold
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hprov', rfl⟩ := hprov
    obtain ⟨rules', hiot, hfold'⟩ := hfold
    obtain ⟨type', ⟨hfresh0, hres0, -, -, -, -, -, -, -, -⟩, hcvAdef,
      -⟩ := hmv
    have hnameA : cvA.name = ci₀.toConstantVal.name := by
      rw [hcvAdef]
    have hfreshP : envP.find? cvA.name = none := by
      rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfresh0
    have hres : reservedBasisNames.contains cvA.name = false := by
      rw [hnameA]; exact hres0
    have hcg : SwapCongr envP envF := SwapShList.congr hsw
    -- the provisioned entry, at the self environment
    have hselfA : envSelf.find? cvA.name
        = some (.recInfo cvA mI rP []) :=
      provisionRecsS_mono rest hprov' _ _
        (Env.find?_cons_self (.recInfo cvA mI rP []) envP)
    have hbnA : blockNames.contains cvA.name = true := by
      rw [hnameA]; exact hbn ci₀ List.mem_cons_self
    have heqfF : envF.find? eqName = some eqA :=
      hcg.findUp eqName eqA heqP
        (fun _ _ _ _ h => ConstantInfo.noConfusion h)
    -- this recursor's rules, fired
    have hfacts := iotaRulesS mS rfl hro hIS hupF hbnA hselfA heqfF
      0 rules rules' hiot
    -- the two accumulators advance in step
    have hfreshF : envF.find? cvA.name = none := by
      rcases hF : envF.find? cvA.name with _ | ciF
      · rfl
      · have := hcg.isSomeEq cvA.name
        rw [hF, hfreshP] at this
        exact nomatch this.symm
    refine ?_
    have hsw' : SwapShList
        (Env.consts ⟨.recInfo cvA mI rP [] :: envP.consts⟩)
        (Env.consts ⟨.recInfo cvA mI rP rules' :: envF.consts⟩) :=
      SwapShList.cons (Or.inr ⟨cvA, mI, rP, rules', rfl, rfl⟩) hsw
    have hnres' : SwapNResS ⟨.recInfo cvA mI rP [] :: envP.consts⟩
        ⟨.recInfo cvA mI rP rules' :: envF.consts⟩ := by
      intro n cv mI₀ rP₀ rules₀ h₀ h₃
      rw [Env.find?_cons] at h₀ h₃
      split at h₀
      · next hn =>
        rw [if_pos (show (ConstantInfo.recInfo cvA mI rP rules').name
          = n from hn)] at h₃
        obtain ⟨rfl, -, -, -⟩ :=
          ConstantInfo.recInfo.inj (Option.some.inj h₀)
        exact Or.inr (by rw [← hn]; exact hres)
      · next hn =>
        rw [if_neg (show ¬(ConstantInfo.recInfo cvA mI rP rules').name
          = n from hn)] at h₃
        exact hnres n cv mI₀ rP₀ rules₀ h₀ h₃
    have hupF' : FoldUpS ⟨.recInfo cvA mI rP rules' :: envF.consts⟩
        envSelf := by
      intro n ci hfx
      rw [Env.find?_cons] at hfx
      split at hfx
      · next hn =>
        obtain rfl := Option.some.inj hfx
        exact Or.inr ⟨cvA, mI, rP, rules', [], rfl, by
          rw [← hn]; exact hselfA⟩
      · exact hupF n ci hfx
    have hupP' : ∀ (n : Name) (ci : ConstantInfo),
        (Env.find? ⟨.recInfo cvA mI rP [] :: envP.consts⟩ n) = some ci →
        envSelf.find? n = some ci := by
      intro n ci hfx
      rw [Env.find?_cons] at hfx
      split at hfx
      · next hn =>
        obtain rfl := Option.some.inj hfx
        rw [← hn]; exact hselfA
      · exact hupP n ci hfx
    have heqP' : Env.find? ⟨.recInfo cvA mI rP [] :: envP.consts⟩ eqName
        = some eqA :=
      Env.find?_cons_of_fresh (c := .recInfo _ mI rP []) hfreshP heqP
    have hents' : ∀ c ∈ (Env.consts
        ⟨.recInfo cvA mI rP rules' :: envF.consts⟩),
        c ∈ envSelf.consts ∨
        ∃ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
          c = .recInfo cv mI rP rules ∧
          ∀ rl ∈ rules, RuleFactsS V envSelf mS.cval cv mI rP rl := by
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact Or.inr ⟨cvA, mI, rP, rules', rfl, hfacts⟩
      · exact hents c hc'
    have hentF' : ∀ (n : Name) (cv : ConstantVal) (mI₀ rP₀ : Nat)
        (rules₀ : List RecRule),
        Env.find? ⟨.recInfo cvA mI rP rules' :: envF.consts⟩ n
          = some (.recInfo cv mI₀ rP₀ rules₀) →
        envSelf.find? n = some (.recInfo cv mI₀ rP₀ rules₀) ∨
        ∀ rl ∈ rules₀, RuleFactsS V envSelf mS.cval cv mI₀ rP₀ rl := by
      intro n cv mI₀ rP₀ rules₀ hfx
      rw [Env.find?_cons] at hfx
      split at hfx
      · obtain ⟨rfl, rfl, rfl, rfl⟩ :=
          ConstantInfo.recInfo.inj (Option.some.inj hfx)
        exact Or.inr hfacts
      · exact hentF n cv mI₀ rP₀ rules₀ hfx
    exact ih hsw' hnres' hupF' hupP' heqP' hents' hentF'
      (fun ci hci => hbn ci (List.mem_cons_of_mem _ hci)) hprov' hfold'

/-! ## The group install -/

/-- A fired law reads the environment only through `denote` and the
constructor's lookup, so it crosses the rule-list swap. -/
theorem RecRuleLawV.swapS {env₀ env₃ : Env} (hcg : SwapCongr env₀ env₃)
    {cval : TConstVal} {φ : Name → Nat} {n : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule}
    (h : RecRuleLawV V env₀ cval φ n cv mI rP rl) :
    RecRuleLawV V env₃ cval φ n cv mI rP rl := by
  have hde : ∀ (d : Nat) (e : Expr),
      denote cval env₀ φ d e = denote cval env₃ φ d e :=
    denote_env_ext hcg.levelsEq hcg.natEq hcg.strEq
  have hdeC : ∀ e : Expr,
      denoteClosed cval env₀ φ e = denoteClosed cval env₃ φ e :=
    fun e => hde 0 e
  obtain ⟨hle, h⟩ := h
  refine ⟨hle, ?_⟩
  intro us hus
  obtain ⟨R, hR, hlaw⟩ := h us hus
  refine ⟨R, by rw [← hdeC]; exact hR, ?_⟩
  intro cvj cnP cnF hfc usj ρ xs ys TV TVj restR restC hx hy hu hlev
    hplain hnested hidx hTV hTVj hfitR hfitC
  rw [← hdeC] at hTV hTVj
  refine hlaw cvj cnP cnF
    (hcg.findDown _ _ hfc (fun _ _ _ _ hcon => nomatch hcon)) usj ρ xs
    ys TV TVj restR restC hx hy hu hlev hplain ?_ hidx hTV hTVj hfitR
    hfitC
  intro lvls pins hfr i hi vp hvp hb
  rw [hde] at hvp
  exact hnested lvls pins hfr i hi vp hvp hb

set_option maxHeartbeats 3200000 in
/-- **The recursor-group phase**: provision, fire, swap. -/
theorem indRecsS (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo} {cval₃ : TConstVal}
    (m : EnvS V env₂) (hI : BlockInstalledTT blockNames env₂ m.cval)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hall : ∀ n, blockNames.contains n = true →
      (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n)
    (h : IndRecsR μ F blockNames env₂ m.cval recs env₃ cval₃) :
    ∃ m₃ : EnvS V env₃,
      m₃.cval = cval₃ ∧ BlockInstalledTT blockNames env₃ cval₃ ∧
      -- what the group *preserves* (the `DeclIndS` assembly's
      -- `EtaPins.transport` premise, and the projection phase's
      -- lookups): a non-recursor entry survives verbatim, every
      -- stored name stays stored, and the group's own members land
      (∀ (n : Name) (ci : ConstantInfo), env₂.find? n = some ci →
        (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
        env₃.find? n = some ci) ∧
      (∀ n : Name,
        (env₂.find? n).isSome = true → (env₃.find? n).isSome = true) ∧
      (∀ ci ∈ recs, (env₃.find? ci.name).isSome = true) := by
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨-, heqf, envSelf, cvalSelf, checked,
    hprov, hfold⟩
  · exact ⟨m, rfl, hI, fun n ci hf _ => hf, fun n hn => hn,
      fun ci hci => nomatch hci⟩
  obtain ⟨mS, hmScval, hIS⟩ := provisionRecsS hkey heta recs m
    hbn hprov hI
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
  -- the block renaming is sound at the provisional environment
  have hro : RenameOkT mS.cval envSelf (fun n =>
      if blockNames.contains n then n.str "_model" else n) := by
    refine ⟨?_, ?_, ?_⟩
    · intro n ciS hfS
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        obtain ⟨cvmS, mvalS, hmS, hfmS, hlpsS, -, -⟩ := hIS n hc ciS hfS
        exact ⟨.defnInfo cvmS mvalS hmS, hfmS, hlpsS⟩
      · rw [if_neg hc]
        exact ⟨ciS, hfS, rfl⟩
    · intro n hfS
      dsimp only
      by_cases hc : blockNames.contains n = true
      · have := hnames n hc
        rw [hfS] at this
        exact nomatch this
      · rw [if_neg hc]
        exact hfS
    · intro n ψ
      dsimp only
      by_cases hc : blockNames.contains n = true
      · rw [if_pos hc]
        rcases hfS : envSelf.find? n with _ | ciS
        · have := hnames n hc
          rw [hfS] at this
          exact nomatch this
        · obtain ⟨-, -, -, -, -, -, hvS⟩ := hIS n hc ciS hfS
          exact (hvS ψ).symm
      · rw [if_neg hc]
  -- run the two folds in step
  obtain ⟨hswR, hnresR, rfl, hentR, hentF⟩ :=
    indRecsFoldS mS hIS hro recs (SwapShList.of_eq env₂.consts)
      (SwapNResS.of_eq env₂)
      (fun n ci hf => Or.inl (provisionRecsS_mono recs hprov n ci hf))
      (provisionRecsS_mono recs hprov) heqf
      (fun c hc => Or.inl (provisionRecsS_mem recs hprov c hc))
      (fun n cv mI rP rules hf =>
        Or.inl (provisionRecsS_mono recs hprov n _ hf))
      hbn hprov hfold
  have hcg : SwapCongr envSelf env₃ := SwapShList.congr hswR
  -- the swapped environment's three global facts
  have hres₃ : ∀ e : Expr, e.constsResolve envSelf = true →
      e.constsResolve env₃ = true := by
    intro e he
    rw [← Expr.constsResolve_congr hcg.isSomeEq]
    exact he
  have hwf₃ : EnvWF env₃ := by
    intro c hc
    rcases hentR c hc with hcS | ⟨cv, mI, rP, rules, rfl, hfacts⟩
    · -- an unswapped entry: its own facts, resolution transported
      obtain ⟨hSw, hSlp, hSres, hSb, hSdef, hSrec, hSthm⟩ := mS.wf c hcS
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb, ?_, ?_, ?_⟩
      · intro cv v hint heq
        obtain ⟨d1, d2, d3, d4⟩ := hSdef cv v hint heq
        exact ⟨d1, d2, hres₃ _ d3, d4⟩
      · intro cv mI rP rules heq r hr
        obtain ⟨r1, r2, r3, r4, r5⟩ := hSrec cv mI rP rules heq r hr
        refine ⟨r1, r2, hres₃ _ r3, r4, ?_⟩
        intro lvls pins hfr
        obtain ⟨n1, n2, n3, n4⟩ := r5 lvls pins hfr
        refine ⟨n1, n2, ?_, n4⟩
        intro pin hpin
        obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
        exact ⟨p1, p2, hres₃ _ p3, p4⟩
      · intro cv v heq
        obtain ⟨t1, t2, t3, t4⟩ := hSthm cv v heq
        exact ⟨t1, t2, hres₃ _ t3, t4⟩
    · -- a swapped recursor: the *type* facts come from the provisional
      -- entry, the *rule* facts from the fired kits
      obtain ⟨c₀, hc₀, hpair⟩ := swapSh_mem_corr hswR _ hc
      obtain ⟨hSw, hSlp, hSres, hSb, -, -, -⟩ := mS.wf c₀ hc₀
      have hcvt : c₀.toConstantVal = cv := by
        rcases hpair with rfl | ⟨cv', mI', rP', rules', rfl, heq⟩
        · rfl
        · obtain ⟨rfl, -, -, -⟩ := ConstantInfo.recInfo.inj heq
          rfl
      rw [hcvt] at hSw hSlp hSres hSb
      refine ⟨hSw, hSlp, hres₃ _ hSres, hSb,
        fun _ _ _ hcon => ConstantInfo.noConfusion hcon, ?_,
        fun _ _ hcon => ConstantInfo.noConfusion hcon⟩
      intro cv' mI' rP' rules' heq r hr
      obtain ⟨rfl, rfl, rfl, rfl⟩ := ConstantInfo.recInfo.inj heq
      obtain ⟨w1, w2, w3, w4, w5, -, -⟩ := hfacts r hr
      refine ⟨w1, w2, hres₃ _ w3, w4, ?_⟩
      intro lvls pins hfr
      obtain ⟨n1, n2, n3, n4⟩ := w5 lvls pins hfr
      refine ⟨n1, n2, ?_, n4⟩
      intro pin hpin
      obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
      exact ⟨p1, p2, hres₃ _ p3, p4⟩
  have hctors₃ : RecCtorsStored env₃ := by
    intro n cv mI rP rules hf r hr
    rcases hentF n cv mI rP rules hf with hfS | hfacts
    · obtain ⟨cvj, cnP, cnF, hfc⟩ :=
        mS.rec_ctors n cv mI rP rules hfS r hr
      exact ⟨cvj, cnP, cnF, hcg.findUp _ _ hfc
        (fun _ _ _ _ hcon => nomatch hcon)⟩
    · obtain ⟨-, -, -, -, -, ⟨cvj, cnP, cnF, hfc⟩, -⟩ := hfacts r hr
      exact ⟨cvj, cnP, cnF, hcg.findUp _ _ hfc
        (fun _ _ _ _ hcon => nomatch hcon)⟩
  have hrec₃ : ∀ φ : Name → Nat, RecRulesV V env₃ mS.cval φ := by
    intro φ n cv mI rP rules hf rl hrl hfire
    rcases hentF n cv mI rP rules hf with hfS | hfacts
    · exact RecRuleLawV.swapS hcg
        (mS.rec_rules φ n cv mI rP rules hfS rl hrl hfire)
    · obtain ⟨-, -, -, -, -, -, hlaw⟩ := hfacts rl hrl
      rw [← Env.find?_name hf]
      exact RecRuleLawV.swapS hcg (hlaw hfire φ)
  refine ⟨mS.swap hswR hwf₃ hctors₃ hrec₃ hnresR, rfl, ?_,
    (fun n ci hf hnr => hcg.findUp n ci
      (provisionRecsS_mono recs hprov n ci hf) hnr),
    (fun n hn => by
      rw [← hcg.isSomeEq n]
      rcases hf : env₂.find? n with _ | ci
      · rw [hf] at hn; exact nomatch hn
      · rw [provisionRecsS_mono recs hprov n ci hf]; rfl),
    (fun ci hci => by
      rw [← hcg.isSomeEq ci.name]
      exact provisionRecsS_stored recs hprov ci hci)⟩
  -- the block invariant survives the swap
  intro n hn ci₃ hf₃
  rcases swapSh_find?_corr hswR n with heq |
    ⟨cv, mI, rP, rules, h₀, h₃, -⟩
  · rw [heq] at hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ := hIS n hn ci₃ hf₃
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm (fun _ _ _ _ hcon => nomatch hcon),
      hlps, hren, hv⟩
  · rw [h₃] at hf₃
    obtain rfl := Option.some.inj hf₃
    obtain ⟨cvm, mval, hm, hfm, hlps, hren, hv⟩ :=
      hIS n hn _ h₀
    exact ⟨cvm, mval, hm,
      hcg.findUp _ _ hfm (fun _ _ _ _ hcon => nomatch hcon),
      hlps, hren, hv⟩

end Setlec.SetR
