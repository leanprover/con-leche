import Setlec.SetBase.IndBlockR
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


/-! ## The two folds, run in step

`SwapNResS` is `EnvS.swap`'s last obligation, stated as a relation
between the provisioning's and the install fold's accumulators so the
step-wise induction can maintain it. -/

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
/-- Every rule the per-recursor fold returns carries its facts.

**Task #161 S6**: the six syntactic conjuncts are `iotaRulesFactsR`'s
(`SetBase/IndBlockR.lean`) — one proof, model-free — and only the
fired law is proved here. -/
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
    obtain ⟨hw, hlp, hres, hb, hnest, hctors, -⟩ :=
      iotaRulesFactsR hup j (r :: rest) rules' h rl hrl
    refine ⟨hw, hlp, hres, hb, hnest, hctors, ?_⟩
    obtain ⟨r', rest', hkit, hrec, rfl⟩ := h
    rcases List.mem_cons.mp hrl with heqrl | hrl'
    · subst heqrl
      intro hfire φ
      exact iotaRuleS mS hf hro hIS hup hbnA hself heqfind hkit hfire φ
    · exact (ih (j + 1) rest' hrec rl hrl').2.2.2.2.2.2

/-! ## The two folds, in step -/

/-- **The provisioning and the install fold, run together** — the
[set] instance of `indRecsFoldFacts` (`SetBase/IndBlockR.lean`), at
`RuleFactsS`. -/
theorem indRecsFoldS {μ : CheckMode} {F : Nat} {blockNames : List Name}
    {envSelf envBase : Env} (mS : EnvS V envSelf)
    (hIS : BlockInstalledTT blockNames envSelf mS.cval)
    (hro : RenameOkT mS.cval envSelf (fun n =>
      if blockNames.contains n then n.str "_model" else n))
    (hupB : FoldUpS envBase envSelf)
    (heqfB : envBase.find? eqName = some eqA) :
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
      IndRecsR.IndRecsFoldR μ F blockNames envBase envSelf mS.cval
        envF cvalF checked env₃ cval₃ →
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
        ∀ rl ∈ rules, RuleFactsS V envSelf mS.cval cv mI rP rl :=
  indRecsFoldFacts (RuleFactsS V envSelf mS.cval)
    (fun _cvA _mI _rP rules rules' hbnA hselfA hiot =>
      iotaRulesS mS rfl hro hIS hupB hbnA hselfA heqfB
        0 rules rules' hiot)

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
    denote_env_ext hcg.levelsEq hcg.natEq hcg.strEq hcg.projEq
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
theorem indRecsS (hkey : MemberKeyS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env₂ env₃ : Env}
    {recs : List ConstantInfo} {cval₃ : TConstVal}
    (m : EnvS V env₂) (hI : BlockInstalledTT blockNames env₂ m.cval)
    (hbn : ∀ ci ∈ recs, blockNames.contains ci.name = true)
    (hall : ∀ n, blockNames.contains n = true →
      (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n)
    (hEC : EtaFamiliesClosedO blockNames env₂)
    (hBP : BlockEtaPinned μ blockNames env₂)
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
  obtain ⟨mS, hmScval, hIS, -, -⟩ := provisionRecsS hkey recs m
    hbn hprov hI hEC hBP
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
  have hro := blockRenameOkT hIS hnames
    (fun sn i entry hf => mS.proj_ok.towerFree sn i entry hf)
  -- run the two folds in step
  obtain ⟨hswR, hnresR, rfl, hentR, hentF⟩ :=
    indRecsFoldS mS hIS hro
      (fun n ci hf => Or.inl (provisionRecsS_mono recs hprov n ci hf))
      heqf recs (SwapShList.of_eq env₂.consts)
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
