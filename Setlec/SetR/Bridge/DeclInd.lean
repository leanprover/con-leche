import Setlec.SetR.Bridge.Decl
import Setlec.SetR.Install.DeclIndS

/-!
# The `indDecl` bridge (task #148, T6): the interleaved walk

Finding 8: `IndMembersR` carries a `ConstantValR` at **each
intermediate environment** of the member fold, whose `Infer`/`DefEq`
conjuncts only `checkBridge` produces and only at an `EnvR` *there* —
which nothing builds except by projection from an `EnvS`, i.e. from
the install layer that consumes the very relation being built.  The
bridge and the install therefore cannot meet at the relation; they
have to walk together.

The recognition rule the finding leaves behind: **a bridge must
interleave with its install exactly when the relation it produces
quantifies over environments the fold creates.**  Check it by asking,
of each conjunct of the target relation, which environment its
lookups and derivations are at.

So each fold below runs the checker's own step, bridges it at the
current invariant's `EnvR`, installs it, and recurses — accumulating
the relation *and* the invariant.  Every sub-theorem is the install
layer's, unchanged; only the orchestration is written a second time.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The member fold, walked.**  `indMembersS`' induction with
`memberValR_of` inserted at each step to *produce* the front door
instead of consuming it. -/
theorem indMembersRS (hkey : MemberKeyS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} (m : EnvS V env)
      {env₂ : Env},
      (∀ ci ∈ members, blockNames.contains ci.name = true) →
      (∀ (cv : ConstantVal) (caps₂ : IndCaps),
        ConstantInfo.indInfo cv caps₂ ∈ members →
        EtaPins μ env cv.name cv.levelParams caps ∧
          (caps.eta = true →
            blockNames.contains caps.etaCtor = true) ∧
          (caps.eta = true → 0 < caps.etaFields →
            env.find? (projFnName cv.name 0) = none)) →
      BlockInstalledTT blockNames env m.cval →
      EtaFamiliesClosedO blockNames env →
      BlockEtaPinned μ blockNames env →
      members.foldlM (checkIndMember (m := CheckM) (fueledOps μ F)
        blockNames caps) env = .ok env₂ →
      ∃ (cval₂ : TConstVal) (m₂ : EnvS V env₂),
        IndMembersR μ F blockNames caps env m.cval members env₂ cval₂ ∧
        m₂.cval = cval₂ ∧ BlockInstalledTT blockNames env₂ cval₂ ∧
        EtaFamiliesClosedO blockNames env₂ ∧
        BlockEtaPinned μ blockNames env₂ := by
  intro members
  induction members with
  | nil =>
    intro env m env₂ _ _ hI hEC hBP h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨m.cval, m, ⟨rfl, rfl⟩, rfl, hI, hEC, hBP⟩
  | cons ci rest ih =>
    intro env m env₂ hbn hp hI hEC hBP h
    simp only [List.foldlM, Bind.bind, Except.bind, checkIndMember] at h
    revert h
    cases hmv0 : checkMemberVal (m := CheckM) (fueledOps μ F) blockNames
        env ci.toConstantVal with
    | error e => intro h; exact nomatch h
    | ok cvA =>
      intro h
      have hmv : MemberValR μ F env m.cval blockNames
          ci.toConstantVal cvA := memberValR_of m.toEnvR hmv0
      obtain ⟨type', hcv, hcvA, -⟩ := id hmv
      have hnameA : cvA.name = ci.toConstantVal.name := by rw [hcvA]
      have hfreshA : env.find? cvA.name = none := by
        rw [hnameA]
        exact Option.isNone_iff_eq_none.mp hcv.1
      have hbnA : blockNames.contains cvA.name = true := by
        rw [hnameA]; exact hbn ci List.mem_cons_self
      have hpshapeA : cvA.name.isProjFnShape = false := by
        rw [hnameA]; exact hcv.2.2.1
      cases ci with
      | indInfo cv caps' =>
        simp only [pure, Except.pure] at h
        obtain ⟨m₁, hm₁cval, hI₁, hEC₁, hBP₁⟩ :=
          memberInstallS hkey m hmv
          hI hbnA
          (fun caps₃ heq => by
            obtain ⟨-, -, -, rfl⟩ := ConstantInfo.indInfo.inj heq
            exact hp cv caps' List.mem_cons_self)
          hEC hBP rfl rfl (Or.inl ⟨caps, rfl⟩)
        obtain ⟨cval₂, m₂, hrel, hm₂, hI₂, hEC₂, hBP₂⟩ :=
          ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
            (fun cv₂ caps₂ hmem => etaMemberData_step hfreshA hpshapeA
              (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)))
            (by rw [hm₁cval]; exact hI₁) hEC₁ hBP₁ h
        exact ⟨cval₂, m₂, ⟨cvA, hmv, by rw [← hm₁cval]; exact hrel⟩,
          hm₂, hI₂, hEC₂, hBP₂⟩
      | ctorInfo cv nP nF =>
        simp only [pure, Except.pure] at h
        obtain ⟨m₁, hm₁cval, hI₁, hEC₁, hBP₁⟩ :=
          memberInstallS hkey m hmv
          hI hbnA (fun caps₃ heq => ConstantInfo.noConfusion heq)
          hEC hBP rfl rfl (Or.inr (Or.inl ⟨nP, nF, rfl⟩))
        obtain ⟨cval₂, m₂, hrel, hm₂, hI₂, hEC₂, hBP₂⟩ :=
          ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
            (fun cv₂ caps₂ hmem => etaMemberData_step hfreshA hpshapeA
              (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)))
            (by rw [hm₁cval]; exact hI₁) hEC₁ hBP₁ h
        exact ⟨cval₂, m₂, ⟨cvA, hmv, by rw [← hm₁cval]; exact hrel⟩,
          hm₂, hI₂, hEC₂, hBP₂⟩
      | axiomInfo cv | defnInfo cv v hint | thmInfo cv v
      | recInfo cv mI rP rules | projInfo e =>
        simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## The provisioning fold

The second of the three interleaved walks, and the last one that
*must* interleave: `ProvisionRecsR`'s per-recursor front door
(`MemberValR`) sits at the accumulator, which the fold grows.

The rules fold that follows it does **not** interleave, and that is
worth stating because it halves what is left.  `IndRecsFoldR` passes
`envSelf`/`cvalSelf` — not the accumulator's — to `IotaRulesR`, so
every *semantic* conjunct of a rule (`denoteClosed cval envSelf …`,
`Infer μ envSelf cval …`) lives at the **fixed** self environment the
provisioning produced.  What varies with the accumulator is only
`env'.find? r.ctor`, a lookup.  One `EnvR envSelf` therefore serves
the whole rules fold, and the recognition rule's check comes out
negative for it. -/

/-- **The provisioning fold, walked.** -/
theorem provisionRecsRS (hkey : MemberKeyS V)
    {μ : CheckMode} {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} (m : EnvS V envAcc)
      {envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      BlockInstalledTT blockNames envAcc m.cval →
      EtaFamiliesClosedO blockNames envAcc →
      BlockEtaPinned μ blockNames envAcc →
      provisionRecs (m := CheckM) (fueledOps μ F) blockNames envAcc recs
        = .ok (envSelf, checked) →
      ∃ (cvalSelf : TConstVal) (mS : EnvS V envSelf),
        ProvisionRecsR μ F blockNames envAcc m.cval recs envSelf
          cvalSelf checked ∧
        mS.cval = cvalSelf ∧
        BlockInstalledTT blockNames envSelf cvalSelf ∧
        EtaFamiliesClosedO blockNames envSelf ∧
        BlockEtaPinned μ blockNames envSelf := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc m envSelf checked _ hI hEC hBP h
    simp only [provisionRecs, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m.cval, m, ⟨rfl, rfl, rfl⟩, rfl, hI, hEC, hBP⟩
  | cons ci rest ih =>
    intro envAcc m envSelf checked hbn hI hEC hBP h
    cases ci with
    | recInfo cv mI rP rules =>
      simp only [provisionRecs, Bind.bind, Except.bind] at h
      revert h
      cases hmv0 : checkMemberVal (m := CheckM) (fueledOps μ F)
          blockNames envAcc (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal with
      | error e => intro h; exact nomatch h
      | ok cvA =>
        intro h
        dsimp only at h
        have hmv : MemberValR μ F envAcc m.cval blockNames
            (ConstantInfo.recInfo cv mI rP rules).toConstantVal cvA :=
          memberValR_of m.toEnvR hmv0
        obtain ⟨type', hcv, hcvA, -⟩ := id hmv
        have hnameA : cvA.name = (ConstantInfo.recInfo cv mI rP
            rules).toConstantVal.name := by rw [hcvA]
        obtain ⟨m₁, hm₁cval, hI₁, hEC₁, hBP₁⟩ :=
          memberInstallS hkey m hmv
          hI (by rw [hnameA]; exact hbn _ List.mem_cons_self)
          (fun caps₃ heq => ConstantInfo.noConfusion heq)
          hEC hBP rfl rfl (Or.inr (Or.inr ⟨mI, rP, rfl⟩))
        cases hrest : provisionRecs (m := CheckM) (fueledOps μ F)
            blockNames ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩
            rest with
        | error e => rw [hrest] at h; exact nomatch h
        | ok p =>
          rw [hrest] at h
          simp only [pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨cvalSelf, mS, hrel, hmS, hIS, hECS, hBPS⟩ :=
            ih m₁
              (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
              (by rw [hm₁cval]; exact hI₁) hEC₁ hBP₁ hrest
          exact ⟨cvalSelf, mS,
            ⟨cvA, mI, rP, rules, p.2, rfl, hmv,
              by rw [← hm₁cval]; exact hrel, rfl⟩,
            hmS, hIS, hECS, hBPS⟩
    | axiomInfo cv | defnInfo cv v hint | thmInfo cv v
    | indInfo cv c | ctorInfo cv nP nF | projInfo e =>
      simp [provisionRecs, throw, throwThe, MonadExceptOf.throw] at h

/-- **The projection-function fold, walked.**  `projInstallS`'
induction with `projFnR_of` inserted at each step.

Finding 8's scorecard put `ProjFnR` in the interleave column and the
plain form confirms it from the other side: a `ProjFnR` at a
*universally quantified* valuation is not provable at all (its rule
front door and its sides pack are semantic), so the earlier
`projInstallR_of`, parametric in that obligation, was vacuously
premised — the assembly is the vacuity gate, and it fired here. -/
theorem projInstallRS {μ : CheckMode} {F : Nat} {T ctorName : Name}
    {lps : List Name} {nP nF : Nat} {blockNames : List Name}
    (hTblock : blockNames.contains T = true)
    (hbshape : ∀ n, blockNames.contains n = true →
      n.isProjFnShape = false) :
    ∀ (fields : List Nat) {env' : Env} (m : EnvS V env') {env₄ : Env},
      fields.foldlM (installProjFnStep (m := CheckM) μ (fueledOps μ F)
        T ctorName lps nP nF) env' = .ok env₄ →
      ProjPhaseInvS T ctorName nF env' m.cval →
      BlockInstalledTT blockNames env' m.cval →
      (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
        EtaPins μ env' T cvT.levelParams capsT) →
      (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
        capsT.eta = true → blockNames.contains capsT.etaCtor = true) →
      (∀ cvT capsT, env'.find? T = some (.indInfo cvT capsT) →
        capsT.eta = true → capsT.etaFields = nF) →
      ∃ (cval₄ : TConstVal) (m₄ : EnvS V env₄),
        ProjInstallR μ F T ctorName lps nP nF env' m.cval fields env₄
          cval₄ ∧
        m₄.cval = cval₄ ∧
        ProjPhaseInvS T ctorName nF env₄ cval₄ ∧
        BlockInstalledTT blockNames env₄ cval₄ := by
  intro fields
  induction fields with
  | nil =>
    intro env' m env₄ h hinv hIB hpinsT hCblock hFields
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨m.cval, m, ⟨rfl, rfl⟩, rfl, hinv, hIB⟩
  | cons i rest ih =>
    intro env' m env₄ h hinv hIB hpinsT hCblock hFields
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hstep : installProjFnStep (m := CheckM) μ (fueledOps μ F) T
        ctorName lps nP nF env' i with
    | error e => intro h; exact nomatch h
    | ok env'' => ?_
    intro h
    by_cases hm : (env'.find? (projModelName T i)).isSome = true
    case neg =>
      -- the skip branch: the step is the identity
      have henv : env'' = env' := by
        simp only [installProjFnStep, if_neg hm, pure, Except.pure,
          Except.ok.injEq] at hstep
        exact hstep.symm
      subst henv
      obtain ⟨cval₄, m₄, hrec, hm₄, hinv₄, hIB₄⟩ :=
        ih m h hinv hIB hpinsT hCblock hFields
      refine ⟨cval₄, m₄, ⟨env'', m.cval, Or.inr ⟨?_, rfl, rfl⟩,
        hrec⟩, hm₄, hinv₄, hIB₄⟩
      revert hm
      cases (env''.find? (projModelName T i)) <;> simp
    -- the install branch
    have hchk : checkProjFn μ (fueledOps μ F) env' T ctorName lps nP
        nF i = .ok env'' := by
      simp only [installProjFnStep, if_pos hm] at hstep
      exact hstep
    have hR := projFnR_of m.toEnvR hchk
    obtain ⟨m₁, hm₁cval, hinv₁, hIB₁⟩ :=
      projFnS m hR hinv hIB hTblock hbshape hpinsT hCblock hFields
    -- the block-level premises, re-established (`projInstallS`')
    obtain ⟨cvj, mcv, mval, mhint, pty, rhsA, hctor, hfm, hmlps,
      hpnone, hTf, -, -, -, -, -, -, -, -, hilt, -, -, henv⟩ :=
      id hR
    have hfresh : env'.find? (projFnName T i) = none :=
      Option.isNone_iff_eq_none.mp hpnone
    have hTne : T ≠ projFnName T i := by
      intro hh
      rw [hh, hfresh] at hTf
      exact nomatch hTf
    have hdown : ∀ (cvT : ConstantVal) (capsT : IndCaps),
        env''.find? T = some (.indInfo cvT capsT) →
        env'.find? T = some (.indInfo cvT capsT) := by
      intro cvT capsT hf
      rw [henv, Env.find?_cons,
        if_neg (fun hh => hTne hh.symm)] at hf
      exact hf
    obtain ⟨cval₄, m₄, hrec, hm₄, hinv₄, hIB₄⟩ :=
      ih m₁ h hinv₁ hIB₁
        (fun cvT capsT hf => by
          rw [henv]
          exact EtaPins.step (hpinsT cvT capsT (hdown cvT capsT hf))
            hfresh)
        (fun cvT capsT hf => hCblock cvT capsT (hdown cvT capsT hf))
        (fun cvT capsT hf => hFields cvT capsT (hdown cvT capsT hf))
    refine ⟨cval₄, m₄, ⟨env'', m₁.cval, Or.inl ⟨hR, hm₁cval⟩, ?_⟩,
      hm₄, hinv₄, hIB₄⟩
    exact hrec


/-! ## The recursor group

The rules fold does **not** interleave (the note above): every
semantic conjunct of a rule lives at the fixed `envSelf` the
provisioning produced, and — since `IndRecsFoldR` now names the
*base* environment — the only accumulator-dependent thing left in the
relation is nothing at all.  One `EnvR envSelf` serves the whole
fold, and `indRecsRS` produces the relation alone; the caller runs
`indRecsS` on it for the invariant. -/

/-- **The rules fold, bridged** at the fixed self environment. -/
theorem indRecsFoldRS {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {envBase envSelf : Env}
    (mS : EnvR envSelf)
    (hro : RenameOkT mS.cval envSelf (fun n =>
      if blockNames.contains n then n.str "_model" else n))
    (htr : ∀ (n : Name) (ci : ConstantInfo),
      envBase.find? n = some ci → envSelf.find? n = some ci) :
    ∀ (checked : List (ConstantVal × Nat × Nat × List RecRule))
      {acc env₃ : Env} {cval : TConstVal},
      (∀ c ∈ checked, envSelf.find? c.1.name
        = some (.recInfo c.1 c.2.1 c.2.2.1 [])) →
      checked.foldlM (fun (acc : Env) c => do
        let rules' ← checkIotaRules (m := CheckM) μ (fueledOps μ F)
          envBase envSelf
          (fun n => if blockNames.contains n then n.str "_model" else n)
          c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩ : Env))
        acc = .ok env₃ →
      ∃ cval₃, IndRecsR.IndRecsFoldR μ F blockNames envBase envSelf
        mS.cval acc cval checked env₃ cval₃ := by
  intro checked
  induction checked with
  | nil =>
    intro acc env₃ cval _ h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact ⟨cval, h.symm, rfl⟩
  | cons c rest ih =>
    intro acc env₃ cval hself h
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hr : checkIotaRules (m := CheckM) μ (fueledOps μ F) envBase
        envSelf
        (fun n => if blockNames.contains n then n.str "_model" else n)
        c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2 with
    | error e => intro h; exact nomatch h
    | ok rules' => ?_
    intro h
    try dsimp only at h
    obtain ⟨cval₃, hrec⟩ :=
      ih (acc := ⟨.recInfo c.1 c.2.1 c.2.2.1 rules' :: acc.consts⟩)
        (cval := cvalModeled cval c.1.name)
        (fun c' hc' => hself c' (List.mem_cons_of_mem _ hc')) h
    refine ⟨cval₃, rules', ?_, hrec⟩
    exact iotaRulesR_of mS (hself c List.mem_cons_self) rfl hro
      (fun n ci hf => ⟨ci, htr n ci hf, rfl⟩) 0 c.2.2.2 rules' hr

/-- **The recursor-group phase, bridged** (`checkIndRecs`): the
empty case, the pinned-`Eq` guard, the provisioning (interleaved,
`provisionRecsRS`), and the rules fold (not interleaved). -/
theorem indRecsRS (hkey : MemberKeyS V)
    {μ : CheckMode} {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {env₂ : Env} (m : EnvS V env₂)
      {env₃ : Env},
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      (∀ n, blockNames.contains n = true →
        (env₂.find? n).isSome = true ∨ ∃ ci ∈ recs, ci.name = n) →
      BlockInstalledTT blockNames env₂ m.cval →
      EtaFamiliesClosedO blockNames env₂ →
      BlockEtaPinned μ blockNames env₂ →
      checkIndRecs (m := CheckM) μ (fueledOps μ F) blockNames env₂ recs
        = .ok env₃ →
      ∃ cval₃, IndRecsR μ F blockNames env₂ m.cval recs env₃ cval₃ := by
  intro recs env₂ m env₃ hbn hall hI hEC hBP h
  simp only [checkIndRecs] at h
  by_cases hemp : recs.isEmpty = true
  · rw [if_pos hemp] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨m.cval, Or.inl ⟨List.isEmpty_iff.mp hemp, h.symm, rfl⟩⟩
  rw [if_neg hemp] at h
  simp only [Bind.bind, Except.bind] at h
  revert h
  by_cases heqf : env₂.find? eqName = some eqA
  case neg =>
    rw [if_neg heqf]
    intro h
    exact nomatch h
  rw [if_pos heqf]
  intro h
  try dsimp only at h
  revert h
  cases hprovE : provisionRecs (m := CheckM) (fueledOps μ F)
      blockNames env₂ recs with
  | error e => intro h; exact nomatch h
  | ok p => ?_
  obtain ⟨envSelf, checked⟩ := p
  intro h
  try dsimp only at h
  obtain ⟨cvalSelf, mS, hprov, hmScval, hIS, -, -⟩ :=
    provisionRecsRS hkey recs m hbn hI hEC hBP hprovE
  rw [← hmScval] at hprov hIS
  have hnames : ∀ n, blockNames.contains n = true →
      (envSelf.find? n).isSome = true := by
    intro n hn
    rcases hall n hn with hfound | ⟨ci, hci, rfl⟩
    · rcases hf : env₂.find? n with _ | ci
      · rw [hf] at hfound; exact nomatch hfound
      · rw [provisionRecsS_mono recs hprov n ci hf]; rfl
    · exact provisionRecsS_stored recs hprov ci hci
  obtain ⟨cval₃, hfold⟩ :=
    indRecsFoldRS (envBase := env₂) mS.toEnvR
      (blockRenameOkT mS hIS hnames)
      (provisionRecsS_mono recs hprov) checked
      (fun c hc => (provisionRecsS_entries recs hprov c hc).1)
      (cval := m.cval) h
  exact ⟨cval₃, Or.inr ⟨fun hc => hemp (by rw [hc]; rfl), heqf,
    envSelf, mS.cval, checked, hprov, hfold⟩⟩

set_option maxHeartbeats 4000000 in
/-- **The `indDecl` branch, walked** (`checkIndDecl`) — the five folds
assembled.  Structurally `declIndS` with each install fold replaced by
its bridge-side twin, and with one premise sourced from the other
side: `declIndS` gets its base `BlockInstalledTT` *vacuously from the
relations* (`indMembersR_fresh` / `indRecsR_fresh`), which the bridge
cannot do because the relations are what it is producing.  The
checker-side twins — `checkIndMember_fold_names`, `checkIndFold_mono`
and `checkIndRecs_fresh` — say the same thing about the same block,
from the verdict instead of the relation. -/
theorem declIndRS (hkey : MemberKeyS V)
    {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} (m : EnvS V env)
    (hE : EtaFamiliesClosed env)
    (h : checkIndDecl (m := CheckM) μ (fueledOps μ F) env block
      = .ok env₂) :
    DeclIndR μ F env m.cval block env₂ := by
  simp only [checkIndDecl, Bind.bind, Except.bind, pure,
    Except.pure] at h
  split at h
  case isFalse => simp [throw, throwThe, MonadExceptOf.throw] at h
  next hsplit =>
  split at h
  case h_2 =>
    next hnone =>
    split at h
    case h_1 => exact nomatch h
    next envM hmemFold =>
    have hbnAll : ∀ ci ∈ block,
        (block.map (·.name)).contains ci.name = true := by
      intro ci hci
      have hmm : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
      simpa using hmm
    have hbnNon : ∀ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => false | _ => true),
        (block.map (·.name)).contains ci.name = true :=
      fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
    have hbnRec : ∀ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => true | _ => false),
        (block.map (·.name)).contains ci.name = true :=
      fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
    have hI0 : BlockInstalledTT (block.map (·.name)) env m.cval := by
      intro n hn ci hf
      exfalso
      have hmm : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · rw [checkIndMember_fold_names _ _ _ hmemFold ci₀ hci₀] at hf
        exact nomatch hf
      · have hup := checkIndFold_mono _ _ _ hmemFold ci₀.name
          (by rw [hf]; rfl)
        rw [checkIndRecs_fresh h ci₀ hci₀] at hup
        exact nomatch hup
    have hEC0 : EtaFamiliesClosedO (block.map (·.name)) env :=
      fun T cvT caps hf hcape hres _ => hE T cvT caps hf hcape hres
    have hBP0 : BlockEtaPinned μ (block.map (·.name)) env := by
      intro n cvS capsS hnb hf _
      exfalso
      have hmm : n ∈ block.map (·.name) := by simpa using hnb
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · rw [checkIndMember_fold_names _ _ _ hmemFold ci₀ hci₀] at hf
        exact nomatch hf
      · have hup := checkIndFold_mono _ _ _ hmemFold ci₀.name
          (by rw [hf]; rfl)
        rw [checkIndRecs_fresh h ci₀ hci₀] at hup
        exact nomatch hup
    obtain ⟨cvalM, m₁, hmem, hm₁cval, hI₁, hEC₁, hBP₁⟩ :=
      indMembersRS hkey _ m hbnNon
        (fun cv caps₂ _ => ⟨etaPins_empty,
          ⟨fun hh => absurd hh (by decide),
            fun hh => absurd hh (by decide)⟩⟩)
        hI0 hEC0 hBP0 hmemFold
    rw [← hm₁cval] at hI₁
    have hall : ∀ n, (block.map (·.name)).contains n = true →
        (envM.find? n).isSome = true ∨
        ∃ ci ∈ block.filter (fun ci => match ci with
          | .recInfo _ _ _ _ => true | _ => false), ci.name = n := by
      intro n hn
      have hmm : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
      rw [hsplit] at hci₀
      rcases List.mem_append.mp hci₀ with hci₀ | hci₀
      · exact Or.inl (indMembersR_stored _ hmem ci₀ hci₀)
      · exact Or.inr ⟨ci₀, hci₀, rfl⟩
    obtain ⟨cval₂, hrecs⟩ :=
      indRecsRS hkey _ m₁ hbnRec hall hI₁ hEC₁ hBP₁ h
    rw [hm₁cval] at hrecs
    refine ⟨hsplit, Or.inr ⟨?_, envM, cvalM, cval₂, hmem, hrecs⟩⟩
    rintro ⟨cvT, capsT, cvC, nP, nF, hI, hC⟩
    exact hnone cvT capsT cvC nP nF hI hC
  next cvT capsT cvC nP nF hIfilt hCfilt =>
  split at h
  case h_1 => exact nomatch h
  next envM hmemFold =>
  split at h
  case h_1 => exact nomatch h
  next envR hrecsFold =>
  split at h
  case isFalse => exact nomatch h
  next hres =>
  split at h
  case isFalse => exact nomatch h
  next hprojFresh =>
  split at h
  case h_1 => exact nomatch h
  next envP hprojFold =>
  -- the block's bookkeeping
  have hbnAll : ∀ ci ∈ block,
      (block.map (·.name)).contains ci.name = true := by
    intro ci hci
    have hmm : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
    simpa using hmm
  have hbnNon : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => false | _ => true),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  have hbnRec : ∀ ci ∈ block.filter (fun ci => match ci with
      | .recInfo _ _ _ _ => true | _ => false),
      (block.map (·.name)).contains ci.name = true :=
    fun ci hci => hbnAll ci (List.mem_filter.mp hci).1
  -- the base invariant, from the *checker*: no block name is stored
  have hI0 : BlockInstalledTT (block.map (·.name)) env m.cval := by
    intro n hn ci hf
    exfalso
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · rw [checkIndMember_fold_names _ _ _ hmemFold ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := checkIndFold_mono _ _ _ hmemFold ci₀.name
        (by rw [hf]; rfl)
      rw [checkIndRecs_fresh hrecsFold ci₀ hci₀] at hup
      exact nomatch hup
  -- the block's two named members
  have hmemFil : ∀ {p : ConstantInfo → Bool} {x : ConstantInfo},
      block.filter p = [x] → x ∈ block := by
    intro p x hfil
    have hx : x ∈ block.filter p := by
      rw [hfil]; exact List.mem_singleton_self _
    exact (List.mem_filter.mp hx).1
  have hsingle : ∀ {p : ConstantInfo → Bool} {x y : ConstantInfo},
      block.filter p = [x] → y ∈ block → p y = true → y = x := by
    intro p x y hfil hy hpy
    have hx : y ∈ block.filter p := List.mem_filter.mpr ⟨hy, hpy⟩
    rw [hfil, List.mem_singleton] at hx
    exact hx
  have hTin : ConstantInfo.indInfo cvT capsT ∈ block := hmemFil hIfilt
  have hCin : ConstantInfo.ctorInfo cvC nP nF ∈ block := hmemFil hCfilt
  have hTnon : ConstantInfo.indInfo cvT capsT ∈ block.filter
      (fun ci => match ci with
        | .recInfo _ _ _ _ => false | _ => true) :=
    List.mem_filter.mpr ⟨hTin, rfl⟩
  have hTblock : (block.map (·.name)).contains cvT.name = true :=
    hbnAll _ hTin
  have hCblockN : (block.map (·.name)).contains cvC.name = true :=
    hbnAll _ hCin
  -- the eta side invariants, and the run's projection freshness
  -- pulled back to the base through the two checker folds
  have hEC0 : EtaFamiliesClosedO (block.map (·.name)) env :=
    fun T cvT' caps hf hcape hres _ => hE T cvT' caps hf hcape hres
  have hBP0 : BlockEtaPinned μ (block.map (·.name)) env := by
    intro n cvS capsS hnb hf _
    exfalso
    have hmm : n ∈ block.map (·.name) := by simpa using hnb
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · rw [checkIndMember_fold_names _ _ _ hmemFold ci₀ hci₀] at hf
      exact nomatch hf
    · have hup := checkIndFold_mono _ _ _ hmemFold ci₀.name
        (by rw [hf]; rfl)
      rw [checkIndRecs_fresh hrecsFold ci₀ hci₀] at hup
      exact nomatch hup
  have hpf0 : 0 < nF → env.find? (projFnName cvT.name 0) = none := by
    intro h0
    have hnone := List.all_eq_true.mp hprojFresh 0
      (List.mem_range.mpr h0)
    rcases hf : env.find? (projFnName cvT.name 0) with _ | ci
    · rfl
    · exfalso
      have h1 := checkIndFold_mono _ _ _ hmemFold
        (projFnName cvT.name 0) (by rw [hf]; rfl)
      have h2 := checkIndRecs_mono hrecsFold hbnRec _ h1
      rcases hfR : envR.find? (projFnName cvT.name 0) with _ | ci'
      · rw [hfR] at h2; exact nomatch h2
      · rw [hfR] at hnone; exact nomatch hnone
  -- the member fold, walked
  obtain ⟨cvalM, m₁, hmem, hm₁cval, hI₁, hEC₁, hBP₁⟩ :=
    indMembersRS hkey _ m hbnNon
      (fun cv caps₂ hmm => by
        obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj
          (hsingle hIfilt (List.mem_filter.mp hmm).1 rfl)
        exact ⟨etaPins_of_indBlockCaps, fun _ => hCblockN,
          fun _ h0 => hpf0 h0⟩)
      hI0 hEC0 hBP0 hmemFold
  rw [← hm₁cval] at hI₁
  -- the recursor group, bridged then installed
  have hall : ∀ n, (block.map (·.name)).contains n = true →
      (envM.find? n).isSome = true ∨
      ∃ ci ∈ block.filter (fun ci => match ci with
        | .recInfo _ _ _ _ => true | _ => false), ci.name = n := by
    intro n hn
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hci₀ | hci₀
    · exact Or.inl (indMembersR_stored _ hmem ci₀ hci₀)
    · exact Or.inr ⟨ci₀, hci₀, rfl⟩
  obtain ⟨cvalR, hrecs⟩ :=
    indRecsRS hkey _ m₁ hbnRec hall hI₁ hEC₁ hBP₁ hrecsFold
  obtain ⟨m₂, hm₂cval, hI₂, hnonrecUp, -, -⟩ :=
    indRecsS hkey m₁ hI₁ hbnRec hall hEC₁ hBP₁ hrecs
  rw [← hm₂cval] at hI₂
  rw [hm₁cval] at hrecs
  have hbshape : ∀ n, (block.map (·.name)).contains n = true →
      n.isProjFnShape = false := by
    intro n hn
    have hmm : n ∈ block.map (·.name) := by simpa using hn
    obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmm
    rw [hsplit] at hci₀
    rcases List.mem_append.mp hci₀ with hx | hx
    · exact (indMembersR_nameGuards _ hmem ci₀ hx).1
    · exact (indRecsR_nameGuards hrecs ci₀ hx).1
  have hTnres : reservedBasisNames.contains cvT.name = false :=
    (indMembersR_nameGuards _ hmem _ hTnon).2
  -- the stored former, identified
  have hidR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
      envR.find? cvT.name = some (.indInfo cvT' capsT') →
      cvT'.levelParams = cvT.levelParams ∧
      capsT' = indBlockCaps μ env cvT cvC nP nF := by
    intro cvT' capsT' hf
    obtain ⟨cvA, hnameA, hlpsA, hfM⟩ :=
      indMembersR_indEntry _ hmem cvT capsT hTnon
    have hfR := hnonrecUp cvT.name (.indInfo cvA
      (indBlockCaps μ env cvT cvC nP nF)) hfM
      (fun cv mI rP rules hh => ConstantInfo.noConfusion hh)
    rw [hf] at hfR
    obtain ⟨h1, h2⟩ := ConstantInfo.indInfo.inj (Option.some.inj hfR)
    exact ⟨by rw [h1]; exact hlpsA, h2⟩
  have hkeepR : ∀ (n : Name) (ci : ConstantInfo),
      env.find? n = some ci →
      (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
      envR.find? n = some ci := by
    intro n ci hf hnr
    exact hnonrecUp n ci (indMembersR_mono _ hmem n ci hf) hnr
  have hinvR : ProjPhaseInvS cvT.name cvC.name nF envR m₂.cval := by
    refine ⟨?_, ?_, ?_⟩
    · intro ci hf
      obtain ⟨cvm, mval, hint, hfm, hlps, -, hv⟩ :=
        hI₂ cvT.name hTblock ci hf
      exact ⟨cvm, mval, hint, hfm, hlps, hv⟩
    · intro ci hf
      obtain ⟨cvm, mval, hint, hfm, hlps, -, hv⟩ :=
        hI₂ cvC.name hCblockN ci hf
      exact ⟨cvm, mval, hint, hfm, hlps, hv⟩
    · intro j hj ci hf
      exfalso
      have hnone := List.all_eq_true.mp hprojFresh j
        (List.mem_range.mpr hj)
      rw [hf] at hnone
      exact nomatch hnone
  have hpinsR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
      envR.find? cvT.name = some (.indInfo cvT' capsT') →
      EtaPins μ envR cvT.name cvT'.levelParams capsT' := by
    intro cvT' capsT' hf
    obtain ⟨hlps', rfl⟩ := hidR cvT' capsT' hf
    rw [hlps']
    exact EtaPins.transport etaPins_of_indBlockCaps hkeepR
  have hCblockR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
      envR.find? cvT.name = some (.indInfo cvT' capsT') →
      capsT'.eta = true →
      (block.map (·.name)).contains capsT'.etaCtor = true := by
    intro cvT' capsT' hf _
    obtain ⟨-, rfl⟩ := hidR cvT' capsT' hf
    exact hCblockN
  have hFieldsR : ∀ (cvT' : ConstantVal) (capsT' : IndCaps),
      envR.find? cvT.name = some (.indInfo cvT' capsT') →
      capsT'.eta = true → capsT'.etaFields = nF := by
    intro cvT' capsT' hf _
    obtain ⟨-, rfl⟩ := hidR cvT' capsT' hf
    rfl
  -- the projection fold, walked; then the templates
  obtain ⟨cvalP, m₃, hproj, hm₃cval, -, -⟩ :=
    projInstallRS hTblock hbshape (List.range nF) m₂ hprojFold hinvR
      hI₂ hpinsR hCblockR hFieldsR
  rw [hm₂cval] at hproj
  refine ⟨hsplit, Or.inl ⟨cvT, capsT, cvC, nP, nF, hIfilt, hCfilt,
    envM, cvalM, envR, cvalR, hmem, hrecs, hres, hprojFresh,
    envP, cvalP, hproj, templatesR_of _ h⟩⟩

end Setlec.SetR
