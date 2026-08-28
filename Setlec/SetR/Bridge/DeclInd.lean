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
theorem indMembersRS (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} (m : EnvS V env)
      {env₂ : Env},
      (∀ ci ∈ members, blockNames.contains ci.name = true) →
      (∀ (cv : ConstantVal) (caps₂ : IndCaps),
        ConstantInfo.indInfo cv caps₂ ∈ members →
        EtaPins μ env cv.name cv.levelParams caps) →
      BlockInstalledTT blockNames env m.cval →
      members.foldlM (checkIndMember (m := CheckM) (fueledOps μ F)
        blockNames caps) env = .ok env₂ →
      ∃ (cval₂ : TConstVal) (m₂ : EnvS V env₂),
        IndMembersR μ F blockNames caps env m.cval members env₂ cval₂ ∧
        m₂.cval = cval₂ ∧ BlockInstalledTT blockNames env₂ cval₂ := by
  intro members
  induction members with
  | nil =>
    intro env m env₂ _ _ hI h
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨m.cval, m, ⟨rfl, rfl⟩, rfl, hI⟩
  | cons ci rest ih =>
    intro env m env₂ hbn hp hI h
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
      cases ci with
      | indInfo cv caps' =>
        simp only [pure, Except.pure] at h
        obtain ⟨m₁, hm₁cval, hI₁⟩ := memberInstallS hkey heta m hmv
          hI hbnA
          (fun caps₃ heq => by
            obtain ⟨-, -, -, rfl⟩ := ConstantInfo.indInfo.inj heq
            exact hp cv caps' List.mem_cons_self)
          rfl rfl (Or.inl ⟨caps, rfl⟩)
        obtain ⟨cval₂, m₂, hrel, hm₂, hI₂⟩ :=
          ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
            (fun cv₂ caps₂ hmem => EtaPins.step
              (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)) hfreshA)
            (by rw [hm₁cval]; exact hI₁) h
        exact ⟨cval₂, m₂, ⟨cvA, hmv, by rw [← hm₁cval]; exact hrel⟩,
          hm₂, hI₂⟩
      | ctorInfo cv nP nF =>
        simp only [pure, Except.pure] at h
        obtain ⟨m₁, hm₁cval, hI₁⟩ := memberInstallS hkey heta m hmv
          hI hbnA (fun caps₃ heq => ConstantInfo.noConfusion heq)
          rfl rfl (Or.inr (Or.inl ⟨nP, nF, rfl⟩))
        obtain ⟨cval₂, m₂, hrel, hm₂, hI₂⟩ :=
          ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
            (fun cv₂ caps₂ hmem => EtaPins.step
              (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)) hfreshA)
            (by rw [hm₁cval]; exact hI₁) h
        exact ⟨cval₂, m₂, ⟨cvA, hmv, by rw [← hm₁cval]; exact hrel⟩,
          hm₂, hI₂⟩
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
theorem provisionRecsRS (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat} {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} (m : EnvS V envAcc)
      {envSelf : Env}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      BlockInstalledTT blockNames envAcc m.cval →
      provisionRecs (m := CheckM) (fueledOps μ F) blockNames envAcc recs
        = .ok (envSelf, checked) →
      ∃ (cvalSelf : TConstVal) (mS : EnvS V envSelf),
        ProvisionRecsR μ F blockNames envAcc m.cval recs envSelf
          cvalSelf checked ∧
        mS.cval = cvalSelf ∧
        BlockInstalledTT blockNames envSelf cvalSelf := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc m envSelf checked _ hI h
    simp only [provisionRecs, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m.cval, m, ⟨rfl, rfl, rfl⟩, rfl, hI⟩
  | cons ci rest ih =>
    intro envAcc m envSelf checked hbn hI h
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
        obtain ⟨m₁, hm₁cval, hI₁⟩ := memberInstallS hkey heta m hmv
          hI (by rw [hnameA]; exact hbn _ List.mem_cons_self)
          (fun caps₃ heq => ConstantInfo.noConfusion heq)
          rfl rfl (Or.inr (Or.inr ⟨mI, rP, rfl⟩))
        cases hrest : provisionRecs (m := CheckM) (fueledOps μ F)
            blockNames ⟨.recInfo cvA mI rP [] :: envAcc.consts⟩
            rest with
        | error e => rw [hrest] at h; exact nomatch h
        | ok p =>
          rw [hrest] at h
          simp only [pure, Except.pure, Except.ok.injEq,
            Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨cvalSelf, mS, hrel, hmS, hIS⟩ :=
            ih m₁
              (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
              (by rw [hm₁cval]; exact hI₁) hrest
          exact ⟨cvalSelf, mS,
            ⟨cvA, mI, rP, rules, p.2, rfl, hmv,
              by rw [← hm₁cval]; exact hrel, rfl⟩,
            hmS, hIS⟩
    | axiomInfo cv | defnInfo cv v hint | thmInfo cv v
    | indInfo cv c | ctorInfo cv nP nF | projInfo e =>
      simp [provisionRecs, throw, throwThe, MonadExceptOf.throw] at h

end Setlec.SetR
