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

end Setlec.SetR
