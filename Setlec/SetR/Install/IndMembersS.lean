import Setlec.SetBase.IndBlockR
import Setlec.SetR.Install.IndMemberS
import Setlec.SetR.Install.EtaLawS
import Setlec.Verify.Extend.Block
import Setlec.Verify.Extend.Iota
import Setlec.Verify.Extend.Ind

/-!
# The block-member fold (task #148, T5, `declIndS` stage 2)

`indMembersS` runs `indMemberS` along `IndMembersR`, carrying the
running valuation (finding 5's resolution) and the block invariant
`BlockInstalledTT` — the [set] lane reuses the TT lane's, verbatim,
since it is `TConstVal`-stated and V-free.

Two obligations stay named, because their suppliers sit outside the
fold:

* `MemberKeyS` — the member's *semantic* content: the model
  artifact's value inhabits the member's (renamed) type.  Supplier:
  the model definition's own `mem_type`, transported across
  `MemberValR`'s `eqUpToNames` pin using the block invariant to
  identify the public names' valuations with the model names'.
* `MemberEtaS` / `MemberUnitS` — the capability head obligations
  `EnvS.cons` asks of *any* install that could complete an eta or
  unit-like family.  They are vacuous at every member but the one that
  completes the family (`EtaFamilyStored` is false until then), and at
  that member the block assembly discharges them through
  `etaLawKeyS`/`unitLawKeyS`.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The block member's key**: the model artifact's value inhabits
the checked member's type, truthfully, at the running valuation. -/
def MemberKeyS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {F : Nat} {blockNames : List Name} {env : Env}
    (m : EnvS V env) {cv cvA : ConstantVal},
    MemberValR μ F env m.cval blockNames cv cvA →
    BlockInstalledTT blockNames env m.cval →
    ∀ ψ : Name → Nat, ∃ t,
      denoteClosed m.cval env ψ cvA.type = some t ∧
      ∀ ρ : Nat → V,
        interp V ρ (m.cval (cvA.name.str "_model") ψ) ∈ˢ interp V ρ t ∧
        AnnotOkV V ρ t

/-- **The unit-like head obligation at a member install** (T5 stage 4).

Re-signed with the premises its discharge needs.  The `caps` an
install stores are not free data — they are `indBlockCaps`' output,
whose two Booleans invert to the checked artifacts' shape pins.  That
inversion is `EtaPins`, and without it `caps.unitlike = true` says
nothing at all.  The block fold carries it (`EtaPins.step` at each
member); `DeclIndR`'s `indBlockCaps` binding is where it is created. -/
def MemberUnitS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {F : Nat} {blockNames : List Name} {env : Env}
    (m : EnvS V env) {cv cvA : ConstantVal} {caps : IndCaps},
    MemberValR μ F env m.cval blockNames cv cvA →
    BlockInstalledTT blockNames env m.cval →
    blockNames.contains cvA.name = true →
    EtaPins μ env cvA.name cvA.levelParams caps →
    caps.unitlike = true →
    reservedBasisNames.contains cvA.name = false →
    UnitLawV V ⟨.indInfo cvA caps :: env.consts⟩
      (cvalModeled m.cval cvA.name) cvA.name cvA caps

set_option maxHeartbeats 1600000 in
/-- **`MemberUnitS`, discharged** (T5 stage 4): `unitLawKeyS`, run one
environment ahead (finding 6), over `EtaPins`' unit half.

Nothing here is a case split — the unit-like law is the *easy* half of
the pair, because it fabricates no side: both of its subjects are
given, so the only work is moving the model's facts onto the installed
valuation and handing `unitLawKeyS` its pins. -/
theorem memberUnitS : MemberUnitS V := by
  intro μ F blockNames env m cv cvA caps hmv hI hbn hpins hcapu hnres
  obtain ⟨type', hcv, hcvA, hms, cvm, mval, hint, hmE, hmlps, hren⟩ :=
    id hmv
  obtain ⟨hfind, -, -, -, -, -, -, -, htr, -⟩ := hcv
  have hnameA : cvA.name = cv.name := by rw [hcvA]
  have htypeA : cvA.type = type' := by rw [hcvA]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfind
  -- the install this member is
  have hi : Installs env m.cval (cvalModeled m.cval cvA.name)
      (.indInfo cvA caps) :=
    Installs.of_fresh hfreshA (fun n hn => by
      rw [cvalModeled, cvalWith_ne (show n ≠ cvA.name from hn)])
  have hcl : ∀ (n : Name) (ψ : Name → Nat),
      VExpr.Closed (cvalModeled m.cval cvA.name n ψ) := by
    intro n ψ
    by_cases hn : n = cvA.name
    · subst hn
      rw [cvalModeled, cvalWith_self]
      exact m.cval_closed _ _
    · rw [cvalModeled, cvalWith_ne hn]
      exact m.cval_closed _ _
  have hresT : ∀ us : List Level,
      (cvA.type.instantiateLevelParams cvA.levelParams us).constsResolve
        env = true := by
    intro us
    rw [Expr.constsResolve_instantiateLevelParams, htypeA]
    exact htr
  -- the public/model identification at the head
  have hvT : ∀ ψ : Name → Nat,
      cvalModeled m.cval cvA.name cvA.name ψ
        = cvalModeled m.cval cvA.name (cvA.name.str "_model") ψ := by
    intro ψ
    simp only [cvalModeled, cvalWith_ne (Name.str_ne cvA.name "_model"),
      cvalWith_self]
  -- the block renaming, on the installed valuation
  have hroB := renameOkT_cvalStep hi
    (fun n hn => by simp only [hn]; rfl) hI.renameOkT
  have hrenT : RenEqT (fun n => if (env.find? n).isSome = true then
      (if blockNames.contains n then n.str "_model" else n) else n)
      cvA.type cvm.type := by
    unfold RenEqT
    rw [htypeA, Expr.renameConsts_congr_resolve
      (g := fun n => if blockNames.contains n then n.str "_model" else n)
      (fun n hn => by simp only [hn, if_true]) _ htr, ← htypeA]
    exact Expr.ErasedEq.of_eqUpToNames hren
  obtain ⟨-, hunitPins⟩ := hpins
  obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlps, hTmE, hTmlps, heqfE, hSstrip,
    hTstrip, hsdoms, hxdom, hydom, hsbody, htySlot, -⟩ :=
    hunitPins hcapu
  -- the two lookups of `T._model` agree
  have hcvmEq : cvm = cvmT := by
    obtain ⟨h1, -, -⟩ :=
      ConstantInfo.defnInfo.inj (Option.some.inj (hmE.symm.trans hTmE))
    exact h1
  rw [hcvmEq] at hrenT
  exact unitLawKeyS (V := V) m hi hcl hresT rfl rfl hthmE htlps hTmE
    hTmlps heqfE hSstrip hTstrip hsdoms hxdom hydom hsbody htySlot hvT
    hroB hrenT

/-! ## The eta head: a threaded invariant, not a forwarded obligation

The T5 handoff called this obligation vacuous and the T6 correction
called it forwardable; both were wrong in the same way (read the
premise's text, P2).  It is neither: the head *is* live — a
`etaFields = 0` structure completes inside the member fold — and the
three rows that are not live die on facts the fold can carry, which is
what `EtaFamiliesClosedO`, `BlockEtaPinned` and `BlockProjFresh` are.
With them the discharge is in-fold, `memberUnitS`'s shape exactly, and
`MemberEtaS` leaves the campaign's hypothesis list entirely. -/

set_option maxHeartbeats 3200000 in
/-- **The eta head at a member install, discharged.**  The projection
disjunct dies on the member's name shape; an outside former's family
is closed, so a fresh member never completes one; and
`etaFields > 0` needs projections the fold has not installed.  What is
left is a block former whose eta pins the fold carries, at
`etaFields = 0`, where `etaLawKeyS`'s projection premises are
vacuous. -/
theorem memberEtaS {μ : CheckMode} {F : Nat} {blockNames : List Name}
    {env : Env} (m : EnvS V env) {cv cvA : ConstantVal}
    {c₀ : ConstantInfo}
    (hmv : MemberValR μ F env m.cval blockNames cv cvA)
    (hI : BlockInstalledTT blockNames env m.cval)
    (hbn : blockNames.contains cvA.name = true)
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hpins : ∀ caps, c₀ = .indInfo cvA caps →
      EtaPins μ env cvA.name cvA.levelParams caps ∧
        (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (projFnName cvA.name 0) = none))
    (hEC : EtaFamiliesClosedO blockNames env)
    (hBP : BlockEtaPinned μ blockNames env) :
    ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨c₀ :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨c₀ :: env.consts⟩ T caps →
      (T = c₀.name ∨ caps.etaCtor = c₀.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = c₀.name) →
      EtaLawV V ⟨c₀ :: env.consts⟩ (cvalModeled m.cval cvA.name)
        T cvT caps := by
  intro T cvT caps hfT hcape hnresT hfam hor
  obtain ⟨type', hcv, hcvA, hms, cvm, mval, hint, hmE, hmlps, hren⟩ :=
    id hmv
  obtain ⟨hfind, -, hpshape, -, -, -, -, -, htr, -⟩ := hcv
  have hnameA : cvA.name = cv.name := by rw [hcvA]
  have htypeA : cvA.type = type' := by rw [hcvA]
  have hlpsA : cvA.levelParams = cv.levelParams := by rw [hcvA]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]; exact Option.isNone_iff_eq_none.mp hfind
  have hfresh0 : env.find? c₀.name = none := by
    rw [hc₀name]; exact hfreshA
  have hpshape0 : c₀.name.isProjFnShape = false := by
    rw [hc₀name, hnameA]; exact hpshape
  -- the projection disjunct dies on the member's name shape
  have hor2 : T = c₀.name ∨ caps.etaCtor = c₀.name := by
    rcases hor with h | h | ⟨j, -, hj⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd hj (projFnName_ne_of_shape hpshape0)
  -- `T` is a block former whose eta pins the fold carries
  have hkey : blockNames.contains T = true ∧
      EtaPins μ env T cvT.levelParams caps ∧
      blockNames.contains caps.etaCtor = true ∧
      (0 < caps.etaFields → env.find? (projFnName T 0) = none) := by
    rw [Env.find?_cons] at hfT
    split at hfT
    · next he =>
      obtain rfl : c₀ = .indInfo cvT caps := Option.some.inj hfT
      have hcvT : cvT = cvA := hc₀cv
      have hTA : T = cvA.name := by rw [← he, hc₀name]
      subst hcvT
      subst hTA
      obtain ⟨hp, hc, hj⟩ := hpins caps rfl
      exact ⟨hbn, hp, hc hcape, hj hcape⟩
    · next hne =>
      by_cases hTb : blockNames.contains T = true
      · exact ⟨hTb, (hBP T cvT caps hTb hfT hcape).1,
          (hBP T cvT caps hTb hfT hcape).2.1,
          (hBP T cvT caps hTb hfT hcape).2.2⟩
      · exfalso
        obtain ⟨cvC, hfC⟩ := hEC T cvT caps hfT hcape hnresT
          (by simpa using hTb)
        rcases hor2 with h | h
        · exact hne h.symm
        · rw [h, hfresh0] at hfC; exact nomatch hfC
  obtain ⟨hTb, hpinsT, hctorB, hprojF⟩ := hkey
  -- the projection fold has not run: `etaFields = 0`
  have hnF0 : caps.etaFields = 0 := by
    rcases Nat.eq_zero_or_pos caps.etaFields with h | h
    · exact h
    · exfalso
      obtain ⟨cvp, mI, rP, rules, hfp⟩ := hfam.2.2 0 h
      rw [Env.find?_cons, if_neg (fun hh =>
        projFnName_ne_of_shape (T := T) (j := 0) hpshape0 hh.symm),
        hprojF h] at hfp
      exact nomatch hfp
  -- the install, and the valuation's basic facts
  have hi : Installs env m.cval (cvalModeled m.cval cvA.name) c₀ :=
    Installs.of_fresh hfresh0 (fun n hn => by
      rw [cvalModeled, cvalWith_ne (show n ≠ cvA.name from
        fun he => hn (by rw [he, hc₀name]))])
  have hcl : ∀ (n : Name) (ψ : Name → Nat),
      VExpr.Closed (cvalModeled m.cval cvA.name n ψ) := by
    intro n ψ
    by_cases hn : n = cvA.name
    · subst hn
      rw [cvalModeled, cvalWith_self]
      exact m.cval_closed _ _
    · rw [cvalModeled, cvalWith_ne hn]
      exact m.cval_closed _ _
  -- the block invariant, reaching the *installed* environment
  have hblk : ∀ (n : Name) (ci : ConstantInfo),
      blockNames.contains n = true →
      (⟨c₀ :: env.consts⟩ : Env).find? n = some ci →
      (∀ ψ : Name → Nat, cvalModeled m.cval cvA.name n ψ
        = cvalModeled m.cval cvA.name (n.str "_model") ψ) ∧
      ∃ cvm' mval' hint',
        env.find? (n.str "_model") = some (.defnInfo cvm' mval' hint') ∧
        cvm'.levelParams = ci.toConstantVal.levelParams ∧
        Expr.eqUpToNames (ci.toConstantVal.type.renameConsts
          (fun n' => if blockNames.contains n' then n'.str "_model"
            else n')) cvm'.type = true := by
    intro n ci hnb hfn
    have hmsn : n.str "_model" ≠ cvA.name := Name.str_model_ne hms
    by_cases hn : n = cvA.name
    · subst hn
      rw [Env.find?_cons, if_pos hc₀name] at hfn
      obtain rfl : c₀ = ci := Option.some.inj hfn
      rw [hc₀cv]
      exact ⟨fun ψ => by
          simp only [cvalModeled, cvalWith_self, cvalWith_ne hmsn],
        cvm, mval, hint, hmE, hmlps, hren⟩
    · rw [Env.find?_cons, if_neg (show ¬ (c₀.name = n) from
        fun he => hn (by rw [← he, hc₀name]))] at hfn
      obtain ⟨cvm', mval', hint', hfm', hlps', heq', hveq⟩ :=
        hI n hnb ci hfn
      refine ⟨fun ψ => ?_, cvm', mval', hint', hfm', hlps', heq'⟩
      simp only [cvalModeled, cvalWith_ne hn, cvalWith_ne hmsn]
      exact hveq ψ
  -- `T`, and its constructor, identified
  obtain ⟨hvT, cvmT', mvalT', hintT', hTmE', hTmlps', hrenT'⟩ :=
    hblk T (.indInfo cvT caps) hTb hfT
  obtain ⟨cvC, hfC⟩ := hfam.2.1
  obtain ⟨hvC, -⟩ := hblk caps.etaCtor
    (.ctorInfo cvC caps.etaParams caps.etaFields) hctorB hfC
  -- `T`'s stored type resolves
  have hTcase : (T = cvA.name ∧ cvT = cvA) ∨
      (T ≠ cvA.name ∧ env.find? T = some (.indInfo cvT caps)) := by
    by_cases hTA : T = cvA.name
    · refine Or.inl ⟨hTA, ?_⟩
      rw [Env.find?_cons, if_pos (by rw [hc₀name, hTA])] at hfT
      obtain rfl : c₀ = .indInfo cvT caps := Option.some.inj hfT
      exact hc₀cv
    · refine Or.inr ⟨hTA, ?_⟩
      rw [Env.find?_cons, if_neg (fun he =>
        hTA (by rw [← he, hc₀name]))] at hfT
      exact hfT
  have hresTy : cvT.type.constsResolve env = true := by
    rcases hTcase with ⟨-, rfl⟩ | ⟨-, hfTe⟩
    · rw [htypeA]; exact htr
    · exact (m.wf _ (Env.find?_mem hfTe)).2.2.1
  have hresT : ∀ us : List Level,
      (cvT.type.instantiateLevelParams cvT.levelParams us).constsResolve
        env = true := by
    intro us
    rw [Expr.constsResolve_instantiateLevelParams]
    exact hresTy
  -- the block renaming, on the installed valuation
  have hroB := renameOkT_cvalStep hi
    (fun n hn => by simp only [hn]; rfl) hI.renameOkT
  have hrenT : RenEqT (fun n => if (env.find? n).isSome = true then
      (if blockNames.contains n then n.str "_model" else n) else n)
      cvT.type cvmT'.type := by
    unfold RenEqT
    rw [Expr.renameConsts_congr_resolve
      (g := fun n => if blockNames.contains n then n.str "_model" else n)
      (fun n hn => by simp only [hn, if_true]) _ hresTy]
    exact Expr.ErasedEq.of_eqUpToNames hrenT'
  -- the checked eta artifacts
  obtain ⟨tcv, tval, cvmT, mvalT, hmcvmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlps, hTmE, hTmlps,
    ⟨cvmC, mvalC, hmcvmC, hCmE, hCmlps⟩, hprojE, heqfE, hSstrip,
    hTstrip, hsdoms, hxdom, hsbody, htySlot⟩ := hpinsT.1 hcape
  have hcvmEq : cvmT' = cvmT := by
    obtain ⟨h1, -, -⟩ :=
      ConstantInfo.defnInfo.inj (Option.some.inj (hTmE'.symm.trans hTmE))
    exact h1
  rw [hcvmEq] at hrenT
  rw [hnF0] at hsbody
  exact etaLawKeyS (V := V) m hi hcl hresT rfl rfl hnF0 rfl
    hthmE htlps hTmE hTmlps hCmE hCmlps
    (fun j hj => absurd hj (Nat.not_lt_zero j))
    heqfE hSstrip hTstrip hsdoms hxdom hsbody htySlot.1
    hvT hvC (fun j hj => absurd hj (Nat.not_lt_zero j))
    hroB hrenT

/-- **One member installed, with the block invariant carried**: the
shared step of both block folds (the non-recursor members and the
recursor provisioning, whose entries are rule-less). -/
theorem memberInstallS (hkey : MemberKeyS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {env : Env} (m : EnvS V env)
    {cv cvA : ConstantVal} {c₀ : ConstantInfo}
    (hmv : MemberValR μ F env m.cval blockNames cv cvA)
    (hI : BlockInstalledTT blockNames env m.cval)
    (hbn : blockNames.contains cvA.name = true)
    -- the block's capability artifacts, at *this* accumulator; the
    -- fold steps them up with `EtaPins.step` (T5 stage 4)
    (hpins : ∀ caps, c₀ = .indInfo cvA caps →
      EtaPins μ env cv.name cv.levelParams caps ∧
        (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (projFnName cv.name 0) = none))
    -- the eta head's two side invariants, stepped by the fold
    (hEC : EtaFamiliesClosedO blockNames env)
    (hBP : BlockEtaPinned μ blockNames env)
    (hc₀cv : c₀.toConstantVal = cvA) (hc₀name : c₀.name = cvA.name)
    (hkind : (∃ caps, c₀ = .indInfo cvA caps) ∨
      (∃ nP nF, c₀ = .ctorInfo cvA nP nF) ∨
      (∃ mI rP, c₀ = .recInfo cvA mI rP [])) :
    ∃ m₁ : EnvS V ⟨c₀ :: env.consts⟩,
      m₁.cval = cvalModeled m.cval cvA.name ∧
      BlockInstalledTT blockNames ⟨c₀ :: env.consts⟩
        (cvalModeled m.cval cvA.name) ∧
      EtaFamiliesClosedO blockNames ⟨c₀ :: env.consts⟩ ∧
      BlockEtaPinned μ blockNames ⟨c₀ :: env.consts⟩ := by
  obtain ⟨type', hcv, hcvA, hms, cvm, mval, hint, hmE, hmlps, hren⟩ :=
    id hmv
  obtain ⟨hfind, hnres, hpshape, hnd, hlbt, hitf, hann, htp, htr, -⟩ :=
    hcv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann hitf hlbt
  have hnameA : cvA.name = cv.name := by rw [hcvA]
  have hlpsA : cvA.levelParams = cv.levelParams := by rw [hcvA]
  have htypeA : cvA.type = type' := by rw [hcvA]
  have hfreshA : env.find? cvA.name = none := by
    rw [hnameA]
    exact Option.isNone_iff_eq_none.mp hfind
  have hnresA : reservedBasisNames.contains cvA.name = false := by
    rw [hnameA]; exact hnres
  have hwf : EnvWF ⟨c₀ :: env.consts⟩ := by
    refine EnvWF.cons m.wf ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hc₀cv, htypeA]; exact htf'
    · rw [hc₀cv, htypeA, hlpsA]; exact htp
    · rw [hc₀cv, htypeA]; exact Expr.constsResolve_mono htr
    · rw [hc₀cv, htypeA]; exact hbt'
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 v2 h2 heq <;> exact nomatch heq
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 mI2 rP2 rules2 heq
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with _ _ _ h4
        intro r hr
        rw [← h4] at hr
        exact nomatch hr
    · rcases hkind with ⟨caps', rfl⟩ | ⟨nP, nF, rfl⟩ | ⟨mI, rP, rfl⟩ <;>
        intro cv2 v2 heq <;> exact nomatch heq
  have hpinsA : ∀ caps, c₀ = .indInfo cvA caps →
      EtaPins μ env cvA.name cvA.levelParams caps ∧
        (caps.eta = true → blockNames.contains caps.etaCtor = true) ∧
        (caps.eta = true → 0 < caps.etaFields →
          env.find? (projFnName cvA.name 0) = none) := by
    intro caps2 hceq
    exact ⟨by rw [hnameA, hlpsA]; exact (hpins caps2 hceq).1,
      (hpins caps2 hceq).2.1,
      by rw [hnameA]; exact (hpins caps2 hceq).2.2⟩
  obtain ⟨m₁, hm₁⟩ := indMemberS m hc₀name hkind hfreshA hwf hnresA
    hmE hmlps (hkey m hmv hI)
    (memberEtaS m hmv hI hbn hc₀cv hc₀name hpinsA hEC hBP)
    (fun cv2 caps2 hceq hcapu2 _ => by
      have hcv2 : cv2 = cvA := by rw [← hc₀cv, hceq]; rfl
      subst hcv2
      rw [hceq]
      exact memberUnitS m hmv hI hbn
        (by rw [hnameA, hlpsA]; exact (hpins caps2 hceq).1) hcapu2
        hnresA)
  have hfresh0 : env.find? c₀.name = none := by
    rw [hc₀name]; exact hfreshA
  have hbn0 : blockNames.contains c₀.name = true := by
    rw [hc₀name]; exact hbn
  have hshape0 : c₀.name.isProjFnShape = false := by
    rw [hc₀name, hnameA]; exact hpshape
  refine ⟨m₁, hm₁, ?_, EtaFamiliesClosedO.cons hEC hfresh0 hbn0,
    BlockEtaPinned.cons hBP hfresh0 hshape0
      (fun cvS capsS heq hcape => by
        have hcvS : cvS = cvA := by rw [← hc₀cv, heq]; rfl
        subst hcvS
        exact ⟨by rw [hc₀name]; exact (hpinsA capsS heq).1,
          (hpinsA capsS heq).2.1 hcape,
          by rw [hc₀name]; exact (hpinsA capsS heq).2.2 hcape⟩)⟩
  refine BlockInstalledTT.step hI (by rw [hc₀name]; exact hms)
    (by rw [hc₀name]; exact hmE)
    (by rw [hc₀cv]; exact hmlps)
    (by rw [hc₀cv]; exact hren)
    (fun ψ => by
      rw [hc₀name]
      exact congrFun cvalWith_self ψ)
    (fun n ψ hn => by
      rw [hc₀name] at hn
      exact congrFun (cvalWith_ne hn) ψ)


/-- **The member fold**: the non-recursor block members install, the
running valuation ends at the fold's, and the block invariant holds
of the result. -/
theorem indMembersS (hkey : MemberKeyS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} {caps : IndCaps} :
    ∀ (members : List ConstantInfo) {env : Env} (m : EnvS V env)
      {env₂ : Env} {cval₂ : TConstVal},
      (∀ ci ∈ members, blockNames.contains ci.name = true) →
      (∀ (cv : ConstantVal) (caps₂ : IndCaps),
        ConstantInfo.indInfo cv caps₂ ∈ members →
        EtaPins μ env cv.name cv.levelParams caps ∧
          (caps.eta = true →
            blockNames.contains caps.etaCtor = true) ∧
          (caps.eta = true → 0 < caps.etaFields →
            env.find? (projFnName cv.name 0) = none)) →
      IndMembersR μ F blockNames caps env m.cval members env₂ cval₂ →
      BlockInstalledTT blockNames env m.cval →
      EtaFamiliesClosedO blockNames env →
      BlockEtaPinned μ blockNames env →
      ∃ m₂ : EnvS V env₂,
        m₂.cval = cval₂ ∧ BlockInstalledTT blockNames env₂ cval₂ ∧
          EtaFamiliesClosedO blockNames env₂ ∧
          BlockEtaPinned μ blockNames env₂ := by
  intro members
  induction members with
  | nil =>
    intro env m env₂ cval₂ hbn hp h hI hEC hBP
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨m, rfl, hI, hEC, hBP⟩
  | cons ci rest ih =>
    intro env m env₂ cval₂ hbn hp h hI hEC hBP
    obtain ⟨cvA, hmv, hmatch⟩ := h
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
      obtain ⟨m₁, hm₁cval, hI₁, hEC₁, hBP₁⟩ :=
        memberInstallS hkey m hmv
        hI hbnA
        (fun caps₃ heq => by
          obtain ⟨-, -, -, rfl⟩ := ConstantInfo.indInfo.inj heq
          exact hp cv caps' List.mem_cons_self)
        hEC hBP
        rfl rfl (Or.inl ⟨caps, rfl⟩)
      exact ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
        (fun cv₂ caps₂ hmem => etaMemberData_step hfreshA hpshapeA
          (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)))
        (by rw [hm₁cval]; exact hmatch)
        (by rw [hm₁cval]; exact hI₁) hEC₁ hBP₁
    | ctorInfo cv nP nF =>
      obtain ⟨m₁, hm₁cval, hI₁, hEC₁, hBP₁⟩ :=
        memberInstallS hkey m hmv
        hI hbnA (fun caps₃ heq => ConstantInfo.noConfusion heq)
        hEC hBP
        rfl rfl (Or.inr (Or.inl ⟨nP, nF, rfl⟩))
      exact ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
        (fun cv₂ caps₂ hmem => etaMemberData_step hfreshA hpshapeA
          (hp cv₂ caps₂ (List.mem_cons_of_mem _ hmem)))
        (by rw [hm₁cval]; exact hmatch)
        (by rw [hm₁cval]; exact hI₁) hEC₁ hBP₁
    | axiomInfo cv => exact nomatch hmatch
    | defnInfo cv v hint => exact nomatch hmatch
    | thmInfo cv v => exact nomatch hmatch
    | recInfo cv mI rP rules => exact nomatch hmatch
    | projInfo e => exact nomatch hmatch

/-- **The recursor provisioning fold**: the group's recursors install
rule-less, giving the *self* environment the rule checks are run
against, its valuation, and the checked list. -/
theorem provisionRecsS (hkey : MemberKeyS V)
    {μ : CheckMode} {F : Nat}
    {blockNames : List Name} :
    ∀ (recs : List ConstantInfo) {envAcc : Env} (m : EnvS V envAcc)
      {envSelf : Env} {cvalSelf : TConstVal}
      {checked : List (ConstantVal × Nat × Nat × List RecRule)},
      (∀ ci ∈ recs, blockNames.contains ci.name = true) →
      ProvisionRecsR μ F blockNames envAcc m.cval recs envSelf cvalSelf
        checked →
      BlockInstalledTT blockNames envAcc m.cval →
      EtaFamiliesClosedO blockNames envAcc →
      BlockEtaPinned μ blockNames envAcc →
      ∃ mS : EnvS V envSelf,
        mS.cval = cvalSelf ∧
        BlockInstalledTT blockNames envSelf cvalSelf ∧
        EtaFamiliesClosedO blockNames envSelf ∧
        BlockEtaPinned μ blockNames envSelf := by
  intro recs
  induction recs with
  | nil =>
    intro envAcc m envSelf cvalSelf checked hbn h hI hEC hBP
    obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨m, rfl, hI, hEC, hBP⟩
  | cons ci rest ih =>
    intro envAcc m envSelf cvalSelf checked hbn h hI hEC hBP
    obtain ⟨cvA, mI, rP, rules, rest', hciE, hmv, hrec, -⟩ := h
    obtain ⟨type', hcv, hcvA, -⟩ := id hmv
    have hnameA : cvA.name = ci.toConstantVal.name := by rw [hcvA]
    obtain ⟨m₁, hm₁cval, hI₁, hEC₁, hBP₁⟩ :=
      memberInstallS hkey m hmv
      hI (by rw [hnameA]; exact hbn ci List.mem_cons_self)
      (fun caps₃ heq => ConstantInfo.noConfusion heq)
      hEC hBP
      rfl rfl (Or.inr (Or.inr ⟨mI, rP, rfl⟩))
    exact ih m₁ (fun ci' hci' => hbn ci' (List.mem_cons_of_mem _ hci'))
      (by rw [hm₁cval]; exact hrec)
      (by rw [hm₁cval]; exact hI₁) hEC₁ hBP₁

/-- **`MemberKeyS`, discharged.**  The witness is *given*: the member
takes its model artifact's valuation, so `EnvS.cval_memType` at the
stored `_model` constant supplies the membership and the truthfulness
outright.  All that is left is that the two types denote the same —
the block renaming carries `cvA.type` to `cvm.type` up to
`eqUpToNames`, and `denote` is blind to exactly that difference.

The renaming is used at a *member* environment, where the block's
later members are not stored yet, so the full `RenameOkT` is
unavailable; `denote_renameConsts_resolve` needs only the two clauses
`BlockInstalledTT` supplies, because `cvA.type` resolves. -/
theorem memberKeyS : MemberKeyS V := by
  intro μ F blockNames env m cv cvA hmv hIB ψ
  obtain ⟨type', hcv, rfl, -, cvm, mval, hint, hfm, hlpm, hren⟩ := hmv
  obtain ⟨-, hres, -, -, -, -, hann, -, htr, -⟩ := hcv
  have hup : ∀ n ci, env.find? n = some ci →
      ∃ ci', env.find? ((fun n =>
          if blockNames.contains n then n.str "_model" else n) n)
        = some ci' ∧
        ci'.toConstantVal.levelParams
          = ci.toConstantVal.levelParams := by
    intro n ci hfn
    dsimp only
    by_cases hb : blockNames.contains n = true
    · obtain ⟨cvm', mval', hint', hfm', hlp', -, -⟩ := hIB n hb ci hfn
      exact ⟨.defnInfo cvm' mval' hint', by rw [if_pos hb]; exact hfm',
        hlp'⟩
    · exact ⟨ci, by rw [if_neg hb]; exact hfn, rfl⟩
  have hval : ∀ (n : Name) (ci : ConstantInfo),
      env.find? n = some ci → ∀ ψ' : Name → Nat,
      m.cval ((fun n =>
        if blockNames.contains n then n.str "_model" else n) n) ψ'
        = m.cval n ψ' := by
    intro n ci hfn ψ'
    dsimp only
    by_cases hb : blockNames.contains n = true
    · obtain ⟨-, -, -, -, -, -, hv⟩ := hIB n hb ci hfn
      rw [if_pos hb, ← hv ψ']
    · rw [if_neg hb]
  -- the model constant's own membership, and the two types agree
  obtain ⟨t, ht, hlaw⟩ :=
    EnvS.cval_memType m (n := (cv.name.str "_model")) hfm ψ
  refine ⟨t, ?_, hlaw⟩
  show denoteClosed m.cval env ψ type' = some t
  rw [← ht]
  show denote m.cval env ψ 0 type' = denote m.cval env ψ 0 cvm.type
  rw [← denote_erasedEq (Expr.ErasedEq.of_eqUpToNames hren) 0]
  exact (denote_renameConsts_resolve (φ := ψ) hup hval type' 0
    htr).symm

end Setlec.SetR
