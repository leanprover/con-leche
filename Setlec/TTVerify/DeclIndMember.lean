import Setlec.TTVerify.EnvSwap
import Setlec.Verify.Extend.Block
import Setlec.TTVerify.DeclInd
import Setlec.Verify.Extend.Modeled
import Setlec.Verify.Extend.Ind

/-!
# The modeled-inductive member installs

Transpose of `Setlec/Model/Extend/{Modeled,Ind}.lean`'s member phase:
the block fold invariant (`BlockInstalledTT`), extension by one opaque
modeled member (`extendModeledOneTT`, an `EnvTT.cons` whose valuation
aliases the `_model` companion's), and the `checkIndMember` step /
fold soundness.  The capability-law head obligations are forwarded to
the block assembly exactly as the model forwards them
(`checkIndMember_sound`'s `hheadEta`), because only the assembly knows
whether the member completes a family.
-/

set_option linter.unusedVariables false

namespace Setlec.TTVerify

/- Task #147: stated at the TT-lane mode. -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

variable {F : Nat}

/- The block fold invariant (`BlockInstalledTT` + `.step`/`.fresh_cons`/
`.renameOkT`) and the member valuation (`cvalAlias` + lemmas) relocated
to `Setlec/Verify/Extend/Block.lean` (task #148, T5) — V-free and
lane-shared; the [set] member fold consumes the same machinery. -/

/-- `ValParams` of an extended valuation whose block members are valued
by their `_model` companions.  Transpose of
`ConstValParams.extend_head`. -/
theorem ValParams.extend_head {env : Env} (m : EnvTT env)
    {ci : ConstantInfo} {cval₁ : TConstVal} {blockNames : List Name}
    (hagree : ∀ (n : Name), n ≠ ci.name → cval₁ n = m.cval n)
    (hI₁ : BlockInstalledTT blockNames (⟨ci :: env.consts⟩ : Env) cval₁)
    (hciblock : blockNames.contains ci.name = true) :
    ValParams (⟨ci :: env.consts⟩ : Env) cval₁ := by
  intro n ci₂ hf ψ₁ ψ₂ hψ
  by_cases hn : n = ci.name
  · subst hn
    rw [Env.find?_cons, if_pos rfl] at hf
    obtain rfl : ci = ci₂ := Option.some.inj hf
    obtain ⟨cvm, mval, hm, hfm, hlps, -, hv⟩ := hI₁ ci.name hciblock ci
      (by rw [Env.find?_cons, if_pos rfl])
    have hfmE : env.find? (ci.name.str "_model") =
        some (.defnInfo cvm mval hm) := by
      rw [Env.find?_cons,
        if_neg (fun h => Name.str_ne ci.name "_model" h.symm)] at hfm
      exact hfm
    rw [hv ψ₁, hv ψ₂,
      show cval₁ (ci.name.str "_model")
        = m.cval (ci.name.str "_model") from
        hagree _ (Name.str_ne ci.name "_model")]
    refine m.val_params _ _ hfmE ψ₁ ψ₂ ?_
    intro p hp
    refine hψ p ?_
    rw [show (ConstantInfo.defnInfo cvm mval hm).toConstantVal = cvm
      from rfl] at hp
    rw [← hlps]
    exact hp
  · rw [Env.find?_cons, if_neg (fun h => hn h.symm)] at hf
    rw [show cval₁ n = m.cval n from hagree n hn]
    exact m.val_params n ci₂ hf ψ₁ ψ₂ hψ

/-! ## Extension by one opaque modeled member -/

set_option maxHeartbeats 1600000 in
/-- Extend a derivation model by one opaque modeled inductive-kind
member: its value is its `_model` companion's, and its type denotes
identically through the block renaming.  Transpose of
`extend_modeled_one`, assembled through `EnvTT.cons`; the
capability-law and constructor-residual head obligations are
forwarded, because only the block assembly can discharge or refute
them. -/
def extendModeledOneTT {env : Env} (m : EnvTT env)
    (ci : ConstantInfo) {blockNames : List Name}
    {cvm : ConstantVal} {mval : Expr} {hmcvm : ReducibilityHint}
    (hfind' : env.find? ci.name = none)
    (hnres : reservedBasisNames.contains ci.name = false)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (htyf : ci.toConstantVal.type.hasFvar = false)
    (htyb : ci.toConstantVal.type.looseBVarsBounded 0 = true)
    (hkind : (∃ cv caps, ci = .indInfo cv caps) ∨
      (∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
      (∃ cv mI rP, ci = .recInfo cv mI rP []))
    (hmodel : env.find? (ci.name.str "_model") =
      some (.defnInfo cvm mval hmcvm))
    (hlps : cvm.levelParams = ci.toConstantVal.levelParams)
    (hren : Expr.eqUpToNames (ci.toConstantVal.type.renameConsts (fun n =>
      if blockNames.contains n then n.str "_model" else n))
      cvm.type = true)
    (hIB : BlockInstalledTT blockNames env m.cval)
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
      (⟨ci :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨ci :: env.consts⟩ T caps →
      (T = ci.name ∨ caps.etaCtor = ci.name ∨
        ∃ j, j < caps.etaFields ∧ projFnName T j = ci.name) →
      EtaLawTT ⟨ci :: env.consts⟩
        (cvalAlias m.cval ci.name (ci.name.str "_model")) T cvT caps)
    (hheadUnit : ∀ cv caps, ci = .indInfo cv caps →
      caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      UnitLawTT ⟨ci :: env.consts⟩
        (cvalAlias m.cval ci.name (ci.name.str "_model"))
        ci.name cv caps)
    (hheadResid : ∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps)
      (cvC : ConstantVal),
      (⟨ci :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
      caps.eta = true →
      reservedBasisNames.contains T = false →
      reservedBasisNames.contains caps.etaCtor = false →
      (⟨ci :: env.consts⟩ : Env).find? caps.etaCtor =
        some (.ctorInfo cvC caps.etaParams caps.etaFields) →
      (T = ci.name ∨ caps.etaCtor = ci.name) →
      CtorResidualPin T cvT.levelParams cvC caps.etaParams
        caps.etaFields) :
    EnvTT ⟨ci :: env.consts⟩ := by
  have hag : ∀ n, n ≠ ci.name →
      m.cval n = cvalAlias m.cval ci.name (ci.name.str "_model") n :=
    fun n hn => (cvalAlias_ne hn).symm
  have hi : Installs env m.cval
      (cvalAlias m.cval ci.name (ci.name.str "_model")) ci :=
    Installs.of_fresh hfind' hag
  -- the type's denotation is the model type's (through the pruned
  -- renaming and the display-name erasure)
  have hroS : RenameOkT m.cval env (fun n =>
      if (env.find? n).isSome = true then
        (if blockNames.contains n then n.str "_model" else n) else n) :=
    hIB.renameOkT
  have hrenS : Expr.eqUpToNames (ci.toConstantVal.type.renameConsts
      (fun n => if (env.find? n).isSome = true then
        (if blockNames.contains n then n.str "_model" else n) else n))
      cvm.type = true := by
    rw [Expr.renameConsts_congr_resolve (f := fun n =>
      if (env.find? n).isSome = true then
        (if blockNames.contains n then n.str "_model" else n) else n)
      (g := fun n =>
        if blockNames.contains n then n.str "_model" else n)
      (fun n hn => by simp only [hn, if_true]) _ htyres0]
    exact hren
  have hkey : ∀ ψ : Name → Nat, ∃ t,
      denoteClosed m.cval env ψ ci.toConstantVal.type = some t ∧
        HasType [] (m.cval (ci.name.str "_model") ψ) t := by
    intro ψ
    obtain ⟨t, hT, hd⟩ := m.has_type _ (find?_mem hmodel) ψ
    have hname : (ConstantInfo.defnInfo cvm mval hmcvm).name
        = ci.name.str "_model" := by
      simpa using List.find?_some hmodel
    refine ⟨t, ?_, by rw [← hname]; exact hd⟩
    show denote m.cval env ψ 0 ci.toConstantVal.type = some t
    rw [← denote_renameConsts hroS ci.toConstantVal.type 0,
      denote_erasedEq (Expr.ErasedEq.of_eqUpToNames hrenS) 0]
    exact hT
  refine EnvTT.cons m hi (EnvWF.cons m.wf hwf) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    hheadEta hheadUnit hheadResid ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the valuation is closed
    intro ψ
    rw [show cvalAlias m.cval ci.name (ci.name.str "_model") ci.name ψ
      = m.cval (ci.name.str "_model") ψ from by simp [cvalAlias]]
    exact m.cval_closed _ ψ
  · -- it reads only the member's level parameters
    intro φ₁ φ₂ hp
    rw [cvalAlias_self]
    refine m.val_params _ _ hmodel φ₁ φ₂ ?_
    intro p hp'
    refine hp p ?_
    rw [show (ConstantInfo.defnInfo cvm mval hmcvm).toConstantVal = cvm
      from rfl] at hp'
    rw [← hlps]
    exact hp'
  · -- and it has a derivation of the member's type
    intro φ
    obtain ⟨t, ht, hd⟩ := hkey φ
    refine ⟨t, hi.denoteUp ht, ?_⟩
    rw [show cvalAlias m.cval ci.name (ci.name.str "_model") ci.name φ
      = m.cval (ci.name.str "_model") φ from by simp [cvalAlias]]
    exact hd
  · -- no definition is installed
    intro cv2 value2 hint2 heq φ
    rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
      ⟨cv', mI', rP', rfl⟩ <;> exact nomatch heq
  · -- no theorem is installed
    intro cv2 value2 heq φ
    rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
      ⟨cv', mI', rP', rfl⟩ <;> exact nomatch heq
  · -- `Empty` is reserved
    intro hE
    exact absurd (hE ▸ hnres) (by decide)
  · -- a provisioned recursor has no rules whose ctors are owed
    intro cv2 mI2 rP2 rules2 heq r hr
    rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
      ⟨cv', mI', rP', rfl⟩
    · exact nomatch heq
    · exact nomatch heq
    · injection heq with h1 h2 h3 h4
      subst h4
      exact nomatch hr
  · -- and no rules to fold
    intro cv2 mI2 rP2 rules2 heq rl hrl
    rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
      ⟨cv', mI', rP', rfl⟩
    · exact nomatch heq
    · exact nomatch heq
    · injection heq with h1 h2 h3 h4
      subst h4
      exact nomatch hrl
  · -- no projection-table entry
    intro entry heq
    rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
      ⟨cv', mI', rP', rfl⟩ <;> exact nomatch heq
  · -- no pinned pair projection
    intro i entry heq
    rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
      ⟨cv', mI', rP', rfl⟩ <;> exact nomatch heq
  · -- `Eq` is reserved
    intro hE
    rw [hE] at hnres
    exact nomatch hnres
  · -- the member is not reserved
    intro hres
    rw [hres] at hnres
    exact nomatch hnres
  · -- no `Nat` operation
    intro cv2 v2 hint2 heq
    rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
      ⟨cv', mI', rP', rfl⟩ <;> exact nomatch heq
  · -- no WF-recursive operation
    intro cv2 v2 hint2 heq
    rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
      ⟨cv', mI', rP', rfl⟩ <;> exact nomatch heq
  · -- no compiler-trust opaque
    intro cv2 heq
    rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
      ⟨cv', mI', rP', rfl⟩ <;> exact nomatch heq

/-- The extension's valuation, by construction. -/
theorem extendModeledOneTT_cval {env : Env} (m : EnvTT env)
    (ci : ConstantInfo) {blockNames : List Name}
    {cvm : ConstantVal} {mval : Expr} {hmcvm : ReducibilityHint}
    (hfind' : env.find? ci.name = none)
    (hnres : reservedBasisNames.contains ci.name = false)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (htyf : ci.toConstantVal.type.hasFvar = false)
    (htyb : ci.toConstantVal.type.looseBVarsBounded 0 = true)
    (hkind : (∃ cv caps, ci = .indInfo cv caps) ∨
      (∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
      (∃ cv mI rP, ci = .recInfo cv mI rP []))
    (hmodel : env.find? (ci.name.str "_model") =
      some (.defnInfo cvm mval hmcvm))
    (hlps : cvm.levelParams = ci.toConstantVal.levelParams)
    (hren : Expr.eqUpToNames (ci.toConstantVal.type.renameConsts (fun n =>
      if blockNames.contains n then n.str "_model" else n))
      cvm.type = true)
    (hIB : BlockInstalledTT blockNames env m.cval)
    (hheadEta) (hheadUnit) (hheadResid) :
    (extendModeledOneTT m ci hfind' hnres hwf htyres0 htyf htyb hkind
        hmodel hlps hren hIB hheadEta hheadUnit hheadResid).cval =
      cvalAlias m.cval ci.name (ci.name.str "_model") := rfl

/-! ## The capability laws at a family-completing member

Transpose of `Setlec/Model/ModeledCaps.lean`: the public-name laws
from the pins and the block identification, through the landed folds
(`UnitFoldTT`/`EtaFoldTT`) instead of the model's `*_rule_fold`s. -/

section Laws

variable {env : Env} (m : EnvTT env)
  {ci : ConstantInfo} {blockNames : List Name} {cval₁ : TConstVal}
  (hfresh : env.find? ci.name = none)
  (hcinres : reservedBasisNames.contains ci.name = false)
  (hkind : (∃ cv caps, ci = .indInfo cv caps) ∨
    (∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
    (∃ cv mI rP rules, ci = .recInfo cv mI rP rules))
  (hagree : ∀ n, n ≠ ci.name → cval₁ n = m.cval n)
  (hcl : ∀ n ψ, VExpr.Closed (cval₁ n ψ))
  (hvp : ValParams (⟨ci :: env.consts⟩ : Env) cval₁)
  (hI₁ : BlockInstalledTT blockNames (⟨ci :: env.consts⟩ : Env) cval₁)

/-- The head is the modeled member, so a stored thm/defn lookup at the
extended environment lands below it. -/
private theorem member_below
    (hkind' : (∃ cv caps, ci = .indInfo cv caps) ∨
      (∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
      (∃ cv mI rP rules, ci = .recInfo cv mI rP rules))
    {nn : Name} {ciX : ConstantInfo}
    (hf : (⟨ci :: env.consts⟩ : Env).find? nn = some ciX)
    (hnI : ∀ cv caps', ciX ≠ .indInfo cv caps')
    (hnC : ∀ cv nP nF, ciX ≠ .ctorInfo cv nP nF)
    (hnR : ∀ cv mI rP rules, ciX ≠ .recInfo cv mI rP rules) :
    env.find? nn = some ciX := by
  rw [Env.find?_cons] at hf
  split at hf
  · obtain rfl := Option.some.inj hf
    rcases hkind' with ⟨cv', caps', rfl⟩ | ⟨cv', a, b, rfl⟩ |
      ⟨cv', a, b, c, rfl⟩
    · exact absurd rfl (hnI _ _)
    · exact absurd rfl (hnC _ _ _)
    · exact absurd rfl (hnR _ _ _ _)
  · exact hf

include hcinres hagree in
private theorem member_eq_law :
    EqLawTT (⟨ci :: env.consts⟩ : Env) cval₁ := by
  refine EqLawTT.cons m.eq_law
    (fun n hn => (hagree n hn).symm) ?_
  intro hE
  exfalso
  rw [hE] at hcinres
  exact absurd hcinres (by decide)

set_option maxHeartbeats 3200000 in
include m hfresh hcinres hkind hagree hcl hvp hI₁ in
/-- The unit-like law of a stored unit-capable modeled former, at the
extension by one fresh block member.  Transpose of
`modeled_caps_unit`, through `UnitFoldTT`; the valuation is abstract,
because the member phase aliases `n._model` while the projection
phase aliases `T._model.proj_i`. -/
theorem modeledCapsUnitTT
    {T : Name} {cvTa : ConstantVal} {capsT : IndCaps}
    (hcapu : capsT.unitlike = true)
    (hpins : EtaPins mode (⟨ci :: env.consts⟩ : Env) T cvTa.levelParams capsT)
    (hren : ∀ cvmT mvalT hm,
      (⟨ci :: env.consts⟩ : Env).find? (T.str "_model") =
        some (.defnInfo cvmT mvalT hm) →
      Expr.eqUpToNames (cvTa.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n))
        cvmT.type = true)
    (htres₁ : cvTa.type.constsResolve (⟨ci :: env.consts⟩ : Env) = true)
    (hvT : ∀ ψ : Name → Nat,
      cval₁ T ψ = cval₁ (T.str "_model") ψ) :
    UnitLawTT (⟨ci :: env.consts⟩ : Env) cval₁ T cvTa capsT := by
  obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE, heqfE,
    hS_stripE, hTm_stripE, hsdomsE, hxdomE, hydomE, hsbodyE,
    htySlotE, hsortE⟩ := hpins.2 hcapu
  have hag : ∀ n, n ≠ ci.name → m.cval n = cval₁ n :=
    fun n hn => (hagree n hn).symm
  have hi : Installs env m.cval cval₁ ci := Installs.of_fresh hfresh hag
  -- the artifact theorem and the model former, below the head
  have hthmE₀ : env.find? ((T.str "_model").str "unitlike") =
      some (.thmInfo tcv tval) :=
    member_below hkind hthmE (fun _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  have hTmE₀ : env.find? (T.str "_model") =
      some (.defnInfo cvmT mvalT hmT) :=
    member_below hkind hTmE (fun _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  -- wf facts
  obtain ⟨hSw, -, -, hSb, -, -, -⟩ := m.wf _ (find?_mem hthmE₀)
  obtain ⟨hTmw, -, -, hTmb, -, -, -⟩ := m.wf _ (find?_mem hTmE₀)
  -- the pruned renaming
  have hroS := hI₁.renameOkT
  have hrenS : Expr.eqUpToNames (cvTa.type.renameConsts (fun n =>
      if ((⟨ci :: env.consts⟩ : Env).find? n).isSome = true then
        (if blockNames.contains n then n.str "_model" else n) else n))
      cvmT.type = true := by
    rw [Expr.renameConsts_congr_resolve
      (g := fun n => if blockNames.contains n then n.str "_model" else n)
      (fun n hn => by simp only [hn, if_true]) _ htres₁]
    exact hren cvmT mvalT hmT hTmE
  -- the two typings, transported up
  have hnameThm : tcv.name = (T.str "_model").str "unitlike" := by
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
      List.find?_some hthmE₀
  have hthmty : ∀ psi : Name → Nat, ∃ t,
      denoteClosed cval₁ (⟨ci :: env.consts⟩ : Env) psi tcv.type
        = some t ∧
      HasType [] (cval₁ tcv.name psi) t := by
    intro psi
    obtain ⟨t, ht, hd⟩ := m.has_type _ (find?_mem hthmE₀) psi
    refine ⟨t, hi.denoteUp ht, ?_⟩
    rw [hagree _ (show tcv.name ≠ ci.name from by
      rw [hnameThm]
      exact Ne.symm (ne_of_isSome_fresh hfresh (by rw [hthmE₀]; rfl)))]
    exact hd
  have hTmty : ∀ psi : Name → Nat, ∃ t,
      denoteClosed cval₁ (⟨ci :: env.consts⟩ : Env) psi cvmT.type
        = some t ∧
      HasType [] (cval₁ (T.str "_model") psi) t := by
    intro psi
    obtain ⟨t, ht, hd⟩ := m.has_type _ (find?_mem hTmE₀) psi
    have hnmT : cvmT.name = T.str "_model" := by
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
        List.find?_some hTmE₀
    refine ⟨t, hi.denoteUp ht, ?_⟩
    rw [hagree _ (show T.str "_model" ≠ ci.name from
      Ne.symm (ne_of_isSome_fresh hfresh (by rw [hTmE₀]; rfl)))]
    rw [← hnmT]
    exact hd
  exact UnitFoldTT (caps := capsT) hcl hvp
    (member_eq_law m hcinres hagree) hroS hTmE hTmlpsE heqfE hS_stripE
    hTm_stripE hsdomsE hxdomE hydomE hsbodyE htySlotE (hsortE rfl) hSw hSb
    hTmw hTmb hrenS hthmty hTmty hvT

set_option maxHeartbeats 3200000 in
include m hfresh hcinres hkind hagree hcl hvp hI₁ in
/-- The structural-eta law of a stored eta-capable modeled former, at
the extension by one fresh block member.  Transpose of
`modeled_caps_eta`, through `EtaFoldTT`; the valuation is abstract for
the same reason as `modeledCapsUnitTT`'s. -/
theorem modeledCapsEtaTT
    {T : Name} {cvTa : ConstantVal} {capsT : IndCaps}
    (hcape : capsT.eta = true)
    (hpins : EtaPins mode (⟨ci :: env.consts⟩ : Env) T cvTa.levelParams capsT)
    (hren : ∀ cvmT mvalT hm,
      (⟨ci :: env.consts⟩ : Env).find? (T.str "_model") =
        some (.defnInfo cvmT mvalT hm) →
      Expr.eqUpToNames (cvTa.type.renameConsts (fun n =>
        if blockNames.contains n then n.str "_model" else n))
        cvmT.type = true)
    (htres₁ : cvTa.type.constsResolve (⟨ci :: env.consts⟩ : Env) = true)
    (hvT : ∀ ψ : Name → Nat,
      cval₁ T ψ = cval₁ (T.str "_model") ψ)
    (hvC : ∀ ψ : Name → Nat,
      cval₁ capsT.etaCtor ψ = cval₁ (capsT.etaCtor.str "_model") ψ)
    (hvP : ∀ j, j < capsT.etaFields → ∀ ψ : Name → Nat,
      cval₁ (projFnName T j) ψ = cval₁ (projModelName T j) ψ)
    (hlpsC : levelParamsAt (⟨ci :: env.consts⟩ : Env) capsT.etaCtor =
      cvTa.levelParams)
    (hlpsP : ∀ j, j < capsT.etaFields →
      levelParamsAt (⟨ci :: env.consts⟩ : Env) (projFnName T j) =
      cvTa.levelParams) :
    EtaLawTT (⟨ci :: env.consts⟩ : Env) cval₁ T cvTa capsT := by
  obtain ⟨tcv, tval, cvmT, mvalT, hmT, sbinders, tbindersM, sbody,
    tbodyM, tySlot, ℓA, hthmE, htlpsE, hTmE, hTmlpsE,
    ⟨cvmC, mvalC, hmC, hCmE, hCmlpsE⟩, hPjE, heqfE, hS_stripE,
    hTm_stripE, hsdomsE, hxdomE, hsbodyE, htySlotE, hsortE⟩ :=
    hpins.1 hcape
  have hag : ∀ n, n ≠ ci.name → m.cval n = cval₁ n :=
    fun n hn => (hagree n hn).symm
  have hi : Installs env m.cval cval₁ ci := Installs.of_fresh hfresh hag
  have hthmE₀ : env.find? ((T.str "_model").str "eta") =
      some (.thmInfo tcv tval) :=
    member_below hkind hthmE (fun _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  have hTmE₀ : env.find? (T.str "_model") =
      some (.defnInfo cvmT mvalT hmT) :=
    member_below hkind hTmE (fun _ _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (fun _ _ _ _ h => nomatch h)
  obtain ⟨hSw, -, -, hSb, -, -, -⟩ := m.wf _ (find?_mem hthmE₀)
  obtain ⟨hTmw, -, -, hTmb, -, -, -⟩ := m.wf _ (find?_mem hTmE₀)
  have hroS := hI₁.renameOkT
  have hrenS : Expr.eqUpToNames (cvTa.type.renameConsts (fun n =>
      if ((⟨ci :: env.consts⟩ : Env).find? n).isSome = true then
        (if blockNames.contains n then n.str "_model" else n) else n))
      cvmT.type = true := by
    rw [Expr.renameConsts_congr_resolve
      (g := fun n => if blockNames.contains n then n.str "_model" else n)
      (fun n hn => by simp only [hn, if_true]) _ htres₁]
    exact hren cvmT mvalT hmT hTmE
  have hnameThm : tcv.name = (T.str "_model").str "eta" := by
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
      List.find?_some hthmE₀
  have hthmty : ∀ psi : Name → Nat, ∃ t,
      denoteClosed cval₁ (⟨ci :: env.consts⟩ : Env) psi tcv.type
        = some t ∧
      HasType [] (cval₁ tcv.name psi) t := by
    intro psi
    obtain ⟨t, ht, hd⟩ := m.has_type _ (find?_mem hthmE₀) psi
    refine ⟨t, hi.denoteUp ht, ?_⟩
    rw [hagree _ (show tcv.name ≠ ci.name from by
      rw [hnameThm]
      exact Ne.symm (ne_of_isSome_fresh hfresh (by rw [hthmE₀]; rfl)))]
    exact hd
  have hTmty : ∀ psi : Name → Nat, ∃ t,
      denoteClosed cval₁ (⟨ci :: env.consts⟩ : Env) psi cvmT.type
        = some t ∧
      HasType [] (cval₁ (T.str "_model") psi) t := by
    intro psi
    obtain ⟨t, ht, hd⟩ := m.has_type _ (find?_mem hTmE₀) psi
    have hnmT : cvmT.name = T.str "_model" := by
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
        List.find?_some hTmE₀
    refine ⟨t, hi.denoteUp ht, ?_⟩
    rw [hagree _ (show T.str "_model" ≠ ci.name from
      Ne.symm (ne_of_isSome_fresh hfresh (by rw [hTmE₀]; rfl)))]
    rw [← hnmT]
    exact hd
  exact EtaFoldTT (caps := capsT) hcl hvp
    (member_eq_law m hcinres hagree) hroS hTmE hTmlpsE hCmE hCmlpsE
    hPjE heqfE hS_stripE hTm_stripE hsdomsE hxdomE hsbodyE htySlotE
    (hsortE rfl) hSw hSb hTmw hTmb hrenS hthmty hTmty hvT hvC hvP hlpsC hlpsP

end Laws

/-! ## The uniform head-eta discharge at a member install -/

set_option maxHeartbeats 3200000 in
/-- The uniform eta head-obligation discharge for a modeled block
member's install.  Transpose of `blockMember_headEta`: a family
completed by the member belongs either to a *block* former — refuted
while projection functions are pending, established through
`modeledCapsEtaTT` when the family is fieldless-complete — or to an
*outside* former, whose family is already closed. -/
theorem blockMemberHeadEtaTT {env : Env} (m : EnvTT env)
    {ciH : ConstantInfo} {blockNames : List Name}
    (hfresh : env.find? ciH.name = none)
    (hcinres : reservedBasisNames.contains ciH.name = false)
    (hshape : ciH.name.isProjFnShape = false)
    (hkind : (∃ cv caps, ciH = .indInfo cv caps) ∨
      (∃ cv nP nF, ciH = .ctorInfo cv nP nF) ∨
      (∃ cv mI rP rules, ciH = .recInfo cv mI rP rules))
    (hciblock : blockNames.contains ciH.name = true)
    (hE1 : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
      env.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → reservedBasisNames.contains T = false →
      blockNames.contains T = false →
      ∃ cvC, env.find? capsT.etaCtor =
        some (.ctorInfo cvC capsT.etaParams capsT.etaFields))
    (hblockT : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
      (⟨ciH :: env.consts⟩ : Env).find? T = some (.indInfo cvT capsT) →
      blockNames.contains T = true → capsT.eta = true →
      EtaPins mode env T cvT.levelParams capsT ∧
      blockNames.contains capsT.etaCtor = true ∧
      cvT.type.constsResolve env = true ∧
      ∀ j, j < capsT.etaFields → env.find? (projFnName T j) = none)
    (hI₁ : BlockInstalledTT blockNames ⟨ciH :: env.consts⟩
      (cvalAlias m.cval ciH.name (ciH.name.str "_model"))) :
    ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
      (⟨ciH :: env.consts⟩ : Env).find? T = some (.indInfo cvT capsT) →
      capsT.eta = true → reservedBasisNames.contains T = false →
      EtaFamilyStored ⟨ciH :: env.consts⟩ T capsT →
      (T = ciH.name ∨ capsT.etaCtor = ciH.name ∨
        ∃ j, j < capsT.etaFields ∧ projFnName T j = ciH.name) →
      EtaLawTT ⟨ciH :: env.consts⟩
        (cvalAlias m.cval ciH.name (ciH.name.str "_model")) T cvT capsT := by
  intro T cvT capsT hfT hcape hresT hfam hpart
  have hPneH : ∀ j, projFnName T j ≠ ciH.name := by
    intro j hh
    rw [← hh] at hshape
    rw [show (projFnName T j).isProjFnShape = true from rfl] at hshape
    exact nomatch hshape
  by_cases hTb : blockNames.contains T = true
  · -- a block former's family
    obtain ⟨hpinsT, hCb, htresT, hPfree⟩ := hblockT T cvT capsT hfT hTb hcape
    obtain ⟨hCres, ⟨cvC, hfC⟩, hfP⟩ := hfam
    cases hEF : capsT.etaFields with
    | succ k =>
      -- a projection function would have to be stored already, but the
      -- family's projection names are still free
      exfalso
      obtain ⟨cv2, mI2, rP2, rules2, hf2⟩ := hfP 0 (by omega)
      rw [Env.find?_cons,
        if_neg (fun hh => hPneH 0 hh.symm)] at hf2
      rw [hPfree 0 (by omega)] at hf2
      exact nomatch hf2
    | zero =>
      -- the family is complete: establish the law
      obtain ⟨cvm', mval', hm', hfm', hlps', hren', hvT'⟩ :=
        hI₁ T hTb _ hfT
      have hvC' : ∀ ψ : Name → Nat,
          cvalAlias m.cval ciH.name (ciH.name.str "_model")
            capsT.etaCtor ψ =
          cvalAlias m.cval ciH.name (ciH.name.str "_model")
            (capsT.etaCtor.str "_model") ψ := by
        intro ψ
        obtain ⟨cvmC, mvalC, hmC, hfmC, -, -, hvC⟩ :=
          hI₁ capsT.etaCtor hCb _ hfC
        exact hvC ψ
      -- the capability constructor's stored level parameters are the
      -- family's: its model is the pins' model
      have hpins₁ : EtaPins mode ⟨ciH :: env.consts⟩ T cvT.levelParams capsT :=
        EtaPins.step hpinsT hfresh
      have hlpsC : levelParamsAt (⟨ciH :: env.consts⟩ : Env)
          capsT.etaCtor = cvT.levelParams := by
        obtain ⟨cvmC2, mvalC2, hmC2, hfmC2, hlpsC2, -, -⟩ :=
          hI₁ capsT.etaCtor hCb _ hfC
        obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
          ⟨cvmC, mvalC, hmC, hCmE, hCmlpsE⟩, -⟩ := hpins₁.1 hcape
        rw [hfmC2] at hCmE
        obtain heq := Option.some.inj hCmE
        injection heq with e1 e2 e3
        subst e1
        unfold levelParamsAt
        rw [hfC]
        show cvC.levelParams = cvT.levelParams
        rw [show (ConstantInfo.ctorInfo cvC capsT.etaParams
          capsT.etaFields).toConstantVal = cvC from rfl] at hlpsC2
        rw [← hlpsC2]
        exact hCmlpsE
      refine modeledCapsEtaTT (ci := ciH) m hfresh hcinres hkind
        (fun n hn => cvalAlias_ne hn) (cvalAlias_closed m.cval_closed)
        (ValParams.extend_head m (fun n hn => cvalAlias_ne hn) hI₁
          hciblock)
        hI₁ hcape hpins₁ ?_
        (Expr.constsResolve_mono htresT) hvT' hvC'
        (fun j hj ψ => by rw [hEF] at hj; exact absurd hj (by omega))
        hlpsC
        (fun j hj => by rw [hEF] at hj; exact absurd hj (by omega))
      · intro cvmT mvalT hm2 hfm₁
        rw [hfm'] at hfm₁
        obtain h1 := Option.some.inj hfm₁
        injection h1 with e1 e2 e3
        subst e1
        exact hren'
  · -- an outside former: its family is closed, so the fresh head
    -- cannot participate
    exfalso
    have hTneH : T ≠ ciH.name := by
      intro he
      rw [he, hciblock] at hTb
      exact hTb rfl
    have hfT' : env.find? T = some (.indInfo cvT capsT) := by
      rw [Env.find?_cons, if_neg (fun hh => hTneH hh.symm)] at hfT
      exact hfT
    have hTbf : blockNames.contains T = false := by
      revert hTb
      cases blockNames.contains T <;> simp
    obtain ⟨cvC, hfC⟩ := hE1 T cvT capsT hfT' hcape hresT hTbf
    rcases hpart with rfl | hC | ⟨j, hj, hP⟩
    · exact hTneH rfl
    · have hsC : (env.find? capsT.etaCtor).isSome = true := by
        rw [hfC]
        rfl
      rw [hC, hfresh] at hsC
      exact nomatch hsC
    · exact hPneH j hP

set_option maxHeartbeats 3200000 in
/-- One `checkIndMember` step preserves having a derivation model
together with the fold invariant.  Transpose of
`checkIndMember_sound`; the eta and constructor-residual head
obligations are forwarded to the caller, the unit law of a freshly
installed unit-like former is discharged here through
`modeledCapsUnitTT`. -/
theorem checkIndMemberTT {blockNames : List Name} {caps : IndCaps}
    {env' env₁ : Env} {ci : ConstantInfo}
    (h : checkIndMember (fueledOps mode F) blockNames caps env' ci = .ok env₁)
    (hpins : ∀ cv caps₂, ci = .indInfo cv caps₂ →
      EtaPins mode env' cv.name cv.levelParams caps)
    (hbn : blockNames.contains ci.name = true)
    (m : EnvTT env') (hI : BlockInstalledTT blockNames env' m.cval)
    (hheadEta : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
      env₁.find? T = some (.indInfo cvT capsT) → capsT.eta = true →
      reservedBasisNames.contains T = false →
      EtaFamilyStored env₁ T capsT →
      (T = ci.name ∨ capsT.etaCtor = ci.name ∨
        ∃ j, j < capsT.etaFields ∧ projFnName T j = ci.name) →
      ∀ cval₁ : TConstVal,
        (∀ n, n ≠ ci.name → cval₁ n = m.cval n) →
        cval₁ ci.name = m.cval (ci.name.str "_model") →
        BlockInstalledTT blockNames env₁ cval₁ →
        EtaLawTT env₁ cval₁ T cvT capsT)
    (hheadResid : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps)
      (cvC : ConstantVal),
      env₁.find? T = some (.indInfo cvT capsT) →
      capsT.eta = true →
      reservedBasisNames.contains T = false →
      reservedBasisNames.contains capsT.etaCtor = false →
      env₁.find? capsT.etaCtor =
        some (.ctorInfo cvC capsT.etaParams capsT.etaFields) →
      (T = ci.name ∨ capsT.etaCtor = ci.name) →
      CtorResidualPin T cvT.levelParams cvC capsT.etaParams
        capsT.etaFields) :
    ∃ m₁ : EnvTT env₁, BlockInstalledTT blockNames env₁ m₁.cval := by
  obtain ⟨cvA, cvm, mval, hmcvm, hccv, hms, hfm, hlps, hrenf, hkind⟩ :=
    checkIndMember_inv h
  obtain ⟨hfind0, hnres0, hpshape0, hnd, hlb, hfv, tyA, stype, u, hann,
    hlp, hres, hst, hsort, hcvA⟩ := checkConstantVal_inv hccv
  have hnameA : cvA.name = ci.name := by rw [hcvA]; rfl
  have hlpsA : cvA.levelParams = ci.toConstantVal.levelParams := by
    rw [hcvA]
  have htypeA : cvA.type = tyA := by rw [hcvA]
  have hfind' : env'.find? cvA.name = none := by rw [hnameA]; exact hfind0
  have hnres : reservedBasisNames.contains cvA.name = false := by
    rw [hnameA]; exact hnres0
  have hbnA : blockNames.contains cvA.name = true := by
    rw [hnameA]; exact hbn
  have htyf : cvA.type.hasFvar = false := by
    rw [htypeA]
    exact Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F _ hann
        (Expr.WScoped.of_not_hasFvar hfv)).fvarsBelow)
  have htyb : cvA.type.looseBVarsBounded 0 = true := by
    rw [htypeA]
    exact annotateCore_looseBVars F _ hann hlb
  have htlp : cvA.type.allLevelParamsDefined cvA.levelParams = true := by
    rw [htypeA, hlpsA]
    exact hlp
  have htres : cvA.type.constsResolve env' = true := by
    rw [htypeA]; exact hres
  -- both kinds share everything but the stored constant
  have hstep : ∀ (ciS : ConstantInfo), ciS.toConstantVal = cvA →
      ciS.name = cvA.name →
      env₁ = ⟨ciS :: env'.consts⟩ →
      ((∃ cv caps', ciS = .indInfo cv caps') ∨
        (∃ cv nP nF, ciS = .ctorInfo cv nP nF) ∨
        (∃ cv mI rP, ciS = .recInfo cv mI rP [])) →
      ConstWF ⟨ciS :: env'.consts⟩ ciS →
      (∀ cv caps', ciS = .indInfo cv caps' → caps' = caps) →
      (∀ cv caps', ciS = .indInfo cv caps' →
        EtaPins mode env' cvA.name cvA.levelParams caps) →
      ∃ m₁ : EnvTT env₁, BlockInstalledTT blockNames env₁ m₁.cval := by
    intro ciS hciScv hciSname henv₁ hkindS hwfS hcapsS hpinsS
    subst henv₁
    have hfreshS : env'.find? ciS.name = none := by
      rw [hciSname]; exact hfind'
    have hnresS : reservedBasisNames.contains ciS.name = false := by
      rw [hciSname]; exact hnres
    have hbnS : blockNames.contains ciS.name = true := by
      rw [hciSname]; exact hbnA
    have hmodelS : env'.find? (ciS.name.str "_model") =
        some (.defnInfo cvm mval hmcvm) := by
      rw [hciSname]; exact hfm
    have hlpsS : cvm.levelParams = ciS.toConstantVal.levelParams := by
      rw [hciScv]; exact hlps
    have hrenS : Expr.eqUpToNames (ciS.toConstantVal.type.renameConsts
        (fun n => if blockNames.contains n then n.str "_model" else n))
        cvm.type = true := by
      rw [hciScv]; exact hrenf
    have hI₁ : BlockInstalledTT blockNames ⟨ciS :: env'.consts⟩
        (cvalAlias m.cval ciS.name (ciS.name.str "_model")) := by
      refine BlockInstalledTT.step hI ?_ hmodelS hlpsS hrenS ?_ ?_
      · rw [hciSname]; exact hms
      · intro ψ; rw [cvalAlias_self]
      · intro n ψ hn; rw [cvalAlias_ne hn]
    refine ⟨extendModeledOneTT m ciS hfreshS hnresS hwfS
      (by rw [hciScv]; exact htres) (by rw [hciScv]; exact htyf)
      (by rw [hciScv]; exact htyb) hkindS hmodelS hlpsS hrenS hI ?_ ?_
      ?_, ?_⟩
    · -- the forwarded eta head obligation, at the concrete valuation
      intro T cvT capsT hfT hcape hresT hfam hpart
      refine hheadEta T cvT capsT hfT hcape hresT hfam
        (by rw [hciSname, hnameA] at hpart; exact hpart)
        (cvalAlias m.cval ciS.name (ciS.name.str "_model"))
        ?_ ?_ hI₁
      · intro n hn
        rw [cvalAlias_ne (show n ≠ ciS.name from by
          rw [hciSname, hnameA]; exact hn)]
      · rw [show ci.name = ciS.name from by rw [hciSname, hnameA],
          cvalAlias_self]
    · -- the unit law of a freshly installed unit-like former
      intro cv2 caps₂ heq hcapu hnres₂
      subst heq
      obtain rfl : caps = caps₂ := (hcapsS cv2 caps₂ rfl).symm
      obtain rfl : cvA = cv2 := by
        rw [show (ConstantInfo.indInfo cv2 caps).toConstantVal = cv2
          from rfl] at hciScv
        exact hciScv.symm
      rw [show (ConstantInfo.indInfo cvA caps).name = cvA.name from rfl]
      -- the pins at the base, then stepped past the head
      have hpinsA : EtaPins mode env' cvA.name cvA.levelParams caps :=
        hpinsS cvA caps rfl
      refine modeledCapsUnitTT (ci := .indInfo cvA caps) m hfreshS
        hnresS (Or.inl ⟨cvA, caps, rfl⟩)
        (fun n hn => cvalAlias_ne (show n ≠ (ConstantInfo.indInfo cvA
          caps).name from hn))
        (cvalAlias_closed m.cval_closed)
        (ValParams.extend_head m (fun n hn => cvalAlias_ne hn) hI₁ hbnS)
        hI₁ hcapu
        (EtaPins.step hpinsA hfreshS) ?_
        (Expr.constsResolve_mono (show cvA.type.constsResolve env' = true
          from htres)) ?_
      · intro cvmT mvalT hm2 hfm₁
        rw [show ((⟨ConstantInfo.indInfo cvA caps :: env'.consts⟩ :
            Env).find? (cvA.name.str "_model")) =
            env'.find? (cvA.name.str "_model") from by
          rw [Env.find?_cons, if_neg (show ¬(ConstantInfo.indInfo cvA
            caps).name = cvA.name.str "_model" from
            fun hh => Name.str_ne cvA.name "_model" hh.symm)]] at hfm₁
        rw [show env'.find? (cvA.name.str "_model") =
            some (.defnInfo cvm mval hmcvm) from hmodelS] at hfm₁
        obtain h1 := Option.some.inj hfm₁
        injection h1 with e1 e2 e3
        subst e1
        exact hrenS
      · intro ψ
        rw [show (ConstantInfo.indInfo cvA caps).name = cvA.name from rfl,
          cvalAlias_self,
          cvalAlias_ne (Name.str_ne cvA.name "_model")]
    · -- the forwarded residual head obligation
      intro T cvT capsT cvC hfT hcape hTres hCres hfC hor
      refine hheadResid T cvT capsT cvC hfT hcape hTres hCres hfC ?_
      rw [show ci.name = ciS.name from by rw [hciSname, hnameA]]
      exact hor
    · -- the fold invariant, at the built model's valuation
      rw [extendModeledOneTT_cval]
      exact hI₁
  rcases hkind with ⟨⟨cv, caps', rfl⟩, rfl⟩ | ⟨cv, nP, nF, rfl, rfl⟩
  · -- inductive type former
    refine hstep (.indInfo cvA caps) rfl rfl rfl (Or.inl ⟨_, _, rfl⟩)
      ?_ ?_ ?_
    · refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_, ?_⟩
      · intro cv2 v2 h2 heq; exact nomatch heq
      · intro cv2 mI' rP' rules heq; exact nomatch heq
      · intro cv2 v2 heq; exact nomatch heq
    · intro cv2 caps2 heq
      injection heq with e1 e2
      exact e2.symm
    · intro cv2 caps2 heq
      have h1 := hpins cv caps' rfl
      show EtaPins mode env' cvA.name cvA.levelParams caps
      rw [hnameA, hlpsA]
      exact h1
  · -- constructor
    refine hstep (.ctorInfo cvA nP nF) rfl rfl rfl
      (Or.inr (Or.inl ⟨_, _, _, rfl⟩)) ?_ ?_ ?_
    · refine ⟨htyf, htlp, Expr.constsResolve_mono htres, htyb, ?_, ?_, ?_⟩
      · intro cv2 v2 h2 heq; exact nomatch heq
      · intro cv2 mI' rP' rules heq; exact nomatch heq
      · intro cv2 v2 heq; exact nomatch heq
    · intro cv2 caps2 heq; exact nomatch heq
    · intro cv2 caps2 heq; exact nomatch heq

set_option maxHeartbeats 3200000 in
/-- The fold of `checkIndDecl`'s generic (multi-constructor) branch
preserves having a derivation model with the block invariant.
Transpose of `checkIndFold_sound`, restricted to a capability record
claiming nothing (`hoffE`/`hoffU`): every capability and residual head
obligation is refuted — a block former never claims a capability, an
outside former's family is closed, so a fresh member never completes
one. -/
theorem checkIndFoldTT {blockNames : List Name} {caps : IndCaps}
    (hoffE : caps.eta = false) (hoffU : caps.unitlike = false) :
    ∀ (rest : List ConstantInfo) (env' env₂ : Env),
    (∀ ci ∈ rest, blockNames.contains ci.name = true) →
    (∀ cv caps₂, (ConstantInfo.indInfo cv caps₂) ∈ rest →
      EtaPins mode env' cv.name cv.levelParams caps) →
    rest.foldlM (checkIndMember (fueledOps mode F) blockNames caps) env'
      = .ok env₂ →
    ∀ m : EnvTT env', BlockInstalledTT blockNames env' m.cval →
    EtaFamiliesClosedO blockNames env' →
    BlockCapsPinned blockNames caps env' →
    ∃ m₂ : EnvTT env₂, BlockInstalledTT blockNames env₂ m₂.cval ∧
      EtaFamiliesClosedO blockNames env₂ ∧
      BlockCapsPinned blockNames caps env₂
  | [], env', env₂, hns, _hp, h, m, hI, hE1O, hBcaps => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ ⟨m, hI, hE1O, hBcaps⟩
  | ci :: rest, env', env₂, hns, hp, h, m, hI, hE1O, hBcaps => by
    rw [List.foldlM_cons] at h
    simp only [Bind.bind, Except.bind] at h
    cases hstep : checkIndMember (fueledOps mode F) blockNames caps env' ci with
    | error e => rw [hstep] at h; exact nomatch h
    | ok env₁ => ?_
    rw [hstep] at h
    obtain ⟨cvA', cvm', mval', hm', hccv', -, -, -, -, hkind'⟩ :=
      checkIndMember_inv hstep
    obtain ⟨hfind0', -, hpshape0', -, -, -, tyA', stype', u', -, -, -,
      -, -, hcvA'⟩ := checkConstantVal_inv hccv'
    have hnameA' : cvA'.name = ci.name := by
      rw [hcvA']
      rfl
    have hfreshc : env'.find? ci.name = none := hfind0'
    have hpshapec : ci.name.isProjFnShape = false := hpshape0'
    have henv₁ : ∃ ci₁ : ConstantInfo, ci₁.name = cvA'.name ∧
        env₁ = ⟨ci₁ :: env'.consts⟩ ∧
        ((∃ capsS, ci₁ = .indInfo cvA' capsS ∧ capsS = caps) ∨
          ∃ nP nF, ci₁ = .ctorInfo cvA' nP nF) := by
      rcases hkind' with ⟨-, rfl⟩ | ⟨cv, nP, nF, -, rfl⟩
      · exact ⟨_, rfl, rfl, Or.inl ⟨caps, rfl, rfl⟩⟩
      · exact ⟨_, rfl, rfl, Or.inr ⟨nP, nF, rfl⟩⟩
    obtain ⟨ci₁, hname₁, rfl, hshape₁⟩ := henv₁
    have hfresh₁ : env'.find? ci₁.name = none := by
      rw [hname₁, hnameA']
      exact hfind0'
    have hcin : ci₁.name = ci.name := by rw [hname₁, hnameA']
    -- kind-based facts about a stored `T` at the extension
    have hfindT : ∀ {T : Name} {cvT : ConstantVal} {capsT : IndCaps},
        (⟨ci₁ :: env'.consts⟩ : Env).find? T =
          some (.indInfo cvT capsT) → capsT.eta = true → T ≠ ci.name →
        env'.find? T = some (.indInfo cvT capsT) := by
      intro T cvT capsT hfT hcape hTne
      rw [Env.find?_cons,
        if_neg (fun hh => hTne (hh.symm.trans hcin))] at hfT
      exact hfT
    -- an old eta-capable family's constructor is not the fresh head
    have hCnotHead : ∀ {T : Name} {cvT : ConstantVal} {capsT : IndCaps},
        env'.find? T = some (.indInfo cvT capsT) → capsT.eta = true →
        reservedBasisNames.contains T = false →
        capsT.etaCtor ≠ ci.name := by
      intro T cvT capsT hfT hcape hres hC
      by_cases hTb : blockNames.contains T = true
      · have hcaps := hBcaps T cvT capsT hTb hfT
        rw [hcaps, hoffE] at hcape
        exact nomatch hcape
      · have hTbf : blockNames.contains T = false := by
          revert hTb
          cases blockNames.contains T <;> simp
        obtain ⟨cvC', hfC'⟩ := hE1O T cvT capsT hfT hcape hres hTbf
        have hsC : (env'.find? capsT.etaCtor).isSome = true := by
          rw [hfC']
          rfl
        rw [hC, hfreshc] at hsC
        exact nomatch hsC
    -- the eta head obligation is refuted
    have hheadEta : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps),
        (⟨ci₁ :: env'.consts⟩ : Env).find? T =
          some (.indInfo cvT capsT) → capsT.eta = true →
        reservedBasisNames.contains T = false →
        EtaFamilyStored ⟨ci₁ :: env'.consts⟩ T capsT →
        (T = ci.name ∨ capsT.etaCtor = ci.name ∨
          ∃ j, j < capsT.etaFields ∧ projFnName T j = ci.name) →
        ∀ cval₁ : TConstVal,
          (∀ n, n ≠ ci.name → cval₁ n = m.cval n) →
          cval₁ ci.name = m.cval (ci.name.str "_model") →
          BlockInstalledTT blockNames ⟨ci₁ :: env'.consts⟩ cval₁ →
          EtaLawTT ⟨ci₁ :: env'.consts⟩ cval₁ T cvT capsT := by
      intro T cvT capsT hfT hcape hresT hfam hpart cval₁ _ _ _
      exfalso
      rcases hpart with rfl | hC | ⟨j, hj, hP⟩
      · -- the head would be the (eta-capable) former
        rw [Env.find?_cons, if_pos hcin] at hfT
        rcases hshape₁ with ⟨capsS', heq₁, rfl⟩ | ⟨nP, nF, heq₁⟩
        · rw [heq₁] at hfT
          obtain hh := Option.some.inj hfT
          injection hh with h1 h2
          rw [← h2, hoffE] at hcape
          exact nomatch hcape
        · rw [heq₁] at hfT
          exact nomatch (Option.some.inj hfT)
      · -- the head would be the family's constructor
        obtain ⟨-, ⟨cvC, hfC⟩, -⟩ := hfam
        rw [hC, Env.find?_cons, if_pos hcin] at hfC
        rcases hshape₁ with ⟨capsS', heq₁, rfl⟩ | ⟨nP, nF, heq₁⟩
        · rw [heq₁] at hfC
          exact nomatch (Option.some.inj hfC)
        · have hTne : T ≠ ci.name := by
            intro he
            rw [he, Env.find?_cons, if_pos hcin, heq₁] at hfT
            exact nomatch (Option.some.inj hfT)
          exact hCnotHead (hfindT hfT hcape hTne) hcape hresT hC
      · rw [← hP] at hpshapec
        simp [projFnName, Name.isProjFnShape] at hpshapec
    -- so is the residual head obligation
    have hheadResid : ∀ (T : Name) (cvT : ConstantVal) (capsT : IndCaps)
        (cvC : ConstantVal),
        (⟨ci₁ :: env'.consts⟩ : Env).find? T =
          some (.indInfo cvT capsT) →
        capsT.eta = true →
        reservedBasisNames.contains T = false →
        reservedBasisNames.contains capsT.etaCtor = false →
        (⟨ci₁ :: env'.consts⟩ : Env).find? capsT.etaCtor =
          some (.ctorInfo cvC capsT.etaParams capsT.etaFields) →
        (T = ci.name ∨ capsT.etaCtor = ci.name) →
        CtorResidualPin T cvT.levelParams cvC capsT.etaParams
          capsT.etaFields := by
      intro T cvT capsT cvC hfT hcape hTres hCres hfC hor
      exfalso
      rcases hor with rfl | hC
      · rw [Env.find?_cons, if_pos hcin] at hfT
        rcases hshape₁ with ⟨capsS', heq₁, rfl⟩ | ⟨nP, nF, heq₁⟩
        · rw [heq₁] at hfT
          obtain hh := Option.some.inj hfT
          injection hh with h1 h2
          rw [← h2, hoffE] at hcape
          exact nomatch hcape
        · rw [heq₁] at hfT
          exact nomatch (Option.some.inj hfT)
      · have hTne : T ≠ ci.name := by
          intro he
          subst he
          rw [Env.find?_cons, if_pos hcin] at hfT
          rcases hshape₁ with ⟨capsS', heq₁, rfl⟩ | ⟨nP, nF, heq₁⟩
          · rw [heq₁] at hfT
            obtain hh := Option.some.inj hfT
            injection hh with h1 h2
            rw [← h2, hoffE] at hcape
            exact nomatch hcape
          · rw [heq₁] at hfT
            exact nomatch (Option.some.inj hfT)
        exact hCnotHead (hfindT hfT hcape hTne) hcape hTres hC
    obtain ⟨m₁, hI₁⟩ := checkIndMemberTT hstep
      (fun cv caps₂ heq => hp cv caps₂
        (by rw [← heq]; exact List.mem_cons_self))
      (hns ci (by simp)) m hI hheadEta hheadResid
    have hE1O₁ : EtaFamiliesClosedO blockNames ⟨ci₁ :: env'.consts⟩ := by
      intro T cvT capsT hfT hcape hres hTb
      have hTne : T ≠ ci₁.name := by
        intro he
        rw [he, hcin, hns ci (by simp)] at hTb
        exact nomatch hTb
      rw [Env.find?_cons, if_neg (fun hh => hTne hh.symm)] at hfT
      obtain ⟨cvC, hfC⟩ := hE1O T cvT capsT hfT hcape hres hTb
      refine ⟨cvC, ?_⟩
      rw [Env.find?_cons_of_isSome hfresh₁ (by rw [hfC]; rfl)]
      exact hfC
    have hBcaps₁ : BlockCapsPinned blockNames caps
        ⟨ci₁ :: env'.consts⟩ := by
      intro n cvS capsS hnb hf
      rw [Env.find?_cons] at hf
      split at hf
      · rcases hshape₁ with ⟨capsS', heq₁, rfl⟩ | ⟨nP, nF, heq₁⟩
        · rw [heq₁] at hf
          obtain h2 := Option.some.inj hf
          injection h2 with e1 e2
          exact e2.symm
        · rw [heq₁] at hf
          exact nomatch (Option.some.inj hf)
      · exact hBcaps n cvS capsS hnb hf
    exact checkIndFoldTT hoffE hoffU rest _ env₂
      (fun ci' hci' => hns ci' (by simp [hci']))
      (fun cv caps₂ hmem => EtaPins.step
        (hp cv caps₂ (List.mem_cons_of_mem _ hmem)) hfresh₁)
      h m₁ hI₁ hE1O₁ hBcaps₁

end Setlec.TTVerify
