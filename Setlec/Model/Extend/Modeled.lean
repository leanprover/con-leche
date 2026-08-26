import Setlec.Verify.Extend.Modeled
import Setlec.Model.Extend.BasisOne
import Setlec.Model.Extend.Iota
import Setlec.Model.Extend.Transport

/-!
# Modeled — split out of `Setlec.Model.Extend`

Extension by opaque modeled inductive-kind members:
`extend_modeled_one` for type formers and constructors,
`extend_modeled_rec` for recursors with checked iota rules, and the
`checkIndMember` inversion feeding them.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Extend a model by one opaque modeled inductive-kind member (an
inductive type former or constructor; the recursor carries rule
obligations and is handled separately): its value is its `_model`
counterpart's, and its type interprets identically through the block
renaming.  The type agreement is structural up to display-only binder
names (`Expr.eqUpToNames`) — the interpretation never reads them — so
the member's own annotation truthfulness is a hypothesis (`hannT`,
from the member's annotation run) rather than transported from the
model's. -/
theorem extend_modeled_one {env : Env} (m : EnvModel V env)
    (ci : ConstantInfo) (f : Name → Name) (mname : Name)
    {cvm : ConstantVal} {mval : Expr}
    (hfind' : env.find? ci.name = none)
    (hnres : reservedBasisNames.contains ci.name = false)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (hkind : (∃ cv caps, ci = .indInfo cv caps) ∨
      (∃ cv nP nF, ci = .ctorInfo cv nP nF) ∨
      (∃ cv mI rP, ci = .recInfo cv mI rP []))
    (hmodel : env.find? mname = some (.defnInfo cvm mval hmcvm))
    (hlps : cvm.levelParams = ci.toConstantVal.levelParams)
    (hren : Expr.eqUpToNames (ci.toConstantVal.type.renameConsts f)
      cvm.type = true)
    (hannT : ∀ ψ : Name → Nat,
      AnnotOk V m.val env ψ 0 (rho0 V) ci.toConstantVal.type)
    (hro : RenameOk m.val env f)
    -- the capability-law head obligations (`CapsOk.cons`'s shape,
    -- see `extend_basis_one`): the eta law is owed when the member
    -- completes a family — the block derivation discharges it from
    -- the artifact facts, with the group-local identification in
    -- scope — and the unit law for a freshly installed unit-like
    -- former
    (hcapsm : ∀ val' : ConstVal V,
      (∀ ψ : Name → Nat, val' ci.name ψ = m.val mname ψ) →
      (∀ (n : Name) (ψ : Name → Nat), n ≠ ci.name →
        val' n ψ = m.val n ψ) →
      (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
        (⟨ci :: env.consts⟩ : Env).find? T = some (.indInfo cvT caps) →
        caps.eta = true → reservedBasisNames.contains T = false →
        EtaFamilyStored ⟨ci :: env.consts⟩ T caps →
        (T = ci.name ∨ caps.etaCtor = ci.name ∨
          ∃ j, j < caps.etaFields ∧ projFnName T j = ci.name) →
        EtaLaw V ⟨ci :: env.consts⟩ val' T cvT caps) ∧
      (∀ cv caps, ci = .indInfo cv caps → caps.unitlike = true →
        reservedBasisNames.contains ci.name = false →
        UnitLaw V ⟨ci :: env.consts⟩ val' ci.name cv caps)) :
    ∃ m' : EnvModel V ⟨ci :: env.consts⟩,
      (∀ ψ, m'.val ci.name ψ = m.val mname ψ) ∧
      (∀ n ψ, n ≠ ci.name → m'.val n ψ = m.val n ψ) := by
  have hmm : ConstantInfo.defnInfo cvm mval hmcvm ∈ env.consts :=
    List.mem_of_find?_eq_some hmodel
  have hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ci.toConstantVal.type = some T ∧
        m.val (mname) ψ ∈ˢ T := by
    intro ψ
    obtain ⟨T, hT, hmem⟩ := m.mem_type _ hmm ψ
    have hname : cvm.name = mname := by
      have := List.find?_some hmodel
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using this
    refine ⟨T, ?_, by rw [← hname]; exact hmem⟩
    have hri : interpClosed V m.val env ψ (ci.toConstantVal.type.renameConsts f) =
        interpClosed V m.val env ψ ci.toConstantVal.type :=
      interp_renameConsts hro _ 0 (rho0 V)
    have hre : interpClosed V m.val env ψ
        (ci.toConstantVal.type.renameConsts f) =
        interpClosed V m.val env ψ cvm.type :=
      interp_erasedEq (Expr.ErasedEq.of_eqUpToNames hren) 0 (rho0 V)
    rw [← hri, hre]
    exact hT
  exact extend_basis_one m ci (fun ψ => m.val (mname) ψ)
    hfind' hwf htyres0
    (fun cv2 value2 h2 => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩ <;> simp)
    hkey
    (fun ψ₁ ψ₂ hψ => by
      refine m.val_params _ _ hmodel ψ₁ ψ₂ ?_
      intro p hp
      refine hψ p ?_
      rwa [show (ConstantInfo.defnInfo cvm mval hmcvm).toConstantVal = cvm from rfl,
        hlps] at hp)
    (fun ψ => hannT ψ)
    (fun cv caps heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv nP nF heq hn => absurd (hn ▸ hnres) (by decide))
    (fun cv caps heq hn => absurd (hn ▸ hnres) (by decide))
    (fun hn => absurd (hn ▸ hnres) (by decide))
    (fun _ hres2 => absurd (hres2 ▸ hnres) (by simp))
    (fun cv mI rP rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · exact ⟨fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide),
          fun hn => absurd hnres (by rw [hn]; decide)⟩)
    (fun val' _ _ cvR mI rP rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4
        subst h4
        intro r hr
        cases hr)
    (fun cvR mI rP rules heq => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩
      · exact nomatch heq
      · exact nomatch heq
      · injection heq with h1 h2 h3 h4
        subst h4
        intro r hr
        cases hr)
    (fun entry heq _ => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩ <;> exact nomatch heq)
    (fun cv2 value2 => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩ <;> simp)
    hcapsm
    (hreduce := fun _ _ _ cv₀ heq _ _ => by
      rcases hkind with ⟨cv', caps', rfl⟩ | ⟨cv', nP', nF', rfl⟩ |
        ⟨cv', mI', rP', rfl⟩ <;> exact ConstantInfo.noConfusion heq)

/-- The fold invariant of `checkIndDecl`: every installed block member
has its `_model` companion stored (as a definition with the same level
parameters), its checked type is the companion's under the block
renaming (up to display names), and it is interpreted by the
companion.  This *is* the group-local public↔`_model` identification:
it lives only inside the one block's install derivation and is
discarded at its end. -/
def BlockInstalled (blockNames : List Name) (env' : Env)
    (val : ConstVal V) : Prop :=
  ∀ n, blockNames.contains n = true → ∀ ci, env'.find? n = some ci →
    ∃ cvm mval hmcvm, env'.find? (n.str "_model") = some (.defnInfo cvm mval hmcvm) ∧
      cvm.levelParams = ci.toConstantVal.levelParams ∧
      Expr.eqUpToNames (ci.toConstantVal.type.renameConsts (fun n' =>
        if blockNames.contains n' then n'.str "_model" else n'))
        cvm.type = true ∧
      ∀ ψ : Name → Nat, val n ψ = val (n.str "_model") ψ

omit [SetTheory V] in
/-- Installing one member with its model's value preserves the fold
invariant. -/
theorem BlockInstalled.step {blockNames : List Name} {env' : Env}
    {val val₁ : ConstVal V} {ci₁ : ConstantInfo} {cvm : ConstantVal}
    {mval : Expr} {hmcvm : ReducibilityHint}
    (hI : BlockInstalled blockNames env' val)
    (hms : ci₁.name.isModelSuffix = false)
    (hfm : env'.find? (ci₁.name.str "_model") = some (.defnInfo cvm mval hmcvm))
    (hlps : cvm.levelParams = ci₁.toConstantVal.levelParams)
    (hren : Expr.eqUpToNames (ci₁.toConstantVal.type.renameConsts
      (fun n' => if blockNames.contains n' then n'.str "_model" else n'))
      cvm.type = true)
    (hval₁ : ∀ ψ, val₁ ci₁.name ψ = val (ci₁.name.str "_model") ψ)
    (hpres₁ : ∀ n ψ, n ≠ ci₁.name → val₁ n ψ = val n ψ) :
    BlockInstalled blockNames ⟨ci₁ :: env'.consts⟩ val₁ := by
  intro n hbn ci₂ hf₂
  rw [Env.find?_cons] at hf₂
  split at hf₂
  · next hh =>
    obtain rfl := Option.some.inj hf₂
    obtain rfl : ci₁.name = n := hh
    refine ⟨cvm, mval, hmcvm, ?_, hlps, hren, ?_⟩
    · rw [Env.find?_cons,
        if_neg (fun h => Name.str_ne ci₁.name "_model" h.symm)]
      exact hfm
    · intro ψ
      rw [hval₁ ψ, hpres₁ _ ψ (Name.str_ne ci₁.name "_model")]
  · next hh =>
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hren₂, hv₂⟩ := hI n hbn ci₂ hf₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, hren₂, ?_⟩
    · rw [Env.find?_cons, if_neg (show ¬ci₁.name = n.str "_model" from
        fun h => Name.str_model_ne hms h.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres₁ _ ψ (fun h => hh h.symm),
        hpres₁ _ ψ (fun h => Name.str_model_ne hms h),
        hv₂ ψ]

omit [SetTheory V] in
/-- Prepending a fresh non-member constant preserves the fold
invariant (the projection-family phase's installs). -/
theorem BlockInstalled.fresh_cons {blockNames : List Name} {env' : Env}
    {val val₁ : ConstVal V} {c₀ : ConstantInfo}
    (hI : BlockInstalled blockNames env' val)
    (hnotb : blockNames.contains c₀.name = false)
    (hfresh : env'.find? c₀.name = none)
    (hpres : ∀ n ψ, n ≠ c₀.name → val₁ n ψ = val n ψ) :
    BlockInstalled blockNames ⟨c₀ :: env'.consts⟩ val₁ := by
  intro n hbn ci₂ hf₂
  rw [Env.find?_cons] at hf₂
  split at hf₂
  · next hh =>
    exfalso
    rw [← hh] at hbn
    rw [hbn] at hnotb
    exact nomatch hnotb
  · next hh =>
    obtain ⟨cvm₂, mval₂, hm₂, hfm₂, hlps₂, hren₂, hv₂⟩ := hI n hbn ci₂ hf₂
    have hnne : n ≠ c₀.name := fun h => hh h.symm
    have hmne : n.str "_model" ≠ c₀.name := by
      intro h
      rw [← h] at hfresh
      rw [hfresh] at hfm₂
      exact nomatch hfm₂
    refine ⟨cvm₂, mval₂, hm₂, ?_, hlps₂, hren₂, ?_⟩
    · rw [Env.find?_cons, if_neg (fun h => hmne h.symm)]
      exact hfm₂
    · intro ψ
      rw [hpres _ ψ hnne, hpres _ ψ hmne, hv₂ ψ]


end Setlec
