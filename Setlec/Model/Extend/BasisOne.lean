import Setlec.Model.Extend.Transport

/-!
# BasisOne — split out of `Setlec.Model.Extend`

`extend_basis_one`: extend a model by one pinned basis constant
with a hand-supplied value.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Extend a model by one pinned basis constant with a hand-supplied
value.  The membership and annotation facts are stated over the *old*
valuation (basis types only mention previously installed constants);
the conclusion exposes the new valuation's equations so block
installation can chain. -/
theorem extend_basis_one {env : Env} (m : EnvModel V env)
    (ci : ConstantInfo) (v₀ : (Name → Nat) → V)
    (hfind' : env.find? ci.name = none)
    (hwf : ConstWF ⟨ci :: env.consts⟩ ci)
    (htyres0 : ci.toConstantVal.type.constsResolve env = true)
    (hnotdefn : ∀ cv2 value2 h2, ci ≠ .defnInfo cv2 value2 h2)
    (hkey : ∀ ψ : Name → Nat, ∃ T,
      interpClosed V m.val env ψ ci.toConstantVal.type = some T ∧ v₀ ψ ∈ˢ T)
    (hparams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → v₀ ψ₁ = v₀ ψ₂)
    (hAty : ∀ ψ : Name → Nat, AnnotOk V m.val env ψ 0 (rho0 V) ci.toConstantVal.type)
    (hnewty : ∀ cv caps, ci = .indInfo cv caps → ci.name = psigmaName →
      cv.levelParams = [uN, vN] ∧
      ∀ ψ : Name → Nat, PairTyFacts V (v₀ ψ) (ψ uN) (ψ vN))
    (hnewmk : ∀ cv nP nF, ci = .ctorInfo cv nP nF → ci.name = psigmaMkName →
      nP = 2 ∧ nF = 2 ∧ cv.levelParams = [uN, vN] ∧
      ∀ ψ : Name → Nat, PairMkFacts V (v₀ ψ) (ψ uN) (ψ vN))
    (hnewunit : ∀ cv caps, ci = .indInfo cv caps → ci.name = punitName →
      ∀ (ψ : Name → Nat) (x : V), x ∈ˢ v₀ ψ → x = pt)
    (hnewempty : ci.name = emptyName →
      ∀ (ψ : Name → Nat) (x : V), x ∈ˢ v₀ ψ → False)
    (hpin : ci.isBasis = true →
      reservedBasisNames.contains ci.name = true →
      ci = pinnedInfo ci.name ∧
      ∀ ψ : Name → Nat, v₀ ψ = pinnedVal V ci.name ψ)
    (hsib : SibFinds env ci)
    (hrecm : ∀ val' : ConstVal V,
      (∀ ψ : Name → Nat, val' ci.name ψ = v₀ ψ) →
      (∀ (n : Name) (ψ : Name → Nat), n ≠ ci.name → val' n ψ = m.val n ψ) →
      RecMemberOk (V := V) ⟨ci :: env.consts⟩ val' ci)
    (hctors : ∀ cvR mI rP rules,
      ci = .recInfo cvR mI rP rules →
      ∀ r ∈ rules, ∃ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF))
    (hprojOk : ∀ entry, ci = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA)
    (hnotthm : ∀ cv2 value2, ci ≠ .thmInfo cv2 value2 := by
      intro cv2 value2 h
      exact ConstantInfo.noConfusion h)
    -- the capability-law head obligations: for a pinned basis
    -- declaration everything is refuted by computation on its name —
    -- a reserved former is exempt from the clauses, a reserved name is
    -- never a (non-reserved) capability constructor, and a pinned name
    -- is never projection-function-shaped
    (hcaps : ∀ val' : ConstVal V,
      (∀ ψ : Name → Nat, val' ci.name ψ = v₀ ψ) →
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
        UnitLaw V ⟨ci :: env.consts⟩ val' ci.name cv caps) := by
      intro val' hv he
      refine ⟨?_, ?_⟩
      · intro T cvT caps hfT hcape hres hfam hpart
        rcases hpart with rfl | hC | ⟨j, hj, hP⟩
        · exact absurd hres (by decide)
        · obtain ⟨hCres, -, -⟩ := hfam
          rw [hC] at hCres
          exact absurd hCres (by decide)
        · exact absurd hP (Name.num_ne_str _ _ _ _)
      · intro cv caps heq hcapu hres
        exact absurd hres (by decide))
    -- the compiler-trust reduce-opaque obligation: at every basis and
    -- standard-axiom install the head is refuted by kind or name
    (hreduce : ∀ val' : ConstVal V,
      (∀ ψ : Name → Nat, val' ci.name ψ = v₀ ψ) →
      (∀ n, n ≠ ci.name → ∀ ψ' : Name → Nat, val' n ψ' = m.val n ψ') →
      ∀ cv₀, ci = .axiomInfo cv₀ → ci.name ∈ reduceOpNames →
      ConstantVal.matchesPin cv₀ (reduceOpCvA ci.name) = true →
      ((⟨ci :: env.consts⟩ : Env).find? (reduceElemName ci.name)).isSome
        = true ∧
      ∀ (ψ : Name → Nat) (x : V),
        x ∈ˢ val' (reduceElemName ci.name) ψ →
        SetTheory.app (val' ci.name ψ) x = x := by
      intro val' _ _ cv₀ heq hmem _
      first
      | exact ConstantInfo.noConfusion heq
      | exact absurd hmem (by decide)) :
    ∃ m' : EnvModel V ⟨ci :: env.consts⟩,
      (∀ ψ, m'.val ci.name ψ = v₀ ψ) ∧
      (∀ n ψ, n ≠ ci.name → m'.val n ψ = m.val n ψ) := by
  refine extend_fresh m ci v₀ hfind' hwf htyres0 ?_ ?_ hkey hparams hAty
    hnewty hnewmk hnewunit hnewempty hpin hsib hrecm hctors
    hprojOk hcaps ?_ ?_ hreduce
  · intro cv2 value2 h2 heq
    exact absurd heq (hnotdefn cv2 value2 h2)
  · intro cv2 value2 heq
    exact absurd heq (hnotthm cv2 value2)
  · intro val' _ _ cv₀ v₀' h₀' heq _
    exact absurd heq (hnotdefn cv₀ v₀' h₀')
  · intro val' _ _ cv₀ v₀' h₀' heq _
    exact absurd heq (hnotdefn cv₀ v₀' h₀')
end Setlec
