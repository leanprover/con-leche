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
    (hmodv : reservedBasisNames.contains ci.name = false →
      ((∃ cv caps, ci = .indInfo cv caps) ∨
       (∃ cv cnP cnF, ci = .ctorInfo cv cnP cnF)) →
      (env.find? (ci.name.str "_model")).isSome = true ∧
      ∀ ψ : Name → Nat, v₀ ψ = m.val (ci.name.str "_model") ψ)
    (hproj : ∀ (T : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat)
      (rules : List RecRule), ci.name = projFnName T j →
      ci = .recInfo cv mI rP rules →
      (env.find? (projModelName T j)).isSome = true ∧
      ∀ ψ : Name → Nat, v₀ ψ = m.val (projModelName T j) ψ)
    (hprojOk : ∀ entry, ci = .projInfo entry → entry.native = true →
      (entry = pairFstEntry ∨ entry = pairSndEntry) ∧
      env.find? psigmaName = some psigmaA ∧
      env.find? psigmaMkName = some psigmaMkA)
    (hetaL : ∀ cv caps, ci = .indInfo cv caps → caps.eta = true →
      reservedBasisNames.contains ci.name = false →
      (env.find? (caps.etaCtor.str "_model")).isSome = true ∧
      (∀ j, j < caps.etaFields →
        (env.find? (projModelName ci.name j)).isSome = true) ∧
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.etaParams →
        x ∈ˢ SpineFold V (v₀ (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = SpineFold V (m.val (caps.etaCtor.str "_model")
            (Level.substFn φ'' cv.levelParams us))
          (ps ++ (List.range caps.etaFields).map fun j =>
            SpineFold V (m.val (projModelName ci.name j)
              (Level.substFn φ'' cv.levelParams us)) (ps ++ [x])))
    (hunitL : ∀ cv caps, ci = .indInfo cv caps → caps.unitlike = true →
      reservedBasisNames.contains ci.name = false →
      ∀ (φ'' : Name → Nat) (us : List Level) (ps : List V) (x y : V)
        (d₁ : Nat) (ρ₁ : Nat → V) (d₂ : Nat) (ρ₂ : Nat → V)
        (rest : Expr),
        ps.length = caps.unitParams →
        x ∈ˢ SpineFold V (v₀ (Level.substFn φ'' cv.levelParams us)) ps →
        y ∈ˢ SpineFold V (v₀ (Level.substFn φ'' cv.levelParams us)) ps →
        TeleFit V m.val env φ'' d₁ ρ₁
          (cv.type.instantiateLevelParams cv.levelParams us) ps d₂ ρ₂
          rest →
        x = y) :
    ∃ m' : EnvModel V ⟨ci :: env.consts⟩,
      (∀ ψ, m'.val ci.name ψ = v₀ ψ) ∧
      (∀ n ψ, n ≠ ci.name → m'.val n ψ = m.val n ψ) := by
  refine extend_fresh m ci v₀ hfind' hwf htyres0 ?_ hkey hparams hAty
    hnewty hnewmk hnewunit hnewempty hpin hsib hrecm hctors hmodv hproj
    hprojOk hetaL hunitL ?_ ?_
  · intro cv2 value2 h2 heq
    exact absurd heq (hnotdefn cv2 value2 h2)
  · intro val' _ _ cv₀ v₀' h₀' heq _
    exact absurd heq (hnotdefn cv₀ v₀' h₀')
  · intro val' _ _ cv₀ v₀' h₀' heq _
    exact absurd heq (hnotdefn cv₀ v₀' h₀')
end Setlec
