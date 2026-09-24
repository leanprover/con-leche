module

public import ConLeche.Model.Inductives.BlockData
public section

/-!
# The constructors' data functions at a block member (task #315 M3)

`FixAssemblyKit.lean`'s `fixCtorFuns_of` at `k` members: every
constructor of ONE member, picked as a function of its position, from
its stage run (`blockCtorData_of`).  No field is classified.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- A block constructor's data, bundled for the choice. -/
structure BlockCtorPick where
  idxArgs : List Expr
  ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)
  Es : (Name → Nat) → List AnnotTerm
  srcs : List (Option Nat)
  fvsP : List Expr
  xFvs : List Expr
  xrest : Expr

/-- **The constructors' data functions at one member of a block**:
every constructor's data, from its stage run. -/
theorem blockCtorFuns_of (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env)
    {F : Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal}
    {env₁ : Env} {caps : IndCaps} {bs : List (Expr × BinderMeta)}
    {ctorsA : List (ConstantVal × Nat)} {sT : Level}
    (hfT : env.find? T = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = lps)
    (hsT : ∀ ψ : Name → Nat, sT.eval ψ = resSort.eval ψ)
    (hstripT : cvTa.type.stripPis (nP + nIdx) = some (bs, .sort sT))
    (hrunOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ (c : ConstantVal × Nat) (sorts : List Level),
        ConLeche.checkSumCtor (ConLeche.fueledOps μ F) env₁ env T lps nP nIdx
          resSort isProp large c.1 cA.2 cvTa = .ok (cA.1, sorts)) :
    ∃ (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
      (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr),
      ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
        BlockCtorDataI mp.base2 T lps cA.1 nP cA.2 nIdx resSort isProp large
          (idxF j) (dsF j) (esF j) (srcsF j) (fvsPF j) (xFvsF j) (xrestF j) := by
  have hex : ∀ j : Nat, ∃ q : BlockCtorPick, ∀ cA : ConstantVal × Nat, ctorsA[j]? = some cA →
      BlockCtorDataI mp.base2 T lps cA.1 nP cA.2 nIdx resSort isProp large
        q.idxArgs q.ds q.Es q.srcs q.fvsP q.xFvs q.xrest := by
    intro j
    cases hj : ctorsA[j]? with
    | none => exact ⟨⟨[], fun _ => [], fun _ => [], [], [], [], .bvar 0⟩, fun _ h => nomatch h⟩
    | some cA =>
      obtain ⟨c, sorts, hCtor⟩ := hrunOf j cA hj
      obtain ⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, hD⟩ :=
        blockCtorData_of hμ mp hCtor hfT hlpsT hsT hstripT
      refine ⟨⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest⟩, fun cA' h => ?_⟩
      obtain rfl := Option.some.inj h
      exact hD
  let q : Nat → BlockCtorPick := fun j => Classical.choose (hex j)
  exact ⟨fun j => (q j).idxArgs, fun j => (q j).ds, fun j => (q j).Es, fun j => (q j).srcs,
    fun j => (q j).fvsP, fun j => (q j).xFvs, fun j => (q j).xrest,
    fun j => Classical.choose_spec (hex j)⟩

end ConLeche.Model
