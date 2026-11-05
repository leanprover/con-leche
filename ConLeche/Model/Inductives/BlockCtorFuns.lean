module

public import ConLeche.Model.Inductives.BlockData
public section

/-!
# The constructors' data functions at a block member

Every constructor of ONE member, picked as a function of its position,
from its stage run (`blockCtorData_of`).  No field is classified.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps
 )

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-- A block constructor's data, bundled for the choice. -/
structure BlockCtorPick where
  idxArgs : List Expr
  ds : (Name → Nat) → List Term
  Es : (Name → Nat) → List Term
  srcs : List (Option Nat)
  fvsP : List Expr
  xFvs : List Expr
  xrest : Expr

/-- **The constructors' data functions at one member of a block**:
every constructor's data, from its stage run. -/
theorem blockCtorFuns_of (mp : EnvModelM V env)
    {F : Nat} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvS cvTa : ConstantVal}
    {env₁ : Env} {caps : IndCaps}
    {ctorList : List (ConstantVal × Nat)}
    (hfT : env.find? T = some (.indInfo cvS caps))
    (hlpsT : cvS.levelParams = lps)
    (hrunOf : ∀ (j : Nat) (ctor : ConstantVal × Nat), ctorList[j]? = some ctor →
      ∃ (c : ConstantVal × Nat) (sorts : List Level),
        ConLeche.checkSumCtor (ConLeche.fueledOps .verified F) env₁ env T lps nP nIdx
          resSort isProp large c.1 ctor.2 cvTa = .ok (ctor.1, sorts)) :
    ∃ (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List Term)
      (esF : Nat → (Name → Nat) → List Term) (srcsF : Nat → List (Option Nat))
      (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr),
      ∀ (j : Nat) (ctor : ConstantVal × Nat), ctorList[j]? = some ctor →
        BlockCtorDataI mp.base2 T lps ctor.1 nP ctor.2 nIdx resSort isProp large
          (idxF j) (dsF j) (esF j) (srcsF j) (fvsPF j) (xFvsF j) (xrestF j) := by
  have hex : ∀ j : Nat, ∃ q : BlockCtorPick, ∀ ctor : ConstantVal × Nat, ctorList[j]? = some ctor →
      BlockCtorDataI mp.base2 T lps ctor.1 nP ctor.2 nIdx resSort isProp large
        q.idxArgs q.ds q.Es q.srcs q.fvsP q.xFvs q.xrest := by
    intro j
    cases hj : ctorList[j]? with
    | none => exact ⟨⟨[], fun _ => [], fun _ => [], [], [], [], .bvar 0⟩, fun _ h => nomatch h⟩
    | some ctor =>
      obtain ⟨c, sorts, hCtor⟩ := hrunOf j ctor hj
      obtain ⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest, hD⟩ :=
        blockCtorData_of mp hCtor hfT hlpsT
      refine ⟨⟨idxArgs, ds, Es, srcs, fvsP, xFvs, xrest⟩, fun ctor' h => ?_⟩
      obtain rfl := Option.some.inj h
      exact hD
  let q : Nat → BlockCtorPick := fun j => Classical.choose (hex j)
  exact ⟨fun j => (q j).idxArgs, fun j => (q j).ds, fun j => (q j).Es, fun j => (q j).srcs,
    fun j => (q j).fvsP, fun j => (q j).xFvs, fun j => (q j).xrest,
    fun j => Classical.choose_spec (hex j)⟩

end ConLeche.Model
