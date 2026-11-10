module

import ConLeche.Verify.Inductives.DirectInv
public import ConLeche.Model.Inductives.FixKit
public section

/-!
# The constructors' loop at a block member

`ctorsLoopAt` (`FixKit.lean`) at a block member.  The loop is
member-local — it is abstract in the former's leaf (`leafT`), in the
fibre fold (`hfold`) and in the carried invariant (`Inv`) — so the
block's member is the one-member loop at the member's one-family shape
(`memberShapeI`) and nothing else changes.

What stays the caller's at a block member, and is where the `k`
members' data meet: `leafT` (the member's stored leaf) with `hfold` its
fibre law at member `m`'s own index readings (the override law,
`blockHoleFold`), and `Inv` recording what the OTHER members' formers
still are.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-- The one-family shape a member's scalars present to the sum route's
loop: the loop reads a shape's name, level parameters, parameter and
index counts, sort and the two flags, and nothing else (D-M31). -/
def memberShapeI (T : Name) (lps : List Name) (nP nIdx : Nat) (resSort : Level)
    (isProp large : Bool) : InductiveShape where
  cvT := { name := T, levelParams := lps, type := .sort .zero }
  ctors := []
  nP := nP
  nIdx := nIdx
  cvR := { name := .anonymous, levelParams := [], type := .sort .zero }
  elim := .anonymous
  resSort := resSort
  rhss := []
  large := large
  isProp := isProp

/-- **The constructors' conses at a block member.** -/
theorem blockCtorsLoop
    {F : Nat} {T : Name} {lps : List Name} {nP nIdx : Nat} {resSort : Level}
    {isProp large : Bool} {env₀ envI : Env} {cvTa : ConstantVal}
    {ctors ctorList : List (ConstantVal × Nat)} {sortss : List (List Level)} {cvS : ConstantVal}
    (hCtors : ConLeche.SumCtorsRun .verified F env₀ envI T
      lps nP nIdx resSort isProp large cvTa ctors ctorList sortss)
    (hnd : (ctorList.map (·.1.name)).Nodup)
    (hlpsT : cvTa.levelParams = lps)
    (hlpsA : ∀ ctor ∈ ctorList, ctor.1.levelParams = lps)
    -- the reserved names' check (`basisNamesOk`)
    (hresA : ∀ ctor ∈ ctorList, ConLeche.reservedBasisNames.contains ctor.1.name = false)
    {ppsAll : (Name → Nat) → List Term}
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List Term}
    {esF : Nat → (Name → Nat) → List Term} {srcsF : Nat → List (Option Nat)}
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      fssOf nP (ctorDataList dsF esF ψ₁ ctorList 0) = fssOf nP (ctorDataList dsF esF ψ₂ ctorList 0))
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ fssOf nP (ctorDataList dsF esF ψ ctorList 0),
      DomsBelow nP Fs)
    (hiff : ∀ j ctor, ctorList[j]? = some ctor → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP)).reverse ρ ↔
        Sat V (((dsF j ψ).take nP)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (fssOf nP (ctorDataList dsF esF ψ ctorList 0)))
    (hIdx : ∀ j ctor, ctorList[j]? = some ctor → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF j ψ).take nP)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop nP)) bs →
        SpineFit ρ (((ppsAll ψ).drop nP)) (idxValsAt ρ (esF j ψ) bs))
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m' : EnvModel V env') (ctor : ConstantVal × Nat)
      (A : (Name → Nat) → Term)
      (mC : EnvModel V ⟨.ctorInfo ctor.1 nP ctor.2 :: env'.consts, env'.tables⟩),
      ctor ∈ ctorList → env'.find? ctor.1.name = none →
      mC.acval = acvalWith m'.acval ctor.1.name A → Inv m' → Inv mC)
    -- the block's capability record and the former's leaf
    (caps : IndCaps)
    (leafT : (Name → Nat) → Term)
    (hfold : ∀ j ctor, ctorList[j]? = some ctor → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take nP)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop nP)) bs →
        interp V (consList bs ρ)
            (Term.mkAppN (leafT ψ) (paramBvars nP ctor.2 ++ esF j ψ))
          = sumSet (resSort.eval ψ) (sumFibre (resSort.eval ψ)
              (consList (idxValsAt ρ (esF j ψ) bs) ρ)
              (rChains nIdx nIdx (fssOf nP (ctorDataList dsF esF ψ ctorList 0))
                (essOf (ctorDataList dsF esF ψ ctorList 0))))) :
    ∀ (rest : List (ConstantVal × Nat)) (k : Nat) (env : Env) (mp : EnvModelM V env),
      (∀ i, rest[i]? = ctorList[k + i]?) → k + rest.length = ctorList.length →
      env.find? T = some (.indInfo cvS caps) →
      cvTa.type.constsResolve env = true →
      FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll →
      (∀ ψ, mp.base2.acval T ψ = leafT ψ) →
      ConsedAt mp.base2 T lps nP nIdx resSort isProp large
        idxF dsF esF srcsF ctorList k →
      PendingAt mp.base2 T lps nP nIdx resSort isProp large
        idxF dsF esF srcsF ctorList k →
      Inv mp.base2 →
      ∃ mp' : EnvModelM V (ConLeche.consSumCtors nP rest env),
        (ConLeche.consSumCtors nP rest env).find? T
          = some (.indInfo cvS caps) ∧
        FormerData mp'.base2 cvTa (nP + nIdx) resSort ppsAll ∧
        (∀ ψ, mp'.base2.acval T ψ = leafT ψ) ∧
        ConsedAt mp'.base2 T lps nP nIdx resSort isProp large
          idxF dsF esF srcsF ctorList ctorList.length ∧
        Inv mp'.base2 :=
  ctorsLoopAt (p := memberShapeI T lps nP nIdx resSort isProp large)
    hCtors hnd hlpsT hlpsA hresA hFssParams hFssBelow hiff hFssOkP hIdx Inv hInv
    caps leafT hfold

end ConLeche.Model
