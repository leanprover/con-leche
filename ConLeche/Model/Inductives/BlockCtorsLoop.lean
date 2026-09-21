module

public import ConLeche.Model.Inductives.FixCtorsLoop
public section

/-!
# The constructors' loop at a block member (task #315 M3)

`ctorsLoopEta` (`FixCtorsLoop.lean`) at the BLOCK's η invariant
(`ConLeche.BlockEtaInv`, `ConLeche/Verify/EnvGuards.lean`): every
stored family outside the block is closed, and every stored member's η
constructor is none of the names the current member is consing.  The
loop itself is member-local — it is already abstract in the former's
leaf (`leafT`), in the fibre fold (`hfold`) and in the carried
invariant (`Inv`) — so the block's member is the one-member loop at
this invariant and nothing else changes.

What is still the caller's at a block member, and is where the `k`
members' data meet: `leafT := fun ψ => blockTyAV … m` with `hfold`
its fibre law at member `m`'s own index readings
(`blockLeafApp`/`chainRealBI_of` and `blockFam_app_eq_sum`, identified
with the dummy former's readings by `blockCtorDataI_ident`), and `Inv`
recording what the OTHER members' formers still are.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The constructors' conses at a block member.** -/
theorem blockCtorsLoop (hμ : μ.verifiedChecks = true)
    {F : Nat} {p : InductiveShape} {env₀ envI : Env} {cvTa : ConstantVal}
    {ctors ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    {names ctorNames : List Name}
    (hmemC : ∀ cA ∈ ctorsA, cA.1.name ∈ ctorNames)
    (hCtors : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) env₀ envI p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa ctors = .ok (ctorsA, sortss))
    (hnd : (ctorsA.map (·.1.name)).Nodup)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hlpsA : ∀ cA ∈ ctorsA, cA.1.levelParams = p.cvT.levelParams)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
      fssOf p.nP (ctorDataList dsF esF ψ₁ ctorsA 0) = fssOf p.nP (ctorDataList dsF esF ψ₂ ctorsA 0))
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0),
      FieldsBelow p.nP Fs)
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) ∧
      SumFieldsValid ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)))
    (hIdx : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
        SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF j ψ) bs))
    (Inv : ∀ {env' : Env}, EnvModel V env' → Prop)
    (hInv : ∀ {env' : Env} (m' : EnvModel V env') (cA : ConstantVal × Nat)
      (A : (Name → Nat) → AnnotTerm)
      (mC : EnvModel V ⟨.ctorInfo cA.1 p.nP cA.2 :: env'.consts⟩),
      cA ∈ ctorsA → env'.find? cA.1.name = none →
      mC.acval = acvalWith m'.acval cA.1.name A → Inv m' → Inv mC)
    -- the block's capability record and its laws at every carrier the
    -- invariant reaches (task #210 Part A)
    (caps : IndCaps)
    (leafT : (Name → Nat) → AnnotTerm)
    (hTlawsOf : ∀ {env' : Env} (m' : EnvModel V env') (k : Nat) (cA : ConstantVal × Nat),
      ctorsA[k]? = some cA → Inv m' →
      FormerData m' cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, m'.acval p.cvT.name ψ = leafT ψ) →
      (∀ ψ, m'.acval cA.1.name ψ
        = sumMkAV (p.resSort.eval ψ) k (dsF k ψ) (((dsF k ψ).drop p.nP).map (·.2.2))
            (uChains (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)))) →
      CapsLawsAt m' p.cvT.name cvTa caps)
    (hfold : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
        interp V (consList bs ρ)
            (AnnotTerm.mkAppN (leafT ψ) (paramBvars p.nP cA.2 ++ esF j ψ))
          = sumSet (p.resSort.eval ψ) (sumFibre (p.resSort.eval ψ)
              (consList (idxValsAt ρ (esF j ψ) bs) ρ)
              (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
                (essOf (ctorDataList dsF esF ψ ctorsA 0))))) :
    ∀ (rest : List (ConstantVal × Nat)) (k : Nat) (env : Env) (mp : EnvModelM V μ env),
      (∀ i, rest[i]? = ctorsA[k + i]?) → k + rest.length = ctorsA.length →
      ConLeche.BlockEtaInv env names ctorNames →
      env.find? p.cvT.name = some (.indInfo cvTa caps) →
      FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, mp.base2.acval p.cvT.name ψ = leafT ψ) →
      ConsedAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF ctorsA k →
      PendingAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF ctorsA k →
      Inv mp.base2 →
      ∃ mp' : EnvModelM V μ (ConLeche.consSumCtors p.nP rest env),
        ConLeche.BlockEtaInv (ConLeche.consSumCtors p.nP rest env) names ctorNames ∧
        (ConLeche.consSumCtors p.nP rest env).find? p.cvT.name
          = some (.indInfo cvTa caps) ∧
        FormerData mp'.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll ∧
        (∀ ψ, mp'.base2.acval p.cvT.name ψ = leafT ψ) ∧
        ConsedAt mp'.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
          idxF dsF esF srcsF ctorsA ctorsA.length ∧
        Inv mp'.base2 :=
  ctorsLoopEta hμ hCtors hnd hlpsT hlpsA hFssParams hFssBelow hiff hFssOkP hIdx Inv hInv
    caps leafT hTlawsOf (fun e => ConLeche.BlockEtaInv e names ctorNames)
    (fun _ _ _ hfresh hE => hE.cons hfresh)
    (fun _ cA hcA hfresh hE _ _ _ hf hne hres hcape _ =>
      hE.other (nP := p.nP) (nF := cA.2) hfresh (hmemC cA hcA) hf hne hres hcape)
    hfold

end ConLeche.Model
