module

public import ConLeche.Model.Inductives.NestedRecsStage
public import ConLeche.Model.Inductives.MutualRecData
import ConLeche.Model.Inductives.NestedRecTypes
import ConLeche.Model.Inductives.MutualRecsStage
import ConLeche.Verify.Inductives.NestedRecDoor
import ConLeche.Verify.Inductives.MutualInv
public section

/-!
# The scratch reading (task #315, M7-2)

The nested route installs its AUXILIARY (scratch) block with the
MUTUAL installer at the `auxRoute` grade.  This file runs the mutual
route's own stage facts at the tail's data: the scratch constructors'
model (`mutualCtorsStage`), the scratch block model at it
(`blockReps_of`), the scratch recursor types read to that block
model's Π-towers (`blockRecData_of`) and their readings
(`BlockModel.blockReadings_of`) — all at the ONE block model
`mutualBlockModel` of the auxiliary block, and with the read-back's
recursor at class `c` identified with the scratch run's `cvRas[c]`
(`auxStored_rec_eq` through `checkMutualRecTy_shape`).

The record `NestedScratchOut` is what the transfer (PLAN-M7 §1e) reads
of the scratch side; `NestedTailIn.scratch` produces it from a tail
input.  Everything here is assembly: no new mathematics.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock MutualFormer MutualCtor4 AuxStored ElimState NestedPin IndCaps
  fueledOps BinderMeta PropWhen RestoreTbl)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

section Record

variable (F : Nat) (env : Env) (b : MutualBlock) (fms : List MutualFormerA)
  (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
  (kinds : List (List (RecFieldKind × Nat)))
  (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
  (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
  (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
  (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
  (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
  (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
  (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
  (stored : List AuxStored)

/-- The scratch (auxiliary) block's constructors' environment. -/
local notation "ENVA" =>
  (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))

/-- The scratch block's block model — the MUTUAL one (the nested
route's own is `nestedBlockModel`). -/
local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

/-! ## The record -/

/-- **The scratch side of the recursors' stage**: at the scratch
constructors' model `mpA` the auxiliary block's block model `DA`
holds (`record`, `reps`, `typed`, `memberStored`), the scratch run's
recursor types are `cvRas` (`rectys`, `cvLen`), the read-back's
recursor at class `c` IS `cvRas[c]` (`cvEq`), those types read to
`DA`'s Π-towers graded at one sort (`recData`) and their readings are
`DA`'s (`readings`); `etaA`, `cons`, `leafM` and `agree` are the
constructors' stage's own output, kept for the transfer. -/
structure NestedScratchOut (mpA : EnvModelM V μ ENVA) (cvRas : List ConstantVal) : Prop where
  /-- the constructors' environment stays η-closed -/
  etaA : ConLeche.EtaFamiliesClosed ENVA
  /-- every scratch constructor's data and leaf at `mpA` -/
  cons : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
    MutualCtorFactsAt mpA.base2 (ConLeche.consMutualFormers fms env) b.members3 b.lps b.nP
      (Level.isEquiv f₀.s Level.zero == some true) b.large
      (fun t => (fms.getD t default).cvTa.name) (fun t => (fms.getD t default).nIdx)
      (mutMemF b) (fun J => (fms.getD (mutMemF b J) default).s) idxF dsF esF srcsF
      (mutKsOf kinds) fvsPF xFvsF xrestF eissF tssF J cA ∧
    (∀ e ∈ idxF J, e.constsResolve ENVA = true) ∧
    ∀ ψ : Name → Nat, mpA.base2.acval cA.1.name ψ
      = sumMkAV (f₀.s.eval ψ) (J - b.ownOffset (mutMemF b J)) (dsF J ψ)
          (((dsF J ψ).drop b.nP).map (·.2.2))
          (uChains ((mutFss b.nP ctorsA.length dsF ψ).drop (b.ownOffset (mutMemF b J))))
  /-- the members' leaves are the formers' model's -/
  leafM : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    mpA.base2.acval f.cvTa.name = mp₁.base2.acval f.cvTa.name
  /-- off the constructors the model is the formers' -/
  agree : ∀ n : Name, (∀ cA ∈ ctorsA, n ≠ cA.1.name) → mpA.base2.acval n = mp₁.base2.acval n
  /-- `DA` is the scratch block's block model -/
  record : MutualBlockModelOf env b fms ctorsA DA
  /-- it holds at every member -/
  reps : IsBlockModels mpA.base2 DA
  /-- the members and constructors are typed -/
  typed : ∀ ψ : Name → Nat, FormersTyped mpA.base2 DA ψ ∧ CtorsTyped mpA.base2 DA ψ
  /-- the members are stored at `DA`'s readings -/
  memberStored : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    MemberStored mpA.base2 b.lps b.nP f (DA).resSort ((DA).ppsM t)
  /-- `cvRas` is the scratch run's recursor-type stage -/
  rectys : ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F) ENVA b
    (ConLeche.mutualGenData b fms ctorsA kinds).1 (ConLeche.mutualGenData b fms ctorsA kinds).2
    none b.k = .ok cvRas
  /-- one per class -/
  cvLen : cvRas.length = b.k
  /-- the read-back's recursor at class `c` IS the scratch run's `cvRas[c]` -/
  cvEq : ∀ (c : Nat) (a : AuxStored), stored[c]? = some a → cvRas[c]? = some a.cvRa
  /-- class `c`'s recursor type reads to `DA`'s Π-tower, graded -/
  recData : ∀ c, c < b.k →
    MutualRecData mpA.base2 (cvRas.getD c default) (DA).nP (DA).k (DA).nCtors ((DA).nIdxAt c) c
      b.elimLevel ((DA).blockRds mpA.base2 b.elimLevel c) ∧
    ∃ u : Level, ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (mkPisAV ((DA).blockRds mpA.base2 b.elimLevel c ψ) ((DA).blockConc c))
        ∈ˢ (univ (u.eval ψ) : V)
  /-- the readings are `DA`'s own -/
  readings : ∀ ψ : Name → Nat,
    BlockReadings mpA.base2 DA ψ b.elimLevel ((DA).recLs mpA.base2 ψ) (DA).recNIdxs ((DA).recPps ψ)
      ((DA).recIpss ψ) ((DA).recCds ψ) (DA).recMots (DA).recTgts

end Record

/-! ## The scratch reading at the run -/

section Run

variable {env : Env} {F : Nat} {mp : EnvModelM V μ env} {p : NestedParts} {envOut : Env}
  {st : ElimState} {b : MutualBlock} {envAux : Env} {stored : List AuxStored}
  {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
  {rulesM rulesN : List (List RecRule)} {fmsA ctorsA₀ : List ConstantVal}
  {fms : List MutualFormerA} {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
  {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn}
  {mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
    (ConLeche.consMutualFormers (fms.take p.k) env))}

local notation "ENVA" =>
  (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))

local notation "DA" => (mutualBlockModel (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xFvsF xrestF eissF tssF)

variable (I : NestedTailIn F mp p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN
  fmsA ctorsA₀ fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF
  tssF dsR xFvsR pinsS mp₂)
include I

/-- **THE SCRATCH READING** (PLAN-M7 §1d): at a tail input the scratch
block's own install stages give a model `mpA` of the scratch
constructors' environment at which the MUTUAL block model `DA` holds,
and the scratch run's recursor types `cvRas` — the read-back's
recursors — read to `DA`'s Π-towers with `DA`'s readings.  Pure
assembly: `mutualCtorsStage`, `blockReps_of`, `mutualBlockModelOf_ofMutual`,
`blockRecData_of` and `BlockModel.blockReadings_of` at the tail's data,
the runs identified with the tail's by determinism, and
`auxStored_rec_eq` through `checkMutualRecTy_shape` for `cvEq`. -/
theorem NestedTailIn.scratch :
    ∃ (mpA : EnvModelM V μ ENVA) (cvRas : List ConstantVal),
      NestedScratchOut F env b fms f₀ ctorsA kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF
        xrestF eissF tssF stored mpA cvRas := by
  -- the scratch install's chain, at the tail's own runs
  obtain ⟨h0, h1, h2, h3, env₁, fms', f₀', tq₀, ctorsA', sortss', kinds', formers4, ctors4,
    cvRas, rulesOf, hformers', hf₀', -, -, -, hctors', hkinds', -, hgd', hrectys', -, -, -⟩ :=
    ConLeche.checkMutualCore_inv I.haux
  obtain ⟨-, rfl⟩ := ConLeche.mutualFormers_inv hformers'
  have hfms : fms = fms' := congrArg Prod.snd (Except.ok.inj (I.out.formers.symm.trans hformers'))
  subst hfms
  have hf0 : f₀ = f₀' := Option.some.inj (I.out.facts.first.symm.trans hf₀')
  subst hf0
  have hcA : ctorsA = ctorsA' :=
    congrArg Prod.fst (Except.ok.inj (I.out.ctors.symm.trans hctors'))
  subst hcA
  have hkd : kinds = kinds' := Except.ok.inj (I.out.kindsRun.symm.trans hkinds')
  subst hkd
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hgd'
  -- the constructors' stage and the block model at it
  obtain ⟨mpA, hEA, hcons, hleafM, hag⟩ :=
    mutualCtorsStage I.out.facts I.hμ I.hE I.out.nodup I.out.grouped
  obtain ⟨hreps, htyped, hstored⟩ :=
    blockReps_of I.hμ I.out.nodup h2 I.out.grouped I.out.facts mpA hcons hleafM hag
  have hd : MutualBlockModelOf env b fms ctorsA (DA) :=
    mutualBlockModelOf_ofMutual env b fms ctorsA I.out.facts.first _ ppsF W _ _ _ _ _ _ _ _ _ _
      _ _ _ _ _ _ _ _ _ _
  -- the block has a member
  have h0k : 0 < b.k := by have := I.kpos; have := I.out.bk; omega
  -- the recursor types, read
  obtain ⟨hlenR, hRD⟩ := blockRecData_of I.hμ mpA hd hreps I.out.facts.lenFms h0k h2
    I.out.grouped I.out.facts.lenA I.out.facts.lenK (ctorsA_names_of I.out.ctors h1).2 hgd'
    (fun _ _ _ _ => ⟨rfl, fun _ => rfl⟩) hstored hrectys'
  have hdk : (DA).k = b.k := hd.k
  refine ⟨mpA, cvRas, ?_⟩
  refine { etaA := hEA, cons := hcons, leafM := hleafM, agree := hag, record := hd
           reps := hreps, typed := htyped, memberStored := hstored, rectys := hrectys'
           cvLen := by rw [hlenR, hdk]
           cvEq := ?_
           recData := fun c hc => hRD c (by rw [hdk]; exact hc)
           readings := fun ψ =>
             (DA).blockReadings_of mpA.base2 ψ b.elimLevel fun mm hmm => (hRD mm hmm).1.below ψ }
  -- **`cvEq`**: the read-back's recursor at class `c` is the scratch run's
  intro c a ha
  have hc : c < b.k := by rw [← I.storedLen]; exact (List.getElem?_eq_some_iff.mp ha).1
  obtain ⟨cvRa, hget, hrun⟩ := (ConLeche.checkMutualRecTys_inv hrectys').2 c hc
  obtain ⟨recTy, -, -, hrt, -, -, -, -, -, -, -, hcv⟩ := ConLeche.checkMutualRecTy_shape hrun
  obtain ⟨hnmA, hlpsA, fms', f₀', ctorsA', sortss', kinds', hformers'', hf₀'', hctors'', hkinds'',
    hrtA, -, -, -, -⟩ := ConLeche.auxStored_rec_eq I.haux I.hstored ha
  have hfms : fms = fms' :=
    congrArg Prod.snd (Except.ok.inj (I.out.formers.symm.trans hformers''))
  subst hfms
  have hf0 : f₀ = f₀' := Option.some.inj (I.out.facts.first.symm.trans hf₀'')
  subst hf0
  have hcA : ctorsA = ctorsA' :=
    congrArg Prod.fst (Except.ok.inj (I.out.ctors.symm.trans hctors''))
  subst hcA
  have hkd : kinds = kinds' := Except.ok.inj (I.out.kindsRun.symm.trans hkinds'')
  subst hkd
  have hty : recTy = a.cvRa.type := Option.some.inj (hrt.symm.trans hrtA)
  have heta : a.cvRa = ⟨a.cvRa.name, a.cvRa.levelParams, a.cvRa.type⟩ := rfl
  rw [hget, hcv, heta, hnmA, hlpsA, hty]

end Run

end ConLeche.Model
