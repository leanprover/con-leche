module

public import ConLeche.Model.Inductives.BlockRepMutual
public import ConLeche.Model.Inductives.MutualStageCtor
public import ConLeche.Model.Inductives.MutualRecs
import ConLeche.Model.Inductives.MutualIdxUniv
public import ConLeche.Verify.Inductives.MutualGrouped
import ConLeche.Model.Inductives.MutualFormersKit
import ConLeche.Model.Inductives.MutualLeafBelow
import ConLeche.Model.Inductives.SumStageFormer
import ConLeche.Model.Inductives.StructFrames
import ConLeche.Model.Inductives.StructRows
import ConLeche.Model.Inductives.StructRecSpine
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Verify.Inductives.MutualInv
public section

/-!
# The mutual install's core, assembled (task #315, M4 session 3)

`MutualCoreModeled`'s proof, in stages: the formers' stage
(`mutualFormersStage`: stages 0–2 of the run, the chain-free first
pass, the constructors' readings, the block's chain facts, the real
conses through the derived former's API `stageTupleFormers`, the
readings identified at the real model), the constructors' stage
(`mutualCtorsStage`: #278's `stageMutualCtors` at the member leaves),
and the datum (`blockReps_of`: `BlockRepData.ofMutual` satisfies
`BlockRep` at every member of the constructors' environment, with the
members and constructors typed).  Each stage's outputs are packaged as
a `Prop`-structure over the data it chose (`MutualFormersFacts`), so
that no single theorem carries the whole run.

The block's index universe `W` is the join of the members' index
binders' own universes, read off the checked formers' Π-inference
rows (`formerLevels_of`, `MutualIdxUniv.lean`): the mutual kernel
runs no index sort row of its own (the fixpoint route's
`checkStructFieldSortsI` is not part of `checkMutualCore`), and the
former's own `checkConstantVal` infers each binder's sort.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind IndCaps RecRule
  MutualBlock MutualFormerA MutualCtor fueledOps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The block's readers -/

/-- Constructor `J`'s member (the block record's). -/
@[expose] def mutMemF (b : MutualBlock) (J : Nat) : Nat := (b.ctors.getD J default).member

/-- Constructor `J`'s field count (the checked constructors'). -/
@[expose] def mutNFOf (ctorsA : List (ConstantVal × Nat)) (J : Nat) : Nat :=
  (ctorsA.getD J default).2

/-- Constructor `J`'s classified kinds. -/
@[expose] def mutKsOf (kinds : List (List (RecFieldKind × Nat))) (J : Nat) :
    List (RecFieldKind × Nat) :=
  kinds.getD J []

/-- **Member `t`'s leaf** at the block's data: the derived `k`-ary
former at the block's lists in global constructor order. -/
@[expose] def mutMemberLeaf (b : MutualBlock) (fms : List MutualFormerA) (f₀ : MutualFormerA)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List (RecFieldKind × Nat)))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (t : Nat)
    (ψ : Name → Nat) : AnnotTerm :=
  tupleLfpAV (W ψ) (f₀.s.eval ψ) (ppsF t ψ) (fms.getD t default).nIdx b.k (blockIds b.nP ppsF ψ)
    (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
    (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (mutRss ctorsA.length (mutKsOf kinds))
    (mutTlss ctorsA.length tssF ψ) (mutEiss0 ctorsA.length eissF ψ)
    (mutFss0 b.nP ctorsA.length dsF (mutKsOf kinds) (mutNFOf ctorsA) ψ)
    (mutEss0 ctorsA.length esF ψ) t

/-! ## The formers' stage, packaged -/

/-- **The formers' stage's outputs** at the real model `mp₁` of the
formers' environment: the members' checks, their data and leaves,
the constructors' readings at `mp₁`, the cross-member frames, the
block's index universe and chain facts, and the derived former's
premises. -/
structure MutualFormersFacts (V : Type w) [SetTheory V] {μ : CheckMode} {env : Env} (F : Nat)
    (mp : EnvModelM V μ env) (b : MutualBlock) (fms : List MutualFormerA) (f₀ : MutualFormerA)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level))
    (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) : Prop where
  /-- the members' count is the block's -/
  lenFms : fms.length = b.k
  /-- the first member -/
  first : fms[0]? = some f₀
  /-- every member's sort evaluates like the first's -/
  sEq : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    ∀ ψ : Name → Nat, f.s.eval ψ = f₀.s.eval ψ
  /-- every member carries the block's level parameters -/
  lps : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → f.cvTa.levelParams = b.lps
  /-- every member is fresh before the block -/
  fresh : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → env.find? f.cvTa.name = none
  /-- every member's type is its telescope -/
  strip : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    ∃ bs : List (Expr × BinderMeta), f.cvTa.type.stripPis (b.nP + f.nIdx) = some (bs, .sort f.s)
  /-- the members' names are the block record's -/
  names : fms.map (·.cvTa.name) = b.memberNames
  /-- the member table reads the members -/
  memT : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    mutualNameOf b.members3 t = f.cvTa.name ∧ mutualNIdxOf b.members3 t = f.nIdx
  /-- the members' types resolve before the block -/
  cbF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → ConstsBound env f.cvTa.type
  /-- every member is stored at the formers' environment with `{}` -/
  find : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    (ConLeche.consMutualFormers fms env).find? f.cvTa.name = some (.indInfo f.cvTa {})
  /-- the members' data at the pre-block model -/
  FD₀ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    FormerData mp.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t)
  /-- the members' data at the formers' model -/
  FD : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    FormerData mp₁.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t)
  /-- the members' leaves -/
  leaf : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    mp₁.base2.acval f.cvTa.name = mutMemberLeaf b fms f₀ ctorsA kinds ppsF W dsF esF eissF tssF t
  /-- the model agrees with the pre-block model off the members -/
  off : ∀ n : Name, (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → n ≠ f.cvTa.name) →
    mp₁.base2.acval n = mp.base2.acval n
  /-- the constructors' count is the block's -/
  lenA : ctorsA.length = b.ctors.length
  /-- the kinds' count is the constructors' -/
  lenK : kinds.length = ctorsA.length
  /-- every constructor's member is a member -/
  motLt : ∀ J : Nat, J < ctorsA.length → mutMemF b J < fms.length
  /-- every constructor's check, at the formers' environment -/
  runC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
    cA.2 = (b.ctors.getD J default).nF ∧
    ∃ sorts : List Level, sortss[J]? = some sorts ∧
      ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) (ConLeche.consMutualFormers fms env)
        b.memberNames (fms.getD (mutMemF b J) default).cvTa.name b.lps b.nP
        (fms.getD (mutMemF b J) default).nIdx (fms.getD (mutMemF b J) default).s
        (Level.isEquiv f₀.s Level.zero == some true) b.large (b.ctors.getD J default).cv cA.2
        (fms.getD (mutMemF b J) default).cvTa = .ok (cA.1, sorts)
  /-- the kinds: as many as fields, re-checked opened, targets members -/
  ksJ : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
    (mutKsOf kinds J).length = cA.2 ∧
    ConLeche.mutualOpenedOk env b.members3 b.lps b.nP cA.1.type cA.2 (mutKsOf kinds J) = true ∧
    ∀ i, tgtAt (mutKsOf kinds J) i < fms.length
  /-- the constructors' data at the formers' model (the pre-block
  environment the opened form's residuals resolve in) -/
  CD : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
    MutualCtorDataI mp₁.base2 env b.members3 (fms.getD (mutMemF b J) default).cvTa.name b.lps
      cA.1 b.nP cA.2 (fms.getD (mutMemF b J) default).nIdx (fms.getD (mutMemF b J) default).s
      (Level.isEquiv f₀.s Level.zero == some true) b.large (idxF J) (dsF J) (esF J) (srcsF J)
      (mutKsOf kinds J) (fvsPF J) (xFvsF J) (xrestF J) (eissF J) (tssF J)
  /-- every constructor carries the block's level parameters -/
  lpsC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA → cA.1.levelParams = b.lps
  /-- the constructors' names are the block record's -/
  namesC : ctorsA.map (·.1.name) = b.ctors.map (·.cv.name)
  /-- every constructor is fresh at the formers' environment -/
  freshC : ∀ c ∈ ctorsA, (ConLeche.consMutualFormers fms env).find? c.1.name = none
  /-- every constructor's type resolves at the formers' environment -/
  resC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
    cA.1.type.constsResolve (ConLeche.consMutualFormers fms env) = true
  /-- **the cross-member identification**: every member's parameter
  frame is the first member's -/
  frame : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρ
  /-- **the tag**: at every member's parameter frame the members' index
  telescopes are graded at the block's index universe, and valid -/
  idxAll : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρ →
      TagOk (W ψ) ρ (tupleIdss b.k (blockIds b.nP ppsF ψ)) ∧
        ∀ Ids ∈ tupleIdss b.k (blockIds b.nP ppsF ψ), FieldsValid ρ Ids
  /-- the constructors' readings depend on the block's parameters only -/
  CDpar : ∀ J : Nat, J < ctorsA.length → ∀ ψ₁ ψ₂ : Name → Nat,
    (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) →
    dsF J ψ₁ = dsF J ψ₂ ∧ esF J ψ₁ = esF J ψ₂ ∧ eissF J ψ₁ = eissF J ψ₂ ∧ tssF J ψ₁ = tssF J ψ₂
  /-- the members' readings depend on the block's parameters only -/
  ppsPar : ∀ t : Nat, t < fms.length → ∀ ψ₁ ψ₂ : Name → Nat,
    (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) → ppsF t ψ₁ = ppsF t ψ₂
  /-- the derived former's block premise -/
  blockOk : TupleLfpBlockOk b.nP b.lps W b.k (blockIds b.nP ppsF)
    (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
    (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (mutRss ctorsA.length (mutKsOf kinds))
    (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
    (fun ψ => mutFss0 b.nP ctorsA.length dsF (mutKsOf kinds) (mutNFOf ctorsA) ψ)
    (fun ψ => mutEss0 ctorsA.length esF ψ)
  /-- the derived former's member premises -/
  stageOk : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
    TupleLfpStageOk V b.nP t f₀.s W b.k (blockIds b.nP ppsF)
      (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
      (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
      (mutRss ctorsA.length (mutKsOf kinds))
      (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
      (fun ψ => mutFss0 b.nP ctorsA.length dsF (mutKsOf kinds) (mutNFOf ctorsA) ψ)
      (fun ψ => mutEss0 ctorsA.length esF ψ) (ppsF t)

/-! ## The formers' stage -/

/-- **The formers' stage of the mutual install** (stages 0–2 of the
run): the chain-free first pass conses the members with dummy leaves,
at which the constructors' data and the block's chain facts are read;
the real conses go through the derived former's API
(`stageTupleFormers`); the constructors' data at the real model are
identified with the first pass's off the recursive slots
(`mutualCtorDataI_ident`). -/
theorem mutualFormersStage (hμ : μ.verifiedChecks = true) {F : Nat}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (b : MutualBlock) {fms : List MutualFormerA} {f₀ : MutualFormerA} {tq₀ : List Expr × Expr}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    {kinds : List (List (RecFieldKind × Nat))}
    (h0 : b.blockNames.Nodup)
    (h1 : (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true)
    (h2 : b.ctors.all (fun c => c.member < b.k) = true)
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (ConLeche.consMutualFormers fms env, fms))
    (hf0 : fms[0]? = some f₀)
    (htq0 : ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some tq₀)
    (hcross : ConLeche.mutualCrossChecks (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b.nP f₀ (tq₀.1.map Expr.fvarTypeD) fms = .ok ())
    (hctors : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) b.ctors
      = .ok (ctorsA, sortss))
    (hkinds : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds)
    (hfo : ConLeche.mutualFieldsOk env b.members3 b.lps b.nP ctorsA kinds = true) :
    ∃ (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
      (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
      (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
      (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
      (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
      (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))),
      MutualFormersFacts V F mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF
        xFvsF xrestF eissF tssF := by
  -- stage 1, split: the checks at the PRE-BLOCK environment, the conses after
  obtain ⟨hchecks, henv₁⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨hlenFms, hposF⟩ := mutualFormerChecks_pos hchecks
  have hkF : fms.length = b.k := hlenFms
  -- the checked members carry the declared names and level parameters
  have hnamesF : fms.map (·.cvTa.name) = b.memberNames := by
    refine List.ext_getElem? fun t => ?_
    rw [List.getElem?_map]
    cases hft : fms[t]? with
    | none =>
      have hn : b.formers[t]? = none := by
        rw [List.getElem?_eq_none_iff] at hft ⊢; omega
      simp [ConLeche.MutualBlock.memberNames, List.getElem?_map, hn]
    | some f =>
      obtain ⟨cv, cv', bs, hl, hccv, hn1, -, -⟩ := hposF t f hft
      obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ :=
        ConLeche.checkConstantVal_inv hccv
      simp [ConLeche.MutualBlock.memberNames, List.getElem?_map, hl, hty, hn1]
  -- the block's names are distinct
  have hndM : (b.formers.map (·.1.name)).Nodup := by
    have h0' := h0
    unfold ConLeche.MutualBlock.blockNames ConLeche.MutualBlock.memberNames at h0'
    exact (List.nodup_append.mp (List.nodup_append.mp h0').1).1
  have hndC : (b.ctors.map (·.cv.name)).Nodup := by
    have h0' := h0
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp (List.nodup_append.mp h0').1).2.1
  have hndF : (fms.map (·.cvTa.name)).Nodup := by
    rw [hnamesF]; exact hndM
  -- every member carries the block's level parameters and is fresh before the block
  have hlpsF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → f.cvTa.levelParams = b.lps := by
    intro t f hft
    obtain ⟨cv, cv', bs, hl, hccv, -, hl2, -⟩ := hposF t f hft
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ :=
      ConLeche.checkConstantVal_inv hccv
    have hall : (b.formers.all fun f => f.1.levelParams == b.lps) = true := by
      simpa using (Bool.and_eq_true _ _ |>.mp h1).1
    have := List.all_eq_true.mp hall (cv, f.nIdx) (List.mem_of_getElem? hl)
    rw [hty]
    show cv'.levelParams = _
    rw [hl2]
    simpa using this
  have hfreshF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      env.find? f.cvTa.name = none := by
    intro t f hft
    obtain ⟨cv, cv', bs, -, hccv, -, -, -⟩ := hposF t f hft
    obtain ⟨hfind, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    rw [hty]; exact hfind
  have hstripF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∃ bs : List (Expr × BinderMeta), f.cvTa.type.stripPis (b.nP + f.nIdx) = some (bs, .sort f.s) := by
    intro t f hft
    obtain ⟨cv, cv', bs, -, -, -, -, hstrip⟩ := hposF t f hft
    exact ⟨bs, hstrip⟩
  have hcbF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f → ConstsBound env f.cvTa.type := by
    intro t f hft
    obtain ⟨cv, cv', bs, -, hccv, -, -, -⟩ := hposF t f hft
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, htr, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    exact constsBound_of_constsResolve _ (by rw [hty]; exact htr)
  -- the members' binder data at the pre-block carrier, and their binders' universes
  have hFDex : ∀ t : Nat, ∃ (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (us : List Level),
      (∀ f : MutualFormerA, fms[t]? = some f →
        FormerData mp.base2 f.cvTa (b.nP + f.nIdx) f.s pps ∧
        ∀ (ψ : Name → Nat) (i : Nat), i < b.nP + f.nIdx → ∀ ρ : Nat → V,
          Sat V ((((pps ψ).take i).map (·.2.2)).reverse) ρ →
          interp V ρ ((pps ψ).getD i default).2.2
            ∈ˢ (univ (Level.eval (restrictΨ b.lps ψ) (us.getD i .zero)) : V)) ∧
      (fms[t]? = none → ∀ ψ : Name → Nat, pps ψ = []) := by
    intro t
    cases hft : fms[t]? with
    | none =>
      refine ⟨fun _ => [], [], fun f hf => ?_, fun _ _ => rfl⟩
      simp at hf
    | some f =>
      obtain ⟨cv, cv', bs, -, hccv, -, -, hstrip⟩ := hposF t f hft
      obtain ⟨pps, hFD⟩ := formerData_of hμ mp hccv hstrip
      obtain ⟨us, -, hus⟩ := formerLevels_of hμ mp hccv hstrip hFD
      refine ⟨pps, us, fun f' hf' => ?_, fun hn => nomatch hn⟩
      obtain rfl := Option.some.inj hf'
      refine ⟨hFD, fun ψ i hi ρ hρ => ?_⟩
      have := hus ψ i hi ρ hρ
      rwa [hlpsF t f hft] at this
  let ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm) := fun t => (hFDex t).choose
  let usF : Nat → List Level := fun t => (hFDex t).choose_spec.choose
  have hFDF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      FormerData mp.base2 f.cvTa (b.nP + f.nIdx) f.s (ppsF t) :=
    fun t f hf => ((hFDex t).choose_spec.choose_spec.1 f hf).1
  have hlvF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (i : Nat), i < b.nP + f.nIdx → ∀ ρ : Nat → V,
        Sat V ((((ppsF t ψ).take i).map (·.2.2)).reverse) ρ →
        interp V ρ ((ppsF t ψ).getD i default).2.2
          ∈ˢ (univ (Level.eval (restrictΨ b.lps ψ) ((usF t).getD i .zero)) : V) :=
    fun t f hf => ((hFDex t).choose_spec.choose_spec.1 f hf).2
  have hppsNone : ∀ t : Nat, fms[t]? = none → ∀ ψ : Name → Nat, ppsF t ψ = [] :=
    fun t => (hFDex t).choose_spec.choose_spec.2
  -- every member is stored at the formers' environment with the block's EMPTY capability record
  have hfindF : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      (ConLeche.consMutualFormers fms env).find? f.cvTa.name = some (.indInfo f.cvTa {}) :=
    fun t f hf => consMutualFormers_find?_self (List.mem_of_getElem? hf) hndF
  -- the cross-member checks: one result sort for the whole block
  have hcrossAll := mutualCrossChecks_all hcross
  have hsEq : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ ψ : Name → Nat, f.s.eval ψ = f₀.s.eval ψ := fun t f hf ψ =>
    Level.isEquiv_sound (hcrossAll f (List.mem_of_getElem? hf)).1 ψ
  have hFD : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      FormerData mp.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t) :=
    fun t f hf => FormerData.congr_sort (hFDF t f hf) (hsEq t f hf)
  -- **the chain-free first pass**: the members consed with the sum route's chain-free towers
  have hmem₀ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      f.cvTa.levelParams = b.lps ∧
      FormerData mp.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t) ∧
      (∀ ψ : Name → Nat,
        Term.bvarsBelow 0 (sumTyAV (f₀.s.eval ψ) (ppsF t ψ) ([] : List (List AnnotTerm))).erase) ∧
      (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) →
        sumTyAV (f₀.s.eval ψ₁) (ppsF t ψ₁) [] = sumTyAV (f₀.s.eval ψ₂) (ppsF t ψ₂) []) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        WellDenotedV V ρ (sumTyAV (f₀.s.eval ψ) (ppsF t ψ) [])) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        interp V ρ (sumTyAV (f₀.s.eval ψ) (ppsF t ψ) [])
          ∈ˢ interp V ρ (mkPisAV (ppsF t ψ) (.sort (f₀.s.eval ψ)))) := by
    intro t f hft
    have hFDt := hFD t f hft
    have hwalk := formerWalksS (V := V) hFDt (Fss := fun _ => [])
      (fun ψ ρ _ => ⟨(fun Fs hFs => nomatch hFs), (fun Fs hFs => nomatch hFs)⟩)
    refine ⟨hlpsF t f hft, hFDt, ?_, ?_, ?_, ?_⟩
    · intro ψ
      exact sumTyAV_below (hFDt.below ψ) (fun Fs hFs => nomatch hFs)
    · intro ψ₁ ψ₂ hφ
      obtain ⟨hp, hw⟩ := hFDt.params ψ₁ ψ₂ (by rw [hlpsF t f hft]; exact hφ)
      show sumTyAV _ _ _ = sumTyAV _ _ _
      rw [hp, hw]
    · exact fun ψ ρ => sumTyAV_wellDenotedV (hwalk ψ ρ).1 (hwalk ψ ρ).2
    · exact fun ψ ρ => sumTyAV_mem (hwalk ψ ρ).1
  obtain ⟨mp₀, hleaf₀, hoff₀⟩ := stageMembersG mp hE hformers hndF hmem₀
  -- the block's readers
  have hk0 : 0 < fms.length := by
    have := (List.getElem?_eq_some_iff.mp hf0).1; omega
  have hfmGet : ∀ t : Nat, t < fms.length → fms[t]? = some (fms.getD t default) := by
    intro t ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl
  have hmemT : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      mutualNameOf b.members3 t = f.cvTa.name ∧ mutualNIdxOf b.members3 t = f.nIdx := by
    intro t f hft
    obtain ⟨cv, cv', bs, hl, hccv, hn1, -, -⟩ := hposF t f hft
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    have htk : t < b.k := by
      show t < b.formers.length
      exact (List.getElem?_eq_some_iff.mp hl).1
    have hgetD : b.formers.getD t default = (cv, f.nIdx) := by
      rw [List.getD_eq_getElem?_getD, hl]; rfl
    rw [mutualNameOf_members3 htk, mutualNIdxOf_members3 htk, hgetD]
    exact ⟨by rw [hty]; exact hn1.symm, rfl⟩
  -- the constructors, positionally, and their classified kinds
  obtain ⟨hlenA, hlenS, hallC⟩ := ConLeche.checkMutualCtors_inv hctors
  obtain ⟨hkindsM, -, -, hlenK⟩ := ConLeche.classifyMutualKinds_inv hkinds
  obtain ⟨hlenAK, hfoJ⟩ := mutualFieldsOk_inv hfo
  have hctorGet : ∀ (J : Nat), J < ctorsA.length →
      b.ctors[J]? = some (b.ctors.getD J default) := by
    intro J hJ
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [← hlenA]; exact hJ)]; rfl
  have hmotLt : ∀ (J : Nat), J < ctorsA.length → mutMemF b J < fms.length := by
    intro J hJ
    have hall : (b.ctors.all fun c => decide (c.member < b.k)) = true := h2
    have := List.all_eq_true.mp hall (b.ctors.getD J default)
      (List.mem_of_getElem? (hctorGet J hJ))
    simp only [decide_eq_true_eq] at this
    show _ < fms.length
    rw [hlenFms]
    exact this
  have hrunC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      cA.2 = (b.ctors.getD J default).nF ∧
      ∃ sorts : List Level, sortss[J]? = some sorts ∧
        ConLeche.checkMutualCtor (ConLeche.fueledOps μ F) (ConLeche.consMutualFormers fms env)
          b.memberNames (fms.getD (mutMemF b J) default).cvTa.name b.lps b.nP
          (fms.getD (mutMemF b J) default).nIdx (fms.getD (mutMemF b J) default).s
          (Level.isEquiv f₀.s Level.zero == some true) b.large (b.ctors.getD J default).cv cA.2
          (fms.getD (mutMemF b J) default).cvTa = .ok (cA.1, sorts) := by
    intro J cA hJ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    obtain ⟨hnF, sorts, hsj, hrun⟩ := hallC J _ cA (hctorGet J hJl) hJ
    exact ⟨hnF, sorts, hsj, by rw [hnF]; exact hrun⟩
  -- the kinds: classified on the stored constructors, re-checked opened, targets members
  have hksJ : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      (mutKsOf kinds J).length = cA.2 ∧
      ConLeche.mutualOpenedOk env b.members3 b.lps b.nP cA.1.type cA.2 (mutKsOf kinds J) = true ∧
      ∀ i, tgtAt (mutKsOf kinds J) i < fms.length := by
    intro J cA hJ
    obtain ⟨ks, hks, hlenks, hopened⟩ := hfoJ J cA hJ
    have hksD : mutKsOf kinds J = ks := by
      show kinds.getD J [] = ks
      rw [List.getD_eq_getElem?_getD, hks]; rfl
    obtain ⟨ks', hks', hkJ⟩ := mapM_option_getElem? hkindsM J cA hJ
    obtain rfl := Option.some.inj (hks.symm.trans hks')
    refine ⟨by rw [hksD]; exact hlenks, by rw [hksD]; exact hopened, fun i => ?_⟩
    rw [hksD]
    rcases mutualCtorKinds_tgt hkJ i with h0' | ⟨x, hx, hxe⟩
    · rw [h0']; exact hk0
    · rw [← hxe, hlenFms]; exact members3_mem_lt hx
  -- the members' data at the formers' carrier: their types resolve before the block
  have hagree₀ : ∀ n : Name, (env.find? n).isSome = true →
      mp.base2.acval n = mp₀.base2.acval n := by
    intro n hn
    refine (hoff₀ n (fun t f hft hh => ?_)).symm
    rw [hh, hfreshF t f hft] at hn
    exact nomatch hn
  obtain ⟨hFP, hLG, hPJ⟩ := consMutualFormers_extend (fms := fms) (env := env)
    (fun f hf => by obtain ⟨t, ht⟩ := List.getElem?_of_mem hf; exact hfreshF t f ht) hndF
  have hFD₁ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      FormerData mp₀.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t) :=
    fun t f hft => FormerData.crossEnv (hFD t f hft) (hcbF t f hft) hFP hLG hPJ hagree₀
  -- **the constructors' data**, at the formers' carrier (any model of it)
  have hCDexAt : ∀ mpX : EnvModelM V μ (ConLeche.consMutualFormers fms env),
      ∀ J : Nat, ∃ (idxF : List Expr)
      (dsF : (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : (Name → Nat) → List AnnotTerm) (srcsF : List (Option Nat))
      (fvsPF xFvsF : List Expr) (xrestF : Expr)
      (eissF : (Name → Nat) → List (List AnnotTerm))
      (tssF : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))),
      ∀ cA : ConstantVal × Nat, ctorsA[J]? = some cA →
        MutualCtorDataI mpX.base2 env b.members3
          (fms.getD (mutMemF b J) default).cvTa.name
          b.lps cA.1 b.nP cA.2
          (fms.getD (mutMemF b J) default).nIdx
          (fms.getD (mutMemF b J) default).s
          (Level.isEquiv f₀.s Level.zero == some true) b.large
          idxF dsF esF srcsF (mutKsOf kinds J) fvsPF xFvsF xrestF eissF tssF := by
    intro mpX J
    cases hJ : ctorsA[J]? with
    | none =>
      exact ⟨[], fun _ => [], fun _ => [], [], [], [], default, fun _ => [], fun _ => [],
        fun cA hcA => nomatch hcA⟩
    | some cA =>
      have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
      obtain ⟨hnF, sorts, hsj, hrun⟩ := hrunC J cA hJ
      obtain ⟨hlenks, hopened, htgt⟩ := hksJ J cA hJ
      have hmt : mutMemF b J < fms.length := hmotLt J hJl
      have hmtG := hfmGet _ hmt
      obtain ⟨bsT, hstripT⟩ := hstripF _ _ hmtG
      have hfM : ∀ i, i < cA.2 →
          (kindAt (mutKsOf kinds J) i = .recursive ∨ kindAt (mutKsOf kinds J) i = .reflexive) →
          ∃ (ci : ConstantInfo) (bs' : List (Expr × BinderMeta)) (s' : Level),
            (ConLeche.consMutualFormers fms env).find?
              (mutualNameOf b.members3 (tgtAt (mutKsOf kinds J) i)) = some ci ∧
            ci.toConstantVal.levelParams = b.lps ∧
            ci.toConstantVal.type.stripPis (b.nP +
                mutualNIdxOf b.members3 (tgtAt (mutKsOf kinds J) i))
              = some (bs', .sort s') ∧
            ∀ ψ : Name → Nat,
              s'.eval ψ = (fms.getD (mutMemF b J) default).s.eval ψ := by
        intro i hi _
        have ht := htgt i
        have htG := hfmGet _ ht
        obtain ⟨hnm, hni⟩ := hmemT _ _ htG
        obtain ⟨bs', hs'⟩ := hstripF _ _ htG
        refine ⟨.indInfo (fms.getD (tgtAt (mutKsOf kinds J) i) default).cvTa {}, bs', _,
          by rw [hnm]; exact hfindF _ _ htG, hlpsF _ _ htG, by rw [hni]; exact hs', fun ψ => ?_⟩
        rw [hsEq _ _ htG ψ, hsEq _ _ hmtG ψ]
      obtain ⟨idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, eissF, tssF, hD⟩ :=
        mutualCtorData_of hμ mpX hrun (hfindF _ _ hmtG) (hlpsF _ _ hmtG) hstripT
          hlenks hfM hopened
      exact ⟨idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, eissF, tssF, fun cA' hcA' => by
        obtain rfl := Option.some.inj hcA'; exact hD⟩
  -- **the cross-member parameter identification**
  have hopened₀ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∃ tq : List Expr × Expr, ConLeche.openPisAtFvars b.nP f.cvTa.type 0 = some tq ∧
        ConLeche.mutualDomsOk (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consMutualFormers fms env) tq.1 (tq₀.1.map Expr.fvarTypeD) b.nP
          = .ok () := fun t f hft => (hcrossAll f (List.mem_of_getElem? hft)).2
  have hOpenedAt : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (tfvs : List Expr) (trest : Expr),
        ConLeche.openPisAtFvars b.nP f.cvTa.type 0 = some (tfvs, trest) →
        Opened mp₀.base2 ψ b.nP f.cvTa.type tfvs trest
          ((((ppsF t ψ).take b.nP).map (·.2.2)).reverse)
          (mkPisAV ((ppsF t ψ).drop b.nP) (.sort (f₀.s.eval ψ))) := by
    intro t f hft ψ tfvs trest hop
    have hFDt := hFD₁ t f hft
    obtain ⟨hTf, -, -, hTb, -⟩ :=
      mp₀.base2.wf _ (ConLeche.Semantics.Env.find?_mem (hfindF t f hft))
    simp only [ConstantInfo.toConstantVal] at hTf hTb
    obtain ⟨Γt, Rt, hteleT, hT⟩ := opened_of hop hTf hTb (hFDt.read ψ) (hFDt.okTy ψ)
    obtain ⟨pps', hst', hΓt⟩ := stripPisAV_of_piTeleAV hteleT
    have hst'' := stripPisAV_mkPisAV_take b.nP (ppsF t ψ)
      (AnnotTerm.sort (f₀.s.eval ψ)) (by rw [hFDt.len ψ]; omega)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst'.symm.trans hst''))
    subst hΓt
    exact hT
  have hframeM : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρ ↔
          Sat V (((ppsF 0 ψ).take b.nP).map (·.2.2)).reverse ρ := by
    intro t f hft ψ ρ
    obtain ⟨tq, hopT, hdoms⟩ := hopened₀ t f hft
    have hpins := ConLeche.mutualDomsOk_inv hdoms
    have hT := hOpenedAt 0 f₀ hf0 ψ tq₀.1 tq₀.2 (by cases tq₀; exact htq0)
    have hC := hOpenedAt t f hft ψ tq.1 tq.2 (by cases tq; exact hopT)
    have hpf := paramFrames (nF := 0) (claimsAt_of hμ mp₀ ψ F) hT hC (fun i hi => by
      obtain ⟨a, b', ha, hb, hdeq⟩ := hpins i hi
      rw [List.getElem?_map] at hb
      obtain ⟨b'', hb', rfl⟩ := Option.map_eq_some_iff.mp hb
      exact ⟨a, b'', ha, hb', hdeq⟩)
    have h := (hpf b.nP (Nat.le_refl _)).1 ρ
    rw [Nat.add_zero, Nat.sub_self, List.drop_zero, List.drop_zero] at h
    exact h
  have hframeAll : ∀ (t t' : Nat) (f f' : MutualFormerA), fms[t]? = some f → fms[t']? = some f' →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρ →
        Sat V (((ppsF t' ψ).take b.nP).map (·.2.2)).reverse ρ :=
    fun t t' f f' hft hft' ψ ρ h => (hframeM t' f' hft' ψ ρ).mpr ((hframeM t f hft ψ ρ).mp h)
  -- **the block's index telescopes and the tag's universe**: the join of the binders' own
  let Wf : (Name → Nat) → Nat := fun ψ =>
    1 + ((List.range fms.length).map fun q =>
      ((usF q).map (Level.eval (restrictΨ b.lps ψ))).foldl max 0).foldl max 0
  let Idssf : (Name → Nat) → List (List AnnotTerm) := fun ψ => tupleIdss b.k (blockIds b.nP ppsF ψ)
  have hIdssGet : ∀ (ψ : Name → Nat) (t : Nat), t < fms.length →
      (Idssf ψ)[t]? = some (((ppsF t ψ).drop b.nP).map (·.2.2)) := by
    intro ψ t ht
    have ht' : t < b.k := by rw [← hkF]; exact ht
    exact tupleIdss_getElem? (Ids := blockIds b.nP ppsF ψ) ht'
  have hIdssLen : ∀ ψ : Name → Nat, (Idssf ψ).length = fms.length := by
    intro ψ; rw [tupleIdss_length, hkF]
  have hWge : ∀ (ψ : Name → Nat) (t j : Nat), t < fms.length →
      Level.eval (restrictΨ b.lps ψ) ((usF t).getD j .zero) ≤ Wf ψ := by
    intro ψ t j ht
    have h1 : Level.eval (restrictΨ b.lps ψ) ((usF t).getD j .zero)
        ≤ ((usF t).map (Level.eval (restrictΨ b.lps ψ))).foldl max 0 := by
      by_cases hj : j < (usF t).length
      · refine le_foldl_max _ _ _ ?_
        rw [← getD_map_eval _ _ hj, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [List.length_map]; exact hj)]
        exact List.getElem_mem _
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        exact Nat.zero_le _
    have h2 : ((usF t).map (Level.eval (restrictΨ b.lps ψ))).foldl max 0
        ≤ ((List.range fms.length).map fun q =>
          ((usF q).map (Level.eval (restrictΨ b.lps ψ))).foldl max 0).foldl max 0 :=
      le_foldl_max _ _ _ (List.mem_map.mpr ⟨t, List.mem_range.mpr ht, rfl⟩)
    show _ ≤ 1 + _
    omega
  have hIdxAll : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρ →
        TagOk (Wf ψ) ρ (Idssf ψ) ∧ ∀ Ids ∈ Idssf ψ, FieldsValid ρ Ids := by
    intro t f hft ψ ρ hρ
    have hpair : ∀ Ids ∈ Idssf ψ, IdxOk (Wf ψ) ρ Ids ∧ FieldsValid ρ Ids := by
      intro Ids hIds
      obtain ⟨t', ht', rfl⟩ := List.mem_map.mp (show Ids ∈ (List.range b.k).map
        (fun q => ((ppsF q ψ).drop b.nP).map (·.2.2)) from hIds)
      have ht'l : t' < fms.length := by rw [hkF]; exact List.mem_range.mp ht'
      exact formerIdxOk (hFD t' _ (hfmGet t' ht'l)) (ψ := ψ)
        (lv := fun i => Level.eval (restrictΨ b.lps ψ) ((usF t').getD i .zero))
        (hlvF t' _ (hfmGet t' ht'l) ψ) (fun j _ => hWge ψ t' (b.nP + j) ht'l) ρ
        (hframeAll t t' f _ hft (hfmGet t' ht'l) ψ ρ hρ)
    exact ⟨⟨show 1 + _ ≠ 0 by omega, fun Ids hIds => (hpair Ids hIds).1⟩,
      fun Ids hIds => (hpair Ids hIds).2⟩
  -- the constructors' data and the block's chain lists
  have hCDex : ∀ J : Nat, _ := hCDexAt mp₀
  let idxF : Nat → List Expr := fun J => (hCDex J).choose
  let dsF₀ : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm) := fun J =>
    (hCDex J).choose_spec.choose
  let esF₀ : Nat → (Name → Nat) → List AnnotTerm := fun J =>
    (hCDex J).choose_spec.choose_spec.choose
  let srcsF₀ : Nat → List (Option Nat) := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose
  let fvsPF₀ : Nat → List Expr := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose
  let xFvsF₀ : Nat → List Expr := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let xrestF₀ : Nat → Expr := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let eissF₀ : Nat → (Name → Nat) → List (List AnnotTerm) := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let tssF₀ : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)) := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hCD₀ : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      MutualCtorDataI mp₀.base2 env b.members3
        (fms.getD (mutMemF b J) default).cvTa.name
        b.lps cA.1 b.nP cA.2
        (fms.getD (mutMemF b J) default).nIdx
        (fms.getD (mutMemF b J) default).s
        (Level.isEquiv f₀.s Level.zero == some true) b.large
        (idxF J) (dsF₀ J) (esF₀ J) (srcsF₀ J) (mutKsOf kinds J) (fvsPF₀ J) (xFvsF₀ J)
        (xrestF₀ J) (eissF₀ J) (tssF₀ J) := fun J =>
    (hCDex J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  -- the block's chain lists (`MutualChains.lean`'s spellings)
  let ksF : Nat → List (RecFieldKind × Nat) := mutKsOf kinds
  let nFs : Nat → Nat := mutNFOf ctorsA
  let memF : Nat → Nat := mutMemF b
  let rssf : List (List Bool) := mutRss ctorsA.length ksF
  let Fss0f : (Name → Nat) → List (List AnnotTerm) := fun ψ =>
    mutFss0 b.nP ctorsA.length dsF₀ ksF nFs ψ
  let tlssf : (Name → Nat) → List (List (List (Nat × Nat × AnnotTerm))) := fun ψ =>
    mutTlss ctorsA.length tssF₀ ψ
  let Essf : (Name → Nat) → List (List AnnotTerm) := fun ψ =>
    mutEss' (n := ctorsA.length) (Wf ψ) (Idssf ψ) memF nFs esF₀ ψ
  let Eissf : (Name → Nat) → List (List (List AnnotTerm)) := fun ψ =>
    mutEiss' (n := ctorsA.length) (Wf ψ) (Idssf ψ) ksF nFs tssF₀ eissF₀ ψ
  have hcAGet : ∀ J : Nat, J < ctorsA.length → ctorsA[J]? = some (ctorsA.getD J default) := by
    intro J hJ
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ]; rfl
  -- **the block's chain facts**, at every member's parameter frame
  have hChainJ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
        Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρp →
        ∀ J : Nat, J < ctorsA.length →
          ChainFacts (Wf ψ) (f₀.s.eval ψ) b.nP (nFs J) ρp
              (auxIds (Wf ψ) (Idssf ψ)) (kindsOf (ksF J)) ((tlssf ψ).getD J [])
              ((Fss0f ψ).getD J []) ((Eissf ψ).getD J []) ((Essf ψ).getD J []) ∧
            ChainValidFacts b.nP (nFs J) ρp (kindsOf (ksF J)) ((tlssf ψ).getD J [])
              ((Fss0f ψ).getD J []) ((Eissf ψ).getD J []) ((Essf ψ).getD J []) := by
    intro t f hft ψ ρp hρ J hJl
    have hJ : ctorsA[J]? = some (ctorsA.getD J default) := hcAGet J hJl
    have hmt : memF J < fms.length := hmotLt J hJl
    have hmtG := hfmGet _ hmt
    have hD := hCD₀ J _ hJ
    obtain ⟨hnF, sorts, hsj, hrun⟩ := hrunC J _ hJ
    have hFDm := FormerData.congr_sort (hFD₁ _ _ hmtG) (fun ψ' => (hsEq _ _ hmtG ψ').symm)
    have hleafTm : ∀ ψ' : Name → Nat, ∃ B,
        mp₀.base2.acval (fms.getD (memF J) default).cvTa.name ψ'
          = mkLamsC ((fms.getD (memF J) default).s.eval ψ' + 1) (ppsF (memF J) ψ') B := by
      intro ψ'
      refine ⟨sumBodyAV (f₀.s.eval ψ') [], ?_⟩
      rw [hsEq _ _ hmtG ψ', hleaf₀ _ _ hmtG]
      rfl
    have hPropJ : (Level.isEquiv f₀.s Level.zero == some true) = true →
        ∀ ψ' : Name → Nat, Level.eval ψ' (fms.getD (memF J) default).s
          = Level.eval ψ' Level.zero := by
      intro hp ψ'
      rw [hsEq _ _ hmtG ψ']
      exact Level.isEquiv_sound (beq_iff_eq.mp hp) ψ'
    have hρJ : Sat V (((ppsF (memF J) ψ).take b.nP).map (·.2.2)).reverse ρp :=
      hframeAll t (memF J) f _ hft hmtG ψ ρp hρ
    obtain ⟨hTagJ, hVJ⟩ := hIdxAll t f hft ψ ρp hρ
    have hTgtJ : ∀ i, i < (ctorsA.getD J default).2 →
        (kindAt (ksF J) i = .recursive ∨ kindAt (ksF J) i = .reflexive) →
        ∃ (ppsT : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
          ppsT.length = b.nP
            + mutualNIdxOf b.members3 (tgtAt (ksF J) i) ∧
          mp₀.base2.acval (mutualNameOf b.members3 (tgtAt (ksF J) i)) ψ
            = mkLamsC ((fms.getD (memF J) default).s.eval ψ + 1) ppsT B ∧
          (Idssf ψ)[tgtAt (ksF J) i]? = some ((ppsT.drop b.nP).map (·.2.2)) := by
      intro i hi _
      obtain ⟨-, -, htgt⟩ := hksJ J _ hJ
      have htl := htgt i
      have htG := hfmGet _ htl
      obtain ⟨hnm, hni⟩ := hmemT _ _ htG
      refine ⟨ppsF (tgtAt (ksF J) i) ψ, sumBodyAV (f₀.s.eval ψ) [], ?_, ?_, hIdssGet ψ _ htl⟩
      · rw [hni]; exact (hFD₁ _ _ htG).len ψ
      · rw [hnm, hsEq _ _ hmtG ψ, hleaf₀ _ _ htG]
        rfl
    have hC := mutualChainFacts_at hμ mp₀ hrun (hfindF _ _ hmtG) hPropJ hFDm hleafTm hD ψ ρp
      hρJ hTagJ (hIdssGet ψ _ hmt) hTgtJ
    have hCV := mutualChainValidFacts_at (W := Wf ψ) hμ mp₀ hrun (hfindF _ _ hmtG) hPropJ hFDm
      hleafTm hD ψ ρp hρJ hVJ (hIdssGet ψ _ hmt)
      (fun i hi _ => by
        obtain ⟨-, -, htgt⟩ := hksJ J _ hJ
        exact ⟨_, hIdssGet ψ _ (htgt i)⟩)
    have hEL : (eissF₀ J ψ).length = nFs J := hD.eissLen ψ
    have hgetT : (tlssf ψ).getD J [] = tssF₀ J ψ := mutTlss_getD hJl
    have hgetF : (Fss0f ψ).getD J []
        = shadowFs b.nP (kindsOf (ksF J)) (nFs J)
            (((dsF₀ J ψ).drop b.nP).map (·.2.2)) := mutFss0_getD hJl
    have hgetE : (Essf ψ).getD J []
        = [tagTupleAV (Wf ψ) (memF J) (nFs J) (Idssf ψ) (esF₀ J ψ)] := mutEss'_getD hJl
    have hgetI : (Eissf ψ).getD J []
        = (List.range (nFs J)).map fun i =>
            [tagTupleAV (Wf ψ) (tgtAt (ksF J) i) (i + ((tssF₀ J ψ).getD i []).length)
              (Idssf ψ) ((eissF₀ J ψ).getD i [])] := mutEiss'_getDJ hJl hEL
    rw [hgetT, hgetF, hgetE, hgetI, hsEq _ _ hmtG ψ] at *
    exact ⟨hC, hCV⟩
  -- **`MemberChainsOk`**, at every member
  have hXAll : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρp : Nat → V),
        Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρp →
        XChainsOk (Wf ψ) (f₀.s.eval ψ) ρp (auxIds (Wf ψ) (Idssf ψ)) rssf (tlssf ψ) (Eissf ψ)
            (Fss0f ψ) (Essf ψ) ∧
          ∀ X, X ∈ˢ lfpFamSpace V (f₀.s.eval ψ) (idxSet (Wf ψ) ρp (auxIds (Wf ψ) (Idssf ψ))) →
            ∀ τ, τ ∈ˢ idxSet (Wf ψ) ρp (auxIds (Wf ψ) (Idssf ψ)) →
              SumFieldsValid (cons τ (cons X ρp))
                (chainsXI (Wf ψ) (auxIds (Wf ψ) (Idssf ψ))
                  (auxIds (Wf ψ) (Idssf ψ)).length rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ)
                  (Essf ψ)) := by
    intro t f hft ψ ρp hρ
    obtain ⟨hTagJ, hVJ⟩ := hIdxAll t f hft ψ ρp hρ
    have hFs₀ : ∀ J : Nat, J < ctorsA.length → ((Fss0f ψ).getD J []).length = nFs J := by
      intro J hJ
      rw [mutFss0_getD hJ]
      exact shadowFs_length
    exact xChainsOk_of (V := V) (u := Wf ψ) (w := f₀.s.eval ψ)
      (nP := b.nP) (n := ctorsA.length) (Ids := auxIds (Wf ψ) (Idssf ψ))
      (ksF := fun J => kindsOf (ksF J)) (rss := rssf) (tlss := tlssf ψ) (Eiss := Eissf ψ)
      (Fss := Fss0f ψ) (Ess := Essf ψ)
      (auxIds_idxOk hTagJ) (auxIds_fieldsValid hVJ)
      (by show ((List.range ctorsA.length).map _).length = _; simp)
      (fun J hJ => mutRss_getD hJ)
      (fun J hJ => by rw [hFs₀ J hJ]; exact (hChainJ t f hft ψ ρp hρ J hJ).1)
      (fun J hJ => by rw [hFs₀ J hJ]; exact (hChainJ t f hft ψ ρp hρ J hJ).2)
  have hMCO : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberChainsOk V b.nP t f₀.s Wf Idssf rssf tlssf Eissf Fss0f Essf (ppsF t) := by
    intro t f hft
    have hlt : t < fms.length := (List.getElem?_eq_some_iff.mp hft).1
    refine ⟨fun ψ => hIdssGet ψ t hlt, fun ψ ρp hρ => ?_⟩
    obtain ⟨hTagJ, hVJ⟩ := hIdxAll t f hft ψ ρp hρ
    obtain ⟨hX, hvalid⟩ := hXAll t f hft ψ ρp hρ
    exact ⟨hTagJ, hVJ, hX.hok, hvalid⟩
  -- the level-parameter dependence of the block's data
  have hlpsC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      cA.1.levelParams = b.lps := by
    intro J cA hJ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    obtain ⟨-, sorts, -, hrun⟩ := hrunC J cA hJ
    obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    have hall : (b.ctors.all fun c => c.cv.levelParams == b.lps) = true := by
      simpa using (Bool.and_eq_true _ _ |>.mp h1).2
    have hthis := List.all_eq_true.mp hall _ (List.mem_of_getElem? (hctorGet J hJl))
    rw [hty]
    simpa using hthis
  have hCDparams : ∀ J : Nat, J < ctorsA.length → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) →
      dsF₀ J ψ₁ = dsF₀ J ψ₂ ∧ esF₀ J ψ₁ = esF₀ J ψ₂ ∧ eissF₀ J ψ₁ = eissF₀ J ψ₂ ∧
        tssF₀ J ψ₁ = tssF₀ J ψ₂ := by
    intro J hJl ψ₁ ψ₂ hφ
    have hJ := hcAGet J hJl
    have hD := hCD₀ J _ hJ
    have hφ' : ∀ q ∈ (ctorsA.getD J default).1.levelParams, ψ₁ q = ψ₂ q := by
      rw [hlpsC J _ hJ]; exact hφ
    obtain ⟨h1', h2'⟩ := hD.params ψ₁ ψ₂ hφ'
    exact ⟨h1', h2', hD.eissParams ψ₁ ψ₂ hφ', hD.tssParams ψ₁ ψ₂ hφ'⟩
  have hppsPar : ∀ t : Nat, t < fms.length → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) → ppsF t ψ₁ = ppsF t ψ₂ := by
    intro t ht ψ₁ ψ₂ hφ
    have hft := hfmGet t ht
    have hφ' : ∀ q ∈ (fms.getD t default).cvTa.levelParams, ψ₁ q = ψ₂ q := by
      rw [hlpsF t _ hft]; exact hφ
    exact ((hFD t _ hft).params ψ₁ ψ₂ hφ').1
  have hWpar : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) → Wf ψ₁ = Wf ψ₂ := by
    intro ψ₁ ψ₂ hφ
    show 1 + ((List.range fms.length).map _).foldl max 0
      = 1 + ((List.range fms.length).map _).foldl max 0
    rw [restrictΨ_congr hφ]
  have hIdssPar : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) →
      blockIds b.nP ppsF ψ₁ = blockIds b.nP ppsF ψ₂ := by
    intro ψ₁ ψ₂ hφ
    funext q
    show ((ppsF q ψ₁).drop b.nP).map (·.2.2) = ((ppsF q ψ₂).drop b.nP).map (·.2.2)
    by_cases hq : q < fms.length
    · rw [hppsPar q hq ψ₁ ψ₂ hφ]
    · have hn : fms[q]? = none := List.getElem?_eq_none (by omega)
      rw [hppsNone q hn ψ₁, hppsNone q hn ψ₂]
  have hParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) →
      Wf ψ₁ = Wf ψ₂ ∧ blockIds b.nP ppsF ψ₁ = blockIds b.nP ppsF ψ₂ ∧ tlssf ψ₁ = tlssf ψ₂ ∧
        mutEiss0 ctorsA.length eissF₀ ψ₁ = mutEiss0 ctorsA.length eissF₀ ψ₂ ∧
        Fss0f ψ₁ = Fss0f ψ₂ ∧ mutEss0 ctorsA.length esF₀ ψ₁ = mutEss0 ctorsA.length esF₀ ψ₂ := by
    intro ψ₁ ψ₂ hφ
    refine ⟨hWpar ψ₁ ψ₂ hφ, hIdssPar ψ₁ ψ₂ hφ, ?_, ?_, ?_, ?_⟩
    · show mutTlss _ _ _ = mutTlss _ _ _
      unfold mutTlss
      exact List.map_congr_left (fun J hJ => by
        rw [(hCDparams J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ).2.2.2])
    · unfold mutEiss0
      exact List.map_congr_left (fun J hJ => by
        rw [(hCDparams J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ).2.2.1])
    · show mutFss0 _ _ _ _ _ _ = mutFss0 _ _ _ _ _ _
      unfold mutFss0
      exact List.map_congr_left (fun J hJ => by
        rw [(hCDparams J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ).1])
    · unfold mutEss0
      exact List.map_congr_left (fun J hJ => by
        rw [(hCDparams J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ).2.1])
  -- the block's data is bounded at the parameters
  have hIdsBelow : ∀ ψ : Name → Nat, ∀ Ids ∈ Idssf ψ, FieldsBelow b.nP Ids := by
    intro ψ Ids hIds
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (show Ids ∈ (List.range b.k).map
      (fun q => ((ppsF q ψ).drop b.nP).map (·.2.2)) from hIds)
    have hql : q < fms.length := by rw [hkF]; exact List.mem_range.mp hq
    have hh := (DomsBelow.drop b.nP ((hFD q _ (hfmGet q hql)).below ψ)).fields
    rwa [Nat.zero_add] at hh
  have hchainBelow : ∀ ψ : Name → Nat, ∀ chain ∈ chainsXI (Wf ψ) (auxIds (Wf ψ) (Idssf ψ)) 1
      rssf (tlssf ψ) (Eissf ψ) (Fss0f ψ) (Essf ψ), FieldsBelow (b.nP + 2) chain := by
    intro ψ
    refine chainsXI_below_of (u := Wf ψ) (nP := b.nP) (nIdx := 1)
      (n := ctorsA.length) (Ids := auxIds (Wf ψ) (Idssf ψ)) (rss := rssf) (tlss := tlssf ψ)
      (Eiss := Eissf ψ) (Fss := Fss0f ψ) (Ess := Essf ψ)
      (show FieldsBelow b.nP (auxIds (Wf ψ) (Idssf ψ)) from
        ⟨tagTyAV_below (hIdsBelow ψ), trivial⟩)
      (by show ((List.range ctorsA.length).map _).length = _; simp) ?_ ?_ ?_ ?_ ?_
    · intro J hJ i
      rw [mutTlss_getD hJ]
      exact (hCD₀ J _ (hcAGet J hJ)).tssBelow ψ i
    · intro J hJ i E hE
      have hEL : (eissF₀ J ψ).length = nFs J := (hCD₀ J _ (hcAGet J hJ)).eissLen ψ
      rw [mutTlss_getD hJ]
      by_cases hi : i < nFs J
      · rw [mutEiss'_getD hJ hi hEL, List.mem_singleton] at hE
        subst hE
        have hb := tagTupleAV_belowM (nP := b.nP) (W := Wf ψ)
          (m := tgtAt (ksF J) i)
          (d := i + ((tssF₀ J ψ).getD i []).length) (hIdsBelow ψ) (fun E hE => by
            have hh := (hCD₀ J _ (hcAGet J hJ)).eissBelow ψ i E hE
            rwa [show b.nP + i + ((tssF₀ J ψ).getD i []).length
              = b.nP + (i + ((tssF₀ J ψ).getD i []).length) from by omega] at hh)
        rwa [show b.nP + (i + ((tssF₀ J ψ).getD i []).length)
          = b.nP + i + ((tssF₀ J ψ).getD i []).length from by omega] at hb
      · rw [mutEiss'_getDJ hJ hEL, List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_eq_none (by simpa using Nat.le_of_not_lt hi)] at hE
        exact nomatch hE
    · intro J hJ
      rw [mutFss0_getD hJ]
      refine shadowFs_below (show (((dsF₀ J ψ).drop b.nP).map (·.2.2)).length = nFs J from
        by rw [List.length_map, List.length_drop, (hCD₀ J _ (hcAGet J hJ)).len ψ]
           show b.nP + nFs J - b.nP = nFs J
           omega) ?_
      have hh := (DomsBelow.drop b.nP ((hCD₀ J _ (hcAGet J hJ)).below ψ)).fields
      rwa [Nat.zero_add] at hh
    · intro J hJ
      rw [mutEss'_getD hJ]
      rfl
    · intro J hJ E hE
      rw [mutEss'_getD hJ, List.mem_singleton] at hE
      subst hE
      rw [mutFss0_getD hJ, shadowFs_length]
      exact tagTupleAV_belowM (nP := b.nP) (W := Wf ψ) (m := memF J) (d := nFs J)
        (hIdsBelow ψ) (fun E hE => (hCD₀ J _ (hcAGet J hJ)).belowE ψ E hE)
  -- **the formers' stage**: the members consed with their `k`-ary leaves
  have hB : TupleLfpBlockOk b.nP b.lps Wf b.k (blockIds b.nP ppsF)
      (mutMems ctorsA.length memF) (mutNFs ctorsA.length nFs) (mutTgts ctorsA.length ksF nFs)
      rssf (fun ψ => tlssf ψ) (fun ψ => mutEiss0 ctorsA.length eissF₀ ψ) (fun ψ => Fss0f ψ)
      (fun ψ => mutEss0 ctorsA.length esF₀ ψ) :=
    TupleLfpBlockOk.of_tagged hParams hIdsBelow hchainBelow
  obtain ⟨mp₁, hleaf₁, hoff₁, hstored⟩ := stageTupleFormers (V := V) (μ := μ) (F := F) hB mp hE
    hformers hndF (fun t f hft => ⟨hlpsF t f hft, hFD t f hft,
      TupleLfpStageOk.of_tagged (hMCO t f hft)⟩)
  have hagree₁ : ∀ n : Name, (env.find? n).isSome = true →
      mp₀.base2.acval n = mp₁.base2.acval n := by
    intro n hn
    have h0' := hoff₀ n (fun t f hft hh => by rw [hh, hfreshF t f hft] at hn; exact nomatch hn)
    have h1' := hoff₁ n (fun t f hft hh => by rw [hh, hfreshF t f hft] at hn; exact nomatch hn)
    rw [h0', h1']
  -- the constructors' data at the MEMBER LEAVES, identified with the
  -- chain-free pass's off the recursive and reflexive slots
  have hCDex₁ : ∀ J : Nat, _ := hCDexAt mp₁
  let idxF₁ : Nat → List Expr := fun J => (hCDex₁ J).choose
  let dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm) := fun J =>
    (hCDex₁ J).choose_spec.choose
  let esF : Nat → (Name → Nat) → List AnnotTerm := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose
  let srcsF : Nat → List (Option Nat) := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose
  let fvsPF : Nat → List Expr := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose
  let xFvsF : Nat → List Expr := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let xrestF : Nat → Expr := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let eissF : Nat → (Name → Nat) → List (List AnnotTerm) := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  let tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)) := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
  have hCD₁ : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      MutualCtorDataI mp₁.base2 env b.members3
        (fms.getD (mutMemF b J) default).cvTa.name
        b.lps cA.1 b.nP cA.2
        (fms.getD (mutMemF b J) default).nIdx
        (fms.getD (mutMemF b J) default).s
        (Level.isEquiv f₀.s Level.zero == some true) b.large
        (idxF₁ J) (dsF J) (esF J) (srcsF J) (mutKsOf kinds J) (fvsPF J) (xFvsF J)
        (xrestF J) (eissF J) (tssF J) := fun J =>
    (hCDex₁ J).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec
  have hident : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      idxF J = idxF₁ J ∧ fvsPF₀ J = fvsPF J ∧ xFvsF₀ J = xFvsF J ∧ xrestF₀ J = xrestF J ∧
      (∀ ψ : Name → Nat, esF₀ J ψ = esF J ψ) ∧
      (∀ ψ : Name → Nat, eissF₀ J ψ = eissF J ψ) ∧
      (∀ ψ : Name → Nat, tssF₀ J ψ = tssF J ψ) ∧
      ∀ (ψ : Name → Nat) (i : Nat), i < cA.2 → kindAt (ksF J) i ≠ .recursive →
        kindAt (ksF J) i ≠ .reflexive →
        ((dsF₀ J ψ).getD (b.nP + i) default).2.2
          = ((dsF J ψ).getD (b.nP + i) default).2.2 :=
    fun J cA hJ => mutualCtorDataI_ident hagree₁ (hCD₀ J cA hJ) (hCD₁ J cA hJ)
  -- **the block's lists at the real readings** are the first pass's
  have hF0eq : ∀ ψ : Name → Nat,
      Fss0f ψ = mutFss0 b.nP ctorsA.length dsF ksF nFs ψ := by
    intro ψ
    show mutFss0 _ _ _ _ _ _ = mutFss0 _ _ _ _ _ _
    unfold mutFss0
    refine List.map_congr_left fun J hJ => ?_
    have hJl : J < ctorsA.length := List.mem_range.mp hJ
    have hJg := hcAGet J hJl
    have hlen₀ : (dsF₀ J ψ).length = b.nP + nFs J := (hCD₀ J _ hJg).len ψ
    have hlen₁ : (dsF J ψ).length = b.nP + nFs J := (hCD₁ J _ hJg).len ψ
    refine shadowFs_congr fun i hi hr => ?_
    have hks : (kindsOf (ksF J)).getD i .ordinary = kindAt (ksF J) i := by
      rw [kindsOf_getD (by rw [(hksJ J _ hJg).1]; exact hi)]
    rw [drop_map_getD hlen₀ hi, drop_map_getD hlen₁ hi]
    refine (hident J _ hJg).2.2.2.2.2.2.2 ψ i hi (fun hk => hr ?_) (fun hk => hr ?_)
    · exact ⟨Nat.le_add_right _ _, Or.inl (by rw [Nat.add_sub_cancel_left, hks]; exact hk)⟩
    · exact ⟨Nat.le_add_right _ _, Or.inr (by rw [Nat.add_sub_cancel_left, hks]; exact hk)⟩
  have hTleq : ∀ ψ : Name → Nat, tlssf ψ = mutTlss ctorsA.length tssF ψ := by
    intro ψ
    show mutTlss _ _ _ = mutTlss _ _ _
    unfold mutTlss
    exact List.map_congr_left fun J hJ =>
      (hident J _ (hcAGet J (List.mem_range.mp hJ))).2.2.2.2.2.2.1 ψ
  have hEseq : ∀ ψ : Name → Nat, mutEss0 ctorsA.length esF₀ ψ = mutEss0 ctorsA.length esF ψ := by
    intro ψ
    unfold mutEss0
    exact List.map_congr_left fun J hJ =>
      (hident J _ (hcAGet J (List.mem_range.mp hJ))).2.2.2.2.1 ψ
  have hEieq : ∀ ψ : Name → Nat,
      mutEiss0 ctorsA.length eissF₀ ψ = mutEiss0 ctorsA.length eissF ψ := by
    intro ψ
    unfold mutEiss0
    exact List.map_congr_left fun J hJ =>
      (hident J _ (hcAGet J (List.mem_range.mp hJ))).2.2.2.2.2.1 ψ
  have hF0fun : (fun ψ => Fss0f ψ) = fun ψ => mutFss0 b.nP ctorsA.length dsF ksF nFs ψ :=
    funext hF0eq
  have hTlfun : (fun ψ => tlssf ψ) = fun ψ => mutTlss ctorsA.length tssF ψ := funext hTleq
  have hEsfun : (fun ψ => mutEss0 ctorsA.length esF₀ ψ) = fun ψ => mutEss0 ctorsA.length esF ψ :=
    funext hEseq
  have hEifun : (fun ψ => mutEiss0 ctorsA.length eissF₀ ψ)
      = fun ψ => mutEiss0 ctorsA.length eissF ψ := funext hEieq
  rw [hF0fun, hTlfun, hEsfun, hEifun] at hB
  -- the constructors' facts at the real model
  have hlenA' : ctorsA.length = b.ctors.length := hlenA
  have hnamesC : ctorsA.map (·.1.name) = b.ctors.map (·.cv.name) := by
    refine List.ext_getElem? fun J => ?_
    rw [List.getElem?_map, List.getElem?_map]
    cases hJ : ctorsA[J]? with
    | none =>
      have hn : b.ctors[J]? = none := by
        rw [List.getElem?_eq_none_iff] at hJ ⊢; omega
      rw [hn]
      rfl
    | some cA =>
      have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
      obtain ⟨-, sorts, -, hrun⟩ := hrunC J cA hJ
      obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
      obtain ⟨-, -, -, -, -, -, _, _, _, -, -, -, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
      rw [hctorGet J hJl]
      simp only [Option.map_some, Option.some.injEq]
      rw [hty]
  have hresC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      cA.1.type.constsResolve (ConLeche.consMutualFormers fms env) = true := by
    intro J cA hJ
    obtain ⟨-, sorts, -, hrun⟩ := hrunC J cA hJ
    obtain ⟨⟨ty', hccv⟩, -, -⟩ := ConLeche.checkMutualCtor_shape hrun
    obtain ⟨-, -, -, -, -, -, _, _, _, -, -, htr, -, -, hty⟩ := ConLeche.checkConstantVal_inv hccv
    rw [hty]; exact htr
  have hCDpar₁ : ∀ J : Nat, J < ctorsA.length → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) →
      dsF J ψ₁ = dsF J ψ₂ ∧ esF J ψ₁ = esF J ψ₂ ∧ eissF J ψ₁ = eissF J ψ₂ ∧
        tssF J ψ₁ = tssF J ψ₂ := by
    intro J hJl ψ₁ ψ₂ hφ
    have hJ := hcAGet J hJl
    have hD := hCD₁ J _ hJ
    have hφ' : ∀ q ∈ (ctorsA.getD J default).1.levelParams, ψ₁ q = ψ₂ q := by
      rw [hlpsC J _ hJ]; exact hφ
    obtain ⟨h1', h2'⟩ := hD.params ψ₁ ψ₂ hφ'
    exact ⟨h1', h2', hD.eissParams ψ₁ ψ₂ hφ', hD.tssParams ψ₁ ψ₂ hφ'⟩
  -- the package
  refine ⟨mp₁, ppsF, Wf, idxF₁, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, eissF, tssF, ?_⟩
  refine
    { lenFms := hkF, first := hf0, sEq := hsEq, lps := hlpsF, fresh := hfreshF, strip := hstripF
      names := hnamesF, memT := hmemT, cbF := hcbF, find := fun t f hft => (hstored t f hft).1
      FD₀ := hFD, FD := fun t f hft => (hstored t f hft).2.1, leaf := ?_, off := hoff₁
      lenA := hlenA', lenK := hlenAK.symm, motLt := hmotLt, runC := hrunC, ksJ := hksJ
      CD := hCD₁, lpsC := hlpsC, namesC := hnamesC
      freshC := ConLeche.Semantics.checkMutualCtors_fresh hctors, resC := hresC
      frame := hframeM, idxAll := hIdxAll, CDpar := hCDpar₁, ppsPar := hppsPar
      blockOk := hB, stageOk := ?_ }
  · intro t f hft
    rw [hleaf₁ t f hft]
    funext ψ
    have hnI : f.nIdx = (fms.getD t default).nIdx := by
      rw [List.getD_eq_getElem?_getD, hft]; rfl
    unfold mutMemberLeaf
    rw [hF0eq ψ, hTleq ψ, hEseq ψ, hEieq ψ, hnI]
  · intro t f hft
    have h : TupleLfpStageOk V b.nP t f₀.s Wf b.k (blockIds b.nP ppsF)
        (mutMems ctorsA.length memF) (mutNFs ctorsA.length nFs) (mutTgts ctorsA.length ksF nFs)
        rssf (fun ψ => tlssf ψ) (fun ψ => mutEiss0 ctorsA.length eissF₀ ψ) (fun ψ => Fss0f ψ)
        (fun ψ => mutEss0 ctorsA.length esF₀ ψ) (ppsF t) :=
      TupleLfpStageOk.of_tagged (hMCO t f hft)
    rw [hF0fun, hTlfun, hEsfun, hEifun] at h
    exact h

/-! ## The block's lists, named -/

/-- The members' index telescopes at a level assignment. -/
@[expose] def blkIdss (b : MutualBlock) (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (ψ : Name → Nat) : List (List AnnotTerm) :=
  tupleIdss b.k (blockIds b.nP ppsF ψ)

/-- The constructors' recursive flags. -/
@[expose] def blkRss (ctorsA : List (ConstantVal × Nat)) (kinds : List (List (RecFieldKind × Nat))) :
    List (List Bool) :=
  mutRss ctorsA.length (mutKsOf kinds)

/-- The constructors' X-source chains (the shadow of the real domains). -/
@[expose] def blkFss0 (b : MutualBlock) (ctorsA : List (ConstantVal × Nat))
    (kinds : List (List (RecFieldKind × Nat)))
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (ψ : Name → Nat) :
    List (List AnnotTerm) :=
  mutFss0 b.nP ctorsA.length dsF (mutKsOf kinds) (mutNFOf ctorsA) ψ

/-- The constructors' tagged terminators. -/
@[expose] def blkEss (b : MutualBlock) (ctorsA : List (ConstantVal × Nat))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ψ : Name → Nat) : List (List AnnotTerm) :=
  tupleEss (W ψ) (blkIdss b ppsF ψ) (mutMems ctorsA.length (mutMemF b))
    (mutNFs ctorsA.length (mutNFOf ctorsA)) (mutEss0 ctorsA.length esF ψ)

/-- The recursive slots' tagged index expressions. -/
@[expose] def blkEiss (b : MutualBlock) (ctorsA : List (ConstantVal × Nat))
    (kinds : List (List (RecFieldKind × Nat)))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    List (List (List AnnotTerm)) :=
  tupleEiss (W ψ) (blkIdss b ppsF ψ) (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA))
    (mutTlss ctorsA.length tssF ψ) (mutEiss0 ctorsA.length eissF ψ)

section Lists

variable {b : MutualBlock} {ctorsA : List (ConstantVal × Nat)}
  {kinds : List (List (RecFieldKind × Nat))}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat}

theorem blkEss_getD {J : Nat} (hJ : J < ctorsA.length) :
    (blkEss b ctorsA ppsF W esF ψ).getD J []
      = [tagTupleAV (W ψ) (mutMemF b J) (mutNFOf ctorsA J) (blkIdss b ppsF ψ) (esF J ψ)] :=
  mutEss'_getD (n := ctorsA.length) (W := W ψ) (Idss := blkIdss b ppsF ψ) (memF := mutMemF b)
    (nFs := mutNFOf ctorsA) (esF := esF) (ψ := ψ) hJ

theorem blkEss_length : (blkEss b ctorsA ppsF W esF ψ).length = ctorsA.length :=
  mutEss'_length (n := ctorsA.length) (W := W ψ) (Idss := blkIdss b ppsF ψ) (memF := mutMemF b)
    (nFs := mutNFOf ctorsA) (esF := esF) (ψ := ψ)

theorem blkEiss_getDJ {J : Nat} (hJ : J < ctorsA.length)
    (hEL : (eissF J ψ).length = mutNFOf ctorsA J) :
    (blkEiss b ctorsA kinds ppsF W eissF tssF ψ).getD J []
      = (List.range (mutNFOf ctorsA J)).map fun i =>
          [tagTupleAV (W ψ) (tgtAt (mutKsOf kinds J) i) (i + ((tssF J ψ).getD i []).length)
            (blkIdss b ppsF ψ) ((eissF J ψ).getD i [])] :=
  mutEiss'_getDJ (n := ctorsA.length) (W := W ψ) (Idss := blkIdss b ppsF ψ)
    (ksF := mutKsOf kinds) (nFs := mutNFOf ctorsA) (tssF := tssF) (eissF := eissF) (ψ := ψ) hJ hEL

theorem blkEiss_getD {J i : Nat} (hJ : J < ctorsA.length) (hi : i < mutNFOf ctorsA J)
    (hEL : (eissF J ψ).length = mutNFOf ctorsA J) :
    ((blkEiss b ctorsA kinds ppsF W eissF tssF ψ).getD J []).getD i []
      = [tagTupleAV (W ψ) (tgtAt (mutKsOf kinds J) i) (i + ((tssF J ψ).getD i []).length)
          (blkIdss b ppsF ψ) ((eissF J ψ).getD i [])] :=
  mutEiss'_getD (n := ctorsA.length) (W := W ψ) (Idss := blkIdss b ppsF ψ)
    (ksF := mutKsOf kinds) (nFs := mutNFOf ctorsA) (tssF := tssF) (eissF := eissF) (ψ := ψ) hJ hi hEL

theorem blkFss0_getD {J : Nat} (hJ : J < ctorsA.length) :
    (blkFss0 b ctorsA kinds dsF ψ).getD J []
      = shadowFs b.nP (kindsOf (mutKsOf kinds J)) (mutNFOf ctorsA J)
          (((dsF J ψ).drop b.nP).map (·.2.2)) :=
  mutFss0_getD hJ

theorem blkRss_getD {J : Nat} (hJ : J < ctorsA.length) :
    (blkRss ctorsA kinds).getD J [] = rsOf (kindsOf (mutKsOf kinds J)) :=
  mutRss_getD hJ

theorem blkIdss_getElem? {t : Nat} (ht : t < b.k) :
    (blkIdss b ppsF ψ)[t]? = some (((ppsF t ψ).drop b.nP).map (·.2.2)) :=
  tupleIdss_getElem? (Ids := blockIds b.nP ppsF ψ) ht

end Lists

/-! ## The formers' facts, read -/

/-- A member position reads its member. -/
theorem fms_get {fms : List MutualFormerA} {t : Nat} (ht : t < fms.length) :
    fms[t]? = some (fms.getD t default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht]; rfl

/-- A constructor position reads its constructor. -/
theorem ctorsA_get {ctorsA : List (ConstantVal × Nat)} {J : Nat} (hJ : J < ctorsA.length) :
    ctorsA[J]? = some (ctorsA.getD J default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJ]; rfl

/-- A constructor's field count is its record's. -/
theorem mutNFOf_eq {ctorsA : List (ConstantVal × Nat)} {J : Nat} {cA : ConstantVal × Nat}
    (hJ : ctorsA[J]? = some cA) : mutNFOf ctorsA J = cA.2 := by
  show (ctorsA.getD J default).2 = cA.2
  rw [List.getD_eq_getElem?_getD, hJ]; rfl

section Facts

variable {F : Nat} {mp : EnvModelM V μ env} {b : MutualBlock} {fms : List MutualFormerA}
  {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
  {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  (h : MutualFormersFacts V F mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF
    xFvsF xrestF eissF tssF)
include h

namespace MutualFormersFacts

/-- A member's leaf is a λ-tower over its data. -/
theorem leafT {t : Nat} {f : MutualFormerA} (hft : fms[t]? = some f) (ψ : Name → Nat) :
    ∃ B, mp₁.base2.acval f.cvTa.name ψ = mkLamsC (f.s.eval ψ + 1) (ppsF t ψ) B := by
  rw [h.sEq t f hft ψ, h.leaf t f hft]
  exact tupleLfpAV_lams _ _ _

/-- A member's leaf, at the representation. -/
theorem leaf_repr {t : Nat} {f : MutualFormerA} (hft : fms[t]? = some f) (ψ : Name → Nat) :
    mp₁.base2.acval f.cvTa.name ψ
      = mutualTyAVI (W ψ) (f₀.s.eval ψ) (ppsF t ψ) f.nIdx (blkIdss b ppsF ψ) (blkRss ctorsA kinds)
          (mutTlss ctorsA.length tssF ψ) (blkEiss b ctorsA kinds ppsF W eissF tssF ψ)
          (blkFss0 b ctorsA kinds dsF ψ) (blkEss b ctorsA ppsF W esF ψ) t := by
  rw [h.leaf t f hft]
  unfold mutMemberLeaf
  rw [tupleLfpAV_repr]
  have hnI : (fms.getD t default).nIdx = f.nIdx := by
    rw [List.getD_eq_getElem?_getD, hft]; rfl
  rw [hnI]
  rfl

/-- The `Prop` bit implies every member's sort is zero. -/
theorem propJ {J : Nat} (hJ : J < ctorsA.length) :
    (Level.isEquiv f₀.s Level.zero == some true) = true →
    ∀ ψ : Name → Nat, Level.eval ψ (fms.getD (mutMemF b J) default).s = Level.eval ψ Level.zero := by
  intro hp ψ
  rw [h.sEq _ _ (fms_get (h.motLt J hJ)) ψ]
  exact Level.isEquiv_sound (beq_iff_eq.mp hp) ψ

/-- The constructor's member's data at its own sort. -/
theorem FDm {J : Nat} (hJ : J < ctorsA.length) :
    FormerData mp₁.base2 (fms.getD (mutMemF b J) default).cvTa
      (b.nP + (fms.getD (mutMemF b J) default).nIdx) (fms.getD (mutMemF b J) default).s
      (ppsF (mutMemF b J)) :=
  FormerData.congr_sort (h.FD _ _ (fms_get (h.motLt J hJ)))
    (fun ψ' => (h.sEq _ _ (fms_get (h.motLt J hJ)) ψ').symm)

/-- **The chain facts per constructor**, at every member's parameter frame. -/
theorem chainJ (hμ : μ.verifiedChecks = true) {t : Nat} {f : MutualFormerA}
    (hft : fms[t]? = some f) (ψ : Name → Nat)
    (ρp : Nat → V) (hρ : Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρp)
    {J : Nat} (hJl : J < ctorsA.length) :
    ChainFacts (W ψ) (f₀.s.eval ψ) b.nP (mutNFOf ctorsA J) ρp
        (auxIds (W ψ) (blkIdss b ppsF ψ)) (kindsOf (mutKsOf kinds J))
        ((mutTlss ctorsA.length tssF ψ).getD J []) ((blkFss0 b ctorsA kinds dsF ψ).getD J [])
        ((blkEiss b ctorsA kinds ppsF W eissF tssF ψ).getD J []) ((blkEss b ctorsA ppsF W esF ψ).getD J []) ∧
      ChainValidFacts b.nP (mutNFOf ctorsA J) ρp (kindsOf (mutKsOf kinds J))
        ((mutTlss ctorsA.length tssF ψ).getD J []) ((blkFss0 b ctorsA kinds dsF ψ).getD J [])
        ((blkEiss b ctorsA kinds ppsF W eissF tssF ψ).getD J []) ((blkEss b ctorsA ppsF W esF ψ).getD J []) := by
  have hJ : ctorsA[J]? = some (ctorsA.getD J default) := ctorsA_get hJl
  have hmt : mutMemF b J < fms.length := h.motLt J hJl
  have hmtG := fms_get hmt
  have hD := h.CD J _ hJ
  obtain ⟨-, sorts, -, hrun⟩ := h.runC J _ hJ
  have hρJ : Sat V (((ppsF (mutMemF b J) ψ).take b.nP).map (·.2.2)).reverse ρp :=
    (h.frame _ _ hmtG ψ ρp).mpr ((h.frame t f hft ψ ρp).mp hρ)
  obtain ⟨hTagJ, hVJ⟩ := h.idxAll t f hft ψ ρp hρ
  have hkT : b.k = fms.length := h.lenFms.symm
  have hTgtJ : ∀ i, i < (ctorsA.getD J default).2 →
      (kindAt (mutKsOf kinds J) i = .recursive ∨ kindAt (mutKsOf kinds J) i = .reflexive) →
      ∃ (ppsT : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
        ppsT.length = b.nP + mutualNIdxOf b.members3 (tgtAt (mutKsOf kinds J) i) ∧
        mp₁.base2.acval (mutualNameOf b.members3 (tgtAt (mutKsOf kinds J) i)) ψ
          = mkLamsC ((fms.getD (mutMemF b J) default).s.eval ψ + 1) ppsT B ∧
        (blkIdss b ppsF ψ)[tgtAt (mutKsOf kinds J) i]? = some ((ppsT.drop b.nP).map (·.2.2)) := by
    intro i _ _
    obtain ⟨-, -, htgt⟩ := h.ksJ J _ hJ
    have htl := htgt i
    have htG := fms_get htl
    obtain ⟨hnm, hni⟩ := h.memT _ _ htG
    obtain ⟨B, hB⟩ := h.leafT htG ψ
    refine ⟨ppsF (tgtAt (mutKsOf kinds J) i) ψ, B, ?_, ?_, blkIdss_getElem? (by rw [hkT]; exact htl)⟩
    · rw [hni]; exact (h.FD _ _ htG).len ψ
    · rw [hnm, hB, h.sEq _ _ htG ψ, h.sEq _ _ hmtG ψ]
  have hC := mutualChainFacts_at hμ mp₁ hrun (h.find _ _ hmtG) (h.propJ hJl) (h.FDm hJl)
    (h.leafT hmtG) hD ψ ρp hρJ hTagJ (blkIdss_getElem? (by rw [hkT]; exact hmt)) hTgtJ
  have hCV := mutualChainValidFacts_at (W := W ψ) hμ mp₁ hrun (h.find _ _ hmtG) (h.propJ hJl)
    (h.FDm hJl) (h.leafT hmtG) hD ψ ρp hρJ hVJ (blkIdss_getElem? (by rw [hkT]; exact hmt))
    (fun i _ _ => by
      obtain ⟨-, -, htgt⟩ := h.ksJ J _ hJ
      exact ⟨_, blkIdss_getElem? (by rw [hkT]; exact htgt i)⟩)
  have hEL : (eissF J ψ).length = mutNFOf ctorsA J := hD.eissLen ψ
  rw [mutTlss_getD hJl, blkFss0_getD hJl, blkEss_getD hJl, blkEiss_getDJ hJl hEL,
    ← h.sEq _ _ hmtG ψ]
  exact ⟨hC, hCV⟩

/-- **The real chains** at every member's parameter frame: the
X-chains' premise, the fixed point's chain grading, the real chains
against the X-source ones, and the chains' validity. -/
theorem chainFull (hμ : μ.verifiedChecks = true) {t : Nat} {f : MutualFormerA}
    (hft : fms[t]? = some f) (ψ : Name → Nat) (ρp : Nat → V)
    (hρ : Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρp) :
    XChainsOk (W ψ) (f₀.s.eval ψ) ρp (auxIds (W ψ) (blkIdss b ppsF ψ)) (blkRss ctorsA kinds)
        (mutTlss ctorsA.length tssF ψ) (blkEiss b ctorsA kinds ppsF W eissF tssF ψ)
        (blkFss0 b ctorsA kinds dsF ψ) (blkEss b ctorsA ppsF W esF ψ) ∧
      FixChainsOkI (W ψ) (f₀.s.eval ψ) ρp (auxIds (W ψ) (blkIdss b ppsF ψ)) 1 (blkRss ctorsA kinds)
        (mutTlss ctorsA.length tssF ψ) (blkEiss b ctorsA kinds ppsF W eissF tssF ψ)
        (blkFss0 b ctorsA kinds dsF ψ) (blkEss b ctorsA ppsF W esF ψ) ∧
      ChainsRealI (auxFamI (W ψ) (f₀.s.eval ψ) ρp (blkIdss b ppsF ψ) (blkRss ctorsA kinds)
          (mutTlss ctorsA.length tssF ψ) (blkEiss b ctorsA kinds ppsF W eissF tssF ψ)
          (blkFss0 b ctorsA kinds dsF ψ) (blkEss b ctorsA ppsF W esF ψ))
        (W ψ) (f₀.s.eval ψ) ρp (auxIds (W ψ) (blkIdss b ppsF ψ)) (blkRss ctorsA kinds)
        (mutTlss ctorsA.length tssF ψ) (blkEiss b ctorsA kinds ppsF W eissF tssF ψ)
        (blkFss0 b ctorsA kinds dsF ψ) (mutFss b.nP ctorsA.length dsF ψ)
        (blkEss b ctorsA ppsF W esF ψ) ∧
      (∀ X, X ∈ˢ lfpFamSpace V (f₀.s.eval ψ) (idxSet (W ψ) ρp (auxIds (W ψ) (blkIdss b ppsF ψ))) →
        ∀ τ, τ ∈ˢ idxSet (W ψ) ρp (auxIds (W ψ) (blkIdss b ppsF ψ)) →
          SumFieldsValid (cons τ (cons X ρp))
            (chainsXI (W ψ) (auxIds (W ψ) (blkIdss b ppsF ψ)) 1 (blkRss ctorsA kinds)
              (mutTlss ctorsA.length tssF ψ) (blkEiss b ctorsA kinds ppsF W eissF tssF ψ)
              (blkFss0 b ctorsA kinds dsF ψ) (blkEss b ctorsA ppsF W esF ψ))) := by
  obtain ⟨hTagJ, hVJ⟩ := h.idxAll t f hft ψ ρp hρ
  have hkT : b.k = fms.length := h.lenFms.symm
  have hFs₀ : ∀ J : Nat, J < ctorsA.length →
      ((blkFss0 b ctorsA kinds dsF ψ).getD J []).length = mutNFOf ctorsA J := by
    intro J hJ
    rw [blkFss0_getD hJ]
    exact shadowFs_length
  have hFsR : ∀ J : Nat, J < ctorsA.length →
      ((mutFss b.nP ctorsA.length dsF ψ).getD J []).length = mutNFOf ctorsA J := by
    intro J hJ
    rw [mutFss_getD hJ, List.length_map, List.length_drop, (h.CD J _ (ctorsA_get hJ)).len ψ]
    show b.nP + mutNFOf ctorsA J - b.nP = mutNFOf ctorsA J
    omega
  have hEsL : ∀ J : Nat, J < ctorsA.length → ((blkEss b ctorsA ppsF W esF ψ).getD J []).length = 1 := by
    intro J hJ; rw [blkEss_getD hJ]; rfl
  refine mutualChainFacts_of (V := V) (nP := b.nP) (n := ctorsA.length)
    (ksF := mutKsOf kinds) (nFs := mutNFOf ctorsA) (rss := blkRss ctorsA kinds)
    (tlss := mutTlss ctorsA.length tssF ψ) (Eiss' := blkEiss b ctorsA kinds ppsF W eissF tssF ψ)
    (Fss₀ := blkFss0 b ctorsA kinds dsF ψ) (Fss := mutFss b.nP ctorsA.length dsF ψ)
    (Ess' := blkEss b ctorsA ppsF W esF ψ) hTagJ hVJ
    (by show ((List.range ctorsA.length).map _).length = _; simp)
    (by show ((List.range ctorsA.length).map _).length = _; simp)
    blkEss_length
    (fun J hJ => blkRss_getD hJ) hFs₀ hFsR hEsL
    (fun J hJ => (h.chainJ hμ hft ψ ρp hρ hJ).1)
    (fun J hJ => (h.chainJ hμ hft ψ ρp hρ hJ).2)
    ?_
  intro J hJ
  have hJg := ctorsA_get hJ
  have hmt : mutMemF b J < fms.length := h.motLt J hJ
  have hmtG := fms_get hmt
  obtain ⟨-, sorts, -, hrun⟩ := h.runC J _ hJg
  have hρJ : Sat V (((ppsF (mutMemF b J) ψ).take b.nP).map (·.2.2)).reverse ρp :=
    (h.frame _ _ hmtG ψ ρp).mpr ((h.frame t f hft ψ ρp).mp hρ)
  have hEL₁ : (eissF J ψ).length = mutNFOf ctorsA J := (h.CD J _ hJg).eissLen ψ
  have hCJ := (h.chainJ hμ hft ψ ρp hρ hJ).1
  rw [mutTlss_getD hJ, blkFss0_getD hJ, blkEss_getD hJ, blkEiss_getDJ hJ hEL₁] at hCJ
  have hAM : ∀ i, i < (ctorsA.getD J default).2 →
      (kindAt (mutKsOf kinds J) i = .recursive ∨ kindAt (mutKsOf kinds J) i = .reflexive) →
      ∃ ppsT : List (Nat × Nat × AnnotTerm),
        ((ppsT.drop b.nP).map (·.2.2)).length = mutualNIdxOf b.members3 (tgtAt (mutKsOf kinds J) i) ∧
        ppsT.length = b.nP + ((ppsT.drop b.nP).map (·.2.2)).length ∧
        (blkIdss b ppsF ψ)[tgtAt (mutKsOf kinds J) i]? = some ((ppsT.drop b.nP).map (·.2.2)) ∧
        Sat V ((ppsT.take b.nP).map (·.2.2)).reverse ρp ∧
        mp₁.base2.acval (mutualNameOf b.members3 (tgtAt (mutKsOf kinds J) i)) ψ
          = mutualTyAVI (W ψ) ((fms.getD (mutMemF b J) default).s.eval ψ) ppsT
              ((ppsT.drop b.nP).map (·.2.2)).length (blkIdss b ppsF ψ) (blkRss ctorsA kinds)
              (mutTlss ctorsA.length tssF ψ) (blkEiss b ctorsA kinds ppsF W eissF tssF ψ)
              (blkFss0 b ctorsA kinds dsF ψ) (blkEss b ctorsA ppsF W esF ψ)
              (tgtAt (mutKsOf kinds J) i) := by
    intro i _ _
    obtain ⟨-, -, htgt⟩ := h.ksJ J _ hJg
    have htl := htgt i
    have htG := fms_get htl
    obtain ⟨hnm, hni⟩ := h.memT _ _ htG
    refine ⟨ppsF (tgtAt (mutKsOf kinds J) i) ψ, ?_, ?_, blkIdss_getElem? (by rw [hkT]; exact htl),
      ?_, ?_⟩
    · rw [hni, List.length_map, List.length_drop, (h.FD _ _ htG).len ψ]
      omega
    · rw [List.length_map, List.length_drop, (h.FD _ _ htG).len ψ]
      omega
    · exact (h.frame _ _ htG ψ ρp).mpr ((h.frame t f hft ψ ρp).mp hρ)
    · have hlen : (((ppsF (tgtAt (mutKsOf kinds J) i) ψ).drop b.nP).map (·.2.2)).length
          = (fms.getD (tgtAt (mutKsOf kinds J) i) default).nIdx := by
        rw [List.length_map, List.length_drop, (h.FD _ _ htG).len ψ]
        exact Nat.add_sub_cancel_left _ _
      rw [hnm, h.leaf_repr htG ψ, h.sEq _ _ hmtG ψ, hlen]
  have hrealJ := mutualChainReal_at (W := W ψ) (mem := mutMemF b J) (Idss := blkIdss b ppsF ψ)
    (rss := blkRss ctorsA kinds) (tlss := mutTlss ctorsA.length tssF ψ)
    (Eiss' := blkEiss b ctorsA kinds ppsF W eissF tssF ψ) (Fss₀ := blkFss0 b ctorsA kinds dsF ψ)
    (Ess' := blkEss b ctorsA ppsF W esF ψ)
    hμ mp₁ hrun (h.find _ _ hmtG) (h.propJ hJ) (h.FDm hJ) (h.leafT hmtG) (h.CD J _ hJg) ψ ρp hρJ
    hTagJ (by rw [h.sEq _ _ hmtG ψ]; exact hCJ) hAM
    (by rw [h.sEq _ _ hmtG ψ]; exact ((h.stageOk t f hft).tagged.2 ψ ρp hρ).2.2.1)
  rw [blkRss_getD hJ, mutTlss_getD hJ, blkFss0_getD hJ, mutFss_getD hJ, blkEiss_getDJ hJ hEL₁]
  rw [h.sEq _ _ hmtG ψ] at hrealJ
  exact hrealJ

/-- **The constructors' frames** at the member leaves: a constructor's
parameter frame is its member's, and at it the fields are graded,
valid, bounded off `Prop`, and the index expressions fit the member's
telescope at every field spine. -/
theorem framesJ (hμ : μ.verifiedChecks = true) {J : Nat} (hJ : J < ctorsA.length) :
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((ppsF (mutMemF b J) ψ).take b.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((dsF J ψ).take b.nP).map (·.2.2)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((dsF J ψ).take b.nP).map (·.2.2)).reverse ρ →
        FieldsOkB ((fms.getD (mutMemF b J) default).s.eval ψ) ρ (((dsF J ψ).drop b.nP).map (·.2.2)) ∧
        FieldsValid ρ (((dsF J ψ).drop b.nP).map (·.2.2)) ∧
        ((Level.isEquiv f₀.s Level.zero == some true) = false →
          FieldsBound ((fms.getD (mutMemF b J) default).s.eval ψ) ρ
            (((dsF J ψ).drop b.nP).map (·.2.2))) ∧
        (∀ bs : List V, SpineFit ρ (((dsF J ψ).drop b.nP).map (·.2.2)) bs →
          (∀ E ∈ esF J ψ, WellDenotedV V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsF (mutMemF b J) ψ).drop b.nP).map (·.2.2))
            (idxValsAt ρ (esF J ψ) bs))) := by
  have hJg := ctorsA_get hJ
  have hmtG := fms_get (h.motLt J hJ)
  obtain ⟨-, sorts, -, hrun⟩ := h.runC J _ hJg
  obtain ⟨h1, h2, -⟩ := mutualCtorFrames hμ mp₁ hrun (h.find _ _ hmtG) (h.propJ hJ) (h.FDm hJ)
    (h.CD J _ hJg).toCtorDataI (h.leafT hmtG)
  exact ⟨h1, h2⟩

/-- **The constructor's fibre fold**: its residual at a fitting field
spine is the auxiliary family's fibre at the tagged index tuple. -/
theorem fold (hμ : μ.verifiedChecks = true) {J : Nat} {cA : ConstantVal × Nat}
    (hJ : ctorsA[J]? = some cA) (ψ : Name → Nat) (ρ : Nat → V)
    (hρ : Sat V (((ppsF (mutMemF b J) ψ).take b.nP).map (·.2.2)).reverse ρ)
    (bs : List V) (hsp : SpineFit ρ (((dsF J ψ).drop b.nP).map (·.2.2)) bs) :
    interp V (consList bs ρ)
        (AnnotTerm.mkAppN (mp₁.base2.acval (fms.getD (mutMemF b J) default).cvTa.name ψ)
          (paramBvars b.nP cA.2 ++ esF J ψ))
      = sumSet (f₀.s.eval ψ) (sumFibre (f₀.s.eval ψ)
          (consList (idxValsAt ρ
            [tagTupleAV (W ψ) (mutMemF b J) cA.2 (blkIdss b ppsF ψ) (esF J ψ)] bs) ρ)
          (rChains 1 1 (mutFss b.nP ctorsA.length dsF ψ) (blkEss b ctorsA ppsF W esF ψ))) := by
  have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  have hmt : mutMemF b J < fms.length := h.motLt J hJl
  have hmtG := fms_get hmt
  have hkT : b.k = fms.length := h.lenFms.symm
  have hlenM : (ppsF (mutMemF b J) ψ).length
      = b.nP + (((ppsF (mutMemF b J) ψ).drop b.nP).map (·.2.2)).length := by
    rw [List.length_map, List.length_drop, (h.FD _ _ hmtG).len ψ]
    omega
  have hIdsM : (blkIdss b ppsF ψ)[mutMemF b J]?
      = some (((ppsF (mutMemF b J) ψ).drop b.nP).map (·.2.2)) :=
    blkIdss_getElem? (by rw [hkT]; exact hmt)
  have hlenbs : bs.length = cA.2 := by
    rw [hsp.length_eq, List.length_map, List.length_drop, (h.CD J _ hJ).len ψ]
    omega
  obtain ⟨hTagJ, -⟩ := h.idxAll _ _ hmtG ψ ρ hρ
  have hfr := (h.framesJ hμ hJl).2 ψ ρ ((h.framesJ hμ hJl).1 ψ ρ |>.mp hρ)
  obtain ⟨hEok, hfit⟩ := hfr.2.2.2 bs hsp
  have hnI : (((ppsF (mutMemF b J) ψ).drop b.nP).map (·.2.2)).length
      = (fms.getD (mutMemF b J) default).nIdx := by
    rw [List.length_map, List.length_drop, (h.FD _ _ hmtG).len ψ]
    exact Nat.add_sub_cancel_left _ _
  have hcl : Term.bvarsBelow 0 (mp₁.base2.acval (fms.getD (mutMemF b J) default).cvTa.name ψ).erase :=
    mp₁.base2.cval_closedL _ ψ
  have hA : ∀ σ : Nat → V, interp V σ (mp₁.base2.acval (fms.getD (mutMemF b J) default).cvTa.name ψ)
      = interp V (fun j => ρ (j + b.nP))
          (mutualTyAVI (W ψ) (f₀.s.eval ψ) (ppsF (mutMemF b J) ψ)
            (((ppsF (mutMemF b J) ψ).drop b.nP).map (·.2.2)).length (blkIdss b ppsF ψ)
            (blkRss ctorsA kinds) (mutTlss ctorsA.length tssF ψ)
            (blkEiss b ctorsA kinds ppsF W eissF tssF ψ) (blkFss0 b ctorsA kinds dsF ψ)
            (blkEss b ctorsA ppsF W esF ψ) (mutMemF b J)) := by
    intro σ
    rw [hnI, ← h.leaf_repr hmtG ψ]
    exact interp_closed V hcl σ _
  have hf := mutualCtorFold (V := V) (nF := cA.2) (mem := mutMemF b J)
    (Fss := mutFss b.nP ctorsA.length dsF ψ)
    hlenM hIdsM hTagJ (h.chainFull hμ hmtG ψ ρ hρ).1 (h.chainFull hμ hmtG ψ ρ hρ).2.2.1 hρ hA
    hlenbs (fun E hE => (hEok E hE).1) hfit
  rw [paramBvars_eq_paramBvarsAt]
  exact hf

/-- **The real chains are graded and valid** at every constructor's
parameter frame. -/
theorem fssOkP (hμ : μ.verifiedChecks = true) {J : Nat} (hJl : J < ctorsA.length)
    (ψ : Name → Nat) (ρ : Nat → V) (hρ : Sat V (((dsF J ψ).take b.nP).map (·.2.2)).reverse ρ) :
    SumFieldsOkB (f₀.s.eval ψ) ρ (mutFss b.nP ctorsA.length dsF ψ) ∧
      SumFieldsValid ρ (mutFss b.nP ctorsA.length dsF ψ) := by
  have hρM : Sat V (((ppsF (mutMemF b J) ψ).take b.nP).map (·.2.2)).reverse ρ :=
    ((h.framesJ hμ hJl).1 ψ ρ).mpr hρ
  have hall : ∀ J' : Nat, J' < ctorsA.length →
      FieldsOkB (f₀.s.eval ψ) ρ (((dsF J' ψ).drop b.nP).map (·.2.2)) ∧
        FieldsValid ρ (((dsF J' ψ).drop b.nP).map (·.2.2)) := by
    intro J' hJ'
    have hρM' : Sat V (((ppsF (mutMemF b J') ψ).take b.nP).map (·.2.2)).reverse ρ :=
      (h.frame _ _ (fms_get (h.motLt J' hJ')) ψ ρ).mpr
        ((h.frame _ _ (fms_get (h.motLt J hJl)) ψ ρ).mp hρM)
    have hfr := (h.framesJ hμ hJ').2 ψ ρ (((h.framesJ hμ hJ').1 ψ ρ).mp hρM')
    rw [h.sEq _ _ (fms_get (h.motLt J' hJ')) ψ] at hfr
    exact ⟨hfr.1, hfr.2.1⟩
  refine ⟨fun Fs hFs => ?_, fun Fs hFs => ?_⟩
  · obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
      (fun J => ((dsF J ψ).drop b.nP).map (·.2.2)) from hFs)
    exact (hall J' (List.mem_range.mp hJ')).1
  · obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
      (fun J => ((dsF J ψ).drop b.nP).map (·.2.2)) from hFs)
    exact (hall J' (List.mem_range.mp hJ')).2

end MutualFormersFacts

/-! ## The constructors' stage -/

/-- **The constructors' stage of the mutual install** (stage 3's
conses): the constructors consed in block order with their sum-route
leaves at the tagged towers, the members' leaves untouched, the
constructors' data crossed. -/
theorem mutualCtorsStage (hμ : μ.verifiedChecks = true) (hE : ConLeche.EtaFamiliesClosed env)
    (h0 : b.blockNames.Nodup) :
    ∃ mp₂ : EnvModelM V μ (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)),
      ConLeche.EtaFamiliesClosed
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) ∧
      (∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
        MutualCtorFactsAt mp₂.base2 (ConLeche.consMutualFormers fms env) b.members3 b.lps b.nP
          (Level.isEquiv f₀.s Level.zero == some true) b.large
          (fun t => (fms.getD t default).cvTa.name) (fun t => (fms.getD t default).nIdx)
          (mutMemF b) (fun J => (fms.getD (mutMemF b J) default).s) idxF dsF esF srcsF
          (mutKsOf kinds) fvsPF xFvsF xrestF eissF tssF J cA ∧
        (∀ e ∈ idxF J, e.constsResolve
          (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) = true) ∧
        ∀ ψ : Name → Nat, mp₂.base2.acval cA.1.name ψ
          = sumMkAV (f₀.s.eval ψ) J (dsF J ψ) (((dsF J ψ).drop b.nP).map (·.2.2))
              (uChains (mutFss b.nP ctorsA.length dsF ψ))) ∧
      (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
        mp₂.base2.acval f.cvTa.name = mp₁.base2.acval f.cvTa.name) ∧
      (∀ n : Name, (∀ cA ∈ ctorsA, n ≠ cA.1.name) → mp₂.base2.acval n = mp₁.base2.acval n) := by
  have hndC : (b.ctors.map (·.cv.name)).Nodup := by
    have h0' := h0
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp (List.nodup_append.mp h0').1).2.1
  have hndA : (ctorsA.map (·.1.name)).Nodup := by rw [h.namesC]; exact hndC
  have hmono₁ : ∀ e : Expr, Expr.constsResolve env e = true →
      Expr.constsResolve (ConLeche.consMutualFormers fms env) e = true :=
    fun e he => constsResolve_consMutualFormers he
  have hE₁ : ConLeche.EtaFamiliesClosed (ConLeche.consMutualFormers fms env) :=
    ConLeche.Semantics.EtaFamiliesClosed.ofFreshExt hE
      (ConLeche.Semantics.consMutualFormers_freshExt fun f hf => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem hf
        exact h.fresh t f ht)
  have hCDparams₁ : ∀ J : Nat, J < ctorsA.length → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ b.lps, ψ₁ q = ψ₂ q) → dsF J ψ₁ = dsF J ψ₂ :=
    fun J hJ ψ₁ ψ₂ hφ => (h.CDpar J hJ ψ₁ ψ₂ hφ).1
  have hFssOkP : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V (((dsF J ψ).take b.nP).map (·.2.2)).reverse ρ →
        SumFieldsOkB (f₀.s.eval ψ) ρ (mutFss b.nP ctorsA.length dsF ψ) ∧
          SumFieldsValid ρ (mutFss b.nP ctorsA.length dsF ψ) := by
    intro J cA hJ ψ ρ hρ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    have hρM : Sat V (((ppsF (mutMemF b J) ψ).take b.nP).map (·.2.2)).reverse ρ :=
      ((h.framesJ hμ hJl).1 ψ ρ).mpr hρ
    have hall : ∀ J' : Nat, J' < ctorsA.length →
        FieldsOkB (f₀.s.eval ψ) ρ (((dsF J' ψ).drop b.nP).map (·.2.2)) ∧
          FieldsValid ρ (((dsF J' ψ).drop b.nP).map (·.2.2)) := by
      intro J' hJ'
      have hρM' : Sat V (((ppsF (mutMemF b J') ψ).take b.nP).map (·.2.2)).reverse ρ :=
        (h.frame _ _ (fms_get (h.motLt J' hJ')) ψ ρ).mpr
          ((h.frame _ _ (fms_get (h.motLt J hJl)) ψ ρ).mp hρM)
      have hfr := (h.framesJ hμ hJ').2 ψ ρ (((h.framesJ hμ hJ').1 ψ ρ).mp hρM')
      rw [h.sEq _ _ (fms_get (h.motLt J' hJ')) ψ] at hfr
      exact ⟨hfr.1, hfr.2.1⟩
    refine ⟨fun Fs hFs => ?_, fun Fs hFs => ?_⟩
    · obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
        (fun J => ((dsF J ψ).drop b.nP).map (·.2.2)) from hFs)
      exact (hall J' (List.mem_range.mp hJ')).1
    · obtain ⟨J', hJ', rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
        (fun J => ((dsF J ψ).drop b.nP).map (·.2.2)) from hFs)
      exact (hall J' (List.mem_range.mp hJ')).2
  have hfoundC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      CtorMembersFound (ConLeche.consMutualFormers fms env) b.members3
        (fun t => (fms.getD t default).cvTa.name) (mutMemF b) (mutKsOf kinds) J cA.2 := by
    intro J cA hJ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    refine ⟨by rw [h.find _ _ (fms_get (h.motLt J hJl))]; rfl, fun i _ _ => ?_⟩
    have htl := (h.ksJ J cA hJ).2.2 i
    rw [(h.memT _ _ (fms_get htl)).1, h.find _ _ (fms_get htl)]
    rfl
  have hpendC : MutualPendingAt mp₁.base2 (ConLeche.consMutualFormers fms env)
      b.members3 b.lps b.nP (Level.isEquiv f₀.s Level.zero == some true) b.large
      (fun t => (fms.getD t default).cvTa.name) (fun t => (fms.getD t default).nIdx) (mutMemF b)
      (fun J => (fms.getD (mutMemF b J) default).s) idxF dsF esF srcsF (mutKsOf kinds) fvsPF xFvsF
      xrestF eissF tssF ctorsA 0 := by
    intro J cA _ hJ
    refine ⟨h.freshC cA (List.mem_of_getElem? hJ), h.resC J cA hJ, ?_, h.lpsC J cA hJ, ?_⟩
    · intro e he
      refine hmono₁ e ?_
      have hr := (h.CD J cA hJ).opened.residRes
      rw [← (h.CD J cA hJ).idxEq] at hr
      exact hr e he
    · exact MutualCtorDataI.monoEnv₀ hmono₁ (h.CD J cA hJ)
  obtain ⟨mp₂, hE₂, -, hleaf₂, hcons₂, -, hleafC₂, hag₂⟩ :=
    stageMutualCtors (V := V) (μ := μ) (F := F)
      (memberNames := b.memberNames) (members := b.members3)
      (lps := b.lps) (nP := b.nP)
      (isProp := Level.isEquiv f₀.s Level.zero == some true) (large := b.large)
      (env₀ := ConLeche.consMutualFormers fms env)
      (Tname := fun t => (fms.getD t default).cvTa.name)
      (nIdxOf := fun t => (fms.getD t default).nIdx) (mots := mutMemF b)
      (resSortOf := fun J => (fms.getD (mutMemF b J) default).s)
      (cvTaOf := fun t => (fms.getD t default).cvTa)
      (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF) (ksF := mutKsOf kinds)
      (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF)
      (ctorsA := ctorsA) (W := W) (w := fun ψ => f₀.s.eval ψ) (Idss := blkIdss b ppsF)
      (FssR := fun ψ => mutFss b.nP ctorsA.length dsF ψ) (Ess' := blkEss b ctorsA ppsF W esF)
      (ppsOf := ppsF)
      (leafT := fun J ψ => mp₁.base2.acval (fms.getD (mutMemF b J) default).cvTa.name ψ)
      (Inv := fun {_} _ => True) mp₁ hndA
      (fun J cA hJ => by
        obtain ⟨-, sorts, -, hrun⟩ := h.runC J cA hJ
        exact ⟨_, sorts, hrun⟩)
      (fun J cA hJ ψ => h.sEq _ _ (fms_get (h.motLt J (List.getElem?_eq_some_iff.mp hJ).1)) ψ)
      (fun J cA hJ ψ ρ hρ bs hsp => h.fold hμ hJ ψ ρ hρ bs hsp)
      (fun J cA hJ ψ => by
        have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
        show ((List.range ctorsA.length).map _)[J]? = _
        rw [List.getElem?_map, List.getElem?_range hJl]
        rfl)
      (fun J cA hJ ψ => by
        have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
        rw [List.getElem?_eq_getElem (show J < (blkEss b ctorsA ppsF W esF ψ).length from
          by rw [blkEss_length]; exact hJl)]
        have hgd := blkEss_getD (b := b) (ppsF := ppsF) (W := W) (esF := esF) (ψ := ψ) hJl
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show J < (blkEss b ctorsA ppsF W esF ψ).length from
          by rw [blkEss_length]; exact hJl)] at hgd
        rw [Option.getD_some] at hgd
        rw [hgd, mutNFOf_eq hJ])
      (fun ψ₁ ψ₂ hφ => ⟨((h.FD₀ 0 f₀ h.first).params ψ₁ ψ₂
          (by rw [h.lps 0 f₀ h.first]; exact hφ)).2,
        by
          show mutFss _ _ _ _ = mutFss _ _ _ _
          unfold mutFss
          exact List.map_congr_left (fun J hJ => by
            rw [hCDparams₁ J (List.mem_range.mp hJ) ψ₁ ψ₂ hφ])⟩)
      (fun ψ Fs hFs => by
        obtain ⟨J, hJ, rfl⟩ := List.mem_map.mp (show Fs ∈ (List.range ctorsA.length).map
          (fun J => ((dsF J ψ).drop b.nP).map (·.2.2)) from hFs)
        have hh := (DomsBelow.drop b.nP
          ((h.CD J _ (ctorsA_get (List.mem_range.mp hJ))).below ψ)).fields
        rwa [Nat.zero_add] at hh)
      (fun J cA hJ => (h.framesJ hμ (List.getElem?_eq_some_iff.mp hJ).1).1)
      hFssOkP (fun _ _ _ _ _ _ _ _ => trivial) hE₁ hfoundC (fun _ _ _ _ => rfl) hpendC trivial
  refine ⟨mp₂, hE₂, fun J cA hJ => ?_, fun t f hft => ?_, hag₂⟩
  · have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    obtain ⟨hfacts, hidx, hleaf⟩ := hcons₂ J cA hJl hJ
    exact ⟨hfacts, hidx, hleaf⟩
  · -- the member's name is no constructor's
    funext ψ
    have hne : ∀ cA ∈ ctorsA, f.cvTa.name ≠ cA.1.name := by
      intro cA hcA heq
      have hmemM : f.cvTa.name ∈ b.memberNames := by
        rw [← h.names]; exact List.mem_map_of_mem (List.mem_of_getElem? hft)
      have hmemC : cA.1.name ∈ b.ctors.map (·.cv.name) := by
        rw [← h.namesC]; exact List.mem_map_of_mem hcA
      have h0' := h0
      unfold ConLeche.MutualBlock.blockNames at h0'
      have hdisj := (List.nodup_append.mp (List.nodup_append.mp h0').1).2.2
      exact hdisj _ hmemM _ hmemC heq
    exact congrFun (hag₂ f.cvTa.name hne) ψ

end Facts

/-! ## Kit for the datum -/

/-- A spine fitting one telescope fits another with the same frames
and the same length. -/
theorem spineFit_of_frames {Ds₁ Ds₂ : List AnnotTerm} (hlen : Ds₁.length = Ds₂.length)
    (hiff : ∀ ρ : Nat → V, Sat V Ds₁.reverse ρ ↔ Sat V Ds₂.reverse ρ) {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ Ds₁ as) : SpineFit ρ Ds₂ as := by
  have h1 := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp
  rw [List.append_nil] at h1
  have h2 := (hiff _).mp h1
  have h3 := spineFit_of_sat (Δ₀ := []) (by rw [List.append_nil]; exact h2)
  have hl : as.length = Ds₂.length := by rw [hsp.length_eq, hlen]
  rw [← hl] at h3
  have hfr : (fun j => consList as ρ (j + as.length)) = ρ := by
    funext j; exact consList_apply_add as ρ j
  rw [hfr] at h3
  have hval : (List.range as.length).reverse.map (consList as ρ) = as := by
    have := consList_range_reverse as.length (consList as ρ)
    rw [hfr] at this
    exact consList_inj_of_length (by simp) this
  rw [hval] at h3
  exact h3
where
  consList_inj_of_length {as bs : List V} {ρ : Nat → V} (hl : as.length = bs.length)
      (h : consList as ρ = consList bs ρ) : as = bs := by
    apply List.ext_getElem hl
    intro i hi₁ hi₂
    have hk : as.length - 1 - i < as.length := by omega
    have := congrFun h (as.length - 1 - i)
    rw [consList_getD_lt as ρ _ hk, consList_getD_lt bs ρ _ (by omega),
      show as.length - 1 - (as.length - 1 - i) = i from by omega,
      show bs.length - 1 - (as.length - 1 - i) = i from by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi₁, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi₂] at this
    exact this

/-- **`FitsFrom` congruence**: along two domain lists of one length,
agreeing at the non-recursive positions, with the recursive flags and
slots agreeing along the way. -/
theorem fitsFrom_congr {rs rs' : List Bool} {slot slot' : Nat → (Nat → V) → V} :
    ∀ {i : Nat} {ρ : Nat → V} {Fs Fs' : List AnnotTerm} {fs : List V},
      Fs.length = Fs'.length →
      (∀ l, l < Fs.length → rs.getD (i + l) false = rs'.getD (i + l) false) →
      (∀ l, l < Fs.length → rs.getD (i + l) false = true →
        ∀ ρ' : Nat → V, slot (i + l) ρ' = slot' (i + l) ρ') →
      (∀ l, l < Fs.length → rs.getD (i + l) false = false →
        Fs.getD l default = Fs'.getD l default) →
      (FitsFrom rs slot i ρ Fs fs ↔ FitsFrom rs' slot' i ρ Fs' fs)
  | _, _, [], [], [], _, _, _, _ => Iff.rfl
  | _, _, [], [], _ :: _, _, _, _, _ => Iff.rfl
  | _, _, [], _ :: _, _, hlen, _, _, _ => by simp at hlen
  | _, _, _ :: _, [], _, hlen, _, _, _ => by simp at hlen
  | _, _, _ :: _, _ :: _, [], _, _, _, _ => Iff.rfl
  | i, ρ, F :: Fs, F' :: Fs', a :: fs, hlen, hrs, hslot, hF => by
    show (a ∈ˢ (if rs.getD i false then slot i ρ else interp V ρ F) ∧
        FitsFrom rs slot (i + 1) (cons a ρ) Fs fs) ↔
      (a ∈ˢ (if rs'.getD i false then slot' i ρ else interp V ρ F') ∧
        FitsFrom rs' slot' (i + 1) (cons a ρ) Fs' fs)
    have h0 : rs.getD i false = rs'.getD i false := by
      have := hrs 0 (by simp); rwa [Nat.add_zero] at this
    have hhead : (if rs.getD i false then slot i ρ else interp V ρ F)
        = (if rs'.getD i false then slot' i ρ else interp V ρ F') := by
      by_cases hri : rs.getD i false = true
      · rw [if_pos hri, if_pos (by rw [← h0]; exact hri)]
        have := hslot 0 (by simp) (by rwa [Nat.add_zero]) ρ
        rwa [Nat.add_zero] at this
      · have hri' : rs.getD i false = false := by simpa using hri
        rw [if_neg (by rw [hri']; exact Bool.false_ne_true),
          if_neg (by rw [← h0, hri']; exact Bool.false_ne_true)]
        have := hF 0 (by simp) (by rwa [Nat.add_zero])
        simp only [List.getD_cons_zero] at this
        rw [this]
    rw [hhead]
    refine and_congr_right fun _ => ?_
    refine fitsFrom_congr (by simpa using hlen) (fun l hl => ?_) (fun l hl hr => ?_) (fun l hl hr => ?_)
    · have := hrs (l + 1) (by simp; omega)
      rwa [show i + (l + 1) = i + 1 + l from by omega] at this
    · have := hslot (l + 1) (by simp; omega) (by rwa [show i + (l + 1) = i + 1 + l from by omega])
      rwa [show i + (l + 1) = i + 1 + l from by omega] at this
    · have := hF (l + 1) (by simp; omega) (by rwa [show i + (l + 1) = i + 1 + l from by omega])
      simpa using this

/-! ## The datum of the run -/

/-- **The uniform datum of the run**: `BlockRepData.ofMutual` at the
formers' stage's data, keyed per member and member-local constructor
through the block's own constructor positions (`ownCtors`), the global
lists in the checked constructors' order. -/
@[expose] noncomputable def mutualDatum (b : MutualBlock) (fms : List MutualFormerA) (f₀ : MutualFormerA)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List (RecFieldKind × Nat))) (env : Env)
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) : BlockRepData V :=
  BlockRepData.ofMutual b.nP b.k f₀.s (Level.isEquiv f₀.s .zero == some true) b.large env
    (fms.map (·.cvTa.name)) (fms.map (·.nIdx)) ppsF W
    (fun t => (b.ownCtors t).map fun q => ctorsA.getD q.1 default)
    (fun mm j => idxF (b.ownOffset mm + j)) (fun mm j => dsF (b.ownOffset mm + j))
    (fun mm j => esF (b.ownOffset mm + j)) (fun mm j => srcsF (b.ownOffset mm + j))
    (fun mm j => kindsOf (mutKsOf kinds (b.ownOffset mm + j)))
    (fun mm j i => tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i)
    (fun mm j => fvsPF (b.ownOffset mm + j)) (fun mm j => xFvsF (b.ownOffset mm + j))
    (fun mm j => xrestF (b.ownOffset mm + j)) (fun mm j => eissF (b.ownOffset mm + j))
    (fun mm j => tssF (b.ownOffset mm + j))
    (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
    (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
    (fun ψ => mutTlss ctorsA.length tssF ψ) (fun ψ => mutEiss0 ctorsA.length eissF ψ)
    (fun ψ => blkFss0 b ctorsA kinds dsF ψ) (fun ψ => mutEss0 ctorsA.length esF ψ)

section Datum

variable {b : MutualBlock} {fms : List MutualFormerA} {f₀ : MutualFormerA}
  {ctorsA : List (ConstantVal × Nat)} {kinds : List (List (RecFieldKind × Nat))}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}

local notation "D" => (mutualDatum (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF
  fvsPF xFvsF xrestF eissF tssF)

/-- The datum's minor index is the block's own offset. -/
theorem mutualDatum_minorIdx (mm j : Nat) : (D).minorIdx mm j = b.ownOffset mm + j := by
  show blockMinorIdx _ mm j = _
  unfold blockMinorIdx ConLeche.MutualBlock.ownOffset
  congr 2
  exact List.map_congr_left fun t _ => List.length_map _

/-- A member's constructor is the checked constructor at the block's position. -/
theorem mutualDatum_ctorsM_get (hg : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hlenA : ctorsA.length = b.ctors.length) {mm j : Nat} {cA : ConstantVal × Nat}
    (hj : ((D).ctorsM mm)[j]? = some cA) :
    b.ownOffset mm + j < ctorsA.length ∧ ctorsA[b.ownOffset mm + j]? = some cA ∧
      mutMemF b (b.ownOffset mm + j) = mm := by
  change ((b.ownCtors mm).map fun q => ctorsA.getD q.1 default)[j]? = some cA at hj
  rw [List.getElem?_map] at hj
  obtain ⟨⟨J, c⟩, hq, rfl⟩ := Option.map_eq_some_iff.mp hj
  have hJ := ownCtors_getElem?_idx hg hq
  obtain ⟨hc, hmem⟩ := ownCtors_getElem?_ctors hq
  subst hJ
  have hlt : b.ownOffset mm + j < ctorsA.length := by
    rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hc).1
  refine ⟨hlt, ctorsA_get hlt, ?_⟩
  show (b.ctors.getD (b.ownOffset mm + j) default).member = mm
  rw [List.getD_eq_getElem?_getD, hc]
  exact hmem

/-- A checked constructor is its member's, at the block's position. -/
theorem mutualDatum_ofCtor (hg : ConLeche.mutualCtorsGrouped b.ctors = true)
    (h2 : b.ctors.all (fun c => c.member < b.k) = true) (hlenA : ctorsA.length = b.ctors.length)
    {J : Nat} (hJ : J < ctorsA.length) :
    mutMemF b J < b.k ∧ b.ownOffset (mutMemF b J) ≤ J ∧
      ((D).ctorsM (mutMemF b J))[J - b.ownOffset (mutMemF b J)]? = some (ctorsA.getD J default) := by
  have hJb : J < b.ctors.length := by rw [← hlenA]; exact hJ
  have hc : b.ctors[J]? = some (b.ctors.getD J default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJb]; rfl
  have hmemF : mutMemF b J = (b.ctors.getD J default).member := rfl
  have hmem : mutMemF b J < b.k := by
    have := List.all_eq_true.mp h2 _ (List.mem_of_getElem? hc)
    rw [hmemF]
    simpa using this
  obtain ⟨hle, hown⟩ := ownCtors_of_ctors hg hc
  rw [← hmemF] at hle hown
  refine ⟨hmem, hle, ?_⟩
  change ((b.ownCtors (mutMemF b J)).map fun q => ctorsA.getD q.1 default)[J - b.ownOffset (mutMemF b J)]? = _
  rw [List.getElem?_map, hown]
  rfl

/-- The datum's member names are the members'. -/
theorem mutualDatum_memberName {t : Nat} {f : MutualFormerA} (hft : fms[t]? = some f) :
    (D).memberName t = f.cvTa.name := by
  show (fms.map (·.cvTa.name)).getD t .anonymous = f.cvTa.name
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hft]
  rfl

/-- The datum's index counts are the members'. -/
theorem mutualDatum_nIdxAt {t : Nat} {f : MutualFormerA} (hft : fms[t]? = some f) :
    (D).nIdxAt t = f.nIdx := by
  show (fms.map (·.nIdx)).getD t 0 = f.nIdx
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hft]
  rfl

end Datum

/-- `ConstsBound` travels to an environment finding everything the
first does. -/
theorem constsBound_mono {env₀ env' : Env} (hF : FindPreserved env₀ env') (e : Expr)
    (h : ConstsBound env₀ e) : ConstsBound env' e := by
  induction e with
  | bvar i => simp
  | sort u => simp
  | lit l => simp
  | const n us =>
    rw [constsBound_const] at h ⊢
    cases hn : env₀.find? n with
    | none => rw [hn] at h; exact nomatch h
    | some ci => rw [hF hn]; rfl
  | fvar idx ty ih =>
    rw [constsBound_fvar] at h ⊢
    exact ih h
  | app f a ihf iha =>
    rw [constsBound_app] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b mb ihty ihb =>
    rw [constsBound_lam] at h ⊢
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b mb ihty ihb =>
    rw [constsBound_forallE] at h ⊢
    exact ⟨ihty h.1, ihb h.2⟩
  | letE ty v b ihty ihv ihb =>
    rw [constsBound_letE] at h ⊢
    exact ⟨ihty h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i e ihe =>
    rw [constsBound_proj] at h ⊢
    exact ihe h

/-! ## The datum at the constructors' environment -/

/-- The constructor's data at another resolution witness (the opened
form's guard is model-free). -/
theorem MutualCtorDataI.withOpened {m : EnvModel V env} {env₀ env₀' : Env}
    {members : List (Name × Nat × Nat)} {T : Name} {lps : List Name} {cvC : ConstantVal}
    {nP nF nIdx : Nat} {resSort : Level} {isProp large : Bool} {idxArgs : List Expr}
    {ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {Es : (Name → Nat) → List AnnotTerm}
    {srcs : List (Option Nat)} {ks : List (RecFieldKind × Nat)} {fvsP xFvs : List Expr}
    {xrest : Expr} {Eiss : (Name → Nat) → List (List AnnotTerm)}
    {tss : (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
    (h : MutualCtorDataI m env₀ members T lps cvC nP nF nIdx resSort isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss)
    (ho : MutualOpened env₀' members lps nP nF ks fvsP xFvs xrest) :
    MutualCtorDataI m env₀' members T lps cvC nP nF nIdx resSort isProp large idxArgs
      ds Es srcs ks fvsP xFvs xrest Eiss tss :=
  { h.toCtorDataI with
    opened := ho, opens := h.opens, ksLen := h.ksLen, xLen := h.xLen, pLen := h.pLen
    xIdx := h.xIdx, pIdx := h.pIdx, idxEq := h.idxEq, domRead := h.domRead, eissLen := h.eissLen
    eisRead := h.eisRead, eisLen := h.eisLen, recEntry := h.recEntry, eissParams := h.eissParams
    eissBelow := h.eissBelow, ordNone := h.ordNone, tssLen := h.tssLen, tssNone := h.tssNone
    tssBits := h.tssBits, tssPiBits := h.tssPiBits, tssBelow := h.tssBelow
    tssParams := h.tssParams, reflOpen := h.reflOpen, eisLenRefl := h.eisLenRefl
    reflEntry := h.reflEntry }

section Reps

variable {F : Nat} {mp : EnvModelM V μ env} {b : MutualBlock} {fms : List MutualFormerA}
  {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
  {kinds : List (List (RecFieldKind × Nat))}
  {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}

local notation "D" => (mutualDatum (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF
  fvsPF xFvsF xrestF eissF tssF)

/-- **The datum at the constructors' environment**: `BlockRep` at
every member, the members and constructors typed. -/
theorem blockReps_of (hμ : μ.verifiedChecks = true) (h0 : b.blockNames.Nodup)
    (h2 : b.ctors.all (fun c => c.member < b.k) = true)
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (h : MutualFormersFacts V F mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF
      xFvsF xrestF eissF tssF)
    (mp₂ : EnvModelM V μ (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)))
    (hcons : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      MutualCtorFactsAt mp₂.base2 (ConLeche.consMutualFormers fms env) b.members3 b.lps b.nP
        (Level.isEquiv f₀.s Level.zero == some true) b.large
        (fun t => (fms.getD t default).cvTa.name) (fun t => (fms.getD t default).nIdx)
        (mutMemF b) (fun J => (fms.getD (mutMemF b J) default).s) idxF dsF esF srcsF
        (mutKsOf kinds) fvsPF xFvsF xrestF eissF tssF J cA ∧
      (∀ e ∈ idxF J, e.constsResolve
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) = true) ∧
      ∀ ψ : Name → Nat, mp₂.base2.acval cA.1.name ψ
        = sumMkAV (f₀.s.eval ψ) J (dsF J ψ) (((dsF J ψ).drop b.nP).map (·.2.2))
            (uChains (mutFss b.nP ctorsA.length dsF ψ)))
    (hleafM : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      mp₂.base2.acval f.cvTa.name = mp₁.base2.acval f.cvTa.name)
    (hag₂ : ∀ n : Name, (∀ cA ∈ ctorsA, n ≠ cA.1.name) → mp₂.base2.acval n = mp₁.base2.acval n) :
    BlockReps mp₂.base2 (D) ∧
    (∀ ψ : Name → Nat, FormersTyped mp₂.base2 (D) ψ ∧ CtorsTyped mp₂.base2 (D) ψ) ∧
    ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      MemberStored mp₂.base2 b.lps b.nP f (D).resSort ((D).ppsM t) := by
  have hlenA : ctorsA.length = b.ctors.length := h.lenA
  have hkT : b.k = fms.length := h.lenFms.symm
  have hndA : (ctorsA.map (·.1.name)).Nodup := by
    rw [h.namesC]
    have h0' := h0
    unfold ConLeche.MutualBlock.blockNames at h0'
    exact (List.nodup_append.mp (List.nodup_append.mp h0').1).2.1
  -- the members' data at the constructors' model
  obtain ⟨hFP₂, hLG₂, hPJ₂⟩ := consMutualCtors_extend (nP := b.nP) h.freshC hndA
  have hag₂' : ∀ n : Name, ((ConLeche.consMutualFormers fms env).find? n).isSome = true →
      mp₁.base2.acval n = mp₂.base2.acval n := by
    intro n hn
    refine (hag₂ n fun cA hcA hh => ?_).symm
    rw [hh, h.freshC cA hcA] at hn
    exact nomatch hn
  obtain ⟨hFP₁, -, -⟩ := consMutualFormers_extend (fms := fms) (env := env)
    (fun f hf => by obtain ⟨t, ht⟩ := List.getElem?_of_mem hf; exact h.fresh t f ht)
    (by rw [h.names]; have h0' := h0; unfold ConLeche.MutualBlock.blockNames at h0'
        exact (List.nodup_append.mp (List.nodup_append.mp h0').1).1)
  have hcbF₁ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ConstsBound (ConLeche.consMutualFormers fms env) f.cvTa.type := fun t f hft =>
    constsBound_mono hFP₁ _ (h.cbF t f hft)
  have hFD₂ : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      FormerData mp₂.base2 f.cvTa (b.nP + f.nIdx) f₀.s (ppsF t) :=
    fun t f hft => FormerData.crossEnv (h.FD t f hft) (hcbF₁ t f hft) hFP₂ hLG₂ hPJ₂ hag₂'
  -- the datum's readers
  have hName : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      (D).memberName t = f.cvTa.name := fun t f hft => mutualDatum_memberName hft
  have hNIdx : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      (D).nIdxAt t = f.nIdx := fun t f hft => mutualDatum_nIdxAt hft
  have hparams : ∀ ψ : Name → Nat, (D).params ψ = ((ppsF 0 ψ).take b.nP).map (·.2.2) := fun _ => rfl
  have hw : ∀ ψ : Name → Nat, (D).w ψ = f₀.s.eval ψ := fun _ => rfl
  have hplen : ∀ ψ : Name → Nat, ((D).params ψ).length = b.nP := by
    intro ψ
    rw [hparams, List.length_map, List.length_take, (h.FD 0 f₀ h.first).len ψ]
    omega
  -- a constructor of a member, positionally
  have hctorJ : ∀ (mm j : Nat) (cA : ConstantVal × Nat), ((D).ctorsM mm)[j]? = some cA →
      b.ownOffset mm + j < ctorsA.length ∧ ctorsA[b.ownOffset mm + j]? = some cA ∧
        mutMemF b (b.ownOffset mm + j) = mm :=
    fun mm j cA hj => mutualDatum_ctorsM_get h3 hlenA hj
  -- the frames: the block's parameter frame is every member's and every constructor's
  have hframeT : ∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V ((D).params ψ).reverse ρ ↔ Sat V (((ppsF t ψ).take b.nP).map (·.2.2)).reverse ρ :=
    fun t f hft ψ ρ => (h.frame t f hft ψ ρ).symm
  have hframeC : ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat V ((D).params ψ).reverse ρ ↔ Sat V (((dsF J ψ).take b.nP).map (·.2.2)).reverse ρ := by
    intro J cA hJ ψ ρ
    have hJl : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
    exact (hframeT _ _ (fms_get (h.motLt J hJl)) ψ ρ).trans ((h.framesJ hμ hJl).1 ψ ρ)
  -- the operator's premise at every parameter frame
  have hOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V ((D).params ψ).reverse ρp →
      TupleLfpOk (W ψ) ((D).w ψ) ρp b.k (blockIds b.nP ppsF ψ) (mutMems ctorsA.length (mutMemF b))
        (mutNFs ctorsA.length (mutNFOf ctorsA))
        (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
        (mutTlss ctorsA.length tssF ψ) (mutEiss0 ctorsA.length eissF ψ)
        (blkFss0 b ctorsA kinds dsF ψ) (mutEss0 ctorsA.length esF ψ) := by
    intro ψ ρp hρp
    exact TupleLfpOk.of_tagged (h.idxAll 0 f₀ h.first ψ ρp hρp).1
      (h.chainFull hμ h.first ψ ρp hρp).1
  -- the lists' shape
  have hS : ∀ ψ : Name → Nat,
      TupleLfpShape b.k (blockIds b.nP ppsF ψ) (mutMems ctorsA.length (mutMemF b))
        (mutNFs ctorsA.length (mutNFOf ctorsA))
        (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
        (mutEiss0 ctorsA.length eissF ψ) (blkFss0 b ctorsA kinds dsF ψ)
        (mutEss0 ctorsA.length esF ψ) := by
    intro ψ
    have hlenF : (blkFss0 b ctorsA kinds dsF ψ).length = ctorsA.length := by
      show ((List.range ctorsA.length).map _).length = _; simp
    refine ⟨by rw [hlenF]; exact mutEss0_length, by rw [hlenF]; exact mutEiss0_length,
      fun J hJ => ?_, fun J hJ => ?_, fun J hJ => ?_, fun J hJ => ?_, fun J hJ i hi hr => ?_⟩
    · rw [hlenF] at hJ
      rw [mutNFs_getD hJ, blkFss0_getD hJ, shadowFs_length]
    · rw [hlenF] at hJ
      rw [mutEiss0_getD hJ, blkFss0_getD hJ, shadowFs_length]
      exact (h.CD J _ (ctorsA_get hJ)).eissLen ψ
    · rw [hlenF] at hJ
      rw [mutMems_getD hJ, hkT]
      exact h.motLt J hJ
    · rw [hlenF] at hJ
      have hmt := h.motLt J hJ
      rw [mutMems_getD hJ, mutEss0_getD hJ, (h.CD J _ (ctorsA_get hJ)).lenE ψ]
      show (fms.getD (mutMemF b J) default).nIdx = (((ppsF (mutMemF b J) ψ).drop b.nP).map (·.2.2)).length
      rw [List.length_map, List.length_drop, (h.FD _ _ (fms_get hmt)).len ψ]
      omega
    · rw [hlenF] at hJ
      have hJg := ctorsA_get hJ
      rw [blkFss0_getD hJ, shadowFs_length] at hi
      rw [blkRss_getD hJ] at hr
      have hksl : (kindsOf (mutKsOf kinds J)).length = mutNFOf ctorsA J := by
        rw [kindsOf_length]; exact (h.ksJ J _ hJg).1
      have hkind := (rsOf_getD_iff (by rw [hksl]; exact hi)).mp hr
      rw [kindsOf_getD (by rw [(h.ksJ J _ hJg).1]; exact hi)] at hkind
      obtain ⟨-, -, htgt⟩ := h.ksJ J _ hJg
      have htl := htgt i
      have htG := fms_get htl
      refine ⟨by rw [mutTgts_getD hJ hi, hkT]; exact htl, ?_⟩
      rw [mutTgts_getD hJ hi, mutEiss0_getD hJ]
      show ((eissF J ψ).getD i []).length = (((ppsF (tgtAt (mutKsOf kinds J) i) ψ).drop b.nP).map (·.2.2)).length
      rw [List.length_map, List.length_drop, (h.FD _ _ htG).len ψ,
        Nat.add_sub_cancel_left, ← (h.memT _ _ htG).2]
      rcases hkind with hk | hk
      · exact (h.CD J _ hJg).eisLen ψ i hk hi
      · exact (h.CD J _ hJg).eisLenRefl ψ i hk hi
  -- the per-member facts
  have hrep : ∀ mm : Nat, mm < b.k → ∃ (cvT cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      BlockRep mp₂.base2 ((D).memberName mm) cvT cvR mI rP rules (D) mm := by
    intro mm hmm
    have hmmF : mm < fms.length := by rw [← hkT]; exact hmm
    have hft := fms_get hmmF
    refine ⟨(fms.getD mm default).cvTa, default, (D).nP + (D).k + (D).nCtors + (D).nIdxAt mm,
      (D).nP + (D).k + (D).nCtors, [], ?_⟩
    have hlpsT : (fms.getD mm default).cvTa.levelParams = b.lps := h.lps _ _ hft
    refine
      { memberLt := hmm, member := rfl, strip := ?_, isProp := rfl, mI := rfl, rP := rfl
        rules := fun hne => absurd rfl hne, former := ?_, ctors := ?_, memsFound := ?_
        tgtsLt := ?_, idxRes := ?_, uParams := ?_, paramsIff := ?_, idxOk := ?_, functor := ?_
        fibre := ?_, leaf := ?_, ctor := ?_, mkZero := ofMutual_mkZero, mkInj := ?_ }
    · -- strip
      obtain ⟨bs, hstrip⟩ := h.strip _ _ hft
      rw [hNIdx _ _ hft]
      exact ⟨bs, _, hstrip, h.sEq _ _ hft⟩
    · -- former
      rw [hNIdx _ _ hft]
      exact hFD₂ _ _ hft
    · -- ctors
      intro mm' j cA hmm' hj
      obtain ⟨hJl, hJ, hmemJ⟩ := hctorJ mm' j cA hj
      obtain ⟨hfind, hlpsC, hCD⟩ := (hcons _ cA hJ).1
      refine ⟨hfind, by rw [hlpsT]; exact hlpsC, ?_⟩
      have hCD' := (hCD.congr_sort (h.sEq _ _ (fms_get (h.motLt _ hJl)))).withOpened
        (h.CD _ cA hJ).opened
      have hB := hCD'.toBlock
      rw [hlpsT]
      have hT : (D).memberName mm' = (fms.getD (mutMemF b (b.ownOffset mm' + j)) default).cvTa.name := by
        rw [hmemJ]; exact hName _ _ (fms_get (by rw [← hkT]; exact hmm'))
      have hTof : (fun i => (D).memberName ((D).tgts mm' j i))
          = fun i => mutualNameOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) i) := by
        funext i
        have htl := (h.ksJ _ cA hJ).2.2 i
        show (D).memberName (tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) i) = _
        rw [hName _ _ (fms_get htl), (h.memT _ _ (fms_get htl)).1]
      have hNof : (fun i => (D).nIdxAt ((D).tgts mm' j i))
          = fun i => mutualNIdxOf b.members3 (tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) i) := by
        funext i
        have htl := (h.ksJ _ cA hJ).2.2 i
        show (D).nIdxAt (tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) i) = _
        rw [hNIdx _ _ (fms_get htl), (h.memT _ _ (fms_get htl)).2]
      have hNI : (D).nIdxAt mm' = (fms.getD (mutMemF b (b.ownOffset mm' + j)) default).nIdx := by
        rw [hmemJ]; exact hNIdx _ _ (fms_get (by rw [← hkT]; exact hmm'))
      rw [hT, hTof, hNof, hNI]
      exact hB
    · -- memsFound
      intro mm' hmm'
      have hft' := fms_get (by rw [← hkT]; exact hmm')
      rw [hName _ _ hft']
      exact ⟨_, _, hFP₂ (h.find _ _ hft')⟩
    · -- tgtsLt
      intro mm' j i _ hj _
      have hj' : ((D).ctorsM mm')[j]? = some (((D).ctorsM mm').getD j default) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
      obtain ⟨-, hJ, -⟩ := hctorJ mm' j _ hj'
      show tgtAt (mutKsOf kinds (b.ownOffset mm' + j)) i < b.k
      rw [hkT]
      exact (h.ksJ _ _ hJ).2.2 i
    · -- idxRes
      intro mm' j cA hmm' hj e he
      obtain ⟨-, hJ, -⟩ := hctorJ mm' j cA hj
      exact (hcons _ cA hJ).2.1 e he
    · -- uParams
      intro mm' _ ψ₁ ψ₂ hφ
      rw [hlpsT] at hφ
      exact (h.blockOk.params hφ).1
    · -- paramsIff
      intro mm' j cA hmm' hj ψ ρ
      obtain ⟨-, hJ, -⟩ := hctorJ mm' j cA hj
      exact hframeC _ cA hJ ψ ρ
    · -- idxOk
      intro ψ ρp hρp mm' hmm'
      exact (hOk ψ ρp hρp).idxOk hmm'
    · -- functor
      intro ψ ρp hρp
      exact ofMutual_functor (hOk ψ ρp hρp)
    · -- fibre
      intro ψ ρp hρp X hX mm' hmm' t ht x
      have hOk' := hOk ψ ρp hρp
      have hS' := hS ψ
      have hlenF : (blkFss0 b ctorsA kinds dsF ψ).length = ctorsA.length := by
        show ((List.range ctorsA.length).map _).length = _; simp
      -- the fit and the terminator, at a constructor's global position
      have hfitJ : ∀ (J j : Nat) (cA : ConstantVal × Nat), J < ctorsA.length →
          b.ownOffset mm' + j = J → ((D).ctorsM mm')[j]? = some cA → ∀ fs : List V,
          FitsFrom ((blkRss ctorsA kinds).getD J [])
              (fun i ρ => slotSet (f₀.s.eval ψ) (W ψ) ρ
                (((mutTlss ctorsA.length tssF ψ).getD J []).getD i [])
                (((mutEiss0 ctorsA.length eissF ψ).getD J []).getD i [])
                (X (((mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)).getD J []).getD i 0)))
              0 ρp ((blkFss0 b ctorsA kinds dsF ψ).getD J []) fs ↔
            FitsFrom (((D).rss mm').getD j []) ((D).slotAt ψ X mm' j) 0 ρp
              (((D).Fss mm' ψ).getD j []) fs := by
        intro J j cA hJl hJeq hj fs
        subst hJeq
        have hJ : ctorsA[b.ownOffset mm' + j]? = some cA := (hctorJ mm' j cA hj).2.1
        have hjl : j < ((D).ctorsM mm').length := (List.getElem?_eq_some_iff.mp hj).1
        have hlenDs : (dsF (b.ownOffset mm' + j) ψ).length = b.nP + cA.2 := (h.CD _ cA hJ).len ψ
        have hksl : (mutKsOf kinds (b.ownOffset mm' + j)).length = cA.2 := (h.ksJ _ cA hJ).1
        have hnF : mutNFOf ctorsA (b.ownOffset mm' + j) = cA.2 := mutNFOf_eq hJ
        rw [BlockRep.rss_getD hjl, BlockRep.Fss_getD hj ψ, blkRss_getD hJl, blkFss0_getD hJl]
        show FitsFrom (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))) _ 0 ρp _ fs ↔
          FitsFrom (rsOf (kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))) _ 0 ρp
            (((dsF (b.ownOffset mm' + j) ψ).drop b.nP).map (·.2.2)) fs
        refine fitsFrom_congr (by rw [shadowFs_length, List.length_map, List.length_drop, hlenDs, hnF]; omega)
          (fun l _ => rfl) (fun l hl hr => ?_) (fun l hl hr => ?_)
        · rw [shadowFs_length, hnF] at hl
          intro ρ'
          show slotSet _ _ _ _ _ _ = slotSet (f₀.s.eval ψ) (W ψ) ρ'
            ((((D).tlss mm' ψ).getD j []).getD (0 + l) [])
            ((((D).Eiss mm' ψ).getD j []).getD (0 + l) []) (X ((D).tgts mm' j (0 + l)))
          rw [BlockRep.tlss_getD hj ψ, BlockRep.Eiss_getD hj ψ, mutTlss_getD hJl, mutEiss0_getD hJl,
            mutTgts_getD hJl (by rw [hnF, Nat.zero_add]; exact hl)]
          rfl
        · rw [shadowFs_length, hnF] at hl
          rw [shadowFs_getD (by rw [hnF]; exact hl), if_neg]
          intro hrec
          have hkind := hrec.2
          rw [Nat.add_sub_cancel_left] at hkind
          have := (rsOf_getD_iff (ks := kindsOf (mutKsOf kinds (b.ownOffset mm' + j)))
            (by rw [kindsOf_length, hksl]; exact hl)).mpr hkind
          rw [Nat.zero_add] at hr
          rw [hr] at this
          exact Bool.false_ne_true this
      have htermJ : ∀ (J j : Nat) (cA : ConstantVal × Nat), J < ctorsA.length →
          b.ownOffset mm' + j = J → ((D).ctorsM mm')[j]? = some cA → ∀ fs : List V,
          (∀ l, l < (blockIds b.nP ppsF ψ mm').length →
            interp V (consList fs ρp) (((mutEss0 ctorsA.length esF ψ).getD J []).getD l default)
              = projS l t) ↔
          ∀ l, l < ((D).IdsM mm' ψ).length →
            interp V (consList fs ρp) ((((D).Ess mm' ψ).getD j []).getD l default) = projS l t := by
        intro J j cA hJl hJeq hj fs
        rw [BlockRep.Ess_getD hj ψ, mutEss0_getD hJl]
        show (∀ l, l < (blockIds b.nP ppsF ψ mm').length → interp V (consList fs ρp) ((esF J ψ).getD l default) = projS l t) ↔
          ∀ l, l < (blockIds b.nP ppsF ψ mm').length →
            interp V (consList fs ρp) ((esF (b.ownOffset mm' + j) ψ).getD l default) = projS l t
        rw [hJeq]
      have hinjJ : ∀ (j : Nat) (fs : List V),
          (D).inj ψ mm' j fs = injW (f₀.s.eval ψ) (b.ownOffset mm' + j) (mkTower (fs ++ [pt])) := by
        intro j fs
        show injW (f₀.s.eval ψ) ((D).minorIdx mm' j) (mkTower (fs ++ [pt])) = _
        rw [mutualDatum_minorIdx]
      show x ∈ˢ SetTheory.app (tupleLfpΦ (W ψ) ((D).w ψ) ρp b.k (blockIds b.nP ppsF ψ)
        (mutMems ctorsA.length (mutMemF b)) (mutNFs ctorsA.length (mutNFOf ctorsA))
        (mutTgts ctorsA.length (mutKsOf kinds) (mutNFOf ctorsA)) (blkRss ctorsA kinds)
        (mutTlss ctorsA.length tssF ψ) (mutEiss0 ctorsA.length eissF ψ)
        (blkFss0 b ctorsA kinds dsF ψ) (mutEss0 ctorsA.length esF ψ) X mm') t ↔ _
      rw [tupleLfpΦ_fibre hOk' hS' hX hmm' ht x]
      constructor
      · rintro ⟨J, fs, hJ, hmemJ, hfit, heqs, rfl⟩
        rw [hlenF] at hJ
        rw [mutMems_getD hJ] at hmemJ
        obtain ⟨-, hle, hj⟩ := mutualDatum_ofCtor (V := V) (fms := fms) (f₀ := f₀) (kinds := kinds)
          (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF) (esF := esF) (srcsF := srcsF)
          (fvsPF := fvsPF) (xFvsF := xFvsF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF)
          h3 h2 hlenA hJ
        rw [hmemJ] at hle hj
        have hJeq : b.ownOffset mm' + (J - b.ownOffset mm') = J := by omega
        refine ⟨J - b.ownOffset mm', fs, (List.getElem?_eq_some_iff.mp hj).1,
          ⟨(hfitJ J _ _ hJ hJeq hj fs).mp hfit, (htermJ J _ _ hJ hJeq hj fs).mp heqs⟩, ?_⟩
        rw [hinjJ, hJeq]
        rfl
      · rintro ⟨j, fs, hjl, ⟨hfit, heqs⟩, rfl⟩
        have hj : ((D).ctorsM mm')[j]? = some (((D).ctorsM mm').getD j default) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; rfl
        obtain ⟨hJl, hJ, hmemJ⟩ := hctorJ mm' j _ hj
        refine ⟨b.ownOffset mm' + j, fs, by rw [hlenF]; exact hJl, ?_,
          (hfitJ _ j _ hJl rfl hj fs).mpr hfit, (htermJ _ j _ hJl rfl hj fs).mpr heqs, ?_⟩
        · rw [mutMems_getD hJl]; exact hmemJ
        · rw [hinjJ]
          rfl
    · -- leaf
      intro ψ ρ as is hsp hi
      rw [hName _ _ hft, hleafM _ _ hft, h.leaf _ _ hft]
      unfold mutMemberLeaf
      have hsp' : SpineFit ρ (((ppsF mm ψ).take b.nP).map (·.2.2)) as :=
        spineFit_of_frames (by
            rw [hplen, List.length_map, List.length_take, (h.FD _ _ hft).len ψ]; omega)
          (fun ρ' => hframeT _ _ hft ψ ρ') hsp
      have hnI : ((ppsF mm ψ).drop b.nP).length = (fms.getD mm default).nIdx := by
        rw [List.length_drop, (h.FD _ _ hft).len ψ]
        exact Nat.add_sub_cancel_left _ _
      rw [← hnI]
      exact ofMutual_leaf hmm (hOk ψ (consList as ρ) ((D).satOfSpine hsp)) hsp' hi
    · -- ctor
      intro mm' j cA hmm' hj ψ ρ as fs hsp hsp₂
      obtain ⟨hJl, hJ, hmemJ⟩ := hctorJ mm' j cA hj
      rw [(hcons _ cA hJ).2.2 ψ]
      rw [BlockRep.Fss_getD hj ψ] at hsp₂
      show (as ++ fs).foldl SetTheory.app (interp V ρ _)
        = injW (f₀.s.eval ψ) ((D).minorIdx mm' j) (mkTower (fs ++ [pt]))
      rw [mutualDatum_minorIdx]
      show (as ++ fs).foldl SetTheory.app (interp V ρ (sumMkAV (f₀.s.eval ψ) (b.ownOffset mm' + j)
          (dsF (b.ownOffset mm' + j) ψ) (((dsF (b.ownOffset mm' + j) ψ).drop b.nP).map (·.2.2))
          (uChains (mutFss b.nP ctorsA.length dsF ψ))))
        = injW (f₀.s.eval ψ) (b.ownOffset mm' + j) (mkTower (fs ++ [pt]))
      by_cases hw0 : f₀.s.eval ψ = 0
      · rw [hw0, sumMkAV_zero, foldl_app_pt, injW_zero]
      · have hlenDs : (dsF (b.ownOffset mm' + j) ψ).length = b.nP + cA.2 := (h.CD _ cA hJ).len ψ
        have hsp₁ : SpineFit ρ (((dsF (b.ownOffset mm' + j) ψ).take b.nP).map (·.2.2)) as :=
          spineFit_of_frames (by
              rw [hplen, List.length_map, List.length_take, hlenDs]; omega)
            (fun ρ' => hframeC _ cA hJ ψ ρ') hsp
        have hsat : Sat V (((dsF (b.ownOffset mm' + j) ψ).take b.nP).map (·.2.2)).reverse
            (consList as ρ) := by
          have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hsp₁
          rwa [List.append_nil] at this
        have hok : SumFieldsOkB (f₀.s.eval ψ) (consList as ρ)
            (uChains (mutFss b.nP ctorsA.length dsF ψ)) :=
          SumFieldsOkB_uChains (h.fssOkP hμ hJl ψ (consList as ρ) hsat).1
        have hFsJ : (uChains (mutFss b.nP ctorsA.length dsF ψ))[b.ownOffset mm' + j]?
            = some ((((dsF (b.ownOffset mm' + j) ψ).drop b.nP).map (·.2.2)) ++ [idxEqAV []]) := by
          rw [uChains_getElem?, List.getElem?_eq_getElem (show b.ownOffset mm' + j
            < (mutFss b.nP ctorsA.length dsF ψ).length from by rw [mutFss_length]; exact hJl)]
          have hgd := mutFss_getD (n := ctorsA.length) (nP := b.nP) (dsF := dsF) (ψ := ψ) hJl
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show b.ownOffset mm' + j
            < (mutFss b.nP ctorsA.length dsF ψ).length from by rw [mutFss_length]; exact hJl),
            Option.getD_some] at hgd
          rw [hgd]
          rfl
        have hsplit : (dsF (b.ownOffset mm' + j) ψ).take b.nP ++ (dsF (b.ownOffset mm' + j) ψ).drop b.nP
            = dsF (b.ownOffset mm' + j) ψ := List.take_append_drop _ _
        have := sumMkAV_fold (V := V) (j := b.ownOffset mm' + j) hw0
          (pds := (dsF (b.ownOffset mm' + j) ψ).take b.nP)
          (fds := (dsF (b.ownOffset mm' + j) ψ).drop b.nP)
          (Fss := uChains (mutFss b.nP ctorsA.length dsF ψ)) hsp₁ hsp₂ hok hFsJ
        rw [hsplit] at this
        rw [this, injW_pos hw0]
    · -- mkInj
      intro ψ hw' mm' hmm' j fs j' fs' hj hj' hlen hlen' heq
      exact ofMutual_mkInj ψ hw' hlen hlen' heq
  refine ⟨hrep, fun ψ => ⟨?_, ?_⟩, fun t f hft => ⟨⟨{}, hFP₂ (h.find _ _ hft)⟩, h.lps _ _ hft,
    h.strip _ _ hft, h.sEq _ _ hft, hFD₂ _ _ hft⟩⟩
  · -- FormersTyped
    intro t ht ρ
    have hft := fms_get (by rw [← hkT]; exact ht)
    rw [hName _ _ hft]
    have hread := (hFD₂ _ _ hft).read ψ
    have := mp₂.mem_type _ (ConLeche.Semantics.Env.find?_mem (hFP₂ (h.find _ _ hft))) ψ _ hread ρ
    exact this
  · -- CtorsTyped
    intro c hc j cA hj ρ
    obtain ⟨hJl, hJ, hmemJ⟩ := hctorJ c j cA hj
    obtain ⟨hfind, -, hCD⟩ := (hcons _ cA hJ).1
    have hread := hCD.read ψ
    have := mp₂.mem_type _ (ConLeche.Semantics.Env.find?_mem hfind) ψ _ hread ρ
    have hT : (D).memberName c = (fms.getD (mutMemF b (b.ownOffset c + j)) default).cvTa.name := by
      rw [hmemJ]; exact hName _ _ (fms_get (by rw [← hkT]; exact hc))
    rw [hT]
    exact this

end Reps

/-! ## The recursors' stage, named; the core -/

/-- **Stage 4 keeps the model and the datum** — the named fact of
`mutualCoreModeled_of` (M4 session 4): at a model of the
constructors' environment carrying the datum (the block at every
member, the members and constructors typed, every other leaf the
pre-block model's; the recursors' names fresh, unreserved and no
projection's there; the members stored at the datum's readings,
`MemberStored`; the datum's kinds the run's classification), the
recursor types, the rules at the rule-less provision and the group
store cons a model of the recursors' environment at which the datum
still holds, every other leaf untouched.  The run facts are the
core's, verbatim.  Consumer: `mutualCoreModeled_of`; discharged
modulo its store half `MutualRecsStored` by `mutualRecsModeled_of`
(`MutualRecsStage.lean`, M4 session 4a). -/
@[expose] def MutualRecsModeled (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env : Env} (mp : EnvModelM V μ env), ConLeche.EtaFamiliesClosed env →
  ∀ (b : MutualBlock) (streamRecs : Option (List (ConstantVal × List RecRule)))
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (tq₀ : List Expr × Expr)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level))
    (kinds : List (List (RecFieldKind × Nat))) (formers4 : List ConLeche.MutualFormer)
    (ctors4 : List ConLeche.MutualCtor4) (cvRas : List ConstantVal)
    (rulesOf : List (List (MutualCtor × Expr))),
    b.blockNames.Nodup →
    (b.formers.all (fun f => f.1.levelParams == b.lps) &&
      b.ctors.all (fun c => c.cv.levelParams == b.lps)) = true →
    b.ctors.all (fun c => c.member < b.k) = true →
    ConLeche.mutualCtorsGrouped b.ctors = true →
    ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (ConLeche.consMutualFormers fms env, fms) →
    fms[0]? = some f₀ →
    ConLeche.openPisAtFvars b.nP f₀.cvTa.type 0 = some tq₀ →
    ConLeche.mutualCrossChecks (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b.nP f₀ (tq₀.1.map Expr.fvarTypeD) fms = .ok () →
    b.large = f₀.s.isNeverZero →
    ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) b.ctors
      = .ok (ctorsA, sortss) →
    ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
      = .ok kinds →
    ConLeche.mutualFieldsOk env b.members3 b.lps b.nP ctorsA kinds = true →
    ConLeche.mutualGenData b fms ctorsA kinds = (formers4, ctors4) →
    ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) b formers4 ctors4
      streamRecs b.k = .ok cvRas →
    ConLeche.checkMutualAllRules (m := ConLeche.CheckM)
      (ConLeche.provisionMutualRecs b fms cvRas.zipIdx
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)))
      b formers4 ctors4 streamRecs b.k = .ok rulesOf →
    ∀ (mp₂ : EnvModelM V μ (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))),
      ConLeche.EtaFamiliesClosed
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) →
      (∀ n, n ∉ b.blockNames → ∀ ψ : Name → Nat, mp₂.base2.acval n ψ = mp.base2.acval n ψ) →
      ∀ d : BlockRepData V, MutualDatumOf env b fms ctorsA d → BlockReps mp₂.base2 d →
        (∀ ψ : Name → Nat, FormersTyped mp₂.base2 d ψ ∧ CtorsTyped mp₂.base2 d ψ) →
        -- the recursors' names are fresh, unreserved and no projection's
        (∀ t, t < b.k →
          (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)).find?
            (b.recName t) = none ∧
          ConLeche.reservedBasisNames.contains (b.recName t) = false ∧
          (b.recName t).isProjFnShape = false) →
        -- the members are stored at the datum's readings
        (∀ (t : Nat) (f : MutualFormerA), fms[t]? = some f →
          MemberStored mp₂.base2 b.lps b.nP f d.resSort (d.ppsM t)) →
        -- the datum's kinds are the run's classification
        (∀ mm j, mm < b.k → j < (d.ctorsM mm).length →
          d.ksF mm j = kindsOf (mutKsOf kinds (b.ownOffset mm + j)) ∧
          ∀ i, d.tgts mm j i = tgtAt (mutKsOf kinds (b.ownOffset mm + j)) i) →
        ∃ mp₃ : EnvModelM V μ
            (ConLeche.storeMutualRecs
              (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) b fms
              rulesOf cvRas.zipIdx
              (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))),
          (∀ n, n ∉ b.blockNames → ∀ ψ : Name → Nat, mp₃.base2.acval n ψ = mp₂.base2.acval n ψ) ∧
          BlockReps mp₃.base2 d ∧
          ∀ ψ : Name → Nat, FormersTyped mp₃.base2 d ψ ∧ CtorsTyped mp₃.base2 d ψ

/-- **The core of the mutual install, modulo its recursors' stage**:
stages 0–3 keep the model and leave the datum at the constructors'
environment (`mutualFormersStage`, `mutualCtorsStage`,
`blockReps_of`); stage 4 is the named fact. -/
theorem mutualCoreModeled_of {F : Nat} (hrec : MutualRecsModeled V μ F) :
    MutualCoreModeled V μ F := by
  intro hμ env mp hE b streamRecs env₁ fms f₀ tq₀ ctorsA sortss kinds formers4 ctors4 cvRas
    rulesOf h0 h1 h2 h3 hformers hf₀ htq₀ hcross hL hctors hkinds hfo hgd hrectys hrules
    hrecNames
  obtain ⟨-, rfl⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨mp₁, ppsF, W, idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, eissF, tssF, h⟩ :=
    mutualFormersStage hμ mp hE b h0 h1 h2 hformers hf₀ htq₀ hcross hctors hkinds hfo
  obtain ⟨mp₂, hE₂, hcons, hleafM, hag₂⟩ := mutualCtorsStage h hμ hE h0
  obtain ⟨hreps, htyped, hstored⟩ := blockReps_of hμ h0 h2 h3 h mp₂ hcons hleafM hag₂
  -- the model agrees with the pre-block model off the block
  have hagree : ∀ n, n ∉ b.blockNames → ∀ ψ : Name → Nat,
      mp₂.base2.acval n ψ = mp.base2.acval n ψ := by
    intro n hn ψ
    have hnM : n ∉ b.memberNames := fun hm => hn (by
      unfold ConLeche.MutualBlock.blockNames
      exact List.mem_append_left _ (List.mem_append_left _ hm))
    have hnC : n ∉ b.ctors.map (·.cv.name) := fun hc => hn (by
      unfold ConLeche.MutualBlock.blockNames
      exact List.mem_append_left _ (List.mem_append_right _ hc))
    have h1' := hag₂ n (fun cA hcA heq => hnC (by
      rw [← h.namesC]; exact heq ▸ List.mem_map_of_mem hcA))
    have h2' := h.off n (fun t f hft heq => hnM (by
      rw [← h.names]; exact heq ▸ List.mem_map_of_mem (List.mem_of_getElem? hft)))
    rw [h1', h2']
  have hd : MutualDatumOf env b fms ctorsA
      (mutualDatum (V := V) b fms f₀ ctorsA kinds env ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF
        eissF tssF) :=
    mutualDatumOf_ofMutual env b fms ctorsA hf₀ _ ppsF W _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨mp₃, hag₃, hreps₃, htyped₃⟩ := hrec hμ mp hE b streamRecs fms f₀ tq₀ ctorsA sortss kinds
    formers4 ctors4 cvRas rulesOf h0 h1 h2 h3 hformers hf₀ htq₀ hcross hL hctors hkinds hfo hgd
    hrectys hrules mp₂ hE₂ hagree _ hd hreps htyped hrecNames hstored
    (fun mm j _ _ => ⟨rfl, fun _ => rfl⟩)
  exact ⟨mp₃, fun n hn ψ => (hag₃ n hn ψ).trans (hagree n hn ψ), _, hd, hreps₃, htyped₃⟩

/-- **`declBlock` at the recursors' stage's fact**: the model survives
a mutual block, given stage 4 (`MutualRecsModeled`) and stage 5
(`MutualTablesModeled`). -/
theorem declBlock_of_recs (hμ : μ.verifiedChecks = true) {F : Nat} {envOut : Env}
    {p : ConLeche.MutualParts} (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hpinOk : ConLeche.mutualRecPinOk p = true)
    (hrec : MutualRecsModeled V μ F) (htables : MutualTablesModeled V μ)
    (h : ConLeche.Semantics.DeclMutualRun μ F env p envOut) :
    Nonempty (EnvModelM V μ envOut) :=
  declBlock hμ mp hE hpinOk (mutualCoreModeled_of hrec) htables h

end ConLeche.Model
