module

public import ConLeche.Model.Inductives.BlockRepMutual
public import ConLeche.Model.Inductives.MutualStageCtor
public import ConLeche.Model.Inductives.MutualIdxUniv
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

end ConLeche.Model
