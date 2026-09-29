module

public import ConLeche.Model.Inductives.DeclNative
public import ConLeche.Model.Inductives.BlockDatum
public import ConLeche.Semantics.Inductives.DeclBlock
public section

/-!
# The uniform block install's records (#315)

The records the uniform block step (`declBlock`,
`Model/Inductives/DeclBlockStep.lean`) is stated over: the conses keep
the members' projection slots free, the recursors' stage's obligation
(`BlockRecStagedT`), the block over an older environment, the positivity
model at the formers' environment, and the recursors' stage's shared
context (`RecCtxBase`; the stage's own, with its run, is `GenRecCtx`,
`GenRecAssembly.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockShape BlockParts MemberShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## `NoProjEnv` across the block's conses -/

/-- The `k` formers' cons keeps a member's slots free: a former's type
resolves before the block, and an `indInfo` carries nothing else. -/
theorem noProjEnv_consBlockInds {T : Name} {i : Nat} {p₁ : ConLeche.BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {j : Nat} {env₀ : Env},
      NoProjEnv env₀ T i → (∀ cvTa ∈ cvTas, Expr.NoProjAt T i cvTa.type) →
      NoProjEnv (ConLeche.consBlockInds p₁ isRec cvTas j env₀) T i
  | [], _, _, h, _ => h
  | cvTa :: rest, j, env₀, h, hall => by
    simp only [ConLeche.consBlockInds]
    refine noProjEnv_consBlockInds
      (h.cons (c₀ := .indInfo cvTa (ConLeche.blockCapsAt p₁ j isRec)) (NoProjHead.ofType
        (hall cvTa List.mem_cons_self) (fun _ _ _ h => nomatch h)
        (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h))) ?_
    exact fun c hc => hall c (List.mem_cons_of_mem _ hc)

/-- The members' constructors' conses keep a member's slots free. -/
theorem noProjEnv_consBlockCtors {T : Name} {i nP : Nat} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env₀ : Env},
      NoProjEnv env₀ T i →
      (∀ ctorsA ∈ ctorsAs, ∀ cA ∈ ctorsA, Expr.NoProjAt T i cA.1.type) →
      NoProjEnv (ConLeche.consBlockCtors nP ctorsAs env₀) T i
  | [], _, h, _ => h
  | ctorsA :: rest, env₀, h, hall => by
    simp only [ConLeche.consBlockCtors]
    refine noProjEnv_consBlockCtors
      (noProjEnv_consSumCtors h (hall ctorsA List.mem_cons_self)) ?_
    exact fun l hl => hall l (List.mem_cons_of_mem _ hl)

/-- A name absent above the constructors' conses was absent below them. -/
theorem find?_none_consBlockCtors {nP : Nat} {n : Name} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env₀ : Env},
      (ConLeche.consBlockCtors nP ctorsAs env₀).find? n = none → env₀.find? n = none
  | [], _, h => h
  | _ :: rest, _env₀, h =>
    ConLeche.consSumCtors_find?_none (find?_none_consBlockCtors (ctorsAs := rest) h)


/-! ## The recursor stage's obligation -/

/-- **What the recursors' stage owes the tables' stage** (conjunct ⑧
of `declBlock`, which `DeclBlockRun` leaves opaque): a carrier at the post-recursor environment that
* reads every name the pre-recursor environment stores as that
  environment's carrier does (`acval` agreement),
* finds everything it found (`find?` monotonicity),
* reads every pre-recursor-bounded expression the same way
  (`denoteMeta` stability — the constructors' and formers' TYPE
  readings cross the conses), and
* keeps every member's projection slots free (`NoProjEnv`
  preservation — the generated recursor types and rule right-hand
  sides carry no projection of a member).

It is four cons-monotonicities and mentions no `BlockData`. -/
@[expose] def BlockRecStagedAt (μ : CheckMode) {V : Type w} [SetTheory V]
    (envC env₃ : Env) (mpC : EnvModelM V μ envC) : Prop :=
  ∃ mp' : EnvModelM V μ env₃,
    (∀ n : Name, (envC.find? n).isSome = true → mp'.base2.acval n = mpC.base2.acval n) ∧
    (∀ (n : Name) (c : ConstantInfo), envC.find? n = some c → env₃.find? n = some c) ∧
    (∀ (ψ : Name → Nat) (dd : Nat) (e : Expr), ConstsBound envC e →
      denoteMeta mp'.base2.acval env₃ ψ dd e = denoteMeta mpC.base2.acval envC ψ dd e) ∧
    (∀ (T : Name) (i : Nat), envC.findProj? T i = none → NoProjEnv envC T i →
      NoProjEnv env₃ T i)


/-- **The tables' invariant crosses the recursors' conses**, by the
four facts of `BlockRecStagedAt` and nothing else. -/
theorem BlockTablesCore.consRecs {envC envR : Env} {mC : EnvModel V envC} {mR : EnvModel V envR}
    {d : BlockData V} {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : ConLeche.BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (h : BlockTablesCore mC d lps cvTasAll p₁ isRec A 0)
    (hag : ∀ n : Name, (envC.find? n).isSome = true → mR.acval n = mC.acval n)
    (hfind : ∀ (n : Name) (c : ConstantInfo), envC.find? n = some c → envR.find? n = some c)
    (hden : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr), ConstsBound envC e →
      denoteMeta mR.acval envR ψ dd e = denoteMeta mC.acval envC ψ dd e)
    (hnp : ∀ (T : Name) (i : Nat), envC.findProj? T i = none →
      NoProjEnv envC T i → NoProjEnv envR T i)
    (hslot : ∀ c, c < d.k → (∃ cA, d.ctorsM c = [cA]) → d.nIdxAt c = 0 →
      ∀ j, envC.findProj? (d.memberName c) j = none) :
    BlockTablesCore mR d lps cvTasAll p₁ isRec A 0 := by
  obtain ⟨hform, hctor, hnpC⟩ := h
  have hsome : ∀ n : Name, (envC.find? n).isSome = true → (envR.find? n).isSome = true := by
    intro n hn
    cases hc : envC.find? n with
    | none => rw [hc] at hn; exact nomatch hn
    | some c => rw [hfind n c hc]; rfl
  refine ⟨fun c cvTb hc => ?_, fun c j cA hj => ?_,
    fun c hc hck h1 h2 j => hnp _ _ (hslot c hck h1 h2 j) (hnpC c hc hck h1 h2 j)⟩
  · obtain ⟨hfindT, hres, hleaf, hFD⟩ := hform c cvTb hc
    refine ⟨hfind _ _ hfindT, Expr.constsResolve_of_find hsome hres, fun ψ => ?_, ?_⟩
    · rw [hag cvTb.name (by rw [hfindT]; rfl)]; exact hleaf ψ
    · exact ⟨fun ψ => by
        rw [hden ψ 0 cvTb.type (constsBound_of_constsResolve _ hres)]; exact hFD.read ψ,
      hFD.len, hFD.bits, hFD.okTy, hFD.below, hFD.params, hFD.syn⟩
  · obtain ⟨hfindC, hlps, hres, hread, hleaf⟩ := hctor c j cA hj
    refine ⟨hfind _ _ hfindC, hlps, Expr.constsResolve_of_find hsome hres, fun ψ => ?_,
      fun ψ => ?_⟩
    · rw [hden ψ 0 cA.1.type (constsBound_of_constsResolve _ hres)]; exact hread ψ
    · rw [hag cA.1.name (by rw [hfindC]; rfl)]; exact hleaf ψ

/-- **The recursors' stage's obligation at the cons at the majors**:
`BlockRecStagedAt`'s four cons-monotonicities at
`consBlockRecsT`, the family consed with each recursor's rules at ITS
major (`.nested` at an outside one). -/
@[expose] def BlockRecStagedT (μ : CheckMode) {V : Type w} [SetTheory V]
    (envC : Env) (p : ConLeche.BlockShape)
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) : Prop :=
  BlockRecStagedAt μ envC
    (ConLeche.consBlockRecsT envC.find? (·.constsResolve envC) p 0 out envC) mpC


/-- **The block over an older environment**: a well-formed environment `env₀` in which no member
name is stored, and in which every constant of `envC` was stored already
unless it is a former or a constructor concluding in a member.  A
container's constructor (it concludes in its own, non-member inductive)
therefore resolves in `env₀` and names no member. -/
@[expose] def BlockOverEnv (envC : Env) (names : List Name) : Prop :=
  ∃ env₀ : Env, ConLeche.EnvWF env₀ ∧ (∀ n ∈ names, env₀.find? n = none) ∧
    ∀ n ci, envC.find? n = some ci → env₀.find? n = some ci ∨
      (∃ cv caps, ci = .indInfo cv caps) ∨
      ∃ cv nP nF bs body us m, ci = .ctorInfo cv nP nF ∧
        cv.type.stripPis (nP + nF) = some (bs, body) ∧ body.getAppFn = .const m us ∧ m ∈ names

/-- **The positivity model at the formers' environment**: a carrier at `envI` covering every recorded block but the
block's own members (`names`), whose recorded blocks are among `mpC`'s and
whose leaves are `mpC`'s at every name stored at `envI` — the model the
positivity derivation's monotonicity (`frame_mono`, at the derivation's
environment `envI`) reads, tied to the recursor stage's carrier.  Every
block `mpC` records is `mk`'s or the block's own `D0` (`FrameMono` asks a container's block in `mk.lfpBlocks`, `lfpSel` selects
from `mpC.lfpBlocks`). -/
@[expose] def FormersModelAt (envI : Env) (names : List Name) {envC : Env}
    (mpC : EnvModelM V μ envC) (d : BlockData V) (lps : List Name) (cvTas : List ConstantVal)
    (p : BlockShape) (isRec : Bool) : Prop :=
  ∃ mk : EnvModelM V μ envI, LfpCover mk names ∧ (∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks) ∧
    (∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n) ∧
    (∀ D ∈ mpC.lfpBlocks, D = d.toLfp ∨ D ∈ mk.lfpBlocks) ∧
    -- the member constructors' hole contexts at the formers' model (the
    -- node-semantics induction's root)
    BlockHoleCtxFacts mk.base2 d lps cvTas p isRec ∧
    -- a reading at the formers' environment is one at the constructors'
    ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mk.base2.acval envI ψ dd e = some ea → denoteMeta mpC.base2.acval envC ψ dd e = some ea

/-- **The recursors' stage's context, without the stage's own run**: what
`GenRecCtx` (the generated stage, `GenRecAssembly.lean`) holds — the positivity run, the constructors'
cons, the block's representation and model records, the block over the
input environment.  The node route's facts that read no recursor run take
this (`nodeListFacts_of`, `dynCtx_of`). -/
@[expose] def RecCtxBase (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (envC envI : Env) (pp : BlockParts)
    (cvTasR : List ConstantVal) (ctorsAsR : List (List (ConstantVal × Nat)))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr))
    (posR : ConLeche.NestState) : Prop :=
  ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
      envI.find? envI.consts pp cvTasR ctorsAsR = .ok (kindsR, nfsR, posR) ∧
  envC = ConLeche.consBlockCtors pp.nP ctorsAsR envI ∧
  ctorsAsR.map (·.map (fun cA => (cA.1.name, cA.2)))
    = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) ∧
  pp.toBlockShape.memberNames.Nodup ∧
  BlockNamesOk (V := V) dR cvTasR ∧
  BlockCtorsStage (V := V) μ F dR pp.lps cvTasR pp.toBlockShape isRecR A envI pp.ctorNamesAt ∧
  BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k ∧
  (∀ c, c < ctorsAsR.length → ctorsAsR[c]? = some (dR.ctorsM c)) ∧
  (∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
    dR = blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf) ∧
  dR.toLfp ∈ mpC.lfpBlocks ∧
  LfpCover mpC [] ∧
  FormersModelAt (V := V) envI pp.toBlockShape.memberNames mpC dR pp.lps cvTasR
    pp.toBlockShape isRecR ∧
  BlockOverEnv envC pp.toBlockShape.memberNames ∧
  (∀ c ∈ ctorsAsR.flatten, ∀ C, (ctorEntry C (.ctorInfo c.1 pp.nP c.2)).isSome = true →
    C ∈ pp.toBlockShape.memberNames)

end ConLeche.Model
