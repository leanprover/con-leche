module

public import ConLeche.Model.Inductives.DeclNative
public import ConLeche.Model.Inductives.BlockDatum
public import ConLeche.Semantics.Inductives.DeclBlock
public section

/-!
# The uniform block install's records (#315)

The records the uniform block step (`declBlock`,
`Model/Inductives/DeclBlockStep.lean`) is stated over: the recursors' stage's obligation
(`BlockRecStagedT`), the block over an older environment, the positivity
model at the formers' environment, and the recursors' stage's shared
context (`RecCtxBase`; the stage's own, with its run, is `GenRecCtx`,
`GenRecAssembly.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockShape BlockShape MemberShape RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The recursor stage's obligation -/

/-- **What the recursors' stage owes the tables' stage** (conjunct ⑧
of `declBlock`, which `DeclBlockRun` leaves opaque): a carrier at the post-recursor environment that
* reads every name the pre-recursor environment stores as that
  environment's carrier does (`acval` agreement),
* finds everything it found (`find?` monotonicity),
* reads every pre-recursor-bounded expression the same way
  (`denote` stability — the constructors' and formers' TYPE
  readings cross the conses).

It is three cons-monotonicities and mentions no `BlockData`. -/
@[expose] def BlockRecStagedAt {V : Type w} [SetTheory V]
    (envC env₃ : Env) (mpC : EnvModelM V envC) : Prop :=
  ∃ mp' : EnvModelM V env₃,
    (∀ n : Name, (envC.find? n).isSome = true → mp'.base2.acval n = mpC.base2.acval n) ∧
    (∀ (n : Name) (c : ConstantInfo), envC.find? n = some c → env₃.find? n = some c) ∧
    (∀ (ψ : Name → Nat) (dd : Nat) (e : Expr), ConstsBound envC e →
      denote mp'.base2.acval env₃ ψ dd e = denote mpC.base2.acval envC ψ dd e)


/-- **The tables' invariant crosses the recursors' conses**, by the
three facts of `BlockRecStagedAt` and nothing else. -/
theorem BlockTablesCore.consRecs {envC envR : Env} {mC : EnvModel V envC} {mR : EnvModel V envR}
    {d : BlockData V} {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : ConLeche.BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → Term}
    (h : BlockTablesCore mC d lps cvTasAll p₁ isRec A)
    (hag : ∀ n : Name, (envC.find? n).isSome = true → mR.acval n = mC.acval n)
    (hfind : ∀ (n : Name) (c : ConstantInfo), envC.find? n = some c → envR.find? n = some c)
    (hden : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr), ConstsBound envC e →
      denote mR.acval envR ψ dd e = denote mC.acval envC ψ dd e) :
    BlockTablesCore mR d lps cvTasAll p₁ isRec A := by
  obtain ⟨hform, hctor⟩ := h
  have hsome : ∀ n : Name, (envC.find? n).isSome = true → (envR.find? n).isSome = true := by
    intro n hn
    cases hc : envC.find? n with
    | none => rw [hc] at hn; exact nomatch hn
    | some c => rw [hfind n c hc]; rfl
  refine ⟨fun c cvTb hc => ?_, fun c j cA hj => ?_⟩
  · obtain ⟨hfindT, hres, hleaf, hFD⟩ := hform c cvTb hc
    refine ⟨hfindT.of_ext hfind hden, Expr.constsResolve_of_find hsome hres, fun ψ => ?_, ?_⟩
    · obtain ⟨cvS, hfS, -⟩ := hfindT
      rw [hag cvTb.name (by rw [hfS]; rfl)]; exact hleaf ψ
    · exact ⟨fun ψ => by
        rw [hden ψ 0 cvTb.type (constsBound_of_constsResolve _ hres)]; exact hFD.read ψ,
      hFD.len, hFD.okTy, hFD.below, hFD.params, hFD.syn⟩
  · obtain ⟨hfindC, hlps, hres, hread, hleaf⟩ := hctor c j cA hj
    refine ⟨hfind _ _ hfindC, hlps, Expr.constsResolve_of_find hsome hres, fun ψ => ?_,
      fun ψ => ?_⟩
    · rw [hden ψ 0 cA.1.type (constsBound_of_constsResolve _ hres)]; exact hread ψ
    · rw [hag cA.1.name (by rw [hfindC]; rfl)]; exact hleaf ψ

/-- **The recursors' stage's obligation at the cons at the majors**:
`BlockRecStagedAt`'s three cons-monotonicities at
`consBlockRecsT`, the family consed with each recursor's rules at ITS
major (`.nested` at an outside one). -/
@[expose] def BlockRecStagedT {V : Type w} [SetTheory V]
    (envC : Env) (p : ConLeche.BlockShape)
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V envC) : Prop :=
  BlockRecStagedAt envC
    (ConLeche.consBlockRecsT p 0 out envC) mpC


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
    (mpC : EnvModelM V envC) (d : BlockData V) (lps : List Name) (cvTas : List ConstantVal)
    (p : BlockShape) (isRec : Bool) : Prop :=
  ∃ mk : EnvModelM V envI, LfpCover mk names ∧ (∀ F, FamilyRead mk F) ∧
    (∀ F, FamilyRead mpC F) ∧ (∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks) ∧
    (∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n) ∧
    (∀ D ∈ mpC.lfpBlocks, D = d.toLfp ∨ D ∈ mk.lfpBlocks) ∧
    -- the member constructors' hole contexts at the formers' model (the
    -- node-semantics induction's root)
    BlockHoleCtxFacts mk.base2 d lps cvTas p isRec ∧
    -- a reading at the formers' environment is one at the constructors'
    ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : Term},
      denote mk.base2.acval envI ψ dd e = some ea → denote mpC.base2.acval envC ψ dd e = some ea

/-- **The recursors' stage's context, without the stage's own run**: what
`GenRecCtx` (the generated stage, `GenRecAssembly.lean`) holds — the positivity run, the constructors'
cons, the block's representation and model records, the block over the
input environment.  The node route's facts that read no recursor run take
this (`nodeListFacts_of`, `dynCtx_of`). -/
@[expose] def RecCtxBase (V : Type w) [SetTheory V] (F : Nat)
    (envC envI : Env) (pp : BlockShape)
    (mpC : EnvModelM V envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → Term)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr))
    (posR : ConLeche.NestState) : Prop :=
  ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps .verified F) envI
      envI.find? pp = .ok (kindsR, nfsR, posR) ∧
  envC = ConLeche.consBlockCtors pp.nP pp.memberCtors envI ∧
  pp.memberCtors.map (·.map (fun cA => (cA.1.name, cA.2)))
    = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) ∧
  pp.memberNames.Nodup ∧
  BlockNamesOk (V := V) dR pp.formers ∧
  BlockCtorsStage (V := V) F dR pp.lps pp.formers pp isRecR A envI pp.ctorNamesAt ∧
  BlockCtorsCore mpC.base2 dR pp.lps pp.formers pp isRecR A dR.k ∧
  (∀ c, c < pp.memberCtors.length → pp.memberCtors[c]? = some (dR.ctorsM c)) ∧
  (∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List Term),
    dR = blockDataOf V pp pk uOfD ppsOf) ∧
  dR.toLfp ∈ mpC.lfpBlocks ∧
  LfpCover mpC [] ∧
  FormersModelAt (V := V) envI pp.memberNames mpC dR pp.lps pp.formers
    pp isRecR ∧
  BlockOverEnv envC pp.memberNames ∧
  (∀ c ∈ pp.memberCtors.flatten, envI.find? c.1.name = none ∧
    ∀ C, (ctorEntry C (.ctorInfo c.1 pp.nP c.2)).isSome = true →
      C ∈ pp.memberNames)

end ConLeche.Model
