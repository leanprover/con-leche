module

public import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Cover
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Model.Rules.Inputs
public import ConLeche.SetModel.Access

public section

/-!
# Positivity from the install's run, containers included (lane NESTKERN, session 2)

`blockCtorPos_of_run` (`BlockPosRun.lean`) reads the walk at flat kinds
(its derivation meets no container, so no coverage is needed).  With
the route switch on (`nst = true`, `uniformNested`) the walk accepts
container fields; the derivation's container rules read coverage
(`ContCover`).  This file is the producer at either switch position:

* **coverage** (`ContCover` at the walk's context): `contCover_of`
  from `LfpCover` at the carrier with the block's members exempt — a
  premise here, discharged at the install by the formers' cons
  (`lfpCover_append`, `blockTablesStage_of_gen`);
* **the derivation** of every stored constructor
  (`checkBlockPositivity_derivM`, the one inversion of the run);
* **positivity** per constructor: `blockCtorPos_of_walk`, by induction on
  the derivation (`memberCtorD_mono`, `PosDerivMono.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal CheckM NestCtx NestState
  NestFieldKind BlockParts BlockShape instPisWith nestAbstract nestHoles nestMemberCtor
  openPisAtFvars fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-- The empty relation is a hole relation of any context. -/
theorem holeRel_empty {env : Env} (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (d : Nat) (Δa : List AnnotTerm) :
    HoleRel m φ ctx [] d Δa (fun _ _ => False) where
  dom := fun _ _ h => h.elim
  agree := fun _ _ h => h.elim
  member := fun _ _ _ _ h => h.elim
  frame := fun _ _ h => by simp at h
  dsScoped := fun _ _ h => by simp at h

/-- **Every member constructor of a uniform block is positive along the
tuple order at the hole frame, at either position of the route switch**
(lane NESTKERN, session 2): `blockCtorPos_of_run` with the container
case — at `nst = true`, under coverage at the formers' carrier (some
model with the carrier's readings, the block's members exempt). -/
theorem blockCtorPos_of_run_gen {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true)
    {env : Env} (mp : EnvModelM V μ env) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec)
    {p : BlockParts} {ctorsAs : List (List (ConstantVal × Nat))}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × ConLeche.NestNodes} {nst : Bool}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps μ F) env env.find? env.consts
      p cvTas ctorsAs nst = .ok posKs)
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    (hinst : d.nInst = 0)
    (hlenCA : ctorsAs.length = d.k)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c))
    (hclosed : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true)
    (hnfs : ∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      d.nfFF c j = (posKs.2.1.getD c []).getD j default)
    -- coverage at the walk's carrier, where the walk may meet a container
    (hcov : nst = true → ∃ mk : EnvModelM V μ env, mk.base2 = mp.base2 ∧
      LfpCover mk p.memberNames) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j := by
  cases nst with
  | false =>
    exact blockCtorPos_of_run hμ mp hN hcore hrun hnames hlps hnP hnIdxs hk hinst hlenCA hctorsAs
      hclosed hnfs
  | true =>
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  obtain ⟨mk, hbk, hcovk⟩ := hcov rfl
  obtain ⟨kinds, nfs, nodes⟩ := posKs
  have hcore' : BlockHoleCtxFacts mk.base2 d lps cvTas p₁ isRec := by rw [hbk]; exact hcore
  obtain ⟨cvTa0, fvsP, rest, holes, hcv0, hop0, hholes, hder⟩ :=
    checkBlockPositivity_derivM mk.base2.wf hrun
      (fun cv h => (mk.base2.wf _ (List.mem_of_find?_eq_some
        (hcore'.1 0 cv (by rwa [List.head?_eq_getElem?] at h)).1)).1)
      (fun c cs hc j cA hj => by
        have hck : c < d.k := by rw [← hlenCA]; exact (List.getElem?_eq_some_iff.mp hc).1
        rw [hctorsAs c hck] at hc
        obtain rfl := Option.some.inj hc
        exact (hclosed c j cA hj).1)
  -- coverage at the walk's context
  have hcC : ContCover mk (p.nestCtx fvsP env.find? env.consts) :=
    contCover_of hcovk (fun _ => rfl) rfl
  intro ψ ρp hs c hc j hj
  have hck : c < d.k := by
    have : c < d.k + d.nInst := hc
    omega
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  obtain ⟨crest, ksr, tsr, hcrest, hd, -, -, ⟨ty, hty⟩, -⟩ :=
    hder c (d.ctorsM c) (hctorsAs c hck) j _ hcj
  obtain ⟨hCf, hCb⟩ := hclosed c j _ hcj
  exact blockCtorPos_of_walk mk (Rules.RulesInputs.ofSem mk ψ) hN hcore' hnames hlps hnP hnIdxs
    hk hcv0 hop0 hholes hcj hCf hCb hcrest hd (fun _ => hcC) hty
    (hnfs c j _ hcj) hs

/-! ## The one fact the nested run owes the block step (lane ACCMODEL)

The hole operator's closed tuple at a `Type`-valued frame (W) comes
from ACCESSIBILITY at every block (maintainer ruling 2026-09-24; flat
blocks by `blockAccTuple_of_run_flat`, lane FLATACC): the hole operator is accessible with one
bound `A` of the level, and `closed_of_acc` (`SetModel/Access.lean`)
turns that into its closed tuple (the consumer, `BlockDatum.lean`'s
`hfunZ`).  The premise states the accessibility as a producer would:
everything the constructors' stage knows at the point where it needs (W)
— the datum's records, the positivity run at the switch ON, its links to
the datum, coverage at the walk's carrier, the formers — and the
fields' grading.  Joint
accessibility at the instantiation is an install-time lemma from the
positivity walk's run, like monotonicity; there is no per-inductive
"accessible in its parameter" clause fact (ruling). -/

/-- **OWED (lane ACCMODEL)**: the hole operator of a block the install
walked with the route switch on is ACCESSIBLE, with a bound `A` that is a
set of the level, at every `Type`-valued parameter frame — what
`closed_of_acc` turns into (W).  The premise of the block step at nested
blocks (`declBlock_nested`); with the switch off its twin is
`blockAccTuple_of_run_flat` (no container case, no coverage). -/
@[expose] def NestedAccOwed (V : Type w) [SetTheory V] (μ : ConLeche.CheckMode) (F : Nat) :
    Prop :=
  ∀ {env : Env} (mp : EnvModelM V μ env) {d : BlockData V} {lps : List Name}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool} {p : BlockParts}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × ConLeche.NestNodes},
    BlockNamesOk (V := V) d cvTas →
    BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec →
    BlockHoleFacts mp.base2 d lps →
    ConLeche.checkBlockPositivity (m := CheckM) (fueledOps μ F) env env.find? env.consts
      p cvTas ctorsAs true = .ok posKs →
    p.memberNames = d.memberNames → p.lps = lps → p.nP = d.nP → p.nIdxs = d.nIdxs →
    p.resSort = d.resSort → d.k = d.memberNames.length → d.memberNames.Nodup →
    d.nInst = 0 → ctorsAs.length = d.k →
    (∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) →
    (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true) →
    (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      d.nfFF c j = (posKs.2.1.getD c []).getD j default) →
    (∀ (ψ : Name → Nat) (t : Nat), t < d.k → ∃ cv caps bs s,
      env.find? (d.memberName t) = some (.indInfo cv caps) ∧ cv.levelParams = lps ∧
      cv.type.stripPis (d.nP + d.nIdxAt t) = some (bs, .sort s) ∧ s.eval ψ = d.w ψ) →
    -- coverage at the walk's carrier (the containers' clauses are recorded)
    (∃ mk : EnvModelM V μ env, mk.base2 = mp.base2 ∧ LfpCover mk p.memberNames) →
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp → d.w ψ ≠ 0 →
    (∀ c, c < d.N → IdxOk (d.uM c ψ) ρp (d.IdsM c ψ)) →
    (∀ m, m < d.k → (d.IdsM m ψ).length = d.nIdxAt m) →
    (∀ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
      ∀ X, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) X →
      FieldsOkB (d.w ψ) (d.toLfp.frame ψ ρp X) (d.absF ψ c j)) →
    ∃ A, A ∈ˢ (univ (d.toLfp.w ψ) : V) ∧
      AccTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) d.toLfp.N (d.toLfp.idx ψ ρp)
        (d.toLfp.holeOp ψ ρp) A

omit [SetTheory V] in
/-- **The walk context's sort is the block's level** (lane ACCMODEL,
session 3): the caller's side of the container case's level link
(`n2_sort`) — `NestCtx.sort` is the block's result sort. -/
theorem nestCtx_sort_eval {d : BlockData V} {p : BlockParts} (hR : p.resSort = d.resSort)
    (fvsP : List Expr) (find? : Name → Option ConLeche.ConstantInfo)
    (consts : List ConLeche.ConstantInfo) (ψ : Name → Nat) :
    (p.nestCtx fvsP find? consts).sort.eval ψ = d.w ψ := by
  show p.resSort.eval ψ = d.resSort.eval ψ
  rw [hR]

end ConLeche.Model
