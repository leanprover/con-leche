module

public import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Cover
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Model.Rules.Inputs

public section

/-!
# Positivity from the install's run, containers included (lane NESTKERN, session 2)

The walk accepts container fields; the derivation's container rules read
coverage (`ContCover`).  This file is the producer:

* **coverage** (`ContCover` at the walk's context): `contCover_of`
  from `LfpCover` at the carrier with the block's members exempt — a
  premise here, discharged at the install by the formers' cons
  (`lfpCover_append`, `blockTablesStage_of`);
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


/-- **Every member constructor of a uniform block is positive along the
tuple order at the hole frame** (lane NESTKERN, session 2), under
coverage at the formers' carrier (some model with the carrier's
readings, the block's members exempt). -/
theorem blockCtorPos_of_run {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true)
    {env : Env} (mp : EnvModelM V μ env) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mp.base2 d lps cvTas p₁ isRec)
    {p : BlockParts} {ctorsAs : List (List (ConstantVal × Nat))}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × ConLeche.NestNodes}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps μ F) env env.find? env.consts
      p cvTas ctorsAs = .ok posKs)
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
    (hcov : ∃ mk : EnvModelM V μ env, mk.base2 = mp.base2 ∧
      LfpCover mk p.memberNames) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j := by
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  obtain ⟨mk, hbk, hcovk⟩ := hcov
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
  obtain ⟨crest, ksr, tsr, hcrest, hd, -, ⟨ty, hty⟩, -⟩ :=
    hder c (d.ctorsM c) (hctorsAs c hck) j _ hcj
  obtain ⟨hCf, hCb⟩ := hclosed c j _ hcj
  exact blockCtorPos_of_walk mk (Rules.RulesInputs.ofSem mk ψ) hN hcore' hnames hlps hnP hnIdxs
    hk hcv0 hop0 hholes hcj hCf hCb hcrest hd (fun _ => hcC) hty
    (hnfs c j _ hcj) hs

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
