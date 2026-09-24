module

public import ConLeche.Model.Inductives.BlockPosRun
public import ConLeche.Model.Inductives.LfpCover
public import ConLeche.Model.Inductives.BlockLfpHoles
import ConLeche.Model.Rules.Inputs

public section

/-!
# Positivity from the install's run, containers included (lane NESTKERN, session 2)

`blockCtorPos_of_run` (`BlockPosRun.lean`) reads the walk at flat kinds
(the ContSem provider `contSem_flat`, no container premise).  With the
route switch on (`nst = true`, `uniformNested`) the walk accepts
container fields; its container case is CONTSEM's `contSem`, at the
kind predicate `True` and the state invariant `CacheInv` (every cached
instantiation positive), under coverage (`ContCover`).  This file is the
producer at either switch position:

* **coverage** (`ContCover` at the walk's context): `contCover_of`
  from `LfpCover` at the carrier with the block's members exempt — a
  premise here, discharged at the install by the formers' cons
  (`lfpCover_append`, `blockTablesStage_of_gen`);
* **the cache invariant, threaded** through the block's constructors
  (`checkBlockPositivity_inv_I`): it holds of the empty state
  (`cacheInv_empty`) and every constructor's run keeps it
  (`nestMemberCtor_sem_cont` at the EMPTY hole relation — the invariant
  half of the theorem does not depend on the relation);
* **positivity** per constructor: `blockCtorPos_of_walk` at the
  provider `contSem`.
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
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr)} {nst : Bool}
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
      d.nfFF c j = (posKs.2.getD c []).getD j default)
    -- coverage at the walk's carrier, where the walk may meet a container
    (hcov : nst = true → ∃ mk : EnvModelM V μ env, mk.base2 = mp.base2 ∧
      LfpCover mk p.memberNames) :
    ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
      ∀ c, c < d.toLfp.N → ∀ j, j < d.toLfp.nctors c →
        d.toLfp.CtorPos (d.toLfp.tupRel ψ ρp) ψ c j := by
  cases nst with
  | false =>
    exact blockCtorPos_of_run hμ mp hN hcore hrun hnames hlps hnP hnIdxs hk hinst hctorsAs
      hclosed hnfs
  | true =>
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  obtain ⟨mk, hbk, hcovk⟩ := hcov rfl
  obtain ⟨kinds, nfs⟩ := posKs
  obtain ⟨cvTa0, fvsP, rest, holes, hcv0, hop0, hholes, hall⟩ :=
    ConLeche.checkBlockPositivity_inv_gen hrun
  obtain ⟨cvTa0', fvsP', rest', holes', hcv0', hop0', hholes', hthr⟩ :=
    ConLeche.checkBlockPositivity_inv_I hrun
  rw [hcv0] at hcv0'
  obtain rfl := Option.some.inj hcv0'
  rw [hop0] at hop0'
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using hop0'
  rw [hholes] at hholes'
  obtain rfl := Option.some.inj hholes'
  -- the walk's context, and coverage at it
  generalize hctx : p.nestCtx fvsP env.find? env.consts = ctx at hholes hall hthr
  have hcN : ctx.names = p.memberNames := by rw [← hctx]; rfl
  have hcC : ContCover mk ctx :=
    contCover_of (by rw [hcN]; exact hcovk) (fun n => by rw [← hctx]; rfl) (by rw [← hctx]; rfl)
  have hcore' : BlockHoleCtxFacts mk.base2 d lps cvTas p₁ isRec := by rw [hbk]; exact hcore
  intro ψ ρp hs c hc j hj
  have hck : c < d.k := by
    have : c < d.k + d.nInst := hc
    omega
  have hin := Rules.RulesInputs.ofSem mk ψ
  -- the cache invariant, threaded: every block constructor's run keeps it
  have hstep : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∀ crest,
      instPisWith fvsP (nestAbstract ctx holes cA.1.type) = some crest →
      ∀ st₀ ks tyN st₁, (nfs.getD c []).getD j default = tyN → CacheInv mk ψ ctx st₀ →
        nestMemberCtor (fueledOps .verified F) env ctx cA.2 crest st₀ = .ok (ks, tyN, st₁) →
        CacheInv mk ψ ctx st₁ := by
    intro c' cs hcs j' cA hcA crest hcrest st₀ ks tyN st₁ hnf hI hm
    have hc' : c' < d.k := by
      rw [← hlenCA]; exact (List.getElem?_eq_some_iff.mp hcs).1
    rw [hctorsAs c' hc'] at hcs
    obtain rfl := Option.some.inj hcs
    obtain ⟨hCf, hCb⟩ := hclosed c' j' cA hcA
    obtain ⟨crest', -, hcrest', -, -, ⟨ty, hty⟩, -⟩ :=
      hall c' (d.ctorsM c') (hctorsAs c' hc') j' cA hcA
    rw [← hctx] at hcrest hcrest' hm hty
    rw [hcrest] at hcrest'
    obtain rfl := Option.some.inj hcrest'
    obtain ⟨ab, abN, hhi, hca, -, -, -, -, hfr, hCP, hgr, -⟩ :=
      blockCtorHoleCtx hin hN hcore' hnames hlps hnP hnIdxs hk hcv0 hop0
        (by rw [hctx]; exact hholes) hcA hCf hCb hcrest hty hm
        (by rw [hnfs c' j' cA hcA]; exact hnf)
    rw [← hhi] at hca hgr hfr hCP
    rw [hctx] at hca hgr hfr hCP hm
    exact (nestMemberCtor_sem_cont mk hin hcC F hm hfr hI hCP hca hgr
      (holeRel_empty mk.base2 ψ ctx _ _)).2
  -- the constructor's own run, from a state satisfying it
  obtain ⟨crest, st₀, ks, tyN, st₁, hcrest, hI₀, hm, hnf⟩ :=
    hthr (CacheInv mk ψ ctx) (cacheInv_empty mk ctx) hstep c (d.ctorsM c) (hctorsAs c hck) j
      _ (List.getElem?_eq_getElem hj)
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  obtain ⟨hCf, hCb⟩ := hclosed c j _ hcj
  obtain ⟨crest', -, hcrest', -, -, ⟨ty, hty⟩, -⟩ :=
    hall c (d.ctorsM c) (hctorsAs c hck) j _ hcj
  rw [hcrest] at hcrest'
  obtain rfl := Option.some.inj hcrest'
  rw [← hctx] at hcrest hm hty
  exact blockCtorPos_of_walk hin hN hcore' hnames hlps hnP hnIdxs hk hcv0 hop0
    (by rw [hctx]; exact hholes) hcj hCf hCb hcrest (P := fun _ => True)
    (I := CacheInv mk ψ (p.nestCtx fvsP env.find? env.consts))
    (fun rec hrec => contSem mk hin (by rw [hctx]; exact hcC) F rec hrec) hm
    (fun _ _ => trivial) (by rw [hctx]; exact hI₀) hty
    (by rw [hnfs c j _ hcj]; exact hnf) hs

/-! ## The one fact the nested run owes the block step (lane NESTW)

With the route switch off, the hole operator's closed tuple at a
`Type`-valued frame (W) comes from the flat presentation of the fields
with holes (`blockHoleClosed_of`, `StoredFieldsFlat`).  A container
field is not flat; (W) for nested blocks is lane NESTW's
(`closed_of_wide_groups`, `WideAt.closed`).  Its statement is the
producer's: everything the constructors' stage knows at the point where
it needs (W) — the datum's records, the positivity run at the switch
ON, its links to the datum, coverage at the walk's carrier, the formers
— and `blockHoleClosed_of`'s own inputs but the flat presentation. -/

/-- **OWED by lane NESTW (L7)**: (W) for the hole operator of a block the
install walked with the route switch on — the premise of the block step
at nested blocks (`declBlock_nested`); with the switch off it is
`blockHoleClosed_of` at the flat presentation. -/
@[expose] def NestedClosedOwed (V : Type w) [SetTheory V] (μ : ConLeche.CheckMode) (F : Nat) :
    Prop :=
  ∀ {env : Env} (mp : EnvModelM V μ env) {d : BlockData V} {lps : List Name}
    {cvTas : List ConstantVal} {p₁ : BlockShape} {isRec : Bool} {p : BlockParts}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr)},
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
      d.nfFF c j = (posKs.2.getD c []).getD j default) →
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
    ∃ L, IsClosedTuple (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) (d.toLfp.holeOp ψ ρp) L

end ConLeche.Model
