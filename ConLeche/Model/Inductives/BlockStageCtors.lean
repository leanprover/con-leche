module

import ConLeche.Model.Inductives.BlockCtorsLoop
import ConLeche.Model.Inductives.FixCtorCross
import ConLeche.Model.Inductives.BlockCaps
import ConLeche.Model.Inductives.BlockRep
public import ConLeche.Model.Inductives.BlockAbsRead
import ConLeche.Model.Annot.LfpHoleOp
import ConLeche.Model.Inductives.BlockHoleFold
public import ConLeche.Model.Inductives.BlockLfpHoles
import ConLeche.Semantics.Inductives.DeclSumEta
public section

/-!
# The constructors' stage at a block member (task #315 M3)

`BlockCtorsCore`: what the `k` constructor loops thread — the `k`
formers found with their leaves and their telescope readings, the
capability families still free, every member's constructors' data at
the carrier, and the constructors consed SO FAR with their leaves.
It is `declNative`'s `Inv` at `k` members, and it is exactly what a
constructor cons preserves (`BlockCtorsCore.cons`).

`stageBlockCtorsAt` is `declNative`'s member-local half at member `m`:
the fibre law of the member's own fixpoint leaf (`blockFold_of` over
the member's REAL chains, built here from the block's operator premise
and the dummy/real identification), the member's capability laws
(`blockCapsLawsAt`), and then `blockCtorsLoop` — so the stage's output
is the carrier after `consSumCtors` of that member's constructors,
with the core invariant one member further on.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  InductiveShape BlockShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The invariant the member loops thread -/

/-- **The block install's carrier invariant at the constructors'
stage**, `nc` members' constructors consed: the `k` formers with their
leaves and telescope readings, the capability families free, every
member's constructors' readings, the earlier members' constructors
stored with their leaves. -/
@[expose] def BlockCtorsCore {env : Env} (m' : EnvModel V env) (d : BlockData V)
    (lps : List Name) (cvTasAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm) (nc : Nat) : Prop :=
  -- the `k` formers
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      env.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p₁ c isRec)) ∧
      cvTb.type.constsResolve env = true ∧
      (∀ ψ, m'.acval cvTb.name ψ = A c ψ) ∧
      FormerData m' cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) ∧
  -- a capable member's projection-function family is still free
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      (ConLeche.blockCapsAt p₁ c isRec).unitlike = false →
      (ConLeche.blockCapsAt p₁ c isRec).eta = true →
      env.find? (projFnName cvTb.name 0) = none) ∧
  -- every member's constructors resolve and read, their fields with
  -- holes the walked term's reading
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      cA.1.type.constsResolve env = true ∧
      (∀ e ∈ d.idxF c j, e.constsResolve env = true) ∧
      BlockCtorDataI m' (d.memberName c) lps cA.1 d.nP cA.2 (d.nIdxAt c) d.resSort d.isProp
        d.large (d.idxF c j) (d.dsF c j) (d.esF c j) (d.srcsF c j) (d.fvsPF c j)
        (d.xFvsF c j) (d.xrestF c j) ∧
      BlockAbsRead m' d lps c j cA) ∧
  -- the members before `nc`: their constructors are stored with their leaves
  (∀ c, c < nc → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      env.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) ∧ cA.1.levelParams = lps ∧
      ∀ ψ, m'.acval cA.1.name ψ
        = sumMkAV (d.w ψ) j (d.dsF c j ψ) (((d.dsF c j ψ).drop d.nP).map (·.2.2))
            (uChains (d.Fss c ψ)))

/-- **The block's names, statically**: a member's name is its former's,
and every constructor is a member's. -/
@[expose] def BlockNamesOk (d : BlockData V) (cvTasAll : List ConstantVal) : Prop :=
  (∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb → d.memberName c = cvTb.name) ∧
  (∀ (c j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA → c < cvTasAll.length) ∧
  cvTasAll.length = d.k

/-- **The core invariant survives a constructor's cons.**  A stored
name is not the fresh one, so nothing found before is disturbed; the
readings cross by `FormerData.cross` and `BlockCtorDataI.cross`. -/
theorem BlockCtorsCore.cons {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm} {nc : Nat}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (h : BlockCtorsCore m' d lps cvTasAll p₁ isRec A nc)
    {cA : ConstantVal × Nat} {B : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? cA.1.name = none)
    (hpshape : cA.1.name.isProjFnShape = false)
    (mC : EnvModel V ⟨.ctorInfo cA.1 d.nP cA.2 :: env.consts⟩)
    (hac : mC.acval = acvalWith m'.acval cA.1.name B) :
    BlockCtorsCore mC d lps cvTasAll p₁ isRec A nc := by
  obtain ⟨hnameOf, hctorLt, hlenCv⟩ := hN
  obtain ⟨hform, hfr, hdata, hconsed⟩ := h
  have hcross : ∀ e : Expr, ConsCrossAt (.ctorInfo cA.1 d.nP cA.2) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ hh => nomatch hh)
  -- a name already stored is not the fresh one
  have hne : ∀ n : Name, (env.find? n).isSome = true → n ≠ cA.1.name := by
    intro n hn hnn
    rw [hnn, hfresh] at hn
    exact nomatch hn
  have hneOf : ∀ (c : Nat) (cvTb : ConstantVal), cvTasAll[c]? = some cvTb →
      cvTb.name ≠ cA.1.name := by
    intro c cvTb hc
    exact hne _ (by rw [(hform c cvTb hc).1]; rfl)
  refine ⟨fun c cvTb hc => ?_, fun c cvTb hc hU he => ?_, fun c j cB hj => ?_,
    fun c hc j cB hj => ?_⟩
  · obtain ⟨hfind, hres, hleaf, hFD⟩ := hform c cvTb hc
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfind,
      Expr.constsResolve_mono hres, fun ψ => ?_, ?_⟩
    · rw [hac]
      show acvalWith m'.acval cA.1.name B cvTb.name ψ = _
      rw [acvalWith_ne (hneOf c cvTb hc)]
      exact hleaf ψ
    · exact hFD.cross (c₀ := .ctorInfo cA.1 d.nP cA.2) hfresh (hcross _)
        (constsBound_of_constsResolve _ hres) mC hac
  · have hnp : ¬ ((ConstantInfo.ctorInfo cA.1 d.nP cA.2).name = projFnName cvTb.name 0) := by
      intro hh
      have hh' : cA.1.name = projFnName cvTb.name 0 := hh
      have := projFnName_isProjFnShape cvTb.name 0
      rw [← hh', hpshape] at this
      exact nomatch this
    rw [ConLeche.Env.find?_cons, if_neg hnp]
    exact hfr c cvTb hc hU he
  · obtain ⟨hres, hresI, hD, hR⟩ := hdata c j cB hj
    refine ⟨Expr.constsResolve_mono hres, fun e he => Expr.constsResolve_mono (hresI e he), ?_,
      hR.cross (c₀ := .ctorInfo cA.1 d.nP cA.2) hfresh hcross (constsBound_of_constsResolve _ hres)
        mC hac⟩
    refine hD.cross (c₀ := .ctorInfo cA.1 d.nP cA.2) hfresh ?_ hcross
      (constsBound_of_constsResolve _ hres)
      (fun e he => constsBound_of_constsResolve _ (hresI e he)) mC hac
    obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTasAll[c]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (hctorLt c j cB hj)⟩
    rw [hnameOf c cvTb hcvTb]
    exact hneOf c cvTb hcvTb
  · obtain ⟨hfind, hlps, hleaf⟩ := hconsed c hc j cB hj
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfind, hlps, fun ψ => ?_⟩
    rw [hac]
    show acvalWith m'.acval cA.1.name B cB.1.name ψ = _
    rw [acvalWith_ne (hne _ (by rw [hfind]; rfl))]
    exact hleaf ψ

/-! ## The loop over the members -/

/-- **What the constructors' stage needs of every member** — the
per-member hypotheses of `stageBlockCtorsAt`, gathered so that the
loop over the `k` members carries ONE obligation. -/
structure BlockCtorsStage (μ : CheckMode) (F : Nat) (d : BlockData V) (lps : List Name)
    (cvTasAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (envI : Env) (ctorsOf : Name → List Name) : Prop where
  /-- the leaves the `k` formers were consed with: the block operator at
  the HOLE chains (lane HOLE2, stage B — charter item 2) -/
  leaf : ∀ (c : Nat) (ψ : Name → Nat), A c ψ
    = blockTyG d.k (d.w ψ) (fun c' => d.uM c' ψ) (fun c' => d.IdsM c' ψ) (d.toLfp.holeChains ψ)
        (d.ppsM c ψ) c
  /-- the hole chains are graded at every parameter frame -/
  holeOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    BlockChainsOkG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ)
  /-- the hole operator is monotone and has a closed tuple at every
  parameter frame (its fixed-point equation's premises) -/
  holeFun : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    MonoTuple (d.w ψ) d.k (blockIdx (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
      (blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ)) ∧
    ∃ L, IsClosedTuple (d.w ψ) d.k (blockIdx (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
      (blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ)) L
  /-- the block has no instance component -/
  inst : d.nInst = 0
  /-- the stored field shape facts, the members' leaves the formers' -/
  shapes : ∀ (ψ : Name → Nat) (c : Nat), c < d.k → ∀ j, j < (d.ctorsM c).length →
    StoredFieldShapes V d.k d.nP (d.w ψ) d.nIdxAt (fun t => A t ψ) (d.params ψ).reverse
      (d.absF ψ c j) ((d.Fss c ψ).getD j [])
  /-- every member's constructors, as checked at the formers' environment -/
  ctors : ∀ (m : Nat) (cvTa : ConstantVal), m < d.k → cvTasAll[m]? = some cvTa →
    ∃ (cs : List (ConstantVal × Nat)) (sortss : List (List Level)),
      ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI cvTa.name lps d.nP (d.nIdxAt m)
        d.resSort d.isProp d.large cvTa cs = .ok (d.ctorsM m, sortss)
  nodup : ∀ m, m < d.k → ((d.ctorsM m).map (·.1.name)).Nodup
  out : ∀ (m : Nat) (cvTa : ConstantVal), m < d.k → cvTasAll[m]? = some cvTa →
    ∀ cA ∈ d.ctorsM m, ∀ T'' ∈ d.memberNames, T'' ≠ cvTa.name → cA.1.name ∉ ctorsOf T''
  lpsT : ∀ (m : Nat) (cvTa : ConstantVal), m < d.k → cvTasAll[m]? = some cvTa →
    cvTa.levelParams = lps
  lpsA : ∀ m, m < d.k → ∀ cA ∈ d.ctorsM m, cA.1.levelParams = lps
  pshape : ∀ m, m < d.k → ∀ cA ∈ d.ctorsM m, cA.1.name.isProjFnShape = false
  ndBlock : ∀ m, m < d.k → ∀ (c : Nat), c ≠ m → ∀ (j : Nat) (cB : ConstantVal × Nat),
    (d.ctorsM c)[j]? = some cB → cB.1.name ∉ (d.ctorsM m).map (·.1.name)
  paramsOf : ∀ m, m < d.k → ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
    ∀ c, c < d.k → Sat V (((d.ppsM c ψ).take d.nP).map (·.2.2)).reverse ρp
  lenPps : ∀ (c : Nat) (ψ : Name → Nat), c < d.k → (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length
  lenIds : ∀ m, m < d.k → ∀ ψ : Name → Nat, (d.IdsM m ψ).length = d.nIdxAt m
  /-- the members' index telescopes are graded at every parameter frame -/
  idxOk : ∀ m, m < d.k → ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρp →
    BlockIdxOk (V := V) d.k (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ)
  frames : ∀ m, m < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρ ↔
        Sat V (((d.dsF m j ψ).take d.nP).map (·.2.2)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.dsF m j ψ).take d.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (d.w ψ) ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) ∧
        FieldsValid ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) ∧
        (∀ bs : List V, SpineFit ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) bs →
          SpineFit ρ (d.IdsM m ψ) (idxValsAt ρ (d.esF m j ψ) bs)))
  capsU : ∀ m, m < d.k → ∀ (cvTa : ConstantVal), cvTasAll[m]? = some cvTa →
    ∀ {env' : Env} (m' : EnvModel V env') (kk : Nat) (cA : ConstantVal × Nat),
    (d.ctorsM m)[kk]? = some cA →
    (ConLeche.blockCapsAt p₁ m isRec).unitlike = true →
    FormerData m' cvTa (d.nP + d.nIdxAt m) d.resSort (d.ppsM m) →
    (∀ ψ, m'.acval cvTa.name ψ = A m ψ) →
    (∀ ψ, m'.acval cA.1.name ψ = sumMkAV (d.w ψ) kk (d.dsF m kk ψ)
      (((d.dsF m kk ψ).drop d.nP).map (·.2.2)) (uChains (d.Fss m ψ))) →
    CapsLawsAt m' cvTa.name cvTa (ConLeche.blockCapsAt p₁ m isRec)

/-! ## The stage at one member -/

/-- **The constructors' hole facts, from the stage's records** (at any
number of members' constructors consed). -/
theorem blockHoleFacts_of_stage {F : Nat} {envC envI : Env} {mo : EnvModel V envC}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {ctorsOf : Name → List Name} {nc : Nat}
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTas p₁ isRec A envI ctorsOf)
    (hcore : BlockCtorsCore mo d lps cvTas p₁ isRec A nc) (hk0 : 0 < d.k) :
    BlockHoleFacts mo d lps := by
  have hNk : d.N = d.k := by rw [BlockData.N, hS.inst]; rfl
  refine ⟨fun c _ j cA hj => (hcore.2.2.1 c j cA hj).2.2.1, fun ψ c hc j hj => ?_,
      fun ψ => ?_, fun ψ mm hmm => ?_,
      fun ψ mm hmm ρ h => hS.paramsOf 0 hk0 ψ ρ h mm hmm,
      fun ψ mm hmm ρ h => hS.paramsOf mm hmm ψ ρ h 0 hk0, fun ψ c hc j hj => ?_⟩
  · refine (hS.shapes ψ c (by rw [← hNk]; exact hc) j hj).congr_leaf fun t ht => ?_
    obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
    rw [hN.1 t cvTb hcvTb]
    exact ((hcore.1 t cvTb hcvTb).2.2.1 ψ).symm
  · show (((d.ppsM 0 ψ).take d.nP).map (·.2.2)).length = d.nP
    rw [List.length_map, List.length_take, hS.lenPps 0 ψ hk0]
    omega
  · show (((d.ppsM mm ψ).take d.nP).map (·.2.2)).length = d.nP
    rw [List.length_map, List.length_take, hS.lenPps mm ψ hmm]
    omega
  · have hck : c < d.k := by rw [← hNk]; exact hc
    have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
    rw [show (d.Ess c ψ).getD j [] = d.esF c j ψ from essOfR_fixCtorDataList_getD hcj,
      ((hcore.2.2.1 c j _ hcj).2.2.1).lenE ψ, hS.lenIds c hck ψ]

set_option maxHeartbeats 1600000 in
/-- **The constructors' stage at one block member**: `declNative`'s
member-local half at member `m`.  The member's own fibre law is the
member's leaf on the hole chains folded by the override law
(`blockHoleFold`: the stored fields are the fields with holes read at
the leaves' frame); with the member's capability laws it feeds
`blockCtorsLoop`; the carrier that comes out is the one after that
member's `consSumCtors`, with the core invariant one member on. -/
theorem stageBlockCtorsAt (hμ : μ.verifiedChecks = true) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
   
    {envI env : Env} {ctorsOf : Name → List Name} {m : Nat} {cvTa : ConstantVal}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTasAll p₁ isRec A envI ctorsOf)
    (hm : m < d.k) (hcvTa : cvTasAll[m]? = some cvTa)
    (mp : EnvModelM V μ env)
    (hE : ConLeche.BlockEtaInv env d.memberNames ctorsOf)
    (hinv : BlockCtorsCore mp.base2 d lps cvTasAll p₁ isRec A m)
    (hfreshC : ∀ c, m ≤ c → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      env.find? cA.1.name = none) :
    ∃ mp' : EnvModelM V μ (ConLeche.consSumCtors d.nP (d.ctorsM m) env),
      ConLeche.BlockEtaInv (ConLeche.consSumCtors d.nP (d.ctorsM m) env) d.memberNames ctorsOf ∧
      BlockCtorsCore mp'.base2 d lps cvTasAll p₁ isRec A (m + 1) ∧
      ∀ c, m + 1 ≤ c → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
        (ConLeche.consSumCtors d.nP (d.ctorsM m) env).find? cA.1.name = none := by
  have hH : BlockHoleFacts mp.base2 d lps := blockHoleFacts_of_stage hN hS hinv (by omega)
  obtain ⟨ctors, sortss, hCtors⟩ := hS.ctors m cvTa hm hcvTa
  have hframes := hS.frames m hm
  have hlpsA := hS.lpsA m hm
  obtain ⟨hnameOf, hctorLt, hlenCv⟩ := hN
  obtain ⟨hform, hfrP, hdata, hconsed⟩ := hinv
  have hTname : d.memberName m = cvTa.name := hnameOf m cvTa hcvTa
  obtain ⟨hfindT, hresT, hleafT, hFD⟩ := hform m cvTa hcvTa
  -- ## the formers' leaves: closed, and the members' values at the carrier
  have hcvOf : ∀ c, c < d.k → ∃ cvTb, cvTasAll[c]? = some cvTb :=
    fun c hc => ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hc)⟩
  have hcl : ∀ c, c < d.k → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A c ψ).erase := by
    intro c hc ψ
    obtain ⟨cvTb, hcvTb⟩ := hcvOf c hc
    have := mp.base2.cval_closedL cvTb.name ψ
    rwa [(hform c cvTb hcvTb).2.2.1 ψ] at this
  have hacv : ∀ c, c < d.k → ∀ ψ : Name → Nat, mp.base2.acval (d.memberName c) ψ = A c ψ := by
    intro c hc ψ
    obtain ⟨cvTb, hcvTb⟩ := hcvOf c hc
    rw [hnameOf c cvTb hcvTb]
    exact (hform c cvTb hcvTb).2.2.1 ψ
  -- ## the member's data, by position
  have hFssEq : ∀ ψ : Name → Nat,
      d.Fss m ψ = fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0) :=
    fun ψ => fssOfR_fixCtorDataList _ _ _ _ _ _ _ _ _
  have hEssEq : ∀ ψ : Name → Nat,
      d.Ess m ψ = essOf (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0) :=
    fun ψ => essOfR_fixCtorDataList _ _ _ _ _ _ _ _
  -- ## the fibre law at the member's own index readings: the override law
  have hfold : ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM m)[j]? = some cA →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((d.dsF m j ψ).drop d.nP).map (·.2.2)) bs →
        interp V (consList bs ρ)
            (AnnotTerm.mkAppN (A m ψ) (paramBvars d.nP cA.2 ++ d.esF m j ψ))
          = sumSet (d.w ψ) (sumFibre (d.w ψ)
              (consList (idxValsAt ρ (d.esF m j ψ) bs) ρ)
              (rChains (d.nIdxAt m) (d.nIdxAt m)
                (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0))
                (essOf (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)))) := by
    intro j cA hj ψ ρ hρ bs hsp
    have hs0 : Sat V (d.params ψ).reverse ρ := hS.paramsOf m hm ψ ρ hρ 0 (by omega)
    have hD := (hdata m j cA hj).2.2.1
    have hlenB : bs.length = cA.2 := by rw [hsp.length_eq]; simp [hD.len ψ]
    have hspE : SpineFit ρ (d.IdsM m ψ) (idxValsAt ρ (d.esF m j ψ) bs) :=
      ((hframes j cA hj).2 ψ ρ (((hframes j cA hj).1 ψ ρ).mp hρ)).2.2 bs hsp
    have hfl := blockHoleFold hH hS.inst (fun c _ => hS.leaf c ψ) hs0
      (fun c hc => hS.lenPps c ψ hc) (hS.idxOk m hm ψ ρ hρ) (hS.holeOk ψ ρ hs0)
      (hS.holeFun ψ ρ hs0).1 (hS.holeFun ψ ρ hs0).2 hm
      (fun j' hj' => blockOverride hH (fun t ht => hacv t ht ψ) ρ hs0
        (show m < d.N by simp [BlockData.N, hS.inst]; exact hm) hj') hspE
    rw [ConLeche.Semantics.interp_mkAppN_foldl, List.map_append, paramBvars_eq_paramBvarsAt,
      map_paramBvarsAt_interp (ρp := ρ) (e := cA.2)
        (fun j' => by rw [← hlenB]; exact consList_apply_add bs ρ j'),
      ← frameIdx_eq_reverse_map, interp_closed V (hcl m hm ψ) _ (shiftE d.nP 0 ρ)]
    rw [show (d.esF m j ψ).map (interp V (consList bs ρ)) = idxValsAt ρ (d.esF m j ψ) bs from rfl,
      hfl, hS.lenIds m hm ψ, hFssEq ψ, hEssEq ψ]
  -- ## the capability laws at every carrier the loop reaches
  have hTlawsOf : ∀ {env' : Env} (m' : EnvModel V env') (kk : Nat) (cA : ConstantVal × Nat),
      (d.ctorsM m)[kk]? = some cA →
      BlockCtorsCore m' d lps cvTasAll p₁ isRec A m →
      FormerData m' cvTa (d.nP + d.nIdxAt m) d.resSort (d.ppsM m) →
      (∀ ψ, m'.acval (d.memberName m) ψ = A m ψ) →
      (∀ ψ, m'.acval cA.1.name ψ = sumMkAV (d.w ψ) kk (d.dsF m kk ψ)
        (((d.dsF m kk ψ).drop d.nP).map (·.2.2))
        (uChains (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)))) →
      CapsLawsAt m' (d.memberName m) cvTa (ConLeche.blockCapsAt p₁ m isRec) := by
    intro env' m' kk cA hkk hinv' hFD' hleaf' hleafC'
    rw [hTname] at hleaf' ⊢
    by_cases hu : (ConLeche.blockCapsAt p₁ m isRec).unitlike = true
    · refine hS.capsU m hm cvTa hcvTa m' kk cA hkk hu hFD' hleaf' (fun ψ => ?_)
      rw [hleafC' ψ, hFssEq ψ]
    · have hU : (ConLeche.blockCapsAt p₁ m isRec).unitlike = false := by simpa using hu
      exact blockCapsLawsAt_vacuous m' hU (hinv'.2.1 m cvTa hcvTa hU)
  -- ## the data's level-parameter invariance and bounds
  have hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ₁ (d.ctorsM m) 0)
        = fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ₂ (d.ctorsM m) 0) := by
    intro ψ₁ ψ₂ hφ
    have hcds : ctorDataList (d.dsF m) (d.esF m) ψ₁ (d.ctorsM m) 0
        = ctorDataList (d.dsF m) (d.esF m) ψ₂ (d.ctorsM m) 0 := by
      refine ctorDataList_params fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, (d.ctorsM m)[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
      exact (hdata m i cAi hi').2.2.1.params ψ₁ ψ₂
        (fun q hq => hφ q (by rw [← hlpsA cAi (List.mem_of_getElem? hi')]; exact hq))
    rw [hcds]
  have hcdMem : ∀ (ψ : Name → Nat) (i : Nat) (cd : CtorDatum),
      (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)[i]? = some cd →
      ∃ cA, (d.ctorsM m)[i]? = some cA ∧ cd = (cA.1.name, cA.2, d.dsF m i ψ, d.esF m i ψ) := by
    intro ψ i cd hi
    rw [ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : (d.ctorsM m)[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some cA => rw [h] at hi; exact ⟨cA, rfl, (Option.some.inj hi).symm⟩
  have hFssBelow : ∀ ψ : Name → Nat,
      ∀ Fs ∈ fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0),
        FieldsBelow d.nP Fs := by
    intro ψ Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    obtain ⟨cA, hiA, rfl⟩ := hcdMem ψ i cd hi
    have := (DomsBelow.drop d.nP ((hdata m i cA hiA).2.2.1.below ψ)).fields
    rwa [Nat.zero_add] at this
  have hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (d.w ψ) ρ (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)) ∧
      SumFieldsValid ρ (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)) := by
    intro ψ ρ hρ
    constructor
    · intro Fs hFs
      obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      obtain ⟨cA, hiA, rfl⟩ := hcdMem ψ i cd hi
      exact ((hframes i cA hiA).2 ψ ρ (((hframes i cA hiA).1 ψ ρ).mp hρ)).1
    · intro Fs hFs
      obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      obtain ⟨cA, hiA, rfl⟩ := hcdMem ψ i cd hi
      exact ((hframes i cA hiA).2 ψ ρ (((hframes i cA hiA).1 ψ ρ).mp hρ)).2.1
  -- ## the member's constructors, consed
  have hCtors' : ConLeche.checkSumCtors (ConLeche.fueledOps μ F) envI envI (d.memberName m) lps
      d.nP (d.nIdxAt m) d.resSort d.isProp d.large cvTa ctors = .ok (d.ctorsM m, sortss) := by
    rw [hTname]; exact hCtors
  have hout' : ∀ cA ∈ d.ctorsM m, ∀ T'' ∈ d.memberNames, T'' ≠ d.memberName m →
      cA.1.name ∉ ctorsOf T'' := by rw [hTname]; exact hS.out m cvTa hm hcvTa
  obtain ⟨mp', hE', hfindT', hFD', hleafT', hconsedAt, hinvC⟩ :=
    blockCtorsLoop (T := d.memberName m) (lps := lps) (nP := d.nP) (nIdx := d.nIdxAt m)
      (resSort := d.resSort) (isProp := d.isProp) (large := d.large)
      (names := d.memberNames) (ctorsOf := ctorsOf) (ppsAll := d.ppsM m)
      (idxF := d.idxF m) (dsF := d.dsF m) (esF := d.esF m) (srcsF := d.srcsF m)
      hμ hout' hCtors' (hS.nodup m hm) (hS.lpsT m cvTa hm hcvTa) hlpsA hFssParams hFssBelow
      (fun j cA hj => (hframes j cA hj).1) hFssOkP
      (fun j cA hj ψ ρ hρ bs hsp => ((hframes j cA hj).2 ψ ρ hρ).2.2 bs hsp)
      (fun {env'} m' => BlockCtorsCore m' d lps cvTasAll p₁ isRec A m)
      (fun m' cA A' mC hcA hfresh hac hinv' =>
        hinv'.cons ⟨hnameOf, hctorLt, hlenCv⟩ hfresh (hS.pshape m hm cA hcA) mC hac)
      (ConLeche.blockCapsAt p₁ m isRec) (A m)
      (fun m' kk cA hkk hinv' hFD' hleaf' hleafC' =>
        hTlawsOf m' kk cA hkk hinv' hFD' hleaf' hleafC')
      hfold
      (d.ctorsM m) 0 env mp (fun i => by rw [Nat.zero_add]) (Nat.zero_add _) hE
      (by rw [hTname]; exact hfindT) hFD (fun ψ => by rw [hTname]; exact hleafT ψ)
      (fun i cA hi _ => absurd hi (Nat.not_lt_zero _))
      (fun i cA _ hi => ⟨hfreshC m (Nat.le_refl _) i cA hi, (hdata m i cA hi).1,
        (hdata m i cA hi).2.1, (hdata m i cA hi).2.2.1.toCtorDataI⟩)
      ⟨hform, hfrP, hdata, hconsed⟩
  -- ## the invariant, one member on
  refine ⟨mp', hE', ⟨hinvC.1, hinvC.2.1, hinvC.2.2.1, fun c hc j cA hj => ?_⟩,
    fun c hc j cA hj => ?_⟩
  · rcases Nat.lt_or_ge c m with hlt | hge
    · exact hinvC.2.2.2 c hlt j cA hj
    · have hcm : c = m := by omega
      subst hcm
      obtain ⟨⟨hfind, hlps, -⟩, -, hleafC⟩ :=
        hconsedAt j cA (List.getElem?_eq_some_iff.mp hj).1 hj
      exact ⟨hfind, hlps, fun ψ => by rw [hleafC ψ, hFssEq ψ]; rfl⟩
  · rw [ConLeche.Semantics.consSumCtors_find?_of_not_mem (hS.ndBlock m hm c (by omega) j cA hj)]
    exact hfreshC c (by omega) j cA hj



/-- **The `k` members' constructors' conses, in block order**
(`consBlockCtors`): `stageBlockCtorsAt` at every member, the core
invariant one member further on at each step. -/
theorem stageBlockCtors (hμ : μ.verifiedChecks = true) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {envI : Env} {ctorsOf : Name → List Name}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (hN : BlockNamesOk (V := V) d cvTasAll)
    (hlenCv : cvTasAll.length = d.k)
    (hS : BlockCtorsStage (V := V) μ F d lps cvTasAll p₁ isRec A envI ctorsOf)
    (hk : ctorsAs.length = d.k)
    (hctorsAs : ∀ c, c < ctorsAs.length → ctorsAs[c]? = some (d.ctorsM c)) :
    ∀ (rest : List (List (ConstantVal × Nat))) (i : Nat) (env : Env) (mp : EnvModelM V μ env),
      (∀ c, rest[c]? = ctorsAs[i + c]?) → i + rest.length = ctorsAs.length →
      ConLeche.BlockEtaInv env d.memberNames ctorsOf →
      BlockCtorsCore mp.base2 d lps cvTasAll p₁ isRec A i →
      (∀ c, i ≤ c → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
        env.find? cA.1.name = none) →
      ∃ mp' : EnvModelM V μ (ConLeche.consBlockCtors d.nP rest env),
        ConLeche.BlockEtaInv (ConLeche.consBlockCtors d.nP rest env) d.memberNames ctorsOf ∧
        BlockCtorsCore mp'.base2 d lps cvTasAll p₁ isRec A d.k
  | [], i, env, mp, _, hi, hE, hinv, _ => by
    simp only [List.length_nil, Nat.add_zero] at hi
    rw [hi, hk] at hinv
    exact ⟨mp, hE, hinv⟩
  | ctorsA :: rest, i, env, mp, hrest, hi, hE, hinv, hfresh => by
    have hilt : i < ctorsAs.length := by simp only [List.length_cons] at hi; omega
    have hiA : ctorsAs[i]? = some ctorsA := by
      have := hrest 0; simpa using this.symm
    have hik : i < d.k := by rw [← hk]; exact hilt
    obtain rfl : ctorsA = d.ctorsM i :=
      Option.some.inj ((hiA.symm.trans (hctorsAs i hilt)))
    obtain ⟨cvTa, hcvTa⟩ : ∃ cvTa, cvTasAll[i]? = some cvTa :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hik)⟩
    obtain ⟨mpI, hE', hinv', hfresh'⟩ :=
      stageBlockCtorsAt hμ hN hS hik hcvTa mp hE hinv (fun c hc j cA hj => hfresh c hc j cA hj)
    have hrest' : ∀ c, rest[c]? = ctorsAs[i + 1 + c]? := by
      intro c
      have := hrest (c + 1)
      rwa [show i + (c + 1) = i + 1 + c from by omega] at this
    exact stageBlockCtors hμ hN hlenCv hS hk hctorsAs rest (i + 1) _ mpI hrest'
      (by simp only [List.length_cons] at hi; omega) hE' hinv' hfresh'

end ConLeche.Model
