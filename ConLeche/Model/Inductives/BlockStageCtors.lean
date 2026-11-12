module

import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Model.Inductives.BlockCtorsLoop
import ConLeche.Model.Inductives.FormerInEnv
import ConLeche.Model.Inductives.FixKit
import ConLeche.Model.Inductives.BlockRep
public import ConLeche.Model.Inductives.BlockAbsRead
import ConLeche.Model.Env.LfpHoleOp
import ConLeche.Model.Inductives.BlockHoleFold
public import ConLeche.Model.Inductives.BlockLfpHoles
import ConLeche.Semantics.Inductives.BlockConsFind
public section

/-!
# The constructors' stage at a block member

`BlockCtorsCore`: what the `k` constructor loops thread — the `k`
formers found with their leaves and their telescope readings, every
member's constructors' data at the carrier, and the constructors consed SO FAR with their leaves.
It is exactly what a constructor cons preserves (`BlockCtorsCore.cons`).

`stageBlockCtorsAt` is the member-local half at member `m`: the fibre
law of the member's own leaf (the override law, `blockHoleFold`), the
and then `blockCtorsLoop` —
so the stage's output is the carrier after `consSumCtors` of that
member's constructors, with the core invariant one member further on.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  InductiveShape BlockShape RecRule)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The invariant the member loops thread -/

/-- **The block install's carrier invariant at the constructors'
stage**, `nc` members' constructors consed: the `k` formers with their
leaves and telescope readings, every member's constructors' readings, the earlier members' constructors
stored with their leaves. -/
@[expose] def BlockCtorsCore {env : Env} (m' : EnvModel V env) (d : BlockData V)
    (lps : List Name) (formersAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → Term) (nc : Nat) : Prop :=
  -- the `k` formers
  (∀ (c : Nat) (cvTb : ConstantVal), formersAll[c]? = some cvTb →
      FormerInEnv m' cvTb (ConLeche.blockCapsAt p₁ c isRec) ∧
      cvTb.type.constsResolve env = true ∧
      (∀ ψ, m'.acval cvTb.name ψ = A c ψ) ∧
      FormerData m' cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)) ∧
  -- every member's constructors resolve and read, their fields with
  -- holes the walked term's reading
  (∀ (c j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM c)[j]? = some ctor →
      ctor.1.type.constsResolve env = true ∧
      (∀ e ∈ d.idxF c j, e.constsResolve env = true) ∧
      BlockCtorDataI m' (d.memberName c) lps ctor.1 d.nP ctor.2 (d.nIdxAt c) d.resSort d.isProp
        d.large (d.idxF c j) (d.dsF c j) (d.esF c j) (d.srcsF c j) (d.fvsPF c j)
        (d.xFvsF c j) (d.xrestF c j) ∧
      BlockAbsRead m' d lps c j ctor) ∧
  -- the members before `nc`: their constructors are stored with their leaves
  (∀ c, c < nc → ∀ (j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM c)[j]? = some ctor →
      env.find? ctor.1.name = some (.ctorInfo ctor.1 d.nP ctor.2 (d.memberName c)) ∧ ctor.1.levelParams = lps ∧
      ∀ ψ, m'.acval ctor.1.name ψ
        = sumMkAV (d.w ψ) j (d.dsF c j ψ) (((d.dsF c j ψ).drop d.nP))
            (uChains (d.Fss c ψ)))

/-- **The block's names, statically**: a member's name is its former's,
and every constructor is a member's. -/
@[expose] def BlockNamesOk (d : BlockData V) (formersAll : List ConstantVal) : Prop :=
  (∀ (c : Nat) (cvTb : ConstantVal), formersAll[c]? = some cvTb → d.memberName c = cvTb.name) ∧
  (∀ (c j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM c)[j]? = some ctor → c < formersAll.length) ∧
  formersAll.length = d.k

/-- **The core invariant survives a constructor's cons.**  A stored
name is not the fresh one, so nothing found before is disturbed; the
readings cross by `FormerData.cross` and `BlockCtorDataI.cross`. -/
theorem BlockCtorsCore.cons {T : Name} {env : Env} {m' : EnvModel V env} {d : BlockData V}
    {lps : List Name} {formersAll : List ConstantVal} {p₁ : BlockShape} {isRec : Bool}
    {A : Nat → (Name → Nat) → Term} {nc : Nat}
    (hN : BlockNamesOk (V := V) d formersAll)
    (h : BlockCtorsCore m' d lps formersAll p₁ isRec A nc)
    {ctor : ConstantVal × Nat} {B : (Name → Nat) → Term}
    (hfresh : env.find? ctor.1.name = none)
    (mC : EnvModel V ⟨.ctorInfo ctor.1 d.nP ctor.2 T :: env.consts, env.tables⟩)
    (hac : mC.acval = acvalWith m'.acval ctor.1.name B) :
    BlockCtorsCore mC d lps formersAll p₁ isRec A nc := by
  obtain ⟨hnameOf, hctorLt, hlenCv⟩ := hN
  obtain ⟨hform, hdata, hconsed⟩ := h
  -- a name already stored is not the fresh one
  have hne : ∀ n : Name, (env.find? n).isSome = true → n ≠ ctor.1.name := by
    intro n hn hnn
    rw [hnn, hfresh] at hn
    exact nomatch hn
  have hneOf : ∀ (c : Nat) (cvTb : ConstantVal), formersAll[c]? = some cvTb →
      cvTb.name ≠ ctor.1.name := by
    intro c cvTb hc
    obtain ⟨cvS, hfS, -⟩ := (hform c cvTb hc).1
    exact hne _ (by rw [hfS]; rfl)
  refine ⟨fun c cvTb hc => ?_, fun c j cB hj => ?_, fun c hc j cB hj => ?_⟩
  · obtain ⟨hfind, hres, hleaf, hFD⟩ := hform c cvTb hc
    refine ⟨hfind.cross (c₀ := .ctorInfo ctor.1 d.nP ctor.2 T) hfresh mC hac,
      Expr.constsResolve_mono hres, fun ψ => ?_, ?_⟩
    · rw [hac]
      show acvalWith m'.acval ctor.1.name B cvTb.name ψ = _
      rw [acvalWith_ne (hneOf c cvTb hc)]
      exact hleaf ψ
    · exact hFD.cross (c₀ := .ctorInfo ctor.1 d.nP ctor.2 T) hfresh
        (constsBound_of_constsResolve _ hres) mC hac
  · obtain ⟨hres, hresI, hD, hR⟩ := hdata c j cB hj
    refine ⟨Expr.constsResolve_mono hres, fun e he => Expr.constsResolve_mono (hresI e he), ?_,
      hR.cross (c₀ := .ctorInfo ctor.1 d.nP ctor.2 T) hfresh (constsBound_of_constsResolve _ hres)
        mC hac⟩
    refine hD.cross (c₀ := .ctorInfo ctor.1 d.nP ctor.2 T) hfresh ?_
      (constsBound_of_constsResolve _ hres)
      (fun e he => constsBound_of_constsResolve _ (hresI e he)) mC hac
    obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, formersAll[c]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (hctorLt c j cB hj)⟩
    rw [hnameOf c cvTb hcvTb]
    exact hneOf c cvTb hcvTb
  · obtain ⟨hfind, hlps, hleaf⟩ := hconsed c hc j cB hj
    refine ⟨ConLeche.Env.find?_cons_of_fresh hfresh hfind, hlps, fun ψ => ?_⟩
    rw [hac]
    show acvalWith m'.acval ctor.1.name B cB.1.name ψ = _
    rw [acvalWith_ne (hne _ (by rw [hfind]; rfl))]
    exact hleaf ψ

/-! ## The loop over the members -/

/-- **What the constructors' stage needs of every member** — the
per-member hypotheses of `stageBlockCtorsAt`, gathered so that the
loop over the `k` members carries ONE obligation. -/
structure BlockCtorsStage (F : Nat) (d : BlockData V) (lps : List Name)
    (formersAll : List ConstantVal) (p₁ : BlockShape) (isRec : Bool)
    (A : Nat → (Name → Nat) → Term)
    (envI : Env) : Prop where
  /-- the leaves the `k` formers were consed with: the block operator at
  the HOLE chains (charter item 2) -/
  leaf : ∀ (c : Nat) (ψ : Name → Nat), A c ψ
    = blockTyG d.k (d.w ψ) (fun c' => d.uM c' ψ) (fun c' => d.IdsM c' ψ) (d.toLfp.holeChains ψ)
        (d.ppsM c ψ) c
  /-- the hole chains are graded at every parameter frame -/
  holeOk : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    BlockChainsOkG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ)
  /-- the hole operator is accessible at every parameter frame (its
  fixed-point equation's premises: `AccW.mono`, `AccW.closed`), its fit
  with a bound of the level at a `Type`-valued block (task #327) -/
  holeFun : ∀ (ψ : Name → Nat) (ρp : Nat → V), Sat V (d.params ψ).reverse ρp →
    AccW (d.w ψ) d.k (blockIdx (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
      (blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ)) ∧
    ∃ A, (d.w ψ ≠ 0 → A ∈ˢ (tg (d.w ψ) : V)) ∧ d.toLfp.FitAcc ψ ρp A
  /-- the block has no instance component -/
  inst : d.nInst = 0
  /-- the stored field shape facts, the members' leaves the formers' -/
  shapes : ∀ (ψ : Name → Nat) (c : Nat), c < d.k → ∀ j, j < (d.ctorsM c).length →
    DeclaredFieldShapes V d.k d.nP (d.w ψ) d.nIdxAt (fun t => A t ψ) (d.params ψ).reverse
      (d.absF ψ c j) ((d.Fss c ψ).getD j [])
  /-- every member's constructors, as checked at the formers' environment -/
  ctors : ∀ (m : Nat) (cvTa : ConstantVal), m < d.k → formersAll[m]? = some cvTa →
    ∃ (cs : List (ConstantVal × Nat)) (sortss : List (List Level)),
      ConLeche.SumCtorsRun .verified F envI envI cvTa.name lps d.nP (d.nIdxAt m)
        d.resSort d.isProp d.large cvTa cs (d.ctorsM m) sortss
  nodup : ∀ m, m < d.k → ((d.ctorsM m).map (·.1.name)).Nodup
  lpsT : ∀ (m : Nat) (cvTa : ConstantVal), m < d.k → formersAll[m]? = some cvTa →
    cvTa.levelParams = lps
  lpsA : ∀ m, m < d.k → ∀ ctor ∈ d.ctorsM m, ctor.1.levelParams = lps
  /-- the reserved names' check (`basisNamesOk`) -/
  resA : ∀ m, m < d.k → ∀ ctor ∈ d.ctorsM m, ConLeche.reservedBasisNames.contains ctor.1.name = false
  ndBlock : ∀ m, m < d.k → ∀ (c : Nat), c ≠ m → ∀ (j : Nat) (cB : ConstantVal × Nat),
    (d.ctorsM c)[j]? = some cB → cB.1.name ∉ (d.ctorsM m).map (·.1.name)
  paramsOf : ∀ m, m < d.k → ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP)).reverse ρp →
    ∀ c, c < d.k → Sat V (((d.ppsM c ψ).take d.nP)).reverse ρp
  lenPps : ∀ (c : Nat) (ψ : Name → Nat), c < d.k → (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length
  lenIds : ∀ m, m < d.k → ∀ ψ : Name → Nat, (d.IdsM m ψ).length = d.nIdxAt m
  /-- the members' index telescopes are graded at every parameter frame -/
  idxOk : ∀ m, m < d.k → ∀ (ψ : Name → Nat) (ρp : Nat → V),
    Sat V (((d.ppsM m ψ).take d.nP)).reverse ρp →
    BlockIdxOk (V := V) d.k (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ)
  frames : ∀ m, m < d.k → ∀ (j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM m)[j]? = some ctor →
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP)).reverse ρ ↔
        Sat V (((d.dsF m j ψ).take d.nP)).reverse ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.dsF m j ψ).take d.nP)).reverse ρ →
        FieldsOkB (d.w ψ) ρ (((d.dsF m j ψ).drop d.nP)) ∧
        (∀ bs : List V, SpineFit ρ (((d.dsF m j ψ).drop d.nP)) bs →
          SpineFit ρ (d.IdsM m ψ) (idxValsAt ρ (d.esF m j ψ) bs)))
  /-- the datum records the telescopes the check read -/
  telescopeAt : ∀ (m : Nat) (cvTa : ConstantVal), formersAll[m]? = some cvTa → d.telescope m = some cvTa

/-! ## The stage at one member -/

/-- **The constructors' hole facts, from the stage's records** (at any
number of members' constructors consed). -/
theorem blockHoleFacts_of_stage {F : Nat} {envC envI : Env} {mo : EnvModel V envC}
    {d : BlockData V} {lps : List Name} {formers : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → Term}
    {nc : Nat}
    (hN : BlockNamesOk (V := V) d formers)
    (hS : BlockCtorsStage (V := V) F d lps formers p₁ isRec A envI)
    (hcore : BlockCtorsCore mo d lps formers p₁ isRec A nc) (hk0 : 0 < d.k) :
    BlockHoleFacts mo d lps := by
  have hNk : d.N = d.k := by rw [BlockData.N, hS.inst]; rfl
  refine ⟨fun c _ j ctor hj => (hcore.2.1 c j ctor hj).2.2.1, fun ψ c hc j hj => ?_,
      fun ψ => ?_, fun ψ mm hmm => ?_,
      fun ψ mm hmm ρ h => hS.paramsOf 0 hk0 ψ ρ h mm hmm,
      fun ψ mm hmm ρ h => hS.paramsOf mm hmm ψ ρ h 0 hk0, fun ψ c hc j hj => ?_⟩
  · refine (hS.shapes ψ c (by rw [← hNk]; exact hc) j hj).congr_leaf fun t ht => ?_
    obtain ⟨cvTb, hcvTb⟩ : ∃ cvTb, formers[t]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
    rw [hN.1 t cvTb hcvTb]
    exact ((hcore.1 t cvTb hcvTb).2.2.1 ψ).symm
  · show (((d.ppsM 0 ψ).take d.nP)).length = d.nP
    rw [List.length_take, hS.lenPps 0 ψ hk0]
    omega
  · show (((d.ppsM mm ψ).take d.nP)).length = d.nP
    rw [List.length_take, hS.lenPps mm ψ hmm]
    omega
  · have hck : c < d.k := by rw [← hNk]; exact hc
    have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
    rw [show (d.Ess c ψ).getD j [] = d.esF c j ψ from essOfR_fixCtorDataList_getD hcj,
      ((hcore.2.1 c j _ hcj).2.2.1).lenE ψ, hS.lenIds c hck ψ]

set_option maxHeartbeats 1600000 in
/-- **The constructors' stage at one block member**: the member-local
half at member `m`.  The member's own fibre law is the
member's leaf on the hole chains folded by the override law
(`blockHoleFold`: the stored fields are the fields with holes read at
the leaves' frame); it feeds `blockCtorsLoop`; the carrier that comes out is the one after that
member's `consSumCtors`, with the core invariant one member on. -/
theorem stageBlockCtorsAt {F : Nat}
    {d : BlockData V} {lps : List Name} {formersAll : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → Term}
   
    {envI env : Env} {m : Nat} {cvTa : ConstantVal}
    (hN : BlockNamesOk (V := V) d formersAll)
    (hS : BlockCtorsStage (V := V) F d lps formersAll p₁ isRec A envI)
    (hm : m < d.k) (hcvTa : formersAll[m]? = some cvTa)
    (mp : EnvModelM V env)
    (hinv : BlockCtorsCore mp.base2 d lps formersAll p₁ isRec A m)
    (hfreshC : ∀ c, m ≤ c → ∀ (j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM c)[j]? = some ctor →
      env.find? ctor.1.name = none) :
    ∃ mp' : EnvModelM V (ConLeche.consSumCtors d.nP (d.memberName m) (d.ctorsM m) env),
      BlockCtorsCore mp'.base2 d lps formersAll p₁ isRec A (m + 1) ∧
      (∀ c, m + 1 ≤ c → ∀ (j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM c)[j]? = some ctor →
        (ConLeche.consSumCtors d.nP (d.memberName m) (d.ctorsM m) env).find? ctor.1.name = none) ∧
      -- every stored name keeps its leaf
      ∀ n : Name, (env.find? n).isSome = true → mp'.base2.acval n = mp.base2.acval n := by
  have hH : BlockHoleFacts mp.base2 d lps := blockHoleFacts_of_stage hN hS hinv (by omega)
  obtain ⟨ctors, sortss, hCtors⟩ := hS.ctors m cvTa hm hcvTa
  have hframes := hS.frames m hm
  have hlpsA := hS.lpsA m hm
  have hresA := hS.resA m hm
  obtain ⟨hnameOf, hctorLt, hlenCv⟩ := hN
  obtain ⟨hform, hdata, hconsed⟩ := hinv
  have hTname : d.memberName m = cvTa.name := hnameOf m cvTa hcvTa
  obtain ⟨⟨cvSm, hfindT, hDm⟩, hresT, hleafT, hFD⟩ := hform m cvTa hcvTa
  -- ## the formers' leaves: closed, and the members' values at the carrier
  have hcvOf : ∀ c, c < d.k → ∃ cvTb, formersAll[c]? = some cvTb :=
    fun c hc => ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hc)⟩
  have hcl : ∀ c, c < d.k → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (A c ψ) := by
    intro c hc ψ
    obtain ⟨cvTb, hcvTb⟩ := hcvOf c hc
    have := mp.base2.cval_closed cvTb.name ψ
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
  have hfold : ∀ (j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM m)[j]? = some ctor →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((d.dsF m j ψ).drop d.nP)) bs →
        interp V (consList bs ρ)
            (Term.mkAppN (A m ψ) (paramBvars d.nP ctor.2 ++ d.esF m j ψ))
          = sumSet (d.w ψ) (sumFibre (d.w ψ)
              (consList (idxValsAt ρ (d.esF m j ψ) bs) ρ)
              (rChains (d.nIdxAt m) (d.nIdxAt m)
                (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0))
                (essOf (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)))) := by
    intro j ctor hj ψ ρ hρ bs hsp
    have hs0 : Sat V (d.params ψ).reverse ρ := hS.paramsOf m hm ψ ρ hρ 0 (by omega)
    have hD := (hdata m j ctor hj).2.2.1
    have hlenB : bs.length = ctor.2 := by rw [hsp.length_eq]; simp [hD.len ψ]
    have hspE : SpineFit ρ (d.IdsM m ψ) (idxValsAt ρ (d.esF m j ψ) bs) :=
      ((hframes j ctor hj).2 ψ ρ (((hframes j ctor hj).1 ψ ρ).mp hρ)).2 bs hsp
    have hfl := blockHoleFold hH hS.inst (fun c _ => hS.leaf c ψ) hs0
      (fun c hc => hS.lenPps c ψ hc) (hS.idxOk m hm ψ ρ hρ) (hS.holeOk ψ ρ hs0)
      (hS.holeFun ψ ρ hs0).1 hm
      (fun j' hj' => blockOverride hH (fun t ht => hacv t ht ψ) ρ hs0
        (show m < d.N by simp [BlockData.N, hS.inst]; exact hm) hj') hspE
    rw [ConLeche.Semantics.interp_mkAppN_foldl, List.map_append, paramBvars_eq_paramBvarsAt,
      map_paramBvarsAt_interp (ρp := ρ) (e := ctor.2)
        (fun j' => by rw [← hlenB]; exact consList_apply_add bs ρ j'),
      ← frameIdx_eq_reverse_map, interp_closed V (hcl m hm ψ) _ (shiftE d.nP 0 ρ)]
    rw [show (d.esF m j ψ).map (interp V (consList bs ρ)) = idxValsAt ρ (d.esF m j ψ) bs from rfl,
      hfl, hS.lenIds m hm ψ, hFssEq ψ, hEssEq ψ]
  -- ## the data's level-parameter invariance and bounds
  have hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ lps, ψ₁ q = ψ₂ q) →
      fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ₁ (d.ctorsM m) 0)
        = fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ₂ (d.ctorsM m) 0) := by
    intro ψ₁ ψ₂ hφ
    have hcds : ctorDataList (d.dsF m) (d.esF m) ψ₁ (d.ctorsM m) 0
        = ctorDataList (d.dsF m) (d.esF m) ψ₂ (d.ctorsM m) 0 := by
      refine ctorDataList_params fun i hi => ?_
      rw [Nat.zero_add]
      obtain ⟨ctori, hi'⟩ : ∃ ctori, (d.ctorsM m)[i]? = some ctori := ⟨_, List.getElem?_eq_getElem hi⟩
      exact (hdata m i ctori hi').2.2.1.params ψ₁ ψ₂
        (fun q hq => hφ q (by rw [← hlpsA ctori (List.mem_of_getElem? hi')]; exact hq))
    rw [hcds]
  have hcdMem : ∀ (ψ : Name → Nat) (i : Nat) (cd : CtorDatum),
      (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)[i]? = some cd →
      ∃ ctor, (d.ctorsM m)[i]? = some ctor ∧ cd = (ctor.1.name, ctor.2, d.dsF m i ψ, d.esF m i ψ) := by
    intro ψ i cd hi
    rw [ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : (d.ctorsM m)[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some ctor => rw [h] at hi; exact ⟨ctor, rfl, (Option.some.inj hi).symm⟩
  have hFssBelow : ∀ ψ : Name → Nat,
      ∀ Fs ∈ fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0),
        DomsBelow d.nP Fs := by
    intro ψ Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    obtain ⟨ctor, hiA, rfl⟩ := hcdMem ψ i cd hi
    have := (DomsBelow.drop d.nP ((hdata m i ctor hiA).2.2.1.below ψ))
    rwa [Nat.zero_add] at this
  have hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V (((d.ppsM m ψ).take d.nP)).reverse ρ →
      SumFieldsOkB (d.w ψ) ρ (fssOf d.nP (ctorDataList (d.dsF m) (d.esF m) ψ (d.ctorsM m) 0)) := by
    intro ψ ρ hρ Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    obtain ⟨ctor, hiA, rfl⟩ := hcdMem ψ i cd hi
    exact ((hframes i ctor hiA).2 ψ ρ (((hframes i ctor hiA).1 ψ ρ).mp hρ)).1
  -- ## the member's constructors, consed
  have hCtors' : ConLeche.SumCtorsRun .verified F envI envI (d.memberName m) lps
      d.nP (d.nIdxAt m) d.resSort d.isProp d.large cvTa ctors (d.ctorsM m) sortss := by
    rw [hTname]; exact hCtors
  obtain ⟨mp', hfindT', hFD', hleafT', hconsedAt, hinvC, hagC⟩ :=
    blockCtorsLoop (T := d.memberName m) (lps := lps) (nP := d.nP) (nIdx := d.nIdxAt m)
      (resSort := d.resSort) (isProp := d.isProp) (large := d.large)
      (ppsAll := d.ppsM m)
      (idxF := d.idxF m) (dsF := d.dsF m) (esF := d.esF m) (srcsF := d.srcsF m)
      hCtors' (hS.nodup m hm) (hS.lpsT m cvTa hm hcvTa) hlpsA hresA hFssParams hFssBelow
      (fun j ctor hj => (hframes j ctor hj).1) hFssOkP
      (fun j ctor hj ψ ρ hρ bs hsp => ((hframes j ctor hj).2 ψ ρ hρ).2 bs hsp)
      (fun {env'} m' => BlockCtorsCore m' d lps formersAll p₁ isRec A m ∧
        ∀ n : Name, (env.find? n).isSome = true →
          m'.acval n = mp.base2.acval n ∧ (env'.find? n).isSome = true)
      (fun m' ctor A' mC _ hfresh hac hinv' =>
        ⟨hinv'.1.cons ⟨hnameOf, hctorLt, hlenCv⟩ hfresh mC hac,
          fun n hn => by
            obtain ⟨h1, h2⟩ := hinv'.2 n hn
            have hne : n ≠ ctor.1.name := fun h => by rw [h, hfresh] at h2; exact nomatch h2
            refine ⟨by rw [hac, acvalWith_ne hne]; exact h1, ?_⟩
            rw [ConLeche.Env.find?_cons_of_isSome hfresh h2]; exact h2⟩)
      (ConLeche.blockCapsAt p₁ m isRec) (A m)
      hfold
      (d.ctorsM m) 0 env mp (fun i => by rw [Nat.zero_add]) (Nat.zero_add _)
      (by rw [hTname]; exact hfindT) hresT hFD (fun ψ => by rw [hTname]; exact hleafT ψ)
      (fun i ctor hi _ => absurd hi (Nat.not_lt_zero _))
      (fun i ctor _ hi => ⟨hfreshC m (Nat.le_refl _) i ctor hi, (hdata m i ctor hi).1,
        (hdata m i ctor hi).2.1, (hdata m i ctor hi).2.2.1.toCtorDataI⟩)
      ⟨⟨hform, hdata, hconsed⟩, fun n hn => ⟨rfl, hn⟩⟩
  -- ## the invariant, one member on
  refine ⟨mp', ⟨hinvC.1, hinvC.2.1, fun c hc j ctor hj => ?_⟩,
    fun c hc j ctor hj => ?_, fun n hn => (hagC n hn).1⟩
  · rcases Nat.lt_or_ge c m with hlt | hge
    · exact hinvC.2.2 c hlt j ctor hj
    · have hcm : c = m := by omega
      subst hcm
      obtain ⟨⟨hfind, hlps, -⟩, -, hleafC⟩ :=
        hconsedAt j ctor (List.getElem?_eq_some_iff.mp hj).1 hj
      exact ⟨hfind, hlps, fun ψ => by rw [hleafC ψ, hFssEq ψ]; rfl⟩
  · rw [ConLeche.Semantics.consSumCtors_find?_of_not_mem (hS.ndBlock m hm c (by omega) j ctor hj)]
    exact hfreshC c (by omega) j ctor hj



/-- **The `k` members' constructors' conses, in block order**
(`consBlockCtors`): `stageBlockCtorsAt` at every member, the core
invariant one member further on at each step. -/
theorem stageBlockCtors {F : Nat}
    {d : BlockData V} {lps : List Name} {formersAll : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → Term}
    {envI : Env}
    {memberCtors : List (Name × List (ConstantVal × Nat))}
    (hN : BlockNamesOk (V := V) d formersAll)
    (hlenCv : formersAll.length = d.k)
    (hS : BlockCtorsStage (V := V) F d lps formersAll p₁ isRec A envI)
    (hk : memberCtors.length = d.k)
    (hmemberCtors : ∀ c, c < memberCtors.length →
      memberCtors[c]? = some (d.memberName c, d.ctorsM c)) :
    ∀ (rest : List (Name × List (ConstantVal × Nat))) (i : Nat) (env : Env) (mp : EnvModelM V env),
      (∀ c, rest[c]? = memberCtors[i + c]?) → i + rest.length = memberCtors.length →
      BlockCtorsCore mp.base2 d lps formersAll p₁ isRec A i →
      (∀ c, i ≤ c → ∀ (j : Nat) (ctor : ConstantVal × Nat), (d.ctorsM c)[j]? = some ctor →
        env.find? ctor.1.name = none) →
      ∃ mp' : EnvModelM V (ConLeche.consBlockCtors d.nP rest env),
        BlockCtorsCore mp'.base2 d lps formersAll p₁ isRec A d.k ∧
        -- every stored name keeps its leaf
        ∀ n : Name, (env.find? n).isSome = true → mp'.base2.acval n = mp.base2.acval n
  | [], i, env, mp, _, hi, hinv, _ => by
    simp only [List.length_nil, Nat.add_zero] at hi
    rw [hi, hk] at hinv
    exact ⟨mp, hinv, fun _ _ => rfl⟩
  | (T, ctorList) :: rest, i, env, mp, hrest, hi, hinv, hfresh => by
    have hilt : i < memberCtors.length := by simp only [List.length_cons] at hi; omega
    have hiA : memberCtors[i]? = some (T, ctorList) := by
      have := hrest 0; simpa using this.symm
    have hik : i < d.k := by rw [← hk]; exact hilt
    obtain ⟨rfl, rfl⟩ : T = d.memberName i ∧ ctorList = d.ctorsM i := by
      have := Option.some.inj ((hiA.symm.trans (hmemberCtors i hilt)))
      exact ⟨(Prod.mk.inj this).1, (Prod.mk.inj this).2⟩
    obtain ⟨cvTa, hcvTa⟩ : ∃ cvTa, formersAll[i]? = some cvTa :=
      ⟨_, List.getElem?_eq_getElem (by rw [hlenCv]; exact hik)⟩
    obtain ⟨mpI, hinv', hfresh', hagI⟩ :=
      stageBlockCtorsAt hN hS hik hcvTa mp hinv (fun c hc j ctor hj => hfresh c hc j ctor hj)
    have hrest' : ∀ c, rest[c]? = memberCtors[i + 1 + c]? := by
      intro c
      have := hrest (c + 1)
      rwa [show i + (c + 1) = i + 1 + c from by omega] at this
    obtain ⟨mp', hinv'', hag'⟩ :=
      stageBlockCtors hN hlenCv hS hk hmemberCtors rest (i + 1) _ mpI hrest'
        (by simp only [List.length_cons] at hi; omega) hinv' hfresh'
    refine ⟨mp', hinv'', fun n hn => ?_⟩
    have hn' : ((ConLeche.consSumCtors d.nP (d.memberName i) (d.ctorsM i) env).find? n).isSome = true := by
      cases h : (ConLeche.consSumCtors d.nP (d.memberName i) (d.ctorsM i) env).find? n with
      | some _ => rfl
      | none => rw [ConLeche.consSumCtors_find?_none h] at hn; exact nomatch hn
    rw [hag' n hn', hagI n hn]

end ConLeche.Model
