module

public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetCallCarrier
import ConLeche.Model.Inductives.TargetCallKey
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Verify.Inductives.RecCheckScope

public section

/-!
# The target recursor model's rows: the graph-built `ih` values: their fit and the `ih` chain (lane RECLIB)

A row of `tgtRecPre_graph` (`TargetGraph.lean`), stated at the target
check's data (`TargetIhData.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Rows

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}

set_option maxHeartbeats 4000000 in
/-- **Row: the graph-built `ih` values fit the `ih` domains** (B3 (e)
6), given the graph is bound-valued at the predecessors. -/
theorem tgtGraphIhF_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTas ctorsAs out)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A fssZ envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hC : LfpClause mpC.base2.acval d.toLfp) (hnd : d.memberNames.Nodup)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    ∀ c, c < (tgtRs out).length →
      SpineFit ρ (d.params ψ) (xs.take d.nP) → SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c) xs →
      ∀ j, j < blockRecNCt (tgtRs out) c → ∀ (i : V) (fs : List V),
      i ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (pp.toBlockShape.recTgtAt c) →
      blockHoleFitRel d ψ ρ pp.toBlockShape.recTgtAt xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ blockGraphPred d ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ) pp.toBlockShape.recTgtAt (tgtRs out).length (tgtCall μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ d ρ) xs (c, j, fs) →
        app g v ∈ˢ blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
          (fun c' => d.uM (pp.toBlockShape.recTgtAt c') ψ) (fun c' => d.nIdxAt (pp.toBlockShape.recTgtAt c')) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ) (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j) (tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)) d ρ xs c j fs g) := by
  intro c hc hpar hpref j hj i fs hi hfit g hg
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  obtain ⟨r0, hr0⟩ : ∃ r0, (tgtRs out)[c]? = some r0 := ⟨_, List.getElem?_eq_getElem hc⟩
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r →
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
        (pp.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hmN : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).N :=
    Nat.lt_of_lt_of_le (blockRecMajor_run (V := V) hμ mpC h hmr hr0 ψ).2.1 (Nat.le_add_right _ _)
  -- the hole fit is the slot fit at the carrier
  obtain ⟨-, hchain⟩ := (hC.holes ψ _ (BlockData.satOfSpine _ hpar) _ (lfpTuple_mem _ _ _ _)
    (pp.toBlockShape.recTgtAt c) hmN i hi j fs).symm.mp hfit
  have hjr : j < r0.2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr0, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, r0.2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r0.2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr0]; exact hjr)⟩
  have hbnd := blockRuleDoms_bounded_at hμ h hcore ψ
  have hspF := blockKitSpF_run hμ h hkLen hcore hmr hM hN rfl hctM ψ hbnd ρ (tgtRs out).length xs
    c hc hpar hpref j hj i fs hi hchain
  rw [blockRecFdomsK_eq_of_bounded hbnd hr0 hcA hrhs] at hspF
  have hxs : xs.length = pp.toBlockShape.rulePrefixAt c :=
    hpref.length_eq.trans (blockRulePdomsAV_length hμ mpC h hr0 ψ)
  obtain ⟨uOf, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hconclTy := blockRecConclTy_run hμ mpC h hmr hM hruns ψ ρ xs
  -- per key
  have hlenK : (tgtKeys μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).length
      = (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).length := by
    simp [tgtKeys]
  refine spineFit_of_getD (by simp [tgtIhv, tgtIhdomsAV, ihDomsLifted, ihTyReads, hlenK])
    fun q hq => ?_
  have hq' : q < (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).length := by
    simpa [tgtIhdomsAV, ihDomsLifted, ihTyReads] using hq
  obtain ⟨hcal, hrPc, hbitsTL, Xr, hTeq, hXval⟩ :=
    tgtIhKey_run hμ h R hkLen hdR' hN hS hcore hmr hM hnd ψ ρ hc hj hspF hxs hq'
  -- the domain, past the values already bound
  have htk : ((tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env
      ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ρ xs c j fs g).take q).length
      = q := by
    rw [List.length_take]; simp [tgtIhv, hlenK]; omega
  have hdomq : (tgtIhdomsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
      fe.env ψ c j).getD q default
      = ((ihTyReads mpC.base2.acval fe.env ψ (tgtB pp.toBlockShape (tgtRs out) c j)
          (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j)).getD q default).liftN
          q 0 := by
    rw [tgtIhdomsAV, ihDomsLifted, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by simpa [ihTyReads] using hq'), Option.map_some, Option.getD_some]
  rw [hdomq]
  have hcancel := interp_liftN_ihvals (V := V)
    (ihvals := (tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env
      ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ρ xs c j fs g).take q)
    (σ := consList (xs ++ fs) ρ)
    ((ihTyReads mpC.base2.acval fe.env ψ (tgtB pp.toBlockShape (tgtRs out) c j)
      (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j)).getD q default)
  rw [htk] at hcancel
  rw [hcancel, hTeq]
  generalize hcq : ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD q
    default).callee = cq at hcal hrPc hXval
  have hval : (tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env
      ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ρ xs c j fs g).getD q pt
      = lamTowerA (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
          (consList (xs ++ fs) ρ) []
          (tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ
            c j q)
          (fun _ τ => app g (tagged cq
            ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
              (pp.toBlockShape.recTgtAt cq)
              ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
                fe.env ψ c j q).map (interp V τ)))
            (interp V τ (tgtFapA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ c j q)))) := by
    rw [tgtIhv, blockRecIhvAt, List.getD_eq_getElem?_getD, List.getElem?_map, tgtKeys,
      List.getElem?_map, List.getElem?_range hq', Option.map_some, Option.map_some,
      Option.getD_some, hcq]
  rw [hval]
  have hbitsQ : ∀ dd ∈ tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
      mpC.base2.acval fe.env ψ c j q,
      (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0
        ↔ dd.2.1 = 0) := by
    intro dd hdd
    rw [hbitsTL dd hdd]
    exact (pwBit_zeronessOf ψ _).symm
  have hleaf : ∀ bs : List V, SpineFit (consList (xs ++ fs) ρ)
      ((tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ
        c j q).map (·.2.2)) bs →
      app g (tagged cq ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
          (pp.toBlockShape.recTgtAt cq)
          ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
            fe.env ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))))
          (interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F fe pp.toBlockShape
            (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j q)))
        ∈ˢ interp V (consList bs (consList (xs ++ fs) ρ)) Xr ∧
      (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0 →
        interp V (consList bs (consList (xs ++ fs) ρ)) Xr ∈ˢ (univZero : V)) := by
    intro bs hbs
    obtain ⟨hIds, hmemX⟩ := tgtCall_carrier hμ h R hkLen hdR' hN hS hcore hmr hM hnd ψ ρ hc hj
      hspF hxs hq' bs hbs
    rw [hcq] at hIds hmemX
    have hXv := hXval bs hbs
    obtain ⟨r1, hr1⟩ : ∃ r1, (tgtRs out)[cq]? = some r1 := ⟨_, List.getElem?_eq_getElem hcal⟩
    obtain ⟨-, hmemk, -, -, -⟩ := blockRecMajor_run hμ mpC h hmr hr1 ψ
    have hmN' : pp.toBlockShape.recTgtAt cq
        < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).N :=
      Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
    have hIok := hM.idxOk ψ _ (BlockData.satOfSpine _ hpar) _ hmN'
    have hisOf := isOfW_tupW hIok hIds
    rw [blockMembers_IdsM_length hmr hmemk ψ] at hisOf
    have hmot := blockRecMot_tagged (V := V) (K := (tgtRs out).length) hcal
      (concl := blockRecConclAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
      (uOf := fun c' => (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).uM
        (pp.toBlockShape.recTgtAt c') ψ)
      (nIdxOf := fun c' => (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD
        ppsOf).nIdxAt (pp.toBlockShape.recTgtAt c')) (ρ := ρ) (xs := xs)
      (i := (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
        (pp.toBlockShape.recTgtAt cq) ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type))
          (tgtRs out) mpC.base2.acval fe.env ψ c j q).map
            (interp V (consList bs (consList (xs ++ fs) ρ)))))
      (x := interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F fe pp.toBlockShape
        (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j q))
    have hisOf' : isOfW ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).uM
        (pp.toBlockShape.recTgtAt cq) ψ)
        ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).nIdxAt
          (pp.toBlockShape.recTgtAt cq))
        ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
          (pp.toBlockShape.recTgtAt cq) ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type))
            (tgtRs out) mpC.base2.acval fe.env ψ c j q).map
              (interp V (consList bs (consList (xs ++ fs) ρ)))))
        = (tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env
            ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ))) := hisOf
    simp only [] at hmot
    rw [hisOf'] at hmot
    -- the call's target is a major and a call
    have hpref1 := blockRecHpref_run hμ mpC h ψ hr0 hr1 hpref
    have hIs : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
        (pp.toBlockShape.recTgtAt cq) ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type))
          (tgtRs out) mpC.base2.acval fe.env ψ c j q).map
            (interp V (consList bs (consList (xs ++ fs) ρ))))
        ∈ˢ blockRecIs (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ψ ρ
          (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
          pp.toBlockShape.recTgtAt xs cq := by
      rw [blockRecIs_pos hpar hpref1]
      exact tupW_mem hIds
    have hCr : interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F fe pp.toBlockShape
          (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j q)
        ∈ˢ app (blockRecCr (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ψ
          ρ pp.toBlockShape.recTgtAt xs cq)
          ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
            (pp.toBlockShape.recTgtAt cq) ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type))
              (tgtRs out) mpC.base2.acval fe.env ψ c j q).map
                (interp V (consList bs (consList (xs ++ fs) ρ))))) := by
      rw [blockRecCr, ← hM.leaf _ hmemk ψ ρ _ _ hpar hIds]
      exact hmemX
    have hU := tagged_mem_unionSet hcal hIs hCr
    have hkm : (q, cq) ∈ tgtKeys μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j := by
      simp only [tgtKeys, List.mem_map, List.mem_range]
      exact ⟨q, hq', by rw [hcq]⟩
    have hcall : tgtCall μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env ψ (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ρ xs c j fs
        (tagged cq ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
          (pp.toBlockShape.recTgtAt cq)
          ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
            fe.env ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))))
          (interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F fe pp.toBlockShape
            (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j q))) :=
      ⟨(q, cq), hkm, bs, hbs, rfl⟩
    refine ⟨?_, fun h0 => ?_⟩
    · rw [hXv, ← hmot]
      exact hg _ (mem_blockGraphPred.mpr ⟨hU, hcall⟩)
    · rw [hXv, ← hmot]
      have hmem := blockRecMot_mem_univ (K := (tgtRs out).length) hconclTy _ hU
      rw [h0, univ_zero] at hmem
      exact hmem
  exact blockGraphIhv_mem (V := V) (c' := cq)
    (tup := fun c'' is => (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
      (pp.toBlockShape.recTgtAt c'') is) hbitsQ hleaf

set_option maxHeartbeats 8000000 in
/-- **Row: the `ih` chain** (B3 (e) 7) — the graph-built `ih` values,
read off any recursor `r` over the rule's predecessors, ARE the target
`ih` terms' readings at the chain frame of any candidate `a` whose fold
along a callee's spine is `r` at the tagged call. -/
theorem tgtGraphIhChain_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTas ctorsAs out)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A fssZ envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (hC : LfpClause mpC.base2.acval d.toLfp) (hnd : d.memberNames.Nodup)
    (ψ : Name → Nat) (ρ : Nat → V) (a : Nat → V) (xs : List V) (r : V → V)
    (hfold : ∀ c', c' < (tgtRs out).length → ∀ (is : List V) (x : V),
      xs.length = pp.toBlockShape.rulePrefixAt c' →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c').map
        (·.2.2)) (xs ++ (is ++ [x])) →
      r (tagged c' (d.tup ψ (pp.toBlockShape.recTgtAt c') is) x) = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ) (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c ++ blockRecFdomsK (tgtRs out).length mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c j) (xs ++ fs) →
      tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)) d ρ xs c j fs
          (graph r (blockGraphPred d ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ) pp.toBlockShape.recTgtAt (tgtRs out).length (tgtCall μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ d ρ) xs (c, j, fs)))
        = (tgtIhsAV μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j).map (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))) := by
  intro c hc j hj fs hxs hsp
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  obtain ⟨r0, hr0⟩ : ∃ r0, (tgtRs out)[c]? = some r0 := ⟨_, List.getElem?_eq_getElem hc⟩
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[c]? = some r →
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
        (pp.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  obtain ⟨cA, rhs, hcA, hrhs, -, -, -, -, hxs', hfsl, -, hpre, hps, -, -, -⟩ :=
    blockRuleSpine_peel hμ h hkLen hcore hmr rfl hctM hr0 hj hxs hsp
  -- the fields at the base frame
  have hfsR : SpineFit (consList xs ρ)
      (blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j) fs := by
    obtain ⟨xs₁, fs₁, heq, h1, h2⟩ := spineFit_append_split hsp
    have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hxs]
    obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
    rw [blockRecFdomsK, ← hxs] at h2
    exact (spineFit_liftDomsK (K := (tgtRs out).length) _ _ _).mp h2
  have hspF := SpineFit.append hpre hfsR
  -- the rule's run
  obtain ⟨rc, rhs0, M, Q, hrP, hct, hds, hbf, hTf, hTb, hTc, hle, hRT3, hPrefEq, hFldEq, hB,
    hFrEq, hAbs⟩ := tgtRuleAt_facts h R hr0 hcA hrhs
  have hformerF : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
    exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1
  obtain ⟨ms0, hms0, hctA, -⟩ := checkBlockRecK_ctorsAt h hr0
  have hmemk0 : pp.toBlockShape.recTgtAt c
      < (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms0).1
  have hcj : ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).ctorsM
      (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk0 j cA hcj
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  obtain ⟨-, hlamR, -, -, -⟩ := targetRule_reads hμ mpC.base2 ψ Q hle hbf hds hTf hTb hTc
    (by rw [hct]; exact hwfC.1) (by rw [hct]; exact hwfC.2.2.2.1)
    (by rw [hct]; exact constsBound_of_constsResolve _ hwfC.2.2.1)
    (fun t ht => hformerF t ht) (fun c' => hRT3 c')
  have hLb : ∀ q, q < Q.ihs.size →
      Term.bvarsBelow (rc.rP + cA.2 + 1)
        ((ihLamReads mpC.base2.acval fe.env ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref
          Q.fvsF (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
          (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) Q.ihs.toList).getD q default).erase := by
    intro q hq
    obtain ⟨Lr, hLr, -, hb⟩ := hlamR q Q.ihs[q] (by simp [hq])
    have e2 : (ihLamReads mpC.base2.acval fe.env ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref
        Q.fvsF (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large)) Q.ihs.toList).getD q default = Lr := by
      rw [ihLamReads, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem hq]
      simp [hLr]
    rw [e2]; exact hb
  have hXlen : (xs ++ fs).length = rc.rP + cA.2 := by
    rw [List.length_append, hxs', hfsl, hrP]
  rw [tgtIhs_map_interp mpC.base2 hB hFrEq hAbs hLb a ρ hXlen]
  have hIhL : tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j = Q.ihs.toList := by
    rw [tgtIhL, ← hAbs]
  have hlenK : (tgtKeys μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).length
      = Q.ihs.toList.length := by
    simp [tgtKeys, hIhL]
  apply List.ext_getElem (by simp [tgtIhv, hlenK, ihValsAt])
  intro q h1 h2
  have hq : q < Q.ihs.toList.length := by simpa [tgtIhv, hlenK] using h1
  have hq' : q < (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).length := by
    rw [hIhL]; exact hq
  have hxsc : xs.length = pp.toBlockShape.rulePrefixAt c := hxs'
  obtain ⟨hcal, hrPc, hbitsTL, -, -, -⟩ :=
    tgtIhKey_run hμ h R hkLen hdR' hN hS hcore hmr hM hnd ψ ρ hc hj hspF hxsc hq'
  have hihq : (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD q default
      = Q.ihs.toList[q] := by
    rw [hIhL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl
  -- the left: the graph's tower at key `q`
  have hL : (tgtIhv μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env
      ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
      (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ρ xs c j fs
      (graph r (blockGraphPred (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf)
        ψ ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
        pp.toBlockShape.recTgtAt (tgtRs out).length
        (tgtCall μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ
          (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ρ) xs (c, j, fs))))[q]
      = lamTowerA (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
          (consList (xs ++ fs) ρ) []
          (tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ
            c j q)
          (fun _ τ => app (graph r (blockGraphPred (blockDataOf V pp.toBlockShape env₀ ctorsAs
              pp.kinds pk uOfD ppsOf) ψ ρ
              (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
              pp.toBlockShape.recTgtAt (tgtRs out).length
              (tgtCall μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
                fe.env ψ (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ρ)
              xs (c, j, fs)))
            (tagged Q.ihs.toList[q].callee
            ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
              (pp.toBlockShape.recTgtAt Q.ihs.toList[q].callee)
              ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
                fe.env ψ c j q).map (interp V τ)))
            (interp V τ (tgtFapA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
              mpC.base2.acval fe.env ψ c j q)))) := by
    simp only [tgtIhv, blockRecIhvAt, List.getElem_map, tgtKeys, List.getElem_range]
    rw [hihq]
  -- the right: the call's λ at the callee's value
  have hR : (ihValsAt a (consList (xs ++ fs) ρ) Q.ihs.toList
      (ihLamReads mpC.base2.acval fe.env ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref Q.fvsF
        (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
        Q.ihs.toList))[q]
      = interp V (cons (a Q.ihs.toList[q].callee) (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + 1)
            (targetCallLam (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref Q.fvsF
              (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
              (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
                pp.toBlockShape.large)) Q.ihs.toList[q])).getD default) := by
    simp only [ihValsAt, ihLamReads, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq, List.getElem?_map, Option.getD_some,
      Option.map_some]
  rw [hL, hR]
  generalize hihd : Q.ihs.toList[q] = ih at hihq ⊢
  have hihMem : ih ∈ Q.ihs.toList := by rw [← hihd]; exact List.getElem_mem hq
  obtain ⟨C⟩ := Q.call hihMem
  rw [hihq] at hcal hrPc
  have hQq : Q.ihs[q]? = some ih := by
    rw [← hihd, Array.getElem?_eq_getElem (by simpa using hq)]; simp
  obtain ⟨Lr, hLr, -, -⟩ := hlamR q ih hQq
  rw [hLr, Option.getD_some]
  have hLr' := hLr
  unfold targetCallLam at hLr'
  rw [← ConLeche.Expr.instantiateList_nil (Expr.mkLamsOf _ _) 0,
    show rc.rP + cA.2 + 1 = rc.rP + cA.2 + 1 + 0 from rfl] at hLr'
  obtain ⟨dsL, bodyL, osL, rfl, hdomsL, hbitsL, hosL, hbodyL⟩ :=
    denoteMeta_mkLamsOf (acval := mpC.base2.acval) (env := fe.env) (φ := ψ)
      (D := rc.rP + cA.2 + 1) _ _ 0 [] _ (LocList.nil _) hLr'
  -- the telescope, at the frame and one slot deeper
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts Q.hpref Q.hcrest hds Q.hfld hTf hTb hTc
    (by rw [hct]; exact hwfC.1) (by rw [hct]; exact hwfC.2.2.2.1)
    (by rw [hct]; exact constsBound_of_constsResolve _ hwfC.2.2.1)
  have hscope := targetIh_scope hμ Q mpC.base2.wf hle hbf hFr hher hcbF hformerF
    (fun c' => (hRT3 c').1) hihMem
  generalize hmdef : ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).length = m at *
  have hmT : (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map fun b =>
      (b.1, (⟨Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large)⟩ : ConLeche.BinderMeta))).length = m := by
    rw [List.length_map, hmdef]
  rw [hmT, Nat.zero_add] at hosL hbodyL
  have htele1 : (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map fun b =>
      (b.1, (⟨Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
        pp.toBlockShape.large)⟩ : ConLeche.BinderMeta))).map (·.1)
      = ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1) := by
    rw [List.map_map]; rfl
  rw [htele1] at hdomsL
  have hleavesT : ∀ t ∈ ((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1),
      ∀ l ∈ t.fvarLeaves, l.1 < rc.rP + cA.2 := by
    intro t ht l hl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact leaf_lt_of_mem hFr (fun l hl => List.mem_reverse.mpr (hscope.2.2.2.2.2 b hb l hl)) l hl
  have hdeep := teleDoms_deepen (acval := mpC.base2.acval) (env := fe.env) (φ := ψ) hacl 1
    (rc.rP + cA.2) _ 0 [] [] hleavesT (LocList.nil _) (LocList.nil _)
  rw [hdomsL] at hdeep
  obtain ⟨ts, hts, hlift⟩ : ∃ ts, teleDoms mpC.base2.acval fe.env ψ (rc.rP + cA.2) []
      (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1)) = some ts ∧
      dsL.map (·.2) = liftAt 1 0 ts := by
    cases hts : teleDoms mpC.base2.acval fe.env ψ (rc.rP + cA.2) []
        (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1)) with
    | none => rw [hts] at hdeep; exact nomatch hdeep
    | some ts => rw [hts] at hdeep; exact ⟨ts, rfl, Option.some.inj hdeep⟩
  have hTel : (tgtFrame μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
      (tgtRs out) c j).teles = Q.fnorm.map fun t => t.piBinders.1 := congrArg (·.teles) hFrEq
  have hTLq : tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env
      ψ c j q = ts.map fun t => (0, pwBit ψ (Level.zeronessOf
        (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)), t) := by
    simp only [tgtTlA, tgtTeleTys]
    rw [hihq, hTel, hB, hts, Option.getD_some]
  have htsl : ts.length = dsL.length := by
    have := congrArg List.length hlift
    rw [List.length_map, liftAt_length] at this
    exact this.symm
  refine lamTowerA_eq_mkLamsAV _ dsL _ _ [] (by rw [hTLq, List.length_map, htsl])
    (fun dd hdd => ?_) (fun bs hbs => ?_) (fun bs hbs => ?_)
  · have h1 : dd.1 ∈ dsL.map (·.1) := List.mem_map.mpr ⟨dd, hdd, rfl⟩
    rw [hbitsL] at h1
    simp only [List.map_map, Function.comp_def, List.mem_map] at h1
    obtain ⟨b, -, hb⟩ := h1
    rw [← hb]
    exact (pwBit_zeronessOf ψ _).symm
  · have hk : bs.length < ts.length := by rw [hTLq, List.length_map] at hbs; exact hbs
    have e1 : ((tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env ψ c j q).getD bs.length default).2.2 = ts.getD bs.length default := by
      rw [hTLq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hk,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; rfl
    have e2' : (dsL.getD bs.length default).2 = (dsL.map (·.2)).getD bs.length default := by
      have hkd : bs.length < dsL.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hkd]; rfl
    have e2 : (dsL.getD bs.length default).2 = (ts.getD bs.length default).liftN 1 (0 + bs.length) := by
      rw [e2', hlift, liftAt_getD 1 0 ts bs.length hk]
    rw [e1, e2, interp_liftN, Nat.zero_add]
    exact congrArg (fun σ' => interp V σ' (ts.getD bs.length default))
      (shiftE_consList_ih (locals := bs) (ihvals := [a ih.callee]) (ρ' := consList (xs ++ fs) ρ)
        rfl rfl).symm
  · -- the call target: a major (the carrier) and a call
    obtain ⟨hIds, hmemX⟩ := tgtCall_carrier hμ h R hkLen hdR' hN hS hcore hmr hM hnd ψ ρ hc hj
      hspF hxsc hq' bs hbs
    rw [hihq] at hIds hmemX
    obtain ⟨r1, hr1⟩ : ∃ r1, (tgtRs out)[ih.callee]? = some r1 := ⟨_, List.getElem?_eq_getElem hcal⟩
    obtain ⟨-, hmemk, -, -, -⟩ := blockRecMajor_run hμ mpC h hmr hr1 ψ
    have hpref1 := blockRecHpref_run hμ mpC h ψ hr0 hr1 hpre
    have hIs : (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
        (pp.toBlockShape.recTgtAt ih.callee) ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type))
          (tgtRs out) mpC.base2.acval fe.env ψ c j q).map
            (interp V (consList bs (consList (xs ++ fs) ρ))))
        ∈ˢ blockRecIs (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ψ ρ
          (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ)
          pp.toBlockShape.recTgtAt xs ih.callee := by
      rw [blockRecIs_pos hps hpref1]
      exact tupW_mem hIds
    have hCr : interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F fe pp.toBlockShape
          (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j q)
        ∈ˢ app (blockRecCr (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ψ
          ρ pp.toBlockShape.recTgtAt xs ih.callee)
          ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
            (pp.toBlockShape.recTgtAt ih.callee) ((tgtEisA μ F fe pp.toBlockShape
              (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j q).map
                (interp V (consList bs (consList (xs ++ fs) ρ))))) := by
      rw [blockRecCr, ← hM.leaf _ hmemk ψ ρ _ _ hps hIds]
      exact hmemX
    have hU := tagged_mem_unionSet hcal hIs hCr
    have hkm : (q, ih.callee) ∈ tgtKeys μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out)
        c j := by
      simp only [tgtKeys, List.mem_map, List.mem_range]
      exact ⟨q, hq', by rw [hihq]⟩
    have hcall : tgtCall μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
        fe.env ψ (blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf) ρ xs c j fs
        (tagged ih.callee ((blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf).tup ψ
          (pp.toBlockShape.recTgtAt ih.callee)
          ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
            fe.env ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))))
          (interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F fe pp.toBlockShape
            (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ c j q))) :=
      ⟨(q, ih.callee), hkm, bs, hbs, rfl⟩
    -- the callee's spine fits its recursor's binder data
    have hxl1 : xs.length = pp.toBlockShape.rulePrefixAt ih.callee := by rw [hrPc, hxsc]
    have hprefR : SpineFit ρ (((blockRecRdsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ
        ih.callee).map (·.2.2)).take (pp.toBlockShape.rulePrefixAt ih.callee)) xs := by
      rw [← List.map_take]; exact hpref1
    have hspC := blockRecSpineFit_of_parts hμ h hmr hr1 ψ ρ hprefR hIds hmemX
    rw [List.append_assoc] at hspC
    show app (graph r _) _ = _
    rw [app_graph (mem_blockGraphPred.mpr ⟨hU, hcall⟩), hfold ih.callee hcal _ _ hxl1 hspC]
    -- the λ's body: the callee variable along the call spine
    have hlp : Q.fvsPref.length = rc.rP := openPisAtFvars_length _ Q.hpref
    have hlf : Q.fvsF.length = cA.2 := openPisAtFvars_length _ Q.hfld
    have hframeL : ∀ x ∈ Q.fvsPref ++ Q.fvsF, ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := frame_leaves_mem hFr hher
    have hidxL : ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves,
        Expr.fvar l.1 l.2 ∈ Q.fvsPref ++ Q.fvsF := by
      rcases targetAbstract_entries (fr := ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out))
          rc.rP Q.fvsPref Q.fvsF Q.fnorm
          (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)))
          (B := rc.rP + cA.2) hle 0 _ #[] _ _ Q.habs _ hihMem with h0 | h0
      · simp at h0
      · intro x hx l hl
        obtain ⟨y, hy, hly⟩ := fvarLeaves_instantiateList hFr Q.body hbf 0 l (h0 x hx l hl)
        exact hframeL y (List.mem_reverse.mp hy) l hly
    have hfi : ih.field < cA.2 := by
      refine Nat.lt_of_not_le fun hge => ?_
      have hg : Q.fvsF.getD ih.field default = .bvar 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      have h0 := C.hfld
      rw [hg] at h0
      exact inferTypeCore_bvar_absurd' h0
    have hfmem : Q.fvsF.getD ih.field default ∈ Q.fvsPref ++ Q.fvsF := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact List.mem_append_right _ (List.getElem_mem _)
    have hidxLt : ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves, l.1 < rc.rP + cA.2 := fun x hx =>
      leaf_lt_of_mem hFr (fun l hl => List.mem_reverse.mpr (hidxL x hx l hl))
    have hfapLt : ∀ l ∈ (Expr.mkAppN (Q.fvsF.getD ih.field default)
        (ConLeche.structTeleVars m)).fvarLeaves, l.1 < rc.rP + cA.2 := by
      refine leaf_lt_of_mem hFr (fun l hl => List.mem_reverse.mpr ?_)
      rcases ConLeche.fvarLeaves_mkAppN hl with h1 | ⟨y, hy, h1⟩
      · exact hframeL _ hfmem l h1
      · rw [ConLeche.structTeleVars_fvarLeaves _ y hy] at h1; exact nomatch h1
    have hfvPref : ∀ i, i < rc.rP → ∃ ty, Q.fvsPref[i]? = some (Expr.fvar i ty) := by
      intro i hi
      have hlt : i < (Q.fvsPref ++ Q.fvsF).length := by simp [hlp, hlf]; omega
      obtain ⟨ty, hty⟩ := hFr.reverse_idx i _
        (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
      refine ⟨ty, ?_⟩
      rw [List.getElem?_eq_getElem (by omega), ← hty, List.getElem_append_left]
    have hbl : bs.length = m := by
      rw [hbs.length_eq, hTLq, List.length_map, List.length_map, htsl, ← hmdef]
      have := congrArg List.length hbitsL
      simpa using this
    have hxl : xs.length = rc.rP := by rw [hxsc, hrP]
    have hlenS : (xs ++ fs).length = rc.rP + cA.2 := by rw [List.length_append, hxl, hfsl]
    have hFF' : (tgtFrame μ F fe pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
        (tgtRs out) c j).fields = Q.fvsF := congrArg (·.fields) hFrEq
    -- one opened argument, read at both depths, has one value
    have hre : ∀ t : Expr, (∀ l ∈ t.fvarLeaves, l.1 < rc.rP + cA.2) →
        (∃ v, denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + 1 + m)
          (t.instantiateList osL 0) = some v) →
        interp V (consList bs (cons (a ih.callee) (consList (xs ++ fs) ρ)))
            ((denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + 1 + m)
              (t.instantiateList osL 0)).getD default)
          = interp V (consList bs (consList (xs ++ fs) ρ))
            ((denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + m)
              (t.instantiateList (locOpen (rc.rP + cA.2) m) 0)).getD default) := by
      intro t hl ⟨v1, hv1⟩
      have hd := denoteMeta_open_deepen (acval := mpC.base2.acval) (env := fe.env) (φ := ψ)
        hacl 1 (rc.rP + cA.2) t m (locOpen (rc.rP + cA.2) m) osL hl (locOpen_locList _ _) hosL
      rw [hv1] at hd
      cases h0 : denoteMeta mpC.base2.acval fe.env ψ (rc.rP + cA.2 + m)
          (t.instantiateList (locOpen (rc.rP + cA.2) m) 0) with
      | none => rw [h0] at hd; exact nomatch hd
      | some A0 =>
        rw [hv1, Option.getD_some, Option.getD_some]
        have := interp_open_indep (V := V) (acval := mpC.base2.acval) (env := fe.env) (φ := ψ)
          hacl hl hosL (show LocList (rc.rP + cA.2 + 0) m (locOpen (rc.rP + cA.2) m) from
            locOpen_locList _ _) hbl (ex1 := [a ih.callee]) (ex2 := []) rfl rfl
          (ρ' := consList (xs ++ fs) ρ) hv1 h0
        simpa using this
    rw [instantiateList_mkAppN] at hbodyL
    simp only [Expr.instantiateList] at hbodyL
    obtain ⟨fa, wsL, hfa, hwsL, rfl⟩ := denoteMeta_mkAppN_inv hbodyL
    rw [denoteMeta_fvar] at hfa
    obtain rfl := Option.some.inj hfa
    rw [interp_mkAppN_foldl, spine_map_getD (mT := mpC.base2) hwsL]
    have hhead : interp V (consList bs (cons (a ih.callee) (consList (xs ++ fs) ρ)))
        (.bvar (rc.rP + cA.2 + 1 + m - 1 - (rc.rP + cA.2))) = a ih.callee := by
      rw [interp_bvar, show rc.rP + cA.2 + 1 + m - 1 - (rc.rP + cA.2) = 0 + bs.length from by
        rw [hbl]; omega, consList_apply_add]
      rfl
    rw [hhead]
    congr 1
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, List.append_assoc]
    congr 1
    · apply List.ext_getElem (by simp [hlp, hxl])
      intro i h1 h2
      obtain ⟨ty, hty⟩ := hfvPref i (by omega)
      rw [List.getElem_map]
      rw [List.getElem?_eq_getElem (by rw [hlp]; omega)] at hty
      rw [Option.some.inj hty]
      simp only [Function.comp, Expr.instantiateList, denoteMeta_fvar, Option.getD_some]
      have hc1 : cons (a ih.callee) (consList (xs ++ fs) ρ)
          = consList [a ih.callee] (consList (xs ++ fs) ρ) := rfl
      rw [hc1, ← consList_append,
        show rc.rP + cA.2 + 1 + m - 1 - i = rc.rP + cA.2 + (1 + m) - 1 - i from by omega,
        interp_frame_fvar hlenS (by simp [hbl]; omega) (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some]
    · have hrd : ∀ t ∈ Q.fvsPref ++ ih.idx ++ [Expr.mkAppN (Q.fvsF.getD ih.field default)
            (ConLeche.structTeleVars m)], ∃ v, denoteMeta mpC.base2.acval fe.env ψ
              (rc.rP + cA.2 + 1 + m) (t.instantiateList osL 0) = some v :=
        fun t ht => spine_reads (mT := mpC.base2) hwsL _ (List.mem_map_of_mem ht)
      congr 1
      · simp only [tgtEisA, tgtTeleTys]
        rw [hihq, hTel, hB, List.length_map, hmdef, List.map_map]
        apply List.map_congr_left
        intro x hx
        exact (hre x (hidxLt x hx) (hrd x (by simp [hx]))).symm
      · simp only [tgtFapA, tgtTeleTys]
        rw [hihq, hTel, hB, hFF', List.length_map, hmdef]
        exact congrArg (·::[]) (hre _ hfapLt (hrd _ (by simp))).symm

end Rows

end ConLeche.Model
