module

public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetCallCarrier
import ConLeche.Model.Inductives.TargetCallKey
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.BlockDeclRun

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
  sorry

end Rows

end ConLeche.Model
