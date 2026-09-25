module

public import ConLeche.Model.Inductives.TargetClassCall
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetCallKey
import ConLeche.Model.Inductives.TargetCallCarrier
import ConLeche.Model.Inductives.TargetRowCall
import ConLeche.Model.Inductives.TargetOutChain
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Semantics.Kit
import ConLeche.Verify.InstList

public section

/-!
# The graph kit's two `ih` rows at every class (lane NESTIND, session 9)

`tgtRecPre_cls`'s premises `hihF` (the graph-built `ih` values fit the
`ih` domains) and `hchain` (the `ih` chain), at the classes: the member
rows' arguments (`tgtGraphIhF_run`, `tgtGraphIhChain_run`) at the frame
of ANY class (`tgtFrame_cls`) and with the call's target a major of the
callee's class read off the callee spine's fit (`tgtKey_cls`, F3) by the
classes' own `hsplit` and `hconcl` rows.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor RecShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Rows

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {outside nested : Bool}
  {block : List ConstantInfo} {names : List Name} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

/-- A class's index set lives under the prefix guard. -/
theorem tgtClsIs_pref {acval : Name → (Name → Nat) → AnnotTerm} {p : BlockShape}
    {ψ : Name → Nat} {ρ : Nat → V} {xs : List V} {c : Nat} {i : V}
    (hi : i ∈ˢ tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs c) :
    SpineFit ρ (blockRulePdomsAV acval envC p (tgtRs out) ψ c) xs := by
  classical
  unfold tgtClsIs at hi
  by_cases hG : tgtClsG d acval envC p out ψ ρ xs c
  · unfold tgtClsG at hG
    split at hG
    · exact hG.2
    · exact hG
  · rw [if_neg hG] at hi; exact absurd hi (not_mem_empty _)

set_option maxHeartbeats 4000000 in
/-- **Row `hihF` at every class**: the graph-built `ih` values fit the
`ih` domains, given the graph is motive-valued at the rule's
predecessors. -/
theorem tgtCls_hihF (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (hnd : d.memberNames.Nodup)
    (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs : List V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ (i : V) (fs : List V),
      i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) (tgtRs out).length
          (tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ) xs (c, j, fs) →
        app g v ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out) ρ xs v) →
      SpineFit (consList (xs ++ fs) ρ)
        (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          envC ψ c j)
        (tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
          ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs g) := by
  intro xs c hc j hj i fs hi hf g hg
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hpre := tgtClsIs_pref hi
  have hspF := tgtCls_hspF hμ hcov h R hcls hdR hcore hmr hM ψ ρ 0 xs c hc j hj i fs hi hf
  rw [tgtFdomsK, liftDomsK_zero] at hspF
  have hxs : xs.length = pp.toBlockShape.rulePrefixAt c :=
    hpre.length_eq.trans (blockRulePdomsAV_length hμ mpC h hr ψ)
  have hconclTy := tgtCls_hconclTy hμ hcov h R hcls hmr hM ψ ρ xs
  have hlenK : (tgtKeys μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length
      = (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length := by
    simp [tgtKeys]
  refine spineFit_of_getD (by simp [tgtIhv, tgtIhdomsAV, ihDomsLifted, ihTyReads, hlenK])
    fun q hq => ?_
  have hq' : q < (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length := by
    simpa [tgtIhdomsAV, ihDomsLifted, ihTyReads] using hq
  obtain ⟨hcal, hrPc, hbitsTL, ⟨Xr, hTeq, hXval⟩, hspC⟩ :=
    tgtKey_cls hμ hcov h R hcls hdR hN hS hcore hmr hnd ψ ρ hc hj hspF hxs hq'
  -- the domain, past the values already bound
  have htk : ((tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
      envC ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
      (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs g).take q).length = q := by
    rw [List.length_take]; simp [tgtIhv, hlenK]; omega
  have hdomq : (tgtIhdomsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
      mpC.base2.acval envC ψ c j).getD q default
      = ((ihTyReads mpC.base2.acval envC ψ (tgtB pp.toBlockShape out c j)
          (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j)).getD q
            default).liftN q 0 := by
    rw [tgtIhdomsAV, ihDomsLifted, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by simpa [ihTyReads] using hq'), Option.map_some, Option.getD_some]
  rw [hdomq]
  have hcancel := interp_liftN_ihvals (V := V)
    (ihvals := (tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
      envC ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
      (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs g).take q)
    (σ := consList (xs ++ fs) ρ)
    ((ihTyReads mpC.base2.acval envC ψ (tgtB pp.toBlockShape out c j)
      (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j)).getD q default)
  rw [htk] at hcancel
  rw [hcancel, hTeq]
  generalize hcq : ((tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q
    default).callee = cq at hcal hrPc hXval hspC
  have hval : (tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
      envC ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
      (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs g).getD q pt
      = lamTowerA (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large))
          (consList (xs ++ fs) ρ) []
          (tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ c j q)
          (fun _ τ => app g (tagged cq
            (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ cq
              ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
                mpC.base2.acval envC ψ c j q).map (interp V τ)))
            (interp V τ (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval envC ψ c j q)))) := by
    rw [tgtIhv, blockRecIhvAt, List.getD_eq_getElem?_getD, List.getElem?_map, tgtKeys,
      List.getElem?_map, List.getElem?_range hq', Option.map_some, Option.map_some,
      Option.getD_some, hcq]
  rw [hval]
  have hbitsQ : ∀ dd ∈ tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
      mpC.base2.acval envC ψ c j q,
      (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0
        ↔ dd.2.1 = 0) := by
    intro dd hdd
    rw [hbitsTL dd hdd]
    exact (pwBit_zeronessOf ψ _).symm
  refine blockGraphIhv_mem (V := V) (c' := cq)
    (tup := tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) hbitsQ fun bs hbs => ?_
  have hys := hspC bs hbs
  have hxl1 : xs.length = pp.toBlockShape.rulePrefixAt cq := by rw [hrPc, hxs]
  obtain ⟨-, -, hIs, hCr⟩ := tgtCls_hsplit hμ hcov h R hcls hmr hM ψ ρ cq hcal _ hys
  simp only [prefOf_split hxl1, idxOf_split hxl1, majOf_split] at hIs hCr
  have hmot := tgtCls_hconcl hμ hcov h R hcls hmr hM ψ ρ cq hcal _ hys
  rw [prefOf_split hxl1, idxOf_split hxl1, majOf_split] at hmot
  have hU := tagged_mem_unionSet hcal hIs hCr
  have hkm : (q, cq) ∈ tgtKeys μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j := by
    simp only [tgtKeys, List.mem_map, List.mem_range]
    exact ⟨q, hq', by rw [hcq]⟩
  have hcall : tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
      envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs
      (tagged cq (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ cq
        ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
          envC ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))))
        (interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F (mkFEnv envC)
          pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q))) :=
    ⟨(q, cq), hkm, bs, hbs, rfl⟩
  refine ⟨?_, fun h0 => ?_⟩
  · rw [hXval bs hbs, ← hmot]
    exact hg _ (mem_graphPredG.mpr ⟨hU, hcall⟩)
  · rw [hXval bs hbs, ← hmot]
    have hmem := blockRecMot_mem_univ (K := (tgtRs out).length) hconclTy _ hU
    rw [h0, univ_zero] at hmem
    exact hmem

end Rows

end ConLeche.Model
