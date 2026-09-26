module

import ConLeche.Model.Inductives.TargetClassCall
import ConLeche.Model.Inductives.TargetClassFrame
public import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Model.Inductives.TargetCallKey
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Semantics.Kit
import ConLeche.Verify.CheckerF

public section

/-!
# The graph kit's two `ih` rows at every class (lane NESTIND, session 9)

`tgtRecPre_cls`'s premises `hihF` (the graph-built `ih` values fit the
`ih` domains) and `hchain` (the `ih` chain), at the classes: at the frame
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

/-- **THE INDUCTION OVER THE RECURSOR CLASSES** (lane NESTIND, session
14: `hind`, named): at every parameter tuple `xs`, the union of the
classes' carriers is well-founded under the graph's predecessor relation
— the recursor family's calls from a major's decoding at its class.
This is the one premise of `tgtRecPre_clsI` that the recursor stage's
run does not give; it is what route A's positivity derivation (lane
POSDERIV) and the (D) typing must supply (DESIGN F13). -/
@[expose] def TgtClassInd (μ : CheckMode) (F : Nat) (envC : Env)
    (acval : Name → (Name → Nat) → AnnotTerm) (p : BlockShape) (formerTys : List Expr)
    (out : List (ConstantVal × TargetMajor × List Expr)) (d : BlockData V)
    (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
    (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ xs : List V, ∀ P : V → Prop,
    (∀ u, u ∈ˢ unionSet (tgtRs out).length
        (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) →
      (∃ e, graphDecG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
          (tgtClsInj d Dc mc cvc p out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length
          (tgtClsFit d Dc mc cvc acval envC p out ψ ρ) xs u e ∧
        ∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
            (tgtClsCr d Dc mc cvc acval envC p out ψ ρ)
            (tgtRs out).length
            (tgtCall μ F (mkFEnv envC) p formerTys out
              acval envC ψ (tgtClsTup d Dc mc cvc p out ψ) ρ) xs e →
          P v) → P u) →
    ∀ u, u ∈ˢ unionSet (tgtRs out).length
        (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) → P u

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

set_option maxHeartbeats 8000000 in
/-- **Row `hchain` at every class**: the graph-built `ih` values, read
off any recursor `r` over the rule's predecessors, ARE the target `ih`
terms' readings at the chain frame of any candidate `a` whose fold along
a callee's spine is `r` at the tagged call — at the frame of any class, the call's target a major of the
callee's class (`tgtKey_cls`). -/
theorem tgtCls_hchain (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
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
    ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < (tgtRs out).length → ∀ (is : List V) (x : V),
        xs.length = pp.toBlockShape.rulePrefixAt c' →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c').map
          (·.2.2)) (xs ++ (is ++ [x])) →
        r (tagged c' ((tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) c' is) x) = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
        SpineFit (chainFrame (tgtRs out).length a ρ)
          (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
          (xs ++ fs) →
        tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
            (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
            (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs
            (graph r (graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) (tgtRs out).length (tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ) xs (c, j, fs)))
          = (tgtIhsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
              envC ψ c j).map (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))) := by
  intro a xs r hfold c hc j hj fs hxs hsp
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  -- the base frame
  have hpK : liftDomsK (tgtRs out).length 0
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
      = blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c :=
    blockRecPdomsK_run (V := V) hμ mpC h hr ψ (tgtRs out).length
  rw [tgtFdomsK] at hsp
  have hspF := chainFit_base hpK hxs hsp
  obtain ⟨rc, rhs0, Q, hrP, -, -, hB, hFrEq, hAbs, hbf, hTf, hTb, hTc, hle, hRT3, hdsOk, hCf, hCb,
    hCc, hfl, -, -⟩ := tgtFrame_cls hμ hcov h R hcls hdR hS hcore hmr ψ hc hr hcA hrhs
  have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = pp.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hxs' : xs.length = pp.toBlockShape.rulePrefixAt c := by rw [hxs, hpl]
  have hfsl : fs.length = cA.2 := by
    have hsl := hspF.length_eq
    simp only [List.length_append, hpl, hfl, hxs'] at hsl
    omega
  have hformerF : ∀ t ∈ cvTas.map (·.type), t.hasFvar = false := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hcv
    exact (hmr.2.2.2.1 m _ (List.getElem?_eq_getElem hm)).2.2.2.1
  obtain ⟨-, hlamR, -, -, -⟩ := targetRule_reads hμ mpC.base2 ψ Q hle hbf hdsOk hTf hTb hTc
    hCf hCb hCc (fun t ht => hformerF t ht) (fun c' => hRT3 c')
  simp only [ConLeche.mkFEnv_env] at hlamR
  have hLb : ∀ q, q < Q.ihs.size →
      Term.bvarsBelow (rc.rP + cA.2 + 1)
        ((ihLamReads mpC.base2.acval envC ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref
          Q.fvsF (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
          (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) Q.ihs.toList).getD q default).erase := by
    intro q hq
    obtain ⟨Lr, hLr, -, hb⟩ := hlamR q Q.ihs[q] (by simp [hq])
    have e2 : (ihLamReads mpC.base2.acval envC ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref
        Q.fvsF (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large)) Q.ihs.toList).getD q default = Lr := by
      rw [ihLamReads, List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem hq]
      simp [hLr]
    rw [e2]; exact hb
  have hXlen : (xs ++ fs).length = rc.rP + cA.2 := by
    rw [List.length_append, hxs', hfsl, hrP]
  have hmapI := tgtIhs_map_interp (fe := mkFEnv envC) mpC.base2 hB hFrEq hAbs hLb a ρ hXlen
  simp only [ConLeche.mkFEnv_env] at hmapI
  rw [hmapI]
  have hIhL : tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j = Q.ihs.toList := by
    rw [tgtIhL, ← hAbs]
  have hlenK : (tgtKeys μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length
      = Q.ihs.toList.length := by
    simp [tgtKeys, hIhL]
  apply List.ext_getElem (by simp [tgtIhv, hlenK, ihValsAt])
  intro q h1 h2
  have hq : q < Q.ihs.toList.length := by simpa [tgtIhv, hlenK] using h1
  have hq' : q < (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).length := by
    rw [hIhL]; exact hq
  have hxsc : xs.length = pp.toBlockShape.rulePrefixAt c := hxs'
  obtain ⟨hcal, hrPc, hbitsTL, -, hspK⟩ :=
    tgtKey_cls hμ hcov h R hcls hdR hN hS hcore hmr hnd ψ ρ hc hj hspF hxsc hq'
  have hihq : (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).getD q default
      = Q.ihs.toList[q] := by
    rw [hIhL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl
  -- the left: the graph's tower at key `q`
  have hL : (tgtIhv μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
      ψ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
      (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs
      (graph r (graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) (tgtRs out).length
        (tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ) xs (c, j, fs))))[q]
      = lamTowerA (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
          (consList (xs ++ fs) ρ) []
          (tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC ψ
            c j q)
          (fun _ τ => app (graph r (graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) (tgtRs out).length
              (tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
                envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ)
              xs (c, j, fs)))
            (tagged Q.ihs.toList[q].callee
            ((tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) Q.ihs.toList[q].callee
              ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
                envC ψ c j q).map (interp V τ)))
            (interp V τ (tgtFapA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval envC ψ c j q)))) := by
    simp only [tgtIhv, blockRecIhvAt, List.getElem_map, tgtKeys, List.getElem_range]
    rw [hihq]
  -- the right: the call's λ at the callee's value
  have hR : (ihValsAt a (consList (xs ++ fs) ρ) Q.ihs.toList
      (ihLamReads mpC.base2.acval envC ψ (tgtFam pp.toBlockShape (tgtRs out)) Q.fvsPref Q.fvsF
        (Q.fnorm.map fun t => t.piBinders.1) (rc.rP + cA.2)
        (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large))
        Q.ihs.toList))[q]
      = interp V (cons (a Q.ihs.toList[q].callee) (consList (xs ++ fs) ρ))
          ((denoteMeta mpC.base2.acval envC ψ (rc.rP + cA.2 + 1)
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
  rw [hihq] at hcal hrPc hspK
  have hQq : Q.ihs[q]? = some ih := by
    rw [← hihd, Array.getElem?_eq_getElem (by simpa using hq)]; simp
  obtain ⟨Lr, hLr, -, -⟩ := hlamR q ih hQq
  rw [hLr, Option.getD_some]
  have hLr' := hLr
  unfold targetCallLam at hLr'
  rw [← ConLeche.Expr.instantiateList_nil (Expr.mkLamsOf _ _) 0,
    show rc.rP + cA.2 + 1 = rc.rP + cA.2 + 1 + 0 from rfl] at hLr'
  obtain ⟨dsL, bodyL, osL, rfl, hdomsL, hbitsL, hosL, hbodyL⟩ :=
    denoteMeta_mkLamsOf (acval := mpC.base2.acval) (env := envC) (φ := ψ)
      (D := rc.rP + cA.2 + 1) _ _ 0 [] _ (LocList.nil _) hLr'
  -- the telescope, at the frame and one slot deeper
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf hCb hCc
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
  have hdeep := teleDoms_deepen (acval := mpC.base2.acval) (env := envC) (φ := ψ) hacl 1
    (rc.rP + cA.2) _ 0 [] [] hleavesT (LocList.nil _) (LocList.nil _)
  rw [hdomsL] at hdeep
  obtain ⟨ts, hts, hlift⟩ : ∃ ts, teleDoms mpC.base2.acval envC ψ (rc.rP + cA.2) []
      (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1)) = some ts ∧
      dsL.map (·.2) = liftAt 1 0 ts := by
    cases hts : teleDoms mpC.base2.acval envC ψ (rc.rP + cA.2) []
        (((Q.fnorm.map fun t => t.piBinders.1).getD ih.field []).map (·.1)) with
    | none => rw [hts] at hdeep; exact nomatch hdeep
    | some ts => rw [hts] at hdeep; exact ⟨ts, rfl, Option.some.inj hdeep⟩
  have hTel : (tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (fun cv : ConstantVal => cv.type))
      out c j).teles = Q.fnorm.map fun t => t.piBinders.1 := congrArg (·.teles) hFrEq
  have hTLq : tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval envC
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
    have e1 : ((tgtTlA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
        envC ψ c j q).getD bs.length default).2.2 = ts.getD bs.length default := by
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
  · -- the call target: a major of the callee's class and a call
    have hspC := hspK bs hbs
    have hxl1 : xs.length = pp.toBlockShape.rulePrefixAt ih.callee := by rw [hrPc, hxsc]
    obtain ⟨-, -, hIs, hCr⟩ := tgtCls_hsplit hμ hcov h R hcls hmr hM ψ ρ ih.callee hcal _ hspC
    simp only [prefOf_split hxl1, idxOf_split hxl1, majOf_split] at hIs hCr
    have hU := tagged_mem_unionSet hcal hIs hCr
    have hkm : (q, ih.callee) ∈ tgtKeys μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
        c j := by
      simp only [tgtKeys, List.mem_map, List.mem_range]
      exact ⟨q, hq', by rw [hihq]⟩
    have hcall : tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
        envC ψ (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs
        (tagged ih.callee ((tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ih.callee
          ((tgtEisA μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ c j q).map (interp V (consList bs (consList (xs ++ fs) ρ)))))
          (interp V (consList bs (consList (xs ++ fs) ρ)) (tgtFapA μ F (mkFEnv envC) pp.toBlockShape
            (cvTas.map (·.type)) out mpC.base2.acval envC ψ c j q))) :=
      ⟨(q, ih.callee), hkm, bs, hbs, rfl⟩
    show app (graph r _) _ = _
    rw [app_graph (mem_graphPredG.mpr ⟨hU, hcall⟩), hfold ih.callee hcal _ _ hxl1 hspC]
    -- the λ's body: the callee variable along the call spine
    have hbl : bs.length = m := by
      rw [hbs.length_eq, hTLq, List.length_map, List.length_map, htsl, ← hmdef]
      have := congrArg List.length hbitsL
      simpa using this
    have hxl : xs.length = rc.rP := by rw [hxsc, hrP]
    rw [instantiateList_mkAppN] at hbodyL
    simp only [Expr.instantiateList] at hbodyL
    obtain ⟨fa, wsL, hfa, hwsL, rfl⟩ := denoteMeta_mkAppN_inv hbodyL
    rw [denoteMeta_fvar] at hfa
    obtain rfl := Option.some.inj hfa
    have hvals := (tgtCallArgs_run mpC.base2 ψ hle hbf hFr hher hB hFrEq hihMem hihq
      hmdef).2.2 1 [a ih.callee] xs fs bs ρ osL wsL rfl hbl hxl hfsl hosL hwsL
    rw [interp_mkAppN_foldl]
    have hhead : interp V (consList bs (cons (a ih.callee) (consList (xs ++ fs) ρ)))
        (.bvar (rc.rP + cA.2 + 1 + m - 1 - (rc.rP + cA.2))) = a ih.callee := by
      rw [interp_bvar, show rc.rP + cA.2 + 1 + m - 1 - (rc.rP + cA.2) = 0 + bs.length from by
        rw [hbl]; omega, consList_apply_add]
      rfl
    rw [hhead]
    exact congrArg (List.foldl app (a ih.callee)) hvals.symm

set_option maxHeartbeats 4000000 in
/-- **THE RECURSOR MODEL OVER THE CLASSES, the `ih` rows discharged**:
`tgtRecPre_cls` with `hihF` and `hchain` at every class (`tgtCls_hihF`,
`tgtCls_hchain`); the induction over the classes `hind` stays a premise. -/
theorem tgtRecPre_clsI (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
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
    (hM : BlockModelAt mpC.base2 names d) (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    (hnd : d.memberNames.Nodup)
    (ψ : Name → Nat) (ρ : Nat → V)
    -- the induction over the classes
    (hind : TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape (cvTas.map (·.type)) out
      d Dc mc cvc ψ ρ) :
    ∃ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) ∧
      ∀ e ∈ iotaEqsAV (tgtRs out).length (blockRecNCt (tgtRs out))
          (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
          (fun c j => liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
          (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
          (tgtIhsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out mpC.base2.acval
            envC ψ)
          (fun c j => (tgtRbAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
              mpC.base2.acval envC ψ c j).liftN (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c
                j).length
              + (tgtIhsAV μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out
                mpC.base2.acval envC ψ c j).length)),
        (pt : V) ∈ˢ interp V (chainFrame (tgtRs out).length a ρ) e := by
  have H := tgtRecPre_cls hμ hcov h R hcls hdR hN hS hcore hmr hM hlfp ψ ρ
    (fun xs c hc j hj i fs hi hf g hg => by
      have := tgtCls_hihF hμ hcov h R hcls hdR hN hS hcore hmr hM hnd ψ ρ xs c hc j hj i fs hi hf g
        hg
      exact this)
    (fun xs P hP u hu => by
      have := hind xs P hP u hu
      exact this)
    (fun a xs r hr c hc j hj fs hxl hsp => by
      have := tgtCls_hchain hμ hcov h R hcls hdR hN hS hcore hmr hM hnd ψ ρ a xs r hr c hc j hj fs
        hxl hsp
      exact this)
  obtain ⟨a, ha, hb⟩ := H
  exact ⟨a, ha, fun e he => hb e he⟩

end Rows

end ConLeche.Model
