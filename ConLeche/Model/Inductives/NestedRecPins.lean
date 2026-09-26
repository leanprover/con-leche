module

import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Verify.InstSpine
import ConLeche.Verify.AbstractRange
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.InstLevels
import ConLeche.Verify.BridgeWfImp
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.NestedRecRest
public import ConLeche.Model.Inductives.BlockRecAssembly
public import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Model.Inductives.TargetOutCerts
import ConLeche.Model.Inductives.TargetOutCa
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.IndPinGrade
import ConLeche.Model.IndOpenRev
import ConLeche.Model.RecRulesCons
import ConLeche.Model.Levels
import ConLeche.Semantics.Tower.FixLeafI

public section

/-!
# The nested recursors' stage: the `.nested` pins' law (L6, lane RECREST)

`NestedRecRest.pins` (`RecRulePinsOk` at every stored rule of the target
family).  A rule fires `.nested` only at an OUTSIDE major
(`tgtFireOf`); there its pins are the major's parameters closed over the
rule prefix (`nestedRuleSyn_open`), so instantiated back at the prefix
openers they ARE the parameters (`instSeq_abstractRange_open`), whose
readings are graded at every prefix spine (`tgtOutSatW`).
`nestedPinGrade` (cnF = 0) carries that grading to the conjunct's chain.
-/

namespace ConLeche

/-! ## The round trip, the other way: closing then opening -/

/-- **Closing a term over the opened variables, then opening it again,
is the identity**: a term whose fvar leaves are all among the openers
`0 … n-1` (in position), abstracted over that range at cursor `c` and
instantiated back at the openers, is itself. -/
theorem instSeq_abstractRange_open {pre : List Expr}
    (hpre : ∀ j (hj : j < pre.length), ∃ ty, pre[j] = .fvar j ty) :
    ∀ (x : Expr) (c : Nat), x.looseBVarsBounded c = true →
      (∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ pre) →
      Expr.instSeq pre (c + pre.length - 1) (x.abstractRange 0 pre.length c) = x := by
  have hcl : ∀ a ∈ pre, a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
    obtain ⟨ty, hty⟩ := hpre j hj
    rw [hty]; rfl
  cases hn : pre.length with
  | zero =>
    have : pre = [] := List.eq_nil_of_length_eq_zero hn
    subst this
    intro x c _ _
    rw [abstractRange_zero]; rfl
  | succ n =>
  intro x
  induction x with
  | bvar i =>
    intro c hb _
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.abstractRange]
    exact instSeq_bvar_below pre _ i (by omega)
  | fvar idx ty _ =>
    intro c _ hl
    have hmem : Expr.fvar idx ty ∈ pre := hl (idx, ty) (by simp [Expr.fvarLeaves])
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hmem
    obtain ⟨ty', hty'⟩ := hpre k hk
    rw [hkx] at hty'
    injection hty' with hik hty''
    subst hik
    simp only [Expr.abstractRange]
    rw [if_pos (by omega)]
    have hget := Expr.instSeq_bvar pre (c + (n + 1) - 1) (c + (0 + (n + 1) - 1 - idx)) hcl
      (by omega) (by omega)
    rw [show c + (n + 1) - 1 - (c + (0 + (n + 1) - 1 - idx)) = idx by omega,
      List.getElem?_eq_getElem hk, hkx] at hget
    exact (Option.some.inj hget).symm
  | sort u =>
    intro c _ _
    simp only [Expr.abstractRange]
    exact Expr.instSeq_eq_self pre _ (by rfl)
  | const nm us =>
    intro c _ _
    simp only [Expr.abstractRange]
    exact Expr.instSeq_eq_self pre _ (by rfl)
  | lit l =>
    intro c _ _
    simp only [Expr.abstractRange]
    exact Expr.instSeq_eq_self pre _ (by rfl)
  | app f a ihf iha =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange]
    rw [Expr.instSeq_app, ihf c hb.1 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      iha c hb.2 (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]
  | lam ty b m iht ihb =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange]
    rw [instSeq_lam pre _ _ _ _ (by omega),
      iht c hb.1 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) (by rw [show c + 1 = c + 1 from rfl]; exact hb.2)
        (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]
  | forallE ty b m iht ihb =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange]
    rw [Expr.instSeq_forallE pre _ _ _ _ (by omega),
      iht c hb.1 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) hb.2 (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]
  | letE ty v b iht ihv ihb =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.abstractRange]
    rw [instSeq_letE pre _ _ _ _ (by omega),
      iht c hb.1.1 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      ihv c hb.1.2 (fun l h => hl l (by simp [Expr.fvarLeaves, h])),
      show c + (n + 1) - 1 + 1 = (c + 1) + (n + 1) - 1 by omega,
      ihb (c + 1) hb.2 (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]
  | proj s i e ih =>
    intro c hb hl
    simp only [Expr.looseBVarsBounded] at hb
    simp only [Expr.abstractRange]
    rw [instSeq_proj, ih c hb (fun l h => hl l (by simp [Expr.fvarLeaves, h]))]

/-- Level instantiation commutes with the reverse opening. -/
theorem openRev_instantiateLevelParams (ks : List Name) (us : List Level) (d : Nat) :
    ∀ (n : Nat) (e : Expr),
      Verify.openRev d n (e.instantiateLevelParams ks us)
        = (Verify.openRev d n e).instantiateLevelParams ks us
  | 0, _ => rfl
  | n + 1, e => by
    simp only [Verify.openRev]
    rw [openRev_instantiateLevelParams ks us d n e, Expr.instantiateLevelParams_instantiate1]
    congr 2

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Pins

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 2000000 in
/-- **L6: the `.nested` pins' law at every stored rule** (`NestedRecRest.pins`).
A `.nested` firing is an outside major's; the pins are its parameters
closed over the rule prefix, so their readings are the parameters'
(`tgtOutSatW`), graded at every prefix spine, and `nestedPinGrade`
carries the grading to the chain of any graded fit of the recursor type. -/
theorem tgtRecPinsOk (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (hcov : LfpCover mpC []) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (R : ConLeche.TargetRecRun μ F (ConLeche.mkFEnv envC) pp.toBlockShape nested block
      cvTas ctorsAs out)
    {Rr : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List AnnotTerm}
    (m₃ : EnvModel V (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC))
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC (tgtRs out) s eqs)
    (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (hr : (tgtRs out)[j]? = some r) (cA : ConstantVal × Nat) (rhs : Expr) :
    RecRulePinsOk m₃ φ r.1 (pp.toBlockShape.rulePrefixAt j)
      (ConLeche.recRuleBits envC.find? r.1.name
          { ctor := cA.1.name, nfields := cA.2, ctorParams := (ConLeche.tgtMajorsOf out j).nPc,
            fire := (ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape
              (ConLeche.tgtMajorsOf out)) j r, rhs := rhs, paramsBlind := true }) := by
  intro us hus lvls pins hf q hq
  simp only [ConLeche.recRuleBits_fire] at hf
  simp only [ConLeche.recRuleBits_ctorParams] at hq
  obtain ⟨-, -, hpinsWf, -⟩ := ConLeche.tgtFireOf_nested hf
  -- the major is outside
  have hMo : (tgtMajor out j).member = none := by
    cases hm : (tgtMajor out j).member with
    | none => rfl
    | some t =>
      have hm' : (ConLeche.tgtMajorsOf out j).member = some t := hm
      revert hf
      simp only [ConLeche.tgtFireOf, hm']
      split <;> simp
  have hm' : (ConLeche.tgtMajorsOf out j).member = none := hMo
  unfold ConLeche.tgtFireOf at hf
  rw [hm'] at hf
  simp only [ConLeche.auxRuleFireR] at hf
  cases hsyn : Expr.nestedRuleSyn (·.constsResolve envC) r.1.levelParams r.1.type
      (pp.toBlockShape.majorIdxAt j) (pp.toBlockShape.rulePrefixAt j)
      (ConLeche.tgtMajorsOf out j).nPc with
  | none => rw [hsyn] at hf; exact nomatch hf
  | some lp =>
  obtain ⟨lvls', pins'⟩ := lp
  rw [hsyn] at hf
  injection hf with hl hp
  rw [hl, hp] at hsyn
  -- the entry
  obtain ⟨rc, u, hrc, ⟨E⟩⟩ := targetEntryAt R hr
  have hRP : pp.toBlockShape.rulePrefixAt j = rc.rP := by
    rw [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hMI : pp.toBlockShape.majorIdxAt j = rc.mI := by
    rw [ConLeche.BlockShape.majorIdxAt, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hTRP : tgtRP pp.toBlockShape j = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  rw [hRP, hMI] at hsyn
  rw [hRP]
  obtain ⟨-, hpinsE⟩ := ConLeche.nestedRuleSyn_open hsyn E.hopen E.hmaj
  obtain ⟨-, -, -, -, -, hdsE, hdsLen, -, -, -⟩ := E.outside_of hMo
  have hMN : (ConLeche.tgtMajorsOf out j).nPc = (tgtMajor out j).nPc := rfl
  rw [hMN, ← hdsE] at hpinsE
  rw [hMN] at hq
  -- the `q`-th pin is the `q`-th parameter, closed
  have hqd : q < (tgtMajor out j).ds.length := by rw [hdsLen]; exact hq
  obtain ⟨x, hxdef⟩ : ∃ x, x = (tgtMajor out j).ds[q] := ⟨_, rfl⟩
  have hpinq : (pins.getD q default) = x.abstractRange 0 rc.rP := by
    rw [← hpinsE, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hqd,
      hxdef]
    rfl
  have hpinMem : pins.getD q default ∈ pins := by
    rw [hpinq, hxdef, ← hpinsE]
    exact List.mem_map_of_mem (List.getElem_mem hqd)
  obtain ⟨hpF, -, hpR, hpB⟩ := hpinsWf _ hpinMem
  rw [hRP] at hpB
  -- the prefix openers
  obtain ⟨hw0, -⟩ := recStage_tyClosed h hr
  obtain ⟨oP, hopP⟩ := ConLeche.openPisAtFvars_prefix rc.rP (rc.mI + 1) r.1.type 0
    (by have := E.hle; omega) E.hopen
  have hoslen : (E.fvs.take rc.rP).length = rc.rP := by
    have := ConLeche.Verify.openPisAtFvars_length _ hopP
    exact this
  have hshape : ∀ (k : Nat) (y : Expr), (E.fvs.take rc.rP)[k]? = some y →
      ∃ ty, y = Expr.fvar k ty := by
    intro k y hy
    simpa using ConLeche.openPisAtFvars_index _ _ _ hopP k y hy
  have hpre : ∀ k (hk : k < (E.fvs.take rc.rP).length), ∃ ty,
      (E.fvs.take rc.rP)[k] = .fvar k ty := by
    intro k hk
    obtain ⟨ty, hty⟩ := hshape k _ (List.getElem?_eq_getElem hk)
    exact ⟨ty, hty⟩
  have hwsOs : ∀ y ∈ E.fvs.take rc.rP, Expr.WScoped (rc.rP + 0) y := by
    intro y hy
    have := (openPisAtFvars_WScoped _ _ 0 hopP hw0).1 y hy
    simpa using this
  have hbOs : ∀ y ∈ E.fvs.take rc.rP, y.looseBVarsBounded 0 = true := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    obtain ⟨ty, hty⟩ := hpre k hk
    rw [hty]; rfl
  -- the parameter's scoping at the prefix
  have hDs := tgtOutDsOk h R hr hMo
  have hPref : tgtPrefFvs pp.toBlockShape out j = E.fvs.take rc.rP := by
    rw [tgtPrefFvs, tgtRecTy_at hr, hTRP, hopP]; rfl
  rw [hTRP, hPref] at hDs
  obtain ⟨-, hxb, -, hxl⟩ := hDs x (by rw [hxdef]; exact List.getElem_mem hqd)
  -- the round trip: the pin opened at the prefix openers IS the parameter
  have hround : Expr.instSpine (E.fvs.take rc.rP) (rc.rP - 1) (pins.getD q default) = x := by
    rw [hpinq, Expr.instSpine_eq_instSeq]
    have := ConLeche.instSeq_abstractRange_open hpre x 0 hxb hxl
    rw [hoslen, Nat.zero_add] at this
    exact this
  -- the level valuation the instantiation reads at
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = Level.substFn φ r.1.levelParams us := ⟨_, rfl⟩
  -- the parameter's reading and its grading
  obtain ⟨D, mm, cvI, hcl⟩ := tgtOutCls_of hcov E hMo
  obtain ⟨dsa, hdsa, -, -, -, hsatW⟩ := tgtOutSatW hμ mpC hcov h R hr hMo hcl ψ
  rw [hTRP] at hdsa hsatW
  obtain ⟨w, -, hw⟩ : ∃ w ∈ dsa, denoteMeta mpC.base2.acval envC ψ rc.rP x = some w :=
    DenoteMetaSpine.mem_val hdsa x (by rw [hxdef]; exact List.getElem_mem hqd)
  have hwGr : ∀ σ : Nat → V,
      Sat V (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).reverse σ →
      WellDenotedV V σ w := by
    intro σ hσ
    have hsp := spineFit_frameIdx_of_sat hσ
    obtain ⟨-, hgr⟩ := hsatW _ _ hsp
    rw [consList_frameIdx] at hgr
    exact hgr w (by
      obtain ⟨w', hw'm, hw'⟩ := DenoteMetaSpine.mem_val hdsa x (by rw [hxdef]; exact List.getElem_mem hqd)
      rw [hw'] at hw
      obtain rfl := Option.some.inj hw
      exact hw'm)
  -- the opened pin's reading, at the constructors' environment
  have hacl := mpC.base2.acval_closed
  have hainst : ∀ (n : Name) (ψ' : Name → Nat) (y : AnnotTerm) (k : Nat),
      (mpC.base2.acval n ψ').inst y k = mpC.base2.acval n ψ' :=
    fun n ψ' y k => AVExprSubst.inst_eq_self_of_closed (mpC.base2.acval_closed n ψ') y k
  have hw' : denoteMeta mpC.base2.acval envC ψ (rc.rP + 0)
      (Expr.instSpine (E.fvs.take rc.rP) (rc.rP - 1) (pins.getD q default)) = some w := by
    rw [hround, Nat.add_zero]; exact hw
  obtain ⟨vpa, hvpden⟩ := pinOpenRevReads (acval := mpC.base2.acval) (cval := mpC.base2.cvalE)
    (env := envC) (φ := ψ) hacl hainst mpC.base2.acval_erase mpC.base2.cval_closed hoslen hshape
    hwsOs hbOs hpF hpB hw'
  -- carried to the recursors' environment and valuation
  have hcbP : ConstsBound envC (pins.getD q default) := constsBound_of_constsResolve _ hpR
  refine ⟨vpa, ?_, ?_⟩
  · rw [ConLeche.openRev_instantiateLevelParams,
      denoteMeta_instLevels (acvalParamsAt_of_core m₃) φ, ← hψ]
    exact blockRecDenote_cross h hac ψ rc.rP _ (constsBound_openRev hcbP 0 rc.rP) hvpden
  · intro ρ zs TVa restR hzslen hzsOk hTVa hfit
    obtain rfl := blockRuleTVa_run hμ mpC h hac hr φ us hTVa
    rw [← hψ] at hfit
    -- the recursor type's prefix telescope
    obtain ⟨-, -, -, -, hTyE, hlenRds, -, -, -, -⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
    rw [hMI] at hlenRds
    have hPdE : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
        = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).take
            rc.rP).map (·.2.2) := by
      rw [blockRulePdomsAV, ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, hrc,
        Option.getD_some]
    have htake : ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).take
        rc.rP).length = rc.rP := by
      rw [List.length_take, hlenRds]; have := E.hle; omega
    have htower : PiTeleAV rc.rP (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).reverse
        (mkPisAV ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).drop
            rc.rP)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)) := by
      rw [hTyE, hPdE, ← List.take_append_drop rc.rP
          (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j), mkPisAV_append,
        List.take_append_drop]
      have := piTeleAV_mkPisAV ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape
        (tgtRs out) ψ j).take rc.rP) (mkPisAV ((blockRecRdsAV mpC.base2.acval envC
          pp.toBlockShape (tgtRs out) ψ j).drop rc.rP)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j))
      rwa [htake] at this
    refine nestedPinGrade (acval := mpC.base2.acval) (cval := mpC.base2.cvalE) (env := envC)
      (φ := ψ) (cnF := 0) hacl hainst mpC.base2.acval_erase mpC.base2.cval_closed hoslen hshape
      hwsOs hbOs hpF hpB hvpden htower ?_ hzslen hzsOk hfit
    intro w0 hw0 σ hσ
    rw [hw'] at hw0
    obtain rfl := Option.some.inj hw0
    exact hwGr σ (by simpa using hσ)

end Pins

end ConLeche.Model
