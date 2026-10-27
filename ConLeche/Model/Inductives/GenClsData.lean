module

public import ConLeche.Model.Inductives.GenClsRhs
import ConLeche.Model.Inductives.GenRecRules
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.GenClsMinor
import ConLeche.Model.Inductives.GenClsFrame
import ConLeche.Model.Inductives.GenClsCall
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.GenRecPins
import ConLeche.Model.Inductives.GenRecClasses
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.ContInst
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetGraph
import ConLeche.Model.Inductives.NestedRecPins
import ConLeche.Model.Env.BlockLfp
import ConLeche.Verify.Denote.Closed
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Verify.Denote.Inst
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Levels
import ConLeche.Model.NatEqs
import ConLeche.Model.IndOpenRev
import ConLeche.Model.IndPinGrade
import ConLeche.Verify.InstSpine
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.Rules.InferSoundKit
public import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.EnvBound
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The generated rules' data rows (lane GENREC-C's `hrow3`)

`BlockRuleRows3` at every fired pair of the generated family: the ι
firing's spine fits the rule frame, the declared index expressions read
as the recursor's index arguments, and the fired spine reads as the
constructor application.

The class side does the work (`GenClsSplit`, `GenClsDec`,
`GenClsDecInv`): once the fired constructor's fields are known to
hole-fit at the RECURSOR's parameter frame and the major to be their
injection, the decoding's inverse gives the fields' fit and the tuple's
spelling, and the decoding the fired spine.  That fact is the major
premise's content — the ι rule compares no parameters:

* at an OUTSIDE class the rule fires `.nested`: the constructor's
  parameters ARE the class's parameters at the prefix (the pins), so the
  constructor's own fit, peeled at them, fits the rule frame's fields;
  the major lies in the class's carrier at the recursor's index tuple
  and, the class never `Prop` at a non-zero elimination level, the
  carrier's decomposition is unique;
* at a MEMBER class (`.plain`) the block's own route: the carrier at the
  recursor's parameters decomposes the major, uniquely at a `Type`-valued
  block (`blockRuleStoredFit_run`), by the subsingleton criterion at a
  `Prop`-valued one (`blockRuleStoredFit_sq`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState
  closeTelescope)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Value-level fits along a peel -/

section Fits

open ConLeche.Model.Rules (PiChain piChain_succ_inv PiChain.inst teleFit_inst0_of)

/-- **A fit continues past a peel**: fitting a ∀-chain at a spine's
values followed by more values, the peel's residual fits the rest. -/
theorem teleFit_peel' :
    ∀ (ws : List Term) {T C : Term} {σ : Nat → V} {fs : List V} {X : V},
      Term.peelPis T ws = some C →
      PiChain (ws.length + fs.length) T →
      TeleFit V σ T (ws.map (interp V σ) ++ fs) X → TeleFit V σ C fs X
  | [], T, C, σ, fs, X, hp, _, h => by
    obtain rfl : T = C := Option.some.inj hp
    simpa using h
  | w :: ws, T, C, σ, fs, X, hp, hpc, h => by
    have hpc' : PiChain ((ws.length + fs.length) + 1) T := by
      simpa [Nat.add_right_comm] using hpc
    obtain ⟨A, B, rfl, hB⟩ := piChain_succ_inv hpc'
    simp only [Term.peelPis] at hp
    rw [List.map_cons, List.cons_append] at h
    cases h with
    | cons _ hfit =>
      exact teleFit_peel' ws hp (PiChain.inst w 0 hB)
        (teleFit_inst0_of (by simpa using hB) hfit)

/-- **A fit moves between frames agreeing below the term's bound.** -/
theorem teleFit_congr_frame' :
    ∀ (vals : List V) {T : Term} {n : Nat} {ρ ρ' : Nat → V} {X : V},
      Term.bvarsBelow n T → (∀ k, k < n → ρ k = ρ' k) →
      TeleFit V ρ T vals X → ∃ X', TeleFit V ρ' T vals X'
  | [], T, _, _, ρ', _, _, _, _ => ⟨_, .nil⟩
  | a :: as, _, n, ρ, ρ', X, hb, hag, h => by
    cases h with
    | cons hmem hfit =>
      obtain ⟨hA, hB⟩ := hb
      obtain ⟨X', hX'⟩ := teleFit_congr_frame' as (n := n + 1) (ρ := cons a ρ)
        (ρ' := cons a ρ') hB (fun k hk => by
          cases k with
          | zero => rfl
          | succ k => exact hag k (by omega)) hfit
      exact ⟨X', .cons (by rw [← interp_congr_below V _ n ρ ρ' hA hag]; exact hmem) hX'⟩

end Fits

/-! ## An outside class's constructor, fitted at the class's parameters -/

section OutFit

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

set_option maxHeartbeats 4000000 in
/-- **The instantiated constructor, as a fit of the stored type** at an
outside class: the constructor's stored type reads, at the class's
levels, as a closed graded Π-tower whose outer binders are the class's
parameter count, and at a prefix spine fitting the rule prefix the
parameters' readings fit it, the residual being the rule frame's
constructor (`tgtCrest`) as read at the prefix. -/
theorem genOutCtorFit (hμ : μ.isVerified = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC [])
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hMo : (tgtMajor out c).member = none) (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c)
    (ψ : Name → Nat) (ρ : Nat → V) {xs : List V}
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs)
    {cA : ConstantVal × Nat} (hcA : (tgtMajor out c).ctors[j]? = some cA) :
    ∃ (T0 : Term) (pps : List Term) (b0 : Term),
      ConstantInfo.ctorInfo cA.1 (tgtMajor out c).ds.length cA.2 ∈ envC.consts ∧
      cA.1.levelParams = cvI.levelParams ∧
      denote mpC.base2.acval envC (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls) 0
        cA.1.type = some T0 ∧
      T0 = mkPisAV pps b0 ∧ pps.length = (tgtMajor out c).ds.length ∧
      (∀ σ : Nat → V, WellDenoted V σ T0) ∧ Term.bvarsBelow 0 T0 ∧
      Rules.PiChain ((tgtMajor out c).ds.length + cA.2) T0 ∧
      ∀ C : Term,
        denote mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c) (tgtCrest out c j) = some C →
        TeleFitPA V (consList xs ρ) T0 (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
          C := by
  have hacl := mpC.base2.acval_closed
  have hDe : tgtClsD d Dc out c = Dc c := by simp [tgtClsD, hMo]
  have hMe : tgtClsM mc pp.toBlockShape out c = mc c := by simp [tgtClsM, hMo]
  have hsatK := Rd.hsat ψ ρ xs hpref
  rw [Rd.hψ] at hsatK
  obtain ⟨hjD, hfc0, hlpC, -⟩ := Rd.hctor j cA hcA
  obtain ⟨-, -, -, hcrd, -⟩ := mpC.lfp_ok _ Rd.hD
  obtain ⟨cv', nPc', nF', hf', -, -, hpars, -⟩ := hcrd.2 _ Rd.hmm j hjD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out c).ds.length = nPc' ∧ cA.2 = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hcons := List.mem_of_find?_eq_some hfc0
  have hwfC := mpC.base2.wf.consts _ hcons
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  -- the stored type's reading at the class's levels, graded
  obtain ⟨T0, hT0⟩ := mpC.type_reads _ hcons
    (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
  change denote mpC.base2.acval envC (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
    0 cA.1.type = some T0 at hT0
  have hT0wd := fun ρ => (mpC.type_wellDenotedTy _ hcons _ T0 hT0 ρ).1
  have hT0cl : Term.bvarsBelow 0 T0 :=
    bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hCf) hCb hT0
  -- its outer parameter binders
  obtain ⟨cv8, nPc8, nF8, hf8, bs, args, hstrip, -⟩ :=
    (hcov.own _ Rd.hD).ctorConcl _ Rd.hmm j hjD
  rw [hfc0] at hf8
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv8 ∧ (tgtMajor out c).ds.length = nPc8 ∧ cA.2 = nF8 := by
    injection hf8 with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hpcT : Rules.PiChain ((tgtMajor out c).ds.length + cA.2) T0 :=
    Rules.piChain_of_stripPis _ (by rw [hstrip]; rfl) hT0
  obtain ⟨fvsA, oA, hopA⟩ := openPisAtFvars_of_stripPis_isSome
    ((tgtMajor out c).ds.length + cA.2) (e := cA.1.type) 0 (by rw [hstrip]; rfl)
  obtain ⟨oP, hopP⟩ := ConLeche.openPisAtFvars_prefix (tgtMajor out c).ds.length
    ((tgtMajor out c).ds.length + cA.2) _ 0 (Nat.le_add_right _ _) hopA
  obtain ⟨pps, b0, hst, -, hplen, -⟩ := denote_openPis (tgtMajor out c).ds.length hopP hT0
  obtain ⟨hT0E, -⟩ := stripPisAV_eq_mkPis hst
  -- the parameters' readings fit the constructor's parameter binders
  have hsatC := hpars _ pps b0 (by rw [← hT0E]; exact hT0) (Nat.le_of_eq hplen.symm) _ hsatK
  rw [List.take_of_length_le (Nat.le_of_eq hplen)] at hsatC
  have hdsa := Rd.hdsa ψ
  have hdl : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).length
      = (tgtMajor out c).ds.length := (DenoteSpine.length_eq hdsa).symm
  have hspK := spineFit_of_sat_consList (Ds := pps)
    (as := (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).map (interp V (consList xs ρ)))
    (by rw [List.length_map, hdl, hplen])
    (by simpa only [keyFrame] using hsatC)
  rw [hT0E] at hT0cl
  have hbnd : ∀ l, l < pps.length →
      Term.bvarsBelow l (pps.getD l default) := by
    intro l hl
    have := (bvarsBelow_mkPisAV_inv hT0cl).1.getD_below l hl
    rwa [Nat.zero_add] at this
  have hsp := spineFit_frame_of_bounded (σ' := consList xs ρ) hbnd hspK
  obtain ⟨rest, hTF⟩ := teleFitPA_mkPisAV_of_spineFit (pds := pps) (b := b0)
    (ws := tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
    (by rw [hdl, hplen]) hsp
  -- the rule frame's constructor IS the instantiation
  obtain ⟨cls, cA', fvs, cb, -, hMcls, hcA', -, ⟨CR⟩, -, hcrest, -, -, -, -, -, -⟩ :=
    genRun_frame hμ R hg hc hj
  have hcc : cA = cA' := Option.some.inj (hcA.symm.trans hcA')
  subst hcc
  have hcr : ConLeche.instPisWith (tgtMajor out c).ds
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out c).lvls)
        = some (tgtCrest out c j) := by
    have h0 := CR.hD
    rw [← hMcls, Rd.hctorAt cA.1 hlpC] at h0
    rw [hcrest]; exact h0
  rw [ConLeche.instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨doms, crest'⟩, hinst, hcr'⟩ := Option.map_eq_some_iff.mp hcr
  obtain rfl : crest' = tgtCrest out c j := hcr'
  have hTy : denote mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c)
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out c).lvls) = some T0 := by
    rw [denote_instLevels mpC.base2.acval_params ψ, hlpC]
    exact denote_depth_of_closed hacl hCf
      (fun k => denote_liftN_eq_self mpC.base2.cval_closed hCf hCb hT0 1 k)
      hT0 _
  have hds' : ∀ x ∈ (tgtMajor out c).ds, Expr.WScoped (tgtRP pp.toBlockShape c) x ∧
      x.looseBVarsBounded 0 = true := by
    intro x hx
    exact ⟨(Rd.hds x hx).1.mono (by rw [tgtRP]; exact hnP), (Rd.hds x hx).2⟩
  obtain ⟨restA, hrest, hpeel⟩ := Rules.denote_instPisAt_peel hacl (acval_inst_self mpC.base2)
    _ hinst (Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hCf))
    hds' hTy hdsa
  have hpe := hTF.peelPis
  rw [← hT0E, hpeel] at hpe
  obtain rfl := Option.some.inj hpe
  refine ⟨T0, pps, b0, hcons, hlpC, hT0, hT0E, hplen, hT0wd, ?_, hpcT,
    fun C hC => ?_⟩
  · rw [hT0E]; exact hT0cl
  · rw [hrest] at hC
    obtain rfl := Option.some.inj hC
    rw [hT0E]; exact hTF

/-- **A `.nested` firing's pins, valued** (at an outside class): the
levels are the class's, and the `q`-th pin, instantiated at the rule's
level arguments and opened at the prefix, reads, and its chain at any
prefix spine is the `q`-th parameter's reading at that spine's frame —
the pin is the class's `q`-th parameter closed over the prefix
(`tgtFireOf_nested_eq`), so opened at the stored type's prefix openers
it is that parameter up to erasure (`instSeq_abstractRange_open`). -/
theorem genOutPinVal
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (h : ConLeche.RecStageG μ F envC pp cvTas (tgtRs out))
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[c]? = some r)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    {lvls : List Level} {pins : List Expr}
    (hf : ConLeche.tgtFireOf pp.toBlockShape (ConLeche.tgtMajorsOf out) c r
      = .nested lvls pins)
    (φ : Name → Nat) (us : List Level) :
    lvls = (tgtMajor out c).lvls ∧
    ∀ q, q < (tgtMajor out c).nPc → ∃ vpa : Term,
      denote mpC.base2.acval envC φ (pp.toBlockShape.rulePrefixAt c)
          (openRev 0 (pp.toBlockShape.rulePrefixAt c)
            ((pins.getD q default).instantiateLevelParams r.1.levelParams us)) = some vpa ∧
      ∀ (ρ : Nat → V) (zs : List Term), zs.length = pp.toBlockShape.rulePrefixAt c →
        interp V ρ (Term.instRevChain zs vpa)
          = interp V (consList (zs.map (interp V ρ)) ρ)
              ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out
                (Level.substFn φ r.1.levelParams us) c).getD q default) := by
  have hsyn := R.fire_nestedRead hr hf
  obtain ⟨-, -, hpinsWf, -⟩ := id hsyn
  obtain ⟨-, rfl, hpinsE⟩ := ConLeche.tgtFireOf_nested_eq hf
  refine ⟨rfl, fun q hq => ?_⟩
  -- the stored type's openers
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  have hopen := TE.hopen
  obtain ⟨rP, hRP⟩ : ∃ n, pp.toBlockShape.rulePrefixAt c = n := ⟨_, rfl⟩
  obtain ⟨mI, hMI⟩ : ∃ n, pp.toBlockShape.majorIdxAt c = n := ⟨_, rfl⟩
  have hle0 : rP ≤ mI := by have := TE.hmI'; omega
  rw [hRP] at hpinsE ⊢
  rw [hMI] at hopen
  -- the `q`-th pin is the `q`-th parameter, closed
  have hqds : q < (tgtMajor out c).ds.length := by have := Rd.hnpc; omega
  obtain ⟨y, hydef⟩ : ∃ y, y = (tgtMajor out c).ds[q] := ⟨_, rfl⟩
  have hpinsL : pins.length = (tgtMajor out c).ds.length := by
    rw [hpinsE, List.length_map]; rfl
  have hpinq : pins.getD q default = y.abstractRange 0 rP := by
    have : pins[q]'(by omega) = Expr.abstractPrefix rP 0 y := by
      simp only [hpinsE, List.getElem_map, hydef]; rfl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some, this,
      ConLeche.abstractPrefix_eq]
  have hpinMem : pins.getD q default ∈ pins := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  obtain ⟨hpF, -, -, hpB⟩ := hpinsWf _ hpinMem
  rw [hRP] at hpB
  -- the prefix openers
  obtain ⟨hw0, hb0⟩ := recStage_tyClosed h hr
  obtain ⟨oP, hopP⟩ := ConLeche.openPisAtFvars_prefix rP (mI + 1) r.1.type 0
    (by omega) hopen
  have hoslen : (TE.fvs.take rP).length = rP := ConLeche.Verify.openPisAtFvars_length _ hopP
  have hshape : ∀ (k : Nat) (y : Expr), (TE.fvs.take rP)[k]? = some y →
      ∃ ty, y = Expr.fvar k ty := by
    intro k y hy
    simpa using ConLeche.openPisAtFvars_index _ _ _ hopP k y hy
  have hpre : ∀ k (hk : k < (TE.fvs.take rP).length), ∃ ty,
      (TE.fvs.take rP)[k] = .fvar k ty := by
    intro k hk
    obtain ⟨ty, hty⟩ := hshape k _ (List.getElem?_eq_getElem hk)
    exact ⟨ty, hty⟩
  have hwsOs : ∀ y ∈ TE.fvs.take rP, Expr.WScoped (rP + 0) y := by
    intro y hy
    have := (openPisAtFvars_WScoped _ _ 0 hopP hw0).1 y hy
    simpa using this
  have hbOs : ∀ y ∈ TE.fvs.take rP, y.looseBVarsBounded 0 = true := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    obtain ⟨ty, hty⟩ := hpre k hk
    rw [hty]; rfl
  -- the round trip: the pin opened at the prefix openers is the parameter, up to erasure
  have hyds := Rd.hds y (by rw [hydef]; exact List.getElem_mem hqds)
  have hylt : ∀ l ∈ y.fvarLeaves, l.1 < rP := fun l hl =>
    ConLeche.Expr.fvarLeaves_lt_of_wscoped
      (ConLeche.WScoped.of_abstractRange_noFvar hyds.1 (by rw [← hpinq]; exact hpF)) l hl
  have hround : Expr.ErasedEq (Expr.instSpine (TE.fvs.take rP) (rP - 1) (pins.getD q default))
      y := by
    rw [hpinq, Expr.instSpine_eq_instSeq]
    have := ConLeche.instSeq_abstractRange_open hpre y 0 hyds.2 (by rw [hoslen]; exact hylt)
    rw [hoslen, Nat.zero_add] at this
    exact this
  -- the parameter's reading is the class's parameter's
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = Level.substFn φ r.1.levelParams us := ⟨_, rfl⟩
  have hdq := DenoteSpine.getD (Rd.hdsa ψ) default q hqds
  have hTRP : tgtRP pp.toBlockShape c = rP := by rw [tgtRP]; exact hRP
  rw [hTRP, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hqds, Option.getD_some,
    ← hydef] at hdq
  have hacl := mpC.base2.acval_closed
  have hainst : ∀ (n : Name) (ψ' : Name → Nat) (y : Term) (k : Nat),
      (mpC.base2.acval n ψ').inst y k = mpC.base2.acval n ψ' :=
    fun n ψ' y k => AVExprSubst.inst_eq_self_of_closed (mpC.base2.acval_closed n ψ') y k
  have hw' : denote mpC.base2.acval envC ψ (rP + 0)
      (Expr.instSpine (TE.fvs.take rP) (rP - 1) (pins.getD q default))
        = some ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).getD q default) := by
    rw [denote_erasedEq hround, Nat.add_zero]; exact hdq
  obtain ⟨vpa, hvpden⟩ := pinOpenRevReads (acval := mpC.base2.acval)
    (env := envC) (φ := ψ) hacl hainst mpC.base2.cval_closed hoslen hshape
    hwsOs hbOs hpF hpB hw'
  refine ⟨vpa, ?_, fun ρ zs hzs => ?_⟩
  · rw [ConLeche.openRev_instantiateLevelParams,
      denote_instLevels mpC.base2.acval_params φ, ← hψ]
    exact hvpden
  · obtain ⟨w0, hw0', hcross⟩ := pinCross (acval := mpC.base2.acval)
      (env := envC) (φ := ψ) (cnF := 0) hacl hainst mpC.base2.cval_closed
      padA hoslen hshape hwsOs hbOs hpF hpB hvpden hzs (vals := zs) (n := rP) hzs
      (Nat.le_refl _) (by omega) (List.take_of_length_le (Nat.le_of_eq hzs))
    obtain rfl := Option.some.inj (hw0'.symm.trans hw')
    rw [← hψ, ← hcross, show rP + 0 - rP = 0 from by omega, List.replicate_zero,
      List.append_nil, show rP + 0 - 1 = zs.length - 1 from by omega, interp_instSeq,
      chain_eq_consList]

end OutFit


/-! ## The elimination guard and an outside class's sort -/

section Guard

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

/-- A non-zero elimination level is a large eliminator. -/
theorem genLarge_of_ne {ψ : Name → Nat}
    (hℓ : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0) :
    pp.toBlockShape.large = true := by
  cases hl : pp.toBlockShape.large with
  | true => rfl
  | false =>
    refine absurd ?_ hℓ
    simp [ConLeche.structElimLevel, hl, ConLeche.Level.eval]

/-- **Never `Prop` at an outside class**: the generated stage's guard
runs at the container bit or'ed with its outside classes (`helim`), so at
a non-zero elimination level with an outside class the block's sort is
never `Prop`. -/
theorem genOutNZ
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) (hMo : (tgtMajor out c).member = none)
    {ψ : Name → Nat}
    (hℓ : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0) :
    pp.toBlockShape.resSort.isNeverZero = true := by
  obtain ⟨-, cls, -, -, -, -, -, -, -, hM, hgc⟩ := genRun_at R hc
  have hi : cls < R.Ms.length := by rw [← hgc]; exact genRun_cls_lt R hc
  obtain ⟨key, M₀, nfs, hMs, hM₀, -⟩ := genRun_class R hi
  have hget : R.Ms.getD cls default = { M₀ with nfs := nfs } := by
    rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
  rw [hget] at hM
  have hMo₀ : M₀.member = none := by rw [hM] at hMo; exact hMo
  have hany : R.Ms₀.any (·.member.isNone) = true :=
    List.any_eq_true.mpr ⟨M₀, List.mem_of_getElem? hM₀, by simp [hMo₀]⟩
  have hel := R.helim
  rw [genLarge_of_ne hℓ, hany, Bool.or_true, Bool.true_and] at hel
  simpa [ConLeche.blockLargeElimAllowed] using hel

/-- **The counting guard**: at a non-zero elimination level and a
`Prop`-valued block, the eliminator is large and there is at most one
constructor. -/
theorem genCount
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {ψ : Name → Nat}
    (hℓ : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0)
    (hw : Level.eval ψ pp.toBlockShape.resSort = 0) :
    pp.toBlockShape.large = true ∧ pp.toBlockShape.numCtors ≤ 1 := by
  have hel := R.helim
  rw [genLarge_of_ne hℓ, Bool.true_and, Bool.not_eq_false'] at hel
  obtain ⟨hl, -, -, hcn⟩ := blockLargeElim_counting hel hw
  exact ⟨hl, hcn⟩

/-- **An outside class's sort is the block's** (the class check's
`Level.isEquiv sI p.resSort`). -/
theorem genOutW
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) (hMo : (tgtMajor out c).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal}
    (hcl : TgtOutCls mpC (tgtMajor out c) D mm cvI) (ψ : Name → Nat) :
    D.w (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
      = Level.eval ψ pp.toBlockShape.resSort := by
  obtain ⟨-, cls, -, -, -, -, -, -, -, hM, hgc⟩ := genRun_at R hc
  have hi : cls < R.Ms.length := by rw [← hgc]; exact genRun_cls_lt R hc
  obtain ⟨key, M₀, nfs, hMs, -, ⟨CR⟩⟩ := genRun_class R hi
  have hget : R.Ms.getD cls default = { M₀ with nfs := nfs } := by
    rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
  rw [hget] at hM
  have hMo₀ : M₀.member = none := by rw [hM] at hMo; exact hMo
  obtain ⟨sI, -, -, -, -, -, -, -, hinst, hequiv⟩ := CR.major.outside_facts hMo₀
  have hinst' : ConLeche.targetOutsideInst (m := ConLeche.CheckM) (mkFEnv envC)
      (tgtMajor out c).ind (tgtMajor out c).lvls (tgtMajor out c).ds
      = .ok ((tgtMajor out c).nIdx, sI) := by rw [hM]; exact hinst
  obtain ⟨cvI', caps', ty, s, hf', hty, hs, hr'⟩ := targetOutsideInst_inv hinst'
  obtain ⟨caps, hfI⟩ := hcl.hfind
  rw [mkFEnv_find?, hfI] at hf'
  obtain ⟨rfl, rfl⟩ : cvI = cvI' ∧ caps = caps' := by simpa using hf'
  obtain ⟨-, -, hrd, -⟩ := mpC.lfp_ok D hcl.hD
  obtain ⟨cv₂, caps₂, hf₂, hab⟩ := hrd mm hcl.hmm
  rw [hcl.hmem, hfI] at hf₂
  obtain ⟨rfl, rfl⟩ : cvI = cv₂ ∧ caps = caps₂ := by simpa using hf₂
  obtain ⟨ab, hta, -⟩ := hab (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
  have hsI : s = sI := (congrArg Prod.snd hr').symm
  subst hsI
  rw [instPis_sort_of_read (φ := ψ) cvI.levelParams (tgtMajor out c).lvls hta hty hs]
  exact ConLeche.Level.isEquiv_sound hequiv ψ

end Guard

/-! ## The rule frame's constructor, read -/

section Crest

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

set_option maxHeartbeats 4000000 in
/-- **The rule frame's constructor reads as a Π-tower over the field
domains** (`genCls_open`'s field half, with the tower itself). -/
theorem genCls_openCrest (hμ : μ.isVerified = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g)
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c) (ψ : Name → Nat)
    {cA : ConstantVal × Nat} (hcA0 : (tgtMajor out c).ctors[j]? = some cA) :
    ∃ (ab : List Term) (body : Term),
      ab.length = cA.2 ∧
      tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
        = Term.substTele (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
            (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) 0 ab ∧
      denote mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c) (tgtCrest out c j)
        = some (mkPisAV (Term.substTele (instTau mpC ψ (tgtClsD d Dc out c)
            (tgtMajor out c).lvls (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) 0 ab) body) := by
  obtain ⟨cls, cA', fvs, cb, hgc, hM, hcA, hctO, ⟨CR⟩, hnF, hcrest, htRP, hop, hFF, hCB, -, -⟩ :=
    genRun_frame hμ R hg hc hj
  have hcc : cA' = cA := Option.some.inj (hcA.symm.trans hcA0)
  subst hcc
  obtain ⟨hjD, hfc, hlpC, hlpsR⟩ := Rd.hctor j cA' hcA
  have hcrD := CR.hD
  rw [← hM, Rd.hctorAt cA'.1 hlpC] at hcrD
  rw [← hcrest] at hcrD hop
  have hRP : tgtRP pp.toBlockShape c = R.pre.length := htRP
  have hds' : ∀ x ∈ (tgtMajor out c).ds, Expr.WScoped (tgtRP pp.toBlockShape c) x ∧
      x.looseBVarsBounded 0 = true :=
    fun x hx => ⟨(Rd.hds x hx).1.mono hnP, (Rd.hds x hx).2⟩
  have hlenP' := Rd.hlenP ψ
  rw [Rd.hψ] at hlenP'
  rw [← hRP] at hop
  obtain ⟨-, ab, -, hlab, hrdF, -, -, hcr⟩ :=
    instCtor_open mpC Rd.hD hlpsR Rd.hnd Rd.hul hds' (Rd.hdsa ψ) hlenP' Rd.hmm hjD
      hfc hcrD hop
  exact ⟨ab, _, hlab, by rw [tgtFdomsAV, hFF, hrdF], hcr⟩

end Crest

/-! ## The three data rows at a class, from the major's decomposition -/

section Core

variable {envC : Env} {pp : BlockParts} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

/-- **The rows from the decomposition**: once the major is the injection
of fields that hole-fit constructor `i` of class `c` at the recursor's
index tuple, the class facts give the frame's fit, the index readings
and the fired spine. -/
theorem genRow3_core {ψ : Name → Nat} {ρ : Nat → V}
    (hS : GenClsSplit pp out mpC d Dc mc cvc ψ ρ) (hD : GenClsDec pp out mpC d Dc mc cvc ψ ρ)
    (hDI : GenClsDecInv pp out mpC d Dc mc cvc ψ ρ)
    {c i : Nat} (hc : c < (tgtRs out).length) (hi : i < blockRecNCt (tgtRs out) c)
    {xs is fs : List V} {x : V}
    (hxl : xs.length = pp.toBlockShape.rulePrefixAt c) (hil : is.length = (tgtMajor out c).nIdx)
    (hws : SpineFit ρ (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
      (xs ++ (is ++ [x])))
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs)
    (hfit : tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
      (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c is) i fs)
    (hx : x = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c i fs) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c i) (xs ++ fs) ∧
    (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c i).map
        (interp V (consList (xs ++ fs) ρ)) = is ∧
    interp V (consList (xs ++ fs) ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c i)
      = x := by
  obtain ⟨hT, -, hisT⟩ := hS c hc xs is x hxl hil hws
  obtain ⟨hfd, hTe⟩ := hDI c hc i hi xs _ fs hT hfit
  have h1 := SpineFit.append hpref hfd
  obtain ⟨-, -, hisO, hmk, -⟩ := hD c hc i hi xs fs hpref.length_eq h1
  refine ⟨h1, ?_, by rw [hmk, hx]⟩
  rw [← hTe] at hisO
  rw [← hisO, hisT]

end Core


/-! ## The two arms -/

section Arms

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

/-- **The recursor fit's values**, split at the rule prefix: the prefix
fits the rule's prefix domains, the whole spine the stored binders. -/
theorem genRow3_frame (hμ : μ.isVerified = true)
    (h : ConLeche.RecStageG μ F envC pp cvTas (tgtRs out))
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (ψ : Name → Nat) {ρ : Nat → V} {xs : List Term}
    {maj restR : Term} (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [maj]) restR) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ∧
    SpineFit ρ (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
        ++ ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) ++ [interp V ρ maj])) ∧
    ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).length
      = pp.toBlockShape.rulePrefixAt j ∧
    ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).length
      = (tgtMajor out j).nIdx := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hrPle := blockRecHrPle (p := pp) h hj
  have hmI := genRec_mI h hr
  obtain ⟨t, -, hrt, hMt⟩ := tgtRs_getElem? hr
  have hnI : r.2.2.1 = (tgtMajor out j).nIdx := by
    rw [hrt]; show t.2.1.nIdx = (ConLeche.tgtMajorsOf out j).nIdx; rw [hMt]
  obtain ⟨-, -, -, hreadT, -⟩ := recStage_tyPis hμ mpC h hr ψ
  have hws := spineFit_blockRecTy hμ mpC h hr ψ hreadT
    (by rw [List.length_append, hxl]; rfl) hfitR
  refine ⟨blockRuleHspPref_run hμ mpC h hr ψ hxl hfitR, ?_, ?_, ?_⟩
  · have e : (xs ++ [maj]).map (interp V ρ)
        = (xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)
          ++ ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) ++ [interp V ρ maj]) := by
      rw [← List.append_assoc, ← List.map_append, List.take_append_drop, List.map_append]; rfl
    rw [← e]; exact hws
  · rw [List.length_map, List.length_take]; omega
  · rw [List.length_map, List.length_drop]; omega

set_option maxHeartbeats 8000000 in
/-- **The rows at a MEMBER class** (the rule fires `.plain`): the block's
route — the constructor's own fit splits at the block's parameters
(`blockRuleCtorFit_run`), the major lies in the carrier at the
recursor's parameters and index tuple, so its fields hole-fit there
(`blockRuleStoredFit_any`: by injectivity at a `Type`-valued block, by
the subsingleton criterion under the counting guard at a `Prop`-valued
one) — `genRow3_core` does the rest. -/
theorem genRows3_mem (hμ : μ.isVerified = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (h : ConLeche.RecStageG μ F envC pp cvTas (tgtRs out))
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List Term}
    {isRec : Bool} {A : Nat → (Name → Nat) → Term} {envI' : Env}
    (hdR : d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hSt : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI'
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    (hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))))
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    (hD : ∀ ψ ρ, GenClsDec pp out mpC d Dc mc cvc ψ ρ)
    (hDI : ∀ ψ ρ, GenClsDecInv pp out mpC d Dc mc cvc ψ ρ)
    {φ : Name → Nat} {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {t : Nat} (hm : (tgtMajor out j).member = some t)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {rl : ConLeche.RecRule} (hplain : ConLeche.RecRule.fire rl = .plain) :
    BlockRuleRows3 (V := V) mpC pp (ConLeche.tgtMajorsOf out j).nPc (tgtRs out)
      (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
      (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
      (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
      (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
      (fun ψ => blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) φ j i r cA rl := by
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ _ hpinC hfitR hfitC
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hi : i < blockRecNCt (tgtRs out) j :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hcA).1 (blockRecNCt_ge hr)
  have hmS : (tgtMajor out j).member.isSome = true := by rw [hm]; rfl
  have hrt : pp.toBlockShape.recTgtAt j = t := genRun_recTgt R hj hm
  -- the class's check as a major: the member's constructors, the block's parameter count
  obtain ⟨-, cls, -, -, -, -, -, -, -, hMj, hgc⟩ := genRun_at R hj
  have hi' : cls < R.Ms.length := by rw [← hgc]; exact genRun_cls_lt R hj
  obtain ⟨key, M₀, nfs, hMs, -, ⟨CR⟩⟩ := genRun_class R hi'
  have hget : R.Ms.getD cls default = { M₀ with nfs := nfs } := by
    rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
  obtain ⟨ms, hms, -, htk⟩ := genRun_member R
    (show (R.Ms.getD cls default).member = some t by rw [← hMj]; exact hm)
  rw [hget] at hMj
  have hm0 : M₀.member = some t := by rw [hMj] at hm; exact hm
  obtain ⟨hctors, hnPc⟩ := CR.major.member_facts hm0
  have hnPc' : (ConLeche.tgtMajorsOf out j).nPc = pp.nP := by
    show (tgtMajor out j).nPc = _; rw [hMj]; exact hnPc
  rw [hnPc'] at hyl hpinC ⊢
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by rw [← tgtRs_ctors hr]; exact hcA
  -- the block datum's facts
  have hctM : d.ctorsM t = M₀.ctors := by
    subst hdR; show ctorsAs.getD t [] = M₀.ctors
    rw [List.getD_eq_getElem?_getD, hctors]; rfl
  have hcj : (d.ctorsM t)[i]? = some cA := by
    rw [hctM]; rw [hMj] at hcAM; exact hcAM
  have htd : t < d.k := by subst hdR; exact htk
  have hdnP : d.nP = pp.nP := by subst hdR; rfl
  have hwd : ∀ ψ, d.w ψ = Level.eval ψ pp.toBlockShape.resSort := by subst hdR; intro ψ; rfl
  have hdl : d.large = pp.toBlockShape.large := by subst hdR; rfl
  have hk0 : 0 < d.k := by omega
  have hmN : t < d.N := Nat.lt_of_lt_of_le htd (Nat.le_add_right _ _)
  have hjl : i < (d.ctorsM t).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hM : BlockModelAt mpC.base2 d.memberNames d := by
    subst hdR; exact blockModelAt_seam h hN hSt hcore
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2 _ htd i cA hcj
  obtain ⟨-, -, hcd, -⟩ := hcore.2.1 _ i cA hcj
  have hcf : BlockCtorFacts mpC.base2 d pp.lps t i cA := ⟨hfindC, hlpsC, hcd⟩
  have hlv := blockRuleLevelAgree hplain hψ
  have hctorRead : ∀ ψ' : Name → Nat, denote mpC.base2.acval envC ψ' 0 cA.1.type
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ') := by
    intro ψ'
    have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
      rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
    rw [blockRecCtorTy, hsel, hcd.read ψ']
    rfl
  generalize hψe : Level.substFn φ r.1.levelParams us = ψ at hℓ hfitR hlv ⊢
  have hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V ((d.dsF t i ψ).take d.nP).reverse σ := fun σ =>
    ⟨fun hσ => ((hSt.frames _ htd i cA hcj).1 _ σ).mp (hSt.paramsOf 0 hk0 _ σ hσ _ htd),
      fun hσ => hSt.paramsOf _ htd _ σ (((hSt.frames _ htd i cA hcj).1 _ σ).mpr hσ) 0 hk0⟩
  have hlenP : (d.params ψ).length = d.nP := by
    have hl := hSt.lenPps 0 ψ hk0
    show ((d.ppsM 0 ψ).take d.nP).length = d.nP
    rw [List.length_take]
    exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hl.symm))
  obtain ⟨hqs, hfq⟩ := blockRuleCtorFit_run hcj hcf hlv hlenP hparamsC (by rw [hyl, hdnP])
    (hctorRead _) hfitC
  obtain ⟨hpref, hws, hxvl, hisl⟩ := genRow3_frame hμ h hr ψ hxl hfitR
  -- the major's class facts
  obtain ⟨hTin, hmajIn, hisT⟩ := hS ψ ρ j hj _ _ _ hxvl hisl hws
  rw [tgtClsIs_mem hmS] at hTin
  obtain ⟨hpar, -⟩ := blockRecIs_fits hTin
  rw [blockRecIs_pos hpar hpref, tgtClsTup_mem hmS] at hTin
  rw [tgtClsU_mem hmS, tgtClsNIdx_mem hmS, tgtClsTup_mem hmS, hrt] at hisT
  have hTin' := hTin
  rw [hrt] at hTin'
  obtain ⟨is', hsp', hTe⟩ := mem_idxSet_elim hTin'
  have hIok := hM.idxOk ψ _ (d.satOfSpine hpar) t hmN
  rw [hTe, ← hSt.lenIds t htd ψ, isOfW_tupW hIok hsp'] at hisT
  rw [hisT] at hsp' hTe
  -- the major, in the member's former
  have hmaj : interp V ρ (Term.mkAppN
      (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys)
      ∈ˢ ((((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP)
        ++ ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))).foldl app (interp V ρ (mpC.base2.acval (d.memberName t) ψ)) := by
    rw [hM.leaf t htd ψ ρ _ ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) hpar hsp']
    rw [tgtClsCr_mem hmS, tgtClsTup_mem hmS] at hmajIn
    unfold blockRecCr at hmajIn
    rw [hrt] at hmajIn
    exact hmajIn
  -- the index pin, for the `Prop` arm
  have hpinW : d.w ψ = 0 →
      ((d.Ess t ψ).getD i []).map
        (interp V (consList ((ys.drop d.nP).map (interp V ρ))
          (consList ((ys.take d.nP).map (interp V ρ)) ρ))) = ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) := fun hw0 => by
    have hguard : interp V ρ (Term.mkAppN
        (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys) = pt := by
      rw [blockCtorMajor_value hM hcj hfindC hmN hlv hqs hfq]
      exact hM.mkZero ψ hw0 _ _ _
    have hrPle := blockRecHrPle (p := pp) h hj
    have hEssD : (d.Ess t ψ).getD i [] = d.esF t i ψ := essOfR_fixCtorDataList_getD hcj
    have hnI : (d.esF t i ψ).length
        = pp.toBlockShape.majorIdxAt j - pp.toBlockShape.rulePrefixAt j := by
      have hq := (hM.resIdxFit ψ _ (d.satOfSpine hqs) t hmN i hjl _ hfq).length_eq
      rw [List.length_map, hEssD] at hq
      rw [hq, ← hsp'.length_eq, List.length_map, List.length_drop, hxl]
    exact blockRuleIdxPin_run hcj hcf hlv (by rw [hyl, hdnP]) hxl hrPle hnI (hctorRead _) hfitC
      (by rw [hdnP]; exact hpinC hguard)
  -- the counting guard, for the `Prop` arm
  have hct1 : d.w ψ = 0 → (d.ctorsM t).length ≤ 1 := fun hw0 => by
    rw [hwd] at hw0
    obtain ⟨-, hnc⟩ := genCount R hℓ hw0
    have hc0 := congrArg (fun L => (L[t]?).map List.length) hnames
    simp only [List.getElem?_map, hms, hctors, Option.map_some, List.length_map,
      Option.some.injEq] at hc0
    have hle := numCtorsOf_ge_of_mem (List.mem_of_getElem? hms)
    rw [hctM, hc0]
    exact Nat.le_trans hle hnc
  have hlarge : d.w ψ = 0 → d.large = true := fun hw0 => by
    rw [hwd] at hw0
    rw [hdl]; exact (genCount R hℓ hw0).1
  have hsf := blockRuleStoredFit_any hM hcj hcf htd hlv hlarge hct1 hparamsC hpar hsp' hqs hfq
    hpinW hmaj
  -- the decomposition, at the class
  have hfitT : tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ
      ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) j
      (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ j ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))) i
      ((ys.drop pp.nP).map (interp V ρ)) := by
    rw [tgtClsTup_mem hmS, tgtClsFit_mem hmS,
      blockHoleFitRel_iff hM hpar (by rw [hrt]; exact hmN) hTin]
    unfold blockStoredFitRel
    rw [hrt, ← hdnP]
    exact hsf
  have hx : interp V ρ (Term.mkAppN
      (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys)
      = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ j i ((ys.drop pp.nP).map (interp V ρ)) := by
    rw [tgtClsInj_mem hmS, hrt, ← hdnP]
    exact blockCtorMajor_value hM hcj hfindC hmN hlv hqs hfq
  exact genRow3_core (hS ψ ρ) (hD ψ ρ) (hDI ψ ρ) hj hi hxvl hisl hws hpref hfitT hx

end Arms

end ConLeche.Model
