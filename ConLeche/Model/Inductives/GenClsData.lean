module

public import ConLeche.Model.Inductives.GenClsRhs
public import ConLeche.Model.Inductives.GenRecRules
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.GenClsMinor
import ConLeche.Model.Inductives.GenClsFrame
import ConLeche.Model.Inductives.GenClsCall
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.GenRecPins
import ConLeche.Model.Inductives.GenRecParams
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
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetGraph
import ConLeche.Model.Inductives.NestedRecPins
import ConLeche.Model.Annot.BlockLfp
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitRename
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
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState BinderMeta
  closeTelescope)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Value-level fits along a peel -/

section Fits

open ConLeche.Model.Rules (PiChain piChain_succ_inv PiChain.inst)

/-- **The fit re-instantiates, under the ∀-chain guard** (the converse
of `teleFit_of_inst`). -/
theorem teleFit_inst_of' {aa : AnnotTerm} :
    ∀ {L : List V} {E : AnnotTerm} {k : Nat} {ρ : Nat → V} {rest : V},
      PiChain L.length E →
      TeleFit V (instE k (interp V (shiftE k 0 ρ) aa) ρ) E L rest →
      TeleFit V ρ (E.inst aa k) L rest := by
  intro L
  induction L with
  | nil =>
    intro E k ρ rest _ h
    rw [teleFit_nil_inv h, ← interp_inst]
    exact .nil
  | cons y ys ih =>
    intro E k ρ rest hpc h
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc
    rw [AnnotTerm.inst_pi]
    cases h with
    | cons hmem hfit =>
      refine .cons (by rw [interp_inst]; exact hmem) ?_
      rw [cons_instE, ← shiftE_succ_cons y k ρ] at hfit
      exact ih (E := B) (k := k + 1) (ρ := cons y ρ) hB hfit

/-- `teleFit_inst_of'` at the head binder. -/
theorem teleFit_inst0_of' {aa : AnnotTerm} {L : List V} {E : AnnotTerm}
    {ρ : Nat → V} {rest : V} (hpc : PiChain L.length E)
    (h : TeleFit V (cons (interp V ρ aa) ρ) E L rest) :
    TeleFit V ρ (E.inst aa) L rest := by
  refine teleFit_inst_of' (k := 0) hpc ?_
  rwa [shiftE_zero_zero, instE_zero]

/-- **A fit continues past a peel**: fitting a ∀-chain at a spine's
values followed by more values, the peel's residual fits the rest. -/
theorem teleFit_peel' :
    ∀ (ws : List AnnotTerm) {T C : AnnotTerm} {σ : Nat → V} {fs : List V} {X : V},
      ConLeche.Model.AnnotTerm.peelPis T ws = some C →
      PiChain (ws.length + fs.length) T →
      TeleFit V σ T (ws.map (interp V σ) ++ fs) X → TeleFit V σ C fs X
  | [], T, C, σ, fs, X, hp, _, h => by
    obtain rfl : T = C := Option.some.inj hp
    simpa using h
  | w :: ws, T, C, σ, fs, X, hp, hpc, h => by
    have hpc' : PiChain ((ws.length + fs.length) + 1) T := by
      simpa [Nat.add_right_comm] using hpc
    obtain ⟨u, v, A, B, rfl, hB⟩ := piChain_succ_inv hpc'
    simp only [ConLeche.Model.AnnotTerm.peelPis] at hp
    rw [List.map_cons, List.cons_append] at h
    cases h with
    | cons _ hfit =>
      exact teleFit_peel' ws hp (PiChain.inst w 0 hB)
        (teleFit_inst0_of' (by simpa using hB) hfit)

/-- **A fit moves between frames agreeing below the term's bound.** -/
theorem teleFit_congr_frame' :
    ∀ (vals : List V) {T : AnnotTerm} {n : Nat} {ρ ρ' : Nat → V} {X : V},
      Term.bvarsBelow n T.erase → (∀ k, k < n → ρ k = ρ' k) →
      TeleFit V ρ T vals X → ∃ X', TeleFit V ρ' T vals X'
  | [], T, _, _, ρ', _, _, _, _ => ⟨_, .nil⟩
  | a :: as, _, n, ρ, ρ', X, hb, hag, h => by
    cases h with
    | cons hmem hfit =>
      simp only [AnnotTerm.erase_pi] at hb
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
theorem genOutCtorFit (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC [])
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hMo : (tgtMajor out c).member = none) (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c)
    (ψ : Name → Nat) (ρ : Nat → V) {xs : List V}
    (hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs)
    {cA : ConstantVal × Nat} (hcA : (tgtMajor out c).ctors[j]? = some cA) :
    ∃ (T0 : AnnotTerm) (pps : List (Nat × Nat × AnnotTerm)) (b0 : AnnotTerm),
      ConstantInfo.ctorInfo cA.1 (tgtMajor out c).ds.length cA.2 ∈ envC.consts ∧
      cA.1.levelParams = cvI.levelParams ∧
      denoteMeta mpC.base2.acval envC (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls) 0
        cA.1.type = some T0 ∧
      T0 = mkPisAV pps b0 ∧ pps.length = (tgtMajor out c).ds.length ∧
      (∀ σ : Nat → V, WellDenotedV V σ T0) ∧ Term.bvarsBelow 0 T0.erase ∧
      ∀ C : AnnotTerm,
        denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c) (tgtCrest out c j) = some C →
        TeleFitPA V (consList xs ρ) T0 (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
          C := by
  have hacl := mpC.base2.acval_closed
  have hDe : tgtClsD d Dc out c = Dc c := by simp [tgtClsD, hMo]
  have hMe : tgtClsM mc pp.toBlockShape out c = mc c := by simp [tgtClsM, hMo]
  have hsatK := Rd.hsat ψ ρ xs hpref
  rw [Rd.hψ] at hsatK
  obtain ⟨hjD, hfc0, hlpC, -⟩ := Rd.hctor j cA hcA
  obtain ⟨-, -, -, hcrd⟩ := mpC.lfp_ok _ Rd.hD
  obtain ⟨cv', nPc', nF', hf', -, -, -, hpars, -⟩ := hcrd.2 _ Rd.hmm j hjD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out c).ds.length = nPc' ∧ cA.2 = nF' := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hcons := List.mem_of_find?_eq_some hfc0
  have hwfC := mpC.base2.wf _ hcons
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  -- the stored type's reading at the class's levels, graded
  obtain ⟨T0, hT0⟩ := mpC.type_reads _ hcons
    (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
  change denoteMeta mpC.base2.acval envC (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
    0 cA.1.type = some T0 at hT0
  have hT0wd := mpC.type_wellDenotedV _ hcons _ T0 hT0
  have hT0cl : Term.bvarsBelow 0 T0.erase :=
    bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hCf) hCb hT0
  -- its outer parameter binders
  obtain ⟨cv8, nPc8, nF8, hf8, bs, args, hstrip, -⟩ :=
    (hcov.own _ Rd.hD).ctorConcl _ Rd.hmm j hjD
  rw [hfc0] at hf8
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv8 ∧ (tgtMajor out c).ds.length = nPc8 ∧ cA.2 = nF8 := by
    injection hf8 with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  obtain ⟨fvsA, oA, hopA⟩ := openPisAtFvars_of_stripPis_isSome
    ((tgtMajor out c).ds.length + cA.2) (e := cA.1.type) 0 (by rw [hstrip]; rfl)
  obtain ⟨oP, hopP⟩ := ConLeche.openPisAtFvars_prefix (tgtMajor out c).ds.length
    ((tgtMajor out c).ds.length + cA.2) _ 0 (Nat.le_add_right _ _) hopA
  obtain ⟨pps, b0, hst, -, hplen, -⟩ := denoteMeta_openPis (tgtMajor out c).ds.length hopP hT0
  obtain ⟨hT0E, -⟩ := stripPisAV_eq_mkPis hst
  -- the parameters' readings fit the constructor's parameter binders
  have hsatC := hpars _ pps b0 (by rw [← hT0E]; exact hT0) (Nat.le_of_eq hplen.symm) _ hsatK
  rw [List.take_of_length_le (Nat.le_of_eq hplen)] at hsatC
  have hdsa := Rd.hdsa ψ
  have hdl : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).length
      = (tgtMajor out c).ds.length := (DenoteMetaSpine.length_eq hdsa).symm
  have hspK := spineFit_of_sat_consList (Ds := pps.map fun p : Nat × Nat × AnnotTerm => p.2.2)
    (as := (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).map (interp V (consList xs ρ)))
    (by rw [List.length_map, List.length_map, hdl, hplen])
    (by simpa only [keyFrame] using hsatC)
  rw [hT0E] at hT0cl
  have hbnd : ∀ l, l < (pps.map fun p : Nat × Nat × AnnotTerm => p.2.2).length →
      Term.bvarsBelow l (((pps.map fun p : Nat × Nat × AnnotTerm => p.2.2).getD l
        default).erase) := by
    intro l hl
    rw [List.length_map] at hl
    have := (bvarsBelow_mkPisAV_inv hT0cl).1.getD_below l hl
    rw [Nat.zero_add] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at this
    exact this
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
  have hTy : denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c)
      (cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out c).lvls) = some T0 := by
    rw [denoteMeta_instLevels (acvalParamsAt_of_core mpC.base2) ψ, hlpC]
    exact denoteMeta_depth_of_closed hacl hCf
      (fun k => denoteMeta_closed mpC.base2.acval_erase mpC.base2.cval_closed hCf hCb hT0 1 k)
      hT0 _
  have hds' : ∀ x ∈ (tgtMajor out c).ds, Expr.WScoped (tgtRP pp.toBlockShape c) x ∧
      x.looseBVarsBounded 0 = true := by
    intro x hx
    exact ⟨(Rd.hds x hx).1.mono (by rw [tgtRP]; exact hnP), (Rd.hds x hx).2⟩
  obtain ⟨restA, hrest, hpeel⟩ := Rules.denoteMeta_instPisAt_peel hacl (acval_inst_self mpC.base2)
    _ hinst (Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hCf))
    hds' hTy hdsa
  have hpe := hTF.peelPis
  rw [← hT0E, hpeel] at hpe
  obtain rfl := Option.some.inj hpe
  refine ⟨T0, pps, b0, hcons, hlpC, hT0, hT0E, hplen, hT0wd, ?_,
    fun C hC => ?_⟩
  · rw [hT0E]; exact hT0cl
  · rw [hrest] at hC
    obtain rfl := Option.some.inj hC
    rw [hT0E]; exact hTF

set_option maxHeartbeats 8000000 in
/-- **A `.nested` firing's pins, valued** (at an outside class): the
levels are the class's, and the `q`-th pin, instantiated at the rule's
level arguments and opened at the prefix, reads, and its chain at any
prefix spine is the `q`-th parameter's reading at that spine's frame —
the pin is the stored major domain's `q`-th argument closed over the
prefix (`nestedRuleSyn_open`), erasure-equal to the class's parameter. -/
theorem genOutPinVal (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[c]? = some r) (hMo : (tgtMajor out c).member = none)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    {lvls : List Level} {pins : List Expr}
    (hf : ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out) c r
      = .nested lvls pins)
    (φ : Name → Nat) (us : List Level) :
    lvls = (tgtMajor out c).lvls ∧
    ∀ q, q < (tgtMajor out c).nPc → ∃ vpa : AnnotTerm,
      denoteMeta mpC.base2.acval envC φ (pp.toBlockShape.rulePrefixAt c)
          (openRev 0 (pp.toBlockShape.rulePrefixAt c)
            ((pins.getD q default).instantiateLevelParams r.1.levelParams us)) = some vpa ∧
      ∀ (ρ : Nat → V) (zs : List AnnotTerm), zs.length = pp.toBlockShape.rulePrefixAt c →
        interp V ρ (AnnotTerm.instRevChain zs vpa)
          = interp V (consList (zs.map (interp V ρ)) ρ)
              ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out
                (Level.substFn φ r.1.levelParams us) c).getD q default) := by
  have hc : c < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, -, hpinsWf, -⟩ := ConLeche.tgtFireOf_nested hf
  have hm' : (ConLeche.tgtMajorsOf out c).member = none := hMo
  unfold ConLeche.tgtFireOf at hf
  rw [hm'] at hf
  simp only [ConLeche.auxRuleFireR] at hf
  cases hsyn : Expr.nestedRuleSyn (·.constsResolve envC) r.1.levelParams r.1.type
      (pp.toBlockShape.majorIdxAt c) (pp.toBlockShape.rulePrefixAt c)
      (ConLeche.tgtMajorsOf out c).nPc with
  | none => rw [hsyn] at hf; exact nomatch hf
  | some lp =>
  obtain ⟨lvls', pins'⟩ := lp
  rw [hsyn] at hf
  injection hf with hl hp
  rw [hl, hp] at hsyn
  -- the stored type's openers
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  have hopen := TE.hopen
  have hmaj := TE.hmaj
  obtain ⟨rP, hRP⟩ : ∃ n, pp.toBlockShape.rulePrefixAt c = n := ⟨_, rfl⟩
  obtain ⟨mI, hMI⟩ : ∃ n, pp.toBlockShape.majorIdxAt c = n := ⟨_, rfl⟩
  have hle0 : rP ≤ mI := by have := TE.hmI'; omega
  rw [hRP, hMI] at hsyn
  rw [hRP]
  rw [hMI] at hopen hmaj
  obtain ⟨⟨D₀, hD₀⟩, hpinsE⟩ := ConLeche.nestedRuleSyn_open hsyn hopen hmaj
  -- the stored major's domain is the class applied, up to erasure
  obtain ⟨clsc, tyc, ifsc, bodyc, -, -, -, -, hifl, hRPc, hmIc, -, -, -, fvs0, o0, hop0, hE⟩ :=
    genRun_binders hμ R hg h mpC (fun _ => 0) hc
  have hrE : (tgtRs out)[c]'hc = r := Option.some.inj ((List.getElem?_eq_getElem hc).symm.trans hr)
  rw [hrE, hMI] at hop0
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj (hop0.symm.trans hopen))
  have hmE := hE mI TE.maj (Expr.mkAppN (.const (tgtMajor out c).ind (tgtMajor out c).lvls)
      ((tgtMajor out c).ds ++ ifsc)) hmaj (by
    rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_append, List.length_map]
    rw [show mI - (R.g.pre.length + ifsc.length) = 0 by omega]
    rfl)
  obtain ⟨f', as', hmajE, hf'E, hasl⟩ := erasedEq_mkAppN_inv _ hmE
  obtain ⟨-, hargE⟩ := ConLeche.erasedEq_mkAppN_args _ hasl (by rw [← hmajE]; exact hmE)
  obtain rfl : f' = .const (tgtMajor out c).ind (tgtMajor out c).lvls := by
    match f', hf'E with
    | .const n' us', hf => obtain ⟨rfl, rfl⟩ := hf; rfl
  have hfn : TE.maj.fvarTypeD.getAppFn = .const (tgtMajor out c).ind (tgtMajor out c).lvls := by
    rw [hmajE, Expr.getAppFn_mkAppN]; rfl
  have hargsE : TE.maj.fvarTypeD.getAppArgs = as' := by
    rw [hmajE, Expr.getAppArgs_mkAppN]; rfl
  refine ⟨?_, fun q hq => ?_⟩
  · rw [hfn] at hD₀
    injection hD₀ with _ h2
    exact h2.symm
  -- the `q`-th pin is the `q`-th parameter, closed
  have hnpc := Rd.hnpc
  have hasl' : as'.length = (tgtMajor out c).ds.length + ifsc.length := by
    rw [hasl, List.length_append]
  have hqd : q < as'.length := by omega
  obtain ⟨x, hxdef⟩ : ∃ x, x = as'[q] := ⟨_, rfl⟩
  have hxA : x ∈ TE.maj.fvarTypeD.getAppArgs := by
    rw [hargsE, hxdef]; exact List.getElem_mem hqd
  have hpinq : (pins.getD q default) = x.abstractRange 0 rP := by
    rw [← hpinsE, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      if_pos (show q < (ConLeche.tgtMajorsOf out c).nPc from hq), hargsE,
      List.getElem?_eq_getElem hqd, hxdef]
    rfl
  have hpinMem : pins.getD q default ∈ pins := by
    rw [← hpinsE]
    rw [← hpinsE] at hpinq
    rw [List.getD_eq_getElem?_getD] at hpinq ⊢
    have hq' : q < ((TE.maj.fvarTypeD.getAppArgs.take (ConLeche.tgtMajorsOf out c).nPc).map
        (·.abstractRange 0 rP)).length := by
      simp only [List.length_map, List.length_take, hargsE]
      have : q < (ConLeche.tgtMajorsOf out c).nPc := hq
      omega
    rw [List.getElem?_eq_getElem hq', Option.getD_some]
    exact List.getElem_mem hq'
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
  have hwsM : Expr.WScoped mI TE.maj.fvarTypeD := by
    have := openPisAtFvars_typeWScoped (mI + 1) hopen hw0 mI TE.maj hmaj
    rwa [Nat.zero_add] at this
  have hwsX : Expr.WScoped rP x := ConLeche.WScoped.of_abstractRange_noFvar
    (wscoped_of_getAppArgs hwsM x hxA) (by rw [← hpinq]; exact hpF)
  have hxb : x.looseBVarsBounded 0 = true :=
    ConLeche.looseBVarsBounded_getAppArgs
      ((openPisAtFvars_bounded _ hopen hb0).2 TE.maj (List.mem_of_getElem? hmaj)) x hxA
  have hnil : r.1.type.fvarLeaves = [] := fvarLeaves_nil_of_wscoped_zero hw0
  have hxlt : ∀ l ∈ x.fvarLeaves, l.1 < rP :=
    fun l hl => ConLeche.Expr.fvarLeaves_lt_of_wscoped hwsX l hl
  have hxl : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ TE.fvs.take rP := by
    intro l hl
    obtain ⟨tyM, hmajE'⟩ := ConLeche.openPisAtFvars_index _ _ _ hopen mI TE.maj hmaj
    have hlM : l ∈ TE.maj.fvarLeaves := by
      have h1 := ConLeche.fvarLeaves_getAppArgs hxA l hl
      rw [hmajE'] at h1 ⊢
      simp only [Expr.fvarTypeD] at h1
      simp only [Expr.fvarLeaves, List.mem_cons]
      exact Or.inr h1
    rcases openPisAtFvars_leaves _ hopen l (Or.inr ⟨TE.maj, List.mem_of_getElem? hmaj, hlM⟩)
      with h' | h'
    · rw [hnil] at h'; exact nomatch h'
    · obtain ⟨pos, hpos⟩ := List.getElem?_of_mem h'
      obtain ⟨ty', hty'⟩ := ConLeche.openPisAtFvars_index _ _ _ hopen pos _ hpos
      have h1 : l.1 = pos := by injection hty' with a b; omega
      have hpt : (TE.fvs.take rP)[pos]? = some (Expr.fvar l.1 l.2) := by
        rw [List.getElem?_take, if_pos (show pos < rP by have := hxlt l hl; omega)]
        exact hpos
      exact List.mem_of_getElem? hpt
  have hround : Expr.instSpine (TE.fvs.take rP) (rP - 1) (pins.getD q default) = x := by
    rw [hpinq, Expr.instSpine_eq_instSeq]
    have := ConLeche.instSeq_abstractRange_open hpre x 0 hxb hxl
    rw [hoslen, Nat.zero_add] at this
    exact this
  -- the parameter's reading is the class's parameter's
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = Level.substFn φ r.1.levelParams us := ⟨_, rfl⟩
  have hqds : q < (tgtMajor out c).ds.length := by omega
  have hxE : Expr.ErasedEq x ((tgtMajor out c).ds.getD q default) := by
    have := hargE q ((tgtMajor out c).ds.getD q default) x (by
      rw [List.getElem?_append_left hqds, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hqds]; rfl)
      (by rw [hxdef]; exact List.getElem?_eq_getElem hqd)
    exact this
  have hdq := DenoteMetaSpine.getD (Rd.hdsa ψ) default q hqds
  have hTRP : tgtRP pp.toBlockShape c = rP := by rw [tgtRP]; exact hRP
  rw [hTRP] at hdq
  have hw : denoteMeta mpC.base2.acval envC ψ rP x
      = some ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).getD q default) := by
    rw [denoteMeta_erasedEq hxE]; exact hdq
  have hacl := mpC.base2.acval_closed
  have hainst : ∀ (n : Name) (ψ' : Name → Nat) (y : AnnotTerm) (k : Nat),
      (mpC.base2.acval n ψ').inst y k = mpC.base2.acval n ψ' :=
    fun n ψ' y k => AVExprSubst.inst_eq_self_of_closed (mpC.base2.acval_closed n ψ') y k
  have hw' : denoteMeta mpC.base2.acval envC ψ (rP + 0)
      (Expr.instSpine (TE.fvs.take rP) (rP - 1) (pins.getD q default))
        = some ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).getD q default) := by
    rw [hround, Nat.add_zero]; exact hw
  obtain ⟨vpa, hvpden⟩ := pinOpenRevReads (acval := mpC.base2.acval) (cval := mpC.base2.cvalE)
    (env := envC) (φ := ψ) hacl hainst mpC.base2.acval_erase mpC.base2.cval_closed hoslen hshape
    hwsOs hbOs hpF hpB hw'
  refine ⟨vpa, ?_, fun ρ zs hzs => ?_⟩
  · rw [ConLeche.openRev_instantiateLevelParams,
      denoteMeta_instLevels (acvalParamsAt_of_core mpC.base2) φ, ← hψ]
    exact hvpden
  · obtain ⟨w0, hw0', hcross⟩ := pinCross (acval := mpC.base2.acval) (cval := mpC.base2.cvalE)
      (env := envC) (φ := ψ) (cnF := 0) hacl hainst mpC.base2.acval_erase mpC.base2.cval_closed
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
  obtain ⟨ab, hta, -, -⟩ := hab (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
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
theorem genCls_openCrest (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g)
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) :
    ∃ (ab : List (Nat × Nat × AnnotTerm)) (body : AnnotTerm),
      tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
        = (AnnotTerm.substTele (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
            (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) 0 ab).map (·.2.2) ∧
      denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c) (tgtCrest out c j)
        = some (mkPisAV (AnnotTerm.substTele (instTau mpC ψ (tgtClsD d Dc out c)
            (tgtMajor out c).lvls (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) 0 ab) body) := by
  obtain ⟨cls, cA, fvs, cb, hgc, hM, hcA, hctO, ⟨CR⟩, hnF, hcrest, htRP, hop, hFF, hCB, -, -⟩ :=
    genRun_frame hμ R hg hc hj
  obtain ⟨hjD, hfc, hlpC, hlpsR⟩ := Rd.hctor j cA hcA
  have hcrD := CR.hD
  rw [← hM, Rd.hctorAt cA.1 hlpC] at hcrD
  rw [← hcrest] at hcrD hop
  have hRP : tgtRP pp.toBlockShape c = R.pre.length := htRP
  have hds' : ∀ x ∈ (tgtMajor out c).ds, Expr.WScoped (tgtRP pp.toBlockShape c) x ∧
      x.looseBVarsBounded 0 = true :=
    fun x hx => ⟨(Rd.hds x hx).1.mono hnP, (Rd.hds x hx).2⟩
  have hlenP' := Rd.hlenP ψ
  rw [Rd.hψ] at hlenP'
  rw [← hRP] at hop
  obtain ⟨-, ab, -, -, hrdF, -, -, hcr⟩ :=
    instCtor_open mpC Rd.hD Rd.hnN Rd.hkN hlpsR Rd.hnd Rd.hul hds' (Rd.hdsa ψ) hlenP' Rd.hmm hjD
      hfc hcrD hop
  exact ⟨ab, _, by rw [tgtFdomsAV, hFF, hrdF], hcr⟩

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
    (hws : SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
      (·.2.2)) (xs ++ (is ++ [x])))
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

end ConLeche.Model
