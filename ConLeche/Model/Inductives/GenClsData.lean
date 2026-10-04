module

public import ConLeche.Model.Inductives.GenClsRhs
import ConLeche.Model.Inductives.GenRecRules
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
      Rules.PiChain ((tgtMajor out c).ds.length + cA.2) T0 ∧
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
  obtain ⟨cv', nPc', nF', hf', -, -, hpars, -⟩ := hcrd.2 _ Rd.hmm j hjD
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
  have hpcT : Rules.PiChain ((tgtMajor out c).ds.length + cA.2) T0 :=
    Rules.piChain_of_stripPis _ (by rw [hstrip]; rfl) hT0
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
  refine ⟨T0, pps, b0, hcons, hlpC, hT0, hT0E, hplen, hT0wd, ?_, hpcT,
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
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c) (ψ : Name → Nat)
    {cA : ConstantVal × Nat} (hcA0 : (tgtMajor out c).ctors[j]? = some cA) :
    ∃ (ab : List (Nat × Nat × AnnotTerm)) (body : AnnotTerm),
      ab.length = cA.2 ∧
      tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
        = (AnnotTerm.substTele (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
            (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) 0 ab).map (·.2.2) ∧
      denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c) (tgtCrest out c j)
        = some (mkPisAV (AnnotTerm.substTele (instTau mpC ψ (tgtClsD d Dc out c)
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
theorem genRow3_frame (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (ψ : Name → Nat) {ρ : Nat → V} {xs : List AnnotTerm}
    {maj restR : AnnotTerm} (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [maj]) restR) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ∧
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).map (·.2.2))
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
/-- **The rows at an OUTSIDE class** (the rule fires `.nested`): the
constructor's parameters are the class's at the prefix (the pins,
`genOutPinVal`), so its own fit peels at them into the rule frame's field
domains (`genOutCtorFit`, `genCls_openCrest`); the major is then the
class's injection of those fields, and the class never `Prop` here
(`genOutNZ`, `genOutW`), the carrier's decomposition at the recursor's
index tuple is that one (`mkInj`) — `genRow3_core` does the rest. -/
theorem genRows3_out (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC []) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    (hD : ∀ ψ ρ, GenClsDec pp out mpC d Dc mc cvc ψ ρ)
    (hDI : ∀ ψ ρ, GenClsDecInv pp out mpC d Dc mc cvc ψ ρ)
    {φ : Name → Nat} {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    (hcl : TgtOutCls mpC (tgtMajor out j) (Dc j) (mc j) (cvc j))
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt j)
    {lvls : List Level} {pins : List Expr}
    (hf : ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out) j r
      = .nested lvls pins)
    {rl : ConLeche.RecRule} (hrl : ConLeche.RecRule.fire rl = .nested lvls pins) :
    BlockRuleRows3 (V := V) mpC pp (ConLeche.tgtMajorsOf out j).nPc (tgtRs out)
      (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
      (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
      (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
      (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
      (fun ψ => blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) φ j i r cA rl := by
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hnest _ hfitR hfitC
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hi : i < blockRecNCt (tgtRs out) j :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hcA).1 (blockRecNCt_ge hr)
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by rw [← tgtRs_ctors hr]; exact hcA
  obtain ⟨hlvls, hpinV⟩ := genOutPinVal hμ R hg h hr hMo Rd hf φ us
  have hMM : (ConLeche.tgtMajorsOf out j).nPc = (tgtMajor out j).nPc := rfl
  rw [hMM] at hyl hnest ⊢
  -- the level assignment of the rule, and the constructor's
  have hlv : ∀ p ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj p
      = Level.substFn (Level.substFn φ r.1.levelParams us) cvI.levelParams
          (tgtMajor out j).lvls p := by
    obtain ⟨-, -, hlpsI, -⟩ := Rd.hctor i cA hcAM
    intro p hp
    rw [hψ]
    simp only [ConLeche.recFireComparands, hrl]
    rw [hlvls, ConLeche.Level.substFn_map_subst (by rw [Rd.hul, hlpsI]) hp, hlpsI]
  generalize hψe : Level.substFn φ r.1.levelParams us = ψ at hℓ hfitR hpinV hlv ⊢
  obtain ⟨hpref, hws, hxvl, hisl⟩ := genRow3_frame hμ h hr ψ hxl hfitR
  -- the class's parameters at the prefix
  have hdsa := Rd.hdsa ψ
  have hdl : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length
      = (tgtMajor out j).nPc := (DenoteMetaSpine.length_eq hdsa).symm.trans Rd.hnpc.symm
  have hrPle : pp.toBlockShape.rulePrefixAt j ≤ pp.toBlockShape.majorIdxAt j :=
    blockRecHrPle (p := pp) h hj
  have hpsv : (ys.take (tgtMajor out j).nPc).map (interp V ρ)
      = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
          (interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ)) := by
    have hlen0 : ((ys.take (tgtMajor out j).nPc).map (interp V ρ)).length
        = ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
          (interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))
            ρ))).length := by
      rw [List.length_map, List.length_map, List.length_take, hyl, hdl]
      show min _ ((tgtMajor out j).nPc + cA.2) = _
      omega
    refine List.ext_getElem hlen0 fun q h1 h2 => ?_
    have hq : q < (tgtMajor out j).nPc := by rw [List.length_map, hdl] at h2; exact h2
    obtain ⟨vpa, hvpa, hval⟩ := hpinV q hq
    have hn := hnest lvls pins hrl q hq vpa hvpa
    rw [List.getElem_map, List.getElem_map, List.getElem_take]
    have hyq : ys[q]'(by omega) = ys.getD q default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hdq : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)[q]'(by omega)
        = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).getD q default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [hyq, hn, hval ρ _ (by rw [List.length_take]; omega), hdq]
  have hysv : ys.map (interp V ρ)
      = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
          (interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ))
        ++ (ys.drop (tgtMajor out j).nPc).map (interp V ρ) := by
    rw [← hpsv, ← List.map_append, List.take_append_drop]
  generalize hxV : (xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) = xsV
    at hpref hws hxvl hpsv hysv ⊢
  generalize hiV : (xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) = isV
    at hws hisl ⊢
  generalize hfV : (ys.drop (tgtMajor out j).nPc).map (interp V ρ) = fsY at hysv ⊢
  -- the instantiated constructor, fitted
  obtain ⟨T0, pps, b0, hcons, hlpsI, hT0, hT0E, hplen, -, hT0cl, hpc, hTFall⟩ :=
    genOutCtorFit hμ R hg hcov hj hi Rd hMo hnP ψ ρ hpref hcAM
  obtain ⟨ab, body, hlab, hfdE, hcrR⟩ := genCls_openCrest hμ R hg hj hi Rd hnP ψ hcAM
  have hTF := hTFall _ hcrR
  have hwfC := mpC.base2.wf _ hcons
  have hctorTy : blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i
      (Level.substFn φ cA.1.levelParams usj) = T0 := by
    have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
      rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
    rw [blockRecCtorTy, hsel, denoteMeta_params_ext mpC.base2 hlv 0 cA.1.type hwfC.2.1, hT0]
    rfl
  replace hfitC : TeleFitPA V ρ T0 ys restC := by rw [← hctorTy]; exact hfitC
  -- the FIELDS fit the rule frame's field domains
  have hfld : SpineFit (consList xsV ρ) (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ j i)
      fsY := by
    have hpc' : Rules.PiChain ys.length T0 := by
      rw [hyl, Rd.hnpc]
      exact hpc
    have h1 := Rules.teleFit_of_teleFitPA hpc' hfitC
    obtain ⟨X', h2⟩ := teleFit_congr_frame' _ (n := 0) (ρ' := consList xsV ρ) hT0cl
      (fun k hk => absurd hk (Nat.not_lt_zero _)) h1
    rw [hysv] at h2
    have hfl : fsY.length = cA.2 := by
      rw [← hfV, List.length_map, List.length_drop, hyl]; show _ + cA.2 - _ = _; omega
    have h3 := teleFit_peel' _ hTF.peelPis
      (by rw [hfl, hdl, Rd.hnpc]; exact hpc) h2
    rw [hfdE]
    refine spineFit_of_teleFit ?_ h3
    rw [substTele_length, hlab, hfl]
  have hsp1 := SpineFit.append hpref hfld
  -- the decoding at the rule frame
  obtain ⟨hfitT', hT'in, -, -, -⟩ := hD ψ ρ j hj i hi xsV fsY hpref.length_eq hsp1
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok _ Rd.hD
  obtain ⟨hiD, hfc0, -, -⟩ := Rd.hctor i cA hcAM
  have hname : cA.1.name = (tgtClsD d Dc out j).ctorName (tgtClsM mc pp.toBlockShape out j) i :=
    ConLeche.Semantics.Env.find?_name hfc0
  have hfindC : envC.find? cA.1.name = some (.ctorInfo cA.1 (tgtMajor out j).ds.length cA.2) := by
    rw [hname]; exact hfc0
  have hmN : tgtClsM mc pp.toBlockShape out j < (tgtClsD d Dc out j).N :=
    Nat.lt_of_lt_of_le Rd.hmm hC.kN
  have hG := (Rd.hG ψ ρ xsV).mpr hpref
  have hFr := Rd.hfr ψ ρ xsV hxvl
  have hIs : tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xsV j
      = (tgtClsD d Dc out j).idx (tgtClsψ cvc out ψ j)
          (tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xsV j)
          (tgtClsM mc pp.toBlockShape out j) := by
    unfold tgtClsIs; rw [if_pos hG]
  have hsatK := Rd.hsat ψ ρ xsV hpref
  have hlv' : ∀ p ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj p
      = tgtClsψ cvc out ψ j p := by
    intro p hp; rw [hlv p hp, Rd.hψ]
  have hval3 : interp V ρ (AnnotTerm.mkAppN
      (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys)
      = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ j i fsY := by
    rw [mpC.base2.acval_params cA.1.name _ hfindC _ _ hlv', interp_mkAppN_foldl, hysv, hname,
      acval_interp_closed mpC.base2 _ _ ρ
        (fun k => consList xsV ρ (k + tgtRP pp.toBlockShape j))]
    have hT'' := hT'in
    rw [hIs, hFr] at hT''
    have hfit'' := hfitT'
    unfold tgtClsFit at hfit''
    rw [hFr] at hfit''
    refine hC.ctor _ hmN i _ _ _ _ _ ?_ hT'' hfit''
    refine spineFit_of_sat_consList ?_ hsatK
    rw [List.length_map, Rd.hlenP ψ, hdl, Rd.hnpc]
  -- the class is never `Prop` here
  have hw : (tgtClsD d Dc out j).w (tgtClsψ cvc out ψ j) ≠ 0 := by
    have e1 : tgtClsD d Dc out j = Dc j := by simp [tgtClsD, hMo]
    have e2 : tgtClsψ cvc out ψ j
        = Level.substFn ψ (cvc j).levelParams (tgtMajor out j).lvls := by simp [tgtClsψ, hMo]
    rw [e1, e2, genOutW R hj hMo hcl ψ]
    exact ConLeche.Level.isNeverZero_sound _ _ (genOutNZ R hj hMo hℓ)
  -- the carrier's decomposition at the recursor's index tuple
  obtain ⟨hTin, hmajIn, -⟩ := hS ψ ρ j hj xsV isV _ hxvl hisl hws
  rw [hIs] at hTin
  have hsatF : Sat V ((tgtClsD d Dc out j).params (tgtClsψ cvc out ψ j)).reverse
      (tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xsV j) := by
    rw [hFr]; exact hsatK
  obtain ⟨j', fs', hfit', heq⟩ := hC.carrier_case hsatF hmN hTin hmajIn
  rw [hval3] at heq
  obtain ⟨hjj, rfl⟩ := hC.mkInj _ hw _ hmN i fsY j' fs' hiD hfit'.1
    hfitT'.2.1.length_eq hfit'.2.1.length_eq heq
  subst hjj
  exact genRow3_core (hS ψ ρ) (hD ψ ρ) (hDI ψ ρ) hj hi hxvl hisl hws hpref hfit' hval3


set_option maxHeartbeats 8000000 in
/-- **The rows at a MEMBER class** (the rule fires `.plain`): the block's
route — the constructor's own fit splits at the block's parameters
(`blockRuleCtorFit_run`), the major lies in the carrier at the
recursor's parameters and index tuple, so its fields hole-fit there
(`blockRuleStoredFit_any`: by injectivity at a `Type`-valued block, by
the subsingleton criterion under the counting guard at a `Prop`-valued
one) — `genRow3_core` does the rest. -/
theorem genRows3_mem (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI' : Env}
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
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ htd i cA hcj
  obtain ⟨-, -, hcd, -⟩ := hcore.2.2.1 _ i cA hcj
  have hcf : BlockCtorFacts mpC.base2 d pp.lps t i cA := ⟨hfindC, hlpsC, hcd⟩
  have hlv := blockRuleLevelAgree hplain hψ
  have hctorRead : ∀ ψ' : Name → Nat, denoteMeta mpC.base2.acval envC ψ' 0 cA.1.type
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ') := by
    intro ψ'
    have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
      rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
    rw [blockRecCtorTy, hsel, hcd.read ψ']
    rfl
  generalize hψe : Level.substFn φ r.1.levelParams us = ψ at hℓ hfitR hlv ⊢
  have hparamsC : ∀ σ : Nat → V, Sat V (d.params ψ).reverse σ
      ↔ Sat V (((d.dsF t i ψ).take d.nP).map (·.2.2)).reverse σ := fun σ =>
    ⟨fun hσ => ((hSt.frames _ htd i cA hcj).1 _ σ).mp (hSt.paramsOf 0 hk0 _ σ hσ _ htd),
      fun hσ => hSt.paramsOf _ htd _ σ (((hSt.frames _ htd i cA hcj).1 _ σ).mpr hσ) 0 hk0⟩
  have hlenP : (d.params ψ).length = d.nP := by
    have hl := hSt.lenPps 0 ψ hk0
    show (((d.ppsM 0 ψ).take d.nP).map (·.2.2)).length = d.nP
    rw [List.length_map, List.length_take]
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
  have hmaj : interp V ρ (AnnotTerm.mkAppN
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
          (consList ((ys.take d.nP).map (interp V ρ)) ρ))) = ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) := fun _ => by
    have hrPle := blockRecHrPle (p := pp) h hj
    have hEssD : (d.Ess t ψ).getD i [] = d.esF t i ψ := essOfR_fixCtorDataList_getD hcj
    have hnI : (d.esF t i ψ).length
        = pp.toBlockShape.majorIdxAt j - pp.toBlockShape.rulePrefixAt j := by
      have hq := (hM.resIdxFit ψ _ (d.satOfSpine hqs) t hmN i hjl _ hfq).length_eq
      rw [List.length_map, hEssD] at hq
      rw [hq, ← hsp'.length_eq, List.length_map, List.length_drop, hxl]
    exact blockRuleIdxPin_run hcj hcf hlv (by rw [hyl, hdnP]) hxl hrPle hnI (hctorRead _) hfitC
      (by rw [hdnP]; exact hpinC)
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
  have hx : interp V ρ (AnnotTerm.mkAppN
      (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys)
      = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ j i ((ys.drop pp.nP).map (interp V ρ)) := by
    rw [tgtClsInj_mem hmS, hrt, ← hdnP]
    exact blockCtorMajor_value hM hcj hfindC hmN hlv hqs hfq
  exact genRow3_core (hS ψ ρ) (hD ψ ρ) (hDI ψ ρ) hj hi hxvl hisl hws hpref hfitT hx

end Arms

end ConLeche.Model
