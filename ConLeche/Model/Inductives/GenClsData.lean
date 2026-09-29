module

public import ConLeche.Model.Inductives.GenClsRhs
public import ConLeche.Model.Inductives.GenRecRules
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
import ConLeche.Model.Annot.BlockLfp
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Levels
import ConLeche.Model.NatEqs
import ConLeche.Model.IndOpenRev
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.Rules.InferSoundKit
public import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Verify.Inductives.DirectGen
import ConLeche.Semantics.Tower.TowerKit

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

end OutFit

end ConLeche.Model
