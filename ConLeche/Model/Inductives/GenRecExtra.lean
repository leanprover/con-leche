module

public import ConLeche.Model.Inductives.GenClsData
import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Model.Inductives.GenRecRules
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.GenRecClasses
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.BlockData
import ConLeche.Model.Inductives.BlockCaps
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Env.BlockLfp
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Rules.DefEqSoundKit
import ConLeche.Verify.InstSpine
import ConLeche.Verify.PropWhen
import ConLeche.Verify.Subst
import ConLeche.Verify.InferLemmas
import ConLeche.Model.IndFrame
import ConLeche.Model.IndPointKit
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.Denote.TeleOpen
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.ContInst
import ConLeche.Model.Env.CanonCrest
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.TargetClass

public section

/-!
# The ι case split's facts at the generated recursors (task #342 L10)

`RecRuleLaw` carries, besides the fired law, the facts the ι step's
case split consumes (`RecRuleExtra`): the K law at any major, the
constructor's arity, (S) a family never `Prop` at the constructor's
levels holds no point, (P) where the major's domain holds the point
every fitting constructor application is the point, (U) at a fired
spine the conditional comparisons are equations.  `blockRecRuleLaw_gen`
derives the K law from the fired law at a witness spine
(`RecRuleKWit`); this file discharges the witness and the rest
(`RecRuleExtraNK`) at every rule of the generated stage.

The facts are all about the CLASS the major lies in — the recursor's
fit puts the major in the class's carrier at the recursor's parameters
and index tuple (`GenClsSplit`):

* at `w ≠ 0` the carrier holds only injections, none the point
  (`LfpClause.injNePt`); at `w = 0` the constructor's type is a truth
  value (its innermost fibre is the member's, a truth value), so the
  constructor and every application of it is the point;
* the member's capability record (`blockCapsAt`) carries the family's
  sort zero-ness, which decides `w` at the constructor's levels, and
  the K bit, which makes the member's only constructor fieldless — so
  the carrier's decomposition (`blockCarrier_case`) is that constructor
  at the recursor's parameters, whose stored fit's index clause is the
  recursor's index tuple;
* the coherence of the conditional comparisons is L7's: the parameters
  are fits of one telescope of types, the indices fits of the
  component's index telescope at them.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## 0. Generic facts -/

section Generic

/-- **A recorded block's sort is read off its member's type**, so two
level assignments agreeing on the member's level parameters give the
same sort. -/
theorem lfpW_congr {envC : Env} (mpC : EnvModelM V envC) {D : LfpDatum V}
    (hD : D ∈ mpC.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : ConLeche.IndCaps} (hf : envC.find? (D.member mm) = some (.indInfo cv caps))
    {ψ₁ ψ₂ : Name → Nat} (hag : ∀ q ∈ cv.levelParams, ψ₁ q = ψ₂ q) : D.w ψ₁ = D.w ψ₂ := by
  obtain ⟨-, -, hrd, -⟩ := mpC.lfp_ok D hD
  obtain ⟨cv', caps', hf', hab⟩ := hrd mm hmm
  rw [hf] at hf'
  obtain ⟨rfl, -⟩ : cv = cv' ∧ caps = caps' := by
    injection hf' with h'; injection h' with h1 h2; exact ⟨h1, h2⟩
  obtain ⟨ab₁, h₁, -⟩ := hab ψ₁
  obtain ⟨ab₂, h₂, -⟩ := hab ψ₂
  have hwf := mpC.base2.wf.consts _ (ConLeche.Env.find?_mem hf)
  rw [denote_params_ext mpC.base2 hag 0 cv.type hwf.2.1, h₂] at h₁
  have h := (mkPisAV_sort_inj (Option.some.inj h₁)).2
  exact h.symm

/-- **The ι case split, unfolded.** -/
theorem iotaCtorNeverProp_inv {f : Name → Option ConstantInfo} {cvj : ConstantVal}
    {usj : List Level} (h : ConLeche.iotaCtorNeverProp f cvj usj = true) :
    ∃ (T : Name) (us₀ : List Level) (cvT : ConstantVal) (caps : ConLeche.IndCaps),
      (cvj.type.piResult).getAppFn = .const T us₀ ∧ f T = some (.indInfo cvT caps) ∧
      cvT.levelParams.length = usj.length ∧
      ConLeche.capsNeverZero cvT.levelParams usj caps = true := by
  revert h
  unfold ConLeche.iotaCtorNeverProp
  match hpr : (cvj.type.piResult).getAppFn with
  | .bvar _ | .fvar _ _ | .sort _ | .app _ _ | .lam _ _
  | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ => intro h; exact nomatch h
  | .const T us₀ =>
    dsimp only
    match hfT : f T with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) | some (.defnInfo _ _ _) | some (.thmInfo _)
    | some (.ctorInfo _ _ _) | some (.recInfo _ _ _ _ _) => intro h; exact nomatch h
    | some (.indInfo cvT caps) =>
      intro h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨T, us₀, cvT, caps, rfl, hfT, h.1, h.2⟩

/-- An application spine over a head that is not a `∀` is its own
`piResult`. -/
theorem piResult_mkAppN_of_ne : ∀ (args : List Expr) (f : Expr),
    (∀ b c, f ≠ .forallE b c) → (Expr.mkAppN f args).piResult = Expr.mkAppN f args
  | [], f, hf => by
    cases f with
    | forallE b c => exact absurd rfl (hf b c)
    | _ => rfl
  | a :: as, f, _ => piResult_mkAppN_of_ne as (.app f a) (fun _ _ h => nomatch h)

/-- **A syntactic telescope ending in a constant application** has that
constant at the head of its `piResult`. -/
theorem piResult_getAppFn_of_stripPis {I : Name} {us : List Level} :
    ∀ (n : Nat) {e : Expr} {bs : List Expr} {args : List Expr},
      e.stripPis n = some (bs, Expr.mkAppN (.const I us) args) →
      (e.piResult).getAppFn = .const I us
  | 0, e, bs, args, h => by
    simp only [ConLeche.Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.2, piResult_mkAppN_of_ne args (.const I us) (fun _ _ h => nomatch h), getAppFn_mkAppN_const]
  | n + 1, e, bs, args, h => by
    match e with
    | .forallE ty b =>
      simp only [ConLeche.Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', r⟩, hr, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      show b.piResult.getAppFn = _
      exact piResult_getAppFn_of_stripPis n hr
    | .bvar _ | .sort _ | .const _ _ | .lit _ | .fvar _ _ | .app _ _ | .lam _ _
    | .letE _ _ _ | .proj _ _ _ => exact absurd h (by simp [ConLeche.Expr.stripPis])

/-- **A never-zero sort datum, instantiated, is never zero.** -/
theorem eval_ne_zero_of_isNever {lps : List Name} {us : List Level} {v : Level}
    (h : (Level.substPW lps us (Level.zeronessOf v)).isNever = true) (φ : Name → Nat) :
    Level.eval (Level.substFn φ lps us) v ≠ 0 := by
  have hn := ConLeche.PropWhen.isNever_iff.mp h
  have hh := ConLeche.Level.holds_substPW φ lps us (Level.zeronessOf v)
  rw [hn, ConLeche.PropWhen.holds_never, ConLeche.PropWhen.zeronessOf_sound] at hh
  intro h0
  rw [h0] at hh
  exact nomatch hh

/-- Every member's record carries the block's sort zero-ness. -/
theorem blockCapsAt_sortZ (p : BlockShape) (mi : Nat) (isRec : Bool) :
    (ConLeche.blockCapsAt p mi isRec).sortZ = Level.zeronessOf p.resSort := by
  rcases blockCapsAt_cases p mi isRec with ⟨c, -, h⟩ | h <;> rw [h]

omit [SetTheory V] in
theorem openFvars_getElem? : ∀ (k d q : Nat), q < k →
    (openFvars d k)[q]? = some (.fvar (d + q) (.sort .zero))
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | k + 1, d, 0, _ => by simp [openFvars]
  | k + 1, d, q + 1, h => by
    rw [openFvars_succ, List.getElem?_cons_succ, openFvars_getElem? k (d + 1) q (by omega)]
    congr 2; omega

omit [SetTheory V] in
theorem openFvars_length : ∀ (k d : Nat), (openFvars d k).length = k
  | 0, _ => rfl
  | k + 1, d => by rw [openFvars_succ, List.length_cons, openFvars_length k (d + 1)]

omit [SetTheory V] in
theorem openFvars_closed : ∀ (k d : Nat), ∀ a ∈ openFvars d k, a.looseBVarsBounded 0 = true
  | 0, _, a, h => nomatch h
  | k + 1, d, a, h => by
    rw [openFvars_succ] at h
    rcases List.mem_cons.mp h with rfl | h
    · rfl
    · exact openFvars_closed k (d + 1) a h

/-- **A stored constructor type of the recorded shape reads as a Π-tower
over its parameters and fields ending in its family at the parameter
variables** (`ctorBodyAVI`'s shape): the syntactic shape (`LfpCaps`)
opened at variables (`openPisAtFvars_stripPis`) and read
(`denote_openPis`), the parameter variables reading as the
parameters' de Bruijn indices. -/
theorem denote_ctorShape {acval : Name → (Name → Nat) → Term} {env : Env}
    {ψ : Name → Nat} {cv : ConstantVal} {I : Name} {nPc nF : Nat}
    {bs : List Expr} {es : List Expr} {ciI : ConstantInfo} {ea : Term}
    (hfI : env.find? I = some ciI)
    (hlI : (cv.levelParams.map Level.param).length = ciI.toConstantVal.levelParams.length)
    (hst : cv.type.stripPis (nPc + nF)
      = some (bs, Expr.mkAppN (.const I (cv.levelParams.map .param))
          (ConLeche.structPsAt nF nPc ++ es)))
    (hread : denote acval env ψ 0 cv.type = some ea) :
    ∃ (pps : List Term) (Es : List Term),
      ea = mkPisAV pps (Term.mkAppN
        (acval I (Level.substFn ψ ciI.toConstantVal.levelParams (cv.levelParams.map .param)))
        (paramBvars nPc nF ++ Es)) ∧
      pps.length = nPc + nF ∧ Es.length = es.length := by
  obtain ⟨fvs, o, hop⟩ := openPisAtFvars_of_stripPis_isSome (nPc + nF) (e := cv.type) 0
    (by rw [hst]; rfl)
  obtain ⟨bs', body₀, hst', -, -, herase⟩ := openPisAtFvars_stripPis (nPc + nF) hop
  rw [hst] at hst'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hst').symm
  obtain ⟨pps, b, hsAV, hb, hplen, -⟩ := denote_openPis (nPc + nF) hop hread
  rw [Nat.zero_add, denote_erasedEq herase, Expr.instSeq_mkAppN,
    Expr.instSeq_eq_self _ _ (show (Expr.const I (cv.levelParams.map .param)).looseBVarsBounded 0
      = true from rfl)] at hb
  obtain ⟨fa, vs, hfa, hspv, rfl⟩ := denote_mkAppN_inv hb
  rw [denote_const hfI hlI] at hfa
  obtain rfl := Option.some.inj hfa
  obtain ⟨hea, -⟩ := stripPisAV_eq_mkPis hsAV
  have hlenv := hspv.length
  rw [List.length_map, List.length_append] at hlenv
  have hPs : (ConLeche.structPsAt nF nPc).length = nPc := by
    simp [ConLeche.structPsAt]
  refine ⟨pps, vs.drop nPc, ?_, hplen, by rw [List.length_drop]; omega⟩
  rw [hea]
  suffices hP : vs.take nPc = paramBvars nPc nF by
    rw [← hP, List.take_append_drop]
  -- the parameter part
  have hspP := hspv.take nPc
  rw [← List.map_take, List.take_left' hPs] at hspP
  have hPL : (paramBvars nPc nF).length = nPc := by simp [paramBvars]
  have hlt : (vs.take nPc).length = (paramBvars nPc nF).length := by
    rw [List.length_take, hPL]; omega
  refine List.ext_getElem hlt fun q h1 h2 => ?_
  have hq : q < nPc := by rw [hPL] at h2; exact h2
  have hg := hspP.getD default q (by rw [List.length_map, hPs]; exact hq)
  have harg : ((ConLeche.structPsAt nF nPc).map
      (Expr.instSeq (openFvars 0 (nPc + nF)) (nPc + nF - 1) ·)).getD q default
      = .fvar q (.sort .zero) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    have hel : (ConLeche.structPsAt nF nPc)[q]? = some (.bvar (nF + nPc - 1 - q)) := by
      simp [ConLeche.structPsAt, List.getElem?_map, List.getElem?_range hq]
    rw [hel, Option.map_some, Option.getD_some]
    have := Expr.instSeq_bvar (openFvars 0 (nPc + nF)) (nPc + nF - 1) (nF + nPc - 1 - q)
      (openFvars_closed _ 0) (by omega) (by rw [openFvars_length]; omega)
    rw [show nPc + nF - 1 - (nF + nPc - 1 - q) = q from by omega,
      openFvars_getElem? _ 0 q (by omega)] at this
    rw [Nat.zero_add] at this
    exact (Option.some.inj this).symm
  rw [harg, denote_fvar] at hg
  have hgv := (Option.some.inj hg)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at hgv
  rw [← hgv]
  simp [paramBvars]

/-- **A never-zero datum, instantiated, fails everywhere.** -/
theorem holds_false_of_isNever {lps : List Name} {us : List Level} {pw : ConLeche.PropWhen}
    (h : (Level.substPW lps us pw).isNever = true) (φ : Name → Nat) :
    pw.holds (Level.substFn φ lps us) = false := by
  have hn := ConLeche.PropWhen.isNever_iff.mp h
  have hh := ConLeche.Level.holds_substPW φ lps us pw
  rw [hn, ConLeche.PropWhen.holds_never] at hh
  exact hh.symm

omit [SetTheory V] in
theorem domsBelow_drop : ∀ (n : Nat) {k : Nat} {ab : List Term},
    DomsBelow k ab → DomsBelow (k + n) (ab.drop n)
  | 0, _, _, h => h
  | _ + 1, _, [], _ => trivial
  | n + 1, k, _ :: ab, h => by
    rw [List.drop_succ_cons, show k + (n + 1) = (k + 1) + n from by omega]
    exact domsBelow_drop n h.2

omit [SetTheory V] in
theorem getD_append_left' {α : Type _} {l₁ l₂ : List α} {q : Nat} {x : α} (hq : q < l₁.length) :
    (l₁ ++ l₂).getD q x = l₁.getD q x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hq]

omit [SetTheory V] in
theorem getD_append_right' {α : Type _} {l₁ l₂ : List α} {q : Nat} {x : α} :
    (l₁ ++ l₂).getD (l₁.length + q) x = l₂.getD q x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

/-- **A fit extends across a peel** (`teleFit_peel'`'s converse): a
fitting prefix spine followed by a fit of the peel's residual is a fit of
the whole telescope. -/
theorem teleFit_unpeel :
    ∀ (ws : List Term) {T C : Term} {σ : Nat → V} {fs : List V} {X : V},
      TeleFitPA V σ T ws C → Rules.PiChain (ws.length + fs.length) T →
      TeleFit V σ C fs X → TeleFit V σ T (ws.map (interp V σ) ++ fs) X
  | [], T, C, σ, fs, X, h, _, hC => by
    cases h
    simpa using hC
  | w :: ws, _, C, σ, fs, X, h, hpc, hC => by
    cases h with
    | @cons A B _ _ _ hmem htail =>
      have hB : Rules.PiChain (ws.length + fs.length) B := by
        have e : (w :: ws).length + fs.length = (ws.length + fs.length) + 1 := by
          simp only [List.length_cons]; omega
        rw [e] at hpc
        exact hpc
      have ih := teleFit_unpeel ws htail (Rules.PiChain.inst w 0 hB) hC
      rw [List.map_cons, List.cons_append]
      exact .cons hmem (Rules.teleFit_of_inst0
        (by rw [List.length_append, List.length_map]; exact hB) ih)

end Generic

/-! ## 1. A member class's facts -/

section Member

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {d : BlockData V}

/-- **What a member class knows of its constructor `i`**, at every level
assignment. -/
structure GenMemAt (mpC : EnvModelM V envC) (d : BlockData V) (pp : BlockParts)
    (out : List (ConstantVal × TargetMajor × List Expr)) (isRec : Bool) (cvT : ConstantVal)
    (j i t : Nat) (cA : ConstantVal × Nat) : Prop where
  hcj : (d.ctorsM t)[i]? = some cA
  htd : t < d.k
  hmN : t < d.N
  hjl : i < (d.ctorsM t).length
  hM : BlockModelAt mpC.base2 d.memberNames d
  hcf : BlockCtorFacts mpC.base2 d pp.lps t i cA
  hdnP : d.nP = pp.nP
  hnPc : (ConLeche.tgtMajorsOf out j).nPc = pp.nP
  hwd : ∀ ψ, d.w ψ = Level.eval ψ pp.toBlockShape.resSort
  hparamsC : ∀ (ψ : Name → Nat) (σ : Nat → V), Sat V (d.params ψ).reverse σ
      ↔ Sat V ((d.dsF t i ψ).take d.nP).reverse σ
  hlenP : ∀ ψ : Name → Nat, (d.params ψ).length = d.nP
  hctorRead : ∀ ψ' : Name → Nat, denote mpC.base2.acval envC ψ' 0 cA.1.type
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ')
  hcaps : envC.find? (d.memberName t)
      = some (.indInfo cvT (ConLeche.blockCapsAt pp.toBlockShape t isRec))
  hlfp : d.toLfp ∈ mpC.lfpBlocks
  hlenIds : ∀ ψ : Name → Nat, (d.IdsM t ψ).length = d.nIdxAt t
  hlpsT : cvT.levelParams = cA.1.levelParams
  hctLen : (d.ctorsM t).length = (pp.toBlockShape.members.getD t default).ctors.length
  hctM : d.ctorsM t = (tgtMajor out j).ctors

set_option maxHeartbeats 4000000 in
/-- **A member class's facts, from the run** (`genRows3_mem`'s preamble). -/
theorem genMemAt_of
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List Term}
    {isRec : Bool} {A : Nat → (Name → Nat) → Term} {envI' : Env}
    (hdR : d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hSt : BlockCtorsStage (V := V) F d pp.lps cvTas pp.toBlockShape isRec A envI'
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    (hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))))
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {t : Nat} (hm : (tgtMajor out j).member = some t)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA) :
    ∃ cvT, GenMemAt mpC d pp out isRec cvT j i t cA := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
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
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by rw [← tgtRs_ctors hr]; exact hcA
  have hctM : d.ctorsM t = M₀.ctors := by
    subst hdR; show ctorsAs.getD t [] = M₀.ctors
    rw [List.getD_eq_getElem?_getD, hctors]; rfl
  have hcj : (d.ctorsM t)[i]? = some cA := by
    rw [hctM]; rw [hMj] at hcAM; exact hcAM
  have htd : t < d.k := by subst hdR; exact htk
  have hdnP : d.nP = pp.nP := by subst hdR; rfl
  have hwd : ∀ ψ, d.w ψ = Level.eval ψ pp.toBlockShape.resSort := by subst hdR; intro ψ; rfl
  have hk0 : 0 < d.k := by omega
  have hmN : t < d.N := Nat.lt_of_lt_of_le htd (Nat.le_add_right _ _)
  have hjl : i < (d.ctorsM t).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hM : BlockModelAt mpC.base2 d.memberNames d := by
    subst hdR; exact blockModelAt_seam h hN hSt hcore
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2 _ htd i cA hcj
  obtain ⟨-, -, hcd, -⟩ := hcore.2.1 _ i cA hcj
  have hcf : BlockCtorFacts mpC.base2 d pp.lps t i cA := ⟨hfindC, hlpsC, hcd⟩
  have hctorRead : ∀ ψ' : Name → Nat, denote mpC.base2.acval envC ψ' 0 cA.1.type
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ') := by
    intro ψ'
    have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
      rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
    rw [blockRecCtorTy, hsel, hcd.read ψ']
    rfl
  have hparamsC : ∀ (ψ : Name → Nat) (σ : Nat → V), Sat V (d.params ψ).reverse σ
      ↔ Sat V ((d.dsF t i ψ).take d.nP).reverse σ := fun ψ σ =>
    ⟨fun hσ => ((hSt.frames _ htd i cA hcj).1 _ σ).mp (hSt.paramsOf 0 hk0 _ σ hσ _ htd),
      fun hσ => hSt.paramsOf _ htd _ σ (((hSt.frames _ htd i cA hcj).1 _ σ).mpr hσ) 0 hk0⟩
  have hlenP : ∀ ψ : Name → Nat, (d.params ψ).length = d.nP := by
    intro ψ
    have hl := hSt.lenPps 0 ψ hk0
    show ((d.ppsM 0 ψ).take d.nP).length = d.nP
    rw [List.length_take]
    exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hl.symm))
  obtain ⟨cvT, hcvT⟩ : ∃ cvT, cvTas[t]? = some cvT :=
    ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact htd)⟩
  obtain ⟨hfT, -, -, -⟩ := hcore.1 t cvT hcvT
  have hcaps : envC.find? (d.memberName t)
      = some (.indInfo cvT (ConLeche.blockCapsAt pp.toBlockShape t isRec)) := by
    rw [hN.1 t cvT hcvT]; exact hfT
  have hctMj : d.ctorsM t = (tgtMajor out j).ctors := by rw [hctM, hMj]
  refine ⟨cvT, hcj, htd, hmN, hjl, hM, hcf, hdnP, hnPc', hwd, hparamsC, hlenP, hctorRead,
    hcaps, hlfp, hSt.lenIds t htd, ?_, ?_, hctMj⟩
  rotate_left
  · have hc0 := congrArg (fun L => (L[t]?).map List.length) hnames
    simp only [List.getElem?_map, hms, hctors, Option.map_some, List.length_map,
      Option.some.injEq] at hc0
    rw [hctM, hc0]
    show _ = (pp.members.getD t default).ctors.length
    rw [List.getD_eq_getElem?_getD, hms, Option.getD_some]
  -- the member's former carries the constructor's level parameters (`LfpCtorReads`)
  obtain ⟨-, -, -, hrdC, -⟩ := mpC.lfp_ok _ hlfp
  obtain ⟨cv, nPc, nF, hfc, -, hall, -⟩ := hrdC.2 t htd i hjl
  have hname : d.toLfp.ctorName t i = cA.1.name := by
    show ((d.ctorsM t).getD i default).1.name = _
    rw [List.getD_eq_getElem?_getD, hcj]; rfl
  rw [hname, hfindC] at hfc
  obtain rfl : cA.1 = cv := by injection hfc with h'; injection h' with h1
  obtain ⟨cvm, capsm, hfm, hlm⟩ := hall t htd
  have hfm' : envC.find? (d.memberName t) = some (.indInfo cvm capsm) := hfm
  rw [hcaps] at hfm'
  obtain rfl : cvT = cvm := by injection hfm' with h'; injection h' with h1
  exact hlm

set_option maxHeartbeats 4000000 in
/-- **The major lies in the member's carrier** at the recursor's
parameters and index tuple (`genRows3_mem`'s class step). -/
theorem genMem_major
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    (ψ : Name → Nat) {ρ : Nat → V} {xs : List Term} {a restR : Term}
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [a]) restR) :
    SpineFit ρ (d.params ψ) (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP) ∧
    SpineFit (consList (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP) ρ)
      (d.IdsM t ψ) ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ∧
    interp V ρ a ∈ˢ app (lfpTuple (d.w ψ) d.N
        (d.idx ψ (consList (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP) ρ))
        (d.Φ ψ (consList (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP) ρ)) t)
      (d.tup ψ t ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))) := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hmS : (tgtMajor out j).member.isSome = true := by rw [hm]; rfl
  have hrt : pp.toBlockShape.recTgtAt j = t := genRun_recTgt R hj hm
  obtain ⟨hpref, hws, hxvl, hisl⟩ := genRow3_frame h hr ψ hxl hfitR
  obtain ⟨hTin, hmajIn, hisT⟩ := hS ψ ρ j hj _ _ _ hxvl hisl hws
  rw [tgtClsIs_mem hmS] at hTin
  obtain ⟨hpar, -⟩ := blockRecIs_fits hTin
  rw [blockRecIs_pos hpar hpref, tgtClsTup_mem hmS] at hTin
  rw [tgtClsU_mem hmS, tgtClsNIdx_mem hmS, tgtClsTup_mem hmS, hrt] at hisT
  have hTin' := hTin
  rw [hrt] at hTin'
  obtain ⟨is', hsp', hTe⟩ := mem_idxSet_elim hTin'
  have hIok := G.hM.idxOk ψ _ (d.satOfSpine hpar) t G.hmN
  rw [hTe, ← G.hlenIds ψ, isOfW_tupW hIok hsp'] at hisT
  rw [hisT] at hsp' hTe
  refine ⟨hpar, hsp', ?_⟩
  rw [tgtClsCr_mem hmS, tgtClsTup_mem hmS] at hmajIn
  unfold blockRecCr at hmajIn
  rw [hrt] at hmajIn
  exact hmajIn

/-- **Above `Prop` the member's carrier holds no point**: the major is an
injection (`blockCarrier_case`), and no injection is the point there. -/
theorem genMem_ne_pt
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    {ψ : Name → Nat} (hw : d.w ψ ≠ 0)
    (ρ : Nat → V) (xs : List Term) (a restR : Term)
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [a]) restR) :
    interp V ρ a ≠ pt := by
  obtain ⟨hpar, hsp', hmaj⟩ := genMem_major h R hS G hr hm ψ hxl hfitR
  have ht : d.tup ψ t ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))
      ∈ˢ d.idx ψ (consList (((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take
        d.nP) ρ) t := tupW_mem hsp'
  obtain ⟨j', fs', -, heq⟩ := blockCarrier_case G.hM (d.satOfSpine hpar) G.hmN ht hmaj
  rw [heq]
  exact (mpC.lfp_ok _ G.hlfp).1.injNePt ψ hw t j' fs'

/-- **The case split's sort fact at a member class**: where the member's
sort is never zero at the constructor's levels (the case split reads the
member's record, `blockCapsAt`, which carries the block's sort
zero-ness), the member is not `Prop` at the recursor's levels. -/
theorem genMem_w_of_lic {isRec : Bool} {cvT : ConstantVal} {j i t : Nat}
    {cA : ConstantVal × Nat} (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {ψ : Name → Nat} {usj : List Level} {φ : Name → Nat}
    (hlv : ∀ q ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj q = ψ q)
    {f : Name → Option ConstantInfo}
    (hfm : f (d.memberName t) = some (.indInfo cvT (ConLeche.blockCapsAt pp.toBlockShape t isRec)))
    (hlic : ConLeche.iotaCtorNeverProp f cA.1 usj = true) :
    d.w ψ ≠ 0 := by
  obtain ⟨T, us₀, cvT', caps, hhead, hfT, -, hnz⟩ := iotaCtorNeverProp_inv hlic
  -- the constructor's family is the member
  obtain ⟨cbs, es, hres, -⟩ := G.hcf.2.2.resid
  rw [piResult_getAppFn_of_stripPis _ hres] at hhead
  obtain ⟨rfl, -⟩ := ConLeche.Expr.const.inj hhead
  rw [hfm] at hfT
  obtain ⟨rfl, rfl⟩ : cvT = cvT' ∧ ConLeche.blockCapsAt pp.toBlockShape t isRec = caps := by
    injection hfT with h'; injection h' with h1 h2; exact ⟨h1, h2⟩
  unfold ConLeche.capsNeverZero at hnz
  rw [blockCapsAt_sortZ] at hnz
  have hne := eval_ne_zero_of_isNever hnz φ
  rw [G.hlpsT, ← G.hwd] at hne
  -- the member's sort at the recursor's levels
  have hc : d.w (Level.substFn φ cA.1.levelParams usj) = d.w ψ :=
    lfpW_congr mpC (D := d.toLfp) G.hlfp G.htd G.hcaps (fun q hq => by
      rw [G.hlpsT] at hq; exact hlv q hq)
  exact hc ▸ hne

/-- **(S) at a member class**: where the case split exempts the rule, the member's
carrier at the recursor's parameters is strict (`genMem_w_of_lic`), so
the major is not the point. -/
theorem genMem_S
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    {ψ : Name → Nat} {usj : List Level} {φ : Name → Nat}
    (hlv : ∀ q ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj q = ψ q)
    {f : Name → Option ConstantInfo}
    (hfm : f (d.memberName t) = some (.indInfo cvT (ConLeche.blockCapsAt pp.toBlockShape t isRec)))
    (hlic : ConLeche.iotaCtorNeverProp f cA.1 usj = true)
    (ρ : Nat → V) (xs : List Term) (a restR : Term)
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [a]) restR) :
    interp V ρ a ≠ pt :=
  genMem_ne_pt h R hS G hr hm (genMem_w_of_lic G hlv hfm hlic) ρ xs a restR hxl hfitR

/-- **At a `Prop` valuation of a member, its constructor is the point**,
and so is every application of it: every binder of the constructor's
type carries the family's zero-ness (its innermost fibre is the
member's, a truth value), so the type is a truth value; a constructor with no binder at all lies in the
member's fibre, whose elements are injections, all the point. -/
theorem genMemCtor_pt {isRec : Bool} {cvT : ConstantVal} {j i t : Nat}
    {cA : ConstantVal × Nat} (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {ψj : Name → Nat} (hw : d.w ψj = 0) (ρ : Nat → V) (ys : List Term) :
    interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys) = pt := by
  refine Rules.interp_mkAppN_pt ?_ ys
  have hcd := G.hcf.2.2
  have hmem := mpC.mem_type _ (ConLeche.Env.find?_mem G.hcf.1) ψj _ (hcd.read ψj) ρ
  change interp V ρ (mpC.base2.acval cA.1.name ψj) ∈ˢ _ at hmem
  cases hds : d.dsF t i ψj with
  | cons dd ds =>
    -- the constructor's type is a truth value: at every fitting spine its
    -- body is the member's fibre at the index tuple, whose elements are
    -- injections, all the point at a `Prop` valuation (`IndFibLaw` at `0`)
    have hlenD := hcd.len ψj
    have htyZ : interp V ρ (mkPisAV (d.dsF t i ψj)
        (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj)))
          ∈ˢ (univZero : V) := by
      refine mkPisAV_mem_univZero fun vs hvs => ?_
      rw [← List.take_append_drop d.nP (d.dsF t i ψj)] at hvs
      obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_inv hvs
      have hxl : xs.length = d.nP := by
        rw [hxs.length_eq, List.length_take, hlenD]; omega
      have hfl : fs.length = cA.2 := by
        rw [hfs.length_eq, List.length_drop, hlenD]; omega
      have hsatD : Sat V (((d.dsF t i ψj).take d.nP)).reverse (consList xs ρ) := by
        have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hxs
        rwa [List.append_nil] at this
      have hsat : Sat V (d.params ψj).reverse (consList xs ρ) := (G.hparamsC ψj _).mpr hsatD
      have hxsP : SpineFit ρ (d.params ψj) xs :=
        spineFit_of_sat_consList (by rw [hxl, G.hlenP]) hsat
      have hFssD : (d.Fss t ψj).getD i [] = ((d.dsF t i ψj).drop d.nP) :=
        fssOfR_fixCtorDataList_getD G.hcj
      have hEssD : (d.Ess t ψj).getD i [] = d.esF t i ψj := essOfR_fixCtorDataList_getD G.hcj
      have hfsF : SpineFit (consList xs ρ) ((d.Fss t ψj).getD i []) fs := by
        rw [hFssD]; exact hfs
      have hres := G.hM.resIdxFit ψj (consList xs ρ) hsat t G.hmN i G.hjl fs hfsF
      rw [hEssD] at hres
      have hleaf := G.hM.leaf t G.htd ψj ρ xs _ hxsP hres
      have hpv : (paramBvars d.nP cA.2).map (interp V (consList (xs ++ fs) ρ)) = xs := by
        have heqP : paramBvars d.nP cA.2 = prefVarsAV d.nP cA.2 := by
          unfold paramBvars prefVarsAV; rw [Nat.add_comm d.nP cA.2]
        rw [heqP, ← hfl]
        exact interp_prefVarsAV hxl
      have hbody : interp V (consList (xs ++ fs) ρ)
          (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj))
          = (xs ++ (d.esF t i ψj).map (interp V (consList fs (consList xs ρ)))).foldl
              SetTheory.app (interp V ρ (mpC.base2.acval (d.memberName t) ψj)) := by
        rw [ctorBodyAVI, interp_mkAppN_foldl, List.map_append, hpv, ← consList_append,
          acval_interp_closed mpC.base2 (d.memberName t) ψj (consList (xs ++ fs) ρ) ρ]
      rw [hbody, hleaf]
      refine mem_univZero.mpr fun y hy => mem_unitSet_iff.mpr ?_
      obtain ⟨j', fs', -, heq⟩ := blockCarrier_case G.hM hsat G.hmN (tupW_mem hres) hy
      rw [heq]
      exact G.hM.mkZero ψj hw t j' fs'
    exact eq_pt_of_mem_univZero htyZ hmem
  | nil =>
    rw [hds] at hmem
    have hlen := hcd.len ψj
    rw [hds, List.length_nil] at hlen
    have hnP0 : d.nP = 0 := by omega
    have hnF0 : cA.2 = 0 := by omega
    -- the body is the member at the result index readings
    have hpar : d.params ψj = [] := List.eq_nil_of_length_eq_zero (by rw [G.hlenP, hnP0])
    have hsat : Sat V (d.params ψj).reverse ρ := by rw [hpar]; exact Sat_nil V ρ
    have hFssD : (d.Fss t ψj).getD i [] = ((d.dsF t i ψj).drop d.nP) :=
      fssOfR_fixCtorDataList_getD G.hcj
    have hFss : (d.Fss t ψj).getD i [] = [] := by rw [hFssD, hds]; simp
    have hfit0 : SpineFit ρ ((d.Fss t ψj).getD i []) [] := by rw [hFss]; trivial
    have hres := G.hM.resIdxFit ψj ρ hsat t G.hmN i G.hjl [] hfit0
    have hEssD : (d.Ess t ψj).getD i [] = d.esF t i ψj := essOfR_fixCtorDataList_getD G.hcj
    rw [hEssD] at hres
    have hleaf := G.hM.leaf t G.htd ψj ρ [] _ (by rw [hpar]; trivial) hres
    simp only [consList_nil, List.nil_append] at hleaf
    have hbody : interp V ρ (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj))
        = ((d.esF t i ψj).map (interp V ρ)).foldl SetTheory.app
            (interp V ρ (mpC.base2.acval (d.memberName t) ψj)) := by
      rw [ctorBodyAVI, hnP0, interp_mkAppN_foldl]
      simp [paramBvars]
    change interp V ρ (mpC.base2.acval cA.1.name ψj)
      ∈ˢ interp V ρ (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj)) at hmem
    rw [hbody, hleaf] at hmem
    have ht : d.tup ψj t ((d.esF t i ψj).map (interp V ρ)) ∈ˢ d.idx ψj ρ t := by
      have := tupW_mem (u := d.uM t ψj) hres
      simp only [consList_nil] at this
      exact this
    obtain ⟨j', fs', -, heq⟩ := blockCarrier_case G.hM (ρp := ρ) hsat G.hmN ht (by
      simpa [consList_nil] using hmem)
    rw [heq]
    exact G.hM.mkZero ψj hw t j' fs'

/-- **(P) at a member class**: where the major's domain holds the point
the member is `Prop` at the recursor's levels (above it the carrier holds
no point), hence at the constructor's, and every application of the
constructor is the point. -/
theorem genMem_P
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    {ψ ψj : Name → Nat} (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    (ρ : Nat → V) (xs : List Term) (a restR : Term)
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [a]) restR)
    (hapt : interp V ρ a = pt) (ys : List Term) :
    interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys) = pt := by
  have hw : d.w ψ = 0 := by
    refine Classical.byContradiction fun hw => ?_
    exact genMem_ne_pt h R hS G hr hm hw ρ xs a restR hxl hfitR hapt
  have hc : d.w ψj = d.w ψ :=
    lfpW_congr mpC (D := d.toLfp) G.hlfp G.htd G.hcaps (fun q hq => by
      rw [G.hlpsT] at hq; exact hlv q hq)
  exact genMemCtor_pt G (hc.trans hw) ρ ys

/-- **The constructor residual's index arguments** (`blockRuleIdxPin_run`'s
decomposition, forwards): a spelling of the residual of a fit of the
constructor's type as an application whose arguments are the parameters
and indices names, at each index position, the constructor's own result
index reading at the fired spine. -/
theorem genMem_residual {isRec : Bool} {cvT : ConstantVal} {j i t : Nat}
    {cA : ConstantVal × Nat} (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {ψ ψj : Name → Nat} (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    {ρ : Nat → V} {ys : List Term} {restC : Term}
    (hys : ys.length = d.nP + cA.2)
    (hfitC : TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) ys restC)
    {Ha : Term} {cargsa : List Term} (hrestEq : restC = Term.mkAppN Ha cargsa)
    (hcarLen : cargsa.length = d.nP + (d.esF t i ψ).length) :
    ∀ q, q < (d.esF t i ψ).length →
      interp V ρ (cargsa.getD (d.nP + q) default)
        = interp V (consList (ys.map (interp V ρ)) ρ) ((d.esF t i ψ).getD q default) := by
  have hD := G.hcf.2.2
  have hct : blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj
      = mkPisAV (d.dsF t i ψj)
          (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj)) :=
    Option.some.inj ((G.hctorRead ψj).symm.trans (hD.read ψj))
  rw [hct] at hfitC
  have hes : d.esF t i ψj = d.esF t i ψ := (hD.params ψj ψ hlv).2
  have hteleC := piTeleAV_mkPisAV (d.dsF t i ψj)
    (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t i ψj))
  rw [hD.len ψj] at hteleC
  have hrest := teleFitPA_rest_eq (d.nP + cA.2) hteleC (by rw [hys]) hfitC
  have hrest2 : Term.mkAppN Ha cargsa
      = Term.mkAppN
          (Term.instSeq ys (d.nP + cA.2 - 1)
            (mpC.base2.acval (d.memberName t) ψj))
          ((paramBvars d.nP cA.2 ++ d.esF t i ψj).map
            (Term.instSeq ys (d.nP + cA.2 - 1))) := by
    rw [← hrestEq, hrest]
    unfold ctorBodyAVI
    rw [instSeqAV_mkAppN]
  obtain ⟨-, hcargs⟩ := Term.mkAppN_inj hrest2
    (by rw [hcarLen, List.length_map, List.length_append, paramBvars, List.length_map,
      List.length_range, hes])
  intro q hq
  have hqj : q < (d.esF t i ψj).length := by rw [hes]; exact hq
  have hcel : cargsa.getD (d.nP + q) default
      = Term.instSeq ys (d.nP + cA.2 - 1) ((d.esF t i ψj).getD q default) := by
    have hq' := congrArg (fun l => l[d.nP + q]?) hcargs
    simp only [List.getElem?_map,
      List.getElem?_append_right
        (show (paramBvars d.nP cA.2).length ≤ d.nP + q by
          rw [paramBvars, List.length_map, List.length_range]; omega),
      show (paramBvars d.nP cA.2).length = d.nP from by
        rw [paramBvars, List.length_map, List.length_range],
      Nat.add_sub_cancel_left] at hq'
    rw [List.getD_eq_getElem?_getD, hq', List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hqj, Option.map_some, Option.getD_some, Option.getD_some]
  rw [hcel, show d.nP + cA.2 - 1 = ys.length - 1 from by rw [hys], interp_instSeq, hes]
  unfold chain
  rw [consN_eq_consList]

omit [SetTheory V] in
theorem getD_take' {α : Type _} {l : List α} {n q : Nat} {x : α} (hq : q < n) :
    (l.take n).getD q x = l.getD q x := by
  simp [List.getD_eq_getElem?_getD, hq]

omit [SetTheory V] in
theorem getD_drop' {α : Type _} {l : List α} {n q : Nat} {x : α} :
    (l.drop n).getD q x = l.getD (n + q) x := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- A mapped spine's `getD` at a position in range. -/
theorem getD_map_pt {f : Term → V} :
    ∀ {l : List Term} {q : Nat}, q < l.length →
      (l.map f).getD q pt = f (l.getD q default) := by
  intro l q hq
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  rfl

set_option maxHeartbeats 4000000 in
/-- **(U)'s index pin at a member class** (L7's coherence): where the
fired constructor application is the point, the step compared the
parameters and the indices, each conditionally; the parameters are fits
of the constructor's parameter telescope (a telescope of types), so
they are equal, and the indices are then fits of the member's index
telescope at the same parameters, so they are equal too. -/
theorem genMem_U
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt j)
    {ψ ψj : Name → Nat} (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    {ρ : Nat → V} {xs ys : List Term} {restR restC : Term}
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j) (hyl : ys.length = pp.nP + cA.2)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    (hfitC : TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) ys restC)
    (hP : ∀ q, q < pp.nP → interp V ρ (ys.getD q default) ≠ pt →
      interp V ρ (xs.getD q default) ≠ pt →
      interp V ρ (ys.getD q default) = interp V ρ (xs.getD q default))
    (hpinC : IotaIndexPinC (V := V) ρ restC pp.nP (pp.toBlockShape.majorIdxAt j)
      (pp.toBlockShape.rulePrefixAt j) xs) :
    IotaIndexPin (V := V) ρ restC pp.nP (pp.toBlockShape.majorIdxAt j)
      (pp.toBlockShape.rulePrefixAt j) xs := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hrPle := blockRecHrPle (p := pp) h hj
  have hys : ys.length = d.nP + cA.2 := by rw [hyl, G.hdnP]
  have hnP' : d.nP ≤ pp.toBlockShape.rulePrefixAt j := by rw [G.hdnP]; exact hnP
  obtain ⟨hqs, hfq⟩ := blockRuleCtorFit_run G.hcj G.hcf hlv (G.hlenP ψ) (G.hparamsC ψ) hys
    (G.hctorRead ψj) hfitC
  obtain ⟨hpar, hsp', -⟩ := genMem_major h R hS G hr hm ψ hxl hfitR
  have hpsV : ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP
      = (xs.take d.nP).map (interp V ρ) := by
    rw [← List.map_take, List.take_take, Nat.min_eq_left hnP']
  rw [hpsV] at hpar hsp'
  -- the parameters, in the constructor's own parameter telescope (a telescope of types)
  have hD := G.hcf.2.2
  have hlenD : (((d.dsF t i ψ).take d.nP)).length = d.nP := by
    rw [List.length_take, hD.len ψ]; omega
  have hTy : SpineTy ρ (((d.dsF t i ψ).take d.nP)) :=
    (spineTy_of_wellDenoted_mkPisAV (hD.okTy ψ ρ).1).take d.nP
  have hlenPs := G.hlenP ψ
  have hq' := (spineFit_iff_of_sat_iff (by rw [hlenPs, hlenD]) (G.hparamsC ψ) ρ _
    (by rw [hqs.length_eq])).mp hqs
  have hp' := (spineFit_iff_of_sat_iff (by rw [hlenPs, hlenD]) (G.hparamsC ψ) ρ _
    (by rw [hpar.length_eq])).mp hpar
  have hxlP : d.nP ≤ xs.length := by rw [hxl]; omega
  have heqP : (ys.take d.nP).map (interp V ρ) = (xs.take d.nP).map (interp V ρ) := by
    refine spineFit_eq_of_cond_getD hTy hq' hp' fun q hq h1 h2 => ?_
    rw [hlenD] at hq
    have hqy : q < (ys.take d.nP).length := by rw [List.length_take]; omega
    have hqx : q < (xs.take d.nP).length := by rw [List.length_take]; omega
    rw [getD_map_pt hqy] at h1 ⊢
    rw [getD_map_pt hqx] at h2 ⊢
    simp only [getD_take' hq] at h1 h2 ⊢
    exact hP q (by rw [← G.hdnP]; exact hq) h1 h2
  -- the indices, in the member's index telescope at those parameters
  have hE := G.hM.resIdxFit ψ _ (d.satOfSpine hqs) t G.hmN i G.hjl _ hfq
  rw [heqP] at hE
  have hTI : SpineTy (consList ((xs.take d.nP).map (interp V ρ)) ρ) (d.IdsM t ψ) :=
    (G.hM.idxOk ψ _ (d.satOfSpine hpar) t G.hmN).1.spineTy
  have hEssD : (d.Ess t ψ).getD i [] = d.esF t i ψ := essOfR_fixCtorDataList_getD G.hcj
  rw [hEssD] at hE
  have hframe : consList ((ys.drop d.nP).map (interp V ρ))
      (consList ((xs.take d.nP).map (interp V ρ)) ρ)
      = consList (ys.map (interp V ρ)) ρ := by
    rw [← heqP, ← consList_append, ← List.map_append, List.take_append_drop]
  rw [hframe] at hE
  have hlenE : (d.esF t i ψ).length
      = pp.toBlockShape.majorIdxAt j - pp.toBlockShape.rulePrefixAt j := by
    have h1 := hE.length_eq
    have h2 := hsp'.length_eq
    rw [List.length_map] at h1
    rw [List.length_map, List.length_drop, hxl] at h2
    omega
  obtain ⟨Ha, cargsa, hrestEq, hcarLen, hcar⟩ := hpinC
  refine ⟨Ha, cargsa, hrestEq, hcarLen, fun q hq => ?_⟩
  have hcarLen' : cargsa.length = d.nP + (d.esF t i ψ).length := by
    rcases hcarLen with hc | hc
    · omega
    · rw [hc, hlenE, G.hdnP]
  have hres := genMem_residual G hlv hys hfitC hrestEq hcarLen'
  have heqI : (d.esF t i ψ).map (interp V (consList (ys.map (interp V ρ)) ρ))
      = (xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) := by
    refine spineFit_eq_of_cond_getD hTI hE hsp' fun l hl h1 h2 => ?_
    have hlE : l < (d.esF t i ψ).length := by
      rw [← List.length_map (f := interp V (consList (ys.map (interp V ρ)) ρ)), hE.length_eq]
      exact hl
    have hlX : l < (xs.drop (pp.toBlockShape.rulePrefixAt j)).length := by
      rw [List.length_drop, hxl]; omega
    rw [getD_map_pt hlE] at h1 ⊢
    rw [getD_map_pt hlX] at h2 ⊢
    rw [getD_drop'] at h2 ⊢
    rw [← hres l hlE] at h1 ⊢
    rw [G.hdnP] at h1 ⊢
    exact hcar l (by omega) h1 h2
  have hq' : q < (d.esF t i ψ).length := by rw [hlenE]; exact hq
  have hl := congrArg (fun l => l.getD q pt) heqI
  rw [getD_map_pt hq', getD_map_pt (by rw [List.length_drop, hxl]; omega), getD_drop',
    ← hres q hq'] at hl
  rw [← G.hdnP]
  exact hl

set_option maxHeartbeats 4000000 in
/-- **The K witness at a member class** (inversion of the least fixed
point): at a member with one fieldless constructor, the major in the
carrier at the recursor's parameters and index tuple is that
constructor's injection at no fields, so it is the value of the
constructor applied to the recursor's own parameters, whose stored fit's
index clause is the recursor's index tuple (the index pin); the spine
fits both types. -/
theorem genMem_K
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt j)
    (hone : (d.ctorsM t).length = 1) (hnf0 : cA.2 = 0)
    {ψ ψj : Name → Nat} (hlv : ∀ q ∈ cA.1.levelParams, ψj q = ψ q)
    (ρ : Nat → V) (xs : List Term) (a restR : Term)
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [a]) restR) :
    ∃ restR' restC,
      TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
        (xs ++ [Term.mkAppN (mpC.base2.acval cA.1.name ψj) (xs.take pp.nP)]) restR' ∧
      TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj)
        (xs.take pp.nP) restC ∧
      IotaIndexPin (V := V) ρ restC pp.nP (pp.toBlockShape.majorIdxAt j)
        (pp.toBlockShape.rulePrefixAt j) xs ∧
      interp V ρ a
        = interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) (xs.take pp.nP)) := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hrPle := blockRecHrPle (p := pp) h hj
  have hnP' : d.nP ≤ pp.toBlockShape.rulePrefixAt j := by rw [G.hdnP]; exact hnP
  have hD := G.hcf.2.2
  obtain ⟨hpar, hsp', hmaj⟩ := genMem_major h R hS G hr hm ψ hxl hfitR
  have hpsV : ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP
      = (xs.take d.nP).map (interp V ρ) := by
    rw [← List.map_take, List.take_take, Nat.min_eq_left hnP']
  rw [hpsV] at hpar hsp' hmaj
  rw [← G.hdnP]
  -- the carrier's decomposition: the one constructor, no fields
  have ht : d.tup ψ t ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))
      ∈ˢ d.idx ψ (consList ((xs.take d.nP).map (interp V ρ)) ρ) t := tupW_mem hsp'
  obtain ⟨j', fs', hfit', heqa⟩ := blockCarrier_case G.hM (d.satOfSpine hpar) G.hmN ht hmaj
  have hj0 : j' = i := by have := hfit'.1; have := G.hjl; omega
  subst hj0
  have hFssD : (d.Fss t ψ).getD j' [] = ((d.dsF t j' ψ).drop d.nP) :=
    fssOfR_fixCtorDataList_getD G.hcj
  have hFss0 : (d.Fss t ψ).getD j' [] = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [hFssD, List.length_drop, hD.len ψ, hnf0]; omega
  have hfs0 : fs' = [] := by
    have := hfit'.2.1.length_eq
    rw [hFss0] at this
    exact List.eq_nil_of_length_eq_zero this
  subst hfs0
  -- the constructor at the recursor's parameters: its value, its fit
  have hyl : (xs.take d.nP).length = d.nP := by rw [List.length_take, hxl]; omega
  have hqs : SpineFit ρ (d.params ψ) (((xs.take d.nP).take d.nP).map (interp V ρ)) := by
    rw [List.take_take, Nat.min_self]; exact hpar
  have hfq : SpineFit (consList (((xs.take d.nP).take d.nP).map (interp V ρ)) ρ)
      ((d.Fss t ψ).getD j' []) (((xs.take d.nP).drop d.nP).map (interp V ρ)) := by
    rw [hFss0, List.drop_eq_nil_of_le (Nat.le_of_eq hyl)]; trivial
  have hval := blockCtorMajor_value G.hM G.hcj G.hcf.1 G.hmN hlv hqs hfq
  rw [List.drop_eq_nil_of_le (Nat.le_of_eq hyl), List.map_nil] at hval
  have heq : interp V ρ a
      = interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) (xs.take d.nP)) := by
    rw [heqa, hval]
  obtain ⟨restR', hfitR'⟩ := Rules.teleFitPA_snoc_congr xs hfitR heq
  have hct : blockRecCtorTy mpC.base2.acval envC (tgtRs out) j j' ψj
      = mkPisAV (d.dsF t j' ψj)
          (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t j' ψj)) :=
    Option.some.inj ((G.hctorRead ψj).symm.trans (hD.read ψj))
  have hds : d.dsF t j' ψj = d.dsF t j' ψ := (hD.params ψj ψ hlv).1
  have hdsLen : (d.dsF t j' ψ).length = d.nP := by rw [hD.len ψ, hnf0]; rfl
  have hspC : SpineFit ρ ((d.dsF t j' ψj)) ((xs.take d.nP).map (interp V ρ)) := by
    have h1 := ((spineFit_iff_of_sat_iff (by rw [G.hlenP ψ, List.length_take,
      hdsLen, Nat.min_self]) (G.hparamsC ψ) ρ _ (by rw [hpar.length_eq])).mp hpar)
    rw [List.take_of_length_le (Nat.le_of_eq hdsLen)] at h1
    rw [hds]; exact h1
  obtain ⟨restC, hfitC⟩ := teleFitPA_mkPisAV_of_spineFit
    (b := ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t j' ψj))
    (by rw [hds, hdsLen, hyl]) hspC
  rw [← hct] at hfitC
  refine ⟨restR', restC, hfitR', hfitC, ?_, heq⟩
  -- the index pin: the residual's index readings are the stored fit's
  have hD' := hD
  have hteleC := piTeleAV_mkPisAV (d.dsF t j' ψj)
    (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψj (d.esF t j' ψj))
  rw [hD.len ψj] at hteleC
  rw [hct] at hfitC
  have hrest := teleFitPA_rest_eq (d.nP + cA.2) hteleC (by rw [hyl, hnf0]; rfl) hfitC
  unfold ctorBodyAVI at hrest
  rw [instSeqAV_mkAppN] at hrest
  have hes : d.esF t j' ψj = d.esF t j' ψ := (hD.params ψj ψ hlv).2
  have hEssD : (d.Ess t ψ).getD j' [] = d.esF t j' ψ := essOfR_fixCtorDataList_getD G.hcj
  have hlenE : (d.esF t j' ψ).length
      = pp.toBlockShape.majorIdxAt j - pp.toBlockShape.rulePrefixAt j := by
    rw [hD.lenE ψ, ← G.hlenIds ψ, ← hsp'.length_eq, List.length_map, List.length_drop, hxl]
  have hcarLen : ((paramBvars d.nP cA.2 ++ d.esF t j' ψj).map
      (Term.instSeq (xs.take d.nP) (d.nP + cA.2 - 1))).length
      = d.nP + (d.esF t j' ψ).length := by
    rw [List.length_map, List.length_append, paramBvars, List.length_map, List.length_range, hes]
  refine ⟨_, _, hrest, Or.inr (by rw [hcarLen, hlenE]), fun q hq => ?_⟩
  have hq' : q < (d.esF t j' ψ).length := by rw [hlenE]; exact hq
  have hres := genMem_residual G (ys := xs.take d.nP) hlv (by rw [hyl, hnf0]; rfl)
    (by rw [hct]; exact hfitC) hrest hcarLen q hq'
  rw [hres]
  -- the stored fit's index clause, at no fields
  have hIdxOk := G.hM.idxOk ψ _ (d.satOfSpine hpar) t G.hmN
  have hql : q < (d.IdsM t ψ).length := by
    rw [← hsp'.length_eq, List.length_map, List.length_drop, hxl]; omega
  have hstep := hfit'.2.2 q hql
  rw [hEssD, consList_nil] at hstep
  rw [hstep, BlockData.tup, projS_tupW hIdxOk hsp' hql, getD_map_pt (by
    rw [List.length_drop, hxl]; omega), getD_drop']

set_option maxHeartbeats 4000000 in
/-- **(T) at a member class** (the ι step's case 2): above `Prop` at the
recursor's levels, a fired constructor application that is not the
point is also the same constructor applied to the recursor's own
parameters and the same fields, at the comparand levels `ψl`.  Its
value is the injection of its fields at its own frame `ψj`, which is
not `Prop` (`genMemCtor_pt`); injections read no level above `Prop`
(`LfpClause.injFrame`), and the major lies in the member's carrier at
the recursor's parameters (`genMem_major`), whose elements are
injections of spines hole-fitting there (`blockCarrier_case`); by
injectivity (`mkInj`) the fields are that spine, so they fit at the
recursor's parameter frame. -/
theorem genMem_T
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt j)
    {ψ ψj ψl : Name → Nat} (hlvl : ∀ q ∈ cA.1.levelParams, ψl q = ψ q) (hw : d.w ψ ≠ 0)
    {ρ : Nat → V} {xs ys : List Term} {restR restC : Term}
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j) (hyl : ys.length = pp.nP + cA.2)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    (hfitC : TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) ys restC)
    (hne : interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys) ≠ pt) :
    ∃ restC',
      TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψl)
        (xs.take pp.nP ++ ys.drop pp.nP) restC' ∧
      interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψl) (xs.take pp.nP ++ ys.drop pp.nP))
        = interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys) := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hrPle := blockRecHrPle (p := pp) h hj
  have hD := G.hcf.2.2
  have hys : ys.length = d.nP + cA.2 := by rw [hyl, G.hdnP]
  have hnP' : d.nP ≤ pp.toBlockShape.rulePrefixAt j := by rw [G.hdnP]; exact hnP
  rw [← G.hdnP]
  -- the fired application at its own frame: its value is an injection, not `Prop`
  obtain ⟨hqsj, hfqj⟩ := blockRuleCtorFit_run (ψ := ψj) G.hcj G.hcf (fun _ _ => rfl)
    (G.hlenP ψj) (G.hparamsC ψj) hys (G.hctorRead ψj) hfitC
  have hvalj := blockCtorMajor_value G.hM G.hcj G.hcf.1 G.hmN (fun _ _ => rfl) hqsj hfqj
  have hwj : d.w ψj ≠ 0 := fun h0 => hne (genMemCtor_pt G h0 ρ ys)
  -- the major, in the member's carrier at the recursor's parameters
  obtain ⟨hpar, hsp', hmaj⟩ := genMem_major h R hS G hr hm ψ hxl hfitR
  have hpsV : ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)).take d.nP
      = (xs.take d.nP).map (interp V ρ) := by
    rw [← List.map_take, List.take_take, Nat.min_eq_left hnP']
  rw [hpsV] at hpar hsp' hmaj
  have ht : d.tup ψ t ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))
      ∈ˢ d.idx ψ (consList ((xs.take d.nP).map (interp V ρ)) ρ) t := tupW_mem hsp'
  obtain ⟨j', fs', hfit', heq⟩ := blockCarrier_case G.hM (d.satOfSpine hpar) G.hmN ht hmaj
  -- one injection: the same constructor, the same fields
  have hinj : d.inj ψj t i ((ys.drop d.nP).map (interp V ρ))
      = d.inj ψ t i ((ys.drop d.nP).map (interp V ρ)) :=
    (mpC.lfp_ok _ G.hlfp).1.injFrame ψj ψ hwj hw t i _
  have hFssD : (d.Fss t ψ).getD i [] = ((d.dsF t i ψ).drop d.nP) :=
    fssOfR_fixCtorDataList_getD G.hcj
  obtain ⟨rfl, rfl⟩ := G.hM.mkInj ψ hw t G.hmN i ((ys.drop d.nP).map (interp V ρ)) j' fs'
    G.hjl hfit'.1
    (by rw [hFssD, List.length_drop, hD.len ψ, List.length_map, List.length_drop, hys])
    hfit'.length_eq (by rw [← hinj, ← hvalj]; exact heq)
  -- the witness: the recursor's parameters, then the same fields
  have hxlP : d.nP ≤ xs.length := by rw [hxl]; omega
  have hpl : (xs.take d.nP).length = d.nP := by rw [List.length_take]; omega
  have htk : (xs.take d.nP ++ ys.drop d.nP).take d.nP = xs.take d.nP := List.take_left' hpl
  have hdr : (xs.take d.nP ++ ys.drop d.nP).drop d.nP = ys.drop d.nP := List.drop_left' hpl
  have hval := blockCtorMajor_value (ys := xs.take d.nP ++ ys.drop d.nP) G.hM G.hcj G.hcf.1
    G.hmN hlvl (by rw [htk]; exact hpar) (by rw [htk, hdr]; exact hfit'.2.1)
  rw [hdr] at hval
  have hfitW : ∃ restC', TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψl)
      (xs.take d.nP ++ ys.drop d.nP) restC' := by
    have hct : blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψl
        = mkPisAV (d.dsF t i ψl)
            (ctorBodyAVI mpC.base2 (d.memberName t) d.nP cA.2 ψl (d.esF t i ψl)) :=
      Option.some.inj ((G.hctorRead ψl).symm.trans (hD.read ψl))
    have hds : d.dsF t i ψl = d.dsF t i ψ := (hD.params ψl ψ hlvl).1
    have hlenD : ((d.dsF t i ψ).take d.nP).length = d.nP := by
      rw [List.length_take, hD.len ψ]; omega
    have hpC := (spineFit_iff_of_sat_iff (by rw [G.hlenP ψ, hlenD]) (G.hparamsC ψ) ρ _
      (by rw [hpar.length_eq])).mp hpar
    have hfC : SpineFit (consList ((xs.take d.nP).map (interp V ρ)) ρ)
        ((d.dsF t i ψ).drop d.nP) ((ys.drop d.nP).map (interp V ρ)) := by
      rw [← hFssD]; exact hfit'.2.1
    have hsp : SpineFit ρ (d.dsF t i ψl)
        ((xs.take d.nP ++ ys.drop d.nP).map (interp V ρ)) := by
      rw [hds, List.map_append, ← List.take_append_drop d.nP (d.dsF t i ψ)]
      exact SpineFit.append hpC hfC
    rw [hct]
    exact teleFitPA_mkPisAV_of_spineFit (by
      rw [hds, hD.len ψ, List.length_append, hpl, List.length_drop, hys]; omega) hsp
  obtain ⟨restC', hfitW⟩ := hfitW
  exact ⟨restC', hfitW, by rw [hval, ← hinj, ← hvalj]⟩

set_option maxHeartbeats 8000000 in
/-- **The case split's facts at a member rule**, at the recursors' cons:
the reading crossings (`blockRuleTVa_run`, `blockRecDenote_cross`), then
the base-frame facts above. -/
theorem genMemExtra
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out)
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {isRec : Bool} {cvT : ConstantVal} {j i t : Nat} {cA : ConstantVal × Nat}
    (G : GenMemAt mpC d pp out isRec cvT j i t cA)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hm : (tgtMajor out j).member = some t)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt j)
    (hctorCB : ConstsBound envC cA.1.type)
    {Rr : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → Bool × List ConLeche.RecRule}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List Term}
    {m₃ : EnvModel V (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC (tgtRs out) s eqs) (φ : Name → Nat)
    {rl : ConLeche.RecRule} (hct : ConLeche.RecRule.ctor rl = cA.1.name)
    (hnf : ConLeche.RecRule.nfields rl = cA.2)
    (hfire : ConLeche.RecRule.fire rl = .plain) :
    RecRuleKWit m₃ φ r.1.name r.1 (pp.toBlockShape.majorIdxAt j) (pp.toBlockShape.rulePrefixAt j)
      (ConLeche.recKExpected pp.toBlockShape (tgtMajor out j)) rl ∧
    RecRuleExtraNK m₃ φ r.1.name r.1 (pp.toBlockShape.majorIdxAt j)
      (pp.toBlockShape.rulePrefixAt j) (ConLeche.recKExpected pp.toBlockShape (tgtMajor out j)) rl := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hrPle := blockRecHrPle (p := pp) h hj
  have hcv := recStage_cvFacts h
  have hkeep := find?_consBlockRecsR_keep (R := Rr) (q := pp.toBlockShape)
    (fun r' hr' => (hcv r' hr').1)
  have hfind3 : (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC).find?
      (ConLeche.RecRule.ctor rl) = some (.ctorInfo cA.1 d.nP cA.2) := by
    rw [hct]; exact hkeep _ _ G.hcf.1
  have hstored : m₃.acval (ConLeche.RecRule.ctor rl) = mpC.base2.acval cA.1.name := by
    rw [hct]; exact blockRecAcv_stored h hac (by rw [G.hcf.1]; rfl)
  have hnp : d.nP = pp.nP := G.hdnP
  -- the constructor's reading at the cons
  have hTVjaOf : ∀ usj : List Level,
      denote m₃.acval (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) φ 0
        (cA.1.type.instantiateLevelParams cA.1.levelParams usj)
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i
          (Level.substFn φ cA.1.levelParams usj)) := by
    intro usj
    rw [denote_instLevels m₃.acval_params φ]
    exact blockRecDenote_cross h hac _ 0 cA.1.type hctorCB (G.hctorRead _)
  refine ⟨fun hk1 => ?_, ?_⟩
  · ------------------------------------------------------------------ K
    -- the flag says the member has one constructor, without fields
    obtain ⟨c, hcs, hnf0⟩ := ConLeche.recKExpected_member hm hk1
    obtain rfl : cA = c := by
      have hj' := G.hcj
      rw [G.hctM, hcs] at hj'
      cases hi' : i with
      | zero => rw [hi'] at hj'; exact (Option.some.inj hj').symm
      | succ n => rw [hi'] at hj'; simp at hj'
    have hone : (d.ctorsM t).length = 1 := by rw [G.hctM, hcs]; rfl
    refine ⟨by rw [hnf, hnf0], fun us hus TVa hTVa ρ xs a restR hxl hfit => ?_⟩
    obtain rfl := blockRuleTVa_run mpC h hac hr φ us hTVa
    have hlv := blockRuleLevelAgree (φ := φ) (lps := cA.1.levelParams) (lpsR := r.1.levelParams)
      (us := us) (usj := (ConLeche.recFireComparands rl d.nP r.1.levelParams us cA.1.levelParams []
        (pp.toBlockShape.rulePrefixAt j)).1) (rP := pp.toBlockShape.rulePrefixAt j) hfire rfl
    obtain ⟨restR', restC, hfitR', hfitC, hpin, hval⟩ :=
      genMem_K h R hS G hr hm hnP hone hnf0 hlv ρ xs a restR hxl hfit
    refine Or.inr ⟨cA.1, d.nP, cA.2,
      (ConLeche.recFireComparands rl d.nP r.1.levelParams us cA.1.levelParams []
        (pp.toBlockShape.rulePrefixAt j)).1, xs.take pp.nP, _, restR', restC,
      hfind3, ?_, ?_, rfl,
      fun _ => by rw [hnp]; exact hpin, hTVjaOf _, by rw [hstored]; exact hfitR',
      hfitC, by rw [hstored]; exact hval, fun hxs y hy => hxs y (List.mem_of_mem_take hy)⟩
    · rw [List.length_take, hnp, hnf, hnf0, hxl]; omega
    · rw [ConLeche.recFireComparands_plain hfire, List.length_map]
  · ------------------------------------------------------------------ NK
    intro us hus TVa hTVa cvj cnP cnF hfind
    rw [hfind3] at hfind
    obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cvj ∧ d.nP = cnP ∧ cA.2 = cnF := by
      injection hfind with h'; injection h' with a b c; exact ⟨a, b, c⟩
    obtain ⟨cbs, es, hres, -⟩ := G.hcf.2.2.resid
    obtain rfl := blockRuleTVa_run mpC h hac hr φ us hTVa
    rw [hstored]
    refine ⟨by rw [hnf, hres]; rfl, fun _ => ⟨fun hlic ρ xs a restR hxl hfit => ?_, ?_,
      fun usj husj hψ TVja hTVja => ?_⟩⟩
    · -- (S), at the comparand levels
      have hlv := blockRuleLevelAgree (φ := φ) (lps := cA.1.levelParams)
        (lpsR := r.1.levelParams) (us := us)
        (usj := (ConLeche.recFireComparands rl d.nP r.1.levelParams us cA.1.levelParams []
          (pp.toBlockShape.rulePrefixAt j)).1) (rP := pp.toBlockShape.rulePrefixAt j) hfire rfl
      exact genMem_S h R hS G hr hm hlv (hkeep _ _ G.hcaps) hlic ρ xs a restR hxl hfit
    · -- (T), at the comparand levels: the recursor's parameters, the same fields
      intro hlic usj _ TVja hTVja ρ xs ys restR restC hxl hyl hfitR hfitC hxsW hysW hne
      rw [hTVjaOf] at hTVja
      obtain rfl := Option.some.inj hTVja
      have hlv := blockRuleLevelAgree (φ := φ) (lps := cA.1.levelParams)
        (lpsR := r.1.levelParams) (us := us)
        (usj := (ConLeche.recFireComparands rl d.nP r.1.levelParams us cA.1.levelParams []
          (pp.toBlockShape.rulePrefixAt j)).1) (rP := pp.toBlockShape.rulePrefixAt j) hfire rfl
      rw [hnp, hnf] at hyl
      obtain ⟨restC', hfitC', hval⟩ := genMem_T h R hS G hr hm hnP hlv
        (genMem_w_of_lic G hlv (hkeep _ _ G.hcaps) hlic) hxl hyl hfitR hfitC hne
      have hxlP : pp.nP ≤ xs.length := by rw [hxl]; have := hrPle; omega
      have hpl : (xs.take pp.nP).length = pp.nP := by rw [List.length_take]; omega
      refine ⟨_, xs.take pp.nP ++ ys.drop pp.nP, _, restC', ?_, rfl, hTVjaOf _, ?_,
        by rw [hnp]; exact List.drop_left' hpl, ?_, hfitC', hval⟩
      · rw [ConLeche.recFireComparands_plain hfire, List.length_map]
      · rw [List.length_append, hpl, List.length_drop, hyl]; omega
      · intro y hy
        rcases List.mem_append.mp hy with hy | hy
        · exact hxsW y (List.mem_of_mem_take hy)
        · exact hysW y (List.mem_of_mem_drop hy)
    rw [hTVjaOf] at hTVja
    obtain rfl := Option.some.inj hTVja
    have hlv := blockRuleLevelAgree hfire hψ
    refine ⟨fun ρ xs a restR hxl hfit hapt ys restC _ _ _ =>
      genMem_P h R hS G hr hm hlv ρ xs a restR hxl hfit hapt ys, ?_⟩
    · intro ρ xs ys restR restC hxl hyl hfitR hfitC _ _ hcP _ hpinC hpt
      rw [hnp] at hpinC hyl ⊢
      rw [hnf] at hyl
      refine genMem_U h R hS G hr hm hnP hlv hxl hyl hfitR hfitC
        (fun q hq h1 h2 => hcP hfire hpt q (by rw [hnp]; exact hq)
          (by have := G.hdnP; omega) h1 h2) (hpinC hpt)

end Member

/-! ## 2. An outside class's facts -/

section Outside

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

/-- **The constructor's arity at a class**: its stored type binds the
class's parameters and its fields syntactically (`LfpOwn.ctorConcl`). -/
theorem genCls_arity (hcov : LfpCover mpC []) {j : Nat} {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI) {i : Nat} {cA : ConstantVal × Nat}
    (hcAM : (tgtMajor out j).ctors[i]? = some cA) :
    (cA.1.type.stripPis ((tgtMajor out j).nPc + cA.2)).isSome = true := by
  obtain ⟨hiD, hfc0, -, -⟩ := Rd.hctor i cA hcAM
  obtain ⟨cv8, nPc8, nF8, hf8, bs, args, hstrip, -⟩ :=
    (hcov.own _ Rd.hD).ctorConcl _ Rd.hmm i hiD
  rw [hfc0] at hf8
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv8 ∧ (tgtMajor out j).ds.length = nPc8 ∧ cA.2 = nF8 := by
    injection hf8 with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  rw [Rd.hnpc, hstrip]; rfl

set_option maxHeartbeats 8000000 in
/-- **(U)'s `.nested` pins at an outside class** (L7's route; read
where the fired application is the point, case 3): the constructor's parameters fit its own parameter
binders, and so do the pins' values, which are the class's parameters at
the prefix (`genOutPinVal`) and fit the container's parameter telescope
there, whose satisfaction carries to the constructor's binders
(`genOutCtorFit`); the binders are a closed telescope of types, so the
conditional comparison is an equation (`spineFit_eq_of_cond`). -/
theorem genOut_pins
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt j)
    {lvls : List Level} {pins : List Expr}
    (hf : ConLeche.tgtFireOf pp.toBlockShape (ConLeche.tgtMajorsOf out) j r
      = .nested lvls pins)
    {φ : Name → Nat} {us usj : List Level}
    (hlv : ∀ p ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj p
      = Level.substFn (Level.substFn φ r.1.levelParams us) cvI.levelParams (tgtMajor out j).lvls p)
    {ρ : Nat → V} {xs ys : List Term} {maj restR restC : Term}
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out)
      (Level.substFn φ r.1.levelParams us) j) (xs ++ [maj]) restR)
    (hfitC : TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i
      (Level.substFn φ cA.1.levelParams usj)) ys restC)
    (hyl : ys.length = (tgtMajor out j).nPc + cA.2)
    (hN : ∀ q, q < (tgtMajor out j).nPc → ∀ vpa : Term,
      denote mpC.base2.acval envC φ (pp.toBlockShape.rulePrefixAt j)
        (openRev 0 (pp.toBlockShape.rulePrefixAt j)
          ((pins.getD q default).instantiateLevelParams r.1.levelParams us)) = some vpa →
      interp V ρ (ys.getD q default) ≠ pt →
      interp V ρ (Term.instRevChain (xs.take (pp.toBlockShape.rulePrefixAt j)) vpa) ≠ pt →
      interp V ρ (ys.getD q default)
        = interp V ρ (Term.instRevChain (xs.take (pp.toBlockShape.rulePrefixAt j)) vpa)) :
    ∀ q, q < (tgtMajor out j).nPc → ∀ vpa : Term,
      denote mpC.base2.acval envC φ (pp.toBlockShape.rulePrefixAt j)
        (openRev 0 (pp.toBlockShape.rulePrefixAt j)
          ((pins.getD q default).instantiateLevelParams r.1.levelParams us)) = some vpa →
      interp V ρ (ys.getD q default)
        = interp V ρ (Term.instRevChain (xs.take (pp.toBlockShape.rulePrefixAt j)) vpa) := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hi : i < blockRecNCt (tgtRs out) j :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hcA).1 (blockRecNCt_ge hr)
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by rw [← tgtRs_ctors hr]; exact hcA
  have hrPle : pp.toBlockShape.rulePrefixAt j ≤ pp.toBlockShape.majorIdxAt j :=
    blockRecHrPle (p := pp) h hj
  obtain ⟨-, hpinV⟩ := genOutPinVal R h hr Rd hf φ us
  generalize hψe : Level.substFn φ r.1.levelParams us = ψ at hfitR hlv hpinV
  obtain ⟨hpref, -, hxvl, -⟩ := genRow3_frame h hr ψ hxl hfitR
  obtain ⟨T0, pps, b0, hcons, hlpsI, hT0, hT0E, hplen, hT0wd, hT0cl, -, hTFall⟩ :=
    genOutCtorFit R hg hcov hj hi Rd hMo hnP ψ ρ hpref hcAM
  obtain ⟨ab, body, -, -, hcrR⟩ := genCls_openCrest R hg hj hi Rd hnP ψ hcAM
  have hTF := hTFall _ hcrR
  have hwfC := mpC.base2.wf.consts _ hcons
  have hctorTy : blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i
      (Level.substFn φ cA.1.levelParams usj) = T0 := by
    have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
      rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
    rw [blockRecCtorTy, hsel, denote_params_ext mpC.base2 hlv 0 cA.1.type hwfC.2.1, hT0]
    rfl
  rw [hctorTy, hT0E] at hfitC
  rw [hT0E] at hTF hT0cl
  have hdl : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length
      = (tgtMajor out j).nPc :=
    (DenoteSpine.length_eq (Rd.hdsa ψ)).symm.trans Rd.hnpc.symm
  have hplen' : pps.length = (tgtMajor out j).nPc := by rw [hplen, Rd.hnpc]
  -- the pins' values, at the base frame
  have hP1 := spineFit_of_teleFitPA (by rw [hdl, hplen']) hTF
  have hbelow := (bvarsBelow_mkPisAV_inv hT0cl).1
  have hP0 : SpineFit ρ (pps)
      ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
        (interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ))) :=
    spineFit_congr_below hbelow (fun i hi => absurd hi (Nat.not_lt_zero i)) hP1
  -- the constructor's parameters
  obtain ⟨mid, hmid⟩ := hfitC.take (tgtMajor out j).nPc
  have hY0 : SpineFit ρ (pps) ((ys.take (tgtMajor out j).nPc).map (interp V ρ)) :=
    spineFit_of_teleFitPA (by rw [List.length_take, hyl, hplen']; omega) hmid
  have hTy : SpineTy ρ (pps) := spineTy_of_wellDenoted_mkPisAV (by
    have := hT0wd ρ; rw [hT0E] at this; exact this)
  have hlenPs : (pps).length = (tgtMajor out j).nPc := by
    rw [hplen']
  -- the pins' chains are their readings
  have hchain : ∀ q, q < (tgtMajor out j).nPc → ∀ vpa : Term,
      denote mpC.base2.acval envC φ (pp.toBlockShape.rulePrefixAt j)
        (openRev 0 (pp.toBlockShape.rulePrefixAt j)
          ((pins.getD q default).instantiateLevelParams r.1.levelParams us)) = some vpa →
      interp V ρ (Term.instRevChain (xs.take (pp.toBlockShape.rulePrefixAt j)) vpa)
        = interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ)
            ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).getD q default) := by
    intro q hq vpa hvpa
    obtain ⟨vpa', hvpa', hval⟩ := hpinV q hq
    rw [hvpa] at hvpa'
    obtain rfl := Option.some.inj hvpa'
    exact hval ρ _ (by rw [List.length_take]; omega)
  have heq : (ys.take (tgtMajor out j).nPc).map (interp V ρ)
      = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
        (interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ)) := by
    refine spineFit_eq_of_cond_getD hTy hY0 hP0 fun q hq h1 h2 => ?_
    rw [hlenPs] at hq
    obtain ⟨vpa, hvpa, -⟩ := hpinV q hq
    have hqy : q < (ys.take (tgtMajor out j).nPc).length := by
      rw [List.length_take, hyl]; omega
    have hqd : q < (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length := by
      rw [hdl]; exact hq
    rw [getD_map_pt hqy, getD_take' hq] at h1 ⊢
    rw [getD_map_pt hqd] at h2 ⊢
    rw [← hchain q hq vpa hvpa] at h2 ⊢
    exact hN q hq vpa hvpa h1 h2
  intro q hq vpa hvpa
  have hqy : q < (ys.take (tgtMajor out j).nPc).length := by
    rw [List.length_take, hyl]; omega
  have hqd : q < (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length := by
    rw [hdl]; exact hq
  have hl := congrArg (fun l => l.getD q pt) heq
  rw [getD_map_pt hqy, getD_take' hq, getD_map_pt hqd] at hl
  rw [hl, hchain q hq vpa hvpa]

set_option maxHeartbeats 4000000 in
/-- **The major lies in an outside class's carrier** at the class's
parameter frame (the pins' readings at the prefix) and the recursor's
index tuple (`genRows3_out`'s class step). -/
theorem genOut_major
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    (ψ : Name → Nat) {ρ : Nat → V} {xs : List Term} {maj restR : Term}
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [maj]) restR) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)
      ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ∧
    Sat V ((tgtClsD d Dc out j).params (tgtClsψ cvc out ψ j)).reverse
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j)
        (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ)) ∧
    SpineFit (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j)
        (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ))
      ((tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j) (tgtClsψ cvc out ψ j))
      ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ∧
    interp V ρ maj ∈ˢ app ((tgtClsD d Dc out j).carrier (tgtClsψ cvc out ψ j)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j)
          (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ))
        (tgtClsM mc pp.toBlockShape out j))
      (tupW ((tgtClsD d Dc out j).u (tgtClsM mc pp.toBlockShape out j) (tgtClsψ cvc out ψ j))
        ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))) := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨hpref, hws, hxvl, hisl⟩ := genRow3_frame h hr ψ hxl hfitR
  obtain ⟨hTin, hmajIn, hisT⟩ := hS ψ ρ j hj _ _ _ hxvl hisl hws
  have hG := (Rd.hG ψ ρ _).mpr hpref
  have hFr := Rd.hfr ψ ρ _ hxvl
  have hIs : tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ
      ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) j
      = (tgtClsD d Dc out j).idx (tgtClsψ cvc out ψ j)
          (tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ
            ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) j)
          (tgtClsM mc pp.toBlockShape out j) := by
    unfold tgtClsIs; rw [ite_eq_left hG]
  rw [hIs, hFr] at hTin
  have hsatK := Rd.hsat ψ ρ _ hpref
  obtain ⟨hC, -⟩ := mpC.lfp_ok _ Rd.hD
  have hmN : tgtClsM mc pp.toBlockShape out j < (tgtClsD d Dc out j).N :=
    Nat.lt_of_lt_of_le Rd.hmm hC.kN
  obtain ⟨is', hsp', hTe⟩ := mem_idxSet_elim hTin
  have hIok := hC.idxOk _ _ hsatK _ hmN
  have hl' : is'.length = tgtClsNIdx d pp.toBlockShape out j := by
    rw [hsp'.length_eq, Rd.hidsLen, Rd.hnIdx]
  unfold tgtClsTup tgtClsU at hisT hTe hmajIn
  rw [hTe, ← hl', hsp'.length_eq, isOfW_tupW hIok hsp'] at hisT
  subst hisT
  refine ⟨hpref, hsatK, hsp', ?_⟩
  rw [hTe] at hmajIn
  unfold tgtClsCr at hmajIn
  rw [hFr] at hmajIn
  exact hmajIn

/-- **Above `Prop` an outside class's carrier holds no point.** -/
theorem genOut_ne_pt {j : Nat} {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {ψc : Name → Nat} {ρp : Nat → V} {is : List V} {a : V}
    (hsat : Sat V ((tgtClsD d Dc out j).params ψc).reverse ρp)
    (hsp : SpineFit ρp ((tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j) ψc) is)
    (hmaj : a ∈ˢ app ((tgtClsD d Dc out j).carrier ψc ρp (tgtClsM mc pp.toBlockShape out j))
      (tupW ((tgtClsD d Dc out j).u (tgtClsM mc pp.toBlockShape out j) ψc) is))
    (hw : (tgtClsD d Dc out j).w ψc ≠ 0) : a ≠ pt := by
  obtain ⟨hC, -⟩ := mpC.lfp_ok _ Rd.hD
  have hmN : tgtClsM mc pp.toBlockShape out j < (tgtClsD d Dc out j).N :=
    Nat.lt_of_lt_of_le Rd.hmm hC.kN
  have ht : tupW ((tgtClsD d Dc out j).u (tgtClsM mc pp.toBlockShape out j) ψc) is
      ∈ˢ (tgtClsD d Dc out j).idx ψc ρp (tgtClsM mc pp.toBlockShape out j) := tupW_mem hsp
  obtain ⟨j', fs', -, heq⟩ := hC.carrier_case hsat hmN ht hmaj
  rw [heq]
  exact hC.injNePt ψc hw _ j' fs'

/-- **An outside class's capability record**: the class's member is the
family the constructor concludes in, and its stored capabilities are
sound (`LfpCaps`). -/
theorem genOut_caps {j : Nat} {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {i : Nat} {cA : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some cA) :
    ∃ caps, envC.find? (tgtMajor out j).ind = some (.indInfo cvI caps) ∧
      (∀ ψ : Name → Nat, (tgtClsD d Dc out j).w ψ = 0 → caps.sortZ.holds ψ = true) ∧
      ∃ (bs : List Expr) (es : List Expr),
        cA.1.type.stripPis ((tgtMajor out j).nPc + cA.2)
          = some (bs, Expr.mkAppN (.const (tgtMajor out j).ind (cA.1.levelParams.map .param))
              (ConLeche.structPsAt cA.2 (tgtMajor out j).nPc ++ es)) := by
  obtain ⟨hiD, hfc0, -, -⟩ := Rd.hctor i cA hcAM
  obtain ⟨-, -, -, -, hcK, hcC⟩ := mpC.lfp_ok _ Rd.hD
  obtain ⟨cv, caps, hf, hz⟩ := hcK _ Rd.hmm
  rw [Rd.hmem] at hf
  obtain ⟨caps₀, hf₀⟩ := Rd.hfind
  rw [hf₀] at hf
  obtain ⟨rfl, rfl⟩ : cvI = cv ∧ caps₀ = caps := by
    injection hf with h'; injection h' with a b; exact ⟨a, b⟩
  obtain ⟨cv', nPc, nF, hf', bs, es, hst⟩ := hcC _ Rd.hmm i hiD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out j).ds.length = nPc ∧ cA.2 = nF := by
    injection hf' with h'; injection h' with a b c; exact ⟨a, b, c⟩
  refine ⟨caps₀, hf₀, hz, bs, es, ?_⟩
  rw [Rd.hnpc, hst, Rd.hmem]

/-- **(S) at an outside class**: the case split reads the container's
recorded sort zero-ness (`LfpCaps`), which fails at the constructor's
levels, so the class's sort is not zero at the recursor's, and the
carrier holds no point. -/
theorem genOut_S {j : Nat} {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {i : Nat} {cA : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some cA)
    {f : Name → Option ConstantInfo}
    (hf : ∀ caps, envC.find? (tgtMajor out j).ind = some (.indInfo cvI caps) →
      f (tgtMajor out j).ind = some (.indInfo cvI caps))
    {φ : Name → Nat} {usj : List Level} {ψc : Name → Nat}
    (hlv : ∀ p ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj p = ψc p)
    (hlic : ConLeche.iotaCtorNeverProp f cA.1 usj = true) :
    (tgtClsD d Dc out j).w ψc ≠ 0 := by
  obtain ⟨-, -, hlpC, -⟩ := Rd.hctor i cA hcAM
  obtain ⟨caps, hfc, hz, bs, es, hst⟩ := genOut_caps Rd hcAM
  obtain ⟨T, us₀, cvT, caps', hhead, hfT, -, hnz⟩ := iotaCtorNeverProp_inv hlic
  rw [piResult_getAppFn_of_stripPis _ hst] at hhead
  obtain ⟨rfl, -⟩ := ConLeche.Expr.const.inj hhead
  rw [hf caps hfc] at hfT
  obtain ⟨rfl, rfl⟩ : cvI = cvT ∧ caps = caps' := by
    injection hfT with h'; injection h' with a b; exact ⟨a, b⟩
  have hfalse := holds_false_of_isNever hnz φ
  have hne : (tgtClsD d Dc out j).w (Level.substFn φ cvI.levelParams usj) ≠ 0 :=
    fun h0 => by rw [hz _ h0] at hfalse; exact nomatch hfalse
  obtain ⟨-, -, hrd, -⟩ := mpC.lfp_ok _ Rd.hD
  have hfm : envC.find? ((tgtClsD d Dc out j).member (tgtClsM mc pp.toBlockShape out j))
      = some (.indInfo cvI caps) := by rw [Rd.hmem]; exact hfc
  rw [lfpW_congr mpC Rd.hD Rd.hmm hfm (ψ₂ := ψc) (fun q hq => by
    rw [← hlpC] at hq ⊢; exact hlv q hq)] at hne
  exact hne

/-- A closed leaf is fixed by every instantiation sequence. -/
theorem instSeq_acval {env : Env} (m : EnvModel V env) (n : Name) (ψ : Name → Nat) :
    ∀ (ws : List Term) (t : Nat),
      Term.instSeq ws t (m.acval n ψ) = m.acval n ψ
  | [], _ => rfl
  | w :: ws, t => by
    show Term.instSeq ws (t - 1) ((m.acval n ψ).inst w t) = _
    rw [acval_inst_self, instSeq_acval m n ψ ws (t - 1)]

/-- **An outside class's constructor residual**: the fit of the
constructor's type at a full spine leaves the container at the spine's
parameters and the constructor's index readings (`LfpCaps`'s shape,
read). -/
theorem genOut_residual (hcov : LfpCover mpC []) {j : Nat} {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {i : Nat} {cA : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some cA)
    {ψj : Name → Nat} {TVja : Term}
    (hread : denote mpC.base2.acval envC ψj 0 cA.1.type = some TVja)
    {ρ : Nat → V} {ys : List Term} {restC : Term}
    (hys : ys.length = (tgtMajor out j).nPc + cA.2)
    (hfitC : TeleFitPA V ρ TVja ys restC) :
    ∃ Es : List Term,
      restC = Term.mkAppN (mpC.base2.acval (tgtMajor out j).ind ψj)
        ((paramBvars (tgtMajor out j).nPc cA.2 ++ Es).map
          (Term.instSeq ys ((tgtMajor out j).nPc + cA.2 - 1))) ∧
      ∀ ψ : Name → Nat, (paramBvars (tgtMajor out j).nPc cA.2 ++ Es).length
        = (tgtMajor out j).nPc
          + ((tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j) ψ).length := by
  obtain ⟨hiD, hfc0, hlpC, -⟩ := Rd.hctor i cA hcAM
  obtain ⟨caps, hfc, -, bs, es, hst⟩ := genOut_caps Rd hcAM
  obtain ⟨pps, Es, hT, hplen, hEl⟩ := denote_ctorShape hfc
    (by show (cA.1.levelParams.map Level.param).length = cvI.levelParams.length
        rw [List.length_map, hlpC]) hst hread
  change TVja = mkPisAV pps (Term.mkAppN (mpC.base2.acval (tgtMajor out j).ind
    (Level.substFn ψj cvI.levelParams (cA.1.levelParams.map Level.param)))
    (paramBvars (tgtMajor out j).nPc cA.2 ++ Es)) at hT
  rw [show Level.substFn ψj cvI.levelParams (cA.1.levelParams.map Level.param) = ψj from by
    rw [← hlpC]; exact ConLeche.Level.substFn_param_self ψj _] at hT
  subst hT
  have htele := piTeleAV_mkPisAV pps (Term.mkAppN (mpC.base2.acval (tgtMajor out j).ind ψj)
    (paramBvars (tgtMajor out j).nPc cA.2 ++ Es))
  rw [hplen] at htele
  have hrest := teleFitPA_rest_eq ((tgtMajor out j).nPc + cA.2) htele hys hfitC
  rw [instSeqAV_mkAppN, instSeq_acval] at hrest
  refine ⟨Es, hrest, fun ψ => ?_⟩
  -- the stored shape's argument count (`LfpOwn.ctorConcl`)
  obtain ⟨cv8, nPc8, nF8, hf8, bs8, args, hstrip, hargs⟩ :=
    (hcov.own _ Rd.hD).ctorConcl _ Rd.hmm i hiD
  rw [hfc0] at hf8
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv8 ∧ (tgtMajor out j).ds.length = nPc8 ∧ cA.2 = nF8 := by
    injection hf8 with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  rw [← Rd.hnpc, hst, Rd.hmem] at hstrip
  have hb := congrArg (fun o => o.map (fun p => p.2.getAppArgs)) hstrip
  simp only [Option.map_some, Expr.getAppArgs_mkAppN] at hb
  have hb' := Option.some.inj hb
  simp only [Expr.getAppArgs, List.nil_append] at hb'
  have hl := hargs ψ
  rw [← hb', List.length_append] at hl
  rw [List.length_append, hEl]
  have hPs : (ConLeche.structPsAt cA.2 (tgtMajor out j).nPc).length = (tgtMajor out j).nPc := by
    simp [ConLeche.structPsAt]
  have hPB : (paramBvars (tgtMajor out j).nPc cA.2).length = (tgtMajor out j).nPc := by
    simp [paramBvars]
  rw [hPs] at hl
  rw [hPB]
  have := Rd.hnpc
  omega

set_option maxHeartbeats 4000000 in
/-- **A fitting graded constructor application lies in the container's
fibre at the residual's arguments**, which fit the container former's
telescope (its parameters, then its indices), and that fibre lies in the
container's universe. -/
theorem genOut_typed (hcov : LfpCover mpC []) {j : Nat} {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {i : Nat} {cA : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some cA)
    {ψj : Name → Nat} {TVja : Term}
    (hread : denote mpC.base2.acval envC ψj 0 cA.1.type = some TVja)
    {ρ : Nat → V} {ys : List Term} {restC : Term}
    (hys : ys.length = (tgtMajor out j).nPc + cA.2)
    (hfitC : TeleFitPA V ρ TVja ys restC) (hWD : ∀ y ∈ ys, WellDenoted V ρ y) :
    ∃ args : List Term,
      args.length = (tgtMajor out j).nPc
        + ((tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j) ψj).length ∧
      (∀ q, q < (tgtMajor out j).nPc →
        interp V ρ (args.getD q default) = interp V ρ (ys.getD q default)) ∧
      restC = Term.mkAppN (mpC.base2.acval (tgtMajor out j).ind ψj) args ∧
      interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys)
        ∈ˢ (args.map (interp V ρ)).foldl SetTheory.app
            (interp V ρ (mpC.base2.acval (tgtMajor out j).ind ψj)) ∧
      SpineFit ρ ((tgtClsD d Dc out j).pars (tgtClsM mc pp.toBlockShape out j) ψj
          ++ (tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j) ψj)
        (args.map (interp V ρ)) ∧
      (args.map (interp V ρ)).foldl SetTheory.app
          (interp V ρ (mpC.base2.acval (tgtMajor out j).ind ψj))
        ∈ˢ (univ ((tgtClsD d Dc out j).w ψj) : V) := by
  obtain ⟨hiD, hfc0, hlpC, -⟩ := Rd.hctor i cA hcAM
  obtain ⟨Es, hrest, hlenA⟩ := genOut_residual hcov Rd hcAM hread hys hfitC
  -- the constructor application lies in the residual
  have hname : cA.1.name = (tgtClsD d Dc out j).ctorName (tgtClsM mc pp.toBlockShape out j) i :=
    ConLeche.Env.find?_name hfc0
  have hcons := List.mem_of_find?_eq_some hfc0
  have hTV : WellDenoted V ρ TVja := (mpC.type_wellDenotedTy _ hcons ψj TVja hread ρ).1
  have hf : WellDenoted V ρ (mpC.base2.acval cA.1.name ψj) :=
    (mpC.base2.acval_wellDenoted _ ψj ρ)
  have hmem : interp V ρ (mpC.base2.acval cA.1.name ψj) ∈ˢ interp V ρ TVja := by
    exact mpC.mem_type _ hcons ψj TVja hread ρ
  obtain ⟨-, hin⟩ := Rules.mkAppN_of_fitA ys hTV hf hWD hmem hfitC
  have hokR := Rules.teleFitPA_rest_graded hfitC hTV hWD
  rw [hrest] at hin hokR
  rw [interp_mkAppN_foldl ρ _ (mpC.base2.acval (tgtMajor out j).ind ψj)] at hin
  -- the container former's telescope
  obtain ⟨-, -, hrd, ⟨-, hrdC⟩, -⟩ := mpC.lfp_ok _ Rd.hD
  obtain ⟨cv, caps, hfm, hab⟩ := hrd _ Rd.hmm
  rw [Rd.hmem] at hfm
  obtain ⟨caps₀, hf₀⟩ := Rd.hfind
  rw [hf₀] at hfm
  obtain ⟨rfl, rfl⟩ : cvI = cv ∧ caps₀ = caps := by
    injection hfm with h'; injection h' with a b; exact ⟨a, b⟩
  obtain ⟨ab, hta, hmap⟩ := hab ψj
  have hconsI := List.mem_of_find?_eq_some hf₀
  have hmemI : interp V ρ (mpC.base2.acval (tgtMajor out j).ind ψj)
      ∈ˢ interp V ρ (mkPisAV ab (.sort ((tgtClsD d Dc out j).w ψj))) := by
    have := mpC.mem_type _ hconsI ψj _ hta ρ
    have hn : (ConstantInfo.indInfo cvI caps₀).name = (tgtMajor out j).ind :=
      ConLeche.Env.find?_name hf₀
    rw [hn] at this
    exact this
  -- the parameter count
  obtain ⟨cv', nPc, nF, hf', -, -, -, A0, -, -, hrdA⟩ := hrdC _ Rd.hmm i hiD
  rw [hfc0] at hf'
  have hnPc : (tgtMajor out j).ds.length = nPc := by
    injection hf' with h; injection h
  have hPl := (hrdA ψj).1
  rw [← hnPc] at hPl
  have hparsL := (mpC.lfp_ok _ Rd.hD).1.parsLen _ Rd.hmm ψj
  have hlab : ((paramBvars (tgtMajor out j).nPc cA.2 ++ Es).map
      (Term.instSeq ys ((tgtMajor out j).nPc + cA.2 - 1))).length
      = ab.length := by
    rw [List.length_map, hlenA ψj, hmap, List.length_append, hparsL, hPl, Rd.hnpc]
  -- "not pt" source (1): the residual is the constructor type's codomain,
  -- a type
  have hne : interp V ρ (Term.mkAppN (mpC.base2.acval (tgtMajor out j).ind ψj)
      ((paramBvars (tgtMajor out j).nPc cA.2 ++ Es).map
        (Term.instSeq ys ((tgtMajor out j).nPc + cA.2 - 1)))) ≠ pt := by
    have hty := Rules.teleFitPA_rest_isTy hfitC
      (mpC.type_wellDenotedTy _ hcons ψj TVja hread ρ) hWD
    rw [hrest] at hty
    exact hty.ne_pt
  have hfit := spineFit_of_wellDenoted_mkAppN_pi hne hokR hmemI hlab
  rw [hmap] at hfit
  refine ⟨_, by rw [List.length_map, hlenA], fun q hq => ?_, hrest, hin, hfit, ?_⟩
  · have hPB : (paramBvars (tgtMajor out j).nPc cA.2).length = (tgtMajor out j).nPc := by
      simp [paramBvars]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_append_left (by rw [hPB]; exact hq)]
    have hel : (paramBvars (tgtMajor out j).nPc cA.2)[q]?
        = some (.bvar ((tgtMajor out j).nPc + cA.2 - 1 - q)) := by
      simp [paramBvars, List.getElem?_range hq]
    rw [hel, Option.map_some, Option.getD_some,
      show (tgtMajor out j).nPc + cA.2 - 1 = ys.length - 1 from by rw [hys], interp_instSeq]
    unfold chain
    rw [consN_eq_consList, interp_bvar,
      consList_getD_of_lt _ _ _ (by rw [List.length_map, hys]; omega), List.length_map, hys,
      show (tgtMajor out j).nPc + cA.2 - 1 - ((tgtMajor out j).nPc + cA.2 - 1 - q) = q from by
        omega, getD_map_pt (by rw [hys]; omega)]
  · have := foldl_app_mem_mkPisAV (by rw [← hmap] at hfit; exact hfit) hmemI
    rw [interp_sort] at this
    exact this

set_option maxHeartbeats 8000000 in
/-- **An outside class's constructor, at its OWN parameters and levels**
(task #342 S5b, S5c): at a graded spine fitting the constructor's stored
type read at any level valuation `ψc`, the application is the container's
injection of the spine's fields at `ψc`, which have the recorded
constructor's length.  The ι step compares the constructor's parameters
(and, outside case 3, its levels) with nothing, so the injection is read
at the spine's own parameters: they fit the container's parameter
telescope — the residual is a type, "not pt" source (1) (`genOut_typed`)
— so the key frame at the canonical parameters is their frame, the
fields fit the instantiated constructor's fields there (peeled off the
stored type's fit), and `instCtor_decode` reads the application.  The
container datum is parametric in its level valuation: the instantiation
is at the constructor's own level parameters. -/
theorem genOutCtorOwn (hcov : LfpCover mpC []) {j : Nat} {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {i : Nat} {cA : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some cA)
    (ψc : Name → Nat) {T0 : Term}
    (hT0 : denote mpC.base2.acval envC ψc 0 cA.1.type = some T0)
    (hT0cl : Term.bvarsBelow 0 T0)
    (hpc : Rules.PiChain ((tgtMajor out j).ds.length + cA.2) T0)
    {ρ : Nat → V} {ys : List Term} {restC : Term}
    (hys : ys.length = (tgtMajor out j).ds.length + cA.2)
    (hfitC : TeleFitPA V ρ T0 ys restC) (hWD : ∀ y ∈ ys, WellDenoted V ρ y) :
    ((ys.drop (tgtMajor out j).ds.length).map (interp V ρ)).length
        = ((tgtClsD d Dc out j).fields ψc (tgtClsM mc pp.toBlockShape out j) i).length ∧
      interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψc) ys)
        = (tgtClsD d Dc out j).inj ψc (tgtClsM mc pp.toBlockShape out j) i
            ((ys.drop (tgtMajor out j).ds.length).map (interp V ρ)) := by
  have hacl := mpC.base2.acval_closed
  obtain ⟨hiD, hfc0, hlpC, hlpsR⟩ := Rd.hctor i cA hcAM
  obtain ⟨hC, -, -, ⟨-, hrdC⟩, -⟩ := mpC.lfp_ok _ Rd.hD
  have hcons := List.mem_of_find?_eq_some hfc0
  have hwfC := mpC.base2.wf.consts _ hcons
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hname : cA.1.name = (tgtClsD d Dc out j).ctorName (tgtClsM mc pp.toBlockShape out j) i :=
    ConLeche.Env.find?_name hfc0
  -- the instantiation at the constructor's own level parameters
  have hself := ConLeche.Level.substFn_param_self ψc cvI.levelParams
  have hul : (cvI.levelParams.map Level.param).length = cvI.levelParams.length :=
    List.length_map _
  have hlenP : ((tgtClsD d Dc out j).params ψc).length = (tgtMajor out j).ds.length := by
    obtain ⟨cv', nPc, nF, hf', -, -, -, A0, -, -, hrdA⟩ := hrdC _ Rd.hmm i hiD
    rw [hfc0] at hf'
    have hnPc : (tgtMajor out j).ds.length = nPc := by
      injection hf' with h; injection h
    rw [(hrdA ψc).1, hnPc]
  -- the spine's parameters fit the container's parameter telescope ("not pt"
  -- source (1): the residual is a type)
  obtain ⟨args, hlenA, hparA, -, -, hfitA, -⟩ :=
    genOut_typed hcov Rd hcAM hT0 (by rw [Rd.hnpc]; exact hys) hfitC hWD
  rw [Rd.hnpc] at hparA hlenA
  generalize hn : (tgtMajor out j).ds.length = n at hys hfc0 hlenP hparA hlenA hpc ⊢
  obtain ⟨as₁, as₂, hasE, hfit1, -⟩ := spineFit_append_inv hfitA
  have hparsL : ((tgtClsD d Dc out j).pars (tgtClsM mc pp.toBlockShape out j) ψc).length = n := by
    rw [hC.parsLen _ Rd.hmm, hlenP]
  have has1L : as₁.length = n := by rw [hfit1.length_eq, hparsL]
  have has1 : as₁ = (ys.take n).map (interp V ρ) := by
    refine List.ext_getElem (by rw [has1L, List.length_map, List.length_take, hys]; omega)
      fun q h1 h2 => ?_
    have hq : q < n := by rw [has1L] at h1; exact h1
    have hA := congrArg (fun l => l.getD q pt) hasE
    rw [getD_map_pt (by rw [hlenA]; omega), getD_append_left' (by rw [has1L]; exact hq),
      hparA q hq] at hA
    rw [List.getElem_map, List.getElem_take]
    have e1 : as₁[q] = as₁.getD q pt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
    have e2 : ys[q]'(by omega) = ys.getD q default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    rw [e1, e2]
    exact hA.symm
  have hsat : Sat V ((tgtClsD d Dc out j).params ψc).reverse (consList as₁ ρ) := by
    have hs := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hfit1
    rw [List.append_nil] at hs
    exact hC.parsSatInv _ Rd.hmm _ _ hs
  -- the canonical parameters, read at the spine's own frame
  have hds : ∀ x ∈ canonParams n, Expr.WScoped n x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_canonParams hx
    exact ⟨by simp [Expr.WScoped, hk], rfl⟩
  obtain ⟨dsa, hdsa⟩ := Rules.DenoteSpine.exists_of_all (acval := mpC.base2.acval)
    (env := envC) (φ := ψc) (d := n) (canonParams n) fun x hx => by
      obtain ⟨k, -, rfl⟩ := mem_canonParams hx
      exact ⟨_, denote_fvar _ _ _ _⟩
  have hdl : dsa.length = n := by
    rw [← DenoteSpine.length_eq hdsa, canonParams_length]
  have hdsaV : dsa.map (interp V (consList as₁ ρ)) = as₁ := by
    refine List.ext_getElem (by rw [List.length_map, hdl, has1L]) fun q h1 h2 => ?_
    have hq : q < n := by rw [List.length_map, hdl] at h1; exact h1
    have hr := DenoteSpine.getD hdsa default q (by rw [canonParams_length]; exact hq)
    have hcq : (canonParams n).getD q default = .fvar q (.sort .zero) := by
      simp [canonParams, ConLeche.nestPhs, List.getD_eq_getElem?_getD, hq]
    rw [hcq, denote_fvar] at hr
    have e1 : dsa[q] = dsa.getD q default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have e2 : as₁[q] = as₁.getD q pt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
    rw [List.getElem_map, e1, ← Option.some.inj hr, interp_bvar,
      consList_getD_of_lt _ _ _ (by rw [has1L]; omega), has1L,
      show n - 1 - (n - 1 - q) = q by omega, e2]
  have hkey : keyFrame dsa n (consList as₁ ρ) = consList as₁ ρ := by
    unfold keyFrame
    rw [hdsaV]
    congr 1
    funext k
    rw [← has1L]
    exact consList_apply_add as₁ ρ k
  -- the instantiated constructor, at the canonical parameters
  have hlenP' : ((tgtClsD d Dc out j).params
      (Level.substFn ψc cvI.levelParams (cvI.levelParams.map Level.param))).length
      = (canonParams n).length := by rw [canonParams_length, hself]; exact hlenP
  have hfc' : envC.find? ((tgtClsD d Dc out j).ctorName (tgtClsM mc pp.toBlockShape out j) i)
      = some (.ctorInfo cA.1 (canonParams n).length cA.2) := by
    rw [canonParams_length]; exact hfc0
  obtain ⟨-, crest, ab, hcr, ⟨Tys, hlT, hTys, hEq⟩, hlab, hcrRead⟩ :=
    instCtor_read mpC Rd.hD hlpsR Rd.hnd hul hds hdsa hlenP' Rd.hmm hiD hfc'
  rw [ConLeche.instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨doms, crest'⟩, hinst, hcr'⟩ := Option.map_eq_some_iff.mp hcr
  obtain rfl : crest' = crest := hcr'
  have hTy : denote mpC.base2.acval envC ψc n
      (cA.1.type.instantiateLevelParams cA.1.levelParams (cvI.levelParams.map Level.param))
      = some T0 := by
    rw [denote_instLevels mpC.base2.acval_params ψc, hlpC, hself]
    exact denote_depth_of_closed hacl hCf
      (fun k => denote_liftN_eq_self mpC.base2.cval_closed hCf hCb hT0 1 k)
      hT0 _
  obtain ⟨restA, hrest, hpeel⟩ := Rules.denote_instPisAt_peel hacl
    (acval_inst_self mpC.base2) _ hinst
    (Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hCf))
    hds hTy hdsa
  have hrestE := hrest.symm.trans hcrRead
  -- the fields fit the instantiated constructor's fields at the spine's frame
  have h1 := Rules.teleFit_of_teleFitPA (by rw [hys]; exact hpc) hfitC
  obtain ⟨X', h2⟩ := teleFit_congr_frame' _ (n := 0) (ρ' := consList as₁ ρ) hT0cl
    (fun k hk => absurd hk (Nat.not_lt_zero k)) h1
  have hysv : ys.map (interp V ρ)
      = dsa.map (interp V (consList as₁ ρ)) ++ (ys.drop n).map (interp V ρ) := by
    rw [hdsaV, has1, ← List.map_append, List.take_append_drop]
  rw [hysv] at h2
  have h3 := teleFit_peel' dsa hpeel
    (by rw [hdl, List.length_map, List.length_drop, hys]
        rw [show n + (n + cA.2 - n) = n + cA.2 by omega]; exact hpc) h2
  rw [Option.some.inj hrestE] at h3
  have hfit := spineFit_of_teleFit
    (by rw [substTele_length, hlab, List.length_map, List.length_drop, hys]; omega) h3
  -- the application, decoded
  obtain ⟨-, hHF, hval⟩ := instCtor_decode mpC Rd.hD hlpsR hul hds hdsa hlenP' Rd.hmm hiD
    hlT hTys hEq hlab (by rw [hkey, hself]; exact hsat) hfit
  rw [hself] at hHF hval
  refine ⟨hHF.2.1.length_eq, ?_⟩
  rw [← hval, interp_mkAppN_foldl, hysv, hname,
    acval_interp_closed mpC.base2 _ _ ρ (consList as₁ ρ)]

set_option maxHeartbeats 8000000 in
/-- **An outside class's constructor, fitted back** (`genOutCtorOwn`'s
converse): at parameter values satisfying the container's parameter
telescope at a level valuation `ψc`, fields fitting the constructor's
recorded fields at the carrier's hole frame there fit, after the
parameters, the constructor's stored type read at `ψc` — the parameters
fit its parameter binders (`LfpCtorReads`), and the fields the
instantiated constructor's fields (`instCtor_fit`), which are the peel's
residual. -/
theorem genOutCtorRefit {j : Nat} {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI) (hcov : LfpCover mpC [])
    {i : Nat} {cA : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some cA)
    (ψc : Name → Nat) {T0 : Term}
    (hT0 : denote mpC.base2.acval envC ψc 0 cA.1.type = some T0)
    (hT0cl : Term.bvarsBelow 0 T0)
    (hpc : Rules.PiChain ((tgtMajor out j).ds.length + cA.2) T0)
    {σ : Nat → V} {as₁ fs : List V} (has1L : as₁.length = (tgtMajor out j).ds.length)
    (hsat : Sat V ((tgtClsD d Dc out j).params ψc).reverse (consList as₁ σ))
    (hfs : SpineFit ((tgtClsD d Dc out j).frame ψc (consList as₁ σ)
        ((tgtClsD d Dc out j).carrier ψc (consList as₁ σ)))
      ((tgtClsD d Dc out j).fields ψc (tgtClsM mc pp.toBlockShape out j) i) fs) :
    ∃ X, TeleFit V σ T0 (as₁ ++ fs) X := by
  have hacl := mpC.base2.acval_closed
  obtain ⟨hiD, hfc0, hlpC, hlpsR⟩ := Rd.hctor i cA hcAM
  obtain ⟨-, -, -, ⟨-, hrdC⟩, -⟩ := mpC.lfp_ok _ Rd.hD
  have hcons := List.mem_of_find?_eq_some hfc0
  have hwfC := mpC.base2.wf.consts _ hcons
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hself := ConLeche.Level.substFn_param_self ψc cvI.levelParams
  have hul : (cvI.levelParams.map Level.param).length = cvI.levelParams.length :=
    List.length_map _
  obtain ⟨cv', nPc, nF, hf', -, -, hpars, A0, -, -, hrdA⟩ := hrdC _ Rd.hmm i hiD
  rw [hfc0] at hf'
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv' ∧ (tgtMajor out j).ds.length = nPc ∧ cA.2 = nF := by
    injection hf' with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hlenP := (hrdA ψc).1
  have hfl : fs.length = cA.2 := by rw [hfs.length_eq, (hrdA ψc).2.1]
  -- the constructor's parameter binders
  have harity : (cA.1.type.stripPis ((tgtMajor out j).ds.length + cA.2)).isSome = true := by
    rw [← Rd.hnpc]; exact genCls_arity hcov Rd hcAM
  obtain ⟨fvsA, oA, hopA⟩ := openPisAtFvars_of_stripPis_isSome
    ((tgtMajor out j).ds.length + cA.2) (e := cA.1.type) 0 harity
  obtain ⟨oP, hopP⟩ := ConLeche.openPisAtFvars_prefix (tgtMajor out j).ds.length
    ((tgtMajor out j).ds.length + cA.2) _ 0 (Nat.le_add_right _ _) hopA
  obtain ⟨pps, b0, hst, -, hplen, -⟩ := denote_openPis (tgtMajor out j).ds.length hopP hT0
  obtain ⟨hT0E, -⟩ := stripPisAV_eq_mkPis hst
  have hsatC := hpars _ pps b0 (by rw [← hT0E]; exact hT0) (Nat.le_of_eq hplen.symm) _ hsat
  rw [List.take_of_length_le (Nat.le_of_eq hplen)] at hsatC
  have hspK : SpineFit σ pps as₁ := spineFit_of_sat_consList (by rw [has1L, hplen]) hsatC
  generalize hn : (tgtMajor out j).ds.length = n at has1L hfc0 hlenP hpc hplen ⊢
  -- the canonical parameters, read at the parameters' frame
  have hds : ∀ x ∈ canonParams n, Expr.WScoped n x ∧ x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_canonParams hx
    exact ⟨by simp [Expr.WScoped, hk], rfl⟩
  obtain ⟨dsa, hdsa⟩ := Rules.DenoteSpine.exists_of_all (acval := mpC.base2.acval)
    (env := envC) (φ := ψc) (d := n) (canonParams n) fun x hx => by
      obtain ⟨k, -, rfl⟩ := mem_canonParams hx
      exact ⟨_, denote_fvar _ _ _ _⟩
  have hdl : dsa.length = n := by
    rw [← DenoteSpine.length_eq hdsa, canonParams_length]
  have hdsaV : dsa.map (interp V (consList as₁ σ)) = as₁ := by
    refine List.ext_getElem (by rw [List.length_map, hdl, has1L]) fun q h1 h2 => ?_
    have hq : q < n := by rw [List.length_map, hdl] at h1; exact h1
    have hr := DenoteSpine.getD hdsa default q (by rw [canonParams_length]; exact hq)
    have hcq : (canonParams n).getD q default = .fvar q (.sort .zero) := by
      simp [canonParams, ConLeche.nestPhs, List.getD_eq_getElem?_getD, hq]
    rw [hcq, denote_fvar] at hr
    have e1 : dsa[q] = dsa.getD q default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have e2 : as₁[q] = as₁.getD q pt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl
    rw [List.getElem_map, e1, ← Option.some.inj hr, interp_bvar,
      consList_getD_of_lt _ _ _ (by rw [has1L]; omega), has1L,
      show n - 1 - (n - 1 - q) = q by omega, e2]
  have hkey : keyFrame dsa n (consList as₁ σ) = consList as₁ σ := by
    unfold keyFrame
    rw [hdsaV]
    congr 1
    funext k
    rw [← has1L]
    exact consList_apply_add as₁ σ k
  -- the instantiated constructor, at the canonical parameters
  have hlenP' : ((tgtClsD d Dc out j).params
      (Level.substFn ψc cvI.levelParams (cvI.levelParams.map Level.param))).length
      = (canonParams n).length := by rw [canonParams_length, hself]; exact hlenP
  have hfc' : envC.find? ((tgtClsD d Dc out j).ctorName (tgtClsM mc pp.toBlockShape out j) i)
      = some (.ctorInfo cA.1 (canonParams n).length cA.2) := by
    rw [canonParams_length]; exact hfc0
  obtain ⟨-, crest, ab, hcr, ⟨Tys, hlT, hTys, hEq⟩, hlab, hcrRead⟩ :=
    instCtor_read mpC Rd.hD hlpsR Rd.hnd hul hds hdsa hlenP' Rd.hmm hiD hfc'
  rw [ConLeche.instPisWith_eq_instPisAt] at hcr
  obtain ⟨⟨doms, crest'⟩, hinst, hcr'⟩ := Option.map_eq_some_iff.mp hcr
  obtain rfl : crest' = crest := hcr'
  have hTy : denote mpC.base2.acval envC ψc n
      (cA.1.type.instantiateLevelParams cA.1.levelParams (cvI.levelParams.map Level.param))
      = some T0 := by
    rw [denote_instLevels mpC.base2.acval_params ψc, hlpC, hself]
    exact denote_depth_of_closed hacl hCf
      (fun k => denote_liftN_eq_self mpC.base2.cval_closed hCf hCb hT0 1 k)
      hT0 _
  obtain ⟨restA, hrest, hpeel⟩ := Rules.denote_instPisAt_peel hacl
    (acval_inst_self mpC.base2) _ hinst
    (Expr.WScoped.of_not_hasFvar (by rw [Expr.hasFvar_instantiateLevelParams]; exact hCf))
    hds hTy hdsa
  have hrestE := hrest.symm.trans hcrRead
  -- the fields fit the instantiated constructor's fields, the peel's residual
  have hF := (instCtor_fit mpC Rd.hD hlpsR hul hds hdsa hlenP' Rd.hmm hiD hlT hTys hEq hlab
    (ρ := consList as₁ σ) (by rw [hkey, hself]; exact hsat)).1 fs
  rw [hkey, hself] at hF
  have hT1 : ∃ X, TeleFit V (consList as₁ σ) restA fs X := by
    rw [Option.some.inj hrestE]
    exact ⟨_, teleFit_mkPisAV_of_spineFit (hF.mpr hfs)⟩
  obtain ⟨X1, hT1⟩ := hT1
  -- the parameters fit the parameter binders, up to the peel
  rw [hT0E] at hT0cl
  have hbnd : ∀ l, l < pps.length → Term.bvarsBelow l (pps.getD l default) := by
    intro l hl
    have := (bvarsBelow_mkPisAV_inv hT0cl).1.getD_below l hl
    rwa [Nat.zero_add] at this
  obtain ⟨rest, hTP⟩ := teleFitPA_mkPisAV_of_spineFit (pds := pps) (b := b0) (ws := dsa)
    (by rw [hdl, hplen]) (by rw [hdsaV]; exact spineFit_frame_of_bounded hbnd hspK)
  rw [← hT0E] at hTP hT0cl
  obtain rfl : rest = restA := Option.some.inj (hTP.peelPis.symm.trans hpeel)
  have hT2 := teleFit_unpeel dsa hTP (by rw [hdl, hfl]; exact hpc) hT1
  rw [hdsaV] at hT2
  exact teleFit_congr_frame' _ (n := 0) (ρ' := σ) hT0cl
    (fun k hk => absurd hk (Nat.not_lt_zero k)) hT2

set_option maxHeartbeats 8000000 in
/-- **(T) at an outside class**: where the class is never `Prop` at the
recursor's levels, a fired application that is not the point, at the
constructor's own levels `ψj` and parameters, is the container's
injection of its fields at `ψj` (`genOutCtorOwn`); not the point, the
container is above `Prop` at `ψj` (`mkZero`), so that injection is the
one at the class's levels (`injFrame`); the major lies in the class's
carrier there, so its decomposition is that injection (`mkInj`): the
fields hole-fit the constructor at the class's frame.  Hence the
constructor at the class's levels, applied to the pins' readings
(`ys₀`, the class's parameters) and the same fields, fits its type there
(`genOutCtorRefit`) and is the same injection (`LfpClause.ctor`). -/
theorem genOut_T
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt j)
    (ψ : Name → Nat) {ψj ψl : Name → Nat}
    (hlv : ∀ p ∈ cA.1.levelParams, ψl p = tgtClsψ cvc out ψ j p)
    (hw : (tgtClsD d Dc out j).w (tgtClsψ cvc out ψ j) ≠ 0)
    {TVja : Term} (hread : denote mpC.base2.acval envC ψj 0 cA.1.type = some TVja)
    {ρ : Nat → V} {xs ys : List Term} {restR restC : Term}
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hyl : ys.length = (tgtMajor out j).nPc + cA.2)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys]) restR)
    (hfitC : TeleFitPA V ρ TVja ys restC) (hWD : ∀ y ∈ ys, WellDenoted V ρ y)
    (hne : interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys) ≠ pt)
    {ys₀ : List Term} (hyl0 : ys₀.length = (tgtMajor out j).nPc)
    (hysv : ∀ q, q < (tgtMajor out j).nPc → interp V ρ (ys₀.getD q default)
      = interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ)
          ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).getD q default)) :
    ∃ restC', TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψl)
        (ys₀ ++ ys.drop (tgtMajor out j).nPc) restC' ∧
      interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψl)
          (ys₀ ++ ys.drop (tgtMajor out j).nPc))
        = interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys) := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hi : i < blockRecNCt (tgtRs out) j :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hcA).1 (blockRecNCt_ge hr)
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by rw [← tgtRs_ctors hr]; exact hcA
  obtain ⟨hpref, hsat, hsp, hmaj⟩ := genOut_major h hS hr Rd ψ hxl hfitR
  obtain ⟨-, -, hxvl, -⟩ := genRow3_frame h hr ψ hxl hfitR
  obtain ⟨T0, pps, b0, hcons, -, hT0, -, -, -, hT0cl, hpc, -⟩ :=
    genOutCtorFit R hg hcov hj hi Rd hMo hnP ψ ρ hpref hcAM
  have hwfC := mpC.base2.wf.consts _ hcons
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hctorTy : blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψl = T0 := by
    have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
      rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
    have hT0' : denote mpC.base2.acval envC (tgtClsψ cvc out ψ j) 0 cA.1.type = some T0 := by
      rw [Rd.hψ]; exact hT0
    rw [blockRecCtorTy, hsel, denote_params_ext mpC.base2 (φ₂ := tgtClsψ cvc out ψ j) hlv 0
      cA.1.type hwfC.2.1, hT0']
    rfl
  obtain ⟨hiD, hfc0, -, -⟩ := Rd.hctor i cA hcAM
  have hname : cA.1.name = (tgtClsD d Dc out j).ctorName (tgtClsM mc pp.toBlockShape out j) i :=
    ConLeche.Env.find?_name hfc0
  have hfindC : envC.find? cA.1.name = some (.ctorInfo cA.1 (tgtMajor out j).ds.length cA.2) := by
    rw [hname]; exact hfc0
  -- the fired application, at its own levels and parameters
  have hTjcl : Term.bvarsBelow 0 TVja :=
    bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hCf) hCb hread
  have hpcj : Rules.PiChain ((tgtMajor out j).ds.length + cA.2) TVja :=
    Rules.piChain_of_stripPis _ (by rw [← Rd.hnpc]; exact genCls_arity hcov Rd hcAM) hread
  obtain ⟨hflj, hvalj⟩ := genOutCtorOwn hcov Rd hcAM ψj hread hTjcl hpcj
    (by rw [hyl, Rd.hnpc]) hfitC hWD
  rw [← Rd.hnpc] at hflj hvalj
  generalize hfV : (ys.drop (tgtMajor out j).nPc).map (interp V ρ) = fsY at hflj hvalj
  obtain ⟨hC, -, -, ⟨-, hrdC⟩, -⟩ := mpC.lfp_ok _ Rd.hD
  -- not the point: the container is above `Prop` at the constructor's levels
  have hwj : (tgtClsD d Dc out j).w ψj ≠ 0 := fun h0 =>
    hne (by rw [hvalj]; exact hC.mkZero _ h0 _ _ _)
  -- the major's decomposition at the class's frame is that injection
  have hmN : tgtClsM mc pp.toBlockShape out j < (tgtClsD d Dc out j).N :=
    Nat.lt_of_lt_of_le Rd.hmm hC.kN
  have ht : tupW ((tgtClsD d Dc out j).u (tgtClsM mc pp.toBlockShape out j) (tgtClsψ cvc out ψ j))
        ((xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ))
      ∈ˢ (tgtClsD d Dc out j).idx (tgtClsψ cvc out ψ j)
        (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
          (tgtRP pp.toBlockShape j)
          (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ))
        (tgtClsM mc pp.toBlockShape out j) := tupW_mem hsp
  obtain ⟨j', fs', hfit', heq⟩ := hC.carrier_case hsat hmN ht hmaj
  rw [hvalj, hC.injFrame _ _ hwj hw] at heq
  have hfl : fsY.length
      = ((tgtClsD d Dc out j).fields (tgtClsψ cvc out ψ j) (tgtClsM mc pp.toBlockShape out j)
          i).length := by
    obtain ⟨cv', nPc, nF, -, -, -, -, A0, -, -, hrdA⟩ := hrdC _ Rd.hmm i hiD
    rw [hflj, (hrdA ψj).2.1, (hrdA _).2.1]
  obtain ⟨hjj, rfl⟩ := hC.mkInj _ hw _ hmN i fsY j' fs' hiD hfit'.1 hfl
    hfit'.2.1.length_eq heq
  subst hjj
  -- the pins' values, the class's frame
  have hdl : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length
      = (tgtMajor out j).nPc :=
    (DenoteSpine.length_eq (Rd.hdsa ψ)).symm.trans Rd.hnpc.symm
  generalize hxV : (xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) = xsV
    at hsat hsp hmaj hysv hxvl hfit' ht
  have hys0V : ys₀.map (interp V ρ)
      = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map (interp V (consList xsV ρ)) := by
    refine List.ext_getElem (by rw [List.length_map, List.length_map, hyl0, hdl])
      fun q h1 h2 => ?_
    rw [List.length_map, hyl0] at h1
    have hq2 : q < (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length := by
      rw [hdl]; exact h1
    have e1 := hysv q h1
    rw [List.getElem_map, List.getElem_map]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hyl0]; exact h1),
      Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq2,
      Option.getD_some] at e1
    exact e1
  have hkeyE : keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
      (tgtRP pp.toBlockShape j) (consList xsV ρ)
      = consList ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
          (interp V (consList xsV ρ))) ρ := by
    unfold keyFrame
    congr 1
    funext k
    rw [show tgtRP pp.toBlockShape j = pp.toBlockShape.rulePrefixAt j from rfl, ← hxvl]
    exact consList_apply_add xsV ρ k
  have hysV : (ys₀ ++ ys.drop (tgtMajor out j).nPc).map (interp V ρ)
      = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map (interp V (consList xsV ρ))
        ++ fsY := by
    rw [List.map_append, hys0V, hfV]
  have hlen' : (ys₀ ++ ys.drop (tgtMajor out j).nPc).length
      = (tgtMajor out j).ds.length + cA.2 := by
    rw [List.length_append, List.length_drop, hyl0, hyl, ← Rd.hnpc]; omega
  -- the constructor at the class's levels, at the pins and the fields: fitted
  have hT0c : denote mpC.base2.acval envC (tgtClsψ cvc out ψ j) 0 cA.1.type = some T0 := by
    rw [Rd.hψ]; exact hT0
  have hfit2 := hfit'.2.1
  rw [hkeyE] at hsat hfit2
  obtain ⟨X, hTF⟩ := genOutCtorRefit Rd hcov hcAM _ hT0c hT0cl hpc
    (by rw [List.length_map, hdl, Rd.hnpc]) hsat hfit2
  rw [← hysV] at hTF
  obtain ⟨restC', hfitPA⟩ := Rules.teleFitPA_of_teleFit _ (by rw [hlen']; exact hpc) hTF
  refine ⟨restC', by rw [hctorTy]; exact hfitPA, ?_⟩
  -- … and the same injection
  have hsa : SpineFit (fun k => consList xsV ρ (k + tgtRP pp.toBlockShape j))
      ((tgtClsD d Dc out j).params (tgtClsψ cvc out ψ j))
      ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
        (interp V (consList xsV ρ))) := by
    refine spineFit_of_sat_consList (by rw [List.length_map, Rd.hlenP ψ, hdl, Rd.hnpc]) ?_
    rw [← hkeyE] at hsat
    exact hsat
  have hval := hC.ctor _ hmN i _ _ _ _ _ hsa ht hfit'
  rw [hvalj, hC.injFrame _ _ hwj hw, mpC.base2.acval_params cA.1.name _ hfindC _ _ hlv,
    interp_mkAppN_foldl, hysV, hname,
    acval_interp_closed mpC.base2 _ _ ρ (fun k => consList xsV ρ (k + tgtRP pp.toBlockShape j)),
    hval]

set_option maxHeartbeats 8000000 in
/-- **The rows at an OUTSIDE class** (the rule fires `.nested`): the
fired constructor application is the class's injection of its fields,
read at its own parameters (`genOutCtorOwn`: the step compares them
only at case 3); the major lies in the class's carrier at the pins'
frame and the recursor's index tuple, and the class is never `Prop`
here (`genOutNZ`, `genOutW`), so the carrier's decomposition there is
that injection (`mkInj`): the fields hole-fit at the pins' frame —
`genRow3_core` does the rest. -/
theorem genRows3_out
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
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
    (hf : ConLeche.tgtFireOf pp.toBlockShape (ConLeche.tgtMajorsOf out) j r
      = .nested lvls pins)
    {rl : ConLeche.RecRule} (hrl : ConLeche.RecRule.fire rl = .nested lvls pins) :
    BlockRuleRows3 (V := V) mpC pp (ConLeche.tgtMajorsOf out j).nPc (tgtRs out)
      (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
      (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
      (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
      (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
      (fun ψ => blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) φ j i r cA rl := by
  intro us hus hℓ usj ρ xs ys restR restC hxl hyl husjl hψ hyWD _ hfitR hfitC
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hi : i < blockRecNCt (tgtRs out) j :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hcA).1 (blockRecNCt_ge hr)
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by rw [← tgtRs_ctors hr]; exact hcA
  obtain ⟨hlvls, -⟩ := genOutPinVal R h hr Rd hf φ us
  have hMM : (ConLeche.tgtMajorsOf out j).nPc = (tgtMajor out j).nPc := rfl
  rw [hMM] at hyl ⊢
  -- the level assignment of the rule, and the constructor's
  have hlv : ∀ p ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj p
      = Level.substFn (Level.substFn φ r.1.levelParams us) cvI.levelParams
          (tgtMajor out j).lvls p := by
    obtain ⟨-, -, hlpsI, -⟩ := Rd.hctor i cA hcAM
    intro p hp
    rw [hψ]
    simp only [ConLeche.recFireComparands, hrl]
    rw [hlvls, ConLeche.Level.substFn_map_subst (by rw [Rd.hul, hlpsI]) hp, hlpsI]
  generalize hψe : Level.substFn φ r.1.levelParams us = ψ at hℓ hfitR hlv ⊢
  obtain ⟨hpref, hws, hxvl, hisl⟩ := genRow3_frame h hr ψ hxl hfitR
  generalize hxV : (xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) = xsV
    at hpref hws hxvl ⊢
  generalize hiV : (xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) = isV
    at hws hisl ⊢
  -- the instantiated constructor, fitted
  obtain ⟨T0, -, -, hcons, -, hT0, -, -, -, hT0cl, hpc, -⟩ :=
    genOutCtorFit R hg hcov hj hi Rd hMo hnP ψ ρ hpref hcAM
  have hwfC := mpC.base2.wf.consts _ hcons
  have hctorTy : blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i
      (Level.substFn φ cA.1.levelParams usj) = T0 := by
    have hrd : (tgtRs out).getD j default = r := by rw [List.getD_eq_getElem?_getD, hr]; rfl
    have hsel : (((tgtRs out).getD j default).2.2.2.getD i default) = cA := by
      rw [hrd, List.getD_eq_getElem?_getD, hcA]; rfl
    rw [blockRecCtorTy, hsel, denote_params_ext mpC.base2 hlv 0 cA.1.type hwfC.2.1, hT0]
    rfl
  replace hfitC : TeleFitPA V ρ T0 ys restC := by rw [← hctorTy]; exact hfitC
  -- the fired application, at its own parameters
  obtain ⟨hfl, hval0⟩ := genOutCtorOwn hcov Rd hcAM _ hT0 hT0cl hpc
    (by rw [hyl, Rd.hnpc]) hfitC hyWD
  rw [← Rd.hnpc, ← Rd.hψ] at hfl hval0
  generalize hfV : (ys.drop (tgtMajor out j).nPc).map (interp V ρ) = fsY at hfl hval0 ⊢
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok _ Rd.hD
  obtain ⟨hiD, hfc0, -, -⟩ := Rd.hctor i cA hcAM
  have hname : cA.1.name = (tgtClsD d Dc out j).ctorName (tgtClsM mc pp.toBlockShape out j) i :=
    ConLeche.Env.find?_name hfc0
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
    unfold tgtClsIs; rw [ite_eq_left hG]
  have hsatK := Rd.hsat ψ ρ xsV hpref
  have hval3 : interp V ρ (Term.mkAppN
      (mpC.base2.acval cA.1.name (Level.substFn φ cA.1.levelParams usj)) ys)
      = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ j i fsY := by
    rw [mpC.base2.acval_params cA.1.name _ hfindC _ _ hlv, ← Rd.hψ]
    exact hval0
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
    hfl hfit'.2.1.length_eq heq
  subst hjj
  exact genRow3_core (hS ψ ρ) (hD ψ ρ) (hDI ψ ρ) hj hi hxvl hisl hws hpref hfit' hval3

/-- **The class's sort at the constructor's levels is its sort at the
class's.** -/
theorem genOut_wCongr {j : Nat} {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {i : Nat} {cA : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some cA)
    {ψj ψc : Name → Nat} (hlv : ∀ p ∈ cA.1.levelParams, ψj p = ψc p) :
    (tgtClsD d Dc out j).w ψj = (tgtClsD d Dc out j).w ψc := by
  obtain ⟨-, -, hlpC, -⟩ := Rd.hctor i cA hcAM
  obtain ⟨caps, hfc, -⟩ := genOut_caps Rd hcAM
  have hfm : envC.find? ((tgtClsD d Dc out j).member (tgtClsM mc pp.toBlockShape out j))
      = some (.indInfo cvI caps) := by rw [Rd.hmem]; exact hfc
  exact lfpW_congr mpC Rd.hD Rd.hmm hfm (fun q hq => by rw [← hlpC] at hq; exact hlv q hq)

/-- **(P) at an outside class**: at a `Prop` valuation of the class a
fitting graded constructor application lies in a truth value (its
residual is the container at fitting arguments, `genOut_typed`). -/
theorem genOut_P (hcov : LfpCover mpC []) {j : Nat} {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {i : Nat} {cA : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some cA)
    {ψj ψc : Name → Nat} (hlv : ∀ p ∈ cA.1.levelParams, ψj p = ψc p)
    (hw : (tgtClsD d Dc out j).w ψc = 0) {TVja : Term}
    (hread : denote mpC.base2.acval envC ψj 0 cA.1.type = some TVja)
    {ρ : Nat → V} {ys : List Term} {restC : Term}
    (hys : ys.length = (tgtMajor out j).nPc + cA.2)
    (hfitC : TeleFitPA V ρ TVja ys restC) (hWD : ∀ y ∈ ys, WellDenoted V ρ y) :
    interp V ρ (Term.mkAppN (mpC.base2.acval cA.1.name ψj) ys) = pt := by
  obtain ⟨args, -, -, -, hin, -, hU⟩ := genOut_typed hcov Rd hcAM hread hys hfitC hWD
  rw [genOut_wCongr Rd hcAM hlv, hw] at hU
  exact mem_univ_zero hU hin

set_option maxHeartbeats 8000000 in
/-- **(U)'s index pin at an outside class** (L7's coherence): where the
fired constructor application is the point, its residual's index
arguments and the recursor's indices are fits of the container's index
telescope at the same parameters (the constructor's are the pins', the
recursor's the class's: equal by the `.nested` pins), compared where
neither is the point — so equal. -/
theorem genOut_pin (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {i : Nat} {cA : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some cA)
    (ψ : Name → Nat) {ψj : Name → Nat}
    (hlv : ∀ p ∈ cA.1.levelParams, ψj p = tgtClsψ cvc out ψ j p) {TVja : Term}
    (hread : denote mpC.base2.acval envC ψj 0 cA.1.type = some TVja)
    {ρ : Nat → V} {xs ys : List Term} {maj restR restC : Term}
    (hxl : xs.length = pp.toBlockShape.majorIdxAt j)
    (hys : ys.length = (tgtMajor out j).nPc + cA.2)
    (hfitR : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ [maj]) restR)
    (hfitC : TeleFitPA V ρ TVja ys restC) (hWD : ∀ y ∈ ys, WellDenoted V ρ y)
    (hpar : ∀ q, q < (tgtMajor out j).nPc → interp V ρ (ys.getD q default)
      = interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ)
          ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).getD q default))
    (hpinC : IotaIndexPinC (V := V) ρ restC (tgtMajor out j).nPc
      (pp.toBlockShape.majorIdxAt j) (pp.toBlockShape.rulePrefixAt j) xs) :
    IotaIndexPin (V := V) ρ restC (tgtMajor out j).nPc
      (pp.toBlockShape.majorIdxAt j) (pp.toBlockShape.rulePrefixAt j) xs := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hrPle := blockRecHrPle (p := pp) h hj
  obtain ⟨-, hsat, hsp, -⟩ := genOut_major h hS hr Rd ψ hxl hfitR
  obtain ⟨args, hlenA, hparA, hrestE, -, hfitA, -⟩ :=
    genOut_typed hcov Rd hcAM hread hys hfitC hWD
  obtain ⟨hC, -, hrd, ⟨-, hrdC⟩, -⟩ := mpC.lfp_ok _ Rd.hD
  have hmN : tgtClsM mc pp.toBlockShape out j < (tgtClsD d Dc out j).N :=
    Nat.lt_of_lt_of_le Rd.hmm hC.kN
  -- the container former's telescope, at the two level assignments
  obtain ⟨hiD, hfc0, hlpC, -⟩ := Rd.hctor i cA hcAM
  obtain ⟨cv, caps, hfm, hab⟩ := hrd _ Rd.hmm
  rw [Rd.hmem] at hfm
  obtain ⟨caps₀, hf₀⟩ := Rd.hfind
  rw [hf₀] at hfm
  obtain ⟨rfl, rfl⟩ : cvI = cv ∧ caps₀ = caps := by
    injection hfm with h'; injection h' with a b; exact ⟨a, b⟩
  have hconsI := List.mem_of_find?_eq_some hf₀
  have hwfI := mpC.base2.wf.consts _ hconsI
  obtain ⟨ab, hta, hmap⟩ := hab ψj
  obtain ⟨ab', hta', hmap'⟩ := hab (tgtClsψ cvc out ψ j)
  rw [denote_params_ext mpC.base2 (φ₂ := tgtClsψ cvc out ψ j)
    (fun q hq => by
      change q ∈ cvI.levelParams at hq
      rw [← hlpC] at hq; exact hlv q hq) 0 cvI.type hwfI.2.1, hta'] at hta
  obtain ⟨habm, hwab⟩ := mkPisAV_sort_inj (Option.some.inj hta).symm
  have hmap'' := habm.trans hmap'
  have hcl : Term.bvarsBelow 0
      (mkPisAV ab (.sort ((tgtClsD d Dc out j).w (tgtClsψ cvc out ψ j)))) := by
    have heq := Option.some.inj hta
    rw [hwab] at heq
    rw [← heq]
    exact bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hwfI.1)
      hwfI.2.2.2.1 hta'
  have hDB := (bvarsBelow_mkPisAV_inv hcl).1
  -- the parameter count
  obtain ⟨cv', nPc, nF, hf', -, -, -, A0, -, -, hrdA⟩ := hrdC _ Rd.hmm i hiD
  rw [hfc0] at hf'
  have hnPc : (tgtMajor out j).ds.length = nPc := by
    injection hf' with h; injection h
  have hPl := fun ψ' => (hrdA ψ').1
  have hparsL := hC.parsLen _ Rd.hmm
  have hnP : (tgtMajor out j).nPc = nPc := by rw [Rd.hnpc, hnPc]
  have hdl : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length
      = (tgtMajor out j).nPc :=
    (DenoteSpine.length_eq (Rd.hdsa ψ)).symm.trans Rd.hnpc.symm
  generalize (tgtMajor out j).nPc = nP at hys hpar hpinC hlenA hparA hnP hdl ⊢
  -- the parameter and index halves
  have hlenPars : ∀ ψ', ((tgtClsD d Dc out j).pars (tgtClsM mc pp.toBlockShape out j) ψ').length
      = nP := fun ψ' => by rw [hparsL, hPl, hnP]
  have hidsE : (tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j) ψj
      = (tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j) (tgtClsψ cvc out ψ j) := by
    have := hmap.symm.trans hmap''
    exact List.append_inj_right this (by rw [hlenPars, hlenPars])
  have hidsAB : (tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j) (tgtClsψ cvc out ψ j)
      = (ab.drop nP) := by
    rw [hmap'', List.drop_left' (hlenPars _)]
  rw [hidsE] at hfitA hlenA
  -- split the residual's fit
  obtain ⟨as₁, as₂, hasE, hfit1, hfit2⟩ := spineFit_append_inv hfitA
  have has1L : as₁.length = nP := by rw [hfit1.length_eq, hlenPars]
  have has1 : as₁ = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).map
      (interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ)) := by
    refine List.ext_getElem (by rw [has1L, List.length_map, hdl]) fun q h1 h2 => ?_
    have hq : q < nP := by rw [has1L] at h1; exact h1
    have hA := congrArg (fun l => l.getD q pt) hasE
    rw [getD_append_left' (by rw [has1L]; exact hq), getD_map_pt (by rw [hlenA]; omega),
      hparA q hq, hpar q hq] at hA
    have hq2 : q < (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).length := by
      rw [hdl]; exact hq
    have e1 : as₁[q] = as₁.getD q pt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
    have e2 : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)[q]
        = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j).getD q default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq2]; rfl
    rw [List.getElem_map, e1, e2]
    exact hA.symm
  -- the indices, at the class's frame
  have hfitI : SpineFit (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ j)
        (tgtRP pp.toBlockShape j)
        (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ))
      ((tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j) (tgtClsψ cvc out ψ j)) as₂ := by
    rw [hidsAB] at hfit2 ⊢
    refine spineFit_congr_below (k := 0 + nP) (by exact domsBelow_drop nP hDB) (fun q hq => ?_) hfit2
    unfold keyFrame
    rw [has1, consList_getD_of_lt _ _ _ (by rw [List.length_map, hdl]; omega),
      consList_getD_of_lt _ _ _ (by rw [List.length_map, hdl]; omega)]
  have hTI := (hC.idxOk _ _ hsat _ hmN).1.spineTy
  have hlenI : ((tgtClsD d Dc out j).ids (tgtClsM mc pp.toBlockShape out j)
      (tgtClsψ cvc out ψ j)).length
      = pp.toBlockShape.majorIdxAt j - pp.toBlockShape.rulePrefixAt j := by
    rw [← hsp.length_eq, List.length_map, List.length_drop, hxl]
  obtain ⟨Ha, cargsa, hrestEq, hcarLen, hcar⟩ := hpinC
  refine ⟨Ha, cargsa, hrestEq, hcarLen, fun q hq => ?_⟩
  have hcarLen' : cargsa.length
      = nP + (pp.toBlockShape.majorIdxAt j - pp.toBlockShape.rulePrefixAt j) := by
    rcases hcarLen with hc | hc
    · omega
    · exact hc
  obtain ⟨-, hcargs⟩ := Term.mkAppN_inj (hrestEq.symm.trans hrestE)
    (by rw [hcarLen', hlenA, hlenI])
  subst hcargs
  -- the residual's index values, by position
  have has2 : ∀ l, l < pp.toBlockShape.majorIdxAt j - pp.toBlockShape.rulePrefixAt j →
      interp V ρ (cargsa.getD (nP + l) default) = as₂.getD l pt := by
    intro l hl
    have hA := congrArg (fun L => L.getD (nP + l) pt) hasE
    rw [getD_map_pt (by rw [hcarLen']; omega), ← has1L, getD_append_right'] at hA
    rw [has1L] at hA
    exact hA
  have heqI : as₂ = (xs.drop (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ) := by
    refine spineFit_eq_of_cond_getD hTI hfitI hsp fun l hl h1 h2 => ?_
    rw [hlenI] at hl
    rw [getD_map_pt (by rw [List.length_drop, hxl]; omega), getD_drop'] at h2 ⊢
    rw [← has2 l hl] at h1 ⊢
    exact hcar l hl h1 h2
  rw [has2 q hq, heqI, getD_map_pt (by rw [List.length_drop, hxl]; omega), getD_drop']

set_option maxHeartbeats 8000000 in
/-- **The case split's facts at an outside rule**, at the recursors' cons. -/
theorem genOutExtra
    (R : GenRecRun .verified F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG .verified F envC pp cvTas (tgtRs out))
    (hS : ∀ ψ ρ, GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) (hMo : (tgtMajor out j).member = none)
    {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt j)
    {lvls : List Level} {pins : List Expr}
    (hf : ConLeche.tgtFireOf pp.toBlockShape (ConLeche.tgtMajorsOf out) j r
      = .nested lvls pins)
    (hctorCB : ConstsBound envC cA.1.type)
    (hctorRead : ∀ ψ' : Name → Nat, denote mpC.base2.acval envC ψ' 0 cA.1.type
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ'))
    {Rr : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → Bool × List ConLeche.RecRule}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List Term}
    {m₃ : EnvModel V (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC)}
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC (tgtRs out) s eqs) (φ : Name → Nat)
    {rl : ConLeche.RecRule} (hct : ConLeche.RecRule.ctor rl = cA.1.name)
    (hnf : ConLeche.RecRule.nfields rl = cA.2)
    (hfire : ConLeche.RecRule.fire rl = .nested lvls pins)
    (hpinsOk : RecRulePinsOk m₃ φ r.1 (pp.toBlockShape.rulePrefixAt j) rl) :
    RecRuleKWit m₃ φ r.1.name r.1 (pp.toBlockShape.majorIdxAt j)
      (pp.toBlockShape.rulePrefixAt j) (ConLeche.recKExpected pp.toBlockShape (tgtMajor out j)) rl ∧
    RecRuleExtraNK m₃ φ r.1.name r.1 (pp.toBlockShape.majorIdxAt j)
      (pp.toBlockShape.rulePrefixAt j) (ConLeche.recKExpected pp.toBlockShape (tgtMajor out j)) rl := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hcAM : (tgtMajor out j).ctors[i]? = some cA := by rw [← tgtRs_ctors hr]; exact hcA
  obtain ⟨hiD, hfc0, hlpC, -⟩ := Rd.hctor i cA hcAM
  have hname : cA.1.name = (tgtClsD d Dc out j).ctorName (tgtClsM mc pp.toBlockShape out j) i :=
    ConLeche.Env.find?_name hfc0
  have hfindC : envC.find? cA.1.name = some (.ctorInfo cA.1 (tgtMajor out j).ds.length cA.2) := by
    rw [hname]; exact hfc0
  have hcv := recStage_cvFacts h
  have hkeep := find?_consBlockRecsR_keep (R := Rr) (q := pp.toBlockShape)
    (fun r' hr' => (hcv r' hr').1)
  have hfind3 : (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC).find?
      (ConLeche.RecRule.ctor rl) = some (.ctorInfo cA.1 (tgtMajor out j).ds.length cA.2) := by
    rw [hct]; exact hkeep _ _ hfindC
  have hstored : m₃.acval (ConLeche.RecRule.ctor rl) = mpC.base2.acval cA.1.name := by
    rw [hct]; exact blockRecAcv_stored h hac (by rw [hfindC]; rfl)
  have hTVjaOf : ∀ usj : List Level,
      denote m₃.acval (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) φ 0
        (cA.1.type.instantiateLevelParams cA.1.levelParams usj)
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i
          (Level.substFn φ cA.1.levelParams usj)) := by
    intro usj
    rw [denote_instLevels m₃.acval_params φ]
    exact blockRecDenote_cross h hac _ 0 cA.1.type hctorCB (hctorRead _)
  have hnpd : (tgtMajor out j).nPc = (tgtMajor out j).ds.length := Rd.hnpc
  -- the pins, read at the cons as at the constructors' environment
  obtain ⟨-, -, hpinsWf, -⟩ := R.fire_nestedRead hr hf
  have hplenP : pins.length = (tgtMajor out j).nPc := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h⟩ := R.fire_nestedRead hr hf
    exact h
  have hpinCross : ∀ (us : List Level) q (vpa : Term),
      denote mpC.base2.acval envC φ (pp.toBlockShape.rulePrefixAt j)
        (openRev 0 (pp.toBlockShape.rulePrefixAt j)
          ((pins.getD q default).instantiateLevelParams r.1.levelParams us)) = some vpa →
      denote m₃.acval (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) φ
        (pp.toBlockShape.rulePrefixAt j)
        (openRev 0 (pp.toBlockShape.rulePrefixAt j)
          ((pins.getD q default).instantiateLevelParams r.1.levelParams us)) = some vpa := by
    intro us q vpa hvpa
    refine blockRecDenote_cross h hac φ _ _ ?_ hvpa
    refine constsBound_openRev (constsBound_of_constsResolve _ ?_) 0 _
    rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
    by_cases hilt : q < pins.length
    · exact (hpinsWf _ (ConLeche.getD_mem hilt)).2.2.1
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl
  -- the levels: the constructor's are the class's at the recursor's
  have hlvOf : ∀ (us usj : List Level),
      Level.substFn φ cA.1.levelParams usj = Level.substFn φ cA.1.levelParams
        (ConLeche.recFireComparands rl (tgtMajor out j).nPc r.1.levelParams us cA.1.levelParams []
          (pp.toBlockShape.rulePrefixAt j)).1 →
      ∀ p ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj p
        = tgtClsψ cvc out (Level.substFn φ r.1.levelParams us) j p := by
    intro us usj hψ p hp
    obtain ⟨hlvls, -⟩ := genOutPinVal R h hr Rd hf φ us
    rw [hψ]
    simp only [ConLeche.recFireComparands, hfire]
    rw [hlvls, ConLeche.Level.substFn_map_subst (by rw [Rd.hul, hlpC]) hp, hlpC, Rd.hψ]
  have hrPle : pp.toBlockShape.rulePrefixAt j ≤ pp.toBlockShape.majorIdxAt j :=
    blockRecHrPle (p := pp) h hj
  -- the pins' readings at the recursor's prefix: the class's parameters, graded
  have hpinSp : ∀ us : List Level, us.length = r.1.levelParams.length →
      ∀ TVa : Term,
        denote m₃.acval (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC) φ 0
          (r.1.type.instantiateLevelParams r.1.levelParams us) = some TVa →
      ∀ (ρ : Nat → V) (xs : List Term) (a restR : Term),
        xs.length = pp.toBlockShape.majorIdxAt j → TeleFitPA V ρ TVa (xs ++ [a]) restR →
      ∃ ys₀ : List Term, ys₀.length = (tgtMajor out j).nPc ∧
        (∀ q, q < (tgtMajor out j).nPc → interp V ρ (ys₀.getD q default)
          = interp V (consList ((xs.take (pp.toBlockShape.rulePrefixAt j)).map (interp V ρ)) ρ)
              ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out
                (Level.substFn φ r.1.levelParams us) j).getD q default)) ∧
        ((∀ x ∈ xs, WellDenoted V ρ x) → ∀ y ∈ ys₀, WellDenoted V ρ y) := by
    intro us hus TVa hTVa ρ xs a restR hxl hfit
    obtain ⟨-, hpinV⟩ := genOutPinVal R h hr Rd hf φ us
    obtain ⟨vF, hvF⟩ : ∃ vF : Nat → Term, ∀ q, q < (tgtMajor out j).nPc →
        denote mpC.base2.acval envC φ (pp.toBlockShape.rulePrefixAt j)
          (openRev 0 (pp.toBlockShape.rulePrefixAt j)
            ((pins.getD q default).instantiateLevelParams r.1.levelParams us)) = some (vF q) ∧
        ∀ (ρ : Nat → V) (zs : List Term), zs.length = pp.toBlockShape.rulePrefixAt j →
          interp V ρ (Term.instRevChain zs (vF q))
            = interp V (consList (zs.map (interp V ρ)) ρ)
                ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out
                  (Level.substFn φ r.1.levelParams us) j).getD q default) :=
      ⟨fun q => if hq : q < (tgtMajor out j).nPc then Classical.choose (hpinV q hq) else default,
        fun q hq => by
          simp only [hq, dite_true]
          exact Classical.choose_spec (hpinV q hq)⟩
    let ys : List Term := (List.range (tgtMajor out j).nPc).map fun q =>
      Term.instRevChain (xs.take (pp.toBlockShape.rulePrefixAt j)) (vF q)
    refine ⟨ys, by simp [ys], fun q hq => ?_, fun hxs y hy => ?_⟩
    · have hysq : ys.getD q default
          = Term.instRevChain (xs.take (pp.toBlockShape.rulePrefixAt j)) (vF q) := by
        simp [ys, List.getD_eq_getElem?_getD, List.getElem?_range hq]
      rw [hysq]
      exact (hvF q hq).2 ρ _ (by rw [List.length_take]; omega)
    · obtain ⟨q, hq, rfl⟩ : ∃ q, q < (tgtMajor out j).nPc ∧
          y = Term.instRevChain (xs.take (pp.toBlockShape.rulePrefixAt j)) (vF q) := by
        simp only [ys, List.mem_map, List.mem_range] at hy
        obtain ⟨q, hq, rfl⟩ := hy
        exact ⟨q, hq, rfl⟩
      obtain ⟨vpa', hvpa', hgr⟩ := hpinsOk us hus lvls pins hfire q (by rw [hplenP]; exact hq)
      rw [hpinCross us q _ (hvF q hq).1] at hvpa'
      obtain rfl := Option.some.inj hvpa'
      obtain ⟨mid, hmid⟩ := hfit.take (pp.toBlockShape.rulePrefixAt j)
      rw [List.take_append_of_le_length (by omega)] at hmid
      exact hgr ρ _ _ mid (by rw [List.length_take]; omega)
        (fun z hz => hxs z (List.mem_of_mem_take hz)) hTVa hmid
  refine ⟨fun hk1 => ?_, ?_⟩

  · -- an outside major's recursor is never K
    exact absurd hk1 (by simp [ConLeche.recKExpected, hMo])
  · ------------------------------------------------------------------ NK
    intro us hus TVa hTVa cvj cnP cnF hfind
    rw [hfind3] at hfind
    obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cvj ∧ (tgtMajor out j).nPc = cnP ∧ cA.2 = cnF := by
      injection hfind with h'; injection h' with a b c; exact ⟨a, by rw [Rd.hnpc]; exact b, c⟩
    obtain rfl := blockRuleTVa_run mpC h hac hr φ us hTVa
    rw [hstored]
    refine ⟨by rw [hnf]; exact genCls_arity hcov Rd hcAM,
      fun _ => ⟨fun hlic ρ xs a restR hxl hfit => ?_, ?_, fun usj husj hψ TVja hTVja => ?_⟩⟩
    · -- (S), at the comparand levels
      have hlv := hlvOf us _ rfl
      obtain ⟨-, hsat, hsp, hmaj⟩ := genOut_major h hS hr Rd _ hxl hfit
      exact genOut_ne_pt Rd hsat hsp hmaj
        (genOut_S Rd hcAM (fun caps hc => hkeep _ _ hc) hlv hlic)
    · -- (T), at the class's levels and parameters (the pins' readings)
      intro hlic usj husj TVja hTVja ρ xs ys restR restC hxl hyl hfitR hfitC hWDx hWDy hne
      rw [hTVjaOf] at hTVja
      obtain rfl := Option.some.inj hTVja
      rw [hnf] at hyl
      have hlv := hlvOf us _ rfl
      obtain ⟨hlvls, -⟩ := genOutPinVal R h hr Rd hf φ us
      obtain ⟨ys₀, hyl0, hysv, hgr⟩ := hpinSp us hus _ hTVa ρ xs _ restR hxl hfitR
      obtain ⟨restC', hfit', hval⟩ := genOut_T R hg hcov h hS hr hMo hcA Rd hnP _ hlv
        (genOut_S Rd hcAM (fun caps hc => hkeep _ _ hc) hlv hlic) (hctorRead _) hxl hyl hfitR
        hfitC hWDy hne hyl0 hysv
      refine ⟨_, ys₀ ++ ys.drop (tgtMajor out j).nPc, _, restC', ?_, rfl, hTVjaOf _, ?_,
        by rw [List.drop_left' hyl0], fun y hy => ?_, hfit', hval⟩
      · simp only [ConLeche.recFireComparands, hfire, List.length_map]
        rw [hlvls, Rd.hul, hlpC]
      · rw [List.length_append, List.length_drop, hyl0, hyl]; omega
      · rcases List.mem_append.mp hy with hy | hy
        · exact hgr hWDx y hy
        · exact hWDy y (List.mem_of_mem_drop hy)
    rw [hTVjaOf] at hTVja
    obtain rfl := Option.some.inj hTVja
    have hlv := hlvOf us usj hψ
    refine ⟨fun ρ xs a restR hxl hfit hapt ys restC hfitC hyl hWD => ?_, ?_⟩
    · obtain ⟨-, hsat, hsp, hmaj⟩ := genOut_major h hS hr Rd _ hxl hfit
      have hw : (tgtClsD d Dc out j).w
          (tgtClsψ cvc out (Level.substFn φ r.1.levelParams us) j) = 0 :=
        Classical.byContradiction fun hw => genOut_ne_pt Rd hsat hsp hmaj hw hapt
      exact genOut_P hcov Rd hcAM hlv hw (hctorRead _) (by rw [hyl, hnf]) hfitC hWD
    · intro ρ xs ys restR restC hxl hyl hfitR hfitC _ hWDy _ hcN hpinC hpt
      rw [hnf] at hyl
      obtain ⟨-, hpinV⟩ := genOutPinVal R h hr Rd hf φ us
      have hlv' : ∀ p ∈ cA.1.levelParams, Level.substFn φ cA.1.levelParams usj p
          = Level.substFn (Level.substFn φ r.1.levelParams us) cvI.levelParams
              (tgtMajor out j).lvls p := fun p hp => by rw [hlv p hp, Rd.hψ]
      have hpins := genOut_pins R hg hcov h hr hMo hcA Rd hnP hf hlv' hxl hfitR hfitC hyl
        (fun q hq vpa hvpa => hcN lvls pins hfire hpt q hq vpa
          (hpinCross us q vpa hvpa))
      refine genOut_pin hcov h hS hr Rd hcAM _ hlv (hctorRead _) hxl hyl hfitR hfitC hWDy
        (fun q hq => ?_) (hpinC hpt)
      obtain ⟨vpa0, hvpa0, hval⟩ := hpinV q hq
      rw [hpins q hq vpa0 hvpa0]
      exact hval ρ _ (by rw [List.length_take]; omega)

end Outside

end ConLeche.Model
