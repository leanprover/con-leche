module

public import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.TargetOutIdx
import ConLeche.Model.Inductives.TargetOutConv
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.ContInst
import ConLeche.Model.Inductives.ContInstRule
import ConLeche.Model.Inductives.TargetOutConcl
import ConLeche.Model.Inductives.TargetOutRow
import ConLeche.Model.Inductives.ContSubst
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.NatEqs
import ConLeche.Model.IndReduct
import ConLeche.Semantics.Tower.BlockRecTower
import ConLeche.Model.Inductives.GenRecPins
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Annot.BitLemmas

public section

/-!
# The generated recursor types' binder data, read (lane GENREC-CLS)

The class-side facts of the generated stage's family premise
(`GenPreSem`, `GenRecPreRun.lean`) read the STORED recursor types' binder
data (`blockRecRdsAV`).  A stored type is the generated one
(`classConstOk` stores its input), a telescope
`closeTelescope (pre ++ ifs.map g.binder ++ [(maj, g.bm)]) 0 (motive …)`
whose index binders `ifs` are the class former's index telescope at the
class's parameters (`ClassGen.major`: `instPisWith ds former`, opened at
the prefix) and whose major is `I lvls (ds ++ ifs)` — by construction,
no comparison needed.  `genRun_binders` states exactly that, at the
readings.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun ClassGenScoped RecShape NestState)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Syntax -/

omit [SetTheory V] in
theorem mkAppN_append' : ∀ (as bs : List Expr) (f : Expr),
    Expr.mkAppN f (as ++ bs) = Expr.mkAppN (Expr.mkAppN f as) bs
  | [], _, _ => rfl
  | a :: as, bs, f => mkAppN_append' as bs (.app f a)

omit [SetTheory V] in
/-- Scoping transfers along erasure: the annotations are the scoped
term's own, the variables' indices the other's. -/
theorem WScoped.of_erasedEq : ∀ (x : Expr) {x₀ : Expr} {D n : Nat}, Expr.ErasedEq x x₀ →
    Expr.WScoped D x → Expr.WScoped n x₀ → Expr.WScoped n x := by
  intro x
  induction x with
  | fvar i ty =>
    intro x₀ D n he hw hw₀
    match x₀, he with
    | .fvar j _, he =>
      obtain rfl : i = j := he
      simp only [Expr.WScoped] at hw hw₀ ⊢
      exact ⟨hw₀.1, hw.2⟩
  | app f a ihf iha =>
    intro x₀ D n he hw hw₀
    match x₀, he with
    | .app g b, he =>
      simp only [Expr.WScoped] at hw hw₀ ⊢
      exact ⟨ihf he.1 hw.1 hw₀.1, iha he.2 hw.2 hw₀.2⟩
  | lam ty b m iht ihb =>
    intro x₀ D n he hw hw₀
    match x₀, he with
    | .lam ty' b' m', he =>
      simp only [Expr.WScoped] at hw hw₀ ⊢
      exact ⟨iht he.2.1 hw.1 hw₀.1, ihb he.2.2 hw.2 hw₀.2⟩
  | forallE ty b m iht ihb =>
    intro x₀ D n he hw hw₀
    match x₀, he with
    | .forallE ty' b' m', he =>
      simp only [Expr.WScoped] at hw hw₀ ⊢
      exact ⟨iht he.2.1 hw.1 hw₀.1, ihb he.2.2 hw.2 hw₀.2⟩
  | letE ty v b iht ihv ihb =>
    intro x₀ D n he hw hw₀
    match x₀, he with
    | .letE ty' v' b', he =>
      simp only [Expr.WScoped] at hw hw₀ ⊢
      exact ⟨iht he.1 hw.1 hw₀.1, ihv he.2.1 hw.2.1 hw₀.2.1, ihb he.2.2 hw.2.2 hw₀.2.2⟩
  | proj s i e ihe =>
    intro x₀ D n he hw hw₀
    match x₀, he with
    | .proj s' i' e', he =>
      simp only [Expr.WScoped] at hw hw₀ ⊢
      exact ihe he.2.2 hw hw₀
  | bvar => intro _ _ _ _ _ _; simp [Expr.WScoped]
  | sort => intro _ _ _ _ _ _; simp [Expr.WScoped]
  | const => intro _ _ _ _ _ _; simp [Expr.WScoped]
  | lit => intro _ _ _ _ _ _; simp [Expr.WScoped]

section Binders

variable {F : Nat} {env₁ envC : Env} {p : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 1600000 in
/-- **The stored binder data of recursor `c`, read**: its class `cls`'s
former instantiated at the class's parameters (`ty`), opened at the rule
prefix to the index openers `ifs`; the stored binder data are `rP + nIdx
+ 1` entries whose index entries are the readings of the openers' domains
and whose major entry is the reading of `I lvls (ds ++ ifs)` (the stored
type IS the generated one). -/
theorem genRun_binders (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (ψ : Name → Nat) {c : Nat} (hc : c < (tgtRs out).length) :
    ∃ (cls : Nat) (ty : Expr) (ifs : List Expr) (body : Expr),
      genClsOf R.rd c = cls ∧ tgtMajor out c = R.g.cls.getD cls default ∧
      ConLeche.instPisWith (tgtMajor out c).ds (R.g.formerTys.getD cls default) = some ty ∧
      ConLeche.openPisAtFvars (tgtMajor out c).nIdx ty (p.toBlockShape.rulePrefixAt c)
        = some (ifs, body) ∧
      ifs.length = (tgtMajor out c).nIdx ∧
      p.toBlockShape.rulePrefixAt c = R.g.pre.length ∧
      p.toBlockShape.majorIdxAt c = p.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx ∧
      ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).map (·.2.2)).length
        = p.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx + 1 ∧
      (∀ (k : Nat) (x : Expr), ifs[k]? = some x →
        denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + k) x.fvarTypeD
          = some (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).map
              (·.2.2)).getD (p.toBlockShape.rulePrefixAt c + k) default)) ∧
      denoteMeta mpC.base2.acval envC ψ
          (p.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx)
          (Expr.mkAppN (.const (tgtMajor out c).ind (tgtMajor out c).lvls)
            ((tgtMajor out c).ds ++ ifs))
        = some (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).map
            (·.2.2)).getD (p.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx) default) ∧
      (∃ fvs o, ConLeche.openPisAtFvars (p.toBlockShape.majorIdxAt c + 1)
          ((tgtRs out)[c]'hc).1.type 0 = some (fvs, o) ∧
        ∀ (i : Nat) (x nd : Expr), fvs[i]? = some x →
          (R.g.pre ++ ifs.map R.g.binder ++ [(Expr.mkAppN (.const (tgtMajor out c).ind
            (tgtMajor out c).lvls) ((tgtMajor out c).ds ++ ifs), R.g.bm)])[i]?.map (·.1) = some nd →
          Expr.ErasedEq x.fvarTypeD nd) := by
  obtain ⟨cls, gty, S, hgc, hM, hgty, -, hread, hmI, hRP, hst⟩ :=
    genRun_storedTy hμ R hg h mpC ψ hc
  -- the stored constant is the generated type
  have hsty : ((tgtRs out)[c]'hc).1.type = gty := by
    obtain ⟨rc, cls', cvG, rhss, -, -, -, ⟨T⟩, ho, -, hgc'⟩ := genRun_at R hc
    obtain rfl : cls' = cls := hgc'.symm.trans hgc
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcvEq⟩ := ConLeche.classConstOk_inv T.hcv
    have hc' : c < out.length := by simpa [tgtRs] using hc
    have hr1 : ((tgtRs out)[c]'hc).1 = cvG := by
      have : out[c] = (cvG, R.Ms.getD cls' default, rhss) :=
        Option.some.inj ((List.getElem?_eq_getElem hc').symm.trans ho)
      simp [tgtRs, this]
    rw [hr1, hcvEq]
    show T.gty = gty
    exact Option.some.inj (T.hgty.symm.trans hgty)
  obtain ⟨ifs, maj, hmaj, hifl, rfl, hcl, hbb⟩ := ConLeche.classGenRecTy_spec hg hgty
  obtain ⟨ty, body, hty, hopI, hmajE⟩ := ConLeche.ClassGen.major_inv hmaj
  rw [← hM] at hty hopI hmajE hifl
  generalize hnds : R.g.pre ++ ifs.map R.g.binder ++ [(maj, R.g.bm)] = nds at hread hcl
  generalize hbody : Expr.mkAppN (R.g.motVar cls)
    (ifs ++ [.fvar (R.g.pre.length + ifs.length) maj]) = bd at hread hbb
  have hn : nds.length = R.g.pre.length + (tgtMajor out c).nIdx + 1 := by
    rw [← hnds]
    simp only [List.length_append, List.length_map, List.length_singleton, hifl]
  obtain ⟨fvs, o, hop, -, hdomE⟩ := open_of_erasedEq_closeTelescope nds 0 bd
    (closeTelescope nds 0 bd) hcl hbb (Expr.ErasedEq.rfl _)
  have hop0 := hop
  rw [hn] at hop
  obtain ⟨pps, b, hst', -, hlen, hbind⟩ := denoteMeta_openPis _ hop hread
  rw [← hM] at hst hmI
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hst.symm.trans hst'))
  have hlenF : fvs.length = R.g.pre.length + (tgtMajor out c).nIdx + 1 := by
    rw [ConLeche.Verify.openPisAtFvars_length _ hop]
  -- entry `i` of the stored binder data is the reading of `nds[i]`
  have hent : ∀ i nd, i < R.g.pre.length + (tgtMajor out c).nIdx + 1 →
      nds[i]?.map (·.1) = some nd →
      denoteMeta mpC.base2.acval envC ψ i nd
        = some (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).map
            (·.2.2)).getD i default) := by
    intro i nd hi hnd
    obtain ⟨x, hx⟩ : ∃ x, fvs[i]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨q, hq, -, hrd⟩ := hbind i x hx
    rw [Nat.zero_add, denoteMeta_erasedEq (hdomE i x nd hx hnd)] at hrd
    rw [hrd, List.getD_eq_getElem?_getD, List.getElem?_map, hq]
    rfl
  refine ⟨cls, ty, ifs, body, hgc, hM, hty, by rw [hRP]; exact hopI, hifl, hRP,
    by rw [hRP]; omega, by rw [List.length_map, hlen, hRP], ?_, ?_, ?_⟩
  · intro k x hx
    have hk : k < ifs.length := (List.getElem?_eq_some_iff.mp hx).1
    rw [hRP]
    refine hent _ _ (by omega) ?_
    rw [← hnds, List.append_assoc, List.getElem?_append_right (by omega),
      List.getElem?_append_left (by simp; omega), Nat.add_sub_cancel_left, List.getElem?_map, hx]
    rfl
  · rw [hRP, ← hmajE]
    refine hent _ _ (by omega) ?_
    rw [← hnds, List.getElem?_append_right (by simp; omega)]
    simp [hifl]
  · refine ⟨fvs, o, ?_, fun i x nd hx hnd => hdomE i x nd hx ?_⟩
    · rw [hsty, hmI, ← hn, hnds, hbody]; exact hop0
    · rw [← hnds, hmajE]; exact hnd

set_option maxHeartbeats 2000000 in
/-- **The class's instantiation `I lvls ds` is graded at every prefix
spine** — a head of the stored major domain's application spine
(`storedMajorSub_graded`: the stored type's own inference). -/
theorem genCls_inst_graded (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) p.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (ψ : Name → Nat) {c : Nat} (hc : c < (tgtRs out).length)
    (hds : ∀ x ∈ (tgtMajor out c).ds, ConLeche.ScB p.nP x)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) :
    ∃ w, denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c)
        (Expr.mkAppN (.const (tgtMajor out c).ind (tgtMajor out c).lvls) (tgtMajor out c).ds)
        = some w ∧
      ∀ σ : Nat → V,
        Sat V (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape (tgtRs out) ψ c).reverse σ →
        WellDenotedV V σ w := by
  obtain ⟨cls, ty, ifs, body, -, -, -, -, hifl, hRP, hmI, -, -, -, fvs, o, hop, hE⟩ :=
    genRun_binders hμ R hg h mpC ψ hc
  have hr : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  have hlenF : fvs.length = p.toBlockShape.majorIdxAt c + 1 :=
    ConLeche.Verify.openPisAtFvars_length _ hop
  obtain ⟨maj, hmaj⟩ : ∃ maj, fvs[p.toBlockShape.majorIdxAt c]? = some maj :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hmE := hE _ maj (Expr.mkAppN (.const (tgtMajor out c).ind (tgtMajor out c).lvls)
    ((tgtMajor out c).ds ++ ifs)) hmaj (by
    rw [List.getElem?_append_right (by simp; omega)]
    simp [hifl, hmI, hRP])
  rw [mkAppN_append'] at hmE
  obtain ⟨x, args, hdE, hxE, -⟩ := erasedEq_mkAppN_inv ifs hmE
  obtain ⟨hw0, -⟩ := recStage_tyClosed h hr
  have hwsM : Expr.WScoped (p.toBlockShape.majorIdxAt c) maj.fvarTypeD := by
    have := openPisAtFvars_typeWScoped _ hop hw0 _ maj hmaj
    rwa [Nat.zero_add] at this
  rw [hdE] at hwsM
  have hwsX : Expr.WScoped (p.toBlockShape.rulePrefixAt c) x :=
    WScoped.of_erasedEq x hxE (WScoped.mkAppN_head args hwsM)
      (Expr.WScoped.mkAppN (by simp only [Expr.WScoped]) fun y hy => (hds y hy).1.mono hnP)
  obtain ⟨w, hw, hgr⟩ := storedMajorSub_graded hμ mpC h hr ψ hop hmaj (.inr ⟨args, hdE⟩)
    (fun l hl => Expr.fvarLeaves_lt_of_wscoped hwsX l hl)
  rw [denoteMeta_erasedEq hxE] at hw
  exact ⟨w, hw, hgr⟩

end Binders

/-! ## A class's reading facts

Every class — a member (the block's own datum `d.toLfp`) or an outside
class (the container's recorded datum) — is ONE recorded lfp datum
`tgtClsD` at a member `tgtClsM` and a level assignment `tgtClsψ`, over
the key frame of its parameters `ds` read at the rule prefix
(`tgtOutDsa`).  `GenClsRd` collects what the readings of the generated
type and rules need of it; the member and outside cases produce it
separately. -/

section Record

variable {envC : Env}

variable (mpC : EnvModelM V μ envC) (d : BlockData V) (Dc : Nat → LfpDatum V) (mc : Nat → Nat)
  (cvc : Nat → ConstantVal) (pp : BlockParts)
  (out : List (ConstantVal × TargetMajor × List Expr)) in
/-- **Class `c`'s reading facts** (`cvI` its inductive's stored former). -/
structure GenClsRd (c : Nat) (cvI : ConstantVal) : Prop where
  hfind : ∃ caps, envC.find? (tgtMajor out c).ind = some (.indInfo cvI caps)
  hmem : (tgtClsD d Dc out c).member (tgtClsM mc pp.toBlockShape out c) = (tgtMajor out c).ind
  hD : tgtClsD d Dc out c ∈ mpC.lfpBlocks
  hmm : tgtClsM mc pp.toBlockShape out c < (tgtClsD d Dc out c).k
  hnN : (tgtClsD d Dc out c).names.Nodup
  hkN : (tgtClsD d Dc out c).names.length = (tgtClsD d Dc out c).k
  hnd : cvI.levelParams.Nodup
  hul : (tgtMajor out c).lvls.length = cvI.levelParams.length
  hψ : ∀ ψ, tgtClsψ cvc out ψ c = Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls
  hds : ∀ x ∈ (tgtMajor out c).ds, Expr.WScoped pp.nP x ∧ x.looseBVarsBounded 0 = true
  hlenP : ∀ ψ, ((tgtClsD d Dc out c).params (tgtClsψ cvc out ψ c)).length
    = (tgtMajor out c).ds.length
  hidsLen : ∀ ψ, ((tgtClsD d Dc out c).ids (tgtClsM mc pp.toBlockShape out c)
    (tgtClsψ cvc out ψ c)).length = (tgtMajor out c).nIdx
  hnIdx : tgtClsNIdx d pp.toBlockShape out c = (tgtMajor out c).nIdx
  hdsa : ∀ ψ, DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c)
    (tgtMajor out c).ds (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
  hG : ∀ ψ ρ xs, tgtClsG d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c ↔
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs
  hfr : ∀ ψ ρ xs, xs.length = tgtRP pp.toBlockShape c →
    tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
      = keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
          (tgtRP pp.toBlockShape c) (consList xs ρ)
  hsat : ∀ ψ ρ xs,
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs →
    Sat V ((tgtClsD d Dc out c).params (tgtClsψ cvc out ψ c)).reverse
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
        (tgtRP pp.toBlockShape c) (consList xs ρ))
  /-- the class's constructors are its datum's, stored at its parameter count -/
  hctor : ∀ j cA, (tgtMajor out c).ctors[j]? = some cA →
    j < (tgtClsD d Dc out c).nctors (tgtClsM mc pp.toBlockShape out c) ∧
    envC.find? ((tgtClsD d Dc out c).ctorName (tgtClsM mc pp.toBlockShape out c) j)
      = some (.ctorInfo cA.1 (tgtMajor out c).ds.length cA.2) ∧
    cA.1.levelParams = cvI.levelParams ∧
    ∀ mm, mm < (tgtClsD d Dc out c).k → ∃ cv caps,
      envC.find? ((tgtClsD d Dc out c).member mm) = some (.indInfo cv caps) ∧
        cv.levelParams = cvI.levelParams
  /-- the constructor at the class's levels -/
  hctorAt : ∀ cv : ConstantVal, cv.levelParams = cvI.levelParams →
    ConLeche.targetCtorAt (tgtMajor out c) cv
      = cv.type.instantiateLevelParams cv.levelParams (tgtMajor out c).lvls
  /-- the class's parameter count is its parameters' -/
  hnpc : (tgtMajor out c).nPc = (tgtMajor out c).ds.length

end Record


/-! ## The core: the index binders and the major, at a class -/

section Core

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

set_option maxHeartbeats 4000000 in
/-- **The index binders and the major of recursor `c`, at its class**: at
a prefix spine fitting the rule prefix, index values fit the stored index
binders exactly when they fit the class's recorded index telescope at the
key frame, and then the stored major domain reads as the class's carrier
at their tuple (`instFormer_read` for the index binders, `keyLeaf` for
the major). -/
theorem genCls_core (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {c : Nat} (hc : c < (tgtRs out).length) {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hformer : R.g.formerTys.getD (genClsOf R.rd c) default
      = cvI.type.instantiateLevelParams cvI.levelParams (tgtMajor out c).lvls)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hxl : xs.length = pp.toBlockShape.rulePrefixAt c)
    (hxfit : SpineFit ρ
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs) :
    (∀ is : List V,
      SpineFit (consList xs ρ)
          ((((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
            (·.2.2)).drop (pp.toBlockShape.rulePrefixAt c)).take (tgtMajor out c).nIdx) is ↔
        SpineFit (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
            (tgtRP pp.toBlockShape c) (consList xs ρ))
          ((tgtClsD d Dc out c).ids (tgtClsM mc pp.toBlockShape out c) (tgtClsψ cvc out ψ c))
          is) ∧
    (∀ is : List V,
      SpineFit (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
            (tgtRP pp.toBlockShape c) (consList xs ρ))
          ((tgtClsD d Dc out c).ids (tgtClsM mc pp.toBlockShape out c) (tgtClsψ cvc out ψ c))
          is →
      interp V (consList (xs ++ is) ρ)
          (((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
            (·.2.2)).getD (pp.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx) default)
        = app ((tgtClsD d Dc out c).carrier (tgtClsψ cvc out ψ c)
            (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
              (tgtRP pp.toBlockShape c) (consList xs ρ)) (tgtClsM mc pp.toBlockShape out c))
          (tupW ((tgtClsD d Dc out c).u (tgtClsM mc pp.toBlockShape out c)
            (tgtClsψ cvc out ψ c)) is)) := by
  obtain ⟨cls, ty, ifs, body, hgc, -, hty, hopI, hifl, -, -, hlenR, hidxR, hmajR, -⟩ :=
    genRun_binders hμ R hg h mpC ψ hc
  rw [hgc] at hformer
  rw [hformer] at hty
  obtain ⟨hfind, hmemR, hDin, hmmk, -, -, hndI, hulI, hψf, hdsS, hlenPf, hidsLf, -, hdsaf,
    -, -, -, -, -, -⟩ := Rd
  have hψc := hψf ψ
  have hdsa := hdsaf ψ
  have hlenP' := hlenPf ψ
  have hidsLen := hidsLf ψ
  generalize hD : tgtClsD d Dc out c = D at hmemR hDin hmmk hlenP' hidsLen ⊢
  generalize hmm : tgtClsM mc pp.toBlockShape out c = mm at hmemR hmmk hidsLen ⊢
  generalize hψD : tgtClsψ cvc out ψ c = ψc at hψc hlenP' hidsLen ⊢
  generalize hrP : pp.toBlockShape.rulePrefixAt c = rP at hxl hopI hidxR hmajR hlenR hnP ⊢
  have hRP : tgtRP pp.toBlockShape c = rP := hrP
  rw [hRP]
  rw [hRP] at hdsa
  generalize hdsaG : tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c = dsa at hdsa ⊢
  generalize hnI : (tgtMajor out c).nIdx = nI at hifl hmajR hlenR hidsLen ⊢
  obtain ⟨caps, hfI⟩ := hfind
  have hfM : envC.find? (D.member mm) = some (.indInfo cvI caps) := by rw [hmemR]; exact hfI
  -- the former strips its parameters
  obtain ⟨hC, -, hrd, -⟩ := mpC.lfp_ok D hDin
  obtain ⟨cv₂, caps₂, hf₂, hab⟩ := hrd mm hmmk
  rw [hfM] at hf₂
  obtain ⟨rfl, rfl⟩ : cvI = cv₂ ∧ caps = caps₂ := by simpa using hf₂
  obtain ⟨ab0, hta0, -, -⟩ := hab ψ
  have hstrip : (cvI.type.stripPis (tgtMajor out c).ds.length).isSome = true := by
    have hok := tailOk_of_read _ cvI.type rfl hta0
    obtain ⟨l1, -, l3⟩ := tail_instantiateLevelParams cvI.levelParams (tgtMajor out c).lvls cvI.type
    obtain ⟨k1, -⟩ := tail_instPisWith (tgtMajor out c).ds (l3.mpr hok) hty
    exact stripPis_isSome_of_piCount _ _ (by omega)
  have hds' : ∀ x ∈ (tgtMajor out c).ds, Expr.WScoped rP x ∧ x.looseBVarsBounded 0 = true :=
    fun x hx => ⟨(hdsS x hx).1.mono hnP, (hdsS x hx).2⟩
  rw [hψc] at hlenP' hidsLen
  obtain ⟨abR, hmapR, hread⟩ := instFormer_read mpC hDin hmmk hfM hndI hulI hlenP' hds'
    hdsa hstrip hty
  generalize hτ : substTau (tgtMajor out c).ds.length rP (fun i => dsa.getD i default) = τ
    at hread
  have hdl : dsa.length = (tgtMajor out c).ds.length := (DenoteMetaSpine.length_eq hdsa).symm
  have hkf : ∀ σ : Nat → V, keyFrame dsa rP σ = substE V τ 0 σ := fun σ => by
    rw [← hτ]; exact keyFrame_eq_substE hdl σ
  have hlenAbR : abR.length = nI := by rw [← hidsLen, ← hmapR, List.length_map]
  obtain ⟨pps, bI, hstI, -, -, hbindI⟩ := denoteMeta_openPis _ hopI hread
  rw [hnI, stripPisAV_mkPisAV_take _ _ _ (by rw [substTele_length]; omega)] at hstI
  have hppsE : pps = AnnotTerm.substTele τ 0 abR := by
    obtain ⟨h1, -⟩ := Prod.mk.inj (Option.some.inj hstI)
    rw [← h1, List.take_of_length_le (by rw [substTele_length]; omega)]
  subst hppsE
  generalize hRds : (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
    (·.2.2) = dR at hidxR hmajR hlenR ⊢
  -- the stored index entries ARE the opened former's
  have hIdxE : (dR.drop rP).take nI = (AnnotTerm.substTele τ 0 abR).map (·.2.2) := by
    refine List.ext_getElem (by simp [hlenR, substTele_length, hlenAbR]; omega) fun k h1 h2 => ?_
    have hk : k < nI := by simp [hlenR] at h1; omega
    obtain ⟨x, hx⟩ : ∃ x, ifs[k]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨q, hq, -, hrdq⟩ := hbindI k x hx
    have e1 := hidxR k x hx
    rw [hrdq] at e1
    have e2 : ((AnnotTerm.substTele τ 0 abR).map (·.2.2))[k] = q.2.2 := by
      simp [List.getElem_map, (List.getElem?_eq_some_iff.mp hq).2]
    rw [e2, List.getElem_take, List.getElem_drop]
    have := (Option.some.inj e1)
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have FitI : ∀ (σ : Nat → V) (zs : List V), SpineFit σ ((dR.drop rP).take nI) zs ↔
      SpineFit (keyFrame dsa rP σ) (D.ids mm ψc) zs := by
    intro σ zs
    rw [hIdxE, spineFit_substTele, ← hkf, hψc, ← hmapR]
  refine ⟨fun is => FitI _ is, fun is hisK => ?_⟩
  -- the major: graded along the stored type, then `keyLeaf`
  have hisl : is.length = nI := by rw [hisK.length_eq, hψc, hidsLen]
  obtain ⟨-, -, -, -, hTyE, hlenRds, -, -, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ
  have hwdR : ∀ ρ' : Nat → V, WellDenotedV V ρ'
      (mkPisAV (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
        (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)) :=
    fun ρ' => by rw [← hTyE]; exact hwdTy ρ'
  have hlenRR : (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = rP + nI + 1 := by rw [← hlenR, ← hRds, List.length_map]
  have hPd : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      = dR.take rP := by
    rw [blockRulePdomsAV, hrP, ← hRds, List.map_take]
  have hys : SpineFit ρ ((((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).take
      (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length).map
        (·.2.2)).take (rP + nI)) (xs ++ is) := by
    rw [List.take_length, hRds, List.take_add]
    rw [hPd] at hxfit
    exact SpineFit.append hxfit ((FitI _ is).mpr hisK)
  have hwd := prefixDoms_graded_of_tower (V := V) (Nat.le_refl _) hwdR
    (l := rP + nI) (by omega) hys
  rw [List.take_length, hRds] at hwd
  have hmajR' : denoteMeta mpC.base2.acval envC ψ (rP + nI)
      (Expr.mkAppN (.const (D.member mm) (tgtMajor out c).lvls) ((tgtMajor out c).ds ++ ifs))
      = some (dR.getD (rP + nI) default) := by rw [hmemR]; exact hmajR
  obtain ⟨-, isa, hisa, hleaf⟩ := keyLeaf mpC hDin hmmk hfM (b := rP) (Nat.le_add_right _ _)
    hmajR' hlenP'.symm (by rw [hifl, hidsLen]) (fun x hx => (hds' x hx).1) hdsa
  have hidxI := ConLeche.openPisAtFvars_index _ _ _ hopI
  have hisaE : isa = (List.range nI).map fun k => AnnotTerm.bvar (rP + nI - 1 - (rP + k)) := by
    have hF := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ) (rP + nI)
      ifs rP (fun k x hx => hidxI k x hx)
    rw [hifl] at hF
    exact DenoteMetaSpine.unique hisa hF
  have hvals : isa.map (interp V (consList (xs ++ is) ρ)) = is := by
    rw [hisaE]; exact map_fieldBvars hxl hisl
  obtain ⟨-, -, hmemE⟩ := hleaf _ hwd
  have hdrop : dropV (rP + nI - rP) (consList (xs ++ is) ρ) = consList xs ρ := by
    funext k
    rw [dropV, consList_append, show rP + nI - rP = is.length by rw [hisl]; omega,
      consList_apply_add]
  rw [hdrop, hvals, ← hψc] at hmemE
  exact hmemE

/-- The class's index set at a fitting prefix is its datum's at the key frame. -/
theorem genCls_Is_eq {c : Nat} {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (ψ : Name → Nat) (ρ : Nat → V) {xs : List V}
    (hxl : xs.length = tgtRP pp.toBlockShape c)
    (hxfit : SpineFit ρ
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs) :
    tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
      = (tgtClsD d Dc out c).idx (tgtClsψ cvc out ψ c)
          (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
            (tgtRP pp.toBlockShape c) (consList xs ρ)) (tgtClsM mc pp.toBlockShape out c) := by
  classical
  rw [tgtClsIs, if_pos ((Rd.hG ψ ρ xs).mpr hxfit), Rd.hfr ψ ρ xs hxl]

/-- The class's carrier at a fitting prefix is its datum's at the key frame. -/
theorem genCls_Cr_eq {c : Nat} {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (ψ : Name → Nat) (ρ : Nat → V) {xs : List V}
    (hxl : xs.length = tgtRP pp.toBlockShape c) :
    tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
      = (tgtClsD d Dc out c).carrier (tgtClsψ cvc out ψ c)
          (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
            (tgtRP pp.toBlockShape c) (consList xs ρ)) (tgtClsM mc pp.toBlockShape out c) := by
  rw [tgtClsCr, Rd.hfr ψ ρ xs hxl]

/-- A class's index set is guarded by the rule prefix's fit. -/
theorem genCls_Is_fits {c : Nat} {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    {ψ : Name → Nat} {ρ : Nat → V} {xs : List V} {i : V}
    (hi : i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs := by
  classical
  unfold tgtClsIs at hi
  by_cases hg : tgtClsG d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
  · exact (Rd.hG ψ ρ xs).mp hg
  · rw [if_neg hg] at hi; exact absurd hi (not_mem_empty _)

set_option maxHeartbeats 2000000 in
/-- **`GenClsSplit` at one class.** -/
theorem genCls_split (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {c : Nat} (hc : c < (tgtRs out).length) {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hformer : R.g.formerTys.getD (genClsOf R.rd c) default
      = cvI.type.instantiateLevelParams cvI.levelParams (tgtMajor out c).lvls)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ (xs is : List V) (x : V),
      xs.length = pp.toBlockShape.rulePrefixAt c → is.length = (tgtMajor out c).nIdx →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
          (·.2.2)) (xs ++ (is ++ [x])) →
      tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c is
          ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c ∧
        x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c)
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c is) ∧
        isOfW (tgtClsU d Dc mc cvc pp.toBlockShape out ψ c) (tgtClsNIdx d pp.toBlockShape out c)
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c is) = is := by
  intro xs is x hxl hisl hfit
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlenD, -, -, -⟩ := genRun_binders hμ R hg h mpC ψ hc
  obtain ⟨xs', is', x', heq, hxl', hisl', h1, h2, h3⟩ := spineFit_split_three hlenD hfit
  obtain ⟨rfl, heq2⟩ := List.append_inj heq (by rw [hxl, hxl'])
  obtain ⟨rfl, hxx⟩ := List.append_inj heq2 (by rw [hisl, hisl'])
  obtain rfl : x = x' := by simpa using hxx
  have hPd : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map (·.2.2)).take
          (pp.toBlockShape.rulePrefixAt c) := by
    rw [blockRulePdomsAV, List.map_take]
  rw [← hPd] at h1
  obtain ⟨hI, hM⟩ := genCls_core hμ R hg h hc Rd hformer hnP ψ ρ xs hxl h1
  have hisK := (hI is).mp h2
  have hmaj := hM is hisK
  have hxlR : xs.length = tgtRP pp.toBlockShape c := hxl
  rw [genCls_Is_eq Rd ψ ρ hxlR h1, genCls_Cr_eq Rd ψ ρ hxlR]
  refine ⟨tupW_mem hisK, ?_, ?_⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
      ← consList_append, hmaj] at h3
    exact h3
  · obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok _ Rd.hD
    have hIk := hC.idxOk _ _ (Rd.hsat ψ ρ xs h1) _ (Nat.lt_of_lt_of_le Rd.hmm hC.kN)
    have e := isOfW_tupW hIk hisK
    rw [Rd.hidsLen ψ] at e
    rw [Rd.hnIdx]
    exact e

set_option maxHeartbeats 2000000 in
/-- **`GenClsBack` at one class.** -/
theorem genCls_back (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {c : Nat} (hc : c < (tgtRs out).length) {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hformer : R.g.formerTys.getD (genClsOf R.rd c) default
      = cvI.type.instantiateLevelParams cvI.levelParams (tgtMajor out c).lvls)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ (xs : List V) (i x : V),
      i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) i →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
          (·.2.2))
        (xs ++ (isOfW (tgtClsU d Dc mc cvc pp.toBlockShape out ψ c)
          (tgtClsNIdx d pp.toBlockShape out c) i ++ [x])) := by
  intro xs i x hi hx
  have hxfit := genCls_Is_fits Rd hi
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hlenD, -, -, -⟩ := genRun_binders hμ R hg h mpC ψ hc
  have hlenPd := blockRulePdomsAV_length (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ
  have hxl : xs.length = pp.toBlockShape.rulePrefixAt c := by
    rw [hxfit.length_eq, hlenPd]
  have hxlR : xs.length = tgtRP pp.toBlockShape c := hxl
  rw [genCls_Is_eq Rd ψ ρ hxlR hxfit] at hi
  rw [genCls_Cr_eq Rd ψ ρ hxlR] at hx
  obtain ⟨is, hisK, rfl⟩ := mem_idxSet_elim hi
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok _ Rd.hD
  have hIk := hC.idxOk _ _ (Rd.hsat ψ ρ xs hxfit) _ (Nat.lt_of_lt_of_le Rd.hmm hC.kN)
  have hret := isOfW_tupW hIk hisK
  rw [Rd.hidsLen ψ] at hret
  rw [Rd.hnIdx]
  show SpineFit ρ _ (xs ++ (isOfW ((tgtClsD d Dc out c).u (tgtClsM mc pp.toBlockShape out c)
    (tgtClsψ cvc out ψ c)) _ _ ++ [x]))
  rw [hret]
  obtain ⟨hI, hM⟩ := genCls_core hμ R hg h hc Rd hformer hnP ψ ρ xs hxl hxfit
  generalize hDs : (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
    (·.2.2) = Ds at hlenD hI hM ⊢
  have hPd : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      = Ds.take (pp.toBlockShape.rulePrefixAt c) := by
    rw [blockRulePdomsAV, List.map_take, hDs]
  rw [hPd] at hxfit
  have hdrop : (Ds.drop (pp.toBlockShape.rulePrefixAt c)).length = (tgtMajor out c).nIdx + 1 := by
    rw [List.length_drop, hlenD]; omega
  have hD : Ds = Ds.take (pp.toBlockShape.rulePrefixAt c)
      ++ ((Ds.drop (pp.toBlockShape.rulePrefixAt c)).take (tgtMajor out c).nIdx
        ++ [(Ds.drop (pp.toBlockShape.rulePrefixAt c)).getD (tgtMajor out c).nIdx default]) := by
    rw [← list_drop_last hdrop, List.take_append_drop]
  rw [hD]
  refine SpineFit.append hxfit (SpineFit.append ((hI is).mpr hisK) ⟨?_, trivial⟩)
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD,
    ← consList_append, hM is hisK]
  exact hx

/-! ## The rule frame: the declared constructor at the class -/

set_option maxHeartbeats 4000000 in
/-- **The rule frame of `(c, j)`, read at the class** (`tgtOutOpen` +
`tgtOutCbody` + `tgtEsAV_outside` at the generated stage, member or
outside alike): the rule frame is the declared constructor at the class's
levels and parameters (`ClassCtorRun.hD`), so the field domains are the
datum's recorded fields substituted by `instTau`, the index expressions
are the recorded result indices substituted (`tgtOutEs`), and the fired
spine is the constructor at the class's parameters and the fields. -/
theorem genCls_open (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC [])
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) :
    ∃ (cA : ConstantVal × Nat) (ab : List (Nat × Nat × AnnotTerm)) (Tys : List AnnotTerm),
      (tgtMajor out c).ctors[j]? = some cA ∧ tgtCtorOf out c j = cA ∧
      j < (tgtClsD d Dc out c).nctors (tgtClsM mc pp.toBlockShape out c) ∧
      Tys.length = (tgtClsD d Dc out c).k ∧
      (∀ mm, mm < (tgtClsD d Dc out c).k → ∃ cvm caps,
        envC.find? ((tgtClsD d Dc out c).member mm) = some (.indInfo cvm caps) ∧
        denoteMeta mpC.base2.acval envC (tgtClsψ cvc out ψ c) 0 cvm.type
          = some (Tys.getD mm default)) ∧
      FieldsEqOn V ((tgtClsD d Dc out c).params (tgtClsψ cvc out ψ c) ++ Tys).reverse
        (ab.map (·.2.2))
        ((tgtClsD d Dc out c).fields (tgtClsψ cvc out ψ c) (tgtClsM mc pp.toBlockShape out c) j) ∧
      ab.length = cA.2 ∧
      tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
        = (AnnotTerm.substTele (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
            (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) 0 ab).map (·.2.2) ∧
      tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
        = tgtOutEs mpC (tgtClsD d Dc out c) (tgtClsM mc pp.toBlockShape out c) cvI.levelParams
            (tgtMajor out c) (tgtRP pp.toBlockShape c) ψ j ∧
      tgtB pp.toBlockShape out c j = tgtRP pp.toBlockShape c + cA.2 ∧
      tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j
        = (denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c + cA.2)
            (Expr.mkAppN (.const cA.1.name (tgtMajor out c).lvls)
              ((tgtMajor out c).ds ++ tgtFieldFvs pp.toBlockShape out c j))).getD default ∧
      (∀ (k : Nat) (x : Expr), (tgtFieldFvs pp.toBlockShape out c j)[k]? = some x →
        ∃ ty, x = .fvar (tgtRP pp.toBlockShape c + k) ty) ∧
      (tgtFieldFvs pp.toBlockShape out c j).length = cA.2 := by
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
  rw [Rd.hψ] at hlenP' ⊢
  rw [← hRP] at hop
  obtain ⟨-, ab, ⟨Tys, hlT, hTys, hEq⟩, hlab, hrdF, hrdL, hrdC, -⟩ :=
    instCtor_open mpC Rd.hD Rd.hnN Rd.hkN hlpsR Rd.hnd Rd.hul hds' (Rd.hdsa ψ) hlenP' Rd.hmm hjD
      hfc hcrD hop
  have hB : tgtB pp.toBlockShape out c j = tgtRP pp.toBlockShape c + cA.2 := by
    rw [tgtB, hctO]
  have hfdoms : tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
      = (AnnotTerm.substTele (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
          (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) 0 ab).map (·.2.2) := by
    rw [tgtFdomsAV, hFF, hrdF]
  have hcbE : tgtCbody pp.toBlockShape out c j = cb := hCB
  -- the conclusion's syntax (`LfpOwn.ctorConcl`)
  obtain ⟨cv₈, nPc₈, nF₈, hf₈, bs, args, hstrip, hlen⟩ :=
    (hcov.own _ Rd.hD).ctorConcl _ Rd.hmm j hjD
  rw [hfc] at hf₈
  obtain ⟨rfl, rfl, rfl⟩ : cA.1 = cv₈ ∧ (tgtMajor out c).ds.length = nPc₈ ∧ cA.2 = nF₈ := by
    injection hf₈ with h; injection h with h1 h2 h3; exact ⟨h1, h2, h3⟩
  have hP0 := piConcl_of_stripPis _ hstrip rfl
  have hP1 := piConcl_instantiateLevelParams cA.1.levelParams (tgtMajor out c).lvls _ _ hP0
  rw [map_param_subst (by rw [hlpC]; exact Rd.hnd) (by rw [hlpC]; exact Rd.hul)] at hP1
  have hP2 := piConcl_instPisWith (tgtMajor out c).ds hP1 hcrD
  obtain ⟨cargs, hcE, -⟩ := piConcl_open _ hP2 hop
  -- the index expressions
  have hes : tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
      = tgtOutEs mpC (tgtClsD d Dc out c) (tgtClsM mc pp.toBlockShape out c) cvI.levelParams
          (tgtMajor out c) (tgtRP pp.toBlockShape c) ψ j := by
    obtain ⟨caps, hfI⟩ := Rd.hfind
    have hrd := hrdC
    rw [hcE] at hrd
    obtain ⟨fa, vs, hfa, hvs, heq⟩ := denoteMeta_mkAppN_inv hrd
    rw [Rd.hmem, denoteMeta_const (ci := .indInfo cvI caps) hfI Rd.hul] at hfa
    obtain rfl := Option.some.inj hfa
    obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok _ Rd.hD
    have hmmk := Rd.hmm
    have hhead : AnnotTerm.substAV (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
          (tgtRP pp.toBlockShape c) (tgtMajor out c).ds)
          (.bvar (cA.2 + ((tgtClsD d Dc out c).k - 1 - tgtClsM mc pp.toBlockShape out c))) cA.2
        = mpC.base2.acval (tgtMajor out c).ind
            (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls) := by
      rw [AnnotTerm.substAV_bvar_ge _ (by omega),
        show cA.2 + ((tgtClsD d Dc out c).k - 1 - tgtClsM mc pp.toBlockShape out c) - cA.2
          = (tgtClsD d Dc out c).k - 1 - tgtClsM mc pp.toBlockShape out c by omega,
        instTau, substTau, if_pos (by omega), grpX, grpS, if_neg (by omega),
        show (tgtMajor out c).ds.length + (tgtClsD d Dc out c).k - 1
            - ((tgtClsD d Dc out c).k - 1 - tgtClsM mc pp.toBlockShape out c)
            - (tgtMajor out c).ds.length = tgtClsM mc pp.toBlockShape out c by omega,
        grpSub_none (by simp), Option.getD_none, Rd.hmem,
        denoteMeta_const (ci := .indInfo cvI caps) hfI Rd.hul, Option.getD_some]
      exact liftN_eq_self_of_closed (mpC.base2.cval_closedL _ _) 0 _
    rw [AnnotTerm.substAV_mkAppN, hhead] at heq
    have hvsE := AnnotTerm.mkAppN_inj_head heq.symm
    have hvsM := denoteMetaSpine_eq_map hvs
    rw [tgtEsAV, hcbE, hcE, Expr.getAppArgs_mkAppN, hB]
    rw [show ∀ (n : Name) (us : List Level), (Expr.const n us).getAppArgs = [] from
      fun _ _ => rfl, List.nil_append]
    rw [List.map_drop, ← hvsM, hvsE, List.map_append, List.drop_left'
      (by rw [List.length_map, List.length_map, List.length_range, Rd.hnpc]), tgtOutEs,
      List.getD_eq_getElem?_getD, hcA, Option.getD_some]
  refine ⟨cA, ab, Tys, hcA, hctO, hjD, hlT, hTys, hEq, hlab, hfdoms, hes, hB, ?_, ?_, ?_⟩
  · rw [tgtMkAV, hctO, hB]
  · rw [hFF]; exact ConLeche.openPisAtFvars_index _ _ _ hop
  · rw [hFF]; exact ConLeche.Verify.openPisAtFvars_length _ hop

set_option maxHeartbeats 4000000 in
/-- **The decoding at the rule frame, at one class** (`GenClsDec`'s body):
`instCtor_decode` at the class's datum, through the rule frame's reading
(`genCls_open`). -/
theorem genCls_dec (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC []) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs fs : List V,
    xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) →
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
        (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
          ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ)))) j fs ∧
      tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
          ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ)))
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c ∧
      isOfW (tgtClsU d Dc mc cvc pp.toBlockShape out ψ c) (tgtClsNIdx d pp.toBlockShape out c)
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) ρ))))
        = (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ)) ∧
      interp V (consList (xs ++ fs) ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j)
        = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs ∧
      tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs
        ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c)
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) ρ)))) := by
  intro xs fs hxl hfit
  obtain ⟨as₁, as₂, heq, hpref, hfF⟩ := spineFit_append_inv hfit
  have hl₁ : as₁.length = xs.length := by rw [hpref.length_eq, hxl]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl₁
  have hlenPd := blockRulePdomsAV_length (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ
  have hxlR : as₁.length = tgtRP pp.toBlockShape c := by rw [hxl, hlenPd]; rfl
  obtain ⟨cA, ab, Tys, hcA, hctO, hjD, hlT, hTys, hEq, hlab, hfdoms, hes, hB, hmkE, hFvs, hFl⟩ :=
    genCls_open hμ R hg hcov hc hj Rd hnP ψ
  obtain ⟨-, hfc, hlpC, hlpsR⟩ := Rd.hctor j cA hcA
  have hsat := Rd.hsat ψ ρ as₁ hpref
  have hds' : ∀ x ∈ (tgtMajor out c).ds, Expr.WScoped (tgtRP pp.toBlockShape c) x ∧
      x.looseBVarsBounded 0 = true :=
    fun x hx => ⟨(Rd.hds x hx).1.mono hnP, (Rd.hds x hx).2⟩
  have hlenP' := Rd.hlenP ψ
  have hψc := Rd.hψ ψ
  rw [hψc] at hlenP' hsat hTys hEq
  rw [hfdoms] at hfF
  obtain ⟨hIdsF, hHF, hleaf⟩ := instCtor_decode mpC Rd.hD Rd.hnN Rd.hkN hlpsR Rd.hnd Rd.hul
    hds' (Rd.hdsa ψ) hlenP' Rd.hmm hjD hlT hTys hEq hlab hsat hfF
  have hfl : as₂.length = cA.2 := by
    rw [hfF.length_eq, List.length_map, substTele_length, hlab]
  -- the index expressions' values
  have hES : (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
        (interp V (consList (as₁ ++ as₂) ρ))
      = ((tgtClsD d Dc out c).resIdx (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
          (tgtClsM mc pp.toBlockShape out c) j).map fun e =>
          interp V (consList as₂ (consList as₁ ρ))
            (AnnotTerm.substAV (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
              (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) e cA.2) := by
    rw [hes, tgtOutEs, List.map_map, consList_append, List.getD_eq_getElem?_getD, hcA,
      Option.getD_some]
    rfl
  -- the fired spine
  have hname : cA.1.name = (tgtClsD d Dc out c).ctorName (tgtClsM mc pp.toBlockShape out c) j :=
    Env.find?_name hfc
  have hconst : denoteMeta mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c + cA.2)
      (.const cA.1.name (tgtMajor out c).lvls)
      = some (mpC.base2.acval cA.1.name
          (Level.substFn ψ cA.1.levelParams (tgtMajor out c).lvls)) := by
    rw [hname]
    exact denoteMeta_const (ci := .ctorInfo cA.1 _ cA.2) hfc
      (by show _ = cA.1.levelParams.length; rw [hlpC]; exact Rd.hul)
  have hdsaL : DenoteMetaSpine mpC.base2.acval envC ψ (tgtRP pp.toBlockShape c + cA.2)
      (tgtMajor out c).ds
      ((tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).map (AnnotTerm.liftN cA.2 · 0)) :=
    denoteMetaSpine_liftD mpC.base2.acval_closed (Rd.hdsa ψ) (fun x hx => (hds' x hx).1) cA.2
  have hspF := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    (tgtRP pp.toBlockShape c + cA.2) (tgtFieldFvs pp.toBlockShape out c j)
    (tgtRP pp.toBlockShape c) hFvs
  rw [hFl] at hspF
  have hmk : interp V (consList (as₁ ++ as₂) ρ)
      (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j)
      = (tgtClsD d Dc out c).inj (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)
          (tgtClsM mc pp.toBlockShape out c) j as₂ := by
    rw [hmkE, denoteMeta_mkAppN_of _ hconst (DenoteMetaSpine.append hdsaL hspF),
      Option.getD_some, interp_mkAppN, foldl_app_map, List.map_append,
      map_fieldBvars hxlR hfl, List.map_map]
    have hmapD : (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).map
          (interp V (consList (as₁ ++ as₂) ρ) ∘ fun x => AnnotTerm.liftN cA.2 x 0)
        = (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c).map
          (interp V (consList as₁ ρ)) := by
      refine List.map_congr_left fun x _ => ?_
      show interp V (consList (as₁ ++ as₂) ρ) (x.liftN cA.2 0) = _
      rw [consList_append, ← hfl, interp_liftN_consList]
    rw [hmapD, acval_interp_closed mpC.base2 _ _ _ (consList as₁ ρ), hname, hlpC]
    exact hleaf
  -- the class data at the key frame
  have hfr := Rd.hfr ψ ρ as₁ hxlR
  have hIs := genCls_Is_eq Rd ψ ρ hxlR hpref
  have hCr := genCls_Cr_eq Rd ψ ρ hxlR
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok _ Rd.hD
  have hmN := Nat.lt_of_lt_of_le Rd.hmm hC.kN
  rw [← hψc] at hIdsF hHF hmk hES
  have hsat' : Sat V ((tgtClsD d Dc out c).params (tgtClsψ cvc out ψ c)).reverse
      (keyFrame (tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c)
        (tgtRP pp.toBlockShape c) (consList as₁ ρ)) := by rw [hψc]; exact hsat
  have hIk := hC.idxOk _ _ hsat' _ hmN
  have hret := isOfW_tupW hIk hIdsF
  rw [Rd.hidsLen ψ] at hret
  have htupE : tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
      ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
        (interp V (consList (as₁ ++ as₂) ρ)))
      = tupW ((tgtClsD d Dc out c).u (tgtClsM mc pp.toBlockShape out c) (tgtClsψ cvc out ψ c))
          (((tgtClsD d Dc out c).resIdx (tgtClsψ cvc out ψ c)
            (tgtClsM mc pp.toBlockShape out c) j).map fun e =>
            interp V (consList as₂ (consList as₁ ρ))
              (AnnotTerm.substAV (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
                (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) e cA.2)) := by
    rw [hES]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [htupE, tgtClsFit, hfr]; exact hHF
  · rw [htupE, hIs]; exact tupW_mem hIdsF
  · rw [htupE, Rd.hnIdx, hES]; exact hret
  · rw [hmk]; rfl
  · rw [htupE, hCr]
    obtain ⟨hmono, -, hcl⟩ := hC.functor _ _ hsat'
    exact lfpTuple_closed hcl hmono _ hmN _ (tupW_mem hIdsF) _
      ((hC.fibre _ _ hsat' _ (lfpTuple_mem _ _ _ _) _ hmN _
        (tupW_mem hIdsF) _).mpr ⟨j, as₂, hHF, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- **The decoding's inverse, at one class** (`GenClsDecInv`'s body): a
hole fit at a tuple of the index set fits the rule's declared field
domains (`instCtor_fit`), and the tuple is the index expressions'
readings' (the hole fit's result indices ARE the tuple's components). -/
theorem genCls_decInv (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) (hcov : LfpCover mpC []) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hnP : pp.nP ≤ pp.toBlockShape.rulePrefixAt c) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ (xs : List V) (i : V) (fs : List V),
    i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c i j fs →
    SpineFit (consList xs ρ) (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) fs ∧
    i = tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
      ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
        (interp V (consList (xs ++ fs) ρ))) := by
  intro xs i fs hi hf
  have hpref := genCls_Is_fits Rd hi
  have hlenPd := blockRulePdomsAV_length (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ
  have hxlR : xs.length = tgtRP pp.toBlockShape c := by rw [hpref.length_eq, hlenPd]; rfl
  rw [genCls_Is_eq Rd ψ ρ hxlR hpref] at hi
  rw [tgtClsFit, Rd.hfr ψ ρ xs hxlR] at hf
  obtain ⟨cA, ab, Tys, hcA, hctO, hjD, hlT, hTys, hEq, hlab, hfdoms, hes, -, -, -, -⟩ :=
    genCls_open hμ R hg hcov hc hj Rd hnP ψ
  obtain ⟨-, -, -, hlpsR⟩ := Rd.hctor j cA hcA
  have hsat := Rd.hsat ψ ρ xs hpref
  have hds' : ∀ x ∈ (tgtMajor out c).ds, Expr.WScoped (tgtRP pp.toBlockShape c) x ∧
      x.looseBVarsBounded 0 = true :=
    fun x hx => ⟨(Rd.hds x hx).1.mono hnP, (Rd.hds x hx).2⟩
  have hlenP' := Rd.hlenP ψ
  have hψc := Rd.hψ ψ
  have hsat' := hsat
  rw [hψc] at hlenP' hsat' hTys hEq
  obtain ⟨hF, hI⟩ := instCtor_fit mpC Rd.hD Rd.hnN Rd.hkN hlpsR Rd.hnd Rd.hul hds' (Rd.hdsa ψ)
    hlenP' Rd.hmm hjD hlT hTys hEq hlab hsat'
  rw [← hψc] at hF hI
  have hfit : SpineFit (consList xs ρ)
      ((AnnotTerm.substTele (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
        (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) 0 ab).map (·.2.2)) fs :=
    (hF fs).mpr hf.2.1
  refine ⟨by rw [hfdoms]; exact hfit, ?_⟩
  obtain ⟨hIdsF, -, -⟩ := instCtor_decode mpC Rd.hD Rd.hnN Rd.hkN hlpsR Rd.hnd Rd.hul hds'
    (Rd.hdsa ψ) hlenP' Rd.hmm hjD hlT hTys hEq hlab hsat' hfit
  rw [← hψc] at hIdsF
  obtain ⟨is0, his0, rfl⟩ := mem_idxSet_elim hi
  obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok _ Rd.hD
  have hIk := hC.idxOk _ _ hsat _ (Nat.lt_of_lt_of_le Rd.hmm hC.kN)
  have hES : (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
        (interp V (consList (xs ++ fs) ρ))
      = ((tgtClsD d Dc out c).resIdx (tgtClsψ cvc out ψ c)
          (tgtClsM mc pp.toBlockShape out c) j).map fun e =>
          interp V (consList fs (consList xs ρ))
            (AnnotTerm.substAV (instTau mpC ψ (tgtClsD d Dc out c) (tgtMajor out c).lvls
              (tgtRP pp.toBlockShape c) (tgtMajor out c).ds) e cA.2) := by
    rw [hes, tgtOutEs, List.map_map, consList_append, List.getD_eq_getElem?_getD, hcA,
      Option.getD_some, hψc]
    rfl
  show _ = tupW _ _
  rw [hES]
  congr 1
  have hlenI := hIdsF.length_eq
  rw [List.length_map] at hlenI
  refine List.ext_getElem (by rw [List.length_map, hlenI, his0.length_eq]) fun l h1 h2 => ?_
  have hl : l < ((tgtClsD d Dc out c).ids (tgtClsM mc pp.toBlockShape out c)
      (tgtClsψ cvc out ψ c)).length := by rw [← his0.length_eq]; exact h1
  obtain ⟨e, he, hev⟩ := hf.2.2 l hl
  have hlr : l < ((tgtClsD d Dc out c).resIdx (tgtClsψ cvc out ψ c)
      (tgtClsM mc pp.toBlockShape out c) j).length := by rw [hlenI]; exact hl
  have heE : ((tgtClsD d Dc out c).resIdx (tgtClsψ cvc out ψ c)
      (tgtClsM mc pp.toBlockShape out c) j)[l] = e :=
    Option.some.inj ((List.getElem?_eq_getElem hlr).symm.trans he)
  rw [List.getElem_map, heE, hI fs hfit e (List.mem_of_getElem? he), hev,
    projS_tupW hIk his0 hl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    Option.getD_some]

end Core

end ConLeche.Model
