module

public import ConLeche.Model.Inductives.GenClsRows
import ConLeche.Model.Inductives.GenClsMinor
import ConLeche.Model.Inductives.GenRecPins
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Rules.Sound
import ConLeche.Model.IndFrame
import ConLeche.Model.Tiers
import ConLeche.Model.Capstone
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Deep
import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Semantics.Tower.FixTower

public section

/-!
# Terms of the rule frame, graded by the stored type's inference (lane GENREC-CLS)

A term whose free variables are the rule frame's openers — the stored
recursor type's prefix openers and the declared fields opened at the rule
prefix — and which the kernel INFERS at the frame's depth is graded at
every spine fitting the frame (`graded_of_infer_openers`: the frame's
context is `CtxOk` by its openers' readings and the frame's own grading,
and the inference is sound).

The inferences come from the stored recursor type's own (`classConstOk`):
the minor premise's prefix entry is inferred at its slot, hence — it is
scoped there — at the rule prefix, where it opens to the declared fields,
the inductive hypotheses and the conclusion `motive es (C ds f⃗)`, each
inferred at its depth.
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

section Kit

/-- **A successful inference of a telescope infers every opened domain**,
at its own depth. -/
theorem inferTypeCore_openPis_dom (hμ : μ.verifiedChecks = true) {envK : Env} {F : Nat}
    {n d : Nat} {e s : Expr} {fvs : List Expr} {o : Expr}
    (hop : openPisAtFvars n e d = some (fvs, o))
    (hinf : ConLeche.inferTypeCore μ envK F d e = .ok s) :
    ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      ∃ t, ConLeche.inferTypeCore μ envK F (d + i) x.fvarTypeD = .ok t := by
  intro i x hx
  have hi : i < fvs.length := (List.getElem?_eq_some_iff.mp hx).1
  have hn : fvs.length = n := ConLeche.Verify.openPisAtFvars_length _ hop
  obtain ⟨fA, fB, o₀, hA, hB, hfe⟩ := openPisAtFvars_split i (m := n - i)
    (by rw [show i + (n - i) = n by omega]; exact hop)
  have hAl : fA.length = i := ConLeche.Verify.openPisAtFvars_length _ hA
  have hBl : fB.length = n - i := ConLeche.Verify.openPisAtFvars_length _ hB
  obtain ⟨k, hk⟩ : ∃ k, n - i = k + 1 := ⟨n - i - 1, by omega⟩
  rw [hk] at hB
  obtain ⟨dom, bd, mb, rfl⟩ : ∃ dom bd mb, o₀ = .forallE dom bd mb := by
    match o₀, hB with
    | .forallE dom bd mb, _ => exact ⟨dom, bd, mb, rfl⟩
  have hxE : x = .fvar (d + i) dom := by
    simp only [openPisAtFvars] at hB
    split at hB
    · next fvs' o' _ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hB
      obtain ⟨rfl, -⟩ := hB
      rw [hfe, List.getElem?_append_right (by omega), hAl, Nat.sub_self] at hx
      simpa using hx.symm
    · exact nomatch hB
  have hdomInf : ∃ t, ConLeche.inferTypeCore μ envK F (d + i) dom = .ok t := by
    cases i with
    | zero =>
      simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hA
      obtain ⟨-, rfl⟩ := hA
      rw [Nat.add_zero]
      exact ConLeche.inferTypeCore_forallE_dom' hinf
    | succ k =>
      obtain ⟨bt, -, hbt, -⟩ := inferTypeCore_openPis_body hμ k hA hinf
      exact ConLeche.inferTypeCore_forallE_dom' hbt
  rw [hxE]
  exact hdomInf

/-- **A term the kernel infers over a frame of openers is graded at every
spine fitting the frame**: the openers' types read as the frame's
domains, which are graded along their fitting spines. -/
theorem graded_of_infer_openers (hμ : μ.verifiedChecks = true) {envC : Env}
    (mpC : EnvModelM V μ envC) (ψ : Name → Nat) {F D : Nat} {fr : List Expr}
    {doms : List AnnotTerm} (hdl : doms.length = D)
    (hshape : ∀ (i : Nat) (x : Expr), fr[i]? = some x → ∃ ty, x = Expr.fvar i ty)
    (hws : ∀ x ∈ fr, Expr.WScoped D x)
    (hlb : ∀ x ∈ fr, (Expr.fvarTypeD x).looseBVarsBounded 0 = true)
    (hdoms : ∀ (i : Nat) (x : Expr), fr[i]? = some x →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD x) = some (doms.getD i default))
    (hok : ∀ l, l < D → ∀ (σ : Nat → V) (ys : List V), SpineFit σ (doms.take l) ys →
      WellDenotedV V (consList ys σ) (doms.getD l default))
    {e t : Expr} (hinf : ConLeche.inferTypeCore μ envC F D e = .ok t)
    (hwsE : Expr.WScoped D e) (hbE : e.looseBVarsBounded 0 = true)
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fr) :
    ∃ w, denoteMeta mpC.base2.acval envC ψ D e = some w ∧
      ∀ (σ : Nat → V) (ys : List V), SpineFit σ doms ys → WellDenotedV V (consList ys σ) w := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hLX : Expr.LeavesBounded e := leavesBounded_of_openers hlb hleaf
  have hltE : ∀ l ∈ e.fvarLeaves, l.1 < D := fun l hl => Expr.fvarLeaves_lt_of_wscoped hwsE l hl
  have hent : ∀ i, i < D → doms.reverse[D - 1 - i]? = some (doms.getD i default) := by
    intro i hi
    rw [List.getElem?_reverse (by omega), hdl, show D - 1 - (D - 1 - i) = i by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hCE : CtxOk mpC.base2 ψ D doms.reverse e :=
    ctxOk_of_openers mpC.base2.acval_closed (Aa := fun i => doms.getD i default)
      (by rw [List.length_reverse, hdl]) hshape hws hdoms hleaf hltE hent
      (fun i hi ρ hρ => by
        have hs := Sat_drop hρ (D - i)
        have hdrop : doms.reverse.drop (D - i) = (doms.take i).reverse := by
          rw [List.drop_reverse, hdl, show D - (D - i) = i by omega]
        rw [hdrop] at hs
        have hsp := spineFit_frameIdx_of_sat hs
        have hc := consList_frameIdx (V := V) (doms.take i).length (fun j => ρ (j + (D - i)))
        have hw := hok i hi _ _ hsp
        rw [hc] at hw
        rw [show (fun j => ρ (j + (D - 1 - i) + 1)) = (fun j => ρ (j + (D - i))) by
          funext j; congr 1; omega]
        exact hw)
  obtain ⟨wa, hwa⟩ := acceptedReads_of mpC.base2 ψ hinf hwsE hbE hLX
  obtain ⟨-, -, -, -, hgr, -⟩ :=
    Rules.infer_sound (Rules.RulesInputs.ofSem mpC ψ) (Rules.inferTypeCore_bridge hinf)
      ⟨hwsE, hbE, hLX⟩ hCE hwa
  refine ⟨wa, hwa, fun σ ys hys => hgr _ ?_⟩
  have := sat_of_spineFit (Δ₀ := ([] : List AnnotTerm)) (Sat_nil V σ) hys
  simpa using this

end Kit

/-! ## The minor premise, opened at the rule frame -/

section Open

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 8000000 in
/-- **The minor premise of `(c, j)`, opened at the rule frame, with its
inferences**: the stored type's openers (their readings the rule
prefix's domains), and the minor premise's prefix entry — inferred at its
slot, hence at the rule prefix — opened there to the declared fields and
the inductive hypotheses (their types erasure-equal to the generator's)
and the conclusion; every opened domain and the conclusion inferred, all
leaves among the openers. -/
theorem genMinorOpen (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) {c j : Nat} (hc : c < (tgtRs out).length)
    (hj : j < blockRecNCt (tgtRs out) c) :
    ∃ (cls s : Nat) (x : ClassCtor) (res : Expr) (ws : List Expr)
      (ihs : List (Expr × BinderMeta)) (fvs1 : List Expr) (o1 : Expr) (xs' : List Expr)
      (rest : Expr),
      genClsOf R.rd c = cls ∧ genCtorAt R.g R.rd c j = x ∧ genMinorSlot R.g R.rd c j = s ∧
      x ∈ R.g.ctors.getD cls [] ∧ tgtMajor out c = R.g.cls.getD cls default ∧
      pp.toBlockShape.rulePrefixAt c = R.g.pre.length ∧ R.g.nP + s < R.g.pre.length ∧
      ConLeche.openPisAtFvars x.nF x.tyD R.g.pre.length
        = some (tgtFieldFvs pp.toBlockShape out c j, res) ∧
      tgtCbody pp.toBlockShape out c j = res ∧ (tgtCtorOf out c j).2 = x.nF ∧
      (tgtCtorOf out c j).1 = x.cv ∧
      ConLeche.targetPiDomsWith (tgtFieldFvs pp.toBlockShape out c j) x.tyN = some ws ∧
      ihs.length = x.recs.length ∧
      (∀ (l i t tele : Nat), x.recs[l]? = some (i, t, tele) →
        (∃ ty, R.g.ihTy t tele (ws.getD i default)
          ((tgtFieldFvs pp.toBlockShape out c j).getD i default)
          (R.g.pre.length + x.nF + l) = some ty ∧ ihs[l]? = some (ty, R.g.bm)) ∧
        (∃ n, ConLeche.classRecOf R.rd.recCls R.cvGs t = some n) ∧
        (∃ xs idx, R.g.ihParts t tele (ws.getD i default) (R.g.pre.length + x.nF)
          = some (xs, idx)) ∧
        ∃ st, ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ t = some st ∧ st < s) ∧
      (∃ sc, ConLeche.ClassRead.motiveSlot ⟨R.g.slots, []⟩ cls = some sc ∧ sc < s) ∧
      -- the stored type's openers
      ConLeche.openPisAtFvars (pp.toBlockShape.majorIdxAt c + 1) ((tgtRs out)[c]'hc).1.type 0
        = some (fvs1, o1) ∧
      R.g.pre.length ≤ pp.toBlockShape.majorIdxAt c ∧
      fvs1.length = pp.toBlockShape.majorIdxAt c + 1 ∧
      (∀ (i : Nat) (y : Expr), fvs1[i]? = some y → ∃ ty, y = Expr.fvar i ty) ∧
      (∀ y ∈ fvs1, Expr.WScoped (pp.toBlockShape.majorIdxAt c + 1) y ∧
        (Expr.fvarTypeD y).looseBVarsBounded 0 = true) ∧
      (∀ (i : Nat) (y : Expr), i < R.g.pre.length → fvs1[i]? = some y →
        denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD y)
          = some ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD i
              default)) ∧
      -- the minor premise, opened at the rule prefix
      xs'.length = x.nF + ihs.length ∧
      (∀ (k : Nat) (y : Expr), xs'[k]? = some y → ∃ ty, y = Expr.fvar (R.g.pre.length + k) ty) ∧
      (∀ y ∈ xs', Expr.WScoped (R.g.pre.length + x.nF + ihs.length) y ∧
        (Expr.fvarTypeD y).looseBVarsBounded 0 = true) ∧
      (∀ (k : Nat) (y : Expr), k < x.nF → xs'[k]? = some y →
        Expr.ErasedEq (Expr.fvarTypeD y)
          (Expr.fvarTypeD ((tgtFieldFvs pp.toBlockShape out c j).getD k default))) ∧
      (∀ (l : Nat) (y : Expr), xs'[x.nF + l]? = some y →
        Expr.ErasedEq (Expr.fvarTypeD y) ((ihs.getD l default).1)) ∧
      Expr.ErasedEq rest
        (Expr.mkAppN (R.g.motVar cls) (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
          [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
            ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])) ∧
      (∀ (k : Nat) (y : Expr), xs'[k]? = some y →
        ∃ t, ConLeche.inferTypeCore μ envC F (R.g.pre.length + k) (Expr.fvarTypeD y) = .ok t) ∧
      (∃ t, ConLeche.inferTypeCore μ envC F (R.g.pre.length + x.nF + ihs.length) rest = .ok t) ∧
      Expr.WScoped (R.g.pre.length + x.nF + ihs.length) rest ∧ rest.looseBVarsBounded 0 = true ∧
      (∀ l, (l ∈ rest.fvarLeaves ∨ ∃ y ∈ xs', l ∈ y.fvarLeaves) →
        Expr.fvar l.1 l.2 ∈ fvs1.take R.g.pre.length ++ xs') := by
  obtain ⟨cls, s, x, T, res, ws, ihs, hgc, hgx, hms, hxmem, hMaj, ⟨ihs0, hsS⟩, hpreT, hTs, hrP,
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, ⟨sc, hmc, hscl⟩, hTE⟩ := genMinorSetup R hg h hfind hc hj
  have hr : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  have hpl : R.g.pre.length = R.g.nP + R.g.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hsl : s < R.g.slots.length := (List.getElem?_eq_some_iff.mp hsS).1
  have hmp : R.g.nP + s < R.g.pre.length := by omega
  -- the stored type's openers
  obtain ⟨cls', ty', ifs', body', -, -, -, -, -, -, -, -, -, -, fvs0, o0, hop0, hE⟩ :=
    genRun_binders hμ R hg h mpC ψ hc
  obtain ⟨fvs1, concl1, hop1, -, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h hr ψ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop1.symm.trans hop0))
  have hle := blockRecHrPle (p := pp) h hc
  have hlenF : fvs1.length = pp.toBlockShape.majorIdxAt c + 1 :=
    ConLeche.Verify.openPisAtFvars_length _ hop1
  obtain ⟨hw0, hb0⟩ := recStage_tyClosed h hr
  have hwsF := (openPisAtFvars_WScoped _ _ 0 hop1 hw0).1
  have hbF := (ConLeche.Verify.openPisAtFvars_bounded _ hop1 hb0).2
  have hshF : ∀ (i : Nat) (y : Expr), fvs1[i]? = some y → ∃ ty, y = Expr.fvar i ty := by
    intro i y hy
    obtain ⟨ty, hty⟩ := openPisAtFvars_index _ _ 0 hop1 i y hy
    exact ⟨ty, by simpa using hty⟩
  have hlenPd := blockRulePdomsAV_length (V := V) hμ mpC h hr ψ
  have hPd : ∀ (i : Nat) (y : Expr), i < R.g.pre.length → fvs1[i]? = some y →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD y)
        = some ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD i
            default) := by
    intro i y hi hy
    obtain ⟨pd, hpd, -, hrd⟩ := hdomsR i y hy
    rw [hrd, blockRulePdomsAV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      if_pos (by rw [hrP]; exact hi), hpd]
    rfl
  -- the minor's entry: erasure-equal to the generator's, inferred at its slot
  obtain ⟨y, hy⟩ : ∃ y, fvs1[R.g.nP + s]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hyE := hE _ y T hy (by
    rw [List.append_assoc, List.getElem?_append_left (by omega), hpreT]; rfl)
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  obtain ⟨stype, -, hinfT, -⟩ := TE.hcv.sorted
  obtain ⟨tT, htT⟩ := inferTypeCore_openPis_dom hμ hop1 hinfT (R.g.nP + s) y hy
  rw [Nat.zero_add] at htT
  have hwsY : Expr.WScoped (R.g.nP + s) (Expr.fvarTypeD y) := by
    have := openPisAtFvars_typeWScoped _ hop1 hw0 (R.g.nP + s) y hy
    rwa [Nat.zero_add] at this
  have htT' : ConLeche.inferTypeCore μ envC F R.g.pre.length (Expr.fvarTypeD y) = .ok tT := by
    rw [ConLeche.inferTypeCore_depth_inv mpC.base2.wf F
      (Expr.WScoped.to_wscopedB (hwsY.mono (by omega)))
      (Expr.WScoped.to_wscopedB hwsY)]
    exact htT
  -- the generator's pieces are scoped and bounded
  obtain ⟨hfl, hfvsS, hresS⟩ := ConLeche.ScB.openPis hopR
    ((hg.tyD cls x hxmem).mono (by omega))
  have hwsS : ∀ i, i < x.nF → ConLeche.ScB (R.g.pre.length + x.nF) (ws.getD i default) :=
    fun i hi => ConLeche.ScB.targetPiDomsWith_getD hwsR
      ((hg.tyN cls x hxmem).mono (by omega)) (fun a ha => by
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
        obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
        rw [hxe]; exact ConLeche.ScB.fvar (by omega) hty) (by omega)
  have hihS : ∀ l ty bm', ihs[l]? = some (ty, bm') →
      ConLeche.ScB (R.g.pre.length + x.nF + l) ty := by
    intro l ty bm' hl
    have hl' : l < x.recs.length := by
      rw [← hihl]; exact (List.getElem?_eq_some_iff.mp hl).1
    obtain ⟨⟨i, t, tele⟩, hq⟩ : ∃ q, x.recs[l]? = some q :=
      ⟨_, List.getElem?_eq_getElem hl'⟩
    obtain ⟨⟨ty', hty', hl2⟩, -, -, st, hst, hstl⟩ := hih l i t tele hq
    rw [hl] at hl2
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl2)
    obtain ⟨hiF, -⟩ := ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hq)
    have hi : i < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hiF
    obtain ⟨tyf, hxe, htyf⟩ := hfvsS i _ (List.getElem?_eq_getElem hi)
    refine genIhTy_scb hst (by omega) ((hwsS i hiF).mono (by omega)) ?_ hty'
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hxe]
    exact ConLeche.ScB.fvar (by omega) (htyf.mono (by omega))
  have hcl : ∀ p ∈ (tgtFieldFvs pp.toBlockShape out c j).map R.g.binder ++ ihs,
      p.1.looseBVarsBounded 0 = true := by
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hp
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy'
      obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
      rw [hxe]; exact hty.2
    · obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hp
      exact (hihS l _ _ (List.getElem?_eq_getElem hl)).2
  have hbbS : ConLeche.ScB (R.g.pre.length + x.nF)
      (Expr.mkAppN (R.g.motVar cls) (res.getAppArgs.drop (R.g.cls.getD cls default).nPc ++
        [Expr.mkAppN (.const x.cv.name (R.g.cls.getD cls default).lvls)
          ((R.g.cls.getD cls default).ds ++ tgtFieldFvs pp.toBlockShape out c j)])) := by
    rw [ConLeche.ClassGen.motVar_eq hmc]
    refine ConLeche.ScB.mkAppN (ConLeche.ScB.fvar (by omega) (ConLeche.ScB.sort _ _))
      fun a ha => ?_
    rcases List.mem_append.mp ha with ha | ha
    · exact ConLeche.ScB.getAppArgs hresS a (List.mem_of_mem_drop ha)
    · simp only [List.mem_singleton] at ha
      subst ha
      refine ConLeche.ScB.mkAppN (ConLeche.ScB.const _ _ _) fun b hb => ?_
      rcases List.mem_append.mp hb with hb | hb
      · exact (hg.ds cls b hb).mono (by omega)
      · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
        obtain ⟨ty, hxe, hty⟩ := hfvsS k _ (List.getElem?_eq_getElem hk)
        rw [hxe]; exact ConLeche.ScB.fvar (by omega) (hty.mono (by omega))
  -- open the entry at the rule prefix
  obtain ⟨xs', rest, hop', hrest, hdoms'⟩ := open_of_erasedEq_closeTelescope _ R.g.pre.length _
    (Expr.fvarTypeD y) hcl hbbS.2 (by rw [← hTE]; exact hyE)
  have hxl' : xs'.length = x.nF + ihs.length := by
    rw [ConLeche.Verify.openPisAtFvars_length _ hop']; simp [hfl]
  rw [show ((tgtFieldFvs pp.toBlockShape out c j).map R.g.binder ++ ihs).length
    = x.nF + ihs.length by simp [hfl]] at hop'
  have hwsY' : Expr.WScoped R.g.pre.length (Expr.fvarTypeD y) := hwsY.mono (by omega)
  obtain ⟨hwsX', hwsR'⟩ := openPisAtFvars_WScoped _ _ _ hop' hwsY'
  have hbY : (Expr.fvarTypeD y).looseBVarsBounded 0 = true := hbF y (List.mem_of_getElem? hy)
  obtain ⟨hbR', hbX'⟩ := ConLeche.Verify.openPisAtFvars_bounded _ hop' hbY
  have hshX : ∀ (k : Nat) (z : Expr), xs'[k]? = some z →
      ∃ ty, z = Expr.fvar (R.g.pre.length + k) ty :=
    fun k z hz => openPisAtFvars_index _ _ _ hop' k z hz
  have hinfX := inferTypeCore_openPis_dom hμ hop' htT'
  have hinfR : ∃ t, ConLeche.inferTypeCore μ envC F (R.g.pre.length + x.nF + ihs.length) rest
      = .ok t := by
    rcases Nat.eq_zero_or_pos (x.nF + ihs.length) with h0 | hpos
    · rw [h0] at hop'
      simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hop'
      obtain ⟨-, rfl⟩ := hop'
      exact ⟨tT, by rw [Nat.add_assoc, h0, Nat.add_zero]; exact htT'⟩
    · obtain ⟨k, hk⟩ : ∃ k, x.nF + ihs.length = k + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
      rw [hk] at hop'
      obtain ⟨bt, -, hbt, -⟩ := inferTypeCore_openPis_body hμ k hop' htT'
      exact ⟨bt, by rw [Nat.add_assoc, hk]; exact hbt⟩
  -- leaves
  have hnil : ((tgtRs out)[c]'hc).1.type.fvarLeaves = [] := fvarLeaves_nil_of_wscoped_zero hw0
  have hleafY : ∀ l ∈ (Expr.fvarTypeD y).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs1.take R.g.pre.length := by
    intro l hl
    have hmem : Expr.fvar l.1 l.2 ∈ fvs1 := by
      rcases openPisAtFvars_leaves _ hop1 l (Or.inr ⟨y, List.mem_of_getElem? hy, by
        obtain ⟨ty, rfl⟩ := hshF _ y hy
        simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
        exact List.mem_cons_of_mem _ hl⟩) with h' | h'
      · rw [hnil] at h'; exact nomatch h'
      · exact h'
    obtain ⟨pos, hpos⟩ := List.getElem?_of_mem hmem
    obtain ⟨ty', hty'⟩ := hshF pos _ hpos
    have h1 : l.1 = pos := by injection hty'
    have hlt : l.1 < R.g.nP + s := Expr.fvarLeaves_lt_of_wscoped hwsY l hl
    have hpt : (fvs1.take R.g.pre.length)[pos]? = some (Expr.fvar l.1 l.2) := by
      rw [List.getElem?_take, if_pos (by omega)]; exact hpos
    exact List.mem_of_getElem? hpt
  have hleafs : ∀ l, (l ∈ rest.fvarLeaves ∨ ∃ z ∈ xs', l ∈ z.fvarLeaves) →
      Expr.fvar l.1 l.2 ∈ fvs1.take R.g.pre.length ++ xs' := by
    intro l hl
    rcases openPisAtFvars_leaves _ hop' l hl with h' | h'
    · exact List.mem_append_left _ (hleafY l h')
    · exact List.mem_append_right _ h'
  refine ⟨cls, s, x, res, ws, ihs, fvs1, _, xs', rest, hgc, hgx, hms, hxmem, hMaj, hrP, hmp,
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, ⟨sc, hmc, hscl⟩, hop1, by rw [← hrP]; exact hle, hlenF,
    hshF, fun z hz => ⟨by simpa using hwsF z hz, hbF z hz⟩, hPd, hxl', hshX,
    fun z hz => ⟨by rw [Nat.add_assoc]; exact hwsX' z hz, hbX' z hz⟩, ?_, ?_, hrest, hinfX,
    hinfR, by rw [Nat.add_assoc]; exact hwsR', hbR', hleafs⟩
  · intro k z hk hz
    have hkf : k < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hk
    have := hdoms' k z _ hz (by
      rw [List.getElem?_append_left (by simpa using hkf), List.getElem?_map,
        List.getElem?_eq_getElem hkf]; rfl)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkf]
    simpa [ClassGen.binder] using this
  · intro l z hz
    have hl : l < ihs.length := by
      have := (List.getElem?_eq_some_iff.mp hz).1; omega
    have := hdoms' (x.nF + l) z _ hz (by
      rw [List.getElem?_append_right (by simp [hfl]), List.length_map, hfl,
        Nat.add_sub_cancel_left, List.getElem?_eq_getElem hl]; rfl)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
    exact this

end Open

end ConLeche.Model
