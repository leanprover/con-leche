module

public import ConLeche.Model.Inductives.GenClsCall
import ConLeche.Model.Inductives.GenClsMinor
import ConLeche.Model.Inductives.GenClsRows
import ConLeche.Model.Inductives.GenClsFrame
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.GenRecRules
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.ClassGenMinor
import ConLeche.Model.Inductives.ClassGenStep
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.ClassRecKit
import ConLeche.Model.Inductives.GenRuleSyn
import ConLeche.Model.Inductives.GenRuleFree
import ConLeche.Model.Inductives.GenCallKit
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.FixKit
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.Valid
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Subst
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Semantics.Tower.TowerKit

public section

/-!
# The generated `ih` terms and residue are graded (lane GENREC-CLS)

`hrhs` of the family premise (`genRecPre_run`): at a typed tuple of
recursor values and a spine fitting the rule frame, every generated `ih`
term `λ a⃗, rec_t x⃗ e⃗ (f a⃗)` is graded — a constant-bit λ-tower
(`mkLamsC_wellDenoted`) whose body is the callee's value applied along
its binder data (`genCallTy`), inhabiting the `ih`'s motive application
(the callee's conclusion, `genRun_conclMot`) — and the residue, the minor
premise applied to the fields and the `ih` values, is graded: the minor
premise's type is the rule frame's Π-tower (`genMinorFit`), the `ih`
values inhabit its `ih` domains (`mkLamsC_mem`).
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

section Fit

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 16000000 in
/-- **The minor premise of `(c, j)` at a prefix spine**: its value lies in
a graded Π-tower at the spine's frame, whose binder data the declared
fields and the `ih` values fit (the rule frame's field domains, then the
`ih` data's domains). -/
theorem genMinorFit (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat} (hc : c < (tgtRs out).length)
    (hj : j < blockRecNCt (tgtRs out) c) {xs : List V}
    (hxs : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs) :
    ∃ (bs : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
      xs.getD (R.g.nP + genMinorSlot R.g R.rd c j) pt ∈ˢ interp V (consList xs ρ) (mkPisAV bs b) ∧
      WellDenotedV V (consList xs ρ) (mkPisAV bs b) ∧
      ∀ fs, SpineFit (consList xs ρ) (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) fs →
      ∀ hs : List V, hs.length = (genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j).length →
      (∀ (l : Nat) (q : IhDatum) (hv : V),
        (genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j)[l]? = some q → hs[l]? = some hv →
        hv ∈ˢ interp V (consList (xs ++ fs) ρ)
          (genIhDomAV ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (classMotPos R.g (genClsOf R.rd q.1)) q)) →
      SpineFit (consList xs ρ) (bs.map (·.2.2)) (fs ++ hs) := by
  obtain ⟨cls, s, x, T, res, ws, ihs, hgc, hgx, hms, hxmem, hMaj, ⟨ihs0, hsS⟩, hpreT, hTs, hrP,
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, ⟨sc, hmc, hscl⟩, hTE⟩ := genMinorSetup R hg h hfind hc hj
  have hr : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  have hpl : R.g.pre.length = R.g.nP + R.g.slots.length :=
    (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1
  have hsl : s < R.g.slots.length := (List.getElem?_eq_some_iff.mp hsS).1
  have hmp : R.g.nP + s < R.g.pre.length := by omega
  -- the stored type's entry at the minor's slot
  obtain ⟨cls', ty', ifs', body', -, -, -, -, -, -, -, -, -, -, fvs0, o0, hop0, hE⟩ :=
    genRun_binders hμ R hg h mpC ψ hc
  obtain ⟨fvs1, concl1, hop1, -, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) hμ mpC h hr ψ
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hop1.symm.trans hop0))
  have hle := blockRecHrPle (p := pp) h hc
  have hlenF : fvs1.length = pp.toBlockShape.majorIdxAt c + 1 :=
    ConLeche.Verify.openPisAtFvars_length _ hop1
  obtain ⟨y, hy⟩ : ∃ y, fvs1[R.g.nP + s]? = some y :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hyE := hE _ y T hy (by
    rw [List.append_assoc, List.getElem?_append_left (by omega), hpreT]; rfl)
  obtain ⟨pd, hpd, -, hrd⟩ := hdomsR _ y hy
  rw [denoteMeta_erasedEq hyE] at hrd
  -- the prefix's entry: the minor's value, valid there
  have hlenPd := blockRulePdomsAV_length (V := V) hμ mpC h hr ψ
  have hPdget : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD
      (R.g.nP + s) default = pd.2.2 := by
    rw [blockRulePdomsAV, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      if_pos (by omega), hpd]; rfl
  have hmem := FixKI.spineFit_getD_mem' hxs (l := R.g.nP + s) (by rw [hlenPd]; omega)
  rw [hPdget] at hmem
  have hv := (hwdTy ρ).2
  rw [hTyE, ← List.take_append_drop (pp.toBlockShape.rulePrefixAt c)
    (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c), mkPisAV_append'] at hv
  have hvA := annotValid_piDom_at hv hxs (R.g.nP + s) (by
    rw [List.length_take, hlenRds]; omega)
  rw [show ((List.take (pp.toBlockShape.rulePrefixAt c)
      (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)).map (·.2.2)).getD
      (R.g.nP + s) default = pd.2.2 from hPdget] at hvA
  -- read at the rule prefix
  have hlift := denoteMeta_lift (env := envC) (φ := ψ) mpC.base2.acval_closed hTs.1 R.g.pre.length
    (by omega)
  rw [hrd, Option.map_some] at hlift
  -- the pieces are bounded
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
  obtain ⟨bs, b, hBE, hbl, hbs, hb⟩ :=
    denoteMeta_closeTelescope_read _ _ _ T hcl hbbS.2 (by rw [← hTE]; exact Expr.ErasedEq.rfl _)
      hlift
  -- the frames
  have hlenPd' : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = R.g.pre.length := hlenPd.trans hrP
  have hxl : xs.length = R.g.pre.length := hxs.length_eq.trans hlenPd'
  have hsh : shiftE (R.g.pre.length - (R.g.nP + s)) 0 (consList xs ρ)
      = consList (xs.take (R.g.nP + s)) ρ := by
    have := shiftE_consList (V := V) (ys := ([] : List V)) (zs := xs) (ρ := ρ)
      (n := R.g.pre.length - (R.g.nP + s)) (k := 0) rfl (by omega)
    rw [show xs.length - (R.g.pre.length - (R.g.nP + s)) = R.g.nP + s by omega] at this
    exact this
  have hmemB : xs.getD (R.g.nP + s) pt ∈ˢ interp V (consList xs ρ) (mkPisAV bs b) := by
    rw [← hBE, interp_liftN, hsh]; exact hmem
  have hvB : AnnotValid V (consList xs ρ) (mkPisAV bs b) := by
    rw [← hBE, AnnotValid_liftN, hsh]; exact hvA
  have hwdB : WellDenotedV V (consList xs ρ) (mkPisAV bs b) := by
    have hgr := blockRulePdomsAV_graded (V := V) hμ mpC h hr ψ (R.g.nP + s) (by omega) ρ
      (xs.take (R.g.nP + s)) (spineFit_take hxs (by omega))
    rw [hPdget] at hgr
    rw [← hBE, WellDenotedV_liftN, hsh]
    exact hgr
  -- the rule frame's field domains are the fields' binder data
  have hRP : tgtRP pp.toBlockShape c = R.g.pre.length := hrP
  have hfdL : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length = x.nF := by
    rw [tgtFdomsAV, readOpenedDoms_length_eq, hfl]
  refine ⟨bs, b, ?_, hwdB, fun fs hfs hs hhl hhs => ?_⟩
  · rw [hms]; exact hmemB
  · have hfsl : fs.length = x.nF := hfs.length_eq.trans hfdL
    have hihdL : (genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j).length
        = x.recs.length := by simp [genIhdAV, hgx]
    have hhsl : hs.length = x.recs.length := hhl.trans hihdL
    have hbsl : bs.length = x.nF + x.recs.length := by rw [hbl]; simp [hfl, hihl]
    have hfit : SpineFit (consList xs ρ) (bs.map (·.2.2)) (fs ++ hs) := by
      refine spineFit_of_getD (by simp [hfsl, hhsl, hbsl]) fun r hr => ?_
      rw [List.length_map] at hr
      rcases Nat.lt_or_ge r x.nF with hrF | hrF
      · -- a field
        have hrf : r < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hrF
        obtain ⟨a, ha, hra⟩ := hbs r (R.g.binder (tgtFieldFvs pp.toBlockShape out c j)[r])
          (by rw [List.getElem?_append_left (by simpa using hrf)]; simp [hrf])
        have hgetB : (bs.map (·.2.2)).getD r default = a := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, ha]; rfl
        have hgetF : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD r default
            = a := by
          rw [List.getD_eq_getElem?_getD, tgtFdomsAV, hRP, List.getElem?_eq_getElem (by simpa using hrf),
            Option.getD_some, readOpenedDoms_getElem _ _ r hrf]
          simp only [ClassGen.binder] at hra
          rw [hra]; rfl
        have hm := FixKI.spineFit_getD_mem' hfs (l := r) (by rw [hfdL]; exact hrF)
        rw [hgetF] at hm
        rw [hgetB, List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD, take_append_of_le (by omega)]
        exact hm
      · -- an inductive hypothesis
        obtain ⟨l, rfl⟩ : ∃ l, r = x.nF + l := ⟨r - x.nF, by omega⟩
        have hl : l < x.recs.length := by omega
        obtain ⟨⟨i, t, tele⟩, hq⟩ : ∃ q, x.recs[l]? = some q := ⟨_, List.getElem?_eq_getElem hl⟩
        obtain ⟨⟨ty, hty, hihq⟩, ⟨n, hrec⟩, hparts, st, hst, hstl⟩ := hih l i t tele hq
        obtain ⟨a, ha, hra⟩ := hbs (x.nF + l) (ty, R.g.bm)
          (by rw [List.getElem?_append_right (by simp [hfl]), List.length_map, hfl,
            Nat.add_sub_cancel_left]; exact hihq)
        have hgetB : (bs.map (·.2.2)).getD (x.nF + l) default = a := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map, ha]; rfl
        rw [show R.g.pre.length + (x.nF + l) = R.g.pre.length + x.nF + l by omega] at hra
        have hq' : (genCtorAt R.g R.rd c j).recs[l]? = some (i, t, tele) := by rw [hgx]; exact hq
        have hop' : ConLeche.openPisAtFvars (genCtorAt R.g R.rd c j).nF (genCtorAt R.g R.rd c j).tyD
            R.g.pre.length = some (tgtFieldFvs pp.toBlockShape out c j, res) := by rw [hgx]; exact hopR
        obtain ⟨hiF, -⟩ := ConLeche.ClassGen.recs_mem (List.mem_of_getElem? hq)
        obtain ⟨qd, hqd, hq1, hae⟩ := genIhEntry_read (acval := mpC.base2.acval) mpC.base2 rfl
          (ψ := ψ) hq' hop' (by simpa [hgx] using hfvsS)
          (by rw [hgx]; exact hwsR) (by rw [hgx]; exact hwsS i hiF)
          (by rw [hgx]; exact hparts) hst (by omega) (by rw [hgx]; exact hty)
          (by rw [hgx]; exact hra) (bit := genBit pp ψ) rfl
        obtain ⟨hv, hhv⟩ : ∃ hv, hs[l]? = some hv := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hmI := hhs l qd hv hqd hhv
        have hcal := (genRecIdx_spec (rd := R.rd) (cvGs := R.cvGs) hrec (by
          have := genRun_recCls_length R
          have h2 := (genRun_lengths R).2
          omega)).1
        have hmt : classMotPos R.g (genClsOf R.rd qd.1) = R.g.nP + st := by
          rw [hq1, genClsOf, List.getD_eq_getElem?_getD, hcal, Option.getD_some, classMotPos, hst]
          rfl
        rw [hmt, hlenPd', hfdL, ← hgx] at hmI
        rw [hgetB, hae, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hfsl,
          Nat.add_sub_cancel_left, hhv, Option.getD_some, List.take_append, List.take_of_length_le
          (by omega), hfsl, Nat.add_sub_cancel_left, consList_append, interp_liftN,
          shiftE_zero_consList (by simp; omega), ← consList_append]
        exact hmI
    exact hfit

end Fit

end ConLeche.Model
