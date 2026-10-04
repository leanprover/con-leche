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
      ite_eq_left (by omega), hpd]; rfl
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

/-! ## The `ih` terms, graded -/

section Ih

/-- `UnderTowerOk` from its spine form: the domains graded along their
fitting spines, and at every full spine the body graded, in the result,
the result a truth value at a zero bit. -/
theorem underTowerOk_of_spines {m : Nat} {b T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      (∀ k, k < ds.length → ∀ zs : List V, SpineFit σ ((ds.map (·.2.2)).take k) zs →
        WellDenoted V (consList zs σ) ((ds.map (·.2.2)).getD k default)) →
      (∀ zs : List V, SpineFit σ (ds.map (·.2.2)) zs →
        WellDenoted V (consList zs σ) b ∧ interp V (consList zs σ) b ∈ˢ interp V (consList zs σ) T ∧
          (m = 0 → interp V (consList zs σ) T ∈ˢ (univZero : V))) →
      UnderTowerOk m σ b T ds
  | [], σ, _, hb => by
    have := hb [] trivial
    simp only [consList_nil] at this
    exact this
  | d :: ds, σ, hd, hb => by
    refine ⟨by simpa using hd 0 (by simp) [] trivial, fun a ha => ?_⟩
    refine underTowerOk_of_spines (fun k hk zs hzs => ?_) (fun zs hzs => ?_)
    · have := hd (k + 1) (by simpa using hk) (a :: zs) ⟨ha, hzs⟩
      simpa [consList_cons] using this
    · have := hb (a :: zs) ⟨ha, hzs⟩
      simpa [consList_cons] using this

theorem domsBelow_of_fieldsBelow {bit : Nat} :
    ∀ {tl : List (Nat × AnnotTerm)} {k : Nat}, FieldsBelow k (tl.map (·.2)) →
      DomsBelow k (tl.map fun p => (0, p.1, p.2))
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, domsBelow_of_fieldsBelow (bit := bit) h.2⟩

/-- A generated `ih` binder type is bound by its frame. -/
theorem genIhDomAV_below {D mt : Nat} {q : IhDatum} (hq : IhDatumBelow D q) (hmt : mt < D) :
    Term.bvarsBelow D (genIhDomAV D mt q).erase := by
  unfold genIhDomAV
  refine mkPisAV_below_of (domsBelow_of_fieldsBelow (bit := 0) hq.1) ?_
  rw [AnnotTerm.erase_mkAppN, List.length_map]
  refine VExprAux.bvarsBelow_mkAppN (by show _ < _; omega) fun a ha => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp ha
  exact hq.2 e he

end Ih

section IhRun

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 16000000 in
/-- **A generated `ih` term's tower is sound over a typed tuple**: its
telescope is graded; at every fitting spine its body — the callee's value
applied to the prefix, the index arguments and the applied field — is
graded and inhabits the `ih`'s motive application, a truth value where
the family eliminates into `Prop`. -/
theorem genIhUnder (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) (ρ : Nat → V) {rs : List V} (hrl : rs.length = (tgtRs out).length)
    (hty : ∀ c, c < (tgtRs out).length →
      rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c))
    {c j : Nat} (hc : c < (tgtRs out).length) (hj : j < blockRecNCt (tgtRs out) c) {ys : List V}
    (hys : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys)
    {q : IhDatum} (hq : q ∈ genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j) :
    UnderTowerOk (genBit pp ψ) (consList ys (consList rs ρ))
      (AnnotTerm.mkAppN (.bvar (R.g.pre.length + (genCtorAt R.g R.rd c j).nF + q.2.1.length
          + ((tgtRs out).length - 1 - q.1)))
        (prefVarsAV R.g.pre.length ((genCtorAt R.g R.rd c j).nF + q.2.1.length)
          ++ (q.2.2.1 ++ [q.2.2.2])))
      (AnnotTerm.mkAppN (.bvar (R.g.pre.length + (genCtorAt R.g R.rd c j).nF + q.2.1.length
          - 1 - classMotPos R.g (genClsOf R.rd q.1)))
        (q.2.2.1 ++ [q.2.2.2]))
      (q.2.1.map fun p => (0, p.1, p.2)) := by
  obtain ⟨l, hl⟩ := List.getElem?_of_mem hq
  obtain ⟨t, st, fr, hq1, hst, hstl, hcnt, hcls, G2, hA, -⟩ :=
    genIhFrame hμ R hg h mpC hfind ψ hc hj hl
  have hr : (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := List.getElem?_eq_getElem hc
  have hK := genRun_cal R mpC.base2.acval envC (genBit pp ψ) ψ c hc j hj q hq
  obtain ⟨hlc, -⟩ := genPdoms_read hμ R hg h mpC ψ hc
  have hnF := genRun_nF hμ R hg mpC.base2.acval ψ c hc j hj
  have hbelow := genRun_below hμ R hg h mpC (genBit pp ψ) ψ c hc j hj q hq
  rw [hlc, ← hnF] at hbelow
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  have hxl : xs.length = R.g.pre.length := hxs.length_eq.trans hlc
  have hfl : fs.length = (genCtorAt R.g R.rd c j).nF := hfs.length_eq.trans hnF.symm
  -- the frame's domains are closed below it
  have hPdB : FieldsBelow 0 (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) :=
    fieldsBelow_of_getD fun l hl' => by
      simpa using blockRulePdomsAV_bounded hμ mpC h hr ψ l hl'
  have hFdB := genRun_fdomsBelow hμ R hg h mpC ψ c hc j hj
  have hFrB := fieldsBelow_append hPdB (by simpa using hFdB)
  have hysR : SpineFit (consList rs ρ) (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape
      (tgtRs out) ψ c ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) :=
    spineFit_congr_fieldsBelow hFrB (fun i hi => absurd hi (Nat.not_lt_zero _)) hys
  generalize hD : R.g.pre.length + (genCtorAt R.g R.rd c j).nF = D at hbelow ⊢
  have hxfl : (xs ++ fs).length = D := by rw [List.length_append, hxl, hfl, hD]
  refine underTowerOk_of_spines (fun k hk zs hzs => ?_) (fun zs hzs => ?_)
  · -- a telescope domain
    rw [List.map_map] at hzs ⊢
    have hfit : SpineFit (consList rs ρ) ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape
        (tgtRs out) ψ c ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
        ++ q.2.1.map (·.2)).take (R.g.pre.length + (genCtorAt R.g R.rd c j).nF + k))
        ((xs ++ fs) ++ zs) := by
      rw [List.take_append, List.take_of_length_le (by simp; omega),
        show R.g.pre.length + (genCtorAt R.g R.rd c j).nF + k
          - (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length = k by
          simp [hlc, ← hnF]]
      exact SpineFit.append hysR hzs
    have := (G2.ok _ (by simp at hk; omega) _ _ hfit).1
    rw [consList_append, list_getD_append_right (by simp [hlc, ← hnF]),
      show R.g.pre.length + (genCtorAt R.g R.rd c j).nF + k
        - (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length = k by
        simp [hlc, ← hnF]] at this
    simpa [Function.comp_def] using this
  · -- the body: the callee applied along its binder data
    rw [List.map_map] at hzs
    simp only [Function.comp_def] at hzs
    have hagD : ∀ i, i < D → consList (xs ++ fs) (consList rs ρ) i = consList (xs ++ fs) ρ i := by
      intro i hi
      exact consList_congr_below (xs ++ fs) (D := 0) (fun k hk => absurd hk (Nat.not_lt_zero _)) i
        (by simpa [hxfl] using hi)
    have hzs' : SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) zs :=
      spineFit_congr_fieldsBelow hbelow.1 hagD hzs
    have hzl : zs.length = q.2.1.length := by rw [hzs.length_eq, List.length_map]
    have hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) := hys
    obtain ⟨-, hxlT, hfitR⟩ := genCallTy hμ R hg h mpC hfind (genBit pp ψ) ψ ρ c hc j hj xs fs
      (by rw [hxl, hlc]) hsp q hq zs hzs'
    -- the arguments read alike at the two frames
    have hagZ : ∀ i, i < D + q.2.1.length →
        consList zs (consList (xs ++ fs) (consList rs ρ)) i = consList zs (consList (xs ++ fs) ρ) i :=
      fun i hi => consList_congr_below zs hagD i (by rw [hzl]; exact hi)
    have havals : (q.2.2.1 ++ [q.2.2.2]).map (interp V (consList zs (consList (xs ++ fs) (consList rs ρ))))
        = (q.2.2.1 ++ [q.2.2.2]).map (interp V (consList zs (consList (xs ++ fs) ρ))) :=
      List.map_congr_left fun e he => interp_congr_below V e _ _ _ (hbelow.2 e he) hagZ
    -- the callee's type and value
    have hrT : (tgtRs out)[q.1]? = some ((tgtRs out)[q.1]'hK) := List.getElem?_eq_getElem hK
    obtain ⟨-, -, -, -, hTyE, -, -, -, -, hwdTy⟩ := recStage_tyPis (V := V) hμ mpC h hrT ψ
    have hhead : interp V (consList zs (consList (xs ++ fs) (consList rs ρ)))
        (.bvar (D + q.2.1.length + ((tgtRs out).length - 1 - q.1))) = rs.getD q.1 pt := by
      rw [interp_bvar, show D + q.2.1.length + ((tgtRs out).length - 1 - q.1)
        = ((tgtRs out).length - 1 - q.1) + (xs ++ fs).length + zs.length by rw [hxfl, hzl]; omega,
        consList_apply_add, consList_apply_add, consList_getD_of_lt _ _ _ (by omega), hrl,
        show (tgtRs out).length - 1 - ((tgtRs out).length - 1 - q.1) = q.1 by omega]
    have hpv : (prefVarsAV R.g.pre.length ((genCtorAt R.g R.rd c j).nF + q.2.1.length)).map
        (interp V (consList zs (consList (xs ++ fs) (consList rs ρ)))) = xs := by
      have := interp_prefVarsAV (V := V) (xs := xs) (bs := fs ++ zs) (ρ := consList rs ρ) hxl
      rw [List.length_append, hfl, hzl, ← List.append_assoc, consList_append] at this
      exact this
    have hvals : (prefVarsAV R.g.pre.length ((genCtorAt R.g R.rd c j).nF + q.2.1.length)
        ++ (q.2.2.1 ++ [q.2.2.2])).map (interp V (consList zs (consList (xs ++ fs) (consList rs ρ))))
        = xs ++ (q.2.2.1.map (interp V (consList zs (consList (xs ++ fs) ρ)))
          ++ [interp V (consList zs (consList (xs ++ fs) ρ)) q.2.2.2]) := by
      rw [List.map_append, hpv, havals, List.map_append]; rfl
    have hframe : SpineFit (consList rs ρ) (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape
        (tgtRs out) ψ c ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j
        ++ q.2.1.map (·.2)) ((xs ++ fs) ++ zs) := SpineFit.append hysR hzs
    obtain ⟨hWD, hIn⟩ := Rules.wellDenotedV_mkAppN_of_fit (ρ := consList zs (consList (xs ++ fs)
        (consList rs ρ))) (σ := ρ)
        (Ta := blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ q.1)
        (f := .bvar (D + q.2.1.length + ((tgtRs out).length - 1 - q.1))) (prefVarsAV R.g.pre.length ((genCtorAt R.g R.rd c j).nF + q.2.1.length)
          ++ (q.2.2.1 ++ [q.2.2.2])) (hwdTy ρ) ⟨by simp [WellDenoted_bvar], by simp [AnnotValid_bvar]⟩
      (fun x hx => by
        rcases List.mem_append.mp hx with hx | hx
        · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
          exact ⟨by simp [WellDenoted_bvar], by simp [AnnotValid_bvar]⟩
        · have := hA x hx _ _ hframe
          rwa [consList_append] at this)
      (by rw [hhead]; exact hty q.1 hK)
      (by
        rw [hvals, hTyE]
        exact teleFit_mkPisAV_of_spineFit hfitR)
    -- the motive application is the callee's conclusion there
    have hmt : classMotPos R.g (genClsOf R.rd q.1) < xs.length := by
      rw [hcls, hxl, classMotPos, hst]; exact hstl
    obtain ⟨clsT, tyT, ifsT, bodyT, hgcT, hMT, -, -, -, hRPT, -, -, -, -, -, -, -, -⟩ :=
      genRun_binders hμ R hg h mpC ψ hK
    have hconcl := genRun_conclMot hμ R hg h mpC ψ ρ q.1 hK xs
      (q.2.2.1.map (interp V (consList zs (consList (xs ++ fs) ρ))))
      (interp V (consList zs (consList (xs ++ fs) ρ)) q.2.2.2) (by rw [hxl, hRPT])
      (by rw [List.length_map, hcnt, hMT, ← hgcT, hcls])
    have hT0 : interp V (consList zs (consList (xs ++ fs) (consList rs ρ)))
        (AnnotTerm.mkAppN (.bvar (D + q.2.1.length - 1 - classMotPos R.g (genClsOf R.rd q.1)))
          (q.2.2.1 ++ [q.2.2.2]))
        = interp V (consList (xs ++ (q.2.2.1.map (interp V (consList zs (consList (xs ++ fs) ρ)))
            ++ [interp V (consList zs (consList (xs ++ fs) ρ)) q.2.2.2])) ρ)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ q.1) := by
      rw [hconcl, interp_mkAppN, ← List.foldl_map, havals, List.map_append]
      congr 1
      rw [interp_bvar, ← consList_append, List.append_assoc,
        show D + q.2.1.length - 1 - classMotPos R.g (genClsOf R.rd q.1)
          = (fs ++ zs).length + xs.length - 1 - classMotPos R.g (genClsOf R.rd q.1) by
          rw [List.length_append, hfl, hzl, ← hxfl, List.length_append, hfl]; omega]
      exact consList_prefix_getD hmt
    refine ⟨hWD.1, by rw [hT0]; exact hIn, fun h0 => ?_⟩
    rw [hT0]
    have hu := genRec_conclTy hμ h ψ ρ q.1 hK _ hfitR
    have he : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large)
        = 0 := (pwBit_zeronessOf ψ _).mp h0
    rw [he, univ_zero] at hu
    exact hu

omit [SetTheory V] in
theorem lamDomsBelow_of_fieldsBelow :
    ∀ {tl : List (Nat × AnnotTerm)} {k : Nat}, FieldsBelow k (tl.map (·.2)) → LamDomsBelow k tl
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.1, lamDomsBelow_of_fieldsBelow h.2⟩

omit [SetTheory V] in
/-- A generated `ih` datum's telescope carries one bit. -/
theorem genIhdAV_bits {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {g : ClassGen}
    {rd : ClassRead} {bit : Nat} {ψ : Name → Nat} {c j : Nat} {q : IhDatum}
    (hq : q ∈ genIhdAV acval env g rd bit ψ c j) : ∀ p ∈ q.2.1, p.1 = bit := by
  unfold genIhdAV at hq
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp hq
  intro p hp
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hp
  rfl

theorem genIhAV_eq_mkLamsC {K rP D bit : Nat} {q : IhDatum} (hb : ∀ p ∈ q.2.1, p.1 = bit) :
    genIhAV K rP D q = mkLamsC bit (q.2.1.map fun p => (0, p.1, p.2))
      (AnnotTerm.mkAppN (.bvar (D + q.2.1.length + (K - 1 - q.1)))
        (prefVarsAV rP (D - rP + q.2.1.length) ++ (q.2.2.1 ++ [q.2.2.2]))) := by
  unfold genIhAV mkLamsC
  congr 1
  rw [List.map_map]
  exact (List.map_id _).symm.trans (List.map_congr_left fun p hp => by
    obtain ⟨p1, p2⟩ := p
    have := hb (p1, p2) hp
    simp only at this
    subst this
    rfl)

set_option maxHeartbeats 16000000 in
/-- **`hrhs` of the family premise**: at a typed tuple of recursor values
and a spine fitting the rule frame, the generated `ih` terms are graded
(a constant-bit λ-tower over `genIhUnder`), and so is the residue at
their values — the minor premise applied to the fields and the `ih`
values along its graded Π-tower (`genMinorFit`). -/
theorem genRhs (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) (ρ : Nat → V) (rs : List V) (hrl : rs.length = (tgtRs out).length)
    (hty : ∀ c, c < (tgtRs out).length →
      rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) :
    ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
      (∀ v ∈ genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ c j,
        WellDenotedV V (consList ys (consList rs ρ)) v) ∧
      WellDenotedV V (consList ((genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd
          (genBit pp ψ) ψ c j).map (interp V (consList ys (consList rs ρ)))) (consList ys ρ))
        (genRbAV R.g R.rd c j) := by
  intro c hc j hj ys hys
  obtain ⟨hlc, -⟩ := genPdoms_read hμ R hg h mpC ψ hc
  have hnF := genRun_nF hμ R hg mpC.base2.acval ψ c hc j hj
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  have hxl : xs.length = R.g.pre.length := hxs.length_eq.trans hlc
  have hfl : fs.length = (genCtorAt R.g R.rd c j).nF := hfs.length_eq.trans hnF.symm
  -- each ih term: its tower, sound
  have hIh : ∀ q ∈ genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j,
      WellDenotedV V (consList (xs ++ fs) (consList rs ρ))
        (genIhAV (tgtRs out).length R.g.pre.length (R.g.pre.length + (genCtorAt R.g R.rd c j).nF) q) ∧
      interp V (consList (xs ++ fs) (consList rs ρ))
          (genIhAV (tgtRs out).length R.g.pre.length (R.g.pre.length + (genCtorAt R.g R.rd c j).nF) q)
        ∈ˢ interp V (consList (xs ++ fs) ρ)
          (genIhDomAV ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (classMotPos R.g (genClsOf R.rd q.1)) q) := by
    intro q hq
    have hbits := genIhdAV_bits hq
    have hU := genIhUnder hμ R hg h mpC hfind ψ ρ hrl hty hc hj hys hq
    have hz : ∀ d ∈ q.2.1.map (fun p => (0, p.1, p.2)), (genBit pp ψ = 0 ↔ d.2.1 = 0) := by
      intro d hd
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hd
      simp [hbits p hp]
    have hbelow := genRun_below hμ R hg h mpC (genBit pp ψ) ψ c hc j hj q hq
    rw [hlc, ← hnF] at hbelow
    have hEq := genIhAV_eq_mkLamsC (K := (tgtRs out).length) (rP := R.g.pre.length)
      (D := R.g.pre.length + (genCtorAt R.g R.rd c j).nF) hbits
    rw [show R.g.pre.length + (genCtorAt R.g R.rd c j).nF - R.g.pre.length
      = (genCtorAt R.g R.rd c j).nF by omega] at hEq
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hEq]
      exact mkLamsC_wellDenoted hz hU
    · -- validity: the telescope and the arguments
      obtain ⟨hF, hA⟩ := genIhValid hμ R hg h mpC hfind ψ ρ hc hj hys hq
      unfold genIhAV
      refine annotValid_lamsApp (fun _ => by simp) q.2.1
        (D := R.g.pre.length + (genCtorAt R.g R.rd c j).nF) (σ := consList (xs ++ fs) ρ)
        (lamDomsBelow_of_fieldsBelow hbelow.1) (fun e he => ?_) (fun i hi => ?_) hF
        (fun bs hbs e he => ?_)
      · rcases List.mem_append.mp he with he | he
        · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
          rw [List.mem_range] at hl
          show _ < _
          omega
        · exact hbelow.2 e he
      · exact (consList_congr_below (xs ++ fs) (D := 0)
          (fun k hk => absurd hk (Nat.not_lt_zero _)) i (by simp [hxl, hfl]; omega)).symm
      · rcases List.mem_append.mp he with he | he
        · obtain ⟨l, -, rfl⟩ := List.mem_map.mp he
          simp
        · exact hA bs hbs e he
    · have hmem := mkLamsC_mem hz hU
      rw [← hEq] at hmem
      have hmt : classMotPos R.g (genClsOf R.rd q.1) < R.g.pre.length := by
        obtain ⟨l, hl⟩ := List.getElem?_of_mem hq
        obtain ⟨t, st, -, -, hst, hstl, -, hcls, -⟩ := genIhFrame hμ R hg h mpC hfind ψ hc hj hl
        rw [hcls, classMotPos, hst]; exact hstl
      have hbD := genIhDomAV_below (D := R.g.pre.length + (genCtorAt R.g R.rd c j).nF)
        (mt := classMotPos R.g (genClsOf R.rd q.1)) hbelow (by omega)
      rw [hlc, ← hnF, ← interp_congr_below V _ _ _ _ hbD (fun i hi =>
        consList_congr_below (xs ++ fs) (D := 0) (fun k hk => absurd hk (Nat.not_lt_zero _)) i
          (by simp [hxl, hfl]; omega))]
      exact hmem
  refine ⟨fun v hv => ?_, ?_⟩
  · unfold genIhsAV at hv
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
    exact (hIh q hq).1
  · -- the residue: the minor premise along its graded tower
    generalize hH : (genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ c
      j).map (interp V (consList (xs ++ fs) (consList rs ρ))) = hvals
    have hHl : hvals.length = (genCtorAt R.g R.rd c j).recs.length := by
      rw [← hH, List.length_map]; unfold genIhsAV; rw [List.length_map, genIhdAV_length']
    obtain ⟨bs, b, hmemB, hwdB, hfitF⟩ := genMinorFit hμ R hg h mpC hfind ψ ρ hc hj hxs
    have hfit := hfitF fs hfs hvals (by rw [hHl, genIhdAV_length']) (fun l q hv hql hvl => by
      rw [← hH] at hvl
      unfold genIhsAV at hvl
      rw [List.map_map, List.getElem?_map, hql] at hvl
      obtain rfl := (Option.some.inj hvl).symm
      exact (hIh q (List.mem_of_getElem? hql)).2)
    have hm : R.g.nP + genMinorSlot R.g R.rd c j < xs.length := by
      have := genRun_min hμ R hg h mpC c hc j hj
      rw [hxl]
      obtain ⟨-, -, -, -, -, -, -, -, -, hRPc, -⟩ := genRun_binders hμ R hg h mpC ψ hc
      omega
    have hv1 : (prefVarsAV fs.length hvals.length).map
        (interp V (consList hvals (consList (xs ++ fs) ρ))) = fs := by
      have := interp_prefVarsAV (V := V) (xs := fs) (bs := hvals) (ρ := consList xs ρ) rfl
      rw [consList_append] at this
      rw [consList_append]
      exact this
    have hv2 : (prefVarsAV hvals.length 0).map
        (interp V (consList hvals (consList (xs ++ fs) ρ))) = hvals := by
      have := interp_prefVarsAV (V := V) (xs := hvals) (bs := []) (ρ := consList (xs ++ fs) ρ) rfl
      simpa using this
    have hhd : interp V (consList hvals (consList (xs ++ fs) ρ))
        (.bvar (hvals.length + fs.length + (xs.length - 1 - (R.g.nP + genMinorSlot R.g R.rd c j))))
        = xs.getD (R.g.nP + genMinorSlot R.g R.rd c j) pt := by
      show consList hvals (consList (xs ++ fs) ρ) _ = _
      rw [← consList_append, List.append_assoc,
        show hvals.length + fs.length + (xs.length - 1 - (R.g.nP + genMinorSlot R.g R.rd c j))
          = (fs ++ hvals).length + xs.length - 1 - (R.g.nP + genMinorSlot R.g R.rd c j) by
          simp; omega]
      exact consList_prefix_getD hm
    have hRb : genRbAV R.g R.rd c j = genRb0 xs.length (R.g.nP + genMinorSlot R.g R.rd c j)
        fs.length hvals.length := by rw [genRbAV, hxl, hfl, hHl]
    rw [hRb]
    unfold genRb0
    refine (Rules.wellDenotedV_mkAppN_of_fit (ρ := consList hvals (consList (xs ++ fs) ρ))
      (σ := consList xs ρ) (Ta := mkPisAV bs b)
      (rest := interp V (consList (fs ++ hvals) (consList xs ρ)) b) (f := .bvar (hvals.length + fs.length
        + (xs.length - 1 - (R.g.nP + genMinorSlot R.g R.rd c j))))
      (prefVarsAV fs.length hvals.length ++ prefVarsAV hvals.length 0) hwdB
      ⟨by simp [WellDenoted_bvar], by simp [AnnotValid_bvar]⟩ (fun x hx => ?_)
      (by rw [hhd]; exact hmemB) ?_).1
    · rcases List.mem_append.mp hx with hx | hx <;>
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
        exact ⟨by simp [WellDenoted_bvar], by simp [AnnotValid_bvar]⟩
    · rw [List.map_append, hv1, hv2]
      exact teleFit_mkPisAV_of_spineFit hfit

end IhRun

end ConLeche.Model
