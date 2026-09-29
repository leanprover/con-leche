module

public import ConLeche.Model.Inductives.GenClsMinor
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.ClassGenMinor
import ConLeche.Model.Inductives.GenRuleSyn
import ConLeche.Model.Inductives.GenRuleFree
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.Valid
import ConLeche.Model.WellDenotedTransport
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.DeclNative
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Verify.Inductives.ClassGenScope

public section

/-!
# The rule frame's grading, from the minor premise (lane GENREC-CLS)

The rule frame's declared field domains are the minor premise's field
binders (`genMinorSetup`: the minor premise's type IS the one built at the
rule prefix).  The minor premise's domain is graded wherever the prefix
fits (it is a binder domain of the stored, inferred recursor type), and a
graded Π-tower grades its binder domains along their fitting spines
(`wellDenotedV_piDom_at`): the field domains are graded — `hframe` of the
family premise, and the field half of `hrowV`.
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

/-- **A graded Π-tower grades its binder domains** along any spine
fitting the domains before them. -/
theorem wellDenotedV_piDom_at {B : AnnotTerm} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      WellDenotedV V ρ (mkPisAV tl B) → ∀ l, l < tl.length → ∀ zs : List V,
      SpineFit ρ ((tl.map (·.2.2)).take l) zs →
        WellDenotedV V (consList zs ρ) ((tl.map (·.2.2)).getD l default)
  | [], _, _, l, hl, _, _ => absurd hl (Nat.not_lt_zero _)
  | d :: tl, ρ, hv, l, hl, zs, hz => by
    have hw : WellDenoted V ρ (.pi d.1 d.2.1 d.2.2 (mkPisAV tl B)) := hv.1
    have hva : AnnotValid V ρ (.pi d.1 d.2.1 d.2.2 (mkPisAV tl B)) := hv.2
    rw [AnnotValid_pi] at hva
    cases l with
    | zero =>
      match zs, hz with
      | [], _ => exact ⟨hw.1, by simpa using hva.1⟩
    | succ l =>
      match zs, hz with
      | z :: zs, hz =>
        simp only [List.map_cons, List.take_succ_cons] at hz
        have ih := wellDenotedV_piDom_at (tl := tl) (ρ := cons z ρ)
          ⟨hw.2 z hz.1, hva.2.1 z hz.1⟩ l (by simpa using hl) zs hz.2
        simpa [consList_cons] using ih

/-- Graded fields are valid fields. -/
theorem fieldsValid_of_graded {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm}, (∀ l, l < Fs.length → ∀ zs : List V, SpineFit ρ (Fs.take l) zs →
      AnnotValid V (consList zs ρ) (Fs.getD l default)) → FieldsValid ρ Fs
  | [], _ => trivial
  | F :: Fs, h => by
    refine ⟨by simpa using h 0 (by simp) [] trivial, fun a ha => ?_⟩
    refine fieldsValid_of_graded (ρ := cons a ρ) fun l hl zs hz => ?_
    have := h (l + 1) (by simpa using hl) (a :: zs) ⟨ha, hz⟩
    simpa [consList_cons] using this

section Tower

variable {F : Nat} {env₁ envC : Env} {pp : BlockParts} {nestedBit : Bool} {pos : NestState}
  {cvTas : List ConstantVal} {block : List ConstantInfo}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 8000000 in
/-- **The minor premise of `(c, j)`, read at the rule prefix**: a Π-tower
whose first binder domains are the rule frame's declared field domains,
graded at every prefix spine fitting the rule prefix. -/
theorem genMinorTower (hμ : μ.verifiedChecks = true)
    (R : GenRecRun μ F (mkFEnv env₁) env₁ (mkFEnv envC) pp.toBlockShape nestedBit pos cvTas
      block ctorsAs out) (hg : ClassGenScoped R.g) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (mpC : EnvModelM V μ envC)
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
        envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2))
    (ψ : Name → Nat) {c j : Nat} (hc : c < (tgtRs out).length)
    (hj : j < blockRecNCt (tgtRs out) c) :
    ∃ (bs : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm),
      (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length ≤ bs.length ∧
      (bs.map (·.2.2)).take (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length
        = tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j ∧
      ∀ (ρ : Nat → V) (xs : List V),
        SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs →
        WellDenotedV V (consList xs ρ) (mkPisAV bs b) := by
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
  -- the rule frame's field domains are the tower's first binder data
  have hRP : tgtRP pp.toBlockShape c = R.g.pre.length := hrP
  have hfdL : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length = x.nF := by
    rw [tgtFdomsAV, readOpenedDoms_length_eq, hfl]
  have hbsl : bs.length = x.nF + x.recs.length := by rw [hbl]; simp [hfl, hihl]
  refine ⟨bs, b, by rw [hfdL, hbsl]; omega, ?_, fun ρ xs hxs => ?_⟩
  · refine List.ext_getElem (by simp [hfdL, hbsl]) fun r h1 h2 => ?_
    have hrF : r < x.nF := by rw [hfdL] at h2; exact h2
    have hrf : r < (tgtFieldFvs pp.toBlockShape out c j).length := by rw [hfl]; exact hrF
    obtain ⟨a, ha, hra⟩ := hbs r (R.g.binder (tgtFieldFvs pp.toBlockShape out c j)[r])
      (by rw [List.getElem?_append_left (by simpa using hrf)]; simp [hrf])
    have hbr : bs[r]'(by omega) = (0, pwBit ψ (R.g.binder
        (tgtFieldFvs pp.toBlockShape out c j)[r]).2.pw, a) := by
      rw [List.getElem?_eq_getElem (by omega)] at ha; exact Option.some.inj ha
    simp only [List.getElem_take, List.getElem_map, hbr]
    have := readOpenedDoms_getElem (acval := mpC.base2.acval) (env := envC) (ψ := ψ)
      R.g.pre.length _ r hrf
    simp only [ClassGen.binder] at hra
    rw [hra] at this
    simp only [tgtFdomsAV, hRP, this, Option.getD_some]
  · have hlenPd' : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        = R.g.pre.length := hlenPd.trans hrP
    have hxl : xs.length = R.g.pre.length := hxs.length_eq.trans hlenPd'
    have hsh : shiftE (R.g.pre.length - (R.g.nP + s)) 0 (consList xs ρ)
        = consList (xs.take (R.g.nP + s)) ρ := by
      have := shiftE_consList (V := V) (ys := ([] : List V)) (zs := xs) (ρ := ρ)
        (n := R.g.pre.length - (R.g.nP + s)) (k := 0) rfl (by omega)
      rw [show xs.length - (R.g.pre.length - (R.g.nP + s)) = R.g.nP + s by omega] at this
      exact this
    have hgr := blockRulePdomsAV_graded (V := V) hμ mpC h hr ψ (R.g.nP + s) (by omega) ρ
      (xs.take (R.g.nP + s)) (by
        have := spineFit_take hxs (i := R.g.nP + s) (by omega)
        exact this)
    rw [hPdget] at hgr
    rw [← hBE, WellDenotedV_liftN, hsh]
    exact hgr

end Tower

end ConLeche.Model
