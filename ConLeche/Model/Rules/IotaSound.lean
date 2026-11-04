module

public import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.EtaSoundKit
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.CtxOkKit
import ConLeche.Semantics.DefEqList

public section

/-!
# The soundness of the ι rule and the three stuck-major rescues (task #305, #342 L10, S5c)

One lemma per constructor: `Red.iota`, `Red.rescueK`, `Red.rescueEta`,
`Red.rescueAnd`; the master induction (`Sound.lean`) consumes them by
name.  The shared helpers live in `IotaSoundKit.lean`.

**Conditional premises, unconditional conclusions** (task #342, L10).
`Red.iota_sound`, `Red.rescueK_sound` and `Red.rescueAnd_sound` take
their premises' CONDITIONAL claims (`RedSem`, `DefEqSem`,
`DefEqListSem`, `TeleAritySem`, `CertsFSem`) and conclude the UNCONDITIONAL
`RedSemU`: no step reads that the redex is not the point.  The
induction of `Sound.lean` weakens the conclusion (`RedSemU.cond`).  The ι step's case split is read through the law's
`RecRuleExtra` (`Model/Env/Laws.lean`): the recursor's spine fits by
its certificate; a K rule fires by the law at the recursor's
own parameters.  At case 2 (the family never `Prop` at the comparand
levels; the step compared nothing) the major is not the point ((S)),
so its reduction is an equation and the fired application, not the
point either, fits its telescope (`teleFitPA_of_graded_ne_pt`); (T)
reads it at the comparand levels, where the law fires.  At case 3 the
step compared the constructor's levels, so the law fires at the
constructor's own levels: the fired application's value is the major's
(by the major's reduction where the major is not the point; by the
slot law (P) where it is), its spine fits (the full-grade certificate),
and where it is the point the comparisons the step ran give the law's
index pin ((U)).  The two fabricating rescues (K,
`And`) equate their fabrication with the major through the one type
both inhabit (`IsTy.eq_of_ne_pt`).  The structure-η rescue
(`Red.rescueEta_sound`, task #342 L11b) reads no certificate: the major
is its fabrication by the family's η law, and the fabrication is graded
by the η constructor's telescope coherence (`etaSide`).

## A rule shape this file relies on

**`DefEqListSem` concludes the walk's length.**  `Red.iota_sound`'s
`.nested` fire needs `pins.length = RecRule.ctorParams rl` before it
can build the comparand list's read spine at all, and the length is
needed to build the spines the motive's equation is about.
`DefEqListSem` therefore leads with `as.length = bs.length`,
discharged in `CertsSound.lean`'s `DefEqList.nil_sound`/`cons_sound`.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}
set_option linter.unusedVariables false in
/-- **The ι row** (task #342 L10, S5c): the stored recursor's fired
contract (`RecRuleLaw`) and its ι facts (`RecRuleExtra`), at the
recursor's telescope arity check over the redex's own spine,
the major prepared by a reduction, and — at case 3 only, decided at
the comparand levels — the level and parameter comparisons, the
constructor's full-grade certificate and the index comparison.  The
premises are the CONDITIONAL claims, the conclusion is the
unconditional one: no step reads that the redex is not the point; the
induction weakens it (`RedSemU.cond`).

Per valuation: the recursor's telescope fits the spine (the arity-checked
certificate).  At a K rule the law at the recursor's own parameters
gives everything; the major is not read.  At case 2 the major's domain
holds no point ((S)), so the major's reduction is an equation, the
fired application is not the point and fits its ∀-telescope, and (T)
moves it to the comparand levels, where the law fires.  At case 3 the
level comparison gives the law's level premise; the fired application's
value is the major's — by the major's reduction where the major is not
the point, by the slot law (P) where it is — its spine fits (the
full-grade certificate), where it is the point the comparisons the
step ran give the index pin ((U)), and the law fires. -/
theorem Red.iota_sound (hin : RulesInputs V m φ) {d : Nat} {e : Expr} {c : Name}
    {us : List Level} {cv : ConstantVal} {mI rP : Nat} {rules : List RecRule}
    {major : Expr} {cj : Name} {usj : List Level} {cvj : ConstantVal}
    {cnP cnF : Nat} {rl : RecRule} {residual : Expr}
    (hhead : e.getAppFn = .const c us)
    (hrec : env.find? c = some (.recInfo cv mI rP rules))
    (hlen : e.getAppArgs.length = mI + 1)
    (hus : us.length = cv.levelParams.length)
    (hmajor : RedSem m φ d (e.getAppArgs.getD mI (.bvar 0)) major)
    (hmhead : major.getAppFn = .const cj usj)
    (hctor : env.find? cj = some (.ctorInfo cvj cnP cnF))
    (hrule : rules.find? (fun r' => r'.ctor == cj) = some rl)
    (hmlen : major.getAppArgs.length = rl.ctorParams + rl.nfields)
    (hlv : ConLeche.iotaCase3 env.find? rl cvj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).1 = true →
      Level.isEquivList usj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).1 = some true)
    (hparams : ConLeche.iotaCase3 env.find? rl cvj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).1 = true →
      DefEqListSem m φ d (major.getAppArgs.take rl.ctorParams)
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).2)
    (hcertR : TeleAritySem m φ d (cv.type.instantiateLevelParams cv.levelParams us)
      e.getAppArgs)
    (hcertC : ConLeche.iotaCase3 env.find? rl cvj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).1 = true →
      CertsFSem m φ d (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs)
    (hres : ConLeche.iotaCase3 env.find? rl cvj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).1 = true → mI ≠ rP →
      ConLeche.piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = some residual)
    (hidx : ConLeche.iotaCase3 env.find? rl cvj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).1 = true → mI ≠ rP →
      DefEqListSem m φ d (residual.getAppArgs.drop rl.ctorParams)
        ((e.getAppArgs.take mI).drop rP)) :
    RedSem m φ d e
      (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)) := by
  intro hf Δa ea hC hea
  have hrmem : rl ∈ rules := List.mem_of_find?_eq_some hrule
  have hrctor : rl.ctor = cj := by
    have := List.find?_some hrule
    simpa using this
  subst hrctor
  -- **the law and its ι facts**, and the fired right-hand side's
  -- reading at every depth
  obtain ⟨hrPle, hlaw0, hextra⟩ := hin.rec_rules c cv mI rP rules hrec rl hrmem
  obtain ⟨Ra, hRa0, hokRa, hpinsOk, hlaw⟩ := hlaw0 us hus
  obtain ⟨hRaD, hRnf, hRbd⟩ := recRhs_depthK hrec hrmem hRa0
  -- the recursor spine, read
  have hfrE := frame_spine hf hC
  have hea' := hea
  rw [show e = Expr.mkAppN e.getAppFn e.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp e).symm, hhead] at hea'
  obtain ⟨vc, xs, hvc, hspx, rfl⟩ := denote_mkAppN_inv hea'
  rw [denote_const hrec (show us.length = _ from hus)] at hvc
  obtain rfl : vc = m.acval c (Level.substFn φ cv.levelParams us) :=
    (Option.some.inj hvc).symm
  have hxsLen : xs.length = mI + 1 := by rw [← hspx.length]; exact hlen
  -- the prepared major: read
  have hmIlt : mI < e.getAppArgs.length := by rw [hlen]; omega
  obtain ⟨hfMa, hCMa⟩ := hfrE _ (ConLeche.getD_mem hmIlt)
  have hdMaj : denote m.acval env φ d (e.getAppArgs.getD mI (.bvar 0))
      = some (xs.getD mI default) := hspx.getD _ mI hmIlt
  obtain ⟨hfmj, hsubmj, vmaj, hvmajSave, hInnerMaj⟩ := hmajor hfMa hCMa hdMaj
  have hCmj : CtxOkS m φ d Δa major := hCMa.of_subset hsubmj
  -- the constructor spine
  have hvmaj := hvmajSave
  rw [show major = Expr.mkAppN major.getAppFn major.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp major).symm, hmhead] at hvmaj
  obtain ⟨vj, ys, hvj, hspy, rfl⟩ := denote_mkAppN_inv hvmaj
  obtain ⟨hlenUj, rfl⟩ := denote_const_arityK hctor hvj
  have hfrC := frame_spine hfmj hCmj
  -- the two stored types
  obtain ⟨TVa, hTVaD, hokTVa, hmemR, hnfR, hbdR⟩ :=
    constTy_pkg hin.const_ty hrec (show us.length = _ from hus)
  obtain ⟨TVja, hTVjaD, hokTVja, hmemJ, hnfJ, hbdJ⟩ :=
    constTy_pkg hin.const_ty hctor hlenUj
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVaD hmemR hnfR hbdR
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVjaD hmemJ hnfJ hbdJ
  obtain ⟨hfR, hCR⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfR hbdR hC.1
  obtain ⟨hfJ, hCJ⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfJ hbdJ hC.1
  -- **the recursor's arity-checked fit**, over the redex's own spine
  obtain ⟨restR, hfitR⟩ :=
    hcertR (fa := m.acval c (Level.substFn φ cv.levelParams us))
      hfR hCR (hTVaD d) hfrE hspx
  -- the ι facts at the recursor's levels
  obtain ⟨hK, hext⟩ := hextra us hus TVa (hTVaD 0)
  obtain ⟨hstrip, hextNK⟩ := hext cvj cnP cnF hctor
  have hlenYs : ys.length = rl.ctorParams + rl.nfields := by
    rw [← hspy.length, hmlen]
  have hpcC : PiChain ys.length TVja := by
    rw [hlenYs]
    exact piChain_of_stripPis _
      (ConLeche.Expr.stripPis_instantiateLevelParams_isSome _ _ _ hstrip) (hTVjaD d)
  -- the comparand levels (currency-free: they read no arguments)
  have hcmpE : (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
      e.getAppArgs rP).1
      = (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1 :=
    recFireComparands_fst_nil _ _ _ _ _ _
  -- the reduct: framed, leaf-covered, read, and graded/equal at any ρ
  have hspOut : DenoteSpine m.acval env φ d
      (e.getAppArgs.take rP ++ major.getAppArgs.drop (RecRule.ctorParams rl))
      (xs.take rP ++ ys.drop (RecRule.ctorParams rl)) :=
    (hspx.take rP).append (hspy.drop _)
  refine ⟨frame_mkAppN ⟨ConLeche.Expr.WScoped.of_not_hasFvar hRnf, hRbd,
      ConLeche.Expr.LeavesBounded.of_not_hasFvar hRnf⟩ (fun y hy => ?_),
    leavesSub_mkAppN (leavesSub_of_not_hasFvar hRnf) (fun y hy => ?_),
    _, denote_mkAppN hspOut (hRaD d), fun ρ hρ hL hg hne => ?_⟩
  · rcases List.mem_append.mp hy with hy' | hy'
    · exact (hfrE y (List.mem_of_mem_take hy')).1
    · exact (hfrC y (List.mem_of_mem_drop hy')).1
  · rcases List.mem_append.mp hy with hy' | hy'
    · intro l hl
      exact ConLeche.fvarLeaves_getAppArgs (List.mem_of_mem_take hy') l hl
    · intro l hl
      exact ConLeche.fvarLeaves_getAppArgs (ConLeche.getD_mem hmIlt) l
        (hsubmj l (ConLeche.fvarLeaves_getAppArgs (List.mem_of_mem_drop hy') l hl))
  -- **per valuation**
  obtain ⟨-, hoX⟩ := hoist_spineV xs hg
  have hLmajSlot : LeavesGr m φ d (e.getAppArgs.getD mI (.bvar 0)) ρ :=
    leavesGr_spine hL _ (ConLeche.getD_mem hmIlt)
  have hokMajArg : WellDenoted V ρ (xs.getD mI default) :=
    hoX _ (ConLeche.getD_mem (by rw [← hspx.length]; exact hmIlt))
  have hLmj : LeavesGr m φ d major ρ := hLmajSlot.of_subset hsubmj
  have hLargsC : ∀ x ∈ major.getAppArgs, LeavesGr m φ d x ρ :=
    leavesGr_spine hLmj
  -- the recursor's fit
  obtain ⟨hfitRVal0, -⟩ :=
    hfitR ρ hρ
      (LeavesGr.of_fvarLeaves_nil
        (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfR))
      (leavesGr_spine hL) (hokTVa ρ) hoX ⟨hg, hmemR ρ, hne⟩
  have hsplit := take_getD_splitAK hxsLen
  have hfitRVal : TeleFitPA V ρ TVa (xs.take mI ++ [xs.getD mI default]) restR := by
    rw [← hsplit]; exact hfitRVal0
  have hoX0 : ∀ x ∈ xs.take mI, WellDenoted V ρ x :=
    fun x hx => hoX x (List.mem_of_mem_take hx)
  have hxs0len : (xs.take mI).length = mI := by
    rw [List.length_take, hxsLen]; omega
  have hsubj0 : interp V ρ (Term.mkAppN
      (m.acval c (Level.substFn φ cv.levelParams us)) xs)
      = interp V ρ (Term.mkAppN
        (m.acval c (Level.substFn φ cv.levelParams us))
        (xs.take mI ++ [xs.getD mI default])) := by
    rw [← hsplit]
  by_cases hk : rl.k = true
  · -- **K**: the law at the recursor's own parameters; the major is not read
    obtain ⟨hnf0, hKlaw⟩ := hK hk
    obtain ⟨heqK, htrK⟩ := hKlaw Ra hRa0 ρ (xs.take mI) _ restR hxs0len hfitRVal hoX0
    have hysdrop : ys.drop (RecRule.ctorParams rl) = [] :=
      List.drop_of_length_le (by rw [hlenYs, hnf0, Nat.add_zero]; exact Nat.le_refl _)
    have hred : xs.take rP ++ ys.drop (RecRule.ctorParams rl) = (xs.take mI).take rP := by
      rw [hysdrop, List.append_nil, List.take_take, Nat.min_eq_left hrPle]
    rw [hred]
    exact ⟨htrK hoX0, hsubj0.trans heqK⟩
  have hk' : rl.k = false := by simpa using hk
  obtain ⟨hS, hT, hPU⟩ := hextNK hk'
  by_cases h2 : ConLeche.iotaCase3 env.find? rl cvj
      (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).1
      = false
  · ---------------------------------------------------------------- case 2
    -- the case split at the comparand levels: the step compared nothing
    have hlic : ConLeche.iotaCtorNeverProp env.find? cvj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1 = true := by
      rw [← hcmpE]
      cases hl : ConLeche.iotaCtorNeverProp env.find? cvj
          (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).1
      · simp [ConLeche.iotaCase3, hk', hl] at h2
      · rfl
    -- the major is not the point (S): its reduction is an equation, and
    -- the fired application, not the point either, fits its telescope
    have hapt : interp V ρ (xs.getD mI default) ≠ pt :=
      hS hlic ρ (xs.take mI) _ restR hxs0len hfitRVal
    obtain ⟨hokMj, heqA⟩ := hInnerMaj ρ hρ hLmajSlot hokMajArg hapt
    obtain ⟨-, hoY⟩ := hoist_spineV ys hokMj
    have hne : interp V ρ (Term.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) ≠ pt := heqA ▸ hapt
    obtain ⟨restC, hfitC⟩ :=
      teleFitPA_of_graded_ne_pt ys hpcC (hokTVja ρ) (hmemJ ρ) hokMj hne
    obtain ⟨restR', hfitR'⟩ := teleFitPA_snoc_congr (xs.take mI) hfitRVal heqA
    -- (T): the fired application, read at the comparand levels
    obtain ⟨usj', ys', TVja', restC', hlen', hψ', hTVja', hyl', hdrop', hoY', hfitC', hval'⟩ :=
      hT hlic usj hlenUj TVja (hTVjaD 0) ρ (xs.take mI) ys restR' restC hxs0len hlenYs
        hfitR' hfitC hoX0 hoY hne
    obtain ⟨restR'', hfitR''⟩ := teleFitPA_snoc_congr (xs.take mI) hfitR' hval'.symm
    -- **fire the law** at the comparand levels
    obtain ⟨heqLaw, htrans⟩ := hlaw cvj cnP cnF hctor usj' ρ (xs.take mI) ys'
      TVa TVja' restR'' restC' hxs0len (by rw [hyl', hlenYs]) hlen' hψ' hoY'
      (fun hpt => absurd (hval' ▸ hpt) hne) (hTVaD 0) hTVja' hfitR'' hfitC'
    rw [List.take_take, Nat.min_eq_left hrPle, hdrop'] at heqLaw htrans
    have hsubj : interp V ρ (Term.mkAppN
        (m.acval c (Level.substFn φ cv.levelParams us)) xs)
        = interp V ρ (Term.mkAppN
          (m.acval c (Level.substFn φ cv.levelParams us))
          (xs.take mI ++ [Term.mkAppN
            (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj')) ys'])) := by
      rw [hsubj0]
      refine interp_mkAppN_congrK _ _ rfl ?_
      simp only [List.map_append, List.map_cons, List.map_nil, heqA, hval']
      rfl
    exact ⟨htrans hoX0 hoY', hsubj.trans heqLaw⟩
  ------------------------------------------------------------------ case 3
  have h3 : ConLeche.iotaCase3 env.find? rl cvj
      (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams e.getAppArgs rP).1
      = true := by simpa using h2
  -- the level comparison ran: the constructor's levels are the
  -- comparands' (currency-free: the comparand reads no arguments)
  have hψ : Level.substFn φ cvj.levelParams usj
      = Level.substFn φ cvj.levelParams
          (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
            [] rP).1 := by
    have hlv' := hlv h3
    rw [recFireComparands_fst_nil] at hlv'
    exact ConLeche.Level.substFn_congr (ConLeche.Level.isEquivList_sound hlv' φ)
  obtain ⟨hP, hU⟩ := hPU usj hlenUj hψ TVja (hTVjaD 0)
  -- the case-3 run, at this valuation
  have hC3 : (∀ y ∈ ys, WellDenoted V ρ y) ∧ ∃ restC, TeleFitPA V ρ TVja ys restC := by
    obtain ⟨restC, hC3⟩ := hcertC h3 hfJ hCJ (hTVjaD d) hfrC hspy
    obtain ⟨hoY, hfitC, -⟩ := hC3 ρ hρ
      (LeavesGr.of_fvarLeaves_nil
        (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ))
      hLargsC (hokTVja ρ)
    exact ⟨hoY, restC, hfitC⟩
  -- **the fired constructor application is the major's value**
  have hcase : interp V ρ (xs.getD mI default)
        = interp V ρ (Term.mkAppN
            (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) ∧
      (∀ y ∈ ys, WellDenoted V ρ y) ∧
      ∃ restC, TeleFitPA V ρ TVja ys restC := by
    by_cases hapt : interp V ρ (xs.getD mI default) = pt
    · -- case 3 at a `Prop` valuation: the slot law (P)
      obtain ⟨hoY, restC, hfitC⟩ := hC3
      refine ⟨?_, hoY, restC, hfitC⟩
      rw [hapt, hP ρ (xs.take mI) _ restR hxs0len hfitRVal hapt ys restC hfitC hlenYs hoY]
    · -- the major is not the point: its reduction is an equation
      obtain ⟨hokMj, heqAll⟩ := hInnerMaj ρ hρ hLmajSlot hokMajArg hapt
      obtain ⟨-, hoY⟩ := hoist_spineV ys hokMj
      refine ⟨heqAll, hoY, ?_⟩
      exact teleFitPA_of_graded_ne_pt ys hpcC (hokTVja ρ) (hmemJ ρ) hokMj
        (heqAll ▸ hapt)
  obtain ⟨heqA, hoY, restC, hfitC⟩ := hcase
  obtain ⟨restR', hfitR'⟩ := teleFitPA_snoc_congr (xs.take mI) hfitRVal heqA
  have hcase3_of_ptC : interp V ρ (Term.mkAppN
      (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) = pt →
      ConLeche.iotaCase3 env.find? rl cvj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).1 = true :=
    fun _ => h3
  -- **the comparisons the step ran (case 3: where the fired
  -- application is the point), conditional**
  -- the `.plain` parameters
  have hplainC : RecRule.fire rl = .plain →
      interp V ρ (Term.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) = pt →
      ∀ i, i < RecRule.ctorParams rl → i < mI →
        interp V ρ (ys.getD i default) ≠ pt →
        interp V ρ ((xs.take mI).getD i default) ≠ pt →
        interp V ρ (ys.getD i default) = interp V ρ ((xs.take mI).getD i default) := by
    intro hp hpt i hi him hy hx
    have hdefP := hparams (hcase3_of_ptC hpt)
    rw [show (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
        e.getAppArgs rP).2 = e.getAppArgs.take (RecRule.ctorParams rl) from by
      unfold ConLeche.recFireComparands; rw [hp]] at hdefP
    have hz := hdefP.2
      (fun x hx => hfrC x (List.mem_of_mem_take hx))
      (fun x hx => hfrE x (List.mem_of_mem_take hx))
      (hspy.take _) (hspx.take _) ρ hρ
      (fun x hx => hLargsC x (List.mem_of_mem_take hx))
      (fun x hx => leavesGr_spine hL x (List.mem_of_mem_take hx))
      (fun x hx => hoY x (List.mem_of_mem_take hx))
      (fun x hx => hoX x (List.mem_of_mem_take hx))
    have hlt : i < (ys.take (RecRule.ctorParams rl)).length := by
      rw [List.length_take, hlenYs]; omega
    have hlenT : (ys.take (RecRule.ctorParams rl)).length
        = (xs.take (RecRule.ctorParams rl)).length := by
      have h1 := hdefP.1
      have h2 := hspy.length
      have h3 := hspx.length
      simp only [List.length_take] at h1 ⊢
      omega
    have hgi := zip_cond_getD (f := interp V ρ) hlenT hz i hlt
      (by rw [getD_takeAK hi]; exact hy)
      (by rw [getD_takeAK hi]; rw [getD_takeAK him] at hx; exact hx)
    rw [getD_takeAK hi, getD_takeAK hi] at hgi
    rw [getD_takeAK him]
    exact hgi
  -- the `.nested` pins
  have hnestedC : ∀ lvls pins, RecRule.fire rl = .nested lvls pins →
      interp V ρ (Term.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) = pt →
      ∀ i, i < RecRule.ctorParams rl →
      ∀ vpa : Term,
        denote m.acval env φ rP (ConLeche.Verify.openRev 0 rP
          ((pins.getD i default).instantiateLevelParams cv.levelParams us))
          = some vpa →
        interp V ρ (ys.getD i default) ≠ pt →
        interp V ρ (Term.instRevChain ((xs.take mI).take rP) vpa) ≠ pt →
        interp V ρ (ys.getD i default)
          = interp V ρ (Term.instRevChain ((xs.take mI).take rP) vpa) := by
    intro lvls pins hn hpt i hi vpa hvpa hy hx
    have hdefP' := hparams (hcase3_of_ptC hpt)
    obtain ⟨-, -, -, -, -, hrec', -⟩ :=
      m.wf.consts _ (ConLeche.Env.find?_mem hrec)
    obtain ⟨-, -, -, -, hnest⟩ := hrec' cv mI rP rules rfl rl hrmem
    obtain ⟨-, -, hpinsWf, -⟩ := hnest lvls pins hn
    have hpinF' : ∀ p ∈ pins,
        (p.instantiateLevelParams cv.levelParams us).hasFvar = false := by
      intro p hp
      obtain ⟨hpinF, -, -, -⟩ := hpinsWf p hp
      rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hpinF
    have hcmp : (ConLeche.recFireComparands rl cv.levelParams us
        cvj.levelParams e.getAppArgs rP).2
        = pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            (p.instantiateLevelParams cv.levelParams us)) := by
      unfold ConLeche.recFireComparands; rw [hn]
    have hprelen : (e.getAppArgs.take rP).length = rP := by
      rw [List.length_take, hlen]; omega
    have hargsPre : ∀ x ∈ e.getAppArgs.take rP, Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true := by
      intro x hx
      obtain ⟨⟨hw2, hb2, -⟩, -⟩ := hfrE x (List.mem_of_mem_take hx)
      exact ⟨hw2, hb2⟩
    have hlenPins : pins.length = RecRule.ctorParams rl := by
      have h1 := hdefP'.1
      rw [hcmp, List.length_map, List.length_take, hmlen] at h1
      omega
    -- the frames of the comparand list
    have hfrPin : ∀ (p : Expr), p ∈ pins →
        Frame d (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us)) ∧
        CtxOkS m φ d Δa (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us)) := by
      intro p hp
      obtain ⟨hpinF, -, -, hpinB⟩ := hpinsWf p hp
      have hpinF0 : (p.instantiateLevelParams cv.levelParams us).hasFvar
          = false := hpinF' p hp
      have hpinB' : (p.instantiateLevelParams cv.levelParams
          us).looseBVarsBounded (e.getAppArgs.take rP).length = true := by
        rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams, hprelen]
        exact hpinB
      refine ⟨⟨ConLeche.instSpine_WScoped _
          (ConLeche.Expr.WScoped.of_not_hasFvar hpinF0)
          (fun y hy => (hargsPre y hy).1), ?_, fun l hl => ?_⟩,
        ⟨hC.1, fun l hl => ?_⟩⟩
      · rw [show rP - 1 = (e.getAppArgs.take rP).length - 1 from by
          rw [hprelen]]
        exact ConLeche.instSpine_closed (fun y hy => (hargsPre y hy).2) hpinB'
      · rcases ConLeche.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
        · exact absurd hl' (by
            rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hpinF0]; simp)
        · exact (hfrE y (List.mem_of_mem_take hy)).1.2.2 l hly
      · rcases ConLeche.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
        · exact absurd hl' (by
            rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hpinF0]; simp)
        · exact ((hfrE y (List.mem_of_mem_take hy)).2).2 l hly
    -- the comparand's LEAVES, graded at this ρ off the recursor's own
    -- prefix (the pin itself is closed)
    have hLComp : ∀ (p : Expr), p ∈ pins →
        LeavesGr m φ d (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us)) ρ := by
      intro p hp l hl tya hden
      rcases ConLeche.fvarLeaves_instSpine _ hl with hl' | ⟨y, hy, hly⟩
      · exact absurd hl' (by
          rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar (hpinF' p hp)]; simp)
      · exact leavesGr_spine hL y (List.mem_of_mem_take hy) l hly tya hden
    -- each comparand reads, to the pin's open reading chained along the
    -- recursor's parameter prefix
    have hcompRead : ∀ (p : Expr), p ∈ pins →
        denote m.acval env φ d
            (Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
              (p.instantiateLevelParams cv.levelParams us))
          = (denote m.acval env φ rP (ConLeche.Verify.openRev 0 rP
              (p.instantiateLevelParams cv.levelParams us))).map
              (Term.instRevChain (xs.take rP)) := by
      intro p hp
      have hpinF0 : (p.instantiateLevelParams cv.levelParams us).hasFvar
          = false := hpinF' p hp
      obtain ⟨-, -, -, hpinB⟩ := hpinsWf p hp
      have hpinB' : (p.instantiateLevelParams cv.levelParams
          us).looseBVarsBounded (e.getAppArgs.take rP).length = true := by
        rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams, hprelen]
        exact hpinB
      have hcden := denote_openRevK m.acval_closed (acval_inst_self m)
        (e.getAppArgs.take rP) hargsPre
        ((ConLeche.Expr.WScoped.of_not_hasFvar (d := d) hpinF0).fvarsBelow)
        hpinB' (hspx.take rP)
      rw [hprelen] at hcden
      have hbase := denote_openRev_base (env := env) (φ := φ)
        m.acval_closed m.cval_closed hpinF0
        (by rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
            exact hpinB) d
      rw [hbase] at hcden
      rw [Expr.instSpine_eq_instSeq]
      simpa using hcden
    -- so the comparand list reads, and its readings are graded by the
    -- law's context-guarded pin conjunct
    have hbsRead : ∀ x ∈ pins.map (fun p =>
        Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us)),
        ∃ v, denote m.acval env φ d x = some v := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨j, hj, hpj⟩ := mem_getD_index hp
      obtain ⟨vpa', hvpa', -⟩ := hpinsOk lvls pins hn j (by omega)
      rw [hcompRead p hp, ← hpj, hvpa']
      exact ⟨_, rfl⟩
    obtain ⟨bsa, hspB⟩ := DenoteSpine.exists_of_all _ hbsRead
    have hokChain : ∀ (vv : Term) (j : Nat), j < pins.length →
        denote m.acval env φ rP (ConLeche.Verify.openRev 0 rP
          ((pins.getD j default).instantiateLevelParams cv.levelParams us))
          = some vv →
        WellDenoted V ρ (Term.instRevChain (xs.take rP) vv) := by
      intro vv j hj hvv
      obtain ⟨vpa', hvpa', hok'⟩ := hpinsOk lvls pins hn j (by omega)
      obtain rfl : vpa' = vv := Option.some.inj (hvpa'.symm.trans hvv)
      obtain ⟨mid, hmid⟩ := hfitRVal0.take rP
      exact hok' ρ (xs.take rP) TVa mid
        (by rw [List.length_take, hxsLen]; omega)
        (fun v hv => hoX v (List.mem_of_mem_take hv))
        (hTVaD 0) hmid
    have hgetB : ∀ j, j < pins.length →
        denote m.acval env φ d
            ((pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
              (p.instantiateLevelParams cv.levelParams us))).getD j default)
          = (denote m.acval env φ rP (ConLeche.Verify.openRev 0 rP
              ((pins.getD j default).instantiateLevelParams cv.levelParams us))).map
              (Term.instRevChain (xs.take rP)) := by
      intro j hj
      rw [show (pins.map (fun p => Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
          (p.instantiateLevelParams cv.levelParams us))).getD j default
          = Expr.instSpine (e.getAppArgs.take rP) (rP - 1)
            ((pins.getD j default).instantiateLevelParams cv.levelParams us) from by
        simp [List.getD, List.getElem?_map, List.getElem?_eq_getElem hj]]
      exact hcompRead _ (ConLeche.getD_mem hj)
    have hlenB : pins.length = bsa.length := by
      have := hspB.length
      simpa using this
    have hgB : ∀ x ∈ bsa, WellDenoted V ρ x := by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := mem_getD_index hx
      have hjp : j < pins.length := by omega
      have h1 := hspB.getD (default : Expr) j (by
        rw [List.length_map]; omega)
      rw [hgetB j hjp] at h1
      obtain ⟨vpa', hvpa', -⟩ := hpinsOk lvls pins hn j (by omega)
      rw [hvpa'] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      rw [← h1]
      exact hokChain vpa' j hjp hvpa'
    have hLb2 : ∀ x ∈ pins.map (fun p => Expr.instSpine
        (e.getAppArgs.take rP) (rP - 1)
        (p.instantiateLevelParams cv.levelParams us)),
        LeavesGr m φ d x ρ := by
      intro x hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hLComp p hp
    rw [hcmp] at hdefP'
    have hz := hdefP'.2
      (fun x hx => hfrC x (List.mem_of_mem_take hx))
      (fun x hx => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        exact hfrPin p hp)
      (hspy.take _) hspB ρ hρ
      (fun x hx => hLargsC x (List.mem_of_mem_take hx))
      hLb2
      (fun x hx => hoY x (List.mem_of_mem_take hx)) hgB
    -- the `i`-th comparand's reading is the chained pin
    have hiB := hspB.getD (default : Expr) i (by
      simp only [List.length_map]; omega)
    rw [hgetB i (by omega), hvpa] at hiB
    simp only [Option.map_some, Option.some.injEq] at hiB
    have hlt : i < (ys.take (RecRule.ctorParams rl)).length := by
      rw [List.length_take, hlenYs]; omega
    have hlenT : (ys.take (RecRule.ctorParams rl)).length = bsa.length := by
      rw [List.length_take, hlenYs, ← hlenB, hlenPins]; omega
    rw [List.take_take, Nat.min_eq_left hrPle] at hx ⊢
    have hgi := zip_cond_getD (f := interp V ρ) hlenT hz i hlt
      (by rw [getD_takeAK hi]; exact hy) (by rw [← hiB]; exact hx)
    rw [getD_takeAK hi, ← hiB] at hgi
    exact hgi
  -- the index pin, where the fired application is the point (case 3)
  have hpinC : interp V ρ (Term.mkAppN
      (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys) = pt →
      IotaIndexPinC (V := V) ρ restC (RecRule.ctorParams rl) mI rP (xs.take mI) := by
    intro hpt
    have h3 := hcase3_of_ptC hpt
    by_cases hmr : mI = rP
    · exact ⟨restC, [], rfl, Or.inl hmr, fun i hi => absurd hi (by omega)⟩
    have hpres := hres h3 hmr
    obtain ⟨hfRes, hCRes⟩ := piResidual_frameK hpres hfJ hCJ hfrC
    have hLRes : LeavesGr m φ d residual ρ :=
      piResidual_leavesGrK hpres
        (LeavesGr.of_fvarLeaves_nil
          (ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfJ))
        hLargsC
    have hfrRes := frame_spine hfRes hCRes
    have hresC : denote m.acval env φ d residual = some restC :=
      teleFitPA_residualK m.acval_closed (acval_inst_self m) major.getAppArgs
        hpres hfJ.1 (fun x hx => ⟨(hfrC x hx).1.1, (hfrC x hx).1.2.1⟩)
        (hTVjaD d) hspy hfitC
    rw [show residual = Expr.mkAppN residual.getAppFn residual.getAppArgs from
      (ConLeche.Expr.mkAppN_getApp residual).symm] at hresC
    obtain ⟨Ha, cargsa, -, hspRes, hCeq⟩ := denote_mkAppN_inv hresC
    -- the residual is graded: the constructor's fit grades its residual
    have hRcA : WellDenoted V ρ (Term.mkAppN Ha cargsa) :=
      hCeq ▸ teleFitPA_rest_graded hfitC (hokTVja ρ) hoY
    obtain ⟨-, hoCargs⟩ := hoist_spineV cargsa hRcA
    have hspIdx : DenoteSpine m.acval env φ d ((e.getAppArgs.take mI).drop rP)
        ((xs.take mI).drop rP) := (hspx.take mI).drop rP
    have hdefI := hidx h3 hmr
    have hzI := hdefI.2
        (fun x hx => hfrRes x (List.mem_of_mem_drop hx))
        (fun x hx => hfrE x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
        (hspRes.drop _) hspIdx ρ hρ
        (fun x hx => leavesGr_spine hLRes x (List.mem_of_mem_drop hx))
        (fun x hx => leavesGr_spine hL x
          (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
        (fun x hx => hoCargs x (List.mem_of_mem_drop hx))
        (fun x hx => hoX x (List.mem_of_mem_take (List.mem_of_mem_drop hx)))
    have hlen1 := hdefI.1
    have hlenI : (cargsa.drop (RecRule.ctorParams rl)).length
        = ((xs.take mI).drop rP).length := by
      have h2 := hspRes.length
      have h3 := hspx.length
      simp only [List.length_drop, List.length_take] at hlen1 ⊢
      omega
    have hlenDisj : mI = rP ∨
        cargsa.length = RecRule.ctorParams rl + (mI - rP) := by
      simp only [List.length_drop, List.length_take] at hlenI
      rw [hxsLen] at hlenI
      omega
    refine ⟨Ha, cargsa, hCeq, hlenDisj, fun i hi hy hx => ?_⟩
    have hlt : i < (cargsa.drop (RecRule.ctorParams rl)).length := by
      rw [List.length_drop]
      rcases hlenDisj with hh | hh <;> omega
    have hgi := zip_cond_getD (f := interp V ρ) hlenI hzI i hlt
      (by rw [getD_dropAK]; exact hy) (by rw [getD_dropAK]; exact hx)
    rw [getD_dropAK, getD_dropAK] at hgi
    exact hgi
  -- **(U)**: where the fired application is the point, the index pin
  have hpinU :=
    hU ρ (xs.take mI) ys restR' restC hxs0len hlenYs hfitR' hfitC hoX0 hoY
      hplainC hnestedC hpinC
  -- **fire the law**
  obtain ⟨heqLaw, htrans⟩ := hlaw cvj cnP cnF hctor usj ρ (xs.take mI) ys
    TVa TVja restR' restC hxs0len hlenYs hlenUj hψ hoY hpinU
    (hTVaD 0) (hTVjaD 0) hfitR' hfitC
  rw [List.take_take, Nat.min_eq_left hrPle] at heqLaw htrans
  have hsubj : interp V ρ (Term.mkAppN
      (m.acval c (Level.substFn φ cv.levelParams us)) xs)
      = interp V ρ (Term.mkAppN
        (m.acval c (Level.substFn φ cv.levelParams us))
        (xs.take mI ++ [Term.mkAppN
          (m.acval rl.ctor (Level.substFn φ cvj.levelParams usj)) ys])) := by
    rw [hsubj0]
    refine interp_mkAppN_congrK _ _ rfl ?_
    simp only [List.map_append, List.map_cons, List.map_nil, heqA]
  exact ⟨htrans hoX0 hoY, hsubj.trans heqLaw⟩

set_option linter.unusedVariables false in
/-- **The K rescue** (task #342 L18): the major is a proof — its io
type's io sort reduces to `Prop` (`htp`, `hpt`: the major's half of the
checker's `proofIrrel` run) — so it is the point at every valuation
(`PropPt`), and a reduction claims nothing of the point: the
conditional claim is vacuous.  The fabrication's frame and reading are
syntactic (the scope guards, the stored constructor's type).

The rule's certificate on the fabricated spine, the fabrication's type
check and the K flag are what make the checker take this branch; the
model reads none of them (the certificate's io claims would not hold
the spine's values, `IORel`).  Hence the linter option. -/
theorem Red.rescueK_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tp : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat} {T : Name}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (hk : rl.k = true)
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const T tus)
    (hind : env.find? T = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSem m φ d tm tmaj)
    (hthead : tmaj.getAppFn = .const T ust)
    (hlv : cvj.levelParams.length = ust.length)
    (hnP : cnP ≤ tmaj.getAppArgs.length)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust) (tmaj.getAppArgs.take cnP))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (htp : InferSemIO m φ d major tp) (hpt : PropPt m φ d tp) :
    RedSem m φ d major fab := by
  intro hfM Δa ea hCM hea
  -- the fabrication's frame comes with the rule's three scope guards
  have hsub : LeavesSub fab major := fun l hl => by
    have := List.all_eq_true.mp hlv' l hl
    simpa using this
  have hfF : Frame d fab :=
    ⟨Expr.WScoped.of_wscopedB hws, hb, fun l hl => hfM.2.2 l (hsub l hl)⟩
  -- the major's io-inferred type, reduced, is the family at its spine
  obtain ⟨hfT0, hsubT0, tm0a, htm0a, -⟩ := htm hfM hCM hea
  obtain ⟨-, -, tmaja, htmaja, -⟩ := htmaj hfT0 (hCM.of_subset hsubT0) htm0a
  rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp tmaj).symm, hthead] at htmaja
  obtain ⟨vT, tsa, -, hspt, rfl⟩ := denote_mkAppN_inv htmaja
  -- the fabrication reads
  have hheadCj : denote m.acval env φ d (.const rl.ctor ust)
      = some (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) :=
    denote_const hctor (show ust.length = _ from hlv.symm)
  have hdF : denote m.acval env φ d fab
      = some (Term.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) (tsa.take cnP)) := by
    rw [hfab]; exact denote_mkAppN (hspt.take cnP) hheadCj
  refine ⟨hfF, hsub, _, hdF, fun ρ hρ hL hg hne => ?_⟩
  -- the major is a proof, the point: nothing is claimed
  obtain ⟨hftp, hsubtp, tpa, htpa, hrowP⟩ := htp hfM hCM hea
  exact absurd (hpt hftp (hCM.of_subset hsubtp) htpa ρ _ hρ (hL.of_subset hsubtp)
    (hrowP ρ hρ hL hg).1) hne

/-- **The structure-η rescue** (task #342 L11b): no certificate.  The
major's io-inferred type is a type ("not pt" source (1)), so its reduct
is graded and equal; `etaSide` then gives the η law (the major IS the
fabrication's value) and the coherence law (the fabricated spine fits
the η constructor's telescope), so the fabrication is graded
(`mkAppN_of_fitA`).  The major may be the point: the laws hold at every
member where the major is not the point: its io type reduces to the
family's application, no ∀, so its io claim is a membership there
(`IORel.mem_of_red`).  Conditional (task #342 L18). -/
theorem Red.rescueEta_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat} {T : Name}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (heta : rl.eta = true)
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const T tus)
    (hind : env.find? T = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSem m φ d tm tmaj)
    (htmajr : Red env d tm tmaj)
    (hthead : tmaj.getAppFn = .const T ust)
    (hlen : tmaj.getAppArgs.length = caps.etaParams)
    (hlv : ust.length = cvT.levelParams.length)
    (_hnz : ConLeche.capsNeverZero cvT.levelParams ust caps = true)
    (hfab : fab = Expr.mkAppN (.const caps.etaCtor ust)
      (ConLeche.etaFabArgsE T tmaj.getAppArgs major caps.etaFields))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hresT : ConLeche.reservedBasisNames.contains T = false)
    (hresC : ConLeche.reservedBasisNames.contains caps.etaCtor = false)
    (htow : ConLeche.towerSlotsAll env T caps.etaFields = true) :
    RedSem m φ d major fab := by
  intro hfM Δa ea hCM hea
  have hsub : LeavesSub fab major := fun l hl => by
    have := List.all_eq_true.mp hlv' l hl
    simpa using this
  have hfF : Frame d fab :=
    ⟨Expr.WScoped.of_wscopedB hws, hb, fun l hl => hfM.2.2 l (hsub l hl)⟩
  -- the family's η record: the rule's constructor IS the family's, and
  -- carries the former's level parameters (`RecCtorsStored`)
  obtain ⟨-, hEbits⟩ := ConLeche.recCtors_bits m.rec_ctors hrec
    List.mem_cons_self hctor hres hind
  obtain ⟨hcapseta, hectr, hlpsE⟩ := hEbits heta
  have hfC : env.find? caps.etaCtor = some (.ctorInfo cvj cnP cnF) := by
    rw [← hectr]; exact hctor
  have hlpj : ust.length = cvj.levelParams.length := by
    rw [hlpsE]; exact hlv
  -- the major's io-inferred type, reduced, is the family at its spine
  obtain ⟨hfT0, hsubT0, tm0a, htm0a, hInnerTm0⟩ := htm hfM hCM hea
  obtain ⟨hfTm, hsubTm, tmaja, htmaja, hInnerTmaj⟩ :=
    htmaj hfT0 (hCM.of_subset hsubT0) htm0a
  have hCTm : CtxOkS m φ d Δa tmaj :=
    (hCM.of_subset hsubT0).of_subset hsubTm
  rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp tmaj).symm, hthead] at htmaja
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denote_mkAppN_inv htmaja
  have hvT' : vT = m.acval T (Level.substFn φ cvT.levelParams ust) := by
    rw [denote_const hind (show ust.length
      = (ConLeche.ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
      from hlv)] at hvT
    exact (Option.some.inj hvT).symm
  subst hvT'
  -- the stuck side's facts
  obtain ⟨ps, hsps, hfps, TCa, hTCa, hside⟩ := etaSide hin hind hcapseta hresT hresC
    hfC hlv hlen htow hfM hCM hea hspt
  -- the fabrication reads
  have hheadC : denote m.acval env φ d (.const caps.etaCtor ust)
      = some (m.acval caps.etaCtor (Level.substFn φ cvT.levelParams ust)) := by
    have h := denote_const (acval := m.acval) (φ := φ) (d := d) hfC
      (show ust.length = _ from hlpj)
    dsimp only [ConLeche.ConstantInfo.toConstantVal] at h
    rw [h, hlpsE]
  have hspF : DenoteSpine m.acval env φ d
      (ConLeche.etaFabArgsE T tmaj.getAppArgs major caps.etaFields)
      (tsa ++ ps) := hspt.append hsps
  have hdF : denote m.acval env φ d fab
      = some (Term.mkAppN
        (m.acval caps.etaCtor (Level.substFn φ cvT.levelParams ust)) (tsa ++ ps)) := by
    rw [hfab]; exact denote_mkAppN hspF hheadC
  -- the constructor's type reading holds its leaf
  obtain ⟨tc, htc, hoktc, hmemC, -, -⟩ :=
    constTy_pkg hin.const_ty hfC (show ust.length = _ from hlpj)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at htc hmemC
  obtain rfl : TCa = tc := Option.some.inj (hTCa.symm.trans (htc 0))
  refine ⟨hfF, hsub, _, hdF, fun ρ hρ hL hg hne => ?_⟩
  obtain ⟨hgT0, hmemM0⟩ := (IORel.mem_of_red (hInnerTm0 ρ hρ hL hg).1 hne htmajr
    (not_forallE_of_getAppFn hthead)).of_reading htm0a
  obtain ⟨hgTm, heqTm⟩ := hInnerTmaj ρ hρ (hL.of_subset hsubT0) hgT0.1 hgT0.ne_pt
  have hmemMW : interp V ρ ea ∈ˢ interp V ρ (Term.mkAppN
      (m.acval T (Level.substFn φ cvT.levelParams ust)) tsa) := heqTm ▸ hmemM0
  have hneW : interp V ρ (Term.mkAppN
      (m.acval T (Level.substFn φ cvT.levelParams ust)) tsa) ≠ pt := by
    rw [← heqTm]; exact hgT0.ne_pt
  have hLtmaj : LeavesGr m φ d tmaj ρ := (hL.of_subset hsubT0).of_subset hsubTm
  obtain ⟨-, hokps, hbη, restC, hfitC⟩ :=
    hside ρ hρ hL (leavesGr_spine hLtmaj) hgTm hneW hg hmemMW
  -- the fabrication is graded: its spine fits the constructor's
  -- telescope (the coherence law)
  have hpc : PiChain (tsa ++ ps).length TCa := by
    have := piChain_of_teleFit hfitC
    rwa [List.length_map] at this
  obtain ⟨resta, hfitPA⟩ := teleFitPA_of_teleFit (tsa ++ ps) hpc hfitC
  obtain ⟨-, hoTs⟩ := hoist_spineV tsa hgTm
  have hoksF : ∀ x ∈ tsa ++ ps, WellDenoted V ρ x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hoTs x hx'
    · exact hokps x hx'
  have hmemC' : interp V ρ (m.acval caps.etaCtor (Level.substFn φ cvT.levelParams ust))
      ∈ˢ interp V ρ TCa := by
    rw [← hlpsE]; exact hmemC ρ
  have hgF := (mkAppN_of_fitA (tsa ++ ps) (hoktc ρ)
    (m.acval_wellDenoted _ _ ρ) hoksF hmemC' hfitPA).1
  refine ⟨hgF, ?_⟩
  rw [hbη, interp_mkAppN, List.foldl_map]

set_option linter.unusedVariables false in
/-- **The `And` rescue** (task #342 L18): as the K rescue, the major is
a proof (`htp`, `hpt`), the point at every valuation, and the
conditional claim is vacuous; the fabrication's frame and reading are
syntactic.  The certificate, the type check and the two stored slots
make the checker take the branch; the model reads them only for the
fabrication's reading. -/
theorem Red.rescueAnd_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tp : Expr} {recName : Name} {cv : ConstantVal}
    {mI rP : Nat} {rl : RecRule} {cvj : ConstantVal} {cnP cnF : Nat}
    {tus ust : List Level} {cvT : ConstantVal} {caps : IndCaps}
    (hrec : env.find? recName = some (.recInfo cv mI rP [rl]))
    (hctor : env.find? rl.ctor = some (.ctorInfo cvj cnP cnF))
    (hres : (cvj.type.piResult).getAppFn = .const andName tus)
    (hind : env.find? andName = some (.indInfo cvT caps))
    (htm : InferSemIO m φ d major tm) (htmaj : RedSem m φ d tm tmaj)
    (hthead : tmaj.getAppFn = .const andName ust)
    (hlen : tmaj.getAppArgs.length = cnP)
    (hlv : cvj.levelParams.length = ust.length)
    (hslots : ConLeche.andRescueSlots env rl.ctor cnP = true)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust)
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (htp : InferSemIO m φ d major tp) (hpt : PropPt m φ d tp) :
    RedSem m φ d major fab := by
  intro hfM Δa ea hCM hea
  have hsub : LeavesSub fab major := fun l hl => by
    have := List.all_eq_true.mp hlv' l hl
    simpa using this
  have hfF : Frame d fab :=
    ⟨Expr.WScoped.of_wscopedB hws, hb, fun l hl => hfM.2.2 l (hsub l hl)⟩
  -- the major's io-inferred type, reduced, is `And` at its parameters
  obtain ⟨hfT0, hsubT0, tm0a, htm0a, -⟩ := htm hfM hCM hea
  obtain ⟨-, -, tmaja, htmaja, -⟩ := htmaj hfT0 (hCM.of_subset hsubT0) htm0a
  rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp tmaj).symm, hthead] at htmaja
  obtain ⟨vT, tsa, -, hspt, rfl⟩ := denote_mkAppN_inv htmaja
  have hslot := ConLeche.andRescueSlots_inv hslots
  -- each projection reads to the tower reading
  have hprojR : ∀ j, j < 2 →
      denote m.acval env φ d (Expr.proj andName j major)
        = some (projNV (j + 1) ea) := by
    intro j hj
    obtain ⟨entry, hfe, -, -, -⟩ := hslot j hj
    exact denote_proj_tower hfe hea
  -- the fabrication reads
  have hheadCj : denote m.acval env φ d (.const rl.ctor ust)
      = some (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) :=
    denote_const hctor (show ust.length = _ from hlv.symm)
  have hspF : DenoteSpine m.acval env φ d
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major])
      (tsa ++ [projNV (0 + 1) ea,
        projNV (1 + 1) ea]) :=
    hspt.append (DenoteSpine.cons (hprojR 0 (by decide))
      (DenoteSpine.cons (hprojR 1 (by decide)) DenoteSpine.nil))
  have hdF : denote m.acval env φ d fab
      = some (Term.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (tsa ++ [projNV (0 + 1) ea,
          projNV (1 + 1) ea])) := by
    rw [hfab]; exact denote_mkAppN hspF hheadCj
  refine ⟨hfF, hsub, _, hdF, fun ρ hρ hL hg hne => ?_⟩
  -- the major is a proof, the point: nothing is claimed
  obtain ⟨hftp, hsubtp, tpa, htpa, hrowP⟩ := htp hfM hCM hea
  exact absurd (hpt hftp (hCM.of_subset hsubtp) htpa ρ _ hρ (hL.of_subset hsubtp)
    (hrowP ρ hρ hL hg).1) hne

end ConLeche.Model.Rules
