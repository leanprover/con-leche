module

public import ConLeche.Model.Rules.Inputs
public import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.CtxOkKit

public section

/-!
# The soundness of the ι rule and the three stuck-major rescues (task #305, lane S-iota)

Split out of `RedSound.lean` before the proof phase so the two lanes
own disjoint files.  One lemma per constructor: `Red.iota`,
`Red.rescueK`, `Red.rescueEta`, `Red.rescueAnd`; the master induction
(`Sound.lean`) consumes them by name.
-/

namespace ConLeche.Model.Rules
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name)
open ConLeche.Rules

universe w

variable {V : Type w} [SetTheory V] {env : Env} {m : EnvModel V env}
  {φ : Name → Nat}
/-- The ι row (`iotaStep_of`, `Steps/IotaRows.lean:492`, with
`iotaReads_of`, `:332`, for the reduct's reading): the stored
recursor's fired contract (`RecRules`) at the two certified telescopes
and the parameter/index comparisons. -/
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
    (hfire : rl.fire ≠ .inert)
    (hlv : Level.isEquivList usj
      (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
        e.getAppArgs rP).1 = some true)
    (hparams : rl.compareParams = true →
      DefEqListSem m φ d (major.getAppArgs.take rl.ctorParams)
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams
          e.getAppArgs rP).2)
    (hcertR : CertsSem m φ d true (cv.type.instantiateLevelParams cv.levelParams us)
      (e.getAppArgs.take mI ++ [major]))
    (hcertC : CertsSem m φ d true
      (cvj.type.instantiateLevelParams cvj.levelParams usj) major.getAppArgs)
    (hres : mI ≠ rP →
      ConLeche.piResidual (cvj.type.instantiateLevelParams cvj.levelParams usj)
        major.getAppArgs = some residual)
    (hidx : mI ≠ rP →
      DefEqListSem m φ d (residual.getAppArgs.drop rl.ctorParams)
        ((e.getAppArgs.take mI).drop rP)) :
    RedSem m φ d e
      (Expr.mkAppN (rl.rhs.instantiateLevelParams cv.levelParams us)
        (e.getAppArgs.take rP ++ major.getAppArgs.drop rl.ctorParams)) := by
  sorry

set_option linter.unusedVariables false in
/-- The K rescue (`majorToCtorFueled_step`'s K arm, `Steps/Major.lean:383`,
with `majorToCtorFueled_reads`, `:178`): the fabrication reads and is
graded by the certified constructor telescope (`certs_telePA`), and
proof irrelevance equates it to the major.

Several of the rule's premises are consumed by the BRIDGE and not by
the semantics: the recursor's storage, the K flag, the constructor's
result family (`hres`/`hind`), the parameter count and the two
type-check certificates `htf`/`hdt` are what makes the checker take
this branch and build `proofIrrel`'s argument; at the motive the whole
of that argument is the `DefEq fab major` premise.  Hence the linter
option. -/
theorem Red.rescueK_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tf : Expr} {recName : Name} {cv : ConstantVal}
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
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs.take cnP))
    (htf : InferSemIO m φ d fab tf) (hdt : DefEqSem m φ d tmaj tf)
    (hpi : DefEqSem m φ d fab major) :
    RedSem m φ d major fab := by
  intro hfM Δa ea hCM hea hgM
  -- the fabrication's frame comes with the rule's three scope guards
  have hsub : LeavesSub fab major := fun l hl => by
    have := List.all_eq_true.mp hlv' l hl
    simpa using this
  have hfF : Frame d fab :=
    ⟨Expr.WScoped.of_wscopedB hws, hb, fun l hl => hfM.2.2 l (hsub l hl)⟩
  have hCF : CtxOk m φ d Δa fab := hCM.of_subset hsub
  -- the major's io-inferred type, reduced, is the family at its spine
  obtain ⟨hfT0, hsubT0, tm0a, htm0a, hgT0, hmemM0⟩ := htm hfM hCM hea hgM
  obtain ⟨hfTm, hsubTm, tmaja, htmaja, hgTm, heqTm⟩ :=
    htmaj hfT0 (hCM.of_subset hsubT0) htm0a hgT0
  have hCTm : CtxOk m φ d Δa tmaj :=
    (hCM.of_subset hsubT0).of_subset hsubTm
  rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp tmaj).symm, hthead] at htmaja
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := readSpine_mkAppN_inv htmaja
  have hfrT := frame_spineK hfTm hCTm
  obtain ⟨-, hoTs⟩ := hoist_spineK tsa hgTm
  -- the constructor's stored type: read, graded, inhabited, closed
  obtain ⟨TVja, hTVjaD, hokTVja, hmemCj, hnfJ, hbdJ⟩ :=
    constTy_pkg hin.const_ty hctor rfl (show ust.length = _ from hlv.symm)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVjaD hmemCj hnfJ hbdJ
  obtain ⟨hfJ, hCJ⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfJ hbdJ hCM.1
  -- the fabrication reads
  have hheadCj : denoteMeta m.acval env φ d (.const rl.ctor ust)
      = some (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) :=
    denoteMeta_const hctor (show ust.length = _ from hlv.symm)
  have hdF : denoteMeta m.acval env φ d fab
      = some (AnnotTerm.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) (tsa.take cnP)) := by
    rw [hfab]; exact readSpine_mkAppN (hspt.take cnP) hheadCj
  -- and is graded: its own telescope certificate is the fit
  obtain ⟨resta, hfit, -⟩ :=
    hcerts (fa := m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
      hfJ hCJ (hTVjaD d) (fun ρ _ => hokTVja ρ)
      (fun x hx => hfrT x (List.mem_of_mem_take hx)) (hspt.take cnP)
      (fun x hx => hoTs x (List.mem_of_mem_take hx)) (by simp)
  have hgF : Graded V Δa (AnnotTerm.mkAppN
      (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) (tsa.take cnP)) :=
    fun ρ hρ => (fitA_grades (tsa.take cnP) (hokTVja ρ)
      ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩
      (fun x hx => hoTs x (List.mem_of_mem_take hx) ρ hρ) (hmemCj ρ)
      (hfit ρ hρ)).1
  -- proof irrelevance identifies the fabrication with the major
  exact ⟨hfF, hsub, _, hdF, hgF,
    fun ρ hρ => (hpi hfF hfM hCF hCM hdF hea hgF hgM ρ hρ).symm⟩

/-- The structure-η rescue (`majorToCtorFueled_step`'s η arm). -/
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
    (hthead : tmaj.getAppFn = .const T ust)
    (hlen : tmaj.getAppArgs.length = caps.etaParams)
    (hlv : ust.length = cvT.levelParams.length)
    (hnz : ConLeche.capsNeverZero cvT.levelParams ust caps = true)
    (hfab : fab = Expr.mkAppN (.const caps.etaCtor ust)
      (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
    (hpi : DefEqSem m φ d fab major) :
    RedSem m φ d major fab := by
  sorry

set_option linter.unusedVariables false in
/-- The `And` rescue (`majorToCtorFueled_step`'s `And` arm): the
fabricated spine is the reduced type's parameters plus the major's two
`.proj` nodes, which read to the tower readings and are graded by the
two stored entries' typing law (`TowerOk`); the `DefEq fab major`
premise carries the proof-irrelevance identification. -/
theorem Red.rescueAnd_sound (hin : RulesInputs V m φ) {d : Nat}
    {major tm tmaj fab tf : Expr} {recName : Name} {cv : ConstantVal}
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
    (hslots : ConLeche.andRescueSlots env rl.ctor cnP ust = true)
    (hfab : fab = Expr.mkAppN (.const rl.ctor ust)
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]))
    (hws : fab.wscopedB d = true) (hb : fab.looseBVarsBounded 0 = true)
    (hlv' : fab.fvarLeaves.all (fun l => major.fvarLeaves.contains l) = true)
    (hcerts : CertsSem m φ d false
      (cvj.type.instantiateLevelParams cvj.levelParams ust)
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major]))
    (htf : InferSemIO m φ d fab tf) (hdt : DefEqSem m φ d tmaj tf)
    (hpi : DefEqSem m φ d fab major) :
    RedSem m φ d major fab := by
  intro hfM Δa ea hCM hea hgM
  have hsub : LeavesSub fab major := fun l hl => by
    have := List.all_eq_true.mp hlv' l hl
    simpa using this
  have hfF : Frame d fab :=
    ⟨Expr.WScoped.of_wscopedB hws, hb, fun l hl => hfM.2.2 l (hsub l hl)⟩
  have hCF : CtxOk m φ d Δa fab := hCM.of_subset hsub
  -- the major's io-inferred type, reduced, is `And` at its parameters
  obtain ⟨hfT0, hsubT0, tm0a, htm0a, hgT0, hmemM0⟩ := htm hfM hCM hea hgM
  obtain ⟨hfTm, hsubTm, tmaja, htmaja, hgTm, heqTm⟩ :=
    htmaj hfT0 (hCM.of_subset hsubT0) htm0a hgT0
  have hCTm : CtxOk m φ d Δa tmaj :=
    (hCM.of_subset hsubT0).of_subset hsubTm
  have hmemMW : ∀ ρ : Nat → V, Sat V Δa ρ →
      interp V ρ ea ∈ˢ interp V ρ tmaja :=
    fun ρ hρ => (heqTm ρ hρ) ▸ hmemM0 ρ hρ
  rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
    (ConLeche.Expr.mkAppN_getApp tmaj).symm, hthead] at htmaja
  obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := readSpine_mkAppN_inv htmaja
  have hfrT := frame_spineK hfTm hCTm
  obtain ⟨-, hoTs⟩ := hoist_spineK tsa hgTm
  -- the constructor's stored type: read, graded, inhabited, closed
  obtain ⟨TVja, hTVjaD, hokTVja, hmemCj, hnfJ, hbdJ⟩ :=
    constTy_pkg hin.const_ty hctor rfl (show ust.length = _ from hlv.symm)
  dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVjaD hmemCj hnfJ hbdJ
  obtain ⟨hfJ, hCJ⟩ := frame_of_not_hasFvar (m := m) (Δa := Δa) hnfJ hbdJ hCM.1
  -- the two pinned slots are stored tower entries; their head data
  -- carries the former's level parameters (`TowerEntryLaw`)
  have hslot := ConLeche.andRescueSlots_inv hslots
  obtain ⟨entry0, hfe0, hctor0, hnP0, -, -⟩ := hslot 0 (by decide)
  obtain ⟨-, -, -, ⟨cvT0, capsT0, hfT0s, hlpsT0, -⟩, -, cvC0, hfC0, hlpsC0, -, -⟩ :=
    hin.tower_ok andName 0 entry0 hfe0
  have hcvT0 : cvT0 = cvT := by
    rw [hind] at hfT0s
    exact (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj hfT0s)).1.symm
  have hcvC0 : cvC0 = cvj := by
    rw [hctor0, hctor] at hfC0
    exact (ConLeche.ConstantInfo.ctorInfo.inj (Option.some.inj hfC0)).1.symm
  have hlenus2 : ust.length = cvT.levelParams.length := by
    rw [← hcvT0, hlpsT0, ← hlpsC0, hcvC0]; exact hlv.symm
  have hvT' : vT = m.acval andName (Level.substFn φ cvT.levelParams ust) := by
    rw [denoteMeta_const hind (show ust.length
      = (ConLeche.ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
      from hlenus2)] at hvT
    exact (Option.some.inj hvT).symm
  -- each projection: read to the tower reading, graded by the law
  have hproj : ∀ j, j < 2 →
      denoteMeta m.acval env φ d (Expr.proj andName j major)
          = some (projAV (j + env.projOff andName) ea) ∧
        Graded V Δa (projAV (j + env.projOff andName) ea) := by
    intro j hj
    obtain ⟨entry, hfe, -, hnP, -, hfire⟩ := hslot j hj
    rw [← ConLeche.Env.findProj?_off hfe]
    refine ⟨denoteMeta_proj_towerK hfe hea, ?_⟩
    intro ρ hρ
    obtain ⟨-, -, -, ⟨cvTj, capsTj, hfTj, hlpsTj, -⟩, hO5j, cvCj, hfCj, hlpsCj,
      hlawj, -⟩ := hin.tower_ok andName j entry hfe
    have hcvTj : cvTj = cvT := by
      rw [hind] at hfTj
      exact (ConLeche.ConstantInfo.indInfo.inj (Option.some.inj hfTj)).1.symm
    have hlpe : entry.levelParams = cvT.levelParams := by rw [← hlpsTj, hcvTj]
    have hgj : TowerGuardAt φ entry ust := towerGuardAt_of_fireOk hO5j hfire
    obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlawj ust (by rw [hlpe]; exact hlenus2)
    have hTad := towerEntry_tele_at_depthK hfe hTa
    have hlenVs : tsa.length = entry.numParams := by
      rw [← hspt.length, hlen, hnP]
    have hpc : PiChainK (tsa ++ [ea]).length Ta := by
      rw [List.length_append, List.length_singleton, hlenVs]
      exact piChainK_of_stripPis _
        (by rw [ConLeche.projTele_stripPis]; rfl) (hTad d)
    obtain ⟨restj, hpeel⟩ := peelPisK_of_piChain _ hpc
    rw [hlpe, ← hvT'] at hA
    exact (hA hgj ρ tsa ea restj hlenVs (hgTm ρ hρ) (hgM ρ hρ)
      (hmemMW ρ hρ) hpeel).1
  -- the fabrication reads and is graded
  have hheadCj : denoteMeta m.acval env φ d (.const rl.ctor ust)
      = some (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) :=
    denoteMeta_const hctor (show ust.length = _ from hlv.symm)
  have hspF : ReadSpine m.acval env φ d
      (tmaj.getAppArgs ++ [.proj andName 0 major, .proj andName 1 major])
      (tsa ++ [projAV (0 + env.projOff andName) ea,
        projAV (1 + env.projOff andName) ea]) :=
    hspt.append (ReadSpine.cons (hproj 0 (by decide)).1
      (ReadSpine.cons (hproj 1 (by decide)).1 ReadSpine.nil))
  have hprFr : ∀ j, Frame d (Expr.proj andName j major) ∧
      CtxOk m φ d Δa (Expr.proj andName j major) := fun j =>
    ⟨⟨by simpa [Expr.WScoped] using hfM.1,
        by simpa [Expr.looseBVarsBounded] using hfM.2.1,
        fun l hl => hfM.2.2 l (by simpa [Expr.fvarLeaves] using hl)⟩,
      hCM.of_subset (fun l hl => by simpa [Expr.fvarLeaves] using hl)⟩
  have hfrF : ∀ x ∈ tmaj.getAppArgs ++
      [Expr.proj andName 0 major, Expr.proj andName 1 major],
      Frame d x ∧ CtxOk m φ d Δa x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hfrT x hx'
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · exact hprFr 0
      · rcases List.mem_singleton.mp hx'' with rfl
        exact hprFr 1
  have hoksF : ∀ x ∈ (tsa ++ [projAV (0 + env.projOff andName) ea,
      projAV (1 + env.projOff andName) ea]), Graded V Δa x := by
    intro x hx
    rcases List.mem_append.mp hx with hx' | hx'
    · exact hoTs x hx'
    · rcases List.mem_cons.mp hx' with rfl | hx''
      · exact (hproj 0 (by decide)).2
      · rcases List.mem_singleton.mp hx'' with rfl
        exact (hproj 1 (by decide)).2
  have hdF : denoteMeta m.acval env φ d fab
      = some (AnnotTerm.mkAppN
        (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
        (tsa ++ [projAV (0 + env.projOff andName) ea,
          projAV (1 + env.projOff andName) ea])) := by
    rw [hfab]; exact readSpine_mkAppN hspF hheadCj
  obtain ⟨resta, hfit, -⟩ :=
    hcerts (fa := m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
      hfJ hCJ (hTVjaD d) (fun ρ _ => hokTVja ρ) hfrF hspF hoksF (by simp)
  have hgF : Graded V Δa (AnnotTerm.mkAppN
      (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
      (tsa ++ [projAV (0 + env.projOff andName) ea,
        projAV (1 + env.projOff andName) ea])) :=
    fun ρ hρ => (fitA_grades _ (hokTVja ρ)
      ⟨m.acval_wellDenoted _ _ ρ, hin.leaf_valid _ _ ρ⟩
      (fun x hx => hoksF x hx ρ hρ) (hmemCj ρ) (hfit ρ hρ)).1
  exact ⟨hfF, hsub, _, hdF, hgF,
    fun ρ hρ => (hpi hfF hfM hCF hCM hdF hea hgF hgM ρ hρ).symm⟩

end ConLeche.Model.Rules
