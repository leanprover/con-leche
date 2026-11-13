module

public import InLeanProof.DeclGuards
public import InLeanProof.IndMembers
/- `DefinitionSafety`'s `BEq` is not exposed by `Lean.Declaration`; the safety gates read it. -/
import all Lean.Declaration

/-!
# O6: the declaration step for the non-inductive kinds (task #451, lane O6)

InLean's declaration check (`InLean/CheckerC.lean`, `InLean/AddDecl.lean`'s
`checkDeclKindC`/`checkDecl`) at the theorem's configuration against master's
pure declaration step (`ConLeche.checkDecl .verified (fueledOps .verified F)`,
`ConLeche/Kernel/CheckDecl.lean`) on the records `toDecl` reads off what it
adds: the shape P4 folds with master's `foldPM`, next to the preservation
lemmas (`presI_*`, `quotGroupPres`).  The core calls are the knot's specs
(`JobEnvI.ops`, from `ssimI_of_pres`); the proofs are functional
(`bindI_ok`, master's `Runs`), as O7's.

* `checkConstantValC_sim` (every kind's constant check) and its job twin
  `checkConstantValCSimI` (O7's named callee, discharged): the guards by the
  translation (`DeclGuards.lean`), master's resolution guard from the
  inference InLean ran (`constsResolve_of_infer`).
* `checkValueC_sim` with `checkDefnVal_runs`/`checkOpaqueVal_runs`, and
  `checkThmC_sim` (master's `checkThmVal`, the proposition test through
  `isEquiv_zero_tr`).
* The arms: `checkDefnC_sim` off the certified `Nat` operations' names,
  `checkOpaqueC_sim` off the compiler-trust names, `checkAxiomC_sorry_sim`,
  `checkAxiomC_quotSound_sim` (master's `checkQuotRecord .sound`),
  `checkQuotC_sim` (the four records' fold, `quotFold_ok`); a mutual block is
  never a `SafeDecl`.
* `checkDeclKindC_sim` on the arms proved (`ProvedArm`), and `checkDecl_sim`
  at the entry point: the fresh state's invariant (`CSOKI_empty`) and
  `sorryAxSquat`'s decline read as "no constant but an axiom at `sorryAx`".
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

variable {lim : InLean.Limits}

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

/-! ## The constant check -/

theorem bindI_ite_throw {β : Type} {c : Bool} {e : InLean.CheckError} {k : Unit → InLean.CheckCM β}
    {s₀ : InLean.CState} {v : β} {s' : InLean.CState}
    (h : ((if c = true then (throw e : InLean.CheckCM Unit) else pure ()) >>= k) s₀ = .ok (v, s')) :
    c = false ∧ k () s₀ = .ok (v, s') := by
  obtain ⟨u, s₁, h1, h2⟩ := bindI_ok h
  split at h1
  · exact (throwI_ok h1).elim
  · obtain ⟨-, rfl⟩ := pureI_ok h1
    exact ⟨by simpa using ‹¬c = true›, h2⟩

/-- The translated constant value. -/
@[expose] def trCVn (n : Name) (lps : List Name) (ty : Expr) : ConLeche.ConstantVal :=
  ⟨toName n, lps.map toName, trC ty⟩

theorem runs_atF {α : Type} {x : ConLeche.FueledM α} {a : α} (h : Runs x a) : ∃ F, x.val F = .ok a := h

/-- **The constant check** (`checkConstantValC`, `checkConstantValS_spec`'s
twin): accepted at `fe` against `L`, master's `checkConstantVal` runs on the
translated constant, at any `allowOp`. -/
theorem checkConstantValC_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {cv : Lean.ConstantVal} {a : Bool} {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hr : Expr.RangeOk cv.type)
    (h : InLean.checkConstantValC .verified fe cv a s₀ = .ok ((), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ okC cv.type = true ∧
      (trC cv.type).looseBVarsBounded 0 = true ∧
      Runs (ConLeche.checkConstantVal (ConLeche.fueledOpsM .verified) L
        (trCVn cv.name cv.levelParams cv.type) a) () := by
  unfold InLean.checkConstantValC at h
  split at h
  · exact (throw_bindI_ok h).elim
  rename_i h1
  try dsimp only at h
  split at h
  · exact (throw_bindI_ok h).elim
  rename_i h3
  try dsimp only at h
  split at h
  rotate_left
  · exact (throw_bindI_ok h).elim
  rename_i h4
  try dsimp only at h
  split at h
  rotate_left
  · exact (throw_bindI_ok h).elim
  rename_i h5
  try dsimp only at h
  obtain ⟨_, s₁, hW, h⟩ := bindI_ok h
  obtain ⟨hs1, hok, hlbb, hfv, hlp⟩ := checkTermWF_ok hr hW
  subst s₁
  try simp only [] at h
  obtain ⟨v, s₂, hI, h⟩ := bindI_ok h
  have hTr : TrS s₀ cv.type = trC cv.type := TrS_of_okC _ hok
  obtain ⟨hs₂, ht₂, hokv, hRI, hwv, hcv⟩ := tripleI_iff_run.1 (hJ.ops.infer (s₀ := s₀) (d := 0)
    (i := cv.type) hs (OkS_of_okC _ hok) (by rw [hTr]; exact trC_wscoped 0 _) (by rw [hTr]; exact hlbb))
    v s₂ hI
  obtain ⟨u, s₃, hS, h⟩ := bindI_ok h
  obtain ⟨hs₃, ht₃, -, hRS⟩ := tripleI_iff_run.1 (hJ.ops.sort (s₀ := s₂) (d := 0) (i := v) hs₂ hokv
    hwv hcv) u s₃ hS
  obtain ⟨-, rfl⟩ := pureI_ok h
  refine ⟨hs₃, ht₂.trans ht₃, hok, hlbb, ?_⟩
  rw [hTr] at hRI
  -- master's guards, read off InLean's
  have g1 : (L.find? (toName cv.name)).isSome = false := by
    rw [hJ.pres.none cv.name (FEnv_find_none (by simpa using h1))]; rfl
  have g3 : (ConLeche.natOpName (toName cv.name) && !a) = false := by
    rw [natOpName_tr]; simpa using h3
  have g4 := litShapeOk_tr hok h4
  have g5 : ConLeche.Name.nodup (cv.levelParams.map toName) = true := by rw [nodup_tr]; exact h5
  obtain ⟨F, hF⟩ := runs_atF hRI
  have g6 : (trC cv.type).constsResolve L = true := constsResolve_of_infer hfv hF
  unfold ConLeche.checkConstantVal
  simp only [trCVn, g1, g3, g4, g5, hlbb, hfv, hlp, g6, Bool.false_eq_true, ↓reduceIte]
  exact Runs.bind hRI (Runs.bind hRS (Runs.pure _))

/-- **The stages' constant check, discharged** (`CheckConstantValCSimI`):
`checkConstantValC_sim` at `allowOp := false`. -/
theorem checkConstantValCSimI : CheckConstantValCSimI := by
  intro fe L cv s₀ s' hJ hs hok h
  obtain ⟨h1, h2, -, h4, h5⟩ := checkConstantValC_sim (a := false) hJ hs (RangeOk_of_okE hok) h
  exact ⟨h1, h2, h4, h5⟩

/-! ## The value check -/

/-- **Master's value guards and checks hold of a translated value**: closed,
no free variable, its level parameters declared, resolving, and its inferred
type definitionally equal to the declared one. -/
@[expose] def ValRuns (L : ConLeche.Env) (cv : ConLeche.ConstantVal) (value : ConLeche.Expr) : Prop :=
  value.looseBVarsBounded 0 = true ∧ value.hasFvar = false ∧
    value.allLevelParamsDefined cv.levelParams = true ∧ value.constsResolve L = true ∧
    ∃ vt, Runs ((ConLeche.fueledOpsM .verified).inferType L 0 value) vt ∧
      Runs ((ConLeche.fueledOpsM .verified).isDefEq L 0 vt cv.type) true

/-- **The value check** (`checkValueC`, the value half of master's
`checkDefnVal`/`checkThmVal`/`checkOpaqueVal`). -/
theorem checkValueC_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {kind : String} {n : Name} {lps : List Name} {ty v : Expr} {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hr : Expr.RangeOk v) (hokT : okC ty = true)
    (hlbbT : (trC ty).looseBVarsBounded 0 = true)
    (h : InLean.checkValueC .verified fe kind n lps ty v s₀ = .ok ((), s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ okC v = true ∧
      ValRuns L (trCVn n lps ty) (trC v) := by
  unfold InLean.checkValueC at h
  obtain ⟨_, s₁, hW, h⟩ := bindI_ok h
  obtain ⟨hs1, hok, hlbb, hfv, hlp⟩ := checkTermWF_ok hr hW
  subst s₁
  try simp only [] at h
  obtain ⟨vt, s₂, hI, h⟩ := bindI_ok h
  have hTr : TrS s₀ v = trC v := TrS_of_okC _ hok
  obtain ⟨hs₂, ht₂, hokv, hRI, hwv, hcv⟩ := tripleI_iff_run.1 (hJ.ops.infer (s₀ := s₀) (d := 0)
    (i := v) hs (OkS_of_okC _ hok) (by rw [hTr]; exact trC_wscoped 0 _) (by rw [hTr]; exact hlbb))
    vt s₂ hI
  obtain ⟨b, s₃, hD, h⟩ := bindI_ok h
  have hTrT : TrS s₂ ty = trC ty := TrS_of_okC _ hokT
  obtain ⟨hs₃, ht₃, hRD⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₂) (d := 0) (i := vt) (j := ty)
    hs₂ hokv (OkS_of_okC _ hokT) hwv (by rw [hTrT]; exact trC_wscoped 0 _) hcv
    (by rw [hTrT]; exact hlbbT)) b s₃ hD
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact (throwI_ok h).elim
  simp only [↓reduceIte] at h
  obtain ⟨-, rfl⟩ := pureI_ok h
  obtain ⟨F, hF⟩ := runs_atF hRI
  rw [hTr] at hRI hF
  rw [hTrT] at hRD
  exact ⟨hs₃, ht₂.trans ht₃, hok, hlbb, hfv, hlp, constsResolve_of_infer hfv hF, _, hRI, hRD⟩

/-- Master's `checkDefnVal` from the value's runs. -/
theorem checkDefnVal_runs {L : ConLeche.Env} {cv : ConLeche.ConstantVal} {value : ConLeche.Expr}
    {hint : ConLeche.ReducibilityHint} (h : ValRuns L cv value) :
    Runs (ConLeche.checkDefnVal (ConLeche.fueledOpsM .verified) L cv value hint)
      ⟨.defnInfo cv value hint :: L.consts, L.tables⟩ := by
  obtain ⟨h1, h2, h3, h4, vt, hI, hD⟩ := h
  unfold ConLeche.checkDefnVal
  simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
  exact Runs.bind hI (Runs.bind hD (by simp only [↓reduceIte]; exact Runs.pure _))

/-- Master's `checkOpaqueVal` from the value's runs. -/
theorem checkOpaqueVal_runs {L : ConLeche.Env} {cv : ConLeche.ConstantVal} {value : ConLeche.Expr}
    (h : ValRuns L cv value) :
    Runs (ConLeche.checkOpaqueVal (ConLeche.fueledOpsM .verified) L cv value)
      ⟨.axiomInfo cv :: L.consts, L.tables⟩ := by
  obtain ⟨h1, h2, h3, h4, vt, hI, hD⟩ := h
  unfold ConLeche.checkOpaqueVal
  simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
  exact Runs.bind hI (Runs.bind hD (by simp only [↓reduceIte]; exact Runs.pure _))

/-! ## The records -/

theorem toCV_of_okC {v : Lean.ConstantVal} (h : okC v.type = true) :
    toCV v = some (trCVn v.name v.levelParams v.type) := by
  simp [toCV, toExprC_of_okC h, trCVn]

/-- Master's pure declaration kind check (`checkDeclKind`, the step without
the reserved names' check) at the fueled family accepts `d` at `L`. -/
@[expose] def KindRuns (pins : List ConLeche.NatOpPinSet) (L : ConLeche.Env) (d : ConLeche.Declaration) :
    Prop :=
  ∃ L', Runs (ConLeche.checkDeclKind (ConLeche.fueledOpsM .verified) pins L d) L'

theorem KindRuns.fueled {pins : List ConLeche.NatOpPinSet} {L : ConLeche.Env} {d : ConLeche.Declaration}
    (h : KindRuns pins L d) :
    ∃ F L', ConLeche.checkDeclKind (ConLeche.fueledOps .verified F) pins L d = .ok L' := by
  obtain ⟨L', F, hF⟩ := h
  exact ⟨F, L', by rw [← ConLeche.checkDeclKind_datF]; exact hF⟩

/-! ## A theorem -/

theorem liftFueledI_ok {α : Type} {what : String} {o : Option α} {s₀ s' : InLean.CState} {a : α}
    (h : (InLean.liftFueled what o : InLean.CheckCM α) s₀ = .ok (a, s')) : o = some a ∧ s' = s₀ := by
  cases o with
  | none => exact (throwI_ok h).elim
  | some b => obtain ⟨rfl, rfl⟩ := pureI_ok h; exact ⟨rfl, rfl⟩

/-- **A theorem** (`checkThmC`, master's `.thmDecl` arm: `checkThmVal`). -/
theorem checkThmC_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {pins : List ConLeche.NatOpPinSet} {v : TheoremVal} {a : InLean.Added} {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hr : Expr.RangeOk v.type) (hrv : Expr.RangeOk v.value)
    (h : InLean.checkThmC .verified fe v s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ a.consts = #[.thmInfo v] ∧ a.quot = false ∧
      ∃ d, toDecl [.thmInfo v] = some d ∧ KindRuns pins L d := by
  unfold InLean.checkThmC at h
  obtain ⟨_, s₁, hC, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hok, hlbb, hRC⟩ := checkConstantValC_sim hJ hs hr hC
  obtain ⟨t, s₂, hI, h⟩ := bindI_ok h
  have hTr : TrS s₁ v.type = trC v.type := TrS_of_okC _ hok
  obtain ⟨hs₂, ht₂, hokt, hRI, hwt, hct⟩ := tripleI_iff_run.1 (hJ.ops.infer (s₀ := s₁) (d := 0)
    (i := v.type) hs₁ (OkS_of_okC _ hok) (by rw [hTr]; exact trC_wscoped 0 _)
    (by rw [hTr]; exact hlbb)) t s₂ hI
  obtain ⟨u, s₃, hS, h⟩ := bindI_ok h
  obtain ⟨hs₃, ht₃, hoku, hRS⟩ := tripleI_iff_run.1 (hJ.ops.sort (s₀ := s₂) (d := 0) (i := t) hs₂
    hokt hwt hct) u s₃ hS
  obtain ⟨b, s₄, hL, h⟩ := bindI_ok h
  obtain ⟨hb, rfl⟩ := liftFueledI_ok hL
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact (throw_bindI_ok h).elim
  simp only [↓reduceIte] at h
  try simp only [] at h
  obtain ⟨_, s₅, hV, h⟩ := bindI_ok h
  obtain ⟨hs₅, ht₅, hokv, hVR⟩ := checkValueC_sim hJ hs₃ hrv hok hlbb hV
  obtain ⟨rfl, rfl⟩ := pureI_ok h
  refine ⟨hs₅, ht₁.trans (ht₂.trans (ht₃.trans ht₅)), rfl, rfl,
    .thmDecl (trCVn v.name v.levelParams v.type) (trC v.value),
    by simp [toDecl, toCV_of_okC (v := v.toConstantVal) hok, toExprC_of_okC hokv], ?_⟩
  rw [hTr] at hRI
  have hiso : ConLeche.Level.isEquiv (trL u) .zero = some true := by
    rw [isEquiv_zero_tr (okL_of_okLv_level hoku)]; exact hb
  obtain ⟨g1, g2, g3, g4, vt, hVI, hVD⟩ := hVR
  refine ⟨⟨.thmInfo (trCVn v.name v.levelParams v.type) :: L.consts, L.tables⟩, Runs.bind hRC ?_⟩
  unfold ConLeche.checkThmVal
  refine Runs.bind hRI (Runs.bind hRS ?_)
  simp only [hiso, ConLeche.liftFueled]
  refine Runs.bind (Runs.pure true) ?_
  simp only [↓reduceIte, g1, g2, g3, g4, Bool.false_eq_true]
  exact Runs.bind hVI (Runs.bind hVD (by simp only [↓reduceIte]; exact Runs.pure _))

/-! ## A definition and an opaque, off the certified names -/

theorem natOpNames_tr (n : Name) :
    ConLeche.natOpNames.contains (toName n) = InLean.natOpNames.contains n := by
  rw [show ConLeche.natOpNames = InLean.natOpNames.map toName from rfl, contains_map_toName]

theorem natDivModNames_tr (n : Name) :
    ConLeche.natDivModNames.contains (toName n) = InLean.natDivModNames.contains n := by
  rw [show ConLeche.natDivModNames = InLean.natDivModNames.map toName from rfl, contains_map_toName]

theorem reduceOpNames_tr (n : Name) :
    ConLeche.reduceOpNames.contains (toName n) = InLean.reduceOpNames.contains n := by
  rw [show ConLeche.reduceOpNames = InLean.reduceOpNames.map toName from rfl, contains_map_toName]

/-- **A safe definition off the certified `Nat` operations' names**
(`checkDefnC`, master's `.defnDecl` arm). -/
theorem checkDefnC_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {pins : List ConLeche.NatOpPinSet} {cfg : InLean.Config} {v : DefinitionVal} {a : InLean.Added}
    {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hr : Expr.RangeOk v.type) (hrv : Expr.RangeOk v.value)
    (hsafe : v.safety = .safe)
    (hnc : (InLean.natOpNames.contains v.name || InLean.natDivModNames.contains v.name) = false)
    (h : InLean.checkDefnC .verified cfg fe v s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ a.consts = #[.defnInfo v] ∧ a.quot = false ∧
      ∃ d, toDecl [.defnInfo v] = some d ∧ KindRuns pins L d := by
  unfold InLean.checkDefnC at h
  simp only [hsafe, show (DefinitionSafety.safe == DefinitionSafety.unsafe) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, hnc] at h
  obtain ⟨_, s₁, hC, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hok, hlbb, hRC⟩ := checkConstantValC_sim hJ hs hr hC
  obtain ⟨_, s₂, hV, h⟩ := bindI_ok h
  obtain ⟨hs₂, ht₂, hokv, hVR⟩ := checkValueC_sim hJ hs₁ hrv hok hlbb hV
  obtain ⟨rfl, rfl⟩ := pureI_ok h
  simp only [Bool.or_eq_false_iff] at hnc
  refine ⟨hs₂, ht₁.trans ht₂, rfl, rfl,
    .defnDecl (trCVn v.name v.levelParams v.type) (trC v.value) (toHint v.hints),
    by simp [toDecl, toCV_of_okC (v := v.toConstantVal) hok, toExprC_of_okC hokv],
    ⟨.defnInfo (trCVn v.name v.levelParams v.type) (trC v.value) (toHint v.hints) :: L.consts,
      L.tables⟩, Runs.bind hRC (Runs.bind (checkDefnVal_runs hVR) ?_)⟩
  simp only [trCVn, natOpNames_tr, natDivModNames_tr, hnc.1, hnc.2, Bool.false_eq_true, ↓reduceIte]
  exact Runs.pure _

/-- **A safe opaque off the compiler-trust names** (`checkOpaqueC`, master's
`.opaqueDecl` arm: stored as an axiom). -/
theorem checkOpaqueC_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {pins : List ConLeche.NatOpPinSet} {v : OpaqueVal} {a : InLean.Added} {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hr : Expr.RangeOk v.type) (hrv : Expr.RangeOk v.value)
    (hnc : InLean.reduceOpNames.contains v.name = false)
    (h : InLean.checkOpaqueC .verified fe v s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ a.consts = #[.opaqueInfo v] ∧ a.quot = false ∧
      ∃ d, toDecl [.opaqueInfo v] = some d ∧ KindRuns pins L d := by
  unfold InLean.checkOpaqueC at h
  obtain ⟨_, s₁, hC, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hok, hlbb, hRC⟩ := checkConstantValC_sim hJ hs hr hC
  obtain ⟨_, s₂, hV, h⟩ := bindI_ok h
  obtain ⟨hs₂, ht₂, hokv, hVR⟩ := checkValueC_sim hJ hs₁ hrv hok hlbb hV
  simp only [hnc, Bool.false_eq_true, ↓reduceIte] at h
  obtain ⟨rfl, rfl⟩ := pureI_ok h
  refine ⟨hs₂, ht₁.trans ht₂, rfl, rfl,
    .opaqueDecl (trCVn v.name v.levelParams v.type) (trC v.value),
    by simp [toDecl, toCV_of_okC (v := v.toConstantVal) hok, toExprC_of_okC hokv],
    ⟨.axiomInfo (trCVn v.name v.levelParams v.type) :: L.consts, L.tables⟩,
    Runs.bind hRC (Runs.bind (checkOpaqueVal_runs hVR) ?_)⟩
  simp only [trCVn, reduceOpNames_tr, hnc, Bool.false_eq_true, ↓reduceIte]
  exact Runs.pure _

/-! ## `sorryAx` and `Quot.sound` -/

theorem cl_axNames :
    toName InLean.sorryAxName = ConLeche.sorryAxName ∧
    toName InLean.quotSoundName = ConLeche.quotSoundName ∧
    toName InLean.propextName = ConLeche.propextName ∧
    toName InLean.choiceName = ConLeche.choiceName ∧
    toName InLean.trustCompilerName = ConLeche.trustCompilerName ∧
    toName InLean.ofReduceNatName = ConLeche.ofReduceNatName ∧
    toName InLean.ofReduceBoolName = ConLeche.ofReduceBoolName ∧
    toName InLean.eqName = ConLeche.eqName ∧ toName InLean.quotName = ConLeche.quotName ∧
    toName InLean.quotMkName = ConLeche.quotMkName :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem find_isSome_of_pres {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Name}
    (h : (fe.find? n).isSome = true) : (L.find? (toName n)).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 h
  obtain ⟨cci, hc, -⟩ := hP.entry n ci hci
  rw [hc]; rfl

/-- **`Quot.sound`** (`checkAxiomC`'s first arm, master's `checkQuotRecord .sound`):
the pin hit at the axiom's level name, what it needs stored, the name fresh. -/
theorem checkAxiomC_quotSound_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    {pins : List ConLeche.NatOpPinSet} {cfg : InLean.Config} {v : AxiomVal} {a : InLean.Added}
    {s₀ s' : InLean.CState} (hr : Expr.RangeOk v.type) (hn : v.name = InLean.quotSoundName)
    (h : InLean.checkAxiomC .verified cfg fe v s₀ = .ok (a, s')) :
    s' = s₀ ∧ a.consts = #[.axiomInfo v] ∧ a.quot = false ∧
      ∃ d, toDecl [.axiomInfo v] = some d ∧ KindRuns pins L d := by
  obtain ⟨c1, c2, -, -, -, -, -, c8, c9, c10⟩ := cl_axNames
  unfold InLean.checkAxiomC at h
  simp only [hn, beq_self_eq_true, ↓reduceIte] at h
  split at h
  rotate_left
  · exact (throw_bindI_ok h).elim
  rename_i hhit
  try simp only [] at h
  split at h
  rotate_left
  · exact (throw_bindI_ok h).elim
  rename_i hpre
  try simp only [] at h
  split at h
  · exact (throw_bindI_ok h).elim
  rename_i hfr
  obtain ⟨rfl, rfl⟩ := pureI_ok h
  -- the hit, read as master's
  unfold quotSoundHit at hhit
  simp only [Bool.and_eq_true, beq_iff_eq] at hhit
  obtain ⟨⟨-, hlen⟩, hcl⟩ := hhit
  obtain ⟨lp, hlp⟩ : ∃ lp, v.levelParams = [lp] := by
    match hv : v.levelParams, hlen with
    | [lp], _ => exact ⟨lp, rfl⟩
  rw [hlp] at hcl
  have hst := storedT_instantiateLevelParams quotSoundPin.lps (R := quotSoundPin.type)
    (us := [.param lp]) (by decide) (by decide) (by decide) rfl rfl
    (by simp [depthS]) (by simp only [maxDepthS, List.foldr, depthS]; decide)
  have hty : toExprC v.type = toExprC (EO.instantiateLevelParams quotSoundPin.type quotSoundPin.lps
      [.param lp]) := toExpr_of_clEq _ hcl
  rw [hst.2.2] at hty
  have hok : okC v.type = true := (trC_of_toExprC hty hr).1
  have hT : trC v.type =
      (ConLeche.quotSoundA.toConstantVal.atLps [toName lp]).type := by
    rw [(trC_of_toExprC hty hr).2]; rfl
  simp only [Bool.and_eq_true] at hpre
  obtain ⟨⟨hEq, hQ⟩, hM⟩ := hpre
  refine ⟨rfl, rfl, rfl, .axiomDecl (trCVn v.name v.levelParams v.type),
    by simp [toDecl, toCV_of_okC (v := v.toConstantVal) hok], ?_⟩
  have hname : toName v.name = ConLeche.quotSoundName := by rw [hn, c2]
  have hcv : (⟨ConLeche.quotSoundName, [toName lp], trC v.type⟩ : ConLeche.ConstantVal) =
      (ConLeche.quotPin .sound).toConstantVal.atLps [toName lp] := by rw [hT]; rfl
  have g1 : ConLeche.quotPinHit .sound (trCVn v.name v.levelParams v.type) = true := by
    simp only [ConLeche.quotPinHit, trCVn, hlp, hname, List.map_cons, List.map_nil]
    rw [hcv]
    simp [ConLeche.Name.nodup, ConLeche.ConstantVal.beqP]
    rfl
  have g2 : ConLeche.quotPredsOk L.find? .sound = true := by
    have e1 := find_isSome_of_pres hP hEq
    have e2 := find_isSome_of_pres hP hQ
    have e3 := find_isSome_of_pres hP hM
    rw [c8] at e1; rw [c9] at e2; rw [c10] at e3
    simp [ConLeche.quotPredsOk, e1, e2, e3]
  have g3 : L.find? ConLeche.quotSoundName = none := by
    rw [← c2, ← hn]; exact hP.none _ (FEnv_find_none (by rw [hn]; simpa using hfr))
  refine ⟨⟨ConLeche.quotAt .sound (trCVn v.name v.levelParams v.type) :: L.consts, L.tables⟩, ?_⟩
  unfold ConLeche.checkDeclKind
  simp only [trCVn, hname, ↓reduceIte]
  unfold ConLeche.checkQuotRecord
  simp only [show ConLeche.quotPinHit .sound ⟨ConLeche.quotSoundName, v.levelParams.map toName,
    trC v.type⟩ = true from by rw [← hname]; exact g1, g2, ↓reduceIte]
  unfold ConLeche.installBasisDecl
  have g3' : (L.find? (ConLeche.quotAt .sound ⟨ConLeche.quotSoundName, v.levelParams.map toName,
      trC v.type⟩).name).isNone = true := by
    rw [show (ConLeche.quotAt .sound ⟨ConLeche.quotSoundName, v.levelParams.map toName,
      trC v.type⟩).name = ConLeche.quotSoundName from rfl, g3]; rfl
  simp only [g3', ↓reduceIte]
  exact Runs.pure _

theorem ne_of_toName {a b : Name} (h : toName a ≠ toName b) : a ≠ b := fun e => h (e ▸ rfl)

/-- **`sorryAx`** (`checkAxiomC` at con-leche's policy: checked as a constant,
installed as nothing). -/
theorem checkAxiomC_sorry_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {pins : List ConLeche.NatOpPinSet} {v : AxiomVal} {a : InLean.Added} {s₀ s' : InLean.CState}
    (hfs : fe.safety = .safe) (hfc : fe.coreAxioms = false)
    (hs : CSOKI .verified false L s₀) (hr : Expr.RangeOk v.type) (hsafe : v.isUnsafe = false)
    (hn : v.name = InLean.sorryAxName)
    (h : InLean.checkAxiomC .verified (InLeanProof.theoremConfig lim) fe v s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ a.consts = #[.axiomInfo v] ∧ a.quot = false ∧
      ∃ d, toDecl [.axiomInfo v] = some d ∧ KindRuns pins L d := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, -, -, -⟩ := cl_axNames
  have nq : InLean.sorryAxName ≠ InLean.quotSoundName := ne_of_toName (by rw [c1, c2]; decide)
  have np : InLean.sorryAxName ≠ InLean.propextName := ne_of_toName (by rw [c1, c3]; decide)
  have nc : InLean.sorryAxName ≠ InLean.choiceName := ne_of_toName (by rw [c1, c4]; decide)
  have nt : InLean.sorryAxName ≠ InLean.trustCompilerName := ne_of_toName (by rw [c1, c5]; decide)
  have no1 : InLean.sorryAxName ≠ InLean.ofReduceNatName := ne_of_toName (by rw [c1, c6]; decide)
  have no2 : InLean.sorryAxName ≠ InLean.ofReduceBoolName := ne_of_toName (by rw [c1, c7]; decide)
  have hfe : fe.withSafety .safe = fe := FEnv.withSafety_of_eq (by assumption)
  have bq : (InLean.sorryAxName == InLean.quotSoundName) = false := by simpa using nq
  have bp : (InLean.sorryAxName == InLean.propextName) = false := by simpa using np
  have bc : (InLean.sorryAxName == InLean.choiceName) = false := by simpa using nc
  have bt : (InLean.sorryAxName == InLean.trustCompilerName) = false := by simpa using nt
  have bo1 : (InLean.sorryAxName == InLean.ofReduceNatName) = false := by simpa using no1
  have bo2 : (InLean.sorryAxName == InLean.ofReduceBoolName) = false := by simpa using no2
  unfold InLean.checkAxiomC at h
  simp only [hn, bq, Bool.false_eq_true, ↓reduceIte, hsafe] at h
  rw [hfe, hfc] at h
  obtain ⟨_, s₁, hC, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hok, -, hRC⟩ := checkConstantValC_sim hJ hs hr hC
  have hstd : InLean.stdAxiomOk fe InLean.sorryAxName v.levelParams v.type = false := by
    simp [InLean.stdAxiomOk, bp, bc]
  simp only [hstd, bp, bc, bt, bo1, bo2, Bool.false_eq_true, ↓reduceIte, Bool.or_false,
    beq_self_eq_true, Bool.true_or] at h
  obtain ⟨rfl, rfl⟩ := pureI_ok h
  refine ⟨hs₁, ht₁, rfl, rfl, .axiomDecl (trCVn v.name v.levelParams v.type),
    by simp [toDecl, toCV_of_okC (v := v.toConstantVal) hok], L, ?_⟩
  have hname : toName v.name = ConLeche.sorryAxName := by rw [hn, c1]
  have hstdC : ConLeche.stdAxiomOk L (trCVn v.name v.levelParams v.type) = false := by
    simp only [ConLeche.stdAxiomOk, trCVn, hname]
    simp +decide
  unfold ConLeche.checkDeclKind
  simp only [trCVn, hname] at hRC hstdC ⊢
  simp +decide only [↓reduceIte]
  refine Runs.bind hRC ?_
  simp +decide only [hstdC, Bool.false_eq_true, ↓reduceIte]
  exact Runs.pure _

/-! ## The quotient package -/

/-- **What an accepted `checkQuotC` read**: the package declared already
(nothing added), or `Eq` stored and the four names fresh; no state change. -/
theorem checkQuotC_run {fe : FEnv} {s s' : InLean.CState} {a : Added}
    (h : InLean.checkQuotC fe s = .ok (a, s')) :
    (a = { quot := true } ∧ s' = s) ∨
    (InLean.quotPredsOk fe = true ∧
    fe.env.find? quotPin.name = none ∧ fe.env.find? quotMkPin.name = none ∧
    fe.env.find? quotLiftPin.name = none ∧ fe.env.find? quotIndPin.name = none ∧
    a = { consts := quotConstsI, quot := true } ∧ s' = s) := by
  simp only [checkQuotC] at h
  cases hi : quotInitialized fe.env
  rotate_left
  · simp [hi, pure, StateT.pure, Except.pure] at h
    exact .inl ⟨h.1.symm, h.2.symm⟩
  refine .inr ?_
  simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
  cases hq : quotPredsOk fe <;>
  cases h1 : fe.env.find? quotPin.name <;> cases h2 : fe.env.find? quotMkPin.name <;>
  cases h3 : fe.env.find? quotLiftPin.name <;> cases h4 : fe.env.find? quotIndPin.name <;>
  simp [hq, h1, h2, h3, h4, bind, StateT.bind, pure, StateT.pure, forIn,
    List.forIn'_cons, List.forIn'_nil, throw, throwThe, MonadExceptOf.throw, StateT.lift, Except.bind,
    Except.pure] at h
  exact ⟨rfl, rfl, rfl, rfl, rfl, h.1.symm, h.2.symm⟩

/-- The package's four records. -/
@[expose] def quotRecords : List ConLeche.Declaration :=
  [.quotDecl .type ConLeche.quotA.toConstantVal, .quotDecl .ctor ConLeche.quotMkA.toConstantVal,
   .quotDecl .lift ConLeche.quotLiftA.toConstantVal, .quotDecl .ind ConLeche.quotIndA.toConstantVal]

theorem quotRecords_eq : quotConstsI.toList.mapM (fun ci => toDecl [ci]) = some quotRecords := by
  decide

/-- **Master's fold over the package's records**, from `Eq` stored and the
four names fresh. -/
theorem quotFold_ok {pins : List ConLeche.NatOpPinSet} {F : Nat} {L : ConLeche.Env}
    (hEq : (L.find? ConLeche.eqName).isSome = true) (h1 : L.find? ConLeche.quotName = none)
    (h2 : L.find? ConLeche.quotMkName = none) (h3 : L.find? ConLeche.quotLiftName = none)
    (h4 : L.find? ConLeche.quotIndName = none) :
    ∃ L', quotRecords.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
      .ok L' := by
  have n1 : (ConLeche.quotAt .type ConLeche.quotA.toConstantVal).name = ConLeche.quotName := rfl
  have n2 : (ConLeche.quotAt .ctor ConLeche.quotMkA.toConstantVal).name = ConLeche.quotMkName := rfl
  have n3 : (ConLeche.quotAt .lift ConLeche.quotLiftA.toConstantVal).name = ConLeche.quotLiftName :=
    rfl
  have n4 : (ConLeche.quotAt .ind ConLeche.quotIndA.toConstantVal).name = ConLeche.quotIndName := rfl
  have p1 : ConLeche.quotPinHit .type ConLeche.quotA.toConstantVal = true := by decide
  have p2 : ConLeche.quotPinHit .ctor ConLeche.quotMkA.toConstantVal = true := by decide
  have p3 : ConLeche.quotPinHit .lift ConLeche.quotLiftA.toConstantVal = true := by decide
  have p4 : ConLeche.quotPinHit .ind ConLeche.quotIndA.toConstantVal = true := by decide
  simp only [quotRecords, List.foldlM, ConLeche.checkDecl, ConLeche.checkDeclKind,
    ConLeche.basisNamesOk, ConLeche.checkQuotRecord, ConLeche.installBasisDecl, p1, p2, p3, p4,
    ↓reduceIte]
  simp only [ConLeche.Env.find?] at hEq h1 h2 h3 h4
  simp +decide [ConLeche.quotPredsOk, ConLeche.Env.find?, n1, n2, n3, n4, hEq, h1,
    h2, h3, h4, bind, Except.bind, pure, Except.pure]

/-- **The quotient package** (`checkQuotC`, master's four `checkQuotRecord`
steps). -/
theorem checkQuotC_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    {pins : List ConLeche.NatOpPinSet} {a : InLean.Added} {s₀ s' : InLean.CState}
    (h : InLean.checkQuotC fe s₀ = .ok (a, s')) :
    s' = s₀ ∧ ∃ ds, a.consts.toList.mapM (fun ci => toDecl [ci]) = some ds ∧
      ∀ F, ∃ L', ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins)
        L = .ok L' := by
  rcases checkQuotC_run h with ⟨rfl, rfl⟩ | ⟨hq, h1, h2, h3, h4, rfl, rfl⟩
  · exact ⟨rfl, [], rfl, fun _ => ⟨L, rfl⟩⟩
  obtain ⟨-, -, -, -, -, -, -, c8, -, -⟩ := cl_axNames
  refine ⟨rfl, _, quotRecords_eq, fun F => quotFold_ok ?_ ?_ ?_ ?_ ?_⟩
  · have := find_isSome_of_pres hP (n := InLean.eqName) hq
    rwa [c8] at this
  · exact hP.none _ (FEnv_find_none h1)
  · exact hP.none _ (FEnv_find_none h2)
  · exact hP.none _ (FEnv_find_none h3)
  · exact hP.none _ (FEnv_find_none h4)

/-! ## The kinds together -/

/-- **The arms proved here**: every kind but an inductive block, off the
certified `Nat` operations' names (a definition), the compiler-trust names (an
opaque) and the pinned axioms' names (an axiom: only `sorryAx` and
`Quot.sound` are proved).  The arms left are named in the record (DESIGN,
"Lane O6"); the pinned axioms' arm is false for the code as it stands. -/
@[expose] def ProvedArm : Declaration → Prop
  | .axiomDecl v => v.name = InLean.sorryAxName ∨ v.name = InLean.quotSoundName
  | .defnDecl v => (InLean.natOpNames.contains v.name || InLean.natDivModNames.contains v.name) = false
  | .thmDecl _ => True
  | .opaqueDecl v => InLean.reduceOpNames.contains v.name = false
  | .quotDecl => True
  | .mutualDefnDecl _ => True
  | .inductDecl .. => False

theorem single_fold {pins : List ConLeche.NatOpPinSet} {L : ConLeche.Env} {d : ConLeche.Declaration}
    (h : KindRuns pins L d) (hn : ConLeche.basisNamesOk d = true) :
    ∃ F L', [d].foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
      .ok L' := by
  obtain ⟨F, L', hF⟩ := h.fueled
  exact ⟨F, L', by simp [List.foldlM, checkDecl_of_kind hF hn, bind, Except.bind, pure,
    Except.pure]⟩

/-- **A one-constant record's reserved names** are InLean's on the constant:
an axiom may be `Quot.sound`, a quotient record passes, any other constant is
off the reserved names. -/
theorem basisNamesOk_toDecl {ci : Lean.ConstantInfo} {d : ConLeche.Declaration}
    (hi : ∀ v, ci ≠ .inductInfo v) (h : toDecl [ci] = some d) :
    ConLeche.basisNamesOk d =
      match ci with
      | .axiomInfo v =>
        (v.name == InLean.quotSoundName || !InLean.reservedBasisNames.contains v.name)
      | .quotInfo _ => true
      | ci => !InLean.reservedBasisNames.contains ci.name := by
  obtain ⟨-, c2, -⟩ := cl_axNames
  cases ci
  case inductInfo v => exact (hi v rfl).elim
  all_goals simp only [toDecl, toCV, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq, reduceCtorEq] at h
  all_goals first
    | (obtain ⟨cv, ⟨t, -, rfl⟩, rfl⟩ := h)
    | (obtain ⟨cv, ⟨t, -, rfl⟩, v, -, rfl⟩ := h)
  all_goals simp only [ConLeche.basisNamesOk, reserved_tr,
    Lean.ConstantInfo.name, Lean.ConstantInfo.toConstantVal]
  rw [← c2, toName_beq]

theorem single_mapM {ci : Lean.ConstantInfo} {d : ConLeche.Declaration} (h : toDecl [ci] = some d) :
    (#[ci] : Array Lean.ConstantInfo).toList.mapM (fun ci => toDecl [ci]) = some [d] := by
  simp [h]

/-- **The declaration step for the non-inductive kinds** (O6): InLean's check
of a safe declaration at the theorem's configuration accepting means master's
pure fueled step accepts the records of what it adds, in order, at `L`. -/
theorem checkDeclKindC_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {pins : List ConLeche.NatOpPinSet} {decl : Declaration} {a : InLean.Added}
    {s₀ s' : InLean.CState}
    (hfs : fe.safety = .safe) (hfc : fe.coreAxioms = false)
    (hs : CSOKI .verified false L s₀) (hd : SafeDecl decl) (hr : DeclRangeOk decl)
    (harm : ProvedArm decl) (hbn : InLean.basisNamesOk decl a = true)
    (h : InLean.checkDeclKindC .verified (InLeanProof.theoremConfig lim) fe decl s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      ∃ ds, a.consts.toList.mapM (fun ci => toDecl [ci]) = some ds ∧
        ∃ F L', ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
          .ok L' := by
  cases decl with
  | axiomDecl v =>
    obtain ⟨hsafe, -⟩ := hd
    rcases harm with hn | hn
    · obtain ⟨h1, h2, h3, -, d, hd, hR⟩ := checkAxiomC_sorry_sim (pins := pins) hJ hfs hfc hs hr hsafe
        hn h
      exact ⟨h1, h2, [d], by rw [h3]; exact single_mapM hd,
      single_fold hR (by rw [basisNamesOk_toDecl (fun _ h => by cases h) hd]; exact hbn)⟩
    · obtain ⟨rfl, h3, -, d, hd, hR⟩ := checkAxiomC_quotSound_sim (pins := pins) hJ.pres hr hn h
      exact ⟨hs, TabLe.refl _, [d], by rw [h3]; exact single_mapM hd,
      single_fold hR (by rw [basisNamesOk_toDecl (fun _ h => by cases h) hd]; exact hbn)⟩
  | defnDecl v =>
    obtain ⟨h1, h2, h3, -, d, hd', hR⟩ := checkDefnC_sim (pins := pins) hJ hs hr.1 hr.2 hd harm h
    exact ⟨h1, h2, [d], by rw [h3]; exact single_mapM hd',
      single_fold hR (by rw [basisNamesOk_toDecl (fun _ h => by cases h) hd']; exact hbn)⟩
  | thmDecl v =>
    obtain ⟨h1, h2, h3, -, d, hd', hR⟩ := checkThmC_sim (pins := pins) hJ hs hr.1 hr.2 h
    exact ⟨h1, h2, [d], by rw [h3]; exact single_mapM hd',
      single_fold hR (by rw [basisNamesOk_toDecl (fun _ h => by cases h) hd']; exact hbn)⟩
  | opaqueDecl v =>
    obtain ⟨h1, h2, h3, -, d, hd', hR⟩ := checkOpaqueC_sim (pins := pins) hJ hs hr.1 hr.2 harm h
    exact ⟨h1, h2, [d], by rw [h3]; exact single_mapM hd',
      single_fold hR (by rw [basisNamesOk_toDecl (fun _ h => by cases h) hd']; exact hbn)⟩
  | quotDecl =>
    obtain ⟨rfl, _, hm, hF⟩ := checkQuotC_sim (pins := pins) hJ.pres h
    obtain ⟨L', hL'⟩ := hF 0
    exact ⟨hs, TabLe.refl _, _, hm, 0, L', hL'⟩
  | mutualDefnDecl vs => exact hd.elim
  | inductDecl => exact harm.elim

/-! ## The certified `Nat` operations, named

A definition at a certified operation's name adds master's certification to
the definition arm: the recurrence equations over two interned `Nat`
variables (`certifyNatEqs`), resp. the pin variants (`checkDivModPin`, whose
variants InLean decodes at run time, `PinSet.op?`; `pins` is master's list, so
the statement is about the `pins` P4 relates to InLean's). -/

/-- **The certified operations' arm** (named, not proved here). -/
@[expose] def CertArmSimI (pins : List ConLeche.NatOpPinSet) : Prop :=
  ∀ (lim : InLean.Limits) (fe : InLean.FEnv) (L : ConLeche.Env) (v : DefinitionVal) (a : InLean.Added)
    (s₀ s' : InLean.CState),
    JobEnvI fe L → fe.safety = .safe → fe.coreAxioms = false → CSOKI .verified false L s₀ →
    Expr.RangeOk v.type → Expr.RangeOk v.value → v.safety = .safe →
    (InLean.natOpNames.contains v.name || InLean.natDivModNames.contains v.name) = true →
    InLean.checkDefnC .verified (InLeanProof.theoremConfig lim) fe v s₀ = .ok (a, s') →
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ a.consts = #[.defnInfo v] ∧
      ∃ d, toDecl [.defnInfo v] = some d ∧ KindRuns pins L d

/-- The arms proved here and the certified operations' arm. -/
@[expose] def ProvedOrCertArm (decl : Declaration) : Prop :=
  ProvedArm decl ∨ ∃ v, decl = .defnDecl v

/-- **`checkDeclKindC_sim` with the certified operations' arm** (from
`CertArmSimI`). -/
theorem checkDeclKindC_sim_cert {pins : List ConLeche.NatOpPinSet} (hC : CertArmSimI pins)
    {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L) {decl : Declaration}
    {a : InLean.Added} {s₀ s' : InLean.CState}
    (hfs : fe.safety = .safe) (hfc : fe.coreAxioms = false)
    (hs : CSOKI .verified false L s₀) (hd : SafeDecl decl) (hr : DeclRangeOk decl)
    (harm : ProvedOrCertArm decl) (hbn : InLean.basisNamesOk decl a = true)
    (h : InLean.checkDeclKindC .verified (InLeanProof.theoremConfig lim) fe decl s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      ∃ ds, a.consts.toList.mapM (fun ci => toDecl [ci]) = some ds ∧
        ∃ F L', ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
          .ok L' := by
  rcases harm with harm | ⟨v, rfl⟩
  · exact checkDeclKindC_sim hJ hfs hfc hs hd hr harm hbn h
  · cases hn : (InLean.natOpNames.contains v.name || InLean.natDivModNames.contains v.name)
    · exact checkDeclKindC_sim hJ hfs hfc hs hd hr hn hbn h
    · obtain ⟨h1, h2, h3, d, hd', hR⟩ := hC lim fe L v a s₀ s' hJ hfs hfc hs hr.1 hr.2 hd hn h
      exact ⟨h1, h2, [d], by rw [h3]; exact single_mapM hd',
      single_fold hR (by rw [basisNamesOk_toDecl (fun _ h => by cases h) hd']; exact hbn)⟩

/-! ## The entry point -/

theorem CSOKIF_empty : CSOKIF ({} : InLean.CState) where
  fv := ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩
  fvClosed := by simp
  lsimp := by simp
  eqv := by simp

theorem CSOKI_empty (L : ConLeche.Env) : CSOKI .verified false L ({} : InLean.CState) :=
  flushI_csoki CSOKIF_empty .verified false L

/-- The entry point from the kinds' simulation at the fresh state: the
reserved names' check passed to it, the `sorryAxSquat` decline read as "no
constant but an axiom at `sorryAx`". -/
theorem checkDecl_sim_of {E : Kernel.Environment} {L : ConLeche.Env}
    {pins : List ConLeche.NatOpPinSet} {decl : Declaration} {a : InLean.Added}
    (hK : ∀ {a : InLean.Added} {s' : InLean.CState},
      InLean.checkDeclKindC .verified (InLeanProof.theoremConfig lim) { env := E, coreAxioms := false, limits := lim } decl
        {} = .ok (a, s') → InLean.basisNamesOk decl a = true →
      ∃ ds, a.consts.toList.mapM (fun ci => toDecl [ci]) = some ds ∧
        ∃ F L', ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
          .ok L')
    (h : InLean.checkDecl (InLeanProof.theoremConfig lim) E decl = .ok a) :
    (∀ ci ∈ a.consts.toList, ci.name = InLean.sorryAxName → ∃ v, ci = .axiomInfo v) ∧
      ∃ ds, a.consts.toList.mapM (fun ci => toDecl [ci]) = some ds ∧
        ∃ F L', ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
          .ok L' := by
  unfold InLean.checkDecl at h
  split at h
  · exact nomatch h
  unfold InLean.runC at h
  dsimp only at h
  split at h
  · rename_i a' s' hrun
    cases h
    obtain ⟨b, s₁, hKr, hT⟩ := bindI_ok hrun
    have hnb : InLean.basisNamesOk decl b = true := by
      cases hc : InLean.basisNamesOk decl b
      · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hT
        exact (throw_bindI_ok hT).elim
      · rfl
    simp only [hnb, ↓reduceIte] at hT
    have hab : b = a ∧ b.consts.any InLean.sorryAxSquat = false := by
      split at hT
      · exact (throw_bindI_ok hT).elim
      · rename_i hc
        obtain ⟨rfl, -⟩ := pureI_ok hT
        exact ⟨rfl, by simpa [show (theoremConfig lim).coreAxioms = false from rfl] using hc⟩
    obtain ⟨rfl, hsq'⟩ := hab
    obtain ⟨ds, hds, F, L', hF⟩ := hK hKr hnb
    refine ⟨fun ci hci hn => ?_, ds, hds, F, L', hF⟩
    simp only [← Array.any_toList, List.any_eq_false] at hsq'
    have := hsq' ci hci
    cases ci with
    | axiomInfo v => exact ⟨v, rfl⟩
    | _ => simp [InLean.sorryAxSquat, hn] at this
  · exact nomatch h

/-- **InLean's declaration check, the non-inductive kinds** (O6, at the entry
point): InLean's `checkDecl` at the theorem's configuration accepting a safe
declaration in range on a proved arm means master's pure fueled step accepts
the records of the constants it adds, in order, at any `L` the job's premises
relate to the environment; and no constant it adds but an axiom takes
`sorryAx`'s name (`sorryAxSquat`, what `presI_defn`/`presI_thm`/
`presI_opaque` need: con-leche's policy hides the name). -/
theorem checkDecl_sim {E : Kernel.Environment} {L : ConLeche.Env}
    (hJ : JobEnvI { env := E, coreAxioms := false, limits := lim } L) {pins : List ConLeche.NatOpPinSet}
    {decl : Declaration} {a : InLean.Added}
    (hd : SafeDecl decl) (hr : DeclRangeOk decl) (harm : ProvedArm decl)
    (h : InLean.checkDecl (InLeanProof.theoremConfig lim) E decl = .ok a) :
    (∀ ci ∈ a.consts.toList, ci.name = InLean.sorryAxName → ∃ v, ci = .axiomInfo v) ∧
      ∃ ds, a.consts.toList.mapM (fun ci => toDecl [ci]) = some ds ∧
        ∃ F L', ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
          .ok L' :=
  checkDecl_sim_of (fun hK hbn =>
    (checkDeclKindC_sim (pins := pins) hJ rfl rfl (CSOKI_empty L) hd hr harm hbn hK).2.2) h

end InLeanProof
