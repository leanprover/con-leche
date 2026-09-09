module

public import ConLeche.Verify.Cached.MainC
public import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.Cached.KnotCongr
public import ConLeche.Model.Installed

public section

/-!
# The driver's type and the pure fold reach the specification (task #253)

`FullyCheckedSpec μ` (`ConLeche/Verify/Installed.lean`) is the
specification of an installed and checked environment, stated over the
pure fueled checker, and `no_proof_of_False_spec`
(`ConLeche/Model/Installed.lean`) its consistency letter.  This module is
where the executable reaches it:

* **The driver's type** `FullyChecked μ ds` (`ConLeche/Cached/Installed.lean`):
  phase A's accepting run (`InstallRun`) installs a separable value
  declaration by the install half and records its datum, and every
  record was checked against the prefix view `fe.restrictTo vis` from a
  fresh memo state (`GroupChecked`).  The prefix view and `mkFEnv` of
  the truncated environment have the same `find?`
  (`mkFEnv_find?_visibleBelow`, under the name uniqueness every driver
  step preserves — `PushChain`), so by `coreKnotI_congr` they run the
  SAME core, and the simulation stated at `mkFEnv env` covers the
  check at the view: `checkPending_run` turns the cached check into
  `checkValueGroup`'s pure run at the prefix.  `installRun_model` walks
  the run, `fullyChecked_spec` packages the walk, and
  `fullyChecked_sound` / `no_proof_of_False_checked` are the letters on
  the driver's type.
* **The ordinary fold** (`checkDecls`): every group is checked in full
  as it is installed, so the trace it leaves has no pending datum
  (`GroupInstalled`'s `none` case at every group) and every group is
  trivially checked — `checkDecls_spec`.

Both walks thread the graded model (`declStep_preserves`) beside the
trace, exactly as `fold_preserves` does: the model at each position
supplies the well-formedness of the environment that every bridge from
the executable core to the pure one takes as its hypothesis — which is
why the set theory is a hypothesis of `fullyChecked_spec` although its
conclusion does not mention it.
-/

namespace ConLeche.Cached

open ConLeche ConLeche.Semantics ConLeche.Model

universe w
variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The push chain of a fold -/

/-- The ordinary fold is a fresh chain. -/
theorem fold_push {env : Env} :
    ∀ (ds : List DeclC) {fe : FEnv} {s₀ : CState} {fe' : FEnv} {s' : CState},
      PushChain env fe →
      (ds.foldlM (checkDeclStepC μ) fe) s₀ = .ok (fe', s') → PushChain env fe' :=
  fun ds {fe} {s₀} {fe'} {s'} h hrun =>
    (Yields.foldlM_rel (R := fun fe (_ : Unit) => PushChain env fe) (g := fun u _ => u)
      (fun _ pd _ hacc => checkDeclStepC_push μ hacc pd) ds fe () h) s₀ fe' s' hrun

/-! ## The ordinary fold -/

/-- The fold's trace: every group checked in full as it was
installed, the model threaded beside it. -/
theorem fold_trace (hμ : μ.verifiedChecks = true) :
    ∀ (ds : List DeclC) (fe : FEnv) {fe' : FEnv} {s₀ s' : CState},
      fe = mkFEnv fe.env →
      EnvModelOk V μ fe.env →
      CSOKF s₀ →
      (ds.foldlM (checkDeclStepC μ) fe) s₀ = .ok (fe', s') →
      EnvModelOk V μ fe'.env ∧
      ∃ gs : List Group, InstallTrace μ fe.env gs fe'.env ∧
        (∀ g ∈ gs, g.value? = none) ∧
        (∀ g ∈ gs, EnvWF (fe'.env.prefixTo g.vis))
  | [], fe, fe', s₀, s', _, hm, _, h => by
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    refine ⟨hm, [], ?_, ?_, ?_⟩
    · show fe.env = fe.env
      rfl
    · intro _ hg; exact (List.not_mem_nil hg).elim
    · intro _ hg; exact (List.not_mem_nil hg).elim
  | pc :: ds, fe, fe', s₀, s', hfe, hm, hres, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstepC, h⟩ := bindC_ok h
    obtain ⟨⟨mp⟩, hE⟩ := hm
    obtain ⟨d, hd⟩ := DeclCRel_total pc
    have hpush : PushChain fe.env fe₁ :=
      checkDeclStepC_push μ (PushChain.refl fe.env) pc s₀ fe₁ s₁ (hfe ▸ hstepC)
    rw [hfe] at hstepC
    obtain ⟨hres₁, hfe₁, F, hF⟩ :=
      checkDeclStepC_run hμ mp.toEnvFacts.wf hres hd hstepC
    have hm₁ : EnvModelOk V μ fe₁.env :=
      declStep_preserves hμ mp hE (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hF)
    obtain ⟨hm', gs, htr, hnone, hwf⟩ := fold_trace hμ ds fe₁ hfe₁ hm₁ hres₁ h
    have hg : GroupInstalled μ F fe.env ⟨d, fe.env.consts.length, none⟩ fe₁.env :=
      ⟨rfl, hpush.2.1, hF⟩
    refine ⟨hm', ⟨d, fe.env.consts.length, none⟩ :: gs, ⟨F, fe₁.env, hg, htr⟩, ?_, ?_⟩
    · intro g hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · rfl
      · exact hnone g hg'
    · intro g hg'
      rcases List.mem_cons.mp hg' with rfl | hg'
      · rw [InstallTrace.prefix_head hg htr]
        exact mp.toEnvFacts.wf
      · exact hwf g hg'

/-- **The ordinary fold yields a fully checked environment**, in the
specification's sense: every group checked in full at its install. -/
theorem checkDecls_spec (V : Type w) [SetTheory V] (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} {env' : Env} (h : checkDecls μ ds = .ok env') :
    ∃ sp : FullyCheckedSpec μ, sp.env = env' := by
  obtain ⟨fe, s', hrun, rfl⟩ := checkDecls_run h
  obtain ⟨⟨⟨mp⟩, -⟩, gs, htr, hnone, hwf⟩ := fold_trace (V := V) hμ ds (mkFEnv Env.empty) rfl
    ⟨⟨EnvModelM.empty V μ⟩, EtaFamiliesClosed.empty⟩ CSOKF.empty hrun
  have hchain := fold_push (env := Env.empty) ds (PushChain.refl Env.empty) hrun
  refine ⟨⟨⟨fe.env, gs, htr, hchain.2.2 List.nodup_nil, hwf, mp.toEnvFacts.wf⟩, ?_⟩, rfl⟩
  intro i
  unfold GroupCheckedSpec
  cases hi : gs[i]? with
  | none => trivial
  | some g =>
    have := hnone g (List.mem_iff_getElem?.mpr ⟨i, hi⟩)
    simp only [this]

/-! ## The two-phase driver: phase A's install halves -/

/-- Phase A's header install simulates the pure install half: from an
invariant state at `mkFEnv env`, a successful run returns the header
with its annotated type, well scoped, and `installConstantVal` succeeds
on it at some fuel. -/
theorem annotConstantValC_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {cv cvA : ConstantVal} {jty : ExprC} {s₀ s' : CState} (hs : CSOK μ env s₀)
    (h : annotConstantValC μ (mkFEnv env) cv s₀ = .ok ((cvA, jty), s')) :
    CSOK μ env s' ∧ cvA = { cv with type := jty } ∧ Expr.WScoped 0 jty ∧
    ∃ F, installConstantVal (fueledOps μ F) env cv = .ok cvA := by
  unfold annotConstantValC at h
  simp only [mkFEnv_find?] at h
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h; exact absurd h throwC_bind_ok
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h; exact absurd h throwC_bind_ok
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h; exact absurd h throwC_bind_ok
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; exact absurd h throwC_bind_ok
  rw [if_pos h4] at h
  rw [ExprC.looseBVarsBounded_spec] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [if_neg h5] at h; exact absurd h throwC_bind_ok
  rw [if_pos h5] at h
  rw [hasFvar_spec rfl] at h
  by_cases h6 : Expr.hasFvar cv.type = true
  · rw [if_pos h6] at h; exact absurd h throwC_bind_ok
  rw [if_neg h6] at h
  obtain ⟨jA, s₁, hann, h⟩ := bindC_ok h
  obtain ⟨hs₁, w, ⟨hjA, hwty⟩, F, hF⟩ :=
    (ssimC hμ env henv checkFuel).annotate hs rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h6)) jA s₁ hann
  obtain rfl := hjA
  rw [ExprC.allLevelParamsDefined_spec] at h
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams jA = true
  case neg => rw [if_neg h7] at h; exact absurd h throwC_bind_ok
  rw [if_pos h7] at h
  rw [constsResolveFC_spec, constsResolveF_eq] at h
  by_cases h8 : Expr.constsResolve env jA = true
  case neg => rw [if_neg h8] at h; exact absurd h throwC_bind_ok
  rw [if_pos h8] at h
  obtain ⟨hv, rfl⟩ := pureC_ok h
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hv
  refine ⟨hs₁, rfl, hwty, F, ?_⟩
  exact installConstantVal_of_facts (Option.not_isSome_iff_eq_none.mp h1)
    (by simpa using h2) (by simpa using h3) h4 h5 (by simpa using h6) hF h7 h8

/-- Phase A's value install simulates the pure install half. -/
theorem annotValC_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {jty value jv : ExprC} {record : Bool} {s₀ s' : CState}
    (hjty : jty = cvA.type) (hs : CSOK μ env s₀)
    (h : annotValC μ (mkFEnv env) cvA jty value record s₀ = .ok (jv, s')) :
    CSOK μ env s' ∧ Expr.WScoped 0 jv ∧
    ∃ F, installValue (fueledOps μ F) env cvA value = .ok jv := by
  unfold annotValC at h
  rw [ExprC.looseBVarsBounded_spec] at h
  by_cases h1 : Expr.looseBVarsBounded 0 value = true
  case neg => rw [if_neg h1] at h; exact absurd h throwC_bind_ok
  rw [if_pos h1] at h
  rw [hasFvar_spec rfl] at h
  by_cases h2 : Expr.hasFvar value = true
  · rw [if_pos h2] at h; exact absurd h throwC_bind_ok
  rw [if_neg h2] at h
  obtain ⟨jA, s₁, hann, h⟩ := bindC_ok h
  obtain ⟨hs₁, w, ⟨hjA, hwv⟩, F, hF⟩ :=
    (ssimC hμ env henv checkFuel).annotate hs rfl
      (Expr.WScoped.of_not_hasFvar (Bool.not_eq_true _ ▸ h2)) jA s₁ hann
  obtain rfl := hjA
  rw [ExprC.allLevelParamsDefined_spec] at h
  by_cases h3 : Expr.allLevelParamsDefined cvA.levelParams jA = true
  case neg => rw [if_neg h3] at h; exact absurd h throwC_bind_ok
  rw [if_pos h3] at h
  rw [constsResolveFC_spec, constsResolveF_eq] at h
  by_cases h4 : Expr.constsResolve env jA = true
  case neg => rw [if_neg h4] at h; exact absurd h throwC_bind_ok
  rw [if_pos h4] at h
  obtain ⟨u, s₂, hrec, h⟩ := bindC_ok h
  obtain ⟨hs₂, -⟩ := recordCConst_eff hs₁ (hjty ▸ rfl)
    (fun vE vi hv => by
      cases record <;> simp only [Bool.false_eq_true, ↓reduceIte] at hv
      · exact nomatch hv
      · cases hv; rfl) u s₂ hrec
  obtain ⟨rfl, rfl⟩ := pureC_ok h
  exact ⟨hs₂, hwv, F, installValue_of_facts h1 (by simpa using h2) hF h3 h4⟩

/-! ## The two-phase driver: phase B's check at the prefix view -/

/-- Phase B's check at the prefix view simulates the pure check half at
the environment the view names: the view and `mkFEnv env` have the same
`find?`, so by `coreKnotI_congr` the check runs the core the
simulation is stated about. -/
theorem checkPending_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {feFinal : FEnv} {pc : PendingCheck}
    (hfind : ∀ n, (feFinal.restrictTo pc.vis).find? n = env.find? n)
    (hwty : Expr.WScoped 0 pc.vg.cvA.type) (hwv : Expr.WScoped 0 pc.vg.jv)
    {s₀ s' : CState} (hres : CSOKF s₀)
    (h : checkPending μ feFinal pc s₀ = .ok ((), s')) :
    CSOKF s' ∧ ∃ F, checkValueGroup (fueledOps μ F) env pc.vg = .ok () := by
  have hfe : (feFinal.restrictTo pc.vis).find? = (mkFEnv env).find? :=
    funext fun n => (hfind n).trans (mkFEnv_find? env n).symm
  unfold checkPending at h
  simp only [coreKnotI_congr hfe, opSIxC_congr hfe] at h
  obtain ⟨u₀, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  have hcs : CSOK μ env s₀.flushed := flushC_csok hres
  obtain ⟨jsty, s₂, hst, h⟩ := bindC_ok h
  obtain ⟨hs₂, wsty, ⟨rfl, hwsty⟩, F₁, hF₁⟩ :=
    (ssimC hμ env henv checkFuel).infer hcs rfl hwty jsty s₂ hst
  obtain ⟨u, s₃, hsort, h⟩ := bindC_ok h
  obtain ⟨hs₃, u', rfl, F₂, hF₂⟩ := opSIxC_sim hμ henv hs₂ rfl hwsty u s₃ hsort
  -- the value's typing, after the theorem test
  have tail : ∀ {s₄ : CState}, CSOK μ env s₄ →
      ((coreKnotI μ (mkFEnv env) checkFuel).infer 0 pc.vg.jv >>= fun jvt =>
        (coreKnotI μ (mkFEnv env) checkFuel).defeq 0 jvt pc.vg.cvA.type >>= fun b =>
          if b = true then pure () else
            throw (.invalid s!"type mismatch in {pc.vg.kind.word} {pc.vg.cvA.name}")) s₄
        = .ok ((), s') →
      CSOKF s' ∧ ∃ F jvt, inferTypeCore μ env F 0 pc.vg.jv = .ok jvt ∧
        isDefEqCore μ env F 0 jvt pc.vg.cvA.type = .ok true := by
    intro s₄ hs₄ h
    obtain ⟨jvt, s₅, hvt, h⟩ := bindC_ok h
    obtain ⟨hs₅, wvt, ⟨rfl, hwvt⟩, F₃, hF₃⟩ :=
      (ssimC hμ env henv checkFuel).infer hs₄ rfl hwv jvt s₅ hvt
    obtain ⟨b, s₆, hde, h⟩ := bindC_ok h
    obtain ⟨hs₆, b', rfl, F₄, hF₄⟩ :=
      (ssimC hμ env henv checkFuel).defeq hs₅ rfl rfl hwvt hwty b s₆ hde
    cases b with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact nomatch h
    | true =>
      simp only [↓reduceIte] at h
      obtain ⟨-, rfl⟩ := pureC_ok h
      exact ⟨hs₆.residue, max F₃ F₄, jvt, inferTypeCore_mono (Nat.le_max_left _ _) hF₃,
        isDefEqCore_mono (Nat.le_max_right _ _) hF₄⟩
  by_cases hk : pc.vg.kind = .thm
  · rw [if_pos hk] at h
    obtain ⟨b, s₄, hlift, h⟩ := bindC_ok h
    obtain ⟨hs₄, b', rfl, F₀, hF₀⟩ := SimC.liftFueled _ _ hs₃ b s₄ hlift
    rw [liftFueled_atF] at hF₀
    cases heqv : Level.isEquiv u .zero with
    | none => rw [heqv] at hF₀; exact nomatch hF₀
    | some b₀ =>
    rw [heqv] at hF₀
    simp only [liftFueled, pure, Except.pure, Except.ok.injEq] at hF₀
    subst hF₀
    cases b₀ with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact absurd h throwC_bind_ok
    | true =>
    simp only [↓reduceIte] at h
    obtain ⟨hres', F₅, jvt, hvt, hde⟩ := tail hs₄ h
    refine ⟨hres', max (max F₁ F₂) F₅, ?_⟩
    exact checkValueGroup_of_facts
      (inferTypeCore_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hF₁)
      (ensureSortCore_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hF₂)
      (fun _ => heqv) (inferTypeCore_mono (Nat.le_max_right _ _) hvt)
      (isDefEqCore_mono (Nat.le_max_right _ _) hde)
  · rw [if_neg hk] at h
    obtain ⟨hres', F₅, jvt, hvt, hde⟩ := tail hs₃ h
    refine ⟨hres', max (max F₁ F₂) F₅, ?_⟩
    exact checkValueGroup_of_facts
      (inferTypeCore_mono (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)) hF₁)
      (ensureSortCore_mono (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) hF₂)
      (fun hk' => absurd hk' hk) (inferTypeCore_mono (Nat.le_max_right _ _) hvt)
      (isDefEqCore_mono (Nat.le_max_right _ _) hde)

/-- Phase A's value install, run: the two halves at a common fuel, the
annotated terms well scoped, the residue kept. -/
theorem annotValueC_run (hμ : μ.verifiedChecks = true) {env : Env} (henv : EnvWF env)
    {cv cvA : ConstantVal} {value jty jv : ExprC} {record : Bool} {s₀ s' : CState}
    (hres : CSOKF s₀)
    (h : annotValueC μ (mkFEnv env) cv value record s₀ = .ok ((cvA, jty, jv), s')) :
    CSOKF s' ∧ cvA = { cv with type := jty } ∧ Expr.WScoped 0 jty ∧ Expr.WScoped 0 jv ∧
    ∃ F, installConstantVal (fueledOps μ F) env cv = .ok cvA ∧
      installValue (fueledOps μ F) env cvA value = .ok jv := by
  unfold annotValueC at h
  obtain ⟨u₀, s₁, hflush, h⟩ := bindC_ok h
  rw [flushC_run] at hflush
  injection hflush with hflush
  obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
  obtain ⟨pr, s₂, hcv, h⟩ := bindC_ok h
  obtain ⟨cvA', jty'⟩ := pr
  obtain ⟨hs₂, hcvA, hwty, F₁, hI⟩ := annotConstantValC_run hμ henv (flushC_csok hres) hcv
  obtain ⟨jv', s₃, hv, h⟩ := bindC_ok h
  obtain ⟨hs₃, hwv, F₂, hV⟩ := annotValC_run hμ henv (by rw [hcvA]) hs₂ hv
  obtain ⟨hv, rfl⟩ := pureC_ok h
  simp only [Prod.mk.injEq] at hv
  obtain ⟨rfl, rfl, rfl⟩ := hv
  exact ⟨hs₃.residue, hcvA, hwty, hwv, max F₁ F₂,
    installConstantVal_mono (Nat.le_max_left _ _) hI, installValue_mono (Nat.le_max_right _ _) hV⟩

/-- The lookup at the prefix view of a canonical, name-unique index whose
environment extends `env` by exactly the constants above `env`'s
length is `env`'s lookup. -/
theorem restrictTo_find?_of_extends {feFinal : FEnv} {env : Env}
    (hcanon : feFinal = mkFEnv feFinal.env) (hnd : NodupNames feFinal.env)
    {new : List ConstantInfo} (hext : feFinal.env.consts = new ++ env.consts) (n : Name) :
    (feFinal.restrictTo env.consts.length).find? n = env.find? n := by
  have h1 : (feFinal.restrictTo env.consts.length).find? n
      = ((mkFEnv feFinal.env).restrictTo env.consts.length).find? n := by
    rw [← hcanon]
  rw [h1, mkFEnv_find?_visibleBelow feFinal.env env.consts.length n hnd,
    Env.prefixTo_of_extends hext]

/-! ## The driver's trace -/

set_option maxHeartbeats 2000000 in
/-- **The driver's trace**: phase A's accepting run from a canonical
index whose environment carries the model, with every record of the
final index checked from a fresh memo state, threads the model and
leaves an install trace whose value groups are checked at their
prefixes.  (The model at each position supplies the well-formedness of
the environment every bridge from the executable core takes; the
records' checks are consumed at the positions that produced them.) -/
theorem installRun_model (hμ : μ.verifiedChecks = true) {ds : List DeclC}
    {p : Nat × FEnv × Array PendingCheck} {s : CState}
    {q : Nat × FEnv × Array PendingCheck} {s' : CState}
    (hrun : InstallRun μ ds p s q s') :
    p.2.1 = mkFEnv p.2.1.env → EnvModelOk V μ p.2.1.env → CSOKF s →
    NodupNames q.2.1.env →
    (∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) →
    EnvModelOk V μ q.2.1.env ∧
    ∃ gs : List Group, InstallTrace μ p.2.1.env gs q.2.1.env ∧
      (∀ g ∈ gs, EnvWF (q.2.1.env.prefixTo g.vis)) ∧
      (∀ g ∈ gs, ∀ vg, g.value? = some vg →
        ∃ F, checkValueGroup (fueledOps μ F) (q.2.1.env.prefixTo g.vis) vg = .ok ()) := by
  induction hrun with
  | nil p s =>
    intro _ hm _ _ _
    refine ⟨hm, [], ?_, ?_, ?_⟩
    · show p.2.1.env = p.2.1.env
      rfl
    · intro _ hg; exact (List.not_mem_nil hg).elim
    · intro _ hg; exact (List.not_mem_nil hg).elim
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    intro hfe hm hresA hnd hB
    obtain ⟨i, fe, pend⟩ := p
    obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    simp only at hfe hstepC
    obtain ⟨hpush₁, -⟩ :=
      annotStepC_push μ i (PushChain.self hfe) pend pd s (fe₁, pend₁) s₁ hstepC
    have hfe₁ : fe₁ = mkFEnv fe₁.env := hpush₁.canon
    obtain ⟨hchainF, new₁, hpend₁⟩ := installRun_trace μ rest (PushChain.self hfe₁)
    obtain ⟨⟨mp⟩, hE⟩ := hm
    have henv : EnvWF fe.env := mp.toEnvFacts.wf
    -- the ordinary step: a group checked in full at its install
    have ordinary : ∀ (pd' : DeclC),
        (checkDeclStepC μ fe pd' >>= fun fe' => pure (fe', pend)) s = .ok ((fe₁, pend₁), s₁) →
        EnvModelOk V μ q.2.1.env ∧
        ∃ gs : List Group, InstallTrace μ fe.env gs q.2.1.env ∧
          (∀ g ∈ gs, EnvWF (q.2.1.env.prefixTo g.vis)) ∧
          (∀ g ∈ gs, ∀ vg, g.value? = some vg →
            ∃ F, checkValueGroup (fueledOps μ F) (q.2.1.env.prefixTo g.vis) vg = .ok ()) := by
      intro pd' hst
      obtain ⟨fe₁', s₁', hstepC', hp⟩ := bindC_ok hst
      obtain ⟨hv, rfl⟩ := pureC_ok hp
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      obtain ⟨d, hd⟩ := DeclCRel_total pd'
      rw [hfe] at hstepC'
      obtain ⟨hres₁, -, F, hF⟩ := checkDeclStepC_run hμ henv hresA hd hstepC'
      have hm₁ : EnvModelOk V μ fe₁'.env :=
        declStep_preserves hμ mp hE (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hF)
      obtain ⟨hm', gs, htr, hwf, hchk⟩ := ih hfe₁ hm₁ hres₁ hnd hB
      have hg : GroupInstalled μ F fe.env ⟨d, fe.env.consts.length, none⟩ fe₁'.env :=
        ⟨rfl, hpush₁.2.1, hF⟩
      refine ⟨hm', ⟨d, fe.env.consts.length, none⟩ :: gs, ⟨F, _, hg, htr⟩, ?_, ?_⟩
      · intro g hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · rw [InstallTrace.prefix_head hg htr]; exact henv
        · exact hwf g hg'
      · intro g hg' vg hvg
        rcases List.mem_cons.mp hg' with rfl | hg'
        · exact nomatch hvg
        · exact hchk g hg' vg hvg
    -- a separable value declaration: phase A's install, phase B's check
    have value : ∀ (cv : ConstantVal) (value : ExprC) (record : Bool) (kind : ValueKind)
        (mk : ConstantVal → ExprC → ConstantInfo) (d : Declaration)
        (cvA : ConstantVal) (jty jv : ExprC),
        annotValueC μ fe cv value record s = .ok ((cvA, jty, jv), s₁) →
        fe₁ = fe.push (mk cvA jv) →
        pend₁ = pend.push ⟨⟨kind, cvA, jv⟩, i, fe.visibleBelow⟩ →
        (∀ (cvA : ConstantVal) (jv : ExprC) (F : Nat),
          installConstantVal (fueledOps μ F) fe.env cv = .ok cvA →
          installValue (fueledOps μ F) fe.env cvA value = .ok jv →
          checkValueGroup (fueledOps μ F) fe.env ⟨kind, cvA, jv⟩ = .ok () →
          GroupInstalled μ F fe.env ⟨d, fe.env.consts.length, some ⟨kind, cvA, jv⟩⟩
            ⟨mk cvA jv :: fe.env.consts⟩ ∧
          checkDecl μ (fueledOps μ F) fe.env d = .ok ⟨mk cvA jv :: fe.env.consts⟩) →
        EnvModelOk V μ q.2.1.env ∧
        ∃ gs : List Group, InstallTrace μ fe.env gs q.2.1.env ∧
          (∀ g ∈ gs, EnvWF (q.2.1.env.prefixTo g.vis)) ∧
          (∀ g ∈ gs, ∀ vg, g.value? = some vg →
            ∃ F, checkValueGroup (fueledOps μ F) (q.2.1.env.prefixTo g.vis) vg = .ok ()) := by
      intro cv value record kind mk d cvA jty jv hval hfe₁' hpend₁' hsplit
      subst hfe₁' hpend₁'
      rw [hfe] at hval
      obtain ⟨hres₁, hcvA, hwty, hwv, F₁, hI, hV⟩ := annotValueC_run hμ henv hresA hval
      -- the record's check, from a fresh memo state
      have hmem : (⟨⟨kind, cvA, jv⟩, i, fe.visibleBelow⟩ : PendingCheck) ∈ q.2.2.toList := by
        rw [hpend₁, Array.toList_push]
        exact List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl))
      obtain ⟨sB, hchk⟩ := hB _ hmem
      have hvis : fe.visibleBelow = fe.env.consts.length := by
        rw [hfe]; exact mkFEnv_visibleBelow _
      have hfind : ∀ n, (q.2.1.restrictTo fe.env.consts.length).find? n = fe.env.find? n := by
        obtain ⟨newF, hnewF⟩ := hchainF.2.1
        exact restrictTo_find?_of_extends hchainF.canon hnd
          (new := newF ++ [mk cvA jv]) (by rw [hnewF, List.append_assoc]; rfl)
      have hwty' : Expr.WScoped 0 (ConstantVal.type cvA) := by rw [hcvA]; exact hwty
      obtain ⟨-, F₂, hC⟩ := checkPending_run hμ henv
        (pc := ⟨⟨kind, cvA, jv⟩, i, fe.visibleBelow⟩) (by rw [hvis]; exact hfind)
        hwty' hwv CSOKF.empty hchk
      -- the two halves are the declaration's check
      obtain ⟨hg, hF⟩ := hsplit cvA jv (max F₁ F₂)
        (installConstantVal_mono (Nat.le_max_left _ _) hI)
        (installValue_mono (Nat.le_max_left _ _) hV)
        (checkValueGroup_mono (Nat.le_max_right _ _) hC)
      have hm₁ : EnvModelOk V μ (fe.push (mk cvA jv)).env :=
        declStep_preserves hμ mp hE (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hF)
      obtain ⟨hm', gs, htr, hwf, hchk'⟩ := ih hfe₁ hm₁ hres₁ hnd hB
      refine ⟨hm', ⟨d, fe.env.consts.length, some ⟨kind, cvA, jv⟩⟩ :: gs,
        ⟨max F₁ F₂, _, hg, htr⟩, ?_, ?_⟩
      · intro g hg'
        rcases List.mem_cons.mp hg' with rfl | hg'
        · rw [InstallTrace.prefix_head hg htr]; exact henv
        · exact hwf g hg'
      · intro g hg' vg hvg
        rcases List.mem_cons.mp hg' with rfl | hg'
        · cases hvg
          rw [InstallTrace.prefix_head hg htr]
          exact ⟨F₂, hC⟩
        · exact hchk' g hg' vg hvg
    cases pd with
    | defnDecl cv val hint =>
      unfold annotStepC at hstepC
      simp only [] at hstepC
      split at hstepC
      · exact ordinary _ hstepC
      · rename_i hnat
        obtain ⟨r, s₁', hval, hp⟩ := bindC_ok hstepC
        obtain ⟨cvA, jty, jv⟩ := r
        obtain ⟨hv, rfl⟩ := pureC_ok hp
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        refine value cv val true .defn (fun cvA jv => .defnInfo cvA jv hint)
          (.defnDecl cv val hint) cvA jty jv hval rfl rfl ?_
        intro cvA jv F hI hV hC
        have hnat' : (natOpNames.contains cv.name || natDivModNames.contains cv.name) = false :=
          Bool.not_eq_true _ ▸ hnat
        exact ⟨⟨rfl, hnat', rfl, hI, hV, rfl⟩, checkDecl_of_split_defn hnat' hI hV hC⟩
    | thmDecl cv val =>
      unfold annotStepC at hstepC
      simp only [] at hstepC
      obtain ⟨r, s₁', hval, hp⟩ := bindC_ok hstepC
      obtain ⟨cvA, jty, jv⟩ := r
      obtain ⟨hv, rfl⟩ := pureC_ok hp
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      refine value cv val true .thm (fun cvA jv => .thmInfo cvA jv) (.thmDecl cv val)
        cvA jty jv hval rfl rfl ?_
      intro cvA jv F hI hV hC
      exact ⟨⟨rfl, rfl, hI, hV, rfl⟩, checkDecl_of_split_thm rfl hI hV hC⟩
    | opaqueDecl cv val =>
      unfold annotStepC at hstepC
      simp only [] at hstepC
      split at hstepC
      · exact ordinary _ hstepC
      · rename_i hred
        obtain ⟨r, s₁', hval, hp⟩ := bindC_ok hstepC
        obtain ⟨cvA, jty, jv⟩ := r
        obtain ⟨hv, rfl⟩ := pureC_ok hp
        simp only [Prod.mk.injEq] at hv
        obtain ⟨rfl, rfl⟩ := hv
        refine value cv val false .opaque (fun cvA _ => .axiomInfo cvA) (.opaqueDecl cv val)
          cvA jty jv hval rfl rfl ?_
        intro cvA jv F hI hV hC
        have hred' : reduceOpNames.contains cv.name = false := Bool.not_eq_true _ ▸ hred
        exact ⟨⟨rfl, hred', rfl, hI, hV, rfl⟩, checkDecl_of_split_opaque hred' hI hV hC⟩
    | axiomDecl cv => unfold annotStepC at hstepC; exact ordinary _ hstepC
    | basisDecl kind => unfold annotStepC at hstepC; exact ordinary _ hstepC
    | indDecl block nP => unfold annotStepC at hstepC; exact ordinary _ hstepC

/-- Every record of a fully checked environment was checked from a
fresh memo state. -/
theorem FullyChecked.records {ds : List DeclC} (fc : FullyChecked μ ds) :
    ∀ pc ∈ fc.1.pend.toList, ∃ s'', checkPending μ fc.1.fe pc {} = .ok ((), s'') := by
  intro pc hpc
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.mp hpc
  have h := fc.2 k
  unfold GroupChecked at h
  rw [Array.getElem?_toList] at hk
  rw [hk] at h
  exact h

/-- **The driver's fully checked environment is one in the
specification's sense** — the bridge from the executable steps to the
pure checker's two halves.  The set theory is a hypothesis because the
bridge threads the model for the well-formedness it needs; the
conclusion does not mention it. -/
theorem fullyChecked_spec (V : Type w) [SetTheory V] (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} (fc : FullyChecked μ ds) :
    ∃ sp : FullyCheckedSpec μ, sp.env = fc.env := by
  obtain ⟨n, s, r⟩ := fc.1.run
  have hchain := installRun_trace μ r (PushChain.refl Env.empty)
  obtain ⟨⟨⟨mp⟩, -⟩, gs, htr, hwf, hchk⟩ := installRun_model (V := V) hμ r rfl
    ⟨⟨EnvModelM.empty V μ⟩, EtaFamiliesClosed.empty⟩ CSOKF.empty
    (hchain.1.2.2 List.nodup_nil) fc.records
  refine ⟨⟨⟨fc.1.fe.env, gs, htr, hchain.1.2.2 List.nodup_nil, hwf, mp.toEnvFacts.wf⟩, ?_⟩, rfl⟩
  intro i
  unfold GroupCheckedSpec
  cases hi : gs[i]? with
  | none => trivial
  | some g =>
    dsimp only
    cases hvg : g.value? with
    | none => trivial
    | some vg => exact hchk g (List.mem_iff_getElem?.mpr ⟨i, hi⟩) vg hvg

/-- **A fully checked environment carries the model.** -/
theorem fullyChecked_sound (V : Type w) [SetTheory V] (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} (fc : FullyChecked μ ds) :
    Nonempty (EnvModelM V μ fc.env) := by
  obtain ⟨sp, hsp⟩ := fullyChecked_spec V hμ fc
  rw [← hsp]
  exact fullyCheckedSpec_sound hμ sp

/-- **THE LETTER ON THE DRIVER'S TYPE**: a fully checked environment, in
a validating mode, holds no constant of type `False`. -/
theorem no_proof_of_False_checked (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {ds : List DeclC}
    (fc : FullyChecked μ ds) :
    ∀ c ∈ fc.env.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := fullyChecked_sound V hμ fc
  exact fun c hc hty => no_constant_of_False mp c hc hty

/-- The same letter about the pinned `Empty`. -/
theorem no_proof_of_Empty_checked (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {ds : List DeclC}
    (fc : FullyChecked μ ds) :
    ∀ c ∈ fc.env.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := fullyChecked_sound V hμ fc
  exact fun c hc hty => no_constant_of_Empty mp c hc hty

end ConLeche.Cached
