module

public import ConLeche.Verify.Cached.InstalledC
public import ConLeche.Model.Fold
public import ConLeche.Verify.Cached.PushChain
import ConLeche.Verify.CheckerSplit
import ConLeche.Verify.Cached.BridgeC

public section

/-!
# The model along the install run, and the letters on the fully checked environment

The model-level half of the walk over phase A's accepting run
(`InstallRun`, `ConLeche/Cached/Installed.lean`); the simulation lemmas
it steps with — phase A's install halves and the record check at the
prefix view — are model-free and live in
`ConLeche/Verify/Cached/InstalledC.lean`.

* `installRun_model` — the walk: at each position the model supplies
  the well-formedness of the environment every bridge from the
  executable core takes; an ordinary step is a `checkDecl` run by
  `checkDeclStepC_run`, a separable value declaration is the two halves
  re-associated into a `checkDecl` run (`checkDecl_of_split_*`,
  `ConLeche/Verify/CheckerSplit.lean`) with the record's check consumed
  at the position that produced it; `declStep_preserves` carries the
  model across either.
* `fullyChecked_sound` / `no_proof_of_False_checked` /
  `no_proof_of_Empty_checked` — the letters on the fully checked
  environment the driver assembles.  The
  fold's letters (`ConLeche/Verify/Cached/MainC.lean`) are these under
  `checkDecls_fullyChecked`.

The set theory is a hypothesis of every walk although the letters'
conclusions do not mention it: the model is what supplies the
well-formedness the bridges need.
-/

namespace ConLeche.Cached

open ConLeche ConLeche.Semantics ConLeche.Model

universe w
variable {V : Type w} [SetTheory V] {μ : CheckMode}
variable {pins : List NatOpPinSet}

/-! ## The model along the run -/

set_option maxHeartbeats 2000000 in
/-- **One step of the run, with the model**: the cons case of
`installRun_model`, as a lemma of its own — phase A's step at a record,
from a canonical index whose environment carries the model, leaves the
model on the environment it produces, keeps the memo residue, and *is*
a pure `checkDecl` run at some fuel.  The last conjunct is what a walk
that wants to know WHAT was installed reads
(`ConLeche/Model/StreamConsts.lean`); `installRun_model` itself
uses only the first two.

The hypotheses about the run's final index (`q`) are the ones a
separable value declaration needs: phase A installs its header and
records the value group, and the group's own check — run at the FINAL
environment, from a fresh memo state — is what the model step consumes. -/
theorem annotStepC_model (hμ : μ.verifiedChecks = true)
    {i : Nat} {fe fe₁ : FEnv} {pend pend₁ : Array PendingCheck} {pd : Declaration}
    {s s₁ : CState} {q : Nat × FEnv × Array PendingCheck} {new₁ : List PendingCheck}
    (hfe : fe = mkFEnv fe.env) (hfe₁ : fe₁ = mkFEnv fe₁.env)
    (hm : EnvModelOk V μ fe.env) (hresA : CSOKF s)
    (hstepC : annotStepC μ pins i fe pend pd s = .ok ((fe₁, pend₁), s₁))
    (hchainF : PushChain fe₁.env q.2.1)
    (hpend₁ : q.2.2.toList = pend₁.toList ++ new₁)
    (hnd : NodupNames q.2.1.env)
    (hB : ∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) :
    EnvModelOk V μ fe₁.env ∧ CSOKF s₁ ∧
      ∃ F, checkDecl μ (fueledOps μ F) pins fe.env pd = .ok fe₁.env := by
    obtain ⟨⟨mp, hcov⟩, hE⟩ := hm
    have henv : EnvWF fe.env := mp.toEnvFacts.wf
    -- the ordinary step: a declaration checked in full at its install
    have ordinary : ∀ (pd' : Declaration),
        (checkDeclStepC μ pins fe pd' >>= fun fe' => pure (fe', pend)) s = .ok ((fe₁, pend₁), s₁) →
        EnvModelOk V μ fe₁.env ∧ CSOKF s₁ ∧
          ∃ F, checkDecl μ (fueledOps μ F) pins fe.env pd' = .ok fe₁.env := by
      intro pd' hst
      obtain ⟨fe₁', s₁', hstepC', hp⟩ := bindC_ok hst
      obtain ⟨hv, rfl⟩ := pureC_ok hp
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      rw [hfe] at hstepC'
      obtain ⟨hres₁, -, F, hF⟩ := checkDeclStepC_run hμ henv hresA hstepC'
      exact ⟨declStep_preserves hμ mp hcov hE
          (ConLeche.Semantics.checkDeclRun_ofEnvFactsK hF), hres₁, F, hF⟩
    -- a separable value declaration: phase A's install (its facts
    -- given), phase B's check at the prefix view
    have value : ∀ (kind : ValueKind) (mk : ConstantVal → Expr → ConstantInfo)
        (d : Declaration) (cvA : ConstantVal) (jv : Expr),
        pd = d →
        CSOKF s₁ →
        fe₁ = fe.push (mk cvA jv) →
        pend₁ = pend.push ⟨⟨kind, cvA, jv⟩, i, fe.visibleBelow⟩ →
        Expr.WScoped 0 cvA.type →
        (kind ≠ .thm → Expr.WScoped 0 jv) →
        (∀ F, checkValueGroup (fueledOps μ F) fe.env ⟨kind, cvA, jv⟩ = .ok () →
          ∃ F', checkDecl μ (fueledOps μ F') pins fe.env d = .ok ⟨mk cvA jv :: fe.env.consts⟩) →
        EnvModelOk V μ fe₁.env ∧ CSOKF s₁ ∧
          ∃ F, checkDecl μ (fueledOps μ F) pins fe.env pd = .ok fe₁.env := by
      intro kind mk d cvA jv hdrel hres₁ hfe₁' hpend₁' hwty hwv hsplit
      subst hfe₁' hpend₁'
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
      obtain ⟨-, F₂, hC⟩ := checkPending_run hμ henv
        (pc := ⟨⟨kind, cvA, jv⟩, i, fe.visibleBelow⟩) (by rw [hvis]; exact hfind)
        hwty hwv CSOKF.empty hchk
      -- the two halves are the declaration's check
      obtain ⟨F', hF⟩ := hsplit F₂ hC
      have hm₁ : EnvModelOk V μ (fe.push (mk cvA jv)).env :=
        declStep_preserves hμ mp hcov hE (ConLeche.Semantics.checkDeclRun_ofEnvFactsK hF)
      exact ⟨hm₁, hres₁, F', hdrel ▸ hF⟩
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
        rw [hfe] at hval
        obtain ⟨hres₁, hcvA, hwty, hwv, F₁, hI, hV⟩ := annotValueC_run hμ henv hresA hval
        refine value .defn (fun cvA jv => .defnInfo cvA jv hint)
          (.defnDecl cv val hint) cvA jv rfl
          hres₁ rfl rfl (by rw [hcvA]; exact hwty)
          (fun _ => hwv) ?_
        intro F hC
        have hnat' : (natOpNames.contains cv.name || natDivModNames.contains cv.name) = false :=
          Bool.not_eq_true _ ▸ hnat
        exact ⟨max F₁ F, checkDecl_of_split_defn hnat' rfl
          (installConstantVal_mono (Nat.le_max_left _ _) hI)
          (installValue_mono (Nat.le_max_left _ _) hV)
          (checkValueGroup_mono (Nat.le_max_right _ _) hC)⟩
    | thmDecl cv val =>
      -- phase A installed the header alone: the flush, the header's
      -- install half, the type record, the push of the RAW value
      unfold annotStepC at hstepC
      simp only [] at hstepC
      obtain ⟨u₀, s₁', hflush, h⟩ := bindC_ok hstepC
      rw [flushC_run] at hflush
      injection hflush with hflush
      obtain rfl : s.flushed = s₁' := congrArg Prod.snd hflush
      obtain ⟨pr, s₂, hcv, h⟩ := bindC_ok h
      obtain ⟨cvA, jty⟩ := pr
      rw [hfe] at hcv
      obtain ⟨hs₂, hcvA, hwty, F₁, hI⟩ :=
        annotConstantValC_run hμ henv (flushC_csok hresA) hcv
      obtain ⟨u₁, s₃, hrec, h⟩ := bindC_ok h
      obtain ⟨hs₃, -⟩ := recordCConst_eff (val := none) hs₂ (by rw [hcvA]; rfl)
        (fun _ _ hv => nomatch hv) u₁ s₃ hrec
      obtain ⟨hv, rfl⟩ := pureC_ok h
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      refine value .thm (fun cvA v => .thmInfo cvA v) (.thmDecl cv val) cvA val
        rfl
        hs₃.residue rfl rfl (by rw [hcvA]; exact hwty) (fun h => absurd rfl h) ?_
      intro F hC
      exact ⟨max F₁ F, checkDecl_of_split_thm rfl
        (installConstantVal_mono (Nat.le_max_left _ _) hI) rfl
        (checkValueGroup_mono (Nat.le_max_right _ _) hC)⟩
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
        rw [hfe] at hval
        obtain ⟨hres₁, hcvA, hwty, hwv, F₁, hI, hV⟩ := annotValueC_run hμ henv hresA hval
        refine value .opaque (fun cvA _ => .axiomInfo cvA) (.opaqueDecl cv val)
          cvA jv rfl
          hres₁ rfl rfl (by rw [hcvA]; exact hwty) (fun _ => hwv) ?_
        intro F hC
        have hred' : reduceOpNames.contains cv.name = false := Bool.not_eq_true _ ▸ hred
        exact ⟨max F₁ F, checkDecl_of_split_opaque hred' rfl
          (installConstantVal_mono (Nat.le_max_left _ _) hI)
          (installValue_mono (Nat.le_max_left _ _) hV)
          (checkValueGroup_mono (Nat.le_max_right _ _) hC)⟩
    | axiomDecl cv => unfold annotStepC at hstepC; exact ordinary _ hstepC
    | basisDecl kind => unfold annotStepC at hstepC; exact ordinary _ hstepC
    | quotDecl k cv => unfold annotStepC at hstepC; exact ordinary _ hstepC
    | indDecl block nP => unfold annotStepC at hstepC; exact ordinary _ hstepC

/-- **The model along the run**: phase A's accepting run from a
canonical index whose environment carries the model, with every record
of the final index checked from a fresh memo state, carries the model
to the final environment.  (The model at each position supplies the
well-formedness of the environment every bridge from the executable
core takes; the records' checks are consumed at the positions that
produced them.)  A theorem's record holds its RAW value: phase A
installed the header alone, and phase B's check — which annotates the
value — is what the theorem's model step consumes. -/
theorem installRun_model (hμ : μ.verifiedChecks = true) {ds : List Declaration}
    {p : Nat × FEnv × Array PendingCheck}
    {q : Nat × FEnv × Array PendingCheck}
    (hrun : InstallRun μ pins ds p q) :
    p.2.1 = mkFEnv p.2.1.env → EnvModelOk V μ p.2.1.env →
    NodupNames q.2.1.env →
    (∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) →
    EnvModelOk V μ q.2.1.env := by
  induction hrun with
  | nil p => exact fun _ hm _ _ => hm
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hfe hm hnd hB
    obtain ⟨i, fe, pend⟩ := p
    obtain ⟨fe₁, pend₁, s₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    simp only at hfe hstepC
    obtain ⟨hpush₁, -⟩ :=
      annotStepC_push μ i (PushChain.self hfe) pend pd {} (fe₁, pend₁) s₁ hstepC
    have hfe₁ : fe₁ = mkFEnv fe₁.env := hpush₁.canon
    obtain ⟨hchainF, new₁, hpend₁⟩ := installRun_trace μ rest (PushChain.self hfe₁)
    obtain ⟨hm₁, -⟩ :=
      annotStepC_model hμ hfe hfe₁ hm CSOKF.empty hstepC hchainF hpend₁ hnd hB
    exact ih hfe₁ hm₁ hnd hB

/-! ## The letters on the fully checked environment -/

/-- **A fully checked environment carries the model.**  The set theory
is a hypothesis because the walk threads the model for the
well-formedness it needs; the conclusion is the model itself. -/
theorem fullyChecked_sound (V : Type w) [SetTheory V] (hμ : μ.verifiedChecks = true)
    {ds : List Declaration} (fc : FullyChecked μ pins ds) :
    Nonempty (EnvModelM V μ fc.env) := by
  obtain ⟨n, r⟩ := fc.1.run
  have hchain := installRun_trace μ r (PushChain.refl Env.empty)
  exact (installRun_model (V := V) hμ r rfl EnvModelOk.empty
    (hchain.1.2.2 List.nodup_nil) fc.records).nonempty

/-- **Coverage on the fully checked environment**: every
stored inductive but `Quot` is a member of a recorded lfp block. -/
theorem fullyChecked_cover (V : Type w) [SetTheory V] (hμ : μ.verifiedChecks = true)
    {ds : List Declaration} (fc : FullyChecked μ pins ds) :
    ∃ mp : EnvModelM V μ fc.env, LfpCover mp [] := by
  obtain ⟨n, r⟩ := fc.1.run
  have hchain := installRun_trace μ r (PushChain.refl Env.empty)
  exact (installRun_model (V := V) hμ r rfl EnvModelOk.empty
    (hchain.1.2.2 List.nodup_nil) fc.records).1

/-- **The letter on the fully checked environment**: such an environment, in
a validating mode, holds no constant of type `False`.  The step the main
corollary rests on (`ConLeche/MainTheorem.lean`, about `checkDecls`) is
this under `checkDecls_fullyChecked`. -/
theorem no_proof_of_False_checked (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {ds : List Declaration}
    (fc : FullyChecked μ pins ds) :
    ∀ c ∈ fc.env.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := fullyChecked_sound V hμ fc
  exact fun c hc hty => no_constant_of_False mp c hc hty

/-- The same letter about the pinned `Empty`. -/
theorem no_proof_of_Empty_checked (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {ds : List Declaration}
    (fc : FullyChecked μ pins ds) :
    ∀ c ∈ fc.env.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := fullyChecked_sound V hμ fc
  exact fun c hc hty => no_constant_of_Empty mp c hc hty

end ConLeche.Cached
