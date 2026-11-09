module

public import ConLeche.Cached.Decls
public import ConLeche.Model.Fold
public import ConLeche.Verify.Cached.SimC
import ConLeche.Verify.Cached.BridgeC

public section

/-!
# The model along the fold's run

An accepting run of the fold (`DeclsRun`, `ConLeche/Cached/Decls.lean`) from a canonical index whose
environment carries the model carries the model to its end: at each position the model supplies the
well-formedness of the environment the bridge from the executable core takes, the record's check is a
pure `checkDecl` run (`checkDeclStepC_run`), and `declStep_preserves` carries the model across it.

The set theory is a hypothesis although the conclusions of the fold's letters
(`ConLeche/Verify/Cached/MainC.lean`) do not mention it: the model is what supplies that
well-formedness.
-/

namespace ConLeche.Cached

open ConLeche ConLeche.Semantics ConLeche.Model

universe w
variable {V : Type w} [SetTheory V]
variable {pins : List NatOpPinSet}

/-- **One record, with the model**: its check, from a canonical index whose environment carries the
model, leaves the model on the environment it produces and *is* a pure `checkDecl` run at some fuel. -/
theorem checkDeclStepC_model {fe fe₁ : FEnv} {pd : Declaration} {s s₁ : CState}
    (hfe : fe = mkFEnv fe.env) (hm : EnvModelOk V fe.env) (hres : CSOKF s)
    (h : checkDeclStepC .verified pins fe pd s = .ok (fe₁, s₁)) :
    EnvModelOk V fe₁.env ∧ fe₁ = mkFEnv fe₁.env ∧ CSOKF s₁ ∧
      ∃ F, checkDecl .verified (fueledOps .verified F) pins fe.env pd = .ok fe₁.env := by
  obtain ⟨⟨mp, hcov, hS⟩, hE, hN⟩ := hm
  have henv : EnvWF fe.env := mp.toEnvFacts.wf
  rw [hfe] at h
  obtain ⟨hres₁, hcanon, F, hF⟩ := checkDeclStepC_run henv hres h
  exact ⟨declStep_preserves mp hcov hS hE hN (ConLeche.Semantics.checkDeclRun_ofEnvFactsK hF),
    hcanon, hres₁, F, hF⟩

/-- **The model along the run.** -/
theorem declsRun_model {ds : List Declaration} {p q : Nat × FEnv}
    (hrun : DeclsRun .verified pins maxNatSize ds p q) :
    p.2 = mkFEnv p.2.env → EnvModelOk V p.2.env → EnvModelOk V q.2.env := by
  induction hrun with
  | nil p => exact fun _ hm => hm
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hfe hm
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    obtain ⟨hm₁, hfe₁, -⟩ := checkDeclStepC_model hfe hm (CSOKF.fresh _) hstepC
    exact ih hfe₁ hm₁

end ConLeche.Cached
