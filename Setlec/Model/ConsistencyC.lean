import Setlec.Model.Consistency
import Setlec.Verify.BridgeWFDecl

/-!
# Consistency of the executable checker

The executable runs the memoized knot unconditionally — there is no
runtime well-formedness gate.  The refinement bridge's per-declaration
lemma (`checkDecl_bridge`, `Setlec/Model/BridgeWF.lean`) reproduces a
successful cached `checkDecl` step by the pure fueled checker under
`EnvWF` of the step's input environment, and that hypothesis is exactly
a field of the environment model invariant (`EnvModel.wf`).  So the
declaration fold below interleaves the two: at each step the current
model supplies `EnvWF`, the bridge supplies the pure run, and
`checkDecl_sound` supplies the next model.  Every consistency statement
transfers to the executable with no hypothesis beyond its acceptance.
-/

namespace Setlec

variable {mode : CheckMode}

/-- The declaration fold of the executable checker preserves having a
model: per step, `EnvWF` from the model feeds the bridge, the bridged
pure run feeds `checkDecl_sound`. -/
private theorem foldlM_soundC {V : Type u} [SetTheory V] :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvModel V env) →
      EtaFamiliesClosed env →
      ds.foldlM (checkDecl mode (cachedOps mode)) env = .ok env' →
      Nonempty (EnvModel V env')
  | [], env, env', hm, _, h => by
    have h' : (Except.ok env : CheckM Env) = Except.ok env' := h
    cases h'
    exact hm
  | d :: ds, env, env', hm, hE1, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl mode (cachedOps mode) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      obtain ⟨F, hF⟩ := checkDecl_bridge m.wf hd
      obtain ⟨hm1, hE1'⟩ := checkDecl_sound hF m hE1
      exact foldlM_soundC ds env1 hm1 hE1' h

/-- Soundness of the **executable** checker: every environment it
accepts has a set-theoretic model. -/
theorem checkDeclsC_sound (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls mode (cachedOps mode) ds = .ok env') :
    Nonempty (EnvModel V env') :=
  foldlM_soundC ds Env.empty ⟨EnvModel.empty V⟩
    EtaFamiliesClosed.empty h

/-- The executable checker never accepts a declaration list containing
a `def` or `theorem` whose stated type is `Empty`. -/
theorem no_proof_of_Empty_input_C (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls mode (cachedOps mode) ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False := by
  suffices hgen : ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvModel V env) →
      EtaFamiliesClosed env →
      ds.foldlM (checkDecl mode (cachedOps mode)) env = .ok env' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False by
    exact hgen ds Env.empty ⟨EnvModel.empty V⟩ EtaFamiliesClosed.empty
      h hd
  intro ds
  induction ds with
  | nil =>
    intro env env' _ _ _ hd
    rcases hd with hd | hd <;> cases hd
  | cons d ds ih =>
    intro env env' hm hE1 h hd
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl mode (cachedOps mode) env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
      rw [hdd] at h
      obtain ⟨m⟩ := hm
      obtain ⟨F, hF⟩ := checkDecl_bridge m.wf hdd
      by_cases hdis : d = Declaration.defnDecl cv value hint ∨
          d = Declaration.thmDecl cv value
      · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis
        rw [hty] at hann
        obtain rfl : Expr.const emptyName [] = type := by
          have h1 : annotateCore mode env F 0 (.const emptyName []) =
              .ok type := hann
          cases F with
          | zero =>
            rw [annotateCore_zero] at h1
            simp [throw, throwThe, MonadExceptOf.throw] at h1
          | succ F' =>
            rw [annotateCore_succ] at h1
            simpa [annotateBody, pure, Except.pure] using h1
        obtain ⟨⟨m1⟩, -⟩ := checkDecl_sound hF m hE1
        exact no_constant_of_Empty m1 c hc (by rw [hcv])
      · have hd' : Declaration.defnDecl cv value hint ∈ ds ∨
            Declaration.thmDecl cv value ∈ ds := by
          rcases hd with hd | hd
          · rcases List.mem_cons.mp hd with rfl | hmem
            · exact absurd (Or.inl rfl) hdis
            · exact Or.inl hmem
          · rcases List.mem_cons.mp hd with rfl | hmem
            · exact absurd (Or.inr rfl) hdis
            · exact Or.inr hmem
        obtain ⟨hm1, hE1'⟩ := checkDecl_sound hF m hE1
        exact ih env1 hm1 hE1' h hd'

/-- **No proof of `Empty` is ever accepted by the executable
checker**: if it accepts a declaration list, no constant in the
resulting environment has type `Empty`. -/
theorem no_proof_of_Empty_C (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls mode (cachedOps mode) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsC_sound V h
  exact no_constant_of_Empty m c hc hty

end Setlec
