import Setlec.Model.Consistency
import Setlec.Model.BridgeS

/-!
# Consistency of the shared-state executable checker (task #51)

The binary runs `checkDeclsShared`: one interned state per declaration
(`Setlec/Kernel/CheckerS.lean`).  The per-declaration bridge
(`checkDeclShared_bridge`, `Setlec/Model/BridgeS.lean`) reproduces a
successful shared-state step by the pure fueled checker under `EnvWF`
of the step's input environment — a field of the environment model
invariant — so the declaration fold interleaves exactly as in
`Setlec/Model/ConsistencyC.lean`: the current model supplies `EnvWF`,
the bridge supplies the pure run, `checkDecl_sound` supplies the next
model.  Every consistency statement transfers to the shared-state
executable with no hypothesis beyond its acceptance.
-/

namespace Setlec

/-- The declaration fold of the shared-state checker preserves having
a model. -/
private theorem foldlM_soundS {V : Type u} [SetTheory V] :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvModel V env) →
      ds.foldlM checkDeclShared env = .ok env' →
      Nonempty (EnvModel V env')
  | [], env, env', hm, h => by
    have h' : (Except.ok env : CheckM Env) = Except.ok env' := h
    cases h'
    exact hm
  | d :: ds, env, env', hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDeclShared env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      obtain ⟨F, hF⟩ := checkDeclShared_bridge m.wf hd
      exact foldlM_soundS ds env1 (checkDecl_sound hF m) h

/-- Soundness of the **shared-state executable** checker: every
environment it accepts has a set-theoretic model. -/
theorem checkDeclsS_sound (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared ds = .ok env') :
    Nonempty (EnvModel V env') :=
  foldlM_soundS ds Env.empty ⟨EnvModel.empty V⟩ h

/-- The shared-state executable never accepts a declaration list
containing a `def` or `theorem` whose stated type is `Empty`. -/
theorem no_proof_of_Empty_input_S (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False := by
  suffices hgen : ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvModel V env) →
      ds.foldlM checkDeclShared env = .ok env' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False by
    exact hgen ds Env.empty ⟨EnvModel.empty V⟩ h hd
  intro ds
  induction ds with
  | nil =>
    intro env env' _ _ hd
    rcases hd with hd | hd <;> cases hd
  | cons d ds ih =>
    intro env env' hm h hd
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDeclShared env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
      rw [hdd] at h
      obtain ⟨m⟩ := hm
      obtain ⟨F, hF⟩ := checkDeclShared_bridge m.wf hdd
      by_cases hdis : d = Declaration.defnDecl cv value hint ∨
          d = Declaration.thmDecl cv value
      · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis
        rw [hty] at hann
        obtain rfl : Expr.const emptyName [] = type := by
          have h1 : annotateCore env F 0 (.const emptyName []) =
              .ok type := hann
          cases F with
          | zero =>
            rw [annotateCore_zero] at h1
            simp [throw, throwThe, MonadExceptOf.throw] at h1
          | succ F' =>
            rw [annotateCore_succ] at h1
            simpa [annotateBody, pure, Except.pure] using h1
        obtain ⟨m1⟩ := checkDecl_sound hF m
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
        exact ih env1 (checkDecl_sound hF m) h hd'

/-- **No proof of `Empty` is ever accepted by the shared-state
executable checker**: if it accepts a declaration list, no constant in
the resulting environment has type `Empty`. -/
theorem no_proof_of_Empty_S (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsS_sound V h
  exact no_constant_of_Empty m c hc hty

end Setlec
