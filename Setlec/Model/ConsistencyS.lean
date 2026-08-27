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

variable {mode : CheckMode}

/-- The declaration fold of the shared-state checker preserves having
a model (the threaded index stays `mkFEnv`-shaped along the fold). -/
private theorem foldlM_soundS {V : Type u} [SetTheory V] :
    ∀ (ds : List Declaration) (fe : FEnv) {fe' : FEnv},
      fe = mkFEnv fe.env →
      Nonempty (EnvModel V fe.env) →
      EtaFamiliesClosed fe.env →
      ds.foldlM (checkDeclSharedF mode) fe = .ok fe' →
      Nonempty (EnvModel V fe'.env)
  | [], fe, fe', _, hm, _, h => by
    have h' : (Except.ok fe : CheckM FEnv) = Except.ok fe' := h
    cases h'
    exact hm
  | d :: ds, fe, fe', hfe, hm, hE1, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDeclSharedF mode fe d with
    | error e => rw [hd] at h; exact nomatch h
    | ok fe1 =>
      rw [hd] at h
      obtain ⟨m⟩ := hm
      rw [hfe] at hd
      obtain ⟨hfe1, F, hF⟩ := checkDeclSharedF_bridge m.wf hd
      obtain ⟨hm1, hE1'⟩ := checkDecl_sound hF m hE1
      exact foldlM_soundS ds fe1 hfe1 hm1 hE1' h

/-- Soundness of the **shared-state executable** checker: every
environment it accepts has a set-theoretic model. -/
theorem checkDeclsS_sound (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared mode ds = .ok env') :
    Nonempty (EnvModel V env') := by
  unfold checkDeclsShared at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : ds.foldlM (checkDeclSharedF mode) (mkFEnv Env.empty) with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    exact foldlM_soundS ds (mkFEnv Env.empty) rfl ⟨EnvModel.empty V⟩
      EtaFamiliesClosed.empty hf

/-- The shared-state executable never accepts a declaration list
containing a `def` or `theorem` whose stated type is `Empty`. -/
theorem no_proof_of_Empty_input_S (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared mode ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False := by
  suffices hgen : ∀ (ds : List Declaration) (fe : FEnv) {fe' : FEnv},
      fe = mkFEnv fe.env →
      Nonempty (EnvModel V fe.env) →
      EtaFamiliesClosed fe.env →
      ds.foldlM (checkDeclSharedF mode) fe = .ok fe' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False by
    unfold checkDeclsShared at h
    simp only [Bind.bind, Except.bind] at h
    cases hf : ds.foldlM (checkDeclSharedF mode) (mkFEnv Env.empty) with
    | error e => rw [hf] at h; exact nomatch h
    | ok fe =>
      exact hgen ds (mkFEnv Env.empty) rfl ⟨EnvModel.empty V⟩
        EtaFamiliesClosed.empty hf hd
  intro ds
  induction ds with
  | nil =>
    intro fe fe' _ _ _ _ hd
    rcases hd with hd | hd <;> cases hd
  | cons d ds ih =>
    intro fe fe' hfe hm hE1 h hd
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDeclSharedF mode fe d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok fe1 =>
      rw [hdd] at h
      obtain ⟨m⟩ := hm
      rw [hfe] at hdd
      obtain ⟨hfe1, F, hF⟩ := checkDeclSharedF_bridge m.wf hdd
      by_cases hdis : d = Declaration.defnDecl cv value hint ∨
          d = Declaration.thmDecl cv value
      · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis
        rw [hty] at hann
        obtain rfl : Expr.const emptyName [] = type := by
          have h1 : annotateCore mode fe.env F 0 (.const emptyName []) =
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
        exact ih fe1 hfe1 hm1 hE1' h hd'

/-- **No proof of `Empty` is ever accepted by the shared-state
executable checker**: if it accepts a declaration list, no constant in
the resulting environment has type `Empty`. -/
theorem no_proof_of_Empty_S (V : Type u) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared mode ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsS_sound V h
  exact no_constant_of_Empty m c hc hty

end Setlec
