module

public import ConLeche.Verify.Installed
public import ConLeche.Verify.CheckerSplit
public import ConLeche.Model.Fold

public section

/-!
# The consistency theorem on the specification (task #253)

`FullyCheckedSpec μ` (`ConLeche/Verify/Installed.lean`) is an environment
properly installed with every declaration group checked, by the pure
fueled checker's two halves, and this module is its consistency
letter: such an environment carries the graded model, so no constant of
type `False` (or `Empty`) is stored in it.  The driver's fully checked
environments and the ordinary fold's accepts reach it
(`ConLeche/Verify/Cached/InstalledC.lean`), and the main theorem
(`ConLeche/MainTheorem.lean`) is its corollary on the driver's type.

The proof walks the install trace: an installed group whose check half
succeeded at the prefix it was installed at is a `checkDecl` run
(`checkDecl_of_split_*`, the two halves re-associated at a common fuel),
and `declStep_preserves` carries the model across it.
-/

namespace ConLeche.Model

open ConLeche ConLeche.Semantics

universe w
variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- An installed group whose check half succeeded — at the environment
it was installed at — was checked by `checkDecl` at some fuel. -/
theorem groupInstalled_checkDecl {F : Nat} {env : Env} {g : Group} {env₁ : Env}
    (hg : GroupInstalled μ F env g env₁)
    (hc : ∀ vg, g.value? = some vg →
      ∃ F', checkValueGroup (fueledOps μ F') env vg = .ok ()) :
    ∃ F', checkDecl μ (fueledOps μ F') env g.decl = .ok env₁ := by
  obtain ⟨d, vis, v?⟩ := g
  obtain ⟨-, h⟩ := hg
  cases v? with
  | none => exact ⟨F, h.2⟩
  | some vg =>
    obtain ⟨F', hC⟩ := hc vg rfl
    cases d with
    | defnDecl cv value hint =>
      obtain ⟨hnat, -, hI, hV, rfl⟩ := h
      exact ⟨max F F', checkDecl_of_split_defn hnat
        (installConstantVal_mono (Nat.le_max_left _ _) hI)
        (installValue_mono (Nat.le_max_left _ _) hV)
        (checkValueGroup_mono (Nat.le_max_right _ _) hC)⟩
    | thmDecl cv value =>
      obtain ⟨hk, hI, hV, rfl⟩ := h
      exact ⟨max F F', checkDecl_of_split_thm hk
        (installConstantVal_mono (Nat.le_max_left _ _) hI)
        (installValue_mono (Nat.le_max_left _ _) hV)
        (checkValueGroup_mono (Nat.le_max_right _ _) hC)⟩
    | opaqueDecl cv value =>
      obtain ⟨hred, -, hI, hV, rfl⟩ := h
      exact ⟨max F F', checkDecl_of_split_opaque hred
        (installConstantVal_mono (Nat.le_max_left _ _) hI)
        (installValue_mono (Nat.le_max_left _ _) hV)
        (checkValueGroup_mono (Nat.le_max_right _ _) hC)⟩
    | axiomDecl _ => exact h.elim
    | basisDecl _ => exact h.elim
    | indDecl _ _ => exact h.elim

/-- **The model threads through an install trace** whose every value
group is checked at the prefix it was installed at. -/
theorem installTrace_preserves (hμ : μ.verifiedChecks = true) :
    ∀ (gs : List Group) (env : Env) {env' : Env},
      InstallTrace μ env gs env' →
      (∀ g ∈ gs, ∀ vg, g.value? = some vg →
        ∃ F, checkValueGroup (fueledOps μ F) (env'.prefixTo g.vis) vg = .ok ()) →
      EnvModelOk V μ env → EnvModelOk V μ env'
  | [], env, env', htr, _, hm => by
    rw [show env' = env from htr]; exact hm
  | g :: gs, env, env', htr, hc, hm => by
    obtain ⟨F, env₁, hg, htr'⟩ := htr
    have hpre : env'.prefixTo g.vis = env := InstallTrace.prefix_head hg htr'
    obtain ⟨F', hF⟩ := groupInstalled_checkDecl hg (fun vg hvg => by
      obtain ⟨F₀, h₀⟩ := hc g List.mem_cons_self vg hvg
      rw [hpre] at h₀
      exact ⟨F₀, h₀⟩)
    obtain ⟨⟨mp⟩, hE⟩ := hm
    exact installTrace_preserves hμ gs env₁ htr'
      (fun g' hg' => hc g' (List.mem_cons_of_mem _ hg'))
      (declStep_preserves hμ mp hE (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hF))

/-- **A fully checked environment carries the model.** -/
theorem fullyCheckedSpec_sound (hμ : μ.verifiedChecks = true) (fc : FullyCheckedSpec μ) :
    Nonempty (EnvModelM V μ fc.env) := by
  refine (installTrace_preserves hμ fc.1.groups Env.empty fc.1.trace ?_
    ⟨⟨EnvModelM.empty V μ⟩, EtaFamiliesClosed.empty⟩).1
  intro g hg vg hvg
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hg
  have h := fc.2 i
  unfold GroupCheckedSpec at h
  rw [hi] at h
  simp only at h
  rw [hvg] at h
  exact h

/-- **THE CONSISTENCY THEOREM ON FULLY CHECKED ENVIRONMENTS**: an
environment properly installed and checked group by group, in a
validating mode, stores no constant of type `False`.  Hypotheses are
the subtype's invariant and nothing else; every driver's letter is a
corollary. -/
theorem no_proof_of_False_spec (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) (fc : FullyCheckedSpec μ) :
    ∀ c ∈ fc.env.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := fullyCheckedSpec_sound (V := V) hμ fc
  exact fun c hc hty => no_constant_of_False mp c hc hty

/-- The same letter about the pinned `Empty`. -/
theorem no_proof_of_Empty_spec (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) (fc : FullyCheckedSpec μ) :
    ∀ c ∈ fc.env.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := fullyCheckedSpec_sound (V := V) hμ fc
  exact fun c hc hty => no_constant_of_Empty mp c hc hty

end ConLeche.Model
