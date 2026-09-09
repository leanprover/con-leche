module

public import ConLeche.Kernel.CheckerSplit
public import ConLeche.Verify.EnvBound
public import ConLeche.Verify.EnvWF

public section

/-!
# The specification of installed, checked and fully checked
environments (task #253)

The driver separates INSTALLING a declaration from CHECKING it
(`ConLeche/Cached/Installed.lean`), and this module is the SPECIFICATION
of that separation — stated over the pure fueled checker alone: no
driver, no memo state, no `IO`, nothing about *how* an environment was
produced.  The driver's own subtypes (`FullyChecked`, over its
executable steps) reach these by the bridge
(`ConLeche/Verify/Cached/InstalledC.lean`):

* `InstalledSpec μ` — **an environment properly installed**: the
  stream's declaration groups in order, each installed by the pure
  install half of the checker at the environment of the constants
  before it (`InstallTrace`), with name uniqueness and the syntactic
  well-formedness of every group's install environment as the
  invariant.  A separable value declaration (a `defn`, `thm` or
  `opaque` off the pinned names) is installed by `installConstantVal`
  and `installValue` and carries its `ValueGroup`; every other group
  was checked in full by `checkDecl` as it was installed.
* `GroupCheckedSpec e i` — **in a properly installed environment, group
  `i` has been checked**: the pure check half `checkValueGroup`
  succeeds on the group's datum at the PREFIX of `e.env` the group was
  installed at (`Env.prefixTo`).  It reads only that prefix and the
  group's own datum, so it is a proposition workers can establish
  independently of one another.
* `FullyCheckedSpec μ` — the subtype of installed environments every group
  of which is checked, and `FullyCheckedSpec.assemble`: properly installed
  plus every group checked is fully checked.

The consistency theorem on the specification is
`no_proof_of_False_spec` (`ConLeche/Model/Installed.lean`); the driver's
`FullyChecked` and the ordinary fold `checkDecls` both reach it
(`fullyChecked_spec`, `checkDecls_spec`,
`ConLeche/Verify/Cached/InstalledC.lean`).
-/

namespace ConLeche

/-- One installed declaration group: the declaration, the number of
constants installed before it (the counter the two-phase driver checks
it at), and — for a separable value declaration — the datum the check
half needs. -/
structure Group where
  decl : Declaration
  vis : Nat
  value? : Option ValueGroup

/-- One group's install, from `env` to `env₁`, by the pure checker at
fuel `F`: a separable value declaration by the install half, recording
its datum; anything else — and a value declaration the driver chose to
check in full — by `checkDecl`. -/
@[expose] def GroupInstalled (μ : CheckMode) (F : Nat) (env : Env) (g : Group)
    (env₁ : Env) : Prop :=
  g.vis = env.consts.length ∧
  match g.value? with
  | none =>
    (∃ new, env₁.consts = new ++ env.consts) ∧
    checkDecl μ (fueledOps μ F) env g.decl = .ok env₁
  | some vg =>
    match g.decl with
    | .defnDecl cv value hint =>
      (natOpNames.contains cv.name || natDivModNames.contains cv.name) = false ∧
      vg.kind = .defn ∧
      installConstantVal (fueledOps μ F) env cv = .ok vg.cvA ∧
      installValue (fueledOps μ F) env vg.cvA value = .ok vg.jv ∧
      env₁ = ⟨.defnInfo vg.cvA vg.jv hint :: env.consts⟩
    | .thmDecl cv value =>
      vg.kind = .thm ∧
      installConstantVal (fueledOps μ F) env cv = .ok vg.cvA ∧
      installValue (fueledOps μ F) env vg.cvA value = .ok vg.jv ∧
      env₁ = ⟨.thmInfo vg.cvA vg.jv :: env.consts⟩
    | .opaqueDecl cv value =>
      reduceOpNames.contains cv.name = false ∧
      vg.kind = .opaque ∧
      installConstantVal (fueledOps μ F) env cv = .ok vg.cvA ∧
      installValue (fueledOps μ F) env vg.cvA value = .ok vg.jv ∧
      env₁ = ⟨.axiomInfo vg.cvA :: env.consts⟩
    | _ => False

/-- The install trace: the groups installed in order, each at the
environment the previous ones built. -/
@[expose] def InstallTrace (μ : CheckMode) : Env → List Group → Env → Prop
  | env, [], env' => env' = env
  | env, g :: gs, env' =>
    ∃ F env₁, GroupInstalled μ F env g env₁ ∧ InstallTrace μ env₁ gs env'

/-- **A properly installed environment.** -/
structure InstalledSpec (μ : CheckMode) where
  env : Env
  groups : List Group
  trace : InstallTrace μ Env.empty groups env
  nodup : NodupNames env
  /-- Every group's install environment is syntactically well-formed
  (the hypothesis every bridge from the executable core to the pure
  one carries). -/
  wf : ∀ g ∈ groups, EnvWF (env.prefixTo g.vis)
  wfEnd : EnvWF env

/-- **In a properly installed environment, group `i` has been
checked**: the pure check half succeeds on the group's datum at the
prefix of the environment the group was installed at.  A group without
a datum was checked in full at its install. -/
@[expose] def GroupCheckedSpec {μ : CheckMode} (e : InstalledSpec μ) (i : Nat) : Prop :=
  match e.groups[i]? with
  | some g =>
    match g.value? with
    | some vg => ∃ F, checkValueGroup (fueledOps μ F) (e.env.prefixTo g.vis) vg = .ok ()
    | none => True
  | none => True

/-- **A fully checked environment**: properly installed, every group
checked. -/
@[expose] def FullyCheckedSpec (μ : CheckMode) : Type :=
  { e : InstalledSpec μ // ∀ i, GroupCheckedSpec e i }

/-- Properly installed plus every group checked is fully checked. -/
@[expose] def FullyCheckedSpec.assemble {μ : CheckMode} (e : InstalledSpec μ)
    (h : ∀ i, GroupCheckedSpec e i) : FullyCheckedSpec μ := ⟨e, h⟩

/-- The environment of a fully checked environment. -/
@[expose] def FullyCheckedSpec.env {μ : CheckMode} (fc : FullyCheckedSpec μ) : Env := fc.1.env

/-! ## The trace's shape -/

/-- An installed group's environment extends the one it was installed
at. -/
theorem GroupInstalled.extends {μ : CheckMode} {F : Nat} {env : Env} {g : Group}
    {env₁ : Env} (h : GroupInstalled μ F env g env₁) :
    ∃ new, env₁.consts = new ++ env.consts := by
  obtain ⟨d, vis, v?⟩ := g
  obtain ⟨-, h⟩ := h
  cases v? with
  | none => exact h.1
  | some vg =>
    cases d with
    | defnDecl cv value hint =>
      obtain ⟨-, -, -, -, rfl⟩ := h; exact ⟨[_], rfl⟩
    | thmDecl cv value =>
      obtain ⟨-, -, -, rfl⟩ := h; exact ⟨[_], rfl⟩
    | opaqueDecl cv value =>
      obtain ⟨-, -, -, -, rfl⟩ := h; exact ⟨[_], rfl⟩
    | axiomDecl _ => exact h.elim
    | basisDecl _ => exact h.elim
    | indDecl _ _ => exact h.elim

/-- The trace's final environment extends every environment along
it. -/
theorem InstallTrace.extends {μ : CheckMode} :
    ∀ {gs : List Group} {env env' : Env}, InstallTrace μ env gs env' →
      ∃ new, env'.consts = new ++ env.consts
  | [], env, env', h => ⟨[], by rw [show env' = env from h]; rfl⟩
  | g :: gs, env, env', h => by
    obtain ⟨F, env₁, hg, htr⟩ := h
    obtain ⟨new₁, h₁⟩ := hg.extends
    obtain ⟨new₂, h₂⟩ := InstallTrace.extends htr
    exact ⟨new₂ ++ new₁, by rw [h₂, h₁, List.append_assoc]⟩

/-- The prefix of the trace's final environment at a group's counter is
the environment the group was installed at. -/
theorem InstallTrace.prefix_head {μ : CheckMode} {F : Nat} {env env₁ env' : Env}
    {g : Group} {gs : List Group} (hg : GroupInstalled μ F env g env₁)
    (htr : InstallTrace μ env₁ gs env') :
    env'.prefixTo g.vis = env := by
  obtain ⟨new₁, h₁⟩ := hg.extends
  obtain ⟨new₂, h₂⟩ := htr.extends
  rw [hg.1]
  exact Env.prefixTo_of_extends (new := new₂ ++ new₁)
    (by rw [h₂, h₁, List.append_assoc])

end ConLeche
