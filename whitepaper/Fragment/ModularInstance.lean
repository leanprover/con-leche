module

public import Fragment.ModularModel
public import Fragment.ModularSemantics
public import Fragment.InstallNest

@[expose] public section

/-!
# The fragment's model as a modular semantics

The fragment's consistency proof, packaged as an instance of the
interface of `ModularSemantics.lean` (`fragmentSemantics`), and the
modular theorem (`modular`) read off the generic one
(`Development.modular`).

* **Environments** are the fragment's environments; a **model** is a
  `BlockModel` in which proofs are the point (`ProofsPt`), its **value**
  at a name the name's set at every list of levels, and **the value of
  every proof** the point.
* **Assembly** is `Assembled` (`ModularModel.lean`), **amalgamation**
  its model (`Assembled.model`, `Assembled.proofsPt`).
* **Proofs**: `ProofIn C E n`, the checker's inference at `C` that the
  type of `E`'s `n` is a proposition, and `ProofBy C E E' n`, a copy of
  the type of `E'`'s `n`, which `E'` infers to be a proposition itself;
  a model keeping proofs the point gives such a constant the point
  (`ProofIn.eq_dflt`, `ProofBy.eq_dflt`).
* **The step** is the installation of a checked list
  (`Checks.blockModel`): every constant of the context keeps its set,
  and proofs stay the point.

A development of modules (`Module`) is a development over the instance
(`toDev`), and a validated module is a valid one (`toDev_valid`): the
local checks are checks of one module and its imports' views.
-/

namespace Fragment

open SetLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

/-! ## The instance -/

/-- **Acceptance**: the checked list over a closed context. -/
def FAccepts (Γ : Env) (D : List Decl) (Γ' : Env) : Prop :=
  Γ' = applyAll D Γ ∧ Checks Γ D ∧ Env.Scoped Γ

/-- **The step**: a model of the context extends to one of the own
environment, keeping every name of the context with its set, and
proofs the point. -/
theorem FAccepts.step {Γ Γ' : Env} {D : List Decl} (h : FAccepts Γ D Γ')
    (m : BlockModel V Γ) (hp : ProofsPt Γ m.M) : ∃ m' : BlockModel V Γ', ProofsPt Γ' m'.M ∧
      ∀ n, (Γ.find? n).isSome = true → (Γ'.find? n).isSome = true ∧ m'.M n = m.M n := by
  obtain ⟨rfl, hc, hs⟩ := h
  obtain ⟨m', hag, hp'⟩ := hc.blockModel hs m hp
  exact ⟨m', hp', fun n hn => ⟨isSome_find?_applyAll hn D, funext (hag n hn)⟩⟩

variable (V) in
/-- **The fragment's model as a modular semantics.** -/
@[reducible] noncomputable def fragmentSemantics : ModularSemantics.{0, u} where
  Env := Env
  Name := Name
  Stores E n := (E.find? n).isSome = true
  Mod E := { m : BlockModel V E // ProofsPt E m.M }
  Val := List Nat → V
  val m n := m.1.M n
  proofVal := dflt
  Assembled C _ E := Assembled C E
  assembled_src h n hn := by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨i, ci', hf', -⟩ := h.le n ci hci
    exact ⟨i, by rw [hf']; rfl⟩
  amalgamate h m hc := by
    obtain ⟨mC, hmC⟩ := h.model (fun i => (m i).1) fun n i i' => hc i i' n
    exact ⟨⟨mC, h.proofsPt _ (fun i => (m i).2) mC.M hmC⟩, fun i n hn _ hs => hmC n i hn hs⟩
  ProofIn := ProofIn
  proof_val h mC m hag := h.eq_dflt mC.1.toEnvModel m.1.M m.2 fun c hC hE => hag c hC hC hE
  ProofBy := ProofBy
  proofBy_val h mC m m' hag hag' := h.eq_dflt mC.1.M m.1.M m'.1.toEnvModel m.2
    (fun c hC hE => hag c hC hC hE) fun c hC hE => hag' c hC hC hE
  Decls := List Decl
  Accepts := FAccepts
  step h m := by
    obtain ⟨m', hp', hm'⟩ := h.step m.1 m.2
    exact ⟨⟨m', hp'⟩, hm'⟩

/-! ## A development of modules, over the instance -/

variable (V) in
/-- **The development**, over the fragment's semantics. -/
def toDev (dev : Nat → Module) : Development (fragmentSemantics V) where
  ctx i := (dev i).context
  decls i := (dev i).decls
  own i := (dev i).own
  sources i := sources dev i
  src i := (dev i).src
  rank i := (dev i).rank
  part i := (dev i).part

theorem Valid.importOk {dev : Nat → Module} {j : Nat} (h : Valid dev j) : ImportOk dev j := by
  rcases h with h | h
  · exact h.importOk
  · exact h.importOk

theorem Valid.iface {dev : Nat → Module} {j : Nat} (h : Valid dev j) : InterfaceOk dev j := by
  rcases h with h | h
  · exact h.iface
  · exact h.iface

/-- **A validated module, its imports validated, is valid over the
instance.** -/
theorem toDev_valid (dev : Nat → Module) (i : Nat) (hv' : ∀ j ≤ i, Valid dev j) :
    (toDev V dev).Valid i := by
  have hv := hv' i (Nat.le_refl i)
  have hi := hv.importOk
  refine ⟨fun x hx => ?_, hi.reads.1, fun n hn => ?_, ?_⟩
  · obtain ⟨hj, hE⟩ := mem_sources.mp hx
    exact ⟨hi.imports _ hj, (hv' _ (Nat.le_of_lt (hi.imports _ hj))).iface _ hE⟩
  · have r := hi.reads.2 n hn
    exact ⟨r.read, r.part, r.below, r.agree⟩
  · rcases hv with h | h
    · exact .inl ⟨rfl, h.checks, h.importOk.reads.1.scoped⟩
    · exact .inr h.own

/-! ## The theorem -/

variable (V) in
/-- **Modular checking** (the theorem): if every module below `k` is
validated, there is a family of models, one of each module's own
environment, that is **compatible**: every module gives each name of
its context the set the module it is read from gives it, and every
proof (a constant the module's own environment infers to be a
proposition) the point.  It is the generic theorem
(`Development.modular`) at the fragment's semantics. -/
theorem modular (dev : Nat → Module) (k : Nat) (h : ∀ i < k, Valid dev i) :
    ∃ m : (i : Nat) → i < k → BlockModel V (dev i).own,
      (∀ j (hj : j < k) n, ((dev j).context.find? n).isSome = true →
        ∃ h : (dev j).src n < k, (m j hj).M n = (m ((dev j).src n) h).M n) ∧
      ∀ j (hj : j < k) n, ProofIn (dev j).own (dev j).own n → ∀ ls, (m j hj).M n ls = pt := by
  obtain ⟨m, hc⟩ := (toDev V dev).modular k fun i hi =>
    toDev_valid dev i fun j hj => h j (Nat.lt_of_le_of_lt hj hi)
  refine ⟨fun i hi => (m i hi).1, fun j hj n hn => ?_, fun j hj n hp ls => ?_⟩
  · obtain ⟨h', he, -⟩ := hc j hj n hn
    exact ⟨h', he⟩
  · exact congrFun (hp.eq_dflt (m j hj).1.toEnvModel (m j hj).1.M (m j hj).2 fun _ _ _ => rfl) ls

variable (V) in
/-- **Every validated module's own environment has a model.** -/
theorem modular_model (dev : Nat → Module) (i : Nat) (h : ∀ j ≤ i, Valid dev j) :
    Nonempty (BlockModel V (dev i).own) := by
  obtain ⟨m, -⟩ := modular V dev (i + 1) fun j hj => h j (Nat.le_of_lt_succ hj)
  exact ⟨m i (Nat.lt_succ_self i)⟩

variable (V) in
include V in
/-- **No closed term of a module inhabits an empty proposition** that
its own environment stores. -/
theorem modular_no_empty_prop_inhabitant (dev : Nat → Module) (i : Nat) (h : ∀ j ≤ i, Valid dev j)
    {name recName elim : Name}
    (hrec : (dev i).own.find? recName = some (IndSpec.falseSpec name recName elim).recInfo)
    (e : Expr) : ¬ Infer (dev i).own [] e (.const name []) := by
  obtain ⟨m⟩ := modular_model V dev i h
  exact no_empty_inductive_inhabitant_of_model V m.toEnvModel
    (S := IndSpec.falseSpec name recName elim) rfl rfl rfl rfl hrec e

variable (V) in
/-- **Every statement a module stores holds in its model** — in
particular every assumption of a compared module (a hole): its type,
at every instantiation, has a member. -/
theorem modular_statements_hold (dev : Nat → Module) (i : Nat) (h : ∀ j ≤ i, Valid dev j) :
    ∃ m : BlockModel V (dev i).own, ∀ c ci, (dev i).own.find? c = some ci →
      ∀ (φ : Name → Nat) (ρ : Nat → V) (ls : List Level), ls.length = ci.lparams.length →
        ∃ x, x ∈ˢ interp m.M φ ρ (ci.type.instL ci.lparams ls) := by
  obtain ⟨m⟩ := modular_model V dev i h
  exact ⟨m, fun c ci hf φ ρ ls hls => ⟨_, (m.type_ok c ci hf φ ρ ls hls).2.2⟩⟩

end Fragment
