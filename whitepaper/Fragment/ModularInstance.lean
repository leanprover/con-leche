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
  `BlockModel`, its **value** at a name the name's set at every list
  of levels, and **the value of every proof** the point.
* **Assembly** is `Assembled` (`ModularModel.lean`), **amalgamation**
  its model (`Assembled.model`).
* **The step** is the installation of a checked list
  (`Checks.blockModel`): every constant of the context keeps its set,
  and every flagged proof's set is the point.

A development of modules (`Module`) is a development over the instance
(`toDev`), and a validated module is a valid one (`toDev_valid`): the
local checks are checks of one module and its imports' views.
-/

namespace Fragment

open SetLib IndLib

universe u

variable {V : Type u} [IndLib V] [LevelOracle]

/-! ## The instance -/

/-- **The names a list of declarations flags as proofs.** -/
def Flagged (D : List Decl × (Name → Bool)) (n : Name) : Prop :=
  ∃ d ∈ D.1, n ∈ d.names ∧ D.2 n = true

/-- **Acceptance**: the checked list over a closed context, with its
proof flags. -/
def FAccepts (Γ : Env) (D : List Decl × (Name → Bool)) (Γ' : Env) : Prop :=
  Γ' = applyAll D.1 Γ ∧ Checks Γ D.1 ∧ FlagsOk D.2 Γ D.1 ∧ Env.Scoped Γ

/-- **The step**: a model of the context extends to one of the own
environment, with the same sets on the context, every flagged proof
the point. -/
theorem FAccepts.step {Γ Γ' : Env} {D : List Decl × (Name → Bool)} (h : FAccepts Γ D Γ')
    (m : BlockModel V Γ) : ∃ m' : BlockModel V Γ',
      (∀ n, (Γ.find? n).isSome = true → m'.M n = m.M n) ∧
      ∀ n, Flagged D n → m'.M n = dflt := by
  obtain ⟨rfl, hc, hfl, hs⟩ := h
  obtain ⟨m', hag, hpt⟩ := hc.blockModel D.2 hfl hs m
  exact ⟨m', fun n hn => funext (hag n hn), fun n ⟨d, hd, hn, hp⟩ => funext (hpt d hd n hn hp)⟩

variable (V) in
/-- **The fragment's model as a modular semantics.** -/
@[reducible] noncomputable def fragmentSemantics : ModularSemantics.{0, u} where
  Env := Env
  Name := Name
  Stores E n := (E.find? n).isSome = true
  Mod := BlockModel V
  Val := List Nat → V
  val m n := m.M n
  proofVal := dflt
  Assembled C _ E same := Assembled C E same
  assembled_src h n hn := by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    obtain ⟨i, hs, ci', hf', -⟩ := h.le n ci hci
    exact ⟨i, hs, by rw [hf']; rfl⟩
  amalgamate h m hc := h.model m hc
  Decls := List Decl × (Name → Bool)
  Flagged := Flagged
  Accepts := FAccepts
  step h m := h.step m

/-! ## A development of modules, over the instance -/

variable (V) in
/-- **The development**, over the fragment's semantics. -/
def toDev (dev : Nat → Module) : Development (fragmentSemantics V) Stmt where
  ctx i := (dev i).context
  decls i := ((dev i).decls, (dev i).proofs)
  own i := (dev i).own
  views i := (dev i).views
  imports i := (dev i).imports
  key i := (dev i).key

/-- **A validated module is valid over the instance.** -/
theorem toDev_valid (dev : Nat → Module) (i : Nat) (hv : Valid dev i) :
    (toDev V dev).Valid i := by
  rcases hv with h | h
  · refine ⟨h.iface, h.importOk.imports, .inl ⟨h.importOk.reads, ⟨rfl, h.checks, h.flags,
      h.importOk.reads.scoped⟩, fun n hn hC => ?_⟩⟩
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hn
    rcases find?_applyAll he with ⟨d, hd, hl⟩ | hl
    · have hnm : n ∈ d.names := (d.mem_names_iff n).mpr ⟨e, key_of_lookup hl⟩
      have hk := h.key_own d hd n hnm e he
      show (dev i).key n = _ ∨ (∃ s, (dev i).key n = _) ∧ Flagged ((dev i).decls, (dev i).proofs) n
      rw [hk]
      unfold Module.ownKey
      split
      · rename_i hp; exact .inr ⟨⟨_, rfl⟩, d, hd, hnm, hp⟩
      · exact .inl rfl
    · exact absurd (show ((dev i).context.find? n).isSome = true by rw [hl]; rfl) hC
  · exact ⟨h.iface, h.imports, .inr h.reads⟩

/-! ## The theorem -/

variable (V) in
/-- **Modular checking** (the theorem): if every module below `k` is
validated, there is a family of models, one of each module's own
environment, that is **compatible**: two modules that store a name
under one key give it one set, and every proof's set is the point.  It
is the generic theorem (`Development.modular`) at the fragment's
semantics. -/
theorem modular (dev : Nat → Module) (k : Nat) (h : ∀ i < k, Valid dev i) :
    ∃ m : (i : Nat) → i < k → BlockModel V (dev i).own,
      (∀ i i' (hi : i < k) (hi' : i' < k) n, ((dev i).own.find? n).isSome →
        ((dev i').own.find? n).isSome → (dev i).key n = (dev i').key n →
          (m i hi).M n = (m i' hi').M n) ∧
      ∀ i (hi : i < k) n s, ((dev i).own.find? n).isSome → (dev i).key n = .proof s →
        ∀ ls, (m i hi).M n ls = pt := by
  obtain ⟨m, hc, hp⟩ := (toDev V dev).modular k fun i hi => toDev_valid dev i (h i hi)
  exact ⟨m, hc, fun i hi n s hn hs ls => congrFun (hp i hi n s hn hs) ls⟩

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
