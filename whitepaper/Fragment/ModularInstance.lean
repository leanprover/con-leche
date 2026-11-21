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
  `BlockModel` in which proofs are the point (`ProofsPt`) and every
  stored constant holds (`Holds`, read off the input), its **value** at
  a name the name's set at every list of levels, and **the value of
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
  proofs stay the point, and every stored constant holds.

A development of modules (`Module`) is a development over the instance
(`toDev`), and a module that passes its local checks is a valid one
(`toDev_valid`): the local checks are checks of one module and its
imports' views.

**The modular theorem** (`modular`) is stated over the input, as the
main theorem is: every module has a model of its own declarations'
constants (`IsModel`, `constantsOf`), and the models agree on every
name a module sees as another module's (`Sees`).
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
environment, keeping every name of the context with its set, proofs
the point, and every stored constant holding. -/
theorem FAccepts.step {Γ Γ' : Env} {D : List Decl} (h : FAccepts Γ D Γ')
    (m : BlockModel V Γ) (hp : ProofsPt Γ m.M) (hh : Holds Γ m.M) :
    ∃ m' : BlockModel V Γ', (ProofsPt Γ' m'.M ∧ Holds Γ' m'.M) ∧
      ∀ n, (Γ.find? n).isSome = true → (Γ'.find? n).isSome = true ∧ m'.M n = m.M n := by
  obtain ⟨rfl, hc, hs⟩ := h
  obtain ⟨m', hag, hp', hh'⟩ := hc.blockModel hs m hp hh
  exact ⟨m', ⟨hp', hh'⟩, fun n hn => ⟨isSome_find?_applyAll hn D, funext (hag n hn)⟩⟩

omit [LevelOracle] in
/-- A constant holds as its refinement too: a refinement is the
constant itself or an assumption of its type (membership only). -/
theorem ModelOf.of_le {M : Name → List Nat → V} {n : Name} {ci ci' : ConstInfo} (hle : ci.Le ci')
    (h : ModelOf M n ci') : ModelOf M n ci := by
  rcases hle with rfl | ⟨hk, k, rfl⟩
  · exact h
  · obtain ⟨ps, T, k'⟩ := ci
    simp only at hk
    subst hk
    intro vals hvals
    exact ⟨(h vals hvals).1, trivial⟩

omit [LevelOracle] in
/-- **Amalgamation keeps `Holds`**: every constant of an assembled
environment is a member's (or an assumption of its type), within the
part of the member it shares, where the amalgamated assignment is the
member's. -/
theorem Assembled.holds {C : Env} {ι : Type} {E : ι → Env} (h : Assembled C E)
    (m : (i : ι) → BlockModel V (E i)) (hh : ∀ i, Holds (E i) (m i).M) (MC : Name → List Nat → V)
    (hmC : ∀ n i, (C.find? n).isSome → ((E i).find? n).isSome → MC n = (m i).M n) :
    Holds C MC := by
  intro n ci hf
  obtain ⟨i, ci', hf', hle, hsc⟩ := h.le n ci hf
  have hag : ∀ d, ((common C (E i)).find? d).isSome → ∀ ls, (m i).M d ls = MC d ls := by
    intro d hd ls
    obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hd
    obtain ⟨h1, h2⟩ := find?_common he
    rw [hmC d i h2 (by rw [h1]; rfl)]
  have hn : ∀ ls, (m i).M n ls = MC n ls := fun ls => by
    rw [hmC n i (by rw [hf]; rfl) (by rw [hf']; rfl)]
  exact ((hh i n ci' hf').of_le hle).congr hn (fun c hc => hag c (hsc.1.2.1 c hc))
    (fun v hv c hc => hag c ((hsc.2.1 v hv).2.1 c hc))
    (fun nP nM nMin nI rules hk rl hrl c hc =>
      hag c ((hsc.2.2.1 nP nM nMin nI rules hk rl hrl).1.2.1 c hc))

variable (V) in
/-- **The fragment's model as a modular semantics.** -/
@[reducible] noncomputable def fragmentSemantics : ModularSemantics.{0, u} where
  Env := Env
  Name := Name
  Stores E n := (E.find? n).isSome = true
  Mod E := { m : BlockModel V E // ProofsPt E m.M ∧ Holds E m.M }
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
    exact ⟨⟨mC, h.proofsPt _ (fun i => (m i).2.1) mC.M hmC,
      h.holds _ (fun i => (m i).2.2) mC.M hmC⟩, fun i n hn _ hs => hmC n i hn hs⟩
  ProofIn := ProofIn
  proof_val h mC m hag := h.eq_dflt mC.1.toEnvModel m.1.M m.2.1 fun c hC hE => hag c hC hC hE
  ProofBy := ProofBy
  proofBy_val h mC m m' hag hag' := h.eq_dflt mC.1.M m.1.M m'.1.toEnvModel m.2.1
    (fun c hC hE => hag c hC hC hE) fun c hC hE => hag' c hC hC hE
  Decls := List Decl
  Accepts := FAccepts
  step h m := by
    obtain ⟨m', hp', hm'⟩ := h.step m.1 m.2.1 m.2.2
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

/-- **A module that passes its local checks, as its imports do, is
valid over the instance.** -/
theorem toDev_valid (dev : Nat → Module) (i : Nat) (hv' : ∀ j ≤ i, LocalOk dev j) :
    (toDev V dev).Valid i := by
  have hv := hv' i (Nat.le_refl i)
  have hi := hv.importOk
  refine ⟨fun x hx => ?_, hi.reads.1, fun n hn => ?_, ?_⟩
  · obtain ⟨hj, hE⟩ := mem_sources.mp hx
    exact ⟨hi.imports _ hj, (hv' _ (Nat.le_of_lt (hi.imports _ hj))).iface _ hE⟩
  · have r := hi.reads.2 n hn
    exact ⟨r.read, r.part, r.below, r.agree⟩
  · exact ⟨rfl, hv.checks, hi.reads.1.scoped⟩

/-! ## The theorem -/

/-- **Module `j` sees the name `n` as module `j'`'s**: `n` is a name of
`j`'s context, and a view of `j'` that `j` imports stores it.  (The
fragment has no import rules — no headers, no parts —, so a view `j`
imports is what `j`'s header loads.)  It specialises to the two
agreements a module's reading needs: the module a name is read from
is seen (`(dev j).src n`, `ReadsOk.read`), and so is every other import
whose views store the name — every copy of it. -/
def Sees (dev : Nat → Module) (j : Nat) (n : Name) (j' : Nat) : Prop :=
  ((dev j).context.find? n).isSome = true ∧ ∃ E, (j', E) ∈ sources dev j ∧ (E.find? n).isSome = true

variable (V) in
/-- **The family the modular theorem reads**: if every module below `k`
passes its local checks, there are assignments, one per module, in
which every constant of the module's own environment holds (`Holds`),
agreeing on every name a module sees as another module's. -/
theorem modular_holds (dev : Nat → Module) (k : Nat) (h : ∀ i < k, LocalOk dev i) :
    ∃ model : Nat → Name → List Nat → V,
      (∀ j < k, Holds (dev j).own (model j)) ∧
      (∀ j < k, ∀ n j', Sees dev j n j' → model j n = model j' n) := by
  obtain ⟨m, hc⟩ := (toDev V dev).modular k fun i hi =>
    toDev_valid dev i fun j hj => h j (Nat.lt_of_le_of_lt hj hi)
  refine ⟨fun j => if hj : j < k then (m j hj).1.M else fun _ _ => pt, fun j hj => ?_,
    fun j hj n j' ⟨hn, E, hE, hs⟩ => ?_⟩
  · simp only [hj, ↓reduceDIte]
    exact (m j hj).2.2
  · obtain ⟨hsrc, he, hy⟩ := hc j hj n hn
    have hj' : j' < k :=
      Nat.lt_trans ((h j hj).importOk.imports j' (mem_sources.mp hE).1) hj
    have hy' := hy (j', E) hE hj' hs
    simp only [hj, hj', ↓reduceDIte]
    exact he.trans hy'.symm

variable (V) in
/-- **Modular checking** (the theorem): if every module below `k`
passes its local checks, there is a model of each module's own
declarations' constants (`IsModel`, `constantsOf`), and every module's
model gives a name it sees as another module's (`Sees`) that module's
set.  It is the generic theorem (`Development.modular`) at the
fragment's semantics (`modular_holds`): its compatible family agrees,
at a context name, with the module the name is read from and with
every source storing it. -/
theorem modular (dev : Nat → Module) (k : Nat) (h : ∀ i < k, LocalOk dev i) :
    ∃ model : Nat → Name → List Nat → V,
      (∀ j < k, IsModel V (model j) (constantsOf (dev j).decls)) ∧
      (∀ j < k, ∀ n j', Sees dev j n j' → model j n = model j' n) := by
  obtain ⟨model, hh, hsees⟩ := modular_holds V dev k h
  exact ⟨model, fun j hj n ci ⟨d, hd, hm⟩ => hh j hj n ci ((h j hj).checks.find?_of_stores hd hm),
    hsees⟩

end Fragment
