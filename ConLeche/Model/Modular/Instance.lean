module

import ConLeche.Modular.Generic
public import ConLeche.Model.Modular.Restrict
import ConLeche.Model.Modular.Step

public section

/-!
# Con-leche's models as a modular semantics

The instance of `ConLeche.Modular.ModularSemantics`
(`ConLeche/Modular/Generic.lean`) for con-leche's graded models
(`conlecheSemantics`), so that the modular theorem is the generic one
(`Development.modular`) at con-leche's models.

* **Environments** are con-leche's environments, each with the names
  it **exposes**; a name is stored when `find?` finds it and it is
  exposed.  A module's own environment and context expose every name;
  the view a module reads of an earlier one is that module's own
  environment exposing only what the reader reads alike (the reader's
  `readsAlike`, `Main.lean`).  Nothing is renamed: a module's
  environment uses its own names, and what declared each name lives in
  the development.
* **A model** (`MMod`) is a leaf assignment, closed and graded, under
  which the environment has a covered model (`EnvModelM`) reading its
  leaves; a name's **value** is its leaf, and every proof's is the
  canonical one (`dfltLeaf`).
* **Assembly** (`AssembledC`): the environment is a member's, exposing
  no more names, or every name of it is exposed and read from a member
  exposing it (`src`), with the part of that member it reads (`R`),
  exposed there, as `CtxRead` (`Restrict.lean`) says.
* **Amalgamation** (`amalgamateC`) gives each name the leaf of the member
  it is read from; where the family is compatible for the environment,
  the leaves a constant's laws read are the leaves of the member it is
  read from, and `CtxSrc.ctxModel` builds the model.
* **Acceptance** (`AcceptsC`) is `AcceptedFrom`, the flagged names new
  in the context and flagged to it; **the step** (`stepC`) is
  `acceptedFrom_model`.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Semantics ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

universe w

theorem find?_filter_name {l : List ConstantInfo} {p : Name → Bool} {n : Name} :
    (l.filter fun c => p c.name).find? (·.name == n) =
      if p n = true then l.find? (·.name == n) else none := by
  induction l with
  | nil => simp
  | cons c l ih =>
    by_cases hp : p c.name = true <;> by_cases hc : c.name = n <;>
      simp_all

/-! ## Models -/

variable (V : Type w) [SetTheory V] (μ : CheckMode)

/-- Leaves that are closed and graded. -/
@[expose] def LeavesOk (a : Name → (Name → Nat) → Term) : Prop :=
  (∀ n ψ, Term.Closed (a n ψ)) ∧ ∀ n ψ (ρ : Nat → V), WellDenoted V ρ (a n ψ)

/-- The default leaf: every proof's, and every name's off the
environment. -/
@[expose] def dfltLeaf : (Name → Nat) → Term := fun _ => .prf

/-- **A model of an environment** (see the module docstring). -/
@[expose] def MMod (E : Env) : Type :=
  { a : Name → (Name → Nat) → Term // LeavesOk V a ∧
    ∃ mp : EnvModelM V μ E, LfpCover mp [] ∧ ConLeche.EtaFamiliesClosed E ∧ NodupNames E ∧
      ∀ n, (E.find? n).isSome = true → mp.base2.acval n = a n }

variable {V μ}

theorem dfltLeaf_closed (ψ : Name → Nat) : Term.Closed (dfltLeaf ψ) := by
  simp [dfltLeaf, Term.Closed, Term.bvarsBelow]

theorem dfltLeaf_wd (ψ : Name → Nat) (ρ : Nat → V) : WellDenoted V ρ (dfltLeaf ψ) := by
  simp [dfltLeaf]

/-! ## Assembly and amalgamation -/

/-- The member a name is read from, as an environment (the empty one for
none). -/
@[expose] def srcEnv {ι : Type} (E : ι → Env) (src : Name → Option ι) (n : Name) : Env :=
  match src n with
  | some i => E i
  | none => Env.empty

/-- **Assembly** (see the module docstring). -/
inductive AssembledC (C : Env × (Name → Prop)) {ι : Type} (E : ι → Env × (Name → Prop)) : Prop
  /-- `C` is a member's environment, exposing no more names -/
  | self (i : ι) (hC : C.1 = (E i).1) (hs : ∀ n, (C.1.find? n).isSome = true → C.2 n → (E i).2 n)
  /-- every name of `C` is exposed, and read from a member exposing it -/
  | reads (src : Name → Option ι) (R : Name → Env)
      (hsrc : ∀ n, (C.1.find? n).isSome = true → C.2 n ∧ ∃ i, src n = some i ∧ (E i).2 n)
      (hR : ∀ n d ci, (R n).find? d = some ci → ∃ i, src n = some i ∧ (E i).2 d)
      (hread : CtxRead C.1 (srcEnv (fun i => (E i).1) src) R)

theorem srcEnv_of {ι : Type} {E : ι → Env} {src : Name → Option ι} {n : Name} {i : ι}
    (h : src n = some i) : srcEnv E src n = E i := by
  simp only [srcEnv, h]

/-- In a reading, the member a stored name is read from stores it. -/
theorem AssembledC.stores_src {C : Env} {ι : Type} {E : ι → Env} {src : Name → Option ι}
    {R : Name → Env} (hread : CtxRead C (srcEnv E src) R) {n : Name} {i : ι}
    (hn : (C.find? n).isSome = true) (hi : src n = some i) : ((E i).find? n).isSome = true := by
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
  obtain ⟨ci', hf, -⟩ := hread.entry n ci hci
  rw [srcEnv_of hi] at hf
  rw [hf]; rfl

/-- The names an environment of the instance stores: the ones it has
and exposes. -/
@[expose] def StoresC (E : Env × (Name → Prop)) (n : Name) : Prop :=
  (E.1.find? n).isSome = true ∧ E.2 n

theorem AssembledC.src {C : Env × (Name → Prop)} {ι : Type} {E : ι → Env × (Name → Prop)}
    (h : AssembledC C E) (n : Name) (hn : StoresC C n) : ∃ i, StoresC (E i) n := by
  cases h with
  | self i hC hs => exact ⟨i, by rw [← hC]; exact hn.1, hs n hn.1 hn.2⟩
  | reads src R hsrc _ hread =>
    obtain ⟨-, i, hi, hs⟩ := hsrc n hn.1
    exact ⟨i, AssembledC.stores_src hread hn.1 hi, hs⟩

/-- **Amalgamation** of a family compatible for `C`. -/
theorem amalgamateC {C : Env × (Name → Prop)} {ι : Type} {E : ι → Env × (Name → Prop)}
    (h : AssembledC C E) (m : (i : ι) → MMod V μ (E i).1)
    (hc : ∀ n i i', StoresC C n → StoresC (E i) n → StoresC (E i') n → (m i).1 n = (m i').1 n) :
    ∃ mC : MMod V μ C.1, ∀ n i, StoresC C n → StoresC (E i) n → mC.1 n = (m i).1 n := by
  classical
  cases h with
  | self i hC hs =>
    refine ⟨⟨(m i).1, by rw [hC]; exact (m i).2⟩, fun n i' hn hs' => ?_⟩
    exact hc n i i' hn ⟨by rw [← hC]; exact hn.1, hs n hn.1 hn.2⟩ hs'
  | reads src R hsrc hR hread =>
    let srcOf : Name → Σ E' : Env, EnvModelM V μ E' := fun n =>
      match src n with
      | some i => ⟨(E i).1, Classical.choose (m i).2.2⟩
      | none => ⟨Env.empty, EnvModelM.empty V μ⟩
    have hpos : ∀ n i, src n = some i → srcOf n = ⟨(E i).1, Classical.choose (m i).2.2⟩ :=
      fun n i h => by simp only [srcOf, h]
    have hneg : ∀ n, src n = none → srcOf n = ⟨Env.empty, EnvModelM.empty V μ⟩ :=
      fun n h => by simp only [srcOf, h]
    have hE : (fun n => (srcOf n).1) = srcEnv (fun i => (E i).1) src := by
      funext n
      cases hs : src n with
      | some i => rw [hpos n i hs, srcEnv_of hs]
      | none => rw [hneg n hs]; simp only [srcEnv, hs]
    let aC : Name → (Name → Nat) → Term := fun n =>
      match src n with
      | some i => (m i).1 n
      | none => dfltLeaf
    have haC : ∀ n i, src n = some i → aC n = (m i).1 n := fun n i h => by simp only [aC, h]
    have hl : LeavesOk V aC := by
      refine ⟨fun n ψ => ?_, fun n ψ ρ => ?_⟩
      · cases hs : src n with
        | some i => rw [haC n i hs]; exact (m i).2.1.1 n ψ
        | none => simp only [aC, hs]; exact dfltLeaf_closed ψ
      · cases hs : src n with
        | some i => rw [haC n i hs]; exact (m i).2.1.2 n ψ ρ
        | none => simp only [aC, hs]; exact dfltLeaf_wd ψ ρ
    -- a name stored in `C` has the leaf of every member storing it
    have hval : ∀ n i, StoresC C n → StoresC (E i) n → aC n = (m i).1 n := by
      intro n i hn he
      obtain ⟨-, i', hi', hs'⟩ := hsrc n hn.1
      rw [haC n i' hi']
      exact hc n i' i hn ⟨AssembledC.stores_src hread hn.1 hi', hs'⟩ he
    let S : CtxSrc V μ C.1 aC :=
      { E := fun n => (srcOf n).1
        m := fun n => (srcOf n).2
        R := R
        read := hE ▸ hread
        leafEq := fun n _ d hRd hEd => by
          obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hRd
          obtain ⟨i, hi, hsd⟩ := hR n d ci hci
          have hCd := (hread.R_sub n d ci hci).2
          rw [hpos n i hi] at hEd ⊢
          rw [hval d i ⟨hCd, (hsrc d hCd).1⟩ ⟨hEd, hsd⟩]
          exact ((Classical.choose_spec (m i).2.2).2.2.2 d hEd).symm
        cover := fun n => by
          cases hs : src n with
          | some i => rw [hpos n i hs]; exact (Classical.choose_spec (m i).2.2).1
          | none => rw [hneg n hs]; exact lfpCover_empty
        eta := fun n => by
          cases hs : src n with
          | some i => rw [hpos n i hs]; exact (Classical.choose_spec (m i).2.2).2.1
          | none => rw [hneg n hs]; exact ConLeche.EtaFamiliesClosed.empty
        closed := hl.1
        wd := hl.2 }
    obtain ⟨mc, hmc, hcov, heta⟩ := S.ctxModel
    exact ⟨⟨aC, hl, mc, hcov, heta, hread.nodup, fun n _ => by rw [hmc]⟩, hval⟩

/-! ## Acceptance and the step -/

variable (μ) in
/-- **Acceptance**: the declarations are accepted from `Γ` at some proof
flags, and every name flagged here is new in `Γ` and flagged there
(the exposed names play no part). -/
@[expose] def AcceptsC (pins : List NatOpPinSet) (Γ : Env) (D : List Declaration × (Name → Bool))
    (Γ' : Env) : Prop :=
  ∃ p : Name → Bool, AcceptedFrom μ pins p Γ D.1 Γ' ∧
    ∀ n, D.2 n = true → p n = true ∧ Γ.find? n = none

/-- **The conservative step.** -/
theorem stepC (hμ : μ.isVerified = true) {pins : List NatOpPinSet} {Γ Γ' : Env}
    {D : List Declaration × (Name → Bool)} (h : AcceptsC μ pins Γ D Γ') (m : MMod V μ Γ) :
    ∃ m' : MMod V μ Γ', (∀ n, (Γ.find? n).isSome = true → m'.1 n = m.1 n) ∧
      ∀ n, D.2 n = true → m'.1 n = dfltLeaf := by
  obtain ⟨p, hacc, hfl⟩ := h
  obtain ⟨a, hl, mp, hcov, heta, hnd, hacv⟩ := m
  obtain ⟨hnd', hext, -⟩ := acceptedFrom_syn hacc hnd
  obtain ⟨mp', hag, hcov', heta', hpf⟩ := acceptedFrom_model hμ hacc mp hcov heta hnd
  let a' : Name → (Name → Nat) → Term := fun n =>
    if (Γ'.find? n).isSome then mp'.base2.acval n else dfltLeaf
  have hpos : ∀ n, (Γ'.find? n).isSome = true → a' n = mp'.base2.acval n :=
    fun n h => by simp only [a', h, ↓reduceIte]
  have hneg : ∀ n, (Γ'.find? n).isSome = false → a' n = dfltLeaf :=
    fun n h => by simp only [a', h, Bool.false_eq_true, ↓reduceIte]
  refine ⟨⟨a', ⟨fun n ψ => ?_, fun n ψ ρ => ?_⟩, mp', hcov', heta', hnd', fun n h => (hpos n h).symm⟩,
    fun n hn => ?_, fun n hn => ?_⟩
  · cases h : (Γ'.find? n).isSome
    · rw [hneg n h]; exact dfltLeaf_closed ψ
    · rw [hpos n h]; exact mp'.base2.cval_closed _ ψ
  · cases h : (Γ'.find? n).isSome
    · rw [hneg n h]; exact dfltLeaf_wd ψ ρ
    · rw [hpos n h]; exact mp'.base2.acval_wellDenoted _ ψ ρ
  · obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    have hE : (Γ'.find? n).isSome = true := by rw [hext.find? hnd' hci]; rfl
    show a' n = a n
    rw [hpos n hE, (hag n hn).2, hacv n hn]
  · obtain ⟨hp, hΓ⟩ := hfl n hn
    show a' n = dfltLeaf
    cases h : (Γ'.find? n).isSome
    · exact hneg n h
    · rw [hpos n h]; exact hpf n hp hΓ h

/-! ## The instance -/

variable (V μ) in
/-- **Con-leche's models as a modular semantics.** -/
@[expose] noncomputable def conlecheSemantics (hμ : μ.isVerified = true) (pins : List NatOpPinSet) :
    ModularSemantics.{0, 0} where
  Env := Env × (Name → Prop)
  Name := Name
  Stores := StoresC
  Mod E := MMod V μ E.1
  Val := (Name → Nat) → Term
  val m n := m.1 n
  proofVal := dfltLeaf
  Assembled C _ E := AssembledC C E
  assembled_src h := h.src
  amalgamate h m hc := by
    obtain ⟨mC, hmC⟩ := amalgamateC h m fun n i i' => hc i i' n
    exact ⟨mC, fun i n hn _ hs => hmC n i hn hs⟩
  Decls := List Declaration × (Name → Bool)
  Flagged D n := D.2 n = true
  Accepts Γ D Γ' := AcceptsC μ pins Γ.1 D Γ'.1
  step h m := by
    obtain ⟨m', h1, h2⟩ := stepC hμ h m
    exact ⟨m', fun n hn => h1 n hn.1, h2⟩

end ConLeche.Model.Modular
