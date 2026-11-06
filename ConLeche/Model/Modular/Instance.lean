module

public import ConLeche.Model.Modular.Restrict
public import ConLeche.Model.Modular.Step
public import ConLeche.Modular.Generic
import ConLeche.Verify.Cached.DeclPushes

public section

/-!
# Con-leche's models as a modular semantics

The instance of `ConLeche.Modular.ModularSemantics` (`ConLeche/Modular/Generic.lean`) for
con-leche's graded models (`conlecheSemantics`), so that the modular theorem is the generic one
(`Development.modular`) at con-leche's models.

* **Environments** are con-leche's environments, each with the names it **exposes**; a name is
  stored when `find?` finds it and it is exposed.  A module's own environment and context expose
  every name; the view a module reads of an earlier one is that module's own environment exposing
  what the reader reads alike.  Nothing is renamed.
* **A model** (`MMod`) is a leaf assignment, closed and graded, under which the environment has a
  covered model (`EnvModelM`, with the η-family run and closure and the `Nat` facts) reading its
  leaves; a name's **value** is its leaf, and every proof's is the canonical proof `.prf`.
* **Assembly** (`AssembledX`): the environment is a member's, exposing no more names, or every name
  of it is exposed and read from a member exposing what it reads (`CtxRead`, `Read.lean`), the
  definition-headed formers reducing as at their sources (`FormerRunsX`).
* **Amalgamation** gives each name the leaf of the member it is read from, and `ctxModel` builds
  the model (`Restrict.lean`).
* **Acceptance** is the fold's run from the context, with the proof flags; **the step** is
  `declsRun_flags` (`Step.lean`).
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular ConLeche.Model ConLeche.Verify ConLeche.Cached
open ConLeche.Term (Term)
open ConLeche.Semantics

universe w

/-- An environment with the names it exposes. -/
abbrev XEnv := Env × (Name → Prop)

/-- The names an environment of the instance stores: the ones it has and exposes. -/
@[expose] def StoresX (E : XEnv) (n : Name) : Prop := (E.1.find? n).isSome = true ∧ E.2 n

variable (V : Type w) [SetTheory V]

/-- **A model of an environment** (see the module docstring). -/
@[expose] def MMod (E : XEnv) : Type :=
  { a : Name → (Name → Nat) → Term // (∀ n ψ, Term.Closed (a n ψ)) ∧
    (∀ n ψ (ρ : Nat → V), WellDenoted V ρ (a n ψ)) ∧
    ∃ mp : EnvModelM V E.1, LfpCover mp [] ∧ FamilyRan mp ∧ EtaFamiliesClosed E.1 ∧ NatFacts E.1 ∧
      ∀ n, (E.1.find? n).isSome = true → mp.base2.acval n = a n }

variable {V}

/-- The member a name is read from, as an environment (the empty one for none). -/
@[expose] def srcEnv {ι : Type} (E : ι → XEnv) (src : Name → Option ι) (n : Name) : Env :=
  match src n with
  | some i => (E i).1
  | none => Env.empty

/-- **The definition-headed formers reduce as at their sources** (`ctxModel`'s `hdh`; see
`ConLeche.Modular.FormerRuns`, which task #469 is to discharge). -/
@[expose] def FormerRunsX (C : Env) (E R : Name → Env) : Prop :=
  ∀ n T cv caps, (C.find? n).isSome = true → ((R n).find? T).isSome = true →
    C.find? T = some (.indInfo cv caps) → formerDefHeaded cv = true →
    ∀ F f, reducedFormer (fueledOps .verified F) (E n) cv (caps.nparams + caps.nIdx) = .ok f →
      f.type.constsResolve (R n) = true ∧
      ∃ F', reducedFormer (fueledOps .verified F') C cv (caps.nparams + caps.nIdx) = .ok f

/-- **Assembly** (see the module docstring). -/
inductive AssembledX (C : XEnv) {ι : Type} (E : ι → XEnv) : Prop
  /-- `C` is a member's environment, exposing no more names -/
  | self (i : ι) (hC : C.1 = (E i).1) (hs : ∀ n, (C.1.find? n).isSome = true → C.2 n → (E i).2 n)
  /-- every name of `C` is exposed and read from a member exposing what it reads -/
  | reads (src : Name → Option ι) (R : Name → Env) (hall : ∀ n, C.2 n)
      (hsrc : ∀ n, (C.1.find? n).isSome = true → (src n).isSome = true)
      (hexp : ∀ n i, src n = some i → ∀ d, ((R n).find? d).isSome = true → (E i).2 d)
      (hread : CtxRead C.1 (srcEnv E src) R) (hruns : FormerRunsX C.1 (srcEnv E src) R)

theorem srcEnv_of {ι : Type} {E : ι → XEnv} {src : Name → Option ι} {n : Name} {i : ι}
    (h : src n = some i) : srcEnv E src n = (E i).1 := by
  simp only [srcEnv, h]

theorem AssembledX.src {C : XEnv} {ι : Type} {E : ι → XEnv} (h : AssembledX C E) (n : Name)
    (hn : StoresX C n) : ∃ i, StoresX (E i) n := by
  cases h with
  | self i hC hs => exact ⟨i, by rw [← hC]; exact hn.1, hs n hn.1 hn.2⟩
  | reads src R hall hsrc hexp hread _ =>
    obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hsrc n hn.1)
    have hself := hread.self n hn.1
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hself
    obtain ⟨hE, -⟩ := hread.R_sub n n ci hci
    rw [srcEnv_of hi] at hE
    exact ⟨i, by rw [hE]; rfl, hexp n i hi n hself⟩

/-- **Amalgamation** of a family that agrees on `C`. -/
theorem amalgamateX {C : XEnv} {ι : Type} {E : ι → XEnv} (h : AssembledX C E)
    (m : (i : ι) → MMod V (E i))
    (hc : ∀ n i i', StoresX C n → StoresX (E i) n → StoresX (E i') n → (m i).1 n = (m i').1 n) :
    ∃ mC : MMod V C, ∀ n i, StoresX C n → StoresX (E i) n → mC.1 n = (m i).1 n := by
  classical
  cases h with
  | self i hC hs =>
    refine ⟨⟨(m i).1, by rw [hC]; exact (m i).2⟩, fun n i' hn hs' => ?_⟩
    exact hc n i i' hn ⟨by rw [← hC]; exact hn.1, hs n hn.1 hn.2⟩ hs'
  | reads src R hall hsrc hexp hread hruns =>
    -- each name's source model
    have hex : ∀ n, ∃ mp : EnvModelM V (srcEnv E src n), LfpCover mp [] ∧ FamilyRan mp ∧
        EtaFamiliesClosed (srcEnv E src n) ∧ NatFacts (srcEnv E src n) ∧
        ∀ i, src n = some i → ∀ d, ((E i).1.find? d).isSome = true →
          mp.base2.acval d = (m i).1 d := by
      intro n
      cases hs : src n with
      | none =>
        rw [show srcEnv E src n = Env.empty by simp only [srcEnv, hs]]
        obtain ⟨⟨mp, hcov, hran⟩, heta, hnat⟩ := EnvModelOk.empty (V := V)
        exact ⟨mp, hcov, hran, heta, hnat, fun _ h => nomatch h⟩
      | some i =>
        rw [show srcEnv E src n = (E i).1 by simp only [srcEnv, hs]]
        obtain ⟨mp, hcov, hran, heta, hnat, hag⟩ := (m i).2.2.2
        exact ⟨mp, hcov, hran, heta, hnat, fun i' hi' d hd => by
          obtain rfl := Option.some.inj hi'
          exact hag d hd⟩
    let mm := fun n => Classical.choose (hex n)
    have hmm := fun n => Classical.choose_spec (hex n)
    let aC : Name → (Name → Nat) → Term := fun n =>
      match src n with
      | some i => (m i).1 n
      | none => fun _ => .prf
    have haC : ∀ n i, src n = some i → aC n = (m i).1 n := fun n i h => by
      simp only [aC, h]
    -- a stored name, stored in its own source and exposed there
    have hown : ∀ d, (C.1.find? d).isSome = true → ∃ i, src d = some i ∧ StoresX (E i) d := by
      intro d hd
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hsrc d hd)
      have hself := hread.self d hd
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hself
      obtain ⟨hE, -⟩ := hread.R_sub d d ci hci
      rw [srcEnv_of hi] at hE
      exact ⟨i, hi, by rw [hE]; rfl, hexp d i hi d hself⟩
    have hclosed : ∀ n ψ, Term.Closed (aC n ψ) := by
      intro n ψ
      cases hs : src n with
      | none => simp only [aC, hs]; simp [Term.Closed, Term.bvarsBelow]
      | some i => simp only [aC, hs]; exact (m i).2.1 n ψ
    have hwd : ∀ n ψ (ρ : Nat → V), WellDenoted V ρ (aC n ψ) := by
      intro n ψ ρ
      cases hs : src n with
      | none => simp only [aC, hs]; simp
      | some i => simp only [aC, hs]; exact (m i).2.2.1 n ψ ρ
    have hleaf : ∀ n, (C.1.find? n).isSome = true → ∀ d, ((R n).find? d).isSome = true →
        aC d = (mm n).base2.acval d := by
      intro n hn d hd
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hsrc n hn)
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hd
      obtain ⟨hEd, hCd⟩ := hread.R_sub n d ci hci
      rw [srcEnv_of hi] at hEd
      obtain ⟨i', hi', hs'⟩ := hown d hCd
      rw [(hmm n).2.2.2.2 i hi d (by rw [hEd]; rfl), haC d i' hi']
      exact hc d i' i ⟨hCd, hall d⟩ hs' ⟨by rw [hEd]; rfl, hexp n i hi d hd⟩
    obtain ⟨mp, hcov, hran, heta, hnat, hac⟩ := ctxModel hread mm (fun n => (hmm n).1)
      (fun n => (hmm n).2.2.1) (fun n => (hmm n).2.2.2.1) (fun n => (hmm n).2.1) hruns hleaf
      hclosed hwd
    refine ⟨⟨aC, hclosed, hwd, mp, hcov, hran, heta, hnat, hac⟩, fun n i hn hs => ?_⟩
    obtain ⟨i', hi', hs'⟩ := hown n hn.1
    show aC n = _
    rw [haC n i' hi']
    exact hc n i' i hn hs' hs

/-! ## Acceptance and the step -/

/-- **The names a list of records flags as proofs.** -/
@[expose] def FlaggedX (D : List Declaration × (Name → Bool)) (n : Name) : Prop :=
  D.2 n = true ∧ ∃ d ∈ D.1, n ∈ declNames d

/-- **Acceptance**: the fold's run from the context's canonical index, with the proof flags. -/
@[expose] def AcceptsX (pins : List NatOpPinSet) (Γ : XEnv) (D : List Declaration × (Name → Bool))
    (Γ' : XEnv) : Prop :=
  Γ'.1 = streamEnv D.1 Γ.1 ∧ (∃ k q, DeclsRun .verified pins D.1 (k, mkFEnv Γ.1) q) ∧
    FlagsOk .verified pins D.2 Γ.1 D.1

/-- **The step**: every model of the context extends to one of the own environment, with the
same leaves on the context and the canonical proof at every flagged proof. -/
theorem AcceptsX.step {pins : List NatOpPinSet} {Γ Γ' : XEnv} {D : List Declaration × (Name → Bool)}
    (h : AcceptsX pins Γ D Γ') (m : MMod V Γ) :
    ∃ m' : MMod V Γ', (∀ n, StoresX Γ n → m'.1 n = m.1 n) ∧
      ∀ n, FlaggedX D n → m'.1 n = fun _ => Term.prf := by
  obtain ⟨hΓ', ⟨k, q, hrun⟩, hfl⟩ := h
  obtain ⟨-, -, mp, hcov, hran, heta, hnat, hag⟩ := m.2
  have key := declsRun_flags (V := V) hrun rfl hfl mp hcov hran heta hnat
  have henv : q.2.env = Γ'.1 := by rw [declsRun_env .verified hrun, hΓ']; rfl
  rw [henv] at key
  obtain ⟨mp', hleaf, hcov', hran', heta', hnat', hflag⟩ := key
  refine ⟨⟨mp'.base2.acval, mp'.base2.cval_closed, mp'.base2.acval_wellDenoted, mp', hcov', hran',
    heta', hnat', fun _ _ => rfl⟩, fun n hn => (hleaf n hn.1).trans (hag n hn.1), fun n ⟨hp, d, hd, hnd⟩ =>
    hflag d hd n hnd hp⟩

variable (V) in
/-- **Con-leche's models as a modular semantics.** -/
@[expose, reducible] noncomputable def conlecheSemantics (pins : List NatOpPinSet) :
    ModularSemantics.{0, 0} where
  Env := XEnv
  Name := Name
  Stores := StoresX
  Mod := MMod V
  Val := (Name → Nat) → Term
  val m n := m.1 n
  proofVal := fun _ => Term.prf
  Assembled C _ E := AssembledX C E
  assembled_src h n hn := h.src n hn
  amalgamate h m hc := by
    obtain ⟨mC, hmC⟩ := amalgamateX h m fun n i i' hn hs hs' => hc i i' n hn hs hs'
    exact ⟨mC, fun i n hn _ hs => hmC n i hn hs⟩
  Decls := List Declaration × (Name → Bool)
  Flagged := FlaggedX
  Accepts := AcceptsX pins
  step h m := h.step m

end ConLeche.Model.Modular
