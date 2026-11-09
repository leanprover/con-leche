module

import ConLeche.Model.Modular.Restrict
public import ConLeche.Model.Modular.Step
import ConLeche.Modular.Generic
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
* **A model** (`MMod`) is a leaf assignment, closed and graded, giving every proof the canonical
  proof `.prf` (`ProofLeaves`), under which the environment has a covered model (`EnvModelM`, with
  the η-family run and closure and the `Nat` facts) reading its leaves; a name's **value** is its
  leaf, and every proof's is `.prf`.
* **Assembly** (`AssembledX`): the environment is a member's, exposing no more names, or every name
  of it is exposed and read from a member exposing what it reads (`CtxRead`, `Read.lean`).
* **Amalgamation** gives each name the leaf of the member it is read from, and `ctxModel` builds
  the model (`Restrict.lean`).
* **A proof by `C`** (`ProofInX`): a definition, theorem or axiom whose type `C` infers to be a
  proposition and reads alike (`ReadsX`); a model of `C` reads it as a truth value, so does the
  agreeing model, and `ProofLeaves` gives the canonical proof.  **A proof by a theorem**
  (`ProofByX`): a definition, theorem or axiom of the type of a theorem of another environment,
  both reading it alike over `C`; the theorem's model reads it as a truth value (`ProofLeaves`),
  so does a model of `C` agreeing with it, and so the copy's model.
* **Acceptance** is the fold's run from the context; **the step** is `declsRun_proofs`
  (`Step.lean`).
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
    (∀ n ψ (ρ : Nat → V), WellDenoted V ρ (a n ψ)) ∧ ProofLeaves V E.1 a ∧
    ∃ mp : EnvModelM V E.1, LfpCover mp [] ∧ EtaFamiliesClosed E.1 ∧ NatFacts E.1 ∧
      ∀ n, (E.1.find? n).isSome = true → mp.base2.acval n = a n }

variable {V}

/-- The member a name is read from, as an environment (the empty one for none). -/
@[expose] def srcEnv {ι : Type} (E : ι → XEnv) (src : Name → Option ι) (n : Name) : Env :=
  match src n with
  | some i => (E i).1
  | none => Env.empty

/-- **Assembly** (see the module docstring). -/
inductive AssembledX (C : XEnv) {ι : Type} (E : ι → XEnv) : Prop
  /-- `C` is a member's environment, exposing no more names -/
  | self (i : ι) (hC : C.1 = (E i).1) (hs : ∀ n, (C.1.find? n).isSome = true → C.2 n → (E i).2 n)
  /-- every name of `C` is exposed and read from a member exposing what it reads -/
  | reads (src : Name → Option ι) (R : Name → Env) (hall : ∀ n, C.2 n)
      (hsrc : ∀ n, (C.1.find? n).isSome = true → (src n).isSome = true)
      (hexp : ∀ n i, src n = some i → ∀ d, ((R n).find? d).isSome = true → (E i).2 d)
      (hread : CtxRead C.1 (srcEnv E src) R)

theorem srcEnv_of {ι : Type} {E : ι → XEnv} {src : Name → Option ι} {n : Name} {i : ι}
    (h : src n = some i) : srcEnv E src n = (E i).1 := by
  simp only [srcEnv, h]

theorem AssembledX.src {C : XEnv} {ι : Type} {E : ι → XEnv} (h : AssembledX C E) (n : Name)
    (hn : StoresX C n) : ∃ i, StoresX (E i) n := by
  cases h with
  | self i hC hs => exact ⟨i, by rw [← hC]; exact hn.1, hs n hn.1 hn.2⟩
  | reads src R hall hsrc hexp hread =>
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
  | reads src R hall hsrc hexp hread =>
    -- each name's source model
    have hex : ∀ n, ∃ mp : EnvModelM V (srcEnv E src n), LfpCover mp [] ∧
        EtaFamiliesClosed (srcEnv E src n) ∧ NatFacts (srcEnv E src n) ∧
        ∀ i, src n = some i → ∀ d, ((E i).1.find? d).isSome = true →
          mp.base2.acval d = (m i).1 d := by
      intro n
      cases hs : src n with
      | none =>
        rw [show srcEnv E src n = Env.empty by simp only [srcEnv, hs]]
        obtain ⟨⟨mp, hcov⟩, heta, hnat⟩ := EnvModelOk.empty (V := V)
        exact ⟨mp, hcov, heta, hnat, fun _ h => nomatch h⟩
      | some i =>
        rw [show srcEnv E src n = (E i).1 by simp only [srcEnv, hs]]
        obtain ⟨mp, hcov, heta, hnat, hag⟩ := (m i).2.2.2.2
        exact ⟨mp, hcov, heta, hnat, fun i' hi' d hd => by
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
      rw [(hmm n).2.2.2 i hi d (by rw [hEd]; rfl), haC d i' hi']
      exact hc d i' i ⟨hCd, hall d⟩ hs' ⟨by rw [hEd]; rfl, hexp n i hi d hd⟩
    obtain ⟨mp, hcov, heta, hnat, hac⟩ := ctxModel hread mm (fun n => (hmm n).1)
      (fun n => (hmm n).2.1) (fun n => (hmm n).2.2.1) hleaf hclosed hwd
    -- every proof's leaf, and every theorem's type, read off its source's
    have hPL : ProofLeaves V C.1 aC := by
      intro n ci hf hk
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp (hsrc n (isSome_of hf))
      obtain ⟨ci', hf', hr⟩ := hread.entry n ci hf
      rw [srcEnv_of hi] at hf'
      have hk' : ci'.isStmtKind = true := by
        rcases hr with rfl | ⟨-, h⟩
        · exact hk
        · exact h
      have hcv : ci.toConstantVal = ci'.toConstantVal := hr.alike.cv
      obtain ⟨h1, h2⟩ := (m i).2.2.2.1 n ci' hf' hk'
      have hden : ∀ ψ, denote (m i).1 (E i).1 ψ 0 ci.toConstantVal.type =
          denote aC C.1 ψ 0 ci.toConstantVal.type := by
        -- the type reads alike at the context and at its source
        let S : CtxSrc V C.1 (srcEnv E src) R aC :=
          ⟨hread, mm, fun n => (hmm n).1, fun n => (hmm n).2.1, fun n => (hmm n).2.2.1, hleaf,
            hclosed, hwd⟩
        have hres : ci.toConstantVal.type.constsResolve (R n) = true :=
          (Expr.constsResolve_iff _).mpr (hread.scope n ci hf).1
        have hwf : EnvWF (E i).1 := by
          have h := (mm n).base2.wf
          rw [srcEnv_of hi] at h
          exact h
        have hresE : ci.toConstantVal.type.constsResolve (E i).1 = true := by
          rw [hcv]; exact (hwf.consts ci' (ConLeche.Env.find?_mem hf')).2.2.1
        intro ψ
        rw [S.denote_eq (isSome_of hf) ψ 0 _ hres]
        refine denote_alike (R := (E i).1) (fun {x} hx => ?_) (fun x hx => ?_) (fun {x} _ => ?_)
          ψ 0 _ hresE
        · obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
          exact ⟨c, c, hc, by rw [srcEnv_of hi]; exact hc, .inl rfl⟩
        · exact ((hmm n).2.2.2 i hi x hx).symm
        · rw [srcEnv_of hi]
      rw [show ci'.toConstantVal.type = ci.toConstantVal.type by rw [hcv]] at h1 h2
      refine ⟨fun ⟨cv, hc⟩ => SemPropType.of_denote (fun ψ => (hden ψ).symm) (h1 ?_),
        fun hc => ?_⟩
      · subst hc
        rcases hr with rfl | ⟨h, -⟩
        · exact ⟨cv, rfl⟩
        · exact nomatch h
      · rw [haC n i hi]
        exact h2 (SemPropType.of_denote hden hc)
    refine ⟨⟨aC, hclosed, hwd, hPL, mp, hcov, heta, hnat, hac⟩, fun n i hn hs => ?_⟩
    obtain ⟨i', hi', hs'⟩ := hown n hn.1
    show aC n = _
    rw [haC n i' hi']
    exact hc n i' i hn hs' hs

/-! ## Acceptance and the step -/

/-- **Acceptance**: the fold's run from the context's canonical index, every name exposed. -/
@[expose] def AcceptsX (pins : List NatOpPinSet) (Γ : XEnv) (D : List Declaration)
    (Γ' : XEnv) : Prop :=
  Γ'.1 = streamEnv D Γ.1 ∧ (∀ n, Γ'.2 n) ∧ ∃ k q, DeclsRun .verified pins D (k, mkFEnv Γ.1) q

theorem streamEnv_isSome_base : ∀ (D : List Declaration) {E : Env} {n : Name},
    (E.find? n).isSome = true → ((streamEnv D E).find? n).isSome = true
  | [], _, _, h => h
  | d :: D, E, n, h => by
    show ((streamEnv D (E.pushDelta (declConstants d) (declTables d))).find? n).isSome = true
    exact streamEnv_isSome_base D (find?_pushDelta_isSome (.inl h))

/-- **The step**: every model of the context extends to one of the own environment, with the
same leaves on the context. -/
theorem AcceptsX.step {pins : List NatOpPinSet} {Γ Γ' : XEnv} {D : List Declaration}
    (h : AcceptsX pins Γ D Γ') (m : MMod V Γ) :
    ∃ m' : MMod V Γ', ∀ n, StoresX Γ n → StoresX Γ' n ∧ m'.1 n = m.1 n := by
  obtain ⟨hΓ', hall, k, q, hrun⟩ := h
  obtain ⟨-, -, hPL, mp, hcov, heta, hnat, hag⟩ := m.2
  have hPL' : ProofLeaves V Γ.1 mp.base2.acval := hPL.of_alike (fun n ci hf ψ =>
    denote_alike (R := Γ.1)
      (fun {x} hx => by
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
        exact ⟨c, c, hc, hc, .inl rfl⟩)
      (fun x hx => hag x hx) (fun _ => rfl) ψ 0 _
      (mp.base2.wf.consts ci (ConLeche.Env.find?_mem hf)).2.2.1) hag
  have key := declsRun_proofs hrun rfl mp hcov heta hnat hPL'
  have henv : q.2.env = Γ'.1 := by rw [declsRun_env .verified hrun, hΓ']; rfl
  rw [henv] at key
  obtain ⟨mp', hleaf, hcov', heta', hnat', hPL''⟩ := key
  refine ⟨⟨mp'.base2.acval, mp'.base2.cval_closed, mp'.base2.acval_wellDenoted, hPL'', mp', hcov',
    heta', hnat', fun _ _ => rfl⟩, fun n hn => ⟨⟨?_, hall n⟩, (hleaf n hn.1).trans (hag n hn.1)⟩⟩
  rw [hΓ']
  exact streamEnv_isSome_base D hn.1

/-! ## Proofs -/

/-- **`E` reads `ty` as `C` does**: every name of `ty` is stored by `C` and exposed by `E`, with
alike copies and one table. -/
@[expose] def ReadsX (C E : XEnv) (ty : Expr) : Prop :=
  ∀ c ∈ ty.readNames, StoresX C c ∧ E.2 c ∧ LookAlike (C.1.find? c) (E.1.find? c) ∧
    C.1.findTable? c = E.1.findTable? c

/-- **A proof by `C`** (see the module docstring): `E` stores `n` as a definition, theorem or axiom
whose type `C` infers to be a proposition and `E` reads as `C` does. -/
@[expose] def ProofInX (C E : XEnv) (n : Name) : Prop :=
  ∃ ci, E.1.find? n = some ci ∧ ci.isStmtKind = true ∧
    TypeIsProp .verified C.1 ci.toConstantVal.type ∧ ReadsX C E ci.toConstantVal.type

/-- **A proof by a theorem** (see the module docstring): `E` stores `n` as a definition, theorem or
axiom of the type of `E'`'s theorem `n`, which both read as `C` does. -/
@[expose] def ProofByX (C E E' : XEnv) (n : Name) : Prop :=
  ∃ ci cv, E.1.find? n = some ci ∧ ci.isStmtKind = true ∧ E'.1.find? n = some (.thmInfo cv) ∧
    cv.type = ci.toConstantVal.type ∧ ReadsX C E ci.toConstantVal.type ∧
    ReadsX C E' ci.toConstantVal.type

theorem LookAlike.symm {f g : Option ConstantInfo} (h : LookAlike f g) : LookAlike g f := by
  obtain ⟨a, b, h1, h2, h3⟩ := h
  exact ⟨b, a, h2, h1, h3.symm⟩

/-- **A type read alike reads alike** in a model of `C` and in a model of `E` that agree on `C`. -/
theorem ReadsX.denote_eq {C E : XEnv} {ty : Expr} (h : ReadsX C E ty) (mC : MMod V C)
    (m : MMod V E) (hag : ∀ c, StoresX C c → StoresX E c → mC.1 c = m.1 c) (ψ : Name → Nat) :
    denote m.1 E.1 ψ 0 ty = denote mC.1 C.1 ψ 0 ty := by
  classical
  -- the names the type reads, as an environment
  let q : Name → Bool := fun x => decide (x ∈ ty.readNames)
  let R : Env := ⟨C.1.consts.filter fun c => q c.toConstantVal.name, []⟩
  have hR : ∀ {x}, (R.find? x).isSome = true → x ∈ ty.readNames := fun {x} hx => by
    rw [find?_filter_name (t := C.1.tables)] at hx
    by_cases hq : q x = true
    · simpa [q] using hq
    · rw [ite_eq_right hq] at hx; exact nomatch hx
  have hresR : ty.constsResolve R = true :=
    Expr.constsResolve_of_readNames fun c hc => by
      rw [find?_filter_name (t := C.1.tables), ite_eq_left (by simpa [q] using hc)]
      exact (h c hc).1.1
  exact denote_alike (a₂ := mC.1) (E₂ := C.1) (R := R) (fun {x} hx => (h x (hR hx)).2.2.1.symm)
    (fun x hx => (hag x (h x (hR hx)).1 ⟨((h x (hR hx)).2.2.1.symm.elim
      fun a hb => by obtain ⟨b, h1, -, -⟩ := hb; rw [h1]; rfl), (h x (hR hx)).2.1⟩).symm)
    (fun {x} hx => (h x (hR hx)).2.2.2.symm) ψ 0 _ hresR

/-- **A proof by `C` gets the canonical proof** in every model agreeing on `C` with one of `C`. -/
theorem proofInX_val {C E : XEnv} {n : Name} (h : ProofInX C E n) (mC : MMod V C) (m : MMod V E)
    (hag : ∀ c, StoresX C c → StoresX E c → mC.1 c = m.1 c) : m.1 n = fun _ => .prf := by
  obtain ⟨ci, hf, hk, hprop, hnames⟩ := h
  obtain ⟨-, -, -, mpC, -, -, -, hagC⟩ := mC.2
  obtain ⟨-, -, hPL, mpE, -, -, -, -⟩ := m.2
  refine (hPL n ci hf hk).2 ?_
  -- the type's scoping, off the source's well-formedness
  have hwf := mpE.base2.wf.consts ci (ConLeche.Env.find?_mem hf)
  have htf : ci.toConstantVal.type.hasFvar = false := hwf.1
  have hsC := semPropType_of_run mpC (Expr.WScoped.of_not_hasFvar htf) hwf.2.2.2.1
    (fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar htf] at hl
      exact absurd hl List.not_mem_nil)
    (Expr.fvarLeaves_eq_nil_of_not_hasFvar htf) hprop
  have hresC : ci.toConstantVal.type.constsResolve C.1 = true :=
    Expr.constsResolve_of_readNames fun c hc => (hnames c hc).1.1
  refine SemPropType.of_denote (fun ψ => ?_) hsC
  rw [hnames.denote_eq mC m hag ψ]
  exact denote_alike (R := C.1) (fun {x} hx => by
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hx
      exact ⟨c, c, hc, hc, .inl rfl⟩)
    (fun x hx => (hagC x hx).symm) (fun _ => rfl) ψ 0 _ hresC

/-- **A proof by a theorem gets the canonical proof** in every model agreeing on `C` with one of
`C` that agrees on `C` with one of the theorem's environment. -/
theorem proofByX_val {C E E' : XEnv} {n : Name} (h : ProofByX C E E' n) (mC : MMod V C)
    (m : MMod V E) (m' : MMod V E') (hag : ∀ c, StoresX C c → StoresX E c → mC.1 c = m.1 c)
    (hag' : ∀ c, StoresX C c → StoresX E' c → mC.1 c = m'.1 c) : m.1 n = fun _ => .prf := by
  obtain ⟨ci, cv, hf, hk, hf', hty, hE, hE'⟩ := h
  -- the theorem's type reads as a truth value in its model, so in `C`'s, so in `E`'s
  have hs' := (m'.2.2.2.1 n _ hf' rfl).1 ⟨cv, rfl⟩
  rw [show (ConstantInfo.thmInfo cv).toConstantVal.type = ci.toConstantVal.type from hty] at hs'
  refine (m.2.2.2.1 n ci hf hk).2 (SemPropType.of_denote (fun ψ => hE.denote_eq mC m hag ψ) ?_)
  exact SemPropType.of_denote (fun ψ => (hE'.denote_eq mC m' hag' ψ).symm) hs'

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
  ProofIn := ProofInX
  proof_val h mC m hag := proofInX_val h mC m fun c hc hs => hag c hc hc hs
  ProofBy := ProofByX
  proofBy_val h mC m m' hag hag' := proofByX_val h mC m m' (fun c hc hs => hag c hc hc hs)
    fun c hc hs => hag' c hc hc hs
  Decls := List Declaration
  Accepts := AcceptsX pins
  step h m := h.step m

end ConLeche.Model.Modular
