module

public import ConLeche.Model.Inductives.StructFrameKit

@[expose] public section

/-!
# A member's former: what the environment holds, what the check read

The environment holds the former the stream declared. The block's check reads its telescope,
which is the declared type itself or, for a type headed by a definition, its reduct. The two
are one family: this module states what ties them, for the model's proofs to read the telescope
while the environment answers with the declared constant.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps)

universe w

variable {V : Type w} [SetTheory V]

/-- **A member's declared former against the telescope its check read**: the two name one
family, each type is closed, and the two read as one value. -/
structure FormerDeclared {env : Env} (m : EnvModel V env) (cvS cvTa : ConstantVal) : Prop where
  name : cvS.name = cvTa.name
  lps : cvS.levelParams = cvTa.levelParams
  fvar : cvS.type.hasFvar = false
  defined : cvS.type.allLevelParamsDefined cvS.levelParams = true
  bounded : cvS.type.looseBVarsBounded 0 = true
  resolve : cvS.type.constsResolve env = true
  /-- the shape at a literal's name, off the constant's check -/
  shape : LitShapeAt cvS
  read : ∀ ψ : Name → Nat, ∃ Ts Tr : Term, denote m.acval env ψ 0 cvS.type = some Ts ∧
    denote m.acval env ψ 0 cvTa.type = some Tr ∧
    ∀ ρ : Nat → V, interp V ρ Ts = interp V ρ Tr ∧ WellDenotedTy V ρ Ts
  readFvar : cvTa.type.hasFvar = false
  readDefined : cvTa.type.allLevelParamsDefined cvTa.levelParams = true
  readBounded : cvTa.type.looseBVarsBounded 0 = true
  readResolve : cvTa.type.constsResolve env = true
  /-- a declared type that shows its telescope is what the check read; one that does not is at
  no literal's family -/
  shows : (ConLeche.formerDefHeaded cvS = true ∧ ConLeche.declinedAtDefinition.contains cvS.name = false)
    ∨ cvS = cvTa

/-- A former that shows its telescope, against itself. -/
theorem FormerDeclared.refl {env : Env} {m : EnvModel V env} {cv : ConstantVal} {nP : Nat}
    {resSort : Level} {pps : (Name → Nat) → List Term} (hFD : FormerData m cv nP resSort pps)
    (hf : cv.type.hasFvar = false) (hd : cv.type.allLevelParamsDefined cv.levelParams = true)
    (hb : cv.type.looseBVarsBounded 0 = true) (hr : cv.type.constsResolve env = true)
    (hs : LitShapeAt cv) :
    FormerDeclared m cv cv :=
  ⟨rfl, rfl, hf, hd, hb, hr, hs, fun ψ => ⟨_, _, hFD.read ψ, hFD.read ψ, fun ρ =>
    ⟨rfl, hFD.okTy ψ ρ, IsTy_mkPisAV_sort _ _ _⟩⟩, hf, hd, hb, hr, .inr rfl⟩

/-- A declared former's facts across a cons of a fresh constant. -/
theorem FormerDeclared.cross {env : Env} {m : EnvModel V env} {cvS cvTa : ConstantVal}
    (h : FormerDeclared m cvS cvTa) {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    {A : (Name → Nat) → Term} (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    FormerDeclared m₂ cvS cvTa := by
  refine ⟨h.name, h.lps, h.fvar, h.defined, h.bounded, Expr.constsResolve_mono h.resolve, h.shape,
    fun ψ => ?_, h.readFvar, h.readDefined, h.readBounded, Expr.constsResolve_mono h.readResolve,
    h.shows⟩
  obtain ⟨Ts, Tr, h₁, h₂, h₃⟩ := h.read ψ
  refine ⟨Ts, Tr, ?_, ?_, h₃⟩
  · rw [hac]; exact denote_cons_mono hfresh ψ 0 (constsBound_of_constsResolve _ h.resolve) h₁
  · rw [hac]; exact denote_cons_mono hfresh ψ 0 (constsBound_of_constsResolve _ h.readResolve) h₂

/-- A family's capability laws read its former only through its level parameters. -/
theorem CapsLawsAt.of_lps {env : Env} {m : EnvModel V env} {T : Name} {a b : ConstantVal}
    {caps : IndCaps} (h : CapsLawsAt m T a caps) (hl : a.levelParams = b.levelParams) :
    CapsLawsAt m T b caps := by
  unfold CapsLawsAt EtaLaw UnitLaw at h ⊢
  rwa [hl] at h

/-- A declared former's facts across a pushed table. -/
theorem FormerDeclared.pushTable {env : Env} {m : EnvModel V env} {cvS cvTa : ConstantVal}
    (h : FormerDeclared m cvS cvTa) {t : ConLeche.ProjTable}
    (hT : env.findTable? t.structName = none) (m₂ : EnvModel V ⟨env.consts, t :: env.tables⟩)
    (hac : m₂.acval = m.acval) : FormerDeclared m₂ cvS cvTa := by
  have hres : ∀ {e : Expr}, e.constsResolve env = true →
      e.constsResolve ⟨env.consts, t :: env.tables⟩ = true :=
    Expr.constsResolve_of_find fun n hn => by rw [Env.find?_pushTable]; exact hn
  refine ⟨h.name, h.lps, h.fvar, h.defined, h.bounded, hres h.resolve, h.shape, fun ψ => ?_, h.readFvar,
    h.readDefined, h.readBounded, hres h.readResolve, h.shows⟩
  obtain ⟨Ts, Tr, h₁, h₂, h₃⟩ := h.read ψ
  refine ⟨Ts, Tr, ?_, ?_, h₃⟩
  · rw [hac]; exact denote_pushTable_mono hT ψ 0 (constsBound_of_constsResolve _ h.resolve) h₁
  · rw [hac]; exact denote_pushTable_mono hT ψ 0 (constsBound_of_constsResolve _ h.readResolve) h₂

/-- **A member's former as the environment holds it**, under the name of the telescope `cvTa`
the check read. -/
def FormerInEnv {env : Env} (m : EnvModel V env) (cvTa : ConstantVal) (caps : IndCaps) : Prop :=
  ∃ cvS, env.find? cvTa.name = some (.indInfo cvS caps) ∧ FormerDeclared m cvS cvTa

/-- A stored former across a cons of a fresh constant. -/
theorem FormerInEnv.cross {env : Env} {m : EnvModel V env} {cvTa : ConstantVal} {caps : IndCaps}
    (h : FormerInEnv m cvTa caps) {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) (m₂ : EnvModel V ⟨c₀ :: env.consts, env.tables⟩)
    {A : (Name → Nat) → Term} (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    FormerInEnv m₂ cvTa caps := by
  obtain ⟨cvS, hf, hD⟩ := h
  exact ⟨cvS, ConLeche.Env.find?_cons_of_fresh hfresh hf, hD.cross hfresh m₂ hac⟩

/-- A stored former at any extension that reads every bound term alike. -/
theorem FormerInEnv.of_ext {envC envR : Env} {mC : EnvModel V envC} {mR : EnvModel V envR}
    {cvTa : ConstantVal} {caps : IndCaps} (h : FormerInEnv mC cvTa caps)
    (hfind : ∀ (n : Name) (c : ConstantInfo), envC.find? n = some c → envR.find? n = some c)
    (hden : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr), ConstsBound envC e →
      denote mR.acval envR ψ dd e = denote mC.acval envC ψ dd e) :
    FormerInEnv mR cvTa caps := by
  obtain ⟨cvS, hf, hD⟩ := h
  have hsome : ∀ n : Name, (envC.find? n).isSome = true → (envR.find? n).isSome = true := by
    intro n hn
    cases hc : envC.find? n with
    | none => rw [hc] at hn; exact nomatch hn
    | some c => rw [hfind n c hc]; rfl
  refine ⟨cvS, hfind _ _ hf, hD.name, hD.lps, hD.fvar, hD.defined, hD.bounded,
    Expr.constsResolve_of_find hsome hD.resolve, hD.shape, fun ψ => ?_, hD.readFvar, hD.readDefined,
    hD.readBounded, Expr.constsResolve_of_find hsome hD.readResolve, hD.shows⟩
  obtain ⟨Ts, Tr, h₁, h₂, h₃⟩ := hD.read ψ
  refine ⟨Ts, Tr, ?_, ?_, h₃⟩
  · rw [hden ψ 0 _ (constsBound_of_constsResolve _ hD.resolve)]; exact h₁
  · rw [hden ψ 0 _ (constsBound_of_constsResolve _ hD.readResolve)]; exact h₂

/-- The formers one pass stored, each against what the check read. -/
theorem formerInEnv_of {envI : Env} {m : EnvModel V envI} {dcl formers : List ConstantVal}
    {caps : Nat → IndCaps} {L : Nat → ConstantVal → Prop} (hlen : dcl.length = formers.length)
    (hD : ∀ (j : Nat) (cvS cvTa : ConstantVal), dcl[j]? = some cvS → formers[j]? = some cvTa →
      FormerDeclared m cvS cvTa)
    (hf : ∀ (j : Nat) (cvS cvTa : ConstantVal), dcl[j]? = some cvS → formers[j]? = some cvTa →
      envI.find? cvTa.name = some (.indInfo cvS (caps j)) ∧ L j cvTa) :
    ∀ (j : Nat) (cvTa : ConstantVal), formers[j]? = some cvTa →
      FormerInEnv m cvTa (caps j) ∧ L j cvTa := by
  intro j cvTa hj
  obtain ⟨cvS, hS⟩ : ∃ cvS, dcl[j]? = some cvS :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlen]; exact (List.getElem?_eq_some_iff.mp hj).1)⟩
  exact ⟨⟨cvS, (hf j cvS cvTa hS hj).1, hD j cvS cvTa hS hj⟩, (hf j cvS cvTa hS hj).2⟩

/-- The telescopes the block's check read are closed. -/
theorem formers_closed {env : Env} {m : EnvModel V env} {formers : List ConstantVal}
    {caps : Nat → IndCaps} {X : Nat → ConstantVal → Prop}
    (hF : ∀ (c : Nat) (cvTb : ConstantVal), formers[c]? = some cvTb →
      FormerInEnv m cvTb (caps c) ∧ X c cvTb) :
    ∀ cv ∈ formers, cv.type.hasFvar = false := by
  intro cv h
  obtain ⟨j, hj⟩ := List.getElem?_of_mem h
  obtain ⟨⟨_, _, hD⟩, _⟩ := hF j cv hj
  exact hD.readFvar

/-- The family inhabits the telescope the check read. -/
theorem FormerInEnv.mem {env : Env} {mp : EnvModelM V env} {cvTa : ConstantVal} {caps : IndCaps}
    (h : FormerInEnv mp.base2 cvTa caps) {ψ : Name → Nat} {T : Term}
    (hT : denote mp.base2.acval env ψ 0 cvTa.type = some T) (ρ : Nat → V) :
    interp V ρ (mp.base2.acval cvTa.name ψ) ∈ˢ interp V ρ T := by
  obtain ⟨cvS, hf, hD⟩ := h
  obtain ⟨Ts, Tr, hTs, hTr, hTeq⟩ := hD.read ψ
  obtain rfl := Option.some.inj (hTr.symm.trans hT)
  have hm := mp.mem_type _ (List.mem_of_find?_eq_some hf) ψ Ts hTs ρ
  rw [(hTeq ρ).1] at hm
  rw [← hD.name]
  exact hm

end ConLeche.Model
