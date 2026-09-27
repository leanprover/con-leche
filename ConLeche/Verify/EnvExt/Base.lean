module

public import ConLeche.Verify.EnvExt.Scope
public import ConLeche.Verify.EnvWF
public import ConLeche.Verify.EnvPreds
public import ConLeche.Kernel.TypeChecker
import ConLeche.Verify.EnvExt.Knot
import ConLeche.Verify.EnvGuards

public section

/-!
# Env extension, part 9: the scope of a base environment

The consumer-facing form.  A BASE environment `B` (for the member tie:
the environment a home block was installed at) determines a scope
`InScope B`: its stored names, the rest of the pinned `Nat` trio and
`PUnit.rec` once one of their block is stored, and everything derived
from those by `projTableName`/`projFnName`.  Two environments `E₁ E₂`
that both extend `B` (`Extends`), `E₂` extending `E₁`, and add no
in-scope name `B` lacks (`NoNewInScope`) agree on it (`Agree.ofBase`),
given `B`'s own invariants `EnvWF`, `RecCtorsStored` and `NatOpGuards`.
An input that resolves in `B` (`Expr.constsResolve`) is in scope
(`sc_of_constsResolve`).

So a kernel run on a term that resolves in `B` answers the same at every
pair of such environments (`whnf_base_agree`, …) — the extension lemma
(`E₁ := B`) and the member tie (`E₁ := env₁(H)`, the formers consed on
`B`; `E₂ :=` a later install's environment) alike.

`NoNewInScope` is where the audit's non-monotone sites live
(DESIGN.md, ENVEXT): a derived name (a structure's projection table or
projection function) that `B` lacks, or a missing member of a stored
pinned block, must not appear later.  Both hold of every fold
environment (`StepOk.noNewInScope`, `Fold.lean`) — no "past the
prelude" hypothesis: a name is in scope only when the input or a stored
constant names it, never merely for being looked up.
-/

namespace ConLeche.EnvExt

open ConLeche

/-- **The scope of a base environment**: its stored names, the pinned
`Nat` trio and `PUnit.rec` along with a stored member of their block,
closed under the derived projection-table and projection-function
names. -/
inductive InScope (B : Env) : Name → Prop where
  | stored {n : Name} : (B.find? n).isSome = true → InScope B n
  | natMate {n m : Name} : n ∈ natLitNames → InScope B n → m ∈ natLitNames → InScope B m
  | punitRec : InScope B punitName → InScope B punitRecName
  | table {T : Name} : InScope B T → InScope B (projTableName T)
  | projFn {T : Name} (j : Nat) : InScope B T → InScope B (projFnName T j)

/-- **The certified `Nat` operations' guards hold where they are
stored** (`EnvModelM`'s `NatOpGuardLaw`, stated `V`-free). -/
@[expose] def NatOpGuards (B : Env) : Prop :=
  ∀ c, (c ∈ natOpNames ∨ c ∈ natDivModNames) → natOpStored B c = true → natOpGuard B c = true

/-- `E` extends `B`: every stored lookup survives. -/
@[expose] def Extends (B E : Env) : Prop :=
  ∀ {n : Name} {ci : ConstantInfo}, B.find? n = some ci → E.find? n = some ci

/-- `E` adds no in-scope name that `B` lacks. -/
@[expose] def NoNewInScope (B E : Env) : Prop :=
  ∀ {n : Name}, InScope B n → B.find? n = none → E.find? n = none

theorem Extends.refl (B : Env) : Extends B B := fun h => h

theorem NoNewInScope.refl (B : Env) : NoNewInScope B B := fun _ h => h

/-- In-scope lookups at an extension adding no in-scope name are the
base's. -/
theorem find?_base {B E : Env} (hx : Extends B E) (hn : NoNewInScope B E) {n : Name}
    (h : InScope B n) : E.find? n = B.find? n := by
  cases hb : B.find? n with
  | none => exact hn h hb
  | some ci => exact hx hb

/-- A term resolving in `B` is in `B`'s scope. -/
theorem sc_of_constsResolve {B : Env} :
    ∀ {e : Expr}, e.constsResolve B = true → Sc (InScope B) e := by
  intro e
  induction e with
  | bvar i => intro _; simp
  | sort u => intro _; simp
  | lit l =>
    intro h
    refine sc_lit.mpr fun n hn => .stored ?_
    cases l with
    | natVal k =>
      simp only [Expr.constsResolve, Bool.and_eq_true] at h
      simp only [litNames, natLitNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl
      · exact h.1.1
      · exact h.1.2
      · exact h.2
    | strVal str =>
      simp only [Expr.constsResolve, Bool.and_eq_true] at h
      simp only [litNames, litGuardNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  | const n us =>
    intro h; simp only [Expr.constsResolve] at h
    exact sc_const.mpr (.stored h)
  | fvar idx ty ih =>
    intro h; simp only [Expr.constsResolve] at h
    exact sc_fvar.mpr (ih h)
  | app f a ihf iha =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact sc_app.mpr ⟨ihf h.1, iha h.2⟩
  | lam ty b m ihty ihb =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact sc_lam.mpr ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact sc_forallE.mpr ⟨ihty h.1, ihb h.2⟩
  | letE t v b iht ihv ihb =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact sc_letE.mpr ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s i e ihe =>
    intro h; simp only [Expr.constsResolve, Bool.and_eq_true] at h
    exact sc_proj.mpr ⟨.stored h.1, ihe h.2⟩

/-- The base's stored constants are in scope, from `EnvWF` and
`RecCtorsStored`. -/
theorem ciSc_of_base {B : Env} (hwf : EnvWF B) (hctors : RecCtorsStored B) {n : Name}
    {ci : ConstantInfo} (h : B.find? n = some ci) : CiSc (InScope B) ci := by
  have hmem : ci ∈ B.consts := List.mem_of_find?_eq_some h
  obtain ⟨-, -, hty, -, hdefn, hrec, htbl, -⟩ := hwf ci hmem
  have hty' := sc_of_constsResolve hty
  cases ci with
  | axiomInfo cv => exact hty'
  | defnInfo cv v hint =>
    exact ⟨hty', sc_of_constsResolve (hdefn cv v hint rfl).2.2.1⟩
  | thmInfo cv v => exact hty'
  | indInfo cv caps => exact hty'
  | ctorInfo cv _ _ => exact hty'
  | recInfo cv mI rP rules =>
    refine ⟨hty', fun rl hrl => ⟨?_, ?_, ?_⟩⟩
    · obtain ⟨⟨cvj, cnP, cnF, hj⟩, -, -⟩ := hctors n cv mI rP rules h rl hrl
      exact .stored (by rw [hj]; rfl)
    · exact sc_of_constsResolve (hrec cv mI rP rules rfl rl hrl).2.2.1
    · intro lvls pins hfire p hp
      exact sc_of_constsResolve
        (((hrec cv mI rP rules rfl rl hrl).2.2.2.2 lvls pins hfire).2.2.1 p hp).2.2.1
  | projInfo tbl =>
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hb
    have hb' : tbl.bodies[i]? = some tbl.bodies.toList[i] := by
      simp [Array.getElem?_eq_getElem (by simpa using hi)]
    exact sc_of_constsResolve ((htbl tbl rfl).2 i _ hb').2.2.1

/-- The guard's names, stored. -/
theorem natLitSupported_names {B : Env} (h : natLitSupported B = true) :
    ∀ m ∈ natLitNames, (B.find? m).isSome = true := by
  obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, h1, h2, h3, -⟩ := natLitSupported_inv h
  intro m hm
  simp only [natLitNames, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl
  · rw [h1]; rfl
  · rw [h2]; rfl
  · rw [h3]; rfl

/-- The `Nat` guard reads only its three names. -/
theorem natLitSupported_of_extends {E₁ E₂ : Env} (h₁₂ : Extends E₁ E₂)
    (h : natLitSupported E₁ = true) : natLitSupported E₂ = true := by
  have hs := natLitSupported_names h
  unfold natLitSupported at h ⊢
  have e : ∀ m ∈ natLitNames, E₂.find? m = E₁.find? m := fun m hm => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (hs m hm)
    rw [hci, h₁₂ hci]
  rw [e _ (by simp [natLitNames]), e _ (by simp [natLitNames]), e _ (by simp [natLitNames])]
  exact h

/-- **The agreement from a base.** -/
theorem Agree.ofBase {B E₁ E₂ : Env} (hwf : EnvWF B) (hctors : RecCtorsStored B)
    (hnat : NatOpGuards B)
    (hx₁ : Extends B E₁) (hn₁ : NoNewInScope B E₁)
    (hx₂ : Extends B E₂) (hn₂ : NoNewInScope B E₂) (h₁₂ : Extends E₁ E₂) :
    Agree (InScope B) E₁ E₂ where
  find h := by rw [find?_base hx₂ hn₂ h, find?_base hx₁ hn₁ h]
  closed h hf := by
    rw [find?_base hx₁ hn₁ h] at hf
    exact ciSc_of_base hwf hctors hf
  etaRule {n cv mI rP rules} h hf rl hrl heta := by
    rw [find?_base hx₁ hn₁ h] at hf
    have := (hctors n cv mI rP rules hf rl hrl).2.2 heta
    exact recRuleEtaOf_mono (fun _ _ _ hb => hx₁ hb) this
  table h := .table h
  projFn j h := .projFn j h
  natMate hn h m hm := .natMate hn h hm
  punitMate h := .punitRec h
  natOp {c} hc hst hmem := by
    have hst' : natOpStored B c = true := by
      unfold natOpStored at hst ⊢; rw [← find?_base hx₁ hn₁ hc]; exact hst
    have hg := hnat c hmem hst'
    unfold natOpGuard at hg
    simp only [Bool.and_eq_true] at hg
    obtain ⟨⟨hlit, -⟩, hbool⟩ := hg
    refine ⟨fun m hm => .stored (natLitSupported_names hlit m hm), fun hbe => ?_⟩
    have hc' : (c = natBeqName || c = natBleName || natDivModNames.contains c) = true := by
      rcases hbe with rfl | rfl <;> simp
    rw [if_pos hc'] at hbool
    simp only [Bool.and_eq_true] at hbool
    obtain ⟨h1, h2⟩ := hbool
    refine ⟨.stored ?_, .stored ?_⟩
    · revert h1; cases B.find? boolTrueName <;> simp
    · revert h2; cases B.find? boolFalseName <;> simp
  natLit h := natLitSupported_of_extends h₁₂ h

/-! ## The corollaries at a base -/

section Base

variable (mode : CheckMode) {B E₁ E₂ : Env} (hwf : EnvWF B) (hctors : RecCtorsStored B)
  (hnat : NatOpGuards B)
  (hx₁ : Extends B E₁) (hn₁ : NoNewInScope B E₁)
  (hx₂ : Extends B E₂) (hn₂ : NoNewInScope B E₂) (h₁₂ : Extends E₁ E₂) {F d : Nat}
include hwf hctors hnat hx₁ hn₁ hx₂ hn₂ h₁₂

/-- **A later run on a term resolving in the base reproduces the
earlier one**: at two environments extending the base without new
in-scope names, the later one extending the earlier, a success of the
later run is the earlier run's. -/
theorem whnf_base_agree {e r : Expr} (he : e.constsResolve B = true)
    (h : whnf mode E₂ F d e = .ok r) : whnf mode E₁ F d e = .ok r :=
  (whnf_agree (Agree.ofBase hwf hctors hnat hx₁ hn₁ hx₂ hn₂ h₁₂) (sc_of_constsResolve he) h).1

theorem inferTypeCore_base_agree {e r : Expr} (he : e.constsResolve B = true)
    (h : inferTypeCore mode E₂ F d e = .ok r) : inferTypeCore mode E₁ F d e = .ok r :=
  (inferTypeCore_agree (Agree.ofBase hwf hctors hnat hx₁ hn₁ hx₂ hn₂ h₁₂)
    (sc_of_constsResolve he) h).1

theorem isDefEqCore_base_agree {a b : Expr} {v : Bool} (ha : a.constsResolve B = true)
    (hb : b.constsResolve B = true) (h : isDefEqCore mode E₂ F d a b = .ok v) :
    isDefEqCore mode E₁ F d a b = .ok v :=
  isDefEqCore_agree (Agree.ofBase hwf hctors hnat hx₁ hn₁ hx₂ hn₂ h₁₂) (sc_of_constsResolve ha)
    (sc_of_constsResolve hb) h

theorem ensureSortCore_base_agree {e : Expr} {u : Level} (he : e.constsResolve B = true)
    (h : ensureSortCore mode E₂ F d e = .ok u) : ensureSortCore mode E₁ F d e = .ok u :=
  ensureSortCore_agree (Agree.ofBase hwf hctors hnat hx₁ hn₁ hx₂ hn₂ h₁₂)
    (sc_of_constsResolve he) h

end Base

end ConLeche.EnvExt
