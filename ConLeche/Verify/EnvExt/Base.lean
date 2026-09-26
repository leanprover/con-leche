module

public import ConLeche.Verify.EnvExt.Scope
public import ConLeche.Verify.EnvWF
public import ConLeche.Verify.EnvPreds
public import ConLeche.Kernel.TypeChecker
import ConLeche.Verify.EnvExt.Knot

public section

/-!
# Env extension, part 9: the scope of a base environment

The consumer-facing form.  A BASE environment `B` (for the member tie:
the environment a home block was installed at) determines a scope
`InScope B`: its stored names, the fixed names, and everything derived
from those by `projTableName`/`projFnName`.  Two environments `E₁ E₂`
that both extend `B` (`FindPreserved`) and add no in-scope name `B`
lacks (`NoNewInScope`) agree on it (`Agree.ofBase`), given `B`'s own
invariants `EnvWF` and `RecCtorsStored`.  An input that resolves in `B`
(`Expr.constsResolve`) is in scope (`sc_of_constsResolve`).

So a kernel run on a term that resolves in `B` answers the same at every
pair of such environments (`whnf_base_agree`, …) — the extension lemma
(`E₁ := B`) and the member tie (`E₁ := env₁(H)`, the formers consed on
`B`; `E₂ :=` a later install's environment) alike.

`NoNewInScope` is where the audit's non-monotone sites live
(DESIGN.md, ENVEXT): a derived name (a structure's projection table or
projection function) or a fixed name (`PUnit`, the literal-guard names,
`And`'s table, the `Bool` constructors) that `B` lacks must not appear
later.  Both hold of fold environments once `B` is past the prelude and
past the installs of its own structures.
-/

namespace ConLeche.EnvExt

open ConLeche

/-- **The scope of a base environment**: its stored names, the fixed
names, closed under the derived projection-table and projection-function
names. -/
inductive InScope (B : Env) : Name → Prop where
  | stored {n : Name} : (B.find? n).isSome = true → InScope B n
  | fixed {n : Name} : n ∈ envExtFixedNames → InScope B n
  | table {T : Name} : InScope B T → InScope B (projTableName T)
  | projFn {T : Name} (j : Nat) : InScope B T → InScope B (projFnName T j)

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
  | lit l => intro _; simp
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

/-- **The agreement from a base.** -/
theorem Agree.ofBase {B E₁ E₂ : Env} (hwf : EnvWF B) (hctors : RecCtorsStored B)
    (hx₁ : Extends B E₁) (hn₁ : NoNewInScope B E₁)
    (hx₂ : Extends B E₂) (hn₂ : NoNewInScope B E₂) :
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
  fixed _ h := .fixed h

/-! ## The corollaries at a base -/

section Base

variable (mode : CheckMode) {B E₁ E₂ : Env} (hwf : EnvWF B) (hctors : RecCtorsStored B)
  (hx₁ : Extends B E₁) (hn₁ : NoNewInScope B E₁)
  (hx₂ : Extends B E₂) (hn₂ : NoNewInScope B E₂) {F d : Nat}
include hwf hctors hx₁ hn₁ hx₂ hn₂

/-- **Runs on a term resolving in the base agree** between any two
environments extending it without new in-scope names. -/
theorem whnf_base_agree {e : Expr} (he : e.constsResolve B = true) :
    whnf mode E₂ F d e = whnf mode E₁ F d e :=
  whnf_agree (Agree.ofBase hwf hctors hx₁ hn₁ hx₂ hn₂) (sc_of_constsResolve he)

theorem inferTypeCore_base_agree {e : Expr} (he : e.constsResolve B = true) :
    inferTypeCore mode E₂ F d e = inferTypeCore mode E₁ F d e :=
  inferTypeCore_agree (Agree.ofBase hwf hctors hx₁ hn₁ hx₂ hn₂) (sc_of_constsResolve he)

theorem isDefEqCore_base_agree {a b : Expr} (ha : a.constsResolve B = true)
    (hb : b.constsResolve B = true) :
    isDefEqCore mode E₂ F d a b = isDefEqCore mode E₁ F d a b :=
  isDefEqCore_agree (Agree.ofBase hwf hctors hx₁ hn₁ hx₂ hn₂) (sc_of_constsResolve ha)
    (sc_of_constsResolve hb)

theorem ensureSortCore_base_agree {e : Expr} (he : e.constsResolve B = true) :
    ensureSortCore mode E₂ F d e = ensureSortCore mode E₁ F d e :=
  ensureSortCore_agree (Agree.ofBase hwf hctors hx₁ hn₁ hx₂ hn₂) (sc_of_constsResolve he)

end Base

/-- **The extension lemma at a base** (`E₁ := B`): a successful `whnf`
run at `B` on a term resolving in `B` is the same run at every `E`
extending `B` without new in-scope names. -/
theorem whnf_extend_base (mode : CheckMode) {B E : Env} (hwf : EnvWF B)
    (hctors : RecCtorsStored B) (hx : Extends B E) (hn : NoNewInScope B E) {F d : Nat}
    {e r : Expr} (he : e.constsResolve B = true) (h : whnf mode B F d e = .ok r) :
    whnf mode E F d e = .ok r := by
  rw [whnf_base_agree mode hwf hctors (Extends.refl B) (NoNewInScope.refl B) hx hn he, h]

end ConLeche.EnvExt
