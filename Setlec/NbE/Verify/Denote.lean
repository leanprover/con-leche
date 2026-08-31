import Setlec.NbE.Check
import Setlec.Verify.Level
import Setlec.SetTheory.Basic

/-!
# NbE pilot verification: denotations

The set-model interpretations of terms and values, parametric in the
campaign's own `SetTheory` interface (`Setlec/SetTheory/*`) — the same
target as the main campaign, so the comparison is apples-to-apples.

* `dTerm κ φ D t` — terms under a constant denotation `κ` (name +
  concrete levels → set), a level-parameter assignment `φ`, and a
  de Bruijn environment `D` (innermost first).  Total; out-of-scope
  indices denote the junk value `pt` (the front door excludes them).
* `dVal κ φ σ v` — values, additionally under a *fresh-variable*
  assignment `σ` (de Bruijn levels → sets).  A closure denotes the
  function `x ↦ dTerm κ φ (x :: dVals ρ) body`: the *same*
  environment-extension shape the machine itself uses — this is what
  makes the fundamental theorem's binder cases definitional.
* A glued neutral denotes its **spine** (head applied to arguments):
  the unfolded face never enters the denotation; the δ-coherence
  theorem (`Verify/Eval.lean`) relates the two.

Level transport: `dTerm_instL` is the *entire* substitution metatheory
of this tier — level instantiation commutes with denotation,
unconditionally (levels need no typing).  Compare the main campaign's
term-substitution transport, which is the dominant cost there; here
term substitution does not exist, so the corresponding lemma does not
either.

Scoping: `ScopedV k v` (all fresh-variable levels `< k`) with
`dVal_ext_σ` — the denotation depends on `σ` only below the frontier.
This is the NbE image of the campaign's scoped-call discipline
(ScopedSim): it reappears, but as one small structural induction over
values instead of a walk over checker call graphs.
-/

namespace Setlec.NbE

open Setlec.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- Positional level assignment: `ks` mapped to `ls`, default `0`. -/
def lvlAssign : List Name → List Nat → Name → Nat
  | k :: ks, l :: ls, n => if k = n then l else lvlAssign ks ls n
  | _, _, _ => 0

/-- Interpretation of terms.  `κ`: constant denotations; `φ`: level
parameters; `D`: de Bruijn environment, innermost first. -/
noncomputable def dTerm (κ : Name → List Nat → V) (φ : Name → Nat) :
    List V → Term → V
  | D, .bvar i => D.getD i pt
  | _, .sort u => univ (u.eval φ)
  | _, .const n us => κ n (us.map (Level.eval φ))
  | D, .app f a => SetTheory.app (dTerm κ φ D f) (dTerm κ φ D a)
  | D, .lam d b => lamC (dTerm κ φ D d) fun x => dTerm κ φ (x :: D) b
  | D, .pi d b => piC (dTerm κ φ D d) fun x => dTerm κ φ (x :: D) b

/-- Interpretation of a neutral head. -/
noncomputable def dHead (κ : Name → List Nat → V) (φ : Name → Nat)
    (σ : Nat → V) : Head → V
  | .fvar l => σ l
  | .const n us => κ n (us.map (Level.eval φ))

mutual

/-- Interpretation of values.  `σ`: fresh variables by de Bruijn level. -/
noncomputable def dVal (κ : Name → List Nat → V) (φ : Name → Nat)
    (σ : Nat → V) : Value → V
  | .sort u => univ (u.eval φ)
  | .pi d cl => piC (dVal κ φ σ d) fun x => dClosure κ φ σ cl x
  | .lam d cl => lamC (dVal κ φ σ d) fun x => dClosure κ φ σ cl x
  | .neu h args => (dVals κ φ σ args).foldl SetTheory.app (dHead κ φ σ h)

/-- A closure denotes environment-extension followed by `dTerm` — the
same shape the machine's `applyCl` has. -/
noncomputable def dClosure (κ : Name → List Nat → V) (φ : Name → Nat)
    (σ : Nat → V) : Closure → V → V
  | .mk ρ b, x => dTerm κ φ (x :: dVals κ φ σ ρ) b

noncomputable def dVals (κ : Name → List Nat → V) (φ : Name → Nat)
    (σ : Nat → V) : List Value → List V
  | [] => []
  | v :: vs => dVal κ φ σ v :: dVals κ φ σ vs

end

variable {κ : Name → List Nat → V} {φ : Name → Nat} {σ : Nat → V}

@[simp] theorem dVals_nil : dVals κ φ σ [] = [] := rfl
@[simp] theorem dVals_cons {v : Value} {vs : List Value} :
    dVals κ φ σ (v :: vs) = dVal κ φ σ v :: dVals κ φ σ vs := rfl

theorem dVals_append (as bs : List Value) :
    dVals κ φ σ (as ++ bs) = dVals κ φ σ as ++ dVals κ φ σ bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [dVals, ih]

theorem dVals_getD {ρ : List Value} {i : Nat} {v : Value}
    (h : ρ[i]? = some v) : (dVals κ φ σ ρ).getD i pt = dVal κ φ σ v := by
  induction ρ generalizing i with
  | nil => simp at h
  | cons a as ih =>
    cases i with
    | zero => simp_all
    | succ j =>
      simp only [List.getElem?_cons_succ] at h
      simpa using ih h

/-- The spine denotation, one argument at a time. -/
theorem dVal_neu_snoc (h : Head) (args : List Value) (a : Value) :
    dVal κ φ σ (.neu h (args ++ [a])) =
      SetTheory.app (dVal κ φ σ (.neu h args)) (dVal κ φ σ a) := by
  simp [dVal, dVals_append, dVals]

/-! ## Level transport

The one substitution-shaped lemma of the tier, and it is unconditional:
no typing, no well-formedness, no environment premise.  (Regime note:
`Level.eval_subst` and `Level.eval_ext` were established for the
kernel's `Level` syntax over all assignments; they transfer verbatim
because NbE carries that same syntax inside terms and values.) -/

theorem dTerm_instL (ks : List Name) (us : List Level) :
    ∀ (t : Term) (D : List V),
      dTerm κ φ D (t.instL ks us) = dTerm κ (Level.substFn φ ks us) D t := by
  intro t
  induction t with
  | bvar i => intro D; rfl
  | sort u => intro D; simp [Term.instL, dTerm, Level.eval_subst]
  | const n vs =>
    intro D
    simp only [Term.instL, dTerm, List.map_map]
    congr 1
    exact List.map_congr_left fun v _ => Level.eval_subst φ ks us v
  | app f a ihf iha => intro D; simp [Term.instL, dTerm, ihf, iha]
  | lam d b ihd ihb =>
    intro D
    simp only [Term.instL, dTerm, ihd]
    congr 1
    funext x
    exact ihb (x :: D)
  | pi d b ihd ihb =>
    intro D
    simp only [Term.instL, dTerm, ihd]
    congr 1
    funext x
    exact ihb (x :: D)

/-- `dTerm` depends on `φ` only at the parameters occurring in `t`. -/
theorem dTerm_ext_φ {ps : List Name} {φ₁ φ₂ : Name → Nat}
    (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (t : Term), t.lvlDefined ps = true →
      ∀ (D : List V), dTerm κ φ₁ D t = dTerm κ φ₂ D t := by
  intro t
  induction t with
  | bvar i => intro _ D; rfl
  | sort u =>
    intro h D
    simp only [Term.lvlDefined] at h
    simp [dTerm, Level.eval_ext h hφ]
  | const n vs =>
    intro h D
    simp only [Term.lvlDefined, List.all_eq_true] at h
    simp only [dTerm]
    congr 1
    exact List.map_congr_left fun v hv => Level.eval_ext (h v hv) hφ
  | app f a ihf iha =>
    intro h D
    simp only [Term.lvlDefined, Bool.and_eq_true] at h
    simp [dTerm, ihf h.1, iha h.2]
  | lam d b ihd ihb =>
    intro h D
    simp only [Term.lvlDefined, Bool.and_eq_true] at h
    simp only [dTerm, ihd h.1]
    congr 1
    funext x
    exact ihb h.2 (x :: D)
  | pi d b ihd ihb =>
    intro h D
    simp only [Term.lvlDefined, Bool.and_eq_true] at h
    simp only [dTerm, ihd h.1]
    congr 1
    funext x
    exact ihb h.2 (x :: D)

/-- The positional assignment agrees with the substitution assignment
on the substituted parameters (equal lengths, no duplicates). -/
theorem substFn_eq_lvlAssign :
    ∀ (ks : List Name) (us : List Level), Name.nodup ks = true →
      ks.length = us.length →
      ∀ p ∈ ks, Level.substFn φ ks us p = lvlAssign ks (us.map (Level.eval φ)) p := by
  intro ks
  induction ks with
  | nil => intro us _ _ p hp; simp at hp
  | cons k ks ih =>
    intro us hnd hlen p hp
    cases us with
    | nil => simp at hlen
    | cons u us =>
      simp only [Name.nodup, Bool.and_eq_true, Bool.not_eq_eq_eq_not,
        Bool.not_true, List.contains_eq_mem, decide_eq_false_iff_not] at hnd
      simp only [Level.substFn, List.map_cons, lvlAssign]
      rcases List.mem_cons.mp hp with rfl | hmem
      · simp
      · have hne : k ≠ p := fun h => hnd.1 (h ▸ hmem)
        rw [if_neg hne, if_neg hne]
        exact ih us hnd.2 (by simpa using hlen) p hmem

/-! ## Scoping

`ScopedV k v`: every fresh-variable level in `v` is `< k`. -/

mutual

def ScopedV (k : Nat) : Value → Prop
  | .sort _ => True
  | .pi d cl => ScopedV k d ∧ ScopedC k cl
  | .lam d cl => ScopedV k d ∧ ScopedC k cl
  | .neu h args => (match h with | .fvar l => l < k | .const _ _ => True) ∧
      ScopedL k args

def ScopedC (k : Nat) : Closure → Prop
  | .mk ρ _ => ScopedL k ρ

def ScopedL (k : Nat) : List Value → Prop
  | [] => True
  | v :: vs => ScopedV k v ∧ ScopedL k vs

end

mutual

theorem ScopedV.mono : ∀ {v : Value} {k k' : Nat}, k ≤ k' →
    ScopedV k v → ScopedV k' v
  | .sort _, _, _, _, h => h
  | .pi _ _, _, _, hk, ⟨hd, hcl⟩ => ⟨ScopedV.mono hk hd, ScopedC.mono hk hcl⟩
  | .lam _ _, _, _, hk, ⟨hd, hcl⟩ => ⟨ScopedV.mono hk hd, ScopedC.mono hk hcl⟩
  | .neu (.fvar _) _, _, _, hk, ⟨hl, hargs⟩ =>
      ⟨Nat.lt_of_lt_of_le hl hk, ScopedL.mono hk hargs⟩
  | .neu (.const _ _) _, _, _, hk, ⟨_, hargs⟩ =>
      ⟨trivial, ScopedL.mono hk hargs⟩

theorem ScopedC.mono : ∀ {cl : Closure} {k k' : Nat}, k ≤ k' →
    ScopedC k cl → ScopedC k' cl
  | .mk _ _, _, _, hk, hρ => ScopedL.mono hk hρ

theorem ScopedL.mono : ∀ {vs : List Value} {k k' : Nat}, k ≤ k' →
    ScopedL k vs → ScopedL k' vs
  | [], _, _, _, h => h
  | _ :: _, _, _, hk, ⟨hv, hvs⟩ => ⟨ScopedV.mono hk hv, ScopedL.mono hk hvs⟩

end

theorem scopedV_freshV {k : Nat} : ScopedV (k + 1) (freshV k) :=
  ⟨Nat.lt_succ_self k, trivial⟩

/- The denotation reads `σ` only below the scoping frontier. -/
mutual

theorem dVal_ext_σ {k : Nat} {σ σ' : Nat → V}
    (hσ : ∀ l, l < k → σ l = σ' l) :
    ∀ {v : Value}, ScopedV k v → dVal κ φ σ v = dVal κ φ σ' v
  | .sort _, _ => rfl
  | .pi _ cl, ⟨hd, hcl⟩ => by
    simp only [dVal, dVal_ext_σ hσ hd]
    congr 1
    funext x
    exact dClosure_ext_σ hσ hcl x
  | .lam _ cl, ⟨hd, hcl⟩ => by
    simp only [dVal, dVal_ext_σ hσ hd]
    congr 1
    funext x
    exact dClosure_ext_σ hσ hcl x
  | .neu (.fvar l) _, ⟨hl, hargs⟩ => by
    simp only [dVal, dVals_ext_σ hσ hargs, dHead, hσ l hl]
  | .neu (.const _ _) _, ⟨_, hargs⟩ => by
    simp only [dVal, dVals_ext_σ hσ hargs, dHead]

theorem dClosure_ext_σ {k : Nat} {σ σ' : Nat → V}
    (hσ : ∀ l, l < k → σ l = σ' l) :
    ∀ {cl : Closure}, ScopedC k cl → ∀ x : V,
      dClosure κ φ σ cl x = dClosure κ φ σ' cl x
  | .mk _ _, hρ, x => by simp only [dClosure, dVals_ext_σ hσ hρ]

theorem dVals_ext_σ {k : Nat} {σ σ' : Nat → V}
    (hσ : ∀ l, l < k → σ l = σ' l) :
    ∀ {vs : List Value}, ScopedL k vs → dVals κ φ σ vs = dVals κ φ σ' vs
  | [], _ => rfl
  | _ :: _, ⟨hv, hvs⟩ => by
    simp only [dVals, dVal_ext_σ hσ hv, dVals_ext_σ hσ hvs]

end

/-- Updating `σ` at the frontier: what a fresh variable at level `k`
denotes once the binder's argument is chosen. -/
def setAt (σ : Nat → V) (k : Nat) (x : V) : Nat → V :=
  fun l => if l = k then x else σ l

omit [SetTheory V] in
@[simp] theorem setAt_self (σ : Nat → V) (k : Nat) (x : V) :
    setAt σ k x k = x := by simp [setAt]

omit [SetTheory V] in
theorem setAt_lt {σ : Nat → V} {k l : Nat} (h : l < k) (x : V) :
    setAt σ k x l = σ l := by
  simp [setAt, Nat.ne_of_lt h]

@[simp] theorem dVal_freshV_setAt (k : Nat) (x : V) :
    dVal κ φ (setAt σ k x) (freshV k) = x := by
  simp [freshV, dVal, dVals, dHead]

end Setlec.NbE
