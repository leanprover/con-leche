module

public import Fragment.WellDenoted
public import Fragment.Scope

@[expose] public section

/-!
# Hygiene: what a term is read through

The congruence lemmas for the four syntactic *scope* predicates of
`Scope.lean`, saying that the interpretation (`interp`) and the invariant
(`WellDenoted`) read a term only through

* the variables below its scope — `Expr.closedAt k`: every bound
  variable is below `k`, so two environments agreeing below `k` give
  the same reading;
* the constants it mentions — `Expr.consts`: two models agreeing on
  those constants (at every level instantiation) give the same
  reading;
* the level parameters it uses — `Expr.lparamsIn ps`: every
  parameter in a sort or a constant's instantiation is one of `ps`, so
  two valuations agreeing on `ps` give the same reading;
* the variables it uses — `Expr.usesVar i`, finer than the depth:
  two environments agreeing at every variable the term uses give the
  same reading.

The predicates are closed under lifting, instantiation, level
instantiation and spine formation (the closure lemmas), which is what
the environment section needs to move them from a stored declaration
to its uses.

Mirrors the scoping side of `ConLeche/Semantics/*` on the fragment's
syntax.
-/

namespace Fragment
open SetLib

universe u

namespace Level

@[simp] theorem paramsIn_zero (ps : List Name) : paramsIn ps zero = true := rfl
@[simp] theorem paramsIn_succ (ps : List Name) (l : Level) :
    paramsIn ps (succ l) = paramsIn ps l := rfl
@[simp] theorem paramsIn_max (ps : List Name) (a b : Level) :
    paramsIn ps (max a b) = (paramsIn ps a && paramsIn ps b) := rfl
@[simp] theorem paramsIn_imax (ps : List Name) (a b : Level) :
    paramsIn ps (imax a b) = (paramsIn ps a && paramsIn ps b) := rfl
@[simp] theorem paramsIn_param (ps : List Name) (n : Name) :
    paramsIn ps (param n) = ps.contains n := rfl

/-- A level's value depends only on the valuation at its parameters. -/
theorem eval_congr {ps : List Name} {φ φ' : Name → Nat} (h : ∀ n ∈ ps, φ n = φ' n) :
    ∀ {l : Level}, paramsIn ps l = true → eval φ l = eval φ' l
  | zero, _ => rfl
  | succ l, hl => by
    rw [paramsIn_succ] at hl
    simp only [eval_succ, eval_congr h hl]
  | max a b, hl => by
    simp only [paramsIn_max, Bool.and_eq_true] at hl
    simp only [eval_max, eval_congr h hl.1, eval_congr h hl.2]
  | imax a b, hl => by
    simp only [paramsIn_imax, Bool.and_eq_true] at hl
    simp only [eval_imax, eval_congr h hl.1, eval_congr h hl.2]
  | param n, hl => by
    rw [paramsIn_param, List.contains_iff_mem] at hl
    exact h n hl

end Level

namespace Expr

/-! ## The four scope predicates -/

@[simp] theorem closedAt_bvar (k i : Nat) : closedAt k (bvar i) = decide (i < k) := rfl
@[simp] theorem closedAt_sort (k : Nat) (u : Level) : closedAt k (sort u) = true := rfl
@[simp] theorem closedAt_const (k : Nat) (c : Name) (ls : List Level) :
    closedAt k (const c ls) = true := rfl
@[simp] theorem closedAt_app (k : Nat) (f a : Expr) :
    closedAt k (app f a) = (closedAt k f && closedAt k a) := rfl
@[simp] theorem closedAt_lam (k : Nat) (A : Expr) (b : Expr) :
    closedAt k (lam A b) = (closedAt k A && closedAt (k + 1) b) := rfl
@[simp] theorem closedAt_pi (k : Nat) (A : Expr) (B : Expr) :
    closedAt k (pi A B) = (closedAt k A && closedAt (k + 1) B) := rfl
@[simp] theorem closedAt_letE (k : Nat) (T v b : Expr) :
    closedAt k (letE T v b) = (closedAt k T && closedAt k v && closedAt (k + 1) b) := rfl

@[simp] theorem consts_bvar (i : Nat) : consts (bvar i) = [] := rfl
@[simp] theorem consts_sort (u : Level) : consts (sort u) = [] := rfl
@[simp] theorem consts_const (c : Name) (ls : List Level) : consts (const c ls) = [c] := rfl
@[simp] theorem consts_app (f a : Expr) : consts (app f a) = consts f ++ consts a := rfl
@[simp] theorem consts_lam (A : Expr) (b : Expr) :
    consts (lam A b) = consts A ++ consts b := rfl
@[simp] theorem consts_pi (A : Expr) (B : Expr) :
    consts (pi A B) = consts A ++ consts B := rfl
@[simp] theorem consts_letE (T v b : Expr) :
    consts (letE T v b) = consts T ++ consts v ++ consts b := rfl

@[simp] theorem lparamsIn_bvar (ps : List Name) (i : Nat) : lparamsIn ps (bvar i) = true := rfl
@[simp] theorem lparamsIn_sort (ps : List Name) (u : Level) :
    lparamsIn ps (sort u) = u.paramsIn ps := rfl
@[simp] theorem lparamsIn_const (ps : List Name) (c : Name) (ls : List Level) :
    lparamsIn ps (const c ls) = ls.all (Level.paramsIn ps) := rfl
@[simp] theorem lparamsIn_app (ps : List Name) (f a : Expr) :
    lparamsIn ps (app f a) = (lparamsIn ps f && lparamsIn ps a) := rfl
@[simp] theorem lparamsIn_lam (ps : List Name) (A : Expr) (b : Expr) :
    lparamsIn ps (lam A b) = (lparamsIn ps A && lparamsIn ps b) := rfl
@[simp] theorem lparamsIn_pi (ps : List Name) (A : Expr) (B : Expr) :
    lparamsIn ps (pi A B) = (lparamsIn ps A && lparamsIn ps B) := rfl
@[simp] theorem lparamsIn_letE (ps : List Name) (T v b : Expr) :
    lparamsIn ps (letE T v b) = (lparamsIn ps T && lparamsIn ps v && lparamsIn ps b) := rfl

@[simp] theorem usesVar_bvar (i j : Nat) : usesVar i (bvar j) = decide (j = i) := rfl
@[simp] theorem usesVar_sort (i : Nat) (u : Level) : usesVar i (sort u) = false := rfl
@[simp] theorem usesVar_const (i : Nat) (c : Name) (ls : List Level) :
    usesVar i (const c ls) = false := rfl
@[simp] theorem usesVar_app (i : Nat) (f a : Expr) :
    usesVar i (app f a) = (usesVar i f || usesVar i a) := rfl
@[simp] theorem usesVar_lam (i : Nat) (A : Expr) (b : Expr) :
    usesVar i (lam A b) = (usesVar i A || usesVar (i + 1) b) := rfl
@[simp] theorem usesVar_pi (i : Nat) (A : Expr) (B : Expr) :
    usesVar i (pi A B) = (usesVar i A || usesVar (i + 1) B) := rfl
@[simp] theorem usesVar_letE (i : Nat) (T v b : Expr) :
    usesVar i (letE T v b) = (usesVar i T || usesVar i v || usesVar (i + 1) b) := rfl

/-! ## Closure

The predicates through lifting, instantiation, level instantiation
and spine formation. -/

/-- A term closed below `j` is closed below any `k ≥ j`. -/
theorem closedAt_mono {j k : Nat} (h : j ≤ k) :
    ∀ {e : Expr}, closedAt j e = true → closedAt k e = true
  | bvar i, he => by
    simp only [closedAt_bvar, decide_eq_true_eq] at he ⊢
    omega
  | sort _, _ => rfl
  | const _ _, _ => rfl
  | app f a, he => by
    simp only [closedAt_app, Bool.and_eq_true] at he ⊢
    exact ⟨closedAt_mono h he.1, closedAt_mono h he.2⟩
  | lam A b, he => by
    simp only [closedAt_lam, Bool.and_eq_true] at he ⊢
    exact ⟨closedAt_mono h he.1, closedAt_mono (Nat.succ_le_succ h) he.2⟩
  | pi A B, he => by
    simp only [closedAt_pi, Bool.and_eq_true] at he ⊢
    exact ⟨closedAt_mono h he.1, closedAt_mono (Nat.succ_le_succ h) he.2⟩
  | letE T v b, he => by
    simp only [closedAt_letE, Bool.and_eq_true] at he ⊢
    exact ⟨⟨closedAt_mono h he.1.1, closedAt_mono h he.1.2⟩,
      closedAt_mono (Nat.succ_le_succ h) he.2⟩

/-- Lifting by `n` (at any cut `k`) keeps a term closed, `n` binders
higher. -/
theorem closedAt_liftN {n : Nat} :
    ∀ {e : Expr} {k j : Nat}, closedAt j e = true → closedAt (j + n) (liftN n e k) = true
  | bvar i, k, j, he => by
    simp only [closedAt_bvar, decide_eq_true_eq, liftN_bvar] at he ⊢
    split <;> omega
  | sort _, _, _, _ => rfl
  | const _ _, _, _, _ => rfl
  | app f a, k, j, he => by
    simp only [closedAt_app, Bool.and_eq_true, liftN_app] at he ⊢
    exact ⟨closedAt_liftN he.1, closedAt_liftN he.2⟩
  | lam A b, k, j, he => by
    simp only [closedAt_lam, Bool.and_eq_true, liftN_lam] at he ⊢
    refine ⟨closedAt_liftN he.1, ?_⟩
    rw [Nat.add_right_comm]
    exact closedAt_liftN he.2
  | pi A B, k, j, he => by
    simp only [closedAt_pi, Bool.and_eq_true, liftN_pi] at he ⊢
    refine ⟨closedAt_liftN he.1, ?_⟩
    rw [Nat.add_right_comm]
    exact closedAt_liftN he.2
  | letE T v b, k, j, he => by
    simp only [closedAt_letE, Bool.and_eq_true, liftN_letE] at he ⊢
    refine ⟨⟨closedAt_liftN he.1.1, closedAt_liftN he.1.2⟩, ?_⟩
    rw [Nat.add_right_comm]
    exact closedAt_liftN he.2

/-- Level instantiation touches no bound variable. -/
theorem closedAt_instL {ps : List Name} {ls : List Level} :
    ∀ {k : Nat} {e : Expr}, closedAt k (instL ps ls e) = closedAt k e
  | _, bvar _ => rfl
  | _, sort _ => rfl
  | _, const _ _ => rfl
  | _, app _ _ => by simp only [instL_app, closedAt_app, closedAt_instL]
  | _, lam _ _ => by simp only [instL_lam, closedAt_lam, closedAt_instL]
  | _, pi _ _ => by simp only [instL_pi, closedAt_pi, closedAt_instL]
  | _, letE _ _ _ => by simp only [instL_letE, closedAt_letE, closedAt_instL]

/-- Lifting mentions the same constants. -/
theorem consts_liftN (n : Nat) : ∀ (k : Nat) (e : Expr), consts (liftN n e k) = consts e
  | _, bvar _ => rfl
  | _, sort _ => rfl
  | _, const _ _ => rfl
  | k, app f a => by simp only [liftN_app, consts_app, consts_liftN n k]
  | k, lam A b => by
    simp only [liftN_lam, consts_lam, consts_liftN n k, consts_liftN n (k + 1)]
  | k, pi A B => by
    simp only [liftN_pi, consts_pi, consts_liftN n k, consts_liftN n (k + 1)]
  | k, letE T v b => by
    simp only [liftN_letE, consts_letE, consts_liftN n k, consts_liftN n (k + 1)]

/-- Level instantiation mentions the same constants. -/
theorem consts_instL (ps : List Name) (ls : List Level) :
    ∀ e : Expr, consts (instL ps ls e) = consts e
  | bvar _ => rfl
  | sort _ => rfl
  | const _ _ => rfl
  | app _ _ => by simp only [instL_app, consts_app, consts_instL ps ls]
  | lam _ _ => by simp only [instL_lam, consts_lam, consts_instL ps ls]
  | pi _ _ => by simp only [instL_pi, consts_pi, consts_instL ps ls]
  | letE _ _ _ => by simp only [instL_letE, consts_letE, consts_instL ps ls]

/-- An instance mentions only the constants of the term and of the
substituted argument. -/
theorem consts_inst {a : Expr} :
    ∀ {e : Expr} {k : Nat} {c : Name}, c ∈ consts (inst e a k) → c ∈ consts e ∨ c ∈ consts a
  | bvar i, k, c, hc => by
    rw [inst_bvar] at hc
    split at hc
    · simp at hc
    · split at hc
      · rw [consts_liftN] at hc
        exact Or.inr hc
      · simp at hc
  | sort _, _, _, hc => by simp at hc
  | const _ _, _, _, hc => by
    rw [inst_const] at hc
    exact Or.inl hc
  | app f b, k, c, hc => by
    rw [inst_app, consts_app, List.mem_append] at hc
    rw [consts_app, List.mem_append]
    rcases hc with hc | hc
    · rcases consts_inst hc with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases consts_inst hc with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | lam A b, k, c, hc => by
    rw [inst_lam, consts_lam, List.mem_append] at hc
    rw [consts_lam, List.mem_append]
    rcases hc with hc | hc
    · rcases consts_inst hc with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases consts_inst hc with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | pi A B, k, c, hc => by
    rw [inst_pi, consts_pi, List.mem_append] at hc
    rw [consts_pi, List.mem_append]
    rcases hc with hc | hc
    · rcases consts_inst hc with h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rcases consts_inst hc with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  | letE T v b, k, c, hc => by
    rw [inst_letE, consts_letE, List.mem_append, List.mem_append] at hc
    rw [consts_letE, List.mem_append, List.mem_append]
    rcases hc with (hc | hc) | hc
    · rcases consts_inst hc with h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inr h
    · rcases consts_inst hc with h | h
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inr h
    · rcases consts_inst hc with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

/-- Instantiation keeps every constant of the term (task #342, F4: a
`let` typed through its instantiated body mentions the body's). -/
theorem consts_of_inst {a : Expr} :
    ∀ {e : Expr} {k : Nat} {c : Name}, c ∈ consts e → c ∈ consts (inst e a k)
  | bvar _, _, _, hc => by simp at hc
  | sort _, _, _, hc => by simp at hc
  | const _ _, _, _, hc => hc
  | app f b, k, c, hc => by
    simp only [consts_app, inst_app, List.mem_append] at hc ⊢
    exact hc.imp consts_of_inst consts_of_inst
  | lam A b, k, c, hc => by
    simp only [consts_lam, inst_lam, List.mem_append] at hc ⊢
    exact hc.imp consts_of_inst consts_of_inst
  | pi A B, k, c, hc => by
    simp only [consts_pi, inst_pi, List.mem_append] at hc ⊢
    exact hc.imp consts_of_inst consts_of_inst
  | letE T v b, k, c, hc => by
    simp only [consts_letE, inst_letE, List.mem_append] at hc ⊢
    exact hc.imp (fun h => h.imp consts_of_inst consts_of_inst) consts_of_inst

/-- An instance closed below `n` at a cut `k ≤ n` comes from a term
closed below `n + 1` (task #342, F4). -/
theorem closedAt_of_inst {a : Expr} :
    ∀ {e : Expr} {k n : Nat}, k ≤ n → closedAt n (inst e a k) = true →
      closedAt (n + 1) e = true
  | bvar i, k, n, hk, he => by
    simp only [inst_bvar] at he
    simp only [closedAt_bvar, decide_eq_true_eq]
    by_cases h1 : i < k
    · omega
    · by_cases h2 : i = k
      · omega
      · rw [ite_eq_right h1, ite_eq_right h2, closedAt_bvar, decide_eq_true_eq] at he
        omega
  | sort _, _, _, _, _ => rfl
  | const _ _, _, _, _, _ => rfl
  | app f b, k, n, hk, he => by
    simp only [inst_app, closedAt_app, Bool.and_eq_true] at he ⊢
    exact ⟨closedAt_of_inst hk he.1, closedAt_of_inst hk he.2⟩
  | lam A b, k, n, hk, he => by
    simp only [inst_lam, closedAt_lam, Bool.and_eq_true] at he ⊢
    exact ⟨closedAt_of_inst hk he.1, closedAt_of_inst (Nat.succ_le_succ hk) he.2⟩
  | pi A B, k, n, hk, he => by
    simp only [inst_pi, closedAt_pi, Bool.and_eq_true] at he ⊢
    exact ⟨closedAt_of_inst hk he.1, closedAt_of_inst (Nat.succ_le_succ hk) he.2⟩
  | letE T v b, k, n, hk, he => by
    simp only [inst_letE, closedAt_letE, Bool.and_eq_true] at he ⊢
    exact ⟨⟨closedAt_of_inst hk he.1.1, closedAt_of_inst hk he.1.2⟩,
      closedAt_of_inst (Nat.succ_le_succ hk) he.2⟩

/-- Lifting uses the same level parameters. -/
theorem lparamsIn_liftN {ps : List Name} {n : Nat} :
    ∀ {k : Nat} {e : Expr}, lparamsIn ps (liftN n e k) = lparamsIn ps e
  | _, bvar _ => rfl
  | _, sort _ => rfl
  | _, const _ _ => rfl
  | _, app _ _ => by simp only [liftN_app, lparamsIn_app, lparamsIn_liftN]
  | _, lam _ _ => by simp only [liftN_lam, lparamsIn_lam, lparamsIn_liftN]
  | _, pi _ _ => by simp only [liftN_pi, lparamsIn_pi, lparamsIn_liftN]
  | _, letE _ _ _ => by simp only [liftN_letE, lparamsIn_letE, lparamsIn_liftN]

/-- A lifted term uses a variable either below the cut, where the
term used it as is, or above the cut and the shift, where the term
used it `n` lower. -/
theorem usesVar_liftN {n : Nat} :
    ∀ {e : Expr} {i k : Nat}, usesVar i (liftN n e k) = true →
      (i < k ∧ usesVar i e = true) ∨ (k + n ≤ i ∧ usesVar (i - n) e = true)
  | bvar j, i, k, h => by
    simp only [liftN_bvar, usesVar_bvar, decide_eq_true_eq] at h ⊢
    split at h <;> omega
  | sort _, _, _, h => by simp at h
  | const _ _, _, _, h => by simp at h
  | app f a, i, k, h => by
    simp only [liftN_app, usesVar_app, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases usesVar_liftN h with ⟨hi, h⟩ | ⟨hi, h⟩
      · exact Or.inl ⟨hi, Or.inl h⟩
      · exact Or.inr ⟨hi, Or.inl h⟩
    · rcases usesVar_liftN h with ⟨hi, h⟩ | ⟨hi, h⟩
      · exact Or.inl ⟨hi, Or.inr h⟩
      · exact Or.inr ⟨hi, Or.inr h⟩
  | lam A b, i, k, h => by
    simp only [liftN_lam, usesVar_lam, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases usesVar_liftN h with ⟨hi, h⟩ | ⟨hi, h⟩
      · exact Or.inl ⟨hi, Or.inl h⟩
      · exact Or.inr ⟨hi, Or.inl h⟩
    · rcases usesVar_liftN h with ⟨hi, h⟩ | ⟨hi, h⟩
      · exact Or.inl ⟨by omega, Or.inr h⟩
      · rw [show i + 1 - n = i - n + 1 by omega] at h
        exact Or.inr ⟨by omega, Or.inr h⟩
  | pi A B, i, k, h => by
    simp only [liftN_pi, usesVar_pi, Bool.or_eq_true] at h ⊢
    rcases h with h | h
    · rcases usesVar_liftN h with ⟨hi, h⟩ | ⟨hi, h⟩
      · exact Or.inl ⟨hi, Or.inl h⟩
      · exact Or.inr ⟨hi, Or.inl h⟩
    · rcases usesVar_liftN h with ⟨hi, h⟩ | ⟨hi, h⟩
      · exact Or.inl ⟨by omega, Or.inr h⟩
      · rw [show i + 1 - n = i - n + 1 by omega] at h
        exact Or.inr ⟨by omega, Or.inr h⟩
  | letE T v b, i, k, h => by
    simp only [liftN_letE, usesVar_letE, Bool.or_eq_true] at h ⊢
    rcases h with (h | h) | h
    · rcases usesVar_liftN h with ⟨hi, h⟩ | ⟨hi, h⟩
      · exact Or.inl ⟨hi, Or.inl (Or.inl h)⟩
      · exact Or.inr ⟨hi, Or.inl (Or.inl h)⟩
    · rcases usesVar_liftN h with ⟨hi, h⟩ | ⟨hi, h⟩
      · exact Or.inl ⟨hi, Or.inl (Or.inr h)⟩
      · exact Or.inr ⟨hi, Or.inl (Or.inr h)⟩
    · rcases usesVar_liftN h with ⟨hi, h⟩ | ⟨hi, h⟩
      · exact Or.inl ⟨by omega, Or.inr h⟩
      · rw [show i + 1 - n = i - n + 1 by omega] at h
        exact Or.inr ⟨by omega, Or.inr h⟩

/-- A spine is closed when its head and arguments are. -/
theorem closedAt_mkAppN {k : Nat} :
    ∀ {f : Expr} {args : List Expr}, closedAt k f = true →
      (∀ a ∈ args, closedAt k a = true) → closedAt k (mkAppN f args) = true
  | _, [], hf, _ => hf
  | f, a :: args, hf, hargs => by
    rw [mkAppN_cons]
    refine closedAt_mkAppN ?_ fun b hb => hargs b (List.mem_cons_of_mem a hb)
    rw [closedAt_app, hf, hargs a List.mem_cons_self]
    rfl

/-- The constants of a spine: the head's, then each argument's. -/
theorem consts_mkAppN : ∀ (f : Expr) (args : List Expr),
    consts (mkAppN f args) = consts f ++ args.flatMap consts
  | _, [] => by simp
  | f, a :: args => by
    rw [mkAppN_cons, consts_mkAppN, consts_app, List.flatMap_cons, List.append_assoc]

/-- A spine uses the level parameters of its head and arguments. -/
theorem lparamsIn_mkAppN {ps : List Name} :
    ∀ {f : Expr} {args : List Expr}, lparamsIn ps f = true →
      (∀ a ∈ args, lparamsIn ps a = true) → lparamsIn ps (mkAppN f args) = true
  | _, [], hf, _ => hf
  | f, a :: args, hf, hargs => by
    rw [mkAppN_cons]
    refine lparamsIn_mkAppN ?_ fun b hb => hargs b (List.mem_cons_of_mem a hb)
    rw [lparamsIn_app, hf, hargs a List.mem_cons_self]
    rfl

/-- A spine uses a variable only if its head or one of its arguments
does. -/
theorem usesVar_mkAppN {i : Nat} :
    ∀ {f : Expr} {args : List Expr}, usesVar i (mkAppN f args) = true →
      usesVar i f = true ∨ ∃ a ∈ args, usesVar i a = true
  | _, [], h => Or.inl h
  | f, a :: args, h => by
    rw [mkAppN_cons] at h
    rcases usesVar_mkAppN h with h | ⟨b, hb, h⟩
    · rw [usesVar_app, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨a, List.mem_cons_self, h⟩
    · exact Or.inr ⟨b, List.mem_cons_of_mem a hb, h⟩

end Expr

/-! ## The congruence lemmas

The interpretation and the invariant read a term only through the
four scopes. -/

variable {V : Type u}

/-- Two environments agreeing below `k` agree below `k + 1` once
extended by the same value. -/
theorem cons_congr_lt {k : Nat} {ρ ρ' : Nat → V} (h : ∀ i, i < k → ρ i = ρ' i) (x : V) :
    ∀ i, i < k + 1 → cons x ρ i = cons x ρ' i
  | 0, _ => rfl
  | i + 1, hi => h i (by omega)

/-- Two environments agreeing at the variables `i` with `p (i + 1)`
agree, once extended by the same value, at the variables with `p i`:
`p` is the use predicate of a binder's body, `p (· + 1)` the one it
induces on the enclosing context. -/
theorem cons_congr_succ {p : Nat → Prop} {ρ ρ' : Nat → V} (h : ∀ i, p (i + 1) → ρ i = ρ' i)
    (x : V) : ∀ i, p i → cons x ρ i = cons x ρ' i
  | 0, _ => rfl
  | i + 1, hi => h i hi

variable [SetLib V] {M M' : Name → List Nat → V} {φ φ' : Name → Nat}

/-- **Variables.**  The interpretation of a term closed below `k` reads
the environment below `k` only. -/
theorem interp_closedAt {k : Nat} {e : Expr} (he : e.closedAt k = true) {ρ ρ' : Nat → V}
    (h : ∀ i, i < k → ρ i = ρ' i) : interp M φ ρ e = interp M φ ρ' e := by
  induction e generalizing k ρ ρ' with
  | bvar i =>
    simp only [Expr.closedAt_bvar, decide_eq_true_eq] at he
    exact h i he
  | sort u => rfl
  | const c ls => rfl
  | app f a ihf iha =>
    simp only [Expr.closedAt_app, Bool.and_eq_true] at he
    simp only [interp_app, ihf he.1 h, iha he.2 h]
  | lam A b ihA ihb =>
    simp only [Expr.closedAt_lam, Bool.and_eq_true] at he
    simp only [interp_lam, ihA he.1 h]
    congr 1
    funext x
    exact ihb he.2 (cons_congr_lt h x)
  | pi A B ihA ihB =>
    simp only [Expr.closedAt_pi, Bool.and_eq_true] at he
    simp only [interp_pi, ihA he.1 h]
    congr 1
    funext x
    exact ihB he.2 (cons_congr_lt h x)
  | letE T v b _ ihv ihb =>
    simp only [Expr.closedAt_letE, Bool.and_eq_true] at he
    simp only [interp_letE, ihv he.1.2 h]
    exact ihb he.2 (cons_congr_lt h _)

/-- **Variables.**  The invariant of a term closed below `k` reads the
environment below `k` only. -/
theorem WellDenoted_closedAt {k : Nat} {e : Expr} (he : e.closedAt k = true) {ρ ρ' : Nat → V}
    (h : ∀ i, i < k → ρ i = ρ' i) : WellDenoted M φ ρ e ↔ WellDenoted M φ ρ' e := by
  induction e generalizing k ρ ρ' with
  | bvar i => simp
  | sort u => simp
  | const c ls => simp
  | app f a ihf iha =>
    simp only [Expr.closedAt_app, Bool.and_eq_true] at he
    rw [WellDenoted_app, WellDenoted_app, ihf he.1 h, iha he.2 h,
      interp_closedAt he.1 h, interp_closedAt he.2 h]
  | lam A b ihA ihb =>
    simp only [Expr.closedAt_lam, Bool.and_eq_true] at he
    rw [WellDenoted_lam, WellDenoted_lam, ihA he.1 h, interp_closedAt he.1 h]
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihb he.2 (cons_congr_lt h x))))
  | pi A B ihA ihB =>
    simp only [Expr.closedAt_pi, Bool.and_eq_true] at he
    rw [WellDenoted_pi, WellDenoted_pi, ihA he.1 h, interp_closedAt he.1 h]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · exact ihB he.2 (cons_congr_lt h x)
    · rw [interp_closedAt he.2 (cons_congr_lt h x)]
  | letE T v b _ ihv ihb =>
    simp only [Expr.closedAt_letE, Bool.and_eq_true] at he
    rw [WellDenoted_letE, WellDenoted_letE, ihv he.1.2 h, interp_closedAt he.1.2 h,
      ihb he.2 (cons_congr_lt h _)]

/-- **Used variables.**  The interpretation reads the environment at
the variables the term uses only. -/
theorem interp_usesVar {e : Expr} {ρ ρ' : Nat → V} (h : ∀ i, e.usesVar i = true → ρ i = ρ' i) :
    interp M φ ρ e = interp M φ ρ' e := by
  induction e generalizing ρ ρ' with
  | bvar i => exact h i (by simp)
  | sort u => rfl
  | const c ls => rfl
  | app f a ihf iha =>
    simp only [Expr.usesVar_app, Bool.or_eq_true, or_imp, forall_and] at h
    simp only [interp_app, ihf h.1, iha h.2]
  | lam A b ihA ihb =>
    simp only [Expr.usesVar_lam, Bool.or_eq_true, or_imp, forall_and] at h
    simp only [interp_lam, ihA h.1]
    congr 1
    funext x
    exact ihb (cons_congr_succ h.2 x)
  | pi A B ihA ihB =>
    simp only [Expr.usesVar_pi, Bool.or_eq_true, or_imp, forall_and] at h
    simp only [interp_pi, ihA h.1]
    congr 1
    funext x
    exact ihB (cons_congr_succ h.2 x)
  | letE T v b _ ihv ihb =>
    simp only [Expr.usesVar_letE, Bool.or_eq_true, or_imp, forall_and] at h
    simp only [interp_letE, ihv h.1.2]
    exact ihb (cons_congr_succ h.2 _)

/-- **Used variables.**  The invariant reads the environment at the
variables the term uses only. -/
theorem WellDenoted_usesVar {e : Expr} {ρ ρ' : Nat → V}
    (h : ∀ i, e.usesVar i = true → ρ i = ρ' i) :
    WellDenoted M φ ρ e ↔ WellDenoted M φ ρ' e := by
  induction e generalizing ρ ρ' with
  | bvar i => simp
  | sort u => simp
  | const c ls => simp
  | app f a ihf iha =>
    simp only [Expr.usesVar_app, Bool.or_eq_true, or_imp, forall_and] at h
    rw [WellDenoted_app, WellDenoted_app, ihf h.1, iha h.2,
      interp_usesVar h.1, interp_usesVar h.2]
  | lam A b ihA ihb =>
    simp only [Expr.usesVar_lam, Bool.or_eq_true, or_imp, forall_and] at h
    rw [WellDenoted_lam, WellDenoted_lam, ihA h.1, interp_usesVar h.1]
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihb (cons_congr_succ h.2 x))))
  | pi A B ihA ihB =>
    simp only [Expr.usesVar_pi, Bool.or_eq_true, or_imp, forall_and] at h
    rw [WellDenoted_pi, WellDenoted_pi, ihA h.1, interp_usesVar h.1]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · exact ihB (cons_congr_succ h.2 x)
    · rw [interp_usesVar (cons_congr_succ h.2 x)]
  | letE T v b _ ihv ihb =>
    simp only [Expr.usesVar_letE, Bool.or_eq_true, or_imp, forall_and] at h
    rw [WellDenoted_letE, WellDenoted_letE, ihv h.1.2, interp_usesVar h.1.2,
      ihb (cons_congr_succ h.2 _)]

/-- **Constants.**  The interpretation reads the model at the
constants the term mentions only. -/
theorem interp_consts {e : Expr} (h : ∀ c ∈ e.consts, ∀ ls, M c ls = M' c ls) {ρ : Nat → V} :
    interp M φ ρ e = interp M' φ ρ e := by
  induction e generalizing ρ with
  | bvar i => rfl
  | sort u => rfl
  | const c ls =>
    simp only [Expr.consts_const, List.mem_singleton, forall_eq] at h
    exact h _
  | app f a ihf iha =>
    simp only [Expr.consts_app, List.mem_append, or_imp, forall_and] at h
    simp only [interp_app, ihf h.1, iha h.2]
  | lam A b ihA ihb =>
    simp only [Expr.consts_lam, List.mem_append, or_imp, forall_and] at h
    simp only [interp_lam, ihA h.1]
    congr 1
    funext x
    exact ihb h.2
  | pi A B ihA ihB =>
    simp only [Expr.consts_pi, List.mem_append, or_imp, forall_and] at h
    simp only [interp_pi, ihA h.1]
    congr 1
    funext x
    exact ihB h.2
  | letE T v b _ ihv ihb =>
    simp only [Expr.consts_letE, List.mem_append, or_imp, forall_and] at h
    simp only [interp_letE, ihv h.1.2]
    exact ihb h.2

/-- **Constants.**  The invariant reads the model at the constants the
term mentions only. -/
theorem WellDenoted_consts {e : Expr} (h : ∀ c ∈ e.consts, ∀ ls, M c ls = M' c ls)
    {ρ : Nat → V} : WellDenoted M φ ρ e ↔ WellDenoted M' φ ρ e := by
  induction e generalizing ρ with
  | bvar i => simp
  | sort u => simp
  | const c ls => simp
  | app f a ihf iha =>
    simp only [Expr.consts_app, List.mem_append, or_imp, forall_and] at h
    rw [WellDenoted_app, WellDenoted_app, ihf h.1, iha h.2,
      interp_consts h.1, interp_consts h.2]
  | lam A b ihA ihb =>
    simp only [Expr.consts_lam, List.mem_append, or_imp, forall_and] at h
    rw [WellDenoted_lam, WellDenoted_lam, ihA h.1, interp_consts h.1]
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihb h.2)))
  | pi A B ihA ihB =>
    simp only [Expr.consts_pi, List.mem_append, or_imp, forall_and] at h
    rw [WellDenoted_pi, WellDenoted_pi, ihA h.1, interp_consts h.1]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · exact ihB h.2
    · rw [interp_consts h.2]
  | letE T v b _ ihv ihb =>
    simp only [Expr.consts_letE, List.mem_append, or_imp, forall_and] at h
    rw [WellDenoted_letE, WellDenoted_letE, ihv h.1.2, interp_consts h.1.2, ihb h.2]

/-- **Level parameters.**  The interpretation reads the valuation at
the parameters the term uses only. -/
theorem interp_lparams {ps : List Name} {e : Expr} (he : e.lparamsIn ps = true)
    (h : ∀ n ∈ ps, φ n = φ' n) {ρ : Nat → V} : interp M φ ρ e = interp M φ' ρ e := by
  induction e generalizing ρ with
  | bvar i => rfl
  | sort u =>
    rw [Expr.lparamsIn_sort] at he
    simp only [interp_sort, Level.eval_congr h he]
  | const c ls =>
    simp only [Expr.lparamsIn_const, List.all_eq_true] at he
    simp only [interp_const]
    congr 1
    exact List.map_congr_left fun l hl => Level.eval_congr h (he l hl)
  | app f a ihf iha =>
    simp only [Expr.lparamsIn_app, Bool.and_eq_true] at he
    simp only [interp_app, ihf he.1, iha he.2]
  | lam A b ihA ihb =>
    simp only [Expr.lparamsIn_lam, Bool.and_eq_true] at he
    simp only [interp_lam, ihA he.1]
    congr 1
    funext x
    exact ihb he.2
  | pi A B ihA ihB =>
    simp only [Expr.lparamsIn_pi, Bool.and_eq_true] at he
    simp only [interp_pi, ihA he.1]
    congr 1
    funext x
    exact ihB he.2
  | letE T v b _ ihv ihb =>
    simp only [Expr.lparamsIn_letE, Bool.and_eq_true] at he
    simp only [interp_letE, ihv he.1.2]
    exact ihb he.2

/-- **Level parameters.**  The invariant reads the valuation at the
parameters the term uses only. -/
theorem WellDenoted_lparams {ps : List Name} {e : Expr} (he : e.lparamsIn ps = true)
    (h : ∀ n ∈ ps, φ n = φ' n) {ρ : Nat → V} :
    WellDenoted M φ ρ e ↔ WellDenoted M φ' ρ e := by
  induction e generalizing ρ with
  | bvar i => simp
  | sort u => simp
  | const c ls => simp
  | app f a ihf iha =>
    simp only [Expr.lparamsIn_app, Bool.and_eq_true] at he
    rw [WellDenoted_app, WellDenoted_app, ihf he.1, iha he.2,
      interp_lparams he.1 h, interp_lparams he.2 h]
  | lam A b ihA ihb =>
    simp only [Expr.lparamsIn_lam, Bool.and_eq_true] at he
    rw [WellDenoted_lam, WellDenoted_lam, ihA he.1, interp_lparams he.1 h]
    exact and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun x => imp_congr Iff.rfl (ihb he.2)))
  | pi A B ihA ihB =>
    simp only [Expr.lparamsIn_pi, Bool.and_eq_true] at he
    rw [WellDenoted_pi, WellDenoted_pi, ihA he.1, interp_lparams he.1 h]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr
      (forall_congr' fun x => imp_congr Iff.rfl ?_)
      (forall_congr' fun x => imp_congr Iff.rfl ?_)))
    · exact ihB he.2
    · rw [interp_lparams he.2 h]
  | letE T v b _ ihv ihb =>
    simp only [Expr.lparamsIn_letE, Bool.and_eq_true] at he
    rw [WellDenoted_letE, WellDenoted_letE, ihv he.1.2, interp_lparams he.1.2 h, ihb he.2]

end Fragment
