module

public import ConLeche.SetModel.Value

@[expose] public section

/-!
# `interp` — the interpretation (task #151, tier B; task #342, L14a)

`interp V ρ e` maps a semantic term to an element of the set-theoretic
universe `V` under a variable environment `ρ : Nat → V`.

* **Total.**  A plain function on terms — never derivation-indexed, so
  coherence is not a theorem to prove but the absence of a question.
* **Environment-free.**  No global environment, no `Option`, no
  auxiliary truthfulness predicate: `interp` is a function of the term
  and the valuation alone.
* **Proof-carrying, zero-junk binders.**  Built via `interpDef`, which
  computes the interpretation under `d` bound-variable parameters
  `Fin d → V` paired with a first-order `DefFun d` witness, supplying
  `HasGraph` / `HasSigmaPairs` proofs to `lamV` / `piV` with zero junk.
* **The regime is read off the values.**  A Π-type is a truth value
  exactly when every fibre over its domain is one (`piV`), an
  abstraction is the point exactly when every body value over its
  domain is (`lamV`), `SetModel/Ops.lean`.  Over an empty domain both
  read "proposition": the function space is `{pt}`, the abstraction the
  point.

| term | value |
|---|---|
| `bvar i` | `ρ i` |
| `sort u` | `univ u` |
| `const c us` | `bval c us` |
| `app f a` | `app ⟦f⟧ ⟦a⟧` (`app pt _ = pt`) |
| `lam A b` | `lamV ⟦A⟧ (fun x => ⟦b⟧ₓ) hG` |
| `pi A B` | `piV ⟦A⟧ (fun x => ⟦B⟧ₓ) hS` |
| `letE v b` | `⟦b⟧` at `cons ⟦v⟧ ρ` |
| `eqE a b` | `eqv ⟦a⟧ ⟦b⟧` |
| `fst e` / `snd e` | `sfst ⟦e⟧` / `ssnd ⟦e⟧` |
| `prf` | `pt` |

β holds on the domain with no other premise (`app_lamV`).
-/

namespace ConLeche.Semantics
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory

universe w

/-! ## Variable environments

Pure `Nat → V` plumbing; no set theory is involved, so this section
carries no `SetTheory` instance.  These are `ConLeche.Term.Semantics`'
`cons`/`shiftE`/`instE` with `V` implicit; they are duplicated rather
than imported so that `Interp/*` depends on **no** module built over
the collapse operators. -/

section Env

variable {V : Type w}

/-- Extend an environment with a new innermost binding. -/
def cons (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

@[simp] theorem cons_zero (x : V) (ρ : Nat → V) : cons x ρ 0 = x := rfl
@[simp] theorem cons_succ (x : V) (ρ : Nat → V) (i : Nat) :
    cons x ρ (i + 1) = ρ i := rfl

/-- The environment transformation matching `Term.liftN n · k`. -/
def shiftE (n k : Nat) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else ρ (i + n)

/-- The environment transformation matching `Term.inst · a k`. -/
def instE (k : Nat) (x : V) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else if i = k then x else ρ (i - 1)

theorem shiftE_zero (n : Nat) (ρ : Nat → V) :
    shiftE n 0 ρ = fun i => ρ (i + n) := by
  funext i; simp [shiftE]

theorem shiftE_zero_zero (ρ : Nat → V) : shiftE 0 0 ρ = ρ := by
  funext i; simp [shiftE]

theorem instE_zero (x : V) (ρ : Nat → V) : instE 0 x ρ = cons x ρ := by
  funext i; cases i <;> simp [instE, cons]

theorem cons_shiftE (x : V) (n k : Nat) (ρ : Nat → V) :
    cons x (shiftE n k ρ) = shiftE n (k + 1) (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [shiftE]
  | succ j =>
    show shiftE n k ρ j = shiftE n (k + 1) (cons x ρ) (j + 1)
    simp only [shiftE]
    by_cases h : j < k
    · rw [ite_eq_left h, ite_eq_left (show j + 1 < k + 1 by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (show ¬ (j + 1 < k + 1) by omega)]
      show ρ (j + n) = cons x ρ (j + 1 + n)
      rw [show j + 1 + n = (j + n) + 1 by omega]; rfl

theorem cons_instE (x : V) (k : Nat) (y : V) (ρ : Nat → V) :
    cons x (instE k y ρ) = instE (k + 1) y (cons x ρ) := by
  funext i
  cases i with
  | zero => simp [instE]
  | succ j =>
    show instE k y ρ j = instE (k + 1) y (cons x ρ) (j + 1)
    simp only [instE]
    by_cases h : j < k
    · rw [ite_eq_left h, ite_eq_left (show j + 1 < k + 1 by omega)]; rfl
    · rw [ite_eq_right h, ite_eq_right (show ¬ (j + 1 < k + 1) by omega)]
      by_cases h2 : j = k
      · rw [ite_eq_left h2, ite_eq_left (show j + 1 = k + 1 by omega)]
      · rw [ite_eq_right h2, ite_eq_right (show ¬ (j + 1 = k + 1) by omega)]
        show ρ (j - 1) = cons x ρ (j + 1 - 1)
        rw [show j + 1 - 1 = (j - 1) + 1 by omega]; rfl

theorem shiftE_succ_cons (x : V) (k : Nat) (ρ : Nat → V) :
    shiftE (k + 1) 0 (cons x ρ) = shiftE k 0 ρ := by
  rw [shiftE_zero, shiftE_zero]
  funext i
  show cons x ρ (i + (k + 1)) = ρ (i + k)
  rw [show i + (k + 1) = (i + k) + 1 by omega]; rfl

/-- Prepend a finite `d`-tuple `xs` in front of a de Bruijn environment `ρ`. -/
def prepend {d : Nat} (xs : Fin d → V) (ρ : Nat → V) : Nat → V :=
  fun i => if h : i < d then xs ⟨i, h⟩ else ρ (i - d)

@[simp] theorem prepend_zero (ρ : Nat → V) :
    prepend (Fin.elim0 : Fin 0 → V) ρ = ρ := by
  funext i
  simp [prepend]

theorem prepend_one (xs : Fin 1 → V) (ρ : Nat → V) :
    prepend xs ρ = cons (xs 0) ρ := by
  funext i
  cases i with
  | zero => rfl
  | succ i => simp [prepend, cons]

theorem prepend_fcons {d : Nat} (x : V) (xs : Fin d → V) (ρ : Nat → V) :
    prepend (fcons x xs) ρ = cons x (prepend xs ρ) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    by_cases h : i < d
    · have h' : i + 1 < d + 1 := Nat.succ_lt_succ h
      simp [prepend, cons, h, h', fcons]
    · have h' : ¬ (i + 1 < d + 1) := fun hlt => h (Nat.lt_of_succ_lt_succ hlt)
      simp [prepend, cons, h, h']

end Env

/-! ## First-order definability worker and interpretation -/

section Worker

variable {V : Type w} [SetTheory V]

theorem defFun1_fcons {d : Nat} {F : (Fin (d + 1) → V) → V}
    (hF : DefFun (d + 1) F) (xs : Fin d → V) :
    DefFun 1 fun v => F (fcons (v 0) xs) := by
  let Gs : Fin (d + 1) → (Fin 1 → V) → V
    | ⟨0, _⟩ => fun v => v 0
    | ⟨i + 1, h⟩ => fun _ => xs ⟨i, Nat.lt_of_succ_lt_succ h⟩
  have hGs : ∀ j : Fin (d + 1), DefFun 1 (Gs j) := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => exact DefFun.proj 0
    | succ j => exact DefFun.const (xs ⟨j, Nat.lt_of_succ_lt_succ hj⟩)
  refine (DefFun.comp hF hGs).congr fun v => ?_
  congr 1
  funext ⟨j, hj⟩
  cases j with
  | zero => rfl
  | succ j => rfl

theorem defFun_subst0 {d : Nat} {B : (Fin (d + 1) → V) → V} {A : (Fin d → V) → V}
    (hB : DefFun (d + 1) B) (hA : DefFun d A) :
    DefFun d fun xs => B (fcons (A xs) xs) := by
  let Gs : Fin (d + 1) → (Fin d → V) → V
    | ⟨0, _⟩ => A
    | ⟨i + 1, hi⟩ => fun xs => xs ⟨i, Nat.lt_of_succ_lt_succ hi⟩
  have hGs : ∀ j : Fin (d + 1), DefFun d (Gs j) := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => exact hA
    | succ j => exact DefFun.proj ⟨j, Nat.lt_of_succ_lt_succ hj⟩
  refine (DefFun.comp hB hGs).congr fun xs => ?_
  congr 1
  funext ⟨j, hj⟩
  cases j with
  | zero => rfl
  | succ j => rfl

end Worker

variable (V : Type w) [SetTheory V]

/-- Proof-carrying worker for `interp`: evaluates `t` under `d` bound-variable
parameters `xs : Fin d → V` prepended to `ρ`, paired with a `DefFun d` witness. -/
noncomputable def interpDef (ρ : Nat → V) :
    (d : Nat) → Term → { f : (Fin d → V) → V // DefFun d f }
  | d, .bvar i =>
    if h : i < d then ⟨fun xs => xs ⟨i, h⟩, DefFun.proj ⟨i, h⟩⟩
    else ⟨fun _ => ρ (i - d), DefFun.const _⟩
  | _, .sort u => ⟨fun _ => univ u, DefFun.const _⟩
  | _, .const c us => ⟨fun _ => bval V c us, DefFun.const _⟩
  | d, .app f a =>
    let f' := interpDef ρ d f
    let a' := interpDef ρ d a
    ⟨fun xs => SetTheory.app (f'.val xs) (a'.val xs), DefFun.app_apply f'.property a'.property⟩
  | d, .lam A b =>
    let A' := interpDef ρ d A
    let b' := interpDef ρ (d + 1) b
    ⟨fun xs => lamV (A'.val xs) (fun x => b'.val (fcons x xs))
        (hasGraph_of_defFun1 (defFun1_fcons b'.property xs)),
      DefFun.lamV_apply b'.property A'.property⟩
  | d, .pi A B =>
    let A' := interpDef ρ d A
    let B' := interpDef ρ (d + 1) B
    ⟨fun xs => piV (A'.val xs) (fun x => B'.val (fcons x xs))
        (hasSigmaPairs_of_defFun1 (defFun1_fcons B'.property xs)),
      DefFun.piV_apply A'.property B'.property⟩
  | d, .letE v b =>
    let v' := interpDef ρ d v
    let b' := interpDef ρ (d + 1) b
    ⟨fun xs => b'.val (fcons (v'.val xs) xs), defFun_subst0 b'.property v'.property⟩
  | d, .eqE a b =>
    let a' := interpDef ρ d a
    let b' := interpDef ρ d b
    ⟨fun xs => eqv (a'.val xs) (b'.val xs), DefFun.eqv_apply a'.property b'.property⟩
  | d, .fst e =>
    let e' := interpDef ρ d e
    ⟨fun xs => sfst (e'.val xs), DefFun.sfst_apply e'.property⟩
  | d, .snd e =>
    let e' := interpDef ρ d e
    ⟨fun xs => ssnd (e'.val xs), DefFun.ssnd_apply e'.property⟩
  | _, .prf => ⟨fun _ => pt, DefFun.pt⟩

theorem interpDef_prepend :
    ∀ (t : Term) (d : Nat) (xs : Fin d → V) (ρ : Nat → V),
      (interpDef V ρ d t).val xs =
        (interpDef V (prepend xs ρ) 0 t).val Fin.elim0
  | .bvar i, d, xs, ρ => by
    by_cases h : i < d
    · simp [interpDef, prepend, h]
    · simp [interpDef, prepend, h]
  | .sort _, _, _, _ => rfl
  | .const _ _, _, _, _ => rfl
  | .app f a, d, xs, ρ => by
    simp only [interpDef]
    rw [interpDef_prepend f d xs ρ, interpDef_prepend a d xs ρ]
  | .lam A b, d, xs, ρ => by
    simp only [interpDef]
    refine lamV_ext (interpDef_prepend A d xs ρ) _ _ fun x _ => ?_
    rw [interpDef_prepend b (d + 1) (fcons x xs) ρ,
        interpDef_prepend b 1 (fcons x Fin.elim0) (prepend xs ρ),
        prepend_fcons, prepend_fcons, prepend_zero]
  | .pi A B, d, xs, ρ => by
    simp only [interpDef]
    refine piV_ext (interpDef_prepend A d xs ρ) _ _ fun x _ => ?_
    rw [interpDef_prepend B (d + 1) (fcons x xs) ρ,
        interpDef_prepend B 1 (fcons x Fin.elim0) (prepend xs ρ),
        prepend_fcons, prepend_fcons, prepend_zero]
  | .letE v b, d, xs, ρ => by
    simp only [interpDef]
    rw [interpDef_prepend v d xs ρ,
        interpDef_prepend b (d + 1) (fcons _ xs) ρ,
        interpDef_prepend b 1 (fcons _ Fin.elim0) (prepend xs ρ),
        prepend_fcons, prepend_fcons, prepend_zero]
  | .eqE a b, d, xs, ρ => by
    simp only [interpDef]
    rw [interpDef_prepend a d xs ρ, interpDef_prepend b d xs ρ]
  | .fst e, d, xs, ρ => by
    simp only [interpDef]
    rw [interpDef_prepend e d xs ρ]
  | .snd e, d, xs, ρ => by
    simp only [interpDef]
    rw [interpDef_prepend e d xs ρ]
  | .prf, _, _, _ => rfl

/-- The interpretation: total, term-directed, environment-free; the
binders read their regime off the values. -/
noncomputable def interp (ρ : Nat → V) (t : Term) : V :=
  (interpDef V ρ 0 t).val Fin.elim0

variable {V} in
theorem interp_defFun_prepend (ρ : Nat → V) (d : Nat) (t : Term) :
    DefFun d fun xs => interp V (prepend xs ρ) t :=
  (interpDef V ρ d t).property.congr fun xs => interpDef_prepend V t d xs ρ

variable {V} in
theorem interp_defFun_cons (ρ : Nat → V) (t : Term) :
    DefFun 1 fun v => interp V (cons (v 0) ρ) t :=
  (interp_defFun_prepend ρ 1 t).congr fun xs => by rw [prepend_one]

variable {V} in
theorem interp_hasGraph_cons (ρ : Nat → V) (A : V) (body : Term) :
    HasGraph A fun x => interp V (cons x ρ) body :=
  hasGraph_of_defFun1 (interp_defFun_cons ρ body)

variable {V} in
theorem interp_hasSigmaPairs_cons (ρ : Nat → V) (A : V) (body : Term) :
    HasSigmaPairs A fun x => interp V (cons x ρ) body :=
  hasSigmaPairs_of_defFun1 (interp_defFun_cons ρ body)

@[simp] theorem interp_bvar (ρ : Nat → V) (i : Nat) :
    interp V ρ (.bvar i) = ρ i := by
  simp [interp, interpDef]

@[simp] theorem interp_sort (ρ : Nat → V) (u : Nat) :
    interp V ρ (.sort u) = univ u := rfl

@[simp] theorem interp_const (ρ : Nat → V) (c : ConLeche.Term.BConst)
    (us : List Nat) : interp V ρ (.const c us) = bval V c us := rfl

@[simp] theorem interp_app (ρ : Nat → V) (f a : Term) :
    interp V ρ (.app f a) = SetTheory.app (interp V ρ f) (interp V ρ a) := rfl

@[simp] theorem interp_lam (ρ : Nat → V) (A b : Term) :
    interp V ρ (.lam A b) =
      lamV (interp V ρ A) (fun x => interp V (cons x ρ) b)
        (interp_hasGraph_cons ρ (interp V ρ A) b) := by
  simp only [interp, interpDef]
  refine lamV_congr _ _ fun x _ => ?_
  rw [interpDef_prepend V b 1 (fcons x Fin.elim0) ρ, prepend_fcons, prepend_zero]

@[simp] theorem interp_pi (ρ : Nat → V) (A B : Term) :
    interp V ρ (.pi A B) =
      piV (interp V ρ A) (fun x => interp V (cons x ρ) B)
        (interp_hasSigmaPairs_cons ρ (interp V ρ A) B) := by
  simp only [interp, interpDef]
  refine piV_congr _ _ fun x _ => ?_
  rw [interpDef_prepend V B 1 (fcons x Fin.elim0) ρ, prepend_fcons, prepend_zero]

@[simp] theorem interp_letE (ρ : Nat → V) (v b : Term) :
    interp V ρ (.letE v b) = interp V (cons (interp V ρ v) ρ) b := by
  simp only [interp, interpDef]
  rw [interpDef_prepend V b 1 (fcons _ Fin.elim0) ρ, prepend_fcons, prepend_zero]

@[simp] theorem interp_eqE (ρ : Nat → V) (a b : Term) :
    interp V ρ (.eqE a b) = eqv (interp V ρ a) (interp V ρ b) := rfl

@[simp] theorem interp_fst (ρ : Nat → V) (e : Term) :
    interp V ρ (.fst e) = sfst (interp V ρ e) := rfl

@[simp] theorem interp_snd (ρ : Nat → V) (e : Term) :
    interp V ρ (.snd e) = ssnd (interp V ρ e) := rfl

@[simp] theorem interp_prf (ρ : Nat → V) : interp V ρ .prf = pt := rfl

variable {V} in
/-- `interp` of an application spine, as a `map`-then-`foldl`. -/
theorem interp_mkAppN_foldl (ρ : Nat → V) :
    ∀ (f : Term) (es : List Term),
      interp V ρ (Term.mkAppN f es) = (es.map (interp V ρ)).foldl SetTheory.app (interp V ρ f)
  | _, [] => rfl
  | f, e :: es => by
    rw [Term.mkAppN_cons, interp_mkAppN_foldl ρ (.app f e) es]
    rfl

end ConLeche.Semantics
