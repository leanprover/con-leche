import Setlec.TT.Judgment
import Setlec.TT.Semantics.Value

/-!
# Interpretation into the set model

`interp V ρ e` maps a `VExpr` to an element of the set-theoretic
universe `V` under a variable environment `ρ : Nat → V`.

Three things are worth noticing, each a direct payoff of the layer's
design:

* **It is total.**  The checker-side `interpExpr` is
  `Option`-valued and comes with the auxiliary truthfulness predicate
  `AnnotOk`, because it interprets *arbitrary* `Expr`s, including
  ill-formed ones, and must reconstruct at every binder the
  fibre/membership facts a typing derivation would have supplied.
  Here the derivation supplies them, so the interpretation is a plain
  function and `AnnotOk` has no counterpart.
* **It has no level-assignment parameter.**  `VExpr` carries ground
  levels, so `⟦Sort n⟧ = univ n` outright.
* **`eqE`'s type argument is not read.**  `⟦eqE T a b⟧ = eqv ⟦a⟧ ⟦b⟧`
  is the truth-set of `⟦a⟧ = ⟦b⟧`, so *inhabitation gives the equation*
  — which is what makes equality reflection sound and what removes any
  need for a mutual typing/equality induction.

The whole substitution metatheory of the layer is the two lemmas
`interp_liftN` and `interp_inst` below.
-/

namespace Setlec.TT

open SetTheory

universe w

/-! ## Variable environments

Pure `Nat → V` plumbing; no set theory is involved, so this section
carries no `SetTheory` instance. -/

section Env

variable (V : Type w)

/-- Extend an environment with a new innermost binding. -/
def cons (x : V) (ρ : Nat → V) : Nat → V
  | 0 => x
  | i + 1 => ρ i

@[simp] theorem cons_zero (x : V) (ρ : Nat → V) : cons V x ρ 0 = x := rfl
@[simp] theorem cons_succ (x : V) (ρ : Nat → V) (i : Nat) :
    cons V x ρ (i + 1) = ρ i := rfl

/-- The environment transformation matching `VExpr.liftN n · k`. -/
def shiftE (n k : Nat) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else ρ (i + n)

/-- The environment transformation matching `VExpr.inst · a k`. -/
def instE (k : Nat) (x : V) (ρ : Nat → V) : Nat → V :=
  fun i => if i < k then ρ i else if i = k then x else ρ (i - 1)

theorem shiftE_zero (n : Nat) (ρ : Nat → V) :
    shiftE V n 0 ρ = fun i => ρ (i + n) := by
  funext i; simp [shiftE]

theorem shiftE_zero_zero (ρ : Nat → V) : shiftE V 0 0 ρ = ρ := by
  funext i; simp [shiftE]

theorem instE_zero (x : V) (ρ : Nat → V) : instE V 0 x ρ = cons V x ρ := by
  funext i; cases i <;> simp [instE, cons]

theorem cons_shiftE (x : V) (n k : Nat) (ρ : Nat → V) :
    cons V x (shiftE V n k ρ) = shiftE V n (k + 1) (cons V x ρ) := by
  funext i
  cases i with
  | zero => simp [shiftE]
  | succ j =>
    show shiftE V n k ρ j = shiftE V n (k + 1) (cons V x ρ) (j + 1)
    simp only [shiftE]
    by_cases h : j < k
    · rw [if_pos h, if_pos (show j + 1 < k + 1 by omega)]; rfl
    · rw [if_neg h, if_neg (show ¬ (j + 1 < k + 1) by omega)]
      show ρ (j + n) = cons V x ρ (j + 1 + n)
      rw [show j + 1 + n = (j + n) + 1 by omega]; rfl

theorem cons_instE (x : V) (k : Nat) (y : V) (ρ : Nat → V) :
    cons V x (instE V k y ρ) = instE V (k + 1) y (cons V x ρ) := by
  funext i
  cases i with
  | zero => simp [instE]
  | succ j =>
    show instE V k y ρ j = instE V (k + 1) y (cons V x ρ) (j + 1)
    simp only [instE]
    by_cases h : j < k
    · rw [if_pos h, if_pos (show j + 1 < k + 1 by omega)]; rfl
    · rw [if_neg h, if_neg (show ¬ (j + 1 < k + 1) by omega)]
      by_cases h2 : j = k
      · rw [if_pos h2, if_pos (show j + 1 = k + 1 by omega)]
      · rw [if_neg h2, if_neg (show ¬ (j + 1 = k + 1) by omega)]
        show ρ (j - 1) = cons V x ρ (j + 1 - 1)
        rw [show j + 1 - 1 = (j - 1) + 1 by omega]; rfl

theorem shiftE_succ_cons (x : V) (k : Nat) (ρ : Nat → V) :
    shiftE V (k + 1) 0 (cons V x ρ) = shiftE V k 0 ρ := by
  rw [shiftE_zero, shiftE_zero]
  funext i
  show cons V x ρ (i + (k + 1)) = ρ (i + k)
  rw [show i + (k + 1) = (i + k) + 1 by omega]; rfl

end Env

variable (V : Type w) [SetTheory V]

/-! ## The interpretation -/

/-- Interpret a term under a variable environment. -/
noncomputable def interp : (Nat → V) → VExpr → V
  | ρ, .bvar i => ρ i
  | _, .sort u => univ u
  | _, .const c us => bval V c us
  | ρ, .app f a => SetTheory.app (interp ρ f) (interp ρ a)
  | ρ, .lam A b => lamC (interp ρ A) fun x => interp (cons V x ρ) b
  | ρ, .pi A B => piC (interp ρ A) fun x => interp (cons V x ρ) B
  | ρ, .letE _ v b => interp (cons V (interp ρ v) ρ) b
  | ρ, .eqE _ a b => eqv (interp ρ a) (interp ρ b)
  | _, .prf => pt

@[simp] theorem interp_bvar (ρ : Nat → V) (i : Nat) :
    interp V ρ (.bvar i) = ρ i := rfl
@[simp] theorem interp_sort (ρ : Nat → V) (u : Nat) :
    interp V ρ (.sort u) = univ u := rfl
@[simp] theorem interp_const (ρ : Nat → V) (c : BConst) (us : List Nat) :
    interp V ρ (.const c us) = bval V c us := rfl
@[simp] theorem interp_app (ρ : Nat → V) (f a : VExpr) :
    interp V ρ (.app f a) = SetTheory.app (interp V ρ f) (interp V ρ a) := rfl
@[simp] theorem interp_lam (ρ : Nat → V) (A b : VExpr) :
    interp V ρ (.lam A b) = lamC (interp V ρ A) fun x => interp V (cons V x ρ) b :=
  rfl
@[simp] theorem interp_pi (ρ : Nat → V) (A B : VExpr) :
    interp V ρ (.pi A B) = piC (interp V ρ A) fun x => interp V (cons V x ρ) B :=
  rfl
@[simp] theorem interp_letE (ρ : Nat → V) (T v b : VExpr) :
    interp V ρ (.letE T v b) = interp V (cons V (interp V ρ v) ρ) b := rfl
@[simp] theorem interp_eqE (ρ : Nat → V) (T a b : VExpr) :
    interp V ρ (.eqE T a b) = eqv (interp V ρ a) (interp V ρ b) := rfl
@[simp] theorem interp_prf (ρ : Nat → V) : interp V ρ .prf = pt := rfl

/-! ## The substitution lemmas

The layer's entire substitution metatheory.  lean4lean needs ~123
syntactic lemmas here because its metatheory is syntactic; soundness
goes straight to the model, so two semantic lemmas suffice. -/

theorem interp_liftN (n : Nat) :
    ∀ (e : VExpr) (k : Nat) (ρ : Nat → V),
      interp V ρ (e.liftN n k) = interp V (shiftE V n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [VExpr.liftN_bvar, interp_bvar, shiftE]
    split <;> rfl
  | sort u => intro k ρ; rfl
  | const c us => intro k ρ; rfl
  | app f a ihf iha =>
    intro k ρ; simp only [VExpr.liftN_app, interp_app, ihf, iha]
  | lam A b ihA ihb =>
    intro k ρ
    simp only [VExpr.liftN_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, cons_shiftE]
  | pi A B ihA ihB =>
    intro k ρ
    simp only [VExpr.liftN_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, cons_shiftE]
  | letE T v b ihT ihv ihb =>
    intro k ρ
    simp only [VExpr.liftN_letE, interp_letE, ihv, ihb, cons_shiftE]
  | eqE T a b ihT iha ihb =>
    intro k ρ; simp only [VExpr.liftN_eqE, interp_eqE, iha, ihb]
  | prf => intro k ρ; rfl

theorem interp_lift (e : VExpr) (ρ : Nat → V) :
    interp V ρ e.lift = interp V (fun i => ρ (i + 1)) e := by
  rw [VExpr.lift, interp_liftN, shiftE_zero]

theorem interp_lift_cons (e : VExpr) (x : V) (ρ : Nat → V) :
    interp V (cons V x ρ) e.lift = interp V ρ e := by
  rw [interp_lift]; rfl

theorem interp_inst :
    ∀ (e a : VExpr) (k : Nat) (ρ : Nat → V),
      interp V ρ (e.inst a k) =
        interp V (instE V k (interp V (shiftE V k 0 ρ) a) ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ
    show interp V ρ
        (if i < k then .bvar i
         else if i = k then VExpr.liftN k a else .bvar (i - 1)) =
      instE V k (interp V (shiftE V k 0 ρ) a) ρ i
    by_cases h : i < k
    · simp only [if_pos h, instE]; rfl
    · by_cases h2 : i = k
      · simp only [if_neg h, if_pos h2, instE]
        exact interp_liftN V k a 0 ρ
      · simp only [if_neg h, if_neg h2, instE]; rfl
  | sort u => intro a k ρ; rfl
  | const c us => intro a k ρ; rfl
  | app f b ihf ihb =>
    intro a k ρ; simp only [VExpr.inst_app, interp_app, ihf, ihb]
  | lam A b ihA ihb =>
    intro a k ρ
    simp only [VExpr.inst_lam, interp_lam, ihA]
    congr 1
    funext x
    rw [ihb, shiftE_succ_cons, cons_instE]
  | pi A B ihA ihB =>
    intro a k ρ
    simp only [VExpr.inst_pi, interp_pi, ihA]
    congr 1
    funext x
    rw [ihB, shiftE_succ_cons, cons_instE]
  | letE T v b ihT ihv ihb =>
    intro a k ρ
    simp only [VExpr.inst_letE, interp_letE, ihv, ihb, shiftE_succ_cons,
      cons_instE]
  | eqE T b c ihT ihb ihc =>
    intro a k ρ; simp only [VExpr.inst_eqE, interp_eqE, ihb, ihc]
  | prf => intro a k ρ; rfl

/-- Substitution at the outermost binder — the form every rule uses. -/
theorem interp_inst0 (e a : VExpr) (ρ : Nat → V) :
    interp V ρ (e.inst a) = interp V (cons V (interp V ρ a) ρ) e := by
  rw [interp_inst, shiftE_zero_zero, instE_zero]

/-! ## Interpretation of the derived formers -/

@[simp] theorem interp_arrow (ρ : Nat → V) (A B : VExpr) :
    interp V ρ (arrow A B) = piC (interp V ρ A) fun _ => interp V ρ B := by
  simp only [arrow, interp_pi]
  congr 1
  funext x
  exact interp_lift_cons V B x ρ

@[simp] theorem interp_relT (ρ : Nat → V) (A : VExpr) :
    interp V ρ (relT A) = relSpace V (interp V ρ A) := by
  simp only [relT, interp_pi, interp_sort, relSpace]
  congr 1
  funext x
  congr 1
  exact interp_lift_cons V A x ρ

theorem interp_mkAppN (ρ : Nat → V) :
    ∀ (as : List VExpr) (f : VExpr),
      interp V ρ (VExpr.mkAppN f as) =
        as.foldl (fun r a => SetTheory.app r (interp V ρ a)) (interp V ρ f)
  | [], _ => rfl
  | a :: as, f => by
    simp only [VExpr.mkAppN_cons, List.foldl_cons]
    rw [interp_mkAppN ρ as (.app f a)]
    rfl

@[simp] theorem interp_natT (ρ : Nat → V) : interp V ρ natT = omega := rfl
@[simp] theorem interp_natZeroT (ρ : Nat → V) : interp V ρ natZeroT = natzero := rfl
@[simp] theorem interp_natSuccT (ρ : Nat → V) (e : VExpr) :
    interp V ρ (natSuccT e) = SetTheory.app (natSuccV V) (interp V ρ e) := rfl
@[simp] theorem interp_punitT (ρ : Nat → V) (u : Nat) :
    interp V ρ (punitT u) = unitSet := rfl
@[simp] theorem interp_punitUnitT (ρ : Nat → V) (u : Nat) :
    interp V ρ (punitUnitT u) = pt := rfl
@[simp] theorem interp_emptyT (ρ : Nat → V) (u : Nat) :
    interp V ρ (emptyT u) = empty := rfl

theorem interp_natRecT (ρ : Nat → V) (u : Nat) (M z s t : VExpr) :
    interp V ρ (natRecT u M z s t) =
      SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (natRecV V u) (interp V ρ M)) (interp V ρ z))
        (interp V ρ s)) (interp V ρ t) := rfl

theorem interp_punitRecT (ρ : Nat → V) (u v : Nat) (M m t : VExpr) :
    interp V ρ (punitRecT u v M m t) =
      SetTheory.app (SetTheory.app (SetTheory.app
        (punitRecV V v) (interp V ρ M)) (interp V ρ m)) (interp V ρ t) := rfl

theorem interp_psigmaT (ρ : Nat → V) (u v : Nat) (A B : VExpr) :
    interp V ρ (psigmaT u v A B) =
      SetTheory.app (SetTheory.app (psigmaV V u v) (interp V ρ A))
        (interp V ρ B) := rfl

theorem interp_psigmaMkT (ρ : Nat → V) (u v : Nat) (A B a b : VExpr) :
    interp V ρ (psigmaMkT u v A B a b) =
      SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaMkV V u v) (interp V ρ A)) (interp V ρ B))
        (interp V ρ a)) (interp V ρ b) := rfl

theorem interp_psigmaFstT (ρ : Nat → V) (u v : Nat) (A B p : VExpr) :
    interp V ρ (psigmaFstT u v A B p) =
      SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaFstV V u v) (interp V ρ A)) (interp V ρ B)) (interp V ρ p) := rfl

theorem interp_psigmaSndT (ρ : Nat → V) (u v : Nat) (A B p : VExpr) :
    interp V ρ (psigmaSndT u v A B p) =
      SetTheory.app (SetTheory.app (SetTheory.app
        (psigmaSndV V u v) (interp V ρ A)) (interp V ρ B)) (interp V ρ p) := rfl

theorem interp_quotT (ρ : Nat → V) (u : Nat) (A r : VExpr) :
    interp V ρ (quotT u A r) =
      SetTheory.app (SetTheory.app (quotV V u) (interp V ρ A))
        (interp V ρ r) := rfl

theorem interp_quotMkT (ρ : Nat → V) (u : Nat) (A r a : VExpr) :
    interp V ρ (quotMkT u A r a) =
      SetTheory.app (SetTheory.app (SetTheory.app
        (quotMkV V u) (interp V ρ A)) (interp V ρ r)) (interp V ρ a) := rfl

theorem interp_quotLiftT (ρ : Nat → V) (u v : Nat) (A r B f h q : VExpr) :
    interp V ρ (quotLiftT u v A r B f h q) =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app (quotLiftV V u v) (interp V ρ A))
          (interp V ρ r)) (interp V ρ B)) (interp V ρ f)) (interp V ρ h))
        (interp V ρ q) := rfl

/-- The minor-premise type of `Nat.rec`.  The `piC_congr` step is where
`Nat.succ`'s *value* (a `lamC` over `ω`) meets `natsucc`: they agree
exactly on the domain the outer product quantifies over. -/
theorem interp_natStepT (ρ : Nat → V) (M : VExpr) :
    interp V ρ (natStepT M) = natStepSpace V (interp V ρ M) := by
  show piC (omega : V) _ = piC (omega : V) _
  refine piC_congr fun n hn => ?_
  show piC (SetTheory.app (interp V (cons V n ρ) (M.liftN 1)) n) _ = _
  rw [interp_lift_cons]
  congr 1
  funext ih
  show SetTheory.app (interp V (cons V ih (cons V n ρ)) (M.liftN 2))
      (SetTheory.app (natSuccV V) n) = _
  rw [interp_liftN, shiftE_zero, natSuccV_app V hn]
  rfl

theorem interp_quotInvT (ρ : Nat → V) (A r B f : VExpr) :
    interp V ρ (quotInvT A r B f) =
      quotInvSpace V (interp V ρ A) (interp V ρ r) (interp V ρ f) := by
  show piC (interp V ρ A) _ = piC (interp V ρ A) _
  congr 1
  funext a
  show piC (interp V (cons V a ρ) (A.liftN 1)) _ = _
  rw [interp_lift_cons]
  congr 1
  funext b
  show piC (interp V (cons V b (cons V a ρ)) (VExpr.mkAppN (r.liftN 2) _)) _ = _
  rw [interp_mkAppN]
  simp only [List.foldl_cons, List.foldl_nil, interp_bvar, cons_zero, cons_succ]
  rw [interp_liftN, shiftE_zero]
  congr 1
  funext hh
  show eqv (SetTheory.app (interp V (cons V hh (cons V b (cons V a ρ)))
      (f.liftN 3)) _) (SetTheory.app (interp V _ (f.liftN 3)) _) = _
  rw [interp_liftN, shiftE_zero]
  rfl

end Setlec.TT
