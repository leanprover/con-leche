import Setlec.TT.Semantics.Soundness
import Setlec.Verify.Denote.VClosed

/-!
# `AnnotOkV`: annotation truthfulness on the env-free syntax (task #148, T4)

The clause-for-clause transpose of `Setlec/Model/Interp.lean`'s
`AnnotOk` onto `VExpr` (campaign design §0 decision 2), with

* `cons`-extension in place of the `updV`/`fvar`-opening (the
  interpretation is `Setlec.TT.interp`, total and env-free);
* the definedness conjuncts dropped (`interp` is total), including the
  `lam` clause's junk `∃ B, w ∈ˢ B` companion;
* two new leaf clauses for the layer-only formers: `eqE` is hereditary
  on its two sides only (the type slot is never read — see
  `Setlec/TT/Syntax.lean` on `eqE`), and `prf` is `True`.

Like the original, this is *hereditary truthfulness of the binder and
application structure*: every application node carries its semantic
typing package, every binder body is truthful over every member of the
domain's interpretation, and a `.proj` subject carries its sigma-set
package.  Soundness consumes it per the T4 architecture record
(`Setlec/SetR/DESIGN.md`): `Infer`-sound *concludes* it for subjects,
`Red`-sound transports it forward, `DefEq`-sound never touches it.

The substitution metatheory is two lemmas (`AnnotOkV_liftN`,
`AnnotOkV_inst`), mirroring `interp_liftN`/`interp_inst` — the
Expr-side swamp (`Model/Subst.lean`'s `AnnotOk.lift`/`AnnotOk_beta`
family) has no other successor.  `TeleFitV` is the `TeleFit`/`TeleFitI`
transpose over `interp`, and its `appN`/`annot` eliminations are the
`certs_fit`-elimination (`app_mem_piC` chain) this tier's iota/rescue
cases consume.
-/

namespace Setlec.SetR

open Setlec.TT
open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-- Hereditary truthfulness of the binder/application structure under a
variable environment.  Transpose of `Setlec.AnnotOk`; see the module
docstring for the clause-level deltas. -/
def AnnotOkV : (Nat → V) → VExpr → Prop
  | ρ, .pi A B =>
    AnnotOkV ρ A ∧
    ∀ x, x ∈ˢ interp V ρ A → AnnotOkV (cons V x ρ) B
  | ρ, .lam A b =>
    AnnotOkV ρ A ∧
    ∀ x, x ∈ˢ interp V ρ A → AnnotOkV (cons V x ρ) b
  | ρ, .app f a =>
    AnnotOkV ρ f ∧ AnnotOkV ρ a ∧
    ∃ A B, interp V ρ f ∈ˢ piC A B ∧ interp V ρ a ∈ˢ A
  | ρ, .letE T v b =>
    AnnotOkV ρ T ∧ AnnotOkV ρ v ∧
    AnnotOkV (cons V (interp V ρ v) ρ) b
  | ρ, .proj i e =>
    AnnotOkV ρ e ∧ i < 2 ∧
    ∃ u v A Bf, interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v
  | ρ, .eqE _ a b => AnnotOkV ρ a ∧ AnnotOkV ρ b
  | _, .bvar _ => True
  | _, .sort _ => True
  | _, .const _ _ => True
  | _, .prf => True

/-! ### Clause equations -/

@[simp] theorem AnnotOkV_bvar (ρ : Nat → V) (i : Nat) :
    AnnotOkV V ρ (.bvar i) = True := by rw [AnnotOkV]
@[simp] theorem AnnotOkV_sort (ρ : Nat → V) (u : Nat) :
    AnnotOkV V ρ (.sort u) = True := by rw [AnnotOkV]
@[simp] theorem AnnotOkV_const (ρ : Nat → V) (c : BConst) (us : List Nat) :
    AnnotOkV V ρ (.const c us) = True := by rw [AnnotOkV]
@[simp] theorem AnnotOkV_prf (ρ : Nat → V) :
    AnnotOkV V ρ .prf = True := by rw [AnnotOkV]
theorem AnnotOkV_pi (ρ : Nat → V) (A B : VExpr) :
    AnnotOkV V ρ (.pi A B) =
      (AnnotOkV V ρ A ∧
        ∀ x, x ∈ˢ interp V ρ A → AnnotOkV V (cons V x ρ) B) := by
  rw [AnnotOkV]
theorem AnnotOkV_lam (ρ : Nat → V) (A b : VExpr) :
    AnnotOkV V ρ (.lam A b) =
      (AnnotOkV V ρ A ∧
        ∀ x, x ∈ˢ interp V ρ A → AnnotOkV V (cons V x ρ) b) := by
  rw [AnnotOkV]
theorem AnnotOkV_app (ρ : Nat → V) (f a : VExpr) :
    AnnotOkV V ρ (.app f a) =
      (AnnotOkV V ρ f ∧ AnnotOkV V ρ a ∧
        ∃ A B, interp V ρ f ∈ˢ piC A B ∧ interp V ρ a ∈ˢ A) := by
  rw [AnnotOkV]
theorem AnnotOkV_letE (ρ : Nat → V) (T v b : VExpr) :
    AnnotOkV V ρ (.letE T v b) =
      (AnnotOkV V ρ T ∧ AnnotOkV V ρ v ∧
        AnnotOkV V (cons V (interp V ρ v) ρ) b) := by
  rw [AnnotOkV]
theorem AnnotOkV_proj (ρ : Nat → V) (i : Nat) (e : VExpr) :
    AnnotOkV V ρ (.proj i e) =
      (AnnotOkV V ρ e ∧ i < 2 ∧
        ∃ u v A Bf, interp V ρ e ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
          A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v) := by
  rw [AnnotOkV]
theorem AnnotOkV_eqE (ρ : Nat → V) (T a b : VExpr) :
    AnnotOkV V ρ (.eqE T a b) = (AnnotOkV V ρ a ∧ AnnotOkV V ρ b) := by
  rw [AnnotOkV]

/-! ### Interpretation invariance below a bound

The [set] shadow of `cval_closed`'s purpose (design §1.3's I3 note): a
closed term's interpretation does not read the environment. -/

theorem interp_congr_below :
    ∀ (e : VExpr) (k : Nat) (ρ ρ' : Nat → V),
      VExpr.bvarsBelow k e → (∀ i, i < k → ρ i = ρ' i) →
      interp V ρ e = interp V ρ' e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ ρ' hb hag
    exact hag i hb
  | sort u => intros; rfl
  | const c us => intros; rfl
  | app f a ihf iha =>
    intro k ρ ρ' hb hag
    simp only [interp_app, ihf k ρ ρ' hb.1 hag, iha k ρ ρ' hb.2 hag]
  | lam A b ihA ihb =>
    intro k ρ ρ' hb hag
    simp only [interp_lam, ihA k ρ ρ' hb.1 hag]
    congr 1
    funext x
    refine ihb (k + 1) _ _ hb.2 fun i hi => ?_
    cases i with
    | zero => rfl
    | succ j => exact hag j (by omega)
  | pi A B ihA ihB =>
    intro k ρ ρ' hb hag
    simp only [interp_pi, ihA k ρ ρ' hb.1 hag]
    congr 1
    funext x
    refine ihB (k + 1) _ _ hb.2 fun i hi => ?_
    cases i with
    | zero => rfl
    | succ j => exact hag j (by omega)
  | letE T v b ihT ihv ihb =>
    intro k ρ ρ' hb hag
    simp only [interp_letE, ihv k ρ ρ' hb.2.1 hag]
    refine ihb (k + 1) _ _ hb.2.2 fun i hi => ?_
    cases i with
    | zero => rfl
    | succ j => exact hag j (by omega)
  | eqE T a b ihT iha ihb =>
    intro k ρ ρ' hb hag
    simp only [interp_eqE, iha k ρ ρ' hb.2.1 hag, ihb k ρ ρ' hb.2.2 hag]
  | proj i e ihe =>
    intro k ρ ρ' hb hag
    simp only [interp_proj, ihe k ρ ρ' hb hag]
  | prf => intros; rfl

/-- A closed term interprets the same under every environment. -/
theorem interp_closed {e : VExpr} (he : VExpr.Closed e)
    (ρ ρ' : Nat → V) : interp V ρ e = interp V ρ' e :=
  interp_congr_below V e 0 ρ ρ' he (fun i hi => absurd hi (Nat.not_lt_zero i))

/-! ### The substitution metatheory (two lemmas) -/

/-- Truthfulness through lifting: the transpose of `AnnotOk.shift`/
`AnnotOk.lift`, in the two-line form the env-free layer affords. -/
theorem AnnotOkV_liftN (n : Nat) :
    ∀ (e : VExpr) (k : Nat) (ρ : Nat → V),
      AnnotOkV V ρ (e.liftN n k) ↔ AnnotOkV V (shiftE V n k ρ) e := by
  intro e
  induction e with
  | bvar i =>
    intro k ρ
    simp only [VExpr.liftN_bvar]
    split <;> simp
  | sort u => intro k ρ; simp
  | const c us => intro k ρ; simp
  | app f a ihf iha =>
    intro k ρ
    rw [VExpr.liftN_app, AnnotOkV_app, AnnotOkV_app, ihf, iha,
      interp_liftN, interp_liftN]
  | lam A b ihA ihb =>
    intro k ρ
    rw [VExpr.liftN_lam, AnnotOkV_lam, AnnotOkV_lam, ihA, interp_liftN]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    rw [ihb, cons_shiftE]
  | pi A B ihA ihB =>
    intro k ρ
    rw [VExpr.liftN_pi, AnnotOkV_pi, AnnotOkV_pi, ihA, interp_liftN]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    rw [ihB, cons_shiftE]
  | letE T v b ihT ihv ihb =>
    intro k ρ
    rw [VExpr.liftN_letE, AnnotOkV_letE, AnnotOkV_letE, ihT, ihv,
      interp_liftN, ihb, cons_shiftE]
  | eqE T a b ihT iha ihb =>
    intro k ρ
    rw [VExpr.liftN_eqE, AnnotOkV_eqE, AnnotOkV_eqE, iha, ihb]
  | proj i e ihe =>
    intro k ρ
    rw [VExpr.liftN_proj, AnnotOkV_proj, AnnotOkV_proj, ihe, interp_liftN]
  | prf => intro k ρ; simp

/-- Truthfulness through instantiation: the transpose of
`AnnotOk_beta`/`AnnotOk_beta_inv`, both directions in one biconditional
(the substituend's truthfulness `ha` is consumed only right-to-left, at
the substituted variable's own leaf). -/
theorem AnnotOkV_inst :
    ∀ (e a : VExpr) (k : Nat) (ρ : Nat → V),
      AnnotOkV V (shiftE V k 0 ρ) a →
      (AnnotOkV V ρ (e.inst a k) ↔
        AnnotOkV V (instE V k (interp V (shiftE V k 0 ρ) a) ρ) e) := by
  intro e
  induction e with
  | bvar i =>
    intro a k ρ ha
    show AnnotOkV V ρ
        (if i < k then .bvar i
         else if i = k then VExpr.liftN k a else .bvar (i - 1)) ↔ _
    by_cases h : i < k
    · simp [if_pos h]
    · by_cases h2 : i = k
      · simp only [if_neg h, if_pos h2, AnnotOkV_bvar, iff_true]
        exact (AnnotOkV_liftN V k a 0 ρ).mpr ha
      · simp [if_neg h, if_neg h2]
  | sort u => intro a k ρ _; simp [VExpr.inst]
  | const c us => intro a k ρ _; simp [VExpr.inst]
  | app f b ihf ihb =>
    intro a k ρ ha
    rw [VExpr.inst_app, AnnotOkV_app, AnnotOkV_app, ihf a k ρ ha,
      ihb a k ρ ha, interp_inst, interp_inst]
  | lam A b ihA ihb =>
    intro a k ρ ha
    rw [VExpr.inst_lam, AnnotOkV_lam, AnnotOkV_lam, ihA a k ρ ha,
      interp_inst]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    have ha' : AnnotOkV V (shiftE V (k + 1) 0 (cons V x ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihb a (k + 1) (cons V x ρ) ha', shiftE_succ_cons, cons_instE]
  | pi A B ihA ihB =>
    intro a k ρ ha
    rw [VExpr.inst_pi, AnnotOkV_pi, AnnotOkV_pi, ihA a k ρ ha,
      interp_inst]
    refine and_congr Iff.rfl (forall_congr' fun x => imp_congr Iff.rfl ?_)
    have ha' : AnnotOkV V (shiftE V (k + 1) 0 (cons V x ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihB a (k + 1) (cons V x ρ) ha', shiftE_succ_cons, cons_instE]
  | letE T v b ihT ihv ihb =>
    intro a k ρ ha
    rw [VExpr.inst_letE, AnnotOkV_letE, AnnotOkV_letE, ihT a k ρ ha,
      ihv a k ρ ha, interp_inst]
    refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
    have ha' : AnnotOkV V (shiftE V (k + 1) 0
        (cons V (interp V (instE V k (interp V (shiftE V k 0 ρ) a) ρ) v)
          ρ)) a := by
      rw [shiftE_succ_cons]; exact ha
    rw [ihb a (k + 1) _ ha', shiftE_succ_cons, cons_instE]
  | eqE T x y ihT ihx ihy =>
    intro a k ρ ha
    rw [VExpr.inst_eqE, AnnotOkV_eqE, AnnotOkV_eqE, ihx a k ρ ha,
      ihy a k ρ ha]
  | proj i e ihe =>
    intro a k ρ ha
    rw [VExpr.inst_proj, AnnotOkV_proj, AnnotOkV_proj, ihe a k ρ ha,
      interp_inst]
  | prf => intro a k ρ _; simp [VExpr.inst]

/-- Substitution at the outermost binder — the form the β/ζ/telescope
cases use.  Left-to-right is the `AnnotOk_beta_inv` transpose (the
`letE` inference rule's source of the opened body's truthfulness);
right-to-left is `AnnotOk_beta`'s (β/ζ transport onto the reduct). -/
theorem AnnotOkV_inst0 {e a : VExpr} {ρ : Nat → V}
    (ha : AnnotOkV V ρ a) :
    AnnotOkV V ρ (e.inst a) ↔
      AnnotOkV V (cons V (interp V ρ a) ρ) e := by
  have h := AnnotOkV_inst V e a 0 ρ (by rwa [shiftE_zero_zero])
  rwa [shiftE_zero_zero, instE_zero] at h

/-! ### `TeleFitV`: values fitting a `∀`-telescope

The transpose of `TeleFit`/`TeleFitI` over `interp` (design §1.4): each
spine argument's interpretation inhabits the corresponding
progressively-instantiated domain.  `Tele`-sound produces it;
the iota/rescue/eta cases and T5's law eliminations consume it through
the two eliminations below (the `certs_fit` → `app_mem_piC`-chain
re-hang). -/

inductive TeleFitV (ρ : Nat → V) : VExpr → List VExpr → VExpr → Prop where
  | nil {T : VExpr} : TeleFitV ρ T [] T
  | cons {A B a rest : VExpr} {as : List VExpr} :
      interp V ρ a ∈ˢ interp V ρ A →
      TeleFitV ρ (B.inst a) as rest →
      TeleFitV ρ (.pi A B) (a :: as) rest

/-- Elimination onto a head: a member of the telescope's interpretation
applied along a fitting spine lands in the residual's interpretation.
Memberships only — no truthfulness enters. -/
theorem TeleFitV.appN {ρ : Nat → V} {T rest : VExpr} {as : List VExpr}
    (h : TeleFitV V ρ T as rest) :
    ∀ {f : VExpr}, interp V ρ f ∈ˢ interp V ρ T →
      interp V ρ (VExpr.mkAppN f as) ∈ˢ interp V ρ rest := by
  induction h with
  | nil => intro f hf; exact hf
  | cons hmem _ ih =>
    intro f hf
    rw [VExpr.mkAppN_cons]
    refine ih ?_
    rw [interp_app, interp_inst0]
    exact app_mem_piC (by exact hf) hmem

/-- The residual of a truthful telescope walked along truthful
arguments is truthful. -/
theorem TeleFitV.rest_annot {ρ : Nat → V} {T rest : VExpr}
    {as : List VExpr} (h : TeleFitV V ρ T as rest)
    (hT : AnnotOkV V ρ T) (has : ∀ a ∈ as, AnnotOkV V ρ a) :
    AnnotOkV V ρ rest := by
  induction h with
  | nil => exact hT
  | @cons A B a rest as hmem htail ih =>
    rw [AnnotOkV_pi] at hT
    refine ih ?_ fun a' ha' => has a' (List.mem_cons_of_mem _ ha')
    rw [AnnotOkV_inst0 V (has a List.mem_cons_self)]
    exact hT.2 _ hmem

/-- Truthfulness assembly along a fitting spine: the application of a
truthful head (with its membership) to fitting truthful arguments is a
truthful term.  This is the `AnnotOkV`-package factory for the
constructor-spine fabrications (R12–R14) and the iota reduct. -/
theorem TeleFitV.appN_annot {ρ : Nat → V} {T rest : VExpr}
    {as : List VExpr} (h : TeleFitV V ρ T as rest)
    (hT : AnnotOkV V ρ T) (has : ∀ a ∈ as, AnnotOkV V ρ a) :
    ∀ {f : VExpr}, interp V ρ f ∈ˢ interp V ρ T → AnnotOkV V ρ f →
      AnnotOkV V ρ (VExpr.mkAppN f as) := by
  induction h with
  | nil => intro f _ hfA; exact hfA
  | @cons A B a rest as hmem htail ih =>
    intro f hf hfA
    rw [AnnotOkV_pi] at hT
    have haA : AnnotOkV V ρ a := has a List.mem_cons_self
    have hpkg : AnnotOkV V ρ (.app f a) := by
      rw [AnnotOkV_app]
      exact ⟨hfA, haA, _, _, hf, hmem⟩
    rw [VExpr.mkAppN_cons]
    refine ih ?_ (fun a' ha' => has a' (List.mem_cons_of_mem _ ha')) ?_ hpkg
    · rw [AnnotOkV_inst0 V haA]
      exact hT.2 _ hmem
    · rw [interp_app, interp_inst0]
      exact app_mem_piC (by exact hf) hmem

end Setlec.SetR
