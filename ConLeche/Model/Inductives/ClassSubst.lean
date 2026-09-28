module

public import ConLeche.Model.Annot.BitRename
public import ConLeche.Model.Annot.LocList
public import ConLeche.Verify.Inductives.ClassAbs
public import ConLeche.Verify.Level
import ConLeche.Model.Annot.BitInst
import ConLeche.Verify.InstList

public section

/-!
# The class abstraction, READ (PROOFPLAN T3, the substitution law P1)

The class check abstracts every recognised class occurrence of a
constructor's crest to the class's hole (`classAbs`, spec
`classAbsSpec`, `ClassAbs.lean`), top-down, the occurrence matched
SYNTACTICALLY: parameters equal up to the free variables' annotations
(`Expr.eraseFVarTys`) at equal levels, else up to levels with equal
simplified forms (`Expr.eqUpToLevels`); then the coarser tier
(`aliasOcc?`) abstracts the occurrences found per component by defeq.
This file is the model's reading of both passes.

1. **What the reading cannot see** (§1): `Expr.SemEq` — free variables
   by index, levels by value, binder data equal — reads alike
   (`denoteMeta_semEq`); the abstraction's comparisons land in it.
   `eqUpToLevels` is an equivalence.
2. **The replacement congruence** (§2, `classAbsSpec_read`), generic in
   the recogniser: the abstraction and its restriction to kept holes `F`
   read alike wherever every occurrence of a hole outside `F` reads as its
   head abstracted by the restriction.
3. **The recogniser** (§3): an occurrence is its class's key up to
   `SemEq`, the recogniser is spine-coherent, and two spellings related by
   `eqUpToLevels` are recognised alike by classes the same up to spelling.
4. **At true values** (§4, `classAbs_read`): with every class hole holding
   its key's value, the abstracted term reads as the concrete one; the
   coarser tier likewise (§5, `aliasAbs_read`).
5. **At stage values** (§6–§7, `classAbs_read_stage`): the abstraction
   reads as its restriction to a class fact's kept holes (own group, free
   cyclic inner classes), every other class read as its key in hole form
   — P1 in hole form, the head obligation discharged.
6. **The true valuation** (§8): it exists over any parameter and member
   valuation, is stage-coherent, and gives same classes one value (iii).

DESIGN record CLASSCHECK / P2B.
-/

/-! ## 1. What the reading cannot see -/

namespace ConLeche

/-- **Structural equality up to what the reading does not read**: free
variables by index (annotations free), universe levels by their value at
every assignment, binder data equal. -/
@[expose] def Expr.SemEq : Expr → Expr → Prop
  | .bvar i, .bvar j => i = j
  | .fvar i _, .fvar j _ => i = j
  | .sort u, .sort v => ∀ φ, Level.eval φ u = Level.eval φ v
  | .const n us, .const n' us' => n = n' ∧ us.length = us'.length ∧
      ∀ φ, Level.EvalEqList φ us us'
  | .app f a, .app g b => Expr.SemEq f g ∧ Expr.SemEq a b
  | .lam ty b m, .lam ty' b' m' => m = m' ∧ Expr.SemEq ty ty' ∧ Expr.SemEq b b'
  | .forallE ty b m, .forallE ty' b' m' => m = m' ∧ Expr.SemEq ty ty' ∧ Expr.SemEq b b'
  | .letE ty v b, .letE ty' v' b' => Expr.SemEq ty ty' ∧ Expr.SemEq v v' ∧ Expr.SemEq b b'
  | .lit l, .lit l' => l = l'
  | .proj s i e, .proj s' i' e' => s = s' ∧ i = i' ∧ Expr.SemEq e e'
  | _, _ => False

theorem Level.evalEqList_refl (φ : Name → Nat) : ∀ us : List Level, Level.EvalEqList φ us us
  | [] => trivial
  | _ :: us => ⟨rfl, Level.evalEqList_refl φ us⟩

theorem Expr.SemEq.refl : ∀ e : Expr, Expr.SemEq e e := by
  intro e
  induction e <;> simp_all [Expr.SemEq, Level.evalEqList_refl]

/-- Erasure-equal terms are `SemEq`. -/
theorem Expr.semEq_of_erasedEq : ∀ {a b : Expr}, Expr.ErasedEq a b → Expr.SemEq a b := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq]
  | fvar i ty => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq]
  | sort u => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq]
  | const n us =>
    intro b h
    cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq, Level.evalEqList_refl]
  | lit l => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.SemEq]
  | app f a ihf iha =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t bd m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨h.1, iht h.2.1, ihb h.2.2⟩
  | forallE t bd m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨h.1, iht h.2.1, ihb h.2.2⟩
  | letE t v bd iht ihv ihb =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨iht h.1, ihv h.2.1, ihb h.2.2⟩
  | proj s i x ih =>
    intro b h
    cases b <;> simp only [Expr.ErasedEq, Expr.SemEq] at h ⊢
    exact ⟨h.1, h.2.1, ih h.2.2⟩

/-- The annotation-erased comparison is erasure equality. -/
theorem Expr.erasedEq_of_eraseFVarTys : ∀ {a b : Expr},
    a.eraseFVarTys = b.eraseFVarTys → Expr.ErasedEq a b := by
  intro a
  induction a <;> intro b <;> cases b <;>
    simp_all [Expr.eraseFVarTys, Expr.replaceFVars, Expr.ErasedEq]

/-- Pointwise level equivalence is pointwise equal value. -/
theorem Level.evalEqList_of_isEquivList {us vs : List Level}
    (h : Level.isEquivList us vs = some true) :
    us.length = vs.length ∧ ∀ φ, Level.EvalEqList φ us vs := by
  refine ⟨?_, Level.isEquivList_sound h⟩
  have h0 := Level.isEquivList_sound h (fun _ => 0)
  clear h
  induction us generalizing vs with
  | nil => cases vs <;> simp_all [Level.EvalEqList]
  | cons u us ih =>
    cases vs with
    | nil => simp [Level.EvalEqList] at h0
    | cons v vs => simp [ih h0.2]

/-- Levels with equal simplified forms have equal values. -/
theorem Level.eval_eq_of_simplify {u v : Level} (h : Level.simplify u = Level.simplify v)
    (φ : Name → Nat) : Level.eval φ u = Level.eval φ v := by
  rw [← Level.eval_simplify φ u, h, Level.eval_simplify]

/-- Pointwise equal simplified forms: pointwise equal values. -/
theorem Level.evalEqList_of_simplify : ∀ {us vs : List Level},
    us.map Level.simplify = vs.map Level.simplify →
    us.length = vs.length ∧ ∀ φ, Level.EvalEqList φ us vs
  | [], [], _ => ⟨rfl, fun _ => trivial⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | u :: us, v :: vs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨hl, hr⟩ := Level.evalEqList_of_simplify h.2
    exact ⟨by simp [hl], fun φ => ⟨Level.eval_eq_of_simplify h.1 φ, hr φ⟩⟩

/-- **The level-equivalence comparison lands in `SemEq`.** -/
theorem Expr.semEq_of_eqUpToLevels : ∀ {a b : Expr},
    Expr.eqUpToLevels a b = true → Expr.SemEq a b := by
  intro a
  induction a with
  | bvar i => intro b h; cases b <;> simp_all [Expr.eqUpToLevels, Expr.SemEq]
  | fvar i ty => intro b h; cases b <;> simp_all [Expr.eqUpToLevels, Expr.SemEq]
  | sort u =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq, beq_iff_eq] at h ⊢
    exact Level.eval_eq_of_simplify h
  | const n us =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq, Bool.and_eq_true,
      beq_iff_eq] at h ⊢
    obtain ⟨h1, h2⟩ := h
    exact ⟨h1, Level.evalEqList_of_simplify h2⟩
  | lit l => intro b h; cases b <;> simp_all [Expr.eqUpToLevels, Expr.SemEq]
  | app f a ihf iha =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq,
      Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | lam t bd m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq, Bool.and_eq_true,
      beq_iff_eq] at h ⊢
    exact ⟨h.1.1, iht h.1.2, ihb h.2⟩
  | forallE t bd m iht ihb =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq, Bool.and_eq_true,
      beq_iff_eq] at h ⊢
    exact ⟨h.1.1, iht h.1.2, ihb h.2⟩
  | letE t v bd iht ihv ihb =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq,
      Bool.and_eq_true] at h ⊢
    exact ⟨iht h.1.1, ihv h.1.2, ihb h.2⟩
  | proj s i x ih =>
    intro b h
    cases b <;> simp only [Expr.eqUpToLevels, Expr.SemEq, reduceCtorEq, Bool.and_eq_true,
      beq_iff_eq] at h ⊢
    exact ⟨h.1.1, h.1.2, ih h.2⟩

theorem Expr.SemEq.instantiate1 :
    ∀ {e e' v v' : Expr} {k : Nat}, Expr.SemEq e e' → Expr.SemEq v v' →
      Expr.SemEq (e.instantiate1 v k) (e'.instantiate1 v' k) := by
  intro e
  induction e with
  | bvar i =>
    intro e' v v' k he hv
    match e', he with
    | .bvar j, he =>
      obtain rfl : i = j := he
      simp only [Expr.instantiate1]
      split
      · exact hv
      · split <;> simp [Expr.SemEq]
  | fvar idx ty =>
    intro e' v v' k he hv
    match e', he with
    | .fvar j ty', he => simpa [Expr.instantiate1, Expr.SemEq] using he
  | sort u =>
    intro e' v v' k he hv
    match e', he with
    | .sort u', he => simpa [Expr.instantiate1, Expr.SemEq] using he
  | const n us =>
    intro e' v v' k he hv
    match e', he with
    | .const n' us', he => simpa [Expr.instantiate1, Expr.SemEq] using he
  | app f a ihf iha =>
    intro e' v v' k he hv
    match e', he with
    | .app g b, he => exact ⟨ihf he.1 hv, iha he.2 hv⟩
  | lam ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .lam ty' body' m', he => exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | forallE ty body m ihty ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .forallE ty' body' m', he => exact ⟨he.1, ihty he.2.1 hv, ihbody he.2.2 hv⟩
  | letE ty vl body ihty ihv ihbody =>
    intro e' v v' k he hv
    match e', he with
    | .letE ty' vl' body', he => exact ⟨ihty he.1 hv, ihv he.2.1 hv, ihbody he.2.2 hv⟩
  | lit l =>
    intro e' v v' k he hv
    match e', he with
    | .lit l', he => simpa [Expr.instantiate1, Expr.SemEq] using he
  | proj sn i pe ih =>
    intro e' v v' k he hv
    match e', he with
    | .proj sn' i' pe', he => exact ⟨he.1, he.2.1, ih he.2.2 hv⟩

/-- `SemEq` terms have the same loose bound variables. -/
theorem Expr.SemEq.looseBVarsBounded : ∀ {a b : Expr}, Expr.SemEq a b →
    ∀ k, a.looseBVarsBounded k = b.looseBVarsBounded k := by
  intro a
  induction a with
  | bvar i => intro b h k; cases b <;> simp_all [Expr.SemEq, Expr.looseBVarsBounded]
  | app f a ihf iha =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, ihf h.1, iha h.2]
  | lam t bd m iht ihb =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, iht h.2.1, ihb h.2.2]
  | forallE t bd m iht ihb =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, iht h.2.1, ihb h.2.2]
  | letE t v bd iht ihv ihb =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, iht h.1, ihv h.2.1, ihb h.2.2]
  | proj s i x ih =>
    intro b h k
    cases b <;> simp only [Expr.SemEq] at h
    simp [Expr.looseBVarsBounded, ih h.2.2]
  | _ => intro b h k; cases b <;> simp_all [Expr.SemEq, Expr.looseBVarsBounded]

theorem Expr.eqUpToLevels_refl : ∀ e : Expr, Expr.eqUpToLevels e e = true := by
  intro e; induction e <;> simp_all [Expr.eqUpToLevels]

theorem Expr.eqUpToLevels_symm : ∀ {a b : Expr}, Expr.eqUpToLevels a b = true →
    Expr.eqUpToLevels b a = true := by
  intro a
  induction a with
  | app f x ihf ihx =>
    intro b h; cases b <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq] at h ⊢
    exact ⟨ihf h.1, ihx h.2⟩
  | lam t bd m iht ihb =>
    intro b h; cases b <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq, beq_iff_eq] at h ⊢
    exact ⟨⟨h.1.1.symm, iht h.1.2⟩, ihb h.2⟩
  | forallE t bd m iht ihb =>
    intro b h; cases b <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq, beq_iff_eq] at h ⊢
    exact ⟨⟨h.1.1.symm, iht h.1.2⟩, ihb h.2⟩
  | letE t v bd iht ihv ihb =>
    intro b h; cases b <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq] at h ⊢
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s i x ih =>
    intro b h; cases b <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq, beq_iff_eq] at h ⊢
    exact ⟨⟨h.1.1.symm, h.1.2.symm⟩, ih h.2⟩
  | bvar i => intro b h; cases b <;> simp_all [Expr.eqUpToLevels]
  | fvar i ty => intro b h; cases b <;> simp_all [Expr.eqUpToLevels]
  | sort u =>
    intro b h; cases b <;> simp only [Expr.eqUpToLevels, beq_iff_eq, reduceCtorEq] at h ⊢
    exact h.symm
  | const n us =>
    intro b h; cases b <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, beq_iff_eq,
      reduceCtorEq] at h ⊢
    exact ⟨h.1.symm, h.2.symm⟩
  | lit l =>
    intro b h; cases b <;> simp only [Expr.eqUpToLevels, beq_iff_eq, reduceCtorEq] at h ⊢
    exact h.symm

theorem Expr.eqUpToLevels_trans : ∀ {a b c : Expr}, Expr.eqUpToLevels a b = true →
    Expr.eqUpToLevels b c = true → Expr.eqUpToLevels a c = true := by
  intro a
  induction a with
  | app f x ihf ihx =>
    intro b c h1 h2; cases b <;> cases c <;>
      simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq] at h1 h2 ⊢
    exact ⟨ihf h1.1 h2.1, ihx h1.2 h2.2⟩
  | lam t bd m iht ihb =>
    intro b c h1 h2; cases b <;> cases c <;>
      simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq, beq_iff_eq] at h1 h2 ⊢
    exact ⟨⟨h1.1.1.trans h2.1.1, iht h1.1.2 h2.1.2⟩, ihb h1.2 h2.2⟩
  | forallE t bd m iht ihb =>
    intro b c h1 h2; cases b <;> cases c <;>
      simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq, beq_iff_eq] at h1 h2 ⊢
    exact ⟨⟨h1.1.1.trans h2.1.1, iht h1.1.2 h2.1.2⟩, ihb h1.2 h2.2⟩
  | letE t v bd iht ihv ihb =>
    intro b c h1 h2; cases b <;> cases c <;>
      simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq] at h1 h2 ⊢
    exact ⟨⟨iht h1.1.1 h2.1.1, ihv h1.1.2 h2.1.2⟩, ihb h1.2 h2.2⟩
  | proj s i x ih =>
    intro b c h1 h2; cases b <;> cases c <;>
      simp only [Expr.eqUpToLevels, Bool.and_eq_true, reduceCtorEq, beq_iff_eq] at h1 h2 ⊢
    exact ⟨⟨h1.1.1.trans h2.1.1, h1.1.2.trans h2.1.2⟩, ih h1.2 h2.2⟩
  | _ => intro b c h1 h2; cases b <;> cases c <;> simp_all [Expr.eqUpToLevels]

theorem Expr.eqUpToLevels_of_erasedEq : ∀ {a b : Expr}, Expr.ErasedEq a b →
    Expr.eqUpToLevels a b = true := by
  intro a
  induction a with
  | app f x ihf ihx =>
    intro b h; cases b <;> simp only [Expr.ErasedEq, Expr.eqUpToLevels, Bool.and_eq_true] at h ⊢
    exact ⟨ihf h.1, ihx h.2⟩
  | lam t bd m iht ihb =>
    intro b h; cases b <;> simp only [Expr.ErasedEq, Expr.eqUpToLevels, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨⟨h.1, iht h.2.1⟩, ihb h.2.2⟩
  | forallE t bd m iht ihb =>
    intro b h; cases b <;> simp only [Expr.ErasedEq, Expr.eqUpToLevels, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨⟨h.1, iht h.2.1⟩, ihb h.2.2⟩
  | letE t v bd iht ihv ihb =>
    intro b h; cases b <;> simp only [Expr.ErasedEq, Expr.eqUpToLevels, Bool.and_eq_true] at h ⊢
    exact ⟨⟨iht h.1, ihv h.2.1⟩, ihb h.2.2⟩
  | proj s i x ih =>
    intro b h; cases b <;> simp only [Expr.ErasedEq, Expr.eqUpToLevels, Bool.and_eq_true, beq_iff_eq] at h ⊢
    exact ⟨⟨h.1, h.2.1⟩, ih h.2.2⟩
  | _ => intro b h; cases b <;> simp_all [Expr.ErasedEq, Expr.eqUpToLevels]

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo BinderMeta)

universe w

section Read

variable {env : Env} {φ : Name → Nat} {acval : Name → (Name → Nat) → AnnotTerm}

/-- **`SemEq` terms read alike** — (i) and (ii) of the P2A record: the
annotation-erased and the level-equivalent comparison. -/
theorem denoteMeta_semEq :
    ∀ {e₁ e₂ : Expr}, Expr.SemEq e₁ e₂ →
      ∀ d : Nat, denoteMeta acval env φ d e₁ = denoteMeta acval env φ d e₂
  | .bvar i, e₂, he, _ => by
    match e₂, he with
    | .bvar j, he => obtain rfl : i = j := he; rfl
  | .fvar i ty, e₂, he, d => by
    match e₂, he with
    | .fvar j ty', he =>
      obtain rfl : i = j := he
      simp [denoteMeta_fvar]
  | .sort u, e₂, he, _ => by
    match e₂, he with
    | .sort u', he => rw [denoteMeta, denoteMeta, he φ]
  | .const n us, e₂, he, _ => by
    match e₂, he with
    | .const n' us', he =>
      obtain ⟨rfl, hlen, hev⟩ := he
      rw [denoteMeta, denoteMeta]
      cases env.find? n with
      | none => rfl
      | some ci =>
        simp only [hlen, Level.substFn_congr (hev φ)]
  | .app f a, e₂, he, d => by
    match e₂, he with
    | .app g b, he =>
      obtain ⟨h1, h2⟩ := he
      simp only [denoteMeta_app, denoteMeta_semEq h1 d, denoteMeta_semEq h2 d]
  | .forallE ty body m, e₂, he, d => by
    match e₂, he with
    | .forallE ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ := he
      simp only [denoteMeta_forallE, denoteMeta_semEq h1 d,
        denoteMeta_semEq (Expr.SemEq.instantiate1 h2
          (show Expr.SemEq (.fvar d ty) (.fvar d ty') from rfl)) (d + 1)]
  | .lam ty body m, e₂, he, d => by
    match e₂, he with
    | .lam ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ := he
      simp only [denoteMeta_lam, denoteMeta_semEq h1 d,
        denoteMeta_semEq (Expr.SemEq.instantiate1 h2
          (show Expr.SemEq (.fvar d ty) (.fvar d ty') from rfl)) (d + 1)]
  | .letE ty vl body, e₂, he, d => by
    match e₂, he with
    | .letE ty' vl' body', he => rw [denoteMeta, denoteMeta]
  | .lit l, e₂, he, _ => by
    match e₂, he with
    | .lit l', he => obtain rfl : l = l' := he; rfl
  | .proj s i e, e₂, he, d => by
    match e₂, he with
    | .proj s' i' e', he =>
      obtain ⟨rfl, rfl, h⟩ := he
      simp only [denoteMeta_proj, denoteMeta_semEq h d]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

end Read

/-! ## 2. The replacement congruence, generic in the recogniser -/

/-- Two optional readings agree: both absent, or both present and
related. -/
@[expose] def OptAgree (P : AnnotTerm → AnnotTerm → Prop) :
    Option AnnotTerm → Option AnnotTerm → Prop
  | some a2, some a1 => P a2 a1
  | none, none => True
  | _, _ => False

theorem OptAgree.refl {P : AnnotTerm → AnnotTerm → Prop} (hP : ∀ a, P a a) :
    ∀ o : Option AnnotTerm, OptAgree P o o
  | none => trivial
  | some a => hP a

/-- **Value agreement** at every admissible base valuation, `d` local
values above it. -/
@[expose] def ValAgree (V : Type w) [SetTheory V] (Good : (Nat → V) → Prop) (d : Nat)
    (a2 a1 : AnnotTerm) : Prop :=
  ∀ (vals : List V) (τ : Nat → V), vals.length = d → Good τ →
    interp V (consList vals τ) a2 = interp V (consList vals τ) a1

/-- A recogniser restricted to the holes `F` keeps: the occurrences of
the other holes are not recognised. -/
@[expose] def occRestrict (occ : Expr → Option (Expr × Nat)) (F : Expr → Bool) :
    Expr → Option (Expr × Nat) := fun x =>
  match occ x with
  | some (h, n) => if F h then some (h, n) else none
  | none => none

theorem occRestrict_eq_none_of {occ : Expr → Option (Expr × Nat)} {F : Expr → Bool} {x h : Expr}
    {n : Nat} (hx : occ x = some (h, n)) (hF : F h = false) : occRestrict occ F x = none := by
  simp [occRestrict, hx, hF]

theorem occRestrict_eq_some_of {occ : Expr → Option (Expr × Nat)} {F : Expr → Bool} {x h : Expr}
    {n : Nat} (hx : occ x = some (h, n)) (hF : F h = true) :
    occRestrict occ F x = some (h, n) := by
  simp [occRestrict, hx, hF]

theorem occRestrict_eq_none {occ : Expr → Option (Expr × Nat)} {F : Expr → Bool} {x : Expr}
    (hx : occ x = none) : occRestrict occ F x = none := by
  simp [occRestrict, hx]

/-- The empty recogniser abstracts nothing. -/
theorem classAbsSpec_none : ∀ e : Expr, classAbsSpec (fun _ => none) none e = e := by
  intro e
  induction e <;> simp_all [classAbsSpec]

theorem occRestrict_false (occ : Expr → Option (Expr × Nat)) :
    occRestrict occ (fun _ => false) = fun _ => none := by
  funext x
  simp only [occRestrict]
  split <;> simp

/-- **What the congruence needs of a recogniser** `occ` and the kept
holes `F`: a recognised occurrence is an application spine whose head
part is recognised with one index fewer (so the abstraction's `some`
mode never leaves the spine), its hole a free variable; and an
occurrence of a hole outside `F` reads, at every admissible valuation,
as its head part abstracted by the restriction. -/
structure AbsReadHyps (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (H : Nat) (Good : (Nat → V) → Prop)
    (occ : Expr → Option (Expr × Nat)) (F : Expr → Bool) : Prop where
  spine : ∀ x h n, occ x = some (h, n + 1) → ∃ f a, x = .app f a ∧ occ f = some (h, n)
  hole : ∀ x h n, occ x = some (h, n) → ∃ i ty, h = .fvar i ty
  head : ∀ x h, occ x = some (h, 0) → F h = false →
    ∀ d as2 as1, LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V Good d) (denoteMeta acval env φ (H + d) h)
        (denoteMeta acval env φ (H + d)
          ((classAbsSpec (occRestrict occ F) none x).instantiateList as1 0))

section Congr

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm} {H : Nat} {Good : (Nat → V) → Prop}
  {occ : Expr → Option (Expr × Nat)} {F : Expr → Bool}

theorem optAgree_refl' {d : Nat} (o : Option AnnotTerm) : OptAgree (ValAgree V Good d) o o :=
  OptAgree.refl (fun _ _ _ _ _ => rfl) o

/-- Application congruence of the agreement. -/
theorem optAgree_app {d : Nat} {f2 f1 a2 a1 : Option AnnotTerm}
    (hf : OptAgree (ValAgree V Good d) f2 f1) (ha : OptAgree (ValAgree V Good d) a2 a1) :
    OptAgree (ValAgree V Good d) (do let f ← f2; let a ← a2; some (.app f a))
      (do let f ← f1; let a ← a1; some (.app f a)) := by
  cases f2 <;> cases f1 <;> cases a2 <;> cases a1 <;> simp_all [OptAgree]
  intro vals τ hvl hτ
  simp [hf vals τ hvl hτ, ha vals τ hvl hτ]

theorem interp_projAV_congr {ρ : Nat → V} :
    ∀ (n : Nat) {e2 e1 : AnnotTerm}, interp V ρ e2 = interp V ρ e1 →
      interp V ρ (projAV n e2) = interp V ρ (projAV n e1)
  | 0, _, _, h => by simp [projAV, h]
  | n + 1, _, _, h => interp_projAV_congr n (by simp [h])

/-- A hole read at depth `H + d`, opened or not. -/
theorem hole_inst {h : Expr} (hh : ∃ i ty, h = .fvar i ty) (as : List Expr) :
    h.instantiateList as 0 = h := by
  obtain ⟨i, ty, rfl⟩ := hh
  simp [Expr.instantiateList]

/-- Two openings at the same indices read alike. -/
theorem denoteMeta_inst_locList {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2)
    (h1 : LocList H d as1) (e : Expr) :
    denoteMeta acval env φ (H + d) (e.instantiateList as2 0)
      = denoteMeta acval env φ (H + d) (e.instantiateList as1 0) := by
  apply denoteMeta_semEq
  have key : ∀ (e : Expr) (k : Nat), Expr.SemEq (e.instantiateList as2 k)
      (e.instantiateList as1 k) := by
    intro e
    induction e with
    | bvar j =>
      intro k
      by_cases hjk : j < k
      · simp only [Expr.instantiateList, if_pos hjk]
        exact Expr.SemEq.refl _
      · by_cases hj : j - k < d
        · obtain ⟨ty2, hty2⟩ := h2.2 (j - k) hj
          obtain ⟨ty1, hty1⟩ := h1.2 (j - k) hj
          obtain ⟨hl2, hg2⟩ := List.getElem?_eq_some_iff.mp hty2
          obtain ⟨hl1, hg1⟩ := List.getElem?_eq_some_iff.mp hty1
          simp only [Expr.instantiateList, if_neg hjk, dif_pos hl2, dif_pos hl1, hg2, hg1]
          exact rfl
        · simp only [Expr.instantiateList, if_neg hjk, h2.1, h1.1, dif_neg hj]
          exact Expr.SemEq.refl _
    | app f a ihf iha =>
      intro k; simp only [Expr.instantiateList]; exact ⟨ihf k, iha k⟩
    | lam t b m iht ihb =>
      intro k; simp only [Expr.instantiateList]; exact ⟨rfl, iht k, ihb (k + 1)⟩
    | forallE t b m iht ihb =>
      intro k; simp only [Expr.instantiateList]; exact ⟨rfl, iht k, ihb (k + 1)⟩
    | letE t v b iht ihv ihb =>
      intro k; simp only [Expr.instantiateList]; exact ⟨iht k, ihv k, ihb (k + 1)⟩
    | proj s i x ih =>
      intro k; simp only [Expr.instantiateList]; exact ⟨rfl, rfl, ih k⟩
    | _ => intro k; simp only [Expr.instantiateList]; exact Expr.SemEq.refl _
  exact key e 0

set_option maxHeartbeats 1600000 in
/-- **The replacement congruence** (see the module docstring): the
abstraction by `occ` and by its restriction to `F` read alike, opened at
any `d` locals, at every admissible valuation — and the `some` mode's
version at a recognised occurrence. -/
theorem classAbsSpec_read_both (hyp : AbsReadHyps V acval env φ H Good occ F) :
    ∀ e : Expr,
      (∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V Good d)
          (denoteMeta acval env φ (H + d) ((classAbsSpec occ none e).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict occ F) none e).instantiateList as1 0))) ∧
      (∀ h n, occ e = some (h, n) →
        ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V Good d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec occ (some (h, n)) e).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((if F h then classAbsSpec (occRestrict occ F) (some (h, n)) e
              else classAbsSpec (occRestrict occ F) none e).instantiateList as1 0))) := by
  -- the `some` mode at a head part (index count `0`)
  have hzero : ∀ (e h : Expr), occ e = some (h, 0) →
      ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V Good d)
        (denoteMeta acval env φ (H + d)
          ((classAbsSpec occ (some (h, 0)) e).instantiateList as2 0))
        (denoteMeta acval env φ (H + d)
          ((if F h then classAbsSpec (occRestrict occ F) (some (h, 0)) e
            else classAbsSpec (occRestrict occ F) none e).instantiateList as1 0)) := by
    intro e h he d as2 as1 h2 h1
    have hh := hyp.hole e h 0 he
    cases hF : F h with
    | true =>
      simp only [classAbsSpec, if_true, hole_inst hh]
      exact optAgree_refl' (V := V) _
    | false =>
      simp only [classAbsSpec, Bool.false_eq_true, if_false, hole_inst hh]
      exact hyp.head e h he hF d as2 as1 h2 h1
  intro e
  induction e with
  | app f a ihf iha =>
    -- the `some` mode, by the index count
    have hsome : ∀ h n, occ (.app f a) = some (h, n) →
        ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V Good d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec occ (some (h, n)) (.app f a)).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((if F h then classAbsSpec (occRestrict occ F) (some (h, n)) (.app f a)
              else classAbsSpec (occRestrict occ F) none (.app f a)).instantiateList as1 0)) := by
      intro h n he d as2 as1 h2 h1
      rcases n with _ | n
      · exact hzero _ h he d as2 as1 h2 h1
      · obtain ⟨f', a', hfa, hf'⟩ := hyp.spine _ h n he
        obtain ⟨rfl, rfl⟩ : f = f' ∧ a = a' := by simpa using hfa
        have hF1 := ihf.2 h n hf' d as2 as1 h2 h1
        have hA1 := iha.1 d as2 as1 h2 h1
        cases hF : F h with
        | true =>
          simp only [hF, if_true] at hF1 ⊢
          simp only [classAbsSpec, Expr.instantiateList, denoteMeta_app]
          exact optAgree_app hF1 hA1
        | false =>
          simp only [hF, Bool.false_eq_true, if_false] at hF1 ⊢
          have hR : occRestrict occ F (.app f a) = none := occRestrict_eq_none_of he hF
          simp only [classAbsSpec, hR, Expr.instantiateList, denoteMeta_app]
          exact optAgree_app hF1 hA1
    refine ⟨fun d as2 as1 h2 h1 => ?_, hsome⟩
    cases he : occ (.app f a) with
    | none =>
      have hR : occRestrict occ F (.app f a) = none := occRestrict_eq_none he
      simp only [classAbsSpec, he, hR, Expr.instantiateList, denoteMeta_app]
      exact optAgree_app (ihf.1 d as2 as1 h2 h1) (iha.1 d as2 as1 h2 h1)
    | some p =>
      obtain ⟨h, n⟩ := p
      have hs := hsome h n he d as2 as1 h2 h1
      -- the `none` mode at a recognised occurrence IS the `some` mode
      have hL : classAbsSpec occ none (.app f a) = classAbsSpec occ (some (h, n)) (.app f a) := by
        rcases n with _ | n
        · simp [classAbsSpec, he]
        · simp [classAbsSpec, he]
      rw [hL]
      cases hF : F h with
      | true =>
        have hR : occRestrict occ F (.app f a) = some (h, n) := occRestrict_eq_some_of he hF
        have hL' : classAbsSpec (occRestrict occ F) none (.app f a)
            = classAbsSpec (occRestrict occ F) (some (h, n)) (.app f a) := by
          rcases n with _ | n
          · simp [classAbsSpec, hR]
          · simp [classAbsSpec, hR]
        rw [hL']
        simpa [hF] using hs
      | false => simpa [hF] using hs
  | lam ty b bm iht ihb | forallE ty b bm iht ihb =>
    refine ⟨fun d as2 as1 h2 h1 => ?_, fun h n he => ?_⟩
    rotate_left
    · rcases n with _ | n
      · exact hzero _ h he
      · obtain ⟨f', a', hfa, -⟩ := hyp.spine _ h n he
        exact nomatch hfa
    have hT := iht.1 d as2 as1 h2 h1
    simp only [classAbsSpec, Expr.instantiateList]
    first
    | rw [denoteMeta_lam, denoteMeta_lam]
    | rw [denoteMeta_forallE, denoteMeta_forallE]
    revert hT
    cases hA2 : denoteMeta acval env φ (H + d)
        ((classAbsSpec occ none ty).instantiateList as2 0)
      <;> cases hA1 : denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict occ F) none ty).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i A2 A1
    intro hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons]
    have hB := ihb.1 (d + 1) _ _ (h2.cons ((classAbsSpec occ none ty).instantiateList as2 0))
      (h1.cons ((classAbsSpec (occRestrict occ F) none ty).instantiateList as1 0))
    rw [show H + (d + 1) = H + d + 1 by omega] at hB
    revert hB
    cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec occ none b).instantiateList
          (Expr.fvar (H + d) ((classAbsSpec occ none ty).instantiateList as2 0) :: as2) 0)
      <;> cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec (occRestrict occ F) none b).instantiateList
          (Expr.fvar (H + d) ((classAbsSpec (occRestrict occ F) none ty).instantiateList as1 0)
            :: as1) 0)
      <;> simp [OptAgree]
    rename_i b2 b1
    intro hb vals τ hvl hτ
    have hbx : ∀ x : V, interp V (cons x (consList vals τ)) b2
        = interp V (cons x (consList vals τ)) b1 := by
      intro x
      have := hb (vals ++ [x]) τ (by simp [hvl]) hτ
      simpa [consList_append] using this
    first
    | (simp only [interp_lam, hA vals τ hvl hτ]; exact lamR_congr fun x _ => hbx x)
    | (simp only [interp_pi, hA vals τ hvl hτ]; exact piR_congr fun x _ => hbx x)
  | proj sn i x ihx =>
    refine ⟨fun d as2 as1 h2 h1 => ?_, fun h n he => ?_⟩
    rotate_left
    · rcases n with _ | n
      · exact hzero _ h he
      · obtain ⟨f', a', hfa, -⟩ := hyp.spine _ h n he
        exact nomatch hfa
    have hX := ihx.1 d as2 as1 h2 h1
    simp only [classAbsSpec, Expr.instantiateList, denoteMeta_proj]
    revert hX
    cases denoteMeta acval env φ (H + d) ((classAbsSpec occ none x).instantiateList as2 0)
      <;> cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict occ F) none x).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i e2 e1
    intro he
    cases env.findProj? sn i with
    | some entry =>
      intro vals τ hvl hτ
      exact interp_projAV_congr _ (he vals τ hvl hτ)
    | none =>
      rcases i with _ | _ | i
      · intro vals τ hvl hτ
        simp [he vals τ hvl hτ]
      · intro vals τ hvl hτ
        simp [he vals τ hvl hτ]
      · simp [AnnotTerm.projPair?]
  | letE t v b =>
    refine ⟨fun d as2 as1 h2 h1 => ?_, fun h n he => ?_⟩
    rotate_left
    · rcases n with _ | n
      · exact hzero _ h he
      · obtain ⟨f', a', hfa, -⟩ := hyp.spine _ h n he
        exact nomatch hfa
    simp only [classAbsSpec, Expr.instantiateList]
    rw [denoteMeta, denoteMeta]
    trivial
  | _ =>
    refine ⟨fun d as2 as1 h2 h1 => ?_, fun h n he => ?_⟩
    rotate_left
    · rcases n with _ | n
      · exact hzero _ h he
      · obtain ⟨f', a', hfa, -⟩ := hyp.spine _ h n he
        exact nomatch hfa
    simp only [classAbsSpec]
    rw [denoteMeta_inst_locList h2 h1]
    exact optAgree_refl' (V := V) _

/-- **The replacement congruence.** -/
theorem classAbsSpec_read (hyp : AbsReadHyps V acval env φ H Good occ F) (e : Expr) {d : Nat}
    {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V Good d)
      (denoteMeta acval env φ (H + d) ((classAbsSpec occ none e).instantiateList as2 0))
      (denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict occ F) none e).instantiateList as1 0)) :=
  (classAbsSpec_read_both hyp e).1 d as2 as1 h2 h1

end Congr

/-! ## 3. The class check's recogniser -/

section Occ

open ConLeche (ClassInfo classOcc? classAbs)

theorem Expr.mkAppN_append' (f : Expr) (as bs : List Expr) :
    Expr.mkAppN f (as ++ bs) = Expr.mkAppN (Expr.mkAppN f as) bs := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => exact ih _

/-- A term is its head applied to its arguments. -/
theorem Expr.mkAppN_getAppFn_getAppArgs : ∀ e : Expr,
    Expr.mkAppN e.getAppFn e.getAppArgs = e
  | .app f a => by
    rw [Expr.getAppFn, Expr.getAppArgs, Expr.mkAppN_append', Expr.mkAppN_getAppFn_getAppArgs f]
    rfl
  | .bvar _ | .fvar .. | .sort _ | .const .. | .lam .. | .forallE .. | .letE .. | .lit _
  | .proj .. => rfl

/-- `SemEq` spines. -/
theorem Expr.SemEq.mkAppN : ∀ {as bs : List Expr} {f g : Expr}, Expr.SemEq f g →
    as.length = bs.length → (∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b → Expr.SemEq a b) →
    Expr.SemEq (Expr.mkAppN f as) (Expr.mkAppN g bs)
  | [], [], _, _, hfg, _, _ => hfg
  | a :: as, b :: bs, f, g, hfg, hl, hab =>
    Expr.SemEq.mkAppN (as := as) (bs := bs) (f := .app f a) (g := .app g b)
      ⟨hfg, hab 0 a b rfl rfl⟩ (by simpa using hl) (fun i a' b' h1 h2 => hab (i + 1) a' b' h1 h2)
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl

theorem Expr.erasedEq_eraseFVarTys : ∀ e : Expr, Expr.ErasedEq e e.eraseFVarTys := by
  intro e
  induction e <;> simp_all [Expr.eraseFVarTys, Expr.replaceFVars, Expr.ErasedEq]

theorem Expr.eraseFVarTys_idem (e : Expr) : e.eraseFVarTys.eraseFVarTys = e.eraseFVarTys := by
  induction e <;> simp_all [Expr.eraseFVarTys, Expr.replaceFVars]

/-- Erasure-equal lists are pointwise `SemEq`. -/
theorem semEq_of_map_erase {as bs : List Expr}
    (h : as.map Expr.eraseFVarTys = bs.map Expr.eraseFVarTys) :
    as.length = bs.length ∧ ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b → Expr.SemEq a b := by
  refine ⟨by simpa using congrArg List.length h, fun i a b ha hb => ?_⟩
  have := congrArg (·[i]?) h
  simp only [List.getElem?_map, ha, hb, Option.map_some, Option.some.injEq] at this
  exact Expr.semEq_of_erasedEq (Expr.erasedEq_of_eraseFVarTys this)

/-- Pointwise level-equivalent lists are pointwise `SemEq`. -/
theorem semEq_of_zip_eqUpToLevels {as bs : List Expr}
    (h : ((as.zip bs).all fun (a, b) => a.eqUpToLevels b) = true) :
    ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b → Expr.SemEq a b := by
  intro i a b ha hb
  rw [List.all_eq_true] at h
  have hz : (as.zip bs)[i]? = some (a, b) := by simp [List.getElem?_zip_eq_some, ha, hb]
  exact Expr.semEq_of_eqUpToLevels (h (a, b) (List.mem_of_getElem? hz))

/-- **What the class check's recogniser needs of the classes**: every
container class's hole is a variable below the frame `H`; its erased
parameters are its parameters erased, as many as the container's; its
key is scoped at `H` with no loose bound variable; classes of one
inductive have one parameter count. -/
structure ClassOccWF (cls : List ClassInfo) (H : Nat) : Prop where
  hole : ∀ c ∈ cls, ∀ h, c.hole = some h → ∃ i ty, h = .fvar i ty ∧ i < H
  dsE : ∀ c ∈ cls, c.hole.isSome → c.dsE = c.dsA.map Expr.eraseFVarTys
  len : ∀ c ∈ cls, c.hole.isSome → c.dsA.length = c.nPc
  keyScoped : ∀ c ∈ cls, c.hole.isSome →
    Expr.WScoped H (Expr.mkAppN (.const c.key.ind c.key.lvls) c.dsA) ∧
    (Expr.mkAppN (.const c.key.ind c.key.lvls) c.dsA).looseBVarsBounded 0 = true
  nPc : ∀ c ∈ cls, ∀ c' ∈ cls, c.hole.isSome → c'.hole.isSome → c.key.ind = c'.key.ind →
    c.nPc = c'.nPc

/-- A class's member-abstracted key. -/
@[expose] def classKeyA (c : ClassInfo) : Expr := Expr.mkAppN (.const c.key.ind c.key.lvls) c.dsA

/-! ### Two spellings of one class are recognised alike -/

/-- Pointwise `eqUpToLevels`. -/
@[expose] def LvEqL (as bs : List Expr) : Prop :=
  as.length = bs.length ∧
    ∀ (i : Nat) (a b : Expr), as[i]? = some a → bs[i]? = some b → Expr.eqUpToLevels a b = true

theorem LvEqL.symm {as bs : List Expr} (h : LvEqL as bs) : LvEqL bs as :=
  ⟨h.1.symm, fun i a b ha hb => Expr.eqUpToLevels_symm (h.2 i b a hb ha)⟩

theorem LvEqL.trans {as bs cs : List Expr} (h1 : LvEqL as bs) (h2 : LvEqL bs cs) : LvEqL as cs := by
  refine ⟨h1.1.trans h2.1, fun i a c ha hc => ?_⟩
  have hi : i < bs.length := by
    have := (List.getElem?_eq_some_iff.mp ha).1
    have := h1.1
    omega
  obtain ⟨b, hb⟩ : ∃ b, bs[i]? = some b := ⟨bs[i], List.getElem?_eq_getElem hi⟩
  exact Expr.eqUpToLevels_trans (h1.2 i a b ha hb) (h2.2 i b c hb hc)

theorem lvEqL_of_zip {as bs : List Expr} (hl : as.length = bs.length)
    (h : ((as.zip bs).all fun (a, b) => a.eqUpToLevels b) = true) : LvEqL as bs := by
  refine ⟨hl, fun i a b ha hb => ?_⟩
  rw [List.all_eq_true] at h
  have hz : (as.zip bs)[i]? = some (a, b) := by simp [List.getElem?_zip_eq_some, ha, hb]
  exact h (a, b) (List.mem_of_getElem? hz)

theorem zip_of_lvEqL {as bs : List Expr} (h : LvEqL as bs) :
    ((as.zip bs).all fun (a, b) => a.eqUpToLevels b) = true := by
  rw [List.all_eq_true]
  intro ab hab
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hab
  have h1 : as[i]? = some ab.1 := by
    have := List.getElem?_eq_getElem hi
    rw [hget, List.getElem?_zip_eq_some] at this
    exact this.1
  have h2 : bs[i]? = some ab.2 := by
    have := List.getElem?_eq_getElem hi
    rw [hget, List.getElem?_zip_eq_some] at this
    exact this.2
  exact h.2 i ab.1 ab.2 h1 h2

theorem lvEqL_of_map_erase {as bs : List Expr}
    (h : as.map Expr.eraseFVarTys = bs.map Expr.eraseFVarTys) : LvEqL as bs := by
  refine ⟨by simpa using congrArg List.length h, fun i a b ha hb => ?_⟩
  have := congrArg (·[i]?) h
  simp only [List.getElem?_map, ha, hb, Option.map_some, Option.some.injEq] at this
  exact Expr.eqUpToLevels_of_erasedEq (Expr.erasedEq_of_eraseFVarTys this)

theorem LvEqL.take {as bs : List Expr} (h : LvEqL as bs) (n : Nat) :
    LvEqL (as.take n) (bs.take n) := by
  refine ⟨by simp [h.1], fun i a b ha hb => ?_⟩
  rw [List.getElem?_take] at ha hb
  split at ha
  · rw [if_pos (by assumption)] at hb
    exact h.2 i a b ha hb
  · exact nomatch ha

theorem LvEqL.append {as bs cs ds : List Expr} (h1 : LvEqL as bs) (h2 : LvEqL cs ds) :
    LvEqL (as ++ cs) (bs ++ ds) := by
  refine ⟨by simp [h1.1, h2.1], fun i a b ha hb => ?_⟩
  rw [List.getElem?_append] at ha hb
  split at ha
  · rename_i hi
    rw [if_pos (by rw [← h1.1]; exact hi)] at hb
    exact h1.2 i a b ha hb
  · rename_i hi
    rw [if_neg (by rw [← h1.1]; exact hi), ← h1.1] at hb
    exact h2.2 _ a b ha hb

/-- The spine of related terms: related heads, related arguments. -/
theorem Expr.eqUpToLevels_spine : ∀ {x y : Expr}, Expr.eqUpToLevels x y = true →
    Expr.eqUpToLevels x.getAppFn y.getAppFn = true ∧ LvEqL x.getAppArgs y.getAppArgs
  | .app f a, y, h => by
    cases y with
    | app g b =>
      simp only [Expr.eqUpToLevels, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := Expr.eqUpToLevels_spine h.1
      refine ⟨h1, ?_⟩
      exact LvEqL.append h2 ⟨rfl, fun i a' b' ha hb => by
        cases i with
        | zero => simp at ha hb; subst ha hb; exact h.2
        | succ i => simp at ha⟩
    | _ => simp [Expr.eqUpToLevels] at h
  | .bvar _, y, h | .fvar .., y, h | .sort _, y, h | .const .., y, h | .lam .., y, h
  | .forallE .., y, h | .letE .., y, h | .lit _, y, h | .proj .., y, h => by
    cases y with
    | app g b => simp [Expr.eqUpToLevels] at h
    | _ => exact ⟨h, rfl, fun _ _ _ ha _ => by simp [Expr.getAppArgs] at ha⟩

/-- **A class matches a spelling**: its inductive at levels with the same
simplified forms, its (member-abstracted) parameters `eqUpToLevels` the
spelling's. -/
@[expose] def ClassMatch (x : Expr) (c : ClassInfo) : Prop :=
  ∃ us, x.getAppFn = .const c.key.ind us ∧ us.map Level.simplify = c.key.lvls.map Level.simplify ∧
    c.nPc ≤ x.getAppArgs.length ∧ LvEqL (x.getAppArgs.take c.nPc) c.dsA

/-- Two classes are the same up to spelling. -/
@[expose] def SameKey (c c' : ClassInfo) : Prop :=
  c.key.ind = c'.key.ind ∧ c.key.lvls.map Level.simplify = c'.key.lvls.map Level.simplify ∧
    LvEqL c.dsA c'.dsA

theorem ClassMatch.transport {x y : Expr} {c : ClassInfo} (hxy : Expr.eqUpToLevels x y = true)
    (h : ClassMatch x c) : ClassMatch y c := by
  obtain ⟨us, hfn, hlv, hle, hps⟩ := h
  obtain ⟨hf, ha⟩ := Expr.eqUpToLevels_spine hxy
  rw [hfn] at hf
  cases hy : y.getAppFn with
  | const n us' =>
    rw [hy] at hf
    simp only [Expr.eqUpToLevels, Bool.and_eq_true, beq_iff_eq] at hf
    obtain ⟨rfl, hl⟩ := hf
    exact ⟨us', hy, hl.symm.trans hlv, by rw [← ha.1]; exact hle, (ha.take c.nPc).symm.trans hps⟩
  | _ => rw [hy] at hf; simp [Expr.eqUpToLevels] at hf

theorem ClassMatch.sameKey {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {x : Expr}
    {c c' : ClassInfo} (hc : c ∈ cls) (hc' : c' ∈ cls) (hch : c.hole.isSome)
    (hch' : c'.hole.isSome) (h : ClassMatch x c) (h' : ClassMatch x c') : SameKey c c' := by
  obtain ⟨us, hfn, hlv, -, hps⟩ := h
  obtain ⟨us', hfn', hlv', -, hps'⟩ := h'
  rw [hfn] at hfn'
  simp only [Expr.const.injEq] at hfn'
  obtain ⟨hI, rfl⟩ := hfn'
  have hN := hwf.nPc c hc c' hc' hch hch' hI
  rw [hN] at hps
  exact ⟨hI, hlv.symm.trans hlv', hps.symm.trans hps'⟩

/-- **What the recogniser returns is a match.** -/
theorem classOcc_match {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {x h : Expr}
    {n : Nat} (hx : classOcc? cls x = some (h, n)) :
    ∃ c ∈ cls, c.hole = some h ∧ ClassMatch x c ∧ n = x.getAppArgs.length - c.nPc := by
  unfold classOcc? at hx
  split at hx
  · rename_i I us hI
    dsimp only at hx
    split at hx
    · exact nomatch hx
    · rename_i cs c0 rest hcs
      have hmem : ∀ c ∈ c0 :: rest, c ∈ cls ∧ c.hole.isSome ∧ c.key.ind = I ∧
          c.nPc ≤ x.getAppArgs.length := by
        intro c hc
        rw [← hcs] at hc
        simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
        exact ⟨hc.1, hc.2.1.1, hc.2.1.2, hc.2.2⟩
      obtain ⟨hc0, hc0h, hc0I, -⟩ := hmem c0 (List.mem_cons_self ..)
      have hpick : ∀ c, c ∈ c0 :: rest →
          (c.hole.map fun h' => (h', x.getAppArgs.length - c.nPc)) = some (h, n) →
          us.map Level.simplify = c.key.lvls.map Level.simplify →
          LvEqL (x.getAppArgs.take c0.nPc) c.dsA →
          ∃ c ∈ cls, c.hole = some h ∧ ClassMatch x c ∧ n = x.getAppArgs.length - c.nPc := by
        intro c hc hp hlv hps
        obtain ⟨hcc, hch, hcI, hcle⟩ := hmem c hc
        have hN : c0.nPc = c.nPc := hwf.nPc c0 hc0 c hcc hc0h hch (hc0I.trans hcI.symm)
        obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp hch
        rw [hh'] at hp
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp
        obtain ⟨rfl, rfl⟩ := hp
        exact ⟨c, hcc, hh', ⟨us, by rw [hI, hcI], hlv, hcle, by rw [← hN]; exact hps⟩, rfl⟩
      split at hx
      · rename_i c hfind
        have hc := List.mem_of_find?_eq_some hfind
        have hcond := List.find?_some hfind
        simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hcc, hch, -, -⟩ := hmem c hc
        refine hpick c hc hx (by rw [hcond.1]) ?_
        rw [hwf.dsE c hcc hch] at hcond
        exact lvEqL_of_map_erase hcond.2
      · split at hx
        · rename_i c hfind
          have hc := List.mem_of_find?_eq_some hfind
          have hcond := List.find?_some hfind
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hcond
          obtain ⟨hcc, hch, -, -⟩ := hmem c hc
          obtain ⟨hlv, hps⟩ := hcond
          refine hpick c hc hx hlv ?_
          rcases hps with hps | ⟨hl, hz⟩
          · rw [hwf.dsE c hcc hch] at hps
            exact lvEqL_of_map_erase hps
          · exact lvEqL_of_zip (by simpa using hl) hz
        · exact nomatch hx
  · exact nomatch hx

/-- **A match is recognised** (by some class). -/
theorem classOcc_some_of_match {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    {x : Expr} {c : ClassInfo} (hc : c ∈ cls) (hch : c.hole.isSome) (hm : ClassMatch x c) :
    ∃ h n, classOcc? cls x = some (h, n) := by
  obtain ⟨us, hfn, hlv, hle, hps⟩ := hm
  have hin : c ∈ cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
      decide (c'.nPc ≤ x.getAppArgs.length)) := by
    simp [List.mem_filter, hc, hch, hle]
  have hmem : ∀ c', c' ∈ cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
      decide (c'.nPc ≤ x.getAppArgs.length)) → c' ∈ cls ∧ c'.hole.isSome ∧ c'.nPc = c.nPc := by
    intro c' hc'
    simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
    exact ⟨hc'.1, hc'.2.1.1, hwf.nPc c' hc'.1 c hc hc'.2.1.1 hch hc'.2.1.2⟩
  unfold classOcc?
  rw [hfn]
  dsimp only
  revert hin hmem
  generalize cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
      decide (c'.nPc ≤ x.getAppArgs.length)) = cs
  intro hin hmem
  match cs, hin, hmem with
  | c0 :: rest, hin, hmem =>
    simp only
    have hN := (hmem c0 (List.mem_cons_self ..)).2.2
    have hpk : ∀ c', c' ∈ c0 :: rest →
        ∃ h n, (c'.hole.map fun h' => (h', x.getAppArgs.length - c'.nPc)) = some (h, n) := by
      intro c' hc'
      obtain ⟨h', hh'⟩ := Option.isSome_iff_exists.mp (hmem c' hc').2.1
      exact ⟨h', _, by rw [hh']; rfl⟩
    split
    · rename_i c1 hf1
      exact hpk c1 (List.mem_of_find?_eq_some hf1)
    · split
      · rename_i c1 hf1
        exact hpk c1 (List.mem_of_find?_eq_some hf1)
      · rename_i hnone
        exfalso
        have := List.find?_eq_none.mp hnone c hin
        rw [hN] at this
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, not_and, not_or] at this
        exact (this hlv).2 (by simpa using hps.1) (zip_of_lvEqL hps)


/-! ### The recogniser's occurrences -/

/-- **An occurrence is its class's key**, up to `SemEq`, applied to the
index arguments. -/
theorem classOcc_spec {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {x h : Expr}
    {n : Nat} (hx : classOcc? cls x = some (h, n)) :
    ∃ c ∈ cls, c.hole = some h ∧ ∃ us, x.getAppFn = .const c.key.ind us ∧
      c.nPc ≤ x.getAppArgs.length ∧ n = x.getAppArgs.length - c.nPc ∧
      Expr.SemEq (Expr.mkAppN (.const c.key.ind us) (x.getAppArgs.take c.nPc)) (classKeyA c) := by
  obtain ⟨c, hc, hch, ⟨us, hfn, hlv, hle, hps⟩, hn⟩ := classOcc_match hwf hx
  refine ⟨c, hc, hch, us, hfn, hle, hn, ?_⟩
  exact Expr.SemEq.mkAppN ⟨rfl, Level.evalEqList_of_simplify hlv⟩ hps.1
    (fun k a b ha hb => Expr.semEq_of_eqUpToLevels (hps.2 k a b ha hb))

/-- **The recogniser is spine-coherent**: an occurrence with index
arguments left is an application whose function part is the same
occurrence with one index fewer. -/
theorem classOcc_app {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {x h : Expr}
    {n : Nat} (hx : classOcc? cls x = some (h, n + 1)) :
    ∃ f a, x = .app f a ∧ classOcc? cls f = some (h, n) := by
  obtain ⟨c, hc, hch, us, hfn, hle, hn, -⟩ := classOcc_spec hwf hx
  cases x with
  | app f a =>
    refine ⟨f, a, rfl, ?_⟩
    have hargs : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := rfl
    have hfn' : f.getAppFn = .const c.key.ind us := hfn
    rw [hargs, List.length_append, List.length_singleton] at hn
    have hN : c.nPc ≤ f.getAppArgs.length := by omega
    have hchs : c.hole.isSome := by rw [hch]; rfl
    have hfilt : cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
          decide (c'.nPc ≤ (f.getAppArgs ++ [a]).length))
        = cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
          decide (c'.nPc ≤ f.getAppArgs.length)) := by
      apply List.filter_congr
      intro c' hc'
      by_cases hh : c'.hole.isSome
      · by_cases hI : c'.key.ind = c.key.ind
        · have := hwf.nPc c' hc' c hc hh hchs hI
          simp [hh, hI, this]
          omega
        · have hI' : (c'.key.ind == c.key.ind) = false := by simpa using hI
          simp [hI']
      · simp [hh]
    unfold classOcc? at hx ⊢
    rw [show (Expr.app f a).getAppFn = f.getAppFn from rfl, hfn'] at hx
    rw [hfn']
    dsimp only at hx ⊢
    rw [hargs, hfilt] at hx
    have hmem : ∀ c', c' ∈ cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
        decide (c'.nPc ≤ f.getAppArgs.length)) → c'.nPc = c.nPc := by
      intro c' hc'
      simp only [List.mem_filter, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc'
      exact hwf.nPc c' hc'.1 c hc hc'.2.1.1 hchs hc'.2.1.2
    revert hmem hx
    generalize cls.filter (fun c' => c'.hole.isSome && c'.key.ind == c.key.ind &&
        decide (c'.nPc ≤ f.getAppArgs.length)) = cs
    intro hx hmem
    match cs, hx, hmem with
    | [], hx, _ => exact nomatch hx
    | c0 :: rest, hx, hmem =>
      have h0 := hmem c0 (List.mem_cons_self ..)
      have htake : (f.getAppArgs ++ [a]).take c0.nPc = f.getAppArgs.take c0.nPc :=
        List.take_append_of_le_length (by omega)
      simp only [htake, List.length_append, List.length_singleton] at hx
      simp only
      have hpk : ∀ c', c' ∈ c0 :: rest → ∀ o : Option (Expr × Nat),
          (c'.hole.map fun h' => (h', f.getAppArgs.length + 1 - c'.nPc)) = some (h, n + 1) →
          (c'.hole.map fun h' => (h', f.getAppArgs.length - c'.nPc)) = some (h, n) := by
        intro c' hc' _ hp
        have := hmem c' hc'
        cases hh : c'.hole with
        | none => rw [hh] at hp; exact nomatch hp
        | some h' =>
          rw [hh] at hp
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hp ⊢
          exact ⟨hp.1, by omega⟩
      split at hx
      · rename_i c1 hf1
        try rw [hf1]
        exact hpk c1 (List.mem_of_find?_eq_some hf1) none hx
      · rename_i hf1
        try rw [hf1]
        split at hx
        · rename_i c1 hf2
          try rw [hf2]
          exact hpk c1 (List.mem_of_find?_eq_some hf2) none hx
        · exact nomatch hx
  | _ =>
    simp only [Expr.getAppArgs, List.length_nil] at hn hle
    omega

/-- A recognised occurrence with no index argument left is its
parameters' spine, its class's key up to `SemEq`. -/
theorem classOcc_head {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {x h : Expr}
    (hx : classOcc? cls x = some (h, 0)) :
    ∃ c ∈ cls, c.hole = some h ∧ Expr.SemEq x (classKeyA c) := by
  obtain ⟨c, hc, hch, us, hfn, hle, hn, hsem⟩ := classOcc_spec hwf hx
  refine ⟨c, hc, hch, ?_⟩
  rw [List.take_of_length_le (by omega), ← hfn, Expr.mkAppN_getAppFn_getAppArgs] at hsem
  exact hsem

end Occ

/-! ## 4. The abstracted term reads as the concrete one (T3, true values) -/

section True

open ConLeche (ClassInfo classOcc? classAbs)

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- **The true class valuation**: every container class's hole slot
holds the value of the class's member-abstracted key (read at the
frame `H`). -/
@[expose] def ClassesTrue (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (cls : List ClassInfo) (H : Nat) (τ : Nat → V) : Prop :=
  ∀ c ∈ cls, ∀ i ty, c.hole = some (.fvar i ty) → ∀ a,
    denoteMeta acval env φ H (classKeyA c) = some a → τ (H - 1 - i) = interp V τ a

/-- A hole read `d` locals above the frame, against a frame-scoped term
lifted: the agreement is the valuation's equation at the hole. -/
theorem hole_agree_lift
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {H : Nat} {Good : (Nat → V) → Prop} {i : Nat} (hi : i < H) (ty : Expr) {K x : Expr}
    (hK : Expr.WScoped H K) (hKb : K.looseBVarsBounded 0 = true) (hx : Expr.SemEq x K)
    (hden : (denoteMeta acval env φ H K).isSome)
    (hgood : ∀ τ, Good τ → ∀ a, denoteMeta acval env φ H K = some a → τ (H - 1 - i) = interp V τ a)
    {d : Nat} {as1 : List Expr} :
    OptAgree (ValAgree V Good d) (denoteMeta acval env φ (H + d) (.fvar i ty))
      (denoteMeta acval env φ (H + d) (x.instantiateList as1 0)) := by
  have hxb : x.looseBVarsBounded 0 = true := by rw [Expr.SemEq.looseBVarsBounded hx 0]; exact hKb
  rw [Expr.instantiateList_eq_self hxb, denoteMeta_semEq hx, denoteMeta_lift hacl hK (H + d)
    (by omega), denoteMeta_fvar]
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hden
  rw [ha]
  simp only [Option.map_some, OptAgree]
  intro vals τ hvl hτ
  rw [interp_bvar, show H + d - 1 - i = (H - 1 - i) + vals.length by omega, consList_apply_add,
    hgood τ hτ a ha, show H + d - H = vals.length by omega, interp_liftN, shiftE_consList]

/-- **T3 at true values** (the substitution law's ground case): at every
valuation carrying the true class values (`ClassesTrue`), the class
abstraction of a term reads as the term — opened at any `d` locals. -/
theorem classAbs_read
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hden : ∀ c ∈ cls, c.hole.isSome → (denoteMeta acval env φ H (classKeyA c)).isSome)
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V (ClassesTrue V acval env φ cls H) d)
      (denoteMeta acval env φ (H + d) ((classAbs cls e).instantiateList as2 0))
      (denoteMeta acval env φ (H + d) (e.instantiateList as1 0)) := by
  have hyp : AbsReadHyps V acval env φ H (ClassesTrue V acval env φ cls H) (classOcc? cls)
      (fun _ => false) := by
    refine ⟨fun x h n hx => classOcc_app hwf hx, fun x h n hx => ?_, fun x h hx _ d' as2' as1' _ _ => ?_⟩
    · obtain ⟨c, hc, hch, -⟩ := classOcc_spec hwf hx
      obtain ⟨i, ty, rfl, -⟩ := hwf.hole c hc h hch
      exact ⟨i, ty, rfl⟩
    · obtain ⟨c, hc, hch, hsem⟩ := classOcc_head hwf hx
      obtain ⟨i, ty, rfl, hi⟩ := hwf.hole c hc h hch
      have hchs : c.hole.isSome := by rw [hch]; rfl
      rw [occRestrict_false, classAbsSpec_none]
      exact hole_agree_lift hacl hi ty (hwf.keyScoped c hc hchs).1 (hwf.keyScoped c hc hchs).2
        hsem (hden c hc hchs) (fun τ hτ a ha => hτ c hc i ty hch a ha)
  have h := classAbsSpec_read hyp e h2 h1
  rwa [occRestrict_false, classAbsSpec_none, ← classAbs_eq_spec] at h

end True

/-! ## 5. The coarser tier: aliases -/

section Alias

open ConLeche (ClassInfo ClassAlias aliasOcc? classAbs classAbsGo)

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- An alias's key: its inductive at its levels, applied to its
(hole-form, annotation-erased) parameters. -/
@[expose] def aliasKey (a : ClassAlias) : Expr := Expr.mkAppN (.const a.ind a.lvls) a.ps

/-- **What the alias recogniser needs**: every alias's hole a variable
below the frame, its parameters as many as its parameter count, its key
frame-scoped with no loose bound variable. -/
structure AliasWF (al : List ClassAlias) (H : Nat) : Prop where
  hole : ∀ a ∈ al, ∃ i ty, a.hole = .fvar i ty ∧ i < H
  len : ∀ a ∈ al, a.ps.length = a.nPc
  keyScoped : ∀ a ∈ al, Expr.WScoped H (aliasKey a) ∧ (aliasKey a).looseBVarsBounded 0 = true

theorem aliasOcc_spec {al : List ClassAlias} {x h : Expr} {n : Nat}
    (hx : aliasOcc? al x = some (h, n)) :
    ∃ a ∈ al, a.hole = h ∧ ∃ us, x.getAppFn = .const a.ind us ∧ a.nPc ≤ x.getAppArgs.length ∧
      n = x.getAppArgs.length - a.nPc ∧ Level.isEquivList us a.lvls = some true ∧
      (x.getAppArgs.take a.nPc).map Expr.eraseFVarTys = a.ps := by
  unfold aliasOcc? at hx
  split at hx
  · rename_i I us hI
    dsimp only at hx
    obtain ⟨a, hfind, hpa⟩ := Option.map_eq_some_iff.mp hx
    have ha := List.mem_of_find?_eq_some hfind
    have hc := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hI', hle⟩, hlv⟩, hps⟩ := hc
    simp only [Prod.mk.injEq] at hpa
    exact ⟨a, ha, hpa.1, us, by rw [hI, hI'], hle, hpa.2.symm, hlv, hps⟩
  · exact nomatch hx

theorem aliasOcc_app {al : List ClassAlias} {x h : Expr} {n : Nat}
    (hx : aliasOcc? al x = some (h, n + 1)) :
    ∃ f a, x = .app f a ∧ aliasOcc? al f = some (h, n) := by
  obtain ⟨b, hb, hbh, us, hfn, hle, hn, -⟩ := aliasOcc_spec hx
  cases x with
  | app f a =>
    refine ⟨f, a, rfl, ?_⟩
    have hargs : (Expr.app f a).getAppArgs = f.getAppArgs ++ [a] := rfl
    unfold aliasOcc? at hx ⊢
    rw [show (Expr.app f a).getAppFn = f.getAppFn from rfl] at hx
    split at hx
    · rename_i I us' hI
      try rw [hI]
      dsimp only at hx ⊢
      rw [hargs] at hx
      obtain ⟨a0, hfind, hpa⟩ := Option.map_eq_some_iff.mp hx
      simp only [Prod.mk.injEq, List.length_append, List.length_singleton] at hpa
      have hc0 := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.length_append,
        List.length_singleton] at hc0
      have hN : a0.nPc ≤ f.getAppArgs.length := by omega
      -- the first alias for `x` is the first for its function part
      have hfind' : al.find? (fun b => b.ind == I && decide (b.nPc ≤ f.getAppArgs.length) &&
          Level.isEquivList us' b.lvls == some true &&
          (f.getAppArgs.take b.nPc).map Expr.eraseFVarTys == b.ps) = some a0 := by
        rw [List.find?_eq_some_iff_append] at hfind ⊢
        obtain ⟨-, pre, post, hsplit, hpre⟩ := hfind
        refine ⟨?_, pre, post, hsplit, fun b hbm => ?_⟩
        · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
          rw [List.take_append_of_le_length hN] at hc0
          exact ⟨⟨⟨hc0.1.1.1, hN⟩, hc0.1.2⟩, hc0.2⟩
        · have := hpre b hbm
          simp only [Bool.not_eq_true', Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq,
            decide_eq_false_iff_not, Nat.not_le, List.length_append,
            List.length_singleton] at this ⊢
          by_cases hbN : b.nPc ≤ f.getAppArgs.length
          · rw [List.take_append_of_le_length hbN] at this
            rcases this with ((h1 | h1) | h1) | h1
            · exact Or.inl (Or.inl (Or.inl h1))
            · omega
            · exact Or.inl (Or.inr h1)
            · exact Or.inr h1
          · exact Or.inl (Or.inl (Or.inr (by omega)))
      rw [hfind']
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
      exact ⟨hpa.1, by omega⟩
    · exact nomatch hx
  | _ =>
    simp only [Expr.getAppArgs, List.length_nil] at hn hle
    omega

/-- **The alias holes read their keys**: every alias's hole slot holds
the value of its (hole-form) key. -/
@[expose] def AliasTrue (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (al : List ClassAlias) (H : Nat) (τ : Nat → V) : Prop :=
  ∀ a ∈ al, ∀ i ty, a.hole = .fvar i ty → ∀ r,
    denoteMeta acval env φ H (aliasKey a) = some r → τ (H - 1 - i) = interp V τ r

/-- **The alias pass reads as its input** at every valuation whose
alias holes read their keys. -/
theorem aliasAbs_read
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {al : List ClassAlias} {H : Nat} (hwf : AliasWF al H)
    (hden : ∀ a ∈ al, (denoteMeta acval env φ H (aliasKey a)).isSome)
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V (AliasTrue V acval env φ al H) d)
      (denoteMeta acval env φ (H + d)
        ((classAbsGo (aliasOcc? al) none {} e).1.instantiateList as2 0))
      (denoteMeta acval env φ (H + d) (e.instantiateList as1 0)) := by
  have hyp : AbsReadHyps V acval env φ H (AliasTrue V acval env φ al H) (aliasOcc? al)
      (fun _ => false) := by
    refine ⟨fun x h n hx => aliasOcc_app hx, fun x h n hx => ?_,
      fun x h hx _ d' as2' as1' _ _ => ?_⟩
    · obtain ⟨a, ha, rfl, -⟩ := aliasOcc_spec hx
      obtain ⟨i, ty, hi, -⟩ := hwf.hole a ha
      exact ⟨i, ty, hi⟩
    · obtain ⟨a, ha, rfl, us, hfn, hle, hn, hlv, hps⟩ := aliasOcc_spec hx
      obtain ⟨i, ty, hi, hiH⟩ := hwf.hole a ha
      have hsem : Expr.SemEq x (aliasKey a) := by
        have hlen : x.getAppArgs.length = a.nPc := by omega
        have hx' : x = Expr.mkAppN (.const a.ind us) (x.getAppArgs.take a.nPc) := by
          rw [List.take_of_length_le (by omega), ← hfn, Expr.mkAppN_getAppFn_getAppArgs]
        rw [hx']
        unfold aliasKey
        have hlvl := Level.evalEqList_of_isEquivList hlv
        have hps' : (x.getAppArgs.take a.nPc).map Expr.eraseFVarTys
            = a.ps.map Expr.eraseFVarTys := by
          rw [hps]
          -- the alias's parameters are erased already
          rw [← hps, List.map_map]
          apply List.map_congr_left
          intro p _
          exact (Expr.eraseFVarTys_idem p).symm
        obtain ⟨hl, hpw⟩ := semEq_of_map_erase hps'
        exact Expr.SemEq.mkAppN ⟨rfl, hlvl⟩ hl hpw
      rw [hi, occRestrict_false, classAbsSpec_none]
      exact hole_agree_lift hacl hiH ty (hwf.keyScoped a ha).1 (hwf.keyScoped a ha).2 hsem
        (hden a ha) (fun τ hτ r hr => hτ a ha i ty hi r hr)
  have h := classAbsSpec_read hyp e h2 h1
  rw [occRestrict_false, classAbsSpec_none] at h
  rwa [(classAbsGo_spec _ e none {} (fun _ _ h => by simp at h)).1]

/-- **The alias pass against its restriction to the holes `F`** (the
coarser tier at stage values): provided every alias occurrence of a hole
outside `F` reads as its head abstracted by the restriction. -/
theorem aliasAbs_read_hole {al : List ClassAlias} {H : Nat} (hwf : AliasWF al H)
    {F : Expr → Bool} {Good : (Nat → V) → Prop}
    (hhead : ∀ x h, aliasOcc? al x = some (h, 0) → F h = false →
      ∀ d as2 as1, LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V Good d) (denoteMeta acval env φ (H + d) h)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (aliasOcc? al) F) none x).instantiateList as1 0)))
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V Good d)
      (denoteMeta acval env φ (H + d)
        ((classAbsGo (aliasOcc? al) none {} e).1.instantiateList as2 0))
      (denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict (aliasOcc? al) F) none e).instantiateList as1 0)) := by
  have hyp : AbsReadHyps V acval env φ H Good (aliasOcc? al) F := by
    refine ⟨fun x h n hx => aliasOcc_app hx, fun x h n hx => ?_, hhead⟩
    obtain ⟨a, ha, rfl, -⟩ := aliasOcc_spec hx
    obtain ⟨i, ty, hi, -⟩ := hwf.hole a ha
    exact ⟨i, ty, hi⟩
  rw [(classAbsGo_spec _ e none {} (fun _ _ h => by simp at h)).1]
  exact classAbsSpec_read hyp e h2 h1

end Alias

/-! ## 6. Hole form (P1): the abstraction against a partial one -/

section Hole

open ConLeche (ClassInfo classOcc? classAbs)

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- The class abstraction restricted to the holes `F` (a class fact's
free holes and own group): the other classes' occurrences stay
concrete. -/
@[expose] def classAbsF (cls : List ClassInfo) (F : Expr → Bool) (e : Expr) : Expr :=
  classAbsSpec (occRestrict (classOcc? cls) F) none e

/-- **P1 in hole form**: at every valuation `Good` admits, the class
abstraction reads as its restriction to the holes `F`, provided every
occurrence of a class outside `F` reads (at `Good`) as its
`F`-abstracted head.  At `F = ∅` this is `classAbs_read`; at a class
fact's `F` it is the reading of the abstracted crest at a STAGE value
(own group and free holes arbitrary, every other class read as its key
in hole form) — the head obligation is where the other classes'
coherence enters (DESIGN CLASSCHECK / P2B). -/
theorem classAbs_read_hole {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    {F : Expr → Bool} {Good : (Nat → V) → Prop}
    (hhead : ∀ x h, classOcc? cls x = some (h, 0) → F h = false →
      ∀ d as2 as1, LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V Good d) (denoteMeta acval env φ (H + d) h)
          (denoteMeta acval env φ (H + d) ((classAbsF cls F x).instantiateList as1 0)))
    (e : Expr) {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V Good d)
      (denoteMeta acval env φ (H + d) ((classAbs cls e).instantiateList as2 0))
      (denoteMeta acval env φ (H + d) ((classAbsF cls F e).instantiateList as1 0)) := by
  have hyp : AbsReadHyps V acval env φ H Good (classOcc? cls) F := by
    refine ⟨fun x h n hx => classOcc_app hwf hx, fun x h n hx => ?_, hhead⟩
    obtain ⟨c, hc, hch, -⟩ := classOcc_spec hwf hx
    obtain ⟨i, ty, rfl, -⟩ := hwf.hole c hc h hch
    exact ⟨i, ty, rfl⟩
  rw [classAbs_eq_spec]
  exact classAbsSpec_read hyp e h2 h1

end Hole


/-! ## 7. P1 at stage values: the abstraction against its restriction, discharged -/

section Stage

open ConLeche (ClassInfo classOcc? classAbs)

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

theorem optAgree_trans {Good : (Nat → V) → Prop} {d : Nat} {o1 o2 o3 : Option AnnotTerm}
    (h1 : OptAgree (ValAgree V Good d) o1 o2) (h2 : OptAgree (ValAgree V Good d) o2 o3) :
    OptAgree (ValAgree V Good d) o1 o3 := by
  cases o1 <;> cases o2 <;> cases o3 <;> simp_all [OptAgree]
  intro vals τ hvl hτ
  rw [h1 vals τ hvl hτ, h2 vals τ hvl hτ]

theorem Expr.instantiateList_mkAppN' (σ : List Expr) (k : Nat) :
    ∀ (as : List Expr) (f : Expr), (Expr.mkAppN f as).instantiateList σ k
      = Expr.mkAppN (f.instantiateList σ k) (as.map (·.instantiateList σ k))
  | [], _ => rfl
  | a :: as, f => by
    rw [Expr.mkAppN, Expr.instantiateList_mkAppN' σ k as]
    simp [Expr.instantiateList, Expr.mkAppN]

theorem Expr.getAppFn_mkAppN' : ∀ (as : List Expr) (f : Expr),
    (Expr.mkAppN f as).getAppFn = f.getAppFn
  | [], _ => rfl
  | a :: as, f => by rw [Expr.mkAppN, Expr.getAppFn_mkAppN' as]; rfl

theorem Expr.getAppArgs_mkAppN' : ∀ (as : List Expr) (f : Expr),
    (Expr.mkAppN f as).getAppArgs = f.getAppArgs ++ as
  | [], _ => by simp [Expr.mkAppN]
  | a :: as, f => by
    rw [Expr.mkAppN, Expr.getAppArgs_mkAppN' as]
    simp [Expr.getAppArgs]

/-- Agreement of application spines, argument by argument. -/
theorem optAgree_mkAppN {Good : (Nat → V) → Prop} {d D : Nat} :
    ∀ (as2 as1 : List Expr) {f2 f1 : Expr}, as2.length = as1.length →
      OptAgree (ValAgree V Good d) (denoteMeta acval env φ D f2) (denoteMeta acval env φ D f1) →
      (∀ (i : Nat) (a2 a1 : Expr), as2[i]? = some a2 → as1[i]? = some a1 →
        OptAgree (ValAgree V Good d) (denoteMeta acval env φ D a2)
          (denoteMeta acval env φ D a1)) →
      OptAgree (ValAgree V Good d) (denoteMeta acval env φ D (Expr.mkAppN f2 as2))
        (denoteMeta acval env φ D (Expr.mkAppN f1 as1))
  | [], [], _, _, _, hf, _ => hf
  | a2 :: as2, a1 :: as1, f2, f1, hl, hf, ha => by
    apply optAgree_mkAppN as2 as1 (by simpa using hl) _ (fun i x y hx hy => ha (i + 1) x y hx hy)
    rw [denoteMeta_app, denoteMeta_app]
    exact optAgree_app hf (ha 0 a2 a1 rfl rfl)
  | [], _ :: _, _, _, hl, _, _ => by simp at hl
  | _ :: _, [], _, _, hl, _, _ => by simp at hl

/-- Two `SemEq` terms opened at the same local indices stay `SemEq`. -/
theorem semEq_instantiateList_loc {H d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2)
    (h1 : LocList H d as1) : ∀ (p q : Expr) (k : Nat), Expr.SemEq p q →
      Expr.SemEq (p.instantiateList as2 k) (q.instantiateList as1 k) := by
  intro p
  induction p with
  | bvar j =>
    intro q k hpq
    cases q <;> simp only [Expr.SemEq] at hpq
    subst hpq
    by_cases hjk : j < k
    · simp only [Expr.instantiateList, if_pos hjk]
      exact Expr.SemEq.refl _
    · by_cases hj : j - k < d
      · obtain ⟨ty2, hty2⟩ := h2.2 (j - k) hj
        obtain ⟨ty1, hty1⟩ := h1.2 (j - k) hj
        obtain ⟨hl2, hg2⟩ := List.getElem?_eq_some_iff.mp hty2
        obtain ⟨hl1, hg1⟩ := List.getElem?_eq_some_iff.mp hty1
        simp only [Expr.instantiateList, if_neg hjk, dif_pos hl2, dif_pos hl1, hg2, hg1]
        exact rfl
      · simp only [Expr.instantiateList, if_neg hjk, h2.1, h1.1, dif_neg hj]
        exact Expr.SemEq.refl _
  | app f a ihf iha =>
    intro q k hpq
    cases q <;> simp only [Expr.SemEq] at hpq
    simp only [Expr.instantiateList]
    exact ⟨ihf _ k hpq.1, iha _ k hpq.2⟩
  | lam t b m iht ihb =>
    intro q k hpq
    cases q <;> simp only [Expr.SemEq] at hpq
    simp only [Expr.instantiateList]
    exact ⟨hpq.1, iht _ k hpq.2.1, ihb _ (k + 1) hpq.2.2⟩
  | forallE t b m iht ihb =>
    intro q k hpq
    cases q <;> simp only [Expr.SemEq] at hpq
    simp only [Expr.instantiateList]
    exact ⟨hpq.1, iht _ k hpq.2.1, ihb _ (k + 1) hpq.2.2⟩
  | letE t v b iht ihv ihb =>
    intro q k hpq
    cases q <;> simp only [Expr.SemEq] at hpq
    simp only [Expr.instantiateList]
    exact ⟨iht _ k hpq.1, ihv _ k hpq.2.1, ihb _ (k + 1) hpq.2.2⟩
  | proj s i x ih =>
    intro q k hpq
    cases q <;> simp only [Expr.SemEq] at hpq
    simp only [Expr.instantiateList]
    exact ⟨hpq.1, hpq.2.1, ih _ k hpq.2.2⟩
  | _ =>
    intro q k hpq
    cases q <;> simp only [Expr.SemEq] at hpq <;> simp only [Expr.instantiateList] <;>
      exact hpq

/-- An argument of a spine is smaller than the spine. -/
theorem sizeOf_lt_of_mem_getAppArgs : ∀ {q a : Expr}, a ∈ q.getAppArgs → sizeOf a < sizeOf q
  | .app f x, a, h => by
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · have := sizeOf_lt_of_mem_getAppArgs h
      simp; omega
    · simp; omega
  | .bvar _, _, h | .fvar .., _, h | .sort _, _, h | .const .., _, h | .lam .., _, h
  | .forallE .., _, h | .letE .., _, h | .lit _, _, h | .proj .., _, h => by
    simp [Expr.getAppArgs] at h

/-- The abstraction descends a spine whose prefixes it does not
recognise. -/
theorem classAbsSpec_spine (occ : Expr → Option (Expr × Nat)) :
    ∀ (as : List Expr) (f : Expr), (∀ j, 1 ≤ j → j ≤ as.length →
      occ (Expr.mkAppN f (as.take j)) = none) →
      classAbsSpec occ none (Expr.mkAppN f as)
        = Expr.mkAppN (classAbsSpec occ none f) (as.map (classAbsSpec occ none))
  | [], _, _ => rfl
  | a :: as, f, h => by
    have h1 := h 1 (Nat.le_refl _) (by simp)
    simp only [List.take_succ_cons, List.take_zero, Expr.mkAppN] at h1
    rw [Expr.mkAppN, classAbsSpec_spine occ as (.app f a) (fun j hj1 hj => by
      have := h (j + 1) (by omega) (by simp; omega)
      simpa [Expr.mkAppN] using this)]
    simp only [classAbsSpec, h1, List.map_cons, Expr.mkAppN]

/-- A class's key in hole form. -/
@[expose] def holeKey (cls : List ClassInfo) (c : ClassInfo) : Expr :=
  Expr.mkAppN (.const c.key.ind c.key.lvls) (c.holeForm cls)

/-- The kept holes are closed under same keys. -/
@[expose] def FClosed (cls : List ClassInfo) (F : Expr → Bool) : Prop :=
  ∀ c ∈ cls, ∀ c' ∈ cls, ∀ h h', c.hole = some h → c'.hole = some h' → SameKey c c' → F h = F h'

/-- **The stage coherence**: a class outside `F` reads as its key in hole
form; classes in `F` the same up to spelling carry one value. -/
@[expose] def StageCoh (V : Type w) [SetTheory V] (acval : Name → (Name → Nat) → AnnotTerm)
    (env : Env) (φ : Name → Nat) (cls : List ClassInfo) (F : Expr → Bool) (H : Nat)
    (τ : Nat → V) : Prop :=
  (∀ c ∈ cls, ∀ i ty, c.hole = some (.fvar i ty) → F (.fvar i ty) = false → ∀ a,
      denoteMeta acval env φ H (holeKey cls c) = some a → τ (H - 1 - i) = interp V τ a) ∧
  (∀ c ∈ cls, ∀ c' ∈ cls, ∀ i ty i' ty', c.hole = some (.fvar i ty) →
      c'.hole = some (.fvar i' ty') → F (.fvar i ty) = true → SameKey c c' →
      τ (H - 1 - i) = τ (H - 1 - i'))

/-- The hole-form keys are frame-scoped, closed, and read. -/
@[expose] def HoleKeysOk (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (cls : List ClassInfo) (H : Nat) : Prop :=
  ∀ c ∈ cls, c.hole.isSome → Expr.WScoped H (holeKey cls c) ∧
    (holeKey cls c).looseBVarsBounded 0 = true ∧
    (denoteMeta acval env φ H (holeKey cls c)).isSome

/-- Related spellings are recognised alike, with the same index count and
classes the same up to spelling. -/
theorem classOcc_both {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {p q h : Expr}
    {n : Nat} (hpq : Expr.eqUpToLevels p q = true) (hp : classOcc? cls p = some (h, n)) :
    ∃ h', classOcc? cls q = some (h', n) ∧ ∃ c ∈ cls, ∃ c' ∈ cls, c.hole = some h ∧
      c'.hole = some h' ∧ SameKey c c' ∧ ClassMatch p c ∧ ClassMatch q c ∧
      n = q.getAppArgs.length - c.nPc := by
  obtain ⟨c, hc, hch, hmp, hn⟩ := classOcc_match hwf hp
  have hchs : c.hole.isSome := by rw [hch]; rfl
  have hmq := hmp.transport hpq
  obtain ⟨h', n', hq⟩ := classOcc_some_of_match hwf hc hchs hmq
  obtain ⟨c', hc', hch', hmq', hn'⟩ := classOcc_match hwf hq
  have hch's : c'.hole.isSome := by rw [hch']; rfl
  have hsk := hmq.sameKey hwf hc hc' hchs hch's hmq'
  have hN := hwf.nPc c hc c' hc' hchs hch's hsk.1
  have hlen := (Expr.eqUpToLevels_spine hpq).2.1
  refine ⟨h', ?_, c, hc, c', hc', hch, hch', hsk, hmp, hmq, by rw [hn, hlen]⟩
  rw [hq, hn', hn, ← hN, hlen]

theorem classOcc_none_of {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {p q : Expr}
    (hpq : Expr.eqUpToLevels p q = true) (hp : classOcc? cls p = none) : classOcc? cls q = none := by
  cases hq : classOcc? cls q with
  | none => rfl
  | some x =>
    obtain ⟨h', n⟩ := x
    obtain ⟨h, hp', -⟩ := classOcc_both hwf (Expr.eqUpToLevels_symm hpq) hq
    rw [hp] at hp'
    exact nomatch hp'

/-- The value a hole variable reads at, `d` locals above the frame. -/
theorem interp_hole_read {H d i : Nat} (hi : i < H) (vals : List V) (τ : Nat → V)
    (hvl : vals.length = d) : interp V (consList vals τ) (.bvar (H + d - 1 - i)) = τ (H - 1 - i) := by
  rw [interp_bvar, show H + d - 1 - i = (H - 1 - i) + vals.length by omega, consList_apply_add]

/-- A spelling shorter than its class's parameter list is no occurrence. -/
theorem classOcc_short {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H) {x : Expr}
    {c : ClassInfo} (hc : c ∈ cls) (hch : c.hole.isSome) {us : List Level}
    (hfn : x.getAppFn = .const c.key.ind us) (hlt : x.getAppArgs.length < c.nPc) :
    classOcc? cls x = none := by
  cases hx : classOcc? cls x with
  | none => rfl
  | some r =>
    obtain ⟨h, n⟩ := r
    obtain ⟨c0, hc0, hch0, ⟨us0, hfn0, -, hle0, -⟩, -⟩ := classOcc_match hwf hx
    have hch0s : c0.hole.isSome := by rw [hch0]; rfl
    rw [hfn] at hfn0
    simp only [Expr.const.injEq] at hfn0
    have := hwf.nPc c0 hc0 c hc hch0s hch hfn0.1.symm
    omega

/-- Non-application terms are left alone by the abstraction. -/
theorem classAbsSpec_none_atom (occ : Expr → Option (Expr × Nat)) {e : Expr}
    (he : ∀ f a, e ≠ .app f a) (hl : ∀ t b m, e ≠ .lam t b m) (hf : ∀ t b m, e ≠ .forallE t b m)
    (hlt : ∀ t v b, e ≠ .letE t v b) (hp : ∀ s i x, e ≠ .proj s i x) :
    classAbsSpec occ none e = e := by
  cases e with
  | app f a => exact absurd rfl (he f a)
  | lam t b m => exact absurd rfl (hl t b m)
  | forallE t b m => exact absurd rfl (hf t b m)
  | letE t v b => exact absurd rfl (hlt t v b)
  | proj s i x => exact absurd rfl (hp s i x)
  | _ => simp [classAbsSpec]

set_option maxHeartbeats 8000000 in
/-- **P1 at stage values, discharged**: for related spellings `p`, `q`,
the class abstraction of `p` and the `F`-restricted abstraction of `q`
read alike at every valuation with the stage coherence — every class
outside `F` read as its key in hole form, the classes in `F` free (one
value per class up to spelling).  With the `some` mode's version. -/
theorem classAbs_read_stage_both
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hhk : HoleKeysOk acval env φ cls H) {F : Expr → Bool} (hF : FClosed cls F) :
    ∀ (N : Nat) (q p : Expr), sizeOf q < N → Expr.eqUpToLevels p q = true →
      (∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V (StageCoh V acval env φ cls F H) d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (classOcc? cls) none p).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) none q).instantiateList as1 0))) ∧
      (∀ h n h', classOcc? cls p = some (h, n) → classOcc? cls q = some (h', n) →
        ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
        OptAgree (ValAgree V (StageCoh V acval env φ cls F H) d)
          (denoteMeta acval env φ (H + d)
            ((classAbsSpec (classOcc? cls) (some (h, n)) p).instantiateList as2 0))
          (denoteMeta acval env φ (H + d)
            ((if F h' then classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) q
              else classAbsSpec (occRestrict (classOcc? cls) F) none q).instantiateList
                as1 0))) := by
  intro N
  induction N with
  | zero => intro q p hN; omega
  | succ N ihN =>
  intro q p hN hpq
  -- the `some` mode
  have hsome : ∀ h n h', classOcc? cls p = some (h, n) → classOcc? cls q = some (h', n) →
      ∀ (d : Nat) (as2 as1 : List Expr), LocList H d as2 → LocList H d as1 →
      OptAgree (ValAgree V (StageCoh V acval env φ cls F H) d)
        (denoteMeta acval env φ (H + d)
          ((classAbsSpec (classOcc? cls) (some (h, n)) p).instantiateList as2 0))
        (denoteMeta acval env φ (H + d)
          ((if F h' then classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) q
            else classAbsSpec (occRestrict (classOcc? cls) F) none q).instantiateList as1 0)) := by
    intro h n h' hp hq d as2 as1 h2 h1
    obtain ⟨h'', hq', c, hc, c', hc', hch, hch', hsk, hmp, hmq, hnq⟩ := classOcc_both hwf hpq hp
    rw [hq] at hq'
    obtain rfl : h' = h'' := by simp at hq'; exact hq'
    have hchs : c.hole.isSome := by rw [hch]; rfl
    obtain ⟨i, ty, rfl, hi⟩ := hwf.hole c hc h hch
    obtain ⟨i', ty', rfl, hi'⟩ := hwf.hole c' hc' h' hch'
    have hFF : F (.fvar i ty) = F (.fvar i' ty') := hF c hc c' hc' _ _ hch hch' hsk
    rcases n with _ | n
    · -- a head part
      simp only [classAbsSpec]
      cases hFq : F (.fvar i' ty') with
      | true =>
        simp only [if_true, Expr.instantiateList, denoteMeta_fvar, OptAgree]
        intro vals τ hvl hτ
        rw [interp_hole_read hi vals τ hvl, interp_hole_read hi' vals τ hvl]
        exact hτ.2 c hc c' hc' i ty i' ty' hch hch' (hFF.trans hFq) hsk
      | false =>
        simp only [Bool.false_eq_true, if_false]
        have hFp : F (.fvar i ty) = false := hFF.trans hFq
        obtain ⟨us', hfn, hlv, hle, hps⟩ := hmq
        have hlen : q.getAppArgs.length = c.nPc := by omega
        have hqe : q = Expr.mkAppN (.const c.key.ind us') q.getAppArgs := by
          rw [← hfn]; exact (Expr.mkAppN_getAppFn_getAppArgs q).symm
        -- the restriction descends `q`'s spine
        have hdesc : classAbsSpec (occRestrict (classOcc? cls) F) none q
            = Expr.mkAppN (.const c.key.ind us')
                (q.getAppArgs.map (classAbsSpec (occRestrict (classOcc? cls) F) none)) := by
          conv => lhs; rw [hqe]
          rw [classAbsSpec_spine _ q.getAppArgs (.const c.key.ind us') (fun j hj1 hj => ?_)]
          · simp [classAbsSpec]
          · rcases Nat.lt_or_ge j q.getAppArgs.length with hjl | hjl
            · apply occRestrict_eq_none
              apply classOcc_short hwf hc hchs (us := us')
              · rw [Expr.getAppFn_mkAppN']; rfl
              · rw [Expr.getAppArgs_mkAppN']
                simp only [Expr.getAppArgs, List.nil_append, List.length_take]
                omega
            · have hj' : j = q.getAppArgs.length := by omega
              rw [hj', List.take_length, ← hqe]
              exact occRestrict_eq_none_of hq hFq
        rw [hdesc]
        have hK := hhk c hc hchs
        rw [show (Expr.fvar i ty).instantiateList as2 0 = .fvar i ty from by
          simp [Expr.instantiateList]]
        refine optAgree_trans (hole_agree_lift (V := V) (Good := StageCoh V acval env φ cls F H)
          (d := d) (as1 := as2) hacl hi ty hK.1 hK.2.1
          (Expr.SemEq.refl _) hK.2.2
          (fun τ (hτ : StageCoh V acval env φ cls F H τ) a ha => hτ.1 c hc i ty hch hFp a ha)) ?_
        unfold holeKey
        rw [Expr.instantiateList_mkAppN', Expr.instantiateList_mkAppN']
        have hdl : c.dsA.length = c.nPc := hwf.len c hc hchs
        have hqa : q.getAppArgs.take c.nPc = q.getAppArgs := List.take_of_length_le (by omega)
        rw [hqa] at hps
        apply optAgree_mkAppN
        · simp only [List.length_map, ConLeche.ClassInfo.holeForm]
          omega
        · simp only [Expr.instantiateList]
          rw [denoteMeta_semEq (show Expr.SemEq (.const c.key.ind c.key.lvls)
            (.const c.key.ind us') from ⟨rfl, (Level.evalEqList_of_simplify hlv.symm).1,
              (Level.evalEqList_of_simplify hlv.symm).2⟩)]
          exact optAgree_refl' (V := V) _
        · intro k a2 a1 ha2 ha1
          simp only [List.getElem?_map, ConLeche.ClassInfo.holeForm, Option.map_eq_some_iff] at ha2 ha1
          obtain ⟨b2, hb2, rfl⟩ := ha2
          obtain ⟨x2', hx2', rfl⟩ := ha1
          obtain ⟨x2, hx2, rfl⟩ := hx2'
          obtain ⟨y2, hy2, rfl⟩ := hb2
          have hR : Expr.eqUpToLevels y2 x2 = true := Expr.eqUpToLevels_symm (hps.2 k x2 y2 hx2 hy2)
          have hlt : sizeOf x2 < sizeOf q :=
            sizeOf_lt_of_mem_getAppArgs (List.mem_of_getElem? hx2)
          rw [classAbs_eq_spec]
          exact (ihN x2 y2 (by omega) hR).1 d as2 as1 h2 h1
    · -- one more index argument
      obtain ⟨pf, pa, rfl, hpf⟩ := classOcc_app hwf hp
      obtain ⟨qf, qa, rfl, hqf⟩ := classOcc_app hwf hq
      simp only [Expr.eqUpToLevels, Bool.and_eq_true] at hpq
      have hsf := (ihN qf pf (by simp at hN; omega) hpq.1).2 _ n _ hpf hqf d as2 as1
        h2 h1
      have hsa := (ihN qa pa (by simp at hN; omega) hpq.2).1 d as2 as1 h2 h1
      cases hFq : F (.fvar i' ty') with
      | true =>
        simp only [hFq, if_true] at hsf ⊢
        simp only [classAbsSpec, Expr.instantiateList, denoteMeta_app]
        exact optAgree_app hsf hsa
      | false =>
        simp only [hFq, Bool.false_eq_true, if_false] at hsf ⊢
        have hR : occRestrict (classOcc? cls) F (.app qf qa) = none := occRestrict_eq_none_of hq hFq
        simp only [classAbsSpec, hR, Expr.instantiateList, denoteMeta_app]
        exact optAgree_app hsf hsa
  refine ⟨fun d as2 as1 h2 h1 => ?_, hsome⟩
  cases q with
  | app qf qa =>
    cases p with
    | app pf pa =>
      have hpq0 := hpq
      simp only [Expr.eqUpToLevels, Bool.and_eq_true] at hpq
      cases hp : classOcc? cls (.app pf pa) with
      | none =>
        have hq : classOcc? cls (.app qf qa) = none := classOcc_none_of hwf hpq0 hp
        have hR : occRestrict (classOcc? cls) F (.app qf qa) = none := occRestrict_eq_none hq
        simp only [classAbsSpec, hp, hR, Expr.instantiateList, denoteMeta_app]
        exact optAgree_app ((ihN qf pf (by simp at hN; omega) hpq.1).1 d as2 as1 h2 h1)
          ((ihN qa pa (by simp at hN; omega) hpq.2).1 d as2 as1 h2 h1)
      | some r =>
        obtain ⟨h, n⟩ := r
        obtain ⟨h', hq, -⟩ := classOcc_both hwf hpq0 hp
        have hs := hsome h n h' hp hq d as2 as1 h2 h1
        have hL : classAbsSpec (classOcc? cls) none (.app pf pa)
            = classAbsSpec (classOcc? cls) (some (h, n)) (.app pf pa) := by
          rcases n with _ | n <;> simp [classAbsSpec, hp]
        rw [hL]
        cases hF' : F h' with
        | true =>
          have hR : occRestrict (classOcc? cls) F (.app qf qa) = some (h', n) :=
            occRestrict_eq_some_of hq hF'
          have hL' : classAbsSpec (occRestrict (classOcc? cls) F) none (.app qf qa)
              = classAbsSpec (occRestrict (classOcc? cls) F) (some (h', n)) (.app qf qa) := by
            rcases n with _ | n <;> simp [classAbsSpec, hR]
          rw [hL']
          simpa [hF'] using hs
        | false => simpa [hF'] using hs
    | _ => simp [Expr.eqUpToLevels] at hpq
  | lam qt qb qm | forallE qt qb qm =>
    cases p <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at hpq
    rename_i pt pb pm
    obtain ⟨⟨rfl, hT⟩, hB⟩ := hpq
    have hTa := (ihN qt pt (by simp at hN; omega) hT).1 d as2 as1 h2 h1
    simp only [classAbsSpec, Expr.instantiateList]
    first
    | rw [denoteMeta_lam, denoteMeta_lam]
    | rw [denoteMeta_forallE, denoteMeta_forallE]
    revert hTa
    cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (classOcc? cls) none pt).instantiateList as2 0)
      <;> cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i A2 A1
    intro hA
    rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons]
    have hB' := (ihN qb pb (by simp at hN; omega) hB).1 (d + 1) _ _
      (h2.cons ((classAbsSpec (classOcc? cls) none pt).instantiateList as2 0))
      (h1.cons ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0))
    rw [show H + (d + 1) = H + d + 1 by omega] at hB'
    revert hB'
    cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec (classOcc? cls) none pb).instantiateList
          (Expr.fvar (H + d) ((classAbsSpec (classOcc? cls) none pt).instantiateList as2 0)
            :: as2) 0)
      <;> cases denoteMeta acval env φ (H + d + 1)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none qb).instantiateList
          (Expr.fvar (H + d)
            ((classAbsSpec (occRestrict (classOcc? cls) F) none qt).instantiateList as1 0)
            :: as1) 0)
      <;> simp [OptAgree]
    rename_i b2 b1
    intro hb vals τ hvl hτ
    have hbx : ∀ x : V, interp V (cons x (consList vals τ)) b2
        = interp V (cons x (consList vals τ)) b1 := by
      intro x
      have := hb (vals ++ [x]) τ (by simp [hvl]) hτ
      simpa [consList_append] using this
    first
    | (simp only [interp_lam, hA vals τ hvl hτ]; exact lamR_congr fun x _ => hbx x)
    | (simp only [interp_pi, hA vals τ hvl hτ]; exact piR_congr fun x _ => hbx x)
  | proj sn si qx =>
    cases p <;> simp only [Expr.eqUpToLevels, Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at hpq
    rename_i ps pi px
    obtain ⟨⟨hs, hi⟩, hX⟩ := hpq
    subst hs hi
    have hXa := (ihN qx px (by simp at hN; omega) hX).1 d as2 as1 h2 h1
    simp only [classAbsSpec, Expr.instantiateList, denoteMeta_proj]
    revert hXa
    cases denoteMeta acval env φ (H + d) ((classAbsSpec (classOcc? cls) none px).instantiateList as2 0)
      <;> cases denoteMeta acval env φ (H + d)
        ((classAbsSpec (occRestrict (classOcc? cls) F) none qx).instantiateList as1 0)
      <;> simp [OptAgree]
    rename_i e2 e1
    intro he
    cases env.findProj? ps pi with
    | some entry =>
      intro vals τ hvl hτ
      exact interp_projAV_congr _ (he vals τ hvl hτ)
    | none =>
      rcases pi with _ | _ | pi
      · intro vals τ hvl hτ
        simp [he vals τ hvl hτ]
      · intro vals τ hvl hτ
        simp [he vals τ hvl hτ]
      · simp [AnnotTerm.projPair?]
  | letE qt qv qb =>
    cases p <;> simp only [Expr.eqUpToLevels, reduceCtorEq] at hpq
    simp only [classAbsSpec, Expr.instantiateList]
    rw [denoteMeta, denoteMeta]
    trivial
  | _ =>
    have hsem := Expr.semEq_of_eqUpToLevels hpq
    rw [classAbsSpec_none_atom _ (by intro f a h; subst h; simp [Expr.eqUpToLevels] at hpq)
        (by intro t b m h; subst h; simp [Expr.eqUpToLevels] at hpq)
        (by intro t b m h; subst h; simp [Expr.eqUpToLevels] at hpq)
        (by intro t v b h; subst h; simp [Expr.eqUpToLevels] at hpq)
        (by intro s i x h; subst h; simp [Expr.eqUpToLevels] at hpq),
      classAbsSpec_none_atom _ (by intro f a h; cases h) (by intro t b m h; cases h)
        (by intro t b m h; cases h) (by intro t v b h; cases h) (by intro s i x h; cases h),
      denoteMeta_semEq (semEq_instantiateList_loc h2 h1 _ _ 0 hsem)]
    exact optAgree_refl' (V := V) _

/-- **P1 at stage values**: the class abstraction reads as its
restriction to the holes `F` at every valuation with the stage
coherence. -/
theorem classAbs_read_stage
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hhk : HoleKeysOk acval env φ cls H) {F : Expr → Bool} (hF : FClosed cls F) (e : Expr)
    {d : Nat} {as2 as1 : List Expr} (h2 : LocList H d as2) (h1 : LocList H d as1) :
    OptAgree (ValAgree V (StageCoh V acval env φ cls F H) d)
      (denoteMeta acval env φ (H + d) ((classAbs cls e).instantiateList as2 0))
      (denoteMeta acval env φ (H + d) ((classAbsF cls F e).instantiateList as1 0)) := by
  rw [classAbs_eq_spec]
  exact (classAbs_read_stage_both hacl hwf hhk hF (sizeOf e + 1) e e (by omega)
    (Expr.eqUpToLevels_refl e)).1 d as2 as1 h2 h1

end Stage

/-! ## 8. The true valuation: exists, is stage-coherent, identifies same classes (iii) -/

section TrueVal

open ConLeche (ClassInfo ClassAlias classOcc? classAbs)

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}
  {acval : Name → (Name → Nat) → AnnotTerm}

/-- At the true valuation a class's key in hole form reads as its
member-abstracted key. -/
theorem holeKey_read_true
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hden : ∀ c ∈ cls, c.hole.isSome → (denoteMeta acval env φ H (classKeyA c)).isSome)
    (c : ClassInfo) :
    OptAgree (ValAgree V (ClassesTrue V acval env φ cls H) 0)
      (denoteMeta acval env φ H (holeKey cls c)) (denoteMeta acval env φ H (classKeyA c)) := by
  unfold holeKey classKeyA ConLeche.ClassInfo.holeForm
  apply optAgree_mkAppN _ _ (by simp) (optAgree_refl' (V := V) _)
  intro i a2 a1 ha2 ha1
  simp only [List.getElem?_map, Option.map_eq_some_iff] at ha2
  obtain ⟨b, hb, rfl⟩ := ha2
  have hab : a1 = b := by rw [ha1] at hb; exact Option.some.inj hb
  subst hab
  have h := classAbs_read (V := V) hacl hwf hden a1 (LocList.nil H) (LocList.nil H)
  simpa [Expr.instantiateList_nil] using h

/-- **The true valuation is stage-coherent with no kept hole.** -/
theorem stageCoh_of_classesTrue
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hden : ∀ c ∈ cls, c.hole.isSome → (denoteMeta acval env φ H (classKeyA c)).isSome)
    {τ : Nat → V} (hτ : ClassesTrue V acval env φ cls H τ) :
    StageCoh V acval env φ cls (fun _ => false) H τ := by
  refine ⟨fun c hc i ty hch _ a ha => ?_, fun _ _ _ _ _ _ _ _ _ _ hF _ => absurd hF (by simp)⟩
  have hchs : c.hole.isSome := by rw [hch]; rfl
  obtain ⟨a1, ha1⟩ := Option.isSome_iff_exists.mp (hden c hc hchs)
  have h := holeKey_read_true (V := V) hacl hwf hden c
  rw [ha, ha1] at h
  have := h [] τ rfl hτ
  simp only [consList_nil] at this
  rw [this]
  exact hτ c hc i ty hch a1 ha1

/-- **(iii) Same classes carry one true value.** -/
theorem classesTrue_sameKey {cls : List ClassInfo} {H : Nat} {τ : Nat → V}
    (hτ : ClassesTrue V acval env φ cls H τ) {c c' : ClassInfo} (hc : c ∈ cls) (hc' : c' ∈ cls)
    {i i' : Nat} {ty ty' : Expr} (hch : c.hole = some (.fvar i ty))
    (hch' : c'.hole = some (.fvar i' ty')) (hsk : SameKey c c')
    (hden : (denoteMeta acval env φ H (classKeyA c)).isSome) :
    τ (H - 1 - i) = τ (H - 1 - i') := by
  have hsem : Expr.SemEq (classKeyA c) (classKeyA c') := by
    unfold classKeyA
    obtain ⟨hI, hlv, hps⟩ := hsk
    rw [hI]
    exact Expr.SemEq.mkAppN ⟨rfl, Level.evalEqList_of_simplify hlv⟩ hps.1
      (fun k a b ha hb => Expr.semEq_of_eqUpToLevels (hps.2 k a b ha hb))
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hden
  have ha' : denoteMeta acval env φ H (classKeyA c') = some a := by
    rw [← denoteMeta_semEq hsem]; exact ha
  rw [hτ c hc i ty hch a ha, hτ c' hc' i' ty' hch' a ha']

/-- **The alias holes read their keys at the true valuation**, given
that every alias's own parameters read as its class's hole-form key (the
per-component defeq of the coarser tier, `ClassAliasOk`, read at the
valuation). -/
theorem aliasTrue_of_classesTrue
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {H : Nat} (hwf : ClassOccWF cls H)
    (hden : ∀ c ∈ cls, c.hole.isSome → (denoteMeta acval env φ H (classKeyA c)).isSome)
    (hhk : HoleKeysOk acval env φ cls H) {al : List ClassAlias} {τ : Nat → V}
    (hτ : ClassesTrue V acval env φ cls H τ)
    (hal : ∀ a ∈ al, ∃ ci ∈ cls, ∃ ps : List Expr, ci.hole = some a.hole ∧
      a.ps = ps.map Expr.eraseFVarTys ∧
      ∀ r r', denoteMeta acval env φ H (Expr.mkAppN (.const a.ind a.lvls) ps) = some r →
        denoteMeta acval env φ H (holeKey cls ci) = some r' → interp V τ r = interp V τ r') :
    AliasTrue V acval env φ al H τ := by
  intro a ha i ty hhole r hr
  obtain ⟨ci, hci, ps, hch, hps, hdef⟩ := hal a ha
  have hchs : ci.hole.isSome := by rw [hch]; rfl
  have hsem : Expr.SemEq (Expr.mkAppN (.const a.ind a.lvls) ps) (aliasKey a) := by
    unfold aliasKey
    obtain ⟨hl, hpw⟩ := semEq_of_map_erase (as := ps) (bs := a.ps) (by
      rw [hps, List.map_map]
      apply List.map_congr_left
      intro p _
      exact (Expr.eraseFVarTys_idem p).symm)
    exact Expr.SemEq.mkAppN (Expr.SemEq.refl _) hl hpw
  have hr0 : denoteMeta acval env φ H (Expr.mkAppN (.const a.ind a.lvls) ps) = some r := by
    rw [denoteMeta_semEq hsem]; exact hr
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (hhk ci hci hchs).2.2
  rw [hdef r r' hr0 hr']
  have hs := stageCoh_of_classesTrue (V := V) hacl hwf hden hτ
  rw [hhole] at hch
  exact hs.1 ci hci i ty hch rfl r' hr'

/-- **The true valuation exists** over any valuation `ρ` of the frame
below the class holes (`K`: the parameters and the members' holes): the
class holes' values are their keys' readings at `ρ`. -/
theorem exists_classesTrue
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {cls : List ClassInfo} {K H : Nat} (hKH : K ≤ H)
    (hhole : ∀ c ∈ cls, ∀ h, c.hole = some h → ∃ i ty, h = .fvar i ty ∧ K ≤ i ∧ i < H)
    (hkey : ∀ c ∈ cls, c.hole.isSome → Expr.WScoped K (classKeyA c))
    (huniq : ∀ c ∈ cls, ∀ c' ∈ cls, ∀ i ty ty', c.hole = some (.fvar i ty) →
      c'.hole = some (.fvar i ty') → classKeyA c = classKeyA c')
    (ρ : Nat → V) :
    ∃ vals : List V, vals.length = H - K ∧
      ClassesTrue V acval env φ cls H (consList vals ρ) := by
  let holeIdx : ClassInfo → Nat → Bool := fun c i => match c.hole with
    | some (.fvar i' _) => i' == i
    | _ => false
  let val : Nat → V := fun j => match cls.find? (holeIdx · (K + j)) with
    | some c => ((denoteMeta acval env φ K (classKeyA c)).map (interp V ρ)).getD pt
    | none => pt
  refine ⟨(List.range (H - K)).map val, by simp, fun c hc i ty hch a ha => ?_⟩
  obtain ⟨i0, ty0, hi0, hKi, hiH⟩ := hhole c hc _ hch
  simp only [Expr.fvar.injEq] at hi0
  obtain ⟨rfl, rfl⟩ := hi0
  have hlen : ((List.range (H - K)).map val).length = H - K := by simp
  rw [consList_getD_of_lt _ _ _ (by rw [hlen]; omega), hlen,
    show H - K - 1 - (H - 1 - i) = i - K by omega, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range (by omega), Option.map_some, Option.getD_some]
  have hchs : c.hole.isSome := by rw [hch]; rfl
  -- the class the construction found at this index has the same key
  have hfind : ∃ c', cls.find? (holeIdx · (K + (i - K))) = some c' ∧ classKeyA c' = classKeyA c := by
    have hsome : (cls.find? (holeIdx · (K + (i - K)))).isSome := by
      rw [List.find?_isSome]
      exact ⟨c, hc, by simp [holeIdx, hch]; omega⟩
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hsome
    refine ⟨c', hc', ?_⟩
    have hmem := List.mem_of_find?_eq_some hc'
    have hp := List.find?_some hc'
    simp only [holeIdx] at hp
    split at hp
    · rename_i i' ty' hh'
      simp only [beq_iff_eq] at hp
      exact huniq c' hmem c hc i' ty' ty hh' (by rw [hch]; congr 2; omega)
    · exact nomatch hp
  obtain ⟨c', hc', hkey'⟩ := hfind
  simp only [val, hc', hkey']
  rw [denoteMeta_lift hacl (hkey c hc hchs) H hKH] at ha
  obtain ⟨aK, haK, rfl⟩ := Option.map_eq_some_iff.mp ha
  rw [haK, Option.map_some, Option.getD_some]
  have key : ∀ (xs : List V) (a : AnnotTerm),
      interp V (consList xs ρ) (a.liftN xs.length 0) = interp V ρ a := fun xs a => by
    rw [interp_liftN, shiftE_consList]
  have := key ((List.range (H - K)).map val) aK
  rw [hlen] at this
  exact this.symm

end TrueVal

end ConLeche.Model
