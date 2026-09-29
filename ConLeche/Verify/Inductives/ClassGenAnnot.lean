module

public import ConLeche.Verify.Subst
import ConLeche.Verify.Abstract
public import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Verify.Cached.NestPosC

public section

/-!
# Annotating a generated telescope

Check 6 of the class check (`Kernel/Inductives/ClassCheck.lean`)
ANNOTATES the generated recursor type before comparing it
(`classRecTyOk`: `ops.annotate … gty`), and the model reads the
annotated term.  The generated type is a `closeTelescope` over the
shared prefix, the class's index binders and its major, of a PLAIN body
(a variable applied to variables).  What the reading needs of the
annotation pass, as pure syntax:

* **the shared prefix stays shared** (`SameDoms`): two telescopes with
  the same first `n` domains keep them equal through `abstract1`,
  `instantiate1` and `annotate` — the annotation of a domain depends
  only on the domains before it, never on the body (the binder DATUM
  does, which is not a domain);
* **a plain body is left alone** (`annotateCore_plain`);
* **the annotated telescope is the telescope of the annotated domains**
  up to erasure (`annotateCore_closeTelescope`), each annotated domain
  the annotation of (an erasure of) the raw one;
* **a motive's type keeps its shape** (`EndsInSort`): `∀ …, Sort u`
  survives annotation, erasure and the de Bruijn operations.
-/

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-! ## Erasure and the de Bruijn operations -/

/-- Closing a bvar-bounded term then re-opening it gives it back up to
erasure. -/
theorem Expr.erasedEq_abstract1_instantiate1 {d : Nat} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      Expr.ErasedEq ((e.abstract1 d k).instantiate1 (.fvar d ty) k) e := by
  intro e
  induction e with
  | bvar i =>
    intro k hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.abstract1, Expr.instantiate1]
    rw [if_neg (by omega), if_neg (by omega)]
    exact Expr.ErasedEq.rfl _
  | fvar idx ty' _ =>
    intro k _
    simp only [Expr.abstract1]
    split
    · rename_i h
      simp only [Expr.instantiate1, if_true]
      exact h.symm
    · exact Expr.ErasedEq.rfl _
  | sort u => intro k _; exact Expr.ErasedEq.rfl _
  | const n us => intro k _; exact Expr.ErasedEq.rfl _
  | lit l => intro k _; exact Expr.ErasedEq.rfl _
  | app f a ihf iha =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨ihf k hb.1, iha k hb.2⟩
  | lam t b mm iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨rfl, iht k hb.1, ihb (k + 1) hb.2⟩
  | forallE t b mm iht ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨rfl, iht k hb.1, ihb (k + 1) hb.2⟩
  | letE t v b iht ihv ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    exact ⟨iht k hb.1.1, ihv k hb.1.2, ihb (k + 1) hb.2⟩
  | proj s i e ih =>
    intro k hb
    simp only [Expr.looseBVarsBounded] at hb
    exact ⟨rfl, rfl, ih k hb⟩

/-- Erasure equality survives abstraction. -/
theorem Expr.ErasedEq.abstract1 {d : Nat} :
    ∀ {e e' : Expr} (k : Nat), Expr.ErasedEq e e' →
      Expr.ErasedEq (e.abstract1 d k) (e'.abstract1 d k) := by
  intro e
  induction e with
  | bvar i =>
    intro e' k he
    match e', he with
    | .bvar j, he => exact he
  | fvar idx ty =>
    intro e' k he
    match e', he with
    | .fvar j ty', he =>
      obtain rfl : idx = j := he
      by_cases hd : idx = d <;> simp [Expr.abstract1, hd, Expr.ErasedEq]
  | sort u =>
    intro e' k he
    match e', he with
    | .sort u', he => exact he
  | const n us =>
    intro e' k he
    match e', he with
    | .const n' us', he => exact he
  | app f a ihf iha =>
    intro e' k he
    match e', he with
    | .app g b, he => exact ⟨ihf k he.1, iha k he.2⟩
  | lam ty body m ihty ihbody =>
    intro e' k he
    match e', he with
    | .lam ty' body' m', he => exact ⟨he.1, ihty k he.2.1, ihbody (k + 1) he.2.2⟩
  | forallE ty body m ihty ihbody =>
    intro e' k he
    match e', he with
    | .forallE ty' body' m', he => exact ⟨he.1, ihty k he.2.1, ihbody (k + 1) he.2.2⟩
  | letE ty vl body ihty ihv ihbody =>
    intro e' k he
    match e', he with
    | .letE ty' vl' body', he =>
      exact ⟨ihty k he.1, ihv k he.2.1, ihbody (k + 1) he.2.2⟩
  | lit l =>
    intro e' k he
    match e', he with
    | .lit l', he => exact he
  | proj sn i pe ih =>
    intro e' k he
    match e', he with
    | .proj sn' i' pe', he => exact ⟨he.1, he.2.1, ih k he.2.2⟩

/-! ## The same first domains -/

/-- The first `n` binders of two `∀`-telescopes have the same domains
(the binder data may differ). -/
@[expose] def SameDoms : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | n + 1, .forallE A b _, .forallE A' b' _ => A = A' ∧ SameDoms n b b'
  | _ + 1, _, _ => False

theorem SameDoms.abstract1 {d : Nat} :
    ∀ (n : Nat) {e₁ e₂ : Expr} (k : Nat), SameDoms n e₁ e₂ →
      SameDoms n (e₁.abstract1 d k) (e₂.abstract1 d k)
  | 0, _, _, _, _ => trivial
  | n + 1, .forallE A b m, .forallE A' b' m', k, h => by
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, SameDoms.abstract1 n (k + 1) h⟩

theorem SameDoms.instantiate1 {v : Expr} :
    ∀ (n : Nat) {e₁ e₂ : Expr} (k : Nat), SameDoms n e₁ e₂ →
      SameDoms n (e₁.instantiate1 v k) (e₂.instantiate1 v k)
  | 0, _, _, _, _ => trivial
  | n + 1, .forallE A b m, .forallE A' b' m', k, h => by
    obtain ⟨rfl, h⟩ := h
    exact ⟨rfl, SameDoms.instantiate1 n (k + 1) h⟩

/-- Two telescopes over the same prefix have the same first domains. -/
theorem SameDoms.closeTelescope_append :
    ∀ (P : List (Expr × BinderMeta)) (X₁ X₂ : List (Expr × BinderMeta)) (i : Nat)
      (B₁ B₂ : Expr),
      SameDoms P.length (closeTelescope (P ++ X₁) i B₁) (closeTelescope (P ++ X₂) i B₂)
  | [], _, _, _, _, _ => trivial
  | (dom, bm) :: P, X₁, X₂, i, B₁, B₂ => by
    simp only [List.cons_append, closeTelescope, List.length_cons]
    exact ⟨rfl, SameDoms.abstract1 _ 0 (SameDoms.closeTelescope_append P X₁ X₂ (i + 1) B₁ B₂)⟩

/-- **Annotation keeps the same first domains**: a domain's annotation
reads only the domains before it. -/
theorem SameDoms.annotate {env : Env} :
    ∀ (n : Nat) {F d : Nat} {e₁ e₂ e₁' e₂' : Expr}, SameDoms n e₁ e₂ →
      annotateCore mode env F d e₁ = .ok e₁' → annotateCore mode env F d e₂ = .ok e₂' →
      SameDoms n e₁' e₂'
  | 0, _, _, _, _, _, _, _, _, _ => trivial
  | n + 1, F, d, .forallE A b m, .forallE A' b' m', e₁', e₂', h, h₁, h₂ => by
    obtain ⟨rfl, h⟩ := h
    cases F with
    | zero => simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h₁
    | succ F =>
      obtain ⟨ty₁, bd₁, pw₁, hty₁, hbd₁, rfl⟩ := annotateCore_forallE_inv h₁
      obtain ⟨ty₂, bd₂, pw₂, hty₂, hbd₂, rfl⟩ := annotateCore_forallE_inv h₂
      obtain rfl : ty₁ = ty₂ := Except.ok.inj (hty₁.symm.trans hty₂)
      exact ⟨rfl, SameDoms.abstract1 n 0
        (SameDoms.annotate n (SameDoms.instantiate1 n 0 h) hbd₁ hbd₂)⟩

/-- **Opening two telescopes with the same first domains** gives the
same variables. -/
theorem SameDoms.open :
    ∀ (n : Nat) {d : Nat} {e₁ e₂ : Expr} {fvs₁ fvs₂ : List Expr} {o₁ o₂ : Expr},
      SameDoms n e₁ e₂ → openPisAtFvars n e₁ d = some (fvs₁, o₁) →
      openPisAtFvars n e₂ d = some (fvs₂, o₂) → fvs₁ = fvs₂
  | 0, _, _, _, _, _, _, _, _, h₁, h₂ => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    rw [← h₁.1, ← h₂.1]
  | n + 1, d, .forallE A b m, .forallE A' b' m', fvs₁, fvs₂, o₁, o₂, h, h₁, h₂ => by
    obtain ⟨rfl, h⟩ := h
    simp only [openPisAtFvars] at h₁ h₂
    split at h₁
    · next fvs₁' o₁' hop₁ =>
      split at h₂
      · next fvs₂' o₂' hop₂ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h₁ h₂
        rw [← h₁.1, ← h₂.1, SameDoms.open n (SameDoms.instantiate1 n 0 h) hop₁ hop₂]
      · exact nomatch h₂
    · exact nomatch h₁

/-- A telescope with `n` leading binders opens. -/
theorem SameDoms.open_isSome :
    ∀ (n : Nat) {d : Nat} {e : Expr}, SameDoms n e e →
      ∃ fvs o, openPisAtFvars n e d = some (fvs, o)
  | 0, _, e, _ => ⟨[], e, rfl⟩
  | n + 1, d, .forallE A b m, h => by
    obtain ⟨fvs, o, hop⟩ := SameDoms.open_isSome n (d := d + 1)
      (SameDoms.instantiate1 (v := .fvar d A) n 0 h.2)
    exact ⟨.fvar d A :: fvs, o, by simp [openPisAtFvars, hop]⟩

/-! ## Plain bodies -/

/-- A PLAIN term: variables, sorts and constants, applied — nothing the
annotation pass rewrites. -/
@[expose] def Expr.Plain : Expr → Prop
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ => True
  | .app f a => Expr.Plain f ∧ Expr.Plain a
  | _ => False

theorem Expr.Plain.mkAppN : ∀ {f : Expr} {as : List Expr}, Expr.Plain f →
    (∀ a ∈ as, Expr.Plain a) → Expr.Plain (Expr.mkAppN f as)
  | _, [], hf, _ => hf
  | f, a :: as, hf, ha => by
    simp only [Expr.mkAppN]
    exact Expr.Plain.mkAppN ⟨hf, ha a List.mem_cons_self⟩
      (fun x hx => ha x (List.mem_cons_of_mem _ hx))

theorem Expr.Plain.of_erasedEq : ∀ {e e' : Expr}, Expr.ErasedEq e e' → Expr.Plain e' →
    Expr.Plain e
  | .bvar _, .bvar _, _, _ => trivial
  | .fvar _ _, .fvar _ _, _, _ => trivial
  | .sort _, .sort _, _, _ => trivial
  | .const _ _, .const _ _, _, _ => trivial
  | .app _ _, .app _ _, he, hp => ⟨Expr.Plain.of_erasedEq he.1 hp.1,
      Expr.Plain.of_erasedEq he.2 hp.2⟩
  | .lam .., .lam .., _, hp => hp.elim
  | .forallE .., .forallE .., _, hp => hp.elim
  | .letE .., .letE .., _, hp => hp.elim
  | .lit _, .lit _, _, hp => hp.elim
  | .proj .., .proj .., _, hp => hp.elim

/-- **Annotation leaves a plain term alone.** -/
theorem annotateCore_plain {env : Env} :
    ∀ (F : Nat) {d : Nat} {e e' : Expr}, Expr.Plain e →
      annotateCore mode env F d e = .ok e' → e' = e
  | 0, _, _, _, _, h => by simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h
  | F + 1, d, e, e', hp, h => by
    match e, hp with
    | .bvar i, _ =>
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      exact h.symm
    | .fvar idx ty, _ =>
      rw [annotateCore_succ] at h
      simp only [annotateBody] at h
      split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h
        exact h.symm
      · simp [throw, throwThe, MonadExceptOf.throw] at h
    | .sort u, _ =>
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      exact h.symm
    | .const n us, _ =>
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      exact h.symm
    | .app f a, hp =>
      obtain ⟨f', a', hf, ha, rfl⟩ := annotateCore_app_inv h
      rw [annotateCore_plain F hp.1 hf, annotateCore_plain F hp.2 ha]

/-! ## The annotated telescope -/

/-- **Annotating (an erasure of) a closed telescope over a plain body**:
the result is, up to erasure, the telescope of the annotated domains
over (an erasure of) the body — each annotated domain the annotation of
an erasure of the raw one, at its own depth. -/
theorem annotateCore_closeTelescope {env : Env} :
    ∀ (nds : List (Expr × BinderMeta)) {F d : Nat} {B E e' : Expr},
      (∀ p ∈ nds, p.1.looseBVarsBounded 0 = true) → B.looseBVarsBounded 0 = true →
      Expr.Plain B → Expr.ErasedEq E (closeTelescope nds d B) →
      annotateCore mode env F d E = .ok e' →
      ∃ (nds' : List (Expr × BinderMeta)) (B' : Expr),
        nds'.length = nds.length ∧ Expr.ErasedEq e' (closeTelescope nds' d B') ∧
        Expr.ErasedEq B' B ∧
        ∀ (k : Nat) (nd' : Expr × BinderMeta), nds'[k]? = some nd' →
          ∃ (X : Expr) (F' : Nat) (nd : Expr × BinderMeta), nds[k]? = some nd ∧
            Expr.ErasedEq X nd.1 ∧ annotateCore mode env F' (d + k) X = .ok nd'.1
  | [], F, d, B, E, e', _, _, hp, he, h => by
    simp only [closeTelescope] at he
    have hpE : Expr.Plain E := Expr.Plain.of_erasedEq he hp
    rw [annotateCore_plain F hpE h]
    exact ⟨[], E, rfl, by simpa [closeTelescope] using Expr.ErasedEq.rfl E, he,
      fun k nd' hk => nomatch hk⟩
  | (dom, bm) :: nds, F, d, B, E, e', hcl, hb, hp, he, h => by
    simp only [closeTelescope] at he
    match E, he with
    | .forallE A b m, he =>
      obtain ⟨rfl, hA, hbE⟩ := he
      cases F with
      | zero => simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h
      | succ F =>
        obtain ⟨A', b', pw, hA', hb', rfl⟩ := annotateCore_forallE_inv h
        have hcl' : ∀ p ∈ nds, p.1.looseBVarsBounded 0 = true :=
          fun p hp => hcl p (List.mem_cons_of_mem _ hp)
        have hC := closeTelescope_bounded nds (d + 1) B hcl' hb
        have hE : Expr.ErasedEq (b.instantiate1 (.fvar d A')) (closeTelescope nds (d + 1) B) :=
          Expr.ErasedEq.trans (Expr.ErasedEq.instantiate1 hbE (v' := .fvar d A') rfl)
            (Expr.erasedEq_abstract1_instantiate1 _ 0 hC)
        obtain ⟨nds', B', hl, he', hB', hdoms⟩ :=
          annotateCore_closeTelescope nds hcl' hb hp hE hb'
        refine ⟨(A', ⟨pw⟩) :: nds', B', by simp [hl], ?_, hB', ?_⟩
        · simp only [closeTelescope]
          exact ⟨rfl, Expr.ErasedEq.rfl _, Expr.ErasedEq.abstract1 0 he'⟩
        · intro k nd' hk
          cases k with
          | zero =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
            subst hk
            exact ⟨A, F, (dom, m), rfl, hA, by simpa using hA'⟩
          | succ k =>
            simp only [List.getElem?_cons_succ] at hk
            obtain ⟨X, F', nd, hnd, hX, hann⟩ := hdoms k nd' hk
            exact ⟨X, F', nd, by simpa using hnd, hX,
              by rw [show d + (k + 1) = d + 1 + k by omega]; exact hann⟩

/-! ## A motive's type: `∀ …, Sort u` -/

/-- `m` leading `∀`-binders, then `Sort u`. -/
@[expose] def EndsInSort : Nat → Level → Expr → Prop
  | 0, u, e => e = .sort u
  | m + 1, u, .forallE _ b _ => EndsInSort m u b
  | _ + 1, _, _ => False

theorem EndsInSort.of_erasedEq {u : Level} :
    ∀ (m : Nat) {e e' : Expr}, Expr.ErasedEq e e' → EndsInSort m u e' → EndsInSort m u e
  | 0, e, e', he, h => by
    simp only [EndsInSort] at h ⊢
    subst h
    match e, he with
    | .sort v, he => rw [show v = u from he]
  | m + 1, e, e', he, h => by
    match e', h with
    | .forallE A' b' mb', h =>
      match e, he with
      | .forallE A b mb, he => exact EndsInSort.of_erasedEq m he.2.2 h
      | .bvar _, he | .fvar _ _, he | .sort _, he | .const _ _, he | .app _ _, he
      | .lam _ _ _, he | .letE _ _ _, he | .lit _, he | .proj _ _ _, he => exact he.elim
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h | .lam _ _ _, h
    | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => exact h.elim

theorem EndsInSort.instantiate1 {u : Level} {v : Expr} :
    ∀ (m : Nat) {e : Expr} (k : Nat), EndsInSort m u e → EndsInSort m u (e.instantiate1 v k)
  | 0, e, k, h => by
    simp only [EndsInSort] at h ⊢
    subst h; rfl
  | m + 1, .forallE A b mb, k, h => EndsInSort.instantiate1 m (k + 1) h

theorem EndsInSort.abstract1 {u : Level} {d : Nat} :
    ∀ (m : Nat) {e : Expr} (k : Nat), EndsInSort m u e → EndsInSort m u (e.abstract1 d k)
  | 0, e, k, h => by
    simp only [EndsInSort] at h ⊢
    subst h; rfl
  | m + 1, .forallE A b mb, k, h => EndsInSort.abstract1 m (k + 1) h

theorem EndsInSort.annotate {env : Env} {u : Level} :
    ∀ (m : Nat) {F d : Nat} {e e' : Expr}, EndsInSort m u e →
      annotateCore mode env F d e = .ok e' → EndsInSort m u e'
  | 0, F, d, e, e', h, ha => by
    simp only [EndsInSort] at h ⊢
    subst h
    exact annotateCore_plain F trivial ha
  | m + 1, F, d, e, e', h, ha => by
    match e, h with
    | .forallE A b mb, h =>
      cases F with
      | zero => simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at ha
      | succ F =>
        obtain ⟨A', b', pw, -, hb', rfl⟩ := annotateCore_forallE_inv ha
        exact EndsInSort.abstract1 m 0 (EndsInSort.annotate m (EndsInSort.instantiate1 m 0 h) hb')
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h | .lam _ _ _, h
    | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => exact h.elim

theorem EndsInSort.stripPis {u : Level} :
    ∀ (m : Nat) {e : Expr}, EndsInSort m u e → ∃ bs, e.stripPis m = some (bs, .sort u)
  | 0, e, h => by
    simp only [EndsInSort] at h
    subst h
    exact ⟨[], rfl⟩
  | m + 1, .forallE A b mb, h => by
    obtain ⟨bs, hbs⟩ := EndsInSort.stripPis m h
    exact ⟨(A, mb) :: bs, by simp [Expr.stripPis, hbs]⟩

end ConLeche
