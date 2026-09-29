module

public import ConLeche.Model.StreamConsts
public import ConLeche.Model.Annot.BitRename

public section

/-!
# What re-annotation keeps (lane GENREC-H)

The generated recursor type and rules are ANNOTATIONS of terms built
from already-annotated pieces (`Kernel/Inductives/GenRec.lean`).  The
annotation pass (`annotateBody`) touches a let-free term in exactly one
way: at a binder whose datum is NOT written (`pwWritten`, i.e. the datum
is `.never` — the placeholder and "never zero" are the same value) it
RECOMPUTES the datum in the context it runs in.  Everything else — the
tree, the leaves, every written datum, every `.proj` node's structure
name (the pass checks it is the subject type's head and keeps it) — is
kept.  `annotateCore_pwKept` proves that, as the relation `Expr.PwKept`.

Consequently (`annotateCore_erasedEq_of_neverFree`,
`denoteMeta_annotate_of_neverFree`): on a let-free piece with no
`.never` binder datum, re-annotation is the identity up to erasure and
reads the same.  What is NOT covered — and is the whole of the
re-annotation gap — is the recomputation at a `.never` binder INSIDE a
piece (a Type-codomain binder of a field domain, of a class parameter,
of the index telescope): showing the recomputed datum is again `.never`
is a stability statement for inferred sorts under the generator's
substitution of the class parameters for the canonical ones, which the
checker's metatheory does not have.
-/

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-! ## The relation -/

/-- **`e'` is `e` with some UNWRITTEN binder data rewritten**: the same
tree up to `fvar` type annotations (as `Expr.ErasedEq`), every written
datum of `e` kept (`pwWritten`), a `.never` datum arbitrary.  No `let`
on the left (the annotation pass ζ-reduces). -/
@[expose] def Expr.PwKept : Expr → Expr → Prop
  | .bvar i, .bvar j => i = j
  | .fvar i _, .fvar j _ => i = j
  | .sort u, .sort v => u = v
  | .const n us, .const n' us' => n = n' ∧ us = us'
  | .lit l, .lit l' => l = l'
  | .app f a, .app f' a' => Expr.PwKept f f' ∧ Expr.PwKept a a'
  | .lam t b m, .lam t' b' m' =>
    (pwWritten m.pw = true → m' = m) ∧ Expr.PwKept t t' ∧ Expr.PwKept b b'
  | .forallE t b m, .forallE t' b' m' =>
    (pwWritten m.pw = true → m' = m) ∧ Expr.PwKept t t' ∧ Expr.PwKept b b'
  | .proj s i e, .proj s' i' e' => s = s' ∧ i = i' ∧ Expr.PwKept e e'
  | _, _ => False

/-- No `let`, hereditarily (not through `fvar` types: the reading never
looks there). -/
@[expose] def Expr.NoLet : Expr → Prop
  | .app f a => Expr.NoLet f ∧ Expr.NoLet a
  | .lam t b _ | .forallE t b _ => Expr.NoLet t ∧ Expr.NoLet b
  | .proj _ _ e => Expr.NoLet e
  | .letE .. => False
  | _ => True

/-- Every binder datum is written, hereditarily (not through `fvar`
types). -/
@[expose] def Expr.NeverFree : Expr → Prop
  | .app f a => Expr.NeverFree f ∧ Expr.NeverFree a
  | .lam t b m | .forallE t b m =>
    pwWritten m.pw = true ∧ Expr.NeverFree t ∧ Expr.NeverFree b
  | .proj _ _ e => Expr.NeverFree e
  | .letE t v b => Expr.NeverFree t ∧ Expr.NeverFree v ∧ Expr.NeverFree b
  | _ => True

/-! ## De Bruijn bookkeeping -/

theorem Expr.NoLet.instantiate1 {v : Expr} (hv : Expr.NoLet v) :
    ∀ {e : Expr} (k : Nat), Expr.NoLet e → Expr.NoLet (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | app f a ihf iha => intro k h; exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b m iht ihb => intro k h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE t b m iht ihb => intro k h; exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | proj s i e ih => intro k h; exact ih k h
  | letE => intro k h; exact h.elim
  | fvar => intro _ _; trivial
  | sort => intro _ _; trivial
  | const => intro _ _; trivial
  | lit => intro _ _; trivial

theorem Expr.NeverFree.instantiate1 {v : Expr} (hv : Expr.NeverFree v) :
    ∀ {e : Expr} (k : Nat), Expr.NeverFree e → Expr.NeverFree (e.instantiate1 v k) := by
  intro e
  induction e with
  | bvar i =>
    intro k _
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | app f a ihf iha => intro k h; exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b m iht ihb => intro k h; exact ⟨h.1, iht k h.2.1, ihb (k + 1) h.2.2⟩
  | forallE t b m iht ihb => intro k h; exact ⟨h.1, iht k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s i e ih => intro k h; exact ih k h
  | letE t w b iht ihw ihb => intro k h; exact ⟨iht k h.1, ihw k h.2.1, ihb (k + 1) h.2.2⟩
  | fvar => intro _ _; trivial
  | sort => intro _ _; trivial
  | const => intro _ _; trivial
  | lit => intro _ _; trivial

/-- `PwKept` survives abstraction (both sides at the same variable). -/
theorem Expr.PwKept.abstract1 {d : Nat} :
    ∀ {e e' : Expr} (k : Nat), Expr.PwKept e e' →
      Expr.PwKept (e.abstract1 d k) (e'.abstract1 d k) := by
  intro e
  induction e with
  | bvar i =>
    intro e' k h
    match e', h with
    | .bvar j, h => exact h
  | fvar idx ty =>
    intro e' k h
    match e', h with
    | .fvar j ty', h =>
      obtain rfl : idx = j := h
      by_cases hd : idx = d <;> simp [Expr.abstract1, hd, Expr.PwKept]
  | sort u =>
    intro e' k h
    match e', h with
    | .sort u', h => exact h
  | const n us =>
    intro e' k h
    match e', h with
    | .const n' us', h => exact h
  | lit l =>
    intro e' k h
    match e', h with
    | .lit l', h => exact h
  | app f a ihf iha =>
    intro e' k h
    match e', h with
    | .app g b, h => exact ⟨ihf k h.1, iha k h.2⟩
  | lam t b m iht ihb =>
    intro e' k h
    match e', h with
    | .lam t' b' m', h => exact ⟨h.1, iht k h.2.1, ihb (k + 1) h.2.2⟩
  | forallE t b m iht ihb =>
    intro e' k h
    match e', h with
    | .forallE t' b' m', h => exact ⟨h.1, iht k h.2.1, ihb (k + 1) h.2.2⟩
  | letE t v b =>
    intro e' k h
    match e', h with
    | .letE .., h => exact h.elim
  | proj s i e ih =>
    intro e' k h
    match e', h with
    | .proj s' i' e'', h => exact ⟨h.1, h.2.1, ih k h.2.2⟩

/-- **A kept term with no unwritten datum is erasure-equal to its
source.** -/
theorem Expr.PwKept.erasedEq :
    ∀ {e e' : Expr}, Expr.PwKept e e' → Expr.NeverFree e → Expr.ErasedEq e e' := by
  intro e
  induction e with
  | bvar i =>
    intro e' h _
    match e', h with
    | .bvar j, h => exact h
  | fvar idx ty =>
    intro e' h _
    match e', h with
    | .fvar j ty', h => exact h
  | sort u =>
    intro e' h _
    match e', h with
    | .sort u', h => exact h
  | const n us =>
    intro e' h _
    match e', h with
    | .const n' us', h => exact h
  | lit l =>
    intro e' h _
    match e', h with
    | .lit l', h => exact h
  | app f a ihf iha =>
    intro e' h hn
    match e', h with
    | .app g b, h => exact ⟨ihf h.1 hn.1, iha h.2 hn.2⟩
  | lam t b m iht ihb =>
    intro e' h hn
    match e', h with
    | .lam t' b' m', h => exact ⟨(h.1 hn.1).symm, iht h.2.1 hn.2.1, ihb h.2.2 hn.2.2⟩
  | forallE t b m iht ihb =>
    intro e' h hn
    match e', h with
    | .forallE t' b' m', h => exact ⟨(h.1 hn.1).symm, iht h.2.1 hn.2.1, ihb h.2.2 hn.2.2⟩
  | letE t v b =>
    intro e' h _
    match e', h with
    | .letE .., h => exact h.elim
  | proj s i e ih =>
    intro e' h hn
    match e', h with
    | .proj s' i' e'', h => exact ⟨h.1, h.2.1, ih h.2.2 hn⟩

/-! ## The binder clauses keep a written datum -/

/-- `annotateCore_forallE_inv`, with the datum: a WRITTEN datum is kept. -/
theorem annotateCore_forallE_pw {env : Env} {fuel d : Nat}
    {ty body e' : Expr} {m : BinderMeta}
    (h : annotateCore mode env (fuel + 1) d (.forallE ty body m) = .ok e') :
    ∃ ty' body' pw, annotateCore mode env fuel d ty = .ok ty' ∧
      annotateCore mode env fuel (d + 1)
        (body.instantiate1 (.fvar d ty')) = .ok body' ∧
      e' = .forallE ty' (body'.abstract1 d) ⟨pw⟩ ∧ (pwWritten m.pw = true → pw = m.pw) := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def] at h
  cases hty : annotateCore mode env fuel d ty with
  | error e => rw [hty] at h; exact nomatch h
  | ok ty' =>
  rw [hty] at h; dsimp only at h
  cases hbody : annotateCore mode env fuel (d + 1)
      (body.instantiate1 (.fvar d ty')) with
  | error e => rw [hbody] at h; exact nomatch h
  | ok body' =>
  rw [hbody] at h; dsimp only at h
  revert h
  split
  · rename_i hw
    cases hpw : annotPwPi (pureFns mode env fuel) env (d + 1) body' with
    | error e => intro h; exact nomatch h
    | ok pw =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨ty', body', pw, rfl, hbody, h.symm, fun hw' => ?_⟩
      rw [hw'] at hw; exact absurd hw (by decide)
  · intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨ty', body', m.pw, rfl, hbody, h.symm, fun _ => rfl⟩

/-- `annotateCore_lam_inv`, with the datum: a WRITTEN datum is kept. -/
theorem annotateCore_lam_pw {env : Env} {fuel d : Nat}
    {ty body e' : Expr} {m : BinderMeta}
    (h : annotateCore mode env (fuel + 1) d (.lam ty body m) = .ok e') :
    ∃ ty' body' pw, annotateCore mode env fuel d ty = .ok ty' ∧
      annotateCore mode env fuel (d + 1)
        (body.instantiate1 (.fvar d ty')) = .ok body' ∧
      e' = .lam ty' (body'.abstract1 d) ⟨pw⟩ ∧ (pwWritten m.pw = true → pw = m.pw) := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def] at h
  cases hty : annotateCore mode env fuel d ty with
  | error e => rw [hty] at h; exact nomatch h
  | ok ty' =>
  rw [hty] at h; dsimp only at h
  cases hbody : annotateCore mode env fuel (d + 1)
      (body.instantiate1 (.fvar d ty')) with
  | error e => rw [hbody] at h; exact nomatch h
  | ok body' =>
  rw [hbody] at h; dsimp only at h
  revert h
  split
  · rename_i hw
    cases hpw : annotPwLam (pureFns mode env fuel) env (d + 1) body' with
    | error e => intro h; exact nomatch h
    | ok pw =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      refine ⟨ty', body', pw, rfl, hbody, h.symm, fun hw' => ?_⟩
      rw [hw'] at hw; exact absurd hw (by decide)
  · intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨ty', body', m.pw, rfl, hbody, h.symm, fun _ => rfl⟩

/-! ## The annotation pass keeps everything but unwritten data -/

/-- **Re-annotation keeps the tree and every written datum**: on a
let-free, bvar-closed, `d`-scoped term the annotation pass returns the
same tree (up to `fvar` types) with every written binder datum and every
`.proj` structure name unchanged; only the `.never` (unwritten) data may
be recomputed. -/
theorem annotateCore_pwKept {env : Env} :
    ∀ (F : Nat) {e : Expr} {d : Nat} {e' : Expr},
      annotateCore mode env F d e = .ok e' →
      e.looseBVarsBounded 0 = true → fvarsBelow d e → Expr.NoLet e → Expr.PwKept e e' := by
  intro F
  induction F with
  | zero =>
    intro e d e' h _ _ _
    simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h
  | succ F ih =>
    intro e
    cases e with
    | bvar i =>
      intro d e' h _ _ _
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
    | sort u =>
      intro d e' h _ _ _
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      subst h; rfl
    | const n us =>
      intro d e' h _ _ _
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      subst h; exact ⟨rfl, rfl⟩
    | fvar idx ty =>
      intro d e' h _ _ _
      rw [annotateCore_succ] at h
      simp only [annotateBody] at h
      revert h
      split
      · intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        subst h; rfl
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | lit l =>
      intro d e' h _ _ _
      rw [annotateCore_succ] at h
      cases l with
      | natVal n =>
        simp only [annotateBody] at h
        revert h
        split
        · intro h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h; rfl
        · intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
      | strVal str =>
        simp only [annotateBody] at h
        revert h
        split
        · intro h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h; rfl
        · intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
    | app f a =>
      intro d e' h hb hf hn
      obtain ⟨f', a', hf', ha', rfl⟩ := annotateCore_app_inv h
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [fvarsBelow] at hf
      exact ⟨ih hf' hb.1 hf.1 hn.1, ih ha' hb.2 hf.2 hn.2⟩
    | proj sn i pe =>
      intro d e' h hb hf hn
      obtain ⟨e₂, he₂, rfl⟩ := annotateCore_proj_name h
      simp only [looseBVarsBounded] at hb
      simp only [fvarsBelow] at hf
      exact ⟨rfl, rfl, ih he₂ hb hf hn⟩
    | letE ty v b =>
      intro d e' h _ _ hn
      exact hn.elim
    | forallE ty b m =>
      intro d e' h hb hf hn
      obtain ⟨ty', body', pw, hty', hbody, rfl, hpw⟩ := annotateCore_forallE_pw h
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [fvarsBelow] at hf
      have hfv : fvarsBelow (d + 1) (Expr.fvar d ty') := by
        simp only [fvarsBelow]; omega
      have h2 := ih hbody
        (looseBVarsBounded_instantiate1 b 0 hb.2)
        (fvarsBelow_instantiate1_gen hfv 0 (fvarsBelow_mono (Nat.le_succ d) hf.2))
        (Expr.NoLet.instantiate1 (v := .fvar d ty') trivial 0 hn.2)
      have h3 := Expr.PwKept.abstract1 (d := d) 0 h2
      rw [instantiate1_abstract1_self b 0 hf.2 hb.2] at h3
      refine ⟨fun hw => ?_, ih hty' hb.1 hf.1 hn.1, h3⟩
      rw [hpw hw]
    | lam ty b m =>
      intro d e' h hb hf hn
      obtain ⟨ty', body', pw, hty', hbody, rfl, hpw⟩ := annotateCore_lam_pw h
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [fvarsBelow] at hf
      have hfv : fvarsBelow (d + 1) (Expr.fvar d ty') := by
        simp only [fvarsBelow]; omega
      have h2 := ih hbody
        (looseBVarsBounded_instantiate1 b 0 hb.2)
        (fvarsBelow_instantiate1_gen hfv 0 (fvarsBelow_mono (Nat.le_succ d) hf.2))
        (Expr.NoLet.instantiate1 (v := .fvar d ty') trivial 0 hn.2)
      have h3 := Expr.PwKept.abstract1 (d := d) 0 h2
      rw [instantiate1_abstract1_self b 0 hf.2 hb.2] at h3
      refine ⟨fun hw => ?_, ih hty' hb.1 hf.1 hn.1, h3⟩
      rw [hpw hw]

/-- **Re-annotating a piece with no unwritten datum is the identity up to
erasure.** -/
theorem annotateCore_erasedEq_of_neverFree {env : Env} {F d : Nat} {e e' : Expr}
    (h : annotateCore mode env F d e = .ok e') (hb : e.looseBVarsBounded 0 = true)
    (hf : fvarsBelow d e) (hn : Expr.NoLet e) (hw : Expr.NeverFree e) :
    Expr.ErasedEq e e' :=
  (annotateCore_pwKept F h hb hf hn).erasedEq hw

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name CheckMode)

/-- **… and reads the same**, at every reading. -/
theorem denoteMeta_annotate_of_neverFree {mode : CheckMode} {env env' : Env} {F d : Nat}
    {e e' : Expr} (h : ConLeche.annotateCore mode env F d e = .ok e')
    (hb : e.looseBVarsBounded 0 = true) (hf : e.fvarsBelow d) (hn : Expr.NoLet e)
    (hw : Expr.NeverFree e) (acval : Name → (Name → Nat) → AnnotTerm) (φ : Name → Nat)
    (k : Nat) :
    denoteMeta acval env' φ k e' = denoteMeta acval env' φ k e :=
  (denoteMeta_erasedEq (ConLeche.annotateCore_erasedEq_of_neverFree h hb hf hn hw) k).symm

end ConLeche.Model
