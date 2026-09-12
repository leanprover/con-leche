module

public import ConLeche.Verify.Abstract
public import ConLeche.Verify.Subst

public section

/-!
# What `checkDecls` stores of what it reads

(module docstring to be written)
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

open Expr

/-! ## The ζ reduct -/

/-- **The ζ reduct of a term**: every `let` inlined by substituting its
value into its body.  The annotation pass returns exactly this — its
`.letE` clause checks the official `infer_let` triple and then recurses
on `body.instantiate1 value` — so it is half of the relation between a
declared type and the stored one.

The substitution is the capture-avoiding one (`instantiate1Lift`): a
`let` nested under a binder has a value that mentions that binder, and
the plain `instantiate1` would capture it.  At the *pass*'s own call the
two agree, because the pass opens every binder before it descends and
meets only bvar-closed values (`instantiate1Lift_eq_instantiate1`). -/
@[expose] def Expr.zeta : Expr → Expr
  | .app f a => .app (zeta f) (zeta a)
  | .lam ty b m => .lam (zeta ty) (zeta b) m
  | .forallE ty b m => .forallE (zeta ty) (zeta b) m
  | .letE _ v b => (zeta b).instantiate1Lift (zeta v) 0
  | .proj s i e => .proj s i (zeta e)
  | .fvar i ty => .fvar i ty
  | e => e

/-- **The relation**: `stored` is an annotation of `declared` — the same
term up to binder data (`Expr.resetMeta`) once the declared side's
`let`s are inlined.  Nothing else about a term is annotation: a node
carries no display data at all (`ConLeche/Kernel/Expr.lean`), so
`BinderMeta.pw` on `lam`/`forallE` is the whole of what the pass writes,
and `resetMeta` is the whole of what erasing it means. -/
@[expose] def AnnotOf (declared stored : Expr) : Prop :=
  stored.resetMeta = declared.zeta.resetMeta

/-- A term that carries no `let` and no written binder datum is its own
annotation — the shape the main corollary's bare constant takes. -/
theorem AnnotOf.refl_const (n : Name) (ls : List Level) :
    AnnotOf (.const n ls) (.const n ls) := rfl

/-! ## `resetMeta` is blind to the de Bruijn operations -/

theorem resetMeta_instantiate1 (v : Expr) :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 v k).resetMeta = e.resetMeta.instantiate1 v.resetMeta k := by
  intro e
  induction e <;> intro k <;> simp_all [instantiate1, resetMeta]
  case bvar i =>
    by_cases h1 : i = k
    · simp [h1, resetMeta]
    · by_cases h2 : i > k <;> simp [h1, h2, resetMeta]

theorem resetMeta_abstract1 (d : Nat) :
    ∀ (e : Expr) (k : Nat),
      (e.abstract1 d k).resetMeta = e.resetMeta.abstract1 d k := by
  intro e
  induction e <;> intro k <;> simp_all [abstract1, resetMeta]
  case fvar idx ty ih => split <;> simp [resetMeta, abstract1, *]

theorem looseBVarsBounded_resetMeta :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      e.resetMeta.looseBVarsBounded k = true := by
  intro e
  induction e <;> intro k h <;> simp_all [resetMeta, looseBVarsBounded]

theorem fvarsBelow_resetMeta (d : Nat) :
    ∀ (e : Expr), fvarsBelow d e → fvarsBelow d e.resetMeta := by
  intro e
  induction e <;> intro h <;> simp_all [resetMeta, fvarsBelow]

/-! ## Bounds and scopes through the capture-avoiding substitution -/

/-- A lift raises the loose-bvar bound by the lift's amount. -/
theorem looseBVarsBounded_lift {n : Nat} :
    ∀ (e : Expr) (b c : Nat), e.looseBVarsBounded b = true →
      (e.liftLooseBVars n c).looseBVarsBounded (b + n) = true := by
  intro e
  induction e with
  | bvar i =>
    intro b c h
    simp only [looseBVarsBounded, decide_eq_true_eq] at h
    simp only [liftLooseBVars]
    split <;> simp only [looseBVarsBounded, decide_eq_true_eq] <;> omega
  | app f a ihf iha =>
    intro b c h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [liftLooseBVars, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf b c h.1, iha b c h.2⟩
  | lam ty bd m ihty ihb =>
    intro b c h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [liftLooseBVars, looseBVarsBounded, Bool.and_eq_true]
    refine ⟨ihty b c h.1, ?_⟩
    rw [show b + n + 1 = b + 1 + n from by omega]
    exact ihb (b + 1) (c + 1) h.2
  | forallE ty bd m ihty ihb =>
    intro b c h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [liftLooseBVars, looseBVarsBounded, Bool.and_eq_true]
    refine ⟨ihty b c h.1, ?_⟩
    rw [show b + n + 1 = b + 1 + n from by omega]
    exact ihb (b + 1) (c + 1) h.2
  | letE ty v bd ihty ihv ihb =>
    intro b c h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [liftLooseBVars, looseBVarsBounded, Bool.and_eq_true]
    refine ⟨⟨ihty b c h.1.1, ihv b c h.1.2⟩, ?_⟩
    rw [show b + n + 1 = b + 1 + n from by omega]
    exact ihb (b + 1) (c + 1) h.2
  | proj sn i pe ih =>
    intro b c h
    simp only [looseBVarsBounded] at h
    simp only [liftLooseBVars, looseBVarsBounded]
    exact ih b c h
  | _ => intro b c h; simp [liftLooseBVars, looseBVarsBounded]

theorem fvarsBelow_liftLooseBVars {d n : Nat} :
    ∀ (e : Expr) (c : Nat), fvarsBelow d e → fvarsBelow d (e.liftLooseBVars n c) := by
  intro e
  induction e <;> intro c h <;> simp_all [liftLooseBVars, fvarsBelow]
  case bvar i => split <;> simp [fvarsBelow]

theorem fvarsBelow_instantiate1Lift {d : Nat} {a : Expr} (ha : fvarsBelow d a) :
    ∀ (e : Expr) (k : Nat), fvarsBelow d e → fvarsBelow d (e.instantiate1Lift a k) := by
  intro e
  induction e <;> intro k h <;> simp_all [instantiate1Lift, fvarsBelow]
  case bvar i =>
    split
    · exact fvarsBelow_liftLooseBVars _ _ ha
    · split <;> simp [fvarsBelow]

theorem looseBVarsBounded_instantiate1Lift {a : Expr} :
    ∀ (e : Expr) (k j : Nat), a.looseBVarsBounded k = true →
      e.looseBVarsBounded (k + j + 1) = true →
      (e.instantiate1Lift a j).looseBVarsBounded (k + j) = true := by
  intro e
  induction e with
  | bvar i =>
    intro k j ha h
    simp only [looseBVarsBounded, decide_eq_true_eq] at h
    simp only [instantiate1Lift]
    split
    · rename_i hij
      subst hij
      exact looseBVarsBounded_lift (n := i) a k 0 ha
    · split <;> simp only [looseBVarsBounded, decide_eq_true_eq] <;> omega
  | app f b ihf ihb =>
    intro k j ha h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [instantiate1Lift, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf k j ha h.1, ihb k j ha h.2⟩
  | lam ty b m ihty ihb =>
    intro k j ha h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [instantiate1Lift, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihty k j ha h.1, ihb k (j + 1) ha h.2⟩
  | forallE ty b m ihty ihb =>
    intro k j ha h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [instantiate1Lift, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihty k j ha h.1, ihb k (j + 1) ha h.2⟩
  | letE ty v b ihty ihv ihb =>
    intro k j ha h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [instantiate1Lift, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨ihty k j ha h.1.1, ihv k j ha h.1.2⟩, ihb k (j + 1) ha h.2⟩
  | proj sn i pe ih =>
    intro k j ha h
    simp only [looseBVarsBounded] at h
    simp only [instantiate1Lift, looseBVarsBounded]
    exact ih k j ha h
  | _ => intro k j ha h; simp [instantiate1Lift, looseBVarsBounded]

/-! ## `zeta` keeps bounds and scopes -/

theorem looseBVarsBounded_zeta :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      e.zeta.looseBVarsBounded k = true := by
  intro e
  induction e with
  | app f b ihf ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [zeta, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf k h.1, ihb k h.2⟩
  | lam ty b m ihty ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [zeta, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihty k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [zeta, looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihty k h.1, ihb (k + 1) h.2⟩
  | letE ty v b ihty ihv ihb =>
    intro k h
    simp only [looseBVarsBounded, Bool.and_eq_true] at h
    simp only [zeta]
    exact looseBVarsBounded_instantiate1Lift (zeta b) k 0 (ihv k h.1.2)
      (ihb (k + 1) h.2)
  | proj sn i pe ih =>
    intro k h
    simp only [looseBVarsBounded] at h
    simp only [zeta, looseBVarsBounded]
    exact ih k h
  | fvar idx ty ih => intro k h; simp [zeta, looseBVarsBounded]
  | _ => intro k h; simpa [zeta] using h

theorem fvarsBelow_zeta (d : Nat) :
    ∀ (e : Expr), fvarsBelow d e → fvarsBelow d e.zeta := by
  intro e
  induction e with
  | app f b ihf ihb =>
    intro h
    simp only [fvarsBelow] at h
    simp only [zeta, fvarsBelow]
    exact ⟨ihf h.1, ihb h.2⟩
  | lam ty b m ihty ihb =>
    intro h
    simp only [fvarsBelow] at h
    simp only [zeta, fvarsBelow]
    exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro h
    simp only [fvarsBelow] at h
    simp only [zeta, fvarsBelow]
    exact ⟨ihty h.1, ihb h.2⟩
  | letE ty v b ihty ihv ihb =>
    intro h
    simp only [fvarsBelow] at h
    simp only [zeta]
    exact fvarsBelow_instantiate1Lift (ihv h.2.1) (zeta b) 0 (ihb h.2.2)
  | proj sn i pe ih =>
    intro h
    simp only [fvarsBelow] at h
    simp only [zeta, fvarsBelow]
    exact ih h
  | fvar idx ty ih => intro h; simpa [zeta, fvarsBelow] using h
  | _ => intro h; simpa [zeta] using h

/-! ## `zeta` commutes with a closed substitution -/

/-- Substituting a bvar-closed term commutes with ζ reduction: the pass
opens a binder with a fresh `fvar` and inlines a `let` value, and both
are closed where it does it. -/
theorem zeta_instantiate1 {s : Expr} (hs : s.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k : Nat),
      (e.instantiate1 s k).zeta = e.zeta.instantiate1 s.zeta k := by
  intro e
  induction e <;> intro k <;> simp_all [instantiate1, zeta]
  case bvar i =>
    by_cases h1 : i = k
    · simp [h1, zeta, instantiate1]
    · by_cases h2 : i > k <;> simp [h1, h2, zeta, instantiate1]
  case letE ty v b ihty ihv ihb =>
    have h := instantiate1Lift_instantiate1 (a := zeta v) (s := zeta s)
      (looseBVarsBounded_zeta s 0 hs) (zeta b) 0 k
    rw [show 0 + 1 + k = k + 1 from by omega, Nat.zero_add] at h
    exact h.symm

/-! ## Opening a binder and closing it again -/

/-- Opening a body with a fresh variable and closing it again is the
identity — the ∀/λ clauses' roundtrip, read in the direction the
annotation pass takes it. -/
theorem instantiate1_abstract1_self {d : Nat} {T : Expr} :
    ∀ (e : Expr) (k : Nat), fvarsBelow d e → e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d T) k).abstract1 d k = e := by
  intro e
  induction e with
  | bvar i =>
    intro k hf hb
    simp only [looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [instantiate1]
    by_cases h1 : i = k
    · simp [h1, abstract1]
    · rw [if_neg h1, if_neg (by omega)]
      simp [abstract1]
  | fvar idx ty ih =>
    intro k hf hb
    simp only [fvarsBelow] at hf
    simp only [instantiate1, abstract1]
    rw [if_neg (by omega)]
  | app f a ihf iha =>
    intro k hf hb
    simp only [fvarsBelow] at hf
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [instantiate1, abstract1, ihf k hf.1 hb.1, iha k hf.2 hb.2]
  | lam ty b m ihty ihb =>
    intro k hf hb
    simp only [fvarsBelow] at hf
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [instantiate1, abstract1, ihty k hf.1 hb.1, ihb (k + 1) hf.2 hb.2]
  | forallE ty b m ihty ihb =>
    intro k hf hb
    simp only [fvarsBelow] at hf
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [instantiate1, abstract1, ihty k hf.1 hb.1, ihb (k + 1) hf.2 hb.2]
  | letE ty v b ihty ihv ihb =>
    intro k hf hb
    simp only [fvarsBelow] at hf
    simp only [looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [instantiate1, abstract1, ihty k hf.1 hb.1.1, ihv k hf.2.1 hb.1.2,
      ihb (k + 1) hf.2.2 hb.2]
  | proj sn i pe ih =>
    intro k hf hb
    simp only [fvarsBelow] at hf
    simp only [looseBVarsBounded] at hb
    simp only [instantiate1, abstract1, ih k hf hb]
  | _ => intro k hf hb; simp [instantiate1, abstract1]

/-! ## The annotation pass returns the ζ reduct -/

variable {mode : CheckMode}

/-- Inversion for `annotate` on projections, keeping the node's own
structure name: the accepting arm checks `T = sn` (task #271), which
`annotateCore_proj_inv` discards. -/
theorem annotateCore_proj_name {env : Env} {fuel d : Nat} {sn : Name}
    {i : Nat} {e e' : Expr}
    (h : annotateCore mode env (fuel + 1) d (.proj sn i e) = .ok e') :
    ∃ e₂, annotateCore mode env fuel d e = .ok e₂ ∧ e' = .proj sn i e₂ := by
  obtain ⟨e₂, tt, te, he₂, -, -, T, us, entry, hfn, hfp, -, heq⟩ :=
    annotateCore_proj_inv h
  refine ⟨e₂, he₂, ?_⟩
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def, inferTypeIO_def, whnf_def] at h
  rw [he₂] at h
  dsimp only at h
  cases hte : inferTypeIO mode env fuel d e₂ with
  | error err => rw [hte] at h; exact nomatch h
  | ok tt' =>
  rw [hte] at h
  dsimp only at h
  cases hw : whnf mode env fuel d tt' with
  | error err => rw [hw] at h; exact nomatch h
  | ok te' =>
  rw [hw] at h
  dsimp only at h
  revert h
  cases hfn' : te'.getAppFn with
  | const T' us' => ?_
  | bvar i2 => intro h; exact nomatch h
  | sort u => intro h; exact nomatch h
  | fvar i2 t2 => intro h; exact nomatch h
  | app f2 a2 => intro h; exact nomatch h
  | lam t2 b2 m2 => intro h; exact nomatch h
  | forallE t2 b2 m2 => intro h; exact nomatch h
  | letE t2 v2 b2 => intro h; exact nomatch h
  | lit l2 => intro h; exact nomatch h
  | proj s2 i2 e2 => intro h; exact nomatch h
  intro h
  dsimp only at h
  revert h
  cases hfp' : env.findProj? T' i with
  | none => intro h; exact nomatch h
  | some entry' => ?_
  intro h
  dsimp only at h
  split at h
  case isFalse => exact nomatch h
  case isTrue hsn =>
  split at h
  case isFalse => exact nomatch h
  case isTrue hlen =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [← h, hsn]

/-- **The annotation pass returns the ζ reduct.**  A successful pure
annotation run over a bvar-closed, `d`-scoped term returns a term
related to it by `AnnotOf`: the `let`s inlined, the binder data
rewritten, and nothing else touched. -/
theorem annotateCore_annotOf {env : Env} :
    ∀ (F : Nat) {e : Expr} {d : Nat} {e' : Expr},
      annotateCore mode env F d e = .ok e' →
      e.looseBVarsBounded 0 = true → fvarsBelow d e → AnnotOf e e' := by
  intro F
  induction F with
  | zero =>
    intro e d e' h _ _
    simp [annotateCore_zero, throw, throwThe, MonadExceptOf.throw] at h
  | succ F ih =>
    intro e
    cases e with
    | bvar i =>
      intro d e' h _ _
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      simp [AnnotOf, ← h, zeta]
    | sort u =>
      intro d e' h _ _
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      simp [AnnotOf, ← h, zeta]
    | const n us =>
      intro d e' h _ _
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      simp [AnnotOf, ← h, zeta]
    | fvar idx ty =>
      intro d e' h _ _
      rw [annotateCore_succ] at h
      simp only [annotateBody] at h
      revert h
      split
      · intro h
        simp only [pure, Except.pure, Except.ok.injEq] at h
        simp [AnnotOf, ← h, zeta]
      · intro h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | lit l =>
      intro d e' h _ _
      rw [annotateCore_succ] at h
      cases l with
      | natVal n =>
        simp only [annotateBody] at h
        revert h
        split
        · intro h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          simp [AnnotOf, ← h, zeta]
        · intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
      | strVal str =>
        simp only [annotateBody] at h
        revert h
        split
        · intro h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          simp [AnnotOf, ← h, zeta]
        · intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
    | app f a =>
      intro d e' h hb hf
      obtain ⟨f', a', hf', ha', rfl⟩ := annotateCore_app_inv h
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [fvarsBelow] at hf
      have h1 := ih hf' hb.1 hf.1
      have h2 := ih ha' hb.2 hf.2
      simp only [AnnotOf, zeta, resetMeta] at h1 h2 ⊢
      rw [h1, h2]
    | proj sn i pe =>
      intro d e' h hb hf
      obtain ⟨e₂, he₂, rfl⟩ := annotateCore_proj_name h
      simp only [looseBVarsBounded] at hb
      simp only [fvarsBelow] at hf
      have h1 := ih he₂ hb hf
      simp only [AnnotOf, zeta, resetMeta] at h1 ⊢
      rw [h1]
    | letE ty v b =>
      intro d e' h hb hf
      obtain ⟨ty', v', -, -, hbody, -⟩ := annotateCore_letE_inv h
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [fvarsBelow] at hf
      have hbv : v.looseBVarsBounded 0 = true := hb.1.2
      have h1 := ih hbody
        (looseBVarsBounded_instantiate1_gen hbv hb.2)
        (fvarsBelow_instantiate1_gen hf.2.1 0 hf.2.2)
      simp only [AnnotOf, zeta] at h1 ⊢
      rw [h1, zeta_instantiate1 hbv b 0,
        instantiate1Lift_eq_instantiate1 (looseBVarsBounded_zeta v 0 hbv)]
    | forallE ty b m =>
      intro d e' h hb hf
      obtain ⟨ty', body', pw, hty', hbody, rfl⟩ := annotateCore_forallE_inv h
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [fvarsBelow] at hf
      have hfv : fvarsBelow (d + 1) (Expr.fvar d ty') := by
        simp only [fvarsBelow]; omega
      have h1 := ih hty' hb.1 hf.1
      have h2 := ih hbody
        (looseBVarsBounded_instantiate1 b 0 hb.2)
        (fvarsBelow_instantiate1_gen hfv 0 (fvarsBelow_mono (Nat.le_succ d) hf.2))
      simp only [AnnotOf] at h1 h2 ⊢
      have hbody2 : (body'.abstract1 d).resetMeta = b.zeta.resetMeta := by
        rw [resetMeta_abstract1, h2,
          zeta_instantiate1 (s := Expr.fvar d ty') (by simp [looseBVarsBounded]) b 0]
        simp only [zeta]
        rw [resetMeta_instantiate1]
        exact instantiate1_abstract1_self _ 0
          (fvarsBelow_resetMeta d _ (fvarsBelow_zeta d b hf.2))
          (looseBVarsBounded_resetMeta _ 1 (looseBVarsBounded_zeta b 1 hb.2))
      simp only [zeta, resetMeta, h1, hbody2]
    | lam ty b m =>
      intro d e' h hb hf
      obtain ⟨ty', body', pw, hty', hbody, rfl⟩ := annotateCore_lam_inv h
      simp only [looseBVarsBounded, Bool.and_eq_true] at hb
      simp only [fvarsBelow] at hf
      have hfv : fvarsBelow (d + 1) (Expr.fvar d ty') := by
        simp only [fvarsBelow]; omega
      have h1 := ih hty' hb.1 hf.1
      have h2 := ih hbody
        (looseBVarsBounded_instantiate1 b 0 hb.2)
        (fvarsBelow_instantiate1_gen hfv 0 (fvarsBelow_mono (Nat.le_succ d) hf.2))
      simp only [AnnotOf] at h1 h2 ⊢
      have hbody2 : (body'.abstract1 d).resetMeta = b.zeta.resetMeta := by
        rw [resetMeta_abstract1, h2,
          zeta_instantiate1 (s := Expr.fvar d ty') (by simp [looseBVarsBounded]) b 0]
        simp only [zeta]
        rw [resetMeta_instantiate1]
        exact instantiate1_abstract1_self _ 0
          (fvarsBelow_resetMeta d _ (fvarsBelow_zeta d b hf.2))
          (looseBVarsBounded_resetMeta _ 1 (looseBVarsBounded_zeta b 1 hb.2))
      simp only [zeta, resetMeta, h1, hbody2]


end ConLeche
