module

public import ConLeche.Verify.Abstract
public import ConLeche.Verify.Subst
public import ConLeche.Verify.Cached.InstalledC

public section

/-!
# What `checkDecls` stores of what it reads

The letters of the fold are about the environment `checkDecls` RETURNS.
This module carries the other direction, for every record kind that
declares a constant: **the record's own name is in that environment,
with the record's own level parameters, and with the annotation of the
record's own type** — `checkDecls_consts`.

## The relation

The annotation pass rewrites a declared type in exactly two ways.  It
inlines every `let` (its `.letE` clause runs the official `infer_let`
triple and then recurses on `body.instantiate1 value`, so the term it
returns is the ζ reduct and the stored term is let-free), and it writes
each binder's prop-ness datum (`BinderMeta.pw`).  Nothing else about a
node is annotation: a node carries no display data at all — no binder
name, no `BinderInfo` — so `pw` is the whole of it.  Hence

    AnnotOf declared stored  :=  stored.resetMeta = declared.zeta.resetMeta

with `Expr.zeta` defined here and `Expr.resetMeta` the checker's own
binder-datum reset.  `annotateCore_annotOf` is the proof that a
successful annotation run satisfies it; on a term with no `let` and no
written datum — a bare constant, say — the relation is equality.

## Which records are covered, and which are not

`DeclC.Declares` says which constant a record declares.  Definitions,
theorems and opaques declare their header; an axiom declares its header
unless its name is *tolerated* (`toleratedAxiomNames`, exactly
`sorryAx`), in which case the record is checked for well-formedness and
then dropped and nothing is stored.  A `basisDecl` names one of the
checker's pinned basis blocks and declares nothing of its own.

**An `indDecl` block's members are outside the claim, and the reason is
not laziness.**  Three of the block's constants are stored as something
other than the annotation of what the record declares:

* the **recursor**'s stored type is the one the checker GENERATES from
  the block (`ConLeche/Kernel/Inductives/NativeInstall.lean`); the
  stream's own record is compared against it by `isDefEq` and then
  discarded, exactly as official's replay does;
* the **type former**'s stored type, on the native route, is the
  annotation of the *whnf'd* telescope whenever the declared type is not
  already a syntactic Π-telescope ending in a sort
  (`checkSumTele`, `ConLeche/Kernel/Inductives/SumInstall.lean`);
* a **constructor**'s stored type, on the native route, is the
  annotation of its type with the field domains *positivity-normalised*
  (`normCtorVal`, same file), when that changes anything.

All three are definitional equalities, not annotations, so an `AnnotOf`
claim about them would be false.  (The modeled route does store the
annotation of the declared type for formers and constructors, and its
run relation — `Semantics.MemberValRun` — already carries the equation;
what is missing there is the `find?`-at-the-end plumbing through the
member, recursor and projection folds.)

## How it is proved

Relating the CACHED annotate to the pure one needs the cached-tier
simulation, which needs `EnvWF` of the environment the record is
installed at, which in this tree comes from the model — hence the
`SetTheory V` parameter, as on the other stream-side statement.  The
walk therefore has `installRun_model`'s hypotheses and threads the model
beside the conclusion; `annotStepC_model`
(`ConLeche/Verify/Cached/InstalledC.lean`) is the per-step lemma both
walks share, and its extra conjunct — the step IS a pure `checkDecl` run
— is what lets the per-record reasoning happen entirely at the pure
checker's own run relation (`Semantics.DeclRun`).

`ConLeche/Verify/Cached/StreamThm.lean` proves the bare-constant special
case a second and cheaper way, with no model and no `V`: a bare constant
needs no annotation specification at all, and the step's own `flushC`
empties the annotation memo, so the cached pass can be read off
directly.  That is why the main corollary at the stream
(`no_False_theorem_accepted`) does not go through this module.
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


/-! ## What a record of the stream declares -/

namespace Cached

open ConLeche ConLeche.Semantics ConLeche.Model

/-- **What a record of the fold's input declares.**  `checkDecls`'s
input is a list of parsed records, and this says which constant each
kind of record claims a name and a type for:

* a definition, a theorem and an opaque declare their header;
* an axiom declares its header **unless its name is tolerated**
  (`toleratedAxiomNames`, exactly `sorryAx`): that record is checked for
  well-formedness and then *dropped*, and every later record that
  mentions the name is declined;
* a `basisDecl` declares nothing of its own — it names one of the
  checker's pinned basis blocks, and the constants installed are the
  pins';
* an `indDecl` block's members are NOT covered here.  See the module
  docstring: the recursor's stored type is the generated one, and the
  native route may annotate a *whnf'd* type former telescope or a
  positivity-normalised constructor type rather than the declared one,
  so no `AnnotOf` claim is true of them. -/
@[expose] def DeclC.Declares : DeclC → ConstantVal → Prop
  | .defnDecl cv _ _, cv' => cv' = cv
  | .thmDecl cv _, cv' => cv' = cv
  | .opaqueDecl cv _, cv' => cv' = cv
  | .axiomDecl cv, cv' => cv' = cv ∧ toleratedAxiomNames.contains cv.name = false
  | .basisDecl _, _ => False
  | .indDecl _ _, _ => False

/-! ## A name-unique environment finds what it holds -/

theorem find?_name_of_mem : ∀ {cs : List ConstantInfo}, (cs.map (·.name)).Nodup →
    ∀ {c : ConstantInfo}, c ∈ cs → cs.find? (·.name == c.name) = some c := by
  intro cs
  induction cs with
  | nil => intro _ c hc; exact absurd hc List.not_mem_nil
  | cons a t ih =>
    intro hnd c hc
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    by_cases hb : (a.name == c.name) = true
    · simp only [hb]
      rcases List.mem_cons.mp hc with rfl | hc'
      · rfl
      · exact absurd (by rw [eq_of_beq hb]; exact List.mem_map.mpr ⟨c, hc', rfl⟩) hnd.1
    · rw [Bool.not_eq_true] at hb
      simp only [hb]
      rcases List.mem_cons.mp hc with rfl | hc'
      · simp at hb
      · exact ih hnd.2 hc'

/-- A name-unique environment finds every constant it holds. -/
theorem find?_of_mem_nodup {env : Env} (hnd : NodupNames env) {c : ConstantInfo}
    (hc : c ∈ env.consts) : env.find? c.name = some c :=
  find?_name_of_mem hnd hc

/-! ## One declaration's install, at the pure checker -/

/-- **What one accepted declaration stores of what it declares.**  Every
record kind that declares a constant stores it under its own name, with
its own level parameters, and with the *annotation* of the declared
type — `AnnotOf`. -/
theorem checkDecl_declares {μ : CheckMode} {env env₂ : Env} {F : Nat}
    {pd : DeclC} {d : Declaration} (hd : DeclCRel pd d)
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂)
    {cv : ConstantVal} (hcv : DeclC.Declares pd cv) :
    ∃ c ∈ env₂.consts, c.name = cv.name ∧
      c.toConstantVal.levelParams = cv.levelParams ∧
      AnnotOf cv.type c.toConstantVal.type := by
  have hrun := ConLeche.Semantics.checkDeclRun_ofEnvFactsE h
  cases hd with
  | @defnDecl cv₀ tyE value ve hint hty hv =>
    obtain rfl : tyE = cv₀.type := hty.symm
    obtain rfl : cv = cv₀ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclDefnRun] at hrun
    obtain ⟨type', value', hcvr, -, henv₂, -, -⟩ := hrun
    obtain ⟨-, -, -, -, hb, hfv, hann, -, -, -⟩ := hcvr
    refine ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact annotateCore_annotOf F hann hb
        ((Expr.WScoped.of_not_hasFvar hfv).fvarsBelow)
  | @thmDecl cv₀ tyE value ve hty hv =>
    obtain rfl : tyE = cv₀.type := hty.symm
    obtain rfl : cv = cv₀ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclThmRun] at hrun
    obtain ⟨type', value', hcvr, -, -, henv₂⟩ := hrun
    obtain ⟨-, -, -, -, hb, hfv, hann, -, -, -⟩ := hcvr
    refine ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ ve, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact annotateCore_annotOf F hann hb
        ((Expr.WScoped.of_not_hasFvar hfv).fvarsBelow)
  | @opaqueDecl cv₀ tyE value ve hty hv =>
    obtain rfl : tyE = cv₀.type := hty.symm
    obtain rfl : cv = cv₀ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclOpaqueRun] at hrun
    obtain ⟨type', value', hcvr, -, henv₂, -⟩ := hrun
    obtain ⟨-, -, -, -, hb, hfv, hann, -, -, -⟩ := hcvr
    refine ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact annotateCore_annotOf F hann hb
        ((Expr.WScoped.of_not_hasFvar hfv).fvarsBelow)
  | @axiomDecl cv₀ tyE hty =>
    obtain rfl : tyE = cv₀.type := hty.symm
    obtain ⟨rfl, htol⟩ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclAxiomRun] at hrun
    obtain ⟨type', hcvr, hdisj⟩ := hrun
    obtain ⟨-, -, -, -, hb, hfv, hann, -, -, -⟩ := hcvr
    have henv₂ : env₂ = ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩ := by
      rcases hdisj with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
        ⟨-, -, -, -, -, -, htol', -⟩
      · exact he
      · exact he
      · exact he
      · exact absurd (htol ▸ htol') (by simp)
    refine ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact annotateCore_annotOf F hann hb
        ((Expr.WScoped.of_not_hasFvar hfv).fvarsBelow)
  | basisDecl => exact hcv.elim
  | indDecl => exact hcv.elim

/-! ## The walk -/

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The walk**: along an accepting phase-A run whose start environment
carries the model, every record's declared constant is stored — with its
name, its level parameters and the annotation of its type — and is still
there at the end.  The hypotheses are `installRun_model`'s. -/
theorem installRun_declares (hμ : μ.verifiedChecks = true) {ds : List DeclC}
    {p : Nat × FEnv × Array PendingCheck} {s : CState}
    {q : Nat × FEnv × Array PendingCheck} {s' : CState}
    (hrun : InstallRun μ ds p s q s') :
    p.2.1 = mkFEnv p.2.1.env → EnvModelOk V μ p.2.1.env → CSOKF s →
    NodupNames q.2.1.env →
    (∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) →
    ∀ pd ∈ ds, ∀ cv : ConstantVal, DeclC.Declares pd cv →
      ∃ c ∈ q.2.1.env.consts, c.name = cv.name ∧
        c.toConstantVal.levelParams = cv.levelParams ∧
        AnnotOf cv.type c.toConstantVal.type := by
  induction hrun with
  | nil p s => exact fun _ _ _ _ _ pd hmem => absurd hmem List.not_mem_nil
  | @cons pd ds p p₁ q s s₁ s' hstep rest ih =>
    intro hfe hm hresA hnd hB pd' hmem cv hcv
    obtain ⟨i, fe, pend⟩ := p
    obtain ⟨fe₁, pend₁, rfl, hstepC⟩ := annotDeclStep_ok hstep
    simp only at hfe hstepC
    obtain ⟨hpush₁, -⟩ :=
      annotStepC_push μ i (PushChain.self hfe) pend pd s (fe₁, pend₁) s₁ hstepC
    have hfe₁ : fe₁ = mkFEnv fe₁.env := hpush₁.canon
    obtain ⟨hchainF, new₁, hpend₁⟩ := installRun_trace μ rest (PushChain.self hfe₁)
    obtain ⟨hm₁, hres₁, dd, F, hdrel, hF⟩ :=
      annotStepC_model (V := V) hμ hfe hfe₁ hm hresA hstepC hchainF hpend₁ hnd hB
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · obtain ⟨c, hc, h1, h2, h3⟩ := checkDecl_declares hdrel hF hcv
      obtain ⟨new, hnew⟩ := hchainF.2.1
      exact ⟨c, by rw [hnew]; exact List.mem_append_right _ hc, h1, h2, h3⟩
    · exact ih hfe₁ hm₁ hres₁ hnd hB pd' hmem' cv hcv

/-! ## The theorem -/

/-- **What `checkDecls` stores of what it reads.**  Every record of the
fold's input that declares a constant — a definition, a theorem, an
opaque, or an axiom whose name is not tolerated — leaves in the returned
environment a constant of that very name, with the record's own level
parameters, whose stored type is the *annotation* of the declared one:
the same term with every `let` inlined and the binder data rewritten
(`AnnotOf`).  `basisDecl` records declare nothing, and an `indDecl`
block's members are outside the claim (see the module docstring). -/
theorem checkDecls_consts (V : Type w) [SetTheory V]
    {ds : List DeclC} {env : Env} (accepted : checkDecls .verified ds = .ok env)
    {pd : DeclC} (hmem : pd ∈ ds) {cv : ConstantVal} (hcv : DeclC.Declares pd cv) :
    ∃ c, env.find? cv.name = some c ∧
      c.toConstantVal.levelParams = cv.levelParams ∧
      AnnotOf cv.type c.toConstantVal.type := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked _ accepted
  obtain ⟨n, st, run⟩ := fc.1.run
  have hchain := installRun_trace _ run (PushChain.refl Env.empty)
  have hnd : NodupNames fc.1.fe.env := hchain.1.2.2 List.nodup_nil
  obtain ⟨c, hc, h1, h2, h3⟩ :=
    installRun_declares (V := V) rfl run rfl
      ⟨⟨EnvModelM.empty V _⟩, EtaFamiliesClosed.empty⟩ CSOKF.empty
      hnd fc.records pd hmem cv hcv
  exact ⟨c, h1 ▸ find?_of_mem_nodup hnd hc, h2, h3⟩

end Cached

end ConLeche
