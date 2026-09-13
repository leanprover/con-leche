module

public import ConLeche.Verify.Inductives.CopyTypes
public import ConLeche.Verify.Mono

public section

/-!
# The two lemmas behind `AuxFormersAnnot` (task #300)

placeholder
-/

namespace ConLeche

open Expr

variable {mode : CheckMode}

/-! ## A conservative environment extension -/

/-- **`env'` extends `env` conservatively**: every constant stored in
`env` is stored in `env'`, unchanged.  This is the checker's own shape
of extension (a cons over a freshness check) and the only thing the
lemmas below need.

`ConLeche/Verify/Denote/Install.lean` states the same relation as
`Verify.EnvExtends` for the denotation transports; that spelling sits
in a plain `public section`, so its body does not unfold outside its
own module and it cannot be *applied* here.  Restating it (four tokens)
is the module system's own answer — the alternative would be to
`@[expose]` a definition the Denote tier deliberately keeps opaque. -/
@[expose] def EnvExt (env env' : Env) : Prop :=
  ∀ n ci, env.find? n = some ci → env'.find? n = some ci

theorem EnvExt.refl (env : Env) : EnvExt env env := fun _ _ h => h

theorem EnvExt.trans {e₁ e₂ e₃ : Env} (h₁ : EnvExt e₁ e₂) (h₂ : EnvExt e₂ e₃) :
    EnvExt e₁ e₃ := fun n ci h => h₂ n ci (h₁ n ci h)

/-- A cons over a fresh name is a conservative extension. -/
theorem EnvExt.cons {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none) : EnvExt env ⟨c₀ :: env.consts⟩ := by
  intro n ci h
  rw [Env.find?_cons]
  split
  · next hn => rw [← hn, hfresh] at h; exact nomatch h
  · exact h

/-! ## The head readers under a conservative environment extension -/

/-- A shape predicate on a stored constant is monotone along an
extension: it rejects `none`, so a `true` reading had to have found the
constant, and the extension stores the same one. -/
private theorem constShapeOk_envExt {env env' : Env} (hext : EnvExt env env')
    (P : Option ConstantInfo → Bool) (hnone : P none = false) (n : Name)
    (h : P (env.find? n) = true) : P (env'.find? n) = true := by
  cases hf : env.find? n with
  | none => rw [hf, hnone] at h; exact nomatch h
  | some ci => rw [hext n ci hf]; rwa [hf] at h

/-- **The head reader's answers survive an extension.**  Every lookup
the reader makes is on the `some` branch of its own answer, so the
extension returns the same constant and the same datum. -/
theorem headTypePW_envExt {env env' : Env} (hext : EnvExt env env')
    {h : Expr} {n : Nat} {pw : PropWhen}
    (hr : headTypePW env.find? h n = some pw) :
    headTypePW env'.find? h n = some pw := by
  cases h with
  | const I us =>
    simp only [headTypePW] at hr ⊢
    cases hf : env.find? I with
    | none => rw [hf] at hr; exact nomatch hr
    | some ci => rw [hext I ci hf]; rwa [hf] at hr
  | _ => exact hr

/-- `typeSortPW`'s answers survive an extension. -/
theorem typeSortPW_envExt {env env' : Env} (hext : EnvExt env env')
    {T : Expr} {pw : PropWhen} (hr : typeSortPW env.find? T = some pw) :
    typeSortPW env'.find? T = some pw := by
  cases T with
  | forallE ty b m => exact hr
  | sort u => exact hr
  | _ =>
    simp only [typeSortPW] at hr ⊢
    exact headTypePW_envExt hext hr

/-- `headProofPW`'s answers survive an extension (through
`typeSortPW`'s, which it reads off the head's stored type). -/
theorem headProofPW_envExt {env env' : Env} (hext : EnvExt env env')
    {h : Expr} {pw : PropWhen} (hr : headProofPW env.find? h = some pw) :
    headProofPW env'.find? h = some pw := by
  cases h with
  | const c us =>
    simp only [headProofPW] at hr ⊢
    cases hf : env.find? c with
    | none => rw [hf] at hr; exact nomatch hr
    | some ci =>
      rw [hext c ci hf]
      rw [hf] at hr
      dsimp only at hr ⊢
      cases hts : typeSortPW env.find? ci.toConstantVal.type with
      | none => rw [hts] at hr; simp at hr
      | some pw0 =>
        rw [hts] at hr
        rw [typeSortPW_envExt hext hts]
        exact hr
  | fvar idx ty => exact typeSortPW_envExt hext hr
  | _ => exact hr

/-- `proofPW`'s answers survive an extension. -/
theorem proofPW_envExt {env env' : Env} (hext : EnvExt env env')
    {a : Expr} {pw : PropWhen} (hr : proofPW env.find? a = some pw) :
    proofPW env'.find? a = some pw := by
  cases a with
  | lam ty b m => exact hr
  | _ =>
    simp only [proofPW] at hr ⊢
    exact headProofPW_envExt hext hr

/-! ## The literal-support guards under an extension -/

theorem natLitSupported_envExt {env env' : Env} (hext : EnvExt env env')
    (h : natLitSupported env = true) : natLitSupported env' = true := by
  simp only [natLitSupported, Bool.and_eq_true] at h ⊢
  exact ⟨⟨constShapeOk_envExt hext natIndOk rfl _ h.1.1,
    constShapeOk_envExt hext natZeroOk rfl _ h.1.2⟩,
    constShapeOk_envExt hext natSuccOk rfl _ h.2⟩

theorem strLitSupported_envExt {env env' : Env} (hext : EnvExt env env')
    (h : strLitSupported env = true) : strLitSupported env' = true := by
  simp only [strLitSupported, Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, hs⟩, hsl⟩, hl⟩, hnil⟩, hcons⟩, hc⟩, hco⟩ := h
  exact ⟨⟨⟨⟨⟨⟨⟨natLitSupported_envExt hext hn,
    constShapeOk_envExt hext stringTyOk rfl _ hs⟩,
    constShapeOk_envExt hext stringOfListTyOk rfl _ hsl⟩,
    constShapeOk_envExt hext listTyOk rfl _ hl⟩,
    constShapeOk_envExt hext listNilTyOk rfl _ hnil⟩,
    constShapeOk_envExt hext listConsTyOk rfl _ hcons⟩,
    constShapeOk_envExt hext charTyOk rfl _ hc⟩,
    constShapeOk_envExt hext charOfNatTyOk rfl _ hco⟩

/-! ## The two missing ingredients, named

The annotation pass is not a pure reader: at a binder whose datum is a
parse placeholder it asks the head reader first and falls back to
INFERENCE, and its `letE` and `proj` clauses run the official typing
triple and the projection lookup outright.  Transporting a run along an
environment extension therefore needs two facts the tree does not have,
and both are stated here as explicit hypotheses rather than assumed
silently.
-/

/-- **Missing ingredient 1** — the inference slots transport along the
extension.  This is the reduction/inference/definitional-equality
counterpart of `annotateCore_envExt` and is exactly what `Verify/` does
NOT prove of `whnf`/`inferType`/`isDefEq`: delta reduction unfolds a
stored value whose own constants need not resolve at the smaller
environment, so the equality is not structural — it needs the
environment's well-formedness closure (`EnvWF`) as well as the
extension.  No lemma of that shape exists in the tree. -/
def SlotsExt (mode : CheckMode) (env env' : Env) : Prop :=
  (∀ f d e t, whnf mode env f d e = .ok t → whnf mode env' f d e = .ok t) ∧
  (∀ f d e t, inferTypeCore mode env f d e = .ok t →
    inferTypeCore mode env' f d e = .ok t) ∧
  (∀ f d e t, inferTypeIO mode env f d e = .ok t →
    inferTypeIO mode env' f d e = .ok t) ∧
  (∀ f d a b r, isDefEqCore mode env f d a b = .ok r →
    isDefEqCore mode env' f d a b = .ok r)

/-- **Missing ingredient 2** — the extension creates no reading where
the reader declined.  `annotPwPi` consults the reader FIRST, so a
constant that is absent at `env` (the reader declines, inference
answers) and present at `env'` (the reader answers) would make the two
runs write different data.  On a term whose constants all resolve at
`env` this is vacuous — but "the pass preserves `constsResolve`" is
itself an unproved fact about `whnf`'s ζ/δ outputs, so the premise is
named here instead of derived. -/
def ReaderNoNew (env env' : Env) : Prop :=
  (∀ e, typeSortPW env.find? e = none → typeSortPW env'.find? e = none) ∧
  (∀ e, proofPW env.find? e = none → proofPW env'.find? e = none)

/-- `ensureSort` transports with `whnf`. -/
theorem ensureSortCore_envExt {env env' : Env} (hs : SlotsExt mode env env')
    {f d : Nat} {e : Expr} {u : Level}
    (h : ensureSortCore mode env f d e = .ok u) :
    ensureSortCore mode env' f d e = .ok u := by
  rw [← ensureSort_def] at h ⊢
  simp only [ensureSort, Bind.bind, Except.bind, whnf_def] at h ⊢
  cases hw : whnf mode env f d e with
  | error err => rw [hw] at h; exact nomatch h
  | ok w =>
    rw [hw] at h
    rw [hs.1 f d e w hw]
    exact h

/-- The ∀ binder's datum transports. -/
theorem annotPwPi_envExt {env env' : Env} (hext : EnvExt env env')
    (hs : SlotsExt mode env env') (hnn : ReaderNoNew env env')
    {f d : Nat} {b : Expr} {pw : PropWhen}
    (h : annotPwPi (pureFns mode env f) env d b = .ok pw) :
    annotPwPi (pureFns mode env' f) env' d b = .ok pw := by
  unfold annotPwPi at h ⊢
  cases hr : typeSortPW env.find? b with
  | some pw0 => rw [hr] at h; rw [typeSortPW_envExt hext hr]; exact h
  | none =>
    rw [hr] at h
    rw [hnn.1 b hr]
    simp only [Bind.bind, Except.bind, inferTypeIO_def, ensureSort_def] at h ⊢
    cases hi : inferTypeIO mode env f d b with
    | error err => rw [hi] at h; exact nomatch h
    | ok t =>
      rw [hi] at h
      rw [hs.2.2.1 f d b t hi]
      dsimp only at h ⊢
      cases hes : ensureSortCore mode env f d t with
      | error err => rw [hes] at h; exact nomatch h
      | ok v =>
        rw [hes] at h
        rw [ensureSortCore_envExt hs hes]
        exact h

/-- The λ binder's datum transports. -/
theorem annotPwLam_envExt {env env' : Env} (hext : EnvExt env env')
    (hs : SlotsExt mode env env') (hnn : ReaderNoNew env env')
    {f d : Nat} {b : Expr} {pw : PropWhen}
    (h : annotPwLam (pureFns mode env f) env d b = .ok pw) :
    annotPwLam (pureFns mode env' f) env' d b = .ok pw := by
  unfold annotPwLam at h ⊢
  cases hr : proofPW env.find? b with
  | some pw0 => rw [hr] at h; rw [proofPW_envExt hext hr]; exact h
  | none =>
    rw [hr] at h
    rw [hnn.2 b hr]
    simp only [Bind.bind, Except.bind, inferTypeIO_def, ensureSort_def] at h ⊢
    cases hi : inferTypeIO mode env f d b with
    | error err => rw [hi] at h; exact nomatch h
    | ok t =>
      rw [hi] at h
      rw [hs.2.2.1 f d b t hi]
      dsimp only at h ⊢
      cases hi2 : inferTypeIO mode env f d t with
      | error err => rw [hi2] at h; exact nomatch h
      | ok t2 =>
        rw [hi2] at h
        rw [hs.2.2.1 f d t t2 hi2]
        dsimp only at h ⊢
        cases hes : ensureSortCore mode env f d t2 with
        | error err => rw [hes] at h; exact nomatch h
        | ok v =>
          rw [hes] at h
          rw [ensureSortCore_envExt hs hes]
          exact h


/-- `annotateCore_proj_inv` (`Verify/Abstract.lean`) **with the node's
own structure name**.  The tree's inversion drops official's
`const_name(I) == proj_sname(e)` premise (task #271) — every consumer so
far was blind to it — but rebuilding the clause at another environment
needs it, so the proof is repeated here with the conjunct kept.  (The
alternative, adding it upstream, would rebuild the whole Verify cone
for one conjunct; the duplication is the cheaper honest move and is
recorded in DESIGN §K.5.) -/
private theorem annotateCore_proj_inv' {env : Env} {fuel d : Nat} {sn : Name}
    {i : Nat} {e e' : Expr}
    (h : annotateCore mode env (fuel + 1) d (.proj sn i e) = .ok e') :
    ∃ e₂ tt te, annotateCore mode env fuel d e = .ok e₂ ∧
      inferTypeIO mode env fuel d e₂ = .ok tt ∧ whnf mode env fuel d tt = .ok te ∧
      (∃ us entry, te.getAppFn = .const sn us ∧
          env.findProj? sn i = some entry ∧
          te.getAppArgs.length = entry.numParams ∧
          e' = .proj sn i e₂) := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def, inferTypeIO_def, whnf_def] at h
  cases he : annotateCore mode env fuel d e with
  | error err => rw [he] at h; exact nomatch h
  | ok e₂ =>
  rw [he] at h
  dsimp only at h
  cases hte : inferTypeIO mode env fuel d e₂ with
  | error err => rw [hte] at h; exact nomatch h
  | ok tt =>
  rw [hte] at h
  dsimp only at h
  cases hw : whnf mode env fuel d tt with
  | error err => rw [hw] at h; exact nomatch h
  | ok te =>
  rw [hw] at h
  dsimp only at h
  refine ⟨e₂, tt, te, rfl, hte, hw, ?_⟩
  revert h
  cases hfn : te.getAppFn with
  | const T us => ?_
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
  cases hfp : env.findProj? T i with
  | none => intro h; exact nomatch h
  | some entry => ?_
  intro h
  dsimp only at h
  split at h
  case isFalse => exact nomatch h
  case isTrue hsn =>
  subst hsn
  split at h
  case isFalse => exact nomatch h
  case isTrue hlen =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact ⟨us, entry, rfl, hfp, hlen, h.symm⟩

/-- The projection table transports. -/
theorem EnvExt.findProj?_mono {env env' : Env} (hext : EnvExt env env')
    {sn : Name} {i : Nat} {entry : ProjEntry}
    (h : env.findProj? sn i = some entry) : env'.findProj? sn i = some entry := by
  obtain ⟨tbl, h0, hi, rfl⟩ := Env.findProj?_some h
  exact Env.findProj?_of_table (hext _ _ h0) hi

/-- **LEMMA (a), the general form.**  An `.ok` annotation run survives a
conservative environment extension, given the two named ingredients.
The pass itself contributes only monotone data: the literal guards and
the projection table are `some`-preserving, the head readers are
(`typeSortPW_envExt`), and everything else is structural. -/
theorem annotateCore_envExt {env env' : Env} (hext : EnvExt env env')
    (hs : SlotsExt mode env env') (hnn : ReaderNoNew env env') :
    ∀ (F d : Nat) (e r : Expr),
      annotateCore mode env F d e = .ok r →
      annotateCore mode env' F d e = .ok r := by
  intro F
  induction F with
  | zero =>
    intro d e r h
    rw [annotateCore_zero] at h
    simp only [throw, throwThe, MonadExceptOf.throw] at h
    exact nomatch h
  | succ f ih =>
    intro d e r h
    cases e with
    | bvar i => rw [annotateCore_succ] at h ⊢; exact h
    | fvar idx ty => rw [annotateCore_succ] at h ⊢; exact h
    | sort u => rw [annotateCore_succ] at h ⊢; exact h
    | const n us => rw [annotateCore_succ] at h ⊢; exact h
    | lit l =>
      rw [annotateCore_succ] at h ⊢
      cases l with
      | natVal n =>
        simp only [annotateBody] at h ⊢
        by_cases hsup : natLitSupported env = true
        · rw [if_pos (natLitSupported_envExt hext hsup)]
          rw [if_pos hsup] at h
          exact h
        · rw [if_neg hsup] at h
          simp only [throw, throwThe, MonadExceptOf.throw] at h
          exact nomatch h
      | strVal s =>
        simp only [annotateBody] at h ⊢
        by_cases hsup : strLitSupported env = true
        · rw [if_pos (strLitSupported_envExt hext hsup)]
          rw [if_pos hsup] at h
          exact h
        · rw [if_neg hsup] at h
          simp only [throw, throwThe, MonadExceptOf.throw] at h
          exact nomatch h
    | app g a =>
      obtain ⟨g', a', hg, ha, rfl⟩ := annotateCore_app_inv h
      rw [annotateCore_succ]
      simp only [annotateBody, Bind.bind, Except.bind, annotate_def]
      rw [ih d g g' hg]
      dsimp only
      rw [ih d a a' ha]
      rfl
    | forallE ty body m =>
      obtain ⟨ty', body', hty, hbody, hcase⟩ := annotateCore_forallE_inv_pw h
      rw [annotateCore_succ]
      simp only [annotateBody, Bind.bind, Except.bind, annotate_def]
      rw [ih d ty ty' hty]
      dsimp only
      rw [ih (d + 1) _ body' hbody]
      dsimp only
      rcases hcase with ⟨hw, rfl⟩ | ⟨hnw, pw, hpw, rfl⟩
      · rw [hw]
        rfl
      · rw [hnw]
        rw [annotPwPi_envExt hext hs hnn hpw]
        rfl
    | lam ty body m =>
      obtain ⟨ty', body', hty, hbody, hcase⟩ := annotateCore_lam_inv_pw h
      rw [annotateCore_succ]
      simp only [annotateBody, Bind.bind, Except.bind, annotate_def]
      rw [ih d ty ty' hty]
      dsimp only
      rw [ih (d + 1) _ body' hbody]
      dsimp only
      rcases hcase with ⟨hw, rfl⟩ | ⟨hnw, pw, hpw, rfl⟩
      · rw [hw]
        rfl
      · rw [hnw]
        rw [annotPwLam_envExt hext hs hnn hpw]
        rfl
    | letE ty v b =>
      obtain ⟨ty', v', hty, hv, hbody, tty, u, tv, hit, hes, hiv, hde⟩ :=
        annotateCore_letE_inv h
      rw [annotateCore_succ]
      simp only [annotateBody, Bind.bind, Except.bind, annotate_def, infer_def,
        defeq_def, ensureSort_def]
      rw [ih d ty ty' hty]
      dsimp only
      rw [hs.2.1 f d ty' tty hit]
      dsimp only
      rw [ensureSortCore_envExt hs hes]
      dsimp only
      rw [ih d v v' hv]
      dsimp only
      rw [hs.2.1 f d v' tv hiv]
      dsimp only
      rw [hs.2.2.2 f d tv ty' true hde]
      dsimp only
      exact ih d (b.instantiate1 v) r hbody
    | proj sn i pe =>
      obtain ⟨e₂, tt, te, he, hte, hw, us, entry, hfn, hfp, hlen, rfl⟩ :=
        annotateCore_proj_inv' h
      rw [annotateCore_succ]
      simp only [annotateBody, Bind.bind, Except.bind, annotate_def,
        inferTypeIO_def, whnf_def]
      rw [ih d pe e₂ he]
      dsimp only
      rw [hs.2.2.1 f d e₂ tt hte]
      dsimp only
      rw [hs.1 f d tt te hw]
      dsimp only
      rw [hfn]
      dsimp only
      rw [hext.findProj?_mono hfp]
      dsimp only
      rw [if_pos (rfl : sn = sn), if_pos hlen]
      rfl

end ConLeche
