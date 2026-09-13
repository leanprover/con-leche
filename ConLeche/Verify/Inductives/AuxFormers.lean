module

public import ConLeche.Verify.Inductives.CopyTypes
public import ConLeche.Verify.Mono
public import ConLeche.Kernel.Inductives.NestedElim
public import ConLeche.Kernel.Inductives.NestedInstall

public section

/-!
# The two lemmas behind `AuxFormersAnnot` (task #300)

**What this is for.**  The nested route's elimination MINTS a copy of a
container member at a pin (`mkCopy`,
`ConLeche/Kernel/Inductives/NestedElim.lean`) and hands the copies to
the mutual install as an auxiliary block.  That install annotates every
former at the **pre-block** environment (`mutualFormerChecks`,
`Kernel/Inductives/MutualInstall.lean`) and KEEPS the annotated
constant when its telescope is already `nP + nIdx` `∀`s ending in a
sort (`checkSumTele`'s first branch,
`Kernel/Inductives/SumInstall.lean`).  The model lane's premise
`AuxFormersAnnot` (DESIGN §M.23, `Model/Inductives/CopyReads.lean`)
says that the copies' STORED formers are, at the **scratch**
environment, the annotations of their minted types — and it named two
lemmas as what turns the run into that statement.  Both are here.

**(a) The annotator under a conservative environment extension.**  The
scratch environment extends the pre-block one (it holds the whole
auxiliary block), so the run the install made at `env` has to be
replayed at `envAux`.  Two theorems:

* `annotateCore_envExt` — THE GENERAL FORM: an `.ok` run transports,
  given two hypotheses that are stated here and **not** proved,
  because the tree does not have them: `SlotsExt` (the
  reduction/inference/definitional-equality slots transport) and
  `ReaderNoNew` (the extension creates no head reading where the
  reader declined).  Everything the pass contributes itself — the head
  readers (`typeSortPW_envExt`, `proofPW_envExt`), the literal guards,
  the projection table — is proved monotone here.
* `ReaderRun` + `annotateCore_envExt_of_readerRun` — THE READER-BRANCH
  CASE, with no hypothesis at all beyond the extension.  A run that
  never leaves the head reader (no `letE`, no `proj`, no inference
  fallback at a binder) transports unconditionally, because every
  environment lookup it makes is on the `some` branch of its own
  answer.  `ReaderRun` is a derivation, stronger than the run
  (`ReaderRun.annotateCore` turns it into one at every mode) by
  exactly the fallbacks it forbids.

  This is the form a copy's former actually needs: a telescope's every
  codomain is a `∀` or a `Sort`, and the reader answers both by `rfl`
  (`typeSortPW_forallE`, `typeSortPW_sort`, `Verify/Inductives/
  CopyTypes.lean`); only the parameter and index DOMAINS can carry a
  redex- or `proj`-headed binder, and that is precisely K.4's frontier.

**(b) The minted former's telescope ends in a sort.**
`mkCopy_type_stripPis_sort` / `auxIdxCount_mkCopy` /
`mkCopy_checkSumTele_keeps`: level instantiation, `instPis` at the
pin's components and `closeTelescope` over the block's parameter
binders are all congruences on `∀` that leave a `Sort` residual a
`Sort`, so the container's telescope shape is inherited by the copy —
`auxIdxCount` reads `nIdx` back off `piBinders`, the annotation pass
preserves the shape (`annotateCore_stripPis_sort`), and
`checkSumTele`'s first branch fires and keeps the annotated constant.

**Off the build graph**, like the other nested Verify modules
(`Verify/Inductives/CopyTypes.lean`): nothing in `ConLeche.lean`'s cone
imports it yet, so it is built explicitly
(`lake build ConLeche.Verify.Inductives.AuxFormers`).
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
@[expose] def SlotsExt (mode : CheckMode) (env env' : Env) : Prop :=
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
@[expose] def ReaderNoNew (env env' : Env) : Prop :=
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

/-! ## The reader-only fragment: the transfer with no missing ingredient

`SlotsExt` and `ReaderNoNew` are needed only where the pass leaves the
head reader: the `letE` and `proj` clauses, and a binder whose parse
placeholder the reader declines.  A run that never does that transports
along ANY conservative extension, with nothing assumed — and that is
the run a minted copy's former has (its telescope's every codomain is a
`∀` or a `Sort`, both of which the reader answers by `rfl`).

`ReaderRun env F d e r` is that run, spelled as a derivation: it is
*stronger* than `annotateCore mode env F d e = .ok r`
(`ReaderRun.annotateCore`) by exactly the fallbacks it forbids, and it
mentions no `CheckMode`, because none of the clauses it keeps does.
-/

/-- **A reader-only annotation run**: `e` annotates to `r` at depth `d`
with fuel `F`, using the head reader for every recomputed binder datum
and never `letE`, `proj` or inference. -/
inductive ReaderRun (env : Env) : Nat → Nat → Expr → Expr → Prop where
  | bvar {F d i} : ReaderRun env (F + 1) d (.bvar i) (.bvar i)
  | fvar {F d idx ty} : idx < d →
      ReaderRun env (F + 1) d (.fvar idx ty) (.fvar idx ty)
  | sort {F d u} : ReaderRun env (F + 1) d (.sort u) (.sort u)
  | const {F d n us} : ReaderRun env (F + 1) d (.const n us) (.const n us)
  | natLit {F d n} : natLitSupported env = true →
      ReaderRun env (F + 1) d (.lit (.natVal n)) (.lit (.natVal n))
  | strLit {F d s} : strLitSupported env = true →
      ReaderRun env (F + 1) d (.lit (.strVal s)) (.lit (.strVal s))
  | app {F d f a f' a'} : ReaderRun env F d f f' → ReaderRun env F d a a' →
      ReaderRun env (F + 1) d (.app f a) (.app f' a')
  | forallE {F d : Nat} {ty body ty' body' : Expr} {m : BinderMeta} {pw : PropWhen} :
      ReaderRun env F d ty ty' →
      ReaderRun env F (d + 1) (body.instantiate1 (.fvar d ty')) body' →
      (pwWritten m.pw = true ∧ pw = m.pw ∨
        pwWritten m.pw = false ∧ typeSortPW env.find? body' = some pw) →
      ReaderRun env (F + 1) d (.forallE ty body m)
        (.forallE ty' (body'.abstract1 d) ⟨pw⟩)
  | lam {F d : Nat} {ty body ty' body' : Expr} {m : BinderMeta} {pw : PropWhen} :
      ReaderRun env F d ty ty' →
      ReaderRun env F (d + 1) (body.instantiate1 (.fvar d ty')) body' →
      (pwWritten m.pw = true ∧ pw = m.pw ∨
        pwWritten m.pw = false ∧ proofPW env.find? body' = some pw) →
      ReaderRun env (F + 1) d (.lam ty body m)
        (.lam ty' (body'.abstract1 d) ⟨pw⟩)

/-- A reader-only run tolerates more fuel (the pass's own
`annotateCore_mono`, at the derivation). -/
theorem ReaderRun.mono {env : Env} : ∀ {F d e r}, ReaderRun env F d e r →
    ∀ {F' : Nat}, F ≤ F' → ReaderRun env F' d e r := by
  intro F d e r h
  induction h with
  | bvar => intro F' hle; cases F' with
    | zero => omega
    | succ f => exact .bvar
  | fvar hd => intro F' hle; cases F' with
    | zero => omega
    | succ f => exact .fvar hd
  | sort => intro F' hle; cases F' with
    | zero => omega
    | succ f => exact .sort
  | const => intro F' hle; cases F' with
    | zero => omega
    | succ f => exact .const
  | natLit hn => intro F' hle; cases F' with
    | zero => omega
    | succ f => exact .natLit hn
  | strLit hn => intro F' hle; cases F' with
    | zero => omega
    | succ f => exact .strLit hn
  | app _ _ ihf iha => intro F' hle; cases F' with
    | zero => omega
    | succ f => exact .app (ihf (by omega)) (iha (by omega))
  | forallE _ _ hpw iht ihb => intro F' hle; cases F' with
    | zero => omega
    | succ f => exact .forallE (iht (by omega)) (ihb (by omega)) hpw
  | lam _ _ hpw iht ihb => intro F' hle; cases F' with
    | zero => omega
    | succ f => exact .lam (iht (by omega)) (ihb (by omega)) hpw

/-- **A reader-only run IS an annotation run** — at every mode: the
clauses are the pass's own, with the fallbacks forbidden. -/
theorem ReaderRun.annotateCore {env : Env} : ∀ {F d e r}, ReaderRun env F d e r →
    annotateCore mode env F d e = .ok r := by
  intro F d e r h
  induction h with
  | bvar => rfl
  | fvar hd =>
    rw [annotateCore_succ]
    simp only [annotateBody]
    rw [if_pos hd]
    rfl
  | sort => rfl
  | const => rfl
  | natLit hn =>
    rw [annotateCore_succ]
    simp only [annotateBody]
    rw [if_pos hn]
    rfl
  | strLit hn =>
    rw [annotateCore_succ]
    simp only [annotateBody]
    rw [if_pos hn]
    rfl
  | app _ _ ihf iha =>
    rw [annotateCore_succ]
    simp only [annotateBody, Bind.bind, Except.bind, annotate_def]
    rw [ihf]
    dsimp only
    rw [iha]
    rfl
  | forallE _ _ hpw iht ihb =>
    rw [annotateCore_succ]
    simp only [annotateBody, Bind.bind, Except.bind, annotate_def]
    rw [iht]
    dsimp only
    rw [ihb]
    dsimp only
    rcases hpw with ⟨hw, rfl⟩ | ⟨hnw, hrd⟩
    · rw [hw]; rfl
    · rw [hnw, annotPwPi_of_reader hrd]; rfl
  | lam _ _ hpw iht ihb =>
    rw [annotateCore_succ]
    simp only [annotateBody, Bind.bind, Except.bind, annotate_def]
    rw [iht]
    dsimp only
    rw [ihb]
    dsimp only
    rcases hpw with ⟨hw, rfl⟩ | ⟨hnw, hrd⟩
    · rw [hw]; rfl
    · rw [hnw, annotPwLam_of_reader hrd]; rfl

/-- **LEMMA (a), the reader-branch case — no missing ingredient.**  A
reader-only run survives any conservative extension: the readers'
answers do (`typeSortPW_envExt`, `proofPW_envExt`), the literal guards
do, and nothing else is consulted. -/
theorem ReaderRun.envExt {env env' : Env} (hext : EnvExt env env') :
    ∀ {F d e r}, ReaderRun env F d e r → ReaderRun env' F d e r := by
  intro F d e r h
  induction h with
  | bvar => exact .bvar
  | fvar hd => exact .fvar hd
  | sort => exact .sort
  | const => exact .const
  | natLit hn => exact .natLit (natLitSupported_envExt hext hn)
  | strLit hn => exact .strLit (strLitSupported_envExt hext hn)
  | app _ _ ihf iha => exact .app ihf iha
  | forallE _ _ hpw iht ihb =>
    refine .forallE iht ihb ?_
    rcases hpw with ⟨hw, rfl⟩ | ⟨hnw, hrd⟩
    · exact Or.inl ⟨hw, rfl⟩
    · exact Or.inr ⟨hnw, typeSortPW_envExt hext hrd⟩
  | lam _ _ hpw iht ihb =>
    refine .lam iht ihb ?_
    rcases hpw with ⟨hw, rfl⟩ | ⟨hnw, hrd⟩
    · exact Or.inl ⟨hw, rfl⟩
    · exact Or.inr ⟨hnw, proofPW_envExt hext hrd⟩

/-- **The reader-branch transfer, assembled.**  The same annotation, at
the smaller environment and at every conservative extension of it, with
no hypothesis beyond the extension. -/
theorem annotateCore_envExt_of_readerRun {env env' : Env} (hext : EnvExt env env')
    {F d : Nat} {e r : Expr} (h : ReaderRun env F d e r) :
    annotateCore mode env F d e = .ok r ∧
      annotateCore mode env' F d e = .ok r :=
  ⟨h.annotateCore, (h.envExt hext).annotateCore⟩

/-! ### The derivation is inhabited

A two-binder witness, so that `ReaderRun` is not a predicate no term
satisfies: the smallest former shape, `∀ (_ : Type), Prop`, whose
codomain the reader answers by `rfl` — which is what every copy's
telescope node looks like. -/

example (env : Env) : ReaderRun env 2 0
    (.forallE (.sort (.succ .zero)) (.sort .zero) ⟨.never⟩)
    (.forallE (.sort (.succ .zero)) (.sort .zero) ⟨.never⟩) :=
  ReaderRun.forallE (body' := .sort .zero) .sort .sort (Or.inr ⟨by simp [pwWritten], rfl⟩)

example (env : Env) (mode : CheckMode) :
    annotateCore mode env 2 0
        (.forallE (.sort (.succ .zero)) (.sort .zero) ⟨.never⟩)
      = .ok (.forallE (.sort (.succ .zero)) (.sort .zero) ⟨.never⟩) :=
  ReaderRun.annotateCore
    (ReaderRun.forallE (body' := .sort .zero) .sort .sort (Or.inr ⟨by simp [pwWritten], rfl⟩))

/-! ## LEMMA (b): the minted former's telescope ends in a sort

`checkSumTele`'s first branch (`Kernel/Inductives/SumInstall.lean`)
fires exactly when the declared type is ALREADY a syntactic telescope
of `nP + nIdx` `∀`s ending in a sort — and then it keeps the annotated
constant untouched, which is what `AuxFormersAnnot` asserts.  A copy
minted by `mkCopy` always is such a telescope, because the container's
stored former is one and neither level instantiation, nor `instPis` at
the pin's components, nor `closeTelescope` over the block's parameter
binders can disturb the shape: all three are congruences on `∀` that
leave a `Sort` residual a `Sort`.

The four closure lemmas below are the whole content; `auxIdxCount` then
reads the index count back off `piBinders`, which a sort-terminated
`stripPis` pins exactly.
-/

/-- A `∀`-telescope ending in a sort survives level instantiation. -/
theorem stripPis_sort_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {u : Level},
      e.stripPis k = some (bs, .sort u) →
      ∃ bs', (e.instantiateLevelParams ks us).stripPis k
        = some (bs', .sort (Level.subst ks us u)) := by
  intro k
  induction k with
  | zero =>
    intro e bs u h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], rfl⟩
  | succ k ih =>
    intro e bs u h
    cases e with
    | forallE ty body m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs0, r0⟩, h0, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨bs', hbs'⟩ := ih h0
      refine ⟨(ty.instantiateLevelParams ks us, ⟨Level.substPW ks us m.pw⟩) :: bs', ?_⟩
      simp only [Expr.instantiateLevelParams, Expr.stripPis, hbs', Option.map_some]
    | _ => simp only [Expr.stripPis] at h; exact nomatch h

/-- A `∀`-telescope ending in a sort survives substitution. -/
theorem stripPis_sort_instantiate1 (v : Expr) :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {u : Level} {j : Nat},
      e.stripPis k = some (bs, .sort u) →
      ∃ bs', (e.instantiate1 v j).stripPis k = some (bs', .sort u) := by
  intro k
  induction k with
  | zero =>
    intro e bs u j h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], rfl⟩
  | succ k ih =>
    intro e bs u j h
    cases e with
    | forallE ty body m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs0, r0⟩, h0, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨bs', hbs'⟩ := ih (j := j + 1) h0
      refine ⟨(ty.instantiate1 v j, m) :: bs', ?_⟩
      simp only [Expr.instantiate1, Expr.stripPis, hbs', Option.map_some]
    | _ => simp only [Expr.stripPis] at h; exact nomatch h

/-- A `∀`-telescope ending in a sort survives abstraction. -/
theorem stripPis_sort_abstract1 :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {u : Level} {d j : Nat},
      e.stripPis k = some (bs, .sort u) →
      ∃ bs', (e.abstract1 d j).stripPis k = some (bs', .sort u) := by
  intro k
  induction k with
  | zero =>
    intro e bs u d j h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], rfl⟩
  | succ k ih =>
    intro e bs u d j h
    cases e with
    | forallE ty body m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs0, r0⟩, h0, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨bs', hbs'⟩ := ih (d := d) (j := j + 1) h0
      refine ⟨(ty.abstract1 d j, m) :: bs', ?_⟩
      simp only [Expr.abstract1, Expr.stripPis, hbs', Option.map_some]
    | _ => simp only [Expr.stripPis] at h; exact nomatch h

/-- Instantiating the leading binders of a sort-terminated telescope
succeeds and leaves a shorter sort-terminated telescope. -/
theorem stripPis_sort_instPis :
    ∀ (as : List Expr) {e : Expr} {k : Nat} {bs : List (Expr × BinderMeta)} {u : Level},
      e.stripPis (as.length + k) = some (bs, .sort u) →
      ∃ t bs', Expr.instPis e as = some t ∧ t.stripPis k = some (bs', .sort u) := by
  intro as
  induction as with
  | nil =>
    intro e k bs u h
    simp only [List.length_nil, Nat.zero_add] at h
    exact ⟨e, bs, rfl, h⟩
  | cons a as ih =>
    intro e k bs u h
    cases e with
    | forallE ty body m =>
      have hlen : (a :: as).length + k = (as.length + k) + 1 := by
        simp only [List.length_cons]; omega
      rw [hlen] at h
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs0, r0⟩, h0, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      obtain ⟨bs1, hbs1⟩ := stripPis_sort_instantiate1 a (as.length + k) (j := 0) h0
      obtain ⟨t, bs', ht, hst⟩ := ih hbs1
      exact ⟨t, bs', ht, hst⟩
    | _ =>
      have hlen : (a :: as).length + k = (as.length + k) + 1 := by
        simp only [List.length_cons]; omega
      rw [hlen] at h
      simp only [Expr.stripPis] at h
      exact nomatch h

/-- Closing a sort-terminated telescope over a parameter prefix leaves
a sort-terminated telescope, longer by the prefix. -/
theorem stripPis_sort_closeTelescope :
    ∀ (pbs : List (Expr × BinderMeta)) {i : Nat} {t : Expr} {k : Nat}
      {bs : List (Expr × BinderMeta)} {u : Level},
      t.stripPis k = some (bs, .sort u) →
      ∃ bs', (closeTelescope pbs i t).stripPis (pbs.length + k)
        = some (bs', .sort u) := by
  intro pbs
  induction pbs with
  | nil =>
    intro i t k bs u h
    simp only [List.length_nil, Nat.zero_add, closeTelescope]
    exact ⟨bs, h⟩
  | cons pb pbs ih =>
    intro i t k bs u h
    obtain ⟨bs0, hbs0⟩ := ih (i := i + 1) (t := t) (k := k) h
    obtain ⟨bs1, hbs1⟩ := stripPis_sort_abstract1 (pbs.length + k) (d := i) (j := 0) hbs0
    refine ⟨(pb.1, pb.2) :: bs1, ?_⟩
    have hlen : (pb :: pbs).length + k = (pbs.length + k) + 1 := by
      simp only [List.length_cons]; omega
    rw [hlen]
    simp only [closeTelescope, Expr.stripPis, hbs1, Option.map_some]

/-- A sort-terminated `stripPis` pins `piBinders` exactly: the residual
is not a `∀`, so the greedy walk stops at the same place. -/
theorem piBinders_of_stripPis_sort :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)} {u : Level},
      e.stripPis k = some (bs, .sort u) → e.piBinders = (bs, .sort u) := by
  intro k
  induction k with
  | zero =>
    intro e bs u h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ k ih =>
    intro e bs u h
    cases e with
    | forallE ty body m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs0, r0⟩, h0, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp only [Expr.piBinders, ih h0]
    | _ => simp only [Expr.stripPis] at h; exact nomatch h

/-- **LEMMA (b).**  A copy minted from a container member whose stored
former is a syntactic telescope of `Ds.length + nIdx` binders ending in
`Sort u` has, for its own type, a syntactic telescope of
`pbs.length + nIdx` binders ending in `Sort u[lvls]` — so
`auxIdxCount pbs.length` returns `nIdx` and `checkSumTele`'s first
branch fires at `pbs.length + nIdx`. -/
theorem mkCopy_type_stripPis_sort {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {auxName : Name} {J : ContainerMember} {copy : AuxType}
    {nIdx : Nat} {bs : List (Expr × BinderMeta)} {u : Level}
    (hJ : J.type.stripPis (Ds.length + nIdx) = some (bs, .sort u))
    (hmk : mkCopy pbs lvls Ds auxName J = .ok copy) :
    ∃ bs', copy.type.stripPis (pbs.length + nIdx)
      = some (bs', .sort (Level.subst J.lps lvls u)) := by
  obtain ⟨bsL, hbsL⟩ := stripPis_sort_instantiateLevelParams J.lps lvls _ hJ
  obtain ⟨tyI, bsI, htyI, hstI⟩ := stripPis_sort_instPis Ds hbsL
  obtain ⟨bs', hbs'⟩ := stripPis_sort_closeTelescope pbs (i := 0) hstI
  refine ⟨bs', ?_⟩
  -- the mint's own value of `tyI` is this one
  unfold mkCopy at hmk
  simp only [bind, Except.bind] at hmk
  split at hmk
  case isFalse => simp at hmk
  case isTrue =>
    rw [htyI] at hmk
    dsimp only at hmk
    split at hmk
    all_goals simp only [pure, Except.pure, reduceCtorEq, Except.ok.injEq] at hmk
    rw [← hmk]
    exact hbs'

/-- The index count the auxiliary block records for a minted copy. -/
theorem auxIdxCount_mkCopy {pbs : List (Expr × BinderMeta)} {lvls : List Level}
    {Ds : List Expr} {auxName : Name} {J : ContainerMember} {copy : AuxType}
    {nIdx : Nat} {bs : List (Expr × BinderMeta)} {u : Level}
    (hJ : J.type.stripPis (Ds.length + nIdx) = some (bs, .sort u))
    (hmk : mkCopy pbs lvls Ds auxName J = .ok copy) :
    auxIdxCount pbs.length copy.type = some nIdx := by
  obtain ⟨bs', hbs'⟩ := mkCopy_type_stripPis_sort hJ hmk
  have hpb := piBinders_of_stripPis_sort _ hbs'
  have hlen : bs'.length = pbs.length + nIdx := stripPis_length _ hbs'
  simp only [auxIdxCount, hpb, hlen]
  rw [if_pos (Nat.le_add_right _ _)]
  simp

/-! ### From the mint to `checkSumTele`'s first branch -/

/-- **The annotation pass preserves a sort-terminated telescope**, with
the sort on the nose: a `∀` node is rebuilt as a `∀`, a `Sort` node is
returned unchanged, and neither the opening at the binder's free
variable nor the closing abstraction can turn the residual into
anything else. -/
theorem annotateCore_stripPis_sort {env : Env} :
    ∀ (k F d : Nat) {e r : Expr} {bs : List (Expr × BinderMeta)} {u : Level},
      annotateCore mode env F d e = .ok r →
      e.stripPis k = some (bs, .sort u) →
      ∃ bs', r.stripPis k = some (bs', .sort u) := by
  intro k
  induction k with
  | zero =>
    intro F d e r bs u h hs
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, rfl⟩ := hs
    cases F with
    | zero =>
      rw [annotateCore_zero] at h
      simp only [throw, throwThe, MonadExceptOf.throw] at h
      exact nomatch h
    | succ f =>
      rw [annotateCore_succ] at h
      simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨[], by rw [← h]; rfl⟩
  | succ k ih =>
    intro F d e r bs u h hs
    cases e with
    | forallE ty body m =>
      simp only [Expr.stripPis, Option.map_eq_some_iff] at hs
      obtain ⟨⟨bs0, r0⟩, h0, heq⟩ := hs
      simp only [Prod.mk.injEq] at heq
      obtain ⟨-, rfl⟩ := heq
      cases F with
      | zero =>
        rw [annotateCore_zero] at h
        simp only [throw, throwThe, MonadExceptOf.throw] at h
        exact nomatch h
      | succ f =>
        obtain ⟨ty', body', pw, -, hbody, rfl⟩ := annotateCore_forallE_inv h
        obtain ⟨bs1, hbs1⟩ :=
          stripPis_sort_instantiate1 (.fvar d ty') k (j := 0) h0
        obtain ⟨bs2, hbs2⟩ := ih f (d + 1) hbody hbs1
        obtain ⟨bs3, hbs3⟩ := stripPis_sort_abstract1 k (d := d) (j := 0) hbs2
        exact ⟨(ty', ⟨pw⟩) :: bs3, by
          simp only [Expr.stripPis, hbs3, Option.map_some]⟩
    | _ => simp only [Expr.stripPis] at hs; exact nomatch hs

/-- **`checkSumTele`'s first branch fires**: an already-syntactic
telescope of `n` binders ending in a sort is kept as it is, and the
result sort is the residual's.  This is the step that makes the
auxiliary install *keep the annotated type* — the premise
`AuxFormersAnnot` states. -/
theorem checkSumTele_of_stripPis_sort {m : Type → Type} [Monad m]
    [MonadExceptOf CheckError m] (ops : CheckerOps m) (env : Env)
    (cv : ConstantVal) (n : Nat) (cvTa₀ : ConstantVal)
    {bs : List (Expr × BinderMeta)} {s : Level}
    (h : cvTa₀.type.stripPis n = some (bs, .sort s)) :
    checkSumTele ops env cv n cvTa₀ = pure (cvTa₀, s) := by
  unfold checkSumTele
  rw [h]

/-- **LEMMA (b), assembled.**  A copy minted from a container member
whose stored former is a `Ds.length + nIdx` telescope ending in a sort
reaches the auxiliary install's former stage with an ALREADY-syntactic
telescope — before annotation (`auxIdxCount` reads `nIdx` back) and
after it (`annotateCore_stripPis_sort`) — so `checkSumTele` keeps the
annotated constant and the stored former IS the annotation of the
minted type. -/
theorem mkCopy_checkSumTele_keeps {env : Env} {pbs : List (Expr × BinderMeta)}
    {lvls : List Level} {Ds : List Expr} {auxName : Name} {J : ContainerMember}
    {copy : AuxType} {nIdx F d : Nat} {bs : List (Expr × BinderMeta)} {u : Level}
    {cv cvTa₀ : ConstantVal}
    (hJ : J.type.stripPis (Ds.length + nIdx) = some (bs, .sort u))
    (hmk : mkCopy pbs lvls Ds auxName J = .ok copy)
    (hann : annotateCore mode env F d copy.type = .ok cvTa₀.type)
    {m : Type → Type} [Monad m] [MonadExceptOf CheckError m] (ops : CheckerOps m) :
    auxIdxCount pbs.length copy.type = some nIdx ∧
      ∃ s, checkSumTele ops env cv (pbs.length + nIdx) cvTa₀ = pure (cvTa₀, s) := by
  refine ⟨auxIdxCount_mkCopy hJ hmk, ?_⟩
  obtain ⟨bs', hbs'⟩ := mkCopy_type_stripPis_sort hJ hmk
  obtain ⟨bs'', hbs''⟩ := annotateCore_stripPis_sort (mode := mode) _ F d hann hbs'
  exact ⟨_, checkSumTele_of_stripPis_sort ops env cv _ cvTa₀ hbs''⟩

/-! ## What the model lane consumes

`AuxFormersAnnot`'s three conjuncts for ONE copy, from the mint, the
container's telescope, the pre-block annotation run and the extension.
The bvar-closedness and fvar-freedom of the minted type are the mint's
own business (the elimination's `nestedOccOk` and `pinsClosed` ledger
entries) and stay with the model lane; what is discharged here is the
annotation equation and the telescope shape the install's first branch
tests. -/
theorem auxFormerAnnot_of_readerRun {env envAux : Env} (hext : EnvExt env envAux)
    {pbs : List (Expr × BinderMeta)} {lvls : List Level} {Ds : List Expr}
    {auxName : Name} {J : ContainerMember} {copy : AuxType} {cvT : ConstantVal}
    {nIdx F : Nat} {bs : List (Expr × BinderMeta)} {u : Level}
    (hJ : J.type.stripPis (Ds.length + nIdx) = some (bs, .sort u))
    (hmk : mkCopy pbs lvls Ds auxName J = .ok copy)
    (hrun : ReaderRun env F 0 copy.type cvT.type) :
    annotateCore mode env F 0 copy.type = .ok cvT.type ∧
      annotateCore mode envAux F 0 copy.type = .ok cvT.type ∧
      auxIdxCount pbs.length copy.type = some nIdx ∧
      ∃ bs' : List (Expr × BinderMeta),
        cvT.type.stripPis (pbs.length + nIdx)
          = some (bs', .sort (Level.subst J.lps lvls u)) := by
  obtain ⟨h₁, h₂⟩ := annotateCore_envExt_of_readerRun (mode := mode) hext hrun
  refine ⟨h₁, h₂, auxIdxCount_mkCopy hJ hmk, ?_⟩
  obtain ⟨bs', hbs'⟩ := mkCopy_type_stripPis_sort hJ hmk
  exact annotateCore_stripPis_sort (mode := mode) _ F 0 h₁ hbs'

end ConLeche
