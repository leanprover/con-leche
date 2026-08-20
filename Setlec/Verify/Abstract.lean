import Setlec.Kernel.TypeChecker
import Setlec.Verify.Knot
import Setlec.Verify.Shift

/-!
# Abstraction and the open/close roundtrip

`annotate` opens each binder, processes the body, and re-closes it with
`abstract1`.  The lemmas here make that roundtrip exact:

* `fvarConsistent d n ty e`: every reachable `fvar d` leaf is exactly
  `fvar d n ty` — true of any opened body and preserved by `annotate`;
* `abstract1_instantiate1`: closing then re-opening is the identity,
  given consistency and no loose bound variables;
* scoping and loose-bvar bookkeeping for `abstract1`/`instantiate1` and
  their preservation through `annotate`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Setlec

open Expr

/-- Every reachable `fvar` leaf with index `d` is exactly `fvar d n ty`. -/
def Expr.fvarConsistent (d : Nat) (n : Name) (ty : Expr) : Expr → Prop
  | .fvar idx n' ty' => idx = d → n' = n ∧ ty' = ty
  | .app f a => fvarConsistent d n ty f ∧ fvarConsistent d n ty a
  | .lam _ t b _ | .forallE _ t b _ => fvarConsistent d n ty t ∧ fvarConsistent d n ty b
  | .letE _ t v b => fvarConsistent d n ty t ∧ fvarConsistent d n ty v ∧ fvarConsistent d n ty b
  | .proj _ _ e => fvarConsistent d n ty e
  | _ => True

/-- Closing then re-opening a binder body is the identity. -/
theorem abstract1_instantiate1 {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), fvarConsistent d n ty e → e.looseBVarsBounded k = true →
      (e.abstract1 d k).instantiate1 (.fvar d n ty) k = e := by
  intro e
  induction e <;> intro k hc hb <;>
    simp_all [Expr.fvarConsistent, Expr.looseBVarsBounded, Expr.abstract1, Expr.instantiate1]
  case bvar i =>
    have h1 : ¬ (i = k) := by omega
    have h2 : ¬ (i > k) := by omega
    simp [h1, h2]
  case fvar idx n' ty' ih =>
    by_cases hidx : idx = d
    · obtain ⟨rfl, rfl⟩ := hc hidx
      simp [hidx, Expr.instantiate1]
    · simp [hidx, Expr.instantiate1]

/-- Abstracting away the top variable lowers the scope bound. -/
theorem WScoped.abstract1 {d : Nat} :
    ∀ {e : Expr} (k : Nat), WScoped (d + 1) e → WScoped d (e.abstract1 d k) := by
  intro e
  induction e <;> intro k hw <;>
    simp_all [Expr.abstract1, WScoped]
  case fvar idx n' ty' ih =>
    by_cases hidx : idx = d
    · simp [hidx, WScoped]
    · simp only [hidx, if_false, WScoped]
      exact ⟨by omega, hw.2⟩

/-- Opening establishes consistency: a body free of `fvar d` opened with
`fvar d n ty` mentions it consistently. -/
theorem fvarConsistent_instantiate1 {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), fvarsBelow d e →
      fvarConsistent d n ty (e.instantiate1 (.fvar d n ty) k) := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.instantiate1, fvarsBelow, Expr.fvarConsistent]
  case bvar i =>
    split
    · simp [Expr.fvarConsistent]
    · split <;> simp [Expr.fvarConsistent]
  case fvar idx n' ty' ih =>
    omega

/-- Consistency at `d` survives opening with a *different* index. -/
theorem fvarConsistent_instantiate1' {d d' : Nat} {n n' : Name} {ty ty' : Expr}
    (hne : d ≠ d') :
    ∀ (e : Expr) (k : Nat), fvarConsistent d n ty e →
      fvarConsistent d n ty (e.instantiate1 (.fvar d' n' ty') k) := by
  intro e
  induction e <;> intro k hc <;>
    simp_all [Expr.instantiate1, Expr.fvarConsistent]
  case bvar i =>
    split
    · simp [Expr.fvarConsistent]
      intro h
      exact absurd h.symm hne
    · split <;> simp [Expr.fvarConsistent]

/-- Consistency at `d` survives abstracting a *different* index. -/
theorem fvarConsistent_abstract1 {d d' : Nat} {n : Name} {ty : Expr}
    (hne : d ≠ d') :
    ∀ (e : Expr) (k : Nat), fvarConsistent d n ty e →
      fvarConsistent d n ty (e.abstract1 d' k) := by
  intro e
  induction e <;> intro k hc <;>
    simp_all [Expr.abstract1, Expr.fvarConsistent]
  case fvar idx n'' ty'' ih =>
    split
    · simp [Expr.fvarConsistent]
    · simpa [Expr.fvarConsistent] using hc

/-- Opening lowers the loose-bvar bound by one. -/
theorem looseBVarsBounded_instantiate1 {d : Nat} {n : Name} {ty : Expr} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded (k + 1) = true →
      (e.instantiate1 (.fvar d n ty) k).looseBVarsBounded k = true := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.instantiate1, Expr.looseBVarsBounded]
  case bvar i =>
    split
    · simp [Expr.looseBVarsBounded]
    · split <;> simp [Expr.looseBVarsBounded] <;> omega

/-- Abstracting raises the loose-bvar bound by one. -/
theorem looseBVarsBounded_abstract1 {d : Nat} :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded k = true →
      (e.abstract1 d k).looseBVarsBounded (k + 1) = true := by
  intro e
  induction e <;> intro k hb <;>
    simp_all [Expr.abstract1, Expr.looseBVarsBounded]
  case bvar i => omega
  case fvar idx n' ty' ih =>
    split <;> simp [Expr.looseBVarsBounded] <;> omega

/-! ## Preservation through `annotate` -/

/-- Inversion for the projection-elimination path: the structure and
its installed projection function were resolved, the scope guard
passed, and the rewrite re-annotated. -/
theorem annotateProjElim_inv {env : Env} {fuel d : Nat} {sn : Name}
    {i : Nat} {te e₂ e' : Expr}
    (h : annotateProjElimP env fuel d sn i te e₂ = .ok e') :
    ∃ us pcv nP nM nm ni rules,
      te.getAppFn = .const sn us ∧
      env.find? (projFnName sn i) =
        some (.recInfo pcv nP nM nm ni rules) ∧
      te.getAppArgs.length = nP ∧
      (Expr.mkAppN (.const (projFnName sn i) us)
        (te.getAppArgs ++ [e₂])).wscopedB d = true ∧
      (Expr.mkAppN (.const (projFnName sn i) us)
        (te.getAppArgs ++ [e₂])).looseBVarsBounded 0 = true ∧
      (Expr.mkAppN (.const (projFnName sn i) us)
        (te.getAppArgs ++ [e₂])).fvarLeaves.all
        (fun l => e₂.fvarLeaves.contains l) = true ∧
      annotateCore env fuel d
        (Expr.mkAppN (.const (projFnName sn i) us)
          (te.getAppArgs ++ [e₂])) = .ok e' := by
  simp only [annotateProjElimP, annotateProjElim] at h
  revert h
  match hfn : te.getAppFn with
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ _ _ => intro h; exact nomatch h
  | .forallE _ _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  | .const T us => ?_
  intro h
  dsimp only at h
  by_cases hT : T = sn
  case neg => rw [if_neg hT] at h; exact nomatch h
  rw [if_pos hT] at h
  subst hT
  try dsimp only at h
  revert h
  match hfp : env.find? (projFnName T i) with
  | none => intro h; exact nomatch h
  | some (.axiomInfo _) => intro h; exact nomatch h
  | some (.defnInfo _ _) => intro h; exact nomatch h
  | some (.thmInfo _ _) => intro h; exact nomatch h
  | some (.indInfo _ _) => intro h; exact nomatch h
  | some (.ctorInfo _ _ _) => intro h; exact nomatch h
  | some (.recInfo pcv nP nM nm ni rules) => ?_
  intro h
  dsimp only at h
  by_cases hlen : te.getAppArgs.length = nP
  case neg => rw [if_neg hlen] at h; exact nomatch h
  rw [if_pos hlen] at h
  try dsimp only at h
  by_cases hg : ((Expr.mkAppN (.const (projFnName T i) us)
      (te.getAppArgs ++ [e₂])).wscopedB d &&
      (Expr.mkAppN (.const (projFnName T i) us)
        (te.getAppArgs ++ [e₂])).looseBVarsBounded 0 &&
      (Expr.mkAppN (.const (projFnName T i) us)
        (te.getAppArgs ++ [e₂])).fvarLeaves.all
        (fun l => e₂.fvarLeaves.contains l)) = true
  · rw [if_pos hg] at h
    simp only [Bool.and_eq_true] at hg
    exact ⟨us, pcv, nP, nM, nm, ni, rules, rfl, rfl, hlen,
      hg.1.1, hg.1.2, hg.2, h⟩
  · rw [if_neg hg] at h
    exact nomatch h

/-- Inversion for `annotate` on projections: either the native basis
pair rule ran, or the projection was eliminated through a recursor. -/
theorem annotateCore_proj_inv {env : Env} {fuel d : Nat} {sn : Name}
    {i : Nat} {e e' : Expr}
    (h : annotateCore env (fuel + 1) d (.proj sn i e) = .ok e') :
    ∃ e₂ tt te, annotateCore env fuel d e = .ok e₂ ∧
      inferTypeCore env fuel d e₂ = .ok tt ∧ whnf env fuel d tt = .ok te ∧
      ((∃ us A B cv caps, te = .app (.app (.const psigmaName us) A) B ∧
          env.find? psigmaName = some (.indInfo cv caps) ∧
          i < 2 ∧ e' = .proj sn i e₂) ∨
        annotateProjElimP env fuel d sn i te e₂ = .ok e') := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def, infer_def, whnf_def] at h
  cases he : annotateCore env fuel d e with
  | error err => rw [he] at h; exact nomatch h
  | ok e₂ =>
  rw [he] at h
  dsimp only at h
  cases hte : inferTypeCore env fuel d e₂ with
  | error err => rw [hte] at h; exact nomatch h
  | ok tt =>
  rw [hte] at h
  dsimp only at h
  cases hw : whnf env fuel d tt with
  | error err => rw [hw] at h; exact nomatch h
  | ok te =>
  rw [hw] at h
  dsimp only at h
  refine ⟨e₂, tt, te, rfl, hte, hw, ?_⟩
  revert h
  match te with
  | .app (.app (.const c us) A) B => ?_
  | .sort u => intro h; exact Or.inr h
  | .fvar i2 n2 t2 => intro h; exact Or.inr h
  | .const n2 us2 => intro h; exact Or.inr h
  | .lam n2 t2 b2 m2 => intro h; exact Or.inr h
  | .forallE n2 t2 b2 m2 => intro h; exact Or.inr h
  | .bvar i2 => intro h; exact Or.inr h
  | .letE n2 t2 v2 b2 => intro h; exact Or.inr h
  | .lit l2 => intro h; exact Or.inr h
  | .proj s2 i2 e2 => intro h; exact Or.inr h
  | .app (.app (.app f3 a3) A) B => intro h; exact Or.inr h
  | .app (.app (.sort u3) A) B => intro h; exact Or.inr h
  | .app (.app (.fvar i3 n3 t3) A) B => intro h; exact Or.inr h
  | .app (.app (.lam n3 t3 b3 m3) A) B => intro h; exact Or.inr h
  | .app (.app (.forallE n3 t3 b3 m3) A) B => intro h; exact Or.inr h
  | .app (.app (.bvar i3) A) B => intro h; exact Or.inr h
  | .app (.app (.letE n3 t3 v3 b3) A) B => intro h; exact Or.inr h
  | .app (.app (.lit l3) A) B => intro h; exact Or.inr h
  | .app (.app (.proj s3 i3 e3) A) B => intro h; exact Or.inr h
  | .app (.sort u3) B => intro h; exact Or.inr h
  | .app (.fvar i3 n3 t3) B => intro h; exact Or.inr h
  | .app (.const n3 us3) B => intro h; exact Or.inr h
  | .app (.lam n3 t3 b3 m3) B => intro h; exact Or.inr h
  | .app (.forallE n3 t3 b3 m3) B => intro h; exact Or.inr h
  | .app (.bvar i3) B => intro h; exact Or.inr h
  | .app (.letE n3 t3 v3 b3) B => intro h; exact Or.inr h
  | .app (.lit l3) B => intro h; exact Or.inr h
  | .app (.proj s3 i3 e3) B => intro h; exact Or.inr h
  intro h
  dsimp only at h
  by_cases hc : c = psigmaName
  · subst hc
    rw [if_pos rfl] at h
    revert h
    match hfind : env.find? psigmaName with
    | none => intro h; exact Or.inr h
    | some (.axiomInfo cv) => intro h; exact Or.inr h
    | some (.defnInfo cv v) => intro h; exact Or.inr h
    | some (.thmInfo cv v) => intro h; exact Or.inr h
    | some (.ctorInfo cv nP nF) => intro h; exact Or.inr h
    | some (.recInfo cv nP nM nm ni rules) => intro h; exact Or.inr h
    | some (.indInfo cv _) => ?_
    intro h
    dsimp only at h
    by_cases hi : i < 2
    · simp only [hi, if_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq] at h
      exact Or.inl ⟨us, A, B, cv, _, rfl, rfl, hi, h.symm⟩
    · rw [if_neg hi] at h
      exact nomatch h
  · rw [if_neg hc] at h
    exact Or.inr h

/-- Inversion for `annotate` on applications: the two annotated subterms
are reassembled, and the application-rule check ran successfully. -/
theorem annotateCore_app_inv {env : Env} {fuel d : Nat} {f a e' : Expr}
    (h : annotateCore env (fuel + 1) d (.app f a) = .ok e') :
    ∃ f' a', annotateCore env fuel d f = .ok f' ∧
      annotateCore env fuel d a = .ok a' ∧
      e' = .app f' a' ∧
      ∃ tf n1 ty1 body1 m1 ta,
        inferTypeCore env fuel d f' = .ok tf ∧
        whnf env fuel d tf = .ok (.forallE n1 ty1 body1 m1) ∧
        inferTypeCore env fuel d a' = .ok ta ∧
        isDefEqCore env fuel d ta ty1 = .ok true := by
  rw [annotateCore_succ] at h
  simp only [annotateBody, Bind.bind, Except.bind] at h
  simp only [annotate_def, infer_def, whnf_def, defeq_def] at h
  cases hf : annotateCore env fuel d f with
  | error e => rw [hf] at h; exact nomatch h
  | ok f' =>
  rw [hf] at h; dsimp only at h
  cases ha : annotateCore env fuel d a with
  | error e => rw [ha] at h; exact nomatch h
  | ok a' =>
  rw [ha] at h; dsimp only at h
  cases hit : inferTypeCore env fuel d f' with
  | error e => rw [hit] at h; exact nomatch h
  | ok tf =>
  rw [hit] at h; dsimp only at h
  cases hwh : whnf env fuel d tf with
  | error e => rw [hwh] at h; exact nomatch h
  | ok w =>
  rw [hwh] at h; dsimp only at h
  cases w with
  | forallE n ty body m =>
    dsimp only at h
    cases hia : inferTypeCore env fuel d a' with
    | error e => rw [hia] at h; exact nomatch h
    | ok ta =>
    rw [hia] at h; dsimp only at h
    cases hde : isDefEqCore env fuel d ta ty with
    | error e => rw [hde] at h; exact nomatch h
    | ok b =>
    rw [hde] at h; dsimp only at h
    cases b with
    | true =>
      simp only [if_true, pure, Except.pure, Except.ok.injEq] at h
      exact ⟨f', a', rfl, rfl, h.symm, tf, n, ty, body, m, ta, hit, hwh, hia, hde⟩
    | false =>
      simp only [Bool.false_eq_true, if_false] at h
      exact nomatch h
  | bvar i => exact nomatch h
  | fvar i n' t' => exact nomatch h
  | sort u => exact nomatch h
  | const n' us => exact nomatch h
  | app f'' a'' => exact nomatch h
  | lam n' t' b' m' => exact nomatch h
  | letE n' t' v' b' => exact nomatch h
  | lit l' => exact nomatch h
  | proj s' i' e'' => exact nomatch h

theorem annotateCore_WScoped {env : Env} :
    ∀ (fuel : Nat) (e : Expr) {d : Nat} {e' : Expr},
      annotateCore env fuel d e = .ok e' → WScoped d e → WScoped d e'
  | 0, _, _, _, h, _ => by simp [annotateCore_zero, throw, throwThe,
      MonadExceptOf.throw] at h
  | fuel + 1, .bvar i, d, e', h, hw => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | fuel + 1, .fvar idx n ty, d, e', h, hw => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | fuel + 1, .sort u, d, e', h, hw => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | fuel + 1, .const n us, d, e', h, hw => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hw
  | fuel + 1, .lit l, d, e', h, hw => by
    rw [annotateCore_succ] at h
    match l, h with
    | .natVal n, h => ?_
    dsimp only [annotateBody] at h
    revert h
    match env.find? natName with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.defnInfo _ _) => intro h; exact nomatch h
    | some (.thmInfo _ _) => intro h; exact nomatch h
    | some (.ctorInfo _ _ _) => intro h; exact nomatch h
    | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
    | some (.indInfo _ _) =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hw
  | fuel + 1, .app f a, d, e', h, hw => by
    simp only [WScoped] at hw
    obtain ⟨f', a', hf, ha, rfl, -⟩ := annotateCore_app_inv h
    simp only [WScoped]
    exact ⟨annotateCore_WScoped fuel f hf hw.1, annotateCore_WScoped fuel a ha hw.2⟩
  | fuel + 1, .proj sn i e, d, e', h, hw => by
    simp only [WScoped] at hw
    obtain ⟨e₂, tt, te, he, -, -, hres⟩ := annotateCore_proj_inv h
    rcases hres with ⟨us, A, B, cv2, caps2, -, -, -, rfl⟩ | hel
    · simp only [WScoped]
      exact annotateCore_WScoped fuel e he hw
    · obtain ⟨us, pcv, nP, nM, nm, ni, rules, -, -, -,
        hwsb, -, -, hann⟩ := annotateProjElim_inv hel
      exact annotateCore_WScoped fuel _ hann (WScoped.of_wscopedB hwsb)
  | fuel + 1, .forallE n ty body m, d, e', h, hw => by
    simp only [WScoped] at hw
    rw [annotateCore_succ] at h
    simp only [annotateBody, Bind.bind, Except.bind] at h
    simp only [annotate_def, infer_def, ensureSort_def] at h
    cases hty : annotateCore env fuel d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    have hwty' := annotateCore_WScoped fuel ty hty hw.1
    cases hbody : annotateCore env fuel (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferTypeCore env fuel (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hes : ensureSortCore env fuel (d + 1) bt with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hwbody' := annotateCore_WScoped fuel (body.instantiate1 (.fvar d n ty')) hbody
      (hwty'.instantiate1 0 hw.2)
    simp only [WScoped]
    exact ⟨hwty', WScoped.abstract1 0 hwbody'⟩
  | fuel + 1, .lam n ty body m, d, e', h, hw => by
    simp only [WScoped] at hw
    rw [annotateCore_succ] at h
    simp only [annotateBody, Bind.bind, Except.bind] at h
    simp only [annotate_def, infer_def, ensureSort_def] at h
    cases hty : annotateCore env fuel d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    have hwty' := annotateCore_WScoped fuel ty hty hw.1
    cases hbody : annotateCore env fuel (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferTypeCore env fuel (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hit2 : inferTypeCore env fuel (d + 1) bt with
    | error e => rw [hit2] at h; exact nomatch h
    | ok bt2 =>
    rw [hit2] at h; dsimp only at h
    cases hes : ensureSortCore env fuel (d + 1) bt2 with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hwbody' := annotateCore_WScoped fuel (body.instantiate1 (.fvar d n ty')) hbody
      (hwty'.instantiate1 0 hw.2)
    simp only [WScoped]
    exact ⟨hwty', WScoped.abstract1 0 hwbody'⟩
  | fuel + 1, .letE _ _ _ _, d, e', h, _ => by
    rw [annotateCore_succ] at h
    simp [annotateBody, throw, throwThe, MonadExceptOf.throw] at h

theorem annotateCore_looseBVars {env : Env} :
    ∀ (fuel : Nat) (e : Expr) {d : Nat} {e' : Expr},
      annotateCore env fuel d e = .ok e' → e.looseBVarsBounded 0 = true →
      e'.looseBVarsBounded 0 = true
  | 0, _, _, _, h, _ => by simp [annotateCore_zero, throw, throwThe,
      MonadExceptOf.throw] at h
  | fuel + 1, .bvar i, d, e', h, hb => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | fuel + 1, .fvar idx n ty, d, e', h, hb => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | fuel + 1, .sort u, d, e', h, hb => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | fuel + 1, .const n us, d, e', h, hb => by
    rw [annotateCore_succ] at h
    simp only [annotateBody, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hb
  | fuel + 1, .lit l, d, e', h, hb => by
    rw [annotateCore_succ] at h
    match l, h with
    | .natVal n, h => ?_
    dsimp only [annotateBody] at h
    revert h
    match env.find? natName with
    | none => intro h; exact nomatch h
    | some (.axiomInfo _) => intro h; exact nomatch h
    | some (.defnInfo _ _) => intro h; exact nomatch h
    | some (.thmInfo _ _) => intro h; exact nomatch h
    | some (.ctorInfo _ _ _) => intro h; exact nomatch h
    | some (.recInfo _ _ _ _ _ _) => intro h; exact nomatch h
    | some (.indInfo _ _) =>
      intro h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact h ▸ hb
  | fuel + 1, .proj sn i e, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded] at hb
    obtain ⟨e₂, tt, te, he, -, -, hres⟩ := annotateCore_proj_inv h
    rcases hres with ⟨us, A, B, cv2, caps2, -, -, -, rfl⟩ | hel
    · simp only [Expr.looseBVarsBounded]
      exact annotateCore_looseBVars fuel e he hb
    · obtain ⟨us, pcv, nP, nM, nm, ni, rules, -, -, -,
        -, hrb, -, hann⟩ := annotateProjElim_inv hel
      exact annotateCore_looseBVars fuel _ hann hrb
  | fuel + 1, .app f a, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    obtain ⟨f', a', hf, ha, rfl, -⟩ := annotateCore_app_inv h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨annotateCore_looseBVars fuel f hf hb.1, annotateCore_looseBVars fuel a ha hb.2⟩
  | fuel + 1, .forallE n ty body m, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [annotateCore_succ] at h
    simp only [annotateBody, Bind.bind, Except.bind] at h
    simp only [annotate_def, infer_def, ensureSort_def] at h
    cases hty : annotateCore env fuel d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotateCore env fuel (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferTypeCore env fuel (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hes : ensureSortCore env fuel (d + 1) bt with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨annotateCore_looseBVars fuel ty hty hb.1, ?_⟩
    exact looseBVarsBounded_abstract1 _ 0
      (annotateCore_looseBVars fuel _ hbody (looseBVarsBounded_instantiate1 body 0 hb.2))
  | fuel + 1, .lam n ty body m, d, e', h, hb => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [annotateCore_succ] at h
    simp only [annotateBody, Bind.bind, Except.bind] at h
    simp only [annotate_def, infer_def, ensureSort_def] at h
    cases hty : annotateCore env fuel d ty with
    | error e => rw [hty] at h; exact nomatch h
    | ok ty' =>
    rw [hty] at h; dsimp only at h
    cases hbody : annotateCore env fuel (d + 1) (body.instantiate1 (.fvar d n ty')) with
    | error e => rw [hbody] at h; exact nomatch h
    | ok body' =>
    rw [hbody] at h; dsimp only at h
    cases hit : inferTypeCore env fuel (d + 1) body' with
    | error e => rw [hit] at h; exact nomatch h
    | ok bt =>
    rw [hit] at h; dsimp only at h
    cases hit2 : inferTypeCore env fuel (d + 1) bt with
    | error e => rw [hit2] at h; exact nomatch h
    | ok bt2 =>
    rw [hit2] at h; dsimp only at h
    cases hes : ensureSortCore env fuel (d + 1) bt2 with
    | error e => rw [hes] at h; exact nomatch h
    | ok v =>
    rw [hes] at h; dsimp only at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
    refine ⟨annotateCore_looseBVars fuel ty hty hb.1, ?_⟩
    exact looseBVarsBounded_abstract1 _ 0
      (annotateCore_looseBVars fuel _ hbody (looseBVarsBounded_instantiate1 body 0 hb.2))
  | fuel + 1, .letE _ _ _ _, d, e', h, _ => by
    rw [annotateCore_succ] at h
    simp [annotateBody, throw, throwThe, MonadExceptOf.throw] at h


/-! ## Leaf equivalence

`annotate`-then-`abstract1` returns a term with the same skeleton and the
same `fvar`/`bvar` leaves as the unopened input — only binder annotations
(and inner binder bodies, recursively in the same way) differ.  `LeafEquiv`
captures exactly what `FvarsOk` can see, so `FvarsOk` transports across it.
-/

/-- Same constructor skeleton and identical `fvar`/`bvar` leaves;
binder names/metadata may differ. -/
def Expr.LeafEquiv : Expr → Expr → Prop
  | .bvar i, .bvar j => i = j
  | .fvar idx n ty, .fvar idx' n' ty' => idx = idx' ∧ n = n' ∧ ty = ty'
  | .sort _, .sort _ => True
  | .const _ _, .const _ _ => True
  | .lit _, .lit _ => True
  | .app f a, .app f' a' => LeafEquiv f f' ∧ LeafEquiv a a'
  | .lam _ ty b _, .lam _ ty' b' _ => LeafEquiv ty ty' ∧ LeafEquiv b b'
  | .forallE _ ty b _, .forallE _ ty' b' _ => LeafEquiv ty ty' ∧ LeafEquiv b b'
  | .letE _ ty v b, .letE _ ty' v' b' =>
    LeafEquiv ty ty' ∧ LeafEquiv v v' ∧ LeafEquiv b b'
  | .proj _ _ e, .proj _ _ e' => LeafEquiv e e'
  | _, _ => False

theorem Expr.LeafEquiv.refl : ∀ (e : Expr), Expr.LeafEquiv e e := by
  intro e
  induction e <;> simp_all [Expr.LeafEquiv]

/-- Leaf-equivalent terms have the same free-variable content. -/
theorem Expr.LeafEquiv.hasFvar_eq : ∀ (e₁ e₂ : Expr), Expr.LeafEquiv e₁ e₂ →
    e₁.hasFvar = e₂.hasFvar := by
  intro e₁
  induction e₁ with
  | fvar idx n ty _ =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
  | app f a ihf iha =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case app f' a' => rw [ihf f' hle.1, iha a' hle.2]
  | lam n ty body m ihty ihbody =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case lam n' ty' body' m' => rw [ihty ty' hle.1, ihbody body' hle.2]
  | forallE n ty body m ihty ihbody =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case forallE n' ty' body' m' => rw [ihty ty' hle.1, ihbody body' hle.2]
  | letE n ty val body ihty ihval ihbody =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case letE n' ty' val' body' =>
      rw [ihty ty' hle.1, ihval val' hle.2.1, ihbody body' hle.2.2]
  | proj s i e ih =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
    case proj s' i' e' => exact ih e' hle
  | bvar i =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
  | sort u =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
  | const n us =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]
  | lit l =>
    intro e₂ hle
    cases e₂ <;> simp_all [Expr.LeafEquiv, Expr.hasFvar]



/-- Un-instantiation: if `y` has the same leaves as `x` opened with
`fvar D`, then abstracting `D` out of `y` recovers the leaves of `x` —
provided `x` does not mention `fvar D` and has no loose bvars above `k`. -/
theorem leafEquiv_abstract_of_inst {D : Nat} {n : Name} {ty : Expr} :
    ∀ (x : Expr) (k : Nat) (y : Expr),
      Expr.LeafEquiv (x.instantiate1 (.fvar D n ty) k) y →
      fvarsBelow D x → x.looseBVarsBounded (k + 1) = true →
      Expr.LeafEquiv x (y.abstract1 D k) := by
  intro x
  induction x with
  | bvar i =>
    intro k y hle hf hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1] at hle
    by_cases hik : i = k
    · simp only [hik, if_pos rfl] at hle
      cases y <;> simp_all [Expr.LeafEquiv]
      case fvar idx n' ty' =>
        obtain ⟨rfl, -, -⟩ := hle
        simp [Expr.abstract1, Expr.LeafEquiv, hik]
    · have hik' : ¬ (i > k) := by omega
      simp only [hik, if_false, hik', Expr.instantiate1] at hle
      cases y <;> simp_all [Expr.LeafEquiv]
      case bvar j =>
        subst hle
        simp [Expr.abstract1, Expr.LeafEquiv]
  | fvar idx n' ty' _ =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv]
    case fvar idx2 n2 ty2 =>
      obtain ⟨rfl, rfl, rfl⟩ := hle
      have : ¬ (idx = D) := by omega
      simp [Expr.abstract1, this, Expr.LeafEquiv]
  | sort u =>
    intro k y hle hf hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | const nm us =>
    intro k y hle hf hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | lit l =>
    intro k y hle hf hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | app f a ihf iha =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | lam nm tyx body ihm ihty ihbody =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | forallE nm tyx body ihm ihty ihbody =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | letE nm tyx vx body ihty ihv ihbody =>
    intro k y hle hf hb
    simp only [Expr.fvarsBelow] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
  | proj s i e ih =>
    intro k y hle hf hb
    simp only [Expr.instantiate1] at hle
    cases y <;> simp_all [Expr.LeafEquiv, Expr.abstract1]
    case proj s2 i2 e2 => exact ih k e2 hle hf hb

end Setlec
