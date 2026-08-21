import Setlec.Kernel.Checker
import Setlec.Model.TypeChecker

/-!
# Frame-crossing interpretation of opened telescopes

The defeq-based iota-rule install opens the stored `iota_j` theorem's
telescope at its *own* free variables (indices `0..`), while the fold
obligation's value spines arrive as telescope fits at *arbitrary*
frames.  The bridge is `interp_instSeq_fvarFrames`: the interpretation
of a closed expression instantiated along a free-variable spine is
determined by the spine's *values* — two spines with pointwise equal
values (at possibly unrelated frames) yield equal interpretations.

On top of it, `instPisAt`/`openPisAtFvars` are characterized as
instantiation sequences of the stripped telescope, and the *walk*
lemmas rebuild telescope fits at the theorem's frame:

* `peel_walk` builds a fit from pointwise memberships in the
  telescope's own (instantiated) domains;
* `pi_walk` transfers memberships along per-binder definitional
  equalities (`isDefEqCore` facts from the kernel's install checks),
  building the theorem-side fit from source-side memberships.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {cval : ConstVal V} {env : Env}
  {φ : Name → Nat}

open SetTheory Expr

/-! ## Fueled spine equalities -/

omit [SetTheory V] in
theorem fueledOpsW_isDefEq (F : Nat) (env : Env) (d : Nat) (a b : Expr) :
    (fueledOps F).isDefEq env d a b = isDefEqCore env F d a b := rfl

/-- Pairwise fueled definitional equality of two spines (the semantic
content of a successful `checkDefEqList`). -/
def DefEqListOk (F : Nat) (env : Env) (d : Nat) :
    List Expr → List Expr → Prop
  | [], [] => True
  | a :: as, b :: bs =>
    isDefEqCore env F d a b = .ok true ∧ DefEqListOk F env d as bs
  | _, _ => False

omit [SetTheory V] in
theorem DefEqListOk.length {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr}, DefEqListOk F env d as bs →
      as.length = bs.length := by
  intro as
  induction as with
  | nil =>
    intro bs h
    match bs, h with
    | [], _ => rfl
  | cons a as ih =>
    intro bs h
    match bs, h with
    | b :: bs, ⟨_, h⟩ => simpa using ih h

omit [SetTheory V] in
theorem DefEqListOk.pointwise {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr}, DefEqListOk F env d as bs →
      ∀ (i : Nat) {a b : Expr}, as[i]? = some a → bs[i]? = some b →
        isDefEqCore env F d a b = .ok true := by
  intro as
  induction as with
  | nil =>
    intro bs h i a b ha hb
    exact nomatch ha
  | cons a₀ as ih =>
    intro bs h i a b ha hb
    match bs, h with
    | b₀ :: bs, ⟨h₀, h⟩ =>
      match i, ha, hb with
      | 0, ha, hb =>
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hb
        exact h₀
      | i + 1, ha, hb => exact ih h i (by simpa using ha) (by simpa using hb)

/-- Invert a successful `checkDefEqList` run. -/
theorem checkDefEqList_inv {F : Nat} {env : Env} {d : Nat} :
    ∀ {as bs : List Expr} {u : Unit},
    checkDefEqList (fueledOps F) env d as bs = .ok u →
    DefEqListOk F env d as bs := by
  intro as
  induction as with
  | nil =>
    intro bs u h
    match bs with
    | [] => trivial
    | _ :: _ =>
      simp only [checkDefEqList] at h
      exact nomatch h
  | cons a as ih =>
    intro bs u h
    match bs with
    | [] =>
      simp only [checkDefEqList] at h
      exact nomatch h
    | b :: bs =>
      simp only [checkDefEqList, fueledOpsW_isDefEq, Bind.bind,
        Except.bind] at h
      revert h
      cases hde : isDefEqCore env F d a b with
      | error e => intro h; exact nomatch h
      | ok v =>
        cases v with
        | false =>
          intro h
          simp [throw, throwThe, MonadExceptOf.throw] at h
        | true =>
          intro h
          simp only [↓reduceIte, pure, Except.pure] at h
          exact ⟨hde, ih h⟩

omit [SetTheory V] in
/-- Invert the boolean equality-head test. -/
theorem isEqHead_inv {e : Expr} (h : isEqHead e = true) :
    ∃ ℓA, e = .const eqName [ℓA] := by
  match e, h with
  | .const c [ℓ], h =>
    refine ⟨ℓ, ?_⟩
    have hc : (c == eqName) = true := by simpa [isEqHead] using h
    rw [eq_of_beq hc]
  | .const _ [], h => simp [isEqHead] at h
  | .const _ (_ :: _ :: _), h => simp [isEqHead] at h
  | .bvar _, h => simp [isEqHead] at h
  | .fvar _ _ _, h => simp [isEqHead] at h
  | .sort _, h => simp [isEqHead] at h
  | .app _ _, h => simp [isEqHead] at h
  | .lam _ _ _ _, h => simp [isEqHead] at h
  | .forallE _ _ _ _, h => simp [isEqHead] at h
  | .letE _ _ _ _, h => simp [isEqHead] at h
  | .lit _, h => simp [isEqHead] at h
  | .proj _ _ _, h => simp [isEqHead] at h


/-! ## Instantiation sequences distribute over the term structure -/

omit [SetTheory V] in
theorem instSeq_app :
    ∀ (args : List Expr) (t : Nat) (f a : Expr),
      instSeq args t (.app f a) =
        .app (instSeq args t f) (instSeq args t a) := by
  intro args
  induction args with
  | nil => intro t f a; rfl
  | cons x xs ih =>
    intro t f a
    show instSeq xs (t - 1) ((Expr.app f a).instantiate1 x t) = _
    simp only [Expr.instantiate1]
    exact ih (t - 1) _ _

omit [SetTheory V] in
theorem instSeq_forallE :
    ∀ (args : List Expr) (t : Nat) (n : Name) (ty body : Expr)
      (m : BinderMeta), args.length ≤ t + 1 →
      instSeq args t (.forallE n ty body m) =
        .forallE n (instSeq args t ty)
          (instSeq args (t + 1) body) m := by
  intro args
  induction args with
  | nil => intro t n ty body m _; rfl
  | cons x xs ih =>
    intro t n ty body m hlen
    show instSeq xs (t - 1) ((Expr.forallE n ty body m).instantiate1 x t)
      = _
    simp only [Expr.instantiate1]
    rw [ih (t - 1) n _ _ m (by simp at hlen; omega)]
    match t, hlen with
    | 0, hlen =>
      obtain rfl : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp at hlen
      rfl
    | t + 1, _ => rfl

omit [SetTheory V] in
theorem instSeq_lam :
    ∀ (args : List Expr) (t : Nat) (n : Name) (ty body : Expr)
      (m : BinderMeta), args.length ≤ t + 1 →
      instSeq args t (.lam n ty body m) =
        .lam n (instSeq args t ty) (instSeq args (t + 1) body) m := by
  intro args
  induction args with
  | nil => intro t n ty body m _; rfl
  | cons x xs ih =>
    intro t n ty body m hlen
    show instSeq xs (t - 1) ((Expr.lam n ty body m).instantiate1 x t) = _
    simp only [Expr.instantiate1]
    rw [ih (t - 1) n _ _ m (by simp at hlen; omega)]
    match t, hlen with
    | 0, hlen =>
      obtain rfl : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp at hlen
      rfl
    | t + 1, _ => rfl

omit [SetTheory V] in
theorem instSeq_letE :
    ∀ (args : List Expr) (t : Nat) (n : Name) (ty v body : Expr),
      args.length ≤ t + 1 →
      instSeq args t (.letE n ty v body) =
        .letE n (instSeq args t ty) (instSeq args t v)
          (instSeq args (t + 1) body) := by
  intro args
  induction args with
  | nil => intro t n ty v body _; rfl
  | cons x xs ih =>
    intro t n ty v body hlen
    show instSeq xs (t - 1) ((Expr.letE n ty v body).instantiate1 x t) = _
    simp only [Expr.instantiate1]
    rw [ih (t - 1) n _ _ _ (by simp at hlen; omega)]
    match t, hlen with
    | 0, hlen =>
      obtain rfl : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp at hlen
      rfl
    | t + 1, _ => rfl

omit [SetTheory V] in
theorem instSeq_proj :
    ∀ (args : List Expr) (t : Nat) (s : Name) (i : Nat) (e : Expr),
      instSeq args t (.proj s i e) = .proj s i (instSeq args t e) := by
  intro args
  induction args with
  | nil => intro t s i e; rfl
  | cons x xs ih =>
    intro t s i e
    show instSeq xs (t - 1) ((Expr.proj s i e).instantiate1 x t) = _
    simp only [Expr.instantiate1]
    exact ih (t - 1) _ _ _

/-! ## Free-variable spines with values -/

/-- A spine of free variables (indices below the frame) whose valuation
values are the given list. -/
def FvarSpine (D : Nat) (ρ : Nat → V) : List Expr → List V → Prop
  | [], [] => True
  | a :: as, v :: vs =>
    (∃ i n ty, a = .fvar i n ty ∧ i < D ∧ ρ i = v) ∧
    FvarSpine D ρ as vs
  | _, _ => False

omit [SetTheory V] in
theorem FvarSpine.length {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V}, FvarSpine D ρ as vs →
      as.length = vs.length
  | [], [], _ => rfl
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: as, _ :: vs, h => by
    simpa using FvarSpine.length h.2

omit [SetTheory V] in
theorem FvarSpine.snoc {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V}, FvarSpine D ρ as vs →
      ∀ {a : Expr} {v : V},
        (∃ i n ty, a = .fvar i n ty ∧ i < D ∧ ρ i = v) →
        FvarSpine D ρ (as ++ [a]) (vs ++ [v])
  | [], [], _, _a, _v, ha => ⟨ha, trivial⟩
  | [], _ :: _, h, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _ => nomatch h
  | _ :: _as, _ :: _vs, h, _a, _v, ha =>
    ⟨h.1, FvarSpine.snoc h.2 ha⟩

omit [SetTheory V] in
/-- Weaken a spine to a higher frame with an agreeing valuation. -/
theorem FvarSpine.lift {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V}, FvarSpine D ρ as vs →
      ∀ {D' : Nat} {ρ' : Nat → V}, D ≤ D' →
        (∀ i, i < D → ρ' i = ρ i) →
        FvarSpine D' ρ' as vs
  | [], [], _, _, _, _, _ => trivial
  | [], _ :: _, h, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _ => nomatch h
  | a :: as, v :: vs, h, D', ρ', hle, hag => by
    obtain ⟨⟨i, n, ty, rfl, hiD, hval⟩, h'⟩ := h
    exact ⟨⟨i, n, ty, rfl, by omega, by rw [hag i hiD]; exact hval⟩,
      FvarSpine.lift h' hle hag⟩

omit [SetTheory V] in
theorem FvarSpine.pointwise {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V}, FvarSpine D ρ as vs →
      ∀ (k : Nat) {a : Expr} {v : V},
        as[k]? = some a → vs[k]? = some v →
        ∃ i n ty, a = .fvar i n ty ∧ i < D ∧ ρ i = v
  | [], [], _, k, a, v, ha, _ => nomatch ha
  | [], _ :: _, h, _, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _, _ => nomatch h
  | a₀ :: as, v₀ :: vs, h, k, a, v, ha, hv => by
    cases k with
    | zero =>
      obtain rfl := Option.some.inj ha
      obtain rfl := Option.some.inj hv
      exact h.1
    | succ k =>
      exact FvarSpine.pointwise h.2 k (by simpa using ha)
        (by simpa using hv)

omit [SetTheory V] in
theorem FvarSpine.bounded {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V}, FvarSpine D ρ as vs →
      ∀ a ∈ as, a.looseBVarsBounded 0 = true := by
  intro as
  induction as with
  | nil => intro vs _ a ha; exact nomatch ha
  | cons a₀ as ih =>
    intro vs h a ha
    match vs, h with
    | v₀ :: vs, h =>
      obtain ⟨⟨i, n, ty, rfl, -, -⟩, h'⟩ := h
      rcases List.mem_cons.mp ha with rfl | ha
      · rfl
      · exact ih h' a ha

/-! ## The frame-crossing interpretation lemma -/

/-- The nonempty-spine core of `interp_instSeq_fvarFrames`. -/
theorem interp_instSeq_fvarFrames_aux :
    ∀ (e : Expr) {spine₁ spine₂ : List Expr} {vs : List V}
      {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V},
      spine₁ ≠ [] →
      e.hasFvar = false →
      e.looseBVarsBounded spine₁.length = true →
      FvarSpine D₁ ρ₁ spine₁ vs → FvarSpine D₂ ρ₂ spine₂ vs →
      interpExpr V cval env φ D₁ ρ₁
        (instSeq spine₁ (spine₁.length - 1) e) =
      interpExpr V cval env φ D₂ ρ₂
        (instSeq spine₂ (spine₂.length - 1) e) := by
  intro e
  induction e with
  | bvar i =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl hb h₁ h₂
    have hlen1 : spine₁.length = vs.length := FvarSpine.length h₁
    have hlen2 : spine₂.length = vs.length := FvarSpine.length h₂
    have hi : i < spine₁.length := by
      simpa [Expr.looseBVarsBounded] using hb
    obtain ⟨a₁, ha₁⟩ : ∃ a, spine₁[spine₁.length - 1 - i]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨a₂, ha₂⟩ : ∃ a, spine₂[spine₂.length - 1 - i]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨v, hv⟩ : ∃ v, vs[spine₁.length - 1 - i]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hs₁ := instSeq_bvar spine₁ (spine₁.length - 1) i
      (FvarSpine.bounded h₁) (by omega) (by omega)
    have hs₂ := instSeq_bvar spine₂ (spine₂.length - 1) i
      (FvarSpine.bounded h₂) (by omega) (by omega)
    rw [ha₁] at hs₁
    rw [ha₂] at hs₂
    have he₁ := Option.some.inj hs₁
    have he₂ := Option.some.inj hs₂
    rw [← he₁, ← he₂]
    obtain ⟨j₁, n₁, t₁, ha₁e, hj₁, hval₁⟩ :=
      FvarSpine.pointwise h₁ _ ha₁ hv
    have hv₂ : vs[spine₂.length - 1 - i]? = some v := by
      rw [show spine₂.length - 1 - i = spine₁.length - 1 - i from by
        omega]
      exact hv
    obtain ⟨j₂, n₂, t₂, ha₂e, hj₂, hval₂⟩ :=
      FvarSpine.pointwise h₂ _ ha₂ hv₂
    rw [ha₁e, ha₂e]
    simp only [interpExpr]
    rw [hval₁, hval₂]
  | fvar idx n ty =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl
    simp [Expr.hasFvar] at hcl
  | sort u =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl hb h₁ h₂
    rw [instSeq_eq_self _ _ (by rfl), instSeq_eq_self _ _ (by rfl)]
    simp [interpExpr]
  | const n us =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl hb h₁ h₂
    rw [instSeq_eq_self _ _ (by rfl), instSeq_eq_self _ _ (by rfl)]
    simp [interpExpr]
  | lit l =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl hb h₁ h₂
    rw [instSeq_eq_self _ _ (by rfl), instSeq_eq_self _ _ (by rfl)]
    cases l with
    | natVal k => simp [interpExpr]
    | strVal st => simp [interpExpr]
  | app f a ihf iha =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl hb h₁ h₂
    have hclf : f.hasFvar = false ∧ a.hasFvar = false := by
      revert hcl; simp [Expr.hasFvar]
    have hbf : f.looseBVarsBounded spine₁.length = true ∧
        a.looseBVarsBounded spine₁.length = true := by
      revert hb; simp [Expr.looseBVarsBounded]
    rw [instSeq_app, instSeq_app]
    simp only [interpExpr]
    rw [ihf hne hclf.1 hbf.1 h₁ h₂, iha hne hclf.2 hbf.2 h₁ h₂]
  | proj s i pe ih =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl hb h₁ h₂
    have hclp : pe.hasFvar = false := by
      revert hcl; simp [Expr.hasFvar]
    have hbp : pe.looseBVarsBounded spine₁.length = true := by
      revert hb; simp [Expr.looseBVarsBounded]
    rw [instSeq_proj, instSeq_proj]
    simp only [interpExpr]
    rw [ih hne hclp hbp h₁ h₂]
  | letE n ty v body ihty ihv ihb =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl hb h₁ h₂
    rw [instSeq_letE _ _ _ _ _ _ (by omega),
      instSeq_letE _ _ _ _ _ _ (by omega)]
    simp [interpExpr]
  | forallE n ty body m ihty ihbody =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl hb h₁ h₂
    have hlen1 : 1 ≤ spine₁.length := by
      cases spine₁ with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    have hclt : ty.hasFvar = false ∧ body.hasFvar = false := by
      revert hcl; simp [Expr.hasFvar]
    have hbt : ty.looseBVarsBounded spine₁.length = true ∧
        body.looseBVarsBounded (spine₁.length + 1) = true := by
      revert hb; simp [Expr.looseBVarsBounded]
    have hlv : spine₁.length = spine₂.length := by
      rw [FvarSpine.length h₁, FvarSpine.length h₂]
    rw [instSeq_forallE _ _ _ _ _ _ (by omega),
      instSeq_forallE _ _ _ _ _ _ (by omega)]
    rw [show spine₁.length - 1 + 1 = spine₁.length from by omega,
      show spine₂.length - 1 + 1 = spine₂.length from by omega]
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some vℓ =>
      simp only []
      rw [ihty hne hclt.1 hbt.1 h₁ h₂]
      cases hty2 : interpExpr V cval env φ D₂ ρ₂
          (instSeq spine₂ (spine₂.length - 1) ty) with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        have hfib := ihbody (spine₁ := spine₁ ++
            [.fvar D₁ n (instSeq spine₁ (spine₁.length - 1) ty)])
          (spine₂ := spine₂ ++
            [.fvar D₂ n (instSeq spine₂ (spine₂.length - 1) ty)])
          (vs := vs ++ [x])
          (D₁ := D₁ + 1) (D₂ := D₂ + 1)
          (ρ₁ := updV V ρ₁ D₁ x) (ρ₂ := updV V ρ₂ D₂ x)
          (by simp) hclt.2 (by simpa using hbt.2)
          (FvarSpine.snoc
            (FvarSpine.lift h₁ (Nat.le_succ D₁)
              (fun i hi => by simp only [updV]; rw [if_neg (by omega)]))
            ⟨D₁, n, _, rfl, by omega, by simp [updV]⟩)
          (FvarSpine.snoc
            (FvarSpine.lift h₂ (Nat.le_succ D₂)
              (fun i hi => by simp only [updV]; rw [if_neg (by omega)]))
            ⟨D₂, n, _, rfl, by omega, by simp [updV]⟩)
        rw [instSeq_append, instSeq_append] at hfib
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hfib
        rw [show spine₁.length + 1 - 1 - spine₁.length = 0 from by omega,
          show spine₂.length + 1 - 1 - spine₂.length = 0 from by omega]
          at hfib
        rw [show spine₁.length + 1 - 1 = spine₁.length from by omega,
          show spine₂.length + 1 - 1 = spine₂.length from by omega]
          at hfib
        simp only [instSeq] at hfib
        exact congrArg (fun o => Option.getD o SetTheory.empty) hfib
  | lam n ty body m ihty ihbody =>
    intro spine₁ spine₂ vs D₁ D₂ ρ₁ ρ₂ hne hcl hb h₁ h₂
    have hlen1 : 1 ≤ spine₁.length := by
      cases spine₁ with
      | nil => exact absurd rfl hne
      | cons _ _ => simp
    have hclt : ty.hasFvar = false ∧ body.hasFvar = false := by
      revert hcl; simp [Expr.hasFvar]
    have hbt : ty.looseBVarsBounded spine₁.length = true ∧
        body.looseBVarsBounded (spine₁.length + 1) = true := by
      revert hb; simp [Expr.looseBVarsBounded]
    have hlv : spine₁.length = spine₂.length := by
      rw [FvarSpine.length h₁, FvarSpine.length h₂]
    rw [instSeq_lam _ _ _ _ _ _ (by omega),
      instSeq_lam _ _ _ _ _ _ (by omega)]
    rw [show spine₁.length - 1 + 1 = spine₁.length from by omega,
      show spine₂.length - 1 + 1 = spine₂.length from by omega]
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some vℓ =>
      simp only []
      rw [ihty hne hclt.1 hbt.1 h₁ h₂]
      cases hty2 : interpExpr V cval env φ D₂ ρ₂
          (instSeq spine₂ (spine₂.length - 1) ty) with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        have hfib := ihbody (spine₁ := spine₁ ++
            [.fvar D₁ n (instSeq spine₁ (spine₁.length - 1) ty)])
          (spine₂ := spine₂ ++
            [.fvar D₂ n (instSeq spine₂ (spine₂.length - 1) ty)])
          (vs := vs ++ [x])
          (D₁ := D₁ + 1) (D₂ := D₂ + 1)
          (ρ₁ := updV V ρ₁ D₁ x) (ρ₂ := updV V ρ₂ D₂ x)
          (by simp) hclt.2 (by simpa using hbt.2)
          (FvarSpine.snoc
            (FvarSpine.lift h₁ (Nat.le_succ D₁)
              (fun i hi => by simp only [updV]; rw [if_neg (by omega)]))
            ⟨D₁, n, _, rfl, by omega, by simp [updV]⟩)
          (FvarSpine.snoc
            (FvarSpine.lift h₂ (Nat.le_succ D₂)
              (fun i hi => by simp only [updV]; rw [if_neg (by omega)]))
            ⟨D₂, n, _, rfl, by omega, by simp [updV]⟩)
        rw [instSeq_append, instSeq_append] at hfib
        simp only [List.length_append, List.length_cons,
          List.length_nil] at hfib
        rw [show spine₁.length + 1 - 1 - spine₁.length = 0 from by omega,
          show spine₂.length + 1 - 1 - spine₂.length = 0 from by omega]
          at hfib
        rw [show spine₁.length + 1 - 1 = spine₁.length from by omega,
          show spine₂.length + 1 - 1 = spine₂.length from by omega]
          at hfib
        simp only [instSeq] at hfib
        exact congrArg (fun o => Option.getD o SetTheory.empty) hfib

/-- The interpretation of a closed expression instantiated along a
free-variable spine is determined by the spine's values: two spines
with pointwise equal values — at possibly unrelated frames — give
equal interpretations. -/
theorem interp_instSeq_fvarFrames {e : Expr} {spine₁ spine₂ : List Expr}
    {vs : List V} {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
    (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded spine₁.length = true)
    (h₁ : FvarSpine D₁ ρ₁ spine₁ vs) (h₂ : FvarSpine D₂ ρ₂ spine₂ vs) :
    interpExpr V cval env φ D₁ ρ₁
      (instSeq spine₁ (spine₁.length - 1) e) =
    interpExpr V cval env φ D₂ ρ₂
      (instSeq spine₂ (spine₂.length - 1) e) := by
  cases hsp : spine₁ with
  | nil =>
    subst hsp
    obtain rfl : spine₂ = [] := by
      have h1 := FvarSpine.length h₁
      have h2 := FvarSpine.length h₂
      cases spine₂ with
      | nil => rfl
      | cons _ _ =>
        simp at h1 h2
        rw [← h1] at h2
        exact nomatch h2
    show interpExpr V cval env φ D₁ ρ₁ e = interpExpr V cval env φ D₂ ρ₂ e
    rw [interp_closed_invariant hcl D₁ ρ₁, interp_closed_invariant hcl D₂ ρ₂]
  | cons s₀ srest =>
    subst hsp
    exact interp_instSeq_fvarFrames_aux e (by simp) hcl hb h₁ h₂

/-! ## Characterizing the kernel's telescope openers -/

omit [SetTheory V] in
theorem instPisAt_length :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instPisAt args e = some (ds, rest) → ds.length = args.length
  | [], e, ds, rest, h => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | a :: as, e, ds, rest, h => by
    match e, h with
    | .forallE n dom body m, h =>
      simp only [Expr.instPisAt] at h
      cases h0 : Expr.instPisAt as (body.instantiate1 a) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hds, -⟩ : dom :: p.1 = ds ∧ p.2 = rest := by
          cases h; exact ⟨rfl, rfl⟩
        subst hds
        simpa using instPisAt_length as (by rw [h0])

omit [SetTheory V] in
/-- Invert one step of the instantiation walk. -/
theorem instPisAt_cons_inv {a : Expr} {as : List Expr} {e : Expr}
    {ds : List Expr} {rest : Expr}
    (h : Expr.instPisAt (a :: as) e = some (ds, rest)) :
    ∃ n dom body m ds', e = .forallE n dom body m ∧ ds = dom :: ds' ∧
      Expr.instPisAt as (body.instantiate1 a) = some (ds', rest) := by
  revert h
  match e with
  | .forallE n dom body m => ?_
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .const _ _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .lam _ _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  intro h
  simp only [Expr.instPisAt] at h
  cases h0 : Expr.instPisAt as (body.instantiate1 a) with
  | none => rw [h0] at h; exact nomatch h
  | some p =>
    rw [h0] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨n, dom, body, m, p.1, rfl, h1.symm, by rw [h0, ← h2]⟩

omit [SetTheory V] in
theorem instLamsAt_length :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instLamsAt args e = some (ds, rest) → ds.length = args.length
  | [], e, ds, rest, h => by
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    rfl
  | a :: as, e, ds, rest, h => by
    match e, h with
    | .lam n dom body m, h =>
      simp only [Expr.instLamsAt] at h
      cases h0 : Expr.instLamsAt as (body.instantiate1 a) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hds, -⟩ : dom :: p.1 = ds ∧ p.2 = rest := by
          cases h; exact ⟨rfl, rfl⟩
        subst hds
        simpa using instLamsAt_length as (by rw [h0])

omit [SetTheory V] in
/-- Split an instantiation walk along a list append. -/
theorem instPisAt_append :
    ∀ (as bs : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instPisAt (as ++ bs) e = some (ds, rest) →
      ∃ ds₁ mid ds₂, Expr.instPisAt as e = some (ds₁, mid) ∧
        Expr.instPisAt bs mid = some (ds₂, rest) ∧ ds = ds₁ ++ ds₂
  | [], bs, e, ds, rest, h => ⟨[], e, ds, rfl, h, rfl⟩
  | a :: as, bs, e, ds, rest, h => by
    match e, h with
    | .forallE n dom body m, h =>
      simp only [List.cons_append, Expr.instPisAt] at h
      cases h0 : Expr.instPisAt (as ++ bs) (body.instantiate1 a) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hds, hrest⟩ : dom :: p.1 = ds ∧ p.2 = rest := by
          cases h; exact ⟨rfl, rfl⟩
        subst hds hrest
        obtain ⟨ds₁, mid, ds₂, h1, h2, h3⟩ :=
          instPisAt_append as bs (by rw [h0])
        refine ⟨dom :: ds₁, mid, ds₂, ?_, h2, by rw [h3]; rfl⟩
        simp only [Expr.instPisAt, h1]
        rfl

omit [SetTheory V] in
/-- The instantiation walk's domains are the stripped telescope's,
instantiated at the consumed prefix; the residual is the instantiated
body. -/
theorem instPisAt_stripPis :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      Expr.instPisAt args e = some (ds, rest) →
      e.stripPis args.length = some (bs, body) →
      rest = instSeq args (args.length - 1) body ∧
      ∀ k b, bs[k]? = some b →
        ds[k]? = some (instSeq (args.take k) (k - 1) b.2.1)
  | [], e, ds, rest, bs, body, h, hstrip => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    simp only [List.length_nil, Expr.stripPis, Option.some.injEq,
      Prod.mk.injEq] at hstrip
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := hstrip
    exact ⟨rfl, fun k b hb => by simp at hb⟩
  | a :: as, e, ds, rest, bs, body, h, hstrip => by
    match e, h with
    | .forallE n dom bodyE m, h =>
      simp only [Expr.instPisAt] at h
      cases h0 : Expr.instPisAt as (bodyE.instantiate1 a) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hds, hrest⟩ : dom :: p.1 = ds ∧ p.2 = rest := by
          cases h; exact ⟨rfl, rfl⟩
        subst hds hrest
        simp only [List.length_cons, Expr.stripPis] at hstrip
        cases hs0 : bodyE.stripPis as.length with
        | none => rw [hs0] at hstrip; exact nomatch hstrip
        | some p0 =>
          rw [hs0] at hstrip
          simp only [Option.map_some, Option.some.injEq] at hstrip
          obtain ⟨hbs, hbody⟩ : (n, dom, m) :: p0.1 = bs ∧ p0.2 = body := by
            cases hstrip; exact ⟨rfl, rfl⟩
          subst hbs hbody
          cases hs1 : (bodyE.instantiate1 a).stripPis as.length with
          | none =>
            exact absurd (Expr.stripPis_instantiate1_isSome as.length 0
              (by rw [hs0]; rfl)) (by rw [hs1]; simp)
          | some p1 =>
            obtain ⟨hbody1, hdoms1⟩ :=
              Expr.stripPis_instantiate1_eq as.length 0 hs0 hs1
            obtain ⟨hrest', hds'⟩ :=
              instPisAt_stripPis as (bs := p1.1) (body := p1.2)
                (by rw [h0]) (by rw [hs1])
            constructor
            · rw [hrest', hbody1]
              show instSeq as (as.length - 1)
                  (p0.2.instantiate1 a (0 + as.length)) =
                instSeq (a :: as) (as.length + 1 - 1) p0.2
              simp only [Nat.zero_add, Nat.add_sub_cancel]
              rfl
            · intro k b hb
              cases k with
              | zero =>
                obtain rfl := Option.some.inj hb
                rfl
              | succ k =>
                simp only [List.getElem?_cons_succ] at hb ⊢
                have hlen1 := Expr.stripPis_length as.length
                  (e := bodyE.instantiate1 a) (by rw [hs1])
                have hlen0 := Expr.stripPis_length as.length
                  (e := bodyE) (by rw [hs0])
                have hlt : k < p1.1.length := by
                  rcases Nat.lt_or_ge k p1.1.length with hlt | hge
                  · exact hlt
                  · rw [List.getElem?_eq_none (by omega)] at hb
                    exact nomatch hb
                obtain ⟨b', hb'⟩ : ∃ b', p1.1[k]? = some b' :=
                  ⟨_, List.getElem?_eq_getElem hlt⟩
                have hdom := hdoms1 k b b' hb hb'
                rw [hds' k b' hb', hdom]
                show some (instSeq (as.take k) (k - 1)
                    (b.2.1.instantiate1 a (0 + k))) =
                  some (instSeq (a :: as.take k) (k + 1 - 1) b.2.1)
                simp only [Nat.zero_add, Nat.add_sub_cancel]
                rfl

omit [SetTheory V] in
/-- λ-version of `instPisAt_stripPis`. -/
theorem instLamsAt_stripLams :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      Expr.instLamsAt args e = some (ds, rest) →
      e.stripLams args.length = some (bs, body) →
      rest = instSeq args (args.length - 1) body ∧
      ∀ k b, bs[k]? = some b →
        ds[k]? = some (instSeq (args.take k) (k - 1) b.2.1)
  | [], e, ds, rest, bs, body, h, hstrip => by
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    simp only [List.length_nil, Expr.stripLams, Option.some.injEq,
      Prod.mk.injEq] at hstrip
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := hstrip
    exact ⟨rfl, fun k b hb => by simp at hb⟩
  | a :: as, e, ds, rest, bs, body, h, hstrip => by
    match e, h with
    | .lam n dom bodyE m, h =>
      simp only [Expr.instLamsAt] at h
      cases h0 : Expr.instLamsAt as (bodyE.instantiate1 a) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hds, hrest⟩ : dom :: p.1 = ds ∧ p.2 = rest := by
          cases h; exact ⟨rfl, rfl⟩
        subst hds hrest
        simp only [List.length_cons, Expr.stripLams] at hstrip
        cases hs0 : bodyE.stripLams as.length with
        | none => rw [hs0] at hstrip; exact nomatch hstrip
        | some p0 =>
          rw [hs0] at hstrip
          simp only [Option.map_some, Option.some.injEq] at hstrip
          obtain ⟨hbs, hbody⟩ : (n, dom, m) :: p0.1 = bs ∧ p0.2 = body := by
            cases hstrip; exact ⟨rfl, rfl⟩
          subst hbs hbody
          cases hs1 : (bodyE.instantiate1 a).stripLams as.length with
          | none =>
            exact absurd (Expr.stripLams_instantiate1_isSome as.length 0
              (by rw [hs0]; rfl)) (by rw [hs1]; simp)
          | some p1 =>
            obtain ⟨hbody1, hdoms1⟩ :=
              Expr.stripLams_instantiate1_eq as.length 0 hs0 hs1
            obtain ⟨hrest', hds'⟩ :=
              instLamsAt_stripLams as (bs := p1.1) (body := p1.2)
                (by rw [h0]) (by rw [hs1])
            constructor
            · rw [hrest', hbody1]
              show instSeq as (as.length - 1)
                  (p0.2.instantiate1 a (0 + as.length)) =
                instSeq (a :: as) (as.length + 1 - 1) p0.2
              simp only [Nat.zero_add, Nat.add_sub_cancel]
              rfl
            · intro k b hb
              cases k with
              | zero =>
                obtain rfl := Option.some.inj hb
                rfl
              | succ k =>
                simp only [List.getElem?_cons_succ] at hb ⊢
                have hlen1 := Expr.stripLams_length as.length
                  (e := bodyE.instantiate1 a) (by rw [hs1])
                have hlen0 := Expr.stripLams_length as.length
                  (e := bodyE) (by rw [hs0])
                have hlt : k < p1.1.length := by
                  rcases Nat.lt_or_ge k p1.1.length with hlt | hge
                  · exact hlt
                  · rw [List.getElem?_eq_none (by omega)] at hb
                    exact nomatch hb
                obtain ⟨b', hb'⟩ : ∃ b', p1.1[k]? = some b' :=
                  ⟨_, List.getElem?_eq_getElem hlt⟩
                have hdom := hdoms1 k b b' hb hb'
                rw [hds' k b' hb', hdom]
                show some (instSeq (as.take k) (k - 1)
                    (b.2.1.instantiate1 a (0 + k))) =
                  some (instSeq (a :: as.take k) (k + 1 - 1) b.2.1)
                simp only [Nat.zero_add, Nat.add_sub_cancel]
                rfl

omit [SetTheory V] in
/-- `openPisAtFvars` is `instPisAt` at the constructed variables, whose
annotations are the walk's (instantiated) domains and whose indices are
consecutive from the start index. -/
theorem openPisAtFvars_spec :
    ∀ (n : Nat) {e : Expr} (i₀ : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i₀ = some (fvs, body) →
      Expr.instPisAt fvs e = some (fvs.map Expr.fvarTypeD, body) ∧
      fvs.length = n ∧
      ∀ k a, fvs[k]? = some a →
        ∃ nm, a = Expr.fvar (i₀ + k) nm (Expr.fvarTypeD a)
  | 0, e, i₀, fvs, body, h => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, fun k a ha => by simp at ha⟩
  | n + 1, e, i₀, fvs, body, h => by
    match e, h with
    | .forallE nm dom bodyE m, h =>
      simp only [openPisAtFvars] at h
      cases h0 : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i₀ nm dom)) (i₀ + 1) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hfvs, hbody⟩ := h
        subst hfvs hbody
        obtain ⟨hinst, hlen, hshape⟩ := openPisAtFvars_spec n (i₀ + 1) h0
        refine ⟨?_, by simpa using hlen, ?_⟩
        · simp only [List.map_cons, Expr.instPisAt, hinst]
          rfl
        · intro k a ha
          cases k with
          | zero =>
            obtain rfl := Option.some.inj ha
            exact ⟨nm, rfl⟩
          | succ k =>
            simp only [List.getElem?_cons_succ] at ha
            obtain ⟨nm', ha'⟩ := hshape k a ha
            refine ⟨nm', ?_⟩
            rw [show i₀ + (k + 1) = i₀ + 1 + k from by omega]
            exact ha'

omit [SetTheory V] in
/-- The opened variables (and body) of `openPisAtFvars` are well-scoped
one past their own index. -/
theorem openPisAtFvars_wscoped :
    ∀ (n : Nat) {e : Expr} (i₀ : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i₀ = some (fvs, body) →
      WScoped i₀ e →
      (∀ k a, fvs[k]? = some a → WScoped (i₀ + k + 1) a) ∧
      WScoped (i₀ + n) body
  | 0, e, i₀, fvs, body, h, hw => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨fun k a ha => by simp at ha, by simpa using hw⟩
  | n + 1, e, i₀, fvs, body, h, hw => by
    match e, h with
    | .forallE nm dom bodyE m, h =>
      simp only [openPisAtFvars] at h
      cases h0 : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i₀ nm dom)) (i₀ + 1) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hfvs, hbody⟩ := h
        subst hfvs hbody
        have hw' : WScoped i₀ dom ∧ WScoped i₀ bodyE := by
          simpa [WScoped] using hw
        have hfv : WScoped (i₀ + 1) (Expr.fvar i₀ nm dom) := by
          simp only [WScoped]
          exact ⟨by omega, hw'.1⟩
        have hbw : WScoped (i₀ + 1)
            (bodyE.instantiate1 (.fvar i₀ nm dom)) :=
          WScoped.instantiate1_gen hfv 0 (hw'.2.mono (by omega))
        obtain ⟨hfvsW, hbodyW⟩ := openPisAtFvars_wscoped n (i₀ + 1) h0 hbw
        refine ⟨?_, by
          rw [show i₀ + (n + 1) = i₀ + 1 + n from by omega]
          exact hbodyW⟩
        intro k a ha
        cases k with
        | zero =>
          obtain rfl := Option.some.inj ha
          exact hfv
        | succ k =>
          simp only [List.getElem?_cons_succ] at ha
          have := hfvsW k a ha
          rw [show i₀ + (k + 1) + 1 = i₀ + 1 + k + 1 from by omega]
          exact this

/-! ## The defeq-transfer telescope walk -/

omit [SetTheory V] in
theorem LeavesBounded.of_forallE_ty {n : Name} {ty body : Expr}
    {m : BinderMeta} (h : Expr.LeavesBounded (.forallE n ty body m)) :
    Expr.LeavesBounded ty := by
  intro l hl
  exact h l (by simp only [fvarLeaves, List.mem_append]; exact Or.inl hl)

omit [SetTheory V] in
theorem LeavesBounded.of_forallE_body {n : Name} {ty body : Expr}
    {m : BinderMeta} (h : Expr.LeavesBounded (.forallE n ty body m)) :
    Expr.LeavesBounded body := by
  intro l hl
  exact h l (by simp only [fvarLeaves, List.mem_append]; exact Or.inr hl)

omit [SetTheory V] in
theorem LeavesBounded.fvar {i : Nat} {n : Name} {ty : Expr}
    (hty : ty.looseBVarsBounded 0 = true)
    (h : Expr.LeavesBounded ty) :
    Expr.LeavesBounded (.fvar i n ty) := by
  intro l hl
  simp only [fvarLeaves, List.mem_cons] at hl
  rcases hl with rfl | hl
  · exact hty
  · exact h l hl

omit [SetTheory V] in
theorem LeavesBounded.instantiate1 {body a : Expr} {k : Nat}
    (hb : Expr.LeavesBounded body) (ha : Expr.LeavesBounded a) :
    Expr.LeavesBounded (body.instantiate1 a k) := by
  intro l hl
  rcases fvarLeaves_instantiate1 body k hl with hl | hl
  · exact hb l hl
  · exact ha l hl

/-- The two-sided defeq-transfer walk: the theorem-side telescope
(whose walk domains are the opening variables' annotations) and a
source-side telescope, opened at the *same* free-variable spine, with
per-binder fueled definitional equality of the domains.  Values known
to inhabit the source domains fit both telescopes, and every spine
variable's typing facts (`FvarsOk`) are established. -/
theorem pi_walk {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {spine : List Expr} {vs : List V} {tyS tyR : Expr}
      {dsR : List Expr} {restS restR : Expr},
      Expr.instPisAt spine tyS = some (spine.map Expr.fvarTypeD, restS) →
      Expr.instPisAt spine tyR = some (dsR, restR) →
      DefEqListOk F env D (spine.map Expr.fvarTypeD) dsR →
      FvarSpine D ρ spine vs →
      (∀ a ∈ spine, WScoped D a) →
      WScoped D tyS → tyS.looseBVarsBounded 0 = true →
      Expr.LeavesBounded tyS → FvarsOk V m.val env φ D ρ tyS →
      AnnotOk V m.val env φ D ρ tyS →
      WScoped D tyR → tyR.looseBVarsBounded 0 = true →
      Expr.LeavesBounded tyR → FvarsOk V m.val env φ D ρ tyR →
      AnnotOk V m.val env φ D ρ tyR →
      (∃ PS, interpExpr V m.val env φ D ρ tyS = some PS) →
      (∃ PR, interpExpr V m.val env φ D ρ tyR = some PR) →
      (∀ (k : Nat) (a : Expr) (v : V), dsR[k]? = some a →
        vs[k]? = some v →
        ∃ B, interpExpr V m.val env φ D ρ a = some B ∧ v ∈ˢ B) →
      TeleFitI V m.val env φ D ρ tyS spine vs restS ∧
      TeleFitI V m.val env φ D ρ tyR spine vs restR ∧
      (∀ a ∈ spine, FvarsOk V m.val env φ D ρ a) := by
  intro spine
  induction spine with
  | nil =>
    intro vs tyS tyR dsR restS restR hopS hopR hde hsp hws hWS hbS hLS
      hFS hAS hWR hbR hLR hFR hAR hIS hIR hmem
    simp only [List.map_nil, Expr.instPisAt, Option.some.injEq,
      Prod.mk.injEq] at hopS hopR
    obtain ⟨-, rfl⟩ := hopS
    obtain ⟨rfl, rfl⟩ := hopR
    match vs, hsp with
    | [], _ =>
      exact ⟨TeleFitI.nil, TeleFitI.nil, fun a ha => nomatch ha⟩
  | cons fv spine' ih =>
    intro vs tyS tyR dsR restS restR hopS hopR hde hsp hws hWS hbS hLS
      hFS hAS hWR hbR hLR hFR hAR hIS hIR hmem
    -- destructure the value spine and the fvar
    match vs, hsp with
    | v :: vs', hsp =>
    obtain ⟨⟨i, nfv, tfv, rfl, hiD, hval⟩, hsp'⟩ := hsp
    -- destructure the two walks
    obtain ⟨nS, domS, bodyS, mS, dsS', rfl, hdsS, hS0⟩ :=
      instPisAt_cons_inv hopS
    obtain ⟨nR, domR, bodyR, mR, dsR', rfl, hdsRc, hR0⟩ :=
      instPisAt_cons_inv hopR
    have hdomS : domS = tfv ∧ dsS' = spine'.map Expr.fvarTypeD := by
      rw [List.map_cons] at hdsS
      injection hdsS with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    obtain ⟨hdomS1, rfl⟩ := hdomS
    subst domS
    subst hdsRc
    -- the defeq fact at this binder
    have hde0 : isDefEqCore env F D tfv domR = .ok true := by
      rw [List.map_cons] at hde
      exact hde.1
    have hde' : DefEqListOk F env D (spine'.map Expr.fvarTypeD) dsR' := by
      rw [List.map_cons] at hde
      exact hde.2
    -- structural facts
    have hWdomS : WScoped D tfv ∧ WScoped D bodyS := by
      simpa [WScoped] using hWS
    have hWdomR : WScoped D domR ∧ WScoped D bodyR := by
      simpa [WScoped] using hWR
    have hbdomS : tfv.looseBVarsBounded 0 = true ∧
        bodyS.looseBVarsBounded 1 = true := by
      revert hbS; simp [Expr.looseBVarsBounded]
    have hbdomR : domR.looseBVarsBounded 0 = true ∧
        bodyR.looseBVarsBounded 1 = true := by
      revert hbR; simp [Expr.looseBVarsBounded]
    have hLdomS := LeavesBounded.of_forallE_ty hLS
    have hLdomR := LeavesBounded.of_forallE_ty hLR
    have hFdomS : FvarsOk V m.val env φ D ρ tfv :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFS
    have hFdomR : FvarsOk V m.val env φ D ρ domR :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFR
    have hAS' := hAS
    simp only [AnnotOk] at hAS'
    obtain ⟨hAdomS, ⟨codS, hcodS⟩, hcondS⟩ := hAS'
    have hAR' := hAR
    simp only [AnnotOk] at hAR'
    obtain ⟨hAdomR, ⟨codR, hcodR⟩, hcondR⟩ := hAR'
    -- interpretations of the two domains
    obtain ⟨PS, hPS⟩ := hIS
    obtain ⟨PR, hPR⟩ := hIR
    have hIdomS : ∃ AS, interpExpr V m.val env φ D ρ tfv = some AS := by
      revert hPS
      simp only [interpExpr, hcodS]
      cases hAS0 : interpExpr V m.val env φ D ρ tfv with
      | none => intro hPS; exact nomatch hPS
      | some AS => intro _; exact ⟨AS, rfl⟩
    obtain ⟨AS, hASi⟩ := hIdomS
    obtain ⟨B, hBi, hvB⟩ := hmem 0 domR v rfl rfl
    -- the defeq identifies the domains' interpretations
    have hASB : AS = B :=
      isDefEqCore_sound m F hde0 hWdomS.1 hWdomR.1 hbdomS.1 hbdomR.1
        hLdomS hLdomR hFdomS hFdomR hAdomS hAdomR hASi hBi
    have hvAS : v ∈ˢ AS := by rw [hASB]; exact hvB
    -- the opening variable's own facts
    have hifv : interpExpr V m.val env φ D ρ (.fvar i nfv tfv) = some v := by
      simp only [interpExpr]
      rw [hval]
    have hFfv : FvarsOk V m.val env φ D ρ (.fvar i nfv tfv) := by
      intro l hl
      simp only [fvarLeaves, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ⟨hiD, hAdomS, AS, hASi, by rw [hval]; exact hvAS⟩
      · exact hFdomS l hl
    have hwfv : WScoped D (Expr.fvar i nfv tfv) :=
      hws _ List.mem_cons_self
    have hLfv : Expr.LeavesBounded (.fvar i nfv tfv) :=
      LeavesBounded.fvar hbdomS.1 hLdomS
    -- step both bodies
    obtain ⟨hAopS, hfibS⟩ := hcondS v AS hASi hvAS
    obtain ⟨hAopR, hfibR⟩ := hcondR v B hBi hvB
    have hAbodyS : AnnotOk V m.val env φ D ρ
        (bodyS.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWdomS.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAopS
    have hAbodyR : AnnotOk V m.val env φ D ρ
        (bodyR.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWdomR.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAopR
    obtain ⟨wS, hwS, -⟩ := hfibS codS hcodS
    obtain ⟨wR, hwR, -⟩ := hfibR codR hcodR
    have hIbodyS : ∃ P, interpExpr V m.val env φ D ρ
        (bodyS.instantiate1 (.fvar i nfv tfv)) = some P := by
      refine ⟨wS, ?_⟩
      rw [interp_beta (n := nS) (ty := tfv) hWdomS.2.fvarsBelow hwfv
        (by rfl) hifv 0]
      exact hwS
    have hIbodyR : ∃ P, interpExpr V m.val env φ D ρ
        (bodyR.instantiate1 (.fvar i nfv tfv)) = some P := by
      refine ⟨wR, ?_⟩
      rw [interp_beta (n := nR) (ty := domR) hWdomR.2.fvarsBelow hwfv
        (by rfl) hifv 0]
      exact hwR
    -- recursive call
    have hrec := ih (vs := vs') (dsR := dsR')
      (restS := restS) (restR := restR)
      hS0 hR0
      hde' hsp' (fun a ha => hws a (List.mem_cons_of_mem _ ha))
      (WScoped.instantiate1_gen hwfv 0 hWdomS.2)
      (looseBVarsBounded_instantiate1_gen (by rfl) hbdomS.2)
      (LeavesBounded.instantiate1 (LeavesBounded.of_forallE_body hLS)
        hLfv)
      (fun l hl => by
        rcases fvarLeaves_instantiate1 bodyS 0 hl with hl' | hl'
        · exact hFS l (by
            simp only [fvarLeaves, List.mem_append]
            exact Or.inr hl')
        · exact hFfv l hl')
      hAbodyS
      (WScoped.instantiate1_gen hwfv 0 hWdomR.2)
      (looseBVarsBounded_instantiate1_gen (by rfl) hbdomR.2)
      (LeavesBounded.instantiate1 (LeavesBounded.of_forallE_body hLR)
        hLfv)
      (fun l hl => by
        rcases fvarLeaves_instantiate1 bodyR 0 hl with hl' | hl'
        · exact hFR l (by
            simp only [fvarLeaves, List.mem_append]
            exact Or.inr hl')
        · exact hFfv l hl')
      hAbodyR hIbodyS hIbodyR
      (fun k a v' ha hv' => hmem (k + 1) a v'
        (show (domR :: dsR')[k + 1]? = some a from by simpa using ha)
        (show (v :: vs')[k + 1]? = some v' from by simpa using hv'))
    obtain ⟨hfitS, hfitR, hspineF⟩ := hrec
    refine ⟨?_, ?_, ?_⟩
    · exact TeleFitI.cons hASi hifv hvAS hWdomS.2.fvarsBelow hwfv
        (by rfl) (by simp [AnnotOk]) hfitS
    · exact TeleFitI.cons hBi hifv hvB hWdomR.2.fvarsBelow hwfv
        (by rfl) (by simp [AnnotOk]) hfitR
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hFfv
      · exact hspineF a ha

/-! ## Renaming and telescope bookkeeping -/

omit [SetTheory V] in
theorem hasFvar_renameConsts {f : Name → Name} :
    ∀ (e : Expr), (e.renameConsts f).hasFvar = e.hasFvar := by
  intro e
  induction e <;> simp_all [Expr.renameConsts, Expr.hasFvar]

omit [SetTheory V] in
/-- Renaming maps a stripped telescope pointwise. -/
theorem stripPis_renameConsts {f : Name → Name} :
    ∀ (n : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr},
      e.stripPis n = some (bs, body) →
      (e.renameConsts f).stripPis n =
        some (bs.map (fun b => (b.1, b.2.1.renameConsts f, b.2.2)),
          body.renameConsts f) := by
  intro n
  induction n with
  | zero =>
    intro e bs body h
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | succ n ih =>
    intro e bs body h
    match e, h with
    | .forallE nm dom b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hbs, hbody⟩ : (nm, dom, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbs hbody
        show ((b.renameConsts f).stripPis n).map _ = _
        rw [ih hs]
        rfl

omit [SetTheory V] in
/-- Domains of a closed telescope are closed. -/
theorem stripPis_doms_hasFvar :
    ∀ (n : Nat) {e : Expr} {bs : List (Name × Expr × BinderMeta)}
      {body : Expr},
      e.stripPis n = some (bs, body) → e.hasFvar = false →
      ∀ b ∈ bs, b.2.1.hasFvar = false := by
  intro n
  induction n with
  | zero =>
    intro e bs body h _
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro b hb
    exact nomatch hb
  | succ n ih =>
    intro e bs body h hcl
    match e, h with
    | .forallE nm dom b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hbs, -⟩ : (nm, dom, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbs
        have hcl' : dom.hasFvar = false ∧ b.hasFvar = false := by
          revert hcl; simp [Expr.hasFvar]
        intro b' hb'
        rcases List.mem_cons.mp hb' with rfl | hb'
        · exact hcl'.1
        · exact ih hs hcl'.2 b' hb'

omit [SetTheory V] in
/-- Domains of a bvar-closed telescope are bounded by their
position. -/
theorem stripPis_doms_bounded :
    ∀ (n : Nat) (j : Nat) {e : Expr}
      {bs : List (Name × Expr × BinderMeta)} {body : Expr},
      e.stripPis n = some (bs, body) →
      e.looseBVarsBounded j = true →
      ∀ (k : Nat) (b : Name × Expr × BinderMeta), bs[k]? = some b →
        b.2.1.looseBVarsBounded (j + k) = true := by
  intro n
  induction n with
  | zero =>
    intro j e bs body h _
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro k b hb
    exact nomatch hb
  | succ n ih =>
    intro j e bs body h hbd
    match e, h with
    | .forallE nm dom b m, h =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis n with
      | none => rw [hs] at h; exact nomatch h
      | some p =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hbs, -⟩ : (nm, dom, m) :: p.1 = bs ∧ p.2 = body := by
          cases h; exact ⟨rfl, rfl⟩
        subst hbs
        have hbd' : dom.looseBVarsBounded j = true ∧
            b.looseBVarsBounded (j + 1) = true := by
          revert hbd; simp [Expr.looseBVarsBounded]
        intro k b' hb'
        cases k with
        | zero =>
          obtain rfl := Option.some.inj hb'
          simpa using hbd'.1
        | succ k =>
          simp only [List.getElem?_cons_succ] at hb'
          have := ih (j + 1) hs hbd'.2 k b' hb'
          rw [show j + (k + 1) = j + 1 + k from by omega]
          exact this

/-- An expression-spine fit is an instantiation walk with pointwise
interpreted memberships. -/
theorem TeleFitI.toInstPisAt {d : Nat} {ρ : Nat → V} :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest →
      ∃ ds, Expr.instPisAt args ty = some (ds, rest) ∧
        ∀ (k : Nat) (a : Expr) (v : V), ds[k]? = some a →
          vs[k]? = some v →
          ∃ B, interpExpr V cval env φ d ρ a = some B ∧ v ∈ˢ B := by
  intro ty args vs rest h
  induction h with
  | nil =>
    exact ⟨[], rfl, fun k a v ha hv => nomatch ha⟩
  | @cons n ty₀ body m arg args x xs A rest hity hiarg hx hfb hwa hba hAa
      ht ih =>
    obtain ⟨ds, hinst, hpt⟩ := ih
    refine ⟨ty₀ :: ds, ?_, ?_⟩
    · simp only [Expr.instPisAt, hinst]
      rfl
    · intro k a v ha hv
      cases k with
      | zero =>
        obtain rfl := Option.some.inj ha
        obtain rfl := Option.some.inj hv
        exact ⟨A, hity, hx⟩
      | succ k =>
        exact hpt k a v (by simpa using ha) (by simpa using hv)

omit [SetTheory V] in
theorem FvarSpine.take {D : Nat} {ρ : Nat → V} :
    ∀ (k : Nat) {as : List Expr} {vs : List V},
      FvarSpine D ρ as vs → FvarSpine D ρ (as.take k) (vs.take k)
  | 0, as, vs, _ => by
    simp only [List.take_zero]
    trivial
  | k + 1, [], vs, h => by
    match vs, h with
    | [], _ =>
      show FvarSpine D ρ [] []
      trivial
  | k + 1, a :: as, vs, h => by
    match vs, h with
    | v :: vs, ⟨ha, h'⟩ =>
      exact ⟨ha, FvarSpine.take k h'⟩

omit [SetTheory V] in
theorem FvarSpine.drop {D : Nat} {ρ : Nat → V} :
    ∀ (k : Nat) {as : List Expr} {vs : List V},
      FvarSpine D ρ as vs → FvarSpine D ρ (as.drop k) (vs.drop k)
  | 0, as, vs, h => by simpa using h
  | k + 1, [], vs, h => by
    match vs, h with
    | [], _ =>
      show FvarSpine D ρ [] []
      trivial
  | k + 1, a :: as, vs, h => by
    match vs, h with
    | v :: vs, ⟨ha, h'⟩ =>
      simpa using FvarSpine.drop k h'

omit [SetTheory V] in
theorem FvarSpine.append {D : Nat} {ρ : Nat → V} :
    ∀ {as bs : List Expr} {vs ws : List V},
      FvarSpine D ρ as vs → FvarSpine D ρ bs ws →
      FvarSpine D ρ (as ++ bs) (vs ++ ws)
  | [], bs, vs, ws, h1, h2 => by
    match vs, h1 with
    | [], _ => simpa using h2
  | a :: as, bs, vs, ws, h1, h2 => by
    match vs, h1 with
    | v :: vs, ⟨ha, h'⟩ =>
      exact ⟨ha, FvarSpine.append h' h2⟩

omit [SetTheory V] in
/-- The variables of `openPisAtFvars` form a spine at any frame whose
valuation carries the values at the consecutive indices. -/
theorem FvarSpine_of_open {n : Nat} {e : Expr} {i₀ : Nat}
    {fvs : List Expr} {body : Expr} {D : Nat} {ρ : Nat → V}
    {vs : List V}
    (h : openPisAtFvars n e i₀ = some (fvs, body))
    (hlen : vs.length = n)
    (hD : i₀ + n ≤ D)
    (hval : ∀ (k : Nat) (v : V), vs[k]? = some v → ρ (i₀ + k) = v) :
    FvarSpine D ρ fvs vs := by
  obtain ⟨-, hfl, hshape⟩ := openPisAtFvars_spec n i₀ h
  clear h
  -- pointwise assembly by induction on the lists
  suffices hgen : ∀ (fvs' : List Expr) (vs' : List V) (off : Nat),
      (∀ (k : Nat) (a : Expr), fvs'[k]? = some a →
        ∃ nm, a = Expr.fvar (i₀ + (off + k)) nm (Expr.fvarTypeD a)) →
      (∀ (k : Nat) (v : V), vs'[k]? = some v → ρ (i₀ + (off + k)) = v) →
      fvs'.length = vs'.length →
      (∀ (k : Nat), k < fvs'.length → i₀ + (off + k) < D) →
      FvarSpine D ρ fvs' vs' by
    refine hgen fvs vs 0 (fun k a ha => by simpa using hshape k a ha)
      (fun k v hv => by simpa using hval k v hv)
      (by omega) ?_
    intro k hk
    omega
  intro fvs'
  induction fvs' with
  | nil =>
    intro vs' off hsh hv hlen' hlt
    match vs', hlen' with
    | [], _ => trivial
  | cons a fvs' ih =>
    intro vs' off hsh hv hlen' hlt
    match vs', hlen' with
    | v :: vs', hlen' =>
      obtain ⟨nm, ha⟩ := hsh 0 a rfl
      refine ⟨⟨i₀ + (off + 0), nm, Expr.fvarTypeD a, ha, ?_, ?_⟩, ?_⟩
      · exact hlt 0 (by simp)
      · exact hv 0 v rfl
      · refine ih vs' (off + 1) ?_ ?_ (by simpa using hlen') ?_
        · intro k b hb
          have := hsh (k + 1) b (by simpa using hb)
          rwa [show i₀ + (off + (k + 1)) = i₀ + (off + 1 + k) from by
            omega] at this
        · intro k w hw
          have := hv (k + 1) w (by simpa using hw)
          rwa [show i₀ + (off + (k + 1)) = i₀ + (off + 1 + k) from by
            omega] at this
        · intro k hk
          have := hlt (k + 1) (by simpa using hk)
          rwa [show i₀ + (off + (k + 1)) = i₀ + (off + 1 + k) from by
            omega] at this

/-- Forward renaming transport for annotation truthfulness. -/
theorem AnnotOk.renameConsts {f : Name → Name}
    (hro : RenameOk cval env f) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      AnnotOk V cval env φ d ρ e →
      AnnotOk V cval env φ d ρ (e.renameConsts f)
  | .forallE n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨haty, hcod, hcond⟩ := ha
    simp only [Expr.renameConsts, AnnotOk]
    refine ⟨AnnotOk.renameConsts hro ty d ρ haty, hcod, ?_⟩
    intro x A hity hx
    rw [interp_renameConsts hro ty d ρ] at hity
    obtain ⟨hbody, hw⟩ := hcond x A hity hx
    have hopen : ((body.renameConsts f).instantiate1
        (.fvar d n (ty.renameConsts f))) =
        (body.instantiate1 (.fvar d n ty)).renameConsts f := by
      rw [Expr.renameConsts_instantiate1]
    constructor
    · rw [hopen]
      exact AnnotOk.renameConsts hro _ (d + 1) (updV V ρ d x) hbody
    · intro v hv
      obtain ⟨w, hwi, hwu⟩ := hw v hv
      refine ⟨w, ?_, hwu⟩
      rw [hopen, interp_renameConsts hro _ (d + 1) (updV V ρ d x)]
      exact hwi
  | .lam n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨haty, hcod, hcond⟩ := ha
    simp only [Expr.renameConsts, AnnotOk]
    refine ⟨AnnotOk.renameConsts hro ty d ρ haty, hcod, ?_⟩
    intro x A hity hx
    rw [interp_renameConsts hro ty d ρ] at hity
    obtain ⟨hbody, hw⟩ := hcond x A hity hx
    have hopen : ((body.renameConsts f).instantiate1
        (.fvar d n (ty.renameConsts f))) =
        (body.instantiate1 (.fvar d n ty)).renameConsts f := by
      rw [Expr.renameConsts_instantiate1]
    constructor
    · rw [hopen]
      exact AnnotOk.renameConsts hro _ (d + 1) (updV V ρ d x) hbody
    · intro v hv
      obtain ⟨w, B, hwi, hwB, hBu⟩ := hw v hv
      refine ⟨w, B, ?_, hwB, hBu⟩
      rw [hopen, interp_renameConsts hro _ (d + 1) (updV V ρ d x)]
      exact hwi
  | .app g a, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨hg, haa, vf, va, vE, A, B, hif, hia, hp, hm, hfib⟩ := ha
    simp only [Expr.renameConsts, AnnotOk]
    refine ⟨AnnotOk.renameConsts hro g d ρ hg,
      AnnotOk.renameConsts hro a d ρ haa,
      vf, va, vE, A, B, ?_, ?_, hp, hm, hfib⟩
    · rw [interp_renameConsts hro g d ρ]; exact hif
    · rw [interp_renameConsts hro a d ρ]; exact hia
  | .proj s i e, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨he, hi2, ve, u, v, A, Bf, hie, hs, hAu, hBf⟩ := ha
    simp only [Expr.renameConsts, AnnotOk]
    refine ⟨AnnotOk.renameConsts hro e d ρ he, hi2,
      ve, u, v, A, Bf, ?_, hs, hAu, hBf⟩
    rw [interp_renameConsts hro e d ρ]
    exact hie
  | .bvar _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .fvar _ _ _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .sort _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .const _ _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .letE _ _ _ _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
  | .lit _, _, _, _ => by simp [Expr.renameConsts, AnnotOk]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-! ## One-sided walks -/

omit [SetTheory V] in
/-- Invert one step of the λ-instantiation walk. -/
theorem instLamsAt_cons_inv {a : Expr} {as : List Expr} {e : Expr}
    {ds : List Expr} {rest : Expr}
    (h : Expr.instLamsAt (a :: as) e = some (ds, rest)) :
    ∃ n dom body m ds', e = .lam n dom body m ∧ ds = dom :: ds' ∧
      Expr.instLamsAt as (body.instantiate1 a) = some (ds', rest) := by
  revert h
  match e with
  | .lam n dom body m => ?_
  | .bvar _ => intro h; exact nomatch h
  | .fvar _ _ _ => intro h; exact nomatch h
  | .sort _ => intro h; exact nomatch h
  | .const _ _ => intro h; exact nomatch h
  | .app _ _ => intro h; exact nomatch h
  | .forallE _ _ _ _ => intro h; exact nomatch h
  | .letE _ _ _ _ => intro h; exact nomatch h
  | .lit _ => intro h; exact nomatch h
  | .proj _ _ _ => intro h; exact nomatch h
  intro h
  simp only [Expr.instLamsAt] at h
  cases h0 : Expr.instLamsAt as (body.instantiate1 a) with
  | none => rw [h0] at h; exact nomatch h
  | some p =>
    rw [h0] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    exact ⟨n, dom, body, m, p.1, rfl, h1.symm, by rw [h0, ← h2]⟩

/-- Build a `∀`-telescope fit at a free-variable frame from pointwise
memberships in the walk's own (instantiated) domains. -/
theorem peel_walk {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {spine : List Expr} {vs : List V} {ty : Expr} {ds : List Expr}
      {rest : Expr},
      Expr.instPisAt spine ty = some (ds, rest) →
      FvarSpine D ρ spine vs →
      (∀ a ∈ spine, WScoped D a) →
      WScoped D ty →
      AnnotOk V cval env φ D ρ ty →
      (∃ P, interpExpr V cval env φ D ρ ty = some P) →
      (∀ (k : Nat) (a : Expr) (v : V), ds[k]? = some a →
        vs[k]? = some v →
        ∃ B, interpExpr V cval env φ D ρ a = some B ∧ v ∈ˢ B) →
      TeleFitI V cval env φ D ρ ty spine vs rest ∧
      (∃ P', interpExpr V cval env φ D ρ rest = some P') := by
  intro spine
  induction spine with
  | nil =>
    intro vs ty ds rest hop hsp hws hW hA hI hmem
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    match vs, hsp with
    | [], _ => exact ⟨TeleFitI.nil, hI⟩
  | cons fv spine' ih =>
    intro vs ty ds rest hop hsp hws hW hA hI hmem
    match vs, hsp with
    | v :: vs', hsp =>
    obtain ⟨⟨i, nfv, tfv, rfl, hiD, hval⟩, hsp'⟩ := hsp
    obtain ⟨n, dom, body, m, ds', rfl, rfl, h0⟩ := instPisAt_cons_inv hop
    have hWd : WScoped D dom ∧ WScoped D body := by
      simpa [WScoped] using hW
    have hA' := hA
    simp only [AnnotOk] at hA'
    obtain ⟨hAdom, ⟨cod, hcod⟩, hcond⟩ := hA'
    obtain ⟨B, hBi, hvB⟩ := hmem 0 dom v rfl rfl
    have hwfv : WScoped D (Expr.fvar i nfv tfv) :=
      hws _ List.mem_cons_self
    have hifv : interpExpr V cval env φ D ρ (.fvar i nfv tfv) = some v := by
      simp only [interpExpr]
      rw [hval]
    obtain ⟨hAop, hfib⟩ := hcond v B hBi hvB
    have hAbody : AnnotOk V cval env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWd.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAop
    obtain ⟨w, hwi, -⟩ := hfib cod hcod
    have hIbody : ∃ P, interpExpr V cval env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) = some P := by
      refine ⟨w, ?_⟩
      rw [interp_beta (n := n) (ty := dom) hWd.2.fvarsBelow hwfv
        (by rfl) hifv 0]
      exact hwi
    obtain ⟨hfit, hIrest⟩ := ih h0 hsp'
      (fun a ha => hws a (List.mem_cons_of_mem _ ha))
      (WScoped.instantiate1_gen hwfv 0 hWd.2) hAbody hIbody
      (fun k a v' ha hv' => hmem (k + 1) a v'
        (show (dom :: ds')[k + 1]? = some a from by simpa using ha)
        (show (v :: vs')[k + 1]? = some v' from by simpa using hv'))
    exact ⟨TeleFitI.cons hBi hifv hvB hWd.2.fvarsBelow hwfv (by rfl)
      (by simp [AnnotOk]) hfit, hIrest⟩

/-- The λ-tower walk: the rule's λ-domains are definitionally the
opening variables' annotations, whose typing packages (`FvarsOk` of
the variables) carry the values' memberships; the values then fit the
λ-tower itself. -/
theorem lam_walk {env : Env} (m : EnvModel V env) (F : Nat)
    {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {spine : List Expr} {vs : List V} {tyL : Expr} {dsL : List Expr}
      {restL : Expr},
      Expr.instLamsAt spine tyL = some (dsL, restL) →
      DefEqListOk F env D (spine.map Expr.fvarTypeD) dsL →
      FvarSpine D ρ spine vs →
      (∀ a ∈ spine, WScoped D a) →
      (∀ a ∈ spine, FvarsOk V m.val env φ D ρ a) →
      (∀ a ∈ spine, Expr.LeavesBounded a) →
      WScoped D tyL → tyL.looseBVarsBounded 0 = true →
      Expr.LeavesBounded tyL → FvarsOk V m.val env φ D ρ tyL →
      AnnotOk V m.val env φ D ρ tyL →
      (∃ L, interpExpr V m.val env φ D ρ tyL = some L) →
      TeleFitLam m.val env φ D ρ tyL spine vs restL := by
  intro spine
  induction spine with
  | nil =>
    intro vs tyL dsL restL hop hde hsp hws hFs hLs hW hb hL hF hA hI
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    match vs, hsp with
    | [], _ => exact TeleFitLam.nil
  | cons fv spine' ih =>
    intro vs tyL dsL restL hop hde hsp hws hFs hLs hW hb hL hF hA hI
    match vs, hsp with
    | v :: vs', hsp =>
    obtain ⟨⟨i, nfv, tfv, rfl, hiD, hval⟩, hsp'⟩ := hsp
    obtain ⟨n, dom, body, m', ds', rfl, rfl, h0⟩ :=
      instLamsAt_cons_inv hop
    -- the λ-side structural facts
    have hWd : WScoped D dom ∧ WScoped D body := by
      simpa [WScoped] using hW
    have hbd : dom.looseBVarsBounded 0 = true ∧
        body.looseBVarsBounded 1 = true := by
      revert hb; simp [Expr.looseBVarsBounded]
    have hLdom : Expr.LeavesBounded dom := by
      intro l hl
      exact hL l (by simp only [fvarLeaves, List.mem_append]
                     exact Or.inl hl)
    have hLbody : Expr.LeavesBounded body := by
      intro l hl
      exact hL l (by simp only [fvarLeaves, List.mem_append]
                     exact Or.inr hl)
    have hFdom : FvarsOk V m.val env φ D ρ dom :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hF
    have hA' := hA
    simp only [AnnotOk] at hA'
    obtain ⟨hAdom, ⟨cod, hcod⟩, hcond⟩ := hA'
    -- the opening variable's package
    have hFfv := hFs _ List.mem_cons_self
    have hhead := hFfv (i, nfv, tfv) (by simp [fvarLeaves])
    obtain ⟨-, hAann, T, hTi, hvT⟩ := hhead
    rw [hval] at hvT
    have hWann : WScoped D tfv := by
      have := hws _ List.mem_cons_self
      have h2 : i < D ∧ WScoped i tfv := by simpa [WScoped] using this
      exact h2.2.mono (by omega)
    have hLann : Expr.LeavesBounded tfv := by
      intro l hl
      exact hLs _ List.mem_cons_self l (by
        simp only [fvarLeaves, List.mem_cons]
        exact Or.inr hl)
    have hbann : tfv.looseBVarsBounded 0 = true := by
      have := hLs _ List.mem_cons_self (i, nfv, tfv)
        (by simp [fvarLeaves])
      exact this
    have hFann : FvarsOk V m.val env φ D ρ tfv :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_cons]
        exact Or.inr hl) hFfv
    -- λ-domain interpretation is defined
    obtain ⟨L, hLi⟩ := hI
    have hIdom : ∃ A, interpExpr V m.val env φ D ρ dom = some A := by
      revert hLi
      simp only [interpExpr, hcod]
      cases hd : interpExpr V m.val env φ D ρ dom with
      | none => intro hLi; exact nomatch hLi
      | some A => intro _; exact ⟨A, rfl⟩
    obtain ⟨A, hAi⟩ := hIdom
    -- the defeq identifies the λ-domain with the annotation
    have hde0 : isDefEqCore env F D tfv dom = .ok true := by
      rw [List.map_cons] at hde
      exact hde.1
    have hTA : T = A :=
      isDefEqCore_sound m F hde0 hWann hWd.1 hbann hbd.1 hLann hLdom
        hFann hFdom hAann hAdom hTi hAi
    have hvA : v ∈ˢ A := by rw [← hTA]; exact hvT
    -- step the body
    have hwfv : WScoped D (Expr.fvar i nfv tfv) :=
      hws _ List.mem_cons_self
    have hifv : interpExpr V m.val env φ D ρ (.fvar i nfv tfv) =
        some v := by
      simp only [interpExpr]
      rw [hval]
    obtain ⟨hAop, hfib⟩ := hcond v A hAi hvA
    have hAbody : AnnotOk V m.val env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWd.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAop
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hfib cod hcod
    have hIbody : ∃ P, interpExpr V m.val env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) = some P := by
      refine ⟨w, ?_⟩
      rw [interp_beta (n := n) (ty := dom) hWd.2.fvarsBelow hwfv
        (by rfl) hifv 0]
      exact hwi
    have hLfv : Expr.LeavesBounded (Expr.fvar i nfv tfv) :=
      hLs _ List.mem_cons_self
    refine TeleFitLam.cons hAi hifv hvA hWd.2.fvarsBelow hwfv (by rfl)
      (by simp [AnnotOk]) ?_
    refine ih h0 (by
        rw [List.map_cons] at hde
        exact hde.2) hsp'
      (fun a ha => hws a (List.mem_cons_of_mem _ ha))
      (fun a ha => hFs a (List.mem_cons_of_mem _ ha))
      (fun a ha => hLs a (List.mem_cons_of_mem _ ha))
      (WScoped.instantiate1_gen hwfv 0 hWd.2)
      (looseBVarsBounded_instantiate1_gen (by rfl) hbd.2)
      (LeavesBounded.instantiate1 hLbody hLfv)
      (fun l hl => by
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact hF l (by
            simp only [fvarLeaves, List.mem_append]
            exact Or.inr hl')
        · exact hFfv l hl')
      hAbody hIbody

/-! ## More telescope bookkeeping -/

omit [SetTheory V] in
/-- Forward composition of instantiation walks. -/
theorem instPisAt_append_of :
    ∀ (as : List Expr) {bs : List Expr} {e : Expr} {ds₁ ds₂ : List Expr}
      {mid rest : Expr},
      Expr.instPisAt as e = some (ds₁, mid) →
      Expr.instPisAt bs mid = some (ds₂, rest) →
      Expr.instPisAt (as ++ bs) e = some (ds₁ ++ ds₂, rest)
  | [], bs, e, ds₁, ds₂, mid, rest, h1, h2 => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simpa using h2
  | a :: as, bs, e, ds₁, ds₂, mid, rest, h1, h2 => by
    obtain ⟨n, dom, body, m, ds', rfl, rfl, h0⟩ := instPisAt_cons_inv h1
    have := instPisAt_append_of as h0 h2
    simp only [List.cons_append, Expr.instPisAt, this]
    rfl

omit [SetTheory V] in
/-- A telescope that strips syntactically admits any instantiation
walk of matching length. -/
theorem instPisAt_isSome_of_stripPis :
    ∀ (args : List Expr) {e : Expr},
      (e.stripPis args.length).isSome = true →
      (Expr.instPisAt args e).isSome = true
  | [], e, _ => by simp [Expr.instPisAt]
  | a :: as, e, h => by
    match e, h with
    | .forallE n dom body m, h =>
      simp only [List.length_cons, Expr.stripPis, Option.isSome_map] at h
      have h' : ((body.instantiate1 a).stripPis as.length).isSome = true :=
        Expr.stripPis_instantiate1_isSome as.length 0 h
      have := instPisAt_isSome_of_stripPis as h'
      simp only [Expr.instPisAt, Option.isSome_map]
      exact this

omit [SetTheory V] in
/-- Scoping of an instantiation walk's domains and residual. -/
theorem instPisAt_wscoped {D : Nat} :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instPisAt args e = some (ds, rest) →
      WScoped D e → (∀ a ∈ args, WScoped D a) →
      (∀ dEl ∈ ds, WScoped D dEl) ∧ WScoped D rest
  | [], e, ds, rest, h, hW, _ => by
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hW⟩
  | a :: as, e, ds, rest, h, hW, hargs => by
    obtain ⟨n, dom, body, m, ds', rfl, rfl, h0⟩ := instPisAt_cons_inv h
    have hW' : WScoped D dom ∧ WScoped D body := by
      simpa [WScoped] using hW
    have hrec := instPisAt_wscoped as h0
      (WScoped.instantiate1_gen (hargs a List.mem_cons_self) 0 hW'.2)
      (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
    refine ⟨?_, hrec.2⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hW'.1
    · exact hrec.1 x hx

omit [SetTheory V] in
/-- Well-formedness of the opened variables: scoping, closed
annotations, bounded leaf annotations. -/
theorem openPisAtFvars_wf :
    ∀ (n : Nat) {e : Expr} (i₀ : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i₀ = some (fvs, body) →
      WScoped i₀ e → e.looseBVarsBounded 0 = true →
      Expr.LeavesBounded e →
      (∀ a ∈ fvs, WScoped (i₀ + n) a ∧ a.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded a) ∧
      (WScoped (i₀ + n) body ∧ body.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded body)
  | 0, e, i₀, fvs, body, h, hW, hb, hL => by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun a ha => nomatch ha), by simpa using hW, hb, hL⟩
  | n + 1, e, i₀, fvs, body, h, hW, hb, hL => by
    match e, h with
    | .forallE nm dom bodyE m, h =>
      simp only [openPisAtFvars] at h
      cases h0 : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i₀ nm dom)) (i₀ + 1) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hfvs, hbody⟩ := h
        subst hfvs hbody
        have hW' : WScoped i₀ dom ∧ WScoped i₀ bodyE := by
          simpa [WScoped] using hW
        have hb' : dom.looseBVarsBounded 0 = true ∧
            bodyE.looseBVarsBounded 1 = true := by
          revert hb; simp [Expr.looseBVarsBounded]
        have hLd := LeavesBounded.of_forallE_ty hL
        have hLb := LeavesBounded.of_forallE_body hL
        have hfvW : WScoped (i₀ + 1) (Expr.fvar i₀ nm dom) := by
          simp only [WScoped]
          exact ⟨by omega, hW'.1⟩
        have hfvL : Expr.LeavesBounded (Expr.fvar i₀ nm dom) :=
          LeavesBounded.fvar hb'.1 hLd
        have hrec := openPisAtFvars_wf n (i₀ + 1) h0
          (WScoped.instantiate1_gen hfvW 0 (hW'.2.mono (by omega)))
          (looseBVarsBounded_instantiate1_gen (by rfl) hb'.2)
          (LeavesBounded.instantiate1 hLb hfvL)
        refine ⟨?_, ?_⟩
        · intro a ha
          rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨hfvW.mono (by omega), by rfl, hfvL⟩
          · obtain ⟨h1, h2, h3⟩ := hrec.1 a ha
            exact ⟨h1.mono (by omega), h2, h3⟩
        · obtain ⟨h1, h2, h3⟩ := hrec.2
          exact ⟨h1.mono (by omega), h2, h3⟩

/-- Extract a value spine from an all-`fvar` fit. -/
theorem FvarSpine_of_fit {D : Nat} {ρ : Nat → V} :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ D ρ ty args vs rest →
      (∀ a ∈ args, ∃ i n t, a = .fvar i n t) →
      FvarSpine D ρ args vs := by
  intro ty args vs rest h
  induction h with
  | nil => intro _; trivial
  | @cons n ty₀ body m arg args x xs A rest hity hiarg hx hfb hwa hba hAa
      ht ih =>
    intro hshape
    obtain ⟨i, nm, t, rfl⟩ := hshape _ List.mem_cons_self
    have hiD : i < D := by
      have h2 : i < D ∧ WScoped i t := by simpa [WScoped] using hwa
      exact h2.1
    have hval : ρ i = x := by
      have : interpExpr V cval env φ D ρ (.fvar i nm t) = some (ρ i) := by
        simp [interpExpr]
      rw [this] at hiarg
      exact Option.some.inj hiarg
    exact ⟨⟨i, nm, t, rfl, hiD, hval⟩,
      ih (fun a ha => hshape a (List.mem_cons_of_mem _ ha))⟩

/-- Transfer a fit's pointwise domain memberships onto another
free-variable spine with the same values: the instantiated domains of
a closed telescope interpret equally at both frames. -/
theorem fit_mem_transfer {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
    {ty : Expr} {n : Nat} {bs : List (Name × Expr × BinderMeta)}
    {body : Expr} {spine₁ : List Expr} {ds₁ : List Expr} {rest₁ : Expr}
    {spine₂ : List Expr} {vs : List V} {rest₂ : Expr}
    (hcl : ty.hasFvar = false)
    (hty0 : ty.looseBVarsBounded 0 = true)
    (hstrip : ty.stripPis n = some (bs, body))
    (hinst₁ : Expr.instPisAt spine₁ ty = some (ds₁, rest₁))
    (hlen₁ : spine₁.length = n)
    (hsp₁ : FvarSpine D₁ ρ₁ spine₁ vs)
    (hsp₂ : FvarSpine D₂ ρ₂ spine₂ vs)
    (hfit : TeleFitI V cval env φ D₂ ρ₂ ty spine₂ vs rest₂) :
    ∀ (k : Nat) (a : Expr) (v : V), ds₁[k]? = some a → vs[k]? = some v →
      ∃ B, interpExpr V cval env φ D₁ ρ₁ a = some B ∧ v ∈ˢ B := by
  have hlen₂ : spine₂.length = n := by
    rw [FvarSpine.length hsp₂, ← FvarSpine.length hsp₁, hlen₁]
  obtain ⟨ds₂, hinst₂, hpt⟩ := TeleFitI.toInstPisAt hfit
  obtain ⟨-, hds₁⟩ := instPisAt_stripPis spine₁ hinst₁
    (by rw [hlen₁]; exact hstrip)
  obtain ⟨-, hds₂⟩ := instPisAt_stripPis spine₂ hinst₂
    (by rw [hlen₂]; exact hstrip)
  intro k a v ha hv
  have hkn : k < n := by
    have hdl := instPisAt_length spine₁ hinst₁
    rcases Nat.lt_or_ge k n with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none (by omega)] at ha
      exact nomatch ha
  obtain ⟨b, hb⟩ : ∃ b, bs[k]? = some b := by
    have := Expr.stripPis_length n hstrip
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have ha' := hds₁ k b hb
  rw [ha] at ha'
  obtain rfl := Option.some.inj ha'
  obtain ⟨a₂, ha₂⟩ : ∃ a₂, ds₂[k]? = some a₂ := by
    have := instPisAt_length spine₂ hinst₂
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨B, hBi, hvB⟩ := hpt k a₂ v ha₂ hv
  have ha₂' := hds₂ k b hb
  rw [ha₂] at ha₂'
  obtain rfl := Option.some.inj ha₂'
  refine ⟨B, ?_, hvB⟩
  have hdomcl : b.2.1.hasFvar = false :=
    stripPis_doms_hasFvar n hstrip hcl b (List.mem_of_getElem? hb)
  have hdombd : b.2.1.looseBVarsBounded k = true := by
    have := stripPis_doms_bounded n 0 hstrip hty0 k b hb
    simpa using this
  have ht1 : (spine₁.take k).length = k := by
    rw [List.length_take, hlen₁]; omega
  have ht2 : (spine₂.take k).length = k := by
    rw [List.length_take, hlen₂]; omega
  have hcong := interp_instSeq_fvarFrames (cval := cval) (env := env)
    (φ := φ) (e := b.2.1) hdomcl (by rw [ht1]; exact hdombd)
    (FvarSpine.take k hsp₁) (FvarSpine.take k hsp₂)
  rw [ht1, ht2] at hcong
  rw [hcong]
  exact hBi

/-- One-sided variant of `pi_walk`: the telescope's walk domains are
the opening variables' annotations, memberships are given directly,
and every opening variable's typing package is established. -/
theorem self_walk {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {spine : List Expr} {vs : List V} {ty : Expr} {rest : Expr},
      Expr.instPisAt spine ty = some (spine.map Expr.fvarTypeD, rest) →
      FvarSpine D ρ spine vs →
      (∀ a ∈ spine, WScoped D a) →
      WScoped D ty → ty.looseBVarsBounded 0 = true →
      Expr.LeavesBounded ty → FvarsOk V cval env φ D ρ ty →
      AnnotOk V cval env φ D ρ ty →
      (∀ (k : Nat) (a : Expr) (v : V),
        (spine.map Expr.fvarTypeD)[k]? = some a → vs[k]? = some v →
        ∃ B, interpExpr V cval env φ D ρ a = some B ∧ v ∈ˢ B) →
      TeleFitI V cval env φ D ρ ty spine vs rest ∧
      (∀ a ∈ spine, FvarsOk V cval env φ D ρ a) := by
  intro spine
  induction spine with
  | nil =>
    intro vs ty rest hop hsp hws hW hb hL hF hA hmem
    simp only [List.map_nil, Expr.instPisAt, Option.some.injEq,
      Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    match vs, hsp with
    | [], _ => exact ⟨TeleFitI.nil, fun a ha => nomatch ha⟩
  | cons fv spine' ih =>
    intro vs ty rest hop hsp hws hW hb hL hF hA hmem
    match vs, hsp with
    | v :: vs', hsp =>
    obtain ⟨⟨i, nfv, tfv, rfl, hiD, hval⟩, hsp'⟩ := hsp
    obtain ⟨n, dom, body, m, ds', rfl, hdsS, h0⟩ := instPisAt_cons_inv hop
    have hdomS : dom = tfv ∧ ds' = spine'.map Expr.fvarTypeD := by
      rw [List.map_cons] at hdsS
      injection hdsS with h1 h2
      exact ⟨h1.symm, h2.symm⟩
    obtain ⟨hdomS1, rfl⟩ := hdomS
    subst dom
    have hWd : WScoped D tfv ∧ WScoped D body := by
      simpa [WScoped] using hW
    have hbd : tfv.looseBVarsBounded 0 = true ∧
        body.looseBVarsBounded 1 = true := by
      revert hb; simp [Expr.looseBVarsBounded]
    have hLdom := LeavesBounded.of_forallE_ty hL
    have hFdom : FvarsOk V cval env φ D ρ tfv :=
      FvarsOk.of_subset (fun l hl => by
        simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hF
    have hA' := hA
    simp only [AnnotOk] at hA'
    obtain ⟨hAdom, ⟨cod, hcod⟩, hcond⟩ := hA'
    obtain ⟨B, hBi, hvB⟩ := hmem 0 tfv v (by simp [Expr.fvarTypeD]) rfl
    have hwfv : WScoped D (Expr.fvar i nfv tfv) :=
      hws _ List.mem_cons_self
    have hifv : interpExpr V cval env φ D ρ (.fvar i nfv tfv) = some v := by
      simp only [interpExpr]
      rw [hval]
    have hFfv : FvarsOk V cval env φ D ρ (.fvar i nfv tfv) := by
      intro l hl
      simp only [fvarLeaves, List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact ⟨hiD, hAdom, B, hBi, by rw [hval]; exact hvB⟩
      · exact hFdom l hl
    have hLfv : Expr.LeavesBounded (.fvar i nfv tfv) :=
      LeavesBounded.fvar hbd.1 hLdom
    obtain ⟨hAop, hfib⟩ := hcond v B hBi hvB
    have hAbody : AnnotOk V cval env φ D ρ
        (body.instantiate1 (.fvar i nfv tfv)) :=
      AnnotOk_beta hWd.2.fvarsBelow hwfv (by rfl) hifv
        (by simp [AnnotOk]) 0 hAop
    obtain ⟨hfit, hspineF⟩ := ih h0 hsp'
      (fun a ha => hws a (List.mem_cons_of_mem _ ha))
      (WScoped.instantiate1_gen hwfv 0 hWd.2)
      (looseBVarsBounded_instantiate1_gen (by rfl) hbd.2)
      (LeavesBounded.instantiate1 (LeavesBounded.of_forallE_body hL) hLfv)
      (fun l hl => by
        rcases fvarLeaves_instantiate1 body 0 hl with hl' | hl'
        · exact hF l (by
            simp only [fvarLeaves, List.mem_append]
            exact Or.inr hl')
        · exact hFfv l hl')
      hAbody
      (fun k a v' ha hv' => hmem (k + 1) a v'
        (show ((Expr.fvar i nfv tfv :: spine').map
            Expr.fvarTypeD)[k + 1]? = some a from by simpa using ha)
        (show (v :: vs')[k + 1]? = some v' from by simpa using hv'))
    refine ⟨TeleFitI.cons hBi hifv hvB hWd.2.fvarsBelow hwfv (by rfl)
      (by simp [AnnotOk]) hfit, ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hFfv
    · exact hspineF a ha


/-- Renaming inside an opening-variable instantiation sequence is
interpretation-invariant. -/
theorem interp_instSeq_ren {f : Name → Name} (hro : RenameOk cval env f)
    {spine : List Expr} {t : Nat} {X : Expr} {D : Nat} {ρ : Nat → V}
    (hfv : ∀ a ∈ spine, ∃ i nm ty, a = .fvar i nm ty) :
    interpExpr V cval env φ D ρ (instSeq spine t (X.renameConsts f)) =
    interpExpr V cval env φ D ρ (instSeq spine t X) := by
  have hee := instSeq_renameConsts (f := f) spine t (X := X)
    (fun a ha => by
      obtain ⟨i, nm, ty, rfl⟩ := hfv a ha
      exact rfl)
  rw [← interp_erasedEq hee D ρ]
  exact interp_renameConsts hro _ D ρ


omit [SetTheory V] in
theorem looseBVarsBounded_renameConsts {f : Name → Name} :
    ∀ (e : Expr) (k : Nat),
      (e.renameConsts f).looseBVarsBounded k = e.looseBVarsBounded k := by
  intro e
  induction e <;> intro k <;>
    simp_all [Expr.renameConsts, Expr.looseBVarsBounded]


omit [SetTheory V] in
theorem renameConsts_mkAppN {f : Name → Name} :
    ∀ (xs : List Expr) (h : Expr),
      (Expr.mkAppN h xs).renameConsts f =
        Expr.mkAppN (h.renameConsts f) (xs.map (·.renameConsts f))
  | [], h => rfl
  | x :: xs, h => by
    show (Expr.mkAppN (.app h x) xs).renameConsts f = _
    rw [renameConsts_mkAppN xs (.app h x)]
    rfl

/-- A free-variable spine interprets pointwise to its values. -/
theorem InterpSpine_of_FvarSpine {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V}, FvarSpine D ρ as vs →
      InterpSpine cval env φ D ρ as vs
  | [], [], _ => trivial
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | a :: as, v :: vs, h => by
    obtain ⟨⟨i, n, ty, rfl, hiD, hval⟩, h'⟩ := h
    exact ⟨by simp [interpExpr, hval], InterpSpine_of_FvarSpine h'⟩


theorem InterpSpine.pointwise {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V},
      InterpSpine cval env φ D ρ as vs →
      ∀ (k : Nat) {a : Expr} {v : V}, as[k]? = some a → vs[k]? = some v →
        interpExpr V cval env φ D ρ a = some v
  | [], [], _, k, a, v, ha, _ => nomatch ha
  | [], _ :: _, h, _, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _, _ => nomatch h
  | a₀ :: as, v₀ :: vs, h, k, a, v, ha, hv => by
    cases k with
    | zero =>
      obtain rfl := Option.some.inj ha
      obtain rfl := Option.some.inj hv
      exact h.1
    | succ k =>
      exact InterpSpine.pointwise h.2 k (by simpa using ha)
        (by simpa using hv)

theorem InterpSpine.of_pointwise {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V},
      as.length = vs.length →
      (∀ (k : Nat) (a : Expr) (v : V), as[k]? = some a →
        vs[k]? = some v → interpExpr V cval env φ D ρ a = some v) →
      InterpSpine cval env φ D ρ as vs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | a₀ :: as, v₀ :: vs, hlen, hpt => by
    refine ⟨hpt 0 a₀ v₀ rfl rfl, ?_⟩
    exact InterpSpine.of_pointwise (by simpa using hlen)
      (fun k a v ha hv => hpt (k + 1) a v (by simpa using ha)
        (by simpa using hv))


omit [SetTheory V] in
/-- A canonical rule's constructor parameters are among the recursor's
prefix. -/
theorem recRulePlain_le {recTy : Expr} {nP nM nm ni cnP : Nat}
    (h : Expr.recRulePlain recTy nP nM nm ni cnP = true) :
    cnP ≤ nP + nM + nm := by
  rw [Expr.recRulePlain, Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

omit [SetTheory V] in
/-- A canonical rule pins the recursor type's telescope. -/
theorem recRulePlain_strip {recTy : Expr} {nP nM nm ni cnP : Nat}
    (h : Expr.recRulePlain recTy nP nM nm ni cnP = true) :
    (recTy.stripPis (nP + nM + nm + ni)).isSome = true := by
  rw [Expr.recRulePlain, Bool.and_eq_true] at h
  have h2 := h.2
  revert h2
  cases hs : recTy.stripPis (nP + nM + nm + ni) with
  | none => intro h2; exact nomatch h2
  | some p => intro _; rfl

end Setlec
