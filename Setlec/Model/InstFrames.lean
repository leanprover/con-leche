import Setlec.Model.RuleTower
import Setlec.Verify.InstSpine
import Setlec.Verify.InferLeaves

/-!
# Cross-frame value-determinedness of instantiation sequences

The interpretation of a closed expression instantiated along an
argument spine is determined by the spine's *values*: relocated from
`Setlec/Model/IotaWalk.lean` so the iota step's soundness
(`Setlec/Model/Core/Iota.lean`, upstream of the claims layer) can
consume it, and generalized from free-variable spines to arbitrary
argument spines with interpreted values (`interp_instSeq_frames`) —
the one frame-crossing device the λ-tower contract's consumers keep.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {cval : ConstVal V} {env : Env}
  {φ : Name → Nat}

open SetTheory Expr

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

-- (`FvarSpine` itself now lives next to `RecRulesOk` in
-- `Setlec/Model/Interp.lean`; its lemmas stay here.)

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


/-! ## Cross-frame congruence for arbitrary argument spines -/

omit [SetTheory V] in
/-- `instSeq` keeps terms well-scoped (the `instSpine` fact under the
verification spelling). -/
theorem instSeq_wscoped {D : Nat} {args : List Expr} (t : Nat) {e : Expr}
    (he : WScoped D e) (hargs : ∀ a ∈ args, WScoped D a) :
    WScoped D (instSeq args t e) := by
  rw [← Expr.instSpine_eq_instSeq]
  exact instSpine_WScoped t he hargs

omit [SetTheory V] in
/-- A full-telescope `instSeq` at bvar-closed arguments closes a
bounded base. -/
theorem instSeq_bclosed {args : List Expr} {e : Expr}
    (hargs : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (he : e.looseBVarsBounded args.length = true) :
    (instSeq args (args.length - 1) e).looseBVarsBounded 0 = true := by
  rw [← Expr.instSpine_eq_instSeq]
  exact instSpine_closed hargs he

/-- A fresh free-variable spine carrying given values above a frame:
`o, o+1, …` with sort-zero annotations, `Dtop` the target frame. -/
theorem fresh_spine_exists {Dtop : Nat} {ρF : Nat → V} :
    ∀ (vs : List V) (o : Nat),
      (∀ (j : Nat) (v : V), vs[j]? = some v → ρF (o + j) = v) →
      o + vs.length ≤ Dtop →
      ∃ spineF : List Expr,
        FvarSpine Dtop ρF spineF vs ∧
        spineF.length = vs.length ∧
        (∀ a ∈ spineF, ∃ i nm, a = .fvar i nm (.sort .zero)) ∧
        InstArgs cval env φ Dtop ρF spineF vs := by
  intro vs
  induction vs with
  | nil =>
    intro o _ _
    exact ⟨[], trivial, rfl, fun a ha => by simp at ha, trivial⟩
  | cons v vs ih =>
    intro o hval hle
    obtain ⟨spineF, hfs, hlen, hsh, hia⟩ := ih (o + 1)
      (fun j w hw => by
        have := hval (j + 1) w (by simpa using hw)
        rwa [show o + (j + 1) = o + 1 + j from by omega] at this)
      (by simp at hle ⊢; omega)
    have hv0 : ρF o = v := by
      have := hval 0 v (by simp)
      simpa using this
    refine ⟨.fvar o .anonymous (.sort .zero) :: spineF, ?_,
      by simpa using hlen, ?_, ?_⟩
    · exact ⟨⟨o, .anonymous, .sort .zero, rfl, by simp at hle; omega, hv0⟩,
        hfs⟩
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨o, .anonymous, rfl⟩
      · exact hsh a ha
    · refine ⟨⟨?_, rfl, ?_⟩, hia⟩
      · simp only [WScoped]
        exact ⟨by simp at hle; omega, trivial⟩
      · simp only [interpExpr]
        rw [hv0]

/-- The lifted valuation of `interp_instSeq_fresh`: below the frame
the original valuation, above it the values. -/
def liftVal (D : Nat) (ρ : Nat → V) (vs : List V) : Nat → V :=
  fun i => if i < D then ρ i else vs.getD (i - D) SetTheory.empty

/-- One side of the frame-crossing: an instantiation sequence at
arbitrary arguments equals the same sequence at a fresh spine above
the frame, carrying the same values. -/
theorem interp_instSeq_fresh {D : Nat} {ρ : Nat → V}
    {args : List Expr} {vs : List V} {e : Expr}
    (h : InstArgs cval env φ D ρ args vs)
    (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded args.length = true) :
    ∃ spineF : List Expr,
      FvarSpine (D + vs.length) (liftVal (V := V) D ρ vs) spineF vs ∧
      spineF.length = vs.length ∧
      (∀ a ∈ spineF, ∃ i nm, a = .fvar i nm (.sort .zero)) ∧
      interpExpr V cval env φ D ρ (instSeq args (args.length - 1) e) =
        interpExpr V cval env φ (D + vs.length) (liftVal (V := V) D ρ vs)
          (instSeq spineF (spineF.length - 1) e) := by
  have hlen := InstArgs.length h
  have hagr : ∀ i, i < D → liftVal (V := V) D ρ vs i = ρ i := by
    intro i hi
    simp [liftVal, hi]
  obtain ⟨spineF, hfs, hlenF, hshF, hiaF⟩ :=
    fresh_spine_exists (cval := cval) (env := env) (φ := φ)
      (Dtop := D + vs.length) (ρF := liftVal (V := V) D ρ vs) vs D
      (fun j v hv => by
        have hj : j < vs.length := by
          rcases Nat.lt_or_ge j vs.length with hlt | hge
          · exact hlt
          · rw [List.getElem?_eq_none (by omega)] at hv
            exact nomatch hv
        show (if D + j < D then ρ (D + j) else
          vs.getD (D + j - D) SetTheory.empty) = v
        rw [if_neg (by omega), Nat.add_sub_cancel_left,
          List.getD_eq_getElem?_getD, hv]
        rfl)
      (by omega)
  have hiaA : InstArgs cval env φ (D + vs.length)
      (liftVal (V := V) D ρ vs) args vs :=
    InstArgs.lift h (by omega) hagr
  have hwX : WScoped D (instSeq args (args.length - 1) e) :=
    instSeq_wscoped _ (WScoped.of_not_hasFvar hcl)
      (fun a ha => InstArgs.wscoped h a ha)
  refine ⟨spineF, hfs, hlenF, hshF, ?_⟩
  rw [← interp_lift hwX (D + vs.length) (by omega) ρ
    (liftVal (V := V) D ρ vs) hagr]
  exact interp_instSeq_congr hiaA hiaF
    (WScoped.of_not_hasFvar hcl).fvarsBelow hb

/-- Interpretation of an instantiation sequence of a **closed**
expression is determined by the argument *values*, across frames: two
argument spines with pointwise equal interpreted values — at possibly
unrelated depths and valuations — yield equal interpretations.  The
one frame-crossing device the λ-tower contract's consumers keep. -/
theorem interp_instSeq_frames {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
    {args₁ args₂ : List Expr} {vs : List V} {e : Expr}
    (h₁ : InstArgs cval env φ D₁ ρ₁ args₁ vs)
    (h₂ : InstArgs cval env φ D₂ ρ₂ args₂ vs)
    (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded args₁.length = true) :
    interpExpr V cval env φ D₁ ρ₁ (instSeq args₁ (args₁.length - 1) e) =
    interpExpr V cval env φ D₂ ρ₂ (instSeq args₂ (args₂.length - 1) e) := by
  obtain ⟨sF₁, hfs₁, hlen₁, -, heq₁⟩ := interp_instSeq_fresh h₁ hcl hb
  obtain ⟨sF₂, hfs₂, hlen₂, -, heq₂⟩ := interp_instSeq_fresh h₂ hcl
    (by rw [InstArgs.length h₂, ← InstArgs.length h₁]; exact hb)
  rw [heq₁, heq₂]
  exact interp_instSeq_fvarFrames hcl
    (by rw [hlen₁, ← InstArgs.length h₁]; exact hb) hfs₁ hfs₂

/-! ## The canonical extension frame, characterized -/

omit [SetTheory V] cval env φ in
theorem snocFrame_fst :
    ∀ (xs : List V) (d : Nat) (ρ : Nat → V),
      (snocFrame (V := V) d ρ xs).1 = d + xs.length := by
  intro xs
  induction xs with
  | nil => intro d ρ; simp [snocFrame]
  | cons x xs ih =>
    intro d ρ
    show (snocFrame (V := V) (d + 1) (updV V ρ d x) xs).1 = _
    rw [ih]
    simp
    omega

omit [SetTheory V] cval env φ in
theorem snocFrame_snd_lt :
    ∀ (xs : List V) (d : Nat) (ρ : Nat → V) (i : Nat), i < d →
      (snocFrame (V := V) d ρ xs).2 i = ρ i := by
  intro xs
  induction xs with
  | nil => intro d ρ i _; rfl
  | cons x xs ih =>
    intro d ρ i hi
    show (snocFrame (V := V) (d + 1) (updV V ρ d x) xs).2 i = ρ i
    rw [ih _ _ _ (by omega)]
    simp only [updV]
    rw [if_neg (by omega)]

omit [SetTheory V] cval env φ in
theorem snocFrame_snd_get :
    ∀ (xs : List V) (d : Nat) (ρ : Nat → V) (j : Nat) (x : V),
      xs[j]? = some x →
      (snocFrame (V := V) d ρ xs).2 (d + j) = x := by
  intro xs
  induction xs with
  | nil =>
    intro d ρ j x hx
    exact nomatch hx
  | cons y xs ih =>
    intro d ρ j x hx
    cases j with
    | zero =>
      have hyx : y = x := by simpa using hx
      show (snocFrame (V := V) (d + 1) (updV V ρ d y) xs).2 (d + 0) = x
      rw [snocFrame_snd_lt _ _ _ _ (by omega)]
      simp [updV, hyx]
    | succ j =>
      show (snocFrame (V := V) (d + 1) (updV V ρ d y) xs).2 (d + (j + 1)) = x
      rw [show d + (j + 1) = (d + 1) + j from by omega]
      exact ih _ _ j x (by simpa using hx)

/-! ## Characterizing the kernel's telescope openers (relocated) -/

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
/-- Split a λ-instantiation walk along a list append. -/
theorem instLamsAt_append :
    ∀ (as bs : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instLamsAt (as ++ bs) e = some (ds, rest) →
      ∃ ds₁ mid ds₂, Expr.instLamsAt as e = some (ds₁, mid) ∧
        Expr.instLamsAt bs mid = some (ds₂, rest) ∧ ds = ds₁ ++ ds₂
  | [], bs, e, ds, rest, h => ⟨[], e, ds, rfl, h, rfl⟩
  | a :: as, bs, e, ds, rest, h => by
    match e, h with
    | .lam n dom body m, h =>
      simp only [List.cons_append, Expr.instLamsAt] at h
      cases h0 : Expr.instLamsAt (as ++ bs) (body.instantiate1 a) with
      | none => rw [h0] at h; exact nomatch h
      | some p =>
        rw [h0] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨hds, hrest⟩ : dom :: p.1 = ds ∧ p.2 = rest := by
          cases h; exact ⟨rfl, rfl⟩
        subst hds hrest
        obtain ⟨ds₁, mid, ds₂, h1, h2, h3⟩ :=
          instLamsAt_append as bs (by rw [h0])
        refine ⟨dom :: ds₁, mid, ds₂, ?_, h2, by rw [h3]; rfl⟩
        simp only [Expr.instLamsAt, h1]
        rfl

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
/-- λ-version of `instPisAt_wscoped`. -/
theorem instLamsAt_wscoped {D : Nat} :
    ∀ (args : List Expr) {e : Expr} {ds : List Expr} {rest : Expr},
      Expr.instLamsAt args e = some (ds, rest) →
      WScoped D e → (∀ a ∈ args, WScoped D a) →
      (∀ dEl ∈ ds, WScoped D dEl) ∧ WScoped D rest
  | [], e, ds, rest, h, hW, _ => by
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hW⟩
  | a :: as, e, ds, rest, h, hW, hargs => by
    obtain ⟨n, dom, body, m, ds', rfl, rfl, h0⟩ := instLamsAt_cons_inv h
    have hW' : WScoped D dom ∧ WScoped D body := by
      simpa [WScoped] using hW
    have hrec := instLamsAt_wscoped as h0
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



/-- The universal frame-and-level bridge: an instantiation sequence of
a closed, parameter-defined expression — level-instantiated
differently on each side — interprets equally across frames, spines
and level assignments whenever the two spines carry the same values
and the composed assignments agree on the expression's own
parameters.  Both sides normalize onto fresh sort-zero-annotated
variable spines, where level instantiation commutes syntactically and
the parameter-extensionality of the interpretation applies. -/
theorem interp_instSeq_swap₂ (hcp : ConstValParams cval env)
    {ψ : Name → Nat} {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
    {args₁ args₂ : List Expr} {vs : List V} {e : Expr}
    {ks₁ ks₂ : List Name} {us₁ us₂ : List Level} {ps : List Name}
    (h₁ : InstArgs cval env ψ D₁ ρ₁ args₁ vs)
    (h₂ : InstArgs cval env φ D₂ ρ₂ args₂ vs)
    (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded args₁.length = true)
    (hps : e.allLevelParamsDefined ps = true)
    (hφψ : ∀ p ∈ ps,
      Level.substFn ψ ks₁ us₁ p = Level.substFn φ ks₂ us₂ p) :
    interpExpr V cval env ψ D₁ ρ₁
      (instSeq args₁ (args₁.length - 1)
        (e.instantiateLevelParams ks₁ us₁)) =
    interpExpr V cval env φ D₂ ρ₂
      (instSeq args₂ (args₂.length - 1)
        (e.instantiateLevelParams ks₂ us₂)) := by
  have hlen12 : args₂.length = args₁.length := by
    rw [InstArgs.length h₂, ← InstArgs.length h₁]
  have hcl₁ : (e.instantiateLevelParams ks₁ us₁).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]; exact hcl
  have hcl₂ : (e.instantiateLevelParams ks₂ us₂).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]; exact hcl
  have hb₁ : (e.instantiateLevelParams ks₁ us₁).looseBVarsBounded
      args₁.length = true := by
    rw [looseBVarsBounded_instantiateLevelParams]; exact hb
  have hb₂ : (e.instantiateLevelParams ks₂ us₂).looseBVarsBounded
      args₂.length = true := by
    rw [looseBVarsBounded_instantiateLevelParams, hlen12]; exact hb
  obtain ⟨sF₁, hfs₁, hlen₁, hsh₁, heq₁⟩ := interp_instSeq_fresh h₁ hcl₁ hb₁
  obtain ⟨sF₂, hfs₂, hlen₂, hsh₂, heq₂⟩ := interp_instSeq_fresh h₂ hcl₂ hb₂
  rw [heq₁, heq₂]
  -- fold the level instantiation over the fresh spines (whose sort-zero
  -- annotations are instantiation-invariant)
  have hmap : ∀ (sF : List Expr) (ks : List Name) (us : List Level),
      (∀ a ∈ sF, ∃ i nm, a = .fvar i nm (.sort .zero)) →
      sF.map (·.instantiateLevelParams ks us) = sF := by
    intro sF ks us hsh
    induction sF with
    | nil => rfl
    | cons a sF ih =>
      obtain ⟨i, nm, rfl⟩ := hsh a List.mem_cons_self
      rw [List.map_cons, ih (fun b hb => hsh b (List.mem_cons_of_mem _ hb))]
      rfl
  have hswap₁ : instSeq sF₁ (sF₁.length - 1)
      (e.instantiateLevelParams ks₁ us₁) =
      (instSeq sF₁ (sF₁.length - 1) e).instantiateLevelParams ks₁ us₁ := by
    rw [instSeq_instantiateLevelParams_fvars ks₁ us₁ sF₁ _ e
      (fun a ha => by obtain ⟨i, nm, rfl⟩ := hsh₁ a ha; exact ⟨i, nm, _, rfl⟩),
      hmap sF₁ ks₁ us₁ hsh₁]
  have hswap₂ : instSeq sF₂ (sF₂.length - 1)
      (e.instantiateLevelParams ks₂ us₂) =
      (instSeq sF₂ (sF₂.length - 1) e).instantiateLevelParams ks₂ us₂ := by
    rw [instSeq_instantiateLevelParams_fvars ks₂ us₂ sF₂ _ e
      (fun a ha => by obtain ⟨i, nm, rfl⟩ := hsh₂ a ha; exact ⟨i, nm, _, rfl⟩),
      hmap sF₂ ks₂ us₂ hsh₂]
  rw [hswap₁, hswap₂, interp_instLevels hcp, interp_instLevels hcp]
  have hpsF : ∀ (sF : List Expr),
      (∀ a ∈ sF, ∃ i nm, a = .fvar i nm (.sort .zero)) →
      (instSeq sF (sF.length - 1) e).allLevelParamsDefined ps = true := by
    intro sF hsh
    refine allLevelParamsDefined_instSeq_fvars sF _ ?_ hps
    intro a ha
    obtain ⟨i, nm, rfl⟩ := hsh a ha
    refine ⟨by simp [Expr.allLevelParamsDefined, Level.allParamsDefined], i, nm, _, rfl⟩
  rw [interp_params_ext hcp hφψ _ _ _ (hpsF sF₁ hsh₁)]
  exact interp_instSeq_fvarFrames hcl
    (by rw [hlen₁, ← InstArgs.length h₁]; exact hb) hfs₁ hfs₂


omit [SetTheory V] in
theorem Level.subst_nil : ∀ u : Level, Level.subst [] [] u = u := by
  intro u
  induction u <;> simp_all [Level.subst, Level.subst.go]

omit [SetTheory V] in
theorem Expr.instantiateLevelParams_nil :
    ∀ e : Expr, e.instantiateLevelParams [] [] = e := by
  intro e
  induction e <;>
    simp_all [Expr.instantiateLevelParams, Level.subst_nil]
  case const n vs =>
    induction vs <;> simp_all [Level.subst_nil]
  case lam n ty body m ihty ihbody =>
    cases m with
    | mk bi cod => cases cod <;> simp [Level.subst_nil]
  case forallE n ty body m ihty ihbody =>
    cases m with
    | mk bi cod => cases cod <;> simp [Level.subst_nil]

/-- One-sided variant of `interp_instSeq_swap₂`: the `ψ` side carries
the raw expression. -/
theorem interp_instSeq_swap₁ (hcp : ConstValParams cval env)
    {ψ : Name → Nat} {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
    {args₁ args₂ : List Expr} {vs : List V} {e : Expr}
    {ks₂ : List Name} {us₂ : List Level} {ps : List Name}
    (h₁ : InstArgs cval env ψ D₁ ρ₁ args₁ vs)
    (h₂ : InstArgs cval env φ D₂ ρ₂ args₂ vs)
    (hcl : e.hasFvar = false)
    (hb : e.looseBVarsBounded args₁.length = true)
    (hps : e.allLevelParamsDefined ps = true)
    (hφψ : ∀ p ∈ ps, ψ p = Level.substFn φ ks₂ us₂ p) :
    interpExpr V cval env ψ D₁ ρ₁
      (instSeq args₁ (args₁.length - 1) e) =
    interpExpr V cval env φ D₂ ρ₂
      (instSeq args₂ (args₂.length - 1)
        (e.instantiateLevelParams ks₂ us₂)) := by
  have h := interp_instSeq_swap₂ (φ := φ) hcp (ks₁ := []) (us₁ := [])
    h₁ h₂ hcl hb hps
    (by
      intro p hp
      show Level.substFn ψ [] [] p = _
      rw [show Level.substFn ψ [] [] p = ψ p from rfl]
      exact hφψ p hp)
  rwa [Expr.instantiateLevelParams_nil] at h


omit cval env φ in
/-- The canonical extension of the all-empty base valuation is the
`getD`-spelling over the values. -/
theorem snocFrame_eq_getD (xs : List V) :
    (snocFrame (V := V) 0 (rho0 V) xs).2 =
      fun j => xs.getD j SetTheory.empty := by
  funext j
  rcases Nat.lt_or_ge j xs.length with hj | hj
  · obtain ⟨x, hx⟩ : ∃ x, xs[j]? = some x :=
      ⟨_, List.getElem?_eq_getElem hj⟩
    have h1 := snocFrame_snd_get (V := V) xs 0 (rho0 V) j x hx
    rw [Nat.zero_add] at h1
    rw [h1, List.getD_eq_getElem?_getD, hx]
    rfl
  · have h2 : ∀ (d : Nat) (ρ : Nat → V) (ys : List V) (i : Nat),
        d + ys.length ≤ i → (snocFrame (V := V) d ρ ys).2 i = ρ i := by
      intro d ρ ys
      induction ys generalizing d ρ with
      | nil => intro i _; rfl
      | cons y ys ih =>
        intro i hi
        show (snocFrame (V := V) (d + 1) (updV V ρ d y) ys).2 i = ρ i
        rw [ih (d + 1) _ i (by simp at hi; omega)]
        simp only [updV]
        rw [if_neg (by simp at hi; omega)]
    rw [h2 0 (rho0 V) xs j (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

end Setlec
