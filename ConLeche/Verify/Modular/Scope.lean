module

public import ConLeche.Verify.Modular.Local
import ConLeche.Verify.Cached.GuardsC

public section

/-!
# What a context entry's laws read (task #370)

From a unit's verified read sets (`lawsOk`) to the scoping facts
`ConLeche.Modular.LocalOk` asks of a context entry: `EntryScoped`,
`EntryProjs`, `BlockIn`.
-/

namespace ConLeche.Cached.Mod

open ConLeche ConLeche.Modular

/-! ## The walks' specifications -/

/-- A resolution walk against one index carries over to an environment
that stores every name the index stores. -/
theorem constsResolve_of_F {fe : FEnv} {R : Env}
    (hsub : ∀ d, (fe.find? d).isSome = true → (R.find? d).isSome = true) :
    ∀ e : Expr, Expr.constsResolveF fe e = true → e.constsResolve R = true := by
  intro e
  induction e with
  | bvar _ => intro _; rfl
  | sort _ => intro _; rfl
  | lit l =>
    cases l with
    | natVal _ =>
      intro h
      simp only [Expr.constsResolveF, Bool.and_eq_true] at h
      simp only [Expr.constsResolve, Bool.and_eq_true]
      exact ⟨⟨hsub _ h.1.1, hsub _ h.1.2⟩, hsub _ h.2⟩
    | strVal _ =>
      intro h
      simp only [Expr.constsResolveF, Bool.and_eq_true] at h
      simp only [Expr.constsResolve, Bool.and_eq_true]
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
      exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨hsub _ h1, hsub _ h2⟩, hsub _ h3⟩, hsub _ h4⟩, hsub _ h5⟩, hsub _ h6⟩,
        hsub _ h7⟩, hsub _ h8⟩, hsub _ h9⟩, hsub _ h10⟩
  | const n _ => intro h; exact hsub n h
  | fvar _ ty ih => intro h; exact ih h
  | app f a ihf iha =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b iht ihb =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b iht ihb =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | proj s _ e ih =>
    intro h
    simp only [Expr.constsResolveF, Bool.and_eq_true] at h
    simp only [Expr.constsResolve, Bool.and_eq_true]
    exact ⟨hsub s h.1, ih h.2⟩

/-- The projection walk carries over to a context that stores every
admitted structure as a type former. -/
theorem projsFormer_of_projsIn {P : Name → Bool} {C : Env}
    (hsub : ∀ s, P s = true → ∃ cv caps, C.find? s = some (.indInfo cv caps)) :
    ∀ e : Expr, Expr.projsIn P e = true → Expr.projsFormer C e = true := by
  intro e
  induction e with
  | proj s _ e ih =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    obtain ⟨cv, caps, hf⟩ := hsub s h.1
    rw [hf]
    exact ⟨rfl, ih h.2⟩
  | app f a ihf iha =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    exact ⟨ihf h.1, iha h.2⟩
  | lam ty b iht ihb =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE ty b iht ihb =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    exact ⟨iht h.1, ihb h.2⟩
  | letE ty v b iht ihv ihb =>
    intro h
    simp only [Expr.projsIn, Bool.and_eq_true] at h
    simp only [Expr.projsFormer, Bool.and_eq_true]
    exact ⟨⟨iht h.1.1, ihv h.1.2⟩, ihb h.2⟩
  | _ => intro _; simp [Expr.projsFormer]

/-! ## Read sets -/

/-- A name the read set's index finds is one of its names. -/
theorem dvOf_find? {r : ReadSet} {d : Name} (h : ((dvOf r).find? d).isSome = true) :
    r.d.contains d = true := by
  unfold dvOf FEnv.find? at h
  simp only at h
  cases hd : r.d[d]? with
  | none =>
    rw [hd] at h
    simp at h
  | some x => rw [Std.HashMap.contains_eq_isSome_getElem? (m := r.d), hd]; rfl

/-- **What a verified read set gives**: if every name of it is good, the
laws read only good names. -/
structure LawsGood (R C : Env) (r : ReadSet) : Prop where
  d : ∀ n, r.d.contains n = true → (R.find? n).isSome = true
  fi : ∀ n, r.fi.contains n = true → ∃ cv caps, C.find? n = some (.indInfo cv caps)
  fc : ∀ n, r.fc.contains n = true → ∃ cv nP nF, C.find? n = some (.ctorInfo cv nP nF)

theorem lawsOk_spec {r : ReadSet} {l : Laws} (h : lawsOk r l = true) :
    (∀ e ∈ l.es, Expr.constsResolveF (dvOf r) e = true) ∧
    (∀ e ∈ l.es, Expr.projsIn r.fi.contains e = true) ∧
    (∀ n ∈ l.ns, ((dvOf r).find? n).isSome = true) ∧
    (∀ n ∈ l.fi, r.fi.contains n = true) ∧ (∀ n ∈ l.fc, r.fc.contains n = true) := by
  unfold lawsOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨fun e he => ?_, fun e he => ?_, h3, h4, h5⟩
  · rw [← constsResolveFC_spec]; exact h1 e he
  · rw [← projsInC_eq]; exact h2 e he

end ConLeche.Cached.Mod
