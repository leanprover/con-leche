module

public import ConLeche.Modular
public import ConLeche.Verify.EnvWF

public section

/-!
# What a constant's laws read, as a predicate on names

`EntryScoped` (`ConLeche/Modular.lean`) says the names a constant's laws
read are stored in an environment (`constsResolve`).  The proofs also
need the same footprint against other predicates — "stored in both, so
read alike" — so this file states it over a predicate on names
(`Expr.constsAll`, `EntryScopedP`) and relates the two.
-/

namespace ConLeche.Model.Modular

open ConLeche ConLeche.Modular

/-- An inductive type former, constructor or recursor: the kinds no
context presents as an assumption. -/
@[expose] def _root_.ConLeche.ConstantInfo.isIndKind : ConstantInfo → Bool
  | .indInfo .. | .ctorInfo .. | .recInfo .. => true
  | _ => false

/-- An inductive type former. -/
@[expose] def _root_.ConLeche.ConstantInfo.isFormer : ConstantInfo → Bool
  | .indInfo .. => true
  | _ => false


/-- **Every name an expression reads satisfies `p`**: `constsResolve`
with a predicate in place of the lookup (a literal reads its support
names, a projection its structure). -/
@[expose] def Expr.constsAll (p : Name → Prop) : Expr → Prop
  | .bvar _ | .sort _ => True
  | .lit (.natVal _) => p natName ∧ p natZeroName ∧ p natSuccName
  | .lit (.strVal _) =>
    p natName ∧ p natZeroName ∧ p natSuccName ∧ p stringName ∧ p stringOfListName ∧
      p listName ∧ p listNilName ∧ p listConsName ∧ p charName ∧ p charOfNatName
  | .const n _ => p n
  | .fvar _ ty => Expr.constsAll p ty
  | .app f a => Expr.constsAll p f ∧ Expr.constsAll p a
  | .lam ty body | .forallE ty body => Expr.constsAll p ty ∧ Expr.constsAll p body
  | .letE ty val body => Expr.constsAll p ty ∧ Expr.constsAll p val ∧ Expr.constsAll p body
  | .proj s _ e => p s ∧ Expr.constsAll p e

theorem Expr.constsAll_mono {p q : Name → Prop} (h : ∀ n, p n → q n) :
    ∀ {e : Expr}, Expr.constsAll p e → Expr.constsAll q e := by
  intro e
  induction e with
  | bvar _ => exact fun _ => trivial
  | sort _ => exact fun _ => trivial
  | const n _ => exact h n
  | lit l =>
    cases l with
    | natVal _ => exact fun ⟨a, b, c⟩ => ⟨h _ a, h _ b, h _ c⟩
    | strVal _ =>
      exact fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ =>
        ⟨h _ a1, h _ a2, h _ a3, h _ a4, h _ a5, h _ a6, h _ a7, h _ a8, h _ a9, h _ a10⟩
  | fvar _ _ ih => exact ih
  | app _ _ ihf iha => exact fun ⟨a, b⟩ => ⟨ihf a, iha b⟩
  | lam _ _ ih1 ih2 => exact fun ⟨a, b⟩ => ⟨ih1 a, ih2 b⟩
  | forallE _ _ ih1 ih2 => exact fun ⟨a, b⟩ => ⟨ih1 a, ih2 b⟩
  | letE _ _ _ ih1 ih2 ih3 => exact fun ⟨a, b, c⟩ => ⟨ih1 a, ih2 b, ih3 c⟩
  | proj _ _ _ ih => exact fun ⟨a, b⟩ => ⟨h _ a, ih b⟩

/-- `constsResolve` is `constsAll` at "stored". -/
theorem Expr.constsResolve_iff (R : Env) :
    ∀ {e : Expr}, e.constsResolve R = true ↔ Expr.constsAll (fun n => (R.find? n).isSome = true) e := by
  intro e
  induction e with
  | bvar _ => simp [ConLeche.Expr.constsResolve, Expr.constsAll]
  | sort _ => simp [ConLeche.Expr.constsResolve, Expr.constsAll]
  | const n _ => simp [ConLeche.Expr.constsResolve, Expr.constsAll]
  | lit l =>
    cases l <;> simp [ConLeche.Expr.constsResolve, Expr.constsAll, and_assoc]
  | fvar _ _ ih => simp only [ConLeche.Expr.constsResolve, Expr.constsAll]; exact ih
  | app _ _ ihf iha =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]; rw [ihf, iha]
  | lam _ _ ih1 ih2 =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]; rw [ih1, ih2]
  | forallE _ _ ih1 ih2 =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]; rw [ih1, ih2]
  | letE _ _ _ ih1 ih2 ih3 =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]
    rw [ih1, ih2, ih3, and_assoc]
  | proj _ _ _ ih =>
    simp only [ConLeche.Expr.constsResolve, Expr.constsAll, Bool.and_eq_true]; rw [ih]

/-- The head constant of an application spine is one it reads. -/
theorem Expr.constsAll_getAppFn {p : Name → Prop} :
    ∀ {e : Expr} {T : Name} {us : List Level}, Expr.constsAll p e →
      e.getAppFn = .const T us → p T := by
  intro e
  induction e with
  | app f a ihf _ => exact fun h he => ihf h.1 he
  | const n _ =>
    intro T us h he
    simp only [ConLeche.Expr.getAppFn, Expr.const.injEq] at he
    exact he.1 ▸ h
  | _ => intro T us _ he; simp [ConLeche.Expr.getAppFn] at he

/-- The head constant of an expression's `∀`-residual is one it reads. -/
theorem Expr.constsAll_piResult_head {p : Name → Prop} :
    ∀ {e : Expr} {T : Name} {us : List Level}, Expr.constsAll p e →
      e.piResult.getAppFn = .const T us → p T := by
  intro e
  induction e with
  | forallE ty b _ ihb => exact fun h he => ihb h.2 he
  | _ => exact fun h he => Expr.constsAll_getAppFn h he

/-- Three predicates on an expression's names combine. -/
theorem Expr.constsAll_and3 {p q r s : Name → Prop} (h : ∀ n, p n → q n → r n → s n) :
    ∀ {e : Expr}, Expr.constsAll p e → Expr.constsAll q e → Expr.constsAll r e →
      Expr.constsAll s e := by
  intro e
  induction e with
  | bvar _ => exact fun _ _ _ => trivial
  | sort _ => exact fun _ _ _ => trivial
  | const n _ => exact h n
  | lit l =>
    cases l with
    | natVal _ =>
      exact fun ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ ⟨c1, c2, c3⟩ => ⟨h _ a1 b1 c1, h _ a2 b2 c2, h _ a3 b3 c3⟩
    | strVal _ =>
      exact fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩
        ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ =>
        ⟨h _ a1 b1 c1, h _ a2 b2 c2, h _ a3 b3 c3, h _ a4 b4 c4, h _ a5 b5 c5, h _ a6 b6 c6,
          h _ a7 b7 c7, h _ a8 b8 c8, h _ a9 b9 c9, h _ a10 b10 c10⟩
  | fvar _ _ ih => exact ih
  | app _ _ ihf iha => exact fun ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ => ⟨ihf a c e, iha b d f⟩
  | lam _ _ ih1 ih2 => exact fun ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ => ⟨ih1 a c e, ih2 b d f⟩
  | forallE _ _ ih1 ih2 => exact fun ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ => ⟨ih1 a c e, ih2 b d f⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    exact fun ⟨a, b, c⟩ ⟨d, e, f⟩ ⟨g, i, j⟩ => ⟨ih1 a d g, ih2 b e i, ih3 c f j⟩
  | proj _ _ _ ih => exact fun ⟨a, b⟩ ⟨c, d⟩ ⟨e, f⟩ => ⟨h _ a c e, ih b d f⟩

/-- **`EntryScoped` over a predicate.** -/
@[expose] def EntryScopedP (p : Name → Prop) (C : Env) (n : Name) (ci : ConstantInfo) : Prop :=
  Expr.constsAll p ci.toConstantVal.type ∧
  (∀ cv v h, ci = .defnInfo cv v h → Expr.constsAll p v) ∧
  (∀ cv mI rP rules, ci = .recInfo cv mI rP rules → ∀ r ∈ rules,
    Expr.constsAll p r.rhs ∧ p r.ctor ∧
    ∀ lvls pins, r.fire = .nested lvls pins → ∀ q ∈ pins, Expr.constsAll p q) ∧
  (∀ cv caps, ci = .indInfo cv caps →
    (∀ m ∈ caps.all, p m) ∧ (∀ c ∈ caps.ctors, p c) ∧ (caps.eta = true → p caps.etaCtor) ∧
    ∀ t, C.findTable? n = some t → p t.ctor ∧ ∀ b ∈ t.bodies.toList, Expr.constsAll p b) ∧
  ∀ d ∈ pinFootprint n, p d

theorem EntryScopedP.mono {p q : Name → Prop} {C : Env} {n : Name} {ci : ConstantInfo}
    (h : EntryScopedP p C n ci) (hpq : ∀ d, p d → q d) : EntryScopedP q C n ci := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨Expr.constsAll_mono hpq h1, fun cv v hh he => Expr.constsAll_mono hpq (h2 cv v hh he),
    fun cv mI rP rules he r hr => ?_, fun cv caps he => ?_, fun d hd => hpq d (h5 d hd)⟩
  · obtain ⟨a, b, c⟩ := h3 cv mI rP rules he r hr
    exact ⟨Expr.constsAll_mono hpq a, hpq _ b, fun lvls pins hf x hx =>
      Expr.constsAll_mono hpq (c lvls pins hf x hx)⟩
  · obtain ⟨a, b, c, d⟩ := h4 cv caps he
    exact ⟨fun m hm => hpq m (a m hm), fun x hx => hpq x (b x hx), fun he' => hpq _ (c he'),
      fun t ht => ⟨hpq _ (d t ht).1, fun b hb => Expr.constsAll_mono hpq ((d t ht).2 b hb)⟩⟩

/-- `EntryScoped` is `EntryScopedP` at "stored". -/
theorem entryScoped_iff {R C : Env} {n : Name} {ci : ConstantInfo} :
    EntryScoped R C n ci ↔ EntryScopedP (fun d => (R.find? d).isSome = true) C n ci := by
  simp only [EntryScoped, EntryScopedP, Expr.constsResolve_iff]

end ConLeche.Model.Modular
