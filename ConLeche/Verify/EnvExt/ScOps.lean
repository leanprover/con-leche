module

public import ConLeche.Verify.EnvExt.Scope

public section

/-!
# Env extension, part 2: scoping through the term operations

`Sc N` is closed under every term operation the knot's bodies build
results with: instantiation (one, a list, a spine, level parameters),
abstraction, lifting, application spines, telescope peeling, and the
literal expansions (whose constants are the literal's own names, `litNames`).
-/

namespace ConLeche.EnvExt

open ConLeche

variable {N : Name → Prop}

theorem sc_instantiate1 {v : Expr} (hv : Sc N v) :
    ∀ (e : Expr) (d : Nat), Sc N e → Sc N (e.instantiate1 v d) := by
  intro e
  induction e with
  | bvar i =>
    intro d _
    rw [Expr.instantiate1]
    split
    · exact hv
    · split <;> simp
  | sort u => intro d _; rw [Expr.instantiate1]; simp
  | const n us => intro d h; rw [Expr.instantiate1]; exact h
  | fvar idx ty => intro d h; rw [Expr.instantiate1]; exact h
  | lit l => intro d h; rw [Expr.instantiate1]; exact h
  | app f a ihf iha =>
    intro d h; simp only [sc_app] at h
    rw [Expr.instantiate1, sc_app]; exact ⟨ihf d h.1, iha d h.2⟩
  | lam ty b m ihty ihb =>
    intro d h; simp only [sc_lam] at h
    rw [Expr.instantiate1, sc_lam]; exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro d h; simp only [sc_forallE] at h
    rw [Expr.instantiate1, sc_forallE]; exact ⟨ihty d h.1, ihb (d + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro d h; simp only [sc_letE] at h
    rw [Expr.instantiate1, sc_letE]; exact ⟨iht d h.1, ihval d h.2.1, ihb (d + 1) h.2.2⟩
  | proj s i e ihe =>
    intro d h; simp only [sc_proj] at h
    rw [Expr.instantiate1, sc_proj]; exact ⟨h.1, ihe d h.2⟩

theorem sc_instantiate1' {e v : Expr} {d : Nat} (he : Sc N e) (hv : Sc N v) :
    Sc N (e.instantiate1 v d) :=
  sc_instantiate1 hv e d he

theorem sc_instantiateList :
    ∀ (e : Expr) (vs : List Expr) (d : Nat), (∀ v ∈ vs, Sc N v) → Sc N e →
      Sc N (e.instantiateList vs d) := by
  intro e vs d hvs he
  induction e, vs, d using Expr.instantiateList.induct with
  | case1 j vs d h => rw [Expr.instantiateList, if_pos h]; exact he
  | case2 j vs d h h' ih =>
    rw [Expr.instantiateList, if_neg h, dif_pos h']
    exact ih (fun v hv => hvs v (List.mem_of_mem_take hv)) (hvs _ (List.getElem_mem _))
  | case3 j vs d h h' => rw [Expr.instantiateList, if_neg h, dif_neg h']; simp
  | case4 => rw [Expr.instantiateList]; exact he
  | case5 => rw [Expr.instantiateList]; exact he
  | case6 => rw [Expr.instantiateList]; exact he
  | case7 f a vs d ihf iha =>
    simp only [sc_app] at he; rw [Expr.instantiateList, sc_app]
    exact ⟨ihf hvs he.1, iha hvs he.2⟩
  | case8 ty b bi vs d ihty ihb =>
    simp only [sc_lam] at he; rw [Expr.instantiateList, sc_lam]
    exact ⟨ihty hvs he.1, ihb hvs he.2⟩
  | case9 ty b bi vs d ihty ihb =>
    simp only [sc_forallE] at he; rw [Expr.instantiateList, sc_forallE]
    exact ⟨ihty hvs he.1, ihb hvs he.2⟩
  | case10 t v b vs d iht ihv ihb =>
    simp only [sc_letE] at he; rw [Expr.instantiateList, sc_letE]
    exact ⟨iht hvs he.1, ihv hvs he.2.1, ihb hvs he.2.2⟩
  | case11 => rw [Expr.instantiateList]; exact he
  | case12 s i e vs d ihe =>
    simp only [sc_proj] at he; rw [Expr.instantiateList, sc_proj]
    exact ⟨he.1, ihe hvs he.2⟩

theorem sc_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ e : Expr, Sc N e → Sc N (e.instantiateLevelParams ks us) := by
  intro e
  induction e with
  | bvar i => intro h; rw [Expr.instantiateLevelParams]; exact h
  | sort u => intro _; rw [Expr.instantiateLevelParams]; simp
  | const n vs => intro h; rw [Expr.instantiateLevelParams]; simpa using h
  | fvar idx ty ih => intro h; rw [Expr.instantiateLevelParams, sc_fvar]; exact ih (by simpa using h)
  | lit l => intro h; rw [Expr.instantiateLevelParams]; exact h
  | app f a ihf iha =>
    intro h; simp only [sc_app] at h
    rw [Expr.instantiateLevelParams, sc_app]; exact ⟨ihf h.1, iha h.2⟩
  | lam ty b m ihty ihb =>
    intro h; simp only [sc_lam] at h
    rw [Expr.instantiateLevelParams, sc_lam]; exact ⟨ihty h.1, ihb h.2⟩
  | forallE ty b m ihty ihb =>
    intro h; simp only [sc_forallE] at h
    rw [Expr.instantiateLevelParams, sc_forallE]; exact ⟨ihty h.1, ihb h.2⟩
  | letE t val b iht ihval ihb =>
    intro h; simp only [sc_letE] at h
    rw [Expr.instantiateLevelParams, sc_letE]; exact ⟨iht h.1, ihval h.2.1, ihb h.2.2⟩
  | proj s i e ihe =>
    intro h; simp only [sc_proj] at h
    rw [Expr.instantiateLevelParams, sc_proj]; exact ⟨h.1, ihe h.2⟩

theorem sc_abstract1 (dd : Nat) :
    ∀ (e : Expr) (k : Nat), Sc N e → Sc N (e.abstract1 dd k) := by
  intro e
  induction e with
  | bvar i => intro k h; rw [Expr.abstract1]; exact h
  | sort u => intro k _; rw [Expr.abstract1]; simp
  | const n vs => intro k h; rw [Expr.abstract1]; exact h
  | fvar idx ty ih => intro k h; rw [Expr.abstract1]; split <;> simp_all
  | lit l => intro k h; rw [Expr.abstract1]; exact h
  | app f a ihf iha =>
    intro k h; simp only [sc_app] at h
    rw [Expr.abstract1, sc_app]; exact ⟨ihf k h.1, iha k h.2⟩
  | lam ty b m ihty ihb =>
    intro k h; simp only [sc_lam] at h
    rw [Expr.abstract1, sc_lam]; exact ⟨ihty k h.1, ihb (k + 1) h.2⟩
  | forallE ty b m ihty ihb =>
    intro k h; simp only [sc_forallE] at h
    rw [Expr.abstract1, sc_forallE]; exact ⟨ihty k h.1, ihb (k + 1) h.2⟩
  | letE t val b iht ihval ihb =>
    intro k h; simp only [sc_letE] at h
    rw [Expr.abstract1, sc_letE]; exact ⟨iht k h.1, ihval k h.2.1, ihb (k + 1) h.2.2⟩
  | proj s i e ihe =>
    intro k h; simp only [sc_proj] at h
    rw [Expr.abstract1, sc_proj]; exact ⟨h.1, ihe k h.2⟩

theorem sc_getAppFn : ∀ {e : Expr}, Sc N e → Sc N e.getAppFn
  | .app f _, h => by rw [Expr.getAppFn]; exact sc_getAppFn (sc_app.mp h).1
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .lam _ _ _, h
  | .forallE _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => h

theorem sc_getAppArgs : ∀ {e : Expr}, Sc N e → ∀ a ∈ e.getAppArgs, Sc N a
  | .app f x, h => by
    rw [Expr.getAppArgs]; intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact sc_getAppArgs (sc_app.mp h).1 a ha
    · simp at ha; subst ha; exact (sc_app.mp h).2
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lam _ _ _, _
  | .forallE _ _ _, _ | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ => by
    intro a ha; simp [Expr.getAppArgs] at ha

theorem sc_mkAppN : ∀ {f : Expr} {as : List Expr}, Sc N f → (∀ a ∈ as, Sc N a) →
    Sc N (Expr.mkAppN f as)
  | _, [], hf, _ => by rw [Expr.mkAppN]; exact hf
  | _, a :: as, hf, has => by
    rw [Expr.mkAppN]
    exact sc_mkAppN (sc_app.mpr ⟨hf, has a (by simp)⟩) (fun b hb => has b (by simp [hb]))

theorem sc_instSpine : ∀ {as : List Expr} {t : Nat} {e : Expr}, (∀ a ∈ as, Sc N a) →
    Sc N e → Sc N (Expr.instSpine as t e)
  | [], _, _, _, he => by rw [Expr.instSpine]; exact he
  | a :: as, _, _, has, he => by
    rw [Expr.instSpine]
    exact sc_instSpine (fun b hb => has b (by simp [hb]))
      (sc_instantiate1' he (has a (by simp)))

theorem sc_piResult : ∀ {e : Expr}, Sc N e → Sc N e.piResult
  | .forallE _ b _, h => by rw [Expr.piResult]; exact sc_piResult (sc_forallE.mp h).2
  | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .lam _ _ _, h
  | .app _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h => h

theorem sc_piResidual : ∀ {e : Expr} {as : List Expr} {r : Expr}, Sc N e →
    (∀ a ∈ as, Sc N a) → piResidual e as = some r → Sc N r
  | _, [], _, he, _, h => by rw [piResidual] at h; cases h; exact he
  | .forallE _ b _, a :: as, _, he, has, h => by
    rw [piResidual] at h
    exact sc_piResidual (sc_instantiate1' (sc_forallE.mp he).2 (has a (by simp)))
      (fun x hx => has x (by simp [hx])) h
  | .bvar _, _ :: _, _, _, _, h | .fvar _ _, _ :: _, _, _, _, h
  | .sort _, _ :: _, _, _, _, h | .const _ _, _ :: _, _, _, _, h
  | .lam _ _ _, _ :: _, _, _, _, h | .app _ _, _ :: _, _, _, _, h
  | .letE _ _ _, _ :: _, _, _, _, h | .lit _, _ :: _, _, _, _, h
  | .proj _ _ _, _ :: _, _, _, _, h => by simp [piResidual] at h

theorem sc_mem_take {as : List Expr} {k : Nat} (h : ∀ a ∈ as, Sc N a) :
    ∀ a ∈ as.take k, Sc N a := fun a ha => h a (List.mem_of_mem_take ha)

theorem sc_mem_drop {as : List Expr} {k : Nat} (h : ∀ a ∈ as, Sc N a) :
    ∀ a ∈ as.drop k, Sc N a := fun a ha => h a (List.mem_of_mem_drop ha)

theorem sc_getD {as : List Expr} {k : Nat} {d : Expr} (h : ∀ a ∈ as, Sc N a)
    (hd : Sc N d) : Sc N (as.getD k d) := by
  rw [List.getD_eq_getElem?_getD]
  cases hk : as[k]? with
  | none => exact hd
  | some a => exact h a (List.mem_of_getElem? hk)

theorem sc_mem_append {as bs : List Expr} (ha : ∀ a ∈ as, Sc N a)
    (hb : ∀ b ∈ bs, Sc N b) : ∀ x ∈ as ++ bs, Sc N x := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact ha x hx
  · exact hb x hx

/-! ## Literal expansions and literal results -/

private theorem optSc_ite {c : Prop} [Decidable c] {x y : Option Expr}
    (hx : ∀ r, x = some r → Sc N r) (hy : ∀ r, y = some r → Sc N r) :
    ∀ r, (if c then x else y) = some r → Sc N r := by
  split
  · exact hx
  · exact hy

private theorem optSc_ite' {c : Prop} [Decidable c] {x y : Option Expr}
    (hx : c → ∀ r, x = some r → Sc N r) (hy : ¬c → ∀ r, y = some r → Sc N r) :
    ∀ r, (if c then x else y) = some r → Sc N r := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

section Agreed

theorem sc_natLit_of {n : Nat} (h : ∀ m ∈ natLitNames, N m) : Sc N (.lit (.natVal n)) :=
  sc_lit.mpr h

theorem sc_natLitToConstructor (n : Nat) (h : ∀ m ∈ natLitNames, N m) :
    Sc N (natLitToConstructor n) := by
  unfold natLitToConstructor
  split
  · exact sc_const.mpr (h _ (by simp [natLitNames]))
  · exact sc_app.mpr ⟨sc_const.mpr (h _ (by simp [natLitNames])), sc_natLit_of h⟩

theorem sc_strLitToConstructor (s : String) (h : ∀ m ∈ litGuardNames, N m) :
    Sc N (strLitToConstructor s) := by
  have hn : ∀ m ∈ natLitNames, N m := fun m hm => h m (by
    simp only [natLitNames, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> simp [litGuardNames])
  have g : ∀ {m : Name}, m ∈ litGuardNames → N m := fun hm => h _ hm
  unfold strLitToConstructor
  refine sc_app.mpr ⟨sc_const.mpr (g (by simp [litGuardNames])), ?_⟩
  induction s.toList with
  | nil => exact sc_app.mpr ⟨sc_const.mpr (g (by simp [litGuardNames])),
      sc_const.mpr (g (by simp [litGuardNames]))⟩
  | cons c cs ih =>
    rw [List.foldr_cons]
    refine sc_app.mpr ⟨sc_app.mpr ⟨sc_app.mpr ⟨sc_const.mpr (g (by simp [litGuardNames])),
      sc_const.mpr (g (by simp [litGuardNames]))⟩, sc_app.mpr ⟨sc_const.mpr
        (g (by simp [litGuardNames])), sc_natLit_of hn⟩⟩, ih⟩

theorem sc_natOpResult {c : Name} {a b : Nat} {r : Expr} (hn : ∀ m ∈ natLitNames, N m)
    (hb : (c = natBeqName ∨ c = natBleName) → N boolTrueName ∧ N boolFalseName)
    (h : natOpResult c a b = some r) : Sc N r := by
  revert r
  unfold natOpResult
  repeat' (first
    | (apply optSc_ite' <;> intro hcnd)
    | (intro r h; simp at h; done)
    | (intro r h; cases h; exact sc_natLit_of hn)
    | (intro r h; cases h; simp only [sc_const]; split
       · first | exact (hb (.inl hcnd)).1 | exact (hb (.inr hcnd)).1
       · first | exact (hb (.inl hcnd)).2 | exact (hb (.inr hcnd)).2))

end Agreed

end ConLeche.EnvExt
