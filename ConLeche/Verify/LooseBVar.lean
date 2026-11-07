module

public import ConLeche.Kernel.CoreDefs

public section

/-!
# Loose bound variables

Facts about `Expr.hasLooseBVar` and its executed form `Expr.hasLooseBVarB`
(the `bvarB` cutoff walk): the cutoff is sound, the occurrence of an index
is untouched by substituting a closed term for a higher one, and a bound
tightens where the top index does not occur.
-/

namespace ConLeche

/-- A node bounded at or below `i` has no loose `bvar i`. -/
theorem Expr.hasLooseBVar_eq_false_of_bound : ∀ (e : Expr) (i : Nat),
    e.bvarBound ≤ i → e.hasLooseBVar i = false
  | .bvar j, i, h => by
    simp only [Expr.bvarBound] at h
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne, ne_eq]
    omega
  | .fvar .., _, _ => rfl
  | .sort _, _, _ => rfl
  | .const .., _, _ => rfl
  | .lit _, _, _ => rfl
  | .app f a, i, h => by
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨hasLooseBVar_eq_false_of_bound f i h.1, hasLooseBVar_eq_false_of_bound a i h.2⟩
  | .lam ty b, i, h => by
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨hasLooseBVar_eq_false_of_bound ty i h.1,
      hasLooseBVar_eq_false_of_bound b (i + 1) (by omega)⟩
  | .forallE ty b, i, h => by
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨hasLooseBVar_eq_false_of_bound ty i h.1,
      hasLooseBVar_eq_false_of_bound b (i + 1) (by omega)⟩
  | .letE t v b, i, h => by
    simp only [Expr.bvarBound, Nat.max_le] at h
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff]
    exact ⟨⟨hasLooseBVar_eq_false_of_bound t i h.1.1, hasLooseBVar_eq_false_of_bound v i h.1.2⟩,
      hasLooseBVar_eq_false_of_bound b (i + 1) (by omega)⟩
  | .proj _ _ e, i, h => by
    simp only [Expr.bvarBound] at h
    simp only [Expr.hasLooseBVar]
    exact hasLooseBVar_eq_false_of_bound e i h

/-- **The cutoff walk is `hasLooseBVar`.** -/
theorem Expr.hasLooseBVarB_eq : ∀ (i : Nat) (e : Expr), e.hasLooseBVarB i = e.hasLooseBVar i := by
  intro i e
  induction e generalizing i with
  | bvar j =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · rfl
  | fvar idx ty _ =>
    rw [Expr.hasLooseBVarB]; split <;> rfl
  | sort u => rw [Expr.hasLooseBVarB]; split <;> rfl
  | const n us => rw [Expr.hasLooseBVarB]; split <;> rfl
  | lit l => rw [Expr.hasLooseBVarB]; split <;> rfl
  | app f a ihf iha =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, ihf, iha]
  | lam ty b iht ihb =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, iht, ihb]
  | forallE ty b iht ihb =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, iht, ihb]
  | letE t v b iht ihv ihb =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, iht, ihv, ihb]
  | proj s i' e ih =>
    rw [Expr.hasLooseBVarB]
    split
    · rename_i hcut
      exact (Expr.hasLooseBVar_eq_false_of_bound _ _ (Expr.bvarB_eq _ ▸ hcut)).symm
    · simp only [Expr.hasLooseBVar, ih]

/-- A term bounded by `k` has no loose index at or above `k`. -/
theorem Expr.hasLooseBVar_eq_false_of_bounded :
    ∀ (e : Expr) {k j : Nat}, e.looseBVarsBounded k = true → k ≤ j → e.hasLooseBVar j = false := by
  intro e
  induction e with
  | bvar i =>
    intro k j hb hkj
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne, ne_eq]
    omega
  | fvar _ _ _ => intro _ _ _ _; rfl
  | sort _ => intro _ _ _ _; rfl
  | const _ _ => intro _ _ _ _; rfl
  | lit _ => intro _ _ _ _; rfl
  | app f a ihf iha =>
    intro k j hb hkj
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.hasLooseBVar, ihf hb.1 hkj, iha hb.2 hkj, Bool.or_self]
  | lam ty b iht ihb =>
    intro k j hb hkj
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.hasLooseBVar, iht hb.1 hkj, ihb (k := k + 1) (j := j + 1) hb.2 (by omega), Bool.or_self]
  | forallE ty b iht ihb =>
    intro k j hb hkj
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.hasLooseBVar, iht hb.1 hkj, ihb (k := k + 1) (j := j + 1) hb.2 (by omega), Bool.or_self]
  | letE t v b iht ihv ihb =>
    intro k j hb hkj
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.hasLooseBVar, iht hb.1.1 hkj, ihv hb.1.2 hkj, ihb (k := k + 1) (j := j + 1) hb.2 (by omega),
      Bool.or_self]
  | proj _ _ e ih =>
    intro k j hb hkj
    simp only [Expr.looseBVarsBounded] at hb
    simp only [Expr.hasLooseBVar, ih hb hkj]

/-- **A bound tightens where its top index does not occur.** -/
theorem Expr.looseBVarsBounded_of_not_hasLooseBVar :
    ∀ (e : Expr) {k : Nat}, e.looseBVarsBounded (k + 1) = true → e.hasLooseBVar k = false →
      e.looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i =>
    intro k hb hn
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb ⊢
    simp only [Expr.hasLooseBVar, beq_eq_false_iff_ne, ne_eq] at hn
    omega
  | fvar _ _ _ => intro _ _ _; rfl
  | sort _ => intro _ _ _; rfl
  | const _ _ => intro _ _ _; rfl
  | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro k hb hn
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hn
    exact ⟨ihf hb.1 hn.1, iha hb.2 hn.2⟩
  | lam ty b iht ihb =>
    intro k hb hn
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hn
    exact ⟨iht hb.1 hn.1, ihb hb.2 hn.2⟩
  | forallE ty b iht ihb =>
    intro k hb hn
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hn
    exact ⟨iht hb.1 hn.1, ihb hb.2 hn.2⟩
  | letE t v b iht ihv ihb =>
    intro k hb hn
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    simp only [Expr.hasLooseBVar, Bool.or_eq_false_iff] at hn
    exact ⟨⟨iht hb.1.1 hn.1.1, ihv hb.1.2 hn.1.2⟩, ihb hb.2 hn.2⟩
  | proj _ _ e ih =>
    intro k hb hn
    simp only [Expr.looseBVarsBounded] at hb ⊢
    simp only [Expr.hasLooseBVar] at hn
    exact ih hb hn

/-- **Substituting a closed term for a higher index leaves a lower index's
occurrence as it was.** -/
theorem Expr.hasLooseBVar_instantiate1_lt {v : Expr} (hv : v.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) {i j : Nat}, j < i → (e.instantiate1 v i).hasLooseBVar j = e.hasLooseBVar j := by
  intro e
  induction e with
  | bvar k =>
    intro i j hji
    simp only [Expr.instantiate1]
    split
    · rename_i hk
      rw [Expr.hasLooseBVar_eq_false_of_bounded v hv (Nat.zero_le j)]
      simp only [Expr.hasLooseBVar]
      exact (beq_eq_false_iff_ne.mpr (by omega)).symm
    · split
      · simp only [Expr.hasLooseBVar]
        rw [beq_eq_false_iff_ne.mpr (by omega), beq_eq_false_iff_ne.mpr (by omega)]
      · rfl
  | fvar _ _ _ => intro _ _ _; rfl
  | sort _ => intro _ _ _; rfl
  | const _ _ => intro _ _ _; rfl
  | lit _ => intro _ _ _; rfl
  | app f a ihf iha =>
    intro i j hji
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ihf hji, iha hji]
  | lam ty b iht ihb =>
    intro i j hji
    simp only [Expr.instantiate1, Expr.hasLooseBVar, iht hji, ihb (Nat.succ_lt_succ hji)]
  | forallE ty b iht ihb =>
    intro i j hji
    simp only [Expr.instantiate1, Expr.hasLooseBVar, iht hji, ihb (Nat.succ_lt_succ hji)]
  | letE t w b iht ihw ihb =>
    intro i j hji
    simp only [Expr.instantiate1, Expr.hasLooseBVar, iht hji, ihw hji,
      ihb (Nat.succ_lt_succ hji)]
  | proj _ _ e ih =>
    intro i j hji
    simp only [Expr.instantiate1, Expr.hasLooseBVar, ih hji]

/-- Level instantiation leaves every index's occurrence as it was. -/
theorem Expr.hasLooseBVar_instantiateLevelParams (ks : List Name) (us : List Level) :
    ∀ (e : Expr) (j : Nat), (e.instantiateLevelParams ks us).hasLooseBVar j = e.hasLooseBVar j := by
  intro e
  induction e <;> intro j <;> simp_all [Expr.instantiateLevelParams, Expr.hasLooseBVar]

end ConLeche
