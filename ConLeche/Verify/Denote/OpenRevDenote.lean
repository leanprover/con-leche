module

public import ConLeche.Verify.Denote.OpenVars

public section

/-!
# Real-argument instantiation, read through the reverse opening

`denote` of an `Expr.instSeq` at real arguments is the denote of the
*reverse-opened* subject with the arguments' denotations chained back
in (`denote_openRev`) — the recursion `denote`'s own β-lemma produces,
which is why the opener indices ascend with the substitution order
rather than with the binder order.
-/

namespace ConLeche.Verify

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- The reverse opening's leaves sit below the opened depth. -/
theorem openRev_fvarsBelow {e : Expr} {d : Nat}
    (hfb : Expr.fvarsBelow d e) :
    ∀ n, Expr.fvarsBelow (d + n) (openRev d n e) := by
  intro n
  induction n with
  | zero => exact Expr.fvarsBelow_mono (by omega) hfb
  | succ n ih =>
    show Expr.fvarsBelow (d + (n + 1))
      ((openRev d n e).instantiate1 (.fvar (d + n) _) 0)
    refine Expr.fvarsBelow_instantiate1_gen ?_ 0
      (Expr.fvarsBelow_mono (by omega) ih)
    show Expr.fvarsBelow (d + (n + 1)) (.fvar (d + n) _)
    simp [Expr.fvarsBelow]

/-- Instantiation strips one loose level at any cut below the bound. -/
private theorem bounded_instantiate1_le {a : Expr}
    (hba : a.looseBVarsBounded 0 = true) :
    ∀ (e : Expr) (k m : Nat), k ≤ m →
      e.looseBVarsBounded (m + 1) = true →
      (e.instantiate1 a k).looseBVarsBounded m = true := by
  intro e
  induction e with
  | bvar i =>
    intro k m hkm hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    simp only [Expr.instantiate1]
    split
    · exact Expr.looseBVarsBounded_mono (by omega) hba
    · split
      · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
        omega
      · simp only [Expr.looseBVarsBounded, decide_eq_true_eq]
        omega
  | fvar idx ty ih => intro k m _ _; rfl
  | sort u => intro k m _ _; rfl
  | const n us => intro k m _ _; rfl
  | lit l => intro k m _ _; rfl
  | app f x ihf ihx =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb ⊢
    exact ⟨ihf k m hkm hb.1, ihx k m hkm hb.2⟩
  | lam ty body bi ihty ihbody =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb ⊢
    exact ⟨ihty k m hkm hb.1, ihbody (k + 1) (m + 1) (by omega) hb.2⟩
  | forallE ty body bi ihty ihbody =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb ⊢
    exact ⟨ihty k m hkm hb.1, ihbody (k + 1) (m + 1) (by omega) hb.2⟩
  | letE ty val body ihty ihval ihbody =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded,
      Bool.and_eq_true] at hb ⊢
    exact ⟨⟨ihty k m hkm hb.1.1, ihval k m hkm hb.1.2⟩,
      ihbody (k + 1) (m + 1) (by omega) hb.2⟩
  | proj s i x ih =>
    intro k m hkm hb
    simp only [Expr.instantiate1, Expr.looseBVarsBounded] at hb ⊢
    exact ih k m hkm hb

/-- The reverse opening consumes the loose variables. -/
theorem openRev_bounded {e : Expr} {d : Nat} :
    ∀ n m, e.looseBVarsBounded (n + m) = true →
      (openRev d n e).looseBVarsBounded m = true := by
  intro n
  induction n generalizing e with
  | zero =>
    intro m h
    rw [Nat.zero_add] at h
    exact h
  | succ n ih =>
    intro m h
    show ((openRev d n e).instantiate1 _ 0).looseBVarsBounded m = true
    refine bounded_instantiate1_le rfl _ 0 m (by omega) ?_
    exact ih (m + 1) (by
      rw [show n + (m + 1) = n + 1 + m from by omega]
      exact h)

end ConLeche.Verify

namespace ConLeche.Verify

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-- The reverse opening is well-scoped at the opened depth. -/
theorem openRev_WScoped {e : Expr} {d : Nat}
    (hws : Expr.WScoped d e) :
    ∀ n, Expr.WScoped (d + n) (openRev d n e) := by
  intro n
  induction n with
  | zero => exact hws.mono (by omega)
  | succ n ih =>
    show Expr.WScoped (d + (n + 1))
      ((openRev d n e).instantiate1 (.fvar (d + n) _) 0)
    have h1 := Expr.WScoped.instantiate1 (d := d + n)
      (ty := .sort .zero)
      (by simp [Expr.WScoped]) 0 ih
    exact h1.mono (by omega)

/-- The reverse opening of a constant-frame subject shifts with its
base. -/
theorem openRev_shiftFrom {e : Expr} (hnf : e.hasFvar = false) :
    ∀ (d n : Nat), (openRev d n e).shiftFrom 0 = openRev (d + 1) n e := by
  intro d n
  induction n with
  | zero =>
    exact Expr.shiftFrom_eq_self
      ((Expr.WScoped.of_not_hasFvar (d := 0) hnf).fvarsBelow)
  | succ n ih =>
    show ((openRev d n e).instantiate1
      (.fvar (d + n) (.sort .zero)) 0).shiftFrom 0 = _
    rw [Expr.shiftFrom_instantiate1 (Nat.zero_le (d + n)), ih]
    show (openRev (d + 1) n e).instantiate1
      (.fvar (d + n + 1) (.sort .zero)) 0 = _
    rw [show d + n + 1 = d + 1 + n from by omega]
    rfl

/-- A bound on every leaf index bounds the free variables. -/
theorem Expr.fvarsBelow_of_fvarLeaves :
    ∀ {e : Expr} {n : Nat},
      (∀ l ∈ e.fvarLeaves, l.1 < n) → Expr.fvarsBelow n e := by
  intro e
  induction e <;> intro n h <;>
    simp only [Expr.fvarsBelow, Expr.fvarLeaves] at h ⊢ <;>
    try trivial
  case fvar idx ty ih => exact h (idx, ty) List.mem_cons_self
  case app f a ihf iha =>
    exact ⟨ihf fun l hl => h l (List.mem_append_left _ hl),
      iha fun l hl => h l (List.mem_append_right _ hl)⟩
  case lam ty b m ihty ihb =>
    exact ⟨ihty fun l hl => h l (List.mem_append_left _ hl),
      ihb fun l hl => h l (List.mem_append_right _ hl)⟩
  case forallE ty b m ihty ihb =>
    exact ⟨ihty fun l hl => h l (List.mem_append_left _ hl),
      ihb fun l hl => h l (List.mem_append_right _ hl)⟩
  case letE ty v b ihty ihv ihb =>
    refine ⟨ihty fun l hl => h l ?_, ihv fun l hl => h l ?_,
      ihb fun l hl => h l ?_⟩
    · exact List.mem_append_left _ (List.mem_append_left _ hl)
    · exact List.mem_append_left _ (List.mem_append_right _ hl)
    · exact List.mem_append_right _ hl
  case proj s i e ihe => exact ihe h

end ConLeche.Verify
