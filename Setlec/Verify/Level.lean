import Setlec.Kernel.Level

/-!
# Soundness of the level operations

Levels are given semantics by evaluation into `Nat` under an assignment of
the parameters (`Level.eval`).  The results proved here:

* `eval_simplify`: `simplify` preserves evaluation.
* `leqCore_sound`: `leqCore … = some true` implies `eval φ l ≤ eval φ r + diff`
  for every assignment `φ`.
* `isEquiv_sound`: `isEquiv l r = some true` implies `eval φ l = eval φ r`
  for every assignment `φ`.

Only the `true` direction is needed: a `false` verdict leads to rejection,
which needs no justification, and `none` is an internal error.
-/

namespace Setlec.Level

/-- Evaluate a level under an assignment of its parameters. -/
def eval (φ : Name → Nat) : Level → Nat
  | .zero => 0
  | .succ l => eval φ l + 1
  | .max l r => Max.max (eval φ l) (eval φ r)
  | .imax l r => if eval φ r = 0 then 0 else Max.max (eval φ l) (eval φ r)
  | .param n => φ n

/-- The assignment corresponding to a parameter substitution. -/
def substFn (φ : Name → Nat) : List Name → List Level → Name → Nat
  | k :: ks, v :: vs, n => if k = n then eval φ v else substFn φ ks vs n
  | _, _, n => φ n

theorem eval_subst_go (φ : Name → Nat) (ks : List Name) (vs : List Level) (n : Name) :
    eval φ (subst.go ks vs n) = substFn φ ks vs n := by
  fun_induction subst.go with grind [eval, substFn]

theorem eval_subst (φ : Name → Nat) (ks : List Name) (vs : List Level) (l : Level) :
    eval φ (subst ks vs l) = eval (substFn φ ks vs) l := by
  fun_induction subst with grind [eval, eval_subst_go]

theorem eval_combining (φ : Name → Nat) (l r : Level) :
    eval φ (combining l r) = Max.max (eval φ l) (eval φ r) := by
  fun_induction combining with grind [eval]

theorem eval_simplify (φ : Name → Nat) (l : Level) :
    eval φ (simplify l) = eval φ l := by
  fun_induction simplify with grind [eval, eval_combining]

/-- The semantic statement decided by `leqCore fuel l r diff = some true`. -/
def Sem (l r : Level) (diff : Int) : Prop :=
  ∀ φ : Name → Nat, (eval φ l : Int) ≤ eval φ r + diff

private theorem bind_and_some_true {x y : Option Bool}
    (h : (do return (← x) && (← y) : Option Bool) = some true) :
    x = some true ∧ y = some true := by
  cases x <;> cases y <;> simp_all [Bind.bind, Option.bind, Pure.pure]

private theorem bind_or_some_true {x y : Option Bool}
    (h : (do return (← x) || (← y) : Option Bool) = some true) :
    x = some true ∨ y = some true := by
  cases x <;> cases y <;> simp_all [Bind.bind, Option.bind, Pure.pure]

/-- Point update of an assignment. -/
private def upd (φ : Name → Nat) (p : Name) (v : Nat) : Name → Nat :=
  fun n => if p = n then v else φ n

private theorem eval_subst_single (φ : Name → Nat) (p : Name) (v : Level) (l : Level) :
    eval φ (subst [p] [v] l) = eval (upd φ p (eval φ v)) l := by
  rw [eval_subst]
  have h : substFn φ [p] [v] = upd φ p (eval φ v) := by
    funext n; simp [substFn, upd]
  rw [h]

/-- `byCases` is sound for an arbitrary split parameter. -/
theorem byCases_sound {fuel : Nat}
    (ih : ∀ l r diff, leqCore fuel l r diff = some true → Sem l r diff)
    {p : Name} {l r : Level} {diff : Int}
    (h : byCases fuel p l r diff = some true) : Sem l r diff := by
  unfold byCases at h
  obtain ⟨h0, hs⟩ := bind_and_some_true h
  have s0 := ih _ _ _ h0
  have ss := ih _ _ _ hs
  intro φ
  by_cases hp : φ p = 0
  · have := s0 (upd φ p 0)
    rw [eval_simplify, eval_simplify, eval_subst_single, eval_subst_single] at this
    have hupd : upd (upd φ p 0) p (eval (upd φ p 0) Level.zero) = φ := by
      funext n; simp only [upd, eval]; split <;> simp_all
    rw [hupd] at this
    exact this
  · obtain ⟨k, hk⟩ : ∃ k, φ p = k + 1 := ⟨φ p - 1, by omega⟩
    have := ss (upd φ p k)
    rw [eval_simplify, eval_simplify, eval_subst_single, eval_subst_single] at this
    have hupd : upd (upd φ p k) p (eval (upd φ p k) (Level.succ (Level.param p))) = φ := by
      funext n; simp only [upd, eval]; split <;> simp_all
    rw [hupd] at this
    exact this

private theorem eval_imax_imax (φ : Name → Nat) (a x y : Level) :
    eval φ (Level.imax a (.imax x y)) = eval φ (Level.max (.imax a y) (.imax x y)) := by
  simp only [eval]; grind

private theorem eval_imax_max (φ : Name → Nat) (a x y : Level) :
    eval φ (Level.imax a (.max x y)) = eval φ (Level.max (.imax a x) (.imax a y)) := by
  simp only [eval]; grind

/-- Soundness of `leqCore` (with `rest`, `imaxRules`, `byCases`):
a `some true` verdict means `l ≤ r + diff` under every assignment. -/
theorem leqCore_sound : ∀ {fuel : Nat} {l r : Level} {diff : Int},
    leqCore fuel l r diff = some true → Sem l r diff := by
  intro fuel
  induction fuel with
  | zero => intro l r diff h; simp [leqCore] at h
  | succ fuel ih =>
    have imaxRules_sound : ∀ {l r diff}, imaxRules fuel l r diff = some true → Sem l r diff := by
      intro l r diff h
      unfold imaxRules at h
      split at h
      · exact byCases_sound (fun _ _ _ => ih) h
      · exact byCases_sound (fun _ _ _ => ih) h
      · intro φ; have H := ih h φ; rw [eval_imax_imax]; exact H
      · intro φ; have H := ih h φ; rw [eval_simplify] at H; rw [eval_imax_max]; exact H
      · intro φ; have H := ih h φ; rw [eval_imax_imax]; exact H
      · intro φ; have H := ih h φ; rw [eval_simplify] at H; rw [eval_imax_max]; exact H
      · simp at h
    have rest_sound : ∀ {l r diff}, rest fuel l r diff = some true → Sem l r diff := by
      intro l r diff h
      unfold rest at h
      split at h
      · simp only [Option.some.injEq, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, hd⟩ := h
        intro φ; omega
      · simp at h
      · simp only [Option.some.injEq, decide_eq_true_eq] at h
        intro φ; simp only [eval]; omega
      · intro φ; have H := ih h φ; simp only [eval]; push_cast; omega
      · intro φ; have H := ih h φ; simp only [eval] at H ⊢; push_cast at H ⊢; omega
      · obtain ⟨h1, h2⟩ := bind_and_some_true h
        intro φ; have H1 := ih h1 φ; have H2 := ih h2 φ
        simp only [eval] at H1 H2 ⊢; omega
      · rcases bind_or_some_true h with h1 | h1 <;>
          { intro φ; have H := ih h1 φ; simp only [eval] at H ⊢; omega }
      · rcases bind_or_some_true h with h1 | h1 <;>
          { intro φ; have H := ih h1 φ; simp only [eval] at H ⊢; omega }
      · split at h
        · split at h
          · subst_eqs
            rename_i hcond
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            obtain ⟨⟨rfl, rfl⟩, hd⟩ := hcond
            intro φ; omega
          · exact imaxRules_sound h
        · exact imaxRules_sound h
    intro l r diff h
    unfold leqCore at h
    split at h
    · next hc =>
      obtain ⟨rfl, hd⟩ := hc
      intro φ; simp only [eval]; omega
    · split at h
      · simp at h
      · exact rest_sound h

theorem leq_sound {l r : Level} (h : leq l r = some true) :
    ∀ φ, eval φ l ≤ eval φ r := by
  intro φ
  have := leqCore_sound (fuel := defaultFuel) (by simpa [leq] using h) φ
  rw [eval_simplify, eval_simplify] at this
  omega

theorem isEquiv_sound {l r : Level} (h : isEquiv l r = some true) :
    ∀ φ, eval φ l = eval φ r := by
  intro φ
  obtain ⟨h1, h2⟩ := bind_and_some_true (by simpa [isEquiv] using h)
  exact Nat.le_antisymm (leq_sound h1 φ) (leq_sound h2 φ)

end Setlec.Level
