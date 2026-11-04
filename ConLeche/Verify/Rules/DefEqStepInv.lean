module

public import ConLeche.Verify.Knot

public section

/-!
# The definitional-equality body, inverted (task #305; lane CHEAPPROJ)

The inversions on their own: the checker's case trees, read back as
disjunctions of the runs each exit made, with no model in sight.  (The
file kept its name from the fused `defeqStep` it inverted before lane
CHEAPPROJ split the body into the official kernel's pieces.)

* `quickDefEq_inv` — the easy cases (`QuickExit`): the syntactic fast
  path, two sorts, two literals, ∀- and λ-congruence.
* `defeqStuck_inv` — the stuck comparison's exits (`DefeqStuckExit`):
  the shape-directed certificates and the `stuckIrrel` fallback every
  non-firing arm takes, on the *same* pair, which is why one disjunct
  covers them all.
* `defeqBody_inv` — the body's case tree: the syntactic fast path, the
  `Bool.true` shortcut, the easy cases and proof irrelevance on the
  unreduced pair (task #333), and then, under the two cheap `whnfCore`
  reducts, the easy cases again, a lazy-delta verdict, or — on the pair
  the lazy loop got stuck on — the proj/proj check, the stuck
  comparison, or the restart after the full `whnfCore`.

The loops (`lazyDeltaReduction`, `lazyDeltaProjReduction`) and the
one-step helpers are bridged directly in `DefEqBridge.lean`, by
induction on their budgets.
-/

namespace ConLeche.Rules

variable {μ : CheckMode} {eager : Bool} {env : Env} {fuel : Nat}

/-- **The easy cases' `true` exits** (`quickDefEq`, `Kernel/Core.lean`). -/
inductive QuickExit (μ : CheckMode) (eager : Bool) (env : Env) (fuel d : Nat) : Expr → Expr → Prop
    where
  /-- The syntactic fast path. -/
  | refl {a : Expr} : QuickExit μ eager env fuel d a a
  /-- Two sorts at equivalent levels. -/
  | sort {u v : Level} :
      Level.isEquiv u v = some true →
      QuickExit μ eager env fuel d (.sort u) (.sort v)
  /-- Two equal literals. -/
  | lit {l : Literal} : QuickExit μ eager env fuel d (.lit l) (.lit l)
  /-- ∀-congruence, the bodies opened at the RIGHT domain. -/
  | forallE {ty₁ bd₁ ty₂ bd₂ : Expr} :
      isDefEqCore μ eager env fuel d ty₁ ty₂ = .ok true →
      isDefEqCore μ eager env fuel (d + 1) (bd₁.instantiate1 (.fvar d ty₂))
        (bd₂.instantiate1 (.fvar d ty₂)) = .ok true →
      QuickExit μ eager env fuel d (.forallE ty₁ bd₁) (.forallE ty₂ bd₂)
  /-- λ-congruence: the λ-telescope comparison (`defeqLams`). -/
  | lam {ty₁ bd₁ ty₂ bd₂ : Expr} :
      defeqLamsFueled μ eager env fuel lamsFuel d ty₁ bd₁ ty₂ bd₂ = .ok true →
      QuickExit μ eager env fuel d (.lam ty₁ bd₁) (.lam ty₂ bd₂)

/-- The ∀ arm of `quickDefEq`: a `some true` run compared the domains,
then the opened bodies. -/
private theorem binder_inv {d : Nat} {ty₁ bd₁ ty₂ bd₂ : Expr}
    (h : (do
      unless ← isDefEqCore μ eager env fuel d ty₁ ty₂ do return some false
      unless ← isDefEqCore μ eager env fuel (d + 1)
          (bd₁.instantiate1 (.fvar d ty₂))
          (bd₂.instantiate1 (.fvar d ty₂)) do return some false
      pure (some true) : CheckM (Option Bool)) = .ok (some true)) :
    isDefEqCore μ eager env fuel d ty₁ ty₂ = .ok true ∧
    isDefEqCore μ eager env fuel (d + 1) (bd₁.instantiate1 (.fvar d ty₂))
      (bd₂.instantiate1 (.fvar d ty₂)) = .ok true := by
  cases hdt : isDefEqCore μ eager env fuel d ty₁ ty₂ with
  | error err => rw [hdt] at h; exact nomatch h
  | ok r =>
  rw [hdt] at h
  cases r with
  | false => simp [pure, Except.pure, Bind.bind, Except.bind] at h
  | true =>
  cases hbd : isDefEqCore μ eager env fuel (d + 1)
      (bd₁.instantiate1 (.fvar d ty₂)) (bd₂.instantiate1 (.fvar d ty₂)) with
  | error err => rw [hbd] at h; simp [Bind.bind, Except.bind] at h
  | ok rb =>
  rw [hbd] at h
  cases rb with
  | false => simp [pure, Except.pure, Bind.bind, Except.bind] at h
  | true => exact ⟨rfl, rfl⟩

/-- **The innermost level of the λ-telescope comparison, inverted**: the
opened bodies compared, their full-grade types inferred and compared. -/
theorem defeqLamsInner_inv (hμ : μ.verifiedChecks = true) {d : Nat} {b₁ b₂ : Expr}
    (h : defeqLamsInnerFueled μ eager env fuel d b₁ b₂ = .ok true) :
    isDefEqCore μ eager env fuel (d + 1) b₁ b₂ = .ok true ∧
    ∃ t₁ t₂, inferTypeCore μ eager env fuel (d + 1) b₁ = .ok t₁ ∧
      inferTypeCore μ eager env fuel (d + 1) b₂ = .ok t₂ ∧
      isDefEqCore μ eager env fuel (d + 1) t₁ t₂ = .ok true := by
  simp only [defeqLamsInnerFueled, defeqLamsInner, defeq_def, infer_def,
    hμ] at h
  cases hb : isDefEqCore μ eager env fuel (d + 1) b₁ b₂ with
  | error err => simp [hb, Bind.bind, Except.bind] at h
  | ok r =>
  cases r with
  | false => simp [hb, pure, Except.pure, Bind.bind, Except.bind] at h
  | true =>
  refine ⟨rfl, ?_⟩
  cases h₁ : inferTypeCore μ eager env fuel (d + 1) b₁ with
  | error err => simp [hb, h₁, Bind.bind, Except.bind] at h
  | ok t₁ =>
  cases h₂ : inferTypeCore μ eager env fuel (d + 1) b₂ with
  | error err => simp [hb, h₁, h₂, Bind.bind, Except.bind] at h
  | ok t₂ =>
  cases ht : isDefEqCore μ eager env fuel (d + 1) t₁ t₂ with
  | error err => simp [hb, h₁, h₂, ht, Bind.bind, Except.bind] at h
  | ok rt =>
  cases rt with
  | false => simp [hb, h₁, h₂, ht, pure, Except.pure, Bind.bind, Except.bind] at h
  | true => exact ⟨t₁, t₂, rfl, rfl, ht⟩

/-- **The λ-telescope comparison, inverted** (`defeqLams`): the domains
compared, then either a descent into two λ bodies (equal, or compared
by the next level), or the innermost level. -/
theorem defeqLams_inv {k d : Nat} {ty₁ bd₁ ty₂ bd₂ : Expr}
    (h : defeqLamsFueled μ eager env fuel k d ty₁ bd₁ ty₂ bd₂ = .ok true) :
    isDefEqCore μ eager env fuel d ty₁ ty₂ = .ok true ∧
    ((∃ k' ty₁' bd₁' ty₂' bd₂', k = k' + 1 ∧
        bd₁.instantiate1 (.fvar d ty₂) = .lam ty₁' bd₁' ∧
        bd₂.instantiate1 (.fvar d ty₂) = .lam ty₂' bd₂' ∧
        (Expr.lam ty₁' bd₁' = .lam ty₂' bd₂' ∨
          defeqLamsFueled μ eager env fuel k' (d + 1) ty₁' bd₁' ty₂' bd₂' = .ok true)) ∨
      defeqLamsInnerFueled μ eager env fuel d (bd₁.instantiate1 (.fvar d ty₂))
        (bd₂.instantiate1 (.fvar d ty₂)) = .ok true) := by
  simp only [defeqLamsFueled] at h
  rw [defeqLams.eq_def] at h
  simp only [defeq_def] at h
  cases hdt : isDefEqCore μ eager env fuel d ty₁ ty₂ with
  | error err => rw [hdt] at h; exact nomatch h
  | ok r =>
  rw [hdt] at h
  cases r with
  | false => simp [pure, Except.pure, Bind.bind, Except.bind] at h
  | true =>
  refine ⟨rfl, ?_⟩
  simp only [Bind.bind, Except.bind, ↓reduceIte] at h
  split at h
  · obtain ⟨h₁, h₂⟩ := Expr.lamPair?_some ‹_›
    refine Or.inl ⟨_, _, _, _, _, rfl, h₁, h₂, ?_⟩
    rw [h₁, h₂] at h
    split at h
    · next heq => exact Or.inl (eq_of_beq heq)
    · exact Or.inr h
  · exact Or.inr h

/-- **The inversion of `quickDefEq`'s `some true`.** -/
theorem quickDefEq_inv {d : Nat} {a b : Expr}
    (h : quickDefEqFueled μ eager env fuel d a b = .ok (some true)) :
    QuickExit μ eager env fuel d a b := by
  simp only [quickDefEqFueled, quickDefEq, defeq_def] at h
  by_cases hab : (a == b) = true
  · obtain rfl : a = b := eq_of_beq hab
    exact .refl
  rw [ite_eq_right hab] at h
  split at h
  · rename_i u v
    simp only [Bind.bind, Except.bind] at h
    cases hle : Level.isEquiv u v with
    | none => rw [hle] at h; simp [liftFueled, throw, throwThe, MonadExceptOf.throw] at h
    | some r =>
      rw [hle] at h
      simp only [liftFueled, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact .sort hle
  · rename_i l₁ l₂
    simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
    obtain rfl : l₁ = l₂ := eq_of_beq h
    exact .lit
  · obtain ⟨h₁, h₂⟩ := binder_inv h
    exact .forallE h₁ h₂
  · simp only [Bind.bind, Except.bind] at h
    cases hl : defeqLams μ (pureFns μ eager env fuel) lamsFuel d _ _ _ _ with
    | error err => rw [hl] at h; exact nomatch h
    | ok r =>
      rw [hl] at h
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact .lam hl
  · simp [pure, Except.pure] at h

/-- **The stuck comparison's exits** (`defeqStuck`, `Kernel/Core.lean`).
`fallback` is the exit of every arm whose shape guard fails: they all
call `stuckIrrel` on the *same* pair, so one constructor stands for all
of them.  The others are the certificates the arms run, each at the
shapes its pattern pinned. -/
inductive DefeqStuckExit (μ : CheckMode) (eager : Bool) (env : Env) (fuel d : Nat) : Expr → Expr →
    Prop where
  /-- Every non-firing arm's fallback. -/
  | fallback {a b : Expr} :
      stuckIrrelFueled μ eager env fuel d a b = .ok true →
      DefeqStuckExit μ eager env fuel d a b
  /-- A string literal against a `String.ofList` application. -/
  | strLitL {s : String} {x : Expr} :
      strLitSupported env = true →
      isDefEqCore μ eager env fuel d (strLitToConstructor s)
        (.app (.const stringOfListName []) x) = .ok true →
      DefeqStuckExit μ eager env fuel d (.lit (.strVal s))
        (.app (.const stringOfListName []) x)
  /-- The mirror. -/
  | strLitR {s : String} {x : Expr} :
      strLitSupported env = true →
      isDefEqCore μ eager env fuel d (.app (.const stringOfListName []) x)
        (strLitToConstructor s) = .ok true →
      DefeqStuckExit μ eager env fuel d (.app (.const stringOfListName []) x)
        (.lit (.strVal s))
  /-- Two free variables of the same index. -/
  | fvar {i : Nat} {ty₁ ty₂ : Expr} :
      DefeqStuckExit μ eager env fuel d (.fvar i ty₁) (.fvar i ty₂)
  /-- The same constant at equivalent levels. -/
  | const {n : Name} {us us' : List Level} :
      Level.isEquivList us us' = some true →
      DefeqStuckExit μ eager env fuel d (.const n us) (.const n us')
  /-- The stuck spine congruence (the equal-length guard is
  `defEqList`'s own). -/
  | spine {a b : Expr} :
      isDefEqCore μ eager env fuel d a.getAppFn b.getAppFn = .ok true →
      defEqListFueled μ eager env fuel d a.getAppArgs b.getAppArgs = .ok true →
      DefeqStuckExit μ eager env fuel d a b
  /-- A one-sided λ on the left — η. -/
  | etaL {ty bd : Expr} {b : Expr} :
      etaCertFueled μ eager env fuel d ty bd b = .ok true →
      DefeqStuckExit μ eager env fuel d (.lam ty bd) b
  /-- A one-sided λ on the right. -/
  | etaR {ty bd : Expr} {a : Expr} :
      etaCertFueled μ eager env fuel d ty bd a = .ok true →
      DefeqStuckExit μ eager env fuel d a (.lam ty bd)

/-- **The inversion of `defeqStuck`.** -/
theorem defeqStuck_inv {d : Nat} {a b : Expr}
    (h : defeqStuckFueled μ eager env fuel d a b = .ok true) :
    DefeqStuckExit μ eager env fuel d a b := by
  have hfall : stuckIrrelFueled μ eager env fuel d a b = .ok true →
      DefeqStuckExit μ eager env fuel d a b := DefeqStuckExit.fallback
  simp only [defeqStuckFueled, defeqStuck, Bind.bind, Except.bind, defeq_def,
    stuckIrrel_fold, defEqList_fold, etaCert_fold] at h
  split at h
  · -- a string literal against a `String.ofList` application
    split at h
    · split at h
      · next hcond =>
        obtain ⟨rfl, rfl, hg⟩ := hcond
        exact .strLitL hg h
      · exact hfall h
    · exact hfall h
  · -- a `String.ofList` application against a string literal
    split at h
    · split at h
      · next hcond =>
        obtain ⟨rfl, rfl, hg⟩ := hcond
        exact .strLitR hg h
      · exact hfall h
    · exact hfall h
  · -- two free variables of the same index
    rename_i i t₁ j t₂
    split at h
    · next hij =>
      obtain rfl : i = j := eq_of_beq hij
      exact .fvar
    · exact hfall h
  · -- the same constant at equivalent levels
    rename_i n us n' us'
    split at h
    · next hnn =>
      subst hnn
      cases hle : Level.isEquivList us us' with
      | none => rw [hle] at h; exact nomatch h
      | some r =>
        rw [hle] at h
        dsimp only [liftFueled] at h
        cases r with
        | false => exact hfall h
        | true => exact .const hle
    · exact hfall h
  · -- the stuck spine congruence
    rename_i f₁ a₁ f₂ a₂
    split at h
    · cases hhd : isDefEqCore μ eager env fuel d
          (Expr.app f₁ a₁).getAppFn (Expr.app f₂ a₂).getAppFn with
      | error err => rw [hhd] at h; exact nomatch h
      | ok r =>
      rw [hhd] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        cases hls : defEqListFueled μ eager env fuel d
            (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs with
        | error err => rw [hls] at h; exact nomatch h
        | ok r' =>
        rw [hls] at h
        dsimp only at h
        cases r' with
        | false => exact hfall h
        | true => exact .spine hhd hls
    · exact hfall h
  · -- a one-sided λ on the left
    split at h
    · exact nomatch h
    · rename_i r he
      cases r
      · exact hfall (by simpa using h)
      · exact .etaL he
  · -- a one-sided λ on the right
    split at h
    · exact nomatch h
    · rename_i r he
      cases r
      · exact hfall (by simpa using h)
      · exact .etaR he
  · -- distinct stuck head symbols
    exact hfall h

/-- `Expr.isBoolTrue` reads exactly the constant `Bool.true`. -/
theorem isBoolTrue_iff {e : Expr} : e.isBoolTrue = true ↔ e = .const boolTrueName [] := by
  cases e <;> (try cases ‹List Level›) <;> simp [Expr.isBoolTrue]

/-- **The inversion of `defeqBody`** (`Kernel/Core.lean`): the
prefix's four exits (the syntactic fast path, the `Bool.true` shortcut,
the easy cases and proof irrelevance, both on the unreduced pair) and,
under the two cheap `whnfCore` reducts, the easy cases, a lazy-delta
verdict, or the three ways
the comparison of the pair the lazy loop got stuck on can succeed. -/
theorem defeqBody_inv {d : Nat} {a b : Expr}
    (h : defeqBody μ eager (pureFns μ eager env fuel) env d a b = .ok true) :
    a = b ∨
    (b = .const boolTrueName [] ∧
      boolTrueShortcutFueled μ eager env fuel d a = .ok true) ∨
    quickDefEqFueled μ eager env fuel d a b = .ok (some true) ∨
    propIrrelFueled μ eager env fuel d a b = .ok true ∨
    ∃ a' b', whnfCore μ eager env fuel d a true = .ok a' ∧
      whnfCore μ eager env fuel d b true = .ok b' ∧
      (quickDefEqFueled μ eager env fuel d a' b' = .ok (some true) ∨
       lazyDeltaReductionFueled μ eager env fuel d defeqLoopFuel a' b' =
         .ok (.verdict true) ∨
       ∃ a₁ b₁, lazyDeltaReductionFueled μ eager env fuel d defeqLoopFuel a' b' =
           .ok (.unknown a₁ b₁) ∧
         (defeqProjPairFueled μ eager env fuel d a₁ b₁ = .ok true ∨
          defeqStuckFueled μ eager env fuel d a₁ b₁ = .ok true ∨
          ∃ a₂ b₂, whnfCore μ eager env fuel d a₁ = .ok a₂ ∧
            whnfCore μ eager env fuel d b₁ = .ok b₂ ∧
            isDefEqCore μ eager env fuel d a₂ b₂ = .ok true)) := by
  simp only [defeqBody, Bind.bind, Except.bind, whnfCore_def,
    propIrrel_fold, boolTrueShortcut_fold, quickDefEq_fold,
    lazyDeltaReduction_fold, defeqProjPair_fold, defeqStuck_fold, defeq_def] at h
  by_cases hab : (a == b) = true
  · exact Or.inl (eq_of_beq hab)
  rw [ite_eq_right hab] at h
  cases hbt : (if b.isBoolTrue && (eager || !a.hasFvar) then
      boolTrueShortcutFueled μ eager env fuel d a else pure false) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok rbt =>
  rw [hbt] at h
  dsimp only at h
  cases rbt with
  | true =>
    have hbt' : boolTrueShortcutFueled μ eager env fuel d a = .ok true ∧
        b.isBoolTrue = true := by
      split at hbt
      · next hc =>
        simp only [Bool.and_eq_true] at hc
        exact ⟨hbt, hc.1⟩
      · exact nomatch hbt
    exact Or.inr (Or.inl ⟨isBoolTrue_iff.mp hbt'.2, hbt'.1⟩)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hq₀ : quickDefEqFueled μ eager env fuel d a b with
  | error err => rw [hq₀] at h; exact nomatch h
  | ok oq₀ =>
  rw [hq₀] at h
  dsimp only at h
  cases oq₀ with
  | some v =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inr (Or.inr (Or.inl rfl))
  | none =>
  dsimp only at h
  cases hir : propIrrelFueled μ eager env fuel d a b with
  | error err => rw [hir] at h; exact nomatch h
  | ok r =>
  rw [hir] at h
  dsimp only at h
  cases r with
  | true => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hwca : whnfCore μ eager env fuel d a true with
  | error err => rw [hwca] at h; exact nomatch h
  | ok a' =>
  rw [hwca] at h
  dsimp only at h
  cases hwcb : whnfCore μ eager env fuel d b true with
  | error err => rw [hwcb] at h; exact nomatch h
  | ok b' =>
  rw [hwcb] at h
  dsimp only at h
  refine Or.inr (Or.inr (Or.inr (Or.inr ⟨a', b', rfl, rfl, ?_⟩)))
  cases hq : quickDefEqFueled μ eager env fuel d a' b' with
  | error err => rw [hq] at h; exact nomatch h
  | ok oq =>
  rw [hq] at h
  dsimp only at h
  cases oq with
  | some v =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inl rfl
  | none =>
  dsimp only at h
  cases hl : lazyDeltaReductionFueled μ eager env fuel d defeqLoopFuel a' b' with
  | error err => rw [hl] at h; exact nomatch h
  | ok lr =>
  rw [hl] at h
  dsimp only at h
  cases lr with
  | verdict v =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inr (Or.inl rfl)
  | unknown a₁ b₁ =>
  refine Or.inr (Or.inr ⟨a₁, b₁, rfl, ?_⟩)
  dsimp only at h
  cases hpp : defeqProjPairFueled μ eager env fuel d a₁ b₁ with
  | error err => rw [hpp] at h; exact nomatch h
  | ok rp =>
  rw [hpp] at h
  dsimp only at h
  cases rp with
  | true => exact Or.inl rfl
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  split at h
  · exact Or.inr (Or.inl h)
  cases hwa : whnfCore μ eager env fuel d a₁ with
  | error err => rw [hwa] at h; exact nomatch h
  | ok a₂ =>
  rw [hwa] at h
  dsimp only at h
  cases hwb : whnfCore μ eager env fuel d b₁ with
  | error err => rw [hwb] at h; exact nomatch h
  | ok b₂ =>
  rw [hwb] at h
  dsimp only at h
  split at h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨a₂, b₂, rfl, rfl, h⟩)

end ConLeche.Rules
