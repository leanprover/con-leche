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
  `Bool.true` shortcut, the two cheap `whnfCore` reducts, and then the
  easy cases, proof irrelevance, a lazy-delta verdict, or — on the pair
  the lazy loop got stuck on — the proj/proj check, the stuck
  comparison, or the restart after the full `whnfCore`.

The loops (`lazyDeltaReduction`, `lazyDeltaProjReduction`) and the
one-step helpers are bridged directly in `DefEqBridge.lean`, by
induction on their budgets.
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-- **The easy cases' `true` exits** (`quickDefEq`, `Kernel/Core.lean`). -/
inductive QuickExit (env : Env) (fuel d : Nat) : Expr → Expr → Prop where
  /-- The syntactic fast path. -/
  | refl {a : Expr} : QuickExit env fuel d a a
  /-- Two sorts at equivalent levels. -/
  | sort {u v : Level} :
      Level.isEquiv u v = some true →
      QuickExit env fuel d (.sort u) (.sort v)
  /-- Two equal literals. -/
  | lit {l : Literal} : QuickExit env fuel d (.lit l) (.lit l)
  /-- ∀-congruence, the bodies opened at the RIGHT domain, the
  annotations equal (the `.verified` validation). -/
  | forallE {ty₁ bd₁ ty₂ bd₂ : Expr} {m₁ m₂ : BinderMeta} :
      isDefEqCore .verified env fuel d ty₁ ty₂ = .ok true →
      isDefEqCore .verified env fuel (d + 1) (bd₁.instantiate1 (.fvar d ty₂))
        (bd₂.instantiate1 (.fvar d ty₂)) = .ok true →
      m₁.pw = m₂.pw →
      QuickExit env fuel d (.forallE ty₁ bd₁ m₁) (.forallE ty₂ bd₂ m₂)
  /-- λ-congruence, likewise. -/
  | lam {ty₁ bd₁ ty₂ bd₂ : Expr} {m₁ m₂ : BinderMeta} :
      isDefEqCore .verified env fuel d ty₁ ty₂ = .ok true →
      isDefEqCore .verified env fuel (d + 1) (bd₁.instantiate1 (.fvar d ty₂))
        (bd₂.instantiate1 (.fvar d ty₂)) = .ok true →
      m₁.pw = m₂.pw →
      QuickExit env fuel d (.lam ty₁ bd₁ m₁) (.lam ty₂ bd₂ m₂)

/-- The binder arms of `quickDefEq` (shared by ∀ and λ): a `some true`
run compared the domains, then the opened bodies, then passed the
annotation check. -/
private theorem binder_inv {d : Nat} {ty₁ bd₁ ty₂ bd₂ : Expr} {m₁ m₂ : BinderMeta}
    {msg : String}
    (h : (do
      unless ← isDefEqCore .verified env fuel d ty₁ ty₂ do return some false
      unless ← isDefEqCore .verified env fuel (d + 1)
          (bd₁.instantiate1 (.fvar d ty₂))
          (bd₂.instantiate1 (.fvar d ty₂)) do return some false
      if CheckMode.verified.verifiedChecks && !(m₁.pw == m₂.pw) then
        throw (.notImplemented msg)
      pure (some true) : CheckM (Option Bool)) = .ok (some true)) :
    isDefEqCore .verified env fuel d ty₁ ty₂ = .ok true ∧
    isDefEqCore .verified env fuel (d + 1) (bd₁.instantiate1 (.fvar d ty₂))
      (bd₂.instantiate1 (.fvar d ty₂)) = .ok true ∧
    m₁.pw = m₂.pw := by
  cases hdt : isDefEqCore .verified env fuel d ty₁ ty₂ with
  | error err => rw [hdt] at h; exact nomatch h
  | ok r =>
  rw [hdt] at h
  cases r with
  | false => simp [pure, Except.pure, Bind.bind, Except.bind] at h
  | true =>
  cases hbd : isDefEqCore .verified env fuel (d + 1)
      (bd₁.instantiate1 (.fvar d ty₂)) (bd₂.instantiate1 (.fvar d ty₂)) with
  | error err => rw [hbd] at h; simp [Bind.bind, Except.bind] at h
  | ok rb =>
  rw [hbd] at h
  cases rb with
  | false => simp [pure, Except.pure, Bind.bind, Except.bind] at h
  | true =>
  refine ⟨rfl, rfl, ?_⟩
  by_cases hq : (m₁.pw == m₂.pw) = true
  · exact eq_of_beq hq
  · exfalso
    have hq1 : (m₁.pw == m₂.pw) = false := by simpa using hq
    simp [hq1, CheckMode.verifiedChecks, throw, throwThe, MonadExceptOf.throw,
      Bind.bind, Except.bind] at h

/-- **The inversion of `quickDefEq`'s `some true`.** -/
theorem quickDefEq_inv {d : Nat} {a b : Expr}
    (h : quickDefEqFueled .verified env fuel d a b = .ok (some true)) :
    QuickExit env fuel d a b := by
  simp only [quickDefEqFueled, quickDefEq, defeq_def] at h
  by_cases hab : (a == b) = true
  · obtain rfl : a = b := eq_of_beq hab
    exact .refl
  rw [if_neg hab] at h
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
  · obtain ⟨h₁, h₂, h₃⟩ := binder_inv h
    exact .forallE h₁ h₂ h₃
  · obtain ⟨h₁, h₂, h₃⟩ := binder_inv h
    exact .lam h₁ h₂ h₃
  · simp [pure, Except.pure] at h

/-- **The stuck comparison's exits** (`defeqStuck`, `Kernel/Core.lean`).
`fallback` is the exit of every arm whose shape guard fails: they all
call `stuckIrrel` on the *same* pair, so one constructor stands for all
of them.  The others are the certificates the arms run, each at the
shapes its pattern pinned. -/
inductive DefeqStuckExit (env : Env) (fuel d : Nat) : Expr → Expr → Prop where
  /-- Every non-firing arm's fallback. -/
  | fallback {a b : Expr} :
      stuckIrrelFueled .verified env fuel d a b = .ok true →
      DefeqStuckExit env fuel d a b
  /-- A string literal against a `String.ofList` application. -/
  | strLitL {s : String} {x : Expr} :
      strLitSupported env = true →
      isDefEqCore .verified env fuel d (strLitToConstructor s)
        (.app (.const stringOfListName []) x) = .ok true →
      DefeqStuckExit env fuel d (.lit (.strVal s))
        (.app (.const stringOfListName []) x)
  /-- The mirror. -/
  | strLitR {s : String} {x : Expr} :
      strLitSupported env = true →
      isDefEqCore .verified env fuel d (.app (.const stringOfListName []) x)
        (strLitToConstructor s) = .ok true →
      DefeqStuckExit env fuel d (.app (.const stringOfListName []) x)
        (.lit (.strVal s))
  /-- Two free variables of the same index. -/
  | fvar {i : Nat} {ty₁ ty₂ : Expr} :
      DefeqStuckExit env fuel d (.fvar i ty₁) (.fvar i ty₂)
  /-- The same constant at equivalent levels. -/
  | const {n : Name} {us us' : List Level} :
      Level.isEquivList us us' = some true →
      DefeqStuckExit env fuel d (.const n us) (.const n us')
  /-- The stuck spine congruence (the equal-length guard is
  `defEqList`'s own). -/
  | spine {a b : Expr} :
      isDefEqCore .verified env fuel d a.getAppFn b.getAppFn = .ok true →
      defEqListFueled .verified env fuel d a.getAppArgs b.getAppArgs = .ok true →
      DefeqStuckExit env fuel d a b
  /-- A one-sided λ on the left — η. -/
  | etaL {ty bd : Expr} {mb : BinderMeta} {b : Expr} :
      etaCertFueled .verified env fuel d ty bd mb b = .ok true →
      DefeqStuckExit env fuel d (.lam ty bd mb) b
  /-- A one-sided λ on the right. -/
  | etaR {ty bd : Expr} {mb : BinderMeta} {a : Expr} :
      etaCertFueled .verified env fuel d ty bd mb a = .ok true →
      DefeqStuckExit env fuel d a (.lam ty bd mb)

/-- **The inversion of `defeqStuck`.** -/
theorem defeqStuck_inv {d : Nat} {a b : Expr}
    (h : defeqStuckFueled .verified env fuel d a b = .ok true) :
    DefeqStuckExit env fuel d a b := by
  have hfall : stuckIrrelFueled .verified env fuel d a b = .ok true →
      DefeqStuckExit env fuel d a b := DefeqStuckExit.fallback
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
    · cases hhd : isDefEqCore .verified env fuel d
          (Expr.app f₁ a₁).getAppFn (Expr.app f₂ a₂).getAppFn with
      | error err => rw [hhd] at h; exact nomatch h
      | ok r =>
      rw [hhd] at h
      dsimp only at h
      cases r with
      | false => exact hfall h
      | true =>
        cases hls : defEqListFueled .verified env fuel d
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
prefix's two exits and, under the two cheap `whnfCore` reducts, the
easy cases, proof irrelevance, a lazy-delta verdict, or the three ways
the comparison of the pair the lazy loop got stuck on can succeed. -/
theorem defeqBody_inv {d : Nat} {a b : Expr}
    (h : defeqBody .verified (pureFns .verified env fuel) env d a b = .ok true) :
    a = b ∨
    (b = .const boolTrueName [] ∧
      boolTrueShortcutFueled .verified env fuel d a = .ok true) ∨
    ∃ a' b', whnfCore .verified env fuel d a true = .ok a' ∧
      whnfCore .verified env fuel d b true = .ok b' ∧
      (quickDefEqFueled .verified env fuel d a' b' = .ok (some true) ∨
       propIrrelFueled .verified env fuel d a' b' = .ok true ∨
       lazyDeltaReductionFueled .verified env fuel d defeqLoopFuel a' b' =
         .ok (.verdict true) ∨
       ∃ a₁ b₁, lazyDeltaReductionFueled .verified env fuel d defeqLoopFuel a' b' =
           .ok (.unknown a₁ b₁) ∧
         (defeqProjPairFueled .verified env fuel d a₁ b₁ = .ok true ∨
          defeqStuckFueled .verified env fuel d a₁ b₁ = .ok true ∨
          ∃ a₂ b₂, whnfCore .verified env fuel d a₁ = .ok a₂ ∧
            whnfCore .verified env fuel d b₁ = .ok b₂ ∧
            isDefEqCore .verified env fuel d a₂ b₂ = .ok true)) := by
  simp only [defeqBody, Bind.bind, Except.bind, whnfCore_def,
    propIrrel_fold, boolTrueShortcut_fold, quickDefEq_fold,
    lazyDeltaReduction_fold, defeqProjPair_fold, defeqStuck_fold, defeq_def] at h
  by_cases hab : (a == b) = true
  · exact Or.inl (eq_of_beq hab)
  rw [if_neg hab] at h
  cases hbt : (if b.isBoolTrue && !a.hasFvar then
      boolTrueShortcutFueled .verified env fuel d a else pure false) with
  | error err => rw [hbt] at h; exact nomatch h
  | ok rbt =>
  rw [hbt] at h
  dsimp only at h
  cases rbt with
  | true =>
    have hbt' : boolTrueShortcutFueled .verified env fuel d a = .ok true ∧
        b.isBoolTrue = true := by
      split at hbt
      · next hc =>
        simp only [Bool.and_eq_true] at hc
        exact ⟨hbt, hc.1⟩
      · exact nomatch hbt
    exact Or.inr (Or.inl ⟨isBoolTrue_iff.mp hbt'.2, hbt'.1⟩)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hwca : whnfCore .verified env fuel d a true with
  | error err => rw [hwca] at h; exact nomatch h
  | ok a' =>
  rw [hwca] at h
  dsimp only at h
  cases hwcb : whnfCore .verified env fuel d b true with
  | error err => rw [hwcb] at h; exact nomatch h
  | ok b' =>
  rw [hwcb] at h
  dsimp only at h
  refine Or.inr (Or.inr ⟨a', b', rfl, rfl, ?_⟩)
  cases hq : quickDefEqFueled .verified env fuel d a' b' with
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
  cases hir : propIrrelFueled .verified env fuel d a' b' with
  | error err => rw [hir] at h; exact nomatch h
  | ok r =>
  rw [hir] at h
  dsimp only at h
  cases r with
  | true => exact Or.inr (Or.inl rfl)
  | false =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  cases hl : lazyDeltaReductionFueled .verified env fuel d defeqLoopFuel a' b' with
  | error err => rw [hl] at h; exact nomatch h
  | ok lr =>
  rw [hl] at h
  dsimp only at h
  cases lr with
  | verdict v =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inr (Or.inr (Or.inl rfl))
  | unknown a₁ b₁ =>
  refine Or.inr (Or.inr (Or.inr ⟨a₁, b₁, rfl, ?_⟩))
  dsimp only at h
  cases hpp : defeqProjPairFueled .verified env fuel d a₁ b₁ with
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
  cases hwa : whnfCore .verified env fuel d a₁ with
  | error err => rw [hwa] at h; exact nomatch h
  | ok a₂ =>
  rw [hwa] at h
  dsimp only at h
  cases hwb : whnfCore .verified env fuel d b₁ with
  | error err => rw [hwb] at h; exact nomatch h
  | ok b₂ =>
  rw [hwb] at h
  dsimp only at h
  split at h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨a₂, b₂, rfl, rfl, h⟩)

end ConLeche.Rules
