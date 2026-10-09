module

public import ConLeche.Verify.Rules.Defs
public import ConLeche.Verify.Rules.DefEqStepInv
import ConLeche.Verify.Rules.Certs
import ConLeche.Verify.Rules.RedBridge
import ConLeche.Rules.Derived

public section

/-!
# The definitional-equality bridge (task #305; lane CHEAPPROJ)

`isDefEqCore` at `fuel + 1` from the five bridges at `fuel`, one
lemma per piece of the body (`Kernel/Core.lean`), each landing on the
rules:

| piece | rule |
|---|---|
| `a == b` | `DefEq.refl` |
| the `Bool.true` shortcut | `boolTrueShortcut_bridge` |
| the cheap `whnfCore` of both sides | `DefEq.redBoth` |
| `quickDefEq` (`QuickExit`) | `refl` / `sort` / `forallE` / `lam` |
| `propIrrel` | `propIrrel_bridge` |
| `defeqOffset` | `refl` / `natZero` / `natSucc` / `app` |
| `tryUnfoldProjApp` | the `whnfCore` bridge |
| `lazyDeltaStep` | `Red.delta` + the `whnfCore` bridge per unfolded side; `defeqSpine_bridge` |
| `lazyDeltaReduction` | literal acceleration `redL`/`redR`; the steps' `Red` chains |
| `lazyDeltaProjReduction` / `defeqProjPair` | `projArg` chains; `DefEq.proj`; `reduceProjCore_bridge` |
| the restart after the full `whnfCore` | `DefEq.redBoth` + the `defeq` bridge |
| `defeqStuck` (`DefeqStuckExit`) | `fvar` / `const` / `spine` / `strLitL`/`R` / η / `stuckIrrel_bridge` |
-/

namespace ConLeche.Rules

variable {env : Env} {fuel : Nat}

/-- The easy cases' exits are equations. -/
theorem quickExit_bridge (hd : DefEqBridge env fuel) {d : Nat} {a b : Expr}
    (h : QuickExit env fuel d a b) : DefEq env d a b := by
  cases h with
  | refl => exact .refl
  | sort hle => exact .sort hle
  | lit => exact .refl
  | forallE hdt hbd hpw => exact .forallE (hd hdt) (hd hbd) hpw
  | lam hdt hbd hpw => exact .lam (hd hdt) (hd hbd) hpw

theorem quickDefEq_bridge (hd : DefEqBridge env fuel) {d : Nat} {a b : Expr}
    (h : quickDefEqFueled .verified env fuel d a b = .ok (some true)) :
    DefEq env d a b :=
  quickExit_bridge hd (quickDefEq_inv h)

/-- `Expr.natPred?`, read back. -/
private theorem natPred?_inv {e x : Expr} (h : e.natPred? = some x) :
    (∃ n, e = .lit (.natVal (n + 1)) ∧ x = .lit (.natVal n)) ∨
    e = .app (.const natSuccName []) x := by
  match e, h with
  | .lit (.natVal (n + 1)), h =>
    simp only [Expr.natPred?, Option.some.injEq] at h
    exact Or.inl ⟨n, rfl, h.symm⟩
  | .app (.const c []) y, h =>
    simp only [Expr.natPred?] at h
    split at h
    · next hc =>
      simp only [Option.some.injEq] at h
      subst hc h
      exact Or.inr rfl
    · exact nomatch h

/-- `Expr.isNatZero`, read back. -/
private theorem isNatZero_inv {e : Expr} (h : e.isNatZero = true) :
    e = .lit (.natVal 0) ∨ e = .const natZeroName [] := by
  match e, h with
  | .lit (.natVal 0), _ => exact Or.inl rfl
  | .const c [], h =>
    simp only [Expr.isNatZero, beq_iff_eq] at h
    exact Or.inr (by rw [h])

/-- **Offsets** (`defeqOffset`): two zeros, or a literal successor / a
`Nat.succ` against another, predecessors compared. -/
theorem defeqOffset_bridge (hd : DefEqBridge env fuel) {d : Nat} {a b : Expr}
    (h : defeqOffsetFueled .verified env fuel d a b = .ok (some true)) :
    DefEq env d a b := by
  simp only [defeqOffsetFueled, defeqOffset, defeq_def] at h
  split at h
  · next hz =>
    simp only [Bool.and_eq_true] at hz
    rcases isNatZero_inv hz.1 with rfl | rfl <;>
      rcases isNatZero_inv hz.2 with rfl | rfl
    · exact .refl
    · exact .natZero
    · exact .natZeroR
    · exact .refl
  split at h
  · simp [pure, Except.pure] at h
  · rename_i hnl
    split at h
    · rename_i x y hx hy
      simp only [Bind.bind, Except.bind] at h
      cases hde : isDefEqCore .verified env fuel d x y with
      | error err => rw [hde] at h; exact nomatch h
      | ok v =>
      rw [hde] at h
      simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      subst h
      have hxy := hd hde
      rcases natPred?_inv hx with ⟨n, rfl, rfl⟩ | rfl <;>
        rcases natPred?_inv hy with ⟨m, rfl, rfl⟩ | rfl
      · simp [Expr.isLit] at hnl
      · exact .natSucc hxy
      · exact .natSuccR hxy
      · exact .app .refl hxy
    · simp [pure, Except.pure] at h

/-- `tryUnfoldProjApp` is the full `whnfCore`. -/
theorem tryUnfoldProjApp_bridge (hwc : WhnfCoreBridge env fuel) {d : Nat}
    {e e' : Expr}
    (h : tryUnfoldProjAppFueled .verified env fuel d e = .ok (some e')) :
    Red env d e e' := by
  simp only [tryUnfoldProjAppFueled, tryUnfoldProjApp, Bind.bind, Except.bind,
    whnfCore_def] at h
  split at h
  · cases hw : whnfCore .verified env fuel d e with
    | error err => rw [hw] at h; exact nomatch h
    | ok e₁ =>
    rw [hw] at h
    dsimp only at h
    split at h
    · simp [pure, Except.pure] at h
    · simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact hwc hw
  · simp [pure, Except.pure] at h

/-- What a lazy-delta step's outcome says about the pair it started
from: `eq` is an equation, `cont` a pair of reductions. -/
@[expose] def StepSound (env : Env) (d : Nat) (a b : Expr) : DeltaStep → Prop
  | .eq => DefEq env d a b
  | .cont a' b' => Red env d a a' ∧ Red env d b b'
  | .diff => True
  | .unknown => True

/-- The end of a step (`deltaQuick`) on reducts of the pair. -/
private theorem deltaQuick_bridge (hd : DefEqBridge env fuel) {d : Nat}
    {a b x y : Expr} {r : DeltaStep}
    (h : deltaQuickFueled .verified env fuel d x y = .ok r)
    (hx : Red env d a x) (hy : Red env d b y) : StepSound env d a b r := by
  simp only [deltaQuickFueled, deltaQuick, Bind.bind, Except.bind,
    quickDefEq_fold] at h
  cases hq : quickDefEqFueled .verified env fuel d x y with
  | error err => rw [hq] at h; exact nomatch h
  | ok o =>
  rw [hq] at h
  dsimp only at h
  match o, hq, h with
  | none, _, h =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨hx, hy⟩
  | some false, _, h =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    trivial
  | some true, hq, h =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact .redBoth hx hy (quickDefEq_bridge hd hq)

/-- An unfolding put through the cheap `whnfCore`. -/
private theorem unfold_bridge (hwc : WhnfCoreBridge env fuel) {d : Nat}
    {a a₂ a₃ : Expr} (hu : unfoldDefinition env a = some a₂)
    (h : whnfCore .verified env fuel d a₂ true = .ok a₃) : Red env d a a₃ :=
  .trans (.delta hu) (hwc h)

/-- **One lazy-delta step** is sound. -/
theorem lazyDeltaStep_bridge (hwc : WhnfCoreBridge env fuel) (hd : DefEqBridge env fuel)
    {d : Nat} {a b : Expr} {r : DeltaStep}
    (h : lazyDeltaStepFueled .verified env fuel d a b = .ok r) :
    StepSound env d a b r := by
  simp only [lazyDeltaStepFueled, lazyDeltaStep, Bind.bind, Except.bind,
    whnfCore_def, tryUnfoldProjApp_fold, deltaQuick_fold, defeqSpine_fold] at h
  -- one unfolded side, put through the cheap `whnfCore`, then `deltaQuick`
  have hL : ∀ {a₂ a₃ : Expr}, unfoldDefinition env a = some a₂ →
      whnfCore .verified env fuel d a₂ true = .ok a₃ →
      deltaQuickFueled .verified env fuel d a₃ b = .ok r →
      StepSound env d a b r :=
    fun hu hw h => deltaQuick_bridge hd h (unfold_bridge hwc hu hw) .refl
  have hR : ∀ {b₂ b₃ : Expr}, unfoldDefinition env b = some b₂ →
      whnfCore .verified env fuel d b₂ true = .ok b₃ →
      deltaQuickFueled .verified env fuel d a b₃ = .ok r →
      StepSound env d a b r :=
    fun hu hw h => deltaQuick_bridge hd h .refl (unfold_bridge hwc hu hw)
  have hU : (pure DeltaStep.unknown : CheckM DeltaStep) = .ok r →
      StepSound env d a b r := by
    intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    trivial
  cases hda : unfoldableHead env a <;> cases hdb : unfoldableHead env b <;>
    rw [hda, hdb] at h <;> dsimp only at h
  · exact hU h
  · -- only `b` unfolds: `a`'s projection application first
    cases ht : tryUnfoldProjAppFueled .verified env fuel d a with
    | error err => rw [ht] at h; exact nomatch h
    | ok o =>
    rw [ht] at h
    dsimp only at h
    cases o with
    | some a₂ => exact deltaQuick_bridge hd h (tryUnfoldProjApp_bridge hwc ht) .refl
    | none =>
      dsimp only at h
      cases hu : unfoldDefinition env b with
      | none => rw [hu] at h; exact hU h
      | some b₂ =>
        rw [hu] at h; dsimp only at h
        cases hw : whnfCore .verified env fuel d b₂ true with
        | error err => rw [hw] at h; exact nomatch h
        | ok x => rw [hw] at h; exact hR hu hw h
  · -- only `a` unfolds: `b`'s projection application first
    cases ht : tryUnfoldProjAppFueled .verified env fuel d b with
    | error err => rw [ht] at h; exact nomatch h
    | ok o =>
    rw [ht] at h
    dsimp only at h
    cases o with
    | some b₂ => exact deltaQuick_bridge hd h .refl (tryUnfoldProjApp_bridge hwc ht)
    | none =>
      dsimp only at h
      cases hu : unfoldDefinition env a with
      | none => rw [hu] at h; exact hU h
      | some a₂ =>
        rw [hu] at h; dsimp only at h
        cases hw : whnfCore .verified env fuel d a₂ true with
        | error err => rw [hw] at h; exact nomatch h
        | ok x => rw [hw] at h; exact hL hu hw h
  · -- both unfold: the hints decide
    split at h
    · cases hu : unfoldDefinition env a with
      | none => rw [hu] at h; exact hU h
      | some a₂ =>
        rw [hu] at h; dsimp only at h
        cases hw : whnfCore .verified env fuel d a₂ true with
        | error err => rw [hw] at h; exact nomatch h
        | ok x => rw [hw] at h; exact hL hu hw h
    split at h
    · cases hu : unfoldDefinition env b with
      | none => rw [hu] at h; exact hU h
      | some b₂ =>
        rw [hu] at h; dsimp only at h
        cases hw : whnfCore .verified env fuel d b₂ true with
        | error err => rw [hw] at h; exact nomatch h
        | ok x => rw [hw] at h; exact hR hu hw h
    cases hsp : (if ReducibilityHint.sameRegular (headHint env a) (headHint env b) &&
        sameConstHeads a b then defeqSpineFueled .verified env fuel d a b
        else pure false) with
    | error err => rw [hsp] at h; exact nomatch h
    | ok sp =>
    rw [hsp] at h
    dsimp only at h
    cases sp with
    | true =>
      simp only [↓reduceIte, pure, Except.pure, Except.ok.injEq] at h
      subst h
      split at hsp
      · exact defeqSpine_bridge hd hsp
      · exact nomatch hsp
    | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hua : unfoldDefinition env a with
    | none => rw [hua] at h; exact hU h
    | some a₂ =>
    cases hub : unfoldDefinition env b with
    | none => rw [hua, hub] at h; exact hU h
    | some b₂ =>
    rw [hua, hub] at h
    dsimp only at h
    cases hwa : whnfCore .verified env fuel d a₂ true with
    | error err => rw [hwa] at h; exact nomatch h
    | ok a₃ =>
    rw [hwa] at h
    dsimp only at h
    cases hwb : whnfCore .verified env fuel d b₂ true with
    | error err => rw [hwb] at h; exact nomatch h
    | ok b₃ =>
    rw [hwb] at h
    exact deltaQuick_bridge hd h (unfold_bridge hwc hua hwa) (unfold_bridge hwc hub hwb)

/-- What the lazy-delta loop's outcome says about the pair it started
from: a `true` verdict is an equation, the stuck pair a pair of
reductions. -/
@[expose] def LazySound (env : Env) (d : Nat) (a b : Expr) : LazyRes → Prop
  | .verdict v => v = true → DefEq env d a b
  | .unknown a₁ b₁ => Red env d a a₁ ∧ Red env d b b₁

/-- **The lazy-delta loop** is sound, at every budget. -/
theorem lazyDeltaReduction_bridge (hwc : WhnfCoreBridge env fuel)
    (hw : WhnfBridge env fuel) (hd : DefEqBridge env fuel) {d : Nat} :
    ∀ (n : Nat) {a b : Expr} {r : LazyRes},
      lazyDeltaReductionFueled .verified env fuel d n a b = .ok r →
      LazySound env d a b r
  | 0, _, _, _, h => by
    simp [lazyDeltaReductionFueled, lazyDeltaReduction, throw, throwThe,
      MonadExceptOf.throw] at h
  | n + 1, a, b, r, h => by
    simp only [lazyDeltaReductionFueled, lazyDeltaReduction, Bind.bind, Except.bind,
      defeqOffset_fold, reduceNat_fold, lazyDeltaStep_fold, defeq_def] at h
    cases ho : defeqOffsetFueled .verified env fuel d a b with
    | error err => rw [ho] at h; exact nomatch h
    | ok o =>
    rw [ho] at h
    dsimp only at h
    cases o with
    | some v =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro hv
      subst hv
      exact defeqOffset_bridge hd ho
    | none =>
    dsimp only at h
    cases hna : (if !a.hasFvar && !b.hasFvar then
        reduceNatFueled .verified env fuel d a else pure none) with
    | error err => rw [hna] at h; exact nomatch h
    | ok o₁ =>
    rw [hna] at h
    dsimp only at h
    have hred : ∀ {x : Expr} {o : Option Expr} {g : Bool},
        (if g then reduceNatFueled .verified env fuel d x else pure none) = .ok o →
        ∀ {x₂ : Expr}, o = some x₂ → Red env d x x₂ := by
      intro x o g hx x₂ ho
      subst ho
      split at hx
      · exact reduceNat_bridge hw hx
      · simp [pure, Except.pure] at hx
    match o₁, hna, h with
    | some a₂, hna, h =>
      dsimp only at h
      cases hde : isDefEqCore .verified env fuel d a₂ b with
      | error err => rw [hde] at h; exact nomatch h
      | ok v =>
      rw [hde] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro hv
      subst hv
      exact .redL (hred hna rfl) (hd hde)
    | none, _, h =>
    dsimp only at h
    cases hnb : (if !a.hasFvar && !b.hasFvar then
        reduceNatFueled .verified env fuel d b else pure none) with
    | error err => rw [hnb] at h; exact nomatch h
    | ok o₂ =>
    rw [hnb] at h
    dsimp only at h
    match o₂, hnb, h with
    | some b₂, hnb, h =>
      dsimp only at h
      cases hde : isDefEqCore .verified env fuel d a b₂ with
      | error err => rw [hde] at h; exact nomatch h
      | ok v =>
      rw [hde] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro hv
      subst hv
      exact .redR (hred hnb rfl) (hd hde)
    | none, _, h =>
    dsimp only at h
    cases hs : lazyDeltaStepFueled .verified env fuel d a b with
    | error err => rw [hs] at h; exact nomatch h
    | ok st =>
    rw [hs] at h
    dsimp only at h
    have hss := lazyDeltaStep_bridge hwc hd hs
    cases st with
    | cont a' b' =>
      obtain ⟨ha, hb⟩ := hss
      have ih := lazyDeltaReduction_bridge hwc hw hd n h
      cases r with
      | verdict v => exact fun hv => .redBoth ha hb (ih hv)
      | unknown a₁ b₁ => exact ⟨.trans ha ih.1, .trans hb ih.2⟩
    | eq =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact fun _ => hss
    | diff =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      intro hv
      exact nomatch hv
    | unknown =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact ⟨.refl, .refl⟩

/-- **`a.i =?= b.i` by the scrutinees** (`lazyDeltaProjReduction`) is
sound, at every budget. -/
theorem lazyDeltaProjReduction_bridge (hwc : WhnfCoreBridge env fuel)
    (hw : WhnfBridge env fuel) (hd : DefEqBridge env fuel)
    (hio : InferIOBridge env fuel) {d : Nat} {sn : Name} {i : Nat} :
    ∀ (n : Nat) {a b : Expr},
      lazyDeltaProjReductionFueled .verified env fuel d sn i n a b = .ok true →
      DefEq env d (.proj sn i a) (.proj sn i b)
  | 0, _, _, h => by
    simp [lazyDeltaProjReductionFueled, lazyDeltaProjReduction, throw, throwThe,
      MonadExceptOf.throw] at h
  | n + 1, a, b, h => by
    simp only [lazyDeltaProjReductionFueled, lazyDeltaProjReduction, Bind.bind,
      Except.bind, lazyDeltaStep_fold, reduceProjCore_fold, defeq_def] at h
    cases hs : lazyDeltaStepFueled .verified env fuel d a b with
    | error err => rw [hs] at h; exact nomatch h
    | ok st =>
    rw [hs] at h
    dsimp only at h
    have hss := lazyDeltaStep_bridge hwc hd hs
    cases st
    case cont a' b' =>
      obtain ⟨ha, hb⟩ := hss
      exact .redBoth (.projArg ha) (.projArg hb)
        (lazyDeltaProjReduction_bridge hwc hw hd hio n h)
    case eq => exact .proj hss
    all_goals
      dsimp only at h
      cases hra : reduceProjCoreFueled .verified env fuel d sn i a with
      | error err => rw [hra] at h; exact nomatch h
      | ok oa =>
      rw [hra] at h
      dsimp only at h
      cases oa with
      | none => exact .proj (hd h)
      | some x =>
      dsimp only at h
      cases hrb : reduceProjCoreFueled .verified env fuel d sn i b with
      | error err => rw [hrb] at h; exact nomatch h
      | ok ob =>
      rw [hrb] at h
      dsimp only at h
      cases ob with
      | none => exact .proj (hd h)
      | some y =>
        exact .redBoth (reduceProjCore_bridge hw hd hio hra)
          (reduceProjCore_bridge hw hd hio hrb) (hd h)

/-- The proj/proj check. -/
theorem defeqProjPair_bridge (hwc : WhnfCoreBridge env fuel)
    (hw : WhnfBridge env fuel) (hd : DefEqBridge env fuel)
    (hio : InferIOBridge env fuel) {d : Nat} {a b : Expr}
    (h : defeqProjPairFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  simp only [defeqProjPairFueled, defeqProjPair, lazyDeltaProjReduction_fold] at h
  split at h
  · split at h
    · next hii =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hii
      obtain ⟨rfl, rfl⟩ := hii
      exact lazyDeltaProjReduction_bridge hwc hw hd hio _ h
    · simp [pure, Except.pure] at h
  · simp [pure, Except.pure] at h

/-- The stuck comparison: one rule per exit. -/
theorem defeqStuck_bridge (hw : WhnfBridge env fuel) (hd : DefEqBridge env fuel)
    (hio : InferIOBridge env fuel) {d : Nat} {a b : Expr}
    (h : defeqStuckFueled .verified env fuel d a b = .ok true) :
    DefEq env d a b := by
  cases defeqStuck_inv h with
  | fallback hs => exact stuckIrrel_bridge hw hd hio hs
  | strLitL hg hde => exact .strLitL hg (hd hde)
  | strLitR hg hde => exact .strLitR hg (hd hde)
  | fvar => exact .fvar
  | const hle => exact .const hle
  | spine hhd hls => exact .spine (hd hhd) (defEqList_bridge hd hls)
  | etaL he => exact etaCert_bridge hw hd hio he
  | etaR he => exact (etaCert_bridge hw hd hio he).symm

/-- **`isDefEqCore` at `fuel + 1`**: the body, piece by piece. -/
theorem defeq_bridge_succ (hwc : WhnfCoreBridge env fuel) (hw : WhnfBridge env fuel)
    (hd : DefEqBridge env fuel) (hio : InferIOBridge env fuel) :
    DefEqBridge env (fuel + 1) := by
  intro d a b h
  rw [isDefEqCore_succ] at h
  rcases defeqBody_inv h with rfl | ⟨rfl, hsc⟩ | hq₀ | hpi | ⟨a', b', hwa, hwb, hrest⟩
  · exact .refl
  · exact boolTrueShortcut_bridge hw hsc
  · exact quickDefEq_bridge hd hq₀
  · exact propIrrel_bridge hw hio hpi
  refine DefEq.redBoth (hwc hwa) (hwc hwb) ?_
  rcases hrest with hq | hl | ⟨a₁, b₁, hl, hpp | hst | ⟨a₂, b₂, hwa₂, hwb₂, hre⟩⟩
  · exact quickDefEq_bridge hd hq
  · exact lazyDeltaReduction_bridge hwc hw hd _ hl rfl
  · obtain ⟨ha, hb⟩ := lazyDeltaReduction_bridge hwc hw hd _ hl
    exact .redBoth ha hb (defeqProjPair_bridge hwc hw hd hio hpp)
  · obtain ⟨ha, hb⟩ := lazyDeltaReduction_bridge hwc hw hd _ hl
    exact .redBoth ha hb (defeqStuck_bridge hw hd hio hst)
  · obtain ⟨ha, hb⟩ := lazyDeltaReduction_bridge hwc hw hd _ hl
    exact .redBoth ha hb (.redBoth (hwc hwa₂) (hwc hwb₂) (hd hre))

end ConLeche.Rules
