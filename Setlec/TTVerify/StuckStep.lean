import Setlec.TTVerify.ProofIrrelStep

/-!
# The stuck configuration

`DefEqStuckStepTT`: `defeqStep` reached its last block — neither side
reduced, neither is a proof, neither head unfolds — so the verdict came
from a leaf comparison, a congruence, or one of the two named
certificate functions the block calls.

Those two are the obligations this file leaves behind, and they sit
where §8.6's factoring rule puts them: at functions the checker names.
-/

namespace Setlec.TTVerify

/- Task #147: this file's lemmas are stated at the TT-lane mode — the
seven gated checks reduce definitionally at `.ttModel`, so the walks
below see the pre-#147 bodies (`CertifiedConfigTT` pins the running
mode to this value). -/
private abbrev mode : CheckMode := .ttModel

open Setlec.TT

/-- `stuckIrrel`'s verdict yields an equation: the five rescues (pair
eta either way, structural eta either way, unit-likeness) with proof
irrelevance last. -/
def StuckIrrelStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {a b : Expr},
    stuckIrrelP mode env fuel d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ a → CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr}, denote m.cval env φ d a = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-- `etaCert`'s verdict yields an equation: a one-sided λ is the other
side's eta-expansion. -/
def EtaCertStepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δ : List VExpr} {n : Name} {ty body b : Expr}
    {mb : BinderMeta},
    etaCertP mode env fuel d n ty body mb b = .ok true →
    Expr.WScoped d (.lam n ty body mb) →
    (Expr.lam n ty body mb).looseBVarsBounded 0 = true →
    Expr.LeavesBounded (.lam n ty body mb) →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    CtxOk m.cval env φ d Δ (.lam n ty body mb) →
    CtxOk m.cval env φ d Δ b →
    ∀ {va vb : VExpr},
      denote m.cval env φ d (.lam n ty body mb) = some va →
      denote m.cval env φ d b = some vb → Deq Δ va vb

/-- A `liftFueled` call that returns a value had one. -/
theorem liftFueled_ok_inv {α : Type} {what : String} {o : Option α}
    {v : α} (h : (liftFueled what o : CheckM α) = .ok v) : o = some v := by
  cases o with
  | none => simp [liftFueled, throw, throwThe, MonadExceptOf.throw] at h
  | some x =>
    simp only [liftFueled, pure, Except.pure, Except.ok.injEq] at h
    rw [h]

/-- A stored constant at the empty instantiation denotes to its
valuation there. -/
theorem denote_const_nil {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {d : Nat} {c : Name} {v : VExpr}
    (h : denote m.cval env φ d (.const c []) = some v) :
    m.cval c (Level.substFn φ [] []) = v := by
  rw [denote_const] at h
  cases hf : env.find? c with
  | none => rw [hf] at h; exact nomatch h
  | some ci =>
    rw [hf] at h
    dsimp only at h
    split at h
    · next hlen =>
      rw [List.eq_nil_of_length_eq_zero hlen.symm] at h
      exact Option.some.inj h
    · exact nomatch h

/-- The literal `0` and the stored `Nat.zero` denote to the same term:
both are the constant's valuation at the empty instantiation. -/
theorem natZero_lit_const {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {d : Nat} {va vb : VExpr}
    (hva : denote m.cval env φ d (.lit (.natVal 0)) = some va)
    (hvb : denote m.cval env φ d (.const natZeroName []) = some vb) :
    Deq Δ va vb := by
  rw [denote_natLit] at hva
  split at hva
  · obtain rfl : natLitT (m.cval natZeroName (Level.substFn φ [] []))
        (m.cval natSuccName (Level.substFn φ [] [])) 0 = va :=
      Option.some.inj hva
    rw [← denote_const_nil m φ hvb]
    exact Deq.refl
  · exact nomatch hva

/-- The frame conditions of a literal, which has no structure to
constrain. -/
theorem lit_frames {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} (hlen : Δ.length = d) (l : Literal) :
    Expr.WScoped d (.lit l) ∧
      (Expr.lit l).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (.lit l) ∧ CtxOk cval env φ d Δ (.lit l) := by
  refine ⟨by simp [Expr.WScoped], rfl, ?_, hlen, ?_⟩ <;>
    (intro x hx; simp [Expr.fvarLeaves] at hx)

/-- The frame conditions of an application's two parts. -/
theorem app_frames {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {f x : Expr}
    (hw : Expr.WScoped d (.app f x))
    (hb : (Expr.app f x).looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded (.app f x))
    (hC : CtxOk cval env φ d Δ (.app f x)) :
    (Expr.WScoped d f ∧ f.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded f ∧ CtxOk cval env φ d Δ f) ∧
      (Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOk cval env φ d Δ x) := by
  simp only [Expr.WScoped] at hw
  simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
  exact ⟨⟨hw.1, hb.1, fun l hl => hL l (by simp [Expr.fvarLeaves, hl]),
      CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC⟩,
    hw.2, hb.2, fun l hl => hL l (by simp [Expr.fvarLeaves, hl]),
      CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hC⟩

/-- **A `Nat` literal against a `Nat.succ` application.**  The literal
is the successor of its predecessor's denotation, so the pair is one
`Deq` at the argument. -/
theorem natSucc_lit_app {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {d : Nat} {Δ : List VExpr} {k : Nat} {x : Expr} {va vb vx : VExpr}
    (hva : denote m.cval env φ d (.lit (.natVal (k + 1))) = some va)
    (hvf : denote m.cval env φ d (.const natSuccName []) = some vb)
    (_hvx : denote m.cval env φ d x = some vx)
    (hlit : ∀ w, denote m.cval env φ d (.lit (.natVal k)) = some w →
      Deq Δ w vx) :
    Deq Δ va (.app vb vx) := by
  rw [denote_natLit] at hva
  split at hva
  · next hg =>
    obtain rfl : natLitT (m.cval natZeroName (Level.substFn φ [] []))
        (m.cval natSuccName (Level.substFn φ [] [])) (k + 1) = va :=
      Option.some.inj hva
    rw [← denote_const_nil m φ hvf]
    refine Deq.appArg (hlit _ ?_)
    rw [denote_natLit, if_pos hg]
  · exact nomatch hva

/-- The frame conditions of a closed expression. -/
theorem closed_frames {cval : TConstVal} {env : Env} {φ : Name → Nat}
    {d : Nat} {Δ : List VExpr} {e : Expr} (hlen : Δ.length = d)
    (hnf : e.hasFvar = false) (hb : e.looseBVarsBounded 0 = true) :
    Expr.WScoped d e ∧ e.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e ∧ CtxOk cval env φ d Δ e :=
  ⟨Expr.WScoped.of_not_hasFvar hnf, hb,
    Expr.LeavesBounded.of_not_hasFvar hnf, hlen, fun l hl => by
      rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at hl
      exact nomatch hl⟩

/-! ## The binder congruences

`.lam`/`.lam` and `.forallE`/`.forallE` are the *same* proof — certify
the domains, open both bodies, recurse — and the layer has `congrLam`
and `congrPi` at exactly that shape, so the content is one lemma and
the two clauses differ only in which rule they end with.

**This is where `CtxOk`'s typing form is spent** (`Setlec/TTVerify/
Claims.lean`).  The checker opens each body with *its own* annotation,
so the second side's leaf is `(d, n₂, ty₂)` while the context's new head
is `⟦ty₁⟧`; `CtxOk.openWith` takes the new variable's typing as a
premise, and the premise is `HasType.bvar` converted along the domain
equation the checker just certified. -/

/-- The two equations a binder congruence needs: the domains, and the
opened bodies in the context the first domain extends. -/
theorem binder_congr {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (ihd : DefEqClaimsTT mode m φ fuel)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    {d : Nat} {Δ : List VExpr} {n₁ n₂ : Name}
    {ty₁ ty₂ body₁ body₂ : Expr} {A₁ B₁ A₂ B₂ : VExpr}
    (hty : isDefEqCore mode env fuel d ty₁ ty₂ = .ok true)
    (hbody : isDefEqCore mode env fuel (d + 1)
      (body₁.instantiate1 (.fvar d n₁ ty₁))
      (body₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true)
    (hw1 : Expr.WScoped d ty₁ ∧ Expr.WScoped d body₁)
    (hb1 : ty₁.looseBVarsBounded 0 = true ∧
      body₁.looseBVarsBounded 1 = true)
    (hL1 : Expr.LeavesBounded ty₁ ∧ Expr.LeavesBounded body₁)
    (hC1 : CtxOk m.cval env φ d Δ ty₁ ∧ CtxOk m.cval env φ d Δ body₁)
    (hw2 : Expr.WScoped d ty₂ ∧ Expr.WScoped d body₂)
    (hb2 : ty₂.looseBVarsBounded 0 = true ∧
      body₂.looseBVarsBounded 1 = true)
    (hL2 : Expr.LeavesBounded ty₂ ∧ Expr.LeavesBounded body₂)
    (hC2 : CtxOk m.cval env φ d Δ ty₂ ∧ CtxOk m.cval env φ d Δ body₂)
    (hA1 : denote m.cval env φ d ty₁ = some A₁)
    (hB1 : denote m.cval env φ (d + 1)
      (body₁.instantiate1 (.fvar d n₁ ty₁)) = some B₁)
    (hA2 : denote m.cval env φ d ty₂ = some A₂)
    (hB2 : denote m.cval env φ (d + 1)
      (body₂.instantiate1 (.fvar d n₂ ty₂)) = some B₂) :
    Deq Δ A₁ A₂ ∧ Deq (A₁ :: Δ) B₁ B₂ := by
  have hDA : Deq Δ A₁ A₂ :=
    ihd hty hw1.1 hb1.1 hL1.1 hw2.1 hb2.1 hL2.1 hC1.1 hC2.1 hA1 hA2
  refine ⟨hDA, ?_⟩
  -- the first side opens with its own annotation
  have hO1 : CtxOk m.cval env φ (d + 1) (A₁ :: Δ)
      (body₁.instantiate1 (.fvar d n₁ ty₁)) :=
    CtxOk.open hcl hC1.2 hC1.1 hA1 hw1.1.fvarsBelow
  -- the second opens with its own, in the *first*'s context
  have hnew : HasType (A₁ :: Δ) (.bvar 0) (A₂.liftN 1) :=
    Deq.conv (HasType.bvar (A := A₁) (by simp))
      (Deq.weakenHead A₁ hDA)
  have hO2 : CtxOk m.cval env φ (d + 1) (A₁ :: Δ)
      (body₂.instantiate1 (.fvar d n₂ ty₂)) :=
    CtxOk.openWith hcl hC2.2 hC2.1 hA2 hw2.1.fvarsBelow hnew
  exact ihd hbody (Expr.WScoped.instantiate1 hw1.1 0 hw1.2)
    (looseBVarsBounded_instantiate1 body₁ 0 hb1.2)
    (fun l hl => by
      rcases Expr.fvarLeaves_instantiate1 body₁ 0 hl with h2 | h2
      · exact hL1.2 l h2
      · rw [Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact hb1.1
        · exact hL1.1 l h3)
    (Expr.WScoped.instantiate1 hw2.1 0 hw2.2)
    (looseBVarsBounded_instantiate1 body₂ 0 hb2.2)
    (fun l hl => by
      rcases Expr.fvarLeaves_instantiate1 body₂ 0 hl with h2 | h2
      · exact hL2.2 l h2
      · rw [Expr.fvarLeaves] at h2
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact hb2.1
        · exact hL2.1 l h3)
    hO1 hO2 hB1 hB2

/-! ## The walk to the block

The premises replay `defeqStep`'s opening moves in order.  This is the
duplication the *input-space restriction* costs: `defeqStep_claim` walks
the same moves to reach the block, and this proof walks them again to
enter it.  It is the price of not slicing the body into stages — the
walk is ten rewrites, the block is the content. -/

/-- **`DefEqStuckStepTT`, discharged.** -/
theorem defeqStuck_stepTT {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (ihd : DefEqClaimsTT mode m φ fuel)
    (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (hsi : StuckIrrelStepTT m φ fuel) (hec : EtaCertStepTT m φ fuel) :
    DefEqStuckStepTT m φ fuel := by
  intro d Δ k a b a' b' h hab hwca hwcb hab' hir hna hnb hha hhb
    hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' va' vb' hva' hvb'
  simp only [defeqStep, Bind.bind, Except.bind, whnfCore_def,
    reduceNat_fold, stuckIrrel_fold,
    defeq_def, hab, hwca, hwcb, hab', hir, hna, hnb, hha, hhb,
    Bool.false_eq_true, if_false] at h
  split at h
  case h_1 _ _ u v =>
    have hlv : Level.eval φ u = Level.eval φ v :=
      Level.isEquiv_sound (liftFueled_ok_inv h) φ
    rw [denote_sort] at hva' hvb'
    obtain rfl : VExpr.sort (Level.eval φ u) = va' := Option.some.inj hva'
    obtain rfl : VExpr.sort (Level.eval φ v) = vb' := Option.some.inj hvb'
    rw [hlv]
  case h_2 _ _ l₁ l₂ =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain rfl : l₁ = l₂ := eq_of_beq h
    simp at hab'
  case h_3 _ _ n c us =>
    by_cases hg : c = natZeroName ∧ us = []
    · rw [if_pos hg] at h
      obtain ⟨rfl, rfl⟩ := hg
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h
      exact natZero_lit_const m φ hva' hvb'
    · rw [if_neg hg] at h
      exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_4 _ _ c us n =>
    by_cases hg : c = natZeroName ∧ us = []
    · rw [if_pos hg] at h
      obtain ⟨rfl, rfl⟩ := hg
      simp only [pure, Except.pure, Except.ok.injEq] at h
      obtain rfl : n = 0 := by simpa using h
      exact (natZero_lit_const m φ hvb' hva').symm
    · rw [if_neg hg] at h
      exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_5 _ _ nn f x =>
    split at h
    case h_1 k c =>
      by_cases hc : c = natSuccName
      · rw [if_pos hc] at h
        subst hc
        obtain ⟨-, hfx⟩ := app_frames hwb' hbb' hLb' hCb'
        rw [denote_app] at hvb'
        cases hvf : denote m.cval env φ d (Expr.const natSuccName []) with
        | none => rw [hvf] at hvb'; exact nomatch hvb'
        | some vf =>
        cases hvx : denote m.cval env φ d x with
        | none => rw [hvf, hvx] at hvb'; exact nomatch hvb'
        | some vx =>
        rw [hvf, hvx] at hvb'
        dsimp only at hvb'
        obtain rfl : VExpr.app vf vx = vb' := Option.some.inj hvb'
        refine natSucc_lit_app m φ hva' hvf hvx (fun w hw => ?_)
        obtain ⟨hwl, hbl, hLl, hCl⟩ := lit_frames (cval := m.cval)
          (env := env) (φ := φ) hCa'.1 (Literal.natVal k)
        exact ihd h hwl hbl hLl hfx.1 hfx.2.1 hfx.2.2.1 hCl hfx.2.2.2 hw hvx
      · rw [if_neg hc] at h
        exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
    case h_2 => exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_6 _ _ f x nn =>
    split at h
    case h_1 k c =>
      by_cases hc : c = natSuccName
      · rw [if_pos hc] at h
        subst hc
        obtain ⟨-, hfx⟩ := app_frames hwa' hba' hLa' hCa'
        rw [denote_app] at hva'
        cases hvf : denote m.cval env φ d (Expr.const natSuccName []) with
        | none => rw [hvf] at hva'; exact nomatch hva'
        | some vf =>
        cases hvx : denote m.cval env φ d x with
        | none => rw [hvf, hvx] at hva'; exact nomatch hva'
        | some vx =>
        rw [hvf, hvx] at hva'
        dsimp only at hva'
        obtain rfl : VExpr.app vf vx = va' := Option.some.inj hva'
        refine (natSucc_lit_app m φ hvb' hvf hvx (fun w hw => ?_)).symm
        obtain ⟨hwl, hbl, hLl, hCl⟩ := lit_frames (cval := m.cval)
          (env := env) (φ := φ) hCb'.1 (Literal.natVal k)
        exact (ihd h hfx.1 hfx.2.1 hfx.2.2.1 hwl hbl hLl hfx.2.2.2 hCl
          hvx hw).symm
      · rw [if_neg hc] at h
        exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
    case h_2 => exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_7 _ _ st cO usO x =>
    by_cases hg : cO = stringOfListName ∧ usO = [] ∧
        strLitSupported env = true
    · rw [if_pos hg] at h
      obtain ⟨rfl, rfl, hs⟩ := hg
      obtain ⟨hw, hb, hL, hC⟩ := closed_frames (cval := m.cval)
        (env := env) (φ := φ) hCa'.1 (strLitToConstructor_hasFvar st)
        (strLitToConstructor_looseBVars st 0)
      refine ihd h hw hb hL hwb' hbb' hLb' hC hCb' ?_ hvb'
      rw [denote_strLitToConstructor m φ hs d]; exact hva'
    · rw [if_neg hg] at h
      exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_8 _ _ cO usO x st =>
    by_cases hg : cO = stringOfListName ∧ usO = [] ∧
        strLitSupported env = true
    · rw [if_pos hg] at h
      obtain ⟨rfl, rfl, hs⟩ := hg
      obtain ⟨hw, hb, hL, hC⟩ := closed_frames (cval := m.cval)
        (env := env) (φ := φ) hCb'.1 (strLitToConstructor_hasFvar st)
        (strLitToConstructor_looseBVars st 0)
      refine ihd h hwa' hba' hLa' hw hb hL hCa' hC hva' ?_
      rw [denote_strLitToConstructor m φ hs d]; exact hvb'
    · rw [if_neg hg] at h
      exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_9 _ _ i n₁ ty₁ j n₂ ty₂ =>
    by_cases hij : (i == j) = true
    · rw [if_pos hij] at h
      obtain rfl : i = j := eq_of_beq hij
      rw [denote_fvar] at hva' hvb'
      obtain rfl : VExpr.bvar (d - 1 - i) = va' := Option.some.inj hva'
      obtain rfl : VExpr.bvar (d - 1 - i) = vb' := Option.some.inj hvb'
      exact Deq.refl
    · rw [if_neg hij] at h
      exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_10 _ _ n us n' us' =>
    by_cases hnn : n = n'
    · subst hnn
      rw [if_pos rfl] at h
      cases hle : liftFueled (m := CheckM) "level comparison"
          (Level.isEquivList us us') with
      | error err => rw [hle] at h; exact nomatch h
      | ok v =>
        rw [hle] at h
        cases v with
        | false =>
          simp only [Bool.false_eq_true, if_false] at h
          exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
        | true =>
          obtain rfl :=
            denote_const_congr m φ (liftFueled_ok_inv hle) hva' hvb'
          exact Deq.refl
    · rw [if_neg hnn] at h
      exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_11 _ _ n₁ ty₁ body₁ mb₁ n₂ ty₂ body₂ mb₂ =>
    cases hty : isDefEqCore mode env fuel d ty₁ ty₂ with
    | error err => rw [hty] at h; exact nomatch h
    | ok v =>
      rw [hty] at h
      cases v with
      | false => simp [pure, Except.pure] at h
      | true =>
        simp only [if_true] at h
        simp only [Expr.WScoped] at hwa' hwb'
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
        rw [denote_forallE] at hva' hvb'
        cases hA1 : denote m.cval env φ d ty₁ with
        | none => rw [hA1] at hva'; exact nomatch hva'
        | some A₁ =>
        cases hB1 : denote m.cval env φ (d + 1)
            (body₁.instantiate1 (.fvar d n₁ ty₁)) with
        | none => rw [hA1, hB1] at hva'; exact nomatch hva'
        | some B₁ =>
        cases hA2 : denote m.cval env φ d ty₂ with
        | none => rw [hA2] at hvb'; exact nomatch hvb'
        | some A₂ =>
        cases hB2 : denote m.cval env φ (d + 1)
            (body₂.instantiate1 (.fvar d n₂ ty₂)) with
        | none => rw [hA2, hB2] at hvb'; exact nomatch hvb'
        | some B₂ =>
        rw [hA1, hB1] at hva'
        rw [hA2, hB2] at hvb'
        obtain rfl : VExpr.pi A₁ B₁ = va' := Option.some.inj hva'
        obtain rfl : VExpr.pi A₂ B₂ = vb' := Option.some.inj hvb'
        obtain ⟨hDA, hDB⟩ := binder_congr m φ ihd hcl hty h hwa' hba'
          ⟨fun l hl => hLa' l (by simp [Expr.fvarLeaves, hl]),
            fun l hl => hLa' l (by simp [Expr.fvarLeaves, hl])⟩
          ⟨CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa',
            CtxOk.of_subset (fun l hl => by
              simp [Expr.fvarLeaves, hl]) hCa'⟩
          hwb' hbb'
          ⟨fun l hl => hLb' l (by simp [Expr.fvarLeaves, hl]),
            fun l hl => hLb' l (by simp [Expr.fvarLeaves, hl])⟩
          ⟨CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb',
            CtxOk.of_subset (fun l hl => by
              simp [Expr.fvarLeaves, hl]) hCb'⟩
          hA1 hB1 hA2 hB2
        obtain ⟨T, hT⟩ := hDA
        obtain ⟨T', hT'⟩ := hDB
        exact ⟨.sort 0, HasType.congrPi hT hT'⟩
  case h_12 _ _ n₁ ty₁ body₁ mb₁ n₂ ty₂ body₂ mb₂ =>
    cases hty : isDefEqCore mode env fuel d ty₁ ty₂ with
    | error err => rw [hty] at h; exact nomatch h
    | ok v =>
      rw [hty] at h
      cases v with
      | false => simp [pure, Except.pure] at h
      | true =>
        simp only [if_true] at h
        simp only [Expr.WScoped] at hwa' hwb'
        simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hba' hbb'
        rw [denote_lam] at hva' hvb'
        cases hA1 : denote m.cval env φ d ty₁ with
        | none => rw [hA1] at hva'; exact nomatch hva'
        | some A₁ =>
        cases hB1 : denote m.cval env φ (d + 1)
            (body₁.instantiate1 (.fvar d n₁ ty₁)) with
        | none => rw [hA1, hB1] at hva'; exact nomatch hva'
        | some B₁ =>
        cases hA2 : denote m.cval env φ d ty₂ with
        | none => rw [hA2] at hvb'; exact nomatch hvb'
        | some A₂ =>
        cases hB2 : denote m.cval env φ (d + 1)
            (body₂.instantiate1 (.fvar d n₂ ty₂)) with
        | none => rw [hA2, hB2] at hvb'; exact nomatch hvb'
        | some B₂ =>
        rw [hA1, hB1] at hva'
        rw [hA2, hB2] at hvb'
        obtain rfl : VExpr.lam A₁ B₁ = va' := Option.some.inj hva'
        obtain rfl : VExpr.lam A₂ B₂ = vb' := Option.some.inj hvb'
        obtain ⟨hDA, hDB⟩ := binder_congr m φ ihd hcl hty h hwa' hba'
          ⟨fun l hl => hLa' l (by simp [Expr.fvarLeaves, hl]),
            fun l hl => hLa' l (by simp [Expr.fvarLeaves, hl])⟩
          ⟨CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCa',
            CtxOk.of_subset (fun l hl => by
              simp [Expr.fvarLeaves, hl]) hCa'⟩
          hwb' hbb'
          ⟨fun l hl => hLb' l (by simp [Expr.fvarLeaves, hl]),
            fun l hl => hLb' l (by simp [Expr.fvarLeaves, hl])⟩
          ⟨CtxOk.of_subset (fun l hl => by simp [Expr.fvarLeaves, hl]) hCb',
            CtxOk.of_subset (fun l hl => by
              simp [Expr.fvarLeaves, hl]) hCb'⟩
          hA1 hB1 hA2 hB2
        obtain ⟨T, hT⟩ := hDA
        obtain ⟨T', hT'⟩ := hDB
        exact ⟨.sort 0, HasType.congrLam hT hT'⟩
  case h_13 _ _ f₁ a₁ f₂ a₂ =>
    by_cases hlen : (Expr.app f₁ a₁).getAppArgs.length
        = (Expr.app f₂ a₂).getAppArgs.length
    · rw [if_pos hlen] at h
      cases hfn : isDefEqCore mode env fuel d (Expr.app f₁ a₁).getAppFn
          (Expr.app f₂ a₂).getAppFn with
      | error err => rw [hfn] at h; exact nomatch h
      | ok v =>
      rw [hfn] at h
      cases v with
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
      | true =>
      simp only [if_true] at h
      cases hlist : defEqList (pureFns mode env fuel) env d
          (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs with
      | error err => rw [hlist] at h; exact nomatch h
      | ok v2 =>
      rw [hlist] at h
      cases v2 with
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
      | true =>
      have hea : Expr.app f₁ a₁ = Expr.mkAppN (Expr.app f₁ a₁).getAppFn
          (Expr.app f₁ a₁).getAppArgs := (Expr.mkAppN_getApp _).symm
      have heb : Expr.app f₂ a₂ = Expr.mkAppN (Expr.app f₂ a₂).getAppFn
          (Expr.app f₂ a₂).getAppArgs := (Expr.mkAppN_getApp _).symm
      rw [hea] at hva'
      rw [heb] at hvb'
      obtain ⟨vfa, vas, hvfa, hspa, rfl⟩ := denote_mkAppN_inv hva'
      obtain ⟨vfb, vbs, hvfb, hspb, rfl⟩ := denote_mkAppN_inv hvb'
      refine spine_congr m φ ihd hlist hwa' hba' hLa' hCa' hwb' hbb' hLb'
        hCb' hspa hspb (ihd hfn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hvfa hvfb)
      · exact hwa'.getAppFn
      · exact looseBVarsBounded_getAppFn hba'
      · exact fun l hl => hLa' l (fvarLeaves_getAppFn l hl)
      · exact hwb'.getAppFn
      · exact looseBVarsBounded_getAppFn hbb'
      · exact fun l hl => hLb' l (fvarLeaves_getAppFn l hl)
      · exact CtxOk.of_subset (fun l hl => fvarLeaves_getAppFn l hl) hCa'
      · exact CtxOk.of_subset (fun l hl => fvarLeaves_getAppFn l hl) hCb'
    · rw [if_neg hlen] at h
      exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_14 _ _ s₁ i₁ e₁ s₂ i₂ e₂ =>
    by_cases hii : (i₁ == i₂) = true
    · rw [if_pos hii] at h
      obtain rfl : i₁ = i₂ := eq_of_beq hii
      cases hde : isDefEqCore mode env fuel d e₁ e₂ with
      | error err => rw [hde] at h; exact nomatch h
      | ok v =>
        rw [hde] at h
        cases v with
        | false =>
          simp only [Bool.false_eq_true, if_false] at h
          exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
        | true =>
          rw [denote_proj] at hva' hvb'
          cases hv1 : denote m.cval env φ d e₁ with
          | none => rw [hv1] at hva'; exact nomatch hva'
          | some v1 =>
          cases hv2 : denote m.cval env φ d e₂ with
          | none => rw [hv2] at hvb'; exact nomatch hvb'
          | some v2 =>
          rw [hv1] at hva'
          rw [hv2] at hvb'
          dsimp only at hva' hvb'
          by_cases hlt : i₁ < 2
          · rw [if_pos hlt] at hva' hvb'
            obtain rfl : VExpr.proj i₁ v1 = va' := Option.some.inj hva'
            obtain rfl : VExpr.proj i₁ v2 = vb' := Option.some.inj hvb'
            refine Deq.proj i₁ (ihd hde ?_ hba' ?_ ?_ hbb' ?_ ?_ ?_ hv1 hv2)
            · simpa [Expr.WScoped] using hwa'
            · exact fun l hl => hLa' l (by simp [Expr.fvarLeaves, hl])
            · simpa [Expr.WScoped] using hwb'
            · exact fun l hl => hLb' l (by simp [Expr.fvarLeaves, hl])
            · exact CtxOk.of_subset (fun l hl => by
                simp [Expr.fvarLeaves, hl]) hCa'
            · exact CtxOk.of_subset (fun l hl => by
                simp [Expr.fvarLeaves, hl]) hCb'
          · rw [if_neg hlt] at hva'; exact nomatch hva'
    · rw [if_neg hii] at h
      exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_15 _ n₁ ty₁ body₁ mb₁ _ =>
    cases hce : etaCertP mode env fuel d n₁ ty₁ body₁ mb₁ b' with
    | error err => rw [etaCert_fold, hce] at h; exact nomatch h
    | ok v =>
      rw [etaCert_fold, hce] at h
      cases v with
      | true =>
        exact hec hce hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_16 _ _ n₂ ty₂ body₂ mb₂ _ =>
    cases hce : etaCertP mode env fuel d n₂ ty₂ body₂ mb₂ a' with
    | error err => rw [etaCert_fold, hce] at h; exact nomatch h
    | ok v =>
      rw [etaCert_fold, hce] at h
      cases v with
      | true =>
        exact (hec hce hwb' hbb' hLb' hwa' hba' hLa' hCb' hCa' hvb' hva').symm
      | false =>
        simp only [Bool.false_eq_true, if_false] at h
        exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'
  case h_17 => exact hsi h hwa' hba' hLa' hwb' hbb' hLb' hCa' hCb' hva' hvb'

/-- **`DefEqClaimsTT` at `fuel + 1`**, with the stuck configuration
discharged too: the remaining obligations are the four certificate
functions `stuckIrrel` calls, plus `etaCert`. -/
theorem defeq_claimsTT_stuck {env : Env} (m : EnvTT env) (φ : Name → Nat)
    {fuel : Nat} (hcl : ∀ n ψ, VExpr.Closed (m.cval n ψ))
    (ihwc : WhnfCoreClaimsTT mode m φ fuel) (ihw : WhnfClaimsTT mode m φ fuel)
    (ihd : DefEqClaimsTT mode m φ fuel) (ihi : InferClaimsTT mode m φ fuel)
    (hsi : StuckIrrelStepTT m φ fuel) (hec : EtaCertStepTT m φ fuel) :
    DefEqClaimsTT mode m φ (fuel + 1) :=
  defeq_claimsTT_closed m φ hcl ihwc ihw
    (proofIrrel_stepTT m φ ihw ihi)
    (defeqStuck_stepTT m φ ihd hcl hsi hec)
    (defeqSpine_stepTT m φ ihd)

end Setlec.TTVerify
