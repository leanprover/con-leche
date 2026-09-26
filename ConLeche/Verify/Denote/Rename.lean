module

public import ConLeche.Verify.InstLevels
public import ConLeche.Verify.Denote.Shift
public import ConLeche.Verify.Subst

public section

/-!
# Constant renaming and level instantiation, on the denotation side

`denote_renameConsts` — the transpose of `interp_renameConsts` — plus
the prefix relation the telescope folds state their domain agreement
with.

**Why the bridge needs it and `DeclBasisTT` did not.**  A pinned basis
constant has no `_model` counterpart, so nothing has to be renamed.  A
modeled block's install does: the capability pins describe the
`T._model` artifact, while the laws (`EtaLawTT`, `UnitLawTT`) are
stated at the **public** former, and `checkMemberVal`'s comparison
relates the two only *through* `renameConsts`.

`RenEqT`/`PiDomsRenEqT` are `V`-free, which is why they live here and
not in the model tier: **do not** import `ConLeche/Model/*` from this
hierarchy — the model tier (`ConLeche/Model/IndRename.lean` and the
frame files around it) imports them from here instead.
-/

namespace ConLeche.Verify

open ConLeche.Term

variable {cval : TConstVal} {env : Env} {φ : Name → Nat}

/-! ## Renaming constants -/

  -- (task #175 wiring W3 added a fourth, tower-freeness conjunct here
  -- because the branched `.proj` reading consulted the table at both
  -- the source and the image name; W5 fixed the struct name under
  -- `renameConsts` instead, and the conjunct is gone.)

/-! ## The domain-agreement prefix relation

Only the *first `k`* domains are constrained, and the residuals are
left free: at a fold's use site the two telescopes agree on the
parameter prefix and then diverge — the type former ends in a sort, the
checked theorem in an equation. -/

/-- Related by constant renaming, modulo the positions the denotation
never reads. -/
@[expose] def RenEqT (f : Name → Name) (e₁ e₂ : Expr) : Prop :=
  Expr.ErasedEq (e₁.renameConsts f) e₂

/-- Renamed-equality survives instantiating both sides with related
arguments. -/
theorem RenEqT.instantiate1 {f : Name → Name} {e₁ e₂ a₁ a₂ : Expr} {k : Nat}
    (he : RenEqT f e₁ e₂) (ha : RenEqT f a₁ a₂) :
    RenEqT f (e₁.instantiate1 a₁ k) (e₂.instantiate1 a₂ k) := by
  unfold RenEqT
  rw [Expr.renameConsts_instantiate1_gen]
  exact Expr.ErasedEq.instantiate1 he ha

/-- **Two telescopes' opening variables are renamed-equal**, whatever
their binders were called and whatever they were annotated with:
`renameConsts` reaches only the annotation, and erasure compares only
the index.  This is what lets one alignment step open *both* sides. -/
theorem RenEqT.fvar {f : Name → Name} {i : Nat}
    {ty ty' : Expr} : RenEqT f (.fvar i ty) (.fvar i ty') := by
  show Expr.ErasedEq (.fvar i (ty.renameConsts f)) (.fvar i ty')
  rfl

/-- The first `k` domains of two `∀`-telescopes are related by the
renaming; their residuals are unconstrained. -/
def PiDomsRenEqT (f : Name → Name) : Nat → Expr → Expr → Prop
  | 0, _, _ => True
  | k + 1, .forallE d₁ b₁ _, e₂ =>
    ∃ d₂ b₂ m₂, e₂ = .forallE d₂ b₂ m₂ ∧ RenEqT f d₁ d₂ ∧
      PiDomsRenEqT f k b₁ b₂
  | _ + 1, _, _ => False

/-- Pointwise domain relatedness assembles the prefix relation. -/
theorem PiDomsRenEqT.of_pointwise {f : Name → Name} :
    ∀ (k : Nat) {e₁ e₂ : Expr}
      {bs₁ bs₂ : List (Expr × BinderMeta)} {body₁ body₂ : Expr},
      e₁.stripPis k = some (bs₁, body₁) →
      e₂.stripPis k = some (bs₂, body₂) →
      (∀ (i : Nat) (b₁ b₂ : Expr × BinderMeta),
        bs₁[i]? = some b₁ → bs₂[i]? = some b₂ → RenEqT f b₁.1 b₂.1) →
      PiDomsRenEqT f k e₁ e₂ := by
  intro k
  induction k with
  | zero => intro e₁ e₂ bs₁ bs₂ body₁ body₂ _ _ _; trivial
  | succ k ih =>
    intro e₁ e₂ bs₁ bs₂ body₁ body₂ h1 h2 hdoms
    match e₁, e₂, h1, h2 with
    | .forallE d₁ b₁ m₁, .forallE d₂ b₂ m₂, h1, h2 =>
      simp only [Expr.stripPis] at h1 h2
      cases hs1 : b₁.stripPis k with
      | none => rw [hs1] at h1; exact nomatch h1
      | some p1 =>
      cases hs2 : b₂.stripPis k with
      | none => rw [hs2] at h2; exact nomatch h2
      | some p2 =>
      rw [hs1] at h1
      rw [hs2] at h2
      simp only [Option.map_some, Option.some.injEq] at h1 h2
      obtain ⟨hb1, -⟩ : (d₁, m₁) :: p1.1 = bs₁ ∧ p1.2 = body₁ := by
        cases h1; exact ⟨rfl, rfl⟩
      obtain ⟨hb2, -⟩ : (d₂, m₂) :: p2.1 = bs₂ ∧ p2.2 = body₂ := by
        cases h2; exact ⟨rfl, rfl⟩
      subst hb1 hb2
      refine ⟨d₂, b₂, m₂, rfl, ?_, ?_⟩
      · exact hdoms 0 (d₁, m₁) (d₂, m₂) rfl rfl
      · exact ih hs1 hs2 (fun i c₁ c₂ hc₁ hc₂ =>
          hdoms (i + 1) c₁ c₂ (by simpa using hc₁) (by simpa using hc₂))

end ConLeche.Verify
