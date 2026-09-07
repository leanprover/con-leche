import ConLeche.SetP.Annot.Bit

/-!
# The `denoteP` lemma battery (task #161, P3.2)

The Step2 ladder consumes `denote2` through a fixed lemma surface —
clause equations, inversions, the depth shift, the environment
crossing — stated and proved at `DefEqRun.lean`'s prelude,
`Dispatch.lean`, and `Denote2Extend.lean`.  This file is that surface
for `denoteP`, mirror by mirror, with the systematic deltas of the
validated-annotation reading:

* **no fuel parameter** — the fuel-monotonicity/cross-fuel/`fuelDown`
  family has no mirror because there is nothing to be monotone in;
* **no sort-run conjuncts** — the binder inversions conclude
  `ea = .pi 0 (pwBit φ mb.pw) ta ba` (resp. `.lam (pwBit φ mb.pw)`)
  *definitionally*, where `denote2`'s conclude `sortOfE`/`lamSortE`
  successes;
* **premises that existed only to move a sort run are dropped** —
  `EnvWF` in the depth shift, `SortAgree` in the environment crossing.
  A premise kept by a mirror is one the *reading itself* needs
  (`hacl`: leaf lift-invariance; `FindPreserved`/`LitGuardsAgree`:
  the constant and literal clauses read the environment).
-/

namespace ConLeche.SetP
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.VExpr ConLeche.Verify
open ConLeche.Semantics (AVExpr)
open ConLeche (CheckMode Env Expr Name Level PropWhen)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AVExpr}

/-! ## Clause equations -/

theorem denoteP_sort (acval : Name → (Name → Nat) → AVExpr)
    (d : Nat) (u : Level) :
    denoteP acval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denoteP]

theorem denoteP_fvar (acval : Name → (Name → Nat) → AVExpr)
    (d idx : Nat) (ty : Expr) :
    denoteP acval env φ d (.fvar idx ty)
      = some (.bvar (d - 1 - idx)) := by
  rw [denoteP]

theorem denoteP_const {acval : Name → (Name → Nat) → AVExpr}
    {d : Nat} {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    denoteP acval env φ d (.const n us)
      = some (acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) := by
  rw [denoteP, hf]
  simp [hlen]

theorem denoteP_app (acval : Name → (Name → Nat) → AVExpr)
    (d : Nat) (f a : Expr) :
    denoteP acval env φ d (.app f a)
      = (do
        let fa ← denoteP acval env φ d f
        let aa ← denoteP acval env φ d a
        some (.app fa aa)) := by
  rw [denoteP]

theorem denoteP_proj (acval : Name → (Name → Nat) → AVExpr)
    (d : Nat) (s : Name) (i : Nat) (e : Expr) :
    denoteP acval env φ d (.proj s i e)
      = (do
        let ea ← denoteP acval env φ d e
        match env.findProj? s i with
        | some _ => some (projAV i ea)
        | none => if i < 2 then some (.proj i ea) else none) := by
  rw [denoteP]
  rfl

/-- The clause at an absent entry — the pre-W3 shape, for consumers
holding an absence fact. -/
theorem denoteP_proj_pair (acval : Name → (Name → Nat) → AVExpr)
    (d : Nat) (s : Name) (i : Nat) (e : Expr)
    (hnt : env.findProj? s i = none) :
    denoteP acval env φ d (.proj s i e)
      = (do
        let ea ← denoteP acval env φ d e
        if i < 2 then some (.proj i ea) else none) := by
  rw [denoteP_proj]
  cases he : denoteP acval env φ d e with
  | none => rfl
  | some ea =>
    show (match env.findProj? s i with
      | some _ => some (projAV i ea)
      | none => if i < 2 then some (AVExpr.proj i ea) else none)
        = if i < 2 then some (AVExpr.proj i ea) else none
    rw [hnt]

theorem denoteP_forallE (acval : Name → (Name → Nat) → AVExpr)
    (d : Nat) (ty body : Expr) (mb : ConLeche.BinderMeta) :
    denoteP acval env φ d (.forallE ty body mb)
      = (do
        let ta ← denoteP acval env φ d ty
        let ba ← denoteP acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty))
        some (.pi 0 (pwBit φ mb.pw) ta ba)) := by
  rw [denoteP]

theorem denoteP_lam (acval : Name → (Name → Nat) → AVExpr)
    (d : Nat) (ty body : Expr) (mb : ConLeche.BinderMeta) :
    denoteP acval env φ d (.lam ty body mb)
      = (do
        let ta ← denoteP acval env φ d ty
        let ba ← denoteP acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty))
        some (.lam (pwBit φ mb.pw) ta ba)) := by
  rw [denoteP]

theorem denoteP_natLit {acval : Name → (Name → Nat) → AVExpr}
    {d n : Nat} (hg : natLitSupported env = true) :
    denoteP acval env φ d (.lit (.natVal n))
      = some (natLitT2 (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] [])) n) := by
  rw [denoteP, if_pos hg]

/-! ## Inversions -/

theorem denoteP_app_inv {d : Nat} {f a : Expr} {ea : AVExpr}
    (h : denoteP acval env φ d (.app f a) = some ea) :
    ∃ fa aa, denoteP acval env φ d f = some fa ∧
      denoteP acval env φ d a = some aa ∧ ea = .app fa aa := by
  rw [denoteP] at h
  cases hf : denoteP acval env φ d f with
  | none => rw [hf] at h; exact nomatch h
  | some fa =>
    cases ha : denoteP acval env φ d a with
    | none => rw [hf, ha] at h; exact nomatch h
    | some aa =>
      rw [hf, ha] at h
      exact ⟨fa, aa, rfl, rfl, (Option.some.inj h).symm⟩

theorem denoteP_proj_inv {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {ea : AVExpr}
    (h : denoteP acval env φ d (.proj s i e) = some ea) :
    ∃ ia, denoteP acval env φ d e = some ia ∧
      ((∃ entry, env.findProj? s i = some entry ∧ ea = projAV i ia) ∨
       (env.findProj? s i = none ∧ i < 2 ∧ ea = .proj i ia)) := by
  rw [denoteP] at h
  cases he : denoteP acval env φ d e with
  | none => rw [he] at h; exact nomatch h
  | some ia =>
    rw [he] at h
    replace h : (match env.findProj? s i with
        | some _ => some (projAV i ia)
        | none => if i < 2 then some (AVExpr.proj i ia) else none)
          = some ea := h
    cases hfp : env.findProj? s i with
    | some entry =>
      rw [hfp] at h
      dsimp only at h
      exact ⟨ia, rfl, Or.inl ⟨entry, rfl, (Option.some.inj h).symm⟩⟩
    | none =>
      rw [hfp] at h
      dsimp only at h
      split at h
      · next hlt =>
        exact ⟨ia, rfl, Or.inr ⟨rfl, hlt, (Option.some.inj h).symm⟩⟩
      · exact nomatch h

/-- The inversion at an absent entry — the pre-W3 shape, for consumers
holding an absence fact. -/
theorem denoteP_proj_inv_pair {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {ea : AVExpr}
    (hnt : env.findProj? s i = none)
    (h : denoteP acval env φ d (.proj s i e) = some ea) :
    ∃ ia, denoteP acval env φ d e = some ia ∧ i < 2 ∧
      ea = .proj i ia := by
  obtain ⟨ia, hia, hcase⟩ := denoteP_proj_inv h
  rcases hcase with ⟨entry, hfp, -⟩ | ⟨-, hlt, rfl⟩
  · rw [hnt] at hfp; exact nomatch hfp
  · exact ⟨ia, hia, hlt, rfl⟩

theorem denoteP_forallE_inv {d : Nat} {ty bd : Expr}
    {mb : ConLeche.BinderMeta} {ea : AVExpr}
    (h : denoteP acval env φ d (.forallE ty bd mb) = some ea) :
    ∃ ta ba, denoteP acval env φ d ty = some ta ∧
      denoteP acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) = some ba ∧
      ea = .pi 0 (pwBit φ mb.pw) ta ba := by
  rw [denoteP] at h
  cases ht : denoteP acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denoteP acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hb] at h
      exact ⟨ta, ba, rfl, rfl, (Option.some.inj h).symm⟩

theorem denoteP_lam_inv {d : Nat} {ty bd : Expr}
    {mb : ConLeche.BinderMeta} {ea : AVExpr}
    (h : denoteP acval env φ d (.lam ty bd mb) = some ea) :
    ∃ ta ba, denoteP acval env φ d ty = some ta ∧
      denoteP acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) = some ba ∧
      ea = .lam (pwBit φ mb.pw) ta ba := by
  rw [denoteP] at h
  cases ht : denoteP acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denoteP acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hb] at h
      exact ⟨ta, ba, rfl, rfl, (Option.some.inj h).symm⟩

theorem denoteP_natLit_inv {d n : Nat} {ea : AVExpr}
    (h : denoteP acval env φ d (.lit (.natVal n)) = some ea) :
    natLitSupported env = true ∧
      ea = natLitT2 (acval natZeroName (Level.substFn φ [] []))
        (acval natSuccName (Level.substFn φ [] [])) n := by
  rw [denoteP] at h
  split at h
  · next hg => exact ⟨hg, (Option.some.inj h).symm⟩
  · exact nomatch h

end ConLeche.SetP
