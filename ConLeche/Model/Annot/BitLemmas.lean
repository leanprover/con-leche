import ConLeche.Model.Annot.Bit

/-!
# The `denoteMeta` lemma battery (task #161, P3.2)

The Steps ladder consumes `denoteAnnot` through a fixed lemma surface —
clause equations, inversions, the depth shift, the environment
crossing — stated and proved at `DefEqRun.lean`'s prelude,
`Dispatch.lean`, and `Denote2Extend.lean`.  This file is that surface
for `denoteMeta`, mirror by mirror, with the systematic deltas of the
validated-annotation reading:

* **no fuel parameter** — the fuel-monotonicity/cross-fuel/`fuelDown`
  family has no mirror because there is nothing to be monotone in;
* **no sort-run conjuncts** — the binder inversions conclude
  `ea = .pi 0 (pwBit φ mb.pw) ta ba` (resp. `.lam (pwBit φ mb.pw)`)
  *definitionally*, where `denoteAnnot`'s conclude `sortOfE`/`lamSortE`
  successes;
* **premises that existed only to move a sort run are dropped** —
  `EnvWF` in the depth shift, `SortAgree` in the environment crossing.
  A premise kept by a mirror is one the *reading itself* needs
  (`hacl`: leaf lift-invariance; `FindPreserved`/`LitGuardsAgree`:
  the constant and literal clauses read the environment).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level PropWhen)

variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-! ## Clause equations -/

theorem denoteMeta_sort (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (u : Level) :
    denoteMeta acval env φ d (.sort u) = some (.sort (u.eval φ)) := by
  rw [denoteMeta]

theorem denoteMeta_fvar (acval : Name → (Name → Nat) → AnnotTerm)
    (d idx : Nat) (ty : Expr) :
    denoteMeta acval env φ d (.fvar idx ty)
      = some (.bvar (d - 1 - idx)) := by
  rw [denoteMeta]

theorem denoteMeta_const {acval : Name → (Name → Nat) → AnnotTerm}
    {d : Nat} {n : Name} {us : List Level} {ci : ConLeche.ConstantInfo}
    (hf : env.find? n = some ci)
    (hlen : us.length = ci.toConstantVal.levelParams.length) :
    denoteMeta acval env φ d (.const n us)
      = some (acval n
          (Level.substFn φ ci.toConstantVal.levelParams us)) := by
  rw [denoteMeta, hf]
  simp [hlen]

theorem denoteMeta_app (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (f a : Expr) :
    denoteMeta acval env φ d (.app f a)
      = (do
        let fa ← denoteMeta acval env φ d f
        let aa ← denoteMeta acval env φ d a
        some (.app fa aa)) := by
  rw [denoteMeta]

theorem denoteMeta_proj (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (s : Name) (i : Nat) (e : Expr) :
    denoteMeta acval env φ d (.proj s i e)
      = (do
        let ea ← denoteMeta acval env φ d e
        match env.findProj? s i with
        | some entry => some (projAV (i + entry.off) ea)
        | none => AnnotTerm.projPair? i ea) := by
  rw [denoteMeta]
  rfl

/-- The clause at an absent entry — the pre-W3 shape, for consumers
holding an absence fact. -/
theorem denoteMeta_proj_pair (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (s : Name) (i : Nat) (e : Expr)
    (hnt : env.findProj? s i = none) :
    denoteMeta acval env φ d (.proj s i e)
      = (do
        let ea ← denoteMeta acval env φ d e
        AnnotTerm.projPair? i ea) := by
  rw [denoteMeta_proj]
  cases he : denoteMeta acval env φ d e with
  | none => rfl
  | some ea =>
    show (match env.findProj? s i with
      | some entry => some (projAV (i + entry.off) ea)
      | none => AnnotTerm.projPair? i ea)
        = AnnotTerm.projPair? i ea
    rw [hnt]

theorem denoteMeta_forallE (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (ty body : Expr) (mb : ConLeche.BinderMeta) :
    denoteMeta acval env φ d (.forallE ty body mb)
      = (do
        let ta ← denoteMeta acval env φ d ty
        let ba ← denoteMeta acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty))
        some (.pi 0 (pwBit φ mb.pw) ta ba)) := by
  rw [denoteMeta]

theorem denoteMeta_lam (acval : Name → (Name → Nat) → AnnotTerm)
    (d : Nat) (ty body : Expr) (mb : ConLeche.BinderMeta) :
    denoteMeta acval env φ d (.lam ty body mb)
      = (do
        let ta ← denoteMeta acval env φ d ty
        let ba ← denoteMeta acval env φ (d + 1)
          (body.instantiate1 (.fvar d ty))
        some (.lam (pwBit φ mb.pw) ta ba)) := by
  rw [denoteMeta]

theorem denoteMeta_natLit {acval : Name → (Name → Nat) → AnnotTerm}
    {d n : Nat} (hg : natLitSupported env = true) :
    denoteMeta acval env φ d (.lit (.natVal n))
      = some (natLitAV (acval natZeroName (Level.substFn φ [] []))
          (acval natSuccName (Level.substFn φ [] [])) n) := by
  rw [denoteMeta, if_pos hg]

/-! ## Inversions -/

theorem denoteMeta_app_inv {d : Nat} {f a : Expr} {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.app f a) = some ea) :
    ∃ fa aa, denoteMeta acval env φ d f = some fa ∧
      denoteMeta acval env φ d a = some aa ∧ ea = .app fa aa := by
  rw [denoteMeta] at h
  cases hf : denoteMeta acval env φ d f with
  | none => rw [hf] at h; exact nomatch h
  | some fa =>
    cases ha : denoteMeta acval env φ d a with
    | none => rw [hf, ha] at h; exact nomatch h
    | some aa =>
      rw [hf, ha] at h
      exact ⟨fa, aa, rfl, rfl, (Option.some.inj h).symm⟩

theorem denoteMeta_proj_inv {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.proj s i e) = some ea) :
    ∃ ia, denoteMeta acval env φ d e = some ia ∧
      ((∃ entry, env.findProj? s i = some entry ∧ ea = projAV (i + entry.off) ia) ∨
       (env.findProj? s i = none ∧ AnnotTerm.projPair? i ia = some ea)) := by
  rw [denoteMeta] at h
  cases he : denoteMeta acval env φ d e with
  | none => rw [he] at h; exact nomatch h
  | some ia =>
    rw [he] at h
    replace h : (match env.findProj? s i with
        | some entry => some (projAV (i + entry.off) ia)
        | none => AnnotTerm.projPair? i ia)
          = some ea := h
    cases hfp : env.findProj? s i with
    | some entry =>
      rw [hfp] at h
      dsimp only at h
      exact ⟨ia, rfl, Or.inl ⟨entry, rfl, (Option.some.inj h).symm⟩⟩
    | none =>
      rw [hfp] at h
      dsimp only at h
      exact ⟨ia, rfl, Or.inr ⟨rfl, h⟩⟩

/-- The inversion at an absent entry — the pre-W3 shape, for consumers
holding an absence fact. -/
theorem denoteMeta_proj_inv_pair {d : Nat} {s : Name} {i : Nat} {e : Expr}
    {ea : AnnotTerm}
    (hnt : env.findProj? s i = none)
    (h : denoteMeta acval env φ d (.proj s i e) = some ea) :
    ∃ ia, denoteMeta acval env φ d e = some ia ∧
      AnnotTerm.projPair? i ia = some ea := by
  obtain ⟨ia, hia, hcase⟩ := denoteMeta_proj_inv h
  rcases hcase with ⟨entry, hfp, -⟩ | ⟨-, hdec⟩
  · rw [hnt] at hfp; exact nomatch hfp
  · exact ⟨ia, hia, hdec⟩

theorem denoteMeta_forallE_inv {d : Nat} {ty bd : Expr}
    {mb : ConLeche.BinderMeta} {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.forallE ty bd mb) = some ea) :
    ∃ ta ba, denoteMeta acval env φ d ty = some ta ∧
      denoteMeta acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) = some ba ∧
      ea = .pi 0 (pwBit φ mb.pw) ta ba := by
  rw [denoteMeta] at h
  cases ht : denoteMeta acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denoteMeta acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hb] at h
      exact ⟨ta, ba, rfl, rfl, (Option.some.inj h).symm⟩

theorem denoteMeta_lam_inv {d : Nat} {ty bd : Expr}
    {mb : ConLeche.BinderMeta} {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.lam ty bd mb) = some ea) :
    ∃ ta ba, denoteMeta acval env φ d ty = some ta ∧
      denoteMeta acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) = some ba ∧
      ea = .lam (pwBit φ mb.pw) ta ba := by
  rw [denoteMeta] at h
  cases ht : denoteMeta acval env φ d ty with
  | none => rw [ht] at h; exact nomatch h
  | some ta =>
    cases hb : denoteMeta acval env φ (d + 1)
        (bd.instantiate1 (.fvar d ty)) with
    | none => rw [ht, hb] at h; exact nomatch h
    | some ba =>
      rw [ht, hb] at h
      exact ⟨ta, ba, rfl, rfl, (Option.some.inj h).symm⟩

theorem denoteMeta_natLit_inv {d n : Nat} {ea : AnnotTerm}
    (h : denoteMeta acval env φ d (.lit (.natVal n)) = some ea) :
    natLitSupported env = true ∧
      ea = natLitAV (acval natZeroName (Level.substFn φ [] []))
        (acval natSuccName (Level.substFn φ [] [])) n := by
  rw [denoteMeta] at h
  split at h
  · next hg => exact ⟨hg, (Option.some.inj h).symm⟩
  · exact nomatch h

end ConLeche.Model
