import Setlec.Cached.ExprC
import Setlec.Kernel.ArenaWF

/-!
# The cached-representation seam floor (task #163)

The erasure `eraseC : ExprC → Expr`, the field invariant `WFc`, and
the facts that replace the arena's `EStore.WF` + `denote_inj` for the
cached checker variant (see DESIGN.md, "Task #163 CACHED-LIVE P1"):

* `WFc e := ofExpr (eraseC e) = e` — every field of every node equals
  the smart constructor's recurrence on the erased term;
* `eraseC` is **injective on `WFc`** (`eraseC_inj`): the fields are
  functions of the structure, so a well-formed `ExprC` is uniquely
  determined by its erasure — `denote_inj` without a table;
* field exactness: on `WFc` nodes the `O(1)` readers `bvarB`/`fvarB`/
  `hasLP` read exactly the spec functions `Expr.bvarBound`/
  `Expr.fvarRange`/`Expr.hasLevelParam` of the erasure, so every
  cutoff the cached operations take is the cutoff the spec takes.

Everything here consumes only the *pure* definitions (`ofExpr` =
`ofExprSpec`, `beq` = `beqSpec`); the two `unsafe` accelerations in
`Setlec/Cached/ExprC.lean` are named trust points the proofs never
touch.
-/

namespace Setlec.Cached

open Setlec

namespace ExprC

/-! ## The erasure -/

/-- Erase the four computed fields, yielding the plain expression the
node represents.  Non-injective on raw `ExprC` (garbage fields erase
away); injective on `WFc` (`eraseC_inj`). -/
def eraseC : ExprC → Expr
  | .bvar i .. => .bvar i
  | .fvar idx n ty .. => .fvar idx n (eraseC ty)
  | .sort u .. => .sort u
  | .const n us .. => .const n us
  | .app f a .. => .app (eraseC f) (eraseC a)
  | .lam n ty b m .. => .lam n (eraseC ty) (eraseC b) m
  | .forallE n ty b m .. => .forallE n (eraseC ty) (eraseC b) m
  | .letE n ty v b .. => .letE n (eraseC ty) (eraseC v) (eraseC b)
  | .lit l .. => .lit l
  | .proj s i e .. => .proj s i (eraseC e)

/-! The smart constructors erase to the plain constructors (the
"erasure half" of field exactness: all `rfl`). -/

@[simp] theorem eraseC_mkBVar (i : Nat) : eraseC (mkBVar i) = .bvar i := rfl

@[simp] theorem eraseC_mkFVar (idx : Nat) (n : Name) (ty : ExprC) :
    eraseC (mkFVar idx n ty) = .fvar idx n (eraseC ty) := rfl

@[simp] theorem eraseC_mkSort (u : Level) : eraseC (mkSort u) = .sort u := rfl

@[simp] theorem eraseC_mkConst (n : Name) (us : List Level) :
    eraseC (mkConst n us) = .const n us := rfl

@[simp] theorem eraseC_mkApp (f a : ExprC) :
    eraseC (mkApp f a) = .app (eraseC f) (eraseC a) := rfl

@[simp] theorem eraseC_mkLam (n : Name) (ty b : ExprC) (m : BinderMeta) :
    eraseC (mkLam n ty b m) = .lam n (eraseC ty) (eraseC b) m := rfl

@[simp] theorem eraseC_mkForallE (n : Name) (ty b : ExprC) (m : BinderMeta) :
    eraseC (mkForallE n ty b m) = .forallE n (eraseC ty) (eraseC b) m := rfl

@[simp] theorem eraseC_mkLetE (n : Name) (ty v b : ExprC) :
    eraseC (mkLetE n ty v b) = .letE n (eraseC ty) (eraseC v) (eraseC b) := rfl

@[simp] theorem eraseC_mkLit (l : Literal) : eraseC (mkLit l) = .lit l := rfl

@[simp] theorem eraseC_mkProj (s : Name) (i : Nat) (e : ExprC) :
    eraseC (mkProj s i e) = .proj s i (eraseC e) := rfl

/-- `ofExpr` (the pure conversion) is a section of the erasure. -/
@[simp] theorem eraseC_ofExpr : ∀ x : Expr, eraseC (ofExpr x) = x := by
  intro x
  induction x with
  | bvar i => rfl
  | fvar idx n ty ih =>
    show eraseC (mkFVar idx n (ofExprSpec ty)) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl, ih]
  | sort u => rfl
  | const n us => rfl
  | app f a ihf iha =>
    show eraseC (mkApp (ofExprSpec f) (ofExprSpec a)) = _
    simp [show ofExprSpec f = ofExpr f from rfl,
      show ofExprSpec a = ofExpr a from rfl, ihf, iha]
  | lam n ty b m iht ihb =>
    show eraseC (mkLam n (ofExprSpec ty) (ofExprSpec b) m) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl,
      show ofExprSpec b = ofExpr b from rfl, iht, ihb]
  | forallE n ty b m iht ihb =>
    show eraseC (mkForallE n (ofExprSpec ty) (ofExprSpec b) m) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl,
      show ofExprSpec b = ofExpr b from rfl, iht, ihb]
  | letE n ty v b iht ihv ihb =>
    show eraseC (mkLetE n (ofExprSpec ty) (ofExprSpec v) (ofExprSpec b)) = _
    simp [show ofExprSpec ty = ofExpr ty from rfl,
      show ofExprSpec v = ofExpr v from rfl,
      show ofExprSpec b = ofExpr b from rfl, iht, ihv, ihb]
  | lit l => rfl
  | proj s i e ih =>
    show eraseC (mkProj s i (ofExprSpec e)) = _
    simp [show ofExprSpec e = ofExpr e from rfl, ih]

/-! ## The field invariant -/

/-- The field invariant: the term is exactly what the pure conversion
builds from its own erasure, i.e. every field of every node satisfies
the smart-constructor recurrence.  Everything the checker constructs
is `WFc`: raw constructor applications appear nowhere outside the
smart constructors. -/
def WFc (e : ExprC) : Prop := ofExpr (eraseC e) = e

/-- The conversion of any expression is well-formed. -/
theorem WFc_ofExpr (x : Expr) : WFc (ofExpr x) := by
  show ofExpr (eraseC (ofExpr x)) = ofExpr x
  rw [eraseC_ofExpr]

/-- **Injectivity on the invariant** — the arena's `denote_inj`
without a table: a well-formed node is determined by its erasure. -/
theorem eraseC_inj {a b : ExprC} (ha : WFc a) (hb : WFc b)
    (h : eraseC a = eraseC b) : a = b := by
  rw [← ha, ← hb, h]

/-! ### Closure under the smart constructors -/

protected theorem WFc.mkBVar (i : Nat) : WFc (mkBVar i) := rfl

protected theorem WFc.mkFVar {ty : ExprC} (idx : Nat) (n : Name)
    (hty : WFc ty) : WFc (mkFVar idx n ty) := by
  show ofExpr (eraseC (mkFVar idx n ty)) = _
  rw [eraseC_mkFVar]
  show mkFVar idx n (ofExprSpec (eraseC ty)) = mkFVar idx n ty
  rw [show ofExprSpec (eraseC ty) = ofExpr (eraseC ty) from rfl, hty]

protected theorem WFc.mkSort (u : Level) : WFc (mkSort u) := rfl

protected theorem WFc.mkConst (n : Name) (us : List Level) :
    WFc (mkConst n us) := rfl

protected theorem WFc.mkApp {f a : ExprC} (hf : WFc f) (ha : WFc a) :
    WFc (mkApp f a) := by
  show ofExpr (eraseC (mkApp f a)) = _
  rw [eraseC_mkApp]
  show mkApp (ofExprSpec (eraseC f)) (ofExprSpec (eraseC a)) = mkApp f a
  rw [show ofExprSpec (eraseC f) = ofExpr (eraseC f) from rfl,
    show ofExprSpec (eraseC a) = ofExpr (eraseC a) from rfl, hf, ha]

protected theorem WFc.mkLam {ty b : ExprC} (n : Name) (m : BinderMeta)
    (hty : WFc ty) (hb : WFc b) : WFc (mkLam n ty b m) := by
  show ofExpr (eraseC (mkLam n ty b m)) = _
  rw [eraseC_mkLam]
  show mkLam n (ofExprSpec (eraseC ty)) (ofExprSpec (eraseC b)) m =
    mkLam n ty b m
  rw [show ofExprSpec (eraseC ty) = ofExpr (eraseC ty) from rfl,
    show ofExprSpec (eraseC b) = ofExpr (eraseC b) from rfl, hty, hb]

protected theorem WFc.mkForallE {ty b : ExprC} (n : Name) (m : BinderMeta)
    (hty : WFc ty) (hb : WFc b) : WFc (mkForallE n ty b m) := by
  show ofExpr (eraseC (mkForallE n ty b m)) = _
  rw [eraseC_mkForallE]
  show mkForallE n (ofExprSpec (eraseC ty)) (ofExprSpec (eraseC b)) m =
    mkForallE n ty b m
  rw [show ofExprSpec (eraseC ty) = ofExpr (eraseC ty) from rfl,
    show ofExprSpec (eraseC b) = ofExpr (eraseC b) from rfl, hty, hb]

protected theorem WFc.mkLetE {ty v b : ExprC} (n : Name)
    (hty : WFc ty) (hv : WFc v) (hb : WFc b) : WFc (mkLetE n ty v b) := by
  show ofExpr (eraseC (mkLetE n ty v b)) = _
  rw [eraseC_mkLetE]
  show mkLetE n (ofExprSpec (eraseC ty)) (ofExprSpec (eraseC v))
    (ofExprSpec (eraseC b)) = mkLetE n ty v b
  rw [show ofExprSpec (eraseC ty) = ofExpr (eraseC ty) from rfl,
    show ofExprSpec (eraseC v) = ofExpr (eraseC v) from rfl,
    show ofExprSpec (eraseC b) = ofExpr (eraseC b) from rfl, hty, hv, hb]

protected theorem WFc.mkLit (l : Literal) : WFc (mkLit l) := rfl

protected theorem WFc.mkProj {e : ExprC} (s : Name) (i : Nat)
    (he : WFc e) : WFc (mkProj s i e) := by
  show ofExpr (eraseC (mkProj s i e)) = _
  rw [eraseC_mkProj]
  show mkProj s i (ofExprSpec (eraseC e)) = mkProj s i e
  rw [show ofExprSpec (eraseC e) = ofExpr (eraseC e) from rfl, he]

/-! ### Inversion: a well-formed node has well-formed children and
recurrence fields

Each inversion re-reads `WFc`'s equation at one constructor: the left
side is the smart constructor on converted children, so constructor
injectivity pins the children converted (their own `WFc`) and every
field to its recurrence. -/

theorem WFc.fvar_inv {idx : Nat} {n : Name} {ty : ExprC}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.fvar idx n ty h bb fb lp)) :
    WFc ty ∧ ExprC.fvar idx n ty h bb fb lp = mkFVar idx n ty := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.fvar idx n ty h bb fb lp) = .fvar idx n (eraseC ty)
      from rfl] at this
  rw [show ofExpr (.fvar idx n (eraseC ty)) =
      mkFVar idx n (ofExpr (eraseC ty)) from rfl] at this
  have hty : WFc ty := by
    show ofExpr (eraseC ty) = ty
    have := congrArg (fun e => match e with
      | ExprC.fvar _ _ t _ _ _ _ => t | _ => ty) this
    simpa [mkFVar] using this
  refine ⟨hty, ?_⟩
  rw [← this, hty]

theorem WFc.app_inv {f a : ExprC} {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.app f a h bb fb lp)) :
    WFc f ∧ WFc a ∧ ExprC.app f a h bb fb lp = mkApp f a := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.app f a h bb fb lp) = .app (eraseC f) (eraseC a)
      from rfl] at this
  rw [show ofExpr (.app (eraseC f) (eraseC a)) =
      mkApp (ofExpr (eraseC f)) (ofExpr (eraseC a)) from rfl] at this
  have hf : WFc f := by
    show ofExpr (eraseC f) = f
    have := congrArg (fun e => match e with
      | ExprC.app g _ _ _ _ _ => g | _ => f) this
    simpa [mkApp] using this
  have ha : WFc a := by
    show ofExpr (eraseC a) = a
    have := congrArg (fun e => match e with
      | ExprC.app _ b _ _ _ _ => b | _ => a) this
    simpa [mkApp] using this
  refine ⟨hf, ha, ?_⟩
  rw [← this, hf, ha]

theorem WFc.lam_inv {n : Name} {ty b : ExprC} {m : BinderMeta}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.lam n ty b m h bb fb lp)) :
    WFc ty ∧ WFc b ∧ ExprC.lam n ty b m h bb fb lp = mkLam n ty b m := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.lam n ty b m h bb fb lp) =
      .lam n (eraseC ty) (eraseC b) m from rfl] at this
  rw [show ofExpr (.lam n (eraseC ty) (eraseC b) m) =
      mkLam n (ofExpr (eraseC ty)) (ofExpr (eraseC b)) m from rfl] at this
  have hty : WFc ty := by
    show ofExpr (eraseC ty) = ty
    have := congrArg (fun e => match e with
      | ExprC.lam _ t _ _ _ _ _ _ => t | _ => ty) this
    simpa [mkLam] using this
  have hb : WFc b := by
    show ofExpr (eraseC b) = b
    have := congrArg (fun e => match e with
      | ExprC.lam _ _ bd _ _ _ _ _ => bd | _ => b) this
    simpa [mkLam] using this
  refine ⟨hty, hb, ?_⟩
  rw [← this, hty, hb]

theorem WFc.forallE_inv {n : Name} {ty b : ExprC} {m : BinderMeta}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.forallE n ty b m h bb fb lp)) :
    WFc ty ∧ WFc b ∧
      ExprC.forallE n ty b m h bb fb lp = mkForallE n ty b m := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.forallE n ty b m h bb fb lp) =
      .forallE n (eraseC ty) (eraseC b) m from rfl] at this
  rw [show ofExpr (.forallE n (eraseC ty) (eraseC b) m) =
      mkForallE n (ofExpr (eraseC ty)) (ofExpr (eraseC b)) m from rfl]
    at this
  have hty : WFc ty := by
    show ofExpr (eraseC ty) = ty
    have := congrArg (fun e => match e with
      | ExprC.forallE _ t _ _ _ _ _ _ => t | _ => ty) this
    simpa [mkForallE] using this
  have hb : WFc b := by
    show ofExpr (eraseC b) = b
    have := congrArg (fun e => match e with
      | ExprC.forallE _ _ bd _ _ _ _ _ => bd | _ => b) this
    simpa [mkForallE] using this
  refine ⟨hty, hb, ?_⟩
  rw [← this, hty, hb]

theorem WFc.letE_inv {n : Name} {ty v b : ExprC}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.letE n ty v b h bb fb lp)) :
    WFc ty ∧ WFc v ∧ WFc b ∧
      ExprC.letE n ty v b h bb fb lp = mkLetE n ty v b := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.letE n ty v b h bb fb lp) =
      .letE n (eraseC ty) (eraseC v) (eraseC b) from rfl] at this
  rw [show ofExpr (.letE n (eraseC ty) (eraseC v) (eraseC b)) =
      mkLetE n (ofExpr (eraseC ty)) (ofExpr (eraseC v))
        (ofExpr (eraseC b)) from rfl] at this
  have hty : WFc ty := by
    show ofExpr (eraseC ty) = ty
    have := congrArg (fun e => match e with
      | ExprC.letE _ t _ _ _ _ _ _ => t | _ => ty) this
    simpa [mkLetE] using this
  have hv : WFc v := by
    show ofExpr (eraseC v) = v
    have := congrArg (fun e => match e with
      | ExprC.letE _ _ vv _ _ _ _ _ => vv | _ => v) this
    simpa [mkLetE] using this
  have hb : WFc b := by
    show ofExpr (eraseC b) = b
    have := congrArg (fun e => match e with
      | ExprC.letE _ _ _ bd _ _ _ _ => bd | _ => b) this
    simpa [mkLetE] using this
  refine ⟨hty, hv, hb, ?_⟩
  rw [← this, hty, hv, hb]

theorem WFc.proj_inv {s : Name} {i : Nat} {e : ExprC}
    {h : UInt64} {bb fb : Nat} {lp : Bool}
    (hw : WFc (.proj s i e h bb fb lp)) :
    WFc e ∧ ExprC.proj s i e h bb fb lp = mkProj s i e := by
  have := hw
  unfold WFc at this
  rw [show eraseC (.proj s i e h bb fb lp) = .proj s i (eraseC e)
      from rfl] at this
  rw [show ofExpr (.proj s i (eraseC e)) =
      mkProj s i (ofExpr (eraseC e)) from rfl] at this
  have he : WFc e := by
    show ofExpr (eraseC e) = e
    have := congrArg (fun x => match x with
      | ExprC.proj _ _ sub _ _ _ _ => sub | _ => e) this
    simpa [mkProj] using this
  refine ⟨he, ?_⟩
  rw [← this, he]

/-! ## Field exactness (the reader form)

On `WFc` nodes the `O(1)` readers are exactly the spec functions of
the erasure — the same exactness the arena's `TWF.bvarBoundD_exact2` /
`fvarRangeD_exact2` / `ehasParamD_exact2` provide for the parallel
arrays, so the cutoff-consequence lemmas transpose verbatim. -/

/-- `bvarB` reads `Expr.bvarBound` of the erasure. -/
theorem bvarB_exact : ∀ {e : ExprC}, WFc e →
    e.bvarB = (eraseC e).bvarBound := by
  intro e
  induction e with
  | bvar i h bb fb lp =>
    intro hw
    have : mkBVar i = ExprC.bvar i h bb fb lp := hw
    rw [← this]
    rfl
  | fvar idx n ty h bb fb lp iht =>
    intro hw
    obtain ⟨-, heq⟩ := hw.fvar_inv
    rw [heq]
    rfl
  | sort u h bb fb lp =>
    intro hw
    have : mkSort u = ExprC.sort u h bb fb lp := hw
    rw [← this]
    rfl
  | const n us h bb fb lp =>
    intro hw
    have : mkConst n us = ExprC.const n us h bb fb lp := hw
    rw [← this]
    rfl
  | app f a h bb fb lp ihf iha =>
    intro hw
    obtain ⟨hf, ha, heq⟩ := hw.app_inv
    rw [heq]
    show max f.bvarB a.bvarB = _
    rw [ihf hf, iha ha]
    rfl
  | lam n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.lam_inv
    rw [heq]
    show max ty.bvarB (b.bvarB - 1) = _
    rw [iht hty, ihb hb]
    rfl
  | forallE n ty b m h bb fb lp iht ihb =>
    intro hw
    obtain ⟨hty, hb, heq⟩ := hw.forallE_inv
    rw [heq]
    show max ty.bvarB (b.bvarB - 1) = _
    rw [iht hty, ihb hb]
    rfl
  | letE n ty v b h bb fb lp iht ihv ihb =>
    intro hw
    obtain ⟨hty, hv, hb, heq⟩ := hw.letE_inv
    rw [heq]
    show max (max ty.bvarB v.bvarB) (b.bvarB - 1) = _
    rw [iht hty, ihv hv, ihb hb]
    rfl
  | lit l h bb fb lp =>
    intro hw
    have : mkLit l = ExprC.lit l h bb fb lp := hw
    rw [← this]
    rfl
  | proj s i e h bb fb lp ihe =>
    intro hw
    obtain ⟨he, heq⟩ := hw.proj_inv
    rw [heq]
    show e.bvarB = _
    rw [ihe he]
    rfl

/-- Cutoff consequence: a bound at or below the cursor certifies
`looseBVarsBounded` of the erasure (the transposition of
`TWF.bvarBoundD_le2`). -/
theorem bvarB_le {e : ExprC} {d : Nat} (hw : WFc e) (hle : e.bvarB ≤ d) :
    (eraseC e).looseBVarsBounded d = true :=
  EStore.looseBVarsBounded_iff.mpr (bvarB_exact hw ▸ hle)

end ExprC

end Setlec.Cached
