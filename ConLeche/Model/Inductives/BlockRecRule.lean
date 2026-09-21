module

public import ConLeche.Model.Inductives.BlockRecRead
public import ConLeche.Semantics.Tower.BlockRecI
import ConLeche.Model.Annot.BitClosed
import ConLeche.Verify.InstList

public section

/-!
# O-1: the abstraction's inverse, at the reading (task #315, milestone M5)

`checkBlockRule` stores the ANNOTATED STREAM right-hand side and keeps
nothing of the abstraction; the model has to read the stored body and
recover the design's `Rb = Rb''[ih_i ↦ ihFun_i]`.  That is **O-1**,
and — the correction of the M5M lane's session 2 — it is an `interp`
equation, not a syntactic one: at a guarded call the abstraction
leaves `ih_r a⃗`, and substituting the ih's λ-tower makes a β-redex,
which `ihFunAV_fold` (`Semantics/Tower/BlockRecI.lean`) evaluates.

## The frame the induction is carried at

`denoteMeta` has no `.bvar` clause, so nothing with a loose bound
variable has a reading at all: the induction must be carried at the
OPENED forms.  The opening is the check's own
(`openPisAtFvars`/`instantiateList` at `(fvsPref ++ fvsF).reverse`) —
loose `bvar j` becomes `fvar (E - 1 - j)` at a frame of `E` variables,
which `denoteMeta` at depth `E` reads straight back as `bvar j`.  So
an opened reading has EXACTLY the raw term's de Bruijn indices, and
the two sides of O-1 differ only by the `nR` `ih` binders the
abstraction inserted.

`FvarList E xs` is that opening list, taken as a PARAMETER rather than
spelled: `denoteMeta` ignores an `fvar`'s stored type, so the frames
the check builds (whose types are the rule's domains) and the ih
frame's are all instances of the same claim, and the induction never
has to know which.

## What the two lemmas are

* `denoteMeta_liftLooseBVars` — the abstraction's NON-call cases, in
  one go: `abstractIh` on a recursor-free subterm IS
  `Expr.liftLooseBVars fr.nR d` (`abstractIh_of_recFree`), and the
  reading of a lifted term is the reading, lifted
  (`AnnotTerm.liftN fr.nR d`).  This also covers the arguments `a⃗` of
  a guarded call, which the abstraction lifts and does not descend
  into.
* `interp_abstractIh` — O-1 itself, by structural induction on the
  rule body, with ONE named premise: `IhNodeVal`, the guarded call's
  value.  Everything else is `interp_liftN` and congruence.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe uv

/-! ## The opening list -/

/-- **A frame opening**: `xs` replaces the `E` loose bound variables of
a term by free variables, `bvar j ↦ fvar (E - 1 - j)`, which is what
`openPisAtFvars`' fvars do when `instantiateList`d in reverse
(`checkBlockRule`'s `(fvsPref ++ fvsF).reverse`).  The fvars' stored
TYPES are free: `denoteMeta` does not read them. -/
@[expose] def FvarList (E : Nat) (xs : List Expr) : Prop :=
  xs.length = E ∧ ∀ j, j < E → ∃ ty : Expr, xs[j]? = some (.fvar (E - 1 - j) ty)

theorem FvarList.cons {E : Nat} {xs : List Expr} (h : FvarList E xs) (ty : Expr) :
    FvarList (E + 1) (Expr.fvar E ty :: xs) := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  cases j with
  | zero => exact ⟨ty, by simp⟩
  | succ j =>
    obtain ⟨ty', hty'⟩ := h.2 j (by omega)
    refine ⟨ty', ?_⟩
    rw [show E + 1 - 1 - (j + 1) = E - 1 - j from by omega]
    simpa using hty'

/-- Opening a loose variable that the frame covers. -/
theorem FvarList.bvar_lt {E j : Nat} {xs : List Expr} (h : FvarList E xs) (hj : j < E) :
    ∃ ty : Expr, (Expr.bvar j).instantiateList xs 0 = .fvar (E - 1 - j) ty := by
  obtain ⟨ty, hty⟩ := h.2 j hj
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hty
  refine ⟨ty, ?_⟩
  rw [Expr.instantiateList, if_neg (by omega), dif_pos (by omega)]
  simp only [Nat.sub_zero]
  rw [show xs[j] = Expr.fvar (E - 1 - j) ty from hget, Expr.instantiateList]

/-- Opening a loose variable above the frame: the index is lowered,
and `denoteMeta` has no clause for it. -/
theorem FvarList.bvar_ge {E j : Nat} {xs : List Expr} (h : FvarList E xs) (hj : E ≤ j) :
    (Expr.bvar j).instantiateList xs 0 = .bvar (j - E) := by
  rw [Expr.instantiateList, if_neg (by omega), dif_neg (by rw [h.1]; omega), h.1]

/-! ## The literal readings are lift-invariant

`BitShift.lean` has these at `liftN 1`; the abstraction inserts `nR`
binders at once, and the leaves' closedness gives every `n`. -/

theorem natLitAV_liftN_gen {za sa : AnnotTerm} {n k : Nat}
    (hz : za.liftN n k = za) (hs : sa.liftN n k = sa) :
    ∀ m : Nat, (natLitAV za sa m).liftN n k = natLitAV za sa m
  | 0 => hz
  | m + 1 => by
    show (AnnotTerm.app sa (natLitAV za sa m)).liftN n k = _
    rw [AnnotTerm.liftN_app, hs, natLitAV_liftN_gen hz hs m]
    rfl

theorem charListAV_liftN_gen {nilA consA ofNatA za sa : AnnotTerm} {n k : Nat}
    (hnil : nilA.liftN n k = nilA) (hcons : consA.liftN n k = consA)
    (hof : ofNatA.liftN n k = ofNatA) (hz : za.liftN n k = za) (hs : sa.liftN n k = sa) :
    ∀ cs : List Char,
      (charListAV nilA consA ofNatA za sa cs).liftN n k
        = charListAV nilA consA ofNatA za sa cs
  | [] => hnil
  | c :: cs => by
    show (AnnotTerm.app (.app consA (.app ofNatA (natLitAV za sa c.toNat)))
      (charListAV nilA consA ofNatA za sa cs)).liftN n k = _
    rw [AnnotTerm.liftN_app, AnnotTerm.liftN_app, AnnotTerm.liftN_app, hcons, hof,
      natLitAV_liftN_gen hz hs, charListAV_liftN_gen hnil hcons hof hz hs cs]
    rfl

/-! ## L1 — the reading of a lifted term is the reading, lifted -/

variable {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}

theorem denoteMeta_bvar {D j : Nat} : denoteMeta acval env φ D (.bvar j) = none := by
  rw [denoteMeta] <;> simp

set_option maxHeartbeats 1000000 in
/-- **The abstraction's non-call step, at the reading.**  A term
opened at a frame of `F + d` variables and the SAME term lifted past
`nR` binders at cut `d`, opened at a frame of `F + nR + d`, read
alike up to `AnnotTerm.liftN nR · d`.

This is what `abstractIh_of_recFree` becomes at the denotation — the
abstraction moved every non-call node and nothing else — and it is
also the guarded call's ARGUMENTS, which the abstraction lifts without
descending into them. -/
theorem denoteMeta_open_liftLooseBVars
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    (nR F : Nat) :
    ∀ (e : Expr) (d : Nat) (as1 as2 : List Expr), e.hasFvar = false →
      FvarList (F + d) as1 → FvarList (F + nR + d) as2 →
      denoteMeta acval env φ (F + nR + d) ((e.liftLooseBVars nR d).instantiateList as2 0)
        = (denoteMeta acval env φ (F + d) (e.instantiateList as1 0)).map
            (AnnotTerm.liftN nR · d)
  | .bvar j, d, as1, as2, _, h1, h2 => by
    rcases Nat.lt_or_ge j d with hjd | hjd
    · -- a LOCAL binder: both frames carry it, at their own index
      obtain ⟨ty1, he1⟩ := h1.bvar_lt (j := j) (by omega)
      obtain ⟨ty2, he2⟩ := h2.bvar_lt (j := j) (by omega)
      rw [Expr.liftLooseBVars, if_neg (by omega), he1, he2,
        denoteMeta_fvar, denoteMeta_fvar, Option.map_some,
        show F + nR + d - 1 - (F + nR + d - 1 - j) = j from by omega,
        show F + d - 1 - (F + d - 1 - j) = j from by omega,
        AnnotTerm.liftN, if_pos hjd]
    rcases Nat.lt_or_ge j (F + d) with hjF | hjF
    · -- a FRAME variable: the same fvar on both sides, read `nR` deeper
      obtain ⟨ty1, he1⟩ := h1.bvar_lt (j := j) hjF
      obtain ⟨ty2, he2⟩ := h2.bvar_lt (j := j + nR) (by omega)
      rw [Expr.liftLooseBVars, if_pos hjd, he1, he2,
        denoteMeta_fvar, denoteMeta_fvar, Option.map_some,
        show F + nR + d - 1 - (F + nR + d - 1 - (j + nR)) = j + nR from by omega,
        show F + d - 1 - (F + d - 1 - j) = j from by omega,
        AnnotTerm.liftN, if_neg (by omega)]
    · -- above the frame: no reading on either side
      rw [Expr.liftLooseBVars, if_pos hjd, h1.bvar_ge (j := j) hjF,
        h2.bvar_ge (j := j + nR) (by omega), denoteMeta_bvar, denoteMeta_bvar,
        Option.map_none]
  | .sort u, d, as1, as2, _, _, _ => by
    simp only [Expr.liftLooseBVars, Expr.instantiateList, denoteMeta, Option.map_some]
    rfl
  | .fvar _ _, _, _, _, hf, _, _ => absurd hf (by simp [Expr.hasFvar])
  | .lit (.natVal k), d, as1, as2, _, _, _ => by
    simp only [Expr.liftLooseBVars, Expr.instantiateList, denoteMeta]
    split
    · rw [Option.map_some]
      exact congrArg some (natLitAV_liftN_gen (hacl _ _ _ _) (hacl _ _ _ _) k).symm
    · rfl
  | .lit (.strVal s), d, as1, as2, _, _, _ => by
    simp only [Expr.liftLooseBVars, Expr.instantiateList, denoteMeta]
    split
    · rw [Option.map_some]
      refine congrArg some ?_
      symm
      rw [AnnotTerm.liftN_app, hacl,
        charListAV_liftN_gen (by rw [AnnotTerm.liftN_app, hacl, hacl])
          (by rw [AnnotTerm.liftN_app, hacl, hacl]) (hacl _ _ _ _)
          (hacl _ _ _ _) (hacl _ _ _ _)]
    · rfl
  | .const n us, d, as1, as2, _, _, _ => by
    simp only [Expr.liftLooseBVars, Expr.instantiateList, denoteMeta]
    cases env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · rw [Option.map_some, hacl]
      · rfl
  | .letE ty v b, d, as1, as2, _, _, _ => by
    simp only [Expr.liftLooseBVars, Expr.instantiateList, denoteMeta, Option.map_none]
  | .app f a, d, as1, as2, hf, h1, h2 => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.liftLooseBVars, Expr.instantiateList, denoteMeta]
    rw [denoteMeta_open_liftLooseBVars hacl nR F f d as1 as2 hf.1 h1 h2,
      denoteMeta_open_liftLooseBVars hacl nR F a d as1 as2 hf.2 h1 h2]
    cases denoteMeta acval env φ (F + d) (f.instantiateList as1 0) with
    | none => rfl
    | some fa =>
      cases denoteMeta acval env φ (F + d) (a.instantiateList as1 0) with
      | none => rfl
      | some aa => rfl
  | .proj sn i e, d, as1, as2, hf, h1, h2 => by
    simp only [Expr.hasFvar] at hf
    simp only [Expr.liftLooseBVars, Expr.instantiateList, denoteMeta]
    rw [denoteMeta_open_liftLooseBVars hacl nR F e d as1 as2 hf h1 h2]
    cases denoteMeta acval env φ (F + d) (e.instantiateList as1 0) with
    | none => rfl
    | some ea =>
      simp only [Option.map_some]
      cases env.findProj? sn i with
      | some entry =>
        show some (projAV (i + entry.off) (AnnotTerm.liftN nR ea d))
          = Option.map (AnnotTerm.liftN nR · d) (some (projAV (i + entry.off) ea))
        simp only [Option.map_some, projAV_liftN]
      | none =>
        dsimp only
        rcases i with _ | _ | i <;> rfl
  | .lam ty b bi, d, as1, as2, hf, h1, h2 => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.liftLooseBVars, Expr.instantiateList, denoteMeta]
    rw [denoteMeta_open_liftLooseBVars hacl nR F ty d as1 as2 hf.1 h1 h2]
    cases hty : denoteMeta acval env φ (F + d) (ty.instantiateList as1 0) with
    | none => rfl
    | some ta =>
      simp only [Option.map_some]
      rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons,
        show F + nR + d + 1 = F + nR + (d + 1) from by omega,
        show F + d + 1 = F + (d + 1) from by omega,
        denoteMeta_open_liftLooseBVars hacl nR F b (d + 1)
          (Expr.fvar (F + d) (ty.instantiateList as1 0) :: as1)
          (Expr.fvar (F + nR + d) ((ty.liftLooseBVars nR d).instantiateList as2 0) :: as2)
          hf.2 (by rw [show F + (d + 1) = F + d + 1 from by omega]; exact h1.cons _)
            (by rw [show F + nR + (d + 1) = F + nR + d + 1 from by omega]; exact h2.cons _)]
      cases denoteMeta acval env φ (F + (d + 1))
          (b.instantiateList (Expr.fvar (F + d) (ty.instantiateList as1 0) :: as1) 0) with
      | none => rfl
      | some ba => rfl
  | .forallE ty b bi, d, as1, as2, hf, h1, h2 => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.liftLooseBVars, Expr.instantiateList, denoteMeta]
    rw [denoteMeta_open_liftLooseBVars hacl nR F ty d as1 as2 hf.1 h1 h2]
    cases hty : denoteMeta acval env φ (F + d) (ty.instantiateList as1 0) with
    | none => rfl
    | some ta =>
      simp only [Option.map_some]
      rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons,
        show F + nR + d + 1 = F + nR + (d + 1) from by omega,
        show F + d + 1 = F + (d + 1) from by omega,
        denoteMeta_open_liftLooseBVars hacl nR F b (d + 1)
          (Expr.fvar (F + d) (ty.instantiateList as1 0) :: as1)
          (Expr.fvar (F + nR + d) ((ty.liftLooseBVars nR d).instantiateList as2 0) :: as2)
          hf.2 (by rw [show F + (d + 1) = F + d + 1 from by omega]; exact h1.cons _)
            (by rw [show F + nR + (d + 1) = F + nR + d + 1 from by omega]; exact h2.cons _)]
      cases denoteMeta acval env φ (F + (d + 1))
          (b.instantiateList (Expr.fvar (F + d) (ty.instantiateList as1 0) :: as1) 0) with
      | none => rfl
      | some ba => rfl

end ConLeche.Model
