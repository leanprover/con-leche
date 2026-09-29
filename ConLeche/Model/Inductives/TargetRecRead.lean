module

import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Rules.Sound
public import ConLeche.Model.Inductives.BlockRecRule

public section

/-!
# The classification-free abstraction, READ

`targetAbstract` (`ConLeche/Kernel/Inductives/RecCheck.lean`) walks a
rule body whose FRAME (the recursor's prefix and the constructor's
fields) is already free variables `0 … base-1` and whose LOCAL binders
are still bound, and replaces every recursive call by an `ih` free
variable `base + r` applied to the call's telescope variables.  This
file is the model's reading of that walk.

The frame being free makes the non-call step simple: the abstraction
leaves a recursor-free node syntactically UNCHANGED, and its two readings — at depth `base + d` (the stored body) and at
`base + n + d` (the residue, `n` `ih` variables deeper) — differ by
`AnnotTerm.liftN n · d` alone (`denoteMeta_open_deepen`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe uv

/-! ## The local opening -/

/-- **A local opening above a free frame**: `xs` replaces the `d`
loose bound variables of a term by the free variables above the frame
`B`, `bvar j ↦ fvar (B + d - 1 - j)`.  The stored types are free:
`denoteMeta` does not read them. -/
@[expose] def LocList (B d : Nat) (xs : List Expr) : Prop :=
  xs.length = d ∧ ∀ j, j < d → ∃ ty : Expr, xs[j]? = some (.fvar (B + d - 1 - j) ty)

theorem LocList.nil (B : Nat) : LocList B 0 [] :=
  ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩

theorem LocList.cons {B d : Nat} {xs : List Expr} (h : LocList B d xs) (ty : Expr) :
    LocList B (d + 1) (Expr.fvar (B + d) ty :: xs) := by
  refine ⟨by simp [h.1], fun j hj => ?_⟩
  cases j with
  | zero => exact ⟨ty, by simp⟩
  | succ j =>
    obtain ⟨ty', hty'⟩ := h.2 j (by omega)
    refine ⟨ty', ?_⟩
    rw [show B + (d + 1) - 1 - (j + 1) = B + d - 1 - j from by omega]
    simpa using hty'

/-- Opening a local variable the list covers. -/
theorem LocList.bvar_lt {B d j : Nat} {xs : List Expr} (h : LocList B d xs) (hj : j < d) :
    ∃ ty : Expr, (Expr.bvar j).instantiateList xs 0 = .fvar (B + d - 1 - j) ty := by
  obtain ⟨ty, hty⟩ := h.2 j hj
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hty
  refine ⟨ty, ?_⟩
  rw [Expr.instantiateList, if_neg (by omega), dif_pos (by omega)]
  simp only [Nat.sub_zero]
  rw [show xs[j] = Expr.fvar (B + d - 1 - j) ty from hget, Expr.instantiateList]

/-- Opening a loose variable above the locals: lowered, unread. -/
theorem LocList.bvar_ge {B d j : Nat} {xs : List Expr} (h : LocList B d xs) (hj : d ≤ j) :
    (Expr.bvar j).instantiateList xs 0 = .bvar (j - d) := by
  rw [Expr.instantiateList, if_neg (by omega), dif_neg (by rw [h.1]; omega), h.1]

/-! ## The non-call step: the same node, read `n` binders deeper -/

variable {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}

set_option maxHeartbeats 1000000 in
/-- **A frame-bounded node read `n` variables deeper.**  A term whose
free variables are all below the frame `B`, opened at `d` locals above
`B` and — the SAME term — at `d` locals above `B + n`, reads alike up
to `AnnotTerm.liftN n · d`: the locals keep their de Bruijn indices,
the frame's move `n` further out. -/
theorem denoteMeta_open_deepen
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    (n B : Nat) :
    ∀ (e : Expr) (d : Nat) (as1 as2 : List Expr), (∀ l ∈ e.fvarLeaves, l.1 < B) →
      LocList B d as1 → LocList (B + n) d as2 →
      denoteMeta acval env φ (B + n + d) (e.instantiateList as2 0)
        = (denoteMeta acval env φ (B + d) (e.instantiateList as1 0)).map
            (AnnotTerm.liftN n · d)
  | .bvar j, d, as1, as2, _, h1, h2 => by
    rcases Nat.lt_or_ge j d with hjd | hjd
    · obtain ⟨ty1, he1⟩ := h1.bvar_lt hjd
      obtain ⟨ty2, he2⟩ := h2.bvar_lt hjd
      rw [he1, he2, denoteMeta_fvar, denoteMeta_fvar, Option.map_some,
        show B + n + d - 1 - (B + n + d - 1 - j) = j from by omega,
        show B + d - 1 - (B + d - 1 - j) = j from by omega,
        AnnotTerm.liftN, if_pos hjd]
    · rw [h1.bvar_ge hjd, h2.bvar_ge hjd, denoteMeta_bvar, denoteMeta_bvar, Option.map_none]
  | .fvar i ty, d, as1, as2, hl, _, _ => by
    have hi : i < B := hl (i, ty) (by simp [Expr.fvarLeaves])
    simp only [Expr.instantiateList]
    rw [denoteMeta_fvar, denoteMeta_fvar, Option.map_some, AnnotTerm.liftN, if_neg (by omega),
      show B + d - 1 - i + n = B + n + d - 1 - i from by omega]
  | .sort u, d, as1, as2, _, _, _ => by
    simp only [Expr.instantiateList, denoteMeta, Option.map_some]
    rfl
  | .lit (.natVal k), d, as1, as2, _, _, _ => by
    simp only [Expr.instantiateList, denoteMeta]
    split
    · rw [Option.map_some]
      exact congrArg some (natLitAV_liftN_gen (hacl _ _ _ _) (hacl _ _ _ _) k).symm
    · rfl
  | .lit (.strVal s), d, as1, as2, _, _, _ => by
    simp only [Expr.instantiateList, denoteMeta]
    split
    · rw [Option.map_some]
      refine congrArg some ?_
      symm
      rw [AnnotTerm.liftN_app, hacl,
        charListAV_liftN_gen (by rw [AnnotTerm.liftN_app, hacl, hacl])
          (by rw [AnnotTerm.liftN_app, hacl, hacl]) (hacl _ _ _ _)
          (hacl _ _ _ _) (hacl _ _ _ _)]
    · rfl
  | .const c us, d, as1, as2, _, _, _ => by
    simp only [Expr.instantiateList, denoteMeta]
    cases env.find? c with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · rw [Option.map_some, hacl]
      · rfl
  | .letE ty v b, d, as1, as2, _, _, _ => by
    simp only [Expr.instantiateList, denoteMeta, Option.map_none]
  | .app f a, d, as1, as2, hl, h1, h2 => by
    have hlf : ∀ l ∈ f.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    have hla : ∀ l ∈ a.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    simp only [Expr.instantiateList, denoteMeta]
    rw [denoteMeta_open_deepen hacl n B f d as1 as2 hlf h1 h2,
      denoteMeta_open_deepen hacl n B a d as1 as2 hla h1 h2]
    cases denoteMeta acval env φ (B + d) (f.instantiateList as1 0) with
    | none => rfl
    | some fa =>
      cases denoteMeta acval env φ (B + d) (a.instantiateList as1 0) with
      | none => rfl
      | some aa => rfl
  | .proj sn i e, d, as1, as2, hl, h1, h2 => by
    have hle : ∀ l ∈ e.fvarLeaves, l.1 < B := fun l h => hl l (by simpa [Expr.fvarLeaves] using h)
    simp only [Expr.instantiateList, denoteMeta]
    rw [denoteMeta_open_deepen hacl n B e d as1 as2 hle h1 h2]
    cases denoteMeta acval env φ (B + d) (e.instantiateList as1 0) with
    | none => rfl
    | some ea =>
      simp only [Option.map_some]
      cases env.findProj? sn i with
      | some entry =>
        show some (projAV (i + entry.off) (AnnotTerm.liftN n ea d))
          = Option.map (AnnotTerm.liftN n · d) (some (projAV (i + entry.off) ea))
        simp only [Option.map_some, projAV_liftN]
      | none =>
        dsimp only
        rcases i with _ | _ | i <;> rfl
  | .lam ty b bi, d, as1, as2, hl, h1, h2 | .forallE ty b bi, d, as1, as2, hl, h1, h2 => by
    have hlt : ∀ l ∈ ty.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    have hlb : ∀ l ∈ b.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    simp only [Expr.instantiateList, denoteMeta]
    rw [denoteMeta_open_deepen hacl n B ty d as1 as2 hlt h1 h2]
    cases hty : denoteMeta acval env φ (B + d) (ty.instantiateList as1 0) with
    | none => rfl
    | some ta =>
      simp only [Option.map_some]
      rw [← Expr.instantiateList_cons, ← Expr.instantiateList_cons,
        show B + n + d + 1 = B + n + (d + 1) from by omega,
        show B + d + 1 = B + (d + 1) from by omega,
        denoteMeta_open_deepen hacl n B b (d + 1)
          (Expr.fvar (B + d) (ty.instantiateList as1 0) :: as1)
          (Expr.fvar (B + n + d) (ty.instantiateList as2 0) :: as2) hlb
          (h1.cons _) (h2.cons _)]
      cases denoteMeta acval env φ (B + (d + 1))
          (b.instantiateList (Expr.fvar (B + d) (ty.instantiateList as1 0) :: as1) 0) with
      | none => rfl
      | some ba => rfl

/-! ## The walk's accumulator -/

/-! ## Opening by a list of free variables

The residue's nodes carry free variables of their own — the frame's and
the `ih` variables.  These are the opening lemmas for an opening list
whose entries are all free variables (`LocList`'s). -/

/-- A term whose every leaf is an entry of a frame list is scoped by it. -/
theorem wscoped_of_leaves_mem {D : Nat} {L : List Expr} (hL : FvarList D L) :
    ∀ (E : Expr), (∀ l ∈ E.fvarLeaves, Expr.fvar l.1 l.2 ∈ L) → Expr.WScoped D E := by
  intro E
  induction E with
  | fvar i ty _ =>
    intro hl
    exact hL.2.2 _ (hl (i, ty) (by simp [Expr.fvarLeaves]))
  | app f a ihf iha =>
    intro hl
    simp only [Expr.WScoped]
    exact ⟨ihf fun l h => hl l (by simp [Expr.fvarLeaves, h]),
      iha fun l h => hl l (by simp [Expr.fvarLeaves, h])⟩
  | lam ty b _ ihty ihb =>
    intro hl
    simp only [Expr.WScoped]
    exact ⟨ihty fun l h => hl l (by simp [Expr.fvarLeaves, h]),
      ihb fun l h => hl l (by simp [Expr.fvarLeaves, h])⟩
  | forallE ty b _ ihty ihb =>
    intro hl
    simp only [Expr.WScoped]
    exact ⟨ihty fun l h => hl l (by simp [Expr.fvarLeaves, h]),
      ihb fun l h => hl l (by simp [Expr.fvarLeaves, h])⟩
  | letE ty v b ihty ihv ihb =>
    intro hl
    simp only [Expr.WScoped]
    exact ⟨ihty fun l h => hl l (by simp [Expr.fvarLeaves, h]),
      ihv fun l h => hl l (by simp [Expr.fvarLeaves, h]),
      ihb fun l h => hl l (by simp [Expr.fvarLeaves, h])⟩
  | proj _ _ e ihe =>
    intro hl
    simp only [Expr.WScoped]
    exact ihe fun l h => hl l (by simpa [Expr.fvarLeaves] using h)
  | bvar _ => intro _; simp [Expr.WScoped]
  | sort _ => intro _; simp [Expr.WScoped]
  | const _ _ => intro _; simp [Expr.WScoped]
  | lit _ => intro _; simp [Expr.WScoped]

/-! ## The walk's context, over a frame that carries its own variables

`WalkCtx` (`BlockRecRule.lean`) is stated over a list `L` of opened
variables; here `L` is the locals opened so far (`as2`) above the
rule's FRAME (`frameIh`: the prefix, the fields and the `ih`
variables, which the residue already mentions as free variables). -/

section Ctx

variable {V : Type uv} [SetTheory V]

/-- A subject that carries free variables, its leaves entries of the frame
list, is framed, in the context and graded. -/
theorem WalkCtx.subjOkL {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D : Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {ρfull : Nat → V} {Δa : List AnnotTerm} {L : List Expr}
    (h2 : FvarList D L) (h : WalkCtx V mT φ D ρfull Δa L)
    {E : Expr} (hcll : ∀ l ∈ E.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hlbb : E.looseBVarsBounded 0 = true) {ea : AnnotTerm}
    (hea : denoteMeta mT.acval envT φ D E = some ea) (hty : IhTyped envT D E) :
    Rules.Frame D E ∧ CtxOk mT φ D Δa E ∧ Rules.Graded V Δa ea := by
  have hLB : Expr.LeavesBounded E := fun l hl => h.2.2.2.2.1 _ (hcll l hl)
  have hFr : Rules.Frame D E := ⟨wscoped_of_leaves_mem h2 E hcll, hlbb, hLB⟩
  have hctx := h.ctxOk hacl h2 hcll
  obtain ⟨t, hInf⟩ := hty
  obtain ⟨-, -, ta, -, hG, -, -⟩ := Rules.infer_sound hin hInf hFr hctx hea
  exact ⟨hFr, hctx, hG⟩

end Ctx

end ConLeche.Model
