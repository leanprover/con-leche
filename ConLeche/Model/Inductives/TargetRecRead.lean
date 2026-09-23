module

import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Inductives.StructEntryKit
public import ConLeche.Model.Inductives.BlockRecRule
public import ConLeche.Kernel.Inductives.RecCheck

public section

/-!
# The classification-free abstraction, READ (lane RECLIB, B3's core)

`targetAbstract` (`ConLeche/Kernel/Inductives/RecCheck.lean`) walks a
rule body whose FRAME (the recursor's prefix and the constructor's
fields) is already free variables `0 … base-1` and whose LOCAL binders
are still bound, and replaces every recursive call by an `ih` free
variable `base + r` applied to the call's telescope variables.  This
file is the model's reading of that walk — the analogue, for the
free-variable frame, of `interp_abstractIh`
(`Model/Inductives/BlockRecRule.lean`), which reads the kind-reading
check's bound-variable abstraction.

The frame being free makes the non-call step simpler than there: the
abstraction leaves a recursor-free node syntactically UNCHANGED, and
its two readings — at depth `base + d` (the stored body) and at
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
  | .lam ty b bi, d, as1, as2, hl, h1, h2 => by
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
  | .forallE ty b bi, d, as1, as2, hl, h1, h2 => by
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

/-- The accumulator's entries are the frame's `ih` variables in order:
entry `r` is `fvar (B + r)` at its own type. -/
@[expose] def TargetIhWF (B : Nat) (acc : Array ConLeche.TargetIh) : Prop :=
  ∀ (r : Nat) (h : r < acc.size), acc[r].fv = .fvar (B + r) acc[r].ty

/-- **The walk only appends**, and keeps the entries' shape. -/
theorem targetAbstract_acc {fr : ConLeche.TargetFrame} {B : Nat} :
    ∀ (d : Nat) (e : Expr) (acc : Array ConLeche.TargetIh) (e' : Expr)
      (acc' : Array ConLeche.TargetIh),
      ConLeche.targetAbstract fr B d e acc = some (e', acc') →
      acc.toList <+: acc'.toList ∧ (TargetIhWF B acc → TargetIhWF B acc')
  | _, .bvar _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨List.prefix_refl _, id⟩
  | _, .sort _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨List.prefix_refl _, id⟩
  | _, .lit _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨List.prefix_refl _, id⟩
  | _, .fvar _ _, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h; exact ⟨List.prefix_refl _, id⟩
  | _, .const n us, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h; exact ⟨List.prefix_refl _, id⟩
  | d, .lam ty b bi, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨p1, w1⟩ := targetAbstract_acc d ty acc ty' acc1 h1
    obtain ⟨p2, w2⟩ := targetAbstract_acc (d + 1) b acc1 b' acc2 h2
    exact ⟨p1.trans p2, fun w => w2 (w1 w)⟩
  | d, .forallE ty b bi, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨b', acc2⟩, h2, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨p1, w1⟩ := targetAbstract_acc d ty acc ty' acc1 h1
    obtain ⟨p2, w2⟩ := targetAbstract_acc (d + 1) b acc1 b' acc2 h2
    exact ⟨p1.trans p2, fun w => w2 (w1 w)⟩
  | d, .letE ty v b, acc, _, _, h => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨ty', acc1⟩, h1, ⟨v', acc2⟩, h2, ⟨b', acc3⟩, h3, h⟩ := h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    obtain ⟨p1, w1⟩ := targetAbstract_acc d ty acc ty' acc1 h1
    obtain ⟨p2, w2⟩ := targetAbstract_acc d v acc1 v' acc2 h2
    obtain ⟨p3, w3⟩ := targetAbstract_acc (d + 1) b acc2 b' acc3 h3
    exact ⟨(p1.trans p2).trans p3, fun w => w3 (w2 (w1 w))⟩
  | d, .proj sn i x, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · exact nomatch h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨x', acc1⟩, h1, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact targetAbstract_acc d x acc x' acc1 h1
  | d, .app f a, acc, _, _, h => by
    simp only [ConLeche.targetAbstract] at h
    split at h
    · next i c m idx hc =>
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨ty, hty, h⟩ := h
      split at h
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h; exact ⟨List.prefix_refl _, id⟩
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        refine ⟨by simp, fun w r hr => ?_⟩
        rw [Array.size_push] at hr
        rcases Nat.lt_or_ge r acc.size with hlt | hge
        · rw [Array.getElem_push_lt hlt]; exact w r hlt
        · obtain rfl : r = acc.size := by omega
          rw [Array.getElem_push_eq]
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨f', acc1⟩, h1, ⟨a', acc2⟩, h2, h⟩ := h
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      obtain ⟨p1, w1⟩ := targetAbstract_acc d f acc f' acc1 h1
      obtain ⟨p2, w2⟩ := targetAbstract_acc d a acc1 a' acc2 h2
      exact ⟨p1.trans p2, fun w => w2 (w1 w)⟩

/-! ## The two kinds of node, at `interp` -/

section Interp

variable {V : Type uv} [SetTheory V]

/-- **The non-call node's `interp` step**: a frame-bounded node, opened
at the two frames, reads the same once the `ih` block is dropped. -/
theorem interp_of_open_deepen
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {n B d : Nat} {e : Expr} {as1 as2 : List Expr} {locals ihvals : List V} {ρ' : Nat → V}
    {A Bv : AnnotTerm} (hl : ∀ l ∈ e.fvarLeaves, l.1 < B)
    (h1 : LocList B d as1) (h2 : LocList (B + n) d as2)
    (hloc : locals.length = d) (hih : ihvals.length = n)
    (hA : denoteMeta acval env φ (B + d) (e.instantiateList as1 0) = some A)
    (hB : denoteMeta acval env φ (B + n + d) (e.instantiateList as2 0) = some Bv) :
    interp V (consList locals ρ') A
      = interp V (consList locals (consList ihvals ρ')) Bv := by
  have hEq := denoteMeta_open_deepen (acval := acval) (env := env) (φ := φ) hacl n B e d as1 as2
    hl h1 h2
  rw [hA, hB, Option.map_some] at hEq
  obtain rfl : Bv = A.liftN n d := Option.some.inj hEq
  rw [interp_liftN V n A d, shiftE_consList_ih hloc hih]

/-- The telescope variables' values: the last `m` locals, in order. -/
theorem consList_teleVars {d m : Nat} {locals : List V} {σ : Nat → V}
    (hloc : locals.length = d) (hm : m ≤ d) :
    (List.range m).map (fun k => consList locals σ (m - 1 - k)) = locals.drop (d - m) := by
  apply List.ext_getElem
  · simp [hloc]; omega
  · intro k hk1 hk2
    simp only [List.length_map, List.length_range] at hk1
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop]
    rw [consList_getD_of_lt _ _ _ (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega), Option.getD_some]
    congr 1
    omega

/-- **The residue's call node, read**: `ih_r a⃗` is the `ih` value folded
along the last `m` locals. -/
theorem interp_ihApp {n B d m r : Nat} {ty : Expr} {as2 : List Expr}
    {locals ihvals : List V} {ρ' : Nat → V} {Bv : AnnotTerm}
    (h2 : LocList (B + n) d as2) (hm : m ≤ d) (hr : r < n)
    (hloc : locals.length = d) (hih : ihvals.length = n)
    (hB : denoteMeta acval env φ (B + n + d)
      ((Expr.mkAppN (.fvar (B + r) ty) (ConLeche.structTeleVars m)).instantiateList as2 0)
      = some Bv) :
    interp V (consList locals (consList ihvals ρ')) Bv
      = (locals.drop (d - m)).foldl SetTheory.app (ihvals.getD r pt) := by
  rw [instantiateList_mkAppN] at hB
  obtain ⟨fa, ws, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hB
  simp only [Expr.instantiateList, denoteMeta_fvar] at hfa
  obtain rfl := Option.some.inj hfa.symm
  -- the arguments: the local variables' own indices
  have hws : ws = (List.range m).map fun k => AnnotTerm.bvar (m - 1 - k) := by
    have key : ∀ (ks : List Nat), (∀ k ∈ ks, k < m) → ∀ ws',
        DenoteMetaSpine acval env φ (B + n + d)
          ((ks.map fun k => Expr.bvar (m - 1 - k)).map (·.instantiateList as2 0)) ws' →
        ws' = ks.map fun k => AnnotTerm.bvar (m - 1 - k) := by
      intro ks
      induction ks with
      | nil => intro _ ws' h; cases h; rfl
      | cons k ks ih =>
        intro hks ws' h
        cases h with
        | @cons _ w _ ws'' hw hrest =>
          have hk := hks k (by simp)
          obtain ⟨tyk, htyk⟩ := h2.bvar_lt (j := m - 1 - k) (by omega)
          simp only at hw
          rw [htyk, denoteMeta_fvar,
            show B + n + d - 1 - (B + n + d - 1 - (m - 1 - k)) = m - 1 - k from by omega] at hw
          rw [← Option.some.inj hw, ih (fun k' hk' => hks k' (by simp [hk'])) ws'' hrest]
          rfl
    exact key (List.range m) (fun k hk => List.mem_range.mp hk) ws
      (by simpa [ConLeche.structTeleVars, List.map_map] using hsp)
  subst hws
  rw [interp_mkAppN_foldl]
  have hhead : interp V (consList locals (consList ihvals ρ'))
      (.bvar (B + n + d - 1 - (B + r))) = ihvals.getD r pt := by
    show consList locals (consList ihvals ρ') (B + n + d - 1 - (B + r)) = _
    rw [show B + n + d - 1 - (B + r) = (n - 1 - r) + locals.length from by omega,
      consList_apply_add, consList_getD_of_lt _ _ _ (by omega), hih,
      show n - 1 - (n - 1 - r) = r from by omega]
  rw [hhead, List.map_map]
  have hargs : (List.range m).map ((interp V (consList locals (consList ihvals ρ'))) ∘
      fun k => AnnotTerm.bvar (m - 1 - k)) = locals.drop (d - m) := by
    rw [← consList_teleVars (σ := consList ihvals ρ') hloc hm]
    rfl
  rw [hargs]

end Interp

/-! ## The walk, read (O-1 for the classification-free check) -/

section Walk

variable {V : Type uv} [SetTheory V]

/-- **The call node's value, as a premise**: at a node `targetCall?`
recognises as the call `(i, c, m, idx)`, whose `ih` variable is entry
`r` of the rule's final accumulator, the STORED node reads to that
variable's value folded along the last `m` locals.  This is the
recursor model's seam (the graph family's value at the call's target),
not this induction's; the residue node it is traded for carries its
typing (`IhTyped`) and the locals their fit. -/
@[expose] def TargetNodeVal (V : Type uv) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat) (envT : Env)
    (fr : ConLeche.TargetFrame) (B : Nat) (ihsF : Array ConLeche.TargetIh) (ρ' : Nat → V)
    (ihvals : List V) : Prop :=
  ∀ (d : Nat) (locals : List V) (e : Expr) (i c m : Nat) (idx : List Expr) (r : Nat)
    (ih : ConLeche.TargetIh) (as1 as2 : List Expr) (A : AnnotTerm),
    ConLeche.targetCall? fr d e = some (i, c, m, idx) →
    ihsF[r]? = some ih → ih.field = i → ih.callee = c → ih.idx = idx →
    (∀ l ∈ e.fvarLeaves, l.1 < B) →
    LocList B d as1 → LocList (B + ihsF.size) d as2 → locals.length = d →
    LocalsFit V acval env φ B ρ' locals as1 →
    IhTyped envT (B + ihsF.size + d)
      ((Expr.mkAppN (.fvar (B + r) ih.ty) (ConLeche.structTeleVars m)).instantiateList as2 0) →
    denoteMeta acval env φ (B + d) (e.instantiateList as1 0) = some A →
    interp V (consList locals ρ') A
      = (locals.drop (d - m)).foldl SetTheory.app (ihvals.getD r pt)

theorem targetCall?_spec {fr : ConLeche.TargetFrame} {d : Nat} {e : Expr} {i c m : Nat}
    {idx : List Expr} (h : ConLeche.targetCall? fr d e = some (i, c, m, idx)) :
    m ≤ d ∧ m = (fr.teles.getD i []).length := by
  unfold ConLeche.targetCall? at h
  repeat' (first | split at h | (dsimp only at h; split at h))
  all_goals (try contradiction)
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rename_i hle _ _
  exact ⟨by simpa using hle, rfl⟩

/-- An entry of a prefix of the final accumulator is the final entry. -/
theorem prefix_getElem? {acc ihsF : Array ConLeche.TargetIh} (hp : acc.toList <+: ihsF.toList)
    {r : Nat} (hr : r < acc.size) : ihsF[r]? = some acc[r] := by
  obtain ⟨t, ht⟩ := hp
  have h1 : ihsF[r]? = ihsF.toList[r]? := by simp
  rw [h1, ← ht, List.getElem?_append_left (by simpa using hr)]
  simp

set_option maxHeartbeats 2000000 in
/-- **O-1 for the classification-free check**: the stored rule body,
read at the rule's frame, is the RESIDUE read at the frame extended by
the `ih` variables' values.  Structural over the body; every node the
walk did not replace is `interp_of_open_deepen`, and the one it did is
the premise `TargetNodeVal` against the residue node's own reading
(`interp_ihApp`). -/
theorem interp_targetAbstract
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {envT : Env} {fr : ConLeche.TargetFrame} {B : Nat} {ihsF : Array ConLeche.TargetIh}
    {ρ' : Nat → V} {ihvals : List V} (hih : ihvals.length = ihsF.size)
    (hcall : TargetNodeVal V acval env φ envT fr B ihsF ρ' ihvals) :
    ∀ (e : Expr) (d : Nat) (acc : Array ConLeche.TargetIh) (e' : Expr)
      (acc' : Array ConLeche.TargetIh) (locals : List V) (as1 as2 : List Expr)
      (A Bv : AnnotTerm),
      ConLeche.targetAbstract fr B d e acc = some (e', acc') →
      acc'.toList <+: ihsF.toList → TargetIhWF B acc →
      (∀ l ∈ e.fvarLeaves, l.1 < B) →
      LocList B d as1 → LocList (B + ihsF.size) d as2 → locals.length = d →
      LocalsFit V acval env φ B ρ' locals as1 →
      IhTyped envT (B + ihsF.size + d) (e'.instantiateList as2 0) →
      denoteMeta acval env φ (B + d) (e.instantiateList as1 0) = some A →
      denoteMeta acval env φ (B + ihsF.size + d) (e'.instantiateList as2 0) = some Bv →
      interp V (consList locals ρ') A = interp V (consList locals (consList ihvals ρ')) Bv
  | .bvar j, d, acc, e', acc', locals, as1, as2, A, Bv, hab, _, _, hl, h1, h2, hloc, _, _, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, -⟩ := hab
    exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA hB
  | .sort u, d, acc, e', acc', locals, as1, as2, A, Bv, hab, _, _, hl, h1, h2, hloc, _, _, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, -⟩ := hab
    exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA hB
  | .lit l, d, acc, e', acc', locals, as1, as2, A, Bv, hab, _, _, hl, h1, h2, hloc, _, _, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, -⟩ := hab
    exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA hB
  | .fvar i ty, d, acc, e', acc', locals, as1, as2, A, Bv, hab, _, _, hl, h1, h2, hloc, _, _, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, -⟩ := hab
    exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA hB
  | .const n us, d, acc, e', acc', locals, as1, as2, A, Bv, hab, _, _, hl, h1, h2, hloc, _, _, hA, hB => by
    simp only [ConLeche.targetAbstract] at hab
    split at hab
    · exact nomatch hab
    · simp only [Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, -⟩ := hab
      exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA hB
  | .letE ty v b, d, _, _, _, _, as1, _, A, _, _, _, _, _, _, _, _, _, _, hA, _ => by
    rw [Expr.instantiateList, denoteMeta] at hA
    exact nomatch hA
  | .proj sn i x, d, acc, e', acc', locals, as1, as2, A, Bv, hab, hpre, hwf, hl, h1, h2, hloc, hlf,
      hty, hA, hB => by
    simp only [ConLeche.targetAbstract] at hab
    split at hab
    · exact nomatch hab
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
    obtain ⟨⟨x', acc1⟩, hx, hab⟩ := hab
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    have hlx : ∀ l ∈ x.fvarLeaves, l.1 < B := fun l h => hl l (by simpa [Expr.fvarLeaves] using h)
    rw [Expr.instantiateList] at hty
    rw [Expr.instantiateList, denoteMeta_proj] at hA hB
    obtain ⟨ea, hea, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨eb, heb, hB⟩ := Option.bind_eq_some_iff.mp hB
    have hrec := interp_targetAbstract hacl hih hcall x d acc x' acc1 locals as1 as2 ea eb hx
      hpre hwf hlx h1 h2 hloc hlf hty.projArg hea heb
    revert hA hB
    cases env.findProj? sn i with
    | some entry =>
      intro hA hB
      obtain rfl : A = projAV (i + entry.off) ea := (Option.some.inj hA).symm
      obtain rfl : Bv = projAV (i + entry.off) eb := (Option.some.inj hB).symm
      rw [projAV_interp, projAV_interp, hrec]
    | none =>
      intro hA hB
      rcases i with _ | _ | i
      · obtain rfl : A = .fst ea := (Option.some.inj hA).symm
        obtain rfl : Bv = .fst eb := (Option.some.inj hB).symm
        rw [interp_fst, interp_fst, hrec]
      · obtain rfl : A = .snd ea := (Option.some.inj hA).symm
        obtain rfl : Bv = .snd eb := (Option.some.inj hB).symm
        rw [interp_snd, interp_snd, hrec]
      · exact nomatch hA
  | .lam ty b bi, d, acc, e', acc', locals, as1, as2, A, Bv, hab, hpre, hwf, hl, h1, h2, hloc, hlf,
      hty, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
    obtain ⟨⟨ty', acc1⟩, hty', ⟨b', acc2⟩, hb', hab⟩ := hab
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    obtain ⟨p1, w1⟩ := targetAbstract_acc d ty acc ty' acc1 hty'
    obtain ⟨p2, -⟩ := targetAbstract_acc (d + 1) b acc1 b' acc2 hb'
    have hlt : ∀ l ∈ ty.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    have hlb : ∀ l ∈ b.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    rw [Expr.instantiateList, denoteMeta_lam] at hA hB
    obtain ⟨ta, hta, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨ba, hba, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨tb, htb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain ⟨bb, hbb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain rfl : A = .lam (pwBit φ bi.pw) ta ba := (Option.some.inj hA).symm
    obtain rfl : Bv = .lam (pwBit φ bi.pw) tb bb := (Option.some.inj hB).symm
    rw [← Expr.instantiateList_cons] at hba hbb
    rw [Expr.instantiateList] at hty
    have hrecT := interp_targetAbstract hacl hih hcall ty d acc ty' acc1 locals as1 as2 ta tb
      hty' (p2.trans hpre) hwf hlt h1 h2 hloc hlf hty.lamDom hta htb
    rw [interp_lam, interp_lam, hrecT]
    refine lamR_congr fun x hxA => ?_
    rw [show B + d + 1 = B + (d + 1) from by omega] at hba
    rw [show B + ihsF.size + d + 1 = B + ihsF.size + (d + 1) from by omega] at hbb
    have := interp_targetAbstract hacl hih hcall b (d + 1) acc1 b' acc2 (locals ++ [x])
      (Expr.fvar (B + d) (ty.instantiateList as1 0) :: as1)
      (Expr.fvar (B + ihsF.size + d) (ty'.instantiateList as2 0) :: as2) ba bb
      hb' hpre (w1 hwf) hlb (h1.cons _) (h2.cons _) (by simp [hloc])
      (by rw [← hloc] at hta ⊢
          exact hlf.cons hta (hrecT ▸ hxA))
      (by rw [show B + ihsF.size + (d + 1) = B + ihsF.size + d + 1 from by omega,
            Expr.instantiateList_cons]
          exact hty.lamBody)
      hba hbb
    rwa [consList_append, consList_append] at this
  | .forallE ty b bi, d, acc, e', acc', locals, as1, as2, A, Bv, hab, hpre, hwf, hl, h1, h2, hloc,
      hlf, hty, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
    obtain ⟨⟨ty', acc1⟩, hty', ⟨b', acc2⟩, hb', hab⟩ := hab
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    obtain ⟨p1, w1⟩ := targetAbstract_acc d ty acc ty' acc1 hty'
    obtain ⟨p2, -⟩ := targetAbstract_acc (d + 1) b acc1 b' acc2 hb'
    have hlt : ∀ l ∈ ty.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    have hlb : ∀ l ∈ b.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    rw [Expr.instantiateList, denoteMeta_forallE] at hA hB
    obtain ⟨ta, hta, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨ba, hba, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨tb, htb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain ⟨bb, hbb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain rfl : A = .pi 0 (pwBit φ bi.pw) ta ba := (Option.some.inj hA).symm
    obtain rfl : Bv = .pi 0 (pwBit φ bi.pw) tb bb := (Option.some.inj hB).symm
    rw [← Expr.instantiateList_cons] at hba hbb
    rw [Expr.instantiateList] at hty
    have hrecT := interp_targetAbstract hacl hih hcall ty d acc ty' acc1 locals as1 as2 ta tb
      hty' (p2.trans hpre) hwf hlt h1 h2 hloc hlf hty.piDom hta htb
    rw [interp_pi, interp_pi, hrecT]
    refine piR_congr fun x hxA => ?_
    rw [show B + d + 1 = B + (d + 1) from by omega] at hba
    rw [show B + ihsF.size + d + 1 = B + ihsF.size + (d + 1) from by omega] at hbb
    have := interp_targetAbstract hacl hih hcall b (d + 1) acc1 b' acc2 (locals ++ [x])
      (Expr.fvar (B + d) (ty.instantiateList as1 0) :: as1)
      (Expr.fvar (B + ihsF.size + d) (ty'.instantiateList as2 0) :: as2) ba bb
      hb' hpre (w1 hwf) hlb (h1.cons _) (h2.cons _) (by simp [hloc])
      (by rw [← hloc] at hta ⊢
          exact hlf.cons hta (hrecT ▸ hxA))
      (by rw [show B + ihsF.size + (d + 1) = B + ihsF.size + d + 1 from by omega,
            Expr.instantiateList_cons]
          exact hty.piBody)
      hba hbb
    rwa [consList_append, consList_append] at this
  | .app f a, d, acc, e', acc', locals, as1, as2, A, Bv, hab, hpre, hwf, hl, h1, h2, hloc, hlf,
      hty, hA, hB => by
    simp only [ConLeche.targetAbstract] at hab
    split at hab
    · next i c m idx hc =>
      obtain ⟨hmd, -⟩ := targetCall?_spec hc
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
      obtain ⟨ty, hty0, hab⟩ := hab
      split at hab
      · next r hr =>
        simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
        obtain ⟨rfl, rfl⟩ := hab
        obtain ⟨hrlt, hpr, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hr
        simp only [Bool.and_eq_true, beq_iff_eq] at hpr
        obtain ⟨⟨hfi, hca⟩, hid⟩ := hpr
        have hget : ihsF[r]? = some acc[r] := prefix_getElem? hpre hrlt
        have hrn : r < ihsF.size := (List.getElem?_eq_some_iff.mp
          (by simpa using hget)).1
        have hfv : (acc.getD r default).fv = .fvar (B + r) acc[r].ty := by
          rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hrlt, Option.getD_some]
          exact hwf r hrlt
        rw [hfv] at hty hB
        rw [hcall d locals (.app f a) i c m idx r acc[r] as1 as2 A hc hget hfi hca hid hl h1 h2
          hloc hlf hty hA]
        exact (interp_ihApp h2 hmd hrn hloc hih hB).symm
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
        obtain ⟨rfl, rfl⟩ := hab
        have hget : ihsF[acc.size]? = some ⟨i, c, idx, ty, .fvar (B + acc.size) ty⟩ := by
          have := prefix_getElem? hpre (r := acc.size) (by simp)
          simpa using this
        have hrn : acc.size < ihsF.size := (List.getElem?_eq_some_iff.mp
          (by simpa using hget)).1
        rw [hcall d locals (.app f a) i c m idx acc.size _ as1 as2 A hc hget rfl rfl rfl hl h1
          h2 hloc hlf hty hA]
        exact (interp_ihApp h2 hmd hrn hloc hih hB).symm
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
      obtain ⟨⟨f', acc1⟩, hf', ⟨a', acc2⟩, ha', hab⟩ := hab
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      obtain ⟨p1, w1⟩ := targetAbstract_acc d f acc f' acc1 hf'
      obtain ⟨p2, -⟩ := targetAbstract_acc d a acc1 a' acc2 ha'
      have hlf' : ∀ l ∈ f.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
      have hla : ∀ l ∈ a.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
      rw [Expr.instantiateList, denoteMeta_app] at hA hB
      obtain ⟨fa, hfa, hA⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨aa, haa, hA⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨fb, hfb, hB⟩ := Option.bind_eq_some_iff.mp hB
      obtain ⟨ab, hab', hB⟩ := Option.bind_eq_some_iff.mp hB
      obtain rfl : A = .app fa aa := (Option.some.inj hA).symm
      obtain rfl : Bv = .app fb ab := (Option.some.inj hB).symm
      rw [Expr.instantiateList] at hty
      rw [interp_app, interp_app,
        interp_targetAbstract hacl hih hcall f d acc f' acc1 locals as1 as2 fa fb hf'
          (p2.trans hpre) hwf hlf' h1 h2 hloc hlf hty.appFn hfa hfb,
        interp_targetAbstract hacl hih hcall a d acc1 a' acc2 locals as1 as2 aa ab ha'
          hpre (w1 hwf) hla h1 h2 hloc hlf hty.appArg haa hab']

end Walk

end ConLeche.Model
