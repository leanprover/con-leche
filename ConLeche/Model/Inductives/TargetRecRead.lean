module

import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Rules.Sound
public import ConLeche.Model.Inductives.BlockRecRule
public import ConLeche.Model.Annot.LocList
import ConLeche.Kernel.Inductives.RecCheck

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

/-- The accumulator's entries are the frame's `ih` variables in order:
entry `r` is `fvar (B + r)` at its own type, and that type is the
call's `ih` type (`targetIhTy`, at the field's telescope width). -/
@[expose] def TargetIhWF (fr : ConLeche.TargetFrame) (B : Nat) (acc : Array ConLeche.TargetIh) :
    Prop :=
  ∀ (r : Nat) (h : r < acc.size), acc[r].fv = .fvar (B + r) acc[r].ty ∧
    ConLeche.targetIhTy fr acc[r].field acc[r].callee (fr.teles.getD acc[r].field []).length
      acc[r].idx = some acc[r].ty

/-- **The walk only appends**, and keeps the entries' shape. -/
theorem targetAbstract_acc {fr : ConLeche.TargetFrame} {B : Nat} :
    ∀ (d : Nat) (e : Expr) (acc : Array ConLeche.TargetIh) (e' : Expr)
      (acc' : Array ConLeche.TargetIh),
      ConLeche.targetAbstract fr B d e acc = some (e', acc') →
      acc.toList <+: acc'.toList ∧ (TargetIhWF fr B acc → TargetIhWF fr B acc')
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
  | d, .lam ty b bi, acc, _, _, h | d, .forallE ty b bi, acc, _, _, h => by
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
          obtain ⟨-, hm⟩ := targetCall?_spec hc
          subst hm
          exact ⟨rfl, hty⟩
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

/-! ## Opening by a list of free variables

The residue's nodes carry free variables of their own — the frame's and
the `ih` variables.  These are the opening lemmas for an opening list
whose entries are all free variables (`LocList`'s). -/

/-- Every entry is a free variable. -/
@[expose] def AllFvars (xs : List Expr) : Prop :=
  ∀ x ∈ xs, ∃ (i : Nat) (ty : Expr), x = .fvar i ty

theorem LocList.allFvars {B d : Nat} {xs : List Expr} (h : LocList B d xs) : AllFvars xs := by
  intro x hx
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
  have hjd : j < d := by rw [← h.1]; exact (List.getElem?_eq_some_iff.mp hj).1
  obtain ⟨ty, hty⟩ := h.2 j hjd
  exact ⟨_, ty, Option.some.inj (hj.symm.trans hty)⟩

/-- Opening draws every leaf from the term or from an opener. -/
theorem fvarLeaves_instantiateList_allFvars {xs : List Expr} (h : AllFvars xs) :
    ∀ (e : Expr) (k : Nat), ∀ l ∈ (e.instantiateList xs k).fvarLeaves,
      l ∈ e.fvarLeaves ∨ ∃ x ∈ xs, l ∈ x.fvarLeaves := by
  intro e
  induction e with
  | bvar j =>
    intro k l hl
    rw [Expr.instantiateList] at hl
    by_cases hjk : j < k
    · rw [if_pos hjk] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
    rw [if_neg hjk] at hl
    by_cases hin : j - k < xs.length
    · rw [dif_pos hin] at hl
      obtain ⟨i, ty, hx⟩ := h _ (List.getElem_mem hin)
      refine Or.inr ⟨xs[j - k], List.getElem_mem hin, ?_⟩
      rw [hx] at hl ⊢
      rw [Expr.instantiateList] at hl
      exact hl
    · rw [dif_neg hin] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
  | fvar i ty =>
    intro k l hl
    rw [Expr.instantiateList] at hl
    exact Or.inl hl
  | sort _ =>
    intro k l hl
    rw [Expr.instantiateList] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
  | const _ _ =>
    intro k l hl
    rw [Expr.instantiateList] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
  | lit _ =>
    intro k l hl
    rw [Expr.instantiateList] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
  | app f a ihf iha =>
    intro k l hl
    rw [Expr.instantiateList, Expr.fvarLeaves, List.mem_append] at hl
    rw [Expr.fvarLeaves, List.mem_append]
    rcases hl with hl | hl
    · exact (ihf k l hl).imp_left Or.inl
    · exact (iha k l hl).imp_left Or.inr
  | lam ty b bi ihty ihb =>
    intro k l hl
    rw [Expr.instantiateList, Expr.fvarLeaves, List.mem_append] at hl
    rw [Expr.fvarLeaves, List.mem_append]
    rcases hl with hl | hl
    · exact (ihty k l hl).imp_left Or.inl
    · exact (ihb (k + 1) l hl).imp_left Or.inr
  | forallE ty b bi ihty ihb =>
    intro k l hl
    rw [Expr.instantiateList, Expr.fvarLeaves, List.mem_append] at hl
    rw [Expr.fvarLeaves, List.mem_append]
    rcases hl with hl | hl
    · exact (ihty k l hl).imp_left Or.inl
    · exact (ihb (k + 1) l hl).imp_left Or.inr
  | letE ty v b ihty ihv ihb =>
    intro k l hl
    rw [Expr.instantiateList, Expr.fvarLeaves, List.mem_append, List.mem_append] at hl
    rw [Expr.fvarLeaves, List.mem_append, List.mem_append]
    rcases hl with (hl | hl) | hl
    · exact (ihty k l hl).imp_left (fun h => Or.inl (Or.inl h))
    · exact (ihv k l hl).imp_left (fun h => Or.inl (Or.inr h))
    · exact (ihb (k + 1) l hl).imp_left Or.inr
  | proj _ _ e ihe =>
    intro k l hl
    rw [Expr.instantiateList, Expr.fvarLeaves] at hl
    rw [Expr.fvarLeaves]
    exact ihe k l hl

/-- Opening by enough free variables closes the loose indices. -/
theorem looseBVarsBounded_instantiateList_allFvars {xs : List Expr} (h : AllFvars xs) :
    ∀ (e : Expr) (k : Nat), e.looseBVarsBounded (k + xs.length) = true →
      (e.instantiateList xs k).looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar j =>
    intro k hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb
    rw [Expr.instantiateList]
    by_cases hjk : j < k
    · rw [if_pos hjk]; simpa [Expr.looseBVarsBounded] using hjk
    rw [if_neg hjk, dif_pos (by omega)]
    obtain ⟨i, ty, hx⟩ := h _ (List.getElem_mem (show j - k < xs.length by omega))
    rw [hx, Expr.instantiateList]
    rfl
  | fvar _ _ => intro k _; rw [Expr.instantiateList]; rfl
  | sort _ => intro k _; rw [Expr.instantiateList]; rfl
  | const _ _ => intro k _; rw [Expr.instantiateList]; rfl
  | lit _ => intro k _; rw [Expr.instantiateList]; rfl
  | app f a ihf iha =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiateList, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihf k hb.1, iha k hb.2⟩
  | lam ty b bi ihty ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiateList, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihty k hb.1, ihb (k + 1) (by rw [show k + 1 + xs.length = k + xs.length + 1 by omega]; exact hb.2)⟩
  | forallE ty b bi ihty ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiateList, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨ihty k hb.1, ihb (k + 1) (by rw [show k + 1 + xs.length = k + xs.length + 1 by omega]; exact hb.2)⟩
  | letE ty v b ihty ihv ihb =>
    intro k hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    simp only [Expr.instantiateList, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨ihty k hb.1.1, ihv k hb.1.2⟩,
      ihb (k + 1) (by rw [show k + 1 + xs.length = k + xs.length + 1 by omega]; exact hb.2)⟩
  | proj _ _ e ihe =>
    intro k hb
    simp only [Expr.looseBVarsBounded] at hb
    simp only [Expr.instantiateList, Expr.looseBVarsBounded]
    exact ihe k hb

/-- Opening by bounded free variables keeps a bounded term bounded. -/
theorem constsBound_instantiateList_allFvars {envT : Env} {xs : List Expr} (h : AllFvars xs)
    (hxs : ∀ x ∈ xs, ConstsBound envT x) :
    ∀ (e : Expr) (k : Nat), ConstsBound envT e → ConstsBound envT (e.instantiateList xs k) := by
  intro e
  induction e with
  | bvar j =>
    intro k _
    rw [Expr.instantiateList]
    by_cases hjk : j < k
    · rw [if_pos hjk]; simp
    rw [if_neg hjk]
    by_cases hin : j - k < xs.length
    · rw [dif_pos hin]
      obtain ⟨i, ty, hx⟩ := h _ (List.getElem_mem hin)
      have hcb := hxs _ (List.getElem_mem hin)
      rw [hx] at hcb ⊢
      rw [Expr.instantiateList]
      exact hcb
    · rw [dif_neg hin]; simp
  | fvar _ _ => intro k hc; rw [Expr.instantiateList]; exact hc
  | sort _ => intro k _; simp [Expr.instantiateList]
  | const _ _ => intro k hc; rw [Expr.instantiateList]; exact hc
  | lit _ => intro k _; simp [Expr.instantiateList]
  | app f a ihf iha =>
    intro k hc
    rw [constsBound_app] at hc
    simp only [Expr.instantiateList, constsBound_app]
    exact ⟨ihf k hc.1, iha k hc.2⟩
  | lam ty b bi ihty ihb =>
    intro k hc
    rw [constsBound_lam] at hc
    simp only [Expr.instantiateList, constsBound_lam]
    exact ⟨ihty k hc.1, ihb (k + 1) hc.2⟩
  | forallE ty b bi ihty ihb =>
    intro k hc
    rw [constsBound_forallE] at hc
    simp only [Expr.instantiateList, constsBound_forallE]
    exact ⟨ihty k hc.1, ihb (k + 1) hc.2⟩
  | letE ty v b ihty ihv ihb =>
    intro k hc
    rw [constsBound_letE] at hc
    simp only [Expr.instantiateList, constsBound_letE]
    exact ⟨ihty k hc.1, ihv k hc.2.1, ihb (k + 1) hc.2.2⟩
  | proj _ _ e ihe =>
    intro k hc
    rw [constsBound_proj] at hc
    simp only [Expr.instantiateList, constsBound_proj]
    exact ihe k hc

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

/-- The context extended by a domain that carries free variables. -/
theorem WalkCtx.consOpenL {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D : Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {ρfull : Nat → V} {Δa : List AnnotTerm} {L : List Expr}
    (h2 : FvarList D L) (h : WalkCtx V mT φ D ρfull Δa L)
    {E : Expr} {tb : AnnotTerm} {x : V}
    (hcll : ∀ l ∈ E.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hlbb : E.looseBVarsBounded 0 = true) (hcb : ConstsBound envT E)
    (htb : denoteMeta mT.acval envT φ D E = some tb) (hty : IhTyped envT D E)
    (hx : x ∈ˢ interp V ρfull tb) :
    WalkCtx V mT φ (D + 1) (ConLeche.Semantics.cons x ρfull) (tb :: Δa) (Expr.fvar D E :: L) := by
  obtain ⟨-, -, hG⟩ := WalkCtx.subjOkL hacl hin h2 h hcll hlbb htb hty
  exact h.cons htb hlbb hcb hcll hG hx

/-- **An opened residue node is a subject of the walk's context**: its
leaves are the frame's or the opened locals', it is bvar-closed, and
it is bounded by `envT`. -/
theorem openedOk {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D Bn d : Nat}
    {ρfull : Nat → V} {Δa : List AnnotTerm} {as2 frameIh : List Expr}
    (h2 : LocList Bn d as2) (hW : WalkCtx V mT φ D ρfull Δa (as2 ++ frameIh))
    {e' : Expr} (hlL : ∀ l ∈ e'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh)
    (hbT : e'.looseBVarsBounded d = true) (hcbe : ConstsBound envT e') :
    (∀ l ∈ (e'.instantiateList as2 0).fvarLeaves, Expr.fvar l.1 l.2 ∈ as2 ++ frameIh) ∧
      (e'.instantiateList as2 0).looseBVarsBounded 0 = true ∧
      ConstsBound envT (e'.instantiateList as2 0) := by
  have hall := h2.allFvars
  refine ⟨fun l hl => ?_, ?_, ?_⟩
  · rcases fvarLeaves_instantiateList_allFvars hall e' 0 l hl with h | ⟨x, hx, hlx⟩
    · exact List.mem_append_right _ (hlL l h)
    · obtain ⟨i, ty, rfl⟩ := hall x hx
      simp only [Expr.fvarLeaves, List.mem_cons] at hlx
      rcases hlx with rfl | hlx
      · exact List.mem_append_left _ hx
      · exact hW.2.2.2.2.2.2 _ (List.mem_append_left _ hx) l hlx
  · exact looseBVarsBounded_instantiateList_allFvars hall e' 0 (by rw [h2.1]; simpa using hbT)
  · exact constsBound_instantiateList_allFvars hall
      (fun x hx => hW.2.2.2.2.2.1 x (List.mem_append_left _ hx)) e' 0 hcbe

end Ctx

/-! ## The walk, read -/

section Walk

variable {V : Type uv} [SetTheory V]

/-- An entry of a prefix of the final accumulator is the final entry. -/
theorem prefix_getElem? {acc ihsF : Array ConLeche.TargetIh} (hp : acc.toList <+: ihsF.toList)
    {r : Nat} (hr : r < acc.size) : ihsF[r]? = some acc[r] := by
  obtain ⟨t, ht⟩ := hp
  have h1 : ihsF[r]? = ihsF.toList[r]? := by simp
  rw [h1, ← ht, List.getElem?_append_left (by simpa using hr)]
  simp

/-- **The call node's value, as a premise**: at a node `targetCall?`
recognises as the call `(i, c, m, idx)`, whose `ih` variable is entry
`r` of the rule's final accumulator, the STORED node reads to that
variable's value folded along the last `m` locals.  The walk hands
over everything it knows at the node: the local fit, the walk's
context over the frame `frameIh` and the residue node's typing — the
`ih` term's fold needs the call's arguments to FIT its telescope,
which is the residue node's typing read in that context. -/
@[expose] def TargetNodeVal (V : Type uv) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat) {envT : Env}
    (mT : EnvModel V envT) (fr : ConLeche.TargetFrame) (B : Nat)
    (ihsF : Array ConLeche.TargetIh) (frameIh : List Expr) (ρ' : Nat → V) (ihvals : List V) :
    Prop :=
  ∀ (d : Nat) (locals : List V) (e : Expr) (i c m : Nat) (idx : List Expr) (r : Nat)
    (ih : ConLeche.TargetIh) (as1 as2 : List Expr) (Δa : List AnnotTerm) (A : AnnotTerm),
    ConLeche.targetCall? fr d e = some (i, c, m, idx) →
    ihsF[r]? = some ih → ih.field = i → ih.callee = c → ih.idx = idx →
    (∀ l ∈ e.fvarLeaves, l.1 < B) →
    LocList B d as1 → LocList (B + ihsF.size) d as2 →
    FvarList (B + ihsF.size + d) (as2 ++ frameIh) → locals.length = d →
    LocalsFit V acval env φ B ρ' locals as1 →
    WalkCtx V mT φ (B + ihsF.size + d) (consList locals (consList ihvals ρ')) Δa
      (as2 ++ frameIh) →
    IhTyped envT (B + ihsF.size + d)
      ((Expr.mkAppN (.fvar (B + r) ih.ty) (ConLeche.structTeleVars m)).instantiateList as2 0) →
    denoteMeta acval env φ (B + d) (e.instantiateList as1 0) = some A →
    interp V (consList locals ρ') A
      = (locals.drop (d - m)).foldl SetTheory.app (ihvals.getD r pt)

/-- One binder deeper: the three lists and the context, extended by the
binder's opened domains. -/
theorem walk_open_step {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}
    (haclT : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {B n d : Nat} {as2 frameIh : List Expr}
    {ρfull : Nat → V} {Δa : List AnnotTerm}
    (h2 : LocList (B + n) d as2) (hL : FvarList (B + n + d) (as2 ++ frameIh))
    (hW : WalkCtx V mT φ (B + n + d) ρfull Δa (as2 ++ frameIh))
    {ty' : Expr} (hlL : ∀ l ∈ ty'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh)
    (hbT : ty'.looseBVarsBounded d = true) (hcbe : ConstsBound envT ty')
    {tb : AnnotTerm} (htb : denoteMeta mT.acval envT φ (B + n + d) (ty'.instantiateList as2 0)
      = some tb)
    (hty : IhTyped envT (B + n + d) (ty'.instantiateList as2 0)) {x : V}
    (hx : x ∈ˢ interp V ρfull tb) :
    LocList (B + n) (d + 1) (Expr.fvar (B + n + d) (ty'.instantiateList as2 0) :: as2) ∧
      FvarList (B + n + (d + 1))
        ((Expr.fvar (B + n + d) (ty'.instantiateList as2 0) :: as2) ++ frameIh) ∧
      WalkCtx V mT φ (B + n + (d + 1)) (ConLeche.Semantics.cons x ρfull) (tb :: Δa)
        ((Expr.fvar (B + n + d) (ty'.instantiateList as2 0) :: as2) ++ frameIh) := by
  obtain ⟨hcll, hlbb, hcb⟩ := openedOk h2 hW hlL hbT hcbe
  refine ⟨h2.cons _, ?_, ?_⟩
  · rw [show B + n + (d + 1) = B + n + d + 1 by omega]
    exact hL.cons _ (wscoped_of_leaves_mem hL _ hcll)
  · rw [show B + n + (d + 1) = B + n + d + 1 by omega]
    exact WalkCtx.consOpenL haclT hin hL hW hcll hlbb hcb htb hty hx

set_option maxHeartbeats 4000000 in
/-- **The abstraction, read**: the stored rule body,
read at the rule's frame, is the RESIDUE read at the frame extended by
the `ih` variables' values.  Structural over the body; every node the
walk did not replace is `interp_of_open_deepen`, and the one it did is
the premise `TargetNodeVal` against the residue node's own reading
(`interp_ihApp`).  The walk carries the residue's context
(`WalkCtx` over the opened locals above the frame `frameIh`), which is
what the premise's discharge reads the call's typing in. -/
theorem interp_targetAbstract
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {envT : Env} {mT : EnvModel V envT}
    (haclT : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    (hproj : ∀ (sn : Name) (i : Nat), envT.findProj? sn i = env.findProj? sn i)
    (hmono : ∀ (D : Nat) (y : Expr) (ya : AnnotTerm), ConstsBound envT y →
      denoteMeta mT.acval envT φ D y = some ya → denoteMeta acval env φ D y = some ya)
    {fr : ConLeche.TargetFrame} {B : Nat} {ihsF : Array ConLeche.TargetIh}
    {frameIh : List Expr} {ρ' : Nat → V} {ihvals : List V} (hih : ihvals.length = ihsF.size)
    (hcall : TargetNodeVal V acval env φ mT fr B ihsF frameIh ρ' ihvals) :
    ∀ (e : Expr) (d : Nat) (acc : Array ConLeche.TargetIh) (e' : Expr)
      (acc' : Array ConLeche.TargetIh) (locals : List V) (as1 as2 : List Expr)
      (Δa : List AnnotTerm) (A Bv : AnnotTerm),
      ConLeche.targetAbstract fr B d e acc = some (e', acc') →
      acc'.toList <+: ihsF.toList → TargetIhWF fr B acc →
      (∀ l ∈ e.fvarLeaves, l.1 < B) →
      (∀ l ∈ e'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh) →
      e'.looseBVarsBounded d = true → ConstsBound envT e' →
      LocList B d as1 → LocList (B + ihsF.size) d as2 →
      FvarList (B + ihsF.size + d) (as2 ++ frameIh) → locals.length = d →
      LocalsFit V acval env φ B ρ' locals as1 →
      WalkCtx V mT φ (B + ihsF.size + d) (consList locals (consList ihvals ρ')) Δa
        (as2 ++ frameIh) →
      IhTyped envT (B + ihsF.size + d) (e'.instantiateList as2 0) →
      denoteMeta acval env φ (B + d) (e.instantiateList as1 0) = some A →
      denoteMeta mT.acval envT φ (B + ihsF.size + d) (e'.instantiateList as2 0) = some Bv →
      interp V (consList locals ρ') A = interp V (consList locals (consList ihvals ρ')) Bv
  | .bvar j, d, acc, e', acc', locals, as1, as2, Δa, A, Bv, hab, _, _, hl, hlL, hbT, hcbe, h1,
      h2, _, hloc, _, hW, _, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, -⟩ := hab
    exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA
      (hmono _ _ _ (openedOk h2 hW hlL hbT hcbe).2.2 hB)
  | .sort u, d, acc, e', acc', locals, as1, as2, Δa, A, Bv, hab, _, _, hl, hlL, hbT, hcbe, h1,
      h2, _, hloc, _, hW, _, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, -⟩ := hab
    exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA
      (hmono _ _ _ (openedOk h2 hW hlL hbT hcbe).2.2 hB)
  | .lit l, d, acc, e', acc', locals, as1, as2, Δa, A, Bv, hab, _, _, hl, hlL, hbT, hcbe, h1,
      h2, _, hloc, _, hW, _, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, -⟩ := hab
    exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA
      (hmono _ _ _ (openedOk h2 hW hlL hbT hcbe).2.2 hB)
  | .fvar i ty, d, acc, e', acc', locals, as1, as2, Δa, A, Bv, hab, _, _, hl, hlL, hbT, hcbe, h1,
      h2, _, hloc, _, hW, _, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, -⟩ := hab
    exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA
      (hmono _ _ _ (openedOk h2 hW hlL hbT hcbe).2.2 hB)
  | .const n us, d, acc, e', acc', locals, as1, as2, Δa, A, Bv, hab, _, _, hl, hlL, hbT, hcbe, h1,
      h2, _, hloc, _, hW, _, hA, hB => by
    simp only [ConLeche.targetAbstract] at hab
    split at hab
    · exact nomatch hab
    · simp only [Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, -⟩ := hab
      exact interp_of_open_deepen hacl hl h1 h2 hloc hih hA
        (hmono _ _ _ (openedOk h2 hW hlL hbT hcbe).2.2 hB)
  | .letE ty v b, d, _, _, _, _, as1, _, _, A, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hA,
      _ => by
    rw [Expr.instantiateList, denoteMeta] at hA
    exact nomatch hA
  | .proj sn i x, d, acc, e', acc', locals, as1, as2, Δa, A, Bv, hab, hpre, hwf, hl, hlL, hbT,
      hcbe, h1, h2, hL, hloc, hlf, hW, hty, hA, hB => by
    simp only [ConLeche.targetAbstract] at hab
    split at hab
    · exact nomatch hab
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
    obtain ⟨⟨x', acc1⟩, hx, hab⟩ := hab
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    have hlx : ∀ l ∈ x.fvarLeaves, l.1 < B := fun l h => hl l (by simpa [Expr.fvarLeaves] using h)
    have hlLx : ∀ l ∈ x'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh :=
      fun l h => hlL l (by simpa [Expr.fvarLeaves] using h)
    simp only [Expr.looseBVarsBounded] at hbT
    rw [constsBound_proj] at hcbe
    rw [Expr.instantiateList] at hty
    rw [Expr.instantiateList, denoteMeta_proj] at hA hB
    obtain ⟨ea, hea, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨eb, heb, hB⟩ := Option.bind_eq_some_iff.mp hB
    have hrec := interp_targetAbstract hacl haclT hin hproj hmono hih hcall x d acc x' acc1 locals
      as1 as2 Δa ea eb hx hpre hwf hlx hlLx hbT hcbe h1 h2 hL hloc hlf hW hty.projArg hea heb
    rw [hproj sn i] at hB
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
  | .lam ty b bi, d, acc, e', acc', locals, as1, as2, Δa, A, Bv, hab, hpre, hwf, hl, hlL, hbT,
      hcbe, h1, h2, hL, hloc, hlf, hW, hty, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
    obtain ⟨⟨ty', acc1⟩, hty', ⟨b', acc2⟩, hb', hab⟩ := hab
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    obtain ⟨p1, w1⟩ := targetAbstract_acc d ty acc ty' acc1 hty'
    obtain ⟨p2, -⟩ := targetAbstract_acc (d + 1) b acc1 b' acc2 hb'
    have hlt : ∀ l ∈ ty.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    have hlb : ∀ l ∈ b.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    have hlLt : ∀ l ∈ ty'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh :=
      fun l h => hlL l (by simp [Expr.fvarLeaves, h])
    have hlLb : ∀ l ∈ b'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh :=
      fun l h => hlL l (by simp [Expr.fvarLeaves, h])
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbT
    rw [constsBound_lam] at hcbe
    rw [Expr.instantiateList, denoteMeta_lam] at hA hB
    obtain ⟨ta, hta, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨ba, hba, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨tb, htb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain ⟨bb, hbb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain rfl : A = .lam (pwBit φ bi.pw) ta ba := (Option.some.inj hA).symm
    obtain rfl : Bv = .lam (pwBit φ bi.pw) tb bb := (Option.some.inj hB).symm
    rw [← Expr.instantiateList_cons] at hba hbb
    rw [Expr.instantiateList] at hty
    have hrecT := interp_targetAbstract hacl haclT hin hproj hmono hih hcall ty d acc ty' acc1
      locals as1 as2 Δa ta tb hty' (p2.trans hpre) hwf hlt hlLt hbT.1 hcbe.1 h1 h2 hL hloc hlf
      hW hty.lamDom hta htb
    rw [interp_lam, interp_lam, hrecT]
    refine lamR_congr fun x hxA => ?_
    rw [show B + d + 1 = B + (d + 1) from by omega] at hba
    rw [show B + ihsF.size + d + 1 = B + ihsF.size + (d + 1) from by omega] at hbb
    obtain ⟨h2', hL', hW'⟩ := walk_open_step haclT hin h2 hL hW hlLt hbT.1 hcbe.1 htb
      hty.lamDom hxA
    have := interp_targetAbstract hacl haclT hin hproj hmono hih hcall b (d + 1) acc1 b' acc2
      (locals ++ [x])
      (Expr.fvar (B + d) (ty.instantiateList as1 0) :: as1)
      (Expr.fvar (B + ihsF.size + d) (ty'.instantiateList as2 0) :: as2) (tb :: Δa) ba bb
      hb' hpre (w1 hwf) hlb hlLb hbT.2 hcbe.2 (h1.cons _) h2' hL' (by simp [hloc])
      (by rw [← hloc] at hta ⊢
          exact hlf.cons hta (hrecT ▸ hxA))
      (by rw [consList_append, consList_cons, consList_nil]; exact hW')
      (by rw [show B + ihsF.size + (d + 1) = B + ihsF.size + d + 1 from by omega,
            Expr.instantiateList_cons]
          exact hty.lamBody)
      hba hbb
    rwa [consList_append, consList_append] at this
  | .forallE ty b bi, d, acc, e', acc', locals, as1, as2, Δa, A, Bv, hab, hpre, hwf, hl, hlL, hbT,
      hcbe, h1, h2, hL, hloc, hlf, hW, hty, hA, hB => by
    simp only [ConLeche.targetAbstract, Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
    obtain ⟨⟨ty', acc1⟩, hty', ⟨b', acc2⟩, hb', hab⟩ := hab
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
    obtain ⟨rfl, rfl⟩ := hab
    obtain ⟨p1, w1⟩ := targetAbstract_acc d ty acc ty' acc1 hty'
    obtain ⟨p2, -⟩ := targetAbstract_acc (d + 1) b acc1 b' acc2 hb'
    have hlt : ∀ l ∈ ty.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    have hlb : ∀ l ∈ b.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
    have hlLt : ∀ l ∈ ty'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh :=
      fun l h => hlL l (by simp [Expr.fvarLeaves, h])
    have hlLb : ∀ l ∈ b'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh :=
      fun l h => hlL l (by simp [Expr.fvarLeaves, h])
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbT
    rw [constsBound_forallE] at hcbe
    rw [Expr.instantiateList, denoteMeta_forallE] at hA hB
    obtain ⟨ta, hta, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨ba, hba, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨tb, htb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain ⟨bb, hbb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain rfl : A = .pi 0 (pwBit φ bi.pw) ta ba := (Option.some.inj hA).symm
    obtain rfl : Bv = .pi 0 (pwBit φ bi.pw) tb bb := (Option.some.inj hB).symm
    rw [← Expr.instantiateList_cons] at hba hbb
    rw [Expr.instantiateList] at hty
    have hrecT := interp_targetAbstract hacl haclT hin hproj hmono hih hcall ty d acc ty' acc1
      locals as1 as2 Δa ta tb hty' (p2.trans hpre) hwf hlt hlLt hbT.1 hcbe.1 h1 h2 hL hloc hlf
      hW hty.piDom hta htb
    rw [interp_pi, interp_pi, hrecT]
    refine piR_congr fun x hxA => ?_
    rw [show B + d + 1 = B + (d + 1) from by omega] at hba
    rw [show B + ihsF.size + d + 1 = B + ihsF.size + (d + 1) from by omega] at hbb
    obtain ⟨h2', hL', hW'⟩ := walk_open_step haclT hin h2 hL hW hlLt hbT.1 hcbe.1 htb
      hty.piDom hxA
    have := interp_targetAbstract hacl haclT hin hproj hmono hih hcall b (d + 1) acc1 b' acc2
      (locals ++ [x])
      (Expr.fvar (B + d) (ty.instantiateList as1 0) :: as1)
      (Expr.fvar (B + ihsF.size + d) (ty'.instantiateList as2 0) :: as2) (tb :: Δa) ba bb
      hb' hpre (w1 hwf) hlb hlLb hbT.2 hcbe.2 (h1.cons _) h2' hL' (by simp [hloc])
      (by rw [← hloc] at hta ⊢
          exact hlf.cons hta (hrecT ▸ hxA))
      (by rw [consList_append, consList_cons, consList_nil]; exact hW')
      (by rw [show B + ihsF.size + (d + 1) = B + ihsF.size + d + 1 from by omega,
            Expr.instantiateList_cons]
          exact hty.piBody)
      hba hbb
    rwa [consList_append, consList_append] at this
  | .app f a, d, acc, e', acc', locals, as1, as2, Δa, A, Bv, hab, hpre, hwf, hl, hlL, hbT,
      hcbe, h1, h2, hL, hloc, hlf, hW, hty, hA, hB => by
    simp only [ConLeche.targetAbstract] at hab
    split at hab
    · next i c m idx hc =>
      obtain ⟨hmd, -⟩ := targetCall?_spec hc
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
      obtain ⟨ty, hty0, hab⟩ := hab
      have hB' := hmono _ _ _ (openedOk h2 hW hlL hbT hcbe).2.2 hB
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
          exact (hwf r hrlt).1
        rw [hfv] at hty hB'
        rw [hcall d locals (.app f a) i c m idx r acc[r] as1 as2 Δa A hc hget hfi hca hid hl h1
          h2 hL hloc hlf hW hty hA]
        exact (interp_ihApp h2 hmd hrn hloc hih hB').symm
      · simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
        obtain ⟨rfl, rfl⟩ := hab
        have hget : ihsF[acc.size]? = some ⟨i, c, idx, ty, .fvar (B + acc.size) ty⟩ := by
          have := prefix_getElem? hpre (r := acc.size) (by simp)
          simpa using this
        have hrn : acc.size < ihsF.size := (List.getElem?_eq_some_iff.mp
          (by simpa using hget)).1
        rw [hcall d locals (.app f a) i c m idx acc.size _ as1 as2 Δa A hc hget rfl rfl rfl hl h1
          h2 hL hloc hlf hW hty hA]
        exact (interp_ihApp h2 hmd hrn hloc hih hB').symm
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hab
      obtain ⟨⟨f', acc1⟩, hf', ⟨a', acc2⟩, ha', hab⟩ := hab
      simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at hab
      obtain ⟨rfl, rfl⟩ := hab
      obtain ⟨p1, w1⟩ := targetAbstract_acc d f acc f' acc1 hf'
      obtain ⟨p2, -⟩ := targetAbstract_acc d a acc1 a' acc2 ha'
      have hlf' : ∀ l ∈ f.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
      have hla : ∀ l ∈ a.fvarLeaves, l.1 < B := fun l h => hl l (by simp [Expr.fvarLeaves, h])
      have hlLf : ∀ l ∈ f'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh :=
        fun l h => hlL l (by simp [Expr.fvarLeaves, h])
      have hlLa : ∀ l ∈ a'.fvarLeaves, Expr.fvar l.1 l.2 ∈ frameIh :=
        fun l h => hlL l (by simp [Expr.fvarLeaves, h])
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbT
      rw [constsBound_app] at hcbe
      rw [Expr.instantiateList, denoteMeta_app] at hA hB
      obtain ⟨fa, hfa, hA⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨aa, haa, hA⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨fb, hfb, hB⟩ := Option.bind_eq_some_iff.mp hB
      obtain ⟨ab, hab', hB⟩ := Option.bind_eq_some_iff.mp hB
      obtain rfl : A = .app fa aa := (Option.some.inj hA).symm
      obtain rfl : Bv = .app fb ab := (Option.some.inj hB).symm
      rw [Expr.instantiateList] at hty
      rw [interp_app, interp_app,
        interp_targetAbstract hacl haclT hin hproj hmono hih hcall f d acc f' acc1 locals as1 as2
          Δa fa fb hf' (p2.trans hpre) hwf hlf' hlLf hbT.1 hcbe.1 h1 h2 hL hloc hlf hW
          hty.appFn hfa hfb,
        interp_targetAbstract hacl haclT hin hproj hmono hih hcall a d acc1 a' acc2 locals as1
          as2 Δa aa ab ha' hpre (w1 hwf) hla hlLa hbT.2 hcbe.2 h1 h2 hL hloc hlf hW hty.appArg
          haa hab']

end Walk

end ConLeche.Model
