module

import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Rules.Sound
public import ConLeche.Model.Inductives.BlockRecRule
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

end Walk

end ConLeche.Model
