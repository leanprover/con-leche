module

import ConLeche.Model.Annot.Bit
import ConLeche.Model.Annot.BitLemmas
public import ConLeche.Semantics.Tower.BlockRecI
import ConLeche.Semantics.Kit
import ConLeche.Verify.Subst
public import ConLeche.Model.Inductives.FixRecRead
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.StructStageCtor
import ConLeche.Model.IndFrame
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Semantics.BasisOk
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Annot.BitInst

public section

/-!
# O-1: the abstraction's inverse, at the reading

`checkBlockRule` stores the ANNOTATED STREAM right-hand side and keeps
nothing of the abstraction; the model has to read the stored body and
recover the design's `Rb = Rb''[ih_i ↦ ihFun_i]`.  That is **O-1**,
and it is an `interp` equation, not a syntactic one: at a guarded call the abstraction
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

* `denoteMeta_open_liftLooseBVars` — the abstraction's NON-call
  cases, in one go: `abstractIh` on a recursor-free subterm IS
  `Expr.liftLooseBVars fr.nR d`, and the reading of a lifted term is the reading, lifted
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
  xs.length = E ∧ (∀ j, j < E → ∃ ty : Expr, xs[j]? = some (.fvar (E - 1 - j) ty)) ∧
    ∀ x ∈ xs, Expr.WScoped E x

theorem FvarList.cons {E : Nat} {xs : List Expr} (h : FvarList E xs) (ty : Expr)
    (hty : Expr.WScoped E ty) :
    FvarList (E + 1) (Expr.fvar E ty :: xs) := by
  refine ⟨by simp [h.1], fun j hj => ?_, fun x hx => ?_⟩
  · cases j with
    | zero => exact ⟨ty, by simp⟩
    | succ j =>
      obtain ⟨ty', hty'⟩ := h.2.1 j (by omega)
      refine ⟨ty', ?_⟩
      rw [show E + 1 - 1 - (j + 1) = E - 1 - j from by omega]
      simpa using hty'
  · rcases List.mem_cons.mp hx with rfl | hx'
    · simp only [Expr.WScoped]
      exact ⟨by omega, hty⟩
    · exact Expr.WScoped.mono (Nat.le_succ E) (h.2.2 x hx')

/-- Opening a loose variable that the frame covers. -/
theorem FvarList.bvar_lt {E j : Nat} {xs : List Expr} (h : FvarList E xs) (hj : j < E) :
    ∃ ty : Expr, (Expr.bvar j).instantiateList xs 0 = .fvar (E - 1 - j) ty := by
  obtain ⟨ty, hty⟩ := h.2.1 j hj
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

/-- **The opened term is well scoped**: the opening list's fvars are
below the frame and the term brought none of its own. -/
theorem wscoped_instantiateList {E : Nat} {xs : List Expr} (h : FvarList E xs) :
    ∀ (e : Expr), e.hasFvar = false → ∀ (k : Nat),
      Expr.WScoped E (e.instantiateList xs k) := by
  intro e
  induction e with
  | bvar j =>
    intro _ k
    rw [Expr.instantiateList]
    by_cases hjk : j < k
    · rw [if_pos hjk]
      exact Expr.WScoped.of_not_hasFvar (by simp [Expr.hasFvar])
    rw [if_neg hjk]
    by_cases hin : j - k < xs.length
    · rw [dif_pos hin]
      obtain ⟨ty, hty⟩ := h.2.1 (j - k) (by rw [h.1] at hin; omega)
      obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hty
      have hw := h.2.2 xs[j - k] (List.getElem_mem hin)
      rw [hget] at hw ⊢
      rw [Expr.instantiateList]
      exact hw
    · rw [dif_neg hin]
      exact Expr.WScoped.of_not_hasFvar (by simp [Expr.hasFvar])
  | fvar _ _ => intro hf _; exact absurd hf (by simp [Expr.hasFvar])
  | sort _ =>
    intro _ k; exact Expr.WScoped.of_not_hasFvar (by simp [Expr.hasFvar, Expr.instantiateList])
  | const _ _ =>
    intro _ k; exact Expr.WScoped.of_not_hasFvar (by simp [Expr.hasFvar, Expr.instantiateList])
  | lit _ =>
    intro _ k; exact Expr.WScoped.of_not_hasFvar (by simp [Expr.hasFvar, Expr.instantiateList])
  | app f a ihf iha =>
    intro hf k
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.instantiateList, Expr.WScoped]
    exact ⟨ihf hf.1 k, iha hf.2 k⟩
  | lam ty b bi ihty ihb =>
    intro hf k
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.instantiateList, Expr.WScoped]
    exact ⟨ihty hf.1 k, ihb hf.2 (k + 1)⟩
  | forallE ty b bi ihty ihb =>
    intro hf k
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.instantiateList, Expr.WScoped]
    exact ⟨ihty hf.1 k, ihb hf.2 (k + 1)⟩
  | letE ty v b ihty ihv ihb =>
    intro hf k
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.instantiateList, Expr.WScoped]
    exact ⟨ihty hf.1.1 k, ihv hf.1.2 k, ihb hf.2 (k + 1)⟩
  | proj _ _ e ihe =>
    intro hf k
    simp only [Expr.hasFvar] at hf
    simp only [Expr.instantiateList, Expr.WScoped]
    exact ihe hf k

/-- **Opening draws every free variable from the opening list.**  The
residue's sub-terms carry no `fvar` of their own (`abstractIh` cannot
introduce one), so every leaf the frame's reading sees belongs to an
opener — which is what puts a node of the walk in the frame's CONTEXT
(`CtxOk.of_subset`) and bounds its leaves (`LeavesBounded`).  The
companion of `wscoped_instantiateList`, proved the same way. -/
theorem fvarLeaves_instantiateList {E : Nat} {xs : List Expr} (h : FvarList E xs) :
    ∀ (e : Expr), e.hasFvar = false → ∀ (k : Nat),
      ∀ l ∈ (e.instantiateList xs k).fvarLeaves, ∃ x ∈ xs, l ∈ x.fvarLeaves := by
  intro e
  induction e with
  | bvar j =>
    intro _ k l hl
    rw [Expr.instantiateList] at hl
    by_cases hjk : j < k
    · rw [if_pos hjk] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
    rw [if_neg hjk] at hl
    by_cases hin : j - k < xs.length
    · rw [dif_pos hin] at hl
      obtain ⟨ty, hty⟩ := h.2.1 (j - k) (by rw [h.1] at hin; omega)
      obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hty
      refine ⟨xs[j - k], List.getElem_mem hin, ?_⟩
      rw [hget] at hl ⊢
      rw [Expr.instantiateList] at hl
      exact hl
    · rw [dif_neg hin] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
  | fvar _ _ => intro hf _; exact absurd hf (by simp [Expr.hasFvar])
  | sort _ =>
    intro _ k l hl
    rw [Expr.instantiateList] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
  | const _ _ =>
    intro _ k l hl
    rw [Expr.instantiateList] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
  | lit _ =>
    intro _ k l hl
    rw [Expr.instantiateList] at hl; exact absurd hl (by simp [Expr.fvarLeaves])
  | app f a ihf iha =>
    intro hf k l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [Expr.instantiateList, Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihf hf.1 k l hl
    · exact iha hf.2 k l hl
  | lam ty b bi ihty ihb =>
    intro hf k l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [Expr.instantiateList, Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hf.1 k l hl
    · exact ihb hf.2 (k + 1) l hl
  | forallE ty b bi ihty ihb =>
    intro hf k l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [Expr.instantiateList, Expr.fvarLeaves, List.mem_append] at hl
    rcases hl with hl | hl
    · exact ihty hf.1 k l hl
    · exact ihb hf.2 (k + 1) l hl
  | letE ty v b ihty ihv ihb =>
    intro hf k l hl
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [Expr.instantiateList, Expr.fvarLeaves, List.mem_append, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact ihty hf.1.1 k l hl
    · exact ihv hf.1.2 k l hl
    · exact ihb hf.2 (k + 1) l hl
  | proj _ _ e ihe =>
    intro hf k l hl
    simp only [Expr.hasFvar] at hf
    rw [Expr.instantiateList, Expr.fvarLeaves] at hl
    exact ihe hf k l hl

/-! ### Two syntactic facts about the call node

Neither is in `BlockRecInv.lean` (they are this consumer's, not the
stage's): the opener's POSITION is in range, and the call's arguments
are subterms of the node — so the rule body's `hasFvar = false` reaches
them. -/

/-- The opener's position is an index of the frame's keys. -/
theorem pairIdxOf?_lt {ps : List (Nat × Nat)} {p : Nat × Nat} {i : Nat}
    (h : ConLeche.pairIdxOf? ps p = some i) : i < ps.length :=
  List.mem_range.mp (List.mem_of_find?_eq_some h)

/-- **A found position names ONE pair**: two keys at the same opener
index are the same key. -/
theorem pairIdxOf?_inj {ps : List (Nat × Nat)} {p q : Nat × Nat} {i : Nat}
    (hp : ConLeche.pairIdxOf? ps p = some i) (hq : ConLeche.pairIdxOf? ps q = some i) :
    p = q := by
  have h1 : ps.getD i (0, 0) = p := by
    have := List.find?_some hp; simpa using this
  have h2 : ps.getD i (0, 0) = q := by
    have := List.find?_some hq; simpa using this
  exact h1.symm.trans h2

/-- A spine's arguments are subterms: no free variable in the node, no
free variable in an argument. -/
theorem hasFvar_of_mem_getAppArgs :
    ∀ {e : Expr}, e.hasFvar = false → ∀ a ∈ e.getAppArgs, a.hasFvar = false
  | .app f b, h, a, ha => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h
    rw [Expr.getAppArgs] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · exact hasFvar_of_mem_getAppArgs h.1 a ha'
    · rw [List.mem_singleton.mp ha']; exact h.2
  | .bvar _, _, a, ha | .sort _, _, a, ha | .lit _, _, a, ha | .const .., _, a, ha
  | .fvar .., _, a, ha | .lam .., _, a, ha | .forallE .., _, a, ha
  | .letE .., _, a, ha | .proj .., _, a, ha => absurd ha (by simp [Expr.getAppArgs])

/-- The bvar twin of `hasFvar_of_mem_getAppArgs`: a bounded spine's
arguments are bounded. -/
theorem bounded_of_mem_getAppArgs {k : Nat} :
    ∀ {e : Expr}, e.looseBVarsBounded k = true →
      ∀ a ∈ e.getAppArgs, a.looseBVarsBounded k = true
  | .app f b, h, a, ha => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    rw [Expr.getAppArgs] at ha
    rcases List.mem_append.mp ha with ha' | ha'
    · exact bounded_of_mem_getAppArgs h.1 a ha'
    · rw [List.mem_singleton.mp ha']; exact h.2
  | .bvar _, _, a, ha | .sort _, _, a, ha | .lit _, _, a, ha | .const .., _, a, ha
  | .fvar .., _, a, ha | .lam .., _, a, ha | .forallE .., _, a, ha
  | .letE .., _, a, ha | .proj .., _, a, ha => absurd ha (by simp [Expr.getAppArgs])

/-- **The call's arguments are the MAJOR's arguments**, and the major
is one of the node's (`IhCallRun.hmaj`/`hasMaj`). -/
theorem blockIhCall?_args_sub {fr : ConLeche.BlockRuleFrame} {d : Nat} {e : Expr}
    {r : Nat} {as : List Expr} (h : ConLeche.blockIhCall? fr d e = some (r, as)) :
    ∃ maj ∈ e.getAppArgs, as = maj.getAppArgs := by
  obtain ⟨C⟩ := ConLeche.blockIhCall?_run h
  exact ⟨C.maj, List.mem_of_getElem? C.hmaj, C.hasMaj⟩

theorem hasFvar_liftLooseBVars {n c : Nat} :
    ∀ {e : Expr}, (e.liftLooseBVars n c).hasFvar = e.hasFvar
  | .bvar _ => by rw [Expr.liftLooseBVars]; split <;> rfl
  | .sort _ | .const .. | .lit _ | .fvar .. => rfl
  | .app f a => by
    simp only [Expr.liftLooseBVars, Expr.hasFvar, hasFvar_liftLooseBVars (e := f),
      hasFvar_liftLooseBVars (e := a)]
  | .lam ty b bi | .forallE ty b bi => by
    simp only [Expr.liftLooseBVars, Expr.hasFvar, hasFvar_liftLooseBVars (e := ty),
      hasFvar_liftLooseBVars (e := b)]
  | .letE ty v b => by
    simp only [Expr.liftLooseBVars, Expr.hasFvar, hasFvar_liftLooseBVars (e := ty),
      hasFvar_liftLooseBVars (e := v), hasFvar_liftLooseBVars (e := b)]
  | .proj _ _ e => by
    simp only [Expr.liftLooseBVars, Expr.hasFvar, hasFvar_liftLooseBVars (e := e)]

theorem hasFvar_mkAppN : ∀ {as : List Expr} {f : Expr}, f.hasFvar = false →
    (∀ a ∈ as, a.hasFvar = false) → (Expr.mkAppN f as).hasFvar = false
  | [], _, hf, _ => hf
  | a :: as, f, hf, ha => by
    refine hasFvar_mkAppN (f := .app f a) ?_ fun x hx => ha x (List.mem_cons_of_mem _ hx)
    simp [Expr.hasFvar, hf, ha a List.mem_cons_self]

/-- **The abstraction brings no free variable**: it only moves bound
ones and replaces spines by `ih` openers (`abstractIh_preserves`). -/
theorem abstractIh_hasFvar {fr : ConLeche.BlockRuleFrame} {e e'' : Expr} {d : Nat}
    (hab : ConLeche.abstractIh fr d e = some e'') (hf : e.hasFvar = false) :
    e''.hasFvar = false :=
  ConLeche.abstractIh_preserves (fun _ e => e.hasFvar = false) (fun _ e => e.hasFvar = false)
    (fun _ _ _ => by split <;> rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ hc hf => by
      obtain ⟨maj, hmaj, rfl⟩ := blockIhCall?_args_sub hc
      refine hasFvar_mkAppN rfl fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      rw [hasFvar_liftLooseBVars]
      exact hasFvar_of_mem_getAppArgs (hasFvar_of_mem_getAppArgs hf maj hmaj) y hy)
    (fun _ _ _ _ _ _ h i1 i2 => by
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h ⊢; exact ⟨i1 h.1, i2 h.2⟩)
    (fun _ _ _ _ _ _ h i1 i2 => by
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h ⊢; exact ⟨i1 h.1, i2 h.2⟩)
    (fun _ _ _ _ _ _ _ h i1 i2 i3 => by
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h ⊢
      exact ⟨⟨i1 h.1.1, i2 h.1.2⟩, i3 h.2⟩)
    (fun _ _ _ _ _ h i1 => by simp only [Expr.hasFvar] at h ⊢; exact i1 h)
    (fun _ _ _ _ _ h i1 i2 => by
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at h ⊢; exact ⟨i1 h.1, i2 h.2⟩)
    hab hf

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

This is the abstraction on a recursor-free subterm, at the
denotation — the abstraction moved every non-call node and nothing
else — and it is
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
          hf.2
          (by rw [show F + (d + 1) = F + d + 1 from by omega]
              exact h1.cons _ (wscoped_instantiateList h1 ty hf.1 0))
          (by rw [show F + nR + (d + 1) = F + nR + d + 1 from by omega]
              exact h2.cons _ (wscoped_instantiateList h2 (ty.liftLooseBVars nR d)
                (by rw [hasFvar_liftLooseBVars]; exact hf.1) 0))]
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
          hf.2
          (by rw [show F + (d + 1) = F + d + 1 from by omega]
              exact h1.cons _ (wscoped_instantiateList h1 ty hf.1 0))
          (by rw [show F + nR + (d + 1) = F + nR + d + 1 from by omega]
              exact h2.cons _ (wscoped_instantiateList h2 (ty.liftLooseBVars nR d)
                (by rw [hasFvar_liftLooseBVars]; exact hf.1) 0))]
      cases denoteMeta acval env φ (F + (d + 1))
          (b.instantiateList (Expr.fvar (F + d) (ty.instantiateList as1 0) :: as1) 0) with
      | none => rfl
      | some ba => rfl

/-! ## The frame kit: the `nR` ih binders, dropped

`AnnotTerm.liftN nR · d` is matched by `shiftE nR d`, and at the
rule's frame that is exactly "forget the ih block". -/

variable {V : Type uv} [SetTheory V]

theorem shiftE_consList_ih {d nR : Nat} {locals ihvals : List V} {ρ' : Nat → V}
    (hloc : locals.length = d) (hih : ihvals.length = nR) :
    shiftE nR d (consList locals (consList ihvals ρ')) = consList locals ρ' := by
  funext i
  rw [shiftE]
  rcases Nat.lt_or_ge i d with hi | hi
  · rw [if_pos hi, consList_getD_of_lt _ _ _ (by omega),
      consList_getD_of_lt _ _ _ (by omega)]
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + d := ⟨i - d, by omega⟩
    rw [if_neg (by omega),
      show i' + d + nR = (i' + nR) + locals.length from by omega,
      consList_apply_add, ← hloc, consList_apply_add,
      show i' + nR = i' + ihvals.length from by omega, consList_apply_add]

omit [SetTheory V] in
/-- **The whole prefix dropped**: `nR + d` below the walk's frame is
the rule's own — the companion of `shiftE_consList_ih`, at the cut
`0` a lifted DOMAIN list is read at. -/
theorem shiftE_consList_two {d nR : Nat} {locals ihvals : List V} {ρ' : Nat → V}
    (hloc : locals.length = d) (hih : ihvals.length = nR) :
    shiftE (nR + d) 0 (consList locals (consList ihvals ρ')) = ρ' := by
  funext i
  rw [shiftE, if_neg (by omega),
    show i + (nR + d) = i + nR + locals.length from by omega, consList_apply_add,
    show i + nR = i + ihvals.length from by omega, consList_apply_add]

/-- Readings are unique, so two read spines of one subject list are
one. -/
theorem denoteMetaSpine_unique {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {D : Nat} :
    ∀ {es : List Expr} {ws ws' : List AnnotTerm},
      DenoteMetaSpine acval env φ D es ws → DenoteMetaSpine acval env φ D es ws' → ws = ws'
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons ha hrest, .cons ha' hrest' => by
    rw [Option.some.inj (ha.symm.trans ha'), denoteMetaSpine_unique hrest hrest']

/-- Each subject of a read spine has its reading in it. -/
theorem denoteMetaSpine_subj {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {D : Nat} :
    ∀ {es : List Expr} {ws : List AnnotTerm}, DenoteMetaSpine acval env φ D es ws →
      ∀ e ∈ es, ∃ x ∈ ws, denoteMeta acval env φ D e = some x
  | _, _, .nil, _, he => nomatch he
  | _, _, .cons (v := v) ha hrest, e, he => by
    rcases List.mem_cons.mp he with rfl | he'
    · exact ⟨v, List.mem_cons_self, ha⟩
    · obtain ⟨x, hx, hde⟩ := denoteMetaSpine_subj hrest e he'
      exact ⟨x, List.mem_cons_of_mem _ hx, hde⟩

/-- A read spine moves along an environment extension, subject by
subject. -/
theorem denoteMetaSpine_mono {acval acvalT : Name → (Name → Nat) → AnnotTerm}
    {env envT : Env} {φ : Name → Nat} {D : Nat}
    (hmono : ∀ (y : Expr) (ya : AnnotTerm), ConstsBound envT y →
      denoteMeta acvalT envT φ D y = some ya → denoteMeta acval env φ D y = some ya) :
    ∀ {es : List Expr} {ws : List AnnotTerm},
      DenoteMetaSpine acvalT envT φ D es ws → (∀ e ∈ es, ConstsBound envT e) →
      DenoteMetaSpine acval env φ D es ws := by
  intro es ws h
  induction h with
  | nil => intro _; exact .nil
  | cons ha _ ih =>
    intro hcb
    exact .cons (hmono _ _ (hcb _ List.mem_cons_self) ha)
      (ih (fun e he => hcb e (List.mem_cons_of_mem _ he)))

/-- A spine's arguments inherit the node's constant bound. -/
theorem constsBound_mkAppN_args {envT : Env} :
    ∀ (as : List Expr) {f : Expr}, ConstsBound envT (Expr.mkAppN f as) →
      ConstsBound envT f ∧ ∀ a ∈ as, ConstsBound envT a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    have h' : ConstsBound envT (Expr.mkAppN (Expr.app f a) as) := h
    obtain ⟨hfa, hargs⟩ := constsBound_mkAppN_args as h'
    rw [constsBound_app] at hfa
    refine ⟨hfa.1, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hfa.2
    · exact hargs b hb'

/-- **The non-call node's `interp` step**: a subterm the abstraction
only lifted reads the same, at the frame with the ih block dropped. -/
theorem interp_of_open_lift
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {nR F d : Nat} {e : Expr} {as1 as2 : List Expr} {locals ihvals : List V} {ρ' : Nat → V}
    {A B : AnnotTerm}
    (hf : e.hasFvar = false) (h1 : FvarList (F + d) as1) (h2 : FvarList (F + nR + d) as2)
    (hloc : locals.length = d) (hih : ihvals.length = nR)
    (hA : denoteMeta acval env φ (F + d) (e.instantiateList as1 0) = some A)
    (hB : denoteMeta acval env φ (F + nR + d)
      ((e.liftLooseBVars nR d).instantiateList as2 0) = some B) :
    interp V (consList locals ρ') A
      = interp V (consList locals (consList ihvals ρ')) B := by
  have hEq := denoteMeta_open_liftLooseBVars (acval := acval) (env := env) (φ := φ)
    hacl nR F e d as1 as2 hf h1 h2
  rw [hA, hB, Option.map_some] at hEq
  obtain rfl : B = A.liftN nR d := Option.some.inj hEq
  rw [interp_liftN V nR A d, shiftE_consList_ih hloc hih]

/-! ## The guarded call's node, as a named premise

O-1's only non-structural case: at a node the abstraction replaced by
`ih_r a⃗`, the stored node's reading and the ih value applied along the
arguments' readings agree.  That is a statement about the ih VALUES —
`ihFunAV`'s readings, folded by `ihFunAV_fold` — and about the leaf,
so it is the recursor model's seam and not this induction's. -/

/-- **The node's own typing**: the residue sub-term the walk has
reached was inferred by the rule stage's own run, at the checker's
CERTIFIED grade (`inferTypeCore μ` at `μ = .verified` is
`Infer … .full`, `Rules.inferTypeCore_bridge`).

The fit of a guarded call's arguments is
a fact about an OCCURRENCE — the run certified THAT node's arguments
— and a premise quantified over every expression of the call's shape
says nothing about it.  The walk that visits the occurrence is
`interp_abstractIh`, and it carries this hypothesis exactly as it
already carries `hasFvar` and `looseBVarsBounded`. -/
@[expose] def IhTyped (envT : Env) (D : Nat) (e : Expr) : Prop :=
  ∃ t : Expr, ConLeche.Rules.Infer envT .full D e t

/-- A projection's scrutinee is typed. -/
theorem IhTyped.projArg {envT : Env} {D : Nat} {sn : Name} {i : Nat} {p : Expr} :
    IhTyped envT D (.proj sn i p) → IhTyped envT D p
  | ⟨_, .proj hp _ _ _ _ _ _⟩ => ⟨_, hp⟩

/-- A λ's domain is typed — at `.full`, where the domain check is not
skipped. -/
theorem IhTyped.lamDom {envT : Env} {D : Nat} {ty b : Expr} {bi : ConLeche.BinderMeta} :
    IhTyped envT D (.lam ty b bi) → IhTyped envT D ty
  | ⟨_, .lam h1 _ _ _ _ _ _⟩ => ⟨_, h1 rfl⟩

/-- A λ's OPENED body is typed, one binder deeper — the opener is the
frame's own `fvar D ty`, which is the list `interp_abstractIh` conses
onto `as2`. -/
theorem IhTyped.lamBody {envT : Env} {D : Nat} {ty b : Expr} {bi : ConLeche.BinderMeta} :
    IhTyped envT D (.lam ty b bi) → IhTyped envT (D + 1) (b.instantiate1 (.fvar D ty))
  | ⟨_, .lam _ _ hb _ _ _ _⟩ => ⟨_, hb⟩

/-- A `∀`'s domain is typed. -/
theorem IhTyped.piDom {envT : Env} {D : Nat} {ty b : Expr} {bi : ConLeche.BinderMeta} :
    IhTyped envT D (.forallE ty b bi) → IhTyped envT D ty
  | ⟨_, .forallE h1 _ _ _ _⟩ => ⟨_, h1⟩

/-- A `∀`'s opened body is typed, one binder deeper. -/
theorem IhTyped.piBody {envT : Env} {D : Nat} {ty b : Expr} {bi : ConLeche.BinderMeta} :
    IhTyped envT D (.forallE ty b bi) → IhTyped envT (D + 1) (b.instantiate1 (.fvar D ty))
  | ⟨_, .forallE _ _ h3 _ _⟩ => ⟨_, h3⟩

/-- An application's head is typed.  `Infer.appSkip` is `.io`-only, so
at `.full` there is exactly one way to infer an application. -/
theorem IhTyped.appFn {envT : Env} {D : Nat} {f a : Expr} :
    IhTyped envT D (.app f a) → IhTyped envT D f
  | ⟨_, .app hf _ _ _⟩ => ⟨_, hf⟩

/-- An application's ARGUMENT is typed. -/
theorem IhTyped.appArg {envT : Env} {D : Nat} {f a : Expr} :
    IhTyped envT D (.app f a) → IhTyped envT D a
  | ⟨_, .app _ _ ha _⟩ => ⟨_, ha⟩

/-- **The walk's LOCAL frame fits its own domains**.

`interp_abstractIh` quantifies `locals` with `locals.length = d` and
nothing about their VALUES.  That is sound for the walk itself — its
conclusion is a reading EQUALITY, true at every frame — but not for
`hfit`, whose consumer β-reduces a λ-tower (`ihFunAV_fold`) and needs
the call's arguments to fit.  One accepted rule refutes the
unqualified form: a reflexive field `f : Nat → T` whose right-hand
side calls the `ih` under a local binder makes the call's argument a
LOCAL, and at a junk local the fit fails.

Binder `j` is counted INNERMOST-FIRST, as `as1` is: it sits at
position `locals.length - 1 - j` of `locals`, and its domain is read
BELOW it, at the locals standing when it was opened. -/
@[expose] def LocalsFit (V : Type uv) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (F : Nat) (ρ' : Nat → V) (locals : List V) (as1 : List Expr) : Prop :=
  ∀ (j : Nat), j < locals.length → ∀ x : Expr, as1[j]? = some x →
    ∀ ta : AnnotTerm,
      denoteMeta acval env φ (F + locals.length - 1 - j) (Expr.fvarTypeD x) = some ta →
      locals.getD (locals.length - 1 - j) pt
        ∈ˢ interp V (consList (locals.take (locals.length - 1 - j)) ρ') ta

/-- The empty local frame fits vacuously — the walk's entry point. -/
theorem LocalsFit.nil {F : Nat} {ρ' : Nat → V} {as1 : List Expr} :
    LocalsFit V acval env φ F ρ' [] as1 := by
  intro j hj; exact absurd hj (by simp)

/-- **Opening one binder extends the local fit** — the membership the
binder congruences (`lamR_congr`, `piR_congr`) hand over is exactly
the new entry's obligation. -/
theorem LocalsFit.cons {F : Nat} {ρ' : Nat → V} {locals : List V} {as1 : List Expr}
    (h : LocalsFit V acval env φ F ρ' locals as1) {x : V} {ty : Expr} {ta : AnnotTerm}
    (hta : denoteMeta acval env φ (F + locals.length) ty = some ta)
    (hx : x ∈ˢ interp V (consList locals ρ') ta) :
    LocalsFit V acval env φ F ρ' (locals ++ [x])
      (Expr.fvar (F + locals.length) ty :: as1) := by
  intro j hj y hy tb htb
  have hlen : (locals ++ [x]).length = locals.length + 1 := by simp
  rw [hlen] at hj htb ⊢
  cases j with
  | zero =>
    obtain rfl : y = Expr.fvar (F + locals.length) ty := by
      simpa using hy.symm
    rw [show Expr.fvarTypeD (Expr.fvar (F + locals.length) ty) = ty from rfl,
      show F + (locals.length + 1) - 1 - 0 = F + locals.length from by omega] at htb
    obtain rfl : tb = ta := Option.some.inj (htb.symm.trans hta)
    rw [show locals.length + 1 - 1 - 0 = locals.length from by omega]
    have h1 : (locals ++ [x]).getD locals.length pt = x := by
      simp [List.getD_eq_getElem?_getD]
    have h2 : (locals ++ [x]).take locals.length = locals := by simp
    rw [h1, h2]
    exact hx
  | succ j =>
    have hjl : j < locals.length := by omega
    have hidx : locals.length + 1 - 1 - (j + 1) = locals.length - 1 - j := by omega
    rw [hidx]
    have h1 : (locals ++ [x]).getD (locals.length - 1 - j) pt
        = locals.getD (locals.length - 1 - j) pt := by
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega)]
    have h2 : (locals ++ [x]).take (locals.length - 1 - j)
        = locals.take (locals.length - 1 - j) :=
      List.take_append_of_le_length (by omega)
    rw [h1, h2]
    refine h j hjl y (by simpa using hy) tb ?_
    rw [show F + locals.length - 1 - j = F + (locals.length + 1) - 1 - (j + 1) from by omega]
    exact htb

/-! ## The frame, in the shape the reading battery wants

`FvarList E as1` is the check's own opening list — DESCENDING, because
`instantiateList` consumes `bvar 0` first.  The reading battery
(`denoteMeta_instSeq_mkPisOf`, `denoteMeta_ihSpineAt`) is stated over
the ASCENDING list `L` with `L[k] = fvar k`, through `Expr.instSeq`.
They are the same frame reversed, and these three lemmas are the
bridge. -/

/-- The opening list, reversed, is the ascending frame. -/
theorem FvarList.reverse_length {E : Nat} {as1 : List Expr} (h : FvarList E as1) :
    as1.reverse.length = E := by rw [List.length_reverse, h.1]

theorem FvarList.reverse_idx {E : Nat} {as1 : List Expr} (h : FvarList E as1) :
    ∀ (k : Nat) (x : Expr), as1.reverse[k]? = some x → ∃ ty, x = Expr.fvar k ty := by
  intro k x hx
  have hk : k < E := by
    rcases Nat.lt_or_ge k E with hk | hk
    · exact hk
    · rw [List.getElem?_eq_none (by rw [h.reverse_length]; omega)] at hx
      exact nomatch hx
  rw [List.getElem?_reverse (by rw [h.1]; omega), h.1] at hx
  obtain ⟨ty, hty⟩ := h.2.1 (E - 1 - k) (by omega)
  rw [hty] at hx
  exact ⟨ty, by rw [← Option.some.inj hx, show E - 1 - (E - 1 - k) = k from by omega]⟩

/-- Opening at a `FvarList` IS the battery's `instSeq` at the
ascending frame. -/
theorem instantiateList_eq_instSeq_of_fvarList {E : Nat} {as1 : List Expr}
    (h : FvarList E as1) (hE : 0 < E) (e : Expr) :
    e.instantiateList as1 0 = Expr.instSeq as1.reverse (E - 1) e := by
  have hne : as1 ≠ [] := by
    intro hnil
    rw [hnil] at h
    exact absurd h.1.symm (by simp; omega)
  rw [ConLeche.instantiateList_eq_instSeq hne e, h.1]

theorem looseBVarsBounded_instSeq : ∀ (sp : List Expr) (t : Nat),
    (∀ s ∈ sp, s.looseBVarsBounded 0 = true) → sp.length = t + 1 →
    ∀ {a : Expr}, a.looseBVarsBounded (t + 1) = true →
      (Expr.instSeq sp t a).looseBVarsBounded 0 = true
  | [], t, _, hlen, _, _ => absurd hlen (by simp)
  | s :: ss, t, hsp, hlen, a, ha => by
    have hss : ss.length = t := by simpa using hlen
    have hs : s.looseBVarsBounded 0 = true := hsp s List.mem_cons_self
    cases t with
    | zero =>
      obtain rfl : ss = [] := List.eq_nil_of_length_eq_zero hss
      exact ConLeche.Expr.looseBVarsBounded_instantiate1_gen hs ha
    | succ t' =>
      show (Expr.instSeq ss t' (a.instantiate1 s (t' + 1))).looseBVarsBounded 0 = true
      exact looseBVarsBounded_instSeq ss t'
        (fun x hx => hsp x (List.mem_cons_of_mem _ hx)) hss
        (ConLeche.Expr.looseBVarsBounded_instantiate1_gen hs ha)

/-! ## The frame's CONTEXT, threaded with the walk

`hfit`'s discharge runs through `certs_sound`, whose conclusion is
`∀ ρ, Sat V Δa ρ → TeleFitPA …`: it needs a CONTEXT at the frame the
walk has reached — the check's `rP + nF + nR` block extended by the
`d` binders the walk opened.  It is ONE predicate, threaded with the
walk, because the residue's opening list
`as2` and the context `Δa` are INDEX-ALIGNED: `as2[j]` is the frame's
variable `D - 1 - j`, `Δa[j]` is its domain's reading at its own
depth, and `Sat`'s orientation (innermost first) is `as2`'s — so all
four obligations `ctxOk_of_openers` asks are read off one list.

The context lives at `envT`, the CONSTRUCTORS' environment, because
that is where the rule stage's `inferType` ran; the residue mentions
no block recursor (`abstractIh` replaced every guarded call by an
`ih` opener), which is what lets its readings live there at all. -/

/-- **Instantiation stays bounded by the environment** — the
companion of `wscoped_instantiateList` and `fvarLeaves_instantiateList`
for `ConstsBound`, proved the same way: the opening list's entries are
the only constants the result gains. -/
theorem constsBound_instantiateList {envT : Env} {E : Nat} {xs : List Expr}
    (h : FvarList E xs) (hxs : ∀ x ∈ xs, ConstsBound envT x) :
    ∀ (e : Expr), e.hasFvar = false → ConstsBound envT e → ∀ (k : Nat),
      ConstsBound envT (e.instantiateList xs k) := by
  intro e
  induction e with
  | bvar j =>
    intro _ _ k
    rw [Expr.instantiateList]
    by_cases hjk : j < k
    · rw [if_pos hjk]; simp
    rw [if_neg hjk]
    by_cases hin : j - k < xs.length
    · rw [dif_pos hin]
      obtain ⟨ty, hty⟩ := h.2.1 (j - k) (by rw [h.1] at hin; omega)
      obtain ⟨hlt', hget⟩ := List.getElem?_eq_some_iff.mp hty
      have hcb := hxs xs[j - k] (List.getElem_mem hin)
      rw [hget] at hcb ⊢
      rw [Expr.instantiateList]
      exact hcb
    · rw [dif_neg hin]; simp
  | fvar _ _ => intro hf _ _; exact absurd hf (by simp [Expr.hasFvar])
  | sort _ => intro _ _ k; simp [Expr.instantiateList]
  | const _ _ => intro _ hc k; rw [Expr.instantiateList]; exact hc
  | lit _ => intro _ _ k; simp [Expr.instantiateList]
  | app f a ihf iha =>
    intro hf hc k
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [constsBound_app] at hc
    simp only [Expr.instantiateList, constsBound_app]
    exact ⟨ihf hf.1 hc.1 k, iha hf.2 hc.2 k⟩
  | lam ty b bi ihty ihb =>
    intro hf hc k
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [constsBound_lam] at hc
    simp only [Expr.instantiateList, constsBound_lam]
    exact ⟨ihty hf.1 hc.1 k, ihb hf.2 hc.2 (k + 1)⟩
  | forallE ty b bi ihty ihb =>
    intro hf hc k
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [constsBound_forallE] at hc
    simp only [Expr.instantiateList, constsBound_forallE]
    exact ⟨ihty hf.1 hc.1 k, ihb hf.2 hc.2 (k + 1)⟩
  | letE ty v b ihty ihv ihb =>
    intro hf hc k
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [constsBound_letE] at hc
    simp only [Expr.instantiateList, constsBound_letE]
    exact ⟨ihty hf.1.1 hc.1 k, ihv hf.1.2 hc.2.1 k, ihb hf.2 hc.2.2 (k + 1)⟩
  | proj _ _ e ihe =>
    intro hf hc k
    simp only [Expr.hasFvar] at hf
    rw [constsBound_proj] at hc
    simp only [Expr.instantiateList, constsBound_proj]
    exact ihe hf hc k

/-- **The walk's context**: the residue frame's opening list `as2`,
the context `Δa` its domains read to, and a valuation satisfying it.
The last three conjuncts are the frame's HEREDITARY facts — the
annotations are closed, bounded by `envT`, and draw their own leaves
from the frame — which is what makes `CtxOk` a projection
(`WalkCtx.ctxOk`) rather than a construction at every node. -/
@[expose] def WalkCtx (V : Type uv) [SetTheory V] {envT : Env} (mT : EnvModel V envT)
    (φ : Name → Nat) (D : Nat) (ρfull : Nat → V) (Δa : List AnnotTerm) (as2 : List Expr) :
    Prop :=
  Δa.length = D ∧
  Sat V Δa ρfull ∧
  (∀ (j : Nat) (x : Expr), as2[j]? = some x →
    denoteMeta mT.acval envT φ (D - 1 - j) (Expr.fvarTypeD x) = some (Δa.getD j default)) ∧
  (∀ s, s < D → ∀ ρ : Nat → V, Sat V Δa ρ →
    WellDenotedV V (fun j => ρ (j + s + 1)) (Δa.getD s default)) ∧
  (∀ x ∈ as2, (Expr.fvarTypeD x).looseBVarsBounded 0 = true) ∧
  (∀ x ∈ as2, ConstsBound envT x) ∧
  (∀ x ∈ as2, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar l.1 l.2 ∈ as2)

/-- **Opening one binder extends the walk's context.**  The new slot
is the binder's own domain, read at the frame it was opened at; its
`Sat` obligation is the membership the binder congruences hand over
(the same one `LocalsFit.cons` consumes) and its `hokΔ` obligation is
the domain's GRADING, which the rule stage's own inference supplies
(`infer_sound` at `IhTyped.lamDom`).  Every older slot's obligation
weakens for free, because it is stated at the slot's own shifted
valuation and `Sat_tail` is the shift. -/
theorem WalkCtx.cons {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D : Nat}
    {ρfull : Nat → V} {Δa : List AnnotTerm} {as2 : List Expr}
    (h : WalkCtx V mT φ D ρfull Δa as2) {ty : Expr} {ta : AnnotTerm} {x : V}
    (hta : denoteMeta mT.acval envT φ D ty = some ta)
    (hlb : ty.looseBVarsBounded 0 = true) (hcb : ConstsBound envT ty)
    (hcl : ∀ l ∈ ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ as2)
    (hG : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ta)
    (hx : x ∈ˢ interp V ρfull ta) :
    WalkCtx V mT φ (D + 1) (cons x ρfull) (ta :: Δa) (Expr.fvar D ty :: as2) := by
  obtain ⟨hlen, hsat, hdoms, hok, hlbs, hcbs, hcls⟩ := h
  refine ⟨by simp [hlen], Sat_cons V hsat hx, ?_, ?_, ?_, ?_, ?_⟩
  · intro j y hy
    cases j with
    | zero =>
      obtain rfl : y = Expr.fvar D ty := by simpa using hy.symm
      rw [show D + 1 - 1 - 0 = D from by omega,
        show (Expr.fvar D ty).fvarTypeD = ty from rfl]
      simpa using hta
    | succ j =>
      rw [show D + 1 - 1 - (j + 1) = D - 1 - j from by omega]
      have := hdoms j y (by simpa using hy)
      simpa using this
  · intro s hs ρ hρ
    cases s with
    | zero => exact hG _ (Sat_tail hρ)
    | succ s =>
      have heq : (fun j => ρ (j + (s + 1) + 1)) = fun j => ρ (j + s + 1 + 1) := by
        funext j; congr 1
      rw [show ((ta :: Δa).getD (s + 1) default) = Δa.getD s default from rfl, heq]
      exact hok s (by omega) (fun j => ρ (j + 1)) (Sat_tail hρ)
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact hlb
    · exact hlbs y hy'
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · rw [constsBound_fvar]; exact hcb
    · exact hcbs y hy'
  · intro y hy l hl
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact List.mem_cons_of_mem _ (hcl l hl)
    · exact List.mem_cons_of_mem _ (hcls y hy' l hl)

/-- **`CtxOk` from the walk's context**, at any node the frame opened:
`ctxOk_of_openers` at the ASCENDING form of the opening list.  Every
one of its six inputs is a field of `WalkCtx` or of the `FvarList`;
nothing is proved per node but the leaf membership, which
`fvarLeaves_instantiateList` gives for the whole walk at once. -/
theorem WalkCtx.ctxOk {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D : Nat}
    {ρfull : Nat → V} {Δa : List AnnotTerm} {as2 : List Expr}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (h2 : FvarList D as2) (h : WalkCtx V mT φ D ρfull Δa as2)
    {e : Expr} (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ as2) :
    CtxOk mT φ D Δa e := by
  obtain ⟨hlen, -, hdoms, hok, -, -, -⟩ := h
  have hrev : ∀ (i : Nat), i < D → as2.reverse[i]? = as2[D - 1 - i]? := by
    intro i hi
    rw [List.getElem?_reverse (by rw [h2.1]; omega), h2.1]
  refine ctxOk_of_openers hacl (fvs := as2.reverse) (n := D)
    (Aa := fun i => Δa.getD (D - 1 - i) default) hlen h2.reverse_idx ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact h2.2.2 x (List.mem_reverse.mp hx)
  · intro i x hx
    have hi : i < D := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [h2.reverse_length] at this
      exact this
    rw [hrev i hi] at hx
    have := hdoms (D - 1 - i) x hx
    rw [show D - 1 - (D - 1 - i) = i from by omega] at this
    exact this
  · intro l hl
    exact List.mem_reverse.mpr (hleaf l hl)
  · intro l hl
    obtain ⟨p, hp⟩ := List.getElem?_of_mem (List.mem_reverse.mpr (hleaf l hl))
    obtain ⟨ty, hty⟩ := h2.reverse_idx p _ hp
    have hpl : p < D := by
      have := (List.getElem?_eq_some_iff.mp hp).1
      rw [h2.reverse_length] at this
      exact this
    obtain ⟨h1', -⟩ : l.1 = p ∧ l.2 = ty := by
      injection hty with a b
      exact ⟨a, b⟩
    omega
  · intro i hi
    rw [List.getD, List.getElem?_eq_getElem (by rw [hlen]; omega)]
    rfl
  · intro i hi ρ hρ
    exact hok (D - 1 - i) (by omega) ρ hρ

/-- **The opened term's leaves ARE frame variables.**
`fvarLeaves_instantiateList` puts each leaf inside SOME opener; a
frame that is leaf-closed (`WalkCtx`'s last conjunct) then puts it in
the frame itself, which is what `WalkCtx.ctxOk` asks. -/
theorem fvarLeaves_mem_instantiateList {E : Nat} {as : List Expr} (h : FvarList E as)
    (hcls : ∀ x ∈ as, ∀ l ∈ (Expr.fvarTypeD x).fvarLeaves, Expr.fvar l.1 l.2 ∈ as)
    {e : Expr} (hf : e.hasFvar = false) (k : Nat) :
    ∀ l ∈ (e.instantiateList as k).fvarLeaves, Expr.fvar l.1 l.2 ∈ as := by
  intro l hl
  obtain ⟨x, hx, hlx⟩ := fvarLeaves_instantiateList h e hf k l hl
  obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
  have hql : q < E := by
    have := (List.getElem?_eq_some_iff.mp hq).1
    rw [h.1] at this; exact this
  obtain ⟨ty, hty⟩ := h.2.1 q hql
  obtain rfl : x = Expr.fvar (E - 1 - q) ty := Option.some.inj (hq.symm.trans hty)
  simp only [Expr.fvarLeaves, List.mem_cons] at hlx
  rcases hlx with rfl | hl'
  · exact hx
  · exact hcls _ hx l hl'

/-- **The opened term is bvar-closed**: the frame's variables are, and
they replace every loose index. -/
theorem looseBVarsBounded_open {E : Nat} {as : List Expr} (h : FvarList E as)
    {e : Expr} (hb : e.looseBVarsBounded E = true) :
    (e.instantiateList as 0).looseBVarsBounded 0 = true := by
  cases hE0 : E with
  | zero =>
    rw [hE0] at h hb
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero h.1
    rw [ConLeche.Expr.instantiateList_nil]
    exact hb
  | succ E' =>
  rw [hE0] at h hb
  have hE : 0 < E' + 1 := by omega
  rw [instantiateList_eq_instSeq_of_fvarList h hE]
  refine looseBVarsBounded_instSeq as.reverse (E' + 1 - 1) ?_ (by rw [h.reverse_length]; omega) ?_
  · intro s hs
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hs
    obtain ⟨ty, hty⟩ := h.reverse_idx q s hq
    rw [hty]; rfl
  · rw [show E' + 1 - 1 + 1 = E' + 1 from by omega]; exact hb

/-- **Opening one of the WALK's binders**, with every obligation
discharged from the frame itself: the new slot's domain is bvar-closed
and `envT`-bounded because the frame is, its leaves are the frame's,
and its GRADING is the rule stage's own inference at that node
(`IhTyped`, through `infer_sound`) — which is the one place the
walk's context needs the check to have typed anything. -/
theorem WalkCtx.subjOk {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D : Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {ρfull : Nat → V} {Δa : List AnnotTerm} {as2 : List Expr}
    (h2 : FvarList D as2) (h : WalkCtx V mT φ D ρfull Δa as2)
    {e : Expr} (hfv : e.hasFvar = false) (hbb : e.looseBVarsBounded D = true)
    {ea : AnnotTerm}
    (hea : denoteMeta mT.acval envT φ D (e.instantiateList as2 0) = some ea)
    (hty : IhTyped envT D (e.instantiateList as2 0)) :
    Rules.Frame D (e.instantiateList as2 0) ∧
      CtxOk mT φ D Δa (e.instantiateList as2 0) ∧
      Rules.Graded V Δa ea := by
  have hcll := fvarLeaves_mem_instantiateList h2 h.2.2.2.2.2.2 hfv 0
  have hlbb := looseBVarsBounded_open h2 hbb
  have hLB : Expr.LeavesBounded (e.instantiateList as2 0) := by
    intro l hl
    exact h.2.2.2.2.1 _ (hcll l hl)
  have hFr : Rules.Frame D (e.instantiateList as2 0) :=
    ⟨wscoped_instantiateList h2 e hfv 0, hlbb, hLB⟩
  have hctx := h.ctxOk hacl h2 hcll
  obtain ⟨t, hInf⟩ := hty
  obtain ⟨-, -, ta, -, hG, -, -⟩ := Rules.infer_sound hin hInf hFr hctx hea
  exact ⟨hFr, hctx, hG⟩

/-- **Opening one of the WALK's binders** — `subjOk` at the domain,
whose grading is the new slot's `hokΔ` and whose membership is the
binder congruence's own. -/
theorem WalkCtx.consOpen {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D : Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {ρfull : Nat → V} {Δa : List AnnotTerm} {as2 : List Expr}
    (h2 : FvarList D as2) (h : WalkCtx V mT φ D ρfull Δa as2)
    {ty' : Expr} {tb : AnnotTerm} {x : V}
    (hfv : ty'.hasFvar = false) (hcb : ConstsBound envT ty')
    (hbb : ty'.looseBVarsBounded D = true)
    (htb : denoteMeta mT.acval envT φ D (ty'.instantiateList as2 0) = some tb)
    (hty : IhTyped envT D (ty'.instantiateList as2 0))
    (hx : x ∈ˢ interp V ρfull tb) :
    WalkCtx V mT φ (D + 1) (ConLeche.Semantics.cons x ρfull) (tb :: Δa)
      (Expr.fvar D (ty'.instantiateList as2 0) :: as2) := by
  obtain ⟨-, -, hG⟩ := WalkCtx.subjOk hacl hin h2 h hfv hbb htb hty
  exact h.cons htb (looseBVarsBounded_open h2 hbb)
    (constsBound_instantiateList h2 h.2.2.2.2.2.1 ty' hfv hcb 0)
    (fvarLeaves_mem_instantiateList h2 h.2.2.2.2.2.2 hfv 0) hG hx

/-- **A frame variable's ANNOTATION is a subject of the context.**
`certs_sound` asks the head's stored type for a `Frame`, a `CtxOk` and
a grading; all three are the frame's own, because `WalkCtx`'s last
three conjuncts say the annotations are closed, leaf-closed and
`envT`-bounded — the grading is `CtxOk`'s own last clause read at the
leaf. -/
theorem WalkCtx.annotOk {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat} {D : Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    {ρfull : Nat → V} {Δa : List AnnotTerm} {as2 : List Expr}
    (h2 : FvarList D as2) (h : WalkCtx V mT φ D ρfull Δa as2)
    {k : Nat} {ty : Expr} (hmem : Expr.fvar k ty ∈ as2) :
    Rules.Frame D ty ∧ CtxOk mT φ D Δa ty ∧
      ∀ ta : AnnotTerm, denoteMeta mT.acval envT φ D ty = some ta → Rules.Graded V Δa ta := by
  have hleafTy : ∀ l ∈ ty.fvarLeaves, Expr.fvar l.1 l.2 ∈ as2 :=
    fun l hl => h.2.2.2.2.2.2 _ hmem l hl
  have hleafV : ∀ l ∈ (Expr.fvar k ty).fvarLeaves, Expr.fvar l.1 l.2 ∈ as2 := by
    intro l hl
    simp only [Expr.fvarLeaves, List.mem_cons] at hl
    rcases hl with rfl | hl'
    · exact hmem
    · exact hleafTy l hl'
  have hws := h2.2.2 _ hmem
  simp only [Expr.WScoped] at hws
  have hlb : ty.looseBVarsBounded 0 = true := h.2.2.2.2.1 _ hmem
  refine ⟨⟨hws.2.mono (by omega), hlb, fun l hl => h.2.2.2.2.1 _ (hleafTy l hl)⟩,
    h.ctxOk hacl h2 hleafTy, fun ta hta ρ hρ => ?_⟩
  obtain ⟨-, hleaf⟩ := h.ctxOk (e := Expr.fvar k ty) hacl h2 hleafV
  obtain ⟨-, -, tya, Aa, htya, -, -, hok⟩ := hleaf (k, ty) (by simp [Expr.fvarLeaves])
  obtain rfl : tya = ta := Option.some.inj (htya.symm.trans hta)
  exact hok ρ hρ

/-- A read spine's entries are readings of its subjects. -/
theorem denoteMetaSpine_mem {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {D : Nat} :
    ∀ {es : List Expr} {ws : List AnnotTerm}, DenoteMetaSpine acval env φ D es ws →
      ∀ x ∈ ws, ∃ e ∈ es, denoteMeta acval env φ D e = some x
  | _, _, .nil, _, hx => nomatch hx
  | _, _, .cons (a := a) ha hrest, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨a, List.mem_cons_self, ha⟩
    · obtain ⟨e, he, hde⟩ := denoteMetaSpine_mem hrest x hx'
      exact ⟨e, List.mem_cons_of_mem _ he, hde⟩

/-- **A typed application spine's ARGUMENTS are typed.**  `Infer.app`
is the only `.full` rule for an application, so peeling the spine
peels the derivation. -/
theorem IhTyped.mkAppN_args {envT : Env} {D : Nat} :
    ∀ (as : List Expr) {f : Expr}, IhTyped envT D (Expr.mkAppN f as) →
      IhTyped envT D f ∧ ∀ a ∈ as, IhTyped envT D a
  | [], _, h => ⟨h, fun _ ha => nomatch ha⟩
  | a :: as, f, h => by
    have h' : IhTyped envT D (Expr.mkAppN (Expr.app f a) as) := h
    obtain ⟨hfa, hargs⟩ := IhTyped.mkAppN_args as h'
    refine ⟨hfa.appFn, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact hfa.appArg
    · exact hargs b hb'

/-- An opened variable's inferred type is its STORED annotation —
`certs_of_infer_mkAppN`'s "the head's type is pinned". -/
theorem IhTyped.fvarTy {envT : Env} {D idx : Nat} {ty t : Expr}
    (h : ConLeche.Rules.Infer envT .full D (.fvar idx ty) t) : t = ty := by
  cases h; rfl

/-- **The guarded call's value.** -/
@[expose] def IhNodeVal (V : Type uv) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) {envT : Env} (mT : EnvModel V envT)
    (φ : Name → Nat)
    (fr : ConLeche.BlockRuleFrame) (F : Nat) (ρ' : Nat → V) (ihvals : List V)
    (as2₀ : List Expr) : Prop :=
  ∀ (d : Nat) (locals : List V) (e : Expr) (r : Nat) (as as1 as2 : List Expr)
    (Δa : List AnnotTerm) (A B : AnnotTerm),
    e.hasFvar = false → e.looseBVarsBounded (F + d) = true →
    ConstsBound envT (Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
      (as.map fun x => x.liftLooseBVars fr.nR d)) →
    locals.length = d → FvarList (F + d) as1 → FvarList (F + fr.nR + d) as2 →
    as2₀ <:+ as2 → LocalsFit V acval env φ F ρ' locals as1 →
    WalkCtx V mT φ (F + fr.nR + d) (consList locals (consList ihvals ρ')) Δa as2 →
    ConLeche.blockIhCall? fr d e = some (r, as) →
    denoteMeta acval env φ (F + d) (e.instantiateList as1 0) = some A →
    denoteMeta mT.acval envT φ (F + fr.nR + d)
      ((Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
        (as.map fun x => x.liftLooseBVars fr.nR d)).instantiateList as2 0) = some B →
    IhTyped envT (F + fr.nR + d)
      ((Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
        (as.map fun x => x.liftLooseBVars fr.nR d)).instantiateList as2 0) →
    interp V (consList locals ρ') A
      = interp V (consList locals (consList ihvals ρ')) B

set_option maxHeartbeats 1000000 in
/-- **O-1**: the abstraction's inverse, at the reading.  The stored
right-hand side's body, read at the rule's frame, is the RESIDUE read
at the frame extended by the `ih` openers' values — `interp`, not
syntax: at a guarded call the residue holds `ih_r a⃗` and substituting
the ih term makes a β-redex (`ihFunAV_fold` evaluates it), so no
`AnnotTerm` equation can hold.

The induction is structural over the rule body; every node the
abstraction did not replace is `interp_of_open_lift`, and the one it
did is the premise `IhNodeVal`. -/
theorem interp_abstractIh
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {envT : Env} {mT : EnvModel V envT}
    (haclT : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    (hproj : ∀ (sn : Name) (i : Nat), envT.findProj? sn i = env.findProj? sn i)
    (hmono : ∀ (D : Nat) (y : Expr) (ya : AnnotTerm), ConstsBound envT y →
      denoteMeta mT.acval envT φ D y = some ya → denoteMeta acval env φ D y = some ya)
    {fr : ConLeche.BlockRuleFrame} {F : Nat} {ρ' : Nat → V} {ihvals : List V}
    (hih : ihvals.length = fr.nR) (hcall : IhNodeVal V acval env mT φ fr F ρ' ihvals as2₀) :
    ∀ (e e'' : Expr) (d : Nat) (locals : List V) (as1 as2 : List Expr) (Δa : List AnnotTerm)
      (A B : AnnotTerm),
      ConLeche.abstractIh fr d e = some e'' → e.hasFvar = false →
      e.looseBVarsBounded (F + d) = true →
      ConstsBound envT e'' → e''.looseBVarsBounded (F + fr.nR + d) = true →
      locals.length = d → FvarList (F + d) as1 → FvarList (F + fr.nR + d) as2 →
      as2₀ <:+ as2 → LocalsFit V acval env φ F ρ' locals as1 →
      WalkCtx V mT φ (F + fr.nR + d) (consList locals (consList ihvals ρ')) Δa as2 →
      denoteMeta acval env φ (F + d) (e.instantiateList as1 0) = some A →
      denoteMeta mT.acval envT φ (F + fr.nR + d) (e''.instantiateList as2 0) = some B →
      IhTyped envT (F + fr.nR + d) (e''.instantiateList as2 0) →
      interp V (consList locals ρ') A
        = interp V (consList locals (consList ihvals ρ')) B
  | .bvar j, e'', d, locals, as1, as2, Δa, A, B, hab, hf, hb, hcbe, hbT, hloc, h1, h2, hsx, hlf, hW, hA, hB, hty => by
    have hB' := hmono _ _ _ (constsBound_instantiateList h2 hW.2.2.2.2.2.1 _
      (abstractIh_hasFvar hab hf) hcbe 0) hB
    obtain rfl : e'' = (Expr.bvar j).liftLooseBVars fr.nR d := by
      rw [ConLeche.abstractIh_bvar] at hab
      rw [Expr.liftLooseBVars, ← Option.some.inj hab]
      split <;> rename_i hj
      · rw [if_neg (by omega)]
      · rw [if_pos (by omega)]
    exact interp_of_open_lift hacl hf h1 h2 hloc hih hA hB'
  | .sort u, e'', d, locals, as1, as2, Δa, A, B, hab, hf, hb, hcbe, hbT, hloc, h1, h2, hsx, hlf, hW, hA, hB, hty => by
    have hB' := hmono _ _ _ (constsBound_instantiateList h2 hW.2.2.2.2.2.1 _
      (abstractIh_hasFvar hab hf) hcbe 0) hB
    obtain rfl : e'' = (Expr.sort u).liftLooseBVars fr.nR d := (Option.some.inj hab).symm
    exact interp_of_open_lift hacl hf h1 h2 hloc hih hA hB'
  | .lit l, e'', d, locals, as1, as2, Δa, A, B, hab, hf, hb, hcbe, hbT, hloc, h1, h2, hsx, hlf, hW, hA, hB, hty => by
    have hB' := hmono _ _ _ (constsBound_instantiateList h2 hW.2.2.2.2.2.1 _
      (abstractIh_hasFvar hab hf) hcbe 0) hB
    obtain rfl : e'' = (Expr.lit l).liftLooseBVars fr.nR d := (Option.some.inj hab).symm
    exact interp_of_open_lift hacl hf h1 h2 hloc hih hA hB'
  | .const n us, e'', d, locals, as1, as2, Δa, A, B, hab, hf, hb, hcbe, hbT, hloc, h1, h2, hsx, hlf, hW, hA, hB, hty => by
    have hB' := hmono _ _ _ (constsBound_instantiateList h2 hW.2.2.2.2.2.1 _
      (abstractIh_hasFvar hab hf) hcbe 0) hB
    rw [ConLeche.abstractIh_const] at hab
    split at hab
    · exact nomatch hab
    · obtain rfl : e'' = (Expr.const n us).liftLooseBVars fr.nR d := (Option.some.inj hab).symm
      exact interp_of_open_lift hacl hf h1 h2 hloc hih hA hB'
  | .fvar _ _, _, _, _, _, _, _, _, _, hab, _, _, _, _, _, _, _, _, _, _, _, _, _ => nomatch hab
  | .letE ty v b, _, d, _, as1, _, _, A, _, _, _, _, _, _, _, _, _, _, _, _, hA, _, _ => by
    rw [Expr.instantiateList, denoteMeta] at hA
    exact nomatch hA
  | .proj sn i e, e'', d, locals, as1, as2, Δa, A, B, hab, hf, hb, hcbe, hbT, hloc, h1, h2, hsx, hlf, hW, hA, hB, hty => by
    simp only [Expr.hasFvar] at hf
    simp only [Expr.looseBVarsBounded] at hb
    rw [ConLeche.abstractIh] at hab
    split at hab
    · exact nomatch hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨e', hpe, rfl⟩ := hab
    rw [Expr.instantiateList] at hty
    rw [constsBound_proj] at hcbe
    simp only [Expr.looseBVarsBounded] at hbT
    rw [Expr.instantiateList, denoteMeta_proj] at hA hB
    obtain ⟨ea, hea, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨eb, heb, hB⟩ := Option.bind_eq_some_iff.mp hB
    have hrec := interp_abstractIh hacl haclT hin hproj hmono hih hcall e e' d locals as1 as2 Δa
      ea eb hpe hf hb hcbe hbT hloc h1 h2 hsx hlf hW hea heb hty.projArg
    rw [hproj sn i] at hB
    revert hA hB
    cases env.findProj? sn i with
    | some entry =>
      intro hA hB
      obtain rfl : A = projAV (i + entry.off) ea := (Option.some.inj hA).symm
      obtain rfl : B = projAV (i + entry.off) eb := (Option.some.inj hB).symm
      rw [projAV_interp, projAV_interp, hrec]
    | none =>
      intro hA hB
      rcases i with _ | _ | i
      · obtain rfl : A = .fst ea := (Option.some.inj hA).symm
        obtain rfl : B = .fst eb := (Option.some.inj hB).symm
        rw [interp_fst, interp_fst, hrec]
      · obtain rfl : A = .snd ea := (Option.some.inj hA).symm
        obtain rfl : B = .snd eb := (Option.some.inj hB).symm
        rw [interp_snd, interp_snd, hrec]
      · exact nomatch hA
  | .lam ty b bi, e'', d, locals, as1, as2, Δa, A, B, hab, hf, hb, hcbe, hbT, hloc, h1, h2, hsx, hlf, hW, hA, hB, hty => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [ConLeche.abstractIh, Option.bind_eq_some_iff] at hab
    obtain ⟨ty', hty', hab⟩ := hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨b', hb', rfl⟩ := hab
    rw [constsBound_lam] at hcbe
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbT
    rw [Expr.instantiateList, denoteMeta_lam] at hA hB
    obtain ⟨ta, hta, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨ba, hba, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨tb, htb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain ⟨bb, hbb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain rfl : A = .lam (pwBit φ bi.pw) ta ba := (Option.some.inj hA).symm
    obtain rfl : B = .lam (pwBit φ bi.pw) tb bb := (Option.some.inj hB).symm
    rw [← Expr.instantiateList_cons] at hba hbb
    rw [Expr.instantiateList] at hty
    have hrecT := interp_abstractIh hacl haclT hin hproj hmono hih hcall ty ty' d locals as1 as2
      Δa ta tb hty' hf.1 hb.1 hcbe.1 hbT.1 hloc h1 h2 hsx hlf hW hta htb hty.lamDom
    rw [interp_lam, interp_lam, hrecT]
    refine lamR_congr fun x hxA => ?_
    rw [show F + d + 1 = F + (d + 1) from by omega] at hba
    rw [show F + fr.nR + d + 1 = F + fr.nR + (d + 1) from by omega] at hbb
    have := interp_abstractIh hacl haclT hin hproj hmono hih hcall b b' (d + 1) (locals ++ [x])
      (Expr.fvar (F + d) (ty.instantiateList as1 0) :: as1)
      (Expr.fvar (F + fr.nR + d) (ty'.instantiateList as2 0) :: as2) (tb :: Δa) ba bb
      hb' hf.2 (by rw [show F + (d + 1) = F + d + 1 from by omega]; exact hb.2) hcbe.2
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega]; exact hbT.2)
      (by simp [hloc])
      (by rw [show F + (d + 1) = F + d + 1 from by omega]
          exact h1.cons _ (wscoped_instantiateList h1 ty hf.1 0))
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega]
          exact h2.cons _ (wscoped_instantiateList h2 ty' (abstractIh_hasFvar hty' hf.1) 0))
      (hsx.trans (List.suffix_cons _ _))
      (by rw [← hloc] at hta ⊢
          exact hlf.cons hta (hrecT ▸ hxA))
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega,
            consList_append, consList_cons, consList_nil]
          exact WalkCtx.consOpen haclT hin h2 hW (abstractIh_hasFvar hty' hf.1) hcbe.1 hbT.1 htb
            hty.lamDom (hrecT ▸ hxA))
      hba hbb
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega,
            Expr.instantiateList_cons]
          exact hty.lamBody)
    rwa [consList_append, consList_append] at this
  | .forallE ty b bi, e'', d, locals, as1, as2, Δa, A, B, hab, hf, hb, hcbe, hbT, hloc, h1, h2, hsx, hlf, hW, hA, hB, hty => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
    rw [ConLeche.abstractIh, Option.bind_eq_some_iff] at hab
    obtain ⟨ty', hty', hab⟩ := hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨b', hb', rfl⟩ := hab
    rw [constsBound_forallE] at hcbe
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbT
    rw [Expr.instantiateList, denoteMeta_forallE] at hA hB
    obtain ⟨ta, hta, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨ba, hba, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨tb, htb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain ⟨bb, hbb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain rfl : A = .pi 0 (pwBit φ bi.pw) ta ba := (Option.some.inj hA).symm
    obtain rfl : B = .pi 0 (pwBit φ bi.pw) tb bb := (Option.some.inj hB).symm
    rw [← Expr.instantiateList_cons] at hba hbb
    rw [Expr.instantiateList] at hty
    have hrecT := interp_abstractIh hacl haclT hin hproj hmono hih hcall ty ty' d locals as1 as2
      Δa ta tb hty' hf.1 hb.1 hcbe.1 hbT.1 hloc h1 h2 hsx hlf hW hta htb hty.piDom
    rw [interp_pi, interp_pi, hrecT]
    refine piR_congr fun x hxA => ?_
    rw [show F + d + 1 = F + (d + 1) from by omega] at hba
    rw [show F + fr.nR + d + 1 = F + fr.nR + (d + 1) from by omega] at hbb
    have := interp_abstractIh hacl haclT hin hproj hmono hih hcall b b' (d + 1) (locals ++ [x])
      (Expr.fvar (F + d) (ty.instantiateList as1 0) :: as1)
      (Expr.fvar (F + fr.nR + d) (ty'.instantiateList as2 0) :: as2) (tb :: Δa) ba bb
      hb' hf.2 (by rw [show F + (d + 1) = F + d + 1 from by omega]; exact hb.2) hcbe.2
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega]; exact hbT.2)
      (by simp [hloc])
      (by rw [show F + (d + 1) = F + d + 1 from by omega]
          exact h1.cons _ (wscoped_instantiateList h1 ty hf.1 0))
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega]
          exact h2.cons _ (wscoped_instantiateList h2 ty' (abstractIh_hasFvar hty' hf.1) 0))
      (hsx.trans (List.suffix_cons _ _))
      (by rw [← hloc] at hta ⊢
          exact hlf.cons hta (hrecT ▸ hxA))
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega,
            consList_append, consList_cons, consList_nil]
          exact WalkCtx.consOpen haclT hin h2 hW (abstractIh_hasFvar hty' hf.1) hcbe.1 hbT.1 htb
            hty.piDom (hrecT ▸ hxA))
      hba hbb
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega,
            Expr.instantiateList_cons]
          exact hty.piBody)
    rwa [consList_append, consList_append] at this
  | .app f a, e'', d, locals, as1, as2, Δa, A, B, hab, hf, hb, hcbe, hbT, hloc, h1, h2, hsx, hlf, hW, hA, hB, hty => by
    rw [ConLeche.abstractIh_app] at hab
    revert hab
    cases hc : ConLeche.blockIhCall? fr d (.app f a) with
    | some ra =>
      intro hab
      obtain ⟨r, as⟩ := ra
      obtain rfl := Option.some.inj hab
      exact hcall d locals (.app f a) r as as1 as2 Δa A B hf hb hcbe hloc h1 h2 hsx hlf hW hc
        hA hB hty
    | none =>
      intro hab
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb
      rw [Option.bind_eq_some_iff] at hab
      obtain ⟨f', hf', hab⟩ := hab
      rw [Option.map_eq_some_iff] at hab
      obtain ⟨a', ha', rfl⟩ := hab
      rw [constsBound_app] at hcbe
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbT
      rw [Expr.instantiateList, denoteMeta_app] at hA hB
      obtain ⟨fa, hfa, hA⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨aa, haa, hA⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨fb, hfb, hB⟩ := Option.bind_eq_some_iff.mp hB
      obtain ⟨ab, hab', hB⟩ := Option.bind_eq_some_iff.mp hB
      obtain rfl : A = .app fa aa := (Option.some.inj hA).symm
      obtain rfl : B = .app fb ab := (Option.some.inj hB).symm
      rw [Expr.instantiateList] at hty
      rw [interp_app, interp_app,
        interp_abstractIh hacl haclT hin hproj hmono hih hcall f f' d locals as1 as2 Δa fa fb
          hf' hf.1 hb.1 hcbe.1 hbT.1 hloc h1 h2 hsx hlf hW hfa hfb hty.appFn,
        interp_abstractIh hacl haclT hin hproj hmono hih hcall a a' d locals as1 as2 Δa aa ab
          ha' hf.2 hb.2 hcbe.2 hbT.2 hloc h1 h2 hsx hlf hW haa hab' hty.appArg]

/-! ## `IhNodeVal`, reduced to a statement about the STORED node

`IhNodeVal` mentions both sides of the abstraction.  Its
RESIDUE side computes outright — the residue's node is
`ih_r a⃗` with `a⃗` only LIFTED, so its value is the ih value folded
along the arguments' own readings (L1 again) — and what is left is a
statement about the STORED node alone:

> the stored guarded call reads to the ih value applied along the
> arguments' readings.

That is `IhCallFold` below, and `ihNodeVal_of_fold` is the reduction.
Nothing of `abstractIh`, of the residue's frame `as2` or of the `nR`
extra binders survives into it. -/

/-- Bulk instantiation distributes over an application spine. -/
theorem instantiateList_mkAppN :
    ∀ (as : List Expr) (f : Expr) (xs : List Expr) (k : Nat),
      (Expr.mkAppN f as).instantiateList xs k
        = Expr.mkAppN (f.instantiateList xs k) (as.map (·.instantiateList xs k))
  | [], _, _, _ => rfl
  | a :: as, f, xs, k => by
    show (Expr.mkAppN (.app f a) as).instantiateList xs k = _
    rw [instantiateList_mkAppN as (.app f a) xs k, Expr.instantiateList]
    rfl

/-- **The typed residue node, in `certs_of_infer_mkAppN`'s shape.**
The guarded call's residue is an application SPINE whose head is the
`ih` opener's own free variable — position `F + r` of the frame — so
the head's inferred type is that opener's stored annotation and the
spine's arguments are the call's own, opened.  This is step 1 of
`hfit`'s discharge; what is left of it is the opener's Π-count
(`piSpine_of_stripPis`) and the `Certs` walk. -/
theorem ihTyped_call_spine {envT : Env} {fr : ConLeche.BlockRuleFrame} {F d r : Nat}
    {as as2 : List Expr} (h2 : FvarList (F + fr.nR + d) as2) (hr : r < fr.nR)
    (hty : IhTyped envT (F + fr.nR + d)
      ((Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
        (as.map fun x => x.liftLooseBVars fr.nR d)).instantiateList as2 0)) :
    ∃ tyOp : Expr,
      (Expr.bvar (d + fr.nR - 1 - r)).instantiateList as2 0 = .fvar (F + r) tyOp ∧
      IhTyped envT (F + fr.nR + d)
        (Expr.mkAppN (.fvar (F + r) tyOp)
          (as.map fun x => (x.liftLooseBVars fr.nR d).instantiateList as2 0)) := by
  obtain ⟨tyOp, htyOp⟩ := h2.bvar_lt (j := d + fr.nR - 1 - r) (by omega)
  rw [show F + fr.nR + d - 1 - (d + fr.nR - 1 - r) = F + r from by omega] at htyOp
  refine ⟨tyOp, htyOp, ?_⟩
  rw [instantiateList_mkAppN, htyOp, List.map_map] at hty
  exact hty

/-- The residue's spine, read: each lifted argument's reading is the
argument's own, at the frame with the ih block dropped. -/
theorem denoteMetaSpine_of_lift
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {nR F d : Nat} {as1 as2 : List Expr}
    (h1 : FvarList (F + d) as1) (h2 : FvarList (F + nR + d) as2)
    {locals ihvals : List V} {ρ' : Nat → V}
    (hloc : locals.length = d) (hih : ihvals.length = nR) :
    ∀ (as : List Expr) (ws : List AnnotTerm), (∀ a ∈ as, a.hasFvar = false) →
      DenoteMetaSpine acval env φ (F + nR + d)
        (as.map fun x => (x.liftLooseBVars nR d).instantiateList as2 0) ws →
      ∃ vs : List AnnotTerm,
        DenoteMetaSpine acval env φ (F + d) (as.map (·.instantiateList as1 0)) vs ∧
        ws.map (interp V (consList locals (consList ihvals ρ')))
          = vs.map (interp V (consList locals ρ'))
  | [], ws, _, hsp => by cases hsp; exact ⟨[], .nil, rfl⟩
  | a :: as, ws, hf, hsp => by
    cases hsp with
    | @cons _ w _ ws' hw hsp' =>
      obtain ⟨vs, hvs, hmap⟩ := denoteMetaSpine_of_lift (ρ' := ρ') hacl h1 h2 hloc hih as ws'
        (fun x hx => hf x (List.mem_cons_of_mem _ hx)) hsp'
      have hfa : a.hasFvar = false := hf a List.mem_cons_self
      have hL := denoteMeta_open_liftLooseBVars (acval := acval) (env := env) (φ := φ)
        hacl nR F a d as1 as2 hfa h1 h2
      rw [hw] at hL
      cases hv : denoteMeta acval env φ (F + d) (a.instantiateList as1 0) with
      | none => rw [hv, Option.map_none] at hL; exact nomatch hL
      | some v =>
        refine ⟨v :: vs, .cons hv hvs, ?_⟩
        simp only [List.map_cons, hmap]
        rw [interp_of_open_lift hacl hfa h1 h2 hloc hih hv hw]

/-- **The residue node's value**: the ih value folded along the
arguments' readings, at the frame with the ih block dropped. -/
theorem interp_ihNode
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {nR F d r : Nat} (hr : r < nR)
    {as as1 as2 : List Expr} (hfa : ∀ a ∈ as, a.hasFvar = false)
    (h1 : FvarList (F + d) as1) (h2 : FvarList (F + nR + d) as2)
    {locals ihvals : List V} {ρ' : Nat → V}
    (hloc : locals.length = d) (hih : ihvals.length = nR)
    {B : AnnotTerm}
    (hB : denoteMeta acval env φ (F + nR + d)
      ((Expr.mkAppN (.bvar (d + nR - 1 - r))
        (as.map fun x => x.liftLooseBVars nR d)).instantiateList as2 0) = some B) :
    ∃ vs : List AnnotTerm,
      DenoteMetaSpine acval env φ (F + d) (as.map (·.instantiateList as1 0)) vs ∧
      interp V (consList locals (consList ihvals ρ')) B
        = (vs.map (interp V (consList locals ρ'))).foldl SetTheory.app (ihvals.getD r pt) := by
  rw [instantiateList_mkAppN] at hB
  obtain ⟨fa, ws, hfa', hsp, rfl⟩ := denoteMeta_mkAppN_inv hB
  -- the head: the ih opener's own value
  obtain ⟨ty, hty⟩ := h2.bvar_lt (j := d + nR - 1 - r) (by omega)
  rw [hty, denoteMeta_fvar] at hfa'
  obtain rfl : fa = .bvar (d + nR - 1 - r) := by
    rw [← Option.some.inj hfa',
      show F + nR + d - 1 - (F + nR + d - 1 - (d + nR - 1 - r)) = d + nR - 1 - r from by omega]
  have hhead : interp V (consList locals (consList ihvals ρ')) (.bvar (d + nR - 1 - r))
      = ihvals.getD r pt := by
    show consList locals (consList ihvals ρ') (d + nR - 1 - r) = _
    rw [show d + nR - 1 - r = (nR - 1 - r) + locals.length from by rw [hloc]; omega,
      consList_apply_add, consList_getD_of_lt _ _ _ (by omega), hih,
      show nR - 1 - (nR - 1 - r) = r from by omega]
  -- the arguments: their own readings
  rw [List.map_map] at hsp
  obtain ⟨vs, hvs, hmap⟩ := denoteMetaSpine_of_lift hacl h1 h2 hloc hih as ws hfa hsp
  refine ⟨vs, hvs, ?_⟩
  rw [interp_mkAppN, hhead, foldl_app_map, hmap]

/-- **The guarded call's value**, said of the STORED node alone: the
node reads to the ih value applied along the arguments' readings.
This is what the exact call comparison, `ihFunAV_fold` and the leaf's
own value (`blockRecAV_facts`) combine to give, and it is the ONLY
thing `IhNodeVal` still wants. -/
@[expose] def IhCallFold (V : Type uv) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) {envT : Env} (mT : EnvModel V envT)
    (φ : Name → Nat)
    (fr : ConLeche.BlockRuleFrame) (F : Nat) (ρ' : Nat → V) (ihvals : List V)
    (as2₀ : List Expr) : Prop :=
  ∀ (d : Nat) (locals : List V) (e : Expr) (r : Nat) (as as1 as2 : List Expr)
    (Δa : List AnnotTerm) (A : AnnotTerm) (vs ws : List AnnotTerm),
    e.hasFvar = false → e.looseBVarsBounded (F + d) = true →
    ConstsBound envT (Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
      (as.map fun x => x.liftLooseBVars fr.nR d)) →
    locals.length = d → FvarList (F + d) as1 → FvarList (F + fr.nR + d) as2 →
    as2₀ <:+ as2 → LocalsFit V acval env φ F ρ' locals as1 →
    WalkCtx V mT φ (F + fr.nR + d) (consList locals (consList ihvals ρ')) Δa as2 →
    ConLeche.blockIhCall? fr d e = some (r, as) →
    IhTyped envT (F + fr.nR + d)
      ((Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
        (as.map fun x => x.liftLooseBVars fr.nR d)).instantiateList as2 0) →
    denoteMeta acval env φ (F + d) (e.instantiateList as1 0) = some A →
    DenoteMetaSpine acval env φ (F + d) (as.map (·.instantiateList as1 0)) vs →
    DenoteMetaSpine mT.acval envT φ (F + fr.nR + d)
      (as.map fun x => (x.liftLooseBVars fr.nR d).instantiateList as2 0) ws →
    interp V (consList locals ρ') A
      = (vs.map (interp V (consList locals ρ'))).foldl SetTheory.app (ihvals.getD r pt)

/-- **O-1's premise, reduced**: `IhNodeVal` from `IhCallFold`.  The
residue side is computed (`interp_ihNode`); what the model still owes
is the stored node's value. -/
theorem ihNodeVal_of_fold
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {envT : Env} {mT : EnvModel V envT}
    (hmono : ∀ (D : Nat) (y : Expr) (ya : AnnotTerm), ConstsBound envT y →
      denoteMeta mT.acval envT φ D y = some ya → denoteMeta acval env φ D y = some ya)
    {fr : ConLeche.BlockRuleFrame} {F : Nat} {ρ' : Nat → V} {ihvals : List V}
    (hih : ihvals.length = fr.nR)
    (hfold : IhCallFold V acval env mT φ fr F ρ' ihvals as2₀) :
    IhNodeVal V acval env mT φ fr F ρ' ihvals as2₀ := by
  intro d locals e r as as1 as2 Δa A B he hb hcbe hloc h1 h2 hsx hlf hW hc hA hB hty
  have hB' := hmono _ _ _ (constsBound_instantiateList h2 hW.2.2.2.2.2.1 _
    (hasFvar_mkAppN rfl (by
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      rw [hasFvar_liftLooseBVars]
      obtain ⟨maj, hmaj, hsub⟩ := blockIhCall?_args_sub hc
      exact hasFvar_of_mem_getAppArgs (hasFvar_of_mem_getAppArgs he maj hmaj) z (hsub ▸ hz)))
    hcbe 0) hB
  obtain ⟨C⟩ := ConLeche.blockIhCall?_run hc
  have hr : r < fr.nR := pairIdxOf?_lt C.hkey
  obtain ⟨maj, hmaj, rfl⟩ := blockIhCall?_args_sub hc
  have hfa : ∀ a ∈ maj.getAppArgs, a.hasFvar = false :=
    hasFvar_of_mem_getAppArgs (hasFvar_of_mem_getAppArgs he maj hmaj)
  obtain ⟨vs, hvs, hval⟩ := interp_ihNode hacl hr hfa h1 h2 hloc hih hB'
  rw [instantiateList_mkAppN] at hB
  obtain ⟨-, ws, -, hws, -⟩ := denoteMeta_mkAppN_inv hB
  rw [List.map_map] at hws
  rw [hval, hfold d locals e r maj.getAppArgs as1 as2 Δa A vs ws he hb hcbe hloc h1 h2 hsx hlf hW
    hc hty hA hvs hws]

/-! ## One step further: the STORED node is the GENERATED spine

`IhCallRun.heq` exports `e = expected` as TERMS (the kernel's
exact comparison), so the stored node's reading at the rule's frame IS the
generated call's — `congrArg` through the opening.  That removes
`blockIhCall?` from the obligation altogether and leaves a statement
about `blockIhSpinePis` alone: the shape the reading batteries
(`denoteMeta_instPisAtLift_peel`, and `FixRecRead`'s `structIdxAt` /
`structTeleAt` lemmas at the one-member route) are written for. -/

/-- **The guarded call's value, said of the GENERATED spine.**  The ih
opener `r` of the key `(i, c')` is valued so that the generated call
`rec_{c'} x⃗ e⃗_i(a⃗) (f_i a⃗)`, read at the rule's frame, is the ih value
folded along `a⃗`'s readings.  This is `ihFunAV_fold` once the spine's
argument values are identified with the design's
`xs ++ (eis ++ [fap])`. -/
@[expose] def IhSpineFold (V : Type uv) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) {envT : Env} (mT : EnvModel V envT)
    (φ : Name → Nat)
    (fr : ConLeche.BlockRuleFrame) (F : Nat) (ρ' : Nat → V) (ihvals : List V)
    (as2₀ : List Expr) : Prop :=
  ∀ (d : Nat) (locals : List V) (nm : Name) (c' i r : Nat) (as as1 as2 : List Expr)
    (Δa : List AnnotTerm) (node expected : Expr) (A : AnnotTerm) (vs ws : List AnnotTerm),
    ConLeche.blockIhCall? fr d node = some (r, as) →
    node.hasFvar = false → node.looseBVarsBounded (F + d) = true →
    ConstsBound envT (Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
      (as.map fun x => x.liftLooseBVars fr.nR d)) →
    locals.length = d → FvarList (F + d) as1 → FvarList (F + fr.nR + d) as2 →
    as2₀ <:+ as2 → LocalsFit V acval env φ F ρ' locals as1 →
    WalkCtx V mT φ (F + fr.nR + d) (consList locals (consList ihvals ρ')) Δa as2 →
    ConLeche.nameIdxOf? fr.recNames nm = some c' →
    ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r →
    as.length = (fr.teleOf i).length →
    Expr.instPisAtLift as
      (ConLeche.blockIhSpinePis nm fr.rlvls fr.pw fr.nP fr.rP fr.nF i d
        (fr.teleOf i) (fr.idxOf i)) = some expected →
    node = expected →
    IhTyped envT (F + fr.nR + d)
      ((Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
        (as.map fun x => x.liftLooseBVars fr.nR d)).instantiateList as2 0) →
    denoteMeta acval env φ (F + d) (expected.instantiateList as1 0) = some A →
    DenoteMetaSpine acval env φ (F + d) (as.map (·.instantiateList as1 0)) vs →
    DenoteMetaSpine mT.acval envT φ (F + fr.nR + d)
      (as.map fun x => (x.liftLooseBVars fr.nR d).instantiateList as2 0) ws →
    interp V (consList locals ρ') A
      = (vs.map (interp V (consList locals ρ'))).foldl SetTheory.app (ihvals.getD r pt)

/-- **`IhCallFold` from `IhSpineFold`** — the stored node IS the
generated spine, so its opened reading is too. -/
theorem ihCallFold_of_spine {envT : Env} {mT : EnvModel V envT}
    {fr : ConLeche.BlockRuleFrame} {F : Nat} {ρ' : Nat → V}
    {ihvals : List V} (h : IhSpineFold V acval env mT φ fr F ρ' ihvals as2₀) :
    IhCallFold V acval env mT φ fr F ρ' ihvals as2₀ := by
  intro d locals e r as as1 as2 Δa A vs ws he hb hcbe hloc h1 h2 hsx hlf hW hc hty hA hvs hws
  obtain ⟨C⟩ := ConLeche.blockIhCall?_run hc
  have hexp := C.hexp
  rw [← C.heq] at hexp
  exact h d locals C.nm C.c' C.i r as as1 as2 Δa e e A vs ws hc he hb hcbe hloc h1 h2 hsx hlf
    hW C.hnm C.hkey C.haslen hexp rfl hty hA hvs hws

/-- **O-1's premise, from the generated spine alone.**  The composite:
`interp_abstractIh`'s `hcall` follows from a statement that mentions
neither `abstractIh` nor `blockIhCall?` — only `blockIhSpinePis`, the
frame, and the ih values. -/
theorem ihNodeVal_of_spine
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {envT : Env} {mT : EnvModel V envT}
    (hmono : ∀ (D : Nat) (y : Expr) (ya : AnnotTerm), ConstsBound envT y →
      denoteMeta mT.acval envT φ D y = some ya → denoteMeta acval env φ D y = some ya)
    {fr : ConLeche.BlockRuleFrame} {F : Nat} {ρ' : Nat → V} {ihvals : List V}
    (hih : ihvals.length = fr.nR) (h : IhSpineFold V acval env mT φ fr F ρ' ihvals as2₀) :
    IhNodeVal V acval env mT φ fr F ρ' ihvals as2₀ :=
  ihNodeVal_of_fold hacl hmono hih (ihCallFold_of_spine h)

/-- **The ascending frame, split in four.**  The reading battery is
stated over `P ++ X ++ F ++ I` — the parameters, the recursor's
arbitrary stretch, the constructor's fields and the `ih` openers
standing so far — with each part's fvar indices pinned.  Any ascending
frame of the right length splits that way, so the check's single
opening list needs no structure of its own. -/
theorem ascFrame_split {L : List Expr} {a b c e : Nat}
    (hL : L.length = a + b + c + e)
    (hidx : ∀ (k : Nat) (x : Expr), L[k]? = some x → ∃ ty, x = Expr.fvar k ty) :
    ∃ P X F I : List Expr, L = P ++ X ++ F ++ I ∧
      P.length = a ∧ X.length = b ∧ F.length = c ∧ I.length = e ∧
      (∀ (k : Nat) (x : Expr), P[k]? = some x → ∃ ty, x = Expr.fvar k ty) ∧
      (∀ (k : Nat) (x : Expr), X[k]? = some x → ∃ ty, x = Expr.fvar (a + k) ty) ∧
      (∀ (k : Nat) (x : Expr), F[k]? = some x → ∃ ty, x = Expr.fvar (a + b + k) ty) ∧
      (∀ (k : Nat) (x : Expr), I[k]? = some x → ∃ ty, x = Expr.fvar (a + b + c + k) ty) := by
  refine ⟨L.take a, (L.drop a).take b, (L.drop (a + b)).take c, L.drop (a + b + c), ?_,
    by rw [List.length_take]; omega,
    by rw [List.length_take, List.length_drop]; omega,
    by rw [List.length_take, List.length_drop]; omega,
    by rw [List.length_drop]; omega, ?_, ?_, ?_, ?_⟩
  · rw [← List.take_add, ← List.take_add, List.take_append_drop]
  · intro k x hx
    rw [List.getElem?_take] at hx
    split at hx
    · exact hidx k x hx
    · exact nomatch hx
  · intro k x hx
    rw [List.getElem?_take] at hx
    split at hx
    · rw [List.getElem?_drop] at hx
      exact (hidx (a + k) x hx).imp fun ty hty => by rw [hty]
    · exact nomatch hx
  · intro k x hx
    rw [List.getElem?_take] at hx
    split at hx
    · rw [List.getElem?_drop] at hx
      exact (hidx (a + b + k) x hx).imp fun ty hty => by rw [hty]
    · exact nomatch hx
  · intro k x hx
    rw [List.getElem?_drop] at hx
    exact (hidx (a + b + c + k) x hx).imp fun ty hty => by rw [hty]

/-! ## The generated guarded call, READ

The block's `blockIhSpinePis` is `denoteMeta_ihSpineAt`
(`Model/Inductives/FixRecRead.lean`) at a CALLEE `.const` head with the
rule's own prefix variables in front — the one-member route's `ih`
domain is the same theorem at the MOTIVE.  This is that instance, at
the check's own opening list. -/

variable {V : Type uv} [SetTheory V]

/-- **The reading of the generated guarded call's Π-telescope.** -/
theorem denoteMeta_blockIhSpinePis {env : Env} {m : EnvModel V env} {ψ : Name → Nat}
    {nP nF o rP d i : Nat} {pw : ConLeche.PropWhen} {cty : Expr}
    {tl : List (Nat × Nat × AnnotTerm)} {Eis : List AnnotTerm}
    {fvs : List Expr} {cr : Expr}
    (hop0 : ConLeche.openPisAtFvars (nP + nF) cty 0 = some (fvs, cr))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (nP + nF)).isSome = true) (hi : i < nF)
    (hfr : FieldReadAt m ψ nP nF i cty fvs tl Eis)
    (ho : rP - nP = o)
    {as1 : List Expr} (h1 : FvarList (nP + o + nF + d) as1)
    {nm : Name} {rlvls : List Level} {ci : ConstantInfo}
    (hfind : env.find? nm = some ci)
    (hlvl : rlvls.length = ci.toConstantVal.levelParams.length) :
    denoteMeta m.acval env ψ (nP + o + nF + d)
        ((ConLeche.blockIhSpinePis nm rlvls pw nP rP nF i d
            (ConLeche.structFieldTeleOf cty nP nF i)
            (ConLeche.structFieldIdxOf cty nP nF i)).instantiateList as1 0)
      = some (mkPisAV (ihTeleAtR nF o i d (rebit (pwBit ψ pw) tl))
          (AnnotTerm.mkAppN (m.acval nm (Level.substFn ψ ci.toConstantVal.levelParams rlvls))
            (((List.range rP).map fun l =>
                AnnotTerm.bvar (d + (ConLeche.structFieldTeleOf cty nP nF i).length + nF
                  + rP - 1 - l))
              ++ Eis.map (ihIdxAtM nF o i d (ConLeche.structFieldTeleOf cty nP nF i).length)
              ++ [AnnotTerm.mkAppN
                    (.bvar (nF - 1 - i + d + (ConLeche.structFieldTeleOf cty nP nF i).length))
                    (teleVarsAV (ConLeche.structFieldTeleOf cty nP nF i).length)]))) := by
  have hE : 0 < nP + o + nF + d := by omega
  rw [instantiateList_eq_instSeq_of_fvarList h1 hE]
  obtain ⟨P, X, F, I, hLsplit, hP, hX, hF, hI, hidxP, hidxX, hidxF, hidxI⟩ :=
    ascFrame_split (a := nP) (b := o) (c := nF) (e := d) h1.reverse_length h1.reverse_idx
  rw [hLsplit]
  have hLlen : (P ++ X ++ F ++ I).length = nP + o + nF + d := by
    rw [List.length_append, List.length_append, List.length_append, hP, hX, hF, hI]
  have hLidx : ∀ (k : Nat) (x : Expr), (P ++ X ++ F ++ I)[k]? = some x →
      ∃ ty, x = Expr.fvar k ty := by rw [← hLsplit]; exact h1.reverse_idx
  have hhd : denoteMeta m.acval env ψ
      (nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length)
      (Expr.instSeq (P ++ X ++ F ++ I ++ ConLeche.Verify.openFvars (nP + o + nF + d)
          (ConLeche.structFieldTeleOf cty nP nF i).length)
        (nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length - 1)
        (.const nm rlvls))
      = some (m.acval nm (Level.substFn ψ ci.toConstantVal.levelParams rlvls)) := by
    rw [Expr.instSeq_eq_self _ _ (by rfl), denoteMeta_const hfind hlvl]
  have hpre : DenoteMetaSpine m.acval env ψ
      (nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length)
      ((ConLeche.blockRulePrefixVars rP nF
          (d + (ConLeche.structFieldTeleOf cty nP nF i).length)).map
        (Expr.instSeq (P ++ X ++ F ++ I ++ ConLeche.Verify.openFvars (nP + o + nF + d)
            (ConLeche.structFieldTeleOf cty nP nF i).length)
          (nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length - 1)))
      ((List.range rP).map fun l =>
        AnnotTerm.bvar (d + (ConLeche.structFieldTeleOf cty nP nF i).length + nF + rP - 1 - l)) := by
    unfold ConLeche.blockRulePrefixVars
    rw [List.map_map]
    simp only [Function.comp_def]
    refine DenoteMetaSpine.of_map (List.range rP) fun l hl => ?_
    have hlt : d + (ConLeche.structFieldTeleOf cty nP nF i).length + nF + rP - 1 - l
        < nP + o + nF + d + (ConLeche.structFieldTeleOf cty nP nF i).length := by
      rw [List.mem_range] at hl; omega
    exact denoteMeta_instSeq_ext_bvar hLlen hLidx hlt
  have h := denoteMeta_ihSpineAt (pw := pw) (o := o) (l := d) hop0 hCf hCb hstripC hi hfr
    hP hX hF hI hidxP hidxX hidxF hidxI hhd hpre
  rw [ConLeche.blockIhSpinePis, ho]
  exact h

/-! ## The peel, transported to the OPENED frame

`denoteMeta_instPisAtLift_peel` (`BlockRecRead.lean`) reads an
`instPisAtLift` at bvar-CLOSED arguments — which the call's arguments
are once the rule body is opened, and are NOT before.  The check's
`instPisAtLift as (blockIhSpinePis …) = some expected` is a fact about
the UNOPENED terms, so it has to be transported, and the per-binder
commutation that does it already exists:
`Expr.instSeq_instantiate1Lift` (`Verify/Subst.lean`) — "a
capture-avoiding substitution followed by the ambient spine is the
plain substitution at the already-instantiated argument".  Three small
lemmas turn it into the statement `instPisAtLift` needs. -/

theorem instSeq_forallE : ∀ (sp : List Expr) (t : Nat), sp.length = t + 1 →
    ∀ (dom body : Expr) (mt : ConLeche.BinderMeta),
      Expr.instSeq sp t (.forallE dom body mt)
        = .forallE (Expr.instSeq sp t dom) (Expr.instSeq sp (t + 1) body) mt
  | [], t, hlen, _, _, _ => absurd hlen (by simp)
  | s :: ss, t, hlen, dom, body, mt => by
    have hss : ss.length = t := by simpa using hlen
    cases t with
    | zero =>
      obtain rfl : ss = [] := List.eq_nil_of_length_eq_zero hss
      rfl
    | succ t' =>
      show Expr.instSeq ss t' ((Expr.forallE dom body mt).instantiate1 s (t' + 1)) = _
      rw [Expr.instantiate1, instSeq_forallE ss t' hss]
      rfl

/-- **The capture-avoiding telescope peel commutes with the frame's
opening.**  This is what transports the check's own
`instPisAtLift as (blockIhSpinePis …) = some expected` to the frame
the model reads at. -/
theorem instPisAtLift_instSeq {sp : List Expr} {t : Nat}
    (hsp : ∀ s ∈ sp, s.looseBVarsBounded 0 = true) (hlen : sp.length = t + 1) :
    ∀ (as : List Expr), (∀ a ∈ as, a.looseBVarsBounded (t + 1) = true) →
      ∀ {ty rest : Expr}, Expr.instPisAtLift as ty = some rest →
        Expr.instPisAtLift (as.map (Expr.instSeq sp t)) (Expr.instSeq sp t ty)
          = some (Expr.instSeq sp t rest)
  | [], _, ty, rest, h => by
    obtain rfl : ty = rest := Option.some.inj h
    rfl
  | a :: as, ha, ty, rest, h => by
    match ty, h with
    | .forallE dom body mt, h =>
      rw [Expr.instPisAtLift] at h
      have hab : a.looseBVarsBounded (t + 1) = true := ha a List.mem_cons_self
      have hcl : (Expr.instSeq sp t a).looseBVarsBounded 0 = true :=
        looseBVarsBounded_instSeq sp t hsp hlen hab
      have hcomm := ConLeche.Expr.instSeq_instantiate1Lift sp t hsp hlen hab body 0
      simp only [Nat.zero_add] at hcomm
      rw [List.map_cons, instSeq_forallE sp t hlen, Expr.instPisAtLift,
        ConLeche.Expr.instantiate1Lift_eq_instantiate1 hcl, ← hcomm]
      exact instPisAtLift_instSeq hsp hlen as
        (fun x hx => ha x (List.mem_cons_of_mem _ hx)) h

/-! ## The peel, evaluated

`AnnotTerm.peelPis` of a `mkPisAV` tower along a spine of its own
length is the body's instantiation sequence
(`peelPis_of_piTeleAV` at `piTeleAV_mkPisAV`), and `interp_instSeq`
evaluates that at the chain — which IS `consList` of the spine's
values, since `chain` is `consN` of them and `consN` is `consList`
(`consN_eq_consList`).  So the whole peel is one `interp` equation. -/

theorem chain_eq_consList (ρ : Nat → V) (ws : List AnnotTerm) :
    chain V ρ ws = consList (ws.map (interp V ρ)) ρ :=
  consN_eq_consList _ _

/-- **The peel, evaluated**: a Π-tower's reading peeled along a spine
of its own length reads as the body at the frame extended by the
spine's values. -/
theorem interp_peelPis_mkPisAV {tlA : List (Nat × Nat × AnnotTerm)} {BodyA A : AnnotTerm}
    {vs : List AnnotTerm} (hlen : vs.length = tlA.length)
    (hpeel : ConLeche.Model.AnnotTerm.peelPis (mkPisAV tlA BodyA) vs = some A)
    (σ : Nat → V) :
    interp V σ A = interp V (consList (vs.map (interp V σ)) σ) BodyA := by
  rw [peelPis_of_piTeleAV tlA.length (piTeleAV_mkPisAV tlA BodyA) hlen] at hpeel
  obtain rfl : A = ConLeche.Model.AnnotTerm.instSeq vs (tlA.length - 1) BodyA :=
    (Option.some.inj hpeel).symm
  rw [← hlen, interp_instSeq, chain_eq_consList]

/-! ## The `d`-shift: the generated spine at ih position `d` is the
design's spine at `0`, lifted

`denoteMeta_blockIhSpinePis` produces the guarded call's reading at ih
position `d` — `ihIdxAtM nF o i d m`, the applied field at
`bvar (nF - 1 - i + d + m)` and the prefix at
`bvar (d + m + nF + rP - 1 - l)`.  The design's data
(`ihFunAV`, `prefVarsAV`) sit at `d = 0`, read at an environment with
no `locals` block.  The two are related by `AnnotTerm.liftN d · m`,
whose environment half is `shiftE_consList_ih` — so these three
lemmas are the whole of the `d` bookkeeping. -/

theorem liftN_bvar_lt {q k n : Nat} (h : q < k) :
    (AnnotTerm.bvar q).liftN n k = .bvar q := by
  simp only [AnnotTerm.liftN_bvar]; rw [if_pos h]

theorem liftN_bvar_ge {q k n : Nat} (h : k ≤ q) :
    (AnnotTerm.bvar q).liftN n k = .bvar (q + n) := by
  simp only [AnnotTerm.liftN_bvar]; rw [if_neg (by omega)]

/-- **The lift exchange** the `ih` index expression needs: a lift at
the telescope's cut and a lift at an OUTER cut commute, the outer cut
moving by the inner lift's amount. -/
theorem liftN_shift_comm {A o d : Nat} :
    ∀ (E : AnnotTerm) (m c : Nat), m ≤ c →
      ((E.liftN A m).liftN o c).liftN d m = (E.liftN (A + d) m).liftN o (c + d)
  | .bvar q, m, c, hmc => by
    rcases Nat.lt_or_ge q m with hq | hq
    · rw [liftN_bvar_lt hq, liftN_bvar_lt (show q < c from by omega), liftN_bvar_lt hq,
        liftN_bvar_lt hq, liftN_bvar_lt (show q < c + d from by omega)]
    · rcases Nat.lt_or_ge (q + A) c with hc | hc
      · rw [liftN_bvar_ge hq, liftN_bvar_lt hc, liftN_bvar_ge (show m ≤ q + A from by omega),
          liftN_bvar_ge hq, liftN_bvar_lt (show q + (A + d) < c + d from by omega)]
        congr 1; omega
      · rw [liftN_bvar_ge hq, liftN_bvar_ge hc,
          liftN_bvar_ge (show m ≤ q + A + o from by omega), liftN_bvar_ge hq,
          liftN_bvar_ge (show c + d ≤ q + (A + d) from by omega)]
        congr 1; omega
  | .sort _, _, _, _ | .const .., _, _, _ | .prf, _, _, _ => rfl
  | .app f a, m, c, hmc => by
    simp only [AnnotTerm.liftN_app, liftN_shift_comm f m c hmc, liftN_shift_comm a m c hmc]
  | .eqE a b, m, c, hmc => by
    simp only [AnnotTerm.liftN_eqE, liftN_shift_comm a m c hmc, liftN_shift_comm b m c hmc]
  | .fst e, m, c, hmc => by
    simp only [AnnotTerm.liftN_fst, liftN_shift_comm e m c hmc]
  | .snd e, m, c, hmc => by
    simp only [AnnotTerm.liftN_snd, liftN_shift_comm e m c hmc]
  | .lam u A b, m, c, hmc => by
    simp only [AnnotTerm.liftN_lam, liftN_shift_comm A m c hmc,
      show c + d + 1 = (c + 1) + d from by omega,
      liftN_shift_comm b (m + 1) (c + 1) (by omega)]
  | .pi u v A B, m, c, hmc => by
    simp only [AnnotTerm.liftN_pi, liftN_shift_comm A m c hmc,
      show c + d + 1 = (c + 1) + d from by omega,
      liftN_shift_comm B (m + 1) (c + 1) (by omega)]

/-- **`ihIdxAtM`'s `d`-shift.** -/
theorem ihIdxAtM_shift (nF o i d m : Nat) (E : AnnotTerm) :
    ihIdxAtM nF o i d m E = (ihIdxAtM nF o i 0 m E).liftN d m := by
  unfold ihIdxAtM
  rw [show nF - i + 0 = nF - i from by omega, show nF + 0 + m = nF + m from by omega,
    liftN_shift_comm (A := nF - i) (o := o) (d := d) E m (nF + m) (by omega),
    show nF + m + d = nF + d + m from by omega]

/-- **The telescope's own variables are below the cut**, so the shift
leaves them alone. -/
theorem teleVarsAV_liftN (d m : Nat) :
    (teleVarsAV m).map (AnnotTerm.liftN d · m) = teleVarsAV m := by
  unfold teleVarsAV
  rw [List.map_map]
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  show (AnnotTerm.bvar (m - 1 - k)).liftN d m = _
  exact liftN_bvar_lt (by omega)

/-- **The applied field's `d`-shift.** -/
theorem fieldApp_shift (nF i d m : Nat) :
    AnnotTerm.mkAppN (.bvar (nF - 1 - i + d + m)) (teleVarsAV m)
      = (AnnotTerm.mkAppN (.bvar (nF - 1 - i + 0 + m)) (teleVarsAV m)).liftN d m := by
  rw [liftN_mkAppN, teleVarsAV_liftN, liftN_bvar_ge (show m ≤ nF - 1 - i + 0 + m from by omega)]
  congr 2
  omega

/-- **The prefix variables' `d`-shift**: the reading
`denoteMeta_blockIhSpinePis` produces is the design's `prefVarsAV`,
lifted. -/
theorem prefVars_shift (rP nF d m : Nat) :
    ((List.range rP).map fun l => AnnotTerm.bvar (d + m + nF + rP - 1 - l))
      = (prefVarsAV rP (nF + m)).map (AnnotTerm.liftN d · m) := by
  unfold prefVarsAV
  rw [List.map_map]
  apply List.map_congr_left
  intro l hl
  rw [List.mem_range] at hl
  show AnnotTerm.bvar _ = (AnnotTerm.bvar (nF + m + rP - 1 - l)).liftN d m
  rw [liftN_bvar_ge (show m ≤ nF + m + rP - 1 - l from by omega)]
  congr 1
  omega

/-! ## The `ih` LEVEL's shift, at the PEEL

`blockIhPis` generates the `r`-th `ih` opener at level `l = r`, so the
run peels the CALLEE's stored type at the `l = r` spine
(`blockRuleHconcl_of`, `BlockRecOpenerRead.lean`) — while every
consumer of the opener's DOMAIN wants the `l = 0` tower lifted past
the `r` earlier openers, because that lift is what cancels their
values (the `liftN r 0` of `blockGraphIhF_run`, through
`interp_liftN_ihvals`).  The three component lemmas above move the
SPINE between the two levels; these move the PEEL, so the `l = r`
conclusion IS the `l = 0` conclusion lifted at the telescope's own
cut.

That is the last syntactic step of the fused opener reading
(`blockKitIhKey_run`, `BlockKitIhRun.lean`): its `BlockRuleConclAt`
conjunct is
stated at `l = 0` — it has to be, `blockRecCa_value` reads it at the
frame the telescope's values sit on — and the run hands out `l = r`. -/

/-- **A lift passes an instantiation.**  `AnnotTerm`'s missing
commutation at a cut ABOVE the substituted variable: substituting at
`k` and then lifting at `m ≥ k` is lifting at `m + 1` — the cut the
peeled binder pushed up — and substituting the lifted value.  The
`q = k` case is the only one with content, and it is
`liftN_shift_comm` at `A = 0`. -/
theorem liftN_inst_comm :
    ∀ (E a : AnnotTerm) (r k m : Nat), k ≤ m →
      (E.inst a k).liftN r m = (E.liftN r (m + 1)).inst (a.liftN r (m - k)) k
  | .bvar q, a, r, k, m, hkm => by
    rcases Nat.lt_trichotomy q k with hq | hq | hq
    · rw [AnnotTerm.inst_bvar, if_pos hq, liftN_bvar_lt (show q < m from by omega),
        liftN_bvar_lt (show q < m + 1 from by omega), AnnotTerm.inst_bvar, if_pos hq]
    · subst hq
      rw [AnnotTerm.inst_bvar, if_neg (Nat.lt_irrefl q), if_pos rfl,
        liftN_bvar_lt (show q < m + 1 from by omega), AnnotTerm.inst_bvar,
        if_neg (Nat.lt_irrefl q), if_pos rfl]
      have h := liftN_shift_comm (A := 0) (o := r) (d := q) a 0 (m - q) (Nat.zero_le _)
      rw [AnnotTerm.liftN_zero, Nat.zero_add, show m - q + q = m from by omega] at h
      exact h.symm
    · rw [AnnotTerm.inst_bvar, if_neg (show ¬ q < k from by omega),
        if_neg (show ¬ q = k from by omega)]
      by_cases h1 : q < m + 1
      · rw [liftN_bvar_lt (show q - 1 < m from by omega), liftN_bvar_lt h1,
          AnnotTerm.inst_bvar, if_neg (show ¬ q < k from by omega),
          if_neg (show ¬ q = k from by omega)]
      · rw [liftN_bvar_ge (show m ≤ q - 1 from by omega),
          liftN_bvar_ge (show m + 1 ≤ q from by omega), AnnotTerm.inst_bvar,
          if_neg (show ¬ q + r < k from by omega), if_neg (show ¬ q + r = k from by omega)]
        congr 1
        omega
  | .sort _, _, _, _, _, _ | .const .., _, _, _, _, _ | .prf, _, _, _, _, _ => rfl
  | .app f b, a, r, k, m, hkm => by
    simp only [AnnotTerm.inst_app, AnnotTerm.liftN_app,
      liftN_inst_comm f a r k m hkm, liftN_inst_comm b a r k m hkm]
  | .eqE b c, a, r, k, m, hkm => by
    simp only [AnnotTerm.inst_eqE, AnnotTerm.liftN_eqE,
      liftN_inst_comm b a r k m hkm, liftN_inst_comm c a r k m hkm]
  | .fst e, a, r, k, m, hkm => by
    simp only [AnnotTerm.inst_fst, AnnotTerm.liftN_fst, liftN_inst_comm e a r k m hkm]
  | .snd e, a, r, k, m, hkm => by
    simp only [AnnotTerm.inst_snd, AnnotTerm.liftN_snd, liftN_inst_comm e a r k m hkm]
  | .lam u A b, a, r, k, m, hkm => by
    simp only [AnnotTerm.inst_lam, AnnotTerm.liftN_lam,
      liftN_inst_comm A a r k m hkm,
      liftN_inst_comm b a r (k + 1) (m + 1) (by omega),
      show m + 1 - (k + 1) = m - k from by omega]
  | .pi u v A B, a, r, k, m, hkm => by
    simp only [AnnotTerm.inst_pi, AnnotTerm.liftN_pi,
      liftN_inst_comm A a r k m hkm,
      liftN_inst_comm B a r (k + 1) (m + 1) (by omega),
      show m + 1 - (k + 1) = m - k from by omega]

/-- **The Π-peel's lift is REVERSIBLE**: from the peel of a LIFTED
tower along a lifted spine back to the peel of the tower itself.

A consumer that states its peel at `l = 0` and a CHECK that generates
the tower at the key's own level `l = r` meet here: the run produces
the peel of the LIFTED spine and the premise wants the peel of the
spine itself.  It is reversible because `liftN` preserves the head constructor —
`(.pi u v A B).liftN r m` is a `.pi` and nothing else lifts to one —
so at every step the peel's own case analysis is decided on `T`
rather than on `T.liftN r m`, and the residual comes back by
`liftN_inst_comm` exactly as it went. -/
theorem peelPis_liftN_inv (r m : Nat) :
    ∀ (as : List AnnotTerm) {T C' : AnnotTerm},
      ConLeche.Model.AnnotTerm.peelPis (T.liftN r m)
          (as.map (AnnotTerm.liftN r · m))
        = some C' →
      ∃ C, ConLeche.Model.AnnotTerm.peelPis T as = some C ∧ C' = C.liftN r m := by
  intro as
  induction as with
  | nil =>
    intro T C' h
    exact ⟨T, rfl, (Option.some.inj h).symm⟩
  | cons a as ih =>
    intro T C' h
    match T with
    | .pi u v A B =>
      have h' : ConLeche.Model.AnnotTerm.peelPis
          ((B.liftN r (m + 1)).inst (a.liftN r m) 0)
          (as.map (AnnotTerm.liftN r · m)) = some C' := h
      have hc := liftN_inst_comm B a r 0 m (Nat.zero_le _)
      rw [Nat.sub_zero] at hc
      rw [← hc] at h'
      exact ih h'
    | .bvar _ => exact absurd (show (none : Option AnnotTerm) = some C' from h) (by simp)
    | .sort _ => exact absurd (show (none : Option AnnotTerm) = some C' from h) (by simp)
    | .const .. => exact absurd (show (none : Option AnnotTerm) = some C' from h) (by simp)
    | .app .. => exact absurd (show (none : Option AnnotTerm) = some C' from h) (by simp)
    | .lam .. => exact absurd (show (none : Option AnnotTerm) = some C' from h) (by simp)
    | .eqE .. => exact absurd (show (none : Option AnnotTerm) = some C' from h) (by simp)
    | .fst _ => exact absurd (show (none : Option AnnotTerm) = some C' from h) (by simp)
    | .snd _ => exact absurd (show (none : Option AnnotTerm) = some C' from h) (by simp)
    | .prf => exact absurd (show (none : Option AnnotTerm) = some C' from h) (by simp)

/-- **The prefix variables' `r`-shift**, at `paramBvarsAt`'s spelling
— `prefVars_shift`'s twin in the form `BlockRuleConclAt` states its
peel in. -/
theorem paramBvarsAt_shift (rP nF m r : Nat) :
    (paramBvarsAt rP (rP + nF + m)).map (AnnotTerm.liftN r · m)
      = (List.range rP).map fun l => AnnotTerm.bvar (r + m + nF + rP - 1 - l) := by
  unfold paramBvarsAt
  rw [List.map_map]
  refine List.map_congr_left fun l hl => ?_
  rw [List.mem_range] at hl
  show (AnnotTerm.bvar (rP + nF + m - 1 - l)).liftN r m = _
  rw [liftN_bvar_ge (show m ≤ rP + nF + m - 1 - l from by omega)]
  congr 1
  omega

/-! ## `IhSpineFold`, discharged from the run

The wide assembly: `denoteMeta_blockIhSpinePis` (the generated call's
Π-tower, read) → `instPisAtLift_instSeq` (the check's peel, moved to
the opened frame) → `denoteMeta_instPisAtLift_peel` → 
`interp_peelPis_mkPisAV` (the peel, evaluated) → the four `d`-shift
rewrites under `interp_liftN` and `shiftE_consList_ih` →
`ihFunAV_fold`.

**The one fact no syntax produces** is `hR`: `ihFunAV`'s head is the
CHAIN COMPONENT `bvar (… + (K - 1 - c'))` while the reading's head is
the CONSTANT `acval rec_{c'}`.  They are never equal as terms; what
closes the gap is the LEAF's value (`blockRecAV_facts`), carried here
as `hleaf`. -/

theorem ihSpineFold_blockRec {env : Env} {mo : EnvModel V env} {ψ : Name → Nat}
    {envT : Env} {mT : EnvModel V envT}
    {fr : ConLeche.BlockRuleFrame} {F o ℓ K : Nat}
    {cty : Expr} {fvs : List Expr} {cr : Expr}
    {tlF : Nat → List (Nat × Nat × AnnotTerm)} {EisF : Nat → List AnnotTerm}
    {σchain : Nat → V} {xs fs : List V} {ihvals : List V}
    (hacl : ∀ (n : Name) (ψ' : Name → Nat) (k : Nat), (mo.acval n ψ').liftN 1 k = mo.acval n ψ')
    (hainst : ∀ (n : Name) (ψ' : Name → Nat) (y : AnnotTerm) (k : Nat),
      (mo.acval n ψ').inst y k = mo.acval n ψ')
    (hcl : ∀ (n : Name) (ψ' : Name → Nat) (ρ1 ρ2 : Nat → V),
      interp V ρ1 (mo.acval n ψ') = interp V ρ2 (mo.acval n ψ'))
    -- the frame's arithmetic
    (hF : fr.nP + o + fr.nF = F) (ho : fr.rP - fr.nP = o)
    (hxl : xs.length = fr.rP) (hfl : fs.length = fr.nF) (hℓ : ℓ ≠ 0)
    -- the constructor's type and its fields' readings
    (hop0 : ConLeche.openPisAtFvars (fr.nP + fr.nF) cty 0 = some (fvs, cr))
    (hCf : cty.hasFvar = false) (hCb : cty.looseBVarsBounded 0 = true)
    (hstripC : (cty.stripPis (fr.nP + fr.nF)).isSome = true)
    (htele : fr.teleOf = ConLeche.structFieldTeleOf cty fr.nP fr.nF)
    (hidx : fr.idxOf = ConLeche.structFieldIdxOf cty fr.nP fr.nF)
    -- the fields with an `ih` opener: the frame's `ihKeys` name exactly the
    -- RECURSIVE and REFLEXIVE ones (`pairIdxOf_blockIhKeys_kind`), and the
    -- constructors' stage supplies the package only there
    (hfld : ∀ (i c' r : Nat), ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r →
      FieldReadAt mo ψ fr.nP fr.nF i cty fvs (tlF i) (EisF i))
    -- the call's arguments live in the rule body's frame
    -- the generated Π-tower is a generated form: no free variable
    (hnofv : ∀ (d i : Nat) (nm : Name),
      (ConLeche.blockIhSpinePis nm fr.rlvls fr.pw fr.nP fr.rP fr.nF i d
        (fr.teleOf i) (fr.idxOf i)).hasFvar = false)
    -- the callee: stored, at the right level arity, and its leaf is the chain's component
    (hcallee : ∀ (nm : Name) (c' : Nat), ConLeche.nameIdxOf? fr.recNames nm = some c' →
      ∃ ci : ConstantInfo, env.find? nm = some ci ∧
        fr.rlvls.length = ci.toConstantVal.levelParams.length ∧
        interp V (consList (xs ++ fs) σchain)
            (mo.acval nm (Level.substFn ψ ci.toConstantVal.levelParams fr.rlvls))
          = σchain (K - 1 - c'))
    -- the field's index is in range, and the opener's value is the design's ih term
    (hi : ∀ (i c' r : Nat), ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r → i < fr.nF)
    (hihv : ∀ (i c' r : Nat), ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r →
      ihvals.getD r pt
        = interp V (consList (xs ++ fs) σchain)
            (ihFunAV ℓ K c' fr.rP fr.nF
              (ihTeleAtR fr.nF o i 0 (rebit (pwBit ψ fr.pw) (tlF i)))
              ((EisF i).map (ihIdxAtM fr.nF o i 0 (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length))
              (AnnotTerm.mkAppN
                (.bvar (fr.nF - 1 - i + 0 +
                  (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length))
                (teleVarsAV (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length))))
    -- The call's fit, at THE CALL the fold is at: the values the guarded
    -- call's OWN arguments read to fit the field whose `ih` opener the
    -- call abstracts to.  Three bounds are load-bearing — quantified
    -- over all value lists of the right length the fit is refutable,
    -- quantified over all fields `i` it asks
    -- the fit at a telescope the call never mentions, and quantified
    -- over all NODES it asks it of a call the rule body does not
    -- contain, which no run certifies.  The index facts are the first
    -- two ties: `nm` is the callee, `c'` its position in the block,
    -- and `(i, c')` the frame's key for the `ih` binder `r`.  The
    -- third is `IhTyped`: the residue's node was inferred by the rule
    -- stage's own run, which is what `certs_of_infer_mkAppN`
    -- (`BlockCallCerts.lean`) inverts.
    (hfit : ∀ (d i c' r : Nat) (nm : Name) (locals : List V) (node : Expr)
      (as as1 as2 : List Expr) (Δa : List AnnotTerm) (vs ws : List AnnotTerm),
      ConLeche.blockIhCall? fr d node = some (r, as) →
      node.hasFvar = false → node.looseBVarsBounded (F + d) = true →
      ConLeche.nameIdxOf? fr.recNames nm = some c' →
      ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r →
      locals.length = d → i < fr.nF →
      FvarList (F + d) as1 → FvarList (F + fr.nR + d) as2 →
      as2₀ <:+ as2 →
      LocalsFit V mo.acval env ψ F (consList (xs ++ fs) σchain) locals as1 →
      ConstsBound envT (Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
        (as.map fun x => x.liftLooseBVars fr.nR d)) →
      WalkCtx V mT ψ (F + fr.nR + d)
        (consList locals (consList ihvals (consList (xs ++ fs) σchain))) Δa as2 →
      IhTyped envT (F + fr.nR + d)
        ((Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
          (as.map fun x => x.liftLooseBVars fr.nR d)).instantiateList as2 0) →
      DenoteMetaSpine mo.acval env ψ (F + d) (as.map (·.instantiateList as1 0)) vs →
      DenoteMetaSpine mT.acval envT ψ (F + fr.nR + d)
        (as.map fun x => (x.liftLooseBVars fr.nR d).instantiateList as2 0) ws →
      (vs.map (interp V (consList locals (consList (xs ++ fs) σchain)))).length
        = (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length →
      SpineFit (consList (xs ++ fs) σchain)
        ((ihTeleAtR fr.nF o i 0 (rebit (pwBit ψ fr.pw) (tlF i))).map (·.2.2))
        (vs.map (interp V (consList locals (consList (xs ++ fs) σchain))))) :
    IhSpineFold V mo.acval env mT ψ fr F (consList (xs ++ fs) σchain) ihvals as2₀ := by
  intro d locals nm c' i r as as1 as2 Δa node expected A vs ws hcall hnodeF hnodeB hcbe hloc h1 h2f hsx hlf hW hnm hrpos hasl hexp hne htyN hA hvs hws
  have hiF : i < fr.nF := hi i c' r hrpos
  obtain ⟨ci, hfind, hlvl, hleafv⟩ := hcallee nm c' hnm
  obtain ⟨maj, hmaj, hasEq⟩ := blockIhCall?_args_sub hcall
  have hbnd : ∀ a ∈ as, a.looseBVarsBounded (F + d) = true ∧ a.hasFvar = false := by
    rw [hasEq]
    exact fun a ha =>
      ⟨bounded_of_mem_getAppArgs (bounded_of_mem_getAppArgs hnodeB maj hmaj) a ha,
        hasFvar_of_mem_getAppArgs (hasFvar_of_mem_getAppArgs hnodeF maj hmaj) a ha⟩
  have hnof := hnofv d i nm
  subst hF
  have hE : 0 < fr.nP + o + fr.nF + d := by omega
  -- the opening list, as the battery's ascending frame
  have hclos : ∀ x ∈ as1, x.looseBVarsBounded 0 = true := by
    intro x hx
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hx
    have hql : q < fr.nP + o + fr.nF + d := by
      rw [← h1.1]; exact (List.getElem?_eq_some_iff.mp hq).1
    obtain ⟨ty, hty⟩ := h1.2.1 q hql
    rw [hty] at hq
    rw [← Option.some.inj hq]
    rfl
  have hspcl : ∀ x ∈ as1.reverse, x.looseBVarsBounded 0 = true :=
    fun x hx => hclos x (List.mem_reverse.mp hx)
  have hsplen : as1.reverse.length = (fr.nP + o + fr.nF + d - 1) + 1 := by
    rw [h1.reverse_length]; omega
  have hopen : ∀ X : Expr,
      Expr.instSeq as1.reverse (fr.nP + o + fr.nF + d - 1) X = X.instantiateList as1 0 :=
    fun X => (instantiateList_eq_instSeq_of_fvarList h1 hE X).symm
  -- (1) the check's peel, moved to the opened frame
  have hpr : Expr.instPisAtLift (as.map (·.instantiateList as1 0))
      ((ConLeche.blockIhSpinePis nm fr.rlvls fr.pw fr.nP fr.rP fr.nF i d
        (fr.teleOf i) (fr.idxOf i)).instantiateList as1 0)
      = some (expected.instantiateList as1 0) := by
    have h := instPisAtLift_instSeq hspcl hsplen as
      (fun a ha => by rw [show fr.nP + o + fr.nF + d - 1 + 1 = fr.nP + o + fr.nF + d from by omega]
                      exact (hbnd a ha).1) hexp
    have hmap : as.map (Expr.instSeq as1.reverse (fr.nP + o + fr.nF + d - 1))
        = as.map (·.instantiateList as1 0) := List.map_congr_left fun a _ => hopen a
    rw [hmap, hopen, hopen] at h
    exact h
  -- (2) the generated Π-tower, read
  rw [htele] at hasl
  rw [htele, hidx] at hexp hpr hnof
  have hTy := denoteMeta_blockIhSpinePis (m := mo) (ψ := ψ) (nm := nm) (rlvls := fr.rlvls)
    (pw := fr.pw) (rP := fr.rP) (d := d) (i := i) hop0 hCf hCb hstripC hiF (hfld i c' r hrpos) ho h1
    hfind hlvl
  -- (3) the peel, read and evaluated
  obtain ⟨restA, hrest, hpeel⟩ := denoteMeta_instPisAtLift_peel
    hacl hainst (as.map (·.instantiateList as1 0)) hpr
    (wscoped_instantiateList h1 _ hnof 0)
    (fun a ha => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ha
      refine ⟨wscoped_instantiateList h1 y (hbnd y hy).2 0, ?_⟩
      rw [← hopen]
      exact looseBVarsBounded_instSeq as1.reverse _ hspcl hsplen
        (by rw [show fr.nP + o + fr.nF + d - 1 + 1 = fr.nP + o + fr.nF + d from by omega]
            exact (hbnd y hy).1))
    hTy hvs
  obtain rfl : restA = A := Option.some.inj (hrest.symm.trans hA)
  -- (4) the peel, evaluated
  have hvlen : vs.length = (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length := by
    rw [← hvs.length, List.length_map]; exact hasl
  have htlen : ∀ l : Nat, (ihTeleAtR fr.nF o i l (rebit (pwBit ψ fr.pw) (tlF i))).length
      = (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length := by
    intro l; rw [ihTeleAtR_length, rebit_length, (hfld i c' r hrpos).1]
  rw [interp_peelPis_mkPisAV (by rw [hvlen, htlen]) hpeel]
  -- (5) the `d`-shift, and the fold
  have hwlen : (vs.map (interp V (consList locals (consList (xs ++ fs) σchain)))).length
      = (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length := by
    rw [List.length_map]; exact hvlen
  have hshift : shiftE d (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length
      (consList (vs.map (interp V (consList locals (consList (xs ++ fs) σchain))))
        (consList locals (consList (xs ++ fs) σchain)))
      = consList (vs.map (interp V (consList locals (consList (xs ++ fs) σchain))))
          (consList (xs ++ fs) σchain) :=
    shiftE_consList_ih hwlen hloc
  have hlift : ∀ X : AnnotTerm,
      interp V (consList (vs.map (interp V (consList locals (consList (xs ++ fs) σchain))))
          (consList locals (consList (xs ++ fs) σchain)))
        (X.liftN d (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length)
      = interp V (consList (vs.map (interp V (consList locals (consList (xs ++ fs) σchain))))
          (consList (xs ++ fs) σchain)) X := by
    intro X; rw [interp_liftN, hshift]
  have hEisShift : (EisF i).map
        (ihIdxAtM fr.nF o i d (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length)
      = ((EisF i).map
          (ihIdxAtM fr.nF o i 0 (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length)).map
          (AnnotTerm.liftN d ·  (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length) := by
    rw [List.map_map]
    exact List.map_congr_left fun x _ => ihIdxAtM_shift _ _ _ _ _ x
  rw [hihv i c' r hrpos,
    ihFunAV_fold (V := V) (ℓ := ℓ) (K := K) (c' := c') (eis := (EisF i).map
        (ihIdxAtM fr.nF o i 0 (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length))
      hℓ hleafv.symm hxl hfl (by rw [List.length_map, hvlen, htlen])
      (hfit d i c' r nm locals node as as1 as2 Δa vs ws hcall hnodeF hnodeB hnm hrpos hloc hiF
        h1 h2f hsx hlf hcbe hW htyN hvs hws hwlen),
    interp_mkAppN, foldl_app_map, hcl nm _ _ (consList (xs ++ fs) σchain), hleafv,
    prefVars_shift, fieldApp_shift, hEisShift,
    show consList (xs ++ fs ++ vs.map (interp V (consList locals (consList (xs ++ fs) σchain))))
          σchain
        = consList (vs.map (interp V (consList locals (consList (xs ++ fs) σchain))))
            (consList (xs ++ fs) σchain) from
      consList_append _ _ _]
  simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
    hlift]
  have hbslen : (fs ++ vs.map (interp V (consList locals (consList (xs ++ fs) σchain)))).length
      = fr.nF + (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length := by
    rw [List.length_append, hfl, hwlen]
  have hpref : (prefVarsAV fr.rP
        (fr.nF + (ConLeche.structFieldTeleOf cty fr.nP fr.nF i).length)).map
      (interp V (consList (vs.map (interp V (consList locals (consList (xs ++ fs) σchain))))
        (consList (xs ++ fs) σchain))) = xs := by
    rw [show consList (vs.map (interp V (consList locals (consList (xs ++ fs) σchain))))
            (consList (xs ++ fs) σchain)
          = consList (xs ++ (fs ++ vs.map
              (interp V (consList locals (consList (xs ++ fs) σchain))))) σchain from by
        rw [← List.append_assoc]
        exact (consList_append _ _ _).symm,
      ← hbslen]
    exact interp_prefVarsAV hxl
  rw [hpref, List.append_assoc]

end ConLeche.Model
