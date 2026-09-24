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

/-- An opened variable's inferred type is its STORED annotation —
`certs_of_infer_mkAppN`'s "the head's type is pinned". -/
theorem IhTyped.fvarTy {envT : Env} {D idx : Nat} {ty t : Expr}
    (h : ConLeche.Rules.Infer envT .full D (.fvar idx ty) t) : t = ty := by
  cases h; rfl

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

/-! ## One step further: the STORED node is the GENERATED spine

`IhCallRun.heq` exports `e = expected` as TERMS (the kernel's
exact comparison), so the stored node's reading at the rule's frame IS the
generated call's — `congrArg` through the opening.  That removes
`blockIhCall?` from the obligation altogether and leaves a statement
about `blockIhSpinePis` alone: the shape the reading batteries
(`denoteMeta_instPisAtLift_peel`, and `FixRecRead`'s `structIdxAt` /
`structTeleAt` lemmas at the one-member route) are written for. -/

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

end ConLeche.Model
