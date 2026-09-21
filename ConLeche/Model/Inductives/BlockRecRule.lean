module

public import ConLeche.Model.Annot.Bit
public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Semantics.Tower.BlockRecI
import ConLeche.Semantics.Kit
import ConLeche.Verify.InstList
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Semantics.Tower.TowerMk
import ConLeche.Semantics.BasisOk

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
so it is the regimes' seam and not this induction's. -/

/-- **The guarded call's value.** -/
@[expose] def IhNodeVal (V : Type uv) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (fr : ConLeche.BlockRuleFrame) (F : Nat) (ρ' : Nat → V) (ihvals : List V) : Prop :=
  ∀ (d : Nat) (locals : List V) (e : Expr) (r : Nat) (as as1 as2 : List Expr)
    (A B : AnnotTerm),
    e.hasFvar = false →
    locals.length = d → FvarList (F + d) as1 → FvarList (F + fr.nR + d) as2 →
    ConLeche.blockIhCall? fr d e = some (r, as) →
    denoteMeta acval env φ (F + d) (e.instantiateList as1 0) = some A →
    denoteMeta acval env φ (F + fr.nR + d)
      ((Expr.mkAppN (.bvar (d + fr.nR - 1 - r))
        (as.map fun x => x.liftLooseBVars fr.nR d)).instantiateList as2 0) = some B →
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
    {fr : ConLeche.BlockRuleFrame} {F : Nat} {ρ' : Nat → V} {ihvals : List V}
    (hih : ihvals.length = fr.nR) (hcall : IhNodeVal V acval env φ fr F ρ' ihvals) :
    ∀ (e e'' : Expr) (d : Nat) (locals : List V) (as1 as2 : List Expr) (A B : AnnotTerm),
      ConLeche.abstractIh fr d e = some e'' → e.hasFvar = false →
      locals.length = d → FvarList (F + d) as1 → FvarList (F + fr.nR + d) as2 →
      denoteMeta acval env φ (F + d) (e.instantiateList as1 0) = some A →
      denoteMeta acval env φ (F + fr.nR + d) (e''.instantiateList as2 0) = some B →
      interp V (consList locals ρ') A
        = interp V (consList locals (consList ihvals ρ')) B
  | .bvar j, e'', d, locals, as1, as2, A, B, hab, hf, hloc, h1, h2, hA, hB => by
    obtain rfl : e'' = (Expr.bvar j).liftLooseBVars fr.nR d := by
      rw [ConLeche.abstractIh_bvar] at hab
      rw [Expr.liftLooseBVars, ← Option.some.inj hab]
      split <;> rename_i hj
      · rw [if_neg (by omega)]
      · rw [if_pos (by omega)]
    exact interp_of_open_lift hacl hf h1 h2 hloc hih hA hB
  | .sort u, e'', d, locals, as1, as2, A, B, hab, hf, hloc, h1, h2, hA, hB => by
    obtain rfl : e'' = (Expr.sort u).liftLooseBVars fr.nR d := (Option.some.inj hab).symm
    exact interp_of_open_lift hacl hf h1 h2 hloc hih hA hB
  | .lit l, e'', d, locals, as1, as2, A, B, hab, hf, hloc, h1, h2, hA, hB => by
    obtain rfl : e'' = (Expr.lit l).liftLooseBVars fr.nR d := (Option.some.inj hab).symm
    exact interp_of_open_lift hacl hf h1 h2 hloc hih hA hB
  | .const n us, e'', d, locals, as1, as2, A, B, hab, hf, hloc, h1, h2, hA, hB => by
    rw [ConLeche.abstractIh_const] at hab
    split at hab
    · exact nomatch hab
    · obtain rfl : e'' = (Expr.const n us).liftLooseBVars fr.nR d := (Option.some.inj hab).symm
      exact interp_of_open_lift hacl hf h1 h2 hloc hih hA hB
  | .fvar _ _, _, _, _, _, _, _, _, hab, _, _, _, _, _, _ => nomatch hab
  | .letE ty v b, _, d, _, as1, _, A, _, _, _, _, _, _, hA, _ => by
    rw [Expr.instantiateList, denoteMeta] at hA
    exact nomatch hA
  | .proj sn i e, e'', d, locals, as1, as2, A, B, hab, hf, hloc, h1, h2, hA, hB => by
    simp only [Expr.hasFvar] at hf
    rw [ConLeche.abstractIh] at hab
    split at hab
    · exact nomatch hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨e', hpe, rfl⟩ := hab
    rw [Expr.instantiateList, denoteMeta_proj] at hA hB
    obtain ⟨ea, hea, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨eb, heb, hB⟩ := Option.bind_eq_some_iff.mp hB
    have hrec := interp_abstractIh hacl hih hcall e e' d locals as1 as2 ea eb
      hpe hf hloc h1 h2 hea heb
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
  | .lam ty b bi, e'', d, locals, as1, as2, A, B, hab, hf, hloc, h1, h2, hA, hB => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [ConLeche.abstractIh, Option.bind_eq_some_iff] at hab
    obtain ⟨ty', hty', hab⟩ := hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨b', hb', rfl⟩ := hab
    rw [Expr.instantiateList, denoteMeta_lam] at hA hB
    obtain ⟨ta, hta, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨ba, hba, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨tb, htb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain ⟨bb, hbb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain rfl : A = .lam (pwBit φ bi.pw) ta ba := (Option.some.inj hA).symm
    obtain rfl : B = .lam (pwBit φ bi.pw) tb bb := (Option.some.inj hB).symm
    rw [← Expr.instantiateList_cons] at hba hbb
    have hrecT := interp_abstractIh hacl hih hcall ty ty' d locals as1 as2 ta tb
      hty' hf.1 hloc h1 h2 hta htb
    rw [interp_lam, interp_lam, hrecT]
    refine lamR_congr fun x _ => ?_
    rw [show F + d + 1 = F + (d + 1) from by omega] at hba
    rw [show F + fr.nR + d + 1 = F + fr.nR + (d + 1) from by omega] at hbb
    have := interp_abstractIh hacl hih hcall b b' (d + 1) (locals ++ [x])
      (Expr.fvar (F + d) (ty.instantiateList as1 0) :: as1)
      (Expr.fvar (F + fr.nR + d) (ty'.instantiateList as2 0) :: as2) ba bb
      hb' hf.2 (by simp [hloc])
      (by rw [show F + (d + 1) = F + d + 1 from by omega]; exact h1.cons _)
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega]; exact h2.cons _)
      hba hbb
    rwa [consList_append, consList_append] at this
  | .forallE ty b bi, e'', d, locals, as1, as2, A, B, hab, hf, hloc, h1, h2, hA, hB => by
    simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
    rw [ConLeche.abstractIh, Option.bind_eq_some_iff] at hab
    obtain ⟨ty', hty', hab⟩ := hab
    rw [Option.map_eq_some_iff] at hab
    obtain ⟨b', hb', rfl⟩ := hab
    rw [Expr.instantiateList, denoteMeta_forallE] at hA hB
    obtain ⟨ta, hta, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨ba, hba, hA⟩ := Option.bind_eq_some_iff.mp hA
    obtain ⟨tb, htb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain ⟨bb, hbb, hB⟩ := Option.bind_eq_some_iff.mp hB
    obtain rfl : A = .pi 0 (pwBit φ bi.pw) ta ba := (Option.some.inj hA).symm
    obtain rfl : B = .pi 0 (pwBit φ bi.pw) tb bb := (Option.some.inj hB).symm
    rw [← Expr.instantiateList_cons] at hba hbb
    have hrecT := interp_abstractIh hacl hih hcall ty ty' d locals as1 as2 ta tb
      hty' hf.1 hloc h1 h2 hta htb
    rw [interp_pi, interp_pi, hrecT]
    refine piR_congr fun x _ => ?_
    rw [show F + d + 1 = F + (d + 1) from by omega] at hba
    rw [show F + fr.nR + d + 1 = F + fr.nR + (d + 1) from by omega] at hbb
    have := interp_abstractIh hacl hih hcall b b' (d + 1) (locals ++ [x])
      (Expr.fvar (F + d) (ty.instantiateList as1 0) :: as1)
      (Expr.fvar (F + fr.nR + d) (ty'.instantiateList as2 0) :: as2) ba bb
      hb' hf.2 (by simp [hloc])
      (by rw [show F + (d + 1) = F + d + 1 from by omega]; exact h1.cons _)
      (by rw [show F + fr.nR + (d + 1) = F + fr.nR + d + 1 from by omega]; exact h2.cons _)
      hba hbb
    rwa [consList_append, consList_append] at this
  | .app f a, e'', d, locals, as1, as2, A, B, hab, hf, hloc, h1, h2, hA, hB => by
    rw [ConLeche.abstractIh_app] at hab
    revert hab
    cases hc : ConLeche.blockIhCall? fr d (.app f a) with
    | some ra =>
      intro hab
      obtain ⟨r, as⟩ := ra
      obtain rfl := Option.some.inj hab
      exact hcall d locals (.app f a) r as as1 as2 A B hf hloc h1 h2 hc hA hB
    | none =>
      intro hab
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      rw [Option.bind_eq_some_iff] at hab
      obtain ⟨f', hf', hab⟩ := hab
      rw [Option.map_eq_some_iff] at hab
      obtain ⟨a', ha', rfl⟩ := hab
      rw [Expr.instantiateList, denoteMeta_app] at hA hB
      obtain ⟨fa, hfa, hA⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨aa, haa, hA⟩ := Option.bind_eq_some_iff.mp hA
      obtain ⟨fb, hfb, hB⟩ := Option.bind_eq_some_iff.mp hB
      obtain ⟨ab, hab', hB⟩ := Option.bind_eq_some_iff.mp hB
      obtain rfl : A = .app fa aa := (Option.some.inj hA).symm
      obtain rfl : B = .app fb ab := (Option.some.inj hB).symm
      rw [interp_app, interp_app,
        interp_abstractIh hacl hih hcall f f' d locals as1 as2 fa fb hf' hf.1 hloc h1 h2 hfa hfb,
        interp_abstractIh hacl hih hcall a a' d locals as1 as2 aa ab ha' hf.2 hloc h1 h2 haa hab']

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
is one of the node's — `blockIhCall?` inverted just far enough to move
`hasFvar` down. -/
theorem blockIhCall?_args_sub {fr : ConLeche.BlockRuleFrame} {d : Nat} {e : Expr}
    {r : Nat} {as : List Expr} (h : ConLeche.blockIhCall? fr d e = some (r, as)) :
    ∃ maj ∈ e.getAppArgs, as = maj.getAppArgs := by
  simp only [ConLeche.blockIhCall?] at h
  split at h
  case h_2 => exact nomatch h
  case h_1 =>
  split at h
  case h_1 => exact nomatch h
  case h_2 =>
  split at h
  case isTrue => exact nomatch h
  case isFalse =>
  split at h
  case isTrue => exact nomatch h
  case isFalse =>
  split at h
  case isTrue => exact nomatch h
  case isFalse =>
  split at h
  case h_1 => exact nomatch h
  case h_2 maj hmaj =>
  have hmem : maj ∈ e.getAppArgs := List.mem_of_getElem? hmaj
  split at h
  case h_2 => exact nomatch h
  case h_1 =>
  split at h
  case isTrue => exact nomatch h
  case isFalse =>
  split at h
  case isTrue => exact nomatch h
  case isFalse =>
  split at h
  case isTrue => exact nomatch h
  case isFalse =>
  split at h
  case isTrue => exact nomatch h
  case isFalse =>
  split at h
  case h_1 => exact nomatch h
  case h_2 =>
  split at h
  case isTrue => exact nomatch h
  case isFalse =>
  split at h
  case h_1 => exact nomatch h
  case h_2 =>
  exact ⟨maj, hmem, (Prod.mk.inj (Option.some.inj h)).2.symm⟩

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
This is what `denoteMeta_blockIhCall`, `ihFunAV_fold` and the leaf's
own value (`blockRecAV_facts`) combine to give, and it is the ONLY
thing `IhNodeVal` still wants. -/
@[expose] def IhCallFold (V : Type uv) [SetTheory V]
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (fr : ConLeche.BlockRuleFrame) (F : Nat) (ρ' : Nat → V) (ihvals : List V) : Prop :=
  ∀ (d : Nat) (locals : List V) (e : Expr) (r : Nat) (as as1 : List Expr)
    (A : AnnotTerm) (vs : List AnnotTerm),
    locals.length = d → FvarList (F + d) as1 →
    ConLeche.blockIhCall? fr d e = some (r, as) →
    denoteMeta acval env φ (F + d) (e.instantiateList as1 0) = some A →
    DenoteMetaSpine acval env φ (F + d) (as.map (·.instantiateList as1 0)) vs →
    interp V (consList locals ρ') A
      = (vs.map (interp V (consList locals ρ'))).foldl SetTheory.app (ihvals.getD r pt)

/-- **O-1's premise, reduced**: `IhNodeVal` from `IhCallFold`.  The
residue side is computed (`interp_ihNode`); what the model still owes
is the stored node's value. -/
theorem ihNodeVal_of_fold
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {fr : ConLeche.BlockRuleFrame} {F : Nat} {ρ' : Nat → V} {ihvals : List V}
    (hih : ihvals.length = fr.nR)
    (hfold : IhCallFold V acval env φ fr F ρ' ihvals) :
    IhNodeVal V acval env φ fr F ρ' ihvals := by
  intro d locals e r as as1 as2 A B he hloc h1 h2 hc hA hB
  obtain ⟨nm, c', i, expected, hh1, hh2, hrpos, hh4, hh5, hh6, hh7, hh8, hh9, hh10⟩ :=
    ConLeche.blockIhCall?_spine hc
  clear hh1 hh2 hh4 hh5 hh6 hh7 hh8 hh9 hh10
  have hr : r < fr.nR := pairIdxOf?_lt hrpos
  obtain ⟨maj, hmaj, rfl⟩ := blockIhCall?_args_sub hc
  have hfa : ∀ a ∈ maj.getAppArgs, a.hasFvar = false :=
    hasFvar_of_mem_getAppArgs (hasFvar_of_mem_getAppArgs he maj hmaj)
  obtain ⟨vs, hvs, hval⟩ := interp_ihNode hacl hr hfa h1 h2 hloc hih hB
  rw [hval, hfold d locals e r maj.getAppArgs as1 A vs hloc h1 hc hA hvs]

/-! ## One step further: the STORED node is the GENERATED spine

`blockIhCall?_spine` exports `e = expected` as TERMS (lane K2's exact
comparison), so the stored node's reading at the rule's frame IS the
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
    (acval : Name → (Name → Nat) → AnnotTerm) (env : Env) (φ : Name → Nat)
    (fr : ConLeche.BlockRuleFrame) (F : Nat) (ρ' : Nat → V) (ihvals : List V) : Prop :=
  ∀ (d : Nat) (locals : List V) (nm : Name) (c' i r : Nat) (as as1 : List Expr)
    (expected : Expr) (A : AnnotTerm) (vs : List AnnotTerm),
    locals.length = d → FvarList (F + d) as1 →
    ConLeche.nameIdxOf? fr.recNames nm = some c' →
    ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r →
    as.length = (fr.teleOf i).length →
    Expr.instPisAtLift as
      (ConLeche.blockIhSpinePis nm fr.rlvls fr.pw fr.nP fr.rP fr.nF i d
        (fr.teleOf i) (fr.idxOf i)) = some expected →
    denoteMeta acval env φ (F + d) (expected.instantiateList as1 0) = some A →
    DenoteMetaSpine acval env φ (F + d) (as.map (·.instantiateList as1 0)) vs →
    interp V (consList locals ρ') A
      = (vs.map (interp V (consList locals ρ'))).foldl SetTheory.app (ihvals.getD r pt)

/-- **`IhCallFold` from `IhSpineFold`** — the stored node IS the
generated spine, so its opened reading is too. -/
theorem ihCallFold_of_spine {fr : ConLeche.BlockRuleFrame} {F : Nat} {ρ' : Nat → V}
    {ihvals : List V} (h : IhSpineFold V acval env φ fr F ρ' ihvals) :
    IhCallFold V acval env φ fr F ρ' ihvals := by
  intro d locals e r as as1 A vs hloc h1 hc hA hvs
  obtain ⟨nm, c', i, expected, -, hnm, hrpos, -, -, -, hasl, -, hexp, rfl⟩ :=
    ConLeche.blockIhCall?_spine hc
  exact h d locals nm c' i r as as1 e A vs hloc h1 hnm hrpos hasl hexp hA hvs

/-- **O-1's premise, from the generated spine alone.**  The composite:
`interp_abstractIh`'s `hcall` follows from a statement that mentions
neither `abstractIh` nor `blockIhCall?` — only `blockIhSpinePis`, the
frame, and the ih values. -/
theorem ihNodeVal_of_spine
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (acval n ψ).liftN m k = acval n ψ)
    {fr : ConLeche.BlockRuleFrame} {F : Nat} {ρ' : Nat → V} {ihvals : List V}
    (hih : ihvals.length = fr.nR) (h : IhSpineFold V acval env φ fr F ρ' ihvals) :
    IhNodeVal V acval env φ fr F ρ' ihvals :=
  ihNodeVal_of_fold hacl hih (ihCallFold_of_spine h)

end ConLeche.Model
