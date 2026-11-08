module

public import ConLeche.Modular
import ConLeche.Verify.BinderLoop
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Mono
import ConLeche.Verify.Knot
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Verify.Level

/-!
# A pinned name's type is no proposition

The certified `Nat` operations and the compiler-trust opaques (`pinnedLeafName`) are stored at
their homes with a pinned type: `Nat → Nat`, `Nat → Nat → Nat`, `Nat → Nat → Bool`
(`natOpTyPinned`), `Nat → Nat` or `Bool → Bool` (`reduceOpCvA`).  Where the environment stores
those constants level-free at `Sort 1`, the kernel infers such a type to be of sort
`imax 1 1` or `imax 1 (imax 1 1)`, never of level zero (`not_typeIsProp_arrows`), so no
inference that the type is a proposition succeeds.  The worker's agreement of two copies at such a
name, which asks that inference unless both copies are theorems, then never passes as a proof
pair.
-/

public section

namespace ConLeche.Driver

open ConLeche ConLeche.Modular

/-- **A constant stored level-free at `Sort 1`.** -/
@[expose] def SortOne (E : Env) (x : Name) : Prop :=
  ∃ ci, E.find? x = some ci ∧ ci.toConstantVal.levelParams = [] ∧
    ci.toConstantVal.type = .sort (.succ .zero)

/-- **A pinned type's shape**: one or two arrows between constants stored level-free at
`Sort 1`. -/
@[expose] def PinnedArrows (E : Env) (ty : Expr) : Prop :=
  (∃ a b, ty = .forallE (.const a []) (.const b []) ∧ SortOne E a ∧ SortOne E b) ∨
    ∃ a a' b, ty = .forallE (.const a []) (.forallE (.const a' []) (.const b [])) ∧
      SortOne E a ∧ SortOne E a' ∧ SortOne E b

section
variable {E : Env}

theorem whnf_sort_ok {F d : Nat} {u : Level} {e : Expr}
    (h : whnf .verified false E F d (.sort u) = .ok e) : e = .sort u := by
  have h1 := whnf_mono (Nat.le_add_right F 2) h
  rw [whnf_sort] at h1
  exact (Except.ok.inj h1).symm

theorem ensureSort_sort_ok {F d : Nat} {u v : Level}
    (h : ensureSortCore .verified false E F d (.sort u) = .ok v) : v = u :=
  Expr.sort.inj (whnf_sort_ok (ensureSortCore_inv h))

/-- A constant stored level-free at `Sort 1`, at no levels, is inferred of type `Sort 1`. -/
theorem infer_sortOne {F d : Nat} {x : Name} {t : Expr} (hx : SortOne E x)
    (h : inferTypeCore .verified false E F d (.const x []) = .ok t) :
    t = .sort (.succ .zero) := by
  obtain ⟨ci, hf, hlp, hty⟩ := hx
  cases F with
  | zero => rw [inferTypeCore_zero] at h; exact nomatch h
  | succ F =>
    obtain ⟨ci', hf', -, rfl⟩ := Rules.inferTypeCore_const_inv_full h
    rw [hf] at hf'
    obtain rfl := Option.some.inj hf'
    rw [hlp, hty]
    rfl

/-- **An arrow out of a constant at `Sort 1`**: its sort is `imax 1 v`, `v` the codomain's
sort. -/
theorem infer_arrow {F d : Nat} {a : Name} {b t : Expr} (ha : SortOne E a)
    (hb : b.instantiate1 (.fvar d (.const a [])) = b)
    (h : inferTypeCore .verified false E F d (.forallE (.const a []) b) = .ok t) :
    ∃ F' bt v, F = F' + 1 ∧ inferTypeCore .verified false E F' (d + 1) b = .ok bt ∧
      ensureSortCore .verified false E F' (d + 1) bt = .ok v ∧
      t = .sort (.imax (.succ .zero) v) := by
  cases F with
  | zero => rw [inferTypeCore_zero] at h; exact nomatch h
  | succ F =>
    rw [inferTypeCore_forallE_eq] at h
    obtain ⟨tty, htty, h⟩ := bind_okB h
    obtain rfl := infer_sortOne ha htty
    obtain ⟨w, hw, h⟩ := bind_okB h
    obtain rfl := whnf_sort_ok hw
    simp only at h
    rw [hb] at h
    obtain ⟨bt, hbt, h⟩ := bind_okB h
    obtain ⟨v, hv, h⟩ := bind_okB h
    exact ⟨F, bt, v, rfl, hbt, hv, (Except.ok.inj h).symm⟩

/-- **A pinned type is no proposition**: its inferred sort is `imax 1 1` or `imax 1 (imax 1 1)`. -/
theorem not_typeIsProp_arrows {ty : Expr} (hp : PinnedArrows E ty) :
    ¬ TypeIsProp .verified E ty := by
  rintro ⟨F, stype, u, hinf, hsort, heq⟩
  rcases hp with ⟨a, b, rfl, ha, hb⟩ | ⟨a, a', b, rfl, ha, ha', hb⟩
  · obtain ⟨F', bt, v, rfl, hbt, hv, rfl⟩ := infer_arrow ha rfl hinf
    obtain rfl := infer_sortOne hb hbt
    obtain rfl := ensureSort_sort_ok hv
    obtain rfl := ensureSort_sort_ok hsort
    exact absurd (Level.isEquiv_sound heq fun _ => 0) (by simp [Level.eval])
  · obtain ⟨F', bt, v, rfl, hbt, hv, rfl⟩ := infer_arrow ha rfl hinf
    obtain ⟨F'', bt', v', rfl, hbt', hv', rfl⟩ := infer_arrow ha' rfl hbt
    obtain rfl := infer_sortOne hb hbt'
    obtain rfl := ensureSort_sort_ok hv'
    obtain rfl := ensureSort_sort_ok hv
    obtain rfl := ensureSort_sort_ok hsort
    exact absurd (Level.isEquiv_sound heq fun _ => 0) (by simp [Level.eval])

end

end ConLeche.Driver
