module

public import ConLeche.Model.Inductives.CopyWalkFactsRun

public section

/-!
# K.23's recorded Bool, inverted into the model's Prop (task #279 M-D′, DESIGN §M.45)

`CopyWalkFactsRun.lean` names `NestedGroupExclusionOk` — the
stored-data conjunct that a copy constructor field which is
copy-recursive into a group-mate has a container constructor field that
is recursive-shaped.  The kernel decides exactly that shape as a `Bool`
(`nestedGroupExclusionOk`, `Kernel/Inductives/NestedInstall.lean`) and
the nested installation refuses to proceed unless it is `true`.

This module is the bridge: the recorded `Bool` *is* the model's `Prop`.
The proof is pure bookkeeping — the `List.all`s become the ∀s, the
`zipIdx` memberships become the `getElem?` equations the `Prop`
carries, and every `| none => true` arm is simply never reached because
the `Prop` hands over the corresponding `some` equation.  The one place
where the two sides genuinely differ is the field index: the kernel
ranges over `i < nFS`, the `Prop` over every `i` with a binder
`bsS[nPS + i]? = some domS`, and `stripPis_length` closes the gap.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState ContainerCtor)

/-- A `getElem?` equation is a `zipIdx` membership. -/
private theorem mem_zipIdx_of_getElem? {α : Type _} {l : List α} {j : Nat} {a : α}
    (h : l[j]? = some a) : (a, j) ∈ l.zipIdx := by
  rw [List.mem_iff_getElem?]
  refine ⟨j, ?_⟩
  rw [List.getElem?_zipIdx, h]
  simp

/-- **K.23's record, read** (task #279): the kernel's decision
`nestedGroupExclusionOk` is the model's `NestedGroupExclusionOk`. -/
theorem nestedGroupExclusionOk_inv {env envAux : Env} {p : ConLeche.NestedParts}
    {st : ElimState} (h : ConLeche.nestedGroupExclusionOk env envAux p st = true) :
    NestedGroupExclusionOk env envAux p st := by
  unfold ConLeche.nestedGroupExclusionOk at h
  rw [List.all_eq_true] at h
  intro j q hq tyA htyA l cn cty nF hc cvS nPS nFS hfind bsS rS hstripS i domS hdomS
    aux args n hhead hmate ci J c hci hJ hJname hcJ bsJ rJ hstripJ domJ hdomJ
  -- the pin `j`: both scrutinees of the outer `match` are `some`
  have hpin := h (q, j) (mem_zipIdx_of_getElem? hq)
  simp only [htyA, hci] at hpin
  -- the container member `J` is the pin's own, so the `!(J.name == _)` guard is `false`
  rw [List.all_eq_true] at hpin
  have hJa := hpin J hJ
  simp only [hJname, beq_self_eq_true, Bool.not_true, Bool.false_or] at hJa
  -- the constructor `l`, its stored `ctorInfo` and its telescope
  rw [List.all_eq_true] at hJa
  have hcl := hJa ((cn, cty, nF), l) (mem_zipIdx_of_getElem? hc)
  simp only [hfind, hstripS] at hcl
  -- the field `i`: the `Prop`'s binder equation forces `i < nFS`
  rw [List.all_eq_true] at hcl
  have hilt : i < nFS := by
    have hlen : bsS.length = nPS + nFS := ConLeche.Expr.stripPis_length _ hstripS
    have hlt : nPS + i < bsS.length := (List.getElem?_eq_some_iff.mp hdomS).1
    omega
  have hfi := hcl i (List.mem_range.mpr hilt)
  simp only [hdomS, hhead] at hfi
  -- the `if` guard: the `Prop`'s group-mate witness makes the kernel's `any` fire.
  -- It is split rather than rewritten: a restated `match` is a DIFFERENT matcher
  -- constant, so `rw` would not find the kernel's own guard.
  split at hfi
  case isFalse hne =>
    exfalso
    apply hne
    obtain ⟨t, ht, q', hq', hq'aux⟩ := hmate
    rw [List.any_eq_true]
    exact ⟨t, List.mem_range.mpr ht, by simp only [hq', hq'aux, beq_self_eq_true]⟩
  case isTrue =>
    -- the container constructor's own field `i`
    simp only [hcJ, hstripJ, hdomJ] at hfi
    cases hfh : ConLeche.fieldHeadAt domJ.1 with
    | none =>
      rw [hfh] at hfi
      exact Bool.noConfusion hfi
    | some x =>
      obtain ⟨C, argsJ, nJ⟩ := x
      rw [hfh] at hfi
      simp only [Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq, List.all_eq_true,
        List.mem_range, beq_iff_eq] at hfi
      -- `cases hfh :` has already rewritten the goal's own `fieldHeadAt` occurrence
      exact ⟨C, argsJ, nJ, rfl, hfi.1.1, hfi.1.2, fun k hk => hfi.2 k hk⟩

end ConLeche.Model
