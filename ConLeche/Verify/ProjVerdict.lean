module

public import ConLeche.Kernel.Core

public section

/-!
# The verdict at a projection without a table

`annotateBody`'s `.proj` clause (`ConLeche/Kernel/Core.lean`, and its
cached twin in `ConLeche/Cached/CoreC.lean`) throws
`projMissError find? hasTable T sn i nArgs` when the subject type's
head `T` has no table entry at field `i`, and `.invalid` outright when
the head is no constant.  This file states what that error is:

* `projMissError_decline`: it is a DECLINE (`.notImplemented`) only at
  a positively detected indexed structure-like type — no table, the
  node names `T`, `T` is a stored inductive with exactly ONE
  constructor, applied beyond its parameters (official's `infer_proj`
  admits `nparams + nindices` arguments), at a field index below that
  constructor's field count.  That is the one shape official's
  `infer_proj` may accept and we do not support.
* `projMissError_invalid`: everywhere else it is a REJECT
  (`.invalid`) — in particular (`projMissError_invalid_of_ctors`) at
  any head that is no stored inductive with a single constructor, as
  official (`invalid_proj_exception`).
-/

namespace ConLeche

/-- The positive detection, unfolded: the node names `T`, a stored
single-constructor inductive applied beyond its parameters, and the
field index is below the constructor's field count. -/
theorem projIndexedStructLike_spec {find? : Name → Option ConstantInfo}
    {T sn : Name} {i nArgs : Nat}
    (h : projIndexedStructLike find? T sn i nArgs = true) :
    T = sn ∧ ∃ v caps c vc nP nF, find? T = some (.indInfo v caps) ∧
      caps.ctors = [c] ∧ caps.nparams < nArgs ∧
      find? c = some (.ctorInfo vc nP nF) ∧ i < nF := by
  unfold projIndexedStructLike at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨rfl, h⟩ := h
  refine ⟨rfl, ?_⟩
  split at h <;> try contradiction
  rename_i v caps hT
  split at h <;> try contradiction
  rename_i c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hn, h⟩ := h
  split at h <;> try contradiction
  rename_i vc nP nF hcf
  exact ⟨v, caps, c, vc, nP, nF, hT, hc, hn, hcf, of_decide_eq_true h⟩

/-- **The only decline.** -/
theorem projMissError_decline {find? : Name → Option ConstantInfo}
    {hasTable : Bool} {T sn : Name} {i nArgs : Nat} {w : String}
    (h : projMissError find? hasTable T sn i nArgs = .notImplemented w) :
    hasTable = false ∧ projIndexedStructLike find? T sn i nArgs = true := by
  unfold projMissError at h
  cases hasTable <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  · refine ⟨rfl, ?_⟩
    cases hp : projIndexedStructLike find? T sn i nArgs <;>
      simp only [hp, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at h ⊢
  · cases h

/-- **Everything else rejects.** -/
theorem projMissError_invalid {find? : Name → Option ConstantInfo}
    {hasTable : Bool} {T sn : Name} {i nArgs : Nat}
    (h : hasTable = true ∨ projIndexedStructLike find? T sn i nArgs = false) :
    ∃ msg, projMissError find? hasTable T sn i nArgs = .invalid msg := by
  unfold projMissError
  rcases h with h | h
  · simp only [h, ↓reduceIte, CheckError.invalid.injEq, exists_eq']
  · cases hasTable <;>
      simp only [h, Bool.false_eq_true, ↓reduceIte, CheckError.invalid.injEq, exists_eq']

/-- **Official's non-structure-like case rejects**: a head that is not
a stored inductive with exactly one constructor (two constructors, none,
an axiom, `Quot`, …). -/
theorem projMissError_invalid_of_ctors {find? : Name → Option ConstantInfo}
    {hasTable : Bool} {T sn : Name} {i nArgs : Nat}
    (h : ∀ v caps c, find? T = some (.indInfo v caps) → caps.ctors ≠ [c]) :
    ∃ msg, projMissError find? hasTable T sn i nArgs = .invalid msg := by
  refine projMissError_invalid (.inr ?_)
  cases hp : projIndexedStructLike find? T sn i nArgs
  · rfl
  · obtain ⟨-, v, caps, c, -, -, -, hT, hc, -⟩ := projIndexedStructLike_spec hp
    exact absurd hc (h v caps c hT)

end ConLeche
