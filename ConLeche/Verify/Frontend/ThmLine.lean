module

public import ConLeche.Frontend.ExportC
import ConLeche.Verify.Frontend.ApplyLine
import ConLeche.Verify.ExceptBind

public section

/-!
# The theorem record of the template (task #290)

`{"thm":{"all":[k],"levelParams":[],"name":k,"type":j,"value":v}}`,
applied at a state whose expression `j` is the constant `False`: the
record is pushed as a `thmDecl` whose declared type is `False`.
`applyLine_thmFalse` is what the file theorem reads off the theorem's
line.  (The parse keeps the file's records as they are — the prelude
dedupe and the basis-pin match are `preparePrelude`'s since task #293
— so there is nothing else the record can become.)
-/

namespace ConLeche.Frontend

/-- A pushed record is in the list. -/
theorem pushDecl_mem (st : StateD) (d : Declaration) : d ∈ (pushDecl st d).decls :=
  (noteDecl_frame _ _).decls d (Array.mem_push.mpr (.inr rfl))

/-- The record's own semantics at the theorem line. -/
theorem processLineCoreD_thmFalse {st st' : StateD} {k j v : Nat}
    (h : processLineCoreD st (.thm ⟨k, [], j⟩ v) = .ok (.inl st'))
    (hj : st.exprs.get? j = some (Expr.mkConst falseName [])) :
    ∃ cv vl, cv.type = .const falseName [] ∧ Declaration.thmDecl cv vl ∈ st'.decls := by
  unfold processLineCoreD at h
  obtain ⟨cvp, hcv, h⟩ := exceptBind_ok h
  -- the header: some name, no level parameters, the type `False`
  have hcvp : cvp.type = .const falseName [] := by
    unfold parseCVD at hcv
    obtain ⟨nm, _, hcv⟩ := exceptBind_ok hcv
    obtain ⟨ty, hty, hcv⟩ := exceptBind_ok hcv
    obtain ⟨lps, _, hcv⟩ := exceptBind_ok hcv
    simp only [pure, Except.pure, Except.ok.injEq] at hcv
    subst hcv
    unfold getDeclD at hty
    unfold StateD.expr at hty
    rw [hj] at hty
    simp only [pure, Except.pure, Except.ok.injEq] at hty
    exact hty.symm
  obtain ⟨vl, _, h⟩ := exceptBind_ok h
  try simp only at h
  -- the push, rewritten or not
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    exact ⟨cvp, _, hcvp, pushDecl_mem _ _⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
    exact ⟨cvp, vl, hcvp, pushDecl_mem _ _⟩

/-- **The theorem line.**  At a state whose expression `j` is `False`,
the record `{"thm":{…,"name":k,"type":j,"value":v}}` leaves a `thmDecl`
of type `False` in the list. -/
theorem applyLine_thmFalse {st st' : StateD} {k j v : Nat}
    (h : applyLine st (.decl (.thm ⟨k, [], j⟩ v)) = .ok (.inl st'))
    (hj : st.exprs.get? j = some (Expr.mkConst falseName [])) :
    ∃ cv vl, cv.type = .const falseName [] ∧ Declaration.thmDecl cv vl ∈ st'.decls := by
  simp only [applyLine] at h
  exact processLineCoreD_thmFalse h hj

end ConLeche.Frontend
