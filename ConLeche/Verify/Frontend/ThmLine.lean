module

public import ConLeche.Verify.Frontend.ApplyLine

public section

/-!
# The theorem record of the template (task #290)

`{"thm":{"all":[k],"levelParams":[],"name":k,"type":j,"value":v}}`,
applied at a state whose expression `j` is the constant `False`: the
record is pushed as a `thmDecl` whose declared type is `False` — or it
is dropped as a copy of a built-in prelude record, which is then a
`thmDecl` of type `False` itself (the dedupe compares canonical forms,
and the canonical form of a bare constant is the constant), or the
parser's taint skip takes it (then the skips are non-empty; the clause
goes with task #292).  `applyLine_thmFalse` is what the file theorem
reads off the theorem's line.
-/

namespace ConLeche.Frontend

open ConLeche.Cached (DeclC ExprC)

/-- The canonical form of a bare constant is the constant: two theorem
records with the same canonical form and one declared at `.const n []`
are both declared at `.const n []`. -/
theorem canon_type_const {cv cv' : ConstantVal} {vl vl' : ExprC} {n : Name}
    (h : ConstantInfo.canon (.thmInfo cv vl) = ConstantInfo.canon (.thmInfo cv' vl'))
    (ht : cv.type = .const n []) : cv'.type = .const n [] := by
  simp only [ConstantInfo.canon, ConstantInfo.toConstantVal, ConstantInfo.thmInfo.injEq] at h
  have hcv := congrArg ConstantVal.type h.1
  simp only [ConstantVal.canon, ht, canonExpr, List.map_nil] at hcv
  cases hty : cv'.type <;> simp only [hty, canonExpr, reduceCtorEq, Expr.const.injEq] at hcv
  obtain ⟨rfl, hus⟩ := hcv
  rw [List.map_eq_nil_iff.mp hus.symm]

/-- The same declaration as a theorem record, in the prelude's sense:
a theorem record with the same canonical form. -/
theorem sameCanon_thm {cv : ConstantVal} {vl : ExprC} {p : DeclC}
    (h : (DeclC.thmDecl cv vl).sameCanon p = true) (ht : cv.type = .const falseName []) :
    ∃ cv' vl', p = .thmDecl cv' vl' ∧ cv'.type = .const falseName [] := by
  cases p with
  | thmDecl cv' vl' =>
    refine ⟨cv', vl', rfl, ?_⟩
    simp only [DeclC.sameCanon, DeclC.asInfo?, ConstantInfo.canonEq, decide_eq_true_eq] at h
    exact canon_type_const h ht
  | axiomDecl cv' =>
    simp [DeclC.sameCanon, DeclC.asInfo?, ConstantInfo.canonEq, ConstantInfo.canon] at h
  | defnDecl cv' v' hint =>
    simp [DeclC.sameCanon, DeclC.asInfo?, ConstantInfo.canonEq, ConstantInfo.canon] at h
  | opaqueDecl cv' v' =>
    simp [DeclC.sameCanon, DeclC.asInfo?, ConstantInfo.canonEq, ConstantInfo.canon] at h
  | basisDecl k => simp [DeclC.sameCanon, DeclC.asInfo?] at h
  | indDecl block nP => simp [DeclC.sameCanon, DeclC.asInfo?] at h

/-- A pushed theorem record is in the list, or it was the same
declaration as a prelude record under its name. -/
theorem pushDecl_thm {st st' : StateD} {cv : ConstantVal} {vl : ExprC}
    (h : pushDecl st (.thmDecl cv vl) = .inl st') :
    DeclC.thmDecl cv vl ∈ st'.decls ∨
      ∃ p, st.prelude.byName[cv.name]? = some p ∧ (DeclC.thmDecl cv vl).sameCanon p = true := by
  unfold pushDecl at h
  simp only [DeclC.names, List.findSome?_cons, List.findSome?_nil] at h
  cases hp : st.prelude.byName[cv.name]? with
  | none =>
    rw [hp] at h
    simp only [Option.map_none, Sum.inl.injEq] at h
    subst h
    exact .inl (Array.mem_push.mpr (.inr rfl))
  | some p =>
    rw [hp] at h
    simp only [Option.map_some] at h
    split at h
    · exact .inr ⟨p, rfl, ‹_›⟩
    · exact absurd h (by simp)

/-- The record's own semantics at the theorem line. -/
theorem processLineCoreD_thmFalse {st st' : StateD} {k j v : Nat}
    (h : processLineCoreD st (.thm ⟨k, [], j⟩ v) = .ok (.inl st'))
    (hj : st.exprs.get? j = some (ExprC.mkConst falseName []))
    (hpre : ∀ (n : Name) (d : DeclC), st.prelude.byName[n]? = some d → d ∈ st.prelude.decls) :
    ∃ cv vl, cv.type = .const falseName [] ∧
      (DeclC.thmDecl cv vl ∈ st.prelude.decls ∨ DeclC.thmDecl cv vl ∈ st'.decls) := by
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
    split at hty
    · cases hty
    · unfold StateD.expr at hty
      rw [hj] at hty
      simp only [pure, Except.pure, Except.ok.injEq] at hty
      exact hty.symm
  obtain ⟨vl, _, h⟩ := exceptBind_ok h
  try simp only at h
  -- the push, rewritten or not
  have core : ∀ {s : StateD} {vl' : ExprC}, pushDecl st (.thmDecl cvp vl') = .inl s →
      ∃ cv vl, cv.type = .const falseName [] ∧
        (DeclC.thmDecl cv vl ∈ st.prelude.decls ∨ DeclC.thmDecl cv vl ∈ s.decls) := by
    intro s vl' hp
    rcases pushDecl_thm hp with hmem | ⟨p, hbn, hsc⟩
    · exact ⟨cvp, vl', hcvp, .inr hmem⟩
    · obtain ⟨cv', vl'', rfl, hty'⟩ := sameCanon_thm hsc hcvp
      exact ⟨cv', vl'', hty', .inl (hpre _ _ hbn)⟩
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    obtain ⟨s, hs, rfl⟩ := Sum.map_inl_eq h
    exact core (s := s) hs
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    exact core h

/-- **The theorem line.**  At a state whose expression `j` is `False`,
the record `{"thm":{…,"name":k,"type":j,"value":v}}` either is skipped
for taint (then the skips are non-empty) or leaves a `thmDecl` of type
`False` in the list — the record's own, or the prelude's copy. -/
theorem applyLine_thmFalse {st st' : StateD} {k j v : Nat}
    (h : applyLine st (.decl (.thm ⟨k, [], j⟩ v)) = .ok (.inl st'))
    (hj : st.exprs.get? j = some (ExprC.mkConst falseName []))
    (hpre : ∀ (n : Name) (d : DeclC), st.prelude.byName[n]? = some d → d ∈ st.prelude.decls) :
    st'.taintSkipped ≠ #[] ∨ ∃ cv vl, cv.type = .const falseName [] ∧
      (DeclC.thmDecl cv vl ∈ st.prelude.decls ∨ DeclC.thmDecl cv vl ∈ st'.decls) := by
  simp only [applyLine] at h
  unfold applyDeclD at h
  simp only at h
  split at h
  · obtain ⟨p, _, h⟩ := exceptBind_ok h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Sum.inl.injEq] at h; subst h
      exact .inl (fun hx => by have := congrArg Array.size hx; simp at this)
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
        exact .inr (processLineCoreD_thmFalse ‹_› hj hpre)
      · split at h
        · exact absurd h (by simp [pure, Except.pure])
        · cases h
  · split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      exact .inr (processLineCoreD_thmFalse ‹_› hj hpre)
    · split at h
      · exact absurd h (by simp [pure, Except.pure])
      · cases h

end ConLeche.Frontend
