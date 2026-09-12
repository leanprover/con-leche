module

public import ConLeche.Accepts
public import ConLeche.Verify.Frontend.Lines
public import ConLeche.Verify.Frontend.ApplyLine
import ConLeche.Verify.Frontend.ThmLine
import ConLeche.Verify.Frontend.FalseLines
import ConLeche.Frontend.Scan.Equiv.Kit

public section

/-!
# From the file to the parsed record (task #290)

The line-level lemma: a file that matches `hasProofOfFalse`
(`ConLeche/Accepts.lean`) and parses, parses to a list holding a
`thmDecl` of type `False`.

The walk is the template's, line by line.  `parseLines_split` carries
the state across each arbitrary part to the next template line as a
line start; `Reach.keeps` says what those steps keep (bound entries,
pushed records); the three line lemmas of
`ConLeche/Verify/Frontend/FalseLines.lean` say what each template line
scans to; `applyLine_nameFalse`, `applyLine_constFalse` and
`applyLine_thmFalse` say what the state does with it.  The name entry
for the theorem's own name is not read at all: it is absorbed into the
part before the theorem line, which may be anything.
-/

namespace ConLeche.Frontend

/-! ## What a chain of lines keeps -/

theorem Reach.keeps {st st' : StateD} (h : Reach st st') : Keeps st st' := by
  induction h with
  | refl => exact Keeps.refl _
  | step r h _ ih => exact (applyLine_keeps h).trans ih

/-! ## The initial state -/

theorem init_names (inModel census : Bool) :
    (StateD.init inModel census).names = IdTable.singleton .anonymous := rfl

/-! ## The bytes of a file that matches the template -/

theorem lit_nl : lit "\n" = [10] := by rw [lit_eq_toByteArray]; decide

/-! ## The walk -/

/-- **The line-level lemma over the line fold.** -/
theorem parseLines_hasProofOfFalse {s : String} (h : hasProofOfFalse s) {st st' : StateD}
    {n : Nat} (hp : parseLines st (lit s) n = .ok st')
    (h0 : st.names.get? 0 = some .anonymous) :
    ∃ cv vl, cv.type = .const falseName [] ∧ Declaration.thmDecl cv vl ∈ st'.decls := by
  obtain ⟨before, b₁, b₂, b₃, after, i, j, k, v, name, rfl⟩ := h
  -- the bytes: the parts and the four lines, each ended by its newline
  rw [lit_append, lit_append, lit_append, lit_append, lit_append, lit_append, lit_append,
    lit_append, lit_append, lit_append, lit_append, lit_append, lit_append, lit_append,
    lit_append, lit_append, lit_nl] at hp
  simp only [List.append_assoc, List.cons_append, List.nil_append] at hp
  -- the part before
  obtain ⟨st₁, n₁, r₁, hp⟩ := parseLines_split (lit before).length (lit before)
    (Nat.le_refl _) st st' _ n hp
  have K₁ := r₁.keeps
  -- the name entry for `False`
  rw [parseLines_line (naiveLine_nameFalse i _)] at hp
  split at hp
  · exact absurd hp (by simp)
  · exact absurd hp (by simp)
  rename_i st₂ h₂
  have hi : st₂.names.get? i = some falseName := applyLine_nameFalse h₂ (K₁.names 0 _ h0)
  -- the part between
  obtain ⟨st₃, n₃, r₃, hp⟩ := parseLines_split (lit b₁).length (lit b₁)
    (Nat.le_refl _) st₂ st' _ _ hp
  have K₃ := r₃.keeps
  -- the expression entry for the constant `False`
  rw [parseLines_line (naiveLine_constFalse j i _)] at hp
  split at hp
  · exact absurd hp (by simp)
  · exact absurd hp (by simp)
  rename_i st₄ h₄
  have hj : st₄.exprs.get? j = some (Expr.mkConst falseName []) :=
    applyLine_constFalse h₄ (K₃.names i _ hi)
  -- the two parts and the theorem's name entry between, as one part
  have hshape : lit b₂ ++ 10 :: (lit s!"\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}" ++
      10 :: (lit b₃ ++ 10 ::
        (lit s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}"
          ++ 10 :: lit after))) =
      (lit b₂ ++ 10 :: (lit s!"\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}" ++
        10 :: lit b₃)) ++ 10 ::
        (lit s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}"
          ++ 10 :: lit after) := by
    simp only [List.append_assoc, List.cons_append]
  rw [hshape] at hp
  obtain ⟨st₅, n₅, r₅, hp⟩ := parseLines_split _ _ (Nat.le_refl _) st₄ st' _ _ hp
  have K₅ := r₅.keeps
  -- the theorem record
  rw [parseLines_line (naiveLine_thm k j v _)] at hp
  split at hp
  · exact absurd hp (by simp)
  · exact absurd hp (by simp)
  rename_i st₆ h₆
  obtain ⟨cv, vl, hty, hmem⟩ := applyLine_thmFalse h₆ (K₅.exprs j _ hj)
  -- the part after
  have K₇ := (parseLines_reach _ _ (Nat.le_refl _) _ _ _ hp).keeps
  exact ⟨cv, vl, hty, K₇.decls _ hmem⟩

/-- **The line-level lemma.**  A file that matches the template and
parses, parses to a list holding a theorem record of type `False`. -/
theorem parseExportD_hasProofOfFalse {s : String} (h : hasProofOfFalse s)
    {inModel census : Bool} {r : ParseResultD}
    (hp : parseExportD s inModel census = .ok r) :
    ∃ cv vl, cv.type = .const falseName [] ∧ Declaration.thmDecl cv vl ∈ r.decls.toList := by
  rw [parseExportD_eq_parseLines s inModel census (parseExportD_ok_size hp)] at hp
  cases hpl : parseLines (.init inModel census) (lit s) 0 with
  | error e => rw [hpl] at hp; simp [Except.map] at hp
  | ok st' =>
    rw [hpl] at hp
    simp only [Except.map, Except.ok.injEq] at hp
    subst hp
    have h0 : (StateD.init inModel census).names.get? 0 = some .anonymous := by
      rw [init_names, IdTable.get?_singleton]; rfl
    obtain ⟨cv, vl, hty, hmem⟩ := parseLines_hasProofOfFalse h hpl h0
    exact ⟨cv, vl, hty, Array.mem_def.mp hmem⟩

end ConLeche.Frontend
