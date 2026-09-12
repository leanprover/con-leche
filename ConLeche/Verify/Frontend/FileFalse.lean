module

public import ConLeche.Accepts
public import ConLeche.Verify.Frontend.Lines
import ConLeche.Verify.Frontend.Chunks
public import ConLeche.Verify.Frontend.ApplyLine
import ConLeche.Verify.Frontend.ThmLine
import ConLeche.Verify.Frontend.FalseLines
import ConLeche.Frontend.Scan.Equiv.Kit

public section

/-!
# From the chunks to the parsed record (task #290, #294, #297)

The line-level lemma: chunks that match `jsonWithTheoremFalse`
(`ConLeche/Accepts.lean`) and parse, parse to a list holding a
`thmDecl` of type `False`.

The walk is the template's, line by line, over the byte list of the
chunks' concatenation (`parseLines_template`).  `parseLines_split`
carries the state across each arbitrary part to the next template
line as a line start; `Reach.keeps` says what those steps keep (bound
entries, pushed records); the three line lemmas of
`ConLeche/Verify/Frontend/FalseLines.lean` say what each template line
scans to; `applyLine_nameFalse`, `applyLine_constFalse` and
`applyLine_thmFalse` say what the state does with it.  The name entry
for the theorem's own name is not read at all: it is absorbed into the
part before the theorem line, which may be anything.
`parseChunks_jsonWithTheoremFalse` then puts the chunks' bytes into
that shape: the streaming parse is the line fold of the concatenation
(`parseChunks_eq_parseLines`), and `template_split` cuts the one
interpolated string of the predicate — whose literal chunks fuse each
newline to the line beside it — back into the five parts and the four
line templates the line lemmas are stated with.
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

/-- The bytes of a string's UTF-8 are its literal's. -/
theorem toUTF8_toList (s : String) : s.toUTF8.data.toList = lit s := by
  rw [String.toUTF8_eq_toByteArray, lit_eq_toByteArray]

/-! ## Cutting the template up

`s!` fuses each of the template's newlines into the literal beside it,
so the whole-file template is not syntactically the five parts and the
four line templates.  Each fusion is undone by one `rfl` on string
literals, and `template_split` then re-associates. -/

/-- `toString` on a `String` is the string. -/
theorem toString_id (s : String) : toString s = s := rfl

theorem fuse_nl_in (x : String) : "\n" ++ ("{\"in\":" ++ x) = "\n{\"in\":" ++ x := by
  rw [← String.append_assoc]; rfl
theorem fuse_strFalse_nl (x : String) :
    ",\"str\":{\"pre\":0,\"str\":\"False\"}}" ++ ("\n" ++ x) =
      ",\"str\":{\"pre\":0,\"str\":\"False\"}}\n" ++ x := by
  rw [← String.append_assoc]; rfl
theorem fuse_nl_ie (x : String) : "\n" ++ ("{\"ie\":" ++ x) = "\n{\"ie\":" ++ x := by
  rw [← String.append_assoc]; rfl
theorem fuse_usNil_nl (x : String) : ",\"us\":[]}}" ++ ("\n" ++ x) = ",\"us\":[]}}\n" ++ x := by
  rw [← String.append_assoc]; rfl
theorem fuse_quote_nl (x : String) : "\"}}" ++ ("\n" ++ x) = "\"}}\n" ++ x := by
  rw [← String.append_assoc]; rfl
theorem fuse_nl_thm (x : String) :
    "\n" ++ ("{\"thm\":{\"all\":[" ++ x) = "\n{\"thm\":{\"all\":[" ++ x := by
  rw [← String.append_assoc]; rfl
theorem fuse_close_nl (x : String) : "}}" ++ ("\n" ++ x) = "}}\n" ++ x := by
  rw [← String.append_assoc]; rfl

/-- **The template, cut up**: the one interpolated string of
`jsonWithTheoremFalse` is the five parts and the four line templates,
newline-separated. -/
theorem template_split (before between₁ between₂ between₃ after name : String) (i j k v : Nat) :
    s!"{before}
\{\"in\":{i},\"str\":\{\"pre\":0,\"str\":\"False\"}}
{between₁}
\{\"ie\":{j},\"const\":\{\"name\":{i},\"us\":[]}}
{between₂}
\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}
{between₃}
\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}
{after}" =
      before ++ "\n" ++ s!"\{\"in\":{i},\"str\":\{\"pre\":0,\"str\":\"False\"}}" ++ "\n" ++
      between₁ ++ "\n" ++ s!"\{\"ie\":{j},\"const\":\{\"name\":{i},\"us\":[]}}" ++ "\n" ++
      between₂ ++ "\n" ++ s!"\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}" ++ "\n" ++
      between₃ ++ "\n" ++
      s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}" ++
      "\n" ++ after := by
  simp only [String.append_assoc, toString_id, fuse_nl_in, fuse_strFalse_nl, fuse_nl_ie,
    fuse_usNil_nl, fuse_quote_nl, fuse_nl_thm, fuse_close_nl]

/-! ## The walk -/

/-- **The line-level lemma over the line fold**: the template's shape
as a byte list — five arbitrary parts, the four lines, each ended by
its newline. -/
theorem parseLines_template {st st' : StateD} {n : Nat}
    (before b₁ b₂ b₃ after : List UInt8) (i j k v : Nat) (name : String)
    (hp : parseLines st (before ++ 10 ::
      (lit s!"\{\"in\":{i},\"str\":\{\"pre\":0,\"str\":\"False\"}}" ++ 10 ::
      (b₁ ++ 10 ::
      (lit s!"\{\"ie\":{j},\"const\":\{\"name\":{i},\"us\":[]}}" ++ 10 ::
      (b₂ ++ 10 ::
      (lit s!"\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}" ++ 10 ::
      (b₃ ++ 10 ::
      (lit s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}"
        ++ 10 :: after)))))))) n = .ok st')
    (h0 : st.names.get? 0 = some .anonymous) :
    ∃ cv vl, cv.type = .const falseName [] ∧ Declaration.thmDecl cv vl ∈ st'.decls := by
  -- the part before
  obtain ⟨st₁, n₁, r₁, hp⟩ := parseLines_split before.length before
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
  obtain ⟨st₃, n₃, r₃, hp⟩ := parseLines_split b₁.length b₁
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
  have hshape : b₂ ++ 10 :: (lit s!"\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}" ++
      10 :: (b₃ ++ 10 ::
        (lit s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}"
          ++ 10 :: after))) =
      (b₂ ++ 10 :: (lit s!"\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}" ++
        10 :: b₃)) ++ 10 ::
        (lit s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}"
          ++ 10 :: after) := by
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

/-- **The line-level lemma.**  Chunks that match the template and
parse, parse to records holding a theorem record of type `False`. -/
theorem parseChunks_jsonWithTheoremFalse {chunks : List ByteArray}
    (h : jsonWithTheoremFalse chunks)
    {inModel census : Bool} {r : ParseResultD}
    (hp : parseChunks chunks inModel census = .ok r) :
    ∃ cv vl, cv.type = .const falseName [] ∧ Declaration.thmDecl cv vl ∈ r.decls := by
  have hsz := parseChunks_ok_size hp
  rw [parseChunks_eq_parseLines inModel census chunks hsz] at hp
  obtain ⟨before, b₁, b₂, b₃, after, name, i, j, k, v, heq⟩ := h
  -- the bytes: the parts and the four lines, each ended by its newline
  have hb : bytes (concatBytes chunks) = lit before ++ 10 ::
      (lit s!"\{\"in\":{i},\"str\":\{\"pre\":0,\"str\":\"False\"}}" ++ 10 ::
      (lit b₁ ++ 10 ::
      (lit s!"\{\"ie\":{j},\"const\":\{\"name\":{i},\"us\":[]}}" ++ 10 ::
      (lit b₂ ++ 10 ::
      (lit s!"\{\"in\":{k},\"str\":\{\"pre\":0,\"str\":\"{name}\"}}" ++ 10 ::
      (lit b₃ ++ 10 ::
      (lit s!"\{\"thm\":\{\"all\":[{k}],\"levelParams\":[],\"name\":{k},\"type\":{j},\"value\":{v}}}"
        ++ 10 :: lit after))))))) := by
    rw [bytes_eq_of_size_lt hsz, heq, template_split]
    simp only [String.toUTF8_eq_toByteArray, String.toByteArray_append, ByteArray.data_append,
      Array.toList_append, ← lit_eq_toByteArray, lit_append, lit_nl, List.append_assoc,
      List.cons_append, List.nil_append]
  rw [hb] at hp
  cases hpl : parseLines (.init inModel census) _ 0 with
  | error e => rw [hpl] at hp; simp [Except.map] at hp
  | ok st' =>
    rw [hpl] at hp
    simp only [Except.map, Except.ok.injEq] at hp
    subst hp
    have h0 : (StateD.init inModel census).names.get? 0 = some .anonymous := by
      rw [init_names, IdTable.get?_singleton]; rfl
    obtain ⟨cv, vl, hty, hmem⟩ := parseLines_template _ _ _ _ _ i j k v name hpl h0
    exact ⟨cv, vl, hty, hmem⟩

end ConLeche.Frontend
