module

public import ConLeche.Accepts
public import ConLeche.Verify.Frontend.Lines
public import ConLeche.Verify.Frontend.ApplyLine
import ConLeche.Verify.Frontend.ThmLine
import ConLeche.Verify.Frontend.FalseLines
import ConLeche.Verify.Frontend.Hoist
import ConLeche.Frontend.Scan.Equiv.Kit

public section

/-!
# From the file to the parsed record (task #290)

The line-level lemma: a file that matches `hasProofOfFalse`
(`ConLeche/Accepts.lean`) and parses, parses to a list holding a
`thmDecl` of type `False` — or the parser's taint skip took a
record, and the run declines (the clause goes with task #292).

The walk is the template's, line by line.  `parseLines_split` carries
the state across each arbitrary part to the next template line as a
line start; `Reach.keeps` says what those steps keep (bound entries,
pushed records, the prelude); the three line lemmas of
`ConLeche/Verify/Frontend/FalseLines.lean` say what each template line
scans to; `applyLine_nameFalse`, `applyLine_constFalse` and
`applyLine_thmFalse` say what the state does with it.  The name entry
for the theorem's own name is not read at all: it is absorbed into the
part before the theorem line, which may be anything.
-/

namespace ConLeche.Frontend

open ConLeche.Cached (DeclC ExprC)

/-! ## What a chain of lines keeps -/

theorem Keeps.trans {st st₁ st₂ : StateD} (h₁ : Keeps st st₁) (h₂ : Keeps st₁ st₂) :
    Keeps st st₂ :=
  ⟨fun i n h => h₂.names i n (h₁.names i n h), fun i e h => h₂.exprs i e (h₁.exprs i e h),
   fun d h => h₂.decls d (h₁.decls d h), h₂.prelude.trans h₁.prelude,
   fun h => h₂.skips (h₁.skips h)⟩

theorem Reach.keeps {st st' : StateD} (h : Reach st st') : Keeps st st' := by
  induction h with
  | refl => exact Keeps.refl _
  | step r h _ ih => exact (applyLine_keeps h).trans ih

/-! ## The initial state and the prelude index -/

theorem init_names (prelude : PreludeIx) (inModel census : Bool) :
    (StateD.init prelude inModel census).names = IdTable.singleton .anonymous := by
  unfold StateD.init
  refine Array.foldl_induction
    (motive := fun (_ : Nat) (st : StateD) => st.names = IdTable.singleton Name.anonymous) rfl ?_
  intro _ _ h; exact h

theorem init_prelude (prelude : PreludeIx) (inModel census : Bool) :
    (StateD.init prelude inModel census).prelude = prelude := by
  unfold StateD.init
  refine Array.foldl_induction (motive := fun (_ : Nat) (st : StateD) => st.prelude = prelude) rfl ?_
  intro _ _ h; exact h

theorem init_taintSkipped (prelude : PreludeIx) (inModel census : Bool) :
    (StateD.init prelude inModel census).taintSkipped = #[] := by
  unfold StateD.init
  refine Array.foldl_induction (motive := fun (_ : Nat) (st : StateD) => st.taintSkipped = #[])
    rfl ?_
  intro _ _ h; exact h

/-- Inserting a record under its names: a lookup finds it or what was there. -/
theorem foldl_insert_getElem? {m : Std.HashMap Name DeclC} {d d' : DeclC} {n : Name} :
    ∀ {l : List Name}, (l.foldl (fun m n => m.insert n d) m)[n]? = some d' →
      d' = d ∨ m[n]? = some d' := by
  intro l
  induction l generalizing m with
  | nil => intro h; exact .inr h
  | cons x l ih =>
    intro h
    rcases ih h with h | h
    · exact .inl h
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · simp only [Option.some.injEq] at h; exact .inl h.symm
      · exact .inr h

/-- The prelude index resolves a name to one of its own records. -/
theorem PreludeIx.ofDecls_byName {ds : Array DeclC} {n : Name} {d : DeclC}
    (h : (PreludeIx.ofDecls ds).byName[n]? = some d) : d ∈ (PreludeIx.ofDecls ds).decls := by
  unfold PreludeIx.ofDecls at h ⊢
  revert h
  refine Array.foldl_induction
    (motive := fun (_ : Nat) (ix : PreludeIx) => ∀ d : DeclC, ix.byName[n]? = some d → d ∈ ix.decls)
    ?_ ?_ d
  · intro d h; simp at h
  · intro i ix hix d
    split
    · intro h; exact Array.mem_push.mpr (.inl (hix d h))
    · intro h
      rcases foldl_insert_getElem? h with rfl | h
      · exact Array.mem_push.mpr (.inr rfl)
      · exact Array.mem_push.mpr (.inl (hix d h))

/-- The built-in prelude's index resolves names to its records. -/
theorem builtinPrelude_byName {prelude : PreludeIx} (h : builtinPreludeE = .ok prelude)
    (n : Name) (d : DeclC) (hd : prelude.byName[n]? = some d) : d ∈ prelude.decls := by
  unfold builtinPreludeE at h
  cases hp : parseExportD builtinPreludeText with
  | error e => rw [hp] at h; simp [Functor.map, Except.map] at h
  | ok r =>
    rw [hp] at h
    simp only [Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact PreludeIx.ofDecls_byName hd

/-! ## The bytes of a file that matches the template -/

theorem lit_nl : lit "\n" = [10] := by rw [lit_eq_toByteArray]; decide

/-! ## The walk -/

/-- **The line-level lemma over the line fold.** -/
theorem parseLines_hasProofOfFalse {s : String} (h : hasProofOfFalse s) {st st' : StateD}
    {n : Nat} (hp : parseLines st (lit s) n = .ok st')
    (h0 : st.names.get? 0 = some .anonymous)
    (hpre : ∀ (n : Name) (d : DeclC), st.prelude.byName[n]? = some d → d ∈ st.prelude.decls) :
    st'.taintSkipped ≠ #[] ∨ ∃ cv vl, cv.type = .const falseName [] ∧
      (DeclC.thmDecl cv vl ∈ st.prelude.decls ∨ DeclC.thmDecl cv vl ∈ st'.decls) := by
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
  have K₂ := applyLine_keeps h₂
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
  have hj : st₄.exprs.get? j = some (ExprC.mkConst falseName []) :=
    applyLine_constFalse h₄ (K₃.names i _ hi)
  have K₄ := applyLine_keeps h₄
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
  have hprel : st₅.prelude = st.prelude := by
    rw [K₅.prelude, K₄.prelude, K₃.prelude, K₂.prelude, K₁.prelude]
  have F := applyLine_thmFalse h₆ (K₅.exprs j _ hj)
    (fun n d hd => by rw [hprel] at hd ⊢; exact hpre n d hd)
  -- the part after
  have r₇ := parseLines_reach _ _ (Nat.le_refl _) _ _ _ hp
  have K₇ := r₇.keeps
  rcases F with hskip | ⟨cv, vl, hty, hmem⟩
  · exact .inl (K₇.skips hskip)
  · refine .inr ⟨cv, vl, hty, ?_⟩
    rcases hmem with hm | hm
    · exact .inl (hprel ▸ hm)
    · exact .inr (K₇.decls _ hm)

/-- **The line-level lemma.**  A file that matches the template and
parses, parses to a list holding a theorem record of type `False` — or
the parser skipped a record for using a tolerated axiom. -/
theorem parseExportD_hasProofOfFalse {s : String} (h : hasProofOfFalse s)
    (hsz : s.utf8ByteSize < USize.size) {prelude : PreludeIx}
    (hpre : ∀ (n : Name) (d : DeclC), prelude.byName[n]? = some d → d ∈ prelude.decls)
    {inModel census : Bool} {r : ParseResultD}
    (hp : parseExportD s prelude inModel census = .ok r) :
    r.taintSkipped ≠ #[] ∨ ∃ cv vl, cv.type = .const falseName [] ∧
      DeclC.thmDecl cv vl ∈ r.decls.toList := by
  rw [parseExportD_eq_parseLines s prelude inModel census hsz] at hp
  cases hpl : parseLines (.init prelude inModel census) (lit s) 0 with
  | error e => rw [hpl] at hp; simp [Except.map] at hp
  | ok st' =>
    rw [hpl] at hp
    simp only [Except.map, Except.ok.injEq] at hp
    subst hp
    have h0 : (StateD.init prelude inModel census).names.get? 0 = some .anonymous := by
      rw [init_names, IdTable.get?_singleton]; rfl
    have hpre' : ∀ (n : Name) (d : DeclC),
        (StateD.init prelude inModel census).prelude.byName[n]? = some d →
        d ∈ (StateD.init prelude inModel census).prelude.decls := by
      rw [init_prelude]; exact hpre
    rcases parseLines_hasProofOfFalse h hpl h0 hpre' with hskip | ⟨cv, vl, hty, hmem⟩
    · exact .inl (by rw [ofState_taintSkipped]; exact hskip)
    · refine .inr ⟨cv, vl, hty, Array.mem_def.mp ?_⟩
      rcases hmem with hm | hm
      · rw [init_prelude] at hm
        have : cv.type = cv.type := rfl
        exact mem_ofState_prelude (st := st') (by
          have hp' : st'.prelude = prelude := by
            rw [(parseLines_reach _ _ (Nat.le_refl _) _ _ _ hpl).keeps.prelude, init_prelude]
          rw [hp']; exact hm)
      · exact mem_ofState_decls hm

end ConLeche.Frontend
