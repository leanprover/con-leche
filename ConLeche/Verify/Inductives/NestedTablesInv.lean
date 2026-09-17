module

public import ConLeche.Kernel.Inductives.NestedInstall
public import ConLeche.Verify.Inductives.StructWF

public section

/-!
# The nested install's table stage: inversion and well-formedness (task #315)

`nestedTables` (`ConLeche/Kernel/Inductives/NestedInstall.lean`) is the
LAST stage of the nested install: it walks the block's members —
restored name, recorded table, restored constructors — and at a
structure-like one conses that member's projection table
(`nestedMemberTable` → `checkStructProjTable`), at every other one
nothing.

This file reads that walk off the monad, as `MutualInv.lean` reads the
mutual route's twin (`mutualTables_inv`, `mutualMemberTable_inv`), and
carries `EnvWF` across it (`MutualWF.lean`'s `mutualTables_wf`).

The member step is SIMPLER than the mutual one: the nested route keeps
the scratch block's table and recomputes only its bodies, so the stage
matches on the pair `(tbl?, ctors)` and takes the table's own recorded
fields — its constructor name, level parameters, result sort, guards
and offset — rather than reading them back off a block record.  The
inversion is therefore a two-case `match` and not an `ownCtors`/`nIdx`
analysis.
-/

namespace ConLeche

/-! ## Inversion -/

/-- **One member's table stage**: nothing, or the table of a
structure-like member — a recorded table and exactly one restored
constructor — consed at the table's OWN recorded data. -/
theorem nestedMemberTable_inv {T : Name} {tbl? : Option ProjTable}
    {cs : List (ConstantVal × Nat × Nat)} {env env' : Env}
    (h : nestedMemberTable (m := CheckM) T tbl? cs env = .ok env') :
    env' = env ∨
    ∃ (tbl : ProjTable) (cvCa : ConstantVal) (nP nF : Nat),
      tbl? = some tbl ∧ cs = [(cvCa, nP, nF)] ∧
      checkStructProjTable (m := CheckM) T tbl.ctor tbl.levelParams nP nF tbl.structSort
        tbl.guards tbl.off cvCa env = .ok env' := by
  unfold nestedMemberTable at h
  cases tbl? with
  | none =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl h.symm
  | some tbl =>
    cases cs with
    | nil =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inl h.symm
    | cons c rest =>
      cases rest with
      | cons _ _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at h
        exact Or.inl h.symm
      | nil =>
        obtain ⟨cvCa, nP, nF⟩ := c
        exact Or.inr ⟨tbl, cvCa, nP, nF, rfl, rfl, h⟩

/-- The table stage over no member changes nothing. -/
theorem nestedTables_nil_inv {env env' : Env}
    (h : nestedTables (m := CheckM) [] env = .ok env') : env' = env := by
  simp only [nestedTables, pure, Except.pure, Except.ok.injEq] at h
  exact h.symm

/-- The table stage over the members, one at a time. -/
theorem nestedTables_inv {T : Name} {tbl? : Option ProjTable}
    {cs : List (ConstantVal × Nat × Nat)}
    {rest : List (Name × Option ProjTable × List (ConstantVal × Nat × Nat))} {env env' : Env}
    (h : nestedTables (m := CheckM) ((T, tbl?, cs) :: rest) env = .ok env') :
    ∃ envI, nestedMemberTable (m := CheckM) T tbl? cs env = .ok envI ∧
      nestedTables (m := CheckM) rest envI = .ok env' := by
  unfold nestedTables at h
  obtain ⟨envI, hI, h⟩ := exceptBind_ok h
  exact ⟨envI, hI, h⟩

/-! ## Well-formedness -/

/-- One member's table stage keeps the environment well-formed: it
conses nothing, or a table whose stage validated its own scoping
(`direct_table_wf`). -/
theorem nestedMemberTable_wf {T : Name} {tbl? : Option ProjTable}
    {cs : List (ConstantVal × Nat × Nat)} {env env' : Env} (henv : EnvWF env)
    (h : nestedMemberTable (m := CheckM) T tbl? cs env = .ok env') : EnvWF env' := by
  rcases nestedMemberTable_inv h with rfl | ⟨tbl, cvCa, nP, nF, -, -, htbl⟩
  · exact henv
  · exact direct_table_wf henv htbl

/-- The table stage at the run level. -/
theorem nestedTables_wf :
    ∀ {l : List (Name × Option ProjTable × List (ConstantVal × Nat × Nat))} {env env' : Env},
      EnvWF env → nestedTables (m := CheckM) l env = .ok env' → EnvWF env'
  | [], env, env', henv, h => by
    obtain rfl := nestedTables_nil_inv h
    exact henv
  | (T, tbl?, cs) :: rest, env, env', henv, h => by
    obtain ⟨envI, hI, hrest⟩ := nestedTables_inv h
    exact nestedTables_wf (nestedMemberTable_wf henv hI) hrest

end ConLeche
