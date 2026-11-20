module

public import ConLeche.Cached.StreamIndex
import ConLeche.Verify.Cached.WalkersC

public section

/-!
# The index does not look at a theorem's value (task #481)

`buildIndex_fill`: the frozen index of records whose theorems hold one value is the index of the
same records holding any other.  A theorem enters the index by its statement (`declConstants`), so
nothing in it depends on the value; this is what lets an `.olean` run build the index while a
theorem's value is still in the file, and read it in the theorem's check.
-/

namespace ConLeche.Cached

open ConLeche

/-- A record with its theorem's value replaced by `F` of it. -/
@[expose] def fillDecl (F : Expr → Expr) : Declaration → Declaration
  | .thmDecl cv v => .thmDecl cv (F v)
  | d => d

variable (F : Expr → Expr)

theorem declConstants_fillDecl (d : Declaration) : declConstants (fillDecl F d) = declConstants d := by
  cases d <;> rfl

theorem declTables_fillDecl (d : Declaration) : declTables (fillDecl F d) = declTables d := by
  cases d <;> rfl

theorem StreamIndex.add_fillDecl (I : StreamIndex) (d : Declaration) :
    I.add (fillDecl F d) = I.add d := by
  simp only [StreamIndex.add, declConstantsC_eq, declConstants_fillDecl, declTablesC_eq,
    declTables_fillDecl]

/-- **The index, at any theorems' values.** -/
theorem buildIndex_fill (ds : Array Declaration) :
    buildIndex (ds.map (fillDecl F)) = buildIndex ds := by
  simp only [buildIndex, Array.foldl_map, StreamIndex.add_fillDecl]

/-- **The environment of the records does not look at a theorem's value.** -/
theorem streamEnv_fill (ds : Array Declaration) (env : Env := Env.empty) :
    streamEnv (ds.map (fillDecl F)).toList env = streamEnv ds.toList env := by
  simp only [streamEnv, Array.toList_map, List.foldl_map, declConstants_fillDecl,
    declTables_fillDecl]

/-- **The record mates do not look at a theorem's value** either: only inductive blocks have
mates. -/
theorem recordMates_fill (ds : Array Declaration) :
    recordMates (ds.map (fillDecl F)) = recordMates ds := by
  simp only [recordMates, Array.foldl_map]
  congr
  funext m d
  cases d <;> rfl

/-- **Nor does the solution a fold reads.** -/
theorem solutionOf_fill (justify : Option Env) (ds : Array Declaration) :
    solutionOf justify (ds.map (fillDecl F)) = solutionOf justify ds := by
  simp only [solutionOf, recordMates_fill]

end ConLeche.Cached
