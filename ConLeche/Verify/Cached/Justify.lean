module

public import ConLeche.Cached.Decls

/-!
# The records a fold with a sidecar checks

`sideRecord` reads a definition whose value uses `sorryAx` as the axiom of its statement; doing so
twice is doing it once (`sideRecords_idem`), so the driver may hand the fold the records it
already read so (`checkDeclsIO`'s premise).
-/

public section

namespace ConLeche.Cached

open ConLeche

theorem sideRecord_idem (d : Declaration) : sideRecord (sideRecord d) = sideRecord d := by
  cases d with
  | defnDecl cv v h =>
    by_cases hc : (!builtinAxiomName cv.name && Expr.mentionsAnyConstC [sorryAxName] v) = true
    · simp only [sideRecord, hc, ↓reduceIte]
    · simp only [sideRecord, hc, Bool.false_eq_true, ↓reduceIte]
  | _ => rfl

theorem sideRecords_idem (j : Option Env) (ds : Array Declaration) :
    sideRecords j (sideRecords j ds) = sideRecords j ds := by
  cases j with
  | none => rfl
  | some e => simp [sideRecords, Array.map_map, Function.comp_def, sideRecord_idem]

/-- The fold reads its records through `sideRecords` itself. -/
theorem checkDecls_sideRecords (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat)
    (j : Option Env) (ds : Array Declaration) :
    checkDecls mode pins maxNatSize (sideRecords j ds) j = checkDecls mode pins maxNatSize ds j := by
  unfold checkDecls
  rw [sideRecords_idem]

end ConLeche.Cached
