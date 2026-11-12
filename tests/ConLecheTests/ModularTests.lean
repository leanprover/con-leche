module

public import ConLeche.Modular
public import ConLeche.Driver.Reach
/- The `#guard`s are evaluated, so the reach is needed at the meta level too. -/
meta import ConLeche.Driver.Reach

public section

/-!
# Modular checking's specification, pinned

A record at a `reduce*` name is presented only as itself: the statement of a definition
`Lean.reduceNat` (say `def Lean.reduceNat (n : Nat) : Nat := 0`) is not a presentation of it.
An importer accepts `Lean.ofReduceNat` by the stored operation's pinned statement, which is true
only of the identity its home's opaque install certifies.

A context record's constructor is validated against the family it is stored under: its type
concludes in that family (`constOk`, the context's `CtorWF`), or the record is refused.
-/

namespace ConLecheTests.ModularTests

open ConLeche ConLeche.Modular

example (lps : List Name) (ty v : Expr) (h : ReducibilityHint) :
    ¬ Presents (.axiomDecl ⟨reduceNatName, lps, ty⟩) (.defnDecl ⟨reduceNatName, lps, ty⟩ v h) := by
  rintro (⟨hc, -⟩ | ⟨-, hn⟩)
  · have hq : reduceNatName ≠ quotSoundName := by decide
    have hs : reduceNatName ≠ sorryAxName := by decide
    simp [declConstants, hq, hs] at hc
  · exact hn reduceNatName (by simp [declConstants]; rfl) (by decide)

/-- A constructor `T.c : T`, stored under the family `fam`. -/
def ctorUnder (fam : Name) : ConstantInfo :=
  .ctorInfo ⟨(Name.str .anonymous "T").str "c", [], .const (.str .anonymous "T") []⟩ 0 0 fam

#guard Driver.constOk (ctorUnder (.str .anonymous "T"))
#guard !Driver.constOk (ctorUnder (.str .anonymous "U"))

end ConLecheTests.ModularTests
