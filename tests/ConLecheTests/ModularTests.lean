module

public import ConLeche.Modular

public section

/-!
# Modular checking's specification, pinned

A record at a `reduce*` name is presented only as itself: the statement of a definition
`Lean.reduceNat` (say `def Lean.reduceNat (n : Nat) : Nat := 0`) is not a presentation of it.
An importer accepts `Lean.ofReduceNat` by the stored operation's pinned statement, which is true
only of the identity its home's opaque install certifies.
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

end ConLecheTests.ModularTests
