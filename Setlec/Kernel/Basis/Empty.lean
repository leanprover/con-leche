import Setlec.Kernel.Basis.Builder

/-!
# The pinned `Empty` basis block

The raw pin — the `Empty` block exactly as the lean-inductive-models
preprocessor emits it (no constructors, hence no iota rules), which is
the toolchain's `Init.Prelude` declaration at the parser's raw binder
annotations.  The *annotated* forms (`emptyA`, `emptyRecA`) are
computed from these by the checker's own annotation pass at
elaboration time; see `Setlec/Kernel/BasisA.lean`.
-/

namespace Setlec

open BasisDSL

/-- `Empty : Type`. -/
def emptyRaw : ConstantInfo :=
  .indInfo ⟨emptyName, [], type1⟩ {}

/-- `Empty.rec.{u} (motive : Empty → Sort u) (t : Empty) : motive t`.
The exporter emits the motive as an *explicit* binder here (there is
no major premise to infer it from). -/
def emptyRecRaw : ConstantInfo :=
  .recInfo ⟨emptyName.str "rec", [uN],
    pi "motive" (pi "t" (cnst emptyName) (srt u)) <|
    pi "t" (cnst emptyName) (.app (bv 1) (bv 0))⟩
    1 1 []

/-- The pinned `Empty` basis block, in install order. -/
def emptyBasis : List ConstantInfo := [emptyRaw, emptyRecRaw]

end Setlec
