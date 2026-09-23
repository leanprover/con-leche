module

import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Inductives.FixStageTable
public import ConLeche.Model.Inductives.FixZeroField
import ConLeche.Verify.Inductives.SumWF
import ConLeche.Verify.Inductives.SumInv
import ConLeche.Kernel.Inductives.NativeInstall
import ConLeche.Verify.Inductives.FixParts
public section

/-!
# The direct recursive install, assembled (task #188)

`declNative`: the P carrier survives the direct recursive
install's run (`DeclNativeRun`).  The stages: the former twice —
first the sum route's stage with the empty chain list, a carrier at
which the constructors' recursive data (`fixCtorFuns_of`) and the
former's index telescope (`idxOk_of`, `idxValid_of`) are read; then
the fixed-point stage (`stageFixFormer`) over the X-chains of that
data (`xChainsOk_of`), the leaf's fields `Fss₀` — the constructors
in order (`ctorsLoopGen`, the fibre fold from the fixed-point leaf
through `fixLeafApp` and `fixFamI_app_eq_sum`, the invariant carrying
every constructor's recursive data across the conses), and the
recursor (`stageFixRec`).  The data at the real former is identified
with the data at the dummy former except at the recursive fields
(`fixCtorDataI_ident`), whose real readings are the family at the
index tuple (`chainRealI_of`): the real chains `ChainsRealI` against
the leaf's.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps InductiveShape
  NativeParts BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Kit -/

/-- A fitting spine's prefix fits the fields' prefix. -/
theorem spineFit_take {Fs : List AnnotTerm} {ρ : Nat → V} {as : List V}
    (h : SpineFit ρ Fs as) {i : Nat} (hi : i ≤ Fs.length) :
    SpineFit ρ (Fs.take i) (as.take i) := by
  have h' : SpineFit ρ (Fs.take i ++ Fs.drop i) as := by rw [List.take_append_drop]; exact h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_inv h'
  have hl : as₁.length = i := by
    rw [h1.length_eq, List.length_take]; exact Nat.min_eq_left hi
  have : as.take i = as₁ := by
    rw [heq, List.take_append, List.take_of_length_le (Nat.le_of_eq hl), hl, Nat.sub_self,
      List.take_zero, List.append_nil]
  rw [this]
  exact h1

end ConLeche.Model
