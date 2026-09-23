module

public import ConLeche.Model.Inductives.SumRecData
public import ConLeche.Model.Inductives.SumStageCtor
import ConLeche.Model.Inductives.StructRecRead
public section

/-!
# The sum recursor's frames (task #175 sum-types, indexed)

`sumRecFrames`: at a parameter frame, the generated sum recursor's
entries read to the recursor leaf's premise `RecBaseS` — the motive
entry to the nested product over the former's index telescope into
the family at each index tuple, minor entry `j` (at the frame under
the motive and the earlier minors) to constructor `j`'s minor space
`minorSpI` (its conclusion at the constructor's own index values),
the index entries to the former's index telescope, the major entry
to the family at the frame's index tuple — and the K-frame's two
hypothesis records (`RecHypS`, `SqHypS`).  The walk: down the minor
chain (`sumMinorsTail`), then down the index chain (`sumIdxTail`),
the frame kept as an explicit `consList`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The chains of a data list -/

/-- The field chains of the constructor data (at the parameter
frame). -/
@[expose] def fssOf (nP : Nat) (cds : List CtorDatum) : List (List AnnotTerm) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The index readings of the constructor data. -/
@[expose] def essOf (cds : List CtorDatum) : List (List AnnotTerm) :=
  cds.map fun cd => cd.2.2.2

theorem fssOf_getElem? (nP : Nat) (cds : List CtorDatum) (j : Nat) :
    (fssOf nP cds)[j]? = cds[j]?.map fun cd => (cd.2.2.1.drop nP).map (·.2.2) := by
  simp [fssOf]

theorem essOf_getElem? (cds : List CtorDatum) (j : Nat) :
    (essOf cds)[j]? = cds[j]?.map fun cd => cd.2.2.2 := by
  simp [essOf]

/-! ## The nested product over a telescope, read -/

/-- **A Π-tower over nonzero-bit domains is the nested product** over
the domains' telescope, the body at the accumulated tuple. -/
theorem interp_mkPisAV_piTele {v : Nat} {B : List V → V} {R : AnnotTerm} :
    ∀ {gds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V} {acc : List V},
      (∀ d ∈ gds, (d.2.1 = 0 ↔ v = 0)) →
      (∀ as : List V, SpineFit σ (gds.map (·.2.2)) as → interp V (consList as σ) R = B (acc ++ as)) →
      interp V σ (mkPisAV gds R) = piTele v (teleOfFields σ (gds.map (·.2.2))) B acc
  | [], σ, acc, _, hbase => by
    have := hbase [] trivial
    simp only [consList, List.append_nil] at this
    simp only [mkPisAV]
    exact this
  | d :: gds, σ, acc, hbits, hbase => by
    simp only [mkPisAV, interp_pi]
    rw [piR_congr_bit (v := d.2.1) (v' := v) (hbits d List.mem_cons_self)]
    apply piR_congr
    intro a ha
    refine interp_mkPisAV_piTele (fun d' hd' => hbits d' (List.mem_cons_of_mem _ hd')) ?_
    intro as hsp
    have := hbase (a :: as) ⟨ha, hsp⟩
    rw [consList_cons] at this
    rw [this, List.append_assoc, List.singleton_append]

end ConLeche.Model
