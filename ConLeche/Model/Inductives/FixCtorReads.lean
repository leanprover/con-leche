module

public import ConLeche.Model.Inductives.FixRecReadDefs
public section

/-!
# The recursive constructors' reading premises (task #188)

The per-constructor facts of a recursive block (`FixCtorDataI`,
`FixDataP.lean` — the sum route's data with the field kinds, the
opened form, the per-field telescopes and index readings) yield the
reading premises `CtorReadsR` (`FixRecReadDefsP.lean`) the generated
recursor's reading theorems consume.  The bridge is that an opened
variable's type is its binder's domain instantiated at the earlier
variables (`openPisAtFvars_fvarTypeD`), and that instantiation at
variables changes neither the domain's leading `∀`-count
(`Expr.piBinders_instSeq`, whence `teleLen` off `reflOpen`'s binder
count) nor its body's argument count (`getAppArgs_instSeq_fvars`,
whence `fieldArity` off the opened form).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## Instantiation at variables and the argument spine -/

/-! ## The constructor data, per block -/

/-- The recursive constructor data of a list of constructors, from
constructor `j` on. -/
@[expose] def fixCtorDataList (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    List (ConstantVal × Nat) → Nat → List CtorDatumR
  | [], _ => []
  | c :: cs, j =>
    (c.1.name, c.2, dsF j ψ, esF j ψ, ConLeche.recIdxOf (ksF j), eissF j ψ, tssF j ψ) ::
      fixCtorDataList dsF esF ksF eissF tssF ψ cs (j + 1)

omit [SetTheory V] in
theorem fixCtorDataList_length (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j : Nat),
      (fixCtorDataList dsF esF ksF eissF tssF ψ cs j).length = cs.length
  | [], _ => rfl
  | _ :: cs, j => by
    simp [fixCtorDataList, fixCtorDataList_length dsF esF ksF eissF tssF ψ cs (j + 1)]

omit [SetTheory V] in
theorem fixCtorDataList_getElem? (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j i : Nat),
      (fixCtorDataList dsF esF ksF eissF tssF ψ cs j)[i]?
        = (cs[i]?).map fun c =>
            (c.1.name, c.2, dsF (j + i) ψ, esF (j + i) ψ, ConLeche.recIdxOf (ksF (j + i)),
              eissF (j + i) ψ, tssF (j + i) ψ)
  | [], _, _ => rfl
  | c :: cs, j, 0 => by simp [fixCtorDataList]
  | c :: cs, j, i + 1 => by
    simp only [fixCtorDataList, List.getElem?_cons_succ]
    rw [fixCtorDataList_getElem? dsF esF ksF eissF tssF ψ cs (j + 1) i]
    congr 2
    funext c
    rw [show j + 1 + i = j + (i + 1) from by omega]

end ConLeche.Model
