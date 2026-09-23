module

import ConLeche.Model.Inductives.SumRecRead
public import ConLeche.Model.Inductives.SumData
import ConLeche.Model.Inductives.StructStageCtor
public section

/-!
# The sum recursor's data (task #175 sum-types, indexed)

`SumRecData`: the generated sum recursor type's reading, peeled — the
`RecData` of the single-constructor route with `n` minor entries, the
index telescope re-emitted after the minors, and the core
`motive ı⃗ t`; read off the generated type by `sumRecData_of`, and
rule `j`'s reading and grading by `sumRuleData_of`.  The constructors'
data (field data, index readings, sources) is carried as functions of
the position (`ctorDataList`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The constructors' data, positionally -/

/-- The constructor data list from position-indexed data functions. -/
@[expose] def ctorDataList (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ψ : Name → Nat) :
    List (ConstantVal × Nat) → Nat → List CtorDatum
  | [], _ => []
  | c :: cs, j => (c.1.name, c.2, dsF j ψ, esF j ψ) :: ctorDataList dsF esF ψ cs (j + 1)

theorem ctorDataList_getElem? (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (j i : Nat),
      (ctorDataList dsF esF ψ cs j)[i]? = cs[i]?.map fun c => (c.1.name, c.2, dsF (j + i) ψ, esF (j + i) ψ)
  | [], _, _ => by simp [ctorDataList]
  | c :: cs, j, 0 => by simp [ctorDataList]
  | c :: cs, j, i + 1 => by
    simp only [ctorDataList, List.getElem?_cons_succ]
    rw [ctorDataList_getElem? dsF esF ψ cs (j + 1) i, show j + 1 + i = j + (i + 1) from by omega]

theorem ctorDataList_params {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ψ₁ ψ₂ : Name → Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {j : Nat},
      (∀ i, i < cs.length → dsF (j + i) ψ₁ = dsF (j + i) ψ₂ ∧ esF (j + i) ψ₁ = esF (j + i) ψ₂) →
      ctorDataList dsF esF ψ₁ cs j = ctorDataList dsF esF ψ₂ cs j
  | [], _, _ => rfl
  | _ :: cs, j, h => by
    simp only [ctorDataList]
    obtain ⟨h0d, h0e⟩ := h 0 (by simp)
    rw [Nat.add_zero] at h0d h0e
    rw [h0d, h0e]
    congr 1
    exact ctorDataList_params fun i hi => by
      rw [show j + 1 + i = j + (i + 1) from by omega]
      exact h (i + 1) (by simpa using hi)

/-- What the readings need of every constructor at its position:
stored, at the block's level parameters, and its data. -/
@[expose] def CtorFactsAt {env : Env} (m : EnvModel V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (j : Nat) (cA : ConstantVal × Nat) : Prop :=
  env.find? cA.1.name = some (.ctorInfo cA.1 nP cA.2) ∧
  cA.1.levelParams = lps ∧
  CtorDataI m T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF j) (dsF j) (esF j) (srcsF j)

end ConLeche.Model
