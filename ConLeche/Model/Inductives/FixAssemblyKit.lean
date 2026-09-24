module

public import ConLeche.Model.Inductives.FixStageRec
public import ConLeche.Model.Inductives.FixStageFormer
public import ConLeche.Model.Inductives.FixCtorsLoop
import ConLeche.Model.Inductives.FixCtorCross
public section

/-!
# Kit for the direct recursive install's assembly (task #188)

The pieces `declNative` joins: the two routes' data lists
identified (`fssOfR_fixCtorDataList`, `essOfR_fixCtorDataList`), the
constructors' data identified across the dummy and the real formers
(`blockCtorDataI_ident`), the former's index telescope valid at the
parameter frame (`idxValid_of`, beside `idxOk_of`), and the chain
validity facts of a recursive constructor (`blockChainValidFacts_of`,
beside `fixChainFacts_of`: the validity halves of the shadow
gradings).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w'

variable {V : Type w'} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The two routes' data lists -/

omit [SetTheory V] in
/-- The recursive route's field chains are the sum route's. -/
theorem fssOfR_fixCtorDataList (nP : Nat) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (k : Nat),
      fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ cs k) = fssOf nP (ctorDataList dsF esF ψ cs k)
  | [], _ => rfl
  | c :: cs, k => by
    show _ :: fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ cs (k + 1))
      = _ :: fssOf nP (ctorDataList dsF esF ψ cs (k + 1))
    rw [fssOfR_fixCtorDataList nP dsF esF ksF eissF tssF ψ cs (k + 1)]

omit [SetTheory V] in
/-- The recursive route's index readings are the sum route's. -/
theorem essOfR_fixCtorDataList (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (ksF : Nat → List RecFieldKind)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))) (ψ : Name → Nat) :
    ∀ (cs : List (ConstantVal × Nat)) (k : Nat),
      essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs k) = essOf (ctorDataList dsF esF ψ cs k)
  | [], _ => rfl
  | c :: cs, k => by
    show _ :: essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs (k + 1))
      = _ :: essOf (ctorDataList dsF esF ψ cs (k + 1))
    rw [essOfR_fixCtorDataList dsF esF ksF eissF tssF ψ cs (k + 1)]

/-! ## The index telescope, valid -/

/-- **The former's index telescope**, valid at the parameter frame
(beside `idxOk_of`). -/
theorem idxValid_of (mp : EnvModelM V μ env)
    {nP nIdx : Nat} {resSort : Level} {cvTa : ConstantVal} {T : Name}
    {caps : IndCaps} (hfT : env.find? T = some (.indInfo cvTa caps))
    {tfvs : List Expr} {trest : Expr}
    (hopT : openPisAtFvars (nP + nIdx) cvTa.type 0 = some (tfvs, trest))
    {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData mp.base2 cvTa (nP + nIdx) resSort ppsAll)
    (ψ : Name → Nat) (ρp : Nat → V)
    (hρp : Sat V (((ppsAll ψ).take nP).map (·.2.2)).reverse ρp) :
    FieldsValid ρp (((ppsAll ψ).drop nP).map (·.2.2)) := by
  obtain ⟨hTf, -, -, hTb, -⟩ := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfT)
  simp only [ConstantInfo.toConstantVal] at hTf hTb
  have hT : Opened mp.base2 ψ (nP + nIdx) cvTa.type tfvs trest
      (((ppsAll ψ).map (·.2.2)).reverse) (.sort (resSort.eval ψ)) :=
    opened_of_peel hopT hTf hTb (hFD.read ψ) (hFD.len ψ) (hFD.okTy ψ)
  have hΓ : (((ppsAll ψ).map (·.2.2)).reverse).length = nP + nIdx := by simp [hFD.len ψ]
  have hρp' : Sat V ((((ppsAll ψ).map (·.2.2)).reverse).drop (nP + nIdx - (nP + 0))) ρp := by
    rw [Nat.add_zero, drop_fields_eq (hFD.len ψ) nP (Nat.le_refl _), Nat.sub_self, List.drop_zero]
    exact hρp
  have hv := fieldsValid_of_frame rfl hΓ hT.okΓ 0 (Nat.zero_le _) ρp hρp'
  rw [fieldsFrom_eq_drop (hFD.len ψ)] at hv
  exact hv

/-! ## The chain validity facts -/

/-! ## The data lists, congruent in one component -/

omit [SetTheory V] in
theorem fssOfR_fixCtorDataList_getD {nP : Nat} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat}
    {cs : List (ConstantVal × Nat)} {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    (fssOfR nP (fixCtorDataList dsF esF ksF eissF tssF ψ cs 0)).getD j []
      = ((dsF j ψ).drop nP).map (·.2.2) := by
  rw [List.getD_eq_getElem?_getD, fssOfR_getElem?, fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl

omit [SetTheory V] in
theorem essOfR_fixCtorDataList_getD {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {esF : Nat → (Name → Nat) → List AnnotTerm} {ksF : Nat → List RecFieldKind}
    {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
    {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))} {ψ : Name → Nat}
    {cs : List (ConstantVal × Nat)} {j : Nat} {cA : ConstantVal × Nat} (hj : cs[j]? = some cA) :
    (essOfR (fixCtorDataList dsF esF ksF eissF tssF ψ cs 0)).getD j [] = esF j ψ := by
  rw [List.getD_eq_getElem?_getD, essOfR_getElem?, fixCtorDataList_getElem?, hj, Nat.zero_add]; rfl

end ConLeche.Model
