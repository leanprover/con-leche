module

public import ConLeche.Model.Inductives.MutualRecRead
import ConLeche.Model.Annot.BitConsCross
import ConLeche.Semantics.ConstsBound
import ConLeche.Semantics.Install
import ConLeche.Model.Install
public section

/-!
# The mutual recursor stage's readings, from the run (task #278, M2.5a)

`FixRecData.lean` at a mutual block: member `mm`'s generated recursor
type (`mutualRecTy`, checked by `checkMutualRecTy`) read off the run —
the READING half, the stored recursor type's binder data
(`mutualRdsAV`) and its reading package (`MutualRecData`).

`SumRecData` does NOT fit: its `len`/`read` are the ONE-motive shape
(`nP + n + nIdx + 2` binders, core `recConcAV n nIdx`), while a mutual
member's recursor carries `k` motives (`nP + k + n + nIdx + 1` binders,
core `mutualConcAV k n nIdx mm`) — the two coincide only at `k = 1`.
`MutualRecData` is the same six clauses at that shape, with
`SumRecData.cross`'s cons-crossing lemma repeated.

No cross-member parameter identification is needed for the READING:
`mutualRecTy` takes the parameter Πs from former `0` and the index Πs
from member `mm`, and the data names exactly those (`ppsOf 0`,
`ipsOf mm`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The stored recursor type's data -/

/-- Member `mm`'s generated recursor type's binder data at the block. -/
@[expose] def mutualRdsAV {env : Env} (m : EnvModel V env) (k nP : Nat) (ℓ : Level)
    (Lof : Nat → (Name → Nat) → AnnotTerm) (nIdxOf : Nat → Nat)
    (ppsOf ipsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (cds : (Name → Nat) → List CtorDatumR) (mots : Nat → Nat) (tgts : Nat → Nat → Nat)
    (mm : Nat) (ψ : Name → Nat) : List (Nat × Nat × AnnotTerm) :=
  mutualRecDataAV m ψ ((List.range k).map fun t => Lof t ψ) nP ((List.range k).map nIdxOf) ℓ
    (ppsOf 0 ψ) ((List.range k).map fun t => ipsOf t ψ) (cds ψ) mots tgts mm

/-- **Member `mm`'s generated recursor type's reading, peeled**
(`SumRecData` at `k` motives): the same six clauses, at the `k`-motive
length `nP + k + n + nIdx + 1` and the `k`-motive core
`mutualConcAV k n nIdx mm`.  At `k = 1` the two shapes agree
(`recConcAV_eq_mutualConcAV`); for `k > 1` they do not, so this is its
own record. -/
structure MutualRecData {env : Env} (m : EnvModel V env) (cvR : ConstantVal)
    (nP k n nIdx mm : Nat) (elimL : Level)
    (rds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) : Prop where
  read : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvR.type
    = some (mkPisAV (rds ψ) (mutualConcAV k n nIdx mm))
  len : ∀ ψ : Name → Nat, (rds ψ).length = nP + k + n + nIdx + 1
  bits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ rds ψ →
    (elimL.eval ψ = 0 ↔ d.2.1 = 0)
  okTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    WellDenotedV V ρ (mkPisAV (rds ψ) (mutualConcAV k n nIdx mm))
  below : ∀ ψ : Name → Nat, DomsBelow 0 (rds ψ)
  params : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvR.levelParams, ψ₁ p = ψ₂ p) →
    rds ψ₁ = rds ψ₂

/-- The data crosses a cons whose slot does not mention the stored
recursor (`SumRecData.cross`). -/
theorem MutualRecData.cross {m : EnvModel V env} {cvR : ConstantVal}
    {nP k n nIdx mm : Nat} {elimL : Level}
    {rds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (h : MutualRecData m cvR nP k n nIdx mm elimL rds)
    {c₀ : ConstantInfo} {A : (Name → Nat) → AnnotTerm}
    (hfresh : env.find? c₀.name = none) (hat : ConsCrossAt c₀ cvR.type)
    (hcb : ConstsBound env cvR.type)
    (m₂ : EnvModel V ⟨c₀ :: env.consts⟩)
    (hac : m₂.acval = acvalWith m.acval c₀.name A) :
    MutualRecData m₂ cvR nP k n nIdx mm elimL rds where
  read ψ := by
    rw [hac]
    exact denoteMeta_cons_mono hfresh hat ψ 0 hcb (h.read ψ)
  len := h.len
  bits := h.bits
  okTy := h.okTy
  below := h.below
  params := h.params

end ConLeche.Model
