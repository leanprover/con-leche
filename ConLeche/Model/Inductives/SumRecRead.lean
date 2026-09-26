module

public import ConLeche.Model.Inductives.StructRecRead
import ConLeche.Model.Annot.BitInst
public section

/-!
# The generated sum recursor's readings (task #175 sum-types, indexed)

`ConLeche/Model/Inductives/StructRecRead.lean` at a constructor list over
an indexed family: the generated recursor type reads to the Π-tower
over `sumRecDataAV` (parameters, motive over the index telescope, one
minor per constructor, the index telescope again, major), with the
core `motive ı⃗ t`, and rule `j` reads to the λ-tower over
`sumRuleDataAV` at constructor `j`'s field data, with the core
`minor_j f⃗`.  The minor entries are read by one induction over the
constructor list (`denoteP_minorsPis` / `denoteP_minorsLams`), the
accumulated variables (the motive first, then the earlier minors)
threaded as `extras`.

The one genuinely new reading is the minor's conclusion
`motive e⃗ (C p⃗ f⃗)`: the constructor's index expressions, spelled at
the recursor frame (under the extras), read to the constructor's own
index readings lifted above the fields
(`denoteMetaSpine_idxArgs_lift`) — obtained by reading the whole opened
residual `T p⃗ e⃗` at that frame and inverting the application spine.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BinderMeta PropWhen)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## `AnnotTerm` bookkeeping -/

theorem liftN_mkAppN (n k : Nat) : ∀ (as : List AnnotTerm) (f : AnnotTerm),
    AnnotTerm.liftN n (AnnotTerm.mkAppN f as) k
      = AnnotTerm.mkAppN (AnnotTerm.liftN n f k) (as.map fun a => AnnotTerm.liftN n a k)
  | [], _ => rfl
  | a :: as, f => by
    simp only [AnnotTerm.mkAppN_cons, List.map_cons, liftN_mkAppN n k as, AnnotTerm.liftN_app]

theorem DenoteMetaSpine.unique {acval : Name → (Name → Nat) → AnnotTerm} {d : Nat} :
    ∀ {as : List Expr} {vs vs' : List AnnotTerm},
      DenoteMetaSpine acval env φ d as vs → DenoteMetaSpine acval env φ d as vs' → vs = vs'
  | [], _, _, .nil, .nil => rfl
  | _ :: _, _, _, .cons ha h, .cons ha' h' => by
    rw [Option.some.inj (ha.symm.trans ha'), DenoteMetaSpine.unique h h']

/-! ## The entries -/

/-- A constructor datum: name, field count, field data, index readings. -/
abbrev CtorDatum := Name × Nat × List (Nat × Nat × AnnotTerm) × List AnnotTerm

end ConLeche.Model
