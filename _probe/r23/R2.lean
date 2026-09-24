import ConLeche.Model.Annot.BlockLfp
import ConLeche.Model.NatEqs
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.StructRecSpine

/-!
# R23PROBE / R2: O12's field-segment row at an instantiated container constructor

`nest_rose_tree`'s auxiliary constructor `List.cons.{u}` at `Ds = [Rose α]`.
The rule contract's field segment reads the Π-domains of the
INSTANTIATED constructor type, `Rose α` and `List (Rose α)` (the second
under the first field's binder), by `denoteMeta` at the rule frame.  The
row: those readings fit a spine exactly when the spine fits `List`'s
RECORDED fields with holes (`LfpDatum.fields`) at the hole frame of the
container's carrier at the instantiated parameter `⟦Rose α⟧`.

The recorded datum `D` is abstract: what is used of it is its clause
(`LfpClause`, only `leaf`), its hole-form cons fields as the uniform
install records them (`absF` of `List.cons`: the head is the parameter
`.bvar 1` above the one hole, the tail the hole applied to the parameter
`.app (.bvar 1) (.bvar 2)`), and the member's own parameter telescope's
length and `Sat`-transfer — which the install proves (`BlockHoleFacts.parsLen`/
`parsSat`, `Model/Inductives/BlockLfpHoles.lean:458`) but the clause does NOT
record.  `hDs` is the instantiation's parameter typing (L3 (ii)'s per-key
typing: `⟦Rose α⟧` fits `List`'s parameter telescope).
-/

open ConLeche ConLeche.Model ConLeche.Semantics ConLeche.SetTheory ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)

universe w
variable {V : Type w} [ConLeche.SetTheory V]

namespace R23

/-- **The field-segment row, `List.cons` at `Ds = [Rose α]`.** -/
theorem listCons_fieldSeg {env : Env} (m : EnvModel V env) (φ : Name → Nat)
    {ListN RoseN : Name} {us : List Level} {ciL ciR : ConstantInfo}
    (hfL : env.find? ListN = some ciL) (hlL : us.length = ciL.toConstantVal.levelParams.length)
    (hfR : env.find? RoseN = some ciR) (hlR : us.length = ciR.toConstantVal.levelParams.length)
    {D : LfpDatum V} (hC : LfpClause m.acval D) (hk : D.k = 1) (hmem : D.member 0 = ListN)
    -- the recorded datum at the use's level assignment
    (hF : D.fields (Level.substFn φ ciL.toConstantVal.levelParams us) 0 1
      = [.bvar 1, .app (.bvar 1) (.bvar 2)])
    (hparsLen : (D.pars 0 (Level.substFn φ ciL.toConstantVal.levelParams us)).length = 1)
    (hparsSat : ∀ ρ : Nat → V, Sat V (D.params (Level.substFn φ ciL.toConstantVal.levelParams us)).reverse ρ →
      Sat V (D.pars 0 (Level.substFn φ ciL.toConstantVal.levelParams us)).reverse ρ)
    (hids : D.ids 0 (Level.substFn φ ciL.toConstantVal.levelParams us) = [])
    -- the block parameter `α` is the variable `a`, the rule frame has depth `D0`
    {a D0 : Nat} (ha : a < D0) (tyA : Expr) (ρ ρ0 : Nat → V)
    (hDs : SpineFit ρ0 (D.params (Level.substFn φ ciL.toConstantVal.levelParams us))
      [interp V ρ (.app (m.acval RoseN (Level.substFn φ ciR.toConstantVal.levelParams us))
        (.bvar (D0 - 1 - a)))]) :
    ∃ R0 R1 : AnnotTerm,
      denoteMeta m.acval env φ D0 (.app (.const RoseN us) (.fvar a tyA)) = some R0 ∧
      denoteMeta m.acval env φ (D0 + 1)
        (.app (.const ListN us) (.app (.const RoseN us) (.fvar a tyA))) = some R1 ∧
      ∀ fs : List V, SpineFit ρ [R0, R1] fs ↔
        SpineFit
          (D.frame (Level.substFn φ ciL.toConstantVal.levelParams us) (consList [interp V ρ R0] ρ0)
            (D.carrier (Level.substFn φ ciL.toConstantVal.levelParams us) (consList [interp V ρ R0] ρ0)))
          (D.fields (Level.substFn φ ciL.toConstantVal.levelParams us) 0 1) fs := by
  -- names for the two level assignments and the instantiated parameter's value
  generalize hψL : Level.substFn φ ciL.toConstantVal.levelParams us = ψL at *
  generalize hψR : Level.substFn φ ciR.toConstantVal.levelParams us = ψR at *
  refine ⟨.app (m.acval RoseN ψR) (.bvar (D0 - 1 - a)),
    .app (m.acval ListN ψL) (.app (m.acval RoseN ψR) (.bvar (D0 + 1 - 1 - a))), ?_, ?_, ?_⟩
  · rw [denoteMeta_app, denoteMeta_const hfR hlR, denoteMeta_fvar, hψR]; rfl
  · rw [denoteMeta_app, denoteMeta_const hfL hlL, denoteMeta_app, denoteMeta_const hfR hlR,
      denoteMeta_fvar, hψL, hψR]; rfl
  intro fs
  generalize hx : interp V ρ (.app (m.acval RoseN ψR) (.bvar (D0 - 1 - a))) = x at *
  -- the parameter frame, its `Sat`, and the carrier
  have hsatP : Sat V (D.params ψL).reverse (consList [x] ρ0) := by
    have := sat_of_spineFit (Sat_nil V ρ0) hDs
    simpa using this
  generalize hX : D.carrier ψL (consList [x] ρ0) = X
  -- the frame is the parameter frame with the one hole above it
  have hframe : D.frame ψL (consList [x] ρ0) X = cons (D.holeVal ψL (consList [x] ρ0) X 0) (cons x ρ0) := by
    unfold LfpDatum.frame
    rw [hk]
    rfl
  -- the tail's set, concretely: `⟦List⟧ ⟦Rose α⟧` by the LEAF
  have hleaf := hC.leaf 0 (by rw [hk]; decide) ψL ρ0 [x] [] hDs (by rw [hids]; trivial)
  rw [hmem, hX] at hleaf
  have htailC : ∀ h, interp V (cons h ρ)
      (.app (m.acval ListN ψL) (.app (m.acval RoseN ψR) (.bvar (D0 + 1 - 1 - a))))
        = app (X 0) (tupW (D.u 0 ψL) []) := by
    intro h
    rw [← hleaf]
    simp only [interp_app, interp_bvar, List.append_nil, List.foldl_cons, List.foldl_nil]
    rw [show D0 + 1 - 1 - a = (D0 - 1 - a) + 1 by omega, cons_succ,
      acval_interp_closedC m ListN ψL (cons h ρ) ρ0]
    congr 1
    rw [← hx, interp_app, acval_interp_closedC m RoseN ψR (cons h ρ) ρ]
    rfl
  -- the tail's set, in hole form: the hole applied to the parameter, `holeVal_app`
  have htailH : ∀ h, interp V (cons h (D.frame ψL (consList [x] ρ0) X)) (.app (.bvar 1) (.bvar 2))
      = app (X 0) (tupW (D.u 0 ψL) []) := by
    intro h
    have hv := LfpDatum.holeVal_app (D := D) (X := X) (m := 0) (is := [])
      (hparsSat _ hsatP) (by rw [hids]; exact (trivial : True))
    rw [hparsLen, List.append_nil] at hv
    rw [← hv, hframe]
    rfl
  rw [hF]
  match fs with
  | [] => exact Iff.rfl
  | [_] => exact ⟨fun h => h.2.elim, fun h => h.2.elim⟩
  | h :: t :: [] =>
    show (h ∈ˢ interp V ρ _ ∧ t ∈ˢ interp V (cons h ρ) _ ∧ True) ↔
      (h ∈ˢ interp V (D.frame ψL (consList [x] ρ0) X) (.bvar 1) ∧
        t ∈ˢ interp V (cons h (D.frame ψL (consList [x] ρ0) X)) (.app (.bvar 1) (.bvar 2)) ∧ True)
    rw [htailC, htailH, hx, interp_bvar, hframe]
    exact Iff.rfl
  | _ :: _ :: _ :: _ => exact ⟨fun h => h.2.2.elim, fun h => h.2.2.elim⟩

end R23

#print axioms R23.listCons_fieldSeg

/-! Sanity: `hF` is what the uniform install's `absField` produces for
`List.cons` (`nP = 1`, `k = 1`): the head is the ordinary field `α`
(`.bvar 0` at the canonical frame, lifted over the one hole), the tail
the finitary recursive field — the hole `.bvar (1 + 0 + (1 - 1 - 0))`
applied to `paramBvarsAt 1 (1 + 1 + 1 + 0)` and no index readings. -/
example : (AnnotTerm.bvar 0).liftN 1 0 = .bvar 1 := rfl
example : AnnotTerm.mkAppN (.bvar (1 + 0 + (1 - 1 - 0))) (paramBvarsAt 1 (1 + 1 + 1 + 0) ++ [])
    = .app (.bvar 1) (.bvar 2) := rfl
