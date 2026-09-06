import Setlec.Verify.Direct.DirectInv
import Setlec.Verify.FastOps

/-!
# The direct recogniser and the projection slots, inverted (task #175 W4c, P3 module 7, part 7)

V-free facts the direct install's assembly reads off the kernel's
recogniser and slot decision:

* `directParts?_inv`: the block's shape facts the recogniser pins —
  the propositionality datum is the result sort's, the recursor is
  `T.rec` at the block's level parameters (plus the large eliminator's
  fresh one), the constructor carries the former's;
* `directProjGuards_getD`: the coarse guard's spelling at a slot.
  (Task #175 S1: the per-slot run and the slot-prefix lemmas went with
  the per-field entries — the table stage is one cons,
  `checkDirectProjTable_inv`.)
-/

namespace Setlec

/-! ## The recogniser -/

theorem directPartsCore?_inv {block : List ConstantInfo} {p : DirectParts}
    (h : directPartsCore? block = some p) :
    p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
    p.cvR.name = p.cvT.name.str "rec" ∧
    p.cvC.levelParams = p.cvT.levelParams ∧
    reservedBasisNames.contains p.cvT.name = false ∧
    reservedBasisNames.contains p.cvC.name = false ∧
    reservedBasisNames.contains p.cvR.name = false ∧
    (p.large = true → p.elim ∈ p.cvR.levelParams) := by
  unfold directPartsCore? at h
  split at h
  · next cvT caps cvC nP nF cvR mI rP rule =>
    split at h
    · next fst mbody hstripL =>
      dsimp only at h
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        cases hstripP : Expr.stripPis nP cvT.type with
        | none => rw [hstripP] at h; exact nomatch h
        | some q =>
          obtain ⟨fstP, body⟩ := q
          rw [hstripP] at h
          cases body
          case sort s =>
            dsimp only at h
            split at h
            · next lq elim' hlarge =>
              obtain rfl := Option.some.inj h
              refine ⟨rfl, hc.1.1.1.1.1.1.1.1.1, hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2,
                hc.1.1.1.1.1.1.2, hc.1.1.1.1.1.2, fun _ => ?_⟩
              show elim' ∈ cvR.levelParams
              split at hlarge
              · next e relps hlp =>
                split at hlarge
                · obtain rfl := Option.some.inj hlarge
                  rw [hlp]
                  exact List.mem_cons_self
                · exact nomatch hlarge
              · exact nomatch hlarge
            · next lq hlarge =>
              split at h
              · obtain rfl := Option.some.inj h
                exact ⟨rfl, hc.1.1.1.1.1.1.1.1.1, hc.1.1.1.1.1.1.1.1.2, hc.1.1.1.1.1.1.1.2,
                  hc.1.1.1.1.1.1.2, hc.1.1.1.1.1.2, fun hl => nomatch hl⟩
              · exact nomatch h
          all_goals (dsimp only at h; exact nomatch h)
      · exact nomatch h
    · -- the rule body does not peel: the guard is false
      dsimp only at h
      simp at h
  · exact nomatch h

theorem directParts?_inv {env : Env} {block : List ConstantInfo} {p : DirectParts}
    (h : directParts? env block = some p) :
    p.isProp = (Level.isEquiv p.resSort .zero == some true) ∧
    p.cvR.name = p.cvT.name.str "rec" ∧
    p.cvC.levelParams = p.cvT.levelParams ∧
    reservedBasisNames.contains p.cvT.name = false ∧
    reservedBasisNames.contains p.cvC.name = false ∧
    reservedBasisNames.contains p.cvR.name = false ∧
    (p.large = true → p.elim ∈ p.cvR.levelParams) := by
  unfold directParts? at h
  cases hp : directPartsCore? block with
  | none => rw [hp] at h; exact nomatch h
  | some p' =>
    rw [hp] at h
    dsimp only at h
    by_cases hnr : directNonRec env p' = true
    · rw [if_pos hnr] at h
      obtain rfl := Option.some.inj h
      exact directPartsCore?_inv hp
    · rw [if_neg hnr] at h
      exact nomatch h

/-! ## The guard's spelling -/

theorem directProjGuards_getD (cty : Expr) (nP nF : Nat) (sorts : List Level) {i : Nat}
    (hi : i < nF) :
    (directProjGuards cty nP nF sorts).getD i .zero
      = (List.range i).foldl
          (fun acc j => if directUsedLater cty nP j then Level.max acc (sorts.getD j .zero)
            else acc)
          (sorts.getD i .zero) := by
  unfold directProjGuards
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

end Setlec
