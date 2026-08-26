import Setlec.Kernel.Checker

/-!
# `V`-free readings of the environment's guards (task #123)

The literal-support guards `natLitSupported` / `strLitSupported` are
`Bool`s the kernel computes from the environment; their inversion
(`_inv`) and their read-set (`_congr`) are facts about `Env.find?`
alone.  `EtaFamilyStored` is the kind- and arity-pinned premise under
which an eta capability is owed — again a statement about what the
environment stores.

All four inversions and the premise were written in
`Setlec/Model/Interp.lean`, under that module's `variable (V) [SetTheory
V]`, but none of them mentions a valuation.  Relocated verbatim so the
declarative type-theory bridge can consume them instead of restating
them (task #123, `Setlec/TTVerify/DESIGN.md` §14.1).
-/

set_option linter.unusedVariables false
set_option linter.defProp false

namespace Setlec

/-- The eta family of an eta-capable stored structure is complete: the
capability record's constructor is stored as a constructor at exactly
the record's arities, and every documented projection function is
stored as a (degenerate) recursor.  This is the *premise* under which
`CapsOk` owes the eta law: mid-block — the former is installed first,
its constructor and projection functions after it — the premise fails
and the law is not yet owed; the family-completing member's install
discharges it.  The premises are deliberately **kind- and
arity-pinned**: an installation of a non-constructor under the
constructor's name (or a non-recursor under a projection name) never
completes the family, which is what keeps the `CapsOk.cons` head
obligations dischargeable at every install site. -/
def EtaFamilyStored (env : Env) (T : Name) (caps : IndCaps) : Prop :=
  -- name-only conjunct (static in `caps`): a reserved-named capability
  -- constructor never completes a family, which keeps the basis
  -- installs' head obligations vacuous by computation
  reservedBasisNames.contains caps.etaCtor = false ∧
  (∃ cvC, env.find? caps.etaCtor =
    some (.ctorInfo cvC caps.etaParams caps.etaFields)) ∧
  ∀ j, j < caps.etaFields → ∃ cv mI rP rules,
    env.find? (projFnName T j) = some (.recInfo cv mI rP rules)

/-- Everything `natLitSupported` checked, as separate facts. -/
theorem natLitSupported_inv {env : Env} (hs : natLitSupported env = true) :
    ∃ cv caps cv0 i0 j0 cv1 i1 j1,
      env.find? natName = some (.indInfo cv caps) ∧
      env.find? natZeroName = some (.ctorInfo cv0 i0 j0) ∧
      env.find? natSuccName = some (.ctorInfo cv1 i1 j1) ∧
      cv.levelParams = [] ∧ cv0.levelParams = [] ∧ cv1.levelParams = [] ∧
      cv.type = .sort (.succ .zero) ∧ cv0.type = .const natName [] ∧
      ∃ nm mb, cv1.type = .forallE nm (.const natName []) (.const natName []) mb := by
  unfold natLitSupported at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨hi, hz⟩, hsc⟩ := hs
  unfold natIndOk at hi
  split at hi
  case h_2 => simp at hi
  next cv caps heqN =>
    unfold natZeroOk at hz
    split at hz
    case h_2 => simp at hz
    next cv0 i0 j0 heqZ =>
      unfold natSuccOk at hsc
      split at hsc
      case h_2 => simp at hsc
      next cv1 i1 j1 heqS =>
        simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hi hz hsc
        refine ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, heqN, heqZ, heqS,
          hi.1, hz.1, hsc.1, hi.2, hz.2, ?_⟩
        obtain ⟨-, h6⟩ := hsc
        revert h6
        split
        case h_2 => intro h; simp at h
        next nm c1 c2 mb heq =>
          intro h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          exact ⟨nm, mb, by rw [heq, h.1, h.2]⟩

/-- The literal guard only reads the three `Nat` slots. -/
theorem natLitSupported_congr {env₁ env₂ : Env}
    (h1 : env₁.find? natName = env₂.find? natName)
    (h2 : env₁.find? natZeroName = env₂.find? natZeroName)
    (h3 : env₁.find? natSuccName = env₂.find? natSuccName) :
    natLitSupported env₁ = natLitSupported env₂ := by
  unfold natLitSupported
  rw [h1, h2, h3]

/-- Everything `strLitSupported` checked beyond `natLitSupported`, as
separate facts (level-parameter lists and exact annotated types of the
seven string-support constants). -/
theorem strLitSupported_inv {env : Env} (hs : strLitSupported env = true) :
    natLitSupported env = true ∧
    ∃ ciS ciO ciL ciN ciC ciH ciF pL pN pC,
      env.find? stringName = some ciS ∧
      env.find? stringOfListName = some ciO ∧
      env.find? listName = some ciL ∧
      env.find? listNilName = some ciN ∧
      env.find? listConsName = some ciC ∧
      env.find? charName = some ciH ∧
      env.find? charOfNatName = some ciF ∧
      ciS.toConstantVal.levelParams = [] ∧
      ciO.toConstantVal.levelParams = [] ∧
      ciL.toConstantVal.levelParams = [pL] ∧
      ciN.toConstantVal.levelParams = [pN] ∧
      ciC.toConstantVal.levelParams = [pC] ∧
      ciH.toConstantVal.levelParams = [] ∧
      ciF.toConstantVal.levelParams = [] ∧
      ciS.toConstantVal.type = .sort (.succ .zero) ∧
      ciH.toConstantVal.type = .sort (.succ .zero) ∧
      (∃ nm mb, ciO.toConstantVal.type =
        .forallE nm (.app (.const listName [.zero]) (.const charName []))
          (.const stringName []) mb) ∧
      (∃ nm mb, ciL.toConstantVal.type =
        .forallE nm (.sort (.succ (.param pL))) (.sort (.succ (.param pL))) mb) ∧
      (∃ nm mb, ciN.toConstantVal.type =
        .forallE nm (.sort (.succ (.param pN)))
          (.app (.const listName [.param pN]) (.bvar 0)) mb) ∧
      (∃ nm1 nm2 nm3 mb1 mb2 mb3, ciC.toConstantVal.type =
        .forallE nm1 (.sort (.succ (.param pC)))
          (.forallE nm2 (.bvar 0)
            (.forallE nm3 (.app (.const listName [.param pC]) (.bvar 1))
              (.app (.const listName [.param pC]) (.bvar 2)) mb3) mb2) mb1) ∧
      (∃ nm mb, ciF.toConstantVal.type =
        .forallE nm (.const natName []) (.const charName []) mb) := by
  unfold strLitSupported at hs
  simp only [Bool.and_eq_true] at hs
  obtain ⟨⟨⟨⟨⟨⟨⟨hnat, hS⟩, hO⟩, hL⟩, hN⟩, hC⟩, hH⟩, hF⟩ := hs
  refine ⟨hnat, ?_⟩
  unfold stringTyOk at hS
  unfold stringOfListTyOk at hO
  unfold listTyOk at hL
  unfold listNilTyOk at hN
  unfold listConsTyOk at hC
  unfold charTyOk at hH
  unfold charOfNatTyOk at hF
  split at hS; case h_2 => simp at hS
  next ciS heqS =>
  split at hO; case h_2 => simp at hO
  next ciO heqO =>
  split at hL; case h_2 => simp at hL
  next ciL heqL =>
  split at hN; case h_2 => simp at hN
  next ciN heqN =>
  split at hC; case h_2 => simp at hC
  next ciC heqC =>
  split at hH; case h_2 => simp at hH
  next ciH heqH =>
  split at hF; case h_2 => simp at hF
  next ciF heqF =>
  simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at hS hH
  -- List: one level parameter, pinned type
  revert hL
  split; case h_2 => intro h; exact nomatch h
  next pL heqPL =>
  split
  case h_2 => intro h; simp at h
  next nmL u1L u2L mbL heqTL =>
  intro hL
  simp only [Bool.and_eq_true, beq_iff_eq] at hL
  -- List.nil
  revert hN
  split; case h_2 => intro h; exact nomatch h
  next pN heqPN =>
  split
  case h_2 => intro h; simp at h
  next nmN u1N l1N us1N mbN heqTN =>
  intro hN
  simp only [Bool.and_eq_true, beq_iff_eq] at hN
  -- List.cons
  revert hC
  split; case h_2 => intro h; exact nomatch h
  next pC heqPC =>
  split
  case h_2 => intro h; simp at h
  next nmC1 u1C nmC2 nmC3 l1C us1C l2C us2C mb3C mb2C mb1C heqTC =>
  intro hC
  simp only [Bool.and_eq_true, beq_iff_eq] at hC
  -- Char.ofNat
  revert hF
  simp only [Bool.and_eq_true, List.isEmpty_iff]
  rintro ⟨hF1, hF2⟩
  revert hF2
  split
  case h_2 => intro h; simp at h
  next nmF c1F c2F mbF heqTF =>
  intro hF2
  simp only [Bool.and_eq_true, beq_iff_eq] at hF2
  -- String.ofList
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hO
  obtain ⟨hO1, hO2⟩ := hO
  revert hO2
  split
  case h_2 => intro h; simp at h
  next nmO l1O us1O c1O c2O mbO heqTO =>
  intro hO2
  simp only [Bool.and_eq_true, beq_iff_eq] at hO2
  refine ⟨ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC,
    heqS, heqO, heqL, heqN, heqC, heqH, heqF,
    hS.1, hO1, heqPL, heqPN, heqPC, hH.1, hF1, hS.2, hH.2, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨nmO, mbO, by
      rw [heqTO, hO2.1.1.1, hO2.1.1.2, hO2.1.2, hO2.2]⟩
  · exact ⟨nmL, mbL, by rw [heqTL, hL.1, hL.2]⟩
  · exact ⟨nmN, mbN, by rw [heqTN, hN.1.1, hN.1.2, hN.2]⟩
  · exact ⟨nmC1, nmC2, nmC3, mb1C, mb2C, mb3C, by
      rw [heqTC, hC.1.1.1.1, hC.1.1.1.2, hC.1.1.2, hC.1.2, hC.2]⟩
  · exact ⟨nmF, mbF, by rw [heqTF, hF2.1, hF2.2]⟩

/-- The string-literal guard only reads the pinned slots
(`strLitNames`). -/
theorem strLitSupported_congr {env₁ env₂ : Env}
    (hNat : env₁.find? natName = env₂.find? natName)
    (hZero : env₁.find? natZeroName = env₂.find? natZeroName)
    (hSucc : env₁.find? natSuccName = env₂.find? natSuccName)
    (hS : env₁.find? stringName = env₂.find? stringName)
    (hO : env₁.find? stringOfListName = env₂.find? stringOfListName)
    (hL : env₁.find? listName = env₂.find? listName)
    (hN : env₁.find? listNilName = env₂.find? listNilName)
    (hC : env₁.find? listConsName = env₂.find? listConsName)
    (hH : env₁.find? charName = env₂.find? charName)
    (hF : env₁.find? charOfNatName = env₂.find? charOfNatName) :
    strLitSupported env₁ = strLitSupported env₂ := by
  unfold strLitSupported
  rw [natLitSupported_congr hNat hZero hSucc, hS, hO, hL, hN, hC, hH, hF]

end Setlec
