module

public import ConLeche.Verify.EnvWF
import ConLeche.Kernel.Checker

public section

/-!
# `V`-free readings of the environment's guards

The literal-support guards `natLitSupported` / `strLitSupported` are
`Bool`s the kernel computes from the environment; their inversion
(`_inv`) and their read-set (`_congr`) are facts about `Env.find?`
alone.

None of them mentions a valuation, so every consumer takes them from
here: this module and `ConLeche/Verify/EnvPreds.lean` are the single
home of the environment's `V`-free readings.
-/

set_option linter.unusedVariables false
set_option linter.defProp false

namespace ConLeche

/-- **A literal's constants stored are at their shapes**: what the declarations' own check says,
at the kinds the `Nat` names hold. -/
theorem natLitSupported_of_shapes {env : Env}
    (hsh : ∀ n c, env.find? n = some c → litShapeOk c = true) (hk : NatKinds env)
    (h : natLitStored env = true) :
    natLitSupported env = true := by
  simp only [natLitStored, Bool.and_eq_true, Option.isSome_iff_exists] at h
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨c, hc⟩⟩ := h
  have sa := hsh _ _ ha
  have sb := hsh _ _ hb
  have sc := hsh _ _ hc
  simp (decide := true) only [litShapeOk, Env.find?_name ha, ↓reduceIte] at sa
  simp (decide := true) only [litShapeOk, Env.find?_name hb, ↓reduceIte] at sb
  simp (decide := true) only [litShapeOk, Env.find?_name hc, ↓reduceIte] at sc
  obtain ⟨cva, capsa, rfl⟩ := hk.1 _ ha
  obtain ⟨cvb, nPb, nFb, Tb, rfl⟩ := hk.2.1 _ hb
  obtain ⟨cvc, nPc, nFc, Tc, rfl⟩ := hk.2.2 _ hc
  simp only [natLitSupported, ha, hb, hc]
  exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨sa, sb⟩, sc⟩

theorem strLitSupported_of_shapes {env : Env}
    (hsh : ∀ n c, env.find? n = some c → litShapeOk c = true) (hk : NatKinds env)
    (h : strLitStored env = true) :
    strLitSupported env = true := by
  simp only [strLitStored, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hn, h₁⟩, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩ := h
  have hnat := natLitSupported_of_shapes hsh hk hn
  have hs : ∀ {n : Name}, (env.find? n).isSome = true →
      ∃ c, env.find? n = some c ∧ litShapeOk c = true ∧ c.name = n := fun hsome => by
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨c, hc, hsh _ _ hc, Env.find?_name hc⟩
  obtain ⟨c₁, f₁, s₁, n₁⟩ := hs h₁
  obtain ⟨c₂, f₂, s₂, n₂⟩ := hs h₂
  obtain ⟨c₃, f₃, s₃, n₃⟩ := hs h₃
  obtain ⟨c₄, f₄, s₄, n₄⟩ := hs h₄
  obtain ⟨c₅, f₅, s₅, n₅⟩ := hs h₅
  obtain ⟨c₆, f₆, s₆, n₆⟩ := hs h₆
  obtain ⟨c₇, f₇, s₇, n₇⟩ := hs h₇
  simp (decide := true) only [litShapeOk, n₁, ↓reduceIte] at s₁
  simp (decide := true) only [litShapeOk, n₂, ↓reduceIte] at s₂
  simp (decide := true) only [litShapeOk, n₃, ↓reduceIte] at s₃
  simp (decide := true) only [litShapeOk, n₄, ↓reduceIte] at s₄
  simp (decide := true) only [litShapeOk, n₅, ↓reduceIte] at s₅
  simp (decide := true) only [litShapeOk, n₆, ↓reduceIte] at s₆
  simp (decide := true) only [litShapeOk, n₇, ↓reduceIte] at s₇
  simp only [strLitSupported, hnat, f₁, f₂, f₃, f₄, f₅, f₆, f₇, s₁, s₂, s₃, s₄, s₅, s₆, s₇,
    Bool.and_self]

theorem natLitSupported_of_stored {env : Env} (henv : EnvWF env) (hk : NatKinds env)
    (h : natLitStored env = true) : natLitSupported env = true :=
  natLitSupported_of_shapes (fun _ _ hc => henv.shapes _ (Env.find?_mem hc)) hk h

theorem strLitSupported_of_stored {env : Env} (henv : EnvWF env) (hk : NatKinds env)
    (h : strLitStored env = true) : strLitSupported env = true :=
  strLitSupported_of_shapes (fun _ _ hc => henv.shapes _ (Env.find?_mem hc)) hk h

/-- Everything `natLitSupported` checked, as separate facts. -/
theorem natLitSupported_inv {env : Env} (hs : natLitSupported env = true) :
    ∃ cv caps cv0 i0 j0 T0 cv1 i1 j1 T1,
      env.find? natName = some (.indInfo cv caps) ∧
      env.find? natZeroName = some (.ctorInfo cv0 i0 j0 T0) ∧
      env.find? natSuccName = some (.ctorInfo cv1 i1 j1 T1) ∧
      cv.levelParams = [] ∧ cv0.levelParams = [] ∧ cv1.levelParams = [] ∧
      cv.type = .sort (.succ .zero) ∧ cv0.type = .const natName [] ∧
      cv1.type = .forallE (.const natName []) (.const natName []) := by
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
    next cv0 i0 j0 T0 heqZ =>
      unfold natSuccOk at hsc
      split at hsc
      case h_2 => simp at hsc
      next cv1 i1 j1 T1 heqS =>
        simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at hi hz hsc
        refine ⟨cv, caps, cv0, i0, j0, T0, cv1, i1, j1, T1, heqN, heqZ, heqS,
          hi.1, hz.1, hsc.1, hi.2, hz.2, ?_⟩
        obtain ⟨-, h6⟩ := hsc
        revert h6
        split
        case h_2 => intro h; simp at h
        next c1 c2 heq =>
          intro h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          rw [heq, h.1, h.2]

/-- Everything `strLitSupported` checked beyond `natLitSupported`, as
separate facts (level-parameter lists and exact stored types of the
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
      ciO.toConstantVal.type =
        .forallE (.app (.const listName [.zero]) (.const charName []))
          (.const stringName []) ∧
      ciL.toConstantVal.type =
        .forallE (.sort (.succ (.param pL))) (.sort (.succ (.param pL))) ∧
      ciN.toConstantVal.type =
        .forallE (.sort (.succ (.param pN)))
          (.app (.const listName [.param pN]) (.bvar 0)) ∧
      ciC.toConstantVal.type =
        .forallE (.sort (.succ (.param pC)))
          (.forallE (.bvar 0)
            (.forallE (.app (.const listName [.param pC]) (.bvar 1))
              (.app (.const listName [.param pC]) (.bvar 2)))) ∧
      ciF.toConstantVal.type =
        .forallE (.const natName []) (.const charName []) := by
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
  next nmL u1L u2L heqTL =>
  intro hL
  simp only [Bool.and_eq_true, beq_iff_eq] at hL
  -- List.nil
  revert hN
  split; case h_2 => intro h; exact nomatch h
  next pN heqPN =>
  split
  case h_2 => intro h; simp at h
  next nmN u1N l1N us1N heqTN =>
  intro hN
  simp only [Bool.and_eq_true, beq_iff_eq] at hN
  -- List.cons
  revert hC
  split; case h_2 => intro h; exact nomatch h
  next pC heqPC =>
  split
  case h_2 => intro h; simp at h
  next nmC1 u1C nmC2 nmC3 l1C us1C l2C us2C heqTC =>
  intro hC
  simp only [Bool.and_eq_true, beq_iff_eq] at hC
  -- Char.ofNat
  revert hF
  simp only [Bool.and_eq_true, List.isEmpty_iff]
  rintro ⟨hF1, hF2⟩
  revert hF2
  split
  case h_2 => intro h; simp at h
  next c1F c2F heqTF =>
  intro hF2
  simp only [Bool.and_eq_true, beq_iff_eq] at hF2
  -- String.ofList
  simp only [Bool.and_eq_true, List.isEmpty_iff] at hO
  obtain ⟨hO1, hO2⟩ := hO
  revert hO2
  split
  case h_2 => intro h; simp at h
  next l1O us1O c1O c2O heqTO =>
  intro hO2
  simp only [Bool.and_eq_true, beq_iff_eq] at hO2
  refine ⟨ciS, ciO, ciL, ciN, ciC, ciH, ciF, pL, pN, pC,
    heqS, heqO, heqL, heqN, heqC, heqH, heqF,
    hS.1, hO1, heqPL, heqPN, heqPC, hH.1, hF1, hS.2, hH.2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heqTO, hO2.1.1.1, hO2.1.1.2, hO2.1.2, hO2.2]
  · rw [heqTL, hL.1, hL.2]
  · rw [heqTN, hN.1.1, hN.1.2, hN.2]
  · rw [heqTC, hC.1.1.1.1, hC.1.1.1.2, hC.1.1.2, hC.1.2, hC.2]
  · rw [heqTF, hF2.1, hF2.2]

/-! ## The guard, inverted -/

/-- Everything `natOpGuard` checked, as separate facts. -/
theorem natOpGuard_inv {c : Name} (h : natOpGuard env c = true) :
    natLitSupported env = true ∧
    (∀ n ∈ natOpDeps c, (env.find? n).isSome = true) ∧
    ((c = natBeqName ∨ c = natBleName ∨ c ∈ natDivModNames) →
      (∃ ciT, env.find? boolTrueName = some ciT ∧
        ciT.toConstantVal.levelParams = []) ∧
      (∃ ciF, env.find? boolFalseName = some ciF ∧
        ciF.toConstantVal.levelParams = [])) := by
  unfold natOpGuard at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hs, hdeps⟩, hbool⟩ := h
  refine ⟨hs, fun n hn => List.all_eq_true.mp hdeps n hn, ?_⟩
  · intro hc
    have hcb : (c = natBeqName || c = natBleName ||
        natDivModNames.contains c) = true := by
      rcases hc with rfl | rfl | hm
      · simp
      · simp
      · rw [List.contains_iff_mem.mpr hm, Bool.or_true]
    rw [ite_eq_left hcb] at hbool
    simp only [Bool.and_eq_true] at hbool
    obtain ⟨hT, hF⟩ := hbool
    constructor
    · revert hT
      split
      · next ciT heq =>
        intro hlp
        simp only [Bool.and_eq_true] at hlp
        exact ⟨ciT, heq, List.isEmpty_iff.mp (by simpa using hlp.1)⟩
      · intro hh; exact nomatch hh
    · revert hF
      split
      · next ciF heq =>
        intro hlp
        simp only [Bool.and_eq_true] at hlp
        exact ⟨ciF, heq, List.isEmpty_iff.mp (by simpa using hlp.1)⟩
      · intro hh; exact nomatch hh


/-- The guard's `Bool` constructors sit at the type `Bool` itself
(task #342 L8: the comparison recurrences relate two members of one
type). -/
theorem natOpGuard_boolTy {c : Name} (h : natOpGuard env c = true)
    (hc : c = natBeqName ∨ c = natBleName ∨ c ∈ natDivModNames) :
    (∃ ciT, env.find? boolTrueName = some ciT ∧
      ciT.toConstantVal.type = .const boolName []) ∧
    (∃ ciF, env.find? boolFalseName = some ciF ∧
      ciF.toConstantVal.type = .const boolName []) := by
  unfold natOpGuard at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨-, hbool⟩ := h
  have hcb : (c = natBeqName || c = natBleName ||
      natDivModNames.contains c) = true := by
    rcases hc with rfl | rfl | hm
    · simp
    · simp
    · rw [List.contains_iff_mem.mpr hm, Bool.or_true]
  rw [ite_eq_left hcb] at hbool
  simp only [Bool.and_eq_true] at hbool
  obtain ⟨hT, hF⟩ := hbool
  constructor
  · revert hT
    split
    · next ciT heq =>
      intro hlp
      simp only [Bool.and_eq_true, beq_iff_eq] at hlp
      exact ⟨ciT, heq, hlp.2⟩
    · intro hh; exact nomatch hh
  · revert hF
    split
    · next ciF heq =>
      intro hlp
      simp only [Bool.and_eq_true, beq_iff_eq] at hlp
      exact ⟨ciF, heq, hlp.2⟩
    · intro hh; exact nomatch hh

/-! ## A stored operation's pin, unpacked

The install checks of a certified operation pin its own stored type
(`natOpStoredOk`, a definition's); its dependencies are only required
stored (`natOpGuard`).  The model's laws carry the pin for every
dependency, of whatever kind the dependency is stored as
(`natOpPinnedOk`), in the form `(natOpDeps c).all (natOpPinnedOk env)`,
and every clause of the literal bridges reads it through the inversions
below. -/

/-- Op `n` is stored, of any kind, level-monomorphically at its pinned
type: what the literal fast path needs of a name it fires on.  The fast
path fires by name, so the model reads the pin off the stored name and
not off its kind (a context may present an operation as an axiom). -/
@[expose] def natOpPinnedOk (env : Env) (n : Name) : Bool :=
  match env.find? n with
  | some ci => ci.toConstantVal.levelParams.isEmpty &&
      natOpTyPinned env n ci.toConstantVal.type
  | none => false

/-- `natOpStoredOk`, inverted. -/
theorem natOpStoredOk_inv {env : Env} {n : Name}
    (h : natOpStoredOk env n = true) :
    ∃ cv v hh, env.find? n = some (.defnInfo cv v hh) ∧
      cv.levelParams = [] ∧ natOpTyPinned env n cv.type = true := by
  unfold natOpStoredOk at h
  revert h
  split
  · next cv v hh heq =>
    intro h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨cv, v, hh, heq, h.1, h.2⟩
  · intro h; exact nomatch h

/-- `natOpPinnedOk`, inverted. -/
theorem natOpPinnedOk_inv {env : Env} {n : Name}
    (h : natOpPinnedOk env n = true) :
    ∃ ci, env.find? n = some ci ∧ ci.toConstantVal.levelParams = [] ∧
      natOpTyPinned env n ci.toConstantVal.type = true := by
  unfold natOpPinnedOk at h
  revert h
  split
  · next ci heq =>
    intro h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨ci, heq, h.1, h.2⟩
  · intro h; exact nomatch h

/-- `natOpPinnedOk` from its parts. -/
theorem natOpPinnedOk_of {env : Env} {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) (hl : ci.toConstantVal.levelParams = [])
    (hp : natOpTyPinned env n ci.toConstantVal.type = true) :
    natOpPinnedOk env n = true := by
  unfold natOpPinnedOk
  rw [hf]
  simp only [hl, List.isEmpty_nil, Bool.true_and]
  exact hp

/-- A definition's pin is a pin. -/
theorem natOpPinnedOk_of_storedOk {env : Env} {n : Name}
    (h : natOpStoredOk env n = true) : natOpPinnedOk env n = true :=
  let ⟨_, _, _, hf, hl, hp⟩ := natOpStoredOk_inv h
  natOpPinnedOk_of hf hl hp

/-- Every dependency pinned: each is stored with no level
parameters. -/
theorem natOpDepsOk_inv {env : Env} {c : Name}
    (h : (natOpDeps c).all (natOpPinnedOk env) = true) :
    ∀ n ∈ natOpDeps c, ∃ ci, env.find? n = some ci ∧
      ci.toConstantVal.levelParams = [] := fun n hn =>
  let ⟨ci, hf, hl, _⟩ := natOpPinnedOk_inv (List.all_eq_true.mp h n hn)
  ⟨ci, hf, hl⟩

/-- A name the install refuses as a certified operation's is none of
them: how the laws hold vacuously at a fresh cons that is not the
operation's own install. -/
theorem not_mem_natOpNames_of {n : Name} (h : natOpName n = false) :
    n ∉ natOpNames ∧ n ∉ natDivModNames := by
  simp only [natOpName, Bool.or_eq_false_iff] at h
  exact ⟨fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.1,
    fun hm => by rw [List.contains_iff_mem.mpr hm] at h; exact Bool.noConfusion h.2⟩

/-- A certified operation's dependencies are certified operations. -/
theorem natOpDeps_mem {c n : Name} (hc : c ∈ natOpNames ∨ c ∈ natDivModNames)
    (hn : n ∈ natOpDeps c) : n ∈ natOpNames ∨ n ∈ natDivModNames := by
  have h1 : ∀ c ∈ natOpNames, ∀ n ∈ natOpDeps c,
      n ∈ natOpNames ∨ n ∈ natDivModNames := by decide
  have h2 : ∀ c ∈ natDivModNames, ∀ n ∈ natOpDeps c,
      n ∈ natOpNames ∨ n ∈ natDivModNames := by decide
  rcases hc with hc | hc
  · exact h1 c hc n hn
  · exact h2 c hc n hn

/-- Every guarded operation is among its own dependencies. -/
theorem mem_natOpDeps_self {c : Name} (h : c ∈ natOpNames ∨ c ∈ natDivModNames) :
    c ∈ natOpDeps c := by
  have h1 : ∀ c ∈ natOpNames, c ∈ natOpDeps c := by decide
  have h2 : ∀ c ∈ natDivModNames, c ∈ natOpDeps c := by decide
  rcases h with h | h
  · exact h1 c h
  · exact h2 c h

/-- A stored operation whose dependencies are pinned has its pinned
type. -/
theorem natOpTyPinned_of_deps {env : Env} {c : Name} {ci : ConstantInfo}
    (hc : c ∈ natOpNames ∨ c ∈ natDivModNames)
    (hdeps : (natOpDeps c).all (natOpPinnedOk env) = true)
    (hf : env.find? c = some ci) :
    natOpTyPinned env c ci.toConstantVal.type = true := by
  obtain ⟨ci', hf', -, hpin⟩ :=
    natOpPinnedOk_inv (List.all_eq_true.mp hdeps c (mem_natOpDeps_self hc))
  rw [hf] at hf'
  obtain rfl := Option.some.inj hf'
  exact hpin

end ConLeche
