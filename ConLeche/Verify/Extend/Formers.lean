module

public import ConLeche.Verify.Extend.Recs
public import ConLeche.Kernel.Inductives.BlockTail

@[expose] public section

/-!
# Two environments alike but for formers' stored types

A def-headed block's job reads the group and its containers at their reduced telescopes, and
the block is stored at what the group declares (`checkBlock`'s second path).  The environments
on the two sides answer every lookup alike, but for a former's type: `FormerSwap`.  `denote` and
the literal guards read an environment only through what a swap keeps, the guards' own families
being no swap's (`litGuardFamilies`).
-/

namespace ConLeche

/-- **`env₃` is `env₀` but for formers' stored types.** -/
structure FormerSwap (env₀ env₃ : Env) : Prop where
  find : ∀ n, env₃.find? n = env₀.find? n ∨
    ∃ cv cv' caps, env₀.find? n = some (.indInfo cv caps) ∧ env₃.find? n = some (.indInfo cv' caps) ∧
      cv'.name = cv.name ∧ cv'.levelParams = cv.levelParams ∧
      litGuardFamilies.contains n = false
  mem : ∀ c ∈ env₃.consts, (∀ cv caps, c ≠ .indInfo cv caps) → c ∈ env₀.consts
  tables : env₃.tables = env₀.tables

namespace FormerSwap

variable {env₀ env₃ : Env}

theorem symm_find (h : FormerSwap env₀ env₃) (n : Name) : env₀.find? n = env₃.find? n ∨
    ∃ cv cv' caps, env₃.find? n = some (.indInfo cv caps) ∧ env₀.find? n = some (.indInfo cv' caps) ∧
      cv'.name = cv.name ∧ cv'.levelParams = cv.levelParams ∧
      litGuardFamilies.contains n = false := by
  rcases h.find n with he | ⟨cv, cv', caps, h₀, h₃, hn, hl, hg⟩
  · exact .inl he.symm
  · exact .inr ⟨cv', cv, caps, h₃, h₀, hn.symm, hl.symm, hg⟩

/-- A lookup other than a former's is the same on both sides. -/
theorem find_of_ne (h : FormerSwap env₀ env₃) {n : Name} {ci : ConstantInfo}
    (hci : ∀ cv caps, ci ≠ .indInfo cv caps) :
    env₃.find? n = some ci ↔ env₀.find? n = some ci := by
  rcases h.find n with he | ⟨cv, cv', caps, h₀, h₃, -⟩
  · rw [he]
  · rw [h₀, h₃]
    constructor
    · intro hx; exact absurd (Option.some.inj hx).symm (hci _ _)
    · intro hx; exact absurd (Option.some.inj hx).symm (hci _ _)

/-- A former stays a former, at its capabilities and level parameters. -/
theorem find_ind (h : FormerSwap env₀ env₃) {n : Name} {cv : ConstantVal} {caps : IndCaps}
    (hf : env₀.find? n = some (.indInfo cv caps)) :
    ∃ cv', env₃.find? n = some (.indInfo cv' caps) ∧ cv'.levelParams = cv.levelParams := by
  rcases h.find n with he | ⟨c₀, c₃, caps', h₀, h₃, -, hl, -⟩
  · exact ⟨cv, by rw [he]; exact hf, rfl⟩
  · rw [hf] at h₀
    obtain ⟨rfl, rfl⟩ : cv = c₀ ∧ caps = caps' := by simpa using h₀
    exact ⟨c₃, h₃, hl⟩

theorem find_ind_back (h : FormerSwap env₀ env₃) {n : Name} {cv : ConstantVal} {caps : IndCaps}
    (hf : env₃.find? n = some (.indInfo cv caps)) :
    ∃ cv', env₀.find? n = some (.indInfo cv' caps) ∧ cv.levelParams = cv'.levelParams := by
  rcases h.find n with he | ⟨c₀, c₃, caps', h₀, h₃, -, hl, -⟩
  · exact ⟨cv, by rw [← he]; exact hf, rfl⟩
  · rw [hf] at h₃
    obtain ⟨rfl, rfl⟩ : cv = c₃ ∧ caps = caps' := by simpa using h₃
    exact ⟨c₀, h₀, hl⟩

/-- A name the guards read is untouched. -/
theorem find_guard (h : FormerSwap env₀ env₃) {n : Name} (hn : litGuardFamilies.contains n = true) :
    env₃.find? n = env₀.find? n := by
  rcases h.find n with he | ⟨-, -, -, -, -, -, -, hg⟩
  · exact he
  · rw [hn] at hg; exact nomatch hg

/-- A reserved name is untouched. -/
theorem find_reserved (h : FormerSwap env₀ env₃) {n : Name}
    (hn : reservedBasisNames.contains n = true) : env₃.find? n = env₀.find? n :=
  h.find_guard (by
    rw [litGuardFamilies, List.contains_append, hn, Bool.or_true])

theorem levelsEq (h : FormerSwap env₀ env₃) (n : Name) :
    (env₀.find? n).map (fun ci => ci.toConstantVal.levelParams)
      = (env₃.find? n).map (fun ci => ci.toConstantVal.levelParams) := by
  rcases h.find n with he | ⟨cv, cv', caps, h₀, h₃, -, hl, -⟩
  · rw [he]
  · rw [h₀, h₃]; simp [ConstantInfo.toConstantVal, hl]

theorem isSomeEq (h : FormerSwap env₀ env₃) (n : Name) :
    (env₀.find? n).isSome = (env₃.find? n).isSome := by
  rcases h.find n with he | ⟨cv, cv', caps, h₀, h₃, -⟩
  · rw [he]
  · rw [h₀, h₃]; rfl

theorem natEq (h : FormerSwap env₀ env₃) : natLitSupported env₀ = natLitSupported env₃ := by
  unfold natLitSupported
  rw [h.find_guard (n := natName) (by decide), h.find_guard (n := natZeroName) (by decide),
    h.find_guard (n := natSuccName) (by decide)]

theorem strEq (h : FormerSwap env₀ env₃) : strLitSupported env₀ = strLitSupported env₃ := by
  unfold strLitSupported
  rw [h.natEq, h.find_guard (n := stringName) (by decide),
    h.find_guard (n := stringOfListName) (by decide), h.find_guard (n := listName) (by decide),
    h.find_guard (n := listNilName) (by decide), h.find_guard (n := listConsName) (by decide),
    h.find_guard (n := charName) (by decide), h.find_guard (n := charOfNatName) (by decide)]

theorem tableEq (h : FormerSwap env₀ env₃) (T : Name) : env₀.findTable? T = env₃.findTable? T := by
  unfold Env.findTable?
  rw [h.isSomeEq, h.tables]

theorem projEq (h : FormerSwap env₀ env₃) (T : Name) (i : Nat) :
    env₀.findProj? T i = env₃.findProj? T i := by
  unfold Env.findProj?
  rw [h.tableEq]

/-- A definition's lookup, whichever other kind a former's swap leaves. -/
theorem defn_match {α : Type} (h : FormerSwap env₀ env₃) (n : Name)
    (f : ConstantVal → Expr → ReducibilityHint → α) (d : α) :
    (match env₃.find? n with
      | some (.defnInfo cv v hh) => f cv v hh
      | _ => d) =
    (match env₀.find? n with
      | some (.defnInfo cv v hh) => f cv v hh
      | _ => d) := by
  rcases h.find n with he | ⟨cv, cv', caps, h₀, h₃, -⟩
  · rw [he]
  · rw [h₀, h₃]

theorem guardEq (h : FormerSwap env₀ env₃) (c : Name) :
    natOpGuard env₀ c = natOpGuard env₃ c := by
  unfold natOpGuard
  rw [h.natEq, h.find_guard (n := boolTrueName) (by decide),
    h.find_guard (n := boolFalseName) (by decide)]
  congr 2
  exact congrArg _ (funext fun n => (h.defn_match n (fun cv _ _ => cv.levelParams.isEmpty) false).symm)

end FormerSwap

end ConLeche
