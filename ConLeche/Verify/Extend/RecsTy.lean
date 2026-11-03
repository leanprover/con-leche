module

public import ConLeche.Verify.Extend.Recs

public section

/-!
# The stored recursors' swap: types and right-hand sides (task #431)

`SwapPairTy`/`SwapTyList`: a stored recursor replaced by one with the
same name, level parameters, major index and rule prefix, and any type
and rules — the step that installs the STORED recursors in place of the
generated ones (`storedRecsCheck`).  Like the rule-list swap
(`SwapShList`, `Recs.lean`) it changes no stored name, no level
parameter and no kind, so it induces the same environment congruences
(`SwapTyList.congr`): `denote` and the guards read the environment only
through those.
-/

namespace ConLeche

/-- The type-and-rules swap pair. -/
@[expose] def SwapPairTy (c₀ c₃ : ConstantInfo) : Prop :=
  c₀ = c₃ ∨
  ∃ cv cv' mI rP rules rules',
    c₀ = .recInfo cv mI rP rules ∧ c₃ = .recInfo cv' mI rP rules' ∧
    cv'.name = cv.name ∧ cv'.levelParams = cv.levelParams ∧ reservedRecName cv.name = false

/-- Pointwise type-and-rules swap of two constant lists. -/
inductive SwapTyList : List ConstantInfo → List ConstantInfo → Prop
  | nil : SwapTyList [] []
  | cons {c₀ c₃ : ConstantInfo} {rest₀ rest₃ : List ConstantInfo} :
      SwapPairTy c₀ c₃ → SwapTyList rest₀ rest₃ →
      SwapTyList (c₀ :: rest₀) (c₃ :: rest₃)

theorem SwapTyList.of_eq : ∀ (l : List ConstantInfo), SwapTyList l l
  | [] => SwapTyList.nil
  | _c :: l => SwapTyList.cons (Or.inl rfl) (SwapTyList.of_eq l)

theorem SwapPairTy.name_eq {c₀ c₃ : ConstantInfo} (h : SwapPairTy c₀ c₃) :
    c₀.name = c₃.name := by
  rcases h with rfl | ⟨cv, cv', mI, rP, rules, rules', rfl, rfl, hn, -, -⟩
  · rfl
  · exact hn.symm

/-- The lookup correspondence of a type-and-rules swap. -/
theorem swapTy_find?_corr {ts : List ProjTable} :
    ∀ {consts₀ consts₃ : List ConstantInfo},
    SwapTyList consts₀ consts₃ →
    ∀ n : Name,
    (Env.mk consts₃ ts).find? n = (Env.mk consts₀ ts).find? n ∨
    ∃ cv cv' mI rP rules rules',
      (Env.mk consts₀ ts).find? n = some (.recInfo cv mI rP rules) ∧
      (Env.mk consts₃ ts).find? n = some (.recInfo cv' mI rP rules') ∧
      cv'.name = cv.name ∧ cv'.levelParams = cv.levelParams ∧ cv.name = n ∧
      reservedRecName cv.name = false := by
  intro consts₀ consts₃ hsw
  induction hsw with
  | nil => intro n; exact Or.inl rfl
  | @cons c₀ c₃ rest₀ rest₃ hpair hrest ih =>
    intro n
    by_cases hn : c₃.name = n
    · have hn₀ : c₀.name = n := by rw [SwapPairTy.name_eq hpair, hn]
      have h₃ : (Env.mk (c₃ :: rest₃) ts).find? n = some c₃ := by
        show (c₃ :: rest₃).find? (·.name == n) = some c₃
        rw [List.find?_cons_of_pos (by simp [hn])]
      have h₀ : (Env.mk (c₀ :: rest₀) ts).find? n = some c₀ := by
        show (c₀ :: rest₀).find? (·.name == n) = some c₀
        rw [List.find?_cons_of_pos (by simp [hn₀])]
      rcases hpair with rfl | ⟨cv, cv', mI, rP, rules, rules', rfl, rfl, hnm, hlp, hres⟩
      · exact Or.inl (h₃.trans h₀.symm)
      · exact Or.inr ⟨cv, cv', mI, rP, rules, rules', h₀, h₃, hnm, hlp, hn₀, hres⟩
    · have hn₀ : ¬c₀.name = n := by
        rw [SwapPairTy.name_eq hpair]
        exact hn
      have h₃ : (Env.mk (c₃ :: rest₃) ts).find? n =
          (Env.mk rest₃ ts).find? n := by
        show (c₃ :: rest₃).find? (·.name == n) =
          rest₃.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn])]
      have h₀ : (Env.mk (c₀ :: rest₀) ts).find? n =
          (Env.mk rest₀ ts).find? n := by
        show (c₀ :: rest₀).find? (·.name == n) =
          rest₀.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn₀])]
      rw [h₃, h₀]
      exact ih n

/-- Every member of the swapped list corresponds to a member of the
original. -/
theorem swapTy_mem_corr :
    ∀ {consts₀ consts₃ : List ConstantInfo},
      SwapTyList consts₀ consts₃ →
      ∀ c₃ ∈ consts₃, ∃ c₀ ∈ consts₀, SwapPairTy c₀ c₃ := by
  intro consts₀ consts₃ hsw
  induction hsw with
  | nil => intro c₃ hc; exact nomatch hc
  | cons hpair hrest ih =>
    intro c₃ hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, List.mem_cons_self, hpair⟩
    · obtain ⟨c₀, hc₀, hp⟩ := ih c₃ hc
      exact ⟨c₀, List.mem_cons_of_mem _ hc₀, hp⟩

/-- A type-and-rules swap induces the congruences. -/
theorem SwapTyList.congr {consts₀ consts₃ : List ConstantInfo} {ts : List ProjTable}
    (hsw : SwapTyList consts₀ consts₃) :
    SwapCongr (Env.mk consts₀ ts) (Env.mk consts₃ ts) := by
  have hcorr := swapTy_find?_corr (ts := ts) hsw
  have hchk : ∀ (chk : Option ConstantInfo → Bool) (n : Name), reservedRecName n = true →
      chk ((Env.mk consts₀ ts).find? n) = chk ((Env.mk consts₃ ts).find? n) := by
    intro chk n hn
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, rules, rules', h₀, h₃, -, -, hname, hres⟩
    · rw [heq]
    · rw [hname, hn] at hres
      exact absurd hres (by decide)
  have hfeq : ∀ n, reservedRecName n = true →
      (Env.mk consts₀ ts).find? n = (Env.mk consts₃ ts).find? n := by
    intro n hn
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, rules, rules', h₀, h₃, -, -, hname, hres⟩
    · rw [heq]
    · rw [hname, hn] at hres
      exact absurd hres (by decide)
  have hnat : natLitSupported (Env.mk consts₀ ts)
      = natLitSupported (Env.mk consts₃ ts) := by
    unfold natLitSupported
    rw [hfeq natName (by decide), hfeq natZeroName (by decide), hfeq natSuccName (by decide)]
  refine ⟨?_, ?_, hnat, ?_, ?_, ?_, ?_, rfl⟩
  · intro n
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, rules, rules', h₀, h₃, -, hlp⟩
    · rw [heq]
    · rw [h₀, h₃]; simp [ConstantInfo.toConstantVal, hlp]
  · intro n
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, rules, rules', h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]; rfl
  · unfold strLitSupported
    rw [hnat, hfeq stringName (by decide), hfeq stringOfListName (by decide),
      hfeq listName (by decide), hfeq listNilName (by decide), hfeq listConsName (by decide),
      hfeq charName (by decide), hfeq charOfNatName (by decide)]
  · intro c
    unfold natOpGuard
    rw [hnat]
    congr 1
    · congr 1
      refine congrArg (List.all (natOpDeps c)) (funext fun n => ?_)
      rcases hcorr n with heq | ⟨cv2, cv2', a, b, c2, c2', h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃]
    · split
      · congr 1
        · rw [hfeq boolTrueName (by decide)]
        · rw [hfeq boolFalseName (by decide)]
      · rfl
  · intro n ci hf hnr
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, rules, rules', h₀, h₃, -⟩
    · rw [← heq]; exact hf
    · rw [h₃] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv' mI rP rules')
  · intro n ci hf hnr
    rcases hcorr n with heq | ⟨cv, cv', mI, rP, rules, rules', h₀, h₃, -⟩
    · rw [heq]; exact hf
    · rw [h₀] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP rules)

theorem SwapTyList.congrEnv {env₀ env₃ : Env} (hsw : SwapTyList env₀.consts env₃.consts)
    (ht : env₃.tables = env₀.tables) : SwapCongr env₀ env₃ := by
  obtain ⟨c₀, t₀⟩ := env₀
  obtain ⟨c₃, t₃⟩ := env₃
  simp only at ht hsw
  subst ht
  exact SwapTyList.congr hsw

theorem swapTy_find?_corrEnv {env₀ env₃ : Env} (hsw : SwapTyList env₀.consts env₃.consts)
    (n : Name) :
    env₃.find? n = env₀.find? n ∨
    ∃ cv cv' mI rP rules rules',
      env₀.find? n = some (.recInfo cv mI rP rules) ∧
      env₃.find? n = some (.recInfo cv' mI rP rules') ∧
      cv'.name = cv.name ∧ cv'.levelParams = cv.levelParams ∧ cv.name = n ∧
      reservedRecName cv.name = false :=
  swapTy_find?_corr (ts := []) hsw n

end ConLeche
