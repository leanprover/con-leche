module

import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Shift
import ConLeche.Kernel.Checker
import ConLeche.Verify.Abstract
import ConLeche.Verify.EnvWF
public import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Subst

public section

/-!
# Recs

The recursor rule-list swap's bookkeeping: `SwapPairSh`/`SwapShList`
(a rule-less stored recursor replaced by one with its rules), the
lookups they correspond (`swapSh_find?_corr`, `swapSh_mem_corr`), and
the environment congruences the swap induces (`SwapCongr`).

All of it is stated over `Env`/`Expr` alone; the runs that read a
valuation are assembled from these records one tier up
(`ConLeche/Semantics/IndBlockFacts.lean`).
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}

open Expr

/-- The shape-level swap pair (no obligations). -/
@[expose] def SwapPairSh (c₀ c₃ : ConstantInfo) : Prop :=
  c₀ = c₃ ∨
  ∃ cv mI rP rules,
    c₀ = .recInfo cv mI rP [] ∧ c₃ = .recInfo cv mI rP rules

/-- Pointwise shape-level swap of two constant lists. -/
inductive SwapShList : List ConstantInfo → List ConstantInfo → Prop
  | nil : SwapShList [] []
  | cons {c₀ c₃ : ConstantInfo} {rest₀ rest₃ : List ConstantInfo} :
      SwapPairSh c₀ c₃ → SwapShList rest₀ rest₃ →
      SwapShList (c₀ :: rest₀) (c₃ :: rest₃)

theorem SwapShList.of_eq : ∀ (l : List ConstantInfo), SwapShList l l
  | [] => SwapShList.nil
  | _c :: l => SwapShList.cons (Or.inl rfl) (SwapShList.of_eq l)

theorem SwapPairSh.name_eq {c₀ c₃ : ConstantInfo}
    (h : SwapPairSh c₀ c₃) : c₀.name = c₃.name := by
  rcases h with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩
  · rfl
  · rfl

/-- The lookup correspondence of a shape-level swap. -/
theorem swapSh_find?_corr :
    ∀ {consts₀ consts₃ : List ConstantInfo},
    SwapShList consts₀ consts₃ →
    ∀ n : Name,
    (Env.mk consts₃).find? n = (Env.mk consts₀).find? n ∨
    ∃ cv mI rP rules,
      (Env.mk consts₀).find? n = some (.recInfo cv mI rP []) ∧
      (Env.mk consts₃).find? n = some (.recInfo cv mI rP rules) ∧
      cv.name = n := by
  intro consts₀ consts₃ hsw
  induction hsw with
  | nil => intro n; exact Or.inl rfl
  | @cons c₀ c₃ rest₀ rest₃ hpair hrest ih =>
    intro n
    by_cases hn : c₃.name = n
    · have hn₀ : c₀.name = n := by rw [SwapPairSh.name_eq hpair, hn]
      have h₃ : (Env.mk (c₃ :: rest₃)).find? n = some c₃ := by
        show (c₃ :: rest₃).find? (·.name == n) = some c₃
        rw [List.find?_cons_of_pos (by simp [hn])]
      have h₀ : (Env.mk (c₀ :: rest₀)).find? n = some c₀ := by
        show (c₀ :: rest₀).find? (·.name == n) = some c₀
        rw [List.find?_cons_of_pos (by simp [hn₀])]
      rcases hpair with rfl | ⟨cv, mI, rP, rules, rfl, rfl⟩
      · exact Or.inl (h₃.trans h₀.symm)
      · exact Or.inr ⟨cv, mI, rP, rules, h₀, h₃,
          (show cv.name = n from hn)⟩
    · have hn₀ : ¬c₀.name = n := by
        rw [SwapPairSh.name_eq hpair]
        exact hn
      have h₃ : (Env.mk (c₃ :: rest₃)).find? n =
          (Env.mk rest₃).find? n := by
        show (c₃ :: rest₃).find? (·.name == n) =
          rest₃.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn])]
      have h₀ : (Env.mk (c₀ :: rest₀)).find? n =
          (Env.mk rest₀).find? n := by
        show (c₀ :: rest₀).find? (·.name == n) =
          rest₀.find? (·.name == n)
        rw [List.find?_cons_of_neg (by simp [hn₀])]
      rw [h₃, h₀]
      exact ih n


/-- Every member of the swapped list corresponds to a member of the
original. -/
theorem swapSh_mem_corr :
    ∀ {consts₀ consts₃ : List ConstantInfo},
      SwapShList consts₀ consts₃ →
      ∀ c₃ ∈ consts₃, ∃ c₀ ∈ consts₀, SwapPairSh c₀ c₃ := by
  intro consts₀ consts₃ hsw
  induction hsw with
  | nil => intro c₃ hc; exact nomatch hc
  | cons hpair hrest ih =>
    intro c₃ hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨_, List.mem_cons_self, hpair⟩
    · obtain ⟨c₀, hc₀, hp⟩ := ih c₃ hc
      exact ⟨c₀, List.mem_cons_of_mem _ hc₀, hp⟩



/-! ## The congruences a shape-level swap induces

Everything `denote` and the environment guards read is invariant under
replacing a rule-less recursor's rule list, because they read the
environment only through `find?`-`toConstantVal`.  Bundled here (task
#148, T5 stage 3) so both lanes' swap transports consume one object;
the TT lane's `EnvTT.swap` still carries an inline copy of these
`have`s, which this supersedes for any future consumer. -/

/-- The environment congruences of a shape-level rule-list swap. -/
structure SwapCongr (env₀ env₃ : Env) : Prop where
  /-- Stored level parameters are unchanged. -/
  levelsEq : ∀ n, (env₀.find? n).map (fun ci => ci.toConstantVal.levelParams)
    = (env₃.find? n).map (fun ci => ci.toConstantVal.levelParams)
  /-- The set of stored names is unchanged. -/
  isSomeEq : ∀ n, (env₀.find? n).isSome = (env₃.find? n).isSome
  /-- The two literal guards are unchanged. -/
  natEq : natLitSupported env₀ = natLitSupported env₃
  strEq : strLitSupported env₀ = strLitSupported env₃
  /-- The `Nat`-operation guards are unchanged. -/
  guardEq : ∀ c, natOpGuard env₀ c = natOpGuard env₃ c
  /-- A non-recursor lookup transports down. -/
  findDown : ∀ (n : Name) (ci : ConstantInfo), env₃.find? n = some ci →
    (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
    env₀.find? n = some ci
  /-- …and up. -/
  findUp : ∀ (n : Name) (ci : ConstantInfo), env₀.find? n = some ci →
    (∀ cv mI rP rules, ci ≠ .recInfo cv mI rP rules) →
    env₃.find? n = some ci

/-- Projection-table lookups transport across the swap: a `projInfo`
is never a recursor, so `findDown`/`findUp` move it both ways (task
#175 wiring W3 — `denote`'s `.proj` clause now reads the entry
kind). -/
theorem SwapCongr.projEq {env₀ env₃ : Env} (hcg : SwapCongr env₀ env₃) :
    ∀ (sn : Name) (i : Nat), env₀.findProj? sn i = env₃.findProj? sn i := by
  intro sn i
  unfold Env.findProj?
  cases h0 : env₀.find? (projTableName sn) with
  | none =>
    cases h3 : env₃.find? (projTableName sn) with
    | none => rfl
    | some ci =>
      have := hcg.isSomeEq (projTableName sn)
      rw [h0, h3] at this
      exact nomatch this
  | some ci =>
    cases ci with
    | projInfo e =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | recInfo cv mI rP rules =>
      cases h3 : env₃.find? (projTableName sn) with
      | none => rfl
      | some ci₃ =>
        cases ci₃ with
        | projInfo e₃ =>
          have := hcg.findDown _ _ h3 (fun _ _ _ _ h => nomatch h)
          rw [h0] at this
          exact nomatch this
        | axiomInfo cv₃ => rfl
        | defnInfo cv₃ v₃ h₃ => rfl
        | thmInfo cv₃ v₃ => rfl
        | indInfo cv₃ caps₃ => rfl
        | ctorInfo cv₃ np₃ nf₃ => rfl
        | recInfo cv₃ mI₃ rP₃ rules₃ => rfl
    | axiomInfo cv =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | defnInfo cv v hint =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | thmInfo cv v =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | indInfo cv caps =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]
    | ctorInfo cv np nf =>
      rw [hcg.findUp _ _ h0 (fun _ _ _ _ h => nomatch h)]

/-- A shape-level swap induces the congruences. -/
theorem SwapShList.congr {consts₀ consts₃ : List ConstantInfo}
    (hsw : SwapShList consts₀ consts₃) :
    SwapCongr (Env.mk consts₀) (Env.mk consts₃) := by
  have hcorr := swapSh_find?_corr hsw
  have hchk : ∀ (chk : Option ConstantInfo → Bool),
      (∀ cv mI rP rules rules',
        chk (some (.recInfo cv mI rP rules)) =
        chk (some (.recInfo cv mI rP rules'))) →
      ∀ n, chk ((Env.mk consts₀).find? n) = chk ((Env.mk consts₃).find? n) := by
    intro chk hins n
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]
      exact hins cv mI rP [] rules
  have hnat : natLitSupported (Env.mk consts₀)
      = natLitSupported (Env.mk consts₃) := by
    unfold natLitSupported
    rw [hchk natIndOk (fun _ _ _ _ _ => rfl) natName,
      hchk natZeroOk (fun _ _ _ _ _ => rfl) natZeroName,
      hchk natSuccOk (fun _ _ _ _ _ => rfl) natSuccName]
  refine ⟨?_, ?_, hnat, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]; rfl
  · intro n
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]
    · rw [h₀, h₃]; rfl
  · unfold strLitSupported
    rw [hnat,
      hchk stringTyOk (fun _ _ _ _ _ => rfl) stringName,
      hchk stringOfListTyOk (fun _ _ _ _ _ => rfl) stringOfListName,
      hchk listTyOk (fun _ _ _ _ _ => rfl) listName,
      hchk listNilTyOk (fun _ _ _ _ _ => rfl) listNilName,
      hchk listConsTyOk (fun _ _ _ _ _ => rfl) listConsName,
      hchk charTyOk (fun _ _ _ _ _ => rfl) charName,
      hchk charOfNatTyOk (fun _ _ _ _ _ => rfl) charOfNatName]
  · intro c
    unfold natOpGuard
    rw [hnat]
    congr 1
    · congr 1
      refine congrArg (List.all (natOpDeps c)) (funext fun n => ?_)
      rcases hcorr n with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
      · rw [heq]
      · rw [h₀, h₃]
    · split
      · congr 1
        · rcases hcorr boolTrueName with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
          · rw [heq]
          · rw [h₀, h₃]; rfl
        · rcases hcorr boolFalseName with heq | ⟨cv2, a, b, c2, h₀, h₃, -⟩
          · rw [heq]
          · rw [h₀, h₃]; rfl
      · rfl
  · intro n ci hf hnr
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [← heq]; exact hf
    · rw [h₃] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP rules)
  · intro n ci hf hnr
    rcases hcorr n with heq | ⟨cv, mI, rP, rules, h₀, h₃, -⟩
    · rw [heq]; exact hf
    · rw [h₀] at hf
      obtain rfl := Option.some.inj hf
      exact absurd rfl (hnr cv mI rP [])

end ConLeche
