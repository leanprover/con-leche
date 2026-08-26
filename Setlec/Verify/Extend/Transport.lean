import Setlec.Verify.EnvWF

/-!
# Transport — the `V`-free half of `Setlec.Model.Extend.Transport`

The rule-list swaps at the clauses that read the environment only:
`Env.find?_recRules_swap`, `Env.recRules_levelext`,
`Env.recRules_isSome`, `ConstWF.recRules_swap` and
`ConstWF.recRules_head_empty` — everything the checker reads through
the environment ignores a stored recursor's rule list.

Relocated from `Setlec/Model/Extend/Transport.lean` (task #123); the
fresh-extension transports and `extend_rec_swap` stay there, being
statements about a valuation.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

open Expr

variable {env : Env} {cvA : ConstantVal} {mI rP : Nat}

/-- Lookups of other names ignore the head recursor's rule list. -/
theorem Env.find?_recRules_swap (rules₁ rules₂ : List RecRule) {n : Name}
    (hn : n ≠ cvA.name) :
    (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n =
    (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n := by
  rw [Env.find?_cons, Env.find?_cons,
    if_neg (show ¬(ConstantInfo.recInfo cvA mI rP rules₁).name = n
      from fun h => hn h.symm),
    if_neg (show ¬(ConstantInfo.recInfo cvA mI rP rules₂).name = n
      from fun h => hn h.symm)]

/-- Stored level parameters ignore the head recursor's rule list. -/
theorem Env.recRules_levelext (rules₁ rules₂ : List RecRule) :
    ∀ n,
      ((⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) =
      ((⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n).map
        (fun ci => ci.toConstantVal.levelParams) := by
  intro n
  rw [Env.find?_cons, Env.find?_cons]
  by_cases h : cvA.name = n
  · rw [if_pos (show (ConstantInfo.recInfo cvA mI rP
        rules₁).name = n from h),
      if_pos (show (ConstantInfo.recInfo cvA mI rP
        rules₂).name = n from h)]
    rfl
  · rw [if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
        rules₁).name = n from h),
      if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
        rules₂).name = n from h)]

/-- Lookup success ignores the head recursor's rule list. -/
theorem Env.recRules_isSome (rules₁ rules₂ : List RecRule) :
    ∀ n,
      ((⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env).find? n).isSome
      =
      ((⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env).find? n).isSome := by
  intro n
  rw [Env.find?_cons, Env.find?_cons]
  by_cases h : cvA.name = n
  · rw [if_pos (show (ConstantInfo.recInfo cvA mI rP
        rules₁).name = n from h),
      if_pos (show (ConstantInfo.recInfo cvA mI rP
        rules₂).name = n from h)]
    rfl
  · rw [if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
        rules₁).name = n from h),
      if_neg (show ¬(ConstantInfo.recInfo cvA mI rP
        rules₂).name = n from h)]

/-- `ConstWF` of a stored constant ignores the head recursor's rule
list. -/
theorem ConstWF.recRules_swap (rules₁ rules₂ : List RecRule)
    {c : ConstantInfo}
    (hc : ConstWF (⟨.recInfo cvA mI rP rules₁ :: env.consts⟩ : Env) c) :
    ConstWF (⟨.recInfo cvA mI rP rules₂ :: env.consts⟩ : Env) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hc
  refine ⟨h1, h2, ?_, h4, ?_, ?_, ?_⟩
  · rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
    exact h3
  · intro cv2 v2 h2 heq
    obtain ⟨a, b, cres, dd⟩ := h5 cv2 v2 h2 heq
    exact ⟨a, b,
      by rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
         exact cres,
      dd⟩
  · intro cv mI' rP' rules heq r hr
    obtain ⟨a, b, cres, dd, nn⟩ := h6 cv mI' rP' rules heq r hr
    refine ⟨a, b,
      by rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
         exact cres,
      dd, ?_⟩
    intro lvls pins hfr
    obtain ⟨n1, n2, n3, n4⟩ := nn lvls pins hfr
    refine ⟨n1, n2, fun pin hpin => ?_, n4⟩
    obtain ⟨p1, p2, p3, p4⟩ := n3 pin hpin
    refine ⟨p1, p2, ?_, p4⟩
    rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
    exact p3
  · intro cv2 v2 heq
    obtain ⟨a, b, cres, dd⟩ := h7 cv2 v2 heq
    exact ⟨a, b,
      by rw [← Expr.constsResolve_congr (Env.recRules_isSome rules₁ rules₂)]
         exact cres,
      dd⟩

/-- The head recursor's own `ConstWF`, with the rule list dropped (the
rules-free provisional install). -/
theorem ConstWF.recRules_head_empty {rules' : List RecRule}
    (hwf : ConstWF (⟨.recInfo cvA mI rP rules' :: env.consts⟩ : Env)
      (.recInfo cvA mI rP rules')) :
    ConstWF (⟨.recInfo cvA mI rP [] :: env.consts⟩ : Env)
      (.recInfo cvA mI rP []) := by
  obtain ⟨h1, h2, h3, h4, -, -, -⟩ := hwf
  refine ⟨h1, h2, ?_, h4, ?_, ?_, ?_⟩
  · rw [← Expr.constsResolve_congr (Env.recRules_isSome rules' [])]
    exact h3
  · intro cv2 v2 h2 heq
    exact nomatch heq
  · intro cv mI' rP' rules heq
    injection heq with e1 e2 e3 e4
    subst e4
    intro r hr
    cases hr
  · intro cv2 v2 heq
    exact nomatch heq

end Setlec
