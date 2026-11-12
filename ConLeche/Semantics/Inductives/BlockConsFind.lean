module

public import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Inductives.BlockInv

@[expose] public section

/-!
# Lookups through a block's conses

What a lookup reads after the uniform install's formers' and
constructors' conses (`consBlockInds`, `consSumCtors`, `consBlockCtors`):
a name none of them carries reads through unchanged, the constructors
store no former, and the formers are consed at names fresh before the
block (`checkBlockInds_fresh`).
-/

namespace ConLeche.Semantics

open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  fueledOps checkConstantVal ProjEntry)

/-! ## Lookups through the constructors' conses -/


open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo
  InductiveShape fueledOps checkSumCtors
   consSumCtors sumRules)

/-- A name none of the consed constructors carries looks up below the
conses. -/
theorem consSumCtors_find?_of_not_mem {nP : Nat} {T : Name} {n : Name} :
    ∀ {ctorList : List (ConstantVal × Nat)} {env : Env},
      n ∉ ctorList.map (·.1.name) → (consSumCtors nP T ctorList env).find? n = env.find? n
  | [], _, _ => rfl
  | c :: cs, env, hn => by
    simp only [consSumCtors]
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [consSumCtors_find?_of_not_mem hn.2, ConLeche.Env.find?_cons, ite_eq_right (fun h => hn.1 h.symm)]


open ConLeche (Env Expr Name Level CheckMode ConstantVal ConstantInfo IndCaps
  BlockShape MemberShape fueledOps
  consBlockInds consBlockCtors consSumCtors
  checkBlockCtors checkSumCtors blockCapsAt)

/-! ## Lookups through the formers' and the constructors' conses -/

/-- A name none of the consed formers carries reads through the
formers' conses unchanged. -/
theorem consBlockInds_find?_of_ne {p₁ : BlockShape} {isRec : Bool} {n : Name} :
    ∀ {formers : List ConstantVal} {i : Nat} {env : Env},
      (∀ cv ∈ formers, cv.name ≠ n) →
      (consBlockInds p₁ isRec formers i env).find? n = env.find? n
  | [], _, _, _ => rfl
  | cv :: rest, i, env, hne => by
    simp only [consBlockInds]
    rw [consBlockInds_find?_of_ne (fun c hc => hne c (List.mem_cons_of_mem _ hc)),
      ConLeche.Env.find?_cons]
    exact ite_eq_right (hne cv List.mem_cons_self)

/-- A name none of the consed constructors carries reads through the
constructors' conses unchanged. -/
theorem consBlockCtors_find?_of_ne {nP : Nat} {n : Name} :
    ∀ {groups : List (Name × List (ConstantVal × Nat))} {env : Env},
      (∀ g ∈ groups, n ∉ g.2.map (·.1.name)) →
      (consBlockCtors nP groups env).find? n = env.find? n
  | [], _, _ => rfl
  | (T, ctorList) :: rest, env, hne => by
    simp only [consBlockCtors]
    rw [consBlockCtors_find?_of_ne (fun c hc => hne c (List.mem_cons_of_mem _ hc)),
      consSumCtors_find?_of_not_mem (hne (T, ctorList) List.mem_cons_self)]

/-- The constructors' conses store no former: a `.indInfo` found above
them was found below them. -/
theorem consSumCtors_find?_indInfo {nP : Nat} {T : Name} {n : Name} {cv : ConstantVal}
    {caps : IndCaps} :
    ∀ {ctorList : List (ConstantVal × Nat)} {env : Env},
      (consSumCtors nP T ctorList env).find? n = some (.indInfo cv caps) →
      env.find? n = some (.indInfo cv caps)
  | [], _, h => h
  | c :: cs, env, h => by
    simp only [consSumCtors] at h
    have h' := consSumCtors_find?_indInfo h
    rw [ConLeche.Env.find?_cons] at h'
    split at h'
    · exact nomatch Option.some.inj h'
    · exact h'

theorem consBlockCtors_find?_indInfo {nP : Nat} {n : Name} {cv : ConstantVal} {caps : IndCaps} :
    ∀ {groups : List (Name × List (ConstantVal × Nat))} {env : Env},
      (consBlockCtors nP groups env).find? n = some (.indInfo cv caps) →
      env.find? n = some (.indInfo cv caps)
  | [], _, h => h
  | (_, _) :: _, _, h => by
    simp only [consBlockCtors] at h
    exact consSumCtors_find?_indInfo (consBlockCtors_find?_indInfo h)

/-! ## The formers' stage: freshness -/

/-- **The k formers are consed at names fresh before the block.** -/
theorem checkBlockInds_fresh {mode : CheckMode} {env envI : Env} {p : BlockShape} {isRec : Bool}
    {p₁ : BlockShape} {F : Nat}
    (h : ConLeche.checkBlockInds (fueledOps mode F) env p isRec = .ok (envI, p₁)) :
    ∀ cv ∈ p.formers, env.find? cv.name = none := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, -, -, h0, hcvs, -⟩ := ConLeche.checkBlockInds_shape h
  have hone : ∀ {ms : MemberShape} {cv : ConstantVal} {s : Level},
      ConLeche.checkBlockTele (fueledOps mode F) env p.nP ms = .ok (cv, s) →
      env.find? cv.name = none := by
    intro ms cv s hh
    obtain ⟨cvT, -, -, heq, hcv, -⟩ := ConLeche.checkBlockTele_shape hh
    obtain ⟨hf, -, -, -, -, -, -, -, -, -⟩ := ConLeche.checkConstantVal_inv hcv
    rw [heq]; exact hf
  intro cv hcv
  rw [← ConLeche.checkBlockInds_teles hm h0 hcvs] at hcv
  rcases List.mem_cons.mp hcv with rfl | hcv'
  · exact hone h0
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcv'
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
    obtain ⟨hlen, hall⟩ := ConLeche.checkBlockTeles_inv hcvs
    have hil : i < rest.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨q', hq', hrun⟩ := hall i (rest[i]) (List.getElem?_eq_getElem hil)
    obtain rfl := Option.some.inj (hi.symm.trans hq')
    exact hone hrun


end ConLeche.Semantics
