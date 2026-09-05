import Setlec.Verify.DirectInv
import Setlec.Verify.FastOps

/-!
# The direct recogniser and the projection slots, inverted (task #175 W4c, P3 module 7, part 7)

V-free facts the direct install's assembly reads off the kernel's
recogniser and slot decision:

* `directParts?_inv`: the block's shape facts the recogniser pins —
  the propositionality datum is the result sort's, the recursor is
  `T.rec` at the block's level parameters (plus the large eliminator's
  fresh one), the constructor carries the former's;
* `checkDirectProj_run`: a slot's run is a skipped slot or the entry
  run at the generated type;
* `directProjSlots_prefix`: an installed slot's earlier slots are
  installed (the generated types peel a prefix, the decision is
  monotone);
* `directProjGuards_getD`: the coarse guard's spelling at a slot.
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

/-! ## A slot's run -/

theorem checkDirectProj_run {μ : CheckMode} {F : Nat} {T C : Name}
    {lps : List Name} {nP nF : Nat} {resSort : Level} {slots : List Bool}
    {guards : List Level} {cvTa cvCa : ConstantVal} {env env' : Env} {i : Nat}
    (h : checkDirectProj (m := CheckM) (fueledOps μ F) T C lps nP nF
      resSort slots guards cvTa cvCa env i = .ok env') :
    (slots.getD i false = false ∧ env' = env) ∨
    (slots.getD i false = true ∧
      ∃ pty, directProjTyP T lps nP nF i cvTa.type cvCa.type = some pty ∧
        checkDirectProjEntry (m := CheckM) (fueledOps μ F) T C lps nP nF resSort
          (guards.getD i .zero) cvCa pty env i = .ok env') := by
  unfold checkDirectProj at h
  split at h
  · next hs =>
    obtain ⟨pty, hpty, h⟩ := exceptBind_ok h
    exact Or.inr ⟨hs, pty, unwrapOr_ok hpty, h⟩
  · next hs =>
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨by simpa using hs, h.symm⟩

/-! ## The slots are a prefix -/

/-- `replacePiBody`'s success depends on the telescope alone. -/
theorem replacePiBody_isSome_congr :
    ∀ (n : Nat) (tty : Expr) (X Y : Expr),
      (Expr.replacePiBody n tty X).isSome = (Expr.replacePiBody n tty Y).isSome
  | 0, _, _, _ => rfl
  | n + 1, .forallE nm ty rest m, X, Y => by
    simp only [Expr.replacePiBody, Option.isSome_map]
    exact replacePiBody_isSome_congr n rest X Y
  | _ + 1, .bvar _, _, _ | _ + 1, .fvar _ _ _, _, _ | _ + 1, .sort _, _, _
  | _ + 1, .const _ _, _, _ | _ + 1, .app _ _, _, _ | _ + 1, .lam _ _ _ _, _, _
  | _ + 1, .letE _ _ _ _, _, _ | _ + 1, .lit _, _, _ | _ + 1, .proj _ _ _, _, _ => rfl

theorem directProjTyP_prefix {T : Name} {lps : List Name} {nP nF i j : Nat}
    {tty cty : Expr} (hj : j < i) (hi : i < nF)
    (h : (directProjTyP T lps nP nF i tty cty).isSome = true) :
    (directProjTyP T lps nP nF j tty cty).isSome = true := by
  have h' : (directProjTyR T lps nP nF i tty
      (Expr.instPisAtLift (directProjPs nP ++ (List.range i).map (directProjArgP T)) cty)).isSome
      = true := h
  show (directProjTyR T lps nP nF j tty
    (Expr.instPisAtLift (directProjPs nP ++ (List.range j).map (directProjArgP T)) cty)).isSome
    = true
  have hsplit : directProjPs nP ++ (List.range i).map (directProjArgP T)
      = (directProjPs nP ++ (List.range j).map (directProjArgP T))
        ++ (((List.range (i - j)).map fun x => j + x).map (directProjArgP T)) := by
    rw [List.append_assoc, ← List.map_append]
    congr 2
    rw [show i = j + (i - j) from by omega, List.range_add, Nat.add_sub_cancel_left]
  rw [hsplit, instPisAtLift_append] at h'
  cases hr : Expr.instPisAtLift (directProjPs nP ++ (List.range j).map (directProjArgP T)) cty with
  | none => rw [hr] at h'; exact nomatch h'
  | some r =>
    rw [hr, Option.bind_some] at h'
    -- the rest peels at least one binder off `r`
    have hne : ((List.range (i - j)).map fun x => j + x).map (directProjArgP T) ≠ [] := by
      simp only [ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
      omega
    match r, h' with
    | .forallE nm dom body mb, h' =>
      show (directProjTyR T lps nP nF j tty (some (.forallE nm dom body mb))).isSome = true
      simp only [directProjTyR, if_pos (show j < nF by omega)]
      cases ho : Expr.instPisAtLift (((List.range (i - j)).map fun x => j + x).map (directProjArgP T))
          (.forallE nm dom body mb) with
      | none => rw [ho] at h'; exact nomatch h'
      | some r' =>
        rw [ho] at h'
        match r', h' with
        | .forallE n' fdom' b' m', h' =>
          simp only [directProjTyR, if_pos hi] at h'
          rw [replacePiBody_isSome_congr]
          exact h'
        | .bvar _, h' | .fvar _ _ _, h' | .sort _, h' | .const _ _, h' | .app _ _, h'
        | .lam _ _ _ _, h' | .letE _ _ _ _, h' | .lit _, h' | .proj _ _ _, h' =>
          exact nomatch h'
    | .bvar _, h' | .fvar _ _ _, h' | .sort _, h' | .const _ _, h' | .app _ _, h'
    | .lam _ _ _ _, h' | .letE _ _ _ _, h' | .lit _, h' | .proj _ _ _, h' =>
      exfalso
      match hl : ((List.range (i - j)).map fun x => j + x).map (directProjArgP T), hne with
      | [], hne => exact hne rfl
      | a :: as, _ => rw [hl] at h'; simp [Expr.instPisAtLift, directProjTyR] at h'

theorem directProjSlots_prefix {p : DirectParts} {i j : Nat} (hj : j < i)
    (hi : i < p.nF) (h : (directProjSlots p).getD i false = true) :
    (directProjSlots p).getD j false = true := by
  unfold directProjSlots at h ⊢
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi] at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some] at h ⊢
  split at h
  · next hty =>
    have hsome := directProjTyP_prefix hj hi (by rw [hty]; rfl)
    split
    · unfold directProjSlotOk at h ⊢
      simp only [Bool.or_eq_true, beq_iff_eq] at h ⊢
      rcases h with (h | h) | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · omega
    · next hnone => rw [hnone] at hsome; exact nomatch hsome
  · exact nomatch h

/-- An installed slot of a propositional structure with the small
eliminator is the first. -/
theorem directProjSlots_first {p : DirectParts} {i : Nat} (hi : i < p.nF)
    (h : (directProjSlots p).getD i false = true) :
    p.isProp = false ∨ p.large = true ∨ i = 0 := by
  unfold directProjSlots at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi] at h
  simp only [Option.map_some, Option.getD_some] at h
  split at h
  · unfold directProjSlotOk at h
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · exact nomatch h

/-! ## The guard's spelling -/

theorem directProjGuards_getD (cty : Expr) (nP nF : Nat) (sorts : List Level) {i : Nat}
    (hi : i < nF) :
    (directProjGuards cty nP nF sorts).getD i .zero
      = (List.range i).foldl (fun acc j => Level.max acc (sorts.getD j .zero))
          (sorts.getD i .zero) := by
  unfold directProjGuards
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

end Setlec
