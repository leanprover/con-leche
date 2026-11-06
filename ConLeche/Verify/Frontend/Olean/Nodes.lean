module

public import ConLeche.Verify.Frontend.Olean.Kids

public section

/-!
# The node functions and the table (task #371)

For each of the four node functions (`nameNode` … `exprNode`,
`ConLeche/Frontend/Olean/Spec.lean`), the three facts the passes use:

* `…_none`: where the marking fails (`¬ MarkOK`), the node function
  fails, whatever its arguments;
* `…_kid`: an object the specification reads leads (`Kid`) only to
  objects it reads (`KindOK`);
* `…_congr`: the node function asks its arguments about the objects
  the object leads to and nothing else.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-! ## Pointers -/

theorem down_none_of {r : Region} {g : Nat} {nil : Bool} {v : UInt64}
    (h : ¬ FieldOK r g nil v) : ¬ (nil = true ∧ v = 1) ∧ r.down g v = none := by
  unfold FieldOK at h
  refine ⟨fun e => h (Or.inl e), ?_⟩
  cases e : r.down g v
  · rfl
  · exact absurd (Or.inr (by simp [e])) h

theorem levelIn_none {r : Region} {g : Nat} {v : UInt64} {sub : (c : Nat) → c < g → Option Level}
    (h : ¬ FieldOK r g true v) : r.levelIn g v sub = none := by
  obtain ⟨h1, h2⟩ := down_none_of h
  unfold Region.levelIn
  simp only [show v ≠ 1 from fun e => h1 ⟨rfl, e⟩, beq_iff_eq, ite_false]
  split
  · rename_i heq; rw [h2] at heq; cases heq
  · rfl

theorem levelsIn_none {r : Region} {g : Nat} {v : UInt64}
    {sub : (c : Nat) → c < g → Option (List Level)}
    (h : ¬ FieldOK r g true v) : r.levelsIn g v sub = none := by
  obtain ⟨h1, h2⟩ := down_none_of h
  unfold Region.levelsIn
  simp only [show v ≠ 1 from fun e => h1 ⟨rfl, e⟩, beq_iff_eq, ite_false]
  split
  · rename_i heq; rw [h2] at heq; cases heq
  · rfl

theorem exprIn_none {r : Region} {g : Nat} {v : UInt64} {sub : (c : Nat) → c < g → Option Expr}
    (h : ¬ FieldOK r g false v) : r.exprIn g v sub = none := by
  obtain ⟨_, h2⟩ := down_none_of h
  unfold Region.exprIn
  split
  · rename_i heq; rw [h2] at heq; cases heq
  · rfl

theorem nameIn_kid {r : Region} {g : Nat} {v : UInt64} {sub : (c : Nat) → c < g → Option Name}
    {x : Name} {c : Nat} (h : r.nameIn g v sub = some x) (hv : ¬ v = 1)
    (hc : r.down g v = some c) : ∃ h, sub c h = some x := by
  unfold Region.nameIn at h
  simp only [hv, beq_iff_eq, ite_false] at h
  split at h
  · rename_i c' heq; rw [hc] at heq; cases heq; exact ⟨_, h⟩
  · cases h

theorem levelIn_kid {r : Region} {g : Nat} {v : UInt64} {sub : (c : Nat) → c < g → Option Level}
    {x : Level} {c : Nat} (h : r.levelIn g v sub = some x) (hv : ¬ v = 1)
    (hc : r.down g v = some c) : ∃ h, sub c h = some x := by
  unfold Region.levelIn at h
  simp only [hv, beq_iff_eq, ite_false] at h
  split at h
  · rename_i c' heq; rw [hc] at heq; cases heq; exact ⟨_, h⟩
  · cases h

theorem levelsIn_kid {r : Region} {g : Nat} {v : UInt64}
    {sub : (c : Nat) → c < g → Option (List Level)}
    {x : List Level} {c : Nat} (h : r.levelsIn g v sub = some x) (hv : ¬ v = 1)
    (hc : r.down g v = some c) : ∃ h, sub c h = some x := by
  unfold Region.levelsIn at h
  simp only [hv, beq_iff_eq, ite_false] at h
  split at h
  · rename_i c' heq; rw [hc] at heq; cases heq; exact ⟨_, h⟩
  · cases h

theorem exprIn_kid {r : Region} {g : Nat} {v : UInt64} {sub : (c : Nat) → c < g → Option Expr}
    {x : Expr} {c : Nat} (h : r.exprIn g v sub = some x)
    (hc : r.down g v = some c) : ∃ h, sub c h = some x := by
  unfold Region.exprIn at h
  split at h
  · rename_i c' heq; rw [hc] at heq; cases heq; exact ⟨_, h⟩
  · cases h

theorem nameIn_congr {r : Region} {g : Nat} {v : UInt64} {f f' : (c : Nat) → c < g → Option Name}
    (h : ∀ c hc, ¬ v = 1 → r.down g v = some c → f c hc = f' c hc) :
    r.nameIn g v f = r.nameIn g v f' := by
  unfold Region.nameIn
  by_cases hv : v = 1
  · simp [hv]
  · simp only [hv, beq_iff_eq, ite_false]
    split
    · rename_i c heq; exact h c _ hv heq
    · rfl

theorem levelIn_congr {r : Region} {g : Nat} {v : UInt64} {f f' : (c : Nat) → c < g → Option Level}
    (h : ∀ c hc, ¬ v = 1 → r.down g v = some c → f c hc = f' c hc) :
    r.levelIn g v f = r.levelIn g v f' := by
  unfold Region.levelIn
  by_cases hv : v = 1
  · simp [hv]
  · simp only [hv, beq_iff_eq, ite_false]
    split
    · rename_i c heq; exact h c _ hv heq
    · rfl

theorem levelsIn_congr {r : Region} {g : Nat} {v : UInt64}
    {f f' : (c : Nat) → c < g → Option (List Level)}
    (h : ∀ c hc, ¬ v = 1 → r.down g v = some c → f c hc = f' c hc) :
    r.levelsIn g v f = r.levelsIn g v f' := by
  unfold Region.levelsIn
  by_cases hv : v = 1
  · simp [hv]
  · simp only [hv, beq_iff_eq, ite_false]
    split
    · rename_i c heq; exact h c _ hv heq
    · rfl

theorem exprIn_congr {r : Region} {g : Nat} {v : UInt64} {f f' : (c : Nat) → c < g → Option Expr}
    (h : ∀ c hc, r.down g v = some c → f c hc = f' c hc) :
    r.exprIn g v f = r.exprIn g v f' := by
  unfold Region.exprIn
  split
  · rename_i c heq; exact h c _ heq
  · rfl

/-! ## Names -/

set_option linter.unusedSimpArgs false in
theorem nameNode_none {r : Region} {g : Nat} (h : ¬ MarkOK r kName g)
    (f : (c : Nat) → c < g → Option Name) : nameNode r g f = none := by
  unfold nameNode
  split
  · rename_i hf
    split
    all_goals first
      | rfl
      | (rename_i ht hn
         simp only [MarkOK, hf, kidTable, ite_true, nameKids, ht, hn, true_and,
           Option.some.injEq, exists_eq_left', List.mem_cons, List.not_mem_nil, or_false,
           forall_eq, Classical.not_and_iff_not_or_not, List.forall_mem_cons] at h
         simp [nameIn_none h])
  · rfl

set_option linter.unusedSimpArgs false in
theorem exprNode_none {r : Region} {g : Nat} (h : ¬ MarkOK r kExpr g)
    (ex : (c : Nat) → c < g → Option Expr) (nm : (c : Nat) → c < g → Option Name)
    (lv : (c : Nat) → c < g → Option Level) (ls : (c : Nat) → c < g → Option (List Level)) :
    exprNode r g ex nm lv ls = none := by
  unfold exprNode
  split
  · rename_i hf
    split
    all_goals first
      | rfl
      | (rename_i ht hn
         simp only [MarkOK, hf, kidTable, show kExpr ≠ kName by decide,
           show kExpr ≠ kLevel by decide, show kExpr ≠ kLevels by decide, ite_false,
           exprKids, ht, hn, true_and,
           Option.some.injEq, exists_eq_left', List.forall_mem_cons, List.not_mem_nil,
           false_imp_iff, implies_true, not_true_eq_false, Classical.not_and_iff_not_or_not, and_true,
           or_false] at h
         all_goals (try (rcases h with h | h))
         all_goals (try (rcases h with h | h))
         all_goals first
           | exact h.elim
           | simp [exprIn_none, nameIn_none, levelIn_none, levelsIn_none, h])
  · rfl


set_option linter.unusedSimpArgs false in
theorem levelNode_none {r : Region} {g : Nat} (h : ¬ MarkOK r kLevel g)
    (lv : (c : Nat) → c < g → Option Level) (nm : (c : Nat) → c < g → Option Name) : levelNode r g lv nm = none := by
  unfold levelNode
  split
  · rename_i hf
    split
    all_goals first
      | rfl
      | (rename_i ht hn
         simp only [MarkOK, hf, kidTable, show kLevel ≠ kName by decide, ite_false, ite_true, levelKids, ht, hn, true_and,
           Option.some.injEq, exists_eq_left', List.forall_mem_cons, List.not_mem_nil,
           false_imp_iff, implies_true, not_true_eq_false, Classical.not_and_iff_not_or_not, and_true,
           or_false] at h
         all_goals (try (rcases h with h | h))
         all_goals (try (rcases h with h | h))
         all_goals first
           | exact h.elim
           | simp [exprIn_none, nameIn_none, levelIn_none, levelsIn_none, h])
  · rfl

set_option linter.unusedSimpArgs false in
theorem levelsNode_none {r : Region} {g : Nat} (h : ¬ MarkOK r kLevels g)
    (ls : (c : Nat) → c < g → Option (List Level)) (lv : (c : Nat) → c < g → Option Level) : levelsNode r g ls lv = none := by
  unfold levelsNode
  split
  · rename_i hf
    split
    all_goals first
      | rfl
      | (rename_i ht hn
         simp only [MarkOK, hf, kidTable, show kLevels ≠ kName by decide, show kLevels ≠ kLevel by decide, ite_false, ite_true, levelsKids, ht, hn, true_and,
           Option.some.injEq, exists_eq_left', List.forall_mem_cons, List.not_mem_nil,
           false_imp_iff, implies_true, not_true_eq_false, Classical.not_and_iff_not_or_not, and_true,
           or_false] at h
         all_goals (try (rcases h with h | h))
         all_goals (try (rcases h with h | h))
         all_goals first
           | exact h.elim
           | simp [exprIn_none, nameIn_none, levelIn_none, levelsIn_none, h])
  · rfl


set_option linter.unusedSimpArgs false in
theorem nameNode_congr {r : Region} {g : Nat} {nm nm' : (c : Nat) → c < g → Option Name}
    (hnm : ∀ c h, Kid r kName g kName c → nm c h = nm' c h) :
    nameNode r g nm = nameNode r g nm' := by
  have enm : ∀ i, (∃ fs, kidTable kName (r.tag g) (r.nobjs g) = some fs ∧ (i, kName, true) ∈ fs) →
      r.fits g = true → r.nameIn g (r.fld g i) nm = r.nameIn g (r.fld g i) nm' :=
    fun i ⟨fs, hfs, hm⟩ hf => nameIn_congr fun c hc hv hd => hnm c hc ⟨hf, fs, hfs, i, true, hm, by simp [hv], hd⟩
  unfold nameNode
  split
  · split
    all_goals first
      | rfl
      | simp (disch := simp_all [kidTable_name, nameKids]) only [enm]
  · rfl

set_option linter.unusedSimpArgs false in
theorem levelNode_congr {r : Region} {g : Nat} {lv lv' : (c : Nat) → c < g → Option Level} {nm nm' : (c : Nat) → c < g → Option Name}
    (hlv : ∀ c h, Kid r kLevel g kLevel c → lv c h = lv' c h)
    (hnm : ∀ c h, Kid r kLevel g kName c → nm c h = nm' c h) :
    levelNode r g lv nm = levelNode r g lv' nm' := by
  have elv : ∀ i, (∃ fs, kidTable kLevel (r.tag g) (r.nobjs g) = some fs ∧ (i, kLevel, true) ∈ fs) →
      r.fits g = true → r.levelIn g (r.fld g i) lv = r.levelIn g (r.fld g i) lv' :=
    fun i ⟨fs, hfs, hm⟩ hf => levelIn_congr fun c hc hv hd => hlv c hc ⟨hf, fs, hfs, i, true, hm, by simp [hv], hd⟩
  have enm : ∀ i, (∃ fs, kidTable kLevel (r.tag g) (r.nobjs g) = some fs ∧ (i, kName, true) ∈ fs) →
      r.fits g = true → r.nameIn g (r.fld g i) nm = r.nameIn g (r.fld g i) nm' :=
    fun i ⟨fs, hfs, hm⟩ hf => nameIn_congr fun c hc hv hd => hnm c hc ⟨hf, fs, hfs, i, true, hm, by simp [hv], hd⟩
  unfold levelNode
  split
  · split
    all_goals first
      | rfl
      | simp (disch := simp_all [kidTable_level, levelKids]) only [elv, enm]
  · rfl

set_option linter.unusedSimpArgs false in
theorem levelsNode_congr {r : Region} {g : Nat} {ls ls' : (c : Nat) → c < g → Option (List Level)} {lv lv' : (c : Nat) → c < g → Option Level}
    (hls : ∀ c h, Kid r kLevels g kLevels c → ls c h = ls' c h)
    (hlv : ∀ c h, Kid r kLevels g kLevel c → lv c h = lv' c h) :
    levelsNode r g ls lv = levelsNode r g ls' lv' := by
  have els : ∀ i, (∃ fs, kidTable kLevels (r.tag g) (r.nobjs g) = some fs ∧ (i, kLevels, true) ∈ fs) →
      r.fits g = true → r.levelsIn g (r.fld g i) ls = r.levelsIn g (r.fld g i) ls' :=
    fun i ⟨fs, hfs, hm⟩ hf => levelsIn_congr fun c hc hv hd => hls c hc ⟨hf, fs, hfs, i, true, hm, by simp [hv], hd⟩
  have elv : ∀ i, (∃ fs, kidTable kLevels (r.tag g) (r.nobjs g) = some fs ∧ (i, kLevel, true) ∈ fs) →
      r.fits g = true → r.levelIn g (r.fld g i) lv = r.levelIn g (r.fld g i) lv' :=
    fun i ⟨fs, hfs, hm⟩ hf => levelIn_congr fun c hc hv hd => hlv c hc ⟨hf, fs, hfs, i, true, hm, by simp [hv], hd⟩
  unfold levelsNode
  split
  · split
    all_goals first
      | rfl
      | simp (disch := simp_all [kidTable_levels, levelsKids]) only [els, elv]
  · rfl

set_option linter.unusedSimpArgs false in
theorem exprNode_congr {r : Region} {g : Nat} {ex ex' : (c : Nat) → c < g → Option Expr} {nm nm' : (c : Nat) → c < g → Option Name} {lv lv' : (c : Nat) → c < g → Option Level} {ls ls' : (c : Nat) → c < g → Option (List Level)}
    (hex : ∀ c h, Kid r kExpr g kExpr c → ex c h = ex' c h)
    (hnm : ∀ c h, Kid r kExpr g kName c → nm c h = nm' c h)
    (hlv : ∀ c h, Kid r kExpr g kLevel c → lv c h = lv' c h)
    (hls : ∀ c h, Kid r kExpr g kLevels c → ls c h = ls' c h) :
    exprNode r g ex nm lv ls = exprNode r g ex' nm' lv' ls' := by
  have eex : ∀ i, (∃ fs, kidTable kExpr (r.tag g) (r.nobjs g) = some fs ∧ (i, kExpr, false) ∈ fs) →
      r.fits g = true → r.exprIn g (r.fld g i) ex = r.exprIn g (r.fld g i) ex' :=
    fun i ⟨fs, hfs, hm⟩ hf => exprIn_congr fun c hc hd => hex c hc ⟨hf, fs, hfs, i, false, hm, by simp, hd⟩
  have enm : ∀ i, (∃ fs, kidTable kExpr (r.tag g) (r.nobjs g) = some fs ∧ (i, kName, true) ∈ fs) →
      r.fits g = true → r.nameIn g (r.fld g i) nm = r.nameIn g (r.fld g i) nm' :=
    fun i ⟨fs, hfs, hm⟩ hf => nameIn_congr fun c hc hv hd => hnm c hc ⟨hf, fs, hfs, i, true, hm, by simp [hv], hd⟩
  have elv : ∀ i, (∃ fs, kidTable kExpr (r.tag g) (r.nobjs g) = some fs ∧ (i, kLevel, true) ∈ fs) →
      r.fits g = true → r.levelIn g (r.fld g i) lv = r.levelIn g (r.fld g i) lv' :=
    fun i ⟨fs, hfs, hm⟩ hf => levelIn_congr fun c hc hv hd => hlv c hc ⟨hf, fs, hfs, i, true, hm, by simp [hv], hd⟩
  have els : ∀ i, (∃ fs, kidTable kExpr (r.tag g) (r.nobjs g) = some fs ∧ (i, kLevels, true) ∈ fs) →
      r.fits g = true → r.levelsIn g (r.fld g i) ls = r.levelsIn g (r.fld g i) ls' :=
    fun i ⟨fs, hfs, hm⟩ hf => levelsIn_congr fun c hc hv hd => hls c hc ⟨hf, fs, hfs, i, true, hm, by simp [hv], hd⟩
  unfold exprNode
  split
  · split
    all_goals first
      | rfl
      | simp (disch := simp_all [kidTable_expr, exprKids]) only [eex, enm, elv, els]
  · rfl


/-! ## A node fails where an object it leads to fails -/

theorem nameIn_kid_none {r : Region} {g : Nat} {v : UInt64} {sub : (c : Nat) → c < g → Option Name}
    {c : Nat} (hv : ¬ v = 1) (hd : r.down g v = some c) (hn : ∀ h, sub c h = none) :
    r.nameIn g v sub = none := by
  unfold Region.nameIn
  simp only [hv, beq_iff_eq, ite_false]
  split
  · rename_i c' heq; rw [hd] at heq; cases heq; exact hn _
  · rfl

theorem levelIn_kid_none {r : Region} {g : Nat} {v : UInt64} {sub : (c : Nat) → c < g → Option Level}
    {c : Nat} (hv : ¬ v = 1) (hd : r.down g v = some c) (hn : ∀ h, sub c h = none) :
    r.levelIn g v sub = none := by
  unfold Region.levelIn
  simp only [hv, beq_iff_eq, ite_false]
  split
  · rename_i c' heq; rw [hd] at heq; cases heq; exact hn _
  · rfl

theorem levelsIn_kid_none {r : Region} {g : Nat} {v : UInt64}
    {sub : (c : Nat) → c < g → Option (List Level)}
    {c : Nat} (hv : ¬ v = 1) (hd : r.down g v = some c) (hn : ∀ h, sub c h = none) :
    r.levelsIn g v sub = none := by
  unfold Region.levelsIn
  simp only [hv, beq_iff_eq, ite_false]
  split
  · rename_i c' heq; rw [hd] at heq; cases heq; exact hn _
  · rfl

theorem exprIn_kid_none {r : Region} {g : Nat} {v : UInt64} {sub : (c : Nat) → c < g → Option Expr}
    {c : Nat} (hd : r.down g v = some c) (hn : ∀ h, sub c h = none) :
    r.exprIn g v sub = none := by
  unfold Region.exprIn
  split
  · rename_i c' heq; rw [hd] at heq; cases heq; exact hn _
  · rfl

set_option linter.unusedSimpArgs false in
theorem nameNode_kid_nm {r : Region} {g c : Nat} (nm : (c : Nat) → c < g → Option Name)
    (hk : Kid r kName g kName c) (hn : ∀ h, nm c h = none) : nameNode r g nm = none := by
  obtain ⟨hf, fs, hfs, i, nil, hm, hne, hd⟩ := hk
  unfold nameNode
  simp only [hf, ite_true]
  split
  all_goals first
    | rfl
    | (rename_i ht hn'
       simp only [kidTable_name, nameKids, ht, hn', Option.some.injEq] at hfs
       subst hfs
       simp (config := {decide := true}) only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
         or_false, kName, kLevel, kExpr, kLevels, false_and, and_false, true_and, false_or] at hm
       all_goals rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       all_goals subst_vars
       all_goals simp at hne
       all_goals simp [nameIn_kid_none, levelIn_kid_none, levelsIn_kid_none, exprIn_kid_none,
         hd, hn, hne])

set_option linter.unusedSimpArgs false in
theorem levelNode_kid_lv {r : Region} {g c : Nat} (lv : (c : Nat) → c < g → Option Level) (nm : (c : Nat) → c < g → Option Name)
    (hk : Kid r kLevel g kLevel c) (hn : ∀ h, lv c h = none) : levelNode r g lv nm = none := by
  obtain ⟨hf, fs, hfs, i, nil, hm, hne, hd⟩ := hk
  unfold levelNode
  simp only [hf, ite_true]
  split
  all_goals first
    | rfl
    | (rename_i ht hn'
       simp only [kidTable_level, levelKids, ht, hn', Option.some.injEq] at hfs
       subst hfs
       simp (config := {decide := true}) only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
         or_false, kName, kLevel, kExpr, kLevels, false_and, and_false, true_and, false_or] at hm
       all_goals rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       all_goals subst_vars
       all_goals simp at hne
       all_goals simp [nameIn_kid_none, levelIn_kid_none, levelsIn_kid_none, exprIn_kid_none,
         hd, hn, hne])

set_option linter.unusedSimpArgs false in
theorem levelNode_kid_nm {r : Region} {g c : Nat} (lv : (c : Nat) → c < g → Option Level) (nm : (c : Nat) → c < g → Option Name)
    (hk : Kid r kLevel g kName c) (hn : ∀ h, nm c h = none) : levelNode r g lv nm = none := by
  obtain ⟨hf, fs, hfs, i, nil, hm, hne, hd⟩ := hk
  unfold levelNode
  simp only [hf, ite_true]
  split
  all_goals first
    | rfl
    | (rename_i ht hn'
       simp only [kidTable_level, levelKids, ht, hn', Option.some.injEq] at hfs
       subst hfs
       simp (config := {decide := true}) only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
         or_false, kName, kLevel, kExpr, kLevels, false_and, and_false, true_and, false_or] at hm
       all_goals rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       all_goals subst_vars
       all_goals simp at hne
       all_goals simp [nameIn_kid_none, levelIn_kid_none, levelsIn_kid_none, exprIn_kid_none,
         hd, hn, hne])

set_option linter.unusedSimpArgs false in
theorem levelsNode_kid_ls {r : Region} {g c : Nat} (ls : (c : Nat) → c < g → Option (List Level)) (lv : (c : Nat) → c < g → Option Level)
    (hk : Kid r kLevels g kLevels c) (hn : ∀ h, ls c h = none) : levelsNode r g ls lv = none := by
  obtain ⟨hf, fs, hfs, i, nil, hm, hne, hd⟩ := hk
  unfold levelsNode
  simp only [hf, ite_true]
  split
  all_goals first
    | rfl
    | (rename_i ht hn'
       simp only [kidTable_levels, levelsKids, ht, hn', Option.some.injEq] at hfs
       subst hfs
       simp (config := {decide := true}) only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
         or_false, kName, kLevel, kExpr, kLevels, false_and, and_false, true_and, false_or] at hm
       all_goals rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       all_goals subst_vars
       all_goals simp at hne
       all_goals simp [nameIn_kid_none, levelIn_kid_none, levelsIn_kid_none, exprIn_kid_none,
         hd, hn, hne])

set_option linter.unusedSimpArgs false in
theorem levelsNode_kid_lv {r : Region} {g c : Nat} (ls : (c : Nat) → c < g → Option (List Level)) (lv : (c : Nat) → c < g → Option Level)
    (hk : Kid r kLevels g kLevel c) (hn : ∀ h, lv c h = none) : levelsNode r g ls lv = none := by
  obtain ⟨hf, fs, hfs, i, nil, hm, hne, hd⟩ := hk
  unfold levelsNode
  simp only [hf, ite_true]
  split
  all_goals first
    | rfl
    | (rename_i ht hn'
       simp only [kidTable_levels, levelsKids, ht, hn', Option.some.injEq] at hfs
       subst hfs
       simp (config := {decide := true}) only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
         or_false, kName, kLevel, kExpr, kLevels, false_and, and_false, true_and, false_or] at hm
       all_goals rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       all_goals subst_vars
       all_goals simp at hne
       all_goals simp [nameIn_kid_none, levelIn_kid_none, levelsIn_kid_none, exprIn_kid_none,
         hd, hn, hne])

set_option linter.unusedSimpArgs false in
theorem exprNode_kid_ex {r : Region} {g c : Nat} (ex : (c : Nat) → c < g → Option Expr) (nm : (c : Nat) → c < g → Option Name) (lv : (c : Nat) → c < g → Option Level) (ls : (c : Nat) → c < g → Option (List Level))
    (hk : Kid r kExpr g kExpr c) (hn : ∀ h, ex c h = none) : exprNode r g ex nm lv ls = none := by
  obtain ⟨hf, fs, hfs, i, nil, hm, hne, hd⟩ := hk
  unfold exprNode
  simp only [hf, ite_true]
  split
  all_goals first
    | rfl
    | (rename_i ht hn'
       simp only [kidTable_expr, exprKids, ht, hn', Option.some.injEq] at hfs
       subst hfs
       simp (config := {decide := true}) only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
         or_false, kName, kLevel, kExpr, kLevels, false_and, and_false, true_and, false_or] at hm
       all_goals rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       all_goals subst_vars
       all_goals simp at hne
       all_goals simp [nameIn_kid_none, levelIn_kid_none, levelsIn_kid_none, exprIn_kid_none,
         hd, hn, hne])

set_option linter.unusedSimpArgs false in
theorem exprNode_kid_nm {r : Region} {g c : Nat} (ex : (c : Nat) → c < g → Option Expr) (nm : (c : Nat) → c < g → Option Name) (lv : (c : Nat) → c < g → Option Level) (ls : (c : Nat) → c < g → Option (List Level))
    (hk : Kid r kExpr g kName c) (hn : ∀ h, nm c h = none) : exprNode r g ex nm lv ls = none := by
  obtain ⟨hf, fs, hfs, i, nil, hm, hne, hd⟩ := hk
  unfold exprNode
  simp only [hf, ite_true]
  split
  all_goals first
    | rfl
    | (rename_i ht hn'
       simp only [kidTable_expr, exprKids, ht, hn', Option.some.injEq] at hfs
       subst hfs
       simp (config := {decide := true}) only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
         or_false, kName, kLevel, kExpr, kLevels, false_and, and_false, true_and, false_or] at hm
       all_goals rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       all_goals subst_vars
       all_goals simp at hne
       all_goals simp [nameIn_kid_none, levelIn_kid_none, levelsIn_kid_none, exprIn_kid_none,
         hd, hn, hne])

set_option linter.unusedSimpArgs false in
theorem exprNode_kid_lv {r : Region} {g c : Nat} (ex : (c : Nat) → c < g → Option Expr) (nm : (c : Nat) → c < g → Option Name) (lv : (c : Nat) → c < g → Option Level) (ls : (c : Nat) → c < g → Option (List Level))
    (hk : Kid r kExpr g kLevel c) (hn : ∀ h, lv c h = none) : exprNode r g ex nm lv ls = none := by
  obtain ⟨hf, fs, hfs, i, nil, hm, hne, hd⟩ := hk
  unfold exprNode
  simp only [hf, ite_true]
  split
  all_goals first
    | rfl
    | (rename_i ht hn'
       simp only [kidTable_expr, exprKids, ht, hn', Option.some.injEq] at hfs
       subst hfs
       simp (config := {decide := true}) only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
         or_false, kName, kLevel, kExpr, kLevels, false_and, and_false, true_and, false_or] at hm
       all_goals rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       all_goals subst_vars
       all_goals simp at hne
       all_goals simp [nameIn_kid_none, levelIn_kid_none, levelsIn_kid_none, exprIn_kid_none,
         hd, hn, hne])

set_option linter.unusedSimpArgs false in
theorem exprNode_kid_ls {r : Region} {g c : Nat} (ex : (c : Nat) → c < g → Option Expr) (nm : (c : Nat) → c < g → Option Name) (lv : (c : Nat) → c < g → Option Level) (ls : (c : Nat) → c < g → Option (List Level))
    (hk : Kid r kExpr g kLevels c) (hn : ∀ h, ls c h = none) : exprNode r g ex nm lv ls = none := by
  obtain ⟨hf, fs, hfs, i, nil, hm, hne, hd⟩ := hk
  unfold exprNode
  simp only [hf, ite_true]
  split
  all_goals first
    | rfl
    | (rename_i ht hn'
       simp only [kidTable_expr, exprKids, ht, hn', Option.some.injEq] at hfs
       subst hfs
       simp (config := {decide := true}) only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil,
         or_false, kName, kLevel, kExpr, kLevels, false_and, and_false, true_and, false_or] at hm
       all_goals rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
       all_goals subst_vars
       all_goals simp at hne
       all_goals simp [nameIn_kid_none, levelIn_kid_none, levelsIn_kid_none, exprIn_kid_none,
         hd, hn, hne])


/-! ## The specification's reading -/

theorem kinds_ne : kName ≠ kLevel ∧ kName ≠ kExpr ∧ kName ≠ kLevels ∧ kLevel ≠ kExpr ∧
    kLevel ≠ kLevels ∧ kExpr ≠ kLevels := by decide

theorem KindOK.name {r : Region} {c : Nat} (h : (nameAt r c).isSome) : KindOK r kName c :=
  ⟨fun _ => h, fun e => absurd e kinds_ne.1, fun e => absurd e kinds_ne.2.2.1,
   fun e => absurd e kinds_ne.2.1⟩
theorem KindOK.level {r : Region} {c : Nat} (h : (levelAt r c).isSome) : KindOK r kLevel c :=
  ⟨fun e => absurd e.symm kinds_ne.1, fun _ => h, fun e => absurd e kinds_ne.2.2.2.2.1,
   fun e => absurd e kinds_ne.2.2.2.1⟩
theorem KindOK.levels {r : Region} {c : Nat} (h : (levelsAt r c).isSome) : KindOK r kLevels c :=
  ⟨fun e => absurd e.symm kinds_ne.2.2.1, fun e => absurd e.symm kinds_ne.2.2.2.2.1, fun _ => h,
   fun e => absurd e.symm kinds_ne.2.2.2.2.2⟩
theorem KindOK.expr {r : Region} {c : Nat} (h : (exprAt r c).isSome) : KindOK r kExpr c :=
  ⟨fun e => absurd e.symm kinds_ne.2.1, fun e => absurd e.symm kinds_ne.2.2.2.1,
   fun e => absurd e kinds_ne.2.2.2.2.2, fun _ => h⟩

theorem isSome_of_none_ne {α : Type} {o : Option α} (h : ¬ o = none) : o.isSome := by
  cases o <;> simp_all

theorem Kid.name_kind {r : Region} {g c : Nat} {k' : UInt8} (h : Kid r kName g k' c) :
    k' = kName := by
  obtain ⟨_, fs, hfs, i, nil, hm, _, _⟩ := h
  rw [kidTable_name] at hfs; unfold nameKids at hfs
  split at hfs <;> simp only [reduceCtorEq, Option.some.injEq] at hfs <;> subst hfs <;> simp_all

theorem Kid.level_kind {r : Region} {g c : Nat} {k' : UInt8} (h : Kid r kLevel g k' c) :
    k' = kLevel ∨ k' = kName := by
  obtain ⟨_, fs, hfs, i, nil, hm, _, _⟩ := h
  rw [kidTable_level] at hfs; unfold levelKids at hfs
  split at hfs <;> simp only [reduceCtorEq, Option.some.injEq] at hfs <;> subst hfs <;> simp at hm <;>
    first | simp [hm] | (rcases hm with hm | hm <;> simp [hm])

theorem Kid.levels_kind {r : Region} {g c : Nat} {k' : UInt8} (h : Kid r kLevels g k' c) :
    k' = kLevels ∨ k' = kLevel := by
  obtain ⟨_, fs, hfs, i, nil, hm, _, _⟩ := h
  rw [kidTable_levels] at hfs; unfold levelsKids at hfs
  split at hfs <;> simp only [reduceCtorEq, Option.some.injEq] at hfs <;> subst hfs <;> simp at hm <;>
    first | simp [hm] | (rcases hm with hm | hm <;> simp [hm])

/-- **An object the specification reads leads to objects it reads.** -/
theorem KindOK.kid {r : Region} {k : UInt8} {g : Nat} (hk : IsKind k) (h : KindOK r k g)
    {k' : UInt8} {c : Nat} (hkid : Kid r k g k' c) : KindOK r k' c := by
  rcases hk with rfl | rfl | rfl | rfl
  · have hg := h.1 rfl
    obtain rfl := hkid.name_kind
    refine KindOK.name (isSome_of_none_ne fun e => ?_)
    rw [nameAt, nameNode_kid_nm _ hkid (fun _ => e)] at hg; cases hg
  · have hg := h.2.1 rfl
    rcases hkid.level_kind with rfl | rfl
    · refine KindOK.level (isSome_of_none_ne fun e => ?_)
      rw [levelAt, levelNode_kid_lv _ _ hkid (fun _ => e)] at hg; cases hg
    · refine KindOK.name (isSome_of_none_ne fun e => ?_)
      rw [levelAt, levelNode_kid_nm _ _ hkid (fun _ => e)] at hg; cases hg
  · have hg := h.2.2.2 rfl
    have hk' := hkid.kind
    rcases hk' with rfl | rfl | rfl | rfl
    · refine KindOK.name (isSome_of_none_ne fun e => ?_)
      rw [exprAt, exprNode_kid_nm _ _ _ _ hkid (fun _ => e)] at hg; cases hg
    · refine KindOK.level (isSome_of_none_ne fun e => ?_)
      rw [exprAt, exprNode_kid_lv _ _ _ _ hkid (fun _ => e)] at hg; cases hg
    · refine KindOK.expr (isSome_of_none_ne fun e => ?_)
      rw [exprAt, exprNode_kid_ex _ _ _ _ hkid (fun _ => e)] at hg; cases hg
    · refine KindOK.levels (isSome_of_none_ne fun e => ?_)
      rw [exprAt, exprNode_kid_ls _ _ _ _ hkid (fun _ => e)] at hg; cases hg
  · have hg := h.2.2.1 rfl
    rcases hkid.levels_kind with rfl | rfl
    · refine KindOK.levels (isSome_of_none_ne fun e => ?_)
      rw [levelsAt, levelsNode_kid_ls _ _ hkid (fun _ => e)] at hg; cases hg
    · refine KindOK.level (isSome_of_none_ne fun e => ?_)
      rw [levelsAt, levelsNode_kid_lv _ _ hkid (fun _ => e)] at hg; cases hg

/-- **Where the marking fails, the specification fails.** -/
theorem KindOK.markOK {r : Region} {k : UInt8} {g : Nat} (hk : IsKind k) (h : KindOK r k g) :
    MarkOK r k g := by
  apply Classical.byContradiction
  intro hm
  rcases hk with rfl | rfl | rfl | rfl
  · have hg := h.1 rfl; rw [nameAt, nameNode_none hm] at hg; cases hg
  · have hg := h.2.1 rfl; rw [levelAt, levelNode_none hm] at hg; cases hg
  · have hg := h.2.2.2 rfl; rw [exprAt, exprNode_none hm] at hg; cases hg
  · have hg := h.2.2.1 rfl; rw [levelsAt, levelsNode_none hm] at hg; cases hg

end ConLeche.Frontend.Olean
