module

public import ConLeche.Verify.Ground.SimState
import ConLeche.Verify.Ground.SimBridge

public section

/-!
# The simulation relation across program growth (task #423 soundness, layer (d), item 2(c))

A compile grows one side's program, or both (`ExtR`, the site's words kept).
Every relation is about keys, so it survives; the sharing slots need the
argument that an owner one side adds later reads empty on both sides
(`SlotRel.ext`): a set slot has an old owner on both sides (`SlotRel`'s
second and third clauses), and owners are unique per slot and, across the
two sides, per key.
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable {j : Nat} {N : Name → Prop} {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}
  {PA PB PA' PB' : G4Prog}

/-- Slot owners survive growth. -/
theorem SlotOwn.fwd {P P' : G4Prog} (hx : ExtR P P') {sl : Nat} {x : Expr ⊕ Nat}
    (h : SlotOwn P sl x) : SlotOwn P' sl x := by
  cases x with
  | inl a =>
    obtain ⟨o, h₁, h₂⟩ := h
    exact ⟨o, hx.closedNode a o h₁, hx.code_some h₂⟩
  | inr k =>
    show P'.kSlot[k]? = some sl
    rw [hx.kSlot k (lt_of_some h)]; exact h

theorem OwnRel.ext (hA : ExtR PA PA') (hB : ExtR PB PB') {x y : Expr ⊕ Nat}
    (h : OwnRel PA PB x y) : OwnRel PA' PB' x y := by
  rcases x with a | k <;> rcases y with b | kB <;> simp only [OwnRel] at h ⊢
  · exact h
  · exact h.ext hA hB

/-- **The slots across growth** of either side. -/
theorem SlotRel.ext (hA : ExtR PA PA') (hB : ExtR PB PB') (hIA : CompInv f₁ p₁ PA')
    (hIB : CompInv f₂ p₂ PB') (eA : PA'.epBase = PA.epBase) (eB : PB'.epBase = PB.epBase)
    {sa sb : Array Nat} (h : SlotRel PA PB sa sb) : SlotRel PA' PB' sa sb := by
  rw [SlotRel, eA, eB]
  refine ⟨fun slA slB x y hoA hoB r => ?_, fun slA hne => ?_, fun slB hne => ?_⟩
  · -- a nonzero read on either side names old owners on both
    have old : SlotOwn PA slA x ∧ SlotOwn PB slB y ∧ OwnRel PA PB x y →
        g4SlotGet sb PB.epBase slB = g4SlotGet sa PA.epBase slA :=
      fun ⟨h₁, h₂, h₃⟩ => h.1 _ _ _ _ h₁ h₂ h₃
    by_cases za : g4SlotGet sa PA.epBase slA = 0
    · by_cases zb : g4SlotGet sb PB.epBase slB = 0
      · rw [za, zb]
      · obtain ⟨x', slA', y', h₁, h₂, h₃⟩ := h.2.2 slB zb
        obtain rfl := hIB.slotUniq _ _ _ (h₂.fwd hB) hoB
        obtain rfl := OwnRel.slot_eqA hIA hIB hoA (h₁.fwd hA) r (h₃.ext hA hB)
        obtain rfl := hIA.slotUniq _ _ _ (h₁.fwd hA) hoA
        exact old ⟨h₁, h₂, h₃⟩
    · obtain ⟨x', slB', y', h₁, h₂, h₃⟩ := h.2.1 slA za
      obtain rfl := hIA.slotUniq _ _ _ (h₁.fwd hA) hoA
      obtain rfl := OwnRel.slot_eqB hIA hIB hoB (h₂.fwd hB) r (h₃.ext hA hB)
      obtain rfl := hIB.slotUniq _ _ _ (h₂.fwd hB) hoB
      exact old ⟨h₁, h₂, h₃⟩
  · obtain ⟨x, slB, y, h₁, h₂, h₃⟩ := h.2.1 slA hne
    exact ⟨x, slB, y, h₁.fwd hA, h₂.fwd hB, h₃.ext hA hB⟩
  · obtain ⟨x, slA, y, h₁, h₂, h₃⟩ := h.2.2 slB hne
    exact ⟨x, slA, y, h₁.fwd hA, h₂.fwd hB, h₃.ext hA hB⟩

theorem RegRel.ext {sA sB : MS} (hA : ExtR sA.P PA') (hB : ExtR sB.P PB')
    (h : RegRel N f₁ p₁ f₂ p₂ sA sB) :
    RegRel N f₁ p₁ f₂ p₂ { sA with P := PA' } { sB with P := PB' } := by
  obtain ⟨he, hg⟩ := h
  refine ⟨he, ?_⟩
  dsimp only
  rcases hmd : sA.mode with _ | _ | _ | _ | _ | md <;> simp only [hmd] at hg ⊢
  · exact ⟨hg.1, hg.2.ext hA hB⟩
  · exact hg
  · exact hg
  · exact ⟨hg.1, hg.2.ext hA hB⟩
  · obtain ⟨hx, t, hN, h₁, h₂⟩ := hg
    exact ⟨hx, t, hN, h₁.extR hA, h₂.extR hB⟩
  · exact hg

/-! ## Lock-step: one set of compiled bodies -/

/-- An entry's key is compiled exactly when the entry's body is. -/
theorem codeK_iff {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P : G4Prog}
    (hI : CompInv f p P) {k : Nat} {i : G4Info} (hi : P.kInfo[k]? = some i) :
    CodeK P (infoKey i) ↔ P.kCode[k]! ≠ 0 := by
  constructor
  · rintro ⟨k', i', hi', hk, hc⟩
    have e := hI.kMapAll _ _ hi; have e' := hI.kMapAll _ _ hi'
    rw [hk, e] at e'; cases e'; exact hc
  · exact fun hc => ⟨k, i, hi, rfl, hc⟩

/-- A recursor entry's rule is compiled exactly when its row is. -/
theorem ruleK_iff {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P : G4Prog}
    (hI : CompInv f p P) {k : Nat} {c : Name} {lps : List Name} {us : List Level} {mI rP base nr : Nat}
    {isK isEta : Bool} (hi : P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta)) {d : Nat}
    (hd : d < nr) : RuleK P (c, us) d ↔ P.ruleCode[base + d]! ≠ 0 := by
  constructor
  · rintro ⟨k', c', lps', us', mI', rP', base', nr', isK', isEta', hi', hk, -, hc⟩
    have e := hI.kMapAll _ _ hi; have e' := hI.kMapAll _ _ hi'
    simp only [infoKey] at e e'
    rw [hk, e] at e'; cases e'
    rw [hi] at hi'; cases hi'; exact hc
  · exact fun hc => ⟨k, c, lps, us, mI, rP, base, nr, isK, isEta, hi, rfl, hd, hc⟩

/-- An extension compiles no key. -/
theorem codeK_ext {P P' : G4Prog} (hx : Ext P P') (κ : Name × List Level) : CodeK P' κ ↔ CodeK P κ := by
  constructor
  · rintro ⟨k, i, hi, hk, hc⟩
    rcases Nat.lt_or_ge k P.kInfo.size with h | h
    · refine ⟨k, i, by rw [← hx.kInfo k h]; exact hi, hk, ?_⟩
      rwa [getElem!_def, ← hx.kCode k h, ← getElem!_def]
    · exact absurd (hx.kCodeNew k h (lt_of_some hi)) hc
  · rintro ⟨k, i, hi, hk, hc⟩
    have h := lt_of_some hi
    refine ⟨k, i, by rw [hx.kInfo k h]; exact hi, hk, ?_⟩
    rwa [getElem!_def, hx.kCode k h, ← getElem!_def]

/-- An extension compiles no rule. -/
theorem ruleK_ext {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P P' : G4Prog}
    (hI : TabInv f p P) (hx : Ext P P') (κ : Name × List Level) (d : Nat) :
    RuleK P' κ d ↔ RuleK P κ d := by
  constructor
  · rintro ⟨k, c, lps, us, mI, rP, base, nr, isK, isEta, hi, hk, hd, hc⟩
    rcases Nat.lt_or_ge k P.kInfo.size with h | h
    · rw [hx.kInfo k h] at hi
      have hr := hI.rows_lt (r := base + d) ⟨c, lps, us, mI, rP, base, nr, isK, isEta, hi, Nat.le_add_right _ _, by omega⟩
      refine ⟨k, c, lps, us, mI, rP, base, nr, isK, isEta, hi, hk, hd, ?_⟩
      rwa [getElem!_def, ← hx.ruleCode _ hr, ← getElem!_def]
    · exact absurd (hx.recRowsNew k h c lps us mI rP base nr isK isEta hi d hd).2 hc
  · rintro ⟨k, c, lps, us, mI, rP, base, nr, isK, isEta, hi, hk, hd, hc⟩
    have hr := hI.rows_lt (r := base + d) ⟨c, lps, us, mI, rP, base, nr, isK, isEta, hi, Nat.le_add_right _ _, by omega⟩
    refine ⟨k, c, lps, us, mI, rP, base, nr, isK, isEta, by rw [hx.kInfo k (lt_of_some hi)]; exact hi,
      hk, hd, ?_⟩
    rwa [getElem!_def, hx.ruleCode _ hr, ← getElem!_def]

/-- Lock-step survives an extension of both programs. -/
theorem CodeSame.ext {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}
    {PA PB : G4Prog} (h : CodeSame PA PB) (hIA : TabInv f₁ p₁ PA) (hIB : TabInv f₂ p₂ PB)
    (hA : Ext PA PA') (hB : Ext PB PB') : CodeSame PA' PB' :=
  ⟨fun κ => (codeK_ext hB κ).trans ((h.1 κ).trans (codeK_ext hA κ).symm),
    fun κ d => (ruleK_ext hIB hB κ d).trans ((h.2 κ d).trans (ruleK_ext hIA hA κ d).symm)⟩

/-- Storing a body adds its entry's key. -/
theorem codeK_set {P : G4Prog} {k w : Nat} (hk : k < P.kCode.size) (hw : w ≠ 0) {i : G4Info}
    (hi : P.kInfo[k]? = some i) (κ : Name × List Level) :
    CodeK { P with kCode := P.kCode.set! k w } κ ↔ CodeK P κ ∨ infoKey i = κ := by
  constructor
  · rintro ⟨k', i', hi', hκ, hc⟩
    by_cases e : k' = k
    · subst e; rw [hi] at hi'; cases hi'; exact .inr hκ
    · refine .inl ⟨k', i', hi', hκ, ?_⟩
      rwa [getElem!_def, ← set!_get?_ne e, ← getElem!_def]
  · rintro (⟨k', i', hi', hκ, hc⟩ | hκ)
    · refine ⟨k', i', hi', hκ, ?_⟩
      by_cases e : k' = k
      · subst e; dsimp only; rw [get!_of_some (set!_get?_self hk)]; exact hw
      · dsimp only; rwa [getElem!_def, set!_get?_ne e, ← getElem!_def]
    · refine ⟨k, i, hi, hκ, ?_⟩
      dsimp only; rw [get!_of_some (set!_get?_self hk)]; exact hw

/-- Storing a rule's right-hand side adds its recursor's key and index. -/
theorem ruleK_set {f : Name → Option ConstantInfo} {p : Name → Nat → Option ProjEntry} {P : G4Prog}
    (hI : TabInv f p P) {k : Nat} {c : Name} {lps : List Name} {us : List Level} {mI rP base nr : Nat}
    {isK isEta : Bool} (hi : P.kInfo[k]? = some (.recr c lps us mI rP base nr isK isEta)) {d w : Nat}
    (hd : d < nr) (hr : base + d < P.ruleCode.size) (hw : w ≠ 0) (κ : Name × List Level) (d' : Nat) :
    RuleK { P with ruleCode := P.ruleCode.set! (base + d) w } κ d' ↔ RuleK P κ d' ∨ ((c, us) = κ ∧ d' = d) := by
  constructor
  · rintro ⟨k', c', lps', us', mI', rP', base', nr', isK', isEta', hi', hκ, hd', hc⟩
    by_cases e : base' + d' = base + d
    · have := hI.rowsDisj k k' (base + d) ⟨_, _, _, _, _, _, _, _, _, hi, Nat.le_add_right _ _, by omega⟩
        ⟨_, _, _, _, _, _, _, _, _, hi', by omega, by omega⟩
      subst this; rw [hi] at hi'; cases hi'
      exact .inr ⟨hκ, by omega⟩
    · refine .inl ⟨k', c', lps', us', mI', rP', base', nr', isK', isEta', hi', hκ, hd', ?_⟩
      rwa [getElem!_def, ← set!_get?_ne e, ← getElem!_def]
  · rintro (⟨k', c', lps', us', mI', rP', base', nr', isK', isEta', hi', hκ, hd', hc⟩ | ⟨hκ, rfl⟩)
    · refine ⟨k', c', lps', us', mI', rP', base', nr', isK', isEta', hi', hκ, hd', ?_⟩
      by_cases e : base' + d' = base + d
      · dsimp only; rw [e, get!_of_some (set!_get?_self hr)]; exact hw
      · dsimp only; rwa [getElem!_def, set!_get?_ne e, ← getElem!_def]
    · refine ⟨k, c, lps, us, mI, rP, base, nr, isK, isEta, hi, hκ, hd, ?_⟩
      dsimp only; rw [get!_of_some (set!_get?_self hr)]; exact hw

/-- In lock-step, two entries of one key have a body on both sides or on neither. -/
theorem CodeSame.code_iff {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}
    {PA PB : G4Prog} (h : CodeSame PA PB) (hIA : CompInv f₁ p₁ PA) (hIB : CompInv f₂ p₂ PB)
    {kA kB : Nat} {iA iB : G4Info} (hiA : PA.kInfo[kA]? = some iA) (hiB : PB.kInfo[kB]? = some iB)
    (hk : infoKey iA = infoKey iB) : PA.kCode[kA]! = 0 ↔ PB.kCode[kB]! = 0 := by
  have e := (codeK_iff hIB hiB).symm.trans ((h.1 _).trans (hk ▸ codeK_iff hIA hiA))
  have := not_congr e
  simp only [ne_eq, Classical.not_not] at this
  exact this.symm

/-- In lock-step, two recursor entries of one key have rule `d` compiled on
both sides or on neither. -/
theorem CodeSame.rule_iff {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}
    {PA PB : G4Prog} (h : CodeSame PA PB) (hIA : CompInv f₁ p₁ PA) (hIB : CompInv f₂ p₂ PB)
    {kA kB : Nat} {c : Name} {lps lps' : List Name} {us : List Level} {mI rP bA nA mI' rP' bB nB : Nat}
    {isK isEta isK' isEta' : Bool}
    (hiA : PA.kInfo[kA]? = some (.recr c lps us mI rP bA nA isK isEta))
    (hiB : PB.kInfo[kB]? = some (.recr c lps' us mI' rP' bB nB isK' isEta')) {d : Nat} (hdA : d < nA)
    (hdB : d < nB) : PA.ruleCode[bA + d]! = 0 ↔ PB.ruleCode[bB + d]! = 0 := by
  have e := (ruleK_iff hIB hiB hdB).symm.trans ((h.2 _ d).trans (ruleK_iff hIA hiA hdA))
  have := not_congr e
  simp only [ne_eq, Classical.not_not] at this
  exact this.symm

/-- **The simulation relation across growth** of either program, the
site's words kept. -/
theorem MRel.ext {sA sB : MS} (h : MRel j N f₁ p₁ f₂ p₂ sA sB) (hA : ExtR sA.P PA') (hB : ExtR sB.P PB')
    (hIA : Inv f₁ p₁ PA') (hIB : Inv f₂ p₂ PB') (sA' : PA'.site = sA.P.site) (sB' : PB'.site = sB.P.site)
    (hc : j = 0 → CodeSame PA' PB') :
    MRel j N f₁ p₁ f₂ p₂ { sA with P := PA' } { sB with P := PB' } := by
  simp only [G4Prog.site, Prod.mk.injEq] at sA' sB'
  have fA := hA.flags; have fB := hB.flags
  simp only [G4Prog.flags, Prod.mk.injEq] at fA fB
  exact {
    invA := hIA
    invB := hIB
    natOk := fun hn => by dsimp only; rw [fA.1, fB.1, h.natOk hn]
    strOk := fun hn => by dsimp only; rw [fA.2.1, fB.2.1, h.strOk hn]
    maxNat := by dsimp only; rw [fA.2.2, fB.2.2, h.maxNat]
    kTrue := by dsimp only; rw [sA'.1, sB'.1]; exact h.kTrue.ext hA hB
    kFalse := by dsimp only; rw [sA'.2.1, sB'.2.1]; exact h.kFalse.ext hA hB
    kZero := by dsimp only; rw [sA'.2.2.1, sB'.2.2.1]; exact h.kZero.ext hA hB
    kSucc := by dsimp only; rw [sA'.2.2.2.1, sB'.2.2.2.1]; exact h.kSucc.ext hA hB
    cel := h.cel.ext hA hB
    val := h.val.ext hA hB
    ev := h.ev
    argA := h.argA
    fs := h.fs.ext hA hB
    mem := h.mem.ext hA hB
    memoA := h.memoA
    memoB := h.memoB
    slots := h.slots.ext hA hB hIA.toCompInv hIB.toCompInv sA'.2.2.2.2.1 sB'.2.2.2.2.1
    mode := h.mode
    st := h.st
    regs := h.regs.ext hA hB
    code := hc }

end

end ConLeche.Verify.Ground
