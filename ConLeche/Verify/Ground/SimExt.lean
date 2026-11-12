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
variable {N : Name → Prop} {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}
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

/-- **The simulation relation across growth** of either program, the
site's words kept. -/
theorem MRel.ext {sA sB : MS} (h : MRel N f₁ p₁ f₂ p₂ sA sB) (hA : ExtR sA.P PA') (hB : ExtR sB.P PB')
    (hIA : Inv f₁ p₁ PA') (hIB : Inv f₂ p₂ PB') (sA' : PA'.site = sA.P.site) (sB' : PB'.site = sB.P.site) :
    MRel N f₁ p₁ f₂ p₂ { sA with P := PA' } { sB with P := PB' } := by
  simp only [G4Prog.site, Prod.mk.injEq] at sA' sB'
  have fA := hA.flags; have fB := hB.flags
  simp only [G4Prog.flags, Prod.mk.injEq] at fA fB
  exact {
    invA := hIA
    invB := hIB
    natOk := by dsimp only; rw [fA.1, fB.1, h.natOk]
    strOk := by dsimp only; rw [fA.2.1, fB.2.1, h.strOk]
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
    regs := h.regs.ext hA hB }

end

end ConLeche.Verify.Ground
