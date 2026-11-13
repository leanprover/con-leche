module

public import ConLeche.Verify.Ground.SimState

public section

/-!
# Memo records and four-word frames on two sides (task #423 soundness, item 2(c))

The pieces mode 3 needs beyond the bridge: a memo record pushed on both
sides (`MemRel.push`), one memo answer on both sides (`MRel.memoFind`: the
records' words are one by `MemRel`, the keys one to one by `EntRel.iff`),
and the ι and literal-operation frames pushed on both sides.
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable {j : Nat} {N : Name → Prop} {f₁ f₂ : Name → Option ConstantInfo} {p₁ p₂ : Name → Nat → Option ProjEntry}
  {PA PB : G4Prog}

/-- **A new memo record** with related entries. -/
theorem MemRel.push {ma mb : Array Nat} (h : MemRel N PA PB ma mb) (h4 : ma.size % 4 = 0)
    {kA kB : Nat} (hk : ERel N PA PB kA kB) (s n c : Nat) :
    MemRel N PA PB ((((ma.push kA).push s).push n).push c) ((((mb.push kB).push s).push n).push c) := by
  have hs := h.1
  refine ⟨by simp [h.1], fun r hr => ?_⟩
  simp only [Array.size_push] at hr
  rcases Nat.lt_or_ge r (ma.size / 4) with hl | hl
  · obtain ⟨e₀, e₁, e₂, e₃⟩ := h.2 r hl
    rw [push4_get (a := ma) (by omega), push4_get (a := ma) (by omega), push4_get (a := ma) (by omega),
      push4_get (a := ma) (by omega), push4_get (a := mb) (by omega), push4_get (a := mb) (by omega),
      push4_get (a := mb) (by omega), push4_get (a := mb) (by omega)]
    exact ⟨e₀, e₁, e₂, e₃⟩
  · obtain rfl : r = ma.size / 4 := by omega
    have hb : mb.size % 4 = 0 := by rw [h.1]; exact h4
    obtain ⟨a₀, a₁, a₂, a₃⟩ := push4_new (a := ma) (w₀ := kA) (w₁ := s) (w₂ := n) (w₃ := c) h4
    obtain ⟨b₀, b₁, b₂, b₃⟩ := push4_new (a := mb) (w₀ := kB) (w₁ := s) (w₂ := n) (w₃ := c) hb
    rw [h.1] at b₀ b₁ b₂ b₃
    rw [a₀, a₁, a₂, a₃, b₀, b₁, b₂, b₃]
    exact ⟨hk, rfl, rfl, rfl⟩

/-- **One memo answer** on both sides: the records' words one, the keys one
to one. -/
theorem memoFind_rel (hIA : CompInv f₁ p₁ PA) (hIB : CompInv f₂ p₂ PB)
    {memA memB mTA mTB fs argA : Array Nat} (hm : MemRel N PA PB memA memB)
    (hA : MemoTab memA argA mTA) (hB : MemoTab memB argA mTB) {kA kB : Nat} (hk : ERel N PA PB kA kB)
    (n : Nat) :
    g4MemoFind memB mTB fs argA kB n mTB.size (g4Slot (g4Hash fs kB n 0 (UInt64.ofNat kB)) mTB.size) =
      g4MemoFind memA mTA fs argA kA n mTA.size (g4Slot (g4Hash fs kA n 0 (UInt64.ofNat kA)) mTA.size) := by
  refine (memoFind_agree hA hB hm.1.symm (fun r hr i h0 h4 => ?_) (fun r hr => ?_)).symm
  · obtain ⟨-, e₁, e₂, e₃⟩ := hm.2 r hr
    rw [g4X4_eq]
    rcases (show i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl
    · exact e₁.symm
    · exact e₂.symm
    · exact e₃.symm
  · rw [g4X4_eq]
    exact (EntRel.iff hIA hIB hk.1 (hm.2 r hr).1.1)

/-! ## Four-word frames -/

theorem push4_reads (a : Array Nat) (w₀ w₁ w₂ w₃ : Nat) :
    ((((a.push w₀).push w₁).push w₂).push w₃)[a.size]! = w₀ ∧
      ((((a.push w₀).push w₁).push w₂).push w₃)[a.size + 1]! = w₁ ∧
      ((((a.push w₀).push w₁).push w₂).push w₃)[a.size + 2]! = w₂ ∧
      ((((a.push w₀).push w₁).push w₂).push w₃)[a.size + 3]! = w₃ := by
  have g : ∀ (b : Array Nat) (x i : Nat), i = b.size → (b.push x)[i]! = x := by
    rintro b x i rfl; exact getElem!_push_eq' b x
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega), getElem!_push_eq']
  · rw [getElem!_push_lt' (by simp only [Array.size_push]; omega),
      getElem!_push_lt' (by simp only [Array.size_push]; omega), g _ _ _ (by simp)]
  · rw [getElem!_push_lt' (by simp only [Array.size_push]; omega), g _ _ _ (by simp)]
  · rw [g _ _ _ (by simp)]

theorem FS2.push4 {fa fb : Array Nat} {t : Nat} (h : FS2 N PA PB fa fb t) (ht : t ≤ fa.size)
    (hs : fb.size = fa.size) (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Nat) :
    FS2 N PA PB ((((fa.push a₀).push a₁).push a₂).push a₃) ((((fb.push b₀).push b₁).push b₂).push b₃) t :=
  h.congr (fun i hi => push4_get (by omega)) (fun i hi => push4_get (by omega))

/-- **Pushing an ι frame** (entry, span start, count, tag `3`) with related entries. -/
theorem FsRel.pushIota {fa fb : Array Nat} (h : FsRel N PA PB fa fb) {kA kB : Nat} (hk : ERel N PA PB kA kB)
    (s n : Nat) :
    FsRel N PA PB ((((fa.push kA).push s).push n).push 3) ((((fb.push kB).push s).push n).push 3) := by
  refine ⟨by simp [h.1], ?_⟩
  simp only [Array.size_push]
  obtain ⟨a₀, a₁, a₂, a₃⟩ := push4_reads fa kA s n 3
  obtain ⟨b₀, b₁, b₂, b₃⟩ := push4_reads fb kB s n 3
  rw [h.1] at b₀ b₁ b₂ b₃
  refine .iota (by rw [a₃, b₃]) (by rw [a₃]; decide) (by rw [a₀, b₀]; exact hk) (by rw [a₁, b₁])
    (by rw [a₂, b₂]) (h.2.push4 (Nat.le_refl _) h.1 _ _ _ _ _ _ _ _)

/-- **Pushing a literal-operation frame** (entry, two cells, tag `5`) with related entries. -/
theorem FsRel.pushNatA {fa fb : Array Nat} (h : FsRel N PA PB fa fb) {kA kB : Nat} (hk : ERel N PA PB kA kB)
    (a b : Nat) :
    FsRel N PA PB ((((fa.push kA).push a).push b).push 5) ((((fb.push kB).push a).push b).push 5) := by
  refine ⟨by simp [h.1], ?_⟩
  simp only [Array.size_push]
  obtain ⟨a₀, a₁, a₂, a₃⟩ := push4_reads fa kA a b 5
  obtain ⟨b₀, b₁, b₂, b₃⟩ := push4_reads fb kB a b 5
  rw [h.1] at b₀ b₁ b₂ b₃
  refine .natA (by rw [a₃, b₃]) (by rw [a₃]; decide) (by rw [a₀, b₀]; exact hk) (by rw [a₁, b₁])
    (by rw [a₂, b₂]) (h.2.push4 (Nat.le_refl _) h.1 _ _ _ _ _ _ _ _)

end

end ConLeche.Verify.Ground
