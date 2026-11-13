module

public import ConLeche.Verify.Ground.SimStep
import ConLeche.Verify.Ground.SimStep1
public import ConLeche.Verify.Ground.SimBridge
import ConLeche.Verify.Ground.SimMemo
import ConLeche.Verify.Ground.SimStep3
import ConLeche.Verify.Ground.Step1N
import ConLeche.Verify.Ground.Step1
import ConLeche.Verify.Ground.Step3

public section

/-!
# The step simulation, mode 1: the literal frames (task #423 soundness, layer (d), item 2(c))

The engine's reading of the returned value (`litRd`, `litM`) is one on both
sides (`MRel.lit`): a literal's word is one, a constructor's entry is
related, and the tests against `Nat.zero`/`Nat.succ` answer alike
(`ent_beq`).  The frame's entry is related (`FsRel.natATop`/`natBTop`), so
its operation word is one (`EntRel.defnW`, tag `3`).
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable {j : Nat} {N : Name → Prop} {PA PB : G4Prog}

/-- **Pushing a second literal frame** (entry, literal, two cells, tag `6`)
with related entries. -/
theorem FsRel.pushNatB {fa fb : Array Nat} (h : FsRel N PA PB fa fb) {kA kB : Nat}
    (hk : ERel N PA PB kA kB) (m a b : Nat) :
    FsRel N PA PB (((((fa.push kA).push m).push a).push b).push 6)
      (((((fb.push kB).push m).push a).push b).push 6) := by
  refine ⟨by simp [h.1], ?_⟩
  simp only [Array.size_push]
  obtain ⟨a₁, a₂, a₃, a₄⟩ := push4_reads (fa.push kA) m a b 6
  obtain ⟨b₁, b₂, b₃, b₄⟩ := push4_reads (fb.push kB) m a b 6
  simp only [Array.size_push] at a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
  rw [h.1] at b₁ b₂ b₃ b₄
  have a₀ : (((((fa.push kA).push m).push a).push b).push 6)[fa.size]! = kA := by
    rw [push4_get (by simp), getElem!_push_eq']
  have b₀ : (((((fb.push kB).push m).push a).push b).push 6)[fa.size]! = kB := by
    rw [push4_get (by simp [h.1]), ← h.1, getElem!_push_eq']
  refine .natB (by rw [a₄, b₄]) (by rw [a₄]; decide) (by rw [a₀, b₀]; exact hk) (by rw [a₁, b₁])
    (by rw [a₂, b₂]) (by rw [a₃, b₃]) ?_
  exact (h.2.push (Nat.le_refl _) h.1 kA kB).push4 (by simp) (by simp [h.1]) _ _ _ _ _ _ _ _

end

section
variable {j : Nat} {N : Name → Prop} {env : Env} {f₂ : Name → Option ConstantInfo}
  {p₂ : Name → Nat → Option ProjEntry} {t₀ : Expr} {n : Nat}

/-- **One literal reading** on both sides. -/
theorem MRel.lit {sA sB : MS} (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB) {x : Nat}
    (hx : x < sA.val.size / 4) :
    litRd sB.P sB.val x = litRd sA.P sA.val x ∧ litM sB.P sB.val sB.argA x = litM sA.P sA.val sA.argA x := by
  obtain ⟨w0, w2, w3, hw⟩ := hr.valW hx
  have e : litRd sB.P sB.val x = litRd sA.P sA.val x := by
    unfold litRd
    rw [w0, w3]
    by_cases h2 : sA.val[g4X4 x]! = 2
    · simp only [h2, beq_self_eq_true, ↓reduceIte]
    by_cases h1 : sA.val[g4X4 x]! = 1
    · rw [h1] at hw
      rw [ent_beq hr.invA.toCompInv hr.invB.toCompInv hw hr.kZero.1,
        ent_beq hr.invA.toCompInv hr.invB.toCompInv hw hr.kSucc.1]
    · have h2' : (sA.val[g4X4 x]! == 2) = false := by simpa using h2
      have h1' : (sA.val[g4X4 x]! == 1) = false := by simpa using h1
      simp only [h2', h1', Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  refine ⟨e, ?_⟩
  unfold litM
  rw [e, w0, w2, hr.argA]
  by_cases h2 : sA.val[g4X4 x]! = 2
  · rw [h2] at hw
    simp only [h2, beq_self_eq_true, ↓reduceIte]
    exact hw.1
  · have h2' : (sA.val[g4X4 x]! == 2) = false := by simpa using h2
    simp only [h2', Bool.false_eq_true, ↓reduceIte]

/-- A `Bool`-valued operation is `Nat.beq` or `Nat.ble`. -/
theorem op_kind1 {c : Name} (h : g4NatKind ((natBin14Names.idxOf? c).getD 0) = 1) :
    c = natBeqName ∨ c = natBleName := by
  cases hi : natBin14Names.idxOf? c with
  | none => simp [hi, g4NatKind] at h
  | some i =>
    rw [hi] at h
    have h45 : i = 4 ∨ i = 5 := by simp [g4NatKind] at h; omega
    have := List.idxOf?_eq_some_iff.mp hi
    rcases h45 with rfl | rfl
    · exact .inl (by simpa [natBin14Names] using this.2.1.symm)
    · exact .inr (by simpa [natBin14Names] using this.2.1.symm)

/-- **Mode 1 at a literal frame.** -/
theorem sim_mode1n (hag : LookAgree N env.find? env.findProj? f₂ p₂) (ih : SimAt j N env f₂ p₂ t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 1) (hn : 0 < sA.fs.size)
    (ht : sA.fs[sA.fs.size - 1]! &&& 15 = 5 ∨ sA.fs[sA.fs.size - 1]! &&& 15 = 6) {m : Nat}
    (hmn : (j = 0 ∧ m = n + 1) ∨ (j = 1 ∧ 2 * n + 1 ≤ m)) :
    OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmB : sB.mode = 1 := by rw [hr.mode, hm]
  have hg := hr.regs
  simp only [RegRel, hm] at hg
  obtain ⟨he, hx, hpc⟩ := hg
  have hxl := (h.val1 hm).1
  unfold MS.run
  rw [hm, g4Run.eq_7 env.find? env.findProj? sA.P sA.cel sA.val sA.ev sA.fs sA.argA sA.slots sA.mem sA.mH 1
    sA.pc sA.env sA.x sA.st n (by decide) (by decide) (by decide) (by decide), hmB,
    g4Run.eq_7 f₂ p₂ sB.P sB.cel sB.val sB.ev sB.fs sB.argA sB.slots sB.mem sB.mH 1
    sB.pc sB.env sB.x sB.st m (by decide) (by decide) (by decide) (by decide)]
  rw [hr.fs.1, hx, hr.fs.top hn]
  split
  next h0 => simp only [beq_iff_eq] at h0; omega
  next =>
  split
  all_goals try (rename_i ht'; rcases ht with ht | ht <;> rw [ht] at ht' <;> cases ht')
  rename_i h2 h1 h3 h4 h7
  dsimp only
  rw [← litRd.eq_1, ← litRd.eq_1, ← litM.eq_1, ← litM.eq_1, (hr.lit hxl).1, (hr.lit hxl).2]
  have hv4 : sA.val.size % 4 = 0 := h.store.valSz
  have hstop : ∀ g, OutRel j N env f₂ p₂ (.stop g sA.st) (.stop g sB.st) :=
    fun g => .inr (.inl ⟨_, _, rfl, by rw [hr.st]⟩)
  split
  next hrd =>
    obtain ⟨fl', h'⟩ := step_lit_succ hR h hm hn ht hrd
    refine ih.app (sB := { sB with
        fs := sB.fs.push 7
        mode := 2
        pc := 0
        env := 0
        x := litM sA.P sA.val sA.argA sA.x }) h' hR ?_ (m := m) (fuel_s hmn)
    exact { hr with
      fs := hr.fs.pushOne 7 (.inr (.inr (by decide)))
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }
  next hrd =>
    split
    next h5 =>
      have h5' : sA.fs[sA.fs.size - 1]! &&& 15 = 5 := by simpa using h5
      obtain ⟨hk, e3, e2, hpopF⟩ := hr.fs.natATop hn h5'
      rw [e3, e2]
      obtain ⟨fl', h'⟩ := step_natA_lit hR h hm hn h5' hrd
      refine ih.app (sB := { sB with
          fs := (((((g4PopN sB.fs 4).push sB.fs[sA.fs.size - 4]!).push (litM sA.P sA.val sA.argA sA.x)).push
            sA.fs[sA.fs.size - 3]!).push sA.fs[sA.fs.size - 2]!).push 6
          mode := 2
          pc := 0
          env := 0
          x := sA.fs[sA.fs.size - 2]! }) h' hR ?_ (m := m) (fuel_s hmn)
      exact { hr with
        fs := hpopF.pushNatB hk _ _ _
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
    next h5 =>
      have h6 : sA.fs[sA.fs.size - 1]! &&& 15 = 6 := by
        rcases ht with e | e
        · exact absurd (by simp [e]) h5
        · exact e
      obtain ⟨hk, e4, e3, e2, hpopF⟩ := hr.fs.natBTop hn h6
      have hkE : sB.P.kE[sB.fs[sA.fs.size - 5]!]! = sA.P.kE[sA.fs[sA.fs.size - 5]!]! := by
        obtain ⟨fl', rfl, -, -⟩ := FS.top_natB h.stack hn h6
        obtain ⟨hkk, -, -, h3⟩ := h.frames _ (List.mem_cons_self ..)
        obtain ⟨c, lps, v, hi, -⟩ := EntOK.tag3 (hr.invA.ents _ hkk) hkk h3
        exact (get!_congr2 ((hk.1.defnW hr.invA hr.invB hi (hag.find c (hk.2 _ hi)).symm
          (hr.natOkAt hag hk c _ _ _ hi)).2.2.1 h3)).symm
      have hop : ∃ c lps v, sA.P.kInfo[sA.fs[sA.fs.size - 5]!]? = some (.defn c lps [] v) ∧
          natBin14 c = true ∧ sA.P.kE[sA.fs[sA.fs.size - 5]!]? = some ((natBin14Names.idxOf? c).getD 0) := by
        obtain ⟨fl', rfl, -, -⟩ := FS.top_natB h.stack hn h6
        obtain ⟨hkk, -, -, h3⟩ := h.frames _ (List.mem_cons_self ..)
        obtain ⟨c, lps, v, hi, -, hb, he⟩ := EntOK.tag3 (hr.invA.ents _ hkk) hkk h3
        exact ⟨c, lps, v, hi, hb, he⟩
      rw [e4, hkE, hr.maxNat]
      split
      next => exact hstop _
      next =>
        split
        next hk0 =>
          split
          next => exact hstop _
          next =>
            obtain ⟨fl', h'⟩ := step_natB_nat hR h hm hn h6 hrd hk0
            rw [hr.val.1]
            refine ih.app (sB := { sB with
                val := (((sB.val.push 2).push (g4NatVal sA.P.kE[sA.fs[sA.fs.size - 5]!]! sA.fs[sA.fs.size - 4]!
                  (litM sA.P sA.val sA.argA sA.x))).push 0).push 0
                fs := g4PopN sB.fs 5
                mode := 1
                pc := 0
                env := 0
                x := sA.val.size >>> 2 }) h' hR ?_ (m := m) (fuel_s hmn)
            obtain ⟨c, lps, v, hi, hb, -⟩ := hop
            exact { hr with
              val := hr.val.push hv4 2 0 0 _ _ ⟨rfl, hag.natOp c (hk.2 _ hi) hb⟩
              fs := hpopF
              mode := rfl
              regs := ⟨rfl, rfl, rfl⟩ }
        next hk1 =>
          obtain ⟨fl', h'⟩ := step_natB_bool hR h hm hn h6 hrd hk1
          rw [hr.val.1]
          have hb : ERel N sA.P sB.P
              (if g4NatVal sA.P.kE[sA.fs[sA.fs.size - 5]!]! sA.fs[sA.fs.size - 4]!
                (litM sA.P sA.val sA.argA sA.x) == 1 then sA.P.kTrue else sA.P.kFalse)
              (if g4NatVal sA.P.kE[sA.fs[sA.fs.size - 5]!]! sA.fs[sA.fs.size - 4]!
                (litM sA.P sA.val sA.argA sA.x) == 1 then sB.P.kTrue else sB.P.kFalse) := by
            have hBN : N boolTrueName ∧ N boolFalseName := by
              obtain ⟨c, lps, v, hi, -, he⟩ := hop
              rw [get!_of_some he] at hk1
              exact hag.boolOp c (hk.2 _ hi) (op_kind1 hk1)
            split
            · exact hr.kTrue.2 hBN.1
            · exact hr.kFalse.2 hBN.2
          refine ih.app (sB := { sB with
              val := (((sB.val.push 1).push (if g4NatVal sA.P.kE[sA.fs[sA.fs.size - 5]!]! sA.fs[sA.fs.size - 4]!
                (litM sA.P sA.val sA.argA sA.x) == 1 then sB.P.kTrue else sB.P.kFalse)).push 0).push 0
              fs := g4PopN sB.fs 5
              mode := 1
              pc := 0
              env := 0
              x := sA.val.size >>> 2 }) h' hR ?_ (m := m) (fuel_s hmn)
          exact { hr with
            val := hr.val.push hv4 1 0 0 _ _ hb
            fs := hpopF
            mode := rfl
            regs := ⟨rfl, rfl, rfl⟩ }
        next => exact hstop _
  next =>
    by_cases h5 : sA.fs[sA.fs.size - 1]! &&& 15 = 5
    · have h5' : (sA.fs[sA.fs.size - 1]! &&& 15 == 5) = true := by simpa using h5
      simp only [h5', ↓reduceIte]
      obtain ⟨hk, e3, e2, hpopF⟩ := hr.fs.natATop hn h5
      rw [e3, e2]
      obtain ⟨fl', h'⟩ := step_natA_delta h hm hn h5
      refine ih.app (sB := { sB with
          fs := ((g4PopN sB.fs 4).push (g4Tag sA.fs[sA.fs.size - 2]! 1)).push (g4Tag sA.fs[sA.fs.size - 3]! 1)
          mode := 3
          pc := 1
          env := 0
          x := sB.fs[sA.fs.size - 4]! }) h' hR ?_ (m := m) (fuel_s hmn)
      exact { hr with
        fs := (hpopF.pushOne _ (.inl (tag_and _ 1 (by omega)))).pushOne _ (.inl (tag_and _ 1 (by omega)))
        mode := rfl
        regs := ⟨rfl, rfl, hk⟩ }
    · have h6 : sA.fs[sA.fs.size - 1]! &&& 15 = 6 := by
        rcases ht with e | e
        · exact absurd e h5
        · exact e
      have h5' : (sA.fs[sA.fs.size - 1]! &&& 15 == 5) = false := by simpa using h5
      simp only [h5', Bool.false_eq_true, ↓reduceIte]
      obtain ⟨hk, -, e3, e2, hpopF⟩ := hr.fs.natBTop hn h6
      rw [e3, e2]
      obtain ⟨fl', h'⟩ := step_natB_delta h hm hn h6
      refine ih.app (sB := { sB with
          fs := ((g4PopN sB.fs 5).push (g4Tag sA.fs[sA.fs.size - 2]! 1)).push (g4Tag sA.fs[sA.fs.size - 3]! 1)
          mode := 3
          pc := 1
          env := 0
          x := sB.fs[sA.fs.size - 5]! }) h' hR ?_ (m := m) (fuel_s hmn)
      exact { hr with
        fs := (hpopF.pushOne _ (.inl (tag_and _ 1 (by omega)))).pushOne _ (.inl (tag_and _ 1 (by omega)))
        mode := rfl
        regs := ⟨rfl, rfl, hk⟩ }

end

end ConLeche.Verify.Ground
