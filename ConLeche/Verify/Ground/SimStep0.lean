module

public import ConLeche.Verify.Ground.SimStep
public import ConLeche.Verify.Ground.SimBridge
import ConLeche.Verify.Ground.Step0

public section

/-!
# The step simulation, mode 0 (task #423 soundness, layer (d), item 2(c))

Evaluating a node: no compile on either side, so one step of A is one step
of B.  The tag and the fields come from the layout bridge (`SimBridge`).
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable {j : Nat} {N : Name → Prop} {env : Env} {f₂ : Name → Option ConstantInfo}
  {p₂ : Name → Nat → Option ProjEntry} {t₀ : Expr} {n : Nat}

theorem shr2_eq (a : Nat) : a >>> 2 = a / 4 := Nat.shiftRight_eq_div_pow _ _

/-- One frame-stack test on both sides: a known call. -/
theorem FsRel.callTest {PA PB : G4Prog} {fa fb : Array Nat} (h : FsRel N PA PB fa fb) :
    (fb.size > 0 && fb[fb.size - 1]! &&& 15 == 1) = (fa.size > 0 && fa[fa.size - 1]! &&& 15 == 1) := by
  by_cases hn : 0 < fa.size
  · rw [h.1, h.top hn]
  · simp [h.1, hn]

/-- **Mode 0**, evaluating a node. -/
theorem sim_mode0 (hag : LookAgree N env.find? env.findProj? f₂ p₂) (ih : SimAt j N env f₂ p₂ t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 0) {m : Nat} (hmn : (j = 0 ∧ m = n + 1) ∨ (j = 1 ∧ 2 * (n + 1) ≤ m)) :
    OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmB : sB.mode = 0 := by rw [hr.mode, hm]
  have hg := hr.regs
  simp only [RegRel, hm] at hg
  obtain ⟨he, hx, hpc⟩ := hg
  have hc4 : sA.cel.size % 4 = 0 := h.store.celSz
  have hv4 : sA.val.size % 4 = 0 := h.store.valSz
  unfold MS.run
  rw [hm, hmB, g4Run.eq_2, g4Run.eq_2, hpc.tag hag]
  dsimp only
  split
  next ht =>
    rw [hpc.bvar ht]
    exact ih.app (step_bvar h hm ht) hR (hr.setRegs 2 0 0 0 _ _ ⟨rfl, by rw [hr.ev, he], rfl⟩)
      (m := m) (by omega)
  next ht =>
    obtain ⟨hn, t, hN, hA, hB⟩ := hpc.spine ht
    rw [hn]
    refine ih.app (sB := { sB with mode := 4, x := sA.P.code[sA.pc + 2]! }) (step_spine h hm ht) hR ?_ (m := m) (by omega)
    exact { hr with
      mode := rfl
      regs := ⟨he, rfl, t, hN, hA, hB⟩ }
  next ht =>
    rw [hr.fs.callTest]
    split
    next htop =>
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htop
      obtain ⟨fl', h'⟩ := step_lam_call h hm ht htop.1 htop.2
      obtain ⟨hcnt, htopA, hpop⟩ := hr.fs.args
      rw [hcnt, hpc.lamTn ht]
      generalize hk : (if g4CountArgs sA.fs sA.fs.size 0 < sA.P.code[sA.pc + 2]! then
        g4CountArgs sA.fs sA.fs.size 0 else sA.P.code[sA.pc + 2]!) = k at h' ⊢
      have hkn : k ≤ g4CountArgs sA.fs sA.fs.size 0 := by rw [← hk]; split <;> omega
      have hkt : k ≤ sA.P.code[sA.pc + 2]! := by rw [← hk]; split <;> omega
      have hbf : g4BindFrames sB.fs sB.ev k 0 sB.env = g4BindFrames sA.fs sA.ev k 0 sA.env := by
        rw [hr.ev, he, bindFrames_congr hr.fs.1 k 0 sA.env sA.ev (fun i hi => htopA _ (by omega))]
      rw [hbf]
      refine ih.app (sB := { sB with
          ev := g4BindFrames sA.fs sA.ev k 0 sA.env, fs := g4PopN sB.fs k,
          pc := if k == sA.P.code[sA.pc + 2]! then sB.P.code[sB.pc + 3]!
            else g4LamWalk sB.P.code k sB.pc,
          env := (g4BindFrames sA.fs sA.ev k 0 sA.env).size >>> 1, mode := 0, x := 0 })
        h' hR ?_ (m := m) (by omega)
      exact { hr with
        ev := rfl
        fs := hpop k hkn
        mode := rfl
        regs := ⟨rfl, rfl, hpc.lamBody ht hkt⟩ }
    next =>
      rw [hr.val.1, he]
      refine ih.app (sB := { sB with
          val := (((sB.val.push 0).push sB.pc).push sA.env).push 0, mode := 1, pc := 0, env := 0,
          x := sA.val.size >>> 2 })
        (step_lam_value h hm ht) hR ?_ (m := m) (by omega)
      exact { hr with
        val := hr.val.push hv4 0 sA.env 0 sA.pc sB.pc hpc
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
  next ht =>
    obtain ⟨hv, hb⟩ := hpc.letE ht
    obtain ⟨oc', h'⟩ := step_let h hm ht
    rw [hr.cel.1, hr.ev, he]
    refine ih.app (sB := { sB with
        cel := (((sB.cel.push 0).push sB.P.code[sB.pc + 1]!).push sA.env).push 0,
        ev := (sA.ev.push (sA.cel.size >>> 2)).push sA.env, mode := 0, pc := sB.P.code[sB.pc + 2]!,
        env := (sA.ev.size >>> 1) + 1, x := 0 })
      h' hR ?_ (m := m) (by omega)
    exact { hr with
      cel := hr.cel.push hc4 0 sA.env 0 _ _ (fun _ => hv)
      ev := rfl
      mode := rfl
      regs := ⟨rfl, rfl, hb⟩ }
  next ht =>
    refine ih.app (sB := { sB with
          mode := 3, pc := 0, env := 0, x := sB.P.code[sB.pc + 1]!,
          st := sB.st + 1 })
      (step_const h hm ht) hR ?_ (m := m) (by omega)
    exact { hr with
      mode := rfl
      st := by simp [hr.st]
      regs := ⟨rfl, rfl, hpc.const ht⟩ }
  next ht =>
    rw [(hpc.natLit ht).1, hr.val.1]
    refine ih.app (sB := { sB with
        val := (((sB.val.push 2).push sA.P.code[sA.pc + 1]!).push 0).push 0, mode := 1, pc := 0,
        env := 0, x := sA.val.size >>> 2 })
      (step_natLit h hm ht) hR ?_ (m := m) (by omega)
    exact { hr with
      val := hr.val.push hv4 2 0 0 _ _ ⟨rfl, (hpc.natLit ht).2⟩
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }
  next ht =>
    rw [hr.val.1]
    refine ih.app (sB := { sB with
        val := (((sB.val.push 3).push sB.P.code[sB.pc + 1]!).push 0).push 0, mode := 1, pc := 0,
        env := 0, x := sA.val.size >>> 2 })
      (step_strLit h hm ht) hR ?_ (m := m) (by omega)
    exact { hr with
      val := hr.val.push hv4 3 0 0 _ _ (hpc.strLit ht)
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }
  next ht =>
    obtain ⟨hp, he'⟩ := hpc.proj hag ht
    refine ih.app (sB := { sB with
          fs := (sB.fs.push sB.P.code[sB.pc + 1]!).push 4, mode := 0,
          pc := sB.P.code[sB.pc + 2]!, x := 0 })
      (step_proj h hm ht) hR ?_ (m := m) (by omega)
    exact { hr with
      fs := hr.fs.pushProj hp
      mode := rfl
      regs := ⟨he, rfl, he'⟩ }
  next ht =>
    obtain ⟨⟨a, hoA, hoB⟩, he'⟩ := hpc.shared ht
    have hsl : g4SlotGet sB.slots sB.P.epBase sB.P.code[sB.pc + 1]! =
        g4SlotGet sA.slots sA.P.epBase sA.P.code[sA.pc + 1]! := hr.slots.1 _ _ _ _ hoA hoB rfl
    rw [hsl]
    split
    next hs =>
      exact ih.app (step_shared_hit h hm ht (by simpa using hs)) hR
        (hr.setRegs 2 0 0 0 _ _ ⟨rfl, rfl, rfl⟩) (m := m) (by omega)
    next hs =>
      obtain ⟨oc', h'⟩ := step_shared_miss h hm ht (by simpa using hs)
      have hc0 : 0 < sA.cel.size >>> 2 := by rw [shr2_eq]; exact h.store.cell0
      rw [hr.cel.1]
      refine ih.app (sB := { sB with
          cel := (((sB.cel.push 0).push sB.P.code[sB.pc + 2]!).push 0).push 0,
          slots := g4SlotSet sB.slots sB.P.code[sB.pc + 1]! (sB.P.epBase + (sA.cel.size >>> 2)),
          mode := 2, pc := 0, env := 0, x := sA.cel.size >>> 2 })
        h' hR ?_ (m := m) (by omega)
      exact { hr with
        cel := hr.cel.push hc4 0 0 0 _ _ (fun _ => he')
        slots := hr.slots.set hr.invA.toCompInv hr.invB.toCompInv hoA hoB rfl hc0
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
  next h0 h1 h2 h3 h4 h5 h6 h7 h9 =>
    have hf := h.focus
    simp only [Focus, hm] at hf
    obtain ⟨u, ⟨s0, cs, hd, -⟩, -⟩ := hf
    have := hd.tag_le
    have h8 : sA.P.code[sA.pc]! = 8 := by
      simp only [imp_false] at h0 h1 h2 h3 h4 h5 h6 h7 h9
      omega
    exact ih.app (step_neutral h hm h8) hR (hr.setRegs 1 0 0 0 _ _ ⟨rfl, rfl, rfl⟩) (m := m) (by omega)

end

end ConLeche.Verify.Ground
