module

public import ConLeche.Verify.Ground.SimStep
import ConLeche.Verify.Ground.SimBridge
import ConLeche.Verify.Ground.Step0
import ConLeche.Verify.Ground.Step1
import ConLeche.Verify.Ground.Step3

public section

/-!
# The step simulation, mode 1: the done state, update and argument frames (task #423 soundness, layer (d), item 2(c))

Returning a value: the frame on top is one word on both sides (`FsRel.top`),
the value record one tag, environment and length, its payload by `ValW`.
A closure's λ node is `TRel` (the known call of mode 0), a constructor's or
partial application's entry `ERel`.
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable {N : Name → Prop} {env : Env} {f₂ : Name → Option ConstantInfo}
  {p₂ : Name → Nat → Option ProjEntry} {t₀ : Expr} {n : Nat}

theorem copyFrom_pre (start : Nat) : ∀ (n j : Nat) (argA : Array Nat), Pre argA (g4CopyFrom argA start n j)
  | 0, _, argA => by simp only [g4CopyFrom]; exact Pre.refl argA
  | n + 1, j, argA => by
    simp only [g4CopyFrom]; exact (Pre.push _ _).trans (copyFrom_pre start n (j + 1) _)

/-- One entry test on both sides: related entries are one to one. -/
theorem ent_beq {PA PB : G4Prog} (hA : CompInv env.find? env.findProj? PA) (hB : CompInv f₂ p₂ PB)
    {kA kB zA zB : Nat} (hk : ERel N PA PB kA kB) (hz : ERel N PA PB zA zB) : (kB == zB) = (kA == zA) := by
  have e := EntRel.iff hA hB hz.1 hk.1
  by_cases h : kA = zA
  · rw [e.mp h, h, beq_self_eq_true, beq_self_eq_true]
  · rw [beq_false_of_ne h, beq_false_of_ne (fun h' => h (e.mpr h'))]

/-- **The returned value's words** on both sides. -/
theorem MRel.valW {sA sB : MS} (hr : MRel N env.find? env.findProj? f₂ p₂ sA sB)
    {x : Nat} (hx : x < sA.val.size / 4) :
    sB.val[g4X4 x]! = sA.val[g4X4 x]! ∧ sB.val[g4X4 x + 2]! = sA.val[g4X4 x + 2]! ∧
      sB.val[g4X4 x + 3]! = sA.val[g4X4 x + 3]! ∧
      ValW N env.find? env.findProj? f₂ p₂ sA.P sB.P sA.val[g4X4 x]! sA.val[g4X4 x + 1]! sB.val[g4X4 x + 1]! := by
  rw [g4X4_eq]; exact hr.val.2 x hx

/-- **Mode 1 at the update and argument frames**, and the done state. -/
theorem sim_mode1a (ih : SimAt N env f₂ p₂ t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 1) (ht : sA.fs.size = 0 ∨ sA.fs[sA.fs.size - 1]! &&& 15 = 1 ∨
      sA.fs[sA.fs.size - 1]! &&& 15 = 2) {m : Nat} (hmn : 2 * n + 1 ≤ m) :
    OutRel N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
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
  obtain ⟨hcnt, htop, hpop⟩ := hr.fs.args
  have hcnt' : g4CountArgs sB.fs sA.fs.size 0 = g4CountArgs sA.fs sA.fs.size 0 := by
    have e := hcnt; rwa [hr.fs.1] at e
  rw [hr.fs.1, hx]
  split
  next h0 =>
    have h0' : sA.fs.size = 0 := by simpa using h0
    exact .inr (.inr ⟨sA, sB, n, m, hr, hm, h0', rfl, by rw [hx]⟩)
  next h0 =>
  have hn : 0 < sA.fs.size := by
    have : sA.fs.size ≠ 0 := by simpa using h0
    omega
  rw [hr.fs.top hn]
  have hc4 : sA.cel.size % 4 = 0 := h.store.celSz
  have hv4 : sA.val.size % 4 = 0 := h.store.valSz
  obtain ⟨w0, w2, w3, hw⟩ := hr.valW hxl
  split
  next ht2 =>
    obtain ⟨fl', h'⟩ := step_pop_update h hm hn ht2
    refine ih.app (sB := { sB with
        cel := sB.cel.set! (g4X4 (sA.fs[sA.fs.size - 1]! >>> 4)) (sA.x + 2)
        fs := sB.fs.pop
        mode := 1
        pc := 0
        env := 0
        x := sA.x }) h' hR ?_ (m := m) (by omega)
    exact { hr with
      cel := hr.cel.setState hc4 (sA.fs[sA.fs.size - 1]! >>> 4) (sA.x + 2) (by omega)
      fs := hr.fs.popOne hn (.inr (.inl ht2))
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }
  next ht1 =>
    dsimp only
    rw [w0]
    split
    next hv =>
      obtain ⟨h1, hcode⟩ := step_arg_enter h hm hv
      rw [hv] at hw
      have hT : TRel N env.find? env.findProj? f₂ p₂ sA.P sB.P sA.val[g4X4 sA.x + 1]! sB.val[g4X4 sA.x + 1]! := hw
      obtain ⟨fl', h'⟩ := step_lam_call h1 rfl hcode hn ht1
      rw [hcnt', hT.lamTn hcode, w2]
      generalize hk : (if g4CountArgs sA.fs sA.fs.size 0 < sA.P.code[sA.val[g4X4 sA.x + 1]! + 2]! then
        g4CountArgs sA.fs sA.fs.size 0 else sA.P.code[sA.val[g4X4 sA.x + 1]! + 2]!) = k at h' ⊢
      have hkn : k ≤ g4CountArgs sA.fs sA.fs.size 0 := by rw [← hk]; split <;> omega
      have hkt : k ≤ sA.P.code[sA.val[g4X4 sA.x + 1]! + 2]! := by rw [← hk]; split <;> omega
      have hbf : g4BindFrames sB.fs sB.ev k 0 sA.val[g4X4 sA.x + 2]! =
          g4BindFrames sA.fs sA.ev k 0 sA.val[g4X4 sA.x + 2]! := by
        rw [hr.ev, bindFrames_congr hr.fs.1 k 0 _ sA.ev (fun i hi => htop _ (by omega))]
      rw [hbf]
      refine ih.app (sB := { sB with
          ev := g4BindFrames sA.fs sA.ev k 0 sA.val[g4X4 sA.x + 2]!, fs := g4PopN sB.fs k,
          pc := if k == sA.P.code[sA.val[g4X4 sA.x + 1]! + 2]! then sB.P.code[sB.val[g4X4 sA.x + 1]! + 3]!
            else g4LamWalk sB.P.code k sB.val[g4X4 sA.x + 1]!,
          env := (g4BindFrames sA.fs sA.ev k 0 sA.val[g4X4 sA.x + 2]!).size >>> 1, mode := 0, x := 0 })
        h' hR ?_ (m := m) (by omega)
      exact { hr with
        ev := rfl
        fs := hpop k hkn
        mode := rfl
        regs := ⟨rfl, rfl, hT.lamBody hcode hkt⟩ }
    next hv =>
      obtain ⟨fl', h'⟩ := step_arg_ctor h hm hv
      rw [hv] at hw
      rw [hcnt', w2, w3, hr.argA, hr.val.1, copyArgs_congr _ 0 _ htop.at]
      refine ih.app (sB := { sB with
          val := (((sB.val.push 1).push sB.val[g4X4 sA.x + 1]!).push sA.argA.size).push
            (sA.val[g4X4 sA.x + 3]! + g4CountArgs sA.fs sA.fs.size 0)
          fs := g4PopN sB.fs (g4CountArgs sA.fs sA.fs.size 0)
          argA := g4CopyArgs sA.fs (g4CopyFrom sA.argA sA.val[g4X4 sA.x + 2]! sA.val[g4X4 sA.x + 3]! 0)
            (g4CountArgs sA.fs sA.fs.size 0) 0
          mode := 1
          pc := 0
          env := 0
          x := sA.val.size >>> 2 }) h' hR ?_ (m := m) (by omega)
      have hpre := (copyFrom_pre sA.val[g4X4 sA.x + 2]! sA.val[g4X4 sA.x + 3]! 0 sA.argA).trans
        (copyArgs_spec sA.fs (g4CountArgs sA.fs sA.fs.size 0) 0 _).2.1
      exact { hr with
        val := hr.val.push hv4 1 _ _ _ _ hw
        argA := rfl
        memoA := hr.memoA.argA hpre
        memoB := (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH).argA hpre
        fs := hpop _ (Nat.le_refl _)
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
    next hv =>
      obtain ⟨fl', h'⟩ := step_arg_pap h hm hv
      rw [hv] at hw
      rw [w2, w3, hr.argA]
      refine ih.app (sB := { sB with
          fs := g4PushArgs sA.argA sA.val[g4X4 sA.x + 2]! sB.fs sA.val[g4X4 sA.x + 3]!
          argA := sA.argA
          mode := 3
          pc := 0
          env := 0
          x := sB.val[g4X4 sA.x + 1]! }) h' hR ?_ (m := m) (by omega)
      exact { hr with
        fs := FsRel.pushArgs _ _ _ hr.fs
        argA := rfl
        memoB := (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH)
        mode := rfl
        regs := ⟨rfl, rfl, hw⟩ }
    next =>
      obtain ⟨fl', h'⟩ := step_arg_pop h hm
      rw [hcnt']
      refine ih.app (sB := { sB with
          fs := g4PopN sB.fs (g4CountArgs sA.fs sA.fs.size 0)
          mode := 1
          pc := 0
          env := 0
          x := 0 }) h' hR ?_ (m := m) (by omega)
      exact { hr with
        fs := hpop _ (Nat.le_refl _)
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
  all_goals (exfalso; rcases ht with h0 | h1 | h2 <;> simp_all)


/-- **Mode 1 at a `Nat.succ` frame.** -/
theorem sim_mode1s (ih : SimAt N env f₂ p₂ t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 1) (hn : 0 < sA.fs.size) (ht : sA.fs[sA.fs.size - 1]! &&& 15 = 7) {m : Nat}
    (hmn : 2 * n + 1 ≤ m) :
    OutRel N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
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
  have hv4 : sA.val.size % 4 = 0 := h.store.valSz
  obtain ⟨w0, w2, w3, hw⟩ := hr.valW hxl
  have hpop := hr.fs.popOne hn (.inr (.inr ht))
  split
  next h0 => simp only [beq_iff_eq] at h0; omega
  next =>
  split
  next ht' => rw [ht] at ht'; cases ht'
  next ht' => rw [ht] at ht'; cases ht'
  next ht' => rw [ht] at ht'; cases ht'
  next ht' => rw [ht] at ht'; cases ht'
  rotate_left
  next h7 => exact absurd ht h7
  dsimp only
  rw [w0]
  split
  next hv =>
    obtain ⟨fl', h'⟩ := step_succ_lit h hm hn ht hv
    rw [hv] at hw
    have hw' : sB.val[g4X4 sA.x + 1]! = sA.val[g4X4 sA.x + 1]! := hw
    rw [hw', hr.val.1]
    refine ih.app (sB := { sB with
        val := (((sB.val.push 2).push (sA.val[g4X4 sA.x + 1]! + 1)).push 0).push 0
        fs := sB.fs.pop
        mode := 1
        pc := 0
        env := 0
        x := sA.val.size >>> 2 }) h' hR ?_ (m := m) (by omega)
    exact { hr with
      val := hr.val.push hv4 2 0 0 _ _ rfl
      fs := hpop
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }
  next hv =>
    rw [hv] at hw
    rw [w3, ent_beq hr.invA.toCompInv hr.invB.toCompInv hw hr.kZero,
      ent_beq hr.invA.toCompInv hr.invB.toCompInv hw hr.kSucc]
    split
    next hz =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hz
      obtain ⟨fl', h'⟩ := step_succ_zero hR h hm hn ht hv hz.1 hz.2
      rw [hr.val.1]
      refine ih.app (sB := { sB with
          val := (((sB.val.push 2).push 1).push 0).push 0
          fs := sB.fs.pop
          mode := 1
          pc := 0
          env := 0
          x := sA.val.size >>> 2 }) h' hR ?_ (m := m) (by omega)
      exact { hr with
        val := hr.val.push hv4 2 0 0 _ _ rfl
        fs := hpop
        mode := rfl
        regs := ⟨rfl, rfl, rfl⟩ }
    next =>
      split
      next hs =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hs
        obtain ⟨fl', h'⟩ := step_succ_succ hR h hm hn ht hv hs.1 hs.2
        rw [hr.argA, w2]
        refine ih.app (sB := { sB with
            fs := sB.fs.push 7
            argA := sA.argA
            mode := 2
            pc := 0
            env := 0
            x := sA.argA[sA.val[g4X4 sA.x + 2]!]! }) h' hR ?_ (m := m) (by omega)
        exact { hr with
          fs := hr.fs.pushOne 7 (.inr (.inr (by decide)))
          argA := rfl
          memoB := (hr.argA ▸ hr.memoB : MemoTab sB.mem sA.argA sB.mH)
          mode := rfl
          regs := ⟨rfl, rfl, rfl⟩ }
      next =>
        obtain ⟨fl', h'⟩ := step_succ_pop h hm hn ht
        refine ih.app (sB := { sB with fs := sB.fs.pop, mode := 1, pc := 0, env := 0, x := 0 }) h' hR ?_
          (m := m) (by omega)
        exact { hr with
          fs := hpop
          mode := rfl
          regs := ⟨rfl, rfl, rfl⟩ }
  next =>
    obtain ⟨fl', h'⟩ := step_succ_pop h hm hn ht
    refine ih.app (sB := { sB with fs := sB.fs.pop, mode := 1, pc := 0, env := 0, x := 0 }) h' hR ?_
      (m := m) (by omega)
    exact { hr with
      fs := hpop
      mode := rfl
      regs := ⟨rfl, rfl, rfl⟩ }

end

end ConLeche.Verify.Ground
