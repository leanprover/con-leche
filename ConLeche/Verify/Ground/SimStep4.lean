module

public import ConLeche.Verify.Ground.SimStep
public import ConLeche.Verify.Ground.SimBridge
import ConLeche.Verify.Ground.SimStep0
import ConLeche.Verify.Ground.Step4

public section

/-!
# The step simulation, mode 4 (task #423 soundness, layer (d), item 2(c))

Pushing a spine's arguments: no compile on either side, one step each.  An
argument position is erased on both sides or related (`comp2_spine`).
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable {N : Name → Prop} {env : Env} {f₂ : Name → Option ConstantInfo}
  {p₂ : Name → Nat → Option ProjEntry} {t₀ : Expr} {n : Nat}

/-- A step that keeps the mode, restated at the mode's value. -/
theorem MInv.setMode {s : MS} {oc : Nat → Expr} {fl : List Fr} (h : MInv env t₀ oc s fl) {md : Nat}
    (hm : s.mode = md) : MInv env t₀ oc { s with mode := md } fl := by
  have e : { s with mode := md } = s := by cases s; cases hm; rfl
  rw [e]; exact h

/-- **Mode 4**, pushing a spine's arguments. -/
theorem sim_mode4 (hag : LookAgree N env.find? env.findProj? f₂ p₂) (ih : SimAt N env f₂ p₂ t₀ n)
    {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 4) {m : Nat} (hmn : 2 * (n + 1) ≤ m) :
    OutRel N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmB : sB.mode = 4 := by rw [hr.mode, hm]
  have hg := hr.regs
  simp only [RegRel, hm] at hg
  obtain ⟨he, hx, t, hN, hA, hB⟩ := hg
  have hc4 : sA.cel.size % 4 = 0 := h.store.celSz
  have hv4 : sA.val.size % 4 = 0 := h.store.valSz
  have hf := h.focus
  simp only [Focus, hm] at hf
  obtain ⟨_, nn, _, _, _, h1, -, hn, -, -, -, -, hxn, -⟩ := hf
  obtain ⟨hhead, -, hargs⟩ := comp2_spine hag hN hA hB h1
  unfold MS.run
  rcases hxA : sA.x with _ | j
  · rw [hm, hmB, hx, hxA, g4Run.eq_3, g4Run.eq_3, he]
    exact ih.app (step_args_done h hm hxA) hR (hr.setRegs 0 _ _ sA.env 0 0 ⟨rfl, rfl, hhead⟩)
      (m := m) (by omega)
  rw [hm, hmB, hx, hxA, g4Run.eq_4, g4Run.eq_4, he]
  dsimp only
  have hj := hargs j (by rw [get!_of_some hn]; omega)
  have htag : sB.P.code[sB.P.code[sB.pc + 3 + j]!]! = sA.P.code[sA.P.code[sA.pc + 3 + j]!]! := by
    rcases hj with ⟨e₁, e₂⟩ | hT
    · rw [e₁, e₂]
    · exact hT.tag hag
  rw [htag]
  have hT : sA.P.code[sA.P.code[sA.pc + 3 + j]!]! ≠ 8 →
      TRel N env.find? env.findProj? f₂ p₂ sA.P sB.P sA.P.code[sA.pc + 3 + j]! sB.P.code[sB.pc + 3 + j]! :=
    fun h8 => hj.resolve_left (fun e => h8 e.1)
  have hc0 : 0 < sA.cel.size >>> 2 := by rw [shr2_eq]; exact h.store.cell0
  split
  next hc =>
    have e : g4EnvGet sB.ev sA.env sB.P.code[sB.P.code[sB.pc + 3 + j]! + 1]! =
        g4EnvGet sA.ev sA.env sA.P.code[sA.P.code[sA.pc + 3 + j]! + 1]! := by
      rw [hr.ev, (hT (by rw [hc]; decide)).bvar hc]
    rw [e]
    refine ih.app (sB := { sB with
        fs := sB.fs.push (g4Tag (g4EnvGet sA.ev sA.env sA.P.code[sA.P.code[sA.pc + 3 + j]! + 1]!) 1)
        env := sA.env
        x := j
        mode := 4 })
      (MInv.setMode (step_arg_var h hm hxA rfl hc) hm) hR ?_ (m := m) (by omega)
    exact { hr with
      fs := hr.fs.pushOne _ (.inl (tag_and _ 1 (by omega)))
      mode := rfl
      regs := ⟨rfl, rfl, t, hN, hA, hB⟩ }
  next hc =>
    have hT' := hT (by rw [hc]; decide)
    obtain ⟨oc', h'⟩ := step_arg_lam h hm hxA rfl hc
    rw [hr.val.1, hr.cel.1]
    refine ih.app (sB := { sB with
        cel := (((sB.cel.push ((sA.val.size >>> 2) + 2)).push sB.P.code[sB.pc + 3 + j]!).push sA.env).push 0
        val := (((sB.val.push 0).push sB.P.code[sB.pc + 3 + j]!).push sA.env).push 0
        fs := sB.fs.push (g4Tag (sA.cel.size >>> 2) 1)
        env := sA.env
        x := j
        mode := 4 })
      (MInv.setMode h' hm) hR ?_ (m := m) (by omega)
    exact { hr with
      cel := hr.cel.push hc4 _ sA.env 0 _ _ (fun e => absurd e (by omega))
      val := hr.val.push hv4 0 sA.env 0 _ _ hT'
      fs := hr.fs.pushOne _ (.inl (tag_and _ 1 (by omega)))
      mode := rfl
      regs := ⟨rfl, rfl, t, hN, hA, hB⟩ }
  next hc =>
    have hT' := hT (by rw [hc]; decide)
    obtain ⟨oc', h'⟩ := step_arg_nat h hm hxA rfl hc
    rw [hr.val.1, hr.cel.1, hT'.natLit hc]
    refine ih.app (sB := { sB with
        cel := (((sB.cel.push ((sA.val.size >>> 2) + 2)).push sB.P.code[sB.pc + 3 + j]!).push 0).push 0
        val := (((sB.val.push 2).push sA.P.code[sA.P.code[sA.pc + 3 + j]! + 1]!).push 0).push 0
        fs := sB.fs.push (g4Tag (sA.cel.size >>> 2) 1)
        env := sA.env
        x := j
        mode := 4 })
      (MInv.setMode h' hm) hR ?_ (m := m) (by omega)
    exact { hr with
      cel := hr.cel.push hc4 _ 0 0 _ _ (fun e => absurd e (by omega))
      val := hr.val.push hv4 2 0 0 _ _ rfl
      fs := hr.fs.pushOne _ (.inl (tag_and _ 1 (by omega)))
      mode := rfl
      regs := ⟨rfl, rfl, t, hN, hA, hB⟩ }
  next hc =>
    refine ih.app (sB := { sB with fs := sB.fs.push 1, env := sA.env, x := j, mode := 4 })
      (MInv.setMode (step_arg_neutral h hm hxA rfl hc) hm) hR ?_ (m := m) (by omega)
    exact { hr with
      fs := hr.fs.pushOne 1 (.inl rfl)
      mode := rfl
      regs := ⟨rfl, rfl, t, hN, hA, hB⟩ }
  next hc =>
    have hT' := hT (by rw [hc]; decide)
    have hk := hT'.const hc
    obtain ⟨⟨iA, iB, hiA, hiB, hkey⟩, -⟩ := hk
    have hoA := slotOwn_entry hr.invA hiA
    have hoB := slotOwn_entry hr.invB hiB
    have hsl := hr.slots.1 _ _ _ _ hoA hoB ⟨iA, iB, hiA, hiB, hkey⟩
    rw [hsl]
    split
    next hs =>
      refine ih.app (sB := { sB with
          fs := sB.fs.push (g4Tag (g4SlotGet sA.slots sA.P.epBase
            sA.P.kSlot[sA.P.code[sA.P.code[sA.pc + 3 + j]! + 1]!]!) 1)
          env := sA.env
          x := j
          mode := 4 })
        (MInv.setMode (step_arg_const_hit h hm hxA rfl hc (by simpa using hs)) hm) hR ?_ (m := m) (by omega)
      exact { hr with
        fs := hr.fs.pushOne _ (.inl (tag_and _ 1 (by omega)))
        mode := rfl
        regs := ⟨rfl, rfl, t, hN, hA, hB⟩ }
    next =>
      obtain ⟨oc', h'⟩ := step_arg_const_miss h hm hxA rfl hc
      rw [hr.cel.1]
      refine ih.app (sB := { sB with
          cel := (((sB.cel.push 0).push sB.P.code[sB.pc + 3 + j]!).push 0).push 0
          fs := sB.fs.push (g4Tag (sA.cel.size >>> 2) 1)
          slots := g4SlotSet sB.slots sB.P.kSlot[sB.P.code[sB.P.code[sB.pc + 3 + j]! + 1]!]!
            (sB.P.epBase + (sA.cel.size >>> 2))
          env := sA.env
          x := j
          mode := 4 })
        (MInv.setMode h' hm) hR ?_ (m := m) (by omega)
      exact { hr with
        cel := hr.cel.push hc4 0 0 0 _ _ (fun _ => hT')
        fs := hr.fs.pushOne _ (.inl (tag_and _ 1 (by omega)))
        slots := hr.slots.set hr.invA.toCompInv hr.invB.toCompInv hoA hoB ⟨iA, iB, hiA, hiB, hkey⟩ hc0
        mode := rfl
        regs := ⟨rfl, rfl, t, hN, hA, hB⟩ }
  next hc =>
    have hT' := hT (by rw [hc]; decide)
    obtain ⟨⟨a, hoA, hoB⟩, he'⟩ := hT'.shared hc
    have hsl := hr.slots.1 _ _ _ _ hoA hoB rfl
    rw [hsl]
    split
    next hs =>
      refine ih.app (sB := { sB with
          fs := sB.fs.push (g4Tag (g4SlotGet sA.slots sA.P.epBase
            sA.P.code[sA.P.code[sA.pc + 3 + j]! + 1]!) 1)
          env := sA.env
          x := j
          mode := 4 })
        (MInv.setMode (step_arg_shared_hit h hm hxA rfl hc (by simpa using hs)) hm) hR ?_ (m := m) (by omega)
      exact { hr with
        fs := hr.fs.pushOne _ (.inl (tag_and _ 1 (by omega)))
        mode := rfl
        regs := ⟨rfl, rfl, t, hN, hA, hB⟩ }
    next =>
      obtain ⟨oc', h'⟩ := step_arg_shared_miss h hm hxA rfl hc
      rw [hr.cel.1]
      refine ih.app (sB := { sB with
          cel := (((sB.cel.push 0).push sB.P.code[sB.P.code[sB.pc + 3 + j]! + 2]!).push 0).push 0
          fs := sB.fs.push (g4Tag (sA.cel.size >>> 2) 1)
          slots := g4SlotSet sB.slots sB.P.code[sB.P.code[sB.pc + 3 + j]! + 1]!
            (sB.P.epBase + (sA.cel.size >>> 2))
          env := sA.env
          x := j
          mode := 4 })
        (MInv.setMode h' hm) hR ?_ (m := m) (by omega)
      exact { hr with
        cel := hr.cel.push hc4 0 0 0 _ _ (fun _ => he')
        fs := hr.fs.pushOne _ (.inl (tag_and _ 1 (by omega)))
        slots := hr.slots.set hr.invA.toCompInv hr.invB.toCompInv hoA hoB rfl hc0
        mode := rfl
        regs := ⟨rfl, rfl, t, hN, hA, hB⟩ }
  next h0 h2 h5 h8 h4 h9 =>
    have hT' := hT (by simpa using h8)
    obtain ⟨oc', h'⟩ := step_arg_thunk h hm hxA rfl
    rw [hr.cel.1]
    refine ih.app (sB := { sB with
        cel := (((sB.cel.push 0).push sB.P.code[sB.pc + 3 + j]!).push sA.env).push 0
        fs := sB.fs.push (g4Tag (sA.cel.size >>> 2) 1)
        env := sA.env
        x := j
        mode := 4 })
      (MInv.setMode h' hm) hR ?_ (m := m) (by omega)
    exact { hr with
      cel := hr.cel.push hc4 0 sA.env 0 _ _ (fun _ => hT')
      fs := hr.fs.pushOne _ (.inl (tag_and _ 1 (by omega)))
      mode := rfl
      regs := ⟨rfl, rfl, t, hN, hA, hB⟩ }

end

end ConLeche.Verify.Ground
