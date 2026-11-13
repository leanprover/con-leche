module

public import ConLeche.Verify.Ground.SimState
public import ConLeche.Verify.Ground.Step1N
public import ConLeche.Verify.Ground.Fuel

public section

/-!
# The step simulation (task #423 soundness, layer (d), item 2(c))

A run on `PA` (the environment's lookups, with the machine invariant `MInv`,
which supplies the bounds) against a run on `PB` (lookups `f₂`/`p₂`) from
`MRel`-related states: every step of A is matched by at most two steps of
B (B may compile a body A has compiled before, then take A's step; where A
compiles a body B has, B takes no step).  So A at fuel `n` and B at any
fuel `m ≥ 2 n` end alike (`OutRel`): A out of budget, or one stop, or both
done in related states.

The induction is `RunSound`'s, one lemma per mode (`sim_mode2` …).
-/

namespace ConLeche.Verify.Ground

open ConLeche

section
variable (j : Nat) (N : Name → Prop) (env : Env) (f₂ : Name → Option ConstantInfo)
  (p₂ : Name → Nat → Option ProjEntry)

/-- **Two outcomes alike**: the first run out of budget (in lock-step,
`j = 0`, the second too), or one stop, or both done, in mode 1 at the empty
stack of related states, the value returned a record of the first. -/
@[expose] def OutRel (oA oB : G4Out) : Prop :=
  (∃ st, oA = budgetStop st ∧ (j = 0 → ∃ st', oB = budgetStop st')) ∨ (∃ g st, oA = .stop g st ∧ oB = .stop g st) ∨
    ∃ (sA sB : MS) (lA lB : Nat), MRel j N env.find? env.findProj? f₂ p₂ sA sB ∧ sA.mode = 1 ∧
      sA.fs.size = 0 ∧ sA.x < sA.val.size / 4 ∧
      oA = .done sA.x sA.val sA.P sA.slots (sA.cel.size >>> 2) sA.st lA ∧
      oB = .done sB.x sB.val sB.P sB.slots (sB.cel.size >>> 2) sB.st lB

/-- **The simulation at fuel `n`**, the second run `j` extra steps per step
of the first: `j = 0` lock-step at one fuel, `j = 1` at twice the fuel. -/
@[expose] def SimAt (t₀ : Expr) (n : Nat) : Prop :=
  ∀ (sA sB : MS) (oc : Nat → Expr) (fl : List Fr), MInv env t₀ oc sA fl → RunOK env sA.P →
    MRel j N env.find? env.findProj? f₂ p₂ sA sB → ∀ m, (j = 0 ∧ m = n) ∨ (j = 1 ∧ 2 * n ≤ m) →
      OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? n) (sB.run f₂ p₂ m)

end

section
variable {j : Nat} {N : Name → Prop} {env : Env} {f₂ : Name → Option ConstantInfo}
  {p₂ : Name → Nat → Option ProjEntry} {t₀ : Expr} {n : Nat}

/-- One step of each run off the fuel bound. -/
theorem fuel_s {j n m : Nat} (h : (j = 0 ∧ m + 1 = n + 1) ∨ (j = 1 ∧ 2 * n + 1 ≤ m + 1)) :
    (j = 0 ∧ m = n) ∨ (j = 1 ∧ 2 * n ≤ m) := by omega

/-- One step of each run off the top fuel bound. -/
theorem fuel_t {j n m : Nat} (h : (j = 0 ∧ m + 1 = n + 1) ∨ (j = 1 ∧ 2 * (n + 1) ≤ m + 1)) :
    (j = 0 ∧ m = n) ∨ (j = 1 ∧ 2 * n ≤ m) := by omega

/-- The induction hypothesis at states the run's arguments spell out. -/
theorem SimAt.app (ih : SimAt j N env f₂ p₂ t₀ n) {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    {m : Nat} (hm : (j = 0 ∧ m = n) ∨ (j = 1 ∧ 2 * n ≤ m)) :
    OutRel j N env f₂ p₂
      (g4Run env.find? env.findProj? n sA.P sA.cel sA.val sA.ev sA.fs sA.argA sA.slots sA.mem sA.mH
        sA.mode sA.pc sA.env sA.x sA.st)
      (g4Run f₂ p₂ m sB.P sB.cel sB.val sB.ev sB.fs sB.argA sB.slots sB.mem sB.mH
        sB.mode sB.pc sB.env sB.x sB.st) :=
  ih sA sB oc fl h hR hr m hm

/-- **New registers**, the rest of the state kept. -/
theorem MRel.setRegs {f₁ : Name → Option ConstantInfo} {p₁ : Name → Nat → Option ProjEntry} {sA sB : MS}
    (hr : MRel j N f₁ p₁ f₂ p₂ sA sB) (md pcA pcB eA xA xB : Nat)
    (hg : RegRel N f₁ p₁ f₂ p₂ { sA with mode := md, pc := pcA, env := eA, x := xA }
      { sB with mode := md, pc := pcB, env := eA, x := xB }) :
    MRel j N f₁ p₁ f₂ p₂ { sA with mode := md, pc := pcA, env := eA, x := xA }
      { sB with mode := md, pc := pcB, env := eA, x := xB } :=
  { hr with mode := rfl, regs := hg }

/-- **Mode 2**, entering a cell. -/
theorem sim_mode2 (ih : SimAt j N env f₂ p₂ t₀ n) {sA sB : MS} {oc : Nat → Expr} {fl : List Fr}
    (h : MInv env t₀ oc sA fl) (hR : RunOK env sA.P) (hr : MRel j N env.find? env.findProj? f₂ p₂ sA sB)
    (hm : sA.mode = 2) {m : Nat} (hmn : (j = 0 ∧ m = n + 1) ∨ (j = 1 ∧ 2 * (n + 1) ≤ m)) :
    OutRel j N env f₂ p₂ (sA.run env.find? env.findProj? (n + 1)) (sB.run f₂ p₂ m) := by
  obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hmB : sB.mode = 2 := by rw [hr.mode, hm]
  have hg := hr.regs
  simp only [RegRel, hm] at hg
  obtain ⟨he, hx, hpc⟩ := hg
  have hf := h.focus
  simp only [Focus, hm] at hf
  have hxN : sA.x < sA.cel.size / 4 := hf.1
  obtain ⟨hs, hth⟩ := hr.cel.2 sA.x hxN
  unfold MS.run
  rw [hm, hmB, g4Run.eq_5, g4Run.eq_5, hx, g4X4_eq, hs]
  dsimp only
  split
  next h2 =>
    have h' := step_enter_value h hm (by rw [g4X4_eq]; exact h2)
    rw [g4X4_eq] at h'
    exact ih.app h' hR (m := m) (hr.setRegs 1 0 0 0 _ _ ⟨rfl, rfl, rfl⟩) (by omega)
  next h2 =>
    split
    next h0 =>
      simp only [beq_iff_eq] at h0
      obtain ⟨hco, hce⟩ := hth h0
      have h' := step_enter_thunk h hm (by rw [g4X4_eq]; exact h0)
      rw [g4X4_eq] at h'
      let sB' : MS := { sB with
        cel := sB.cel.set! (4 * sA.x) 1
        fs := sB.fs.push (g4Tag sA.x 2)
        mode := 0
        pc := sB.cel[4 * sA.x + 1]!
        env := sB.cel[4 * sA.x + 2]!
        x := 0 }
      refine ih.app (m := m) (sB := sB') h' hR ?_ (by omega)
      have hc4 : sA.cel.size % 4 = 0 := h.store.celSz
      exact { hr with
        cel := by
          have := hr.cel.setState hc4 sA.x 1 (by omega)
          rw [g4X4_eq] at this; exact this
        fs := by
          exact hr.fs.pushOne (g4Tag sA.x 2) (.inr (.inl (tag_and _ 2 (by omega))))
        mode := rfl
        regs := ⟨hce, rfl, hco⟩ }
    next => exact .inr (.inl ⟨_, _, rfl, by rw [hr.st]⟩)

end

end ConLeche.Verify.Ground
