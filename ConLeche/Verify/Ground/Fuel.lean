module

public import ConLeche.Kernel.Ground

public section

/-!
# The run's fuel (task #423 soundness, layer (d))

`g4Run`'s fuel is a step budget: a run that ends without exhausting it ends
the same way at any larger budget, with the surplus left over
(`g4Run_fuel_mono`).  Every recursive call of `g4Run` is a tail call at the
fuel one down, so the induction over the fuel is one case split per branch,
the same on both sides.
-/

namespace ConLeche.Verify.Ground

open ConLeche

/-- The stop at an exhausted budget. -/
@[expose] def budgetStop (st : Nat) : G4Out :=
  .stop (.decline "ground evaluation did not finish within its step budget") st

/-- A run's outcome at `k` more fuel: a finished run has `k` more left; a stop
is the same stop. -/
@[expose] def _root_.ConLeche.G4Out.addFuel (k : Nat) : G4Out → G4Out
  | .done v val P sl cells st left => .done v val P sl cells st (left + k)
  | o => o

/-- The outcome at more fuel is the outcome at less, shifted, unless the
lesser run exhausted its budget. -/
@[expose] def FuelRel (k : Nat) (o' o : G4Out) : Prop :=
  (∀ st, o ≠ budgetStop st) → o' = o.addFuel k

/-- **Fuel monotonicity**: a run that does not exhaust its budget `n` ends
the same way at `n + k`, with `k` more fuel left. -/
theorem g4Run_fuel_mono (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (k : Nat) :
    ∀ (n : Nat) (P : G4Prog) (cel val ev fs argA slots mem mH : Array Nat) (mode pc env x st : Nat),
      FuelRel k (g4Run find? findProj? (n + k) P cel val ev fs argA slots mem mH mode pc env x st)
        (g4Run find? findProj? n P cel val ev fs argA slots mem mH mode pc env x st) := by
  intro n
  induction n with
  | zero =>
    intro P cel val ev fs argA slots mem mH mode pc env x st h
    exact absurd (by rw [g4Run.eq_1]; rfl) (h st)
  | succ n ih =>
    intro P cel val ev fs argA slots mem mH mode pc env x st
    rw [show n + 1 + k = (n + k) + 1 by omega]
    rcases mode with _ | _ | _ | _ | _ | mode
    · rw [g4Run.eq_2, g4Run.eq_2]
      repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
    · rw [g4Run.eq_7 find? findProj? P cel val ev fs argA slots mem mH 1 pc env x st (n + k)
          (by decide) (by decide) (by decide) (by decide),
        g4Run.eq_7 find? findProj? P cel val ev fs argA slots mem mH 1 pc env x st n (by decide) (by decide) (by decide) (by decide)]
      repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
    · rw [g4Run.eq_5, g4Run.eq_5]
      repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
    · rw [g4Run.eq_6, g4Run.eq_6]
      repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
    · rcases x with _ | x
      · rw [g4Run.eq_3, g4Run.eq_3]
        repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
      · rw [g4Run.eq_4, g4Run.eq_4]
        repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
    · rw [g4Run.eq_7 find? findProj? P cel val ev fs argA slots mem mH (mode + 5) pc env x st (n + k)
          (by omega) (by omega) (by omega) (by omega),
        g4Run.eq_7 find? findProj? P cel val ev fs argA slots mem mH (mode + 5) pc env x st n (by omega) (by omega) (by omega) (by omega)]
      repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)

/-- A finished run finishes the same way at any larger fuel. -/
theorem g4Run_done_mono {find? : Name → Option ConstantInfo}
    {findProj? : Name → Nat → Option ProjEntry} {n m : Nat} (hnm : n ≤ m) {P : G4Prog}
    {cel val ev fs argA slots mem mH : Array Nat} {mode pc env x st : Nat} {v : Nat}
    {val' : Array Nat} {P' : G4Prog} {sl : Array Nat} {cells st' left : Nat}
    (h : g4Run find? findProj? n P cel val ev fs argA slots mem mH mode pc env x st =
      .done v val' P' sl cells st' left) :
    g4Run find? findProj? m P cel val ev fs argA slots mem mH mode pc env x st =
      .done v val' P' sl cells st' (left + (m - n)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [g4Run_fuel_mono find? findProj? k n P cel val ev fs argA slots mem mH mode pc env x st
    (by rw [h]; intro _ hb; exact nomatch hb), h]
  simp only [G4Out.addFuel, Nat.add_sub_cancel_left]

/-- A stop other than the exhausted budget is the same stop at any larger fuel. -/
theorem g4Run_stop_mono {find? : Name → Option ConstantInfo}
    {findProj? : Name → Nat → Option ProjEntry} {n m : Nat} (hnm : n ≤ m) {P : G4Prog}
    {cel val ev fs argA slots mem mH : Array Nat} {mode pc env x st : Nat} {why : G4Stop}
    {st' : Nat} (hw : ∀ st'', G4Out.stop why st' ≠ budgetStop st'')
    (h : g4Run find? findProj? n P cel val ev fs argA slots mem mH mode pc env x st =
      .stop why st') :
    g4Run find? findProj? m P cel val ev fs argA slots mem mH mode pc env x st = .stop why st' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [g4Run_fuel_mono find? findProj? k n P cel val ev fs argA slots mem mH mode pc env x st
    (by rw [h]; exact hw), h]
  rfl

/-- **The site at more fuel**: an answer at fuel `n` is the same answer, with
the same kept program and counters, at any larger fuel. -/
theorem ground4BoolCoreF_mono {find? : Name → Option ConstantInfo}
    {findProj? : Name → Nat → Option ProjEntry} {natOk strOk : Bool} {maxNat n m : Nat}
    (hnm : n ≤ m) {P₀ : G4Prog} {e : Expr} {b : Bool}
    (h : (ground4BoolCoreF find? findProj? natOk strOk maxNat n P₀ e).1.1 = .ok b) :
    ground4BoolCoreF find? findProj? natOk strOk maxNat m P₀ e =
      ground4BoolCoreF find? findProj? natOk strOk maxNat n P₀ e := by
  unfold ground4BoolCoreF at h ⊢
  generalize g4Setup find? findProj? natOk strOk maxNat P₀ = P at h ⊢
  rcases hc : g4Comp find? findProj? P e with ⟨o, P⟩
  simp only [hc] at h ⊢
  generalize hr : g4Run find? findProj? n { P with slotA := #[] } #[2, 0, 0, 0] #[5, 0, 0, 0] #[] #[]
    #[] P.slotA #[] (Array.replicate 1024 0) 0 o 0 0 0 = r at h ⊢
  cases r with
  | done v val P' sl cells st left =>
    simp only [g4Run_done_mono hnm hr]
    have : m - (left + (m - n)) = n - left := by omega
    rw [this]
  | stop why st =>
    have hw : ∀ st'', G4Out.stop why st ≠ budgetStop st'' := by
      intro st'' hb
      simp only [budgetStop, G4Out.stop.injEq] at hb
      obtain ⟨rfl, -⟩ := hb
      simp at h
    simp only [g4Run_stop_mono hnm hw hr]
    cases why <;> rfl

end ConLeche.Verify.Ground
