module

public import ConLeche.Kernel.Ground

public section

/-!
# The run's fuel and its `Nat` size bound (task #423 soundness, layer (d))

`g4Run`'s fuel is a step budget: a run that ends without exhausting it ends
the same way at any larger budget, with the surplus left over
(`g4Run_fuel_mono`).  Every recursive call of `g4Run` is a tail call at the
fuel one down, so the induction over the fuel is one case split per branch,
the same on both sides.

The maximum `Nat` size only adds refusals: a run at bound `some M` that does
not refuse ends as the unbounded run (`none`, the specification's) does
(`g4Run_unbounded`, `ground4BoolCoreF_unbounded`), by the same induction.
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
    (findProj? : Name → Nat → Option ProjEntry) (mx : Option Nat) (k : Nat) :
    ∀ (n : Nat) (P : G4Prog) (cel val ev fs argA slots mem mH : Array Nat) (mode pc env x st : Nat),
      FuelRel k (g4Run find? findProj? mx (n + k) P cel val ev fs argA slots mem mH mode pc env x st)
        (g4Run find? findProj? mx n P cel val ev fs argA slots mem mH mode pc env x st) := by
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
    · rw [g4Run.eq_7 find? findProj? mx P cel val ev fs argA slots mem mH 1 pc env x st (n + k)
          (by decide) (by decide) (by decide) (by decide),
        g4Run.eq_7 find? findProj? mx P cel val ev fs argA slots mem mH 1 pc env x st n (by decide) (by decide) (by decide) (by decide)]
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
    · rw [g4Run.eq_7 find? findProj? mx P cel val ev fs argA slots mem mH (mode + 5) pc env x st (n + k)
          (by omega) (by omega) (by omega) (by omega),
        g4Run.eq_7 find? findProj? mx P cel val ev fs argA slots mem mH (mode + 5) pc env x st n (by omega) (by omega) (by omega) (by omega)]
      repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)

/-- A finished run finishes the same way at any larger fuel. -/
theorem g4Run_done_mono {find? : Name → Option ConstantInfo}
    {findProj? : Name → Nat → Option ProjEntry} {mx : Option Nat} {n m : Nat} (hnm : n ≤ m) {P : G4Prog}
    {cel val ev fs argA slots mem mH : Array Nat} {mode pc env x st : Nat} {v : Nat}
    {val' : Array Nat} {P' : G4Prog} {sl : Array Nat} {cells st' left : Nat}
    (h : g4Run find? findProj? mx n P cel val ev fs argA slots mem mH mode pc env x st =
      .done v val' P' sl cells st' left) :
    g4Run find? findProj? mx m P cel val ev fs argA slots mem mH mode pc env x st =
      .done v val' P' sl cells st' (left + (m - n)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [g4Run_fuel_mono find? findProj? mx k n P cel val ev fs argA slots mem mH mode pc env x st
    (by rw [h]; intro _ hb; exact nomatch hb), h]
  simp only [G4Out.addFuel, Nat.add_sub_cancel_left]

/-- A stop other than the exhausted budget is the same stop at any larger fuel. -/
theorem g4Run_stop_mono {find? : Name → Option ConstantInfo}
    {findProj? : Name → Nat → Option ProjEntry} {mx : Option Nat} {n m : Nat} (hnm : n ≤ m) {P : G4Prog}
    {cel val ev fs argA slots mem mH : Array Nat} {mode pc env x st : Nat} {why : G4Stop}
    {st' : Nat} (hw : ∀ st'', G4Out.stop why st' ≠ budgetStop st'')
    (h : g4Run find? findProj? mx n P cel val ev fs argA slots mem mH mode pc env x st =
      .stop why st') :
    g4Run find? findProj? mx m P cel val ev fs argA slots mem mH mode pc env x st = .stop why st' := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [g4Run_fuel_mono find? findProj? mx k n P cel val ev fs argA slots mem mH mode pc env x st
    (by rw [h]; exact hw), h]
  rfl

/-- **The site at more fuel**: an answer at fuel `n` is the same answer, with
the same kept program and counters, at any larger fuel. -/
theorem ground4BoolCoreF_mono {find? : Name → Option ConstantInfo}
    {findProj? : Name → Nat → Option ProjEntry} {natOk strOk : Bool} {mx : Option Nat} {n m : Nat}
    (hnm : n ≤ m) {P₀ : G4Prog} {e : Expr} {b : Bool}
    (h : (ground4BoolCoreF find? findProj? natOk strOk mx n P₀ e).1.1 = .ok b) :
    ground4BoolCoreF find? findProj? natOk strOk mx m P₀ e =
      ground4BoolCoreF find? findProj? natOk strOk mx n P₀ e := by
  unfold ground4BoolCoreF at h ⊢
  generalize g4Setup find? findProj? natOk strOk P₀ = P at h ⊢
  rcases hc : g4Comp find? findProj? P e with ⟨o, P⟩
  simp only [hc] at h ⊢
  generalize hr : g4Run find? findProj? mx n { P with slotA := #[] } #[2, 0, 0, 0] #[5, 0, 0, 0] #[] #[]
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

/-! ## The maximum `Nat` size -/

/-- A run's outcome is a refusal of the maximum `Nat` size. -/
@[expose] def _root_.ConLeche.G4Out.Refused : G4Out → Prop
  | .stop (.refuse ..) _ => True
  | _ => False

/-- The unbounded outcome is the bounded one, unless the bounded run refused. -/
@[expose] def MaxRel (o' o : G4Out) : Prop := ¬ o.Refused → o' = o

/-- The unbounded test before computing refuses only where a bound does too
(the count bound `natCountMax`, in both). -/
theorem g4NatPreRefuses_none {M op a b : Nat} :
    ((op == 3 || op == 12) && g4NatPreRefuses none op a b) = true →
      ((op == 3 || op == 12) && g4NatPreRefuses (some M) op a b) = true := by
  simp only [g4NatPreRefuses, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
  intro ⟨h, h'⟩
  refine ⟨h, ?_⟩
  rcases h with rfl | rfl <;> simp_all

/-- The unbounded test after computing never refuses. -/
theorem g4SizeOver_none {M op r : Nat} : (decide (op ≤ 2) && g4SizeOver none r) = true →
    (decide (op ≤ 2) && g4SizeOver (some M) r) = true := by
  simp [g4SizeOver]

-- raised: the return mode's (mode 1, and modes ≥ 5) many leaves each try the two
-- refusal closers' assumption searches over a large context (default 200000)
set_option maxHeartbeats 400000 in
/-- **The bound only adds refusals**: a run at the maximum `Nat` size
`some M` that does not refuse ends as the unbounded run does. -/
theorem g4Run_unbounded (find? : Name → Option ConstantInfo)
    (findProj? : Name → Nat → Option ProjEntry) (M : Nat) :
    ∀ (n : Nat) (P : G4Prog) (cel val ev fs argA slots mem mH : Array Nat) (mode pc env x st : Nat),
      MaxRel (g4Run find? findProj? none n P cel val ev fs argA slots mem mH mode pc env x st)
        (g4Run find? findProj? (some M) n P cel val ev fs argA slots mem mH mode pc env x st) := by
  intro n
  induction n with
  | zero =>
    intro P cel val ev fs argA slots mem mH mode pc env x st _
    rw [g4Run.eq_1, g4Run.eq_1]
  | succ n ih =>
    intro P cel val ev fs argA slots mem mH mode pc env x st
    rcases mode with _ | _ | _ | _ | _ | mode
    · rw [g4Run.eq_2, g4Run.eq_2]
      repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
    · rw [g4Run.eq_7 find? findProj? none P cel val ev fs argA slots mem mH 1 pc env x st n
          (by decide) (by decide) (by decide) (by decide),
        g4Run.eq_7 find? findProj? (some M) P cel val ev fs argA slots mem mH 1 pc env x st n
          (by decide) (by decide) (by decide) (by decide)]
      repeat' (first
        | (intro _; rfl)
        | apply ih
        | (intro h; exact absurd trivial h)
        | exact absurd (g4NatPreRefuses_none ‹(_ && g4NatPreRefuses none _ _ _) = true›) ‹_›
        | exact absurd (g4SizeOver_none ‹(_ && g4SizeOver none _) = true›) ‹_›
        | split
        | extract_lets
        | dsimp +zetaDelta only)
    · rw [g4Run.eq_5, g4Run.eq_5]
      repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
    · rw [g4Run.eq_6, g4Run.eq_6]
      repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
    · rcases x with _ | x
      · rw [g4Run.eq_3, g4Run.eq_3]
        repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
      · rw [g4Run.eq_4, g4Run.eq_4]
        repeat' (first | (intro _; rfl) | apply ih | split | extract_lets | dsimp +zetaDelta only)
    · rw [g4Run.eq_7 find? findProj? none P cel val ev fs argA slots mem mH (mode + 5) pc env x st n
          (by omega) (by omega) (by omega) (by omega),
        g4Run.eq_7 find? findProj? (some M) P cel val ev fs argA slots mem mH (mode + 5) pc env x st n
          (by omega) (by omega) (by omega) (by omega)]
      repeat' (first
        | (intro _; rfl)
        | apply ih
        | (intro h; exact absurd trivial h)
        | exact absurd (g4NatPreRefuses_none ‹(_ && g4NatPreRefuses none _ _ _) = true›) ‹_›
        | exact absurd (g4SizeOver_none ‹(_ && g4SizeOver none _) = true›) ‹_›
        | split
        | extract_lets
        | dsimp +zetaDelta only)

/-- **The site without a bound** (the third instance of the independence
lemma): an answer at the maximum `Nat` size `some M` other than a refusal
is the unbounded site's answer, with the same counters and kept program. -/
theorem ground4BoolCoreF_unbounded {find? : Name → Option ConstantInfo}
    {findProj? : Name → Nat → Option ProjEntry} {natOk strOk : Bool} {M n : Nat} {P₀ : G4Prog}
    {e : Expr} (h : ∀ op a b post,
      (ground4BoolCoreF find? findProj? natOk strOk (some M) n P₀ e).1.1 ≠ .error (.refuse op a b post)) :
    ground4BoolCoreF find? findProj? natOk strOk none n P₀ e =
      ground4BoolCoreF find? findProj? natOk strOk (some M) n P₀ e := by
  unfold ground4BoolCoreF at h ⊢
  generalize g4Setup find? findProj? natOk strOk P₀ = P at h ⊢
  rcases hc : g4Comp find? findProj? P e with ⟨o, P⟩
  simp only [hc] at h ⊢
  have hu := g4Run_unbounded find? findProj? M n { P with slotA := #[] } #[2, 0, 0, 0] #[5, 0, 0, 0] #[] #[]
    #[] P.slotA #[] (Array.replicate 1024 0) 0 o 0 0 0
  generalize g4Run find? findProj? (some M) n { P with slotA := #[] } #[2, 0, 0, 0] #[5, 0, 0, 0] #[] #[]
    #[] P.slotA #[] (Array.replicate 1024 0) 0 o 0 0 0 = r at h hu ⊢
  rw [hu ?_]
  intro hr
  cases r with
  | done => exact hr
  | stop why st =>
    cases why with
    | refuse op a b post => exact h op a b post rfl
    | _ => exact hr

end ConLeche.Verify.Ground
