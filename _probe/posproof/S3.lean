/-
S3 (lane POSPROOF): the per-frame facts `nestPos`'s run supplies at a
cycle through a mutual container group do NOT imply monotonicity.

Shape (`inmodel_groups`): `F α | mk : G α → F α`, `G α | … F α …`,
a field `F N`.  Per-key frames: the F-frame reduces F's fields with its
own hole `Y_F` and `G N` CONCRETE (not in progress when the frame
starts); the G-frame reduces G's fields with `Y_F` and `Y_G` both holes.
What the runs give, with the group's operator `Ψ = (Ψ_F, Ψ_G)` and its
least fixed point `L X = (L_F X, L_G X)` at the outer holes `X`:

  (1) `Ψ X` is monotone in the group's holes, at every `X` (the clause);
  (2) the G-frame: `Ψ_G` is jointly monotone in `(X, Y_F, Y_G)`;
  (3) the F-frame: `Ψ_F X (Y_F, L_G X) = D X Y_F (L_G X)` for every
      `Y_F`, with `D` (the reduct's reading, `G N` read as a slot)
      jointly monotone — `Ψ_F` is known ONLY at `Y_G = L_G X`.

Bekić needs `Ψ_F X (Y_F, Y_G)` at `Y_G = inner X Y_F ≠ L_G X`.  The
countermodel: sets = `Prop`, `X : Bool` (`false ≤ true`),
`Ψ_G X (a, b) = a`, `Ψ_F X (a, b) = if X then b else True`,
`D X a w = w`.  (1)–(3) hold, and `L_F false = True`, `L_F true = False`.
(The kernel's facts are true of the real `Ψ`; what is missing is a
PROVABLE link between `Ψ_F` off `L_G X` and the run — the whnf
commutation of S1, or a frame that abstracts `G` too.)
-/

def ΨF (X : Bool) (p : Prop × Prop) : Prop := if X then p.2 else True
def ΨG (_X : Bool) (p : Prop × Prop) : Prop := p.1
def D (_X : Bool) (_a w : Prop) : Prop := w

/-- a pre-fixed pair of the group operator at `X` -/
def Closed (X : Bool) (p : Prop × Prop) : Prop := (ΨF X p → p.1) ∧ (ΨG X p → p.2)

/-- `L X`: the least pre-fixed pair, componentwise the intersection. -/
def L (X : Bool) : Prop × Prop :=
  (∀ p, Closed X p → p.1, ∀ p, Closed X p → p.2)

-- (1) the operator is monotone in the holes at every X
example (X : Bool) (p q : Prop × Prop) (h1 : p.1 → q.1) (h2 : p.2 → q.2) :
    (ΨF X p → ΨF X q) ∧ (ΨG X p → ΨG X q) := by
  cases X <;> exact ⟨fun h => by simp_all [ΨF], h1⟩

-- (2) Ψ_G is jointly monotone (it ignores X)
example (X X' : Bool) (p q : Prop × Prop) (h1 : p.1 → q.1) : ΨG X p → ΨG X' q := h1

-- (3) D is jointly monotone, and agrees with Ψ_F at Y_G = L_G X
example (X X' : Bool) (a a' w w' : Prop) (hw : w → w') : D X a w → D X' a' w' := hw

theorem L_false : (L false).1 ∧ (L false).2 := by
  refine ⟨fun p hp => hp.1 (by simp [ΨF]), fun p hp => hp.2 (hp.1 (by simp [ΨF]))⟩

theorem L_true_F : ¬ (L true).1 := fun h => h (False, False) ⟨fun x => x, fun x => x⟩

theorem agree (X : Bool) (a : Prop) : ΨF X (a, (L X).2) ↔ D X a (L X).2 := by
  cases X
  · simp only [ΨF, D]; exact ⟨fun _ => L_false.2, fun _ => trivial⟩
  · simp [ΨF, D]

/-- **not monotone in `X`**, though (1)–(3) hold. -/
theorem not_mono : ¬ ((L false).1 → (L true).1) := fun h => L_true_F (h L_false.1)
