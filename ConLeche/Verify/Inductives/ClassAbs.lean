module

public import ConLeche.Kernel.Inductives.ClassCheck

public section

/-!
# The class abstraction, without its memo (PROOFPLAN T3, syntactic half)

`classAbsGo` (`ConLeche/Kernel/Inductives/ClassCheck.lean`) abstracts
every recognised class occurrence, TOP-DOWN (outermost first), memoised
on the node.  `classAbsSpec` is the same walk without the memo; the memo
only ever records the spec's value (`ClassAbsMemoOk`), so the run IS the
spec (`classAbsGo_spec`, `classAbs_eq_spec`).  Everything the model says
about the abstraction is said about `classAbsSpec`.
-/

namespace ConLeche

/-- **The class abstraction, declaratively**: `hd = some (h, n)` — `e` is
the head part of a recognised occurrence, `n` index arguments still to
keep (abstracted themselves); `none` — look for an occurrence at `e`
(`occ`), else descend. -/
@[expose] def classAbsSpec (occ : Expr → Option (Expr × Nat)) : Option (Expr × Nat) → Expr → Expr
  | some (h, 0), _ => h
  | some (h, n + 1), .app f a => .app (classAbsSpec occ (some (h, n)) f) (classAbsSpec occ none a)
  | some _, e => e
  | none, e@(.app f a) =>
    match occ e with
    | some (h, 0) => h
    | some (h, n + 1) => .app (classAbsSpec occ (some (h, n)) f) (classAbsSpec occ none a)
    | none => .app (classAbsSpec occ none f) (classAbsSpec occ none a)
  | none, .lam ty b bm => .lam (classAbsSpec occ none ty) (classAbsSpec occ none b) bm
  | none, .forallE ty b bm => .forallE (classAbsSpec occ none ty) (classAbsSpec occ none b) bm
  | none, .letE ty v b =>
    .letE (classAbsSpec occ none ty) (classAbsSpec occ none v) (classAbsSpec occ none b)
  | none, .proj s i x => .proj s i (classAbsSpec occ none x)
  | none, e => e

/-- The memo records only the spec's values. -/
@[expose] def ClassAbsMemoOk (occ : Expr → Option (Expr × Nat)) (memo : Std.HashMap Expr Expr) :
    Prop :=
  ∀ k v, memo[k]? = some v → v = classAbsSpec occ none k

theorem ClassAbsMemoOk.insert {occ : Expr → Option (Expr × Nat)} {memo : Std.HashMap Expr Expr}
    (h : ClassAbsMemoOk occ memo) (e : Expr) :
    ClassAbsMemoOk occ (memo.insert e (classAbsSpec occ none e)) := by
  intro k v hk
  rw [Std.HashMap.getElem?_insert] at hk
  split at hk
  · rename_i he
    simp only [beq_iff_eq] at he
    subst he
    exact (Option.some.inj hk).symm
  · exact h k v hk

/-- **The memoised walk is the spec**, and keeps the memo sound. -/
theorem classAbsGo_spec (occ : Expr → Option (Expr × Nat)) :
    ∀ (e : Expr) (hd : Option (Expr × Nat)) (memo : Std.HashMap Expr Expr),
      ClassAbsMemoOk occ memo →
      (classAbsGo occ hd memo e).1 = classAbsSpec occ hd e ∧
        ClassAbsMemoOk occ (classAbsGo occ hd memo e).2 := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro hd memo hm
    rcases hd with _ | ⟨h, _ | n⟩
    · unfold classAbsGo
      split
      · rename_i r hr
        refine ⟨?_, hm⟩
        rw [hm _ _ hr]
      · rename_i hr
        cases hocc : occ (.app f a) with
        | none =>
          simp only
          obtain ⟨h1, h2⟩ := ihf none memo hm
          obtain ⟨h3, h4⟩ := iha none _ h2
          have hs : classAbsSpec occ none (.app f a) =
              .app (classAbsSpec occ none f) (classAbsSpec occ none a) := by
            simp [classAbsSpec, hocc]
          refine ⟨by rw [hs, h1, h3], ?_⟩
          rw [← h1, ← h3] at hs
          rw [← hs]
          exact h4.insert _
        | some p =>
          obtain ⟨hv, _ | n⟩ := p
          · simp only
            have hs : classAbsSpec occ none (.app f a) = hv := by simp [classAbsSpec, hocc]
            refine ⟨hs.symm, ?_⟩
            rw [← hs]
            exact hm.insert _
          · simp only
            obtain ⟨h1, h2⟩ := ihf (some (hv, n)) memo hm
            obtain ⟨h3, h4⟩ := iha none _ h2
            have hs : classAbsSpec occ none (.app f a) =
                .app (classAbsSpec occ (some (hv, n)) f) (classAbsSpec occ none a) := by
              simp [classAbsSpec, hocc]
            refine ⟨by rw [hs, h1, h3], ?_⟩
            rw [← h1, ← h3] at hs
            rw [← hs]
            exact h4.insert _
    · simp [classAbsGo, classAbsSpec, hm]
    · simp only [classAbsGo, classAbsSpec]
      obtain ⟨h1, h2⟩ := ihf (some (h, n)) memo hm
      obtain ⟨h3, h4⟩ := iha none _ h2
      exact ⟨by rw [h1, h3], h4⟩
  | lam ty b bm iht ihb =>
    intro hd memo hm
    rcases hd with _ | ⟨h, _ | n⟩
    · unfold classAbsGo
      split
      · rename_i r hr
        exact ⟨hm _ _ hr, hm⟩
      · obtain ⟨h1, h2⟩ := iht none memo hm
        obtain ⟨h3, h4⟩ := ihb none _ h2
        have hs : classAbsSpec occ none (.lam ty b bm) =
            .lam (classAbsSpec occ none ty) (classAbsSpec occ none b) bm := by simp [classAbsSpec]
        refine ⟨by simp only; rw [hs, h1, h3], ?_⟩
        simp only
        rw [h1, h3, ← hs]
        exact h4.insert _
    · simp [classAbsGo, classAbsSpec, hm]
    · simp [classAbsGo, classAbsSpec, hm]
  | forallE ty b bm iht ihb =>
    intro hd memo hm
    rcases hd with _ | ⟨h, _ | n⟩
    · unfold classAbsGo
      split
      · rename_i r hr
        exact ⟨hm _ _ hr, hm⟩
      · obtain ⟨h1, h2⟩ := iht none memo hm
        obtain ⟨h3, h4⟩ := ihb none _ h2
        have hs : classAbsSpec occ none (.forallE ty b bm) =
            .forallE (classAbsSpec occ none ty) (classAbsSpec occ none b) bm := by
          simp [classAbsSpec]
        refine ⟨by simp only; rw [hs, h1, h3], ?_⟩
        simp only
        rw [h1, h3, ← hs]
        exact h4.insert _
    · simp [classAbsGo, classAbsSpec, hm]
    · simp [classAbsGo, classAbsSpec, hm]
  | letE ty v b iht ihv ihb =>
    intro hd memo hm
    rcases hd with _ | ⟨h, _ | n⟩
    · unfold classAbsGo
      split
      · rename_i r hr
        exact ⟨hm _ _ hr, hm⟩
      · obtain ⟨h1, h2⟩ := iht none memo hm
        obtain ⟨h3, h4⟩ := ihv none _ h2
        obtain ⟨h5, h6⟩ := ihb none _ h4
        have hs : classAbsSpec occ none (.letE ty v b) =
            .letE (classAbsSpec occ none ty) (classAbsSpec occ none v) (classAbsSpec occ none b) := by
          simp [classAbsSpec]
        refine ⟨by simp only; rw [hs, h1, h3, h5], ?_⟩
        simp only
        rw [h1, h3, h5, ← hs]
        exact h6.insert _
    · simp [classAbsGo, classAbsSpec, hm]
    · simp [classAbsGo, classAbsSpec, hm]
  | proj s i x ihx =>
    intro hd memo hm
    rcases hd with _ | ⟨h, _ | n⟩
    · unfold classAbsGo
      split
      · rename_i r hr
        exact ⟨hm _ _ hr, hm⟩
      · obtain ⟨h1, h2⟩ := ihx none memo hm
        have hs : classAbsSpec occ none (.proj s i x) = .proj s i (classAbsSpec occ none x) := by
          simp [classAbsSpec]
        refine ⟨by simp only; rw [hs, h1], ?_⟩
        simp only
        rw [h1, ← hs]
        exact h2.insert _
    · simp [classAbsGo, classAbsSpec, hm]
    · simp [classAbsGo, classAbsSpec, hm]
  | _ =>
    intro hd memo hm
    rcases hd with _ | ⟨h, _ | n⟩ <;> simp [classAbsGo, classAbsSpec, hm]

/-- **The class abstraction is the spec.** -/
theorem classAbs_eq_spec (cls : List ClassInfo) (e : Expr) :
    classAbs cls e = classAbsSpec (classOcc? cls) none e :=
  (classAbsGo_spec _ e none {} (fun _ _ h => by simp at h)).1

end ConLeche
