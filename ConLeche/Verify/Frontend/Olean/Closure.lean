module

public import ConLeche.Frontend.Olean.Closure
import ConLeche.Verify.Frontend.ModelIO
import Std.Data.HashSet.Lemmas

/-!
# The module walk

`closureOrder_ok`: where the walk has a value, it holds every root, and every module in
it comes after all of that module's imports (`ClosedOrder`).

The walk is a depth-first search on an explicit stack, an entry `(m, false)` a module to
expand and `(m, true)` a module whose imports are being walked.  What it keeps
(`WalkGood`): above an entry `(m, true)`, every import of `m` not yet done is still on the
stack, so that all of them are done when that entry comes up; and an entry `(k, false)`
whose module has been seen is done, or has its `(k, true)` above it, so that skipping it
when it comes up loses nothing.
-/

public section

namespace ConLeche.Frontend.Olean

open ConLeche

/-- **The module order of a closure**: each module, in the model, has imports, all of them
before it. -/
@[expose] def ClosedOrder (sp : SearchPath) (fs : FS) (out : Array Name) : Prop :=
  ∀ k (hk : k < out.size), ∃ imps, (moduleImports sp out[k] : ModelIO _) fs (.ok (.ok imps)) ∧
    ∀ i ∈ imps, i.module ∈ out.toList.take k

/-- A module done, or still on the stack above. -/
def Cover (done : Std.HashSet Name) (above : List (Name × Bool)) (i : Name) : Prop :=
  done.contains i = true ∨ (i, false) ∈ above ∨ (i, true) ∈ above

/-- **What the walk keeps of its stack**, `above` the entries over the rest. -/
def WalkGood (sp : SearchPath) (fs : FS) (done seen : Std.HashSet Name) :
    List (Name × Bool) → List (Name × Bool) → Prop
  | _, [] => True
  | above, (m, true) :: rest =>
    (∃ imps, (moduleImports sp m : ModelIO _) fs (.ok (.ok imps)) ∧
      ∀ i ∈ imps, Cover done above i.module) ∧ WalkGood sp fs done seen ((m, true) :: above) rest
  | above, (k, false) :: rest =>
    (seen.contains k = true → done.contains k = true ∨ (k, true) ∈ above) ∧
      WalkGood sp fs done seen ((k, false) :: above) rest

theorem WalkGood.mono {sp : SearchPath} {fs : FS} {d d' s s' : Std.HashSet Name}
    {above above' : List (Name × Bool)}
    (hc : ∀ a i, Cover d (a ++ above) i → Cover d' (a ++ above') i)
    (hs : ∀ a k, s'.contains k = true →
      (s.contains k = true → d.contains k = true ∨ (k, true) ∈ a ++ above) →
      d'.contains k = true ∨ (k, true) ∈ a ++ above') :
    ∀ (t a : List (Name × Bool)), WalkGood sp fs d s (a ++ above) t →
      WalkGood sp fs d' s' (a ++ above') t
  | [], _, _ => trivial
  | (m, true) :: rest, a, h => by
    obtain ⟨⟨imps, h1, h2⟩, h3⟩ := h
    exact ⟨⟨imps, h1, fun i hi => hc a _ (h2 i hi)⟩,
      WalkGood.mono hc hs rest ((m, true) :: a) h3⟩
  | (k, false) :: rest, a, h => by
    obtain ⟨h1, h3⟩ := h
    exact ⟨fun hk => hs a k hk h1, WalkGood.mono hc hs rest ((k, false) :: a) h3⟩

/-- Unseen modules pushed. -/
theorem WalkGood.kids {sp : SearchPath} {fs : FS} {d s : Std.HashSet Name} :
    ∀ (ks : List Name) (above t : List (Name × Bool)), (∀ k ∈ ks, s.contains k = false) →
      WalkGood sp fs d s (ks.reverse.map (·, false) ++ above) t →
      WalkGood sp fs d s above (ks.map (·, false) ++ t)
  | [], _, _, _, h => by simpa using h
  | k :: ks, above, t, hu, h => by
    refine ⟨fun hk => ?_, ?_⟩
    · rw [hu k List.mem_cons_self] at hk
      cases hk
    · refine WalkGood.kids ks _ t (fun x hx => hu x (List.mem_cons_of_mem _ hx)) ?_
      simpa using h

/-- **What the walk keeps.** -/
structure WalkInv (sp : SearchPath) (fs : FS) (R : Array Name) (stack : List (Name × Bool))
    (seen done : Std.HashSet Name) (out : Array Name) : Prop where
  outDone : ∀ m, m ∈ out ↔ done.contains m = true
  closed : ClosedOrder sp fs out
  good : WalkGood sp fs done seen [] stack
  roots : ∀ r ∈ R, Cover done stack r

/-- A module whose imports are done goes last. -/
theorem ClosedOrder.push {sp : SearchPath} {fs : FS} {out : Array Name} {m : Name}
    {imps : Array ImportRec} (hc : ClosedOrder sp fs out)
    (hm : (moduleImports sp m : ModelIO _) fs (.ok (.ok imps))) (hi : ∀ i ∈ imps, i.module ∈ out) :
    ClosedOrder sp fs (out.push m) := by
  intro k hk
  rw [Array.size_push] at hk
  by_cases hlt : k < out.size
  · obtain ⟨is, h1, h2⟩ := hc k hlt
    refine ⟨is, by rwa [Array.getElem_push_lt hlt], fun i hm' => ?_⟩
    rw [Array.toList_push, List.take_append_of_le_length (by simp; omega)]
    exact h2 i hm'
  · obtain rfl : k = out.size := by omega
    refine ⟨imps, by simpa using hm, fun i hm' => ?_⟩
    rw [Array.toList_push, List.take_append_of_le_length (by simp),
      List.take_of_length_le (by simp)]
    exact Array.mem_toList_iff.mpr (hi i hm')

/-- **The walk's value.** -/
theorem closureGo_ok {sp : SearchPath} {fs : FS} {R : Array Name} :
    ∀ (fuel : Nat) (stack : List (Name × Bool)) (seen done : Std.HashSet Name) (out res : Array Name),
      WalkInv sp fs R stack seen done out →
      (closureGo sp fuel stack seen done out : ModelIO _) fs (.ok (.ok res)) →
      ClosedOrder sp fs res ∧ ∀ r ∈ R, r ∈ res := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack seen done out res hi h
    cases stack with
    | nil =>
      simp only [closureGo, ModelIO.pure_iff, Except.ok.injEq] at h
      cases h
      refine ⟨hi.closed, fun r hr => (hi.outDone r).2 ?_⟩
      rcases hi.roots r hr with h | h | h
      · exact h
      · cases h
      · cases h
    | cons x t =>
      simp [closureGo] at h
  | succ fuel ih =>
    intro stack seen done out res hi h
    match stack, hi, h with
    | [], hi, h =>
      simp only [closureGo, ModelIO.pure_iff, Except.ok.injEq] at h
      cases h
      refine ⟨hi.closed, fun r hr => (hi.outDone r).2 ?_⟩
      rcases hi.roots r hr with h | h | h
      · exact h
      · cases h
      · cases h
    | (m, true) :: rest, hi, h =>
      simp only [closureGo] at h
      obtain ⟨⟨imps, h1, h2⟩, h3⟩ := hi.good
      refine ih rest seen (done.insert m) (out.push m) res ⟨?_, ?_, ?_, ?_⟩ h
      · intro x
        simp only [Array.mem_push, hi.outDone x, Std.HashSet.contains_insert, Bool.or_eq_true,
          beq_iff_eq]
        constructor
        · rintro (h | h)
          · exact .inr h
          · exact .inl h.symm
        · rintro (h | h)
          · exact .inr h.symm
          · exact .inl h
      · refine hi.closed.push h1 fun i hm => (hi.outDone _).2 ?_
        rcases h2 i hm with h | h | h
        · exact h
        · cases h
        · cases h
      · refine WalkGood.mono (above := [(m, true)]) (above' := []) ?_ ?_ rest [] h3
        · intro a i hc
          simp only [List.append_nil]
          rcases hc with hc | hc | hc
          · exact .inl (by simp [Std.HashSet.contains_insert, hc])
          · rcases List.mem_append.mp hc with hc | hc
            · exact .inr (.inl hc)
            · simp at hc
          · rcases List.mem_append.mp hc with hc | hc
            · exact .inr (.inr hc)
            · simp only [List.mem_singleton, Prod.mk.injEq, and_true] at hc
              subst hc
              exact .inl (by simp [Std.HashSet.contains_insert])
        · intro a k hk h4
          simp only [List.append_nil]
          rcases h4 hk with h5 | h5
          · exact .inl (by simp [Std.HashSet.contains_insert, h5])
          · rcases List.mem_append.mp h5 with h5 | h5
            · exact .inr h5
            · simp only [List.mem_singleton, Prod.mk.injEq, and_true] at h5
              subst h5
              exact .inl (by simp [Std.HashSet.contains_insert])
      · intro r hr
        rcases hi.roots r hr with hc | hc | hc
        · exact .inl (by simp [Std.HashSet.contains_insert, hc])
        · rcases List.mem_cons.mp hc with hc | hc
          · simp at hc
          · exact .inr (.inl hc)
        · simp only [List.mem_cons, Prod.mk.injEq, and_true] at hc
          rcases hc with rfl | hc
          · exact .inl (by simp [Std.HashSet.contains_insert])
          · exact .inr (.inr hc)
    | (m, false) :: rest, hi, h =>
      obtain ⟨h1, h3⟩ := hi.good
      simp only [closureGo] at h
      split at h
      · rename_i hseen
        have hd : done.contains m = true := by
          rcases h1 hseen with h4 | h4
          · exact h4
          · cases h4
        refine ih rest seen done out res ⟨hi.outDone, hi.closed, ?_, ?_⟩ h
        · refine WalkGood.mono (above := [(m, false)]) (above' := []) ?_ ?_ rest [] h3
          · intro a i hc
            simp only [List.append_nil]
            rcases hc with hc | hc | hc
            · exact .inl hc
            · rcases List.mem_append.mp hc with hc | hc
              · exact .inr (.inl hc)
              · simp only [List.mem_singleton, Prod.mk.injEq, and_true] at hc
                subst hc
                exact .inl hd
            · rcases List.mem_append.mp hc with hc | hc
              · exact .inr (.inr hc)
              · simp at hc
          · intro a k hk h4
            simp only [List.append_nil]
            rcases h4 hk with h5 | h5
            · exact .inl h5
            · rcases List.mem_append.mp h5 with h5 | h5
              · exact .inr h5
              · simp at h5
        · intro r hr
          rcases hi.roots r hr with hc | hc | hc
          · exact .inl hc
          · simp only [List.mem_cons, Prod.mk.injEq, and_true] at hc
            rcases hc with rfl | hc
            · exact .inl hd
            · exact .inr (.inl hc)
          · rcases List.mem_cons.mp hc with hc | hc
            · simp at hc
            · exact .inr (.inr hc)
      · rename_i hseen
        simp only [ModelIO.bind_ok] at h
        obtain ⟨y, hy, h⟩ := h
        rcases y with e | imps
        · simp at h
        · simp only at h
          cases hf : (imps.map (·.module)).find? (fun i => (seen.insert m).contains i && !done.contains i) with
          | some c =>
            simp only [hf] at h
            simp at h
          | none =>
            simp only [hf] at h
            have hno : ∀ i ∈ imps, (seen.insert m).contains i.module = true →
                done.contains i.module = true := by
              intro i hm' hs
              have := Array.find?_eq_none.mp hf i.module (by
                exact Array.mem_map.mpr ⟨i, hm', rfl⟩)
              simpa [hs] using this
            have hmn : seen.contains m = false := by simpa using hseen
            let ks := (imps.map (·.module)).toList.filter (fun x => !(seen.insert m).contains x)
            have hk : ∀ k ∈ ks, (seen.insert m).contains k = false := by
              intro k hm'
              simpa using (List.mem_filter.mp hm').2
            have hrevk : ∀ x, (x, false) ∈ ks.reverse.map (·, false) ↔ x ∈ ks := by
              intro x
              simp
            refine ih _ (seen.insert m) done out res ⟨hi.outDone, hi.closed, ?_, ?_⟩ h
            · refine WalkGood.kids ks [] _ hk ?_
              refine ⟨⟨imps, hy, fun i hm' => ?_⟩, ?_⟩
              · by_cases hs : (seen.insert m).contains i.module = true
                · exact .inl (hno i hm' hs)
                · refine .inr (.inl ?_)
                  simp only [List.append_nil]
                  refine (hrevk _).2 (List.mem_filter.mpr ⟨?_, by simpa using hs⟩)
                  simp only [Array.mem_toList_iff]
                  exact Array.mem_map.mpr ⟨i, hm', rfl⟩
              · refine WalkGood.mono (above := [(m, false)])
                  (above' := (m, true) :: (ks.reverse.map (·, false) ++ [])) ?_ ?_ rest [] h3
                · intro a i hc
                  rcases hc with hc | hc | hc
                  · exact .inl hc
                  · rcases List.mem_append.mp hc with hc | hc
                    · exact .inr (.inl (List.mem_append_left _ hc))
                    · simp only [List.mem_singleton, Prod.mk.injEq, and_true] at hc
                      subst hc
                      exact .inr (.inr (by simp))
                  · rcases List.mem_append.mp hc with hc | hc
                    · exact .inr (.inr (List.mem_append_left _ hc))
                    · simp at hc
                · intro a k hk' h4
                  by_cases hkm : k = m
                  · subst hkm
                    exact .inr (by simp)
                  · have hks : seen.contains k = true := by
                      simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at hk'
                      rcases hk' with h6 | h6
                      · exact absurd h6.symm hkm
                      · exact h6
                    rcases h4 hks with h5 | h5
                    · exact .inl h5
                    · rcases List.mem_append.mp h5 with h5 | h5
                      · exact .inr (List.mem_append_left _ h5)
                      · simp at h5
            · intro r hr
              rcases hi.roots r hr with hc | hc | hc
              · exact .inl hc
              · simp only [List.mem_cons, Prod.mk.injEq, and_true] at hc
                rcases hc with rfl | hc
                · exact .inr (.inr (by simp))
                · exact .inr (.inl (by simp [hc]))
              · rcases List.mem_cons.mp hc with hc | hc
                · simp at hc
                · exact .inr (.inr (by simp [hc]))

/-- **The closure's order**: where the walk has a value, it holds every root, and every
module in it comes after all of that module's imports. -/
theorem closureOrder_ok {sp : SearchPath} {roots order : Array Name} {fs : FS}
    (h : (closureOrder sp roots : ModelIO _) fs (.ok (.ok order))) :
    ClosedOrder sp fs order ∧ ∀ r ∈ roots, r ∈ order := by
  refine closureGo_ok closureFuel _ {} {} #[] order ⟨?_, ?_, ?_, ?_⟩ h
  · intro m
    simp
  · intro k hk
    simp at hk
  · have := WalkGood.kids (sp := sp) (fs := fs) (d := {}) (s := {}) roots.toList [] []
      (fun k _ => by simp) trivial
    simpa using this
  · intro r hr
    refine .inr (.inl ?_)
    simpa using hr

end ConLeche.Frontend.Olean
