module

public import ConLeche.Kernel.Inductives.RecCheck
import ConLeche.Verify.Inductives.RecCallGraph

public section

/-!
# The call graph's rank splits into strongly connected components (PRIMREC / NESTKN-RP)

The recursor check's nested route (`Kernel/Inductives/RecNestK.lean`) classifies calls
per STRONGLY CONNECTED COMPONENT of the family's call graph (`sccRK`, `hotRK`): a call
between two classes of equal rank is an intra-component one.  The class induction
(`graphInd_of_comps`, `Model/Inductives/TargetCompInd.lean`) needs exactly that fact of
the rank (`graphRank`): along an edge the rank never climbs (`graphRank_mono`), and it
stays level ONLY inside a component (`graphRank_edge_back`: an edge `c → c'` with equal
ranks has a path back `c' →* c`).

* `GReach g` — the reflexive-transitive closure of the edges;
* `reachFix_some` — the fuel `g.length ^ 2 + 1` never runs out (every non-fixed round adds
  an entry to an `n × n` matrix);
* `reachFix_inv` — every entry of the fixed point is a path, and the diagonal is set;
* `graphRank_edge_back`, `graphRank_reach_mono`.
-/

namespace ConLeche

/-- **Reachability along the edges** (reflexive, transitive). -/
inductive GReach (g : List (List Nat)) : Nat → Nat → Prop
  | refl (c : Nat) : GReach g c c
  | step {c c' c'' : Nat} : c' ∈ g.getD c [] → GReach g c' c'' → GReach g c c''

theorem GReach.trans {g : List (List Nat)} {a b c : Nat} (h₁ : GReach g a b)
    (h₂ : GReach g b c) : GReach g a c := by
  induction h₁ with
  | refl => exact h₂
  | step he _ ih => exact .step he (ih h₂)

theorem GReach.edge {g : List (List Nat)} {a b : Nat} (he : b ∈ g.getD a []) : GReach g a b :=
  .step he (.refl b)

/-- An entry of a matrix of rows. -/
@[expose] def entK (R : List (List Bool)) (c x : Nat) : Bool := (R.getD c []).getD x false

/-- A square matrix of side `n`. -/
@[expose] def SquareK (n : Nat) (R : List (List Bool)) : Prop :=
  R.length = n ∧ ∀ c, c < n → (R.getD c []).length = n

theorem entK_reachStep {g : List (List Nat)} {R : List (List Bool)} {c x : Nat}
    (hc : c < g.length) (hx : x < g.length) :
    entK (reachStep g R) c x =
      (entK R c x || (g.getD c []).any fun c' => entK R c' x) := by
  simp only [entK, reachStep, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hc, Option.map_some, Option.getD_some, List.getElem?_range hx]

theorem squareK_reachStep (g : List (List Nat)) (R : List (List Bool)) :
    SquareK g.length (reachStep g R) := by
  refine ⟨by simp [reachStep], fun c hc => ?_⟩
  simp [reachStep, List.getD_eq_getElem?_getD, List.getElem?_range hc]

/-- Out of a square matrix, every entry is unset. -/
theorem entK_out {n : Nat} {R : List (List Bool)} (hR : SquareK n R) {c x : Nat}
    (h : ¬(c < n ∧ x < n)) : entK R c x = false := by
  unfold entK
  by_cases hc : c < n
  · have hl := hR.2 c hc
    rw [List.getD_eq_getElem?_getD (l := R.getD c []), List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getD_eq_getElem?_getD (l := R), List.getElem?_eq_none (by have := hR.1; omega)]
    rfl

theorem entK_reachStep_out {g : List (List Nat)} {R : List (List Bool)} {c x : Nat}
    (h : ¬(c < g.length ∧ x < g.length)) : entK (reachStep g R) c x = false :=
  entK_out (squareK_reachStep g R) h

/-- Two square matrices with the same entries are equal. -/
theorem squareK_ext {n : Nat} {R R' : List (List Bool)} (h : SquareK n R) (h' : SquareK n R')
    (he : ∀ c x, c < n → x < n → entK R c x = entK R' c x) : R = R' := by
  apply List.ext_getElem (h.1.trans h'.1.symm)
  intro c hc hc'
  have hcn : c < n := h.1 ▸ hc
  have hl := h.2 c hcn
  have hl' := h'.2 c hcn
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at hl
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc', Option.getD_some] at hl'
  apply List.ext_getElem (hl.trans hl'.symm)
  intro x hx hx'
  have := he c x hcn (hl ▸ hx)
  simp only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc,
    List.getElem?_eq_getElem hc', Option.getD_some, List.getElem?_eq_getElem hx,
    List.getElem?_eq_getElem hx'] at this
  exact this

/-! ## The number of set entries -/

/-- The number of set entries. -/
@[expose] def totK (R : List (List Bool)) : Nat := (R.map (·.count true)).sum

theorem count_true_le_length (l : List Bool) : l.count true ≤ l.length := List.count_le_length

theorem totK_le {n : Nat} {R : List (List Bool)} (h : SquareK n R) : totK R ≤ n * n := by
  obtain ⟨hl, hr⟩ := h
  unfold totK
  have : ∀ (R : List (List Bool)) (k : Nat), (∀ c, c < R.length → (R.getD c []).length = n) →
      (R.map (·.count true)).sum ≤ R.length * n := by
    intro R
    induction R with
    | nil => intro _ _; simp
    | cons r rs ih =>
      intro k hk
      have h0 := hk 0 (by simp)
      simp only [List.getD_cons_zero] at h0
      have ht := ih k fun c hc => by
        have := hk (c + 1) (by simp; omega)
        simpa using this
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have := count_true_le_length r
      rw [Nat.succ_mul]
      omega
  have := this R 0 (fun c hc => hr c (hl ▸ hc))
  rw [hl] at this
  exact this

/-- A pointwise-larger list with one more set entry counts more. -/
theorem count_true_lt_of_imp :
    ∀ {l₁ l₂ : List Bool}, l₁.length = l₂.length →
      (∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), l₁[i] = true → l₂[i] = true) →
      ∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), l₁[i] = false → l₂[i] = true →
      l₁.count true < l₂.count true
  | [], [], _, _, i, h₁, _, _, _ => nomatch h₁
  | [], _ :: _, h, _, _, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _, _, _ => nomatch h
  | a :: as, b :: bs, hl, himp, i, h₁, h₂, hf, ht => by
    have hrest := count_true_le_of_imp (l₁ := as) (l₂ := bs) (by simpa using hl)
      fun i h₁ h₂ hi => himp (i + 1) (by simp; omega) (by simp; omega) hi
    have h0 := himp 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hf ht
      subst hf; subst ht
      simp; omega
    | succ i =>
      have := count_true_lt_of_imp (l₁ := as) (l₂ := bs) (by simpa using hl)
        (fun i h₁ h₂ hi => himp (i + 1) (by simp; omega) (by simp; omega) hi) i
        (by simp at h₁; omega) (by simp at h₂; omega) (by simpa using hf) (by simpa using ht)
      cases a <;> cases b <;> simp at h0 ⊢ <;> omega

/-- The row-wise sum grows when every row grows and one grows strictly. -/
theorem sum_lt_of_le_of_lt :
    ∀ {xs ys : List Nat}, xs.length = ys.length →
      (∀ i (h₁ : i < xs.length) (h₂ : i < ys.length), xs[i] ≤ ys[i]) →
      ∀ i (h₁ : i < xs.length) (h₂ : i < ys.length), xs[i] < ys[i] → xs.sum < ys.sum
  | [], [], _, _, i, h₁, _, _ => nomatch h₁
  | [], _ :: _, h, _, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _, _ => nomatch h
  | a :: as, b :: bs, hl, hle, i, h₁, h₂, hlt => by
    have hsle : as.sum ≤ bs.sum := by
      have key : ∀ {xs ys : List Nat}, xs.length = ys.length →
          (∀ i (h₁ : i < xs.length) (h₂ : i < ys.length), xs[i] ≤ ys[i]) → xs.sum ≤ ys.sum := by
        intro xs
        induction xs with
        | nil => intro ys h _; cases ys <;> simp_all
        | cons x xs ih =>
          intro ys h hle
          cases ys with
          | nil => simp at h
          | cons y ys =>
            have h0 := hle 0 (by simp) (by simp)
            simp only [List.getElem_cons_zero] at h0
            have := ih (ys := ys) (by simpa using h)
              fun i h₁ h₂ => hle (i + 1) (by simp; omega) (by simp; omega)
            simp only [List.sum_cons]; omega
      exact key (by simpa using hl) fun i h₁ h₂ => hle (i + 1) (by simp; omega) (by simp; omega)
    have h0 := hle 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at h0
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero] at hlt
      simp only [List.sum_cons]; omega
    | succ i =>
      have := sum_lt_of_le_of_lt (xs := as) (ys := bs) (by simpa using hl)
        (fun i h₁ h₂ => hle (i + 1) (by simp; omega) (by simp; omega)) i
        (by simp at h₁; omega) (by simp at h₂; omega) (by simpa using hlt)
      simp only [List.sum_cons]; omega

/-- **A round that changes the matrix sets a new entry.** -/
theorem totK_reachStep_lt {g : List (List Nat)} {R : List (List Bool)}
    (hR : SquareK g.length R) (hne : reachStep g R ≠ R) : totK R < totK (reachStep g R) := by
  have hS := squareK_reachStep g R
  -- some entry differs; by inflation it is new
  have hex : ∃ c x, c < g.length ∧ x < g.length ∧ entK R c x = false ∧
      entK (reachStep g R) c x = true := by
    apply Classical.byContradiction
    intro hno
    apply hne
    refine squareK_ext hS hR fun c x hc hx => ?_
    rw [entK_reachStep hc hx]
    cases h1 : entK R c x
    · cases h2 : (g.getD c []).any fun c' => entK R c' x
      · rfl
      · exact absurd ⟨c, x, hc, hx, h1, by rw [entK_reachStep hc hx, h1, h2]; rfl⟩ hno
    · rfl
  obtain ⟨c, x, hc, hx, hf, ht⟩ := hex
  unfold totK
  have hlenR : R.length = g.length := hR.1
  have hlenS : (reachStep g R).length = g.length := hS.1
  refine sum_lt_of_le_of_lt (by simp [hlenR, hlenS]) (fun i h₁ h₂ => ?_) c
    (by simp [hlenR]; exact hc) (by simp [hlenS]; exact hc) ?_
  · simp only [List.getElem_map]
    have hi : i < g.length := by simpa [hlenR] using h₁
    have hrl := hR.2 i hi
    have hsl := hS.2 i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₁),
      Option.getD_some] at hrl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₂),
      Option.getD_some] at hsl
    refine count_true_le_of_imp (hrl.trans hsl.symm) fun y hy₁ hy₂ hy => ?_
    have hy' : y < g.length := hrl ▸ hy₁
    have := entK_reachStep (g := g) (R := R) hi hy'
    have e1 : entK R i y = true := by
      simp only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₁),
        Option.getD_some, List.getElem?_eq_getElem hy₁]; exact hy
    rw [e1, Bool.true_or] at this
    simp only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h₂),
      Option.getD_some, List.getElem?_eq_getElem hy₂] at this
    exact this
  · simp only [List.getElem_map]
    have hrl := hR.2 c hc
    have hsl := hS.2 c hc
    have hc₁ : c < R.length := by omega
    have hc₂ : c < (reachStep g R).length := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc₁, Option.getD_some] at hrl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc₂, Option.getD_some] at hsl
    refine count_true_lt_of_imp (hrl.trans hsl.symm) (fun y hy₁ hy₂ hy => ?_) x
      (by omega) (by omega) ?_ ?_
    · have hy' : y < g.length := hrl ▸ hy₁
      have := entK_reachStep (g := g) (R := R) hc hy'
      have e1 : entK R c y = true := by
        simp only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc₁,
          Option.getD_some, List.getElem?_eq_getElem hy₁]; exact hy
      rw [e1, Bool.true_or] at this
      simp only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc₂,
        Option.getD_some, List.getElem?_eq_getElem hy₂] at this
      exact this
    · simp only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc₁,
        Option.getD_some, List.getElem?_eq_getElem (show x < R[c].length by omega)] at hf
      exact hf
    · simp only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc₂,
        Option.getD_some, List.getElem?_eq_getElem (show x < (reachStep g R)[c].length by omega)]
        at ht
      exact ht

/-- **The fuel suffices** once it exceeds the entries still unset. -/
theorem reachFix_some_of {g : List (List Nat)} :
    ∀ (fuel : Nat) (R : List (List Bool)), SquareK g.length R →
      g.length * g.length < fuel + totK R → ∃ R', reachFix g fuel R = some R'
  | 0, R, hR, hlt => by have := totK_le hR; omega
  | fuel + 1, R, hR, hlt => by
    unfold reachFix
    split
    · exact ⟨R, rfl⟩
    · next hne =>
      have hne' : reachStep g R ≠ R := fun h => hne (by rw [h]; exact beq_self_eq_true R)
      have := totK_reachStep_lt hR hne'
      exact reachFix_some_of fuel _ (squareK_reachStep g R) (by omega)

/-- The identity matrix. -/
@[expose] def idK (n : Nat) : List (List Bool) :=
  (List.range n).map fun c => (List.range n).map (· == c)

theorem squareK_idK (n : Nat) : SquareK n (idK n) := by
  refine ⟨by simp [idK], fun c hc => ?_⟩
  simp [idK, List.getD_eq_getElem?_getD, List.getElem?_range hc]

theorem entK_idK {n c x : Nat} (hc : c < n) (hx : x < n) : entK (idK n) c x = (x == c) := by
  simp [entK, idK, List.getD_eq_getElem?_getD, List.getElem?_range hc, List.getElem?_range hx]

theorem entK_idK_imp {n c x : Nat} (h : entK (idK n) c x = true) : x = c := by
  by_cases hb : c < n ∧ x < n
  · rw [entK_idK hb.1 hb.2] at h; simpa using h
  · rw [entK_out (squareK_idK n) hb] at h; exact absurd h (by simp)

/-- **The rank's fixed point exists** at the check's fuel. -/
theorem reachFix_some (g : List (List Nat)) :
    ∃ R, reachFix g (g.length * g.length + 1) (idK g.length) = some R :=
  reachFix_some_of _ _ (squareK_idK _) (by omega)

/-! ## The fixed point's entries -/

/-- What every round preserves: a square matrix, the diagonal set, every entry a path. -/
@[expose] def ReachInvK (g : List (List Nat)) (R : List (List Bool)) : Prop :=
  SquareK g.length R ∧ (∀ c, c < g.length → entK R c c = true) ∧
    ∀ c x, entK R c x = true → GReach g c x

theorem reachInvK_step {g : List (List Nat)} {R : List (List Bool)} (h : ReachInvK g R) :
    ReachInvK g (reachStep g R) := by
  obtain ⟨hS, hd, hp⟩ := h
  refine ⟨squareK_reachStep g R, fun c hc => ?_, fun c x he => ?_⟩
  · rw [entK_reachStep hc hc, hd c hc, Bool.true_or]
  · by_cases hb : c < g.length ∧ x < g.length
    · rw [entK_reachStep hb.1 hb.2] at he
      rcases Bool.or_eq_true_iff.mp he with he | he
      · exact hp c x he
      · obtain ⟨c', hc', he'⟩ := List.any_eq_true.mp he
        exact .step hc' (hp c' x he')
    · rw [entK_reachStep_out hb] at he; exact absurd he (by simp)

theorem reachInvK_fix {g : List (List Nat)} :
    ∀ {fuel : Nat} {R₀ R : List (List Bool)}, ReachInvK g R₀ → reachFix g fuel R₀ = some R →
      ReachInvK g R
  | 0, _, _, _, h => nomatch h
  | fuel + 1, R₀, R, hI, h => by
    unfold reachFix at h
    split at h
    · obtain rfl := Option.some.inj h; exact hI
    · exact reachInvK_fix (reachInvK_step hI) h

theorem reachInvK_idK (g : List (List Nat)) : ReachInvK g (idK g.length) := by
  refine ⟨squareK_idK _, fun c hc => by rw [entK_idK hc hc]; simp, fun c x he => ?_⟩
  obtain rfl := entK_idK_imp he
  exact .refl _

/-- The rank, at its fixed point. -/
theorem graphRank_eq {g : List (List Nat)} {R : List (List Bool)}
    (hR : reachFix g (g.length * g.length + 1) (idK g.length) = some R) :
    graphRank g = R.map (·.count true) := by
  unfold graphRank
  have : ((List.range g.length).map fun c => (List.range g.length).map (· == c))
      = idK g.length := rfl
  rw [this, hR]

/-- **An edge that keeps the rank level has a path back**: at the fixed point the
caller's reach holds the callee's (`reachStep_row`); equal counts make the rows equal, so
the callee reaches the caller (the caller's diagonal). -/
theorem graphRank_edge_back {g : List (List Nat)} {c c' : Nat} (hc : c < g.length)
    (hc' : c' < g.length) (he : c' ∈ g.getD c [])
    (hr : (graphRank g).getD c' 0 = (graphRank g).getD c 0) : GReach g c' c := by
  obtain ⟨R, hRf⟩ := reachFix_some g
  have hI := reachInvK_fix (reachInvK_idK g) hRf
  have hfix := reachFix_fix hRf
  obtain ⟨⟨hlen, hrow⟩, hdiag, hpath⟩ := hI
  rw [graphRank_eq hRf] at hr
  have hcR : c < R.length := by omega
  have hc'R : c' < R.length := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hc'R,
    Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem hcR, Option.map_some, Option.getD_some] at hr
  have hrc := hrow c hc
  have hrc' := hrow c' hc'
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcR, Option.getD_some] at hrc
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc'R, Option.getD_some] at hrc'
  -- the callee's row implies the caller's
  have himp : ∀ x (h₁ : x < R[c'].length) (h₂ : x < R[c].length), R[c'][x] = true →
      R[c][x] = true := by
    intro x h₁ h₂ hx
    have hx' : x < g.length := hrc' ▸ h₁
    have := entK_reachStep (g := g) (R := R) hc hx'
    rw [hfix] at this
    have e1 : entK R c' x = true := by
      simp only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc'R,
        Option.getD_some, List.getElem?_eq_getElem h₁]; exact hx
    have : entK R c x = true := by
      rw [this, Bool.or_eq_true_iff]
      exact Or.inr (List.any_eq_true.mpr ⟨c', he, e1⟩)
    simpa only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcR,
      Option.getD_some, List.getElem?_eq_getElem h₂] using this
  -- equal counts: the caller's diagonal entry is in the callee's row
  have hcc : R[c'][c]'(by omega) = true := by
    apply Classical.byContradiction
    intro hne
    have hf : R[c'][c]'(by omega) = false := by simpa using hne
    have hdc := hdiag c hc
    have ht : R[c][c]'(by omega) = true := by
      simpa only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcR,
        Option.getD_some, List.getElem?_eq_getElem (show c < R[c].length by omega)] using hdc
    have := count_true_lt_of_imp (hrc'.trans hrc.symm) himp c (by omega) (by omega) hf ht
    omega
  apply hpath c' c
  simpa only [entK, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc'R,
    Option.getD_some, List.getElem?_eq_getElem (show c < R[c'].length by omega)] using hcc

/-- An edge never climbs the rank, at every pair (out of range the rank reads `0`). -/
theorem graphRank_mono' {g : List (List Nat)} {c c' : Nat} (he : c' ∈ g.getD c []) :
    (graphRank g).getD c' 0 ≤ (graphRank g).getD c 0 := by
  have hc : c < g.length := by
    apply Classical.byContradiction
    intro h
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at he
    simp at he
  by_cases hc' : c' < g.length
  · exact graphRank_mono hc hc' he
  · have hlen : (graphRank g).length = g.length := by
      unfold graphRank; split <;> simp_all
      next R hR =>
        have := (reachInvK_fix (reachInvK_idK g) (by exact hR)).1.1
        simpa using this
    rw [List.getD_eq_getElem?_getD (l := graphRank g) (i := c'),
      List.getElem?_eq_none (by omega)]
    exact Nat.zero_le _

/-- **The rank never climbs along a path.** -/
theorem graphRank_reach_mono {g : List (List Nat)} {c c' : Nat} (h : GReach g c c') :
    (graphRank g).getD c' 0 ≤ (graphRank g).getD c 0 := by
  induction h with
  | refl => exact Nat.le_refl _
  | step he _ ih => exact Nat.le_trans ih (graphRank_mono' he)

/-- Classes on a cycle share their rank. -/
theorem graphRank_comp_eq {g : List (List Nat)} {c c' : Nat} (h₁ : GReach g c c')
    (h₂ : GReach g c' c) : (graphRank g).getD c' 0 = (graphRank g).getD c 0 :=
  Nat.le_antisymm (graphRank_reach_mono h₁) (graphRank_reach_mono h₂)

end ConLeche
