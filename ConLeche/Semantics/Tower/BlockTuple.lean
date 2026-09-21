module

public import ConLeche.Semantics.Tower.SumRecCase
@[expose] public section

/-!
# The non-dependent tuple VALUE (task #315, the uniform block route)

`ndTowerAV` (`Semantics/BasisType.lean`) spells the non-dependent pair
tower's TYPE; the block carrier's leaf also has to spell an inhabitant
of one — the operator tuple `⟨λ t. Σ_j …⟩_m` that `lfpTuple k` takes as
its second argument.  `ndMkTowerAV` is that inhabitant's spelling, the
`.psigmaMk [r, r]` tower over the same component types, and this module
carries its two laws (its value is the uniform tupler `mkTower` of the
components' values; it is graded) plus the set-level membership
`ndMkTowerSet_mem` that puts it in `ndTowerSet`.

The type arguments of `.psigmaMk` are NOT junk: the pinned pair's value
computes only at a member of the component's type and a member of the
tail tower's, which is exactly what the tuple's own typing gives.  The
fibre argument is a `λ` whose body is the TAIL's type tower, so that
tower starts at depth `1` — the reason `ndTowerAV` lifts its components
to their own depth itself.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower (mkTower projS)

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The value -/

/-- The non-dependent tuple value at level `r`: `⟨G s, …, G (s+n-1)⟩`,
with the component TYPES `Gty` at the base frame (the tail tower lifts
its own components past the fibre binder). -/
def ndMkTowerAV (r : Nat) (Gty G : Nat → AnnotTerm) : Nat → Nat → AnnotTerm
  | _, 0 => .const .punitUnit [r]
  | s, n + 1 =>
    AnnotTerm.mkAppN (.const .psigmaMk [r, r])
      [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
       G s, ndMkTowerAV r Gty G (s + 1) n]

/-- The tuple value's set: the uniform tupler over the components. -/
noncomputable def ndMkTowerSet (g : Nat → V) : Nat → Nat → V
  | _, 0 => pt
  | s, n + 1 => spair (g s) (ndMkTowerSet g (s + 1) n)

theorem ndMkTowerSet_eq_mkTower (g : Nat → V) :
    ∀ (n s : Nat), ndMkTowerSet g s n = mkTower ((List.range n).map fun i => g (s + i))
  | 0, _ => rfl
  | n + 1, s => by
    show spair (g s) (ndMkTowerSet g (s + 1) n) = _
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    show _ = mkTower (g (s + 0) :: _)
    rw [Nat.add_zero, ndMkTowerSet_eq_mkTower g n (s + 1)]
    congr 2
    refine List.map_congr_left fun i _ => ?_
    show g (s + 1 + i) = g (s + (i + 1))
    rw [show s + 1 + i = s + (i + 1) from by omega]

/-- **Intro**: a tuple whose components sit in the tower's is a member
of the tower's carrier. -/
theorem ndMkTowerSet_mem {r : Nat} (hr : r ≠ 0) {F g : Nat → V} :
    ∀ (n s : Nat), (∀ m, m < s + n → g m ∈ˢ F m) →
      ndMkTowerSet g s n ∈ˢ ndTowerSet V r F s n
  | 0, _, _ => pt_mem_unitSet
  | n + 1, s, hg => by
    show spair (g s) (ndMkTowerSet g (s + 1) n)
      ∈ˢ sigmaSet r (F s) fun _ => ndTowerSet V r F (s + 1) n
    exact spair_mem hr (hg s (by omega))
      (ndMkTowerSet_mem hr n (s + 1) fun m hm => hg m (by omega))

theorem ndMkTowerSet_zero (g : Nat → V) (n : Nat) :
    ndMkTowerSet g 0 n = mkTower ((List.range n).map g) := by
  rw [ndMkTowerSet_eq_mkTower]
  congr 1
  exact List.map_congr_left fun i _ => by rw [Nat.zero_add]

theorem projS_ndMkTowerSet {g : Nat → V} :
    ∀ (n s i : Nat), i < n → projS i (ndMkTowerSet g s n) = g (s + i)
  | 0, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, s, 0, _ => by
    show sfst (spair (g s) (ndMkTowerSet g (s + 1) n)) = g (s + 0)
    rw [sfst_spair, Nat.add_zero]
  | n + 1, s, i + 1, hi => by
    show projS i (ssnd (spair (g s) (ndMkTowerSet g (s + 1) n))) = g (s + (i + 1))
    rw [ssnd_spair, projS_ndMkTowerSet n (s + 1) i (Nat.lt_of_succ_lt_succ hi),
      show s + 1 + i = s + (i + 1) from by omega]

/-! ## The pinned pair constructor's four-step product -/

/-- The four-step product `psigmaMk.{r,r}` inhabits, at the joint level
`max r r = r`. -/
theorem psigmaMkV_rr_mem {r : Nat} (hr : r ≠ 0) :
    psigmaMkV V r r ∈ˢ piR r (univ r : V) fun A =>
      piR r (psigmaFibreSpace V r A) fun B =>
        piR r A fun a => piR r (SetTheory.app B a) fun _ =>
          sigmaSet r A fun x => SetTheory.app B x := by
  have hmax : Nat.max r r = r := Nat.max_self r
  rw [psigmaMkV, hmax]
  exact lamR_mem fun A _ => lamR_mem fun B _ => lamR_mem fun a ha =>
    lamR_mem fun b hb => spair_mem hr ha hb

/-! ## The tuple value's two laws -/

/-- **The tuple value reads back as the uniform tupler of its
components, and is graded.**  Both halves at once: the grading's app
slots need the value's own memberships. -/
theorem ndMkTowerAV_facts {r : Nat} (hr : r ≠ 0) {Gty G : Nat → AnnotTerm} {F g : Nat → V}
    {ρ : Nat → V} :
    ∀ (n s : Nat),
      (∀ m, m < s + n → interp V ρ (Gty m) = F m) →
      (∀ m, m < s + n → WellDenoted V ρ (Gty m)) →
      (∀ m, m < s + n → F m ∈ˢ (univ r : V)) →
      (∀ m, m < s + n → interp V ρ (G m) = g m) →
      (∀ m, m < s + n → WellDenoted V ρ (G m)) →
      (∀ m, m < s + n → g m ∈ˢ F m) →
      interp V ρ (ndMkTowerAV r Gty G s n) = ndMkTowerSet g s n ∧
        WellDenoted V ρ (ndMkTowerAV r Gty G s n)
  | 0, _, _, _, _, _, _, _ => ⟨rfl, trivial⟩
  | n + 1, s, hGty, hGtyok, hF, hG, hGok, hg => by
    have hvac : ¬ r + 1 = 0 := Nat.succ_ne_zero r
    have hA : interp V ρ (Gty s) = F s := hGty s (by omega)
    have hAu : interp V ρ (Gty s) ∈ˢ (univ r : V) := hA ▸ hF s (by omega)
    have htail : ∀ x : V, interp V (cons x ρ) (ndTowerAV r Gty (s + 1) 1 n)
        = ndTowerSet V r F (s + 1) n := fun x =>
      ndTowerAV_interp V n (s + 1) 1 (cons x ρ)
        (by rw [shiftE_succ_cons, shiftE_zero_zero]) (fun m hm => hGty m (by omega))
        (fun m hm => hF m (by omega))
    have hBv : interp V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n))
        = lamR (r + 1) (interp V ρ (Gty s))
            fun _ => ndTowerSet V r F (s + 1) n := by
      rw [interp_lam]
      exact lamR_congr fun x _ => htail x
    have hBmem : interp V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n))
        ∈ˢ psigmaFibreSpace V r (interp V ρ (Gty s)) := by
      rw [hBv]
      show lamR (r + 1) (interp V ρ (Gty s)) (fun _ => ndTowerSet V r F (s + 1) n)
        ∈ˢ piR (r + 1) (interp V ρ (Gty s)) (fun _ => (univ r : V))
      exact lamR_mem fun _ _ => ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)
    have hBok : WellDenoted V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n)) := by
      rw [WellDenoted_lam]
      refine ⟨hGtyok s (by omega), fun x _ => ?_, fun _ => (univ r : V),
        fun x _ => ?_, fun h0 => absurd h0 hvac⟩
      · exact ndTowerAV_wellDenoted V n (s + 1) 1 (cons x ρ)
          (by rw [shiftE_succ_cons, shiftE_zero_zero]) (fun m hm => hGty m (by omega))
          (fun m hm => hGtyok m (by omega)) (fun m hm => hF m (by omega))
      · rw [htail x]
        exact ndTowerSet_mem_univ V n (s + 1) fun m hm => hF m (by omega)
    have hav : interp V ρ (G s) = g s := hG s (by omega)
    have hamem : interp V ρ (G s) ∈ˢ interp V ρ (Gty s) := by rw [hav, hA]; exact hg s (by omega)
    obtain ⟨hbv, hbok⟩ := ndMkTowerAV_facts hr n (s + 1) (fun m hm => hGty m (by omega))
      (fun m hm => hGtyok m (by omega)) (fun m hm => hF m (by omega))
      (fun m hm => hG m (by omega)) (fun m hm => hGok m (by omega))
      (fun m hm => hg m (by omega))
    have hBapp : SetTheory.app (interp V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n)))
        (interp V ρ (G s)) = ndTowerSet V r F (s + 1) n := by
      rw [hBv, app_lamR_pos hvac hamem]
    have hbmem : interp V ρ (ndMkTowerAV r Gty G (s + 1) n)
        ∈ˢ SetTheory.app (interp V ρ (.lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n)))
            (interp V ρ (G s)) := by
      rw [hBapp, hbv]
      exact ndMkTowerSet_mem hr n (s + 1) fun m hm => hg m (by omega)
    -- the four-step application chain
    have hmk : interp V ρ (.const .psigmaMk [r, r]) = psigmaMkV V r r := rfl
    have hchain : AppChainOk (interp V ρ (.const .psigmaMk [r, r]))
        (([Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
           G s, ndMkTowerAV r Gty G (s + 1) n] : List AnnotTerm).map (interp V ρ)) := by
      rw [hmk]
      have hstep := psigmaMkV_rr_mem (V := V) hr
      have h1 := app_mem_piR_pos hr hstep hAu
      have h2 := app_mem_piR_pos hr h1 hBmem
      have h3 := app_mem_piR_pos hr h2 hamem
      intro l hl
      match l, hl with
      | 0, _ => exact ⟨r, univ r, _, hstep, hAu, fun h0 => absurd h0 hr⟩
      | 1, _ =>
        exact ⟨r, psigmaFibreSpace V r (interp V ρ (Gty s)), _, h1, hBmem,
          fun h0 => absurd h0 hr⟩
      | 2, _ => exact ⟨r, interp V ρ (Gty s), _, h2, hamem, fun h0 => absurd h0 hr⟩
      | 3, _ => exact ⟨r, _, _, h3, hbmem, fun h0 => absurd h0 hr⟩
    have hcl := mkAppN_wellDenoted_of_chain (f := (.const .psigmaMk [r, r] : AnnotTerm))
      (args := [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
        G s, ndMkTowerAV r Gty G (s + 1) n]) (σ := ρ) trivial
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact hGtyok s (by omega)
        · exact hBok
        · exact hGok s (by omega)
        · exact hbok)
      hchain
    refine ⟨?_, hcl.1⟩
    show interp V ρ (AnnotTerm.mkAppN (.const .psigmaMk [r, r])
      [Gty s, .lam (r + 1) (Gty s) (ndTowerAV r Gty (s + 1) 1 n),
       G s, ndMkTowerAV r Gty G (s + 1) n]) = _
    rw [hcl.2, hmk]
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkV V r r)
      (interp V ρ (Gty s))) _) _) _ = _
    rw [psigmaMkV_app V hAu hBmem hamem hbmem, if_neg (by rw [show Nat.max r r = r from Nat.max_self r]; exact hr)]
    show spair (interp V ρ (G s)) (interp V ρ (ndMkTowerAV r Gty G (s + 1) n)) = _
    rw [hav, hbv]
    rfl

end ConLeche.Semantics
