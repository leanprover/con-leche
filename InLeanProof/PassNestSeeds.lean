module

public import InLeanProof.PassNestWalk

/-!
# O7-positivity: the seeds' walk against master's (task #451, lane O7-positivity)

`nestSeedsI_run`: the classes the recursors eliminate, walked as container
instantiations met at the empty frame stack (`nestSeeds`): each seed's fuel
is master's (`whnfWalkFuel_TrS`), its instantiation's type
(`nestInstTypeI_run`) and its frame (`nestContKeyI_run`, the walk at that
fuel by `nestPosI_run`).  The seeds are taken as their readings
(`trKey`), the form `classSeedsI_run` gives master's `classSeeds` in; what a
seed must satisfy (`SeedOkI`: levels with a reading, parameters readable,
scoped at the holes' depth and closed) is what master's `nestSeedOf_ds` and
`nestSeedOf_closed` give of master's seeds.
-/

public section

namespace InLeanProof

open Lean InLean ConLeche.Cached

/-- A seed as the walk needs it: levels with a reading, parameters readable,
scoped at `d`, closed. -/
@[expose] def SeedOkI (s : InLean.CState) (d : Nat) (q : InLean.NestKey × Nat) : Prop :=
  q.1.lvls.all okLv = true ∧ ∀ a ∈ q.1.ds, TOk s d a

theorem SeedOkI.mono {s₀ s₁ : InLean.CState} (ht : TabLe s₀ s₁) {d : Nat}
    {q : InLean.NestKey × Nat} (h : SeedOkI s₀ d q) :
    SeedOkI s₁ d q ∧ trKey s₁ q.1 = trKey s₀ q.1 := by
  refine ⟨⟨h.1, TOk_all_mono ht h.2⟩, ?_⟩
  have hok : OkSL s₀ q.1.ds = true := by
    simp only [OkSL, List.all_eq_true]; exact fun a ha => (h.2 a ha).1
  simp only [trKey, TrSL_of_tabLe ht hok]

/-- A seed's fuel, read: master's on the readings of its parameters. -/
theorem seedFuel_tr (s : InLean.CState) (ds : List Lean.Expr) (a : Nat) :
    ds.foldl (fun a d => max a (InLean.whnfWalkFuel d)) a =
      (TrSL s ds).foldl (fun a d => max a (ConLeche.whnfWalkFuel d)) a := by
  induction ds generalizing a with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldl_cons, TrSL_cons]
    rw [whnfWalkFuel_TrS s d]
    exact ih _

/-- **The seeds walked** (`nestSeeds`): each seed's instantiation met at the
empty frame stack, at the seed's own fuel; master's on the readings. -/
theorem nestSeedsI_run {fe : InLean.FEnv} {L : ConLeche.Env} {ctx : InLean.NestCtx}
    {cctx : ConLeche.NestCtx} (hJ : JobEnvI fe L) (hRF : ReducedFormerSimI) :
    ∀ (ks : List (InLean.NestKey × Nat)) (st : InLean.NestState) {s₀ s' : InLean.CState}
      {v : InLean.NestState},
      CSOKI .verified false L s₀ → WalkRel fe L s₀ ctx cctx → StOk s₀ st →
      (∀ q ∈ ks, SeedOkI s₀ (ctx.hiAt 0) q) →
      InLean.nestSeeds .verified fe ctx ks st s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ StOk s' v ∧
        Runs (ConLeche.nestSeeds (ConLeche.fueledOpsM .verified) L cctx
          (ks.map fun q => (trKey s₀ q.1, q.2)) (trSt s₀ st)) (trSt s' v)
  | [], st, s₀, s', v, hs, _, hst, _, h => by
    unfold InLean.nestSeeds at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs, TabLe.refl _, hst, ?_⟩
    unfold ConLeche.nestSeeds
    exact Runs.pure _
  | (key, nPc) :: ks, st, s₀, s', v, hs, hW, hst, hks, h => by
    obtain ⟨hlv, hdsT⟩ := hks (key, nPc) List.mem_cons_self
    have hds : OkSL s₀ key.ds = true := by
      simp only [OkSL, List.all_eq_true]; exact fun a ha => (hdsT a ha).1
    unfold InLean.nestSeeds at h
    simp only at h
    obtain ⟨⟨k, cty⟩, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hok₁, hcl₁, hws₁, hR1⟩ := nestInstTypeI_run hJ hRF hW.canon hW.fe hW.find
      hW.sort hW.sortOk hs hlv hds (fun a ha => (hdsT a ha).2.2) h1
    have hcty : GrpOk s₁ key.ds [(key.cname, cty)] := by
      intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      refine ⟨hok₁, hcl₁, fun d hd => hws₁ d ?_⟩
      intro a ha
      rw [← TrS_of_tabLe ht₁ (hdsT a ha).1]
      exact hd a ha
    obtain ⟨⟨kd, st₁⟩, s₂, h2, h⟩ := bind_run h
    simp only at h
    obtain ⟨hs₂, ht₂, hst₂, hR2⟩ := nestContKeyI_run hJ hRF (nestPosI_run hJ hRF _) [] 0
      key.cname key.lvls key.ds nPc cty st hlv hs₁ (hW.mono ht₁) (fun _ h => nomatch h)
      (hst.mono ht₁).1 (okSL_of_tabLe ht₁ hds) (by simpa using TOk_all_mono ht₁ hdsT) hcty h2
    have ht12 := ht₁.trans ht₂
    obtain ⟨hs', ht', hst', hR3⟩ := nestSeedsI_run hJ hRF ks st₁ hs₂ (hW.mono ht12) hst₂
      (fun q hq => (SeedOkI.mono ht12 (hks q (List.mem_cons_of_mem _ hq))).1) h
    refine ⟨hs', ht12.trans ht', hst', ?_⟩
    rw [List.map_congr_left (fun q hq => by
      rw [(SeedOkI.mono ht12 (hks q (List.mem_cons_of_mem _ hq))).2])] at hR3
    rw [(hst.mono ht₁).2, TrSL_of_tabLe ht₁ hds] at hR2
    have hF : InLean.fuelSlack = ConLeche.fuelSlack := rfl
    rw [seedFuel_tr s₀ key.ds, hF] at hR2
    unfold ConLeche.nestSeeds
    simp only [List.map_cons, hiAt_rel hW.canon]
    refine Runs.bind hR1 ?_
    simp only [trKey, List.map_nil] at hR2 ⊢
    refine Runs.bind hR2 ?_
    exact hR3

end InLeanProof
