import Setlec.SetR.Annot.SortCoh.Mono

/-!
# Run-level sort coherence — the trio discharge tier, (B), the summit skeleton

Split from `SortCoh.lean` (pure motion; the umbrella
`Setlec.SetR.Annot.SortCoh` re-exports the whole family).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify
open Setlec (CheckMode Env Expr Name Level inferTypeCore whnf whnfCore
  isDefEqCore unfoldDefinition)

/-! ## The trio discharge tier

The recorded recipe, mechanized: the loop assembly
(`typeTransportLoopF_of`), the collision engine
(`typeWhnfLE_collide` — spine fact at the head-normal form of a
sort-converging subject is pinned to the successor sort), and the
ctor-headed route (`ctorHead_no_sort` — no spine: nat continuation is
`NatStepNoSort` verbatim, δ is refuted by the ctor head, stuck
collides an app head with `.sort`). -/

section Discharge
variable {μ : CheckMode} {env : Env}

/-- The loop assembly: chain transport from the step species plus the
invariant supply chain, by one budget induction. -/
theorem typeTransportLoopF_of
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) :
    TypeTransportLoopF μ env := by
  intro g l
  induction l with
  | zero => intro d e s w h; exact nomatch h
  | succ l ih =>
    intro d e s w h hI hT
    rw [whnfLoop_succ] at h
    obtain ⟨e₁, hwcg, htri⟩ := whnfStep_decompose h
    have hwc : whnfCore μ env g d e = .ok e₁ := hwcg
    have hI₁ := hIC hwc hI
    have hT₁ := hTC hwc hI hT
    rcases htri with ⟨x, hrn, hk⟩ | ⟨hrn, x, hud, hk⟩ | ⟨hrn, hud, rfl⟩
    · exact ih hk (hIN hrn hI₁) (hTN hrn hI₁ hT₁)
    · exact ih hk (hID hud hI₁) (hTD hud hI₁ hT₁)
    · exact hT₁

/-- The collision engine. -/
theorem typeWhnfLE_collide (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    {g l f d : Nat} {a a' w : Expr} {ℓ : Level}
    (hI : SubjInv d a)
    (hwc : whnfCore μ env f d a = .ok a')
    (hloop : Setlec.whnfLoop (Setlec.pureFns μ env g) env d l a
      = .ok (.sort ℓ))
    (hW : TypeWhnfLE μ env d a' w) : w = .sort (.succ ℓ) := by
  cases l with
  | zero => exact nomatch hloop
  | succ l =>
    rw [whnfLoop_succ] at hloop
    obtain ⟨a₁, hwcg, htri⟩ := whnfStep_decompose hloop
    obtain rfl : a' = a₁ :=
      ((KnotFuelDet_of_mono hm).2.2.1
        (hwcg : whnfCore μ env g d a = .ok a₁) hwc).symm
    have hI₁ : SubjInv d a' := hIC hwc hI
    rcases htri with ⟨x, hrn, hk⟩ | ⟨hrn, x, hud, hk⟩ | ⟨hrn, hud, rfl⟩
    · exact TypeWhnfLE_det hm
        (hT hk (hIN hrn hI₁) (hTN hrn hI₁ hW)) typeWhnfLE_sort
    · exact TypeWhnfLE_det hm
        (hT hk (hID hud hI₁) (hTD hud hI₁ hW)) typeWhnfLE_sort
    · exact TypeWhnfLE_det hm hW typeWhnfLE_sort

/-- Constructor heads never unfold. -/
theorem unfoldDefinition_ctor_none {c : Name} {us : List Level}
    {e : Expr} {cv : Setlec.ConstantVal} {nP nF : Nat}
    (hhd : e.getAppFn = .const c us)
    (hf : env.find? c = some (.ctorInfo cv nP nF)) :
    Setlec.unfoldDefinition env e = none := by
  simp only [Setlec.unfoldDefinition, hhd, hf]

/-- The ctor-headed route: a head-normal form with a stored-inert
constant head never continues to a sort. -/
theorem ctorHead_no_sort (hm : KnotFuelMono μ env)
    (hN : NatStepNoSort μ env)
    {g l f d : Nat} {a a' : Expr} {c : Name} {us : List Level}
    {ℓ : Level}
    (hwc : whnfCore μ env f d a = .ok a')
    (hloop : Setlec.whnfLoop (Setlec.pureFns μ env g) env d l a
      = .ok (.sort ℓ))
    (hhd : a'.getAppFn = .const c us)
    (hud : Setlec.unfoldDefinition env a' = none) : False := by
  have h0 := hloop
  cases l with
  | zero => exact nomatch hloop
  | succ l =>
    rw [whnfLoop_succ] at hloop
    obtain ⟨a₁, hwcg, htri⟩ := whnfStep_decompose hloop
    obtain rfl : a' = a₁ :=
      ((KnotFuelDet_of_mono hm).2.2.1
        (hwcg : whnfCore μ env g d a = .ok a₁) hwc).symm
    rcases htri with ⟨x, hrn, hk⟩ | ⟨hrn, x, hud', hk⟩ | ⟨hrn, hud', rfl⟩
    · exact hN hwc hrn h0
    · rw [hud] at hud'; exact nomatch hud'
    · simp [Setlec.Expr.getAppFn] at hhd

/-- Literal sorts are never unit-like (computation leaf). -/
theorem isUnitLikeTy_sort {ℓ : Level} :
    Setlec.isUnitLikeTy env (.sort ℓ) = false := rfl

/-- **Eta routing discharged** (against the spine): `etaCert`'s own
`whnf (infer a')` run lands at a `∀`, which the collision engine pins
to the successor sort — shape clash. -/
theorem etaSortVacuity_of (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) {Q : Nat → Expr → Expr → Prop} :
    EtaSortVacuity μ env Q := by
  intro g g' l f d a a' n ty body m ℓ hI _hQv hwc hcert hloop
  unfold Setlec.etaCert at hcert
  simp only [Bind.bind, Except.bind] at hcert
  cases hinf : (Setlec.pureFns μ env g).infer d a' with
  | error err => rw [hinf] at hcert; exact nomatch hcert
  | ok tb =>
  rw [hinf] at hcert
  simp only [] at hcert
  cases hw : (Setlec.pureFns μ env g).whnf d tb with
  | error err => rw [hw] at hcert; exact nomatch hcert
  | ok wtb =>
  rw [hw] at hcert
  simp only [] at hcert
  split at hcert
  · next n₂ ty₂ body₂ m₂ =>
    obtain ⟨gw, lw, -, hlw⟩ :=
      whnf_peel (hw : whnf μ env g d tb = .ok (.forallE n₂ ty₂ body₂ m₂))
    have hW : TypeWhnfLE μ env d a' (.forallE n₂ ty₂ body₂ m₂) :=
      ⟨g, tb, hinf, gw, lw, hlw⟩
    exact nomatch (typeWhnfLE_collide hm hT hTD hTN hIC hID hIN
      hI hwc hloop hW)
  · exact nomatch hcert

/-- **Probe routing discharged** (the double spine): the unit check's
own `whnf ta` run collides to the successor sort, killing the unit
branch by computation (`isUnitLikeTy_sort`); the sort branch's
level-2 fact `TypeWhnfLE ta (.sort uT)` transports along `ta`'s own
whnf chain (entered through `InvPreserveInferF`) onto the successor
sort, pinning `uT` to a double successor — refuting the cert's
`isEquiv uT 0` through `Level.isEquiv_sound`. -/
theorem proofIrrel_no_sort (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    {g g' l f d : Nat} {a a' b' : Expr} {ℓ : Level}
    (hI : SubjInv d a)
    (hwc : whnfCore μ env f d a = .ok a')
    (hpi : Setlec.proofIrrel (Setlec.pureFns μ env g) env d a' b'
      = .ok true)
    (hloop : Setlec.whnfLoop (Setlec.pureFns μ env g') env d l a
      = .ok (.sort ℓ)) : False := by
  unfold Setlec.proofIrrel at hpi
  simp only [Bind.bind, Except.bind] at hpi
  cases hinfa : (Setlec.pureFns μ env g).infer d a' with
  | error err => rw [hinfa] at hpi; exact nomatch hpi
  | ok ta =>
  rw [hinfa] at hpi
  simp only [] at hpi
  cases hwta : (Setlec.pureFns μ env g).whnf d ta with
  | error err => rw [hwta] at hpi; exact nomatch hpi
  | ok wta =>
  rw [hwta] at hpi
  simp only [] at hpi
  have hW1 : TypeWhnfLE μ env d a' wta := by
    obtain ⟨gw, lw, -, hlw⟩ :=
      whnf_peel (hwta : whnf μ env g d ta = .ok wta)
    exact ⟨g, ta, hinfa, gw, lw, hlw⟩
  obtain rfl : wta = .sort (.succ ℓ) :=
    typeWhnfLE_collide hm hT hTD hTN hIC hID hIN hI hwc hloop hW1
  rw [isUnitLikeTy_sort, if_neg Bool.false_ne_true] at hpi
  cases hinfta : (Setlec.pureFns μ env g).infer d ta with
  | error err => rw [hinfta] at hpi; exact nomatch hpi
  | ok sa =>
  rw [hinfta] at hpi
  simp only [] at hpi
  cases hwsa : (Setlec.pureFns μ env g).whnf d sa with
  | error err => rw [hwsa] at hpi; exact nomatch hpi
  | ok wsa =>
  rw [hwsa] at hpi
  simp only [] at hpi
  split at hpi
  · next uT =>
    -- the second spine application, along `ta`'s own whnf chain
    have hIta : SubjInv d ta := hInf hinfa (hIC hwc hI)
    have hW2 : TypeWhnfLE μ env d ta (.sort uT) := by
      obtain ⟨gs, ls, -, hls⟩ :=
        whnf_peel (hwsa : whnf μ env g d sa = .ok (.sort uT))
      exact ⟨g, sa, hinfta, gs, ls, hls⟩
    obtain ⟨gt, lt, -, hlt⟩ :=
      whnf_peel (hwta : whnf μ env g d ta = .ok (.sort (.succ ℓ)))
    have hW3 : TypeWhnfLE μ env d (.sort (.succ ℓ)) (.sort uT) :=
      hT hlt hIta hW2
    obtain rfl : uT = .succ (.succ ℓ) :=
      Setlec.Expr.sort.inj (TypeWhnfLE_det hm hW3 typeWhnfLE_sort)
    cases hlift : Setlec.liftFueled "level comparison"
        (Level.isEquiv (.succ (.succ ℓ)) .zero)
        (m := Setlec.CheckM) with
    | error err => rw [hlift] at hpi; exact nomatch hpi
    | ok okA =>
    rw [hlift] at hpi
    simp only [] at hpi
    rw [Setlec.liftFueled.eq_def] at hlift
    split at hlift
    · next okA' hEq =>
      obtain rfl : okA' = okA := by
        simpa [pure, Except.pure] using hlift
      cases okA' with
      | true =>
        have hev := Level.isEquiv_sound hEq (fun _ => 0)
        simp only [Setlec.Level.eval] at hev
        omega
      | false =>
        -- the b-side walk: every terminal returns `false` or throws
        cases hinfb : (Setlec.pureFns μ env g).infer d b' with
        | error err => rw [hinfb] at hpi; exact nomatch hpi
        | ok tb =>
        rw [hinfb] at hpi
        simp only [] at hpi
        cases hinftb : (Setlec.pureFns μ env g).infer d tb with
        | error err => rw [hinftb] at hpi; exact nomatch hpi
        | ok sb =>
        rw [hinftb] at hpi
        simp only [] at hpi
        cases hwsb : (Setlec.pureFns μ env g).whnf d sb with
        | error err => rw [hwsb] at hpi; exact nomatch hpi
        | ok wsb =>
        rw [hwsb] at hpi
        simp only [] at hpi
        split at hpi
        · next vT =>
          cases hliftB : Setlec.liftFueled "level comparison"
              (Level.isEquiv vT .zero) (m := Setlec.CheckM) with
          | error err => rw [hliftB] at hpi; exact nomatch hpi
          | ok okB => rw [hliftB] at hpi; exact nomatch hpi
        · exact nomatch hpi
    · exact nomatch hlift
  · exact nomatch hpi

/-- **Rescue routing discharged**: the five-way read of `stuckIrrel`.
The a-directed pair/struct-eta branches need no spine (the subject is
ctor-headed — `ctorHead_no_sort`); the b-directed branches and the
unit cert collide a const-app-headed `w` with the successor sort; the
fallback is the probe (`proofIrrel_no_sort`). -/
theorem rescueSortVacuity_of (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    (hN : NatStepNoSort μ env) {Q : Nat → Expr → Expr → Prop} :
    RescueSortVacuity μ env Q := by
  intro g g' l f d a a' b' ℓ hI _hQv hwc hsi hloop
  unfold Setlec.stuckIrrel at hsi
  simp only [Bind.bind, Except.bind] at hsi
  -- branch 1: pairEtaCert a' b' (a-directed; ctor-headed route)
  cases h1 : Setlec.pairEtaCert μ (Setlec.pureFns μ env g) env d a' b' with
  | error err => rw [h1] at hsi; exact nomatch hsi
  | ok c1 =>
  rw [h1] at hsi
  simp only [] at hsi
  cases c1 with
  | true =>
    unfold Setlec.pairEtaCert at h1
    split at h1
    · next c us pα pβ s₁ s₂ =>
      split at h1
      · next _cvm hfind =>
        exact ctorHead_no_sort hm hN hwc hloop
          (show Setlec.Expr.getAppFn _ = .const c us from rfl)
          (unfoldDefinition_ctor_none rfl hfind)
      · exact nomatch h1
    · exact nomatch h1
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 2: pairEtaCert b' a' (b-directed; spine)
  cases h2 : Setlec.pairEtaCert μ (Setlec.pureFns μ env g) env d b' a' with
  | error err => rw [h2] at hsi; exact nomatch hsi
  | ok c2 =>
  rw [h2] at hsi
  simp only [] at hsi
  cases c2 with
  | true =>
    unfold Setlec.pairEtaCert at h2
    simp only [Bind.bind, Except.bind] at h2
    split at h2
    · next cB usB pαB pβB s₁B s₂B =>
      split at h2
      · next _cvmB hfindB =>
        cases hinf2 : (Setlec.pureFns μ env g).infer d a' with
        | error err => rw [hinf2] at h2; exact nomatch h2
        | ok tb =>
        rw [hinf2] at h2
        simp only [] at h2
        cases hw2 : (Setlec.pureFns μ env g).whnf d tb with
        | error err => rw [hw2] at h2; exact nomatch h2
        | ok wtb =>
        rw [hw2] at h2
        simp only [] at h2
        split at h2
        · next c' us' A B =>
          obtain ⟨gw, lw, -, hlw⟩ :=
            whnf_peel (hw2 : whnf μ env g d tb = .ok _)
          exact nomatch (typeWhnfLE_collide hm hT hTD hTN hIC hID hIN
            hI hwc hloop (⟨g, tb, hinf2, gw, lw, hlw⟩ :
              TypeWhnfLE μ env d a' _))
        · exact nomatch h2
      · exact nomatch h2
    · exact nomatch h2
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 3: structEtaCert a' b' (a-directed; ctor-headed route)
  cases h3 : Setlec.structEtaCert μ (Setlec.pureFns μ env g) env d a' b' with
  | error err => rw [h3] at hsi; exact nomatch hsi
  | ok c3 =>
  rw [h3] at hsi
  simp only [] at hsi
  cases c3 with
  | true =>
    unfold Setlec.structEtaCert at h3
    simp only [Bind.bind, Except.bind] at h3
    cases hinf3 : (Setlec.pureFns μ env g).infer d b' with
    | error err => rw [hinf3] at h3; exact nomatch h3
    | ok tb =>
    rw [hinf3] at h3
    simp only [] at h3
    cases hw3 : (Setlec.pureFns μ env g).whnf d tb with
    | error err => rw [hw3] at h3; exact nomatch h3
    | ok wtb =>
    rw [hw3] at h3
    simp only [] at h3
    unfold Setlec.structEtaCertWith at h3
    split at h3
    · next c us heqa =>
      split at h3
      · next cvc cnP cnF hfinda =>
        exact ctorHead_no_sort hm hN hwc hloop heqa
          (unfoldDefinition_ctor_none heqa hfinda)
      · exact nomatch h3
    · exact nomatch h3
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 4: structEtaCert b' a' (b-directed; spine)
  cases h4 : Setlec.structEtaCert μ (Setlec.pureFns μ env g) env d b' a' with
  | error err => rw [h4] at hsi; exact nomatch hsi
  | ok c4 =>
  rw [h4] at hsi
  simp only [] at hsi
  cases c4 with
  | true =>
    unfold Setlec.structEtaCert at h4
    simp only [Bind.bind, Except.bind] at h4
    cases hinf4 : (Setlec.pureFns μ env g).infer d a' with
    | error err => rw [hinf4] at h4; exact nomatch h4
    | ok tb =>
    rw [hinf4] at h4
    simp only [] at h4
    cases hw4 : (Setlec.pureFns μ env g).whnf d tb with
    | error err => rw [hw4] at h4; exact nomatch h4
    | ok wtb =>
    rw [hw4] at h4
    simp only [] at h4
    obtain rfl : wtb = .sort (.succ ℓ) := by
      obtain ⟨gw, lw, -, hlw⟩ :=
        whnf_peel (hw4 : whnf μ env g d tb = .ok wtb)
      exact typeWhnfLE_collide hm hT hTD hTN hIC hID hIN
        hI hwc hloop ⟨g, tb, hinf4, gw, lw, hlw⟩
    unfold Setlec.structEtaCertWith at h4
    split at h4
    · next cB usB heqb =>
      split at h4
      · next cvcB cnPB cnFB hfindb =>
        split at h4
        · split at h4
          · next T us' heqw => exact nomatch heqw
          · exact nomatch h4
        · exact nomatch h4
      · exact nomatch h4
    · exact nomatch h4
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 5: structUnitCert (spine at the unit type's const head)
  cases h5 : Setlec.structUnitCert (Setlec.pureFns μ env g) env d a' b' with
  | error err => rw [h5] at hsi; exact nomatch hsi
  | ok c5 =>
  rw [h5] at hsi
  simp only [] at hsi
  cases c5 with
  | true =>
    unfold Setlec.structUnitCert at h5
    simp only [Bind.bind, Except.bind] at h5
    cases hinf5 : (Setlec.pureFns μ env g).infer d a' with
    | error err => rw [hinf5] at h5; exact nomatch h5
    | ok ta =>
    rw [hinf5] at h5
    simp only [] at h5
    cases hw5 : (Setlec.pureFns μ env g).whnf d ta with
    | error err => rw [hw5] at h5; exact nomatch h5
    | ok wta =>
    rw [hw5] at h5
    simp only [] at h5
    obtain rfl : wta = .sort (.succ ℓ) := by
      obtain ⟨gw, lw, -, hlw⟩ :=
        whnf_peel (hw5 : whnf μ env g d ta = .ok wta)
      exact typeWhnfLE_collide hm hT hTD hTN hIC hID hIN
        hI hwc hloop ⟨g, ta, hinf5, gw, lw, hlw⟩
    split at h5
    · next T us' heqw => exact nomatch heqw
    · exact nomatch h5
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  -- branch 6: the proofIrrel fallback = the probe
  exact proofIrrel_no_sort hm hT hTD hTN hIC hID hIN hInf
    hI hwc hsi hloop

/-- The probe routing, packaged. -/
theorem probeSortVacuity_of (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env)
    (hTD : TypeTransportDeltaF μ env) (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    {Q : Nat → Expr → Expr → Prop} :
    ProbeSortVacuity μ env Q := by
  intro g g' l f d a a' b' ℓ hI _hQv hwc hpi hloop
  exact proofIrrel_no_sort hm hT hTD hTN hIC hID hIN hInf
    hI hwc hpi hloop

/-! ### The spine routing, reduced to its both-δ core

The `defeqSpine` scoping map (graded-unknown discipline): a `true`
verdict pins both subjects const-headed with the *same* head `n`,
equal arg counts, `isEquivList`-equivalent levels, and pointwise
`defEqList`-certified args.  On a sort-converging subject the loop's
stuck leg clashes with the const head and the nat leg is
`NatStepNoSort` verbatim — so both sides take δ steps, unfolding the
*same stored value* at equivalent levels with certified args.  That
both-δ residue is the routing's irreducible core, named below; the
reduction `spineSortAgree_of` is proved here, the core's supplier is
graded (DESIGN — it embeds certified-pair convergence at argument
positions, not level bookkeeping). -/

/-- **The both-δ core** (graded unknown #1, reduced form, restated
dual-success per the unhold's Gap 2): a same-head
`defeqSpine`-certified pair whose members' own chains reach literal
sorts has equal numerals.  The sort runs are stated ON `a'`/`b'` (the
(A-T) liveness pattern — the consumer assembles them from its
decomposition; the discharge reads the δ steps off the runs), and
the no-cumulativity finding fixes the discharge route: both sides'
type-sorts are ONE level expression in `us`/`us'` (Gap 1 =
`DeltaSortLinked` at two-instantiation strength), transported along
each run by `TypeTransportLoopF`, pinned by `typeWhnfLE_sort` + det,
and equated by `isEquivList` soundness. -/
def DeltaSpineSortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {a' b' : Expr} {ℓa ℓb : Level},
    SubjInv d a' → SubjInv d b' → PairedLeaves a' b' → Q d a' b' →
    Setlec.defeqSpine (Setlec.pureFns μ env fc) env d a' b'
      = .ok true →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la a'
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb b'
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The spine routing reduced**: `SpineSortAgree` from the both-δ
core — the stuck legs clash with `defeqSpine`'s const heads, the nat
legs are `NatStepNoSort`, the δ-δ leg is the core with `SubjInv`
carried across the whnfCore step. -/
theorem spineSortAgree_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop} (hm : KnotFuelMono μ env)
    (hB : BoolCtorsInert env) (hIC : InvPreserveCoreF μ env)
    (hLC : PairedPreserveCoreF μ env)
    (hQC : QPreserveCoreF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hD : DeltaSpineSortAgree μ env φ Q) :
    SpineSortAgree μ env φ Q := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc l d ga la gb lb f₁ f₂ a b a' b' ℓa ℓb hIa hIb hPab hQab
    hc hwa hwb hs ha hb
  cases la with
  | zero => exact nomatch ha
  | succ la' =>
  cases lb with
  | zero => exact nomatch hb
  | succ lb' =>
  have haD := ha
  rw [whnfLoop_succ] at haD
  obtain ⟨a₁, hwca, htriA⟩ := whnfStep_decompose haD
  obtain rfl : a' = a₁ :=
    ((KnotFuelDet_of_mono hm).2.2.1
      (hwca : whnfCore μ env ga d a = .ok a₁) hwa).symm
  have hbD := hb
  rw [whnfLoop_succ] at hbD
  obtain ⟨b₁, hwcb, htriB⟩ := whnfStep_decompose hbD
  obtain rfl : b' = b₁ :=
    ((KnotFuelDet_of_mono hm).2.2.1
      (hwcb : whnfCore μ env gb d b = .ok b₁) hwb).symm
  rcases htriA with ⟨x, hrx, -⟩ | ⟨hrga, xa, hux, hkx⟩ |
    ⟨-, -, hstopA⟩
  · exact (hN hwa hrx ha).elim
  · rcases htriB with ⟨y, hry, -⟩ | ⟨hrgb, xb, huy, hky⟩ |
      ⟨-, -, hstopB⟩
    · exact (hN hwb hry hb).elim
    · -- both-δ: assemble the dual-success runs on `a'`/`b'` (the
      -- spine cert's const heads make whnfCore re-idem) and hand
      -- the core its inputs.
      obtain ⟨na, usa, heqa⟩ : ∃ n us, a'.getAppFn = .const n us := by
        have hs' := hs
        unfold Setlec.defeqSpine at hs'
        split at hs'
        · next n us heq => exact ⟨n, us, heq⟩
        · exact nomatch hs'
      obtain ⟨nb, usb, heqb⟩ : ∃ n us, b'.getAppFn = .const n us := by
        have hs' := hs
        unfold Setlec.defeqSpine at hs'
        split at hs'
        · next n us heq =>
          split at hs'
          · next n' us' heq' => exact ⟨n', us', heq'⟩
          · exact nomatch hs'
        · exact nomatch hs'
      have ha' : Setlec.whnfLoop (Setlec.pureFns μ env (max f₁ ga))
          env d (la' + 1) a' = .ok (.sort ℓa) := by
        rw [whnfLoop_succ]
        exact whnfStep_assemble_delta
          (hm.2.2.1 (Nat.le_max_left f₁ ga)
            (whnfCore_reidem_const hm hwa heqa))
          (hm.2.2.2.2 (Nat.le_max_right f₁ ga) hrga) hux
          (whnfLoop_r_mono hm (Nat.le_max_right f₁ ga) hkx)
      have hb' : Setlec.whnfLoop (Setlec.pureFns μ env (max f₂ gb))
          env d (lb' + 1) b' = .ok (.sort ℓb) := by
        rw [whnfLoop_succ]
        exact whnfStep_assemble_delta
          (hm.2.2.1 (Nat.le_max_left f₂ gb)
            (whnfCore_reidem_const hm hwb heqb))
          (hm.2.2.2.2 (Nat.le_max_right f₂ gb) hrgb) huy
          (whnfLoop_r_mono hm (Nat.le_max_right f₂ gb) hky)
      exact hD (hIC hwa hIa) (hIC hwb hIb)
        ((hLC hwb ((hLC hwa hPab).symm)).symm)
        (hQs (hQC hwb (hQs (hQC hwa hQab)))) hs ha' hb'
    · obtain rfl := hstopB
      unfold Setlec.defeqSpine at hs
      split at hs
      · exact nomatch hs
      · exact nomatch hs
  · obtain rfl := hstopA
    unfold Setlec.defeqSpine at hs
    exact nomatch hs

/-- **The shell against the species tier**: `EnsureSortAgreeR` from
the env fact, the invariant supply chain, the three transport step
species, and the spine routing.  The PSS trio is discharged — the
branch's remaining unknowns are (F)-species-shaped plus
`SpineSortAgree`. -/
theorem ensureSortAgreeR_of_species {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hB : BoolCtorsInert env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hS : SpineSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q :=
  have hm : KnotFuelMono μ env := knotFuelMono μ env
  have hT : TypeTransportLoopF μ env :=
    typeTransportLoopF_of hTC hTD hTN hIC hID hIN
  ensureSortAgreeR_of_pss (Q := Q) hB hIC hID hIN hLC hLD hLN
    hQC hQD hQN hQs
    (probeSortVacuity_of hm hT hTD hTN hIC hID hIN hInf)
    (rescueSortVacuity_of hm hT hTD hTN hIC hID hIN hInf
      (natStepNoSort_of hB))
    (etaSortVacuity_of hm hT hTD hTN hIC hID hIN) hS

/-- **The branch primitive at its irreducibles**: `EnsureSortAgreeR`
from the env fact, the three transport step species, the four
invariant preservers, and the both-δ spine core.  Everything else on
the defeq branch is discharged. -/
theorem ensureSortAgreeR_of_core {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hB : BoolCtorsInert env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hD : DeltaSpineSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q :=
  ensureSortAgreeR_of_species (Q := Q) hB hTC hTD hTN hIC hID hIN
    hInf hLC hLD hLN hQC hQD hQN hQs
    (spineSortAgree_of (Q := Q) (knotFuelMono μ env) hB hIC hLC hQC
      hQs hD)

/-! ## (B)'s dual shell — `sortOfE` agreement on the same decomposition

The type-level dual of the (A) shell, on the settled motive shape
(`SubjInv` per side + concrete cross-`PairedLeaves` + the abstract
`Q`-slot).  Bases and re-entries are proved here (determinism,
arithmetic, and the transport species); the congruence tier and the
type-level vacuities are the named routings below, each at its own
seal.  Three map corrections landed with the build: `etaL`/`etaR`/
`lamCong` all die on `LamTySortVacuity` (a λ's inferred type is a
`∀`, never a sort — the eta cert is not even consumed), and
`natL`/`natR` are plain re-entries through the nat transport species,
not vacuities. -/

/-- `SortOfLE` transports across a head-normalization step (the
(F-core) sort instance). -/
theorem sortOfLE_step_core {φ : Name → Nat}
    (hTC : TypeTransportCoreF μ env) {f d : Nat} {e e' : Expr}
    {u : Nat} (hwc : whnfCore μ env f d e = .ok e') (hI : SubjInv d e)
    (h : SortOfLE μ env φ d e u) : SortOfLE μ env φ d e' u := by
  obtain ⟨ℓ, hW, hev⟩ := sortOfLE_iff_typeWhnfLE.1 h
  exact sortOfLE_iff_typeWhnfLE.2 ⟨ℓ, hTC hwc hI hW, hev⟩

/-- `SortOfLE` transports across one unfolding ((F-δ) sort
instance). -/
theorem sortOfLE_step_delta {φ : Name → Nat}
    (hTD : TypeTransportDeltaF μ env) {d : Nat} {e e' : Expr}
    {u : Nat} (hud : Setlec.unfoldDefinition env e = some e')
    (hI : SubjInv d e)
    (h : SortOfLE μ env φ d e u) : SortOfLE μ env φ d e' u := by
  obtain ⟨ℓ, hW, hev⟩ := sortOfLE_iff_typeWhnfLE.1 h
  exact sortOfLE_iff_typeWhnfLE.2 ⟨ℓ, hTD hud hI hW, hev⟩

/-- `SortOfLE` transports across one literal-acceleration step
((F-nat) sort instance). -/
theorem sortOfLE_step_nat {φ : Name → Nat}
    (hTN : TypeTransportNatF μ env) {f d : Nat} {e e' : Expr}
    {u : Nat}
    (hrn : Setlec.reduceNat (Setlec.pureFns μ env f) env d e
      = .ok (some e'))
    (hI : SubjInv d e)
    (h : SortOfLE μ env φ d e u) : SortOfLE μ env φ d e' u := by
  obtain ⟨ℓ, hW, hev⟩ := sortOfLE_iff_typeWhnfLE.1 h
  exact sortOfLE_iff_typeWhnfLE.2 ⟨ℓ, hTN hrn hI hW, hev⟩

/-- A successful loop-level sort computation on a literal sort is
the successor numeral. -/
theorem sortOfLE_sort_out {φ : Name → Nat} (hm : KnotFuelMono μ env)
    {d : Nat} {w : Level} {u : Nat}
    (h : SortOfLE μ env φ d (.sort w) u) : u = w.eval φ + 1 := by
  obtain ⟨ℓ, hW, hev⟩ := sortOfLE_iff_typeWhnfLE.1 h
  obtain rfl : ℓ = .succ w :=
    Setlec.Expr.sort.inj (TypeWhnfLE_det hm hW typeWhnfLE_sort)
  exact hev.symm

/-! ### (B)'s routed hypotheses (each at its own seal) -/

/-- Type-level probe vacuity: a `proofIrrel`-certified subject's
type never whnf-converges to a literal sort. -/
def ProbeTySortVacuity (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d : Nat} {a' b' : Expr} {ℓ : Level},
    SubjInv d a' → Q d a' b' →
    Setlec.proofIrrel (Setlec.pureFns μ env g) env d a' b' = .ok true →
    TypeWhnfLE μ env d a' (.sort ℓ) → False

/-- Type-level rescue vacuity, five-way as before. -/
def RescueTySortVacuity (μ : CheckMode) (env : Env)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d : Nat} {a' b' : Expr} {ℓ : Level},
    SubjInv d a' → Q d a' b' →
    Setlec.stuckIrrel μ (Setlec.pureFns μ env g) env d a' b'
      = .ok true →
    TypeWhnfLE μ env d a' (.sort ℓ) → False

/-- A λ's inferred type is a `∀`, never a sort — kills `etaL`,
`etaR` and `lamCong` without reading their certs. -/
def LamTySortVacuity (μ : CheckMode) (env : Env) : Prop :=
  ∀ {d : Nat} {n : Name} {ty body : Expr} {m : Setlec.BinderMeta}
    {ℓ : Level},
    TypeWhnfLE μ env d (.lam n ty body m) (.sort ℓ) → False

/-- Mixed terminal: the `Nat` literal against the stored zero. -/
def NatZeroTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {d u v : Nat},
    SortOfLE μ env φ d (.lit (.natVal 0)) u →
    SortOfLE μ env φ d (.const Setlec.natZeroName []) v → u = v

/-- Mixed terminal: successor packing, literal side left. -/
def NatSuccLTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {g d u v n : Nat} {x : Expr},
    (Setlec.pureFns μ env g).defeq d (.lit (.natVal n)) x = .ok true →
    SortOfLE μ env φ d (.lit (.natVal (n + 1))) u →
    SortOfLE μ env φ d (.app (.const Setlec.natSuccName []) x) v →
    u = v

/-- Mixed terminal: successor packing, literal side right. -/
def NatSuccRTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {g d u v n : Nat} {x : Expr},
    Setlec.unfoldableHead env
      (.app (.const Setlec.natSuccName []) x) = false →
    (Setlec.pureFns μ env g).defeq d x (.lit (.natVal n)) = .ok true →
    SortOfLE μ env φ d (.app (.const Setlec.natSuccName []) x) u →
    SortOfLE μ env φ d (.lit (.natVal (n + 1))) v → u = v

/-- Mixed terminal: the string literal against a stuck app. -/
def StrLTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {g d u v : Nat} {st : String} {cO : Name} {usO : List Level}
    {x : Expr},
    (Setlec.pureFns μ env g).defeq d (Setlec.strLitToConstructor st)
      (.app (.const cO usO) x) = .ok true →
    SortOfLE μ env φ d (.lit (.strVal st)) u →
    SortOfLE μ env φ d (.app (.const cO usO) x) v → u = v

/-- Mixed terminal: the stuck app against the string literal. -/
def StrRTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {g d u v : Nat} {st : String} {cO : Name} {usO : List Level}
    {x : Expr},
    Setlec.unfoldableHead env (.app (.const cO usO) x) = false →
    (Setlec.pureFns μ env g).defeq d (.app (.const cO usO) x)
      (Setlec.strLitToConstructor st) = .ok true →
    SortOfLE μ env φ d (.app (.const cO usO) x) u →
    SortOfLE μ env φ d (.lit (.strVal st)) v → u = v

/-- The `fvars` leaf: same index, own annotations — cross-pairing
pins the annotations equal, and `infer` is name-blind. -/
def FvarTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {d u v i : Nat} {n₁ n₂ : Name} {ty₁ ty₂ : Expr},
    SubjInv d (.fvar i n₁ ty₁) → SubjInv d (.fvar i n₂ ty₂) →
    PairedLeaves (.fvar i n₁ ty₁) (.fvar i n₂ ty₂) →
    SortOfLE μ env φ d (.fvar i n₁ ty₁) u →
    SortOfLE μ env φ d (.fvar i n₂ ty₂) v → u = v

/-- The `consts` leaf: one stored type at two equivalent level
instantiations — the spine core's argless sibling. -/
def ConstTySortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) : Prop :=
  ∀ {d u v : Nat} {n : Name} {us us' : List Level},
    Setlec.unfoldableHead env (.const n us) = false →
    Level.isEquivList us us' = some true →
    SortOfLE μ env φ d (.const n us) u →
    SortOfLE μ env φ d (.const n us') v → u = v

/-- The spine's type-level agreement (`Q`-carrying, like its (A)
sibling). -/
def SpineTySortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d u v : Nat} {a' b' : Expr},
    SubjInv d a' → SubjInv d b' → Q d a' b' →
    Setlec.defeqSpine (Setlec.pureFns μ env g) env d a' b'
      = .ok true →
    SortOfLE μ env φ d a' u → SortOfLE μ env φ d b' v → u = v

/-- The `∀`-congruence tier (the Θ-motive proper; `Q`-carrying). -/
def PiCongTySortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d u v : Nat} {n₁ n₂ : Name} {ty₁ ty₂ body₁ body₂ : Expr}
    {m₁ m₂ : Setlec.BinderMeta},
    SubjInv d (.forallE n₁ ty₁ body₁ m₁) →
    SubjInv d (.forallE n₂ ty₂ body₂ m₂) →
    PairedLeaves (.forallE n₁ ty₁ body₁ m₁)
      (.forallE n₂ ty₂ body₂ m₂) →
    Q d (.forallE n₁ ty₁ body₁ m₁) (.forallE n₂ ty₂ body₂ m₂) →
    (Setlec.pureFns μ env g).defeq d ty₁ ty₂ = .ok true →
    (Setlec.pureFns μ env g).defeq (d + 1)
      (body₁.instantiate1 (.fvar d n₁ ty₁))
      (body₂.instantiate1 (.fvar d n₂ ty₂)) = .ok true →
    SortOfLE μ env φ d (.forallE n₁ ty₁ body₁ m₁) u →
    SortOfLE μ env φ d (.forallE n₂ ty₂ body₂ m₂) v → u = v

/-- The application-congruence tier (`Q`-carrying). -/
def AppCongTySortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d u v : Nat} {f₁ a₁ f₂ a₂ : Expr},
    SubjInv d (.app f₁ a₁) → SubjInv d (.app f₂ a₂) →
    PairedLeaves (.app f₁ a₁) (.app f₂ a₂) →
    Q d (.app f₁ a₁) (.app f₂ a₂) →
    Setlec.unfoldableHead env (.app f₁ a₁) = false →
    (Expr.app f₁ a₁).getAppArgs.length =
      (Expr.app f₂ a₂).getAppArgs.length →
    (Setlec.pureFns μ env g).defeq d (Expr.app f₁ a₁).getAppFn
      (Expr.app f₂ a₂).getAppFn = .ok true →
    Setlec.defEqList (Setlec.pureFns μ env g) env d
      (Expr.app f₁ a₁).getAppArgs (Expr.app f₂ a₂).getAppArgs
      = .ok true →
    SortOfLE μ env φ d (.app f₁ a₁) u →
    SortOfLE μ env φ d (.app f₂ a₂) v → u = v

/-- The projection-congruence tier (`Q`-carrying). -/
def ProjCongTySortAgree (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {g d u v i : Nat} {s₁ s₂ : Name} {e₁ e₂ : Expr},
    SubjInv d (.proj s₁ i e₁) → SubjInv d (.proj s₂ i e₂) →
    PairedLeaves (.proj s₁ i e₁) (.proj s₂ i e₂) →
    Q d (.proj s₁ i e₁) (.proj s₂ i e₂) →
    (Setlec.pureFns μ env g).defeq d e₁ e₂ = .ok true →
    SortOfLE μ env φ d (.proj s₁ i e₁) u →
    SortOfLE μ env φ d (.proj s₂ i e₂) v → u = v

/-- The `Q`-enriched (B) claim; `SortOfAgreeR` is its `Q := True`
instance. -/
def SortOfAgreeRQ (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d : Nat} {a b : Expr} {f₁ f₂ : Nat} {u v : Nat},
    isDefEqCore μ env fc d a b = .ok true →
    Expr.WScoped d a → a.looseBVarsBounded 0 = true →
    Expr.LeavesBounded a →
    Expr.WScoped d b → b.looseBVarsBounded 0 = true →
    Expr.LeavesBounded b →
    PairedLeaves a b →
    Q d a b →
    sortOfE μ env φ f₁ d a = some u →
    sortOfE μ env φ f₂ d b = some v →
    u = v

/-- **(B)'s dual shell**: `SortOfAgreeRQ` from the transport species,
the three supply chains, and the routed hypotheses — the same
budget-only cert-loop induction as (A), at the type level. -/
theorem sortOfAgreeRQ_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeTySortVacuity μ env Q)
    (hR : RescueTySortVacuity μ env Q)
    (hLam : LamTySortVacuity μ env)
    (hZ : NatZeroTySortAgree μ env φ)
    (hSL : NatSuccLTySortAgree μ env φ)
    (hSR : NatSuccRTySortAgree μ env φ)
    (hStL : StrLTySortAgree μ env φ) (hStR : StrRTySortAgree μ env φ)
    (hF : FvarTySortAgree μ env φ) (hK : ConstTySortAgree μ env φ)
    (hSp : SpineTySortAgree μ env φ Q)
    (hPi : PiCongTySortAgree μ env φ Q)
    (hAp : AppCongTySortAgree μ env φ Q)
    (hPj : ProjCongTySortAgree μ env φ Q) :
    SortOfAgreeRQ μ env φ Q := by
  have main : ∀ (fc L : Nat) {d : Nat} {a b : Expr},
      Setlec.defeqLoop μ (Setlec.pureFns μ env fc) env d L a b
        = .ok true →
      SubjInv d a → SubjInv d b → PairedLeaves a b → Q d a b →
      ∀ {u v : Nat}, SortOfLE μ env φ d a u →
        SortOfLE μ env φ d b v → u = v := by
    intro fc L
    induction L with
    | zero => intro d a b hc; exact nomatch hc
    | succ l ih =>
      intro d a b hc hIa hIb hPab hQab u v hu hv
      rw [defeqLoop_succ] at hc
      rcases defeqStep_decompose hc with rfl | ⟨a', b', hwa, hwb, hcert⟩
      · exact SortOfLE_det hm hu hv
      have hIa' := hIC hwa hIa
      have hIb' := hIC hwb hIb
      have hu' := sortOfLE_step_core hTC hwa hIa hu
      have hv' := sortOfLE_step_core hTC hwb hIb hv
      have hPab' : PairedLeaves a' b' :=
        ((hLC hwb ((hLC hwa hPab).symm)).symm)
      have hQab' : Q d a' b' := hQs (hQC hwb (hQs (hQC hwa hQab)))
      cases hcert with
      | syn => exact SortOfLE_det hm hu' hv'
      | irrel _ _ hpi =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hu'
        exact (hP hIa' hQab' hpi hW).elim
      | natL _ _ a₂ hrn hk =>
        exact ih hk (hIN hrn hIa') hIb' (hLN hrn hPab')
          (hQN hrn hQab') (sortOfLE_step_nat hTN hrn hIa' hu') hv'
      | natR _ _ b₂ hrnA hrnB hk =>
        exact ih hk hIa' (hIN hrnB hIb')
          ((hLN hrnB hPab'.symm).symm)
          (hQs (hQN hrnB (hQs hQab'))) hu'
          (sortOfLE_step_nat hTN hrnB hIb' hv')
      | deltaL _ _ a₂ hud hk =>
        exact ih hk (hID hud hIa') hIb' (hLD hud hPab')
          (hQD hud hQab') (sortOfLE_step_delta hTD hud hIa' hu') hv'
      | deltaR _ _ b₂ hud hk =>
        exact ih hk hIa' (hID hud hIb')
          ((hLD hud hPab'.symm).symm)
          (hQs (hQD hud (hQs hQab'))) hu'
          (sortOfLE_step_delta hTD hud hIb' hv')
      | deltaB _ _ a₂ b₂ hua hub hk =>
        exact ih hk (hID hua hIa') (hID hub hIb')
          ((hLD hub ((hLD hua hPab').symm)).symm)
          (hQs (hQD hub (hQs (hQD hua hQab'))))
          (sortOfLE_step_delta hTD hua hIa' hu')
          (sortOfLE_step_delta hTD hub hIb' hv')
      | spine _ _ hs => exact hSp hIa' hIb' hQab' hs hu' hv'
      | sorts u' v' hiseq =>
        rw [sortOfLE_sort_out hm hu', sortOfLE_sort_out hm hv',
          Level.isEquiv_sound hiseq φ]
      | lits _ => exact SortOfLE_det hm hu' hv'
      | natZeroL => exact hZ hu' hv'
      | natZeroR _ => exact (hZ hv' hu').symm
      | natSuccL n x hd => exact hSL hd hu' hv'
      | natSuccR n x hua hd => exact hSR hua hd hu' hv'
      | strL st cO usO x hd => exact hStL hd hu' hv'
      | strR st cO usO x hua hd => exact hStR hua hd hu' hv'
      | fvars i n₁ n₂ ty₁ ty₂ => exact hF hIa' hIb' hPab' hu' hv'
      | consts n us us' hua hiseq => exact hK hua hiseq hu' hv'
      | piCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂ hd hbody =>
        exact hPi hIa' hIb' hPab' hQab' hd hbody hu' hv'
      | lamCong n₁ n₂ ty₁ ty₂ body₁ body₂ m₁ m₂ hd hbody =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hu'
        exact (hLam hW).elim
      | appCong f₁ a₁ f₂ a₂ hua hlen hdf hdl =>
        exact hAp hIa' hIb' hPab' hQab' hua hlen hdf hdl hu' hv'
      | projCong s₁ s₂ i e₁ e₂ hd =>
        exact hPj hIa' hIb' hPab' hQab' hd hu' hv'
      | etaL n₁ ty₁ body₁ m₁ b₂ he =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hu'
        exact (hLam hW).elim
      | etaR _ n₂ ty₂ body₂ m₂ he =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hv'
        exact (hLam hW).elim
      | rescue _ _ hsi =>
        obtain ⟨ℓ, hW, -⟩ := sortOfLE_iff_typeWhnfLE.1 hu'
        exact (hR hIa' hQab' hsi hW).elim
  intro fc d a b f₁ f₂ u v hc hwsa hba hLa hwsb hbb hLb hp hQ h₁ h₂
  cases fc with
  | zero => exact nomatch hc
  | succ fc =>
    rw [Setlec.isDefEqCore_succ] at hc
    exact main fc Setlec.defeqLoopFuel hc
      (SubjInv.of_pair hwsa hba hLa hp)
      (SubjInv.of_pair_right hwsb hbb hLb hp) hp hQ
      (SortOfLE_of_run h₁) (SortOfLE_of_run h₂)

/-! ### (B)'s mechanizable discharges: λ, fvar, probe -/

/-- `whnfCore` is the identity on `∀`s (value branch). -/
theorem whnfCore_forallE_run {μ : CheckMode} {env : Env} {f d : Nat}
    {n : Name} {ty body : Expr} {m : Setlec.BinderMeta} (hf : 1 ≤ f) :
    whnfCore μ env f d (.forallE n ty body m)
      = .ok (.forallE n ty body m) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- Inference on a `λ` only ever returns a `∀` with the λ's own
domain and meta (the clause's every success path). -/
theorem inferTypeCore_lam_out {μ : CheckMode} {env : Env} {f d : Nat}
    {n : Name} {ty body : Expr} {m : Setlec.BinderMeta} {t : Expr}
    (h : inferTypeCore μ env f d (.lam n ty body m) = .ok t) :
    ∃ bt, t = .forallE n ty bt m := by
  cases f with
  | zero => exact nomatch h
  | succ f =>
    rw [Setlec.inferTypeCore_succ] at h
    unfold Setlec.inferBody at h
    simp only [Setlec.viewM, Setlec.Expr.view, Bind.bind, Except.bind,
      pure, Except.pure] at h
    cases h1 : (Setlec.pureFns μ env f).infer d ty with
    | error err => rw [h1] at h; exact nomatch h
    | ok tty =>
    rw [h1] at h
    simp only [] at h
    cases h2 : (Setlec.pureFns μ env f).whnf d tty with
    | error err => rw [h2] at h; exact nomatch h
    | ok wty =>
    rw [h2] at h
    simp only [] at h
    split at h
    · cases h3 : (Setlec.pureFns μ env f).infer (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | error err => rw [h3] at h; exact nomatch h
      | ok bt =>
      rw [h3] at h
      simp only [] at h
      split at h
      · revert h
        cases body.lamPw with
        | some pwI =>
          intro h
          dsimp only at h
          split at h
          · exact ⟨bt.abstract1 d, (Except.ok.inj h).symm⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
        | none =>
          intro h
          dsimp only at h
          cases h4 : (Setlec.pureFns μ env f).infer (d + 1) bt with
          | error err => rw [h4] at h; exact nomatch h
          | ok btt =>
          rw [h4] at h
          simp only [] at h
          cases h5 : Setlec.ensureSort (Setlec.pureFns μ env f) env
              (d + 1) btt with
          | error err => rw [h5] at h; exact nomatch h
          | ok s =>
          rw [h5] at h
          dsimp only at h
          split at h
          · exact ⟨bt.abstract1 d, (Except.ok.inj h).symm⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
      · exact ⟨bt.abstract1 d, (Except.ok.inj h).symm⟩
    · exact nomatch h

/-- Inference on an `fvar` leaf is name-blind: it returns the stored
annotation. -/
theorem inferTypeCore_fvar_out {μ : CheckMode} {env : Env} {f d : Nat}
    {i : Nat} {n : Name} {ty t : Expr}
    (h : inferTypeCore μ env f d (.fvar i n ty) = .ok t) : t = ty := by
  cases f with
  | zero => exact nomatch h
  | succ f =>
    rw [Setlec.inferTypeCore_succ] at h
    unfold Setlec.inferBody at h
    simp only [Setlec.viewM, Setlec.Expr.view, Bind.bind, Except.bind,
      pure, Except.pure] at h
    split at h
    · exact (Except.ok.inj h).symm
    · exact nomatch h

/-- **λ vacuity discharged**: a λ infers to a `∀`, and `∀`s are
whnf-inert — never a sort. -/
theorem lamTySortVacuity_of (hm : KnotFuelMono μ env) :
    LamTySortVacuity μ env := by
  intro d n ty body m ℓ hW
  obtain ⟨ft, t, hi, g, l, hl⟩ := hW
  obtain ⟨bt, rfl⟩ := inferTypeCore_lam_out hi
  exact nomatch (loop_stuck_out hm hl
    (whnfCore_forallE_run (μ := μ) (env := env) (d := d)
      (Nat.le_refl 1))
    (fun _ => reduceNat_forallE) unfoldDefinition_forallE)

/-- **The fvar leaf discharged**: cross-pairing pins the two
annotations equal, and `infer` reads the annotation name-blind, so
both sort computations run on one type. -/
theorem fvarTySortAgree_of (hm : KnotFuelMono μ env)
    {φ : Name → Nat} : FvarTySortAgree μ env φ := by
  intro d u v i n₁ n₂ ty₁ ty₂ _ _ hp hu hv
  have hty : ty₁ = ty₂ :=
    hp (i, n₁, ty₁)
      (List.mem_append_left _ (by simp [Setlec.Expr.fvarLeaves]))
      (i, n₂, ty₂)
      (List.mem_append_right _ (by simp [Setlec.Expr.fvarLeaves]))
      rfl
  obtain ⟨f₁, t₁, hi₁, g₁, l₁, ℓ₁, hl₁, hev₁⟩ := hu
  obtain ⟨f₂, t₂, hi₂, g₂, l₂, ℓ₂, hl₂, hev₂⟩ := hv
  obtain rfl : t₁ = ty₁ := inferTypeCore_fvar_out hi₁
  obtain rfl : t₂ = ty₂ := inferTypeCore_fvar_out hi₂
  subst hty
  obtain rfl : ℓ₁ = ℓ₂ :=
    Setlec.Expr.sort.inj (whnfLoop_det hm hl₁ hl₂)
  rw [← hev₁, ← hev₂]

/-- **The type-level probe vacuity discharged** — the (A) double
spine with determinism in place of the loop collide: the cert's own
unit-check run det-collides with the given type-sort fact, the sort
branch pins `uT` to the single successor through the second
transport, and `Level.isEquiv_sound` refutes at the zero
valuation. -/
theorem probeTySortVacuity_of (hm : KnotFuelMono μ env)
    (hT : TypeTransportLoopF μ env) (hInf : InvPreserveInferF μ env)
    {Q : Nat → Expr → Expr → Prop} :
    ProbeTySortVacuity μ env Q := by
  intro g d a' b' ℓ hIa' _hQv hpi hW
  unfold Setlec.proofIrrel at hpi
  simp only [Bind.bind, Except.bind] at hpi
  cases hinfa : (Setlec.pureFns μ env g).infer d a' with
  | error err => rw [hinfa] at hpi; exact nomatch hpi
  | ok ta =>
  rw [hinfa] at hpi
  simp only [] at hpi
  cases hwta : (Setlec.pureFns μ env g).whnf d ta with
  | error err => rw [hwta] at hpi; exact nomatch hpi
  | ok wta =>
  rw [hwta] at hpi
  simp only [] at hpi
  have hW1 : TypeWhnfLE μ env d a' wta := by
    obtain ⟨gw, lw, -, hlw⟩ :=
      whnf_peel (hwta : whnf μ env g d ta = .ok wta)
    exact ⟨g, ta, hinfa, gw, lw, hlw⟩
  obtain rfl : wta = .sort ℓ := TypeWhnfLE_det hm hW1 hW
  rw [isUnitLikeTy_sort, if_neg Bool.false_ne_true] at hpi
  cases hinfta : (Setlec.pureFns μ env g).infer d ta with
  | error err => rw [hinfta] at hpi; exact nomatch hpi
  | ok sa =>
  rw [hinfta] at hpi
  simp only [] at hpi
  cases hwsa : (Setlec.pureFns μ env g).whnf d sa with
  | error err => rw [hwsa] at hpi; exact nomatch hpi
  | ok wsa =>
  rw [hwsa] at hpi
  simp only [] at hpi
  split at hpi
  · next uT =>
    have hIta : SubjInv d ta := hInf hinfa hIa'
    have hW2 : TypeWhnfLE μ env d ta (.sort uT) := by
      obtain ⟨gs, ls, -, hls⟩ :=
        whnf_peel (hwsa : whnf μ env g d sa = .ok (.sort uT))
      exact ⟨g, sa, hinfta, gs, ls, hls⟩
    obtain ⟨gt, lt, -, hlt⟩ :=
      whnf_peel (hwta : whnf μ env g d ta = .ok (.sort ℓ))
    have hW3 : TypeWhnfLE μ env d (.sort ℓ) (.sort uT) :=
      hT hlt hIta hW2
    obtain rfl : uT = .succ ℓ :=
      Setlec.Expr.sort.inj (TypeWhnfLE_det hm hW3 typeWhnfLE_sort)
    cases hlift : Setlec.liftFueled "level comparison"
        (Level.isEquiv (.succ ℓ) .zero)
        (m := Setlec.CheckM) with
    | error err => rw [hlift] at hpi; exact nomatch hpi
    | ok okA =>
    rw [hlift] at hpi
    simp only [] at hpi
    rw [Setlec.liftFueled.eq_def] at hlift
    split at hlift
    · next okA' hEq =>
      obtain rfl : okA' = okA := by
        simpa [pure, Except.pure] using hlift
      cases okA' with
      | true =>
        have hev := Level.isEquiv_sound hEq (fun _ => 0)
        simp only [Setlec.Level.eval] at hev
        omega
      | false =>
        cases hinfb : (Setlec.pureFns μ env g).infer d b' with
        | error err => rw [hinfb] at hpi; exact nomatch hpi
        | ok tb =>
        rw [hinfb] at hpi
        simp only [] at hpi
        cases hinftb : (Setlec.pureFns μ env g).infer d tb with
        | error err => rw [hinftb] at hpi; exact nomatch hpi
        | ok sb =>
        rw [hinftb] at hpi
        simp only [] at hpi
        cases hwsb : (Setlec.pureFns μ env g).whnf d sb with
        | error err => rw [hwsb] at hpi; exact nomatch hpi
        | ok wsb =>
        rw [hwsb] at hpi
        simp only [] at hpi
        split at hpi
        · next vT =>
          cases hliftB : Setlec.liftFueled "level comparison"
              (Level.isEquiv vT .zero) (m := Setlec.CheckM) with
          | error err => rw [hliftB] at hpi; exact nomatch hpi
          | ok okB => rw [hliftB] at hpi; exact nomatch hpi
        · exact nomatch hpi
    · exact nomatch hlift
  · exact nomatch hpi

/-! ## The summit statement: the certified-pair eval-sort simulation

**Lineage** (the arc closing its own loop): the module docstring's
trap list said from the start "(C)'s β case is
`SortSubstStable`-shaped and `SortSubstStable`'s leaf is (B)-shaped
— one mutual induction".  After the w-general species' refutation,
every surviving agreement consumer (the spine core, (B)'s
re-entries, the congruence routings) converges on exactly that one
induction; `CertZip` and the two claims below are its statement.

**The relation**: lockstep pairs — one template at two
`isEquiv`-linked level instantiations, with `defEqList`-certified
leaves.  The `cert` leaf carries a GIVEN `isDefEqCore` run at knot
fuel `fc` — the relation's index and the mutual induction's primary
measure component (a leaf cert always sits at strictly smaller knot
fuel than the claim run that exposed it: `isDefEqCore (fc+1)` opens
to `defeqLoop` over `pureFns fc`, whose cert fields run at `fc`).

**The claims are dual-success eval currency throughout**: both runs
GIVEN, conclusions are `eval`-equalities — no liveness, no
constructed runs, no syntactic level identity (the refutation's
seeds are absorbed: isEquiv slack by eval, proofIrrel stuck slack by
never claiming output identity).

**Audit records (statement-tier, before any case work — DESIGN
carries the full versions)**:
* the zip tier is `Q`-FREE — the syntactic route displaced the model
  tier for agreements, so leaf recursion consumes the (A)/(B) claims
  at `Q := True` (no descent obligation); `Q`'s surviving consumer
  is the semantic trio alone;
* leaf recursion needs the (A)-claim's cross-`PairedLeaves` at the
  leaf pair, so the claims carry `PairedLeaves s t` (and the (A)
  motive gains the concrete pairing thread at the collapse seal —
  (B)'s motive is the proved pattern);
* the measure is lexicographic
  [env declaration index, cert knot fuel `fc`, run budgets]:
  δ-template linking recurses through INSTALL certs, which live at
  the env prefix — the outer layer needs env-indexed claims and
  prefix transport (`Extend/Transport` is the named supplier);
* β-closure of the zip is shape-restricted and sufficient: whnf
  β-reduces only at the head, where a zip head-λ is a template pair
  (contractum = template body with the arg zip substituted at
  substituAND positions — leaves are never substituted INTO) or a
  `cert` leaf (decomposed by the (A)-machinery at smaller `fc`);
  asymmetric stages (one side's redex cert fails) are disciplined by
  the GIVEN runs (a stuck non-sort output contradicts the run). -/

/-- The lockstep relation.  Generated minimally for the audited
consumers: syntactic identity, certified leaves (at knot fuel `fc`),
level slack at exactly the two level-carrying nodes, and structural
congruence (what `instantiateLevelParams` crosses) — the
"one template, two instantiations, certified leaves" pairs are
derivable, not primitive. -/
inductive CertZip (μ : CheckMode) (env : Env) (fc d : Nat) :
    Expr → Expr → Prop
  | refl (e : Expr) : CertZip μ env fc d e e
  | cert (a b : Expr) :
      a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
      isDefEqCore μ env fc d a b = .ok true →
      CertZip μ env fc d a b
  | sortSlack (u v : Level) :
      (∀ φ' : Name → Nat, u.eval φ' = v.eval φ') →
      CertZip μ env fc d (.sort u) (.sort v)
  | constSlack (n : Name) (us us' : List Level) :
      (∀ φ' : Name → Nat,
        us.map (Level.eval φ') = us'.map (Level.eval φ')) →
      CertZip μ env fc d (.const n us) (.const n us')
  | fvar (i : Nat) (n : Name) (ty₁ ty₂ : Expr) :
      CertZip μ env fc d ty₁ ty₂ →
      CertZip μ env fc d (.fvar i n ty₁) (.fvar i n ty₂)
  | app (f₁ a₁ f₂ a₂ : Expr) :
      CertZip μ env fc d f₁ f₂ → CertZip μ env fc d a₁ a₂ →
      CertZip μ env fc d (.app f₁ a₁) (.app f₂ a₂)
  | lam (n : Name) (ty₁ ty₂ body₁ body₂ : Expr)
      (m₁ m₂ : Setlec.BinderMeta) :
      CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d body₁ body₂ →
      CertZip μ env fc d (.lam n ty₁ body₁ m₁) (.lam n ty₂ body₂ m₂)
  | forallE (n : Name) (ty₁ ty₂ body₁ body₂ : Expr)
      (m₁ m₂ : Setlec.BinderMeta) :
      CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d body₁ body₂ →
      CertZip μ env fc d (.forallE n ty₁ body₁ m₁)
        (.forallE n ty₂ body₂ m₂)
  | letE (n : Name) (ty₁ ty₂ v₁ v₂ body₁ body₂ : Expr) :
      CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d v₁ v₂ →
      CertZip μ env fc d body₁ body₂ →
      CertZip μ env fc d (.letE n ty₁ v₁ body₁)
        (.letE n ty₂ v₂ body₂)
  | proj (s : Name) (i : Nat) (e₁ e₂ : Expr) :
      CertZip μ env fc d e₁ e₂ →
      CertZip μ env fc d (.proj s i e₁) (.proj s i e₂)

/-! ### (E): env-extension run stability — the third install-tier fact

The env-layer ruling: the zip claims stay single-env; the δ-link's
install cert (which ran at the env PREFIX of its declaration) is
transported FORWARD by (E).  Stated with the pre-build check
(DESIGN): success-lifting survives every env-consulting clause —
`find?` agrees on prefix names (`FindPreserved`; supplier:
duplicate-name installs are rejected, no shadowing), presence guards
(`natLitSupported`/`strLitSupported`/`natOpGuard`) are
`find?`-monotone and env₀-success pins them `true`, and the run's
reachable name set stays inside env₀ given the subject premise
(`ConstsBound`) plus stored-material closure (env₀'s stored exprs
are themselves bound — install-tier, fixed in clause form at the
discharge seal).  `ConstsBound`'s supplier for BOTH declared types
and values is the one install traversal: install typechecks every
declaration, inference visits every const leaf, and unknown
constants throw; recursor-rule right-hand sides ride the RecRulesOk
fold facts.  Discharge = the `CoreSub`-pattern oracle-extension
induction (the `KnotFuelMono` precedent), with the internal motive
strengthened by output-boundness. -/

/-- Every constant the expression mentions is bound in `env₀`
(hereditarily through annotations, like the leaf machinery). -/
def ConstsBound (env₀ : Env) : Expr → Prop
  | .const n _ => (env₀.find? n).isSome = true
  | .app f a => ConstsBound env₀ f ∧ ConstsBound env₀ a
  | .lam _ ty b _ => ConstsBound env₀ ty ∧ ConstsBound env₀ b
  | .forallE _ ty b _ => ConstsBound env₀ ty ∧ ConstsBound env₀ b
  | .letE _ t v b =>
      ConstsBound env₀ t ∧ ConstsBound env₀ v ∧ ConstsBound env₀ b
  | .proj _ _ e => ConstsBound env₀ e
  | .fvar _ _ ty => ConstsBound env₀ ty
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Setlec.Expr.sizeF]; omega)
  | simp [Setlec.Expr.sizeF]

/-- The extension is conservative on the prefix: every stored lookup
survives verbatim (no shadowing — duplicate installs are
rejected). -/
def FindPreserved (env₀ env : Env) : Prop :=
  ∀ {n : Name} {ci : Setlec.ConstantInfo},
    env₀.find? n = some ci → env.find? n = some ci

/-- **(E)**: successful runs on prefix-bound subjects are reproduced
verbatim at the extended env, knot-wide (the `CoreSub` field set).
The `inferTypeCore` conjunct also concludes `ConstsBound env₀` of
the OUTPUT type (junction amendment for the consumer lane's
`sortOfE` chain — infer's output feeds whnf's `ConstsBound`
premise; the discharge's internal motive already carries
output-boundness, this exposes it).

Junction amendments two and three (consumer-lane exposure
requests): (i) the BACKWARD direction — on prefix-bound subjects
the extension's runs REPRODUCE at env₀ (conservativity: the run
only consults `ConstsBound env₀`-reachable names, whose entries
`FindPreserved` pins and whose stored material is env₀-closed), the
transport the uniqueness ruling's denote2-premises need; (ii) the
LITERAL-GUARD agreement conjuncts — `ConstsBound`'s catch-all
grades literals while the literal reduction clauses gate on the
support guards, and an extension may FLIP a guard (their
`litGuardsAgree_probe` refutes the diagonal-only repair), so (E)
demands guard agreement outright — `find?`-monotone, cheap at
install. -/
def EnvExtendStable (μ : CheckMode) (env₀ env : Env) : Prop :=
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    whnfCore μ env₀ f d e = .ok x → whnfCore μ env f d e = .ok x) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    whnf μ env₀ f d e = .ok x → whnf μ env f d e = .ok x) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    inferTypeCore μ env₀ f d e = .ok x →
    inferTypeCore μ env f d e = .ok x ∧ ConstsBound env₀ x) ∧
  (∀ {f d : Nat} {a b : Expr} {v : Bool},
    ConstsBound env₀ a → ConstsBound env₀ b →
    isDefEqCore μ env₀ f d a b = .ok v →
    isDefEqCore μ env f d a b = .ok v) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    Setlec.annotateCore μ env₀ f d e = .ok x →
    Setlec.annotateCore μ env f d e = .ok x) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    whnfCore μ env f d e = .ok x → whnfCore μ env₀ f d e = .ok x) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    whnf μ env f d e = .ok x → whnf μ env₀ f d e = .ok x) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    inferTypeCore μ env f d e = .ok x →
    inferTypeCore μ env₀ f d e = .ok x) ∧
  (∀ {f d : Nat} {a b : Expr} {v : Bool},
    ConstsBound env₀ a → ConstsBound env₀ b →
    isDefEqCore μ env f d a b = .ok v →
    isDefEqCore μ env₀ f d a b = .ok v) ∧
  (∀ {f d : Nat} {e x : Expr}, ConstsBound env₀ e →
    Setlec.annotateCore μ env f d e = .ok x →
    Setlec.annotateCore μ env₀ f d e = .ok x) ∧
  Setlec.natLitSupported env₀ = Setlec.natLitSupported env ∧
  Setlec.strLitSupported env₀ = Setlec.strLitSupported env ∧
  (∀ c : Name,
    Setlec.natOpGuard env₀ c = Setlec.natOpGuard env c)

/-- Pointwise eval-equal substitutions induce the same assignment
(the level side of the instantiation zip). -/
theorem substFn_eval_congr {φ : Name → Nat} :
    ∀ {lps : List Name} {us us' : List Level},
      us.map (Level.eval φ) = us'.map (Level.eval φ) →
      Setlec.Level.substFn φ lps us = Setlec.Level.substFn φ lps us'
  | [], _, _, _ => by funext n; rfl
  | k :: ks, [], [], _ => rfl
  | k :: ks, [], v' :: vs', h => nomatch h
  | k :: ks, v :: vs, [], h => nomatch h
  | k :: ks, v :: vs, v' :: vs', h => by
    injection h with h1 h2
    funext n
    simp only [Setlec.Level.substFn]
    rw [h1, substFn_eval_congr (lps := ks) h2]

/-- **One template, two instantiations, zipped**: level-instantiating
a single expression at pointwise eval-equal level lists lands in
`CertZip` — the δ-case's bridge from the spine's `isEquivList`
verdict (via `isEquivList` soundness) to the lockstep relation. -/
theorem certZip_instantiate {μ : CheckMode} {env : Env} {fc d : Nat}
    {lps : List Name} {us us' : List Level}
    (hev : ∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) :
    ∀ v : Expr, CertZip μ env fc d
      (v.instantiateLevelParams lps us)
      (v.instantiateLevelParams lps us') := by
  intro v
  induction v with
  | bvar i => exact .refl _
  | fvar i n ty ih => exact .fvar _ _ _ _ ih
  | sort u =>
    exact .sortSlack _ _ fun φ' => by
      rw [show (Setlec.Level.subst lps us u).eval φ'
          = Setlec.Level.eval (Setlec.Level.substFn φ' lps us) u from
        Setlec.Level.eval_subst φ' lps us u,
        show (Setlec.Level.subst lps us' u).eval φ'
          = Setlec.Level.eval (Setlec.Level.substFn φ' lps us') u from
        Setlec.Level.eval_subst φ' lps us' u,
        substFn_eval_congr (hev φ')]
  | const n vs =>
    exact .constSlack _ _ _ fun φ' => by
      simp only [List.map_map]
      congr 1
      funext l
      show (Setlec.Level.subst lps us l).eval φ'
        = (Setlec.Level.subst lps us' l).eval φ'
      rw [Setlec.Level.eval_subst φ' lps us l,
        Setlec.Level.eval_subst φ' lps us' l,
        substFn_eval_congr (hev φ')]
  | app f a ihf iha => exact .app _ _ _ _ ihf iha
  | lam n ty body m iht ihb => exact .lam _ _ _ _ _ _ _ iht ihb
  | forallE n ty body m iht ihb =>
    exact .forallE _ _ _ _ _ _ _ iht ihb
  | letE n ty val body iht ihv ihb =>
    exact .letE _ _ _ _ _ _ _ iht ihv ihb
  | lit l => exact .refl _
  | proj s i e ih => exact .proj _ _ _ _ ih

/-- Per-argument extraction from a spine certificate: a `true`
`defEqList` verdict yields the pairwise `defeq` runs (and the length
equation). -/
theorem defEqList_extract {r : Setlec.CoreFns Setlec.CheckM}
    {env : Env} {d : Nat} :
    ∀ {as bs : List Expr},
      Setlec.defEqList r env d as bs = .ok true →
      as.length = bs.length ∧
      ∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        r.defeq d as[i] bs[i] = .ok true := by
  intro as
  induction as with
  | nil =>
    intro bs h
    cases bs with
    | nil =>
      exact ⟨rfl, fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)⟩
    | cons b bs => exact nomatch h
  | cons a as ih =>
    intro bs h
    cases bs with
    | nil => exact nomatch h
    | cons b bs =>
      unfold Setlec.defEqList at h
      simp only [Bind.bind, Except.bind] at h
      cases hd : r.defeq d a b with
      | error err => rw [hd] at h; exact nomatch h
      | ok c =>
        rw [hd] at h
        simp only [] at h
        cases c with
        | false => exact nomatch h
        | true =>
          rw [if_pos rfl] at h
          obtain ⟨hlen, hall⟩ := ih h
          refine ⟨by simp [hlen], ?_⟩
          intro i h₁ h₂
          cases i with
          | zero => simpa using hd
          | succ i =>
            simpa using hall i (by simpa using h₁) (by simpa using h₂)

/-- `EvalEqList` as a map equality (the bridge from `isEquivList`
soundness to `constSlack`'s premise). -/
theorem evalEqList_map {φ : Name → Nat} :
    ∀ {us vs : List Level}, Setlec.Level.EvalEqList φ us vs →
      us.map (Level.eval φ) = vs.map (Level.eval φ)
  | [], [], _ => rfl
  | u :: us, v :: vs, h => by
    obtain ⟨h1, h2⟩ := h
    simp only [List.map]
    rw [h1, evalEqList_map h2]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Zip a spine fold: a zipped head applied to pointwise-certified
argument lists stays zipped. -/
theorem certZip_mkAppN {μ : CheckMode} {env : Env} {fc d : Nat} :
    ∀ {as bs : List Expr} {f₁ f₂ : Expr},
      CertZip μ env fc d f₁ f₂ →
      as.length = bs.length →
      (∀ x ∈ as, x.looseBVarsBounded 0 = true) →
      (∀ x ∈ bs, x.looseBVarsBounded 0 = true) →
      (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        isDefEqCore μ env fc d as[i] bs[i] = .ok true) →
      CertZip μ env fc d (Setlec.Expr.mkAppN f₁ as)
        (Setlec.Expr.mkAppN f₂ bs) := by
  intro as
  induction as with
  | nil =>
    intro bs f₁ f₂ hz hlen hba hbb hcert
    cases bs with
    | nil => exact hz
    | cons b bs => exact nomatch hlen
  | cons a as ih =>
    intro bs f₁ f₂ hz hlen hba hbb hcert
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      simp only [Setlec.Expr.mkAppN]
      exact ih
        (.app _ _ _ _ hz
          (.cert _ _ (hba a (List.mem_cons_self ..))
            (hbb b (List.mem_cons_self ..))
            (hcert 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))))
        (by simpa using hlen)
        (fun x hx => hba x (List.mem_cons_of_mem _ hx))
        (fun x hx => hbb x (List.mem_cons_of_mem _ hx))
        (fun i h₁ h₂ =>
          hcert (i + 1)
            (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega))

/-- Substitution leaves bounded expressions verbatim (all loose
bvars below `j ≤ k` — the closed-cert-leaf case's engine). -/
theorem instantiate1_bounded : ∀ {x v : Expr} {j k : Nat},
    x.looseBVarsBounded j = true → j ≤ k →
    x.instantiate1 v k = x := by
  intro x
  induction x with
  | bvar i =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded,
      decide_eq_true_eq] at h
    simp only [Setlec.Expr.instantiate1]
    rw [if_neg (by omega), if_neg (by omega)]
  | fvar idx n ty ih => intro v j k h hjk; rfl
  | sort u => intro v j k h hjk; rfl
  | const n us => intro v j k h hjk; rfl
  | app f a ihf iha =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiate1, ihf h.1 hjk, iha h.2 hjk]
  | lam n ty body m iht ihb =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiate1, iht h.1 hjk,
      ihb h.2 (Nat.succ_le_succ hjk)]
  | forallE n ty body m iht ihb =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiate1, iht h.1 hjk,
      ihb h.2 (Nat.succ_le_succ hjk)]
  | letE n ty val body iht ihv ihb =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiate1, iht h.1.1 hjk,
      ihv h.1.2 hjk, ihb h.2 (Nat.succ_le_succ hjk)]
  | lit l => intro v j k h hjk; rfl
  | proj s i e ih =>
    intro v j k h hjk
    simp only [Setlec.Expr.looseBVarsBounded] at h
    simp only [Setlec.Expr.instantiate1, ih h hjk]

/-- **Substitution lemma (i)**: one template, two zipped args — the
`refl`-leaf replacement (a `refl` body does not survive
substitution; this is what it becomes). -/
theorem certZip_instantiate1 {μ : CheckMode} {env : Env} {fc d : Nat}
    {a₁ a₂ : Expr} (hz : CertZip μ env fc d a₁ a₂) :
    ∀ (e : Expr) (k : Nat),
      CertZip μ env fc d (e.instantiate1 a₁ k)
        (e.instantiate1 a₂ k) := by
  intro e
  induction e with
  | bvar i =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    by_cases h : i = k
    · rw [if_pos h, if_pos h]; exact hz
    · rw [if_neg h, if_neg h]
      by_cases h2 : i > k <;> exact .refl _
  | fvar idx n ty ih => intro k; exact .refl _
  | sort u => intro k; exact .refl _
  | const n us => intro k; exact .refl _
  | app f a ihf iha =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .app _ _ _ _ (ihf k) (iha k)
  | lam n ty body m iht ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .lam _ _ _ _ _ _ _ (iht k) (ihb (k + 1))
  | forallE n ty body m iht ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .forallE _ _ _ _ _ _ _ (iht k) (ihb (k + 1))
  | letE n ty val body iht ihv ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .letE _ _ _ _ _ _ _ (iht k) (ihv k) (ihb (k + 1))
  | lit l => intro k; exact .refl _
  | proj s i e ih =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .proj _ _ _ _ (ih k)

/-- **Substitution lemma (ii)**: zipped bodies at zipped args stay
zipped — `refl` leaves by (i), `cert` leaves verbatim by closedness
(the summit map's Finding 1), congruence structurally.  The β case's
engine. -/
theorem certZip_subst {μ : CheckMode} {env : Env} {fc d : Nat}
    {a₁ a₂ : Expr} (ha : CertZip μ env fc d a₁ a₂) :
    ∀ {body₁ body₂ : Expr}, CertZip μ env fc d body₁ body₂ →
    ∀ k : Nat,
      CertZip μ env fc d (body₁.instantiate1 a₁ k)
        (body₂.instantiate1 a₂ k) := by
  intro body₁ body₂ hb
  induction hb with
  | refl e => intro k; exact certZip_instantiate1 ha e k
  | cert x y hbx hby hc =>
    intro k
    rw [instantiate1_bounded hbx (Nat.zero_le k),
      instantiate1_bounded hby (Nat.zero_le k)]
    exact .cert _ _ hbx hby hc
  | sortSlack u v hev => intro k; exact .sortSlack _ _ hev
  | constSlack n us us' hev => intro k; exact .constSlack _ _ _ hev
  | fvar i n ty₁ ty₂ hty ih => intro k; exact .fvar _ _ _ _ hty
  | app f₁ x₁ f₂ x₂ hf hx ihf ihx =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .app _ _ _ _ (ihf k) (ihx k)
  | lam n ty₁ ty₂ b₁ b₂ m₁ m₂ hty hbody iht ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .lam _ _ _ _ _ _ _ (iht k) (ihb (k + 1))
  | forallE n ty₁ ty₂ b₁ b₂ m₁ m₂ hty hbody iht ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .forallE _ _ _ _ _ _ _ (iht k) (ihb (k + 1))
  | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody iht ihv ihb =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .letE _ _ _ _ _ _ _ (iht k) (ihv k) (ihb (k + 1))
  | proj s i e₁ e₂ he ih =>
    intro k
    simp only [Setlec.Expr.instantiate1]
    exact .proj _ _ _ _ (ih k)

/-- `proofIrrel` never certifies two literal sorts: the subject's
type-chain pins `uT` to a double successor, refuting the `Prop`
check by eval arithmetic (the probe walk, at literal subjects). -/
theorem proofIrrel_sorts_absurd {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g d : Nat} {u v : Level}
    (hpi : Setlec.proofIrrel (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) = .ok true) : False := by
  have hdet := KnotFuelDet_of_mono hm
  unfold Setlec.proofIrrel at hpi
  simp only [Bind.bind, Except.bind] at hpi
  cases hinfa : (Setlec.pureFns μ env g).infer d (.sort u) with
  | error err => rw [hinfa] at hpi; exact nomatch hpi
  | ok ta =>
  rw [hinfa] at hpi
  simp only [] at hpi
  obtain rfl : ta = .sort (.succ u) := inferTypeCore_sort_out hinfa
  cases hwta : (Setlec.pureFns μ env g).whnf d (.sort (.succ u)) with
  | error err => rw [hwta] at hpi; exact nomatch hpi
  | ok wta =>
  rw [hwta] at hpi
  simp only [] at hpi
  obtain rfl : wta = .sort (.succ u) := whnf_sort_out hdet hwta
  rw [isUnitLikeTy_sort, if_neg Bool.false_ne_true] at hpi
  cases hinfta : (Setlec.pureFns μ env g).infer d (.sort (.succ u)) with
  | error err => rw [hinfta] at hpi; exact nomatch hpi
  | ok sa =>
  rw [hinfta] at hpi
  simp only [] at hpi
  obtain rfl : sa = .sort (.succ (.succ u)) :=
    inferTypeCore_sort_out hinfta
  cases hwsa : (Setlec.pureFns μ env g).whnf d
      (.sort (.succ (.succ u))) with
  | error err => rw [hwsa] at hpi; exact nomatch hpi
  | ok wsa =>
  rw [hwsa] at hpi
  simp only [] at hpi
  obtain rfl : wsa = .sort (.succ (.succ u)) := whnf_sort_out hdet hwsa
  simp only [] at hpi
  cases hlift : Setlec.liftFueled "level comparison"
      (Level.isEquiv (.succ (.succ u)) .zero)
      (m := Setlec.CheckM) with
  | error err => rw [hlift] at hpi; exact nomatch hpi
  | ok okA =>
  rw [hlift] at hpi
  simp only [] at hpi
  rw [Setlec.liftFueled.eq_def] at hlift
  split at hlift
  · next okA' hEq =>
    obtain rfl : okA' = okA := by
      simpa [pure, Except.pure] using hlift
    cases okA' with
    | true =>
      have hev := Level.isEquiv_sound hEq (fun _ => 0)
      simp only [Setlec.Level.eval] at hev
      omega
    | false =>
      cases hinfb : (Setlec.pureFns μ env g).infer d (.sort v) with
      | error err => rw [hinfb] at hpi; exact nomatch hpi
      | ok tb =>
      rw [hinfb] at hpi
      simp only [] at hpi
      cases hinftb : (Setlec.pureFns μ env g).infer d tb with
      | error err => rw [hinftb] at hpi; exact nomatch hpi
      | ok sb =>
      rw [hinftb] at hpi
      simp only [] at hpi
      cases hwsb : (Setlec.pureFns μ env g).whnf d sb with
      | error err => rw [hwsb] at hpi; exact nomatch hpi
      | ok wsb =>
      rw [hwsb] at hpi
      simp only [] at hpi
      split at hpi
      · next vT =>
        cases hliftB : Setlec.liftFueled "level comparison"
            (Level.isEquiv vT .zero) (m := Setlec.CheckM) with
        | error err => rw [hliftB] at hpi; exact nomatch hpi
        | ok okB => rw [hliftB] at hpi; exact nomatch hpi
      · exact nomatch hpi
  · exact nomatch hlift

/-- `stuckIrrel` never certifies two literal sorts (the five-way
walk at literal subjects; the fallback is
`proofIrrel_sorts_absurd`). -/
theorem stuckIrrel_sorts_absurd {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g d : Nat} {u v : Level}
    (hsi : Setlec.stuckIrrel μ (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) = .ok true) : False := by
  have hdet := KnotFuelDet_of_mono hm
  unfold Setlec.stuckIrrel at hsi
  simp only [Bind.bind, Except.bind] at hsi
  cases h1 : Setlec.pairEtaCert μ (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) with
  | error err => rw [h1] at hsi; exact nomatch hsi
  | ok c1 =>
  rw [h1] at hsi
  simp only [] at hsi
  cases c1 with
  | true => unfold Setlec.pairEtaCert at h1; exact nomatch h1
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  cases h2 : Setlec.pairEtaCert μ (Setlec.pureFns μ env g) env d
      (.sort v) (.sort u) with
  | error err => rw [h2] at hsi; exact nomatch hsi
  | ok c2 =>
  rw [h2] at hsi
  simp only [] at hsi
  cases c2 with
  | true => unfold Setlec.pairEtaCert at h2; exact nomatch h2
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  cases h3 : Setlec.structEtaCert μ (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) with
  | error err => rw [h3] at hsi; exact nomatch hsi
  | ok c3 =>
  rw [h3] at hsi
  simp only [] at hsi
  cases c3 with
  | true =>
    unfold Setlec.structEtaCert at h3
    simp only [Bind.bind, Except.bind] at h3
    cases hinf3 : (Setlec.pureFns μ env g).infer d (.sort v) with
    | error err => rw [hinf3] at h3; exact nomatch h3
    | ok tb =>
    rw [hinf3] at h3
    simp only [] at h3
    cases hw3 : (Setlec.pureFns μ env g).whnf d tb with
    | error err => rw [hw3] at h3; exact nomatch h3
    | ok wtb =>
    rw [hw3] at h3
    simp only [] at h3
    unfold Setlec.structEtaCertWith at h3
    exact nomatch h3
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  cases h4 : Setlec.structEtaCert μ (Setlec.pureFns μ env g) env d
      (.sort v) (.sort u) with
  | error err => rw [h4] at hsi; exact nomatch hsi
  | ok c4 =>
  rw [h4] at hsi
  simp only [] at hsi
  cases c4 with
  | true =>
    unfold Setlec.structEtaCert at h4
    simp only [Bind.bind, Except.bind] at h4
    cases hinf4 : (Setlec.pureFns μ env g).infer d (.sort u) with
    | error err => rw [hinf4] at h4; exact nomatch h4
    | ok tb =>
    rw [hinf4] at h4
    simp only [] at h4
    cases hw4 : (Setlec.pureFns μ env g).whnf d tb with
    | error err => rw [hw4] at h4; exact nomatch h4
    | ok wtb =>
    rw [hw4] at h4
    simp only [] at h4
    unfold Setlec.structEtaCertWith at h4
    exact nomatch h4
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  cases h5 : Setlec.structUnitCert (Setlec.pureFns μ env g) env d
      (.sort u) (.sort v) with
  | error err => rw [h5] at hsi; exact nomatch hsi
  | ok c5 =>
  rw [h5] at hsi
  simp only [] at hsi
  cases c5 with
  | true =>
    unfold Setlec.structUnitCert at h5
    simp only [Bind.bind, Except.bind] at h5
    cases hinf5 : (Setlec.pureFns μ env g).infer d (.sort u) with
    | error err => rw [hinf5] at h5; exact nomatch h5
    | ok ta =>
    rw [hinf5] at h5
    simp only [] at h5
    obtain rfl : ta = .sort (.succ u) := inferTypeCore_sort_out hinf5
    cases hw5 : (Setlec.pureFns μ env g).whnf d (.sort (.succ u)) with
    | error err => rw [hw5] at h5; exact nomatch h5
    | ok wta =>
    rw [hw5] at h5
    simp only [] at h5
    obtain rfl : wta = .sort (.succ u) := whnf_sort_out hdet hw5
    exact nomatch h5
  | false =>
  rw [if_neg Bool.false_ne_true] at hsi
  exact proofIrrel_sorts_absurd hm hsi

/-- **The sort-sort cert inversion** (the summit's stuck-stuck
terminal and the cert case's base): a certified pair of literal
sorts has eval-equal levels. -/
theorem isDefEqCore_sorts_eval {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (hm : KnotFuelMono μ env)
    {fc d : Nat} {u v : Level}
    (h : isDefEqCore μ env fc d (.sort u) (.sort v) = .ok true) :
    u.eval φ = v.eval φ := by
  have hdet := KnotFuelDet_of_mono hm
  cases fc with
  | zero => exact nomatch h
  | succ fc =>
  rw [Setlec.isDefEqCore_succ] at h
  obtain ⟨L, hL⟩ := Setlec.defeqLoopFuel_succ
  unfold Setlec.defeqBody at h
  rw [hL, defeqLoop_succ] at h
  rcases defeqStep_decompose h with heq | ⟨a', b', hwa, hwb, hcert⟩
  · rw [Setlec.Expr.sort.inj heq]
  · obtain rfl : a' = .sort u :=
      hdet.2.2.1 hwa (whnfCore_sort_run (whnfCore_pos hwa))
    obtain rfl : b' = .sort v :=
      hdet.2.2.1 hwb (whnfCore_sort_run (whnfCore_pos hwb))
    cases hcert with
    | syn => rfl
    | irrel _ _ hpi => exact (proofIrrel_sorts_absurd hm hpi).elim
    | natL _ _ a₂ hrn hk => exact nomatch hrn
    | natR _ _ b₂ hrnA hrnB hk => exact nomatch hrnB
    | deltaL _ _ a₂ hu hk => exact nomatch hu
    | deltaR _ _ b₂ hu hk => exact nomatch hu
    | deltaB _ _ a₂ b₂ hua hub hk => exact nomatch hua
    | spine _ _ hs =>
      unfold Setlec.defeqSpine at hs
      exact nomatch hs
    | sorts _ _ hiseq => exact Level.isEquiv_sound hiseq φ
    | rescue _ _ hsi => exact (stuckIrrel_sorts_absurd hm hsi).elim

/-- Spine arguments of a bvar-closed expression are bvar-closed. -/
theorem getAppArgs_bounded : ∀ {e : Expr},
    e.looseBVarsBounded 0 = true →
    ∀ x ∈ e.getAppArgs, x.looseBVarsBounded 0 = true := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro h x hx
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.getAppArgs] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact ihf h.1 x hx
    · simp only [List.mem_singleton] at hx
      exact hx ▸ h.2
  | bvar i => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | fvar i n ty ih => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | sort u => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | const n us => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | lam n ty body m iht ihb =>
    intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | forallE n ty body m iht ihb =>
    intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | letE n ty val body iht ihv ihb =>
    intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | lit l => intro h x hx; simp [Setlec.Expr.getAppArgs] at hx
  | proj sn i pe ih =>
    intro h x hx; simp [Setlec.Expr.getAppArgs] at hx

/-- **Summit claim, subject form**: zipped pairs whose members'
whnf chains both reach literal sorts have eval-equal levels.  The
spine core and (A)'s remaining routings collapse onto this. -/
def ZipWhnfSortAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {s t : Expr} {ℓa ℓb : Level},
    CertZip μ env fc d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Summit claim, type form**: zipped pairs on which both sort
computations succeed have equal numerals.  (B)'s re-entries and the
congruence routings collapse onto this. -/
def ZipSortOfAgree (μ : CheckMode) (env : Env)
    (φ : Name → Nat) (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d : Nat} {s t : Expr} {u v : Nat},
    CertZip μ env fc d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
    SortOfLE μ env φ d s u → SortOfLE μ env φ d t v → u = v

/-! ### The summit skeleton (build order, step 2)

The one induction, on the audited lexicographic measure — outer
strong induction on the cert fuel `fc`, inner on the loop-budget sum
— with `ZipBelow` as the continuation contract handed to the routed
cases (the house pattern: the recursion travels as a premise, cases
seal separately).  Inline here: `refl` (determinism), `sortSlack`
(stuck + eval), and the four stuck-shape vacuities (`fvar`, `lam`,
`forallE`; `lit` rides `refl`).  Routed: the cert case (the shells'
template — build step 3), the constSlack both-δ case (needs the
`StoredWF` supply kit), and the three sim roots (`app`, `letE`,
`proj` — the knot-fuel tier, iota getting its full treatment when
reached). -/

/-- The summit claim strictly below the measure `(fc, r)` —
lexicographically: smaller cert fuel, or equal fuel and smaller
loop-budget sum. -/
def ZipBelow (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) (fc g r : Nat) : Prop :=
  ∀ {fc' d ga la gb lb : Nat} {s t : Expr} {ℓa ℓb : Level},
    (fc' < fc ∨ (fc' = fc ∧
      (ga + gb < g ∨ (ga + gb = g ∧ la + lb < r)))) →
    CertZip μ env fc' d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- Stored definition/theorem values are fvar-free, bvar-closed and
leaf-bounded — the install-tier fact the constSlack case's
continuations consume (the ledgered value-closedness family, in the
form the summit reads). -/
def StoredWF (env : Env) : Prop :=
  ∀ {n : Name} {cv : Setlec.ConstantVal} {value : Expr},
    ((∃ hint, env.find? n = some (.defnInfo cv value hint)) ∨
      env.find? n = some (.thmInfo cv value)) →
    value.fvarLeaves = [] ∧ value.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded value

/-- The fc-only recursion contract (what the cert case actually
consumes — its spine feeds strictly smaller cert fuel, nothing
else; consumers can therefore supply it from ANY measure
position). -/
def ZipBelowFc (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) (fc : Nat) : Prop :=
  ∀ {fc' d ga la gb lb : Nat} {s t : Expr} {ℓa ℓb : Level},
    fc' < fc →
    CertZip μ env fc' d s t →
    SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the cert case** (the shells' template — a certified
pair with both sort convergences, the recursion available at
strictly smaller cert fuel). -/
def ZipCertCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {a b : Expr} {ℓa ℓb : Level},
    ZipBelowFc μ env φ Q fc →
    a.looseBVarsBounded 0 = true → b.looseBVarsBounded 0 = true →
    isDefEqCore μ env fc d a b = .ok true →
    SubjInv d a → SubjInv d b → PairedLeaves a b → Q d a b →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la a
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb b
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the constSlack both-δ case** (same head at eval-equal
levels; the continuations are `certZip_instantiate` zips of one
stored value, `StoredWF` supplying their invariants). -/
def ZipConstCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name} {us us' : List Level}
    {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    Q d (.const n us) (.const n us') →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la (.const n us)
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb (.const n us')
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the app sim root** (the knot-fuel tier; the cert-headed
sub-case is the mutual knot with binder opening — full pre-build
treatment at its seal). -/
def ZipAppCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {f₁ x₁ f₂ x₂ : Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d f₁ f₂ → CertZip μ env fc d x₁ x₂ →
    SubjInv d (.app f₁ x₁) → SubjInv d (.app f₂ x₂) →
    PairedLeaves (.app f₁ x₁) (.app f₂ x₂) →
    Q d (.app f₁ x₁) (.app f₂ x₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la (.app f₁ x₁)
      = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb (.app f₂ x₂)
      = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the letE sim root** (lockstep zeta through
`certZip_subst`, inside the knot-fuel tier). -/
def ZipLetECase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name}
    {ty₁ ty₂ v₁ v₂ b₁ b₂ : Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d v₁ v₂ →
    CertZip μ env fc d b₁ b₂ →
    SubjInv d (.letE n ty₁ v₁ b₁) → SubjInv d (.letE n ty₂ v₂ b₂) →
    PairedLeaves (.letE n ty₁ v₁ b₁) (.letE n ty₂ v₂ b₂) →
    Q d (.letE n ty₁ v₁ b₁) (.letE n ty₂ v₂ b₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (.letE n ty₁ v₁ b₁) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (.letE n ty₂ v₂ b₂) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **Routed: the proj sim root** (whnf-of-scrutinee lockstep +
`projLitToCtor` + the structural rule; its seal carries the
struct-name-slack audit flagged at the map). -/
def ZipProjCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb i : Nat} {sn : Name} {e₁ e₂ : Expr}
    {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d e₁ e₂ →
    SubjInv d (.proj sn i e₁) → SubjInv d (.proj sn i e₂) →
    PairedLeaves (.proj sn i e₁) (.proj sn i e₂) →
    Q d (.proj sn i e₁) (.proj sn i e₂) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (.proj sn i e₁) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (.proj sn i e₂) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- Fvar leaves re-core to themselves (value branch). -/
theorem whnfCore_fvar_run {μ : CheckMode} {env : Env} {f d : Nat}
    {i : Nat} {n : Name} {ty : Expr} (hf : 1 ≤ f) :
    whnfCore μ env f d (.fvar i n ty) = .ok (.fvar i n ty) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- Lams re-core to themselves (value branch). -/
theorem whnfCore_lam_run {μ : CheckMode} {env : Env} {f d : Nat}
    {n : Name} {ty body : Expr} {m : Setlec.BinderMeta} (hf : 1 ≤ f) :
    whnfCore μ env f d (.lam n ty body m) = .ok (.lam n ty body m) := by
  cases f with
  | zero => exact nomatch hf
  | succ f => rw [Setlec.whnfCore_succ]; rfl

/-- **The summit skeleton**: `ZipWhnfSortAgree` from the five routed
cases, by the one lexicographic induction; the determinism, stuck
and slack cases are inline. -/
theorem zipWhnfSortAgree_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hCert : ZipCertCase μ env φ Q) (hConst : ZipConstCase μ env φ Q)
    (hApp : ZipAppCase μ env φ Q) (hLet : ZipLetECase μ env φ Q)
    (hProj : ZipProjCase μ env φ Q) :
    ZipWhnfSortAgree μ env φ Q := by
  have main : ∀ fc g r {d ga la gb lb : Nat} {s t : Expr}
      {ℓa ℓb : Level}, ga + gb ≤ g → la + lb ≤ r →
      CertZip μ env fc d s t →
      SubjInv d s → SubjInv d t → PairedLeaves s t → Q d s t →
      Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la s
        = .ok (.sort ℓa) →
      Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb t
        = .ok (.sort ℓb) →
      ℓa.eval φ = ℓb.eval φ := by
    intro fc
    induction fc using Nat.strongRecOn with
    | ind fc ihfc =>
    intro g
    induction g using Nat.strongRecOn with
    | ind g ihg =>
    intro r
    induction r with
    | zero =>
      intro d ga la gb lb s t ℓa ℓb hgle hle hz hIs hIt hp hQ ha hb
      obtain rfl : la = 0 := by omega
      exact nomatch ha
    | succ r ihr =>
      intro d ga la gb lb s t ℓa ℓb hgle hle hz hIs hIt hp hQ ha hb
      have below : ZipBelow μ env φ Q fc (ga + gb) (la + lb) := by
        intro fc' d' ga' la' gb' lb' s' t' ℓa' ℓb' hlt hz' hIs' hIt'
          hp' hQ' ha' hb'
        rcases hlt with hlt | ⟨rfl, hlt | ⟨hge, hlt⟩⟩
        · exact ihfc fc' hlt (ga' + gb') (la' + lb') (Nat.le_refl _)
            (Nat.le_refl _) hz' hIs' hIt' hp' hQ' ha' hb'
        · exact ihg (ga' + gb') (Nat.lt_of_lt_of_le hlt hgle)
            (la' + lb') (Nat.le_refl _) (Nat.le_refl _) hz' hIs'
            hIt' hp' hQ' ha' hb'
        · exact ihr (hge ▸ hgle) (by omega) hz' hIs' hIt' hp' hQ'
            ha' hb'
      cases hz with
      | refl e =>
        rw [Setlec.Expr.sort.inj (whnfLoop_det hm ha hb)]
      | cert a b hba hbb hc =>
        exact hCert
          (fun hlt hz' hIs' hIt' hp' hQ' ha' hb' =>
            below (Or.inl hlt) hz' hIs' hIt' hp' hQ' ha' hb')
          hba hbb hc hIs hIt hp hQ ha hb
      | sortSlack u v hev =>
        have h1 : Expr.sort ℓa = Expr.sort u :=
          loop_stuck_out hm ha (whnfCore_sort_run (Nat.le_refl 1))
            (fun _ => reduceNat_sort) unfoldDefinition_sort
        have h2 : Expr.sort ℓb = Expr.sort v :=
          loop_stuck_out hm hb (whnfCore_sort_run (Nat.le_refl 1))
            (fun _ => reduceNat_sort) unfoldDefinition_sort
        rw [Setlec.Expr.sort.inj h1, Setlec.Expr.sort.inj h2]
        exact hev φ
      | constSlack n us us' hev => exact hConst below hev hQ ha hb
      | fvar i nm ty₁ ty₂ hty =>
        exact nomatch (loop_stuck_out hm ha
          (whnfCore_fvar_run (Nat.le_refl 1))
          (fun _ => reduceNat_fvar) unfoldDefinition_fvar)
      | lam n ty₁ ty₂ b₁ b₂ m₁ m₂ hty hbody =>
        exact nomatch (loop_stuck_out hm ha
          (whnfCore_lam_run (Nat.le_refl 1))
          (fun _ => reduceNat_lam) unfoldDefinition_lam)
      | forallE n ty₁ ty₂ b₁ b₂ m₁ m₂ hty hbody =>
        exact nomatch (loop_stuck_out hm ha
          (whnfCore_forallE_run (Nat.le_refl 1))
          (fun _ => reduceNat_forallE) unfoldDefinition_forallE)
      | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody =>
        exact hLet below hty hval hbody hIs hIt hp hQ ha hb
      | app f₁ x₁ f₂ x₂ hf hx =>
        exact hApp below hf hx hIs hIt hp hQ ha hb
      | proj sn i e₁ e₂ he =>
        exact hProj below he hIs hIt hp hQ ha hb
  intro fc d ga la gb lb s t ℓa ℓb hz hIs hIt hp hQ ha hb
  exact main fc (ga + gb) (la + lb) (Nat.le_refl _) (Nat.le_refl _)
    hz hIs hIt hp hQ ha hb

/-- **The cert case DISCHARGED** (build step 3): the extracted
cert-loop template, with the spine handler zipping the post-core
pair (`constSlack` head through `isEquivList` soundness, `.cert`
leaves through `defEqList_extract`, dual-success runs assembled from
the spine's const heads) and feeding `ZipBelow` at the strictly
smaller cert fuel. -/
theorem zipCertCase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q) :
    ZipCertCase μ env φ Q := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc d ga la gb lb a b ℓa ℓb below hba hbb hc hIa hIb hp hQ ha hb
  cases fc with
  | zero => exact nomatch hc
  | succ fc =>
  rw [Setlec.isDefEqCore_succ] at hc
  have hSp : SpineHandler μ env φ Q fc := by
    intro l d' ga' la' gb' lb' f₁ f₂ a0 b0 a' b' ℓa' ℓb'
      hIa' hIb' hPab' hQab' hc0 hwa hwb hs ha' hb'
    cases la' with
    | zero => exact nomatch ha'
    | succ la'' =>
    cases lb' with
    | zero => exact nomatch hb'
    | succ lb'' =>
    have haD := ha'
    rw [whnfLoop_succ] at haD
    obtain ⟨a₁, hwca, htriA⟩ := whnfStep_decompose haD
    obtain rfl : a' = a₁ :=
      ((KnotFuelDet_of_mono hm).2.2.1
        (hwca : whnfCore μ env ga' d' a0 = .ok a₁) hwa).symm
    have hbD := hb'
    rw [whnfLoop_succ] at hbD
    obtain ⟨b₁, hwcb, htriB⟩ := whnfStep_decompose hbD
    obtain rfl : b' = b₁ :=
      ((KnotFuelDet_of_mono hm).2.2.1
        (hwcb : whnfCore μ env gb' d' b0 = .ok b₁) hwb).symm
    rcases htriA with ⟨x, hrx, -⟩ | ⟨hrga, xa, hux, hkx⟩ |
      ⟨-, -, hstopA⟩
    · exact (hN hwa hrx ha').elim
    · rcases htriB with ⟨y, hry, -⟩ | ⟨hrgb, xb, huy, hky⟩ |
        ⟨-, -, hstopB⟩
      · exact (hN hwb hry hb').elim
      · obtain ⟨na, usa, heqa⟩ : ∃ n us,
            a'.getAppFn = .const n us := by
          have hs' := hs
          unfold Setlec.defeqSpine at hs'
          split at hs'
          · next n us heq => exact ⟨n, us, heq⟩
          · exact nomatch hs'
        obtain ⟨nb, usb, heqb⟩ : ∃ n us,
            b'.getAppFn = .const n us := by
          have hs' := hs
          unfold Setlec.defeqSpine at hs'
          split at hs'
          · next n us heq =>
            split at hs'
            · next n' us' heq' => exact ⟨n', us', heq'⟩
            · exact nomatch hs'
          · exact nomatch hs'
        have hA : Setlec.whnfLoop (Setlec.pureFns μ env (max f₁ ga'))
            env d' (la'' + 1) a' = .ok (.sort ℓa') := by
          rw [whnfLoop_succ]
          exact whnfStep_assemble_delta
            (hm.2.2.1 (Nat.le_max_left f₁ ga')
              (whnfCore_reidem_const hm hwa heqa))
            (hm.2.2.2.2 (Nat.le_max_right f₁ ga') hrga) hux
            (whnfLoop_r_mono hm (Nat.le_max_right f₁ ga') hkx)
        have hB2 : Setlec.whnfLoop (Setlec.pureFns μ env (max f₂ gb'))
            env d' (lb'' + 1) b' = .ok (.sort ℓb') := by
          rw [whnfLoop_succ]
          exact whnfStep_assemble_delta
            (hm.2.2.1 (Nat.le_max_left f₂ gb')
              (whnfCore_reidem_const hm hwb heqb))
            (hm.2.2.2.2 (Nat.le_max_right f₂ gb') hrgb) huy
            (whnfLoop_r_mono hm (Nat.le_max_right f₂ gb') hky)
        have hIa2 := hIC hwa hIa'
        have hIb2 := hIC hwb hIb'
        unfold Setlec.defeqSpine at hs
        split at hs
        · next n us heqa2 =>
          split at hs
          · next n' us' heqb2 =>
            split at hs
            · next hcond =>
              obtain ⟨rfl, hlen⟩ := hcond
              split at hs
              · next heql =>
                obtain ⟨hlen', hcerts⟩ := defEqList_extract hs
                have hzip : CertZip μ env fc d' a' b' := by
                  rw [← Setlec.Expr.mkAppN_getApp a',
                    ← Setlec.Expr.mkAppN_getApp b', heqa2, heqb2]
                  exact certZip_mkAppN
                    (.constSlack n us us' fun φ' =>
                      evalEqList_map
                        (Setlec.Level.isEquivList_sound heql φ'))
                    hlen' (getAppArgs_bounded hIa2.2.1)
                    (getAppArgs_bounded hIb2.2.1) hcerts
                exact below (Nat.lt_succ_self fc) hzip
                  hIa2 hIb2
                  ((hLC hwb ((hLC hwa hPab').symm)).symm)
                  (hQs (hQC hwb (hQs (hQC hwa hQab')))) hA hB2
              · exact nomatch hs
            · exact nomatch hs
          · exact nomatch hs
        · exact nomatch hs
      · obtain rfl := hstopB
        unfold Setlec.defeqSpine at hs
        split at hs
        · exact nomatch hs
        · exact nomatch hs
    · obtain rfl := hstopA
      unfold Setlec.defeqSpine at hs
      exact nomatch hs
  exact certLoop_sortAgree (φ := φ) (Q := Q) hm hIC hID hIN
    hLC hLD hLN hQC hQD hQN hQs hP hR hE hN fc hSp
    Setlec.defeqLoopFuel hc hIa hIb hp hQ ha hb

/-! ### The StoredWF supply kit (instantiation preservation) -/

/-- Level instantiation creates no fvar leaves. -/
theorem instL_fvarLeaves_nil {lps : List Name} {us : List Level} :
    ∀ {e : Expr}, e.fvarLeaves = [] →
      (e.instantiateLevelParams lps us).fvarLeaves = [] := by
  intro e
  induction e with
  | bvar i =>
    intro h
    simp [Setlec.Expr.instantiateLevelParams, Setlec.Expr.fvarLeaves]
  | fvar idx n ty ih =>
    intro h
    simp [Setlec.Expr.fvarLeaves] at h
  | sort u =>
    intro h
    simp [Setlec.Expr.instantiateLevelParams, Setlec.Expr.fvarLeaves]
  | const n vs =>
    intro h
    simp [Setlec.Expr.instantiateLevelParams, Setlec.Expr.fvarLeaves]
  | app f a ihf iha =>
    intro h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, ihf h.1, iha h.2, List.append_nil]
  | lam n ty body m iht ihb =>
    intro h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, iht h.1, ihb h.2, List.append_nil]
  | forallE n ty body m iht ihb =>
    intro h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, iht h.1, ihb h.2, List.append_nil]
  | letE n ty val body iht ihv ihb =>
    intro h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, iht h1, ihv h2, ihb h3,
      List.append_nil]
  | lit l =>
    intro h
    simp [Setlec.Expr.instantiateLevelParams, Setlec.Expr.fvarLeaves]
  | proj sn i e ih =>
    intro h
    simp only [Setlec.Expr.fvarLeaves] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.fvarLeaves, ih h]

/-- Level instantiation touches no bvars. -/
theorem instL_looseBVarsBounded {lps : List Name} {us : List Level} :
    ∀ {e : Expr} {k : Nat}, e.looseBVarsBounded k = true →
      (e.instantiateLevelParams lps us).looseBVarsBounded k = true := by
  intro e
  induction e with
  | bvar i =>
    intro k h
    simpa [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded] using h
  | fvar idx n ty ih =>
    intro k h
    simp [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded]
  | sort u =>
    intro k h
    simp [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded]
  | const n vs =>
    intro k h
    simp [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded]
  | app f a ihf iha =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, ihf h.1, iha h.2,
      Bool.and_self]
  | lam n ty body m iht ihb =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, iht h.1, ihb h.2,
      Bool.and_self]
  | forallE n ty body m iht ihb =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, iht h.1, ihb h.2,
      Bool.and_self]
  | letE n ty val body iht ihv ihb =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, iht h1, ihv h2, ihb h3,
      Bool.and_self]
  | lit l =>
    intro k h
    simp [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded]
  | proj sn i e ih =>
    intro k h
    simp only [Setlec.Expr.looseBVarsBounded] at h
    simp only [Setlec.Expr.instantiateLevelParams,
      Setlec.Expr.looseBVarsBounded, ih h]

/-- Fvar-leaf-free expressions are well-scoped at any depth. -/
theorem wScoped_of_fvarLeaves_nil :
    ∀ {e : Expr} {d : Nat}, e.fvarLeaves = [] → Expr.WScoped d e := by
  intro e
  induction e with
  | bvar i => intro d h; simp [Setlec.Expr.WScoped]
  | fvar idx n ty ih =>
    intro d h
    simp [Setlec.Expr.fvarLeaves] at h
  | sort u => intro d h; simp [Setlec.Expr.WScoped]
  | const n vs => intro d h; simp [Setlec.Expr.WScoped]
  | app f a ihf iha =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.WScoped]
    exact ⟨ihf h.1, iha h.2⟩
  | lam n ty body m iht ihb =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.WScoped]
    exact ⟨iht h.1, ihb h.2⟩
  | forallE n ty body m iht ihb =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    simp only [Setlec.Expr.WScoped]
    exact ⟨iht h.1, ihb h.2⟩
  | letE n ty val body iht ihv ihb =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves, List.append_eq_nil_iff] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [Setlec.Expr.WScoped]
    exact ⟨iht h1, ihv h2, ihb h3⟩
  | lit l => intro d h; simp [Setlec.Expr.WScoped]
  | proj sn i e ih =>
    intro d h
    simp only [Setlec.Expr.fvarLeaves] at h
    simp only [Setlec.Expr.WScoped]
    exact ih h

/-- The `SubjInv` package for an fvar-leaf-free, bvar-closed
expression. -/
theorem subjInv_of_nil {e : Expr} {d : Nat}
    (h1 : e.fvarLeaves = []) (h2 : e.looseBVarsBounded 0 = true) :
    SubjInv d e :=
  ⟨wScoped_of_fvarLeaves_nil h1, h2,
    fun l hl => absurd hl (by rw [h1]; exact List.not_mem_nil),
    fun l hl => absurd hl (by
      rw [List.mem_append, h1] at hl
      exact absurd (hl.elim id id) List.not_mem_nil)⟩

/-- Pairing is vacuous on fvar-leaf-free pairs. -/
theorem pairedLeaves_of_nil {a b : Expr}
    (h1 : a.fvarLeaves = []) (h2 : b.fvarLeaves = []) :
    PairedLeaves a b := by
  intro l hl
  rw [h1, h2] at hl
  exact absurd hl List.not_mem_nil

/-- Both instantiations of a same-head δ unfold together (the guard
reads only the length). -/
theorem unfoldDefinition_const_both {env : Env} {n : Name}
    {us us' : List Level} {xa : Expr}
    (hlen : us.length = us'.length)
    (hux : Setlec.unfoldDefinition env (.const n us) = some xa) :
    ∃ cv value, xa
        = Setlec.Expr.instantiateLevelParams cv.levelParams us value ∧
      Setlec.unfoldDefinition env (.const n us')
        = some (Setlec.Expr.instantiateLevelParams
            cv.levelParams us' value) ∧
      ((∃ hint, env.find? n = some (.defnInfo cv value hint)) ∨
        env.find? n = some (.thmInfo cv value)) := by
  unfold Setlec.unfoldDefinition at hux
  simp only [Setlec.Expr.getAppFn] at hux
  cases hf : env.find? n with
  | none => rw [hf] at hux; exact nomatch hux
  | some ci =>
    rw [hf] at hux
    cases ci with
    | defnInfo cv value hint =>
      simp only [] at hux
      by_cases hl : us.length = cv.levelParams.length
      · rw [if_pos hl] at hux
        refine ⟨cv, value, ?_, ?_, .inl ⟨hint, rfl⟩⟩
        · have h2 := Option.some.inj hux
          simp only [Setlec.Expr.getAppArgs,
            Setlec.Expr.mkAppN] at h2
          exact h2.symm
        · simp only [Setlec.unfoldDefinition, Setlec.Expr.getAppFn,
            hf]
          rw [if_pos (hlen ▸ hl)]
          simp [Setlec.Expr.getAppArgs, Setlec.Expr.mkAppN]
      · rw [if_neg hl] at hux; exact nomatch hux
    | thmInfo cv value =>
      simp only [] at hux
      by_cases hl : us.length = cv.levelParams.length
      · rw [if_pos hl] at hux
        refine ⟨cv, value, ?_, ?_, .inr rfl⟩
        · have h2 := Option.some.inj hux
          simp only [Setlec.Expr.getAppArgs,
            Setlec.Expr.mkAppN] at h2
          exact h2.symm
        · simp only [Setlec.unfoldDefinition, Setlec.Expr.getAppFn,
            hf]
          rw [if_pos (hlen ▸ hl)]
          simp [Setlec.Expr.getAppArgs, Setlec.Expr.mkAppN]
      · rw [if_neg hl] at hux; exact nomatch hux
    | axiomInfo cv => exact nomatch hux
    | indInfo cv caps => exact nomatch hux
    | ctorInfo cv a b => exact nomatch hux
    | recInfo cv a b c => exact nomatch hux
    | projInfo entry => exact nomatch hux

/-- **The constSlack case DISCHARGED** (both-δ of one stored value):
the two sides unfold together, the continuations are
`certZip_instantiate` zips with the `StoredWF` package, and the
recursion runs at the same cert fuel with a smaller loop-budget
sum. -/
theorem zipConstCase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hSW : StoredWF env)
    (hQD : QPreserveDeltaF env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a) :
    ZipConstCase μ env φ Q := by
  intro fc d ga la gb lb n us us' ℓa ℓb below hev hQ ha hb
  have hlen : us.length = us'.length := by
    have := congrArg List.length (hev fun _ => 0)
    simpa using this
  cases la with
  | zero => exact nomatch ha
  | succ la' =>
  cases lb with
  | zero => exact nomatch hb
  | succ lb' =>
  have haD := ha
  rw [whnfLoop_succ] at haD
  obtain ⟨a₁, hwca, htriA⟩ := whnfStep_decompose haD
  obtain rfl : a₁ = .const n us :=
    (KnotFuelDet_of_mono hm).2.2.1
      (hwca : whnfCore μ env ga d (.const n us) = .ok a₁)
      (whnfCore_const_run (Nat.le_refl 1))
  have hbD := hb
  rw [whnfLoop_succ] at hbD
  obtain ⟨b₁, hwcb, htriB⟩ := whnfStep_decompose hbD
  obtain rfl : b₁ = .const n us' :=
    (KnotFuelDet_of_mono hm).2.2.1
      (hwcb : whnfCore μ env gb d (.const n us') = .ok b₁)
      (whnfCore_const_run (Nat.le_refl 1))
  rcases htriA with ⟨x, hrx, -⟩ | ⟨-, xa, hux, hkx⟩ | ⟨-, -, hstopA⟩
  · exact nomatch hrx
  · obtain ⟨cv, value, rfl, huy', hstore⟩ :=
      unfoldDefinition_const_both hlen hux
    obtain ⟨hnil, hbnd, -⟩ := hSW hstore
    rcases htriB with ⟨y, hry, -⟩ | ⟨-, xb, huy, hky⟩ | ⟨-, hudb, -⟩
    · exact nomatch hry
    · rw [huy'] at huy
      obtain rfl := (Option.some.inj huy).symm
      exact below (Or.inr ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩)
        (certZip_instantiate hev value)
        (subjInv_of_nil (instL_fvarLeaves_nil hnil)
          (instL_looseBVarsBounded hbnd))
        (subjInv_of_nil (instL_fvarLeaves_nil hnil)
          (instL_looseBVarsBounded hbnd))
        (pairedLeaves_of_nil (instL_fvarLeaves_nil hnil)
          (instL_fvarLeaves_nil hnil))
        (hQs (hQD huy' (hQs (hQD hux hQ)))) hkx hky
    · rw [huy'] at hudb; exact nomatch hudb
  · exact nomatch hstopA

/-- **Zip inversion at two literal sorts** (the sim tier's terminal):
only `refl`, `sortSlack` and `cert` can relate two sorts, and each
forces eval-equal levels (`cert` through the landed
`isDefEqCore_sorts_eval`). -/
theorem certZip_sorts_eval {μ : CheckMode} {env : Env}
    {φ : Name → Nat} (hm : KnotFuelMono μ env)
    {fc d : Nat} {u v : Level}
    (hz : CertZip μ env fc d (.sort u) (.sort v)) :
    u.eval φ = v.eval φ := by
  cases hz with
  | refl _ => rfl
  | sortSlack _ _ hev => exact hev φ
  | cert _ _ _ _ hc => exact isDefEqCore_sorts_eval hm hc

/-- **The Θ seam, frozen** (the one routed hard case of the sim
tier): a cert-related head pair under pointwise-zipped spines, both
sort convergences given, the recursion available strictly below.
Subsumes β-under-cert-head, the exposed-argument mutual knot, and
the eta-rescue-on-cert-major seam (`as = []` is `ZipCertCase`'s
content, already discharged — this Prop's obligation is the
nonempty-spine tier).  Its discharge is the binder-opening
machinery: the head cert's `lamCong` decomposition relates OPENED
bodies at `d+1`, and connecting the substituted-with-args forms is
the Θ-motive apparatus the module docstring promised. -/
def ZipCertSpineCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {f₁ f₂ : Expr} {as bs : List Expr}
    {ℓa ℓb : Level},
    ZipBelowFc μ env φ Q fc →
    f₁.looseBVarsBounded 0 = true → f₂.looseBVarsBounded 0 = true →
    isDefEqCore μ env fc d f₁ f₂ = .ok true →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN f₁ as) →
    SubjInv d (Setlec.Expr.mkAppN f₂ bs) →
    PairedLeaves (Setlec.Expr.mkAppN f₁ as)
      (Setlec.Expr.mkAppN f₂ bs) →
    Q d (Setlec.Expr.mkAppN f₁ as) (Setlec.Expr.mkAppN f₂ bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN f₁ as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN f₂ bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The whnfCore-app internal decomposition** (the discharge
campaign's first brick): every success on an application splits into
the head's core run at knot `g` plus exactly one of the four
continuations — fired β (with the argument cert), stuck β (cert
false), fired iota, or stuck iota. -/
theorem whnfCore_app_decompose {μ : CheckMode} {env : Env}
    {g d : Nat} {f x s : Expr}
    (h : whnfCore μ env (g + 1) d (.app f x) = .ok s) :
    ∃ f', whnfCore μ env g d f = .ok f' ∧
      ((∃ n ty body m ta,
          f' = .lam n ty body m ∧
          inferTypeCore μ env g d x = .ok ta ∧
          isDefEqCore μ env g d ta ty = .ok true ∧
          whnfCore μ env g d (body.instantiate1 x) = .ok s) ∨
       (∃ n ty body m ta,
          f' = .lam n ty body m ∧
          inferTypeCore μ env g d x = .ok ta ∧
          isDefEqCore μ env g d ta ty = .ok false ∧
          s = .app f' x) ∨
       ((∀ n ty body mb, f' ≠ .lam n ty body mb) ∧
        ((∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env g) env d
            (.app f' x) = .ok (some e'') ∧
          whnfCore μ env g d e'' = .ok s) ∨
         (Setlec.iotaRec μ (Setlec.pureFns μ env g) env d
            (.app f' x) = .ok none ∧ s = .app f' x)))) := by
  rw [Setlec.whnfCore_succ] at h
  unfold Setlec.whnfCoreBody at h
  simp only [Bind.bind, Except.bind] at h
  cases hwf : (Setlec.pureFns μ env g).whnfCore d f with
  | error err => rw [hwf] at h; exact nomatch h
  | ok f' =>
  rw [hwf] at h
  simp only [] at h
  refine ⟨f', hwf, ?_⟩
  split at h
  · next n ty body mb =>
    cases hinf : (Setlec.pureFns μ env g).infer d x with
    | error err => rw [hinf] at h; exact nomatch h
    | ok ta =>
    rw [hinf] at h
    simp only [] at h
    cases hdq : (Setlec.pureFns μ env g).defeq d ta ty with
    | error err => rw [hdq] at h; exact nomatch h
    | ok c =>
    rw [hdq] at h
    simp only [] at h
    cases c with
    | true =>
      rw [if_pos rfl] at h
      exact .inl ⟨n, ty, body, mb, ta, rfl, hinf, hdq, h⟩
    | false =>
      rw [if_neg Bool.false_ne_true] at h
      exact .inr (.inl ⟨n, ty, body, mb, ta, rfl, hinf, hdq,
        (Except.ok.inj h).symm⟩)
  · next hne =>
    cases hio : Setlec.iotaRec μ (Setlec.pureFns μ env g) env d
        (.app f' x) with
    | error err => rw [hio] at h; exact nomatch h
    | ok o =>
    rw [hio] at h
    simp only [] at h
    cases o with
    | some e'' =>
      exact .inr (.inr ⟨fun n ty body mb heq => hne n ty body mb heq,
        .inl ⟨e'', rfl, h⟩⟩)
    | none =>
      exact .inr (.inr ⟨fun n ty body mb heq => hne n ty body mb heq,
        .inr ⟨rfl, (Except.ok.inj h).symm⟩⟩)

/-- **The app-layer assemble** (the decompose's inverse): a head run
plus a leg package build the layer's core run at joined fuel.  The
connecting runs of re-based seams are assembled with this — the
seam's own head run replaces the original's, the original legs are
reused verbatim. -/
theorem whnfCore_app_assemble {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {g gl d : Nat} {P y h' s : Expr}
    (hh : whnfCore μ env g d P = .ok h')
    (hlegs :
      (∃ n ty body mb ta,
          h' = .lam n ty body mb ∧
          inferTypeCore μ env gl d y = .ok ta ∧
          isDefEqCore μ env gl d ta ty = .ok true ∧
          whnfCore μ env gl d (body.instantiate1 y) = .ok s) ∨
      (∃ n ty body mb ta,
          h' = .lam n ty body mb ∧
          inferTypeCore μ env gl d y = .ok ta ∧
          isDefEqCore μ env gl d ta ty = .ok false ∧
          s = .app h' y) ∨
      ((∀ n ty body mb, h' ≠ .lam n ty body mb) ∧
       ((∃ e'', Setlec.iotaRec μ (Setlec.pureFns μ env gl) env d
            (.app h' y) = .ok (some e'') ∧
          whnfCore μ env gl d e'' = .ok s) ∨
        (Setlec.iotaRec μ (Setlec.pureFns μ env gl) env d
            (.app h' y) = .ok none ∧ s = .app h' y)))) :
    whnfCore μ env (max g gl + 1) d (.app P y) = .ok s := by
  have hh' : (Setlec.pureFns μ env (max g gl)).whnfCore d P
      = .ok h' :=
    hm.2.2.1 (Nat.le_max_left g gl) hh
  rw [show whnfCore μ env (max g gl + 1) d (.app P y)
      = Setlec.whnfCoreBody μ (Setlec.pureFns μ env (max g gl)) env d
        (.app P y) from Setlec.whnfCore_succ ..]
  unfold Setlec.whnfCoreBody
  simp only [Bind.bind, Except.bind]
  rw [hh']
  simp only []
  rcases hlegs with ⟨n, ty, body, mb, ta, rfl, hinf, hdq, hrun⟩ |
    ⟨n, ty, body, mb, ta, rfl, hinf, hdq, rfl⟩ | ⟨hnl, hio⟩
  · simp only []
    rw [show (Setlec.pureFns μ env (max g gl)).infer d y = .ok ta
      from hm.1 (Nat.le_max_right g gl) hinf]
    simp only []
    rw [show (Setlec.pureFns μ env (max g gl)).defeq d ta ty
        = .ok true
      from hm.2.2.2.1 (Nat.le_max_right g gl) hdq]
    simp only []
    rw [if_pos trivial]
    exact hm.2.2.1 (Nat.le_max_right g gl) hrun
  · simp only []
    rw [show (Setlec.pureFns μ env (max g gl)).infer d y = .ok ta
      from hm.1 (Nat.le_max_right g gl) hinf]
    simp only []
    rw [show (Setlec.pureFns μ env (max g gl)).defeq d ta ty
        = .ok false
      from hm.2.2.2.1 (Nat.le_max_right g gl) hdq]
    simp only []
    rw [if_neg Bool.false_ne_true]
    rfl
  · rcases hio with ⟨e'', hio, hrun⟩ | ⟨hio, rfl⟩
    · have hioG := iotaRec_mono
        (coreSub_le μ env (Nat.le_max_right g gl)) hio
      have hrunG : (Setlec.pureFns μ env (max g gl)).whnfCore d e''
          = .ok s :=
        hm.2.2.1 (Nat.le_max_right g gl) hrun
      cases h' with
      | lam n2 ty2 b2 m2 => exact absurd rfl (hnl n2 ty2 b2 m2)
      | bvar i =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | fvar i n2 ty2 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | sort u0 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | const n2 us2 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | app p q =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | forallE n2 ty2 b2 m2 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | letE n2 ty2 v2 b2 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | lit l =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
      | proj sn i e0 =>
        simp only []; rw [hioG]
        simp only []; exact hrunG
    · have hioG := iotaRec_mono
        (coreSub_le μ env (Nat.le_max_right g gl)) hio
      cases h' with
      | lam n2 ty2 b2 m2 => exact absurd rfl (hnl n2 ty2 b2 m2)
      | bvar i =>
        simp only []; rw [hioG]; rfl
      | fvar i n2 ty2 =>
        simp only []; rw [hioG]; rfl
      | sort u0 =>
        simp only []; rw [hioG]; rfl
      | const n2 us2 =>
        simp only []; rw [hioG]; rfl
      | app p q =>
        simp only []; rw [hioG]; rfl
      | forallE n2 ty2 b2 m2 =>
        simp only []; rw [hioG]; rfl
      | letE n2 ty2 v2 b2 =>
        simp only []; rw [hioG]; rfl
      | lit l =>
        simp only []; rw [hioG]; rfl
      | proj sn i e0 =>
        simp only []; rw [hioG]; rfl

/-- Zeta is one knot level down (the letE analog of the app
decomposition). -/
theorem whnfCore_letE_step {μ : CheckMode} {env : Env}
    {g d : Nat} {n : Name} {ty v b s : Expr} :
    whnfCore μ env (g + 1) d (.letE n ty v b) = .ok s ↔
    whnfCore μ env g d (b.instantiate1 v) = .ok s := by
  rw [Setlec.whnfCore_succ]
  exact Iff.rfl

/-- `getAppFn` outputs are never applications. -/
theorem getAppFn_not_app : ∀ {e p q : Expr},
    e.getAppFn ≠ .app p q := by
  intro e
  induction e with
  | app f a ihf iha =>
    intro p q h
    rw [show (Expr.app f a).getAppFn = f.getAppFn from rfl] at h
    exact ihf h
  | bvar i => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | fvar idx n ty ih => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | sort u => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | const n us => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | lam n ty body m iht ihb =>
    intro p q h; simp [Setlec.Expr.getAppFn] at h
  | forallE n ty body m iht ihb =>
    intro p q h; simp [Setlec.Expr.getAppFn] at h
  | letE n ty val body iht ihv ihb =>
    intro p q h; simp [Setlec.Expr.getAppFn] at h
  | lit l => intro p q h; simp [Setlec.Expr.getAppFn] at h
  | proj sn i e ih => intro p q h; simp [Setlec.Expr.getAppFn] at h

/-- One-step spine extension of the fold. -/
theorem mkAppN_append_one {f a : Expr} : ∀ {as : List Expr},
    Setlec.Expr.mkAppN f (as ++ [a])
      = .app (Setlec.Expr.mkAppN f as) a := by
  intro as
  induction as generalizing f with
  | nil => rfl
  | cons b bs ih =>
    show Setlec.Expr.mkAppN (.app f b) (bs ++ [a]) = _
    rw [ih]
    rfl

/-- Left-part indexing of an appended singleton (self-contained; the
core lemma names shift across toolchains). -/
theorem getElem_append_left' {α : Type _} :
    ∀ (l₁ l₂ : List α) (i : Nat) (h : i < l₁.length)
      {h' : i < (l₁ ++ l₂).length},
      (l₁ ++ l₂)[i]'h' = l₁[i]'h
  | _ :: _, _, 0, _, _ => rfl
  | _ :: xs, l₂, i + 1, h, _ =>
    getElem_append_left' xs l₂ i (Nat.lt_of_succ_lt_succ h)
  | [], _, i, h, _ => absurd h (Nat.not_lt_zero i)

/-- The appended element sits at the old length. -/
theorem getElem_append_last {α : Type _} :
    ∀ (l : List α) (a : α) {h : l.length < (l ++ [a]).length},
      (l ++ [a])[l.length]'h = a
  | [], _, _ => rfl
  | _ :: xs, a, _ => getElem_append_last xs a

/-- **The spine view**: every zip flattens to a head zip over
pointwise-zipped argument lists, where the head is either a
certified pair (possibly app-shaped — the Θ seam's territory) or a
non-application zip node (the case analysis' terminating heads). -/
theorem certZip_app_view {μ : CheckMode} {env : Env} {fc d : Nat} :
    ∀ {u v : Expr}, CertZip μ env fc d u v →
    ∃ (F₁ F₂ : Expr) (as bs : List Expr),
      u = Setlec.Expr.mkAppN F₁ as ∧ v = Setlec.Expr.mkAppN F₂ bs ∧
      as.length = bs.length ∧
      (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) ∧
      ((F₁.looseBVarsBounded 0 = true ∧ F₂.looseBVarsBounded 0 = true ∧
        isDefEqCore μ env fc d F₁ F₂ = .ok true) ∨
       ((∀ p q, F₁ ≠ .app p q) ∧ (∀ p q, F₂ ≠ .app p q) ∧
        CertZip μ env fc d F₁ F₂)) := by
  intro u v hz
  induction hz with
  | app h₁ y₁ h₂ y₂ hh hy ihh ihy =>
    obtain ⟨F₁, F₂, as, bs, rfl, rfl, hlen, hargs, hhead⟩ := ihh
    refine ⟨F₁, F₂, as ++ [y₁], bs ++ [y₂], ?_, ?_, ?_, ?_, hhead⟩
    · rw [mkAppN_append_one]
    · rw [mkAppN_append_one]
    · simp [hlen]
    · intro i hi₁ hi₂
      by_cases hlt : i < as.length
      · have hlt₂ : i < bs.length := hlen ▸ hlt
        rw [getElem_append_left' as [y₁] i hlt,
          getElem_append_left' bs [y₂] i hlt₂]
        exact hargs i hlt hlt₂
      · have hi : i = as.length := by
          simp only [List.length_append, List.length_cons,
            List.length_nil] at hi₁
          omega
        subst hi
        rw [getElem_append_last as y₁]
        simp only [hlen]
        rw [getElem_append_last bs y₂]
        exact hy
  | cert a b hba hbb hc =>
    exact ⟨a, b, [], [], rfl, rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inl ⟨hba, hbb, hc⟩⟩
  | refl e =>
    exact ⟨e.getAppFn, e.getAppFn, e.getAppArgs, e.getAppArgs,
      (Setlec.Expr.mkAppN_getApp e).symm,
      (Setlec.Expr.mkAppN_getApp e).symm, rfl,
      (fun i h₁ h₂ => CertZip.refl _),
      Or.inr ⟨(fun p q => getAppFn_not_app),
        (fun p q => getAppFn_not_app), CertZip.refl _⟩⟩
  | sortSlack w x hev =>
    exact ⟨.sort w, .sort x, [], [], rfl, rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.sortSlack _ _ hev⟩⟩
  | constSlack n us us' hev =>
    exact ⟨.const n us, .const n us', [], [], rfl, rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.constSlack _ _ _ hev⟩⟩
  | fvar i n ty₁ ty₂ hty ihty =>
    exact ⟨.fvar i n ty₁, .fvar i n ty₂, [], [], rfl, rfl, rfl,
      (fun j h₁ _ => absurd h₁ (Nat.not_lt_zero j)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.fvar _ _ _ _ hty⟩⟩
  | lam n ty₁ ty₂ b₁ b₂ m₁ m₂ hty hbody ihty ihbody =>
    exact ⟨.lam n ty₁ b₁ m₁, .lam n ty₂ b₂ m₂, [], [], rfl, rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.lam _ _ _ _ _ _ _ hty hbody⟩⟩
  | forallE n ty₁ ty₂ b₁ b₂ m₁ m₂ hty hbody ihty ihbody =>
    exact ⟨.forallE n ty₁ b₁ m₁, .forallE n ty₂ b₂ m₂, [], [], rfl,
      rfl, rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.forallE _ _ _ _ _ _ _ hty hbody⟩⟩
  | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody ihty ihval ihbody =>
    exact ⟨.letE n ty₁ v₁ b₁, .letE n ty₂ v₂ b₂, [], [], rfl, rfl,
      rfl,
      (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.letE _ _ _ _ _ _ _ hty hval hbody⟩⟩
  | proj sn i e₁ e₂ he ihe =>
    exact ⟨.proj sn i e₁, .proj sn i e₂, [], [], rfl, rfl, rfl,
      (fun j h₁ _ => absurd h₁ (Nat.not_lt_zero j)),
      Or.inr ⟨(fun p q h => nomatch h), (fun p q h => nomatch h),
        CertZip.proj _ _ _ _ he⟩⟩

/-- **The flat-spine leg** (the campaign's one remaining sim
routing): a NON-application head zip over pointwise-zipped spines,
both sort convergences given.  Every non-cert-headed shape funnels
here through the view — including empty-spine letE/proj/congruence
pairs — and its discharge is the F-driven analysis (refl heads
det-synchronized, lam-congruence β through `certZip_subst`,
constSlack through the iota/δ lockstep, shape-stuck vacuities). -/
def ZipSpineFlatCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {F₁ F₂ : Expr} {as bs : List Expr}
    {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    (∀ p q, F₁ ≠ .app p q) → (∀ p q, F₂ ≠ .app p q) →
    CertZip μ env fc d F₁ F₂ →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN F₁ as) →
    SubjInv d (Setlec.Expr.mkAppN F₂ bs) →
    PairedLeaves (Setlec.Expr.mkAppN F₁ as)
      (Setlec.Expr.mkAppN F₂ bs) →
    Q d (Setlec.Expr.mkAppN F₁ as) (Setlec.Expr.mkAppN F₂ bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN F₁ as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN F₂ bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The app wrapper DISCHARGED**: view, then dispatch — cert heads
to the Θ seam, everything else to the flat-spine leg. -/
theorem zipAppCase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hSpine : ZipSpineFlatCase μ env φ Q) :
    ZipAppCase μ env φ Q := by
  intro fc d ga la gb lb f₁ x₁ f₂ x₂ ℓa ℓb below hf hx hIs hIt hp
    hQ ha hb
  obtain ⟨F₁, F₂, as, bs, hu, hv, hlen, hargs, hhead⟩ :=
    certZip_app_view (CertZip.app f₁ x₁ f₂ x₂ hf hx)
  rw [hu] at hIs ha
  rw [hv] at hIt hb
  rw [hu, hv] at hp hQ
  rcases hhead with ⟨hba, hbb, hc⟩ | ⟨hne₁, hne₂, hFz⟩
  · exact hΘ
      (fun hlt hz' hIs' hIt' hp' hQ' ha' hb' =>
        below (Or.inl hlt) hz' hIs' hIt' hp' hQ' ha' hb')
      hba hbb hc hlen hargs hIs hIt hp hQ ha hb
  · exact hSpine below hne₁ hne₂ hFz hlen hargs hIs hIt hp hQ ha hb

/-- **The letE wrapper DISCHARGED**: a letE pair is a non-app head
with an empty spine — straight to the flat-spine leg. -/
theorem zipLetECase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hSpine : ZipSpineFlatCase μ env φ Q) :
    ZipLetECase μ env φ Q := by
  intro fc d ga la gb lb n ty₁ ty₂ v₁ v₂ b₁ b₂ ℓa ℓb below hty hval
    hbody hIs hIt hp hQ ha hb
  exact hSpine (F₁ := .letE n ty₁ v₁ b₁) (F₂ := .letE n ty₂ v₂ b₂)
    (as := []) (bs := []) below
    (fun p q h => nomatch h) (fun p q h => nomatch h)
    (CertZip.letE _ _ _ _ _ _ _ hty hval hbody) rfl
    (fun i h₁ _ => absurd h₁ (Nat.not_lt_zero i))
    hIs hIt hp hQ ha hb

/-- **The proj wrapper DISCHARGED**: likewise a bare non-app head. -/
theorem zipProjCase_of {φ : Name → Nat} {Q : Nat → Expr → Expr → Prop}
    (hSpine : ZipSpineFlatCase μ env φ Q) :
    ZipProjCase μ env φ Q := by
  intro fc d ga la gb lb i sn e₁ e₂ ℓa ℓb below he hIs hIt hp hQ
    ha hb
  exact hSpine (F₁ := .proj sn i e₁) (F₂ := .proj sn i e₂)
    (as := []) (bs := []) below
    (fun p q h => nomatch h) (fun p q h => nomatch h)
    (CertZip.proj _ _ _ _ he) rfl
    (fun j h₁ _ => absurd h₁ (Nat.not_lt_zero j))
    hIs hIt hp hQ ha hb

/-- **The summit at its two sim obligations**: `ZipWhnfSortAgree`
from the Θ seam and the flat-spine leg (plus the trio's Q-frame
vacuities and the env facts).  Every structural case is
discharged. -/
theorem zipWhnfSortAgree_of_two {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hSW : StoredWF env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hSpine : ZipSpineFlatCase μ env φ Q) :
    ZipWhnfSortAgree μ env φ Q :=
  zipWhnfSortAgree_of (φ := φ) (Q := Q) hm
    (zipCertCase_of (φ := φ) (Q := Q) hm hB hIC hID hIN hLC hLD hLN
      hQC hQD hQN hQs hP hR hE)
    (zipConstCase_of (φ := φ) (Q := Q) hm hSW hQD hQs)
    (zipAppCase_of (φ := φ) (Q := Q) hΘ hSpine)
    (zipLetECase_of (φ := φ) (Q := Q) hSpine)
    (zipProjCase_of (φ := φ) (Q := Q) hSpine)

/-! ### The flat-spine bases kit -/

/-- Pure congruence fold: a zipped head under pointwise-zipped
arguments stays zipped (no cert leaves manufactured). -/
theorem certZip_mkAppN_zips {μ : CheckMode} {env : Env} {fc d : Nat} :
    ∀ {as bs : List Expr} {F₁ F₂ : Expr},
      CertZip μ env fc d F₁ F₂ →
      as.length = bs.length →
      (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
        CertZip μ env fc d as[i] bs[i]) →
      CertZip μ env fc d (Setlec.Expr.mkAppN F₁ as)
        (Setlec.Expr.mkAppN F₂ bs) := by
  intro as
  induction as with
  | nil =>
    intro bs F₁ F₂ hz hlen hargs
    cases bs with
    | nil => exact hz
    | cons b bs => exact nomatch hlen
  | cons a as ih =>
    intro bs F₁ F₂ hz hlen hargs
    cases bs with
    | nil => exact nomatch hlen
    | cons b bs =>
      simp only [Setlec.Expr.mkAppN]
      exact ih
        (.app _ _ _ _ hz
          (hargs 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)))
        (by simpa using hlen)
        (fun i h₁ h₂ =>
          hargs (i + 1)
            (by simp only [List.length_cons]; omega)
            (by simp only [List.length_cons]; omega))

/-- A non-const-headed subject never iota-fires. -/
theorem iotaRec_none_of_fn_not_const {μ : CheckMode} {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e : Expr}
    (h : ∀ n us, e.getAppFn ≠ .const n us) :
    Setlec.iotaRec μ r env d e = .ok none := by
  unfold Setlec.iotaRec
  split
  · next n us heq => exact absurd heq (h n us)
  · rfl

/-- A non-const-headed subject never δ-unfolds. -/
theorem unfoldDefinition_none_of_fn_not_const {env : Env} {e : Expr}
    (h : ∀ n us, e.getAppFn ≠ .const n us) :
    Setlec.unfoldDefinition env e = none := by
  unfold Setlec.unfoldDefinition
  split
  · next n us heq => exact absurd heq (h n us)
  · rfl

/-- A non-const-headed subject never nat-steps. -/
theorem reduceNat_none_of_fn_not_const {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e : Expr}
    (h : ∀ n us, e.getAppFn ≠ .const n us) :
    Setlec.reduceNat r env d e = .ok none := by
  unfold Setlec.reduceNat
  split
  · next c a =>
    exact absurd (show (Expr.app (.const c []) a).getAppFn
        = .const c [] from rfl) (h c [])
  · next c a b =>
    exact absurd (show (Expr.app (.app (.const c []) a) b).getAppFn
        = .const c [] from rfl) (h c [])
  · rfl

/-- **Spine inertness**: a stuck, non-λ, non-const-headed head keeps
its whole spine stuck (fuel grows one per spine layer). -/
theorem whnfCore_mkAppN_inert {μ : CheckMode} {env : Env} {d : Nat} :
    ∀ (as : List Expr) {F : Expr} {hd : Nat},
      (∀ g, hd ≤ g → whnfCore μ env g d F = .ok F) →
      (∀ n ty body m, F ≠ .lam n ty body m) →
      (∀ n us, F.getAppFn ≠ .const n us) →
      ∀ {g : Nat}, hd + as.length ≤ g →
        whnfCore μ env g d (Setlec.Expr.mkAppN F as)
          = .ok (Setlec.Expr.mkAppN F as) := by
  intro as
  induction as with
  | nil =>
    intro F hd hF _ _ g hg
    exact hF g (by simpa using hg)
  | cons a as ih =>
    intro F hd hF hnl hnc g hg
    show whnfCore μ env g d (Setlec.Expr.mkAppN (.app F a) as) = _
    refine ih (F := .app F a) (hd := hd + 1) ?_ ?_ ?_ ?_
    · intro g' hg'
      cases g' with
      | zero => exact absurd hg' (by omega)
      | succ g'' =>
        rw [show whnfCore μ env (g'' + 1) d (.app F a)
            = Setlec.whnfCoreBody μ (Setlec.pureFns μ env g'') env d
              (.app F a) from Setlec.whnfCore_succ ..]
        have hiota : Setlec.iotaRec μ (Setlec.pureFns μ env g'') env d
            (.app F a) = .ok none :=
          iotaRec_none_of_fn_not_const
            (by intro n us hh
                exact hnc n us
                  ((show (Expr.app F a).getAppFn = F.getAppFn
                    from rfl) ▸ hh))
        have hFrun : (Setlec.pureFns μ env g'').whnfCore d F
            = .ok F := hF g'' (by omega)
        cases F with
        | lam n ty body m => exact absurd rfl (hnl n ty body m)
        | const n us =>
          exact absurd (show (Expr.const n us).getAppFn
            = .const n us from rfl) (hnc n us)
        | bvar i =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | fvar i n ty =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | sort u =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | forallE n ty body m =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | letE n ty v b =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | lit l =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | proj sn i e =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
        | app p q =>
          unfold Setlec.whnfCoreBody
          simp only [Bind.bind, Except.bind]
          rw [hFrun]
          simp only []
          rw [hiota]
          rfl
    · intro n ty body m hh; exact nomatch hh
    · intro n us hh
      exact hnc n us
        ((show (Expr.app F a).getAppFn = F.getAppFn from rfl) ▸ hh)
    · simp only [List.length_cons] at hg ⊢
      omega

/-- Nonempty spines are application-shaped. -/
theorem mkAppN_cons_app {F a : Expr} : ∀ {as : List Expr},
    ∃ p q, Setlec.Expr.mkAppN F (a :: as) = .app p q := by
  intro as
  induction as generalizing F a with
  | nil => exact ⟨F, a, rfl⟩
  | cons b bs ih => exact ih (F := .app F a) (a := b)

/-- The spine head inherits the bvar bound. -/
theorem mkAppN_bounded_head {k : Nat} : ∀ {as : List Expr} {F : Expr},
    (Setlec.Expr.mkAppN F as).looseBVarsBounded k = true →
    F.looseBVarsBounded k = true := by
  intro as
  induction as with
  | nil => intro F h; exact h
  | cons a as ih =>
    intro F h
    have := ih (F := .app F a) h
    simp only [Setlec.Expr.looseBVarsBounded, Bool.and_eq_true]
      at this
    exact this.1

/-- **The inert-spine loop terminal**: an inert head pins the loop
output to the spine itself. -/
theorem spine_inert_out {μ : CheckMode} {env : Env}
    (hm : KnotFuelMono μ env) {d ga la : Nat} {F : Expr}
    {as : List Expr} {ℓ : Level}
    (hF : ∀ g, 1 ≤ g → whnfCore μ env g d F = .ok F)
    (hnl : ∀ n ty body m, F ≠ .lam n ty body m)
    (hnc : ∀ n us, F.getAppFn ≠ .const n us)
    (hloop : Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN F as) = .ok (.sort ℓ)) :
    Expr.sort ℓ = Setlec.Expr.mkAppN F as := by
  have hncS : ∀ n us,
      (Setlec.Expr.mkAppN F as).getAppFn ≠ .const n us := by
    intro n us h
    exact hnc n us (Setlec.Expr.getAppFn_mkAppN as F ▸ h)
  exact loop_stuck_out hm hloop
    (whnfCore_mkAppN_inert as (hd := 1) hF hnl hnc (Nat.le_refl _))
    (fun _ => reduceNat_none_of_fn_not_const hncS)
    (unfoldDefinition_none_of_fn_not_const hncS)

/-! ### The routed head cases of the flat-spine leg -/

/-- Const-headed spines at eval-linked levels (δ, iota — the iota
lockstep's home — and the nat-op vacuities). -/
def ZipConstHeadCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name} {us us' : List Level}
    {as bs : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us) as) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us') bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Q d (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.const n us) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.const n us') bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- λ-headed spines (the β-chain: reassociation + spine-length
induction). -/
def ZipLamHeadCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name} {ty₁ ty₂ b₁ b₂ : Expr}
    {m₁ m₂ : Setlec.BinderMeta} {as bs : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d b₁ b₂ →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.lam n ty₁ b₁ m₁) as) →
    SubjInv d (Setlec.Expr.mkAppN (.lam n ty₂ b₂ m₂) bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.lam n ty₁ b₁ m₁) as)
      (Setlec.Expr.mkAppN (.lam n ty₂ b₂ m₂) bs) →
    Q d (Setlec.Expr.mkAppN (.lam n ty₁ b₁ m₁) as)
      (Setlec.Expr.mkAppN (.lam n ty₂ b₂ m₂) bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.lam n ty₁ b₁ m₁) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.lam n ty₂ b₂ m₂) bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- letE-headed spines (zeta under application, knot-paid). -/
def ZipLetEHeadCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb : Nat} {n : Name}
    {ty₁ ty₂ v₁ v₂ b₁ b₂ : Expr} {as bs : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d ty₁ ty₂ → CertZip μ env fc d v₁ v₂ →
    CertZip μ env fc d b₁ b₂ →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.letE n ty₁ v₁ b₁) as) →
    SubjInv d (Setlec.Expr.mkAppN (.letE n ty₂ v₂ b₂) bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.letE n ty₁ v₁ b₁) as)
      (Setlec.Expr.mkAppN (.letE n ty₂ v₂ b₂) bs) →
    Q d (Setlec.Expr.mkAppN (.letE n ty₁ v₁ b₁) as)
      (Setlec.Expr.mkAppN (.letE n ty₂ v₂ b₂) bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.letE n ty₁ v₁ b₁) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.letE n ty₂ v₂ b₂) bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- proj-headed spines (the proj clause's walk; the struct-name
slack audit lives at its seal). -/
def ZipProjHeadCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb i : Nat} {sn : Name} {e₁ e₂ : Expr}
    {as bs : List Expr} {ℓa ℓb : Level},
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    CertZip μ env fc d e₁ e₂ →
    as.length = bs.length →
    (∀ j (h₁ : j < as.length) (h₂ : j < bs.length),
      CertZip μ env fc d as[j] bs[j]) →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e₁) as) →
    SubjInv d (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.proj sn i e₁) as)
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    Q d (Setlec.Expr.mkAppN (.proj sn i e₁) as)
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.proj sn i e₁) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.proj sn i e₂) bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The flat-spine leg DISCHARGED to its four head cases**: the
stuck-shape and terminal legs inline (the bases kit), cert heads to
Θ, const/λ/letE/proj heads routed. -/
theorem zipSpineFlatCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hLam : ZipLamHeadCase μ env φ Q)
    (hLetE : ZipLetEHeadCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ZipSpineFlatCase μ env φ Q := by
  intro fc d ga la gb lb F₁ F₂ as bs ℓa ℓb below hne₁ hne₂ hFz hlen
    hargs hIs hIt hp hQ ha hb
  cases hFz with
  | app p₁ q₁ p₂ q₂ hp' hq' => exact absurd rfl (hne₁ p₁ q₁)
  | cert a b hba hbb hc =>
    exact hΘ
      (fun hlt hz' hIs' hIt' hp' hQ' ha' hb' =>
        below (Or.inl hlt) hz' hIs' hIt' hp' hQ' ha' hb')
      hba hbb hc hlen hargs hIs hIt hp hQ ha hb
  | constSlack n us us' hev =>
    exact hConst below hev hlen hargs hIs hIt hp hQ ha hb
  | lam n ty₁ ty₂ b₁ b₂ m₁ m₂ hty hbody =>
    exact hLam below hty hbody hlen hargs hIs hIt hp hQ ha hb
  | letE n ty₁ ty₂ v₁ v₂ b₁ b₂ hty hval hbody =>
    exact hLetE below hty hval hbody hlen hargs hIs hIt hp hQ ha hb
  | proj sn i e₁ e₂ he =>
    exact hProj below he hlen hargs hIs hIt hp hQ ha hb
  | sortSlack u v hev =>
    have h1 := spine_inert_out hm (F := .sort u) (as := as)
      (fun g hg => whnfCore_sort_run hg)
      (fun _ _ _ _ h => nomatch h)
      (fun n' us' h => nomatch
        ((show (Expr.sort u).getAppFn = Expr.sort u from rfl) ▸ h)) ha
    have h2 := spine_inert_out hm (F := .sort v) (as := bs)
      (fun g hg => whnfCore_sort_run hg)
      (fun _ _ _ _ h => nomatch h)
      (fun n' us' h => nomatch
        ((show (Expr.sort v).getAppFn = Expr.sort v from rfl) ▸ h)) hb
    cases as with
    | nil =>
      cases bs with
      | cons b bs => exact nomatch hlen
      | nil =>
        rw [Setlec.Expr.sort.inj h1, Setlec.Expr.sort.inj h2]
        exact hev φ
    | cons a as' =>
      obtain ⟨p, q, hpq⟩ :=
        mkAppN_cons_app (F := Expr.sort u) (a := a) (as := as')
      rw [hpq] at h1
      exact nomatch h1
  | fvar i n ty₁ ty₂ hty =>
    have h1 := spine_inert_out hm (F := .fvar i n ty₁) (as := as)
      (fun g hg => whnfCore_fvar_run hg)
      (fun _ _ _ _ h => nomatch h)
      (fun n' us' h => nomatch
        ((show (Expr.fvar i n ty₁).getAppFn = Expr.fvar i n ty₁
          from rfl) ▸ h)) ha
    cases as with
    | nil => exact nomatch h1
    | cons a as' =>
      obtain ⟨p, q, hpq⟩ :=
        mkAppN_cons_app (F := Expr.fvar i n ty₁) (a := a) (as := as')
      rw [hpq] at h1
      exact nomatch h1
  | forallE n ty₁ ty₂ b₁ b₂ m₁ m₂ hty hbody =>
    have h1 := spine_inert_out hm (F := .forallE n ty₁ b₁ m₁)
      (as := as)
      (fun g hg => whnfCore_forallE_run hg)
      (fun _ _ _ _ h => nomatch h)
      (fun n' us' h => nomatch
        ((show (Expr.forallE n ty₁ b₁ m₁).getAppFn
          = Expr.forallE n ty₁ b₁ m₁ from rfl) ▸ h)) ha
    cases as with
    | nil => exact nomatch h1
    | cons a as' =>
      obtain ⟨p, q, hpq⟩ := mkAppN_cons_app
        (F := Expr.forallE n ty₁ b₁ m₁) (a := a) (as := as')
      rw [hpq] at h1
      exact nomatch h1
  | refl _ =>
    cases F₁ with
    | app p q => exact absurd rfl (hne₁ p q)
    | bvar i =>
      have hbd := mkAppN_bounded_head (k := 0) hIs.2.1
      simp [Setlec.Expr.looseBVarsBounded] at hbd
    | const n us =>
      exact hConst below (fun _ => rfl) hlen hargs hIs hIt hp hQ
        ha hb
    | lam n ty b m =>
      exact hLam below (CertZip.refl ty) (CertZip.refl b) hlen hargs
        hIs hIt hp hQ ha hb
    | letE n ty v b =>
      exact hLetE below (CertZip.refl ty) (CertZip.refl v)
        (CertZip.refl b) hlen hargs hIs hIt hp hQ ha hb
    | proj sn i e =>
      exact hProj below (CertZip.refl e) hlen hargs hIs hIt hp hQ
        ha hb
    | sort u =>
      have h1 := spine_inert_out hm (F := .sort u) (as := as)
        (fun g hg => whnfCore_sort_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.sort u).getAppFn = Expr.sort u from rfl) ▸ h)) ha
      have h2 := spine_inert_out hm (F := .sort u) (as := bs)
        (fun g hg => whnfCore_sort_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.sort u).getAppFn = Expr.sort u from rfl) ▸ h)) hb
      cases as with
      | nil =>
        cases bs with
        | cons b bs => exact nomatch hlen
        | nil =>
          rw [Setlec.Expr.sort.inj h1, Setlec.Expr.sort.inj h2]
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ :=
          mkAppN_cons_app (F := Expr.sort u) (a := a) (as := as')
        rw [hpq] at h1
        exact nomatch h1
    | fvar i n ty =>
      have h1 := spine_inert_out hm (F := .fvar i n ty) (as := as)
        (fun g hg => whnfCore_fvar_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.fvar i n ty).getAppFn = Expr.fvar i n ty
            from rfl) ▸ h)) ha
      cases as with
      | nil => exact nomatch h1
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ :=
          mkAppN_cons_app (F := Expr.fvar i n ty) (a := a) (as := as')
        rw [hpq] at h1
        exact nomatch h1
    | lit l =>
      have h1 := spine_inert_out hm (F := .lit l) (as := as)
        (fun g hg => whnfCore_lit_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.lit l).getAppFn = Expr.lit l from rfl) ▸ h)) ha
      cases as with
      | nil => exact nomatch h1
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ :=
          mkAppN_cons_app (F := Expr.lit l) (a := a) (as := as')
        rw [hpq] at h1
        exact nomatch h1
    | forallE n ty b m =>
      have h1 := spine_inert_out hm (F := .forallE n ty b m)
        (as := as)
        (fun g hg => whnfCore_forallE_run hg)
        (fun _ _ _ _ h => nomatch h)
        (fun n' us' h => nomatch
          ((show (Expr.forallE n ty b m).getAppFn
            = Expr.forallE n ty b m from rfl) ▸ h)) ha
      cases as with
      | nil => exact nomatch h1
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ := mkAppN_cons_app
          (F := Expr.forallE n ty b m) (a := a) (as := as')
        rw [hpq] at h1
        exact nomatch h1

/-- **The summit at its head cases**: `ZipWhnfSortAgree` from the Θ
seam and the four head cases (const/λ/letE/proj), plus the trio's
Q-frame vacuities and the env facts.  The flat-spine leg is
dissolved. -/
theorem zipWhnfSortAgree_of_heads {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hSW : StoredWF env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hP : ProbeSortVacuity μ env Q) (hR : RescueSortVacuity μ env Q)
    (hE : EtaSortVacuity μ env Q)
    (hΘ : ZipCertSpineCase μ env φ Q)
    (hConst : ZipConstHeadCase μ env φ Q)
    (hLam : ZipLamHeadCase μ env φ Q)
    (hLetE : ZipLetEHeadCase μ env φ Q)
    (hProj : ZipProjHeadCase μ env φ Q) :
    ZipWhnfSortAgree μ env φ Q :=
  zipWhnfSortAgree_of_two (φ := φ) (Q := Q) hm hB hSW hIC hID hIN
    hLC hLD hLN hQC hQD hQN hQs hP hR hE hΘ
    (zipSpineFlatCase_of (φ := φ) (Q := Q) hm hΘ hConst hLam hLetE
      hProj)

/-! ### The const head: δ and nat-op legs (iota routed) -/

/-- A non-recursor const head never iota-fires. -/
theorem iotaRec_none_of_not_rec {μ : CheckMode} {env : Env}
    {r : Setlec.CoreFns Setlec.CheckM} {d : Nat} {e : Expr}
    {n : Name} {us : List Level}
    (hfn : e.getAppFn = .const n us)
    (hnr : ∀ cv mI rP rules,
      env.find? n ≠ some (.recInfo cv mI rP rules)) :
    Setlec.iotaRec μ r env d e = .ok none := by
  unfold Setlec.iotaRec
  split
  · next n' us' heq =>
    rw [hfn] at heq
    obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := by
      cases heq; exact ⟨rfl, rfl⟩
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      cases ci with
      | recInfo cv mI rP rules => exact absurd hf (hnr cv mI rP rules)
      | axiomInfo cv => rfl
      | defnInfo cv value hint => rfl
      | thmInfo cv value => rfl
      | indInfo cv caps => rfl
      | ctorInfo cv a b => rfl
      | projInfo entry => rfl
  · rfl

/-- A non-recursor const head keeps its whole spine
whnfCore-stuck. -/
theorem whnfCore_mkAppN_const_inert {μ : CheckMode} {env : Env}
    {d : Nat} {n : Name} {us : List Level}
    (hnr : ∀ cv mI rP rules,
      env.find? n ≠ some (.recInfo cv mI rP rules)) :
    ∀ (as : List Expr) {g : Nat}, 1 + as.length ≤ g →
      whnfCore μ env g d (Setlec.Expr.mkAppN (.const n us) as)
        = .ok (Setlec.Expr.mkAppN (.const n us) as) := by
  have main : ∀ (as : List Expr) {F : Expr} {hd : Nat},
      F.getAppFn = .const n us →
      (∀ g, hd ≤ g → whnfCore μ env g d F = .ok F) →
      (∀ n' ty body m, F ≠ .lam n' ty body m) →
      ∀ {g : Nat}, hd + as.length ≤ g →
        whnfCore μ env g d (Setlec.Expr.mkAppN F as)
          = .ok (Setlec.Expr.mkAppN F as) := by
    intro as
    induction as with
    | nil =>
      intro F hd hfn hF _ g hg
      exact hF g (by simpa using hg)
    | cons a as ih =>
      intro F hd hfn hF hnl g hg
      show whnfCore μ env g d
        (Setlec.Expr.mkAppN (.app F a) as) = _
      refine ih (F := .app F a) (hd := hd + 1)
        ((show (Expr.app F a).getAppFn = F.getAppFn from rfl).trans
          hfn) ?_ ?_ ?_
      · intro g' hg'
        cases g' with
        | zero => exact absurd hg' (by omega)
        | succ g'' =>
          rw [show whnfCore μ env (g'' + 1) d (.app F a)
              = Setlec.whnfCoreBody μ (Setlec.pureFns μ env g'')
                env d (.app F a) from Setlec.whnfCore_succ ..]
          have hiota : Setlec.iotaRec μ (Setlec.pureFns μ env g'')
              env d (.app F a) = .ok none :=
            iotaRec_none_of_not_rec
              ((show (Expr.app F a).getAppFn = F.getAppFn
                from rfl).trans hfn) hnr
          have hFrun : (Setlec.pureFns μ env g'').whnfCore d F
              = .ok F := hF g'' (by omega)
          cases F with
          | lam n' ty body m => exact absurd rfl (hnl n' ty body m)
          | const n' us' =>
            unfold Setlec.whnfCoreBody
            simp only [Bind.bind, Except.bind]
            rw [hFrun]
            simp only []
            rw [hiota]
            rfl
          | app p q =>
            unfold Setlec.whnfCoreBody
            simp only [Bind.bind, Except.bind]
            rw [hFrun]
            simp only []
            rw [hiota]
            rfl
          | bvar i => exact nomatch hfn
          | fvar i n' ty => exact nomatch hfn
          | sort u => exact nomatch hfn
          | forallE n' ty body m => exact nomatch hfn
          | letE n' ty v b => exact nomatch hfn
          | lit l => exact nomatch hfn
          | proj sn i e => exact nomatch hfn
      · intro n' ty body m h; exact nomatch h
      · simp only [List.length_cons] at hg ⊢
        omega
  intro as g hg
  exact main as
    (show (Expr.const n us).getAppFn = Expr.const n us from rfl)
    (fun g' hg' => whnfCore_const_run hg')
    (fun _ _ _ _ h => nomatch h) hg

/-- Both instantiated spines of a same-head δ unfold together. -/
theorem unfoldDefinition_spine_both {env : Env} {n : Name}
    {us us' : List Level} {as bs : List Expr} {xa : Expr}
    (hlen : us.length = us'.length)
    (hux : Setlec.unfoldDefinition env
      (Setlec.Expr.mkAppN (.const n us) as) = some xa) :
    ∃ cv value,
      xa = Setlec.Expr.mkAppN
        (Setlec.Expr.instantiateLevelParams cv.levelParams us value)
        as ∧
      Setlec.unfoldDefinition env
        (Setlec.Expr.mkAppN (.const n us') bs)
        = some (Setlec.Expr.mkAppN
          (Setlec.Expr.instantiateLevelParams cv.levelParams us'
            value) bs) ∧
      ((∃ hint, env.find? n = some (.defnInfo cv value hint)) ∨
        env.find? n = some (.thmInfo cv value)) := by
  unfold Setlec.unfoldDefinition at hux
  rw [Setlec.Expr.getAppFn_mkAppN,
    show (Expr.const n us).getAppFn = Expr.const n us from rfl]
    at hux
  simp only [] at hux
  cases hf : env.find? n with
  | none => rw [hf] at hux; exact nomatch hux
  | some ci =>
    rw [hf] at hux
    cases ci with
    | defnInfo cv value hint =>
      simp only [] at hux
      by_cases hl : us.length = cv.levelParams.length
      · rw [if_pos hl] at hux
        refine ⟨cv, value, ?_, ?_, .inl ⟨hint, rfl⟩⟩
        · have h2 := Option.some.inj hux
          rw [Setlec.Expr.getAppArgs_mkAppN,
            show (Expr.const n us).getAppArgs = ([] : List Expr)
              from rfl, List.nil_append] at h2
          exact h2.symm
        · simp only [Setlec.unfoldDefinition,
            Setlec.Expr.getAppFn_mkAppN]
          rw [show (Expr.const n us').getAppFn = Expr.const n us'
            from rfl]
          simp only [hf]
          rw [if_pos (hlen ▸ hl)]
          rw [Setlec.Expr.getAppArgs_mkAppN,
            show (Expr.const n us').getAppArgs = ([] : List Expr)
              from rfl, List.nil_append]
      · rw [if_neg hl] at hux; exact nomatch hux
    | thmInfo cv value =>
      simp only [] at hux
      by_cases hl : us.length = cv.levelParams.length
      · rw [if_pos hl] at hux
        refine ⟨cv, value, ?_, ?_, .inr rfl⟩
        · have h2 := Option.some.inj hux
          rw [Setlec.Expr.getAppArgs_mkAppN,
            show (Expr.const n us).getAppArgs = ([] : List Expr)
              from rfl, List.nil_append] at h2
          exact h2.symm
        · simp only [Setlec.unfoldDefinition,
            Setlec.Expr.getAppFn_mkAppN]
          rw [show (Expr.const n us').getAppFn = Expr.const n us'
            from rfl]
          simp only [hf]
          rw [if_pos (hlen ▸ hl)]
          rw [Setlec.Expr.getAppArgs_mkAppN,
            show (Expr.const n us').getAppArgs = ([] : List Expr)
              from rfl, List.nil_append]
      · rw [if_neg hl] at hux; exact nomatch hux
    | axiomInfo cv => exact nomatch hux
    | indInfo cv caps => exact nomatch hux
    | ctorInfo cv a b => exact nomatch hux
    | recInfo cv a b c => exact nomatch hux
    | projInfo entry => exact nomatch hux

/-- **Routed: the iota case** (recursor-headed spines at eval-linked
levels — the standing full treatment at its seal). -/
def ZipIotaCase (μ : CheckMode) (env : Env) (φ : Name → Nat)
    (Q : Nat → Expr → Expr → Prop) : Prop :=
  ∀ {fc d ga la gb lb mI rP : Nat} {n : Name} {us us' : List Level}
    {cv : Setlec.ConstantVal} {rules : List Setlec.RecRule}
    {as bs : List Expr} {ℓa ℓb : Level},
    env.find? n = some (.recInfo cv mI rP rules) →
    ZipBelow μ env φ Q fc (ga + gb) (la + lb) →
    (∀ φ' : Name → Nat,
      us.map (Level.eval φ') = us'.map (Level.eval φ')) →
    as.length = bs.length →
    (∀ i (h₁ : i < as.length) (h₂ : i < bs.length),
      CertZip μ env fc d as[i] bs[i]) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us) as) →
    SubjInv d (Setlec.Expr.mkAppN (.const n us') bs) →
    PairedLeaves (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Q d (Setlec.Expr.mkAppN (.const n us) as)
      (Setlec.Expr.mkAppN (.const n us') bs) →
    Setlec.whnfLoop (Setlec.pureFns μ env ga) env d la
      (Setlec.Expr.mkAppN (.const n us) as) = .ok (.sort ℓa) →
    Setlec.whnfLoop (Setlec.pureFns μ env gb) env d lb
      (Setlec.Expr.mkAppN (.const n us') bs) = .ok (.sort ℓb) →
    ℓa.eval φ = ℓb.eval φ

/-- **The both-δ core COLLAPSED onto the summit**: the spine facts
zip the pair (head by `constSlack` through `isEquivList` soundness,
args as `.cert` leaves through `defEqList_extract`), and
`ZipWhnfSortAgree` concludes. -/
theorem deltaSpineSortAgree_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hZ : ZipWhnfSortAgree μ env φ Q) :
    DeltaSpineSortAgree μ env φ Q := by
  intro fc d ga la gb lb a' b' ℓa ℓb hIa hIb hPab hQ hs hla hlb
  unfold Setlec.defeqSpine at hs
  split at hs
  · next n us heqa =>
    split at hs
    · next n' us' heqb =>
      split at hs
      · next hcond =>
        obtain ⟨rfl, hlen⟩ := hcond
        split at hs
        · next heql =>
          obtain ⟨hlen', hcerts⟩ := defEqList_extract hs
          have hzip : CertZip μ env fc d a' b' := by
            rw [← Setlec.Expr.mkAppN_getApp a',
              ← Setlec.Expr.mkAppN_getApp b', heqa, heqb]
            exact certZip_mkAppN
              (.constSlack n us us' fun φ' =>
                evalEqList_map (Setlec.Level.isEquivList_sound heql φ'))
              hlen' (getAppArgs_bounded hIa.2.1)
              (getAppArgs_bounded hIb.2.1) hcerts
          exact hZ hzip hIa hIb hPab hQ hla hlb
        · exact nomatch hs
      · exact nomatch hs
    · exact nomatch hs
  · exact nomatch hs

/-- **The branch primitive at the summit**: `EnsureSortAgreeRQ` with
the spine core discharged onto `ZipWhnfSortAgree`.  (The trio legs
still route through the refuted transport species pending the
semantic discharge — this composite tracks the live frontier.) -/
theorem ensureSortAgreeR_of_summit {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hB : BoolCtorsInert env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env) (hInf : InvPreserveInferF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hQC : QPreserveCoreF μ env Q) (hQD : QPreserveDeltaF env Q)
    (hQN : QPreserveNatF μ env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hZ : ZipWhnfSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q :=
  have hD : DeltaSpineSortAgree μ env φ Q :=
    deltaSpineSortAgree_of (φ := φ) (Q := Q) hZ
  ensureSortAgreeR_of_core (Q := Q) hB hTC hTD hTN hIC hID hIN hInf
    hLC hLD hLN hQC hQD hQN hQs hD

/-! ### The public claims collapse onto the summit

The `.cert` leaf absorbs the entire top level: a certified pair IS a
zipped pair, so both public claims are one-line corollaries of the
summit claims.  The landed 25-case shells are thereby superseded as
DISCHARGE routes — but not deleted: their case work is the summit
induction's `.cert`-case template (the mutual knot's design: the
summit's cert case decomposes the cert run exactly as the shells do,
with leaf certs at strictly smaller knot fuel feeding the ih). -/

/-- **(A) collapses onto the summit**: `EnsureSortAgreeRQ` from
`ZipWhnfSortAgree` alone, via the `.cert` leaf. -/
theorem ensureSortAgreeRQ_of_zip {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hZ : ZipWhnfSortAgree μ env φ Q) :
    EnsureSortAgreeRQ μ env φ Q := by
  intro fc d a b f₁ f₂ ℓ₁ ℓ₂ hc hwsa hba hLa hwsb hbb hLb hp hQ
    h₁ h₂
  obtain ⟨ga, la, -, hla⟩ := whnf_peel h₁
  obtain ⟨gb, lb, -, hlb⟩ := whnf_peel h₂
  exact hZ (.cert a b hba hbb hc) (SubjInv.of_pair hwsa hba hLa hp)
    (SubjInv.of_pair_right hwsb hbb hLb hp) hp hQ hla hlb

/-- **(B) collapses onto the summit**: `SortOfAgreeRQ` from
`ZipSortOfAgree` alone, via the `.cert` leaf. -/
theorem sortOfAgreeRQ_of_zip {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hZ : ZipSortOfAgree μ env φ Q) :
    SortOfAgreeRQ μ env φ Q := by
  intro fc d a b f₁ f₂ u v hc hwsa hba hLa hwsb hbb hLb hp hQ h₁ h₂
  exact hZ (.cert a b hba hbb hc) (SubjInv.of_pair hwsa hba hLa hp)
    (SubjInv.of_pair_right hwsb hbb hLb hp) hp hQ
    (SortOfLE_of_run h₁) (SortOfLE_of_run h₂)

/-- The slot-free (B) shell: `SortOfAgreeR` as the `Q := True`
instance. -/
theorem sortOfAgreeR_of {φ : Name → Nat}
    (hm : KnotFuelMono μ env)
    (hTC : TypeTransportCoreF μ env) (hTD : TypeTransportDeltaF μ env)
    (hTN : TypeTransportNatF μ env)
    (hIC : InvPreserveCoreF μ env) (hID : InvPreserveDeltaF env)
    (hIN : InvPreserveNatF μ env)
    (hLC : PairedPreserveCoreF μ env) (hLD : PairedPreserveDeltaF env)
    (hLN : PairedPreserveNatF μ env)
    (hP : ProbeTySortVacuity μ env fun _ _ _ => True)
    (hR : RescueTySortVacuity μ env fun _ _ _ => True)
    (hLam : LamTySortVacuity μ env)
    (hZ : NatZeroTySortAgree μ env φ)
    (hSL : NatSuccLTySortAgree μ env φ)
    (hSR : NatSuccRTySortAgree μ env φ)
    (hStL : StrLTySortAgree μ env φ) (hStR : StrRTySortAgree μ env φ)
    (hF : FvarTySortAgree μ env φ) (hK : ConstTySortAgree μ env φ)
    (hSp : SpineTySortAgree μ env φ fun _ _ _ => True)
    (hPi : PiCongTySortAgree μ env φ fun _ _ _ => True)
    (hAp : AppCongTySortAgree μ env φ fun _ _ _ => True)
    (hPj : ProjCongTySortAgree μ env φ fun _ _ _ => True) :
    SortOfAgreeR μ env φ := by
  intro fc d a b f₁ f₂ u v hc hwsa hba hLa hwsb hbb hLb hp h₁ h₂
  exact sortOfAgreeRQ_of (Q := fun _ _ _ => True) hm hTC hTD hTN
    hIC hID hIN hLC hLD hLN
    (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun h => h)
    hP hR hLam hZ hSL hSR hStL hStR hF hK hSp hPi hAp hPj
    hc hwsa hba hLa hwsb hbb hLb hp trivial h₁ h₂

/-- **The const head DISCHARGED to iota**: non-recursor heads are
inert (nat steps die on `NatStepNoSort`, δ unfolds together into
zipped instantiations, stuck outputs clash with the sorts); recursor
heads route to `ZipIotaCase`. -/
theorem zipConstHeadCase_of {φ : Name → Nat}
    {Q : Nat → Expr → Expr → Prop}
    (hm : KnotFuelMono μ env) (hB : BoolCtorsInert env)
    (hID : InvPreserveDeltaF env) (hLD : PairedPreserveDeltaF env)
    (hQD : QPreserveDeltaF env Q)
    (hQs : ∀ {d : Nat} {a b : Expr}, Q d a b → Q d b a)
    (hIota : ZipIotaCase μ env φ Q) :
    ZipConstHeadCase μ env φ Q := by
  have hN : NatStepNoSort μ env := natStepNoSort_of hB
  intro fc d ga la gb lb n us us' as bs ℓa ℓb below hev hlen hargs
    hIs hIt hp hQ ha hb
  by_cases hrec : ∃ cv mI rP rules,
      env.find? n = some (.recInfo cv mI rP rules)
  · obtain ⟨cv, mI, rP, rules, hf⟩ := hrec
    exact hIota hf below hev hlen hargs hIs hIt hp hQ ha hb
  · have hnr : ∀ cv mI rP rules,
        env.find? n ≠ some (.recInfo cv mI rP rules) :=
      fun cv mI rP rules hf => hrec ⟨cv, mI, rP, rules, hf⟩
    have hnr' : ∀ cv mI rP rules,
        env.find? n ≠ some (.recInfo cv mI rP rules) := hnr
    have hlen' : us.length = us'.length := by
      have := congrArg List.length (hev fun _ => 0)
      simpa using this
    have hstuckA := whnfCore_mkAppN_const_inert (μ := μ) (d := d)
      (us := us) hnr as (Nat.le_refl _)
    have hstuckB := whnfCore_mkAppN_const_inert (μ := μ) (d := d)
      (us := us') hnr bs (Nat.le_refl _)
    cases la with
    | zero => exact nomatch ha
    | succ la' =>
    cases lb with
    | zero => exact nomatch hb
    | succ lb' =>
    have haD := ha
    rw [whnfLoop_succ] at haD
    obtain ⟨e₁, hwca, htriA⟩ := whnfStep_decompose haD
    obtain rfl : e₁ = Setlec.Expr.mkAppN (.const n us) as :=
      (KnotFuelDet_of_mono hm).2.2.1
        (hwca : whnfCore μ env ga d _ = .ok e₁) hstuckA
    have hbD := hb
    rw [whnfLoop_succ] at hbD
    obtain ⟨e₂, hwcb, htriB⟩ := whnfStep_decompose hbD
    obtain rfl : e₂ = Setlec.Expr.mkAppN (.const n us') bs :=
      (KnotFuelDet_of_mono hm).2.2.1
        (hwcb : whnfCore μ env gb d _ = .ok e₂) hstuckB
    rcases htriA with ⟨x, hrx, -⟩ | ⟨hrga, xa, hux, hkx⟩ |
      ⟨-, -, hstopA⟩
    · exact (hN hstuckA hrx ha).elim
    · obtain ⟨cv, value, rfl, huy', hstore⟩ :=
        unfoldDefinition_spine_both (us' := us') (bs := bs)
          hlen' hux
      rcases htriB with ⟨y, hry, -⟩ | ⟨hrgb, xb, huy, hky⟩ |
        ⟨-, hudb, -⟩
      · exact (hN hstuckB hry hb).elim
      · rw [huy'] at huy
        obtain rfl := (Option.some.inj huy).symm
        exact below (Or.inr ⟨rfl, Or.inr ⟨rfl, by omega⟩⟩)
          (certZip_mkAppN_zips (certZip_instantiate hev value)
            hlen hargs)
          (hID hux hIs) (hID huy' hIt)
          ((hLD huy' ((hLD hux hp).symm)).symm)
          (hQs (hQD huy' (hQs (hQD hux hQ)))) hkx hky
      · rw [huy'] at hudb; exact nomatch hudb
    · cases as with
      | nil =>
        simp only [Setlec.Expr.mkAppN] at hstopA
        exact nomatch hstopA
      | cons a as' =>
        obtain ⟨p, q, hpq⟩ := mkAppN_cons_app
          (F := Expr.const n us) (a := a) (as := as')
        rw [hpq] at hstopA
        exact nomatch hstopA

end Discharge

end Setlec.SetR.Interp2
