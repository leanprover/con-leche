module

public import ConLeche.Model.Inductives.MutualStageRec
public section

/-!
# The mutual rule's term-level ι law (task #278, M2.5d′)

`MutualRecParts.RuleFires` — the premise the recursor stage's rule law
(`mutualRecRuleLaw`) hands on — proved from the landed laws:

* the spine SPLIT.  The recursor's flat spine fit (its arguments
  against the stored type's binder data) is split along
  `mutualRecDataAV_doms` into the block frame
  `(p⃗, M⃗, S⃗, ı⃗, t)` that `mutualRecLawCore` and `mutualRecIotaCore`
  are stated at — the `k`-motive twin of `fixRecLawCore`'s
  `kframe_split`/`block_split`, which here is four
  `spineFit_append_inv`s because the binder data's blocks are already
  spelled out;
* the `ℓ = 0` regime, by hand: every binder of both λ-towers carries
  the bit `0`, so both sides read as the point;
* the `ℓ ≠ 0` regime, through `mutualRecLawCore`, whose `hfitRa` is
  rebuilt here from the split (the rule's λ-tower binds the RECURSOR's
  parameters, so the constructor's fields must be refitted there — the
  `paramsBlind` price) and whose `hiota` is `mutualRecIotaCore`'s
  conclusion.

Two premises are left for the caller, both at the SPLIT frame, where
they are the fixpoint route's own two steps:

* `hfitB` — the constructor's fields, refitted at the recursor's
  parameter values (`fixRecLawCore`'s graph-regime inversion:
  `sumSet_elim` + `towerSet_elim_teleOfFields` at the auxiliary
  family's restricted chain);
* `hiota` — `mutualRecIotaCore`'s conclusion, whose own spine premises
  (`hspAux`, `hih`, the auxiliary `FixPre`) are the member leaf's
  typing at the rule's frame.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecRule)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The rule's binder domains -/

/-- **The rule's binder data's domains, split** (`mutualRecDataAV_doms`
at the rule's tower): the recursor's parameter, motive and minor
blocks, and then the constructor's field domains lifted under them. -/
theorem mutualRuleDataAV_doms {m : EnvModel V env} {ψ : Name → Nat} {elimL : Level}
    {nP n k b : Nat} {Ls : List AnnotTerm} {nIdxs : List Nat}
    {pps : List (Nat × Nat × AnnotTerm)} {ipss : List (List (Nat × Nat × AnnotTerm))}
    {cds : List CtorDatumR} {mems : Nat → Nat} {tgts : Nat → Nat → Nat}
    {ds : List (Nat × Nat × AnnotTerm)}
    (hb : pwBit ψ (Level.zeronessOf elimL) = b) (hLs : Ls.length = k) (hn : cds.length = n) :
    (mutualRuleDataAV m ψ Ls nP nIdxs elimL pps ipss cds mems tgts ds).map (·.2)
      = ((pps.map (·.2.2) ++
          (motivesDataGo (fun t => Ls.getD t default) (fun t => nIdxs.getD t 0)
            (fun t => ipss.getD t []) ψ nP elimL b k 0).map (·.2.2)) ++
          (fixMinorsDataM mems tgts m ψ nP b cds k).map (·.2.2)) ++
        (liftDoms (k + n) 0 (ds.drop nP)).map (·.2.2) := by
  unfold mutualRuleDataAV
  rw [hb, hLs, hn]
  simp only [List.map_map, List.map_append, Function.comp_def, rebit_map_dom]

/-! ## The law -/

set_option maxHeartbeats 6400000 in
/-- **The mutual rule fires**: `MutualRecParts.RuleFires` from the
landed laws.  The spine is split into the block frame, the `ℓ = 0`
regime is the point on both sides, and the `ℓ ≠ 0` regime is
`mutualRecLawCore` at the split. -/
theorem ruleFires_of (p : MutualRecParts) {env₀ : Env} {m₀ : EnvModel V env₀}
    (hyp : p.LeafHyp V m₀) {t J mI rP : Nat} {cdF : (Name → Nat) → CtorDatumR}
    (ht : t < p.k)
    (hmI : mI = p.nP + p.k + p.n + p.nIdxOf t) (hrP : rP = p.nP + p.k + p.n)
    (hcdJ : ∀ ψ : Name → Nat, (p.cds ψ)[J]? = some (cdF ψ))
    (hRDlen : ∀ ψ : Name → Nat, (p.rds m₀ t ψ).length = p.nP + p.k + p.n + p.nIdxOf t + 1)
    (hRDbits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ p.rds m₀ t ψ →
      (p.elimL.eval ψ = 0 ↔ d.2.1 = 0))
    (hRuleOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), WellDenotedV V ρ (p.ruleAV m₀ J (cdF ψ) ψ))
    (hmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (p.leaf m₀ t ψ) ∈ˢ interp V ρ (mkPisAV (p.rds m₀ t ψ) (p.conc t)))
    -- the constructor's fields, refitted at the RECURSOR's parameter
    -- values (`fixRecLawCore`'s graph-regime inversion)
    (hfitB : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as₁ Ms ms is as₂ : List V) (tv : V)
      (ys : List AnnotTerm),
      p.ℓ ψ ≠ 0 → as₁.length = p.nP → Ms.length = p.k → ms.length = p.n →
      is.length = p.nIdxOf t → as₂.length = (cdF ψ).2.1 →
      SpineFit ρ ((p.rds m₀ t ψ).map (·.2.2)) (as₁ ++ Ms ++ ms ++ is ++ [tv]) →
      tv = interp V ρ (AnnotTerm.mkAppN (sumMkAV (p.wB ψ) J (cdF ψ).2.2.1
        (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψ))) ys) →
      SpineFit ρ ((cdF ψ).2.2.1.map (·.2.2)) (ys.map (interp V ρ)) →
      SpineFit (consList as₁ ρ) (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) as₂)
    -- the ι equation at the split frame (`mutualRecIotaCore`)
    (hiota : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as₁ Ms ms is as₂ : List V) (tv : V),
      p.ℓ ψ ≠ 0 → as₁.length = p.nP → Ms.length = p.k → ms.length = p.n →
      is.length = p.nIdxOf t → as₂.length = (cdF ψ).2.1 →
      SpineFit ρ ((p.rds m₀ t ψ).map (·.2.2)) (as₁ ++ Ms ++ ms ++ is ++ [tv]) →
      SpineFit (consList as₁ ρ) (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) as₂ →
      (as₁ ++ Ms ++ ms ++ is ++ [tv]).foldl SetTheory.app (interp V ρ (p.leaf m₀ t ψ))
        = interp V (consList as₂ (consList ms (consList Ms (consList as₁ ρ))))
            (mutualRuleCoreAV (p.bb ψ) (fun q => p.leaf m₀ q ψ) (p.tgts J) p.nP p.k p.n
              (cdF ψ).2.1 J (cdF ψ).2.2.2.2.1 (cdF ψ).2.2.2.2.2.2 (cdF ψ).2.2.2.2.2.1)) :
    p.RuleFires V m₀ t J mI rP cdF := by
  subst hmI
  subst hrP
  intro ψ ρ xs ys hxl hyl hspR hspC _hpin
  have hh := hyp t ht ψ
  have hLs : (p.Ls ψ).length = p.k := by simp [MutualRecParts.Ls]
  obtain ⟨hlenDs, -, -, -, -, -, -, -, -⟩ := hh.hcd J (cdF ψ) (hcdJ ψ)
  -- the rule's tower, and its bits
  have hldsBits : ∀ d ∈ mutualRuleDataAV m₀ ψ (p.Ls ψ) p.nP p.nIdxs p.elimL (p.ppsOf 0 ψ)
      (p.ipss ψ) (p.cds ψ) p.mems p.tgts (cdF ψ).2.2.1, d.1 = p.bb ψ :=
    fun d hd => by rw [mem_mutualRuleDataAV hd, hh.hb]
  have hldsLen : (mutualRuleDataAV m₀ ψ (p.Ls ψ) p.nP p.nIdxs p.elimL (p.ppsOf 0 ψ)
      (p.ipss ψ) (p.cds ψ) p.mems p.tgts (cdF ψ).2.2.1).length
      = p.nP + p.k + p.n + (cdF ψ).2.1 := by
    rw [mutualRuleDataAV_length hh.hlenP hlenDs, hLs, hh.hn]
  -- the split of the recursor's spine
  have hspR' := hspR
  rw [show p.rds m₀ t ψ = mutualRecDataAV m₀ ψ (p.Ls ψ) p.nP p.nIdxs p.elimL (p.ppsOf 0 ψ)
      (p.ipss ψ) (p.cds ψ) p.mems p.tgts t from rfl,
    mutualRecDataAV_doms hh.hb hLs hh.hn] at hspR'
  generalize hvs : (xs ++ [AnnotTerm.mkAppN (sumMkAV (p.wB ψ) J (cdF ψ).2.2.1
    (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψ))) ys]).map (interp V ρ) = vs
    at hspR'
  obtain ⟨as₃, ts, rfl, hsp₃, hspT⟩ := spineFit_append_inv hspR'
  obtain ⟨tv, rfl, -⟩ := spineFit_singleton hspT
  obtain ⟨as₂', is, rfl, hsp₂, hspI⟩ := spineFit_append_inv hsp₃
  obtain ⟨as₁', Ss, rfl, hsp₁, hspS⟩ := spineFit_append_inv hsp₂
  obtain ⟨ps, Ms, rfl, hspP, hspM⟩ := spineFit_append_inv hsp₁
  -- the blocks' lengths
  have hlenPs : ps.length = p.nP := by rw [hspP.length_eq, List.length_map, hh.hlenP]
  have hlenMs : Ms.length = p.k := by
    rw [hspM.length_eq, List.length_map, motivesDataGo_length]
  have hlenSs : Ss.length = p.n := by
    rw [hspS.length_eq, List.length_map, fixMinorsDataM_length, hh.hn]
  have hlenIs : is.length = p.nIdxOf t := by
    have hlt := hspI.length_eq
    rw [List.length_map, liftDoms_length] at hlt
    obtain ⟨Ids, hIds, hlenIds, hipd⟩ := hh.hIdss t ht
    rw [hlt, ← List.length_map (f := fun d : Nat × Nat × AnnotTerm => d.2.2), hipd, hlenIds,
      p.nIdxs_getD ht]
  -- the flat spine, as the block frame
  have hflat : ((ps ++ Ms) ++ Ss) ++ is ++ [tv] = ps ++ Ms ++ Ss ++ is ++ [tv] := by
    simp only [List.append_assoc]
  have hspRF : SpineFit ρ ((p.rds m₀ t ψ).map (·.2.2)) (ps ++ Ms ++ Ss ++ is ++ [tv]) := by
    have h := hspR
    rw [hvs] at h
    simpa only [List.append_assoc] using h
  -- the values of `xs` and of the major
  have hxsv : xs.map (interp V ρ) = ps ++ Ms ++ Ss ++ is ∧
      tv = interp V ρ (AnnotTerm.mkAppN (sumMkAV (p.wB ψ) J (cdF ψ).2.2.1
        (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψ))) ys) := by
    rw [List.map_append, List.map_cons, List.map_nil] at hvs
    have h := hvs
    rw [← hflat] at h
    obtain ⟨h1, h2⟩ := List.append_inj h (by
      rw [List.length_map, hxl]
      simp only [List.length_append, hlenPs, hlenMs, hlenSs, hlenIs])
    exact ⟨h1, by simpa using h2.symm⟩
  obtain ⟨hxv, htv⟩ := hxsv
  -- the rule's own tower and its length
  have hlenAs₂ : ((ys.drop p.nP).map (interp V ρ)).length = (cdF ψ).2.1 := by
    rw [List.length_map, List.length_drop, hyl]
    omega
  -- the two regimes
  by_cases hℓ0 : p.ℓ ψ = 0
  · -- the point on both sides
    have hb0 : p.bb ψ = 0 := hh.hbz.mp hℓ0
    have hRpt : interp V ρ (p.leaf m₀ t ψ) = pt := by
      refine eq_pt_of_mem_univZero ?_ (hmem ψ ρ)
      cases hrds : p.rds m₀ t ψ with
      | nil =>
        have := hRDlen ψ
        rw [hrds] at this
        simp at this
      | cons d rest =>
        show interp V ρ (mkPisAV (d :: rest) (p.conc t)) ∈ˢ _
        show piR d.2.1 _ _ ∈ˢ _
        rw [(hRDbits ψ d (by rw [hrds]; exact List.mem_cons_self)).mp (by
          rw [← hh.hℓ] at hℓ0; exact hℓ0)]
        exact piR_zero_mem_univZero
    have hRaPt : interp V ρ (p.ruleAV m₀ J (cdF ψ) ψ) = pt := by
      cases hlds : mutualRuleDataAV m₀ ψ (p.Ls ψ) p.nP p.nIdxs p.elimL (p.ppsOf 0 ψ)
          (p.ipss ψ) (p.cds ψ) p.mems p.tgts (cdF ψ).2.2.1 with
      | nil =>
        rw [hlds] at hldsLen
        simp at hldsLen
        omega
      | cons d rest =>
        have hd : d.1 = 0 := by
          rw [← hb0]
          exact hldsBits d (by rw [hlds]; exact List.mem_cons_self)
        show interp V ρ (mkLamsAV _ _) = _
        rw [hlds, mkLamsAV, interp_lam, hd, lamR_zero]
    refine ⟨?_, fun hxs_ok hys_ok => ?_⟩
    · rw [interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), hRpt,
        foldl_app_pt_sum, interp_mkAppN,
        ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), hRaPt, foldl_app_pt_sum]
    · refine mkAppN_wellDenotedV_of_pt (hRuleOk ψ ρ) hRaPt ?_
      intro a ha
      rcases List.mem_append.mp ha with h | h
      · exact hxs_ok a (List.mem_of_mem_take h)
      · exact hys_ok a (List.mem_of_mem_drop h)
  · -- the graph regime
    have hfitB' : SpineFit (consList ps ρ) (((cdF ψ).2.2.1.drop p.nP).map (·.2.2))
        ((ys.drop p.nP).map (interp V ρ)) :=
      hfitB ψ ρ ps Ms Ss is ((ys.drop p.nP).map (interp V ρ)) tv ys hℓ0 hlenPs hlenMs hlenSs
        hlenIs hlenAs₂ hspRF htv hspC
    -- the rule's tower fits the block and the fields
    have hshift : shiftE (p.k + p.n) 0 (consList ((ps ++ Ms) ++ Ss) ρ) = consList ps ρ := by
      rw [show (ps ++ Ms) ++ Ss = ps ++ (Ms ++ Ss) from by simp only [List.append_assoc],
        consList_append,
        show p.k + p.n = (Ms ++ Ss).length from by
          simp only [List.length_append, hlenMs, hlenSs]]
      exact shiftE_consList _ _
    have hxtake : (xs.take (p.nP + p.k + p.n)).map (interp V ρ) = (ps ++ Ms) ++ Ss := by
      rw [List.map_take, hxv,
        show p.nP + p.k + p.n = ((ps ++ Ms) ++ Ss).length from by
          simp only [List.length_append, hlenPs, hlenMs, hlenSs],
        show ps ++ Ms ++ Ss ++ is = ((ps ++ Ms) ++ Ss) ++ is from by
          simp only [List.append_assoc],
        List.take_left]
    have hfitRa : SpineFit ρ ((mutualRuleDataAV m₀ ψ (p.Ls ψ) p.nP p.nIdxs p.elimL (p.ppsOf 0 ψ)
        (p.ipss ψ) (p.cds ψ) p.mems p.tgts (cdF ψ).2.2.1).map (·.2))
        ((xs.take (p.nP + p.k + p.n) ++ ys.drop p.nP).map (interp V ρ)) := by
      rw [mutualRuleDataAV_doms hh.hb hLs hh.hn, List.map_append, hxtake]
      refine SpineFit.append hsp₂ ?_
      rw [spineFit_liftDoms, hshift]
      exact hfitB'
    -- the law
    have hcore := mutualRecLawCore (V := V) (ℓ := p.ℓ ψ) (b := p.bb ψ) (k := p.k) (n := p.n)
      (nF := (cdF ψ).2.1) (j := J) (mm := t) (nP := p.nP)
      (Rof := fun q => p.leaf m₀ q ψ) (tgtsJ := p.tgts J)
      (recIdxJ := (cdF ψ).2.2.2.2.1) (tlsJ := (cdF ψ).2.2.2.2.2.2)
      (EissJ := (cdF ψ).2.2.2.2.2.1)
      (lds := mutualRuleDataAV m₀ ψ (p.Ls ψ) p.nP p.nIdxs p.elimL (p.ppsOf 0 ψ) (p.ipss ψ)
        (p.cds ψ) p.mems p.tgts (cdF ψ).2.2.1)
      (Ra := p.ruleAV m₀ J (cdF ψ) ψ) (ρ := ρ) (as₁ := ps) (Ms := Ms) (ms := Ss) (is := is)
      (as₂ := (ys.drop p.nP).map (interp V ρ)) (t := tv) (xs := xs) (ys := ys)
      (ctor := AnnotTerm.mkAppN (sumMkAV (p.wB ψ) J (cdF ψ).2.2.1
        (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψ))) ys)
      hh.hbz (by omega) rfl hldsBits hldsLen hlenPs hlenMs hlenSs hxv rfl htv.symm
      (hRuleOk ψ) hfitRa (fun h => absurd h hℓ0)
      (fun _ => hiota ψ ρ ps Ms Ss is ((ys.drop p.nP).map (interp V ρ)) tv hℓ0 hlenPs hlenMs
        hlenSs hlenIs hlenAs₂ hspRF hfitB')
    exact hcore

end ConLeche.Model
