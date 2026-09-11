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

Both steps at the split frame are done here, and they are the fixpoint
route's own two:

* the constructor's fields, **refitted at the recursor's parameter
  values** — the constructor's own parameter spine is never identified
  with the recursor's; instead the major lies in the major domain's
  reading, which is the auxiliary fibre at `⟨inj t ı⃗⟩`, and the
  auxiliary premise's K-frame (`FixPre.hK` at the auxiliary spine)
  presents that fibre as the restricted tagged union at the
  RECURSOR's parameters (`RecHypCore.hfam`).  `sumSet_elim` +
  `towerSet_elim_teleOfFields` at `rChains 1 1 FssR Ess'`, with
  `inj_inj` and `mkTower` injectivity identifying the constructor's tag
  and fields (`fixRecLawCore`'s graph-regime inversion; the squash
  regime is vacuous — `wB ψ = 0 → ℓ ψ = 0`);
* `mutualRecIotaCore`'s conclusion, whose spine premises are the member
  leaf's typing at the rule's frame: `hspAux` is
  `mutualAuxSpine_of` and `hih` is `mutualIhSpine_of`
  (`Model/Inductives/MutualRecTyping.lean`), `hpre` the auxiliary
  `FixPre` (`auxFixPre_of`).

`(p.FssR ψ).length = p.n` is not a hypothesis: it is the auxiliary
premise's own length clause (`FixPre.hlen` against
`fixRecDataAVL_length`).
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
    -- every member's recursor leaf is closed (`MutualRecParts.leaf_below`)
    (hAcl : ∀ (q : Nat), q < p.k → ∀ ψ : Name → Nat, Term.bvarsBelow 0 (p.leaf m₀ q ψ).erase)
    -- the mutual regime: a `Prop`-valued block eliminates into `Prop` only
    (hregime : ∀ ψ : Name → Nat, p.wB ψ = 0 → p.ℓ ψ = 0)
    -- the AUXILIARY recursor's premise (`auxFixPre_of`)
    (hpre : ∀ ψ : Name → Nat, FixPre V (p.ℓ ψ) (p.wB ψ) (p.W ψ) p.nP (p.FssR ψ) (p.Ess' ψ)
      (p.Fss₀ ψ) (auxIds (p.W ψ) (p.Idss ψ)) p.rss (p.tlss ψ) (p.Eiss' ψ)
      (auxRecDataAV m₀ ψ (p.W ψ) (p.wB ψ) p.nP p.elimL (p.ppsOf 0 ψ) (p.Idss ψ) p.rss
        (p.tlss ψ) (p.Eiss' ψ) (p.Fss₀ ψ) (p.Ess' ψ) p.mems p.tgts (p.cds ψ)) (p.s ψ)) :
    p.RuleFires V m₀ t J mI rP cdF := by
  subst hmI
  subst hrP
  intro ψ ρ xs ys hxl hyl hspR hspC _hpin
  have hh := hyp t ht ψ
  have hLs : (p.Ls ψ).length = p.k := by simp [MutualRecParts.Ls]
  obtain ⟨hlenDs, htakeP, -, -, hFssJ, hrecIdxJ, htlsJ, hEissOJ, hEissJ⟩ :=
    hh.hcd J (cdF ψ) (hcdJ ψ)
  have hJn : J < p.n := by
    have h := (List.getElem?_eq_some_iff.mp (hcdJ ψ)).1
    rwa [hh.hn] at h
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
  obtain ⟨tv, rfl, htmaj⟩ := spineFit_singleton hspT
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
    have hw : p.wB ψ ≠ 0 := fun h0 => hℓ0 (hregime ψ h0)
    -- the recursor's parameter frame, and the block's data there
    have hsatP : Sat V (((p.ppsOf 0 ψ).map (·.2.2)).reverse) (consList ps ρ) := by
      have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspP
      rwa [List.append_nil] at h
    have hF := hh.hframes _ hsatP
    -- the constructor's spine, split at its own parameters
    have hspC' := hspC
    rw [show (cdF ψ).2.2.1.map (·.2.2) = ((cdF ψ).2.2.1.take p.nP).map (·.2.2)
        ++ ((cdF ψ).2.2.1.drop p.nP).map (·.2.2) from by
      rw [← List.map_append, List.take_append_drop]] at hspC'
    obtain ⟨qs, fs, hysv, hspq, hspf⟩ := spineFit_append_inv hspC'
    have hlenqs : qs.length = p.nP := by
      rw [hspq.length_eq, htakeP, List.length_map, hh.hlenP]
    have hfseq : fs = (ys.drop p.nP).map (interp V ρ) := by
      rw [List.map_drop, hysv, List.drop_left' hlenqs]
    subst hfseq
    -- the CONSTRUCTOR's parameter frame (never identified with the recursor's)
    have hsatC : Sat V (((p.ppsOf 0 ψ).map (·.2.2)).reverse) (consList qs ρ) := by
      have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hspq
      rw [List.append_nil, htakeP] at h
      exact h
    have hFC := hh.hframes _ hsatC
    -- the constructor's value: the injection of its field tower
    have hokU : SumFieldsOkB (p.wB ψ) (consList qs ρ) (uChains (p.FssR ψ)) :=
      SumFieldsOkB_uChains hFC.fieldsB
    have hjU : (uChains (p.FssR ψ))[J]?
        = some (((cdF ψ).2.2.1.drop p.nP).map (·.2.2) ++ [idxEqAV []]) := by
      rw [uChains_getElem?, hFssJ]; rfl
    have hmajV : tv = inj J (mkTower ((ys.drop p.nP).map (interp V ρ) ++ [pt])) := by
      rw [htv, interp_mkAppN, ← List.foldl_map (f := interp V ρ) (g := SetTheory.app), hysv,
        show sumMkAV (p.wB ψ) J (cdF ψ).2.2.1 (((cdF ψ).2.2.1.drop p.nP).map (·.2.2))
            (uChains (p.FssR ψ))
          = sumMkAV (p.wB ψ) J ((cdF ψ).2.2.1.take p.nP ++ (cdF ψ).2.2.1.drop p.nP)
              (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) (uChains (p.FssR ψ)) from by
          rw [List.take_append_drop]]
      exact sumMkAV_fold hw hspq hspf hokU hjU
    -- member `t`'s index telescope, and the index spine at the parameters
    obtain ⟨IdsM, hIdsMM, hlenIdsMM, hipdMM⟩ := hh.hIdss t ht
    have hfr1 : consList (ps ++ Ms) ρ = consList Ms (consList ps ρ) := consList_append _ _ _
    have hfr2 : consList (ps ++ Ms ++ Ss) ρ = consList Ss (consList Ms (consList ps ρ)) := by
      rw [consList_append, hfr1]
    have hfr4 : consList (ps ++ Ms ++ Ss ++ is ++ [tv]) ρ
        = cons tv (consList is (consList Ss (consList Ms (consList ps ρ)))) := by
      rw [consList_append, consList_append, hfr2, consList_cons, consList_nil]
    have hshY : shiftE (p.k + p.n) 0 (consList Ss (consList Ms (consList ps ρ)))
        = consList ps ρ := by
      rw [← consList_append, show p.k + p.n = (Ms ++ Ss).length from by
        simp [hlenMs, hlenSs]]
      exact shiftE_consList _ _
    have hidxFit : SpineFit (consList ps ρ) IdsM is := by
      have h := hspI
      rw [hfr2, spineFit_liftDoms_iff, hshY, hipdMM] at h
      exact h
    -- the AUXILIARY recursor's spine (`mutualAuxSpine_of`)
    have hspAux := mutualAuxSpine_of hh hlenMs hlenSs
      (by rw [p.nIdxs_getD ht]; exact hlenIs) hspP hspM hspS hspI htmaj
    -- the number of constructor chains, off the auxiliary premise's length clause
    have hlenFss : (p.FssR ψ).length = p.n := by
      have h1 := (hpre ψ).hlen
      unfold auxRecDataAV at h1
      rw [fixRecDataAVL_length hh.hlenP
          (show (tagIps (p.W ψ) (p.Idss ψ)).length = 1 from rfl), auxCtorData_length, hh.hn,
        show (auxIds (p.W ψ) (p.Idss ψ)).length = 1 from rfl] at h1
      omega
    -- the auxiliary recursor's K-frame at this spine
    obtain ⟨hK, htK⟩ := (hpre ψ).hK ρ
      (ps ++ [interp V (cons tv (consList is (consList Ss (consList Ms (consList ps ρ)))))
          (motDispAV (p.ℓ ψ) (p.W ψ) (p.wB ψ) (p.k + p.n + p.nIdxs.getD t 0 + 1)
            (p.n + p.nIdxs.getD t 0 + 1) p.k (p.Idss ψ) p.rss (p.tlss ψ) (p.Eiss' ψ)
            (p.Fss₀ ψ) (p.Ess' ψ))] ++ Ss ++ [inj t (mkTower (is ++ [pt]))]) tv hspAux
    have hKfr : consList (ps ++ [interp V
          (cons tv (consList is (consList Ss (consList Ms (consList ps ρ)))))
          (motDispAV (p.ℓ ψ) (p.W ψ) (p.wB ψ) (p.k + p.n + p.nIdxs.getD t 0 + 1)
            (p.n + p.nIdxs.getD t 0 + 1) p.k (p.Idss ψ) p.rss (p.tlss ψ) (p.Eiss' ψ)
            (p.Fss₀ ψ) (p.Ess' ψ))] ++ Ss ++ [inj t (mkTower (is ++ [pt]))]) ρ
        = consList [inj t (mkTower (is ++ [pt]))] (consList Ss (cons (interp V
            (cons tv (consList is (consList Ss (consList Ms (consList ps ρ)))))
            (motDispAV (p.ℓ ψ) (p.W ψ) (p.wB ψ) (p.k + p.n + p.nIdxs.getD t 0 + 1)
              (p.n + p.nIdxs.getD t 0 + 1) p.k (p.Idss ψ) p.rss (p.tlss ψ) (p.Eiss' ψ)
              (p.Fss₀ ψ) (p.Ess' ψ))) (consList ps ρ))) :=
      consList_kframe ps _ Ss [inj t (mkTower (is ++ [pt]))] ρ
    have hlenmsF : Ss.length = (p.FssR ψ).length := by rw [hlenSs, hlenFss]
    have hsh : shiftE ((auxIds (p.W ψ) (p.Idss ψ)).length + (p.FssR ψ).length + 1) 0
        (consList [inj t (mkTower (is ++ [pt]))] (consList Ss (cons (interp V
            (cons tv (consList is (consList Ss (consList Ms (consList ps ρ)))))
            (motDispAV (p.ℓ ψ) (p.W ψ) (p.wB ψ) (p.k + p.n + p.nIdxs.getD t 0 + 1)
              (p.n + p.nIdxs.getD t 0 + 1) p.k (p.Idss ψ) p.rss (p.tlss ψ) (p.Eiss' ψ)
              (p.Fss₀ ψ) (p.Ess' ψ))) (consList ps ρ)))) = consList ps ρ :=
      kframe_frP (his := show [inj t (mkTower (is ++ [pt]))].length
        = (auxIds (p.W ψ) (p.Idss ψ)).length from rfl) hlenmsF
    -- the major in the restricted tagged union at the RECURSOR's parameters
    have ht' : tv ∈ˢ sumSet (p.wB ψ) (sumFibre (p.wB ψ)
        (consList (ps ++ [interp V
            (cons tv (consList is (consList Ss (consList Ms (consList ps ρ)))))
            (motDispAV (p.ℓ ψ) (p.W ψ) (p.wB ψ) (p.k + p.n + p.nIdxs.getD t 0 + 1)
              (p.n + p.nIdxs.getD t 0 + 1) p.k (p.Idss ψ) p.rss (p.tlss ψ) (p.Eiss' ψ)
              (p.Fss₀ ψ) (p.Ess' ψ))] ++ Ss ++ [inj t (mkTower (is ++ [pt]))]) ρ)
        (rChains ((auxIds (p.W ψ) (p.Idss ψ)).length + (p.FssR ψ).length + 1)
          (auxIds (p.W ψ) (p.Idss ψ)).length (p.FssR ψ) (p.Ess' ψ))) := by
      rw [← hK.hyp.hfam]
      exact htK
    obtain ⟨Es', hEsj⟩ : ∃ Es', (p.Ess' ψ)[J]? = some Es' :=
      ⟨_, List.getElem?_eq_getElem (by rw [hK.hreal.2.1, hlenFss]; exact hJn)⟩
    have hRj : (rChains ((auxIds (p.W ψ) (p.Idss ψ)).length + (p.FssR ψ).length + 1)
          (auxIds (p.W ψ) (p.Idss ψ)).length (p.FssR ψ) (p.Ess' ψ))[J]?
        = some (rChain ((auxIds (p.W ψ) (p.Idss ψ)).length + (p.FssR ψ).length + 1)
            (auxIds (p.W ψ) (p.Idss ψ)).length (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) Es') := by
      rw [rChains_getElem?, hFssJ, hEsj]
    have hlenFs : (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)).length = (cdF ψ).2.1 := by
      rw [List.length_map, List.length_drop, hlenDs]; omega
    -- **`hfitB`**: the fields, refitted at the RECURSOR's parameters
    have hfitB' : SpineFit (consList ps ρ) (((cdF ψ).2.2.1.drop p.nP).map (·.2.2))
        ((ys.drop p.nP).map (interp V ρ)) := by
      obtain ⟨i, a, ha, hta⟩ := sumSet_elim hw ht'
      rw [hmajV] at hta
      obtain ⟨rfl, rfl⟩ := inj_inj hta
      rw [sumFibre_of_getElem? hRj] at ha
      obtain ⟨hfitR, heta⟩ := towerSet_elim_teleOfFields hw ha
      have hlenR : (rChain ((auxIds (p.W ψ) (p.Idss ψ)).length + (p.FssR ψ).length + 1)
          (auxIds (p.W ψ) (p.Idss ψ)).length (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) Es').length
          = (cdF ψ).2.1 + 1 := by
        rw [rChain, List.length_append, liftFields_length, hlenFs, List.length_singleton]
      have hpl : projList (rChain ((auxIds (p.W ψ) (p.Idss ψ)).length + (p.FssR ψ).length + 1)
          (auxIds (p.W ψ) (p.Idss ψ)).length (((cdF ψ).2.2.1.drop p.nP).map (·.2.2)) Es').length
          (mkTower ((ys.drop p.nP).map (interp V ρ) ++ [pt]))
          = (ys.drop p.nP).map (interp V ρ) ++ [pt] := by
        refine mkTower_inj ?_ heta.symm
        rw [projList_length, hlenR, List.length_append, hlenAs₂, List.length_singleton]
      rw [hpl] at hfitR
      unfold rChain at hfitR
      have hpref := spineFit_prefix (as := (ys.drop p.nP).map (interp V ρ)) (bs := [pt]) hfitR
      rw [List.take_left' (by rw [liftFields_length, hlenFs, hlenAs₂])] at hpref
      rw [spineFit_liftFields, hKfr, hsh] at hpref
      exact hpref
    -- **`hiota`**: `mutualRecIotaCore` at the split
    have hiota : (ps ++ Ms ++ Ss ++ is ++ [tv]).foldl SetTheory.app
          (interp V ρ (p.leaf m₀ t ψ))
        = interp V (consList ((ys.drop p.nP).map (interp V ρ))
            (consList Ss (consList Ms (consList ps ρ))))
            (mutualRuleCoreAV (p.bb ψ) (fun q => p.leaf m₀ q ψ) (p.tgts J) p.nP p.k p.n
              (cdF ψ).2.1 J (cdF ψ).2.2.2.2.1 (cdF ψ).2.2.2.2.2.2 (cdF ψ).2.2.2.2.2.1) := by
      have h := mutualRecIotaCore (V := V) (EissRaw := p.EissO ψ)
        (Rof := fun q => p.leaf m₀ q ψ) hh.hbz hℓ0 hw (by rw [hLs]; exact ht)
        (by rw [hh.hn]; exact hJn) (by rw [hlenFss, hh.hn]) hlenPs (by rw [hLs]; exact hlenMs)
        (by rw [hh.hn]; exact hlenSs) (by rw [p.nIdxs_getD ht]; exact hlenIs) hlenAs₂
        (by rw [List.getD_eq_getElem?_getD, hFssJ, Option.getD_some]; exact hlenFs)
        (fun q _ => rfl)
        (fun q hq σ => (p.leaf_facts hyp (by rwa [hLs] at hq) ψ σ).1.1)
        (fun q hq => hAcl q (by rwa [hLs] at hq) ψ) hh.hclR hF.tag hIdsMM hidxFit hspRF
        (by rw [hLs, hh.hn, hfr4]) (hpre ψ) hspAux hmajV
        (fun i hi => by
          rw [hEissJ, List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_range (mem_recIdx.mp hi).1]
          rfl)
        (fun i _ => by rw [hLs]; exact hh.htgts J i)
        (mutualIhSpine_of hh (hcdJ ψ) hlenMs hlenSs hspP hspM hspS hfitB')
      rw [hLs, hh.hn, ← hrecIdxJ, ← htlsJ, ← hEissOJ] at h
      exact h
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
      (fun _ => hiota)
    exact hcore

end ConLeche.Model
