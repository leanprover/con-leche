module

public import ConLeche.Model.Inductives.BlockKitRuleRun
public import ConLeche.Model.Inductives.BlockRuleGrading
public import ConLeche.Model.Inductives.BlockIndRegimeRun
public import ConLeche.Model.Inductives.BlockRuleCaRun
public import ConLeche.Model.Inductives.BlockKitIhRun
import ConLeche.Model.Inductives.BlockRecPreHpre

public section

/-!
# Regime IND's per-rule bundle at the run (lane RM55)

`BlockIndOwed`'s one row (`BlockRecPreHpre.lean`) is `BlockIndRuleAt`
(`BlockIndRegimeRun.lean` §3) at every (recursor, constructor) pair:
the rule's certificates, the `ih` openers' count and fused reading, the
conclusion's truth value at every certified frame (`hCaZ`), the
conclusion at the SPLIT data (`hCaE`) and the `ih` openers' fit at the
chain frame.

**The conclusion's fit (§1).**  Two consumers ask for the same fact
about the rule's CONCLUSION `Ca` — the recursor type peeled along the
rule's spine (`BlockRuleConclAt`): the certificate producer's `hfit`
(`blockRuleCerts_of_run`, the `hokC` half) and regime IND's `hCaZ`
(`blockRuleConclUnivZero_run`'s `hfit`).  Both want the peel's
arguments — the prefix bvars, the index readings and the fired spine,
each read one `ih` block deeper — to fit the recursor type's tower at
EVERY frame satisfying the rule's context.  That is KIT1's
`blockKitRule_run` (the fired spine fits the recursor's binder data) at
the context's own values, `K = 0`, carried to a `TeleFitPA` by RM53's
`teleFitPA_mkPisAV_of_spineFit`.  §1 states it once.

**The frame.**  The context is the rule's own
`ihdoms.reverse ++ (pdoms ++ fdoms).reverse`, at the BASE-frame
components (`blockRuleFdomsAV`, `blockRuleIhdomsAV` — the spelling
`blockRuleCerts_of_run` concludes at); nothing is stated at a frame
that does not satisfy it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-! ## 1. The rule's conclusion FITS the recursor's tower -/

section ConclFit

/-- A satisfied reversed context is a fitting spine of its own frame
index over its shift. -/
theorem spineFit_frameIdx_of_sat {Ds : List AnnotTerm} {σ : Nat → V}
    (h : Sat V Ds.reverse σ) :
    SpineFit (shiftE Ds.length 0 σ) Ds (ConLeche.Semantics.frameIdx Ds.length σ) := by
  have hlen : (ConLeche.Semantics.frameIdx Ds.length σ).length = Ds.length := by
    simp [ConLeche.Semantics.frameIdx]
  refine spineFit_of_sat_consList hlen ?_
  rw [consList_frameIdx]
  exact h

/-- **The rule's conclusion FITS the recursor's tower** at every frame
satisfying the rule's context: the peel's arguments — the prefix
bvars, the constructor's result index readings and the fired spine,
each lifted past the `ih` block — read along the recursor type's
Π-tower.  It is `blockRuleCerts_of_run`'s `hfit` and regime IND's
`hCaZ` fit (`blockRuleConclUnivZero_run`), at the peel's own argument
list. -/
theorem blockRuleConclFit_run (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) (hN : BlockNamesOk (V := V) d cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    (ψ : Name → Nat) {c : Nat} (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c) :
    ∀ σ : Nat → V,
      Sat V ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse) σ →
      ∃ rest, TeleFitPA V σ (blockRecTyAV mpC.base2.acval envC rs ψ c)
        (paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
            ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
              + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
              + (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length)
          ++ (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
              (·.liftN (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length 0)
          ++ [(blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
              (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length 0]) rest := by
  intro σ hsat
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  -- the context's values, split into the prefix, the fields and the `ih` block
  have hL : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).reverse
        ++ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).reverse
      = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
          ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).reverse :=
    List.reverse_append.symm
  rw [hL] at hsat
  have hsp := spineFit_frameIdx_of_sat hsat
  have hσ := consList_frameIdx (V := V)
    (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
      ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length σ
  generalize ConLeche.Semantics.frameIdx _ σ = vals at hsp hσ
  generalize shiftE _ 0 σ = σ₀ at hsp hσ
  subst hσ
  obtain ⟨ab, ws, rfl, hab, hws⟩ := spineFit_append_split hsp
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hab
  have hxl : xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length :=
    hxs.length_eq
  have hfl : fs.length = (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length :=
    hfs.length_eq
  have hwl : ws.length = (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length :=
    hws.length_eq
  -- KIT1's fired-spine fit, at `K = 0`
  have hsp0 : SpineFit (chainFrame 0 (fun _ => (pt : V)) σ₀)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [chainFrame_zero, blockRecFdomsK, liftDomsK_zero]
    exact hab
  have hfire := blockKitRule_run hμ h hkLen hcore hmr hM hN hdnP hctM ψ 0 (fun _ => pt) σ₀
    c hc j hj xs fs hxl hsp0
  rw [chainFrame_zero] at hfire
  -- the recursor's tower, and its binder data's bounds
  obtain ⟨-, -, -, -, hTyE, -, -, -, -, -⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
  obtain ⟨hbndR, -⟩ := checkBlockRecK_tyBounds hμ mpC h hr ψ
  -- the argument list reads to the fired spine's values
  have hframe : consList (xs ++ fs ++ ws) σ₀ = consList ws (consList (xs ++ fs) σ₀) := by
    rw [consList_append]
  have hpb : (paramBvarsAt (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
          + (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length)).map
        (interp V (consList (xs ++ fs ++ ws) σ₀)) = xs := by
    have hLlen : (xs ++ fs ++ ws).length
        = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
          + (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length := by
      rw [List.length_append, List.length_append, hxl, hfl, hwl]
    rw [map_bvarAt_take (nP := (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length)
      hLlen.symm (by rw [hLlen]; omega), List.append_assoc, List.take_left' hxl]
  have hes : ((blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
        (·.liftN (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length 0)).map
        (interp V (consList (xs ++ fs ++ ws) σ₀))
      = (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
        (interp V (consList (xs ++ fs) σ₀)) := by
    rw [List.map_map]
    refine List.map_congr_left fun e _ => ?_
    show interp V (consList (xs ++ fs ++ ws) σ₀)
      (e.liftN (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length 0) = _
    rw [hframe, ← hwl]
    exact interp_liftN_ihvals e
  have hmk : interp V (consList (xs ++ fs ++ ws) σ₀)
        ((blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
          (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length 0)
      = interp V (consList (xs ++ fs) σ₀)
          (blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) := by
    rw [hframe, ← hwl]
    exact interp_liftN_ihvals _
  -- the tower's binder data is closed below its own entries, so the fit
  -- moves from the base frame to the context's
  have hbnd : ∀ l, l < ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
      (fun b : Nat × Nat × AnnotTerm => b.2.2)).length →
      Term.bvarsBelow l ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (fun b : Nat × Nat × AnnotTerm => b.2.2)).getD l default).erase) := by
    intro l hl
    rw [List.length_map] at hl
    have hq := hbndR l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at hq
    exact hq
  have hfitσ := spineFit_frame_of_bounded (σ' := consList (xs ++ fs ++ ws) σ₀) hbnd hfire
  rw [hTyE]
  refine teleFitPA_mkPisAV_of_spineFit ?_ ?_
  · have hq := hfire.length_eq
    simp only [List.length_map, List.length_append, List.length_singleton] at hq
    simp only [List.length_append, List.length_map, paramBvarsAt_length, List.length_singleton]
    omega
  · rw [List.map_append, List.map_append, hpb, hes, List.map_cons, List.map_nil, hmk]
    rw [← List.append_assoc] at hfitσ
    exact hfitσ

end ConclFit

/-! ## 2. Regime IND's per-rule rows, at the pinned witnesses

`BlockIndRuleAt` at `ihKeys := (blockRuleFrameAt p rs c j).ihKeys`,
`ihdoms := blockRecIhdomsK` (the grading bundle's pin) and
`Ca := blockRuleCaAV` (the conclusion's pin, `BlockRuleCaRun.lean`):

* the openers' COUNT — the pinned `ihdoms` has the frame's `nR` entries,
  which IS the key list's length (`BlockRuleFrame.nR`);
* the conclusion's TRUTH VALUE at every certified frame (`hCaZ`) —
  `blockRuleConclUnivZero_run` with the peel (`blockRuleCaAV_run`) and
  §1's fit, the `K` lifts of the field and `ih` domains being the
  identity (`blockRecFdomsK_eq_of_bounded`, `blockRecIhdomsK_eq`);
* the conclusion at the SPLIT data (`hCaE`) — `blockIndCaE_of_rules` at
  the pinned `hdat` (`blockIndCaE_hdat_run`).

**The frame.**  `hCaZ` is stated at every `σ` and every pair of fits,
exactly as the bundle states it (the consumer instantiates it at the
split frame and at the chain frame); `hCaE` at the split data at the
base frame `ρ`. -/

section IndRows

/-- **Regime IND's count, truth-value and split-data rows** at one
(recursor, constructor) pair, at the pinned `ihdoms`/`Ca`. -/
theorem blockIndRuleRows_run (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (ψ : Name → Nat) (ρ : Nat → V)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0)
    {c : Nat} (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c) :
    (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j).length
        = ((blockRuleFrameAt p rs c j).ihKeys).length ∧
    (∀ (σ : Nat → V) (xs fs vs : List V),
      SpineFit σ
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)
        (xs ++ fs) →
      SpineFit (consList (xs ++ fs) σ) (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j)
        vs →
      interp V (consList vs (consList (xs ++ fs) σ)) (blockRuleCaAV p rs mpC.base2.acval envC ψ c j)
        ∈ˢ (univZero : V)) ∧
    (∀ (as ms is : List V) (x : V),
      SpineFit ρ (d.params ψ) as →
      SpineFit (consList as ρ)
        ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).drop
          d.nP).take (p.toBlockShape.rulePrefixAt c - d.nP)) ms →
      SpineFit (consList as ρ) (d.IdsM (p.toBlockShape.recTgtAt c) ψ) is →
      ∀ fs : List V,
      d.ChainFit ψ (consList as ρ)
        (sepTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
          (blockIndP d ψ ρ rs.length p.toBlockShape.rulePrefixAt p.toBlockShape.recTgtAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) as))
        (d.tup ψ (p.toBlockShape.recTgtAt c) is) (p.toBlockShape.recTgtAt c) j fs →
      x = d.inj ψ (p.toBlockShape.recTgtAt c) j fs →
      interp V
          (consList (List.replicate (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j).length
            (pt : V)) (consList (as ++ ms ++ fs) ρ)) (blockRuleCaAV p rs mpC.base2.acval envC ψ c j)
        = interp V (consList (as ++ ms ++ is ++ [x]) ρ)
            (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c)) := by
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR'
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  obtain ⟨r, cA, rhs, ci, hr', hcA, hrhs, hfind, hlps, hnP, hcj, hjc, hcon, hes, hpl, hfl, hih,
    hFss, hrdsLen, hmemN⟩ := blockRuleCaAV_pair hμ h hkLen hcore hmr rfl hctM ψ hc hj
  obtain rfl : r = rs[c] := Option.some.inj (hr'.symm.trans hr)
  -- the `K` lifts are the identity
  have hFK := blockRecFdomsK_eq_of_bounded (blockRuleDoms_bounded_at hμ h hcore ψ) hr hcA hrhs
    rs.length
  have hIK := blockRecIhdomsK_eq hμ h hkLen hdR hN hS hcore hmr hM hc hj ψ rs.length
  refine ⟨hih, ?_, ?_⟩
  · -- `hCaZ`: the peel, §1's fit and the checked level
    obtain ⟨us, uOf, helim, hmemU, hbitsE, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
    have hℓ' : (us.headD .zero).eval ψ = 0 := by
      rw [blockRecHeadLevel_run h helim hmemU hruns ψ]; exact hℓ
    have hbits : OneElimLevel 0 rs.length
        (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) := by
      rw [← hℓ']
      exact blockRecOneElimLevel helim ψ hmemU (hbitsE ψ)
    have hfit := blockRuleConclFit_run hμ h hkLen hcore hmr hM hN rfl hctM ψ hc hj
    have hIl : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length
        = (blockRuleFrameAt p rs c j).nR := by
      rw [← hIK]; exact hih
    rw [hpl, hfl, hIl] at hfit
    -- the peel's argument list is as long as the recursor's binder data
    have hesl : (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        = ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).IdsM
          (p.toBlockShape.recTgtAt c) ψ).length := by
      have hmemk : p.toBlockShape.recTgtAt c
          < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
        (blockRecMajor_run (V := V) hμ mpC h hmr hr ψ).2.1
      have hcd := blockCtorData_of_core hcore hcj
      rw [blockRecEsK, List.length_map, hes, List.length_map, BlockData.Ess, BlockData.cds,
        essOfR_fixCtorDataList_getD hcj, hcd.lenE ψ, blockMembers_IdsM_length hmr hmemk ψ]
    have hlen : (paramBvarsAt (p.toBlockShape.rulePrefixAt c)
          (p.toBlockShape.rulePrefixAt c + cA.2 + (blockRuleFrameAt p rs c j).nR)
        ++ (blockRecEsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
            (·.liftN (blockRuleFrameAt p rs c j).nR 0)
        ++ [(blockRecMkK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j).liftN
            (blockRuleFrameAt p rs c j).nR 0]).length
        = (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length := by
      rw [List.length_append, List.length_append, paramBvarsAt_length, List.length_map, hesl,
        List.length_singleton, hrdsLen]
    rw [hFK, hIK]
    exact blockRuleConclUnivZero_run hμ mpC h ψ hc hbits hlen hcon hfit
  · -- `hCaE`: the split data — §29b's `blockIndCaE_of_run` at the pinned peel, with
    -- the fields' fit at the parameter frame off the split's own `hspF`
    intro as ms is x hpar hms his fs hfit hx
    have hmemk : p.toBlockShape.recTgtAt c
        < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
      (blockRecMajor_run (V := V) hμ mpC h hmr hr ψ).2.1
    have hk0 : 0 < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
      Nat.lt_of_le_of_lt (Nat.zero_le _) hmemk
    have hlenP : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).params ψ).length
        = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP := by
      have hl := hS.lenPps 0 ψ hk0
      rw [BlockData.params, List.length_map, List.length_take]
      exact Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) (Nat.le_of_eq hl.symm))
    obtain ⟨hnPle, hlenDc, -, -, -⟩ := blockRecTyShape_run hμ mpC h hmr rfl ψ ρ c hc
    have hasl : as.length = p.nP := by rw [hpar.length_eq, hlenP]; rfl
    have hmsl : ms.length = p.toBlockShape.rulePrefixAt c - p.nP := by
      have hdn : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP = p.nP := rfl
      rw [hms.length_eq, List.length_take, List.length_drop, List.length_map, hrdsLen, hdn]
      omega
    have hxs : (as ++ ms).length = p.toBlockShape.rulePrefixAt c := by
      rw [List.length_append, hasl, hmsl]; omega
    have htake : (as ++ ms).take p.nP = as := List.take_left' hasl
    -- the split's rule spine fits, and its field half fits the constructor's own domains
    have hspF := blockIndSpF_run hμ h hkLen hcore hmr hM hN rfl hctM ψ
      (blockRuleDoms_bounded_at hμ h hcore ψ) hlenP ρ c hc as ms is hpar hms his j hj fs hfit
    rw [hFK, ← blockRecFdomsK_eq_of_bounded (blockRuleDoms_bounded_at hμ h hcore ψ) hr hcA hrhs 0]
      at hspF
    obtain ⟨cA', rhs', hcA', -, -, -, -, -, -, hfsl, -, -, -, hsf, -, -⟩ :=
      blockRuleSpine_peel hμ h hkLen hcore hmr rfl hctM hr hj (K := 0) (a := fun _ => pt)
        (ρ := ρ) (by rw [hxs, hpl]) (by rw [chainFrame_zero]; exact hspF)
    obtain rfl : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
    rw [show (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP = p.nP from rfl,
      htake] at hsf
    rw [← htake] at hpar his hfit hsf
    have hq := blockIndCaE_of_run (ihvals := List.replicate
      (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j).length (pt : V))
      hμ hM h hr hcA hrhs hfind hlps hnP rfl hmemN hcj hjc ψ hcon
      rfl rfl hes hpl hfl
      (by rw [hrdsLen]) rfl hxs hfsl (by rw [List.length_replicate, hih]) hpar hsf his hfit hx
    exact hq

end IndRows

end ConLeche.Model
