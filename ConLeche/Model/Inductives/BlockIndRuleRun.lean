module

public import ConLeche.Model.Inductives.BlockKitRuleRun
public import ConLeche.Model.Inductives.BlockRuleGrading
public import ConLeche.Model.Inductives.BlockIndRegimeRun
public import ConLeche.Model.Inductives.BlockRuleCaRun
public import ConLeche.Model.Inductives.BlockKitIhRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Annot.BitInst

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

**Regime IND's rows (§2)** at the pinned witnesses (`ihKeys` the rule
frame's, `ihdoms := blockRecIhdomsK`, `Ca := blockRuleCaAV`): the count,
the fused opener reading, `hCaZ` and `hCaE`.  The bundle's last row (the
openers' fit at the POINT tuple's chain frame) is (F) at that tuple and
needs the arm's own induction to know the tuple is typed; the tested
patch `rm55-ind-hihTy.patch` restates it at every typed tuple, where
`blockIhFitTyped_run` pays it.

**The certificate family (§3)** at the pinned `Ca`, which closes
`BlockGradeOwed`'s `hcertsW` and regime IND's first row.
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
  identity (`blockRuleCertsChain_eq`, RM54);
* the conclusion at the SPLIT data (`hCaE`) — §29b's `blockIndCaE_of_run`
  at the pinned peel, the fields' fit at the parameter frame taken off
  the split's own `hspF` (`blockIndSpF_run`, peeled by
  `blockRuleSpine_peel`).  `blockIndCaE_of_rules`' `hfld` is NOT used:
  it quantifies over an index spine `is0` with no fit, and the slot
  agreement needs the tuple in the member's index set — over-quantified,
  and its one use has the fit (`his`) in scope.

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
  obtain ⟨hFK, hIK, -⟩ := blockRuleCertsChain_eq hμ h hkLen hcore ψ hc hj rs.length
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

/-- **Regime IND's fused `ih` opener reading** (`BlockIndRuleAt`'s third
row, `hihOpen` at one pair) at the pinned `ihdoms`: the IH sub-lane's
key (`blockKitIhKey_run`: the callee's peel and the opener's domain, at
the frame's MOVED telescope) restated at the BLOCK's rows — its three
row identities — with the tower's bit `0` at the IND regime
(`pwBit_zeronessOf` at the checked elimination level). -/
theorem blockIndIhOpen_run (hμ : μ.verifiedChecks = true)
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
    (ψ : Name → Nat)
    (hℓ : Level.eval ψ (ConLeche.structElimLevel p.toBlockShape.elim p.toBlockShape.large) = 0)
    {c : Nat} (hc : c < rs.length) {j : Nat} (hj : j < blockRecNCt rs c) :
    ∀ r, r < ((blockRuleFrameAt p rs c j).ihKeys).length →
      ∃ (i c' nF nIdx m : Nat) (eisA : List AnnotTerm) (fapA CihR : AnnotTerm),
        (((blockRuleFrameAt p rs c j).ihKeys).getD r (0, 0)).1 = i ∧
        (((blockRuleFrameAt p rs c j).ihKeys).getD r (0, 0)).2 = c' ∧
        c' < rs.length ∧
        i < ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length ∧
        ((d.rss (p.toBlockShape.recTgtAt c)).getD j []).getD i false = true ∧
        d.tgts (p.toBlockShape.recTgtAt c) j i = p.toBlockShape.recTgtAt c' ∧
        ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = nF ∧
        (((d.tlss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i []).length = m ∧
        (((d.Eiss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i []).length = nIdx ∧
        (d.IdsM (p.toBlockShape.recTgtAt c') ψ).length = nIdx ∧
        eisA = (((d.Eiss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i []).map
            (ihIdxAtM nF (p.toBlockShape.rulePrefixAt c - d.nP) i 0 m) ∧
        fapA = AnnotTerm.mkAppN (.bvar (nF - 1 - i + m)) (teleVarsAV m) ∧
        BlockRuleConclAt (p.toBlockShape.rulePrefixAt c') nF m
          (blockRecTyAV mpC.base2.acval envC rs ψ c') eisA fapA CihR ∧
        (blockRecIhdomsK rs.length p mpC.base2.acval envC rs ψ c j).getD r default
          = (mkPisAV (ihTeleAtR nF (p.toBlockShape.rulePrefixAt c - d.nP) i 0
              (rebit 0 (((d.tlss (p.toBlockShape.recTgtAt c) ψ).getD j []).getD i [])))
              CihR).liftN r 0 := by
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR'
  obtain ⟨-, hIK, -⟩ := blockRuleCertsChain_eq hμ h hkLen hcore ψ hc hj rs.length
  intro q hq
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  have hct : blockRuleCtorOf rs c j = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨hfrP, -, hfrF, -, -, -, -, hpw⟩ := blockRuleFrameAt_rows (pp := p) hct
  obtain ⟨fi, c', CihR, hkeyE, hc'K, hfiC, -, hrss, htgt, hIget, -, hcon, -, -, -, -, eT, eE,
    eL, -⟩ := blockKitIhKey_run hμ h hkLen hdR hN hS hcore hmr hM hr hcA ψ hq
  -- the member, the constructor's record and the field's kind
  obtain ⟨ms, hms, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
  have hmemk : p.toBlockShape.recTgtAt c
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
    (List.getElem?_eq_some_iff.mp hms).1
  have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hcf : BlockCtorFacts mpC.base2
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) p.lps
      (p.toBlockShape.recTgtAt c) j cA := ⟨hfindC, hlpsC, hcd⟩
  have hks : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ksF
      (p.toBlockShape.recTgtAt c) j = (blockRuleKsOf p c j).map ConLeche.BlockFieldKind.toRec := by
    rw [blockDataOf_ksF]; rfl
  have hksLen : (blockRuleKsOf p c j).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  have hFssLen : (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
      (p.toBlockShape.recTgtAt c) ψ).getD j []).length = cA.2 := by
    rw [BlockData.Fss, BlockData.cds, fssOfR_fixCtorDataList_getD hcj, List.length_map,
      List.length_drop, hcd.len ψ]
    show p.nP + cA.2 - p.nP = cA.2
    omega
  obtain ⟨-, hlenR, -⟩ := checkBlockRecK_recNames h
  have hrecTgtsLen : p.recTgts.length = rs.length := by
    show ((List.range p.recs.length).map p.toBlockShape.recTgtAt).length = _
    rw [List.length_map, List.length_range, hlenR]
  have hrecTgts : ∀ e, e < rs.length → p.recTgts.getD e rs.length = p.toBlockShape.recTgtAt e := by
    intro e he
    show ((List.range p.recs.length).map p.toBlockShape.recTgtAt).getD e rs.length = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  have hkey' : (ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt c)
      ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
      (blockRuleKsOf p c j)).getD q (0, 0) = (fi, c') := by
    show ((blockRuleFrameAt p rs c j).ihKeys).getD q (0, 0) = _
    rw [List.getD_eq_getElem?_getD, hkeyE]; rfl
  obtain ⟨-, -, -, -, -, hkind⟩ :=
    blockIhKey_block_facts (d := blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
      (ψ := ψ) (K := rs.length) (mem := p.toBlockShape.recTgtAt) hcj hks hksLen hFssLen
      (fun _ => rfl) hrecTgtsLen hrecTgts hkey' (by exact hq)
  obtain ⟨-, hEl⟩ := blockIhKey_block_lengths (V := V) ψ hcj hcf hfiC hkind
  rw [htgt] at hEl
  have hmemk' : p.toBlockShape.recTgtAt c'
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k := by
    obtain ⟨r', hr'⟩ : ∃ r', rs[c']? = some r' := ⟨rs[c']'hc'K, List.getElem?_eq_getElem hc'K⟩
    exact (blockRecMajor_run (V := V) hμ mpC h hmr hr' ψ).2.1
  have hIds := blockMembers_IdsM_length hmr hmemk' ψ
  -- the tower's bit at the IND regime
  have hb0 : pwBit ψ (blockRuleFrameAt p rs c j).pw = 0 := by
    rw [hpw, pwBit_zeronessOf]; exact hℓ
  -- the key's moved data, at the block's rows
  have hTl : blockKitTlA p rs mpC.base2.acval envC ψ c j fi
      = ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
          (rebit 0 (((
            (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tlss
              (p.toBlockShape.recTgtAt c) ψ).getD j []).getD fi [])) := by
    rw [blockKitTlA, hb0, eT, hfrF]
  have hEis : blockKitEisA p rs mpC.base2.acval envC ψ c j fi
      = ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Eiss
          (p.toBlockShape.recTgtAt c) ψ).getD j []).getD fi []).map
        (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
          ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tlss
            (p.toBlockShape.recTgtAt c) ψ).getD j []).getD fi []).length) := by
    rw [blockKitEisA, eE, eL, hfrF]
  have hFap : blockKitFapA p rs c j fi
      = AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi
          + ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tlss
            (p.toBlockShape.recTgtAt c) ψ).getD j []).getD fi []).length))
        (teleVarsAV ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tlss
            (p.toBlockShape.recTgtAt c) ψ).getD j []).getD fi []).length) := by
    rw [blockKitFapA, eL, hfrF, Nat.add_zero]
  have hTlLen : (blockKitTlA p rs mpC.base2.acval envC ψ c j fi).length
      = ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tlss
            (p.toBlockShape.recTgtAt c) ψ).getD j []).getD fi []).length := by
    rw [hTl, ihTeleAtR_length, rebit_length]
  rw [hTlLen, hEis, hFap] at hcon
  refine ⟨fi, c', cA.2, _, _, _, _, CihR, ?_, ?_, hc'K, by rw [hFssLen]; exact hfiC, hrss, htgt,
    hFssLen, rfl, by rw [hEl, hIds], rfl, rfl, rfl, hcon, ?_⟩
  · rw [List.getD_eq_getElem?_getD, hkeyE]; rfl
  · rw [List.getD_eq_getElem?_getD, hkeyE]; rfl
  · rw [hIK, hIget, hTl]
    rfl

end IndRows

/-! ## 3. The certificate family, PRODUCED at the pinned `Ca`

`BlockGradeOwed`'s `hcertsW` (RM54: at the BASE frame, the rule's own
openers) is `BlockRuleCerts.of_segments` at the three pinned segments
(`blockRulePdomsAV`, `blockRuleFdomsAV`, `blockRuleIhdomsAV`), the pinned
residue `blockRuleRbAV` and the pinned conclusion `blockRuleCaAV`:

* the openings, their scoping, closedness, constants and leaves — the
  run (`blockRuleData_run`, `blockRuleResidueData_runP`,
  `blockRuleOpened_run`, `blockRuleConclClosed_of`);
* the three segments' readings — `blockRulePdomsAV_reads`,
  `blockRuleFdomsAV_eq`, `blockRuleIhReads_run`;
* `hokA` — the rule frame's grading (G), `blockRuleGrading_run`;
* the residue's and the conclusion's readings — `blockRuleOpened_run`'s
  last conjunct and `blockRuleCaAV_run`;
* `hokC` — `blockRuleHokC_of_run` at the conclusion's peel
  (`blockRuleCaAV_run`), its fit (§1) and the peel's arguments' grading:
  the prefix bvars are free, the index readings are the constructor's
  (`blockCtorEs_wdV`) and the fired spine is graded
  (`blockRuleMkAV_wdV`), each read one `ih` block deeper. -/

section Certs

/-- A satisfied rule context is a prefix spine, a field spine and an
`ih` spine over a base frame. -/
theorem sat_blockRuleCtx_split {P Fd IH : List AnnotTerm} {σ : Nat → V}
    (h : Sat V (IH.reverse ++ (P ++ Fd).reverse) σ) :
    ∃ (σ₀ : Nat → V) (xs fs ws : List V),
      σ = consList ws (consList (xs ++ fs) σ₀) ∧ SpineFit σ₀ (P ++ Fd) (xs ++ fs) ∧
      SpineFit σ₀ P xs ∧ SpineFit (consList xs σ₀) Fd fs ∧
      SpineFit (consList (xs ++ fs) σ₀) IH ws := by
  rw [← List.reverse_append] at h
  have hsp := spineFit_frameIdx_of_sat h
  have hσ := consList_frameIdx (V := V) (P ++ Fd ++ IH).length σ
  generalize ConLeche.Semantics.frameIdx _ σ = vals at hsp hσ
  generalize shiftE _ 0 σ = σ₀ at hsp hσ
  subst hσ
  obtain ⟨ab, ws, rfl, hab, hws⟩ := spineFit_append_split hsp
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hab
  exact ⟨σ₀, xs, fs, ws, by rw [consList_append], hab, hxs, hfs, hws⟩

/-- **The certificate family at the pinned `Ca`** — `BlockGradeOwed`'s
`hcertsW` row with `Ca := blockRuleCaAV` and `Rb0 := blockRuleRbAV`. -/
theorem blockRuleCertsP_run (hμ : μ.verifiedChecks = true)
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
    (hM : BlockModelAt mpC.base2 names d) :
    ∀ (ψ : Name → Nat), ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      BlockRuleCerts V mpC F ψ (p.toBlockShape.rulePrefixAt c)
        (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
        (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c)
        (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j)
        (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j)
        (blockRuleRbAV p rs mpC.base2.acval envC ψ c j)
        (blockRuleCaAV p rs mpC.base2.acval envC ψ c j) := by
  intro ψ c hc j hj
  have hG := blockRuleGrading_run hμ h hkLen hdR hN hS hcore hmr hM
  have hdR' := hdR
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR'
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  have hct : blockRuleCtorOf rs c j = cA := blockRuleCtorOf_eq hr hcA
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  -- the constructor's record and stored type
  have hmemk : p.toBlockShape.recTgtAt c
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
    (blockRecMajor_run (V := V) hμ mpC h hmr hr ψ).2.1
  have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c))[j]? = some cA := by rw [hctM c _ hr]; exact hcA
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hcf : BlockCtorFacts mpC.base2
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) p.lps
      (p.toBlockShape.recTgtAt c) j cA := ⟨hfindC, hlpsC, hcd⟩
  have hcdP := hcd
  rw [show (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP = p.nP
    from rfl] at hcdP
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hcbC : ConstsBound envC cA.1.type := constsBound_of_constsResolve _ hwfC.2.2.1
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).fvsPF
            (p.toBlockShape.recTgtAt c) j
          ++ (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xFvsF
            (p.toBlockShape.recTgtAt c) j,
          (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xrestF
            (p.toBlockShape.recTgtAt c) j) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  obtain ⟨bsC, bodyC0, hstC, -, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hop0
  have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by rw [hstC]; rfl
  have hks : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ksF
      (p.toBlockShape.recTgtAt c) j = (blockRuleKsOf p c j).map ConLeche.BlockFieldKind.toRec := by
    rw [blockDataOf_ksF]; rfl
  have hksLen : (blockRuleKsOf p c j).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  obtain ⟨_, cvTa, _, _, _, _, _, -, hcvTa, hnP, -⟩ := checkBlockRecK_tyMajor h hr
  obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ cvTa hcvTa
  have hframes := (hS.frames _ hmemk j cA hcj).1 ψ
  -- the run's openings
  obtain ⟨o₁, cpref, rbs, body, ldoms, lrest, h₁, hinstC, h₂, -, -, -, -, -⟩ :=
    blockRuleData_run h hr hcA hrhs
  obtain ⟨-, ty, concl, -, -, -, hopen, hinf, hconcl, hdeq⟩ :=
    blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨-, -, -, hlbF, hcbF, hclF, -, hbodyO, -, hbR, hleafR, hw₃, hexB⟩ :=
    blockRuleOpened_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  obtain ⟨hw₁, hb₁⟩ := checkBlockRecK_tyClosed h hr
  have hf₁ : rs[c].1.type.hasFvar = false :=
    (ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr)).1
  have hb₂ : (blockRuleCrest p.toBlockShape rs c j).looseBVarsBounded 0 = true :=
    (instPisAt_bounded _ hinstC hCb
      (fun a ha => openPisAtFvars_fvars_closed h₁ a (List.mem_of_mem_take ha))).2
  obtain ⟨hbC, hleafC⟩ := blockRuleConclClosed_of h₁ h₂ hf₁ hCf hb₁ hb₂ hinstC hconcl
  obtain ⟨hCa, hcon⟩ := blockRuleCaAV_run hμ h hr hcA hrhs hcdP hCf hCb hfindC hlpsC hnP ψ
  -- the lengths
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [blockRuleFdomsAV, readOpenedDoms_length_eq, openPisAtFvars_length _ h₂]
  have hil : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length
      = (blockRuleFrameAt p rs c j).nR := by
    rw [blockRuleIhdomsAV, hct, readOpenedDoms_length_eq, openPisAtFvars_length _ hopen]
  -- the residue's reading
  have hRb : denoteMeta mpC.base2.acval envC ψ
      (p.toBlockShape.rulePrefixAt c + cA.2 + (blockRuleFrameAt p rs c j).nR)
      (blockRuleBodyOAt p rs c j) = some (blockRuleRbAV p rs mpC.base2.acval envC ψ c j) := by
    obtain ⟨B, hB⟩ := hexB ψ
    rw [blockRuleRbAV, hct, ← hbodyO, hB]
    rfl
  -- the `ih` openers' readings
  have hexI := blockRuleIhReads_run hμ h hkLen hdR hN hS hcore hmr hM hr hcA ψ
  have hI : ∀ (l : Nat) (x : Expr), (blockRuleFvsIhAt p rs c j)[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt c + cA.2 + l)
        (Expr.fvarTypeD x)
      = some ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).getD l default) := by
    intro l x hx
    rw [blockRuleIhdomsAV, hct]
    exact readOpenedDoms_reads hexI l x hx
  -- `hokC`: the peel, its fit, and the peel's arguments graded
  have hfit := blockRuleConclFit_run hμ h hkLen hcore hmr hM hN rfl hctM ψ hc hj
  rw [hpl, hfl, hil] at hfit
  have hokC := blockRuleHokC_of_run hμ mpC h hr ψ hcon hfit (fun ρ hρ a ha => by
    obtain ⟨σ₀, xs, fs, ws, rfl, hab, hxs, hfs, hws⟩ := sat_blockRuleCtx_split hρ
    have hxl : xs.length = p.toBlockShape.rulePrefixAt c := by rw [hxs.length_eq, hpl]
    have hwl : ws.length = (blockRuleFrameAt p rs c j).nR := by rw [hws.length_eq, hil]
    have hsp0 : SpineFit (chainFrame 0 (fun _ => (pt : V)) σ₀)
        (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRecFdomsK 0 mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
      rw [chainFrame_zero, blockRecFdomsK, liftDomsK_zero]; exact hab
    obtain ⟨cA', rhs', hcA', -, -, -, -, -, hxs', hfsl, -, hpre, -, hfb, hes, -⟩ :=
      blockRuleSpine_peel hμ h hkLen hcore hmr rfl hctM hr hj
        (by rw [hxs.length_eq]) hsp0
    obtain rfl : cA' = cA := Option.some.inj (hcA'.symm.trans hcA)
    have hpc := blockRuleParamFit_run hμ mpC h hr ψ hcvTa hfT hFD (Nat.le_add_right _ _)
      (hcd.len ψ) hframes (spineFit_take_any hpre p.nP)
    refine blockRuleHokC_args (fun e he => ?_) ?_ a ha
    · -- an index reading, one `ih` block deeper
      obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
      rw [blockRecEsK] at he'
      obtain ⟨E0, hE0, rfl⟩ := List.mem_map.mp he'
      rw [AnnotTerm.liftN_zero, WellDenotedV_liftN, ← hwl, shiftE_consList]
      rw [hes] at hE0
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp hE0
      have hq := (wellDenotedV_liftN_rule (K := 0) (a := fun _ => (pt : V)) (ρ := σ₀)
        (nP := (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP)
        hxl hfsl E).mpr (blockCtorEs_wdV hcf hcj hpc hfb E hE)
      rw [chainFrame_zero, AnnotTerm.liftN_zero] at hq
      exact hq
    · -- the fired spine, one `ih` block deeper
      rw [blockRecMkK, AnnotTerm.liftN_zero, WellDenotedV_liftN, ← hwl, shiftE_consList]
      exact blockRuleMkAV_wdV h hr hcA hrhs hcf hcj rfl hnP hxl hfsl hpc hfb)
  rw [hfl, hil]
  refine BlockRuleCerts.of_segments mpC h₁ h₂ hopen hw₁
    (blockRuleHw2_of h₁ hw₁ hCf hinstC) hw₃ hlbF hcbF hclF hpl hfl hil
    (blockRulePdomsAV_reads hμ mpC h hr ψ h₁)
    (blockRuleFdomsAV_eq h hr hcA hrhs hcdP hCf hnP ψ).2 hI
    (fun l hl σ ys hys => hG c rs[c] hr j cA hcA ψ l hl σ ys hys)
    hinf hdeq hbR hbC hleafR (fun l hl => List.mem_append_left _ (hleafC l hl)) hRb (hCa _ hconcl)
    hokC

end Certs

end ConLeche.Model
