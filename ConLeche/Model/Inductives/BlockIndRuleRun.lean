module

public import ConLeche.Model.Inductives.BlockKitRuleRun
public import ConLeche.Model.Inductives.BlockRuleGrading
public import ConLeche.Model.Inductives.BlockIndRegimeRun

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

end ConLeche.Model
