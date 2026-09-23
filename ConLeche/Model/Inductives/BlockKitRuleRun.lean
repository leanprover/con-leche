module

public import ConLeche.Model.Inductives.BlockRecTyShapeRun
public import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockStageCtors
import ConLeche.Model.Inductives.FixAssemblyKit

public section

/-!
# The kit arms' `hrule` — the fired spine fits the recursor's type

`blockKitRegime_wf` / `blockKitRegime_sq` (`BlockRecPreRun.lean` §19,
§36) ask, at the ONE datum each arm builds (§19a: `blockWfCand` /
`blockSqCand`), that the rule's fired spine — the rule prefix `x⃗`, the
constructor's result index readings and the fired constructor
application — fits the recursor's own binder data:

```
SpineFit ρ ((rds c).map (·.2.2)) (x⃗ ++ (e⃗ ++ [mk]))
```

whenever `x⃗ ++ f⃗` fits the rule's prefix and field domains at the
arm's chain frame.  Stage (b'')'s converse (`blockRecIdxConv_run`,
`BlockRecIdxConv.lean`) makes it composable from the run alone:

* **the prefix** — the chain lift of the (closed) prefix domains is the
  identity (`blockRecPdomsK_run` + `spineFit_liftDomsK`), so `x⃗` fits
  the recursor's first `rP` binders at the BASE frame;
* **the index values** — the constructor's result index readings fit
  the MEMBER's index telescope (`BlockModelAt.resIdxFit`, at the field
  spine §23's transport hands down), and the converse carries them to
  the RECURSOR's index binders;
* **the major** — the fired spine reads to the block's injection
  (`blockRecMkK_value`), the injection of a `ChainFit` spine lies in the
  operator's fibre (`BlockModelAt.fibre`) and so in the carrier
  (`lfpTuple_closed`), the carrier is the member's former applied
  (`BlockModelAt.leaf`), which is the major binder's reading
  (`interp_of_major_reading`).

Nothing here reads the chain frame's candidate: the generic statement
(`blockKitRule_run`) holds at every `chainFrame K a ρ`, and the two
arm-shaped statements (`blockWfRule_run`, `blockSqRule_run`) are it at
the arms' own data, spelled exactly as `BlockWfOwed`/`BlockSqOwed`'s
`hrule` row.

**The frame.**  The converse is a `DefEqClaim` read at the recursor's
rule prefix followed by the member's indices; it concludes only at a
prefix fitting the recursor's prefix domains.  That fit is exactly what
the antecedent gives (the prefix half of the chain-frame fit), so the
producer is stated at the satisfying frame and nowhere else.
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

/-! ## 1. The rule's own spine, peeled to the constructor's datum -/

section Peel

/-- **The rule's spine at a chain frame, peeled**: the constructor the
rule names (the SAME `cA` in the recursor's rule list and in the
member's constructor list), its record, the prefix fit at the BASE
frame (the `K` lift of a closed telescope is the identity, §28 of
`BlockRecPreRun`), the parameter fit (`blockRecParams_run`), the field
spine at the chain frame and at the parameter frame (§23's transport),
and the two syntactic identities `hes`/`hfd`.  The rule's right-hand
side, which `blockRuleEsAV_eq` and `blockRuleFdomsAV_datum` both name,
exists because the kinds cover the constructors (`hkLen`,
`checkBlockRecK_rulesLen`). -/
theorem blockRuleSpine_peel (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (p.kinds.getD c []).length = ctorsA.length)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hdnP : d.nP = p.nP)
    (hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r → d.ctorsM (p.toBlockShape.recTgtAt c) = r.2.2.2)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {j : Nat} (hj : j < blockRecNCt rs c)
    {ψ : Name → Nat} {K : Nat} {a ρ : Nat → V} {xs fs : List V}
    (hxs : xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length)
    (hsp : SpineFit (chainFrame K a ρ)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs)) :
    ∃ (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[j]? = some cA ∧ r.2.1[j]? = some rhs ∧
      (d.ctorsM (p.toBlockShape.recTgtAt c))[j]? = some cA ∧
      BlockCtorFacts mpC.base2 d p.lps (p.toBlockShape.recTgtAt c) j cA ∧
      p.toBlockShape.recTgtAt c < d.k ∧
      p.nP ≤ p.toBlockShape.rulePrefixAt c ∧
      xs.length = p.toBlockShape.rulePrefixAt c ∧ fs.length = cA.2 ∧
      ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = cA.2 ∧
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs ∧
      SpineFit ρ (d.params ψ) (xs.take d.nP) ∧
      SpineFit (consList (xs.take d.nP) ρ)
        ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []) fs ∧
      blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
        = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
            (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2) ∧
      blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
        = liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0
            ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []) := by
  -- the constructor the rule names, and its right-hand side
  have hjr : j < r.2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, r.2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  have hcj : (d.ctorsM (p.toBlockShape.recTgtAt c))[j]? = some cA := by
    rw [hctM c r hr]; exact hcA
  have hmemk : p.toBlockShape.recTgtAt c < d.k :=
    (blockRecMajor_run (V := V) hμ mpC h hmr hr (fun _ => 0)).2.1
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk j cA hcj
  obtain ⟨-, -, hcd⟩ := hcore.2.2.1 _ j cA hcj
  have hCf : cA.1.type.hasFvar = false :=
    (mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)).1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
  have hnP := TE.nP_le
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hxs' : xs.length = p.toBlockShape.rulePrefixAt c := by rw [hxs, hpl]
  have hfd := blockRuleFdomsAV_datum h hr hcA hrhs hcore hmemk hcj hnP hdnP ψ
  have hcd' := hcd
  rw [hdnP] at hcd'
  have hes : blockRuleEsAV p.toBlockShape rs mpC.base2.acval envC ψ c j
      = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
          (·.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2) := by
    rw [blockRuleEsAV_eq h hr hcA hrhs hcd' hCf hnP ψ, hdnP]
    exact congrArg (List.map _) (essOfR_fixCtorDataList_getD hcj).symm
  have hnF : ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []).length = cA.2 := by
    have hFssD : (d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []
        = ((d.dsF (p.toBlockShape.recTgtAt c) j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hcd.len ψ]
    omega
  -- the split
  obtain ⟨xs₁, fs₁, heq, h1, h2⟩ := spineFit_append_split hsp
  have hl1 : xs₁.length = xs.length := by rw [h1.length_eq, hxs]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq hl1.symm
  -- the prefix, at the base frame
  have hpre : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs := by
    rw [← blockRecPdomsK_run hμ mpC h hr ψ K, blockRecPdomsK] at h1
    exact (spineFit_liftDomsK (K := K) (a := a) (ρ := ρ) _ [] xs).mp h1
  -- the parameters
  have hps : SpineFit ρ (d.params ψ) (xs.take d.nP) := by
    have ht := spineFit_take hpre (i := d.nP) (by rw [hpl, hdnP]; exact hnP)
    have hte : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).take d.nP
        = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).take d.nP := by
      rw [blockRulePdomsAV, List.map_take, List.take_take,
        Nat.min_eq_left (by rw [hdnP]; exact hnP)]
    rw [hte] at ht
    exact (blockRecParams_run hμ mpC h hmr hr ψ ρ _).mp ht
  -- the fields
  have h2' : SpineFit (consList xs (chainFrame K a ρ))
      (liftDomsK K (p.toBlockShape.rulePrefixAt c)
        (liftDomsK (p.toBlockShape.rulePrefixAt c - d.nP) 0
          ((d.Fss (p.toBlockShape.recTgtAt c) ψ).getD j []))) fs := by
    rw [blockRecFdomsK, hpl, hfd] at h2; exact h2
  have hfb := (spineFit_liftDomsK_rule (nP := d.nP) hxs').mp h2'
  exact ⟨cA, rhs, hcA, hrhs, hcj, ⟨hfindC, hlpsC, hcd⟩, hmemk, hnP, hxs',
    by rw [hfb.length_eq, hnF], hnF, hpre, hps, hfb, hes, hfd⟩

end Peel

/-! ## 2. A spine of the recursor's binder data, from its three parts

`blockRecConclTy_run`'s assembly, as a lemma: a prefix fitting the
recursor's prefix domains, index values fitting the MEMBER's telescope
(carried to the recursor's index binders by the converse) and an
element of the member's former applied there fit the recursor's whole
binder data. -/

section Assemble

/-- **The recursor's binder data, fitted part by part.** -/
theorem blockRecSpineFit_of_parts (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) (ψ : Name → Nat) (ρ : Nat → V) {xs is : List V} {x : V}
    (hprefR : SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
      (·.2.2)).take (p.toBlockShape.rulePrefixAt c)) xs)
    (hisfit : SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (p.toBlockShape.recTgtAt c) ψ) is)
    (hx : x ∈ˢ (xs.take d.nP ++ is).foldl app
      (interp V ρ (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ))) :
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2))
      (xs ++ is ++ [x]) := by
  obtain ⟨hnPle, hmemk, hmI, hlenRds, hmajRead⟩ := blockRecMajor_run hμ mpC h hmr hr ψ
  have hlenIds := blockMembers_IdsM_length hmr hmemk ψ
  have hxlen : xs.length = p.toBlockShape.rulePrefixAt c := by
    rw [hprefR.length_eq, List.length_take, List.length_map, hlenRds]; omega
  have hislen : is.length = d.nIdxAt (p.toBlockShape.recTgtAt c) := by
    rw [hisfit.length_eq, hlenIds]
  -- THE CONVERSE: the index values fit the recursor's index binders
  have hidxR := blockRecIdxConv_run hμ mpC h hmr hr ψ ρ xs is hprefR hisfit
  rw [hlenIds] at hidxR
  -- the major
  have hmaj : x ∈ˢ interp V (consList (xs ++ is) ρ)
      (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).getD
        (p.toBlockShape.majorIdxAt c) default) := by
    have hget : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
          (·.2.2)).getD (p.toBlockShape.majorIdxAt c) default
        = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).getD
          (p.toBlockShape.majorIdxAt c) default).2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlenRds]; omega)]
      rfl
    rw [hget, hmajRead, hmI, interp_of_major_reading hxlen hislen hnPle
      (fun ρ₁ ρ₂ => acval_interp_closed mpC.base2 _ ψ ρ₁ ρ₂)]
    exact hx
  -- the whole spine fits the recursor's binder data
  have hsplitL : (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)
      = ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).take
          (p.toBlockShape.rulePrefixAt c))
        ++ ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).drop
          (p.toBlockShape.rulePrefixAt c)).take (d.nIdxAt (p.toBlockShape.recTgtAt c))))
        ++ [((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)).getD
          (p.toBlockShape.majorIdxAt c) default] := by
    have hlen : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
        (·.2.2)).length = p.toBlockShape.rulePrefixAt c + d.nIdxAt (p.toBlockShape.recTgtAt c)
          + 1 := by
      rw [List.length_map, hlenRds, hmI]
    rw [hmI]
    generalize ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2)) = L
      at hlen ⊢
    generalize p.toBlockShape.rulePrefixAt c = a at hlen ⊢
    generalize d.nIdxAt (p.toBlockShape.recTgtAt c) = b at hlen ⊢
    rw [← List.take_add]
    have hd : L.drop (a + b) = [L.getD (a + b) default] := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    rw [← hd, List.take_append_drop]
  rw [hsplitL]
  exact SpineFit.append (SpineFit.append hprefR hidxR) ⟨hmaj, trivial⟩

end Assemble

/-! ## 3. `hrule`, at every chain frame -/

section Rule

/-- **The kit arms' `hrule`, at ANY chain frame** — nothing here reads
the candidate `a`.  The peel (§1) hands the base-frame prefix, the
parameter fit and the field spine at the parameter frame; the index
values fit the member's telescope (`resIdxFit`); the fired spine is the
block's injection (`blockRecMkK_value`) of a `ChainFit` spine
(`blockRecCtorFitsFrom_of`, `blockRecCtorIdx`), hence in the carrier;
§2 assembles. -/
theorem blockKitRule_run (hμ : μ.verifiedChecks = true)
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
    (ψ : Name → Nat) (K : Nat) (a ρ : Nat → V) :
    ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ xs fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame K a ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2))
          (xs ++ ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
              (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
            ++ [interp V (consList (xs ++ fs) (chainFrame K a ρ))
              (blockRecMkK K mpC.base2.acval envC p.toBlockShape rs ψ c j)])) := by
  intro c hc j hj xs fs hxs hsp
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfs, hnF, hpre, hps, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel hμ h hkLen hcore hmr hdnP hctM hr hj hxs hsp
  have hmN : p.toBlockShape.recTgtAt c < d.N := Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hjl : j < (d.ctorsM (p.toBlockShape.recTgtAt c)).length :=
    (List.getElem?_eq_some_iff.mp hcj).1
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [hfd, liftDomsK_length, hnF]
  have hasLen : (xs.take d.nP).length = d.nP := by
    rw [List.length_take, hxs']; rw [hdnP]; exact Nat.min_eq_left hnP
  have hsat : Sat V (d.params ψ).reverse (consList (xs.take d.nP) ρ) := d.satOfSpine hps
  -- the index values fit the member's own telescope
  have hres := hM.resIdxFit ψ _ hsat _ hmN j hjl fs hfb
  have hEsK : blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j
      = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map fun e =>
          (e.liftN (p.toBlockShape.rulePrefixAt c - d.nP) cA.2).liftN K
            (p.toBlockShape.rulePrefixAt c + cA.2) := by
    rw [blockRecEsK, hes, List.map_map, hpl, hfl]
    rfl
  have hmapEq : (blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
        (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
      = ((d.Ess (p.toBlockShape.recTgtAt c) ψ).getD j []).map
          (interp V (consList fs (consList (xs.take d.nP) ρ))) := by
    rw [hEsK, List.map_map]
    exact List.map_congr_left fun e _ => interp_liftN_rule (nP := d.nP) hxs' hfs e
  have hisfit : SpineFit (consList (xs.take d.nP) ρ) (d.IdsM (p.toBlockShape.recTgtAt c) ψ)
      ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
        (interp V (consList (xs ++ fs) (chainFrame K a ρ)))) := by
    rw [hmapEq]; exact hres
  -- the index tuple lies in the member's index set
  have htup : d.tup ψ (p.toBlockShape.recTgtAt c)
        ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
          (interp V (consList (xs ++ fs) (chainFrame K a ρ))))
      ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (p.toBlockShape.recTgtAt c) :=
    tupW_mem hisfit
  -- the constructor's spine fits at the carrier
  have hspK : SpineFit (chainFrame K a ρ)
      (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [blockRecPdomsK_run hμ mpC h hr ψ K]; exact hsp
  have hxsK : xs.length
      = (blockRecPdomsK K mpC.base2.acval envC p.toBlockShape rs ψ c).length := by
    rw [blockRecPdomsK_run hμ mpC h hr ψ K]; exact hxs
  have hfit : d.ChainFit ψ (consList (xs.take d.nP) ρ)
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
        (d.Φ ψ (consList (xs.take d.nP) ρ)))
      (d.tup ψ (p.toBlockShape.recTgtAt c)
        ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
          (interp V (consList (xs ++ fs) (chainFrame K a ρ)))))
      (p.toBlockShape.recTgtAt c) j fs :=
    ⟨blockRecCtorFitsFrom_of (mem := p.toBlockShape.recTgtAt) hM hμ h hr hcj hcf hfd hasLen
      hps (fun l _ => by rw [← hN.2.2.2]; exact hN.2.1 _ j l) hmN hjl htup
      (lfpTuple_mem _ _ _ _) hxsK hspK,
     blockRecCtorIdx (mem := p.toBlockShape.recTgtAt) hM hes hpl hfl hxs' hfs hmN hjl hps hfb⟩
  -- the fired spine is the block's injection
  have hmk : interp V (consList (xs ++ fs) (chainFrame K a ρ))
        (blockRecMkK K mpC.base2.acval envC p.toBlockShape rs ψ c j)
      = d.inj ψ (p.toBlockShape.recTgtAt c) j fs :=
    blockRecMkK_value (mem := p.toBlockShape.recTgtAt) hM h hr hcA hrhs hcf.1
      (by rw [← hcf.2.1]; rfl) hnP hmN hcj ψ hxs' hfs
      (by rw [hpl, hfl, hxs', hfs]) (by rw [← hdnP]; exact hps) (by rw [← hdnP]; exact hfb)
  -- the injection lies in the carrier: the fibre, then closure
  obtain ⟨hmono, -, hcl⟩ := hM.functor ψ _ hsat
  have hin : d.inj ψ (p.toBlockShape.recTgtAt c) j fs
      ∈ˢ app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) ρ))
          (d.Φ ψ (consList (xs.take d.nP) ρ)) (p.toBlockShape.recTgtAt c))
        (d.tup ψ (p.toBlockShape.recTgtAt c)
          ((blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame K a ρ))))) :=
    lfpTuple_closed hcl hmono _ hmN _ htup _
      ((hM.fibre ψ _ hsat _ (lfpTuple_mem _ _ _ _) _ hmN _ htup _).mpr ⟨j, fs, hjl, hfit, rfl⟩)
  -- the carrier is the member's former applied
  have hx : d.inj ψ (p.toBlockShape.recTgtAt c) j fs
      ∈ˢ (xs.take d.nP ++ (blockRecEsK K mpC.base2.acval envC p.toBlockShape rs ψ c j).map
          (interp V (consList (xs ++ fs) (chainFrame K a ρ)))).foldl app
        (interp V ρ (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c)) ψ)) := by
    rw [hM.leaf _ hmemk ψ ρ (xs.take d.nP) _ hps hisfit]
    exact hin
  -- the prefix fits the recursor's own prefix domains
  have hprefR : SpineFit ρ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map
      (·.2.2)).take (p.toBlockShape.rulePrefixAt c)) xs := by
    rw [← List.map_take]; exact hpre
  rw [hmk, ← List.append_assoc]
  exact blockRecSpineFit_of_parts hμ h hmr hr ψ ρ hprefR hisfit hx

end Rule

/-! ## 4. `hrule` at the arms' own data

`BlockWfOwed`'s and `BlockSqOwed`'s `hrule` rows (`BlockRecPreHpre.lean`
§4), verbatim: §3 at the chain frame of the ONE datum each arm builds
(`blockWfCand`, `blockSqCand`, §19a of `BlockRecPreRun`).  The level
`ℓ`, the residues `Rb0`, the `ih` values `ihv` and (SQ) the source
lists `srcs` are free — nothing reads them — so each statement is the
row at whatever witnesses the seam chooses. -/

section Arms

/-- **REGIME WF's `hrule`**, in `BlockWfOwed`'s spelling. -/
theorem blockWfRule_run (hμ : μ.verifiedChecks = true)
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
    (ψ : Name → Nat) (ρ : Nat → V) (ℓ : Nat) (Rb0 : Nat → Nat → AnnotTerm)
    (ihv : List V → Nat → Nat → List V → V → List V) :
    ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2))
          (xs ++ ((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ)))
            ++ [interp V (consList (xs ++ fs) (chainFrame rs.length (blockWfCand ℓ rs.length p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) Rb0 ihv) ρ))
              (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)])) :=
  blockKitRule_run hμ h hkLen hcore hmr hM hN hdnP hctM ψ rs.length _ ρ

/-- **REGIME SQ's `hrule`**, in `BlockSqOwed`'s spelling (at any source
lists `srcs`; the seam's are `blockSqSrcs d ψ`).  `c < 1` reaches the
family's first recursor through `0 < rs.length` (`blockRecLen_run`). -/
theorem blockSqRule_run (hμ : μ.verifiedChecks = true)
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
    (h0 : 0 < rs.length)
    (ψ : Name → Nat) (ρ : Nat → V) (ℓ : Nat) (srcs : Nat → List (Option Nat))
    (Rb0 : Nat → Nat → AnnotTerm) (ihv : List V → Nat → Nat → List V → V → List V) :
    ∀ c, c < 1 → ∀ j, j < blockRecNCt rs c →
        ∀ xs fs : List V, xs.length = (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length →
        SpineFit (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ)
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) ++ (blockRecFdomsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)) (xs ++ fs) →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c).map (·.2.2))
          (xs ++ ((blockRecEsK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j).map
            (interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ)))
            ++ [interp V (consList (xs ++ fs) (chainFrame 1 (blockSqCand ℓ p.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ) d ψ ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ)
            p.toBlockShape.recTgtAt (blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ) srcs Rb0 ihv) ρ))
              (blockRecMkK 1 mpC.base2.acval envC p.toBlockShape rs ψ c j)])) :=
  fun c hc => blockKitRule_run hμ h hkLen hcore hmr hM hN hdnP hctM ψ 1 _ ρ c
    (Nat.lt_of_lt_of_le hc h0)

end Arms

end ConLeche.Model
