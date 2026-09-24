module

import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.BlockLfpHoles

public section

/-!
# The grading bundle's `hlhs` and the `ih` terms' grading

`BlockGradeOwed` (`BlockRecPreHpre.lean` §4) owes, besides the
certificates, the rule frame's grading (G) and the typed tuple's `ih`
fit (F) (`blockRuleGrading_run`, `blockIhFitTyped_run`) — two rows about a TYPED tuple `as`
(each component in its recursor type's reading) and a rule frame `ys`
fitting the rule's prefix and field domains at `consList as ρ`:

* `hlhs`: the ι equation's LEFT-hand side — the recursor variable of
  class `c` applied to the rule's spine (the prefix, the constructor's
  result index readings and the fired constructor application) — is
  graded;
* `hihsWd`'s first half: every pinned `ih` term (`blockRuleIhsRunAV`,
  one curried call per key) is graded.

**The frame.**  `consList as ρ` IS the chain frame of the tuple
(`consList_eq_chainFrame`), so every statement here is at a chain frame
`chainFrame K a ρ` with `a c = as.getD c pt`, and the rule's own
components are lifted past it (§20 of `BlockRecPreRun`).

* `hlhs` is an application chain along the recursor's own type:
  `blockKitRule_run` (`BlockKitRuleRun.lean`) fits the spine to the recursor's binder
  data at ANY chain frame; the head reads to the tuple's component,
  which inhabits the type; the arguments are graded — the prefix
  variables trivially, the index readings off the constructor's stored
  type (its `okTy` body at the constructor's frame), the fired
  constructor application off its own stored type (`mem_type`) along the
  constructor's binder data.
* the `ih` terms are λ-towers over the field's MOVED telescope
  (`mkLamsC_wellDenoted`), whose leaf is the callee component applied
  along the call's spine: graded as an application chain along the
  CALLEE's type, at the fit `blockIhCallFit_of` exports, landing in the
  call's peeled conclusion `CihR` (`blockRuleIhKey_run`).
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

/-! ## 1. Transports and the constructor's two graded readings -/

section CtorReadings

/-- **The rule's double lift, graded** — `interp_liftN_rule`'s
`WellDenotedV` twin: a form of the constructor's field frame, lifted
past the rule prefix's non-parameter binders and then past the `K`
chain binders, is graded at the chain frame exactly when it is at the
constructor's frame. -/
theorem wellDenotedV_liftN_rule {K nP rP nF : Nat} {a ρ : Nat → V} {xs fs : List V}
    (hxs : xs.length = rP) (hfs : fs.length = nF) (e : AnnotTerm) :
    WellDenotedV V (consList (xs ++ fs) (chainFrame K a ρ))
        ((e.liftN (rP - nP) nF).liftN K (rP + nF))
      ↔ WellDenotedV V (consList fs (consList (xs.take nP) ρ)) e := by
  have hlen : (xs ++ fs).length = rP + nF := by rw [List.length_append, hxs, hfs]
  rw [WellDenotedV_liftN, ← hlen, chainFrame,
    shiftE_consList_ih (locals := xs ++ fs) (ihvals := (List.range K).map a) rfl (by simp),
    WellDenotedV_liftN, consList_append]
  have hsplit : consList xs ρ = consList (xs.drop nP) (consList (xs.take nP) ρ) := by
    rw [← consList_append, List.take_append_drop]
  have hdrop : (xs.drop nP).length = rP - nP := by rw [List.length_drop, hxs]
  rw [hsplit, ← hdrop, ← hfs, shiftE_consList_ih rfl rfl]

/-- **The chain lift, graded**: a form lifted past the `K` chain binders
at the frame's own depth is graded at the chain frame exactly when it
is at the base frame. -/
theorem wellDenotedV_liftN_chainFrame {K : Nat} {a ρ : Nat → V} (ws : List V)
    (e : AnnotTerm) :
    WellDenotedV V (consList ws (chainFrame K a ρ)) (e.liftN K ws.length)
      ↔ WellDenotedV V (consList ws ρ) e := by
  rw [WellDenotedV_liftN, chainFrame,
    shiftE_consList_ih (locals := ws) (ihvals := (List.range K).map a) rfl (by simp)]

/-- **The constructor's index readings are graded** at its own field
frame: the stored type's reading is graded at every valuation
(`okTy`), so its body — the member at the parameters and the index
readings — is graded at a spine fitting its binder data, and so is each
argument. -/
theorem blockCtorEs_wdV {lps : List Name} {mm j : Nat} {cA : ConstantVal × Nat}
    (hcf : BlockCtorFacts mpC.base2 d lps mm j cA)
    (hcj : (d.ctorsM mm)[j]? = some cA) {ψ : Name → Nat} {ρ : Nat → V} {ps fs : List V}
    (hpc : SpineFit ρ (((d.dsF mm j ψ).take d.nP).map (·.2.2)) ps)
    (hfs : SpineFit (consList ps ρ) ((d.Fss mm ψ).getD j []) fs) :
    ∀ E ∈ (d.Ess mm ψ).getD j [], WellDenotedV V (consList fs (consList ps ρ)) E := by
  intro E hE
  have hcd := hcf.2.2
  have hFssD : (d.Fss mm ψ).getD j [] = ((d.dsF mm j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hEssD : (d.Ess mm ψ).getD j [] = d.esF mm j ψ := essOfR_fixCtorDataList_getD hcj
  rw [hFssD] at hfs
  rw [hEssD] at hE
  have hfit : SpineFit ρ ((d.dsF mm j ψ).map (·.2.2)) (ps ++ fs) := by
    rw [← List.take_append_drop d.nP (d.dsF mm j ψ), List.map_append]
    exact SpineFit.append hpc hfs
  have hok := hcd.okTy ψ ρ
  have hb : WellDenotedV V (consList (ps ++ fs) ρ)
      (ctorBodyAVI mpC.base2 (d.memberName mm) d.nP cA.2 ψ (d.esF mm j ψ)) :=
    ⟨(WellDenoted_mkPisAV_inv hok.1).2 _ hfit, (AnnotValid_mkPisAV_inv hok.2).2 _ hfit⟩
  rw [ctorBodyAVI, consList_append] at hb
  exact WellDenotedV_mkAppN_args _ hb E (List.mem_append_right _ hE)

/-- **The fired constructor application is graded** at the rule's base
frame: the constructor's leaf inhabits its stored type's reading
(`mem_type`), which is graded (`okTy`), and the frame's parameter and
field values fit that type's binder data, so the application chain is
graded (`wellDenotedV_mkAppN_of_fit`). -/
theorem blockRuleMkAV_wdV
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    {c : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[c]? = some r) {j : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[j]? = some cA)
    {rhs : Expr} (hrhs : r.2.1[j]? = some rhs) {mm : Nat}
    (hcf : BlockCtorFacts mpC.base2 d p.lps mm j cA)
    (hcj : (d.ctorsM mm)[j]? = some cA) (hdnP : d.nP = p.nP)
    (hnP : p.nP ≤ p.toBlockShape.rulePrefixAt c) {ψ : Name → Nat} {ρ : Nat → V}
    {xs fs : List V} (hxs : xs.length = p.toBlockShape.rulePrefixAt c)
    (hfsl : fs.length = cA.2)
    (hpc : SpineFit ρ (((d.dsF mm j ψ).take d.nP).map (·.2.2)) (xs.take p.nP))
    (hfs : SpineFit (consList (xs.take p.nP) ρ) ((d.Fss mm ψ).getD j []) fs) :
    WellDenotedV V (consList (xs ++ fs) ρ)
      (blockRuleMkAV p.toBlockShape rs mpC.base2.acval envC ψ c j) := by
  have hcd := hcf.2.2
  have hlps : (ConstantInfo.ctorInfo cA.1 d.nP cA.2).toConstantVal.levelParams = p.lps :=
    hcf.2.1
  rw [blockRuleMkAV_eq h hr hcA hrhs hcf.1 hlps hnP ψ, Level.substFn_param_self]
  have hlenL : (xs ++ fs).length = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [List.length_append, hxs, hfsl]
  -- the arguments read the frame's parameters and fields
  have hvals : (paramBvarsAt p.nP (p.toBlockShape.rulePrefixAt c + cA.2)
        ++ (List.range cA.2).map fun k =>
          AnnotTerm.bvar (p.toBlockShape.rulePrefixAt c + cA.2 - 1
            - (p.toBlockShape.rulePrefixAt c + k))).map (interp V (consList (xs ++ fs) ρ))
      = xs.take p.nP ++ fs := by
    rw [List.map_append, map_bvarAt_take (hD := by rw [hlenL]) (by rw [hlenL]; omega),
      map_fieldBvars hxs hfsl, List.take_append_of_le_length (by omega)]
  -- the spine fits the constructor's binder data
  have hFssD : (d.Fss mm ψ).getD j [] = ((d.dsF mm j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  rw [hFssD, ← hdnP] at hfs
  have hvals' : (paramBvarsAt p.nP (p.toBlockShape.rulePrefixAt c + cA.2)
        ++ (List.range cA.2).map fun k =>
          AnnotTerm.bvar (p.toBlockShape.rulePrefixAt c + cA.2 - 1
            - (p.toBlockShape.rulePrefixAt c + k))).map (interp V (consList (xs ++ fs) ρ))
      = xs.take d.nP ++ fs := by rw [hdnP]; exact hvals
  have hfit : SpineFit ρ ((d.dsF mm j ψ).map (·.2.2)) (xs.take d.nP ++ fs) := by
    rw [← List.take_append_drop d.nP (d.dsF mm j ψ), List.map_append]
    exact SpineFit.append (by rw [← hdnP] at hpc; exact hpc) hfs
  have hTF := teleFit_mkPisAV_of_spineFit
    (B := ctorBodyAVI mpC.base2 (d.memberName mm) d.nP cA.2 ψ (d.esF mm j ψ)) hfit
  rw [← hvals'] at hTF
  -- the leaf inhabits the stored type's reading
  have hmemC : ConstantInfo.ctorInfo cA.1 d.nP cA.2 ∈ envC.consts :=
    List.mem_of_find?_eq_some hcf.1
  have hmem : interp V (consList (xs ++ fs) ρ) (mpC.base2.acval cA.1.name ψ)
      ∈ˢ interp V ρ (mkPisAV (d.dsF mm j ψ)
        (ctorBodyAVI mpC.base2 (d.memberName mm) d.nP cA.2 ψ (d.esF mm j ψ))) := by
    rw [acval_interp_closedC mpC.base2 cA.1.name ψ _ ρ]
    exact mpC.mem_type _ hmemC ψ _ (hcd.read ψ) ρ
  refine (Rules.wellDenotedV_mkAppN_of_fit _ (hcd.okTy ψ ρ)
    ⟨mpC.base2.acval_wellDenoted _ _ _, mpC.acval_validV _ _ _⟩ (fun x hx => ?_) hmem hTF).1
  rcases List.mem_append.mp hx with hx | hx
  · simp only [paramBvarsAt, List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact ⟨trivial, trivial⟩
  · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
    exact ⟨trivial, trivial⟩

end CtorReadings

/-! ## 2. `hlhs` — the ι equation's left-hand side is graded -/

section Lhs

/-- **`BlockGradeOwed`'s `hlhs`, at the run** — its row verbatim.  The
typed tuple's frame is the chain frame (`consList_eq_chainFrame`), at
which `blockKitRule_run` fits the rule's fired spine to the
recursor's binder data; the head reads to the tuple's component, which
inhabits the recursor type's reading; the arguments are graded (§1). -/
theorem blockGradeLhs_run
    (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) :
    (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ ys : List V,
        SpineFit (consList as ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) ys →
        WellDenoted V (consList ys (consList as ρ))
          (AnnotTerm.mkAppN
            (.bvar
              ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
                + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
                + (rs.length - 1 - c)))
            (prefVarsAV (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
                (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
              ++ blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j
              ++ [blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j]))) := by
  intro ψ ρ as hlen htyp c hc j hj ys hys
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hctM : ∀ (c : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[c]? = some r →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
        (p.toBlockShape.recTgtAt c) = r.2.2.2 := by
    intro c r hr
    obtain ⟨-, -, hctA, -⟩ := recStage_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hch := consList_eq_chainFrame (V := V) hlen ρ
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  have hxl := hxs.length_eq
  have hsp : SpineFit (chainFrame rs.length (fun c => as.getD c pt) ρ)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [← hch]; exact hys
  have hfit := blockKitRule_run hμ h hcore hmr hM rfl hctM ψ rs.length
    (fun c => as.getD c pt) ρ c hc j hj xs fs hxl hsp
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfsl, -, hpre, -, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel hμ h hcore hmr rfl hctM hr hj hxl hsp
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      = p.toBlockShape.rulePrefixAt c := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfl : (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [hfd, liftDomsK_length]
    have := hfb.length_eq
    rw [← this, hfsl]
  have hflK : (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
      = fs.length := by
    rw [blockRecFdomsK, liftDomsK_length, hfl, hfsl]
  -- the constructor's parameter fit (the hop through the member's former)
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hcvTa := TE.hcvTa
  obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ TE.cvTa hcvTa
  have hframes := (hS.frames _ hmemk j cA hcj).1 ψ
  have hcd := hcf.2.2
  have hpc := blockRuleParamFit_run hμ mpC h hr ψ hcvTa hfT hFD (Nat.le_add_right _ _)
    (hcd.len ψ) hframes (spineFit_take_any hpre p.nP)
  -- the frame, the head, the spine's values
  rw [hch]
  have hpv : (prefVarsAV (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length).map
        (interp V (consList (xs ++ fs) (chainFrame rs.length (fun c => as.getD c pt) ρ)))
      = xs := by
    rw [hflK]; exact interp_prefVarsAV hxl
  have hvals : (prefVarsAV (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
          (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        ++ blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j
        ++ [blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j]).map
        (interp V (consList (xs ++ fs) (chainFrame rs.length (fun c => as.getD c pt) ρ)))
      = xs ++ ((blockRecEsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).map
          (interp V (consList (xs ++ fs) (chainFrame rs.length (fun c => as.getD c pt) ρ)))
        ++ [interp V (consList (xs ++ fs) (chainFrame rs.length (fun c => as.getD c pt) ρ))
          (blockRecMkK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j)]) := by
    rw [List.map_append, List.map_append, hpv, List.map_cons, List.map_nil, List.append_assoc]
  have hhead : interp V (consList (xs ++ fs) (chainFrame rs.length (fun c => as.getD c pt) ρ))
      (.bvar ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        + (rs.length - 1 - c))) = as.getD c pt := by
    show consList (xs ++ fs) _ _ = _
    rw [show (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        + (rs.length - 1 - c) = (rs.length - 1 - c) + (xs ++ fs).length from by
          rw [List.length_append, hxl, hflK]; omega,
      consList_apply_add, chainFrame_apply hc]
  -- the recursor's type, fitted along the spine
  obtain ⟨-, -, -, -, hTyE, -, -, -, -, hwdTy⟩ := recStage_tyPis hμ mpC h hr ψ
  have hTF := teleFit_mkPisAV_of_spineFit
    (B := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c) hfit
  rw [← hTyE, ← hvals] at hTF
  have hmem : interp V (consList (xs ++ fs) (chainFrame rs.length (fun c => as.getD c pt) ρ))
      (.bvar ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        + (rs.length - 1 - c))) ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c) := by
    rw [hhead]; exact htyp c hc
  have hlenL : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
      + (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j).length
      = (xs ++ fs).length := by
    rw [List.length_append, hxl, hfl, hfsl]
  refine (Rules.wellDenotedV_mkAppN_of_fit _
    (f := .bvar ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c).length
        + (blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j).length
        + (rs.length - 1 - c))) (hwdTy ρ) ⟨trivial, trivial⟩ (fun x hx => ?_) hmem hTF).1.1
  rcases List.mem_append.mp hx with hx | hx
  · rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      exact ⟨trivial, trivial⟩
    · -- an index reading, lifted twice
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      rw [hes] at he
      obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he
      rw [hpl, hfl]
      exact (wellDenotedV_liftN_rule hxs' hfsl E).mpr (blockCtorEs_wdV hcf hcj hpc hfb E hE)
  · -- the fired constructor application, lifted past the chain
    rw [List.mem_singleton] at hx
    rw [hx, blockRecMkK, hlenL, wellDenotedV_liftN_chainFrame]
    exact blockRuleMkAV_wdV h hr hcA hrhs hcf hcj rfl hnP hxs' hfsl hpc hfb

end Lhs

/-! ## 3. The `ih` terms are graded -/

section Ihs

end Ihs

end ConLeche.Model
