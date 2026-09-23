module

public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockKitRuleRun
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Rules.InferSoundKit

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
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
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
    obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hch := consList_eq_chainFrame (V := V) hlen ρ
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  have hxl := hxs.length_eq
  have hsp : SpineFit (chainFrame rs.length (fun c => as.getD c pt) ρ)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) (xs ++ fs) := by
    rw [← hch]; exact hys
  have hfit := blockKitRule_run hμ h hkLen hcore hmr hM hN rfl hctM ψ rs.length
    (fun c => as.getD c pt) ρ c hc j hj xs fs hxl hsp
  obtain ⟨cA, rhs, hcA, hrhs, hcj, hcf, hmemk, hnP, hxs', hfsl, -, hpre, -, hfb, hes, hfd⟩ :=
    blockRuleSpine_peel hμ h hkLen hcore hmr rfl hctM hr hj hxl hsp
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
  obtain ⟨_, cvTa, _, _, _, _, _, -, hcvTa, -, -⟩ := checkBlockRecK_tyMajor h hr
  obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ cvTa hcvTa
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
  obtain ⟨-, -, -, -, hTyE, -, -, -, -, hwdTy⟩ := checkBlockRecK_tyPis hμ mpC h hr ψ
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

/-- **`UnderTowerOk` from a spine-indexed grading**: the tower's domains
hereditarily graded (`FieldsOkB 0`) and the three leaf facts at every
fitting spine. -/
theorem underTowerOk_of_fieldsOkB {m : Nat} {b T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {σ : Nat → V},
      FieldsOkB 0 σ (ds.map (·.2.2)) →
      (∀ bs : List V, SpineFit σ (ds.map (·.2.2)) bs →
        WellDenoted V (consList bs σ) b ∧
          interp V (consList bs σ) b ∈ˢ interp V (consList bs σ) T ∧
          (m = 0 → interp V (consList bs σ) T ∈ˢ (univZero : V))) →
      UnderTowerOk m σ b T ds
  | [], σ, _, hB => by
    have h := hB [] trivial
    rw [consList_nil] at h
    exact h
  | d :: ds, σ, hF, hB => by
    refine ⟨hF.1, fun a ha => underTowerOk_of_fieldsOkB (hF.2.2 a ha) fun bs hbs => ?_⟩
    have h := hB (a :: bs) ⟨ha, hbs⟩
    rwa [consList_cons] at h

/-- **`BlockGradeOwed`'s `ih` terms' grading (`hihsWd`'s first half), at
the run** — its row verbatim at the pinned `ihs := blockRuleIhsRunAV`.

Each term is the curried call of the typed tuple's callee component
(`ihFunAV`): a constant-bit λ-tower (`mkLamsC_wellDenoted`) over the
field's MOVED telescope, whose domains are graded by the field's own
telescope (`blockRuleIhTele_graded_of_ctorTower`) carried to the rule's
frame (`fieldsWD_ihTeleAtGo_rule`), and whose leaf — the component
applied along the call's spine — is graded as an application chain
along the CALLEE's type (the call fit `blockIhCallFit_of`), lands in the
call's peeled conclusion and makes it a truth value at a `Prop`
elimination (`blockRuleIhKey_run`). -/
theorem blockGradeIhs_run
    (hμ : μ.verifiedChecks = true)
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
    (∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ as : List V, as.length = rs.length →
      (∀ c, c < rs.length →
        as.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ c)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c →
      ∀ ys : List V,
        SpineFit (consList as ρ)
          (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
            ++ blockRecFdomsK rs.length mpC.base2.acval envC p.toBlockShape rs ψ c j) ys →
        ∀ v ∈ blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j,
          WellDenoted V (consList ys (consList as ρ)) v) := by
  intro ψ ρ as hlen htyp c hc j hj ys hys v hv
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  obtain ⟨_, _, _, _, _, _, _, -, -, hnP, -⟩ := checkBlockRecK_tyMajor h hr
  have hkey := fun q (hq : q < (blockRuleFrameAt p rs c j).nR) =>
    blockRuleIhKey_run hμ h hkLen hdR hN hS hcore hmr hM hr hcA ψ hq
  obtain ⟨env₀, pk, uOfD, ppsOf, hdE⟩ := hdR
  -- the frame: the typed tuple's chain frame, the rule's values fitting at it
  have hch := consList_eq_chainFrame (V := V) hlen ρ
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  have hxl0 := hxs.length_eq
  have hxsρ : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c) xs := by
    rw [hch, ← blockRecPdomsK_run hμ mpC h hr ψ rs.length, blockRecPdomsK] at hxs
    exact (spineFit_liftDomsK (K := rs.length) (ρ := ρ) _ [] xs).mp hxs
  have hfsρ : SpineFit (consList xs ρ)
      (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) fs := by
    rw [hch, blockRecFdomsK, ← hxl0] at hfs
    exact (spineFit_liftDomsK (K := rs.length) (ρ := ρ) _ xs fs).mp hfs
  have hσfit := spineFit_frame_of_bounded (σ' := consList as ρ)
    (blockRuleDoms_bounded_at hμ h (hdE ▸ hcore) ψ c rs[c] hr j cA rhs hcA hrhs)
    (SpineFit.append hxsρ hfsρ)
  obtain ⟨xs', fs', heq, hxsσ, hfsσ⟩ := spineFit_append_split hσfit
  obtain ⟨hx1, hf1⟩ := List.append_inj heq (by rw [hxsσ.length_eq, hxl0])
  rw [← hx1] at hxsσ hfsσ
  rw [← hf1] at hfsσ
  -- the key, at the tuple's frame
  have hqR : ∀ q, q < (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).length →
      q < (blockRuleFrameAt p rs c j).nR := by
    intro q hq; rw [blockRuleIhsRunAV, blockRuleIhsAV_length] at hq; exact hq
  obtain ⟨q, hq, rfl⟩ := List.mem_iff_getElem.mp hv
  obtain ⟨fi, c', CihR, -, hc'K, hfiC, -, -, hihsGet, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcallF⟩ := hkey q (hqR q hq)
  obtain ⟨hxlen, hfsl, ⟨hFok, hVok⟩, hconv, hcall⟩ := hcallF (consList as ρ) xs fs hxsσ hfsσ
  have hlenps : (xs.take p.nP).length = p.nP := by rw [List.length_take, hxlen]; omega
  have hxl : xs.length = (xs.take p.nP).length + (p.toBlockShape.rulePrefixAt c - p.nP) := by
    rw [hlenps, hxlen]; omega
  have htake : xs.take (xs.take p.nP).length = xs.take p.nP := by rw [hlenps]
  have hvq : (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j)[q]
      = (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).getD q default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]; rfl
  rw [hvq, hihsGet, ihFunAV]
  have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'K
  -- the callee's type, closed, and its binder data
  obtain ⟨-, -, -, hreadT, hTyE, -, -, -, -, hwdTy⟩ :=
    checkBlockRecK_tyPis hμ mpC h hr' ψ
  obtain ⟨hTf, -, -, hTb, -⟩ := ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')
  have hTcl := denoteMeta_closed mpC.base2.acval_erase mpC.base2.cval_closed hTf hTb hreadT
  have hRmem : as.getD c' pt ∈ˢ interp V (consList as ρ)
      (blockRecTyAV mpC.base2.acval envC rs ψ c') := by
    have hq := interp_liftN_ihvals (V := V) (ihvals := as) (σ := ρ)
      (blockRecTyAV mpC.base2.acval envC rs ψ c')
    rw [hTcl] at hq
    rw [hq]
    exact htyp c' hc'K
  -- the telescope's domains, graded at the rule's frame
  have hmv := fieldsWD_ihTeleAtGo_rule (ρ := consList as ρ) (i := fi) hxl htake hfsl
    (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw)
      ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi [])) []
    (by rw [rebit_map_dom, consList_nil]; exact hFok)
    (by rw [rebit_map_dom, consList_nil]; exact hVok)
  rw [List.length_nil, consList_nil, ← ihTeleAtR] at hmv
  refine mkLamsC_wellDenoted (T := CihR) (fun dd hdd => ?_)
    (underTowerOk_of_fieldsOkB hmv.1 fun bs hbs => ?_)
  · obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hdd
    rw [he, mem_rebit hd']
    exact (pwBit_zeronessOf ψ _).symm
  -- the leaf, at a spine of the moved telescope
  have hbsC := hconv bs hbs
  have hbl : bs.length = ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length := by
    rw [hbsC.length_eq, List.length_map]
  obtain ⟨-, H0, VAL, hfitB, hmk, hes, hEsWd, hFapWd⟩ := hcall bs hbsC
  have hR : consList as ρ (rs.length - 1 - c') = as.getD c' pt := by
    rw [consList_getD_of_lt _ _ _ (by omega), hlen,
      show rs.length - 1 - (rs.length - 1 - c') = c' from by omega]
  have hbl' : bs.length = (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
      (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw)
        ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []))).length := by
    rw [ihTeleAtR_length, rebit_length, hbl]
  refine ⟨?_, ?_, fun h0 => H0 ((pwBit_zeronessOf ψ _).mpr h0)⟩
  · -- graded: an application chain along the callee's type
    have hpv : (prefVarsAV (p.toBlockShape.rulePrefixAt c)
        (cA.2 + (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
          (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw)
            ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []))).length)).map
        (interp V (consList bs (consList (xs ++ fs) (consList as ρ)))) = xs := by
      have hq := interp_prefVarsAV (V := V) (rP := p.toBlockShape.rulePrefixAt c) (xs := xs)
        (bs := fs ++ bs) (ρ := consList as ρ) hxlen
      rw [List.length_append, hfsl, hbl'] at hq
      simp only [consList_append] at hq ⊢
      exact hq
    have hvals : (prefVarsAV (p.toBlockShape.rulePrefixAt c)
          (cA.2 + (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
            (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw)
              ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []))).length)
        ++ ((d.eissF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).map
          (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
            ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length)
        ++ [AnnotTerm.mkAppN
            (.bvar (cA.2 - 1 - fi + ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length))
            (teleVarsAV ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length)]).map
        (interp V (consList bs (consList (xs ++ fs) (consList as ρ))))
      = xs ++ (((d.eissF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).map
          (interp V (consList bs (consList (fs.take fi) (consList (xs.take p.nP)
            (consList as ρ)))))
          ++ [bs.foldl SetTheory.app (fs.getD fi pt)]) := by
      rw [List.map_append, List.map_append, hpv, hes, List.map_cons, List.map_nil, hmk,
        List.append_assoc]
    have hTF := teleFit_mkPisAV_of_spineFit
      (B := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c') hfitB
    rw [← hTyE, ← hvals] at hTF
    have hhead : interp V (consList bs (consList (xs ++ fs) (consList as ρ)))
        (.bvar ((ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
          (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw)
            ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []))).length
          + cA.2 + p.toBlockShape.rulePrefixAt c + (rs.length - 1 - c')))
        = as.getD c' pt := by
      show consList bs (consList (xs ++ fs) (consList as ρ)) _ = _
      rw [← consList_append, ← hbl',
        show bs.length + cA.2 + p.toBlockShape.rulePrefixAt c + (rs.length - 1 - c')
          = (rs.length - 1 - c') + (xs ++ fs ++ bs).length from by
            rw [List.length_append, List.length_append, hxlen, hfsl]; omega,
        consList_apply_add, hR]
    have hmem : interp V (consList bs (consList (xs ++ fs) (consList as ρ)))
        (.bvar ((ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
          (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw)
            ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []))).length
          + cA.2 + p.toBlockShape.rulePrefixAt c + (rs.length - 1 - c')))
        ∈ˢ interp V (consList as ρ) (blockRecTyAV mpC.base2.acval envC rs ψ c') := by
      rw [hhead]; exact hRmem
    refine (Rules.wellDenotedV_mkAppN_of_fit _
      (f := .bvar ((ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
          (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw)
            ((d.tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []))).length
          + cA.2 + p.toBlockShape.rulePrefixAt c + (rs.length - 1 - c')))
      (hwdTy _) ⟨trivial, trivial⟩ (fun x hx => ?_) hmem hTF).1.1
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
        exact ⟨trivial, trivial⟩
      · exact hEsWd x hx
    · rw [List.mem_singleton] at hx
      subst hx
      exact hFapWd
  · -- the value lands in the call's peeled conclusion
    rw [interp_ihFunAV_body (V := V) (K := rs.length) hR hxlen hfsl hbl']
    exact VAL _ hRmem

end Ihs

end ConLeche.Model
