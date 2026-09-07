import Lech.SetP.Direct.DirectRecLawCoreP

/-!
# The recursor rule's law (task #175 W4c, P3 module 6, part 19; S2)

`recRuleLaw`: the fired-iota contract `RecRuleLawP` of the direct
block's single (plain) rule at the recursor's extension.  Since task
#175 S2 the stored rule is the *generated* one, whose reading is the
λ-tower over `ruleDataAV` — the recursor type's parameter, motive and
minor entries followed by the constructor's field entries lifted two
under (`denoteP_directRecRhs`) — so the rule's λ-domains are the
frame's own entries and their fit is `spineFit_of_sat2` (the
`recLawFits` pins are gone); the frames' `RecBase` feeds
`recLawCore`.
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-! ## Kit -/

omit [SetTheory V] in
/-- The full frame's values, outermost first, are the reversed range. -/
theorem frameVals_eq_reverse_range (ρ : Nat → V) (N : Nat) :
    frameVals ρ N N = (List.range N).reverse.map ρ := by
  apply List.ext_getElem
  · simp [frameVals]
  · intro i h1 h2
    have hi : i < N := by simpa [frameVals] using h1
    simp only [frameVals, List.getElem_map, List.getElem_range, List.getElem_reverse,
      List.length_range]

/-- The rule's λ-domains are the recursor's first `nP + 2` domains
followed by the constructor's field domains lifted two under. -/
theorem ruleDataAV_map_dom {m : EnvS2Core V env} {T C : Name} {ψ : Name → Nat}
    {nP nF : Nat} {ℓ : Level} {pps ds : List (Nat × Nat × AVExpr)} (hlenP : pps.length = nP) :
    (ruleDataAV m T C ψ nP nF ℓ pps ds).map (·.2)
      = ((recDataAV m T C ψ nP nF ℓ pps ds).take (nP + 2)).map (·.2.2) ++
        (liftDoms 2 0 (ds.drop nP)).map (·.2.2) := by
  unfold ruleDataAV recDataAV
  have hsplit : ∀ (L : List (Nat × Nat × AVExpr)) (a b c : Nat × Nat × AVExpr),
      L ++ [a, b, c] = (L ++ [a, b]) ++ [c] := fun L a b c => by simp
  rw [hsplit, List.take_left' (by simp [hlenP])]
  simp [List.map_append, rebit, List.map_map, Function.comp_def]

set_option maxHeartbeats 6400000 in
/-- **The direct block's rule fires at the readings.** -/
theorem recRuleLaw (mp : EnvS2PM V μ env)
    {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {rhsA : Expr}
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa (Lech.directCaps p)))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    {pps ds rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hCD : CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds)
    (hRD : RecData mp.base2 cvRa p.nP (elimLevel p) rds)
    (hrds : ∀ ψ, rds ψ
      = recDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p) (pps ψ) (ds ψ))
    {fvsR : List Expr} {oR : Expr}
    (hR : ∀ ψ : Name → Nat,
      OpenedP mp.base2 ψ (p.nP + 3) cvRa.type fvsR oR (((rds ψ).map (·.2.2)).reverse)
        (.app (.bvar 2) (.bvar 0)))
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hleafC : ∀ ψ, mp.base2.acval p.cvC.name ψ
      = directMkAV (p.resSort.eval ψ) (ds ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        (p.isProp = false → FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (p.isProp = true → p.large = true →
          FieldsBound 0 ρ (((ds ψ).drop p.nP).map (·.2.2))))
    (hRuleRead : ∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 rhsA
      = some (mkLamsAV (ruleDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p)
          (pps ψ) (ds ψ)) (AVExpr.mkAppN (.bvar p.nF) (fieldBvars p.nF))))
    (hRuleOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (mkLamsAV (ruleDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p)
          (pps ψ) (ds ψ)) (AVExpr.mkAppN (.bvar p.nF) (fieldBvars p.nF))))
    (hrhsRes : rhsA.constsResolve env = true)
    (hRres : cvRa.type.constsResolve env = true)
    (hfresh : env.find? cvRa.name = none)
    {rule : RecRule} (hrule : rule = ⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩)
    (m₂ : EnvS2Core V ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2) [rule] :: env.consts⟩)
    (hac : m₂.acval = acvalWith mp.base2.acval cvRa.name
      (fun ψ => directRecAV ((elimLevel p).eval ψ) (rds ψ) p.nF))
    (hAokP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (directRecAV ((elimLevel p).eval ψ) (rds ψ) p.nF))
    (φ : Name → Nat) :
    RecRuleLawP m₂ φ cvRa.name cvRa (p.nP + 2) (p.nP + 2) rule := by
  subst hrule
  -- the constructor's stored type
  obtain ⟨-, -, hCres, -, -⟩ := mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCres
  have hcbC : ConstsBound env cvCa.type := constsBound_of_constsResolve _ hCres
  have hcbT : ConstsBound env cvRa.type := constsBound_of_constsResolve _ hRres
  have hcbR : ConstsBound env rhsA := constsBound_of_constsResolve _ hrhsRes
  have hRC : p.cvC.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfC; exact nomatch hfC
  have hRT : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  -- the cons crossing
  have hcross : ∀ e : Expr, ConsCrossAt (.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩]) e :=
    fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hfindC : (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩] :: env.consts⟩ : Env).find? p.cvC.name
      = some (.ctorInfo cvCa p.nP p.nF) := by
    rw [Lech.Env.find?_cons, if_neg (fun h => hRC h.symm)]
    exact hfC
  -- the law
  refine ⟨Nat.le_refl _, fun us hus => ?_⟩
  dsimp only
  -- the readings at the instantiation
  have hinstR : ∀ (d : Nat) (e : Expr),
      denoteP m₂.acval _ φ d (e.instantiateLevelParams cvRa.levelParams us)
        = denoteP m₂.acval _ (Level.substFn φ cvRa.levelParams us) d e :=
    fun d e => denoteP_instLevels (acvalParamsAt_of_core m₂) φ d e
  generalize hψR : Level.substFn φ cvRa.levelParams us = ψR at hinstR ⊢
  -- the right-hand side's reading, at the extension
  have hRa₂ : denoteP m₂.acval ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩] :: env.consts⟩ φ 0
      (rhsA.instantiateLevelParams cvRa.levelParams us)
      = some (mkLamsAV (ruleDataAV mp.base2 p.cvT.name p.cvC.name ψR p.nP p.nF (elimLevel p)
          (pps ψR) (ds ψR)) (AVExpr.mkAppN (.bvar p.nF) (fieldBvars p.nF))) := by
    rw [hinstR, hac]
    exact denoteP_cons_mono hfresh (hcross _) ψR 0 hcbR (hRuleRead ψR)
  refine ⟨_, hRa₂, hRuleOk ψR, fun _ _ h => absurd h (by simp), ?_⟩
  intro cvj cnP cnF hfcj usj ρ xs ys TVa TVja restR restC hxl hyl husjl hψ hplain _ _ hTVa
    hTVja hfitR hfitC
  -- the constructor found is the block's
  obtain ⟨rfl, rfl, rfl⟩ := ConstantInfo.ctorInfo.inj (Option.some.inj (hfindC.symm.trans hfcj))
  -- the level assignments
  have hagree : ∀ q ∈ p.cvT.levelParams,
      Level.substFn φ cvCa.levelParams usj q = ψR q := by
    have h := hψ
    simp only [Lech.recFireComparands] at h
    rw [hlpsC] at h
    rw [hlpsC, ← hψR]
    exact substFn_agree_of_comparand h
  have hdsEq : ds (Level.substFn φ cvCa.levelParams usj) = ds ψR :=
    hCD.params (Level.substFn φ cvCa.levelParams usj) ψR
      (fun q hq => hagree q (by rw [← hlpsC]; exact hq))
  have hwEq : p.resSort.eval (Level.substFn φ cvCa.levelParams usj) = p.resSort.eval ψR :=
    (hFD.params (Level.substFn φ cvCa.levelParams usj) ψR
      (fun q hq => hagree q (by rw [← hlpsT]; exact hq))).2
  -- the recursor and constructor types' readings, at the extension
  have hRD₂ := hRD.cross (c₀ := .recInfo cvRa (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩]) hfresh (hcross _) hcbT m₂ hac
  have hCD₂ := hCD.cross (c₀ := .recInfo cvRa (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩]) hfresh hRT (hcross _) hcbC m₂ hac
  have hTVa' : TVa = mkPisAV (rds ψR) (.app (.bvar 2) (.bvar 0)) := by
    have h := hTVa
    rw [hinstR] at h
    exact Option.some.inj (h.symm.trans (hRD₂.read ψR))
  have hTVja' : TVja = mkPisAV (ds ψR)
      (ctorBodyAV m₂ p.cvT.name p.nP p.nF (Level.substFn φ cvCa.levelParams usj)) := by
    have h := hTVja
    rw [denoteP_instLevels (acvalParamsAt_of_core m₂) φ 0 cvCa.type] at h
    have := Option.some.inj (h.symm.trans (hCD₂.read (Level.substFn φ cvCa.levelParams usj)))
    rw [this, hdsEq]
  -- the constructor's leaf at the extension
  have hleafC₂ : m₂.acval p.cvC.name (Level.substFn φ cvCa.levelParams usj)
      = directMkAV (p.resSort.eval ψR) (ds ψR) (((ds ψR).drop p.nP).map (·.2.2)) := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ p.cvC.name (Level.substFn φ cvCa.levelParams usj) = _
    rw [acvalWith_ne hRC, hleafC (Level.substFn φ cvCa.levelParams usj), hdsEq, hwEq]
  have hleafR₂ : m₂.acval cvRa.name ψR
      = directRecAV ((elimLevel p).eval ψR) (rds ψR) p.nF := by
    rw [hac]
    show acvalWith mp.base2.acval cvRa.name _ cvRa.name ψR = _
    rw [acvalWith_self]
  -- the fits, as spines
  have hspR : SpineFit ρ ((rds ψR).map (·.2.2))
      ((xs ++ [AVExpr.mkAppN (directMkAV (p.resSort.eval ψR) (ds ψR)
        (((ds ψR).drop p.nP).map (·.2.2))) ys]).map (interp2 V ρ)) := by
    have hst := stripPisAV_mkPisAV (rds ψR) (AVExpr.app (.bvar 2) (.bvar 0))
    rw [hRD.len ψR] at hst
    have htele := piTeleP_of_stripPisAV hst
    have hfit := hfitR
    rw [hTVa'] at hfit
    try simp only [RecRule.ctor] at hfit
    rw [hleafC₂] at hfit
    have hchain := teleFitPA_to_chain (p.nP + 3) htele (by simp [hxl]) hfit
    refine spineFit_of_chain (by simp [hxl, hRD.len ψR]) ?_
    intro n hn
    have := hchain n (by simpa [hRD.len ψR] using hn)
    simpa [hRD.len ψR] using this
  have hspC : SpineFit ρ ((ds ψR).map (·.2.2)) (ys.map (interp2 V ρ)) := by
    have hst := stripPisAV_mkPisAV (ds ψR)
      (ctorBodyAV m₂ p.cvT.name p.nP p.nF (Level.substFn φ cvCa.levelParams usj))
    rw [hCD.len ψR] at hst
    have htele := piTeleP_of_stripPisAV hst
    have hfit := hfitC
    rw [hTVja'] at hfit
    have hchain := teleFitPA_to_chain (p.nP + p.nF) htele (by simpa using hyl) hfit
    refine spineFit_of_chain (by simp [hyl, hCD.len ψR]) ?_
    intro n hn
    have := hchain n (by simpa [hCD.len ψR] using hn)
    simpa [hCD.len ψR] using this
  have hplain' : ∀ i, i < p.nP →
      interp2 V ρ (ys.getD i default) = interp2 V ρ (xs.getD i default) :=
    fun i hi => hplain rfl i hi (by omega)
  -- the frames at ψR
  obtain ⟨-, hbase⟩ := recFrames (m := mp.base2) hFD hCD hleafT hleafC hiff hfields ψR
    (hrds ψR) (hR ψR)
  -- the bound at squash with a large eliminator
  have hbound0 : (elimLevel p).eval ψR ≠ 0 → p.resSort.eval ψR = 0 → ∀ ρ' : Nat → V,
      Sat2 V ((((ds ψR).take p.nP).map (·.2.2)).reverse) ρ' →
      FieldsBound 0 ρ' (((ds ψR).drop p.nP).map (·.2.2)) := by
    intro hl hw ρ' hρ'
    have hlarge : p.large = true := by
      cases hpl : p.large
      · exfalso
        apply hl
        simp [elimLevel, Lech.directElimLevel, hpl, Level.eval]
      · rfl
    by_cases hnp : p.isProp = true
    · exact (hfields ψR ρ' hρ').2.2.2 hnp hlarge
    · have := (hfields ψR ρ' hρ').2.2.1 (by simpa using hnp)
      rwa [hw] at this
  -- the rule's λ-domains are the frame's entries: the fit is the frame's `Sat2`
  have hlenL : (ruleDataAV mp.base2 p.cvT.name p.cvC.name ψR p.nP p.nF (elimLevel p)
      (pps ψR) (ds ψR)).length = p.nP + 2 + p.nF := by
    simp only [ruleDataAV, List.length_map, List.length_append, rebit_length, liftDoms_length,
      List.length_drop, List.length_cons, List.length_nil, hFD.len ψR, hCD.len ψR]
    omega
  have hlenΓ : (((rds ψR).map (·.2.2)).reverse).length = p.nP + 3 := by simp [hRD.len ψR]
  have hdrop1 : (((rds ψR).map (·.2.2)).reverse).drop 1
      = (((rds ψR).map (·.2.2)).reverse).getD 1 default :: (((rds ψR).map (·.2.2)).reverse).drop 2 := by
    have h := drop_succ_eq_getD_cons hlenΓ (i := p.nP + 1) (by omega)
    rwa [show p.nP + 3 - (p.nP + 1 + 1) = 1 from by omega,
      show p.nP + 3 - 1 - (p.nP + 1) = 1 from by omega,
      show p.nP + 3 - (p.nP + 1) = 2 from by omega] at h
  have hdrop1' : (((rds ψR).map (·.2.2)).reverse).drop 1
      = (((rds ψR).take (p.nP + 2)).map (·.2.2)).reverse := by
    rw [reverse_map_take_drop (rds ψR) (p.nP + 2), List.drop_left' (by simp [hRD.len ψR])]
  have hfitsL : ∀ ρ'' : Nat → V,
      Sat2 V ((((liftDoms 2 0 ((ds ψR).drop p.nP)).map (·.2.2)).reverse) ++
        ((((rds ψR).map (·.2.2)).reverse).getD 1 default ::
          (((rds ψR).map (·.2.2)).reverse).drop 2)) ρ'' →
      SpineFit (fun k => ρ'' (k + (p.nP + 2 + p.nF)))
        ((ruleDataAV mp.base2 p.cvT.name p.cvC.name ψR p.nP p.nF (elimLevel p)
          (pps ψR) (ds ψR)).map (·.2))
        (frameVals ρ'' (p.nP + 2 + p.nF) (p.nP + 2 + p.nF)) := by
    intro ρ'' hρ''
    rw [← hdrop1, hdrop1', ← List.reverse_append, ← List.map_append] at hρ''
    have hsp := spineFit_of_sat2 (Δ₀ := []) (by rw [List.append_nil]; exact hρ'')
    rw [ruleDataAV_map_dom (hFD.len ψR), ← hrds ψR, frameVals_eq_reverse_range]
    have hlen' : (((rds ψR).take (p.nP + 2) ++ liftDoms 2 0 ((ds ψR).drop p.nP)).map (·.2.2)).length
        = p.nP + 2 + p.nF := by
      simp only [List.length_map, List.length_append, List.length_take, liftDoms_length,
        List.length_drop, hRD.len ψR, hCD.len ψR]
      omega
    rw [hlen', List.map_append] at hsp
    exact hsp
  -- the law's two halves
  have hcore := recLawCore (hRD.len ψR) (hCD.len ψR) (fun ρ' => (hAokP ψR ρ').1) hbase
    (fun ρ' h => (hfields ψR ρ' h).1) hbound0 hlenL rfl (hRuleOk ψR) hfitsL
    hxl (by simpa using hyl) hspR hspC hplain'
  try simp only [RecRule.ctor, RecRule.ctorParams] at hcore ⊢
  rw [hleafR₂, hleafC₂]
  exact hcore

end Lech.SetP
