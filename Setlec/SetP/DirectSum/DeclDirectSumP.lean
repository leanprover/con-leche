import Setlec.SetP.Direct.DeclDirectP
import Setlec.SetP.DirectSum.SumStageRecP
import Setlec.Semantics.Direct.DeclDirectSum

/-!
# The direct sum's install, assembled (task #175 sum-types)

`declDirectSumP`: the P carrier survives the direct sum install's run
(`DeclDirectSumRun`).  The stages: the former (twice — first with the
empty chain list, to read the constructors' field data at a carrier
storing the former; then with the chains read, the readings
identified by `denoteP_openPis_agree` since no field domain mentions
the former), the constructors in order (`sumCtorsLoop`, every earlier
constructor's data and leaf crossing each later cons; the pending
constructors staying fresh by the distinct-names guard), and the
recursor (`stageSumRec`).
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Kit -/

/-- The field chains depend on the data only past the parameters. -/
theorem fssOf_ctorDataList_congr {nP : Nat} {dsF dsF' : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {ψ : Name → Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {k : Nat},
      (∀ i, i < cs.length → (dsF (k + i) ψ).drop nP = (dsF' (k + i) ψ).drop nP) →
      fssOf nP (ctorDataList dsF ψ cs k) = fssOf nP (ctorDataList dsF' ψ cs k)
  | [], _, _ => rfl
  | _ :: cs, k, h => by
    simp only [fssOf, ctorDataList, List.map_cons]
    have h0 := h 0 (by simp)
    rw [Nat.add_zero] at h0
    rw [h0]
    congr 1
    have := fssOf_ctorDataList_congr (nP := nP) (dsF := dsF) (dsF' := dsF') (ψ := ψ) (cs := cs)
      (k := k + 1) fun i hi => by
        rw [show k + 1 + i = k + (i + 1) from by omega]
        exact h (i + 1) (by simpa using hi)
    simpa [fssOf] using this

/-- Distinct names, positionally. -/
theorem names_ne_of_nodup {ctorsA : List (ConstantVal × Nat)}
    (hnd : (ctorsA.map (·.1.name)).Nodup) {i j : Nat} {cAi cAj : ConstantVal × Nat}
    (hi : ctorsA[i]? = some cAi) (hj : ctorsA[j]? = some cAj) (hne : i ≠ j) :
    cAi.1.name ≠ cAj.1.name := by
  have hil : i < ctorsA.length := (List.getElem?_eq_some_iff.mp hi).1
  have hjl : j < ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hp := List.pairwise_iff_getElem.mp hnd
  have hi' : ctorsA[i] = cAi := by
    have := List.getElem?_eq_getElem hil; rw [hi] at this; exact (Option.some.inj this).symm
  have hj' : ctorsA[j] = cAj := by
    have := List.getElem?_eq_getElem hjl; rw [hj] at this; exact (Option.some.inj this).symm
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · have := hp i j (by simpa using hil) (by simpa using hjl) hlt
    simp only [List.getElem_map, hi', hj'] at this
    exact this
  · have := hp j i (by simpa using hjl) (by simpa using hil) hgt
    simp only [List.getElem_map, hi', hj'] at this
    exact fun h => this h.symm

/-! ## The constructors' loop -/

/-- The facts about the pending constructors at an environment. -/
def PendingAt {env : Env} (m : EnvS2Core V env) (T : Name) (nP : Nat) (resSort : Level)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)) (ctorsA : List (ConstantVal × Nat))
    (k : Nat) : Prop :=
  ∀ i cA, k ≤ i → ctorsA[i]? = some cA →
    env.find? cA.1.name = none ∧ cA.1.type.constsResolve env = true ∧
    CtorData m T cA.1 nP cA.2 resSort (dsF i)

/-- The facts about the consed constructors at an environment. -/
def ConsedAt {env : Env} (m : EnvS2Core V env) (T : Name) (lps : List Name) (nP : Nat)
    (resSort : Level)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)) (ctorsA : List (ConstantVal × Nat))
    (k : Nat) : Prop :=
  ∀ i cA, i < k → ctorsA[i]? = some cA →
    CtorFactsAt m T lps nP resSort dsF i cA ∧
    ∀ ψ, m.acval cA.1.name ψ
      = directSumMkAV (resSort.eval ψ) i (dsF i ψ) (((dsF i ψ).drop nP).map (·.2.2))
          (fssOf nP (ctorDataList dsF ψ ctorsA 0))

set_option maxHeartbeats 6400000 in
/-- **The constructors' conses, in order.** -/
theorem sumCtorsLoop (hμ : μ.verifiedChecks = true)
    {F : Nat} {p : DirectSumParts} {env₀ envI : Env} {cvTa : ConstantVal}
    {ctors ctorsA : List (ConstantVal × Nat)}
    (hCtors : Setlec.checkDirectSumCtors (Setlec.fueledOps μ F) env₀ envI p.cvT.name
      p.cvT.levelParams p.nP p.resSort p.isProp p.large cvTa ctors = .ok ctorsA)
    (hnd : (ctorsA.map (·.1.name)).Nodup)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hlpsA : ∀ cA ∈ ctorsA, cA.1.levelParams = p.cvT.levelParams)
    (hstripA : ∀ cA ∈ ctorsA, (cA.1.type.stripPis (p.nP + cA.2)).isSome = true)
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
      fssOf p.nP (ctorDataList dsF ψ₁ ctorsA 0) = fssOf p.nP (ctorDataList dsF ψ₂ ctorsA 0))
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF ψ ctorsA 0),
      FieldsBelow p.nP Fs)
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat2 V ((pps ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)) ∧
      SumFieldsValid ρ (fssOf p.nP (ctorDataList dsF ψ ctorsA 0))) :
    ∀ (rest : List (ConstantVal × Nat)) (k : Nat) (env : Env) (mp : EnvS2PM V μ env),
      (∀ i, rest[i]? = ctorsA[k + i]?) → k + rest.length = ctorsA.length →
      Setlec.EtaFamiliesClosed env →
      env.find? p.cvT.name = some (.indInfo cvTa {}) →
      FormerData mp.base2 cvTa p.nP p.resSort pps →
      (∀ ψ, mp.base2.acval p.cvT.name ψ
        = directSumTyAV (p.resSort.eval ψ) (pps ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0))) →
      ConsedAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.resSort dsF ctorsA k →
      PendingAt mp.base2 p.cvT.name p.nP p.resSort dsF ctorsA k →
      ∃ mp' : EnvS2PM V μ (Setlec.consSumCtors p.nP rest env),
        Setlec.EtaFamiliesClosed (Setlec.consSumCtors p.nP rest env) ∧
        (Setlec.consSumCtors p.nP rest env).find? p.cvT.name = some (.indInfo cvTa {}) ∧
        FormerData mp'.base2 cvTa p.nP p.resSort pps ∧
        (∀ ψ, mp'.base2.acval p.cvT.name ψ
          = directSumTyAV (p.resSort.eval ψ) (pps ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0))) ∧
        ConsedAt mp'.base2 p.cvT.name p.cvT.levelParams p.nP p.resSort dsF ctorsA
          ctorsA.length
  | [], k, env, mp, _, hk, hE, hfT, hFD, hleafT, hcons, _ => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    exact ⟨mp, hE, hfT, hFD, hleafT, hcons⟩
  | cA :: rest, k, env, mp, hrest, hk, hE, hfT, hFD, hleafT, hcons, hpend => by
    have hcAk : ctorsA[k]? = some cA := by
      have := hrest 0; simpa using this.symm
    obtain ⟨hlen, hall⟩ := Setlec.checkDirectSumCtors_inv hCtors
    have hkl : k < ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hcAk).1; omega
    obtain ⟨hnF, hCtor⟩ := hall k (ctors[k]) cA (List.getElem?_eq_getElem hkl) hcAk
    rw [← hnF] at hCtor
    obtain ⟨hfresh, htr, hCD⟩ := hpend k cA (Nat.le_refl _) hcAk
    have hlpsC : cA.1.levelParams = p.cvT.levelParams := hlpsA cA (List.mem_of_getElem? hcAk)
    have hstripC := hstripA cA (List.mem_of_getElem? hcAk)
    have hTC : p.cvT.name ≠ cA.1.name := by
      intro h; rw [h, hfresh] at hfT; exact nomatch hfT
    -- the stage
    obtain ⟨mpC, hacC⟩ := stageSumCtor (j := k) hE mp hCtor hfresh htr hfT hlpsT hlpsC hFD hCD
      hleafT (fun ψ => by rw [fssOf_getElem?, ctorDataList_getElem?, hcAk, Nat.zero_add]; rfl)
      hFssParams hFssBelow (hiff k cA hcAk) hFssOk
    -- the invariants at the extension
    have hcbT : ConstsBound env cvTa.type :=
      constsBound_of_constsResolve _ (mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfT)).2.2.1
    have hcbC : ConstsBound env cA.1.type := constsBound_of_constsResolve _ htr
    have hcross : ∀ e : Expr, ConsCrossAt (.ctorInfo cA.1 p.nP cA.2) e :=
      fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
    have hE' : Setlec.EtaFamiliesClosed ⟨.ctorInfo cA.1 p.nP cA.2 :: env.consts⟩ := by
      intro T'' cvT'' caps hf he hr
      rw [Setlec.Env.find?_cons] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨cvC', hfC'⟩ := hE T'' cvT'' caps hf he hr
        exact ⟨cvC', Setlec.Env.find?_cons_of_fresh hfresh hfC'⟩
    have hfT' : (⟨.ctorInfo cA.1 p.nP cA.2 :: env.consts⟩ : Env).find? p.cvT.name
        = some (.indInfo cvTa {}) := Setlec.Env.find?_cons_of_fresh hfresh hfT
    have hFD' : FormerData mpC.base2 cvTa p.nP p.resSort pps :=
      hFD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh (hcross _) hcbT mpC.base2 hacC
    have hleafT' : ∀ ψ, mpC.base2.acval p.cvT.name ψ
        = directSumTyAV (p.resSort.eval ψ) (pps ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)) := by
      intro ψ
      rw [hacC]
      show acvalWith mp.base2.acval cA.1.name _ p.cvT.name ψ = _
      rw [acvalWith_ne hTC]
      exact hleafT ψ
    have hcons' : ConsedAt mpC.base2 p.cvT.name p.cvT.levelParams p.nP p.resSort dsF ctorsA
        (k + 1) := by
      intro i cAi hi hcAi
      rcases Nat.lt_or_ge i k with hlt | hge
      · obtain ⟨⟨hfi, hlpsi, hstripi, hCDi⟩, hleaf⟩ := hcons i cAi hlt hcAi
        have hne : cAi.1.name ≠ cA.1.name := names_ne_of_nodup hnd hcAi hcAk (by omega)
        have hcbi : ConstsBound env cAi.1.type :=
          constsBound_of_constsResolve _
            (mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfi)).2.2.1
        refine ⟨⟨Setlec.Env.find?_cons_of_fresh hfresh hfi, hlpsi, hstripi,
          hCDi.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC (hcross _) hcbi mpC.base2 hacC⟩,
          ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cAi.1.name ψ = _
        rw [acvalWith_ne hne]
        exact hleaf ψ
      · have hik : i = k := by omega
        subst hik
        obtain rfl := Option.some.inj (hcAk.symm.trans hcAi)
        refine ⟨⟨Setlec.Env.find?_cons_self (.ctorInfo cA.1 p.nP cA.2) env, hlpsC, hstripC,
          hCD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC (hcross _) hcbC mpC.base2 hacC⟩,
          ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cA.1.name ψ = _
        rw [acvalWith_self]
    have hpend' : PendingAt mpC.base2 p.cvT.name p.nP p.resSort dsF ctorsA (k + 1) := by
      intro i cAi hi hcAi
      obtain ⟨hfreshi, htri, hCDi⟩ := hpend i cAi (by omega) hcAi
      have hne : cA.1.name ≠ cAi.1.name := names_ne_of_nodup hnd hcAk hcAi (by omega)
      refine ⟨?_, Expr.constsResolve_mono htri,
        hCDi.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC (hcross _)
          (constsBound_of_constsResolve _ htri) mpC.base2 hacC⟩
      rw [Setlec.Env.find?_cons]
      split
      · next h => exact absurd h hne
      · exact hfreshi
    have hrest' : ∀ i, rest[i]? = ctorsA[k + 1 + i]? := by
      intro i
      have := hrest (i + 1)
      rwa [show k + (i + 1) = k + 1 + i from by omega] at this
    exact sumCtorsLoop hμ hCtors hnd hlpsT hlpsA hstripA hFssParams hFssBelow hiff hFssOk rest
      (k + 1) _ mpC hrest' (by simp at hk; omega) hE' hfT' hFD' hleafT' hcons' hpend'

/-! ## The assembly -/

set_option maxHeartbeats 6400000 in
/-- **The P carrier survives a direct sum install.** -/
theorem declDirectSumP (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p : DirectSumParts} (mp : EnvS2PM V μ env)
    (hE : Setlec.EtaFamiliesClosed env) (hdp : Setlec.directSumParts? env block = some p)
    (h : Setlec.Semantics.DeclDirectSumRun μ F env p env₂) : Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨helim, hnd, cvTa, envI, ctorsA, cvRa, rhss, hInd, hCtors, hRec, rfl⟩ := h
  obtain ⟨hProp, -, hn1, hClps, -, -, helimR, hRlps, -⟩ := Setlec.directSumParts?_inv hdp
  -- the former
  obtain ⟨hccvT, rfl, bsT, hstripT⟩ := Setlec.checkDirectSumInd_shape hInd
  obtain ⟨hfindT, -, -, -, -, -, typeT, -, -, -, -, htrT, -, -, htyT⟩ :=
    Setlec.checkConstantVal_inv hccvT
  have hTname : cvTa.name = p.cvT.name := by rw [htyT]
  have hlpsT : cvTa.levelParams = p.cvT.levelParams := by rw [htyT]
  have hTtype : cvTa.type = typeT := by rw [htyT]
  obtain ⟨pps, hFD⟩ := formerData_of hμ mp hccvT hstripT
  have hTfresh : env.find? cvTa.name = none := by rw [hTname]; exact hfindT
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (by rw [hTtype]; exact htrT)
  have hfT_I : (⟨.indInfo cvTa {} :: env.consts⟩ : Env).find? p.cvT.name
      = some (.indInfo cvTa {}) := by
    rw [← hTname]; exact Setlec.Env.find?_cons_self _ _
  have hProp' : p.isProp = true → (Level.isEquiv p.resSort .zero == some true) = true :=
    fun h => by rw [← hProp]; exact h
  obtain ⟨tfvs, trest, hopT⟩ := openPisAtFvars_of_stripPis_isSome p.nP 0 (by rw [hstripT]; rfl)
  have hE_I : Setlec.EtaFamiliesClosed ⟨.indInfo cvTa {} :: env.consts⟩ := by
    intro T'' cvT'' caps hf he hr
    rw [Setlec.Env.find?_cons] at hf
    split at hf
    · obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
      exact absurd he Bool.false_ne_true
    · obtain ⟨cvC', hfC'⟩ := hE T'' cvT'' caps hf he hr
      exact ⟨cvC', Setlec.Env.find?_cons_of_fresh hTfresh hfC'⟩
  -- the constructors' runs
  obtain ⟨hlenA, hall⟩ := Setlec.checkDirectSumCtors_inv hCtors
  have hrunOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ c : ConstantVal × Nat, p.ctors[j]? = some c ∧
      cA.1.name = c.1.name ∧ cA.1.levelParams = p.cvT.levelParams ∧
      (⟨.indInfo cvTa {} :: env.consts⟩ : Env).find? cA.1.name = none ∧
      cA.1.type.constsResolve ⟨.indInfo cvTa {} :: env.consts⟩ = true ∧
      (cA.1.type.stripPis (p.nP + cA.2)).isSome = true ∧
      Setlec.checkDirectSumCtor (Setlec.fueledOps μ F) env ⟨.indInfo cvTa {} :: env.consts⟩
        p.cvT.name p.cvT.levelParams p.nP p.resSort p.isProp p.large c.1 cA.2 cvTa = .ok cA.1 := by
    intro j cA hj
    have hjl : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1; omega
    obtain ⟨hnF, hCtor⟩ := hall j (p.ctors[j]) cA (List.getElem?_eq_getElem hjl) hj
    rw [← hnF] at hCtor
    obtain ⟨hccvC, ⟨cbs, hstripC⟩, -⟩ := Setlec.checkDirectSumCtor_shape hCtor
    obtain ⟨hfindC, -, -, -, -, -, typeC, -, -, -, -, htrC, -, -, htyC⟩ :=
      Setlec.checkConstantVal_inv hccvC
    refine ⟨p.ctors[j], List.getElem?_eq_getElem hjl, by rw [htyC], ?_, ?_, ?_,
      by rw [hstripC]; rfl, hCtor⟩
    · rw [htyC]
      exact (hClps _ (List.getElem_mem hjl)).1
    · show Env.find? _ cA.1.name = none
      rw [htyC]; exact hfindC
    · show Expr.constsResolve _ cA.1.type = true
      rw [htyC]; exact htrC
  have hndA : (ctorsA.map (·.1.name)).Nodup := by
    have heq : ctorsA.map (·.1.name) = p.ctors.map (·.1.name) := by
      apply List.ext_getElem?
      intro i
      rw [List.getElem?_map, List.getElem?_map]
      cases hi : ctorsA[i]? with
      | none =>
        have : p.ctors[i]? = none := by
          rw [List.getElem?_eq_none_iff] at hi ⊢; omega
        rw [this]
      | some cA =>
        obtain ⟨c, hc, hname, -⟩ := hrunOf i cA hi
        rw [hc]
        simp [hname]
    rw [heq]; exact hnd
  -- the dummy former: the constructors' field readings need a carrier
  -- storing the former
  obtain ⟨mpI₀, hacI₀⟩ := stageSumFormer mp hE hInd hFD (fun _ => []) (fun _ _ _ => rfl)
    (fun _ _ h => nomatch h) (fun _ _ _ => ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩)
  have hex₀ : ∀ j : Nat, ∃ ds : (Name → Nat) → List (Nat × Nat × AVExpr),
      ∀ cA : ConstantVal × Nat, ctorsA[j]? = some cA →
      CtorData mpI₀.base2 p.cvT.name cA.1 p.nP cA.2 p.resSort ds := by
    intro j
    cases hj : ctorsA[j]? with
    | none => exact ⟨fun _ => [], fun _ h => nomatch h⟩
    | some cA =>
      obtain ⟨c, -, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
      obtain ⟨ds, hCD⟩ := sumCtorData_of hμ mpI₀ hCtor hfT_I hlpsT hstripT
      exact ⟨ds, fun cA' h => by obtain rfl := Option.some.inj h; exact hCD⟩
  let dsF₀ : Nat → (Name → Nat) → List (Nat × Nat × AVExpr) := fun j => Classical.choose (hex₀ j)
  have hdsF₀ : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      CtorData mpI₀.base2 p.cvT.name cA.1 p.nP cA.2 p.resSort (dsF₀ j) :=
    fun j => Classical.choose_spec (hex₀ j)
  have hFD_I₀ : FormerData mpI₀.base2 cvTa p.nP p.resSort pps :=
    hFD.cross (c₀ := .indInfo cvTa {}) hTfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT mpI₀.base2 hacI₀
  have hframes₀ : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
          Sat2 V (((dsF₀ j ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V (((dsF₀ j ψ).take p.nP).map (·.2.2)).reverse ρ →
          FieldsOkB (p.resSort.eval ψ) ρ (((dsF₀ j ψ).drop p.nP).map (·.2.2)) ∧
          FieldsValid ρ (((dsF₀ j ψ).drop p.nP).map (·.2.2))) := by
    intro j cA hj
    obtain ⟨c, -, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
    obtain ⟨hiff, hfields⟩ := sumCtorFrames hμ mpI₀ hCtor hfT_I hProp' hFD_I₀ (hdsF₀ j cA hj)
    exact ⟨hiff, fun ψ ρ h => ⟨(hfields ψ ρ h).1, (hfields ψ ρ h).2.1⟩⟩
  -- the field-chain facts of a data function
  have hFssFacts : ∀ (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)),
      (∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
        ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ cA.1.levelParams, ψ₁ q = ψ₂ q) → dsF j ψ₁ = dsF j ψ₂) →
      (∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA → ∀ ψ, DomsBelow 0 (dsF j ψ)) →
      (∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
        (∀ (ψ : Name → Nat) (ρ : Nat → V),
          Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
            Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V),
          Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
            FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
            FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)))) →
      (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
        fssOf p.nP (ctorDataList dsF ψ₁ ctorsA 0) = fssOf p.nP (ctorDataList dsF ψ₂ ctorsA 0)) ∧
      (∀ ψ : Name → Nat, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF ψ ctorsA 0), FieldsBelow p.nP Fs) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), Sat2 V ((pps ψ).map (·.2.2)).reverse ρ →
        SumFieldsOkB (p.resSort.eval ψ) ρ (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)) ∧
        SumFieldsValid ρ (fssOf p.nP (ctorDataList dsF ψ ctorsA 0))) := by
    intro dsF hparams hbelow hframes
    refine ⟨fun ψ₁ ψ₂ hφ => ?_, fun ψ Fs hFs => ?_, fun ψ ρ hρ => ?_⟩
    · unfold fssOf
      rw [ctorDataList_params]
      intro i hi
      rw [Nat.zero_add]
      obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
      obtain ⟨-, -, -, hlpsi, -⟩ := hrunOf i cAi hi'
      exact hparams i cAi hi' ψ₁ ψ₂ (fun q hq => hφ q (by rw [← hlpsi]; exact hq))
    · obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      rw [ctorDataList_getElem?, Nat.zero_add] at hi
      cases h : ctorsA[i]? with
      | none => rw [h] at hi; exact nomatch hi
      | some cA =>
        rw [h] at hi
        obtain rfl := Option.some.inj hi
        have := (DomsBelow.drop p.nP (hbelow i cA h ψ)).fields
        rwa [Nat.zero_add] at this
    · constructor
      · intro Fs hFs
        obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
        rw [ctorDataList_getElem?, Nat.zero_add] at hi
        cases h : ctorsA[i]? with
        | none => rw [h] at hi; exact nomatch hi
        | some cA =>
          rw [h] at hi
          obtain rfl := Option.some.inj hi
          exact ((hframes i cA h).2 ψ ρ (((hframes i cA h).1 ψ ρ).mp hρ)).1
      · intro Fs hFs
        obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
        rw [ctorDataList_getElem?, Nat.zero_add] at hi
        cases h : ctorsA[i]? with
        | none => rw [h] at hi; exact nomatch hi
        | some cA =>
          rw [h] at hi
          obtain rfl := Option.some.inj hi
          exact ((hframes i cA h).2 ψ ρ (((hframes i cA h).1 ψ ρ).mp hρ)).2
  obtain ⟨hFssParams₀, hFssBelow₀, hFssOk₀⟩ := hFssFacts dsF₀
    (fun j cA hj ψ₁ ψ₂ hφ => (hdsF₀ j cA hj).params ψ₁ ψ₂ hφ)
    (fun j cA hj ψ => (hdsF₀ j cA hj).below ψ) hframes₀
  -- the real former
  obtain ⟨mpI, hacI⟩ := stageSumFormer mp hE hInd hFD
    (fun ψ => fssOf p.nP (ctorDataList dsF₀ ψ ctorsA 0))
    (fun ψ₁ ψ₂ hφ => hFssParams₀ ψ₁ ψ₂ (fun q hq => hφ q (by rw [hlpsT]; exact hq)))
    hFssBelow₀ hFssOk₀
  -- the constructors' data at the real former, their fields identified
  have hex : ∀ j : Nat, ∃ ds : (Name → Nat) → List (Nat × Nat × AVExpr),
      ∀ cA : ConstantVal × Nat, ctorsA[j]? = some cA →
      CtorData mpI.base2 p.cvT.name cA.1 p.nP cA.2 p.resSort ds := by
    intro j
    cases hj : ctorsA[j]? with
    | none => exact ⟨fun _ => [], fun _ h => nomatch h⟩
    | some cA =>
      obtain ⟨c, -, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
      obtain ⟨ds, hCD⟩ := sumCtorData_of hμ mpI hCtor hfT_I hlpsT hstripT
      exact ⟨ds, fun cA' h => by obtain rfl := Option.some.inj h; exact hCD⟩
  let dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr) := fun j => Classical.choose (hex j)
  have hdsF : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      CtorData mpI.base2 p.cvT.name cA.1 p.nP cA.2 p.resSort (dsF j) :=
    fun j => Classical.choose_spec (hex j)
  have hdsEq : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA → ∀ ψ, (dsF j ψ).drop p.nP = (dsF₀ j ψ).drop p.nP := by
    intro j cA hj ψ
    obtain ⟨c, -, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
    obtain ⟨-, -, fvsP, crest, tfvs', trest', xFvs, sorts, hopC, -, -, hopX, hxres, -⟩ :=
      Setlec.checkDirectSumCtor_shape hCtor
    have hopAll := openPisAtFvars_add p.nP hopC (by rw [Nat.zero_add]; exact hopX)
    have hlenP : fvsP.length = p.nP := openPisAtFvars_length _ hopC
    have h1 := (hdsF j cA hj).read ψ
    have h2 := (hdsF₀ j cA hj).read ψ
    rw [hacI] at h1
    rw [hacI₀] at h2
    refine denoteP_openPis_agree (p.nP + cA.2) hopAll h1 h2
      (by rw [← (hdsF j cA hj).len ψ]; exact stripPisAV_mkPisAV _ _)
      (by rw [← (hdsF₀ j cA hj).len ψ]; exact stripPisAV_mkPisAV _ _) ?_
    intro i x hx hi
    have hxin : x ∈ xFvs := by
      rw [List.getElem?_append_right (by omega)] at hx
      exact List.mem_of_getElem? hx
    exact denoteP_acvalWith_unmentioned₂ hTfresh _ _ (hxres x hxin)
  have hFssEq : ∀ ψ, fssOf p.nP (ctorDataList dsF₀ ψ ctorsA 0)
      = fssOf p.nP (ctorDataList dsF ψ ctorsA 0) := by
    intro ψ
    refine fssOf_ctorDataList_congr (k := 0) fun i hi => ?_
    rw [Nat.zero_add]
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    exact (hdsEq i cAi hi' ψ).symm
  have hleafT_I : ∀ ψ, mpI.base2.acval p.cvT.name ψ
      = directSumTyAV (p.resSort.eval ψ) (pps ψ) (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)) := by
    intro ψ
    rw [hacI, ← hTname, acvalWith_self]
    show directSumTyAV _ _ _ = _
    rw [hFssEq ψ]
  have hFD_I : FormerData mpI.base2 cvTa p.nP p.resSort pps :=
    hFD.cross (c₀ := .indInfo cvTa {}) hTfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT mpI.base2 hacI
  have hframes : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
          Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
          FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
          FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2))) := by
    intro j cA hj
    obtain ⟨c, -, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
    obtain ⟨hiff, hfields⟩ := sumCtorFrames hμ mpI hCtor hfT_I hProp' hFD_I (hdsF j cA hj)
    exact ⟨hiff, fun ψ ρ h => ⟨(hfields ψ ρ h).1, (hfields ψ ρ h).2.1⟩⟩
  obtain ⟨hFssParams, hFssBelow, hFssOk⟩ := hFssFacts dsF
    (fun j cA hj ψ₁ ψ₂ hφ => (hdsF j cA hj).params ψ₁ ψ₂ hφ)
    (fun j cA hj ψ => (hdsF j cA hj).below ψ) hframes
  -- the constructors' conses
  obtain ⟨mpC, hE_C, hfT_C, hFD_C, hleafT_C, hconsAll⟩ := sumCtorsLoop hμ hCtors hndA hlpsT
    (fun cA hcA => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
      obtain ⟨-, -, -, hlps, -⟩ := hrunOf j cA hj
      exact hlps)
    (fun cA hcA => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
      obtain ⟨-, -, -, -, -, -, hstrip, -⟩ := hrunOf j cA hj
      exact hstrip)
    hFssParams hFssBelow (fun j cA hj => (hframes j cA hj).1) hFssOk
    ctorsA 0 _ mpI (fun i => by rw [Nat.zero_add]) (Nat.zero_add _) hE_I hfT_I hFD_I hleafT_I
    (fun i cA hi _ => absurd hi (Nat.not_lt_zero _))
    (fun i cA _ hi => by
      obtain ⟨-, -, -, -, hfresh, htr, -, -⟩ := hrunOf i cA hi
      exact ⟨hfresh, htr, hdsF i cA hi⟩)
  -- the recursor
  have hcf_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      CtorFactsAt mpC.base2 p.cvT.name p.cvT.levelParams p.nP p.resSort dsF j cA :=
    fun j cA hj => (hconsAll j cA (List.getElem?_eq_some_iff.mp hj).1 hj).1
  have hleafC_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA → ∀ ψ, mpC.base2.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (fssOf p.nP (ctorDataList dsF ψ ctorsA 0)) :=
    fun j cA hj => (hconsAll j cA (List.getElem?_eq_some_iff.mp hj).1 hj).2
  have hwl : p.large = true → p.resSort.isNeverZero = true ∨ ctorsA.length < 2 := by
    intro hl
    rcases helim hl with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hlenA]; exact h)
  have hn1' : ctorsA.length ≠ 1 := by rw [hlenA]; exact hn1
  have hmI : p.nP + 1 + p.ctors.length = p.nP + 1 + ctorsA.length := by rw [hlenA]
  obtain ⟨mp₃, -⟩ := stageSumRec hE_C hμ mpC hmI hRec hstripT hfT_C hlpsT hopT helimR hRlps
    hFD_C hcf_C hleafT_C hleafC_C (fun j cA hj => (hframes j cA hj).1)
    (fun j cA hj => (hframes j cA hj).2) hwl hn1'
  exact ⟨mp₃⟩

end Setlec.SetP
