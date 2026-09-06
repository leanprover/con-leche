import Lech.SetP.Direct.DeclDirectP
import Lech.SetP.DirectSum.SumStageRecP
import Lech.Semantics.Direct.DeclDirectSum

/-!
# The direct sum's install, assembled (task #175 sum-types, indexed)

`declDirectSumP`: the P carrier survives the direct sum install's run
(`DeclDirectSumRun`).  The stages: the former (twice — first with the
empty chain list, to read the constructors' field data and index
readings at a carrier storing the former; then with the restricted
chains `rChains` read off that data, the readings identified by
`denoteP_openPis_agree` (field domains) and `CtorDataI.Es_eq` (index
readings) since neither mentions the former), the constructors in
order (`sumCtorsLoop`, every earlier constructor's data and leaf
crossing each later cons; the pending constructors staying fresh by
the distinct-names guard), and the recursor (`stageSumRec`).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.TT Lech.TTVerify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## Kit -/

/-- The field chains depend on the data only past the parameters. -/
theorem fssOf_ctorDataList_congr {nP : Nat}
    {dsF dsF' : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF esF' : Nat → (Name → Nat) → List AVExpr} {ψ : Name → Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {k : Nat},
      (∀ i, i < cs.length → (dsF (k + i) ψ).drop nP = (dsF' (k + i) ψ).drop nP) →
      fssOf nP (ctorDataList dsF esF ψ cs k) = fssOf nP (ctorDataList dsF' esF' ψ cs k)
  | [], _, _ => rfl
  | _ :: cs, k, h => by
    simp only [fssOf, ctorDataList, List.map_cons]
    have h0 := h 0 (by simp)
    rw [Nat.add_zero] at h0
    rw [h0]
    congr 1
    have := fssOf_ctorDataList_congr (nP := nP) (dsF := dsF) (dsF' := dsF') (esF := esF)
      (esF' := esF') (ψ := ψ) (cs := cs) (k := k + 1) fun i hi => by
        rw [show k + 1 + i = k + (i + 1) from by omega]
        exact h (i + 1) (by simpa using hi)
    simpa [fssOf] using this

/-- The index readings depend on the data only through the readings. -/
theorem essOf_ctorDataList_congr
    {dsF dsF' : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF esF' : Nat → (Name → Nat) → List AVExpr} {ψ : Name → Nat} :
    ∀ {cs : List (ConstantVal × Nat)} {k : Nat},
      (∀ i, i < cs.length → esF (k + i) ψ = esF' (k + i) ψ) →
      essOf (ctorDataList dsF esF ψ cs k) = essOf (ctorDataList dsF' esF' ψ cs k)
  | [], _, _ => rfl
  | _ :: cs, k, h => by
    simp only [essOf, ctorDataList, List.map_cons]
    have h0 := h 0 (by simp)
    rw [Nat.add_zero] at h0
    rw [h0]
    congr 1
    have := essOf_ctorDataList_congr (dsF := dsF) (dsF' := dsF') (esF := esF)
      (esF' := esF') (ψ := ψ) (cs := cs) (k := k + 1) fun i hi => by
        rw [show k + 1 + i = k + (i + 1) from by omega]
        exact h (i + 1) (by simpa using hi)
    simpa [essOf] using this

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

/-- The reversed context of the former below its index binders is the
parameters'. -/
theorem drop_idx_params {ppsAll : List (Nat × Nat × AVExpr)} {nP nIdx : Nat}
    (hlen : ppsAll.length = nP + nIdx) :
    ((ppsAll.map (·.2.2)).reverse).drop nIdx = ((ppsAll.take nP).map (·.2.2)).reverse := by
  rw [reverse_map_take_drop ppsAll nP, List.drop_left' (by simp [hlen])]

/-! ## The constructors' loop -/

/-- The facts about the pending constructors at an environment. -/
def PendingAt {env : Env} (m : EnvS2Core V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (esF : Nat → (Name → Nat) → List AVExpr) (srcsF : Nat → List (Option Nat))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ i cA, k ≤ i → ctorsA[i]? = some cA →
    env.find? cA.1.name = none ∧ cA.1.type.constsResolve env = true ∧
    (∀ e ∈ idxF i, e.constsResolve env = true) ∧
    CtorDataI m T lps cA.1 nP cA.2 nIdx resSort isProp large (idxF i) (dsF i) (esF i) (srcsF i)

/-- The facts about the consed constructors at an environment. -/
def ConsedAt {env : Env} (m : EnvS2Core V env) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (idxF : Nat → List Expr)
    (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
    (esF : Nat → (Name → Nat) → List AVExpr) (srcsF : Nat → List (Option Nat))
    (ctorsA : List (ConstantVal × Nat)) (k : Nat) : Prop :=
  ∀ i cA, i < k → ctorsA[i]? = some cA →
    CtorFactsAt m T lps nP nIdx resSort isProp large idxF dsF esF srcsF i cA ∧
    (∀ e ∈ idxF i, e.constsResolve env = true) ∧
    ∀ ψ, m.acval cA.1.name ψ
      = directSumMkAV (resSort.eval ψ) i (dsF i ψ) (((dsF i ψ).drop nP).map (·.2.2))
          (uChains (fssOf nP (ctorDataList dsF esF ψ ctorsA 0)))

set_option maxHeartbeats 6400000 in
/-- **The constructors' conses, in order.** -/
theorem sumCtorsLoop (hμ : μ.verifiedChecks = true)
    {F : Nat} {p : DirectSumParts} {env₀ envI : Env} {cvTa : ConstantVal}
    {ctors ctorsA : List (ConstantVal × Nat)}
    (hCtors : Lech.checkDirectSumCtors (Lech.fueledOps μ F) env₀ envI p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa ctors = .ok ctorsA)
    (hnd : (ctorsA.map (·.1.name)).Nodup)
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hlpsA : ∀ cA ∈ ctorsA, cA.1.levelParams = p.cvT.levelParams)
    {ppsAll : (Name → Nat) → List (Nat × Nat × AVExpr)}
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF : Nat → (Name → Nat) → List AVExpr} {srcsF : Nat → List (Option Nat)}
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
      fssOf p.nP (ctorDataList dsF esF ψ₁ ctorsA 0) = fssOf p.nP (ctorDataList dsF esF ψ₂ ctorsA 0))
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0),
      FieldsBelow p.nP Fs)
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hFssOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) ∧
      SumFieldsValid ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)))
    (hIdx : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
      ∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
        SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF j ψ) bs))
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat2 V ((ppsAll ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ
        (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0))) ∧
      SumFieldsValid ρ
        (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0)))) :
    ∀ (rest : List (ConstantVal × Nat)) (k : Nat) (env : Env) (mp : EnvS2PM V μ env),
      (∀ i, rest[i]? = ctorsA[k + i]?) → k + rest.length = ctorsA.length →
      Lech.EtaFamiliesClosed env →
      env.find? p.cvT.name = some (.indInfo cvTa (Lech.directSumCaps p)) →
      FormerData mp.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll →
      (∀ ψ, mp.base2.acval p.cvT.name ψ
        = directSumTyAV (p.resSort.eval ψ) (ppsAll ψ)
            (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
              (essOf (ctorDataList dsF esF ψ ctorsA 0)))) →
      ConsedAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF ctorsA k →
      PendingAt mp.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF ctorsA k →
      ∃ mp' : EnvS2PM V μ (Lech.consSumCtors p.nP rest env),
        Lech.EtaFamiliesClosed (Lech.consSumCtors p.nP rest env) ∧
        (Lech.consSumCtors p.nP rest env).find? p.cvT.name
          = some (.indInfo cvTa (Lech.directSumCaps p)) ∧
        FormerData mp'.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll ∧
        (∀ ψ, mp'.base2.acval p.cvT.name ψ
          = directSumTyAV (p.resSort.eval ψ) (ppsAll ψ)
              (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
                (essOf (ctorDataList dsF esF ψ ctorsA 0)))) ∧
        ConsedAt mp'.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
          idxF dsF esF srcsF ctorsA ctorsA.length
  | [], k, env, mp, _, hk, hE, hfT, hFD, hleafT, hcons, _ => by
    simp only [List.length_nil, Nat.add_zero] at hk
    subst hk
    exact ⟨mp, hE, hfT, hFD, hleafT, hcons⟩
  | cA :: rest, k, env, mp, hrest, hk, hE, hfT, hFD, hleafT, hcons, hpend => by
    have hcAk : ctorsA[k]? = some cA := by
      have := hrest 0; simpa using this.symm
    obtain ⟨hlen, hall⟩ := Lech.checkDirectSumCtors_inv hCtors
    have hkl : k < ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hcAk).1; omega
    obtain ⟨hnF, hCtor⟩ := hall k (ctors[k]) cA (List.getElem?_eq_getElem hkl) hcAk
    rw [← hnF] at hCtor
    obtain ⟨hfresh, htr, hidxRes, hCD⟩ := hpend k cA (Nat.le_refl _) hcAk
    have hlpsC : cA.1.levelParams = p.cvT.levelParams := hlpsA cA (List.mem_of_getElem? hcAk)
    have hTC : p.cvT.name ≠ cA.1.name := by
      intro h; rw [h, hfresh] at hfT; exact nomatch hfT
    have hFsj : ∀ ψ, (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))[k]?
        = some (((dsF k ψ).drop p.nP).map (·.2.2)) := by
      intro ψ
      rw [fssOf_getElem?, ctorDataList_getElem?, hcAk, Nat.zero_add]; rfl
    have hEsj : ∀ ψ, (essOf (ctorDataList dsF esF ψ ctorsA 0))[k]? = some (esF k ψ) := by
      intro ψ
      rw [essOf_getElem?, ctorDataList_getElem?, hcAk, Nat.zero_add]; rfl
    -- the stage
    obtain ⟨mpC, hacC⟩ := stageSumCtor (j := k) hE mp hCtor hfresh htr hfT rfl rfl hlpsT hlpsC hFD hCD
      hleafT hFsj hEsj hFssParams hFssBelow (hiff k cA hcAk)
      hFssOk (fun ψ ρ hρ => hFssOkP ψ ρ ((hiff k cA hcAk ψ ρ).mpr hρ)) (hIdx k cA hcAk)
    -- the invariants at the extension
    have hcbT : ConstsBound env cvTa.type :=
      constsBound_of_constsResolve _ (mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfT)).2.2.1
    have hcbC : ConstsBound env cA.1.type := constsBound_of_constsResolve _ htr
    have hcross : ∀ e : Expr, ConsCrossAt (.ctorInfo cA.1 p.nP cA.2) e :=
      fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
    have hE' : Lech.EtaFamiliesClosed ⟨.ctorInfo cA.1 p.nP cA.2 :: env.consts⟩ := by
      intro T'' cvT'' caps hf he hr
      rw [Lech.Env.find?_cons] at hf
      split at hf
      · exact nomatch (Option.some.inj hf)
      · obtain ⟨cvC', hfC'⟩ := hE T'' cvT'' caps hf he hr
        exact ⟨cvC', Lech.Env.find?_cons_of_fresh hfresh hfC'⟩
    have hfT' : (⟨.ctorInfo cA.1 p.nP cA.2 :: env.consts⟩ : Env).find? p.cvT.name
        = some (.indInfo cvTa (Lech.directSumCaps p)) := Lech.Env.find?_cons_of_fresh hfresh hfT
    have hFD' : FormerData mpC.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll :=
      hFD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh (hcross _) hcbT mpC.base2 hacC
    have hleafT' : ∀ ψ, mpC.base2.acval p.cvT.name ψ
        = directSumTyAV (p.resSort.eval ψ) (ppsAll ψ)
            (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
              (essOf (ctorDataList dsF esF ψ ctorsA 0))) := by
      intro ψ
      rw [hacC]
      show acvalWith mp.base2.acval cA.1.name _ p.cvT.name ψ = _
      rw [acvalWith_ne hTC]
      exact hleafT ψ
    have hcons' : ConsedAt mpC.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ctorsA (k + 1) := by
      intro i cAi hi hcAi
      rcases Nat.lt_or_ge i k with hlt | hge
      · obtain ⟨⟨hfi, hlpsi, hCDi⟩, hresi, hleaf⟩ := hcons i cAi hlt hcAi
        have hne : cAi.1.name ≠ cA.1.name := names_ne_of_nodup hnd hcAi hcAk (by omega)
        have hcbi : ConstsBound env cAi.1.type :=
          constsBound_of_constsResolve _
            (mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfi)).2.2.1
        refine ⟨⟨Lech.Env.find?_cons_of_fresh hfresh hfi, hlpsi,
          hCDi.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcross hcbi
            (fun e he => constsBound_of_constsResolve _ (hresi e he)) mpC.base2 hacC⟩,
          fun e he => Expr.constsResolve_mono (hresi e he), ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cAi.1.name ψ = _
        rw [acvalWith_ne hne]
        exact hleaf ψ
      · have hik : i = k := by omega
        subst hik
        obtain rfl := Option.some.inj (hcAk.symm.trans hcAi)
        refine ⟨⟨Lech.Env.find?_cons_self (.ctorInfo cA.1 p.nP cA.2) env, hlpsC,
          hCD.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcross hcbC
            (fun e he => constsBound_of_constsResolve _ (hidxRes e he)) mpC.base2 hacC⟩,
          fun e he => Expr.constsResolve_mono (hidxRes e he), ?_⟩
        intro ψ
        rw [hacC]
        show acvalWith mp.base2.acval cA.1.name _ cA.1.name ψ = _
        rw [acvalWith_self]
    have hpend' : PendingAt mpC.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp
        p.large idxF dsF esF srcsF ctorsA (k + 1) := by
      intro i cAi hi hcAi
      obtain ⟨hfreshi, htri, hresi, hCDi⟩ := hpend i cAi (by omega) hcAi
      have hne : cA.1.name ≠ cAi.1.name := names_ne_of_nodup hnd hcAk hcAi (by omega)
      refine ⟨?_, Expr.constsResolve_mono htri, fun e he => Expr.constsResolve_mono (hresi e he),
        hCDi.cross (c₀ := .ctorInfo cA.1 p.nP cA.2) hfresh hTC hcross
          (constsBound_of_constsResolve _ htri)
          (fun e he => constsBound_of_constsResolve _ (hresi e he)) mpC.base2 hacC⟩
      rw [Lech.Env.find?_cons]
      split
      · next h => exact absurd h hne
      · exact hfreshi
    have hrest' : ∀ i, rest[i]? = ctorsA[k + 1 + i]? := by
      intro i
      have := hrest (i + 1)
      rwa [show k + (i + 1) = k + 1 + i from by omega] at this
    exact sumCtorsLoop hμ hCtors hnd hlpsT hlpsA hFssParams hFssBelow hiff hFssOkP hIdx hFssOk rest
      (k + 1) _ mpC hrest' (by simp at hk; omega) hE' hfT' hFD' hleafT' hcons' hpend'

/-! ## The assembly -/

set_option maxHeartbeats 12800000 in
/-- **The P carrier survives a direct sum install** — the core, at the
COMPLETED record
(task #195): the stages after the former run on the record the
former's run completed with the result sort (`DirectSumParts.withSort`);
the facts this proof needs about that record are exactly the
recogniser's invariants transported to it, the two guards, the former's
`checkConstantVal` run at the block's header (the declared type or its
whnf'd telescope — the proof never asks which), and its telescope. -/
theorem declDirectSumP_core (hμ : μ.verifiedChecks = true) {F : Nat} {env : Env}
    {p : DirectSumParts} {cvTa : ConstantVal} {ctorsA : List (ConstantVal × Nat)}
    {cvRa : ConstantVal} {rhss : List Expr} {cvT : ConstantVal}
    (mp : EnvS2PM V μ env) (hE : Lech.EtaFamiliesClosed env)
    (hProp : p.isProp = (Level.isEquiv p.resSort .zero == some true))
    (hClps : ∀ c ∈ p.ctors, c.1.levelParams = p.cvT.levelParams ∧
      Lech.reservedBasisNames.contains c.1.name = false)
    (helimR : p.large = true → p.elim ∈ p.cvR.levelParams)
    (hRlps : ∀ q ∈ p.cvT.levelParams, q ∈ p.cvR.levelParams)
    (helim : p.large = true → p.resSort.isNeverZero = true ∨ p.ctors.length < 2)
    (hnd : (p.ctors.map (·.1.name)).Nodup)
    (hTname₀ : cvT.name = p.cvT.name) (hTlps₀ : cvT.levelParams = p.cvT.levelParams)
    (hccvT : Lech.checkConstantVal (Lech.fueledOps μ F) env cvT = .ok cvTa)
    (hstripT : ∃ bsT, cvTa.type.stripPis (p.nP + p.nIdx) = some (bsT, .sort p.resSort))
    (hCtors : Lech.checkDirectSumCtors (Lech.fueledOps μ F) env
      ⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩ p.cvT.name
      p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors = .ok ctorsA)
    (hRec : Lech.checkDirectSumRec (Lech.fueledOps μ F)
      (Lech.consSumCtors p.nP ctorsA ⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩)
      p cvTa ctorsA = .ok (cvRa, rhss)) :
    Nonempty (EnvS2PM V μ ⟨.recInfo cvRa p.majorIdx p.rulePrefix
      (Lech.directSumRules p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)
      :: (Lech.consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩).consts⟩) := by
  -- the former
  obtain ⟨bsT, hstripT⟩ := hstripT
  obtain ⟨hfindT, -, -, -, -, -, typeT, -, -, -, -, htrT, -, -, htyT⟩ :=
    Lech.checkConstantVal_inv hccvT
  have hTname : cvTa.name = p.cvT.name := by rw [htyT]; exact hTname₀
  have hlpsT : cvTa.levelParams = p.cvT.levelParams := by rw [htyT]; exact hTlps₀
  have hTtype : cvTa.type = typeT := by rw [htyT]
  obtain ⟨ppsAll, hFD⟩ := formerData_of hμ mp hccvT hstripT
  have hTfresh : env.find? cvTa.name = none := by rw [hTname, ← hTname₀]; exact hfindT
  have hcbT : ConstsBound env cvTa.type :=
    constsBound_of_constsResolve _ (by rw [hTtype]; exact htrT)
  have hfT_I : (⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩ : Env).find? p.cvT.name
      = some (.indInfo cvTa (Lech.directSumCaps p)) := by
    rw [← hTname]; exact Lech.Env.find?_cons_self _ _
  have hProp' : p.isProp = true → (Level.isEquiv p.resSort .zero == some true) = true :=
    fun h => by rw [← hProp]; exact h
  obtain ⟨tfvs, trest, hopT⟩ := openPisAtFvars_of_stripPis_isSome p.nP 0
    (Lech.stripPis_isSome_of_le (Nat.le_add_right _ _) (by rw [hstripT]; rfl))
  have hE_I : Lech.EtaFamiliesClosed ⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩ := by
    intro T'' cvT'' caps hf he hr
    rw [Lech.Env.find?_cons] at hf
    split at hf
    · obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj hf)
      exact absurd he Bool.false_ne_true
    · obtain ⟨cvC', hfC'⟩ := hE T'' cvT'' caps hf he hr
      exact ⟨cvC', Lech.Env.find?_cons_of_fresh hTfresh hfC'⟩
  -- the constructors' runs
  obtain ⟨hlenA, hall⟩ := Lech.checkDirectSumCtors_inv hCtors
  have hrunOf : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∃ c : ConstantVal × Nat, p.ctors[j]? = some c ∧
      cA.1.name = c.1.name ∧ cA.1.levelParams = p.cvT.levelParams ∧
      (⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩ : Env).find? cA.1.name = none ∧
      cA.1.type.constsResolve ⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩ = true ∧
      Lech.checkDirectSumCtor (Lech.fueledOps μ F) env
        ⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩
        p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large c.1 cA.2 cvTa = .ok cA.1 := by
    intro j cA hj
    have hjl : j < p.ctors.length := by
      have := (List.getElem?_eq_some_iff.mp hj).1; omega
    obtain ⟨hnF, hCtor⟩ := hall j (p.ctors[j]) cA (List.getElem?_eq_getElem hjl) hj
    rw [← hnF] at hCtor
    obtain ⟨hccvC, -, -⟩ := Lech.checkDirectSumCtor_shape hCtor
    obtain ⟨hfindC, -, -, -, -, -, typeC, -, -, -, -, htrC, -, -, htyC⟩ :=
      Lech.checkConstantVal_inv hccvC
    refine ⟨p.ctors[j], List.getElem?_eq_getElem hjl, by rw [htyC], ?_, ?_, ?_, hCtor⟩
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
  -- the dummy former: the constructors' readings need a carrier
  -- storing the former
  obtain ⟨mpI₀, hacI₀⟩ := stageSumFormer mp hE hccvT hTname₀ hFD (fun _ => []) (fun _ _ _ => rfl)
    (fun _ _ h => nomatch h) (fun _ _ _ => ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩)
  have hex₀ : ∀ j : Nat, ∃ q : List Expr × ((Name → Nat) → List (Nat × Nat × AVExpr)) ×
      ((Name → Nat) → List AVExpr) × List (Option Nat),
      ∀ cA : ConstantVal × Nat, ctorsA[j]? = some cA →
      (∀ e ∈ q.1, e.constsResolve env = true) ∧
      (∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
        openPisAtFvars p.nP cA.1.type 0 = some (fvsP, crest) ∧
        openPisAtFvars cA.2 crest p.nP = some (xFvs, xrest) ∧
        q.1 = xrest.getAppArgs.drop p.nP) ∧
      CtorDataI mpI₀.base2 p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort p.isProp
        p.large q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    intro j
    cases hj : ctorsA[j]? with
    | none => exact ⟨([], fun _ => [], fun _ => [], []), fun _ h => nomatch h⟩
    | some cA =>
      obtain ⟨c, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
      obtain ⟨idxArgs, ds, Es, srcs, hres, hopen, hCD⟩ :=
        sumCtorData_of hμ mpI₀ hCtor hfT_I hlpsT hstripT
      exact ⟨(idxArgs, ds, Es, srcs), fun cA' h => by
        obtain rfl := Option.some.inj h; exact ⟨hres, hopen, hCD⟩⟩
  let q₀ : Nat → List Expr × ((Name → Nat) → List (Nat × Nat × AVExpr)) ×
      ((Name → Nat) → List AVExpr) × List (Option Nat) := fun j => Classical.choose (hex₀ j)
  let idxF₀ : Nat → List Expr := fun j => (q₀ j).1
  let dsF₀ : Nat → (Name → Nat) → List (Nat × Nat × AVExpr) := fun j => (q₀ j).2.1
  let esF₀ : Nat → (Name → Nat) → List AVExpr := fun j => (q₀ j).2.2.1
  let srcsF₀ : Nat → List (Option Nat) := fun j => (q₀ j).2.2.2
  have hq₀ : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      (∀ e ∈ idxF₀ j, e.constsResolve env = true) ∧
      (∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
        openPisAtFvars p.nP cA.1.type 0 = some (fvsP, crest) ∧
        openPisAtFvars cA.2 crest p.nP = some (xFvs, xrest) ∧
        idxF₀ j = xrest.getAppArgs.drop p.nP) ∧
      CtorDataI mpI₀.base2 p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort p.isProp
        p.large (idxF₀ j) (dsF₀ j) (esF₀ j) (srcsF₀ j) :=
    fun j => Classical.choose_spec (hex₀ j)
  have hdsF₀ : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      CtorDataI mpI₀.base2 p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort p.isProp
        p.large (idxF₀ j) (dsF₀ j) (esF₀ j) (srcsF₀ j) :=
    fun j cA hj => (hq₀ j cA hj).2.2
  have hFD_I₀ : FormerData mpI₀.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll :=
    hFD.cross (c₀ := .indInfo cvTa (Lech.directSumCaps p)) hTfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT mpI₀.base2 hacI₀
  have hleafT₀ : ∀ ψ, mpI₀.base2.acval p.cvT.name ψ
      = directSumTyAV (p.resSort.eval ψ) (ppsAll ψ) [] := by
    intro ψ
    rw [hacI₀, ← hTname, acvalWith_self]
  have hframes₀ : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
          Sat2 V (((dsF₀ j ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V (((dsF₀ j ψ).take p.nP).map (·.2.2)).reverse ρ →
          FieldsOkB (p.resSort.eval ψ) ρ (((dsF₀ j ψ).drop p.nP).map (·.2.2)) ∧
          FieldsValid ρ (((dsF₀ j ψ).drop p.nP).map (·.2.2)) ∧
          (∀ bs : List V, SpineFit ρ (((dsF₀ j ψ).drop p.nP).map (·.2.2)) bs →
            (∀ E ∈ esF₀ j ψ, AnnotOkP V (consList bs ρ) E) ∧
            SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF₀ j ψ) bs))) := by
    intro j cA hj
    obtain ⟨c, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
    obtain ⟨hiff, hfields⟩ := sumCtorFrames hμ mpI₀ hCtor hfT_I hProp' hFD_I₀ (hdsF₀ j cA hj) hleafT₀
    exact ⟨hiff, fun ψ ρ h => ⟨(hfields ψ ρ h).1, (hfields ψ ρ h).2.1, (hfields ψ ρ h).2.2.2⟩⟩
  -- the field-chain facts of a data function
  have hFssFacts : ∀ (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr))
      (esF : Nat → (Name → Nat) → List AVExpr) (srcsF : Nat → List (Option Nat))
      (m : EnvS2Core V ⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩),
      (∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
        CtorDataI m p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort p.isProp
          p.large (idxF j) (dsF j) (esF j) (srcsF j)) →
      (∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
        (∀ (ψ : Name → Nat) (ρ : Nat → V),
          Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
            Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
        (∀ (ψ : Name → Nat) (ρ : Nat → V),
          Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
            FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
            FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
            (∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
              (∀ E ∈ esF j ψ, AnnotOkP V (consList bs ρ) E) ∧
              SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF j ψ) bs)))) →
      (∀ ψ₁ ψ₂ : Name → Nat, (∀ q ∈ p.cvT.levelParams, ψ₁ q = ψ₂ q) →
        fssOf p.nP (ctorDataList dsF esF ψ₁ ctorsA 0) = fssOf p.nP (ctorDataList dsF esF ψ₂ ctorsA 0) ∧
        essOf (ctorDataList dsF esF ψ₁ ctorsA 0) = essOf (ctorDataList dsF esF ψ₂ ctorsA 0)) ∧
      (∀ ψ : Name → Nat, ∀ Fs ∈ fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0), FieldsBelow p.nP Fs) ∧
      (∀ ψ : Name → Nat, ∀ Fs ∈ rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
        (essOf (ctorDataList dsF esF ψ ctorsA 0)), FieldsBelow (p.nP + p.nIdx) Fs) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
        SumFieldsOkB (p.resSort.eval ψ) ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) ∧
        SumFieldsValid ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V), Sat2 V ((ppsAll ψ).map (·.2.2)).reverse ρ →
        SumFieldsOkB (p.resSort.eval ψ) ρ
          (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
            (essOf (ctorDataList dsF esF ψ ctorsA 0))) ∧
        SumFieldsValid ρ
          (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
            (essOf (ctorDataList dsF esF ψ ctorsA 0)))) := by
    intro idxF dsF esF srcsF m hCDs hframes
    have hcd : ∀ ψ i cd, (ctorDataList dsF esF ψ ctorsA 0)[i]? = some cd →
        ∃ cA, ctorsA[i]? = some cA ∧ cd = (cA.1.name, cA.2, dsF i ψ, esF i ψ) := by
      intro ψ i cd hi
      rw [ctorDataList_getElem?, Nat.zero_add] at hi
      cases h : ctorsA[i]? with
      | none => rw [h] at hi; exact nomatch hi
      | some cA => rw [h] at hi; exact ⟨cA, rfl, (Option.some.inj hi).symm⟩
    have hFsjD : ∀ ψ j cA, ctorsA[j]? = some cA →
        (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)).getD j [] = ((dsF j ψ).drop p.nP).map (·.2.2) := by
      intro ψ j cA hj
      rw [List.getD_eq_getElem?_getD, fssOf_getElem?, ctorDataList_getElem?, hj, Nat.zero_add]; rfl
    have hEsjD : ∀ ψ j cA, ctorsA[j]? = some cA →
        (essOf (ctorDataList dsF esF ψ ctorsA 0)).getD j [] = esF j ψ := by
      intro ψ j cA hj
      rw [List.getD_eq_getElem?_getD, essOf_getElem?, ctorDataList_getElem?, hj, Nat.zero_add]; rfl
    have hlenFs : ∀ ψ, (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)).length = ctorsA.length :=
      fun ψ => by rw [fssOf_length, ctorDataList_length]
    have hOkP : ∀ (ψ : Name → Nat) (ρ : Nat → V), Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ →
        SumFieldsOkB (p.resSort.eval ψ) ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) ∧
        SumFieldsValid ρ (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) := by
      intro ψ ρ hρ
      constructor
      · intro Fs hFs
        obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
        obtain ⟨cA, hiA, rfl⟩ := hcd ψ i cd hi
        exact ((hframes i cA hiA).2 ψ ρ (((hframes i cA hiA).1 ψ ρ).mp hρ)).1
      · intro Fs hFs
        obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
        obtain ⟨cA, hiA, rfl⟩ := hcd ψ i cd hi
        exact ((hframes i cA hiA).2 ψ ρ (((hframes i cA hiA).1 ψ ρ).mp hρ)).2.1
    refine ⟨fun ψ₁ ψ₂ hφ => ?_, fun ψ Fs hFs => ?_, fun ψ => ?_, hOkP, fun ψ ρ hρ => ?_⟩
    · have hcds : ctorDataList dsF esF ψ₁ ctorsA 0 = ctorDataList dsF esF ψ₂ ctorsA 0 := by
        refine ctorDataList_params fun i hi => ?_
        rw [Nat.zero_add]
        obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
        obtain ⟨-, -, -, hlpsi, -⟩ := hrunOf i cAi hi'
        exact (hCDs i cAi hi').params ψ₁ ψ₂ (fun q hq => hφ q (by rw [← hlpsi]; exact hq))
      rw [hcds]
      exact ⟨rfl, rfl⟩
    · obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
      obtain ⟨cA, hiA, rfl⟩ := hcd ψ i cd hi
      have := (DomsBelow.drop p.nP ((hCDs i cA hiA).below ψ)).fields
      rwa [Nat.zero_add] at this
    · refine rChains_below (Nat.le_refl _) (fun Fs hFs => ?_) (fun j hj => ?_)
      · obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
        obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
        obtain ⟨cA, hiA, rfl⟩ := hcd ψ i cd hi
        have := (DomsBelow.drop p.nP ((hCDs i cA hiA).below ψ)).fields
        rwa [Nat.zero_add] at this
      · rw [hlenFs] at hj
        obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
        rw [hEsjD ψ j cA hjA, hFsjD ψ j cA hjA]
        refine ⟨(hCDs j cA hjA).lenE ψ, fun E hE => ?_⟩
        have := (hCDs j cA hjA).belowE ψ E hE
        rwa [show p.nP + (((dsF j ψ).drop p.nP).map (·.2.2)).length = p.nP + cA.2 from by
          simp [(hCDs j cA hjA).len ψ]]
    · -- the restricted chains at the full frame: the chains at the
      -- parameter frame beneath, the index readings at fitting fields
      have hρP : Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse (shiftE p.nIdx 0 ρ) := by
        have := Sat2_drop hρ p.nIdx
        rw [drop_idx_params (hFD.len ψ)] at this
        rw [shiftE_zero]
        exact this
      obtain ⟨hok, hv⟩ := hOkP ψ _ hρP
      constructor
      · intro Fs' hFs'
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs'
        rw [rChains_getElem?] at hj
        cases hF : (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))[j]? with
        | none => rw [hF] at hj; exact nomatch hj
        | some Fs =>
          cases hEs : (essOf (ctorDataList dsF esF ψ ctorsA 0))[j]? with
          | none => rw [hF, hEs] at hj; exact nomatch hj
          | some Es =>
            rw [hF, hEs] at hj
            obtain rfl := Option.some.inj hj
            have hjn : j < ctorsA.length := by
              have := (List.getElem?_eq_some_iff.mp hF).1; rwa [hlenFs] at this
            obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjn⟩
            have hF' : Fs = ((dsF j ψ).drop p.nP).map (·.2.2) := by
              have := hFsjD ψ j cA hjA; rw [List.getD_eq_getElem?_getD, hF] at this; exact this
            have hE' : Es = esF j ψ := by
              have := hEsjD ψ j cA hjA; rw [List.getD_eq_getElem?_getD, hEs] at this; exact this
            subst hF' hE'
            have hsatC := ((hframes j cA hjA).1 ψ _).mp hρP
            refine FieldsOkB_rChain ((hCDs j cA hjA).lenE ψ) ?_ ?_
            · exact ((hframes j cA hjA).2 ψ _ hsatC).1
            · intro bs hsp E hE
              exact ((((hframes j cA hjA).2 ψ _ hsatC).2.2 bs hsp).1 E hE).1
      · refine rChains_validV hv fun j hj bs hsp E hE => ?_
        rw [hlenFs] at hj
        obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
        rw [hFsjD ψ j cA hjA] at hsp
        rw [hEsjD ψ j cA hjA] at hE
        have hsatC := ((hframes j cA hjA).1 ψ _).mp hρP
        exact ((((hframes j cA hjA).2 ψ _ hsatC).2.2 bs hsp).1 E hE).2
  obtain ⟨hFssParams₀, -, hRBelow₀, -, hFssOk₀⟩ :=
    hFssFacts idxF₀ dsF₀ esF₀ srcsF₀ mpI₀.base2 hdsF₀ hframes₀
  -- the real former
  obtain ⟨mpI, hacI⟩ := stageSumFormer mp hE hccvT hTname₀ hFD
    (fun ψ => rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF₀ esF₀ ψ ctorsA 0))
      (essOf (ctorDataList dsF₀ esF₀ ψ ctorsA 0)))
    (fun ψ₁ ψ₂ hφ => by
      obtain ⟨h1, h2⟩ := hFssParams₀ ψ₁ ψ₂ (fun q hq => hφ q (by rw [hlpsT]; exact hq))
      rw [h1, h2])
    hRBelow₀ hFssOk₀
  -- the constructors' data at the real former, their readings identified
  have hex : ∀ j : Nat, ∃ q : List Expr × ((Name → Nat) → List (Nat × Nat × AVExpr)) ×
      ((Name → Nat) → List AVExpr) × List (Option Nat),
      ∀ cA : ConstantVal × Nat, ctorsA[j]? = some cA →
      (∀ e ∈ q.1, e.constsResolve env = true) ∧
      (∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
        openPisAtFvars p.nP cA.1.type 0 = some (fvsP, crest) ∧
        openPisAtFvars cA.2 crest p.nP = some (xFvs, xrest) ∧
        q.1 = xrest.getAppArgs.drop p.nP) ∧
      CtorDataI mpI.base2 p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort p.isProp
        p.large q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    intro j
    cases hj : ctorsA[j]? with
    | none => exact ⟨([], fun _ => [], fun _ => [], []), fun _ h => nomatch h⟩
    | some cA =>
      obtain ⟨c, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
      obtain ⟨idxArgs, ds, Es, srcs, hres, hopen, hCD⟩ :=
        sumCtorData_of hμ mpI hCtor hfT_I hlpsT hstripT
      exact ⟨(idxArgs, ds, Es, srcs), fun cA' h => by
        obtain rfl := Option.some.inj h; exact ⟨hres, hopen, hCD⟩⟩
  let q : Nat → List Expr × ((Name → Nat) → List (Nat × Nat × AVExpr)) ×
      ((Name → Nat) → List AVExpr) × List (Option Nat) := fun j => Classical.choose (hex j)
  let idxF : Nat → List Expr := fun j => (q j).1
  let dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr) := fun j => (q j).2.1
  let esF : Nat → (Name → Nat) → List AVExpr := fun j => (q j).2.2.1
  let srcsF : Nat → List (Option Nat) := fun j => (q j).2.2.2
  have hq : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      (∀ e ∈ idxF j, e.constsResolve env = true) ∧
      (∃ (fvsP : List Expr) (crest : Expr) (xFvs : List Expr) (xrest : Expr),
        openPisAtFvars p.nP cA.1.type 0 = some (fvsP, crest) ∧
        openPisAtFvars cA.2 crest p.nP = some (xFvs, xrest) ∧
        idxF j = xrest.getAppArgs.drop p.nP) ∧
      CtorDataI mpI.base2 p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort p.isProp
        p.large (idxF j) (dsF j) (esF j) (srcsF j) :=
    fun j => Classical.choose_spec (hex j)
  have hdsF : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      CtorDataI mpI.base2 p.cvT.name p.cvT.levelParams cA.1 p.nP cA.2 p.nIdx p.resSort p.isProp
        p.large (idxF j) (dsF j) (esF j) (srcsF j) :=
    fun j cA hj => (hq j cA hj).2.2
  have hidxEq : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA → idxF j = idxF₀ j := by
    intro j cA hj
    obtain ⟨-, ⟨fvsP, crest, xFvs, xrest, hopC, hopX, hq1⟩, -⟩ := hq j cA hj
    obtain ⟨-, ⟨fvsP', crest', xFvs', xrest', hopC', hopX', hq1'⟩, -⟩ := hq₀ j cA hj
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj (hopC.symm.trans hopC')
    obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ Option.some.inj (hopX.symm.trans hopX')
    rw [hq1, hq1']
  have hdsEq : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA → ∀ ψ,
      (dsF j ψ).drop p.nP = (dsF₀ j ψ).drop p.nP := by
    intro j cA hj ψ
    obtain ⟨c, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
    obtain ⟨-, -, fvsP, crest, tfvs', trest', xFvs, idxArgs', sorts, hopC, -, -, hopX, -, hxres, -, -⟩ :=
      Lech.checkDirectSumCtor_shape hCtor
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
  have hesEq : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA → ∀ ψ,
      esF j ψ = esF₀ j ψ := by
    intro j cA hj ψ
    have h₀ := hdsF₀ j cA hj
    rw [← hidxEq j cA hj] at h₀
    exact CtorDataI.Es_eq hacI hacI₀ hTfresh (hdsF j cA hj) h₀ (hq j cA hj).1 ψ
  have hFssEq : ∀ ψ, fssOf p.nP (ctorDataList dsF₀ esF₀ ψ ctorsA 0)
      = fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0) := by
    intro ψ
    refine fssOf_ctorDataList_congr (k := 0) fun i hi => ?_
    rw [Nat.zero_add]
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    exact (hdsEq i cAi hi' ψ).symm
  have hEssEq : ∀ ψ, essOf (ctorDataList dsF₀ esF₀ ψ ctorsA 0)
      = essOf (ctorDataList dsF esF ψ ctorsA 0) := by
    intro ψ
    refine essOf_ctorDataList_congr (k := 0) fun i hi => ?_
    rw [Nat.zero_add]
    obtain ⟨cAi, hi'⟩ : ∃ cAi, ctorsA[i]? = some cAi := ⟨_, List.getElem?_eq_getElem hi⟩
    exact (hesEq i cAi hi' ψ).symm
  have hleafT_I : ∀ ψ, mpI.base2.acval p.cvT.name ψ
      = directSumTyAV (p.resSort.eval ψ) (ppsAll ψ)
          (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
            (essOf (ctorDataList dsF esF ψ ctorsA 0))) := by
    intro ψ
    rw [hacI, ← hTname, acvalWith_self]
    show directSumTyAV _ _ _ = _
    rw [hFssEq ψ, hEssEq ψ]
  have hFD_I : FormerData mpI.base2 cvTa (p.nP + p.nIdx) p.resSort ppsAll :=
    hFD.cross (c₀ := .indInfo cvTa (Lech.directSumCaps p)) hTfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) hcbT mpI.base2 hacI
  have hframes : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
          Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ) ∧
      (∀ (ψ : Name → Nat) (ρ : Nat → V),
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
          FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
          FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
          (∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
            (∀ E ∈ esF j ψ, AnnotOkP V (consList bs ρ) E) ∧
            SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF j ψ) bs))) := by
    intro j cA hj
    obtain ⟨c, -, -, -, -, -, hCtor⟩ := hrunOf j cA hj
    obtain ⟨hiff, hfields⟩ := sumCtorFrames hμ mpI hCtor hfT_I hProp' hFD_I (hdsF j cA hj) hleafT_I
    exact ⟨hiff, fun ψ ρ h => ⟨(hfields ψ ρ h).1, (hfields ψ ρ h).2.1, (hfields ψ ρ h).2.2.2⟩⟩
  obtain ⟨hFssParams, hFssBelow, -, hFssOkP, hFssOk⟩ :=
    hFssFacts idxF dsF esF srcsF mpI.base2 hdsF hframes
  -- the constructors' conses
  obtain ⟨mpC, hE_C, hfT_C, hFD_C, hleafT_C, hconsAll⟩ := sumCtorsLoop hμ hCtors hndA hlpsT
    (fun cA hcA => by
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
      obtain ⟨-, -, -, hlps, -⟩ := hrunOf j cA hj
      exact hlps)
    (fun ψ₁ ψ₂ hφ => (hFssParams ψ₁ ψ₂ hφ).1) hFssBelow (fun j cA hj => (hframes j cA hj).1) hFssOkP
    (fun j cA hj ψ ρ hρ bs hsp => ((hframes j cA hj).2 ψ ρ hρ).2.2 bs hsp |>.2) hFssOk
    ctorsA 0 _ mpI (fun i => by rw [Nat.zero_add]) (Nat.zero_add _) hE_I hfT_I hFD_I hleafT_I
    (fun i cA hi _ => absurd hi (Nat.not_lt_zero _))
    (fun i cA _ hi => by
      obtain ⟨-, -, -, -, hfresh, htr, -⟩ := hrunOf i cA hi
      exact ⟨hfresh, htr, fun e he => Expr.constsResolve_mono ((hq i cA hi).1 e he), hdsF i cA hi⟩)
  -- the recursor
  have hcf_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      CtorFactsAt mpC.base2 p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF j cA :=
    fun j cA hj => (hconsAll j cA (List.getElem?_eq_some_iff.mp hj).1 hj).1
  have hidxRes_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ∀ e ∈ idxF j, e.constsResolve (Lech.consSumCtors p.nP ctorsA
        ⟨.indInfo cvTa (Lech.directSumCaps p) :: env.consts⟩) = true :=
    fun j cA hj => (hconsAll j cA (List.getElem?_eq_some_iff.mp hj).1 hj).2.1
  have hleafC_C : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA → ∀ ψ,
      mpC.base2.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))) :=
    fun j cA hj => (hconsAll j cA (List.getElem?_eq_some_iff.mp hj).1 hj).2.2
  have hwl : p.large = true → p.resSort.isNeverZero = true ∨ ctorsA.length < 2 := by
    intro hl
    rcases helim hl with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [hlenA]; exact h)
  have hmI : p.majorIdx = p.nP + 1 + ctorsA.length + p.nIdx := by
    simp only [DirectSumParts.majorIdx, DirectSumParts.rulePrefix, hlenA]
  have hrP : p.rulePrefix = p.nP + 1 + ctorsA.length := by
    simp only [DirectSumParts.rulePrefix, hlenA]
  obtain ⟨mp₃, -⟩ := stageSumRec hE_C hμ mpC hmI hrP hRec hstripT hfT_C rfl rfl hlpsT hopT helimR hRlps
    hFD_C hcf_C hidxRes_C hleafT_C hleafC_C (fun j cA hj => (hframes j cA hj).1)
    (fun j cA hj => (hframes j cA hj).2) hFssOk hwl
  exact ⟨mp₃⟩


/-- The direct sum declaration's P step: the run's former stage
completes the record (`checkDirectSumInd_shape`: `p' = p.withSort s`),
the recogniser's invariants transport to it by the `withSort`
projections, and the core does the rest. -/
theorem declDirectSumP (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {p : DirectSumParts} (mp : EnvS2PM V μ env)
    (hE : Lech.EtaFamiliesClosed env) (hdp : Lech.directSumParts? env block = some p)
    (h : Lech.Semantics.DeclDirectSumRun μ F env p env₂) : Nonempty (EnvS2PM V μ env₂) := by
  obtain ⟨hnd, cvTa, envI, p', ctorsA, cvRa, rhss, hInd, helim, hCtors, hRec, rfl⟩ := h
  obtain ⟨-, -, -, hClps, -, -, helimR, hRlps, -, -⟩ := Lech.directSumParts?_inv hdp
  obtain ⟨cvT, s, hTname, hTlps, hccvT, hps, rfl, bsT, hstripT⟩ :=
    Lech.checkDirectSumInd_shape hInd
  subst hps
  refine declDirectSumP_core hμ mp hE (p := p.withSort s) rfl ?_ ?_ ?_ helim
    (by simpa using hnd) hTname hTlps hccvT ⟨bsT, hstripT⟩ hCtors hRec
  · simpa using hClps
  · simpa using helimR
  · simpa using hRlps

end Lech.SetP
