module

public import ConLeche.Model.Inductives.PsiBody
import ConLeche.Model.Inductives.FixCtorReads
public section

/-!
# The forward fold `ψ`: the setup, typing and ι (task #279 M-B′ step 3h)

`InvSetup` (ψ⁻¹, `InvFold.lean`) bundled the datum-level hypotheses of
the fold kit over the auxiliary datum and the ψ⁻¹ choice.  `PsiSetup`
is its twin over the CONTAINER's datum `d` (at the level instantiation
the pin names) for the copy's fold: the fold's frame is the block's
parameter frame, `ps` the pins' readings there, the targets are the
copies' carriers at the block's parameters (through `invTgAV`, the same
shape as ψ⁻¹'s containers-at-pins), and the bodies rebuild with the
copy's constructor at ψ's spine (`psiBodyAV`): the field, the kit's
hypothesis, or the transport by the term built for an earlier copy.
Beyond `InvSetup`'s fields it carries the transports' facts — the
transport specification `via` per field, the transports' targets
`TgV`, the ONE fact each transport consumes of the earlier copy's
term (`hvia`), the transports' well-denotedness (`hviaWD`), their
telescope bits, and the `NoBVar` facts over the REPLACED positions —
and the constructor's tower at the TRANSPORTED domains (`CtorAtDoms`)
in place of `CtorAtPins`.

From it, as for ψ⁻¹: the kit's per-constructor bundle (`hmin`, through
`psiBody_leaf`), the prefix fit, **`fold_mem`** (ψ is typed: the
container's recursor at the choice's prefix, at index readings and a
major, lands in the copy's carrier at the indices) and **`fold_iota`**
(ι: at a real constructor's index readings and at `C p⃗ f⃗`, the fold is
the head at ψ's VALUES — the fields, the target-fold hypotheses, the
transports).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

namespace IndRepData

variable (d : IndRepData V)

/-- **The ψ choice's setup** over the container's datum `d`. -/
structure PsiSetup {μ : CheckMode} (mp : EnvModelM V μ env) (lps lpsT : List Name)
    (ψ : Name → Nat) (ρ : Nat → V) (ps : List AnnotTerm) (L : Nat → AnnotTerm)
    (pinsT : Nat → List AnnotTerm) (head : Nat → AnnotTerm) (useIh : Nat → Nat → Bool)
    (via : Nat → Nat → Option ViaSpec) (TgV : Nat → AnnotTerm) : Prop where
  hR : ∀ t, t < d.k → RecReadAt mp.base2 d lps t
  hps : ps.length = d.nP
  hpsWD : ∀ p ∈ ps, WellDenotedV V ρ p
  hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ))
  hpps : ((d.ppsM 0 ψ).take d.nP).length = d.nP
  hipsLen : ∀ t, t < d.k → ((d.ipss ψ).getD t []).length = d.nIdxs.getD t 0
  hk : 0 < d.k
  hctorsC : d.ctorsC = []
  hpins : ∀ t, d.pinsOf ψ t = paramBvarsAt d.nP d.nP
  hview : ∀ J, d.ksR J = d.ksF J ∧ d.tgtsR J = d.tgts J ∧ d.eissR J = d.eissF J ∧
    d.tssR J = d.tssF J
  hLS : ∀ t, t < d.k → d.LeafShape mp.base2 ψ t
  hFF : ∀ t, t < d.k → d.FormerFacts mp.base2 ψ t
  hctors : ∀ J cA, d.ctorsA[J]? = some cA →
    FixCtorFactsAt mp.base2 d.env₀ (d.memberName (d.mems J)) lpsT d.nP (d.nIdxAt (d.mems J))
      d.resSort d.isProp d.large d.idxF d.dsF d.esF d.srcsF d.ksF d.fvsPF d.xFvsF d.xrestF d.eissF
      d.tssF J cA (fun i => d.memberName (d.tgts J i)) (fun i => d.nIdxAt (d.tgts J i))
  hpIff : ∀ J cA, d.ctorsA[J]? = some cA → ∀ ρ' : Nat → V,
    Sat V (d.params ψ).reverse ρ' ↔ Sat V (((d.dsF J ψ).take d.nP).map (·.2.2)).reverse ρ'
  hmems : ∀ J, J < d.ctorsA.length → d.mems J < d.k
  htgts : ∀ J i, d.tgts J i < d.k
  hTg : ∀ t, t < d.k → d.TargetOk ψ ρ ps L pinsT t
  huse : ∀ J i, useIh J i = true → i ∈ ConLeche.recIdxOf (d.ksR J)
  /-- the transports' telescope bits are the elimination bit -/
  hbits : ∀ J i Ψ Eis tl, via J i = some (Ψ, Eis, tl) → ∀ dd ∈ tl, dd.2.1 = d.bb ψ
  /-- no later reading mentions a REPLACED position (a hypothesis or a
  transport): the datum's `NoBVar` facts over `replaced`, and the
  transports' own -/
  hnbP : ∀ J cA, d.ctorsA[J]? = some cA →
    ∀ (C : Name) (nF : Nat) (ds : List (Nat × Nat × AnnotTerm)) (Es : List AnnotTerm)
      (recIdx : List Nat) (Eiss : List (List AnnotTerm)) (tls : List (List (Nat × Nat × AnnotTerm))),
      (d.cdsR ψ)[J]? = some (C, nF, ds, Es, recIdx, Eiss, tls) →
      (∀ i, i < nF →
        NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i))
          ((ds.getD (d.nP + i) default).2.2)) ∧
      (∀ i, i < nF → ∀ k dd, (tls.getD i [])[k]? = some dd →
        NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i + k)) dd.2.2) ∧
      (∀ i, i < nF → ∀ E ∈ Eiss.getD i [],
        NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i + (tls.getD i []).length))
          E) ∧
      (∀ E ∈ Es, NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) nF) (d.nP + nF)) E) ∧
      (∀ i, i < nF → ∀ Ψ Eis tl, via J i = some (Ψ, Eis, tl) →
        (∀ k dd, tl[k]? = some dd →
          NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i + k)) dd.2.2) ∧
        ∀ E ∈ Eis, NoBVar (exclP (replP d.nP (replaced (useIh J) (via J)) i) (d.nP + i + tl.length)) E)
  /-- the ONE fact of each transport: at every telescope spine the
  earlier copy's term at the index values and the field lands in the
  transport's target -/
  hvia : ∀ J cA, d.ctorsA[J]? = some cA →
    ∀ (C : Name) (nF : Nat) (ds : List (Nat × Nat × AnnotTerm)) (Es : List AnnotTerm)
      (recIdx : List Nat) (Eiss : List (List AnnotTerm)) (tls : List (List (Nat × Nat × AnnotTerm))),
      (d.cdsR ψ)[J]? = some (C, nF, ds, Es, recIdx, Eiss, tls) →
      ∀ i, i < nF → ∀ Ψ Eis tl, via J i = some (Ψ, Eis, tl) → ∀ fs : List V,
        SpineFit (consList (ps.map (interp V ρ)) ρ) ((ds.drop d.nP).map (·.2.2)) fs →
        ∀ as, SpineFit (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)) (tl.map (·.2.2)) as →
          (Eis.map (interp V (consList as (consList (fs.take i) (consList (ps.map (interp V ρ)) ρ)))) ++
            [as.foldl SetTheory.app (fs.getD i pt)]).foldl SetTheory.app
              (interp V (consList (ps.map (interp V ρ)) ρ) Ψ)
            ∈ˢ (Eis.map (interp V (consList as (consList (fs.take i)
                  (consList (ps.map (interp V ρ)) ρ))))).foldl SetTheory.app (interp V ρ (TgV i))
  /-- the transports are well-denoted at the leaf frame -/
  hviaWD : ∀ J cA, d.ctorsA[J]? = some cA →
    ∀ (C : Name) (nF : Nat) (ds : List (Nat × Nat × AnnotTerm)) (Es : List AnnotTerm)
      (recIdx : List Nat) (Eiss : List (List AnnotTerm)) (tls : List (List (Nat × Nat × AnnotTerm))),
      (d.cdsR ψ)[J]? = some (C, nF, ds, Es, recIdx, Eiss, tls) →
      ∀ fs ihs : List V, fs.length = nF → ihs.length = recIdx.length →
        SpineFit (consList ((ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
            d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
              (d.psiBodyAV head useIh via) J).map (interp V ρ)) ρ)
          ((minorDataTg (d.invTgAV ψ ps L pinsT) (d.tgtsR J) d.nP nF (d.bb ψ) (d.k + J) ds recIdx tls
            Eiss).map (·.2.2))
          (fs ++ ihs) →
        ∀ i Ψ Eis tl, via J i = some (Ψ, Eis, tl) →
          WellDenotedV V (consList (fs ++ ihs)
              (consList ((ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
                d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
                  (d.psiBodyAV head useIh via) J).map (interp V ρ)) ρ))
            (viaEntryAV Ψ nF (d.k + J) i recIdx.length tl Eis)
  /-- the copy's constructor at the transported domains -/
  hCAD : ∀ J cA, d.ctorsA[J]? = some cA →
    d.CtorAtDoms ρ ps (d.invTgAV ψ ps L pinsT) J (head J) cA.2
      (psiDomsAV (d.invTgAV ψ ps L pinsT) TgV (useIh J) (via J) d.nP (d.bb ψ) (d.tgtsR J)
        (d.dsF J ψ) (d.eissR J ψ) (d.tssR J ψ) cA.2)
      (d.esF J ψ)

namespace PsiSetup

variable {μ : CheckMode} {mp : EnvModelM V μ env} {lps lpsT : List Name} {ψ : Name → Nat}
  {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
  {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {via : Nat → Nat → Option ViaSpec}
  {TgV : Nat → AnnotTerm}

/-- Every constructor of the recursor's block is real. -/
theorem nAll_eq (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) :
    d.nAll = d.ctorsA.length := by
  unfold IndRepData.nAll; rw [S.hctorsC]; rfl

theorem ctorsAll_eq (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) :
    d.ctorsAll = d.ctorsA := by
  unfold IndRepData.ctorsAll; rw [S.hctorsC, List.append_nil]

set_option maxHeartbeats 3200000 in
/-- **The kit's per-constructor bundle holds of the ψ choice.** -/
theorem hmin (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) :
    d.KitMin mp.base2 ψ ρ ps (d.invTgAV ψ ps L pinsT) (d.psiBodyAV head useIh via) := by
  intro J hJ C nF ds Es recIdx Eiss tls hcd
  have hcd' := hcd
  unfold IndRepData.cdsR at hcd'
  rw [fixCtorDataList_getElem?, Nat.zero_add, S.ctorsAll_eq] at hcd'
  obtain ⟨cA, hcA, hcAeq⟩ := Option.map_eq_some_iff.mp hcd'
  simp only [Prod.mk.injEq] at hcAeq
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hcAeq
  have hJA : J < d.ctorsA.length := by rw [← S.nAll_eq]; exact hJ
  obtain ⟨hks, htgtR, heiss, htss⟩ := S.hview J
  have hC := S.hctors J cA hcA
  have hD := hC.2.2
  have hmemJ : d.mems J < d.k := S.hmems J hJA
  have htgtR' : ∀ i, d.tgtsR J i = d.tgts J i := fun i => by rw [htgtR]
  have cff := d.ctorFieldFacts_of mp S.hps S.hpins S.hLS S.hFF S.hparams hC (S.hpIff J cA hcA)
    hmemJ (S.htgts J) htgtR'
  obtain ⟨hnb, hnbT, hnbE, hnbEs, hnbV⟩ := S.hnbP J cA hcA _ _ _ _ _ _ _ hcd
  refine ⟨hD.len ψ, hmemJ, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hks] at hi
    obtain ⟨hlt, -⟩ := mem_recIdxOf.mp hi
    rw [hD.ksLen] at hlt
    exact ⟨hlt, by rw [htgtR]; exact S.htgts J i⟩
  · rw [hks, heiss, htss]; exact cff.1
  · exact cff.2
  · refine d.psiBody_leaf S.hps (d.motChoiceAVs_length _ _ _ _) S.hk
      (d.minChoiceAVs_length _ _ _ _ _) hcd (hD.len ψ) hnb hnbT hnbE hnbEs hnbV (S.huse J)
      (S.hbits J) (S.hvia J cA hcA _ _ _ _ _ _ _ hcd) (S.hviaWD J cA hcA _ _ _ _ _ _ _ hcd)
      (S.hCAD J cA hcA) ?_
    intro h0 fs hfs
    have h0' : d.elimL.eval ψ = 0 := (pwBit_zeronessOf ψ d.elimL).mp h0
    rw [d.invTg_fold ψ (cff.2 fs hfs).1]
    have := ((S.hTg (d.mems J) hmemJ).2 _ (cff.2 fs hfs).1).2
    rw [h0', univ_zero] at this
    exact this

/-- **The choice's prefix fits the recursor tower.** -/
theorem prefixFit (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) :
    SpineFit ρ ((d.recPrefixAV mp.base2 ψ).map (·.2.2))
      ((ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
        d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
          (d.psiBodyAV head useIh via) d.nAll).map (interp V ρ)) :=
  d.choice_prefix_fit mp.base2 (d.psiBodyAV head useIh via) S.hps S.hk S.hpps S.hipsLen
    ((S.hR 0 S.hk).tower_wellDenotedV mp ψ ρ)
    (by rw [rebit_map_dom]; exact S.hparams)
    (fun t ht => d.invTg_fact ψ S.hpsWD (S.hTg t ht)) S.hmin

set_option maxHeartbeats 1600000 in
/-- **ψ is typed**: member `t`'s recursor at the choice's prefix, at
index readings and a major fitting the member's motive binder at the
parameter frame, lands in the copy's carrier `L t` at `pinsT t` at the
index values. -/
theorem fold_mem (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) {t : Nat}
    (ht : t < d.k) {is' : List AnnotTerm} {x' : AnnotTerm}
    (hfitM : SpineFit (consList (ps.map (interp V ρ)) ρ) ((d.motDataAV mp.base2 ψ t).map (·.2.2))
      ((is' ++ [x']).map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ)
        (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
          d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
            (d.psiBodyAV head useIh via) d.nAll ++ is' ++ [x']))
      ∈ˢ interp V (consList (is'.map (interp V ρ)) (consList (ps.map (interp V ρ)) ρ))
          (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) := by
  obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms = d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) := ⟨_, rfl⟩
  obtain ⟨Ns, hNs⟩ : ∃ Ns, Ns = d.minChoiceAVs ψ ps Ms (d.psiBodyAV head useIh via) d.nAll :=
    ⟨_, rfl⟩
  have hMsLen : Ms.length = d.k := by rw [hMs]; exact d.motChoiceAVs_length _ _ _ _
  have hNsLen : Ns.length = d.nAll := by rw [hNs]; exact d.minChoiceAVs_length _ _ _ _ _
  have hpre := S.prefixFit
  rw [← hMs, ← hNs] at hpre ⊢
  have h1 := recFold_mem mp (S.hR t ht) ψ hpre
  have hframe : consList ((ps ++ Ms ++ Ns).map (interp V ρ)) ρ
      = consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ := by
    rw [List.map_append, List.map_append]
  rw [hframe] at h1
  have hiff := d.spineFit_recPostAV_iff mp.base2 ψ ht (S.hipsLen t ht) (ρ := ρ)
    (psV := ps.map (interp V ρ)) (MsV := Ms.map (interp V ρ)) (NsV := Ns.map (interp V ρ))
    (by rw [List.length_map, hMsLen]) (by rw [List.length_map, hNsLen])
  have hconc : ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ)
        ((d.recPostAV mp.base2 ψ t).map (·.2.2)) vs →
      ∃ is x, vs = is ++ [x] ∧
        SpineFit (consList (ps.map (interp V ρ)) ρ)
          ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).map (·.2.2)) is ∧
        interp V (consList vs (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
            Ns.map (interp V ρ)) ρ)) (mutualConcAV d.k d.nAll (d.nIdxAt t) t)
          = interp V (consList is (consList (ps.map (interp V ρ)) ρ))
              (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) := by
    intro vs hvs
    have hvsM := (hiff vs).mp hvs
    have hsplit := hvsM
    unfold IndRepData.motDataAV at hsplit
    rw [List.map_append, List.map_singleton, spineFit_append_singleton_iff] at hsplit
    obtain ⟨is, x, rfl, hisFit, -⟩ := hsplit
    refine ⟨is, x, rfl, hisFit, ?_⟩
    have hisLen : is.length = d.nIdxAt t := by
      rw [hisFit.length_eq, List.length_map, rebit_length]; exact S.hipsLen t ht
    rw [← consList_append, ← List.append_assoc,
      interp_mutualConcAV_frame (by rw [List.length_map, hMsLen]) (by rw [List.length_map, hNsLen])
        hisLen ht,
      hMs, d.motChoiceAVs_getD mp.base2 ψ ps _ ρ ht]
    have hfold := d.motChoiceAV_fold mp.base2 (Tg := d.invTgAV ψ ps L pinsT) S.hps (S.hipsLen t ht)
      hvsM
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hfold
    rw [hfold, d.invTg_fold ψ hisFit]
  have h0 : d.bb ψ = 0 → ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ)
        ((d.recPostAV mp.base2 ψ t).map (·.2.2)) vs →
      interp V (consList vs (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
        Ns.map (interp V ρ)) ρ)) (mutualConcAV d.k d.nAll (d.nIdxAt t) t) ∈ˢ (univZero : V) := by
    intro hb0 vs hvs
    obtain ⟨is, x, rfl, hisFit, heq⟩ := hconc vs hvs
    rw [heq]
    have h0' : d.elimL.eval ψ = 0 := (pwBit_zeronessOf ψ d.elimL).mp hb0
    have := ((S.hTg t ht).2 is hisFit).2
    rw [h0', univ_zero] at this
    exact this
  have hfitPost : SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
      Ns.map (interp V ρ)) ρ) ((d.recPostAV mp.base2 ψ t).map (·.2.2)) ((is' ++ [x']).map (interp V ρ)) :=
    (hiff _).mpr hfitM
  have h2 := mkPisAV_fold_mem (m := d.bb ψ) (fun dd hd => by rw [d.mem_recPostAV hd]) h0 h1 hfitPost
  obtain ⟨is, x, heq, hisFit, hconcEq⟩ := hconc _ hfitPost
  rw [hconcEq] at h2
  rw [List.map_append, List.map_singleton] at heq
  obtain ⟨rfl, -⟩ := List.append_inj heq (by
    have h1 := hfitM.length_eq
    rw [List.length_map, List.length_append, List.length_singleton, List.length_map] at h1
    unfold IndRepData.motDataAV at h1
    rw [List.length_append, rebit_length, List.length_singleton, S.hipsLen t ht] at h1
    have h2 := hisFit.length_eq
    rw [List.length_map, rebit_length, S.hipsLen t ht] at h2
    rw [List.length_map]
    omega)
  rw [show ps ++ Ms ++ Ns ++ is' ++ [x'] = (ps ++ Ms ++ Ns) ++ (is' ++ [x']) from by
      simp only [List.append_assoc],
    AnnotTerm.mkAppN_append, interp_mkAppN_map]
  exact h2

set_option maxHeartbeats 1600000 in
/-- **ι of ψ**: at real constructor `J`'s index readings and at
`C p⃗ f⃗`, the fold is the head at ψ's VALUES — the fields, at the
hypothesis positions the target-fold hypotheses (each recursive field's
hypothesis the λ-tower over its telescope of its member's fold at the
same choice), and at the transport positions the transports' values
(`viaVal`). -/
theorem fold_iota (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) (hb : d.bb ψ ≠ 0)
    {J : Nat} {cA : ConstantVal × Nat} (hj : d.ctorsA[J]? = some cA) {fs : List AnnotTerm}
    (hfitC : SpineFit ρ ((d.dsF J ψ).map (·.2.2)) ((ps ++ fs).map (interp V ρ))) :
    interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames (d.mems J)) ψ)
        (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
          d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
            (d.psiBodyAV head useIh via) d.nAll ++
          d.ctorIdxAt ψ J (ps ++ fs) ++
          [AnnotTerm.mkAppN (mp.base2.acval cA.1.name ψ) (ps ++ fs)]))
      = (psiVals (d.bb ψ) (consList (ps.map (interp V ρ)) ρ) (ConLeche.recIdxOf (d.ksR J)) (useIh J)
          (via J) (fs.map (interp V ρ))
          ((ConLeche.recIdxOf (d.ksR J)).map fun i =>
            lamTower (d.bb ψ)
              (consList ((fs.map (interp V ρ)).take i) (consList (ps.map (interp V ρ)) ρ))
              ((d.tssR J ψ).getD i []) fun σ' =>
                (ps.map (interp V ρ) ++
                  (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT)).map (interp V ρ) ++
                  (d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
                    (d.psiBodyAV head useIh via) d.nAll).map (interp V ρ) ++
                  ((d.eissR J ψ).getD i []).map (interp V σ') ++
                  [(Semantics.frameIdx (((d.tssR J ψ).getD i []).length) σ').foldl
                    SetTheory.app ((fs.map (interp V ρ)).getD i pt)]).foldl
                  SetTheory.app (interp V ρ (mp.base2.acval (d.recNames (d.tgtsR J i)) ψ)))).foldl
          SetTheory.app (interp V (consList (ps.map (interp V ρ)) ρ) (head J)) := by
  have hJA : J < d.ctorsA.length := (List.getElem?_eq_some_iff.mp hj).1
  have hjAll : d.ctorsAll[J]? = some cA := by rw [S.ctorsAll_eq]; exact hj
  have hC := S.hctors J cA hj
  have hD := hC.2.2
  have hks : (d.ksR J).length = cA.2 := by rw [(S.hview J).1]; exact hD.ksLen
  have hiota := d.choice_fold_iota mp S.hR (d.psiBodyAV head useIh via) S.hps S.hk S.hpps S.hipsLen hb
    (by rw [rebit_map_dom]; exact S.hparams)
    (fun t ht => d.invTg_fact ψ S.hpsWD (S.hTg t ht)) S.hmin hjAll hJA hC hks
    (S.hpins (d.mems J)) hfitC
  rw [hiota]
  -- the body at the leaf frame
  obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms = d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) := ⟨_, rfl⟩
  obtain ⟨prior, hprior⟩ : ∃ prior, prior = d.minChoiceAVs ψ ps Ms (d.psiBodyAV head useIh via) J :=
    ⟨_, rfl⟩
  obtain ⟨ihs, hihs⟩ : ∃ ihs : List V, ihs = (ConLeche.recIdxOf (d.ksR J)).map fun i =>
      lamTower (d.bb ψ)
        (consList ((fs.map (interp V ρ)).take i) (consList (ps.map (interp V ρ)) ρ))
        ((d.tssR J ψ).getD i []) fun σ' =>
          (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
            (d.minChoiceAVs ψ ps Ms (d.psiBodyAV head useIh via) d.nAll).map (interp V ρ) ++
            ((d.eissR J ψ).getD i []).map (interp V σ') ++
            [(Semantics.frameIdx (((d.tssR J ψ).getD i []).length) σ').foldl
              SetTheory.app ((fs.map (interp V ρ)).getD i pt)]).foldl
            SetTheory.app (interp V ρ (mp.base2.acval (d.recNames (d.tgtsR J i)) ψ)) := ⟨_, rfl⟩
  rw [← hMs, ← hprior, ← hihs]
  have hMsLen : Ms.length = d.k := by rw [hMs]; exact d.motChoiceAVs_length _ _ _ _
  have hpriorLen : prior.length = J := by rw [hprior]; exact d.minChoiceAVs_length _ _ _ _ _
  have hihsLen : ihs.length = (ConLeche.recIdxOf (d.ksR J)).length := by
    rw [hihs, List.length_map]
  have hfsLen : (fs.map (interp V ρ)).length = cA.2 := by
    have := hfitC.length_eq
    rw [List.length_map, List.length_append, List.length_map, hD.len ψ, S.hps] at this
    rw [List.length_map]; omega
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [S.hps]
  have hnFget : (d.ctorsAll.getD J default).2 = cA.2 := by
    rw [List.getD_eq_getElem?_getD, hjAll]; rfl
  have hσb : consList (fs.map (interp V ρ) ++ ihs) (consList ((ps ++ Ms ++ prior).map (interp V ρ)) ρ)
      = consList ihs (consList (fs.map (interp V ρ)) (consList (prior.map (interp V ρ))
          (consList (Ms.map (interp V ρ)) (consList (ps.map (interp V ρ)) ρ)))) := by
    simp only [List.map_append, consList_append]
  have hshiftB : shiftE (d.k + J + cA.2 + (ConLeche.recIdxOf (d.ksR J)).length) 0
      (consList ihs (consList (fs.map (interp V ρ)) (consList (prior.map (interp V ρ))
        (consList (Ms.map (interp V ρ)) (consList (ps.map (interp V ρ)) ρ)))))
      = consList (ps.map (interp V ρ)) ρ := by
    rw [← consList_append, ← consList_append, ← consList_append,
      show d.k + J + cA.2 + (ConLeche.recIdxOf (d.ksR J)).length
        = (Ms.map (interp V ρ) ++ (prior.map (interp V ρ) ++ (fs.map (interp V ρ) ++ ihs))).length from by
          simp only [List.length_append, List.length_map, hMsLen, hpriorLen, hihsLen]
          rw [List.length_map] at hfsLen
          rw [hfsLen]; omega]
    exact shiftE_consList _ _
  unfold IndRepData.psiBodyAV
  rw [hnFget, interp_mkAppN_map, hσb, ← hfsLen,
    interp_psiVarsAV (o := d.k + J) (b := d.bb ψ)
      (by rw [List.length_map, List.length_map, hpriorLen, hMsLen]; omega)
      (by rw [List.length_map, hMsLen]; exact S.hk) (S.huse J) hihsLen (S.hbits J),
    hfsLen, interp_liftN, hshiftB]

set_option maxHeartbeats 1600000 in
/-- **ψ is typed, at VALUE spines**: index values and a major fitting
the member's motive binder at the parameter frame, applied to the fold
at the prefix, land in the copy's carrier at the indices. -/
theorem fold_mem_vals (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) {t : Nat}
    (ht : t < d.k) {is : List V} {x : V}
    (hfitM : SpineFit (consList (ps.map (interp V ρ)) ρ) ((d.motDataAV mp.base2 ψ t).map (·.2.2))
      (is ++ [x])) :
    (is ++ [x]).foldl SetTheory.app
        (interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ)
          (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
            d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
              (d.psiBodyAV head useIh via) d.nAll)))
      ∈ˢ interp V (consList is (consList (ps.map (interp V ρ)) ρ))
          (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) := by
  obtain ⟨Ms, hMs⟩ : ∃ Ms, Ms = d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) := ⟨_, rfl⟩
  obtain ⟨Ns, hNs⟩ : ∃ Ns, Ns = d.minChoiceAVs ψ ps Ms (d.psiBodyAV head useIh via) d.nAll :=
    ⟨_, rfl⟩
  have hMsLen : Ms.length = d.k := by rw [hMs]; exact d.motChoiceAVs_length _ _ _ _
  have hNsLen : Ns.length = d.nAll := by rw [hNs]; exact d.minChoiceAVs_length _ _ _ _ _
  have hpre := S.prefixFit
  rw [← hMs, ← hNs] at hpre ⊢
  have h1 := recFold_mem mp (S.hR t ht) ψ hpre
  have hframe : consList ((ps ++ Ms ++ Ns).map (interp V ρ)) ρ
      = consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ := by
    rw [List.map_append, List.map_append]
  rw [hframe] at h1
  have hiff := d.spineFit_recPostAV_iff mp.base2 ψ ht (S.hipsLen t ht) (ρ := ρ)
    (psV := ps.map (interp V ρ)) (MsV := Ms.map (interp V ρ)) (NsV := Ns.map (interp V ρ))
    (by rw [List.length_map, hMsLen]) (by rw [List.length_map, hNsLen])
  have hconc : ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ)
        ((d.recPostAV mp.base2 ψ t).map (·.2.2)) vs →
      ∃ is x, vs = is ++ [x] ∧
        SpineFit (consList (ps.map (interp V ρ)) ρ)
          ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD t [])).map (·.2.2)) is ∧
        interp V (consList vs (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
            Ns.map (interp V ρ)) ρ)) (mutualConcAV d.k d.nAll (d.nIdxAt t) t)
          = interp V (consList is (consList (ps.map (interp V ρ)) ρ))
              (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0)) := by
    intro vs hvs
    have hvsM := (hiff vs).mp hvs
    have hsplit := hvsM
    unfold IndRepData.motDataAV at hsplit
    rw [List.map_append, List.map_singleton, spineFit_append_singleton_iff] at hsplit
    obtain ⟨is, x, rfl, hisFit, -⟩ := hsplit
    refine ⟨is, x, rfl, hisFit, ?_⟩
    have hisLen : is.length = d.nIdxAt t := by
      rw [hisFit.length_eq, List.length_map, rebit_length]; exact S.hipsLen t ht
    rw [← consList_append, ← List.append_assoc,
      interp_mutualConcAV_frame (by rw [List.length_map, hMsLen]) (by rw [List.length_map, hNsLen])
        hisLen ht,
      hMs, d.motChoiceAVs_getD mp.base2 ψ ps _ ρ ht]
    have hfold := d.motChoiceAV_fold mp.base2 (Tg := d.invTgAV ψ ps L pinsT) S.hps (S.hipsLen t ht)
      hvsM
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at hfold
    rw [hfold, d.invTg_fold ψ hisFit]
  have h0 : d.bb ψ = 0 → ∀ vs : List V,
      SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++ Ns.map (interp V ρ)) ρ)
        ((d.recPostAV mp.base2 ψ t).map (·.2.2)) vs →
      interp V (consList vs (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
        Ns.map (interp V ρ)) ρ)) (mutualConcAV d.k d.nAll (d.nIdxAt t) t) ∈ˢ (univZero : V) := by
    intro hb0 vs hvs
    obtain ⟨is, x, rfl, hisFit, heq⟩ := hconc vs hvs
    rw [heq]
    have h0' : d.elimL.eval ψ = 0 := (pwBit_zeronessOf ψ d.elimL).mp hb0
    have := ((S.hTg t ht).2 is hisFit).2
    rw [h0', univ_zero] at this
    exact this
  have hfitPost : SpineFit (consList (ps.map (interp V ρ) ++ Ms.map (interp V ρ) ++
      Ns.map (interp V ρ)) ρ) ((d.recPostAV mp.base2 ψ t).map (·.2.2)) (is ++ [x]) :=
    (hiff _).mpr hfitM
  have h2 := mkPisAV_fold_mem (m := d.bb ψ) (fun dd hd => by rw [d.mem_recPostAV hd]) h0 h1 hfitPost
  obtain ⟨is₂, x₂, heq, hisFit, hconcEq⟩ := hconc _ hfitPost
  rw [hconcEq] at h2
  obtain ⟨rfl, -⟩ := List.append_inj heq (by
    have h1 := hfitM.length_eq
    rw [List.length_map, List.length_append, List.length_singleton] at h1
    unfold IndRepData.motDataAV at h1
    rw [List.length_append, rebit_length, List.length_singleton, S.hipsLen t ht] at h1
    have h2 := hisFit.length_eq
    rw [List.length_map, rebit_length, S.hipsLen t ht] at h2
    omega)
  exact h2

end PsiSetup

/-- **ψ is typed** — the ONE fact a later copy's transport consumes of
an earlier copy's term: at every index spine and major fitting the
member's motive binder at the parameter frame, the term applied to
them lands in the copy's carrier `L t` at `pinsT t` at the indices. -/
@[expose] def PsiTyped (m : EnvModel V env) (ψ : Name → Nat) (ρ : Nat → V) (ps : List AnnotTerm)
    (L : Nat → AnnotTerm) (pinsT : Nat → List AnnotTerm) (t : Nat) (Ψ : AnnotTerm) : Prop :=
  ∀ (is : List V) (x : V),
    SpineFit (consList (ps.map (interp V ρ)) ρ) ((d.motDataAV m ψ t).map (·.2.2)) (is ++ [x]) →
    (is ++ [x]).foldl SetTheory.app (interp V ρ Ψ)
      ∈ˢ interp V (consList is (consList (ps.map (interp V ρ)) ρ))
          (famAppAV (L t) (pinsT t) d.nP (d.nP + d.nIdxs.getD t 0) (d.nIdxs.getD t 0))

namespace PsiSetup

variable {μ : CheckMode} {mp : EnvModelM V μ env} {lps lpsT : List Name} {ψ : Name → Nat}
  {ρ : Nat → V} {ps : List AnnotTerm} {L : Nat → AnnotTerm} {pinsT : Nat → List AnnotTerm}
  {head : Nat → AnnotTerm} {useIh : Nat → Nat → Bool} {via : Nat → Nat → Option ViaSpec}
  {TgV : Nat → AnnotTerm}

/-- **The fold at the choice's prefix is typed** (`fold_mem_vals`,
packaged). -/
theorem typed (S : d.PsiSetup mp lps lpsT ψ ρ ps L pinsT head useIh via TgV) {t : Nat}
    (ht : t < d.k) :
    d.PsiTyped mp.base2 ψ ρ ps L pinsT t
      (AnnotTerm.mkAppN (mp.base2.acval (d.recNames t) ψ)
        (ps ++ d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT) ++
          d.minChoiceAVs ψ ps (d.motChoiceAVs mp.base2 ψ ps (d.invTgAV ψ ps L pinsT))
            (d.psiBodyAV head useIh via) d.nAll)) :=
  fun _ _ hfit => fold_mem_vals d S ht hfit

end PsiSetup

/-- **A typed earlier term serves a transport**: lifted over the later
copy's container parameters (`nP`), applied to the field's index
values and the field at the telescope's values, it lands in the
earlier copy's target at those index values — `PsiSetup.hvia`'s shape,
with the transport's target `invTgAV ψ' ps' L' pinsT' t'`.  The field's
fit against the earlier container's motive binder (`hfit`) is the
consumer's, from the field's domain reading as that container's family
at the pin (the syntactic-to-datum bridge `R_ψ ⊆ CopyRef` of DESIGN
§M.22). -/
theorem via_of_typed (m : EnvModel V env) {ψ' : Name → Nat} {ρ : Nat → V} {ps' : List AnnotTerm}
    {L' : Nat → AnnotTerm} {pinsT' : Nat → List AnnotTerm} {t' : Nat} {Ψ' : AnnotTerm}
    (hT : d.PsiTyped m ψ' ρ ps' L' pinsT' t' Ψ') {psV : List V} {EisV : List V} {x : V}
    (hfit : SpineFit (consList (ps'.map (interp V ρ)) ρ) ((d.motDataAV m ψ' t').map (·.2.2))
      (EisV ++ [x]))
    (hisFit : SpineFit (consList (ps'.map (interp V ρ)) ρ)
      ((rebit (pwBit ψ' ConLeche.PropWhen.never) ((d.ipss ψ' ).getD t' [])).map (·.2.2)) EisV) :
    (EisV ++ [x]).foldl SetTheory.app (interp V (consList psV ρ) (Ψ'.liftN psV.length 0))
      ∈ˢ EisV.foldl SetTheory.app (interp V ρ (d.invTgAV ψ' ps' L' pinsT' t')) := by
  rw [interp_liftN, shiftE_consList, d.invTg_fold ψ' hisFit]
  exact hT EisV x hfit

end IndRepData

end ConLeche.Model
