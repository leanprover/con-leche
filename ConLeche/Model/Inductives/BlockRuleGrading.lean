module

public import ConLeche.Verify.Inductives.RecStage
public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockModel
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockFieldRead
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.BlockLfpHoles

public section

/-!
# The rule frame's GRADING, at the run

`blockRuleHokA_of_run` (`BlockRecPreRun.lean` §40.12) assembles the
grading of a rule frame's three segments — the recursor's prefix
domains, the constructor's field domains and the `ih` openers' domains
— from three producers; the prefix and field segments' are elsewhere.
The third segment's input `hIent` is PER KEY and has two halves:

* the KEY-STATIC half (the field index, the field's telescope, the
  opener's reading as a Π-tower over the guarded call's conclusion) is
  `blockIhOpenerDom_run` read against the constructor's record;
* the FRAME-DEPENDENT half (`hR`: the call's conclusion is graded;
  `h0`: at a `Prop` elimination it is a truth value) needs the CALLEE
  recursor's type to FIT at the call's spine.  That fit: the
  prefix is the family's shared prefix, the index values fit the
  TARGET member's telescope through the recursive slot's `SlotFit`
  (`BlockModelAt.idxFit`) and then the callee's own index binders
  through stage (b'')'s converse (`blockRecIdxConv_run`), and the
  applied field lies in the member's former applied there
  (`interp_of_major_reading`).

**The frame.**  Every statement here is at the frame the segment
quantifies: a prefix fitting the recursor's prefix domains, fields
fitting the constructor's field domains, and the `ih` values already
bound.  Nothing is stated at an arbitrary frame.
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

/-! ## 1. Fits of a Π-tower reading, from `SpineFit` -/

section TowerFits

/-- **A value spine fitting a Π-tower's domains is a `TeleFit` of the
tower**, with the body at the extended frame as residual. -/
theorem teleFit_mkPisAV_of_spineFit {B : AnnotTerm} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {bs : List V},
      SpineFit ρ (tl.map (·.2.2)) bs →
      TeleFit V ρ (mkPisAV tl B) bs (interp V (consList bs ρ) B)
  | [], ρ, [], _ => by
    show TeleFit V ρ B [] (interp V ρ B)
    exact TeleFit.nil
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | d :: tl, ρ, b :: bs, h => by
    rw [consList_cons]
    exact TeleFit.cons h.1 (teleFit_mkPisAV_of_spineFit h.2)

/-- **A `SpineFit` of a Π-tower's domains at the readings of a spine is
a `TeleFitPA` of the tower at the spine** — `spineFit_of_teleFitPA`'s
converse. -/
theorem teleFitPA_mkPisAV_of_spineFit {pds : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm}
    {ρ : Nat → V} {ws : List AnnotTerm} (hlen : ws.length = pds.length)
    (hsp : SpineFit ρ (pds.map (·.2.2)) (ws.map (interp V ρ))) :
    ∃ rest, TeleFitPA V ρ (mkPisAV pds b) ws rest := by
  have htele := piTeleAV_of_stripPisAV (stripPisAV_mkPisAV pds b)
  refine ⟨_, teleFitPA_of_tower pds.length htele hlen fun n hn => ?_⟩
  have hn' : n < (pds.map (·.2.2)).length := by rw [List.length_map]; exact hn
  have hm := FixKI.spineFit_getD_mem' hsp hn'
  have hwn : n < ws.length := by omega
  have e1 : (ws.map (interp V ρ)).getD n pt = interp V ρ (ws.getD n default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hwn,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hwn]
    rfl
  have e2 : (ws.map (interp V ρ)).take n = (ws.take n).map (interp V ρ) := by
    rw [List.map_take]
  have e3 : (pds.map (·.2.2)).reverse.getD (pds.length - 1 - n) default
      = (pds.map (·.2.2)).getD n default := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by rw [List.length_map]; omega),
      List.length_map, show pds.length - 1 - (pds.length - 1 - n) = n from by omega,
      ← List.getD_eq_getElem?_getD]
  rw [e1, e2] at hm
  rw [e3, chain, consN_eq_consList]
  exact hm

/-- **A telescope bounded at its own depths fits at every frame alike**:
entry `l` reads only the `l` values before it. -/
theorem spineFit_frame_of_bounded {Ds : List AnnotTerm}
    (hb : ∀ l, l < Ds.length → Term.bvarsBelow l ((Ds.getD l default).erase))
    {σ σ' : Nat → V} {vs : List V} (h : SpineFit σ Ds vs) : SpineFit σ' Ds vs := by
  have hlen : vs.length = Ds.length := h.length_eq
  refine spineFit_of_getD hlen fun r hr => ?_
  have hm := FixKI.spineFit_getD_mem' h hr
  have htl : (vs.take r).length = r := by rw [List.length_take]; omega
  rw [interp_congr_below (V := V) (Ds.getD r default) r (consList (vs.take r) σ')
    (consList (vs.take r) σ) (hb r hr) fun i hi => by
      rw [consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega)]]
  exact hm

/-- **An application along a Π-tower lands in its body** — at a
VALID tower, whose `Prop` binders carry the truth-value fibres
`app_mem_piR` asks for. -/
theorem foldl_app_mem_mkPisAV {B : AnnotTerm} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {bs : List V} {f : V},
      AnnotValid V ρ (mkPisAV tl B) → SpineFit ρ (tl.map (·.2.2)) bs →
      f ∈ˢ interp V ρ (mkPisAV tl B) →
      bs.foldl SetTheory.app f ∈ˢ interp V (consList bs ρ) B
  | [], ρ, [], f, _, _, hf => hf
  | [], _, _ :: _, _, _, h, _ => h.elim
  | _ :: _, _, [], _, _, h, _ => h.elim
  | d :: tl, ρ, b :: bs, f, hv, h, hf => by
    have hv' : AnnotValid V ρ (.pi d.1 d.2.1 d.2.2 (mkPisAV tl B)) := hv
    have hf' : f ∈ˢ interp V ρ (.pi d.1 d.2.1 d.2.2 (mkPisAV tl B)) := hf
    rw [AnnotValid_pi] at hv'
    rw [interp_pi] at hf'
    have happ := app_mem_piR hf' h.1 hv'.2.2
    rw [List.foldl_cons, consList_cons]
    exact foldl_app_mem_mkPisAV (hv'.2.1 b h.1) h.2 happ

end TowerFits

/-! ## 2. THE CALL FIT — the callee's binder data at the `ih` call's spine

The `ih` opener for key `(fi, c')` guards a call of recursor `c'` at
the spine

  `x⃗` (the shared rule prefix), the field's index readings under the
  field's own telescope `b⃗`, the field `fs[fi]` applied to `b⃗`,

and its domain's body is the callee's type PEELED along that spine.
Both halves of `hIent`'s frame-dependent part (the peel's grading and,
at a `Prop` elimination, its truth value) rest on ONE fact: the spine's
values FIT the callee's binder data.  This section proves it, in the
block datum's currency, at the constructor's own frame
(`consList (fs.take fi) (consList (x⃗.take nP) σ)`), where the
constructor's typing speaks:

* the index readings fit the TARGET member's index telescope — the
  recursive slot's `SlotFit` (`BlockModelAt.idxFit`), at the fixpoint
  tuple, whose slots agree with the field domains' readings
  (`blockSlot_agree`);
* they then fit the CALLEE's index binders — stage (b'')'s converse
  (`blockRecIdxConv_run`), whose frame is the callee's rule prefix,
  which the key's filter makes the rule's own;
* the applied field lies in the member's former applied at the prefix
  parameters and those indices — the field domain's reading
  (`blockCtorDataI_fieldEntry`) at a valid tower (the constructor's
  own grading) — which is the callee's MAJOR domain
  (`interp_of_major_reading`). -/

section CallFit

variable {envC : Env} {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {d : BlockData V} {names : List Name}

/-- **The call fit.**  Also returned: the field domain's grading at
the constructor frame and the index readings' grading under the
telescope, which the peel's argument grading consumes. -/
theorem blockIhCallFit_of (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d) {lps : List Name}
    {mm i : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM mm)[i]? = some cA) (hcf : BlockCtorFacts mpC.base2 d lps mm i cA)
    (hmmN : mm < d.N) (htgts : ∀ l, l < cA.2 → d.tgts mm i l < d.k)
    {fi : Nat} (hfi : fi < cA.2)
    (hkind : (d.ksF mm i).getD fi .ordinary = .recursive ∨
      (d.ksF mm i).getD fi .ordinary = .reflexive)
    (hrss : ((d.rss mm).getD i []).getD fi false = true)
    {c' : Nat} {r' : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr' : rs[c']? = some r') (htgt : d.tgts mm i fi = p.toBlockShape.recTgtAt c')
    {ψ : Name → Nat} {σ : Nat → V} {xs fs bs : List V}
    (hprefR : SpineFit σ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map
      (·.2.2)).take (p.toBlockShape.rulePrefixAt c')) xs)
    (hps : SpineFit σ (d.params ψ) (xs.take d.nP))
    (hpc : SpineFit σ (((d.dsF mm i ψ).take d.nP).map (·.2.2)) (xs.take d.nP))
    (hfs : SpineFit (consList (xs.take d.nP) σ) ((d.Fss mm ψ).getD i []) fs)
    (hbs : SpineFit (consList (fs.take fi) (consList (xs.take d.nP) σ))
      ((((d.tlss mm ψ).getD i []).getD fi []).map (·.2.2)) bs) :
    WellDenotedV V (consList (fs.take fi) (consList (xs.take d.nP) σ))
        (((d.Fss mm ψ).getD i []).getD fi default) ∧
      ((((d.Fss mm ψ).getD i []).getD fi default)
        = mkPisAV (((d.tlss mm ψ).getD i []).getD fi [])
            (AnnotTerm.mkAppN (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c')) ψ)
              (paramBvarsAt d.nP (d.nP + fi + (((d.tlss mm ψ).getD i []).getD fi []).length)
                ++ ((d.Eiss mm ψ).getD i []).getD fi []))) ∧
      (∀ E ∈ ((d.Eiss mm ψ).getD i []).getD fi [],
        WellDenotedV V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ))) E) ∧
      SpineFit σ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2))
        (xs ++ ((((d.Eiss mm ψ).getD i []).getD fi []).map
            (interp V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ))))
          ++ [bs.foldl SetTheory.app (fs.getD fi pt)])) := by
  have hcd := hcf.2.2
  have hjl : i < (d.ctorsM mm).length := (List.getElem?_eq_some_iff.mp hcj).1
  have hFssD : (d.Fss mm ψ).getD i [] = ((d.dsF mm i ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hnF : ((d.Fss mm ψ).getD i []).length = cA.2 := by
    rw [hFssD, List.length_map, List.length_drop, hcd.len ψ]
    omega
  have hdsLen : (d.dsF mm i ψ).length = d.nP + cA.2 := hcd.len ψ
  have htlE : (d.tlss mm ψ).getD i [] = d.tssF mm i ψ := by
    rw [BlockData.tlss, BlockData.cds, tlssOfR_fixCtorDataList_getD hcj]
  have hEisE : (d.Eiss mm ψ).getD i [] = d.eissF mm i ψ := by
    rw [BlockData.Eiss, BlockData.cds, eissOfR_fixCtorDataList_getD hcj]
  -- the field's domain, and its reading
  have hFget : ((d.Fss mm ψ).getD i []).getD fi default
      = ((d.dsF mm i ψ).getD (d.nP + fi) default).2.2 := by
    rw [hFssD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hentry := blockCtorDataI_fieldEntry hcd ψ hfi hkind
  have hTof : d.memberName (d.tgts mm i fi) = d.memberName (p.toBlockShape.recTgtAt c') := by
    rw [htgt]
  have hDom : ((d.Fss mm ψ).getD i []).getD fi default
      = mkPisAV (((d.tlss mm ψ).getD i []).getD fi [])
          (AnnotTerm.mkAppN (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c')) ψ)
            (paramBvarsAt d.nP (d.nP + fi + (((d.tlss mm ψ).getD i []).getD fi []).length)
              ++ ((d.Eiss mm ψ).getD i []).getD fi [])) := by
    rw [hFget, hentry, htlE, hEisE, ← hTof]
  -- the field domain is graded at the constructor's frame (its own tower)
  have hfs' : SpineFit (consList (xs.take d.nP) σ) (((d.dsF mm i ψ).drop d.nP).map (·.2.2)) fs := by
    rw [← hFssD]; exact hfs
  have hfsl : fs.length = cA.2 := by rw [hfs.length_eq, hnF]
  have hDwd : WellDenotedV V (consList (fs.take fi) (consList (xs.take d.nP) σ))
      (((d.Fss mm ψ).getD i []).getD fi default) := by
    have hsplit : ((d.dsF mm i ψ).take (d.nP + fi)).map (fun d : Nat × Nat × AnnotTerm => d.2.2)
        = ((d.dsF mm i ψ).take d.nP).map (·.2.2)
          ++ (((d.dsF mm i ψ).drop d.nP).take fi).map (·.2.2) := by
      rw [← List.map_append, List.take_add]
    have hfit : SpineFit σ (((d.dsF mm i ψ).take (d.nP + fi)).map (·.2.2))
        (xs.take d.nP ++ fs.take fi) := by
      rw [hsplit]
      exact SpineFit.append hpc (by rw [List.map_take]; exact spineFit_take_any hfs' fi)
    have hq := towerDom_graded_of_tower (hcd.okTy ψ) (by omega) hfit
    rw [consList_append] at hq
    rw [hFget]
    exact hq
  rw [hDom] at hDwd
  -- under the telescope: the body is graded, so are the index readings
  have hbody : WellDenotedV V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ)))
      (AnnotTerm.mkAppN (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c')) ψ)
        (paramBvarsAt d.nP (d.nP + fi + (((d.tlss mm ψ).getD i []).getD fi []).length)
          ++ ((d.Eiss mm ψ).getD i []).getD fi [])) :=
    ⟨(WellDenoted_mkPisAV_inv hDwd.1).2 bs hbs, (AnnotValid_mkPisAV_inv hDwd.2).2 bs hbs⟩
  have hEwd : ∀ E ∈ ((d.Eiss mm ψ).getD i []).getD fi [],
      WellDenotedV V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ))) E :=
    fun E hE => WellDenotedV_mkAppN_args _ hbody E (List.mem_append_right _ hE)
  refine ⟨by rw [hDom]; exact hDwd, hDom, hEwd, ?_⟩
  -- the prefix, the parameters and the lengths
  obtain ⟨hnPle', hmemk', hmI, hlenRds, hmajRead⟩ := blockRecMajor_run hμ mpC h hmr hr' ψ
  have hxlen : xs.length = p.toBlockShape.rulePrefixAt c' := by
    rw [hprefR.length_eq, List.length_take, List.length_map, hlenRds]; omega
  have hasLen : (xs.take d.nP).length = d.nP := by
    rw [List.length_take, hxlen]; omega
  have hsat : Sat V (d.params ψ).reverse (consList (xs.take d.nP) σ) := d.satOfSpine hps
  -- the fixpoint tuple, and an index tuple of the constructor's member
  have hX := lfpTuple_mem (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) σ))
    (d.Φ ψ (consList (xs.take d.nP) σ))
  have hres := hM.resIdxFit ψ _ hsat mm hmmN i hjl fs hfs
  have ht : tupW (d.uM mm ψ)
        (((d.Ess mm ψ).getD i []).map (interp V (consList fs (consList (xs.take d.nP) σ))))
      ∈ˢ d.idx ψ (consList (xs.take d.nP) σ) mm := tupW_mem hres
  -- the earlier fields fit the SLOTS (the fixpoint's slots are the domains' readings)
  have hfiF : fi ≤ ((d.Fss mm ψ).getD i []).length := by omega
  have hFitsTake : FitsFrom ((d.rss mm).getD i [])
      (d.slotAt ψ (lfpTuple (d.w ψ) d.N (d.idx ψ (consList (xs.take d.nP) σ))
        (d.Φ ψ (consList (xs.take d.nP) σ))) mm i) 0 (consList (xs.take d.nP) σ)
      (((d.Fss mm ψ).getD i []).take fi) (fs.take fi) := by
    refine fitsFrom_of_spineFit (fun l hl bs' hb hrb => ?_) (spineFit_take hfs hfiF)
    have hl' : l < fi := by rw [List.length_take] at hl; omega
    have htk : (((d.Fss mm ψ).getD i []).take fi).take l = ((d.Fss mm ψ).getD i []).take l := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hl')]
    have hgt : (((d.Fss mm ψ).getD i []).take fi).getD l default
        = ((d.Fss mm ψ).getD i []).getD l default := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hl',
        ← List.getD_eq_getElem?_getD]
    rw [htk] at hb
    rw [Nat.zero_add] at hrb ⊢
    rw [hgt]
    exact blockSlot_agree hM hcj hcf hasLen hps htgts hmmN hjl ht hX l
      (by omega) bs' hb hrb
  -- the recursive slot's `SlotFit`: the index readings fit the TARGET's telescope
  have hSF := hM.idxFit ψ _ hsat _ hX mm hmmN _ ht i hjl fi (by omega) hrss (fs.take fi)
    hFitsTake
  have hisfit : SpineFit (consList (xs.take d.nP) σ) (d.IdsM (p.toBlockShape.recTgtAt c') ψ)
      ((((d.Eiss mm ψ).getD i []).getD fi []).map
        (interp V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ))))) := by
    have hq := (hSF.2.2 bs hbs).2
    rw [consList_append, htgt] at hq
    exact hq
  -- THE CONVERSE: the index values fit the CALLEE's index binders
  have hlenIds := blockMembers_IdsM_length hmr hmemk' ψ
  have hislen : ((((d.Eiss mm ψ).getD i []).getD fi []).map
      (interp V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ))))).length
      = d.nIdxAt (p.toBlockShape.recTgtAt c') := by
    rw [hisfit.length_eq, hlenIds]
  have hidxR := blockRecIdxConv_run hμ mpC h hmr hr' ψ σ xs _ hprefR hisfit
  rw [hlenIds] at hidxR
  -- the applied field lies in the member's former applied
  have hbl : bs.length = (((d.tlss mm ψ).getD i []).getD fi []).length := by
    rw [hbs.length_eq, List.length_map]
  have hmemF : fs.getD fi pt ∈ˢ interp V (consList (fs.take fi) (consList (xs.take d.nP) σ))
      (mkPisAV (((d.tlss mm ψ).getD i []).getD fi [])
        (AnnotTerm.mkAppN (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c')) ψ)
          (paramBvarsAt d.nP (d.nP + fi + (((d.tlss mm ψ).getD i []).getD fi []).length)
            ++ ((d.Eiss mm ψ).getD i []).getD fi []))) := by
    have hq := FixKI.spineFit_getD_mem' hfs (l := fi) (by omega)
    rw [hDom] at hq
    exact hq
  have hmaj0 := foldl_app_mem_mkPisAV hDwd.2 hbs hmemF
  have hBv : interp V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ)))
      (AnnotTerm.mkAppN (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c')) ψ)
        (paramBvarsAt d.nP (d.nP + fi + (((d.tlss mm ψ).getD i []).getD fi []).length)
          ++ ((d.Eiss mm ψ).getD i []).getD fi []))
      = (xs.take d.nP ++ (((d.Eiss mm ψ).getD i []).getD fi []).map
          (interp V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ))))).foldl
          SetTheory.app
          (interp V σ (mpC.base2.acval (d.memberName (p.toBlockShape.recTgtAt c')) ψ)) := by
    have hL : consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ))
        = consList (xs.take d.nP ++ fs.take fi ++ bs) σ := by
      simp only [consList_append]
    have hLlen : (xs.take d.nP ++ fs.take fi ++ bs).length
        = d.nP + fi + (((d.tlss mm ψ).getD i []).getD fi []).length := by
      rw [List.length_append, List.length_append, hasLen, List.length_take, hfsl, hbl]
      omega
    have hpb : (paramBvarsAt d.nP (d.nP + fi + (((d.tlss mm ψ).getD i []).getD fi []).length)).map
        (interp V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ))))
        = xs.take d.nP := by
      rw [hL, map_bvarAt_take (hD := hLlen.symm) (by rw [hLlen]; omega), List.append_assoc,
        List.take_left' hasLen]
    rw [interp_mkAppN, foldl_app_map, List.map_append, hpb,
      acval_interp_closed mpC.base2 _ ψ _ σ]
  rw [hBv] at hmaj0
  -- which is the callee's MAJOR domain
  have hmaj : bs.foldl SetTheory.app (fs.getD fi pt) ∈ˢ interp V
      (consList (xs ++ (((d.Eiss mm ψ).getD i []).getD fi []).map
        (interp V (consList bs (consList (fs.take fi) (consList (xs.take d.nP) σ))))) σ)
      (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2)).getD
        (p.toBlockShape.majorIdxAt c') default) := by
    have hget : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map
          (·.2.2)).getD (p.toBlockShape.majorIdxAt c') default
        = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').getD
          (p.toBlockShape.majorIdxAt c') default).2.2 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlenRds]; omega)]
      rfl
    rw [hget, hmajRead, hmI, interp_of_major_reading hxlen hislen hnPle'
      (fun ρ₁ ρ₂ => acval_interp_closed mpC.base2 _ ψ ρ₁ ρ₂)]
    exact hmaj0
  -- the whole spine fits the callee's binder data
  have hsplitL : (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2)
      = ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2)).take
          (p.toBlockShape.rulePrefixAt c'))
        ++ ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2)).drop
          (p.toBlockShape.rulePrefixAt c')).take (d.nIdxAt (p.toBlockShape.recTgtAt c'))))
        ++ [((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2)).getD
          (p.toBlockShape.majorIdxAt c') default] := by
    have hlen : ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map
        (·.2.2)).length = p.toBlockShape.rulePrefixAt c' + d.nIdxAt (p.toBlockShape.recTgtAt c')
          + 1 := by
      rw [List.length_map, hlenRds, hmI]
    rw [hmI]
    generalize ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2)) = L
      at hlen ⊢
    generalize p.toBlockShape.rulePrefixAt c' = a at hlen ⊢
    generalize d.nIdxAt (p.toBlockShape.recTgtAt c') = b at hlen ⊢
    rw [← List.take_add]
    have hd : L.drop (a + b) = [L.getD (a + b) default] := by
      rw [List.drop_eq_getElem_cons (by omega), List.drop_of_length_le (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    rw [← hd, List.take_append_drop]
  rw [hsplitL, ← List.append_assoc]
  exact SpineFit.append (SpineFit.append hprefR hidxR) ⟨hmaj, trivial⟩

end CallFit

/-! ## 3. THE GRADING — `blockRuleHokA_of_run` at the run, every rule

The statement is the rule frame's GRADING (G), the spelling
`blockRecEqs_valid_seam` and `blockRuleDataB_seam` take (`declBlock_run`
pays both with it): every entry of the three segments
`pdoms ++ fdoms ++ ihdoms` of every rule is graded at every frame
fitting the entries before it.  The prefix and field segments are
`blockRuleHokA_of_run`'s own; the `ih` segment's `hIent` is produced
here per key — its static half from `blockIhOpenerDom_run` and the
constructor's record, its frame-dependent half from §2's call fit. -/

section Grading

variable {envC : Env} {mpC : EnvModelM V μ envC} {p : ConLeche.BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
  {names : List Name} {d : BlockData V}

/-- **The rule frame's grading on its PREFIX and FIELDS, at the run**
(kind-free): `blockRuleHokA_of_run` with no `ih` segment, fed the
constructor's reading record at the rule's member — its former, the
former's data, the stored type's reading and its length, the parameter
frames — and §27's field-domain spelling.  The `ih` segment of the frame
is the check's own (`tgtIhsAV`) and is graded by the walk. -/
theorem blockRuleHokPF_run
    (hμ : μ.verifiedChecks = true)
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}
    (h : ConLeche.RecStageOk μ F envC p cvTas ctorsAs rs)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
    (hS : BlockCtorsStage (V := V) μ F d p.lps cvTas p.toBlockShape isRec A fssZ envI
      p.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d p.lps cvTas p.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d p.toBlockShape cvTas) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∀ l, l < p.toBlockShape.rulePrefixAt j + cA.2 →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i).getD l default) := by
  intro j r hr i cA hcA ψ l hl σ' ys hys
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hir : i < r.2.2.2.length := (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[i]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [recStage_rulesLen h hr]; exact hir)⟩
  obtain ⟨ms, hms, hctA, -⟩ := recStage_ctorsAt h hr
  have hmemk : p.toBlockShape.recTgtAt j
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
    (blockRecMajor_run (V := V) hμ mpC h hmr hr (fun _ => 0)).2.1
  have hctM : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt j) = r.2.2.2 := by
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt j))[i]? = some cA := by rw [hctM]; exact hcA
  have hcd := blockCtorData_of_core hcore hcj
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStage_tyAt h hr
  have hcvTa := TE.hcvTa
  have hnP := TE.nP_le
  obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ TE.cvTa hcvTa
  have hframes := (hS.frames _ hmemk i cA hcj).1 ψ
  have ho : p.toBlockShape.rulePrefixAt j = p.nP + (p.toBlockShape.rulePrefixAt j - p.nP) := by
    omega
  have hFE := blockRuleFdomsAV_liftDoms h hr hcA hrhs hcore hmemk hcj hnP rfl ho ψ
  have hq := blockRuleHokA_of_run hμ mpC h hr ψ hcvTa hfT hFD (Nat.le_add_right _ _)
    (hcd.okTy ψ) (hcd.len ψ) hframes ho rfl hFE (I := []) (nR := 0) rfl
    (fun q hq => absurd hq (Nat.not_lt_zero q)) l (by omega) σ' ys
    (by simpa only [List.append_nil] using hys)
  simpa only [List.append_nil] using hq

/-! ## 4. (F) THE TYPED TUPLE'S `ih` FIT

At a tuple typed at the recursor types, the pinned `ih` TERMS — read
at the chain frame, the tuple under the rule's frame — fit the pinned
`ih` openers' DOMAINS.  Per opener it is §3's call once more: the term
is the curried call of the tuple's callee component (`ihFunAV`), a
λ-tower over the SAME binder data as the domain's Π-tower; the two
frames agree below the rule's depth (the telescope and the call's
arguments are bounded there, `ihTeleAtGo_below`, `ihIdxAtM_below`), so
the tower moves to the base frame (`lamTowerA_congr_below`), and at a
leaf the callee component, folded along the call's spine, lands in the
peeled conclusion — `blockRuleIhKey_run`'s third frame fact, at the
component's typing. -/

end Grading

end ConLeche.Model
