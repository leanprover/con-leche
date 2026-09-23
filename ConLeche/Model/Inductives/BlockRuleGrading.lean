module

public import ConLeche.Model.Inductives.BlockRuleRun
public import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockRecIdxConv
import ConLeche.Model.Inductives.BlockModel
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockFieldRead
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.Rules.InferSoundKit

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
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockRuleFrame)

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
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
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

/-- **ONE `ih` KEY of one rule, at the run** — everything the grading
(§3) and the typed tuple's `ih` fit (§4) read about the `q`-th opener:
its key `(fi, c')`, the field entry the key names, the opener's domain
(the moved field telescope over the callee's peeled conclusion
`CihR`), the opener's TERM (the curried call), the record's bounds on
the telescope and the index readings, and — at the call's own frame,
the prefix and the fields fitting the rule's domains and a spine
fitting the field's telescope — the conclusion's grading, its truth
value at a `Prop` elimination, and that the callee's recursor type,
folded along the call's spine, lands in it. -/
theorem blockRuleIhKey_run
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
    (hM : BlockModelAt mpC.base2 names d)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) {i : Nat} {cA : ConstantVal × Nat} (hcA : r.2.2.2[i]? = some cA)
    (ψ : Name → Nat) {q : Nat} (hq : q < (blockRuleFrameAt p rs j i).nR) :
    ∃ (fi c' : Nat) (CihR : AnnotTerm),
      (blockRuleFrameAt p rs j i).ihKeys[q]? = some (fi, c') ∧ c' < rs.length ∧ fi < cA.2 ∧
      ((d.dsF (p.toBlockShape.recTgtAt j) i ψ).getD (p.nP + fi) default).2.2
        = mkPisAV ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi [])
            (AnnotTerm.mkAppN
              (mpC.base2.acval (d.memberName (d.tgts (p.toBlockShape.recTgtAt j) i fi)) ψ)
              (paramBvarsAt p.nP (p.nP + fi + ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length) ++ (d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi [])) ∧
      (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default
        = (mkPisAV (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
            (rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw) ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []))) CihR).liftN q 0 ∧
      (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ j i).getD q default
        = ihFunAV (Level.eval ψ (ConLeche.structElimLevel p.elim p.large)) rs.length c'
            (p.toBlockShape.rulePrefixAt j) cA.2
            (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
              (rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw) ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi [])))
            (((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0 ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
            (AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi + ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)) (teleVarsAV ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)) ∧
      DomsBelow (p.nP + fi) ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []) ∧
      (∀ E ∈ (d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi [], Term.bvarsBelow (p.nP + fi + ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length) E.erase) ∧
      -- the key's block facts
      p.toBlockShape.rulePrefixAt c' = p.toBlockShape.rulePrefixAt j ∧
      ((d.rss (p.toBlockShape.recTgtAt j)).getD i []).getD fi false = true ∧
      d.tgts (p.toBlockShape.recTgtAt j) i fi = p.toBlockShape.recTgtAt c' ∧
      -- the opener's domain: its bound and its reading (`hexI` at `q`)
      Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2 + q)
        ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default).erase ∧
      (∀ x : Expr, (blockRuleFvsIhAt p rs j i)[q]? = some x →
        denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + q)
          (Expr.fvarTypeD x)
          = some ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default)) ∧
      -- the rule's field reads ARE the block's rows
      blockRuleTlAV p rs mpC.base2.acval envC ψ j i fi
        = (d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi [] ∧
      blockRuleEisAV p rs mpC.base2.acval envC ψ j i fi
        = (d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi [] ∧
      (ConLeche.structFieldTeleOf (blockRuleCtorOf rs j i).1.type (blockRuleFrameAt p rs j i).nP
          (blockRuleFrameAt p rs j i).nF fi).length
        = ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length ∧
      (d.tlss (p.toBlockShape.recTgtAt j) ψ).getD i [] = d.tssF (p.toBlockShape.recTgtAt j) i ψ ∧
      (d.Eiss (p.toBlockShape.recTgtAt j) ψ).getD i [] = d.eissF (p.toBlockShape.recTgtAt j) i ψ ∧
      -- the callee's conclusion, peeled along the call's spine
      BlockRuleConclAt (p.toBlockShape.rulePrefixAt c') cA.2
        ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length
        (blockRecTyAV mpC.base2.acval envC rs ψ c')
        (((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
          (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
            ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
        (AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi +
          ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
          (teleVarsAV ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)) CihR ∧
      ∀ (σ : Nat → V) (xs fs : List V),
        SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j) xs →
        SpineFit (consList xs σ) (blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i)
          fs →
        xs.length = p.toBlockShape.rulePrefixAt j ∧ fs.length = cA.2 ∧
        -- the field's telescope, graded at the call's frame
        (FieldsOkB 0 (consList (fs.take fi) (consList (xs.take p.nP) σ))
            (((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map (·.2.2)) ∧
          FieldsValid (consList (fs.take fi) (consList (xs.take p.nP) σ))
            (((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map (·.2.2))) ∧
        -- a spine of the MOVED telescope fits the field's own
        (∀ bs : List V, SpineFit (consList (xs ++ fs) σ)
            ((ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
              (rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw)
                ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []))).map (·.2.2)) bs →
          SpineFit (consList (fs.take fi) (consList (xs.take p.nP) σ))
            (((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map (·.2.2)) bs) ∧
        ∀ bs : List V, SpineFit (consList (fs.take fi) (consList (xs.take p.nP) σ))
          (((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map (·.2.2)) bs →
        WellDenotedV V (consList bs (consList (xs ++ fs) σ)) CihR ∧
          (pwBit ψ (blockRuleFrameAt p rs j i).pw = 0 →
            interp V (consList bs (consList (xs ++ fs) σ)) CihR ∈ˢ (univZero : V)) ∧
          (∀ R : V, R ∈ˢ interp V σ (blockRecTyAV mpC.base2.acval envC rs ψ c') →
            (xs ++ ((((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
              (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
                ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
              ++ [AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi +
                ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
                  (teleVarsAV ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)]).map
                (interp V (consList bs (consList (xs ++ fs) σ)))).foldl SetTheory.app R
              ∈ˢ interp V (consList bs (consList (xs ++ fs) σ)) CihR) ∧
          -- the call's spine fits the callee's binder data (the MOVED fit)
          SpineFit σ ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2))
            (xs ++ (((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
                (interp V (consList bs (consList (fs.take fi) (consList (xs.take p.nP) σ))))
              ++ [bs.foldl SetTheory.app (fs.getD fi pt)])) ∧
          -- the call's arguments, read at the call's frame
          interp V (consList bs (consList (xs ++ fs) σ))
              (AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi +
                ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
                (teleVarsAV ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
            = bs.foldl SetTheory.app (fs.getD fi pt) ∧
          (((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
            (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
                ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)).map
              (interp V (consList bs (consList (xs ++ fs) σ)))
            = ((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
              (interp V (consList bs (consList (fs.take fi) (consList (xs.take p.nP) σ)))) ∧
          -- and are graded there
          (∀ a ∈ ((d.eissF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
            (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
                ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length),
            WellDenotedV V (consList bs (consList (xs ++ fs) σ)) a) ∧
          WellDenotedV V (consList bs (consList (xs ++ fs) σ))
            (AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi +
              ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
              (teleVarsAV ((d.tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)) := by
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hjR : j < rs.length := (List.getElem?_eq_some_iff.mp hr).1
  -- the rule's right-hand side (the kinds cover the constructors)
  have hir : i < r.2.2.2.length := (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[i]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hir)⟩
  -- the member, the constructor and its record
  obtain ⟨ms, hms, hctA, hlenms⟩ := checkBlockRecK_ctorsAt h hr
  have hmemk : p.toBlockShape.recTgtAt j
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k :=
    (blockRecMajor_run (V := V) hμ mpC h hmr hr (fun _ => 0)).2.1
  have hmmN : p.toBlockShape.recTgtAt j
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).N :=
    Nat.lt_of_lt_of_le hmemk (Nat.le_add_right _ _)
  have hctM : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt j) = r.2.2.2 := by
    show ctorsAs.getD _ [] = _
    rw [List.getD_eq_getElem?_getD, hctA]; rfl
  have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt j))[i]? = some cA := by rw [hctM]; exact hcA
  obtain ⟨hfindC, hlpsC, -⟩ := hcore.2.2.2 _ hmemk i cA hcj
  have hcd := blockCtorData_of_core hcore hcj
  have hcf : BlockCtorFacts mpC.base2
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf) p.lps
      (p.toBlockShape.recTgtAt j) i cA := ⟨hfindC, hlpsC, hcd⟩
  have hcdP := hcd
  rw [show (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP = p.nP
    from rfl] at hcdP
  have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
  have hCf : cA.1.type.hasFvar = false := hwfC.1
  have hCb : cA.1.type.looseBVarsBounded 0 = true := hwfC.2.2.2.1
  have hcbC : ConstsBound envC cA.1.type := constsBound_of_constsResolve _ hwfC.2.2.1
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
  have hcvTa := TE.hcvTa
  have hnP := TE.nP_le
  obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ TE.cvTa hcvTa
  have hframes := (hS.frames _ hmemk i cA hcj).1 ψ
  have ho : p.toBlockShape.rulePrefixAt j = p.nP + (p.toBlockShape.rulePrefixAt j - p.nP) := by
    omega
  have hFE := blockRuleFdomsAV_liftDoms h hr hcA hrhs hcore hmemk hcj hnP rfl ho ψ
  -- the `ih` openers: the frame, the tower, its opening and the fused readings
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨hfrP, hfrR, hfrF, -, -, htele, hidxF, hpw⟩ :=
    blockRuleFrameAt_rows (pp := p) hct
  obtain ⟨rbs, ty, concl, -, -, hpis, hopen, -, -, -⟩ :=
    blockRuleResidueData_runP h hr hcA hrhs
  obtain ⟨crestC, hoP, hoF⟩ := hcd.opens
  have hop0 : ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0
      = some ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).fvsPF
            (p.toBlockShape.recTgtAt j) i
          ++ (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xFvsF
            (p.toBlockShape.recTgtAt j) i,
          (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xrestF
            (p.toBlockShape.recTgtAt j) i) :=
    openPisAtFvars_add p.nP hoP (by rw [Nat.zero_add]; exact hoF)
  have hcfv : blockRuleCtorFvs p rs j i
      = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).fvsPF
            (p.toBlockShape.recTgtAt j) i
          ++ (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).xFvsF
            (p.toBlockShape.recTgtAt j) i := by
    rw [blockRuleCtorFvs, hct, hop0]; rfl
  obtain ⟨bsC, bodyC0, hstC, -, -, -⟩ := ConLeche.Verify.openPisAtFvars_stripPis _ hop0
  have hstripC : (cA.1.type.stripPis (p.nP + cA.2)).isSome = true := by rw [hstC]; rfl
  have hks : (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ksF
      (p.toBlockShape.recTgtAt j) i = (blockRuleKsOf p j i).map ConLeche.BlockFieldKind.toRec := by
    rw [blockDataOf_ksF]; rfl
  have hksLen : (blockRuleKsOf p j i).length = cA.2 := by
    have := hcd.ksLen; rw [hks, List.length_map] at this; exact this
  obtain ⟨hihfv, hL2, -, hlb, -, -, -, -, -, -, -, hWt, -⟩ :=
    blockRuleOpened_run mpC h hr hcA hrhs hCf hCb hcbC hstripC hksLen
  have hrow1 : ConLeche.openPisAtFvars ((blockRuleFrameAt p rs j i).nP
      + (blockRuleFrameAt p rs j i).nF) cA.1.type 0
      = some (blockRuleCtorFvs p rs j i,
          ((ConLeche.openPisAtFvars (p.nP + cA.2) cA.1.type 0).map (·.2)).getD default) := by
    rw [hfrP, hfrF, hcfv, hop0]; rfl
  have hrow2 : (cA.1.type.stripPis ((blockRuleFrameAt p rs j i).nP
      + (blockRuleFrameAt p rs j i).nF)).isSome = true := by
    rw [hfrP, hfrF]; exact hstripC
  have hrow3 : ∀ q, (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q).length
      = (ConLeche.structFieldTeleOf cA.1.type (blockRuleFrameAt p rs j i).nP
          (blockRuleFrameAt p rs j i).nF q).length := by
    intro q
    simp only [blockRuleTlAV, hct, hfrP, hfrF, List.length_map, List.length_range]
  have hkeys : (blockRuleFrameAt p rs j i).ihKeys
      = ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt j)
        ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
        (blockRuleKsOf p j i) := rfl
  -- a key's field reads, at the block's rows too
  have hfldM : ∀ q c' : Nat, (q, c') ∈ (blockRuleFrameAt p rs j i).ihKeys →
      q < cA.2 ∧
        FieldReadAt mpC.base2 ψ (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).nF q
          cA.1.type (blockRuleCtorFvs p rs j i) (blockRuleTlAV p rs mpC.base2.acval envC ψ j i q)
          (blockRuleEisAV p rs mpC.base2.acval envC ψ j i q) ∧
        blockRuleTlAV p rs mpC.base2.acval envC ψ j i q
          = ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD q [] ∧
        blockRuleEisAV p rs mpC.base2.acval envC ψ j i q
          = ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
              (p.toBlockShape.recTgtAt j) i ψ).getD q [] := by
    intro q c' hm
    rw [hkeys] at hm
    obtain ⟨hqF, hk⟩ := mem_blockIhKeys_kind hm
    have hF := blockFieldReadAt_of (ψ := ψ) hcdP hop0 (show q < cA.2 by omega)
      (by rw [hks]; exact hk)
    obtain ⟨e1, e2⟩ := fieldReadAt_eq hF
    have eT : blockRuleTlAV p rs mpC.base2.acval envC ψ j i q
        = ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD q [] := by
      rw [e1]; simp only [blockRuleTlAV, hct, hcfv]
    have eE : blockRuleEisAV p rs mpC.base2.acval envC ψ j i q
        = ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
            (p.toBlockShape.recTgtAt j) i ψ).getD q [] := by
      rw [e2]; simp only [blockRuleEisAV, hct, hcfv]
    refine ⟨by omega, ?_, eT, eE⟩
    rw [hfrP, hfrF, hcfv, eT, eE]
    exact hF
  -- the callees' stored types
  have hrecTyM : ∀ c' : Nat,
      ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).hasFvar = false ∧
        ((rs.map (·.1.type)).getD c' (Expr.sort .zero)).looseBVarsBounded 0 = true ∧
        ∃ TVa : AnnotTerm, denoteMeta mpC.base2.acval envC ψ 0
          ((rs.map (·.1.type)).getD c' (Expr.sort .zero)) = some TVa := by
    intro c'
    by_cases hc' : c' < rs.length
    · have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'
      have hg : (rs.map (·.1.type)).getD c' (.sort .zero) = rs[c'].1.type := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
      rw [hg]
      obtain ⟨hf, -, -, hb, -⟩ := ConLeche.checkBlockRecK_facts h _ (List.mem_of_getElem? hr')
      obtain ⟨-, -, -, hread, -⟩ := checkBlockRecK_tyPis hμ mpC h hr' ψ
      exact ⟨hf, hb, _, hread⟩
    · rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by rw [List.length_map]; omega)]
      exact ⟨rfl, rfl, AnnotTerm.sort (Level.eval ψ Level.zero), by simp [denoteMeta]⟩
  have hrow8 : FvarList ((blockRuleFrameAt p rs j i).rP + (blockRuleFrameAt p rs j i).nF)
      (blockRulePrefFvs p.toBlockShape rs j ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse := by
    rw [hfrR, hfrF, List.reverse_append]; exact hL2
  have hpisF : ConLeche.blockIhPis (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).rP
      (blockRuleFrameAt p rs j i).nF (blockRuleFrameAt p rs j i).pw
      (fun c' => (rs.map (·.1.type)).getD c' (.sort .zero)) (blockRuleFrameAt p rs j i).teleOf
      (blockRuleFrameAt p rs j i).idxOf (blockRuleFrameAt p rs j i).ihKeys 0
      (blockRuleResidAt p rs j i) = some (blockRuleIhTeleAt p rs j i) := by
    rw [hfrP, hfrR, hfrF]; exact hpis
  have hopenF : ConLeche.openPisAtFvars (blockRuleFrameAt p rs j i).ihKeys.length
      ((blockRuleIhTeleAt p rs j i).instantiateList (blockRulePrefFvs p.toBlockShape rs j
        ++ blockRuleFieldFvs p.toBlockShape rs j i).reverse)
      ((blockRuleFrameAt p rs j i).rP + (blockRuleFrameAt p rs j i).nF)
      = some (blockRuleFvsIhAt p rs j i, blockRuleBodyOAt p rs j i) := by
    rw [hfrR, hfrF]; exact hopen
  have hopDom := blockIhOpenerDom_run (mT := mpC.base2) (ψ := ψ)
    (o := p.toBlockShape.rulePrefixAt j - p.nP)
    (by rw [hfrR, hfrP]) (by rw [hfrP, hfrR]; omega) hrow1 hCf hCb hrow2
    (by rw [hfrP, hfrF]; exact htele) (by rw [hfrP, hfrF]; exact hidxF) hrow3
    (fun q c' _ hk => ⟨by rw [hfrF]; exact (hfldM q c' (List.mem_of_getElem? hk)).1,
      (hfldM q c' (List.mem_of_getElem? hk)).2.1⟩)
    (fun _ c' _ _ => hrecTyM c') hpisF hihfv hrow8 hopenF
  have hlenFvsIh : (blockRuleFvsIhAt p rs j i).length = (blockRuleFrameAt p rs j i).nR :=
    openPisAtFvars_length _ hopen
  have hexI : ∀ (l : Nat) (x : Expr), (blockRuleFvsIhAt p rs j i)[l]? = some x →
      ∃ A, denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + l)
        (Expr.fvarTypeD x) = some A := by
    intro l x hx
    have hl : l < (blockRuleFrameAt p rs j i).ihKeys.length := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [hlenFvsIh] at this
      exact this
    obtain ⟨_, _, -, -, hread⟩ := hopDom ((blockRuleFrameAt p rs j i).ihKeys[l]).1
      ((blockRuleFrameAt p rs j i).ihKeys[l]).2 l x (List.getElem?_eq_getElem hl) hx
    rw [hfrR, hfrF] at hread
    exact ⟨_, hread⟩
  have hIdomE : blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i
      = readOpenedDoms mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2)
          (blockRuleFvsIhAt p rs j i) := by
    rw [blockRuleIhdomsAV, hct]
  -- the key
  have hqK : q < (blockRuleFrameAt p rs j i).ihKeys.length := hq
  obtain ⟨fi, c', hkeyE⟩ : ∃ fi c', (blockRuleFrameAt p rs j i).ihKeys[q]? = some (fi, c') :=
    ⟨_, _, List.getElem?_eq_getElem hqK⟩
  obtain ⟨x, hx⟩ : ∃ x, (blockRuleFvsIhAt p rs j i)[q]? = some x :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenFvsIh]; exact hq)⟩
  obtain ⟨TVa, CihR, hTVa, hpeel, hread⟩ := hopDom fi c' q x hkeyE hx
  have hmemKey : (fi, c') ∈ (blockRuleFrameAt p rs j i).ihKeys := List.mem_of_getElem? hkeyE
  obtain ⟨hfiC, -, eT, eE⟩ := hfldM fi c' hmemKey
  -- the key's block facts
  obtain ⟨-, hlenR, -⟩ := checkBlockRecK_recNames h
  have hrecTgtsLen : p.recTgts.length = rs.length := by
    show ((List.range p.recs.length).map p.toBlockShape.recTgtAt).length = _
    rw [List.length_map, List.length_range, hlenR]
  have hrecTgts : ∀ e, e < rs.length → p.recTgts.getD e rs.length = p.toBlockShape.recTgtAt e := by
    intro e he
    show ((List.range p.recs.length).map p.toBlockShape.recTgtAt).getD e rs.length = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  have hFssLen : (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
      (p.toBlockShape.recTgtAt j) ψ).getD i []).length = cA.2 := by
    have hFssD : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
        (p.toBlockShape.recTgtAt j) ψ).getD i []
        = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).dsF
          (p.toBlockShape.recTgtAt j) i ψ).drop p.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hcd.len ψ]
    show p.nP + cA.2 - p.nP = cA.2
    omega
  have hkey' : (ConLeche.blockIhKeys (p.toBlockShape.rulePrefixAt j)
      ((List.range p.recs.length).map p.toBlockShape.rulePrefixAt) p.recTgts
      (blockRuleKsOf p j i)).getD q (0, 0) = (fi, c') := by
    rw [← hkeys, List.getD_eq_getElem?_getD, hkeyE]; rfl
  obtain ⟨hc'K, hfiF, hrss, htgtc', hrPs, hkind⟩ :=
    blockIhKey_block_facts (d := blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf)
      (ψ := ψ) (K := rs.length) (mem := p.toBlockShape.recTgtAt) hcj hks hksLen hFssLen
      (fun _ => rfl) hrecTgtsLen hrecTgts hkey' (by rw [← hkeys]; exact hqK)
  have hr' : rs[c']? = some rs[c'] := List.getElem?_eq_getElem hc'K
  have hrPc' : p.toBlockShape.rulePrefixAt c' = p.toBlockShape.rulePrefixAt j := by
    rw [← hrPs, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (by omega)]
    rfl
  -- the opener's domain IS the moved telescope over the call's conclusion
  have hIget : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default
      = (mkPisAV (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
          (rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw)
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []))) CihR).liftN q 0 := by
    have hr1 := readOpenedDoms_reads hexI q x hx
    rw [← hIdomE] at hr1
    rw [hfrR, hfrF] at hread
    have heq := Option.some.inj (hr1.symm.trans hread)
    rw [heq, eT]
  -- the opener's TERM is the curried call
  have hihsGet : (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ j i).getD q default
      = ihFunAV (Level.eval ψ (ConLeche.structElimLevel p.elim p.large)) rs.length c'
          (p.toBlockShape.rulePrefixAt j) cA.2
          (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
            (rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw)
              (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
                (p.toBlockShape.recTgtAt j) i ψ).getD fi [])))
          ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
            (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
              (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
                (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
          (AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi
              + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
                (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
            (teleVarsAV (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
                (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)) := by
    rw [blockRuleIhsRunAV, blockRuleIhsAV, blockRecIhsAt, List.getD_eq_getElem?_getD,
      List.getElem?_map, hkeyE, Option.map_some, Option.getD_some]
    simp only [hct]
    rw [← hrow3 fi, eT, eE, hfrR, hfrF, Nat.add_zero]
  -- the opener's domain: its reading at `q`, and its bound
  have hreadQ : ∀ x' : Expr, (blockRuleFvsIhAt p rs j i)[q]? = some x' →
      denoteMeta mpC.base2.acval envC ψ (p.toBlockShape.rulePrefixAt j + cA.2 + q)
        (Expr.fvarTypeD x')
        = some ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default) := by
    intro x' hx'
    have hr1 := readOpenedDoms_reads hexI q x' hx'
    rw [← hIdomE] at hr1
    exact hr1
  have hIB : Term.bvarsBelow (p.toBlockShape.rulePrefixAt j + cA.2 + q)
      ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default).erase := by
    have hW := openPisAtFvars_typeWScoped _ hopen hWt q x hx
    exact bvarsBelow_of_reading (m := mpC.base2) hW
      (hlb x (List.mem_append_right _ (List.mem_of_getElem? hx))) (hreadQ x hx)
  -- the block's rows, at the constructor
  have htlE : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tlss
      (p.toBlockShape.recTgtAt j) ψ).getD i []
      = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
        (p.toBlockShape.recTgtAt j) i ψ := by
    rw [BlockData.tlss, BlockData.cds, tlssOfR_fixCtorDataList_getD hcj]
  have hEisE : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Eiss
      (p.toBlockShape.recTgtAt j) ψ).getD i []
      = (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
        (p.toBlockShape.recTgtAt j) i ψ := by
    rw [BlockData.Eiss, BlockData.cds, eissOfR_fixCtorDataList_getD hcj]
  have hm : (ConLeche.structFieldTeleOf (blockRuleCtorOf rs j i).1.type
        (blockRuleFrameAt p rs j i).nP (blockRuleFrameAt p rs j i).nF fi).length
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
          (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length := by
    rw [hct, ← hrow3 fi, eT]
  -- the callee's type, its binder data and its conclusion
  obtain ⟨-, -, -, hreadT, hTyE, hrdsLen, -, -, -, hwdTy⟩ :=
    checkBlockRecK_tyPis hμ mpC h hr' ψ
  have hTVaE : TVa = blockRecTyAV mpC.base2.acval envC rs ψ c' := by
    have hg : (rs.map (·.1.type)).getD c' (.sort .zero) = rs[c'].1.type := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, hr']; rfl
    rw [hg] at hTVa
    exact Option.some.inj (hTVa.symm.trans hreadT)
  obtain ⟨hnPle', -, hmI', hlenRds', -⟩ := blockRecMajor_run hμ mpC h hmr hr' ψ
  obtain ⟨hbndR, hconclB⟩ := checkBlockRecK_tyBounds hμ mpC h hr' ψ
  obtain ⟨-, hEl⟩ := blockIhKey_block_lengths (V := V) ψ hcj hcf hfiC hkind
  rw [htgtc'] at hEl
  -- the key's spine, in the frame's own spelling
  have hcon : BlockRuleConclAt (p.toBlockShape.rulePrefixAt c') cA.2
      (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length
      (blockRecTyAV mpC.base2.acval envC rs ψ c')
      ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
        (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
          (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
      (AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi
          + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
        (teleVarsAV (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)) CihR := by
    rw [← hTVaE, hrPc']
    rw [hfrR, hfrF, eT, eE, Nat.add_zero] at hpeel
    exact hpeel
  have hentry := blockCtorDataI_fieldEntry hcdP ψ hfiC hkind
  refine ⟨fi, c', CihR, hkeyE, hc'K, hfiC, hentry, hIget,
    hihsGet, hcdP.tssBelow ψ fi, hcdP.eissBelow ψ fi, hrPc', hrss, htgtc', hIB, hreadQ, eT, eE,
    hm, htlE, hEisE, hcon, ?_⟩
  intro σ xs fs hxs hfs
  -- the frame's lengths and the prefix's split
  have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j).length
      = p.toBlockShape.rulePrefixAt j := blockRulePdomsAV_length hμ mpC h hr ψ
  have hxlen : xs.length = p.toBlockShape.rulePrefixAt j := by rw [hxs.length_eq, hpl]
  have hlenps : (xs.take p.nP).length = p.nP := by rw [List.length_take, hxlen]; omega
  have hms : (xs.drop p.nP).length = p.toBlockShape.rulePrefixAt j - p.nP := by
    rw [List.length_drop, hxlen]
  have hshift : shiftE (p.toBlockShape.rulePrefixAt j - p.nP) 0 (consList xs σ)
      = consList (xs.take p.nP) σ := by
    have hregroup : consList xs σ = consList (xs.drop p.nP) (consList (xs.take p.nP) σ) := by
      rw [← consList_append, List.take_append_drop]
    rw [hregroup, ← hms]
    exact shiftE_consList _ _
  have hfsB0 : SpineFit (consList (xs.take p.nP) σ)
      ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).dsF
        (p.toBlockShape.recTgtAt j) i ψ).drop p.nP).map (·.2.2)) fs := by
    rw [← hshift]
    rw [hFE] at hfs
    exact (spineFit_liftDoms (V := V) _).mp hfs
  have hFssD : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
      (p.toBlockShape.recTgtAt j) ψ).getD i []
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).dsF
        (p.toBlockShape.recTgtAt j) i ψ).drop p.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hfsB : SpineFit (consList (xs.take p.nP) σ)
      (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).Fss
        (p.toBlockShape.recTgtAt j) ψ).getD i []) fs := by
    rw [hFssD]; exact hfsB0
  have hfsl : fs.length = cA.2 := by rw [hfsB.length_eq, hFssLen]
  -- the parameters: the block's, and the constructor's own
  have hps : SpineFit σ
      ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).params ψ)
      (xs.take p.nP) := by
    have ht := spineFit_take hxs (i := p.nP) (by rw [hpl]; exact hnP)
    have hte : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j).take p.nP
        = ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ j).map (·.2.2)).take
          p.nP := by
      rw [blockRulePdomsAV, List.map_take, List.take_take, Nat.min_eq_left hnP]
    rw [hte] at ht
    exact (blockRecParams_run hμ mpC h hmr hr ψ σ _).mp ht
  have hpc := blockRuleParamFit_run hμ mpC h hr ψ hcvTa hfT hFD (Nat.le_add_right _ _)
    (hcd.len ψ) hframes (spineFit_take_any hxs p.nP)
  -- the callee's prefix is the rule's
  have hprefR : SpineFit σ (((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map
      (·.2.2)).take (p.toBlockShape.rulePrefixAt c')) xs := by
    rw [← List.map_take]
    exact blockRecHpref_run hμ mpC h ψ hr hr' hxs
  have htgts : ∀ l, l < cA.2 →
      (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tgts
        (p.toBlockShape.recTgtAt j) i l
      < (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).k := by
    intro l _
    rw [← hN.2.2.2]
    exact hN.2.1 _ i l
  have hxl : xs.length = (xs.take p.nP).length + (p.toBlockShape.rulePrefixAt j - p.nP) := by
    rw [hlenps, hxlen]; omega
  have htake : xs.take (xs.take p.nP).length = xs.take p.nP := by rw [hlenps]
  have hxlen' : xs.length = p.toBlockShape.rulePrefixAt c' := by rw [hrPc', hxlen]
  refine ⟨hxlen, hfsl,
    blockRuleIhTele_graded_of_ctorTower (hcd.okTy ψ) (hcd.len ψ) hfiC hentry hpc hfsB0,
    fun bs hbs => spineFit_ihTeleAtR_rule (ρ := σ) (i := fi) hxl htake hfsl hbs, ?_⟩
  -- THE CORE, at ih level 0: the call at the call's own frame
  intro bs hbsC
  have hbl : bs.length
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length := by
    rw [hbsC.length_eq, List.length_map]
  obtain ⟨hDwd, hDom, hEwd, hfitB⟩ := blockIhCallFit_of hμ mpC h hmr hM hcj hcf hmmN htgts
    hfiC hkind hrss hr' htgtc' hprefR hps hpc hfsB (by rw [htlE]; exact hbsC)
  rw [htlE, hEisE] at hDom
  rw [hEisE] at hEwd hfitB
  have hes : ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
        (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
          (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)).map
        (interp V (consList bs (consList (xs ++ fs) σ)))
      = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
        (interp V (consList bs (consList (fs.take fi) (consList (xs.take p.nP) σ)))) := by
    rw [List.map_map]
    exact List.map_congr_left fun E _ => interp_ihIdxAtM_rule (i := fi) hxl htake hfsl hbl E
  have hmk := interp_fieldApp_rule (ρ := σ) (xs := xs) hfsl hfiC hbl
  -- the call's arguments are graded: the moved index readings ...
  have hEsWd : ∀ a ∈ (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
        (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
        (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
          (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length),
      WellDenotedV V (consList bs (consList (xs ++ fs) σ)) a := by
    intro a ha
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp ha
    exact (wellDenotedV_ihIdxAtM_rule (i := fi) hxl htake hfsl hbl E).mpr (hEwd E hE)
  -- ... and the applied field: the field's value along its own domain
  have hFapWd : WellDenotedV V (consList bs (consList (xs ++ fs) σ))
      (AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi
          + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
        (teleVarsAV (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)) := by
    have hval : interp V (consList bs (consList (xs ++ fs) σ))
        (.bvar (cA.2 - 1 - fi
          + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
        = fs.getD fi pt := by
      rw [consList_ruleFrame]
      have hk : fi < (fs ++ bs).length := by rw [List.length_append]; omega
      have hidx : cA.2 - 1 - fi
          + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length
          = (fs ++ bs).length - 1 - fi := by
        rw [List.length_append, hfsl, hbl]; omega
      rw [hidx, interp_bvarAt hk, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
    have hmemB := FixKI.spineFit_getD_mem' hfsB (l := fi) (by rw [hFssLen]; exact hfiC)
    rw [hDom] at hmemB hDwd
    rw [← hval] at hmemB
    have hTeleFit := teleFit_mkPisAV_of_spineFit
      (B := AnnotTerm.mkAppN (mpC.base2.acval (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk
          uOfD ppsOf |>.memberName (p.toBlockShape.recTgtAt c')) ψ)
        (paramBvarsAt (blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP
          ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).nP + fi
            + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)
          ++ ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi [])) hbsC
    rw [← map_teleVarsAV_interp' hbl (consList (xs ++ fs) σ)] at hTeleFit
    exact (Rules.wellDenotedV_mkAppN_of_fit _
      (f := .bvar (cA.2 - 1 - fi
          + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)) hDwd ⟨trivial, trivial⟩
      (fun x hx => by
        obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
        exact ⟨trivial, trivial⟩) hmemB hTeleFit).1
  refine ⟨?_, fun hb0 => ?_, fun R hR => ?_, hfitB, hmk, hes, hEsWd, hFapWd⟩
  · -- the grading: the callee's tower, fitted at the call's spine and peeled
    have hL : consList bs (consList (xs ++ fs) σ) = consList (xs ++ fs ++ bs) σ := by
      simp only [consList_append]
    have hLlen : (xs ++ fs ++ bs).length
        = p.toBlockShape.rulePrefixAt c' + cA.2
          + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length := by
      rw [List.length_append, List.length_append, hxlen', hfsl, hbl]
    have hpb : (paramBvarsAt (p.toBlockShape.rulePrefixAt c')
        (p.toBlockShape.rulePrefixAt c' + cA.2
          + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)).map
        (interp V (consList bs (consList (xs ++ fs) σ))) = xs := by
      rw [hL, map_bvarAt_take (hD := hLlen.symm) (by rw [hLlen]; omega), List.append_assoc,
        List.take_left' hxlen']
    have hmapS : (paramBvarsAt (p.toBlockShape.rulePrefixAt c')
          (p.toBlockShape.rulePrefixAt c' + cA.2
            + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)
        ++ (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
          (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
          (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)
        ++ [AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi
            + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
          (teleVarsAV (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)]).map
        (interp V (consList bs (consList (xs ++ fs) σ)))
      = xs ++ ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
          (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
          (interp V (consList bs (consList (fs.take fi) (consList (xs.take p.nP) σ))))
        ++ [bs.foldl SetTheory.app (fs.getD fi pt)]) := by
      rw [List.map_append, List.map_append, hpb, hes, List.map_cons, List.map_nil, hmk,
        List.append_assoc]
    -- the fit, moved to the call's frame (the binder data is bounded at its depths)
    have hbnd : ∀ l, l < ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map
        (fun d : Nat × Nat × AnnotTerm => d.2.2)).length →
        Term.bvarsBelow l ((((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map
          (fun d : Nat × Nat × AnnotTerm => d.2.2)).getD l default).erase) := by
      intro l hl
      rw [List.length_map] at hl
      have hq := hbndR l hl
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl] at hq
      exact hq
    have hfit1 : SpineFit (consList bs (consList (xs ++ fs) σ))
        ((blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').map (·.2.2))
        ((paramBvarsAt (p.toBlockShape.rulePrefixAt c')
          (p.toBlockShape.rulePrefixAt c' + cA.2
            + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)
        ++ (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
          (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
          (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)
        ++ [AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi
            + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
          (teleVarsAV (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)]).map
        (interp V (consList bs (consList (xs ++ fs) σ)))) := by
      rw [hmapS]
      exact spineFit_frame_of_bounded hbnd hfitB
    have hSlen : (paramBvarsAt (p.toBlockShape.rulePrefixAt c')
          (p.toBlockShape.rulePrefixAt c' + cA.2
            + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)
        ++ (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF
          (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map
          (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi 0
            (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)
        ++ [AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi
            + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length))
          (teleVarsAV (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
              (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length)]).length
        = (blockRecRdsAV mpC.base2.acval envC p.toBlockShape rs ψ c').length := by
      rw [List.length_append, List.length_append, paramBvarsAt_length, List.length_map,
        List.length_singleton, ← hEisE, hEl, hlenRds', hmI']
    obtain ⟨rest, hTF⟩ := teleFitPA_mkPisAV_of_spineFit
      (b := blockRecConclAV mpC.base2.acval envC p.toBlockShape rs ψ c') hSlen hfit1
    rw [← hTyE] at hTF
    obtain rfl : rest = CihR := Option.some.inj (hTF.peelPis.symm.trans hcon)
    exact teleFitPA_wellDenotedV hTF (hwdTy _) (blockRuleHokC_args hEsWd hFapWd)
  · -- the truth value: the elimination level is zero, and the spine fits
    obtain ⟨us, uOf, -, -, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
    obtain ⟨fvs, conclE, sty, hop, hinf, hens⟩ := hruns c' hc'K
    have hrd : rs.getD c' default = rs[c'] := by
      rw [List.getD_eq_getElem?_getD, hr']; rfl
    rw [hrd] at hop
    have hu0 : (uOf c').eval ψ = 0 := by
      rw [blockRecElimPin_run h hruns ψ hc'K]
      exact (pwBit_zeronessOf ψ _).mp (by rw [← hpw]; exact hb0)
    exact blockRuleIseg_h0_of_conclAt hμ mpC h hr' ψ hop hinf hens hu0 hcon
      (by rw [hlenRds', hmI'])
      (by rw [List.length_map, ← hEisE]; exact hEl)
      hconclB hxlen' hfsl hbl hes hmk hfitB
  · -- the value: the callee's type, applied along a fitting spine, lands in the peel
    rw [List.map_append, hes, List.map_cons, List.map_nil, hmk]
    rw [hTyE] at hR
    have hmemR := foldl_app_mem_mkPisAV (by rw [← hTyE]; exact (hwdTy σ).2) hfitB hR
    rw [blockRecCa_value hcon hTyE (by rw [hlenRds', hmI'])
      (by rw [List.length_map, ← hEisE]; exact hEl) hconclB hxlen' hfsl hbl hes hmk]
    exact hmemR

/-- **The rule's RECORD group at the run** — the constructor's reading
record at the rule's member (its former, the former's data, the
stored type's reading and its length, the parameter frames), §27's
field-domain spelling, and the `ih` segment's per-key data `hIent` at
the pinned openers, carried from `ih` level `0` to the opener's own
level `q` (`blockRuleIhKey_run`, `ihTeleAtR_merge`,
`shiftE_consList_ih`).  It is the input group that `blockRuleHokA_of_run`
and `blockRuleCerts_of_run` share, named once. -/
theorem blockRuleRecord_run
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
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∃ (cvTa : ConstantVal) (caps : ConLeche.IndCaps) (nFull : Nat) (resSort : Level)
        (pps : (Name → Nat) → List (Nat × Nat × AnnotTerm))
        (dsC : List (Nat × Nat × AnnotTerm)) (bodyC : AnnotTerm),
        cvTas[p.toBlockShape.recTgtAt j]? = some cvTa ∧
        envC.find? cvTa.name = some (.indInfo cvTa caps) ∧
        FormerData mpC.base2 cvTa nFull resSort pps ∧ p.nP ≤ nFull ∧
        (∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV dsC bodyC)) ∧
        dsC.length = p.nP + cA.2 ∧
        (∀ ρ : Nat → V, Sat V (((pps ψ).take p.nP).map (·.2.2)).reverse ρ ↔
          Sat V ((dsC.take p.nP).map (·.2.2)).reverse ρ) ∧
        p.toBlockShape.rulePrefixAt j = p.nP + (p.toBlockShape.rulePrefixAt j - p.nP) ∧
        blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
          = (liftDoms (p.toBlockShape.rulePrefixAt j - p.nP) 0 (dsC.drop p.nP)).map (·.2.2) ∧
        (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).length
          = (blockRuleFrameAt p rs j i).nR ∧
        (∀ q, q < (blockRuleFrameAt p rs j i).nR →
          ∃ (i' b : Nat) (tl : List (Nat × Nat × AnnotTerm)) (bodyF conclA : AnnotTerm),
            i' < cA.2 ∧
            (dsC.getD (p.nP + i') default).2.2 = mkPisAV tl bodyF ∧
            (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD q default
              = mkPisAV (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) i' q
                  (rebit b tl)) conclA ∧
            ∀ (σ : Nat → V) (xs fs ys : List V),
              SpineFit σ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j) xs →
              SpineFit (consList xs σ)
                ((liftDoms (p.toBlockShape.rulePrefixAt j - p.nP) 0 (dsC.drop p.nP)).map
                  (·.2.2)) fs →
              SpineFit (consList fs (consList xs σ))
                ((blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).take q) ys →
              (∀ bs, SpineFit (consList ys (consList fs (consList xs σ)))
                  ((ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) i' q
                    (rebit b tl)).map (·.2.2)) bs →
                WellDenotedV V (consList bs (consList ys (consList fs (consList xs σ)))) conclA) ∧
              (b = 0 → ∀ bs, SpineFit (consList ys (consList fs (consList xs σ)))
                  ((ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) i' q
                    (rebit b tl)).map (·.2.2)) bs →
                interp V (consList bs (consList ys (consList fs (consList xs σ)))) conclA
                  ∈ˢ (univZero : V))) := by
  intro j r hr i cA hcA ψ
  have hkey := fun q (hq : q < (blockRuleFrameAt p rs j i).nR) =>
    blockRuleIhKey_run hμ h hkLen hdR hN hS hcore hmr hM hr hcA ψ hq
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hir : i < r.2.2.2.length := (List.getElem?_eq_some_iff.mp hcA).1
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, r.2.1[i]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hir)⟩
  obtain ⟨ms, hms, hctA, hlenms⟩ := checkBlockRecK_ctorsAt h hr
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
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
  have hcvTa := TE.hcvTa
  have hnP := TE.nP_le
  obtain ⟨hfT, -, -, hFD⟩ := hcore.1 _ TE.cvTa hcvTa
  have hframes := (hS.frames _ hmemk i cA hcj).1 ψ
  have ho : p.toBlockShape.rulePrefixAt j = p.nP + (p.toBlockShape.rulePrefixAt j - p.nP) := by
    omega
  have hFE := blockRuleFdomsAV_liftDoms h hr hcA hrhs hcore hmemk hcj hnP rfl ho ψ
  have hct : blockRuleCtorOf rs j i = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨rbs, ty, concl, -, -, -, hopen, -, -, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  have hIlen : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).length
      = (blockRuleFrameAt p rs j i).nR := by
    rw [blockRuleIhdomsAV, hct, readOpenedDoms_length_eq]
    exact openPisAtFvars_length _ hopen
  refine ⟨TE.cvTa, _, _, _, _, _, _, hcvTa, hfT, hFD, Nat.le_add_right _ _, hcd.okTy ψ, hcd.len ψ,
    hframes, ho, hFE, hIlen, ?_⟩
  intro q hq
  obtain ⟨fi, c', CihR, -, -, hfiC, hentry, hIget, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcall⟩ := hkey q hq
  refine ⟨fi, pwBit ψ (blockRuleFrameAt p rs j i).pw,
    ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
      (p.toBlockShape.recTgtAt j) i ψ).getD fi [], _,
    CihR.liftN q (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
      (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length, hfiC, hentry, ?_, ?_⟩
  · rw [hIget, mkPisAV_ihTeleAtR_liftN]
  · intro σ xs fs ys hxs hfs hys
    rw [← hFE] at hfs
    have hpl : (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j).length
        = p.toBlockShape.rulePrefixAt j := blockRulePdomsAV_length hμ mpC h hr ψ
    have hxlen : xs.length = p.toBlockShape.rulePrefixAt j := by rw [hxs.length_eq, hpl]
    have hlenps : (xs.take p.nP).length = p.nP := by rw [List.length_take, hxlen]; omega
    have hxl : xs.length = (xs.take p.nP).length + (p.toBlockShape.rulePrefixAt j - p.nP) := by
      rw [hlenps, hxlen]; omega
    have htake : xs.take (xs.take p.nP).length = xs.take p.nP := by rw [hlenps]
    have hfsl : fs.length = cA.2 := by
      rw [hfs.length_eq, hFE, List.length_map, liftDoms_length, List.length_drop, hcd.len ψ]
      show p.nP + cA.2 - p.nP = cA.2
      omega
    have hyl : ys.length = q := by
      rw [hys.length_eq, List.length_take, hIlen]; omega
    have htr : ∀ bs : List V,
        SpineFit (consList ys (consList fs (consList xs σ)))
          ((ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt j - p.nP) fi q
            (rebit (pwBit ψ (blockRuleFrameAt p rs j i).pw)
              (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
                (p.toBlockShape.recTgtAt j) i ψ).getD fi []))).map (·.2.2)) bs →
        SpineFit (consList (fs.take fi) (consList (xs.take p.nP) σ))
          ((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt j) i ψ).getD fi []).map (·.2.2)) bs := by
      intro bs hb
      rw [ihTeleAtR_merge (Nat.le_of_lt hfiC)] at hb
      have hfl' : (fs ++ ys).length = cA.2 + q := by rw [List.length_append, hfsl, hyl]
      have hfr : consList ys (consList fs (consList xs σ)) = consList (xs ++ (fs ++ ys)) σ := by
        simp only [consList_append]
      rw [hfr] at hb
      have hq' := spineFit_ihTeleAtR_rule (ρ := σ) (i := fi) hxl htake hfl' hb
      rwa [List.take_append_of_le_length (by omega)] at hq'
    have hfr0 : consList fs (consList xs σ) = consList (xs ++ fs) σ := by
      simp only [consList_append]
    refine ⟨fun bs hb => ?_, fun hb0 bs hb => ?_⟩
    · have hbl : bs.length = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
          ppsOf).tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length := by
        rw [(htr bs hb).length_eq, List.length_map]
      rw [WellDenotedV_liftN, ← hbl, shiftE_consList_ih rfl hyl, hfr0]
      exact ((hcall σ xs fs hxs hfs).2.2.2.2 bs (htr bs hb)).1
    · have hbl : bs.length = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD
          ppsOf).tssF (p.toBlockShape.recTgtAt j) i ψ).getD fi []).length := by
        rw [(htr bs hb).length_eq, List.length_map]
      rw [interp_liftN, ← hbl, shiftE_consList_ih rfl hyl, hfr0]
      exact ((hcall σ xs fs hxs hfs).2.2.2.2 bs (htr bs hb)).2.1 hb0


/-- **(G) THE RULE FRAME'S GRADING, AT THE RUN** — the
spelling `declBlock_run` passes on: `blockRuleHokA_of_run` at the pinned
`blockRulePdomsAV`/`blockRuleFdomsAV`/`blockRuleIhdomsAV`, its record
group and `ih` segment's `hIent` off `blockRuleRecord_run`. -/
theorem blockRuleGrading_run
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
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      rs[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      ∀ ψ : Name → Nat,
      ∀ l, l < p.toBlockShape.rulePrefixAt j + cA.2 + (blockRuleFrameAt p rs j i).nR →
      ∀ (σ' : Nat → V) (ys : List V),
        SpineFit σ' ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).take l) ys →
        WellDenotedV V (consList ys σ')
          ((blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ j
            ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ j i
            ++ blockRuleIhdomsAV p rs mpC.base2.acval envC ψ j i).getD l default) := by
  intro j r hr i cA hcA ψ
  obtain ⟨cvTa, caps, nFull, resSort, pps, dsC, bodyC, hcvTa, hfT, hFD, hle, hwd, hlenD, hframes,
    ho, hFE, hIlen, hIent⟩ :=
    blockRuleRecord_run hμ h hkLen hdR hN hS hcore hmr hM j r hr i cA hcA ψ
  rw [hFE]
  exact blockRuleHokA_of_run hμ mpC h hr ψ hcvTa hfT hFD hle hwd hlenD hframes ho rfl rfl hIlen
    hIent

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

omit [SetTheory V] in
/-- A re-bitted telescope keeps its domains, so its bounds. -/
theorem domsBelow_rebit {b : Nat} :
    ∀ {k : Nat} {ds : List (Nat × Nat × AnnotTerm)}, DomsBelow k ds → DomsBelow k (rebit b ds)
  | _, [], _ => trivial
  | _, _ :: ds, h => ⟨h.1, domsBelow_rebit (ds := ds) h.2⟩

/-- **(F) at the run** — `BlockIhFitTypedOwed` (`BlockDeclRun.lean`)
unfolded, at every typed tuple. -/
theorem blockIhFitTyped_run
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
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c → ∀ ys : List V,
        SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
        SpineFit (consList ys ρ) (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j)
          ((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
            (interp V (consList ys (consList tup ρ)))) := by
  intro ψ ρ tup htupl htyped c hc j hj ys hys
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  have hkey := fun q (hq : q < (blockRuleFrameAt p rs c j).nR) =>
    blockRuleIhKey_run hμ h hkLen hdR hN hS hcore hmr hM hr hcA ψ hq
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  -- the frame split
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.checkBlockRecK_tyAt h hr
  have hnP := TE.nP_le
  have hct : blockRuleCtorOf rs c j = cA := blockRuleCtorOf_eq hr hcA
  obtain ⟨rbs, ty, concl, -, -, -, hopen, -, -, -⟩ := blockRuleResidueData_runP h hr hcA hrhs
  have hIlen : (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j).length
      = (blockRuleFrameAt p rs c j).nR := by
    rw [blockRuleIhdomsAV, hct, readOpenedDoms_length_eq]
    exact openPisAtFvars_length _ hopen
  have hvlen : ((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
      (interp V (consList (xs ++ fs) (consList tup ρ)))).length
      = (blockRuleFrameAt p rs c j).nR := by
    rw [List.length_map, blockRuleIhsRunAV, blockRuleIhsAV_length]
  refine spineFit_of_getD (by rw [hvlen, hIlen]) fun q hq => ?_
  rw [hIlen] at hq
  obtain ⟨fi, c', CihR, -, hc'K, hfiC, -, hIget, hihsGet, hTlB, hEisB, -, -, -, -, -, -, -, -, -,
    -, -, hcallF⟩ := hkey q hq
  obtain ⟨hxlen, hfsl, -, hconv, hcall⟩ := hcallF ρ xs fs hxs hfs
  -- the domain, past the `q` values already bound
  have htk : ((((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
      (interp V (consList (xs ++ fs) (consList tup ρ))))).take q).length = q := by
    rw [List.length_take, hvlen]; omega
  rw [hIget]
  have hcancel := interp_liftN_ihvals (V := V)
    (ihvals := (((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
      (interp V (consList (xs ++ fs) (consList tup ρ))))).take q)
    (σ := consList (xs ++ fs) ρ)
    (mkPisAV (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
      (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw)
        (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
          (p.toBlockShape.recTgtAt c) j ψ).getD fi []))) CihR)
  rw [htk] at hcancel
  rw [hcancel]
  -- the value: the curried call of the tuple's callee component
  have hval : (((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
      (interp V (consList (xs ++ fs) (consList tup ρ))))).getD q pt
      = interp V (consList (xs ++ fs) (consList tup ρ))
          ((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).getD q default) := by
    have hq' : q < (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).length := by
      rw [blockRuleIhsRunAV, blockRuleIhsAV_length]; exact hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq',
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq']
    rfl
  rw [hval, hihsGet, ihFunAV, interp_mkLamsC_A (acc := ([] : List V))]
  have hbl0 : (ihTeleAtR cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
      (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw) (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []))).length = (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length := by
    rw [ihTeleAtR_length, rebit_length]
  have hxl' : xs.length = p.toBlockShape.rulePrefixAt c := hxlen
  -- the tower moves to the base frame
  rw [lamTowerA_congr_below (N := (xs ++ fs).length) (ρ₂ := consList (xs ++ fs) ρ)
    (g₂ := fun _ τ => (xs ++ (((((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).eissF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).map (ihIdxAtM cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0
        (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length)) ++ [AnnotTerm.mkAppN (.bvar (cA.2 - 1 - fi + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length))
          (teleVarsAV (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length)]).map (interp V τ)).foldl SetTheory.app (tup.getD c' pt))
    (consList_below_indep (xs ++ fs) (consList tup ρ) ρ) ?hb ?hbody]
  case hb =>
    intro l hl
    have hD := ihTeleAtGo_below (nF := cA.2) (o := p.toBlockShape.rulePrefixAt c - p.nP)
      (i := fi) (l := 0) (K := p.nP + fi) (k := 0)
      (tl := rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw) (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []))
      (by rw [Nat.add_zero]; exact domsBelow_rebit hTlB)
    have hl' : l < (ihTeleAtGo cA.2 (p.toBlockShape.rulePrefixAt c - p.nP) fi 0 0
        (rebit (pwBit ψ (blockRuleFrameAt p rs c j).pw)
          (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF
            (p.toBlockShape.recTgtAt c) j ψ).getD fi []))).length := hl
    have hq := DomsBelow.getD_below l hD hl'
    have hN : p.nP + fi + (cA.2 - fi + 0) + (p.toBlockShape.rulePrefixAt c - p.nP) + 0
        = (xs ++ fs).length := by
      rw [List.length_append, hxlen, hfsl]; omega
    rw [hN] at hq
    exact hq
  case hbody =>
    intro bs hbs
    rw [hbl0] at hbs
    have hR : consList tup ρ (rs.length - 1 - c') = tup.getD c' pt := by
      rw [consList_getD_of_lt _ _ _ (by omega), htupl,
        show rs.length - 1 - (rs.length - 1 - c') = c' from by omega]
    rw [interp_ihFunAV_body (V := V) (K := rs.length) hR hxl' hfsl (by rw [hbl0]; exact hbs)]
    rw [List.map_append, List.map_append, List.map_cons, List.map_nil, List.map_cons,
      List.map_nil, interp_fieldApp_rule hfsl hfiC hbs, interp_fieldApp_rule hfsl hfiC hbs]
    congr 2
    refine congrArg (· ++ _) (List.map_congr_left fun e he => ?_)
    obtain ⟨E, hE, rfl⟩ := List.mem_map.mp he
    have hEb := ihIdxAtM_below (nF := cA.2) (o := p.toBlockShape.rulePrefixAt c - p.nP) (i := fi)
      (l := 0) (m := (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length) (hEisB E hE)
    refine interp_congr_below (V := V) _ ((xs ++ fs).length + bs.length) _ _ ?_ fun i hi => ?_
    · have hN : p.nP + fi + (((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).tssF (p.toBlockShape.recTgtAt c) j ψ).getD fi []).length + (cA.2 - fi + 0) + (p.toBlockShape.rulePrefixAt c - p.nP)
          = (xs ++ fs).length + bs.length := by
        rw [List.length_append, hxlen, hfsl, hbs]; omega
      rw [hN] at hEb
      exact hEb
    · rw [show consList bs (consList (xs ++ fs) (consList tup ρ))
          = consList (xs ++ fs ++ bs) (consList tup ρ) from by simp only [consList_append],
        show consList bs (consList (xs ++ fs) ρ) = consList (xs ++ fs ++ bs) ρ from by
          simp only [consList_append]]
      exact consList_below_indep _ _ _ i (by rw [List.length_append]; omega)
  -- the tower inhabits the opener's domain
  refine lamTowerA_mem (fun dd hdd => ?_) (towerWalkA_of_spines_body fun bs hsp => ?_)
  · obtain ⟨d', hd', he⟩ := mem_ihTeleAtGo hdd
    rw [he, mem_rebit hd']
    exact (pwBit_zeronessOf ψ _).symm
  · obtain ⟨-, H0, VAL, -⟩ := hcall bs (hconv bs hsp)
    refine ⟨?_, fun hℓ0 => H0 ((pwBit_zeronessOf ψ _).mpr hℓ0)⟩
    exact VAL _ (htyped c' hc'K)


/-- **(F) at the CHAIN frame** — the typed tuple's `ih` fit with the
domains read where the values are: under the tuple itself.  This is
the spelling the rule stage's peel consumes (`BlockRuleIhFitOwed`, at
`chainFrame K a ρ`, which IS `consList` of the tuple).  It is
`blockIhFitTyped_run` at the base frame `consList tup ρ`: the prefix
and field domains are bounded (`blockRuleDoms_bounded_at`), the
recursor types closed (`closed_blockRecTyAV`), and the `ih` terms read
nothing past the tuple (`blockRuleIhsRunAV_below`), so the second copy
of the tuple the base-frame statement puts under them is invisible. -/
theorem blockIhFitChain_run
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
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = rs.length →
      (∀ mm, mm < rs.length →
        tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC rs ψ mm)) →
      ∀ c, c < rs.length → ∀ j, j < blockRecNCt rs c → ∀ ys : List V,
        SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
          ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) ys →
        SpineFit (consList ys (consList tup ρ)) (blockRuleIhdomsAV p rs mpC.base2.acval envC ψ c j)
          ((blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
            (interp V (consList ys (consList tup ρ)))) := by
  intro ψ ρ tup htupl htyped c hc j hj ys hys
  have hF := blockIhFitTyped_run hμ h hkLen hdR hN hS hcore hmr hM
  obtain ⟨env₀, pk, uOfD, ppsOf, rfl⟩ := hdR
  have hr : rs[c]? = some rs[c] := List.getElem?_eq_getElem hc
  have hjr : j < rs[c].2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some] at hj; exact hj
  obtain ⟨cA, hcA⟩ : ∃ cA, rs[c].2.2.2[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjr⟩
  obtain ⟨rhs, hrhs⟩ : ∃ rhs, rs[c].2.1[j]? = some rhs :=
    ⟨_, List.getElem?_eq_getElem (by rw [checkBlockRecK_rulesLen h hkLen hr]; exact hjr)⟩
  obtain ⟨-, -, hctA, -⟩ := checkBlockRecK_ctorsAt h hr
  have hcj : ((blockDataOf V p.toBlockShape env₀ ctorsAs p.kinds pk uOfD ppsOf).ctorsM
      (p.toBlockShape.recTgtAt c))[j]? = some cA := by
    show (ctorsAs.getD _ [])[j]? = _
    rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
  -- the base frame `consList tup ρ`: the spine still fits, the tuple is still typed
  have hys' : SpineFit (consList tup ρ)
      (blockRulePdomsAV mpC.base2.acval envC p.toBlockShape rs ψ c
        ++ blockRuleFdomsAV p.toBlockShape rs mpC.base2.acval envC ψ c j) ys :=
    spineFit_frame_of_bounded (blockRuleDoms_bounded_at hμ h hcore ψ c rs[c] hr j cA rhs hcA hrhs)
      hys
  have htyped' : ∀ mm, mm < rs.length →
      tup.getD mm pt ∈ˢ interp V (consList tup ρ) (blockRecTyAV mpC.base2.acval envC rs ψ mm) :=
    fun mm hmm => by
      rw [interp_closed (V := V) (closed_blockRecTyAV hμ mpC h (List.getElem?_eq_getElem hmm) ψ)
        (consList tup ρ) ρ]
      exact htyped mm hmm
  have hq := hF ψ (consList tup ρ) tup htupl htyped' c hc j hj ys hys'
  -- the `ih` terms read nothing past the tuple
  have hbd := blockRuleIhsRunAV_below (mpC := mpC) h hr hcA hcore hcj rfl
    (by rw [blockDataOf_ksF]; rfl) ψ
  have hyl : ys.length = p.toBlockShape.rulePrefixAt c + cA.2 := by
    rw [hys.length_eq, List.length_append, blockRulePdomsAV_length hμ mpC h hr ψ,
      blockRuleFdomsAV_length_run h hr hcA hrhs ψ]
  have hmap : (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
        (interp V (consList ys (consList tup (consList tup ρ))))
      = (blockRuleIhsRunAV p rs mpC.base2.acval envC ψ c j).map
        (interp V (consList ys (consList tup ρ))) := by
    refine List.map_congr_left fun v hv => ?_
    refine interp_congr_below (V := V) v (rs.length + p.toBlockShape.rulePrefixAt c + cA.2) _ _
      (hbd v hv) fun l hl => ?_
    rw [← consList_append tup ys (consList tup ρ), ← consList_append tup ys ρ]
    exact consList_below_indep (tup ++ ys) _ _ l (by rw [List.length_append, htupl, hyl]; omega)
  rw [hmap] at hq
  exact hq

end Grading

end ConLeche.Model
