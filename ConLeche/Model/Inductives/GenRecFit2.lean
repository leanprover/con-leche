module

public import ConLeche.Model.Inductives.GenRecFitBase
public import ConLeche.Model.Inductives.GenRecExtra
import ConLeche.Model.Inductives.GenClsData
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.GenRecPre
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.GenRecClasses
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetOutRow
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Env.BlockLfp
import ConLeche.Model.Env.CanonCrest
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Semantics.Tower.FixTower

public section

/-!
# The generated rules' fit of the recursor at a constructor (`GenFit2`)

`genRecFit2`: at every generated rule `(j, i)`, a prefix fitting the recursor's first `rP`
binders, the rule's parameters (`GenPs`), fields completing the constructor's fit and indices
pinned to its conclusion fit the recursor's whole telescope, the constructor application its
major binder.  The converse of the consumer rows (`genRows3_out`, `genRows3_mem`): there a
recursor fit gives the constructor's; here the constructor's gives the recursor's.

The route is one for both kinds of class (`genFit2_core`), through the class's recorded lfp
clause (`GenClsRd`):

* the constructor's fit at `ps ++ fs` makes its residual the class's member applied to
  arguments fitting the member's whole telescope, and the application an element of that
  application (`genOut_typed`, which reads only the class record);
* the index pin identifies the residual's index arguments with the recursor's indices, so the
  arguments are `ps ++ is`;
* the parameters satisfy the class's parameter telescope (`parsSatInv`), at a frame that is the
  class's own frame at the prefix (`hfr`: the prefix's leading values at a member class, the
  pins read at the prefix at an outside one) — the class is live there, `is`' tuple is in its
  index set and the leaf puts the application in the carrier at that tuple;
* `GenClsBack` turns that major into a fit of the stored domains, and the stored type is the
  Π-tower over them (`recStage_tyPis`).

The two kinds differ only in the frame and the level valuation (`genFit2_mem`,
`genFit2_out`), read off `GenPs` and `GenLv`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape TargetMajor FEnv
  GenRecRun NestState)

universe w

variable {V : Type w} [SetTheory V]

/-- Two value lists of one length agreeing at every position are equal. -/
theorem list_eq_of_getD {l₁ l₂ : List V} (hl : l₁.length = l₂.length)
    (h : ∀ q, q < l₁.length → l₁.getD q pt = l₂.getD q pt) : l₁ = l₂ := by
  refine List.ext_getElem hl fun q h1 h2 => ?_
  have := h q h1
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some] at this

/-- A mapped list's position. -/
theorem getD_map_interp {ρ : Nat → V} {ts : List Term} {q : Nat} (hq : q < ts.length) :
    (ts.map (interp V ρ)).getD q pt = interp V ρ (ts.getD q default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hq,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
  rfl

section Core

variable {F : Nat} {envC : Env} {pp : BlockShape}
  {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

set_option maxHeartbeats 4000000 in
/-- **The recursor's fit from the constructor's, at a class** (see the module docstring): at
a level valuation `ψj` agreeing with the class's on the constructor's level parameters and a
parameter list whose values make the class's frame at the prefix, the prefix, the indices and
the constructor application fit the recursor's whole telescope. -/
theorem genFit2_core (h : ConLeche.RecStageG .verified F envC pp (tgtRs out))
    (hcov : LfpCover mpC []) {ψ : Name → Nat} {ρ : Nat → V}
    (hB : GenClsBack pp out mpC d Dc mc cvc ψ ρ)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    {i : Nat} {ctor : ConstantVal × Nat} (hcAM : (tgtMajor out j).ctors[i]? = some ctor)
    {ψj : Name → Nat} (hlv : ∀ q ∈ ctor.1.levelParams, ψj q = tgtClsψ cvc out ψ j q)
    (hread : denote mpC.base2.acval envC ψj 0 ctor.1.type
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj))
    {xs ps : List Term} {mid : Term}
    (hxl : xs.length = pp.rulePrefixAt j)
    (hmid : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j) xs mid)
    (hpl : ps.length = (tgtMajor out j).nPc) (hpw : ∀ p ∈ ps, WellDenoted V ρ p)
    (hfr : tgtClsFr d mpC.base2.acval envC pp out ψ ρ (xs.map (interp V ρ)) j
      = consList (ps.map (interp V ρ)) ρ)
    {fs is : List Term} {restC : Term}
    (hfl : fs.length = ctor.2) (hil : is.length = pp.majorIdxAt j - pp.rulePrefixAt j)
    (hfw : ∀ f ∈ fs, WellDenoted V ρ f)
    (hfit : TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj)
      (ps ++ fs) restC)
    (hpin : IotaIndexPin (V := V) ρ restC (tgtMajor out j).nPc (pp.majorIdxAt j)
      (pp.rulePrefixAt j) (xs ++ is)) :
    ∃ restR, TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
      (xs ++ is ++ [Term.mkAppN (mpC.base2.acval ctor.1.name ψj) (ps ++ fs)]) restR := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨-, -, -, -, hTyE, hlenRds, -⟩ := recStage_tyPis mpC h hr ψ
  have hmI := genRec_mI h hr
  obtain ⟨t, -, hrt, hMt⟩ := tgtRs_getElem? hr
  have hnI : r.2.2.1 = (tgtMajor out j).nIdx := by
    rw [hrt]; show t.2.1.nIdx = (ConLeche.tgtMajorsOf out j).nIdx; rw [hMt]
  have hnIdx : pp.majorIdxAt j - pp.rulePrefixAt j = (tgtMajor out j).nIdx := by omega
  -- the prefix fits the rule's prefix domains
  have hpref : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ j)
      (xs.map (interp V ρ)) := by
    have e := List.take_append_drop (pp.rulePrefixAt j)
      (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ j)
    rw [hTyE, ← e, mkPisAV_append] at hmid
    exact spineFit_of_teleFitPA (by unfold blockRulePdomsAV; rw [List.length_take, hlenRds, hxl]; omega) hmid
  -- the constructor's residual is the class's member at fitting arguments
  have hys : (ps ++ fs).length = (tgtMajor out j).nPc + ctor.2 := by
    rw [List.length_append, hpl, hfl]
  have hWD : ∀ y ∈ ps ++ fs, WellDenoted V ρ y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hpw y hy
    · exact hfw y hy
  obtain ⟨args, -, hparA, hrestE, hin, hfitA, -⟩ :=
    genOut_typed hcov Rd hcAM hread hys hfit hWD
  obtain ⟨hC, -, -, -, ⟨hcK, -⟩⟩ := mpC.lfp_ok _ Rd.hD
  obtain ⟨-, -, hlpC, -⟩ := Rd.hctor i ctor hcAM
  obtain ⟨caps₀, hf₀⟩ := Rd.hfind
  have hfm : envC.find? ((tgtClsD d Dc out j).member (tgtClsM mc pp out j))
      = some (.indInfo cvI caps₀) := by rw [Rd.hmem]; exact hf₀
  have hag : ∀ q ∈ cvI.levelParams, ψj q = tgtClsψ cvc out ψ j q :=
    fun q hq => by rw [← hlpC] at hq; exact hlv q hq
  have hTow := mpC.tower_congr Rd.hD Rd.hmm hfm (ψ₁ := ψj) (ψ₂ := tgtClsψ cvc out ψ j) hag
  have hlenT : ((tgtClsD d Dc out j).pars (tgtClsM mc pp out j) ψj
      ++ (tgtClsD d Dc out j).ids (tgtClsM mc pp out j) ψj).length
      = ((tgtClsD d Dc out j).pars (tgtClsM mc pp out j) (tgtClsψ cvc out ψ j)
        ++ (tgtClsD d Dc out j).ids (tgtClsM mc pp out j) (tgtClsψ cvc out ψ j)).length := by
    obtain ⟨cvK, capsK, hfK, -, hlK⟩ := hcK _ Rd.hmm
    rw [hlK, hlK]
  generalize hψc : tgtClsψ cvc out ψ j = ψc at hag hTow hlenT
  generalize hD : tgtClsD d Dc out j = D at hTow hlenT hC hfitA
  generalize hmm : tgtClsM mc pp out j = mm at hTow hlenT hfitA
  have hfitA' := ((spineFit_iff_of_mkPisAV_eq hlenT (hTow ρ) _).1).mp (hfitA ρ)
  have hparsC : (D.pars mm ψc).length = (tgtMajor out j).nPc := by
    have := Rd.hlenP ψ
    rw [hψc, hD] at this
    rw [hC.parsLen _ (by rw [← hD, ← hmm]; exact Rd.hmm), this, Rd.hnpc]
  have hidsC : (D.ids mm ψc).length = (tgtMajor out j).nIdx := by
    have := Rd.hidsLen ψ
    rw [hψc, hD, hmm] at this
    exact this
  have hargsL : args.length = (tgtMajor out j).nPc + (tgtMajor out j).nIdx := by
    have := hfitA'.length_eq
    rw [List.length_map, List.length_append, hparsC, hidsC] at this
    exact this
  -- the arguments are the parameters and the recursor's indices
  have hargsV : args.map (interp V ρ) = ps.map (interp V ρ) ++ is.map (interp V ρ) := by
    refine list_eq_of_getD (by simp [hargsL, hpl, hil, hnIdx]) fun q hq => ?_
    rw [List.length_map] at hq
    rw [getD_map_interp hq]
    by_cases hqP : q < (tgtMajor out j).nPc
    · rw [getD_append_left' (by rw [List.length_map, hpl]; exact hqP),
        getD_map_interp (by rw [hpl]; exact hqP), hparA q hqP,
        getD_append_left' (by rw [hpl]; exact hqP)]
    · obtain ⟨Ha, cargsa, hrestEq, hcarLen, hcar⟩ := hpin
      obtain ⟨l, rfl⟩ : ∃ l, q = (tgtMajor out j).nPc + l := ⟨q - (tgtMajor out j).nPc, by omega⟩
      have hl : l < pp.majorIdxAt j - pp.rulePrefixAt j := by
        rw [hnIdx]; omega
      have hcarLen' : cargsa.length = args.length := by
        rcases hcarLen with hc | hc
        · omega
        · rw [hc, hargsL, hnIdx]
      obtain ⟨-, rfl⟩ := Term.mkAppN_inj (hrestEq.symm.trans hrestE) hcarLen'
      rw [hcar l hl,
        show (tgtMajor out j).nPc + l = (ps.map (interp V ρ)).length + l by
          rw [List.length_map, hpl],
        getD_append_right', getD_map_interp (by rw [hil]; omega),
        show pp.rulePrefixAt j + l = xs.length + l by rw [hxl], getD_append_right']
  rw [hargsV] at hfitA' hin
  obtain ⟨hP, hI⟩ := spineFit_append_at (by rw [List.length_map, hpl, hparsC]) hfitA'
  generalize hpV : ps.map (interp V ρ) = psV at hP hI hin hfr
  generalize hiV : is.map (interp V ρ) = isV at hI hin
  -- the parameters satisfy the class's parameter telescope, at the class's frame
  have hmmk : mm < D.k := by rw [← hD, ← hmm]; exact Rd.hmm
  have hmN : mm < D.N := Nat.lt_of_lt_of_le hmmk hC.kN
  have hsP : Sat V (D.params ψc).reverse (consList psV ρ) := by
    have hs := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hP
    rw [List.append_nil] at hs
    exact hC.parsSatInv _ hmmk _ _ hs
  have hPs : SpineFit ρ (D.params ψc) psV := by
    refine spineFit_of_sat_consList ?_ hsP
    rw [hP.length_eq, hparsC]
    have := Rd.hlenP ψ
    rw [hψc, hD] at this
    rw [this, Rd.hnpc]
  -- the major, in the carrier at the indices' tuple
  have hleaf := hC.leaf mm hmmk ψc ρ psV isV hPs hI
  have hind : mpC.base2.acval (D.member mm) ψc = mpC.base2.acval (tgtMajor out j).ind ψj := by
    have hm := Rd.hmem
    rw [hD, hmm] at hm
    rw [hm]
    exact (mpC.base2.acval_params _ _ hf₀ ψj ψc hag).symm
  rw [hind] at hleaf
  rw [hleaf] at hin
  have hxV : (xs.map (interp V ρ)).length = tgtRP pp j := by
    rw [List.length_map, hxl]; rfl
  have hG := (Rd.hG ψ ρ (xs.map (interp V ρ))).mpr hpref
  have hLive : tgtClsLive d Dc cvc mpC.base2.acval envC pp out ψ ρ (xs.map (interp V ρ)) j := by
    unfold tgtClsLive
    split
    · trivial
    · rw [hD, hψc, hfr]
      exact ⟨hsP, mm, hmmk, isV, hI⟩
  have hIs := tgtClsIs_of (mc := mc) hG hLive
  rw [hD, hψc, hmm, hfr] at hIs
  have hT : tgtClsTup d Dc mc cvc pp out ψ j isV
      ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp out ψ ρ (xs.map (interp V ρ)) j := by
    rw [hIs, tgtClsTup, tgtClsU, hD, hψc, hmm]
    exact tupW_mem hI
  have hX : interp V ρ (Term.mkAppN (mpC.base2.acval ctor.1.name ψj) (ps ++ fs))
      ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp out ψ ρ (xs.map (interp V ρ)) j)
        (tgtClsTup d Dc mc cvc pp out ψ j isV) := by
    rw [tgtClsCr, tgtClsTup, tgtClsU, hD, hψc, hmm, hfr]
    exact hin
  have hisO : isOfW (tgtClsU d Dc mc cvc pp out ψ j) (tgtClsNIdx d pp out j)
      (tgtClsTup d Dc mc cvc pp out ψ j isV) = isV := by
    rw [tgtClsTup, tgtClsU, Rd.hnIdx, hD, hψc, hmm, ← hidsC]
    exact isOfW_tupW (hC.idxOk ψc _ hsP mm hmN) hI
  have hsp := hB j hj _ _ _ hT hX
  rw [hisO] at hsp
  -- the recursor's whole telescope
  rw [hTyE]
  refine teleFitPA_mkPisAV_of_spineFit
    (by rw [List.length_append, List.length_append, hxl, hil, hlenRds]; simp; omega) ?_
  rw [List.map_append, List.map_append, hiV]
  simpa only [List.map_cons, List.map_nil, List.append_assoc] using hsp

end Core

/-! ## The generated rules -/

section Assembly

variable {F : Nat} {env₁ envC : Env} {pp : BlockShape} {nestedBit : Bool} {pos : NestState}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

set_option maxHeartbeats 4000000 in
/-- **`GenFit2` at every generated rule**: `genFit2_core`, with the class's level valuation
read off `GenLv` and its frame off `GenPs` — the prefix's leading `nP` values at a member
class (the block's parameter count, `member_facts`), the pins read at the prefix (the key
frame) at an outside one. -/
theorem genRecFit2
    (R : GenRecRun .verified F (ConLeche.mkFEnv env₁) env₁ (ConLeche.mkFEnv envC) pp nestedBit
      pos block out)
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out)) (hcov : LfpCover mpC [])
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List Term} (hdR : d = blockDataOf V pp pk uOfD ppsOf)
    (hB : ∀ ψ ρ, GenClsBack pp out mpC d Dc mc cvc ψ ρ)
    (hrdAll : ∀ c, c < (tgtRs out).length → pp.nP ≤ pp.rulePrefixAt c ∧
      ∃ cvI, GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hseam : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        ∃ iT, envC.find? ctor.1.name
            = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2 iT) ∧
        ConstsBound envC ctor.1.type ∧
        ∀ ψ : Name → Nat,
          denote mpC.base2.acval envC ψ 0 ctor.1.type
            = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ)) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat),
      r.2.2.2[i]? = some ctor → GenFit2 mpC pp out j i ctor := by
  intro j r hr i ctor hctor ψ ψj hlvG ρ xs ps mid hxl _ hmid hpw hps fs is restC hfl hil hfw _
    hfit hpin
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨hnP, cvI, Rd⟩ := hrdAll j hj
  obtain ⟨-, -, -, hreadAll⟩ := hseam j r hr i ctor hctor
  have hcAM : (tgtMajor out j).ctors[i]? = some ctor := by rw [← tgtRs_ctors hr]; exact hctor
  obtain ⟨hpl, hpv⟩ := hps
  have hxV : (xs.map (interp V ρ)).length = tgtRP pp j := by rw [List.length_map, hxl]; rfl
  cases hmb : (tgtMajor out j).member with
  | some t =>
    have hmS : (tgtMajor out j).member.isSome = true := by rw [hmb]; rfl
    -- the class's parameter count is the block's
    obtain ⟨-, cls, -, -, -, -, -, -, -, hMj, hgc⟩ := genRun_at R hj
    have hi' : cls < R.Ms.length := by rw [← hgc]; exact genRun_cls_lt R hj
    obtain ⟨key, M₀, nfs, hMs, -, ⟨CR⟩⟩ := genRun_class R hi'
    have hget : R.Ms.getD cls default = { M₀ with nfs := nfs } := by
      rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
    rw [hget] at hMj
    have hm0 : M₀.member = some t := by rw [hMj] at hmb; exact hmb
    obtain ⟨-, hnPc⟩ := CR.major.member_facts hm0
    have hnPc' : (tgtMajor out j).nPc = d.nP := by
      rw [hMj]; subst hdR; exact hnPc
    refine genFit2_core h hcov (hB ψ ρ) hr Rd hcAM (fun q hq => ?_) (hreadAll ψj) hxl hmid
      hpl hpw ?_ hfl hil hfw hfit hpin
    · have := hlvG q hq
      simp only [hmS, ite_true] at this
      simp only [tgtClsψ, hmS, ite_true]
      exact this
    · simp only [tgtClsFr, hmS, ite_true]
      congr 1
      have hle : d.nP ≤ xs.length := by
        rw [hxl, ← hnPc']
        have hdn : d.nP = pp.nP := by subst hdR; rfl
        rw [hnPc', hdn]; exact hnP
      refine list_eq_of_getD (by simp [hpl, hnPc']; omega) fun q hq => ?_
      have hq' : q < d.nP := by simp at hq; omega
      have := hpv q (by rw [hnPc']; exact hq')
      simp only [hmS, ite_true] at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hq', ← List.getD_eq_getElem?_getD,
        getD_map_interp (by omega), getD_map_interp (by rw [hpl, hnPc']; exact hq'), this]
  | none =>
    have hmS : (tgtMajor out j).member.isSome = false := by rw [hmb]; rfl
    refine genFit2_core h hcov (hB ψ ρ) hr Rd hcAM (fun q hq => ?_) (hreadAll ψj) hxl hmid
      hpl hpw ?_ hfl hil hfw hfit hpin
    · have := hlvG q hq
      simp only [hmS, Bool.false_eq_true, ite_false] at this
      obtain ⟨-, -, hlpC, -⟩ := Rd.hctor i ctor hcAM
      rw [Rd.hψ, this, hlpC]
    · rw [Rd.hfr ψ ρ _ hxV]
      unfold keyFrame
      congr 1
      · have hdl : (tgtOutDsa mpC.base2.acval envC pp out ψ j).length = (tgtMajor out j).nPc := by
          rw [← DenoteSpine.length_eq (Rd.hdsa ψ), Rd.hnpc]
        refine list_eq_of_getD (by simp [hdl, hpl]) fun q hq => ?_
        rw [List.length_map, hdl] at hq
        have := hpv q hq
        simp only [hmS, Bool.false_eq_true, ite_false] at this
        rw [getD_map_interp (by rw [hdl]; exact hq), getD_map_interp (by rw [hpl]; exact hq),
          this]
      · funext k
        rw [← hxV]
        exact consList_apply_add _ _ _

end Assembly

end ConLeche.Model
