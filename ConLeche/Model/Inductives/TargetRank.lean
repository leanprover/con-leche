module

public import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutRow
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.StructFrameKit

public section

/-!
# The induction over the recursor classes, layer by layer (PRIMREC)

`TgtClassInd` (`TargetClassRows.lean`) is the ONE premise of the recursor
stage that the rule rows do not give: an induction over the union of the
family's classes along the graph's predecessor relation (the calls).  The
node route (`tgtClassInd_of_pres`) reads it off the positivity walk.  This
module gives the walk-free route of PRIMREC (`_tmp/primrec/PLAN.md`,
`_tmp/uniform-inds/STAGEFACT.md` §3): order the classes by a RANK along
the family's own calls, and prove the induction one layer at a time.

* `graphInd_of_layers` — the generic statement: if every layer is
  inductive given the layers below (`LayerStep`), the whole union is.
* `layerStep_strict` — a layer every call of which leaves it downwards
  (an ACYCLIC layer: STAGEFACT's acyclic SCC) is inductive as soon as its
  classes' elements DECODE: nothing but the lfp clause's case analysis
  (`LfpClause.carrier_case`), no stage, no tie, no walk.
* at the target check's classes: every element decodes
  (`tgtCls_decodes`, the recorded clause of the class's block — the
  block's own at a member major, the container's at an outside one); a
  call's target is tagged with one of the rule's callees
  (`tgtCall_callee`).  Hence `tgtClassInd_of_rank`: a rank along which
  every call strictly decreases gives the induction.

A layer with calls inside it (a CYCLIC SCC) is the business of the
completeness facts (lanes FLATHOME / NESTHOME): they supply its
`LayerStep`, and `graphInd_of_layers` assembles.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor)

universe w

variable {V : Type w} [SetTheory V]

/-! ## 1. Layers, generically -/

section Layers

variable (Is Cr : List V → Nat → V) (injX : Nat → Nat → List V → V) (nCt : Nat → Nat)
  (K : Nat) (fit : List V → Nat → V → Nat → List V → Prop)
  (call : List V → Nat → Nat → List V → V → Prop)

/-- **The closure hypothesis** of the induction over the classes at the
prefix spine `xs`: `P` holds at a major once it holds at the
predecessors of SOME decoding. -/
@[expose] def GraphClosed (xs : List V) (P : V → Prop) : Prop :=
  ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
    (∃ e, graphDecG Is injX nCt K fit xs u e ∧
      ∀ v, v ∈ˢ graphPredG Is Cr K call xs e → P v) → P u

/-- `P` holds at every element of class `c`. -/
@[expose] def ClsAll (xs : List V) (P : V → Prop) (c : Nat) : Prop :=
  ∀ t, t ∈ˢ Is xs c → ∀ y, y ∈ˢ app (Cr xs c) t → P (tagged c t y)

/-- **Layer `n` is inductive** along the rank `r`: at every prefix
spine and closed `P`, once `P` holds on every class below `n`, it holds
on every class of rank `n`. -/
@[expose] def LayerStep (r : Nat → Nat) (n : Nat) : Prop :=
  ∀ xs P, GraphClosed Is Cr injX nCt K fit call xs P →
    (∀ c, c < K → r c < n → ClsAll Is Cr xs P c) → ∀ c, c < K → r c = n → ClsAll Is Cr xs P c

/-- **Every element of class `c` decodes**: it is an injection of a
constructor's fields that fit. -/
@[expose] def ClsDecodes (xs : List V) (c : Nat) : Prop :=
  ∀ t, t ∈ˢ Is xs c → ∀ y, y ∈ˢ app (Cr xs c) t →
    ∃ j fs, j < nCt c ∧ fit xs c t j fs ∧ y = injX c j fs

variable {Is Cr injX nCt K fit call}

/-- **The induction over the classes, from its layers.** -/
theorem graphInd_of_layers {r : Nat → Nat}
    (h : ∀ n, LayerStep Is Cr injX nCt K fit call r n) :
    ∀ xs P, GraphClosed Is Cr injX nCt K fit call xs P →
      ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) → P u := by
  intro xs P hP
  have key : ∀ n, ∀ c, c < K → r c < n → ClsAll Is Cr xs P c := by
    intro n
    induction n with
    | zero => intro c _ hlt; exact absurd hlt (Nat.not_lt_zero _)
    | succ n ih =>
      intro c hc hlt
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h' | h'
      · exact ih c hc h'
      · exact h n xs P hP ih c hc h'
  intro u hu
  obtain ⟨c, hc, t, ht, y, hy, rfl⟩ := mem_unionSet.mp hu
  exact key (r c + 1) c hc (Nat.lt_succ_self _) t ht y hy

/-- **An acyclic layer is inductive**: when every call out of a class of
rank `n` lands strictly below `n`, the case analysis of the class's
elements is all the induction needs. -/
theorem layerStep_strict {r : Nat → Nat} {n : Nat}
    (hdec : ∀ xs c, c < K → r c = n → ClsDecodes Is Cr injX nCt fit xs c)
    (hcall : ∀ xs c, c < K → r c = n → ∀ j fs c' t y,
      call xs c j fs (tagged c' t y) → r c' < n) :
    LayerStep Is Cr injX nCt K fit call r n := by
  intro xs P hP hlow c hc hrc t ht y hy
  obtain ⟨j, fs, hj, hf, rfl⟩ := hdec xs c hc hrc t ht y hy
  refine hP _ (tagged_mem_unionSet hc ht hy)
    ⟨(c, j, fs), ⟨hc, hj, t, ht, hf, rfl⟩, fun v hv => ?_⟩
  obtain ⟨hvU, hcv⟩ := mem_graphPredG.mp hv
  obtain ⟨c', hc', t', ht', y', hy', rfl⟩ := mem_unionSet.mp hvU
  exact hlow c' hc' (hcall xs c hc hrc j fs c' t' y' hcv) t' ht' y' hy'

/-- **A strictly decreasing rank gives the induction.** -/
theorem graphInd_of_rank {r : Nat → Nat}
    (hdec : ∀ xs c, c < K → ClsDecodes Is Cr injX nCt fit xs c)
    (hcall : ∀ xs c, c < K → ∀ j fs c' t y, call xs c j fs (tagged c' t y) → r c' < r c) :
    ∀ xs P, GraphClosed Is Cr injX nCt K fit call xs P →
      ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) → P u :=
  graphInd_of_layers fun _ => layerStep_strict (fun xs c hc _ => hdec xs c hc)
    (fun xs c hc hrc j fs c' t y h => by rw [← hrc]; exact hcall xs c hc j fs c' t y h)

end Layers

/-! ## 2. At the target check's classes -/

section Target

/-- **A call's target is tagged with one of the rule's callees** (the
`ih` variables' `callee` fields, `tgtIhL`). -/
theorem tgtCall_callee {mode : CheckMode} {F : Nat} {fe : FEnv} {p : BlockShape}
    {formerTys : List Expr} {out : List (ConstantVal × TargetMajor × List Expr)}
    {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {ψ : Name → Nat}
    {tup : Nat → List V → V} {ρ : Nat → V} {xs : List V} {c j : Nat} {fs : List V}
    {c' : Nat} {t y : V}
    (h : tgtCall mode F fe p formerTys out acval env ψ tup ρ xs c j fs (tagged c' t y)) :
    c' ∈ (tgtIhL mode F fe p formerTys out c j).map (·.callee) := by
  obtain ⟨key, hkey, bs, -, heq⟩ := h
  obtain ⟨rfl, -, -⟩ := tagged_inj heq
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hkey
  have hr' : r < (tgtIhL mode F fe p formerTys out c j).length := List.mem_range.mp hr
  refine List.mem_map.mpr ⟨_, ?_, rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr', Option.getD_some]
  exact List.getElem_mem hr'

variable {μ : CheckMode} {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

/-- **Every element of every class decodes** (`LfpClause.carrier_case`
at the class's recorded clause): a member class reads the block's own
clause at the prefix's parameters, an outside class the container's at
the key frame (`tgtOutSat`: the major's parameters satisfy the
container's parameter telescope there). -/
theorem tgtCls_decodes (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks) (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs c, c < (tgtRs out).length →
      ClsDecodes (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
        (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
        (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (blockRecNCt (tgtRs out))
        (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) xs c := by
  intro xs c hc t ht y hy
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hnCt : blockRecNCt (tgtRs out) c = ((tgtRs out)[c]).2.2.2.length := by
    rw [blockRecNCt, List.getD_eq_getElem?_getD, hr, Option.getD_some]
  cases hmb : (tgtMajor out c).member with
  | some tm =>
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    rw [tgtClsIs_mem hm] at ht
    rw [tgtClsCr_mem hm] at hy
    obtain ⟨hpar, hpref⟩ := blockRecIs_fits ht
    rw [blockRecIs_pos hpar hpref] at ht
    have hsat : Sat V (d.toLfp.params ψ).reverse (consList (xs.take d.nP) ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (fun _ _ h => nomatch h) hpar
      simp only [List.append_nil] at this
      exact this
    have hmemk := (blockRecMajor_run (hm := hmR) (V := V) hμ mpC h hmr hr ψ).2.1
    have hcl := mpC.lfpClause_of_mem hlfp
    have hmN : pp.toBlockShape.recTgtAt c < d.toLfp.N :=
      Nat.lt_of_lt_of_le hmemk hcl.kN
    obtain ⟨j, fs, hHF, rfl⟩ := hcl.carrier_case hsat hmN ht hy
    refine ⟨j, fs, ?_, (tgtClsFit_mem hm xs t j fs).mpr hHF, by rw [tgtClsInj_mem hm]; rfl⟩
    rw [hnCt, ← tgtCls_hctM h hdR c _ hmR hr]
    exact hHF.1
  | none =>
    have hm' : (tgtMajor out c).member.isSome = false := by rw [hmb]; rfl
    have hcl0 := hcls c hc hmb
    have hpref := tgtClsIs_out_fits hmb ht
    rw [tgtClsIs_out_pos hmb hpref] at ht
    rw [tgtClsCr_out hmb] at hy
    obtain ⟨dsa, hdsa, -, -, -, hsatF⟩ := tgtOutSat hμ mpC hcov h R hr hmb hcl0 ψ
    have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c :=
      denoteMetaSpine_eq_map hdsa
    subst hdsaE
    have hsat := hsatF ρ xs hpref
    have hcl := mpC.lfpClause_of_mem hcl0.hD
    have hmN : mc c < (Dc c).N := Nat.lt_of_lt_of_le hcl0.hmm hcl.kN
    obtain ⟨j, fs, hHF, rfl⟩ := hcl.carrier_case hsat hmN ht hy
    refine ⟨j, fs, ?_, (tgtClsFit_out hmb xs t j fs).mpr hHF, by rw [tgtClsInj_out hmb]⟩
    rw [hnCt, tgtRs_ctors hr, hcl0.hlen]
    exact hHF.1

/-- **`TgtClassInd` from a rank** along which every call of every rule
strictly decreases — no positivity node, no walk: the classes' case
analysis (`tgtCls_decodes`) and the calls' callees (`tgtCall_callee`). -/
theorem tgtClassInd_of_rank (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks) (formerTys : List Expr) (r : Nat → Nat)
    (hr : ∀ c, c < (tgtRs out).length → ∀ j,
      ∀ c' ∈ (tgtIhL μ F (mkFEnv envC) pp.toBlockShape formerTys out c j).map (·.callee),
        r c' < r c)
    (ψ : Name → Nat) (ρ : Nat → V) :
    TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape formerTys out d Dc mc cvc ψ ρ :=
  graphInd_of_rank (r := r)
    (tgtCls_decodes hμ hcov h R hcls hdR hmr hlfp ψ ρ)
    (fun _ c hc j _ _ _ _ hcall => hr c hc j _ (tgtCall_callee hcall))

end Target

end ConLeche.Model
