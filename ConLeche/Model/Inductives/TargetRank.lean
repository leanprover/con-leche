module

public import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Verify.Inductives.RecCallGraph

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
    (hcall : ∀ xs c, c < K → r c = n → ∀ j, j < nCt c → ∀ fs c' t y,
      call xs c j fs (tagged c' t y) → r c' < n) :
    LayerStep Is Cr injX nCt K fit call r n := by
  intro xs P hP hlow c hc hrc t ht y hy
  obtain ⟨j, fs, hj, hf, rfl⟩ := hdec xs c hc hrc t ht y hy
  refine hP _ (tagged_mem_unionSet hc ht hy)
    ⟨(c, j, fs), ⟨hc, hj, t, ht, hf, rfl⟩, fun v hv => ?_⟩
  obtain ⟨hvU, hcv⟩ := mem_graphPredG.mp hv
  obtain ⟨c', hc', t', ht', y', hy', rfl⟩ := mem_unionSet.mp hvU
  exact hlow c' hc' (hcall xs c hc hrc j hj fs c' t' y' hcv) t' ht' y' hy'

/-- **A strictly decreasing rank gives the induction.** -/
theorem graphInd_of_rank {r : Nat → Nat}
    (hdec : ∀ xs c, c < K → ClsDecodes Is Cr injX nCt fit xs c)
    (hcall : ∀ xs c, c < K → ∀ j, j < nCt c → ∀ fs c' t y,
      call xs c j fs (tagged c' t y) → r c' < r c) :
    ∀ xs P, GraphClosed Is Cr injX nCt K fit call xs P →
      ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) → P u :=
  graphInd_of_layers fun _ => layerStep_strict (fun xs c hc _ => hdec xs c hc)
    (fun xs c hc hrc j hj fs c' t y h => by rw [← hrc]; exact hcall xs c hc j hj fs c' t y h)

/-! ### A cyclic layer: derivations along the calls (`Der`)

A layer with calls inside it (a cyclic SCC, STAGEFACT §3) is inductive
once every element of its classes has a DERIVATION along the family's
calls (PROPREL's `Der`, at the family's classes): a decoding at the true
carrier whose calls INTO the layer land at elements that have a
derivation in turn.  `Der` is a Lean inductive, so its induction is
Lean's own (no rank on values, no regularity: the `Prop` case).
Completeness — every element of the layer's classes has one — is the
cyclic lanes' obligation (FLATHOME: the home's lfp induction; NESTHOME:
the recorded per-block completeness); `layerStep_of_der` turns it into
the layer's `LayerStep`, and `graphInd_of_layers` assembles. -/

/-- **A derivation along the calls inside a layer** (`S` the layer's
classes) at the prefix spine `xs`: an element of a class of the layer, a
decoding of it, and its calls into the layer landing at derived
elements. -/
inductive Der (xs : List V) (S : Nat → Prop) : V → Prop
  | mk {c : Nat} {t : V} {j : Nat} {fs : List V} :
      c < K → S c → t ∈ˢ Is xs c → injX c j fs ∈ˢ app (Cr xs c) t → j < nCt c →
      fit xs c t j fs →
      (∀ c' t' y', S c' → t' ∈ˢ Is xs c' → y' ∈ˢ app (Cr xs c') t' →
        call xs c j fs (tagged c' t' y') → Der xs S (tagged c' t' y')) →
      Der xs S (tagged c t (injX c j fs))

/-- **A layer whose elements all have derivations is inductive**, given
that the calls out of it never go up (`hdown`). -/
theorem layerStep_of_der {r : Nat → Nat} {n : Nat}
    (hdown : ∀ xs c, c < K → r c = n → ∀ j fs c' t y,
      call xs c j fs (tagged c' t y) → r c' ≤ n)
    (hcomp : ∀ xs c, c < K → r c = n → ∀ t, t ∈ˢ Is xs c → ∀ y, y ∈ˢ app (Cr xs c) t →
      Der (Is := Is) (Cr := Cr) (injX := injX) (nCt := nCt) (K := K) (fit := fit)
        (call := call) xs (fun c' => r c' = n) (tagged c t y)) :
    LayerStep Is Cr injX nCt K fit call r n := by
  intro xs P hP hlow c₀ hc₀ hrc₀ t₀ ht₀ y₀ hy₀
  suffices hall : ∀ u, Der (Is := Is) (Cr := Cr) (injX := injX) (nCt := nCt) (K := K)
      (fit := fit) (call := call) xs (fun c' => r c' = n) u → P u from
    hall _ (hcomp xs c₀ hc₀ hrc₀ t₀ ht₀ y₀ hy₀)
  intro u hD
  induction hD with
  | @mk c t j fs hc hS ht hy hj hf _ ih =>
    refine hP _ (tagged_mem_unionSet hc ht hy)
      ⟨(c, j, fs), ⟨hc, hj, t, ht, hf, rfl⟩, fun v hv => ?_⟩
    obtain ⟨hvU, hcv⟩ := mem_graphPredG.mp hv
    obtain ⟨c', hc', t', ht', y', hy', rfl⟩ := mem_unionSet.mp hvU
    rcases Nat.lt_or_eq_of_le (hdown xs c hc hS j fs c' t' y' hcv) with hlt | heq
    · exact hlow c' hc' hlt t' ht' y' hy'
    · exact ih c' t' y' heq ht' hy' hcv

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
    (hr : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ c' ∈ (tgtIhL μ F (mkFEnv envC) pp.toBlockShape formerTys out c j).map (·.callee),
        r c' < r c)
    (ψ : Name → Nat) (ρ : Nat → V) :
    TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape formerTys out d Dc mc cvc ψ ρ :=
  graphInd_of_rank (r := r)
    (tgtCls_decodes hμ hcov h R hcls hdR hmr hlfp ψ ρ)
    (fun _ c hc j hj _ _ _ _ hcall => hr c hc j hj _ (tgtCall_callee hcall))

/-- **Every recognised call is an edge of the family's call graph**
(`targetCallGraph`, read off the stream's rules): at a rule of recursor
`c`, the callee `c'` of every `ih` variable. -/
theorem tgtCallee_edge
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {c : Nat} (hc : c < (tgtRs out).length) {j : Nat} (hj : j < blockRecNCt (tgtRs out) c)
    {c' : Nat}
    (hc' : c' ∈ (tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j).map
      (·.callee)) :
    c < (ConLeche.targetCallGraph (pp.toBlockShape.recs.map (·.cvR.name))
        (pp.toBlockShape.recs.map (·.rhss))).length ∧
      c' < (ConLeche.targetCallGraph (pp.toBlockShape.recs.map (·.cvR.name))
        (pp.toBlockShape.recs.map (·.rhss))).length ∧
      c' ∈ (ConLeche.targetCallGraph (pp.toBlockShape.recs.map (·.cvR.name))
        (pp.toBlockShape.recs.map (·.rhss))).getD c [] := by
  obtain ⟨cA, rhs, hcA, hrhs⟩ := tgtRule_exists h hc hj
  obtain ⟨rc, rhs0, M, u, Q, hrc, hrhs0, -, -, -, -, -, -, -, hAbs⟩ :=
    targetRuleAtRaw R (List.getElem?_eq_getElem hc) hcA hrhs
  obtain ⟨ih, hih, rfl⟩ := List.mem_map.mp hc'
  have hih' : ih ∈ Q.ihs.toList := by
    have : tgtIhL μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j = Q.ihs.toList := by
      rw [tgtIhL, ← hAbs]
    rwa [this] at hih
  obtain ⟨hlt, hn⟩ := Q.callee_names ih hih'
  have hcR : c < pp.toBlockShape.recs.length := (List.getElem?_eq_some_iff.mp hrc).1
  refine ⟨by simpa [ConLeche.targetCallGraph] using hcR,
    by simpa [ConLeche.targetCallGraph, tgtFam] using hlt, ?_⟩
  exact ConLeche.mem_targetCallGraph (rs := rc.rhss) (by simp [hrc])
    (List.mem_of_getElem? hrhs0) (by simpa [tgtFam] using hlt) (by simpa [tgtFam] using hn)

/-- **`TgtClassInd` at an ACYCLIC call graph** (the kernel's
`graphAcyclic`, the case `targetLegacyAux` checks without the walk): the
rank is the graph's (`graphRank`), and every recognised call is an edge
(`tgtCallee_edge`). -/
theorem tgtClassInd_of_acyclic (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hlfp : d.toLfp ∈ mpC.lfpBlocks)
    (hac : ConLeche.graphAcyclic (ConLeche.targetCallGraph
      (pp.toBlockShape.recs.map (·.cvR.name)) (pp.toBlockShape.recs.map (·.rhss))) = true)
    (ψ : Name → Nat) (ρ : Nat → V) :
    TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape (cvTas.map (·.type)) out d Dc mc cvc
      ψ ρ :=
  tgtClassInd_of_rank hμ hcov h R hcls hdR hmr hlfp _ _
    (fun _ hc _ hj _ hc' =>
      let ⟨hcg, _, he⟩ := tgtCallee_edge h R hc hj hc'
      ConLeche.graphAcyclic_descends hac hcg he) ψ ρ

/-- **The calls never climb the family's rank** (`graphRank_mono`): the
`hdown` of a cyclic layer's `layerStep_of_der`, at the target check's
classes. -/
theorem tgtCall_rank_le
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape nested block cvTas
      ctorsAs out)
    {acval : Name → (Name → Nat) → AnnotTerm} {ψ : Name → Nat} {tup : Nat → List V → V}
    {ρ : Nat → V} {xs : List V} {c : Nat} (hc : c < (tgtRs out).length) {j : Nat}
    (hj : j < blockRecNCt (tgtRs out) c) {fs : List V} {c' : Nat} {t y : V}
    (hcall : tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out acval envC ψ
      tup ρ xs c j fs (tagged c' t y)) :
    (ConLeche.graphRank (ConLeche.targetCallGraph (pp.toBlockShape.recs.map (·.cvR.name))
        (pp.toBlockShape.recs.map (·.rhss)))).getD c' 0
      ≤ (ConLeche.graphRank (ConLeche.targetCallGraph (pp.toBlockShape.recs.map (·.cvR.name))
        (pp.toBlockShape.recs.map (·.rhss)))).getD c 0 :=
  let ⟨hcg, hcg', he⟩ := tgtCallee_edge h R hc hj (tgtCall_callee hcall)
  ConLeche.graphRank_mono hcg hcg' he

end Target

end ConLeche.Model
