module

public import ConLeche.Model.Inductives.TargetNodeDynOf
public import ConLeche.Model.Inductives.TargetNodeDyn
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.LfpAcc
import ConLeche.Semantics.Tower.FixLeafI
import ConLeche.Semantics.Tower.IdxEq
import ConLeche.Semantics.Tower.TowerMk
import ConLeche.Verify.Level

public section

/-!
# Node `0`'s patched valuation (lane NESTIND, session 28)

A container field of a member constructor lands at a ROOT kid of the
member forests, whose frame stack is empty: its admissible valuations
(`AdmVal … []`) hold, at each member hole, an element the visit's
hypotheses hold of at the block's own parameters and, elsewhere, one below
the member's constant.  The walk reads the constructor at the block's hole
frame `D.frame ψ ρp Y`, whose member holes are BLIND in their parameters
(`LfpDatum.holeVal`) — not admissible.  The PATCHED frame (`patchFrame`)
holds `Y` at the block's parameters `P` and the member's true value
elsewhere (`memberPatch`); it agrees with the hole frame whenever a hole
is applied to the parameters (`patchFrame_holeAgree`), so the fields —
whose holes occur only so applied (the clause's M3, `holeApp`) — fit there
alike; it satisfies the hole context (`patchFrame_sat`), and it is
admissible at the visit's hypotheses extended by node `0`'s own tuple
(`admVal_patch`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx NestHole
  BlockParts BlockShape fueledOps PosTree)

universe w

variable {V : Type w} [SetTheory V]

/-- **The patched hole frame** at the block's parameters `P` (below them
`ρ`), the tuple `Y` and the members' true values `cv`. -/
@[expose] noncomputable def patchFrame (D : LfpDatum V) (ψ : Name → Nat) (ρ : Nat → V)
    (P : List V) (Y : Nat → V) (cv : Nat → V) : Nat → V :=
  consList ((List.range D.k).map fun t => memberPatch D ψ ρ P Y (cv t) t) (consList P ρ)

section Patch

variable {acval : Name → (Name → Nat) → AnnotTerm} {D : LfpDatum V}

theorem patchFrame_hole {ψ : Name → Nat} {ρ : Nat → V} {P : List V} {Y cv : Nat → V} {t : Nat}
    (ht : t < D.k) :
    patchFrame D ψ ρ P Y cv (D.k - 1 - t) = memberPatch D ψ ρ P Y (cv t) t := by
  unfold patchFrame
  rw [consList_getD_of_lt _ _ _ (by simp; omega)]
  simp only [List.length_map, List.length_range, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range (show D.k - 1 - (D.k - 1 - t) < D.k by omega)]
  rw [show D.k - 1 - (D.k - 1 - t) = t by omega]
  rfl

theorem patchFrame_param {ψ : Name → Nat} {ρ : Nat → V} {P : List V} {Y cv : Nat → V} (i : Nat) :
    patchFrame D ψ ρ P Y cv (i + D.k) = consList P ρ i := by
  unfold patchFrame
  have := consList_apply_add ((List.range D.k).map fun t => memberPatch D ψ ρ P Y (cv t) t)
    (consList P ρ) i
  simpa using this

/-- The block's parameters fit every member's own telescope. -/
theorem spineFit_pars_of_params (hcl : LfpClause acval D) {m : Nat} (hm : m < D.k)
    {ψ : Name → Nat} {ρ : Nat → V} {P : List V} (hP : SpineFit ρ (D.params ψ) P) :
    SpineFit ρ (D.pars m ψ) P := by
  have hs := sat_of_spineFit (Sat_nil (V := V) ρ) hP
  rw [List.append_nil] at hs
  refine spineFit_of_sat_consList' ?_ (hcl.parsSat m hm ψ _ hs)
  rw [SpineFit.length_eq hP, hcl.parsLen m hm ψ]

/-- **The patched frame agrees with the hole frame** where a hole is
applied to the block's parameters. -/
theorem patchFrame_holeAgree (hcl : LfpClause acval D) {ψ : Name → Nat} {ρ : Nat → V}
    {P : List V} (hP : SpineFit ρ (D.params ψ) P) (Y cv : Nat → V) :
    HoleAgree D.k (D.params ψ).length 0 (D.frame ψ (consList P ρ) Y) (patchFrame D ψ ρ P Y cv) := by
  have hPl : P.length = (D.params ψ).length := SpineFit.length_eq hP
  refine LfpDatum.holeAgree_frame (by simp) fun m hm is => ?_
  rw [List.getElem_map, List.getElem_range]
  rw [frameIdx_consList hPl]
  have hpl : (D.pars m ψ).length = P.length := by rw [hcl.parsLen m hm ψ, hPl]
  have hfit := spineFit_pars_of_params hcl hm hP
  unfold LfpDatum.holeVal memberPatch
  rw [hpl, shiftE_consList, holeFam_append_apply _ _ _ hfit,
    holeFam_append_apply _ _ _ hfit]
  congr 2
  funext bs
  rw [List.take_left, if_pos rfl]

/-- **The fields fit the patched frame** exactly where they fit the hole
frame (M3). -/
theorem patchFrame_fit (hcl : LfpClause acval D) {ψ : Name → Nat} {ρ : Nat → V}
    {P : List V} (hP : SpineFit ρ (D.params ψ) P) (Y cv : Nat → V) {c j : Nat} (hc : c < D.N)
    (hj : j < D.nctors c) (fs : List V) :
    SpineFit (D.frame ψ (consList P ρ) Y) (D.fields ψ c j) fs ↔
      SpineFit (patchFrame D ψ ρ P Y cv) (D.fields ψ c j) fs :=
  spineFit_congr_holeApp _ (fun l F hF => by simpa using (hcl.holeApp ψ c hc j hj).1 l F hF)
    (patchFrame_holeAgree hcl hP Y cv) fs

end Patch

/-! ## At the block -/

section Block

variable {μ : ConLeche.CheckMode} {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI}
  {mpC : EnvModelM V μ envC} {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}

/-- The block's members' true values, at the prefix spine. -/
@[expose] noncomputable def memberTrue (mpC : EnvModelM V μ envC) (ctx : NestCtx) (ψ : Name → Nat)
    (ρ : Nat → V) (xs : List V) (t : Nat) : V :=
  trueVal mpC ctx ψ ρ xs [] (ctx.hiAt 0 - 1 - (ctx.nP + t))

/-- A member's true value is its former's leaf, read anywhere. -/
theorem memberTrue_eq (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hxs : ctx.nP ≤ xs.length) {t : Nat} (ht : t < d.k) (σ : Nat → V) :
    memberTrue mpC ctx ψ ρ xs t = interp V σ (mk.base2.acval (d.memberName t) ψ) := by
  have hkN := lfp_namesLen mpC H.hd0
  have htn : t < ctx.names.length := by rw [H.hnames]; exact hkN ▸ ht
  obtain ⟨cv, caps, hf, hlps⟩ := H.hlpsM _ (List.getElem_mem htn)
  have hlen : (ctx.lps.map Level.param).length = cv.levelParams.length := by
    rw [List.length_map, hlps]
  unfold memberTrue
  have e := trueVal_member mpC ctx ψ ρ xs hxs [] htn
  simp only [List.length_nil] at e
  rw [e, dyn_constRead H hf hlen, hlps, ConLeche.Level.substFn_param_self,
    acval_interp_closed mk.base2 _ ψ ρ σ]
  congr 2
  show ctx.names[t] = d.memberNames.getD t .anonymous
  rw [List.getD_eq_getElem?_getD, ← show d.toLfp.names = d.memberNames from rfl, ← H.hnames,
    List.getElem?_eq_getElem htn, Option.getD_some]

set_option maxHeartbeats 1000000 in
/-- **The patched frame satisfies the hole context**: at the block's
parameters a patched hole is `Y`'s family (a hole value's, in the member's
type as `holeVal_mem`), elsewhere the member's constant applied (its
former's type). -/
theorem patchFrame_sat (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hxs : ctx.nP ≤ xs.length) {P : List V} (hP : SpineFit ρ (d.params ψ) P)
    {Y : Nat → V} (hY : InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList P ρ)) Y) :
    Sat V (d.holeCtx ψ).reverse
      (patchFrame d.toLfp ψ ρ P Y (memberTrue mpC ctx ψ ρ xs)) := by
  obtain ⟨cvTas, p, isRec, hN, hF⟩ := H.hformers
  have hkN := lfp_namesLen mpC H.hd0
  have hcl := mpC.lfpClause_of_mem H.hd0
  have hsP : Sat V (d.params ψ).reverse (consList P ρ) := by
    have := sat_of_spineFit (Sat_nil (V := V) ρ) hP
    rwa [List.append_nil] at this
  unfold patchFrame
  simp only [BlockData.holeCtx, List.reverse_append]
  refine sat_of_spineFit hsP (spineFit_range_closed d.k (fun t ht σ => ?_) _)
  obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
  obtain ⟨hfb, hFDt⟩ := hF t cvTb hcvb
  have hmemT : ∀ σ' : Nat → V, memberTrue mpC ctx ψ ρ xs t
      ∈ˢ interp V σ' (mkPisAV (d.ppsM t ψ) (.sort (d.w ψ))) := by
    intro σ'
    rw [memberTrue_eq H ψ ρ xs hxs ht σ', show d.memberName t = cvTb.name from hN.1 t cvTb hcvb]
    exact mk.mem_type _ (List.mem_of_find?_eq_some hfb) ψ _ (hFDt.read ψ) σ'
  have hcl0 : Term.bvarsBelow 0 (mkPisAV (d.ppsM t ψ) (.sort (d.w ψ))).erase := by
    have := mkPisAV_below_of (C := .sort (d.w ψ)) (hFDt.below ψ)
      (by simp [AnnotTerm.erase, Term.bvarsBelow])
    simpa using this
  rw [interp_closed V hcl0 σ ρ]
  have hab : (d.ppsM t ψ).map (·.2.2) = d.toLfp.pars t ψ ++ d.toLfp.ids t ψ := by
    show _ = ((d.ppsM t ψ).take d.nP).map (·.2.2) ++ ((d.ppsM t ψ).drop d.nP).map (·.2.2)
    rw [← List.map_append, List.take_append_drop]
  have htN : t < d.toLfp.N := Nat.lt_of_lt_of_le ht hcl.kN
  unfold memberPatch
  rw [← hab]
  refine holeFam_mem_mkPisAV (hFDt.bits ψ) fun vs hvs => ?_
  split
  · rw [interp_sort]
    by_cases hT : tupW (d.toLfp.u t ψ) (vs.drop (d.toLfp.pars t ψ).length)
        ∈ˢ d.toLfp.idx ψ (consList P ρ) t
    · exact app_mem_of_mem_piSet (hY t htN) hT
    · rw [app_off_dom_of_mem_piSet (hY t htN) hT]
      exact empty_mem_univ _
  · exact foldl_app_mem_mkPisAV_pos (hFDt.bits ψ) hvs (hmemT ρ)

set_option maxHeartbeats 1000000 in
/-- **Node `0`'s patched valuation is admissible** for the empty stack at
the visit's hypotheses extended by node `0`'s own tuple `Y` (at any owner
function: the empty stack has no frame hole). -/
theorem admVal_patch (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    (hids : ∀ t, t < ctx.names.length → (d.toLfp.ids t ψ).length = ctx.nIdxs.getD t 0)
    {Y : Nat → V}
    (hY : InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ)) Y)
    (own : Nat → Nat) (G : Nat → Nat → V → V → Prop) :
    AdmVal mk mpC ctx d ns ψ ρ xs own
      (addOwn G 0 (nlDb mpC d ns 0).N
        ((nlDb mpC d ns 0).idx (nlψ envC ns ψ 0) (nlFr mpC ctx d ns ψ ρ xs 0)) Y) []
      (patchFrame d.toLfp ψ ρ (xs.take d.nP) Y (memberTrue mpC ctx ψ ρ xs)) := by
  classical
  have hkN := lfp_namesLen mpC H.hd0
  have hcl := mpC.lfpClause_of_mem H.hd0
  have hxs' : ctx.nP ≤ xs.length := by rw [H.hnP]; exact hxs
  have hPl : (xs.take d.nP).length = (d.toLfp.params ψ).length := hparams.length_eq
  have hkk : d.toLfp.k = d.k := rfl
  have hnP := H.hnP
  have hPn : (xs.take d.nP).length = d.nP := by rw [List.length_take]; omega
  have hkc : ctx.names.length = d.k := by rw [H.hnames]; exact hkN
  have hhi0 : ctx.hiAt 0 = d.nP + d.k := by
    simp only [ConLeche.NestCtx.hiAt]; rw [H.hnP, hkc]; omega
  have hnl0 : nlDb mpC d ns 0 = d.toLfp := by unfold nlDb; rw [if_pos rfl]
  have hnψ0 : nlψ envC ns ψ 0 = ψ := by unfold nlψ; rw [if_pos rfl]
  have hnF0 : nlFr mpC ctx d ns ψ ρ xs 0 = consList (xs.take d.nP) ρ := by
    unfold nlFr; rw [if_pos rfl]
  rw [hnl0, hnψ0, hnF0]
  refine ⟨?_, ?_, ?_, fun i hk hi => by simp at hi⟩
  · rw [stackCtx_nil]
    exact patchFrame_sat H ψ ρ xs hxs' hparams hY
  · -- off the member holes: the parameters and the tail
    intro i hi
    simp only [List.length_nil] at hi
    have hik : d.k ≤ i := by
      refine Nat.le_of_not_lt fun hlt => hi ⟨by omega, by omega, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, i = q + d.k := ⟨i - d.k, by omega⟩
    rw [← hkk, patchFrame_param, hkk]
    unfold trueVal nodeTrueVal
    have hlv : ((nodeHv mpC.base2.acval envC ctx ψ []).map (interp V ρ)).length = d.k := by
      simp [nodeHv, nodeHoleConsts, hkc]
    rw [consList_append, ← hlv, consList_apply_add, H.hnP]
  · -- a member hole: `Y` at the block's parameters, the true value elsewhere
    intro t ht as has y hy
    have htk : t < d.k := by rw [← hkc]; exact ht
    have hpl : (d.toLfp.pars t ψ).length = d.nP := by
      rw [hcl.parsLen t (by rw [hkk]; exact htk) ψ, ← hPl, hPn]
    have hidx : ctx.hiAt ([] : List NestHole).length - 1 - (ctx.nP + t) = d.k - 1 - t := by
      simp only [List.length_nil]; rw [hhi0, H.hnP]; omega
    rw [hidx, ← hkk, patchFrame_hole (by rw [hkk]; exact htk)] at hy
    rw [hidx]
    have hasl : as.length = (d.toLfp.pars t ψ ++ d.toLfp.ids t ψ).length := by
      rw [List.length_append, hpl, hids t ht, has, H.hnP]
    unfold memberPatch at hy
    rcases holeFam_foldl_full (ρ := ρ) (Fs := d.toLfp.pars t ψ ++ d.toLfp.ids t ψ) (vs := as)
        (fun as => if as.take (d.toLfp.pars t ψ).length = xs.take d.nP then
          app (Y t) (tupW (d.toLfp.u t ψ) (as.drop (d.toLfp.pars t ψ).length))
        else as.foldl app (memberTrue mpC ctx ψ ρ xs t)) hasl with ⟨hfit, heq⟩ | he
    · rw [heq] at hy
      obtain ⟨as₁, as₂, rfl, h1, h2⟩ := spineFit_append_split hfit
      have hl1 : as₁.length = d.nP := by rw [SpineFit.length_eq h1, hpl]
      rw [H.hnP, List.take_left' hl1, List.drop_left' hl1]
      simp only [hpl, List.take_left' hl1, List.drop_left' hl1] at hy
      by_cases hP' : as₁ = xs.take d.nP
      · rw [if_pos hP'] at hy
        subst hP'
        refine ⟨fun _ hfit2 => Or.inr ⟨rfl, Nat.lt_of_lt_of_le htk hcl.kN, tupW_mem hfit2, hy⟩,
          fun hn => absurd ⟨rfl, h2⟩ hn⟩
      · rw [if_neg hP'] at hy
        have hidx0 : ctx.hiAt 0 - 1 - (ctx.nP + t) = d.k - 1 - t := by rw [hhi0, H.hnP]; omega
        unfold memberTrue at hy
        rw [hidx0] at hy
        exact ⟨fun h => absurd h hP', fun _ => hy⟩
    · rw [he] at hy
      exact absurd hy (not_mem_empty y)

end Block

end ConLeche.Model
