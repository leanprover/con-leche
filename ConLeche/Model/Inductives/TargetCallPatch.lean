module

public import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Semantics.Tower.SumTower
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Level

public section

/-!
# Node `0`'s admissible valuation

A container field of a member constructor lands at a ROOT kid of the
member forests, whose frame stack is empty: its admissible valuations
(`AdmVal … []`) hold, at each member hole applied to indices fitting the
member's telescope at the block's parameters, an element the visit's
hypotheses hold of, and nothing elsewhere.  The walk reads the
constructor at the block's hole frame `D.frame ψ ρp Y`, whose member holes
are families over the indices only (`LfpDatum.holeVal`): `Y`'s component
where the indices fit, empty elsewhere.  So the hole frame itself satisfies
the hole context (`frame0_sat`) and is admissible at the visit's
hypotheses extended by node `0`'s own tuple (`admVal_frame0`).
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

section Block

variable {μ : ConLeche.CheckMode} {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI}
  {mpC : EnvModelM V μ envC} {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}

/-- **The hole frame satisfies the hole context**: each member's hole
value lies in the member's index family type (`holeVal_mem`). -/
theorem frame0_sat (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) {ρp : Nat → V}
    (hs : Sat V (d.params ψ).reverse ρp)
    {Y : Nat → V} (hY : InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) Y) :
    Sat V (d.holeCtx ψ).reverse (d.toLfp.frame ψ ρp Y) := by
  obtain ⟨cvTas, p, isRec, hN, hF⟩ := H.hformers
  have hcl := mpC.lfpClause_of_mem H.hd0
  simp only [BlockData.holeCtx, List.reverse_append]
  refine sat_of_spineFit hs (spineFit_range_lift d.k (fun t ht => ?_))
  obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
    ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact ht)⟩
  obtain ⟨-, hFDt⟩ := hF t cvTb hcvb
  exact LfpDatum.holeVal_mem hcl.kN hY ht (ab := (d.ppsM t ψ).drop d.nP) rfl
    (fun x hx => hFDt.bits ψ x (List.mem_of_mem_drop hx))

set_option maxHeartbeats 1000000 in
/-- **Node `0`'s hole frame is admissible** for the empty stack at the
visit's hypotheses extended by node `0`'s own tuple `Y` (at any owner
function: the empty stack has no frame hole). -/
theorem admVal_frame0 (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP))
    (hids : ∀ t, t < ctx.names.length → (d.toLfp.ids t ψ).length = ctx.nIdxs.getD t 0)
    {Y : Nat → V}
    (hY : InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ (consList (xs.take d.nP) ρ)) Y)
    (own : Nat → Nat) (G : Nat → Nat → V → V → Prop) :
    AdmVal mk mpC ctx d ns ψ ρ xs own
      (addOwn G 0 (nlDb mpC d ns 0).N
        ((nlDb mpC d ns 0).idx (nlψ envC ns ψ 0) (nlFr mpC ctx d ns ψ ρ xs 0)) Y) []
      (d.toLfp.frame ψ (consList (xs.take d.nP) ρ) Y) := by
  classical
  have hkN := lfp_namesLen mpC H.hd0
  have hcl := mpC.lfpClause_of_mem H.hd0
  have hkk : d.toLfp.k = d.k := rfl
  have hnP := H.hnP
  have hkc : ctx.names.length = d.k := by rw [H.hnames]; exact hkN
  have hhi0 : ctx.hiAt 0 = d.nP + d.k := by
    simp only [ConLeche.NestCtx.hiAt]; rw [H.hnP, hkc]; omega
  have hnl0 : nlDb mpC d ns 0 = d.toLfp := by unfold nlDb; rw [ite_eq_left rfl]
  have hnψ0 : nlψ envC ns ψ 0 = ψ := by unfold nlψ; rw [ite_eq_left rfl]
  have hnF0 : nlFr mpC ctx d ns ψ ρ xs 0 = consList (xs.take d.nP) ρ := by
    unfold nlFr; rw [ite_eq_left rfl]
  rw [hnl0, hnψ0, hnF0]
  have hsP : Sat V (d.params ψ).reverse (consList (xs.take d.nP) ρ) := by
    have := sat_of_spineFit (Sat_nil (V := V) ρ) hparams
    rwa [List.append_nil] at this
  refine ⟨?_, ?_, ?_, fun i hk hi => by simp at hi⟩
  · rw [stackCtx_nil]
    exact frame0_sat H ψ hsP hY
  · -- off the member holes: the parameters and the tail
    intro i hi
    simp only [List.length_nil] at hi
    have hik : d.k ≤ i := by
      refine Nat.le_of_not_lt fun hlt => hi ⟨by omega, by omega, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, i = q + d.k := ⟨i - d.k, by omega⟩
    rw [← hkk, LfpDatum.frame_param, hkk]
    unfold trueVal nodeTrueVal
    have hlv : ((nodeHv mpC.base2.acval envC ctx ψ [] xs.length).map
        (interp V (consList xs ρ))).length = d.k := by
      simp only [nodeHv, List.length_map, List.length_range, ConLeche.NestCtx.hiAt,
        List.length_nil]
      omega
    rw [consList_append, ← hlv, consList_apply_add, H.hnP]
  · -- a member hole: `Y` where the indices fit, nothing elsewhere
    intro t ht is his y hy
    have htk : t < d.k := by rw [← hkc]; exact ht
    have hidx : ctx.hiAt ([] : List NestHole).length - 1 - (ctx.nP + t) = d.k - 1 - t := by
      simp only [List.length_nil]; rw [hhi0, H.hnP]; omega
    rw [hidx, ← hkk, LfpDatum.frame_hole (by rw [hkk]; exact htk)] at hy
    obtain ⟨hfit, hyY⟩ := holeVal_foldl_mem (by rw [hids t ht, his]) hy
    exact ⟨fun _ => Or.inr ⟨rfl, Nat.lt_of_lt_of_le htk hcl.kN, tupW_mem hfit, hyY⟩,
      fun hn => absurd (by rw [hnP]; exact hfit) hn⟩

end Block

end ConLeche.Model
