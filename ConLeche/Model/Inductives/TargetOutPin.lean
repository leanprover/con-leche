module

import ConLeche.Model.Annot.Laws
public import ConLeche.Model.IndFrame
import ConLeche.Model.IndPointKit
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Model.Inductives.SumKit
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Model.Inductives.HoleSubst

public section

/-!
# An outside rule's index readings, from the fired pin

At an outside class the rule contract's INDEX conjunct asks that the
class's index expressions (`tgtOutEs`), read at the rule's frame, be
the recursor's index arguments.  Where the class is `Type`-valued the
carrier's case analysis gives it (the container's injection is
injective); where it is `Prop`-valued it does not — every injection is
the point, and the carrier at two index tuples may both hold it.  What
gives it at every sort is the fired modeled-iota contract's own index
pin (`IotaIndexPin`): the constructor's residual at the fired spine is
an application whose trailing arguments ARE the recursor's index
arguments.

This file is that identification, stated over readings alone
(`idxRow_of_pin`): the constructor's stored type reads as a Π-tower
`mkPisAV pps B0` over its parameters and fields with conclusion
`B0 = h0 argsR`; the fired residual is `B0` instantiated at the fired
spine `ys`; the instantiated constructor's reading `C` is `T0` peeled at
the major's parameter readings `dsa`, whose conclusion is `hC0 (ps ++
es)`; where the fired parameters' values are `dsa`'s, the conclusion's
index arguments `es` read, at the fields, as the pin's.

The two instantiations are compared by value (`interp_instSeq_under`:
instantiating below `n` binders is evaluating at the chain inserted
below them), since `ys`'s parameters and `dsa` are different terms at
different frames.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Frames -/

/-- **Instantiation below `n` binders is evaluation at the chain
inserted below them**: `interp_instSeq` under a pushed list of `n`
values. -/
theorem interp_instSeq_under :
    ∀ (ws : List AnnotTerm) (e : AnnotTerm) (σ : Nat → V) (fs : List V),
      interp V (consList fs σ)
          (ConLeche.Model.AnnotTerm.instSeq ws (ws.length - 1 + fs.length) e)
        = interp V (consList fs (chain V σ ws)) e := by
  intro ws
  induction ws with
  | nil => intro e σ fs; rfl
  | cons w ws ih =>
    intro e σ fs
    rw [show (w :: ws).length - 1 + fs.length = ws.length + fs.length by simp,
      AnnotTerm.instSeq_cons]
    have hcut : ConLeche.Model.AnnotTerm.instSeq ws (ws.length + fs.length - 1)
          (e.inst w (ws.length + fs.length))
        = ConLeche.Model.AnnotTerm.instSeq ws (ws.length - 1 + fs.length)
          (e.inst w (ws.length + fs.length)) := by
      cases ws with
      | nil => rfl
      | cons _ _ => congr 1; simp only [List.length_cons]; omega
    rw [hcut, ih, interp_inst]
    have hsh : shiftE (ws.length + fs.length) 0 (consList fs (chain V σ ws)) = σ := by
      funext i
      simp only [shiftE, Nat.not_lt_zero, if_false]
      rw [show i + (ws.length + fs.length) = (i + ws.length) + fs.length by omega,
        consList_apply_add, chain_ge (by omega), Nat.add_sub_cancel]
    rw [hsh, Nat.add_comm ws.length fs.length, instE_consList_add, ← chain_cons_eq_instE]

omit [SetTheory V] in
/-- Instantiation passes under a Π-tower, at the cut moved past its
binders. -/
theorem inst_mkPisAV (a : AnnotTerm) :
    ∀ (ds : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm) (t : Nat),
      ∃ ds' : List (Nat × Nat × AnnotTerm), ds'.length = ds.length ∧
        (mkPisAV ds B).inst a t = mkPisAV ds' (B.inst a (t + ds.length))
  | [], B, t => ⟨[], rfl, rfl⟩
  | d :: ds, B, t => by
    obtain ⟨ds', hl, he⟩ := inst_mkPisAV a ds B (t + 1)
    refine ⟨(d.1, d.2.1, d.2.2.inst a t) :: ds', by simp [hl], ?_⟩
    simp only [mkPisAV, AnnotTerm.inst_pi, he, List.length_cons]
    rw [show t + 1 + ds.length = t + (ds.length + 1) by omega]

omit [SetTheory V] in
/-- Spine instantiation passes under a Π-tower. -/
theorem instSeq_mkPisAV :
    ∀ (ws : List AnnotTerm) (ds : List (Nat × Nat × AnnotTerm)) (B : AnnotTerm),
      ∃ ds' : List (Nat × Nat × AnnotTerm), ds'.length = ds.length ∧
        ConLeche.Model.AnnotTerm.instSeq ws (ws.length - 1) (mkPisAV ds B)
          = mkPisAV ds' (ConLeche.Model.AnnotTerm.instSeq ws (ws.length - 1 + ds.length) B)
  | [], ds, B => ⟨ds, rfl, rfl⟩
  | w :: ws, ds, B => by
    obtain ⟨ds1, hl1, he1⟩ := inst_mkPisAV w ds B ws.length
    obtain ⟨ds2, hl2, he2⟩ := instSeq_mkPisAV ws ds1 (B.inst w (ws.length + ds.length))
    refine ⟨ds2, by rw [hl2, hl1], ?_⟩
    rw [show (w :: ws).length - 1 = ws.length by simp, AnnotTerm.instSeq_cons, he1, he2,
      show ws.length + ds.length = (w :: ws).length - 1 + ds.length by simp,
      AnnotTerm.instSeq_cons, hl1]
    cases ws with
    | nil => rfl
    | cons _ _ => congr 2; simp only [List.length_cons]; omega

omit [SetTheory V] in
/-- Π-towers of one length are equal only at equal bodies. -/
theorem mkPisAV_body_inj {ds ds' : List (Nat × Nat × AnnotTerm)} {b b' : AnnotTerm}
    (h : mkPisAV ds b = mkPisAV ds' b') (hl : ds.length = ds'.length) : b = b' := by
  have h1 := stripPisAV_mkPisAV ds b
  rw [h, hl, stripPisAV_mkPisAV ds' b'] at h1
  exact (Prod.mk.inj (Option.some.inj h1)).2.symm

/-! ## The index readings -/

/-- **The fired pin identifies the index readings** (see the module
docstring): a constructor type `T0 = mkPisAV pps (h0 argsR)` over `nPc`
parameters and `nF` fields, fitted at the fired spine `ys` to the pin's
residual and peeled at the parameter readings `dsa` (whose values are
the fired parameters') to `mkPisAV fps (hC0 (ps ++ es))`: the index
arguments `es`, read at the fields, are the recursor's index arguments. -/
theorem idxRow_of_pin {T0 B0 h0 C hC0 restC : AnnotTerm}
    {pps fps : List (Nat × Nat × AnnotTerm)} {argsR ps es ys dsa xs : List AnnotTerm}
    {nPc nF mI rP : Nat} {ρ σ : Nat → V}
    (hT0 : T0 = mkPisAV pps B0) (hpl : pps.length = nPc + nF)
    (hB0 : B0 = AnnotTerm.mkAppN h0 argsR)
    (hB0cl : Term.bvarsBelow (nPc + nF) B0.erase)
    (hyl : ys.length = nPc + nF) (hfitC : TeleFitPA V ρ T0 ys restC)
    (hdl : dsa.length = nPc) (hC : ConLeche.Model.AnnotTerm.peelPis T0 dsa = some C)
    (hCeq : C = mkPisAV fps (AnnotTerm.mkAppN hC0 (ps ++ es))) (hfl : fps.length = nF)
    (hlenA : argsR.length = ps.length + es.length) (hpsl : ps.length = nPc)
    (hvals : (ys.take nPc).map (interp V ρ) = dsa.map (interp V σ))
    (hpin : IotaIndexPin (V := V) ρ restC nPc mI rP xs)
    (hxl : xs.length = mI) (hlenE : es.length = mI - rP) :
    es.map (interp V (consList ((ys.drop nPc).map (interp V ρ)) σ))
      = (xs.drop rP).map (interp V ρ) := by
  -- the residual: the conclusion at the fired spine
  have hrest : restC = AnnotTerm.mkAppN
      (ConLeche.Model.AnnotTerm.instSeq ys (nPc + nF - 1) h0)
      (argsR.map (ConLeche.Model.AnnotTerm.instSeq ys (nPc + nF - 1))) := by
    have hpt := piTeleAV_mkPisAV pps B0
    rw [hpl, ← hT0] at hpt
    rw [teleFitPA_rest_eq (nPc + nF) hpt hyl hfitC, hB0, instSeqAV_mkAppN]
  -- the instantiated constructor's conclusion: the conclusion at the parameters
  have hsplit : T0 = mkPisAV (pps.take nPc) (mkPisAV (pps.drop nPc) B0) := by
    rw [hT0, ← mkPisAV_append, List.take_append_drop]
  have hpt2 := piTeleAV_mkPisAV (pps.take nPc) (mkPisAV (pps.drop nPc) B0)
  rw [← hsplit, List.length_take, Nat.min_eq_left (by omega)] at hpt2
  rw [peelPis_of_piTeleAV nPc hpt2 hdl] at hC
  obtain ⟨ds', hl', hds'⟩ := instSeq_mkPisAV dsa (pps.drop nPc) B0
  rw [hdl, List.length_drop, hpl, show nPc + nF - nPc = nF by omega] at hds'
  have hbody : ConLeche.Model.AnnotTerm.instSeq dsa (nPc - 1 + nF) B0
      = AnnotTerm.mkAppN hC0 (ps ++ es) := by
    have hC' : C = ConLeche.Model.AnnotTerm.instSeq dsa (nPc - 1) (mkPisAV (pps.drop nPc) B0) :=
      (Option.some.inj hC).symm
    have hlen' : ds'.length = fps.length := by
      rw [hl', List.length_drop, hpl, hfl]; omega
    exact mkPisAV_body_inj (hds'.symm.trans (hC'.symm.trans hCeq)) hlen'
  rw [hB0, instSeqAV_mkAppN] at hbody
  obtain ⟨-, hargs⟩ := AnnotTerm.mkAppN_inj hbody (by rw [List.length_map, hlenA,
    List.length_append])
  -- per index argument
  have hfsl : ((ys.drop nPc).map (interp V ρ)).length = nF := by
    rw [List.length_map, List.length_drop, hyl]; omega
  have hargsCl : ∀ a ∈ argsR, Term.bvarsBelow (nPc + nF) a.erase := by
    intro a ha
    rw [hB0, AnnotTerm.erase_mkAppN] at hB0cl
    exact (bvarsBelow_mkAppN_inv hB0cl).2 _ (List.mem_map.mpr ⟨a, ha, rfl⟩)
  refine List.ext_getElem (by rw [List.length_map, List.length_map, List.length_drop, hxl,
    hlenE]) fun l h1 h2 => ?_
  rw [List.length_map, hlenE] at h1
  have hl : nPc + l < argsR.length := by rw [hlenA, hpsl]; omega
  -- the conclusion's argument, both ways
  have hesl : es[l]'(by rw [hlenE]; exact h1)
      = ConLeche.Model.AnnotTerm.instSeq dsa (nPc - 1 + nF) (argsR[nPc + l]'hl) := by
    have hq := congrArg (fun L => L[nPc + l]?) hargs
    simp only [List.getElem?_map, List.getElem?_eq_getElem hl, Option.map_some] at hq
    rw [List.getElem?_append_right (by omega), hpsl, Nat.add_sub_cancel_left,
      List.getElem?_eq_getElem (by rw [hlenE]; exact h1)] at hq
    exact (Option.some.inj hq).symm
  -- the pin's argument
  obtain ⟨Ha, cargsa, hrestEq, hcarLen, hcarI⟩ := hpin
  have hcarLen' : cargsa.length = nPc + (mI - rP) := by
    rcases hcarLen with hc | hq
    · omega
    · exact hq
  obtain ⟨-, hcargs⟩ := AnnotTerm.mkAppN_inj (hrestEq.symm.trans hrest)
    (by rw [hcarLen', List.length_map, hlenA, hpsl, hlenE])
  have hcar := hcarI l (by omega)
  have hcel : cargsa.getD (nPc + l) default
      = ConLeche.Model.AnnotTerm.instSeq ys (nPc + nF - 1) (argsR[nPc + l]'hl) := by
    rw [hcargs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl]
    rfl
  rw [hcel, show nPc + nF - 1 = ys.length - 1 by rw [hyl], interp_instSeq] at hcar
  rw [List.getElem_map, List.getElem_map, List.getElem_drop, hesl,
    show nPc - 1 + nF = dsa.length - 1 + ((ys.drop nPc).map (interp V ρ)).length by
      rw [hdl, hfsl],
    interp_instSeq_under,
    show xs[rP + l] = xs.getD (rP + l) default from by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl,
    ← hcar]
  -- the two frames agree below the parameters and fields
  refine interp_congr_below (V := V) _ (nPc + nF) _ _ (hargsCl _ (List.getElem_mem hl)) fun i hi => ?_
  rw [chain_eq_consList, chain_eq_consList, ← consList_append,
    show ys.map (interp V ρ) = (ys.take nPc).map (interp V ρ) ++ (ys.drop nPc).map (interp V ρ)
      by rw [← List.map_append, List.take_append_drop],
    hvals]
  have hL : (dsa.map (interp V σ) ++ (ys.drop nPc).map (interp V ρ)).length = nPc + nF := by
    rw [List.length_append, List.length_map, hdl, hfsl]
  rw [consList_getD_of_lt _ _ _ (by rw [hL]; exact hi),
    consList_getD_of_lt _ _ _ (by rw [hL]; exact hi)]

end ConLeche.Model
