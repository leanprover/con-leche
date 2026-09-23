module

public import ConLeche.Model.Inductives.BlockRep
import ConLeche.Semantics.Kit
import ConLeche.Model.Inductives.BlockModel
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Model.NatEqs
import ConLeche.Semantics.Tower.BlockRecI
public section

/-!
# The block's lfp clause IN HOLE FORM, from the representation (lane HOLE2)

Charter item 2: every stored `I p⃗` is the least fixed point of its
right-hand-side operator — the interpretation of its constructor types
with holes at the block's members.  The clause the environment records
(`Model/Annot/BlockLfp.lean`) says so through `LfpClause.holes`: the fit
relation of the operator's fibre IS the telescope fit of the
constructors' fields with holes (`BlockData.absF`, `BlockRep.lean`) at
the hole frame (`LfpDatum.frame`: the parameter frame with each member's
hole holding the tuple's family, curried).

This file proves it for a uniform block from its representation
(`BlockModelAt`) and its constructors' reading facts (`BlockCtorFacts`):

* a hole-free field reads at the hole frame as it reads at the parameter
  frame (`interp_liftN_consList2`);
* a field reading a member reads, at the hole frame of `X`, as the
  fixpoint route's slot at `X` (`interp_absField_rec`): the member's hole
  applied to the block's parameters and the field's index readings is
  `X`'s component at their tuple (`LfpDatum.holeVal_app`), under the
  field's own telescope (`interp_liftTeleK_piTele`) — the index readings
  fitting the target's telescope being `BlockModelAt.idxFit`;
* so the fixpoint route's fit (`ChainFit`) and the hole fit (`HFits`) are
  one relation (`blockReadsHoles`), and the clause (`BlockModelAt.toLfp`)
  gains `holes`, `mkZero`, `mkInj` and `ctor` (E2E-DESIGN's U3).

The slot-to-domain identity at the carrier (`blockSlot_eq_entry`, moved
here from `BlockRecPreRun.lean` so the install can record the clause) is
what turns the hole fit at the carrier into the constructor's own
domains' fit for `ctor`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Frames (moved from `BlockRecPreRun.lean`) -/

/-- **A frame's `k`-th entry, as a bvar.** -/
theorem interp_bvarAt {L : List V} {ρ : Nat → V} {k : Nat} (hk : k < L.length) :
    interp V (consList L ρ) (.bvar (L.length - 1 - k)) = L.getD k pt := by
  rw [interp_bvar, consList_getD_of_lt L ρ _ (by omega),
    show L.length - 1 - (L.length - 1 - k) = k from by omega]

/-- A prefix of a list, as its first entries. -/
theorem take_eq_map_getD : ∀ (L : List V) (n : Nat), n ≤ L.length →
    L.take n = (List.range n).map fun k => L.getD k pt := by
  intro L n hn
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  have hi : i < n := by
    have := h1
    simp only [List.length_take] at this
    omega
  rw [List.getElem_take, List.getElem_map, List.getElem_range,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  rfl

/-- The parameter bvars read the frame's first `nP` entries. -/
theorem map_bvarAt_take {L : List V} {ρ : Nat → V} {nP D : Nat} (hD : D = L.length)
    (hnP : nP ≤ L.length) :
    (paramBvarsAt nP D).map (interp V (consList L ρ)) = L.take nP := by
  subst hD
  rw [take_eq_map_getD L nP hnP, paramBvarsAt, List.map_map]
  refine List.map_congr_left fun k hk => ?_
  exact interp_bvarAt (by simpa using Nat.lt_of_lt_of_le (List.mem_range.mp hk) hnP)

/-! ## The slot IS the domain's reading at the carrier (moved from `BlockRecPreRun.lean` §25) -/

section SlotEntry

/-- **The slot-to-domain identity at a recursive position.** -/
theorem blockSlot_eq_entry {env : Env} {mo : EnvModel V env} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mo names d) {lps : List Name}
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hcf : BlockCtorFacts mo d lps c j cA)
    {ψ : Name → Nat} {ρ : Nat → V} {as bs : List V} {l : Nat}
    (hasLen : as.length = d.nP) (hps : SpineFit ρ (d.params ψ) as)
    (hl : l < cA.2) (hbs : bs.length = l) (htgt : d.tgts c j l < d.k)
    (hSF : SlotFit (d.uM (d.tgts c j l) ψ) (d.w ψ) (consList as ρ) (d.IdsM (d.tgts c j l) ψ)
      (((d.tlss c ψ).getD j []).getD l []) (((d.Eiss c ψ).getD j []).getD l []) bs)
    (hrec : ((d.rss c).getD j []).getD l false = true) :
    d.slotAt ψ (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) c j l
        (consList bs (consList as ρ))
      = interp V (consList bs (consList as ρ)) (((d.Fss c ψ).getD j []).getD l default) := by
  classical
  obtain ⟨-, -, hD⟩ := hcf
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hcj
  have hlenD : (d.dsF c j ψ).length = d.nP + cA.2 := hD.len ψ
  have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hTlD : (d.tlss c ψ).getD j [] = d.tssF c j ψ := tlssOfR_fixCtorDataList_getD hcj
  have hEiD : (d.Eiss c ψ).getD j [] = d.eissF c j ψ := eissOfR_fixCtorDataList_getD hcj
  have hksLen : (d.ksF c j).length = cA.2 := hD.ksLen
  have hkind : (d.ksF c j).getD l .ordinary = .recursive
      ∨ (d.ksF c j).getD l .ordinary = .reflexive := by
    have hrs : (d.rss c).getD j [] = rsOf (d.ksF c j) := rssOfK_getD hj
    rw [hrs] at hrec
    exact (rsOf_getD_iff (by rw [hksLen]; exact hl)).mp hrec
  -- the frame, as one list
  have hfrm : consList bs (consList as ρ) = consList (as ++ bs) ρ := (consList_append as bs ρ).symm
  have hlenAB : (as ++ bs).length = d.nP + l := by rw [List.length_append, hasLen, hbs]
  have htakeAB : (as ++ bs).take d.nP = as := by
    rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
  -- the leaf, at a fitting index spine
  have hleaf : ∀ is : List V, SpineFit (consList as ρ) (d.IdsM (d.tgts c j l) ψ) is →
      ∀ σ : Nat → V,
      (as ++ is).foldl app (interp V σ (mo.acval (d.memberName (d.tgts c j l)) ψ))
        = app (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))
            (d.tgts c j l)) (tupW (d.uM (d.tgts c j l) ψ) is) := by
    intro is his σ
    rw [acval_interp_closedC mo (d.memberName (d.tgts c j l)) ψ σ ρ]
    exact hM.leaf (d.tgts c j l) htgt ψ ρ as is hps his
  rw [hFssD, drop_map_getD hlenD hl, BlockData.slotAt]
  rcases hkind with hk | hk
  · -- a FINITARY recursive field: an empty telescope
    have hnone : ((d.tlss c ψ).getD j []).getD l [] = [] := by
      rw [hTlD]
      exact hD.tssNone ψ l (by rw [hk]; intro hcon; cases hcon)
    have hentry : ((d.dsF c j ψ).getD (d.nP + l) default).2.2
        = AnnotTerm.mkAppN (mo.acval (d.memberName (d.tgts c j l)) ψ)
            (paramBvarsAt d.nP (d.nP + l) ++ ((d.Eiss c ψ).getD j []).getD l []) := by
      rw [hEiD]
      exact hD.recEntry ψ l hk hl
    have hfit0 := (hSF.2.2 [] (by rw [hnone]; trivial)).2
    simp only [List.append_nil] at hfit0
    rw [hentry, hnone, slotSet_nil, interp_mkAppN, foldl_app_map, List.map_append, hfrm,
      map_bvarAt_take (hD := hlenAB.symm) (by omega), htakeAB]
    exact (hleaf _ (by rw [hfrm] at hfit0; exact hfit0) _).symm
  · -- a REFLEXIVE field: the nested product of the target's family
    have hentry : ((d.dsF c j ψ).getD (d.nP + l) default).2.2
        = mkPisAV (((d.tlss c ψ).getD j []).getD l [])
            (AnnotTerm.mkAppN (mo.acval (d.memberName (d.tgts c j l)) ψ)
              (paramBvarsAt d.nP (d.nP + l + ((((d.tlss c ψ).getD j []).getD l [])).length)
                ++ ((d.Eiss c ψ).getD j []).getD l [])) := by
      rw [hEiD, hTlD]
      exact hD.reflEntry ψ l hk hl
    have hbits : ∀ dd ∈ ((d.tlss c ψ).getD j []).getD l [], (dd.2.1 = 0 ↔ d.w ψ = 0) := by
      rw [hTlD]
      exact fun dd hdd => hD.tssBits ψ l dd hdd
    rw [hentry]
    unfold slotSet
    refine (interp_mkPisAV_piTele (v := d.w ψ) (acc := []) hbits ?_).symm
    intro ts hsp
    have htsLen : ts.length = ((((d.tlss c ψ).getD j []).getD l [])).length := by
      rw [hsp.length_eq, List.length_map]
    have hfrm2 : consList ts (consList bs (consList as ρ)) = consList (as ++ bs ++ ts) ρ := by
      rw [consList_append, consList_append]
    have hlenABT : (as ++ bs ++ ts).length
        = d.nP + l + ((((d.tlss c ψ).getD j []).getD l [])).length := by
      rw [List.length_append, hlenAB, htsLen]
    have htakeABT : (as ++ bs ++ ts).take d.nP = as := by
      rw [List.take_append_of_le_length (by rw [hlenAB]; omega), htakeAB]
    have hfit := (hSF.2.2 ts hsp).2
    rw [consList_append] at hfit
    rw [List.nil_append, interp_mkAppN, foldl_app_map, List.map_append, hfrm2,
      map_bvarAt_take (hD := hlenABT.symm) (by rw [hlenABT]; omega), htakeABT]
    exact hleaf _ (by rw [hfrm2] at hfit; exact hfit) _

/-- **§24's `hslot`, as a function of the run**: the agreement at
every recursive position, at every frame the walk reaches.  The only
thing the frame contributes is the prefix's LENGTH — the fitting
content is `hEis`, the field's index readings landing in the target
member's index telescope. -/
theorem blockSlot_agree {env : Env} {mo : EnvModel V env} {names : List Name}
    {d : BlockData V} (hM : BlockModelAt mo names d) {lps : List Name}
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hcf : BlockCtorFacts mo d lps c j cA)
    {ψ : Name → Nat} {ρ : Nat → V} {as : List V}
    (hasLen : as.length = d.nP) (hps : SpineFit ρ (d.params ψ) as)
    (htgt : ∀ l, l < cA.2 → d.tgts c j l < d.k)
    (hc : c < d.N) (hj : j < (d.ctorsM c).length) {_t : V}
    (ht : _t ∈ˢ d.idx ψ (consList as ρ) c)
    (hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList as ρ))
      (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ)))) :
    ∀ l, l < ((d.Fss c ψ).getD j []).length → ∀ bs : List V,
      FitsFrom ((d.rss c).getD j [])
        (d.slotAt ψ (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) c j)
        0 (consList as ρ) (((d.Fss c ψ).getD j []).take l) bs →
      ((d.rss c).getD j []).getD l false = true →
      d.slotAt ψ (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) c j l
          (consList bs (consList as ρ))
        = interp V (consList bs (consList as ρ)) (((d.Fss c ψ).getD j []).getD l default) := by
  have hnF : ((d.Fss c ψ).getD j []).length = cA.2 := by
    obtain ⟨-, -, hD⟩ := hcf
    have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
      fssOfR_fixCtorDataList_getD hcj
    rw [hFssD, List.length_map, List.length_drop, hD.len ψ]
    omega
  intro l hl bs hb hrec
  have hbs : bs.length = l := by
    have := hb.length_eq
    rw [List.length_take] at this
    omega
  have hSF := hM.idxFit ψ (consList as ρ) (d.satOfSpine hps) _ hX c hc _t ht j hj l hl hrec bs hb
  rw [hnF] at hl
  exact blockSlot_eq_entry hM hcj hcf hasLen hps hl hbs (htgt l hl) hSF hrec

end SlotEntry

/-! ## Reading below the holes -/

/-- **A term lifted over variables inserted below a spine** reads at the
frame with them as the term at the frame without. -/
theorem interp_liftN_consList2 (e : AnnotTerm) (bs hs : List V) (ρ : Nat → V) :
    interp V (consList bs (consList hs ρ)) (e.liftN hs.length bs.length)
      = interp V (consList bs ρ) e := by
  rw [interp_liftN, ConLeche.Semantics.shiftE_consList_len, shiftE_consList]

namespace BlockData

variable (d : BlockData V)

/-- The member holes' values at `(ψ, ρp, X)`: the hole frame is the
parameter frame with these above it. -/
@[expose] noncomputable def holeList (ψ : Name → Nat) (ρp X : Nat → V) : List V :=
  (List.range d.k).map (d.toLfp.holeVal ψ ρp X)

theorem toLfp_frame (ψ : Name → Nat) (ρp X : Nat → V) :
    d.toLfp.frame ψ ρp X = consList (d.holeList ψ ρp X) ρp := rfl

variable {d}

theorem holeList_length {ψ : Name → Nat} {ρp X : Nat → V} : (d.holeList ψ ρp X).length = d.k := by
  simp [holeList]

/-- **A member's hole, read above a spine**: the bvar at the hole's
position is the member's hole value. -/
theorem interp_hole_bvar {ψ : Name → Nat} {ρp X : Nat → V} {t : Nat} (ht : t < d.k) (L : List V) :
    interp V (consList L (consList (d.holeList ψ ρp X) ρp)) (.bvar (L.length + (d.k - 1 - t)))
      = d.toLfp.holeVal ψ ρp X t := by
  rw [interp_bvar, show L.length + (d.k - 1 - t) = (d.k - 1 - t) + L.length by omega,
    consList_apply_add, consList_getD_of_lt _ _ _ (by rw [holeList_length]; omega),
    holeList_length, show d.k - 1 - (d.k - 1 - t) = t by omega]
  simp [holeList, List.getD_eq_getElem?_getD, ht]

/-- **The parameter variables above the holes** read the parameter frame's
own values. -/
theorem map_paramBvars_holes {ψ : Name → Nat} {ρp X : Nat → V} (L : List V) :
    (paramBvarsAt d.nP (d.nP + d.k + L.length)).map
        (interp V (consList L (consList (d.holeList ψ ρp X) ρp)))
      = frameIdx d.nP ρp := by
  unfold paramBvarsAt frameIdx
  rw [List.map_map]
  refine List.map_congr_left fun p hp => ?_
  have := List.mem_range.mp hp
  simp only [Function.comp_def, interp_bvar]
  rw [show d.nP + d.k + L.length - 1 - p = (d.nP - 1 - p + d.k) + L.length by omega,
    consList_apply_add,
    show d.nP - 1 - p + d.k = (d.nP - 1 - p) + (d.holeList ψ ρp X).length by
      rw [holeList_length],
    consList_apply_add]

end BlockData

/-- **A telescope lifted over the holes** reads, at the hole frame, as
the nested product over the telescope at the parameter frame. -/
theorem interp_liftTeleK_piTele {w : Nat} {B : List V → V} {R : AnnotTerm} (hs : List V)
    (ρ : Nat → V) :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) (bs acc : List V),
      (∀ dd ∈ tl, (dd.2.1 = 0 ↔ w = 0)) →
      (∀ ts, SpineFit (consList bs ρ) (tl.map (·.2.2)) ts →
        interp V (consList ts (consList bs (consList hs ρ))) R = B (acc ++ ts)) →
      interp V (consList bs (consList hs ρ)) (mkPisAV (BlockData.liftTeleK hs.length bs.length tl) R)
        = piTele w (teleOfFields (consList bs ρ) (tl.map (·.2.2))) B acc
  | [], bs, acc, _, hb => by
    have := hb [] trivial
    simp only [consList_nil, List.append_nil] at this
    simp only [BlockData.liftTeleK, mkPisAV]
    exact this
  | dd :: tl, bs, acc, hbits, hb => by
    simp only [BlockData.liftTeleK, mkPisAV, interp_pi]
    rw [interp_liftN_consList2]
    refine piR_zero_agree (hbits dd List.mem_cons_self) fun a ha => ?_
    have h := interp_liftTeleK_piTele (B := B) (R := R) hs ρ tl (bs ++ [a]) (acc ++ [a])
      (fun d' hd' => hbits d' (List.mem_cons_of_mem _ hd')) (fun ts hts => by
        have := hb (a :: ts) ⟨ha, by rw [consList_snoc']; exact hts⟩
        rw [consList_cons, consList_snoc'] at this
        rw [this, List.append_assoc, List.singleton_append])
    rw [List.length_append, List.length_singleton, ← consList_snoc', ← consList_snoc'] at h
    exact h

/-! ## The fields with holes read as the fixpoint route's entries -/

section Entries

variable {d : BlockData V} {ψ : Name → Nat} {ρp X : Nat → V}

/-- **A hole-free field** reads at the hole frame as at the parameter
frame. -/
theorem interp_absField_ord {c j i : Nat} (hr : ((d.rss c).getD j []).getD i false = false)
    {as : List V} (has : as.length = i) :
    interp V (consList as (d.toLfp.frame ψ ρp X)) (d.absField ψ c j i)
      = interp V (consList as ρp) (((d.Fss c ψ).getD j []).getD i default) := by
  unfold BlockData.absField
  rw [if_neg (by rw [hr]; exact Bool.false_ne_true), BlockData.toLfp_frame, ← has,
    ← (BlockData.holeList_length (d := d) (ψ := ψ) (ρp := ρp) (X := X))]
  exact interp_liftN_consList2 _ _ _ _

/-- **A field reading a member** reads at the hole frame of `X` as the
fixpoint route's slot at `X`: the hole applied to the parameters and the
index readings is `X`'s component at their tuple, under the telescope. -/
theorem interp_absField_rec (hs : Sat V (d.params ψ).reverse ρp)
    (hlenP : (d.params ψ).length = d.nP) {c j i : Nat}
    (hr : ((d.rss c).getD j []).getD i false = true) (ht : d.tgts c j i < d.k)
    (hbits : ∀ dd ∈ ((d.tlss c ψ).getD j []).getD i [], (dd.2.1 = 0 ↔ d.w ψ = 0))
    {as : List V} (has : as.length = i)
    (hSF : SlotFit (d.uM (d.tgts c j i) ψ) (d.w ψ) ρp (d.IdsM (d.tgts c j i) ψ)
      (((d.tlss c ψ).getD j []).getD i []) (((d.Eiss c ψ).getD j []).getD i []) as) :
    interp V (consList as (d.toLfp.frame ψ ρp X)) (d.absField ψ c j i)
      = d.slotAt ψ X c j i (consList as ρp) := by
  unfold BlockData.absField BlockData.slotAt slotSet
  rw [if_pos hr, BlockData.toLfp_frame]
  have hk : d.k = (d.holeList ψ ρp X).length := BlockData.holeList_length.symm
  rw [show BlockData.liftTeleK d.k i (((d.tlss c ψ).getD j []).getD i [])
      = BlockData.liftTeleK (d.holeList ψ ρp X).length as.length
          (((d.tlss c ψ).getD j []).getD i []) by rw [← hk, has]]
  refine interp_liftTeleK_piTele _ ρp _ as [] hbits fun ts hts => ?_
  have htsLen : ts.length = (((d.tlss c ψ).getD j []).getD i []).length := by
    rw [hts.length_eq, List.length_map]
  rw [← consList_append, interp_mkAppN, foldl_app_map, List.map_append, List.map_map,
    List.nil_append]
  have hL : (as ++ ts).length = i + (((d.tlss c ψ).getD j []).getD i []).length := by
    rw [List.length_append, has, htsLen]
  rw [show i + (((d.tlss c ψ).getD j []).getD i []).length + (d.k - 1 - d.tgts c j i)
      = (as ++ ts).length + (d.k - 1 - d.tgts c j i) by rw [hL],
    BlockData.interp_hole_bvar ht,
    show d.nP + d.k + i + (((d.tlss c ψ).getD j []).getD i []).length
      = d.nP + d.k + (as ++ ts).length by rw [hL]; omega,
    BlockData.map_paramBvars_holes]
  have heis : (((d.Eiss c ψ).getD j []).getD i []).map
        ((interp V (consList (as ++ ts) (consList (d.holeList ψ ρp X) ρp))) ∘
          (·.liftN d.k (i + (((d.tlss c ψ).getD j []).getD i []).length)))
      = (((d.Eiss c ψ).getD j []).getD i []).map (interp V (consList (as ++ ts) ρp)) := by
    refine List.map_congr_left fun E _ => ?_
    simp only [Function.comp_def]
    rw [hk, ← hL]
    exact interp_liftN_consList2 _ _ _ _
  rw [heis, ← hlenP]
  have hfit := (hSF.2.2 ts hts).2
  have := d.toLfp.holeVal_app (X := X) hs _ hfit
  simp only [consList_append] at this ⊢
  exact this

end Entries

/-! ## The fit relation IS the hole fit -/

/-- `FitsFrom` extended by one value at the next position. -/
theorem FitsFrom.snoc {rs : List Bool} {slot : Nat → (Nat → V) → V} {G : AnnotTerm} {b : V} :
    ∀ {s : Nat} {ρ : Nat → V} {L : List AnnotTerm} {as : List V},
      FitsFrom rs slot s ρ L as →
      b ∈ˢ (if rs.getD (s + L.length) false then slot (s + L.length) (consList as ρ)
        else interp V (consList as ρ) G) →
      FitsFrom rs slot s ρ (L ++ [G]) (as ++ [b])
  | _, _, [], [], _, hb => ⟨by simpa using hb, trivial⟩
  | _, _, [], _ :: _, h, _ => h.elim
  | _, _, _ :: _, [], h, _ => h.elim
  | s, ρ, F :: L, a :: as, h, hb => by
    refine ⟨h.1, FitsFrom.snoc h.2 ?_⟩
    rw [show s + 1 + L.length = s + (F :: L).length by simp; omega]
    simpa using hb

theorem take_succ_getD {α : Type} {Fs : List α} {i : Nat} (d : α) (hi : i < Fs.length) :
    Fs.take (i + 1) = Fs.take i ++ [Fs.getD i d] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  rfl

/-- **The fit along a list of readings at another frame** is the fixpoint
route's fit, when the readings agree with its entries at every prefix
the fit reaches. -/
theorem spineFit_map_iff_fitsFrom {rs : List Bool} {slot : Nat → (Nat → V) → V}
    {ρ σ : Nat → V} {Fs : List AnnotTerm} {G : Nat → AnnotTerm}
    (hent : ∀ l, l < Fs.length → ∀ as : List V, as.length = l →
      FitsFrom rs slot 0 ρ (Fs.take l) as →
      interp V (consList as σ) (G l)
        = (if rs.getD l false then slot l (consList as ρ)
            else interp V (consList as ρ) (Fs.getD l default))) :
    ∀ (bs as : List V) (i : Nat), as.length = i → FitsFrom rs slot 0 ρ (Fs.take i) as →
      (SpineFit (consList as σ) (((List.range Fs.length).map G).drop i) bs ↔
        FitsFrom rs slot i (consList as ρ) (Fs.drop i) bs)
  | [], as, i, _, _ => by
    by_cases hi : i < Fs.length
    · rw [List.drop_eq_getElem_cons (by simpa using hi), List.drop_eq_getElem_cons hi]
      exact ⟨fun h => h.elim, fun h => h.elim⟩
    · rw [List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by omega)]
      exact ⟨fun _ => trivial, fun _ => trivial⟩
  | b :: bs, as, i, has, hpre => by
    by_cases hi : i < Fs.length
    · rw [List.drop_eq_getElem_cons (by simpa using hi), List.drop_eq_getElem_cons hi]
      simp only [List.getElem_map, List.getElem_range]
      have hhead := hent i hi as has hpre
      have hFi : Fs[i] = Fs.getD i default := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
      rw [hFi]
      show (b ∈ˢ interp V (consList as σ) (G i) ∧ _) ↔
        (b ∈ˢ (if rs.getD i false then slot i (consList as ρ)
          else interp V (consList as ρ) (Fs.getD i default)) ∧ _)
      rw [hhead]
      have hpreOf : b ∈ˢ (if rs.getD i false then slot i (consList as ρ)
            else interp V (consList as ρ) (Fs.getD i default)) →
          FitsFrom rs slot 0 ρ (Fs.take (i + 1)) (as ++ [b]) := fun hb => by
        rw [take_succ_getD default hi]
        refine FitsFrom.snoc hpre ?_
        rw [List.length_take_of_le (by omega), Nat.zero_add]
        exact hb
      have hlen' : (as ++ [b]).length = i + 1 := by simp [has]
      constructor
      · rintro ⟨hb, hrest⟩
        refine ⟨hb, ?_⟩
        rw [consList_snoc'] at hrest ⊢
        exact (spineFit_map_iff_fitsFrom hent bs (as ++ [b]) (i + 1) hlen' (hpreOf hb)).mp hrest
      · rintro ⟨hb, hrest⟩
        refine ⟨hb, ?_⟩
        rw [consList_snoc'] at hrest ⊢
        exact (spineFit_map_iff_fitsFrom hent bs (as ++ [b]) (i + 1) hlen' (hpreOf hb)).mpr hrest
    · rw [List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by omega)]
      exact ⟨fun h => h.elim, fun h => h.elim⟩

/-! ## `ReadsHoles` and the clause -/

section Clause

variable {env : Env} {m : EnvModel V env} {names : List Name} {d : BlockData V} {lps : List Name}

/-- **What the clause's production reads off the stages** beside the
representation: every constructor's reading facts, the recursive
fields' targets among the members, and the lengths of the parameter
telescope and of the result index readings. -/
structure BlockHoleFacts (m : EnvModel V env) (d : BlockData V) (lps : List Name) : Prop where
  facts : ∀ c, c < d.N → ∀ j cA, (d.ctorsM c)[j]? = some cA → BlockCtorFacts m d lps c j cA
  tgt : ∀ c, c < d.N → ∀ j cA, (d.ctorsM c)[j]? = some cA → ∀ l, l < cA.2 → d.tgts c j l < d.k
  lenP : ∀ ψ, (d.params ψ).length = d.nP
  lenE : ∀ ψ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
    ((d.Ess c ψ).getD j []).length = (d.IdsM c ψ).length

/-- A constructor's field readings number its fields. -/
theorem BlockCtorFacts.nF {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hcf : BlockCtorFacts m d lps c j cA) (ψ : Name → Nat) :
    ((d.Fss c ψ).getD j []).length = cA.2 := by
  obtain ⟨-, -, hD⟩ := hcf
  have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  rw [hFssD, List.length_map, List.length_drop, hD.len ψ]
  omega

/-- **The fixpoint route's fit IS the hole fit** (lane HOLE2): at every
parameter frame of the domain, every tuple of the space and every index
tuple, a spine fits a constructor's `ChainFit` exactly when it fits the
constructor's fields with holes at the hole frame, its result index
readings the tuple's components. -/
theorem blockReadsHoles (hM : BlockModelAt m names d) (hH : BlockHoleFacts m d lps) :
    d.toLfp.ReadsHoles := by
  intro ψ ρp hs X hX c hc t ht j fs
  show (j < (d.ctorsM c).length ∧ d.ChainFit ψ ρp X t c j fs) ↔
    (j < (d.ctorsM c).length ∧ SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs ∧
      ∀ l, l < (d.IdsM c ψ).length → ∃ e, (d.absE ψ c j)[l]? = some e ∧
        interp V (consList fs (d.toLfp.frame ψ ρp X)) e = projS l t)
  by_cases hj : j < (d.ctorsM c).length
  case neg => exact ⟨fun h => absurd h.1 hj, fun h => absurd h.1 hj⟩
  have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
  have hcf := hH.facts c hc j _ hcj
  have hnF := hcf.nF hcj ψ
  -- the entries agree at every prefix the fit reaches
  have hent : ∀ l, l < ((d.Fss c ψ).getD j []).length → ∀ as : List V, as.length = l →
      FitsFrom ((d.rss c).getD j []) (d.slotAt ψ X c j) 0 ρp
        (((d.Fss c ψ).getD j []).take l) as →
      interp V (consList as (d.toLfp.frame ψ ρp X)) (d.absField ψ c j l)
        = (if ((d.rss c).getD j []).getD l false then d.slotAt ψ X c j l (consList as ρp)
            else interp V (consList as ρp) (((d.Fss c ψ).getD j []).getD l default)) := by
    intro l hl as has hpre
    by_cases hr : ((d.rss c).getD j []).getD l false = true
    · rw [if_pos hr]
      obtain ⟨-, -, hD⟩ := hcf
      have hTl : (d.tlss c ψ).getD j [] = d.tssF c j ψ := tlssOfR_fixCtorDataList_getD hcj
      refine interp_absField_rec hs (hH.lenP ψ) hr (hH.tgt c hc j _ hcj l (by omega))
        (fun dd hdd => ?_) has (hM.idxFit ψ ρp hs X hX c hc t ht j hj l hl hr as hpre)
      rw [hTl] at hdd
      exact (hD.tssBits ψ l dd hdd).trans Iff.rfl
    · have hr' : ((d.rss c).getD j []).getD l false = false := by simpa using hr
      rw [if_neg hr]
      exact interp_absField_ord hr' has
  have hfit : SpineFit (d.toLfp.frame ψ ρp X) (d.absF ψ c j) fs ↔
      FitsFrom ((d.rss c).getD j []) (d.slotAt ψ X c j) 0 ρp ((d.Fss c ψ).getD j []) fs := by
    have := spineFit_map_iff_fitsFrom hent fs [] 0 rfl trivial
    simpa [BlockData.absF] using this
  -- the result index readings, lifted over the holes
  have hres : ∀ fs : List V, fs.length = ((d.Fss c ψ).getD j []).length →
      ((∀ l, l < (d.IdsM c ψ).length →
          interp V (consList fs ρp) (((d.Ess c ψ).getD j []).getD l default) = projS l t) ↔
        (∀ l, l < (d.IdsM c ψ).length → ∃ e, (d.absE ψ c j)[l]? = some e ∧
          interp V (consList fs (d.toLfp.frame ψ ρp X)) e = projS l t)) := by
    intro fs hfs
    have hlenE := hH.lenE ψ c hc j hj
    have hget : ∀ l, l < (d.IdsM c ψ).length → (d.absE ψ c j)[l]?
        = some ((((d.Ess c ψ).getD j []).getD l default).liftN d.k
            ((d.Fss c ψ).getD j []).length) := by
      intro l hl
      have hlE : l < ((d.Ess c ψ).getD j []).length := by rw [hlenE]; exact hl
      unfold BlockData.absE
      generalize (d.Ess c ψ).getD j [] = E at hlE ⊢
      have hgd : E.getD l default = E[l] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlE]; rfl
      rw [List.getElem?_map, List.getElem?_eq_getElem hlE, Option.map_some, hgd]
    have hread : ∀ E : AnnotTerm,
        interp V (consList fs (d.toLfp.frame ψ ρp X)) (E.liftN d.k ((d.Fss c ψ).getD j []).length)
          = interp V (consList fs ρp) E := by
      intro E
      rw [BlockData.toLfp_frame, ← hfs,
        ← (BlockData.holeList_length (d := d) (ψ := ψ) (ρp := ρp) (X := X))]
      exact interp_liftN_consList2 _ _ _ _
    constructor
    · intro h l hl
      exact ⟨_, hget l hl, by rw [hread]; exact h l hl⟩
    · intro h l hl
      obtain ⟨e, he, heq⟩ := h l hl
      rw [hget l hl] at he
      obtain rfl := Option.some.inj he
      rw [hread] at heq
      exact heq
  constructor
  · rintro ⟨-, hF, hE⟩
    have hlen : fs.length = ((d.Fss c ψ).getD j []).length := FitsFrom.length_eq hF
    exact ⟨hj, hfit.mpr hF, (hres fs hlen).mp hE⟩
  · rintro ⟨-, hF, hE⟩
    have hF' := hfit.mp hF
    have hlen : fs.length = ((d.Fss c ψ).getD j []).length := FitsFrom.length_eq hF'
    exact ⟨hj, hF', (hres fs hlen).mpr hE⟩

/-- **The representation's lfp clause, in hole form** — `functor`,
`fibre`, `leaf`, `mkZero`, `mkInj` verbatim; `holes` is
`blockReadsHoles`; `ctor` is the representation's `ctor` at the domains'
fit the hole fit at the carrier gives (`blockSlot_agree`). -/
theorem BlockModelAt.toLfp (hM : BlockModelAt m names d) (hH : BlockHoleFacts m d lps) :
    LfpClause m.acval d.toLfp where
  kN := Nat.le_add_right _ _
  functor := hM.functor
  fibre := fun ψ ρp hsat X hX c hc t ht x => by
    show x ∈ˢ app (d.Φ ψ ρp X c) t ↔
      ∃ j fs, (j < (d.ctorsM c).length ∧ d.ChainFit ψ ρp X t c j fs) ∧ x = d.inj ψ c j fs
    rw [hM.fibre ψ ρp hsat X hX c hc t ht x]
    constructor
    · rintro ⟨j, fs, hj, hfit, rfl⟩; exact ⟨j, fs, ⟨hj, hfit⟩, rfl⟩
    · rintro ⟨j, fs, ⟨hj, hfit⟩, rfl⟩; exact ⟨j, fs, hj, hfit, rfl⟩
  leaf := hM.leaf
  holes := blockReadsHoles hM hH
  mkZero := hM.mkZero
  mkInj := fun ψ hw c hc j fs j' fs' hj hj' hl hl' h =>
    hM.mkInj ψ hw c hc j fs j' fs' hj hj'
      (by rw [hl]; simp [BlockData.toLfp, BlockData.absF])
      (by rw [hl']; simp [BlockData.toLfp, BlockData.absF]) h
  ctor := fun c hc j ψ ρ as fs t hsa ht hf => by
    have hsat := d.satOfSpine hsa
    have hX : InTupleSpace (d.w ψ) d.N (d.idx ψ (consList as ρ))
        (lfpTuple (d.w ψ) d.N (d.idx ψ (consList as ρ)) (d.Φ ψ (consList as ρ))) :=
      lfpTuple_mem _ _ _ _
    obtain ⟨hj, hcf, -⟩ := (blockReadsHoles hM hH ψ (consList as ρ) hsat _ hX c hc t ht j fs).mpr hf
    have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
    have hasLen : as.length = d.nP := by rw [hsa.length_eq]; exact hH.lenP ψ
    have hsp : SpineFit (consList as ρ) ((d.Fss c ψ).getD j []) fs :=
      spineFit_of_fitsFrom (fun l hl bs hb hr => by
        rw [Nat.zero_add] at hr ⊢
        exact blockSlot_agree hM hcj (hH.facts c hc j _ hcj) hasLen hsa (hH.tgt c hc j _ hcj)
          hc hj ht hX l hl bs hb hr) hcf
    show (as ++ fs).foldl app (interp V ρ (m.acval ((d.ctorsM c).getD j default).1.name ψ))
      = d.inj ψ c j fs
    rw [List.getD_eq_getElem?_getD, hcj]
    exact hM.ctor c hc j _ hcj ψ ρ as fs hsa hsp

end Clause

end ConLeche.Model
