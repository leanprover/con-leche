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

/-- **A hole-free field** reads below ANY `k` hole values as at the
parameter frame. -/
theorem interp_absField_ord_at {c j i : Nat} (hr : ((d.rss c).getD j []).getD i false = false)
    {hs : List V} (hhs : hs.length = d.k) {as : List V} (has : as.length = i) (ρ : Nat → V) :
    interp V (consList as (consList hs ρ)) (d.absField ψ c j i)
      = interp V (consList as ρ) (((d.Fss c ψ).getD j []).getD i default) := by
  unfold BlockData.absField
  rw [if_neg (by rw [hr]; exact Bool.false_ne_true), ← has, ← hhs]
  exact interp_liftN_consList2 _ _ _ _

end Entries

/-! ## The fit relation IS the hole fit -/

theorem take_succ_getD {α : Type} {Fs : List α} {i : Nat} (d : α) (hi : i < Fs.length) :
    Fs.take (i + 1) = Fs.take i ++ [Fs.getD i d] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi]
  rfl

/-! ## `ReadsHoles` and the clause -/

section Clause

variable {env : Env} {m : EnvModel V env} {names : List Name} {d : BlockData V} {lps : List Name}

/-- **What the clause's production reads off the stages** beside the
representation: every constructor's reading facts, the recursive
fields' targets among the members, and the lengths of the parameter
telescope and of the result index readings. -/
structure BlockHoleFacts (m : EnvModel V env) (d : BlockData V) (lps : List Name) : Prop where
  facts : ∀ c, c < d.N → ∀ j cA, (d.ctorsM c)[j]? = some cA → BlockCtorRead m d lps c j cA
  tgt : ∀ c, c < d.N → ∀ j cA, (d.ctorsM c)[j]? = some cA → ∀ l, l < cA.2 → d.tgts c j l < d.k
  lenP : ∀ ψ, (d.params ψ).length = d.nP
  /-- every member's own parameter telescope: `nP` long, satisfied where
  the block's is -/
  parsLen : ∀ ψ m, m < d.k → (d.toLfp.pars m ψ).length = d.nP
  parsSat : ∀ ψ m, m < d.k → ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ →
    Sat V (d.toLfp.pars m ψ).reverse ρ
  parsSatInv : ∀ ψ m, m < d.k → ∀ ρ : Nat → V, Sat V (d.toLfp.pars m ψ).reverse ρ →
    Sat V (d.params ψ).reverse ρ
  lenE : ∀ ψ c, c < d.N → ∀ j, j < (d.ctorsM c).length →
    ((d.Ess c ψ).getD j []).length = (d.IdsM c ψ).length

/-- A constructor's field readings number its fields. -/
theorem BlockCtorRead.nF {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hD : BlockCtorRead m d lps c j cA) (ψ : Name → Nat) :
    ((d.Fss c ψ).getD j []).length = cA.2 := by
  unfold BlockCtorRead at hD
  have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  rw [hFssD, List.length_map, List.length_drop, hD.len ψ]
  omega

/-! ## The holes occur only applied to the parameters (lane CONTSEM, M3) -/

/-- A Π-telescope whose `l`-th domain is `HoleApp` at `lo + l` and whose
body is at `lo + |ab|` is `HoleApp` at `lo`. -/
theorem holeApp_mkPisAV {k nP : Nat} :
    ∀ (ab : List (Nat × Nat × AnnotTerm)) {lo : Nat} {b : AnnotTerm},
      (∀ l dd, ab[l]? = some dd → HoleApp k nP (lo + l) dd.2.2) →
      HoleApp k nP (lo + ab.length) b → HoleApp k nP lo (mkPisAV ab b)
  | [], lo, b, _, hb => by simp only [List.length_nil, Nat.add_zero] at hb; exact hb
  | dd :: ab, lo, b, hd, hb => by
    refine .pi (by simpa using hd 0 dd rfl) (holeApp_mkPisAV ab (fun l d' hl => ?_) ?_)
    · have := hd (l + 1) d' (by simpa using hl)
      rwa [show lo + (l + 1) = lo + 1 + l by omega] at this
    · rwa [show lo + 1 + ab.length = lo + (dd :: ab).length by simp; omega]

theorem liftTeleK_getElem? (n : Nat) :
    ∀ (i : Nat) (tl : List (Nat × Nat × AnnotTerm)) (l : Nat) (dd : Nat × Nat × AnnotTerm),
      (BlockData.liftTeleK n i tl)[l]? = some dd →
      ∃ e : AnnotTerm, dd.2.2 = e.liftN n (i + l)
  | _, [], _, _, h => nomatch h
  | i, d0 :: tl, 0, dd, h => by
    simp only [BlockData.liftTeleK, List.getElem?_cons_zero, Option.some.injEq] at h
    subst h; exact ⟨d0.2.2, by simp⟩
  | i, _ :: tl, l + 1, dd, h => by
    simp only [BlockData.liftTeleK, List.getElem?_cons_succ] at h
    obtain ⟨e, he⟩ := liftTeleK_getElem? n (i + 1) tl l dd h
    exact ⟨e, by rw [he, show i + 1 + l = i + (l + 1) by omega]⟩

theorem liftTeleK_length' (n : Nat) :
    ∀ (i : Nat) (tl : List (Nat × Nat × AnnotTerm)), (BlockData.liftTeleK n i tl).length = tl.length
  | _, [] => rfl
  | i, _ :: tl => by
    show (_ :: BlockData.liftTeleK n (i + 1) tl).length = _
    simp [liftTeleK_length' n (i + 1) tl]

/-- **A uniform block's fields with holes apply each hole to the
parameters** (`absField`'s recursive arm is the hole applied to
`paramBvarsAt` and the lifted index readings; every other reading is
lifted over the holes). -/
theorem absField_holeApp (hH : BlockHoleFacts m d lps) {ψ : Name → Nat} {c : Nat} (hc : c < d.N)
    {j : Nat} (hj : j < (d.ctorsM c).length) (i : Nat) (hi : i < ((d.Fss c ψ).getD j []).length) :
    HoleApp d.k (d.params ψ).length i (d.absField ψ c j i) := by
  unfold BlockData.absField
  split
  · rename_i hr
    have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
    have hnF := (hH.facts c hc j _ hcj).nF hcj ψ
    have htg := hH.tgt c hc j _ hcj i (by omega)
    generalize (((d.tlss c ψ).getD j []).getD i []) = tl
    refine holeApp_mkPisAV _ (fun l dd hl => ?_) ?_
    · obtain ⟨e, he⟩ := liftTeleK_getElem? d.k i tl l dd hl
      rw [he]; exact holeApp_liftN _ _ e _
    · rw [liftTeleK_length', hH.lenP ψ]
      have hp : paramBvarsAt d.nP (d.nP + d.k + i + tl.length) = holeParams d.k d.nP (i + tl.length) := by
        unfold paramBvarsAt holeParams
        refine List.map_congr_left fun p _ => ?_
        congr 1; omega
      rw [hp]
      exact .hole (by omega) (by omega) fun r hr => by
        obtain ⟨E, -, rfl⟩ := List.mem_map.mp hr
        exact holeApp_liftN _ _ E _
  · exact holeApp_liftN _ _ _ _

theorem blockHolesApplied (hH : BlockHoleFacts m d lps) (ψ : Name → Nat) {c : Nat} (hc : c < d.N)
    {j : Nat} (hj : j < (d.ctorsM c).length) : d.toLfp.HolesApplied ψ c j := by
  refine ⟨fun l F hl => ?_, fun e he => ?_⟩
  · show HoleApp d.k (d.params ψ).length l F
    have hl' : l < ((d.Fss c ψ).getD j []).length := by
      have := (List.getElem?_eq_some_iff.mp hl).1
      simpa [BlockData.toLfp, BlockData.absF] using this
    have hF : F = d.absField ψ c j l := by
      have : (d.absF ψ c j)[l]? = some (d.absField ψ c j l) := by
        unfold BlockData.absF
        rw [List.getElem?_map, List.getElem?_range hl']
        rfl
      exact Option.some.inj (hl.symm.trans this)
    rw [hF]; exact absField_holeApp hH hc hj l hl'
  · show HoleApp d.k (d.params ψ).length (d.absF ψ c j).length e
    obtain ⟨E, -, rfl⟩ := List.mem_map.mp he
    rw [show (d.absF ψ c j).length = ((d.Fss c ψ).getD j []).length by simp [BlockData.absF]]
    exact holeApp_liftN _ _ E _

/-- **The representation's lfp clause, in hole form** — `functor`,
`fibre`, `leaf`, `mkZero`, `mkInj` verbatim; `ctor` is the
representation's `ctor` at the stored fit the hole fit at the carrier is
(`BlockModelAt.carrier`). -/
theorem BlockModelAt.toLfp (hM : BlockModelAt m names d) (hH : BlockHoleFacts m d lps) :
    LfpClause m.acval d.toLfp where
  kN := Nat.le_add_right _ _
  functor := hM.functor
  fibre := hM.fibre
  fitsMono := hM.fitsMono
  leaf := hM.leaf
  mkZero := hM.mkZero
  mkInj := fun ψ hw c hc j fs j' fs' hj hj' hl hl' h =>
    hM.mkInj ψ hw c hc j fs j' fs' hj hj'
      (by rw [hl]; simp [BlockData.toLfp, BlockData.absF])
      (by rw [hl']; simp [BlockData.toLfp, BlockData.absF]) h
  ctor := fun c hc j ψ ρ as fs t hsa ht hf => by
    have hsat := d.satOfSpine hsa
    obtain ⟨hj, hsp, -⟩ := (hM.carrier ψ (consList as ρ) hsat c hc t ht j fs).mp hf
    have hcj : (d.ctorsM c)[j]? = some (d.ctorsM c)[j] := List.getElem?_eq_getElem hj
    show (as ++ fs).foldl app (interp V ρ (m.acval ((d.ctorsM c).getD j default).1.name ψ))
      = d.inj ψ c j fs
    rw [List.getD_eq_getElem?_getD, hcj]
    exact hM.ctor c hc j _ hcj ψ ρ as fs hsa hsp
  parsLen := fun mm hmm ψ => (hH.parsLen ψ mm hmm).trans (hH.lenP ψ).symm
  parsSat := fun mm hmm ψ ρ hs => hH.parsSat ψ mm hmm ρ hs
  parsSatInv := fun mm hmm ψ ρ hs => hH.parsSatInv ψ mm hmm ρ hs
  holeApp := fun ψ c hc j hj => blockHolesApplied hH ψ hc hj

end Clause

end ConLeche.Model
