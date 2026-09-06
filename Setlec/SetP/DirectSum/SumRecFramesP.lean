import Setlec.SetP.DirectSum.SumRecDataP
import Setlec.SetP.DirectSum.SumStageCtorP
import Setlec.SetP.Direct.DirectRecFramesP

/-!
# The sum recursor's frames (task #175 sum-types, indexed)

`sumRecFrames`: at a parameter frame, the generated sum recursor's
entries read to the recursor leaf's premise `RecBaseS` — the motive
entry to the nested product over the former's index telescope into
the family at each index tuple, minor entry `j` (at the frame under
the motive and the earlier minors) to constructor `j`'s minor space
`minorSpI` (its conclusion at the constructor's own index values),
the index entries to the former's index telescope, the major entry
to the family at the frame's index tuple — and the K-frame's two
hypothesis records (`RecHypS`, `SqHypS`).  The walk: down the minor
chain (`sumMinorsTail`), then down the index chain (`sumIdxTail`),
the frame kept as an explicit `consList`.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-! ## The chains of a data list -/

/-- The field chains of the constructor data (at the parameter
frame). -/
def fssOf (nP : Nat) (cds : List CtorDatum) : List (List AVExpr) :=
  cds.map fun cd => (cd.2.2.1.drop nP).map (·.2.2)

/-- The index readings of the constructor data. -/
def essOf (cds : List CtorDatum) : List (List AVExpr) :=
  cds.map fun cd => cd.2.2.2

/-- The sources of the first `n` constructors. -/
def srcssOf (srcsF : Nat → List (Option Nat)) (n : Nat) : List (List (Option Nat)) :=
  (List.range n).map srcsF

theorem fssOf_length (nP : Nat) (cds : List CtorDatum) : (fssOf nP cds).length = cds.length := by
  simp [fssOf]

theorem fssOf_getElem? (nP : Nat) (cds : List CtorDatum) (j : Nat) :
    (fssOf nP cds)[j]? = cds[j]?.map fun cd => (cd.2.2.1.drop nP).map (·.2.2) := by
  simp [fssOf]

theorem essOf_length (cds : List CtorDatum) : (essOf cds).length = cds.length := by
  simp [essOf]

theorem essOf_getElem? (cds : List CtorDatum) (j : Nat) :
    (essOf cds)[j]? = cds[j]?.map fun cd => cd.2.2.2 := by
  simp [essOf]

theorem srcssOf_getD (srcsF : Nat → List (Option Nat)) {n j : Nat} (hj : j < n) :
    (srcssOf srcsF n).getD j [] = srcsF j := by
  simp [srcssOf, List.getD_eq_getElem?_getD, hj]

theorem sumMinorsData_getElem? {m : EnvS2Core V env} {ψ : Name → Nat} {nP b : Nat} :
    ∀ (cds : List CtorDatum) (o j : Nat),
      (sumMinorsData m ψ nP b cds o)[j]?
        = cds[j]?.map fun cd => (0, b, minorAVAt m cd.1 ψ nP cd.2.1 b (o + j) cd.2.2.1 cd.2.2.2)
  | [], _, _ => by simp [sumMinorsData]
  | (C, nF, ds, Es) :: cs, o, 0 => by simp [sumMinorsData]
  | (C, nF, ds, Es) :: cs, o, j + 1 => by
    simp only [sumMinorsData, List.getElem?_cons_succ]
    rw [sumMinorsData_getElem? cs (o + 1) j, show o + 1 + j = o + (j + 1) from by omega]

/-! ## The recursor data's entries -/

section Entries

variable {pds dms dis : List (Nat × Nat × AVExpr)} {dM dt : Nat × Nat × AVExpr}

theorem rds_getElem?_M {i : Nat} (hi : i = pds.length) :
    (pds ++ [dM] ++ dms ++ dis ++ [dt])[i]? = some dM := by
  subst hi
  rw [List.getElem?_append_left (by simp), List.getElem?_append_left (by simp),
    List.getElem?_append_left (by simp),
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

theorem rds_getElem?_minor {i j : Nat} (hj : j < dms.length) (hi : i = pds.length + 1 + j) :
    (pds ++ [dM] ++ dms ++ dis ++ [dt])[i]? = dms[j]? := by
  subst hi
  rw [List.getElem?_append_left (by simp <;> omega), List.getElem?_append_left (by simp <;> omega),
    List.getElem?_append_right (by simp <;> omega)]
  simp

theorem rds_getElem?_idx {i l : Nat} (hl : l < dis.length)
    (hi : i = pds.length + 1 + dms.length + l) :
    (pds ++ [dM] ++ dms ++ dis ++ [dt])[i]? = dis[l]? := by
  subst hi
  rw [List.getElem?_append_left (by simp <;> omega),
    List.getElem?_append_right (by simp <;> omega)]
  simp only [List.length_append, List.length_singleton]
  congr 1
  omega

theorem rds_getElem?_t {i : Nat} (hi : i = pds.length + 1 + dms.length + dis.length) :
    (pds ++ [dM] ++ dms ++ dis ++ [dt])[i]? = some dt := by
  subst hi
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_append, List.length_singleton]
  rw [show pds.length + 1 + dms.length + dis.length - (pds.length + 1 + dms.length + dis.length) = 0
    from by omega]
  rfl

theorem rds_length :
    (pds ++ [dM] ++ dms ++ dis ++ [dt]).length = pds.length + dms.length + dis.length + 2 := by
  simp; omega

/-- The reversed context below the motive is the parameters'. -/
theorem rds_drop_params :
    (((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse).drop (dms.length + dis.length + 2)
      = (pds.map (·.2.2)).reverse := by
  have h : ((pds ++ [dM] ++ dms ++ dis ++ [dt]).map (·.2.2)).reverse
      = ([dt.2.2] ++ (dis.map (·.2.2)).reverse ++ (dms.map (·.2.2)).reverse ++ [dM.2.2]) ++
        (pds.map (·.2.2)).reverse := by
    simp [List.reverse_append, List.map_append, List.append_assoc]
  rw [h, List.drop_left' (by simp; omega)]

end Entries

/-! ## The nested product over a telescope, read -/

/-- **A Π-tower over nonzero-bit domains is the nested product** over
the domains' telescope, the body at the accumulated tuple. -/
theorem interp_mkPisAV_piTele {v : Nat} {B : List V → V} {R : AVExpr} :
    ∀ {gds : List (Nat × Nat × AVExpr)} {σ : Nat → V} {acc : List V},
      (∀ d ∈ gds, (d.2.1 = 0 ↔ v = 0)) →
      (∀ as : List V, SpineFit σ (gds.map (·.2.2)) as → interp2 V (consList as σ) R = B (acc ++ as)) →
      interp2 V σ (mkPisAV gds R) = piTele v (teleOfFields σ (gds.map (·.2.2))) B acc
  | [], σ, acc, _, hbase => by
    have := hbase [] trivial
    simp only [consList, List.append_nil] at this
    simp only [mkPisAV]
    exact this
  | d :: gds, σ, acc, hbits, hbase => by
    simp only [mkPisAV, interp2_pi]
    rw [piR_congr_bit (v := d.2.1) (v' := v) (hbits d List.mem_cons_self)]
    apply piR_congr
    intro a ha
    refine interp_mkPisAV_piTele (fun d' hd' => hbits d' (List.mem_cons_of_mem _ hd')) ?_
    intro as hsp
    have := hbase (a :: as) ⟨ha, hsp⟩
    rw [consList_cons] at this
    rw [this, List.append_assoc, List.singleton_append]

/-! ## The minor space, read -/

/-- **The minor space with an explicit conclusion is the interpreted
Π-tower** over field domains agreeing with the chain's. -/
theorem interp_minorSpI_of_tele {ℓ : Nat} {c : List V → V} :
    ∀ {Fs : List AVExpr} {gds : List (Nat × Nat × AVExpr)} {Rm : AVExpr}
      {σ ρf : Nat → V} {acc : List V},
      gds.length = Fs.length →
      (∀ d ∈ gds, (ℓ = 0 ↔ d.2.1 = 0)) →
      (∀ (j : Nat) (as : List V), j < Fs.length → SpineFit ρf (Fs.take j) as →
        interp2 V (consList as σ) ((gds.getD j default).2.2)
          = interp2 V (consList as ρf) (Fs.getD j default)) →
      (∀ as : List V, SpineFit ρf Fs as →
        interp2 V (consList as σ) Rm = c (acc ++ as)) →
      interp2 V σ (mkPisAV gds Rm) = minorSpI ℓ c Fs ρf acc
  | [], [], Rm, σ, ρf, acc, _, _, _, hbase => by
    have := hbase [] trivial
    simp only [consList, List.append_nil] at this
    simpa [mkPisAV, minorSpI] using this
  | [], _ :: _, _, _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, _, _, hlen, _, _, _ => by simp at hlen
  | F :: Fs, d :: gds, Rm, σ, ρf, acc, hlen, hbits, hdom, hbase => by
    simp only [mkPisAV, interp2_pi, minorSpI]
    have hd0 : interp2 V σ d.2.2 = interp2 V ρf F := by
      have := hdom 0 [] (by simp) trivial
      simpa [consList] using this
    rw [hd0, piR_congr_bit (v := d.2.1) (v' := ℓ) (hbits d List.mem_cons_self).symm]
    apply piR_congr
    intro a ha
    refine interp_minorSpI_of_tele (by simpa using hlen)
      (fun d' hd' => hbits d' (List.mem_cons_of_mem _ hd')) ?_ ?_
    · intro j as hj hsp
      have := hdom (j + 1) (a :: as) (by simpa using hj)
        (by simp only [List.take_succ_cons, SpineFit]; exact ⟨ha, hsp⟩)
      simpa [consList_cons] using this
    · intro as hsp
      have := hbase (a :: as) ⟨ha, hsp⟩
      rw [consList_cons] at this
      rw [this, List.append_cons]

/-! ## The K-frame -/

section KFrame

variable {ρp : Nat → V} {M : V} {ms is : List V} {n nIdx : Nat}

omit [SetTheory V] in
theorem kframe_apply_add (his : is.length = nIdx) (hms : ms.length = n) (i : Nat) :
    consList is (consList ms (cons M ρp)) (i + (nIdx + n + 1)) = ρp i := by
  rw [show i + (nIdx + n + 1) = (i + 1 + n) + is.length from by omega, consList_apply_add,
    show i + 1 + n = (i + 1) + ms.length from by omega, consList_apply_add]
  rfl

omit [SetTheory V] in
theorem kframe_frP (his : is.length = nIdx) (hms : ms.length = n) :
    frP n nIdx (consList is (consList ms (cons M ρp))) = ρp := by
  unfold frP
  rw [shiftE_zero]
  funext i
  exact kframe_apply_add his hms i

omit [SetTheory V] in
theorem kframe_frM (his : is.length = nIdx) (hms : ms.length = n) :
    frM n nIdx (consList is (consList ms (cons M ρp))) = M := by
  unfold frM
  rw [show nIdx + n = n + is.length from by omega, consList_apply_add,
    show n = 0 + ms.length from by omega, consList_apply_add]
  rfl

theorem kframe_frMs (his : is.length = nIdx) (hms : ms.length = n) {j : Nat} (hj : j < n) :
    frMs n nIdx (consList is (consList ms (cons M ρp))) j = ms.getD j pt := by
  unfold frMs
  rw [show nIdx + n - 1 - j = (n - 1 - j) + is.length from by omega, consList_apply_add,
    consList_apply_lt _ _ _ (by omega), hms, show n - 1 - (n - 1 - j) = j from by omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some,
    Option.getD_some]

omit [SetTheory V] in
theorem kframe_frameIdx (his : is.length = nIdx) :
    frameIdx nIdx (consList is (consList ms (cons M ρp))) = is :=
  frameIdx_consList his _

end KFrame

/-! ## The restricted chains at two frames -/

/-- The restricted tower depends on the frame only through the
shifted frame and the index tuple. -/
theorem towerSet_rChain_congr {w d d' nIdx : Nat} {Fs Es : List AVExpr} {σ σ' : Nat → V}
    (hEs : Es.length = nIdx) (hsh : shiftE d 0 σ = shiftE d' 0 σ')
    (hidx : frameIdx nIdx σ = frameIdx nIdx σ') :
    towerSet w (teleOfFields σ (rChain d nIdx Fs Es))
      = towerSet w (teleOfFields σ' (rChain d' nIdx Fs Es)) := by
  unfold rChain
  apply SetTheory.ext
  intro y
  by_cases hw : w = 0
  · subst hw
    constructor
    · intro hy
      obtain ⟨rfl, bs, hsp, hall⟩ := restricted_member_zero hy
      have hsp' : SpineFit (shiftE d 0 σ) Fs bs := (spineFit_liftFields d).mp hsp
      rw [EqAll_idxEqsAt hEs hsp'.length_eq, hsh, hidx] at hall
      have := restricted_member_intro (w := 0) (Fs := liftFields d' 0 Fs)
        ((spineFit_liftFields d').mpr (hsh ▸ hsp'))
        ((EqAll_idxEqsAt (d := d') hEs hsp'.length_eq).mpr hall)
      rw [if_pos rfl] at this
      exact this
    · intro hy
      obtain ⟨rfl, bs, hsp, hall⟩ := restricted_member_zero hy
      have hsp' : SpineFit (shiftE d' 0 σ') Fs bs := (spineFit_liftFields d').mp hsp
      rw [EqAll_idxEqsAt hEs hsp'.length_eq, ← hsh, ← hidx] at hall
      have := restricted_member_intro (w := 0) (Fs := liftFields d 0 Fs)
        ((spineFit_liftFields d).mpr (hsh.symm ▸ hsp'))
        ((EqAll_idxEqsAt (d := d) hEs hsp'.length_eq).mpr hall)
      rw [if_pos rfl] at this
      exact this
  · constructor
    · intro hy
      obtain ⟨hsp, -, hall, heta⟩ := restricted_member_elim hw hy
      rw [liftFields_length] at hsp hall heta
      have hsp' : SpineFit (shiftE d 0 σ) Fs (projList Fs.length y) := (spineFit_liftFields d).mp hsp
      rw [EqAll_idxEqsAt hEs hsp'.length_eq, hsh, hidx] at hall
      have := restricted_member_intro (w := w) (Fs := liftFields d' 0 Fs)
        ((spineFit_liftFields d').mpr (hsh ▸ hsp'))
        ((EqAll_idxEqsAt (d := d') hEs hsp'.length_eq).mpr hall)
      rw [if_neg hw] at this
      rw [heta]
      exact this
    · intro hy
      obtain ⟨hsp, -, hall, heta⟩ := restricted_member_elim hw hy
      rw [liftFields_length] at hsp hall heta
      have hsp' : SpineFit (shiftE d' 0 σ') Fs (projList Fs.length y) :=
        (spineFit_liftFields d').mp hsp
      rw [EqAll_idxEqsAt hEs hsp'.length_eq, ← hsh, ← hidx] at hall
      have := restricted_member_intro (w := w) (Fs := liftFields d 0 Fs)
        ((spineFit_liftFields d).mpr (hsh.symm ▸ hsp'))
        ((EqAll_idxEqsAt (d := d) hEs hsp'.length_eq).mpr hall)
      rw [if_neg hw] at this
      rw [heta]
      exact this

/-- The sum fibre over the restricted chains depends on the frame
only through the shifted frame and the index tuple. -/
theorem sumFibre_rChains_congr {w d d' nIdx : Nat} {Fss Ess : List (List AVExpr)} {σ σ' : Nat → V}
    (hEs : ∀ j, j < Fss.length → (Ess.getD j []).length = nIdx) (hlenE : Ess.length = Fss.length)
    (hsh : shiftE d 0 σ = shiftE d' 0 σ') (hidx : frameIdx nIdx σ = frameIdx nIdx σ') :
    sumFibre w σ (rChains d nIdx Fss Ess) = sumFibre w σ' (rChains d' nIdx Fss Ess) := by
  funext i
  rcases Nat.lt_or_ge i Fss.length with hi | hi
  · obtain ⟨Fs, hFs⟩ : ∃ Fs, Fss[i]? = some Fs := ⟨_, List.getElem?_eq_getElem hi⟩
    obtain ⟨Es, hEs'⟩ : ∃ Es, Ess[i]? = some Es := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have h1 : (rChains d nIdx Fss Ess)[i]? = some (rChain d nIdx Fs Es) := by
      rw [rChains_getElem?, hFs, hEs']
    have h2 : (rChains d' nIdx Fss Ess)[i]? = some (rChain d' nIdx Fs Es) := by
      rw [rChains_getElem?, hFs, hEs']
    rw [sumFibre_of_getElem? h1, sumFibre_of_getElem? h2]
    have hEsD : Ess.getD i [] = Es := by rw [List.getD_eq_getElem?_getD, hEs']; rfl
    exact towerSet_rChain_congr (by rw [← hEsD]; exact hEs i hi) hsh hidx
  · rw [sumFibre_of_ge (by rw [rChains_length, hlenE]; exact Nat.le_trans (Nat.min_le_left _ _) hi),
      sumFibre_of_ge (by rw [rChains_length, hlenE]; exact Nat.le_trans (Nat.min_le_left _ _) hi)]

/-! ## The family spine at an index tuple -/

/-- The family at an index tuple, at the parameter frame. -/
noncomputable def sumFamAt (w nIdx : Nat) (ρp : Nat → V) (Fss Ess : List (List AVExpr))
    (is : List V) : V :=
  sumSet w (sumFibre w (consList is ρp) (rChains nIdx nIdx Fss Ess))

/-- **The family spine's value** at a frame whose `e`-th tail is a
parameter valuation and whose first `nIdx` entries are a fitting index
tuple: the family at that tuple. -/
theorem sumFamSpineI_val {w nIdx nP : Nat} {Fss Ess : List (List AVExpr)}
    {ppsAll : List (Nat × Nat × AVExpr)}
    (hlen : ppsAll.length = nP + nIdx)
    (hok : ∀ ρ : Nat → V, ParamsOkS w ρ (rChains nIdx nIdx Fss Ess) ppsAll)
    {ρp σ : Nat → V} {is : List V} {e : Nat} (hlenI : is.length = nIdx)
    (hσ : ∀ j, σ (j + e) = ρp j) (hidx : ∀ j, j < nIdx → σ j = consList is ρp j)
    (hsatP : Sat2 V (((ppsAll.take nP).map (·.2.2)).reverse) ρp)
    (hfit : SpineFit ρp ((ppsAll.drop nP).map (·.2.2)) is)
    (K : AVExpr) (hK : VExpr.bvarsBelow 0 K.erase)
    (hleaf : interp2 V (fun j => ρp (j + nP)) K
      = interp2 V (fun j => ρp (j + nP)) (directSumTyAV w ppsAll (rChains nIdx nIdx Fss Ess))) :
    interp2 V σ (AVExpr.mkAppN K (paramBvarsAt nP (nP + e) ++ fieldBvars nIdx))
      = sumFamAt w nIdx ρp Fss Ess is := by
  have hspP := spineFit_of_sat2 (Δ₀ := []) (Ds := (ppsAll.take nP).map (·.2.2))
    (by rw [List.append_nil]; exact hsatP)
  have hlenTake : ((ppsAll.take nP).map (·.2.2)).length = nP := by
    rw [List.length_map, List.length_take, hlen]; omega
  rw [hlenTake] at hspP
  have hρ0 : consList ((List.range nP).reverse.map ρp) (fun j => ρp (j + nP)) = ρp :=
    consList_range_reverse nP ρp
  have hfit' : SpineFit (consList ((List.range nP).reverse.map ρp) (fun j => ρp (j + nP)))
      ((ppsAll.drop nP).map (·.2.2)) is := by
    rw [hρ0]; exact hfit
  have hspAll : SpineFit (fun j => ρp (j + nP)) (ppsAll.map (·.2.2))
      ((List.range nP).reverse.map ρp ++ is) := by
    rw [← List.take_append_drop nP ppsAll, List.map_append]
    exact hspP.append hfit'
  have hps : (paramBvarsAt nP (nP + e)).map (interp2 V σ) = (List.range nP).reverse.map ρp :=
    map_paramBvarsAt_interp hσ
  have his : (fieldBvars nIdx).map (interp2 V σ) = is := by
    apply List.ext_getElem
    · simp [fieldBvars, hlenI]
    · intro k h1 h2
      have hk : k < nIdx := by simpa [fieldBvars] using h1
      simp only [fieldBvars, List.getElem_map, List.getElem_range, interp2_bvar]
      rw [hidx _ (by omega), consList_apply_lt _ _ _ (by omega), hlenI,
        show nIdx - 1 - (nIdx - 1 - k) = k from by omega, List.getElem?_eq_getElem h2,
        Option.getD_some]
  rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V σ) (g := SetTheory.app), List.map_append,
    hps, his, interp2_closed (V := V) hK σ (fun j => ρp (j + nP)), hleaf,
    sumFormerFold (hok _) hspAll, consList_append, hρ0]
  rfl

/-! ## The sources at a fitting spine -/

theorem srcVals_cons (is : List V) (s : Option Nat) (srcs : List (Option Nat)) :
    srcVals is (s :: srcs) = (match s with | some l => is.getD l pt | none => pt) :: srcVals is srcs :=
  rfl

/-- A fitting spine at a source-bounded chain whose index sources hit
the index tuple is the sources' values. -/
theorem srcVals_of_fit {is : List V} :
    ∀ {Fs : List AVExpr} {srcs : List (Option Nat)} {ρ : Nat → V} {bs : List V},
      srcs.length = Fs.length → FieldsBoundSrc ρ Fs srcs → SpineFit ρ Fs bs →
      (∀ j l, srcs[j]? = some (some l) → is.getD l pt = bs.getD j pt) →
      bs = srcVals is srcs
  | [], [], _, [], _, _, _, _ => rfl
  | [], [], _, _ :: _, _, _, hsp, _ => hsp.elim
  | [], _ :: _, _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, _ :: _, _, [], _, _, hsp, _ => hsp.elim
  | F :: Fs, s :: srcs, ρ, b :: bs, hlen, hbnd, hsp, hidx => by
    have ih := srcVals_of_fit (is := is) (Fs := Fs) (srcs := srcs) (ρ := cons b ρ) (bs := bs)
      (by simpa using hlen) (hbnd.2 b hsp.1) hsp.2
      (fun j l hj => by simpa using hidx (j + 1) l (by simpa using hj))
    rw [srcVals_cons]
    refine List.cons_eq_cons.mpr ⟨?_, ih⟩
    cases s with
    | none => exact mem_univ_zero (hbnd.1 rfl) hsp.1
    | some l =>
      have := hidx 0 l rfl
      simpa using this.symm

/-! ## The index chain -/

/-- **The walk down the index chain**: at the frame under the motive,
all minors and the first `l` indices, the remaining index entries read
to the former's index domains and at the K-frame the two hypothesis
records hold. -/
theorem sumIdxTail {m : EnvS2Core V env} {ψ : Name → Nat} {nP nIdx ℓ w b : Nat}
    {ρp : Nat → V} {M : V} {ms : List V} {pps ips : List (Nat × Nat × AVExpr)}
    {cds : List CtorDatum} {dM dt : Nat × Nat × AVExpr} {srcss : List (List (Option Nat))}
    (hlenP : pps.length = nP) (hlenI : ips.length = nIdx) (hlenM : ms.length = cds.length)
    (hokΓ : ∀ i, i < nP + cds.length + nIdx + 2 → ∀ σ : Nat → V,
      Sat2 V ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse).drop
        (nP + cds.length + nIdx + 2 - i)) σ →
      AnnotOkP V σ ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse).getD
        (nP + cds.length + nIdx + 2 - 1 - i) default))
    (hbase : ∀ is : List V, SpineFit ρp (ips.map (·.2.2)) is →
      AnnotOk2 V (consList is (consList ms (cons M ρp))) dt.2.2 →
      interp2 V (consList is (consList ms (cons M ρp))) dt.2.2
          = sumSet w (sumFibre w (consList is (consList ms (cons M ρp)))
              (rChains (nIdx + cds.length + 1) nIdx (fssOf nP cds) (essOf cds))) ∧
        RecHypS ℓ w (consList is (consList ms (cons M ρp))) (fssOf nP cds) (essOf cds)
          (ips.map (·.2.2)) (sumFamAt w nIdx ρp (fssOf nP cds) (essOf cds)) ∧
        SqHypS ℓ w (consList is (consList ms (cons M ρp))) (fssOf nP cds) (essOf cds)
          (ips.map (·.2.2)) srcss) :
    ∀ (k l : Nat) (is : List V), nIdx - l = k → l ≤ nIdx → is.length = l →
      SpineFit ρp ((ips.take l).map (·.2.2)) is →
      Sat2 V ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse).drop
        (nP + cds.length + nIdx + 2 - (nP + 1 + cds.length + l))) (consList is (consList ms (cons M ρp))) →
      RecIdxS ℓ w (fssOf nP cds) (essOf cds) (ips.map (·.2.2))
        (sumFamAt w nIdx ρp (fssOf nP cds) (essOf cds)) srcss dt
        ((rebit b (liftDoms (cds.length + 1) 0 ips)).drop l) (consList is (consList ms (cons M ρp))) := by
  have hlenR : (pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).length
      = nP + cds.length + nIdx + 2 := by
    rw [rds_length, hlenP, sumMinorsData_length, rebit_length, liftDoms_length, hlenI]
  have hlenΓ : ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse)).length
      = nP + cds.length + nIdx + 2 := by rw [List.length_reverse, List.length_map, hlenR]
  intro k
  induction k with
  | zero =>
    intro l is hk hl hlenIs hfit hsat
    have hln : l = nIdx := by omega
    subst hln
    rw [List.drop_eq_nil_of_le (by rw [rebit_length, liftDoms_length]; omega)]
    rw [List.take_of_length_le (by omega)] at hfit
    have hokt := (hokΓ (nP + 1 + cds.length + l) (by omega) _ hsat).1
    have hent := getD_reverse_of_peel hlenR (i := nP + 1 + cds.length + l) (by omega)
      (rds_getElem?_t (by rw [hlenP, sumMinorsData_length, rebit_length, liftDoms_length, hlenI] <;> omega))
    rw [hent] at hokt
    obtain ⟨hval, hyp, hsq⟩ := hbase is hfit hokt
    exact ⟨hokt, by rw [List.length_map, hlenI, fssOf_length]; exact hval, hyp, hsq⟩
  | succ k ih =>
    intro l is hk hl hlenIs hfit hsat
    have hln : l < nIdx := by omega
    obtain ⟨d, hd⟩ : ∃ d, ips[l]? = some d := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hdropl : (rebit b (liftDoms (cds.length + 1) 0 ips)).drop l
        = (d.1, b, d.2.2.liftN (cds.length + 1) l) :: (rebit b (liftDoms (cds.length + 1) 0 ips)).drop (l + 1) := by
      rw [List.drop_eq_getElem_cons (by rw [rebit_length, liftDoms_length, hlenI]; exact hln)]
      congr 1
      rw [List.getElem_eq_iff]
      unfold rebit
      rw [List.getElem?_map, liftDoms_getElem?, hd]
      simp only [Option.map_some, Nat.zero_add]
    rw [hdropl]
    have hentl : ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse)).getD
        (nP + cds.length + nIdx + 2 - 1 - (nP + 1 + cds.length + l)) default
        = d.2.2.liftN (cds.length + 1) l := by
      have := getD_reverse_of_peel hlenR (i := nP + 1 + cds.length + l) (by omega)
        (p := (d.1, b, d.2.2.liftN (cds.length + 1) l))
        (by rw [rds_getElem?_idx (by rw [rebit_length, liftDoms_length, hlenI]; exact hln)
                (by rw [hlenP, sumMinorsData_length])]
            unfold rebit
            rw [List.getElem?_map, liftDoms_getElem?, hd]
            simp only [Option.map_some, Nat.zero_add])
      exact this
    have hokl := (hokΓ (nP + 1 + cds.length + l) (by omega) _ hsat).1
    rw [hentl] at hokl
    -- the entry reads to the former's `l`-th index domain at the index frame
    have hdom : interp2 V (consList is (consList ms (cons M ρp))) (d.2.2.liftN (cds.length + 1) l)
        = interp2 V (consList is ρp) d.2.2 := by
      rw [interp2_liftN, ← hlenIs, shiftE_consList_len, ← hlenM,
        shiftE_consList_add ms 1 (cons M ρp), shiftE_one_cons]
    refine ⟨hokl, fun i hi => ?_⟩
    have hi0 := hi
    rw [hdom] at hi
    have hfit' : SpineFit ρp ((ips.take (l + 1)).map (·.2.2)) (is ++ [i]) := by
      rw [List.take_add_one, hd]
      simp only [Option.toList, List.map_append, List.map_cons, List.map_nil]
      exact hfit.append ⟨hi, trivial⟩
    have hsat' : Sat2 V ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse).drop
        (nP + cds.length + nIdx + 2 - (nP + 1 + cds.length + (l + 1)))) (cons i (consList is (consList ms (cons M ρp)))) := by
      have h := drop_succ_eq_getD_cons hlenΓ (i := nP + 1 + cds.length + l) (by omega)
      rw [show nP + 1 + cds.length + (l + 1) = nP + 1 + cds.length + l + 1 from by omega, h, hentl]
      exact Sat2_cons V hsat hi0
    have := ih (l + 1) (is ++ [i]) (by omega) (by omega) (by simp [hlenIs]) hfit' (by
      rw [consList_append]; exact hsat')
    rwa [consList_append] at this

/-! ## The minor chain -/

/-- **The walk down the minor chain**: at the frame under the motive
and the first `j` minors, the remaining minor entries read to their
spaces, then the index chain. -/
theorem sumMinorsTail {m : EnvS2Core V env} {ψ : Name → Nat} {nP nIdx ℓ w b : Nat}
    {ρp : Nat → V} {M : V} {pps ips : List (Nat × Nat × AVExpr)}
    {cds : List CtorDatum} {dM dt : Nat × Nat × AVExpr} {srcss : List (List (Option Nat))}
    (hlenP : pps.length = nP) (hlenI : ips.length = nIdx)
    (hokΓ : ∀ i, i < nP + cds.length + nIdx + 2 → ∀ σ : Nat → V,
      Sat2 V ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse).drop
        (nP + cds.length + nIdx + 2 - i)) σ →
      AnnotOkP V σ ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse).getD
        (nP + cds.length + nIdx + 2 - 1 - i) default))
    (hctor : ∀ (i : Nat) (cd : CtorDatum), cds[i]? = some cd →
      ∀ ms : List V, ms.length = i →
      interp2 V (consList ms (cons M ρp)) (minorAVAt m cd.1 ψ nP cd.2.1 b (1 + i) cd.2.2.1 cd.2.2.2)
        = minorSpI ℓ (concI w ρp M ((essOf cds).getD i []) i) ((fssOf nP cds).getD i []) ρp [])
    (hbase : ∀ (ms : List V), ms.length = cds.length →
      (∀ j, j < cds.length →
        ms.getD j pt ∈ˢ minorSpI ℓ (concI w ρp M ((essOf cds).getD j []) j) ((fssOf nP cds).getD j []) ρp []) →
      ∀ is : List V, SpineFit ρp (ips.map (·.2.2)) is →
      AnnotOk2 V (consList is (consList ms (cons M ρp))) dt.2.2 →
      interp2 V (consList is (consList ms (cons M ρp))) dt.2.2
          = sumSet w (sumFibre w (consList is (consList ms (cons M ρp)))
              (rChains (nIdx + cds.length + 1) nIdx (fssOf nP cds) (essOf cds))) ∧
        RecHypS ℓ w (consList is (consList ms (cons M ρp))) (fssOf nP cds) (essOf cds)
          (ips.map (·.2.2)) (sumFamAt w nIdx ρp (fssOf nP cds) (essOf cds)) ∧
        SqHypS ℓ w (consList is (consList ms (cons M ρp))) (fssOf nP cds) (essOf cds)
          (ips.map (·.2.2)) srcss) :
    ∀ (k j : Nat) (ms : List V), cds.length - j = k → j ≤ cds.length → ms.length = j →
      (∀ j', j' < j →
        ms.getD j' pt ∈ˢ minorSpI ℓ (concI w ρp M ((essOf cds).getD j' []) j')
          ((fssOf nP cds).getD j' []) ρp []) →
      Sat2 V ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse).drop
        (nP + cds.length + nIdx + 2 - (nP + 1 + j))) (consList ms (cons M ρp)) →
      RecTailS ℓ w (fssOf nP cds) (essOf cds) (ips.map (·.2.2))
        (sumFamAt w nIdx ρp (fssOf nP cds) (essOf cds)) srcss
        (rebit b (liftDoms (cds.length + 1) 0 ips)) dt
        (sumMinorsData m ψ nP b (cds.drop j) (1 + j)) (consList ms (cons M ρp)) := by
  have hlenR : (pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).length
      = nP + cds.length + nIdx + 2 := by
    rw [rds_length, hlenP, sumMinorsData_length, rebit_length, liftDoms_length, hlenI]
  have hlenΓ : ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse)).length
      = nP + cds.length + nIdx + 2 := by rw [List.length_reverse, List.length_map, hlenR]
  intro k
  induction k with
  | zero =>
    intro j ms hk hj hlenM hms hsat
    have hjn : j = cds.length := by omega
    subst hjn
    rw [List.drop_eq_nil_of_le (Nat.le_refl _)]
    show RecIdxS ℓ w _ _ _ _ _ dt (rebit b (liftDoms (cds.length + 1) 0 ips)) (consList ms (cons M ρp))
    have h := sumIdxTail (m := m) (ψ := ψ) (nP := nP) (nIdx := nIdx) (ℓ := ℓ) (w := w) (b := b)
      (ρp := ρp) (M := M) (ms := ms) (pps := pps) (ips := ips) (cds := cds) (dM := dM) (dt := dt)
      (srcss := srcss) hlenP hlenI hlenM hokΓ (hbase ms hlenM hms) nIdx 0 [] (by omega)
      (Nat.zero_le _) rfl trivial (by
        rw [Nat.add_zero]
        show Sat2 V _ (consList [] (consList ms (cons M ρp)))
        exact hsat)
    rw [List.drop_zero] at h
    exact h
  | succ k ih =>
    intro j ms hk hj hlenM hms hsat
    have hjn : j < cds.length := by omega
    obtain ⟨cd, hcd⟩ : ∃ cd, cds[j]? = some cd := ⟨_, List.getElem?_eq_getElem hjn⟩
    rw [List.drop_eq_getElem_cons hjn, Option.some.inj ((List.getElem?_eq_getElem hjn).symm.trans hcd)]
    obtain ⟨C, nF, ds, Es⟩ := cd
    show AnnotOk2 V (consList ms (cons M ρp)) (minorAVAt m C ψ nP nF b (1 + j) ds Es) ∧
      ∀ mv, mv ∈ˢ interp2 V (consList ms (cons M ρp)) (minorAVAt m C ψ nP nF b (1 + j) ds Es) →
        RecTailS ℓ w _ _ _ _ srcss (rebit b (liftDoms (cds.length + 1) 0 ips)) dt
          (sumMinorsData m ψ nP b (cds.drop (j + 1)) (1 + j + 1)) (cons mv (consList ms (cons M ρp)))
    have hentj : ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse)).getD
        (nP + cds.length + nIdx + 2 - 1 - (nP + 1 + j)) default
        = minorAVAt m C ψ nP nF b (1 + j) ds Es := by
      have := getD_reverse_of_peel hlenR (i := nP + 1 + j) (by omega)
        (p := (0, b, minorAVAt m C ψ nP nF b (1 + j) ds Es))
        (by rw [rds_getElem?_minor (by rw [sumMinorsData_length]; exact hjn)
                (by rw [hlenP]),
              sumMinorsData_getElem?, hcd]
            rfl)
      exact this
    have hokj := (hokΓ (nP + 1 + j) (by omega) _ hsat).1
    rw [hentj] at hokj
    have hread := hctor j (C, nF, ds, Es) hcd ms hlenM
    refine ⟨hokj, fun mv hmv => ?_⟩
    have hsat' : Sat2 V ((((pps ++ [dM] ++ sumMinorsData m ψ nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++ [dt]).map (·.2.2)).reverse).drop
        (nP + cds.length + nIdx + 2 - (nP + 1 + (j + 1)))) (cons mv (consList ms (cons M ρp))) := by
      have h := drop_succ_eq_getD_cons hlenΓ (i := nP + 1 + j) (by omega)
      rw [show nP + 1 + (j + 1) = nP + 1 + j + 1 from by omega, h, hentj]
      exact Sat2_cons V hsat hmv
    have hms' : ∀ j', j' < j + 1 →
        (ms ++ [mv]).getD j' pt ∈ˢ minorSpI ℓ (concI w ρp M ((essOf cds).getD j' []) j')
          ((fssOf nP cds).getD j' []) ρp [] := by
      intro j' hj'
      rcases Nat.lt_or_ge j' j with hlt | hge
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD]
        exact hms j' hlt
      · have hjj : j' = j := by omega
        subst hjj
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlenM, Nat.sub_self]
        simp only [List.getElem?_cons_zero, Option.getD_some]
        rw [← hread]
        exact hmv
    have := ih (j + 1) (ms ++ [mv]) (by omega) (by omega) (by simp [hlenM]) hms' (by
      rw [consList_append]; exact hsat')
    rw [consList_append] at this
    rwa [show 1 + (j + 1) = 1 + j + 1 from by omega] at this

set_option maxHeartbeats 6400000 in
/-- **The sum recursor's frames, by computation.** -/
theorem sumRecFrames {m : EnvS2Core V env} {p : DirectSumParts} {cvTa cvRa : ConstantVal}
    {ctorsA : List (ConstantVal × Nat)}
    {ppsAll : (Name → Nat) → List (Nat × Nat × AVExpr)}
    {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AVExpr)}
    {esF : Nat → (Name → Nat) → List AVExpr} {srcsF : Nat → List (Option Nat)}
    (hFD : FormerData m cvTa (p.nP + p.nIdx) p.resSort ppsAll)
    (hcf : ∀ j cA, ctorsA[j]? = some cA →
      CtorFactsAt m p.cvT.name p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large
        idxF dsF esF srcsF j cA)
    (hleafT : ∀ ψ, m.acval p.cvT.name ψ
      = directSumTyAV (p.resSort.eval ψ) (ppsAll ψ)
          (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
            (essOf (ctorDataList dsF esF ψ ctorsA 0))))
    (hleafC : ∀ j cA, ctorsA[j]? = some cA → ∀ ψ, m.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))))
    (hiff : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ j cA, ctorsA[j]? = some cA → ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((dsF j ψ).drop p.nP).map (·.2.2)) ∧
        (∀ bs : List V, SpineFit ρ (((dsF j ψ).drop p.nP).map (·.2.2)) bs →
          (∀ E ∈ esF j ψ, AnnotOkP V (consList bs ρ) E) ∧
          SpineFit ρ (((ppsAll ψ).drop p.nP).map (·.2.2)) (idxValsAt ρ (esF j ψ) bs)))
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((ppsAll ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ
        (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0))) ∧
      SumFieldsValid ρ
        (rChains p.nIdx p.nIdx (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0))))
    (hwl : p.large = true → p.resSort.isNeverZero = true ∨ ctorsA.length < 2)
    (ψ : Name → Nat) {fvsR : List Expr} {oR : Expr}
    (hR : OpenedP m ψ (p.nP + ctorsA.length + p.nIdx + 2) cvRa.type fvsR oR
      (((sumRdsAV m p ppsAll dsF esF ctorsA ψ).map (·.2.2)).reverse)
      (recConcAV ctorsA.length p.nIdx)) :
    ∀ ρp : Nat → V, Sat2 V ((((ppsAll ψ).take p.nP).map (·.2.2)).reverse) ρp →
      RecBaseS ((sumElimLevel p).eval ψ) (p.resSort.eval ψ) ρp
        (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0)) (essOf (ctorDataList dsF esF ψ ctorsA 0))
        (((ppsAll ψ).drop p.nP).map (·.2.2))
        (sumFamAt (p.resSort.eval ψ) p.nIdx ρp (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))
          (essOf (ctorDataList dsF esF ψ ctorsA 0)))
        (srcssOf srcsF ctorsA.length)
        (0, pwBit ψ (Level.zeronessOf (sumElimLevel p)),
          motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ((ppsAll ψ).drop p.nP))
        (sumMinorsData m ψ p.nP (pwBit ψ (Level.zeronessOf (sumElimLevel p)))
          (ctorDataList dsF esF ψ ctorsA 0) 1)
        (rebit (pwBit ψ (Level.zeronessOf (sumElimLevel p)))
          (liftDoms ((ctorDataList dsF esF ψ ctorsA 0).length + 1) 0 ((ppsAll ψ).drop p.nP)))
        (0, pwBit ψ (Level.zeronessOf (sumElimLevel p)),
          majorAVAt m p.cvT.name ψ p.nP p.nIdx (ctorDataList dsF esF ψ ctorsA 0).length) := by
  intro ρp hsatP
  -- the facts at `ψ`
  have hleafTψ := hleafT ψ
  have hleafCψ : ∀ j cA, ctorsA[j]? = some cA → m.acval cA.1.name ψ
      = directSumMkAV (p.resSort.eval ψ) j (dsF j ψ) (((dsF j ψ).drop p.nP).map (·.2.2))
          (uChains (fssOf p.nP (ctorDataList dsF esF ψ ctorsA 0))) := fun j cA h => hleafC j cA h ψ
  have hiffψ : ∀ j cA, ctorsA[j]? = some cA → ∀ ρ : Nat → V,
      Sat2 V (((ppsAll ψ).take p.nP).map (·.2.2)).reverse ρ ↔
        Sat2 V (((dsF j ψ).take p.nP).map (·.2.2)).reverse ρ := fun j cA h ρ => hiff j cA h ψ ρ
  have hfieldsψ := fun j cA h ρ => hfields j cA h ψ ρ
  have hwalks := formerWalksS hFD hFssOk ψ
  have hclT := m.cval_closedL p.cvT.name ψ
  -- names
  generalize hcds : ctorDataList dsF esF ψ ctorsA 0 = cds at hleafTψ hleafCψ hR hwalks ⊢
  generalize hb : pwBit ψ (Level.zeronessOf (sumElimLevel p)) = b at hR ⊢
  generalize hℓ : (sumElimLevel p).eval ψ = ℓ
  generalize hw : p.resSort.eval ψ = w at hleafTψ hleafCψ hfieldsψ hwalks ⊢
  generalize hpps : (ppsAll ψ).take p.nP = pps at hR hsatP hwalks hiffψ ⊢
  generalize hips : (ppsAll ψ).drop p.nP = ips at hR hwalks hfieldsψ ⊢
  have hn : cds.length = ctorsA.length := by rw [← hcds, ctorDataList_length]
  have hlenP : pps.length = p.nP := by rw [← hpps, List.length_take, hFD.len ψ]; omega
  have hlenI : ips.length = p.nIdx := by rw [← hips, List.length_drop, hFD.len ψ]; omega
  have hbelowI : DomsBelow p.nP ips := by
    rw [← hips]; have := DomsBelow.drop p.nP (hFD.below ψ); rwa [Nat.zero_add] at this
  have hpal : ppsAll ψ = pps ++ ips := by rw [← hpps, ← hips, List.take_append_drop]
  rw [← hn] at hR
  have hbz : ℓ = 0 ↔ b = 0 := by
    rw [← hb, ← hℓ, pwBit_eq_zero_iff, Setlec.PropWhen.zeronessOf_sound, beq_iff_eq]
  have hrds : sumRdsAV m p ppsAll dsF esF ctorsA ψ
      = rebit b pps ++ [(0, b, motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips)] ++
        sumMinorsData m ψ p.nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++
        [(0, b, majorAVAt m p.cvT.name ψ p.nP p.nIdx cds.length)] := by
    rw [sumRdsAV, sumRecDataAV, hcds, hb, hpps, hips]
  rw [hrds] at hR
  -- the per-constructor facts, positionally on `cds`
  have hcd : ∀ i cd, cds[i]? = some cd → ∃ cA, ctorsA[i]? = some cA ∧
      cd = (cA.1.name, cA.2, dsF i ψ, esF i ψ) := by
    intro i cd hi
    rw [← hcds, ctorDataList_getElem?, Nat.zero_add] at hi
    cases h : ctorsA[i]? with
    | none => rw [h] at hi; exact nomatch hi
    | some cA => rw [h] at hi; exact ⟨cA, rfl, (Option.some.inj hi).symm⟩
  have hcdA : ∀ i cA, ctorsA[i]? = some cA → cds[i]? = some (cA.1.name, cA.2, dsF i ψ, esF i ψ) := by
    intro i cA hi
    rw [← hcds, ctorDataList_getElem?, hi, Nat.zero_add]
    rfl
  have hFsj : ∀ i cA, ctorsA[i]? = some cA →
      (fssOf p.nP cds)[i]? = some (((dsF i ψ).drop p.nP).map (·.2.2)) := by
    intro i cA hi
    rw [fssOf_getElem?, hcdA i cA hi]
    rfl
  have hEsj : ∀ i cA, ctorsA[i]? = some cA → (essOf cds)[i]? = some (esF i ψ) := by
    intro i cA hi
    rw [essOf_getElem?, hcdA i cA hi]
    rfl
  have hFsjD : ∀ i cA, ctorsA[i]? = some cA →
      (fssOf p.nP cds).getD i [] = ((dsF i ψ).drop p.nP).map (·.2.2) := by
    intro i cA hi
    rw [List.getD_eq_getElem?_getD, hFsj i cA hi]; rfl
  have hEsjD : ∀ i cA, ctorsA[i]? = some cA → (essOf cds).getD i [] = esF i ψ := by
    intro i cA hi
    rw [List.getD_eq_getElem?_getD, hEsj i cA hi]; rfl
  have hlenFs : (fssOf p.nP cds).length = ctorsA.length := by rw [fssOf_length, hn]
  have hlenEs : (essOf cds).length = ctorsA.length := by rw [essOf_length, hn]
  have hlenIds : (ips.map (·.2.2)).length = p.nIdx := by rw [List.length_map, hlenI]
  -- the field chains at the parameter frame
  have hokB : SumFieldsOkB w ρp (fssOf p.nP cds) := by
    intro Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    obtain ⟨cA, hiA, rfl⟩ := hcd i cd hi
    exact (hfieldsψ i cA hiA ρp ((hiffψ i cA hiA ρp).mp hsatP)).1
  have hvB : SumFieldsValid ρp (fssOf p.nP cds) := by
    intro Fs hFs
    obtain ⟨cd, hcdm, rfl⟩ := List.mem_map.mp hFs
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hcdm
    obtain ⟨cA, hiA, rfl⟩ := hcd i cd hi
    exact (hfieldsψ i cA hiA ρp ((hiffψ i cA hiA ρp).mp hsatP)).2.1
  have hok : ∀ ρ : Nat → V, ParamsOkS w ρ (rChains p.nIdx p.nIdx (fssOf p.nP cds) (essOf cds))
      (pps ++ ips) := fun ρ => by
    have := (hwalks ρ).1
    rwa [hpal] at this
  have hcl : VExpr.bvarsBelow 0
      (directSumTyAV w (pps ++ ips) (rChains p.nIdx p.nIdx (fssOf p.nP cds) (essOf cds))).erase := by
    rw [← hpal]
    rwa [hleafTψ] at hclT
  have hlenAll : (pps ++ ips).length = p.nP + p.nIdx := by simp [hlenP, hlenI]
  have hleafT' : interp2 V (fun j => ρp (j + p.nP)) (m.acval p.cvT.name ψ)
      = interp2 V (fun j => ρp (j + p.nP))
          (directSumTyAV w (pps ++ ips) (rChains p.nIdx p.nIdx (fssOf p.nP cds) (essOf cds))) := by
    rw [hleafTψ, hpal]
  -- the frame's context
  have hlenR : (rebit b pps ++ [(0, b, motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips)] ++
      sumMinorsData m ψ p.nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++
      [(0, b, majorAVAt m p.cvT.name ψ p.nP p.nIdx cds.length)]).length
      = p.nP + cds.length + p.nIdx + 2 := by
    rw [rds_length, rebit_length, hlenP, sumMinorsData_length, rebit_length, liftDoms_length, hlenI]
  have hlenΓ : ((((rebit b pps ++ [(0, b, motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips)] ++
      sumMinorsData m ψ p.nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++
      [(0, b, majorAVAt m p.cvT.name ψ p.nP p.nIdx cds.length)]).map
        (fun d : Nat × Nat × AVExpr => d.2.2)).reverse)).length = p.nP + cds.length + p.nIdx + 2 := by
    rw [List.length_reverse, List.length_map, hlenR]
  have hsatΓ : Sat2 V (((((rebit b pps ++ [(0, b, motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips)] ++
      sumMinorsData m ψ p.nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++
      [(0, b, majorAVAt m p.cvT.name ψ p.nP p.nIdx cds.length)]).map
        (fun d : Nat × Nat × AVExpr => d.2.2)).reverse)).drop (p.nP + cds.length + p.nIdx + 2 - p.nP)) ρp := by
    rw [show p.nP + cds.length + p.nIdx + 2 - p.nP
        = (sumMinorsData m ψ p.nP b cds 1).length + (rebit b (liftDoms (cds.length + 1) 0 ips)).length + 2 from by
        rw [sumMinorsData_length, rebit_length, liftDoms_length, hlenI]; omega,
      rds_drop_params, rebit_map_dom]
    exact hsatP
  have hentM : ((((rebit b pps ++ [(0, b, motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips)] ++
      sumMinorsData m ψ p.nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++
      [(0, b, majorAVAt m p.cvT.name ψ p.nP p.nIdx cds.length)]).map
        (fun d : Nat × Nat × AVExpr => d.2.2)).reverse)).getD (p.nP + cds.length + p.nIdx + 2 - 1 - p.nP) default
      = motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips := by
    have := getD_reverse_of_peel hlenR (i := p.nP) (by omega)
      (p := (0, b, motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips))
      (rds_getElem?_M (by rw [rebit_length, hlenP]))
    exact this
  -- the elimination restriction
  have hwl' : w = 0 → ℓ ≠ 0 → (fssOf p.nP cds).length ≤ 1 := by
    intro hw0 hl0
    have hlarge : p.large = true := by
      cases hpl : p.large
      · exfalso; apply hl0
        rw [← hℓ]; simp [sumElimLevel, Setlec.directElimLevel, hpl, Level.eval]
      · rfl
    rcases hwl hlarge with hnz | hlt
    · exfalso
      exact Setlec.Level.isNeverZero_sound ψ _ hnz (by rw [hw]; exact hw0)
    · rw [hlenFs]; omega
  have hlarge_of : ℓ ≠ 0 → p.large = true := by
    intro hl0
    cases hpl : p.large
    · exfalso; apply hl0
      rw [← hℓ]; simp [sumElimLevel, Setlec.directElimLevel, hpl, Level.eval]
    · rfl
  -- `RecBaseS`
  refine ⟨by rw [sumMinorsData_length, fssOf_length], by rw [rebit_length, liftDoms_length, hlenI, hlenIds], ?_, ?_⟩
  · -- the motive's grading
    have h := (hR.okΓ p.nP (by omega) ρp hsatΓ).1
    rw [hentM] at h
    exact h
  · intro M hM
    have hsatM : Sat2 V (((((rebit b pps ++ [(0, b, motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips)] ++
        sumMinorsData m ψ p.nP b cds 1 ++ rebit b (liftDoms (cds.length + 1) 0 ips) ++
        [(0, b, majorAVAt m p.cvT.name ψ p.nP p.nIdx cds.length)]).map
          (fun d : Nat × Nat × AVExpr => d.2.2)).reverse)).drop
          (p.nP + cds.length + p.nIdx + 2 - (p.nP + 1 + 0))) (consList [] (cons M ρp)) := by
      have h := drop_succ_eq_getD_cons hlenΓ (i := p.nP) (by omega)
      rw [Nat.add_zero, h, hentM]
      exact Sat2_cons V hsatΓ hM
    -- the motive's value: the nested product over the index telescope
    have hMtele : M ∈ˢ piTele (ℓ + 1) (teleOfFields ρp (ips.map (·.2.2)))
        (fun is' => piR (ℓ + 1) (sumFamAt w p.nIdx ρp (fssOf p.nP cds) (essOf cds) is')
          fun _ => (univ ℓ : V)) [] := by
      have hMv : M ∈ˢ interp2 V ρp (motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips) := hM
      unfold motiveAVI at hMv
      rw [interp_mkPisAV_piTele (v := ℓ + 1) (gds := rebit (pwBit ψ PropWhen.never) ips)
        (fun d hd => by
          rw [mem_rebit hd]
          exact ⟨fun h => absurd h (pwBit_ne_zero_of_isNever rfl ψ),
            fun h => absurd h (Nat.succ_ne_zero _)⟩)
        (B := fun is' => piR (ℓ + 1) (sumFamAt w p.nIdx ρp (fssOf p.nP cds) (essOf cds) is')
          fun _ => (univ ℓ : V)) ?_, rebit_map_dom] at hMv
      · exact hMv
      intro as hsp
      rw [rebit_map_dom] at hsp
      have hlenAs : as.length = p.nIdx := by rw [hsp.length_eq, hlenIds]
      rw [interp2_pi, hℓ]
      have hfam := sumFamSpineI_val (w := w) (nIdx := p.nIdx) (nP := p.nP)
        (Fss := fssOf p.nP cds) (Ess := essOf cds) hlenAll hok (σ := consList as ρp) (e := p.nIdx)
        hlenAs (fun j => by rw [← hlenAs]; exact consList_apply_add as ρp j) (fun j _ => rfl)
        (by rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]; exact hsatP)
        (by rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]; exact hsp)
        (m.acval p.cvT.name ψ) hclT hleafT'
      rw [hfam, List.nil_append, piR_congr_bit (v' := ℓ + 1)
        ⟨fun h => absurd h (pwBit_ne_zero_of_isNever rfl ψ), fun h => absurd h (Nat.succ_ne_zero _)⟩]
      rfl
    -- the tail walk
    have htail := sumMinorsTail (m := m) (ψ := ψ) (nP := p.nP) (nIdx := p.nIdx) (ℓ := ℓ) (w := w)
      (b := b) (ρp := ρp) (M := M) (pps := rebit b pps) (ips := ips) (cds := cds)
      (dM := (0, b, motiveAVI m p.cvT.name ψ p.nP p.nIdx (sumElimLevel p) ips))
      (dt := (0, b, majorAVAt m p.cvT.name ψ p.nP p.nIdx cds.length))
      (srcss := srcssOf srcsF ctorsA.length) (by rw [rebit_length, hlenP]) hlenI
      hR.okΓ ?_ ?_ cds.length 0 [] (by omega) (Nat.zero_le _) rfl
      (fun j' hj' => absurd hj' (Nat.not_lt_zero _)) hsatM
    · rw [List.drop_zero, Nat.add_zero] at htail
      exact htail
    · -- minor `i`'s reading: the minor space
      intro i cd hi ms hlenM
      obtain ⟨cA, hiA, rfl⟩ := hcd i cd hi
      obtain ⟨-, -, hCD⟩ := hcf i cA hiA
      have hsatC := (hiffψ i cA hiA ρp).mp hsatP
      have hlenFs' : ((((dsF i ψ).drop p.nP).map (·.2.2))).length = cA.2 := by simp [hCD.len ψ]
      have hlenFds : (((dsF i ψ).drop p.nP)).length = cA.2 := by simp [hCD.len ψ]
      rw [hFsjD i cA hiA, hEsjD i cA hiA]
      show interp2 V (consList ms (cons M ρp))
        (minorAVAt m cA.1.name ψ p.nP cA.2 b (1 + i) (dsF i ψ) (esF i ψ)) = _
      have hsh : shiftE (1 + i) 0 (consList ms (cons M ρp)) = ρp := by
        rw [← hlenM, Nat.add_comm, shiftE_consList_add ms 1 (cons M ρp), shiftE_one_cons]
      have hσi : consList ms (cons M ρp) i = M := by
        rw [← hlenM, show ms.length = 0 + ms.length from (Nat.zero_add _).symm, consList_apply_add]
        rfl
      unfold minorAVAt
      refine interp_minorSpI_of_tele
        (by simp only [rebit_length, liftDoms_length, List.length_map]) ?_ ?_ ?_
      · intro d hd
        rw [mem_rebit hd]; exact hbz
      · -- the field domains agree along a fitting chain
        intro j as hj hsp
        rw [hlenFs'] at hj
        have hlenAs : as.length = j := by
          rw [hsp.length_eq, List.length_take, hlenFs']; omega
        rw [rebit_getD _ _ _ (by rw [liftDoms_length]; omega)]
        show interp2 V (consList as (consList ms (cons M ρp)))
          ((liftDoms (1 + i) 0 ((dsF i ψ).drop p.nP)).getD j default).2.2 = _
        obtain ⟨q, hq⟩ : ∃ q, ((dsF i ψ).drop p.nP)[j]? = some q :=
          ⟨_, List.getElem?_eq_getElem (by rw [hlenFds]; exact hj)⟩
        have hsh' : shiftE (1 + i) j (consList as (consList ms (cons M ρp))) = consList as ρp := by
          rw [← hlenAs, shiftE_consList_len, hsh]
        rw [List.getD_eq_getElem?_getD, liftDoms_getElem?, hq, Option.map_some, Option.getD_some]
        show interp2 V (consList as (consList ms (cons M ρp))) (q.2.2.liftN (1 + i) (0 + j)) = _
        rw [interp2_liftN, Nat.zero_add, hsh', fields_getD (by rw [hlenFds]; exact hj),
          List.getD_eq_getElem?_getD, hq, Option.getD_some]
      · -- the core: the motive at the index values and the constructor leaf's fold
        intro as hsp
        have hlenAs : as.length = cA.2 := by rw [hsp.length_eq, hlenFs']
        have hMval : consList as (consList ms (cons M ρp)) (cA.2 + (1 + i) - 1) = M := by
          rw [show cA.2 + (1 + i) - 1 = i + as.length from by omega, consList_apply_add]
          exact hσi
        have hσ : ∀ j, consList as (consList ms (cons M ρp)) (j + ((1 + i) + cA.2)) = ρp j := by
          intro j
          rw [show j + ((1 + i) + cA.2) = (j + (i + 1)) + as.length from by omega,
            consList_apply_add, ← hlenM, show j + (ms.length + 1) = (j + 1) + ms.length from by omega,
            consList_apply_add]
          rfl
        have hshF : shiftE (1 + i) cA.2 (consList as (consList ms (cons M ρp))) = consList as ρp := by
          rw [← hlenAs, shiftE_consList_len, hsh]
        have hleafC' : m.acval cA.1.name ψ
            = directSumMkAV w i ((dsF i ψ).take p.nP ++ (dsF i ψ).drop p.nP)
                (((dsF i ψ).drop p.nP).map (·.2.2)) (uChains (fssOf p.nP cds)) := by
          rw [hleafCψ i cA hiA, List.take_append_drop]
        rw [AVExpr.mkAppN_append_one, interp2_app, interp2_mkAppN, interp2_bvar, hMval,
          ← List.foldl_map (f := interp2 V (consList as (consList ms (cons M ρp)))) (g := SetTheory.app),
          List.map_map]
        have hidxv : (esF i ψ).map ((interp2 V (consList as (consList ms (cons M ρp)))) ∘
            fun E => E.liftN (1 + i) cA.2) = idxValsAt ρp (esF i ψ) as := by
          unfold idxValsAt
          apply List.map_congr_left
          intro E _
          simp only [Function.comp]
          rw [interp2_liftN, hshF]
        rw [hidxv]
        unfold concI
        congr 1
        rw [interp2_mkAppN,
          ← List.foldl_map (f := interp2 V (consList as (consList ms (cons M ρp)))) (g := SetTheory.app),
          List.map_append, show p.nP + (1 + i) + cA.2 = p.nP + ((1 + i) + cA.2) from by omega,
          map_paramBvarsAt_interp hσ,
          show fieldBvars cA.2 = (List.range cA.2).map (fun k => AVExpr.bvar (cA.2 - 1 - k)) from rfl,
          map_fieldBvars_interp hlenAs,
          interp2_closed (V := V) (m.cval_closedL cA.1.name ψ) _ (fun j => ρp (j + p.nP)),
          hleafC']
        have hlenP' : ((((dsF i ψ).take p.nP).map (·.2.2))).length = p.nP := by simp [hCD.len ψ]
        have hsp₁ := spineFit_of_sat2 (Δ₀ := []) (Ds := ((dsF i ψ).take p.nP).map (·.2.2))
          (by rw [List.append_nil]; exact hsatC)
        rw [hlenP'] at hsp₁
        unfold ctorValI
        rw [List.nil_append]
        rcases Nat.eq_zero_or_pos w with hw0 | hwpos
        · rw [hw0, directSumMkAV_zero, foldl_app_pt_sum, if_pos rfl]
        · have hw' : w ≠ 0 := Nat.pos_iff_ne_zero.mp hwpos
          rw [directSumMkAV_fold hw' hsp₁ (by rw [consList_range_reverse]; exact hsp)
            (by rw [consList_range_reverse]; exact SumFieldsOkB_uChains hokB)
            (by rw [uChains_getElem?, hFsj i cA hiA]; rfl), if_neg hw']
    · -- the K-frame: the major's reading and the two hypothesis records
      intro ms hlenM hms is hfit hokt
      have hlenIs : is.length = p.nIdx := by rw [hfit.length_eq, hlenIds]
      have hfrP := kframe_frP (ρp := ρp) (M := M) (n := cds.length) (nIdx := p.nIdx) hlenIs hlenM
      have hfrIdx := kframe_frameIdx (ρp := ρp) (M := M) (ms := ms) hlenIs
      have hshK : shiftE (p.nIdx + cds.length + 1) 0 (consList is (consList ms (cons M ρp))) = ρp := by
        unfold frP at hfrP; exact hfrP
      have hlenIs' : is.length = (ips.map (·.2.2)).length := by rw [hlenIds]; exact hlenIs
      have hlenM' : ms.length = (fssOf p.nP cds).length := by rw [fssOf_length]; exact hlenM
      have hshK' : shiftE ((ips.map (·.2.2)).length + (fssOf p.nP cds).length + 1) 0
          (consList is (consList ms (cons M ρp))) = ρp := by
        rw [hlenIds, hlenFs, ← hn]; exact hshK
      -- the major's value
      have hval : interp2 V (consList is (consList ms (cons M ρp)))
          (majorAVAt m p.cvT.name ψ p.nP p.nIdx cds.length)
          = sumFamAt w p.nIdx ρp (fssOf p.nP cds) (essOf cds) is := by
        unfold majorAVAt
        rw [show p.nP + 1 + cds.length + p.nIdx = p.nP + (1 + cds.length + p.nIdx) from by omega]
        refine sumFamSpineI_val hlenAll hok hlenIs (fun j => ?_) (fun j hj => ?_)
          (by rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]; exact hsatP)
          (by rw [List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega), List.nil_append]; exact hfit)
          (m.acval p.cvT.name ψ) hclT hleafT'
        · rw [show 1 + cds.length + p.nIdx = p.nIdx + cds.length + 1 from by omega]
          exact kframe_apply_add hlenIs hlenM j
        · rw [consList_apply_lt is (consList ms (cons M ρp)) j (by omega),
            consList_apply_lt is ρp j (by omega),
            List.getElem?_eq_getElem (by omega), Option.getD_some, Option.getD_some]
      have hfibre : sumFamAt w p.nIdx ρp (fssOf p.nP cds) (essOf cds) is
          = sumSet w (sumFibre w (consList is (consList ms (cons M ρp)))
              (rChains (p.nIdx + cds.length + 1) p.nIdx (fssOf p.nP cds) (essOf cds))) := by
        unfold sumFamAt
        congr 1
        refine sumFibre_rChains_congr (fun j hj => ?_) (by rw [hlenEs, hlenFs]) ?_ ?_
        · rw [hlenFs] at hj
          obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
          rw [hEsjD j cA hjA]
          exact (hcf j cA hjA).2.2.lenE ψ
        · rw [hshK, ← hlenIs, shiftE_consList]
        · rw [hfrIdx, frameIdx_consList hlenIs]
      refine ⟨by rw [hval, hfibre], ?_, ?_⟩
      · -- `RecHypS`
        refine ⟨?_, ?_, by rw [hlenEs, hlenFs], ?_, ?_, ?_, ?_⟩
        · -- the restricted chains are graded at the K-frame
          intro Fs' hFs'
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hFs'
          rw [rChains_getElem?] at hj
          cases hF : (fssOf p.nP cds)[j]? with
          | none => rw [hF] at hj; exact nomatch hj
          | some Fs =>
            cases hE : (essOf cds)[j]? with
            | none => rw [hF, hE] at hj; exact nomatch hj
            | some Es =>
              rw [hF, hE] at hj
              obtain rfl := Option.some.inj hj
              have hjn : j < ctorsA.length := by
                have := (List.getElem?_eq_some_iff.mp hF).1; rwa [hlenFs] at this
              obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hjn⟩
              obtain rfl := Option.some.inj ((hFsj j cA hjA).symm.trans hF)
              obtain rfl := Option.some.inj ((hEsj j cA hjA).symm.trans hE)
              have hsatC := (hiffψ j cA hjA ρp).mp hsatP
              refine FieldsOkB_rChain (by rw [hlenIds]; exact (hcf j cA hjA).2.2.lenE ψ) ?_ ?_
              · rw [hshK']; exact (hfieldsψ j cA hjA ρp hsatC).1
              · rw [hshK']
                intro bs hsp E hE'
                exact ((hfieldsψ j cA hjA ρp hsatC).2.2 bs hsp).1 E hE' |>.1
        · intro j hj
          rw [hlenFs] at hj
          obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
          rw [hEsjD j cA hjA, hlenIds]
          exact (hcf j cA hjA).2.2.lenE ψ
        · rw [kframe_frM hlenIs' hlenM', kframe_frP hlenIs' hlenM']
          exact hMtele
        · rw [kframe_frP hlenIs' hlenM', kframe_frameIdx hlenIs']
          exact hfit
        · rw [kframe_frameIdx hlenIs', hlenIds, hlenFs, ← hn]
          exact hfibre
        · intro j hj
          rw [kframe_frMs hlenIs' hlenM' hj, kframe_frP hlenIs' hlenM', kframe_frM hlenIs' hlenM']
          exact hms j (by rw [fssOf_length] at hj; exact hj)
      · -- `SqHypS`
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro j hj
          rw [hlenFs] at hj
          obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
          rw [hFsjD j cA hjA, srcssOf_getD srcsF hj, (hcf j cA hjA).2.2.srcLen]
          simp [(hcf j cA hjA).2.2.len ψ]
        · intro j hj s hs l hsl
          rw [hlenFs] at hj
          obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
          rw [srcssOf_getD srcsF hj] at hs
          rw [hlenIds]
          exact (hcf j cA hjA).2.2.srcBnd s hs l hsl
        · exact hwl'
        · intro hw0 hl0 j hj bs hsp hidx
          rw [hlenFs] at hj
          obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
          have hCD := (hcf j cA hjA).2.2
          rw [kframe_frP hlenIs' hlenM', hFsjD j cA hjA] at hsp
          rw [kframe_frP hlenIs' hlenM', kframe_frameIdx hlenIs', hEsjD j cA hjA] at hidx
          rw [kframe_frameIdx hlenIs']
          rw [srcssOf_getD srcsF hj]
          have hsatC := (hiffψ j cA hjA ρp).mp hsatP
          have hlenB : bs.length = cA.2 := by rw [hsp.length_eq]; simp [hCD.len ψ]
          refine srcVals_of_fit (by rw [hCD.srcLen]; simp [hCD.len ψ])
            (hCD.srcProp (hlarge_of hl0) ψ (by rw [hw]; exact hw0) ρp hsatC) hsp ?_
          intro j' l hjl
          have hj'n : j' < cA.2 := by
            have := (List.getElem?_eq_some_iff.mp hjl).1; rwa [hCD.srcLen] at this
          have hEl := hCD.srcIdx j' l hjl ψ
          have hl : l < (esF j ψ).length := (List.getElem?_eq_some_iff.mp hEl).1
          have hisl : is[l]? = some (bs.getD j' pt) := by
            rw [← hidx]
            unfold idxValsAt
            rw [List.getElem?_map, hEl, Option.map_some, interp2_bvar,
              consList_apply_lt _ _ _ (by omega), hlenB,
              show cA.2 - 1 - (cA.2 - 1 - j') = j' from by omega, List.getD_eq_getElem?_getD,
              List.getElem?_eq_getElem (show j' < bs.length by omega), Option.getD_some,
              Option.getD_some]
          rw [List.getD_eq_getElem?_getD, hisl, Option.getD_some]

end Setlec.SetP
