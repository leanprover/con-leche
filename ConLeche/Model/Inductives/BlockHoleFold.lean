module

public import ConLeche.Model.Inductives.BlockLfpHoles
public import ConLeche.Model.Annot.LfpHoleOp
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.Inductives.FixAssemblyKit
import ConLeche.Semantics.Tower.BlockRecI
public section

/-!
# The constructors' clause by the override law (lane HOLE2, checkpoint (d) stage C)

Charter item 2: every stored `I p⃗` is the least fixed point of the
interpretation of its constructor types with holes at the block's
members.  The members' formers are consed with the block operator at the
HOLE chains (`blockTyG … (holeChains ψ)`, stage B).  This file proves the
fibre law the constructors' stage consumes (`blockCtorsLoop`'s `hfold`)
directly at those chains, with no field classification in the argument:

* **the leaf at the frame's parameters IS the hole value at the least
  tuple** (`blockTyG_holeVal`): both are λ-towers of graphs over the
  member's own parameter-and-index telescope; applied to the frame's
  parameters they are λ-towers over the index telescope read at the same
  frame, agreeing on every fitting index spine (the leaf's fold);
* so the frame whose member slots hold the LEAVES' values agrees with the
  hole frame at the holes (`blockLeaf_holeAgree`, `HoleAgree`), and a
  constructor's fields with holes read at it as its STORED fields read
  at the parameter frame (the override law, `interp_absField_override`:
  the stored field is the field with holes with each hole replaced by
  the member's former);
* the member's fibre at the least tuple is then the tagged union of its
  constructors' stored fields (`blockHoleFold`): the fixed-point
  equation (monotonicity and a closed tuple premises), the hole
  operator's fibre (`LfpDatum.holeOp_fibre`), the hole fit moved to the
  leaves' frame (`LfpDatum.hfits_iff_of_holeAgree`, M3), and the
  override law field by field.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Small readings -/

/-- **Fits along two lists of readings agree** when the readings agree at
every prefix. -/
theorem spineFit_map_congr_at {σ ρ : Nat → V} {Fs : List AnnotTerm} {G : Nat → AnnotTerm}
    (h : ∀ i, i < Fs.length → ∀ as : List V, as.length = i →
      interp V (consList as σ) (G i) = interp V (consList as ρ) (Fs.getD i default)) :
    ∀ (fs as : List V) (i : Nat), as.length = i →
      (SpineFit (consList as σ) (((List.range Fs.length).map G).drop i) fs ↔
        SpineFit (consList as ρ) (Fs.drop i) fs)
  | [], as, i, _ => by
    by_cases hi : i < Fs.length
    · rw [List.drop_eq_getElem_cons (by simpa using hi), List.drop_eq_getElem_cons hi]
      exact ⟨fun h => h.elim, fun h => h.elim⟩
    · rw [List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by omega)]
      exact ⟨fun _ => trivial, fun _ => trivial⟩
  | b :: bs, as, i, has => by
    by_cases hi : i < Fs.length
    · rw [List.drop_eq_getElem_cons (by simpa using hi), List.drop_eq_getElem_cons hi]
      simp only [List.getElem_map, List.getElem_range]
      have hFi : Fs[i] = Fs.getD i default := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl
      rw [hFi]
      show (b ∈ˢ interp V (consList as σ) (G i) ∧
          SpineFit (cons b (consList as σ)) (((List.range Fs.length).map G).drop (i + 1)) bs) ↔
        (b ∈ˢ interp V (consList as ρ) (Fs.getD i default) ∧
          SpineFit (cons b (consList as ρ)) (Fs.drop (i + 1)) bs)
      rw [h i hi as has, consList_snoc', consList_snoc']
      exact and_congr Iff.rfl (spineFit_map_congr_at h bs (as ++ [b]) (i + 1) (by simp [has]))
    · rw [List.drop_eq_nil_of_le (by simp; omega), List.drop_eq_nil_of_le (by omega)]
      exact ⟨fun h => h.elim, fun h => h.elim⟩

/-- `spineFit_map_congr_at` at the empty prefix. -/
theorem spineFit_map_congr {σ ρ : Nat → V} {Fs : List AnnotTerm} {G : Nat → AnnotTerm}
    (h : ∀ i, i < Fs.length → ∀ as : List V, as.length = i →
      interp V (consList as σ) (G i) = interp V (consList as ρ) (Fs.getD i default))
    (fs : List V) :
    SpineFit σ ((List.range Fs.length).map G) fs ↔ SpineFit ρ Fs fs := by
  have := spineFit_map_congr_at h fs [] 0 rfl
  simpa using this

/-! ## The leaf at the frame's parameters is the hole value -/

section Leaf

variable {d : BlockData V} {ψ : Name → Nat} {ρp : Nat → V}

/-- **A member's leaf on the hole chains, applied to the frame's
parameters and then to anything, is its hole value at the least tuple,
so applied** (see the module docstring). -/
theorem blockTyG_holeVal {c : Nat} (hc : c < d.k)
    (hlenPps : (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length)
    (hs : Sat V (d.toLfp.pars c ψ).reverse ρp)
    (hI : BlockIdxOk (V := V) d.k (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
    (hok : BlockChainsOkG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
      (d.toLfp.holeChains ψ)) (is : List V) :
    (frameIdx d.nP ρp ++ is).foldl app
        (interp V (shiftE d.nP 0 ρp) (blockTyG d.k (d.w ψ) (fun c => d.uM c ψ)
          (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ) (d.ppsM c ψ) c))
      = (frameIdx d.nP ρp ++ is).foldl app (d.toLfp.holeVal ψ ρp
          (blockFamG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
            (d.toLfp.holeChains ψ)) c) := by
  have hlenP : (d.toLfp.pars c ψ).length = d.nP := by
    show (((d.ppsM c ψ).take d.nP).map (·.2.2)).length = d.nP
    rw [List.length_map, List.length_take, hlenPps]; omega
  have hsplit : (d.ppsM c ψ).map (·.2.2) = d.toLfp.pars c ψ ++ d.IdsM c ψ := by
    show _ = ((d.ppsM c ψ).take d.nP).map (·.2.2) ++ ((d.ppsM c ψ).drop d.nP).map (·.2.2)
    rw [← List.map_append, List.take_append_drop]
  have hsp : SpineFit (shiftE d.nP 0 ρp) (d.toLfp.pars c ψ) (frameIdx d.nP ρp) := by
    have := spineFit_frameIdx_of_sat hs
    rwa [hlenP] at this
  have hfr : consList (frameIdx d.nP ρp) (shiftE d.nP 0 ρp) = ρp := consList_frameIdx _ ρp
  have hlenF : (frameIdx d.nP ρp).length = d.nP := by simp [frameIdx]
  unfold blockTyG
  rw [show ((d.ppsM c ψ).map fun dd => (d.w ψ + 1, dd.2.2))
      = ((d.ppsM c ψ).map (·.2.2)).map (d.w ψ + 1, ·) by rw [List.map_map]; rfl,
    interp_mkLamsAV_pos (Nat.succ_ne_zero _), hsplit, List.foldl_append,
    holeFam_foldl_prefix _ _ hsp, hfr]
  unfold LfpDatum.holeVal
  rw [List.foldl_append, hlenP, holeFam_foldl_prefix _ _ hsp, hfr]
  congr 1
  refine holeFam_congr fun is' his' => ?_
  have hlenI : is'.length = (d.IdsM c ψ).length := his'.length_eq
  have hsh : shiftE (d.IdsM c ψ).length 0 (consList is' ρp) = ρp := by
    rw [← hlenI]; exact shiftE_consList is' ρp
  have hfi : frameIdx (d.IdsM c ψ).length (consList is' ρp) = is' := by
    rw [← hlenI]; exact frameIdx_consList' is' ρp
  have hbase : BlockBaseG d.k (d.w ψ) (consList is' ρp) (fun c => d.uM c ψ)
      (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ) c := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hsh]; exact hI
    · rw [hsh]; exact hok
    · rw [hsh, hfi]; exact his'
  rw [consList_append, hfr, (blockLeafBodyG_facts hc hbase).1, hsh, hfi,
    List.drop_left' hlenF]
  rfl

/-- **The leaves' frame agrees with the hole frame at the holes**: the
parameter frame below, and member slots holding the leaves' values. -/
theorem blockLeaf_holeAgree {A : Nat → (Name → Nat) → AnnotTerm}
    (hA : ∀ c, c < d.k → A c ψ = blockTyG d.k (d.w ψ) (fun c => d.uM c ψ)
      (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ) (d.ppsM c ψ) c)
    (hlenPps : ∀ c, c < d.k → (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length)
    (hs : ∀ c, c < d.k → Sat V (d.toLfp.pars c ψ).reverse ρp)
    (hI : BlockIdxOk (V := V) d.k (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
    (hok : BlockChainsOkG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
      (d.toLfp.holeChains ψ)) :
    HoleAgree d.k d.nP 0
      (d.toLfp.frame ψ ρp (blockFamG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
        (d.toLfp.holeChains ψ)))
      (consList ((List.range d.k).map fun c => interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp) := by
  refine LfpDatum.holeAgree_frame (D := d.toLfp) (by simp [BlockData.toLfp]) fun c hc is => ?_
  simp only [List.getElem_map, List.getElem_range]
  rw [hA c hc]
  exact (blockTyG_holeVal hc (hlenPps c hc) (hs c hc) hI hok is).symm

end Leaf

/-! ## The override law, field by field -/

section Override

variable {env : Env} {mo : EnvModel V env} {d : BlockData V} {lps : List Name}

/-- **A field reading a member, as stored**: the member's former at the
parameter variables and the field's index readings, under the field's
own telescope (empty at a finitary field). -/
theorem BlockCtorRead.recField {c j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM c)[j]? = some cA) (hD : BlockCtorRead mo d lps c j cA) (ψ : Name → Nat)
    {i : Nat} (hi : i < cA.2) (hr : ((d.rss c).getD j []).getD i false = true) :
    ((d.Fss c ψ).getD j []).getD i default
      = mkPisAV (((d.tlss c ψ).getD j []).getD i [])
          (AnnotTerm.mkAppN (mo.acval (d.memberName (d.tgts c j i)) ψ)
            (paramBvarsAt d.nP (d.nP + i + (((d.tlss c ψ).getD j []).getD i []).length) ++
              ((d.Eiss c ψ).getD j []).getD i [])) := by
  unfold BlockCtorRead at hD
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hcj
  have hlenD : (d.dsF c j ψ).length = d.nP + cA.2 := hD.len ψ
  have hFssD : (d.Fss c ψ).getD j [] = ((d.dsF c j ψ).drop d.nP).map (·.2.2) :=
    fssOfR_fixCtorDataList_getD hcj
  have hTlD : (d.tlss c ψ).getD j [] = d.tssF c j ψ := tlssOfR_fixCtorDataList_getD hcj
  have hEiD : (d.Eiss c ψ).getD j [] = d.eissF c j ψ := eissOfR_fixCtorDataList_getD hcj
  have hksLen : (d.ksF c j).length = cA.2 := hD.ksLen
  have hkind : (d.ksF c j).getD i .ordinary = .recursive
      ∨ (d.ksF c j).getD i .ordinary = .reflexive := by
    have hrs : (d.rss c).getD j [] = rsOf (d.ksF c j) := rssOfK_getD hj
    rw [hrs] at hr
    exact (rsOf_getD_iff (by rw [hksLen]; exact hi)).mp hr
  rw [hFssD, drop_map_getD hlenD hi, hTlD, hEiD]
  rcases hkind with hk | hk
  · rw [hD.tssNone ψ i (by rw [hk]; intro hcon; cases hcon)]
    simp only [mkPisAV, List.length_nil, Nat.add_zero]
    exact hD.recEntry ψ i hk hi
  · exact hD.reflEntry ψ i hk hi

/-- **The override law**: a constructor's field with holes, read below
hole values `hs` where the field's target member's slot holds its
former's value, is the stored field read at the parameter frame. -/
theorem interp_absField_override {c j : Nat} {cA : ConstantVal × Nat}
    (hcj : (d.ctorsM c)[j]? = some cA) (hD : BlockCtorRead mo d lps c j cA) {ψ : Name → Nat}
    {i : Nat} (hi : i < cA.2) (htgt : d.tgts c j i < d.k)
    {hs : List V} (hhs : hs.length = d.k) (ρ : Nat → V)
    (hval : ∀ σ : Nat → V,
      interp V σ (mo.acval (d.memberName (d.tgts c j i)) ψ) = hs.getD (d.tgts c j i) pt)
    {as : List V} (has : as.length = i) :
    interp V (consList as (consList hs ρ)) (d.absField ψ c j i)
      = interp V (consList as ρ) (((d.Fss c ψ).getD j []).getD i default) := by
  by_cases hr : ((d.rss c).getD j []).getD i false = true
  case neg =>
    exact interp_absField_ord_at (by simpa using hr) hhs has ρ
  have hD' := hD
  unfold BlockCtorRead at hD'
  have hTlD : (d.tlss c ψ).getD j [] = d.tssF c j ψ := tlssOfR_fixCtorDataList_getD hcj
  have hbits : ∀ dd ∈ ((d.tlss c ψ).getD j []).getD i [], (dd.2.1 = 0 ↔ d.w ψ = 0) := by
    rw [hTlD]; exact fun dd hdd => hD'.tssBits ψ i dd hdd
  rw [BlockCtorRead.recField hcj hD ψ hi hr]
  unfold BlockData.absField
  rw [if_pos hr]
  generalize htl : ((d.tlss c ψ).getD j []).getD i [] = tl at hbits ⊢
  generalize hEis : ((d.Eiss c ψ).getD j []).getD i [] = Eis
  generalize ht : d.tgts c j i = t at htgt hval ⊢
  let B : List V → V := fun ts =>
    ((List.range d.nP).reverse.map ρ ++ Eis.map (interp V (consList (as ++ ts) ρ))).foldl app
      (hs.getD t pt)
  rw [show BlockData.liftTeleK d.k i tl = BlockData.liftTeleK hs.length as.length tl by
    rw [hhs, has]]
  rw [interp_liftTeleK_piTele (B := B) hs ρ tl as [] hbits fun ts hts => ?_,
    ConLeche.Semantics.interp_mkPisAV_piTele (v := d.w ψ) (B := B) (acc := []) hbits
      fun ts hts => ?_]
  · -- the stored field's body: the former at the parameters and indices
    have hL : (as ++ ts).length = i + tl.length := by
      rw [List.length_append, has, hts.length_eq, List.length_map]
    rw [← consList_append, interp_mkAppN, foldl_app_map, List.map_append,
      show d.nP + i + tl.length = d.nP + (as ++ ts).length by rw [hL]; omega,
      map_paramBvarsAt_interp (fun j => consList_apply_add (as ++ ts) ρ j), hval]
    rfl
  · -- the field with holes' body: the hole at the parameters and indices
    have hL : (as ++ ts).length = i + tl.length := by
      rw [List.length_append, has, hts.length_eq, List.length_map]
    rw [← consList_append, interp_mkAppN, foldl_app_map, List.map_append,
      show d.nP + d.k + i + tl.length = d.nP + (d.k + (as ++ ts).length) by rw [hL]; omega,
      map_paramBvarsAt_interp (fun j => by
        rw [show j + (d.k + (as ++ ts).length) = (j + hs.length) + (as ++ ts).length by
          rw [hhs]; omega, consList_apply_add, consList_apply_add])]
    have hbv : interp V (consList (as ++ ts) (consList hs ρ)) (.bvar (i + tl.length + (d.k - 1 - t)))
        = hs.getD t pt := by
      rw [interp_bvar, show i + tl.length + (d.k - 1 - t) = (d.k - 1 - t) + (as ++ ts).length by
        rw [hL]; omega, consList_apply_add, consList_getD_of_lt _ _ _ (by rw [hhs]; omega), hhs,
        show d.k - 1 - (d.k - 1 - t) = t by omega]
    have heis : Eis.map (interp V (consList (as ++ ts) (consList hs ρ)) ∘
          (·.liftN d.k (i + tl.length)))
        = Eis.map (interp V (consList (as ++ ts) ρ)) := by
      refine List.map_congr_left fun E _ => ?_
      simp only [Function.comp_def]
      rw [show d.k = hs.length from hhs.symm, ← hL]
      exact interp_liftN_consList2 _ _ _ _
    rw [hbv, List.map_map, heis]
    rfl

end Override

/-! ## The member's fibre at the least tuple -/

section Fold

variable {env : Env} {mo : EnvModel V env} {d : BlockData V} {lps : List Name}

/-- A list of readings is a spine exactly when it agrees with it
pointwise. -/
theorem map_eq_iff_getD {σ : Nat → V} {Es : List AnnotTerm} {is : List V}
    (hlen : is.length = Es.length) :
    Es.map (interp V σ) = is ↔ ∀ l, l < Es.length → interp V σ (Es.getD l default) = is.getD l pt := by
  constructor
  · rintro rfl l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem hl]
    rfl
  · intro h
    refine List.ext_getElem (by rw [List.length_map, hlen]) fun l h1 h2 => ?_
    have hl : l < Es.length := by simpa using h1
    have := h l hl
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2] at this
    simpa using this

/-- **The hole fit at the least tuple IS the stored fit** (the override
law, fibre by fibre): at the least tuple of the hole operator, a spine
hole-fits member `m`'s constructor `j` at the index tuple of a fitting
index spine exactly when it fits the constructor's STORED field readings
at the parameter frame and the stored result index readings are that
spine.  The hole fit moves to the leaves' frame (`hfits_iff_of_holeAgree`,
M3) and there each field with holes reads as the stored field
(`hover`). -/
theorem blockHFits_lfp_iff (hH : BlockHoleFacts mo d lps) (hinst : d.nInst = 0)
    {A : Nat → (Name → Nat) → AnnotTerm} {ψ : Name → Nat}
    (hA : ∀ c, c < d.k → A c ψ = blockTyG d.k (d.w ψ) (fun c => d.uM c ψ)
      (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ) (d.ppsM c ψ) c)
    {ρp : Nat → V} (hs : Sat V (d.params ψ).reverse ρp)
    (hlenPps : ∀ c, c < d.k → (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length)
    (hI : BlockIdxOk (V := V) d.k (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
    (hok : BlockChainsOkG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
      (d.toLfp.holeChains ψ))
    {m : Nat} (hm : m < d.k)
    (hover : ∀ j, j < (d.ctorsM m).length → ∀ i, i < ((d.Fss m ψ).getD j []).length →
      ∀ as : List V, as.length = i →
      interp V (consList as (consList ((List.range d.k).map fun c =>
          interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp)) (d.absField ψ m j i)
        = interp V (consList as ρp) (((d.Fss m ψ).getD j []).getD i default))
    (t : V) (j : Nat) (fs : List V) :
    d.toLfp.HFits ψ ρp (blockFamG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
        (d.toLfp.holeChains ψ)) t m j fs ↔ d.StoredFit ψ ρp t m j fs := by
  have hNk : d.N = d.k := by simp [BlockData.N, hinst]
  have hmN : m < d.N := by rw [hNk]; exact hm
  have hsP : ∀ c, c < d.k → Sat V (d.toLfp.pars c ψ).reverse ρp :=
    fun c hc => hH.parsSat ψ c hc ρp hs
  have happ : ∀ j, j < d.toLfp.nctors m → d.toLfp.HolesApplied ψ m j :=
    fun j hj => blockHolesApplied hH ψ hmN hj
  have hag : HoleAgree d.toLfp.k (d.toLfp.params ψ).length 0
      (d.toLfp.frame ψ ρp (blockFamG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
        (d.toLfp.holeChains ψ)))
      (consList ((List.range d.k).map fun c => interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp) := by
    show HoleAgree d.k (d.params ψ).length 0 _ _
    rw [hH.lenP ψ]
    exact blockLeaf_holeAgree (fun c hc => hA c hc) hlenPps hsP hI hok
  have hlenHs : ((List.range d.k).map fun c => interp V (shiftE d.nP 0 ρp) (A c ψ)).length = d.k := by
    simp
  by_cases hj : j < (d.ctorsM m).length
  case neg =>
    exact ⟨fun h => absurd h.1 hj, fun h => absurd h.1 hj⟩
  rw [LfpDatum.hfits_iff_of_holeAgree (happ j hj) hag]
  have hEsLen : ((d.Ess m ψ).getD j []).length = (d.IdsM m ψ).length := hH.lenE ψ m hmN j hj
  -- the fields: the override law, at every prefix
  have hsp : SpineFit (consList ((List.range d.k).map fun c =>
        interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp) (d.toLfp.fields ψ m j) fs ↔
      SpineFit ρp ((d.Fss m ψ).getD j []) fs :=
    spineFit_map_congr (fun i hi as has => hover j hj i hi as has) fs
  -- the result index readings, lifted over the holes and the fields
  have hgetE : ∀ l, l < ((d.Ess m ψ).getD j []).length →
      (d.absE ψ m j)[l]? = some ((((d.Ess m ψ).getD j []).getD l default).liftN d.k
        ((d.Fss m ψ).getD j []).length) := by
    intro l hl
    have hget : ((d.Ess m ψ).getD j [])[l]? = some (((d.Ess m ψ).getD j []).getD l default) := by
      rw [List.getD_eq_getElem?_getD (l := (d.Ess m ψ).getD j []), List.getElem?_eq_getElem hl]; rfl
    show (((d.Ess m ψ).getD j []).map (·.liftN d.k ((d.Fss m ψ).getD j []).length))[l]? = _
    rw [List.getElem?_map, hget]
    rfl
  have hliftE : ∀ fs' : List V, fs'.length = ((d.Fss m ψ).getD j []).length → ∀ E : AnnotTerm,
      interp V (consList fs' (consList ((List.range d.k).map fun c =>
          interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp)) (E.liftN d.k ((d.Fss m ψ).getD j []).length)
        = interp V (consList fs' ρp) E := by
    intro fs' hfs' E
    have := interp_liftN_consList2 E fs' ((List.range d.k).map fun c =>
      interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp
    rwa [hlenHs, hfs'] at this
  constructor
  · rintro ⟨-, hf, hidx⟩
    have hf' := hsp.mp hf
    have hlenfs : fs.length = ((d.Fss m ψ).getD j []).length := hf'.length_eq
    refine ⟨hj, hf', fun l hlI => ?_⟩
    have hl : l < ((d.Ess m ψ).getD j []).length := by rw [hEsLen]; exact hlI
    obtain ⟨e, he, hev⟩ := hidx l hlI
    obtain rfl := Option.some.inj (he.symm.trans (hgetE l hl))
    rw [hliftE fs hlenfs] at hev
    exact hev
  · rintro ⟨-, hf, hall⟩
    have hlenfs : fs.length = ((d.Fss m ψ).getD j []).length := hf.length_eq
    refine ⟨hj, hsp.mpr hf, fun l hl => ?_⟩
    have hl' : l < ((d.Ess m ψ).getD j []).length := by rw [hEsLen]; exact hl
    refine ⟨_, hgetE l hl', ?_⟩
    rw [hliftE fs hlenfs]
    exact hall l hl

/-- **THE MEMBER'S FIBRE AT THE LEAST TUPLE, by the override law** (see
the module docstring): a member's leaf on the hole chains, at the
frame's parameters and a fitting index spine, is the tagged union of
the member's constructors' STORED fields at that spine — given the hole
operator's monotonicity and a closed tuple, and the stored fields'
agreement with the fields with holes at the leaves' frame
(`interp_absField_override` supplies it at a model storing the
formers). -/
theorem blockHoleFold (hH : BlockHoleFacts mo d lps) (hinst : d.nInst = 0)
    {A : Nat → (Name → Nat) → AnnotTerm} {ψ : Name → Nat}
    (hA : ∀ c, c < d.k → A c ψ = blockTyG d.k (d.w ψ) (fun c => d.uM c ψ)
      (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ) (d.ppsM c ψ) c)
    {ρp : Nat → V} (hs : Sat V (d.params ψ).reverse ρp)
    (hlenPps : ∀ c, c < d.k → (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length)
    (hI : BlockIdxOk (V := V) d.k (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
    (hok : BlockChainsOkG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
      (d.toLfp.holeChains ψ))
    (hmono : MonoTuple (d.w ψ) d.k (blockIdx (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
      (blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ)))
    (hclosed : ∃ L, IsClosedTuple (d.w ψ) d.k (blockIdx (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
      (blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ)) L)
    {m : Nat} (hm : m < d.k)
    (hover : ∀ j, j < (d.ctorsM m).length → ∀ i, i < ((d.Fss m ψ).getD j []).length →
      ∀ as : List V, as.length = i →
      interp V (consList as (consList ((List.range d.k).map fun c =>
          interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp)) (d.absField ψ m j i)
        = interp V (consList as ρp) (((d.Fss m ψ).getD j []).getD i default))
    {is : List V} (his : SpineFit ρp (d.IdsM m ψ) is) :
    (frameIdx d.nP ρp ++ is).foldl app (interp V (shiftE d.nP 0 ρp) (A m ψ))
      = sumSet (d.w ψ) (sumFibre (d.w ψ) (consList is ρp)
          (rChains (d.IdsM m ψ).length (d.IdsM m ψ).length (d.Fss m ψ) (d.Ess m ψ))) := by
  classical
  have hNk : d.N = d.k := by simp [BlockData.N, hinst]
  have hmN : m < d.N := by rw [hNk]; exact hm
  have hsP : ∀ c, c < d.k → Sat V (d.toLfp.pars c ψ).reverse ρp :=
    fun c hc => hH.parsSat ψ c hc ρp hs
  have hlenC : (d.Fss m ψ).length = (d.ctorsM m).length := by
    show (fssOfR _ _).length = _
    rw [fssOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hlenCE : (d.Ess m ψ).length = (d.ctorsM m).length := by
    show (essOfR _).length = _
    rw [essOfR_length]
    exact fixCtorDataList_length _ _ _ _ _ _ _ _
  have hislen : is.length = (d.IdsM m ψ).length := his.length_eq
  -- the leaf at the parameters and the index spine: the least tuple's component
  have ht : tupW (d.uM m ψ) is ∈ˢ idxSet (d.uM m ψ) ρp (d.IdsM m ψ) := tupW_mem his
  have hv := LfpDatum.holeVal_app (D := d.toLfp) (hsP m hm) his
    (X := blockFamG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
      (d.toLfp.holeChains ψ))
  rw [hH.parsLen ψ m hm] at hv
  rw [hA m hm, blockTyG_holeVal hm (hlenPps m hm) (hsP m hm) hI hok is, hv]
  -- the fixed point: the operator's fibre at the least tuple
  have hfix : app (blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
        (d.toLfp.holeChains ψ) (blockFamG d.k (d.w ψ) ρp (fun c => d.uM c ψ)
          (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ)) m) (tupW (d.uM m ψ) is)
      = app (blockFamG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
          (d.toLfp.holeChains ψ) m) (tupW (d.uM m ψ) is) :=
    app_lfpTuple_eq hclosed hmono (blockPhi_maps_of hok) hm ht
  have hop : ∀ X, blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
      (d.toLfp.holeChains ψ) X = d.toLfp.holeOp ψ ρp X := by
    intro X
    unfold LfpDatum.holeOp
    rw [show d.toLfp.N = d.k from hNk]
    rfl
  show app _ (tupW (d.uM m ψ) is) = _
  rw [← hfix, hop]
  -- the two unions, member by member
  have hHT : d.toLfp.HoleTmOk ψ ρp := fun c hc =>
    ⟨⟨(hH.parsLen ψ c hc).trans (hH.lenP ψ).symm, hsP c hc⟩, fun _ => (hI c hc).2⟩
  have hkN : d.toLfp.k ≤ d.toLfp.N := by show d.k ≤ d.N; omega
  have happ : ∀ j, j < d.toLfp.nctors m → d.toLfp.HolesApplied ψ m j :=
    fun j hj => blockHolesApplied hH ψ hmN hj
  have hres : ∀ j, j < d.toLfp.nctors m →
      (d.toLfp.resIdx ψ m j).length = (d.toLfp.ids m ψ).length := by
    intro j hj
    show (d.absE ψ m j).length = (d.IdsM m ψ).length
    simp only [BlockData.absE, List.length_map]
    exact hH.lenE ψ m hmN j hj
  have hag : HoleAgree d.toLfp.k (d.toLfp.params ψ).length 0
      (d.toLfp.frame ψ ρp (blockFamG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
        (d.toLfp.holeChains ψ)))
      (consList ((List.range d.k).map fun c => interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp) := by
    show HoleAgree d.k (d.params ψ).length 0 _ _
    rw [hH.lenP ψ]
    exact blockLeaf_holeAgree (fun c hc => hA c hc) hlenPps hsP hI hok
  have hlenHs : ((List.range d.k).map fun c => interp V (shiftE d.nP 0 ρp) (A c ψ)).length = d.k := by
    simp
  -- the restricted chains, as terminated chains
  have hrc : rChains (d.IdsM m ψ).length (d.IdsM m ψ).length (d.Fss m ψ) (d.Ess m ψ)
      = (List.range ((d.Fss m ψ).map (liftFields (d.IdsM m ψ).length 0)).length).map fun j =>
          ((d.Fss m ψ).map (liftFields (d.IdsM m ψ).length 0)).getD j [] ++
            [idxEqAV (((List.range (d.Fss m ψ).length).map fun j =>
              idxEqsAt (d.IdsM m ψ).length (d.IdsM m ψ).length ((d.Fss m ψ).getD j []).length
                ((d.Ess m ψ).getD j [])).getD j [])] := by
    refine List.ext_getElem? fun j => ?_
    rw [rChains_getElem?, List.getElem?_map]
    by_cases hj : j < (d.Fss m ψ).length
    · have hjE : j < (d.Ess m ψ).length := by rw [hlenCE, ← hlenC]; exact hj
      rw [List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjE,
        List.getElem?_range (by simpa using hj)]
      simp only [Option.map_some, rChain, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hjE, List.getElem?_range hj,
        Option.map_some, Option.getD_some]
    · rw [List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (show (List.range _).length ≤ j by simp; omega)]
      rfl
  apply SetTheory.ext
  intro x
  rw [LfpDatum.holeOp_fibre hHT hkN _ happ hres ht x, hrc, sumSet_termChs_mem_iff]
  simp only [List.length_map]
  refine exists_congr fun j => exists_congr fun fs => ?_
  by_cases hj : j < (d.ctorsM m).length
  case neg =>
    constructor
    · rintro ⟨hf, -⟩; exact absurd hf.1 hj
    · rintro ⟨hj', -⟩; exact absurd (hlenC ▸ hj') hj
  have hjF : j < (d.Fss m ψ).length := by rw [hlenC]; exact hj
  have hFs : ((d.Fss m ψ).map (liftFields (d.IdsM m ψ).length 0)).getD j []
      = liftFields (d.IdsM m ψ).length 0 ((d.Fss m ψ).getD j []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hjF]
    rfl
  have hEq : ((List.range (d.Fss m ψ).length).map fun j =>
        idxEqsAt (d.IdsM m ψ).length (d.IdsM m ψ).length ((d.Fss m ψ).getD j []).length
          ((d.Ess m ψ).getD j [])).getD j []
      = idxEqsAt (d.IdsM m ψ).length (d.IdsM m ψ).length ((d.Fss m ψ).getD j []).length
          ((d.Ess m ψ).getD j []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hjF]
    rfl
  rw [hFs, hEq, LfpDatum.hfits_iff_of_holeAgree (happ j hj) hag]
  have hEsLen : ((d.Ess m ψ).getD j []).length = (d.IdsM m ψ).length := hH.lenE ψ m hmN j hj
  -- the fields: the override law, at every prefix
  have hsp : SpineFit (consList ((List.range d.k).map fun c =>
        interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp) (d.toLfp.fields ψ m j) fs ↔
      SpineFit ρp ((d.Fss m ψ).getD j []) fs :=
    spineFit_map_congr (fun i hi as has => hover j hj i hi as has) fs
  have hspL : SpineFit (consList is ρp) (liftFields (d.IdsM m ψ).length 0 ((d.Fss m ψ).getD j [])) fs ↔
      SpineFit ρp ((d.Fss m ψ).getD j []) fs := by
    rw [spineFit_liftFields, ← hislen, shiftE_consList]
  -- the result index readings, lifted over the holes and the fields
  have hgetE : ∀ l, l < ((d.Ess m ψ).getD j []).length →
      (d.absE ψ m j)[l]? = some ((((d.Ess m ψ).getD j []).getD l default).liftN d.k
        ((d.Fss m ψ).getD j []).length) := by
    intro l hl
    have hget : ((d.Ess m ψ).getD j [])[l]? = some (((d.Ess m ψ).getD j []).getD l default) := by
      rw [List.getD_eq_getElem?_getD (l := (d.Ess m ψ).getD j []), List.getElem?_eq_getElem hl]; rfl
    show (((d.Ess m ψ).getD j []).map (·.liftN d.k ((d.Fss m ψ).getD j []).length))[l]? = _
    rw [List.getElem?_map, hget]
    rfl
  have hliftE : ∀ fs' : List V, fs'.length = ((d.Fss m ψ).getD j []).length → ∀ E : AnnotTerm,
      interp V (consList fs' (consList ((List.range d.k).map fun c =>
          interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp)) (E.liftN d.k ((d.Fss m ψ).getD j []).length)
        = interp V (consList fs' ρp) E := by
    intro fs' hfs' E
    have := interp_liftN_consList2 E fs' ((List.range d.k).map fun c =>
      interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp
    rwa [hlenHs, hfs'] at this
  constructor
  · rintro ⟨⟨-, hf, hidx⟩, rfl⟩
    have hf' := hsp.mp hf
    have hlenfs : fs.length = ((d.Fss m ψ).getD j []).length := hf'.length_eq
    refine ⟨hjF, hspL.mpr hf', ?_, rfl⟩
    rw [EqAll_idxEqsAt hEsLen hlenfs, ← hislen, shiftE_consList, frameIdx_consList']
    refine (map_eq_iff_getD (by rw [hislen, hEsLen])).mpr fun l hl => ?_
    have hlI : l < (d.IdsM m ψ).length := by rw [hEsLen] at hl; exact hl
    obtain ⟨e, he, hev⟩ := hidx l hlI
    obtain rfl := Option.some.inj (he.symm.trans (hgetE l hl))
    rw [hliftE fs hlenfs, projS_tupW (hI m hm) his hlI] at hev
    exact hev
  · rintro ⟨-, hf, hall, rfl⟩
    have hf' := hspL.mp hf
    have hlenfs : fs.length = ((d.Fss m ψ).getD j []).length := hf'.length_eq
    refine ⟨⟨hj, hsp.mpr hf', fun l hl => ?_⟩, rfl⟩
    rw [EqAll_idxEqsAt hEsLen hlenfs, ← hislen, shiftE_consList, frameIdx_consList'] at hall
    have hl' : l < ((d.Ess m ψ).getD j []).length := by rw [hEsLen]; exact hl
    refine ⟨_, hgetE l hl', ?_⟩
    rw [hliftE fs hlenfs, projS_tupW (hI m hm) his hl]
    exact (map_eq_iff_getD (by rw [hislen, hEsLen])).mp hall l hl'

/-- **`blockHoleFold` at an index-free member, along a whole parameter
spine**: the leaf applied to a spine fitting its telescope is the tagged
union of the member's constructors' stored fields at the extended frame
(the capability laws' and the table stage's fold). -/
theorem blockHoleFold_params (hH : BlockHoleFacts mo d lps) (hinst : d.nInst = 0)
    {A : Nat → (Name → Nat) → AnnotTerm} {ψ : Name → Nat}
    (hA : ∀ c, c < d.k → A c ψ = blockTyG d.k (d.w ψ) (fun c => d.uM c ψ)
      (fun c => d.IdsM c ψ) (d.toLfp.holeChains ψ) (d.ppsM c ψ) c)
    (hlenPps : ∀ c, c < d.k → (d.ppsM c ψ).length = d.nP + (d.IdsM c ψ).length)
    {m : Nat} (hm : m < d.k) (hIds0 : d.IdsM m ψ = [])
    (hI : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      BlockIdxOk (V := V) d.k (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
    (hok : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      BlockChainsOkG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
        (d.toLfp.holeChains ψ))
    (hfun : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      MonoTuple (d.w ψ) d.k (blockIdx (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
        (blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
          (d.toLfp.holeChains ψ)) ∧
      ∃ L, IsClosedTuple (d.w ψ) d.k (blockIdx (fun c => d.uM c ψ) ρp (fun c => d.IdsM c ψ))
        (blockPhiG d.k (d.w ψ) ρp (fun c => d.uM c ψ) (fun c => d.IdsM c ψ)
          (d.toLfp.holeChains ψ)) L)
    (hover : ∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
      ∀ j, j < (d.ctorsM m).length → ∀ i, i < ((d.Fss m ψ).getD j []).length →
      ∀ as : List V, as.length = i →
      interp V (consList as (consList ((List.range d.k).map fun c =>
          interp V (shiftE d.nP 0 ρp) (A c ψ)) ρp)) (d.absField ψ m j i)
        = interp V (consList as ρp) (((d.Fss m ψ).getD j []).getD i default))
    {ρ : Nat → V} {ts : List V} (hsp : SpineFit ρ ((d.ppsM m ψ).map (·.2.2)) ts) :
    ts.foldl app (interp V ρ (A m ψ))
      = sumSet (d.w ψ) (sumFibre (d.w ψ) (consList ts ρ)
          (rChains 0 0 (d.Fss m ψ) (d.Ess m ψ))) := by
  have hlenP : (d.ppsM m ψ).length = d.nP := by rw [hlenPps m hm, hIds0]; rfl
  have hlenT : ts.length = d.nP := by rw [hsp.length_eq, List.length_map, hlenP]
  have hpars : d.toLfp.pars m ψ = (d.ppsM m ψ).map (·.2.2) := by
    show ((d.ppsM m ψ).take d.nP).map (·.2.2) = _
    rw [List.take_of_length_le (Nat.le_of_eq hlenP)]
  have hsP : Sat V (d.toLfp.pars m ψ).reverse (consList ts ρ) := by
    rw [hpars]; simpa using sat_of_spineFit (Sat_nil V ρ) hsp
  have hs : Sat V (d.params ψ).reverse (consList ts ρ) := hH.parsSatInv ψ m hm _ hsP
  have hfl := blockHoleFold hH hinst hA hs hlenPps (hI _ hs) (hok _ hs) (hfun _ hs).1 (hfun _ hs).2
    hm (hover _ hs) (is := []) (by rw [hIds0]; trivial)
  have hts : frameIdx d.nP (consList ts ρ) = ts := by rw [← hlenT]; exact frameIdx_consList' ts ρ
  have hsh : shiftE d.nP 0 (consList ts ρ) = ρ := by rw [← hlenT]; exact shiftE_consList ts ρ
  rw [List.append_nil, hts, hsh, consList_nil, hIds0] at hfl
  exact hfl

end Fold

end ConLeche.Model
