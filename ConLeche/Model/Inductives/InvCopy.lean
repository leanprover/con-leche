module

public import ConLeche.Model.Inductives.CopyCtorRun
import ConLeche.Verify.Inductives.NestedCtors
import ConLeche.Verify.Inductives.NestedLeaves

public section

/-!
# The copies' side of ψ⁻¹, from the constructor record (task #279 M-C′, DESIGN §M.32)

`InvFold.lean` closes ψ⁻¹ — the fold of the SCRATCH block's recursors at
one choice of motives and minors — under `InvSetup`, whose copy-side
fields `CopyPins.lean` discharges from three records (`PinRead`,
`CopyIdxRead`, `CopyCtorRead`).  The first two are read off the run
(`CopyReads.lean`, `PsiRun.lean`: `CopyData.Ok`); the third is derived
HERE from the constructor-side record `CopyCtorAsRead` (the same record
ψ consumes, DESIGN §M.31) together with the container's representation:

* **the choice** — `invL`/`invPinsT` (a real member keeps its own leaf
  at the parameter variables; a copy's leaf is its container member's
  at the pin's assignment, its pins the pin's readings), `invUseIh` (a
  copy constructor's fields recursive into a COPY use their
  hypothesis; every other field is passed as-is), and the heads
  (`invHead`: a real constructor at the parameter variables, a copy's
  the CONTAINER constructor at the pin's readings);
* **`copyCtorRead_of_asRead`** — `CopyCtorRead` at a copy's constructor
  from the record: the tower is the container constructor's residual
  instantiated at the pin (`instSeq_mkPisAV`), the head is in it by
  `mem_type` along the fitting pin, and field by field the target
  form is the container's substituted domain — `ord` where no
  hypothesis is used; at a container-recursive field (`kindR`) the
  hypothesis's domain is the container's recursive entry with the
  group-mate's leaf, the index readings' fit transferred through the
  group-mate's `CopyIdxRead`; at a transport (`kindT`) the record's
  own equation with the target's leaf, the fit through the target's
  `CopyIdxRead` (`transport_fits`);
* **the run level** — `invSetup_of_run`: `InvSetup` for the scratch
  block from `DeclNestedRun` under `ContainersRep` and `CopyCtorsRead`
  (the same two premises ψ has), at every level assignment sending the
  block's elimination universe to its carrier's rank and every
  parameter frame; hence ψ⁻¹ TYPED (`InvSetup.fold_mem`) and FIRING
  (`InvSetup.fold_iota`) end to end.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `instSeq` bookkeeping -/

omit [SetTheory V] in
/-- The depth of an `instSeq` matters only at a non-empty spine. -/
theorem instSeq_congr_depth {ws : List AnnotTerm} {t t' : Nat} (h : ws ≠ [] → t = t')
    (e : AnnotTerm) :
    ConLeche.Model.AnnotTerm.instSeq ws t e = ConLeche.Model.AnnotTerm.instSeq ws t' e := by
  cases ws with
  | nil => rfl
  | cons w ws => rw [h (List.cons_ne_nil w ws)]

omit [SetTheory V] in
/-- `instSeqDoms` commutes with a prefix. -/
theorem instSeqDoms_take (ws : List AnnotTerm) :
    ∀ (t : Nat) (Γ : List (Nat × Nat × AnnotTerm)) (i : Nat),
      (instSeqDoms ws t Γ).take i = instSeqDoms ws t (Γ.take i)
  | _, [], _ => by simp [instSeqDoms]
  | _, _ :: _, 0 => by simp [instSeqDoms]
  | t, (u, v, A) :: Γ, i + 1 => by
    simp only [instSeqDoms, List.take_succ_cons]
    rw [instSeqDoms_take ws (t + 1) Γ i]

/-- The family at a closed leaf and pins, read at index values over the
base frame. -/
theorem interp_famAppAV_pins {L : AnnotTerm} (hL : Term.bvarsBelow 0 L.erase)
    (pins : List AnnotTerm) (nP : Nat) {is : List V} {σ : Nat → V} {nIdx : Nat}
    (his : is.length = nIdx) :
    interp V (consList is σ) (famAppAV L pins nP (nP + nIdx) nIdx)
      = (pins.map (interp V σ) ++ is).foldl SetTheory.app (interp V σ L) := by
  subst his
  have h := interp_famAppAV_at (L := L) (fun σ₁ σ₂ => interp_closed (V := V) hL σ₁ σ₂) pins nP
    (extra := []) (is := is) (σ := σ)
  simp only [consList_nil, List.length_nil, Nat.add_zero] at h
  exact h

/-! ## The choice -/

namespace IndRepData

variable (d : IndRepData V)

/-- **ψ⁻¹'s leaves**: a real member's own leaf; a copy's (aux member
`k₀ + j`) its container member's leaf at the pin's assignment. -/
@[expose] def invL (m : EnvModel V env) (ψ : Name → Nat) (k₀ : Nat) (cd : Nat → CopyData V) :
    Nat → AnnotTerm :=
  fun t => if t < k₀ then m.acval (d.memberName t) ψ
    else m.acval ((cd (t - k₀)).dJ.memberName (cd (t - k₀)).mm) (cd (t - k₀)).ψ'

/-- **ψ⁻¹'s pins**: the parameter variables at a real member, the pin's
readings at a copy. -/
@[expose] def invPinsT (k₀ : Nat) (cd : Nat → CopyData V) : Nat → List AnnotTerm :=
  fun t => if t < k₀ then paramBvarsAt d.nP d.nP else (cd (t - k₀)).DsA

/-- **Which fields use their hypothesis**: a copy constructor's fields
recursive into a copy (a container-recursive field, whose target is the
group-mate's copy, or a transport). -/
@[expose] def invUseIh (k₀ : Nat) : Nat → Nat → Bool :=
  fun J i => decide (k₀ ≤ d.mems J ∧ i ∈ ConLeche.recIdxOf (d.ksR J) ∧ k₀ ≤ d.tgtsR J i)

omit [SetTheory V] in
theorem invUseIh_mem {k₀ J i : Nat} (h : d.invUseIh k₀ J i = true) :
    i ∈ ConLeche.recIdxOf (d.ksR J) := by
  unfold invUseIh at h
  exact (of_decide_eq_true h).2.1

omit [SetTheory V] in
theorem invUseIh_real {k₀ J : Nat} (h : d.mems J < k₀) : ∀ i, d.invUseIh k₀ J i = false := by
  intro i
  unfold invUseIh
  exact decide_eq_false fun h' => absurd h'.1 (Nat.not_le.mpr h)

theorem invL_real {m : EnvModel V env} {ψ : Name → Nat} {k₀ : Nat} {cd : Nat → CopyData V}
    {t : Nat} (h : t < k₀) : d.invL m ψ k₀ cd t = m.acval (d.memberName t) ψ := by
  unfold invL; rw [if_pos h]

omit [SetTheory V] in
theorem invPinsT_real {k₀ : Nat} {cd : Nat → CopyData V} {t : Nat} (h : t < k₀) :
    d.invPinsT k₀ cd t = paramBvarsAt d.nP d.nP := by
  unfold invPinsT; rw [if_pos h]

theorem invL_copy {m : EnvModel V env} {ψ : Name → Nat} {k₀ : Nat} {cd : Nat → CopyData V}
    (j : Nat) :
    d.invL m ψ k₀ cd (k₀ + j) = m.acval ((cd j).dJ.memberName (cd j).mm) (cd j).ψ' := by
  unfold invL
  rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)), Nat.add_sub_cancel_left]

omit [SetTheory V] in
theorem invPinsT_copy {k₀ : Nat} {cd : Nat → CopyData V} (j : Nat) :
    d.invPinsT k₀ cd (k₀ + j) = (cd j).DsA := by
  unfold invPinsT
  rw [if_neg (Nat.not_lt.mpr (Nat.le_add_right _ _)), Nat.add_sub_cancel_left]

/-! ## The copy's constructor, read through the container's -/

set_option maxHeartbeats 6400000 in
/-- **`CopyCtorRead` at a copy's constructor, from the record**: the
tower is the container constructor's residual instantiated at the pin's
readings (`instSeq_mkPisAV`); the head — the container's constructor at
the readings — is graded and in it (`mem_type` along the pin, which fits
the constructor's parameter domains through `paramsIff`); field by
field, at a prefix fitting the instantiated earlier domains (the
container's at the pin, `spineFit_instSeqDoms_iff`), the target form is
the instantiated domain — at a field passing its value (`invUseIh`
false) the record's `ord`; at a container-recursive field the
container's recursive entry (`recRefl_entry`) under the substitution
against the group-mate copy's target (`kindR`; the index readings fit
the group-mate's telescope through its `CopyIdxRead`,
`idxFit_of_entry`); at a transport the record's own equation against the
target copy's target (`kindT`; `transport_fits` for the index readings'
fit); and the body is the copy's target at the container constructor's
index readings (`es`, the fit from the container's `CtorFieldFacts`). -/
theorem copyCtorRead_of_asRead {μ : CheckMode} (mp : EnvModelM V μ env) {lpsT : List Name}
    {ψ : Name → Nat} {ρ : Nat → V} {ps : List AnnotTerm} (hps : ps.length = d.nP)
    (hparams : SpineFit ρ (d.params ψ) (ps.map (interp V ρ)))
    (hlev : d.elimL.eval ψ = d.w ψ)
    {k₀ : Nat} {cd : Nat → CopyData V}
    -- the container's datum at the pin's assignment, and its group's data
    {dJ : IndRepData V} {ψ' : Name → Nat} {DsA : List AnnotTerm} {j₀ : Nat}
    (hkRJ : dJ.kReal = dJ.k)
    (hpinsJ : ∀ (t : Nat) (φ : Name → Nat), dJ.pinsAV t φ = paramBvarsAt dJ.nP dJ.nP)
    (hviewJ : ∀ J, dJ.ksR J = dJ.ksF J ∧ dJ.tgtsR J = dJ.tgts J ∧ dJ.eissR J = dJ.eissF J ∧
      dJ.tssR J = dJ.tssF J)
    {T : Name} {cvT cvR : ConstantVal} {mI rP : Nat} {rules : List RecRule} {t₀ : Nat}
    (ht₀ : t₀ < dJ.k) (hrepJ : IndRep mp.base2 T cvT cvR mI rP rules dJ t₀)
    (hlen : DsA.length = dJ.nP)
    (hgrp : ∀ t, t < dJ.k → CopyData.Ok mp.base2 d ψ k₀ (j₀ + t) ⟨dJ, t, ψ', DsA, j₀⟩)
    (hLgrp : ∀ t, t < dJ.k →
      d.invL mp.base2 ψ k₀ cd (k₀ + j₀ + t) = mp.base2.acval (dJ.memberName t) ψ' ∧
      d.invPinsT k₀ cd (k₀ + j₀ + t) = DsA)
    -- the constructor and its copy
    {Jc Ja : Nat} {cAJ cAa : ConstantVal × Nat} (hJc : dJ.ctorsA[Jc]? = some cAJ)
    (hf : CopyCtorFacts mp.base2 d dJ ψ ψ' DsA k₀ j₀ cd lpsT Jc Ja cAJ cAa)
    (hcd : ∀ i, i < cAJ.2 → i ∈ ConLeche.recIdxOf (d.ksR Ja) → i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
      k₀ ≤ d.tgtsR Ja i →
      CopyData.Ok mp.base2 d ψ k₀ (d.tgtsR Ja i - k₀) (cd (d.tgtsR Ja i - k₀))) :
    d.CopyCtorRead ψ ρ ps (d.invL mp.base2 ψ k₀ cd) (d.invPinsT k₀ cd) (d.invUseIh k₀ Ja) Ja
      (AnnotTerm.mkAppN (mp.base2.acval cAJ.1.name ψ') DsA) cAJ.2
      (instSeqDoms DsA (dJ.nP - 1) ((dJ.dsF Jc ψ').drop dJ.nP))
      (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1 + cAJ.2)
        (ctorBodyAVI mp.base2 (dJ.memberName (dJ.mems Jc)) dJ.nP cAJ.2 ψ' (dJ.esF Jc ψ'))) := by
  -- the two constructors' data
  have hrec := hf.read
  have hnF := hf.nF
  obtain ⟨-, -, hDA⟩ := hf.ctor
  have hCJ := hrepJ.ctors Jc cAJ hJc
  obtain ⟨hfindJ, -, hDJ⟩ := hrepJ.ctors Jc cAJ hJc
  have hviewA := hf.view
  have hpsLen : (ps.map (interp V ρ)).length = d.nP := by simp [hps]
  have hlenDsJ : (dJ.dsF Jc ψ').length = dJ.nP + cAJ.2 := hDJ.len ψ'
  have hksLenA : (d.ksR Ja).length = cAJ.2 := by rw [hviewA.1, hDA.ksLen, hnF]
  have hksLenJ : (dJ.ksF Jc).length = cAJ.2 := hDJ.ksLen
  -- the container member and its group data
  have hJA : Jc < dJ.ctorsA.length := (List.getElem?_eq_some_iff.mp hJc).1
  have hmemJ : dJ.mems Jc < dJ.k := by
    have h := (hrepJ.memsReal Jc (by unfold IndRepData.nAll; omega)).mpr hJA
    rw [hkRJ] at h; exact h
  have hk0 : 0 < dJ.k := Nat.lt_of_le_of_lt (Nat.zero_le _) ht₀
  have hcg := hgrp (dJ.mems Jc) hmemJ
  have hc0 := hgrp 0 hk0
  have hFFJ : ∀ t, t < dJ.k → dJ.FormerFacts mp.base2 ψ' t :=
    fun t ht => dJ.formerFacts_of_indRep hrepJ hkRJ ψ' ht
  have hLSJ : ∀ t, t < dJ.k → dJ.LeafShape mp.base2 ψ' t :=
    fun t ht => hrepJ.leafShape t (by rw [hkRJ]; exact ht) ψ'
  have hclosedJ : ∀ t, Term.bvarsBelow 0 (mp.base2.acval (dJ.memberName t) ψ').erase :=
    fun t => mp.base2.cval_closedL _ ψ'
  have hclosedA : ∀ t, Term.bvarsBelow 0 (mp.base2.acval (d.memberName t) ψ).erase :=
    fun t => mp.base2.cval_closedL _ ψ
  -- the frames
  have hsatA : Sat V (d.params ψ).reverse (consList (ps.map (interp V ρ)) ρ) := by
    have h := sat_of_spineFit (Δ₀ := []) (Sat_nil V _) hparams
    rwa [List.append_nil] at h
  generalize hσ : consList (ps.map (interp V ρ)) ρ = σ at hsatA
  have hshiftAll : ∀ (ws as : List V),
      shiftE (d.nP + ws.length + as.length) 0 (consList as (consList ws σ)) = ρ := by
    intro ws as
    rw [← hσ, ← consList_append, ← consList_append,
      show d.nP + ws.length + as.length = (ps.map (interp V ρ) ++ (ws ++ as)).length from by
        simp only [List.length_append, hpsLen]; omega]
    exact shiftE_consList _ _
  have hDsWD : ∀ D ∈ DsA, WellDenotedV V σ D :=
    (WellDenotedV.mkAppN_args (hcg.pin.wd σ hsatA)).2
  have hDsLen : (DsA.map (interp V σ)).length = dJ.nP := by simp [hlen]
  have hparamsJ : SpineFit σ (dJ.params ψ') (DsA.map (interp V σ)) :=
    d.pinFit_of_leafShape rfl (hFFJ 0 hk0) (hLSJ 0 hk0) hc0.pin hsatA
  have hpIffJ := hrepJ.paramsIff Jc cAJ hJc ψ'
  have hfitPJ : SpineFit σ (((dJ.dsF Jc ψ').take dJ.nP).map (·.2.2)) (DsA.map (interp V σ)) :=
    spineFit_of_paramsIff hDsLen (by simp [hlenDsJ]) hparamsJ hpIffJ
  have hne : ∀ (xs : List V) (t : Nat), (1 ≤ dJ.nP → t + 1 = dJ.nP + xs.length) →
      (DsA ≠ [] → DsA.length + xs.length = t + 1) := by
    intro xs t ht hne'
    have h1 : 1 ≤ dJ.nP := by rw [← hlen]; exact List.length_pos_iff.mpr hne'
    rw [hlen]; omega
  -- the elimination bit
  have hbA : d.bb ψ = 0 ↔ d.resSort.eval ψ = 0 := by
    unfold IndRepData.bb; rw [pwBit_zeronessOf, hlev]; exact Iff.rfl
  have hwJ : dJ.resSort.eval ψ' = d.resSort.eval ψ := hcg.idx.sort
  have hbJ : d.bb ψ = 0 ↔ dJ.resSort.eval ψ' = 0 := by rw [hbA, hwJ]
  -- the container constructor's tower, split at its parameters
  obtain ⟨bodyJ, hbodyJ⟩ : ∃ b, b = ctorBodyAVI mp.base2 (dJ.memberName (dJ.mems Jc)) dJ.nP cAJ.2 ψ'
    (dJ.esF Jc ψ') := ⟨_, rfl⟩
  rw [← hbodyJ]
  have hsplitJ : mkPisAV (dJ.dsF Jc ψ') bodyJ
      = mkPisAV ((dJ.dsF Jc ψ').take dJ.nP) (mkPisAV ((dJ.dsF Jc ψ').drop dJ.nP) bodyJ) := by
    rw [← mkPisAV_append, List.take_append_drop]
  have hokJ : WellDenotedV V σ (mkPisAV (dJ.dsF Jc ψ') bodyJ) := by
    rw [hbodyJ]; exact hDJ.okTy ψ' σ
  have hcmemJ : interp V σ (mp.base2.acval cAJ.1.name ψ')
      ∈ˢ interp V σ (mkPisAV (dJ.dsF Jc ψ') bodyJ) := by
    rw [hbodyJ]; exact mp.mem_type _ (Env.find?_mem hfindJ) ψ' _ (hDJ.read ψ') σ
  have hTσ' : WellDenotedV V (consList (DsA.map (interp V σ)) σ)
      (mkPisAV ((dJ.dsF Jc ψ').drop dJ.nP) bodyJ) := by
    have h := hokJ
    rw [hsplitJ] at h
    exact ⟨wellDenoted_mkPisAV_body h.1 _ hfitPJ, annotValid_mkPisAV_body h.2 _ hfitPJ⟩
  have hhead := wellDenotedV_mkAppN_of_spineFit (σ := σ) (ds := (dJ.dsF Jc ψ').take dJ.nP)
    (C := mkPisAV ((dJ.dsF Jc ψ').drop dJ.nP) bodyJ) (f := mp.base2.acval cAJ.1.name ψ') (as := DsA)
    (by rw [← hsplitJ]; exact hokJ) ⟨mp.base2.acval_wellDenoted _ ψ' _, mp.acval_validV _ ψ' _⟩
    hDsWD (by rw [← hsplitJ]; exact hcmemJ) hfitPJ
  have hdropLen : ((dJ.dsF Jc ψ').drop dJ.nP).length = cAJ.2 := by
    rw [List.length_drop, hlenDsJ]; omega
  have hle : DsA.length ≤ dJ.nP - 1 + 1 := by rw [hlen]; omega
  have hinstT : ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1)
        (mkPisAV ((dJ.dsF Jc ψ').drop dJ.nP) bodyJ)
      = mkPisAV (instSeqDoms DsA (dJ.nP - 1) ((dJ.dsF Jc ψ').drop dJ.nP))
          (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP - 1 + cAJ.2) bodyJ) := by
    rw [instSeq_mkPisAV DsA _ _ _ hle, hdropLen]
  have hdepth : dJ.nP - 1 = DsA.length - 1 := by rw [hlen]
  -- the instantiated entries
  have hdsCi : ∀ i, i < cAJ.2 →
      ((instSeqDoms DsA (dJ.nP - 1) ((dJ.dsF Jc ψ').drop dJ.nP)).getD i default).2.2
        = ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1)
            ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2 := by
    intro i hi
    have hlt : dJ.nP + i < (dJ.dsF Jc ψ').length := by rw [hlenDsJ]; omega
    simp only [List.getD_eq_getElem?_getD, instSeqDoms_getElem?, List.getElem?_drop,
      List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some]
    exact instSeq_congr_depth (fun hne' => by
      have h1 : 1 ≤ dJ.nP := by rw [← hlen]; exact List.length_pos_iff.mpr hne'
      omega) _
  -- fitting prefixes transfer to the container's frame
  have hfitTake : ∀ (i : Nat) (ws : List V),
      SpineFit σ (((instSeqDoms DsA (dJ.nP - 1) ((dJ.dsF Jc ψ').drop dJ.nP)).take i).map (·.2.2)) ws →
      SpineFit (consList (DsA.map (interp V σ)) σ)
        ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) ws := by
    intro i ws h
    rw [instSeqDoms_take] at h
    exact (spineFit_instSeqDoms_iff (σ := σ) [] (dJ.nP - 1) _ ws
      (hne [] _ (fun h1 => by simp only [List.length_nil]; omega))).mp h
  -- the container constructor's field facts at the pin
  have hcffJ := dJ.ctorFieldFacts_of mp hlen (fun t => hpinsJ t ψ') hLSJ hFFJ hparamsJ hCJ hpIffJ
    hmemJ (fun i => by have := hrepJ.tgtsRLt Jc i; rw [(hviewJ Jc).2.1] at this; exact this)
    (fun i => by rw [(hviewJ Jc).2.1])
  refine ⟨by rw [instSeqDoms_length, hdropLen], ?_, by rw [hσ]; exact hhead.1, ?_, ?_, ?_⟩
  · -- the tower, graded
    rw [hσ, ← hinstT]
    exact wellDenotedV_instSeq_under σ DsA [] (dJ.nP - 1) _
      (hne [] _ (fun h1 => by simp only [List.length_nil]; omega)) hDsWD hTσ'
  · -- the head, in it
    rw [hσ, ← hinstT, hdepth, interp_instSeq_consList]
    exact hhead.2
  · -- the fields
    intro i hi ws hws hfitC
    rw [hσ] at hfitC ⊢
    have hfitJ := hfitTake i ws hfitC
    rw [hdsCi i hi]
    unfold tgFieldAV
    have hmemA : d.mems Ja = k₀ + j₀ + dJ.mems Jc := hrec.mem
    by_cases hu : d.invUseIh k₀ Ja i = true
    · rw [if_pos hu]
      unfold IndRepData.invUseIh at hu
      obtain ⟨-, hA, hk⟩ := of_decide_eq_true hu
      have hkA : i < (d.ksR Ja).length ∧ ((d.ksR Ja).getD i .ordinary = .recursive ∨
          (d.ksR Ja).getD i .ordinary = .reflexive) := mem_recIdxOf.mp hA
      have htgtLt : d.tgtsR Ja i < d.k := hf.tgts i
      -- the copy's telescope and index readings at this field
      obtain ⟨tlsA, htlsA⟩ : ∃ x, x = (d.tssR Ja ψ).getD i [] := ⟨_, rfl⟩
      obtain ⟨eissA, heissA⟩ : ∃ x, x = (d.eissR Ja ψ).getD i [] := ⟨_, rfl⟩
      rw [← htlsA, ← heissA]
      have hEls : eissA.length = d.nIdxAt (d.tgtsR Ja i) := by
        rw [heissA, hviewA.2.2.1, hviewA.2.1]
        rcases hkA.2 with hk' | hk'
        · rw [hviewA.1] at hk'; exact hDA.eisLen ψ i hk' (by rw [hnF]; exact hi)
        · rw [hviewA.1] at hk'; exact hDA.eisLenRefl ψ i hk' (by rw [hnF]; exact hi)
      by_cases hR : i ∈ ConLeche.recIdxOf (dJ.ksF Jc)
      · -- a container-recursive field: the group-mate's copy
        obtain ⟨hks, htgt, htls, heiss⟩ := hrec.kindR i hR
        rw [← htlsA] at htls
        rw [← heissA] at heiss
        have hkJ := mem_recIdxOf.mp hR
        have hentry := FixCtorDataI.recRefl_entry hDJ ψ' hR
        obtain ⟨tlsJ, htlsJ⟩ : ∃ x, x = (dJ.tssF Jc ψ').getD i [] := ⟨_, rfl⟩
        obtain ⟨eissJ, heissJ⟩ : ∃ x, x = (dJ.eissF Jc ψ').getD i [] := ⟨_, rfl⟩
        rw [← htlsJ] at hentry htls heiss
        rw [← heissJ] at hentry heiss
        have htgtJ : dJ.tgts Jc i < dJ.k := by
          have := hrepJ.tgtsRLt Jc i; rw [(hviewJ Jc).2.1] at this; exact this
        have hElJ : eissJ.length = dJ.nIdxAt (dJ.tgts Jc i) := by
          rw [heissJ]
          rcases hkJ.2 with hk' | hk'
          · exact hDJ.eisLen ψ' i hk' hi
          · exact hDJ.eisLenRefl ψ' i hk' hi
        have hcgT := hgrp (dJ.tgts Jc i) htgtJ
        obtain ⟨hL, hp⟩ := hLgrp (dJ.tgts Jc i) htgtJ
        rw [hentry, interp_instSeq_under σ DsA ws _ _ (hne ws _ (fun h1 => by rw [hws]; omega))]
        have htlsLen : tlsA.length = tlsJ.length := by rw [htls, instSeqDoms_length]
        refine interp_mkPisAV_congr (by simp [rebit, htlsLen]) ?_ ?_ ?_
        · intro k d₁ d₂ h₁ h₂
          rw [mem_rebit (List.mem_of_getElem? h₁), hDJ.tssBits ψ' i d₂ (by rw [← htlsJ]; exact List.mem_of_getElem? h₂)]
          exact hbJ
        · intro k d₁ d₂ as h₁ h₂ hsp
          have hasLen : as.length = k := by
            rw [hsp.length_eq, List.length_map, List.length_take]
            unfold rebit
            rw [List.length_map, htlsLen]
            have := (List.getElem?_eq_some_iff.mp h₂).1
            omega
          have h₁' : d₁.2.2 = ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1 + k) d₂.2.2 := by
            unfold rebit at h₁
            rw [List.getElem?_map, htls, instSeqDoms_getElem?, h₂] at h₁
            simp only [Option.map_some, Option.some.injEq] at h₁
            rw [← h₁]
          rw [h₁', ← consList_append, ← consList_append,
            interp_instSeq_under σ DsA (ws ++ as) _ _ (hne _ _ (fun h1 => by
              rw [List.length_append, hws, hasLen]; omega))]
        · intro as hsp
          have hasLen : as.length = tlsJ.length := by
            rw [hsp.length_eq, List.length_map]
            unfold rebit
            rw [List.length_map, htlsLen]
          have hasJ : SpineFit (consList ws (consList (DsA.map (interp V σ)) σ)) (tlsJ.map (·.2.2)) as := by
            rw [rebit_map_dom, htls] at hsp
            exact (spineFit_instSeqDoms_iff (σ := σ) ws (dJ.nP + i - 1) tlsJ as
              (hne ws _ (fun h1 => by rw [hws]; omega))).mp hsp
          -- the left-hand side's head: the target at the base frame
          have hlift : interp V (consList as (consList ws σ))
              ((d.invTgAV ψ ps (d.invL mp.base2 ψ k₀ cd) (d.invPinsT k₀ cd) (d.tgtsR Ja i)).liftN
                (d.nP + i + tlsA.length) 0)
              = interp V ρ (d.invTgAV ψ ps (d.invL mp.base2 ψ k₀ cd) (d.invPinsT k₀ cd) (d.tgtsR Ja i)) := by
            rw [interp_liftN, show d.nP + i + tlsA.length = d.nP + ws.length + as.length by
              rw [hws, htlsLen, hasLen], hshiftAll]
          -- the right-hand side: the group-mate's leaf at the pin and the readings
          rw [interp_mkAppN_map, interp_mkAppN_map, hlift, List.map_append, Nat.add_assoc dJ.nP i,
            map_paramBvarsAt_interp (ρp := consList (DsA.map (interp V σ)) σ) (fun j => by
              rw [← consList_append, show i + tlsJ.length = (ws ++ as).length from by
                rw [List.length_append, hws, hasLen]]
              exact consList_apply_add _ _ _),
            range_reverse_map_consList' hDsLen, interp_closed (V := V) (hclosedJ _) _ σ]
          have hEv : eissA.map (interp V (consList as (consList ws σ)))
              = eissJ.map (interp V (consList as (consList ws (consList (DsA.map (interp V σ)) σ)))) := by
            rw [heiss, List.map_map]
            apply List.map_congr_left
            intro E _
            simp only [Function.comp_def]
            rw [← consList_append, ← consList_append,
              interp_instSeq_under σ DsA (ws ++ as) _ _ (hne _ _ (fun h1 => by
                rw [List.length_append, hws, hasLen]; omega))]
          rw [hEv]
          -- the readings fit the group-mate's index telescope
          have hokE : WellDenoted V (consList (ws ++ as) (consList (DsA.map (interp V σ)) σ))
              (AnnotTerm.mkAppN (mp.base2.acval (dJ.memberName (dJ.tgts Jc i)) ψ')
                (paramBvarsAt dJ.nP (dJ.nP + (i + tlsJ.length)) ++ eissJ)) := by
            have h1 := wellDenoted_mkPisAV_dom hTσ'.1 ws i _
              (List.getElem?_eq_getElem (by rw [hdropLen]; exact hi)) hfitJ
            have hlt : dJ.nP + i < (dJ.dsF Jc ψ').length := by rw [hlenDsJ]; omega
            have hd : (dJ.dsF Jc ψ')[dJ.nP + i]'hlt = (dJ.dsF Jc ψ').getD (dJ.nP + i) default := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
            rw [List.getElem_drop, hd, hentry] at h1
            have h2 := wellDenoted_mkPisAV_body h1 as hasJ
            rw [consList_append, ← Nat.add_assoc]
            exact h2
          have hfitJI := dJ.idxFit_of_entry (ρ₀ := σ) (psA := DsA) hlen (hFFJ _ htgtJ) (hLSJ _ htgtJ)
            (σas := ws ++ as) (e := i + tlsJ.length) (by rw [List.length_append, hws, hasLen])
            hokE hElJ
          rw [consList_append] at hfitJI
          have hfitA : SpineFit σ (d.IdsM (k₀ + (j₀ + dJ.tgts Jc i)) ψ) _ :=
            (hcgT.idx.idxIff σ hsatA _).mpr hfitJI
          have htgtE : d.tgtsR Ja i = k₀ + (j₀ + dJ.tgts Jc i) := by rw [htgt, Nat.add_assoc]
          have hfitE' : SpineFit (consList (ps.map (interp V ρ)) ρ)
              ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.tgtsR Ja i) [])).map (·.2.2))
              (eissJ.map (interp V (consList as (consList ws (consList (DsA.map (interp V σ)) σ))))) := by
            rw [hσ, d.ipss_getD ψ htgtLt, rebit_map_dom, htgtE]
            exact hfitA
          have hfold := d.invTg_fold ψ (L := d.invL mp.base2 ψ k₀ cd) (pinsT := d.invPinsT k₀ cd) hfitE'
          rw [hσ] at hfold
          rw [hfold, htgt, hL, hp]
          have hnI : eissJ.length = d.nIdxs.getD (k₀ + j₀ + dJ.tgts Jc i) 0 := by
            rw [hElJ, hcgT.idx.nIdx, Nat.add_assoc]; rfl
          rw [interp_famAppAV_pins (hclosedJ _) DsA d.nP (by rw [List.length_map]; exact hnI)]
      · -- a transport: the target copy
        obtain ⟨j', hj', -, hagr, hgr⟩ := hrec.kindT i hi hR hA hk
        rw [← htlsA, ← heissA] at hagr hgr
        have hEq := hagr σ ws hws hsatA hfitJ
        have hWD := hgr σ ws hws hsatA hfitJ
        rw [hEq]
        have hct := hcd i hi hA hR hk
        rw [hj', Nat.add_sub_cancel_left] at hct
        refine interp_mkPisAV_congr (by simp [rebit]) ?_ ?_ ?_
        · intro k d₁ d₂ h₁ h₂
          rw [mem_rebit (List.mem_of_getElem? h₁),
            hDA.tssBits ψ i d₂ (by rw [htlsA, hviewA.2.2.2] at h₂; exact List.mem_of_getElem? h₂)]
          exact hbA
        · intro k d₁ d₂ as h₁ h₂ _
          have h₁' : d₁.2.2 = d₂.2.2 := by
            unfold rebit at h₁
            rw [List.getElem?_map, h₂] at h₁
            simp only [Option.map_some, Option.some.injEq] at h₁
            rw [← h₁]
          rw [h₁']
        · intro as hsp
          rw [rebit_map_dom] at hsp
          have hasLen : as.length = tlsA.length := by rw [hsp.length_eq, List.length_map]
          obtain ⟨hWDb, hval, -, hfitT⟩ := d.transport_fits mp.base2 hct (tssA := tlsA)
            (eissA := eissA) (by rw [← hj']; exact hEls) hws hWD hsp
          have hlift : interp V (consList as (consList ws σ))
              ((d.invTgAV ψ ps (d.invL mp.base2 ψ k₀ cd) (d.invPinsT k₀ cd) (d.tgtsR Ja i)).liftN
                (d.nP + i + tlsA.length) 0)
              = interp V ρ (d.invTgAV ψ ps (d.invL mp.base2 ψ k₀ cd) (d.invPinsT k₀ cd) (d.tgtsR Ja i)) := by
            rw [interp_liftN, show d.nP + i + tlsA.length = d.nP + ws.length + as.length by
              rw [hws, hasLen], hshiftAll]
          rw [hval, interp_mkAppN_map, hlift]
          have hfitA : SpineFit σ (d.IdsM (k₀ + j') ψ) _ := (hct.idx.idxIff σ hsatA _).mpr hfitT
          have hfitE' : SpineFit (consList (ps.map (interp V ρ)) ρ)
              ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.tgtsR Ja i) [])).map (·.2.2))
              (eissA.map (interp V (consList as (consList ws σ)))) := by
            rw [hσ, d.ipss_getD ψ htgtLt, rebit_map_dom, hj']
            exact hfitA
          have hfold := d.invTg_fold ψ (L := d.invL mp.base2 ψ k₀ cd) (pinsT := d.invPinsT k₀ cd) hfitE'
          rw [hσ] at hfold
          rw [hfold, hj', d.invL_copy, d.invPinsT_copy]
          rw [interp_famAppAV_pins (mp.base2.cval_closedL _ _) _ d.nP
            (by rw [List.length_map, hEls, hj']; rfl)]
    · rw [if_neg hu]
      unfold IndRepData.invUseIh at hu
      simp only [decide_eq_true_eq, not_and] at hu
      have hu' : ¬ (i ∈ ConLeche.recIdxOf (d.ksR Ja) ∧ k₀ ≤ d.tgtsR Ja i) :=
        fun h => hu (by rw [hmemA]; omega) h.1 h.2
      have hT : i ∉ ConLeche.recIdxOf (dJ.ksF Jc) := by
        intro hR
        obtain ⟨hks, htgt, -, -⟩ := hrec.kindR i hR
        have hkJ := mem_recIdxOf.mp hR
        refine hu' ⟨mem_recIdxOf.mpr ⟨by rw [hksLenA]; exact hi, by rw [hks]; exact hkJ.2⟩, ?_⟩
        rw [htgt]; omega
      have hord := hrec.ord i hi hT (by
        by_cases hA : i ∈ ConLeche.recIdxOf (d.ksR Ja)
        · exact Or.inr (Nat.lt_of_not_le fun hk => hu' ⟨hA, hk⟩)
        · exact Or.inl hA)
      exact hord σ ws hws hsatA hfitJ
  · -- the body
    intro vs hvs
    rw [hσ] at hvs ⊢
    have hfitJv : SpineFit (consList (DsA.map (interp V σ)) σ)
        (((dJ.dsF Jc ψ').drop dJ.nP).map (·.2.2)) vs :=
      (spineFit_instSeqDoms_iff (σ := σ) [] (dJ.nP - 1) _ vs
        (hne [] _ (fun h1 => by simp only [List.length_nil]; omega))).mp hvs
    have hvsLen : vs.length = cAJ.2 := by rw [hfitJv.length_eq, List.length_map, hdropLen]
    rw [interp_instSeq_under σ DsA vs (dJ.nP - 1 + cAJ.2) bodyJ
      (hne vs _ (fun h1 => by rw [hvsLen]; omega)), hbodyJ]
    unfold ctorBodyAVI
    rw [paramBvars_eq_paramBvarsAt, interp_mkAppN_map, List.map_append,
      map_paramBvarsAt_interp (ρp := consList (DsA.map (interp V σ)) σ)
        (fun j => by rw [← hvsLen]; exact consList_apply_add vs _ j),
      range_reverse_map_consList' hDsLen, interp_closed (V := V) (hclosedJ _) _ σ]
    -- the copy's index readings are the container's
    have hEv : (d.esF Ja ψ).map (interp V (consList vs σ))
        = (dJ.esF Jc ψ').map (interp V (consList vs (consList (DsA.map (interp V σ)) σ))) := by
      rw [hrec.es, List.map_map]
      apply List.map_congr_left
      intro E _
      simp only [Function.comp_def]
      rw [interp_instSeq_under σ DsA vs (dJ.nP + cAJ.2 - 1) E
        (hne vs _ (fun h1 => by rw [hvsLen]; omega))]
    rw [hEv]
    -- the fit into the copy's index telescope
    have hfitEJ := (hcffJ.2 vs hfitJv).1
    rw [dJ.ipss_getD ψ' hmemJ, rebit_map_dom] at hfitEJ
    have hfitEA : SpineFit σ (d.IdsM (k₀ + (j₀ + dJ.mems Jc)) ψ) _ :=
      (hcg.idx.idxIff σ hsatA _).mpr hfitEJ
    have hmemA : d.mems Ja = k₀ + (j₀ + dJ.mems Jc) := by rw [hrec.mem, Nat.add_assoc]
    have hmemLt : d.mems Ja < d.k := hf.mem
    have hfitE' : SpineFit (consList (ps.map (interp V ρ)) ρ)
        ((rebit (pwBit ψ ConLeche.PropWhen.never) ((d.ipss ψ).getD (d.mems Ja) [])).map (·.2.2))
        ((dJ.esF Jc ψ').map (interp V (consList vs (consList (DsA.map (interp V σ)) σ)))) := by
      rw [hσ, d.ipss_getD ψ hmemLt, rebit_map_dom, hmemA]
      exact hfitEA
    have hfold := d.invTg_fold ψ (L := d.invL mp.base2 ψ k₀ cd) (pinsT := d.invPinsT k₀ cd) hfitE'
    rw [hσ] at hfold
    rw [hfold]
    obtain ⟨hL, hp⟩ := hLgrp (dJ.mems Jc) hmemJ
    rw [hrec.mem, hL, hp]
    have hnI : (dJ.esF Jc ψ').length = d.nIdxs.getD (k₀ + j₀ + dJ.mems Jc) 0 := by
      rw [hDJ.lenE ψ', hcg.idx.nIdx, Nat.add_assoc]; rfl
    rw [interp_famAppAV_pins (hclosedJ _) DsA d.nP (by rw [List.length_map]; exact hnI)]

end IndRepData

/-! ## The heads -/

namespace IndRepData

variable (d : IndRepData V)

open Classical in
/-- **ψ⁻¹'s heads**: a real constructor at the parameter variables; a
copy's constructor `J` the CONTAINER constructor at the pin's readings,
at a representative `(j', Jc)` of `J` under `auxOfs` (any representative
gives `CtorAtPins`, `copyCtorRead_of_asRead`; the heads' agreement
across representatives is M-C′'s coherence, DESIGN §M.32). -/
@[expose] noncomputable def invHead (m : EnvModel V env) (ψ : Name → Nat) (n : Nat)
    (cd : Nat → CopyData V) (auxOfs : Nat → Nat → Nat) (J : Nat) : AnnotTerm :=
  if h : ∃ x : Nat × Nat × (ConstantVal × Nat), x.1 < n ∧ (cd x.1).dJ.ctorsA[x.2.1]? = some x.2.2 ∧
      auxOfs x.1 x.2.1 = J then
    AnnotTerm.mkAppN (m.acval (Classical.choose h).2.2.1.name (cd (Classical.choose h).1).ψ')
      (cd (Classical.choose h).1).DsA
  else AnnotTerm.mkAppN (m.acval (d.ctorsA.getD J default).1.name ψ) (paramBvarsAt d.nP d.nP)

/-- A real constructor's head, when every copy's constructor index is a
copy member's. -/
theorem invHead_real (m : EnvModel V env) (ψ : Name → Nat) {k₀ n : Nat} {cd : Nat → CopyData V}
    {auxOfs : Nat → Nat → Nat}
    (hOfs : ∀ j' Jc cAJ, j' < n → (cd j').dJ.ctorsA[Jc]? = some cAJ → k₀ ≤ d.mems (auxOfs j' Jc))
    {J : Nat} (hJ : d.mems J < k₀) :
    d.invHead m ψ n cd auxOfs J
      = AnnotTerm.mkAppN (m.acval (d.ctorsA.getD J default).1.name ψ) (paramBvarsAt d.nP d.nP) := by
  unfold invHead
  rw [dif_neg]
  rintro ⟨⟨j', Jc, cAJ⟩, hj', hJc, hE⟩
  have := hOfs j' Jc cAJ hj' hJc
  rw [hE] at this
  omega

/-- A copy constructor's head: the container constructor of SOME
representative at that pin's readings. -/
theorem invHead_copy (m : EnvModel V env) (ψ : Name → Nat) (n : Nat) (cd : Nat → CopyData V)
    (auxOfs : Nat → Nat → Nat) {J : Nat}
    (h : ∃ x : Nat × Nat × (ConstantVal × Nat), x.1 < n ∧ (cd x.1).dJ.ctorsA[x.2.1]? = some x.2.2 ∧
      auxOfs x.1 x.2.1 = J) :
    ∃ j' Jc cAJ, j' < n ∧ (cd j').dJ.ctorsA[Jc]? = some cAJ ∧ auxOfs j' Jc = J ∧
      d.invHead m ψ n cd auxOfs J
        = AnnotTerm.mkAppN (m.acval cAJ.1.name (cd j').ψ') (cd j').DsA := by
  unfold invHead
  rw [dif_pos h]
  obtain ⟨hj', hJc, hE⟩ := Classical.choose_spec h
  exact ⟨_, _, _, hj', hJc, hE, rfl⟩

end IndRepData

/-! ## The run level -/

/-- **A group-mate's data agree with the pin's**: the copy of member `t`
of pin `j`'s container (pin `base + t`) has the leaf and the readings
`invL`/`invPinsT` name for it — its container member's name is
`j`'s datum's member `t` (`PinRunFacts`' group clause), its leaf at its
own assignment reads as at the pin's level substitution (both do), and
its readings are the pin's (`DenoteMetaSpine.unique` at the group's
one component list). -/
theorem invChoice_group {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts}
    {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hcd : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    {j : Nat} (hj : j < st.pins.length) {t : Nat} (ht : t < (cd j).dJ.k) :
    d.invL mpAux.base2 ψ p.k cd (p.k + (cd j).base + t)
        = mpAux.base2.acval ((cd j).dJ.memberName t) (cd j).ψ' ∧
      d.invPinsT p.k cd (p.k + (cd j).base + t) = (cd j).DsA := by
  obtain ⟨⟨-, -, q, I, ci, Jm, lvls, Ds, cvTJ, capsJ, -, hci, -, -, -, hlenM, hgrp, -, -, -, -, -,
    hsp, -, -, -, -, -, hab⟩, -⟩ := hcd j hj
  obtain ⟨J', hJ'⟩ : ∃ J', ci.members[t]? = some J' :=
    ⟨_, List.getElem?_eq_getElem (by rw [hlenM]; exact ht)⟩
  obtain ⟨q', hq', hq'c, hq'p, -, -⟩ := hgrp t J' hJ'
  have hj₂ : (cd j).base + t < st.pins.length := (List.getElem?_eq_some_iff.mp hq').1
  obtain ⟨hname, hacv⟩ := hab t J' hJ'
  obtain ⟨⟨-, -, q₂, I₂, ci₂, J₂, lvls₂, Ds₂, cvTJ₂, capsJ₂, hq₂, hci₂, hJ₂, hJ₂n, hmn₂, -, -, hqp₂,
    -, -, -, -, hsp₂, -, -, -, -, -, hab₂⟩, -⟩ := hcd _ hj₂
  obtain rfl : q₂ = q' := Option.some.inj (hq₂.symm.trans hq')
  obtain ⟨-, hlv, hDs⟩ := group_pin_eq hq' hq' hq'p hqp₂
  have hDsA : (cd ((cd j).base + t)).DsA = (cd j).DsA := by
    rw [← hDs] at hsp₂
    exact DenoteMetaSpine.unique hsp₂ hsp
  have hname₂ : (cd ((cd j).base + t)).dJ.memberName (cd ((cd j).base + t)).mm = J'.name := by
    rw [hmn₂, hq'c]
  obtain ⟨-, hacv₂⟩ := hab₂ _ J₂ hJ₂
  have hJ₂name : J₂.name = J'.name := by rw [hJ₂n, hq'c]
  have hJ₂lps : J₂.lps = J'.lps := by
    obtain ⟨⟨cv₁, caps₁, hf₁, -, hl₁⟩, -⟩ :=
      ConLeche.containerInfo?_stored hci₂ J₂ (List.mem_of_getElem? hJ₂)
    obtain ⟨⟨cv₂, caps₂, hf₂, -, hl₂⟩, -⟩ :=
      ConLeche.containerInfo?_stored hci J' (List.mem_of_getElem? hJ')
    rw [hJ₂name] at hf₁
    obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hf₁.symm.trans hf₂))
    rw [hl₁, hl₂]
  rw [hJ₂name, hJ₂lps, ← hlv] at hacv₂
  refine ⟨?_, ?_⟩
  · rw [show p.k + (cd j).base + t = p.k + ((cd j).base + t) from Nat.add_assoc _ _ _,
      d.invL_copy, hname₂, hname, hacv, hacv₂]
  · rw [show p.k + (cd j).base + t = p.k + ((cd j).base + t) from Nat.add_assoc _ _ _,
      d.invPinsT_copy, hDsA]

/-- **Every copy's constructor is a container constructor's copy**: an
auxiliary constructor of a copy member (`p.k ≤ mems J`) is
`auxOfsOf st p.k cd j' Jc` for its pin `j'` and the container
constructor `Jc` at its member and position (`auxBlock_ctor_inv` for
the position, `CopyCtorsStored` for the copy's constructor count,
`ContainerCtorsAt.inv` for `Jc`). -/
theorem copyCtor_repr {μ : CheckMode} {F : Nat} {env envAux : Env} {p : ConLeche.NestedParts}
    {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hb : ConLeche.auxBlock p st = some b) (hlenSt : st.types.length = p.k + st.pins.length)
    (hchk : CtorsChecked μ F env b true d)
    (hcd : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : d.ctorsA[J]? = some cA) (hge : p.k ≤ d.mems J) :
    ∃ j' Jc cAJ, j' < st.pins.length ∧ (cd j').dJ.ctorsA[Jc]? = some cAJ ∧
      auxOfsOf st p.k cd j' Jc = J := by
  obtain ⟨env₁, fms, f₀, ctorsA, sortss, -, -, hctors, hdA, -, hmems⟩ := hchk
  obtain ⟨hlenC, -, -⟩ := ConLeche.checkMutualCtors_inv hctors
  have hJlt : J < b.ctors.length := by
    rw [← hlenC, ← hdA]; exact (List.getElem?_eq_some_iff.mp hJ).1
  obtain ⟨c, hc⟩ : ∃ c, b.ctors[J]? = some c := ⟨_, List.getElem?_eq_getElem hJlt⟩
  obtain ⟨t, l, ty, c', hty, hc', hJE, rfl⟩ := ConLeche.auxBlock_ctor_inv hb hc
  have hmemJ : d.mems J = t := by
    rw [hmems J, List.getD_eq_getElem?_getD, hc]; rfl
  rw [hmemJ] at hge
  have htLt : t < st.types.length := (List.getElem?_eq_some_iff.mp hty).1
  obtain ⟨j, rfl⟩ : ∃ j, t = p.k + j := ⟨t - p.k, by omega⟩
  have hj : j < st.pins.length := by omega
  obtain ⟨⟨-, hbm, q, I, ci, Jm, lvls, Ds, cvTJ, capsJ, -, -, hJm, -, -, -, -, -, -, -, -, -, -,
    hcat, hcst, -⟩, -⟩ := hcd j hj
  obtain ⟨tyA, htyA, -, hlenA, -⟩ := hcst
  obtain rfl : tyA = ty := Option.some.inj (htyA.symm.trans hty)
  have hl : l < Jm.ctors.length := by
    rw [← hlenA]; exact (List.getElem?_eq_some_iff.mp hc').1
  obtain ⟨cJ, hcJ⟩ : ∃ cJ, Jm.ctors[l]? = some cJ := ⟨_, List.getElem?_eq_getElem hl⟩
  obtain ⟨Jc, cAJ, hJc, hmm, hpos⟩ := hcat.inv _ l Jm cJ hJm hcJ
  refine ⟨j, Jc, cAJ, hj, hJc, ?_⟩
  unfold auxOfsOf
  rw [hmm, hpos, hbm, hJE]

set_option maxHeartbeats 1600000 in
/-- **ψ⁻¹'s SETUP FROM THE PINS' FACTS** (task #279 M-C′): at the run's
pin data (`PinRunFacts`) with the constructor record (`CopyCtorsRead`),
at a level assignment sending the scratch block's elimination universe
to its carrier's rank, `InvSetup` holds for the scratch block at the
choice `invL`/`invPinsT`/`invHead`/`invUseIh` (at the block's datum
re-sorted to the member with rules) at EVERY parameter frame: the real
members at the identity (`invSetup_of_blockReps_nested`), every copy's
target from its pin's read (`targetOk_copy` at `CopyData.Ok`), every
copy constructor's `CtorAtPins` from the record through
`copyCtorRead_of_asRead` at a representative (`copyCtor_repr`).  Hence
ψ⁻¹ is TYPED (`InvSetup.fold_mem`) and FIRING (`InvSetup.fold_iota`)
end to end.  The sort `s` is the block's, chosen once (member `t₀`'s),
before the frame. -/
theorem invSetup_of_pinFacts {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    (hb : ConLeche.auxBlock p st = some b) (hlenSt : st.types.length = p.k + st.pins.length)
    (hcd : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hread : CopyCtorsRead mpAux d ψ st p.k st.pins.length cd) (hlev : d.elimL.eval ψ = d.w ψ)
    {t₀ : Nat} (ht₀ : t₀ < b.k) (hct₀ : d.memberCtors t₀ ≠ []) :
    ∃ (s : Level) (lps lpsT : List Name),
      (∀ φ : Name → Nat, s.eval φ = d.resSort.eval φ) ∧
      ∀ (ρ : Nat → V) (ps : List AnnotTerm), ps.length = d.nP →
        (∀ q ∈ ps, WellDenotedV V ρ q) →
        SpineFit ρ (d.params ψ) (ps.map (interp V ρ)) →
        ({d with resSort := s} : IndRepData V).InvSetup mpAux lps lpsT ψ ρ ps
          (d.invL mpAux.base2 ψ p.k cd) (d.invPinsT p.k cd)
          (d.invHead mpAux.base2 ψ st.pins.length cd (auxOfsOf st p.k cd))
          (d.invUseIh p.k) := by
  have hreps' := hreps
  obtain ⟨-, hkb, -, -, -, -, -, hall⟩ := hreps
  have hdk : d.k = p.k + st.pins.length := by rw [hkb, ConLeche.auxBlock_k hb, hlenSt]
  obtain ⟨-, hFFA, -, hpIffMA⟩ := auxFacts_of_blockReps hreps' ψ
  have hk0 : 0 < d.k := by rw [hkb]; exact Nat.lt_of_le_of_lt (Nat.zero_le _) ht₀
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, hsv₀, hrep₀⟩ :=
    hall 0 (by rw [← hkb]; exact hk0)
  -- every copy's data are live at its pin
  have hok : ∀ j, j < st.pins.length → CopyData.Ok mpAux.base2 d ψ p.k j (cd j) := by
    intro j hj
    obtain ⟨⟨pf, hbm, -⟩, -⟩ := hcd j hj
    have h := pf.grp (cd j).mm pf.mm
    rw [hbm] at h
    exact h
  -- every copy's constructor index is a copy member's
  have hOfs : ∀ j' Jc cAJ, j' < st.pins.length → (cd j').dJ.ctorsA[Jc]? = some cAJ →
      p.k ≤ d.mems (auxOfsOf st p.k cd j' Jc) := by
    intro j' Jc cAJ hj' hJc
    obtain ⟨cA', -, hf, -⟩ :=
      copyCtorFacts_of_read hreps' hchk hcd hsv₀ hrep₀ hj' hJc (hread j' hj' Jc cAJ hJc)
    rw [hf.read.mem]
    exact Nat.le_add_right_of_le (Nat.le_add_right _ _)
  -- the real members: their own leaves
  have hreal : ∀ t, t < p.k → t < d.k →
      d.invL mpAux.base2 ψ p.k cd t = mpAux.base2.acval (d.memberName t) ψ ∧
        d.invPinsT p.k cd t = paramBvarsAt d.nP d.nP := by
    intro t ht _
    exact ⟨d.invL_real ht, d.invPinsT_real ht⟩
  -- the real constructors: their own heads, no hypothesis in use
  have hrealC : ∀ J cA, d.ctorsA[J]? = some cA → d.mems J < p.k →
      d.invHead mpAux.base2 ψ st.pins.length cd (auxOfsOf st p.k cd) J
          = AnnotTerm.mkAppN (mpAux.base2.acval cA.1.name ψ) (paramBvarsAt d.nP d.nP) ∧
        ∀ i, d.invUseIh p.k J i = false := by
    intro J cA hJ hlt
    refine ⟨?_, d.invUseIh_real hlt⟩
    rw [d.invHead_real _ _ hOfs hlt, List.getD_eq_getElem?_getD, hJ]
    rfl
  obtain ⟨s, lps, lpsT, hsv, hS⟩ := invSetup_of_blockReps_nested hreps' ht₀ hct₀ hlev (kR := p.k)
    hreal hrealC (fun J i h => d.invUseIh_mem h)
  refine ⟨s, lps, lpsT, hsv, fun ρ ps hps hpsWD hparams => hS ρ ps hps hpsWD hparams ?_ ?_⟩
  · -- the copies' targets, from their pins' reads
    intro t hkt ht
    obtain ⟨j, rfl⟩ : ∃ j, t = p.k + j := ⟨t - p.k, by omega⟩
    have hj : j < st.pins.length := by omega
    have hc := hok j hj
    refine d.targetOk_copy mpAux hps ht (hFFA _ ht) (hpIffMA _ ht) hparams hlev hc.ff hc.ls
      (d.invL_copy j) (d.invPinsT_copy j) ?_ hc.idx
    rw [d.invL_copy j]
    exact hc.pin
  · -- the copies' constructors, from the record at a representative
    intro J cA hJ hge
    obtain ⟨j', Jc, cAJ, hj', hJc, hE⟩ := copyCtor_repr hb hlenSt hchk hcd hJ hge
    obtain ⟨j'', Jc', cAJ', hj'', hJc', hE', hhead⟩ :=
      d.invHead_copy mpAux.base2 ψ st.pins.length cd (auxOfsOf st p.k cd)
        ⟨⟨j', Jc, cAJ⟩, hj', hJc, hE⟩
    obtain ⟨cA', hget, hf, -, -⟩ :=
      copyCtorFacts_of_read hreps' hchk hcd hsv₀ hrep₀ hj'' hJc' (hread j'' hj'' Jc' cAJ' hJc')
    rw [hE'] at hget hf
    obtain rfl : cA' = cA := Option.some.inj (hget.symm.trans hJ)
    rw [hhead, hf.nF]
    obtain ⟨⟨pf, -, -⟩, -⟩ := hcd j'' hj''
    obtain ⟨T, cvT, cvR, mI, rP, rules, t₀', ht₀', -, -, hrepJ⟩ := pf.rep
    refine d.ctorAtPins_copy (d.copyCtorRead_of_asRead mpAux hps hparams hlev pf.kReal pf.pinsAV
      pf.view ht₀' hrepJ pf.len pf.grp ?_ hJc' hf ?_)
    · intro t ht
      exact invChoice_group hcd hj'' ht
    · intro i hi hA hT hk
      have htgt : d.tgtsR J i < d.k := hf.tgts i
      have hj₂ : d.tgtsR J i - p.k < st.pins.length := by omega
      have h := hok _ hj₂
      exact h


set_option maxHeartbeats 1600000 in
/-- **ψ⁻¹'s SETUP FROM THE RUN** (task #279 M-C′): under the containers'
representation (`ContainersRep`) and the constructor record
(`CopyCtorsRead`) — the two premises ψ has — at every level assignment
sending the scratch block's elimination universe to its carrier's rank
and every parameter frame, `InvSetup` holds for the scratch block at
the choice `invL`/`invPinsT`/`invHead`/`invUseIh` (at the block's datum
re-sorted to the member with rules): the real members at the identity
(`invSetup_of_blockReps_nested`), every copy's target from its pin's
read (`targetOk_copy` at `CopyData.Ok`), every copy constructor's
`CtorAtPins` from the record through `copyCtorRead_of_asRead` at a
representative (`copyCtor_repr`).  Hence ψ⁻¹ is TYPED
(`InvSetup.fold_mem`) and FIRING (`InvSetup.fold_iota`) end to end. -/
theorem invSetup_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env),
      ConLeche.auxBlock p st = some b ∧
      st.types.length = p.k + st.pins.length ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧
        ∃ (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta)),
        (ContainersRep env envAux mpAux.base2 → ∀ ψ : Name → Nat,
          ∃ cd : Nat → CopyData V,
            (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) ∧
            (CopyCtorsRead mpAux d ψ st p.k st.pins.length cd →
              d.elimL.eval ψ = d.w ψ →
              ∀ t₀, t₀ < b.k → d.memberCtors t₀ ≠ [] →
              ∃ (s : Level) (lps lpsT : List Name),
                (∀ φ : Name → Nat, s.eval φ = d.resSort.eval φ) ∧
                ∀ (ρ : Nat → V) (ps : List AnnotTerm), ps.length = d.nP →
                  (∀ q ∈ ps, WellDenotedV V ρ q) →
                  SpineFit ρ (d.params ψ) (ps.map (interp V ρ)) →
                  ({d with resSort := s} : IndRepData V).InvSetup mpAux lps lpsT ψ ρ ps
                    (d.invL mpAux.base2 ψ p.k cd) (d.invPinsT p.k cd)
                    (d.invHead mpAux.base2 ψ st.pins.length cd (auxOfsOf st p.k cd))
                    (d.invUseIh p.k))) := by
  obtain ⟨st, b, envAux, params, pbs, fmsA, ctorsA, stored, order, hb, -, -, hlenSt, -, -, -, -, -,
    -, -, -, -, -, -, -, -, -, mpAux, d, hreps, hchk, -, hpins⟩ := pinFacts_of_run hμ mp hE h
  refine ⟨st, b, envAux, hb, hlenSt, mpAux, d, hreps, hchk, params, pbs, ?_⟩
  intro hcr ψ
  obtain ⟨cd, hcd⟩ := hpins hcr ψ
  refine ⟨cd, hcd, ?_⟩
  exact invSetup_of_pinFacts hreps hchk hb hlenSt hcd

end ConLeche.Model

