import ConLeche.Semantics.Tower.SumRecCase

/-!
# The sum recursor leaf (task #175 sum-types, stage S4b; indexed)

`directSumRecAV ℓ w rds Fss Ess srcs nIdx = mkLamsC ℓ rds (sumRecBodyAV …)` —
the constant-bit λ-tower (bit `ℓ`) over the recursor type reading's
binder data (parameters, motive, one minor per constructor, the
`nIdx` index binders, major), whose body sits one binder below the
K-frame `(p⃗, motive, minors, ı⃗)` and is, in the **graph regime**, the
case recursor (`caseRecAV`, stage `0`, depth `1`) on the major's tag
applied to the major's payload:

    sumRecBodyAV = (caseRec 0 (t.0)) (t.1)        t = bvar 0

and at a **squash instantiation** (`w = 0`, task #175 indexed) the
first minor applied to the fields' SOURCES — an index variable for a
field that is one of the constructor's index expressions, the point
for a proof field (`srcAV`): the squashed value carries no field, so
the recursor reads the data fields off the index arguments, which is
official's subsingleton elimination (`Eq`'s large eliminator).  A
squash body with no constructor is the point.

`sumRecBody_facts` gives the body's grading and its membership in
`M ı⃗ t` at every carrier member (the graph regime through the case
recursor's stage-`0` motive; the squash regime through the minors'
inhabitation at a zero elimination level, and through the sources'
fit when the elimination level is nonzero — then there is exactly one
constructor and the sources ARE the witness's fields, `SqHypS.hsrc`),
and `sumRecBody_iota` the iota: at `t = inj j (mkTower (f⃗ ++ [pt]))`
the body is minor `j` folded along `f⃗`.  The leaf's ONE hereditary
premise is `RecPreS` — the parameter walk ending in `RecBaseS`: the
motive entry graded, and under every motive, minor and index the
major entry reads to the carrier and the K-frame satisfies `RecHypS`
and `SqHypS` — and `underTowerOk_of_recPreS` turns it into the
tower's premise.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The sources -/

/-- A field's source at depth `D'` below the K-frame: the index
variable it occurs as, or the point. -/
def srcAV (nIdx D' : Nat) : Option Nat → AVExpr
  | some l => .bvar (D' + nIdx - 1 - l)
  | none => .prf

/-- The sources' values at an index tuple. -/
noncomputable def srcVals (is : List V) (src : List (Option Nat)) : List V :=
  src.map fun s => match s with
    | some l => is.getD l pt
    | none => pt

theorem srcAV_ok2 (nIdx D' : Nat) (s : Option Nat) (σ : Nat → V) : AnnotOk2 V σ (srcAV nIdx D' s) := by
  cases s <;> trivial

/-- The sources read to their values at the frame. -/
theorem map_srcAV_interp {nIdx D' : Nat} {ρ₀ σ : Nat → V} (h : RecFrameS D' ρ₀ σ)
    (src : List (Option Nat)) (hsrc : ∀ s ∈ src, ∀ l, s = some l → l < nIdx) :
    (src.map (srcAV nIdx D')).map (interp2 V σ) = srcVals (frameIdx nIdx ρ₀) src := by
  unfold srcVals
  rw [List.map_map]
  apply List.map_congr_left
  intro s hs
  cases s with
  | none => rfl
  | some l =>
    simp only [Function.comp_def, srcAV, interp2_bvar]
    exact h.idx (hsrc _ hs l rfl)

/-- The squash-regime body at depth `1`: the first minor at the
sources, the point without constructors. -/
def sqRecBodyAV (nIdx : Nat) (srcs : List (List (Option Nat))) : Nat → AVExpr
  | 0 => .prf
  | n + 1 => AVExpr.mkAppN (.bvar (1 + nIdx + (n + 1) - 1 - 0))
      ((srcs.getD 0 []).map (srcAV nIdx 1))

/-- The recursor body at depth `1` below the K-frame, both regimes. -/
def sumRecBodyAV (ℓ w : Nat) (Fss Ess : List (List AVExpr)) (srcs : List (List (Option Nat)))
    (nIdx : Nat) : AVExpr :=
  if w = 0 then sqRecBodyAV nIdx srcs Fss.length
  else .app (caseRecAV ℓ w (rChains (nIdx + Fss.length + 1) nIdx Fss Ess)
      (fun j => (Fss.getD j []).length) Fss.length nIdx Fss.length 1 0 (.proj 0 (.bvar 0)))
    (.proj 1 (.bvar 0))

theorem sumRecBodyAV_zero (ℓ : Nat) (Fss Ess : List (List AVExpr)) (srcs : List (List (Option Nat)))
    (nIdx : Nat) : sumRecBodyAV ℓ 0 Fss Ess srcs nIdx = sqRecBodyAV nIdx srcs Fss.length := if_pos rfl

theorem sumRecBodyAV_pos {w : Nat} (hw : w ≠ 0) (ℓ : Nat) (Fss Ess : List (List AVExpr))
    (srcs : List (List (Option Nat))) (nIdx : Nat) :
    sumRecBodyAV ℓ w Fss Ess srcs nIdx
      = .app (caseRecAV ℓ w (rChains (nIdx + Fss.length + 1) nIdx Fss Ess)
          (fun j => (Fss.getD j []).length) Fss.length nIdx Fss.length 1 0 (.proj 0 (.bvar 0)))
        (.proj 1 (.bvar 0)) := if_neg hw

/-- The recursor leaf. -/
def directSumRecAV (ℓ w : Nat) (rds : List (Nat × Nat × AVExpr)) (Fss Ess : List (List AVExpr))
    (srcs : List (List (Option Nat))) (nIdx : Nat) : AVExpr :=
  mkLamsC ℓ rds (sumRecBodyAV ℓ w Fss Ess srcs nIdx)

/-- The squash-regime hypotheses at the K-frame: the sources' counts,
the elimination restriction, and — at a nonzero elimination level —
the sources are the fields of any fitting spine at the frame's index
tuple. -/
structure SqHypS (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr)
    (srcs : List (List (Option Nat))) : Prop where
  hsrclen : ∀ j, j < Fss.length → (srcs.getD j []).length = (Fss.getD j []).length
  hsrcbnd : ∀ j, j < Fss.length → ∀ s ∈ srcs.getD j [], ∀ l, s = some l → l < Ids.length
  hwl : w = 0 → ℓ ≠ 0 → Fss.length ≤ 1
  hsrc : w = 0 → ℓ ≠ 0 → ∀ j, j < Fss.length → ∀ bs : List V,
    SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j []) bs →
    idxValsAt (frP Fss.length Ids.length ρ₀) (Ess.getD j []) bs = frameIdx Ids.length ρ₀ →
    bs = srcVals (frameIdx Ids.length ρ₀) (srcs.getD j [])

/-! ## The major's projections -/

/-- The major's tag and payload nodes are graded (graph regime)
through the carrier's own `sigmaSet`. -/
theorem major_proj_ok2 {w : Nat} (hw : w ≠ 0) {ρ₀ σ : Nat → V} {Fss' : List (List AVExpr)}
    (hok : SumFieldsOkB w ρ₀ Fss') (ht : σ 0 ∈ˢ sumSet w (sumFibre w ρ₀ Fss')) {i : Nat}
    (hi : i < 2) : AnnotOk2 V σ (.proj i (.bvar 0)) := by
  rw [AnnotOk2_proj]
  refine ⟨trivial, hi, w, w, omega, natFibre (sumFibre w ρ₀ Fss'), ?_, omega_mem_univ_pos hw, ?_⟩
  · rw [interp2_bvar, show Nat.max w w = w from Nat.max_self w]
    exact ht
  · intro k hk
    obtain ⟨i', rfl, hfib⟩ := natFibre_of_mem (sumFibre w ρ₀ Fss') hk
    rw [hfib]
    unfold sumFibre
    cases hi' : Fss'[i']? with
    | none => exact empty_mem_univ w
    | some Fs =>
      exact towerSet_univ_teleOfFields ((hok Fs (List.mem_of_getElem? hi')).toBound hw)

/-- A fit of values graded by their arguments. -/
theorem argsOkFit_of_values {σ : Nat → V} :
    ∀ {args Fs : List AVExpr} {ρf : Nat → V},
      (∀ a ∈ args, AnnotOk2 V σ a) → SpineFit ρf Fs (args.map (interp2 V σ)) →
      ArgsOkFit σ args Fs ρf
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim
  | a :: _, _ :: _, _, hok, hsp =>
    ⟨hok a List.mem_cons_self, hsp.1,
      argsOkFit_of_values (fun a' ha' => hok a' (List.mem_cons_of_mem _ ha')) hsp.2⟩

/-! ## The body -/

/-- **The recursor body's facts** at a carrier member: graded, and in
the motive (at the frame's indices) at the major. -/
theorem sumRecBody_facts {ℓ w : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V} {srcs : List (List (Option Nat))}
    (hfr : RecFrameS 1 ρ₀ σ)
    (hyp : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) (hsq : SqHypS ℓ w ρ₀ Fss Ess Ids srcs)
    (ht : σ 0 ∈ˢ sumSet w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))) :
    AnnotOk2 V σ (sumRecBodyAV ℓ w Fss Ess srcs Ids.length) ∧
    interp2 V σ (sumRecBodyAV ℓ w Fss Ess srcs Ids.length)
      ∈ˢ SetTheory.app (frMi Fss.length Ids.length ρ₀) (σ 0) := by
  by_cases hw : w = 0
  · -- the squash regime
    subst hw
    rw [sumRecBodyAV_zero]
    obtain ⟨hpt, i, a, ha⟩ := sumSet_zero_elim ht
    have hi : i < Fss.length := by
      rcases Nat.lt_or_ge i Fss.length with h | h
      · exact h
      · exfalso
        rw [sumFibre_of_ge (by rw [hyp.rChains_length']; exact h)] at ha
        exact not_mem_empty a ha
    -- the witness: constructor `i`'s fields at the frame's index tuple
    rw [sumFibre_of_getElem? (hyp.rChain_getElem? hi)] at ha
    obtain ⟨-, bs, hspL, hall⟩ := restricted_member_zero ha
    have hspP : SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD i []) bs :=
      (spineFit_liftFields _).mp hspL
    have hidx : idxValsAt (frP Fss.length Ids.length ρ₀) (Ess.getD i []) bs = frameIdx Ids.length ρ₀ :=
      (EqAll_idxEqsAt (hyp.hEs i hi) hspP.length_eq).mp hall
    have hconc : concI 0 (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD i []) i bs
        = SetTheory.app (frMi Fss.length Ids.length ρ₀) pt := by
      unfold concI ctorValI frMi
      rw [hidx, if_pos rfl]
    obtain ⟨n', hn'⟩ : ∃ n', Fss.length = n' + 1 := ⟨Fss.length - 1, by omega⟩
    have hbodyeq : sqRecBodyAV Ids.length srcs Fss.length
        = AVExpr.mkAppN (.bvar (1 + Ids.length + Fss.length - 1 - 0))
            ((srcs.getD 0 []).map (srcAV Ids.length 1)) := by
      rw [hn']; rfl
    rw [hbodyeq]
    have hminor : σ (1 + Ids.length + Fss.length - 1 - 0) = frMs Fss.length Ids.length ρ₀ 0 :=
      hfr.minor (n := Fss.length) (nIdx := Ids.length) (j := 0) (by omega)
    have hargsok : ∀ a ∈ (srcs.getD 0 []).map (srcAV Ids.length 1), AnnotOk2 V σ a := by
      intro a ha
      obtain ⟨s, -, rfl⟩ := List.mem_map.mp ha
      exact srcAV_ok2 _ _ _ _
    have hvals := map_srcAV_interp hfr (srcs.getD 0 []) (hsq.hsrcbnd 0 (by omega))
    by_cases h0 : ℓ = 0
    · -- a zero elimination level: the minor is the point, the motive at
      -- the point is inhabited by the witness
      have hmpt : frMs Fss.length Ids.length ρ₀ 0 = pt := hyp.minor_pt h0 (by omega)
      have hpt' := mkAppN_ok2_of_pt_head (f := .bvar (1 + Ids.length + Fss.length - 1 - 0)) (σ := σ)
        trivial (by rw [interp2_bvar, hminor, hmpt]) hargsok
      refine ⟨hpt'.1, ?_⟩
      rw [hpt'.2, hpt]
      obtain ⟨v, hv⟩ := minorSpI_zero_inhab (h0 ▸ hyp.hms i hi) hspP
      rw [List.nil_append, hconc] at hv
      have hv' : v = pt := eq_pt_of_mem_univZero (hyp.hM0 h0 _) hv
      subst hv'
      exact hv
    · -- a nonzero elimination level: one constructor, the sources are
      -- the witness's fields
      have hn1 : Fss.length ≤ 1 := hsq.hwl rfl h0
      have hi0 : i = 0 := by omega
      subst hi0
      have hbs : bs = srcVals (frameIdx Ids.length ρ₀) (srcs.getD 0 []) :=
        hsq.hsrc rfl h0 0 (by omega) bs hspP hidx
      have hfit : ArgsOkFit σ ((srcs.getD 0 []).map (srcAV Ids.length 1)) (Fss.getD 0 [])
          (frP Fss.length Ids.length ρ₀) := by
        refine argsOkFit_of_values hargsok ?_
        rw [hvals, ← hbs]; exact hspP
      have hsp := minorSpI_spine (V := V) (fun h => absurd h h0) (Fs := Fss.getD 0 [])
        (args := (srcs.getD 0 []).map (srcAV Ids.length 1)) (ρf := frP Fss.length Ids.length ρ₀)
        (acc := []) (f := .bvar (1 + Ids.length + Fss.length - 1 - 0)) (σ := σ) trivial
        (by rw [interp2_bvar, hminor]; exact hyp.hms 0 (by omega)) hfit
      refine ⟨hsp.1, ?_⟩
      have h := hsp.2
      rw [List.nil_append, hvals, ← hbs, hconc, ← hpt] at h
      exact h
  · -- the graph regime: the major is an injection
    rw [sumRecBodyAV_pos hw]
    generalize hR : rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess = Fss' at *
    have hok : SumFieldsOkB w ρ₀ Fss' := hR ▸ hyp.hok
    have hcase := caseRec_facts hw hyp Fss.length (D := 1) (j := 0) (σ := σ)
      (k := .proj 0 (.bvar 0)) hfr (Nat.zero_add _)
    rw [hR] at hcase
    have hok0 := major_proj_ok2 hw hok ht (i := 0) (by omega)
    have hok1 := major_proj_ok2 hw hok ht (i := 1) (by omega)
    obtain ⟨i, a, ha, hta⟩ := sumSet_elim hw ht
    have htag : interp2 V σ (.proj 0 (.bvar 0)) = vnat i := by
      rw [interp2_proj, if_pos rfl, interp2_bvar, hta, sfst_inj]
    have hpay : interp2 V σ (.proj 1 (.bvar 0)) = a := by
      rw [interp2_proj, if_neg Nat.one_ne_zero, interp2_bvar, hta, ssnd_inj]
    have hkω : interp2 V σ (.proj 0 (.bvar 0)) ∈ˢ (omega : V) := by
      rw [htag]; exact vnat_mem_omega i
    obtain ⟨hmem, -⟩ := hcase.1 hkω
    rw [htag, motSem_vnat, Nat.zero_add] at hmem
    have hB0 : ℓ = 0 → ∀ y, y ∈ˢ sumFibre w ρ₀ Fss' i →
        SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w i y) ∈ˢ (univZero : V) :=
      fun h0 y _ => hyp.hM0 h0 _
    refine ⟨?_, ?_⟩
    · show AnnotOk2 V σ (.app _ _)
      rw [AnnotOk2_app]
      refine ⟨hcase.2 hok0 (fun _ => hkω), hok1, ℓ, sumFibre w ρ₀ Fss' i, _, hmem, ?_, hB0⟩
      rw [hpay]; exact ha
    · show SetTheory.app (interp2 V σ (caseRecAV ℓ w Fss' _ _ _ _ 1 0 (.proj 0 (.bvar 0))))
        (interp2 V σ (.proj 1 (.bvar 0))) ∈ˢ _
      rw [hpay]
      have := app_mem_piR hmem ha hB0
      rwa [injW_pos hw, ← hta] at this

theorem foldl_app_pt_sum : ∀ (ts : List V), ts.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | t :: ts => by rw [List.foldl_cons, app_pt]; exact foldl_app_pt_sum ts

/-- **The body's iota** (graph regime): at the injection of constructor
`j`'s point-terminated tupler the body is minor `j` folded along the
fields. -/
theorem sumRecBody_iota {ℓ w : Nat} (hw : w ≠ 0) {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V} {srcs : List (List (Option Nat))}
    (hfr : RecFrameS 1 ρ₀ σ) (hyp : RecHypS ℓ w ρ₀ Fss Ess Ids famAt) {j : Nat}
    (hj : j < Fss.length) {bs : List V} (hlen : bs.length = (Fss.getD j []).length)
    (hmaj : σ 0 = inj j (mkTower (bs ++ [pt])))
    (hbs : mkTower (bs ++ [pt])
      ∈ˢ sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j) :
    interp2 V σ (sumRecBodyAV ℓ w Fss Ess srcs Ids.length)
      = bs.foldl SetTheory.app (frMs Fss.length Ids.length ρ₀ j) := by
  rw [sumRecBodyAV_pos hw]
  have hcase := caseRec_facts hw hyp Fss.length (D := 1) (j := 0) (σ := σ)
    (k := .proj 0 (.bvar 0)) hfr (Nat.zero_add _)
  have htag : interp2 V σ (.proj 0 (.bvar 0)) = vnat j := by
    rw [interp2_proj, if_pos rfl, interp2_bvar, hmaj, sfst_inj]
  have hpay : interp2 V σ (.proj 1 (.bvar 0)) = mkTower (bs ++ [pt]) := by
    rw [interp2_proj, if_neg Nat.one_ne_zero, interp2_bvar, hmaj, ssnd_inj]
  have hkω : interp2 V σ (.proj 0 (.bvar 0)) ∈ˢ (omega : V) := by
    rw [htag]; exact vnat_mem_omega j
  have hsel := (hcase.1 hkω).2 j htag hj
  rw [Nat.zero_add] at hsel
  show SetTheory.app (interp2 V σ (caseRecAV ℓ w _ _ _ _ _ 1 0 (.proj 0 (.bvar 0))))
    (interp2 V σ (.proj 1 (.bvar 0))) = _
  rw [hsel, hpay]
  unfold baseSem
  by_cases h0 : ℓ = 0
  · rw [h0, lamR_zero, app_pt, hyp.minor_pt h0 hj]
    exact (foldl_app_pt_sum bs).symm
  · rw [app_lamR_pos h0 hbs]
    congr 1
    -- the first `nF` projections of the point-terminated tuple are the fields
    rw [← projList_eq_map_range, ← hlen]
    apply List.ext_getElem
    · rw [projList_length]
    · intro i h1 h2
      rw [projList_get _ _ _ (by rwa [projList_length] at h1)]
      have := projS_mkTower i (bs ++ [pt]) (by simp; omega)
      rw [this, List.getElem_append_left h2]

/-- **The body's iota at a squash instantiation with a nonzero
elimination level**: the sources are the fields. -/
theorem sumRecBody_iota_sq {ℓ : Nat} (h0 : ℓ ≠ 0) {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {srcs : List (List (Option Nat))}
    (hfr : RecFrameS 1 ρ₀ σ) (hsq : SqHypS ℓ 0 ρ₀ Fss Ess Ids srcs)
    (hn : 0 < Fss.length) {bs : List V}
    (hspP : SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD 0 []) bs)
    (hidx : idxValsAt (frP Fss.length Ids.length ρ₀) (Ess.getD 0 []) bs = frameIdx Ids.length ρ₀) :
    interp2 V σ (sumRecBodyAV ℓ 0 Fss Ess srcs Ids.length)
      = bs.foldl SetTheory.app (frMs Fss.length Ids.length ρ₀ 0) := by
  rw [sumRecBodyAV_zero]
  obtain ⟨n', hn'⟩ : ∃ n', Fss.length = n' + 1 := ⟨Fss.length - 1, by omega⟩
  have hbodyeq : sqRecBodyAV Ids.length srcs Fss.length
      = AVExpr.mkAppN (.bvar (1 + Ids.length + Fss.length - 1 - 0))
          ((srcs.getD 0 []).map (srcAV Ids.length 1)) := by
    rw [hn']; rfl
  have hminor : σ (1 + Ids.length + Fss.length - 1 - 0) = frMs Fss.length Ids.length ρ₀ 0 :=
    hfr.minor (n := Fss.length) (nIdx := Ids.length) (j := 0) (by omega)
  have hbs : bs = srcVals (frameIdx Ids.length ρ₀) (srcs.getD 0 []) :=
    hsq.hsrc rfl h0 0 hn bs hspP hidx
  have hvals := map_srcAV_interp hfr (srcs.getD 0 []) (hsq.hsrcbnd 0 hn)
  rw [hbodyeq, interp2_mkAppN, ← List.foldl_map (f := interp2 V σ) (g := SetTheory.app),
    hvals, interp2_bvar, hminor, hbs]

/-! ## The hereditary premise -/

/-- The walk down the index entries, ending at the major: at the
K-frame the major entry reads to the carrier and the two hypothesis
records hold. -/
def RecIdxS (ℓ w : Nat) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr) (famAt : List V → V)
    (srcs : List (List (Option Nat))) (dt : Nat × Nat × AVExpr) :
    List (Nat × Nat × AVExpr) → (Nat → V) → Prop
  | [], σ => AnnotOk2 V σ dt.2.2 ∧
      interp2 V σ dt.2.2 = sumSet w (sumFibre w σ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) ∧
      RecHypS ℓ w σ Fss Ess Ids famAt ∧ SqHypS ℓ w σ Fss Ess Ids srcs
  | d :: dis, σ => AnnotOk2 V σ d.2.2 ∧
      ∀ i, i ∈ˢ interp2 V σ d.2.2 → RecIdxS ℓ w Fss Ess Ids famAt srcs dt dis (cons i σ)

/-- The walk down the minor entries, then the index entries. -/
def RecTailS (ℓ w : Nat) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr) (famAt : List V → V)
    (srcs : List (List (Option Nat))) (dis : List (Nat × Nat × AVExpr)) (dt : Nat × Nat × AVExpr) :
    List (Nat × Nat × AVExpr) → (Nat → V) → Prop
  | [], σ => RecIdxS ℓ w Fss Ess Ids famAt srcs dt dis σ
  | d :: dms, σ => AnnotOk2 V σ d.2.2 ∧
      ∀ m, m ∈ˢ interp2 V σ d.2.2 → RecTailS ℓ w Fss Ess Ids famAt srcs dis dt dms (cons m σ)

/-- The recursor's post-parameter phase facts. -/
structure RecBaseS (ℓ w : Nat) (ρp : Nat → V) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr)
    (famAt : List V → V) (srcs : List (List (Option Nat)))
    (dM : Nat × Nat × AVExpr) (dms dis : List (Nat × Nat × AVExpr)) (dt : Nat × Nat × AVExpr) :
    Prop where
  hlen : dms.length = Fss.length
  hlenI : dis.length = Ids.length
  okM : AnnotOk2 V ρp dM.2.2
  tail : ∀ M, M ∈ˢ interp2 V ρp dM.2.2 → RecTailS ℓ w Fss Ess Ids famAt srcs dis dt dms (cons M ρp)

/-- `RecPreS`: the parameter walk ending in `RecBaseS`. -/
def RecPreS (ℓ w : Nat) (ρ : Nat → V) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr)
    (famAt : (Nat → V) → List V → V) (srcs : List (List (Option Nat)))
    (dM : Nat × Nat × AVExpr) (dms dis : List (Nat × Nat × AVExpr)) (dt : Nat × Nat × AVExpr) :
    List (Nat × Nat × AVExpr) → Prop
  | [] => RecBaseS ℓ w ρ Fss Ess Ids (famAt ρ) srcs dM dms dis dt
  | d :: pds => AnnotOk2 V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp2 V ρ d.2.2 → RecPreS ℓ w (cons a ρ) Fss Ess Ids famAt srcs dM dms dis dt pds

/-- The conclusion `motive ı⃗ t` spelled at the body frame. -/
def recConcAV (n nIdx : Nat) : AVExpr := .app (motAppAV n nIdx 1) (.bvar 0)

/-- The base of the walk: at the K-frame, the tower's premise over
the major entry. -/
theorem underTowerOk_at_major {ℓ w : Nat} {ρ₀ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V} {srcs : List (List (Option Nat))}
    {dt : Nat × Nat × AVExpr}
    (h : RecIdxS ℓ w Fss Ess Ids famAt srcs dt [] ρ₀) :
    UnderTowerOk ℓ ρ₀ (sumRecBodyAV ℓ w Fss Ess srcs Ids.length) (recConcAV Fss.length Ids.length) [dt] := by
  obtain ⟨hokt, hteq, hyp, hsq⟩ := h
  refine ⟨hokt, fun t ht => ?_⟩
  rw [hteq] at ht
  have hfr : RecFrameS 1 ρ₀ (cons t ρ₀) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  have ht' : cons t ρ₀ 0 ∈ˢ sumSet w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) := ht
  have hfacts := sumRecBody_facts hfr hyp hsq ht'
  obtain ⟨hMv, -⟩ := motApp_facts hfr hyp.toRecHypCore
  refine ⟨hfacts.1, ?_, ?_⟩
  · show interp2 V (cons t ρ₀) (sumRecBodyAV ℓ w Fss Ess srcs Ids.length)
      ∈ˢ interp2 V (cons t ρ₀) (.app (motAppAV Fss.length Ids.length 1) (.bvar 0))
    rw [interp2_app, hMv, interp2_bvar]
    exact hfacts.2
  · intro h0
    show interp2 V (cons t ρ₀) (.app (motAppAV Fss.length Ids.length 1) (.bvar 0)) ∈ˢ _
    rw [interp2_app, hMv, interp2_bvar]
    exact hyp.hM0 h0 t

/-- The walk down the index entries. -/
theorem underTowerOk_of_recIdx {ℓ w : Nat} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : List V → V} {srcs : List (List (Option Nat))} {dt : Nat × Nat × AVExpr} :
    ∀ {dis : List (Nat × Nat × AVExpr)} {σ : Nat → V},
      RecIdxS ℓ w Fss Ess Ids famAt srcs dt dis σ →
      UnderTowerOk ℓ σ (sumRecBodyAV ℓ w Fss Ess srcs Ids.length) (recConcAV Fss.length Ids.length)
        (dis ++ [dt])
  | [], _, h => underTowerOk_at_major h
  | _ :: _, _, h => ⟨h.1, fun i hi => underTowerOk_of_recIdx (h.2 i hi)⟩

/-- The walk down the minor entries. -/
theorem underTowerOk_of_recTail {ℓ w : Nat} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : List V → V} {srcs : List (List (Option Nat))} {dis : List (Nat × Nat × AVExpr)}
    {dt : Nat × Nat × AVExpr} :
    ∀ {dms : List (Nat × Nat × AVExpr)} {σ : Nat → V},
      RecTailS ℓ w Fss Ess Ids famAt srcs dis dt dms σ →
      UnderTowerOk ℓ σ (sumRecBodyAV ℓ w Fss Ess srcs Ids.length) (recConcAV Fss.length Ids.length)
        (dms ++ dis ++ [dt])
  | [], _, h => by simpa using underTowerOk_of_recIdx h
  | _ :: _, _, h => ⟨h.1, fun m hm => underTowerOk_of_recTail (h.2 m hm)⟩

/-- **The recursor leaf's `UnderTowerOk`** from `RecPreS`. -/
theorem underTowerOk_of_recPreS {ℓ w : Nat} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : (Nat → V) → List V → V} {srcs : List (List (Option Nat))}
    {dM : Nat × Nat × AVExpr} {dms dis : List (Nat × Nat × AVExpr)} {dt : Nat × Nat × AVExpr} :
    ∀ {pds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      RecPreS ℓ w ρ Fss Ess Ids famAt srcs dM dms dis dt pds →
      UnderTowerOk ℓ ρ (sumRecBodyAV ℓ w Fss Ess srcs Ids.length) (recConcAV Fss.length Ids.length)
        (pds ++ [dM] ++ dms ++ dis ++ [dt])
  | d :: pds, ρ, h =>
    ⟨h.1, fun a ha => underTowerOk_of_recPreS (h.2 a ha)⟩
  | [], ρp, h => by
    refine ⟨h.okM, fun M hM => ?_⟩
    have := underTowerOk_of_recTail (h.tail M hM)
    simpa using this

/-- **The recursor leaf inhabits its type's reading.** -/
theorem directSumRecAV_mem {ℓ w : Nat} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : (Nat → V) → List V → V} {srcs : List (List (Option Nat))} {ρ : Nat → V}
    {pds : List (Nat × Nat × AVExpr)} {dM : Nat × Nat × AVExpr} {dms dis : List (Nat × Nat × AVExpr)}
    {dt : Nat × Nat × AVExpr}
    (hz : ∀ d ∈ pds ++ [dM] ++ dms ++ dis ++ [dt], (ℓ = 0 ↔ d.2.1 = 0))
    (hpre : RecPreS ℓ w ρ Fss Ess Ids famAt srcs dM dms dis dt pds) :
    interp2 V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ dis ++ [dt]) Fss Ess srcs Ids.length)
      ∈ˢ interp2 V ρ (mkPisAV (pds ++ [dM] ++ dms ++ dis ++ [dt]) (recConcAV Fss.length Ids.length)) :=
  mkLamsC_mem hz (underTowerOk_of_recPreS hpre)

/-- **The recursor leaf is graded.** -/
theorem directSumRecAV_ok2 {ℓ w : Nat} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
    {famAt : (Nat → V) → List V → V} {srcs : List (List (Option Nat))} {ρ : Nat → V}
    {pds : List (Nat × Nat × AVExpr)} {dM : Nat × Nat × AVExpr} {dms dis : List (Nat × Nat × AVExpr)}
    {dt : Nat × Nat × AVExpr}
    (hz : ∀ d ∈ pds ++ [dM] ++ dms ++ dis ++ [dt], (ℓ = 0 ↔ d.2.1 = 0))
    (hpre : RecPreS ℓ w ρ Fss Ess Ids famAt srcs dM dms dis dt pds) :
    AnnotOk2 V ρ (directSumRecAV ℓ w (pds ++ [dM] ++ dms ++ dis ++ [dt]) Fss Ess srcs Ids.length) :=
  mkLamsC_ok2 hz (underTowerOk_of_recPreS hpre)

end ConLeche.Semantics
