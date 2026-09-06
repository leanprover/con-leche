import Lech.Semantics.Tower.SumRecCase
import Lech.Semantics.Tower.FixLeaf

/-!
# The recursive recursor's case split, spelled (task #188)

The one-step unfolding of a recursive type's recursor is the sum
route's case split (`Lech/Semantics/Tower/SumRecCase.lean`) with the
**inductive hypotheses** supplied: constructor `j`'s branch is

    λ (y : T_j), m_j (y.0) … (y.(nF-1)) (r (y.i₁)) … (r (y.i_m))

where `r` — the function being unfolded, a binder ABOVE the case split
(at `bvar (D - 1)` at depth `D` below the K-frame; the spelling of the
step is `λ r t. case …` at the K-frame, so `r` sits one binder below
the K-frame and the split starts at depth `2`) — is applied to the recursive components
`i₁ < … < i_m` of the payload (`recIdx`).  The stage motives, the
`Nat.rec` tower and the frame arithmetic are the sum route's verbatim
(`caseMotiveAV`, `motive_facts`); only the branch changes
(`caseBaseAVR`, `base_factsR`) and the facts are re-run
(`caseRec_factsR`).

The minors' spaces are the sum route's `minorSpI` with the conclusion
replaced by the **ih tower** `ihSp`: the Π-tower over `M (f_{i})` for
the recursive components, ending in the motive at the constructor's
value (`RecHypR.hms`).  The value of `r` is a frame datum (`rV`), a
member of `Π (t : T), M t`; the branch's ihs land in `M (f_i)` because
the recursive components of a payload are carrier members
(`RecHypR.hrecT`: the real chain's recursive domains read to the
carrier at every prefix).
-/

namespace Lech.Semantics
open Lech.SetModel

open SetTheory
open Lech.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The recursive positions and the ih tower -/

/-- The recursive positions among the first `k` fields. -/
def recIdx (rs : List Bool) (k : Nat) : List Nat :=
  (List.range k).filter fun i => rs.getD i false

theorem mem_recIdx {rs : List Bool} {k i : Nat} :
    i ∈ recIdx rs k ↔ i < k ∧ rs.getD i false = true := by
  unfold recIdx
  rw [List.mem_filter, List.mem_range]

/-- The ih tower: the (non-dependent) Π-tower over the motive at the
recursive components of `fs`, ending in `C`. -/
noncomputable def ihSp (ℓ : Nat) (M : V) (fs : List V) (C : V) : List Nat → V
  | [] => C
  | i :: is => piR ℓ (SetTheory.app M (fs.getD i pt)) fun _ => ihSp ℓ M fs C is

theorem ihSp_zero_univZero {ℓ : Nat} {M : V} {fs : List V} {C : V} (h0 : ℓ = 0)
    (hC : C ∈ˢ (univZero : V)) : ∀ is, ihSp ℓ M fs C is ∈ˢ (univZero : V)
  | [] => hC
  | _ :: _ => by
    show piR ℓ _ _ ∈ˢ _
    rw [h0]
    exact piR_zero_mem_univZero

/-- The graded fold of an ih-tower member along graded ih arguments. -/
theorem ihSp_spine {ℓ : Nat} {M : V} {fs : List V} {C : V} (hC0 : ℓ = 0 → C ∈ˢ (univZero : V)) :
    ∀ {is : List Nat} {args : List AVExpr} {f : AVExpr} {σ : Nat → V},
      AnnotOk2 V σ f → interp2 V σ f ∈ˢ ihSp ℓ M fs C is →
      args.length = is.length →
      (∀ l, l < is.length → AnnotOk2 V σ (args.getD l default) ∧
        interp2 V σ (args.getD l default) ∈ˢ SetTheory.app M (fs.getD (is.getD l 0) pt)) →
      (ℓ = 0 → ∀ i ∈ is, SetTheory.app M (fs.getD i pt) ∈ˢ (univZero : V)) →
      AnnotOk2 V σ (AVExpr.mkAppN f args) ∧ interp2 V σ (AVExpr.mkAppN f args) ∈ˢ C
  | [], [], _, _, hokf, hmf, _, _, _ => ⟨hokf, hmf⟩
  | [], _ :: _, _, _, _, _, hlen, _, _ => nomatch hlen
  | _ :: _, [], _, _, _, _, hlen, _, _ => nomatch hlen
  | i :: is, a :: args, f, σ, hokf, hmf, hlen, hargs, hz => by
    have hB0 : ℓ = 0 → ∀ x, x ∈ˢ SetTheory.app M (fs.getD i pt) →
        ihSp ℓ M fs C is ∈ˢ (univZero : V) :=
      fun h0 _ _ => ihSp_zero_univZero h0 (hC0 h0) is
    have h0 := hargs 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    have happ : SetTheory.app (interp2 V σ f) (interp2 V σ a) ∈ˢ ihSp ℓ M fs C is :=
      app_mem_piR hmf h0.2 hB0
    have hoka : AnnotOk2 V σ (.app f a) := by
      rw [AnnotOk2_app]
      exact ⟨hokf, h0.1, ℓ, _, _, hmf, h0.2, hB0⟩
    rw [AVExpr.mkAppN_cons]
    refine ihSp_spine hC0 (is := is) (args := args) hoka happ (by simpa using hlen) ?_
      (fun h0 i hi => hz h0 i (List.mem_cons_of_mem _ hi))
    intro l hl
    have := hargs (l + 1) (by simpa using hl)
    simpa only [List.getD_cons_succ] using this

/-- The semantic fold of an ih-tower member along ih values. -/
theorem ihSp_fold {ℓ : Nat} {M : V} {fs : List V} {C : V} (hC0 : ℓ = 0 → C ∈ˢ (univZero : V))
    (g : V → V) :
    ∀ {is : List Nat} {x : V}, x ∈ˢ ihSp ℓ M fs C is →
      (∀ i ∈ is, g (fs.getD i pt) ∈ˢ SetTheory.app M (fs.getD i pt)) →
      (is.map fun i => g (fs.getD i pt)).foldl SetTheory.app x ∈ˢ C
  | [], x, hx, _ => hx
  | i :: is, x, hx, hg => by
    rw [List.map_cons, List.foldl_cons]
    refine ihSp_fold hC0 g (is := is) ?_ (fun i hi => hg i (List.mem_cons_of_mem _ hi))
    exact app_mem_piR hx (hg i List.mem_cons_self)
      (fun h0 _ _ => ihSp_zero_univZero h0 (hC0 h0) is)

omit [SetTheory V] in
theorem AVExpr.mkAppN_append (f : AVExpr) :
    ∀ (as bs : List AVExpr), AVExpr.mkAppN f (as ++ bs) = AVExpr.mkAppN (AVExpr.mkAppN f as) bs
  | [], _ => rfl
  | a :: as, bs => by
    rw [List.cons_append, AVExpr.mkAppN_cons, AVExpr.mkAppN_cons]
    exact AVExpr.mkAppN_append (.app f a) as bs

/-- The `l`-th value of a fitting spine is in the `l`-th domain at the
prefix. -/
theorem spineFit_getD_mem {ρ : Nat → V} :
    ∀ {Fs : List AVExpr} {as : List V} {l : Nat}, SpineFit ρ Fs as → l < Fs.length →
      as.getD l pt ∈ˢ interp2 V (consList (as.take l) ρ) (Fs.getD l default)
  | [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, [], _, h, _ => h.elim
  | F :: Fs, a :: as, 0, h, _ => by simpa using h.1
  | F :: Fs, a :: as, l + 1, h, hl => by
    simp only [List.getD_cons_succ, List.take_succ_cons, consList_cons]
    exact spineFit_getD_mem (Fs := Fs) (as := as) (l := l) h.2 (by simpa using hl)

/-! ## The spelled pieces -/

/-- Constructor `j`'s branch with the inductive hypotheses, at depth
`D` (the unfolded function at `bvar (D - 1)`, so `bvar D` under the
payload binder). -/
def caseBaseAVR (ℓ w : Nat) (Fss : List (List AVExpr)) (ar : Nat → Nat) (recs : Nat → List Nat)
    (n nIdx D j : Nat) : AVExpr :=
  .lam ℓ ((towerBodyAV w (Fss.getD j [])).liftN D 0)
    (AVExpr.mkAppN (.bvar (D + 1 + nIdx + n - 1 - j))
      (((List.range (ar j)).map fun i => projAV i (.bvar 0)) ++
        ((recs j).map fun i => .app (.bvar D) (projAV i (.bvar 0)))))

/-- The case recursor with inductive hypotheses from stage `j` with
`r` constructors remaining, at depth `D`, on the tag `k`. -/
def caseRecAVR (ℓ w : Nat) (Fss : List (List AVExpr)) (ar : Nat → Nat) (recs : Nat → List Nat)
    (n nIdx : Nat) : Nat → Nat → Nat → AVExpr → AVExpr
  | 0, _, _, _ => .lam ℓ (.const .empty [w]) .prf
  | r + 1, D, j, k =>
    natRecAV (imaxN w ℓ) (caseMotiveAV ℓ w Fss n nIdx D j) (caseBaseAVR ℓ w Fss ar recs n nIdx D j)
      (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ) (caseMotiveBodyAV ℓ w Fss n nIdx D j)
        (caseRecAVR ℓ w Fss ar recs n nIdx r (D + 2) (j + 1) (.bvar 1))))
      k

/-- Constructor `j`'s branch, semantically: the minor applied along
the payload's first `nF` projections and then along `r` at the
recursive projections. -/
noncomputable def baseSemR (ℓ : Nat) (f : Nat → V) (ms : Nat → V) (nF : Nat) (recs : List Nat)
    (rV : V) (j : Nat) : V :=
  lamR ℓ (f j) fun y =>
    (((List.range nF).map fun i => projS i y) ++ (recs.map fun i => SetTheory.app rV (projS i y))).foldl
      SetTheory.app (ms j)

/-! ## The hypotheses -/

/-- The recursive route's K-frame hypotheses: the sum route's core,
the recursive flags, the recursive domains reading to the carrier,
and the minors in their ih-extended spaces. -/
structure RecHypR (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess : List (List AVExpr))
    (Ids : List AVExpr) (famAt : List V → V) (rss : List (List Bool)) : Prop
    extends RecHypCore ℓ w ρ₀ Fss Ess Ids famAt where
  hlenR : rss.length = Fss.length
  hrecT : ∀ j, j < Fss.length → ∀ i, i < (Fss.getD j []).length → (rss.getD j []).getD i false = true →
    ∀ as : List V, as.length = i →
      interp2 V (consList as (frP Fss.length Ids.length ρ₀)) ((Fss.getD j []).getD i default)
        = famAt (frameIdx Ids.length ρ₀)
  hms : ∀ j, j < Fss.length →
    frMs Fss.length Ids.length ρ₀ j
      ∈ˢ minorSpI ℓ
        (fun fs => ihSp ℓ (frMi Fss.length Ids.length ρ₀) fs
          (concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j []) j fs)
          (recIdx (rss.getD j []) (Fss.getD j []).length))
        (Fss.getD j []) (frP Fss.length Ids.length ρ₀) []

namespace RecHypR

variable {ℓ w : Nat} {ρ₀ : Nat → V} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
  {famAt : List V → V} {rss : List (List Bool)}

/-- At a zero elimination level the minors are the point. -/
theorem minor_pt (h : RecHypR ℓ w ρ₀ Fss Ess Ids famAt rss) (h0 : ℓ = 0) {j : Nat}
    (hj : j < Fss.length) : frMs Fss.length Ids.length ρ₀ j = pt :=
  eq_pt_of_mem_univZero
    (h0 ▸ minorSpI_zero_univZero h0
      (fun fs => ihSp_zero_univZero h0 (h.conc_univZero h0 hj fs) _) _ _ _)
    (h.hms j hj)

end RecHypR

/-! ## The base branch -/

omit [SetTheory V] in
theorem cons_apply_pred {σ : Nat → V} {D : Nat} (hD : 1 ≤ D) (y : V) :
    cons y σ D = σ (D - 1) := by
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  show cons y σ (D' + 1) = σ D'
  rw [cons_succ]

/-- Constructor `j`'s branch with ihs (graph regime): its value, its
grading, its membership in the stage motive at the numeral `0`. -/
theorem base_factsR {ℓ w D : Nat} (hw : w ≠ 0) {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V} {rss : List (List Bool)} {rV : V}
    (hfr : RecFrameS D ρ₀ σ) (hD : 1 ≤ D) (hrσ : σ (D - 1) = rV)
    (hyp : RecHypR ℓ w ρ₀ Fss Ess Ids famAt rss)
    (hrV : rV ∈ˢ piR ℓ (famAt (frameIdx Ids.length ρ₀))
      fun t => SetTheory.app (frMi Fss.length Ids.length ρ₀) t)
    {j : Nat} (hj : j < Fss.length) :
    interp2 V σ (caseBaseAVR ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length)
          (fun j => recIdx (rss.getD j []) (Fss.getD j []).length) Fss.length Ids.length D j)
        = baseSemR ℓ (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
            (frMs Fss.length Ids.length ρ₀) (Fss.getD j []).length
            (recIdx (rss.getD j []) (Fss.getD j []).length) rV j ∧
      AnnotOk2 V σ (caseBaseAVR ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length)
          (fun j => recIdx (rss.getD j []) (Fss.getD j []).length) Fss.length Ids.length D j) ∧
      interp2 V σ (caseBaseAVR ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length)
          (fun j => recIdx (rss.getD j []) (Fss.getD j []).length) Fss.length Ids.length D j)
        ∈ˢ motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
            (frMi Fss.length Ids.length ρ₀) j (vnat 0) := by
  have hjF := hyp.rChain_getElem? hj
  have hokF : FieldsOkB w ρ₀
      (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
    hyp.hok _ (List.mem_of_getElem? hjF)
  have hfj : sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess) j
      = towerSet w (teleOfFields ρ₀
          (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []))) :=
    sumFibre_of_getElem? hjF
  have hgetD : (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j []
      = rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []) := by
    rw [List.getD_eq_getElem?_getD, hjF]; rfl
  have hdomv : interp2 V σ ((towerBodyAV w
        ((rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j [])).liftN D 0)
      = towerSet w (teleOfFields ρ₀
          (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []))) := by
    rw [interp2_liftN, hfr, hgetD]
    exact towerBodyAV_interp (fun hw => hokF.toBound hw)
  have hokdom : AnnotOk2 V σ ((towerBodyAV w
      ((rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess).getD j [])).liftN D 0) := by
    rw [AnnotOk2_liftN, hfr, hgetD]
    exact towerBodyAV_ok2 hokF
  have hminor : ∀ y : V, cons y σ (D + 1 + Ids.length + Fss.length - 1 - j)
      = frMs Fss.length Ids.length ρ₀ j :=
    fun y => (hfr.push y).minor hj
  have hrslot : ∀ y : V, cons y σ D = rV := fun y => by rw [cons_apply_pred hD, hrσ]
  have hms := hyp.hms j hj
  have hEslen : (Ess.getD j []).length = Ids.length := hyp.hEs j hj
  have hc0 : ℓ = 0 → ∀ acc, concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀)
      (Ess.getD j []) j acc ∈ˢ (univZero : V) :=
    fun h0 acc => hyp.conc_univZero h0 hj acc
  have hM0 : ℓ = 0 → ∀ x, SetTheory.app (frMi Fss.length Ids.length ρ₀) x ∈ˢ (univZero : V) :=
    fun h0 x => hyp.hM0 h0 x
  -- the body at a payload: the minor's fold along the projections and the ihs
  have hbody : ∀ y : V, y ∈ˢ towerSet w (teleOfFields ρ₀
        (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j []))) →
      AnnotOk2 V (cons y σ) (AVExpr.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)) ++
          ((recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
            .app (.bvar D) (projAV i (.bvar 0))))) ∧
      interp2 V (cons y σ) (AVExpr.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)) ++
          ((recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
            .app (.bvar D) (projAV i (.bvar 0)))))
        = (((List.range (Fss.getD j []).length).map fun i => projS i y) ++
            ((recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
              SetTheory.app rV (projS i y))).foldl SetTheory.app
            (frMs Fss.length Ids.length ρ₀ j) ∧
      interp2 V (cons y σ) (AVExpr.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)) ++
          ((recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
            .app (.bvar D) (projAV i (.bvar 0)))))
        ∈ˢ SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w j y) := by
    intro y hy
    have hpv : ∀ i, interp2 V (cons y σ) (projAV i (.bvar 0)) = projS i y := by
      intro i; rw [projAV_interp, interp2_bvar]; rfl
    have hval : interp2 V (cons y σ) (AVExpr.mkAppN (.bvar (D + 1 + Ids.length + Fss.length - 1 - j))
        (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)) ++
          ((recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
            .app (.bvar D) (projAV i (.bvar 0)))))
        = (((List.range (Fss.getD j []).length).map fun i => projS i y) ++
            ((recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
              SetTheory.app rV (projS i y))).foldl SetTheory.app
            (frMs Fss.length Ids.length ρ₀ j) := by
      rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V (cons y σ)) (g := SetTheory.app),
        interp2_bvar, hminor, List.map_append, List.map_map, List.map_map]
      congr 2
      · apply List.map_congr_left
        intro i _
        exact hpv i
      · apply List.map_congr_left
        intro i _
        show SetTheory.app (interp2 V (cons y σ) (.bvar D)) (interp2 V (cons y σ) (projAV i (.bvar 0)))
          = _
        rw [interp2_bvar, hrslot, hpv]
    -- the payload's projections: fitting, the index equation, the eta
    have helim := restricted_member_elim hw
      (Fs := liftFields (Ids.length + Fss.length + 1) 0 (Fss.getD j []))
      (eqs := idxEqsAt (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []).length (Ess.getD j []))
      (ρ := ρ₀) (y := y) hy
    rw [liftFields_length] at helim
    obtain ⟨hspL, hlast, hall, heta⟩ := helim
    have hspP : SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j [])
        (projList (Fss.getD j []).length y) :=
      (spineFit_liftFields (Ids.length + Fss.length + 1)).mp hspL
    have hidx : idxValsAt (frP Fss.length Ids.length ρ₀) (Ess.getD j [])
        (projList (Fss.getD j []).length y) = frameIdx Ids.length ρ₀ :=
      (EqAll_idxEqsAt hEslen (projList_length _ _)).mp hall
    -- the projection spine fits the field chain
    have hbnd : FieldsBound w ρ₀
        (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
      hokF.toBound hw
    have hlenR : (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])).length
        = (Fss.getD j []).length + 1 := rChain_length _ _ _ _
    have hpok : ∀ i, i < (Fss.getD j []).length → AnnotOk2 V (cons y σ) (projAV i (.bvar 0)) := by
      intro i hi
      exact projAV_ok2_tower (by simp) (by rw [interp2_bvar]; exact hy) hbnd (by omega)
    have hfit : ArgsOkFit (cons y σ)
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0))
        (Fss.getD j []) (frP Fss.length Ids.length ρ₀) := by
      rw [List.range_eq_range']
      refine argsOkFit_of_projSpine (y := y) ?_ ?_ ?_
      · rw [← List.range_eq_range', ← projList_eq_map_range]; exact hspP
      · intro i _ hi
        exact hpok i (by omega)
      · exact hpv
    have hmap : (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)).map
        (interp2 V (cons y σ))) = projList (Fss.getD j []).length y := by
      rw [List.map_map, projList_eq_map_range]
      apply List.map_congr_left
      intro i _
      exact hpv i
    -- the recursive components are carrier members
    have hrecmem : ∀ i ∈ recIdx (rss.getD j []) (Fss.getD j []).length,
        projS i y ∈ˢ famAt (frameIdx Ids.length ρ₀) := by
      intro i hi
      obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
      have := spineFit_getD_mem hspP hik
      rw [hyp.hrecT j hj i hik hri _ (by rw [List.length_take, projList_length]; omega)] at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [projList_length]; exact hik),
        Option.getD_some, projList_get _ _ _ hik] at this
      exact this
    -- the conclusion at the projections
    have hconv : concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j []) j
        (projList (Fss.getD j []).length y)
        = SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w j y) := by
      unfold concI ctorValI frMi
      rw [hidx, if_neg hw, injW_pos hw, ← heta]
    -- the fold along the fields lands in the ih tower
    have hsp := minorSpI_spine (V := V)
      (c := fun fs => ihSp ℓ (frMi Fss.length Ids.length ρ₀) fs
        (concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j []) j fs)
        (recIdx (rss.getD j []) (Fss.getD j []).length))
      (fun h0 fs => ihSp_zero_univZero h0 (hc0 h0 fs) _) (Fs := Fss.getD j [])
      (args := (List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0))
      (ρf := frP Fss.length Ids.length ρ₀) (acc := [])
      (f := .bvar (D + 1 + Ids.length + Fss.length - 1 - j)) (σ := cons y σ) (by simp)
      (by rw [interp2_bvar, hminor]; exact hms) hfit
    rw [List.nil_append, hmap] at hsp
    -- then along the ihs
    have hih := ihSp_spine (V := V) (ℓ := ℓ) (M := frMi Fss.length Ids.length ρ₀)
      (fs := projList (Fss.getD j []).length y)
      (C := concI w (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) (Ess.getD j []) j
        (projList (Fss.getD j []).length y))
      (fun h0 => hc0 h0 _)
      (is := recIdx (rss.getD j []) (Fss.getD j []).length)
      (args := (recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
        .app (.bvar D) (projAV i (.bvar 0)))
      (σ := cons y σ) hsp.1 hsp.2 (by rw [List.length_map]) ?_ ?_
    · rw [← AVExpr.mkAppN_append] at hih
      rw [hconv] at hih
      exact ⟨hih.1, hval, hih.2⟩
    · intro l hl
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
        Option.map_some, Option.getD_some]
      have hi : (recIdx (rss.getD j []) (Fss.getD j []).length)[l] ∈
          recIdx (rss.getD j []) (Fss.getD j []).length := List.getElem_mem hl
      obtain ⟨hik, _⟩ := mem_recIdx.mp hi
      have hmem := hrecmem _ hi
      have h1 : (recIdx (rss.getD j []) (Fss.getD j []).length).getD l 0
          = (recIdx (rss.getD j []) (Fss.getD j []).length)[l] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      have hgd : (projList (Fss.getD j []).length y).getD
          ((recIdx (rss.getD j []) (Fss.getD j []).length).getD l 0) pt
          = projS ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) y := by
        rw [h1, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by rw [projList_length]; exact hik), Option.getD_some,
          projList_get _ _ _ hik]
      refine ⟨?_, ?_⟩
      · rw [AnnotOk2_app]
        refine ⟨trivial, hpok _ hik, ℓ, famAt (frameIdx Ids.length ρ₀),
          fun t => SetTheory.app (frMi Fss.length Ids.length ρ₀) t, ?_, ?_, ?_⟩
        · rw [interp2_bvar, hrslot]; exact hrV
        · rw [hpv]; exact hmem
        · intro h0 x _; exact hM0 h0 x
      · rw [hgd, interp2_app, interp2_bvar, hrslot, hpv]
        exact app_mem_piR hrV hmem (fun h0 x _ => hM0 h0 x)
    · intro h0 i _
      exact hM0 h0 _
  refine ⟨?_, ?_, ?_⟩
  · show lamR ℓ _ _ = _
    unfold baseSemR
    rw [hdomv, hfj]
    exact lamR_congr fun y hy => (hbody y hy).2.1
  · show AnnotOk2 V σ (.lam ℓ _ _)
    rw [AnnotOk2_lam]
    refine ⟨hokdom, fun y hy => (hbody y (hdomv ▸ hy)).1,
      fun y => SetTheory.app (frMi Fss.length Ids.length ρ₀) (injW w j y),
      fun y hy => (hbody y (hdomv ▸ hy)).2.2, fun h0 y hy => ?_⟩
    have := hyp.hMapp (injW_mem (f := sumFibre w ρ₀
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) (i := j)
      (by rw [hfj]; exact hdomv ▸ hy))
    rwa [h0, univ_zero] at this
  · show lamR ℓ _ _ ∈ˢ _
    rw [motSem_vnat]
    simp only [Nat.add_zero]
    rw [hfj, hdomv]
    exact lamR_mem fun y hy => (hbody y hy).2.2

/-! ## The case recursor -/

/-- **The case recursor's facts** with inductive hypotheses (graph
regime): `caseRec_facts` re-run with the ih branch. -/
theorem caseRec_factsR {ℓ w : Nat} (hw : w ≠ 0) {ρ₀ : Nat → V} {Fss Ess : List (List AVExpr)}
    {Ids : List AVExpr} {famAt : List V → V} {rss : List (List Bool)} {rV : V}
    (hyp : RecHypR ℓ w ρ₀ Fss Ess Ids famAt rss)
    (hrV : rV ∈ˢ piR ℓ (famAt (frameIdx Ids.length ρ₀))
      fun t => SetTheory.app (frMi Fss.length Ids.length ρ₀) t) :
    ∀ (r : Nat) {D j : Nat} {σ : Nat → V} {k : AVExpr},
      RecFrameS D ρ₀ σ → 1 ≤ D → σ (D - 1) = rV → j + r = Fss.length →
      ((interp2 V σ k ∈ˢ (omega : V) →
        interp2 V σ (caseRecAVR ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
            (fun j => (Fss.getD j []).length)
            (fun j => recIdx (rss.getD j []) (Fss.getD j []).length) Fss.length Ids.length r D j k)
          ∈ˢ motSem ℓ w (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
              (frMi Fss.length Ids.length ρ₀) j (interp2 V σ k) ∧
        ∀ i, interp2 V σ k = vnat i → i < r →
          interp2 V σ (caseRecAVR ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
              (fun j => (Fss.getD j []).length)
              (fun j => recIdx (rss.getD j []) (Fss.getD j []).length) Fss.length Ids.length r D j k)
            = baseSemR ℓ (sumFibre w ρ₀ (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess))
                (frMs Fss.length Ids.length ρ₀) (Fss.getD (j + i) []).length
                (recIdx (rss.getD (j + i) []) (Fss.getD (j + i) []).length) rV (j + i)) ∧
      (AnnotOk2 V σ k → (ℓ ≠ 0 → interp2 V σ k ∈ˢ (omega : V)) →
        AnnotOk2 V σ (caseRecAVR ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length)
          (fun j => recIdx (rss.getD j []) (Fss.getD j []).length) Fss.length Ids.length r D j k)))
  | 0, D, j, σ, k, hfr, _, _, hjr => by
    refine ⟨fun hk => ⟨?_, fun i _ hi => absurd hi (Nat.not_lt_zero i)⟩, fun _ _ => ?_⟩
    · obtain ⟨i, hki⟩ := mem_omega_iff.mp hk
      rw [hki, motSem_vnat]
      show lamR ℓ (empty : V) _ ∈ˢ _
      rw [sumFibre_of_ge (by rw [hyp.rChains_length']; omega)]
      exact lamR_mem fun _ hx => absurd hx (not_mem_empty _)
    · show AnnotOk2 V σ (.lam ℓ (.const .empty [w]) .prf)
      rw [AnnotOk2_lam]
      exact ⟨trivial, fun _ hx => absurd hx (not_mem_empty _), fun _ => unitSet,
        fun _ hx => absurd hx (not_mem_empty _), fun _ _ hx => absurd hx (not_mem_empty _)⟩
  | r + 1, D, j, σ, k, hfr, hD, hrσ, hjr => by
    have hjn : j < Fss.length := by omega
    obtain ⟨hMv, hMsp, hMapp, hMok⟩ := motive_facts hfr hyp.toRecHypCore j
    obtain ⟨hzv, hzok, hzm⟩ := base_factsR hw hfr hD hrσ hyp hrV hjn
    generalize hR : rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess = Fss' at *
    generalize hAr : (fun j => (Fss.getD j []).length) = ar at *
    generalize hRc : (fun j => recIdx (rss.getD j []) (Fss.getD j []).length) = recs at *
    have hz : interp2 V σ (caseBaseAVR ℓ w Fss' ar recs Fss.length Ids.length D j)
        ∈ˢ SetTheory.app (interp2 V σ (caseMotiveAV ℓ w Fss' Fss.length Ids.length D j)) natzero := by
      rw [hMapp natzero natzero_mem, natzero_eq_vnat]; exact hzm
    have hrσ' : ∀ a b : V, cons a (cons b σ) (D + 2 - 1) = rV := by
      intro a b
      obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
      show cons a (cons b σ) (D' + 1 + 1) = rV
      rw [cons_succ, cons_succ]; exact hrσ
    -- the step's inner recursor at every step frame
    have hinner : ∀ (a b : V), b ∈ˢ (omega : V) →
        interp2 V (cons a (cons b σ))
            (caseRecAVR ℓ w Fss' ar recs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))
          ∈ˢ motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) (j + 1) b ∧
        (∀ i, b = vnat i → i < r →
          interp2 V (cons a (cons b σ))
              (caseRecAVR ℓ w Fss' ar recs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))
            = baseSemR ℓ (sumFibre w ρ₀ Fss') (frMs Fss.length Ids.length ρ₀)
                (Fss.getD (j + 1 + i) []).length
                (recIdx (rss.getD (j + 1 + i) []) (Fss.getD (j + 1 + i) []).length) rV (j + 1 + i)) ∧
        AnnotOk2 V (cons a (cons b σ))
          (caseRecAVR ℓ w Fss' ar recs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1)) := by
      intro a b hb
      have h := caseRec_factsR hw hyp hrV r (D := D + 2) (j := j + 1) (σ := cons a (cons b σ))
        (k := .bvar 1) (hfr.step a b) (by omega) (hrσ' a b) (by omega)
      rw [hR, hAr, hRc] at h
      have hb' : interp2 V (cons a (cons b σ)) (.bvar 1) ∈ˢ (omega : V) := by
        rw [interp2_bvar]; exact hb
      refine ⟨(h.1 hb').1, fun i hi hir => (h.1 hb').2 i (by rw [interp2_bvar]; exact hi) hir,
        h.2 trivial (fun _ => hb')⟩
    -- the motive at a successor is the next stage's motive
    have hsucc : ∀ (i : Nat), motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (vnat (i + 1))
        = motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) (j + 1) (vnat i) := by
      intro i
      rw [motSem_vnat, motSem_vnat, show j + (i + 1) = j + 1 + i from by omega]
    -- the step: its value and its membership in the step space
    have hsv : interp2 V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ)
          (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j)
          (caseRecAVR ℓ w Fss' ar recs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))))
        = lamR (imaxN w ℓ) omega fun b =>
            lamR (imaxN w ℓ) (interp2 V (cons b σ) (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j))
              fun a => interp2 V (cons a (cons b σ))
                (caseRecAVR ℓ w Fss' ar recs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1)) := rfl
    have hmb := fun (b : V) (hb : b ∈ˢ (omega : V)) => motiveBody_facts hfr hyp.toRecHypCore j hb
    rw [hR] at hmb
    have hs : interp2 V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ)
          (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j)
          (caseRecAVR ℓ w Fss' ar recs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))))
        ∈ˢ natStepSpace2 V (imaxN w ℓ) (interp2 V σ (caseMotiveAV ℓ w Fss' Fss.length Ids.length D j)) := by
      rw [hsv]
      unfold natStepSpace2
      refine lamR_mem fun b hb => ?_
      rw [hMapp b hb, hMapp (natsucc b) (natsucc_mem hb), (hmb b hb).1]
      refine lamR_mem fun a _ => ?_
      obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
      rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
      exact (hinner a _ hb).1
    refine ⟨fun hk => ⟨?_, ?_⟩, fun hokk hkω => ?_⟩
    · -- membership
      have h := natRecAV_mem hMsp hz hs hk
      rwa [hMapp _ hk] at h
    · -- iota
      intro i hi hir
      show interp2 V σ (natRecAV (imaxN w ℓ) _ _ _ k) = _
      rw [interp2_natRecAV hMsp hz hs hk, hi, natrec_vnat]
      -- the iteration's values inhabit the stage motive
      have hiter : ∀ i', natIter (interp2 V σ (caseBaseAVR ℓ w Fss' ar recs Fss.length Ids.length D j))
          (interp2 V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ)
            (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j)
            (caseRecAVR ℓ w Fss' ar recs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))))) i'
          ∈ˢ motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (vnat i') := by
        intro i'
        have h := natRecV2_mem_fibre V hMsp hz hs (vnat_mem_omega i')
        rwa [natrec_vnat, hMapp _ (vnat_mem_omega i')] at h
      cases i with
      | zero =>
        rw [Nat.add_zero]
        exact hzv
      | succ i =>
        show SetTheory.app (SetTheory.app _ (vnat i)) (natIter _ _ i) = _
        by_cases h0 : ℓ = 0
        · -- the zero level: everything is the point
          have hz' : imaxN w ℓ = 0 := (imaxN_eq_zero_iff w ℓ).mpr h0
          rw [hsv, hz', lamR_zero, app_pt, app_pt]
          unfold baseSemR
          rw [h0, lamR_zero]
        · have hz' : imaxN w ℓ ≠ 0 := fun h => h0 ((imaxN_eq_zero_iff w ℓ).mp h)
          rw [hsv, app_lamR_pos hz' (vnat_mem_omega i),
            app_lamR_pos hz' (by
              rw [(hmb _ (vnat_mem_omega i)).1]
              exact hiter i),
            (hinner _ _ (vnat_mem_omega i)).2.1 i rfl (by omega),
            show j + 1 + i = j + (i + 1) from by omega]
    · -- the grading
      by_cases h0 : ℓ = 0
      · -- the point-headed spine
        have hz' : imaxN w ℓ = 0 := (imaxN_eq_zero_iff w ℓ).mpr h0
        refine (mkAppN_ok2_of_pt_head (f := .const .natRec [imaxN w ℓ]) (σ := σ) trivial
          (by show natRecV2 V (imaxN w ℓ) = pt; rw [hz', natRecV2, lamR_zero]) ?_).1
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        · exact hMok
        · exact hzok
        · rw [AnnotOk2_lam]
          refine ⟨trivial, fun b hb => ?_, fun b => piR (imaxN w ℓ)
              (motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j b)
              (fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b)),
            fun b hb => ?_, fun _ b hb => by rw [hz']; exact piR_zero_mem_univZero⟩
          · rw [AnnotOk2_lam]
            refine ⟨(hmb b hb).2, fun a _ => (hinner a b hb).2.2,
              fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b),
              fun a _ => ?_, fun _ a _ => ?_⟩
            · obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
              rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
              exact (hinner a _ hb).1
            · obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
              rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc,
                motSem_vnat, h0]
              exact piR_zero_mem_univZero
          · show lamR (imaxN w ℓ) (interp2 V (cons b σ) (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j))
              (fun a => interp2 V (cons a (cons b σ))
                (caseRecAVR ℓ w Fss' ar recs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))) ∈ˢ piR (imaxN w ℓ) _ _
            rw [(hmb b hb).1]
            refine lamR_mem fun a _ => ?_
            obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
            rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
            exact (hinner a _ hb).1
        · exact hokk
      · -- `Nat.rec`'s own chain
        refine natRecAV_ok2 hMok hzok ?_ hokk hMsp hz hs (hkω h0)
        rw [AnnotOk2_lam]
        refine ⟨trivial, fun b hb => ?_, fun b => piR (imaxN w ℓ)
            (motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j b)
            (fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b)),
          fun b hb => ?_, fun h => absurd ((imaxN_eq_zero_iff w ℓ).mp h) h0⟩
        · rw [AnnotOk2_lam]
          refine ⟨(hmb b hb).2, fun a _ => (hinner a b hb).2.2,
            fun _ => motSem ℓ w (sumFibre w ρ₀ Fss') (frMi Fss.length Ids.length ρ₀) j (natsucc b),
            fun a _ => ?_, fun h => absurd ((imaxN_eq_zero_iff w ℓ).mp h) h0⟩
          obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
          rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
          exact (hinner a _ hb).1
        · show lamR (imaxN w ℓ) (interp2 V (cons b σ) (caseMotiveBodyAV ℓ w Fss' Fss.length Ids.length D j))
            (fun a => interp2 V (cons a (cons b σ))
              (caseRecAVR ℓ w Fss' ar recs Fss.length Ids.length r (D + 2) (j + 1) (.bvar 1))) ∈ˢ piR (imaxN w ℓ) _ _
          rw [(hmb b hb).1]
          refine lamR_mem fun a _ => ?_
          obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
          rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
          exact (hinner a _ hb).1

end Lech.Semantics
