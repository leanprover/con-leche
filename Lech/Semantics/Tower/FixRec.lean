import Lech.Semantics.Tower.FixCase
import Lech.Semantics.Tower.SumRec

/-!
# The recursive recursor: the fixed point and its leaf (task #188)

The recursor of a directly installed recursive type is spelled at the
K-frame `(p⃗, motive, minors)` as a **fixed point of its one-step
unfolding**, selected by the basis `Classical.choice`:

    Step := λ (r : Π t:T, M t) (t : T). case_r t          (`fixStepAV`)
    Σ    := Σ' (r : Π t:T, M t), Step r = r               (`fixSigAV`)
    Sel  := (choice Σ prf).1                              (`fixSelAV`)
    body := Sel t                                          (`fixRecBodyAV`, under the major)

where `case_r` is the case split with the inductive hypotheses read
off `r` (`Lech/Semantics/Tower/FixCase.lean`).  The certificate `prf`
is typed by `¬¬Σ`, i.e. by the EXISTENCE of a fixed point, which the
semantics exhibits: the carrier is the ω-iterate of its tower functor
(`fixCarrier_eq_iterU`), so a function is defined by **rank
recursion** — `fixSem n` unfolds the step `n` times from junk
(`fixSem`), is stable above a member's stage (`fixSem_stable`), lands
in the motive (`fixSem_mem`), and the function sending each carrier
member to its own stage's value is a fixed point (`fixStar_fixed`).
No uniqueness is needed anywhere: the selected fixed point `R` is what
the recursor reads to, and iota is `R (c_j f⃗) = Step R (c_j f⃗) = m_j
f⃗ (R f_{i₁}) …` (`fixRecBody_iota`).  At a zero elimination level
everything is the proof point and the certificate is the motive's
inhabitation, proved by the same rank induction (`fixSem_inhab`).

Both regimes: at a squash instantiation (`w = 0`) the elimination
level is zero (kernel guard, `FixHypR.hwℓ`) and the body is spelled as
the point.
-/

namespace Lech.Semantics
open Lech.SetModel

open SetTheory
open Lech.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Fits of the X-chains -/

omit [SetTheory V] in
theorem chainXGo_length (rs : List Bool) : ∀ (Fs : List AVExpr) (i : Nat),
    (chainXGo rs Fs i).length = Fs.length
  | [], _ => rfl
  | _ :: Fs, i => by simp [chainXGo, chainXGo_length rs Fs (i + 1)]

/-- The recursive components of a tuple fitting the X-chain at `X` are
members of `X`. -/
theorem fitsX_rec_mem {ρp : Nat → V} {X : V} (rs : List Bool) :
    ∀ (Fs₀ : List AVExpr) (i : Nat) (as bs : List V), as.length = i →
      SpineFit (consList as (cons X ρp)) (chainXGo rs Fs₀ i) bs →
      ∀ l, l < bs.length → rs.getD (i + l) false = true → bs.getD l pt ∈ˢ X
  | [], _, _, [], _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _ :: _, _, h, _, _, _ => h.elim
  | _ :: _, _, _, [], _, h, _, _, _ => h.elim
  | F₀ :: Fs₀, i, as, b :: bs, hi, h, l, hl, hr => by
    subst hi
    simp only [chainXGo, SpineFit] at h
    cases l with
    | zero =>
      rw [Nat.add_zero] at hr
      rw [if_pos hr, interp2_chainX_rec] at h
      exact h.1
    | succ l =>
      have h2 := h.2
      rw [consList_snoc] at h2
      have := fitsX_rec_mem rs Fs₀ (as.length + 1) (as ++ [b]) bs (length_snoc b as) h2 l
        (by simpa using hl) (by rw [show as.length + 1 + l = as.length + (l + 1) from by omega]; exact hr)
      simpa using this

/-- A tuple fitting the X-chain at a subset of the carrier fits the
real chain. -/
theorem spineFit_real_of_X {μ X : V} {ρp : Nat → V} (rs : List Bool) (hX : X ⊆ˢ μ) :
    ∀ (Fs₀ Fs : List AVExpr) (i : Nat) (as bs : List V), as.length = i →
      ChainReal μ ρp rs i Fs₀ Fs →
      SpineFit (consList as (cons X ρp)) (chainXGo rs Fs₀ i) bs →
      SpineFit (consList as ρp) Fs bs
  | [], [], _, _, [], _, _, _ => trivial
  | [], [], _, _, _ :: _, _, _, h => h.elim
  | [], _ :: _, _, _, _, _, hc, _ => hc.elim
  | _ :: _, [], _, _, _, _, hc, _ => hc.elim
  | _ :: _, _ :: _, _, _, [], _, _, h => h.elim
  | F₀ :: Fs₀, F :: Fs, i, as, b :: bs, hi, hc, h => by
    subst hi
    simp only [chainXGo, SpineFit] at h ⊢
    obtain ⟨hhead, htail⟩ := hc
    refine ⟨?_, ?_⟩
    · split at h
      · rw [if_pos ‹_›] at hhead
        rw [interp2_chainX_rec] at h
        rw [hhead as rfl]
        exact hX b h.1
      · rw [if_neg ‹_›] at hhead
        rw [interp2_chainX_ordinary] at h
        rw [hhead]
        exact h.1
    · have h2 := h.2
      rw [consList_snoc] at h2 ⊢
      exact spineFit_real_of_X rs hX Fs₀ Fs (as.length + 1) (as ++ [b]) bs (length_snoc b as) htail h2

/-! ## Stage elimination -/

/-- A member of the functor at `X` (graph regime): the injection of a
point-terminated tuple whose recursive components lie in `X` and which
fits the real chain whenever `X` lies in the carrier. -/
theorem fixStep_elim {w : Nat} (hw : w ≠ 0) {ρp : Nat → V} {rss : List (List Bool)}
    {Fss₀ : List (List AVExpr)} {X t : V} (ht : t ∈ˢ fixStep w ρp rss Fss₀ X) :
    ∃ j fs, t = inj j (mkTower (fs ++ [pt])) ∧ j < Fss₀.length ∧ j < rss.length ∧
      fs.length = (Fss₀.getD j []).length ∧
      (∀ l, l < fs.length → (rss.getD j []).getD l false = true → fs.getD l pt ∈ˢ X) ∧
      (∀ {μ : V} {Fss : List (List AVExpr)}, X ⊆ˢ μ → ChainsReal μ ρp rss Fss₀ Fss →
        SpineFit ρp (Fss.getD j []) fs) := by
  unfold fixStep at ht
  obtain ⟨j, a, ha, rfl⟩ := sumSet_elim hw ht
  unfold sumFibre at ha
  rw [chainsX_getElem?] at ha
  cases hr : rss[j]? with
  | none => rw [hr] at ha; exact absurd ha (not_mem_empty _)
  | some rs =>
    cases hF : Fss₀[j]? with
    | none => rw [hr, hF] at ha; exact absurd ha (not_mem_empty _)
    | some Fs₀ =>
      rw [hr, hF] at ha
      simp only at ha
      obtain ⟨hfit, heta⟩ := towerSet_elim_teleOfFields hw ha
      unfold chainX at hfit heta
      obtain ⟨fs, hfs, hsp, -⟩ := spineFit_append_idxEq.mp hfit
      have hjF : j < Fss₀.length := (List.getElem?_eq_some_iff.mp hF).1
      have hjr : j < rss.length := (List.getElem?_eq_some_iff.mp hr).1
      have hgF : Fss₀.getD j [] = Fs₀ := by rw [List.getD_eq_getElem?_getD, hF]; rfl
      have hgr : rss.getD j [] = rs := by rw [List.getD_eq_getElem?_getD, hr]; rfl
      have hlen : fs.length = Fs₀.length := by
        have := hsp.length_eq
        rwa [chainXGo_length] at this
      refine ⟨j, fs, ?_, hjF, hjr, by rw [hgF]; exact hlen, ?_, ?_⟩
      · rw [heta, hfs]
      · intro l hl hrl
        rw [hgr] at hrl
        have := fitsX_rec_mem (ρp := ρp) (X := X) rs Fs₀ 0 [] fs rfl hsp l hl
          (by rw [Nat.zero_add]; exact hrl)
        exact this
      · intro μ Fss hX hreal
        obtain ⟨hl₁, hl₂, h⟩ := hreal
        obtain ⟨Fs, hFs⟩ : ∃ Fs, Fss[j]? = some Fs := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hgFs : Fss.getD j [] = Fs := by rw [List.getD_eq_getElem?_getD, hFs]; rfl
        rw [hgFs]
        exact spineFit_real_of_X rs hX Fs₀ Fs 0 [] fs rfl (h j rs Fs₀ Fs hr hF hFs) hsp

/-- A member of the functor at `X` (squash regime): the point, with
some tuple whose recursive components lie in `X` and which fits the
real chain whenever `X` lies in the carrier. -/
theorem fixStep_zero_elim {ρp : Nat → V} {rss : List (List Bool)}
    {Fss₀ : List (List AVExpr)} {X t : V} (ht : t ∈ˢ fixStep 0 ρp rss Fss₀ X) :
    t = pt ∧ ∃ j fs, j < Fss₀.length ∧ j < rss.length ∧
      fs.length = (Fss₀.getD j []).length ∧
      (∀ l, l < fs.length → (rss.getD j []).getD l false = true → fs.getD l pt ∈ˢ X) ∧
      (∀ {μ : V} {Fss : List (List AVExpr)}, X ⊆ˢ μ → ChainsReal μ ρp rss Fss₀ Fss →
        SpineFit ρp (Fss.getD j []) fs) := by
  unfold fixStep at ht
  obtain ⟨rfl, j, a, ha⟩ := sumSet_zero_elim ht
  refine ⟨rfl, ?_⟩
  unfold sumFibre at ha
  rw [chainsX_getElem?] at ha
  cases hr : rss[j]? with
  | none => rw [hr] at ha; exact absurd ha (not_mem_empty _)
  | some rs =>
    cases hF : Fss₀[j]? with
    | none => rw [hr, hF] at ha; exact absurd ha (not_mem_empty _)
    | some Fs₀ =>
      rw [hr, hF] at ha
      simp only at ha
      obtain ⟨-, as, hfit⟩ := towerSet_zero_elim _ ha
      have hfit' := fitsS_teleOfFields.mp hfit
      unfold chainX at hfit'
      obtain ⟨fs, -, hsp, -⟩ := spineFit_append_idxEq.mp hfit'
      have hjF : j < Fss₀.length := (List.getElem?_eq_some_iff.mp hF).1
      have hjr : j < rss.length := (List.getElem?_eq_some_iff.mp hr).1
      have hgF : Fss₀.getD j [] = Fs₀ := by rw [List.getD_eq_getElem?_getD, hF]; rfl
      have hgr : rss.getD j [] = rs := by rw [List.getD_eq_getElem?_getD, hr]; rfl
      have hlen : fs.length = Fs₀.length := by
        have := hsp.length_eq
        rwa [chainXGo_length] at this
      refine ⟨j, fs, hjF, hjr, by rw [hgF]; exact hlen, ?_, ?_⟩
      · intro l hl hrl
        rw [hgr] at hrl
        exact fitsX_rec_mem (ρp := ρp) (X := X) rs Fs₀ 0 [] fs rfl hsp l hl
          (by rw [Nat.zero_add]; exact hrl)
      · intro μ Fss hX hreal
        obtain ⟨hl₁, hl₂, h⟩ := hreal
        obtain ⟨Fs, hFs⟩ : ∃ Fs, Fss[j]? = some Fs := ⟨_, List.getElem?_eq_getElem (by omega)⟩
        have hgFs : Fss.getD j [] = Fs := by rw [List.getD_eq_getElem?_getD, hFs]; rfl
        rw [hgFs]
        exact spineFit_real_of_X rs hX Fs₀ Fs 0 [] fs rfl (h j rs Fs₀ Fs hr hF hFs) hsp

/-- The real chain and the dummy chain of a constructor have the same
length. -/
theorem ChainReal.length_eq' {μ : V} {ρp : Nat → V} {rs : List Bool} :
    ∀ {i : Nat} {Fs₀ Fs : List AVExpr}, ChainReal μ ρp rs i Fs₀ Fs → Fs.length = Fs₀.length
  | _, [], [], _ => rfl
  | _, [], _ :: _, h => h.elim
  | _, _ :: _, [], h => h.elim
  | _, _ :: _, _ :: _, h => by simp [ChainReal.length_eq' h.2]

theorem ChainsReal.length_eq {μ : V} {ρp : Nat → V} {rss : List (List Bool)}
    {Fss₀ Fss : List (List AVExpr)} (h : ChainsReal μ ρp rss Fss₀ Fss) {j : Nat}
    (hj : j < Fss.length) : (Fss.getD j []).length = (Fss₀.getD j []).length := by
  obtain ⟨hl₁, hl₂, hc⟩ := h
  obtain ⟨Fs, hFs⟩ : ∃ Fs, Fss[j]? = some Fs := ⟨_, List.getElem?_eq_getElem hj⟩
  obtain ⟨Fs₀, hF₀⟩ : ∃ Fs₀, Fss₀[j]? = some Fs₀ := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨rs, hr⟩ : ∃ rs, rss[j]? = some rs := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  rw [List.getD_eq_getElem?_getD, hFs, List.getD_eq_getElem?_getD, hF₀]
  exact ChainReal.length_eq' (hc j rs Fs₀ Fs hr hF₀ hFs)

/-- `fixStep_elim` for a GIVEN decomposition: the recursive components
of `inj j (mkTower (fs ++ [pt]))` lie in `X`, and `fs` fits the real
chain whenever `X` lies in the carrier. -/
theorem fixStep_elim_at {w : Nat} (hw : w ≠ 0) {ρp : Nat → V} {rss : List (List Bool)}
    {Fss₀ : List (List AVExpr)} {X : V} {j : Nat} {fs : List V}
    (ht : inj j (mkTower (fs ++ [pt])) ∈ˢ fixStep w ρp rss Fss₀ X)
    (hlen : fs.length = (Fss₀.getD j []).length) :
    (∀ l, l < fs.length → (rss.getD j []).getD l false = true → fs.getD l pt ∈ˢ X) ∧
      (∀ {μ : V} {Fss : List (List AVExpr)}, X ⊆ˢ μ → ChainsReal μ ρp rss Fss₀ Fss →
        SpineFit ρp (Fss.getD j []) fs) := by
  obtain ⟨j', fs', heq, -, -, hlen', hrec, hfit⟩ := fixStep_elim hw ht
  obtain ⟨rfl, heq'⟩ := inj_inj heq
  have hfs : fs = fs' :=
    List.append_inj_left' (mkTower_inj (by simp [hlen, hlen']) heq') rfl
  subst hfs
  exact ⟨hrec, hfit⟩

/-! ## The semantic recursion -/

open Classical in
/-- The numeral of a tag (junk off `ω`). -/
noncomputable def natIdx (k : V) : Nat :=
  if h : ∃ i, k = vnat i then Classical.choose h else 0

theorem natIdx_vnat (i : Nat) : natIdx (vnat i : V) = i := by
  unfold natIdx
  rw [dif_pos ⟨i, rfl⟩]
  exact (vnat_inj (Classical.choose_spec (⟨i, rfl⟩ : ∃ i', (vnat i : V) = vnat i'))).symm

/-- One step of the recursion at constructor `j`: the minor folded
along the fields and then along `g` at the recursive components. -/
noncomputable def stepBr (ms : Nat → V) (recs : Nat → List Nat) (j : Nat) (g : V → V)
    (fs : List V) : V :=
  (fs ++ (recs j).map fun i => g (fs.getD i pt)).foldl SetTheory.app (ms j)

theorem stepBr_congr {ms : Nat → V} {recs : Nat → List Nat} {j : Nat} {g g' : V → V} {fs : List V}
    (h : ∀ i ∈ recs j, g (fs.getD i pt) = g' (fs.getD i pt)) :
    stepBr ms recs j g fs = stepBr ms recs j g' fs := by
  unfold stepBr
  congr 2
  exact List.map_congr_left h

/-- The rank recursion: `n` unfoldings of the step from junk. -/
noncomputable def fixSem (ms : Nat → V) (recs : Nat → List Nat) (ar : Nat → Nat) :
    Nat → V → V
  | 0, _ => pt
  | n + 1, t => stepBr ms recs (natIdx (sfst t)) (fixSem ms recs ar n)
      (projList (ar (natIdx (sfst t))) (ssnd t))

theorem fixSem_inj {ms : Nat → V} {recs : Nat → List Nat} {ar : Nat → Nat} (n j : Nat)
    {fs : List V} (hlen : fs.length = ar j) :
    fixSem ms recs ar (n + 1) (inj j (mkTower (fs ++ [pt]))) = stepBr ms recs j (fixSem ms recs ar n) fs := by
  show stepBr ms recs (natIdx (sfst (inj j (mkTower (fs ++ [pt]))))) (fixSem ms recs ar n)
    (projList (ar (natIdx (sfst (inj j (mkTower (fs ++ [pt])))))) (ssnd (inj j (mkTower (fs ++ [pt]))))) = _
  rw [sfst_inj, natIdx_vnat, ssnd_inj]
  congr 1
  have h1 : projList (fs.length + 1) (mkTower (fs ++ [pt])) = fs ++ [pt] :=
    projList_mkTower _ _ (by simp)
  have h2 := projList_take (fs.length + 1) fs.length (mkTower (fs ++ [pt])) (Nat.le_succ _)
  rw [h1, List.take_left] at h2
  rw [← hlen, ← h2]

open Classical in
/-- The stage of a member of the ω-iterate (junk off it). -/
noncomputable def rkOf (Φ : V → V) (t : V) : Nat :=
  if h : ∃ n, t ∈ˢ iterF Φ n then Classical.choose h else 0

theorem mem_iterF_rkOf {Φ : V → V} {t : V} (ht : t ∈ˢ iterU Φ) : t ∈ˢ iterF Φ (rkOf Φ t) := by
  unfold rkOf
  have h := mem_iterU.mp ht
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem rkOf_ne_zero {Φ : V → V} {t : V} (ht : t ∈ˢ iterU Φ) : rkOf Φ t ≠ 0 := by
  intro h0
  have := mem_iterF_rkOf ht
  rw [h0, iterF_zero] at this
  exact not_mem_empty _ this

/-- The semantic fold of a minor-space member along a fitting spine. -/
theorem minorSpI_fold {ℓ : Nat} {c : List V → V} (hc0 : ℓ = 0 → ∀ acc, c acc ∈ˢ (univZero : V)) :
    ∀ {Fs : List AVExpr} {ρf : Nat → V} {acc : List V} {m : V} {as : List V},
      m ∈ˢ minorSpI ℓ c Fs ρf acc → SpineFit ρf Fs as →
      as.foldl SetTheory.app m ∈ˢ c (acc ++ as)
  | [], _, acc, m, [], hm, _ => by simpa [minorSpI] using hm
  | [], _, _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρf, acc, m, a :: as, hm, hsp => by
    have happ : SetTheory.app m a ∈ˢ minorSpI ℓ c Fs (cons a ρf) (acc ++ [a]) :=
      app_mem_piR hm hsp.1 (fun h0 x _ => minorSpI_zero_univZero h0 (hc0 h0) Fs (cons x ρf) (acc ++ [x]))
    have := minorSpI_fold hc0 (Fs := Fs) (as := as) happ hsp.2
    rw [List.append_assoc, List.singleton_append] at this
    rw [List.foldl_cons]
    exact this

/-- At a zero elimination level an ih tower is inhabited exactly when
its conclusion is, given the motive inhabited at the components. -/
theorem ihSp_zero_inhab {M : V} {fs : List V} {C : V} :
    ∀ {is : List Nat} {x : V}, x ∈ˢ ihSp 0 M fs C is →
      (∀ i ∈ is, ∃ z, z ∈ˢ SetTheory.app M (fs.getD i pt)) → ∃ y, y ∈ˢ C
  | [], x, hx, _ => ⟨x, hx⟩
  | i :: is, x, hx, hg => by
    have hx' : x ∈ˢ piR 0 (SetTheory.app M (fs.getD i pt)) (fun _ => ihSp 0 M fs C is) := hx
    rw [piR_zero] at hx'
    obtain ⟨z, hz⟩ := hg i List.mem_cons_self
    obtain ⟨y, hy⟩ := of_mem_truthVal hx' z hz
    exact ihSp_zero_inhab hy (fun i hi => hg i (List.mem_cons_of_mem _ hi))


/-! ## The K-frame package -/

/-- The carrier at the K-frame `(p⃗, motive, minors)`: the tagged union
of the restricted chains scoped there (`nIdx = 0`). -/
noncomputable def carK (w : Nat) (ρ₀ : Nat → V) (Fss Ess : List (List AVExpr)) : V :=
  sumSet w (sumFibre w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess))

/-- The functor at the parameter frame under the K-frame. -/
noncomputable def ΦK (w : Nat) (ρ₀ : Nat → V) (Fss Fss₀ : List (List AVExpr))
    (rss : List (List Bool)) : V → V :=
  fixStep w (frP Fss.length 0 ρ₀) rss Fss₀

/-- The constructor arities and recursive positions at the K-frame. -/
abbrev arK (Fss : List (List AVExpr)) : Nat → Nat := fun j => (Fss.getD j []).length
abbrev recsK (Fss : List (List AVExpr)) (rss : List (List Bool)) : Nat → List Nat :=
  fun j => recIdx (rss.getD j []) (Fss.getD j []).length

/-- The recursion's data at the K-frame. -/
noncomputable def fixSemK (ρ₀ : Nat → V) (Fss : List (List AVExpr)) (rss : List (List Bool)) :
    Nat → V → V :=
  fixSem (frMs Fss.length 0 ρ₀) (recsK Fss rss) (arK Fss)

theorem fixSemK_inj {ρ₀ : Nat → V} {Fss : List (List AVExpr)} {rss : List (List Bool)} (n j : Nat)
    {fs : List V} (hlen : fs.length = (Fss.getD j []).length) :
    fixSemK ρ₀ Fss rss (n + 1) (inj j (mkTower (fs ++ [pt])))
      = stepBr (frMs Fss.length 0 ρ₀) (recsK Fss rss) j (fixSemK ρ₀ Fss rss n) fs :=
  fixSem_inj n j hlen

/-- `Π (t : T), M t` at the K-frame, semantically. -/
noncomputable def piTMK (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess : List (List AVExpr)) : V :=
  piR ℓ (carK w ρ₀ Fss Ess) fun t => SetTheory.app (frMi Fss.length 0 ρ₀) t

/-- The recursive route's K-frame hypotheses: the case split's
(`RecHypR`, unindexed), the elimination restriction, and the carrier's
identification with the least fixed point of the X-chain functor at
the parameter frame (`hokX`, `hreal`, `hcar`). -/
structure FixHypR (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess Fss₀ : List (List AVExpr))
    (rss : List (List Bool)) : Prop where
  hyp : RecHypR ℓ w ρ₀ Fss Ess [] (fun _ => carK w ρ₀ Fss Ess) rss
  hwℓ : w = 0 → ℓ = 0
  hokX : FixChainsOk w (frP Fss.length 0 ρ₀) rss Fss₀
  hreal : ChainsReal (carK w ρ₀ Fss Ess) (frP Fss.length 0 ρ₀) rss Fss₀ Fss
  hcar : fixCarrier w (frP Fss.length 0 ρ₀) rss Fss₀ = carK w ρ₀ Fss Ess

namespace FixHypR

variable {ℓ w : Nat} {ρ₀ : Nat → V} {Fss Ess Fss₀ : List (List AVExpr)} {rss : List (List Bool)}

theorem hok (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) :
    SumFieldsOkB w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess) := by
  have := h.hyp.hok
  simpa only [List.length_nil, Nat.zero_add] using this

theorem hM (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) :
    frMi Fss.length 0 ρ₀ ∈ˢ piR (ℓ + 1) (carK w ρ₀ Fss Ess) fun _ => (univ ℓ : V) := by
  have := h.hyp.hM
  simpa only [List.length_nil, Nat.zero_add, carK] using this

theorem hM0 (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (h0 : ℓ = 0) (x : V) :
    SetTheory.app (frMi Fss.length 0 ρ₀) x ∈ˢ (univZero : V) := h.hyp.hM0 h0 x

theorem hMapp (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) {t : V} (ht : t ∈ˢ carK w ρ₀ Fss Ess) :
    SetTheory.app (frMi Fss.length 0 ρ₀) t ∈ˢ (univ ℓ : V) :=
  app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hM ht

theorem hEs0 (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) {j : Nat} (hj : j < Fss.length) :
    Ess.getD j [] = [] :=
  List.eq_nil_of_length_eq_zero (h.hyp.hEs j hj)

/-- The carrier is the ω-iterate of the functor. -/
theorem car_iter (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) :
    carK w ρ₀ Fss Ess = iterU (ΦK w ρ₀ Fss Fss₀ rss) := by
  rw [← h.hcar]; exact fixCarrier_eq_iterU h.hokX

theorem iterF_sub (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (n : Nat) :
    iterF (ΦK w ρ₀ Fss Fss₀ rss) n ⊆ˢ carK w ρ₀ Fss Ess := by
  rw [h.car_iter]; exact iterF_subset_iterU _ n

theorem hlen₀ (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) : Fss₀.length = Fss.length := h.hreal.2.1

/-- The recursive components of a fitting real spine are carrier
members. -/
theorem rec_mem (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) {j : Nat} (hj : j < Fss.length) {fs : List V}
    (hsp : SpineFit (frP Fss.length 0 ρ₀) (Fss.getD j []) fs) {i : Nat}
    (hi : i ∈ recsK Fss rss j) : fs.getD i pt ∈ˢ carK w ρ₀ Fss Ess := by
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
  have := spineFit_getD_mem hsp hik
  have hT := h.hyp.hrecT j hj i hik hri (fs.take i)
    (by rw [List.length_take, hsp.length_eq]; omega)
  simp only [List.length_nil] at hT
  rw [hT] at this
  exact this

/-- The conclusion of constructor `j`'s minor at a spine. -/
theorem conc_eq (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) {j : Nat} (hj : j < Fss.length) (fs : List V) :
    concI w (frP Fss.length 0 ρ₀) (frM Fss.length 0 ρ₀) (Ess.getD j []) j fs
      = SetTheory.app (frMi Fss.length 0 ρ₀) (ctorValI w j fs) := by
  rw [h.hEs0 hj]; rfl

theorem hms (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) {j : Nat} (hj : j < Fss.length) :
    frMs Fss.length 0 ρ₀ j
      ∈ˢ minorSpI ℓ
        (fun fs => ihSp ℓ (frMi Fss.length 0 ρ₀) fs
          (SetTheory.app (frMi Fss.length 0 ρ₀) (ctorValI w j fs)) (recsK Fss rss j))
        (Fss.getD j []) (frP Fss.length 0 ρ₀) [] := by
  have := h.hyp.hms j hj
  simp only [List.length_nil] at this
  have hc : (fun fs => ihSp ℓ (frMi Fss.length 0 ρ₀) fs
      (concI w (frP Fss.length 0 ρ₀) (frM Fss.length 0 ρ₀) (Ess.getD j []) j fs)
      (recIdx (rss.getD j []) (Fss.getD j []).length))
      = fun fs => ihSp ℓ (frMi Fss.length 0 ρ₀) fs
        (SetTheory.app (frMi Fss.length 0 ρ₀) (ctorValI w j fs)) (recsK Fss rss j) := by
    funext fs; rw [h.conc_eq hj]
  rw [hc] at this
  exact this

theorem minor_pt (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (h0 : ℓ = 0) {j : Nat}
    (hj : j < Fss.length) : frMs Fss.length 0 ρ₀ j = pt := h.hyp.minor_pt h0 hj

end FixHypR

/-! ## The rank recursion at the K-frame -/

section Recursion

variable {ℓ w : Nat} {ρ₀ : Nat → V} {Fss Ess Fss₀ : List (List AVExpr)} {rss : List (List Bool)}

/-- **The rank recursion lands in the motive** (nonzero elimination
level, graph regime). -/
theorem fixSem_mem (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) (hℓ : ℓ ≠ 0) :
    ∀ n t, t ∈ˢ iterF (ΦK w ρ₀ Fss Fss₀ rss) n →
      fixSemK ρ₀ Fss rss n t ∈ˢ SetTheory.app (frMi Fss.length 0 ρ₀) t
  | 0, _, ht => absurd ht (not_mem_empty _)
  | n + 1, t, ht => by
    rw [iterF_succ] at ht
    obtain ⟨j, fs, rfl, hjF, -, hlen, hrec, hfit⟩ := fixStep_elim hw ht
    have hj : j < Fss.length := by rw [← h.hlen₀]; exact hjF
    have hsp := hfit (h.iterF_sub n) h.hreal
    have hlen' : fs.length = (Fss.getD j []).length := hsp.length_eq
    rw [fixSemK_inj n j hlen']
    unfold stepBr
    rw [List.foldl_append]
    have hfold := minorSpI_fold (fun h0 => absurd h0 hℓ) (h.hms hj) hsp
    rw [List.nil_append] at hfold
    have := ihSp_fold (fun h0 => absurd h0 hℓ) (fixSemK ρ₀ Fss rss n) hfold ?_
    · rwa [ctorValI, if_neg hw] at this
    · intro i hi
      obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
      exact fixSem_mem h hw hℓ n _ (hrec i (by omega) hri)

/-- **Stability**: above a member's stage the recursion is constant. -/
theorem fixSem_stable (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) :
    ∀ n t, t ∈ˢ iterF (ΦK w ρ₀ Fss Fss₀ rss) n → ∀ m, n ≤ m →
      fixSemK ρ₀ Fss rss m t = fixSemK ρ₀ Fss rss n t
  | 0, _, ht, _, _ => absurd ht (not_mem_empty _)
  | n + 1, t, ht, m, hnm => by
    rw [iterF_succ] at ht
    obtain ⟨j, fs, rfl, hjF, -, hlen, hrec, hfit⟩ := fixStep_elim hw ht
    have hj : j < Fss.length := by rw [← h.hlen₀]; exact hjF
    have hsp := hfit (h.iterF_sub n) h.hreal
    have hlen' : fs.length = (Fss.getD j []).length := hsp.length_eq
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    rw [fixSemK_inj n j hlen', fixSemK_inj m' j hlen']
    refine stepBr_congr fun i hi => ?_
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    exact fixSem_stable h hw n _ (hrec i (by omega) hri) m' (by omega)

/-- **Inhabitation at a zero elimination level**, both regimes: the
motive is inhabited at every carrier member. -/
theorem fixSem_inhab (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (h0 : ℓ = 0) :
    ∀ n t, t ∈ˢ iterF (ΦK w ρ₀ Fss Fss₀ rss) n →
      ∃ y, y ∈ˢ SetTheory.app (frMi Fss.length 0 ρ₀) t
  | 0, _, ht => absurd ht (not_mem_empty _)
  | n + 1, t, ht => by
    rw [iterF_succ] at ht
    have key : ∀ (j : Nat) (fs : List V), j < Fss₀.length →
        (∀ l, l < fs.length → (rss.getD j []).getD l false = true →
          fs.getD l pt ∈ˢ iterF (ΦK w ρ₀ Fss Fss₀ rss) n) →
        SpineFit (frP Fss.length 0 ρ₀) (Fss.getD j []) fs →
        ∃ y, y ∈ˢ SetTheory.app (frMi Fss.length 0 ρ₀) (ctorValI w j fs) := by
      intro j fs hjF hrec hsp
      have hj : j < Fss.length := by rw [← h.hlen₀]; exact hjF
      have hlen' : fs.length = (Fss.getD j []).length := hsp.length_eq
      have hms := h.hms hj
      rw [h0] at hms
      obtain ⟨x, hx⟩ := minorSpI_zero_inhab hms hsp
      rw [List.nil_append] at hx
      refine ihSp_zero_inhab hx fun i hi => ?_
      obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
      exact fixSem_inhab h h0 n _ (hrec i (by omega) hri)
    by_cases hw : w = 0
    · subst hw
      obtain ⟨rfl, j, fs, hjF, -, -, hrec, hfit⟩ := fixStep_zero_elim ht
      have := key j fs hjF hrec (hfit (h.iterF_sub n) h.hreal)
      rwa [ctorValI, if_pos rfl] at this
    · obtain ⟨j, fs, rfl, hjF, -, -, hrec, hfit⟩ := fixStep_elim hw ht
      have := key j fs hjF hrec (hfit (h.iterF_sub n) h.hreal)
      rwa [ctorValI, if_neg hw] at this

/-- The motive is inhabited at every carrier member (zero level). -/
theorem motive_inhab (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (h0 : ℓ = 0) {t : V}
    (ht : t ∈ˢ carK w ρ₀ Fss Ess) : (pt : V) ∈ˢ SetTheory.app (frMi Fss.length 0 ρ₀) t := by
  rw [h.car_iter] at ht
  obtain ⟨n, hn⟩ := mem_iterU.mp ht
  obtain ⟨y, hy⟩ := fixSem_inhab h h0 n t hn
  have := eq_pt_of_mem_univZero (h.hM0 h0 t) hy
  subst this
  exact hy

/-- The candidate fixed point: each carrier member's own stage's
value. -/
noncomputable def fixStar (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess Fss₀ : List (List AVExpr))
    (rss : List (List Bool)) : V :=
  lamR ℓ (carK w ρ₀ Fss Ess) fun t =>
    fixSemK ρ₀ Fss rss (rkOf (ΦK w ρ₀ Fss Fss₀ rss) t) t

theorem fixStar_mem (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) (hℓ : ℓ ≠ 0) :
    fixStar ℓ w ρ₀ Fss Ess Fss₀ rss ∈ˢ piTMK ℓ w ρ₀ Fss Ess := by
  refine lamR_mem fun t ht => ?_
  rw [h.car_iter] at ht
  exact fixSem_mem h hw hℓ _ t (mem_iterF_rkOf ht)

/-- **The candidate's unfolding** at a constructor value: the step at
the candidate itself. -/
theorem fixStar_app (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) (hℓ : ℓ ≠ 0)
    {j : Nat} (hj : j < Fss.length) {fs : List V}
    (hsp : SpineFit (frP Fss.length 0 ρ₀) (Fss.getD j []) fs)
    (ht : inj j (mkTower (fs ++ [pt])) ∈ˢ carK w ρ₀ Fss Ess) :
    SetTheory.app (fixStar ℓ w ρ₀ Fss Ess Fss₀ rss) (inj j (mkTower (fs ++ [pt])))
      = stepBr (frMs Fss.length 0 ρ₀) (recsK Fss rss) j
          (fun x => SetTheory.app (fixStar ℓ w ρ₀ Fss Ess Fss₀ rss) x) fs := by
  have hlen' : fs.length = (Fss.getD j []).length := hsp.length_eq
  have ht' := ht
  rw [h.car_iter] at ht'
  have hrk := mem_iterF_rkOf ht'
  obtain ⟨n, hn⟩ : ∃ n, rkOf (ΦK w ρ₀ Fss Fss₀ rss) (inj j (mkTower (fs ++ [pt]))) = n + 1 :=
    ⟨rkOf (ΦK w ρ₀ Fss Fss₀ rss) (inj j (mkTower (fs ++ [pt]))) - 1,
      by have := rkOf_ne_zero ht'; omega⟩
  rw [hn] at hrk
  have hv : SetTheory.app (fixStar ℓ w ρ₀ Fss Ess Fss₀ rss) (inj j (mkTower (fs ++ [pt])))
      = stepBr (frMs Fss.length 0 ρ₀) (recsK Fss rss) j (fixSemK ρ₀ Fss rss n) fs := by
    unfold fixStar
    rw [app_lamR_pos hℓ ht, hn, fixSemK_inj n j hlen']
  rw [hv]
  refine stepBr_congr fun i hi => ?_
  -- the recursive component: in the carrier, at stage `n`
  have hmem : fs.getD i pt ∈ˢ carK w ρ₀ Fss Ess := h.rec_mem hj hsp hi
  have hrhs : SetTheory.app (fixStar ℓ w ρ₀ Fss Ess Fss₀ rss) (fs.getD i pt)
      = fixSemK ρ₀ Fss rss (rkOf (ΦK w ρ₀ Fss Fss₀ rss) (fs.getD i pt)) (fs.getD i pt) := by
    unfold fixStar
    rw [app_lamR_pos hℓ hmem]
  rw [hrhs]
  -- its stage-`n` value is its own stage's value, by stability
  rw [iterF_succ] at hrk
  have hlen0 : fs.length = (Fss₀.getD j []).length := by
    rw [hlen']; exact h.hreal.length_eq hj
  obtain ⟨hrec', -⟩ := fixStep_elim_at hw hrk hlen0
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
  have hstage : fs.getD i pt ∈ˢ iterF (ΦK w ρ₀ Fss Fss₀ rss) n := hrec' i (by omega) hri
  have hrk' := mem_iterF_rkOf (h.car_iter ▸ hmem)
  rw [← fixSem_stable h hw n _ hstage (max n (rkOf (ΦK w ρ₀ Fss Fss₀ rss) (fs.getD i pt)))
      (Nat.le_max_left _ _),
    ← fixSem_stable h hw _ _ hrk' (max n (rkOf (ΦK w ρ₀ Fss Fss₀ rss) (fs.getD i pt)))
      (Nat.le_max_right _ _)]

end Recursion

/-! ## The spelled pieces at the K-frame -/

/-- The carrier spelled at the K-frame. -/
def carrierAV (w n : Nat) (Fss Ess : List (List AVExpr)) : AVExpr :=
  sumBodyAV w (rChains (n + 1) 0 Fss Ess)

/-- `Π (t : T), M t` at the K-frame. -/
def piTMAV (ℓ w n : Nat) (Fss Ess : List (List AVExpr)) : AVExpr :=
  .pi w ℓ (carrierAV w n Fss Ess) (.app (motAppAV n 0 1) (.bvar 0))

/-- The one-step unfolding `λ r t. case_r t` at the K-frame. -/
def fixStepAV (ℓ w n : Nat) (Fss Ess : List (List AVExpr)) (ar : Nat → Nat)
    (recs : Nat → List Nat) : AVExpr :=
  .lam (imaxN w ℓ) (piTMAV ℓ w n Fss Ess) (.lam ℓ ((carrierAV w n Fss Ess).liftN 1 0)
    (.app (caseRecAVR ℓ w (rChains (n + 1) 0 Fss Ess) ar recs n 0 n 2 0 (.proj 0 (.bvar 0)))
      (.proj 1 (.bvar 0))))

/-- `Σ' (r : Π t, M t), Step r = r` at the K-frame. -/
def fixSigAV (ℓ w n : Nat) (Fss Ess : List (List AVExpr)) (ar : Nat → Nat)
    (recs : Nat → List Nat) : AVExpr :=
  AVExpr.mkAppN (.const .psigma [imaxN w ℓ, 0]) [piTMAV ℓ w n Fss Ess,
    .lam 1 (piTMAV ℓ w n Fss Ess)
      (.eqE ((piTMAV ℓ w n Fss Ess).liftN 1 0)
        (.app ((fixStepAV ℓ w n Fss Ess ar recs).liftN 1 0) (.bvar 0)) (.bvar 0))]

/-- The selected fixed point `(choice Σ prf).1` at the K-frame. -/
def fixSelAV (ℓ w n : Nat) (Fss Ess : List (List AVExpr)) (ar : Nat → Nat)
    (recs : Nat → List Nat) : AVExpr :=
  .proj 0 (AVExpr.mkAppN (.const .choice [imaxN w ℓ]) [fixSigAV ℓ w n Fss Ess ar recs, .prf])

/-- The recursor body under the major (depth `1`): the selected fixed
point at the major; the point at a squash instantiation. -/
def fixRecBodyAV (ℓ w n : Nat) (Fss Ess : List (List AVExpr)) (ar : Nat → Nat)
    (recs : Nat → List Nat) : AVExpr :=
  if w = 0 then .prf else .app ((fixSelAV ℓ w n Fss Ess ar recs).liftN 1 0) (.bvar 0)

theorem fixRecBodyAV_zero (ℓ n : Nat) (Fss Ess : List (List AVExpr)) (ar : Nat → Nat)
    (recs : Nat → List Nat) : fixRecBodyAV ℓ 0 n Fss Ess ar recs = .prf := if_pos rfl

theorem fixRecBodyAV_pos {w : Nat} (hw : w ≠ 0) (ℓ n : Nat) (Fss Ess : List (List AVExpr))
    (ar : Nat → Nat) (recs : Nat → List Nat) :
    fixRecBodyAV ℓ w n Fss Ess ar recs
      = .app ((fixSelAV ℓ w n Fss Ess ar recs).liftN 1 0) (.bvar 0) := if_neg hw

/-- The recursor leaf. -/
def directFixRecAV (ℓ w : Nat) (rds : List (Nat × Nat × AVExpr)) (Fss Ess : List (List AVExpr))
    (ar : Nat → Nat) (recs : Nat → List Nat) : AVExpr :=
  mkLamsC ℓ rds (fixRecBodyAV ℓ w Fss.length Fss Ess ar recs)

/-! ## The pieces' facts -/

section Facts

variable {ℓ w : Nat} {ρ₀ : Nat → V} {Fss Ess Fss₀ : List (List AVExpr)} {rss : List (List Bool)}

theorem carrierAV_facts0 (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) :
    interp2 V ρ₀ (carrierAV w Fss.length Fss Ess) = carK w ρ₀ Fss Ess ∧
    AnnotOk2 V ρ₀ (carrierAV w Fss.length Fss Ess) :=
  ⟨sumBodyAV_interp h.hok, sumBodyAV_ok2 h.hok⟩

theorem carrierAV_facts (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) {d : Nat} {σ : Nat → V}
    (hfr : RecFrameS d ρ₀ σ) :
    interp2 V σ ((carrierAV w Fss.length Fss Ess).liftN d 0) = carK w ρ₀ Fss Ess ∧
    AnnotOk2 V σ ((carrierAV w Fss.length Fss Ess).liftN d 0) := by
  rw [interp2_liftN, AnnotOk2_liftN, hfr]
  exact carrierAV_facts0 h

theorem carK_univ (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) : carK w ρ₀ Fss Ess ∈ˢ (univ w : V) :=
  sumSet_univ_of_okB h.hok

/-- `Π (t : T), M t`: its value, its formation, its grading. -/
theorem piTMAV_facts0 (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) :
    interp2 V ρ₀ (piTMAV ℓ w Fss.length Fss Ess) = piTMK ℓ w ρ₀ Fss Ess ∧
      piTMK ℓ w ρ₀ Fss Ess ∈ˢ (univ (imaxN w ℓ) : V) ∧
      AnnotOk2 V ρ₀ (piTMAV ℓ w Fss.length Fss Ess) := by
  have hfr0 : RecFrameS 0 ρ₀ ρ₀ := shiftE_zero_zero ρ₀
  obtain ⟨hcv, hcok⟩ := carrierAV_facts0 h
  have hmot : ∀ t : V, interp2 V (cons t ρ₀) (motAppAV Fss.length 0 1) = frMi Fss.length 0 ρ₀ ∧
      AnnotOk2 V (cons t ρ₀) (motAppAV Fss.length 0 1) := by
    intro t
    have := motApp_facts (hfr0.push t) h.hyp.toRecHypCore
    simpa only [List.length_nil] using this
  have hv : interp2 V ρ₀ (piTMAV ℓ w Fss.length Fss Ess) = piTMK ℓ w ρ₀ Fss Ess := by
    show piR ℓ (interp2 V ρ₀ (carrierAV w Fss.length Fss Ess)) _ = _
    rw [hcv]
    exact piR_congr fun t _ => by rw [interp2_app, (hmot t).1, interp2_bvar, cons_zero]
  refine ⟨hv, ?_, ?_⟩
  · have := piR_mem_univ (u := w) (carK_univ h) (fun t ht => h.hMapp ht)
    exact this
  · show AnnotOk2 V ρ₀ (.pi w ℓ _ _)
    rw [AnnotOk2_pi]
    refine ⟨hcok, fun t ht => ?_⟩
    rw [hcv] at ht
    rw [AnnotOk2_app]
    refine ⟨(hmot t).2, trivial, ℓ + 1, carK w ρ₀ Fss Ess, fun _ => (univ ℓ : V), ?_, ?_,
      fun h => absurd h (Nat.succ_ne_zero _)⟩
    · rw [(hmot t).1]; exact h.hM
    · rw [interp2_bvar, cons_zero]; exact ht

theorem piTMAV_facts (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) {d : Nat} {σ : Nat → V}
    (hfr : RecFrameS d ρ₀ σ) :
    interp2 V σ ((piTMAV ℓ w Fss.length Fss Ess).liftN d 0) = piTMK ℓ w ρ₀ Fss Ess ∧
      AnnotOk2 V σ ((piTMAV ℓ w Fss.length Fss Ess).liftN d 0) := by
  rw [interp2_liftN, AnnotOk2_liftN, hfr]
  exact ⟨(piTMAV_facts0 h).1, (piTMAV_facts0 h).2.2⟩

theorem piTMK_univZero (_h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (h0 : ℓ = 0) :
    piTMK ℓ w ρ₀ Fss Ess ∈ˢ (univZero : V) := by
  unfold piTMK; rw [h0]; exact piR_zero_mem_univZero

/-- The semantic step. -/
noncomputable def stepK (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess : List (List AVExpr))
    (rss : List (List Bool)) : V :=
  lamR (imaxN w ℓ) (piTMK ℓ w ρ₀ Fss Ess)
    fun r => lamR ℓ (carK w ρ₀ Fss Ess) fun t =>
      interp2 V (cons t (cons r ρ₀))
        (.app (caseRecAVR ℓ w (rChains (Fss.length + 1) 0 Fss Ess) (arK Fss) (recsK Fss rss)
          Fss.length 0 Fss.length 2 0 (.proj 0 (.bvar 0))) (.proj 1 (.bvar 0)))

/-- The case facts, normalized to the K-frame (`nIdx = 0`). -/
theorem caseK_facts (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) {r : V}
    (hr : r ∈ˢ piTMK ℓ w ρ₀ Fss Ess) (t : V) :
    ((interp2 V (cons t (cons r ρ₀)) (.proj 0 (.bvar 0)) ∈ˢ (omega : V) →
      interp2 V (cons t (cons r ρ₀)) (caseRecAVR ℓ w (rChains (Fss.length + 1) 0 Fss Ess)
          (arK Fss) (recsK Fss rss) Fss.length 0 Fss.length 2 0 (.proj 0 (.bvar 0)))
        ∈ˢ motSem ℓ w (sumFibre w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess))
            (frMi Fss.length 0 ρ₀) 0 (interp2 V (cons t (cons r ρ₀)) (.proj 0 (.bvar 0))) ∧
      ∀ i, interp2 V (cons t (cons r ρ₀)) (.proj 0 (.bvar 0)) = vnat i → i < Fss.length →
        interp2 V (cons t (cons r ρ₀)) (caseRecAVR ℓ w (rChains (Fss.length + 1) 0 Fss Ess)
            (arK Fss) (recsK Fss rss) Fss.length 0 Fss.length 2 0 (.proj 0 (.bvar 0)))
          = baseSemR ℓ (sumFibre w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess))
              (frMs Fss.length 0 ρ₀) (Fss.getD i []).length
              (recIdx (rss.getD i []) (Fss.getD i []).length) r i) ∧
    (AnnotOk2 V (cons t (cons r ρ₀)) (.proj 0 (.bvar 0)) →
      (ℓ ≠ 0 → interp2 V (cons t (cons r ρ₀)) (.proj 0 (.bvar 0)) ∈ˢ (omega : V)) →
      AnnotOk2 V (cons t (cons r ρ₀)) (caseRecAVR ℓ w (rChains (Fss.length + 1) 0 Fss Ess)
        (arK Fss) (recsK Fss rss) Fss.length 0 Fss.length 2 0 (.proj 0 (.bvar 0))))) := by
  have hfr0 : RecFrameS 0 ρ₀ ρ₀ := shiftE_zero_zero ρ₀
  have hfr2 : RecFrameS 2 ρ₀ (cons t (cons r ρ₀)) := hfr0.step t r
  have hr' : r ∈ˢ piR ℓ ((fun _ => carK w ρ₀ Fss Ess) (frameIdx ([] : List AVExpr).length ρ₀))
      fun t => SetTheory.app (frMi Fss.length ([] : List AVExpr).length ρ₀) t := hr
  have := caseRec_factsR hw h.hyp hr' Fss.length (D := 2) (j := 0) (σ := cons t (cons r ρ₀))
    (k := .proj 0 (.bvar 0)) hfr2 (by omega) (by rfl) (Nat.zero_add _)
  simp only [List.length_nil, Nat.zero_add] at this
  exact this

/-- The inner body `case_r t` at a carrier member: graded and in the
motive. -/
theorem fixInner_facts (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) {r : V}
    (hr : r ∈ˢ piTMK ℓ w ρ₀ Fss Ess) {t : V} (ht : t ∈ˢ carK w ρ₀ Fss Ess) :
    AnnotOk2 V (cons t (cons r ρ₀))
        (.app (caseRecAVR ℓ w (rChains (Fss.length + 1) 0 Fss Ess) (arK Fss) (recsK Fss rss)
          Fss.length 0 Fss.length 2 0 (.proj 0 (.bvar 0))) (.proj 1 (.bvar 0))) ∧
      interp2 V (cons t (cons r ρ₀))
        (.app (caseRecAVR ℓ w (rChains (Fss.length + 1) 0 Fss Ess) (arK Fss) (recsK Fss rss)
          Fss.length 0 Fss.length 2 0 (.proj 0 (.bvar 0))) (.proj 1 (.bvar 0)))
        ∈ˢ SetTheory.app (frMi Fss.length 0 ρ₀) t := by
  have hcase := caseK_facts h hw hr t
  have hok0 := major_proj_ok2 hw h.hok (σ := cons t (cons r ρ₀)) ht (i := 0) (by omega)
  have hok1 := major_proj_ok2 hw h.hok (σ := cons t (cons r ρ₀)) ht (i := 1) (by omega)
  obtain ⟨i, a, ha, hta⟩ := sumSet_elim hw ht
  have htag : interp2 V (cons t (cons r ρ₀)) (.proj 0 (.bvar 0)) = vnat i := by
    rw [interp2_proj, if_pos rfl, interp2_bvar, cons_zero, hta, sfst_inj]
  have hpay : interp2 V (cons t (cons r ρ₀)) (.proj 1 (.bvar 0)) = a := by
    rw [interp2_proj, if_neg Nat.one_ne_zero, interp2_bvar, cons_zero, hta, ssnd_inj]
  have hkω : interp2 V (cons t (cons r ρ₀)) (.proj 0 (.bvar 0)) ∈ˢ (omega : V) := by
    rw [htag]; exact vnat_mem_omega i
  obtain ⟨hmem, -⟩ := hcase.1 hkω
  rw [htag, motSem_vnat, Nat.zero_add] at hmem
  have hB0 : ℓ = 0 → ∀ y, y ∈ˢ sumFibre w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess) i →
      SetTheory.app (frMi Fss.length 0 ρ₀) (injW w i y) ∈ˢ (univZero : V) :=
    fun h0 y _ => h.hM0 h0 _
  refine ⟨?_, ?_⟩
  · rw [AnnotOk2_app]
    refine ⟨hcase.2 hok0 (fun _ => hkω), hok1, ℓ, sumFibre w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess) i,
      _, hmem, ?_, hB0⟩
    rw [hpay]; exact ha
  · rw [interp2_app, hpay]
    have := app_mem_piR hmem ha hB0
    rwa [injW_pos hw, ← hta] at this

/-- The inner body's iota at a constructor value. -/
theorem fixInner_iota (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) {r : V}
    (hr : r ∈ˢ piTMK ℓ w ρ₀ Fss Ess)
    {j : Nat} (hj : j < Fss.length) {fs : List V} (hlen : fs.length = (Fss.getD j []).length)
    (hmem : mkTower (fs ++ [pt]) ∈ˢ sumFibre w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess) j) :
    interp2 V (cons (inj j (mkTower (fs ++ [pt]))) (cons r ρ₀))
        (.app (caseRecAVR ℓ w (rChains (Fss.length + 1) 0 Fss Ess) (arK Fss) (recsK Fss rss)
          Fss.length 0 Fss.length 2 0 (.proj 0 (.bvar 0))) (.proj 1 (.bvar 0)))
      = stepBr (frMs Fss.length 0 ρ₀) (recsK Fss rss) j (fun x => SetTheory.app r x) fs := by
  have hcase := caseK_facts h hw hr (inj j (mkTower (fs ++ [pt])))
  have htag : interp2 V (cons (inj j (mkTower (fs ++ [pt]))) (cons r ρ₀)) (.proj 0 (.bvar 0))
      = vnat j := by
    rw [interp2_proj, if_pos rfl, interp2_bvar, cons_zero, sfst_inj]
  have hpay : interp2 V (cons (inj j (mkTower (fs ++ [pt]))) (cons r ρ₀)) (.proj 1 (.bvar 0))
      = mkTower (fs ++ [pt]) := by
    rw [interp2_proj, if_neg Nat.one_ne_zero, interp2_bvar, cons_zero, ssnd_inj]
  have hkω : interp2 V (cons (inj j (mkTower (fs ++ [pt]))) (cons r ρ₀)) (.proj 0 (.bvar 0))
      ∈ˢ (omega : V) := by
    rw [htag]; exact vnat_mem_omega j
  have hsel := (hcase.1 hkω).2 j htag hj
  rw [interp2_app, hsel, hpay]
  unfold baseSemR stepBr
  by_cases h0 : ℓ = 0
  · rw [h0, lamR_zero, app_pt, h.minor_pt h0 hj]
    exact (foldl_app_pt_sum _).symm
  · rw [app_lamR_pos h0 hmem]
    -- the projections of the point-terminated tuple are the fields
    have hproj : ∀ i, i < fs.length → projS i (mkTower (fs ++ [pt])) = fs.getD i pt := by
      intro i hi
      rw [projS_mkTower i (fs ++ [pt]) (by simp; omega), List.getElem_append_left hi,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    congr 2
    · rw [← projList_eq_map_range, ← hlen]
      apply List.ext_getElem
      · rw [projList_length]
      · intro i h1 h2
        rw [projList_get _ _ _ (by rwa [projList_length] at h1), hproj i h2,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]
    · apply List.map_congr_left
      intro i hi
      obtain ⟨hik, -⟩ := mem_recIdx.mp hi
      rw [hproj i (by omega)]

/-- **The step's facts**: its value, its membership in
`(Π t, M t) → (Π t, M t)`, its grading. -/
theorem fixStepAV_facts (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) :
    interp2 V ρ₀ (fixStepAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss))
        = stepK ℓ w ρ₀ Fss Ess rss ∧
      stepK ℓ w ρ₀ Fss Ess rss
        ∈ˢ piR (imaxN w ℓ) (piTMK ℓ w ρ₀ Fss Ess) (fun _ => piTMK ℓ w ρ₀ Fss Ess) ∧
      AnnotOk2 V ρ₀ (fixStepAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) := by
  have hfr0 : RecFrameS 0 ρ₀ ρ₀ := shiftE_zero_zero ρ₀
  obtain ⟨hpv, hpu, hpok⟩ := piTMAV_facts0 h
  have hcar : ∀ r : V, interp2 V (cons r ρ₀) ((carrierAV w Fss.length Fss Ess).liftN 1 0)
      = carK w ρ₀ Fss Ess ∧ AnnotOk2 V (cons r ρ₀) ((carrierAV w Fss.length Fss Ess).liftN 1 0) :=
    fun r => carrierAV_facts h (hfr0.push r)
  have hB0 : ℓ = 0 → ∀ t, t ∈ˢ carK w ρ₀ Fss Ess →
      SetTheory.app (frMi Fss.length 0 ρ₀) t ∈ˢ (univZero : V) := fun h0 t _ => h.hM0 h0 t
  have hv : interp2 V ρ₀ (fixStepAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss))
      = stepK ℓ w ρ₀ Fss Ess rss := by
    unfold fixStepAV stepK
    rw [interp2_lam, hpv]
    refine lamR_congr fun r _ => ?_
    rw [interp2_lam, (hcar r).1]
  refine ⟨hv, ?_, ?_⟩
  · unfold stepK
    refine lamR_mem fun r hr => lamR_mem fun t ht => ?_
    exact (fixInner_facts h hw hr ht).2
  · unfold fixStepAV
    rw [AnnotOk2_lam]
    refine ⟨hpok, fun r hr => ?_, fun _ => piTMK ℓ w ρ₀ Fss Ess, fun r hr => ?_, fun h0 r _ => ?_⟩
    · rw [hpv] at hr
      rw [AnnotOk2_lam]
      refine ⟨(hcar r).2, fun t ht => ?_, fun t => SetTheory.app (frMi Fss.length 0 ρ₀) t,
        fun t ht => ?_, fun h0 t ht => ?_⟩
      · rw [(hcar r).1] at ht
        exact (fixInner_facts h hw hr ht).1
      · rw [(hcar r).1] at ht
        exact (fixInner_facts h hw hr ht).2
      · rw [(hcar r).1] at ht
        exact hB0 h0 t ht
    · rw [hpv] at hr
      rw [interp2_lam, (hcar r).1]
      exact lamR_mem fun t ht => (fixInner_facts h hw hr ht).2
    · exact piTMK_univZero h ((imaxN_eq_zero_iff w ℓ).mp h0)

theorem stepK_app (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) {r : V}
    (hr : r ∈ˢ piTMK ℓ w ρ₀ Fss Ess)
    {j : Nat} (hj : j < Fss.length) {fs : List V} (hlen : fs.length = (Fss.getD j []).length)
    (hmem : mkTower (fs ++ [pt]) ∈ˢ sumFibre w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess) j)
    (hℓ : ℓ ≠ 0) :
    SetTheory.app (SetTheory.app (stepK ℓ w ρ₀ Fss Ess rss) r) (inj j (mkTower (fs ++ [pt])))
      = stepBr (frMs Fss.length 0 ρ₀) (recsK Fss rss) j (fun x => SetTheory.app r x) fs := by
  have hu : imaxN w ℓ ≠ 0 := fun h0 => hℓ ((imaxN_eq_zero_iff w ℓ).mp h0)
  have ht : inj j (mkTower (fs ++ [pt])) ∈ˢ carK w ρ₀ Fss Ess := inj_mem hw hmem
  unfold stepK
  rw [app_lamR_pos hu hr, app_lamR_pos hℓ ht]
  exact fixInner_iota h hw hr hj hlen hmem

/-- **A fixed point exists** (graph regime): the rank-recursive
candidate above a zero level, the point at level zero. -/
theorem fixed_exists (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) :
    ∃ r, r ∈ˢ piTMK ℓ w ρ₀ Fss Ess ∧ SetTheory.app (stepK ℓ w ρ₀ Fss Ess rss) r = r := by
  by_cases hℓ : ℓ = 0
  · -- the point: the motive is inhabited everywhere
    refine ⟨pt, ?_, ?_⟩
    · unfold piTMK
      rw [hℓ, piR_zero]
      exact pt_mem_truthVal fun t ht => ⟨pt, motive_inhab h hℓ ht⟩
    · unfold stepK
      rw [(imaxN_eq_zero_iff w ℓ).mpr hℓ, lamR_zero, app_pt]
  · refine ⟨fixStar ℓ w ρ₀ Fss Ess Fss₀ rss, fixStar_mem h hw hℓ, ?_⟩
    have hu : imaxN w ℓ ≠ 0 := fun h0 => hℓ ((imaxN_eq_zero_iff w ℓ).mp h0)
    have hmem := fixStar_mem h hw hℓ
    have hv : SetTheory.app (stepK ℓ w ρ₀ Fss Ess rss) (fixStar ℓ w ρ₀ Fss Ess Fss₀ rss)
        = lamR ℓ (carK w ρ₀ Fss Ess) fun t =>
            interp2 V (cons t (cons (fixStar ℓ w ρ₀ Fss Ess Fss₀ rss) ρ₀))
              (.app (caseRecAVR ℓ w (rChains (Fss.length + 1) 0 Fss Ess) (arK Fss) (recsK Fss rss)
                Fss.length 0 Fss.length 2 0 (.proj 0 (.bvar 0))) (.proj 1 (.bvar 0))) := by
      unfold stepK
      rw [app_lamR_pos hu hmem]
    rw [hv]
    show _ = lamR ℓ (carK w ρ₀ Fss Ess) fun t =>
      fixSemK ρ₀ Fss rss (rkOf (ΦK w ρ₀ Fss Fss₀ rss) t) t
    refine lamR_congr fun t ht => ?_
    -- at a carrier member: a constructor value
    have ht' := ht
    rw [h.car_iter] at ht'
    have hrk := mem_iterF_rkOf ht'
    obtain ⟨n, hn⟩ : ∃ n, rkOf (ΦK w ρ₀ Fss Fss₀ rss) t = n + 1 :=
      ⟨rkOf (ΦK w ρ₀ Fss Fss₀ rss) t - 1, by have := rkOf_ne_zero ht'; omega⟩
    rw [hn, iterF_succ] at hrk
    obtain ⟨j, fs, rfl, hjF, -, -, -, hfit⟩ := fixStep_elim hw hrk
    have hj : j < Fss.length := by rw [← h.hlen₀]; exact hjF
    have hsp := hfit (h.iterF_sub n) h.hreal
    have hlen' : fs.length = (Fss.getD j []).length := hsp.length_eq
    obtain ⟨j', a', ha', hta'⟩ := sumSet_elim hw ht
    obtain ⟨rfl, rfl⟩ := inj_inj hta'
    have hstar := fixStar_app h hw hℓ hj hsp ht
    have hstar' : fixSemK ρ₀ Fss rss (rkOf (ΦK w ρ₀ Fss Fss₀ rss) (inj j (mkTower (fs ++ [pt]))))
        (inj j (mkTower (fs ++ [pt])))
        = stepBr (frMs Fss.length 0 ρ₀) (recsK Fss rss) j
            (fun x => SetTheory.app (fixStar ℓ w ρ₀ Fss Ess Fss₀ rss) x) fs := by
      rw [← hstar]
      unfold fixStar
      rw [app_lamR_pos hℓ ht]
    rw [hstar']
    exact fixInner_iota h hw (fixStar_mem h hw hℓ) hj hlen' ha'

omit [SetTheory V] in
theorem imaxN_max_zero (w ℓ : Nat) : Nat.max (imaxN w ℓ) 0 = imaxN w ℓ := Nat.max_zero _

/-- `pt` witnesses the double negation of an inhabited set. -/
theorem pt_mem_dnegSpace2 {A x : V} (hx : x ∈ˢ A) : (pt : V) ∈ˢ dnegSpace2 V A := by
  unfold dnegSpace2
  have h1 : piR 0 A (fun _ => (empty : V)) = empty := by
    rw [piR_zero]
    exact truthVal_eq_empty fun hf => not_mem_empty _ (hf x hx).choose_spec
  rw [h1, piR_zero_empty]
  exact pt_mem_unitSet

/-- The sigma type's fibre function. -/
noncomputable def sigBK (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess : List (List AVExpr))
    (rss : List (List Bool)) : V :=
  lamR 1 (piTMK ℓ w ρ₀ Fss Ess) fun r => eqv (SetTheory.app (stepK ℓ w ρ₀ Fss Ess rss) r) r

/-- The sigma type's value. -/
noncomputable def sigK (ℓ w : Nat) (ρ₀ : Nat → V) (Fss Ess : List (List AVExpr))
    (rss : List (List Bool)) : V :=
  sigmaSet (imaxN w ℓ) (piTMK ℓ w ρ₀ Fss Ess) fun r => SetTheory.app (sigBK ℓ w ρ₀ Fss Ess rss) r

theorem sigBK_app {r : V} (hr : r ∈ˢ piTMK ℓ w ρ₀ Fss Ess) :
    SetTheory.app (sigBK ℓ w ρ₀ Fss Ess rss) r = eqv (SetTheory.app (stepK ℓ w ρ₀ Fss Ess rss) r) r :=
  app_lamR_pos Nat.one_ne_zero hr

theorem sigBK_mem : sigBK ℓ w ρ₀ Fss Ess rss ∈ˢ psigmaFibreSpace V 0 (piTMK ℓ w ρ₀ Fss Ess) :=
  lamR_mem fun r _ => by rw [univ_zero]; exact eqv_mem_univZero _ _

theorem psigmaV2_mem_general (u v : Nat) :
    psigmaV2 V u v ∈ˢ piR (Nat.max u v + 1) (univ u : V)
      (fun A => piR (Nat.max u v + 1) (psigmaFibreSpace V v A) fun _ => (univ (Nat.max u v) : V)) :=
  lamR_mem fun _ hA => lamR_mem fun _ hB => sigma_mem_univ hA (fun _ hx => psigmaFibre_apply V hB hx)

/-- The sigma type's value, formation and grading. -/
theorem fixSigAV_facts (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) :
    interp2 V ρ₀ (fixSigAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) = sigK ℓ w ρ₀ Fss Ess rss ∧
      sigK ℓ w ρ₀ Fss Ess rss ∈ˢ (univ (imaxN w ℓ) : V) ∧
      AnnotOk2 V ρ₀ (fixSigAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) := by
  have hfr0 : RecFrameS 0 ρ₀ ρ₀ := shiftE_zero_zero ρ₀
  obtain ⟨hpv, hpu, hpok⟩ := piTMAV_facts0 h
  obtain ⟨hsv, hsm, hsok⟩ := fixStepAV_facts h hw
  have hu0 : imaxN w ℓ = 0 → piTMK ℓ w ρ₀ Fss Ess ∈ˢ (univZero : V) :=
    fun h0 => piTMK_univZero h ((imaxN_eq_zero_iff w ℓ).mp h0)
  -- the pieces under the sigma's λ
  have hpv1 : ∀ r : V, interp2 V (cons r ρ₀) ((piTMAV ℓ w Fss.length Fss Ess).liftN 1 0)
      = piTMK ℓ w ρ₀ Fss Ess := fun r => (piTMAV_facts h (hfr0.push r)).1
  have hsv1 : ∀ r : V, interp2 V (cons r ρ₀)
      ((fixStepAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)).liftN 1 0)
      = stepK ℓ w ρ₀ Fss Ess rss := by
    intro r; rw [interp2_liftN, shiftE_succ_cons, shiftE_zero_zero, hsv]
  have hsok1 : ∀ r : V, AnnotOk2 V (cons r ρ₀)
      ((fixStepAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)).liftN 1 0) := by
    intro r; rw [AnnotOk2_liftN, shiftE_succ_cons, shiftE_zero_zero]; exact hsok
  have hbody : ∀ r : V, r ∈ˢ piTMK ℓ w ρ₀ Fss Ess →
      interp2 V (cons r ρ₀) (.eqE ((piTMAV ℓ w Fss.length Fss Ess).liftN 1 0)
        (.app ((fixStepAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)).liftN 1 0) (.bvar 0))
        (.bvar 0))
        = eqv (SetTheory.app (stepK ℓ w ρ₀ Fss Ess rss) r) r ∧
      AnnotOk2 V (cons r ρ₀) (.eqE ((piTMAV ℓ w Fss.length Fss Ess).liftN 1 0)
        (.app ((fixStepAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)).liftN 1 0) (.bvar 0))
        (.bvar 0)) := by
    intro r hr
    refine ⟨?_, ?_⟩
    · rw [interp2_eqE, interp2_app, hsv1, interp2_bvar, cons_zero]
    · rw [AnnotOk2_eqE, AnnotOk2_app]
      refine ⟨⟨hsok1 r, trivial, imaxN w ℓ, piTMK ℓ w ρ₀ Fss Ess, fun _ => piTMK ℓ w ρ₀ Fss Ess,
        ?_, ?_, fun h0 _ _ => hu0 h0⟩, trivial⟩
      · rw [hsv1]; exact hsm
      · rw [interp2_bvar, cons_zero]; exact hr
  -- the λ's value
  have hlamv : interp2 V ρ₀ (.lam 1 (piTMAV ℓ w Fss.length Fss Ess)
      (.eqE ((piTMAV ℓ w Fss.length Fss Ess).liftN 1 0)
        (.app ((fixStepAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)).liftN 1 0) (.bvar 0))
        (.bvar 0)))
      = sigBK ℓ w ρ₀ Fss Ess rss := by
    unfold sigBK
    rw [interp2_lam, hpv]
    exact lamR_congr fun r hr => (hbody r hr).1
  have hps := psigmaV2_mem_general (V := V) (imaxN w ℓ) 0
  rw [imaxN_max_zero] at hps
  have hv : interp2 V ρ₀ (fixSigAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss))
      = sigK ℓ w ρ₀ Fss Ess rss := by
    show SetTheory.app (SetTheory.app (psigmaV2 V (imaxN w ℓ) 0)
      (interp2 V ρ₀ (piTMAV ℓ w Fss.length Fss Ess))) (interp2 V ρ₀ (.lam 1 _ _)) = _
    rw [hpv, hlamv, psigmaV2_app V hpu sigBK_mem, imaxN_max_zero]
    rfl
  refine ⟨hv, ?_, ?_⟩
  · have := sigma_mem_univ (u := imaxN w ℓ) (v := 0) hpu
      (fun r hr => psigmaFibre_apply V (sigBK_mem (ℓ := ℓ) (w := w) (ρ₀ := ρ₀) (Fss := Fss)
        (Ess := Ess) (rss := rss)) hr)
    rwa [imaxN_max_zero] at this
  · show AnnotOk2 V ρ₀ (.app (.app (.const .psigma [imaxN w ℓ, 0]) _) _)
    rw [AnnotOk2_app]
    refine ⟨?_, ?_, ?_⟩
    · rw [AnnotOk2_app]
      exact ⟨trivial, hpok, imaxN w ℓ + 1, univ (imaxN w ℓ),
        fun A => piR (imaxN w ℓ + 1) (psigmaFibreSpace V 0 A) fun _ => (univ (imaxN w ℓ) : V),
        hps, hpv ▸ hpu, fun h => absurd h (Nat.succ_ne_zero _)⟩
    · rw [AnnotOk2_lam]
      refine ⟨hpok, fun r hr => ?_, fun _ => (univ 0 : V), fun r hr => ?_,
        fun h => absurd h Nat.one_ne_zero⟩
      · rw [hpv] at hr; exact (hbody r hr).2
      · rw [hpv] at hr; rw [(hbody r hr).1, univ_zero]; exact eqv_mem_univZero _ _
    · refine ⟨imaxN w ℓ + 1, psigmaFibreSpace V 0 (piTMK ℓ w ρ₀ Fss Ess),
        fun _ => (univ (imaxN w ℓ) : V), ?_, ?_, fun h => absurd h (Nat.succ_ne_zero _)⟩
      · show SetTheory.app (psigmaV2 V (imaxN w ℓ) 0) (interp2 V ρ₀ (piTMAV ℓ w Fss.length Fss Ess)) ∈ˢ _
        rw [hpv]
        exact app_mem_piR_pos (Nat.succ_ne_zero _) hps hpu
      · rw [hlamv]; exact sigBK_mem

/-- **The selected fixed point**: a member of `Π t, M t`, a fixed
point of the step, and the selection is graded. -/
theorem fixSelAV_facts (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) :
    interp2 V ρ₀ (fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) ∈ˢ piTMK ℓ w ρ₀ Fss Ess ∧
      SetTheory.app (stepK ℓ w ρ₀ Fss Ess rss)
          (interp2 V ρ₀ (fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)))
        = interp2 V ρ₀ (fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) ∧
      AnnotOk2 V ρ₀ (fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) := by
  obtain ⟨hSv, hSu, hSok⟩ := fixSigAV_facts h hw
  -- the sigma type is inhabited
  obtain ⟨r₀, hr₀, hfix₀⟩ := fixed_exists h hw
  have hSne : ∃ x, x ∈ˢ sigK ℓ w ρ₀ Fss Ess rss := by
    by_cases hu0 : imaxN w ℓ = 0
    · refine ⟨pt, ?_⟩
      unfold sigK
      rw [hu0]
      exact pt_mem_sigma (a := r₀) (b := pt) hr₀ (by rw [sigBK_app hr₀, hfix₀]; exact pt_mem_eqv_self _)
    · refine ⟨spair r₀ pt, ?_⟩
      exact spair_mem hu0 hr₀ (by rw [sigBK_app hr₀, hfix₀]; exact pt_mem_eqv_self _)
  have hchoice : interp2 V ρ₀ (AVExpr.mkAppN (.const .choice [imaxN w ℓ])
      [fixSigAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss), .prf])
      = schoice (sigK ℓ w ρ₀ Fss Ess rss) := by
    show SetTheory.app (SetTheory.app (choiceV2 V (imaxN w ℓ)) (interp2 V ρ₀ (fixSigAV ℓ w Fss.length
      Fss Ess (arK Fss) (recsK Fss rss)))) pt = _
    rw [hSv]
    exact choiceV2_app V hSu (pt_mem_dnegSpace2 hSne.choose_spec)
  have hsel := schoice_mem hSne.choose_spec
  obtain ⟨a, b, ha, hb, hz, hpos⟩ := mem_sigma_elim hsel
  rw [sigBK_app ha] at hb
  have hfixa : SetTheory.app (stepK ℓ w ρ₀ Fss Ess rss) a = a := eq_of_mem_eqv hb
  have hval : interp2 V ρ₀ (fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) = a := by
    show sfst (interp2 V ρ₀ (AVExpr.mkAppN (.const .choice [imaxN w ℓ]) [_, .prf])) = a
    rw [hchoice]
    by_cases hu0 : imaxN w ℓ = 0
    · rw [hz hu0, sfst_pt]
      exact (eq_pt_of_mem_univZero (piTMK_univZero h ((imaxN_eq_zero_iff w ℓ).mp hu0)) ha).symm
    · rw [hpos hu0, sfst_spair]
  refine ⟨by rw [hval]; exact ha, by rw [hval]; exact hfixa, ?_⟩
  -- the grading
  have hchoiceV : choiceV2 V (imaxN w ℓ) ∈ˢ piR (imaxN w ℓ) (univ (imaxN w ℓ) : V)
      (fun A => piR (imaxN w ℓ) (dnegSpace2 V A) fun _ => A) :=
    lamR_mem fun A hA => lamR_mem fun h hh => schoice_mem (exists_mem_of_dneg2 V hh).choose_spec
  show AnnotOk2 V ρ₀ (.proj 0 (AVExpr.mkAppN (.const .choice [imaxN w ℓ])
    [fixSigAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss), .prf]))
  rw [AnnotOk2_proj]
  refine ⟨?_, by omega, imaxN w ℓ, 0, piTMK ℓ w ρ₀ Fss Ess,
    fun r => SetTheory.app (sigBK ℓ w ρ₀ Fss Ess rss) r, ?_, ?_, ?_⟩
  · show AnnotOk2 V ρ₀ (.app (.app (.const .choice [imaxN w ℓ]) _) .prf)
    rw [AnnotOk2_app]
    refine ⟨?_, trivial, imaxN w ℓ, dnegSpace2 V (sigK ℓ w ρ₀ Fss Ess rss),
      fun _ => sigK ℓ w ρ₀ Fss Ess rss, ?_, ?_, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨trivial, hSok, imaxN w ℓ, univ (imaxN w ℓ),
        fun A => piR (imaxN w ℓ) (dnegSpace2 V A) fun _ => A, hchoiceV, hSv ▸ hSu,
        fun hu0 A _ => ?_⟩
      show piR (imaxN w ℓ) _ _ ∈ˢ _
      rw [hu0]; exact piR_zero_mem_univZero
    · show SetTheory.app (choiceV2 V (imaxN w ℓ)) (interp2 V ρ₀ (fixSigAV ℓ w Fss.length Fss Ess
        (arK Fss) (recsK Fss rss))) ∈ˢ _
      rw [hSv]
      refine app_mem_piR hchoiceV hSu (fun hu0 A _ => ?_)
      show piR (imaxN w ℓ) _ _ ∈ˢ _
      rw [hu0]; exact piR_zero_mem_univZero
    · exact pt_mem_dnegSpace2 hSne.choose_spec
    · intro hu0 _ _
      rw [hu0] at hSu
      rwa [univ_zero] at hSu
  · rw [hchoice, imaxN_max_zero]; exact hsel
  · exact (piTMAV_facts0 h).2.1
  · intro r hr
    show SetTheory.app (sigBK ℓ w ρ₀ Fss Ess rss) r ∈ˢ _
    rw [sigBK_app hr, univ_zero]; exact eqv_mem_univZero _ _

/-! ## The body -/

/-- **The recursor body's facts** at a carrier member: graded, and in
the motive at the major. -/
theorem fixRecBody_facts (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) {σ : Nat → V}
    (hfr : RecFrameS 1 ρ₀ σ) (ht : σ 0 ∈ˢ carK w ρ₀ Fss Ess) :
    AnnotOk2 V σ (fixRecBodyAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) ∧
    interp2 V σ (fixRecBodyAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss))
      ∈ˢ SetTheory.app (frMi Fss.length 0 ρ₀) (σ 0) := by
  by_cases hw : w = 0
  · subst hw
    rw [fixRecBodyAV_zero]
    exact ⟨trivial, motive_inhab h (h.hwℓ rfl) ht⟩
  · rw [fixRecBodyAV_pos hw]
    obtain ⟨hR, -, hRok⟩ := fixSelAV_facts h hw
    have hsel1 : interp2 V σ ((fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)).liftN 1 0)
        = interp2 V ρ₀ (fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) := by
      rw [interp2_liftN, hfr]
    have hsel1ok : AnnotOk2 V σ ((fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)).liftN 1 0) := by
      rw [AnnotOk2_liftN, hfr]; exact hRok
    have hB0 : ℓ = 0 → ∀ t, t ∈ˢ carK w ρ₀ Fss Ess →
        SetTheory.app (frMi Fss.length 0 ρ₀) t ∈ˢ (univZero : V) := fun h0 t _ => h.hM0 h0 t
    refine ⟨?_, ?_⟩
    · rw [AnnotOk2_app]
      refine ⟨hsel1ok, trivial, ℓ, carK w ρ₀ Fss Ess, fun t => SetTheory.app (frMi Fss.length 0 ρ₀) t,
        ?_, ?_, hB0⟩
      · rw [hsel1]; exact hR
      · rw [interp2_bvar]; exact ht
    · rw [interp2_app, hsel1, interp2_bvar]
      exact app_mem_piR hR ht hB0

/-- The fields of a payload of the K-frame fibre fit the real chain at
the parameter frame. -/
theorem spineFit_of_fibre (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) {j : Nat}
    (hj : j < Fss.length) {fs : List V} (hlen : fs.length = (Fss.getD j []).length)
    (hmem : mkTower (fs ++ [pt]) ∈ˢ sumFibre w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess) j) :
    SpineFit (frP Fss.length 0 ρ₀) (Fss.getD j []) fs := by
  have hjF := h.hyp.rChain_getElem? hj
  simp only [List.length_nil, Nat.zero_add] at hjF
  rw [sumFibre_of_getElem? hjF] at hmem
  have := restricted_member_elim hw (Fs := liftFields (Fss.length + 1) 0 (Fss.getD j []))
    (eqs := idxEqsAt (Fss.length + 1) 0 (Fss.getD j []).length (Ess.getD j [])) (ρ := ρ₀)
    (y := mkTower (fs ++ [pt])) hmem
  rw [liftFields_length] at this
  obtain ⟨hspL, -, -, -⟩ := this
  have hspP := (spineFit_liftFields (Fss.length + 1)).mp hspL
  have hpl : projList (Fss.getD j []).length (mkTower (fs ++ [pt])) = fs := by
    have h1 : projList (fs.length + 1) (mkTower (fs ++ [pt])) = fs ++ [pt] :=
      projList_mkTower _ _ (by simp)
    have h2 := projList_take (fs.length + 1) fs.length (mkTower (fs ++ [pt])) (Nat.le_succ _)
    rw [h1, List.take_left] at h2
    rw [← hlen, ← h2]
  rw [hpl] at hspP
  show SpineFit (shiftE (0 + Fss.length + 1) 0 ρ₀) _ _
  rw [Nat.zero_add]
  exact hspP

/-- **The body's iota** (graph regime): at the injection of
constructor `j`'s point-terminated tupler the body is minor `j` folded
along the fields and along the recursor (the leaf applied at the
K-frame) at the recursive fields. -/
theorem fixRecBody_iota (h : FixHypR ℓ w ρ₀ Fss Ess Fss₀ rss) (hw : w ≠ 0) {σ : Nat → V}
    (hfr : RecFrameS 1 ρ₀ σ) {j : Nat} (hj : j < Fss.length) {fs : List V}
    (hlen : fs.length = (Fss.getD j []).length)
    (hmaj : σ 0 = inj j (mkTower (fs ++ [pt])))
    (hmem : mkTower (fs ++ [pt]) ∈ˢ sumFibre w ρ₀ (rChains (Fss.length + 1) 0 Fss Ess) j) :
    interp2 V σ (fixRecBodyAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss))
      = (fs ++ (recsK Fss rss j).map fun i =>
          SetTheory.app (lamR ℓ (carK w ρ₀ Fss Ess) fun t =>
            interp2 V (cons t ρ₀) (fixRecBodyAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)))
            (fs.getD i pt)).foldl SetTheory.app (frMs Fss.length 0 ρ₀ j) := by
  rw [fixRecBodyAV_pos hw]
  obtain ⟨hR, hfix, -⟩ := fixSelAV_facts h hw
  have hsel1 : ∀ σ' : Nat → V, RecFrameS 1 ρ₀ σ' →
      interp2 V σ' ((fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)).liftN 1 0)
        = interp2 V ρ₀ (fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) := by
    intro σ' hfr'; rw [interp2_liftN, hfr']
  have hbody : ∀ t : V, interp2 V (cons t ρ₀)
      (.app ((fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)).liftN 1 0) (.bvar 0))
      = SetTheory.app (interp2 V ρ₀ (fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss))) t := by
    intro t
    rw [interp2_app, hsel1 (cons t ρ₀) (by unfold RecFrameS; rw [shiftE_succ_cons, shiftE_zero_zero]),
      interp2_bvar, cons_zero]
  rw [interp2_app, hsel1 σ hfr, interp2_bvar, hmaj]
  by_cases hℓ : ℓ = 0
  · -- everything is the point
    have hR0 : interp2 V ρ₀ (fixSelAV ℓ w Fss.length Fss Ess (arK Fss) (recsK Fss rss)) = pt :=
      eq_pt_of_mem_univZero (piTMK_univZero h hℓ) hR
    rw [hR0, app_pt, h.minor_pt hℓ hj]
    exact (foldl_app_pt_sum _).symm
  · rw [← hfix, stepK_app h hw hR hj hlen hmem hℓ]
    unfold stepBr
    congr 2
    apply List.map_congr_left
    intro i hi
    have hsp := spineFit_of_fibre h hw hj hlen hmem
    have hmemi : fs.getD i pt ∈ˢ carK w ρ₀ Fss Ess := h.rec_mem hj hsp hi
    rw [app_lamR_pos hℓ hmemi, hbody]

end Facts

end Lech.Semantics
