import Lech.Semantics.Tower.FixCaseI
import Lech.Semantics.Tower.SumRec
import Lech.Semantics.Tower.SumWire

/-!
# The recursive family's recursor: the fixed point and its leaf (task #188, indexed)

The recursor of a directly installed recursive family is spelled as a
**closed** term — a fixed point of its one-step unfolding over the
recursor's whole type `RecTy = Π p⃗ M m⃗ ı⃗ t, M ı⃗ t`, selected by
`Classical.choice`:

    Step := λ (r : RecTy). λ p⃗ M m⃗ ı⃗ t. case_r t     (`fixStepAVI`)
    Σ    := Σ' (r : RecTy), Step r = r                 (`fixSigAVI`)
    Sel  := (choice Σ prf).1                           (`fixSelAVI`; the leaf)

The function being unfolded thus sits at the BOTTOM of every frame of
the case split — below the parameters — so the sum route's K-frame
arithmetic (`(p⃗, M, m⃗, ı⃗)` above the frame's tail) applies unchanged,
and the recursor type's binder data, being closed, needs no lifting
under `λ r`.  The inductive hypothesis for a recursive field `f_i`
(with index expressions `e⃗_i` at the earlier fields) is
`r p⃗ M m⃗ e⃗_i f_i`, the index expressions read at the payload's
projections by SUBSTITUTION (`substProj`: `interp2_inst0` at each field
binder — no λ-tower).  The case split's abstract ih obligation
(`IhArgsOk`, `FixCaseI.lean`) is discharged here.

The certificate `prf : ¬¬Σ` is the existence of a fixed point,
exhibited by rank recursion over the ω-iterate family (`fixSem`, as in
the non-indexed checkpoint): the candidate is the semantic λ-tower over
the recursor's binder data (`lamTower`) whose body at a leaf frame is the
major's own stage's value.
-/

namespace Lech.Semantics
open Lech.SetModel

open SetTheory
open Lech.SetTheory.Tower
open Lech.TT (VExpr)

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Substitution of the payload's projections -/

/-- Substitute the `i` innermost (virtual) field variables by the
projections of the payload `y = bvar 0` below them. -/
def substProj : Nat → AVExpr → AVExpr
  | 0, e => e
  | i + 1, e => substProj i (e.inst (projAV i (.bvar i)))

theorem interp2_substProj (σ : Nat → V) (y : V) :
    ∀ (i : Nat) (e : AVExpr),
      interp2 V (cons y σ) (substProj i e) = interp2 V (consList (projList i y) (cons y σ)) e
  | 0, _ => rfl
  | i + 1, e => by
    show interp2 V (cons y σ) (substProj i (e.inst (projAV i (.bvar i)))) = _
    rw [interp2_substProj σ y i, interp2_inst0, projAV_interp, interp2_bvar]
    have hy : consList (projList i y) (cons y σ) i = y := by
      have := consList_apply_add (projList i y) (cons y σ) 0
      rwa [Nat.zero_add, projList_length] at this
    rw [hy, consList_snoc', ← projList_snoc]

theorem AnnotOk2_substProj (σ : Nat → V) (y : V) :
    ∀ (i : Nat) (e : AVExpr),
      (∀ m, m < i → AnnotOk2 V (consList (projList m y) (cons y σ)) (projAV m (.bvar m))) →
      (AnnotOk2 V (cons y σ) (substProj i e) ↔
        AnnotOk2 V (consList (projList i y) (cons y σ)) e)
  | 0, _, _ => Iff.rfl
  | i + 1, e, hp => by
    show AnnotOk2 V (cons y σ) (substProj i (e.inst (projAV i (.bvar i)))) ↔ _
    rw [AnnotOk2_substProj σ y i _ (fun m hm => hp m (by omega)),
      AnnotOk2_inst0 V (hp i (by omega)), projAV_interp, interp2_bvar]
    have hy : consList (projList i y) (cons y σ) i = y := by
      have := consList_apply_add (projList i y) (cons y σ) 0
      rwa [Nat.zero_add, projList_length] at this
    rw [hy, consList_snoc', ← projList_snoc]

omit [SetTheory V] in
theorem shiftE_add' (a b : Nat) (ρ : Nat → V) : shiftE (a + b) 0 ρ = shiftE b 0 (shiftE a 0 ρ) := by
  rw [shiftE_zero, shiftE_zero, shiftE_zero]
  funext i
  show ρ (i + (a + b)) = ρ (i + b + a)
  congr 1
  omega

/-! ## The Π-tower's fold and application chain -/

/-- A member of a Π-tower's reading, applied along a fitting spine,
lands in the conclusion's reading at the spine's frame. -/
theorem mkPisAV_fold_mem {m : Nat} {C : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {f : V} {as : List V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) →
      (m = 0 → ∀ as', SpineFit ρ (ds.map (·.2.2)) as' → interp2 V (consList as' ρ) C ∈ˢ (univZero : V)) →
      f ∈ˢ interp2 V ρ (mkPisAV ds C) → SpineFit ρ (ds.map (·.2.2)) as →
      as.foldl SetTheory.app f ∈ˢ interp2 V (consList as ρ) C
  | [], _, _, [], _, _, hf, _ => hf
  | [], _, _, _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, _, hsp => hsp.elim
  | d :: ds, ρ, f, a :: as, hz, h0, hf, hsp => by
    have hf' : f ∈ˢ piR d.2.1 (interp2 V ρ d.2.2)
        (fun x => interp2 V (cons x ρ) (mkPisAV ds C)) := hf
    have hB0 : d.2.1 = 0 → ∀ x, x ∈ˢ interp2 V ρ d.2.2 →
        interp2 V (cons x ρ) (mkPisAV ds C) ∈ˢ (univZero : V) := by
      intro hd x hx
      have hm : m = 0 := (hz d (.head _)).mpr hd
      cases ds with
      | nil =>
        have := h0 hm [x] ⟨hx, trivial⟩
        rw [consList_cons, consList_nil] at this
        exact this
      | cons d' ds' =>
        show piR d'.2.1 _ _ ∈ˢ _
        rw [(hz d' (.tail _ (.head _))).mp hm]
        exact piR_zero_mem_univZero
    rw [List.foldl_cons]
    refine mkPisAV_fold_mem (ds := ds) (ρ := cons a ρ) (f := SetTheory.app f a) (as := as)
      (fun d' hd' => hz d' (.tail _ hd')) ?_ (app_mem_piR hf' hsp.1 hB0) hsp.2
    intro hm as' hsp'
    have := h0 hm (a :: as') ⟨hsp.1, hsp'⟩
    rwa [consList_cons] at this

/-- The application chain of a Π-tower member along a fitting spine is
graded. -/
theorem appChainOk_of_mkPisAV' {m : Nat} {C : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {f : V} {as : List V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) →
      (m = 0 → ∀ as', SpineFit ρ (ds.map (·.2.2)) as' → interp2 V (consList as' ρ) C ∈ˢ (univZero : V)) →
      f ∈ˢ interp2 V ρ (mkPisAV ds C) → SpineFit ρ (ds.map (·.2.2)) as → AppChainOk f as
  | [], _, _, [], _, _, _, _ => fun l hl => absurd hl (Nat.not_lt_zero _)
  | [], _, _, _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, _, _, hsp => hsp.elim
  | d :: ds, ρ, f, a :: as, hz, h0, hf, hsp => by
    have hf' : f ∈ˢ piR d.2.1 (interp2 V ρ d.2.2)
        (fun x => interp2 V (cons x ρ) (mkPisAV ds C)) := hf
    have hB0 : d.2.1 = 0 → ∀ x, x ∈ˢ interp2 V ρ d.2.2 →
        interp2 V (cons x ρ) (mkPisAV ds C) ∈ˢ (univZero : V) := by
      intro hd x hx
      have hm : m = 0 := (hz d (.head _)).mpr hd
      cases ds with
      | nil =>
        have := h0 hm [x] ⟨hx, trivial⟩
        rw [consList_cons, consList_nil] at this
        exact this
      | cons d' ds' =>
        show piR d'.2.1 _ _ ∈ˢ _
        rw [(hz d' (.tail _ (.head _))).mp hm]
        exact piR_zero_mem_univZero
    intro l hl
    cases l with
    | zero =>
      refine ⟨d.2.1, interp2 V ρ d.2.2, fun x => interp2 V (cons x ρ) (mkPisAV ds C), ?_, ?_, hB0⟩
      · simpa using hf'
      · simpa using hsp.1
    | succ l =>
      have ih := appChainOk_of_mkPisAV' (ds := ds) (ρ := cons a ρ) (f := SetTheory.app f a)
        (as := as) (fun d' hd' => hz d' (.tail _ hd'))
        (fun hm as' hsp' => by
          have := h0 hm (a :: as') ⟨hsp.1, hsp'⟩
          rwa [consList_cons] at this)
        (app_mem_piR hf' hsp.1 hB0) hsp.2 l (by simpa using hl)
      obtain ⟨v, A, B, h1, h2, h3⟩ := ih
      refine ⟨v, A, B, ?_, ?_, h3⟩
      · simpa only [List.take_succ_cons, List.foldl_cons] using h1
      · simpa only [List.getD_cons_succ] using h2

/-! ## The semantic λ-tower over binder data -/

/-- The semantic λ-tower over binder data, with a body given as a
function of the leaf frame. -/
noncomputable def lamTower (m : Nat) : (Nat → V) → List (Nat × Nat × AVExpr) → ((Nat → V) → V) → V
  | ρ, [], g => g ρ
  | ρ, d :: ds, g => lamR m (interp2 V ρ d.2.2) fun a => lamTower m (cons a ρ) ds g

/-- The tower's walk premise: at every leaf frame reached the body is
in the conclusion's reading (a truth value at a zero bit). -/
def TowerWalk (m : Nat) (C : AVExpr) (g : (Nat → V) → V) :
    (Nat → V) → List (Nat × Nat × AVExpr) → Prop
  | ρ, [] => g ρ ∈ˢ interp2 V ρ C ∧ (m = 0 → interp2 V ρ C ∈ˢ (univZero : V))
  | ρ, d :: ds => ∀ a, a ∈ˢ interp2 V ρ d.2.2 → TowerWalk m C g (cons a ρ) ds

theorem towerWalk_res_univZero {m : Nat} {C : AVExpr} {g : (Nat → V) → V} (h0 : m = 0) :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → TowerWalk m C g ρ ds →
      interp2 V ρ (mkPisAV ds C) ∈ˢ (univZero : V)
  | [], _, _, h => h.2 h0
  | d :: _, _, hz, _ => by
    show piR d.2.1 _ _ ∈ˢ _
    rw [(hz d (.head _)).mp h0]
    exact piR_zero_mem_univZero

/-- **The tower inhabits the Π-tower's reading.** -/
theorem lamTower_mem {m : Nat} {C : AVExpr} {g : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → TowerWalk m C g ρ ds →
      lamTower m ρ ds g ∈ˢ interp2 V ρ (mkPisAV ds C)
  | [], _, _, h => h.1
  | d :: ds, ρ, hz, h => by
    show lamR m (interp2 V ρ d.2.2) (fun a => lamTower m (cons a ρ) ds g)
      ∈ˢ piR d.2.1 (interp2 V ρ d.2.2) fun a => interp2 V (cons a ρ) (mkPisAV ds C)
    exact lamR_mem_zero_agree (hz d (.head _))
      fun a ha => lamTower_mem (fun d' hd' => hz d' (.tail _ hd')) (h a ha)

/-- The constant-bit spelled tower reads to the semantic tower. -/
theorem interp2_mkLamsC (m : Nat) (b : AVExpr) :
    ∀ (ds : List (Nat × Nat × AVExpr)) (ρ : Nat → V),
      interp2 V ρ (mkLamsC m ds b) = lamTower m ρ ds (fun σ => interp2 V σ b)
  | [], _ => rfl
  | d :: ds, ρ => by
    show lamR m (interp2 V ρ d.2.2) (fun a => interp2 V (cons a ρ) (mkLamsC m ds b)) = _
    unfold lamTower
    exact lamR_congr fun a _ => interp2_mkLamsC m b ds (cons a ρ)

omit [SetTheory V] in
/-- Two frames agreeing below a depth. -/
theorem agreeOff_consList_ge : ∀ (as : List V) (ρ₁ ρ₂ : Nat → V),
    AgreeOff (fun i => as.length ≤ i) (consList as ρ₁) (consList as ρ₂)
  | [], _, _ => fun i hi => absurd (Nat.zero_le i) hi
  | a :: as, ρ₁, ρ₂ => by
    rw [consList_cons, consList_cons]
    intro i hi
    simp only [List.length_cons] at hi
    have hi' : i < as.length + 1 := Nat.lt_of_not_le hi
    by_cases h : i < as.length
    · exact agreeOff_consList_ge as (cons a ρ₁) (cons a ρ₂) i (by omega)
    · have hi'' : i = as.length := by omega
      subst hi''
      have h1 := consList_apply_add as (cons a ρ₁) 0
      have h2 := consList_apply_add as (cons a ρ₂) 0
      rw [Nat.zero_add] at h1 h2
      rw [h1, h2, cons_zero, cons_zero]

/-- **Bottom-frame independence** of a tower over closed binder data:
the domains are closed at their depth, so the readings agree at any
two bottoms; the bodies must agree at corresponding leaf frames. -/
theorem lamTower_congr_bottom {m : Nat} {g₁ g₂ : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {as : List V} {ρ₁ ρ₂ : Nat → V},
      (∀ k d, ds[k]? = some d → VExpr.bvarsBelow (as.length + k) d.2.2.erase) →
      (∀ bs, SpineFit (consList as ρ₁) (ds.map (·.2.2)) bs →
        g₁ (consList (as ++ bs) ρ₁) = g₂ (consList (as ++ bs) ρ₂)) →
      lamTower m (consList as ρ₁) ds g₁ = lamTower m (consList as ρ₂) ds g₂
  | [], as, ρ₁, ρ₂, _, hg => by
    show g₁ (consList as ρ₁) = g₂ (consList as ρ₂)
    have := hg [] trivial
    simpa using this
  | d :: ds, as, ρ₁, ρ₂, hcl, hg => by
    show lamR m (interp2 V (consList as ρ₁) d.2.2) (fun a => lamTower m (cons a (consList as ρ₁)) ds g₁)
      = lamR m (interp2 V (consList as ρ₂) d.2.2) (fun a => lamTower m (cons a (consList as ρ₂)) ds g₂)
    have hdom : interp2 V (consList as ρ₁) d.2.2 = interp2 V (consList as ρ₂) d.2.2 :=
      interp2_congr_noBVar d.2.2 (NoBVar_of_bvarsBelow (by simpa using hcl 0 d rfl) fun _ hi => hi)
        (agreeOff_consList_ge as ρ₁ ρ₂)
    rw [hdom]
    refine lamR_congr fun a ha => ?_
    rw [consList_snoc', consList_snoc']
    refine lamTower_congr_bottom (as := as ++ [a]) ?_ ?_
    · intro k d' hd'
      have := hcl (k + 1) d' (by simpa using hd')
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    · intro bs hbs
      have := hg (a :: bs) ⟨by show a ∈ˢ interp2 V (consList as ρ₁) d.2.2; rw [hdom]; exact ha,
        by rw [consList_snoc']; exact hbs⟩
      simpa [List.append_assoc] using this

/-! ## The K-frame's accessors -/

/-- The recursive positions among the first `k` fields. -/
def recIdx (rs : List Bool) (k : Nat) : List Nat :=
  (List.range k).filter fun i => rs.getD i false

theorem mem_recIdx {rs : List Bool} {k i : Nat} :
    i ∈ recIdx rs k ↔ i < k ∧ rs.getD i false = true := by
  unfold recIdx
  rw [List.mem_filter, List.mem_range]

/-- The unfolded function's value: the entry just below the parameters. -/
noncomputable def frR (nP n nIdx : Nat) (ρ₀ : Nat → V) : V := frP n nIdx ρ₀ nP

/-- The minors' values, in order. -/
noncomputable def frMsL (n nIdx : Nat) (ρ₀ : Nat → V) : List V := (List.range n).map (frMs n nIdx ρ₀)

theorem frMsL_getD (n nIdx : Nat) (ρ₀ : Nat → V) {j : Nat} (hj : j < n) :
    (frMsL n nIdx ρ₀).getD j pt = frMs n nIdx ρ₀ j := by
  unfold frMsL
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj, Option.map_some,
    Option.getD_some]

/-- The frame below the unfolded function. -/
noncomputable def frBelow (nP n nIdx : Nat) (ρ₀ : Nat → V) : Nat → V :=
  shiftE (nIdx + n + 1 + nP + 1) 0 ρ₀

/-- The K-frame's `(p⃗, M, m⃗)` part as a spine. -/
noncomputable def frKSpine (nP n nIdx : Nat) (ρ₀ : Nat → V) : List V :=
  frameIdx (nP + 1 + n) (shiftE nIdx 0 ρ₀)

omit [SetTheory V] in
/-- The frame below the function, consed with the function and the
`(p⃗, M, m⃗, ı⃗)` spine, is the K-frame. -/
theorem consList_frKSpine (nP n nIdx : Nat) (ρ₀ : Nat → V) :
    consList (frKSpine nP n nIdx ρ₀ ++ frameIdx nIdx ρ₀) (cons (frR nP n nIdx ρ₀) (frBelow nP n nIdx ρ₀))
      = ρ₀ := by
  have h1 : cons (frR nP n nIdx ρ₀) (frBelow nP n nIdx ρ₀) = shiftE (nIdx + n + 1 + nP) 0 ρ₀ := by
    funext i
    cases i with
    | zero =>
      show frP n nIdx ρ₀ nP = shiftE (nIdx + n + 1 + nP) 0 ρ₀ 0
      unfold frP
      rw [shiftE_zero, shiftE_zero]
      show ρ₀ (nP + (nIdx + n + 1)) = ρ₀ (0 + (nIdx + n + 1 + nP))
      congr 1; omega
    | succ i =>
      show frBelow nP n nIdx ρ₀ i = shiftE (nIdx + n + 1 + nP) 0 ρ₀ (i + 1)
      unfold frBelow
      rw [shiftE_zero, shiftE_zero]
      show ρ₀ (i + (nIdx + n + 1 + nP + 1)) = ρ₀ (i + 1 + (nIdx + n + 1 + nP))
      congr 1; omega
  have h2 : shiftE (nIdx + n + 1 + nP) 0 ρ₀ = shiftE (nP + 1 + n) 0 (shiftE nIdx 0 ρ₀) := by
    rw [← shiftE_add']; congr 1; omega
  rw [h1, h2, consList_append]
  unfold frKSpine
  rw [consList_frameIdx (nP + 1 + n) (shiftE nIdx 0 ρ₀)]
  exact consList_frameIdx nIdx ρ₀

/-! ## The inductive hypothesis arguments -/

/-- The ih argument for recursive field `i` at the payload frame (depth
`D + 1`): the unfolded function at the `(p⃗, M, m⃗)` block, the field's
index expressions (read at the payload's projections) and the field. -/
def ihArgAV (nP n nIdx D i : Nat) (Eis : List AVExpr) : AVExpr :=
  AVExpr.mkAppN (.bvar (D + 1 + nIdx + n + 1 + nP))
    (idxVarsAV (nP + 1 + n) (D + 1 + nIdx) ++
      Eis.map (fun E => substProj i (E.liftN (D + nIdx + n + 2) i)) ++ [projAV i (.bvar 0)])

/-- The ih arguments of constructor `j`. -/
def ihArgsI (nP n nIdx : Nat) (rss : List (List Bool)) (Eiss : List (List (List AVExpr)))
    (ar : Nat → Nat) (D j : Nat) : List AVExpr :=
  (recIdx (rss.getD j []) (ar j)).map fun i => ihArgAV nP n nIdx D i ((Eiss.getD j []).getD i [])

/-- The ih domains at a field spine: the motive at the field's index
values, at the field. -/
noncomputable def ihDomsI (ρp : Nat → V) (M : V) (rss : List (List Bool))
    (Eiss : List (List (List AVExpr))) (ar : Nat → Nat) (j : Nat) (fs : List V) : List V :=
  (recIdx (rss.getD j []) (ar j)).map fun i =>
    SetTheory.app ((((Eiss.getD j []).getD i []).map (interp2 V (consList (fs.take i) ρp))).foldl
      SetTheory.app M) (fs.getD i pt)

/-- The ih values at a payload: the function at the spine. -/
noncomputable def ihValsI (ρp : Nat → V) (rV : V) (kspine : List V) (rss : List (List Bool))
    (Eiss : List (List (List AVExpr))) (ar : Nat → Nat) (j : Nat) (y : V) : List V :=
  (recIdx (rss.getD j []) (ar j)).map fun i =>
    (kspine ++ (((Eiss.getD j []).getD i []).map (interp2 V (consList (projList i y) ρp)))
      ++ [projS i y]).foldl SetTheory.app rV

section IhFacts

variable {ℓ w u nP : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
  {rss : List (List Bool)} {Eiss : List (List (List AVExpr))} {D : Nat}

/-- The `(p⃗, M, m⃗)` block's variables read to the K-frame's spine. -/
theorem kSpineAt_interp (hfr : RecFrameS D ρ₀ σ) (y : V) :
    (idxVarsAV (nP + 1 + Fss.length) (D + 1 + Ids.length)).map (interp2 V (cons y σ))
      = frKSpine nP Fss.length Ids.length ρ₀ := by
  have hfr' : RecFrameS (D + 1 + Ids.length) (shiftE Ids.length 0 ρ₀) (cons y σ) := by
    unfold RecFrameS
    rw [shiftE_add', shiftE_succ_cons, hfr]
  exact map_idxVarsAV_interp hfr'

theorem rAt_interp (hfr : RecFrameS D ρ₀ σ) (y : V) :
    interp2 V (cons y σ) (.bvar (D + 1 + Ids.length + Fss.length + 1 + nP))
      = frR nP Fss.length Ids.length ρ₀ := by
  rw [interp2_bvar, show D + 1 + Ids.length + Fss.length + 1 + nP
      = (D + 1) + (Ids.length + Fss.length + 1 + nP) from by omega, (hfr.push y).apply]
  unfold frR frP
  rw [shiftE_zero]
  show ρ₀ _ = ρ₀ _
  congr 1
  omega

theorem MAt_interp (hfr : RecFrameS D ρ₀ σ) (y : V) :
    interp2 V (cons y σ) (.bvar (D + 1 + Ids.length + Fss.length)) = frM Fss.length Ids.length ρ₀ := by
  rw [interp2_bvar]; exact (hfr.push y).motive

omit [SetTheory V] in
/-- The payload frame's shift by the K-frame's depth over the
parameter frame. -/
theorem shiftE_payload (hfr : RecFrameS D ρ₀ σ) (y : V) :
    shiftE (D + Ids.length + Fss.length + 2) 0 (cons y σ) = frP Fss.length Ids.length ρ₀ := by
  rw [show D + Ids.length + Fss.length + 2 = (D + 1) + (Ids.length + Fss.length + 1) from by omega,
    shiftE_add', shiftE_succ_cons, hfr]
  rfl

/-- An index expression of field `i`, read at the payload's
projections. -/
theorem ihIdx_interp (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (E : AVExpr) :
    interp2 V (cons y σ) (substProj i (E.liftN (D + Ids.length + Fss.length + 2) i))
      = interp2 V (consList (projList i y) (frP Fss.length Ids.length ρ₀)) E := by
  have h := shiftE_consList_len (D + Ids.length + Fss.length + 2) (projList i y) (cons y σ)
  rw [projList_length] at h
  rw [interp2_substProj, interp2_liftN, h, shiftE_payload hfr]

theorem ihIdx_ok2 (hfr : RecFrameS D ρ₀ σ) (y : V) (i : Nat) (E : AVExpr)
    (hp : ∀ m, m < i → AnnotOk2 V (consList (projList m y) (cons y σ)) (projAV m (.bvar m)))
    (hE : AnnotOk2 V (consList (projList i y) (frP Fss.length Ids.length ρ₀)) E) :
    AnnotOk2 V (cons y σ) (substProj i (E.liftN (D + Ids.length + Fss.length + 2) i)) := by
  have h := shiftE_consList_len (D + Ids.length + Fss.length + 2) (projList i y) (cons y σ)
  rw [projList_length] at h
  rw [AnnotOk2_substProj σ y i _ hp, AnnotOk2_liftN, h, shiftE_payload hfr]
  exact hE

end IhFacts

/-! ## The K-frame package and the ih obligation -/

/-- The real-chain relation, walked down to a recursive position along a
fitting field spine: the index expressions there are graded and fit,
and the real domain reads to the carrier at their tuple. -/
theorem chainRealI_at {u : Nat} {ρp : Nat → V} {Ids : List AVExpr} {μ : V} {rs : List Bool}
    {Eis : List (List AVExpr)} :
    ∀ (Fs₀ Fs : List AVExpr) (i₀ : Nat) (as fs : List V), as.length = i₀ →
      ChainRealI μ u ρp Ids rs Eis i₀ as Fs₀ Fs → SpineFit (consList as ρp) Fs fs →
      ∀ l, l < Fs.length → rs.getD (i₀ + l) false = true →
        (∀ E ∈ Eis.getD (i₀ + l) [], AnnotOk2 V (consList (as ++ fs.take l) ρp) E) ∧
        SpineFit ρp Ids ((Eis.getD (i₀ + l) []).map (interp2 V (consList (as ++ fs.take l) ρp))) ∧
        interp2 V (consList (as ++ fs.take l) ρp) (Fs.getD l default)
          = SetTheory.app μ (tupW u ((Eis.getD (i₀ + l) []).map (interp2 V (consList (as ++ fs.take l) ρp))))
  | [], [], _, _, _, _, _, _, _, hl, _ => absurd hl (Nat.not_lt_zero _)
  | [], _ :: _, _, _, _, _, hc, _, _, _, _ => hc.elim
  | _ :: _, [], _, _, _, _, hc, _, _, _, _ => hc.elim
  | _ :: _, _ :: _, _, _, [], _, _, hsp, _, _, _ => hsp.elim
  | F₀ :: Fs₀, F :: Fs, i₀, as, f :: fs, hi, hc, hsp, l, hl, hr => by
    subst hi
    obtain ⟨hhead, htail⟩ := hc
    cases l with
    | zero =>
      rw [Nat.add_zero] at hr ⊢
      rw [if_pos hr] at hhead
      simpa using hhead
    | succ l =>
      have ih := chainRealI_at Fs₀ Fs (as.length + 1) (as ++ [f]) fs (length_snoc' f as)
        (htail f hsp.1) (by rw [← consList_snoc']; exact hsp.2) l (by simpa using hl)
        (by rw [show as.length + 1 + l = as.length + (l + 1) from by omega]; exact hr)
      rw [show as.length + 1 + l = as.length + (l + 1) from by omega] at ih
      simpa [List.append_assoc] using ih

/-- The recursor's conclusion `M ı⃗ t`, read at a walk frame. -/
theorem recConcAV_at {n nIdx : Nat} {ρ₁ : Nat → V} (vals : List V) (hlen : vals.length = nIdx) (f : V) :
    interp2 V (cons f (consList vals ρ₁)) (recConcAV n nIdx)
      = SetTheory.app (vals.foldl SetTheory.app (ρ₁ n)) f := by
  have hfr : RecFrameS 1 (consList vals ρ₁) (cons f (consList vals ρ₁)) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  unfold recConcAV motAppAV
  rw [interp2_app, interp2_mkAppN, ← List.foldl_map (f := interp2 V (cons f (consList vals ρ₁)))
    (g := SetTheory.app), map_idxVarsAV_interp hfr, interp2_bvar, interp2_bvar, cons_zero]
  have hM : cons f (consList vals ρ₁) (1 + nIdx + n) = ρ₁ n := by
    rw [show 1 + nIdx + n = (n + vals.length) + 1 from by omega, cons_succ, consList_apply_add]
  have hI : frameIdx nIdx (consList vals ρ₁) = vals := by
    rw [← hlen]; exact frameIdx_consList' vals ρ₁
  rw [hM, hI]

/-- **The K-frame package of the recursive family's recursor**: the
case split's hypotheses (with the family as `famAt` and the ih
domains at the motive), the family's functor facts at the parameter
frame, the identification of the real chains, and the unfolded
function's typing at the recursor's type (a closed Π-tower over the
binder data `rds`, read at the frame below the function) with the
spine-fit of the ih application. -/
structure FixKI₀ (ℓ w u : Nat) (ρ₀ : Nat → V) (Fss Ess Fss₀ : List (List AVExpr))
    (Ids : List AVExpr) (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) : Prop where
  hyp : RecHypI ℓ w ρ₀ Fss Ess Ids
    (fun is => SetTheory.app
      (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss Eiss Fss₀ Ess) (tupW u is))
    (ihDomsI (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) rss Eiss
      (fun j => (Fss.getD j []).length))
  hX : XChainsOk u w (frP Fss.length Ids.length ρ₀) Ids rss Eiss Fss₀ Ess
  hreal : ChainsRealI (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss Eiss Fss₀ Ess)
    u (frP Fss.length Ids.length ρ₀) Ids rss Eiss Fss₀ Fss Ess

/-- `FixKI₀` plus the unfolded function's typing at the recursor's type
(a closed Π-tower over the binder data `rds`, read at the frame below
the function) with the spine-fit of the ih application and the
conclusion's zero-level condition. -/
structure FixKI (ℓ w u nP : Nat) (ρ₀ : Nat → V) (Fss Ess Fss₀ : List (List AVExpr))
    (Ids : List AVExpr) (rss : List (List Bool)) (Eiss : List (List (List AVExpr)))
    (rds : List (Nat × Nat × AVExpr)) : Prop
    extends FixKI₀ ℓ w u ρ₀ Fss Ess Fss₀ Ids rss Eiss where
  hz : ∀ d ∈ rds, (ℓ = 0 ↔ d.2.1 = 0)
  hrV : frR nP Fss.length Ids.length ρ₀
    ∈ˢ interp2 V (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))
      (mkPisAV rds (recConcAV Fss.length Ids.length))
  hspine : ∀ (vals : List V) (f : V), SpineFit (frP Fss.length Ids.length ρ₀) Ids vals →
    f ∈ˢ SetTheory.app
      (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss Eiss Fss₀ Ess) (tupW u vals) →
    SpineFit (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))
      (rds.map (·.2.2)) (frKSpine nP Fss.length Ids.length ρ₀ ++ vals ++ [f])
  hspineLen : rds.length = nP + 1 + Fss.length + Ids.length + 1
  hconc0 : ℓ = 0 → ∀ as', SpineFit (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))
    (rds.map (·.2.2)) as' →
    interp2 V (consList as' (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀)))
      (recConcAV Fss.length Ids.length) ∈ˢ (univZero : V)

namespace FixKI

variable {ℓ w u nP : Nat} {ρ₀ : Nat → V} {Fss Ess Fss₀ : List (List AVExpr)} {Ids : List AVExpr}
  {rss : List (List Bool)} {Eiss : List (List (List AVExpr))} {rds : List (Nat × Nat × AVExpr)}

/-- The block frame `(p⃗, M, m⃗)` over the function is the K-frame's
shift past the indices. -/
theorem block_frame (_h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss Eiss rds) :
    consList (frKSpine nP Fss.length Ids.length ρ₀)
        (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))
      = shiftE Ids.length 0 ρ₀ := by
  have hk := consList_frKSpine nP Fss.length Ids.length ρ₀
  rw [consList_append] at hk
  have h := shiftE_consList (frameIdx Ids.length ρ₀)
    (consList (frKSpine nP Fss.length Ids.length ρ₀)
      (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀)))
  rw [frameIdx_length, hk] at h
  exact h.symm

/-- The conclusion at a spine frame is the motive at the index values
at the major. -/
theorem conc_at (h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss Eiss rds) {vals : List V}
    (hlen : vals.length = Ids.length) (f : V) :
    interp2 V (consList (frKSpine nP Fss.length Ids.length ρ₀ ++ vals ++ [f])
        (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀)))
        (recConcAV Fss.length Ids.length)
      = SetTheory.app (vals.foldl SetTheory.app (frM Fss.length Ids.length ρ₀)) f := by
  rw [consList_append, consList_append]
  have := recConcAV_at (n := Fss.length) (nIdx := Ids.length)
    (ρ₁ := consList (frKSpine nP Fss.length Ids.length ρ₀)
      (cons (frR nP Fss.length Ids.length ρ₀) (frBelow nP Fss.length Ids.length ρ₀))) vals hlen f
  show interp2 V (cons f _) _ = _
  rw [this, h.block_frame, shiftE_zero]
  unfold frM
  show SetTheory.app (vals.foldl SetTheory.app (ρ₀ (Fss.length + Ids.length))) f = _
  rw [Nat.add_comm]

/-- The membership of the function's application at a fitting spine
in the conclusion. -/
theorem app_mem (h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss Eiss rds) {vals : List V}
    (hsp : SpineFit (frP Fss.length Ids.length ρ₀) Ids vals) {f : V}
    (hf : f ∈ˢ SetTheory.app
      (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss Eiss Fss₀ Ess) (tupW u vals)) :
    (frKSpine nP Fss.length Ids.length ρ₀ ++ vals ++ [f]).foldl SetTheory.app
        (frR nP Fss.length Ids.length ρ₀)
      ∈ˢ SetTheory.app (vals.foldl SetTheory.app (frM Fss.length Ids.length ρ₀)) f := by
  have := mkPisAV_fold_mem h.hz h.hconc0 h.hrV (h.hspine vals f hsp hf)
  rwa [h.conc_at hsp.length_eq f] at this

/-- The application chain of the function at a fitting spine is
graded. -/
theorem app_chain (h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss Eiss rds) {vals : List V}
    (hsp : SpineFit (frP Fss.length Ids.length ρ₀) Ids vals) {f : V}
    (hf : f ∈ˢ SetTheory.app
      (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss Eiss Fss₀ Ess) (tupW u vals)) :
    AppChainOk (frR nP Fss.length Ids.length ρ₀) (frKSpine nP Fss.length Ids.length ρ₀ ++ vals ++ [f]) :=
  appChainOk_of_mkPisAV' h.hz h.hconc0 h.hrV (h.hspine vals f hsp hf)

/-- The `l`-th value of a fitting spine is in the `l`-th domain at the
prefix. -/
theorem spineFit_getD_mem' {ρ : Nat → V} :
    ∀ {Fs : List AVExpr} {as : List V} {l : Nat}, SpineFit ρ Fs as → l < Fs.length →
      as.getD l pt ∈ˢ interp2 V (consList (as.take l) ρ) (Fs.getD l default)
  | [], _, _, _, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, [], _, h, _ => h.elim
  | F :: Fs, a :: as, 0, h, _ => by simpa using h.1
  | F :: Fs, a :: as, l + 1, h, hl => by
    simp only [List.getD_cons_succ, List.take_succ_cons, consList_cons]
    exact spineFit_getD_mem' (Fs := Fs) (as := as) (l := l) h.2 (by simpa using hl)

/-- **The ih obligation is discharged** at every frame of the case
split (graph regime). -/
theorem ihArgsOk_of (h : FixKI ℓ w u nP ρ₀ Fss Ess Fss₀ Ids rss Eiss rds) (hw : w ≠ 0)
    {D : Nat} {σ : Nat → V} (hfr : RecFrameS D ρ₀ σ) {j : Nat} (hj : j < Fss.length) :
    IhArgsOk w ρ₀ σ Fss Ess Ids
      (ihDomsI (frP Fss.length Ids.length ρ₀) (frM Fss.length Ids.length ρ₀) rss Eiss
        (fun j => (Fss.getD j []).length))
      (ihValsI (frP Fss.length Ids.length ρ₀) (frR nP Fss.length Ids.length ρ₀)
        (frKSpine nP Fss.length Ids.length ρ₀) rss Eiss (fun j => (Fss.getD j []).length))
      (ihArgsI nP Fss.length Ids.length rss Eiss (fun j => (Fss.getD j []).length)) D j := by
  intro y hy
  have hjF := h.hyp.rChain_getElem? hj
  rw [sumFibre_of_getElem? hjF] at hy
  have hokF : FieldsOkB w ρ₀
      (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])) :=
    h.hyp.hok _ (List.mem_of_getElem? hjF)
  have hbnd := hokF.toBound hw
  have hlenR : (rChain (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []) (Ess.getD j [])).length
      = (Fss.getD j []).length + 1 := rChain_length _ _ _ _
  -- the payload's projections fit the real chain at the parameter frame
  have helim := restricted_member_elim hw
    (Fs := liftFields (Ids.length + Fss.length + 1) 0 (Fss.getD j []))
    (eqs := idxEqsAt (Ids.length + Fss.length + 1) Ids.length (Fss.getD j []).length (Ess.getD j []))
    (ρ := ρ₀) (y := y) hy
  rw [liftFields_length] at helim
  obtain ⟨hspL, -, -, -⟩ := helim
  have hspP : SpineFit (frP Fss.length Ids.length ρ₀) (Fss.getD j [])
      (projList (Fss.getD j []).length y) :=
    (spineFit_liftFields (Ids.length + Fss.length + 1)).mp hspL
  -- the projections are graded at their frames
  have hproj : ∀ m, m < (Fss.getD j []).length →
      ∀ (σ' : Nat → V) (k : Nat), interp2 V σ' (.bvar k) = y → AnnotOk2 V σ' (projAV m (.bvar k)) := by
    intro m hm σ' k hσ'
    refine projAV_ok2_tower (w := w) (ρ := ρ₀) (by simp) ?_ hbnd (by omega)
    rw [hσ']; exact hy
  have hp : ∀ i, i ≤ (Fss.getD j []).length → ∀ m, m < i →
      AnnotOk2 V (consList (projList m y) (cons y σ)) (projAV m (.bvar m)) := by
    intro i hi m hm
    refine hproj m (by omega) _ m ?_
    rw [interp2_bvar]
    have := consList_apply_add (projList m y) (cons y σ) 0
    rwa [Nat.zero_add, projList_length] at this
  have hp0 : ∀ i, i < (Fss.getD j []).length → AnnotOk2 V (cons y σ) (projAV i (.bvar 0)) := by
    intro i hi
    exact hproj i hi _ 0 (by rw [interp2_bvar]; rfl)
  -- per recursive position
  have hpos : ∀ l, ∀ hl : l < (recIdx (rss.getD j []) (Fss.getD j []).length).length,
      let i := (recIdx (rss.getD j []) (Fss.getD j []).length)[l]'hl
      let vals := ((Eiss.getD j []).getD i []).map
        (interp2 V (consList (projList i y) (frP Fss.length Ids.length ρ₀)))
      i < (Fss.getD j []).length ∧
      (∀ E ∈ (Eiss.getD j []).getD i [],
        AnnotOk2 V (consList (projList i y) (frP Fss.length Ids.length ρ₀)) E) ∧
      SpineFit (frP Fss.length Ids.length ρ₀) Ids vals ∧
      projS i y ∈ˢ SetTheory.app
        (fixFamI u w (frP Fss.length Ids.length ρ₀) Ids Ids.length rss Eiss Fss₀ Ess) (tupW u vals) := by
    intro l hl
    have hmem : (recIdx (rss.getD j []) (Fss.getD j []).length)[l]
        ∈ recIdx (rss.getD j []) (Fss.getD j []).length := List.getElem_mem hl
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hmem
    have hc := chainRealI_at (Fss₀.getD j []) (Fss.getD j []) 0 [] (projList (Fss.getD j []).length y)
      rfl (h.hreal.2.2.2.2 j hj) (by simpa using hspP) _ hik (by rw [Nat.zero_add]; exact hri)
    rw [Nat.zero_add, List.nil_append, projList_take _ _ _ (Nat.le_of_lt hik)] at hc
    obtain ⟨hEok, hvsp, heq⟩ := hc
    refine ⟨hik, hEok, hvsp, ?_⟩
    have := spineFit_getD_mem' hspP hik
    rw [projList_take _ _ _ (Nat.le_of_lt hik), heq] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [projList_length]; exact hik),
      Option.getD_some, projList_get _ _ _ hik] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · -- the readings
    unfold ihArgsI ihValsI
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    obtain ⟨hik, -⟩ := mem_recIdx.mp hi
    show interp2 V (cons y σ) (ihArgAV nP Fss.length Ids.length D i _) = _
    unfold ihArgAV
    have hmid : ((Eiss.getD j []).getD i []).map
        (interp2 V (cons y σ) ∘ fun E => substProj i (E.liftN (D + Ids.length + Fss.length + 2) i))
        = ((Eiss.getD j []).getD i []).map
          (interp2 V (consList (projList i y) (frP Fss.length Ids.length ρ₀))) :=
      List.map_congr_left fun E _ => ihIdx_interp hfr y i E
    rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V (cons y σ)) (g := SetTheory.app),
      rAt_interp hfr, List.map_append, List.map_append, kSpineAt_interp hfr, List.map_map, hmid]
    simp only [List.map_cons, List.map_nil, projAV_interp, interp2_bvar, cons_zero]
  · -- the lengths
    unfold ihArgsI ihDomsI
    simp only [List.length_map]
  · -- the gradings and the memberships
    intro l hl
    unfold ihDomsI at hl ⊢
    rw [List.length_map] at hl
    obtain ⟨hik, hEok, hvsp, hfmem⟩ := hpos l hl
    have hgetA : (ihArgsI nP Fss.length Ids.length rss Eiss (fun j => (Fss.getD j []).length) D j).getD l default
        = ihArgAV nP Fss.length Ids.length D ((recIdx (rss.getD j []) (Fss.getD j []).length)[l])
            ((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []) := by
      unfold ihArgsI
      rw [List.getD_eq_getElem?_getD (i := l), List.getElem?_map, List.getElem?_eq_getElem hl,
        Option.map_some, Option.getD_some]
    have hgetD : (((recIdx (rss.getD j []) (Fss.getD j []).length)).map fun i =>
        SetTheory.app ((((Eiss.getD j []).getD i []).map (interp2 V (consList ((projList (Fss.getD j []).length y).take i)
          (frP Fss.length Ids.length ρ₀)))).foldl SetTheory.app (frM Fss.length Ids.length ρ₀))
          ((projList (Fss.getD j []).length y).getD i pt)).getD l pt
        = SetTheory.app ((((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []).map
            (interp2 V (consList (projList ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) y)
              (frP Fss.length Ids.length ρ₀)))).foldl SetTheory.app (frM Fss.length Ids.length ρ₀))
            (projS ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) y) := by
      rw [List.getD_eq_getElem?_getD (i := l), List.getElem?_map, List.getElem?_eq_getElem hl,
        Option.map_some, Option.getD_some, projList_take _ _ _ (Nat.le_of_lt hik),
        List.getD_eq_getElem?_getD (l := projList (Fss.getD j []).length y),
        List.getElem?_eq_getElem (by rw [projList_length]; exact hik), Option.getD_some,
        projList_get _ _ _ hik]
    rw [hgetA, hgetD]
    -- the argument's value
    have hval : interp2 V (cons y σ) (ihArgAV nP Fss.length Ids.length D
        ((recIdx (rss.getD j []) (Fss.getD j []).length)[l])
        ((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []))
        = (frKSpine nP Fss.length Ids.length ρ₀ ++
            (((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []).map
              (interp2 V (consList (projList ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) y)
                (frP Fss.length Ids.length ρ₀)))) ++
            [projS ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) y]).foldl SetTheory.app
            (frR nP Fss.length Ids.length ρ₀) := by
      unfold ihArgAV
      have hmid : ((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []).map
          (interp2 V (cons y σ) ∘ fun E => substProj ((recIdx (rss.getD j []) (Fss.getD j []).length)[l])
            (E.liftN (D + Ids.length + Fss.length + 2) ((recIdx (rss.getD j []) (Fss.getD j []).length)[l])))
          = ((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []).map
            (interp2 V (consList (projList ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) y)
              (frP Fss.length Ids.length ρ₀))) :=
        List.map_congr_left fun E _ => ihIdx_interp hfr y _ E
      rw [interp2_mkAppN, ← List.foldl_map (f := interp2 V (cons y σ)) (g := SetTheory.app),
        rAt_interp hfr, List.map_append, List.map_append, kSpineAt_interp hfr, List.map_map, hmid]
      simp only [List.map_cons, List.map_nil, projAV_interp, interp2_bvar, cons_zero]
    refine ⟨?_, ?_⟩
    · -- graded: the application chain of the function at the spine
      unfold ihArgAV
      have hargs : ∀ a ∈ idxVarsAV (nP + 1 + Fss.length) (D + 1 + Ids.length) ++
          ((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []).map
            (fun E => substProj ((recIdx (rss.getD j []) (Fss.getD j []).length)[l])
              (E.liftN (D + Ids.length + Fss.length + 2) ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]))) ++
          [projAV ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) (.bvar 0)],
          AnnotOk2 V (cons y σ) a := by
        intro a ha
        simp only [List.mem_append, List.mem_map, List.mem_singleton] at ha
        rcases ha with (ha | ⟨E, hE, rfl⟩) | rfl
        · obtain ⟨_, -, rfl⟩ := List.mem_map.mp ha
          simp
        · exact ihIdx_ok2 hfr y _ E (hp _ (Nat.le_of_lt hik)) (hEok E hE)
        · exact hp0 _ hik
      have hchain : AppChainOk (interp2 V (cons y σ) (.bvar (D + 1 + Ids.length + Fss.length + 1 + nP)))
          ((idxVarsAV (nP + 1 + Fss.length) (D + 1 + Ids.length) ++
            ((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []).map
              (fun E => substProj ((recIdx (rss.getD j []) (Fss.getD j []).length)[l])
                (E.liftN (D + Ids.length + Fss.length + 2) ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]))) ++
            [projAV ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) (.bvar 0)]).map
              (interp2 V (cons y σ))) := by
        rw [rAt_interp hfr, List.map_append, List.map_append, kSpineAt_interp hfr, List.map_map]
        have hm : (((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []).map
            (interp2 V (cons y σ) ∘ fun E => substProj ((recIdx (rss.getD j []) (Fss.getD j []).length)[l])
              (E.liftN (D + Ids.length + Fss.length + 2) ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]))))
            = ((Eiss.getD j []).getD ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) []).map
              (interp2 V (consList (projList ((recIdx (rss.getD j []) (Fss.getD j []).length)[l]) y)
                (frP Fss.length Ids.length ρ₀))) := by
          apply List.map_congr_left
          intro E _
          exact ihIdx_interp hfr y _ E
        rw [hm]
        simp only [List.map_cons, List.map_nil, projAV_interp, interp2_bvar, cons_zero]
        exact h.app_chain hvsp hfmem
      exact (mkAppN_ok2_of_chain (by simp) hargs hchain).1
    · rw [hval]
      exact h.app_mem hvsp hfmem

end FixKI

/-! ## The rank recursion -/

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
/-- The stage of a member of a fibrewise iterate at a tuple (junk off
it). -/
noncomputable def rkFam (Φ : Nat → V) (tup t : V) : Nat :=
  if h : ∃ n, t ∈ˢ SetTheory.app (Φ n) tup then Classical.choose h else 0

theorem mem_rkFam {Φ : Nat → V} {tup t : V} (h : ∃ n, t ∈ˢ SetTheory.app (Φ n) tup) :
    t ∈ˢ SetTheory.app (Φ (rkFam Φ tup t)) tup := by
  unfold rkFam
  rw [dif_pos h]
  exact Classical.choose_spec h

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

section KRec

variable {ℓ w u : Nat} {K : Nat → V} {Fss Ess Fss₀ : List (List AVExpr)} {Ids : List AVExpr}
  {rss : List (List Bool)} {Eiss : List (List (List AVExpr))}

/-- The recursion's data at a K-frame. -/
noncomputable def fixSemK (K : Nat → V) (Fss : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) : Nat → V → V :=
  fixSem (fun j => (frMsL Fss.length Ids.length K).getD j pt)
    (fun j => recIdx (rss.getD j []) (Fss.getD j []).length) (fun j => (Fss.getD j []).length)

/-- The fibrewise iterates at a K-frame. -/
noncomputable def iterK (u w : Nat) (K : Nat → V) (Fss Ess Fss₀ : List (List AVExpr))
    (Ids : List AVExpr) (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) : Nat → V :=
  famIter u w (frP Fss.length Ids.length K) Ids rss Eiss Fss₀ Ess

/-- The family at a K-frame. -/
noncomputable def famK (u w : Nat) (K : Nat → V) (Fss Ess Fss₀ : List (List AVExpr))
    (Ids : List AVExpr) (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) : V :=
  fixFamI u w (frP Fss.length Ids.length K) Ids Ids.length rss Eiss Fss₀ Ess

theorem iterK_le_fam (h : FixKI₀ ℓ w u K Fss Ess Fss₀ Ids rss Eiss) (n : Nat) :
    FamLe (idxSet u (frP Fss.length Ids.length K) Ids) (iterK u w K Fss Ess Fss₀ Ids rss Eiss n)
      (famK u w K Fss Ess Fss₀ Ids rss Eiss) := by
  intro i hi
  unfold famK
  rw [fixFamI_app_eq_famU h.hX hi]
  exact famIter_le_famU h.hX n i hi

/-- A member of a stage at a tuple: the decomposition and the facts
the recursion consumes. -/
theorem stage_elim (h : FixKI₀ ℓ w u K Fss Ess Fss₀ Ids rss Eiss) (hw : w ≠ 0) {n : Nat}
    {is : List V} (hsp : SpineFit (frP Fss.length Ids.length K) Ids is) {t : V}
    (ht : t ∈ˢ SetTheory.app (iterK u w K Fss Ess Fss₀ Ids rss Eiss (n + 1)) (tupW u is)) :
    ∃ j fs, t = inj j (mkTower (fs ++ [pt])) ∧ j < Fss.length ∧
      fs.length = (Fss.getD j []).length ∧
      SpineFit (frP Fss.length Ids.length K) (Fss.getD j []) fs ∧
      idxValsAt (frP Fss.length Ids.length K) (Ess.getD j []) fs = is ∧
      (∀ l, l < fs.length → (rss.getD j []).getD l false = true →
        fs.getD l pt ∈ˢ SetTheory.app (iterK u w K Fss Ess Fss₀ Ids rss Eiss n)
          (tupW u ((((Eiss.getD j []).getD l []).map
            (interp2 V (consList (fs.take l) (frP Fss.length Ids.length K)))))) ∧
        SpineFit (frP Fss.length Ids.length K) Ids
          (((Eiss.getD j []).getD l []).map
            (interp2 V (consList (fs.take l) (frP Fss.length Ids.length K))))) := by
  have ht' : t ∈ˢ fixStepI u w (frP Fss.length Ids.length K) Ids Ids.length rss Eiss Fss₀ Ess
      (iterK u w K Fss Ess Fss₀ Ids rss Eiss n) (tupW u is) := by
    unfold iterK famIter at ht
    rwa [famFI_app (tupW_mem hsp)] at ht
  obtain ⟨j, fs, rfl, hj₀, hlen₀, hspX, hall⟩ := fixStepI_elim hw ht'
  obtain ⟨hl₀, hlE, hEs, hlenj, hc⟩ := h.hreal
  have hj : j < Fss.length := by omega
  have hfit := h.hX.hfit _ (famIter_mem h.hX n) _ (tupW_mem hsp) j hj₀
  have hspR := spineFit_real_of_XI h.hX.hI (iterK_le_fam h n) (Fss₀.getD j []) (Fss.getD j []) 0 [] fs rfl
    (hc j hj) hfit hspX
  have hlen : fs.length = (Fss.getD j []).length := by rw [hlen₀]; exact hlenj j hj
  refine ⟨j, fs, rfl, hj, hlen, hspR, ?_, ?_⟩
  · rw [← hlen₀] at hall
    exact idxValsAt_of_eqsXI h.hX.hI hsp (hEs j hj) hall
  · intro l hl hrl
    have hmem := fitsXI_rec_mem h.hX.hI (Fss₀.getD j []) 0 [] fs rfl hfit hspX l hl
      (by rw [Nat.zero_add]; exact hrl)
    rw [Nat.zero_add, List.nil_append] at hmem
    have hat := chainRealI_at (Fss₀.getD j []) (Fss.getD j []) 0 [] fs rfl (hc j hj) (by simpa using hspR) l
      (by omega) (by rw [Nat.zero_add]; exact hrl)
    rw [Nat.zero_add, List.nil_append] at hat
    exact ⟨hmem, hat.2.1⟩

/-- **The rank recursion lands in the motive** (nonzero elimination
level, graph regime). -/
theorem fixSemK_mem (h : FixKI₀ ℓ w u K Fss Ess Fss₀ Ids rss Eiss) (hw : w ≠ 0) (hℓ : ℓ ≠ 0) :
    ∀ (n : Nat) (is : List V) (t : V), SpineFit (frP Fss.length Ids.length K) Ids is →
      t ∈ˢ SetTheory.app (iterK u w K Fss Ess Fss₀ Ids rss Eiss n) (tupW u is) →
      fixSemK K Fss Ids rss n t ∈ˢ SetTheory.app (is.foldl SetTheory.app (frM Fss.length Ids.length K)) t
  | 0, is, _, hsp, ht => by
    unfold iterK famIter at ht
    rw [app_graph (tupW_mem hsp)] at ht
    exact absurd ht (not_mem_empty _)
  | n + 1, is, t, hsp, ht => by
    obtain ⟨j, fs, rfl, hj, hlen, hspR, hidx, hrec⟩ := stage_elim h hw hsp ht
    unfold fixSemK
    rw [fixSem_inj n j hlen]
    unfold stepBr
    rw [List.foldl_append]
    simp only [frMsL_getD Fss.length Ids.length K hj]
    have hfold := minorSpI_fold (fun h0 => absurd h0 hℓ) (h.hyp.hms j hj) hspR
    rw [List.nil_append] at hfold
    have hC0 : ℓ = 0 → concI w (frP Fss.length Ids.length K) (frM Fss.length Ids.length K) (Ess.getD j []) j fs
        ∈ˢ (univZero : V) := fun h0 => absurd h0 hℓ
    have := ihSpL_fold hC0 (As := ihDomsI (frP Fss.length Ids.length K) (frM Fss.length Ids.length K) rss Eiss
        (fun j => (Fss.getD j []).length) j fs)
      (vs := (recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
        fixSemK K Fss Ids rss n (fs.getD i pt)) hfold (by simp [ihDomsI]) ?_
    · unfold concI ctorValI at this
      rw [hidx, if_neg hw] at this
      exact this
    · intro l hl
      unfold ihDomsI at hl
      rw [List.length_map] at hl
      have hi : (recIdx (rss.getD j []) (Fss.getD j []).length)[l]
          ∈ recIdx (rss.getD j []) (Fss.getD j []).length := List.getElem_mem hl
      obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
      unfold ihDomsI
      rw [List.getD_eq_getElem?_getD (i := l), List.getElem?_map, List.getElem?_eq_getElem hl,
        Option.map_some, Option.getD_some, List.getD_eq_getElem?_getD (i := l), List.getElem?_map,
        List.getElem?_eq_getElem hl, Option.map_some, Option.getD_some]
      obtain ⟨hmem, hvsp⟩ := hrec _ (by omega) hri
      exact fixSemK_mem h hw hℓ n _ _ hvsp hmem

/-- **Stability**: above a member's stage the recursion is constant. -/
theorem fixSemK_stable (h : FixKI₀ ℓ w u K Fss Ess Fss₀ Ids rss Eiss) (hw : w ≠ 0) :
    ∀ (n : Nat) (is : List V) (t : V), SpineFit (frP Fss.length Ids.length K) Ids is →
      t ∈ˢ SetTheory.app (iterK u w K Fss Ess Fss₀ Ids rss Eiss n) (tupW u is) →
      ∀ m, n ≤ m → fixSemK K Fss Ids rss m t = fixSemK K Fss Ids rss n t
  | 0, is, _, hsp, ht, _, _ => by
    unfold iterK famIter at ht
    rw [app_graph (tupW_mem hsp)] at ht
    exact absurd ht (not_mem_empty _)
  | n + 1, is, t, hsp, ht, m, hnm => by
    obtain ⟨j, fs, rfl, hj, hlen, -, -, hrec⟩ := stage_elim h hw hsp ht
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    unfold fixSemK
    rw [fixSem_inj n j hlen, fixSem_inj m' j hlen]
    refine stepBr_congr fun i hi => ?_
    obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
    obtain ⟨hmem, hvsp⟩ := hrec i (by rw [hlen]; simpa using hik) hri
    exact fixSemK_stable h hw n _ _ hvsp hmem m' (by omega)

/-- **Inhabitation at a zero elimination level** (graph regime): the
motive is inhabited at every member of every stage. -/
theorem fixSemK_inhab (h : FixKI₀ ℓ w u K Fss Ess Fss₀ Ids rss Eiss) (hw : w ≠ 0) (h0 : ℓ = 0) :
    ∀ (n : Nat) (is : List V) (t : V), SpineFit (frP Fss.length Ids.length K) Ids is →
      t ∈ˢ SetTheory.app (iterK u w K Fss Ess Fss₀ Ids rss Eiss n) (tupW u is) →
      ∃ y, y ∈ˢ SetTheory.app (is.foldl SetTheory.app (frM Fss.length Ids.length K)) t
  | 0, is, _, hsp, ht => by
    unfold iterK famIter at ht
    rw [app_graph (tupW_mem hsp)] at ht
    exact absurd ht (not_mem_empty _)
  | n + 1, is, t, hsp, ht => by
    obtain ⟨j, fs, rfl, hj, hlen, hspR, hidx, hrec⟩ := stage_elim h hw hsp ht
    have hms := h.hyp.hms j hj
    rw [h0] at hms
    obtain ⟨x, hx⟩ := minorSpI_zero_inhab hms hspR
    rw [List.nil_append] at hx
    have := ihSpL_zero_inhab hx ?_
    · unfold concI ctorValI at this
      rwa [hidx, if_neg hw] at this
    · intro A hA
      unfold ihDomsI at hA
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
      obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
      obtain ⟨hmem, hvsp⟩ := hrec i (by rw [hlen]; simpa using hik) hri
      exact fixSemK_inhab h hw h0 n _ _ hvsp hmem

end KRec

/-! ## Closed binder data at any bottom -/

/-- A term closed at depth `k` reads the same at any two frames
agreeing below `k`. -/
theorem interp2_closed_bottom {e : AVExpr} {k : Nat} (hcl : VExpr.bvarsBelow k e.erase)
    {as : List V} (hlen : as.length = k) (ρ₁ ρ₂ : Nat → V) :
    interp2 V (consList as ρ₁) e = interp2 V (consList as ρ₂) e :=
  interp2_congr_noBVar e (NoBVar_of_bvarsBelow hcl fun _ hi => hlen ▸ hi)
    (agreeOff_consList_ge as ρ₁ ρ₂)

theorem AnnotOk2_closed_bottom {e : AVExpr} {k : Nat} (hcl : VExpr.bvarsBelow k e.erase)
    {as : List V} (hlen : as.length = k) (ρ₁ ρ₂ : Nat → V) :
    AnnotOk2 V (consList as ρ₁) e ↔ AnnotOk2 V (consList as ρ₂) e :=
  AnnotOk2_congr_noBVar e (NoBVar_of_bvarsBelow hcl fun _ hi => hlen ▸ hi)
    (agreeOff_consList_ge as ρ₁ ρ₂)

/-- A spine fits closed binder data at any bottom. -/
theorem spineFit_closed_bottom :
    ∀ {ds : List (Nat × Nat × AVExpr)} {as bs : List V} {ρ₁ ρ₂ : Nat → V},
      (∀ k d, ds[k]? = some d → VExpr.bvarsBelow (as.length + k) d.2.2.erase) →
      SpineFit (consList as ρ₁) (ds.map (·.2.2)) bs → SpineFit (consList as ρ₂) (ds.map (·.2.2)) bs
  | [], _, [], _, _, _, h => h
  | [], _, _ :: _, _, _, _, h => h.elim
  | _ :: _, _, [], _, _, _, h => h.elim
  | d :: ds, as, b :: bs, ρ₁, ρ₂, hcl, h => by
    refine ⟨?_, ?_⟩
    · have := h.1
      rwa [interp2_closed_bottom (by simpa using hcl 0 d rfl) (as := as) rfl ρ₁ ρ₂] at this
    · have h2 := h.2
      rw [consList_snoc'] at h2 ⊢
      refine spineFit_closed_bottom (as := as ++ [b]) ?_ h2
      intro k d' hd'
      have := hcl (k + 1) d' (by simpa using hd')
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- The Π-tower over closed binder data reads the same at any bottom. -/
theorem mkPisAV_closed_bottom {C : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {as : List V} {ρ₁ ρ₂ : Nat → V},
      (∀ k d, ds[k]? = some d → VExpr.bvarsBelow (as.length + k) d.2.2.erase) →
      VExpr.bvarsBelow (as.length + ds.length) C.erase →
      interp2 V (consList as ρ₁) (mkPisAV ds C) = interp2 V (consList as ρ₂) (mkPisAV ds C)
  | [], as, ρ₁, ρ₂, _, hC => by
    show interp2 V (consList as ρ₁) C = interp2 V (consList as ρ₂) C
    exact interp2_closed_bottom (by simpa using hC) rfl ρ₁ ρ₂
  | d :: ds, as, ρ₁, ρ₂, hcl, hC => by
    show piR d.2.1 (interp2 V (consList as ρ₁) d.2.2) (fun a => interp2 V (cons a (consList as ρ₁)) (mkPisAV ds C))
      = piR d.2.1 (interp2 V (consList as ρ₂) d.2.2) (fun a => interp2 V (cons a (consList as ρ₂)) (mkPisAV ds C))
    rw [interp2_closed_bottom (by simpa using hcl 0 d rfl) (as := as) rfl ρ₁ ρ₂]
    refine piR_congr fun a _ => ?_
    rw [consList_snoc', consList_snoc']
    refine mkPisAV_closed_bottom (as := as ++ [a]) ?_ (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hC)
    intro k d' hd'
    have := hcl (k + 1) d' (by simpa using hd')
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-! ## The spelled recursor -/

/-- The sort of a Π-tower's reading from its first binder's bits. -/
def recSortOf : List (Nat × Nat × AVExpr) → Nat
  | [] => 0
  | d :: _ => imaxN d.1 d.2.1

/-- The recursor's type, spelled: the Π-tower over its binder data
ending in `M ı⃗ t`. -/
def recTyAV (n nIdx : Nat) (rds : List (Nat × Nat × AVExpr)) : AVExpr :=
  mkPisAV rds (recConcAV n nIdx)

/-- The recursor body under the major, at depth `1` below the K-frame:
the case split with the ih arguments (graph regime), the point at a
squash instantiation. -/
def fixRecBodyAVI (ℓ w nP : Nat) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) : AVExpr :=
  if w = 0 then .prf
  else .app (caseRecAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
      (fun j => (Fss.getD j []).length)
      (ihArgsI nP Fss.length Ids.length rss Eiss (fun j => (Fss.getD j []).length))
      Fss.length Ids.length Fss.length 1 0 (.proj 0 (.bvar 0)))
    (.proj 1 (.bvar 0))

theorem fixRecBodyAVI_zero (ℓ nP : Nat) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) :
    fixRecBodyAVI ℓ 0 nP Fss Ess Ids rss Eiss = .prf := if_pos rfl

theorem fixRecBodyAVI_pos {w : Nat} (hw : w ≠ 0) (ℓ nP : Nat) (Fss Ess : List (List AVExpr))
    (Ids : List AVExpr) (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) :
    fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss
      = .app (caseRecAVI ℓ w (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)
          (fun j => (Fss.getD j []).length)
          (ihArgsI nP Fss.length Ids.length rss Eiss (fun j => (Fss.getD j []).length))
          Fss.length Ids.length Fss.length 1 0 (.proj 0 (.bvar 0)))
        (.proj 1 (.bvar 0)) := if_neg hw

/-- The one-step unfolding `λ r. λ p⃗ M m⃗ ı⃗ t. body`. -/
def fixStepAVI (ℓ w nP : Nat) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) (rds : List (Nat × Nat × AVExpr)) :
    AVExpr :=
  .lam (recSortOf rds) (recTyAV Fss.length Ids.length rds)
    (mkLamsC ℓ rds (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss))

/-- `Σ' (r : RecTy), Step r = r`. -/
def fixSigAVI (ℓ w nP : Nat) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) (rds : List (Nat × Nat × AVExpr)) :
    AVExpr :=
  AVExpr.mkAppN (.const .psigma [recSortOf rds, 0]) [recTyAV Fss.length Ids.length rds,
    .lam 1 (recTyAV Fss.length Ids.length rds)
      (.eqE ((recTyAV Fss.length Ids.length rds).liftN 1 0)
        (.app ((fixStepAVI ℓ w nP Fss Ess Ids rss Eiss rds).liftN 1 0) (.bvar 0)) (.bvar 0))]

/-- The selected fixed point `(choice Σ prf).1` — **the recursor leaf**
(a closed term). -/
def fixSelAVI (ℓ w nP : Nat) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) (rds : List (Nat × Nat × AVExpr)) :
    AVExpr :=
  .proj 0 (AVExpr.mkAppN (.const .choice [recSortOf rds])
    [fixSigAVI ℓ w nP Fss Ess Ids rss Eiss rds, .prf])

/-! ## The premise -/

/-- The domains of binder data graded along every fitting walk. -/
def DomsWalk : (Nat → V) → List (Nat × Nat × AVExpr) → Prop
  | _, [] => True
  | ρ, d :: ds => AnnotOk2 V ρ d.2.2 ∧ ∀ a, a ∈ˢ interp2 V ρ d.2.2 → DomsWalk (cons a ρ) ds

/-- `UnderTowerOk` from the domain walk and the base facts at every
fitting leaf. -/
theorem underTowerOk_of_walk {m : Nat} {b C : AVExpr} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      DomsWalk ρ ds →
      (∀ as, SpineFit ρ (ds.map (·.2.2)) as →
        AnnotOk2 V (consList as ρ) b ∧ interp2 V (consList as ρ) b ∈ˢ interp2 V (consList as ρ) C ∧
        (m = 0 → interp2 V (consList as ρ) C ∈ˢ (univZero : V))) →
      UnderTowerOk m ρ b C ds
  | [], ρ, _, hb => by
    have := hb [] trivial
    simp only [consList_nil] at this
    exact this
  | d :: ds, ρ, hw, hb => by
    refine ⟨hw.1, fun a ha => underTowerOk_of_walk (hw.2 a ha) fun as hsp => ?_⟩
    have := hb (a :: as) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- **The recursor's premise** — frame-generic (every field holds at
every bottom frame `ρb`): the binder data's bits zero-agree with the
elimination level, the data are closed, the domains are graded along
every walk, at every K-frame reached the case split's package holds
and the major's domain reads to the carrier at the frame's index tuple,
the index and major binders admit the ih spine, the conclusion is a
truth value at level zero, and the recursor's type reads to a graded
member of its sort's universe. -/
structure FixPre (V : Type uv) [SetTheory V] (ℓ w u nP : Nat) (Fss Ess Fss₀ : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) (rds : List (Nat × Nat × AVExpr)) :
    Prop where
  hz : ∀ d ∈ rds, (ℓ = 0 ↔ d.2.1 = 0)
  hlen : rds.length = nP + 1 + Fss.length + Ids.length + 1
  hclosed : ∀ k d, rds[k]? = some d → VExpr.bvarsBelow k d.2.2.erase
  hwℓ : w = 0 → ℓ = 0
  hdoms : ∀ ρb : Nat → V, DomsWalk ρb rds
  hK : ∀ (ρb : Nat → V) (as : List V) (t : V), SpineFit ρb (rds.map (·.2.2)) (as ++ [t]) →
    FixKI₀ ℓ w u (consList as ρb) Fss Ess Fss₀ Ids rss Eiss ∧
    t ∈ˢ SetTheory.app (famK u w (consList as ρb) Fss Ess Fss₀ Ids rss Eiss)
      (tupW u (frameIdx Ids.length (consList as ρb)))
  hspine : ∀ (ρb : Nat → V) (as : List V), SpineFit ρb ((rds.take (nP + 1 + Fss.length)).map (·.2.2)) as →
    ∀ (vals : List V) (f : V), SpineFit (shiftE (Fss.length + 1) 0 (consList as ρb)) Ids vals →
    f ∈ˢ SetTheory.app
      (fixFamI u w (shiftE (Fss.length + 1) 0 (consList as ρb)) Ids Ids.length rss Eiss Fss₀ Ess)
      (tupW u vals) →
    SpineFit ρb (rds.map (·.2.2)) (as ++ vals ++ [f])
  hconc0 : ℓ = 0 → ∀ (ρb : Nat → V) (as' : List V), SpineFit ρb (rds.map (·.2.2)) as' →
    interp2 V (consList as' ρb) (recConcAV Fss.length Ids.length) ∈ˢ (univZero : V)
  hRecTy : ∀ ρb : Nat → V,
    interp2 V ρb (recTyAV Fss.length Ids.length rds) ∈ˢ (univ (recSortOf rds) : V) ∧
    AnnotOk2 V ρb (recTyAV Fss.length Ids.length rds)
  hEbelow : ∀ j i, ∀ E ∈ (Eiss.getD j []).getD i [], VExpr.bvarsBelow (nP + i) E.erase

/-! ## K-frames of the walk -/

section WalkFrames

variable {u w : Nat} {Fss Ess Fss₀ : List (List AVExpr)} {Ids : List AVExpr} {rss : List (List Bool)}
  {Eiss : List (List (List AVExpr))}

omit [SetTheory V] in
/-- The K-frame of a leaf frame. -/
theorem shiftE_leaf (as : List V) (t : V) (ρb : Nat → V) :
    shiftE 1 0 (consList (as ++ [t]) ρb) = consList as ρb := by
  rw [← consList_snoc', show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]

omit [SetTheory V] in
/-- The function slot of a K-frame `(ρb, r, p⃗, M, m⃗, ı⃗)`. -/
theorem frR_of (nP n nIdx : Nat) {as : List V} (hlen : as.length = nP + 1 + n + nIdx) (r : V)
    (ρb : Nat → V) : frR nP n nIdx (consList as (cons r ρb)) = r := by
  unfold frR frP
  rw [shiftE_zero]
  show consList as (cons r ρb) (nP + (nIdx + n + 1)) = r
  have := consList_apply_add as (cons r ρb) 0
  rw [Nat.zero_add, hlen, show nP + 1 + n + nIdx = nP + (nIdx + n + 1) from by omega] at this
  rw [this]; rfl

omit [SetTheory V] in
/-- The frame below the function slot. -/
theorem frBelow_of (nP n nIdx : Nat) {as : List V} (hlen : as.length = nP + 1 + n + nIdx) (r : V)
    (ρb : Nat → V) : frBelow nP n nIdx (consList as (cons r ρb)) = ρb := by
  unfold frBelow
  rw [show nIdx + n + 1 + nP + 1 = as.length + 1 from by omega, shiftE_consList_add,
    shiftE_succ_cons, shiftE_zero_zero]

omit [SetTheory V] in
/-- The parameter frame of a K-frame over a bottom: the bottom under
the parameters, i.e. the shift of the block frame past the motive and
the minors. -/
theorem frP_of (n nIdx : Nat) {as is : List V} (hlen : is.length = nIdx) (ρb : Nat → V) :
    frP n nIdx (consList (as ++ is) ρb) = shiftE (n + 1) 0 (consList as ρb) := by
  unfold frP
  rw [consList_append, show nIdx + n + 1 = is.length + (n + 1) from by omega, shiftE_consList_add]

omit [SetTheory V] in
/-- The block spine of a K-frame over a bottom. -/
theorem frKSpine_of (nP n nIdx : Nat) {as is : List V} (hlen : as.length = nP + 1 + n)
    (hilen : is.length = nIdx) (ρb : Nat → V) :
    frKSpine nP n nIdx (consList (as ++ is) ρb) = as := by
  unfold frKSpine
  rw [consList_append, ← hilen, shiftE_consList, ← hlen]
  exact frameIdx_consList' as ρb

omit [SetTheory V] in
/-- The index tuple of a K-frame over a bottom. -/
theorem frameIdx_of (nIdx : Nat) {as is : List V} (hilen : is.length = nIdx) (ρb : Nat → V) :
    frameIdx nIdx (consList (as ++ is) ρb) = is := by
  rw [consList_append, ← hilen]
  exact frameIdx_consList' is _

omit [SetTheory V] in
/-- The minors of a K-frame over a bottom depend on the block only. -/
theorem frMs_of (n nIdx : Nat) {as is : List V} (hilen : is.length = nIdx) (ρb : Nat → V) {j : Nat}
    (hj : j < n) : frMs n nIdx (consList (as ++ is) ρb) j = consList as ρb (n - 1 - j) := by
  unfold frMs
  rw [consList_append, show nIdx + n - 1 - j = (n - 1 - j) + is.length from by omega,
    consList_apply_add]

omit [SetTheory V] in
theorem frM_of (n nIdx : Nat) {as is : List V} (hilen : is.length = nIdx) (ρb : Nat → V) :
    frM n nIdx (consList (as ++ is) ρb) = consList as ρb n := by
  unfold frM
  rw [consList_append, show nIdx + n = n + is.length from by omega, consList_apply_add]

/-- The fold of a semantic tower along a fitting spine (nonzero bit). -/
theorem lamTower_fold {m : Nat} (hm : m ≠ 0) {g : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V} {bs : List V},
      SpineFit ρ (ds.map (·.2.2)) bs → bs.foldl SetTheory.app (lamTower m ρ ds g) = g (consList bs ρ)
  | [], _, [], _ => rfl
  | [], _, _ :: _, hsp => hsp.elim
  | _ :: _, _, [], hsp => hsp.elim
  | d :: ds, ρ, b :: bs, hsp => by
    show bs.foldl SetTheory.app (SetTheory.app (lamR m (interp2 V ρ d.2.2)
      fun a => lamTower m (cons a ρ) ds g) b) = _
    rw [app_lamR_pos hm hsp.1, consList_cons]
    exact lamTower_fold hm hsp.2

end WalkFrames

/-! ## The squash regime's stages -/

section KRecZero

variable {ℓ w u : Nat} {K : Nat → V} {Fss Ess Fss₀ : List (List AVExpr)} {Ids : List AVExpr}
  {rss : List (List Bool)} {Eiss : List (List (List AVExpr))}

/-- A member of a stage at a tuple (squash regime): the point, with a
constructor's fitting tuple. -/
theorem stage_elim_zero (h : FixKI₀ ℓ 0 u K Fss Ess Fss₀ Ids rss Eiss) {n : Nat}
    {is : List V} (hsp : SpineFit (frP Fss.length Ids.length K) Ids is) {t : V}
    (ht : t ∈ˢ SetTheory.app (iterK u 0 K Fss Ess Fss₀ Ids rss Eiss (n + 1)) (tupW u is)) :
    t = pt ∧ ∃ j fs, j < Fss.length ∧ fs.length = (Fss.getD j []).length ∧
      SpineFit (frP Fss.length Ids.length K) (Fss.getD j []) fs ∧
      idxValsAt (frP Fss.length Ids.length K) (Ess.getD j []) fs = is ∧
      (∀ l, l < fs.length → (rss.getD j []).getD l false = true →
        fs.getD l pt ∈ˢ SetTheory.app (iterK u 0 K Fss Ess Fss₀ Ids rss Eiss n)
          (tupW u ((((Eiss.getD j []).getD l []).map
            (interp2 V (consList (fs.take l) (frP Fss.length Ids.length K)))))) ∧
        SpineFit (frP Fss.length Ids.length K) Ids
          (((Eiss.getD j []).getD l []).map
            (interp2 V (consList (fs.take l) (frP Fss.length Ids.length K))))) := by
  have ht' : t ∈ˢ fixStepI u 0 (frP Fss.length Ids.length K) Ids Ids.length rss Eiss Fss₀ Ess
      (iterK u 0 K Fss Ess Fss₀ Ids rss Eiss n) (tupW u is) := by
    unfold iterK famIter at ht
    rwa [famFI_app (tupW_mem hsp)] at ht
  obtain ⟨rfl, j, fs, hj₀, hlen₀, hspX, hall⟩ := fixStepI_zero_elim ht'
  obtain ⟨hl₀, hlE, hEs, hlenj, hc⟩ := h.hreal
  have hj : j < Fss.length := by omega
  have hfit := h.hX.hfit _ (famIter_mem h.hX n) _ (tupW_mem hsp) j hj₀
  have hspR := spineFit_real_of_XI h.hX.hI (iterK_le_fam h n) (Fss₀.getD j []) (Fss.getD j []) 0 [] fs rfl
    (hc j hj) hfit hspX
  have hlen : fs.length = (Fss.getD j []).length := by rw [hlen₀]; exact hlenj j hj
  refine ⟨rfl, j, fs, hj, hlen, hspR, ?_, ?_⟩
  · rw [← hlen₀] at hall
    exact idxValsAt_of_eqsXI h.hX.hI hsp (hEs j hj) hall
  · intro l hl hrl
    have hmem := fitsXI_rec_mem h.hX.hI (Fss₀.getD j []) 0 [] fs rfl hfit hspX l hl
      (by rw [Nat.zero_add]; exact hrl)
    rw [Nat.zero_add, List.nil_append] at hmem
    have hat := chainRealI_at (Fss₀.getD j []) (Fss.getD j []) 0 [] fs rfl (hc j hj) (by simpa using hspR) l
      (by omega) (by rw [Nat.zero_add]; exact hrl)
    rw [Nat.zero_add, List.nil_append] at hat
    exact ⟨hmem, hat.2.1⟩

/-- **Inhabitation at a zero elimination level** (squash regime). -/
theorem fixSemK_inhab_zero (h : FixKI₀ ℓ 0 u K Fss Ess Fss₀ Ids rss Eiss) (h0 : ℓ = 0) :
    ∀ (n : Nat) (is : List V) (t : V), SpineFit (frP Fss.length Ids.length K) Ids is →
      t ∈ˢ SetTheory.app (iterK u 0 K Fss Ess Fss₀ Ids rss Eiss n) (tupW u is) →
      ∃ y, y ∈ˢ SetTheory.app (is.foldl SetTheory.app (frM Fss.length Ids.length K)) t
  | 0, is, _, hsp, ht => by
    unfold iterK famIter at ht
    rw [app_graph (tupW_mem hsp)] at ht
    exact absurd ht (not_mem_empty _)
  | n + 1, is, t, hsp, ht => by
    obtain ⟨rfl, j, fs, hj, hlen, hspR, hidx, hrec⟩ := stage_elim_zero h hsp ht
    have hms := h.hyp.hms j hj
    rw [h0] at hms
    obtain ⟨x, hx⟩ := minorSpI_zero_inhab hms hspR
    rw [List.nil_append] at hx
    have := ihSpL_zero_inhab hx ?_
    · unfold concI ctorValI at this
      rwa [hidx, if_pos rfl] at this
    · intro A hA
      unfold ihDomsI at hA
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hA
      obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
      obtain ⟨hmem, hvsp⟩ := hrec i (by rw [hlen]; simpa using hik) hri
      exact fixSemK_inhab_zero h h0 n _ _ hvsp hmem

end KRecZero

/-! ## The recursor's semantics -/

section Rec

variable {ℓ w u nP : Nat} {Fss Ess Fss₀ : List (List AVExpr)} {Ids : List AVExpr}
  {rss : List (List Bool)} {Eiss : List (List (List AVExpr))} {rds : List (Nat × Nat × AVExpr)}

theorem recConcAV_below (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) :
    VExpr.bvarsBelow rds.length (recConcAV Fss.length Ids.length).erase := by
  have hlt : Ids.length + Fss.length < rds.length - 1 := by rw [h.hlen]; omega
  have := motAppAV_below (D' := 1) (K := rds.length - 1) hlt
  rw [show rds.length - 1 + 1 = rds.length from by rw [h.hlen]; omega] at this
  exact ⟨this, show 0 < rds.length by rw [h.hlen]; omega⟩

/-- The recursor type's reading is bottom-independent. -/
theorem recTy_bottom (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) (ρ₁ ρ₂ : Nat → V) :
    interp2 V ρ₁ (recTyAV Fss.length Ids.length rds) = interp2 V ρ₂ (recTyAV Fss.length Ids.length rds) := by
  unfold recTyAV
  have := mkPisAV_closed_bottom (C := recConcAV Fss.length Ids.length) (ds := rds) (as := [])
    (ρ₁ := ρ₁) (ρ₂ := ρ₂) (by simpa using h.hclosed) (by simpa using recConcAV_below h)
  simpa using this

theorem recSort_zero_iff (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) :
    recSortOf rds = 0 ↔ ℓ = 0 := by
  cases hr : rds with
  | nil => have := h.hlen; rw [hr] at this; simp at this
  | cons d ds =>
    show imaxN d.1 d.2.1 = 0 ↔ ℓ = 0
    rw [imaxN_eq_zero_iff]
    have := h.hz d (by rw [hr]; exact .head _)
    exact this.symm

/-- A spine fitting a chain fits a prefix of it. -/
theorem spineFit_prefix {ρ : Nat → V} {Ds : List AVExpr} {as bs : List V}
    (h : SpineFit ρ Ds (as ++ bs)) : SpineFit ρ (Ds.take as.length) as := by
  have hlen : (as ++ bs).length = Ds.length := h.length_eq
  have hsplit : Ds = Ds.take as.length ++ Ds.drop as.length := (List.take_append_drop _ _).symm
  rw [hsplit] at h
  obtain ⟨as₁, as₂, heq, h1, -⟩ := spineFit_append_split h
  have hl₁ : as₁.length = as.length := by
    rw [h1.length_eq, List.length_take]
    rw [List.length_append] at hlen
    omega
  obtain ⟨rfl, -⟩ := List.append_inj heq hl₁.symm
  exact h1

/-- The tower walk from the leaves. -/
theorem towerWalk_of_leaves {m : Nat} {C : AVExpr} {g : (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AVExpr)} {ρ : Nat → V},
      (∀ bs, SpineFit ρ (ds.map (·.2.2)) bs →
        g (consList bs ρ) ∈ˢ interp2 V (consList bs ρ) C ∧ (m = 0 → interp2 V (consList bs ρ) C ∈ˢ (univZero : V))) →
      TowerWalk m C g ρ ds
  | [], ρ, hb => by
    have := hb [] trivial
    simp only [consList_nil] at this
    exact this
  | d :: ds, ρ, hb => fun a ha => towerWalk_of_leaves fun bs hsp => by
    have := hb (a :: bs) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- The K-frame package with the function, at a walk K-frame over
`cons r ρb` with `r` in the recursor's type. -/
theorem fixKI_of (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) (ρb : Nat → V) {r : V}
    (hr : r ∈ˢ interp2 V ρb (recTyAV Fss.length Ids.length rds)) {as : List V} {t : V}
    (hsp : SpineFit (cons r ρb) (rds.map (·.2.2)) (as ++ [t])) :
    FixKI ℓ w u nP (consList as (cons r ρb)) Fss Ess Fss₀ Ids rss Eiss rds := by
  obtain ⟨h0, -⟩ := h.hK (cons r ρb) as t hsp
  have hlen_as : as.length = nP + 1 + Fss.length + Ids.length := by
    have := hsp.length_eq
    rw [List.length_append, List.length_singleton, List.length_map, h.hlen] at this
    omega
  obtain ⟨as₀, is, rfl, hl₀, hli⟩ : ∃ as₀ is, as = as₀ ++ is ∧ as₀.length = nP + 1 + Fss.length ∧
      is.length = Ids.length :=
    ⟨as.take (nP + 1 + Fss.length), as.drop (nP + 1 + Fss.length), (List.take_append_drop _ _).symm,
      by rw [List.length_take]; omega, by rw [List.length_drop]; omega⟩
  refine ⟨h0, h.hz, ?_, ?_, h.hlen, ?_⟩
  · rw [frR_of nP Fss.length Ids.length hlen_as, frBelow_of nP Fss.length Ids.length hlen_as]
    show r ∈ˢ interp2 V (cons r ρb) (recTyAV Fss.length Ids.length rds)
    rw [recTy_bottom h (cons r ρb) ρb]
    exact hr
  · intro vals f hv hf
    rw [frR_of nP Fss.length Ids.length hlen_as, frBelow_of nP Fss.length Ids.length hlen_as,
      frKSpine_of nP Fss.length Ids.length hl₀ hli]
    have hsp₀ : SpineFit (cons r ρb) ((rds.take (nP + 1 + Fss.length)).map (·.2.2)) as₀ := by
      have := spineFit_prefix (as := as₀) (bs := is ++ [t]) (by rw [← List.append_assoc]; exact hsp)
      rwa [hl₀, ← List.map_take] at this
    rw [frP_of Fss.length Ids.length hli] at hv hf
    exact h.hspine (cons r ρb) as₀ hsp₀ vals f hv hf
  · intro h0 as' hsp'
    rw [frR_of nP Fss.length Ids.length hlen_as, frBelow_of nP Fss.length Ids.length hlen_as] at hsp' ⊢
    exact h.hconc0 h0 (cons r ρb) as' hsp'

/-- **The recursor body's facts** at a walk leaf: graded, in the
conclusion, a truth value at level zero. -/
theorem body_facts (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) (ρb : Nat → V) {r : V}
    (hr : r ∈ˢ interp2 V ρb (recTyAV Fss.length Ids.length rds)) {as : List V} {t : V}
    (hsp : SpineFit (cons r ρb) (rds.map (·.2.2)) (as ++ [t])) :
    AnnotOk2 V (consList (as ++ [t]) (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss) ∧
    interp2 V (consList (as ++ [t]) (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss)
      ∈ˢ interp2 V (consList (as ++ [t]) (cons r ρb)) (recConcAV Fss.length Ids.length) ∧
    (ℓ = 0 → interp2 V (consList (as ++ [t]) (cons r ρb)) (recConcAV Fss.length Ids.length)
      ∈ˢ (univZero : V)) := by
  have hKI := fixKI_of h ρb hr hsp
  obtain ⟨-, ht⟩ := h.hK (cons r ρb) as t hsp
  rw [← consList_snoc']
  have hfr : RecFrameS 1 (consList as (cons r ρb)) (cons t (consList as (cons r ρb))) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  obtain ⟨hMv, -⟩ := motApp_facts hfr hKI.hyp.toRecHypCore
  have hconc : interp2 V (cons t (consList as (cons r ρb))) (recConcAV Fss.length Ids.length)
      = SetTheory.app (frMi Fss.length Ids.length (consList as (cons r ρb))) t := by
    unfold recConcAV
    rw [interp2_app, hMv, interp2_bvar, cons_zero]
  have hfitI := hKI.hyp.hfit
  have ht' : t ∈ˢ sumSet w (sumFibre w (consList as (cons r ρb))
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) := by
    rw [← hKI.hyp.hfam]
    exact ht
  refine ⟨?_, ?_, fun h0 => by rw [hconc]; exact hKI.hyp.hM0 h0 t⟩
  · -- graded
    by_cases hw : w = 0
    · subst hw; rw [fixRecBodyAVI_zero]; trivial
    · rw [fixRecBodyAVI_pos hw]
      have hcase := caseRec_factsI hw hKI.hyp
        (fun D' j' σ' hfr' hj' => FixKI.ihArgsOk_of hKI hw hfr' hj') Fss.length (D := 1) (j := 0)
        (σ := cons t (consList as (cons r ρb))) (k := .proj 0 (.bvar 0)) hfr (Nat.zero_add _)
      have hok0 := major_proj_ok2 hw hKI.hyp.hok (σ := cons t (consList as (cons r ρb))) ht' (i := 0) (by omega)
      have hok1 := major_proj_ok2 hw hKI.hyp.hok (σ := cons t (consList as (cons r ρb))) ht' (i := 1) (by omega)
      obtain ⟨i, a, ha, hta⟩ := sumSet_elim hw ht'
      have htag : interp2 V (cons t (consList as (cons r ρb))) (.proj 0 (.bvar 0)) = vnat i := by
        rw [interp2_proj, if_pos rfl, interp2_bvar, cons_zero, hta, sfst_inj]
      have hpay : interp2 V (cons t (consList as (cons r ρb))) (.proj 1 (.bvar 0)) = a := by
        rw [interp2_proj, if_neg Nat.one_ne_zero, interp2_bvar, cons_zero, hta, ssnd_inj]
      have hkω : interp2 V (cons t (consList as (cons r ρb))) (.proj 0 (.bvar 0)) ∈ˢ (omega : V) := by
        rw [htag]; exact vnat_mem_omega i
      obtain ⟨hmem, -⟩ := hcase.1 hkω
      rw [htag, motSem_vnat, Nat.zero_add] at hmem
      rw [AnnotOk2_app]
      refine ⟨hcase.2 hok0 (fun _ => hkω), hok1, ℓ, _, _, hmem, ?_, ?_⟩
      · rw [hpay]; exact ha
      · intro h0 y _
        exact hKI.hyp.hM0 h0 _
  · -- in the conclusion
    rw [hconc]
    by_cases hw : w = 0
    · subst hw
      rw [fixRecBodyAVI_zero, interp2_prf]
      have h0 : ℓ = 0 := h.hwℓ rfl
      have hiter := ht
      unfold famK at hiter
      rw [fixFamI_app_eq_famU hKI.hX (tupW_mem hfitI), famU_app (tupW_mem hfitI)] at hiter
      obtain ⟨n, hn⟩ := mem_natUnion.mp hiter
      obtain ⟨y, hy⟩ := fixSemK_inhab_zero hKI.toFixKI₀ h0 n _ t hfitI hn
      have := eq_pt_of_mem_univZero (hKI.hyp.hM0 h0 t) hy
      subst this
      exact hy
    · rw [fixRecBodyAVI_pos hw]
      have hcase := caseRec_factsI hw hKI.hyp
        (fun D' j' σ' hfr' hj' => FixKI.ihArgsOk_of hKI hw hfr' hj') Fss.length (D := 1) (j := 0)
        (σ := cons t (consList as (cons r ρb))) (k := .proj 0 (.bvar 0)) hfr (Nat.zero_add _)
      obtain ⟨i, a, ha, hta⟩ := sumSet_elim hw ht'
      have htag : interp2 V (cons t (consList as (cons r ρb))) (.proj 0 (.bvar 0)) = vnat i := by
        rw [interp2_proj, if_pos rfl, interp2_bvar, cons_zero, hta, sfst_inj]
      have hpay : interp2 V (cons t (consList as (cons r ρb))) (.proj 1 (.bvar 0)) = a := by
        rw [interp2_proj, if_neg Nat.one_ne_zero, interp2_bvar, cons_zero, hta, ssnd_inj]
      have hkω : interp2 V (cons t (consList as (cons r ρb))) (.proj 0 (.bvar 0)) ∈ˢ (omega : V) := by
        rw [htag]; exact vnat_mem_omega i
      obtain ⟨hmem, -⟩ := hcase.1 hkω
      rw [htag, motSem_vnat, Nat.zero_add] at hmem
      rw [interp2_app, hpay]
      have := app_mem_piR hmem ha (fun h0 y _ => hKI.hyp.hM0 h0 _)
      rwa [injW_pos hw, ← hta] at this

/-- The semantic step at a bottom. -/
noncomputable def stepVI (ℓ w nP : Nat) (Fss Ess : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) (rds : List (Nat × Nat × AVExpr))
    (ρb : Nat → V) : V :=
  lamR (recSortOf rds) (interp2 V ρb (recTyAV Fss.length Ids.length rds)) fun r =>
    lamTower ℓ (cons r ρb) rds fun σ => interp2 V σ (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss)

/-- **The step's facts**: its value, its membership in
`RecTy → RecTy`, its grading. -/
theorem stepAV_facts (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) (ρb : Nat → V) :
    interp2 V ρb (fixStepAVI ℓ w nP Fss Ess Ids rss Eiss rds) = stepVI ℓ w nP Fss Ess Ids rss Eiss rds ρb ∧
    stepVI ℓ w nP Fss Ess Ids rss Eiss rds ρb
      ∈ˢ piR (recSortOf rds) (interp2 V ρb (recTyAV Fss.length Ids.length rds))
          (fun _ => interp2 V ρb (recTyAV Fss.length Ids.length rds)) ∧
    AnnotOk2 V ρb (fixStepAVI ℓ w nP Fss Ess Ids rss Eiss rds) := by
  have hleaf : ∀ r, r ∈ˢ interp2 V ρb (recTyAV Fss.length Ids.length rds) →
      ∀ bs, SpineFit (cons r ρb) (rds.map (·.2.2)) bs →
        AnnotOk2 V (consList bs (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss) ∧
        interp2 V (consList bs (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss)
          ∈ˢ interp2 V (consList bs (cons r ρb)) (recConcAV Fss.length Ids.length) ∧
        (ℓ = 0 → interp2 V (consList bs (cons r ρb)) (recConcAV Fss.length Ids.length) ∈ˢ (univZero : V)) := by
    intro r hr bs hsp
    rcases List.eq_nil_or_concat bs with rfl | ⟨as, t, rfl⟩
    · have := hsp.length_eq
      rw [List.length_map, h.hlen] at this
      simp at this
    · rw [List.concat_eq_append] at hsp ⊢
      exact body_facts h ρb hr hsp
  have hmemTower : ∀ r, r ∈ˢ interp2 V ρb (recTyAV Fss.length Ids.length rds) →
      lamTower ℓ (cons r ρb) rds (fun σ => interp2 V σ (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss))
        ∈ˢ interp2 V ρb (recTyAV Fss.length Ids.length rds) := by
    intro r hr
    rw [recTy_bottom h ρb (cons r ρb)]
    exact lamTower_mem h.hz (towerWalk_of_leaves fun bs hsp => ⟨(hleaf r hr bs hsp).2.1, (hleaf r hr bs hsp).2.2⟩)
  refine ⟨?_, ?_, ?_⟩
  · unfold fixStepAVI stepVI
    rw [interp2_lam]
    exact lamR_congr fun r _ => interp2_mkLamsC ℓ _ rds (cons r ρb)
  · unfold stepVI
    exact lamR_mem fun r hr => hmemTower r hr
  · unfold fixStepAVI
    rw [AnnotOk2_lam]
    refine ⟨(h.hRecTy ρb).2, fun r hr => ?_, fun _ => interp2 V ρb (recTyAV Fss.length Ids.length rds),
      fun r hr => ?_, fun h0 _ _ => ?_⟩
    · exact mkLamsC_ok2 h.hz (underTowerOk_of_walk (h.hdoms (cons r ρb)) (hleaf r hr))
    · rw [interp2_mkLamsC]
      exact hmemTower r hr
    · have := (h.hRecTy ρb).1
      rwa [h0, univ_zero] at this

/-! ## The body's iota at a walk leaf -/

/-- The recursive route's data at a K-frame `(ρb, r, p⃗, M, m⃗, ı⃗)`:
the block `(p⃗, M, m⃗)` and the index tuple. -/
theorem kframe_split (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) {ρ : Nat → V} {as : List V}
    {t : V} (hsp : SpineFit ρ (rds.map (·.2.2)) (as ++ [t])) :
    ∃ as₀ is, as = as₀ ++ is ∧ as₀.length = nP + 1 + Fss.length ∧ is.length = Ids.length := by
  have hlen_as : as.length = nP + 1 + Fss.length + Ids.length := by
    have := hsp.length_eq
    rw [List.length_append, List.length_singleton, List.length_map, h.hlen] at this
    omega
  exact ⟨as.take (nP + 1 + Fss.length), as.drop (nP + 1 + Fss.length), (List.take_append_drop _ _).symm,
    by rw [List.length_take]; omega, by rw [List.length_drop]; omega⟩

omit [SetTheory V] in
/-- The parameter frame of a K-frame over a bottom: the bottom under
the parameters. -/
theorem frP_block {ρb : Nat → V} {as₀ is : List V} (hl₀ : as₀.length = nP + 1 + Fss.length)
    (hli : is.length = Ids.length) :
    frP Fss.length Ids.length (consList (as₀ ++ is) ρb) = consList (as₀.take nP) ρb := by
  rw [frP_of Fss.length Ids.length hli]
  have hsplit : as₀ = as₀.take nP ++ as₀.drop nP := (List.take_append_drop _ _).symm
  conv => lhs; rw [hsplit]
  rw [consList_append, show Fss.length + 1 = (as₀.drop nP).length from by
    rw [List.length_drop]; omega, shiftE_consList]

/-- **The body's iota** at a walk leaf whose major is a constructor
value: the minor at the fields and the ih values (the function at the
block, the field's index values, the field). -/
theorem body_iota (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) (hw : w ≠ 0) (hℓ : ℓ ≠ 0)
    (ρb : Nat → V) {r : V} (hr : r ∈ˢ interp2 V ρb (recTyAV Fss.length Ids.length rds))
    {as : List V} {t : V} (hsp : SpineFit (cons r ρb) (rds.map (·.2.2)) (as ++ [t]))
    {j : Nat} (hj : j < Fss.length) {fs : List V} (hlen : fs.length = (Fss.getD j []).length)
    (hmaj : t = inj j (mkTower (fs ++ [pt]))) :
    interp2 V (consList (as ++ [t]) (cons r ρb)) (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss)
      = (fs ++ (recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
          (frKSpine nP Fss.length Ids.length (consList as (cons r ρb)) ++
            (((Eiss.getD j []).getD i []).map
              (interp2 V (consList (projList i (mkTower (fs ++ [pt])))
                (frP Fss.length Ids.length (consList as (cons r ρb)))))) ++
            [fs.getD i pt]).foldl SetTheory.app r).foldl SetTheory.app
          (frMs Fss.length Ids.length (consList as (cons r ρb)) j) := by
  have hKI := fixKI_of h ρb hr hsp
  obtain ⟨-, ht⟩ := h.hK (cons r ρb) as t hsp
  rw [← consList_snoc']
  have hfr : RecFrameS 1 (consList as (cons r ρb)) (cons t (consList as (cons r ρb))) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  have ht' : t ∈ˢ sumSet w (sumFibre w (consList as (cons r ρb))
      (rChains (Ids.length + Fss.length + 1) Ids.length Fss Ess)) := by
    rw [← hKI.hyp.hfam]; exact ht
  have hlen_as : as.length = nP + 1 + Fss.length + Ids.length := by
    have := hsp.length_eq
    rw [List.length_append, List.length_singleton, List.length_map, h.hlen] at this
    omega
  rw [fixRecBodyAVI_pos hw]
  have hcase := caseRec_factsI hw hKI.hyp
    (fun D' j' σ' hfr' hj' => FixKI.ihArgsOk_of hKI hw hfr' hj') Fss.length (D := 1) (j := 0)
    (σ := cons t (consList as (cons r ρb))) (k := .proj 0 (.bvar 0)) hfr (Nat.zero_add _)
  have htag : interp2 V (cons t (consList as (cons r ρb))) (.proj 0 (.bvar 0)) = vnat j := by
    rw [interp2_proj, if_pos rfl, interp2_bvar, cons_zero, hmaj, sfst_inj]
  have hpay : interp2 V (cons t (consList as (cons r ρb))) (.proj 1 (.bvar 0)) = mkTower (fs ++ [pt]) := by
    rw [interp2_proj, if_neg Nat.one_ne_zero, interp2_bvar, cons_zero, hmaj, ssnd_inj]
  have hkω : interp2 V (cons t (consList as (cons r ρb))) (.proj 0 (.bvar 0)) ∈ˢ (omega : V) := by
    rw [htag]; exact vnat_mem_omega j
  have hsel := (hcase.1 hkω).2 j htag hj
  rw [Nat.zero_add] at hsel
  rw [interp2_app, hsel, hpay]
  -- the payload is in the fibre
  obtain ⟨j', a, ha, hta⟩ := sumSet_elim hw ht'
  rw [hmaj] at hta
  obtain ⟨rfl, rfl⟩ := inj_inj hta
  unfold baseSemI
  rw [app_lamR_pos hℓ ha]
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
  · unfold ihValsI
    apply List.map_congr_left
    intro i hi
    obtain ⟨hik, -⟩ := mem_recIdx.mp hi
    rw [frR_of nP Fss.length Ids.length hlen_as, hproj i (by rw [hlen]; simpa using hik)]

/-! ## The candidate fixed point -/

/-- The candidate's body at a leaf frame: the point at level zero,
else the major's own stage's value. -/
noncomputable def gStar (ℓ u w : Nat) (Fss Ess Fss₀ : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) (σ : Nat → V) : V :=
  if ℓ = 0 then pt else
    fixSemK (shiftE 1 0 σ) Fss Ids rss
      (rkFam (iterK u w (shiftE 1 0 σ) Fss Ess Fss₀ Ids rss Eiss)
        (tupW u (frameIdx Ids.length (shiftE 1 0 σ))) (σ 0)) (σ 0)

/-- The candidate: the semantic tower over the recursor's binder data. -/
noncomputable def rStar (ℓ w u : Nat) (Fss Ess Fss₀ : List (List AVExpr)) (Ids : List AVExpr)
    (rss : List (List Bool)) (Eiss : List (List (List AVExpr))) (rds : List (Nat × Nat × AVExpr))
    (ρb : Nat → V) : V :=
  lamTower ℓ ρb rds (gStar ℓ u w Fss Ess Fss₀ Ids rss Eiss)

omit [SetTheory V] in
theorem leaf_zero (as : List V) (t : V) (ρb : Nat → V) : consList (as ++ [t]) ρb 0 = t := by
  rw [← consList_snoc', cons_zero]

/-- The conclusion at a walk leaf over a K-frame with the core package. -/
theorem conc_leaf {K : Nat → V} (h0 : FixKI₀ ℓ w u K Fss Ess Fss₀ Ids rss Eiss) (t : V) :
    interp2 V (cons t K) (recConcAV Fss.length Ids.length)
      = SetTheory.app ((frameIdx Ids.length K).foldl SetTheory.app (frM Fss.length Ids.length K)) t := by
  have hfr : RecFrameS 1 K (cons t K) := by
    unfold RecFrameS
    rw [show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
  obtain ⟨hMv, -⟩ := motApp_facts hfr h0.hyp.toRecHypCore
  unfold recConcAV
  rw [interp2_app, hMv, interp2_bvar, cons_zero]
  rfl

/-- **The candidate's body lands in the conclusion** at every walk
leaf. -/
theorem gStar_leaf (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) (ρb : Nat → V)
    {as : List V} {t : V} (hsp : SpineFit ρb (rds.map (·.2.2)) (as ++ [t])) :
    gStar ℓ u w Fss Ess Fss₀ Ids rss Eiss (consList (as ++ [t]) ρb)
      ∈ˢ interp2 V (consList (as ++ [t]) ρb) (recConcAV Fss.length Ids.length) := by
  obtain ⟨h0, ht⟩ := h.hK ρb as t hsp
  rw [← consList_snoc', conc_leaf h0 t]
  unfold gStar
  rw [shiftE_succ_cons, shiftE_zero_zero, cons_zero]
  have hfit := h0.hyp.hfit
  have hiter := ht
  unfold famK at hiter
  rw [fixFamI_app_eq_famU h0.hX (tupW_mem hfit), famU_app (tupW_mem hfit)] at hiter
  obtain ⟨n, hn⟩ := mem_natUnion.mp hiter
  by_cases hℓ : ℓ = 0
  · rw [if_pos hℓ]
    by_cases hw : w = 0
    · subst hw
      obtain ⟨y, hy⟩ := fixSemK_inhab_zero h0 hℓ n _ t hfit hn
      have := eq_pt_of_mem_univZero (h0.hyp.hM0 hℓ t) hy
      subst this; exact hy
    · obtain ⟨y, hy⟩ := fixSemK_inhab h0 hw hℓ n _ t hfit hn
      have := eq_pt_of_mem_univZero (h0.hyp.hM0 hℓ t) hy
      subst this; exact hy
  · rw [if_neg hℓ]
    have hw : w ≠ 0 := fun hw => hℓ (h.hwℓ hw)
    exact fixSemK_mem h0 hw hℓ _ _ t hfit (mem_rkFam ⟨n, hn⟩)

/-- **The candidate inhabits the recursor's type.** -/
theorem rStar_mem (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) (ρb : Nat → V) :
    rStar ℓ w u Fss Ess Fss₀ Ids rss Eiss rds ρb ∈ˢ interp2 V ρb (recTyAV Fss.length Ids.length rds) := by
  unfold rStar recTyAV
  refine lamTower_mem h.hz (towerWalk_of_leaves fun bs hsp => ?_)
  rcases List.eq_nil_or_concat bs with rfl | ⟨as, t, rfl⟩
  · have := hsp.length_eq
    rw [List.length_map, h.hlen] at this
    simp at this
  · rw [List.concat_eq_append] at hsp ⊢
    exact ⟨gStar_leaf h ρb hsp, fun h0 => h.hconc0 h0 ρb _ hsp⟩

/-- The candidate's application along a fitting spine (nonzero level). -/
theorem rStar_fold (_h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) (hℓ : ℓ ≠ 0) (ρb : Nat → V)
    {bs : List V} (hsp : SpineFit ρb (rds.map (·.2.2)) bs) :
    bs.foldl SetTheory.app (rStar ℓ w u Fss Ess Fss₀ Ids rss Eiss rds ρb)
      = gStar ℓ u w Fss Ess Fss₀ Ids rss Eiss (consList bs ρb) :=
  lamTower_fold hℓ hsp

omit [SetTheory V] in
/-- The K-frame's minors over two bottoms. -/
theorem frMs_bottom {as₀ is : List V} (hl₀ : as₀.length = nP + 1 + Fss.length) (hli : is.length = Ids.length)
    (ρ₁ ρ₂ : Nat → V) {j : Nat} (hj : j < Fss.length) :
    frMs Fss.length Ids.length (consList (as₀ ++ is) ρ₁) j
      = frMs Fss.length Ids.length (consList (as₀ ++ is) ρ₂) j := by
  rw [frMs_of Fss.length Ids.length hli ρ₁ hj, frMs_of Fss.length Ids.length hli ρ₂ hj]
  exact agreeOff_consList_ge as₀ ρ₁ ρ₂ _ (by omega)

omit [SetTheory V] in
theorem frM_bottom {as₀ is : List V} (hl₀ : as₀.length = nP + 1 + Fss.length) (hli : is.length = Ids.length)
    (ρ₁ ρ₂ : Nat → V) :
    frM Fss.length Ids.length (consList (as₀ ++ is) ρ₁) = frM Fss.length Ids.length (consList (as₀ ++ is) ρ₂) := by
  rw [frM_of Fss.length Ids.length hli ρ₁, frM_of Fss.length Ids.length hli ρ₂]
  exact agreeOff_consList_ge as₀ ρ₁ ρ₂ _ (by omega)

/-- A recursive field's index values do not see the bottom. -/
theorem idxVals_bottom (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) {as₀ is : List V}
    (hl₀ : as₀.length = nP + 1 + Fss.length) (hli : is.length = Ids.length) (ρ₁ ρ₂ : Nat → V)
    (j i : Nat) (y : V) :
    ((Eiss.getD j []).getD i []).map
        (interp2 V (consList (projList i y) (frP Fss.length Ids.length (consList (as₀ ++ is) ρ₁))))
      = ((Eiss.getD j []).getD i []).map
        (interp2 V (consList (projList i y) (frP Fss.length Ids.length (consList (as₀ ++ is) ρ₂)))) := by
  rw [frP_block (nP := nP) hl₀ hli, frP_block (nP := nP) hl₀ hli]
  apply List.map_congr_left
  intro E hE
  rw [← consList_append, ← consList_append]
  exact interp2_closed_bottom (h.hEbelow j i E hE) (as := as₀.take nP ++ projList i y)
    (by rw [List.length_append, List.length_take, projList_length]; omega) ρ₁ ρ₂

omit [SetTheory V] in
theorem frMsL_bottom {as₀ is : List V} (hl₀ : as₀.length = nP + 1 + Fss.length) (hli : is.length = Ids.length)
    (ρ₁ ρ₂ : Nat → V) :
    frMsL Fss.length Ids.length (consList (as₀ ++ is) ρ₁) = frMsL Fss.length Ids.length (consList (as₀ ++ is) ρ₂) := by
  unfold frMsL
  apply List.map_congr_left
  intro j hj
  exact frMs_bottom (nP := nP) hl₀ hli ρ₁ ρ₂ (List.mem_range.mp hj)

/-- The recursion's data at two K-frames over the same block. -/
theorem fixSemK_block {ρb : Nat → V} {as₀ is is' : List V} (_hl₀ : as₀.length = nP + 1 + Fss.length)
    (hli : is.length = Ids.length) (hli' : is'.length = Ids.length) :
    fixSemK (consList (as₀ ++ is) ρb) Fss Ids rss = fixSemK (consList (as₀ ++ is') ρb) Fss Ids rss := by
  unfold fixSemK
  have : frMsL Fss.length Ids.length (consList (as₀ ++ is) ρb)
      = frMsL Fss.length Ids.length (consList (as₀ ++ is') ρb) := by
    unfold frMsL
    apply List.map_congr_left
    intro j hj
    rw [frMs_of Fss.length Ids.length hli ρb (List.mem_range.mp hj),
      frMs_of Fss.length Ids.length hli' ρb (List.mem_range.mp hj)]
  rw [this]

theorem iterK_block {ρb : Nat → V} {as₀ is is' : List V}
    (hli : is.length = Ids.length) (hli' : is'.length = Ids.length) :
    iterK u w (consList (as₀ ++ is) ρb) Fss Ess Fss₀ Ids rss Eiss
      = iterK u w (consList (as₀ ++ is') ρb) Fss Ess Fss₀ Ids rss Eiss := by
  unfold iterK
  rw [frP_of Fss.length Ids.length hli, frP_of Fss.length Ids.length hli']

/-- **The candidate's body is the unfolding's body** at every walk
leaf: the fixed-point equation, leafwise. -/
theorem leaf_eq (h : FixPre V ℓ w u nP Fss Ess Fss₀ Ids rss Eiss rds) (hw : w ≠ 0) (hℓ : ℓ ≠ 0)
    (ρb : Nat → V) {as : List V} {t : V}
    (hsp : SpineFit (cons (rStar ℓ w u Fss Ess Fss₀ Ids rss Eiss rds ρb) ρb) (rds.map (·.2.2)) (as ++ [t])) :
    interp2 V (consList (as ++ [t]) (cons (rStar ℓ w u Fss Ess Fss₀ Ids rss Eiss rds ρb) ρb))
        (fixRecBodyAVI ℓ w nP Fss Ess Ids rss Eiss)
      = gStar ℓ u w Fss Ess Fss₀ Ids rss Eiss (consList (as ++ [t]) ρb) := by
  have hR := rStar_mem h ρb
  have hcl : ∀ k d, rds[k]? = some d → VExpr.bvarsBelow (([] : List V).length + k) d.2.2.erase := by
    simpa using h.hclosed
  have hsp₀ : SpineFit ρb (rds.map (·.2.2)) (as ++ [t]) :=
    spineFit_closed_bottom (as := []) (ρ₁ := cons (rStar ℓ w u Fss Ess Fss₀ Ids rss Eiss rds ρb) ρb) hcl hsp
  obtain ⟨h0, ht⟩ := h.hK ρb as t hsp₀
  obtain ⟨as₀, is, rfl, hl₀, hli⟩ := kframe_split h hsp₀
  have hfi : frameIdx Ids.length (consList (as₀ ++ is) ρb) = is := frameIdx_of Ids.length hli ρb
  have hfit : SpineFit (frP Fss.length Ids.length (consList (as₀ ++ is) ρb)) Ids is := by
    have := h0.hyp.hfit; rwa [hfi] at this
  rw [hfi] at ht
  have hiter := ht
  unfold famK at hiter
  rw [fixFamI_app_eq_famU h0.hX (tupW_mem hfit), famU_app (tupW_mem hfit)] at hiter
  obtain ⟨n₀, hn₀⟩ := mem_natUnion.mp hiter
  have hrk := mem_rkFam (Φ := iterK u w (consList (as₀ ++ is) ρb) Fss Ess Fss₀ Ids rss Eiss) ⟨n₀, hn₀⟩
  obtain ⟨m', hm⟩ : ∃ m', rkFam (iterK u w (consList (as₀ ++ is) ρb) Fss Ess Fss₀ Ids rss Eiss) (tupW u is) t
      = m' + 1 := by
    refine ⟨rkFam (iterK u w (consList (as₀ ++ is) ρb) Fss Ess Fss₀ Ids rss Eiss) (tupW u is) t - 1, ?_⟩
    have hne : rkFam (iterK u w (consList (as₀ ++ is) ρb) Fss Ess Fss₀ Ids rss Eiss) (tupW u is) t ≠ 0 := by
      intro hz
      rw [hz] at hrk
      unfold iterK famIter at hrk
      rw [app_graph (tupW_mem hfit)] at hrk
      exact not_mem_empty _ hrk
    omega
  rw [hm] at hrk
  obtain ⟨j, fs, hmaj, hj, hlen, hspR, hidx, hrec⟩ := stage_elim h0 hw hfit hrk
  -- the right-hand side: the stage's value
  have hrhs : gStar ℓ u w Fss Ess Fss₀ Ids rss Eiss (consList (as₀ ++ is ++ [t]) ρb)
      = (fs ++ (recIdx (rss.getD j []) (Fss.getD j []).length).map fun i =>
          fixSemK (consList (as₀ ++ is) ρb) Fss Ids rss m' (fs.getD i pt)).foldl SetTheory.app
          (frMs Fss.length Ids.length (consList (as₀ ++ is) ρb) j) := by
    unfold gStar
    rw [if_neg hℓ, shiftE_leaf, leaf_zero, hfi, hm, hmaj]
    unfold fixSemK
    rw [fixSem_inj m' j hlen]
    unfold stepBr
    simp only [frMsL_getD Fss.length Ids.length _ hj]
    try rfl
  rw [hrhs, body_iota h hw hℓ ρb hR hsp hj hlen hmaj]
  rw [frMs_bottom (nP := nP) hl₀ hli (cons _ ρb) ρb hj]
  congr 2
  apply List.map_congr_left
  intro i hi
  obtain ⟨hik, hri⟩ := mem_recIdx.mp hi
  obtain ⟨hmem, hvfit⟩ := hrec i (by rw [hlen]; exact hik) hri
  have hproj : projList i (mkTower (fs ++ [pt])) = fs.take i := by
    have h1 : projList (fs.length + 1) (mkTower (fs ++ [pt])) = fs ++ [pt] := projList_mkTower _ _ (by simp)
    have h2 := projList_take (fs.length + 1) i (mkTower (fs ++ [pt])) (by rw [hlen]; omega)
    rw [h1, List.take_append_of_le_length (by rw [hlen]; omega)] at h2
    exact h2.symm
  rw [frKSpine_of nP Fss.length Ids.length hl₀ hli, idxVals_bottom h hl₀ hli (cons _ ρb) ρb j i, hproj]
  -- the ih value: the candidate at the block, the index values and the field
  have hvals_len : (((Eiss.getD j []).getD i []).map
      (interp2 V (consList (fs.take i) (frP Fss.length Ids.length (consList (as₀ ++ is) ρb))))).length
      = Ids.length := hvfit.length_eq
  have hpre : SpineFit ρb ((rds.take (nP + 1 + Fss.length)).map (·.2.2)) as₀ := by
    have := spineFit_prefix (as := as₀) (bs := is ++ [t]) (by rw [← List.append_assoc]; exact hsp₀)
    rwa [hl₀, ← List.map_take] at this
  have hfmem : fs.getD i pt ∈ˢ SetTheory.app
      (fixFamI u w (shiftE (Fss.length + 1) 0 (consList as₀ ρb)) Ids Ids.length rss Eiss Fss₀ Ess)
      (tupW u (((Eiss.getD j []).getD i []).map
        (interp2 V (consList (fs.take i) (frP Fss.length Ids.length (consList (as₀ ++ is) ρb)))))) := by
    rw [← frP_of Fss.length Ids.length hli]
    exact iterK_le_fam h0 m' _ (tupW_mem hvfit) _ hmem
  have hspi := h.hspine ρb as₀ hpre _ (fs.getD i pt) (by rw [← frP_of Fss.length Ids.length hli]; exact hvfit) hfmem
  rw [rStar_fold h hℓ ρb hspi]
  unfold gStar
  rw [if_neg hℓ, shiftE_leaf, leaf_zero, frameIdx_of Ids.length hvals_len ρb,
    fixSemK_block (nP := nP) hl₀ hvals_len hli, iterK_block hvals_len hli]
  -- stability at the recursive component
  have hmem' := hmem
  have hmemrk := mem_rkFam (Φ := iterK u w (consList (as₀ ++ is) ρb) Fss Ess Fss₀ Ids rss Eiss)
    (tup := tupW u (((Eiss.getD j []).getD i []).map
      (interp2 V (consList (fs.take i) (frP Fss.length Ids.length (consList (as₀ ++ is) ρb))))))
    (t := fs.getD i pt) ⟨m', hmem'⟩
  generalize hrk : rkFam (iterK u w (consList (as₀ ++ is) ρb) Fss Ess Fss₀ Ids rss Eiss)
    (tupW u (((Eiss.getD j []).getD i []).map
      (interp2 V (consList (fs.take i) (frP Fss.length Ids.length (consList (as₀ ++ is) ρb))))))
    (fs.getD i pt) = rk at hmemrk ⊢
  rw [← fixSemK_stable h0 hw m' _ _ hvfit hmem' (max m' rk) (Nat.le_max_left _ _),
    ← fixSemK_stable h0 hw rk _ _ hvfit hmemrk (max m' rk) (Nat.le_max_right _ _)]

end Rec

end Lech.Semantics
