import Lech.Semantics.Tower.FixCaseI
import Lech.Semantics.Tower.SumRec

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

/-- The parameters' values at the K-frame, in order. -/
noncomputable def frPs (nP n nIdx : Nat) (ρ₀ : Nat → V) : List V :=
  (List.range nP).map fun m => frP n nIdx ρ₀ (nP - 1 - m)

/-- The unfolded function's value: the entry just below the parameters. -/
noncomputable def frR (nP n nIdx : Nat) (ρ₀ : Nat → V) : V := frP n nIdx ρ₀ nP

/-- The minors' values, in order. -/
noncomputable def frMsL (n nIdx : Nat) (ρ₀ : Nat → V) : List V := (List.range n).map (frMs n nIdx ρ₀)

/-- The frame below the unfolded function. -/
noncomputable def frBelow (nP n nIdx : Nat) (ρ₀ : Nat → V) : Nat → V :=
  shiftE (nIdx + n + 1 + nP + 1) 0 ρ₀

/-- The K-frame's `(p⃗, M, m⃗)` part as a spine. -/
noncomputable def frKSpine (nP n nIdx : Nat) (ρ₀ : Nat → V) : List V :=
  frameIdx (nP + 1 + n) (shiftE nIdx 0 ρ₀)

omit [SetTheory V] in
theorem frPs_length (nP n nIdx : Nat) (ρ₀ : Nat → V) : (frPs nP n nIdx ρ₀).length = nP := by
  simp [frPs]

omit [SetTheory V] in
theorem frMsL_length (n nIdx : Nat) (ρ₀ : Nat → V) : (frMsL n nIdx ρ₀).length = n := by
  simp [frMsL]

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

/-- The parameter variables at the payload frame (depth `D + 1`). -/
def paramsAtAV (nP n nIdx D : Nat) : List AVExpr :=
  (List.range nP).map fun m => .bvar (D + 1 + nIdx + n + 1 + (nP - 1 - m))

/-- The minor variables at the payload frame. -/
def minorsAtAV (n nIdx D : Nat) : List AVExpr :=
  (List.range n).map fun j => .bvar (D + 1 + nIdx + n - 1 - j)

/-- The ih argument for recursive field `i` at the payload frame: the
unfolded function at the parameters, the motive, the minors, the
field's index expressions (read at the payload's projections) and the
field. -/
def ihArgAV (nP n nIdx D i : Nat) (Eis : List AVExpr) : AVExpr :=
  AVExpr.mkAppN (.bvar (D + 1 + nIdx + n + 1 + nP))
    (paramsAtAV nP n nIdx D ++ [.bvar (D + 1 + nIdx + n)] ++ minorsAtAV n nIdx D ++
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
noncomputable def ihValsI (ρp : Nat → V) (rV M : V) (ps ms : List V) (rss : List (List Bool))
    (Eiss : List (List (List AVExpr))) (ar : Nat → Nat) (j : Nat) (y : V) : List V :=
  (recIdx (rss.getD j []) (ar j)).map fun i =>
    (ps ++ [M] ++ ms ++ (((Eiss.getD j []).getD i []).map (interp2 V (consList (projList i y) ρp)))
      ++ [projS i y]).foldl SetTheory.app rV

section IhFacts

variable {ℓ w u nP : Nat} {ρ₀ σ : Nat → V} {Fss Ess : List (List AVExpr)} {Ids : List AVExpr}
  {rss : List (List Bool)} {Eiss : List (List (List AVExpr))} {D : Nat}

/-- The parameter variables read to the parameters. -/
theorem paramsAtAV_interp (hfr : RecFrameS D ρ₀ σ) (y : V) :
    (paramsAtAV nP Fss.length Ids.length D).map (interp2 V (cons y σ))
      = frPs nP Fss.length Ids.length ρ₀ := by
  unfold paramsAtAV frPs
  rw [List.map_map]
  apply List.map_congr_left
  intro m _
  show interp2 V (cons y σ) (.bvar (D + 1 + Ids.length + Fss.length + 1 + (nP - 1 - m))) = _
  rw [interp2_bvar, show D + 1 + Ids.length + Fss.length + 1 + (nP - 1 - m)
      = (D + 1) + (Ids.length + Fss.length + 1 + (nP - 1 - m)) from by omega,
    (hfr.push y).apply]
  unfold frP
  rw [shiftE_zero]
  show ρ₀ _ = ρ₀ _
  congr 1
  omega

theorem minorsAtAV_interp (hfr : RecFrameS D ρ₀ σ) (y : V) :
    (minorsAtAV Fss.length Ids.length D).map (interp2 V (cons y σ))
      = frMsL Fss.length Ids.length ρ₀ := by
  unfold minorsAtAV frMsL
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  show interp2 V (cons y σ) (.bvar (D + 1 + Ids.length + Fss.length - 1 - j)) = _
  rw [interp2_bvar]
  exact (hfr.push y).minor (List.mem_range.mp hj)

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

end Lech.Semantics
