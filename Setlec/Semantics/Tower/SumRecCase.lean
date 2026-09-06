import Setlec.Semantics.Tower.SumMk
import Setlec.Semantics.Tower.TowerRec
import Setlec.Semantics.Univ

/-!
# The sum recursor's case split, spelled (task #175 sum-types, stage S4a)

The body of a direct sum's recursor cases on the major's tag with a
nested `Nat.rec` tower (`caseRecAV`): stage `j` is a `Nat.rec` whose
motive is `λ k, Π (y : case (drop j) k), M (mk (succ^j k) y)`, whose base
is constructor `j`'s branch `λ (y : T_j), m_j (y.0) … (y.(nF_j - 1))`
(the minor applied along the uniform projections of the payload —
`towerRec`'s witness, as in the structure route), and whose step
descends to stage `j + 1` on the predecessor tag; past the last
constructor the branch is the vacuous `λ (y : Empty), prf`.  Every
piece is spelled at an explicit depth `D` below the parameter frame
(`RecFrameS`), with the motive `M = bvar (D - 1)` and the minors
`m_j = bvar (D - 2 - j)`, so the nesting (two binders per stage) is
plain arithmetic and no substitution is ever performed.

Semantically the stage-`j` motive at the numeral `i` is the product
`piR ℓ (f (j + i)) (λ y, M (inj (j + i) y))` (`motSem`), the branch is
`baseSem`, and the three facts — membership in the motive, iota (the
selected branch), and grading — are one induction on the remaining
constructor count (`caseRec_facts`).  The minor space `minorSpC` is
the structure route's `minorSp` with an explicit conclusion function
(`ctorVal`: the injection of the tupler, the point at squash).

Two regime facts do the work: at a zero elimination level the whole
`Nat.rec` spine is the proof point (`natRecV2 0 = pt`), so its grading
is the trivial-slot spine (`mkAppN_ok2_of_pt_head`) and needs no
numeral; and at a squash instantiation the elimination level is zero
whenever there are constructors (the kernel's elimination restriction,
consumed as `hwl`), so the base branch is the point and inhabitation
is all that is asked.
-/

namespace Setlec.Semantics
open Setlec.SetModel

open SetTheory
open Setlec.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Numerals under successors -/

/-- `Nat.succ^j k`. -/
def succsAV : Nat → AVExpr → AVExpr
  | 0, k => k
  | j + 1, k => .app (.const .natSucc []) (succsAV j k)

theorem interp2_succsAV : ∀ (j : Nat) {k : AVExpr} {σ : Nat → V} {i : Nat},
    interp2 V σ k = vnat i → interp2 V σ (succsAV j k) = vnat (i + j)
  | 0, _, _, _, h => h
  | j + 1, k, σ, i, h => by
    show SetTheory.app (natSuccV2 V) (interp2 V σ (succsAV j k)) = vsucc (vnat (i + j))
    rw [interp2_succsAV j h, natSuccV2_app V (vnat_mem_omega _), natsucc_eq_vsucc]

theorem succsAV_ok2 : ∀ (j : Nat) {k : AVExpr} {σ : Nat → V} {i : Nat},
    AnnotOk2 V σ k → interp2 V σ k = vnat i → AnnotOk2 V σ (succsAV j k)
  | 0, _, _, _, hok, _ => hok
  | j + 1, k, σ, i, hok, h => by
    show AnnotOk2 V σ (.app (.const .natSucc []) (succsAV j k))
    rw [AnnotOk2_app]
    refine ⟨trivial, succsAV_ok2 j hok h, 1, omega, fun _ => omega, natSuccV2_mem V, ?_,
      fun h => absurd h Nat.one_ne_zero⟩
    rw [interp2_succsAV j h]
    exact vnat_mem_omega _

/-! ## The generalized minor space -/

/-- The minor space with an explicit conclusion: the Π-tower over the
field chain (bit `ℓ`) ending in the motive at `c` of the accumulated
tuple. -/
noncomputable def minorSpC (ℓ : Nat) (M : V) (c : List V → V) :
    List AVExpr → (Nat → V) → List V → V
  | [], _, acc => SetTheory.app M (c acc)
  | F :: Fs, ρf, acc => piR ℓ (interp2 V ρf F)
      fun a => minorSpC ℓ M c Fs (cons a ρf) (acc ++ [a])

/-- Constructor `j`'s value at a field tuple: the injection of the
tupler, the point at squash. -/
noncomputable def ctorVal (w j : Nat) (acc : List V) : V :=
  if w = 0 then pt else inj j (mkTower acc)

theorem minorSpC_zero_univZero {ℓ : Nat} {M : V} {c : List V → V} (h0 : ℓ = 0)
    (hM0 : ∀ y : V, SetTheory.app M y ∈ˢ (univZero : V)) :
    ∀ (Fs : List AVExpr) (ρf : Nat → V) (acc : List V),
      minorSpC ℓ M c Fs ρf acc ∈ˢ (univZero : V)
  | [], _, _ => hM0 _
  | _ :: _, _, _ => by
    show piR ℓ _ _ ∈ˢ _
    rw [h0]
    exact piR_zero_mem_univZero

/-- The graded fold of a minor-space member along a graded fitting
spine (`minorSp_spine` with the explicit conclusion). -/
theorem minorSpC_spine {ℓ : Nat} {M : V} {c : List V → V}
    (hM0 : ℓ = 0 → ∀ y : V, SetTheory.app M y ∈ˢ (univZero : V)) :
    ∀ {Fs args : List AVExpr} {ρf : Nat → V} {acc : List V} {f : AVExpr} {σ : Nat → V},
      AnnotOk2 V σ f → interp2 V σ f ∈ˢ minorSpC ℓ M c Fs ρf acc →
      ArgsOkFit σ args Fs ρf →
      AnnotOk2 V σ (AVExpr.mkAppN f args) ∧
        interp2 V σ (AVExpr.mkAppN f args)
          ∈ˢ SetTheory.app M (c (acc ++ args.map (interp2 V σ)))
  | [], [], _, acc, f, σ, hokf, hmf, _ => by
    refine ⟨hokf, ?_⟩
    show interp2 V σ f ∈ˢ SetTheory.app M (c (acc ++ []))
    rw [List.append_nil]
    exact hmf
  | [], _ :: _, _, _, _, _, _, _, hfit => hfit.elim
  | _ :: _, [], _, _, _, _, _, _, hfit => hfit.elim
  | F :: Fs, a :: args, ρf, acc, f, σ, hokf, hmf, hfit => by
    have hB0 : ℓ = 0 → ∀ x, x ∈ˢ interp2 V ρf F →
        minorSpC ℓ M c Fs (cons x ρf) (acc ++ [x]) ∈ˢ (univZero : V) :=
      fun h0 x _ => minorSpC_zero_univZero h0 (hM0 h0) Fs (cons x ρf) (acc ++ [x])
    have happ : SetTheory.app (interp2 V σ f) (interp2 V σ a)
        ∈ˢ minorSpC ℓ M c Fs (cons (interp2 V σ a) ρf) (acc ++ [interp2 V σ a]) :=
      app_mem_piR hmf hfit.2.1 hB0
    have hoka : AnnotOk2 V σ (.app f a) := by
      rw [AnnotOk2_app]
      exact ⟨hokf, hfit.1, ⟨ℓ, interp2 V ρf F, _, hmf, hfit.2.1, hB0⟩⟩
    have hres := minorSpC_spine hM0 (Fs := Fs) (args := args) (f := .app f a) hoka happ hfit.2.2
    refine ⟨hres.1, ?_⟩
    have hassoc : (acc ++ [interp2 V σ a]) ++ args.map (interp2 V σ)
        = acc ++ (a :: args).map (interp2 V σ) := by simp
    rw [hassoc] at hres
    exact hres.2

/-- At elimination level `0` the minor space is inhabited exactly when
the motive is inhabited at the conclusion along a fitting spine. -/
theorem minorSpC_zero_inhab {M : V} {c : List V → V} :
    ∀ {Fs : List AVExpr} {ρf : Nat → V} {acc : List V} {m : V} {as : List V},
      m ∈ˢ minorSpC 0 M c Fs ρf acc → SpineFit ρf Fs as →
      ∃ y, y ∈ˢ SetTheory.app M (c (acc ++ as))
  | [], _, acc, m, [], hm, _ => ⟨m, by simpa [minorSpC] using hm⟩
  | [], _, _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρf, acc, m, a :: as, hm, hsp => by
    have hm' : m ∈ˢ piR 0 (interp2 V ρf F)
      (fun a => minorSpC 0 M c Fs (cons a ρf) (acc ++ [a])) := hm
    rw [piR_zero] at hm'
    obtain ⟨y, hy⟩ := of_mem_truthVal hm' a hsp.1
    have h := minorSpC_zero_inhab hy hsp.2
    rwa [List.append_assoc, List.singleton_append] at h

/-! ## The frame -/

/-- The recursor body's frame invariant at depth `D` below the
parameter frame `ρp`: the motive sits at `D - 1`, minor `j` at
`D - 2 - j`. -/
structure RecFrameS (n D : Nat) (ρp : Nat → V) (M : V) (ms : Nat → V) (σ : Nat → V) : Prop where
  sh : shiftE D 0 σ = ρp
  hD : n + 2 ≤ D
  hM : σ (D - 1) = M
  hm : ∀ j, j < n → σ (D - 2 - j) = ms j

omit [SetTheory V] in
theorem RecFrameS.step {n D : Nat} {ρp : Nat → V} {M : V} {ms σ : Nat → V}
    (h : RecFrameS n D ρp M ms σ) (a b : V) :
    RecFrameS n (D + 2) ρp M ms (cons a (cons b σ)) where
  sh := by rw [shiftE_step, h.sh]
  hD := by have := h.hD; omega
  hM := by
    show cons a (cons b σ) (D + 2 - 1) = M
    rw [show D + 2 - 1 = (D - 1) + 2 from by have := h.hD; omega]
    exact h.hM
  hm := by
    intro j hj
    show cons a (cons b σ) (D + 2 - 2 - j) = ms j
    rw [show D + 2 - 2 - j = (D - 2 - j) + 2 from by have := h.hD; omega]
    exact h.hm j hj

omit [SetTheory V] in
/-- Under one binder the motive sits at `D`. -/
theorem RecFrameS.tag {n D : Nat} {ρp : Nat → V} {M : V} {ms σ : Nat → V}
    (h : RecFrameS n D ρp M ms σ) (k : V) : cons k σ D = M := by
  obtain ⟨D', rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by have := h.hD; omega⟩
  show cons k σ (D' + 1) = M
  rw [cons_succ]
  have := h.hM
  rwa [Nat.add_sub_cancel] at this

omit [SetTheory V] in
/-- Under two binders the motive sits at `D + 1`. -/
theorem RecFrameS.tag2 {n D : Nat} {ρp : Nat → V} {M : V} {ms σ : Nat → V}
    (h : RecFrameS n D ρp M ms σ) (y k : V) : cons y (cons k σ) (D + 1) = M := by
  show cons y (cons k σ) (D + 1) = M
  rw [show D + 1 = (D - 1) + 2 from by have := h.hD; omega]
  exact h.hM

omit [SetTheory V] in
/-- Under one binder minor `j` sits at `D - 1 - j`. -/
theorem RecFrameS.minor1 {n D : Nat} {ρp : Nat → V} {M : V} {ms σ : Nat → V}
    (h : RecFrameS n D ρp M ms σ) (y : V) {j : Nat} (hj : j < n) :
    cons y σ (D - 1 - j) = ms j := by
  rw [show D - 1 - j = (D - 2 - j) + 1 from by have := h.hD; omega]
  exact h.hm j hj

omit [SetTheory V] in
theorem RecFrameS.sh1 {n D : Nat} {ρp : Nat → V} {M : V} {ms σ : Nat → V}
    (h : RecFrameS n D ρp M ms σ) (k : V) : shiftE (D + 1) 0 (cons k σ) = ρp := by
  rw [shiftE_succ_cons, h.sh]

/-! ## The semantic pieces -/

/-- The stage-`j` motive at a tag: the product over the `(j + i)`-th
fibre into the motive at the injection. -/
noncomputable def motSem (ℓ w : Nat) (f : Nat → V) (M : V) (j : Nat) (k : V) : V :=
  natFibre (fun i => piR ℓ (f (j + i)) fun y => SetTheory.app M (injW w (j + i) y)) k

theorem motSem_vnat (ℓ w : Nat) (f : Nat → V) (M : V) (j i : Nat) :
    motSem ℓ w f M j (vnat i) = piR ℓ (f (j + i)) fun y => SetTheory.app M (injW w (j + i) y) :=
  natFibre_vnat _ i

/-- Constructor `j`'s branch: the minor applied along the payload's
projections. -/
noncomputable def baseSem (ℓ : Nat) (f : Nat → V) (ms : Nat → V) (nF j : Nat) : V :=
  lamR ℓ (f j) fun y => ((List.range nF).map fun i => projS i y).foldl SetTheory.app (ms j)

/-- The numeral `imax w ℓ`. -/
def imaxN (w ℓ : Nat) : Nat := if ℓ = 0 then 0 else Nat.max w ℓ

theorem imaxN_zero (w : Nat) : imaxN w 0 = 0 := if_pos rfl
theorem imaxN_pos (w : Nat) {ℓ : Nat} (hℓ : ℓ ≠ 0) : imaxN w ℓ = Nat.max w ℓ := if_neg hℓ
theorem imaxN_eq_zero_iff (w ℓ : Nat) : imaxN w ℓ = 0 ↔ ℓ = 0 := by
  unfold imaxN
  by_cases h : ℓ = 0
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun h' => absurd (Nat.le_zero.mp (h' ▸ Nat.le_max_right w ℓ)) h, fun h' => absurd h' h⟩

/-! ## The spelled pieces -/

/-- The stage-`j` motive body, under the motive's own tag binder
(`k = bvar 0`, `M = bvar D`), at depth `D`. -/
def caseMotiveBodyAV (ℓ w : Nat) (Fss : List (List AVExpr)) (D j : Nat) : AVExpr :=
  .pi w ℓ (caseAVAt w ((Fss.map (towerBodyAV w)).drop j) (D + 1) (.bvar 0))
    (.app (.bvar (D + 1)) (sumInjAtAV w Fss (D + 2) (succsAV j (.bvar 1)) (.bvar 0)))

/-- The stage-`j` motive. -/
def caseMotiveAV (ℓ w : Nat) (Fss : List (List AVExpr)) (D j : Nat) : AVExpr :=
  .lam (imaxN w ℓ + 1) natAV (caseMotiveBodyAV ℓ w Fss D j)

/-- Constructor `j`'s branch at depth `D`: `λ (y : T_j), m_j (y.0) …`. -/
def caseBaseAV (ℓ w : Nat) (Fss : List (List AVExpr)) (D j : Nat) : AVExpr :=
  .lam ℓ ((towerBodyAV w (Fss.getD j [])).liftN D 0)
    (AVExpr.mkAppN (.bvar (D - 1 - j))
      ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)))

/-- The case recursor from stage `j` with `r` constructors remaining,
at depth `D`, on the tag `k`. -/
def caseRecAV (ℓ w : Nat) (Fss : List (List AVExpr)) : Nat → Nat → Nat → AVExpr → AVExpr
  | 0, _, _, _ => .lam ℓ (.const .empty [w]) .prf
  | r + 1, D, j, k =>
    natRecAV (imaxN w ℓ) (caseMotiveAV ℓ w Fss D j) (caseBaseAV ℓ w Fss D j)
      (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ) (caseMotiveBodyAV ℓ w Fss D j)
        (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1))))
      k

/-! ## The hypotheses of the stage facts -/

/-- The semantic hypotheses of the recursor body: the motive in its
space, every minor in its space, the constructor chains graded, and
the elimination restriction. -/
structure RecHypS (ℓ w : Nat) (ρp : Nat → V) (Fss : List (List AVExpr)) (M : V)
    (ms : Nat → V) : Prop where
  hok : SumFieldsOkB w ρp Fss
  hM : M ∈ˢ piR (ℓ + 1) (sumSet w (sumFibre w ρp Fss)) fun _ => (univ ℓ : V)
  hms : ∀ j, j < Fss.length →
    ms j ∈ˢ minorSpC ℓ M (ctorVal w j) (Fss.getD j []) ρp []
  hwl : w = 0 → Fss.length = 0 ∨ ℓ = 0

namespace RecHypS

variable {ℓ w : Nat} {ρp : Nat → V} {Fss : List (List AVExpr)} {M : V} {ms : Nat → V}

/-- The motive's applications are truth values at a zero elimination
level (off the carrier the application is junk, which is empty). -/
theorem hM0 (h : RecHypS ℓ w ρp Fss M ms) (h0 : ℓ = 0) :
    ∀ y : V, SetTheory.app M y ∈ˢ (univZero : V) := by
  intro y
  by_cases hy : y ∈ˢ sumSet w (sumFibre w ρp Fss)
  · have hmem := app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hM hy
    rw [h0, univ_zero] at hmem
    exact hmem
  · rw [(mem_piR_pos (Nat.succ_ne_zero ℓ) h.hM).2.2.1 y hy, ← univ_zero]
    exact empty_mem_univ 0

/-- The motive at a carrier member lives in `univ ℓ`. -/
theorem hMapp (h : RecHypS ℓ w ρp Fss M ms) {y : V} (hy : y ∈ˢ sumSet w (sumFibre w ρp Fss)) :
    SetTheory.app M y ∈ˢ (univ ℓ : V) :=
  app_mem_piR_pos (Nat.succ_ne_zero ℓ) h.hM hy

/-- The fibres live in `univ w`. -/
theorem fibre_univ (h : RecHypS ℓ w ρp Fss M ms) (i : Nat) :
    sumFibre w ρp Fss i ∈ˢ (univ w : V) := by
  unfold sumFibre
  cases hi : Fss[i]? with
  | none => exact empty_mem_univ w
  | some Fs => exact towerSet_univ_of_okB (fun hw => (h.hok Fs (List.mem_of_getElem? hi)).toBound hw)

/-- The stage motive at a numeral lives in `univ (imax w ℓ)`. -/
theorem motSem_univ (h : RecHypS ℓ w ρp Fss M ms) (j i : Nat) :
    motSem ℓ w (sumFibre w ρp Fss) M j (vnat i) ∈ˢ (univ (imaxN w ℓ) : V) := by
  rw [motSem_vnat]
  have := piR_mem_univ (u := w) (v := ℓ) (h.fibre_univ (j + i))
    (fun y hy => h.hMapp (injW_mem hy))
  exact this

/-- At a zero elimination level the minors are the point. -/
theorem minor_pt (h : RecHypS ℓ w ρp Fss M ms) (h0 : ℓ = 0) {j : Nat} (hj : j < Fss.length) :
    ms j = pt :=
  eq_pt_of_mem_univZero (h0 ▸ minorSpC_zero_univZero h0 (h.hM0 h0) _ _ _) (h.hms j hj)

end RecHypS

/-! ## The motive's reading -/

/-- The stage-`j` motive body at a tag in `ω` reads to `motSem`, and
is graded. -/
theorem motiveBody_facts {ℓ w n D : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V}
    (hfr : RecFrameS n D ρp M ms σ) (hyp : RecHypS ℓ w ρp Fss M ms) (j : Nat) {k : V}
    (hk : k ∈ˢ (omega : V)) :
    interp2 V (cons k σ) (caseMotiveBodyAV ℓ w Fss D j) = motSem ℓ w (sumFibre w ρp Fss) M j k ∧
    AnnotOk2 V (cons k σ) (caseMotiveBodyAV ℓ w Fss D j) := by
  obtain ⟨i, rfl⟩ := mem_omega_iff.mp hk
  have hsh1 : shiftE (D + 1) 0 (cons (vnat i) σ) = ρp := hfr.sh1 _
  obtain ⟨hT, hokT⟩ := towers_facts hyp.hok
  have hTd : ∀ T ∈ (Fss.map (towerBodyAV w)).drop j, interp2 V ρp T ∈ˢ (univ w : V) :=
    fun T hT' => hT T (List.mem_of_mem_drop hT')
  have hokTd : ∀ T ∈ (Fss.map (towerBodyAV w)).drop j, AnnotOk2 V ρp T :=
    fun T hT' => hokT T (List.mem_of_mem_drop hT')
  -- the domain: the `(j + i)`-th fibre
  have hdom := caseAVAt_facts (w := w) (Ts := (Fss.map (towerBodyAV w)).drop j) (d := D + 1)
    (k := .bvar 0) (σ := cons (vnat i) σ) (by rw [hsh1]; exact hTd) (by rw [hsh1]; exact hokTd)
    trivial (by rw [interp2_bvar]; exact hk)
  rw [hsh1] at hdom
  have hdomv : interp2 V (cons (vnat i) σ)
      (caseAVAt w ((Fss.map (towerBodyAV w)).drop j) (D + 1) (.bvar 0))
      = sumFibre w ρp Fss (j + i) := by
    rw [hdom.2.1 i (by rw [interp2_bvar]; rfl)]
    unfold selFibre sumFibre
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop, List.getElem?_map]
    cases hj : Fss[j + i]? with
    | none => rfl
    | some Fs =>
      simp only [Option.map_some, Option.getD_some]
      exact towerBodyAV_interp (fun hw => (hyp.hok Fs (List.mem_of_getElem? hj)).toBound hw)
  -- the codomain: the motive at the injection
  have hsh2 : ∀ y : V, shiftE (D + 2) 0 (cons y (cons (vnat i) σ)) = ρp := fun y => by
    rw [shiftE_step, hfr.sh]
  have htag : ∀ y : V, interp2 V (cons y (cons (vnat i) σ)) (succsAV j (.bvar 1)) = vnat (i + j) :=
    fun y => interp2_succsAV j (by rw [interp2_bvar]; rfl)
  have hcod : ∀ y : V, y ∈ˢ sumFibre w ρp Fss (j + i) →
      interp2 V (cons y (cons (vnat i) σ))
          (.app (.bvar (D + 1)) (sumInjAtAV w Fss (D + 2) (succsAV j (.bvar 1)) (.bvar 0)))
        = SetTheory.app M (injW w (j + i) y) ∧
      AnnotOk2 V (cons y (cons (vnat i) σ))
        (.app (.bvar (D + 1)) (sumInjAtAV w Fss (D + 2) (succsAV j (.bvar 1)) (.bvar 0))) := by
    intro y hy
    have hpay : w ≠ 0 → interp2 V (cons y (cons (vnat i) σ)) (.bvar 0)
        ∈ˢ sumFibre w ρp Fss (i + j) := by
      intro _; rw [interp2_bvar, Nat.add_comm]; exact hy
    have hv := sumInjAtAV_interp (hsh2 y) hyp.hok (htag y) hpay
    rw [interp2_bvar] at hv
    have hij : i + j = j + i := Nat.add_comm i j
    refine ⟨?_, ?_⟩
    · rw [interp2_app, interp2_bvar, hfr.tag2, hv, hij, cons_zero]
    · rw [AnnotOk2_app]
      refine ⟨trivial, sumInjAtAV_ok2 (hsh2 y) hyp.hok (succsAV_ok2 j trivial
        (by rw [interp2_bvar]; rfl)) (htag y) trivial hpay,
        ℓ + 1, sumSet w (sumFibre w ρp Fss), fun _ => (univ ℓ : V), ?_, ?_,
        fun h => absurd h (Nat.succ_ne_zero _)⟩
      · rw [interp2_bvar, hfr.tag2]; exact hyp.hM
      · rw [hv, hij, cons_zero]; exact injW_mem hy
  refine ⟨?_, ?_⟩
  · show piR ℓ _ _ = _
    rw [motSem_vnat, hdomv]
    exact piR_congr fun y hy => (hcod y hy).1
  · show AnnotOk2 V (cons (vnat i) σ) (.pi w ℓ _ _)
    rw [AnnotOk2_pi]
    refine ⟨hdom.2.2, fun y hy => ?_⟩
    rw [hdomv] at hy
    exact (hcod y hy).2

/-- The stage-`j` motive: its value, its membership in the motive space,
its applications, its grading. -/
theorem motive_facts {ℓ w n D : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V}
    (hfr : RecFrameS n D ρp M ms σ) (hyp : RecHypS ℓ w ρp Fss M ms) (j : Nat) :
    interp2 V σ (caseMotiveAV ℓ w Fss D j)
        = lamR (imaxN w ℓ + 1) omega (motSem ℓ w (sumFibre w ρp Fss) M j) ∧
      interp2 V σ (caseMotiveAV ℓ w Fss D j) ∈ˢ natMotiveSpace V (imaxN w ℓ) ∧
      (∀ k, k ∈ˢ (omega : V) →
        SetTheory.app (interp2 V σ (caseMotiveAV ℓ w Fss D j)) k
          = motSem ℓ w (sumFibre w ρp Fss) M j k) ∧
      AnnotOk2 V σ (caseMotiveAV ℓ w Fss D j) := by
  have hv : interp2 V σ (caseMotiveAV ℓ w Fss D j)
      = lamR (imaxN w ℓ + 1) omega (motSem ℓ w (sumFibre w ρp Fss) M j) := by
    show lamR (imaxN w ℓ + 1) omega (fun k => interp2 V (cons k σ) (caseMotiveBodyAV ℓ w Fss D j)) = _
    exact lamR_congr fun k hk => (motiveBody_facts hfr hyp j hk).1
  have hmot : ∀ k, k ∈ˢ (omega : V) →
      motSem ℓ w (sumFibre w ρp Fss) M j k ∈ˢ (univ (imaxN w ℓ) : V) := by
    intro k hk
    obtain ⟨i, rfl⟩ := mem_omega_iff.mp hk
    exact hyp.motSem_univ j i
  refine ⟨hv, ?_, ?_, ?_⟩
  · rw [hv]
    exact lamR_mem_zero_agree
      ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => absurd h (Nat.succ_ne_zero _)⟩ hmot
  · intro k hk
    rw [hv]
    exact app_lamR_pos (Nat.succ_ne_zero _) hk
  · show AnnotOk2 V σ (.lam (imaxN w ℓ + 1) natAV (caseMotiveBodyAV ℓ w Fss D j))
    rw [AnnotOk2_lam]
    refine ⟨trivial, fun k hk => (motiveBody_facts hfr hyp j hk).2,
      fun _ => (univ (imaxN w ℓ) : V), fun k hk => ?_, fun h => absurd h (Nat.succ_ne_zero _)⟩
    rw [(motiveBody_facts hfr hyp j hk).1]
    exact hmot k hk

/-! ## The base branch -/

/-- Constructor `j`'s branch: its value, its grading, its membership
in the stage motive at the numeral `0`. -/
theorem base_facts {ℓ w n D : Nat} {ρp σ : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V} (hn : n = Fss.length)
    (hfr : RecFrameS n D ρp M ms σ) (hyp : RecHypS ℓ w ρp Fss M ms) {j : Nat} (hj : j < n) :
    interp2 V σ (caseBaseAV ℓ w Fss D j)
        = baseSem ℓ (sumFibre w ρp Fss) ms (Fss.getD j []).length j ∧
      AnnotOk2 V σ (caseBaseAV ℓ w Fss D j) ∧
      interp2 V σ (caseBaseAV ℓ w Fss D j)
        ∈ˢ motSem ℓ w (sumFibre w ρp Fss) M j (vnat 0) := by
  have hjF : Fss[j]? = some (Fss.getD j []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hokF : FieldsOkB w ρp (Fss.getD j []) := hyp.hok _ (List.mem_of_getElem? hjF)
  have hfj : sumFibre w ρp Fss j = towerSet w (teleOfFields ρp (Fss.getD j [])) :=
    sumFibre_of_getElem? hjF
  have hdomv : interp2 V σ ((towerBodyAV w (Fss.getD j [])).liftN D 0)
      = towerSet w (teleOfFields ρp (Fss.getD j [])) := by
    rw [interp2_liftN V D _ 0 σ, hfr.sh]
    exact towerBodyAV_interp (fun hw => hokF.toBound hw)
  have hokdom : AnnotOk2 V σ ((towerBodyAV w (Fss.getD j [])).liftN D 0) := by
    rw [AnnotOk2_liftN, hfr.sh]
    exact towerBodyAV_ok2 hokF
  have hminor : ∀ y : V, cons y σ (D - 1 - j) = ms j := fun y => hfr.minor1 y (hn ▸ hj)
  have hms := hyp.hms j (hn ▸ hj)
  -- the body at a payload: the minor's fold along the projections
  have hbody : ∀ y : V, y ∈ˢ towerSet w (teleOfFields ρp (Fss.getD j [])) →
      AnnotOk2 V (cons y σ) (AVExpr.mkAppN (.bvar (D - 1 - j))
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0))) ∧
      interp2 V (cons y σ) (AVExpr.mkAppN (.bvar (D - 1 - j))
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)))
        = ((List.range (Fss.getD j []).length).map fun i => projS i y).foldl
            SetTheory.app (ms j) ∧
      interp2 V (cons y σ) (AVExpr.mkAppN (.bvar (D - 1 - j))
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)))
        ∈ˢ SetTheory.app M (injW w j y) := by
    intro y hy
    have hval : interp2 V (cons y σ) (AVExpr.mkAppN (.bvar (D - 1 - j))
        ((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)))
        = ((List.range (Fss.getD j []).length).map fun i => projS i y).foldl
            SetTheory.app (ms j) := by
      rw [interp2_mkAppN, List.foldl_map, List.foldl_map, interp2_bvar, hminor]
      congr 1
      funext acc i
      rw [projAV_interp, interp2_bvar]
      rfl
    by_cases hw : w = 0
    · -- squash: the elimination level is zero (constructors exist), the
      -- minor is the point, the payload is the point
      subst hw
      have h0 : ℓ = 0 := (hyp.hwl rfl).resolve_left (by omega)
      have hmpt : ms j = pt := hyp.minor_pt h0 (hn ▸ hj)
      obtain ⟨rfl, as, hfit⟩ := towerSet_zero_elim _ hy
      have hpt := mkAppN_ok2_pt (V := V)
        (args := (List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0))
        (f := .bvar (D - 1 - j)) (σ := cons pt σ)
        (by simp) (by rw [interp2_bvar, hminor, hmpt])
        (fun a ha => by
          obtain ⟨i, -, rfl⟩ := List.mem_map.mp ha
          exact projAV_ok2_pt i (by simp) (by rw [interp2_bvar]; rfl))
      refine ⟨hpt.1, hval, ?_⟩
      rw [hpt.2, injW_zero]
      obtain ⟨v, hv⟩ := minorSpC_zero_inhab (h0 ▸ hms) (fitsS_teleOfFields.mp hfit)
      have hv' : v = pt := eq_pt_of_mem_univZero (hyp.hM0 h0 _) hv
      subst hv'
      simpa [ctorVal] using hv
    · -- graph: the projection spine fits, the fold lands at the injection
      have hbnd : FieldsBound w ρp (Fss.getD j []) := hokF.toBound hw
      have hfit := argsOkFit_projSpine (Fs := Fss.getD j []) (ρp := ρp) (σ := cons y σ)
        (by rw [cons_zero]; exact hy) hbnd (Fss.getD j []).length 0 (Nat.zero_add _)
      rw [← List.range_eq_range', List.drop_zero] at hfit
      have hsp := minorSpC_spine (V := V) (hyp.hM0)
        (Fs := Fss.getD j []) (args := (List.range (Fss.getD j []).length).map
          fun i => projAV i (.bvar 0)) (ρf := ρp) (acc := []) (f := .bvar (D - 1 - j))
        (σ := cons y σ) (by simp) (by rw [interp2_bvar, hminor]; exact hms)
        (by rw [cons_zero, projList_eq_map_range] at hfit; simpa [consList_nil] using hfit)
      refine ⟨hsp.1, hval, ?_⟩
      have hconv : ctorVal w j ([] ++ ((List.range (Fss.getD j []).length).map
          fun i => projAV i (.bvar 0)).map (interp2 V (cons y σ))) = injW w j y := by
        have hmap : (((List.range (Fss.getD j []).length).map fun i => projAV i (.bvar 0)).map
            (interp2 V (cons y σ))) = projList (Fss.getD j []).length y := by
          rw [List.map_map, projList_eq_map_range]
          apply List.map_congr_left
          intro i _
          show interp2 V _ (projAV i (.bvar 0)) = projS i y
          rw [projAV_interp, interp2_bvar]
          rfl
        rw [List.nil_append, hmap, ctorVal, if_neg hw, injW_pos hw,
          ← (towerSet_elim_teleOfFields hw hy).2]
      have h := hsp.2
      rw [hconv] at h
      exact h
  refine ⟨?_, ?_, ?_⟩
  · show lamR ℓ _ _ = _
    unfold baseSem
    rw [hdomv, hfj]
    exact lamR_congr fun y hy => (hbody y hy).2.1
  · show AnnotOk2 V σ (.lam ℓ _ _)
    rw [AnnotOk2_lam]
    refine ⟨hokdom, fun y hy => (hbody y (hdomv ▸ hy)).1,
      fun y => SetTheory.app M (injW w j y), fun y hy => (hbody y (hdomv ▸ hy)).2.2,
      fun h0 y hy => ?_⟩
    have := hyp.hMapp (injW_mem (f := sumFibre w ρp Fss) (i := j) (by rw [hfj]; exact hdomv ▸ hy))
    rwa [h0, univ_zero] at this
  · show lamR ℓ _ _ ∈ˢ _
    rw [motSem_vnat, Nat.add_zero, hfj, hdomv]
    exact lamR_mem fun y hy => (hbody y hy).2.2

/-! ## The case recursor -/

/-- **The case recursor's facts**, one induction on the remaining
constructor count: membership in the stage motive at every tag in `ω`,
iota (the tag `i < r` selects constructor `j + i`'s branch), and the
grading (at a zero elimination level from the point-headed spine, so
no numeral is needed; above it from `Nat.rec`'s own chain). -/
theorem caseRec_facts {ℓ w n : Nat} {ρp : Nat → V} {Fss : List (List AVExpr)} {M : V}
    {ms : Nat → V} (hn : n = Fss.length) (hyp : RecHypS ℓ w ρp Fss M ms) :
    ∀ (r : Nat) {D j : Nat} {σ : Nat → V} {k : AVExpr},
      RecFrameS n D ρp M ms σ → j + r = n →
      ((interp2 V σ k ∈ˢ (omega : V) →
        interp2 V σ (caseRecAV ℓ w Fss r D j k)
          ∈ˢ motSem ℓ w (sumFibre w ρp Fss) M j (interp2 V σ k) ∧
        ∀ i, interp2 V σ k = vnat i → i < r →
          interp2 V σ (caseRecAV ℓ w Fss r D j k)
            = baseSem ℓ (sumFibre w ρp Fss) ms (Fss.getD (j + i) []).length (j + i)) ∧
      (AnnotOk2 V σ k → (ℓ ≠ 0 → interp2 V σ k ∈ˢ (omega : V)) →
        AnnotOk2 V σ (caseRecAV ℓ w Fss r D j k)))
  | 0, D, j, σ, k, hfr, hjr => by
    refine ⟨fun hk => ⟨?_, fun i _ hi => absurd hi (Nat.not_lt_zero i)⟩, fun _ _ => ?_⟩
    · obtain ⟨i, hki⟩ := mem_omega_iff.mp hk
      rw [hki, motSem_vnat]
      show lamR ℓ (empty : V) _ ∈ˢ _
      rw [sumFibre_of_ge (by omega)]
      exact lamR_mem fun _ hx => absurd hx (not_mem_empty _)
    · show AnnotOk2 V σ (.lam ℓ (.const .empty [w]) .prf)
      rw [AnnotOk2_lam]
      exact ⟨trivial, fun _ hx => absurd hx (not_mem_empty _), fun _ => unitSet,
        fun _ hx => absurd hx (not_mem_empty _), fun _ _ hx => absurd hx (not_mem_empty _)⟩
  | r + 1, D, j, σ, k, hfr, hjr => by
    have hjn : j < n := by omega
    obtain ⟨hMv, hMsp, hMapp, hMok⟩ := motive_facts hfr hyp j
    obtain ⟨hzv, hzok, hzm⟩ := base_facts hn hfr hyp hjn
    have hz : interp2 V σ (caseBaseAV ℓ w Fss D j)
        ∈ˢ SetTheory.app (interp2 V σ (caseMotiveAV ℓ w Fss D j)) natzero := by
      rw [hMapp natzero natzero_mem, natzero_eq_vnat]; exact hzm
    -- the step's inner recursor at every step frame
    have hinner : ∀ (a b : V), b ∈ˢ (omega : V) →
        interp2 V (cons a (cons b σ)) (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1))
          ∈ˢ motSem ℓ w (sumFibre w ρp Fss) M (j + 1) b ∧
        (∀ i, b = vnat i → i < r →
          interp2 V (cons a (cons b σ)) (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1))
            = baseSem ℓ (sumFibre w ρp Fss) ms (Fss.getD (j + 1 + i) []).length (j + 1 + i)) ∧
        AnnotOk2 V (cons a (cons b σ)) (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1)) := by
      intro a b hb
      have h := caseRec_facts hn hyp r (D := D + 2) (j := j + 1) (σ := cons a (cons b σ))
        (k := .bvar 1) (hfr.step a b) (by omega)
      have hb' : interp2 V (cons a (cons b σ)) (.bvar 1) ∈ˢ (omega : V) := by
        rw [interp2_bvar]; exact hb
      refine ⟨(h.1 hb').1, fun i hi hir => (h.1 hb').2 i (by rw [interp2_bvar]; exact hi) hir,
        h.2 trivial (fun _ => hb')⟩
    -- the motive at a successor is the next stage's motive
    have hsucc : ∀ (i : Nat), motSem ℓ w (sumFibre w ρp Fss) M j (vnat (i + 1))
        = motSem ℓ w (sumFibre w ρp Fss) M (j + 1) (vnat i) := by
      intro i
      rw [motSem_vnat, motSem_vnat, show j + (i + 1) = j + 1 + i from by omega]
    -- the step: its value and its membership in the step space
    have hsv : interp2 V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ) (caseMotiveBodyAV ℓ w Fss D j)
          (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1))))
        = lamR (imaxN w ℓ) omega fun b =>
            lamR (imaxN w ℓ) (interp2 V (cons b σ) (caseMotiveBodyAV ℓ w Fss D j)) fun a =>
              interp2 V (cons a (cons b σ)) (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1)) := rfl
    have hs : interp2 V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ) (caseMotiveBodyAV ℓ w Fss D j)
          (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1))))
        ∈ˢ natStepSpace2 V (imaxN w ℓ) (interp2 V σ (caseMotiveAV ℓ w Fss D j)) := by
      rw [hsv]
      unfold natStepSpace2
      refine lamR_mem fun b hb => ?_
      rw [hMapp b hb, hMapp (natsucc b) (natsucc_mem hb), (motiveBody_facts hfr hyp j hb).1]
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
      have hiter : ∀ i', natIter (interp2 V σ (caseBaseAV ℓ w Fss D j))
          (interp2 V σ (.lam (imaxN w ℓ) natAV (.lam (imaxN w ℓ) (caseMotiveBodyAV ℓ w Fss D j)
            (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1))))) i'
          ∈ˢ motSem ℓ w (sumFibre w ρp Fss) M j (vnat i') := by
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
          unfold baseSem
          rw [h0, lamR_zero]
        · have hz' : imaxN w ℓ ≠ 0 := fun h => h0 ((imaxN_eq_zero_iff w ℓ).mp h)
          rw [hsv, app_lamR_pos hz' (vnat_mem_omega i),
            app_lamR_pos hz' (by
              rw [(motiveBody_facts hfr hyp j (vnat_mem_omega i)).1]
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
              (motSem ℓ w (sumFibre w ρp Fss) M j b)
              (fun _ => motSem ℓ w (sumFibre w ρp Fss) M j (natsucc b)),
            fun b hb => ?_, fun _ b hb => by rw [hz']; exact piR_zero_mem_univZero⟩
          · rw [AnnotOk2_lam]
            refine ⟨(motiveBody_facts hfr hyp j hb).2, fun a _ => (hinner a b hb).2.2,
              fun _ => motSem ℓ w (sumFibre w ρp Fss) M j (natsucc b), fun a _ => ?_,
              fun _ a _ => ?_⟩
            · obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
              rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
              exact (hinner a _ hb).1
            · obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
              rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc,
                motSem_vnat, h0]
              exact piR_zero_mem_univZero
          · show lamR (imaxN w ℓ) (interp2 V (cons b σ) (caseMotiveBodyAV ℓ w Fss D j))
              (fun a => interp2 V (cons a (cons b σ))
                (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1))) ∈ˢ piR (imaxN w ℓ) _ _
            rw [(motiveBody_facts hfr hyp j hb).1]
            refine lamR_mem fun a _ => ?_
            obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
            rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
            exact (hinner a _ hb).1
        · exact hokk
      · -- `Nat.rec`'s own chain
        refine natRecAV_ok2 hMok hzok ?_ hokk hMsp hz hs (hkω h0)
        rw [AnnotOk2_lam]
        refine ⟨trivial, fun b hb => ?_, fun b => piR (imaxN w ℓ)
            (motSem ℓ w (sumFibre w ρp Fss) M j b)
            (fun _ => motSem ℓ w (sumFibre w ρp Fss) M j (natsucc b)),
          fun b hb => ?_, fun h => absurd ((imaxN_eq_zero_iff w ℓ).mp h) h0⟩
        · rw [AnnotOk2_lam]
          refine ⟨(motiveBody_facts hfr hyp j hb).2, fun a _ => (hinner a b hb).2.2,
            fun _ => motSem ℓ w (sumFibre w ρp Fss) M j (natsucc b), fun a _ => ?_,
            fun h => absurd ((imaxN_eq_zero_iff w ℓ).mp h) h0⟩
          obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
          rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
          exact (hinner a _ hb).1
        · show lamR (imaxN w ℓ) (interp2 V (cons b σ) (caseMotiveBodyAV ℓ w Fss D j))
            (fun a => interp2 V (cons a (cons b σ))
              (caseRecAV ℓ w Fss r (D + 2) (j + 1) (.bvar 1))) ∈ˢ piR (imaxN w ℓ) _ _
          rw [(motiveBody_facts hfr hyp j hb).1]
          refine lamR_mem fun a _ => ?_
          obtain ⟨i, rfl⟩ := mem_omega_iff.mp hb
          rw [natsucc_eq_vsucc, show vsucc (vnat i) = vnat (i + 1) from rfl, hsucc]
          exact (hinner a _ hb).1

/-- At a zero elimination level the case recursor with constructors
remaining is the point. -/
theorem caseRec_zero {ℓ w : Nat} (h0 : ℓ = 0) (Fss : List (List AVExpr)) (r D j : Nat)
    (k : AVExpr) (σ : Nat → V) :
    interp2 V σ (caseRecAV ℓ w Fss (r + 1) D j k) = pt := by
  show interp2 V σ (natRecAV (imaxN w ℓ) _ _ _ k) = pt
  rw [interp2_natRecAV_raw, (imaxN_eq_zero_iff w ℓ).mpr h0, natRecV2, lamR_zero, app_pt, app_pt,
    app_pt, app_pt]

end Setlec.Semantics
