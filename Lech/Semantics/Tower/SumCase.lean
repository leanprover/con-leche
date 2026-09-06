import Lech.Semantics.Tower.TowerLeaf
import Lech.SetModel.TaggedSum

/-!
# The numeral case split, spelled (task #175 sum-types, stage S1)

The tagged sum's tag is a `Nat` numeral and its case split is
`Nat.rec`: this module spells both in the `AVExpr` alphabet and reads
them back.

* `numeralAV i` — `Nat.succ^i Nat.zero`, reading to `vnat i`;
* `natRecAV u M z s k` — the four-application spine of `Nat.rec.{u}`,
  reading to `natrec ⟦z⟧ ⟦s⟧ ⟦k⟧` under the motive/base/step
  memberships (`natRecV2_app`), graded from the same memberships
  (`natRecAV_ok2` — the spine's four slots are `Nat.rec`'s own product
  chain, both regimes);
* `caseAVAt w Ts d k` — **the fibre selector**: the nested `Nat.rec`
  tower with the constant motive `λ _ : Nat, Sort w` that picks the
  `i`-th of the type spellings `Ts` at the numeral `i` and `Empty`
  beyond.  The spellings are scoped `d` binders below the point of use
  (they are lifted by `d` at each use; the nesting adds two binders per
  level), so the reading is stated at the retracted environment
  `shiftE d 0 σ` — no capture-avoiding substitution anywhere.
-/

namespace Lech.Semantics
open Lech.SetModel

open SetTheory
open Lech.SetTheory.Tower
open Lech.TT (VExpr)

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The numerals -/

/-- `Nat`, spelled. -/
def natAV : AVExpr := .const .nat []

/-- `Nat.succ^i Nat.zero`. -/
def numeralAV : Nat → AVExpr
  | 0 => .const .natZero []
  | i + 1 => .app (.const .natSucc []) (numeralAV i)

theorem natzero_eq_vnat : (natzero : V) = vnat 0 := by
  unfold natzero; rfl

theorem natsucc_eq_vsucc (n : V) : natsucc n = vsucc n := by
  unfold natsucc; rfl

@[simp] theorem interp2_natAV (ρ : Nat → V) : interp2 V ρ natAV = omega := rfl

theorem interp2_numeralAV : ∀ (i : Nat) (ρ : Nat → V), interp2 V ρ (numeralAV i) = vnat i
  | 0, _ => natzero_eq_vnat
  | i + 1, ρ => by
    show SetTheory.app (natSuccV2 V) (interp2 V ρ (numeralAV i)) = vsucc (vnat i)
    rw [interp2_numeralAV i ρ, natSuccV2_app V (vnat_mem_omega i), natsucc_eq_vsucc]

theorem numeralAV_ok2 : ∀ (i : Nat) (ρ : Nat → V), AnnotOk2 V ρ (numeralAV i)
  | 0, _ => by simp [numeralAV]
  | i + 1, ρ => by
    show AnnotOk2 V ρ (.app (.const .natSucc []) (numeralAV i))
    rw [AnnotOk2_app]
    refine ⟨trivial, numeralAV_ok2 i ρ, 1, omega, fun _ => omega, natSuccV2_mem V, ?_,
      fun h => absurd h Nat.one_ne_zero⟩
    rw [interp2_numeralAV]
    exact vnat_mem_omega i

theorem numeralAV_liftN (i n k : Nat) : (numeralAV i).liftN n k = numeralAV i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [numeralAV, AVExpr.liftN_app, ih]; rfl

theorem numeralAV_erase_below (i k : Nat) : VExpr.bvarsBelow k (numeralAV i).erase := by
  induction i with
  | zero => trivial
  | succ i ih => exact ⟨trivial, ih⟩

/-! ## A proof-point-headed spine is graded -/

/-- An application spine whose head reads to the point is graded from
its arguments' gradings alone, and reads to the point: every slot is
the trivial product over the argument's singleton. -/
theorem mkAppN_ok2_of_pt_head :
    ∀ {args : List AVExpr} {f : AVExpr} {σ : Nat → V},
      AnnotOk2 V σ f → interp2 V σ f = pt → (∀ a ∈ args, AnnotOk2 V σ a) →
      AnnotOk2 V σ (AVExpr.mkAppN f args) ∧ interp2 V σ (AVExpr.mkAppN f args) = pt
  | [], _, _, hf, hpt, _ => ⟨hf, hpt⟩
  | a :: args, f, σ, hf, hpt, hargs => by
    rw [AVExpr.mkAppN_cons]
    refine mkAppN_ok2_of_pt_head ?_ ?_ fun a' ha' => hargs a' (.tail _ ha')
    · rw [AnnotOk2_app]
      refine ⟨hf, hargs a (.head _), 0, sing (interp2 V σ a), fun _ => unitSet, ?_,
        mem_sing.mpr rfl, fun _ _ _ => by rw [← univ_zero]; exact unitSet_mem_univ 0⟩
      rw [hpt]
      exact pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitSet⟩
    · rw [interp2_app, hpt, app_pt]

/-! ## `Nat.rec` spines -/

/-- The `Nat.rec.{u}` spine. -/
def natRecAV (u : Nat) (M z s k : AVExpr) : AVExpr :=
  AVExpr.mkAppN (.const .natRec [u]) [M, z, s, k]

theorem interp2_natRecAV_raw (u : Nat) (M z s k : AVExpr) (σ : Nat → V) :
    interp2 V σ (natRecAV u M z s k)
      = SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (natRecV2 V u)
          (interp2 V σ M)) (interp2 V σ z)) (interp2 V σ s)) (interp2 V σ k) := rfl

/-- The spine reads to `natrec` (`natRecV2_app`). -/
theorem interp2_natRecAV {u : Nat} {M z s k : AVExpr} {σ : Nat → V}
    (hM : interp2 V σ M ∈ˢ natMotiveSpace V u)
    (hz : interp2 V σ z ∈ˢ SetTheory.app (interp2 V σ M) natzero)
    (hs : interp2 V σ s ∈ˢ natStepSpace2 V u (interp2 V σ M))
    (hk : interp2 V σ k ∈ˢ (omega : V)) :
    interp2 V σ (natRecAV u M z s k) = natrec (interp2 V σ z) (interp2 V σ s) (interp2 V σ k) := by
  rw [interp2_natRecAV_raw]
  exact natRecV2_app V hM hz hs hk

/-- The spine inhabits the motive at the numeral. -/
theorem natRecAV_mem {u : Nat} {M z s k : AVExpr} {σ : Nat → V}
    (hM : interp2 V σ M ∈ˢ natMotiveSpace V u)
    (hz : interp2 V σ z ∈ˢ SetTheory.app (interp2 V σ M) natzero)
    (hs : interp2 V σ s ∈ˢ natStepSpace2 V u (interp2 V σ M))
    (hk : interp2 V σ k ∈ˢ (omega : V)) :
    interp2 V σ (natRecAV u M z s k) ∈ˢ SetTheory.app (interp2 V σ M) (interp2 V σ k) := by
  rw [interp2_natRecAV hM hz hs hk]
  exact natRecV2_mem_fibre V hM hz hs hk

/-- **The spine is graded**, both regimes: the four slots are
`Nat.rec`'s own product chain, with the squash-side fibre conditions
landing on `piR_zero_mem_univZero` and the motive's own fibres. -/
theorem natRecAV_ok2 {u : Nat} {M z s k : AVExpr} {σ : Nat → V}
    (hokM : AnnotOk2 V σ M) (hokz : AnnotOk2 V σ z) (hoks : AnnotOk2 V σ s)
    (hokk : AnnotOk2 V σ k)
    (hM : interp2 V σ M ∈ˢ natMotiveSpace V u)
    (hz : interp2 V σ z ∈ˢ SetTheory.app (interp2 V σ M) natzero)
    (hs : interp2 V σ s ∈ˢ natStepSpace2 V u (interp2 V σ M))
    (hk : interp2 V σ k ∈ˢ (omega : V)) :
    AnnotOk2 V σ (natRecAV u M z s k) := by
  have hbv : interp2 V σ (.const .natRec [u]) = natRecV2 V u := rfl
  have h0 : natRecV2 V u ∈ˢ piR u (natMotiveSpace V u) fun M =>
      piR u (SetTheory.app M natzero) fun _ =>
        piR u (natStepSpace2 V u M) fun _ => piR u omega fun n => SetTheory.app M n := by
    unfold natRecV2
    exact lamR_mem fun M hM => lamR_mem fun z hz => lamR_mem fun s hs =>
      lamR_mem fun n hn => natRecV2_mem_fibre V hM hz hs hn
  have hz1 : u = 0 → ∀ M', M' ∈ˢ natMotiveSpace V u →
      (piR u (SetTheory.app M' natzero) fun _ =>
        piR u (natStepSpace2 V u M') fun _ => piR u omega fun n => SetTheory.app M' n)
        ∈ˢ (univZero : V) := by
    intro h0 _ _; subst h0; exact piR_zero_mem_univZero
  have h1 := app_mem_piR h0 hM hz1
  have hz2 : u = 0 → ∀ z', z' ∈ˢ SetTheory.app (interp2 V σ M) natzero →
      (piR u (natStepSpace2 V u (interp2 V σ M)) fun _ =>
        piR u omega fun n => SetTheory.app (interp2 V σ M) n) ∈ˢ (univZero : V) := by
    intro h0 _ _; subst h0; exact piR_zero_mem_univZero
  have h2 := app_mem_piR h1 hz hz2
  have hz3 : u = 0 → ∀ s', s' ∈ˢ natStepSpace2 V u (interp2 V σ M) →
      (piR u omega fun n => SetTheory.app (interp2 V σ M) n) ∈ˢ (univZero : V) := by
    intro h0 _ _; subst h0; exact piR_zero_mem_univZero
  have h3 := app_mem_piR h2 hs hz3
  have hz4 : u = 0 → ∀ n, n ∈ˢ (omega : V) →
      SetTheory.app (interp2 V σ M) n ∈ˢ (univZero : V) := by
    intro h0 n hn
    have := natMotive_apply V hM hn
    rw [h0, univ_zero] at this
    exact this
  show AnnotOk2 V σ (.app (.app (.app (.app (.const .natRec [u]) M) z) s) k)
  rw [AnnotOk2_app]
  refine ⟨?_, hokk, u, omega, fun n => SetTheory.app (interp2 V σ M) n, ?_, hk, hz4⟩
  · rw [AnnotOk2_app]
    refine ⟨?_, hoks, u, natStepSpace2 V u (interp2 V σ M), _, ?_, hs, hz3⟩
    · rw [AnnotOk2_app]
      refine ⟨?_, hokz, u, SetTheory.app (interp2 V σ M) natzero, _, ?_, hz, hz2⟩
      · rw [AnnotOk2_app]
        exact ⟨trivial, hokM, u, natMotiveSpace V u, _, hbv ▸ h0, hM, hz1⟩
      · show SetTheory.app (interp2 V σ (.const .natRec [u])) (interp2 V σ M) ∈ˢ _
        rw [hbv]; exact h1
    · show SetTheory.app (SetTheory.app (interp2 V σ (.const .natRec [u])) (interp2 V σ M))
        (interp2 V σ z) ∈ˢ _
      rw [hbv]; exact h2
  · show SetTheory.app (SetTheory.app (SetTheory.app (interp2 V σ (.const .natRec [u]))
      (interp2 V σ M)) (interp2 V σ z)) (interp2 V σ s) ∈ˢ _
    rw [hbv]; exact h3

/-! ## The fibre selector -/

/-- The constant motive `λ _ : Nat, Sort w` (its body's type is
`Sort (w + 1)`, hence the bit). -/
def natSortMotiveAV (w : Nat) : AVExpr := .lam (w + 1) natAV (.sort w)

theorem interp2_natSortMotiveAV (w : Nat) (σ : Nat → V) :
    interp2 V σ (natSortMotiveAV w) = lamR (w + 1) omega fun _ => univ w := rfl

theorem natSortMotiveAV_mem (w : Nat) (σ : Nat → V) :
    interp2 V σ (natSortMotiveAV w) ∈ˢ natMotiveSpace V (w + 1) := by
  rw [interp2_natSortMotiveAV]
  exact lamR_mem_zero_agree
    ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => absurd h (Nat.succ_ne_zero _)⟩
    fun _ _ => univ_mem_univ w

theorem natSortMotiveAV_app (w : Nat) (σ : Nat → V) {n : V} (hn : n ∈ˢ (omega : V)) :
    SetTheory.app (interp2 V σ (natSortMotiveAV w)) n = univ w := by
  rw [interp2_natSortMotiveAV]
  exact app_lamR_pos (Nat.succ_ne_zero w) hn

theorem natSortMotiveAV_ok2 (w : Nat) (σ : Nat → V) : AnnotOk2 V σ (natSortMotiveAV w) := by
  show AnnotOk2 V σ (.lam (w + 1) natAV (.sort w))
  rw [AnnotOk2_lam]
  exact ⟨trivial, fun _ _ => trivial, fun _ => univ (w + 1), fun _ _ => univ_mem_univ w,
    fun h => absurd h (Nat.succ_ne_zero _)⟩

/-- **The fibre selector**: the type spellings `Ts` are scoped `d`
binders below; the `i`-th is selected at the numeral `i`, `Empty`
beyond.  Each nesting level adds the step's two binders. -/
def caseAVAt (w : Nat) : List AVExpr → Nat → AVExpr → AVExpr
  | [], _, _ => .const .empty [w]
  | T :: Ts, d, k =>
    natRecAV (w + 1) (natSortMotiveAV w) (T.liftN d 0)
      (.lam (w + 1) natAV (.lam (w + 1) (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1)))) k

omit [SetTheory V] in
/-- The environment retraction across the step's two binders. -/
theorem shiftE_step (d : Nat) (σ : Nat → V) (a b : V) :
    shiftE (d + 2) 0 (cons a (cons b σ)) = shiftE d 0 σ := by
  rw [show d + 2 = (d + 1) + 1 from rfl, shiftE_succ_cons, shiftE_succ_cons]

/-- The selected fibre, semantically: the `i`-th reading, `empty`
beyond. -/
noncomputable def selFibre (ρ : Nat → V) (Ts : List AVExpr) (i : Nat) : V :=
  (Ts.map (interp2 V ρ)).getD i empty

theorem selFibre_nil (ρ : Nat → V) (i : Nat) : selFibre ρ ([] : List AVExpr) i = empty := rfl
theorem selFibre_cons_zero (ρ : Nat → V) (T : AVExpr) (Ts : List AVExpr) :
    selFibre ρ (T :: Ts) 0 = interp2 V ρ T := rfl
theorem selFibre_cons_succ (ρ : Nat → V) (T : AVExpr) (Ts : List AVExpr) (i : Nat) :
    selFibre ρ (T :: Ts) (i + 1) = selFibre ρ Ts i := rfl

/-- The selector's three facts, in one induction: at every member of
`ω` the selector's reading lies in `univ w`, at the numeral `i` it is
the `i`-th fibre, and the spine is graded.  `hT` bounds the spellings
at the retracted environment. -/
theorem caseAVAt_facts {w : Nat} :
    ∀ {Ts : List AVExpr} {d : Nat} {k : AVExpr} {σ : Nat → V},
      (∀ T ∈ Ts, interp2 V (shiftE d 0 σ) T ∈ˢ (univ w : V)) →
      (∀ T ∈ Ts, AnnotOk2 V (shiftE d 0 σ) T) →
      AnnotOk2 V σ k → interp2 V σ k ∈ˢ (omega : V) →
      interp2 V σ (caseAVAt w Ts d k) ∈ˢ (univ w : V) ∧
      (∀ i, interp2 V σ k = vnat i →
        interp2 V σ (caseAVAt w Ts d k) = selFibre (shiftE d 0 σ) Ts i) ∧
      AnnotOk2 V σ (caseAVAt w Ts d k)
  | [], d, k, σ, _, _, _, _ => by
    refine ⟨empty_mem_univ w, fun i _ => rfl, ?_⟩
    show AnnotOk2 V σ (.const .empty [w])
    trivial
  | T :: Ts, d, k, σ, hT, hokT, hokk, hk => by
    -- the parts
    have hM := natSortMotiveAV_mem w σ
    have hTv : interp2 V σ (T.liftN d 0) = interp2 V (shiftE d 0 σ) T := interp2_liftN V d T 0 σ
    have hz : interp2 V σ (T.liftN d 0)
        ∈ˢ SetTheory.app (interp2 V σ (natSortMotiveAV w)) natzero := by
      rw [natSortMotiveAV_app w σ natzero_mem, hTv]
      exact hT T (.head _)
    -- the step's inner selector, at every step frame
    have hinner : ∀ (a b : V), b ∈ˢ (omega : V) →
        interp2 V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1)) ∈ˢ (univ w : V) ∧
        (∀ i, b = vnat i →
          interp2 V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1))
            = selFibre (shiftE d 0 σ) Ts i) ∧
        AnnotOk2 V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1)) := by
      intro a b hb
      have h := caseAVAt_facts (w := w) (Ts := Ts) (d := d + 2) (k := .bvar 1)
        (σ := cons a (cons b σ))
        (by rw [shiftE_step]; exact fun T' hT' => hT T' (.tail _ hT'))
        (by rw [shiftE_step]; exact fun T' hT' => hokT T' (.tail _ hT'))
        trivial (by rw [interp2_bvar]; exact hb)
      rw [shiftE_step] at h
      exact ⟨h.1, fun i hi => h.2.1 i (by rw [interp2_bvar]; exact hi), h.2.2⟩
    have hsv : interp2 V σ (.lam (w + 1) natAV (.lam (w + 1) (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1))))
        = lamR (w + 1) omega fun b => lamR (w + 1) (univ w) fun a =>
            interp2 V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1)) := rfl
    have hs : interp2 V σ (.lam (w + 1) natAV (.lam (w + 1) (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1))))
        ∈ˢ natStepSpace2 V (w + 1) (interp2 V σ (natSortMotiveAV w)) := by
      rw [hsv]
      unfold natStepSpace2
      refine lamR_mem fun b hb => ?_
      rw [natSortMotiveAV_app w σ hb, natSortMotiveAV_app w σ (natsucc_mem hb)]
      exact lamR_mem fun a _ => (hinner a b hb).1
    refine ⟨?_, ?_, ?_⟩
    · -- the bound
      have h := natRecAV_mem hM hz hs hk
      rwa [natSortMotiveAV_app w σ hk] at h
    · -- the selection
      intro i hi
      show interp2 V σ (natRecAV (w + 1) (natSortMotiveAV w) (T.liftN d 0) _ k) = _
      rw [interp2_natRecAV hM hz hs hk, hi, natrec_vnat]
      -- unroll the iteration
      have hiter : ∀ j, natIter (interp2 V σ (T.liftN d 0))
          (interp2 V σ (.lam (w + 1) natAV (.lam (w + 1) (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1)))))
          j ∈ˢ (univ w : V) := by
        intro j
        have h := natRecV2_mem_fibre V hM hz hs (vnat_mem_omega j)
        rwa [natrec_vnat, natSortMotiveAV_app w σ (vnat_mem_omega j)] at h
      cases i with
      | zero => exact hTv
      | succ i =>
        show SetTheory.app (SetTheory.app _ (vnat i)) (natIter _ _ i) = selFibre (shiftE d 0 σ) Ts i
        rw [hsv, app_lamR_pos (Nat.succ_ne_zero w) (vnat_mem_omega i),
          app_lamR_pos (Nat.succ_ne_zero w) (by rw [← hsv]; exact hiter i)]
        exact (hinner _ _ (vnat_mem_omega i)).2.1 i rfl
    · -- the grading
      refine natRecAV_ok2 (natSortMotiveAV_ok2 w σ) ?_ ?_ hokk hM hz hs hk
      · rw [AnnotOk2_liftN]; exact hokT T (.head _)
      · rw [AnnotOk2_lam]
        refine ⟨trivial, fun b hb => ?_,
          fun _ => piR (w + 1) (univ w : V) fun _ => (univ w : V), ?_,
          fun h => absurd h (Nat.succ_ne_zero _)⟩
        · rw [AnnotOk2_lam]
          refine ⟨trivial, fun a _ => (hinner a b hb).2.2,
            fun _ => (univ w : V), fun a _ => (hinner a b hb).1, fun h => absurd h (Nat.succ_ne_zero _)⟩
        · intro b hb
          exact lamR_mem fun a _ => (hinner a b hb).1

end Lech.Semantics
