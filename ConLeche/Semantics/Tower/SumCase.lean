module

public import ConLeche.Semantics.Tower.TowerLeaf
public import ConLeche.SetModel.TaggedSum

@[expose] public section

/-!
# The numeral case split, spelled (task #175 sum-types, stage S1)

The tagged sum's tag is a `Nat` numeral and its case split is
`Nat.rec`: this module spells both in the `AnnotTerm` alphabet and reads
them back.

* `numeralAV i` — `Nat.succ^i Nat.zero`, reading to `vnat i`;
* `natRecAV u M z s k` — the four-application spine of `Nat.rec.{u}`,
  reading to `natrec ⟦z⟧ ⟦s⟧ ⟦k⟧` under the motive/base/step
  memberships (`natRecV_app`), graded from the same memberships
  (`natRecAV_wellDenoted` — the spine's four slots are `Nat.rec`'s own product
  chain, both regimes);
* `caseAVAt w Ts d k` — **the fibre selector**: the nested `Nat.rec`
  tower with the constant motive `λ _ : Nat, Sort w` that picks the
  `i`-th of the type spellings `Ts` at the numeral `i` and `Empty`
  beyond.  The spellings are scoped `d` binders below the point of use
  (they are lifted by `d` at each use; the nesting adds two binders per
  level), so the reading is stated at the retracted environment
  `shiftE d 0 σ` — no capture-avoiding substitution anywhere.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Term (Term)

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The numerals -/

/-- `Nat`, spelled. -/
def natAV : AnnotTerm := .const .nat []

/-- `Nat.succ^i Nat.zero`. -/
def numeralAV : Nat → AnnotTerm
  | 0 => .const .natZero []
  | i + 1 => .app (.const .natSucc []) (numeralAV i)

theorem natzero_eq_vnat : (natzero : V) = vnat 0 := by
  unfold natzero; rfl

theorem natsucc_eq_vsucc (n : V) : natsucc n = vsucc n := by
  unfold natsucc; rfl

theorem interp_numeralAV : ∀ (i : Nat) (ρ : Nat → V), interp V ρ (numeralAV i) = vnat i
  | 0, _ => natzero_eq_vnat
  | i + 1, ρ => by
    show SetTheory.app (natSuccV V) (interp V ρ (numeralAV i)) = vsucc (vnat i)
    rw [interp_numeralAV i ρ, natSuccV_app V (vnat_mem_omega i), natsucc_eq_vsucc]

theorem numeralAV_wellDenoted : ∀ (i : Nat) (ρ : Nat → V), WellDenoted V ρ (numeralAV i)
  | 0, _ => by simp [numeralAV]
  | i + 1, ρ => by
    show WellDenoted V ρ (.app (.const .natSucc []) (numeralAV i))
    rw [WellDenoted_app]
    refine ⟨trivial, numeralAV_wellDenoted i ρ, 1, omega, fun _ => omega, natSuccV_mem V, ?_,
      fun h => absurd h Nat.one_ne_zero⟩
    rw [interp_numeralAV]
    exact vnat_mem_omega i

theorem numeralAV_erase_below (i k : Nat) : Term.bvarsBelow k (numeralAV i).erase := by
  induction i with
  | zero => trivial
  | succ i ih => exact ⟨trivial, ih⟩

/-! ## A proof-point-headed spine is graded -/

/-- An application spine whose head reads to the point is graded from
its arguments' gradings alone, and reads to the point: every slot is
the trivial product over the argument's singleton. -/
theorem mkAppN_wellDenoted_of_pt_head :
    ∀ {args : List AnnotTerm} {f : AnnotTerm} {σ : Nat → V},
      WellDenoted V σ f → interp V σ f = pt → (∀ a ∈ args, WellDenoted V σ a) →
      WellDenoted V σ (AnnotTerm.mkAppN f args) ∧ interp V σ (AnnotTerm.mkAppN f args) = pt
  | [], _, _, hf, hpt, _ => ⟨hf, hpt⟩
  | a :: args, f, σ, hf, hpt, hargs => by
    rw [AnnotTerm.mkAppN_cons]
    refine mkAppN_wellDenoted_of_pt_head ?_ ?_ fun a' ha' => hargs a' (.tail _ ha')
    · rw [WellDenoted_app]
      refine ⟨hf, hargs a (.head _), 0, sing (interp V σ a), fun _ => unitSet, ?_,
        mem_sing.mpr rfl, fun _ _ _ => by rw [← univ_zero]; exact unitSet_mem_univ 0⟩
      rw [hpt]
      exact pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitSet⟩
    · rw [interp_app, hpt, app_pt]

/-! ## `Nat.rec` spines -/

/-- The `Nat.rec.{u}` spine. -/
def natRecAV (u : Nat) (M z s k : AnnotTerm) : AnnotTerm :=
  AnnotTerm.mkAppN (.const .natRec [u]) [M, z, s, k]

theorem interp_natRecAV_raw (u : Nat) (M z s k : AnnotTerm) (σ : Nat → V) :
    interp V σ (natRecAV u M z s k)
      = SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (natRecV V u)
          (interp V σ M)) (interp V σ z)) (interp V σ s)) (interp V σ k) := by rfl

/-- The spine reads to `natrec` (`natRecV_app`). -/
theorem interp_natRecAV {u : Nat} {M z s k : AnnotTerm} {σ : Nat → V}
    (hM : interp V σ M ∈ˢ natMotiveSpace V u)
    (hz : interp V σ z ∈ˢ SetTheory.app (interp V σ M) natzero)
    (hs : interp V σ s ∈ˢ natStepSpace V u (interp V σ M))
    (hk : interp V σ k ∈ˢ (omega : V)) :
    interp V σ (natRecAV u M z s k) = natrec (interp V σ z) (interp V σ s) (interp V σ k) := by
  rw [interp_natRecAV_raw]
  exact natRecV_app V hM hz hs hk

/-- The spine inhabits the motive at the numeral. -/
theorem natRecAV_mem {u : Nat} {M z s k : AnnotTerm} {σ : Nat → V}
    (hM : interp V σ M ∈ˢ natMotiveSpace V u)
    (hz : interp V σ z ∈ˢ SetTheory.app (interp V σ M) natzero)
    (hs : interp V σ s ∈ˢ natStepSpace V u (interp V σ M))
    (hk : interp V σ k ∈ˢ (omega : V)) :
    interp V σ (natRecAV u M z s k) ∈ˢ SetTheory.app (interp V σ M) (interp V σ k) := by
  rw [interp_natRecAV hM hz hs hk]
  exact natRecV_mem_fibre V hM hz hs hk

/-- **The spine is graded**, both regimes: the four slots are
`Nat.rec`'s own product chain, with the squash-side fibre conditions
landing on `piR_zero_mem_univZero` and the motive's own fibres. -/
theorem natRecAV_wellDenoted {u : Nat} {M z s k : AnnotTerm} {σ : Nat → V}
    (hokM : WellDenoted V σ M) (hokz : WellDenoted V σ z) (hoks : WellDenoted V σ s)
    (hokk : WellDenoted V σ k)
    (hM : interp V σ M ∈ˢ natMotiveSpace V u)
    (hz : interp V σ z ∈ˢ SetTheory.app (interp V σ M) natzero)
    (hs : interp V σ s ∈ˢ natStepSpace V u (interp V σ M))
    (hk : interp V σ k ∈ˢ (omega : V)) :
    WellDenoted V σ (natRecAV u M z s k) := by
  have hbv : interp V σ (.const .natRec [u]) = natRecV V u := rfl
  have h0 : natRecV V u ∈ˢ piR u (natMotiveSpace V u) fun M =>
      piR u (SetTheory.app M natzero) fun _ =>
        piR u (natStepSpace V u M) fun _ => piR u omega fun n => SetTheory.app M n := by
    unfold natRecV
    exact lamR_mem fun M hM => lamR_mem fun z hz => lamR_mem fun s hs =>
      lamR_mem fun n hn => natRecV_mem_fibre V hM hz hs hn
  have hz1 : u = 0 → ∀ M', M' ∈ˢ natMotiveSpace V u →
      (piR u (SetTheory.app M' natzero) fun _ =>
        piR u (natStepSpace V u M') fun _ => piR u omega fun n => SetTheory.app M' n)
        ∈ˢ (univZero : V) := by
    intro h0 _ _; subst h0; exact piR_zero_mem_univZero
  have h1 := app_mem_piR h0 hM hz1
  have hz2 : u = 0 → ∀ z', z' ∈ˢ SetTheory.app (interp V σ M) natzero →
      (piR u (natStepSpace V u (interp V σ M)) fun _ =>
        piR u omega fun n => SetTheory.app (interp V σ M) n) ∈ˢ (univZero : V) := by
    intro h0 _ _; subst h0; exact piR_zero_mem_univZero
  have h2 := app_mem_piR h1 hz hz2
  have hz3 : u = 0 → ∀ s', s' ∈ˢ natStepSpace V u (interp V σ M) →
      (piR u omega fun n => SetTheory.app (interp V σ M) n) ∈ˢ (univZero : V) := by
    intro h0 _ _; subst h0; exact piR_zero_mem_univZero
  have h3 := app_mem_piR h2 hs hz3
  have hz4 : u = 0 → ∀ n, n ∈ˢ (omega : V) →
      SetTheory.app (interp V σ M) n ∈ˢ (univZero : V) := by
    intro h0 n hn
    have := natMotive_apply V hM hn
    rw [h0, univ_zero] at this
    exact this
  show WellDenoted V σ (.app (.app (.app (.app (.const .natRec [u]) M) z) s) k)
  rw [WellDenoted_app]
  refine ⟨?_, hokk, u, omega, fun n => SetTheory.app (interp V σ M) n, ?_, hk, hz4⟩
  · rw [WellDenoted_app]
    refine ⟨?_, hoks, u, natStepSpace V u (interp V σ M), _, ?_, hs, hz3⟩
    · rw [WellDenoted_app]
      refine ⟨?_, hokz, u, SetTheory.app (interp V σ M) natzero, _, ?_, hz, hz2⟩
      · rw [WellDenoted_app]
        exact ⟨trivial, hokM, u, natMotiveSpace V u, _, hbv ▸ h0, hM, hz1⟩
      · show SetTheory.app (interp V σ (.const .natRec [u])) (interp V σ M) ∈ˢ _
        rw [hbv]; exact h1
    · show SetTheory.app (SetTheory.app (interp V σ (.const .natRec [u])) (interp V σ M))
        (interp V σ z) ∈ˢ _
      rw [hbv]; exact h2
  · show SetTheory.app (SetTheory.app (SetTheory.app (interp V σ (.const .natRec [u]))
      (interp V σ M)) (interp V σ z)) (interp V σ s) ∈ˢ _
    rw [hbv]; exact h3

/-! ## The fibre selector -/

/-- The constant motive `λ _ : Nat, Sort w` (its body's type is
`Sort (w + 1)`, hence the bit). -/
def natSortMotiveAV (w : Nat) : AnnotTerm := .lam (w + 1) natAV (.sort w)

theorem interp_natSortMotiveAV (w : Nat) (σ : Nat → V) :
    interp V σ (natSortMotiveAV w) = lamR (w + 1) omega fun _ => univ w := by rfl

theorem natSortMotiveAV_mem (w : Nat) (σ : Nat → V) :
    interp V σ (natSortMotiveAV w) ∈ˢ natMotiveSpace V (w + 1) := by
  rw [interp_natSortMotiveAV]
  exact lamR_mem_zero_agree
    ⟨fun h => absurd h (Nat.succ_ne_zero _), fun h => absurd h (Nat.succ_ne_zero _)⟩
    fun _ _ => univ_mem_univ w

theorem natSortMotiveAV_app (w : Nat) (σ : Nat → V) {n : V} (hn : n ∈ˢ (omega : V)) :
    SetTheory.app (interp V σ (natSortMotiveAV w)) n = univ w := by
  rw [interp_natSortMotiveAV]
  exact app_lamR_pos (Nat.succ_ne_zero w) hn

theorem natSortMotiveAV_wellDenoted (w : Nat) (σ : Nat → V) : WellDenoted V σ (natSortMotiveAV w) := by
  show WellDenoted V σ (.lam (w + 1) natAV (.sort w))
  rw [WellDenoted_lam]
  exact ⟨trivial, fun _ _ => trivial, fun _ => univ (w + 1), fun _ _ => univ_mem_univ w,
    fun h => absurd h (Nat.succ_ne_zero _)⟩

/-- **The fibre selector**: the type spellings `Ts` are scoped `d`
binders below; the `i`-th is selected at the numeral `i`, `Empty`
beyond.  Each nesting level adds the step's two binders. -/
def caseAVAt (w : Nat) : List AnnotTerm → Nat → AnnotTerm → AnnotTerm
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
noncomputable def selFibre (ρ : Nat → V) (Ts : List AnnotTerm) (i : Nat) : V :=
  (Ts.map (interp V ρ)).getD i empty

/-- The selector's three facts, in one induction: at every member of
`ω` the selector's reading lies in `univ w`, at the numeral `i` it is
the `i`-th fibre, and the spine is graded.  `hT` bounds the spellings
at the retracted environment. -/
theorem caseAVAt_facts {w : Nat} :
    ∀ {Ts : List AnnotTerm} {d : Nat} {k : AnnotTerm} {σ : Nat → V},
      (∀ T ∈ Ts, interp V (shiftE d 0 σ) T ∈ˢ (univ w : V)) →
      (∀ T ∈ Ts, WellDenoted V (shiftE d 0 σ) T) →
      WellDenoted V σ k → interp V σ k ∈ˢ (omega : V) →
      interp V σ (caseAVAt w Ts d k) ∈ˢ (univ w : V) ∧
      (∀ i, interp V σ k = vnat i →
        interp V σ (caseAVAt w Ts d k) = selFibre (shiftE d 0 σ) Ts i) ∧
      WellDenoted V σ (caseAVAt w Ts d k)
  | [], d, k, σ, _, _, _, _ => by
    refine ⟨empty_mem_univ w, fun i _ => rfl, ?_⟩
    show WellDenoted V σ (.const .empty [w])
    trivial
  | T :: Ts, d, k, σ, hT, hokT, hokk, hk => by
    -- the parts
    have hM := natSortMotiveAV_mem w σ
    have hTv : interp V σ (T.liftN d 0) = interp V (shiftE d 0 σ) T := interp_liftN V d T 0 σ
    have hz : interp V σ (T.liftN d 0)
        ∈ˢ SetTheory.app (interp V σ (natSortMotiveAV w)) natzero := by
      rw [natSortMotiveAV_app w σ natzero_mem, hTv]
      exact hT T (.head _)
    -- the step's inner selector, at every step frame
    have hinner : ∀ (a b : V), b ∈ˢ (omega : V) →
        interp V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1)) ∈ˢ (univ w : V) ∧
        (∀ i, b = vnat i →
          interp V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1))
            = selFibre (shiftE d 0 σ) Ts i) ∧
        WellDenoted V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1)) := by
      intro a b hb
      have h := caseAVAt_facts (w := w) (Ts := Ts) (d := d + 2) (k := .bvar 1)
        (σ := cons a (cons b σ))
        (by rw [shiftE_step]; exact fun T' hT' => hT T' (.tail _ hT'))
        (by rw [shiftE_step]; exact fun T' hT' => hokT T' (.tail _ hT'))
        trivial (by rw [interp_bvar]; exact hb)
      rw [shiftE_step] at h
      exact ⟨h.1, fun i hi => h.2.1 i (by rw [interp_bvar]; exact hi), h.2.2⟩
    have hsv : interp V σ (.lam (w + 1) natAV (.lam (w + 1) (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1))))
        = lamR (w + 1) omega fun b => lamR (w + 1) (univ w) fun a =>
            interp V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1)) := rfl
    have hs : interp V σ (.lam (w + 1) natAV (.lam (w + 1) (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1))))
        ∈ˢ natStepSpace V (w + 1) (interp V σ (natSortMotiveAV w)) := by
      rw [hsv]
      unfold natStepSpace
      refine lamR_mem fun b hb => ?_
      rw [natSortMotiveAV_app w σ hb, natSortMotiveAV_app w σ (natsucc_mem hb)]
      exact lamR_mem fun a _ => (hinner a b hb).1
    refine ⟨?_, ?_, ?_⟩
    · -- the bound
      have h := natRecAV_mem hM hz hs hk
      rwa [natSortMotiveAV_app w σ hk] at h
    · -- the selection
      intro i hi
      show interp V σ (natRecAV (w + 1) (natSortMotiveAV w) (T.liftN d 0) _ k) = _
      rw [interp_natRecAV hM hz hs hk, hi, natrec_vnat]
      -- unroll the iteration
      have hiter : ∀ j, natIter (interp V σ (T.liftN d 0))
          (interp V σ (.lam (w + 1) natAV (.lam (w + 1) (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1)))))
          j ∈ˢ (univ w : V) := by
        intro j
        have h := natRecV_mem_fibre V hM hz hs (vnat_mem_omega j)
        rwa [natrec_vnat, natSortMotiveAV_app w σ (vnat_mem_omega j)] at h
      cases i with
      | zero => exact hTv
      | succ i =>
        show SetTheory.app (SetTheory.app _ (vnat i)) (natIter _ _ i) = selFibre (shiftE d 0 σ) Ts i
        rw [hsv, app_lamR_pos (Nat.succ_ne_zero w) (vnat_mem_omega i),
          app_lamR_pos (Nat.succ_ne_zero w) (by rw [← hsv]; exact hiter i)]
        exact (hinner _ _ (vnat_mem_omega i)).2.1 i rfl
    · -- the grading
      refine natRecAV_wellDenoted (natSortMotiveAV_wellDenoted w σ) ?_ ?_ hokk hM hz hs hk
      · rw [WellDenoted_liftN]; exact hokT T (.head _)
      · rw [WellDenoted_lam]
        refine ⟨trivial, fun b hb => ?_,
          fun _ => piR (w + 1) (univ w : V) fun _ => (univ w : V), ?_,
          fun h => absurd h (Nat.succ_ne_zero _)⟩
        · rw [WellDenoted_lam]
          refine ⟨trivial, fun a _ => (hinner a b hb).2.2,
            fun _ => (univ w : V), fun a _ => (hinner a b hb).1, fun h => absurd h (Nat.succ_ne_zero _)⟩
        · intro b hb
          exact lamR_mem fun a _ => (hinner a b hb).1

/-! ## Numerals under successors -/

/-- `Nat.succ^j k`. -/
def succsAV : Nat → AnnotTerm → AnnotTerm
  | 0, k => k
  | j + 1, k => .app (.const .natSucc []) (succsAV j k)

theorem interp_succsAV : ∀ (j : Nat) {k : AnnotTerm} {σ : Nat → V} {i : Nat},
    interp V σ k = vnat i → interp V σ (succsAV j k) = vnat (i + j)
  | 0, _, _, _, h => h
  | j + 1, k, σ, i, h => by
    show SetTheory.app (natSuccV V) (interp V σ (succsAV j k)) = vsucc (vnat (i + j))
    rw [interp_succsAV j h, natSuccV_app V (vnat_mem_omega _), natsucc_eq_vsucc]

theorem succsAV_wellDenoted : ∀ (j : Nat) {k : AnnotTerm} {σ : Nat → V} {i : Nat},
    WellDenoted V σ k → interp V σ k = vnat i → WellDenoted V σ (succsAV j k)
  | 0, _, _, _, hok, _ => hok
  | j + 1, k, σ, i, hok, h => by
    show WellDenoted V σ (.app (.const .natSucc []) (succsAV j k))
    rw [WellDenoted_app]
    refine ⟨trivial, succsAV_wellDenoted j hok h, 1, omega, fun _ => omega, natSuccV_mem V, ?_,
      fun h => absurd h Nat.one_ne_zero⟩
    rw [interp_succsAV j h]
    exact vnat_mem_omega _

/-! ## The numeral selector (task #279 D-1, DESIGN §M.60)

The mutual reduction's MEMBER-LOCAL constructor tags need, at three
places of the fixpoint kit, a numeral computed from other numerals by
a finite table: the flat position of a value's constructor from its
member and its local tag (`flatTagAV`, the family body's fibre selector
and the recursor's scrutinee), and the local tag of a flat position
(`locTagAV`, the case recursor's motive).  `natSelAV` is the table: the
`i`-th of the terms `ts` at the numeral `i`, `dflt` beyond —
`caseAVAt`'s `Nat.rec` tower at the constant motive `λ _ : Nat, Nat`.
The empty table is the NATIVE route, and every spelling reduces to its
old form there by definition (`flatTagAV [] _ _ k = k`, `locTagAV [] _
j k = succsAV j k`). -/

/-- `λ _ : Nat, Nat`, the numeral table's motive. -/
def natNatMotiveAV : AnnotTerm := .lam 1 natAV natAV

theorem interp_natNatMotiveAV (σ : Nat → V) :
    interp V σ natNatMotiveAV = lamR 1 omega fun _ => omega := rfl

theorem natNatMotiveAV_mem (σ : Nat → V) :
    interp V σ natNatMotiveAV ∈ˢ natMotiveSpace V 1 := by
  rw [interp_natNatMotiveAV]
  exact lamR_mem_zero_agree
    ⟨fun h => absurd h Nat.one_ne_zero, fun h => absurd h (Nat.succ_ne_zero _)⟩
    fun _ _ => omega_mem_univ_succ 0

theorem natNatMotiveAV_app (σ : Nat → V) {n : V} (hn : n ∈ˢ (omega : V)) :
    SetTheory.app (interp V σ natNatMotiveAV) n = omega := by
  rw [interp_natNatMotiveAV]
  exact app_lamR_pos Nat.one_ne_zero hn

theorem natNatMotiveAV_wellDenoted (σ : Nat → V) : WellDenoted V σ natNatMotiveAV := by
  show WellDenoted V σ (.lam 1 natAV natAV)
  rw [WellDenoted_lam]
  exact ⟨trivial, fun _ _ => trivial, fun _ => univ 1, fun _ _ => omega_mem_univ_succ 0,
    fun h => absurd h Nat.one_ne_zero⟩

/-- **The numeral selector**: the `i`-th of the terms `ts` at the
numeral `i`, `dflt` beyond; the terms are scoped `d` binders below the
point of use (as `caseAVAt`). -/
def natSelAV : List AnnotTerm → AnnotTerm → Nat → AnnotTerm → AnnotTerm
  | [], dflt, d, _ => dflt.liftN d 0
  | T :: Ts, dflt, d, k =>
    natRecAV 1 natNatMotiveAV (T.liftN d 0)
      (.lam 1 natAV (.lam 1 natAV (natSelAV Ts dflt (d + 2) (.bvar 1)))) k

/-- The selector's three facts (`caseAVAt_facts` at the numeral
motive): in `ω` at every member of `ω`, the `i`-th term at the numeral
`i`, graded. -/
theorem natSelAV_facts :
    ∀ {ts : List AnnotTerm} {dflt : AnnotTerm} {d : Nat} {k : AnnotTerm} {σ : Nat → V},
      (∀ T ∈ ts, interp V (shiftE d 0 σ) T ∈ˢ (omega : V)) →
      (∀ T ∈ ts, WellDenoted V (shiftE d 0 σ) T) →
      interp V (shiftE d 0 σ) dflt ∈ˢ (omega : V) → WellDenoted V (shiftE d 0 σ) dflt →
      WellDenoted V σ k → interp V σ k ∈ˢ (omega : V) →
      interp V σ (natSelAV ts dflt d k) ∈ˢ (omega : V) ∧
      (∀ i, interp V σ k = vnat i →
        interp V σ (natSelAV ts dflt d k) = interp V (shiftE d 0 σ) (ts.getD i dflt)) ∧
      WellDenoted V σ (natSelAV ts dflt d k)
  | [], dflt, d, k, σ, _, _, hdm, hdok, _, _ => by
    refine ⟨?_, fun i _ => ?_, ?_⟩
    · show interp V σ (dflt.liftN d 0) ∈ˢ _
      rw [interp_liftN]; exact hdm
    · show interp V σ (dflt.liftN d 0) = _
      rw [interp_liftN]; rfl
    · show WellDenoted V σ (dflt.liftN d 0)
      rw [WellDenoted_liftN]; exact hdok
  | T :: Ts, dflt, d, k, σ, hT, hokT, hdm, hdok, hokk, hk => by
    have hM := natNatMotiveAV_mem (V := V) σ
    have hTv : interp V σ (T.liftN d 0) = interp V (shiftE d 0 σ) T := interp_liftN V d T 0 σ
    have hz : interp V σ (T.liftN d 0)
        ∈ˢ SetTheory.app (interp V σ natNatMotiveAV) natzero := by
      rw [natNatMotiveAV_app σ natzero_mem, hTv]
      exact hT T (.head _)
    have hinner : ∀ (a b : V), b ∈ˢ (omega : V) →
        interp V (cons a (cons b σ)) (natSelAV Ts dflt (d + 2) (.bvar 1)) ∈ˢ (omega : V) ∧
        (∀ i, b = vnat i →
          interp V (cons a (cons b σ)) (natSelAV Ts dflt (d + 2) (.bvar 1))
            = interp V (shiftE d 0 σ) (Ts.getD i dflt)) ∧
        WellDenoted V (cons a (cons b σ)) (natSelAV Ts dflt (d + 2) (.bvar 1)) := by
      intro a b hb
      have h := natSelAV_facts (ts := Ts) (dflt := dflt) (d := d + 2) (k := .bvar 1)
        (σ := cons a (cons b σ))
        (by rw [shiftE_step]; exact fun T' hT' => hT T' (.tail _ hT'))
        (by rw [shiftE_step]; exact fun T' hT' => hokT T' (.tail _ hT'))
        (by rw [shiftE_step]; exact hdm) (by rw [shiftE_step]; exact hdok)
        trivial (by rw [interp_bvar]; exact hb)
      rw [shiftE_step] at h
      exact ⟨h.1, fun i hi => h.2.1 i (by rw [interp_bvar]; exact hi), h.2.2⟩
    have hsv : interp V σ (.lam 1 natAV (.lam 1 natAV (natSelAV Ts dflt (d + 2) (.bvar 1))))
        = lamR 1 omega fun b => lamR 1 omega fun a =>
            interp V (cons a (cons b σ)) (natSelAV Ts dflt (d + 2) (.bvar 1)) := rfl
    have hs : interp V σ (.lam 1 natAV (.lam 1 natAV (natSelAV Ts dflt (d + 2) (.bvar 1))))
        ∈ˢ natStepSpace V 1 (interp V σ natNatMotiveAV) := by
      rw [hsv]
      unfold natStepSpace
      refine lamR_mem fun b hb => ?_
      rw [natNatMotiveAV_app σ hb, natNatMotiveAV_app σ (natsucc_mem hb)]
      exact lamR_mem fun a _ => (hinner a b hb).1
    refine ⟨?_, ?_, ?_⟩
    · have h := natRecAV_mem hM hz hs hk
      rwa [natNatMotiveAV_app σ hk] at h
    · intro i hi
      show interp V σ (natRecAV 1 natNatMotiveAV (T.liftN d 0) _ k) = _
      rw [interp_natRecAV hM hz hs hk, hi, natrec_vnat]
      have hiter : ∀ j, natIter (interp V σ (T.liftN d 0))
          (interp V σ (.lam 1 natAV (.lam 1 natAV (natSelAV Ts dflt (d + 2) (.bvar 1)))))
          j ∈ˢ (omega : V) := by
        intro j
        have h := natRecV_mem_fibre V hM hz hs (vnat_mem_omega j)
        rwa [natrec_vnat, natNatMotiveAV_app σ (vnat_mem_omega j)] at h
      cases i with
      | zero => exact hTv
      | succ i =>
        show SetTheory.app (SetTheory.app _ (vnat i)) (natIter _ _ i)
          = interp V (shiftE d 0 σ) (Ts.getD i dflt)
        rw [hsv, app_lamR_pos Nat.one_ne_zero (vnat_mem_omega i),
          app_lamR_pos Nat.one_ne_zero (by rw [← hsv]; exact hiter i)]
        exact (hinner _ _ (vnat_mem_omega i)).2.1 i rfl
    · refine natRecAV_wellDenoted (natNatMotiveAV_wellDenoted σ) ?_ ?_ hokk hM hz hs hk
      · rw [WellDenoted_liftN]; exact hokT T (.head _)
      · rw [WellDenoted_lam]
        refine ⟨trivial, fun b hb => ?_,
          fun _ => piR 1 (omega : V) fun _ => (omega : V), ?_,
          fun h => absurd h Nat.one_ne_zero⟩
        · rw [WellDenoted_lam]
          refine ⟨trivial, fun a _ => (hinner a b hb).2.2,
            fun _ => (omega : V), fun a _ => (hinner a b hb).1, fun h => absurd h Nat.one_ne_zero⟩
        · intro b hb
          exact lamR_mem fun a _ => (hinner a b hb).1

omit [SetTheory V] in
theorem getD_map_numeralAV (row : List Nat) (i dflt : Nat) :
    (row.map numeralAV).getD i (numeralAV dflt) = numeralAV (row.getD i dflt) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases row[i]? <;> rfl

/-- A table of numerals: its reading is the numeral of the table's
entry (the default beyond), in `ω`, graded. -/
theorem numeralTable_facts {row : List Nat} {dflt : Nat} {k : AnnotTerm} {σ : Nat → V}
    (hokk : WellDenoted V σ k) (hk : interp V σ k ∈ˢ (omega : V)) :
    interp V σ (natSelAV (row.map numeralAV) (numeralAV dflt) 0 k) ∈ˢ (omega : V) ∧
    (∀ i, interp V σ k = vnat i →
      interp V σ (natSelAV (row.map numeralAV) (numeralAV dflt) 0 k) = vnat (row.getD i dflt)) ∧
    WellDenoted V σ (natSelAV (row.map numeralAV) (numeralAV dflt) 0 k) := by
  have h := natSelAV_facts (ts := row.map numeralAV) (dflt := numeralAV dflt) (d := 0) (k := k)
    (σ := σ)
    (by
      intro T hT
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hT
      rw [shiftE_zero_zero, interp_numeralAV]; exact vnat_mem_omega c)
    (by
      intro T hT
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp hT
      rw [shiftE_zero_zero]; exact numeralAV_wellDenoted c σ)
    (by rw [shiftE_zero_zero, interp_numeralAV]; exact vnat_mem_omega dflt)
    (by rw [shiftE_zero_zero]; exact numeralAV_wellDenoted dflt σ) hokk hk
  refine ⟨h.1, fun i hi => ?_, h.2.2⟩
  rw [h.2.1 i hi, shiftE_zero_zero, getD_map_numeralAV, interp_numeralAV]

/-! ## The tag table (task #279 D-1, DESIGN §M.60)

A mutual block's **tag table** `tbl : List (List Nat)`: row `m` lists
the flat positions of member `m`'s constructors in order.  A value of
member `m` built by its `jc`-th constructor is `inj jc ⟨fs, pt⟩`
(member-LOCAL tag), and the flat position of that constructor is
`flatOf tbl n m jc` — read off the TUPLE at the family body and the
recursor (`tagOf`: the member is the tag of the index tuple's first
component, `t = ⟨inj m ⟨ı⃗⟩⟩`), off a numeral at the constructor leaf.
`locOf tbl J` is the converse (the position of `J` in its row).  The
EMPTY table is the native route: every map is the identity there. -/

open Classical in
/-- The numeral of a tag (junk off `ω`). -/
noncomputable def natIdx (k : V) : Nat :=
  if h : ∃ i, k = vnat i then Classical.choose h else 0

theorem natIdx_vnat (i : Nat) : natIdx (vnat i : V) = i := by
  unfold natIdx
  rw [dif_pos ⟨i, rfl⟩]
  exact (vnat_inj (Classical.choose_spec (⟨i, rfl⟩ : ∃ i', (vnat i : V) = vnat i'))).symm

/-- A tuple's MEMBER tag: at `t = ⟨inj m ⟨ı⃗⟩⟩` the numeral `m`. -/
noncomputable def memTag (t : V) : Nat := natIdx (sfst (sfst t))

theorem memTag_mkTower_inj (m : Nat) (p : V) (rest : List V) :
    memTag (mkTower (inj m p :: rest)) = m := by
  unfold memTag
  show natIdx (sfst (sfst (spair (inj m p) (mkTower rest)))) = m
  rw [sfst_spair, sfst_inj, natIdx_vnat]

/-- The flat position of member `m`'s `jc`-th constructor; `jc` at the
empty table, `dead` beyond the row. -/
def flatOf (tbl : List (List Nat)) (dead m jc : Nat) : Nat :=
  match tbl with
  | [] => jc
  | _ :: _ => (tbl.getD m []).getD jc dead

omit [SetTheory V] in
@[simp] theorem flatOf_nil (dead m jc : Nat) : flatOf [] dead m jc = jc := rfl

omit [SetTheory V] in
theorem flatOf_cons (r : List Nat) (rs : List (List Nat)) (dead m jc : Nat) :
    flatOf (r :: rs) dead m jc = ((r :: rs).getD m []).getD jc dead := rfl

/-- The flat position at the member read off a tuple. -/
noncomputable def tagOf (tbl : List (List Nat)) (dead : Nat) (t : V) (jc : Nat) : Nat :=
  flatOf tbl dead (memTag t) jc

@[simp] theorem tagOf_nil (dead : Nat) (t : V) (jc : Nat) : tagOf [] dead t jc = jc := rfl

/-- The local position of a flat constructor: its index in its row;
itself at the empty table or off every row. -/
def locOf (tbl : List (List Nat)) (J : Nat) : Nat :=
  match tbl.find? (fun row => row.contains J) with
  | some row => row.idxOf J
  | none => J

omit [SetTheory V] in
@[simp] theorem locOf_nil (J : Nat) : locOf [] J = J := rfl

/-- **A valid tag table**: each row without repetition, distinct rows
disjoint (rows off the table are empty, so no bounds are needed). -/
def TblOk (tbl : List (List Nat)) : Prop :=
  (∀ row ∈ tbl, row.Nodup) ∧
  ∀ i k, i ≠ k → ∀ J, J ∈ tbl.getD i [] → J ∉ tbl.getD k []

omit [SetTheory V] in
theorem TblOk.tail {r : List Nat} {rs : List (List Nat)} (h : TblOk (r :: rs)) : TblOk rs := by
  refine ⟨fun row hrow => h.1 row (List.mem_cons_of_mem r hrow), fun i k hik J hJ => ?_⟩
  have := h.2 (i + 1) (k + 1) (by omega) J
  exact this hJ

omit [SetTheory V] in
/-- The first row containing an entry of row `m` is row `m`. -/
theorem find?_row_of_mem : ∀ {tbl : List (List Nat)}, TblOk tbl → ∀ {m J : Nat}, J ∈ tbl.getD m [] →
    tbl.find? (fun row => row.contains J) = some (tbl.getD m [])
  | [], _, m, J, hJ => by
    exact absurd hJ (by simp)
  | r :: rs, h, m, J, hJ => by
    cases m with
    | zero =>
      exact List.find?_cons_of_pos (p := fun row => row.contains J) (a := r)
        (List.contains_iff_mem.mpr hJ)
    | succ k =>
      have hJ' : J ∈ rs.getD k [] := hJ
      have hnot : ¬ (r.contains J = true) := by
        intro hc
        exact h.2 (k + 1) 0 (by omega) J hJ (List.contains_iff_mem.mp hc)
      rw [List.find?_cons_of_neg (p := fun row => row.contains J) (a := r) hnot]
      exact find?_row_of_mem h.tail hJ'

omit [SetTheory V] in
/-- **The local tag of a table entry is its row position** at a valid
table: `locOf tbl (flatOf tbl n m jc) = jc` whenever the entry is live
(`< n`, so the row has it at `jc`). -/
theorem locOf_flatOf {tbl : List (List Nat)} (h : TblOk tbl) {n m jc : Nat}
    (hlt : flatOf tbl n m jc < n) : locOf tbl (flatOf tbl n m jc) = jc := by
  cases tbl with
  | nil => rfl
  | cons r rs =>
    rw [flatOf_cons] at hlt ⊢
    have hjc : jc < ((r :: rs).getD m []).length := by
      refine Classical.byContradiction fun hge => ?_
      rw [List.getD_eq_getElem?_getD (l := (r :: rs).getD m []),
        List.getElem?_eq_none (by omega), Option.getD_none] at hlt
      exact Nat.lt_irrefl _ hlt
    have hget : ((r :: rs).getD m []).getD jc n = ((r :: rs).getD m [])[jc] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjc, Option.getD_some]
    have hmem : ((r :: rs).getD m [])[jc] ∈ (r :: rs).getD m [] := List.getElem_mem hjc
    have hrow : (r :: rs).getD m [] ∈ r :: rs := by
      have hm : m < (r :: rs).length := by
        refine Classical.byContradiction fun hge => ?_
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hjc
        simp at hjc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some]
      exact List.getElem_mem hm
    rw [hget]
    unfold locOf
    rw [find?_row_of_mem h hmem]
    exact (h.1 _ hrow).idxOf_getElem jc hjc

/-- The same at the tag map of a tuple: at any table (validity asked
only when it is nonempty), a live flat position's local tag is the
tag it came from. -/
theorem locOf_tagOf {tbl : List (List Nat)} (h : tbl ≠ [] → TblOk tbl) {n : Nat} {t : V} {jc j : Nat}
    (hJ : j = tagOf tbl n t jc) (hlt : j < n) : locOf tbl j = jc := by
  cases tbl with
  | nil => rw [hJ]; rfl
  | cons r rs =>
    rw [hJ] at hlt ⊢
    exact locOf_flatOf (h (List.cons_ne_nil r rs)) hlt

/-- The local tag of the flat position `j + i`, as the case recursor's
motive at stage `j` needs it at the numeral `i`: `i + j` at the empty
table (`succsAV`), the row position below `n`. -/
def locAt (tbl : List (List Nat)) (n j i : Nat) : Nat :=
  match tbl with
  | [] => i + j
  | _ :: _ => if j + i < n then locOf tbl (j + i) else 0

omit [SetTheory V] in
theorem locAt_eq_locOf {tbl : List (List Nat)} {n j i : Nat} (h : j + i < n) :
    locAt tbl n j i = locOf tbl (j + i) := by
  cases tbl with
  | nil => show i + j = j + i; omega
  | cons r rs => show (if j + i < n then _ else _) = _; rw [if_pos h]

omit [SetTheory V] in
/-- The local tag one stage on. -/
theorem locAt_succ (tbl : List (List Nat)) (n j i : Nat) :
    locAt tbl n j (i + 1) = locAt tbl n (j + 1) i := by
  cases tbl with
  | nil => show i + 1 + j = i + (j + 1); omega
  | cons r rs =>
    show (if j + (i + 1) < n then locOf (r :: rs) (j + (i + 1)) else 0)
      = (if j + 1 + i < n then locOf (r :: rs) (j + 1 + i) else 0)
    rw [show j + (i + 1) = j + 1 + i from by omega]

/-- **The flat tag, spelled**: from a member term and a local-tag term;
`k` itself at the empty table. -/
def flatTagAV (tbl : List (List Nat)) (dead : Nat) (mem k : AnnotTerm) : AnnotTerm :=
  match tbl with
  | [] => k
  | _ :: _ =>
    natSelAV (tbl.map fun row => natSelAV (row.map numeralAV) (numeralAV dead) 0 k)
      (numeralAV dead) 0 mem

omit [SetTheory V] in
@[simp] theorem flatTagAV_nil (dead : Nat) (mem k : AnnotTerm) : flatTagAV [] dead mem k = k := rfl

/-- **The local tag of `j + k`, spelled** (the motive's reconstruction
of the major): `succsAV j k` at the empty table. -/
def locTagAV (tbl : List (List Nat)) (n j : Nat) (k : AnnotTerm) : AnnotTerm :=
  match tbl with
  | [] => succsAV j k
  | _ :: _ =>
    natSelAV (((List.range n).drop j).map fun J => numeralAV (locOf tbl J)) (numeralAV 0) 0 k

omit [SetTheory V] in
@[simp] theorem locTagAV_nil (n j : Nat) (k : AnnotTerm) : locTagAV [] n j k = succsAV j k := rfl

/-- **The flat tag's facts** at a nonempty table: at a member numeral
`m` and a local numeral `i` it reads `flatOf tbl dead m i`, in `ω`,
graded. -/
theorem flatTagAV_facts {tbl : List (List Nat)} (hne : tbl ≠ []) {dead : Nat} {mem k : AnnotTerm}
    {σ : Nat → V} {m i : Nat} (hmem : interp V σ mem = vnat m) (hokm : WellDenoted V σ mem)
    (hk : interp V σ k = vnat i) (hokk : WellDenoted V σ k) :
    interp V σ (flatTagAV tbl dead mem k) = vnat (flatOf tbl dead m i) ∧
    interp V σ (flatTagAV tbl dead mem k) ∈ˢ (omega : V) ∧
    WellDenoted V σ (flatTagAV tbl dead mem k) := by
  obtain ⟨r, rs, rfl⟩ : ∃ r rs, tbl = r :: rs := by
    cases tbl with
    | nil => exact absurd rfl hne
    | cons r rs => exact ⟨r, rs, rfl⟩
  have hkω : interp V σ k ∈ˢ (omega : V) := by rw [hk]; exact vnat_mem_omega i
  have hleaf : ∀ row : List Nat,
      interp V σ (natSelAV (row.map numeralAV) (numeralAV dead) 0 k) ∈ˢ (omega : V) ∧
      interp V σ (natSelAV (row.map numeralAV) (numeralAV dead) 0 k) = vnat (row.getD i dead) ∧
      WellDenoted V σ (natSelAV (row.map numeralAV) (numeralAV dead) 0 k) := by
    intro row
    have h := numeralTable_facts (row := row) (dflt := dead) hokk hkω
    exact ⟨h.1, h.2.1 i hk, h.2.2⟩
  have h := natSelAV_facts
    (ts := (r :: rs).map fun row => natSelAV (row.map numeralAV) (numeralAV dead) 0 k)
    (dflt := numeralAV dead) (d := 0) (k := mem) (σ := σ)
    (by
      intro T hT
      obtain ⟨row, -, rfl⟩ := List.mem_map.mp hT
      rw [shiftE_zero_zero]; exact (hleaf row).1)
    (by
      intro T hT
      obtain ⟨row, -, rfl⟩ := List.mem_map.mp hT
      rw [shiftE_zero_zero]; exact (hleaf row).2.2)
    (by rw [shiftE_zero_zero, interp_numeralAV]; exact vnat_mem_omega dead)
    (by rw [shiftE_zero_zero]; exact numeralAV_wellDenoted dead σ)
    hokm (by rw [hmem]; exact vnat_mem_omega m)
  refine ⟨?_, h.1, h.2.2⟩
  show interp V σ (natSelAV _ (numeralAV dead) 0 mem) = vnat (((r :: rs).getD m []).getD i dead)
  rw [h.2.1 m hmem, shiftE_zero_zero, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getD_eq_getElem?_getD (l := r :: rs)]
  cases (r :: rs)[m]? with
  | none => show interp V σ (numeralAV dead) = vnat (([] : List Nat).getD i dead); rw [interp_numeralAV]; rfl
  | some row => exact (hleaf row).2.1

/-- **The local tag's facts**: at the numeral `i` it reads `locAt tbl n
j i`, in `ω`, graded. -/
theorem locTagAV_facts {tbl : List (List Nat)} {n j : Nat} {k : AnnotTerm} {σ : Nat → V} {i : Nat}
    (hk : interp V σ k = vnat i) (hokk : WellDenoted V σ k) :
    interp V σ (locTagAV tbl n j k) = vnat (locAt tbl n j i) ∧
    interp V σ (locTagAV tbl n j k) ∈ˢ (omega : V) ∧
    WellDenoted V σ (locTagAV tbl n j k) := by
  cases tbl with
  | nil =>
    show interp V σ (succsAV j k) = vnat (i + j) ∧ interp V σ (succsAV j k) ∈ˢ (omega : V) ∧
      WellDenoted V σ (succsAV j k)
    refine ⟨interp_succsAV j hk, ?_, succsAV_wellDenoted j hokk hk⟩
    rw [interp_succsAV j hk]; exact vnat_mem_omega _
  | cons r rs =>
    have hkω : interp V σ k ∈ˢ (omega : V) := by rw [hk]; exact vnat_mem_omega i
    have h := numeralTable_facts (row := ((List.range n).drop j).map (locOf (r :: rs))) (dflt := 0)
      hokk hkω
    have hrow : ((List.range n).drop j).map (fun J => numeralAV (locOf (r :: rs) J))
        = (((List.range n).drop j).map (locOf (r :: rs))).map numeralAV := by
      rw [List.map_map]; rfl
    unfold locTagAV locAt
    rw [hrow]
    refine ⟨?_, h.1, h.2.2⟩
    rw [h.2.1 i hk]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_drop]
    by_cases hlt : j + i < n
    · rw [List.getElem?_range hlt, if_pos hlt]; rfl
    · rw [List.getElem?_eq_none (by simp; omega), if_neg hlt]; rfl

/-! ## The member tag's grading -/

/-- A value with a graded pair structure: what `WellDenoted (.fst _)`
asks of it (`WellDenoted_fst`). -/
def SigmaMem (t : V) : Prop :=
  ∃ u v A Bf, t ∈ˢ sigmaSet (Nat.max u v) A Bf ∧ A ∈ˢ (univ u : V) ∧
    ∀ x, x ∈ˢ A → Bf x ∈ˢ (univ v : V)

/-- **A tag tuple**: a graded pair whose first component is a graded
pair over a numeral — the index tuple `⟨inj m ⟨ı⃗⟩⟩` of a mutual block's
member (`OffOk`, `FixLeafI.lean`), read by `.fst (.fst _)`. -/
def TagTuple (t : V) : Prop := SigmaMem t ∧ SigmaMem (sfst t) ∧ sfst (sfst t) ∈ˢ (omega : V)

/-- The member tag's node, read and graded at a tag tuple. -/
theorem fst_fst_facts {σ : Nat → V} {e : AnnotTerm} (hok : WellDenoted V σ e)
    (ht : TagTuple (interp V σ e)) :
    interp V σ (.fst (.fst e)) = sfst (sfst (interp V σ e)) ∧
    interp V σ (.fst (.fst e)) ∈ˢ (omega : V) ∧ WellDenoted V σ (.fst (.fst e)) := by
  obtain ⟨h1, h2, h3⟩ := ht
  refine ⟨by rw [interp_fst, interp_fst], by rw [interp_fst, interp_fst]; exact h3, ?_⟩
  rw [WellDenoted_fst]
  refine ⟨?_, by rw [interp_fst]; exact h2⟩
  rw [WellDenoted_fst]
  exact ⟨hok, h1⟩

theorem fst_facts {σ : Nat → V} {e : AnnotTerm} (hok : WellDenoted V σ e)
    (ht : TagTuple (interp V σ e)) :
    interp V σ (.fst e) = sfst (interp V σ e) ∧ WellDenoted V σ (.fst e) := by
  refine ⟨by rw [interp_fst], ?_⟩
  rw [WellDenoted_fst]
  exact ⟨hok, ht.1⟩

end ConLeche.Semantics
