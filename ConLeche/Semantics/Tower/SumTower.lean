module

public import ConLeche.Semantics.Tower.TowerKit
public import ConLeche.Verify.Denote.Shift
public import ConLeche.SetModel.TaggedSum
import ConLeche.Semantics.Univ

@[expose] public section

/-!
# The tagged-sum leaves over an indexed family

The tower leaves' syntactic battery; the numeral case split and the
tagged sum carrier, spelled; the index equation; the sum constructor
leaf; the sum leaves' syntactic battery.
-/

/-!
## The tower leaves' syntactic battery

The closedness row of an install-step leaf (`ConsHead.vclosed`) is
`Term.bvarsBelow 0 (leaf)`.  So this
section is a bvar-bound walk per leaf former, plus the peel lemma that
produces the binder domains' bounds from the (closed) type reading
(`stripPisAV_below`).  No semantics, no `V`.
-/

namespace ConLeche.Semantics
open ConLeche.Verify (projNV)
open ConLeche.SetModel

open ConLeche.Term

/-! ## Bound-variable bounds -/

/-- The domains of a Π-frame, each bounded at its own depth
(`mkPisAV`'s data). -/
def DomsBelow (k : Nat) : List Term → Prop
  | [] => True
  | d :: ds => Term.bvarsBelow k d ∧ DomsBelow (k + 1) ds

/-- Two field chains, one after the other. -/
theorem domsBelow_append : ∀ {Ds Es : List Term} {k : Nat},
    DomsBelow k Ds → DomsBelow (k + Ds.length) Es → DomsBelow k (Ds ++ Es)
  | [], _, k, _, hE => by simpa using hE
  | D :: Ds, Es, k, hD, hE =>
    ⟨hD.1, domsBelow_append hD.2
      (by rw [show k + 1 + Ds.length = k + (D :: Ds).length from by
            rw [List.length_cons]; omega]; exact hE)⟩

/-- The domains' closedness, entry by entry. -/
theorem DomsBelow.getD_below {K : Nat} :
    ∀ {ds : List Term}, DomsBelow K ds → ∀ k, k < ds.length →
      Term.bvarsBelow (K + k) (ds.getD k default)
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | d :: ds, h, 0, _ => by simpa using h.1
  | d :: ds, h, k + 1, hk => by
    simp only [List.getD_cons_succ]
    have := DomsBelow.getD_below (K := K + 1) (ds := ds) h.2 k (by simpa using hk)
    rwa [show K + 1 + k = K + (k + 1) from by omega] at this

/-! ## The `Term`-side helpers -/

namespace VExprAux

open ConLeche.Term.Term

/-- Lifting raises a bound by exactly the inserted count, at any
cut. -/
theorem bvarsBelow_liftN (n : Nat) :
    ∀ (v : Term) (m k : Nat), Term.bvarsBelow m v →
      Term.bvarsBelow (m + n) (Term.liftN n v k) := by
  intro v
  induction v with
  | bvar i =>
    intro m k h
    show Term.bvarsBelow (m + n) (.bvar (if i < k then i else i + n))
    by_cases hik : i < k
    · rw [ite_eq_left hik]
      exact Nat.lt_of_lt_of_le (show i < m from h) (Nat.le_add_right m n)
    · rw [ite_eq_right hik]
      exact Nat.add_lt_add_right (show i < m from h) n
  | sort u => intro _ _ _; trivial
  | const c us => intro _ _ _; trivial
  | prf => intro _ _ _; trivial
  | app f a ihf iha =>
    intro m k h
    exact ⟨ihf m k h.1, iha m k h.2⟩
  | lam A b ihA ihb =>
    intro m k h
    refine ⟨ihA m k h.1, ?_⟩
    have := ihb (m + 1) (k + 1) h.2
    rw [show m + 1 + n = m + n + 1 by omega] at this
    exact this
  | pi A B ihA ihB =>
    intro m k h
    refine ⟨ihA m k h.1, ?_⟩
    have := ihB (m + 1) (k + 1) h.2
    rw [show m + 1 + n = m + n + 1 by omega] at this
    exact this
  | letE v b ihv ihb =>
    intro m k h
    refine ⟨ihv m k h.1, ?_⟩
    have := ihb (m + 1) (k + 1) h.2
    rw [show m + 1 + n = m + n + 1 by omega] at this
    exact this
  | eqE a b iha ihb =>
    intro m k h
    exact ⟨iha m k h.1, ihb m k h.2⟩
  | fst e ihe =>
    intro m k h
    exact ihe m k h
  | snd e ihe =>
    intro m k h
    exact ihe m k h

/-- Application spines preserve a bound. -/
theorem bvarsBelow_mkAppN :
    ∀ {as : List Term} {f : Term} {k : Nat}, Term.bvarsBelow k f →
      (∀ a ∈ as, Term.bvarsBelow k a) →
      Term.bvarsBelow k (Term.mkAppN f as)
  | [], _, _, hf, _ => hf
  | a :: as, f, k, hf, has => by
    rw [Term.mkAppN_cons]
    exact bvarsBelow_mkAppN ⟨hf, has a (.head _)⟩
      fun a' ha' => has a' (.tail _ ha')

end VExprAux

/-! ## The leaf constructors' bounds -/

/-- The carrier body (graph regime): bounded from the field chain's
own bounds. -/
theorem towerBodyAVPos_below {w : Nat} :
    ∀ {Fs : List Term} {k : Nat}, DomsBelow k Fs →
      Term.bvarsBelow k (towerBodyAVPos w Fs)
  | [], _, _ => trivial
  | _ :: _, _, h =>
    ⟨⟨trivial, h.1⟩, h.1, towerBodyAVPos_below h.2⟩

/-- The carrier body (squash regime): bounded from the field chain's
own bounds. -/
theorem sqBodyAV_below :
    ∀ {Fs : List Term} {k : Nat}, DomsBelow k Fs →
      Term.bvarsBelow k (sqBodyAV Fs)
  | [], _, _ => trivial
  | _ :: _, _, h =>
    ⟨⟨h.1, sqBodyAV_below h.2, trivial⟩, trivial⟩

/-- The carrier body, both regimes. -/
theorem towerBodyAV_below {w : Nat} {Fs : List Term} {k : Nat}
    (h : DomsBelow k Fs) :
    Term.bvarsBelow k (towerBodyAV w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_below h
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_below h

/-- The uniform projection spelling adds no variables. -/
theorem projNV_below :
    ∀ {i : Nat} {e : Term} {k : Nat}, Term.bvarsBelow k e →
      Term.bvarsBelow k (projNV i e)
  | 0, _, _, h => h
  | i + 1, e, _, h => projNV_below (i := i) (e := .snd e) h

/-- The tupler (graph regime): bounded at the full field frame. -/
theorem mkTowerGoPos_below {w : Nat} :
    ∀ {Fs : List Term} {k : Nat}, DomsBelow k Fs →
      Term.bvarsBelow (k + Fs.length) (mkTowerGoPos w Fs)
  | [], _, _ => trivial
  | F :: Fs, k, h => by
    have hF : Term.bvarsBelow (k + (Fs.length + 1))
        (F.liftN (Fs.length + 1)) := by
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1) F k 0 h.1
      exact this
    have hbody : Term.bvarsBelow (k + (Fs.length + 1) + 1)
        ((towerBodyAV w Fs).liftN (Fs.length + 1) 1) := by
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1)
        (towerBodyAV w Fs) (k + 1) 1 (towerBodyAV_below h.2)
      rw [show k + 1 + (Fs.length + 1) = k + (Fs.length + 1) + 1
        by omega] at this
      exact this
    have hrec : Term.bvarsBelow (k + (Fs.length + 1))
        (mkTowerGoPos w Fs) := by
      have := mkTowerGoPos_below (w := w) (Fs := Fs) (k := k + 1) h.2
      rw [show k + 1 + Fs.length = k + (Fs.length + 1) by omega] at this
      exact this
    exact ⟨⟨⟨⟨trivial, hF⟩, hF, hbody⟩,
      show Fs.length < k + (Fs.length + 1) by omega⟩, hrec⟩

/-- The tupler, both regimes. -/
theorem mkTowerGo_below {w : Nat} {Fs : List Term} {k : Nat}
    (h : DomsBelow k Fs) :
    Term.bvarsBelow (k + Fs.length) (mkTowerGo w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero]; trivial
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_below h

/-- The λ-tower former: bounded from the frame's own bounds and the
body's at the full depth. -/
theorem mkLamsAV_below :
    ∀ {ds : List Term} {b : Term} {k : Nat},
      DomsBelow k ds →
      Term.bvarsBelow (k + ds.length) b →
      Term.bvarsBelow k (mkLamsAV ds b)
  | [], _, _, _, hb => hb
  | d :: ds, b, k, h, hb =>
    ⟨h.1, mkLamsAV_below h.2 (by
      rw [show k + 1 + ds.length = k + (ds.length + 1) by omega]
      exact hb)⟩

/-! ## The peel: bounds off a bounded reading -/

/-- A successful `stripPisAV` of a bounded reading bounds every binder
domain at its own depth and the residual at the full depth. -/
theorem stripPisAV_below :
    ∀ {n : Nat} {e : Term} {ps : List Term}
      {b : Term} {k : Nat},
      stripPisAV n e = some (ps, b) →
      Term.bvarsBelow k e →
      DomsBelow k ps ∧ Term.bvarsBelow (k + n) b
  | 0, e, ps, b, k, h, he => by
    obtain ⟨rfl, rfl⟩ : ps = [] ∧ b = e := by
      simpa [stripPisAV] using h.symm
    exact ⟨trivial, he⟩
  | n + 1, .pi A B, ps, b, k, h, he => by
    simp only [stripPisAV, Option.map_eq_some_iff] at h
    obtain ⟨⟨ps', b'⟩, hstrip, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : A :: ps' = ps ∧ b' = b := by
      simpa using heq
    obtain ⟨hds, hb⟩ := stripPisAV_below hstrip he.2
    exact ⟨⟨he.1, hds⟩, by
      rw [show k + (n + 1) = k + 1 + n by omega]
      exact hb⟩

/-! ## Lift-invariance of a closed leaf

A leaf bounded at `0` is bounded at every cut
(`Term.bvarsBelow.mono`), and a lift below the bound is the identity
(`Term.liftN_eq_self`). -/

/-- A closed leaf is `liftN`-invariant at every cut. -/
theorem liftN_eq_self_of_closed {e : Term}
    (h : Term.bvarsBelow 0 e) (k n : Nat) :
    Term.liftN n e k = e :=
  Term.liftN_eq_self (Term.bvarsBelow.mono (Nat.zero_le k) h) n

/-!
## The numeral case split, spelled

The tagged sum's tag is a `Nat` numeral and its case split is
`Nat.rec`: this module spells both in the `Term` alphabet and reads
them back.

* `numeralAV i` — `Nat.succ^i Nat.zero`, reading to `vnat i`;
* `natRecAV u M z s k` — the four-application spine of `Nat.rec.{u}`,
  reading to `natrec ⟦z⟧ ⟦s⟧ ⟦k⟧` under the motive/base/step
  memberships (`natRecV_app`), graded from the same memberships
  (`natRecAV_wellDenoted` — the spine's four slots are `Nat.rec`'s own function-space
  chain, both regimes);
* `caseAVAt w Ts d k` — **the fibre selector**: the nested `Nat.rec`
  tower with the constant motive `λ _ : Nat, Sort w` that picks the
  `i`-th of the type spellings `Ts` at the numeral `i` and `Empty`
  beyond.  The spellings are scoped `d` binders below the point of use
  (they are lifted by `d` at each use; the nesting adds two binders per
  level), so the reading is stated at the retracted environment
  `shiftE d 0 σ` — no capture-avoiding substitution anywhere.
-/

open SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Term (Term)

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The numerals -/

/-- `Nat`, spelled. -/
def natAV : Term := .const .nat []

/-- `Nat.succ^i Nat.zero`. -/
def numeralAV : Nat → Term
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
      fun h => absurd h Nat.one_ne_zero, fun _ => IsTy_omega⟩
    rw [interp_numeralAV]
    exact vnat_mem_omega i

theorem numeralAV_below (i k : Nat) : Term.bvarsBelow k (numeralAV i) := by
  induction i with
  | zero => trivial
  | succ i ih => exact ⟨trivial, ih⟩

/-! ## A proof-point-headed spine is graded -/

/-- An application spine whose head reads to the point is graded from
its arguments' gradings alone, and reads to the point: every slot is
the trivial function space over the argument's singleton. -/
theorem mkAppN_wellDenoted_of_pt_head :
    ∀ {args : List Term} {f : Term} {σ : Nat → V},
      WellDenoted V σ f → interp V σ f = pt → (∀ a ∈ args, WellDenoted V σ a) →
      WellDenoted V σ (Term.mkAppN f args) ∧ interp V σ (Term.mkAppN f args) = pt
  | [], _, _, hf, hpt, _ => ⟨hf, hpt⟩
  | a :: args, f, σ, hf, hpt, hargs => by
    rw [Term.mkAppN_cons]
    refine mkAppN_wellDenoted_of_pt_head ?_ ?_ fun a' ha' => hargs a' (.tail _ ha')
    · rw [WellDenoted_app]
      refine ⟨hf, hargs a (.head _), 0, sing (interp V σ a), fun _ => unitSet, ?_,
        mem_sing.mpr rfl, fun _ _ _ => by rw [← univ_zero]; exact unitSet_mem_univ 0,
        fun h => absurd rfl h⟩
      rw [hpt]
      exact pt_mem_piR_zero fun _ _ => ⟨pt, pt_mem_unitSet⟩
    · rw [interp_app, hpt, app_pt]

/-! ## `Nat.rec` spines -/

/-- The `Nat.rec.{u}` spine. -/
def natRecAV (u : Nat) (M z s k : Term) : Term :=
  Term.mkAppN (.const .natRec [u]) [M, z, s, k]

theorem interp_natRecAV_raw (u : Nat) (M z s k : Term) (σ : Nat → V) :
    interp V σ (natRecAV u M z s k)
      = SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (natRecV V u)
          (interp V σ M)) (interp V σ z)) (interp V σ s)) (interp V σ k) := by rfl

/-- The spine reads to `natrec` (`natRecV_app`). -/
theorem interp_natRecAV {u : Nat} {M z s k : Term} {σ : Nat → V}
    (hM : interp V σ M ∈ˢ natMotiveSpace V u)
    (hz : interp V σ z ∈ˢ SetTheory.app (interp V σ M) natzero)
    (hs : interp V σ s ∈ˢ natStepSpace V (interp V σ M))
    (hk : interp V σ k ∈ˢ (omega : V)) :
    interp V σ (natRecAV u M z s k) = natrec (interp V σ z) (interp V σ s) (interp V σ k) := by
  rw [interp_natRecAV_raw]
  exact natRecV_app V hM hz hs hk

/-- The spine inhabits the motive at the numeral. -/
theorem natRecAV_mem {u : Nat} {M z s k : Term} {σ : Nat → V}
    (hM : interp V σ M ∈ˢ natMotiveSpace V u)
    (hz : interp V σ z ∈ˢ SetTheory.app (interp V σ M) natzero)
    (hs : interp V σ s ∈ˢ natStepSpace V (interp V σ M))
    (hk : interp V σ k ∈ˢ (omega : V)) :
    interp V σ (natRecAV u M z s k) ∈ˢ SetTheory.app (interp V σ M) (interp V σ k) := by
  rw [interp_natRecAV hM hz hs hk]
  exact natRecV_mem_fibre V hz hs hk

/-- **The spine is graded**, both regimes: the four slots are
`Nat.rec`'s own function-space chain, with the squash-side fibre conditions
landing on `piR_zero_mem_univZero` and the motive's own fibres. -/
theorem natRecAV_wellDenoted {u : Nat} {M z s k : Term} {σ : Nat → V}
    (hokM : WellDenoted V σ M) (hokz : WellDenoted V σ z) (hoks : WellDenoted V σ s)
    (hokk : WellDenoted V σ k)
    (hM : interp V σ M ∈ˢ natMotiveSpace V u)
    (hz : interp V σ z ∈ˢ SetTheory.app (interp V σ M) natzero)
    (hs : interp V σ s ∈ˢ natStepSpace V (interp V σ M))
    (hk : interp V σ k ∈ˢ (omega : V)) :
    WellDenoted V σ (natRecAV u M z s k) := by
  have hbv : interp V σ (.const .natRec [u]) = natRecV V u := rfl
  have h0 := natRecV_mem V u
  have h1 : SetTheory.app (natRecV V u) (interp V σ M) ∈ˢ
      piV (SetTheory.app (interp V σ M) natzero) fun _ =>
        piV (natStepSpace V (interp V σ M)) fun _ =>
          piV omega fun n => SetTheory.app (interp V σ M) n := app_mem_piV h0 hM
  have h2 := app_mem_piV h1 hz
  have h3 := app_mem_piV h2 hs
  show WellDenoted V σ (.app (.app (.app (.app (.const .natRec [u]) M) z) s) k)
  rw [WellDenoted_app]
  refine ⟨?_, hokk, ?_⟩
  · rw [WellDenoted_app]
    refine ⟨?_, hoks, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨?_, hokz, ?_⟩
      · rw [WellDenoted_app]
        exact ⟨trivial, hokM, by rw [hbv]; exact piV_slot h0 hM IsTy_piV⟩
      · show ∃ v A B, SetTheory.app (interp V σ (.const .natRec [u])) (interp V σ M)
          ∈ˢ piR v A B ∧ _
        rw [hbv]
        exact piV_slot h1 hz (IsTy_of_mem_univ (natMotive_apply V hM natzero_mem))
    · show ∃ v A B, SetTheory.app (SetTheory.app (interp V σ (.const .natRec [u]))
        (interp V σ M)) (interp V σ z) ∈ˢ piR v A B ∧ _
      rw [hbv]; exact piV_slot h2 hs IsTy_piV
  · show ∃ v A B, SetTheory.app (SetTheory.app (SetTheory.app
      (interp V σ (.const .natRec [u])) (interp V σ M)) (interp V σ z)) (interp V σ s)
      ∈ˢ piR v A B ∧ _
    rw [hbv]; exact piV_slot h3 hk IsTy_omega

/-! ## The fibre selector -/

/-- The constant motive `λ _ : Nat, Sort w` (its body's type is
`Sort (w + 1)`, so it reads as a graph). -/
def natSortMotiveAV (w : Nat) : Term := .lam natAV (.sort w)

theorem interp_natSortMotiveAV (w : Nat) (σ : Nat → V) :
    interp V σ (natSortMotiveAV w) = lamR (w + 1) omega fun _ => univ w :=
  lamV_eq_pos (Nat.succ_ne_zero w) natzero_mem (IsTy_univ w).ne_pt

theorem natSortMotiveAV_mem (w : Nat) (σ : Nat → V) :
    interp V σ (natSortMotiveAV w) ∈ˢ natMotiveSpace V (w + 1) := by
  rw [natSortMotiveAV, interp_lam]
  exact lamV_mem (fun _ _ => univ_mem_univ w) fun _ _ => IsTy_univ _

theorem natSortMotiveAV_app (w : Nat) (σ : Nat → V) {n : V} (hn : n ∈ˢ (omega : V)) :
    SetTheory.app (interp V σ (natSortMotiveAV w)) n = univ w := by
  rw [interp_natSortMotiveAV]
  exact app_lamR_pos (Nat.succ_ne_zero w) hn

theorem natSortMotiveAV_wellDenoted (w : Nat) (σ : Nat → V) : WellDenoted V σ (natSortMotiveAV w) := by
  show WellDenoted V σ (.lam natAV (.sort w))
  rw [WellDenoted_lam]
  exact ⟨trivial, IsTy_omega, fun _ _ => trivial, fun _ => univ (w + 1),
    fun _ _ => univ_mem_univ w, fun _ _ => IsTy_univ _⟩

/-- **The fibre selector**: the type spellings `Ts` are scoped `d`
binders below; the `i`-th is selected at the numeral `i`, `Empty`
beyond.  Each nesting level adds the step's two binders. -/
def caseAVAt (w : Nat) : List Term → Nat → Term → Term
  | [], _, _ => .const .empty [w]
  | T :: Ts, d, k =>
    natRecAV (w + 1) (natSortMotiveAV w) (T.liftN d 0)
      (.lam natAV (.lam (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1)))) k

omit [SetTheory V] in
/-- The environment retraction across the step's two binders. -/
theorem shiftE_step (d : Nat) (σ : Nat → V) (a b : V) :
    shiftE (d + 2) 0 (cons a (cons b σ)) = shiftE d 0 σ := by
  rw [show d + 2 = (d + 1) + 1 from rfl, shiftE_succ_cons, shiftE_succ_cons]

/-- The selected fibre, semantically: the `i`-th reading, `empty`
beyond. -/
noncomputable def selFibre (ρ : Nat → V) (Ts : List Term) (i : Nat) : V :=
  (Ts.map (interp V ρ)).getD i empty

/-- The selector's three facts, in one induction: at every member of
`ω` the selector's reading lies in `univ w`, at the numeral `i` it is
the `i`-th fibre, and the spine is graded.  `hT` bounds the spellings
at the retracted environment. -/
theorem caseAVAt_facts {w : Nat} :
    ∀ {Ts : List Term} {d : Nat} {k : Term} {σ : Nat → V},
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
    have hin : ∀ b, b ∈ˢ (omega : V) →
        interp V (cons b σ) (.lam (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1)))
          = lamR (w + 1) (univ w) fun a =>
            interp V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1)) := fun b hb =>
      lamV_eq_pos (Nat.succ_ne_zero w) (empty_mem_univ w)
        (IsTy_of_mem_univ (hinner empty b hb).1).ne_pt
    have hsv : interp V σ (.lam natAV (.lam (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1))))
        = lamR (w + 1) omega fun b => lamR (w + 1) (univ w) fun a =>
            interp V (cons a (cons b σ)) (caseAVAt w Ts (d + 2) (.bvar 1)) :=
      (lamV_congr hin).trans
        (lamV_eq_pos (Nat.succ_ne_zero w) natzero_mem (lamR_ne_pt (Nat.succ_ne_zero w)))
    have hs : interp V σ (.lam natAV (.lam (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1))))
        ∈ˢ natStepSpace V (interp V σ (natSortMotiveAV w)) := by
      rw [interp_lam]
      refine lamV_mem (fun b hb => ?_) fun _ _ => IsTy_piV
      simp only [interp_lam, interp_sort]
      rw [natSortMotiveAV_app w σ hb, natSortMotiveAV_app w σ (natsucc_mem hb)]
      exact lamV_mem (fun a _ => (hinner a b hb).1) fun _ _ => IsTy_univ w
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
          (interp V σ (.lam natAV (.lam (.sort w) (caseAVAt w Ts (d + 2) (.bvar 1)))))
          j ∈ˢ (univ w : V) := by
        intro j
        have h := natRecV_mem_fibre V hz hs (vnat_mem_omega j)
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
        refine ⟨trivial, IsTy_omega, fun b hb => ?_,
          fun _ => piR (w + 1) (univ w : V) fun _ => (univ w : V), ?_,
          fun _ _ => IsTy_piR _ _ _⟩
        · rw [WellDenoted_lam]
          refine ⟨trivial, IsTy_univ w, fun a _ => (hinner a b hb).2.2,
            fun _ => (univ w : V), fun a _ => (hinner a b hb).1, fun _ _ => IsTy_univ w⟩
        · intro b hb
          rw [hin b hb]
          exact lamR_mem fun a _ => (hinner a b hb).1

/-!
## The tagged sum carrier, spelled

The carrier body of a direct sum: the `.psigma [w, w]` node over the
tag domain `Nat` whose fibre is the numeral case split
(`caseAVAt`) over the constructors' tuple-tower bodies
(`towerBodyAV w Fs_i`), reading to the tier's `sumSet w (sumFibre …)`
(`ConLeche/SetModel/TaggedSum.lean`).  At `w = 0` the `.psigma` spelling
cannot serve (its pinned valuation reads the tag domain in `univ 0`),
so — as `sqBodyAV` — the squash carrier is spelt
classically, `¬ ∀ k : Nat, ¬ (case k)`, whose truth-value Π-types truncate
whatever their domains are; both spellings read to the ONE semantic
carrier, and `sigmaSet`'s zero test makes the two regimes one
statement (`sumBodyAV_interp`).

The type-former leaf `sumTyAV` is the λ-tower over the parameter
domains with this body; its laws consume one hereditary premise,
`ParamsOkS` — the parameter domains graded, with the per-constructor
chain grading `SumFieldsOkB` at the base.
-/

/-! ## The semantic fibres -/

/-- The `i`-th constructor's tower at the parameter frame, `empty`
beyond the constructor count. -/
noncomputable def sumFibre (w : Nat) (ρ : Nat → V) (Fss : List (List Term)) (i : Nat) : V :=
  match Fss[i]? with
  | some Fs => towerSet w (teleOfFields ρ Fs)
  | none => empty

theorem sumFibre_of_getElem? {w : Nat} {ρ : Nat → V} {Fss : List (List Term)} {i : Nat}
    {Fs : List Term} (h : Fss[i]? = some Fs) :
    sumFibre w ρ Fss i = towerSet w (teleOfFields ρ Fs) := by
  unfold sumFibre; rw [h]

theorem sumFibre_of_ge {w : Nat} {ρ : Nat → V} {Fss : List (List Term)} {i : Nat}
    (h : Fss.length ≤ i) : sumFibre w ρ Fss i = empty := by
  unfold sumFibre; rw [List.getElem?_eq_none h]

/-- Per-constructor hereditary grading: every constructor's chain is
`FieldsOkB`. -/
def SumFieldsOkB (w : Nat) (ρ : Nat → V) (Fss : List (List Term)) : Prop :=
  ∀ Fs ∈ Fss, FieldsOkB w ρ Fs

theorem SumFieldsOkB.bound {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (h : SumFieldsOkB w ρ Fss) : ∀ Fs ∈ Fss, w ≠ 0 → FieldsBound w ρ Fs :=
  fun Fs hFs hw => (h Fs hFs).toBound hw

/-- The selector over the tower bodies picks the semantic fibres. -/
theorem selFibre_towers {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (hb : ∀ Fs ∈ Fss, w ≠ 0 → FieldsBound w ρ Fs) (i : Nat) :
    selFibre ρ (Fss.map (towerBodyAV w)) i = sumFibre w ρ Fss i := by
  unfold selFibre sumFibre
  rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : Fss[i]? with
  | none => rfl
  | some Fs =>
    simp only [Option.map_some, Option.getD_some, Function.comp_def]
    exact towerBodyAV_interp (hb Fs (List.mem_of_getElem? h))

/-- The tower bodies are bounded and graded from the chains'. -/
theorem towers_facts {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) :
    (∀ T ∈ Fss.map (towerBodyAV w), interp V ρ T ∈ˢ (univ w : V)) ∧
    (∀ T ∈ Fss.map (towerBodyAV w), WellDenoted V ρ T) := by
  constructor
  · intro T hT
    obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
    rw [towerBodyAV_interp (fun hw => (hok Fs hFs).toBound hw)]
    exact towerSet_univ_of_okB (fun hw => (hok Fs hFs).toBound hw)
  · intro T hT
    obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
    exact towerBodyAV_wellDenoted (hok Fs hFs)

/-- The case split at a tag frame `d + 1` binders below the parameter
frame reads to the fibre function. -/
theorem case_fibre_at {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List Term)} (hok : SumFieldsOkB w ρp Fss) {k : V} (hk : k ∈ˢ (omega : V)) :
    interp V (cons k σ) (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0))
        = natFibre (sumFibre w ρp Fss) k ∧
      interp V (cons k σ) (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0))
        ∈ˢ (univ w : V) ∧
      WellDenoted V (cons k σ) (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)) := by
  have hsh' : shiftE (d + 1) 0 (cons k σ) = ρp := by rw [shiftE_succ_cons, hsh]
  obtain ⟨hT, hokT⟩ := towers_facts hok
  have h := caseAVAt_facts (w := w) (Ts := Fss.map (towerBodyAV w)) (d := d + 1) (k := .bvar 0)
    (σ := cons k σ) (by rw [hsh']; exact hT) (by rw [hsh']; exact hokT) trivial
    (by rw [interp_bvar]; exact hk)
  rw [hsh'] at h
  refine ⟨?_, h.1, h.2.2⟩
  obtain ⟨i, rfl, hfib⟩ := natFibre_of_mem (sumFibre w ρp Fss) hk
  rw [hfib, h.2.1 i (by rw [interp_bvar]; rfl), selFibre_towers hok.bound]

/-- The case split at the tag frame reads to the fibre function. -/
theorem case_fibre {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) {k : V} (hk : k ∈ˢ (omega : V)) :
    interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0))
        = natFibre (sumFibre w ρ Fss) k ∧
      interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0))
        ∈ˢ (univ w : V) ∧
      WellDenoted V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0)) :=
  case_fibre_at (d := 0) (shiftE_zero_zero ρ) hok hk

/-! ## The carrier body -/

/-- The carrier body, graph regime. -/
def sumBodyAVPos (w : Nat) (Fss : List (List Term)) : Term :=
  .app (.app (.const .psigma [w, w]) natAV)
    (.lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0)))

/-- The carrier body, squash regime: `¬ ∀ k : Nat, ¬ (case k)`. -/
def sqSumBodyAV (Fss : List (List Term)) : Term :=
  negAV (.pi natAV (negAV (caseAVAt 0 (Fss.map (towerBodyAV 0)) 1 (.bvar 0))))

/-- The carrier body, both regimes. -/
def sumBodyAV (w : Nat) (Fss : List (List Term)) : Term :=
  if w = 0 then sqSumBodyAV Fss else sumBodyAVPos w Fss

theorem sumBodyAV_zero (Fss : List (List Term)) : sumBodyAV 0 Fss = sqSumBodyAV Fss := ite_eq_left rfl

theorem sumBodyAV_pos {w : Nat} (hw : w ≠ 0) (Fss : List (List Term)) :
    sumBodyAV w Fss = sumBodyAVPos w Fss := ite_eq_right hw

/-- `ω` sits in every positive universe. -/
theorem omega_mem_univ_pos {w : Nat} (hw : w ≠ 0) : (omega : V) ∈ˢ univ w := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact omega_mem_univ_succ w'

/-- The squash body reads to the squash carrier. -/
theorem sqSumBodyAV_interp {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB 0 ρ Fss) :
    interp V ρ (sqSumBodyAV Fss) = sumSet 0 (sumFibre 0 ρ Fss) := by
  unfold sqSumBodyAV sumSet
  rw [interp_negAV, sigmaSet_zero]
  refine truthVal_congr ?_
  rw [interp_pi, piV_eq_zero (fun _ _ => by rw [interp_negAV]; exact truthVal_mem_univZero _),
    piR_zero, exists_mem_truthVal]
  have hin : ∀ k : V, k ∈ˢ (omega : V) →
      ((∃ y, y ∈ˢ interp V (cons k ρ) (negAV (caseAVAt 0 (Fss.map (towerBodyAV 0)) 1 (.bvar 0))))
        ↔ ¬ ∃ z, z ∈ˢ natFibre (sumFibre 0 ρ Fss) k) := by
    intro k hk
    rw [interp_negAV, (case_fibre hok hk).1, exists_mem_truthVal]
  constructor
  · intro h
    exact Classical.byContradiction fun hno =>
      h fun k hk => (hin k hk).mpr fun hz => hno ⟨k, hk, hz⟩
  · rintro ⟨k, hk, y, hy⟩ hall
    exact (hin k hk).mp (hall k hk) ⟨y, hy⟩

/-- The carrier's fibre λ over the tags (an inhabited domain, type
bodies) is the graph. -/
theorem sumFibreLam_eq {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) :
    interp V ρ (.lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0)))
      = lamR (w + 1) omega fun k =>
        interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0)) :=
  lamV_eq_pos (Nat.succ_ne_zero w) natzero_mem
    (IsTy_of_mem_univ (case_fibre hok natzero_mem).2.1).ne_pt

/-- The graph body reads to the graph carrier. -/
theorem sumBodyAVPos_interp {w : Nat} (hw : w ≠ 0) {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) :
    interp V ρ (sumBodyAVPos w Fss) = sumSet w (sumFibre w ρ Fss) := by
  have hbv : bval V .psigma [w, w] = psigmaV V w w := rfl
  have hB : (lamR (w + 1) omega fun k =>
        interp V (cons k ρ) (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0)))
      ∈ˢ psigmaFibreSpace V w omega :=
    lamR_mem_psigmaFibreSpace V natzero_mem fun k hk => (case_fibre hok hk).2.1
  show SetTheory.app (SetTheory.app (bval V .psigma [w, w]) omega)
      (interp V ρ (.lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) 1 (.bvar 0))))
    = sumSet w (sumFibre w ρ Fss)
  rw [sumFibreLam_eq hok, hbv, psigmaV_app V (omega_mem_univ_pos hw) hB, show Nat.max w w = w from Nat.max_self w]
  unfold sumSet
  exact sigma_congr fun k hk => by
    rw [app_lamR_pos (Nat.succ_ne_zero w) hk, (case_fibre hok hk).1]

/-- **The carrier body reads to the tier's carrier**, both regimes. -/
theorem sumBodyAV_interp {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) :
    interp V ρ (sumBodyAV w Fss) = sumSet w (sumFibre w ρ Fss) := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_interp hok
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_interp hw hok

/-- The carrier's formation, both regimes. -/
theorem sumSet_univ_of_okB {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) :
    sumSet w (sumFibre w ρ Fss) ∈ˢ (univ w : V) := by
  by_cases hw : w = 0
  · subst hw; rw [univ_zero]; exact sumSet_zero_mem_univZero _
  · refine sumSet_mem_univ hw fun i => ?_
    unfold sumFibre
    cases h : Fss[i]? with
    | none => exact empty_mem_univ w
    | some Fs => exact towerSet_univ_teleOfFields ((hok Fs (List.mem_of_getElem? h)).toBound hw)

/-- The carrier's formation in the strict universe, the least fixed
points' fibre space. -/
theorem sumSet_strictU_of_okB {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) :
    sumSet w (sumFibre w ρ Fss) ∈ˢ (strictU w : V) :=
  mem_strictU_of_univ (sumSet_univ_of_okB hok) fun hw => strict_sumSet hw _

/-- The squash body is graded. -/
theorem sqSumBodyAV_wellDenoted {ρ : Nat → V} {Fss : List (List Term)} (hok : SumFieldsOkB 0 ρ Fss) :
    WellDenoted V ρ (sqSumBodyAV Fss) := by
  unfold sqSumBodyAV negAV
  rw [WellDenoted_pi]
  refine ⟨?_, IsTy_piV, fun _ _ => by simp, fun _ _ => IsTy_empty⟩
  rw [WellDenoted_pi]
  refine ⟨trivial, IsTy_omega, fun k hk => ?_, fun _ _ => IsTy_piV⟩
  rw [WellDenoted_pi]
  exact ⟨(case_fibre hok hk).2.2, IsTy_of_mem_univ (case_fibre hok hk).2.1,
    fun _ _ => by simp, fun _ _ => IsTy_empty⟩

/-- The graph body is graded: the two `.psigma` slots from
`psigmaV_rr_mem`, the fibre λ from the selector's facts. -/
theorem sumBodyAVPos_wellDenoted {w : Nat} (hw : w ≠ 0) {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) : WellDenoted V ρ (sumBodyAVPos w Fss) := by
  have hbv : interp V ρ (.const .psigma [w, w]) = psigmaV V w w := rfl
  have hvac : ¬ w + 1 = 0 := Nat.succ_ne_zero w
  have hA : (omega : V) ∈ˢ univ w := omega_mem_univ_pos hw
  unfold sumBodyAVPos
  rw [WellDenoted_app]
  refine ⟨?_, ?_, ?_⟩
  · rw [WellDenoted_app]
    exact ⟨trivial, trivial, w + 1, univ w,
      fun A => piR (w + 1) (psigmaFibreSpace V w A) fun _ => (univ w : V),
      hbv ▸ psigmaV_rr_mem (V := V) w, hA, fun h => absurd h hvac,
      fun _ => IsTy_univ w⟩
  · rw [WellDenoted_lam]
    exact ⟨trivial, IsTy_omega, fun k hk => (case_fibre hok hk).2.2,
      fun _ => (univ w : V), fun k hk => (case_fibre hok hk).2.1,
      fun _ _ => IsTy_univ w⟩
  · refine ⟨w + 1, psigmaFibreSpace V w omega, fun _ => (univ w : V), ?_, ?_,
      fun h => absurd h hvac, fun _ => IsTy_piR _ _ _⟩
    · show SetTheory.app (interp V ρ (.const .psigma [w, w])) omega ∈ˢ _
      rw [hbv]
      exact app_mem_piR_pos hvac (psigmaV_rr_mem (V := V) w) hA
    · rw [sumFibreLam_eq hok]
      exact lamR_mem_psigmaFibreSpace V natzero_mem fun k hk => (case_fibre hok hk).2.1

/-- **The carrier body is graded**, both regimes. -/
theorem sumBodyAV_wellDenoted {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) : WellDenoted V ρ (sumBodyAV w Fss) := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_wellDenoted hok
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_wellDenoted hw hok

/-! ## The type-former leaf -/

/-- The type-former leaf of a direct sum: the λ-tower over the
parameter domains with the sum carrier body. -/
def sumTyAV (w : Nat) (pps : List Term) (Fss : List (List Term)) :
    Term :=
  mkLamsAV pps (sumBodyAV w Fss)

/-- `ParamsOkS`: the leaf's one hereditary premise — the parameter
domains graded types, with the per-constructor chain grading at the
base. -/
def ParamsOkS (w : Nat) (ρ : Nat → V) (Fss : List (List Term)) :
    List Term → Prop
  | [] => SumFieldsOkB w ρ Fss
  | d :: pps => WellDenoted V ρ d ∧ IsTy (interp V ρ d) ∧
      ∀ a, a ∈ˢ interp V ρ d → ParamsOkS w (cons a ρ) Fss pps

/-- **The leaf inhabits its type's reading.** -/
theorem sumTyAV_mem {w : Nat} {Fss : List (List Term)} :
    ∀ {pps : List Term} {ρ : Nat → V},
      ParamsOkS w ρ Fss pps →
      interp V ρ (sumTyAV w pps Fss) ∈ˢ interp V ρ (mkPisAV pps (.sort w))
  | [], ρ, h => by
    show interp V ρ (sumBodyAV w Fss) ∈ˢ (univ w : V)
    rw [sumBodyAV_interp h]
    exact sumSet_univ_of_okB h
  | d :: pps, ρ, h => by
    show (lamV (interp V ρ d)
        fun a => interp V (cons a ρ) (mkLamsAV pps (sumBodyAV w Fss)))
      ∈ˢ piV (interp V ρ d)
        fun a => interp V (cons a ρ) (mkPisAV pps (.sort w))
    exact lamV_mem (fun a ha => sumTyAV_mem (h.2.2 a ha))
      fun a _ => IsTy_mkPisAV_sort pps w (cons a ρ)

/-- **The leaf is graded.** -/
theorem sumTyAV_wellDenoted {w : Nat} {Fss : List (List Term)} :
    ∀ {pps : List Term} {ρ : Nat → V},
      ParamsOkS w ρ Fss pps → WellDenoted V ρ (sumTyAV w pps Fss)
  | [], _, h => sumBodyAV_wellDenoted h
  | d :: pps, ρ, h => by
    show WellDenoted V ρ (.lam d (mkLamsAV pps (sumBodyAV w Fss)))
    rw [WellDenoted_lam]
    exact ⟨h.1, h.2.1, fun a ha => sumTyAV_wellDenoted (h.2.2 a ha),
      ⟨fun a => interp V (cons a ρ) (mkPisAV pps (.sort w)),
       fun a ha => sumTyAV_mem (h.2.2 a ha),
       fun a _ => IsTy_mkPisAV_sort pps w (cons a ρ)⟩⟩

/-- **The leaf's application fold**: along a fitting parameter spine
the leaf computes the instantiated carrier. -/
theorem sumTyAV_fold {w : Nat} {Fss : List (List Term)}
    {pps : List Term} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ pps as)
    (hok : SumFieldsOkB w (consList as ρ) Fss) :
    as.foldl SetTheory.app (interp V ρ (sumTyAV w pps Fss))
      = sumSet w (sumFibre w (consList as ρ) Fss) := by
  rw [sumTyAV, mkLamsAV_fold hsp, sumBodyAV_interp hok]

/-!
## The index equation, spelled

An indexed family's carrier at an index tuple `ı⃗` is the tagged union
of the constructor towers **restricted** to the constructors' index
equations `e⃗_k f⃗ = ı⃗`.  The restriction is one extra proof-field per
constructor: the chain `Fs_k ++ [idxEqAV eqs_k]`, where `idxEqAV eqs`
spells the conjunction of the equations `eqs = [(e₀, ı₀), …]` as the
truth value

    ¬ (e₀ = ı₀ → e₁ = ı₁ → … → False)

with truth-value Π nodes and `eqE` equations (whose reading is the
equality's truth value, `eqv`).  Nothing here depends on how the
equations are spelled: `idxEqAV_interp` reads it to `truthVal (EqAll ρ
eqs)` (every left side interprets as its right side), `idxEqAV_wellDenoted`
grades it from the sides' gradings, and `idxEqAV_mem_univ` bounds it in
every universe (a truth value).  The chain-level facts
(`FieldsOkB_append_idxEq`, `spineFit_append_idxEq`) are what the fibre
construction consumes: a fitting spine of the restricted chain is a
fitting spine of the fields followed by the point, with the equations
holding at the fields.
-/

/-! ## The spelling -/

/-- `e₀ = ı₀ → e₁ = ı₁ → … → False`, each later equation lifted under
the earlier binders (the equations are scoped at the chain's head). -/
def eqChainAV : List (Term × Term) → Term
  | [] => .const .empty [0]
  | (a, b) :: r => .pi (.eqE a b) ((eqChainAV r).liftN 1 0)

/-- **The index equation**: the truth value of every equation holding. -/
def idxEqAV (eqs : List (Term × Term)) : Term := negAV (eqChainAV eqs)

/-- Every equation holds at `ρ`. -/
def EqAll (ρ : Nat → V) (eqs : List (Term × Term)) : Prop :=
  ∀ e ∈ eqs, interp V ρ e.1 = interp V ρ e.2

theorem EqAll_nil (ρ : Nat → V) : EqAll (V := V) ρ [] := fun _ h => nomatch h

theorem EqAll_cons {ρ : Nat → V} {a b : Term} {r : List (Term × Term)} :
    EqAll ρ ((a, b) :: r) ↔ interp V ρ a = interp V ρ b ∧ EqAll ρ r := by
  constructor
  · intro h
    exact ⟨h (a, b) List.mem_cons_self, fun e he => h e (List.mem_cons_of_mem _ he)⟩
  · rintro ⟨h1, h2⟩ e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact h1
    · exact h2 e he'

/-! ## The reading -/

/-- The chain reads to a truth value. -/
theorem eqChainAV_univZero :
    ∀ (eqs : List (Term × Term)) (ρ : Nat → V),
      interp V ρ (eqChainAV eqs) ∈ˢ (univZero : V)
  | [], _ => univ_zero (V := V) ▸ empty_mem_univ 0
  | (a, b) :: r, ρ => by
    show piV (eqv (interp V ρ a) (interp V ρ b))
      (fun x => interp V (cons x ρ) ((eqChainAV r).liftN 1 0)) ∈ˢ _
    rw [piV_eq_zero fun x _ => by
      rw [interp_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      exact eqChainAV_univZero r ρ]
    exact piR_zero_mem_univZero

/-- The chain is inhabited exactly when some equation fails. -/
theorem eqChainAV_inhab :
    ∀ (eqs : List (Term × Term)) (ρ : Nat → V),
      (∃ y, y ∈ˢ interp V ρ (eqChainAV eqs)) ↔ ¬ EqAll ρ eqs
  | [], ρ => by
    refine ⟨fun ⟨y, hy⟩ => absurd hy (not_mem_empty y), fun h => absurd (EqAll_nil ρ) h⟩
  | (a, b) :: r, ρ => by
    show (∃ y, y ∈ˢ piV (eqv (interp V ρ a) (interp V ρ b))
      fun x => interp V (cons x ρ) ((eqChainAV r).liftN 1 0)) ↔ _
    rw [piV_eq_zero fun x _ => by
      rw [interp_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
      exact eqChainAV_univZero r ρ]
    have heqv : eqv (interp V ρ a) (interp V ρ b)
        = truthVal (interp V ρ a = interp V ρ b) := by unfold eqv; rfl
    rw [heqv, piR_zero, exists_mem_truthVal, EqAll_cons]
    have hlift : ∀ x : V, interp V (cons x ρ) ((eqChainAV r).liftN 1 0)
        = interp V ρ (eqChainAV r) := fun x => by
      rw [interp_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons, shiftE_zero_zero]
    constructor
    · intro h ⟨hab, hall⟩
      have := h pt (pt_mem_truthVal hab)
      rw [hlift] at this
      exact (eqChainAV_inhab r ρ).mp this hall
    · intro h x hx
      rw [hlift]
      refine (eqChainAV_inhab r ρ).mpr fun hall => h ⟨of_mem_truthVal hx, hall⟩

/-- The chain reads to a type: `∅`, or a function space. -/
theorem IsTy_eqChainAV : ∀ (eqs : List (Term × Term)) (ρ : Nat → V),
    IsTy (interp V ρ (eqChainAV eqs))
  | [], _ => IsTy_empty
  | (_, _) :: _, _ => IsTy_piV

/-- **The index equation reads to the truth value of every equation
holding.** -/
theorem idxEqAV_interp (eqs : List (Term × Term)) (ρ : Nat → V) :
    interp V ρ (idxEqAV eqs) = truthVal (EqAll ρ eqs) := by
  unfold idxEqAV
  rw [interp_negAV]
  refine truthVal_congr ?_
  rw [eqChainAV_inhab]
  exact ⟨fun h => Classical.byContradiction h, fun h h' => h' h⟩

/-- A truth value sits in every universe. -/
theorem truthVal_mem_univ (p : Prop) (w : Nat) : (truthVal p : V) ∈ˢ univ w :=
  univ_mono (Nat.zero_le w) _ (univ_zero (V := V) ▸ truthVal_mem_univZero p)

theorem idxEqAV_mem_univ (eqs : List (Term × Term)) (ρ : Nat → V) (w : Nat) :
    interp V ρ (idxEqAV eqs) ∈ˢ (univ w : V) := by
  rw [idxEqAV_interp]; exact truthVal_mem_univ _ w

/-- The point inhabits the index equation exactly when every equation
holds. -/
theorem pt_mem_idxEqAV {eqs : List (Term × Term)} {ρ : Nat → V} :
    (pt : V) ∈ˢ interp V ρ (idxEqAV eqs) ↔ EqAll ρ eqs := by
  rw [idxEqAV_interp, mem_truthVal]
  exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩

theorem mem_idxEqAV {eqs : List (Term × Term)} {ρ : Nat → V} {x : V}
    (hx : x ∈ˢ interp V ρ (idxEqAV eqs)) : x = pt ∧ EqAll ρ eqs := by
  rw [idxEqAV_interp, mem_truthVal] at hx
  exact ⟨hx.2, hx.1⟩

/-! ## The grading -/

/-- The equations' sides graded at `ρ`. -/
def EqsOk (ρ : Nat → V) (eqs : List (Term × Term)) : Prop :=
  ∀ e ∈ eqs, WellDenoted V ρ e.1 ∧ WellDenoted V ρ e.2

theorem eqChainAV_wellDenoted :
    ∀ {eqs : List (Term × Term)} {ρ : Nat → V}, EqsOk ρ eqs →
      WellDenoted V ρ (eqChainAV eqs)
  | [], _, _ => trivial
  | (a, b) :: r, ρ, hok => by
    show WellDenoted V ρ (.pi (.eqE a b) ((eqChainAV r).liftN 1 0))
    rw [WellDenoted_pi, WellDenoted_eqE]
    refine ⟨hok (a, b) List.mem_cons_self, IsTy_eqv _ _, fun x _ => ?_, fun x _ => ?_⟩
    · rw [WellDenoted_liftN, show (1 : Nat) = 0 + 1 from rfl, shiftE_succ_cons,
        shiftE_zero_zero]
      exact eqChainAV_wellDenoted fun e he => hok e (List.mem_cons_of_mem _ he)
    · rw [interp_liftN]; exact IsTy_eqChainAV r _

/-- **The index equation is graded** from its sides' gradings. -/
theorem idxEqAV_wellDenoted {eqs : List (Term × Term)} {ρ : Nat → V} (hok : EqsOk ρ eqs) :
    WellDenoted V ρ (idxEqAV eqs) := by
  unfold idxEqAV negAV
  rw [WellDenoted_pi]
  exact ⟨eqChainAV_wellDenoted hok, IsTy_eqChainAV eqs ρ, fun _ _ => trivial,
    fun _ _ => IsTy_empty⟩

/-! ## The restricted chain -/

/-- The restricted chain `Fs ++ [idxEqAV eqs]` is graded when the
fields are and the equations' sides are graded at every fitting field
frame. -/
theorem FieldsOkB_append_idxEq {w : Nat} {eqs : List (Term × Term)} :
    ∀ {Fs : List Term} {ρ : Nat → V}, FieldsOkB w ρ Fs →
      (∀ bs : List V, SpineFit ρ Fs bs → EqsOk (consList bs ρ) eqs) →
      FieldsOkB w ρ (Fs ++ [idxEqAV eqs])
  | [], ρ, _, hE => by
    refine ⟨idxEqAV_wellDenoted (by simpa [consList] using hE [] trivial),
      IsTy_of_mem_univ (idxEqAV_mem_univ eqs ρ 0),
      fun _ => idxEqAV_mem_univ eqs ρ w, fun _ _ => trivial⟩
  | F :: Fs, ρ, hok, hE => by
    refine ⟨hok.1, hok.2.1, hok.2.2.1, fun a ha => ?_⟩
    refine FieldsOkB_append_idxEq (hok.2.2.2 a ha) fun bs hsp => ?_
    have := hE (a :: bs) ⟨ha, hsp⟩
    rwa [consList_cons] at this

/-- A spine fits the restricted chain exactly when it is a fitting
field spine followed by the point, with every equation holding at the
fields. -/
theorem spineFit_append_idxEq {Fs : List Term} {eqs : List (Term × Term)}
    {ρ : Nat → V} {as : List V} :
    SpineFit ρ (Fs ++ [idxEqAV eqs]) as ↔
      ∃ bs, as = bs ++ [pt] ∧ SpineFit ρ Fs bs ∧ EqAll (consList bs ρ) eqs := by
  constructor
  · intro h
    obtain ⟨bs, cs, rfl, hsp, hE⟩ := spineFit_append_inv h
    match cs, hE with
    | [], hE => exact hE.elim
    | [c], hE =>
      obtain ⟨rfl, hall⟩ := mem_idxEqAV hE.1
      exact ⟨bs, rfl, hsp, hall⟩
    | _ :: _ :: _, hE => exact hE.2.elim
  · rintro ⟨bs, rfl, hsp, hall⟩
    exact hsp.append ⟨pt_mem_idxEqAV.mpr hall, trivial⟩

/-- The restricted tower's intro: a fitting field spine at which the
equations hold puts the point-terminated tuple in the tower (graph
regime) and the point in the squash. -/
theorem restricted_member_intro {w : Nat} {Fs : List Term} {eqs : List (Term × Term)}
    {ρ : Nat → V} {bs : List V} (hsp : SpineFit ρ Fs bs) (hall : EqAll (consList bs ρ) eqs) :
    (if w = 0 then (pt : V) else mkTower (bs ++ [pt]))
      ∈ˢ towerSet w (teleOfFields ρ (Fs ++ [idxEqAV eqs])) := by
  have hsp' : SpineFit ρ (Fs ++ [idxEqAV eqs]) (bs ++ [pt]) :=
    spineFit_append_idxEq.mpr ⟨bs, rfl, hsp, hall⟩
  split
  · next hz => exact hz ▸ pt_mem_tower_teleOfFields hsp'
  · next hnz => exact mkTower_mem_teleOfFields hnz hsp'

/-! ## Bounds -/

theorem eqChainAV_below {k : Nat} :
    ∀ {eqs : List (Term × Term)},
      (∀ e ∈ eqs, Term.bvarsBelow k e.1 ∧ Term.bvarsBelow k e.2) →
      Term.bvarsBelow k (eqChainAV eqs)
  | [], _ => trivial
  | (a, b) :: r, h => by
    refine ⟨⟨(h (a, b) List.mem_cons_self).1, (h (a, b) List.mem_cons_self).2⟩, ?_⟩
    exact VExprAux.bvarsBelow_liftN 1 _ k 0
      (eqChainAV_below fun e he => h e (List.mem_cons_of_mem _ he))

theorem idxEqAV_below {k : Nat} {eqs : List (Term × Term)}
    (h : ∀ e ∈ eqs, Term.bvarsBelow k e.1 ∧ Term.bvarsBelow k e.2) :
    Term.bvarsBelow k (idxEqAV eqs) :=
  ⟨eqChainAV_below h, trivial⟩

/-- The restricted chain is bounded when the fields are and the
equations are bounded at the field frame. -/
theorem DomsBelow_append_idxEq {eqs : List (Term × Term)} :
    ∀ {Fs : List Term} {k : Nat}, DomsBelow k Fs →
      (∀ e ∈ eqs, Term.bvarsBelow (k + Fs.length) e.1 ∧
        Term.bvarsBelow (k + Fs.length) e.2) →
      DomsBelow k (Fs ++ [idxEqAV eqs])
  | [], k, _, h => ⟨idxEqAV_below (by simpa using h), trivial⟩
  | F :: Fs, k, hb, h => by
    refine ⟨hb.1, DomsBelow_append_idxEq hb.2 ?_⟩
    intro e he
    have := h e he
    rwa [List.length_cons, show k + (Fs.length + 1) = k + 1 + Fs.length from by omega] at this

/-! ## Lifting a chain into a deeper frame -/

/-- A field chain lifted by `n` at cutoff `k` (domain `i` at cutoff
`k + i`, as `liftDoms` does for binder domains). -/
def liftFields (n : Nat) : Nat → List Term → List Term
  | _, [] => []
  | k, F :: Fs => F.liftN n k :: liftFields n (k + 1) Fs

@[simp] theorem liftFields_cons (n k : Nat) (F : Term) (Fs : List Term) :
    liftFields n k (F :: Fs) = F.liftN n k :: liftFields n (k + 1) Fs := rfl

theorem liftFields_length (n : Nat) :
    ∀ (Fs : List Term) (k : Nat), (liftFields n k Fs).length = Fs.length
  | [], _ => rfl
  | _ :: Fs, k => by simp [liftFields_length n Fs (k + 1)]

/-- A spine fits the lifted chain at `σ` exactly when it fits the
chain at the shifted frame. -/
theorem spineFit_liftFields (n : Nat) :
    ∀ {Fs : List Term} {k : Nat} {σ : Nat → V} {as : List V},
      SpineFit σ (liftFields n k Fs) as ↔ SpineFit (shiftE n k σ) Fs as
  | [], _, _, [] => Iff.rfl
  | [], _, _, _ :: _ => Iff.rfl
  | _ :: _, _, _, [] => Iff.rfl
  | F :: Fs, k, σ, a :: as => by
    simp only [liftFields_cons, SpineFit, interp_liftN]
    rw [cons_shiftE]
    exact and_congr Iff.rfl (spineFit_liftFields n)

/-- The lifted chain's grading is the chain's at the shifted frame. -/
theorem FieldsOkB_liftFields {w n : Nat} :
    ∀ {Fs : List Term} {k : Nat} {σ : Nat → V},
      FieldsOkB w σ (liftFields n k Fs) ↔ FieldsOkB w (shiftE n k σ) Fs
  | [], _, _ => Iff.rfl
  | F :: Fs, k, σ => by
    simp only [liftFields_cons, FieldsOkB, WellDenoted_liftN, interp_liftN]
    refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (forall_congr' fun a => imp_congr Iff.rfl ?_)))
    rw [cons_shiftE]
    exact FieldsOkB_liftFields

theorem DomsBelow_liftFields {n : Nat} :
    ∀ {Fs : List Term} {k K : Nat}, k ≤ K → DomsBelow K Fs →
      DomsBelow (K + n) (liftFields n k Fs)
  | [], _, _, _, _ => trivial
  | F :: Fs, k, K, hk, hb => by
    refine ⟨?_, ?_⟩
    · exact VExprAux.bvarsBelow_liftN n _ K k hb.1
    · have := DomsBelow_liftFields (n := n) (Fs := Fs) (k := k + 1) (K := K + 1)
        (by omega) hb.2
      rwa [show K + 1 + n = K + n + 1 from by omega] at this

/-! ## The restricted chains of an indexed family

A constructor's field chain `Fs` is scoped at the parameter frame, its
index expressions `Es` at the constructor frame (parameters, then the
`nF` fields).  At a frame `d` binders below the parameters whose LAST
`nIdx` binders are the index variables — `(p⃗, ı⃗)` for the former's
leaf, `(p⃗, motive, minors, ı⃗)` for the recursor's — the restricted
chain is the lifted field chain followed by the index equation
`e⃗ = ı⃗` (each `e_l` lifted under the `d` binders past the fields, the
index variable `ı_l` at `nF + nIdx - 1 - l`). -/

/-- The equations `e_l = ı_l` at a frame `d` below the parameters,
under `nF` fields. -/
def idxEqsAt (d nIdx nF : Nat) (Es : List Term) : List (Term × Term) :=
  (List.range nIdx).map fun l => ((Es.getD l default).liftN d nF, .bvar (nF + nIdx - 1 - l))

/-- Constructor's restricted chain at a frame `d` below the parameters. -/
def rChain (d nIdx : Nat) (Fs : List Term) (Es : List Term) : List Term :=
  liftFields d 0 Fs ++ [idxEqAV (idxEqsAt d nIdx Fs.length Es)]

/-- The restricted chains of all constructors. -/
def rChains (d nIdx : Nat) (Fss : List (List Term)) (Ess : List (List Term)) :
    List (List Term) :=
  List.zipWith (rChain d nIdx) Fss Ess

theorem rChains_getElem? (d nIdx : Nat) (Fss Ess : List (List Term)) (j : Nat) :
    (rChains d nIdx Fss Ess)[j]? = match Fss[j]?, Ess[j]? with
      | some Fs, some Es => some (rChain d nIdx Fs Es)
      | _, _ => none := by
  simp only [rChains, List.getElem?_zipWith]
  cases Fss[j]? <;> cases Ess[j]? <;> rfl

/-- The frame's index tuple: the last `nIdx` binders' values, the first
index first. -/
def frameIdx (nIdx : Nat) (σ : Nat → V) : List V :=
  (List.range nIdx).map fun l => σ (nIdx - 1 - l)

omit [SetTheory V] in
theorem frameIdx_eq_reverse_map (n : Nat) (σ : Nat → V) :
    frameIdx n σ = (List.range n).reverse.map σ := by
  apply List.ext_getElem
  · simp [frameIdx]
  · intro l h1 h2
    simp only [frameIdx, List.getElem_map, List.getElem_reverse, List.getElem_range]
    simp only [List.length_range]

/-- A constructor's index tuple at a field spine, read at the
parameter frame. -/
noncomputable def idxValsAt (ρp : Nat → V) (Es : List Term) (bs : List V) : List V :=
  Es.map (interp V (consList bs ρp))

omit [SetTheory V] in
theorem shiftE_consList_len' (n : Nat) :
    ∀ (as : List V) (k : Nat) (σ : Nat → V),
      shiftE n (as.length + k) (consList as σ) = consList as (shiftE n k σ)
  | [], k, σ => by simp [consList]
  | a :: as, k, σ => by
    rw [consList_cons, consList_cons, List.length_cons,
      show as.length + 1 + k = as.length + (k + 1) from by omega,
      shiftE_consList_len' n as (k + 1) (cons a σ), cons_shiftE]

omit [SetTheory V] in
theorem shiftE_consList_len (n : Nat) (as : List V) (σ : Nat → V) :
    shiftE n as.length (consList as σ) = consList as (shiftE n 0 σ) := by
  have := shiftE_consList_len' n as 0 σ
  rwa [Nat.add_zero] at this

theorem getD_mem_of_lt {l : Nat} {Es : List Term} (hl : l < Es.length) :
    Es.getD l default ∈ Es := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
  exact List.getElem_mem hl

/-- **The index equation at a fitting spine**: every `e_l = ı_l` holds
exactly when the constructor's index tuple at the fields is the
frame's index tuple. -/
theorem EqAll_idxEqsAt {d nIdx nF : Nat} {Es : List Term} (hEs : Es.length = nIdx)
    {σ : Nat → V} {bs : List V} (hbs : bs.length = nF) :
    EqAll (consList bs σ) (idxEqsAt d nIdx nF Es) ↔
      idxValsAt (shiftE d 0 σ) Es bs = frameIdx nIdx σ := by
  have hvar : ∀ l, l < nIdx →
      interp V (consList bs σ) (.bvar (nF + nIdx - 1 - l)) = σ (nIdx - 1 - l) := by
    intro l hl
    rw [interp_bvar, show nF + nIdx - 1 - l = (nIdx - 1 - l) + bs.length from by omega,
      consList_apply_add]
  have hlift : ∀ E : Term, interp V (consList bs σ) (E.liftN d nF)
      = interp V (consList bs (shiftE d 0 σ)) E := by
    intro E
    rw [interp_liftN, ← hbs, shiftE_consList_len]
  -- the pointwise form of the equation
  have hpt : EqAll (consList bs σ) (idxEqsAt d nIdx nF Es) ↔
      ∀ l, l < nIdx → interp V (consList bs (shiftE d 0 σ)) (Es.getD l default)
        = σ (nIdx - 1 - l) := by
    unfold EqAll idxEqsAt
    constructor
    · intro h l hl
      have := h ((Es.getD l default).liftN d nF, .bvar (nF + nIdx - 1 - l))
        (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)
      simp only at this
      rwa [hlift, hvar l hl] at this
    · intro h e he
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
      simp only
      rw [hlift, hvar l (List.mem_range.mp hl)]
      exact h l (List.mem_range.mp hl)
  rw [hpt]
  unfold idxValsAt frameIdx
  constructor
  · intro h
    apply List.ext_getElem
    · simp [hEs]
    · intro l h1 h2
      have hl : l < nIdx := by simpa using h2
      simp only [List.getElem_map, List.getElem_range]
      have := h l hl
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        at this
  · intro h l hl
    have := congrArg (fun xs : List V => xs[l]?) h
    simp only [List.getElem?_map, List.getElem?_range hl, Option.map_some] at this
    rw [List.getElem?_eq_getElem (by omega), Option.map_some, Option.some.injEq] at this
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact this

/-!
## The sum constructor leaf

Constructor `j` of a direct sum is the λ-tower
over its type reading's binder domains with the **injection** body: the
pinned pair constructor applied to the tag domain, the case-split
fibre, the numeral `j` and the constructor's own tupler.  Every
constructor tower carries one extra proof-field —
the index equation at the family's carrier, the trivially true
`idxEqAV []` at the constructor's own leaf — so the tupler is
`mkTowerGoU`: the tuple of the fields followed by the point.  It reads
to `inj j (mkTower (f⃗ ++ [pt]))` in the graph regime and to the point
at squash (`psigmaMkV`'s own collapse — `injW`), and its laws consume
`MkPreS`, with the per-constructor chain grading and the constructor's
index at the base; the type reading's
body is only required to read to SOME tagged union whose `j`-th fibre
holds the tuple (at an indexed family that fibre is the restricted
tower at the constructor's own index tuple).
-/

/-! ## The injection, spelled at a frame -/

/-- `PSigma'.mk Nat (λ k, case k) tag payload`, spelled `d` binders below
the parameter frame (the tower bodies are scoped there). -/
def sumInjAtAV (w : Nat) (Fss : List (List Term)) (d : Nat) (tag payload : Term) : Term :=
  Term.mkAppN (.const .psigmaMk [w, w])
    [natAV, .lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)),
      tag, payload]

/-- The semantic injection, both regimes: the point at squash. -/
noncomputable def injW (w i : Nat) (a : V) : V := if w = 0 then pt else inj i a

theorem injW_zero (i : Nat) (a : V) : injW 0 i a = pt := ite_eq_left rfl
theorem injW_pos {w : Nat} (hw : w ≠ 0) (i : Nat) (a : V) : injW w i a = inj i a := ite_eq_right hw

/-- The injection's value lands in the carrier. -/
theorem injW_mem {w : Nat} {f : Nat → V} {i : Nat} {a : V} (ha : a ∈ˢ f i) :
    injW w i a ∈ˢ sumSet w f := by
  by_cases hw : w = 0
  · subst hw; rw [injW_zero]; exact pt_mem_sumSet_zero ha
  · rw [injW_pos hw]; exact inj_mem hw ha

/-- The case-split fibre λ at a frame. -/
theorem sumFibreLam_facts {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List Term)} (hok : SumFieldsOkB w ρp Fss) :
    interp V σ (.lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))
        = lamR (w + 1) omega (natFibre (sumFibre w ρp Fss)) ∧
      lamR (w + 1) (omega : V) (natFibre (sumFibre w ρp Fss)) ∈ˢ psigmaFibreSpace V w omega ∧
      WellDenoted V σ (.lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0))) := by
  refine ⟨?_, ?_, ?_⟩
  · show lamV omega _ = _
    rw [lamV_congr fun k hk => (case_fibre_at hsh hok hk).1]
    refine lamV_eq_pos (Nat.succ_ne_zero w) natzero_mem (IsTy_of_mem_univ (n := w) ?_).ne_pt
    rw [← (case_fibre_at hsh hok natzero_mem).1]
    exact (case_fibre_at hsh hok natzero_mem).2.1
  · refine lamR_mem_psigmaFibreSpace V natzero_mem fun k hk => ?_
    rw [← (case_fibre_at hsh hok hk).1]
    exact (case_fibre_at hsh hok hk).2.1
  · rw [WellDenoted_lam]
    exact ⟨trivial, IsTy_omega, fun k hk => (case_fibre_at hsh hok hk).2.2,
      fun _ => (univ w : V), fun k hk => (case_fibre_at hsh hok hk).2.1,
      fun _ _ => IsTy_univ w⟩

/-- **The injection reads to `injW`**: the pair at a numeral tag with
a fitting payload, the point at squash. -/
theorem sumInjAtAV_interp {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List Term)} (hok : SumFieldsOkB w ρp Fss) {tag payload : Term} {i : Nat}
    (htag : interp V σ tag = vnat i)
    (hpay : w ≠ 0 → interp V σ payload ∈ˢ sumFibre w ρp Fss i) :
    interp V σ (sumInjAtAV w Fss d tag payload) = injW w i (interp V σ payload) := by
  obtain ⟨hBv, hBm, -⟩ := sumFibreLam_facts hsh hok
  show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (bval V .psigmaMk [w, w])
    omega) (interp V σ (.lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))))
    (interp V σ tag)) (interp V σ payload) = _
  rw [hBv, htag]
  by_cases hw : w = 0
  · subst hw
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkV V 0 0) _) _) _) _ = _
    rw [psigmaMkV_eq_pt V (show Nat.max 0 0 = 0 from rfl), app_pt, app_pt, app_pt, app_pt,
      injW_zero]
  · have hpay' : interp V σ payload
        ∈ˢ SetTheory.app (lamR (w + 1) omega (natFibre (sumFibre w ρp Fss))) (vnat i) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) (vnat_mem_omega i), natFibre_vnat]
      exact hpay hw
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkV V w w) _) _) _) _ = _
    rw [psigmaMkV_app V (omega_mem_univ_pos hw) hBm (vnat_mem_omega i) hpay',
      show Nat.max w w = w from Nat.max_self w, ite_eq_right hw, injW_pos hw]
    rfl

/-- **The injection is graded**: in the graph regime the four slots
are the pair constructor's product chain, at squash the head is the
point and the slots are trivial. -/
theorem sumInjAtAV_wellDenoted {w : Nat} {ρp σ : Nat → V} {d : Nat} (hsh : shiftE d 0 σ = ρp)
    {Fss : List (List Term)} (hok : SumFieldsOkB w ρp Fss) {tag payload : Term} {i : Nat}
    (hoktag : WellDenoted V σ tag) (htag : interp V σ tag = vnat i)
    (hokpay : WellDenoted V σ payload)
    (hpay : w ≠ 0 → interp V σ payload ∈ˢ sumFibre w ρp Fss i) :
    WellDenoted V σ (sumInjAtAV w Fss d tag payload) := by
  obtain ⟨hBv, hBm, hBok⟩ := sumFibreLam_facts hsh hok
  by_cases hw : w = 0
  · subst hw
    refine (mkAppN_wellDenoted_of_pt_head (f := .const .psigmaMk [0, 0]) (σ := σ) trivial ?_ ?_).1
    · exact psigmaMkV_eq_pt V (show Nat.max 0 0 = 0 from rfl)
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl
      · trivial
      · exact hBok
      · exact hoktag
      · exact hokpay
  · have hbv : interp V σ (.const .psigmaMk [w, w]) = psigmaMkV V w w := rfl
    have hA : (omega : V) ∈ˢ univ w := omega_mem_univ_pos hw
    have hm0 := psigmaMkV_ww_mem (V := V) w
    have hm1 := app_mem_piV hm0 hA
    have hm2 := app_mem_piV hm1 hBm
    have hm3 := app_mem_piV hm2 (vnat_mem_omega i)
    have hpay' : interp V σ payload
        ∈ˢ SetTheory.app (lamR (w + 1) omega (natFibre (sumFibre w ρp Fss))) (vnat i) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) (vnat_mem_omega i), natFibre_vnat]
      exact hpay hw
    show WellDenoted V σ (.app (.app (.app (.app (.const .psigmaMk [w, w]) natAV)
      (.lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))) tag) payload)
    rw [WellDenoted_app]
    refine ⟨?_, hokpay, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨?_, hoktag, ?_⟩
      · rw [WellDenoted_app]
        refine ⟨?_, hBok, ?_⟩
        · rw [WellDenoted_app]
          exact ⟨trivial, trivial, by rw [hbv]; exact piV_slot hm0 hA (IsTy_univ w)⟩
        · show ∃ v A B, SetTheory.app (interp V σ (.const .psigmaMk [w, w])) omega
            ∈ˢ piR v A B ∧ _
          rw [hbv, hBv]; exact piV_slot hm1 hBm IsTy_piV
      · show ∃ v A B, SetTheory.app (SetTheory.app (interp V σ (.const .psigmaMk [w, w])) omega)
          (interp V σ (.lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0))))
          ∈ˢ piR v A B ∧ _
        rw [hbv, hBv, htag]; exact piV_slot hm2 (vnat_mem_omega i) IsTy_omega
    · show ∃ v A B, SetTheory.app (SetTheory.app (SetTheory.app
        (interp V σ (.const .psigmaMk [w, w])) omega)
        (interp V σ (.lam natAV (caseAVAt w (Fss.map (towerBodyAV w)) (d + 1) (.bvar 0)))))
        (interp V σ tag) ∈ˢ piR v A B ∧ _
      rw [hbv, hBv, htag]
      exact piV_slot hm3 hpay' (IsTy_of_mem_univ (psigmaFibre_apply V hBm (vnat_mem_omega i)))

/-! ## The tupler with the proof-field terminator

`mkTowerGoU w Fs E` spells `mkTower (f⃗ ++ [pt])` at the constructor
λ-frame: `mkTowerGoPos`'s tower over the chain `Fs ++ [E]`, whose last
component — the proof-field `E`, scoped at the full field frame — is
valued by `.prf` rather than by a binder.  Its facts are
`mkTowerGoPos`'s with one extra base case. -/

/-- The proof-field-terminated tupler, graph regime. -/
def mkTowerGoUPos (w : Nat) (E : Term) : List Term → Term
  | [] =>
    .app (.app (.app (.app (.const .psigmaMk [w, w]) E)
        (.lam E (.const .punit [w]))) .prf)
      (.const .punitUnit [w])
  | F :: Fs =>
    .app (.app (.app (.app (.const .psigmaMk [w, w])
        (F.liftN (Fs.length + 1)))
        (.lam (F.liftN (Fs.length + 1))
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)))
        (.bvar Fs.length))
      (mkTowerGoUPos w E Fs)

/-- The tupler, both regimes: the point at squash. -/
def mkTowerGoU (w : Nat) (Fs : List Term) (E : Term) : Term :=
  if w = 0 then .const .punitUnit [] else mkTowerGoUPos w E Fs

theorem mkTowerGoU_zero (Fs : List Term) (E : Term) :
    mkTowerGoU 0 Fs E = .const .punitUnit [] := ite_eq_left rfl

theorem mkTowerGoU_pos {w : Nat} (hw : w ≠ 0) (Fs : List Term) (E : Term) :
    mkTowerGoU w Fs E = mkTowerGoUPos w E Fs := ite_eq_right hw

/-- The tupler at a fitting spine with the proof-field inhabited by the
point reads to the point-terminated tuple. -/
theorem mkTowerGoUPos_interp {w : Nat} (hw : w ≠ 0) {E : Term} :
    ∀ {Fs : List Term} {ρp : Nat → V} {bs : List V},
      FieldsBound w ρp (Fs ++ [E]) → SpineFit ρp Fs bs →
      (pt : V) ∈ˢ interp V (consList bs ρp) E →
      interp V (consList bs ρp) (mkTowerGoUPos w E Fs) = mkTower (bs ++ [pt])
  | [], ρp, [], hb, _, hpt => by
    have hA : interp V ρp E ∈ˢ (univ w : V) := hb.1
    have hpt' : (pt : V) ∈ˢ interp V ρp E := by simpa [consList] using hpt
    have hB : (lamR (w + 1) (interp V ρp E) fun _ => (unitSetAt w : V))
        ∈ˢ psigmaFibreSpace V w (interp V ρp E) :=
      lamR_mem_psigmaFibreSpace V hpt' fun _ _ => unitSetAt_mem_univ w
    have hb' : (unitAt w : V) ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp E) fun _ => (unitSetAt w : V)) pt := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hpt']
      exact unitAt_mem_unitSetAt w
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (bval V .psigmaMk [w, w])
        (interp V ρp E)) (lamV (interp V ρp E) fun _ => (unitSetAt w : V))) pt) (unitAt w)
      = mkTower [pt]
    have hbv : bval V .psigmaMk [w, w] = psigmaMkV V w w := rfl
    rw [lamV_eq_pos (Nat.succ_ne_zero w) hpt' (IsTy_of_mem_univ (unitSetAt_mem_univ w)).ne_pt,
      hbv, psigmaMkV_app V hA hB hpt' hb', show Nat.max w w = w from Nat.max_self w, ite_eq_right hw,
      unitAt_pos hw]
    rfl
  | [], _, _ :: _, _, hsp, _ => hsp.elim
  | _ :: _, _, [], _, hsp, _ => hsp.elim
  | F :: Fs, ρp, b :: bs, hb, hsp, hpt => by
    simp only [List.cons_append] at hb
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    have hA : interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp V ρp F := by
      rw [interp_liftN, hshift]
    have hBfun : ∀ x : V,
        interp V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)
        = interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])) := fun x => by
      rw [interp_liftN, ← cons_shiftE, hshift]
    have hval : consList bs (cons b ρp) (Fs.length) = b := by
      rw [← hlen, show bs.length = 0 + bs.length by rw [Nat.zero_add],
        consList_apply_add bs (cons b ρp) 0, cons_zero]
    have hrec : interp V (consList bs (cons b ρp)) (mkTowerGoUPos w E Fs)
        = mkTower (bs ++ [pt]) :=
      mkTowerGoUPos_interp hw (hb.2 b hsp.1) hsp.2 hpt
    have hAm : interp V ρp F ∈ˢ (univ w : V) := hb.1
    have hBm : (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])))
        ∈ˢ psigmaFibreSpace V w (interp V ρp F) :=
      lamR_mem_psigmaFibreSpace V hsp.1 fun x hx => by
        rw [towerBodyAV_interp (fun _ => hb.2 x hx)]
        exact towerSet_univ_teleOfFields (hb.2 x hx)
    have hfib : SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) b
        = towerSet w (teleOfFields (cons b ρp) (Fs ++ [E])) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hsp.1,
        towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
    have hbm : mkTower (bs ++ [pt])
        ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) b := by
      rw [hfib]
      refine mkTower_mem_teleOfFields hw (spineFit_append_inv_mpr hsp.2 ?_)
      show SpineFit (consList bs (cons b ρp)) [E] [pt]
      exact ⟨hpt, trivial⟩
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (bval V .psigmaMk [w, w])
        (interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))))
        (lamV
          (interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1)))
          fun x => interp V (cons x (consList bs (cons b ρp)))
            ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)))
        (consList bs (cons b ρp) Fs.length))
        (interp V (consList bs (cons b ρp)) (mkTowerGoUPos w E Fs))
      = mkTower (b :: bs ++ [pt])
    have hbv : bval V .psigmaMk [w, w] = psigmaMkV V w w := rfl
    rw [hA, hval, hrec]
    have hBeq : (fun x => interp V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1))
        = fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])) :=
      funext hBfun
    have hlam : (lamV (interp V ρp F) fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])))
        = lamR (w + 1) (interp V ρp F) fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])) :=
      lamV_eq_pos (Nat.succ_ne_zero w) hsp.1 (by
        rw [towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
        exact (IsTy_of_mem_univ (towerSet_univ_teleOfFields (hb.2 b hsp.1))).ne_pt)
    rw [hBeq, hlam, hbv, psigmaMkV_app V hAm hBm hsp.1 hbm,
      show Nat.max w w = w from Nat.max_self w, ite_eq_right hw]
    rfl
where
  spineFit_append_inv_mpr {ρ : Nat → V} {Fs Gs : List Term} {as bs : List V}
      (h1 : SpineFit ρ Fs as) (h2 : SpineFit (consList as ρ) Gs bs) :
      SpineFit ρ (Fs ++ Gs) (as ++ bs) := h1.append h2

/-- **The tupler reads to the point-terminated tuple**, both regimes. -/
theorem mkTowerGoU_interp {w : Nat} {E : Term} {Fs : List Term} {ρp : Nat → V}
    {bs : List V} (hb : w ≠ 0 → FieldsBound w ρp (Fs ++ [E])) (hsp : SpineFit ρp Fs bs)
    (hpt : (pt : V) ∈ˢ interp V (consList bs ρp) E) :
    interp V (consList bs ρp) (mkTowerGoU w Fs E)
      = if w = 0 then pt else mkTower (bs ++ [pt]) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGoU_zero, ite_eq_left rfl]; rfl
  · rw [mkTowerGoU_pos hw, ite_eq_right hw]; exact mkTowerGoUPos_interp hw (hb hw) hsp hpt

/-- The tupler is graded (graph regime). -/
theorem mkTowerGoUPos_wellDenoted {w : Nat} (hw : w ≠ 0) {E : Term} :
    ∀ {Fs : List Term} {ρp : Nat → V} {bs : List V},
      FieldsOkB w ρp (Fs ++ [E]) → SpineFit ρp Fs bs →
      (pt : V) ∈ˢ interp V (consList bs ρp) E →
      WellDenoted V (consList bs ρp) (mkTowerGoUPos w E Fs)
  | [], ρp, [], hok, _, hpt => by
    have hokE : WellDenoted V ρp E := hok.1
    have hA : interp V ρp E ∈ˢ (univ w : V) := hok.2.2.1 hw
    have hpt' : (pt : V) ∈ˢ interp V ρp E := by simpa [consList] using hpt
    have hBm : (lamR (w + 1) (interp V ρp E) fun _ => (unitSetAt w : V))
        ∈ˢ psigmaFibreSpace V w (interp V ρp E) :=
      lamR_mem_psigmaFibreSpace V hpt' fun _ _ => unitSetAt_mem_univ w
    have hbv : interp V ρp (.const .psigmaMk [w, w]) = psigmaMkV V w w := rfl
    have hm0 := psigmaMkV_ww_mem (V := V) w
    have hm1 := app_mem_piV hm0 hA
    have hm2 := app_mem_piV hm1 hBm
    have hm3 := app_mem_piV hm2 hpt'
    have hlam : interp V ρp (.lam E (.const .punit [w]))
        = lamR (w + 1) (interp V ρp E) fun _ => (unitSetAt w : V) :=
      lamV_eq_pos (Nat.succ_ne_zero w) hpt' (IsTy_of_mem_univ (unitSetAt_mem_univ w)).ne_pt
    have hb' : (unitAt w : V) ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp E) fun _ => (unitSetAt w : V)) pt := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hpt']
      exact unitAt_mem_unitSetAt w
    show WellDenoted V ρp (.app (.app (.app (.app (.const .psigmaMk [w, w]) E)
      (.lam E (.const .punit [w]))) .prf) (.const .punitUnit [w]))
    rw [WellDenoted_app]
    refine ⟨?_, trivial, ?_⟩
    · rw [WellDenoted_app]
      refine ⟨?_, trivial, ?_⟩
      · rw [WellDenoted_app]
        refine ⟨?_, ?_, ?_⟩
        · rw [WellDenoted_app]
          exact ⟨trivial, hokE, by rw [hbv]; exact piV_slot hm0 hA (IsTy_univ w)⟩
        · rw [WellDenoted_lam]
          exact ⟨hokE, IsTy_of_mem_univ hA, fun _ _ => trivial, fun _ => (univ w : V),
            fun _ _ => unitSetAt_mem_univ w, fun _ _ => IsTy_univ w⟩
        · show ∃ v A B, SetTheory.app (interp V ρp (.const .psigmaMk [w, w])) (interp V ρp E)
            ∈ˢ piR v A B ∧ _
          rw [hbv, hlam]; exact piV_slot hm1 hBm IsTy_piV
      · show ∃ v A B, SetTheory.app (SetTheory.app (interp V ρp (.const .psigmaMk [w, w]))
          (interp V ρp E)) (interp V ρp (.lam E (.const .punit [w]))) ∈ˢ piR v A B ∧ _
        rw [hbv, hlam, interp_prf]; exact piV_slot hm2 hpt' (IsTy_of_mem_univ hA)
    · show ∃ v A B, SetTheory.app (SetTheory.app (SetTheory.app
        (interp V ρp (.const .psigmaMk [w, w]))
        (interp V ρp E)) (interp V ρp (.lam E (.const .punit [w]))))
        (interp V ρp .prf) ∈ˢ piR v A B ∧ _
      rw [hbv, hlam, interp_prf]
      exact piV_slot hm3 hb' (by
        rw [app_lamR_pos (Nat.succ_ne_zero w) hpt']
        exact IsTy_of_mem_univ (unitSetAt_mem_univ w))
  | [], _, _ :: _, _, hsp, _ => hsp.elim
  | _ :: _, _, [], _, hsp, _ => hsp.elim
  | F :: Fs, ρp, b :: bs, hok, hsp, hpt => by
    simp only [List.cons_append] at hok
    have hb : FieldsBound w ρp (F :: (Fs ++ [E])) := hok.toBound hw
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    have hA : interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp V ρp F := by
      rw [interp_liftN, hshift]
    have hBfun : ∀ x : V,
        interp V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)
        = interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])) := fun x => by
      rw [interp_liftN, ← cons_shiftE, hshift]
    have hval : consList bs (cons b ρp) (Fs.length) = b := by
      rw [← hlen, show bs.length = 0 + bs.length by rw [Nat.zero_add],
        consList_apply_add bs (cons b ρp) 0, cons_zero]
    have hrec : interp V (consList bs (cons b ρp)) (mkTowerGoUPos w E Fs)
        = mkTower (bs ++ [pt]) :=
      mkTowerGoUPos_interp hw (hb.2 b hsp.1) hsp.2 hpt
    have hAm : interp V ρp F ∈ˢ (univ w : V) := hb.1
    have hBv : interp V (consList bs (cons b ρp))
        (Term.lam (F.liftN (Fs.length + 1))
          ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1))
        = lamR (w + 1) (interp V ρp F)
            (fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) := by
      rw [interp_lam, hA, funext hBfun]
      exact lamV_eq_pos (Nat.succ_ne_zero w) hsp.1 (by
        rw [towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
        exact (IsTy_of_mem_univ (towerSet_univ_teleOfFields (hb.2 b hsp.1))).ne_pt)
    have hBm : (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E])))
        ∈ˢ psigmaFibreSpace V w (interp V ρp F) :=
      lamR_mem_psigmaFibreSpace V hsp.1 fun x hx => by
        rw [towerBodyAV_interp (fun _ => hb.2 x hx)]
        exact towerSet_univ_teleOfFields (hb.2 x hx)
    have hm0 := psigmaMkV_ww_mem (V := V) w
    have hm1 := app_mem_piV hm0 hAm
    have hm2 := app_mem_piV hm1 hBm
    have hm3 := app_mem_piV hm2 hsp.1
    have hfib : SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) b
        = towerSet w (teleOfFields (cons b ρp) (Fs ++ [E])) := by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hsp.1,
        towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
    have hrm : interp V (consList bs (cons b ρp)) (mkTowerGoUPos w E Fs)
        ∈ˢ SetTheory.app (lamR (w + 1) (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w (Fs ++ [E]))) b := by
      rw [hrec, hfib]
      exact mkTower_mem_teleOfFields hw (hsp.2.append ⟨hpt, trivial⟩)
    show WellDenoted V (consList bs (cons b ρp))
      (.app (.app (.app (.app (.const .psigmaMk [w, w])
          (F.liftN (Fs.length + 1)))
          (.lam (F.liftN (Fs.length + 1))
            ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1)))
          (.bvar Fs.length))
        (mkTowerGoUPos w E Fs))
    rw [WellDenoted_app]
    refine ⟨?_, mkTowerGoUPos_wellDenoted hw (hok.2.2.2 b hsp.1) hsp.2 hpt, ?_⟩
    · -- the triple-application head
      rw [WellDenoted_app]
      refine ⟨?_, trivial, ?_⟩
      · -- the double-application head
        rw [WellDenoted_app]
        refine ⟨?_, ?_, ?_⟩
        · rw [WellDenoted_app]
          refine ⟨trivial, ?_, ?_⟩
          · rw [WellDenoted_liftN, hshift]
            exact hok.1
          · exact piV_slot hm0 (by rw [interp_liftN, hshift]; exact hAm) (IsTy_univ w)
        · rw [WellDenoted_lam]
          refine ⟨?_, ?_, ?_, ?_⟩
          · rw [WellDenoted_liftN, hshift]
            exact hok.1
          · rw [hA]; exact hok.2.1
          · intro x hx
            rw [hA] at hx
            rw [WellDenoted_liftN, ← cons_shiftE, hshift]
            exact towerBodyAV_wellDenoted (hok.2.2.2 x hx)
          · refine ⟨fun _ => (univ w : V), fun x hx => ?_, fun _ _ => IsTy_univ w⟩
            rw [hA] at hx
            rw [hBfun x, towerBodyAV_interp (fun _ => hb.2 x hx)]
            exact towerSet_univ_teleOfFields (hb.2 x hx)
        · show ∃ v A B, SetTheory.app (interp V (consList bs (cons b ρp))
                (.const .psigmaMk [w, w]))
              (interp V (consList bs (cons b ρp))
                (F.liftN (Fs.length + 1))) ∈ˢ piR v A B ∧ _
          rw [hA, hBv]
          exact piV_slot hm1 hBm IsTy_piV
      · show ∃ v A B, SetTheory.app (SetTheory.app
              (interp V (consList bs (cons b ρp))
                (.const .psigmaMk [w, w]))
              (interp V (consList bs (cons b ρp))
                (F.liftN (Fs.length + 1))))
            (interp V (consList bs (cons b ρp))
              (.lam (F.liftN (Fs.length + 1))
                ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1))) ∈ˢ piR v A B ∧ _
        rw [hA, hBv, interp_bvar, hval]
        exact piV_slot hm2 hsp.1 hok.2.1
    · show ∃ v A B, SetTheory.app (SetTheory.app (SetTheory.app
          (interp V (consList bs (cons b ρp))
            (.const .psigmaMk [w, w]))
          (interp V (consList bs (cons b ρp))
            (F.liftN (Fs.length + 1))))
          (interp V (consList bs (cons b ρp))
            (.lam (F.liftN (Fs.length + 1))
              ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1))))
        (interp V (consList bs (cons b ρp)) (.bvar Fs.length)) ∈ˢ piR v A B ∧ _
      rw [hA, hBv, interp_bvar, hval]
      exact piV_slot hm3 hrm (by
        rw [hfib]; exact IsTy_of_mem_univ (towerSet_univ_teleOfFields (hb.2 b hsp.1)))

/-- **The tupler is graded**, both regimes. -/
theorem mkTowerGoU_wellDenoted {w : Nat} {E : Term} {Fs : List Term} {ρp : Nat → V}
    {bs : List V} (hok : FieldsOkB w ρp (Fs ++ [E])) (hsp : SpineFit ρp Fs bs)
    (hpt : (pt : V) ∈ˢ interp V (consList bs ρp) E) :
    WellDenoted V (consList bs ρp) (mkTowerGoU w Fs E) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGoU_zero]; simp
  · rw [mkTowerGoU_pos hw]; exact mkTowerGoUPos_wellDenoted hw hok hsp hpt

/-! ## The unit-restricted chains -/

/-- The constructor leaf's chains: every constructor's field chain
followed by the trivially true index equation (the extra proof-field
is the point). -/
def uChains (Fss : List (List Term)) : List (List Term) :=
  Fss.map fun Fs => Fs ++ [idxEqAV []]

theorem uChains_getElem? (Fss : List (List Term)) (j : Nat) :
    (uChains Fss)[j]? = Fss[j]?.map fun Fs => Fs ++ [idxEqAV []] := by
  simp [uChains]

/-- The unit-restricted chains are graded when the chains are. -/
theorem SumFieldsOkB_uChains {w : Nat} {ρ : Nat → V} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρ Fss) : SumFieldsOkB w ρ (uChains Fss) := by
  intro Fs' hFs'
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hFs'
  exact FieldsOkB_append_idxEq (hok Fs hFs) fun _ _ _ h => nomatch h

/-- The trivially true index equation holds. -/
theorem pt_mem_idxEqAV_nil (ρ : Nat → V) : (pt : V) ∈ˢ interp V ρ (idxEqAV []) :=
  pt_mem_idxEqAV.mpr (EqAll_nil ρ)

/-! ## The constructor leaf -/

/-- **Constructor `j`'s leaf**: the λ-tower
over the constructor type reading's binder domains with the injection
of the point-terminated tupler at the numeral `j`. -/
def sumMkAV (w j : Nat) (ds : List Term) (Fs : List Term)
    (Fss : List (List Term)) : Term :=
  mkLamsAV ds (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV [])))

/-- `MkPreS`: the constructor leaf's ONE hereditary premise — each
parameter domain graded and a type, and under every fitting parameter spine every
constructor's chain is graded, this constructor's chain is the `j`-th,
and the type reading's body reads back as SOME tagged union whose
`j`-th fibre holds the point-terminated tuple. -/
def MkPreS (w j : Nat) (ρ : Nat → V) (Fs : List Term) (Fss : List (List Term))
    (bodyC : Term) : List Term → Prop
  | [] => SumFieldsOkB w ρ Fss ∧ Fss[j]? = some (Fs ++ [idxEqAV []]) ∧ ∀ bs, SpineFit ρ Fs bs →
      ∃ f : Nat → V, interp V (consList bs ρ) bodyC = sumSet w f ∧
        (if w = 0 then (pt : V) else mkTower (bs ++ [pt])) ∈ˢ f j
  | d :: pds => WellDenoted V ρ d ∧ IsTy (interp V ρ d) ∧
      ∀ a, a ∈ˢ interp V ρ d → MkPreS w j (cons a ρ) Fs Fss bodyC pds

/-- The injection body at a fitting field frame: its value and its
grading. -/
theorem sumInj_at_fields {w j : Nat} {ρp : Nat → V} {Fs : List Term}
    {Fss : List (List Term)} {bs : List V}
    (hok : SumFieldsOkB w ρp Fss) (hj : Fss[j]? = some (Fs ++ [idxEqAV []]))
    (hsp : SpineFit ρp Fs bs) :
    interp V (consList bs ρp)
        (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV [])))
        = injW w j (if w = 0 then pt else mkTower (bs ++ [pt])) ∧
      WellDenoted V (consList bs ρp)
        (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV []))) := by
  have hokF : FieldsOkB w ρp (Fs ++ [idxEqAV []]) := hok _ (List.mem_of_getElem? hj)
  have hlen : bs.length = Fs.length := hsp.length_eq
  have hsh : shiftE Fs.length 0 (consList bs ρp) = ρp := by rw [← hlen]; exact shiftE_consList bs ρp
  have hpt : (pt : V) ∈ˢ interp V (consList bs ρp) (idxEqAV []) := pt_mem_idxEqAV_nil _
  have hmk := mkTowerGoU_interp (w := w) (fun hw => hokF.toBound hw) hsp hpt
  have hpay : w ≠ 0 → interp V (consList bs ρp) (mkTowerGoU w Fs (idxEqAV []))
      ∈ˢ sumFibre w ρp Fss j := by
    intro hw
    rw [hmk, ite_eq_right hw, sumFibre_of_getElem? hj]
    exact mkTower_mem_teleOfFields hw (hsp.append ⟨hpt, trivial⟩)
  have hv := sumInjAtAV_interp hsh hok (interp_numeralAV j _) hpay
  rw [hmk] at hv
  exact ⟨hv, sumInjAtAV_wellDenoted hsh hok (numeralAV_wellDenoted j _) (interp_numeralAV j _)
    (mkTowerGoU_wellDenoted hokF hsp hpt) hpay⟩

/-- The field phase of the constructor leaf's premise (the walk
carries the prefix spine). -/
theorem underTowerOkS_fields {w j : Nat} {bodyC : Term} {ρp : Nat → V}
    {Fs : List Term} {Fss : List (List Term)}
    (hok : SumFieldsOkB w ρp Fss) (hj : Fss[j]? = some (Fs ++ [idxEqAV []]))
    (hbody : ∀ bs : List V, SpineFit ρp Fs bs →
      ∃ f : Nat → V, interp V (consList bs ρp) bodyC = sumSet w f ∧
        (if w = 0 then (pt : V) else mkTower (bs ++ [pt])) ∈ˢ f j) :
    ∀ {rest : List Term} {pre : List Term} {bs : List V},
      Fs = pre ++ rest → SpineFit ρp pre bs →
      UnderTowerOk (consList bs ρp)
        (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV []))) bodyC rest
  | [], pre, bs, hsplit, hsp => by
    have hspF : SpineFit ρp Fs bs := by
      rw [hsplit, List.append_nil]; exact hsp
    obtain ⟨hv, hok2⟩ := sumInj_at_fields hok hj hspF
    obtain ⟨f, hf, hmem⟩ := hbody bs hspF
    refine ⟨hok2, ?_, ?_⟩
    · rw [hf, hv]; exact injW_mem hmem
    · rw [hf]; exact IsTy_sumSet w f
  | d :: rest, pre, bs, hsplit, hsp => by
    have hokF : FieldsOkB w ρp (Fs ++ [idxEqAV []]) := hok _ (List.mem_of_getElem? hj)
    have hd : FieldsOkB w (consList bs ρp) (d :: (rest ++ [idxEqAV []])) := by
      have := FieldsOkB.drop (Fs₁ := pre) (Fs₂ := d :: (rest ++ [idxEqAV []]))
        (by rw [hsplit, List.append_assoc] at hokF; simpa using hokF) hsp
      exact this
    refine ⟨hd.1, hd.2.1, fun a ha => ?_⟩
    have hstep : UnderTowerOk (consList (bs ++ [a]) ρp)
        (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV []))) bodyC rest :=
      underTowerOkS_fields hok hj hbody (pre := pre ++ [d])
        (by rw [hsplit, List.append_assoc, List.singleton_append])
        (hsp.append ⟨ha, trivial⟩)
    rwa [consList_append, consList_cons, consList_nil] at hstep

/-- The parameter phase: `MkPreS` walks down to the field phase. -/
theorem underTowerOk_of_mkPreS {w j : Nat} {bodyC : Term}
    {Fs : List Term} {Fss : List (List Term)} {fds : List Term} :
    ∀ {pds : List Term} {ρ : Nat → V},
      MkPreS w j ρ Fs Fss bodyC pds → Fs = fds →
      UnderTowerOk ρ (sumInjAtAV w Fss Fs.length (numeralAV j) (mkTowerGoU w Fs (idxEqAV [])))
        bodyC (pds ++ fds)
  | [], ρ, h, hFs =>
    underTowerOkS_fields h.1 h.2.1 h.2.2 (pre := []) (bs := []) (by simpa using hFs) trivial
  | d :: pds, ρ, h, hFs =>
    ⟨h.1, h.2.1, fun a ha => underTowerOk_of_mkPreS (h.2.2 a ha) hFs⟩

/-- **The constructor leaf inhabits its type's reading.** -/
theorem sumMkAV_mem {w j : Nat} {bodyC : Term} {ρ : Nat → V}
    {Fss : List (List Term)} {pds fds : List Term}
    (hpre : MkPreS w j ρ fds Fss bodyC pds) :
    interp V ρ (sumMkAV w j (pds ++ fds) fds Fss)
      ∈ˢ interp V ρ (mkPisAV (pds ++ fds) bodyC) :=
  mkLamsAV_mem (underTowerOk_of_mkPreS hpre rfl)

/-- **The constructor leaf is graded.** -/
theorem sumMkAV_wellDenoted {w j : Nat} {bodyC : Term} {ρ : Nat → V}
    {Fss : List (List Term)} {pds fds : List Term}
    (hpre : MkPreS w j ρ fds Fss bodyC pds) :
    WellDenoted V ρ (sumMkAV w j (pds ++ fds) fds Fss) :=
  mkLamsAV_wellDenoted (underTowerOk_of_mkPreS hpre rfl)

/-- **The constructor leaf's application fold** (graph regime): along
a fitting parameter + field spine the leaf computes the injection of
the point-terminated tupler. -/
theorem sumMkAV_fold {w j : Nat} (hw : w ≠ 0)
    {pds fds : List Term} {Fss : List (List Term)} {ρ : Nat → V}
    {as bs : List V}
    (hsp₁ : SpineFit ρ pds as)
    (hsp₂ : SpineFit (consList as ρ) fds bs)
    (hok : SumFieldsOkB w (consList as ρ) Fss)
    (hj : Fss[j]? = some (fds ++ [idxEqAV []])) :
    (as ++ bs).foldl SetTheory.app
        (interp V ρ (sumMkAV w j (pds ++ fds) fds Fss))
      = inj j (mkTower (bs ++ [pt])) := by
  have hsp : SpineFit ρ (pds ++ fds) (as ++ bs) := hsp₁.append hsp₂
  rw [sumMkAV, mkLamsAV_fold hsp,
    consList_append, (sumInj_at_fields hok hj hsp₂).1, ite_eq_right hw, injW_pos hw]

/-- **The constructor leaf at a squash instantiation is the point.** -/
theorem sumMkAV_zero {j : Nat} {ds : List Term} {Fs : List Term}
    {Fss : List (List Term)} {ρ : Nat → V} :
    interp V ρ (sumMkAV 0 j ds Fs Fss) = (pt : V) := by
  match ds with
  | [] =>
    show interp V ρ (sumInjAtAV 0 Fss Fs.length (numeralAV j) (mkTowerGoU 0 Fs (idxEqAV []))) = pt
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app (psigmaMkV V 0 0) _) _) _) _ = _
    rw [psigmaMkV_eq_pt V (show Nat.max 0 0 = 0 from rfl), app_pt, app_pt, app_pt, app_pt]
  | d :: ds =>
    show lamV _ (fun x => interp V (cons x ρ) (sumMkAV 0 j ds Fs Fss)) = pt
    exact lamV_eq_pt fun _ _ => sumMkAV_zero

/-! ## Application chains -/

/-- The application chain `M i₀ … i_{k-1}` is graded: each prefix is a
member of a function space the next index inhabits. -/
def AppChainOk (M : V) (is : List V) : Prop :=
  ∀ l, l < is.length → ∃ (v : Nat) (A : V) (B : V → V),
    (is.take l).foldl SetTheory.app M ∈ˢ piR v A B ∧ is.getD l pt ∈ˢ A ∧
    (v = 0 → ∀ x, x ∈ˢ A → B x ∈ˢ (univZero : V)) ∧ (v ≠ 0 → IsTy A)

/-- An application spine graded by the chain: its grading and its
value as the fold. -/
theorem mkAppN_wellDenoted_of_chain :
    ∀ {args : List Term} {f : Term} {σ : Nat → V},
      WellDenoted V σ f → (∀ a ∈ args, WellDenoted V σ a) →
      AppChainOk (interp V σ f) (args.map (interp V σ)) →
      WellDenoted V σ (Term.mkAppN f args) ∧
        interp V σ (Term.mkAppN f args)
          = (args.map (interp V σ)).foldl SetTheory.app (interp V σ f)
  | [], _, _, hf, _, _ => ⟨hf, rfl⟩
  | a :: args, f, σ, hf, hargs, hchain => by
    obtain ⟨v, A, B, hm, ha, hz, hA⟩ := hchain 0 (by simp)
    simp only [List.take_zero, List.foldl_nil, List.map_cons, List.getD_cons_zero] at hm ha
    have hoka : WellDenoted V σ (.app f a) := by
      rw [WellDenoted_app]
      exact ⟨hf, hargs a List.mem_cons_self, v, A, B, hm, ha, hz, hA⟩
    have hchain' : AppChainOk (interp V σ (.app f a)) (args.map (interp V σ)) := by
      intro l hl
      obtain ⟨v', A', B', hm', ha', hz', hA'⟩ := hchain (l + 1) (by simpa using hl)
      simp only [List.map_cons, List.take_succ_cons, List.foldl_cons, List.getD_cons_succ] at hm' ha'
      exact ⟨v', A', B', hm', ha', hz', hA'⟩
    have ih := mkAppN_wellDenoted_of_chain (args := args) (f := .app f a) hoka
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha')) hchain'
    rw [Term.mkAppN_cons]
    exact ⟨ih.1, by rw [ih.2, List.map_cons, List.foldl_cons]; rfl⟩

namespace RecHypCore

variable {ℓ w : Nat} {ρ₀ : Nat → V} {Fss Ess : List (List Term)} {Ids : List Term}
  {famAt : List V → V}

end RecHypCore

/-! ## The sources -/

/-- The sources' values at an index tuple. -/
noncomputable def srcVals (is : List V) (src : List (Option Nat)) : List V :=
  src.map fun s => match s with
    | some l => is.getD l pt
    | none => pt

/-!
## The sum leaves' syntactic battery

The closedness rows of the sum leaves: bound-variable bounds of their
erasures, one structural walk per spelled former.  The tower bodies
are scoped at the frame `K` and lifted by the depth `d` where they are
used, so every lifted use is bounded at `K + d` (`bvarsBelow_liftN`).
-/

/-! ## The case split -/

theorem natSortMotiveAV_below (w k : Nat) :
    Term.bvarsBelow k (natSortMotiveAV w) :=
  ⟨trivial, trivial⟩

theorem natRecAV_below {u : Nat} {M z s kx : Term} {k : Nat}
    (hM : Term.bvarsBelow k M) (hz : Term.bvarsBelow k z)
    (hs : Term.bvarsBelow k s) (hk : Term.bvarsBelow k kx) :
    Term.bvarsBelow k (natRecAV u M z s kx) :=
  ⟨⟨⟨⟨trivial, hM⟩, hz⟩, hs⟩, hk⟩

/-- The selector at depth `K + d` over spellings bounded at `K`. -/
theorem caseAVAt_below {w K : Nat} :
    ∀ {Ts : List Term} {d : Nat} {kx : Term},
      (∀ T ∈ Ts, Term.bvarsBelow K T) →
      Term.bvarsBelow (K + d) kx →
      Term.bvarsBelow (K + d) (caseAVAt w Ts d kx)
  | [], _, _, _, _ => trivial
  | T :: Ts, d, kx, hT, hk => by
    refine natRecAV_below (natSortMotiveAV_below w _) ?_ ?_ hk
    · exact VExprAux.bvarsBelow_liftN d T K 0 (hT T List.mem_cons_self)
    · refine ⟨trivial, trivial, ?_⟩
      have := caseAVAt_below (w := w) (K := K) (Ts := Ts) (d := d + 2) (kx := .bvar 1)
        (fun T' hT' => hT T' (List.mem_cons_of_mem _ hT'))
        (show (1 : Nat) < K + (d + 2) by omega)
      rwa [show K + (d + 2) = K + d + 1 + 1 from by omega] at this

/-! ## The carrier -/

theorem towers_below {w K : Nat} {Fss : List (List Term)}
    (h : ∀ Fs ∈ Fss, DomsBelow K Fs) :
    ∀ T ∈ Fss.map (towerBodyAV w), Term.bvarsBelow K T := by
  intro T hT
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hT
  exact towerBodyAV_below (h Fs hFs)

theorem sumBodyAVPos_below {w K : Nat} {Fss : List (List Term)}
    (h : ∀ Fs ∈ Fss, DomsBelow K Fs) :
    Term.bvarsBelow K (sumBodyAVPos w Fss) := by
  refine ⟨⟨trivial, trivial⟩, trivial, ?_⟩
  have := caseAVAt_below (w := w) (K := K) (Ts := Fss.map (towerBodyAV w)) (d := 1)
    (kx := .bvar 0) (towers_below h) (show (0 : Nat) < K + 1 by omega)
  exact this

theorem sqSumBodyAV_below {K : Nat} {Fss : List (List Term)}
    (h : ∀ Fs ∈ Fss, DomsBelow K Fs) :
    Term.bvarsBelow K (sqSumBodyAV Fss) := by
  refine ⟨⟨trivial, ⟨?_, trivial⟩⟩, trivial⟩
  have := caseAVAt_below (w := 0) (K := K) (Ts := Fss.map (towerBodyAV 0)) (d := 1)
    (kx := .bvar 0) (towers_below h) (show (0 : Nat) < K + 1 by omega)
  exact this

theorem sumBodyAV_below {w K : Nat} {Fss : List (List Term)}
    (h : ∀ Fs ∈ Fss, DomsBelow K Fs) :
    Term.bvarsBelow K (sumBodyAV w Fss) := by
  by_cases hw : w = 0
  · subst hw; rw [sumBodyAV_zero]; exact sqSumBodyAV_below h
  · rw [sumBodyAV_pos hw]; exact sumBodyAVPos_below h

/-- **The type-former leaf is bounded.** -/
theorem sumTyAV_below {w : Nat} {pps : List Term}
    {Fss : List (List Term)} {k : Nat} (hp : DomsBelow k pps)
    (hF : ∀ Fs ∈ Fss, DomsBelow (k + pps.length) Fs) :
    Term.bvarsBelow k (sumTyAV w pps Fss) :=
  mkLamsAV_below hp (sumBodyAV_below hF)

/-! ## The constructor -/

theorem sumInjAtAV_below {w K : Nat} {Fss : List (List Term)} {d : Nat}
    {tag payload : Term} (h : ∀ Fs ∈ Fss, DomsBelow K Fs)
    (ht : Term.bvarsBelow (K + d) tag) (hp : Term.bvarsBelow (K + d) payload) :
    Term.bvarsBelow (K + d) (sumInjAtAV w Fss d tag payload) := by
  refine ⟨⟨⟨⟨trivial, trivial⟩, trivial, ?_⟩, ht⟩, hp⟩
  have := caseAVAt_below (w := w) (K := K) (Ts := Fss.map (towerBodyAV w)) (d := d + 1)
    (kx := .bvar 0) (towers_below h) (show (0 : Nat) < K + (d + 1) by omega)
  rwa [show K + (d + 1) = K + d + 1 from by omega] at this

/-- The point-terminated tupler (graph regime): bounded at the full
field frame. -/
theorem mkTowerGoUPos_below {w : Nat} {E : Term} :
    ∀ {Fs : List Term} {k : Nat}, DomsBelow k (Fs ++ [E]) →
      Term.bvarsBelow (k + Fs.length) (mkTowerGoUPos w E Fs)
  | [], k, h => by
    have hE : Term.bvarsBelow k E := h.1
    exact ⟨⟨⟨⟨trivial, hE⟩, hE, trivial⟩, trivial⟩, trivial⟩
  | F :: Fs, k, h => by
    simp only [List.cons_append] at h
    have hF : Term.bvarsBelow (k + (Fs.length + 1))
        (F.liftN (Fs.length + 1)) := by
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1) F k 0 h.1
      exact this
    have hbody : Term.bvarsBelow (k + (Fs.length + 1) + 1)
        ((towerBodyAV w (Fs ++ [E])).liftN (Fs.length + 1) 1) := by
      have := VExprAux.bvarsBelow_liftN (Fs.length + 1)
        (towerBodyAV w (Fs ++ [E])) (k + 1) 1 (towerBodyAV_below h.2)
      rw [show k + 1 + (Fs.length + 1) = k + (Fs.length + 1) + 1
        by omega] at this
      exact this
    have hrec : Term.bvarsBelow (k + (Fs.length + 1))
        (mkTowerGoUPos w E Fs) := by
      have := mkTowerGoUPos_below (w := w) (E := E) (Fs := Fs) (k := k + 1) h.2
      rw [show k + 1 + Fs.length = k + (Fs.length + 1) by omega] at this
      exact this
    exact ⟨⟨⟨⟨trivial, hF⟩, hF, hbody⟩,
      show Fs.length < k + (Fs.length + 1) by omega⟩, hrec⟩

/-- The point-terminated tupler, both regimes. -/
theorem mkTowerGoU_below {w : Nat} {Fs : List Term} {E : Term} {k : Nat}
    (h : DomsBelow k (Fs ++ [E])) :
    Term.bvarsBelow (k + Fs.length) (mkTowerGoU w Fs E) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGoU_zero]; trivial
  · rw [mkTowerGoU_pos hw]; exact mkTowerGoUPos_below h

/-- The unit-restricted chains are bounded when the chains are. -/
theorem uChains_below {K : Nat} {Fss : List (List Term)} (h : ∀ Fs ∈ Fss, DomsBelow K Fs) :
    ∀ Fs' ∈ uChains Fss, DomsBelow K Fs' := by
  intro Fs' hFs'
  obtain ⟨Fs, hFs, rfl⟩ := List.mem_map.mp hFs'
  exact DomsBelow_append_idxEq (h Fs hFs) fun _ h => nomatch h

/-- **The constructor leaf is bounded** (`hlen` is the frame
accounting: the field frame ends at the binder tower's). -/
theorem sumMkAV_below {w j : Nat} {ds : List Term}
    {Fs : List Term} {Fss : List (List Term)} {k nP : Nat} (hd : DomsBelow k ds)
    (hF : DomsBelow (k + nP) Fs) (hFss : ∀ Fs' ∈ Fss, DomsBelow (k + nP) Fs')
    (hlen : nP + Fs.length = ds.length) :
    Term.bvarsBelow k (sumMkAV w j ds Fs Fss) :=
  mkLamsAV_below hd (by
    have hmk := mkTowerGoU_below (w := w) (E := idxEqAV [])
      (DomsBelow_append_idxEq hF fun _ h => nomatch h)
    have := sumInjAtAV_below (w := w) (K := k + nP) (Fss := Fss) (d := Fs.length)
      (tag := numeralAV j) (payload := mkTowerGoU w Fs (idxEqAV [])) hFss (numeralAV_below j _) hmk
    rwa [show k + nP + Fs.length = k + ds.length from by omega] at this)

end ConLeche.Semantics
