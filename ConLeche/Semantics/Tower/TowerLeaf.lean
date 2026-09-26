module

public import ConLeche.Semantics.Tower.TowerIntro
public import ConLeche.Semantics.BasisOk
@[expose] public section

/-!
# The carrier body and the uniform projection spelling (task #175, stage 2)

The value-introduction half of the direct-structure bridge: the tier's
semantic values must be *stored*, and the P dialect stores constant
denotations as closed `AnnotTerm` leaves over the `BConst` alphabet
(`EnvModel.acval`).  This module supplies the two body spellings and
their interpretation equations:

* `towerBodyAV w Fs` — the carrier, spelled through `.psigma` at level
  instantiation `[w, w]` with a `unitSet` terminator (`.punit`).  Two
  interface facts make this land exactly on the tier's `towerSet w`:
  `sigmaSet` reads its level only through the zero test
  (`sigmaSet_pos`/`sigmaSet_zero`), so `max w w = w` closes the level
  bookkeeping; and the fibre λ's annotation is the *codomain type's*
  sort `w + 1 ≠ 0`, so the fibre computes by `app_lamR_pos` in **both**
  regimes and `sigma_congr` rewrites it to the tier's fibre.  The
  premises of `psigmaV_app` are exactly `FieldsBound w` — O5 plus
  cumulativity, nothing else.

* `projAV i` — the tier's structure-independent `projS i = sfst ∘
  ssnd^i`, spelled by the iterated projection formers `.fst ∘ .snd^i`.
  No type arguments, no entry consultation; `projAV_interp` is the
  definitional commutation.  The *definition* and `projAV_interp` live
  one layer down (`Semantics/BasisType.lean`, `Semantics/BasisOk.lean`),
  because a basis constant's type — `lfpTuple k`'s index-set tuple —
  reads its arguments with them; the lifting/instantiation laws are
  here.

`towerBodyAV_wellDenoted` grades the body (`WellDenoted`) from the hereditary
`FieldsOkB` premise (the domains' own `WellDenoted` + `FieldsBound`);
the app slots are discharged by `psigmaV_rr_mem`, the `[w, w]`
instance of the pinned pair former's product membership.  Bit validity
(`AnnotValid`) is a lane predicate and lands with the Model battery
(stage 4).
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- The carrier body, graph regime: the right-nested `.psigma [w, w]`
application tower over the field domains, `.punit`-terminated.  The
fibre λ is annotated `w + 1` (its body is a type of sort `w`), so it
is a graph at every regime. -/
def towerBodyAVPos (w : Nat) : List AnnotTerm → AnnotTerm
  | [] => .const .punit [w + 1]
  | F :: Fs => .app (.app (.const .psigma [w, w]) F)
      (.lam (w + 1) F (towerBodyAVPos w Fs))

/-- `(_ : P) → Empty` at bit `0`: the truth value of `P`'s emptiness
(`piR 0`'s ∀ over an empty codomain). -/
def negAV (P : AnnotTerm) : AnnotTerm := .pi 0 0 P (.const .empty [0])

/-- The carrier body, **squash regime** (task #175 W4c/O4): the truth
value of the field chain's inhabitation, spelled classically as
`¬ ∀ x₀ : F₀, ¬ ∀ x₁ : F₁, … ¬ True` with bit-`0` Π nodes.  The
`.psigma [0, 0]` spelling cannot serve here — its pinned valuation
reads the first component in `univ 0`, and a `Prop`-declared
structure may carry data fields (arena tutorial 087) — while `piR 0`
truncates whatever its domain is, exactly as `sigmaSet 0` does.  No
field bound is needed for the interpretation. -/
def sqBodyAV : List AnnotTerm → AnnotTerm
  | [] => .const .punit [1]
  | F :: Fs => negAV (.pi 0 0 F (negAV (sqBodyAV Fs)))

/-- The carrier body, both regimes: the squash spelling at `w = 0`,
the pair tower above. -/
def towerBodyAV (w : Nat) (Fs : List AnnotTerm) : AnnotTerm :=
  if w = 0 then sqBodyAV Fs else towerBodyAVPos w Fs

theorem towerBodyAV_zero (Fs : List AnnotTerm) :
    towerBodyAV 0 Fs = sqBodyAV Fs := if_pos rfl

theorem towerBodyAV_pos {w : Nat} (hw : w ≠ 0) (Fs : List AnnotTerm) :
    towerBodyAV w Fs = towerBodyAVPos w Fs := if_neg hw

/-- `FieldsOkB w ρ Fs`: the hereditary grading the body's `WellDenoted`
consumes — each domain is itself graded and, in the graph regime, its
interpretation is bounded, at every fitting prefix.  (At squash the
carrier is a truth value whatever the fields are — `towerBodyAV`'s
`sqBodyAV` spelling — so no bound is asked; task #175 W4c/O4.) -/
def FieldsOkB (w : Nat) (ρ : Nat → V) : List AnnotTerm → Prop
  | [] => True
  | F :: Fs => WellDenoted V ρ F ∧ (w ≠ 0 → interp V ρ F ∈ˢ (univ w : V)) ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsOkB w (cons a ρ) Fs

theorem FieldsOkB.toBound {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V},
      FieldsOkB w ρ Fs → FieldsBound w ρ Fs
  | [], _, _ => trivial
  | _ :: Fs, _, h =>
    ⟨h.2.1 hw, fun a ha => FieldsOkB.toBound hw (Fs := Fs) (h.2.2 a ha)⟩

/-! ## The squash spelling's interpretation -/

theorem exists_mem_truthVal {p : Prop} :
    (∃ y : V, y ∈ˢ (truthVal p : V)) ↔ p :=
  ⟨fun ⟨_, hy⟩ => of_mem_truthVal hy, fun hp => ⟨pt, pt_mem_truthVal hp⟩⟩

theorem interp_negAV (ρ : Nat → V) (P : AnnotTerm) :
    interp V ρ (negAV P) = truthVal (¬ ∃ x, x ∈ˢ interp V ρ P) := by
  show piR 0 (interp V ρ P) (fun _ => (empty : V)) = _
  rw [piR_zero]
  refine truthVal_congr ⟨fun h ⟨x, hx⟩ => ?_, fun h x hx => absurd ⟨x, hx⟩ h⟩
  obtain ⟨y, hy⟩ := h x hx
  exact not_mem_empty y hy

/-- **The squash body reads back as the squash carrier**, with no
premise at all. -/
theorem sqBodyAV_interp :
    ∀ (Fs : List AnnotTerm) (ρ : Nat → V),
      interp V ρ (sqBodyAV Fs) = towerSet 0 (teleOfFields ρ Fs)
  | [], _ => rfl
  | F :: Fs, ρ => by
    show interp V ρ (negAV (.pi 0 0 F (negAV (sqBodyAV Fs)))) = _
    rw [interp_negAV, teleOfFields_cons]
    show _ = sigmaSet 0 (interp V ρ F)
      (fun a => towerSet 0 (teleOfFields (cons a ρ) Fs))
    rw [sigmaSet_zero]
    refine truthVal_congr ?_
    rw [interp_pi, piR_zero, exists_mem_truthVal]
    have hin : ∀ x : V, (∃ y, y ∈ˢ interp V (cons x ρ) (negAV (sqBodyAV Fs)))
        ↔ ¬ ∃ z, z ∈ˢ towerSet 0 (teleOfFields (cons x ρ) Fs) := by
      intro x
      rw [interp_negAV, sqBodyAV_interp Fs (cons x ρ), exists_mem_truthVal]
    constructor
    · intro h
      exact Classical.byContradiction fun hno =>
        h fun x hx => (hin x).mpr fun hz => hno ⟨x, hx, hz⟩
    · rintro ⟨x, hx, y, hy⟩ hall
      exact (hin x).mp (hall x hx) ⟨y, hy⟩

/-- **The squash body is graded** from the chain's own gradings. -/
theorem sqBodyAV_wellDenoted :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsOkB 0 ρ Fs →
      WellDenoted V ρ (sqBodyAV Fs)
  | [], ρ, _ => by simp [sqBodyAV]
  | F :: Fs, ρ, hok => by
    show WellDenoted V ρ (negAV (.pi 0 0 F (negAV (sqBodyAV Fs))))
    unfold negAV
    rw [WellDenoted_pi]
    refine ⟨?_, fun _ _ => by simp⟩
    rw [WellDenoted_pi]
    refine ⟨hok.1, fun x hx => ?_⟩
    rw [WellDenoted_pi]
    exact ⟨sqBodyAV_wellDenoted (hok.2.2 x hx), fun _ _ => by simp⟩

/-- **The carrier body reads back as the tier's carrier**: under the
hereditary bound (O5's semantic form), the `.psigma` spelling
interprets to `towerSet w` of the interpreted telescope — at every
level, both regimes. -/
theorem towerBodyAVPos_interp {w : Nat} :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsBound w ρ Fs →
      interp V ρ (towerBodyAVPos w Fs)
        = towerSet w (teleOfFields ρ Fs)
  | [], _, _ => rfl
  | F :: Fs, ρ, hb => by
    have hA : interp V ρ F ∈ˢ (univ w : V) := hb.1
    have hG : ∀ x, x ∈ˢ interp V ρ F →
        interp V (cons x ρ) (towerBodyAVPos w Fs)
          = towerSet w (teleOfFields (cons x ρ) Fs) :=
      fun x hx => towerBodyAVPos_interp (hb.2 x hx)
    have hB : (lamR (w + 1) (interp V ρ F)
          fun x => interp V (cons x ρ) (towerBodyAVPos w Fs))
        ∈ˢ piR (w + 1) (interp V ρ F) (fun _ => (univ w : V)) :=
      lamR_mem fun x hx => by
        rw [hG x hx]
        exact towerSet_univ_teleOfFields (hb.2 x hx)
    have hbv : bval V .psigma [w, w] = psigmaV V w w := rfl
    show SetTheory.app (SetTheory.app (bval V .psigma [w, w])
        (interp V ρ F))
        (lamR (w + 1) (interp V ρ F)
          fun x => interp V (cons x ρ) (towerBodyAVPos w Fs))
      = towerSet w (teleOfFields ρ (F :: Fs))
    rw [hbv, psigmaV_app V hA hB,
      show Nat.max w w = w from Nat.max_self w, teleOfFields_cons]
    show sigmaSet w _ _ = sigmaSet w _ _
    exact sigma_congr fun x hx => by
      rw [app_lamR_pos (Nat.succ_ne_zero w) hx, hG x hx]

/-- **The carrier body reads back as the tier's carrier**, both
regimes: unconditionally at squash, under the hereditary bound (O5's
semantic form) in the graph regime. -/
theorem towerBodyAV_interp {w : Nat} {Fs : List AnnotTerm} {ρ : Nat → V}
    (hb : w ≠ 0 → FieldsBound w ρ Fs) :
    interp V ρ (towerBodyAV w Fs) = towerSet w (teleOfFields ρ Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_interp Fs ρ
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_interp (hb hw)

/-- The carrier's formation, both regimes. -/
theorem towerSet_univ_of_okB {w : Nat} {Fs : List AnnotTerm} {ρ : Nat → V}
    (hb : w ≠ 0 → FieldsBound w ρ Fs) :
    towerSet w (teleOfFields ρ Fs) ∈ˢ (univ w : V) := by
  by_cases hw : w = 0
  · subst hw
    rw [univ_zero]
    exact towerSet_zero_univZero_teleOfFields
  · exact towerSet_univ_teleOfFields (hb hw)

/-- `projAV` commutes with lifting (it introduces no binders). -/
theorem projAV_liftN :
    ∀ (i : Nat) (e : AnnotTerm) (n k : Nat),
      (projAV i e).liftN n k = projAV i (e.liftN n k)
  | 0, _, _, _ => rfl
  | i + 1, e, n, k => projAV_liftN i (.snd e) n k

/-- `projAV` commutes with instantiation. -/
theorem projAV_inst :
    ∀ (i : Nat) (e a : AnnotTerm) (k : Nat),
      (projAV i e).inst a k = projAV i (e.inst a k)
  | 0, _, _, _ => rfl
  | i + 1, e, a, k => projAV_inst i (.snd e) a k

/-- **The carrier body is graded** (`WellDenoted`): every app slot is
supplied by `psigmaV_rr_mem` and the fibre package by the tier's
formation laws; the hereditary premise carries the domains' own
grading. -/
theorem towerBodyAVPos_wellDenoted {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List AnnotTerm} {ρ : Nat → V}, FieldsOkB w ρ Fs →
      WellDenoted V ρ (towerBodyAVPos w Fs)
  | [], ρ, _ => by simp [towerBodyAVPos]
  | F :: Fs, ρ, hok => by
    have hb : FieldsBound w ρ (F :: Fs) := hok.toBound hw
    have hA : interp V ρ F ∈ˢ (univ w : V) := hok.2.1 hw
    have hG : ∀ x, x ∈ˢ interp V ρ F →
        interp V (cons x ρ) (towerBodyAVPos w Fs)
          = towerSet w (teleOfFields (cons x ρ) Fs) :=
      fun x hx => towerBodyAVPos_interp (hb.2 x hx)
    have hbv : interp V ρ (.const .psigma [w, w]) = psigmaV V w w := rfl
    have hvac : ¬ w + 1 = 0 := Nat.succ_ne_zero w
    show WellDenoted V ρ (.app (.app (.const .psigma [w, w]) F)
      (.lam (w + 1) F (towerBodyAVPos w Fs)))
    rw [WellDenoted_app]
    refine ⟨?_, ?_, ?_⟩
    · -- the inner application `.psigma [w,w] F`
      rw [WellDenoted_app]
      exact ⟨trivial, hok.1,
        ⟨w + 1, univ w,
          fun A => piR (w + 1) (psigmaFibreSpace V w A)
            fun _ => (univ w : V),
          hbv ▸ psigmaV_rr_mem (V := V) w, hA, fun h => absurd h hvac⟩⟩
    · -- the fibre λ
      rw [WellDenoted_lam]
      refine ⟨hok.1, fun x hx => towerBodyAVPos_wellDenoted hw (hok.2.2 x hx),
        ⟨fun _ => (univ w : V), fun x hx => ?_, fun h => absurd h hvac⟩⟩
      rw [hG x hx]
      exact towerSet_univ_teleOfFields (hb.2 x hx)
    · -- the outer application's kind slot
      refine ⟨w + 1, psigmaFibreSpace V w (interp V ρ F),
        fun _ => (univ w : V), ?_, ?_, fun h => absurd h hvac⟩
      · show SetTheory.app (interp V ρ (.const .psigma [w, w]))
            (interp V ρ F) ∈ˢ _
        rw [hbv]
        exact app_mem_piR_pos hvac (psigmaV_rr_mem (V := V) w) hA
      · exact lamR_mem fun x hx => by
          rw [hG x hx]
          exact towerSet_univ_teleOfFields (hb.2 x hx)

/-- **The carrier body is graded** (`WellDenoted`), both regimes. -/
theorem towerBodyAV_wellDenoted {w : Nat} {Fs : List AnnotTerm} {ρ : Nat → V}
    (hok : FieldsOkB w ρ Fs) : WellDenoted V ρ (towerBodyAV w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_wellDenoted hok
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_wellDenoted hw hok

/-! ## Stage 3: the λ/Π-tower formers

`mkLamsAV`/`mkPisAV` are the generic tower formers over peeled binder
data; `stripPisAV` is the peel whose inversion hands the wiring the
`(binder data, body)` decomposition of a stored type's reading. -/

/-- The λ-tower former over `(codomain-sort bit, domain)` data. -/
def mkLamsAV : List (Nat × AnnotTerm) → AnnotTerm → AnnotTerm
  | [], b => b
  | d :: ds, b => .lam d.1 d.2 (mkLamsAV ds b)

/-- The Π-tower former over `(domain sort, codomain sort, domain)`
data — the shape of a stored Π-type's reading. -/
def mkPisAV : List (Nat × Nat × AnnotTerm) → AnnotTerm → AnnotTerm
  | [], b => b
  | d :: ds, b => .pi d.1 d.2.1 d.2.2 (mkPisAV ds b)

/-- Peel `n` Π-binders off a reading. -/
def stripPisAV : Nat → AnnotTerm → Option (List (Nat × Nat × AnnotTerm) × AnnotTerm)
  | 0, e => some ([], e)
  | n + 1, .pi u v A B =>
    (stripPisAV n B).map fun p => ((u, v, A) :: p.1, p.2)
  | _ + 1, _ => none

/-- The peel's inversion: a successful strip exhibits the reading as
the Π-tower of its parts (the wiring's hook). -/
theorem stripPisAV_eq_mkPis :
    ∀ {n : Nat} {e : AnnotTerm} {ps : List (Nat × Nat × AnnotTerm)} {b : AnnotTerm},
      stripPisAV n e = some (ps, b) → e = mkPisAV ps b ∧ ps.length = n
  | 0, e, ps, b, h => by
    obtain ⟨rfl, rfl⟩ : ps = [] ∧ b = e := by
      simpa [stripPisAV] using h.symm
    exact ⟨rfl, rfl⟩
  | n + 1, .pi u v A B, ps, b, h => by
    simp only [stripPisAV, Option.map_eq_some_iff] at h
    obtain ⟨⟨ps', b'⟩, hstrip, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : (u, v, A) :: ps' = ps ∧ b' = b := by
      simpa using heq
    obtain ⟨hB, hlen⟩ := stripPisAV_eq_mkPis hstrip
    exact ⟨by rw [mkPisAV, ← hB], by simp [hlen]⟩

/-- **The generic λ-tower fold**: at all-nonzero bits, applying the
tower along a fitting spine computes the body at the spine's
environment (`app_lamR_pos` iterated). -/
theorem mkLamsAV_fold :
    ∀ {ds : List (Nat × AnnotTerm)} {b : AnnotTerm} {ρ : Nat → V} {as : List V},
      (∀ d ∈ ds, d.1 ≠ 0) → SpineFit ρ (ds.map (·.2)) as →
      as.foldl SetTheory.app (interp V ρ (mkLamsAV ds b))
        = interp V (consList as ρ) b
  | [], _, _, [], _, _ => rfl
  | [], _, _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, _, [], _, hsp => hsp.elim
  | d :: ds, b, ρ, a :: as, hnz, hsp => by
    show (as.foldl SetTheory.app
      (SetTheory.app (lamR d.1 (interp V ρ d.2)
        fun x => interp V (cons x ρ) (mkLamsAV ds b)) a)) = _
    rw [app_lamR_pos (hnz d (.head _)) hsp.1]
    exact mkLamsAV_fold (fun d' hd' => hnz d' (.tail _ hd')) hsp.2

/-- A zero-annotated head collapses the tower to the proof point — the
squash regime of a value whose type became a proposition. -/
theorem mkLamsAV_zero_head (A : AnnotTerm) (ds : List (Nat × AnnotTerm))
    (b : AnnotTerm) (ρ : Nat → V) :
    interp V ρ (mkLamsAV ((0, A) :: ds) b) = (pt : V) := lamR_zero

/-! ### The constant-bit λ-tower, generically

The constructor and recursor leaves are λ-towers whose bits are ONE
numeral (`w`, resp. the elimination level) zero-agreeing with every
codomain annotation of their Π-type's reading.  `mkLamsC` is that
shape; `UnderTowerOk` is its single hereditary premise; `mkLamsC_mem`
and `mkLamsC_wellDenoted` are the once-for-all membership and grading. -/

/-- The constant-bit λ-tower over a Π-tower's own binder data. -/
def mkLamsC (m : Nat) (ds : List (Nat × Nat × AnnotTerm)) (b : AnnotTerm) :
    AnnotTerm :=
  mkLamsAV (ds.map fun d => (m, d.2.2)) b

/-- The hereditary premise of the constant-bit tower's laws: each
domain graded, and at every fitting spine the body is graded, a member
of the result type's reading, and — when the bit is zero — that
reading is a truth value. -/
def UnderTowerOk (m : Nat) (ρ : Nat → V) (b T : AnnotTerm) :
    List (Nat × Nat × AnnotTerm) → Prop
  | [] => WellDenoted V ρ b ∧ interp V ρ b ∈ˢ interp V ρ T ∧
      (m = 0 → interp V ρ T ∈ˢ (univZero : V))
  | d :: ds => WellDenoted V ρ d.2.2 ∧
      ∀ a, a ∈ˢ interp V ρ d.2.2 → UnderTowerOk m (cons a ρ) b T ds

/-- The residual Π-tower is a truth value at a zero bit (either the
first codomain annotation is zero, or the base's own condition). -/
theorem underTowerOk_res_univZero {m : Nat} {b T : AnnotTerm} (h0 : m = 0) :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → UnderTowerOk m ρ b T ds →
      interp V ρ (mkPisAV ds T) ∈ˢ (univZero : V)
  | [], _, _, h => h.2.2 h0
  | d :: ds, ρ, hz, _ => by
    show piR d.2.1 _ _ ∈ˢ _
    rw [(hz d (.head _)).mp h0]
    exact piR_zero_mem_univZero

/-- **The constant-bit tower inhabits its Π-tower's reading**
(`lamR_mem_zero_agree` per binder, the base's membership at the
bottom). -/
theorem mkLamsC_mem {m : Nat} {b T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → UnderTowerOk m ρ b T ds →
      interp V ρ (mkLamsC m ds b) ∈ˢ interp V ρ (mkPisAV ds T)
  | [], _, _, h => h.2.1
  | d :: ds, ρ, hz, h => by
    show (lamR m (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkLamsC m ds b))
      ∈ˢ piR d.2.1 (interp V ρ d.2.2)
        fun a => interp V (cons a ρ) (mkPisAV ds T)
    exact lamR_mem_zero_agree (hz d (.head _))
      fun a ha => mkLamsC_mem (fun d' hd' => hz d' (.tail _ hd'))
        (h.2 a ha)

/-- **The constant-bit tower is graded** (`WellDenoted`): the fibre
packages are the interpreted residual Π-towers, membership from
`mkLamsC_mem` at each suffix, the zero component from
`underTowerOk_res_univZero`. -/
theorem mkLamsC_wellDenoted {m : Nat} {b T : AnnotTerm} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      (∀ d ∈ ds, (m = 0 ↔ d.2.1 = 0)) → UnderTowerOk m ρ b T ds →
      WellDenoted V ρ (mkLamsC m ds b)
  | [], _, _, h => h.1
  | d :: ds, ρ, hz, h => by
    show WellDenoted V ρ (.lam m d.2.2 (mkLamsC m ds b))
    rw [WellDenoted_lam]
    refine ⟨h.1, fun a ha => mkLamsC_wellDenoted
        (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha),
      ⟨fun a => interp V (cons a ρ) (mkPisAV ds T),
       fun a ha => mkLamsC_mem (fun d' hd' => hz d' (.tail _ hd'))
         (h.2 a ha),
       fun h0 a ha => underTowerOk_res_univZero h0
         (fun d' hd' => hz d' (.tail _ hd')) (h.2 a ha)⟩⟩

end ConLeche.Semantics
