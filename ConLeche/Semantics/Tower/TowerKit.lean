module

import ConLeche.Semantics.WellDenoted
public import ConLeche.Semantics.BasisOk
public import ConLeche.SetModel.Tower

@[expose] public section

/-!
# The tower leaves: telescopes, the carrier, the tupler, the projection spine

The telescope introduction (`TeleS` from an interpreted binder chain);
the carrier body and the uniform projection spelling; the constructor
tupler; the projection spine on tower members.
-/

/-!
## The telescope introduction: `TeleS` from an interpreted binder chain

The tuple tier (`ConLeche/SetModel/TupleTower.lean`) states its laws over
an abstract dependent telescope `TeleS V n`.  A checked
direct-structure block does not hand the install a `TeleS` — it hands
a list of **field domains** (`Fs : List Term`, the
constructor type reading's pi-domains after the parameters, each
scoped under its predecessors).  This module is the bridge:

    teleOfFields ρ Fs : TeleS V Fs.length

interprets the chain under successively consed environments — the
dependency of field `i` on fields `0..i−1` is carried by the
*environment*, exactly as `interp` carries every binder dependency,
so the length-indexed fully-dependent tail of `TeleS`
(`cons (A : V) (B : V → TeleS V n)`) is populated with no new
machinery: `B a` is the tail's telescope at `cons a ρ`.

The tier's premise/conclusion currencies transpose:

| tier | Term currency (this file) |
|---|---|
| `FitsS T as` | `SpineFit ρ Fs as` (`fitsS_teleOfFields`) |
| `teleNth T i pre` | `⟦Fs[i]⟧` at `consList pre ρ` (`teleNth_teleOfFields`) |
| `BoundS w T` | `FieldsBound w ρ Fs` (`boundS_teleOfFields`) |
| `PropS T` | `FieldsBound 0 ρ Fs` (`propS_teleOfFields`; `univ_zero`) |

R2 (recursive fields) never reaches this file: O2 excludes the class syntactically, and the
`teleOfFields` walk interprets every domain in the pre-block alphabet.

The four capstone corollaries (`mkTower_mem_teleOfFields`,
`towerSet_elim_teleOfFields`, `projS_mem_teleOfFields`,
`towerSet_univ_teleOfFields`) are the tier's intro/eta/projection/
formation laws restated in the Term currency — the shapes the
install battery consumes.  `projS_mem_teleOfFields`'s premise
`(w = 0 → FieldsBound 0 ρ Fs)` IS the per-use O4/R1 branch: vacuous at
graph instantiations, the proof-field legality (`infer_proj`'s Prop
restriction, semantically) at squash ones.
-/

namespace ConLeche.Semantics
open ConLeche.Verify (projNV)
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- The environment a value spine ends in: the values consed in order,
outermost (earliest binder) first — `consList [a₀, …, aₖ] ρ` is the
frame under binders `a₀ … aₖ`, innermost last.  (The Model tier's
`consN` (`Model/IndTele.lean`) is the same fold; this layer cannot
import it.) -/
def consList : List V → (Nat → V) → Nat → V
  | [], ρ => ρ
  | a :: as, ρ => consList as (cons a ρ)

omit [SetTheory V] in
@[simp] theorem consList_nil (ρ : Nat → V) : consList [] ρ = ρ := rfl

omit [SetTheory V] in
@[simp] theorem consList_cons (a : V) (as : List V) (ρ : Nat → V) :
    consList (a :: as) ρ = consList as (cons a ρ) := rfl

/-- **The telescope introduction**: the semantic `TeleS` over the
interpreted binder chain.  Field `i`'s set is `⟦Fs[i]⟧` at the
environment binding the earlier fields' values — the dependent tail is
the interpretation environment itself. -/
noncomputable def teleOfFields (ρ : Nat → V) :
    (Fs : List Term) → TeleS V Fs.length
  | [] => .nil
  | F :: Fs => .cons (interp V ρ F) fun a => teleOfFields (cons a ρ) Fs

@[simp] theorem teleOfFields_nil (ρ : Nat → V) :
    teleOfFields ρ ([] : List Term) = .nil := rfl

@[simp] theorem teleOfFields_cons (ρ : Nat → V) (F : Term)
    (Fs : List Term) :
    teleOfFields ρ (F :: Fs)
      = .cons (interp V ρ F) (fun a => teleOfFields (cons a ρ) Fs) := rfl

/-- `SpineFit ρ Fs as`: the values fit the interpreted chain — right
length, each value in its domain's interpretation at the earlier
values.  The Term currency of the tier's `FitsS`. -/
def SpineFit (ρ : Nat → V) : List Term → List V → Prop
  | [], [] => True
  | F :: Fs, a :: as => a ∈ˢ interp V ρ F ∧ SpineFit (cons a ρ) Fs as
  | _, _ => False

/-- `FieldsBound w ρ Fs`: every field's interpretation lives in
`univ w`, hereditarily — O5's semantic form, the tier's `BoundS`. -/
def FieldsBound (w : Nat) (ρ : Nat → V) : List Term → Prop
  | [] => True
  | F :: Fs => interp V ρ F ∈ˢ (univ w : V) ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsBound w (cons a ρ) Fs

omit [SetTheory V] in
theorem consList_append (xs ys : List V) (ρ : Nat → V) :
    consList (xs ++ ys) ρ = consList ys (consList xs ρ) := by
  induction xs generalizing ρ with
  | nil => rfl
  | cons x xs ih => rw [List.cons_append, consList_cons, consList_cons, ih]

/-- Fits concatenate: a fit of the first chain and a fit of the second
at the extended environment give a fit of the concatenation. -/
theorem SpineFit.append :
    ∀ {Fs₁ : List Term} {as₁ : List V} {Fs₂ : List Term}
      {as₂ : List V} {ρ : Nat → V},
      SpineFit ρ Fs₁ as₁ → SpineFit (consList as₁ ρ) Fs₂ as₂ →
      SpineFit ρ (Fs₁ ++ Fs₂) (as₁ ++ as₂)
  | [], [], _, _, _, _, h₂ => h₂
  | [], _ :: _, _, _, _, h₁, _ => h₁.elim
  | _ :: _, [], _, _, _, h₁, _ => h₁.elim
  | _ :: Fs₁, _a :: as₁, _, _, _, h₁, h₂ =>
    ⟨h₁.1, SpineFit.append (Fs₁ := Fs₁) (as₁ := as₁) h₁.2 h₂⟩

/-- A fit of an appended chain splits. -/
theorem spineFit_append_inv :
    ∀ {Ds₁ Ds₂ : List Term} {ρ : Nat → V} {as : List V},
      SpineFit ρ (Ds₁ ++ Ds₂) as →
      ∃ as₁ as₂, as = as₁ ++ as₂ ∧ SpineFit ρ Ds₁ as₁ ∧ SpineFit (consList as₁ ρ) Ds₂ as₂
  | [], _, ρ, as, h => ⟨[], as, rfl, trivial, h⟩
  | _ :: _, _, _, [], h => h.elim
  | D :: Ds₁, Ds₂, ρ, a :: as, h => by
    obtain ⟨as₁, as₂, rfl, h1, h2⟩ := spineFit_append_inv (Ds₁ := Ds₁) h.2
    exact ⟨a :: as₁, as₂, rfl, ⟨h.1, h1⟩, by rw [consList_cons]; exact h2⟩

theorem SpineFit.length_eq :
    ∀ {Fs : List Term} {ρ : Nat → V} {as : List V},
      SpineFit ρ Fs as → as.length = Fs.length
  | [], _, [], _ => rfl
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | _ :: Fs, _, _ :: as, h =>
    congrArg Nat.succ (SpineFit.length_eq (Fs := Fs) (as := as) h.2)

/-- The fit currencies coincide: the tier's `FitsS` at `teleOfFields`
is `SpineFit`. -/
theorem fitsS_teleOfFields :
    ∀ {Fs : List Term} {ρ : Nat → V} {as : List V},
      FitsS (teleOfFields ρ Fs) as ↔ SpineFit ρ Fs as
  | [], _, [] => Iff.rfl
  | [], _, _ :: _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | _ :: Fs, _, _ :: as =>
    and_congr Iff.rfl (fitsS_teleOfFields (Fs := Fs) (as := as))

/-- The `i`-th field set at a prefix valuation is the `i`-th domain's
interpretation at the prefix environment. -/
theorem teleNth_teleOfFields :
    ∀ {Fs : List Term} (ρ : Nat → V) (i : Nat) (h : i < Fs.length)
      (pre : List V), pre.length = i →
      teleNth (teleOfFields ρ Fs) i pre = interp V (consList pre ρ) Fs[i]
  | F :: Fs, ρ, 0, _, [], _ => rfl
  | F :: Fs, ρ, i + 1, h, a :: pre, hlen => by
    rw [List.getElem_cons_succ, consList_cons]
    exact teleNth_teleOfFields (cons a ρ) i (Nat.lt_of_succ_lt_succ h) pre
      (Nat.succ.inj hlen)

/-- The bound currencies coincide: the tier's `BoundS` at
`teleOfFields` is `FieldsBound`. -/
theorem boundS_teleOfFields :
    ∀ {w : Nat} {Fs : List Term} {ρ : Nat → V},
      BoundS w (teleOfFields ρ Fs) ↔ FieldsBound w ρ Fs
  | _, [], _ => Iff.rfl
  | _, _ :: Fs, _ =>
    and_congr Iff.rfl (forall_congr' fun _a => imp_congr Iff.rfl
      (boundS_teleOfFields (Fs := Fs)))

/-- The squash currency: the tier's `PropS` at `teleOfFields` is
`FieldsBound 0` (`univ 0 = univZero` definitionally). -/
theorem propS_teleOfFields :
    ∀ {Fs : List Term} {ρ : Nat → V},
      PropS (teleOfFields ρ Fs) ↔ FieldsBound 0 ρ Fs
  | [], _ => Iff.rfl
  | _ :: Fs, _ =>
    and_congr (by rw [univ_zero]) (forall_congr' fun _a => imp_congr Iff.rfl
      (propS_teleOfFields (Fs := Fs)))

/-! ## The tier's laws at the interpreted telescope

The four capstone corollaries, in the currencies the install battery
consumes.  Iota needs no bridge at all (`projS_mkTower` mentions no
telescope), and coherence (`mkTower_inj`) likewise. -/

/-- **Introduction** (graph regime): a fitting spine's tower inhabits
the interpreted carrier. -/
theorem mkTower_mem_teleOfFields {w : Nat} (hw : w ≠ 0)
    {Fs : List Term} {ρ : Nat → V} {as : List V}
    (hsp : SpineFit ρ Fs as) :
    mkTower as ∈ˢ towerSet w (teleOfFields ρ Fs) :=
  mkTower_mem hw (fitsS_teleOfFields.mpr hsp)

/-- **Introduction** (squash regime): a fitting spine puts `pt` in the
interpreted carrier. -/
theorem pt_mem_tower_teleOfFields {Fs : List Term} {ρ : Nat → V}
    {as : List V} (hsp : SpineFit ρ Fs as) :
    (pt : V) ∈ˢ towerSet 0 (teleOfFields ρ Fs) :=
  pt_mem_tower (fitsS_teleOfFields.mpr hsp)

/-- **Eta + elimination** (graph regime): a member of the interpreted
carrier is the tower of its own projections, and those projections fit
the interpreted chain. -/
theorem towerSet_elim_teleOfFields {w : Nat} (hw : w ≠ 0)
    {Fs : List Term} {ρ : Nat → V} {x : V}
    (hx : x ∈ˢ towerSet w (teleOfFields ρ Fs)) :
    SpineFit ρ Fs (projList Fs.length x)
      ∧ x = mkTower (projList Fs.length x) := by
  obtain ⟨hf, heta⟩ := towerSet_elim hw (teleOfFields ρ Fs) hx
  exact ⟨fitsS_teleOfFields.mp hf, heta⟩

/-- **Projection membership**, two regimes in one statement: the
`i`-th projection lands in the `i`-th domain's interpretation at the
earlier projections.  The premise is the O4/R1 per-use branch —
vacuous at a graph instantiation, the proof-field legality (`PropS`
via `propS_teleOfFields`) at a squash one. -/
theorem projS_mem_teleOfFields {w : Nat} {Fs : List Term}
    {ρ : Nat → V} {x : V} (hreg : w = 0 → FieldsBound 0 ρ Fs)
    (hx : x ∈ˢ towerSet w (teleOfFields ρ Fs)) {i : Nat}
    (h : i < Fs.length) :
    projS i x ∈ˢ interp V (consList (projList i x) ρ) Fs[i] := by
  have hnth := teleNth_teleOfFields ρ i h (projList i x)
    (projList_length i x)
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · have hm := projS_mem_zero (propS_teleOfFields.mpr (hreg rfl)) hx i h
    rwa [hnth] at hm
  · have hm := projS_mem (Nat.pos_iff_ne_zero.mp hw) hx i h
    rwa [hnth] at hm

/-- **Formation** (graph regime): the interpreted carrier lives at the
structure's own level, from the hereditary bound. -/
theorem towerSet_univ_teleOfFields {w : Nat} {Fs : List Term}
    {ρ : Nat → V} (hb : FieldsBound w ρ Fs) :
    towerSet w (teleOfFields ρ Fs) ∈ˢ (univ w : V) :=
  towerSet_mem_univ _ (boundS_teleOfFields.mpr hb)

/-- **Formation** (squash regime) needs nothing: restated for the
consumer's symmetry. -/
theorem towerSet_zero_univZero_teleOfFields {Fs : List Term}
    {ρ : Nat → V} :
    towerSet 0 (teleOfFields ρ Fs) ∈ˢ (univZero : V) :=
  towerSet_zero_mem_univZero _


/-!
## The carrier body and the uniform projection spelling

The value-introduction half of the direct-structure bridge: the tier's
semantic values must be *stored*, and the P dialect stores constant
denotations as closed `Term` leaves over the `BConst` alphabet
(`EnvModel.acval`).  This module supplies the two body spellings and
their interpretation equations:

* `towerBodyAV w Fs` — the carrier, spelled through `.psigma` at level
  instantiation `[w, w]` with the unit terminator `.punit [w]`.  Two
  interface facts make this land exactly on the tier's `towerSet w`:
  `sigmaSet` reads its level only through the zero test
  (`sigmaSet_pos`/`sigmaSet_zero`), so `max w w = w` closes the level
  bookkeeping; and the fibre λ's body is a type at every point, so
  `lamV_mem` places the fibre in the pair former's fibre space.  The
  premises of `psigmaV_app` are exactly `FieldsBound w` — O5 plus
  cumulativity, nothing else.

* `projNV i` — the tier's structure-independent `projS i = sfst ∘
  ssnd^i`, spelled by the iterated projection formers `.fst ∘ .snd^i`.
  No type arguments, no entry consultation; `projNV_interp` is the
  definitional commutation.  The definition and its lifting and
  instantiation laws live with `denote` (`Verify/Denote.lean`), whose
  `.proj` clause spells it; `projNV_interp` lives one layer down
  (`Semantics/BasisOk.lean`), because a basis constant's type —
  `lfpTuple k`'s index-set tuple — reads its arguments with it.

`towerBodyAV_wellDenoted` grades the body (`WellDenoted`) from the hereditary
`FieldsOkB` premise (the domains' own `WellDenoted` + `FieldsBound`);
the app slots are discharged by `psigmaV_rr_mem`, the `[w, w]`
instance of the pinned pair former's function-space membership.
-/


/-- The carrier body, graph regime: the right-nested `.psigma [w, w]`
application tower over the field domains, terminated by `PUnit.{w}`
(`{∅}` above `Prop`, task #342 C).  The fibre λ's body is a type of
sort `w`, so it reads as a graph (`lamV`). -/
def towerBodyAVPos (w : Nat) : List Term → Term
  | [] => .const .punit [w]
  | F :: Fs => .app (.app (.const .psigma [w, w]) F)
      (.lam F (towerBodyAVPos w Fs))

/-- `(_ : P) → Empty`: the truth value of `P`'s emptiness (a ∀ over an
empty codomain). -/
def negAV (P : Term) : Term := .pi P (.const .empty [0])

/-- The carrier body, **squash regime** (O4): the truth
value of the field chain's inhabitation, spelled classically as
`¬ ∀ x₀ : F₀, ¬ ∀ x₁ : F₁, … ¬ True`, every Π node a truth value.  The
`.psigma [0, 0]` spelling cannot serve here — its pinned valuation
reads the first component in `univ 0`, and a `Prop`-declared
structure may carry data fields (arena tutorial 087) — while `piR 0`
truncates whatever its domain is, exactly as `sigmaSet 0` does.  No
field bound is needed for the interpretation. -/
def sqBodyAV : List Term → Term
  | [] => .const .punit [0]
  | F :: Fs => negAV (.pi F (negAV (sqBodyAV Fs)))

/-- The carrier body, both regimes: the squash spelling at `w = 0`,
the pair tower above. -/
def towerBodyAV (w : Nat) (Fs : List Term) : Term :=
  if w = 0 then sqBodyAV Fs else towerBodyAVPos w Fs

theorem towerBodyAV_zero (Fs : List Term) :
    towerBodyAV 0 Fs = sqBodyAV Fs := ite_eq_left rfl

theorem towerBodyAV_pos {w : Nat} (hw : w ≠ 0) (Fs : List Term) :
    towerBodyAV w Fs = towerBodyAVPos w Fs := ite_eq_right hw

/-- `FieldsOkB w ρ Fs`: the hereditary grading the body's `WellDenoted`
consumes — each domain is itself graded and a type and, in the graph
regime, its interpretation is bounded, at every fitting prefix.  (At
squash the carrier is a truth value whatever the fields are —
`towerBodyAV`'s `sqBodyAV` spelling — so no bound is asked; the domains
are still types, which the spelling's `Π`s need.) -/
def FieldsOkB (w : Nat) (ρ : Nat → V) : List Term → Prop
  | [] => True
  | F :: Fs => WellDenoted V ρ F ∧ IsTy (interp V ρ F) ∧
      (w ≠ 0 → interp V ρ F ∈ˢ (univ w : V)) ∧
      ∀ a, a ∈ˢ interp V ρ F → FieldsOkB w (cons a ρ) Fs

theorem FieldsOkB.toBound {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List Term} {ρ : Nat → V},
      FieldsOkB w ρ Fs → FieldsBound w ρ Fs
  | [], _, _ => trivial
  | _ :: Fs, _, h =>
    ⟨h.2.2.1 hw, fun a ha => FieldsOkB.toBound hw (Fs := Fs) (h.2.2.2 a ha)⟩

/-! ## The squash spelling's interpretation -/

theorem exists_mem_truthVal {p : Prop} :
    (∃ y : V, y ∈ˢ (truthVal p : V)) ↔ p :=
  ⟨fun ⟨_, hy⟩ => of_mem_truthVal hy, fun hp => ⟨pt, pt_mem_truthVal hp⟩⟩

theorem interp_negAV (ρ : Nat → V) (P : Term) :
    interp V ρ (negAV P) = truthVal (¬ ∃ x, x ∈ˢ interp V ρ P) := by
  show piV (interp V ρ P) (fun _ => (empty : V)) = _
  rw [piV_eq_zero (fun _ _ => univ_zero (V := V) ▸ empty_mem_univ 0), piR_zero]
  refine truthVal_congr ⟨fun h ⟨x, hx⟩ => ?_, fun h x hx => absurd ⟨x, hx⟩ h⟩
  obtain ⟨y, hy⟩ := h x hx
  exact not_mem_empty y hy

/-- **The squash body reads back as the squash carrier**, with no
premise at all. -/
theorem sqBodyAV_interp :
    ∀ (Fs : List Term) (ρ : Nat → V),
      interp V ρ (sqBodyAV Fs) = towerSet 0 (teleOfFields ρ Fs)
  | [], _ => rfl
  | F :: Fs, ρ => by
    show interp V ρ (negAV (.pi F (negAV (sqBodyAV Fs)))) = _
    rw [interp_negAV, teleOfFields_cons]
    show _ = sigmaSet 0 (interp V ρ F)
      (fun a => towerSet 0 (teleOfFields (cons a ρ) Fs))
    rw [sigmaSet_zero]
    refine truthVal_congr ?_
    rw [interp_pi, piV_eq_zero (fun x _ => by
      rw [interp_negAV]; exact truthVal_mem_univZero _), piR_zero, exists_mem_truthVal]
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

/-- The squash body's reading is a type (a truth value). -/
theorem IsTy_sqBody (Fs : List Term) (ρ : Nat → V) :
    IsTy (interp V ρ (sqBodyAV Fs)) := by
  rw [sqBodyAV_interp]
  exact Or.inl towerSet_zero_univZero_teleOfFields

/-- **The squash body is graded** from the chain's own gradings. -/
theorem sqBodyAV_wellDenoted :
    ∀ {Fs : List Term} {ρ : Nat → V}, FieldsOkB 0 ρ Fs →
      WellDenoted V ρ (sqBodyAV Fs)
  | [], ρ, _ => by simp [sqBodyAV]
  | F :: Fs, ρ, hok => by
    show WellDenoted V ρ (negAV (.pi F (negAV (sqBodyAV Fs))))
    unfold negAV
    rw [WellDenoted_pi]
    refine ⟨?_, IsTy_piR _ _ _, fun _ _ => by simp, fun _ _ => IsTy_empty⟩
    rw [WellDenoted_pi]
    refine ⟨hok.1, hok.2.1, fun x hx => ?_, fun _ _ => IsTy_piR _ _ _⟩
    rw [WellDenoted_pi]
    exact ⟨sqBodyAV_wellDenoted (hok.2.2.2 x hx), IsTy_sqBody _ _,
      fun _ _ => by simp, fun _ _ => IsTy_empty⟩

/-- **The carrier body reads back as the tier's carrier**: under the
hereditary bound (O5's semantic form), the `.psigma` spelling
interprets to `towerSet w` of the interpreted telescope — at every
level, both regimes. -/
theorem towerBodyAVPos_interp {w : Nat} :
    ∀ {Fs : List Term} {ρ : Nat → V}, FieldsBound w ρ Fs →
      interp V ρ (towerBodyAVPos w Fs)
        = towerSet w (teleOfFields ρ Fs)
  | [], _, _ => rfl
  | F :: Fs, ρ, hb => by
    have hA : interp V ρ F ∈ˢ (univ w : V) := hb.1
    have hG : ∀ x, x ∈ˢ interp V ρ F →
        interp V (cons x ρ) (towerBodyAVPos w Fs)
          = towerSet w (teleOfFields (cons x ρ) Fs) :=
      fun x hx => towerBodyAVPos_interp (hb.2 x hx)
    have hB : (lamV (interp V ρ F)
          fun x => interp V (cons x ρ) (towerBodyAVPos w Fs))
        ∈ˢ psigmaFibreSpace V w (interp V ρ F) :=
      lamV_mem (fun x hx => by
        rw [hG x hx]
        exact towerSet_univ_teleOfFields (hb.2 x hx)) fun _ _ => IsTy_univ w
    have hbv : bval V .psigma [w, w] = psigmaV V w w := rfl
    show SetTheory.app (SetTheory.app (bval V .psigma [w, w])
        (interp V ρ F))
        (lamV (interp V ρ F)
          fun x => interp V (cons x ρ) (towerBodyAVPos w Fs))
      = towerSet w (teleOfFields ρ (F :: Fs))
    rw [hbv, psigmaV_app V hA hB,
      show Nat.max w w = w from Nat.max_self w, teleOfFields_cons]
    show sigmaSet w _ _ = sigmaSet w _ _
    exact sigma_congr fun x hx => by
      rw [app_lamV hx, hG x hx]

/-- **The carrier body reads back as the tier's carrier**, both
regimes: unconditionally at squash, under the hereditary bound (O5's
semantic form) in the graph regime. -/
theorem towerBodyAV_interp {w : Nat} {Fs : List Term} {ρ : Nat → V}
    (hb : w ≠ 0 → FieldsBound w ρ Fs) :
    interp V ρ (towerBodyAV w Fs) = towerSet w (teleOfFields ρ Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_interp Fs ρ
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_interp (hb hw)

/-- The carrier's formation, both regimes. -/
theorem towerSet_univ_of_okB {w : Nat} {Fs : List Term} {ρ : Nat → V}
    (hb : w ≠ 0 → FieldsBound w ρ Fs) :
    towerSet w (teleOfFields ρ Fs) ∈ˢ (univ w : V) := by
  by_cases hw : w = 0
  · subst hw
    rw [univ_zero]
    exact towerSet_zero_univZero_teleOfFields
  · exact towerSet_univ_teleOfFields (hb hw)

/-- **The carrier body is graded** (`WellDenoted`): every app slot is
supplied by `psigmaV_rr_mem` and the fibre package by the tier's
formation laws; the hereditary premise carries the domains' own
grading. -/
theorem towerBodyAVPos_wellDenoted {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List Term} {ρ : Nat → V}, FieldsOkB w ρ Fs →
      WellDenoted V ρ (towerBodyAVPos w Fs)
  | [], ρ, _ => by simp [towerBodyAVPos]
  | F :: Fs, ρ, hok => by
    have hb : FieldsBound w ρ (F :: Fs) := hok.toBound hw
    have hA : interp V ρ F ∈ˢ (univ w : V) := hok.2.2.1 hw
    have hG : ∀ x, x ∈ˢ interp V ρ F →
        interp V (cons x ρ) (towerBodyAVPos w Fs)
          = towerSet w (teleOfFields (cons x ρ) Fs) :=
      fun x hx => towerBodyAVPos_interp (hb.2 x hx)
    have hbv : interp V ρ (.const .psigma [w, w]) = psigmaV V w w := rfl
    have hvac : ¬ w + 1 = 0 := Nat.succ_ne_zero w
    show WellDenoted V ρ (.app (.app (.const .psigma [w, w]) F)
      (.lam F (towerBodyAVPos w Fs)))
    rw [WellDenoted_app]
    refine ⟨?_, ?_, ?_⟩
    · -- the inner application `.psigma [w,w] F`
      rw [WellDenoted_app]
      exact ⟨trivial, hok.1,
        ⟨w + 1, univ w,
          fun A => piR (w + 1) (psigmaFibreSpace V w A)
            fun _ => (univ w : V),
          hbv ▸ psigmaV_rr_mem (V := V) w, hA, fun h => absurd h hvac,
          fun _ => IsTy_univ w⟩⟩
    · -- the fibre λ
      rw [WellDenoted_lam]
      refine ⟨hok.1, hok.2.1,
        fun x hx => towerBodyAVPos_wellDenoted hw (hok.2.2.2 x hx),
        ⟨fun _ => (univ w : V), fun x hx => ?_, fun _ _ => IsTy_univ w⟩⟩
      rw [hG x hx]
      exact towerSet_univ_teleOfFields (hb.2 x hx)
    · -- the outer application's kind slot
      refine ⟨w + 1, psigmaFibreSpace V w (interp V ρ F),
        fun _ => (univ w : V), ?_, ?_, fun h => absurd h hvac,
        fun _ => IsTy_piR _ _ _⟩
      · show SetTheory.app (interp V ρ (.const .psigma [w, w]))
            (interp V ρ F) ∈ˢ _
        rw [hbv]
        exact app_mem_piR_pos hvac (psigmaV_rr_mem (V := V) w) hA
      · rw [interp_lam]
        exact lamV_mem (fun x hx => by
          rw [hG x hx]
          exact towerSet_univ_teleOfFields (hb.2 x hx)) fun _ _ => IsTy_univ w

/-- **The carrier body is graded** (`WellDenoted`), both regimes. -/
theorem towerBodyAV_wellDenoted {w : Nat} {Fs : List Term} {ρ : Nat → V}
    (hok : FieldsOkB w ρ Fs) : WellDenoted V ρ (towerBodyAV w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [towerBodyAV_zero]; exact sqBodyAV_wellDenoted hok
  · rw [towerBodyAV_pos hw]; exact towerBodyAVPos_wellDenoted hw hok

/-! ## The λ/Π-tower formers

`mkLamsAV`/`mkPisAV` are the generic tower formers over peeled binder
domains; `stripPisAV` is the peel whose inversion hands the wiring the
`(domains, body)` decomposition of a stored type's reading. -/

/-- The λ-tower former over a list of domains. -/
def mkLamsAV : List Term → Term → Term
  | [], b => b
  | d :: ds, b => .lam d (mkLamsAV ds b)

/-- The Π-tower former over a list of domains — the shape of a stored
Π-type's reading. -/
def mkPisAV : List Term → Term → Term
  | [], b => b
  | d :: ds, b => .pi d (mkPisAV ds b)

/-- A Π-tower over a sort is a tower of function spaces. -/
theorem towerEnds_mkPisAV : ∀ (ab : List Term) (ρ : Nat → V) (w : Nat),
    TowerEnds ab.length (interp V ρ (mkPisAV ab (.sort w))) w
  | [], _, _ => rfl
  | _ :: ab, ρ, w => ⟨_, _, rfl, fun a _ => towerEnds_mkPisAV ab (cons a ρ) w⟩

/-- A fit of a Π-tower over a sort is a path through it. -/
theorem towerPath_of_spineFit {w : Nat} : ∀ {ab : List Term} {ρ : Nat → V} {vs : List V},
    SpineFit ρ ab vs → TowerPath ab.length (interp V ρ (mkPisAV ab (.sort w))) w
  | [], _, [], _ => .zero
  | _ :: ab, ρ, _ :: _, h =>
    .succ (fun x _ => towerEnds_mkPisAV ab (cons x ρ) w) h.1 (towerPath_of_spineFit h.2)
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- A Π-tower over a sort that a walk reads above `0`, along a fit, is above `0`. -/
theorem sort_ne_zero_of_walk {ab : List Term} {ρ : Nat → V} {vs : List V} {w w' : Nat}
    (hfit : SpineFit ρ ab vs)
    (ht : TowerEndsPt ab.length (interp V ρ (mkPisAV ab (.sort w))) w') (hw : w' ≠ 0) : w ≠ 0 :=
  (towerPath_of_spineFit hfit).ne_zero ht hw

/-- A Π-tower over a sort reads to a type: a function space, or the universe. -/
theorem IsTy_mkPisAV_sort (ds : List Term) (w : Nat) (ρ : Nat → V) :
    IsTy (interp V ρ (mkPisAV ds (.sort w))) := by
  cases ds with
  | nil => exact IsTy_univ w
  | cons _ _ => exact IsTy_piV

/-! ### Fits of one telescope of types, compared off the point (task #342 L7)

The conditional claims compare two
values only where neither is the point.  Two spines fitting ONE
telescope whose domains are types are still equal everywhere: position
by position, under equal earlier values, the two values lie in one
type, whose members are all the point or none of them
(`IsTy.eq_of_ne_pt`).  This is the fragment's `FitsVals_eq_of_cond`. -/

/-- **The domains of a telescope are types** under every fitting
prefix. -/
def SpineTy (ρ : Nat → V) : List Term → Prop
  | [] => True
  | F :: Fs => IsTy (interp V ρ F) ∧ ∀ a, a ∈ˢ interp V ρ F → SpineTy (cons a ρ) Fs

/-- A graded Π-tower's domains are types (`WellDenoted`'s Π clause). -/
theorem spineTy_of_wellDenoted_mkPisAV {B : Term} :
    ∀ {ab : List Term} {ρ : Nat → V},
      WellDenoted V ρ (mkPisAV ab B) → SpineTy ρ ab
  | [], _, _ => trivial
  | d :: ab, ρ, h => by
    have h' : WellDenoted V ρ (.pi d (mkPisAV ab B)) := h
    rw [WellDenoted_pi] at h'
    exact ⟨h'.2.1, fun a ha => spineTy_of_wellDenoted_mkPisAV (h'.2.2.1 a ha)⟩

/-- A telescope's prefix is a telescope of types. -/
theorem SpineTy.take :
    ∀ {Fs : List Term} {ρ : Nat → V} (n : Nat), SpineTy ρ Fs → SpineTy ρ (Fs.take n)
  | [], _, _, _ => by rw [List.take_nil]; trivial
  | _ :: _, _, 0, _ => trivial
  | _ :: _, _, n + 1, h => ⟨h.1, fun a ha => SpineTy.take n (h.2 a ha)⟩

/-- A graded field telescope (`FieldsOkB`) is a telescope of types. -/
theorem FieldsOkB.spineTy {w : Nat} :
    ∀ {Fs : List Term} {ρ : Nat → V}, FieldsOkB w ρ Fs → SpineTy ρ Fs
  | [], _, _ => trivial
  | _ :: _, _, h => ⟨h.2.1, fun a ha => FieldsOkB.spineTy (h.2.2.2 a ha)⟩

/-- **Fitting values compared where neither is the point are equal**
(`FitsVals_eq_of_cond`): two spines fitting one telescope of types,
equal at every position where neither value is the point, are equal. -/
theorem spineFit_eq_of_cond :
    ∀ {Fs : List Term} {ρ : Nat → V} {as bs : List V},
      SpineTy ρ Fs → SpineFit ρ Fs as → SpineFit ρ Fs bs →
      (∀ p ∈ as.zip bs, p.1 ≠ pt → p.2 ≠ pt → p.1 = p.2) → as = bs
  | [], _, [], [], _, _, _, _ => rfl
  | [], _, _ :: _, _, _, h, _, _ => h.elim
  | [], _, [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, _, [], _, _, h, _, _ => h.elim
  | _ :: _, _, _ :: _, [], _, _, h, _ => h.elim
  | F :: Fs, ρ, a :: as, b :: bs, hT, ha, hb, h => by
    have hab : a = b := hT.1.eq_of_ne_pt ha.1 hb.1 (h (a, b) List.mem_cons_self)
    subst hab
    rw [spineFit_eq_of_cond (hT.2 a ha.1) ha.2 hb.2
      fun p hp => h p (List.mem_cons_of_mem _ hp)]

/-- `spineFit_eq_of_cond` positionwise: equal where neither is the
point, at every position below the spines' common length. -/
theorem spineFit_eq_of_cond_getD {Fs : List Term} {ρ : Nat → V} {as bs : List V}
    (hT : SpineTy ρ Fs) (ha : SpineFit ρ Fs as) (hb : SpineFit ρ Fs bs)
    (h : ∀ i, i < Fs.length → as.getD i pt ≠ pt → bs.getD i pt ≠ pt →
      as.getD i pt = bs.getD i pt) : as = bs := by
  refine spineFit_eq_of_cond hT ha hb fun p hp => ?_
  obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hp
  have hia : i < as.length := by
    have := hi; rw [List.length_zip] at this; omega
  have hib : i < bs.length := by
    have := hi; rw [List.length_zip] at this; omega
  have hiF : i < Fs.length := by rw [← ha.length_eq]; exact hia
  rw [List.getElem_zip] at hpi
  subst hpi
  have := h i hiF
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hia, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hib, Option.getD_some] at this
  exact this

/-- Peel `n` Π-binders off a reading. -/
def stripPisAV : Nat → Term → Option (List Term × Term)
  | 0, e => some ([], e)
  | n + 1, .pi A B =>
    (stripPisAV n B).map fun p => (A :: p.1, p.2)
  | _ + 1, _ => none

/-- The peel's inversion: a successful strip exhibits the reading as
the Π-tower of its parts (the wiring's hook). -/
theorem stripPisAV_eq_mkPis :
    ∀ {n : Nat} {e : Term} {ps : List Term} {b : Term},
      stripPisAV n e = some (ps, b) → e = mkPisAV ps b ∧ ps.length = n
  | 0, e, ps, b, h => by
    obtain ⟨rfl, rfl⟩ : ps = [] ∧ b = e := by
      simpa [stripPisAV] using h.symm
    exact ⟨rfl, rfl⟩
  | n + 1, .pi A B, ps, b, h => by
    simp only [stripPisAV, Option.map_eq_some_iff] at h
    obtain ⟨⟨ps', b'⟩, hstrip, heq⟩ := h
    obtain ⟨rfl, rfl⟩ : A :: ps' = ps ∧ b' = b := by
      simpa using heq
    obtain ⟨hB, hlen⟩ := stripPisAV_eq_mkPis hstrip
    exact ⟨by rw [mkPisAV, ← hB], by simp [hlen]⟩

/-- **The generic λ-tower fold**: applying the tower along a fitting
spine computes the body at the spine's environment (`app_lamV`
iterated). -/
theorem mkLamsAV_fold :
    ∀ {ds : List Term} {b : Term} {ρ : Nat → V} {as : List V},
      SpineFit ρ ds as →
      as.foldl SetTheory.app (interp V ρ (mkLamsAV ds b))
        = interp V (consList as ρ) b
  | [], _, _, [], _ => rfl
  | [], _, _, _ :: _, hsp => hsp.elim
  | _ :: _, _, _, [], hsp => hsp.elim
  | d :: ds, b, ρ, a :: as, hsp => by
    show (as.foldl SetTheory.app
      (SetTheory.app (lamV (interp V ρ d)
        fun x => interp V (cons x ρ) (mkLamsAV ds b)) a)) = _
    rw [app_lamV hsp.1]
    exact mkLamsAV_fold hsp.2

/-! ### The λ-tower over a Π-tower's domains, generically

The constructor and recursor leaves are λ-towers over their Π-type's
own domains.  `UnderTowerOk` is the single hereditary premise;
`mkLamsAV_mem` and `mkLamsAV_wellDenoted` are the once-for-all
membership and grading. -/

/-- The hereditary premise of the tower's laws: each domain graded and
a type, and at every fitting spine the body is graded and a member of
the result type's reading, which is a type. -/
def UnderTowerOk (ρ : Nat → V) (b T : Term) :
    List Term → Prop
  | [] => WellDenoted V ρ b ∧ interp V ρ b ∈ˢ interp V ρ T ∧ IsTy (interp V ρ T)
  | d :: ds => WellDenoted V ρ d ∧ IsTy (interp V ρ d) ∧
      ∀ a, a ∈ˢ interp V ρ d → UnderTowerOk (cons a ρ) b T ds

/-- The residual Π-tower's reading is a type: a function space, or the
base's type. -/
theorem underTowerOk_res_IsTy {b T : Term} :
    ∀ {ds : List Term} {ρ : Nat → V},
      UnderTowerOk ρ b T ds → IsTy (interp V ρ (mkPisAV ds T))
  | [], _, h => h.2.2
  | _ :: _, _, _ => IsTy_piV

/-- **The tower's membership**: the λ-tower lies in the Π-tower over
the same domains (`lamV_mem` per binder, the residual towers' types as
the fibres, the base's membership at the bottom). -/
theorem mkLamsAV_mem {b T : Term} :
    ∀ {ds : List Term} {ρ : Nat → V},
      UnderTowerOk ρ b T ds →
      interp V ρ (mkLamsAV ds b) ∈ˢ interp V ρ (mkPisAV ds T)
  | [], _, h => h.2.1
  | d :: ds, ρ, h => by
    show (lamV (interp V ρ d)
        fun a => interp V (cons a ρ) (mkLamsAV ds b))
      ∈ˢ piV (interp V ρ d)
        fun a => interp V (cons a ρ) (mkPisAV ds T)
    exact lamV_mem (fun a ha => mkLamsAV_mem (h.2.2 a ha))
      fun a ha => underTowerOk_res_IsTy (h.2.2 a ha)

/-- **The tower's grading**: the λ-tower is graded; its fibre
packages are the interpreted residual Π-towers, membership from
`mkLamsAV_mem` at each suffix. -/
theorem mkLamsAV_wellDenoted {b T : Term} :
    ∀ {ds : List Term} {ρ : Nat → V},
      UnderTowerOk ρ b T ds →
      WellDenoted V ρ (mkLamsAV ds b)
  | [], _, h => h.1
  | d :: ds, ρ, h => by
    show WellDenoted V ρ (.lam d (mkLamsAV ds b))
    rw [WellDenoted_lam]
    refine ⟨h.1, h.2.1, fun a ha => mkLamsAV_wellDenoted (h.2.2 a ha),
      ⟨fun a => interp V (cons a ρ) (mkPisAV ds T),
       fun a ha => mkLamsAV_mem (h.2.2 a ha),
       fun a ha => underTowerOk_res_IsTy (h.2.2 a ha)⟩⟩


/-!
## The constructor tupler

`mkTowerGo w Fs` spells the tier's `mkTower` — the right-nested
`.psigmaMk [w, w]` application tower with the `.punitUnit [w]` terminator
— **at the constructor λ-frame**: the field values are the frame's own
bound variables (`.bvar m`, `m` = the count of later fields), and the
pair type arguments are the field domains lifted to that frame
(`liftN (m + 1)`, cutoff `0` for the first-component type, cutoff `1`
under the fibre λ).

The de Bruijn accounting, once: the input list is scoped as peeled —
domain `j` under the parameters plus `j` earlier fields — while every
application node sits under ALL `nF` field binders.  A suffix head
with `m` later fields therefore lifts by `m + 1` (its own binder plus
the `m` later ones); the recursive call's input is scoped one binder
deeper, and its lift amount is one smaller — the arithmetic is
self-consistent with no length parameter threaded.

`mkTowerGo_interp` is the one interpretation equation, two regimes in
one statement: at a fitting spine the tupler reads back as
`if w = 0 then pt else mkTower bs` — exactly `psigmaMkV_app`'s own
collapse, and exactly what the tier expects (`mkTower_mem` at the
graph regime, `pt_mem_tower` at squash).  The premises are
`FieldsBound` + `SpineFit`, nothing else.
-/


/-! ## The environment kit for the λ-frame -/

omit [SetTheory V] in
theorem shiftE_consList_add :
    ∀ (bs : List V) (j : Nat) (ρ : Nat → V),
      shiftE (bs.length + j) 0 (consList bs ρ) = shiftE j 0 ρ
  | [], j, ρ => by simp
  | b :: bs, j, ρ => by
    rw [consList_cons,
      show (b :: bs).length + j = bs.length + (j + 1) by
        simp [List.length_cons]; omega,
      shiftE_consList_add bs (j + 1) (cons b ρ), shiftE_succ_cons]

omit [SetTheory V] in
/-- Dropping a spine's worth of bindings lands back at the base
environment. -/
theorem shiftE_consList (bs : List V) (ρ : Nat → V) :
    shiftE bs.length 0 (consList bs ρ) = ρ := by
  have h := shiftE_consList_add bs 0 ρ
  rwa [shiftE_zero_zero] at h

omit [SetTheory V] in
theorem consList_apply_add :
    ∀ (bs : List V) (ρ : Nat → V) (i : Nat),
      consList bs ρ (i + bs.length) = ρ i
  | [], _, _ => rfl
  | b :: bs, ρ, i => by
    rw [consList_cons,
      show i + (b :: bs).length = (i + 1) + bs.length by
        simp [List.length_cons]; omega,
      consList_apply_add bs (cons b ρ) (i + 1), cons_succ]

/-- A spine position below the spine's length reads the spine. -/
theorem consList_getD_of_lt : ∀ (as : List V) (σ : Nat → V) (k : Nat), k < as.length →
    consList as σ k = as.getD (as.length - 1 - k) pt
  | [], _, _, hk => absurd hk (Nat.not_lt_zero _)
  | a :: as, σ, k, hk => by
    rw [consList_cons]
    rcases Nat.lt_or_ge k as.length with hlt | hge
    · rw [consList_getD_of_lt as (cons a σ) k hlt, List.length_cons,
        show as.length + 1 - 1 - k = (as.length - 1 - k) + 1 from by omega, List.getD_cons_succ]
    · have hk' : k = as.length := by simp at hk; omega
      subst hk'
      rw [← Nat.zero_add as.length, consList_apply_add, cons_zero, List.length_cons,
        show as.length + 1 - 1 - (0 + as.length) = 0 from by omega, List.getD_cons_zero]

/-! ## The tupler -/

/-- The constructor tupler at the λ-frame (see the module docstring
for the de Bruijn accounting). -/
def mkTowerGoPos (w : Nat) : List Term → Term
  | [] => .const .punitUnit [w]
  | F :: Fs =>
    .app (.app (.app (.app (.const .psigmaMk [w, w])
        (F.liftN (Fs.length + 1)))
        (.lam (F.liftN (Fs.length + 1))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
        (.bvar Fs.length))
      (mkTowerGoPos w Fs)

/-- The tupler, both regimes: at squash the constructor's value is the
proof point outright (`.punitUnit`, O4 — the pair
constructor's pinned valuation cannot take a data field there), the
pair tower above. -/
def mkTowerGo (w : Nat) (Fs : List Term) : Term :=
  if w = 0 then .const .punitUnit [] else mkTowerGoPos w Fs

theorem mkTowerGo_zero (Fs : List Term) :
    mkTowerGo 0 Fs = .const .punitUnit [] := ite_eq_left rfl

theorem mkTowerGo_pos {w : Nat} (hw : w ≠ 0) (Fs : List Term) :
    mkTowerGo w Fs = mkTowerGoPos w Fs := ite_eq_right hw

/-- **The tupler reads back as the tier's tupler**, two regimes in one
statement: at a fitting spine, `mkTower bs` in the graph regime and
`pt` at squash — `psigmaMkV_app`'s own collapse, matching the tier's
`mkTower_mem`/`pt_mem_tower` intro pair. -/
theorem mkTowerGoPos_interp {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List Term} {ρp : Nat → V} {bs : List V},
      FieldsBound w ρp Fs → SpineFit ρp Fs bs →
      interp V (consList bs ρp) (mkTowerGoPos w Fs)
        = if w = 0 then pt else mkTower bs
  | [], _, [], _, _ => by rw [ite_eq_right hw]; exact unitAt_pos hw
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hb, hsp => by
    have hlen : bs.length = Fs.length := hsp.2.length_eq
    -- the frame environment and its retraction to the base
    have hshift : shiftE (Fs.length + 1) 0 (consList bs (cons b ρp)) = ρp := by
      rw [← hlen,
        show bs.length + 1 = bs.length + (0 + 1) by rw [Nat.zero_add],
        shiftE_consList_add bs (0 + 1) (cons b ρp), Nat.zero_add,
        shiftE_succ_cons, shiftE_zero_zero]
    -- the pair-type argument's interpretation
    have hA : interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))
        = interp V ρp F := by
      rw [interp_liftN, hshift]
    -- the fibre λ's interpretation
    have hBfun : ∀ x : V,
        interp V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)
        = interp V (cons x ρp) (towerBodyAV w Fs) := fun x => by
      rw [interp_liftN, ← cons_shiftE, hshift]
    -- the field value's read-back
    have hval : consList bs (cons b ρp) (Fs.length) = b := by
      rw [← hlen, show bs.length = 0 + bs.length by rw [Nat.zero_add],
        consList_apply_add bs (cons b ρp) 0, cons_zero]
    -- the recursive read-back
    have hrec : interp V (consList bs (cons b ρp)) (mkTowerGoPos w Fs)
        = if w = 0 then pt else mkTower bs :=
      mkTowerGoPos_interp hw (hb.2 b hsp.1) hsp.2
    -- the psigmaMk application premises
    have hAm : interp V ρp F ∈ˢ (univ w : V) := hb.1
    have hBm : (lamV (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs))
        ∈ˢ psigmaFibreSpace V w (interp V ρp F) :=
      lamV_mem (fun x hx => by
        rw [towerBodyAV_interp (fun _ => hb.2 x hx)]
        exact towerSet_univ_teleOfFields (hb.2 x hx)) fun _ _ => IsTy_univ w
    have hfib : SetTheory.app (lamV (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs)) b
        = towerSet w (teleOfFields (cons b ρp) Fs) := by
      rw [app_lamV hsp.1, towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
    have hbm : (if w = 0 then pt else mkTower bs)
        ∈ˢ SetTheory.app (lamV (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs)) b := by
      rw [hfib]
      split
      · next hz => exact hz ▸ pt_mem_tower_teleOfFields hsp.2
      · next hnz => exact mkTower_mem_teleOfFields hnz hsp.2
    -- assemble
    show SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (bval V .psigmaMk [w, w])
        (interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1))))
        (lamV
          (interp V (consList bs (cons b ρp)) (F.liftN (Fs.length + 1)))
          fun x => interp V (cons x (consList bs (cons b ρp)))
            ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
        (consList bs (cons b ρp) Fs.length))
        (interp V (consList bs (cons b ρp)) (mkTowerGoPos w Fs))
      = if w = 0 then pt else mkTower (b :: bs)
    have hbv : bval V .psigmaMk [w, w] = psigmaMkV V w w := rfl
    rw [hA, hval, hrec]
    have hBeq : (fun x => interp V (cons x (consList bs (cons b ρp)))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1))
        = fun x => interp V (cons x ρp) (towerBodyAV w Fs) :=
      funext hBfun
    rw [hBeq, hbv, psigmaMkV_app V hAm hBm hsp.1 hbm,
      show Nat.max w w = w from Nat.max_self w]
    split <;> rfl

/-- **The tupler reads back as the tier's tupler**, both regimes. -/
theorem mkTowerGo_interp {w : Nat} {Fs : List Term} {ρp : Nat → V}
    {bs : List V} (hb : w ≠ 0 → FieldsBound w ρp Fs)
    (hsp : SpineFit ρp Fs bs) :
    interp V (consList bs ρp) (mkTowerGo w Fs)
      = if w = 0 then pt else mkTower bs := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero, ite_eq_left rfl]; rfl
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_interp hw (hb hw) hsp

/-! ## The tupler's grading -/

/-- The `[w, w]` instance of the pair constructor's membership in its
function space. -/
theorem psigmaMkV_ww_mem (w : Nat) :
    psigmaMkV V w w ∈ˢ piV (univ w : V) (fun A =>
      piV (psigmaFibreSpace V w A) (fun B =>
        piV A (fun a =>
          piV (SetTheory.app B a) (fun _ =>
            sigmaSet w A fun x => SetTheory.app B x)))) := by
  have h := psigmaMkV_mem V w w
  rwa [show Nat.max w w = w from Nat.max_self w] at h

/-- **The tupler is graded** (`WellDenoted`): the four application slots
are `psigmaMkV_ww_mem` chained down by `app_mem_piR`, the squash-side
fibre conditions all landing on `piR_zero_mem_univZero`/`sigmaSet`'s
truth value. -/
theorem mkTowerGoPos_wellDenoted {w : Nat} (hw : w ≠ 0) :
    ∀ {Fs : List Term} {ρp : Nat → V} {bs : List V},
      FieldsOkB w ρp Fs → SpineFit ρp Fs bs →
      WellDenoted V (consList bs ρp) (mkTowerGoPos w Fs)
  | [], _, [], _, _ => by simp [mkTowerGoPos]
  | [], _, _ :: _, _, hsp => hsp.elim
  | _ :: _, _, [], _, hsp => hsp.elim
  | F :: Fs, ρp, b :: bs, hok, hsp => by
    have hb : FieldsBound w ρp (F :: Fs) := hok.toBound hw
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
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)
        = interp V (cons x ρp) (towerBodyAV w Fs) := fun x => by
      rw [interp_liftN, ← cons_shiftE, hshift]
    have hval : consList bs (cons b ρp) (Fs.length) = b := by
      rw [← hlen, show bs.length = 0 + bs.length by rw [Nat.zero_add],
        consList_apply_add bs (cons b ρp) 0, cons_zero]
    have hrec : interp V (consList bs (cons b ρp)) (mkTowerGoPos w Fs)
        = if w = 0 then pt else mkTower bs :=
      mkTowerGoPos_interp hw (hb.2 b hsp.1) hsp.2
    have hAm : interp V ρp F ∈ˢ (univ w : V) := hb.1
    have hBv : interp V (consList bs (cons b ρp))
        (Term.lam (F.liftN (Fs.length + 1))
          ((towerBodyAV w Fs).liftN (Fs.length + 1) 1))
        = lamV (interp V ρp F)
            (fun x => interp V (cons x ρp) (towerBodyAV w Fs)) := by
      rw [interp_lam, hA, funext hBfun]
    have hBm : (lamV (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs))
        ∈ˢ psigmaFibreSpace V w (interp V ρp F) :=
      lamV_mem (fun x hx => by
        rw [towerBodyAV_interp (fun _ => hb.2 x hx)]
        exact towerSet_univ_teleOfFields (hb.2 x hx)) fun _ _ => IsTy_univ w
    -- the membership chain down the function spaces
    have hm0 := psigmaMkV_ww_mem (V := V) w
    have hm1 : SetTheory.app (psigmaMkV V w w) (interp V ρp F)
        ∈ˢ piV (psigmaFibreSpace V w (interp V ρp F)) (fun B =>
          piV (interp V ρp F) (fun a =>
            piV (SetTheory.app B a) (fun _ =>
              sigmaSet w (interp V ρp F) fun x => SetTheory.app B x))) :=
      app_mem_piV hm0 hAm
    have hm2 := app_mem_piV hm1 hBm
    have hm3 := app_mem_piV hm2 hsp.1
    have hfib : SetTheory.app (lamV (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs)) b
        = towerSet w (teleOfFields (cons b ρp) Fs) := by
      rw [app_lamV hsp.1, towerBodyAV_interp (fun _ => hb.2 b hsp.1)]
    have hrm : interp V (consList bs (cons b ρp)) (mkTowerGoPos w Fs)
        ∈ˢ SetTheory.app (lamV (interp V ρp F)
          fun x => interp V (cons x ρp) (towerBodyAV w Fs)) b := by
      rw [hrec, hfib]
      split
      · next hz => exact hz ▸ pt_mem_tower_teleOfFields hsp.2
      · next hnz => exact mkTower_mem_teleOfFields hnz hsp.2
    -- assemble the clause tree
    show WellDenoted V (consList bs (cons b ρp))
      (.app (.app (.app (.app (.const .psigmaMk [w, w])
          (F.liftN (Fs.length + 1)))
          (.lam (F.liftN (Fs.length + 1))
            ((towerBodyAV w Fs).liftN (Fs.length + 1) 1)))
          (.bvar Fs.length))
        (mkTowerGoPos w Fs))
    rw [WellDenoted_app]
    refine ⟨?_, mkTowerGoPos_wellDenoted hw (hok.2.2.2 b hsp.1) hsp.2, ?_⟩
    · -- the triple-application head
      rw [WellDenoted_app]
      refine ⟨?_, trivial, ?_⟩
      · -- the double-application head
        rw [WellDenoted_app]
        refine ⟨?_, ?_, ?_⟩
        · -- `.psigmaMk [w,w] A`
          rw [WellDenoted_app]
          refine ⟨trivial, ?_, ?_⟩
          · rw [WellDenoted_liftN, hshift]
            exact hok.1
          · exact piV_slot hm0 (by rw [interp_liftN, hshift]; exact hAm) (IsTy_univ w)
        · -- the fibre λ
          rw [WellDenoted_lam]
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
        · -- the second application's kind slot
          show ∃ v A B, SetTheory.app (interp V (consList bs (cons b ρp))
                (.const .psigmaMk [w, w]))
              (interp V (consList bs (cons b ρp))
                (F.liftN (Fs.length + 1))) ∈ˢ piR v A B ∧ _
          rw [hA, hBv]
          exact piV_slot hm1 hBm IsTy_piV
      · -- the third application's kind slot
        show ∃ v A B, SetTheory.app (SetTheory.app
              (interp V (consList bs (cons b ρp))
                (.const .psigmaMk [w, w]))
              (interp V (consList bs (cons b ρp))
                (F.liftN (Fs.length + 1))))
            (interp V (consList bs (cons b ρp))
              (.lam (F.liftN (Fs.length + 1))
                ((towerBodyAV w Fs).liftN (Fs.length + 1) 1))) ∈ˢ piR v A B ∧ _
        rw [hA, hBv, interp_bvar, hval]
        exact piV_slot hm2 hsp.1 hok.2.1
    · -- the outer application's kind slot
      show ∃ v A B, SetTheory.app (SetTheory.app (SetTheory.app
          (interp V (consList bs (cons b ρp))
            (.const .psigmaMk [w, w]))
          (interp V (consList bs (cons b ρp))
            (F.liftN (Fs.length + 1))))
          (interp V (consList bs (cons b ρp))
            (.lam (F.liftN (Fs.length + 1))
              ((towerBodyAV w Fs).liftN (Fs.length + 1) 1))))
        (interp V (consList bs (cons b ρp)) (.bvar Fs.length)) ∈ˢ piR v A B ∧ _
      rw [hA, hBv, interp_bvar, hval]
      exact piV_slot hm3 hrm (by
        rw [hfib]; exact IsTy_of_mem_univ (towerSet_univ_teleOfFields (hb.2 b hsp.1)))

/-- **The tupler is graded** (`WellDenoted`), both regimes. -/
theorem mkTowerGo_wellDenoted {w : Nat} {Fs : List Term} {ρp : Nat → V}
    {bs : List V} (hok : FieldsOkB w ρp Fs) (hsp : SpineFit ρp Fs bs) :
    WellDenoted V (consList bs ρp) (mkTowerGo w Fs) := by
  by_cases hw : w = 0
  · subst hw; rw [mkTowerGo_zero]; simp
  · rw [mkTowerGo_pos hw]; exact mkTowerGoPos_wellDenoted hw hok hsp

/-! ## Walking the graded chain along a prefix spine -/

/-- Walking a fitting prefix spine drops the graded chain to the
suffix. -/
theorem FieldsOkB.drop {w : Nat} :
    ∀ {Fs₁ : List Term} {as : List V} {Fs₂ : List Term}
      {ρ : Nat → V},
      FieldsOkB w ρ (Fs₁ ++ Fs₂) → SpineFit ρ Fs₁ as →
      FieldsOkB w (consList as ρ) Fs₂
  | [], [], _, _, h, _ => h
  | [], _ :: _, _, _, _, hsp => hsp.elim
  | _ :: _, [], _, _, _, hsp => hsp.elim
  | _ :: Fs₁, a :: as, Fs₂, ρ, h, hsp => by
    exact FieldsOkB.drop (Fs₁ := Fs₁) (as := as) (Fs₂ := Fs₂)
      (ρ := cons a ρ) (h.2.2.2 a hsp.1) hsp.2


/-!
## The projection spine on tower members

`projList` as a mapped range, and the grading of the uniform projection
spelling `projNV` on members of a tower carrier — the two facts the
structure and sum stages read a tower's fields through.
-/


/-! ## Projection-list arithmetic -/

theorem projList_eq_map_range (n : Nat) (x : V) :
    projList n x = (List.range n).map fun i => projS i x := by
  apply List.ext_getElem
  · rw [projList_length, List.length_map, List.length_range]
  · intro i h1 h2
    rw [List.getElem_map, List.getElem_range]
    exact projList_get n i x (by rwa [projList_length] at h1)

/-! ## The projection spine's grading -/

/-- **The uniform projection spelling is graded on tower members**:
each `.proj` node's `WellDenoted` package is one `sigmaSet w` level of
the carrier, peeled by `mem_sigma_elim` — both regimes (at squash the
subject is `pt` throughout and the tail memberships are `pt`'s). -/
theorem projNV_wellDenoted_tower {w : Nat} :
    ∀ {i : Nat} {Fs : List Term} {ρ : Nat → V} {e : Term}
      {σ : Nat → V},
      WellDenoted V σ e →
      interp V σ e ∈ˢ towerSet w (teleOfFields ρ Fs) →
      FieldsBound w ρ Fs → i < Fs.length →
      WellDenoted V σ (projNV i e)
  | 0, F :: Fs', ρ, e, σ, hok, hx, hbnd, _ => by
    show WellDenoted V σ (.fst e)
    rw [WellDenoted]
    refine ⟨hok, w, w, interp V ρ F,
      fun a => towerSet w (teleOfFields (cons a ρ) Fs'), ?_, hbnd.1,
      fun a ha => towerSet_univ_teleOfFields (hbnd.2 a ha)⟩
    rwa [show Nat.max w w = w from Nat.max_self w]
  | i + 1, F :: Fs', ρ, e, σ, hok, hx, hbnd, hi => by
    obtain ⟨a, b, ha, hb, hz, hpos⟩ :=
      mem_sigma_elim (A := interp V ρ F)
        (B := fun a => towerSet w (teleOfFields (cons a ρ) Fs')) hx
    have hok1 : WellDenoted V σ (.snd e) := by
      rw [WellDenoted]
      refine ⟨hok, w, w, interp V ρ F,
        fun a => towerSet w (teleOfFields (cons a ρ) Fs'), ?_, hbnd.1,
        fun a' ha' => towerSet_univ_teleOfFields (hbnd.2 a' ha')⟩
      rwa [show Nat.max w w = w from Nat.max_self w]
    have hmem1 : interp V σ (.snd e)
        ∈ˢ towerSet w (teleOfFields (cons a ρ) Fs') := by
      rw [interp_snd]
      rcases Nat.eq_zero_or_pos w with rfl | hwpos
      · rw [hz rfl, ssnd_pt]
        rw [(towerSet_zero_elim _ hb).1] at hb
        exact hb
      · rw [hpos (Nat.pos_iff_ne_zero.mp hwpos), ssnd_spair]
        exact hb
    exact projNV_wellDenoted_tower (i := i) (Fs := Fs') (ρ := cons a ρ)
      (e := .snd e) hok1 hmem1 (hbnd.2 a ha)
      (by exact Nat.lt_of_succ_lt_succ hi)

end ConLeche.Semantics
