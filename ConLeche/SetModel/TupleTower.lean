module

public import ConLeche.SetTheory.Derive.Sigma

@[expose] public section

/-!
# The uniform tuple model: unit-terminated pair towers (agent/tuple-model)

The semantic carrier construction for directly-installed structures
(DESIGN.md, "AMENDMENT — the uniform tuple model"): every qualifying
structure's carrier is the **right-nested pair tower with unit
terminator**

    towerSet w ⟨F₀, …, F_{n−1}⟩ = F₀ ⋉ (F₁ ⋉ (… ⋉ (F_{n−1} ⋉ unitSetAt w)))

(each `⋉` a `sigmaSet w`, dependency right-nested along the field
telescope), the constructor is the uniform tupler `mkTower`, and the
semantic projection family is ONE definition depending only on the
index:

    projS i = sfst ∘ ssnd^i        (structure-independent)

The unit terminator is what buys index-only uniformity: with a bare
tail the last field would be read by `ssnd^{n−1}` (no `sfst`), making
the family depend on the arity — i.e. on the structure.  It also
gives the 0/1-field degeneracies for free (`n = 0`: the carrier is
the unit `unitSetAt w`, in the graph regime members exactly `∅ =
mkTower []`; `n = 1`: members are `spair a ∅` and `projS 0 = sfst` is
lawful).  The terminator is `{∅}`/`∅` rather than `{pt}`/`pt` (task
#342 C) so that a carrier never contains the proof point; `∅` is no
pair, so the destructors read it as they read `pt`.

Under the strictly first-order `SetTheory` axiomatization, `towerSet w T`
is **proof-carrying and zero-junk**, taking `h : HasTeleS w T` (witnessed
for any first-order definable telescope family `DefTeleS`).
-/

namespace ConLeche.SetTheory.Tower

universe u

/-- A dependent field-set telescope over `V`, indexed by its length:
field `i`'s set may depend on the values of fields `0..i−1`. -/
inductive TeleS (V : Type u) : Nat → Type u where
  | nil : TeleS V 0
  | cons {n : Nat} (A : V) (B : V → TeleS V n) : TeleS V (n + 1)

variable {V : Type u} [SetTheory V]

/-- `FitsS T as`: the value list `as` fits the telescope `T` — right
length, each value in its field's set at the earlier values. -/
def FitsS : {n : Nat} → TeleS V n → List V → Prop
  | _, .nil, [] => True
  | _, .nil, _ :: _ => False
  | _, .cons _ _, [] => False
  | _, .cons A B, a :: as => a ∈ˢ A ∧ FitsS (B a) as

/-- Relational specification of `towerSet w T = t`: `t` is the right-nested
`sigmaSet w` tower over `T` terminated by `unitSetAt w`. -/
def HasTower (w : Nat) : {n : Nat} → TeleS V n → V → Prop
  | _, .nil, t => t = unitSetAt w
  | _, .cons A B, t =>
    ∃ (F : V → V) (hS : HasSigmaPairs A F),
      (∀ a, a ∈ˢ A → HasTower w (B a) (F a)) ∧
      t = sigmaSet w A F hS

theorem HasTower.unique {w : Nat} : ∀ {n : Nat} {T : TeleS V n} {t₁ t₂ : V},
    HasTower w T t₁ → HasTower w T t₂ → t₁ = t₂
  | _, .nil, _, _, h₁, h₂ => h₁.trans h₂.symm
  | _, .cons _ _, _, _, h₁, h₂ => by
    obtain ⟨_, hS₁, hB₁, rfl⟩ := h₁
    obtain ⟨_, hS₂, hB₂, rfl⟩ := h₂
    exact sigmaSet_congr hS₁ hS₂ fun a ha => HasTower.unique (hB₁ a ha) (hB₂ a ha)

/-- Proof-carrying predicate asserting that `towerSet w T` exists as a set
in `V`. -/
def HasTeleS (w : Nat) {n : Nat} (T : TeleS V n) : Prop :=
  ∃ t : V, HasTower w T t

/-- Proof-carrying, zero-junk carrier: the right-nested `sigmaSet w` tower
over the telescope, terminated by the unit at level `w` (`unitSetAt w`:
`{pt}` at `0`, `{∅}` above — task #342 C). -/
noncomputable def towerSet (w : Nat) {n : Nat} (T : TeleS V n) (h : HasTeleS w T) : V :=
  Classical.choose h

theorem towerSet_irrel {w n : Nat} (T : TeleS V n) (h₁ h₂ : HasTeleS w T) :
    towerSet w T h₁ = towerSet w T h₂ :=
  HasTower.unique (Classical.choose_spec h₁) (Classical.choose_spec h₂)

theorem hasTeleS_nil (w : Nat) : HasTeleS w (.nil : TeleS V 0) :=
  ⟨unitSetAt w, rfl⟩

theorem towerSet_nil {w : Nat} {h : HasTeleS w (.nil : TeleS V 0)} :
    towerSet w (.nil : TeleS V 0) h = unitSetAt w :=
  Classical.choose_spec h

theorem towerSet_eq_of_nil {w : Nat} {T : TeleS V 0} (h : HasTeleS w T) :
    towerSet w T h = unitSetAt w := by
  cases T
  exact towerSet_nil

theorem hasTeleS_cons_of {w n : Nat} {A : V} {B : V → TeleS V n}
    (hB : ∀ a, a ∈ˢ A → HasTeleS w (B a))
    {F : V → V} (hF : ∀ a, (ha : a ∈ˢ A) → F a = towerSet w (B a) (hB a ha))
    (hS : HasSigmaPairs A F) : HasTeleS w (.cons A B) :=
  ⟨sigmaSet w A F hS, F, hS, fun a ha =>
    (hF a ha) ▸ Classical.choose_spec (hB a ha), rfl⟩

open Classical in
theorem hasTeleS_cons {w n : Nat} {A : V} {B : V → TeleS V n}
    (hB : ∀ a, a ∈ˢ A → HasTeleS w (B a))
    (hS : HasSigmaPairs A (fun a => if ha : a ∈ˢ A then towerSet w (B a) (hB a ha) else empty)) :
    HasTeleS w (.cons A B) :=
  hasTeleS_cons_of hB (fun _ ha => dite_eq_left ha) hS

theorem towerSet_cons_elim {w n : Nat} {A : V} {B : V → TeleS V n}
    (h : HasTeleS w (.cons A B)) :
    ∃ (F : V → V) (hS : HasSigmaPairs A F),
      (∀ a, a ∈ˢ A → HasTower w (B a) (F a)) ∧
      towerSet w (.cons A B) h = sigmaSet w A F hS :=
  Classical.choose_spec h

theorem HasTeleS.tail {w n : Nat} {A : V} {B : V → TeleS V n}
    (h : HasTeleS w (.cons A B)) {a : V} (ha : a ∈ˢ A) : HasTeleS w (B a) := by
  obtain ⟨_, F, _, hF, _⟩ := h
  exact ⟨F a, hF a ha⟩

theorem towerSet_cons_eq {w n : Nat} {A : V} {B : V → TeleS V n}
    {h : HasTeleS w (.cons A B)}
    (hB : ∀ a, a ∈ˢ A → HasTeleS w (B a))
    {F : V → V} (hF : ∀ a, (ha : a ∈ˢ A) → F a = towerSet w (B a) (hB a ha))
    (hS : HasSigmaPairs A F) :
    towerSet w (.cons A B) h = sigmaSet w A F hS :=
  HasTower.unique (Classical.choose_spec h)
    ⟨F, hS, fun a ha => (hF a ha) ▸ Classical.choose_spec (hB a ha), rfl⟩

theorem towerSet_cons {w n : Nat} {A : V} {B : V → TeleS V n}
    {h : HasTeleS w (.cons A B)}
    (hB : ∀ a, HasTeleS w (B a))
    (hS : HasSigmaPairs A (fun a => towerSet w (B a) (hB a))) :
    towerSet w (.cons A B) h = sigmaSet w A (fun a => towerSet w (B a) (hB a)) hS :=
  towerSet_cons_eq (fun a _ => hB a) (fun _ _ => rfl) hS

/-- The uniform tupler: the right-nested Kuratowski pair tower with
`∅` (the sole member of the positive-level unit `unitSetAt (w+1)`) as
terminator.  The tupler is read only in the graph regime (`w ≠ 0`); a
squash-regime member is `pt` outright. -/
noncomputable def mkTower : List V → V
  | [] => empty
  | a :: as => spair a (mkTower as)

/-- **The uniform semantic projection family**: `projS i = sfst ∘
ssnd^i`.  One definition for every structure and every index. -/
noncomputable def projS : Nat → V → V
  | 0, x => sfst x
  | i + 1, x => projS i (ssnd x)

/-- The first-`n` projection tuple of a value. -/
noncomputable def projList : Nat → V → List V
  | 0, _ => []
  | n + 1, x => sfst x :: projList n (ssnd x)

/-- The `k`-fold second projection (task #210 Part A): the tuple tower
below `k` leading pair components — `projS (i + k) x = projS i (dropS k
x)`, so a projection table with offset `k` reads its fields off
`dropS k` of the subject (`k = 1` at the fixpoint route's tagged
tower, whose first component is the constructor tag). -/
noncomputable def dropS : Nat → V → V
  | 0, x => x
  | k + 1, x => dropS k (ssnd x)

theorem projS_add_dropS : ∀ (i k : Nat) (x : V), projS (i + k) x = projS i (dropS k x)
  | _, 0, _ => rfl
  | i, k + 1, x => by
    show projS (i + k) (ssnd x) = projS i (dropS k (ssnd x))
    exact projS_add_dropS i k (ssnd x)

theorem dropS_pt : ∀ k : Nat, dropS k (pt : V) = pt
  | 0 => rfl
  | k + 1 => by show dropS k (ssnd pt) = pt; rw [ssnd_pt, dropS_pt k]

/-- The `i`-th field set of a telescope at a prefix valuation
(`empty` out of range — never consumed in range). -/
noncomputable def teleNth : {n : Nat} → TeleS V n → Nat → List V → V
  | _, .nil, _, _ => empty
  | _, .cons A _, 0, _ => A
  | _, .cons _ B, i + 1, a :: as => teleNth (B a) i as
  | _, .cons _ _, _ + 1, [] => empty

/-- `PropS T`: every field set is a truth value, hereditarily — the
levelwise `structSort = 0 → field sort = 0` bound, telescope-side. -/
def PropS : {n : Nat} → TeleS V n → Prop
  | _, .nil => True
  | _, .cons A B => A ∈ˢ (univZero : V) ∧ ∀ a, a ∈ˢ A → PropS (B a)

/-- `BoundS w T`: every field set lives in `univ w`, hereditarily —
the formation premise (per-field sorts `≤ w` via cumulativity). -/
def BoundS (w : Nat) : {n : Nat} → TeleS V n → Prop
  | _, .nil => True
  | _, .cons A B => A ∈ˢ (univ w : V) ∧ ∀ a, a ∈ˢ A → BoundS w (B a)

/-! ## Auxiliary lemmas -/

theorem FitsS.length_eq : ∀ {n} {T : TeleS V n} {as : List V},
    FitsS T as → as.length = n
  | _, .nil, [], _ => rfl
  | _, .cons _ _, _ :: _, h =>
    congrArg Nat.succ (FitsS.length_eq h.2)

theorem projList_length : ∀ (n : Nat) (x : V), (projList n x).length = n
  | 0, _ => rfl
  | n + 1, x => congrArg Nat.succ (projList_length n (ssnd x))

theorem projList_get : ∀ (n i : Nat) (x : V) (h : i < n),
    (projList n x)[i]'((projList_length n x).symm ▸ h) = projS i x
  | _ + 1, 0, _, _ => rfl
  | n + 1, i + 1, x, h =>
    projList_get n i (ssnd x) (Nat.lt_of_succ_lt_succ h)

theorem projList_take : ∀ (n i : Nat) (x : V), i ≤ n →
    (projList n x).take i = projList i x
  | _, 0, _, _ => rfl
  | n + 1, i + 1, x, h => by
    show sfst x :: (projList n (ssnd x)).take i = sfst x :: projList i (ssnd x)
    rw [projList_take n i (ssnd x) (Nat.le_of_succ_le_succ h)]

theorem projList_mkTower : ∀ (n : Nat) (as : List V), as.length = n →
    projList n (mkTower as) = as
  | 0, [], _ => rfl
  | n + 1, a :: as, h => by
    show sfst (spair a (mkTower as)) :: projList n (ssnd (spair a (mkTower as)))
      = a :: as
    rw [sfst_spair, ssnd_spair, projList_mkTower n as (Nat.succ.inj h)]

theorem projList_pt : ∀ n : Nat, projList n (pt : V) = List.replicate n pt
  | 0 => rfl
  | n + 1 => by
    show sfst (pt : V) :: projList n (ssnd (pt : V)) = pt :: List.replicate n pt
    rw [sfst_pt, ssnd_pt, projList_pt n]

/-- `projS` fixes `pt`: the interface's pt-vs-pair separation
(`sfst_pt`/`ssnd_pt`, from `pt_ne_kpair`) makes projection-of-`pt`
return `pt` — the correct proof-field answer, with no separate
`Prop`-structure variant. -/
theorem projS_pt : ∀ i : Nat, projS i (pt : V) = pt
  | 0 => sfst_pt
  | i + 1 => by rw [projS, ssnd_pt, projS_pt i]

/-- `FitsS` reads off `teleNth` membership: each fitting value is in
its field's set at the earlier values. -/
theorem fitsS_mem_teleNth : ∀ {n} {T : TeleS V n} {as : List V},
    (hf : FitsS T as) → ∀ (i : Nat) (h : i < n),
    as[i]'(FitsS.length_eq hf ▸ h) ∈ˢ teleNth T i (as.take i)
  | _, .cons _ _, _ :: _, hf, 0, _ => hf.1
  | _, .cons _ B, a :: as, hf, i + 1, h =>
    fitsS_mem_teleNth (T := B a) (as := as) hf.2 i (Nat.lt_of_succ_lt_succ h)

/-- `PropS` forces every fitting value to `pt`, so the all-`pt` list
fits whenever anything does. -/
theorem fitsS_replicate_of_prop : ∀ {n} {T : TeleS V n} {as : List V},
    PropS T → FitsS T as → FitsS T (List.replicate n pt)
  | _, .nil, [], _, _ => trivial
  | _, .cons _ B, a :: as, hP, hf => by
    have ha : a = pt := eq_pt_of_mem_univZero hP.1 hf.1
    show (pt : V) ∈ˢ _ ∧ FitsS (B pt) (List.replicate _ pt)
    exact ⟨ha ▸ hf.1, ha ▸ fitsS_replicate_of_prop (hP.2 a hf.1) hf.2⟩

/-! ## The law families (frozen in the DESIGN amendment) -/

/-- **Intro** (graph regime): a fitting tuple's tower is in the
carrier. -/
theorem mkTower_mem {w : Nat} (hw : w ≠ 0) :
    ∀ {n} {T : TeleS V n} {hT : HasTeleS w T} {as : List V},
    FitsS T as → mkTower as ∈ˢ towerSet w T hT
  | _, .nil, _, [], _ => by
    rw [towerSet_nil]
    show (empty : V) ∈ˢ unitSetAt w
    rw [← unitAt_pos hw]; exact unitAt_mem_unitSetAt w
  | _, .cons _ B, hT, a :: _, hf => by
    obtain ⟨F, hS, hF, heq⟩ := towerSet_cons_elim hT
    rw [heq]
    have hBa : HasTeleS w (B a) := ⟨F a, hF a hf.1⟩
    have hFa : F a = towerSet w (B a) hBa :=
      HasTower.unique (hF a hf.1) (Classical.choose_spec hBa)
    exact spair_mem hw hf.1 (hFa ▸ mkTower_mem hw (hT := hBa) hf.2)

/-- **Intro** (squash regime): the carrier at `w = 0` is the truth
value of fittability. -/
theorem pt_mem_tower : ∀ {n} {T : TeleS V n} {hT : HasTeleS 0 T} {as : List V},
    FitsS T as → (pt : V) ∈ˢ towerSet 0 T hT
  | _, .nil, _, [], _ => by
    rw [towerSet_nil, unitSetAt_zero]; exact pt_mem_unitSet
  | _, .cons _ B, hT, a :: _, hf => by
    obtain ⟨F, hS, hF, heq⟩ := towerSet_cons_elim hT
    rw [heq]
    have hBa : HasTeleS 0 (B a) := ⟨F a, hF a hf.1⟩
    have hFa : F a = towerSet 0 (B a) hBa :=
      HasTower.unique (hF a hf.1) (Classical.choose_spec hBa)
    exact pt_mem_sigma hf.1 (hFa ▸ pt_mem_tower (hT := hBa) hf.2)

/-- **Iota — UNCONDITIONAL**: no membership premise, no level.  The
checker's `.proj`/`mk` reduction is denotation-sound with no typing of
the fields at all. -/
theorem projS_mkTower : ∀ (i : Nat) (as : List V) (h : i < as.length),
    projS i (mkTower as) = as[i]
  | 0, a :: as, _ => by
    show sfst (spair a (mkTower as)) = a
    exact sfst_spair a (mkTower as)
  | i + 1, a :: as, h => by
    show projS i (ssnd (spair a (mkTower as))) = as[i]'(Nat.lt_of_succ_lt_succ h)
    rw [ssnd_spair]
    exact projS_mkTower i as (Nat.lt_of_succ_lt_succ h)

/-- The projection list of a point-terminated tower is the fields'
prefix (task #210: the fixpoint route's constructor payload). -/
theorem projList_mkTower_take {fs : List V} {i : Nat} (hi : i ≤ fs.length) :
    projList i (mkTower (fs ++ [pt])) = fs.take i := by
  have h1 : projList (fs.length + 1) (mkTower (fs ++ [pt])) = fs ++ [pt] := projList_mkTower _ _ (by simp)
  have h2 := projList_take (fs.length + 1) i (mkTower (fs ++ [pt])) (by omega)
  rw [h1, List.take_append_of_le_length hi] at h2
  exact h2.symm

/-- A field projection of a point-terminated tower, `getD`-form. -/
theorem projS_mkTower_getD {fs : List V} {i : Nat} (hi : i < fs.length) :
    projS i (mkTower (fs ++ [pt])) = fs.getD i pt := by
  rw [projS_mkTower i (fs ++ [pt]) (by simp; omega), List.getElem_append_left hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- **Eta + elim** (graph regime): every carrier member IS the tower
of its own projections, and those projections fit the telescope. -/
theorem towerSet_elim {w : Nat} (hw : w ≠ 0) :
    ∀ {n} (T : TeleS V n) {hT : HasTeleS w T} {x : V},
    x ∈ˢ towerSet w T hT →
    FitsS T (projList n x) ∧ x = mkTower (projList n x)
  | _, .nil, _, x, hx => ⟨trivial, by
    rw [towerSet_nil] at hx
    have := mem_unitSetAt_iff.mp hx
    rwa [unitAt_pos hw] at this⟩
  | _, .cons A B, hT, x, hx => by
    obtain ⟨F, hS, hF, heq⟩ := towerSet_cons_elim hT
    rw [heq] at hx
    obtain ⟨a, b, ha, hb, -, hpos⟩ := mem_sigma_elim hx
    have hx' : x = spair a b := hpos hw
    subst hx'
    have hBa : HasTeleS w (B a) := ⟨F a, hF a ha⟩
    have hFa : F a = towerSet w (B a) hBa :=
      HasTower.unique (hF a ha) (Classical.choose_spec hBa)
    obtain ⟨hfit, heta⟩ := towerSet_elim hw (B a) (hT := hBa) (hFa ▸ hb)
    constructor
    · show sfst (spair a b) ∈ˢ A ∧ FitsS (B (sfst (spair a b)))
        (projList _ (ssnd (spair a b)))
      rw [sfst_spair, ssnd_spair]
      exact ⟨ha, hfit⟩
    · show spair a b
        = spair (sfst (spair a b)) (mkTower (projList _ (ssnd (spair a b))))
      rw [sfst_spair, ssnd_spair, ← heta]

/-- **Elim** (squash regime): a `w = 0` carrier member is `pt`, and
some tuple fits. -/
theorem towerSet_zero_elim : ∀ {n} (T : TeleS V n) {hT : HasTeleS 0 T} {x : V},
    x ∈ˢ towerSet 0 T hT → x = pt ∧ ∃ as, FitsS T as
  | _, .nil, _, x, hx => ⟨by
    rw [towerSet_nil] at hx
    have := mem_unitSetAt_iff.mp hx
    rwa [unitAt_zero] at this, [], trivial⟩
  | _, .cons _ B, hT, x, hx => by
    obtain ⟨F, hS, hF, heq⟩ := towerSet_cons_elim hT
    rw [heq] at hx
    obtain ⟨a, b, ha, hb, hz, -⟩ := mem_sigma_elim hx
    have hBa : HasTeleS 0 (B a) := ⟨F a, hF a ha⟩
    have hFa : F a = towerSet 0 (B a) hBa :=
      HasTower.unique (hF a ha) (Classical.choose_spec hBa)
    obtain ⟨-, as, hfit⟩ := towerSet_zero_elim (B a) (hT := hBa) (hFa ▸ hb)
    exact ⟨hz rfl, a :: as, ha, hfit⟩

/-- **Membership** (graph regime): the `i`-th projection lands in the
`i`-th field set at the earlier projections. -/
theorem projS_mem {w : Nat} (hw : w ≠ 0) {n} {T : TeleS V n} {hT : HasTeleS w T}
    {x : V} (hx : x ∈ˢ towerSet w T hT) (i : Nat) (h : i < n) :
    projS i x ∈ˢ teleNth T i (projList i x) := by
  obtain ⟨hfit, -⟩ := towerSet_elim hw T hx
  have hm := fitsS_mem_teleNth hfit i h
  rw [projList_take n i x (Nat.le_of_lt h)] at hm
  rw [← projList_get n i x h]
  exact hm

/-- **Membership** (squash regime): the SAME statement, with the
proof-field premise `PropS` in place of `w ≠ 0` — every member is
`pt`, `projS` fixes it, and every truth-value field set at the
all-`pt` prefix contains it (proof irrelevance, semantically). -/
theorem projS_mem_zero {n} {T : TeleS V n} {hT : HasTeleS 0 T} {x : V}
    (hP : PropS T) (hx : x ∈ˢ towerSet 0 T hT) (i : Nat) (h : i < n) :
    projS i x ∈ˢ teleNth T i (projList i x) := by
  obtain ⟨rfl, as, hfit⟩ := towerSet_zero_elim T hx
  have hrep := fitsS_replicate_of_prop hP hfit
  have hm := fitsS_mem_teleNth hrep i h
  rw [List.take_replicate, Nat.min_eq_left (Nat.le_of_lt h),
    List.getElem_replicate] at hm
  rw [projS_pt, projList_pt]
  exact hm

/-- **Coherence by uniform tupling**: `ProjCoh` holds by
representation — equal towers of equal arity have equal components.
Proved through the iota law alone (`kpair_inj` iterated). -/
theorem mkTower_inj {as bs : List V} (hlen : as.length = bs.length)
    (h : mkTower as = mkTower bs) : as = bs := by
  apply List.ext_getElem hlen
  intro i h1 h2
  rw [← projS_mkTower i as h1, ← projS_mkTower i bs h2, h]

/-- **Formation**: the carrier lives at the structure's own level,
given the per-field bound (cumulativity is applied by the consumer
when a field's sort is `< w`). -/
theorem towerSet_mem_univ {w : Nat} : ∀ {n} (T : TeleS V n) {hT : HasTeleS w T},
    BoundS w T → towerSet w T hT ∈ˢ (univ w : V)
  | _, .nil, _, _ => by
    rw [towerSet_nil]; exact unitSetAt_mem_univ w
  | _, .cons _ B, hT, hb => by
    obtain ⟨F, hS, hF, heq⟩ := towerSet_cons_elim hT
    rw [heq]
    have h := sigma_mem_univ (u := w) (v := w) (B := F) hb.1 (fun a ha => by
      have hBa : HasTeleS w (B a) := ⟨F a, hF a ha⟩
      have hFa : F a = towerSet w (B a) hBa :=
        HasTower.unique (hF a ha) (Classical.choose_spec hBa)
      rw [hFa]
      exact towerSet_mem_univ (B a) (hT := hBa) (hb.2 a ha)) hS
    rwa [show Nat.max w w = w from Nat.max_self w] at h

/-- **Formation, squash regime — UNCONDITIONAL**: at `w = 0` the
carrier is a truth value with no field bounds at all (`sigmaSet 0`
truncates whatever its arguments are), so definitely-`Prop`
structures with arbitrary-sorted data fields (`Exists`) still get a
lawful carrier; only their *projections* wait on `PropS`. -/
theorem towerSet_zero_mem_univZero : ∀ {n} (T : TeleS V n) {hT : HasTeleS 0 T},
    towerSet 0 T hT ∈ˢ (univZero : V)
  | _, .nil, _ => by
    rw [towerSet_nil]
    exact univ_zero (V := V) ▸ unitSetAt_mem_univ 0
  | _, .cons _ _, hT => by
    obtain ⟨_, hS, _, heq⟩ := towerSet_cons_elim hT
    rw [heq, sigmaSet_zero]
    exact truthVal_mem_univZero _

theorem Fib_towerSet (w : Nat) : ∀ {n} (T : TeleS V n) (hT : HasTeleS w T),
    Fib (decide (w = 0)) (towerSet w T hT)
  | _, .nil, _ => by
    rw [towerSet_nil]; exact Fib_unitSetAt w
  | _, .cons _ _, hT => by
    obtain ⟨_, _, _, heq⟩ := towerSet_cons_elim hT
    rw [heq]; exact Fib_sigmaSet w _ _

theorem IsTy_towerSet (w : Nat) {n} (T : TeleS V n) (hT : HasTeleS w T) :
    IsTy (towerSet w T hT) :=
  IsTy_of_Fib (Fib_towerSet w T hT)

theorem towerSet_ne_pt (w : Nat) {n} (T : TeleS V n) (hT : HasTeleS w T) :
    towerSet w T hT ≠ (pt : V) :=
  (IsTy_towerSet w T hT).ne_pt

/-! ## First-order definability (`DefTeleS` and `DefFun` closures) -/

/-- First-order definability of a `k`-parameterized telescope family
`T : (Fin k → V) → TeleS V n`: each head domain is `DefFun k` and each
tail is `DefTeleS (k + 1)` under `fcons`. -/
def DefTeleS : {k n : Nat} → ((Fin k → V) → TeleS V n) → Prop
  | _, 0, _ => True
  | k, _ + 1, T =>
    ∃ (A : (Fin k → V) → V) (B : (Fin (k + 1) → V) → TeleS V _),
      (∀ env, T env = .cons (A env) (fun x => B (fcons x env))) ∧
      DefFun k A ∧
      DefTeleS B

theorem DefTeleS.nil {k : Nat} : DefTeleS (V := V) (k := k) fun _ => .nil :=
  trivial

theorem DefTeleS.cons {k n : Nat} {A : (Fin k → V) → V}
    {B : (Fin (k + 1) → V) → TeleS V n}
    (hA : DefFun k A) (hB : DefTeleS B) :
    DefTeleS fun env => .cons (A env) (fun x => B (fcons x env)) :=
  ⟨A, B, fun _ => rfl, hA, hB⟩

theorem DefTeleS.cons_curry {k n : Nat} {A : (Fin k → V) → V}
    {B : V → (Fin k → V) → TeleS V n}
    (hA : DefFun k A) (hB : DefTeleS fun v => B (v 0) (ftail v)) :
    DefTeleS fun env => .cons (A env) (fun x => B x env) :=
  DefTeleS.cons (B := fun v => B (v 0) (ftail v)) hA hB

theorem DefTeleS.congr : ∀ {k n : Nat} {T T' : (Fin k → V) → TeleS V n},
    DefTeleS T → (∀ env, T env = T' env) → DefTeleS T'
  | _, 0, _, _, _, _ => trivial
  | _, _ + 1, _, _, ⟨A, B, hEq, hA, hB⟩, h =>
    ⟨A, B, fun env => (h env).symm.trans (hEq env), hA, hB⟩

theorem DefTeleS.reIndex : ∀ {n m r : Nat} {T : (Fin m → V) → TeleS V n},
    DefTeleS T → (f : Fin m → Fin r) →
    DefTeleS fun env => T (fun i => env (f i))
  | 0, _, _, _, _, _ => trivial
  | _ + 1, _, _, _, ⟨A, B, hEq, hA, hB⟩, f => by
    refine ⟨fun env => A (fun i => env (f i)),
      fun v => B (fcons (v 0) (fun i => ftail v (f i))),
      fun env => hEq (fun i => env (f i)),
      hA.reIndex f, ?_⟩
    have hB' := DefTeleS.reIndex hB (Formula.liftFin f)
    refine DefTeleS.congr hB' fun v => ?_
    congr 1
    funext ⟨j, hj⟩
    cases j with
    | zero => rfl
    | succ j => rfl

theorem DefTeleS.weaken {k n : Nat} {T : (Fin k → V) → TeleS V n} (hT : DefTeleS T) :
    DefTeleS fun env => T (ftail env) :=
  hT.reIndex Fin.succ

private theorem defTeleS_has_and_defFun :
    ∀ {n k : Nat} (w : Nat) {T : (Fin k → V) → TeleS V n}, DefTeleS T →
      ∃ h : ∀ env, HasTeleS w (T env),
        DefFun k fun env => towerSet w (T env) (h env)
  | 0, k, w, T, _ => by
    have h : ∀ env, HasTeleS w (T env) := fun env => by
      cases T env
      exact hasTeleS_nil w
    refine ⟨h, (DefFun.unitSetAt_const (k := k) w).congr fun env => ?_⟩
    exact (towerSet_eq_of_nil (h env)).symm
  | n + 1, k, w, T, ⟨A, B, hEq, hA, hB⟩ => by
    obtain ⟨hHasB, hDefB⟩ := defTeleS_has_and_defFun (n := n) (k := k + 1) w hB
    have hDefB_fix : ∀ env : Fin k → V,
        DefFun 1 fun v => towerSet w (B (fcons (v 0) env)) (hHasB (fcons (v 0) env)) := by
      intro env
      let Gs : Fin (k + 1) → (Fin 1 → V) → V
        | ⟨0, _⟩ => fun v => v 0
        | ⟨j + 1, hj⟩ => fun _ => env ⟨j, Nat.lt_of_succ_lt_succ hj⟩
      have hGs : ∀ i : Fin (k + 1), DefFun 1 (Gs i) := by
        rintro ⟨j, hj⟩
        cases j with
        | zero => exact DefFun.proj 0
        | succ j => exact DefFun.const _
      have heqv : ∀ v : Fin 1 → V, (fun i : Fin (k + 1) => Gs i v) = fcons (v 0) env := by
        intro v
        funext ⟨j, hj⟩
        cases j with
        | zero => rfl
        | succ j => rfl
      exact (hDefB.comp hGs).congr fun v => by rw [heqv v]
    have hS : ∀ env, HasSigmaPairs (A env)
        (fun x => towerSet w (B (fcons x env)) (hHasB (fcons x env))) := fun env =>
      hasSigmaPairs_of_defFun1 (hDefB_fix env)
    have hT : ∀ env, HasTeleS w (T env) := fun env =>
      (hEq env).symm ▸ hasTeleS_cons_of (fun x _ => hHasB (fcons x env))
        (fun _ _ => rfl) (hS env)
    refine ⟨hT, (DefFun.sigmaSet_apply w (h := hS) hA hDefB).congr fun env => ?_⟩
    exact (towerSet_cons_eq (h := hEq env ▸ hT env)
      (fun x _ => hHasB (fcons x env)) (fun _ _ => rfl) (hS env) |>.symm).trans (by
        congr 1; exact (hEq env).symm)

theorem DefTeleS.hasTeleS {k n : Nat} (w : Nat) {T : (Fin k → V) → TeleS V n}
    (hT : DefTeleS T) (env : Fin k → V) : HasTeleS w (T env) :=
  (defTeleS_has_and_defFun w hT).choose env

theorem _root_.ConLeche.SetTheory.DefFun.towerSet_apply {k n : Nat} (w : Nat)
    {T : (Fin k → V) → TeleS V n} {h : ∀ env, HasTeleS w (T env)}
    (hT : DefTeleS T) :
    DefFun k fun env => towerSet w (T env) (h env) := by
  obtain ⟨h', hdef⟩ := defTeleS_has_and_defFun w hT
  exact hdef.congr fun env => towerSet_irrel (T env) (h' env) (h env)

theorem _root_.ConLeche.SetTheory.DefFun.projS_apply {k : Nat} (i : Nat)
    {X : (Fin k → V) → V} (hX : DefFun k X) :
    DefFun k fun env => projS i (X env) := by
  induction i generalizing k X with
  | zero => exact DefFun.sfst_apply hX
  | succ i ih => exact ih (DefFun.ssnd_apply hX)

theorem _root_.ConLeche.SetTheory.DefFun.dropS_apply {k : Nat} (m : Nat)
    {X : (Fin k → V) → V} (hX : DefFun k X) :
    DefFun k fun env => dropS m (X env) := by
  induction m generalizing k X with
  | zero => exact hX
  | succ m ih => exact ih (DefFun.ssnd_apply hX)

theorem _root_.ConLeche.SetTheory.DefFun.mkTower_apply {k : Nat} :
    ∀ (as : List ((Fin k → V) → V)), (∀ f ∈ as, DefFun k f) →
      DefFun k fun env => mkTower (as.map fun f => f env)
  | [], _ => DefFun.empty
  | a :: as, h =>
    DefFun.spair_apply (h a (List.Mem.head _))
      (DefFun.mkTower_apply as fun f hf => h f (List.Mem.tail _ hf))

theorem _root_.ConLeche.SetTheory.DefFun.mkTower_range_apply {k : Nat} (n : Nat)
    {F : Nat → (Fin k → V) → V} (hF : ∀ i, i < n → DefFun k (F i)) :
    DefFun k fun env => mkTower ((List.range n).map fun i => F i env) := by
  have h := DefFun.mkTower_apply ((List.range n).map F) (fun f hf => by
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hf
    exact hF i (List.mem_range.mp hi))
  exact h.congr fun env => by rw [List.map_map]; rfl

/-! ## Degeneracy checks (build-time regressions) -/

/-- `n = 1`: the terminator makes `projS 0 = sfst` lawful — the sole
field of a one-field tower reads back. -/
example (a : V) : projS 0 (mkTower [a]) = a :=
  projS_mkTower 0 [a] (by simp)

/-- `n = 2`: both indices read back through the one uniform family. -/
example (a b : V) : projS 0 (mkTower [a, b]) = a ∧ projS 1 (mkTower [a, b]) = b :=
  ⟨projS_mkTower 0 [a, b] (by simp), projS_mkTower 1 [a, b] (by simp)⟩

/-- `n = 0`: the empty tower's sole member is `mkTower []` (graph
regime). -/
example {w : Nat} (hw : w ≠ 0) {x : V}
    (hx : x ∈ˢ towerSet w (.nil : TeleS V 0) (hasTeleS_nil w)) :
    x = mkTower [] :=
  (towerSet_elim hw .nil hx).2

end ConLeche.SetTheory.Tower
