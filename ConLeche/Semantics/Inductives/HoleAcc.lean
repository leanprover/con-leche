module

public import ConLeche.Semantics.Inductives.HoleMono

@[expose] public section

/-!
# Accessibility in the holes, case by case (strictly first-order)

The twin of `HoleMono.lean` for the closure witness (W), formulated over
purely first-order ZFC + Grothendieck set theory:

* **Set-valued occurrence space (`AppPaths`, `GraphOccs`, `occSpaceQ`).**
  An occurrence `(i, vs, y)` is encoded as
  `occEncItem i vs y := kpair (vnat i) (kpair (vnat vs.length) (encSpineY vs y))`.
  Because `app pt v = pt` holds over the proper class of all `v : V`, a
  `foldl app` prefix hitting `pt` cannot form a set of spines in `V`.
  Whenever `f ≠ pt`, `app_eq_empty_of_not_mem` guarantees that any `v` with
  `app f v ≠ ∅` lies in the domain set `domSet f := sUnion (sUnion f)`.
  Iterating `sigmaPairs` over `domSet f := if f = pt then ∅ else sUnion (sUnion f)`
  for `n` steps builds the genuine set `AppPaths f n` (`GraphOccs ρ i n`,
  `occSpaceQ ρ qs`), and `pt`-hitting prefixes are dropped with empty support
  in `AccOn.holeApp` via `FrameRel.PtHitStable`.
* **First-order Skolemization (`AccOn.pi`).**  Replaced meta-level `Classical.choose`
  over `V → Occ V` with `piSet_choose` over finite-support `DefRel` relations
  (`FrameRel.Def d`), finite `(i, n)` listings (`FinQ Q`), and definable bounds
  (`DefBound d A`), returning a genuine set-level support graph `g : V`.
-/

namespace ConLeche.Semantics
open ConLeche.Term (Term)
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## Application paths and set-valued occurrence spaces (B1) -/

/-- The effective domain set of `f`: empty if `f = pt`, otherwise
`sUnion (sUnion f)`, which contains every `v` with `app f v ≠ ∅`. -/
noncomputable def domSet (f : V) : V :=
  open Classical in if f = pt then empty else sUnion (sUnion f)

theorem DefFun.domSet_apply {k : Nat} {F : (Fin k → V) → V} (hF : DefFun k F) :
    DefFun k fun env => domSet (F env) := by
  unfold domSet
  exact DefFun.ite (DefRel.eq_apply hF DefFun.pt) DefFun.empty
    (DefFun.sUnion_apply (DefFun.sUnion_apply hF))

theorem ne_pt_of_mem_domSet {f v : V} (hv : v ∈ˢ domSet f) : f ≠ pt := by
  intro hpt
  unfold domSet at hv
  rw [ite_eq_left hpt] at hv
  exact not_mem_empty v hv

theorem mem_domSet_of_app_ne_empty {f v : V} (hf : f ≠ pt) (ha : app f v ≠ empty) :
    v ∈ˢ domSet f := by
  unfold domSet
  rw [ite_eq_right hf]
  have hex : ∃ y, kpair v y ∈ˢ f := by
    refine Classical.byContradiction fun hne => ha ?_
    exact app_eq_empty_of_not_mem hf fun y hy => hne ⟨y, hy⟩
  obtain ⟨y, hy⟩ := hex
  exact mem_sUnion.mpr ⟨sing v, mem_sUnion.mpr ⟨kpair v y, hy, mem_upair_left _ _⟩,
    mem_sing.mpr rfl⟩

/-- Non-`pt` prefix condition along a `foldl app` spine. -/
def NoPtPrefix (f : V) : List V → Prop
  | [] => True
  | v :: vs => f ≠ pt ∧ NoPtPrefix (app f v) vs

theorem foldlApp_pt_aux : ∀ (vs : List V), vs.foldl app (pt : V) = pt
  | [] => rfl
  | _ :: vs => by
    show vs.foldl app (app pt _) = pt
    rw [app_pt]
    exact foldlApp_pt_aux vs

theorem foldlApp_empty_aux : ∀ (vs : List V), vs.foldl app (empty : V) = empty
  | [] => rfl
  | _ :: vs => by
    show vs.foldl app (app empty _) = empty
    rw [app_empty]
    exact foldlApp_empty_aux vs

theorem foldlApp_eq_pt_of_not_noPtPrefix : ∀ {f : V} {vs : List V},
    ¬ NoPtPrefix f vs → vs.foldl app f = pt
  | _, [], h => absurd trivial h
  | f, v :: vs, h => by
    unfold NoPtPrefix at h
    by_cases hf : f = pt
    · subst hf
      show vs.foldl app (app pt v) = pt
      rw [app_pt]
      exact foldlApp_pt_aux vs
    · show vs.foldl app (app f v) = pt
      exact foldlApp_eq_pt_of_not_noPtPrefix fun hrest => h ⟨hf, hrest⟩

/-- Right-nested encoding of `(vs, y)` in `V`. -/
noncomputable def encSpineY : List V → V → V
  | [], y => kpair empty y
  | v :: vs, y => kpair v (encSpineY vs y)

theorem encSpineY_inj : ∀ {vs₁ vs₂ : List V} {y₁ y₂ : V},
    vs₁.length = vs₂.length → encSpineY vs₁ y₁ = encSpineY vs₂ y₂ → vs₁ = vs₂ ∧ y₁ = y₂
  | [], [], _, _, _, h => ⟨rfl, (kpair_inj h).2⟩
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | v₁ :: vs₁, v₂ :: vs₂, y₁, y₂, hlen, h => by
    obtain ⟨hv, hrest⟩ := kpair_inj h
    obtain ⟨hvs, hy⟩ := encSpineY_inj (by simpa using hlen) hrest
    exact ⟨by subst hv; subst hvs; rfl, hy⟩

/-- First-order Kuratowski encoding of a support item `(i, vs, y)` in `V`. -/
noncomputable def occEncItem (i : Nat) (vs : List V) (y : V) : V :=
  kpair (vnat i) (kpair (vnat vs.length) (encSpineY vs y))

theorem occEncItem_inj {i₁ i₂ : Nat} {vs₁ vs₂ : List V} {y₁ y₂ : V}
    (h : occEncItem i₁ vs₁ y₁ = occEncItem i₂ vs₂ y₂) :
    i₁ = i₂ ∧ vs₁ = vs₂ ∧ y₁ = y₂ := by
  obtain ⟨hi, hrest⟩ := kpair_inj h
  obtain ⟨hlen, hsp⟩ := kpair_inj hrest
  have hi' := vnat_inj hi
  have hlen' := vnat_inj hlen
  obtain ⟨hvs, hy⟩ := encSpineY_inj hlen' hsp
  exact ⟨hi', hvs, hy⟩

/-- Evaluates an `encSpineY`-encoded spine of fixed length `n` starting from `f`. -/
noncomputable def evalSpineY (f s : V) : Nat → V
  | 0 => f
  | n + 1 => evalSpineY (app f (sfst s)) (ssnd s) n

theorem evalSpineY_encSpineY : ∀ (f : V) (vs : List V) (y : V),
    evalSpineY f (encSpineY vs y) vs.length = vs.foldl app f
  | f, [], _ => rfl
  | f, v :: vs, y => by
    show evalSpineY (app f (sfst (kpair v (encSpineY vs y)))) (ssnd (kpair v (encSpineY vs y)))
      vs.length = vs.foldl app (app f v)
    rw [sfst_kpair, ssnd_kpair]
    exact evalSpineY_encSpineY (app f v) vs y

theorem DefFun.evalSpineY_apply {k : Nat} :
    ∀ (n : Nat) {F S : (Fin k → V) → V}, DefFun k F → DefFun k S →
      DefFun k fun env => evalSpineY (F env) (S env) n
  | 0, _, _, hF, _ => hF
  | n + 1, _, _, hF, hS =>
    DefFun.evalSpineY_apply n (DefFun.app_apply hF (DefFun.sfst_apply hS)) (DefFun.ssnd_apply hS)

/-- Extracts the value `y` from `encSpineY vs y` of fixed length `n`. -/
noncomputable def lastVal (s : V) : Nat → V
  | 0 => ssnd s
  | n + 1 => lastVal (ssnd s) n

theorem lastVal_encSpineY : ∀ (vs : List V) (y : V),
    lastVal (encSpineY vs y) vs.length = y
  | [], y => ssnd_kpair empty y
  | v :: vs, y => by
    show lastVal (ssnd (kpair v (encSpineY vs y))) vs.length = y
    rw [ssnd_kpair]
    exact lastVal_encSpineY vs y

theorem DefFun.lastVal_apply {k : Nat} :
    ∀ (n : Nat) {S : (Fin k → V) → V}, DefFun k S →
      DefFun k fun env => lastVal (S env) n
  | 0, _, hS => DefFun.ssnd_apply hS
  | n + 1, _, hS => DefFun.lastVal_apply n (DefFun.ssnd_apply hS)

/-- First-order check that `s` has the `encSpineY` shape for length `n`. -/
def isSpineY (s : V) : Nat → Prop
  | 0 => ∃ y, s = kpair empty y
  | n + 1 => ∃ v s', s = kpair v s' ∧ isSpineY s' n

theorem isSpineY_encSpineY : ∀ (vs : List V) (y : V), isSpineY (encSpineY vs y) vs.length
  | [], y => ⟨y, rfl⟩
  | v :: vs, y => ⟨v, encSpineY vs y, rfl, isSpineY_encSpineY vs y⟩

theorem isSpineY_elim : ∀ {n : Nat} {s : V}, isSpineY s n →
    ∃ vs y, vs.length = n ∧ s = encSpineY vs y
  | 0, _, ⟨y, rfl⟩ => ⟨[], y, rfl, rfl⟩
  | n + 1, _, ⟨v, s', rfl, hs'⟩ => by
    obtain ⟨vs, y, hlen, rfl⟩ := isSpineY_elim hs'
    exact ⟨v :: vs, y, by simpa using hlen, rfl⟩

theorem DefRel.isSpineY_apply {k : Nat} :
    ∀ (n : Nat) {S : (Fin k → V) → V}, DefFun k S →
      DefRel k fun env => isSpineY (S env) n
  | 0, _, hS =>
    DefRel.exists_curry (DefRel.eq_apply hS.weaken (DefFun.kpair_apply DefFun.empty (DefFun.proj 0)))
  | n + 1, _, hS =>
    DefRel.exists_curry (DefRel.exists_curry (DefRel.and
      (DefRel.eq_apply hS.weaken.weaken (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)))
      (DefRel.isSpineY_apply n (DefFun.proj 0))))

/-- Internal `n`-step application paths along non-`pt` intermediate graphs,
paired with its `DefFun 1` witness. -/
noncomputable def appPathsDef : (n : Nat) → { F : V → V // DefFun 1 fun v => F (v 0) }
  | 0 =>
    ⟨fun f => image (kpair empty) f (hasImage_of_defFun1 (DefFun.kpair_apply DefFun.empty (DefFun.proj 0)) f),
     DefFun.image_apply_curry (DefFun.kpair_apply DefFun.empty (DefFun.proj 0)) (DefFun.proj 0)⟩
  | n + 1 =>
    let rec_ := appPathsDef n
    ⟨fun f => sigmaPairs (domSet f) (fun v => rec_.val (app f v))
        (hasSigmaPairs_of_defFun1 (rec_.property.comp1 (DefFun.app_apply (DefFun.const f) (DefFun.proj 0)))),
     DefFun.sigmaPairs_apply_curry (DefFun.domSet_apply (DefFun.proj 0))
       (rec_.property.comp1 (DefFun.app_apply (DefFun.proj 1) (DefFun.proj 0)))⟩

/-- The set of encoded `(vs, y)` with `vs.length = n`, non-`pt` prefixes of `f`,
and `y ∈ˢ vs.foldl app f`. -/
noncomputable def AppPaths (f : V) (n : Nat) : V :=
  (appPathsDef n).val f

theorem defFun_appPaths (n : Nat) : DefFun (V := V) 1 fun v => AppPaths (v 0) n :=
  (appPathsDef n).property

theorem mem_appPaths_iff : ∀ {n : Nat} {f p : V},
    p ∈ˢ AppPaths f n ↔
      ∃ vs y, vs.length = n ∧ p = encSpineY vs y ∧ NoPtPrefix f vs ∧ y ∈ˢ vs.foldl app f
  | 0, f, p => by
    unfold AppPaths appPathsDef
    rw [mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨[], y, rfl, rfl, trivial, hy⟩
    · rintro ⟨vs, y, hlen, rfl, -, hy⟩
      cases vs with
      | nil => exact ⟨y, hy, rfl⟩
      | cons _ _ => simp at hlen
  | n + 1, f, p => by
    unfold AppPaths appPathsDef
    dsimp only
    rw [mem_sigmaPairs]
    constructor
    · rintro ⟨v, hv, q, hq, rfl⟩
      have hne : f ≠ pt := ne_pt_of_mem_domSet hv
      obtain ⟨vs, y, hlen, rfl, hnp, hy⟩ := mem_appPaths_iff.mp hq
      exact ⟨v :: vs, y, by simpa using hlen, rfl, ⟨hne, hnp⟩, hy⟩
    · rintro ⟨vs, y, hlen, rfl, hnp, hy⟩
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
        obtain ⟨hf, hnp'⟩ := hnp
        have hne_app : app f v ≠ empty := by
          intro h0
          change y ∈ˢ vs.foldl app (app f v) at hy
          rw [h0, foldlApp_empty_aux] at hy
          exact not_mem_empty y hy
        have hv : v ∈ˢ domSet f := mem_domSet_of_app_ne_empty hf hne_app
        have hq : encSpineY vs y ∈ˢ AppPaths (app f v) n :=
          mem_appPaths_iff.mpr ⟨vs, y, by simpa using hlen, rfl, hnp', hy⟩
        exact ⟨v, hv, encSpineY vs y, hq, rfl⟩

/-- **Set-valued occurrence space** at frame `ρ`, position `i`, arity `n`:
all `occEncItem i vs y` with `vs.length = n`, `NoPtPrefix (ρ i) vs`, and
`y ∈ˢ vs.foldl app (ρ i)`. -/
noncomputable def GraphOccs (ρ : Nat → V) (i n : Nat) : V :=
  image (fun p => kpair (vnat i) (kpair (vnat n) p)) (AppPaths (ρ i) n)
    (hasImage_of_defFun1 (f := fun p => kpair (vnat i) (kpair (vnat n) p))
      (DefFun.kpair_apply (DefFun.const (vnat i))
        (DefFun.kpair_apply (DefFun.const (vnat n)) (DefFun.proj 0)))
      (AppPaths (ρ i) n))

theorem mem_graphOccs_iff {ρ : Nat → V} {i n : Nat} {o : V} :
    o ∈ˢ GraphOccs ρ i n ↔
      ∃ vs y, vs.length = n ∧ o = occEncItem i vs y ∧ NoPtPrefix (ρ i) vs ∧ y ∈ˢ vs.foldl app (ρ i) := by
  unfold GraphOccs
  rw [mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨vs, y, hlen, rfl, hnp, hy⟩ := mem_appPaths_iff.mp hp
    exact ⟨vs, y, hlen, by unfold occEncItem; rw [hlen], hnp, hy⟩
  · rintro ⟨vs, y, hlen, rfl, hnp, hy⟩
    refine ⟨encSpineY vs y, mem_appPaths_iff.mpr ⟨vs, y, hlen, rfl, hnp, hy⟩, ?_⟩
    unfold occEncItem; rw [hlen]

theorem occEncItem_mem_graphOccs {ρ : Nat → V} {i : Nat} {vs : List V} {y : V}
    (hnp : NoPtPrefix (ρ i) vs) (hy : y ∈ˢ vs.foldl app (ρ i)) :
    occEncItem i vs y ∈ˢ GraphOccs ρ i vs.length :=
  mem_graphOccs_iff.mpr ⟨vs, y, rfl, rfl, hnp, hy⟩

/-- Finite union of `GraphOccs ρ i n` over a finite list of admissible `(i, n)` pairs. -/
noncomputable def occSpaceQ (ρ : Nat → V) : List (Nat × Nat) → V
  | [] => empty
  | p :: qs => binUnion (GraphOccs ρ p.1 p.2) (occSpaceQ ρ qs)

theorem mem_occSpaceQ_iff {ρ : Nat → V} {o : V} :
    ∀ {qs : List (Nat × Nat)}, o ∈ˢ occSpaceQ ρ qs ↔ ∃ p ∈ qs, o ∈ˢ GraphOccs ρ p.1 p.2
  | [] => by
    unfold occSpaceQ
    exact ⟨fun h => absurd h (not_mem_empty o), fun ⟨_, hp, _⟩ => by cases hp⟩
  | p :: qs => by
    unfold occSpaceQ
    rw [mem_binUnion, mem_occSpaceQ_iff]
    constructor
    · rintro (h | ⟨q, hq, ho⟩)
      · exact ⟨p, by simp, h⟩
      · exact ⟨q, by simp [hq], ho⟩
    · rintro ⟨q, hq, ho⟩
      simp only [List.mem_cons] at hq
      rcases hq with rfl | hq
      · exact Or.inl ho
      · exact Or.inr ⟨q, hq, ho⟩

theorem occSpaceQ_congr {ρ₁ ρ₂ : Nat → V} :
    ∀ {qs : List (Nat × Nat)}, (∀ p ∈ qs, ρ₁ p.1 = ρ₂ p.1) → occSpaceQ ρ₁ qs = occSpaceQ ρ₂ qs
  | [], _ => rfl
  | p :: qs, h => by
    unfold occSpaceQ
    have hp := h p (by simp)
    have hrest := occSpaceQ_congr (qs := qs) fun q hq => h q (by simp [hq])
    rw [hrest]
    congr 1
    simp only [GraphOccs]
    exact image_ext (congrArg (fun x => AppPaths x p.2) hp) _ _ fun _ _ => rfl

/-- Shifts an encoded item `occEncItem (i + 1) vs y` down by 1 to `occEncItem i vs y`. -/
noncomputable def downOcc (o : V) : V :=
  open Classical in
  if h : ExistsUnique fun r => ∃ k rest, k ∈ˢ (omega : V) ∧ o = kpair (vsucc k) rest ∧ r = kpair k rest
  then Classical.choose h else empty

theorem downOcc_occEncItem (i : Nat) (vs : List V) (y : V) :
    downOcc (occEncItem (i + 1) vs y) = occEncItem i vs y := by
  unfold downOcc occEncItem
  rw [show (vnat (i + 1) : V) = vsucc (vnat i) from rfl]
  have hex : ExistsUnique fun r =>
      ∃ k rest, k ∈ˢ (omega : V) ∧ kpair (vsucc (vnat i)) (kpair (vnat vs.length) (encSpineY vs y)) =
        kpair (vsucc k) rest ∧ r = kpair k rest := by
    refine ⟨kpair (vnat i) (kpair (vnat vs.length) (encSpineY vs y)),
      ⟨vnat i, _, vnat_mem_omega i, rfl, rfl⟩, ?_⟩
    rintro r ⟨k, rest, -, heq, rfl⟩
    obtain ⟨hk, hr⟩ := kpair_inj heq
    rw [vsucc_inj hk, hr]
  rw [dite_eq_left hex]
  exact hex.unique (Classical.choose_spec hex).1 ⟨vnat i, _, vnat_mem_omega i, rfl, rfl⟩

theorem DefFun.downOcc_apply {k : Nat} {O : (Fin k → V) → V} (hO : DefFun k O) :
    DefFun k fun env => downOcc (O env) := by
  unfold downOcc
  exact DefFun.uniqueChoice_curry
    (DefRel.exists_curry (DefRel.exists_curry
      (DefRel.and (DefRel.mem_apply (DefFun.proj 1) DefFun.omega_const)
        (DefRel.and
          (DefRel.eq_apply hO.weaken.weaken.weaken
            (DefFun.kpair_apply (DefFun.vsucc_apply (DefFun.proj 1)) (DefFun.proj 0)))
          (DefRel.eq_apply (DefFun.proj 2) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0)))))))

/-! ## Support items and the predicate -/

/-- A meta-level support item (kept for downstream decoding helpers). -/
abbrev Occ (V : Type uv) := Nat × List V × V

/-- **The frame holds the item** (`Occ V` view). -/
def Holds (ρ : Nat → V) (o : Occ V) : Prop := o.2.2 ∈ˢ o.2.1.foldl app (ρ o.1)

/-- The admissible items (`Occ V` view). -/
def Adm (Q : Nat → Nat → Prop) (o : Occ V) : Prop := Q o.1 o.2.1.length

/-- First-order held item predicate on encoded `o : V`. -/
def HoldsItem (ρ : Nat → V) (o : V) : Prop :=
  ∃ i vs y, o = occEncItem i vs y ∧ y ∈ˢ vs.foldl app (ρ i)

/-- First-order non-`pt` held item predicate on encoded `o : V`. -/
def HoldsNonPt (ρ : Nat → V) (o : V) : Prop :=
  ∃ i vs y, o = occEncItem i vs y ∧ NoPtPrefix (ρ i) vs ∧ y ∈ˢ vs.foldl app (ρ i)

/-- First-order admissible item predicate on encoded `o : V`. -/
def AdmItem (Q : Nat → Nat → Prop) (o : V) : Prop :=
  ∃ i vs y, o = occEncItem i vs y ∧ Q i vs.length

theorem HoldsNonPt.toHoldsItem {ρ : Nat → V} {o : V} (h : HoldsNonPt ρ o) : HoldsItem ρ o :=
  let ⟨i, vs, y, heq, _, hy⟩ := h; ⟨i, vs, y, heq, hy⟩

theorem admItem_congrQ {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q i n ↔ Q' i n) {o : V} :
    AdmItem Q o ↔ AdmItem Q' o :=
  ⟨fun ⟨i, vs, y, heq, hq⟩ => ⟨i, vs, y, heq, (hQ i vs.length).mp hq⟩,
   fun ⟨i, vs, y, heq, hq⟩ => ⟨i, vs, y, heq, (hQ i vs.length).mpr hq⟩⟩

theorem occEncItem_mem_occSpaceQ {ρ : Nat → V} {Q : Nat → Nat → Prop} {qs : List (Nat × Nat)}
    (hqs : ∀ i n, Q i n ↔ (i, n) ∈ qs) {o : V}
    (hA : AdmItem Q o) (hH : HoldsNonPt ρ o) : o ∈ˢ occSpaceQ ρ qs := by
  obtain ⟨i, vs, y, rfl, hq⟩ := hA
  obtain ⟨i', vs', y', heq, hnp, hy⟩ := hH
  obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj heq
  exact mem_occSpaceQ_iff.mpr ⟨(i, vs.length), (hqs i vs.length).mp hq, occEncItem_mem_graphOccs hnp hy⟩

/-- Finite listing witness for admissible `(position, arity)` pairs. -/
def FinQ (Q : Nat → Nat → Prop) : Prop :=
  ∃ qs : List (Nat × Nat), ∀ i n, Q i n ↔ (i, n) ∈ qs

/-- The admissible items one binder down: never the bound variable. -/
def shiftQ (Q : Nat → Nat → Prop) : Nat → Nat → Prop
  | 0, _ => False
  | i + 1, n => Q i n

theorem FinQ.congr {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q i n ↔ Q' i n)
    (h : FinQ Q) : FinQ Q' := by
  obtain ⟨qs, hqs⟩ := h
  exact ⟨qs, fun i n => (hQ i n).symm.trans (hqs i n)⟩

theorem FinQ.shiftQ {Q : Nat → Nat → Prop} (h : FinQ Q) : FinQ (Semantics.shiftQ Q) := by
  obtain ⟨qs, hqs⟩ := h
  refine ⟨qs.map fun p => (p.1 + 1, p.2), fun i n => ?_⟩
  cases i with
  | zero =>
    simp only [Semantics.shiftQ, List.mem_map, false_iff, not_exists, not_and]
    intro _ _ heq
    have := congrArg Prod.fst heq
    omega
  | succ i =>
    simp only [Semantics.shiftQ, hqs, List.mem_map]
    constructor
    · intro hp; exact ⟨(i, n), hp, rfl⟩
    · rintro ⟨⟨a, b⟩, hab, heq⟩
      obtain ⟨ha, hb⟩ := Prod.mk.inj heq
      have h1 : a = i := by omega
      subst h1; subst hb; exact hab

/-- First-order check that `o` is a valid `(i, n)` item held at `f`. -/
def HoldsAt (f : V) (i n : Nat) (o : V) : Prop :=
  ∃ s, o = kpair (vnat i) (kpair (vnat n) s) ∧ isSpineY s n ∧ lastVal s n ∈ˢ evalSpineY f s n

theorem holdsAt_iff {f : V} {i n : Nat} {o : V} :
    HoldsAt f i n o ↔ ∃ vs y, vs.length = n ∧ o = occEncItem i vs y ∧ y ∈ˢ vs.foldl app f := by
  constructor
  · rintro ⟨s, rfl, hsp, hy⟩
    obtain ⟨vs, y, hlen, rfl⟩ := isSpineY_elim hsp
    rw [← hlen, lastVal_encSpineY, evalSpineY_encSpineY] at hy
    refine ⟨vs, y, hlen, ?_, hy⟩
    unfold occEncItem; rw [hlen]
  · rintro ⟨vs, y, rfl, rfl, hy⟩
    refine ⟨encSpineY vs y, rfl, isSpineY_encSpineY vs y, ?_⟩
    rw [lastVal_encSpineY, evalSpineY_encSpineY]
    exact hy

theorem DefRel.holdsAt_apply {k : Nat} (i n : Nat) {F O : (Fin k → V) → V}
    (hF : DefFun k F) (hO : DefFun k O) :
    DefRel k fun env => HoldsAt (F env) i n (O env) :=
  DefRel.exists_curry (DefRel.and
    (DefRel.eq_apply hO.weaken
      (DefFun.kpair_apply (DefFun.const (vnat i)) (DefFun.kpair_apply (DefFun.const (vnat n)) (DefFun.proj 0))))
    (DefRel.and (DefRel.isSpineY_apply n (DefFun.proj 0))
      (DefRel.mem_apply (DefFun.lastVal_apply n (DefFun.proj 0))
        (DefFun.evalSpineY_apply n hF.weaken (DefFun.proj 0)))))

/-- Finite disjunction of `HoldsAt` over a concrete list `qs : List (Nat × Nat)`. -/
def HoldsQ (ρ : Nat → V) : List (Nat × Nat) → V → Prop
  | [], _ => False
  | p :: qs, o => HoldsAt (ρ p.1) p.1 p.2 o ∨ HoldsQ ρ qs o

theorem holdsQ_iff {ρ : Nat → V} {o : V} :
    ∀ {qs : List (Nat × Nat)}, HoldsQ ρ qs o ↔ AdmItem (fun i n => (i, n) ∈ qs) o ∧ HoldsItem ρ o
  | [] => by
    unfold HoldsQ AdmItem
    exact ⟨False.elim, fun ⟨⟨_, _, _, _, hm⟩, _⟩ => by cases hm⟩
  | p :: qs => by
    unfold HoldsQ
    rw [holdsAt_iff, holdsQ_iff]
    constructor
    · rintro (⟨vs, y, hlen, rfl, hy⟩ | ⟨⟨i, vs, y, rfl, hq⟩, hH⟩)
      · exact ⟨⟨p.1, vs, y, rfl, by simp [hlen]⟩, ⟨p.1, vs, y, rfl, hy⟩⟩
      · exact ⟨⟨i, vs, y, rfl, by simp [hq]⟩, hH⟩
    · rintro ⟨⟨i, vs, y, rfl, hmem⟩, ⟨i', vs', y', heq, hy⟩⟩
      obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj heq
      simp only [List.mem_cons] at hmem
      rcases hmem with hEq | hmem
      · obtain ⟨rfl, hlen'⟩ := Prod.mk.inj hEq
        exact Or.inl ⟨vs, y, hlen', rfl, hy⟩
      · exact Or.inr ⟨⟨i, vs, y, rfl, hmem⟩, ⟨i, vs, y, rfl, hy⟩⟩

theorem holdsAt_cons_prepend {dep n : Nat} (i ar : Nat) (tail : Nat → V)
    (D_fn : (Fin n → V) → V) (hD : DefFun n D_fn)
    (Xs_fn : Fin dep → (Fin n → V) → V) (hXs : ∀ j, DefFun n (Xs_fn j))
    (O_fn : (Fin n → V) → V) (hO : DefFun n O_fn) :
    DefRel n fun env => HoldsAt (cons (D_fn env) (prepend (fun j => Xs_fn j env) tail) i) i ar (O_fn env) := by
  cases i with
  | zero =>
    exact (DefRel.holdsAt_apply 0 ar hD hO).congr fun _ => by simp [cons]
  | succ i =>
    by_cases hi : i < dep
    · exact (DefRel.holdsAt_apply (i + 1) ar (hXs ⟨i, hi⟩) hO).congr fun env => by
        simp [cons, prepend, hi]
    · exact (DefRel.holdsAt_apply (i + 1) ar (DefFun.const (tail (i - dep))) hO).congr fun env => by
        simp [cons, prepend, hi]

theorem defRel_holdsQ_cons_prepend {dep n : Nat} (tail : Nat → V)
    (D_fn : (Fin n → V) → V) (hD : DefFun n D_fn)
    (Xs_fn : Fin dep → (Fin n → V) → V) (hXs : ∀ j, DefFun n (Xs_fn j))
    (O_fn : (Fin n → V) → V) (hO : DefFun n O_fn) :
    ∀ qs : List (Nat × Nat),
      DefRel n fun env => HoldsQ (cons (D_fn env) (prepend (fun j => Xs_fn j env) tail)) qs (O_fn env)
  | [] => DefRel.false
  | p :: qs => by
    unfold HoldsQ
    exact DefRel.or (holdsAt_cons_prepend p.1 p.2 tail D_fn hD Xs_fn hXs O_fn hO)
      (defRel_holdsQ_cons_prepend tail D_fn hD Xs_fn hXs O_fn hO qs)

/-- **Small at the level**: a member of `tg w` at a `Type`-valued level;
at `w = 0` nothing is asked (task #327). -/
def SmallAt (w : Nat) (x : V) : Prop := w ≠ 0 → x ∈ˢ (tg w : V)

theorem SmallAt.zero (x : V) : SmallAt 0 x := fun h => absurd rfl h

/-- **Definable bound** at depth `d`: `xs ↦ A (prepend xs tail)` is `DefFun d`. -/
def DefBound (d : Nat) (A : (Nat → V) → V) : Prop :=
  ∀ tail : Nat → V, DefFun d fun xs => A (prepend xs tail)

theorem DefBound.const (d : Nat) (c : V) : DefBound d (fun _ => c) :=
  fun _ => DefFun.const c

theorem DefBound.defFun1_cons {d : Nat} {A : (Nat → V) → V} (hA : DefBound (d + 1) A)
    (ρ : Nat → V) : DefFun 1 fun v => A (cons (v 0) ρ) := by
  let tail : Nat → V := fun i => ρ (d + i)
  let Gs : Fin (d + 1) → (Fin 1 → V) → V := fun j v =>
    if hj : j.val = 0 then v 0 else ρ (j.val - 1)
  have hGs : ∀ j : Fin (d + 1), DefFun 1 (Gs j) := fun j => by
    dsimp only [Gs]
    by_cases hj : j.val = 0
    · simp only [hj, ↓reduceDIte]; exact DefFun.proj 0
    · simp only [hj, ↓reduceDIte]; exact DefFun.const _
  refine ((hA tail).comp hGs).congr fun v => ?_
  congr 1
  funext k
  cases k with
  | zero => rfl
  | succ k =>
    by_cases hk : k < d
    · simp [prepend, hk, Gs]
    · have hk1 : ¬ (k + 1 < d + 1) := by omega
      simp only [prepend, hk1, ↓reduceDIte, tail, cons]
      congr 1
      omega

/-- **Accessible along `R` with bound `A`, admissible items `Q`, at the
level `w`**: returns a set-level support graph `g ∈ˢ piSet B (fun _ => U) _`. -/
def AccOn (w : Nat) (Q : Nat → Nat → Prop) (R : FrameRel V) (A : (Nat → V) → V)
    (a : Term) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ x, SmallAt w x → x ∈ˢ interp V ρ a →
    ∃ (B g : V), B ⊆ˢ A ρ ∧
      (∃ U : V, g ∈ˢ piSet B (fun _ => U) (hasSigmaPairs_const _ _)) ∧
      (∀ b, b ∈ˢ B → AdmItem Q (app g b) ∧ HoldsNonPt ρ (app g b)) ∧
      ∀ ρ', R ρ ρ' → (∀ b, b ∈ˢ B → HoldsItem ρ' (app g b)) → x ∈ˢ interp V ρ' a

/-- **The bound is a set of the level** at every frame of the relation. -/
def SizeOn (w : Nat) (R : FrameRel V) (A : (Nat → V) → V) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → SmallAt w (A ρ)

/-- **The bound reads only the positions `M`.** -/
def InvOn (M : Nat → Prop) (A : (Nat → V) → V) : Prop :=
  ∀ ρ ρ' : Nat → V, (∀ i, M i → ρ i = ρ' i) → A ρ = A ρ'

/-- **The point is stable**: a reading holding the point at a frame holds
it at every related frame. -/
def PtOn (R : FrameRel V) (a : Term) : Prop :=
  ∀ ρ ρ', R ρ ρ' → (pt : V) ∈ˢ interp V ρ a → (pt : V) ∈ˢ interp V ρ' a

/-- **Point-free holes**: an admissible position, applied at its arity,
never holds the point at a frame of the relation. -/
def PtFreeOn (Q : Nat → Nat → Prop) (R : FrameRel V) : Prop :=
  ∀ ρ ρ₀, R ρ ρ₀ → ∀ (i : Nat) (vs : List V), Q i vs.length → ¬ (pt : V) ∈ˢ vs.foldl app (ρ i)

/-- **The fibres are types** at both frames of every related pair (the
grading of a walked Π's body, at satisfying frames). -/
def FibTyOn (R : FrameRel V) (D B : Term) : Prop :=
  ∀ ρ ρ', R ρ ρ' → (∀ x, x ∈ˢ interp V ρ D → IsTy (interp V (cons x ρ) B)) ∧
    (∀ x, x ∈ˢ interp V ρ' D → IsTy (interp V (cons x ρ') B))

namespace FrameRel

/-- **Under a binder of domain `A`, the value in the domain at both
frames.** -/
def underBoth (R : FrameRel V) (A : Term) : FrameRel V :=
  fun σ σ' => ∃ x ρ ρ', σ = cons x ρ ∧ σ' = cons x ρ' ∧ R ρ ρ' ∧
    x ∈ˢ interp V ρ A ∧ x ∈ˢ interp V ρ' A

/-- A symmetric relation. -/
def Symm (R : FrameRel V) : Prop := ∀ ρ ρ', R ρ ρ' → R ρ' ρ

/-- Related frames agree at all positions `≥ d`. -/
def AgreesAbove (d : Nat) (R : FrameRel V) : Prop :=
  ∀ ρ ρ', R ρ ρ' → ∀ j, d ≤ j → ρ j = ρ' j

/-- **First-order finite-support definability of `R` at depth `d` (B2).** -/
def Def (d : Nat) (R : FrameRel V) : Prop :=
  R.AgreesAbove d ∧
    ∀ tail : Nat → V, DefRel (d + d) fun v => R (prepend (ftake v) tail) (prepend (fdrop v) tail)

/-- **`pt`-stability along holes (`holeFam_foldl_nofit` / `frame_item_nofit`, B1):**
when a `foldl app` spine hits `pt` at `ρ`, `ρ'` holds `pt` (so `B = ∅` suffices). -/
def PtHitStable (Q : Nat → Nat → Prop) (R : FrameRel V) : Prop :=
  ∀ ρ ρ', R ρ ρ' → ∀ i vs, Q i vs.length → ¬ NoPtPrefix (ρ i) vs → (pt : V) ⊆ˢ vs.foldl app (ρ' i)

theorem AgreesOff.underBoth {R : FrameRel V} {P : Nat → Prop} (h : R.AgreesOff P)
    (A : Term) : (R.underBoth A).AgreesOff (shiftP P) := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -, -⟩
  exact agreeOff_cons (h ρ ρ' hR) x

theorem Symm.underBoth {R : FrameRel V} (h : R.Symm) (A : Term) : (R.underBoth A).Symm := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, hx, hx'⟩
  exact ⟨x, ρ', ρ, rfl, rfl, h ρ ρ' hR, hx', hx⟩

theorem AgreesAbove.underBoth {d : Nat} {R : FrameRel V} (h : R.AgreesAbove d) (A : Term) :
    (R.underBoth A).AgreesAbove (d + 1) := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -, -⟩ j hj
  cases j with
  | zero => omega
  | succ j => exact h ρ ρ' hR j (by omega)

theorem Def.underBoth {d : Nat} {R : FrameRel V} (h : R.Def d) (A : Term) :
    (R.underBoth A).Def (d + 1) := by
  refine ⟨h.1.underBoth A, fun tail => ?_⟩
  let reR : Fin (d + d) → Fin ((d + 1) + (d + 1)) := fun i =>
    if hlt : i.val < d then ⟨i.val + 1, by omega⟩ else ⟨(d + 1) + (i.val - d) + 1, by omega⟩
  let reL : Fin d → Fin ((d + 1) + (d + 1)) := fun i => ⟨i.val + 1, by omega⟩
  let reY : Fin d → Fin ((d + 1) + (d + 1)) := fun i => ⟨(d + 1) + i.val + 1, by omega⟩
  have hrelR : DefRel ((d + 1) + (d + 1)) fun v =>
      R (prepend (fun i : Fin d => v ⟨i.val + 1, by omega⟩) tail)
        (prepend (fun i : Fin d => v ⟨(d + 1) + i.val + 1, by omega⟩) tail) :=
    ((h.2 tail).reIndex reR).congr fun v => by
      have ht : ftake (fun i => v (reR i)) = fun i : Fin d => v ⟨i.val + 1, by omega⟩ := by
        funext ⟨i, hi⟩; simp [ftake, reR, hi]
      have hd : fdrop (fun i => v (reR i)) = fun i : Fin d => v ⟨(d + 1) + i.val + 1, by omega⟩ := by
        funext ⟨i, hi⟩
        have hge : ¬ (d + i < d) := by omega
        simp [fdrop, reR, hge]
      rw [ht, hd]
  have hA := interp_defFun_prepend tail d A
  have hL : DefRel ((d + 1) + (d + 1)) fun v =>
      v 0 ∈ˢ interp V (prepend (fun i : Fin d => v ⟨i.val + 1, by omega⟩) tail) A :=
    DefRel.mem_apply (DefFun.proj 0) ((hA.reIndex reL).congr fun _ => rfl)
  have hY : DefRel ((d + 1) + (d + 1)) fun v =>
      v ⟨d + 1, by omega⟩ ∈ˢ interp V (prepend (fun i : Fin d => v ⟨(d + 1) + i.val + 1, by omega⟩) tail) A :=
    DefRel.mem_apply (DefFun.proj ⟨d + 1, by omega⟩) ((hA.reIndex reY).congr fun _ => rfl)
  have h0eq : DefRel (V := V) ((d + 1) + (d + 1)) fun v => v 0 = v ⟨d + 1, by omega⟩ :=
    DefRel.eq_apply (DefFun.proj (k := (d + 1) + (d + 1)) 0)
      (DefFun.proj (k := (d + 1) + (d + 1)) ⟨d + 1, by omega⟩)
  refine (DefRel.and h0eq (DefRel.and hrelR (DefRel.and hL hY))).congr fun v => ?_
  have hpL : prepend (ftake v) tail =
      cons (v 0) (prepend (fun i : Fin d => v ⟨i.val + 1, by omega⟩) tail) := by
    funext k
    cases k with
    | zero => simp [prepend, ftake, cons]
    | succ k =>
      by_cases hk : k < d
      · have hk1 : k + 1 < d + 1 := by omega
        simp [prepend, ftake, cons, hk, hk1]
      · have hk1 : ¬ (k + 1 < d + 1) := by omega
        simp only [prepend, cons, hk, hk1, ↓reduceDIte]
        congr 1; omega
  have hpY : prepend (fdrop v) tail =
      cons (v ⟨d + 1, by omega⟩) (prepend (fun i : Fin d => v ⟨(d + 1) + i.val + 1, by omega⟩) tail) := by
    funext k
    cases k with
    | zero => simp [prepend, fdrop, cons]
    | succ k =>
      by_cases hk : k < d
      · have hk1 : k + 1 < d + 1 := by omega
        simp only [prepend, fdrop, cons, hk, hk1, ↓reduceDIte]
        congr 2
      · have hk1 : ¬ (k + 1 < d + 1) := by omega
        simp only [prepend, cons, hk, hk1, ↓reduceDIte]
        congr 1; omega
  constructor
  · rintro ⟨heq0, hR, hx, hx'⟩
    refine ⟨v 0, _, _, hpL, hpY.trans (by rw [heq0]), hR, hx, heq0 ▸ hx'⟩
  · rintro ⟨x, ρ, ρ', h1, h2, hR, hx, hx'⟩
    have hρ0 : v 0 = x := by
      have := congrFun h1 0
      simpa [prepend, ftake, cons] using this
    have hρ'0 : v ⟨d + 1, by omega⟩ = x := by
      have := congrFun h2 0
      simpa [prepend, fdrop, cons] using this
    have hρ_eq : prepend (fun i : Fin d => v ⟨i.val + 1, by omega⟩) tail = ρ := by
      funext k
      have := congrFun h1 (k + 1)
      rw [hpL] at this
      exact this
    have hρ'_eq : prepend (fun i : Fin d => v ⟨(d + 1) + i.val + 1, by omega⟩) tail = ρ' := by
      funext k
      have := congrFun h2 (k + 1)
      rw [hpY] at this
      exact this
    rw [hρ_eq, hρ'_eq]
    exact ⟨hρ0.trans hρ'0.symm, hR, hρ0 ▸ hx, hρ'0 ▸ hx'⟩

theorem PtHitStable.congrQ {Q Q' : Nat → Nat → Prop} (hQ : ∀ i n, Q i n ↔ Q' i n)
    {R : FrameRel V} (h : R.PtHitStable Q) : R.PtHitStable Q' :=
  fun ρ ρ' hr i vs hq hnp => h ρ ρ' hr i vs ((hQ _ _).mpr hq) hnp

theorem PtHitStable.underBoth {Q : Nat → Nat → Prop} {R : FrameRel V}
    (h : R.PtHitStable Q) (A : Term) : (R.underBoth A).PtHitStable (Semantics.shiftQ Q) := by
  rintro _ _ ⟨x, ρ, ρ', rfl, rfl, hR, -, -⟩ i vs hQ hnp
  cases i with
  | zero => exact hQ.elim
  | succ i => exact h ρ ρ' hR i vs hQ hnp

end FrameRel

/-! ## Generic facts -/

/-- **Point-freeness survives a binder.** -/
theorem PtFreeOn.underBoth {Q : Nat → Nat → Prop} {R : FrameRel V} (h : PtFreeOn Q R)
    (A : Term) : PtFreeOn (shiftQ Q) (R.underBoth A) := by
  rintro _ _ ⟨x, ρ, ρ₀, rfl, rfl, hR, -, -⟩ i vs hQ
  cases i with
  | zero => exact hQ.elim
  | succ i => exact h ρ ρ₀ hR i vs hQ

/-! ## The cases: accessibility -/

theorem SizeOn.const {w : Nat} {R : FrameRel V} {c : V} (hc : c ∈ˢ (tg w : V)) :
    SizeOn w R (fun _ => c) := fun _ _ _ _ => hc

/-- **A hole-free reading** is accessible with the empty bound. -/
theorem ConstOn.accOn {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {a : Term}
    (h : ConstOn R a) : AccOn w Q R (fun _ => empty) a := by
  intro ρ ρ₀ _ x _ hx
  refine ⟨empty, graph (fun _ => empty) empty (hasGraph_empty _), Subset.refl _,
    ⟨empty, graph_mem_piSet fun _ hb => absurd hb (not_mem_empty _)⟩,
    fun b hb => absurd hb (not_mem_empty b), fun ρ' hR' _ => ?_⟩
  rw [← h ρ ρ' hR']
  exact hx

/-- **The `whnf` step.** -/
theorem AccOn.of_eqOn {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {P : (Nat → V) → Prop}
    (hdom : ∀ ρ ρ', R ρ ρ' → P ρ ∧ P ρ') {A : (Nat → V) → V} {a b : Term}
    (heq : ∀ ρ, P ρ → interp V ρ a = interp V ρ b) (hb : AccOn w Q R A b) : AccOn w Q R A a := by
  intro ρ ρ₀ hR x hxw hx
  rw [heq ρ (hdom ρ ρ₀ hR).1] at hx
  obtain ⟨B, g, hB, hg, hitems, hs⟩ := hb ρ ρ₀ hR x hxw hx
  exact ⟨B, g, hB, hg, hitems, fun ρ' hR' h' => by rw [heq ρ' (hdom ρ ρ' hR').2]; exact hs ρ' hR' h'⟩

/-- An item one binder down, seen above it. -/
def Occ.down (o : Occ V) : Occ V := (o.1 - 1, o.2)

theorem holds_cons_down {x : V} {ρ : Nat → V} {o : Occ V} (h0 : o.1 ≠ 0) :
    Holds (cons x ρ) o ↔ Holds ρ o.down := by
  obtain ⟨i, vs, y⟩ := o
  cases i with
  | zero => exact absurd rfl h0
  | succ i => rfl

/-- A small function's domain and values are small. -/
theorem small_of_mem_piSet {w : Nat} (hw : w ≠ 0) {D f : V} {F : V → V}
    {hS : HasSigmaPairs D F} (hf : f ∈ˢ piSet D F hS)
    (hfw : f ∈ˢ (tg w : V)) : D ∈ˢ (tg w : V) ∧ ∀ d, d ∈ˢ D → app f d ∈ˢ (tg w : V) := by
  have hU := tg_isGrothendieck (V := V) hw
  have hpair : ∀ d, d ∈ˢ D → kpair d (app f d) ∈ˢ f := by
    intro d hd
    rw [← eq_graph_app_of_mem_piSet hf]
    exact mem_graph.mpr ⟨d, hd, by rw [eq_graph_app_of_mem_piSet hf]⟩
  have hkp : ∀ d, d ∈ˢ D → kpair d (app f d) ∈ˢ (tg w : V) :=
    fun d hd => hU.transitive hfw (hpair d hd)
  refine ⟨?_, fun d hd => ?_⟩
  · refine hU.mem_of_subset_mem (hU.sUnion_mem (hU.sUnion_mem hfw)) fun d hd => ?_
    exact mem_sUnion.mpr ⟨sing d, mem_sUnion.mpr ⟨kpair d (app f d), hpair d hd,
      mem_upair_left _ _⟩, mem_sing.mpr rfl⟩
  · exact hU.transitive (hU.transitive (hkp d hd) (mem_upair_right _ _)) (mem_upair_right _ _)

/-- **The bound of a Π**: the glued bounds of the body over the domain,
where the domain is small and has `HasSigmaPairs`. -/
noncomputable def piBound (w : Nat) (D : Term) (Bb : (Nat → V) → V) (ρ : Nat → V) : V :=
  open Classical in
  if h : SmallAt w (interp V ρ D) ∧ HasSigmaPairs (interp V ρ D) (fun d => Bb (cons d ρ))
  then sigmaPairs (interp V ρ D) (fun d => Bb (cons d ρ)) h.2 else empty

theorem DefBound.piBound {d w : Nat} (D : Term) {Bb : (Nat → V) → V}
    (hB : DefBound (d + 1) Bb) : DefBound d (piBound w D Bb) := by
  intro tail
  have hD := interp_defFun_prepend tail d D
  have hS : ∀ xs : Fin d → V,
      HasSigmaPairs (interp V (prepend xs tail) D) (fun x => Bb (prepend (fcons x xs) tail)) :=
    fun xs => hasSigmaPairs_of_defFun1 (hB.defFun1_cons (prepend xs tail) |>.congr fun v => by
      rw [prepend_fcons])
  have hSmall : DefRel d fun xs => SmallAt w (interp V (prepend xs tail) D) := by
    by_cases hw : w = 0
    · subst hw
      exact DefRel.true.congr fun _ => ⟨fun _ h => absurd rfl h, fun _ => trivial⟩
    · exact (DefRel.mem_apply hD (DefFun.tg_const w)).congr fun xs =>
        ⟨fun h _ => h, fun h => h hw⟩
  have hSig : DefFun d fun xs =>
      sigmaPairs (interp V (prepend xs tail) D) (fun x => Bb (prepend (fcons x xs) tail)) (hS xs) :=
    DefFun.sigmaPairs_apply hD (hB tail)
  refine (DefFun.ite hSmall hSig DefFun.empty).congr fun xs => ?_
  unfold Semantics.piBound
  have hS' : HasSigmaPairs (interp V (prepend xs tail) D) (fun x => Bb (cons x (prepend xs tail))) :=
    (hS xs).congr fun x _ => by rw [prepend_fcons]
  by_cases hs : SmallAt w (interp V (prepend xs tail) D)
  · rw [ite_eq_left hs, dite_eq_left ⟨hs, hS'⟩]
    exact sigmaPairs_congr (hS xs) hS' fun x _ => by rw [prepend_fcons]
  · rw [ite_eq_right hs, dite_eq_right (fun h => hs h.1)]

/-- The point is small. -/
theorem SmallAt.pt (w : Nat) : SmallAt w (pt : V) := fun hw =>
  (tg_isGrothendieck hw).transitive (unitSet_mem_tg w) pt_mem_unitSet

/-- First-order Skolemization over `S` returning `DefFun 1` selectors `(Bf, gf)`
with `B' ⊆ˢ A d` (`A` definable over `S`) and `g' ∈ˢ piSet B' (fun _ => U) _`. -/
private theorem skolem_occ_fo {S U : V} {A : V → V} (hA : DefFun 1 fun v => A (v 0))
    {Q : V → V → V → Prop} (hQ : DefRel 3 fun v => Q (v 0) (v 1) (v 2))
    (h : ∀ d, d ∈ˢ S →
      ∃ B g, B ⊆ˢ A d ∧ g ∈ˢ piSet B (fun _ => U) (hasSigmaPairs_const _ _) ∧ Q d B g) :
    ∃ (Bf gf : V → V),
      (DefFun 1 fun v => Bf (v 0)) ∧
      (DefFun 1 fun v => gf (v 0)) ∧
      ∀ d, d ∈ˢ S →
        Bf d ⊆ˢ A d ∧
        gf d ∈ˢ piSet (Bf d) (fun _ => U) (hasSigmaPairs_const _ _) ∧
        Q d (Bf d) (gf d) := by
  let P_sp : V → V := fun d =>
    sigmaPairs (power (A d)) (fun B => piSet B (fun _ => U) (hasSigmaPairs_const _ _))
      (hasSigmaPairs_of_defFun1 (DefFun.piSet_apply_curry (DefFun.proj 0) (DefFun.const U)))
  have hP_def : DefFun 1 fun v => P_sp (v 0) :=
    DefFun.sigmaPairs_apply_curry (DefFun.power_apply hA)
      (DefFun.piSet_apply_curry (DefFun.proj 0) (DefFun.const U))
  have hRelSlice : DefRel 2 fun v => ∃ B g, v 0 = kpair B g ∧ Q (v 1) B g := by
    refine DefRel.exists_curry (DefRel.exists_curry (DefRel.and ?_ ?_))
    · exact DefRel.eq_apply (DefFun.proj 2) (DefFun.kpair_apply (DefFun.proj 1) (DefFun.proj 0))
    · exact hQ.reIndex fun i => match i with | ⟨0, _⟩ => 3 | ⟨1, _⟩ => 1 | ⟨2, _⟩ => 0
  have hSepSlice : ∀ d, HasSep (P_sp d) (fun p => ∃ B g, p = kpair B g ∧ Q d B g) := fun d =>
    hasSep_of_defPred <|
      (hRelSlice.reIndex fun i => match i with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 0).fixParam d
  let Slice : V → V := fun d =>
    sep (P_sp d) (fun p => ∃ B g, p = kpair B g ∧ Q d B g) (hSepSlice d)
  have hSlice_def : DefFun 1 fun v => Slice (v 0) :=
    DefFun.sep_apply_curry hP_def hRelSlice
  have hSlice_sig : HasSigmaPairs S Slice := hasSigmaPairs_of_defFun1 hSlice_def
  have hSlice_ne : ∀ d, d ∈ˢ S → ∃ p, p ∈ˢ Slice d := fun d hd => by
    obtain ⟨B, g, hBA, hg, hQd⟩ := h d hd
    exact ⟨kpair B g, mem_sep.mpr ⟨mem_sigmaPairs.mpr ⟨B, mem_power.mpr hBA, g, hg, rfl⟩,
      B, g, rfl, hQd⟩⟩
  obtain ⟨c, hc_mem⟩ := piSet_choose hSlice_sig hSlice_ne
  refine ⟨fun d => sfst (app c d), fun d => ssnd (app c d),
    DefFun.sfst_apply (DefFun.app_apply (DefFun.const c) (DefFun.proj 0)),
    DefFun.ssnd_apply (DefFun.app_apply (DefFun.const c) (DefFun.proj 0)),
    fun d hd => ?_⟩
  have hc_mem' : app c d ∈ˢ Slice d := app_mem_of_mem_piSet hc_mem hd
  obtain ⟨hp_sp, B, g, hkp, hQd⟩ := mem_sep.mp hc_mem'
  obtain ⟨B', hB', g', hg', hkp'⟩ := mem_sigmaPairs.mp hp_sp
  rw [hkp] at hkp'
  obtain ⟨rfl, rfl⟩ := kpair_inj hkp'
  dsimp only
  simp only [hkp, sfst_kpair, ssnd_kpair]
  exact ⟨mem_power.mp hB', hg', hQd⟩

/-- **Π over a hole-free domain** (first-order `piSet_choose` Skolemization):
uses finite `(i, n)` listing `hQfin`, finite-support definability `hRdef` at depth `dep`,
and `DefBound (dep + 1) Bb`. -/
theorem AccOn.pi {w dep : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {D B : Term}
    (hD : ConstOn R D) (hQfin : FinQ Q) (hRdef : R.Def dep)
    {Bb : (Nat → V) → V} (hBdef : DefBound (dep + 1) Bb)
    (hB : AccOn w (shiftQ Q) (R.underBoth D) Bb B)
    (hT : FibTyOn R D B) (hP : w ≠ 0 → PtOn (R.underBoth D) B) :
    AccOn w Q R (piBound w D Bb) (.pi D B) := by
  intro ρ ρ₀ hR f hfw hf
  rw [interp_pi] at hf
  have hTy0 : ∀ x, x ∈ˢ interp V ρ D → IsTy (interp V (cons x ρ) B) := (hT ρ ρ₀ hR).1
  have hTy : ∀ ρ', R ρ ρ' → ∀ x, x ∈ˢ interp V ρ D → IsTy (interp V (cons x ρ') B) :=
    fun ρ' hR' x hx => (hT ρ ρ' hR').2 x (hD ρ ρ' hR' ▸ hx)
  by_cases hDw' : ¬ SmallAt w (interp V ρ D)
  · have hw : w ≠ 0 := fun h0 => hDw' (h0 ▸ SmallAt.zero _)
    have hfp : f = pt := Classical.byContradiction fun hfp =>
      hDw' fun hw' => (small_of_mem_piSet hw' (mem_piSet_of_mem_piV hf hfp) (hfw hw')).1
    subst hfp
    refine ⟨empty, graph (fun _ => empty) empty (hasGraph_empty _),
      fun b hb => absurd hb (not_mem_empty b),
      ⟨empty, graph_mem_piSet fun _ hb => absurd hb (not_mem_empty _)⟩,
      fun b hb => absurd hb (not_mem_empty b), fun ρ' hR' _ => ?_⟩
    rw [interp_pi, ← hD ρ ρ' hR']
    refine (pt_mem_piV_iff (hTy ρ' hR')).mpr fun d hd => ?_
    exact hP hw (cons d ρ) (cons d ρ') ⟨d, ρ, ρ', rfl, rfl, hR', hd, hD ρ ρ' hR' ▸ hd⟩
      ((pt_mem_piV_iff hTy0).mp hf d hd)
  have hDw : SmallAt w (interp V ρ D) := Classical.not_not.mp hDw'
  have happw : ∀ d, d ∈ˢ interp V ρ D → SmallAt w (app f d) := by
    intro d hd hw
    by_cases hfp : f = pt
    · rw [hfp, app_pt]; exact SmallAt.pt w hw
    · exact (small_of_mem_piSet hw (mem_piSet_of_mem_piV hf hfp) (hfw hw)).2 d hd
  obtain ⟨qs, hqs⟩ := hQfin
  let qs' : List (Nat × Nat) := qs.map fun p => (p.1 + 1, p.2)
  have hqs' : ∀ i n, shiftQ Q i n ↔ (i, n) ∈ qs' := by
    intro i n
    cases i with
    | zero =>
      simp only [shiftQ, qs', List.mem_map, false_iff, not_exists, not_and]
      intro _ _ heq
      have := congrArg Prod.fst heq; omega
    | succ i =>
      simp only [shiftQ, hqs, qs', List.mem_map]
      exact ⟨fun hp => ⟨(i, n), hp, rfl⟩, fun ⟨⟨a, b⟩, hab, heq⟩ => by
        obtain ⟨ha, rfl⟩ := Prod.mk.inj heq
        have h1 : a = i := by omega
        subst h1; exact hab⟩
  let tail : Nat → V := fun i => ρ (dep + i)
  let U_occ : V := occSpaceQ (cons empty ρ) qs'
  have hU_occ : ∀ d, occSpaceQ (cons d ρ) qs' = U_occ := fun d => by
    refine occSpaceQ_congr fun p hp => ?_
    simp only [qs', List.mem_map] at hp
    obtain ⟨q, _, rfl⟩ := hp
    rfl
  let Qsk : V → V → V → Prop := fun d B' g' =>
    (∀ b, b ∈ˢ B' → HoldsQ (cons d ρ) qs' (app g' b)) ∧
    ∀ xs : Fin dep → V, R ρ (prepend xs tail) →
      d ∈ˢ interp V (prepend xs tail) D →
      (∀ b, b ∈ˢ B' → HoldsQ (cons d (prepend xs tail)) qs' (app g' b)) →
      app f d ∈ˢ interp V (cons d (prepend xs tail)) B
  have hQsk_def : DefRel 3 fun v => Qsk (v 0) (v 1) (v 2) := by
    dsimp only [Qsk]
    refine DefRel.and ?_ ?_
    · refine DefRel.bForall_curry (DefFun.proj 1) ?_
      exact (defRel_holdsQ_cons_prepend (dep := 0) (n := 4) ρ
        (fun v => v 1) (DefFun.proj 1)
        (fun j => Fin.elim0 j) (fun j => Fin.elim0 j)
        (fun v => app (v 3) (v 0)) (DefFun.app_apply (DefFun.proj 3) (DefFun.proj 0)) qs').congr
        fun v => by
          have hp : prepend (fun j : Fin 0 => j.elim0) ρ = ρ := funext fun _ => rfl
          change HoldsQ (cons (v 1) (prepend (fun j : Fin 0 => j.elim0) ρ)) qs' (app (v 3) (v 0)) ↔
            HoldsQ (cons (ftail v 0) ρ) qs' (app (ftail v 2) (v 0))
          rw [hp]
          exact Iff.rfl
    · have hQ_body : DefRel (dep + 3) fun v =>
          R ρ (prepend (ftake v) tail) →
          fdrop v 0 ∈ˢ interp V (prepend (ftake v) tail) D →
          (∀ b, b ∈ˢ fdrop v 1 → HoldsQ (cons (fdrop v 0) (prepend (ftake v) tail)) qs' (app (fdrop v 2) b)) →
          app f (fdrop v 0) ∈ˢ interp V (cons (fdrop v 0) (prepend (ftake v) tail)) B := by
        refine DefRel.imp ?_ (DefRel.imp ?_ (DefRel.imp ?_ ?_))
        · let Gs : Fin (dep + dep) → (Fin (dep + 3) → V) → V := fun j v =>
            if hj : j.val < dep then ρ j.val else v ⟨j.val - dep, by omega⟩
          have hGs : ∀ j : Fin (dep + dep), DefFun (dep + 3) (Gs j) := fun j => by
            dsimp only [Gs]; split
            · exact DefFun.const _
            · exact DefFun.proj ⟨_, by omega⟩
          refine ((hRdef.2 tail).comp hGs).congr fun v => ?_
          have ht : prepend (ftake fun j => Gs j v) tail = ρ := by
            funext k
            by_cases hk : k < dep
            · simp [prepend, ftake, Gs, hk]
            · simp only [prepend, hk, ↓reduceDIte, tail]
              congr 1; omega
          have hd : fdrop (fun j => Gs j v) = ftake v := by
            funext ⟨j, hj⟩
            have hge : ¬ (dep + j < dep) := by omega
            simp [fdrop, ftake, Gs, hge]
          rw [ht, hd]
        · have hD' : DefFun (dep + 3) fun v => interp V (prepend (ftake v) tail) D :=
            ((interp_defFun_prepend tail dep D).reIndex fun j =>
              ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_add_right dep 3)⟩).congr fun _ => rfl
          exact DefRel.mem_apply (DefFun.fdrop_proj (k := dep) (p := 3) 0) hD'
        · refine DefRel.bForall_curry (DefFun.fdrop_proj (k := dep) (p := 3) 1) ?_
          exact defRel_holdsQ_cons_prepend (dep := dep) (n := dep + 3 + 1) tail
            (fun v => fdrop (ftail v) 0) (DefFun.fdrop_proj (k := dep) (p := 3) 0).weaken
            (fun idx v => ftake (ftail v) idx) (fun idx => (DefFun.ftake_proj (k := dep) (p := 3) idx).weaken)
            (fun v => app (fdrop (ftail v) 2) (v 0))
            (DefFun.app_apply (DefFun.fdrop_proj (k := dep) (p := 3) 2).weaken (DefFun.proj 0)) qs'
        · let reB : Fin (dep + 1) → Fin (dep + 3)
            | ⟨0, _⟩ => ⟨dep, by omega⟩
            | ⟨i + 1, hi⟩ => ⟨i, by omega⟩
          have hB' : DefFun (dep + 3) fun v =>
              interp V (cons (fdrop v 0) (prepend (ftake v) tail)) B :=
            ((interp_defFun_prepend tail (dep + 1) B).reIndex reB).congr fun v => by
              congr 1
              funext k
              cases k with
              | zero => rfl
              | succ k =>
                by_cases hk : k < dep
                · simp [prepend, ftake, reB, hk, show k + 1 < dep + 1 by omega]
                · simp only [prepend, cons, hk, show ¬ (k + 1 < dep + 1) by omega, ↓reduceDIte]
                  congr 1; omega
          exact DefRel.mem_apply
            (DefFun.app_apply (DefFun.const f) (DefFun.fdrop_proj (k := dep) (p := 3) 0)) hB'
      exact (DefRel.forall_fin hQ_body).congr fun v => by
        simp only [ftake_fappend, fdrop_fappend]
  obtain ⟨Bf, gf, hBf_def, hgf_def, hsk⟩ :=
    skolem_occ_fo (S := interp V ρ D) (U := U_occ) (A := fun d => Bb (cons d ρ))
      (hBdef.defFun1_cons ρ) hQsk_def fun d hd => by
        obtain ⟨B', g', hB'sub, ⟨U', hg'⟩, hitems, hs⟩ :=
          hB (cons d ρ) (cons d ρ₀) ⟨d, ρ, ρ₀, rfl, rfl, hR, hd, hD ρ ρ₀ hR ▸ hd⟩ _
            (happw d hd) (app_mem_piV hf hd)
        have hg'_occ : g' ∈ˢ piSet B' (fun _ => U_occ) (hasSigmaPairs_const _ _) := by
          rw [← eq_graph_app_of_mem_piSet hg']
          refine graph_mem_piSet fun b hb => ?_
          rw [← hU_occ d]
          exact occEncItem_mem_occSpaceQ hqs' (hitems b hb).1 (hitems b hb).2
        refine ⟨B', g', hB'sub, hg'_occ, fun b hb => ?_, fun xs hRxs hdxs hheld => ?_⟩
        · exact holdsQ_iff.mpr ⟨admItem_congrQ hqs' |>.mp (hitems b hb).1,
            (hitems b hb).2.toHoldsItem⟩
        · refine hs (cons d (prepend xs tail))
            ⟨d, ρ, prepend xs tail, rfl, rfl, hRxs, hd, hdxs⟩ fun b hb => ?_
          exact (holdsQ_iff.mp (hheld b hb)).2
  have hBf_sig : HasSigmaPairs (interp V ρ D) Bf := hasSigmaPairs_of_defFun1 hBf_def
  let B_tot := sigmaPairs (interp V ρ D) Bf hBf_sig
  have hg_def : DefFun 1 fun v => downOcc (app (gf (sfst (v 0))) (ssnd (v 0))) :=
    DefFun.downOcc_apply
      (DefFun.app_apply (hgf_def.comp1 (DefFun.sfst_apply (DefFun.proj 0)))
        (DefFun.ssnd_apply (DefFun.proj 0)))
  let g_tot := graph (fun p => downOcc (app (gf (sfst p)) (ssnd p))) B_tot (hasGraph_of_defFun1 hg_def)
  refine ⟨B_tot, g_tot, ?_, ⟨image downOcc U_occ (hasImage_of_defFun1 (DefFun.downOcc_apply (DefFun.proj 0)) U_occ),
      graph_mem_piSet fun p hp => ?_⟩, ?_, ?_⟩
  · intro p hp
    obtain ⟨d, hd, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
    unfold piBound
    have hS_pi : HasSigmaPairs (interp V ρ D) (fun x => Bb (cons x ρ)) :=
      hasSigmaPairs_of_defFun1 (hBdef.defFun1_cons ρ)
    rw [dite_eq_left ⟨hDw, hS_pi⟩]
    exact mem_sigmaPairs.mpr ⟨d, hd, b, (hsk d hd).1 b hb, rfl⟩
  · obtain ⟨d, hd, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
    rw [sfst_kpair, ssnd_kpair]
    exact mem_image.mpr ⟨app (gf d) b, app_mem_of_mem_piSet (hsk d hd).2.1 hb, rfl⟩
  · intro p hp
    obtain ⟨d, hd, b, hb, rfl⟩ := mem_sigmaPairs.mp hp
    dsimp only [g_tot]
    rw [app_graph hp, sfst_kpair, ssnd_kpair]
    have hocc : app (gf d) b ∈ˢ U_occ := app_mem_of_mem_piSet (hsk d hd).2.1 hb
    rw [← hU_occ d, mem_occSpaceQ_iff] at hocc
    obtain ⟨⟨i, n⟩, hin, hgo⟩ := hocc
    simp only [qs', List.mem_map] at hin
    obtain ⟨⟨i₀, n₀⟩, hi₀, heq⟩ := hin
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    obtain ⟨vs, y, hlen, heq_o, hnp, hy⟩ := mem_graphOccs_iff.mp hgo
    rw [heq_o, downOcc_occEncItem]
    exact ⟨⟨i₀, vs, y, rfl, (hqs i₀ vs.length).mpr (hlen ▸ hi₀)⟩,
      ⟨i₀, vs, y, rfl, hnp, hy⟩⟩
  · intro ρ' hR' h'
    rw [interp_pi, ← hD ρ ρ' hR']
    refine mem_piV_of_app hf hTy0 (hTy ρ' hR') fun d hd => ?_
    let xs : Fin dep → V := fun j => ρ' j.val
    have hρ'_eq : prepend xs tail = ρ' := by
      funext k
      by_cases hk : k < dep
      · simp [prepend, xs, hk]
      · simp only [prepend, hk, ↓reduceDIte, tail]
        rw [show dep + (k - dep) = k by omega]
        exact hRdef.1 ρ ρ' hR' k (by omega)
    have hres := (hsk d hd).2.2.2 xs (hρ'_eq ▸ hR') (hρ'_eq ▸ (hD ρ ρ' hR' ▸ hd)) fun b hb => ?_
    · rwa [hρ'_eq] at hres
    have hp_mem : kpair d b ∈ˢ B_tot := mem_sigmaPairs.mpr ⟨d, hd, b, hb, rfl⟩
    have hitem := h' (kpair d b) hp_mem
    dsimp only [g_tot] at hitem
    rw [app_graph hp_mem, sfst_kpair, ssnd_kpair] at hitem
    have hocc : app (gf d) b ∈ˢ U_occ := app_mem_of_mem_piSet (hsk d hd).2.1 hb
    rw [← hU_occ d, mem_occSpaceQ_iff] at hocc
    obtain ⟨⟨i, n⟩, hin, hgo⟩ := hocc
    simp only [qs', List.mem_map] at hin
    obtain ⟨⟨i₀, n₀⟩, hi₀, heq⟩ := hin
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    obtain ⟨vs, y, hlen, heq_o, -, -⟩ := mem_graphOccs_iff.mp hgo
    rw [heq_o, downOcc_occEncItem] at hitem
    obtain ⟨i', vs', y', heq', hy'⟩ := hitem
    obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj heq'
    rw [heq_o]
    refine holdsQ_iff.mpr ⟨⟨i₀ + 1, vs, y, rfl, ?_⟩, ⟨i₀ + 1, vs, y, rfl, ?_⟩⟩
    · simp only [qs', List.mem_map]
      exact ⟨(i₀, vs.length), hlen ▸ hi₀, rfl⟩
    · rw [hρ'_eq]
      exact hy'

/-- The Π bound is a set of the level. -/
theorem SizeOn.pi {w : Nat} {R : FrameRel V} {D : Term} (hD : ConstOn R D)
    {Bb : (Nat → V) → V} (hB : SizeOn w (R.underBoth D) Bb) : SizeOn w R (piBound w D Bb) := by
  intro ρ ρ₀ hR hw
  unfold piBound
  split
  · rename_i hDw
    exact (tg_isGrothendieck hw).sigmaPairs_mem (hDw.1 hw) (fun d hd =>
      hB (cons d ρ) (cons d ρ₀) ⟨d, ρ, ρ₀, rfl, rfl, hR, hd, hD ρ ρ₀ hR ▸ hd⟩ hw) hDw.2
  · exact empty_mem_tg w

/-- **A member hole at its full arity, at hole-free arguments.**
Non-`pt` spines use the singleton occurrence graph `{occEncItem h vs x}`;
`pt`-hitting spines are dropped with `B = ∅` via `FrameRel.PtHitStable`. -/
theorem AccOn.holeApp {w : Nat} {Q : Nat → Nat → Prop} {R : FrameRel V} {h : Nat}
    {es : List Term} (hQ : Q h es.length) (hes : ∀ e ∈ es, ConstOn R e)
    (hRhit : R.PtHitStable Q) :
    AccOn w Q R (fun _ => unitSet) (Term.mkAppN (.bvar h) es) := by
  intro ρ ρ₀ _ x _ hx
  rw [interp_mkAppN_foldl, interp_bvar] at hx
  let vs := es.map (interp V ρ)
  have hQvs : Q h vs.length := by simpa [vs] using hQ
  by_cases hnp : NoPtPrefix (ρ h) vs
  · let o := occEncItem h vs x
    let g := graph (fun _ => o) unitSet (hasGraph_const o unitSet)
    refine ⟨unitSet, g, Subset.refl _,
      ⟨GraphOccs ρ h vs.length, graph_mem_piSet fun _ _ => occEncItem_mem_graphOccs hnp hx⟩,
      fun b hb => ?_, fun ρ' hR' h' => ?_⟩
    · rw [app_graph hb]
      exact ⟨⟨h, vs, x, rfl, hQvs⟩, ⟨h, vs, x, rfl, hnp, hx⟩⟩
    · rw [interp_mkAppN_foldl, interp_bvar]
      have hmap : vs = es.map (interp V ρ') :=
        List.map_congr_left fun e he => hes e he ρ ρ' hR'
      rw [← hmap]
      have hi := h' pt pt_mem_unitSet
      dsimp only [g] at hi
      rw [app_graph pt_mem_unitSet] at hi
      obtain ⟨i', vs', y', heq, hy'⟩ := hi
      obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj heq
      exact hy'
  · let g := graph (fun _ => empty) empty (hasGraph_empty (V := V) fun _ => empty)
    refine ⟨empty, g, empty_subset _,
      ⟨empty, graph_mem_piSet fun _ hb => absurd hb (not_mem_empty _)⟩,
      fun b hb => absurd hb (not_mem_empty b), fun ρ' hR' _ => ?_⟩
    rw [interp_mkAppN_foldl, interp_bvar]
    have hmap : vs = es.map (interp V ρ') :=
      List.map_congr_left fun e he => hes e he ρ ρ' hR'
    rw [← hmap]
    have hpt : vs.foldl app (ρ h) = pt := foldlApp_eq_pt_of_not_noPtPrefix hnp
    rw [hpt] at hx
    exact hRhit ρ ρ' hR' h vs hQvs hnp x hx

/-! ## The cases: the point -/

theorem ConstOn.ptOn {R : FrameRel V} {a : Term} (h : ConstOn R a) : PtOn R a :=
  fun ρ ρ' hR hp => h ρ ρ' hR ▸ hp

theorem PtOn.of_eqOn {R : FrameRel V} {P : (Nat → V) → Prop}
    (hdom : ∀ ρ ρ', R ρ ρ' → P ρ ∧ P ρ') {a b : Term}
    (heq : ∀ ρ, P ρ → interp V ρ a = interp V ρ b) (hb : PtOn R b) : PtOn R a := by
  intro ρ ρ' hR hp
  rw [heq ρ' (hdom ρ ρ' hR).2]
  rw [heq ρ (hdom ρ ρ' hR).1] at hp
  exact hb ρ ρ' hR hp

/-- **A Π over a hole-free domain** holds the point exactly when every
fibre does (its fibres being types, `hT`), so it carries the point along
the relation as its body does. -/
theorem PtOn.pi {R : FrameRel V} {D B : Term} (hD : ConstOn R D)
    (hT : FibTyOn R D B) (hB : PtOn (R.underBoth D) B) : PtOn R (.pi D B) := by
  intro ρ ρ' hR hp
  rw [interp_pi] at hp ⊢
  rw [← hD ρ ρ' hR]
  refine (pt_mem_piV_iff fun x hx => (hT ρ ρ' hR).2 x (hD ρ ρ' hR ▸ hx)).mpr fun d hd => ?_
  exact hB (cons d ρ) (cons d ρ') ⟨d, ρ, ρ', rfl, rfl, hR, hd, hD ρ ρ' hR ▸ hd⟩
    ((pt_mem_piV_iff (hT ρ ρ' hR).1).mp hp d hd)

/-- **A hole at its full arity** never holds the point (`PtFreeOn`), so
it carries it vacuously. -/
theorem PtOn.holeApp {Q : Nat → Nat → Prop} {R : FrameRel V} (hfree : PtFreeOn Q R) {h : Nat}
    {es : List Term} (hQ : Q h es.length) : PtOn R (Term.mkAppN (.bvar h) es) := by
  intro ρ ρ' hR hp
  rw [interp_mkAppN_foldl, interp_bvar] at hp
  exact absurd hp (hfree ρ ρ' hR h (es.map (interp V ρ)) (by simpa using hQ))

/-! ## Bounds reading given positions -/

/-- The positions `M` seen one binder down, the bound variable read. -/
def liftM (M : Nat → Prop) : Nat → Prop
  | 0 => True
  | i + 1 => M i

omit [SetTheory V] in
theorem InvOn.const (M : Nat → Prop) (c : V) : InvOn M (fun _ : Nat → V => c) :=
  fun _ _ _ => rfl

/-- **The Π bound reads what its domain and its body's bound read.** -/
theorem InvOn.pi {w : Nat} {M : Nat → Prop} {D : Term} (hD : NoBVar (fun i => ¬ M i) D)
    {Bb : (Nat → V) → V} (hB : InvOn (liftM M) Bb) : InvOn M (piBound w D Bb) := by
  intro ρ ρ' hag
  have hD' : interp V ρ D = interp V ρ' D :=
    interp_congr_noBVar D hD fun i hi => hag i (Classical.byContradiction hi)
  have hb : ∀ d, Bb (cons d ρ) = Bb (cons d ρ') := by
    intro d
    refine hB _ _ fun i hi => ?_
    cases i with
    | zero => rfl
    | succ i => exact hag i hi
  unfold piBound
  by_cases h1 : SmallAt w (interp V ρ D) ∧ HasSigmaPairs (interp V ρ D) (fun d => Bb (cons d ρ))
  · have h2 : SmallAt w (interp V ρ' D) ∧ HasSigmaPairs (interp V ρ' D) (fun d => Bb (cons d ρ')) :=
      ⟨hD' ▸ h1.1, h1.2.ext hD' fun d _ => hb d⟩
    rw [dite_eq_left h1, dite_eq_left h2]
    exact sigmaPairs_ext hD' h1.2 h2.2 fun d _ => hb d
  · have h2 : ¬ (SmallAt w (interp V ρ' D) ∧ HasSigmaPairs (interp V ρ' D) (fun d => Bb (cons d ρ'))) := by
      rintro ⟨hs, hsig⟩
      exact h1 ⟨hD' ▸ hs, hsig.ext hD'.symm fun d _ => (hb d).symm⟩
    rw [dite_eq_right h1, dite_eq_right h2]

end ConLeche.Semantics
