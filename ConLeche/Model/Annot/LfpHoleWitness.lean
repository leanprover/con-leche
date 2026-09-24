module

public import ConLeche.Model.Annot.LfpHoleOp
import ConLeche.SetModel.TupleContainer
public import ConLeche.Semantics.NoBVar
import ConLeche.Semantics.Tower.FixRecCoreI
import ConLeche.Semantics.Tower.SumRecCase
import ConLeche.Semantics.Tower.FixSquashI
import ConLeche.Semantics.Tower.FixLeafI
import ConLeche.Semantics.Tower.TowerMk

public section

/-!
# The closed tuple of a block whose fields with holes are FLAT (lane HOLE2, stage D)

(W) at tuples for the hole operator, with no field kinds in the datum:
the closure witness of `LfpClause.functor` at a `Type`-valued block,
read off a FLAT PRESENTATION of every constructor's fields with holes
(`LfpDatum.FlatAt`) — the shape the positivity function's run leaves
(every field hole-free, or a Π-tower of hole-free domains over a member
hole applied to the parameters and hole-free indices) together with U4
(no later field reads a recursive field, the
walk's class condition).

The presentation is SEMANTIC in its link to the fields: `fas` agrees
with the fields with holes at every hole frame and fitting prefix, so a
producer may present the fields by their reduced forms (the walk's
normal forms) as well as by themselves.

The container (`tupleContainer_closed_exists`):
* a SHAPE is a constructor tag with its fields' SHADOW tuple — the
  recursive positions replaced by `pt` — among the shadows of the
  elements of the component's fibre at SOME tuple of the space (the
  ordinary fields are hole-free and, by U4, read no recursive value, so
  a shadow determines them); the shape set is a member because it is
  cut from the tagged sum of the shadow telescopes, each ordinary domain
  kept where it is a member of the universe;
* its POSITIONS are the recursive fields' telescope spines, tagged by
  the field's position (a member of the universe: the field's value set
  is one, and an element's domain is its telescope);
* a position's TARGET is the member the field's hole names, at the
  tuple of the hole's index readings;
* the BUILDER puts the shadow's ordinary values back and curries the
  function on positions into each recursive slot.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open SetTheory
open ConLeche.SetTheory.Tower (projS mkTower inj TeleS BoundS towerSet FitsS projList)

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

namespace LfpDatum

/-- The hole positions at local depth `lo`: the variables `lo ..< lo + k`. -/
@[expose] def holeSlots (k lo : Nat) : Nat → Prop := fun i => lo ≤ i ∧ i < lo + k

/-- Field `l`'s variable, seen from depth `l'` (`l < l'`). -/
@[expose] def fieldSlot (l l' : Nat) : Nat → Prop := fun i => i = l' - 1 - l

/-- **Constructor `(c, j)`'s fields with holes, presented FLAT** at the
level assignment `ψ` and the parameter frame `ρp` (see the module
docstring): `fas` reads as the fields at every hole frame and fitting
prefix; a field `l` with `rec l = some (tl, m, es)` is the Π-tower over
`tl` (hole-free domains, nonzero codomain bits) of member `m`'s hole
applied to the parameters and the hole-free index readings `es`, whose
values fit member `m`'s index telescope; every other field is hole-free;
no later field reads a recursive field; the fields are sets of the block's level at every
fitting prefix. -/
@[expose] def FlatAt (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) (c j : Nat)
    (fas : List AnnotTerm)
    (rec : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)) : Prop :=
  fas.length = (D.fields ψ c j).length ∧
  -- the presentation reads as the fields
  (∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ l, l < (D.fields ψ c j).length →
    ∀ as : List V, SpineFit (D.frame ψ ρp X) ((D.fields ψ c j).take l) as →
    interp V (consList as (D.frame ψ ρp X)) ((D.fields ψ c j).getD l default)
      = interp V (consList as (D.frame ψ ρp X)) (fas.getD l default)) ∧
  -- a recursive field: a Π-tower of hole-free domains over a member hole
  (∀ l tl m es, rec l = some (tl, m, es) → l < (D.fields ψ c j).length ∧ m < D.k ∧
    fas.getD l default = mkPisAV tl (AnnotTerm.mkAppN (.bvar (l + tl.length + (D.k - 1 - m)))
      (holeParams D.k (D.params ψ).length (l + tl.length) ++ es)) ∧
    (∀ q dd, tl[q]? = some dd → dd.2.1 ≠ 0 ∧ NoBVar (holeSlots D.k (l + q)) dd.2.2) ∧
    (∀ e ∈ es, NoBVar (holeSlots D.k (l + tl.length)) e)) ∧
  -- an ordinary field: hole-free
  (∀ l, l < (D.fields ψ c j).length → rec l = none →
    NoBVar (holeSlots D.k l) (fas.getD l default)) ∧
  -- U4: no later field reads a recursive field
  (∀ l, l < (D.fields ψ c j).length → rec l ≠ none →
    ∀ l', l < l' → l' < (D.fields ψ c j).length →
      NoBVar (fieldSlot l l') (fas.getD l' default)) ∧
  -- a recursive call's indices fit its member's index telescope
  (∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ l tl m es, rec l = some (tl, m, es) →
    ∀ as : List V, SpineFit (D.frame ψ ρp X) ((D.fields ψ c j).take l) as →
    ∀ bs : List V, SpineFit (consList as (D.frame ψ ρp X)) (tl.map (·.2.2)) bs →
    SpineFit ρp (D.ids m ψ) (es.map (interp V (consList (as ++ bs) (D.frame ψ ρp X))))) ∧
  -- the fields are sets of the block's level
  (∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ l, l < (D.fields ψ c j).length →
    ∀ as : List V, SpineFit (D.frame ψ ρp X) ((D.fields ψ c j).take l) as →
    interp V (consList as (D.frame ψ ρp X)) ((D.fields ψ c j).getD l default)
      ∈ˢ (univ (D.w ψ) : V))

/-! ## Kit: variables a term does not read -/

section Kit

omit [SetTheory V] in
private theorem noBVar_exists {α : Type} :
    ∀ {e : AnnotTerm} {P : α → Nat → Prop}, (∀ a, NoBVar (P a) e) →
      NoBVar (fun i => ∃ a, P a i) e := by
  intro e
  induction e with
  | bvar i => intro P h; exact fun ⟨a, ha⟩ => h a ha
  | sort u => intros; trivial
  | const c us => intros; trivial
  | prf => intros; trivial
  | app f a ihf iha => intro P h; exact ⟨ihf fun a => (h a).1, iha fun a => (h a).2⟩
  | eqE a b iha ihb => intro P h; exact ⟨iha fun a => (h a).1, ihb fun a => (h a).2⟩
  | fst e ihe => intro P h; exact ihe fun a => h a
  | snd e ihe => intro P h; exact ihe fun a => h a
  | lam v A b ihA ihb =>
    intro P h
    refine ⟨ihA fun a => (h a).1, NoBVar.mono (fun i hi => ?_)
      (ihb (P := fun a => shiftP (P a)) fun a => (h a).2)⟩
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi
  | pi u v A B ihA ihB =>
    intro P h
    refine ⟨ihA fun a => (h a).1, NoBVar.mono (fun i hi => ?_)
      (ihB (P := fun a => shiftP (P a)) fun a => (h a).2)⟩
    cases i with
    | zero => exact hi.elim
    | succ i => exact hi

/-- A predicate on variables, seen `n` binders deeper. -/
private def shiftN (n : Nat) (P : Nat → Prop) : Nat → Prop := fun i => n ≤ i ∧ P (i - n)

omit [SetTheory V] in
private theorem noBVar_mkPisAV :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm} {P : Nat → Prop},
      NoBVar P (mkPisAV tl B) →
      (∀ q dd, tl[q]? = some dd → NoBVar (shiftN q P) dd.2.2) ∧ NoBVar (shiftN tl.length P) B
  | [], B, P, h => ⟨fun q dd hq => by simp at hq,
      NoBVar.mono (fun i hi => by simpa [shiftN] using hi.2) h⟩
  | d :: tl, B, P, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := noBVar_mkPisAV (tl := tl) (B := B) h2
    have hsh : ∀ q i, shiftN (q + 1) P i → shiftN q (shiftP P) i := by
      intro q i ⟨hqi, hp⟩
      refine ⟨by omega, ?_⟩
      obtain ⟨n, hn⟩ : ∃ n, i - q = n + 1 := ⟨i - q - 1, by omega⟩
      rw [hn]
      show P n
      rwa [show i - (q + 1) = n by omega] at hp
    refine ⟨fun q dd hq => ?_, ?_⟩
    · cases q with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hq
        subst hq
        exact NoBVar.mono (fun i hi => by simpa [shiftN] using hi.2) h1
      | succ q =>
        simp only [List.getElem?_cons_succ] at hq
        exact NoBVar.mono (hsh q) (ih1 q dd hq)
    · exact NoBVar.mono (hsh tl.length) ih2

omit [SetTheory V] in
private theorem noBVar_mkAppN :
    ∀ {args : List AnnotTerm} {f : AnnotTerm} {P : Nat → Prop},
      NoBVar P (AnnotTerm.mkAppN f args) → NoBVar P f ∧ ∀ a ∈ args, NoBVar P a
  | [], f, P, h => ⟨h, fun a ha => by simp at ha⟩
  | a :: args, f, P, h => by
    rw [AnnotTerm.mkAppN_cons] at h
    obtain ⟨⟨hf, ha⟩, hr⟩ := noBVar_mkAppN (args := args) h
    refine ⟨hf, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact hr b hb

omit [SetTheory V] in
private theorem shiftN_holeSlots {k l q i : Nat} :
    shiftN q (holeSlots k l) i → holeSlots k (l + q) i := by
  intro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega⟩

omit [SetTheory V] in
private theorem holeSlots_shiftN {k l q i : Nat} :
    holeSlots k (l + q) i → shiftN q (holeSlots k l) i := by
  intro ⟨h1, h2⟩; exact ⟨by omega, by omega, by omega⟩

omit [SetTheory V] in
private theorem fieldSlot_shiftN {l'' l q i : Nat} (hl : l'' < l) :
    fieldSlot l'' (l + q) i → shiftN q (fieldSlot l'' l) i := by
  intro h
  unfold fieldSlot at h
  exact ⟨by omega, by show i - q = l - 1 - l''; omega⟩

/-! ## Frames -/

omit [SetTheory V] in
private theorem consList_apply_ge (bs : List V) (ρ : Nat → V) {i : Nat} (hi : bs.length ≤ i) :
    consList bs ρ i = ρ (i - bs.length) := by
  have := consList_apply_add bs ρ (i - bs.length)
  rwa [Nat.sub_add_cancel hi] at this

private theorem consList_apply_lt (bs : List V) (ρ : Nat → V) {i : Nat} (hi : i < bs.length) :
    consList bs ρ i = bs.getD (bs.length - 1 - i) pt := by
  induction bs generalizing ρ i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons b bs ih =>
    rw [consList_cons]
    rcases Nat.lt_or_ge i bs.length with h | h
    · rw [ih _ h, List.length_cons,
        show bs.length + 1 - 1 - i = (bs.length - 1 - i) + 1 by omega, List.getD_cons_succ]
    · have hi' : i = bs.length := by simp at hi; omega
      subst hi'
      rw [consList_apply_ge _ _ (Nat.le_refl _), Nat.sub_self, List.length_cons,
        Nat.add_sub_cancel, Nat.sub_self, List.getD_cons_zero]
      rfl

variable {D : LfpDatum V}

/-- Two hole frames, extended by field lists agreeing off the recursive
positions and then by one list, agree off the holes and the recursive
fields' variables. -/
private theorem frame_agree {ψ : Name → Nat} {ρp : Nat → V} (X X' : Nat → V) (r : Nat → Bool)
    (as as' bs : List V) (hlen : as.length = as'.length)
    (hag : ∀ i, i < as.length → r i = false → as.getD i pt = as'.getD i pt) :
    AgreeOff (fun i => ∃ o : Option Nat, match o with
        | none => holeSlots D.k (as.length + bs.length) i
        | some l => l < as.length ∧ r l = true ∧ fieldSlot l (as.length + bs.length) i)
      (consList (as ++ bs) (D.frame ψ ρp X)) (consList (as' ++ bs) (D.frame ψ ρp X')) := by
  intro i hi
  rw [consList_append, consList_append]
  rcases Nat.lt_or_ge i bs.length with h | h
  · rw [consList_apply_lt _ _ h, consList_apply_lt _ _ h]
  rw [consList_apply_ge _ _ h, consList_apply_ge _ _ h]
  rcases Nat.lt_or_ge (i - bs.length) as.length with h2 | h2
  · rw [consList_apply_lt _ _ h2, consList_apply_lt _ _ (hlen ▸ h2), ← hlen]
    refine hag _ (by omega) ?_
    cases hr : r (as.length - 1 - (i - bs.length)) with
    | false => rfl
    | true =>
      exact absurd ⟨some (as.length - 1 - (i - bs.length)), by omega, hr,
        by unfold fieldSlot; omega⟩ hi
  rw [consList_apply_ge _ _ h2, consList_apply_ge _ _ (hlen ▸ h2), ← hlen]
  unfold LfpDatum.frame
  have hk : ∀ Y : Nat → V, ((List.range D.k).map (D.holeVal ψ ρp Y)).length = D.k := by simp
  rcases Nat.lt_or_ge (i - bs.length - as.length) D.k with h3 | h3
  · exact absurd ⟨none, show as.length + bs.length ≤ i ∧ i < as.length + bs.length + D.k by
      omega⟩ hi
  rw [consList_apply_ge _ _ (by rw [hk]; exact h3), consList_apply_ge _ _ (by rw [hk]; exact h3),
    hk, hk]

/-- **Transport** of a term reading no hole and no recursive field below
it, between hole frames extended by field lists agreeing off the
recursive positions. -/
private theorem interp_transport {ψ : Name → Nat} {ρp : Nat → V} (X X' : Nat → V)
    (r : Nat → Bool) {as as' : List V} (bs : List V) (hlen : as.length = as'.length)
    (hag : ∀ i, i < as.length → r i = false → as.getD i pt = as'.getD i pt) {e : AnnotTerm}
    (hh : NoBVar (holeSlots D.k (as.length + bs.length)) e)
    (hf : ∀ l, l < as.length → r l = true → NoBVar (fieldSlot l (as.length + bs.length)) e) :
    interp V (consList (as ++ bs) (D.frame ψ ρp X)) e
      = interp V (consList (as' ++ bs) (D.frame ψ ρp X')) e := by
  refine interp_congr_noBVar e (noBVar_exists fun o => ?_) (frame_agree X X' r as as' bs hlen hag)
  cases o with
  | none => exact hh
  | some l =>
    by_cases hl : l < as.length ∧ r l = true
    · exact NoBVar.mono (fun i hi => hi.2.2) (hf l hl.1 hl.2)
    · exact NoBVar.mono (fun i hi => absurd ⟨hi.1, hi.2.1⟩ hl) hh

/-! ## Members of a universe -/

private theorem app_mem_univ' {w : Nat} (hw : w ≠ 0) {f a : V} (hf : f ∈ˢ (univ w : V)) :
    app f a ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  unfold app
  split
  · exact hU.pt_mem (empty_mem_univ w)
  · exact hU.sUnion_mem (hU.sep_mem (hU.sUnion_mem (hU.sUnion_mem hf)))

private theorem kpair_fst_mem {w : Nat} (hw : w ≠ 0) {a b : V} (h : kpair a b ∈ˢ (univ w : V)) :
    a ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  unfold kpair at h
  exact hU.transitive (hU.transitive h (mem_upair_left _ _)) (mem_sing.mpr rfl)

private theorem spair_mem_univ' {w : Nat} (hw : w ≠ 0) {a b : V} (ha : a ∈ˢ (univ w : V))
    (hb : b ∈ˢ (univ w : V)) : spair a b ∈ˢ (univ w : V) := by
  rw [spair_eq_kpair]
  exact (univ_isTGUniverse hw).kpair_mem ha ha hb

private theorem vnat_mem_univ' {w : Nat} (hw : w ≠ 0) (j : Nat) : (vnat j : V) ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  exact (univ_isTGUniverse hw).transitive (omega_mem_univ_succ w') (vnat_mem_omega j)

private theorem inj_mem_univ' {w : Nat} (hw : w ≠ 0) (j : Nat) {x : V} (hx : x ∈ˢ (univ w : V)) :
    ConLeche.SetTheory.Tower.inj j x ∈ˢ (univ w : V) :=
  spair_mem_univ' hw (vnat_mem_univ' hw j) hx

private theorem mkTower_mem_univ' {w : Nat} (hw : w ≠ 0) :
    ∀ {L : List V}, (∀ x, x ∈ L → x ∈ˢ (univ w : V)) → mkTower L ∈ˢ (univ w : V)
  | [], _ => (univ_isTGUniverse hw).pt_mem (empty_mem_univ w)
  | a :: L, h => by
    show spair a (mkTower L) ∈ˢ _
    exact spair_mem_univ' hw (h a List.mem_cons_self)
      (mkTower_mem_univ' hw fun x hx => h x (List.mem_cons_of_mem a hx))

/-- A function's domain is a member when the function is. -/
private theorem dom_mem_univ {w : Nat} (hw : w ≠ 0) {A f : V} {B : V → V}
    (hf : f ∈ˢ piSet A B) (hfU : f ∈ˢ (univ w : V)) : A ∈ˢ (univ w : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  obtain ⟨hsub, htot⟩ := mem_piSet.mp hf
  refine hU.mem_of_subset_mem (hU.image_mem (F := sfst) hfU fun z hz => ?_) fun x hx => ?_
  · obtain ⟨a, -, b, -, rfl⟩ := mem_sigmaPairs.mp (hsub z hz)
    rw [sfst_kpair]
    exact kpair_fst_mem hw (hU.transitive hfU hz)
  · obtain ⟨y, hy, -⟩ := htot x hx
    exact mem_image.mpr ⟨_, hy, (sfst_kpair x y).symm⟩

/-- A member of a nested product at a positive sort bounds its telescope
hereditarily, when it is a member of the universe. -/
private theorem boundS_of_piTele {w : Nat} (hw : w ≠ 0) {B : List V → V} :
    ∀ {n : Nat} {T : TeleS V n} {acc : List V} {f : V},
      f ∈ˢ piTele w T B acc → f ∈ˢ (univ w : V) → BoundS w T
  | _, .nil, _, _, _, _ => trivial
  | _, .cons A T, acc, f, hf, hfU => by
    have hf' : f ∈ˢ piR w A fun a => piTele w (T a) B (acc ++ [a]) := hf
    refine ⟨dom_mem_univ hw (by rw [piR_pos hw] at hf'; exact hf') hfU, fun a ha => ?_⟩
    exact boundS_of_piTele hw (app_mem_piR_pos hw hf' ha) (app_mem_univ' hw hfU)

/-! ## λ-towers over telescopes -/

omit [SetTheory V] in
private theorem frameIdx_cons_consList' (a : V) (bs : List V) (ρ : Nat → V) :
    frameIdx (bs.length + 1) (consList bs (cons a ρ)) = a :: bs := by
  have := frameIdx_consList' (a :: bs) ρ
  rwa [List.length_cons, consList_cons] at this

/-- **Eta**: a member of the nested product is the λ-tower of its spine
folds. -/
private theorem piTele_eta' {w : Nat} (hw : w ≠ 0) {B : List V → V} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V} {f : V},
      f ∈ˢ piTele w (teleOfFields ρ (tl.map (·.2.2))) B acc →
      lamTower w ρ tl (fun σ => (frameIdx tl.length σ).foldl SetTheory.app f) = f
  | [], _, _, _, _ => by simp [lamTower, frameIdx]
  | d :: tl, ρ, acc, f, hf => by
    rw [List.map_cons] at hf
    simp only [teleOfFields, piTele] at hf
    show lamR w (interp V ρ d.2.2) (fun a => lamTower w (cons a ρ) tl
      (fun σ => (frameIdx (tl.length + 1) σ).foldl SetTheory.app f)) = f
    refine Eq.trans ?_ (lamR_eta hf)
    refine lamR_congr fun a ha => ?_
    have hfa := app_mem_piR_pos hw hf ha
    rw [← piTele_eta' hw hfa]
    refine lamTower_congr_leaves fun bs hbs => ?_
    have hlen : bs.length = tl.length := by rw [hbs.length_eq, List.length_map]
    rw [← hlen, frameIdx_cons_consList', frameIdx_consList', List.foldl_cons]

/-- A λ-tower over a bounded telescope with member values is a member. -/
private theorem lamTower_mem_univ' {w : Nat} (hw : w ≠ 0) {g : (Nat → V) → V} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V},
      BoundS w (teleOfFields ρ (tl.map (·.2.2))) →
      (∀ bs, SpineFit ρ (tl.map (·.2.2)) bs → g (consList bs ρ) ∈ˢ (univ w : V)) →
      lamTower w ρ tl g ∈ˢ (univ w : V)
  | [], ρ, _, hg => by simpa [lamTower] using hg [] trivial
  | d :: tl, ρ, hF, hg => by
    have hU := univ_isTGUniverse (V := V) hw
    rw [List.map_cons] at hF
    obtain ⟨hA, hB⟩ := hF
    show lamR w (interp V ρ d.2.2) (fun a => lamTower w (cons a ρ) tl g) ∈ˢ _
    rw [lamR_pos hw]
    unfold graph
    refine hU.image_mem hA fun a ha => ?_
    refine hU.kpair_mem hA (hU.transitive hA ha) ?_
    refine lamTower_mem_univ' hw (hB a ha) fun bs hbs => ?_
    have := hg (a :: bs) ⟨ha, hbs⟩
    rwa [consList_cons] at this

/-- λ-towers over frames whose telescope readings agree, of a body that
agrees at the leaves. -/
private theorem lamTower_congr_frame {m : Nat} :
    ∀ (tl : List (Nat × Nat × AnnotTerm)) {σ σ' : Nat → V} {g : (Nat → V) → V},
      (∀ q dd (bs : List V), tl[q]? = some dd → bs.length = q →
        interp V (consList bs σ) dd.2.2 = interp V (consList bs σ') dd.2.2) →
      (∀ bs : List V, bs.length = tl.length → g (consList bs σ) = g (consList bs σ')) →
      lamTower m σ tl g = lamTower m σ' tl g
  | [], σ, σ', g, _, hg => hg [] rfl
  | d :: tl, σ, σ', g, hd, hg => by
    show lamR m (interp V σ d.2.2) (fun a => lamTower m (cons a σ) tl g)
      = lamR m (interp V σ' d.2.2) (fun a => lamTower m (cons a σ') tl g)
    rw [show interp V σ d.2.2 = interp V σ' d.2.2 from hd 0 d [] rfl rfl]
    congr 1
    funext a
    refine lamTower_congr_frame tl (fun q dd bs hq hbs => ?_) (fun bs hbs => ?_)
    · have := hd (q + 1) dd (a :: bs) (by simpa using hq) (by simp [hbs])
      simpa [consList_cons] using this
    · have := hg (a :: bs) (by simp [hbs])
      simpa [consList_cons] using this

/-- Telescopes whose domains read the same along every extension are
equal. -/
private theorem teleOfFields_congr :
    ∀ (Fs : List AnnotTerm) {σ σ' : Nat → V},
      (∀ q F (bs : List V), Fs[q]? = some F → bs.length = q →
        interp V (consList bs σ) F = interp V (consList bs σ') F) →
      teleOfFields σ Fs = teleOfFields σ' Fs
  | [], _, _, _ => rfl
  | F :: Fs, σ, σ', h => by
    simp only [teleOfFields_cons]
    rw [show interp V σ F = interp V σ' F from h 0 F [] rfl rfl]
    congr 1
    funext a
    refine teleOfFields_congr Fs fun q G bs hq hbs => ?_
    have := h (q + 1) G (a :: bs) (by simpa using hq) (by simp [hbs])
    simpa [consList_cons] using this

/-! ## Shadow spines -/

/-- The recursive positions of a presentation. -/
private def isR (r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm))
    (l : Nat) : Bool := (r l).isSome

/-- The shadow of a field spine from position `i` on: the recursive
positions hold `pt`. -/
private noncomputable def shGo (r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)) :
    Nat → List V → List V
  | _, [] => []
  | i, a :: as => (if isR r i then pt else a) :: shGo r (i + 1) as

private theorem shGo_length (r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)) :
    ∀ (i : Nat) (fs : List V), (shGo r i fs).length = fs.length
  | _, [] => rfl
  | i, _ :: fs => by simp [shGo, shGo_length r (i + 1) fs]

private theorem shGo_getD (r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)) :
    ∀ (i : Nat) (fs : List V) (l : Nat),
      (shGo r i fs).getD l pt = if isR r (i + l) then pt else fs.getD l pt
  | i, [], l => by by_cases h : isR r (i + l) <;> simp [shGo, h]
  | i, a :: fs, 0 => by simp [shGo]
  | i, a :: fs, l + 1 => by
    simp only [shGo, List.getD_cons_succ]
    rw [shGo_getD r (i + 1) fs l, show i + 1 + l = i + (l + 1) by omega]

private theorem shGo_take (r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)) :
    ∀ (i : Nat) (fs : List V) (l : Nat), (shGo r i fs).take l = shGo r i (fs.take l)
  | _, [], _ => by simp [shGo]
  | _, _ :: _, 0 => rfl
  | i, a :: fs, l + 1 => by
    simp only [shGo, List.take_succ_cons]
    rw [shGo_take r (i + 1) fs l]

/-! ## One constructor's fields, at a hole frame and at the shadow -/

private theorem spineFit_take' {ρ : Nat → V} :
    ∀ {Fs : List AnnotTerm} {as : List V}, SpineFit ρ Fs as → ∀ l,
      SpineFit ρ (Fs.take l) (as.take l)
  | [], [], _, _ => by simp; trivial
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim
  | _ :: _, _ :: _, _, 0 => by simp; trivial
  | _ :: Fs, _ :: as, h, l + 1 => by
    simp only [List.take_succ_cons]
    exact ⟨h.1, spineFit_take' (Fs := Fs) (as := as) h.2 l⟩

/-- The fixed tuple the shadow frames read the hole slots at (the shapes'
data is hole-free, so any tuple does). -/
private noncomputable def X₀ : Nat → V := fun _ => empty

private theorem shGo_agree (r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm))
    (as : List V) : ∀ i, i < as.length → isR r i = false → as.getD i pt = (shGo r 0 as).getD i pt := by
  intro i _ hr
  rw [shGo_getD, Nat.zero_add, hr]
  rfl

section Ctor

variable {ψ : Name → Nat} {ρp : Nat → V} {c j : Nat} {fas : List AnnotTerm}
  {r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)}

private theorem isR_of_ne {l : Nat} (h : r l ≠ none) : isR r l = true := by
  unfold isR; cases hr : r l with
  | none => exact absurd hr h
  | some _ => rfl

private theorem ne_of_isR {l : Nat} (h : isR r l = true) : r l ≠ none := by
  unfold isR at h; cases hr : r l with
  | none => rw [hr] at h; exact nomatch h
  | some _ => exact Option.some_ne_none _

private theorem none_of_isR {l : Nat} (h : isR r l = false) : r l = none := by
  unfold isR at h; cases hr : r l with
  | none => rfl
  | some _ => rw [hr] at h; exact nomatch h

/-- **An ordinary field reads at the shadow** of its prefix, at the
fixed tuple. -/
private theorem ord_read (hF : D.FlatAt ψ ρp c j fas r) {X : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) {fs : List V}
    (hfs : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs) {l : Nat}
    (hl : l < (D.fields ψ c j).length) (hr : isR r l = false) :
    interp V (consList (fs.take l) (D.frame ψ ρp X)) ((D.fields ψ c j).getD l default)
      = interp V (consList (shGo r 0 (fs.take l)) (D.frame ψ ρp X₀)) (fas.getD l default) := by
  obtain ⟨-, hagr, -, hord, hU4, -⟩ := hF
  have hlen : (fs.take l).length = l := by
    rw [List.length_take, hfs.length_eq]; omega
  rw [hagr X hX l hl _ (spineFit_take' hfs l)]
  have := interp_transport (D := D) (ψ := ψ) (ρp := ρp) X X₀ (isR r) (as := fs.take l)
    (as' := shGo r 0 (fs.take l)) [] (shGo_length r 0 _).symm (shGo_agree r _)
    (e := fas.getD l default)
    (by rw [hlen]; exact hord l hl (none_of_isR hr))
    (fun l'' hl'' hr'' => by
      rw [hlen] at hl'' ⊢
      exact hU4 l'' (by omega) (ne_of_isR hr'') l hl'' hl)
  simpa using this

/-- **A recursive field's telescope domains read at the shadow** of its
prefix. -/
private theorem rec_entry (hF : D.FlatAt ψ ρp c j fas r) {X : Nat → V} {fs : List V}
    (hfs : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs) {l : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {m : Nat} {es : List AnnotTerm}
    (hrl : r l = some (tl, m, es)) :
    ∀ q dd (bs : List V), tl[q]? = some dd → bs.length = q →
      interp V (consList bs (consList (fs.take l) (D.frame ψ ρp X))) dd.2.2
        = interp V (consList bs (consList (shGo r 0 (fs.take l)) (D.frame ψ ρp X₀))) dd.2.2 := by
  obtain ⟨-, -, hrec, -, hU4, -⟩ := hF
  obtain ⟨hl, -, hfl, htl, -⟩ := hrec l tl m es hrl
  have hlen : (fs.take l).length = l := by
    rw [List.length_take, hfs.length_eq]; omega
  intro q dd bs hdd hbs
  rw [← consList_append, ← consList_append]
  refine interp_transport X X₀ (isR r) bs (shGo_length r 0 _).symm (shGo_agree r _)
    (by rw [hlen, hbs]; exact (htl q dd hdd).2) (fun l'' hl'' hr'' => ?_)
  rw [hlen] at hl'' ⊢
  rw [hbs]
  have hU := hU4 l'' (by omega) (ne_of_isR hr'') l hl'' hl
  rw [hfl] at hU
  exact NoBVar.mono (fun i hi => fieldSlot_shiftN hl'' hi) ((noBVar_mkPisAV hU).1 q dd hdd)

/-- **A recursive field's telescope reads at the shadow** of its prefix. -/
private theorem rec_tele (hF : D.FlatAt ψ ρp c j fas r) {X : Nat → V} {fs : List V}
    (hfs : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs) {l : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {m : Nat} {es : List AnnotTerm}
    (hrl : r l = some (tl, m, es)) :
    teleOfFields (consList (fs.take l) (D.frame ψ ρp X)) (tl.map (·.2.2))
      = teleOfFields (consList (shGo r 0 (fs.take l)) (D.frame ψ ρp X₀)) (tl.map (·.2.2)) := by
  refine teleOfFields_congr _ fun q F bs hq hbs => ?_
  rw [List.getElem?_map] at hq
  obtain ⟨dd, hdd, rfl⟩ := Option.map_eq_some_iff.mp hq
  exact rec_entry hF hfs hrl q dd bs hdd hbs

/-- **A recursive field's index readings read at the shadow** of its
prefix. -/
private theorem rec_es (hF : D.FlatAt ψ ρp c j fas r) {X : Nat → V} {fs : List V}
    (hfs : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs) {l : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {m : Nat} {es : List AnnotTerm}
    (hrl : r l = some (tl, m, es)) {bs : List V} (hbs : bs.length = tl.length) :
    es.map (interp V (consList (fs.take l ++ bs) (D.frame ψ ρp X)))
      = es.map (interp V (consList (shGo r 0 (fs.take l) ++ bs) (D.frame ψ ρp X₀))) := by
  obtain ⟨-, -, hrec, -, hU4, -⟩ := hF
  obtain ⟨hl, -, hfl, -, hes⟩ := hrec l tl m es hrl
  have hlen : (fs.take l).length = l := by
    rw [List.length_take, hfs.length_eq]; omega
  refine List.map_congr_left fun e he => ?_
  refine interp_transport X X₀ (isR r) bs (shGo_length r 0 _).symm (shGo_agree r _)
    (by rw [hlen, hbs]; exact hes e he) (fun l'' hl'' hr'' => ?_)
  rw [hlen] at hl'' ⊢
  rw [hbs]
  have hU := hU4 l'' (by omega) (ne_of_isR hr'') l hl'' hl
  rw [hfl] at hU
  have h2 := (noBVar_mkAppN (noBVar_mkPisAV hU).2).2 e (List.mem_append_right _ he)
  exact NoBVar.mono (fun i hi => fieldSlot_shiftN hl'' hi) h2

/-- **A recursive field reads, at a hole frame, as the nested product**
over its telescope of its member's family at the index tuple. -/
private theorem rec_read (hw : D.w ψ ≠ 0) (hok : D.HoleTmOk ψ ρp) (hF : D.FlatAt ψ ρp c j fas r)
    {X : Nat → V} (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) {fs : List V}
    (hfs : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs) {l : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {m : Nat} {es : List AnnotTerm}
    (hrl : r l = some (tl, m, es)) :
    interp V (consList (fs.take l) (D.frame ψ ρp X)) ((D.fields ψ c j).getD l default)
      = piTele (D.w ψ) (teleOfFields (consList (fs.take l) (D.frame ψ ρp X)) (tl.map (·.2.2)))
          (fun bs => app (X m) (tupW (D.u m ψ)
            (es.map (interp V (consList (fs.take l ++ bs) (D.frame ψ ρp X)))))) [] := by
  obtain ⟨-, hagr, hrec, -, -, htgt, -⟩ := hF
  obtain ⟨hl, hm, hfl, htl, -⟩ := hrec l tl m es hrl
  have hlen : (fs.take l).length = l := by
    rw [List.length_take, hfs.length_eq]; omega
  have hpre := spineFit_take' hfs l
  rw [hagr X hX l hl _ hpre, hfl]
  refine interp_mkPisAV_piTele (fun d hd => ?_) fun bs hbs => ?_
  · obtain ⟨q, hq⟩ := List.getElem?_of_mem hd
    exact ⟨fun h => absurd h (htl q d hq).1, fun h => absurd h hw⟩
  · have hbl : bs.length = tl.length := by rw [hbs.length_eq, List.length_map]
    rw [List.nil_append, ← consList_append, interp_mkAppN_foldl, List.map_append,
      map_interp_holeParams]
    have hL : (fs.take l ++ bs).length = l + tl.length := by simp [hlen, hbl]
    -- the hole's value
    have hhole : interp V (consList (fs.take l ++ bs) (D.frame ψ ρp X))
        (.bvar (l + tl.length + (D.k - 1 - m))) = D.holeVal ψ ρp X m := by
      show consList _ _ _ = _
      rw [consList_apply_ge _ _ (by rw [hL]; omega), hL,
        show l + tl.length + (D.k - 1 - m) - (l + tl.length) = D.k - 1 - m by omega]
      unfold LfpDatum.frame
      rw [consList_apply_lt _ _ (by simp; omega)]
      simp only [List.length_map, List.length_range]
      rw [show D.k - 1 - (D.k - 1 - m) = m by omega, List.getD_eq_getElem?_getD,
        List.getElem?_map, List.getElem?_range (by omega)]
      rfl
    -- the parameters' values
    have hpar : holeParamVals D.k (D.params ψ).length (l + tl.length)
        (consList (fs.take l ++ bs) (D.frame ψ ρp X))
          = frameIdx (D.pars m ψ).length ρp := by
      rw [(hok m hm).1.1]
      unfold holeParamVals frameIdx
      refine List.map_congr_left fun p hp => ?_
      have hp' := List.mem_range.mp hp
      rw [consList_apply_ge _ _ (by rw [hL]; omega), hL]
      unfold LfpDatum.frame
      rw [consList_apply_ge _ _ (by simp; omega)]
      simp only [List.length_map, List.length_range]
      congr 1
      omega
    rw [hhole, hpar]
    exact D.holeVal_app (hok m hm).1.2 (htgt X hX l tl m es hrl _ hpre bs hbs)

end Ctor

end Kit

/-! ## The shadow telescope -/

section Container

/-- A presentation's recursive data. -/
private abbrev RecFn := Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)

open Classical in
/-- A set, kept where it is a member of the universe. -/
private noncomputable def wrapU (w : Nat) (S : V) : V := if S ∈ˢ (univ w : V) then S else empty

private theorem wrapU_mem (w : Nat) (S : V) : wrapU w S ∈ˢ (univ w : V) := by
  unfold wrapU; split
  · assumption
  · exact empty_mem_univ w

private theorem wrapU_of_mem {w : Nat} {S : V} (h : S ∈ˢ (univ w : V)) : wrapU w S = S := by
  unfold wrapU; rw [if_pos h]

/-- The shadow telescope's field `i` at the prefix `acc`. -/
private noncomputable def shG (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V)
    (fas : List AnnotTerm) (r : RecFn) (i : Nat) (acc : List V) : V :=
  if isR r i then unitSet
  else wrapU (D.w ψ) (interp V (consList acc (D.frame ψ ρp X₀)) (fas.getD i default))

/-- **The shadow telescope**: a recursive position is the unit set, an
ordinary one its presentation at the shadow frame, kept in the
universe. -/
private noncomputable def shTele (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V)
    (fas : List AnnotTerm) (r : RecFn) : (n i : Nat) → List V → TeleS V n
  | 0, _, _ => .nil
  | n + 1, i, acc => .cons (shG D ψ ρp fas r i acc) fun a => shTele D ψ ρp fas r n (i + 1) (acc ++ [a])

private theorem boundS_shTele (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V)
    (fas : List AnnotTerm) (r : RecFn) :
    ∀ (n i : Nat) (acc : List V), BoundS (D.w ψ) (shTele D ψ ρp fas r n i acc)
  | 0, _, _ => trivial
  | n + 1, i, acc => by
    refine ⟨?_, fun a _ => boundS_shTele D ψ ρp fas r n (i + 1) (acc ++ [a])⟩
    unfold shG; split
    · exact unitSet_mem_univ _
    · exact wrapU_mem _ _

private theorem fitsS_shTele (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V)
    (fas : List AnnotTerm) (r : RecFn) :
    ∀ (n i : Nat) (acc bs : List V), bs.length = n →
      (∀ q, q < n → bs.getD q pt ∈ˢ shG D ψ ρp fas r (i + q) (acc ++ bs.take q)) →
      FitsS (shTele D ψ ρp fas r n i acc) bs
  | 0, _, _, [], _, _ => trivial
  | 0, _, _, _ :: _, h, _ => by simp at h
  | _ + 1, _, _, [], h, _ => by simp at h
  | n + 1, i, acc, b :: bs, hlen, h => by
    refine ⟨by simpa using h 0 (by omega), ?_⟩
    refine fitsS_shTele D ψ ρp fas r n (i + 1) (acc ++ [b]) bs (by simpa using hlen)
      fun q hq => ?_
    have := h (q + 1) (by omega)
    simpa [show i + (q + 1) = i + 1 + q by omega, List.append_assoc] using this

/-- **The shadow of a fitting spine fits the shadow telescope.** -/
private theorem shadow_fits {D : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V} {c j : Nat}
    {fas : List AnnotTerm} {r : RecFn} (hF : D.FlatAt ψ ρp c j fas r) {X : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) {fs : List V}
    (hfs : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs) :
    FitsS (shTele D ψ ρp fas r (D.fields ψ c j).length 0 []) (shGo r 0 fs) := by
  refine fitsS_shTele D ψ ρp fas r _ 0 [] _ (by rw [shGo_length, hfs.length_eq]) fun q hq => ?_
  rw [List.nil_append, shGo_take, shGo_getD]
  simp only [Nat.zero_add]
  unfold shG
  by_cases hr : isR r q = true
  · rw [if_pos hr, if_pos hr]; exact pt_mem_unitSet
  · have hr' : isR r q = false := by simpa using hr
    rw [if_neg hr, if_neg hr, ← ord_read hF hX hfs hq hr']
    have hmem := ConLeche.Semantics.FixKI.spineFit_getD_mem' hfs hq
    rw [wrapU_of_mem (hF.2.2.2.2.2.2 X hX q hq _ (spineFit_take' hfs q))]
    exact hmem

/-! ## The container data -/


private def nF (D : LfpDatum V) (ψ : Name → Nat) (c j : Nat) : Nat := (D.fields ψ c j).length

private noncomputable def fam (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) (fd : Nat → Nat → List AnnotTerm × RecFn) (c j : Nat) : V :=
  if j < D.nctors c then towerSet (D.w ψ) (shTele D ψ ρp (fd c j).1 (fd c j).2 (nF D ψ c j) 0 [])
  else empty

private noncomputable def shapeOf (fd : Nat → Nat → List AnnotTerm × RecFn) (c j : Nat) (fs : List V) : V :=
  ConLeche.SetTheory.Tower.inj c (ConLeche.SetTheory.Tower.inj j (mkTower (shGo (fd c j).2 0 fs)))

/-- **The shapes**: the tagged shadows of the elements of the fibre at
some tuple. -/
private noncomputable def shapes (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) (fd : Nat → Nat → List AnnotTerm × RecFn) (c : Nat) (t : V) : V :=
  sep (image (ConLeche.SetTheory.Tower.inj c) (ConLeche.SetTheory.Tower.sumSet (D.w ψ) (fam D ψ ρp fd c))) fun a =>
    ∃ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X ∧ ∃ j fs, D.HFits ψ ρp X t c j fs ∧
      a = shapeOf fd c j fs

private noncomputable def sC (a : V) : Nat := natIdx (sfst a)
private noncomputable def sJ (a : V) : Nat := natIdx (sfst (ssnd a))
private noncomputable def sF (D : LfpDatum V) (ψ : Name → Nat) (a : V) : List V :=
  projList (nF D ψ (sC a) (sJ a)) (ssnd (ssnd a))
private noncomputable def sR (fd : Nat → Nat → List AnnotTerm × RecFn) (a : V) : RecFn := (fd (sC a) (sJ a)).2

private def tlOf (r : RecFn) (l : Nat) : List (Nat × Nat × AnnotTerm) := ((r l).map (·.1)).getD []
private def mOf (r : RecFn) (l : Nat) : Nat := ((r l).map (·.2.1)).getD 0
private def esOf (r : RecFn) (l : Nat) : List AnnotTerm := ((r l).map (·.2.2)).getD []

private noncomputable def spineAt (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) (fd : Nat → Nat → List AnnotTerm × RecFn) (a : V) (l : Nat) : V :=
  towerSet (D.w ψ) (teleOfFields (consList ((sF D ψ a).take l) (D.frame ψ ρp X₀))
    ((tlOf (sR fd a) l).map (·.2.2)))

/-- **The positions**: the recursive fields' telescope spines, tagged. -/
private noncomputable def posns (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) (fd : Nat → Nat → List AnnotTerm × RecFn) (a : V) : V :=
  sigmaPairs (sep omega fun q => ∃ l, l < nF D ψ (sC a) (sJ a) ∧ isR (sR fd a) l = true ∧
      q = vnat l)
    fun q => spineAt D ψ ρp fd a (natIdx q)

private noncomputable def pL (p : V) : Nat := natIdx (sfst p)
private noncomputable def pS (fd : Nat → Nat → List AnnotTerm × RecFn) (a p : V) : List V :=
  projList (tlOf (sR fd a) (pL p)).length (ssnd p)

private noncomputable def tgtM (fd : Nat → Nat → List AnnotTerm × RecFn) (a p : V) : Nat := mOf (sR fd a) (pL p)

private noncomputable def tgtI (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) (fd : Nat → Nat → List AnnotTerm × RecFn) (a p : V) : V :=
  tupW (D.u (tgtM fd a p) ψ) ((esOf (sR fd a) (pL p)).map
    (interp V (consList ((sF D ψ a).take (pL p) ++ pS fd a p) (D.frame ψ ρp X₀))))

/-- **The builder**: the shadow's ordinary values, the function on
positions curried into the recursive slots. -/
private noncomputable def mkS (D : LfpDatum V) (ψ : Name → Nat) (ρp : Nat → V) (fd : Nat → Nat → List AnnotTerm × RecFn) (_c : Nat) (a g : V) : V :=
  ConLeche.SetTheory.Tower.inj (sJ a) (mkTower (((List.range (nF D ψ (sC a) (sJ a))).map fun l =>
    if isR (sR fd a) l then
      lamTower (D.w ψ) (consList ((sF D ψ a).take l) (D.frame ψ ρp X₀)) (tlOf (sR fd a) l)
        fun σ => app g (kpair (vnat l) (mkTower (frameIdx (tlOf (sR fd a) l).length σ)))
    else (sF D ψ a).getD l pt) ++ [pt]))

variable {D : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V}
  {fd : Nat → Nat → List AnnotTerm × (Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm))}

private theorem shape_read {c j : Nat} {fs : List V}
    (hlen : fs.length = nF D ψ c j) :
    sC (shapeOf fd c j fs) = c ∧ sJ (shapeOf fd c j fs) = j ∧
      sF D ψ (shapeOf fd c j fs) = shGo (fd c j).2 0 fs ∧ sR fd (shapeOf fd c j fs) = (fd c j).2 := by
  have h1 : sC (shapeOf fd c j fs) = c := by
    unfold sC shapeOf; rw [ConLeche.SetTheory.Tower.sfst_inj, natIdx_vnat]
  have h2 : sJ (shapeOf fd c j fs) = j := by
    unfold sJ shapeOf; rw [ConLeche.SetTheory.Tower.ssnd_inj, ConLeche.SetTheory.Tower.sfst_inj, natIdx_vnat]
  refine ⟨h1, h2, ?_, by unfold sR; rw [h1, h2]⟩
  unfold sF
  rw [h1, h2]
  unfold shapeOf
  rw [ConLeche.SetTheory.Tower.ssnd_inj, ConLeche.SetTheory.Tower.ssnd_inj, ConLeche.SetTheory.Tower.projList_mkTower _ _ (by rw [shGo_length, hlen])]

private theorem mem_shapes {c : Nat} {t a : V} (ha : a ∈ˢ shapes D ψ ρp fd c t) :
    ∃ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X ∧ ∃ j fs, D.HFits ψ ρp X t c j fs ∧
      a = shapeOf fd c j fs := (mem_sep.mp ha).2

private theorem rec_some {r : RecFn} {l : Nat} (h : isR r l = true) :
    ∃ tl m es, r l = some (tl, m, es) := by
  unfold isR at h
  cases hr : r l with
  | none => rw [hr] at h; exact nomatch h
  | some x => exact ⟨x.1, x.2.1, x.2.2, rfl⟩

end Container


/-! ## The container's obligations -/

section Obligations

variable {D : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V}
  {fd : Nat → Nat → List AnnotTerm × (Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm))}
  (hw : D.w ψ ≠ 0) (hok : D.HoleTmOk ψ ρp)
  (hfd : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.FlatAt ψ ρp c j (fd c j).1 (fd c j).2)

include hfd in
/-- The witness behind a shape. -/
private theorem shape_wit {c : Nat} (hc : c < D.N) {t a : V} (ha : a ∈ˢ shapes D ψ ρp fd c t) :
    ∃ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X ∧ ∃ j fs, D.HFits ψ ρp X t c j fs ∧
      D.FlatAt ψ ρp c j (fd c j).1 (fd c j).2 ∧
      fs.length = nF D ψ c j ∧ sC a = c ∧ sJ a = j ∧ sF D ψ a = shGo (fd c j).2 0 fs ∧
      sR fd a = (fd c j).2 := by
  obtain ⟨X, hX, j, fs, hH, rfl⟩ := mem_shapes ha
  have hlen : fs.length = nF D ψ c j := hH.2.1.length_eq
  obtain ⟨h1, h2, h3, h4⟩ := shape_read (fd := fd) hlen
  exact ⟨X, hX, j, fs, hH, hfd c hc j hH.1, hlen, h1, h2, h3, h4⟩

include hw hok in
/-- A recursive field's value, at a witness, is a member of the nested
product, and of the universe. -/
private theorem rec_val {c j : Nat} {fas : List AnnotTerm}
    {r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)}
    (hF : D.FlatAt ψ ρp c j fas r) {X : Nat → V} (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X)
    {fs : List V} (hfs : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs) {l : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {m : Nat} {es : List AnnotTerm}
    (hrl : r l = some (tl, m, es)) :
    fs.getD l pt ∈ˢ piTele (D.w ψ) (teleOfFields (consList (fs.take l) (D.frame ψ ρp X)) (tl.map (·.2.2)))
          (fun bs => app (X m) (tupW (D.u m ψ)
            (es.map (interp V (consList (fs.take l ++ bs) (D.frame ψ ρp X)))))) [] ∧
      fs.getD l pt ∈ˢ (univ (D.w ψ) : V) := by
  have hl : l < (D.fields ψ c j).length := (hF.2.2.1 l tl m es hrl).1
  have hmem := ConLeche.Semantics.FixKI.spineFit_getD_mem' hfs hl
  have hU := hF.2.2.2.2.2.2 X hX l hl _ (spineFit_take' hfs l)
  refine ⟨?_, (univ_isTGUniverse hw).transitive hU hmem⟩
  rw [← rec_read hw hok hF hX hfs hrl]
  exact hmem

include hw hok in
/-- The shadow telescope of a recursive field is bounded, at a witness. -/
private theorem rec_bound {c j : Nat} {fas : List AnnotTerm}
    {r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)}
    (hF : D.FlatAt ψ ρp c j fas r) {X : Nat → V} (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X)
    {fs : List V} (hfs : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs) {l : Nat}
    {tl : List (Nat × Nat × AnnotTerm)} {m : Nat} {es : List AnnotTerm}
    (hrl : r l = some (tl, m, es)) :
    BoundS (D.w ψ) (teleOfFields (consList ((shGo r 0 fs).take l) (D.frame ψ ρp X₀)) (tl.map (·.2.2))) := by
  rw [shGo_take, ← rec_tele hF hfs hrl]
  obtain ⟨h1, h2⟩ := rec_val hw hok hF hX hfs hrl
  exact boundS_of_piTele hw h1 h2

private theorem tlOf_some {r : Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)}
    {l : Nat} {tl : List (Nat × Nat × AnnotTerm)} {m : Nat} {es : List AnnotTerm}
    (h : r l = some (tl, m, es)) : tlOf r l = tl ∧ mOf r l = m ∧ esOf r l = es := by
  simp [tlOf, mOf, esOf, h]

/-- Decoding a position. -/
private theorem mem_posns {a p : V} (hp : p ∈ˢ posns D ψ ρp fd a) :
    ∃ l, l < nF D ψ (sC a) (sJ a) ∧ isR (sR fd a) l = true ∧ ∃ s, s ∈ˢ spineAt D ψ ρp fd a l ∧
      p = kpair (vnat l) s ∧ pL p = l ∧
      pS fd a p = projList (tlOf (sR fd a) l).length s := by
  obtain ⟨q, hq, s, hs, rfl⟩ := mem_sigmaPairs.mp hp
  obtain ⟨-, l, hl, hr, rfl⟩ := mem_sep.mp hq
  rw [natIdx_vnat] at hs
  have hpL : pL (kpair (vnat l) s : V) = l := by unfold pL; rw [sfst_kpair, natIdx_vnat]
  refine ⟨l, hl, hr, s, hs, rfl, hpL, ?_⟩
  unfold pS; rw [hpL, ssnd_kpair]

include hw in
private theorem ob_hA (c : Nat) (t : V) :
    shapes D ψ ρp fd c t ∈ˢ (univ (D.w ψ) : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  have hS : ConLeche.SetTheory.Tower.sumSet (D.w ψ) (fam D ψ ρp fd c) ∈ˢ (univ (D.w ψ) : V) :=
    ConLeche.SetTheory.Tower.sumSet_mem_univ hw fun j => by
      unfold fam; split
      · exact ConLeche.SetTheory.Tower.towerSet_mem_univ _ (boundS_shTele _ _ _ _ _ _ _ _)
      · exact empty_mem_univ _
  exact univ_sep_mem (hU.image_mem hS fun x hx => inj_mem_univ' hw c (hU.transitive hS hx))

include hw hok hfd in
private theorem ob_hB {c : Nat} (hc : c < D.N) {t a : V} (ha : a ∈ˢ shapes D ψ ρp fd c t) :
    posns D ψ ρp fd a ∈ˢ (univ (D.w ψ) : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  obtain ⟨w', hw'⟩ : ∃ w', D.w ψ = w' + 1 := ⟨D.w ψ - 1, by omega⟩
  refine hU.sigmaPairs_mem (univ_sep_mem (by rw [hw']; exact omega_mem_univ_succ w'))
    fun q hq => ?_
  obtain ⟨-, l, -, hr, rfl⟩ := mem_sep.mp hq
  rw [natIdx_vnat]
  obtain ⟨X, hX, j, fs, hH, hF, -, -, -, hsF, hsR⟩ := shape_wit hfd hc ha
  rw [hsR] at hr
  obtain ⟨tl, m, es, hrl⟩ := rec_some hr
  unfold spineAt
  rw [hsF, hsR, (tlOf_some hrl).1]
  exact ConLeche.SetTheory.Tower.towerSet_mem_univ _ (rec_bound hw hok hF hX hH.2.1 hrl)

include hw hfd in
private theorem ob_htgt (hkN : D.k ≤ D.N) {c : Nat} (hc : c < D.N) {t a p : V}
    (ha : a ∈ˢ shapes D ψ ρp fd c t) (hp : p ∈ˢ posns D ψ ρp fd a) :
    tgtM fd a p < D.N ∧ tgtI D ψ ρp fd a p ∈ˢ D.idx ψ ρp (tgtM fd a p) := by
  obtain ⟨l, -, hr, s, hs, rfl, hpL, hpS⟩ := mem_posns hp
  obtain ⟨X, hX, j, fs, hH, hF, -, -, -, hsF, hsR⟩ := shape_wit hfd hc ha
  rw [hsR] at hr hpS
  obtain ⟨tl, m, es, hrl⟩ := rec_some hr
  obtain ⟨htl, hm, hes⟩ := tlOf_some hrl
  have hfs := hH.2.1
  have hM : tgtM fd a (kpair (vnat l) s) = m := by
    unfold tgtM; rw [hsR, hpL, hm]
  have hmk : m < D.k := (hF.2.2.1 l tl m es hrl).2.1
  refine ⟨by rw [hM]; omega, ?_⟩
  unfold spineAt at hs
  rw [hsF, hsR, htl, shGo_take, ← rec_tele hF hfs hrl] at hs
  obtain ⟨hsp, -⟩ := towerSet_elim_teleOfFields hw hs
  rw [List.length_map] at hsp
  unfold tgtI
  rw [hM, hsR, hpL, hes, hpS, htl, hsF, shGo_take,
    ← rec_es hF hfs hrl (by simp [ConLeche.SetTheory.Tower.projList_length])]
  exact tupW_mem (hF.2.2.2.2.2.1 X hX l tl m es hrl _ (spineFit_take' hfs l) _ hsp)

include hw hok hfd in
private theorem ob_hmkU {c : Nat} (hc : c < D.N) {t a g : V} (ha : a ∈ˢ shapes D ψ ρp fd c t)
    (hg : g ∈ˢ (univ (D.w ψ) : V)) : mkS D ψ ρp fd c a g ∈ˢ (univ (D.w ψ) : V) := by
  have hU := univ_isTGUniverse (V := V) hw
  obtain ⟨X, hX, j, fs, hH, hF, hlen, hsC, hsJ, hsF, hsR⟩ := shape_wit hfd hc ha
  have hfs := hH.2.1
  unfold mkS
  rw [hsC, hsJ, hsF, hsR]
  refine inj_mem_univ' hw j (mkTower_mem_univ' hw fun x hx => ?_)
  rcases List.mem_append.mp hx with hx | hx
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    have hl' : l < (D.fields ψ c j).length := List.mem_range.mp hl
    by_cases hr : isR (fd c j).2 l = true
    · rw [if_pos hr]
      obtain ⟨tl, m, es, hrl⟩ := rec_some hr
      rw [(tlOf_some hrl).1]
      exact lamTower_mem_univ' hw (rec_bound hw hok hF hX hfs hrl) fun _ _ => app_mem_univ' hw hg
    · have hr' : isR (fd c j).2 l = false := by simpa using hr
      rw [if_neg hr, shGo_getD, Nat.zero_add, hr']
      exact hU.transitive (hF.2.2.2.2.2.2 X hX l hl' _ (spineFit_take' hfs l))
        (ConLeche.Semantics.FixKI.spineFit_getD_mem' hfs hl')
  · rw [List.mem_singleton.mp hx]
    exact hU.pt_mem (empty_mem_univ _)

include hw hok hfd in
private theorem ob_helim (Φ : (Nat → V) → Nat → V)
    (hfib : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x, x ∈ˢ app (Φ X c) t →
        ∃ j fs, D.HFits ψ ρp X t c j fs ∧ x = ConLeche.SetTheory.Tower.inj j (mkTower (fs ++ [pt])))
    {X : Nat → V} (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) {c : Nat} (hc : c < D.N)
    {t : V} (ht : t ∈ˢ D.idx ψ ρp c) {x : V} (hx : x ∈ˢ app (Φ X c) t) :
    ∃ a, a ∈ˢ shapes D ψ ρp fd c t ∧ ∃ g, g ∈ˢ piSet (posns D ψ ρp fd a)
        (fun p => app (X (tgtM fd a p)) (tgtI D ψ ρp fd a p)) ∧
      x = mkS D ψ ρp fd c a g := by
  obtain ⟨j, fs, hH, rfl⟩ := hfib X hX c hc t ht x hx
  have hF := hfd c hc j hH.1
  have hfs := hH.2.1
  have hlen : fs.length = nF D ψ c j := hfs.length_eq
  obtain ⟨hsC, hsJ, hsF, hsR⟩ := shape_read (fd := fd) hlen
  have ha : shapeOf fd c j fs ∈ˢ shapes D ψ ρp fd c t := by
    refine mem_sep.mpr ⟨mem_image.mpr ⟨_, ConLeche.SetTheory.Tower.inj_mem hw ?_, rfl⟩,
      X, hX, j, fs, hH, rfl⟩
    unfold fam; rw [if_pos hH.1]
    exact ConLeche.SetTheory.Tower.mkTower_mem hw (shadow_fits hF hX hfs)
  -- the spine of a position fits the field's telescope at the hole frame
  have hspine : ∀ {l : Nat} {tl : List (Nat × Nat × AnnotTerm)} {m : Nat} {es : List AnnotTerm},
      (fd c j).2 l = some (tl, m, es) → ∀ {s : V},
      s ∈ˢ spineAt D ψ ρp fd (shapeOf fd c j fs) l ↔
        s ∈ˢ towerSet (D.w ψ) (teleOfFields (consList (fs.take l) (D.frame ψ ρp X)) (tl.map (·.2.2))) := by
    intro l tl m es hrl s
    unfold spineAt
    rw [hsF, hsR, (tlOf_some hrl).1, shGo_take, ← rec_tele hF hfs hrl]
  refine ⟨_, ha, graph (fun p => (pS fd (shapeOf fd c j fs) p).foldl app (fs.getD (pL p) pt))
    (posns D ψ ρp fd (shapeOf fd c j fs)), graph_mem_piSet fun p hp => ?_, ?_⟩
  · obtain ⟨l, -, hr, s, hs, rfl, hpL, hpS⟩ := mem_posns hp
    rw [hsR] at hr hpS
    obtain ⟨tl, m, es, hrl⟩ := rec_some hr
    obtain ⟨htl, hm, hes⟩ := tlOf_some hrl
    rw [hspine hrl] at hs
    obtain ⟨hsp, -⟩ := towerSet_elim_teleOfFields hw hs
    rw [List.length_map] at hsp
    have hM : tgtM fd (shapeOf fd c j fs) (kpair (vnat l) s) = m := by
      unfold tgtM; rw [hsR, hpL, hm]
    have hfold := piTele_fold hw (rec_val hw hok hF hX hfs hrl).1 (fitsS_teleOfFields.mpr hsp)
    rw [List.nil_append] at hfold
    show _ ∈ˢ app (X (tgtM fd (shapeOf fd c j fs) (kpair (vnat l) s)))
      (tgtI D ψ ρp fd (shapeOf fd c j fs) (kpair (vnat l) s))
    unfold tgtI
    rw [hM, hsR, hpL, hes, hpS, htl, hsF, shGo_take,
      ← rec_es hF hfs hrl (by simp [ConLeche.SetTheory.Tower.projList_length])]
    exact hfold
  · unfold mkS
    rw [hsC, hsJ, hsF, hsR]
    congr 2
    refine congrArg (· ++ [pt]) (List.ext_getElem (by simp [nF, hlen]) fun n h1 h2 => ?_)
    rw [List.getElem_map, List.getElem_range]
    have hn : n < (D.fields ψ c j).length := by rw [← hfs.length_eq]; exact h1
    have hget : fs[n] = fs.getD n pt := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
    rw [hget]
    by_cases hr : isR (fd c j).2 n = true
    · rw [if_pos hr]
      obtain ⟨tl, m, es, hrl⟩ := rec_some hr
      rw [(tlOf_some hrl).1]
      obtain ⟨hf, -⟩ := rec_val hw hok hF hX hfs hrl
      symm
      rw [shGo_take]
      refine (lamTower_congr_frame tl (fun q dd bs hdd hbs =>
        (rec_entry hF hfs hrl q dd bs hdd hbs).symm) fun bs hbs => ?_).trans
        ((lamTower_congr_leaves fun bs hbs => ?_).trans (piTele_eta' hw hf))
      · rw [← hbs, frameIdx_consList', frameIdx_consList']
      · have hbl : bs.length = tl.length := by rw [hbs.length_eq, List.length_map]
        rw [← hbl, frameIdx_consList']
        have hmem : kpair (vnat n) (mkTower bs) ∈ˢ posns D ψ ρp fd (shapeOf fd c j fs) := by
          refine mem_sigmaPairs.mpr ⟨vnat n, mem_sep.mpr ⟨vnat_mem_omega n, n,
            by rw [hsC, hsJ]; exact hn, by rw [hsR]; exact hr, rfl⟩, mkTower bs, ?_, rfl⟩
          rw [natIdx_vnat, hspine hrl]
          exact ConLeche.SetTheory.Tower.mkTower_mem hw (fitsS_teleOfFields.mpr hbs)
        rw [app_graph hmem]
        have hpL : pL (kpair (vnat n) (mkTower bs) : V) = n := by
          unfold pL; rw [sfst_kpair, natIdx_vnat]
        have hpS : pS fd (shapeOf fd c j fs) (kpair (vnat n) (mkTower bs)) = bs := by
          unfold pS
          rw [hpL, ssnd_kpair, hsR, (tlOf_some hrl).1, ← hbl,
            ConLeche.SetTheory.Tower.projList_mkTower _ _ rfl]
        rw [hpS, hpL]
    · have hr' : isR (fd c j).2 n = false := by simpa using hr
      rw [if_neg hr, shGo_getD, Nat.zero_add, hr']
      rfl

end Obligations

/-- **(W) for an operator whose fibre is the hole fit of flat fields**
(see the module docstring): at a `Type`-valued block, an operator every
element of whose fibre is the injection of a spine hole-fitting one of
the component's constructors has a closed tuple, when every
constructor's fields with holes are presented flat. -/
theorem closed_of_flat {D : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V} (hw : D.w ψ ≠ 0)
    (hkN : D.k ≤ D.N) (hok : D.HoleTmOk ψ ρp) (Φ : (Nat → V) → Nat → V)
    (hfib : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x, x ∈ˢ app (Φ X c) t →
        ∃ j fs, D.HFits ψ ρp X t c j fs ∧ x = ConLeche.SetTheory.Tower.inj j (mkTower (fs ++ [pt])))
    (hflat : ∀ c, c < D.N → ∀ j, j < D.nctors c → ∃ fas rec, D.FlatAt ψ ρp c j fas rec) :
    ∃ L, IsClosedTuple (D.w ψ) D.N (D.idx ψ ρp) Φ L := by
  classical
  let fd : Nat → Nat → List AnnotTerm ×
      (Nat → Option (List (Nat × Nat × AnnotTerm) × Nat × List AnnotTerm)) := fun c j =>
    if h : ∃ fas rec, D.FlatAt ψ ρp c j fas rec then (h.choose, h.choose_spec.choose)
    else ([], fun _ => none)
  have hfd : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.FlatAt ψ ρp c j (fd c j).1 (fd c j).2 := by
    intro c hc j hj
    have h := hflat c hc j hj
    have hfd' : fd c j = (h.choose, h.choose_spec.choose) := by simp only [fd]; exact dif_pos h
    rw [hfd']
    exact h.choose_spec.choose_spec
  exact tupleContainer_closed_exists hw (Is := D.idx ψ ρp) Φ (shapes D ψ ρp fd)
    (posns D ψ ρp fd) (tgtM fd) (tgtI D ψ ρp fd) (mkS D ψ ρp fd)
    (fun m _ i _ => ob_hA hw m i)
    (fun _ hm _ _ _ ha => ob_hB hw hok hfd hm ha)
    (fun _ hm _ _ _ _ ha hp => ob_htgt hw hfd hkN hm ha hp)
    (fun _ hm _ _ _ _ ha hg => ob_hmkU hw hok hfd hm ha hg)
    (fun _ hX _ hm _ hi _ hx => ob_helim hw hok hfd Φ hfib hX hm hi hx)

end LfpDatum

end ConLeche.Model
