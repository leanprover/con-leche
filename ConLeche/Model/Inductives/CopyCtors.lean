module

public import ConLeche.Model.Inductives.PsiSetup
public import ConLeche.Model.Inductives.CopyPins
public section

/-!
# The copies' CONSTRUCTORS, as the fold `ψ` reads them (task #279 M-B′ step 3j)

DESIGN §M.25 (c) states what the model consumes of a copy's constructor:
its stored type reads as the container constructor's stored type
instantiated at the pin's annotated components, with every nested
occurrence in a field domain replaced by the copy the walk minted for
it — "`CopyCtorRead`'s `dsC`/`bodyC` are the readings of the REWRITTEN
instantiated constructor, field by field".  This module states that
sentence ONCE, in the vocabulary of the two data the folds run over —
the AUXILIARY datum `d` (the copy's constructor as the scratch block
stored it) and the CONTAINER datum `dJ` (the container's constructor as
the pre-block environment stored it) — as the record
`CopyCtorAsRead`: field by field, the copy's reading is the container's
reading with the container's parameter variables SUBSTITUTED by the
pin's readings (`AnnotTerm.instSeq`), except at the fields the walk
rewrote, where the container's (substituted) field domain is the
Π-tower over the copy's telescope of the TARGET pin's container at that
pin's readings at the copy's index readings, and the copy's field is
recursive into the target's copy.  Three kinds of field:

* **`kindR`** — a field the CONTAINER already sees as recursive (its
  head a member of the container's own group): the copy's field is
  recursive into the group-mate's copy, its telescope and index readings
  the container's substituted;
* **`kindT`** — a TRANSPORT: a field the container sees as ordinary
  whose domain is a nested occurrence of another container (the walk's
  rewrite): the copy's field is recursive into that occurrence's copy
  (outside the group), and the container's substituted domain IS the
  Π-tower over the copy's telescope of the target container at the
  target pin's readings at the copy's index readings;
* **`ord`** — a field neither sees as recursive: the readings agree
  under the substitution.

The record is a HYPOTHESIS of the assembly until the kernel lane's
constructor-stage identity (DESIGN K.12: the elimination on annotated
inputs) lands, from which it is read the way `CopyTypesAsMinted` is read
off the formers' identity (`copyTypesAsMinted_of_facts`).  The reference
relation the fold recurses along (`CopyRef`, `NestedOrder.lean`) is
bridged at the run level, not here.

The module also carries the transports the assembly needs:
`shiftE_consList_middle` (a lift inserting binders between two frame
segments), `NoBVar_instSeq_iff` (substituting parameters below a cut
touches no field variable), `wellDenotedV_instSeq_under` (grading
crosses a substitution under binders), and `NoBVar_mono`/
`NoBVar_of_pointwise`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Frames: a lift inserting binders in the middle -/

/-- Shifting by `ys.length` at cutoff `xs.length` skips the middle
segment. -/
theorem shiftE_consList_middle (xs ys : List V) (ρ : Nat → V) :
    shiftE ys.length xs.length (consList xs (consList ys ρ)) = consList xs ρ := by
  funext j
  simp only [shiftE]
  split
  · next hj =>
    rw [consList_apply_lt' xs _ hj, consList_apply_lt' xs _ hj]
  · next hj =>
    have h1 := consList_apply_add xs (consList ys ρ) (j + ys.length - xs.length)
    have h2 := consList_apply_add ys ρ (j - xs.length)
    have h3 := consList_apply_add xs ρ (j - xs.length)
    rw [show j + ys.length - xs.length + xs.length = j + ys.length from by omega] at h1
    rw [show j - xs.length + ys.length = j + ys.length - xs.length from by omega] at h2
    rw [show j - xs.length + xs.length = j from by omega] at h3
    rw [h1, h2, h3]

/-- The interpretation of a term lifted over a middle segment. -/
theorem interp_liftN_middle (xs ys : List V) (ρ : Nat → V) (e : AnnotTerm) :
    interp V (consList xs (consList ys ρ)) (e.liftN ys.length xs.length)
      = interp V (consList xs ρ) e := by
  rw [interp_liftN, shiftE_consList_middle]

/-- Grading of a term lifted over a middle segment. -/
theorem WellDenotedV_liftN_middle (xs ys : List V) (ρ : Nat → V) (e : AnnotTerm) :
    WellDenotedV V (consList xs (consList ys ρ)) (e.liftN ys.length xs.length)
      ↔ WellDenotedV V (consList xs ρ) e := by
  rw [WellDenotedV_liftN, shiftE_consList_middle]

/-! ## `NoBVar` across a substitution below a cut -/

omit [SetTheory V] in
/-- Substituting at index `k` touches no variable below `k`: a
predicate on the indices below `k` sees the same variables before and
after. -/
theorem NoBVar_inst_iff (a : AnnotTerm) :
    ∀ (e : AnnotTerm) {k : Nat} {P : Nat → Prop}, (∀ q, P q → q < k) →
      (NoBVar P (e.inst a k) ↔ NoBVar P e)
  | .bvar i, k, P, hP => by
    show NoBVar P (if i < k then .bvar i else if i = k then a.liftN k 0 else .bvar (i - 1)) ↔ ¬ P i
    split
    · exact Iff.rfl
    · next hik =>
      split
      · next hik' =>
        subst hik'
        exact ⟨fun _ h => (Nat.lt_irrefl _ (hP _ h)), fun _ => NoBVar_liftN_zero hP a⟩
      · next hik' =>
        show ¬ P (i - 1) ↔ ¬ P i
        constructor
        · intro _ h; have := hP _ h; omega
        · intro _ h; have := hP _ h; omega
  | .sort _, _, _, _ => Iff.rfl
  | .const _ _, _, _, _ => Iff.rfl
  | .prf, _, _, _ => Iff.rfl
  | .app f b, k, P, hP => by
    show NoBVar P (f.inst a k) ∧ NoBVar P (b.inst a k) ↔ NoBVar P f ∧ NoBVar P b
    rw [NoBVar_inst_iff a f hP, NoBVar_inst_iff a b hP]
  | .lam _ A b, k, P, hP => by
    show NoBVar P (A.inst a k) ∧ NoBVar (shiftP P) (b.inst a (k + 1)) ↔
      NoBVar P A ∧ NoBVar (shiftP P) b
    rw [NoBVar_inst_iff a A hP, NoBVar_inst_iff a b (k := k + 1) (P := shiftP P) fun q hq => by
      cases q with
      | zero => exact hq.elim
      | succ q => have := hP q hq; omega]
  | .pi _ _ A B, k, P, hP => by
    show NoBVar P (A.inst a k) ∧ NoBVar (shiftP P) (B.inst a (k + 1)) ↔
      NoBVar P A ∧ NoBVar (shiftP P) B
    rw [NoBVar_inst_iff a A hP, NoBVar_inst_iff a B (k := k + 1) (P := shiftP P) fun q hq => by
      cases q with
      | zero => exact hq.elim
      | succ q => have := hP q hq; omega]
  | .eqE b c, k, P, hP => by
    show NoBVar P (b.inst a k) ∧ NoBVar P (c.inst a k) ↔ NoBVar P b ∧ NoBVar P c
    rw [NoBVar_inst_iff a b hP, NoBVar_inst_iff a c hP]
  | .fst e, k, P, hP => NoBVar_inst_iff a e hP
  | .snd e, k, P, hP => NoBVar_inst_iff a e hP

omit [SetTheory V] in
/-- **A substitution along a spine below a cut touches no variable
below the last cut**: with `ws.length` arguments at cuts
`t, t - 1, …, t - ws.length + 1`, a predicate on the indices below
`t - ws.length + 1` sees the same variables. -/
theorem NoBVar_instSeq_iff :
    ∀ (ws : List AnnotTerm) (t : Nat) (e : AnnotTerm) {P : Nat → Prop},
      (∀ q, P q → q + ws.length ≤ t) →
      (NoBVar P (ConLeche.Model.AnnotTerm.instSeq ws t e) ↔ NoBVar P e)
  | [], _, _, _, _ => Iff.rfl
  | w :: ws, t, e, P, hP => by
    rw [AnnotTerm.instSeq_cons, NoBVar_instSeq_iff ws (t - 1) (e.inst w t) (fun q hq => by
        have := hP q hq; simp only [List.length_cons] at this; omega),
      NoBVar_inst_iff w e (fun q hq => by have := hP q hq; simp only [List.length_cons] at this; omega)]

/-! ## Grading across a substitution under binders -/

/-- **Grading crosses `instSeq` under binders** (`wellDenotedV_instSeq`
with `xs` binders between the substituted variables and the term): a
term graded at the frame with the arguments' values pushed under `xs`,
substituted along arguments graded at the base frame, is graded at the
frame without them. -/
theorem wellDenotedV_instSeq_under (σ : Nat → V) :
    ∀ (ws : List AnnotTerm) (xs : List V) (t : Nat) (e : AnnotTerm),
      (ws ≠ [] → ws.length + xs.length = t + 1) →
      (∀ w ∈ ws, WellDenotedV V σ w) →
      WellDenotedV V (consList xs (consList (ws.map (interp V σ)) σ)) e →
      WellDenotedV V (consList xs σ) (ConLeche.Model.AnnotTerm.instSeq ws t e)
  | [], xs, t, e, _, _, h => h
  | w :: ws, xs, t, e, hlen, hws, h => by
    have ht : t = ws.length + xs.length := by
      have := hlen (List.cons_ne_nil w ws)
      simp only [List.length_cons] at this
      omega
    have hokw : WellDenotedV V σ w := hws w List.mem_cons_self
    rw [AnnotTerm.instSeq_cons]
    refine wellDenotedV_instSeq_under σ ws xs (t - 1) (e.inst w t)
      (fun hne => by
        have hpos : ws.length ≠ 0 := fun h0 => hne (List.eq_nil_of_length_eq_zero h0)
        omega)
      (fun x hx => hws x (List.mem_cons_of_mem _ hx)) ?_
    have hfr : consList xs (consList (ws.map (interp V σ)) σ)
        = consList (ws.map (interp V σ) ++ xs) σ := (consList_append _ _ _).symm
    have hlenF : (ws.map (interp V σ) ++ xs).length = t := by
      rw [List.length_append, List.length_map, ht]
    have hshift : shiftE t 0 (consList xs (consList (ws.map (interp V σ)) σ)) = σ := by
      rw [hfr, ← hlenF, shiftE_consList]
    have hE : instE t (interp V (shiftE t 0 (consList xs (consList (ws.map (interp V σ)) σ))) w)
        (consList xs (consList (ws.map (interp V σ)) σ))
        = consList xs (consList ((w :: ws).map (interp V σ)) σ) := by
      rw [hshift, hfr, ← hlenF, ← Nat.add_zero (ws.map (interp V σ) ++ xs).length, instE_consList,
        instE_zero_eq_cons, List.map_cons, consList_cons, consList_append]
    refine ⟨?_, ?_⟩
    · rw [WellDenoted_inst V e w t _ (by rw [hshift]; exact hokw.1), hE]
      exact h.1
    · rw [AnnotValid_inst V e w t _ (by rw [hshift]; exact hokw.2), hE]
      exact h.2

omit [SetTheory V] in
/-- `NoBVar` is antitone in the predicate. -/
theorem NoBVar_mono {P Q : Nat → Prop} (h : ∀ j, P j → Q j) :
    ∀ (e : AnnotTerm), NoBVar Q e → NoBVar P e
  | .bvar i, hn => fun hp => hn (h i hp)
  | .sort _, _ => trivial
  | .const _ _, _ => trivial
  | .prf, _ => trivial
  | .app f a, hn => ⟨NoBVar_mono h f hn.1, NoBVar_mono h a hn.2⟩
  | .lam _ A b, hn => ⟨NoBVar_mono h A hn.1, NoBVar_mono (shiftP_mono h) b hn.2⟩
  | .pi _ _ A B, hn => ⟨NoBVar_mono h A hn.1, NoBVar_mono (shiftP_mono h) B hn.2⟩
  | .eqE a b, hn => ⟨NoBVar_mono h a hn.1, NoBVar_mono h b hn.2⟩
  | .fst e, hn => NoBVar_mono h e hn
  | .snd e, hn => NoBVar_mono h e hn

omit [SetTheory V] in
/-- `NoBVar` at a union, from `NoBVar` at each member. -/
theorem NoBVar_of_pointwise :
    ∀ (e : AnnotTerm) {P : Nat → Prop}, (∀ j, P j → NoBVar (· = j) e) → NoBVar P e
  | .bvar i, P, h => fun hp => h i hp rfl
  | .sort _, _, _ => trivial
  | .const _ _, _, _ => trivial
  | .prf, _, _ => trivial
  | .app f a, P, h => ⟨NoBVar_of_pointwise f fun j hj => (h j hj).1,
      NoBVar_of_pointwise a fun j hj => (h j hj).2⟩
  | .lam _ A b, P, h => ⟨NoBVar_of_pointwise A fun j hj => (h j hj).1,
      NoBVar_of_pointwise b fun j hj => by
        cases j with
        | zero => exact hj.elim
        | succ j =>
          refine NoBVar_congr (fun q => ?_) _ (h j hj).2
          cases q with
          | zero => exact ⟨fun h => h.elim, fun h => nomatch h⟩
          | succ q => exact ⟨fun h => by rw [h], fun h => Nat.succ.inj h⟩⟩
  | .pi _ _ A B, P, h => ⟨NoBVar_of_pointwise A fun j hj => (h j hj).1,
      NoBVar_of_pointwise B fun j hj => by
        cases j with
        | zero => exact hj.elim
        | succ j =>
          refine NoBVar_congr (fun q => ?_) _ (h j hj).2
          cases q with
          | zero => exact ⟨fun h => h.elim, fun h => nomatch h⟩
          | succ q => exact ⟨fun h => by rw [h], fun h => Nat.succ.inj h⟩⟩
  | .eqE a b, P, h => ⟨NoBVar_of_pointwise a fun j hj => (h j hj).1,
      NoBVar_of_pointwise b fun j hj => (h j hj).2⟩
  | .fst e, P, h => NoBVar_of_pointwise e h
  | .snd e, P, h => NoBVar_of_pointwise e h

/-! ## The record -/

namespace IndRepData

/-- **Two readings of a copy's field agree at the CONTAINER's field
frame** (DESIGN §M.31, the maintainer's ruling on §M.30 finding 3): at
every frame of the block's parameters (`Sat`) and every spine of `i`
earlier values fitting the CONTAINER constructor's earlier field domains
at the pin's readings (`dJ.dsF Jc ψ'` under `DsA`), the two
interpretations coincide.  The frames carry VALUES — a container field
value at every earlier position, whatever the copy's later reading of
that position is — so the equation covers the erasing shape
`(h : (fun _ : f Nat => Nat) x)` at a λ-pin: the copy's stored domain is
the reduct `Nat` and the container's substituted domain is the redex,
equal wherever `x` is a container value (`WhnfClaim`, K.17's witness).
The copy's own no-mention facts (`noBVar_entries`) carry the equation
from this frame to ψ's transported one (`psiBody_leaf`'s `hord`/`hnbA`). -/
@[expose] def CopyFieldAgree (d : IndRepData V) (ψ : Name → Nat) (dJ : IndRepData V) (ψ' : Name → Nat)
    (DsA : List AnnotTerm) (Jc i : Nat) (A B : AnnotTerm) : Prop :=
  ∀ (σ : Nat → V) (ws : List V), ws.length = i → Sat V (d.params ψ).reverse σ →
    SpineFit (consList (DsA.map (interp V σ)) σ) ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) ws →
    interp V (consList ws σ) A = interp V (consList ws σ) B

/-- **A copy's constructor, read through the container's** (DESIGN
§M.25 (c) in the two data's vocabulary; weakened to the INTERPRETATION
level at §M.30 and restated at the CONTAINER's field frames at §M.31,
so that the positivity normalisation's `whnf` arm — a λ-pin's
`(fun _ => PT α) k ↦ PT α`, four in the Mathlib cone — and the erasing
shape are covered).  `d` is the auxiliary datum (the copy's constructor
`Ja` is its constructor `Ja`, of member `k₀ + j₀ + dJ.mems Jc`: the
block's own `k₀` members, then the copies, the container's group at pins
`j₀ …`), `dJ` the container datum (at the level assignment `ψ'` the pin
names) and `DsA` the pin's readings at the block's parameter frame.
Every container reading is at the frame `DsA` over the block's
parameters; the copy's at the block's parameters alone — `instSeq DsA`
at the container's parameter depth is the bridge.  For a transport
(`kindT`) the target pin `j'` comes with its container's name, level
assignment and readings (`tgtCont`, `tgtLps`, `tgtDsA`).

The kinds of field, by the two classifications:

* **`kindR`** — the CONTAINER sees the field as recursive: the copy's
  field is recursive into the group-mate's copy, its telescope and
  index readings the container's substituted, SYNTACTICALLY (the walk
  fires at the head, whose `whnf` is the identity on an inductive
  application under its own binders);
* **`kindT`** — a TRANSPORT: the container sees the field as ordinary,
  the copy as recursive into a COPY (`k₀ ≤` target): the target is
  outside the group, and the container's substituted domain reads,
  at the container's field frame, as the Π-tower over the copy's
  telescope of the target container at the target pin's readings at
  the copy's index readings, graded there;
* **`ord`** — the container sees the field as ordinary and the copy as
  ordinary OR as recursive into a BLOCK MEMBER (`< k₀`, the λ-pin's
  `(fun _ => PT α) k ↦ PT α`, where the copy's field is the block's own
  member and ψ passes the container's value through): the readings
  agree at the container's field frame.

No syntactic clause about the container's later readings is asked
(§M.30's `nbT` is gone): the copy's readings mention none of the copy's
recursive positions (`noBVar_entries` of the copy, from the auxiliary
install's own positivity check), and that is what ψ's transported
frame needs.

The record is a HYPOTHESIS of the assembly, read off the run field by
field (the identity arm of `nestedCopyCtorType_eq` syntactically, the
`whnf` arm through K.17's witness, DESIGN §M.31). -/
structure CopyCtorAsRead (m : EnvModel V env) (d dJ : IndRepData V) (ψ ψ' : Name → Nat)
    (DsA : List AnnotTerm) (k₀ j₀ : Nat)
    (tgtCont : Nat → Name) (tgtLps : Nat → Name → Nat) (tgtDsA : Nat → List AnnotTerm)
    (Jc Ja nF : Nat) : Prop where
  /-- the copy's constructor belongs to the group-mate's copy -/
  mem : d.mems Ja = k₀ + j₀ + dJ.mems Jc
  /-- a field the container sees as recursive: the copy's field is
  recursive into the group-mate's copy, its telescope and index readings
  the container's substituted -/
  kindR : ∀ i, i ∈ ConLeche.recIdxOf (dJ.ksF Jc) →
    (d.ksR Ja).getD i .ordinary = (dJ.ksF Jc).getD i .ordinary ∧
    d.tgtsR Ja i = k₀ + j₀ + dJ.tgts Jc i ∧
    (d.tssR Ja ψ).getD i [] = instSeqDoms DsA (dJ.nP + i - 1) ((dJ.tssF Jc ψ').getD i []) ∧
    (d.eissR Ja ψ).getD i [] = ((dJ.eissF Jc ψ').getD i []).map
      (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i + ((dJ.tssF Jc ψ').getD i []).length - 1))
  /-- a TRANSPORT: the copy's field is recursive into the copy of a pin
  outside the group, and the container's substituted domain reads, at
  the container's field frame, as the Π-tower over the copy's telescope
  of that pin's container at the pin's readings at the copy's index
  readings, graded there -/
  kindT : ∀ i, i < nF → i ∉ ConLeche.recIdxOf (dJ.ksF Jc) → i ∈ ConLeche.recIdxOf (d.ksR Ja) →
    k₀ ≤ d.tgtsR Ja i →
    ∃ j', d.tgtsR Ja i = k₀ + j' ∧ ¬ (j₀ ≤ j' ∧ j' < j₀ + dJ.k) ∧
      d.CopyFieldAgree ψ dJ ψ' DsA Jc i
        (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1)
          ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2)
        (mkPisAV ((d.tssR Ja ψ).getD i [])
          (AnnotTerm.mkAppN (m.acval (tgtCont j') (tgtLps j'))
            ((tgtDsA j').map (·.liftN (i + ((d.tssR Ja ψ).getD i []).length) 0) ++
              (d.eissR Ja ψ).getD i []))) ∧
      ∀ (σ : Nat → V) (ws : List V), ws.length = i → Sat V (d.params ψ).reverse σ →
        SpineFit (consList (DsA.map (interp V σ)) σ)
          ((((dJ.dsF Jc ψ').drop dJ.nP).take i).map (·.2.2)) ws →
        WellDenotedV V (consList ws σ)
          (mkPisAV ((d.tssR Ja ψ).getD i [])
            (AnnotTerm.mkAppN (m.acval (tgtCont j') (tgtLps j'))
              ((tgtDsA j').map (·.liftN (i + ((d.tssR Ja ψ).getD i []).length) 0) ++
                (d.eissR Ja ψ).getD i [])))
  /-- an ordinary field on the container's side, ordinary or into a
  block member on the copy's: the readings agree at the container's
  field frame -/
  ord : ∀ i, i < nF → i ∉ ConLeche.recIdxOf (dJ.ksF Jc) →
    (i ∉ ConLeche.recIdxOf (d.ksR Ja) ∨ d.tgtsR Ja i < k₀) →
    d.CopyFieldAgree ψ dJ ψ' DsA Jc i ((d.dsF Ja ψ).getD (d.nP + i) default).2.2
      (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + i - 1)
        ((dJ.dsF Jc ψ').getD (dJ.nP + i) default).2.2)
  /-- the result's index readings agree under the substitution (the
  residual is untouched by the normalisation) -/
  es : d.esF Ja ψ = (dJ.esF Jc ψ').map (ConLeche.Model.AnnotTerm.instSeq DsA (dJ.nP + nF - 1))

end IndRepData

end ConLeche.Model
