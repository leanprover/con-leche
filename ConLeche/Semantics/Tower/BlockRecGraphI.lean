module

public import ConLeche.Semantics.Tower.BlockRecI
public import ConLeche.SetModel.GraphRec
import ConLeche.Semantics.Tower.FixLeafI
@[expose] public section

/-!
# The recursor family's candidate from the GRAPH kit (lane GRAPH1)

DESIGN, ruling of 2026-09-23: the recursor model is the graph route.
A checked recursor family is the selector of its GRAPH — the least
relation closed under its rules read as closure conditions over
DECODINGS of the majors (`GraphRecKit`, `SetModel/GraphRec.lean`) —
and the graph is functional by ONE induction over the majors plus
`huniq` (decodings equal, or the bound a subsingleton).  That replaces
the three regimes (IND at `ℓ = 0`, WF at `w ≠ 0`, SQ at `w = 0`) and
their dispatch: the family's candidate is ONE λ-tower whose body is
the kit's recursor, at EVERY level.

**Classes are the stream's recursors**, as in the retired kit arm: the
majors are tagged by the recursor class `c`, with the class's own
index sets and ORDINARY carriers per prefix spine (`GraphFamData`).

**At `ℓ = 0`** the tower is the point and so is every value of the
graph (its bound is a truth value), which is why `famCandG_fold` needs
no level split at its consumers: both sides are the point.

**What the Model tier owes** (`famCandG_hCand`): that a rule's spine
FITS the recursor's type (`hrule`); that the rule's own fields are a
DECODING of the constructed major (`hdec` — the rule reads the
constructor it is keyed by, at any sort); and that the kit's step at
that decoding, with the `ih`s read off the recursor over its
predecessors, IS the residue at the `ih` terms' values (`hst`).  The ι
law is then `GraphRecKit.rec_eq` at THAT decoding: no decoding is
ever chosen.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-! ## The recursor's spine, decomposed

A fitting spine of `rec_c`'s type is `x⃗ ++ ı⃗ ++ [t]`: the rule prefix
(`rP c` binders — record-read, PER RECURSOR), the class's indices, the
major. -/

/-- The rule prefix of a spine. -/
def prefOf (rP : Nat) (ys : List V) : List V := ys.take rP

/-- The index values of a spine. -/
def idxOf (rP : Nat) (ys : List V) : List V := (ys.drop rP).dropLast

/-- The major of a spine. -/
noncomputable def majOf (ys : List V) : V := ys.reverse.headD pt

omit [SetTheory V] in
@[simp] theorem prefOf_split {rP : Nat} {xs is : List V} {t : V} (hx : xs.length = rP) :
    prefOf rP (xs ++ (is ++ [t])) = xs := by
  rw [prefOf, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

omit [SetTheory V] in
@[simp] theorem idxOf_split {rP : Nat} {xs is : List V} {t : V} (hx : xs.length = rP) :
    idxOf rP (xs ++ (is ++ [t])) = is := by
  rw [idxOf, List.drop_append_of_le_length (by omega),
    List.drop_of_length_le (by omega), List.nil_append, List.dropLast_concat]

@[simp] theorem majOf_split {xs is : List V} {t : V} :
    majOf (xs ++ (is ++ [t])) = t := by
  simp [majOf]

/-- **The recursion data of a recursor family over the graph kit**, at
the base frame `ρ`: per PREFIX SPINE a `GraphRecKit` over the tagged
union of the classes' ORDINARY carriers, with decodings in `R`, and the
two readings the recursors' TYPES fix. -/
structure GraphFamData (V : Type uv) [SetTheory V] (ℓ K : Nat) (rP : Nat → Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (concl : Nat → AnnotTerm) (ρ : Nat → V)
    (R : Type uv) where
  /-- The classes' index sets, at a prefix frame. -/
  Is : List V → Nat → V
  /-- The classes' ORDINARY carriers. -/
  Cr : List V → Nat → V
  /-- The index TUPLE of a class's index spine. -/
  tupOf : Nat → List V → V
  /-- The kit, one per prefix spine. -/
  kit : ∀ xs : List V, GraphRecKit ℓ (unionSet K (Is xs) (Cr xs)) R
  /-- A fitting spine of `rec_c`'s type is `x⃗ ++ ı⃗ ++ [t]`, a major of
  class `c`. -/
  hsplit : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (prefOf (rP c) ys).length = rP c ∧
    ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
    tupOf c (idxOf (rP c) ys) ∈ˢ Is (prefOf (rP c) ys) c ∧
    majOf ys ∈ˢ app (Cr (prefOf (rP c) ys) c) (tupOf c (idxOf (rP c) ys))
  /-- The conclusion reads to the kit's bound at the tagged major. -/
  hconcl : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (kit (prefOf (rP c) ys)).B (tagged c (tupOf c (idxOf (rP c) ys)) (majOf ys))
      = interp V (consList ys ρ) (concl c)

section Cand

variable {ℓ K : Nat} {rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {concl : Nat → AnnotTerm} {ρ : Nat → V} {R : Type uv}

/-- **The candidate at class `c`**: the λ-tower over the recursor
type's binder data whose body is the kit's recursor at the tagged
major the spine names. -/
noncomputable def famCandG (D : GraphFamData V ℓ K rP rds concl ρ R) (c : Nat) : V :=
  lamTowerA ℓ ρ [] (rds c) fun ys _ =>
    (D.kit (prefOf (rP c) ys)).recAt (tagged c (D.tupOf c (idxOf (rP c) ys)) (majOf ys))

/-- A fitting spine's tagged major is a major of the kit. -/
theorem GraphFamData.mem_union (D : GraphFamData V ℓ K rP rds concl ρ R) {c : Nat}
    (hc : c < K) {ys : List V} (hsp : SpineFit ρ ((rds c).map (·.2.2)) ys) :
    tagged c (D.tupOf c (idxOf (rP c) ys)) (majOf ys)
      ∈ˢ unionSet K (D.Is (prefOf (rP c) ys)) (D.Cr (prefOf (rP c) ys)) := by
  obtain ⟨-, -, hi, hx⟩ := D.hsplit c hc ys hsp
  exact tagged_mem_unionSet hc hi hx

/-- **`mem_type` of the candidate**, at every level: the kit's
recursor lies in its bound, which is the conclusion's reading; at
`ℓ = 0` that reading is a truth value because the bound is a set of
level `0`. -/
theorem famCandG_mem (D : GraphFamData V ℓ K rP rds concl ρ R) {c : Nat} (hc : c < K)
    (hbits : ∀ d ∈ rds c, (ℓ = 0 ↔ d.2.1 = 0)) :
    famCandG D c ∈ˢ interp V ρ (mkPisAV (rds c) (concl c)) := by
  refine lamTowerA_mem hbits (towerWalkA_of_spines_body fun ys hsp => ?_)
  have hu := D.mem_union hc hsp
  have hB := (D.kit (prefOf (rP c) ys)).hB _ hu
  rw [D.hconcl c hc ys hsp] at hB
  refine ⟨?_, fun h0 => ?_⟩
  · have hmem := (D.kit (prefOf (rP c) ys)).rec_mem_B hu
    rw [D.hconcl c hc ys hsp] at hmem
    simpa using hmem
  · subst h0
    rwa [univ_zero] at hB

/-- **The candidate folds to the kit's recursor** along a fitting spine
`x⃗ ++ ı⃗ ++ [t]` — at EVERY level.  Above `Prop` it is the tower's
fold; at `ℓ = 0` both sides are the point (the tower is `lamR 0 …`,
the recursor lies in a truth value). -/
theorem famCandG_fold (D : GraphFamData V ℓ K rP rds concl ρ R) {c : Nat} (hc : c < K)
    {xs is : List V} {t : V} (hx : xs.length = rP c)
    (hsp : SpineFit ρ ((rds c).map (·.2.2)) (xs ++ (is ++ [t]))) :
    (xs ++ (is ++ [t])).foldl SetTheory.app (famCandG D c)
      = (D.kit xs).recAt (tagged c (D.tupOf c is) t) := by
  by_cases hℓ : ℓ = 0
  · subst hℓ
    have hu := D.mem_union hc hsp
    rw [prefOf_split hx, idxOf_split hx, majOf_split] at hu
    have hB := (D.kit xs).hB _ hu
    rw [univ_zero] at hB
    rw [eq_pt_of_mem_univZero hB ((D.kit xs).rec_mem_B hu)]
    obtain ⟨dd, ds, hrds⟩ : ∃ dd ds, rds c = dd :: ds := by
      cases h : rds c with
      | nil =>
        have hl := hsp.length_eq
        rw [h] at hl
        simp at hl
      | cons dd ds => exact ⟨dd, ds, rfl⟩
    rw [famCandG, hrds]
    show (xs ++ (is ++ [t])).foldl SetTheory.app (lamR 0 _ _) = _
    rw [lamR_zero]
    exact foldl_app_pt' _
  · rw [famCandG, lamTowerA_fold hℓ hsp]
    simp only [List.nil_append]
    rw [prefOf_split hx, idxOf_split hx, majOf_split]

variable {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm}

/-- **THE CANDIDATE, from the graph kit** — the ONE producer of
`BlockRecPre.hCand`, at every level (DESIGN, ruling of 2026-09-23).

* `hrule`: a rule's own spine (the prefix, the constructor's index
  expressions, the constructed major) FITS the recursor's type;
* `hdec`: the rule's fields, keyed by the rule, are a DECODING
  (`dOf`) of that major;
* `hst`: the kit's step at that decoding, the `ih`s read off the
  recursor over the decoding's predecessors, IS the residue at the
  `ih` terms' values.

The ι law is `GraphRecKit.rec_eq` at the rule's own decoding. -/
theorem famCandG_hCand (D : GraphFamData V ℓ K rP rds concl ρ R)
    (dOf : List V → Nat → Nat → List V → R)
    (hTy : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ K rds)
    (hpl : ∀ c, c < K → (pdoms c).length = rP c)
    (hrule : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCandG D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)) (mk c j)])))
    (hdec : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCandG D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (D.kit xs).Dec
        (tagged c
          (D.tupOf c ((es c j).map
            (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)))))
          (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)) (mk c j)))
        (dOf xs c j fs))
    (hst : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCandG D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (D.kit xs).st (dOf xs c j fs)
          (graph (fun v => (D.kit xs).recAt v) ((D.kit xs).pred (dOf xs c j fs)))
        = interp V
            (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ))))
              (consList (xs ++ fs) (chainFrame K (famCandG D) ρ))) (Rb c j)) :
    ∃ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        (pt : V) ∈ˢ interp V (chainFrame K a ρ) e := by
  refine hCand_iotaEqsAV_of (famCandG D) (fun c hc => ?_) fun c hc j hj xs fs hxl hsp => ?_
  · rw [hTy c hc]
    exact famCandG_mem D hc (hbits c hc)
  · have hxr : xs.length = rP c := by rw [hxl, hpl c hc]
    have hfit := hrule c hc j hj xs fs hxl hsp
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [famCandG_fold D hc hxr hfit]
    have hu := D.mem_union hc hfit
    rw [prefOf_split hxr, idxOf_split hxr, majOf_split] at hu
    rw [(D.kit xs).rec_eq hu (hdec c hc j hj xs fs hxl hsp)]
    exact hst c hc j hj xs fs hxl hsp

end Cand

end ConLeche.Semantics
