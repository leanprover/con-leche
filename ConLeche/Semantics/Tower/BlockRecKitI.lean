module

public import ConLeche.Semantics.Tower.BlockRecI
public import ConLeche.SetModel.UnionRec
@[expose] public section

/-!
# The recursor family's candidate from a CLASS KIT (task #315, M5 model half)

DESIGN "DESIGN DOCUMENT 2, v2" §3.2/§3.4.  Two of the three regimes —
WF (`¬allProp ∧ w ≠ 0`) and SQ (`¬allProp ∧ w = 0`) — build the
candidate the same way: a recursion over the tagged union of the
classes' carriers, differing ONLY in what a predecessor is and why the
relation is well-founded.

* WF: predecessors are the ∈-smaller elements (`tcPred`), accessibility
  is regularity — F5's `WfRecKit`;
* SQ: predecessors are the recursive calls' INDEX tuples (`sqPred`),
  accessibility is the block's own lfp induction — `FixSquashI`'s kit.

`UnionRecKitC` (`SetModel/UnionRec.lean`) is exactly their common
interface — `pred`/`B`/`st` with four obligations, giving `recAt`,
`rec_mem_B` and `rec_eq` — so this file states the arm ONCE, over a
`UnionRecKitC`, and each regime is an instantiation.  Nothing here
knows about `tc`, about fixed points, or about the sort.

**Classes are the stream's RECURSORS**, not the block's members: under
the maintainer's naming ruling (2026-09-21) a member may carry any
number of recursors, each assigned to it by its MAJOR's type and each
with its OWN rule prefix.  So `K` counts recursors and `rP : Nat → Nat`
is per class.
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

/-! ## The kit's graph at an index

`rec_eq` reads the recursor's value as the step at the recursor's own
graph over the value's predecessors.  That graph is what a rule's ih
openers are valued in, so it gets a name. -/

/-- The recursor's graph over `u`'s predecessors. -/
noncomputable def kitGraphAt {ℓ k : Nat} {Is C : Nat → V} (Kt : UnionRecKitC ℓ k Is C) (u : V) :
    V :=
  graph (fun j => recSel (recGraph ℓ (unionSet k Is C) Kt.pred Kt.B Kt.st) j) (Kt.pred u)

theorem kit_rec_eq {ℓ k : Nat} {Is C : Nat → V} (Kt : UnionRecKitC ℓ k Is C) {c : Nat}
    (hc : c < k) {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (C c) i) :
    Kt.recAt c i x = Kt.st (tagged c i x) (kitGraphAt Kt (tagged c i x)) :=
  Kt.rec_eq hc hi hx

/-! ## The EMPTY kit — O-3's escape

`RecFamData.kit` is total over prefix spines, including spines that
fit no recursor's prefix.  That is not a burden on an instantiation:
at empty carriers the tagged union is empty and ALL FOUR obligations
are vacuous, so the instantiator never has to invent a recursion
there.  This is that kit. -/

/-! ## The family's data -/

/-- **The recursion data of a recursor family** at the base frame `ρ`:
per PREFIX SPINE a class kit over the classes' ORDINARY carriers, with
the two readings the recursors' TYPES fix.

The kit is indexed by a prefix spine, not by a class: the classes
recurse SIMULTANEOUSLY, and a guarded call passes the rule's own
prefix variables (M5k §14.2, answer 2 strict), so two classes that
call each other are read at the same spine.  Classes that call nobody
may have their own `rP c` and are simply read at their own. -/
structure RecFamData (V : Type uv) [SetTheory V] (ℓ K : Nat) (rP : Nat → Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (concl : Nat → AnnotTerm) (ρ : Nat → V) where
  /-- The classes' index sets, at a prefix frame. -/
  Is : List V → Nat → V
  /-- The classes' ORDINARY carriers — `⟦T_m p⃗⟧` or `⟦C Ds⟧`, nothing
  identified with anything. -/
  Cr : List V → Nat → V
  /-- The index TUPLE of a class's index spine. -/
  tupOf : Nat → List V → V
  /-- The kit, one per prefix spine (`emptyKitC` where nothing fits). -/
  kit : ∀ xs : List V, UnionRecKitC ℓ K (Is xs) (Cr xs)
  /-- A fitting spine of `rec_c`'s type is `x⃗ ++ ı⃗ ++ [t]`, its index
  tuple in the class's index set and its major in the class's carrier. -/
  hsplit : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (prefOf (rP c) ys).length = rP c ∧
    ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
    tupOf c (idxOf (rP c) ys) ∈ˢ Is (prefOf (rP c) ys) c ∧
    majOf ys ∈ˢ app (Cr (prefOf (rP c) ys) c) (tupOf c (idxOf (rP c) ys))
  /-- The conclusion reads to the kit's motive at the tagged index. -/
  hconcl : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (kit (prefOf (rP c) ys)).B (tagged c (tupOf c (idxOf (rP c) ys)) (majOf ys))
      = interp V (consList ys ρ) (concl c)

/-! ## The candidate -/

/-- **The candidate at class `c`**: the λ-tower over the recursor
type's binder data whose body is the kit's recursor at the spine's
index tuple and major. -/
noncomputable def famCand {ℓ K : Nat} {rP : Nat → Nat}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl : Nat → AnnotTerm} {ρ : Nat → V}
    (D : RecFamData V ℓ K rP rds concl ρ) (c : Nat) : V :=
  lamTowerA ℓ ρ [] (rds c) fun ys _ =>
    (D.kit (prefOf (rP c) ys)).recAt c (D.tupOf c (idxOf (rP c) ys)) (majOf ys)

/-- **`mem_type` of the candidate**: it inhabits the recursor's type. -/
theorem famCand_mem {ℓ K : Nat} {rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    {concl : Nat → AnnotTerm} {ρ : Nat → V} (D : RecFamData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0)
    {c : Nat} (hc : c < K) (hbits : ∀ d ∈ rds c, (ℓ = 0 ↔ d.2.1 = 0)) :
    famCand D c ∈ˢ interp V ρ (mkPisAV (rds c) (concl c)) := by
  refine lamTowerA_mem hbits (towerWalkA_of_spines_body fun ys hsp => ⟨?_, fun h0 => absurd h0 hℓ⟩)
  obtain ⟨-, -, hi, hx⟩ := D.hsplit c hc ys hsp
  have hmem := (D.kit (prefOf (rP c) ys)).rec_mem_B hc hi hx
  rw [D.hconcl c hc ys hsp] at hmem
  simpa using hmem

/-- **The candidate folds to the kit's recursor** along a fitting
spine `x⃗ ++ ı⃗ ++ [t]` (the ι law's left-hand side). -/
theorem famCand_fold {ℓ K : Nat} {rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    {concl : Nat → AnnotTerm} {ρ : Nat → V} (D : RecFamData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0)
    {c : Nat} {xs is : List V} {t : V} (hx : xs.length = rP c)
    (hsp : SpineFit ρ ((rds c).map (·.2.2)) (xs ++ (is ++ [t]))) :
    (xs ++ (is ++ [t])).foldl SetTheory.app (famCand D c)
      = (D.kit xs).recAt c (D.tupOf c is) t := by
  rw [famCand, lamTowerA_fold hℓ hsp]
  simp only [List.nil_append]
  rw [prefOf_split hx, idxOf_split hx, majOf_split]

/-! ## The arm's deliverable -/

section Cand

variable {ℓ K : Nat} {rP : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {concl RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **THE KIT ARM'S CANDIDATE** (DESIGN v2 §3.2 at `WfRecKit`, §3.4 at
the squash kit): at `ℓ ≠ 0` a class kit gives a tuple typed at the
recursor types satisfying every rule's ι law, once the Model tier's
two bridges hold —

* `hrule`: a rule's own spine (the prefix, the constructor's index
  expressions, the constructed major) FITS the recursor's type at the
  base frame;
* `hst`: the kit's step at that tagged index, applied to the
  recursor's graph over its predecessors, READS as the residue at the
  ih values (the ih openers valued in the graph — F3's curried
  ih-tower finding; the kit's own `hst` is G1, the residue's certified
  typing).

Everything else is this file's. -/
theorem famCand_hCand (D : RecFamData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0)
    (hTy : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ K rds)
    (hpl : ∀ c, c < K → (pdoms c).length = rP c)
    (hrule : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)])))
    (hst : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (famCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (D.kit xs).st
          (tagged c
            (D.tupOf c ((es c j).map
              (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
            (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j)))
          (kitGraphAt (D.kit xs)
            (tagged c
              (D.tupOf c ((es c j).map
                (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)))))
              (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ)) (mk c j))))
        = interp V
            (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (famCand D) ρ))))
              (consList (xs ++ fs) (chainFrame K (famCand D) ρ))) (Rb c j)) :
    ∃ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        (pt : V) ∈ˢ interp V (chainFrame K a ρ) e := by
  refine hCand_iotaEqsAV_of (famCand D) (fun c hc => ?_) fun c hc j hj xs fs hxl hsp => ?_
  · rw [hTy c hc]
    exact famCand_mem D hℓ hc (hbits c hc)
  · have hxr : xs.length = rP c := by rw [hxl, hpl c hc]
    have hfit := hrule c hc j hj xs fs hxl hsp
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [famCand_fold D hℓ hxr hfit]
    obtain ⟨-, -, hi, hx⟩ := D.hsplit c hc _ hfit
    rw [prefOf_split hxr, idxOf_split hxr] at hi
    rw [prefOf_split hxr, idxOf_split hxr, majOf_split] at hx
    rw [kit_rec_eq (D.kit xs) hc hi hx]
    exact hst c hc j hj xs fs hxl hsp

end Cand

end ConLeche.Semantics
