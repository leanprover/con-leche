module

public import ConLeche.Semantics.Tower.BlockRecI
public import ConLeche.SetModel.WfRec
@[expose] public section

/-!
# Regime WF: the recursor family's candidate by ∈-recursion (task #315, M5 model half)

DESIGN "DESIGN DOCUMENT 2, v2" §3.2.  At `¬allProp ∧ w ≠ 0` the
recursion is **well-founded recursion on the global subterm relation**
`x ⊏ y := x ∈ tc y` over the tagged union of the majors' ORDINARY
carriers — lane F5's `WfRecKit` (`ConLeche/SetModel/WfRec.lean`), which
asks nothing of the carriers: no fixed-point structure, no
`PredsFrom`, no simultaneous accessibility.  What this file does is
turn that kit into `BlockRecPre`'s `hCand` at the TERM level:

* the candidate is the λ-tower over the recursor type's binder data
  whose body at a leaf frame is `kit.recAt c ⟨ı⃗⟩ t` — `lamTowerA`,
  because the kit is built per PREFIX frame (the carriers depend on the
  parameters, and the minors live in the arbitrary `nP…rP-1` stretch);
* `mem_type` is `rec_mem_B` composed with the reading of the
  conclusion (`WfRecData.hconcl`);
* the ι law is `lamTowerA_fold` (the spine folds into the body)
  composed with `rec_eq` (the body is the step at the graph) composed
  with the model's bridge `st = the residue's reading` (`hst` below).

**What is a premise here and who discharges it.**  Everything that
mentions the STORED forms is the Model tier's: that a rule's spine
fits the recursor's type, that the conclusion reads to the kit's
motive, and that the kit's step reads to the residue at the ih values.
This file proves only that those facts compose into the recursion
theorem.  The kit's own two obligations (`hB`, `hst`) are F5's shape
and the Model tier's content — `hst` is G1, the residue's certified
typing at the constructors' environment.
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
(`rP` binders — record-read, M5k §13), the class's indices, the
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
graph over the value's ∈-predecessors.  That graph is what a rule's ih
openers are valued in, so it gets a name. -/

/-- The recursor's graph over `u`'s ∈-predecessors. -/
noncomputable def kitGraphAt {ℓ k : Nat} {Is C : Nat → V} (Kt : WfRecKit ℓ k Is C) (u : V) : V :=
  graph
    (fun j => recSel (recGraph ℓ (unionSet k Is C) (tcPred (unionSet k Is C)) Kt.B Kt.st) j)
    (tcPred (unionSet k Is C) u)

theorem kit_rec_eq {ℓ k : Nat} {Is C : Nat → V} (Kt : WfRecKit ℓ k Is C) {c : Nat} (hc : c < k)
    {i x : V} (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (C c) i) :
    Kt.recAt c i x = Kt.st (tagged c i x) (kitGraphAt Kt (tagged c i x)) :=
  Kt.rec_eq hc hi hx

/-! ## The regime's data -/

/-- **The WF regime's data** at the base frame `ρ`: per PREFIX frame a
`WfRecKit` over the classes' ordinary carriers, with the two readings
the recursor's TYPE fixes — the spine's decomposition (with the index
tuple in the class's index set and the major in its carrier) and the
conclusion as the kit's motive. -/
structure WfRecData (V : Type uv) [SetTheory V] (ℓ K rP : Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (concl : Nat → AnnotTerm) (ρ : Nat → V) where
  /-- The classes' index sets, at a prefix frame. -/
  Is : List V → Nat → V
  /-- The classes' ORDINARY carriers — `⟦T_m p⃗⟧` or `⟦C Ds⟧`, nothing
  identified with anything. -/
  Cr : List V → Nat → V
  /-- The index TUPLE of a class's index spine. -/
  tupOf : Nat → List V → V
  /-- The kit, one per prefix frame. -/
  kit : ∀ xs : List V, WfRecKit ℓ K (Is xs) (Cr xs)
  /-- A fitting spine of `rec_c`'s type is `x⃗ ++ ı⃗ ++ [t]`, its index
  tuple in the class's index set and its major in the class's carrier. -/
  hsplit : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (prefOf rP ys).length = rP ∧
    ys = prefOf rP ys ++ (idxOf rP ys ++ [majOf ys]) ∧
    tupOf c (idxOf rP ys) ∈ˢ Is (prefOf rP ys) c ∧
    majOf ys ∈ˢ app (Cr (prefOf rP ys) c) (tupOf c (idxOf rP ys))
  /-- The conclusion reads to the kit's motive at the tagged index. -/
  hconcl : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
    (kit (prefOf rP ys)).B (tagged c (tupOf c (idxOf rP ys)) (majOf ys))
      = interp V (consList ys ρ) (concl c)

/-! ## The candidate -/

/-- **The WF regime's candidate at class `c`**: the λ-tower over the
recursor type's binder data whose body is the kit's recursor at the
spine's index tuple and major. -/
noncomputable def wfCand {ℓ K rP : Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    {concl : Nat → AnnotTerm} {ρ : Nat → V} (D : WfRecData V ℓ K rP rds concl ρ) (c : Nat) : V :=
  lamTowerA ℓ ρ [] (rds c) fun ys _ =>
    (D.kit (prefOf rP ys)).recAt c (D.tupOf c (idxOf rP ys)) (majOf ys)

/-- `TowerWalkA` from the facts at every fitting spine. -/
theorem towerWalkA_of_spines {m : Nat} {C : AnnotTerm} {g : List V → (Nat → V) → V} :
    ∀ {ds : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {acc : List V},
      (∀ ys, SpineFit ρ (ds.map (·.2.2)) ys →
        g (acc ++ ys) (consList ys ρ) ∈ˢ interp V (consList ys ρ) C ∧
          (m = 0 → interp V (consList ys ρ) C ∈ˢ (univZero : V))) →
      TowerWalkA m C g ρ acc ds
  | [], ρ, acc, h => by
    have h0 := h [] trivial
    rw [List.append_nil, consList_nil] at h0
    exact h0
  | d :: ds, ρ, acc, h => by
    intro a ha
    refine towerWalkA_of_spines fun ys hsp => ?_
    have := h (a :: ys) ⟨ha, hsp⟩
    rw [consList_cons] at this
    simpa using this

/-- **`mem_type` of the candidate**: it inhabits the recursor's type. -/
theorem wfCand_mem {ℓ K rP : Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    {concl : Nat → AnnotTerm} {ρ : Nat → V} (D : WfRecData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0)
    {c : Nat} (hc : c < K) (hbits : ∀ d ∈ rds c, (ℓ = 0 ↔ d.2.1 = 0)) :
    wfCand D c ∈ˢ interp V ρ (mkPisAV (rds c) (concl c)) := by
  refine lamTowerA_mem hbits (towerWalkA_of_spines fun ys hsp => ⟨?_, fun h0 => absurd h0 hℓ⟩)
  obtain ⟨-, -, hi, hx⟩ := D.hsplit c hc ys hsp
  have hmem := (D.kit (prefOf rP ys)).rec_mem_B hc hi hx
  rw [D.hconcl c hc ys hsp] at hmem
  simpa using hmem

/-- **The candidate folds to the kit's recursor** along a fitting
spine `x⃗ ++ ı⃗ ++ [t]` (the ι law's left-hand side). -/
theorem wfCand_fold {ℓ K rP : Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
    {concl : Nat → AnnotTerm} {ρ : Nat → V} (D : WfRecData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0)
    {c : Nat} {xs is : List V} {t : V} (hx : xs.length = rP)
    (hsp : SpineFit ρ ((rds c).map (·.2.2)) (xs ++ (is ++ [t]))) :
    (xs ++ (is ++ [t])).foldl SetTheory.app (wfCand D c)
      = (D.kit xs).recAt c (D.tupOf c is) t := by
  rw [wfCand, lamTowerA_fold hℓ hsp]
  simp only [List.nil_append]
  rw [prefOf_split hx, idxOf_split hx, majOf_split]

/-! ## The regime's deliverable -/

section Cand

variable {ℓ s K rP : Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)} {concl RecTy : Nat → AnnotTerm}
  {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm} {fdoms es : Nat → Nat → List AnnotTerm}
  {mk : Nat → Nat → AnnotTerm} {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm}
  {ρ : Nat → V}

/-- **THE WF REGIME'S CANDIDATE** (DESIGN v2 §3.2): at `ℓ ≠ 0` the kit
gives a tuple typed at the recursor types satisfying every rule's ι
law, once the Model tier's two bridges hold —

* `hrule`: a rule's own spine (the prefix, the constructor's index
  expressions, the constructed major) FITS the recursor's type at the
  base frame;
* `hst`: the kit's step at that tagged index, applied to the
  recursor's graph over its ∈-predecessors, READS as the residue at
  the ih values (the ih openers valued in the graph — F3's curried
  ih-tower finding; `hst` of the kit is G1, the residue's certified
  typing).

Everything else is this file's. -/
theorem wfCand_hCand (D : WfRecData V ℓ K rP rds concl ρ) (hℓ : ℓ ≠ 0)
    (hTy : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ K rds)
    (hpl : ∀ c, c < K → (pdoms c).length = rP)
    (hrule : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (wfCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K (wfCand D) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K (wfCand D) ρ)) (mk c j)])))
    (hst : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (wfCand D) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (D.kit xs).st
          (tagged c
            (D.tupOf c ((es c j).map
              (interp V (consList (xs ++ fs) (chainFrame K (wfCand D) ρ)))))
            (interp V (consList (xs ++ fs) (chainFrame K (wfCand D) ρ)) (mk c j)))
          (kitGraphAt (D.kit xs)
            (tagged c
              (D.tupOf c ((es c j).map
                (interp V (consList (xs ++ fs) (chainFrame K (wfCand D) ρ)))))
              (interp V (consList (xs ++ fs) (chainFrame K (wfCand D) ρ)) (mk c j))))
        = interp V
            (consList ((ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (wfCand D) ρ))))
              (consList (xs ++ fs) (chainFrame K (wfCand D) ρ))) (Rb c j)) :
    ∃ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        (pt : V) ∈ˢ interp V (chainFrame K a ρ) e := by
  refine hCand_iotaEqsAV_of (wfCand D) (fun c hc => ?_) fun c hc j hj xs fs hxl hsp => ?_
  · rw [hTy c hc]
    exact wfCand_mem D hℓ hc (hbits c hc)
  · have hxr : xs.length = rP := by rw [hxl, hpl c hc]
    have hfit := hrule c hc j hj xs fs hxl hsp
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [wfCand_fold D hℓ hxr hfit]
    obtain ⟨-, -, hi, hx⟩ := D.hsplit c hc _ hfit
    rw [prefOf_split hxr, idxOf_split hxr] at hi
    rw [prefOf_split hxr, idxOf_split hxr, majOf_split] at hx
    rw [kit_rec_eq (D.kit xs) hc hi hx]
    exact hst c hc j hj xs fs hxl hsp

end Cand

end ConLeche.Semantics
