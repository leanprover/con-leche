module

public import ConLeche.Model.Inductives.BlockRecGraph

public section

/-!
# The graph route at the GENERATED recursor family (G1)

The class check (`Kernel/Inductives/ClassCheck.lean`, check 6) GENERATES
the recursor family: per recursor `c` a type
`Π (prefix) (ı⃗ : index domains) (t : I D⃗ ı⃗), motive_c ı⃗ t` whose
prefix (parameters, motives, minors) is shared, and per constructor a
rule `λ prefix f⃗, minor f⃗ (λ a⃗, rec_t prefix e⃗ (f a⃗))…`.  The recursor
model's producer `graphRecPre_core` (`BlockRecGraph.lean`) is generic in
the family's classes (`Is`, `Cr`, `injX`, the index tuple, the decoding
`fit`, the calls) and asks rows of them.  Read off the GENERATED family,
most rows hold BY CONSTRUCTION — this file chooses the classes so:

* **the majors are the generated type's own readings**: a class's index
  set is the index-tuple set of the type's index domains
  (`genIs`), its carrier at an index tuple the major domain's reading
  (`genCr`).  So the type split (`hsplit`) and the conclusion
  (`hconcl`) are the type's reading, nothing else;
* **a decoding's fit is the rule's own binder fit** (`genFit`): the
  fields fit the rule's field domains and the index tuple is the
  constructor's index expressions' reading.  So `hspF` and `hdec`'s fit
  half are definitional;
* **the calls are the generated `ih`s' own** (`genCall`, over the
  generator's call relation `callAt`: an `ih` of callee `t` at a
  telescope spine), and the graph's `ih` values are the `ih` terms read
  at the chain valuation `genF g` — every recursor the λ-tower reading
  the graph `g` at its tagged major.  So `hchain` is the `ih` terms'
  CHAIN READING (`hihRead`: an `ih` term reads the chain only at its
  calls' spines) and the calls' typing (`hcallTy`: a call's spine fits
  its callee's type) — no K.53′, no call tie, no node landing: the
  callee is literally the class the generator used.

What is left as premises is what no construction gives:
* the CONSTRUCTOR's typing at the class (`hctorTy`: the rule's own
  spine fits the recursor type — the class side's T3′) and its
  parameter-blind reading (`hmk`: the model's constructor value);
* the rows' independence of the chain frame (`hchI`: the prefix and
  field domains, index expressions and fired spine name no recursor —
  syntactic, the generated terms mention the recursors only in the
  `ih`s);
* the index telescope's grading (`hIdx`), the family's level (`hbits`),
  and the kit's typing, uniqueness and induction rows, passed through
  (`hconclTy`, `hcerts`, `hihF`, `hCaB`, `huniq`, `hind`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The classes, read off the generated family -/

section Defs

variable (K : Nat) (ρ : Nat → V) (rP : Nat → Nat)
  (pre idxB : Nat → List (Nat × Nat × AnnotTerm)) (majB : Nat → Nat × Nat × AnnotTerm)
  (uX : Nat → Nat)

/-- The generated recursor type's binder data: the shared prefix, the
class's index binders, its major. -/
@[expose] def genRds (c : Nat) : List (Nat × Nat × AnnotTerm) := pre c ++ (idxB c ++ [majB c])

/-- The prefix domains. -/
@[expose] def genPdoms (c : Nat) : List AnnotTerm := (pre c).map (·.2.2)

/-- The index domains (at the prefix frame). -/
@[expose] def genIdxDoms (c : Nat) : List AnnotTerm := (idxB c).map (·.2.2)

/-- **The class's index set** at a prefix spine: the index tuples of the
generated type's index domains, guarded by the prefix's fit. -/
@[expose] noncomputable def genIs (xs : List V) (c : Nat) : V :=
  open Classical in
  if SpineFit ρ (genPdoms pre c) xs then idxSet (uX c) (consList xs ρ) (genIdxDoms idxB c)
  else empty

/-- **The class's carrier** at a prefix spine: at an index tuple, the
major domain's reading. -/
@[expose] noncomputable def genCr (xs : List V) (c : Nat) : V :=
  graph (fun i => interp V (consList (isOfW (uX c) (idxB c).length i) (consList xs ρ))
    (majB c).2.2) (genIs ρ pre idxB uX xs c)

/-- **A decoding's fit**: the fields fit the rule's field domains, and
the index tuple is the constructor's index expressions' reading. -/
@[expose] def genFit (fdoms es : Nat → Nat → List AnnotTerm) (xs : List V) (c : Nat) (i : V)
    (j : Nat) (fs : List V) : Prop :=
  SpineFit (consList xs ρ) (fdoms c j) fs ∧
    i = tupW (uX c) ((es c j).map (interp V (consList (xs ++ fs) ρ)))

/-- **The calls**: the tagged majors the generator's calls name. -/
@[expose] def genCall (callAt : List V → Nat → Nat → List V → Nat → List V → V → Prop)
    (xs : List V) (c j : Nat) (fs : List V) (v : V) : Prop :=
  ∃ t is x, callAt xs c j fs t is x ∧ v = tagged t (tupW (uX t) is) x

/-- **The chain valuation of a graph**: every recursor the graph-regime
λ-tower over its type's binder data reading `g` at the tagged major. -/
@[expose] noncomputable def genF (g : V) (t : Nat) : V :=
  lamTowerA 1 ρ [] (genRds pre idxB majB t) fun sp _ =>
    app g (tagged t (tupW (uX t) (idxOf (rP t) sp)) (majOf sp))

/-- **The graph's `ih` values**: the `ih` terms read at the chain
valuation of the graph. -/
@[expose] noncomputable def genIhv (ihs : Nat → Nat → List AnnotTerm) (xs : List V) (c j : Nat)
    (fs : List V) (g : V) : List V :=
  (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (genF ρ rP pre idxB majB uX g) ρ)))

end Defs

/-! ## 2. The rows, by construction -/

section Rows

variable {K : Nat} {ρ : Nat → V} {rP : Nat → Nat}
  {pre idxB : Nat → List (Nat × Nat × AnnotTerm)} {majB : Nat → Nat × Nat × AnnotTerm}
  {uX : Nat → Nat}

theorem genIs_pos {xs : List V} {c : Nat} (h : SpineFit ρ (genPdoms pre c) xs) :
    genIs ρ pre idxB uX xs c = idxSet (uX c) (consList xs ρ) (genIdxDoms idxB c) := by
  classical
  rw [genIs, if_pos h]

theorem genIs_fits {xs : List V} {c : Nat} {i : V} (h : i ∈ˢ genIs ρ pre idxB uX xs c) :
    SpineFit ρ (genPdoms pre c) xs := by
  classical
  by_cases hg : SpineFit ρ (genPdoms pre c) xs
  · exact hg
  · rw [genIs, if_neg hg] at h
    exact absurd h (not_mem_empty _)

/-- A fitting split spine names a major: its index tuple is in the index
set, its major in the carrier there. -/
theorem genMajor_mem (hIdx : ∀ xs, SpineFit ρ (genPdoms pre c) xs →
      IdxOk (uX c) (consList xs ρ) (genIdxDoms idxB c))
    {xs is : List V} {x : V} (hxs : SpineFit ρ (genPdoms pre c) xs)
    (his : SpineFit (consList xs ρ) (genIdxDoms idxB c) is)
    (hx : x ∈ˢ interp V (consList is (consList xs ρ)) (majB c).2.2) :
    tupW (uX c) is ∈ˢ genIs ρ pre idxB uX xs c ∧
      x ∈ˢ app (genCr ρ pre idxB majB uX xs c) (tupW (uX c) is) := by
  have hi : tupW (uX c) is ∈ˢ genIs ρ pre idxB uX xs c := by
    rw [genIs_pos hxs]; exact tupW_mem his
  refine ⟨hi, ?_⟩
  rw [genCr, app_graph hi]
  have hl : (idxB c).length = (genIdxDoms idxB c).length := by simp [genIdxDoms]
  rw [hl, isOfW_tupW (hIdx xs hxs) his]
  exact hx

/-- A fit of the generated type's binder data splits as prefix, index
spine and major. -/
theorem genRds_split {c : Nat} {ys : List V}
    (h : SpineFit ρ ((genRds pre idxB majB c).map (·.2.2)) ys) :
    ∃ xs is x, ys = xs ++ (is ++ [x]) ∧ SpineFit ρ (genPdoms pre c) xs ∧
      SpineFit (consList xs ρ) (genIdxDoms idxB c) is ∧
      x ∈ˢ interp V (consList is (consList xs ρ)) (majB c).2.2 := by
  simp only [genRds, List.map_append, List.map_cons, List.map_nil] at h
  obtain ⟨xs, ys', rfl, hxs, h'⟩ := spineFit_append_split h
  obtain ⟨is, zs, rfl, his, hz⟩ := spineFit_append_split h'
  match zs, hz with
  | [x], hz => exact ⟨xs, is, x, rfl, hxs, his, hz.1⟩

/-- The converse: prefix, index spine and major fit the binder data. -/
theorem genRds_fit {c : Nat} {xs is : List V} {x : V}
    (hxs : SpineFit ρ (genPdoms pre c) xs)
    (his : SpineFit (consList xs ρ) (genIdxDoms idxB c) is)
    (hx : x ∈ˢ interp V (consList is (consList xs ρ)) (majB c).2.2) :
    SpineFit ρ ((genRds pre idxB majB c).map (·.2.2)) (xs ++ (is ++ [x])) := by
  simp only [genRds, List.map_append, List.map_cons, List.map_nil]
  exact SpineFit.append hxs (SpineFit.append his ⟨hx, trivial⟩)

/-- **`hchain`, by construction.** -/
theorem genHchain {nCt : Nat → Nat} {fdoms ihs : Nat → Nat → List AnnotTerm}
    {callAt : List V → Nat → Nat → List V → Nat → List V → V → Prop}
    (hpl : ∀ c, c < K → (pre c).length = rP c)
    (hIdx : ∀ c, c < K → ∀ xs, SpineFit ρ (genPdoms pre c) xs →
      IdxOk (uX c) (consList xs ρ) (genIdxDoms idxB c))
    (hcallTy : ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs fs : List V) (a : Nat → V),
      xs.length = (genPdoms pre c).length →
      SpineFit (chainFrame K a ρ) (genPdoms pre c ++ fdoms c j) (xs ++ fs) →
      ∀ t is x, callAt xs c j fs t is x →
        t < K ∧ xs.length = rP t ∧
          SpineFit ρ ((genRds pre idxB majB t).map (·.2.2)) (xs ++ (is ++ [x])))
    (hihRead : ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs fs : List V) (a a' : Nat → V),
      xs.length = (genPdoms pre c).length →
      SpineFit (chainFrame K a ρ) (genPdoms pre c ++ fdoms c j) (xs ++ fs) →
      (∀ t is x, callAt xs c j fs t is x →
        (xs ++ (is ++ [x])).foldl SetTheory.app (a t)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a' t)) →
      (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
        = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K a' ρ)))) :
    ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < K → ∀ (is : List V) (x : V),
        xs.length = rP c' →
        SpineFit ρ ((genRds pre idxB majB c').map (·.2.2)) (xs ++ (is ++ [x])) →
        r (tagged c' (tupW (uX c') is) x) = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < K → ∀ j, j < nCt c → ∀ fs : List V,
        xs.length = (genPdoms pre c).length →
        SpineFit (chainFrame K a ρ) (genPdoms pre c ++ fdoms c j) (xs ++ fs) →
        genIhv K ρ rP pre idxB majB uX ihs xs c j fs
            (graph r (graphPredG (genIs ρ pre idxB uX) (genCr ρ pre idxB majB uX) K
              (genCall uX callAt) xs (c, j, fs)))
          = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ))) := by
  intro a xs r hr c hc j hj fs hxl hsp
  refine (hihRead c hc j hj xs fs a _ hxl hsp fun t is x hcall => ?_).symm
  obtain ⟨ht, hxlT, hfitT⟩ := hcallTy c hc j hj xs fs a hxl hsp t is x hcall
  obtain ⟨xs', is', x', heq, hxs', his', hx'⟩ := genRds_split hfitT
  -- the split is the call's own spine
  have hxs : xs' = xs := by
    have := congrArg (prefOf (rP t)) heq
    rwa [prefOf_split hxlT, prefOf_split (by rw [← hpl t ht, hxs'.length_eq]; simp [genPdoms]),
      eq_comm] at this
  subst hxs
  have his : is' = is := by
    have := congrArg (idxOf (rP t)) heq
    rw [idxOf_split hxlT, idxOf_split hxlT] at this; exact this.symm
  subst his
  have hx : x' = x := by
    have := congrArg majOf heq
    rw [majOf_split, majOf_split] at this; exact this.symm
  subst hx
  -- the graph-regime tower folds to the graph at the tagged major
  have hfold := lamTowerA_fold (m := 1) Nat.one_ne_zero
    (g := fun sp _ => app (graph r (graphPredG (genIs ρ pre idxB uX)
      (genCr ρ pre idxB majB uX) K (genCall uX callAt) xs' (c, j, fs)))
        (tagged t (tupW (uX t) (idxOf (rP t) sp)) (majOf sp)))
    (acc := []) hfitT
  rw [List.nil_append, idxOf_split hxlT, majOf_split] at hfold
  show _ = (xs' ++ (is' ++ [x'])).foldl SetTheory.app (genF ρ rP pre idxB majB uX _ t)
  rw [genF, hfold]
  -- the tagged major is a predecessor
  obtain ⟨hi, hxC⟩ := genMajor_mem (hIdx t ht) hxs' his' hx'
  have hpred : tagged t (tupW (uX t) is') x' ∈ˢ graphPredG (genIs ρ pre idxB uX)
      (genCr ρ pre idxB majB uX) K (genCall uX callAt) xs' (c, j, fs) :=
    mem_graphPredG.mpr ⟨tagged_mem_unionSet ht hi hxC, ⟨t, is', x', hcall, rfl⟩⟩
  rw [app_graph hpred]
  exact (hr t ht is' x' hxlT hfitT).symm

end Rows

end ConLeche.Model
