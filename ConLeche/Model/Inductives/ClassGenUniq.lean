module

public import ConLeche.Model.Inductives.ClassRecKit

public section

/-!
# `huniq` and `hconclTy` at the generated recursor family

Two premises of `graphRecPre_gen` (`ClassRecKit.lean`) that the generator
does not produce, over PLAIN hypotheses (no class kit):

* **`huniq`** (`genUniq`): two decodings of a major are equal, or the
  motive's value at it is a subsingleton.  At `ℓ = 0` the bound is a truth
  value (from `hconclTy`); at a nonzero width the class's recorded clause
  injection is injective (`LfpClause.mkInj`), given the class's fit is the
  clause's hole fit at its carrier and its injection the clause's; at a
  `Prop`-valued class under a large eliminator a per-major LICENCE (fits at
  one index tuple coincide — the elimination guard's criterion).
* **`hconclTy`** (`genConclTy_of`): the conclusion's typing at every fit of
  the generated binder data, read at the generated classes.

Ported from the parked class checker's `ClassInd.lean` (`ClassPres.uniq`,
`genConclTy_of`); `genUniq` states the one-node-per-class presentation's
fields it used as plain hypotheses, indexed by class.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name)

universe w

variable {V : Type w} [SetTheory V]

/-! ## `huniq` -/

section Uniq

variable {acval : Name → (Name → Nat) → AnnotTerm} {K : Nat} {nCt : Nat → Nat}
  {Is Cr : List V → Nat → V} {injX : Nat → Nat → List V → V}
  {fit : List V → Nat → V → Nat → List V → Prop} {xs : List V}

/-- **`huniq`**: two decodings of a major are equal, or the bound is a
subsingleton.  Class `c` (when it has an index tuple) is component `m c`
of the recorded clause `D c` at `ψ c` and the true frame `fr c`: its
decoding fit is the clause's hole fit at the carrier (`hfit`) and its
injection the clause's (`hinj`).  At `ℓ = 0` the bound is a truth value
(`hconclTy`); at a nonzero width the injection is injective; at width `0`
under `ℓ ≠ 0` the licence `hlic` does it. -/
theorem genUniq (D : Nat → LfpDatum V) (ψ : Nat → Name → Nat) (fr : Nat → Nat → V)
    (m : Nat → Nat)
    (hcl : ∀ c, c < K → ∀ t, t ∈ˢ Is xs c → LfpClause acval (D c))
    (hm : ∀ c, c < K → ∀ t, t ∈ˢ Is xs c → m c < (D c).N)
    (hinj : ∀ c, c < K → ∀ t, t ∈ˢ Is xs c → ∀ j fs, injX c j fs = (D c).inj (ψ c) (m c) j fs)
    (hfit : ∀ c, c < K → ∀ t j fs, t ∈ˢ Is xs c → fit xs c t j fs →
      (D c).HFits (ψ c) (fr c) ((D c).carrier (ψ c) (fr c)) t (m c) j fs)
    {ℓ : Nat} {concl : Nat → AnnotTerm} {uX nIdxX : Nat → Nat} {ρ : Nat → V}
    (hconclTy : ∀ c, c < K → ∀ i, i ∈ˢ Is xs c → ∀ x, x ∈ˢ app (Cr xs c) i →
      interp V (consList (xs ++ (isOfW (uX c) (nIdxX c) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hlic : ℓ ≠ 0 → ∀ c, c < K → (D c).w (ψ c) = 0 → ∀ t, t ∈ˢ Is xs c → ∀ j fs j' fs',
      fit xs c t j fs → fit xs c t j' fs' → j = j' ∧ fs = fs') :
    ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
      ∀ e e', graphDecG Is injX nCt K fit xs u e → graphDecG Is injX nCt K fit xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v' ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v = v' := by
  by_cases hℓ : ℓ = 0
  · refine huniq_of_prop fun u hu => ?_
    have hmem := blockRecMot_mem_univ (K := K) hconclTy u hu
    rwa [hℓ] at hmem
  refine huniq_of_dec fun u _ e e' he he' => ?_
  obtain ⟨c, j, fs⟩ := e
  obtain ⟨c', j', fs'⟩ := e'
  obtain ⟨hc, -, i, hi, hf, rfl⟩ := he
  obtain ⟨-, -, i', hi', hf', heq⟩ := he'
  obtain ⟨rfl, rfl, hinjE⟩ := tagged_inj heq
  suffices h : j = j' ∧ fs = fs' by rw [h.1, h.2]
  by_cases hw : (D c).w (ψ c) = 0
  · exact hlic hℓ c hc hw i hi j fs j' fs' hf hf'
  · have hF := hfit c hc i j fs hi hf
    have hF' := hfit c hc i j' fs' hi hf'
    rw [hinj c hc i hi, hinj c hc i hi] at hinjE
    exact (hcl c hc i hi).mkInj _ hw (m c) (hm c hc i hi) j fs j' fs'
      hF.1 hF'.1 hF.2.1.length_eq hF'.2.1.length_eq hinjE

end Uniq

/-! ## `hconclTy` at the generated classes

The conclusion's typing is a fact of the generated TYPE: at every fit of
its binder data (prefix, index spine, major) the conclusion reads to a
set of the elimination level (`hty`).  Read at the graph's classes — an
index tuple of the generated index domains, a major of the major
domain's reading there — it is `graphRecPre_gen`'s `hconclTy`. -/

section ConclTy

variable {K : Nat} {ρ : Nat → V} {pre idxB : Nat → List (Nat × Nat × AnnotTerm)}
  {majB : Nat → Nat × Nat × AnnotTerm} {uX : Nat → Nat}

/-- **`hconclTy` from the generated type's conclusion typing.** -/
theorem genConclTy_of {ℓ : Nat} {concl : Nat → AnnotTerm}
    (hIdx : ∀ c, c < K → ∀ xs, SpineFit ρ (genPdoms pre c) xs →
      IdxOk (uX c) (consList xs ρ) (genIdxDoms idxB c))
    (hty : ∀ c, c < K → ∀ ys, SpineFit ρ ((genRds pre idxB majB c).map (·.2.2)) ys →
      interp V (consList ys ρ) (concl c) ∈ˢ (univ ℓ : V)) :
    ∀ xs : List V, ∀ c, c < K → ∀ i, i ∈ˢ genIs ρ pre idxB uX xs c →
      ∀ x, x ∈ˢ app (genCr ρ pre idxB majB uX xs c) i →
      interp V (consList (xs ++ (isOfW (uX c) (idxB c).length i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V) := by
  intro xs c hc i hi x hx
  have hxs := genIs_fits hi
  rw [genCr, app_graph hi] at hx
  have hi' := hi
  rw [genIs_pos hxs] at hi'
  obtain ⟨is, his, rfl⟩ := mem_idxSet_elim hi'
  have hl : (idxB c).length = (genIdxDoms idxB c).length := by simp [genIdxDoms]
  rw [hl, isOfW_tupW (hIdx c hc xs hxs) his] at hx ⊢
  exact hty c hc _ (genRds_fit hxs his hx)

end ConclTy

end ConLeche.Model
