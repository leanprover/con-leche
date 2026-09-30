module

public import ConLeche.Model.Inductives.BlockRecGraph

public section

/-!
# The graph route at the GENERATED recursor family (G1)

The generated recursor stage (`Kernel/Inductives/GenRec.lean`) GENERATES
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
  (`hconclTy`; `hstep`, the step's typing — at the generated rule the
  minor premise's own type, §0; `huniq`; `hind`).
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


/-! ## 0. The graph producer over a STEP premise

`graphRecPre_core` (`BlockRecGraph.lean`) types the kit's step through
`BlockRuleCerts` — the per-part typing run of the OLD rule stage, which
the generated stage does not run (it infers the generated rule WHOLE,
`classRuleOk`).  At the generated family
the step's typing is the minor premise's own type (a minor applied to
the fields and the `ih` values lands in the motive at the constructor),
so the producer is restated over the kit's step fact itself (`hstep`);
`graphRecPre_core`'s `hcerts`/`hihF`/`hCaB` are one way to give it. -/

section CoreR

variable {ℓ K : Nat} {ρ : Nat → V} {nCt rP : Nat → Nat}
  {concl : Nat → AnnotTerm} {pdoms : Nat → List AnnotTerm} {fdoms : Nat → Nat → List AnnotTerm}
  {Rb0 : Nat → Nat → AnnotTerm} {ihv : List V → Nat → Nat → List V → V → List V}
  {call : List V → Nat → Nat → List V → V → Prop}

/-- **The graph kit over a step premise** (`graphKitG` with the step's
typing given directly). -/
noncomputable def graphKitR
    (Is Cr : List V → Nat → V) (injX : Nat → Nat → List V → V) (uX nIdxX : Nat → Nat)
    (fit : List V → Nat → V → Nat → List V → Prop) (xs : List V)
    (hconclTy : ∀ c, c < K → ∀ i, i ∈ˢ Is xs c →
      ∀ x, x ∈ˢ app (Cr xs c) i →
      interp V (consList (xs ++ (isOfW (uX c) (nIdxX c) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hstep : ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ Is xs c → fit xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ graphPredG Is Cr K call xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl uX nIdxX ρ xs v) →
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j)
        ∈ˢ blockRecMot K concl uX nIdxX ρ xs (tagged c i (injX c j fs)))
    (huniq : ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
      ∀ e e', graphDecG Is injX nCt K fit xs u e → graphDecG Is injX nCt K fit xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v' ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v = v')
    (hind : ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
        (∃ e, graphDecG Is injX nCt K fit xs u e ∧
          ∀ v, v ∈ˢ graphPredG Is Cr K call xs e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) → P u) :
    GraphRecKit ℓ (unionSet K (Is xs) (Cr xs)) (Nat × Nat × List V) where
  Dec := graphDecG Is injX nCt K fit xs
  pred := graphPredG Is Cr K call xs
  B := blockRecMot K concl uX nIdxX ρ xs
  st := blockGraphStep ρ Rb0 ihv xs
  hpred := fun _ _ _ _ => sep_subset
  hB := blockRecMot_mem_univ hconclTy
  hst := by
    intro u _ e he g hg
    obtain ⟨c, j, fs⟩ := e
    obtain ⟨hc, hj, i, hi, hfit, rfl⟩ := he
    have hgB : ∀ v, v ∈ˢ graphPredG Is Cr K call xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl uX nIdxX ρ xs v := by
      intro v hv
      have h1 := app_mem_of_mem_piSet hg hv
      exact gGraph_mem_B (blockRecMot_mem_univ hconclTy) (fun _ _ _ _ => sep_subset)
        (mem_graphPredG.mp hv).1 h1
    exact hstep c hc j hj i fs hi hfit g hgB
  huniq := huniq
  ind := hind

set_option maxHeartbeats 1000000 in
/-- **`graphRecPre_core` over a step premise.**  The same candidate and
the same rows; the step's typing is `hstep`. -/
theorem graphRecPre_coreR {es ihs : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
    {rds : Nat → List (Nat × Nat × AnnotTerm)} {RecTy : Nat → AnnotTerm}
    (Is Cr : List V → Nat → V) (injX : Nat → Nat → List V → V) (uX nIdxX : Nat → Nat)
    (tupX : Nat → List V → V)
    (fit : List V → Nat → V → Nat → List V → Prop)
    (hTyP : ∀ c, c < K → RecTy c = mkPisAV (rds c) (concl c))
    (hbits : OneElimLevel ℓ K rds)
    (hpl : ∀ c, c < K → (pdoms c).length = rP c)
    (hsplit : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      (prefOf (rP c) ys).length = rP c ∧
      ys = prefOf (rP c) ys ++ (idxOf (rP c) ys ++ [majOf ys]) ∧
      tupX c (idxOf (rP c) ys) ∈ˢ Is (prefOf (rP c) ys) c ∧
      majOf ys ∈ˢ app (Cr (prefOf (rP c) ys) c) (tupX c (idxOf (rP c) ys)))
    (hconcl : ∀ c, c < K → ∀ ys, SpineFit ρ ((rds c).map (·.2.2)) ys →
      blockRecMot K concl uX nIdxX ρ (prefOf (rP c) ys)
          (tagged c (tupX c (idxOf (rP c) ys)) (majOf ys))
        = interp V (consList ys ρ) (concl c))
    (hconclTy : ∀ xs : List V, ∀ c, c < K → ∀ i, i ∈ˢ Is xs c →
      ∀ x, x ∈ˢ app (Cr xs c) i →
      interp V (consList (xs ++ (isOfW (uX c) (nIdxX c) i ++ [x])) ρ) (concl c)
        ∈ˢ (univ ℓ : V))
    (hstep : ∀ xs : List V, ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ Is xs c → fit xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ graphPredG Is Cr K call xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl uX nIdxX ρ xs v) →
      interp V (consList (ihv xs c j fs g) (consList (xs ++ fs) ρ)) (Rb0 c j)
        ∈ˢ blockRecMot K concl uX nIdxX ρ xs (tagged c i (injX c j fs)))
    (huniq : ∀ xs : List V, ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
      ∀ e e', graphDecG Is injX nCt K fit xs u e → graphDecG Is injX nCt K fit xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v' ∈ˢ blockRecMot K concl uX nIdxX ρ xs u →
        v = v')
    (hind : ∀ xs : List V, ∀ P : V → Prop,
      (∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) →
        (∃ e, graphDecG Is injX nCt K fit xs u e ∧
          ∀ v, v ∈ˢ graphPredG Is Cr K call xs e → P v) → P u) →
      ∀ u, u ∈ˢ unionSet K (Is xs) (Cr xs) → P u)
    (hrule : ∀ a : Nat → V, ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      SpineFit ρ ((rds c).map (·.2.2))
        (xs ++ ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame K a ρ)) (mk c j)])))
    (hdec : ∀ a : Nat → V, ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      fit xs c (tupX c ((es c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ))))) j fs ∧
      interp V (consList (xs ++ fs) (chainFrame K a ρ)) (mk c j) = injX c j fs)
    (hchain : ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < K → ∀ (is : List V) (x : V),
        xs.length = rP c' →
        SpineFit ρ ((rds c').map (·.2.2)) (xs ++ (is ++ [x])) →
        r (tagged c' (tupX c' is) x) = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < K → ∀ j, j < nCt c → ∀ fs : List V,
        xs.length = (pdoms c).length →
        SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
        ihv xs c j fs (graph r (graphPredG Is Cr K call xs (c, j, fs)))
          = (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K a ρ)))) :
    ∃ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs
          (fun c j => (Rb0 c j).liftN K ((pdoms c).length + (fdoms c j).length
            + (ihs c j).length)),
        (pt : V) ∈ˢ interp V (chainFrame K a ρ) e := by
  let D : GraphFamData V ℓ K rP rds concl ρ (Nat × Nat × List V) :=
    { Is := Is, Cr := Cr, tupOf := tupX,
      kit := fun xs => graphKitR (Rb0 := Rb0) (ihv := ihv) (call := call) (nCt := nCt)
        Is Cr injX uX nIdxX fit xs (hconclTy xs) (hstep xs) (huniq xs) (hind xs),
      hsplit := hsplit, hconcl := hconcl }
  refine famCandG_hCand D (fun _ c j fs => (c, j, fs)) hTyP hbits hpl (hrule (famCandG D)) ?_ ?_
  · intro c hc j hj xs fs hxl hsp
    have hfit := hrule (famCandG D) c hc j hj xs fs hxl hsp
    have hxr : xs.length = rP c := by rw [hxl, hpl c hc]
    obtain ⟨-, -, hi, -⟩ := D.hsplit c hc _ hfit
    rw [prefOf_split hxr, idxOf_split hxr] at hi
    obtain ⟨hf, hmk⟩ := hdec (famCandG D) c hc j hj xs fs hxl hsp
    exact ⟨hc, hj, _, hi, hf, by rw [hmk]⟩
  · intro c hc j hj xs fs hxl hsp
    have hlen : (xs ++ fs).length = (pdoms c).length + (fdoms c j).length := by
      rw [hsp.length_eq, List.length_append]
    have hch := hchain (famCandG D) xs (fun v => (D.kit xs).recAt v)
      (fun c' hc' is x hxl' hsp' => (famCandG_fold D hc' hxl' hsp').symm) c hc j hj fs hxl hsp
    show interp V (consList (ihv xs c j fs
        (graph (fun v => (D.kit xs).recAt v) (graphPredG Is Cr K call xs (c, j, fs))))
        (consList (xs ++ fs) ρ)) (Rb0 c j) = _
    rw [hch,
      show (pdoms c).length + (fdoms c j).length + (ihs c j).length
        = (xs ++ fs).length + ((ihs c j).map
            (interp V (consList (xs ++ fs) (chainFrame K (famCandG D) ρ)))).length from by
        rw [hlen, List.length_map],
      interp_Rb_chain]

end CoreR

/-! ## 1. The classes, read off the generated family -/

section Defs

variable (K : Nat) (ρ : Nat → V) (rP : Nat → Nat)
  (pre idxB : Nat → List (Nat × Nat × AnnotTerm)) (majB : Nat → Nat × Nat × AnnotTerm)
  (uX : Nat → Nat)

/-- The prefix domains. -/
@[expose] def genPdoms (c : Nat) : List AnnotTerm := (pre c).map (·.2.2)

end Defs

/-! ## 2. The rows, by construction -/

section Rows

variable {K : Nat} {ρ : Nat → V} {rP : Nat → Nat}
  {pre idxB : Nat → List (Nat × Nat × AnnotTerm)} {majB : Nat → Nat × Nat × AnnotTerm}
  {uX : Nat → Nat}

/-- A fit of an appended chain whose first part has the first chain's
length splits there. -/
theorem spineFit_append_at {Ds₁ Ds₂ : List AnnotTerm} {σ : Nat → V} {xs fs : List V}
    (hl : xs.length = Ds₁.length) (h : SpineFit σ (Ds₁ ++ Ds₂) (xs ++ fs)) :
    SpineFit σ Ds₁ xs ∧ SpineFit (consList xs σ) Ds₂ fs := by
  obtain ⟨as₁, as₂, heq, h1, h2⟩ := spineFit_append_split h
  have hl1 : as₁.length = xs.length := by rw [h1.length_eq, hl]
  obtain ⟨rfl, rfl⟩ := List.append_inj heq.symm hl1
  exact ⟨h1, h2⟩

end Rows

/-! ## 4. The generated `ih`s: they read the chain only at their calls

A generated `ih` is `λ a⃗, rec_t x⃗ e⃗ (f a⃗)` — at the rule's frame
`x⃗ ++ f⃗` (depth `D`), a λ-telescope whose body applies the CHAIN
variable of its callee `t` to the prefix variables, the index
arguments and the major argument.  Read at two chain valuations it
agrees as soon as the two recursors agree along every spine the body
applies them to — the `hihRead` premise of `graphRecPre_gen`, by
construction.  The telescope's domains and the arguments name no chain
variable (they are bounded below the chain). -/

section Ihs

/-- A fit is a fit at any frame agreeing below the chain's bound. -/
theorem spineFit_congr_fieldsBelow :
    ∀ {Ds : List AnnotTerm} {k : Nat} {σ σ' : Nat → V} {bs : List V},
      FieldsBelow k Ds → (∀ i, i < k → σ i = σ' i) → SpineFit σ Ds bs → SpineFit σ' Ds bs
  | [], _, _, _, [], _, _, _ => trivial
  | [], _, _, _, _ :: _, _, _, h => h.elim
  | _ :: _, _, _, _, [], _, _, h => h.elim
  | D :: Ds, k, σ, σ', b :: bs, hb, hag, h => by
    refine ⟨?_, spineFit_congr_fieldsBelow (k := k + 1) hb.2 (fun i hi => ?_) h.2⟩
    · rw [← interp_congr_below V D k σ σ' hb.1 hag]; exact h.1
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)

/-- **The `ih` shape's chain reading**: an `ih`-shaped term reads alike
at two frames agreeing below its depth `D`, as soon as the head
variable's two values agree along every spine the body applies them
to. -/
theorem interp_ihShape_congr {m : Nat} (args : List AnnotTerm) :
    ∀ (tele : List (Nat × AnnotTerm)) {D : Nat} {σ σ' : Nat → V},
      FieldsBelow D (tele.map (·.2)) →
      (∀ e ∈ args, Term.bvarsBelow (D + tele.length) e.erase) →
      (∀ i, i < D → σ i = σ' i) →
      (∀ bs, SpineFit σ (tele.map (·.2)) bs →
        (args.map (interp V (consList bs σ))).foldl SetTheory.app (σ (D + m))
          = (args.map (interp V (consList bs σ))).foldl SetTheory.app (σ' (D + m))) →
      interp V σ (mkLamsAV tele (AnnotTerm.mkAppN (.bvar (D + tele.length + m)) args))
        = interp V σ' (mkLamsAV tele (AnnotTerm.mkAppN (.bvar (D + tele.length + m)) args))
  | [], D, σ, σ', _, hargs, hag, h => by
    simp only [mkLamsAV, List.length_nil, Nat.add_zero, interp_mkAppN, interp_bvar]
    have h0 := h [] trivial
    simp only [consList_nil] at h0
    have hmap : args.map (interp V σ') = args.map (interp V σ) :=
      List.map_congr_left fun e he =>
        (interp_congr_below V e D σ σ' (by simpa using hargs e he) hag).symm
    rw [← List.foldl_map, ← List.foldl_map (f := interp V σ'), hmap]
    exact h0
  | (v, A) :: tele, D, σ, σ', hb, hargs, hag, h => by
    show lamR v (interp V σ A) (fun x => interp V (cons x σ) _)
      = lamR v (interp V σ' A) (fun x => interp V (cons x σ') _)
    have hA : interp V σ A = interp V σ' A := interp_congr_below V A D σ σ' hb.1 hag
    rw [← hA]
    refine lamR_congr fun x hx => ?_
    have hidx : D + ((v, A) :: tele).length + m = (D + 1) + tele.length + m := by
      simp; omega
    rw [hidx]
    refine interp_ihShape_congr args tele (D := D + 1) hb.2 (fun e he => ?_)
      (fun i hi => ?_) (fun bs hbs => ?_)
    · have := hargs e he
      simpa [Nat.add_assoc, Nat.add_comm 1 tele.length] using this
    · cases i with
      | zero => rfl
      | succ i => exact hag i (by omega)
    · have hfit : SpineFit σ (((v, A) :: tele).map (·.2)) (x :: bs) := ⟨hx, hbs⟩
      have := h (x :: bs) hfit
      simpa [consList_cons, Nat.add_right_comm D 1 m] using this

/-- One generated `ih`: its callee, its telescope, its index arguments
and its major argument. -/
abbrev IhDatum := Nat × List (Nat × AnnotTerm) × List AnnotTerm × AnnotTerm

/-- **A generated `ih` term** at the rule's depth `D` (prefix `rP`):
`λ a⃗, rec_t x⃗ e⃗ m`, the callee the chain variable `K-1-t` below the
frame. -/
@[expose] def genIhAV (K rP D : Nat) (q : IhDatum) : AnnotTerm :=
  mkLamsAV q.2.1 (AnnotTerm.mkAppN (.bvar (D + q.2.1.length + (K - 1 - q.1)))
    (prefVarsAV rP (D - rP + q.2.1.length) ++ (q.2.2.1 ++ [q.2.2.2])))

/-- **The generated calls**: an `ih` of callee `t` at a fitting
telescope spine calls `t` at its index arguments' and major argument's
readings. -/
@[expose] def genIhCallAt (ρ : Nat → V) (ihd : Nat → Nat → List IhDatum) (xs : List V)
    (c j : Nat) (fs : List V) (t : Nat) (is : List V) (x : V) : Prop :=
  ∃ q ∈ ihd c j, q.1 = t ∧ ∃ bs : List V,
    SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs ∧
    is = q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ))) ∧
    x = interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2

/-- The data of a generated `ih` names no chain variable: its telescope
and arguments are bounded below the chain. -/
@[expose] def IhDatumBelow (D : Nat) (q : IhDatum) : Prop :=
  FieldsBelow D (q.2.1.map (·.2)) ∧
  (∀ e ∈ q.2.2.1 ++ [q.2.2.2], Term.bvarsBelow (D + q.2.1.length) e.erase)

/-- **`hihRead`, by construction** at the generated `ih`s. -/
theorem genIhs_hihRead {K : Nat} {ρ : Nat → V} {nCt : Nat → Nat}
    {pre : Nat → List (Nat × Nat × AnnotTerm)} {fdoms : Nat → Nat → List AnnotTerm}
    {ihd : Nat → Nat → List IhDatum}
    (hcal : ∀ c, c < K → ∀ j, j < nCt c → ∀ q ∈ ihd c j, q.1 < K)
    (hbelow : ∀ c, c < K → ∀ j, j < nCt c → ∀ q ∈ ihd c j,
      IhDatumBelow ((genPdoms pre c).length + (fdoms c j).length) q) :
    ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs fs : List V) (a a' : Nat → V),
      xs.length = (genPdoms pre c).length →
      SpineFit (chainFrame K a ρ) (genPdoms pre c ++ fdoms c j) (xs ++ fs) →
      (∀ t is x, genIhCallAt ρ ihd xs c j fs t is x →
        (xs ++ (is ++ [x])).foldl SetTheory.app (a t)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a' t)) →
      ((ihd c j).map (genIhAV K (genPdoms pre c).length
          ((genPdoms pre c).length + (fdoms c j).length))).map
          (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
        = ((ihd c j).map (genIhAV K (genPdoms pre c).length
          ((genPdoms pre c).length + (fdoms c j).length))).map
          (interp V (consList (xs ++ fs) (chainFrame K a' ρ))) := by
  intro c hc j hj xs fs a a' hxl hsp hcall
  have hfl : fs.length = (fdoms c j).length := by
    have := hsp.length_eq
    simp only [List.length_append] at this
    omega
  have hD : (genPdoms pre c).length + (fdoms c j).length = (xs ++ fs).length := by
    simp [hxl, hfl]
  simp only [List.map_map]
  refine List.map_congr_left fun q hq => ?_
  obtain ⟨hbT, hbA⟩ := hbelow c hc j hj q hq
  simp only [Function.comp, genIhAV]
  rw [hD] at hbT hbA ⊢
  refine interp_ihShape_congr _ q.2.1 hbT (fun e he => ?_) (fun i hi => ?_) (fun bs hbs => ?_)
  · rcases List.mem_append.mp he with he | he
    · -- a prefix variable: below the rule's frame
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp he
      show Term.bvarsBelow _ (AnnotTerm.bvar _).erase
      simp only [AnnotTerm.erase, Term.bvarsBelow, List.mem_range] at hl ⊢
      omega
    · exact hbA e he
  · -- the two frames share the spine
    rw [consList_getD_of_lt _ _ _ hi, consList_getD_of_lt _ _ _ hi]
  · -- the head's two values, and the arguments' readings
    have hq1 := hcal c hc j hj q hq
    have hhead : ∀ b : Nat → V, consList (xs ++ fs) (chainFrame K b ρ)
        ((xs ++ fs).length + (K - 1 - q.1)) = b q.1 := by
      intro b
      rw [Nat.add_comm, consList_apply_add, chainFrame_apply hq1]
    rw [hhead a, hhead a']
    -- the arguments read the call's spine
    have hbsρ : SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs := by
      refine spineFit_congr_fieldsBelow (k := (xs ++ fs).length) hbT (fun i hi => ?_) hbs
      rw [consList_getD_of_lt _ _ _ hi, consList_getD_of_lt _ _ _ hi]
    have hbl : bs.length = q.2.1.length := by rw [hbs.length_eq, List.length_map]
    have hargR : ∀ e ∈ q.2.2.1 ++ [q.2.2.2],
        interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ))) e
          = interp V (consList bs (consList (xs ++ fs) ρ)) e := by
      intro e he
      refine interp_congr_below V e ((xs ++ fs).length + q.2.1.length) _ _ (hbA e he)
        fun i hi => ?_
      rw [← consList_append, ← consList_append,
        consList_getD_of_lt _ _ _ (by simp [hbl]; omega),
        consList_getD_of_lt _ _ _ (by simp [hbl]; omega)]
    have hpre : (prefVarsAV (genPdoms pre c).length
          ((xs ++ fs).length - (genPdoms pre c).length + q.2.1.length)).map
          (interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ)))) = xs := by
      have h := interp_prefVarsAV (V := V) (xs := xs) (bs := fs ++ bs)
        (ρ := chainFrame K a ρ) hxl
      rw [← List.append_assoc, consList_append] at h
      simpa [hbl, hxl, Nat.add_sub_cancel_left] using h
    have hcallq : genIhCallAt ρ ihd xs c j fs q.1
        (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ))))
        (interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2) :=
      ⟨q, hq, rfl, bs, hbsρ, rfl, rfl⟩
    have heq := hcall _ _ _ hcallq
    have hargs : (prefVarsAV (genPdoms pre c).length
          ((xs ++ fs).length - (genPdoms pre c).length + q.2.1.length) ++
          (q.2.2.1 ++ [q.2.2.2])).map
          (interp V (consList bs (consList (xs ++ fs) (chainFrame K a ρ))))
        = xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
          ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2]) := by
      rw [List.map_append, hpre, List.map_congr_left hargR]
      simp
    rw [hargs]
    exact heq

end Ihs

end ConLeche.Model
