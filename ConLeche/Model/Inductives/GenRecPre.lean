module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.NestedRecEqs
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.BlockRecRun

public section

/-!
# The family premise at the GENERATED recursor stage (`hpre`, lane GENREC-B1)

The skeleton's `hpre` obligation (`GenRecAssembly.lean`, `genRecStage`) —
the recursor model's family premise `BlockRecPre` at every level
assignment and base frame — at the generated family's equation
components (`blockRulePdomsAV`, `tgtFdomsAV`, `tgtEsAV`, `genIhsAV`,
`tgtMkAV`, `genRbAV`).  Its three halves:

* `hTy` — the recursor types' level (`blockRecLevel_run`), passed in;
* `hEq` — the equations are truth values (by their shape,
  `iotaEqAV_univZero`) and graded at every typed tuple (a row);
* `hCand` — the candidate, through the graph producer over a step
  premise (`graphRecPre_coreR`, `ClassRecKit.lean`) at the OLD class data
  (`tgtClsIs`/`tgtClsCr`/`tgtClsInj`/`tgtClsU`/`tgtClsNIdx`/`tgtClsTup`/
  `tgtClsFit`, `TargetClasses.lean`), the generated calls (`genCallT`) and
  the class induction in the interface form `GenClassInd` (lane B2).

The graph's `ih` values are the generated `ih` terms read at the chain
valuation of the graph (`genIhvT`: every recursor the graph-regime
λ-tower over its stored type's binder data reading the graph at the
tagged major).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The graph's `ih` values -/

section Ihv

/-- **The chain valuation of a graph** at the stored binder data `rds`:
recursor `t` is the graph-regime λ-tower over its binder data reading
`g` at the tagged major (`genF` over any binder data and tuple
function). -/
@[expose] noncomputable def genFT (ρ : Nat → V) (rP : Nat → Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (tup : Nat → List V → V) (g : V) (t : Nat) : V :=
  lamTowerA 1 ρ [] (rds t) fun sp _ => app g (tagged t (tup t (idxOf (rP t) sp)) (majOf sp))

/-- **The graph's `ih` values**: the `ih` terms read at the chain
valuation of the graph. -/
@[expose] noncomputable def genIhvT (K : Nat) (ρ : Nat → V) (rP : Nat → Nat)
    (rds : Nat → List (Nat × Nat × AnnotTerm)) (tup : Nat → List V → V)
    (ihs : Nat → Nat → List AnnotTerm) (xs : List V) (c j : Nat) (fs : List V) (g : V) :
    List V :=
  (ihs c j).map (interp V (consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup g) ρ)))

end Ihv

/-! ## 2. The equation list at the chain spelling -/

section Eqs

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC}

/-- **The generated equation list, at the chain spelling** (`tgtClsEqs_eq`
at any `ih` terms and residue): the prefix domains are closed
(`blockRecPdomsK_run`), and the chain lifts keep the field domains'
lengths. -/
theorem genClsEqs_eq (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm) (ψ : Name → Nat) :
    iotaEqsAV (tgtRs out).length (blockRecNCt (tgtRs out))
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
        (fun c j => liftEsK (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
          (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
        (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
        (ihs ψ)
        (fun c j => (Rb0 ψ c j).liftN (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c
              j).length
            + (ihs ψ c j).length))
      = blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          ihs
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          Rb0 ψ := by
  show _ = iotaEqsAV _ _ _ _ _ _ _ _
  refine iotaEqsAV_congr (fun c hc => ?_) (fun c _ j _ => ?_)
  · exact (blockRecPdomsK_run (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ _).symm
  · simp only [tgtFdomsK, liftDomsK_length]

/-- Every member of the family's equation list is a truth value. -/
theorem blockRecEqs_univZero (nCt : Nat → Nat)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (pdoms0 : (Name → Nat) → Nat → List AnnotTerm)
    (fdoms0 es0 ihs : (Name → Nat) → Nat → Nat → List AnnotTerm)
    (mk0 Rb0 : (Name → Nat) → Nat → Nat → AnnotTerm) (ψ : Name → Nat) (σ : Nat → V) :
    ∀ e ∈ blockRecEqs nCt rs pdoms0 fdoms0 es0 ihs mk0 Rb0 ψ,
      interp V σ e ∈ˢ (univZero : V) :=
  forall_iotaEqsAV fun _ _ _ _ => iotaEqAV_univZero

end Eqs

/-! ## 3. The candidate, from the rows

`graphRecPre_coreR` at the old class data, the generated calls and the
graph's `ih` values `genIhvT`.  The type half of the producer
(`hTyP`), the family's one elimination level (`hbits`) and the prefix
lengths (`hpl`) are the stage record's; every other row is a premise,
stated exactly as the producer consumes it (§4 discharges them). -/

section Cand

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal} {g : ClassGen} {rd : ClassRead}

set_option maxHeartbeats 4000000 in
/-- **The candidate of the generated family** — `BlockRecPre.hCand` at the
generated components, from the producer's rows at the old class data. -/
theorem genRecPre_hCand (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (ψ : Name → Nat) (ρ : Nat → V)
    (hsplit : ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
          (·.2.2)) ys →
      (prefOf (pp.toBlockShape.rulePrefixAt c) ys).length = pp.toBlockShape.rulePrefixAt c ∧
      ys = prefOf (pp.toBlockShape.rulePrefixAt c) ys
        ++ (idxOf (pp.toBlockShape.rulePrefixAt c) ys ++ [majOf ys]) ∧
      tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c (idxOf (pp.toBlockShape.rulePrefixAt c) ys)
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ
          (prefOf (pp.toBlockShape.rulePrefixAt c) ys) c ∧
      majOf ys ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ
          (prefOf (pp.toBlockShape.rulePrefixAt c) ys) c)
        (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
          (idxOf (pp.toBlockShape.rulePrefixAt c) ys)))
    (hconcl : ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
          (·.2.2)) ys →
      blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval envC pp.toBlockShape
          (tgtRs out) ψ) (tgtClsU d Dc mc cvc pp.toBlockShape out ψ)
          (tgtClsNIdx d pp.toBlockShape out) ρ (prefOf (pp.toBlockShape.rulePrefixAt c) ys)
          (tagged c (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            (idxOf (pp.toBlockShape.rulePrefixAt c) ys)) (majOf ys))
        = interp V (consList ys ρ)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c))
    (hconclTy : ∀ xs : List V, ∀ c, c < (tgtRs out).length →
      ∀ i, i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      ∀ x, x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) i →
      interp V (consList (xs ++ (isOfW (tgtClsU d Dc mc cvc pp.toBlockShape out ψ c)
          (tgtClsNIdx d pp.toBlockShape out c) i ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large)) : V))
    (hstep : ∀ xs : List V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ (i : V) (fs : List V),
      i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c i j fs → ∀ gv : V,
      (∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ) (tgtRs out).length
          (genCallT (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ
            (fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j)) xs (c, j, fs) →
        app gv v ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out) ρ xs v) →
      interp V (consList (genIhvT (tgtRs out).length ρ pp.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
            (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ)
            (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ) xs c j fs gv)
          (consList (xs ++ fs) ρ)) (genRbAV g rd c j)
        ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out) ρ xs
          (tagged c i (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs)))
    (huniq : ∀ xs : List V,
      ∀ u, u ∈ˢ unionSet (tgtRs out).length
          (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs)
          (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs) →
      ∀ e e',
        graphDecG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          xs u e →
        graphDecG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          xs u e' →
      e = e' ∨ ∀ v v',
        v ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out) ρ xs u →
        v' ∈ˢ blockRecMot (tgtRs out).length
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out) ρ xs u →
        v = v')
    (hind : GenClassInd mpC.base2.acval envC pp.toBlockShape out d Dc mc cvc
      (fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j) ψ ρ)
    (hrule : ∀ a : Nat → V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j) (xs ++ fs) →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map (·.2.2))
        (xs ++ ((liftEsK (tgtRs out).length
              ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
                + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
              (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)).map
            (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)])))
    (hdec : ∀ a : Nat → V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j) (xs ++ fs) →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            ((liftEsK (tgtRs out).length
                ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
                  + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
              (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)).map
              (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))))) j fs ∧
        interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
          = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs)
    (hchain : ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < (tgtRs out).length → ∀ (is : List V) (x : V),
        xs.length = pp.toBlockShape.rulePrefixAt c' →
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c').map
          (·.2.2)) (xs ++ (is ++ [x])) →
        r (tagged c' (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c' is) x)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ fs : List V,
        xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
        SpineFit (chainFrame (tgtRs out).length a ρ)
          (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
          (xs ++ fs) →
        genIhvT (tgtRs out).length ρ pp.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
            (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ)
            (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ) xs c j fs
            (graph r (graphPredG (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
              (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
              (tgtRs out).length
              (genCallT (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ
                (fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j)) xs
              (c, j, fs)))
          = (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ c j).map
              (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ)))) :
    ∃ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) ∧
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ') ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun _ => genRbAV g rd) ψ,
        (pt : V) ∈ˢ interp V (chainFrame (tgtRs out).length a ρ) e := by
  obtain ⟨uOf, hbitsE, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have H := graphRecPre_coreR (ℓ := Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
      pp.toBlockShape.large)) (K := (tgtRs out).length) (ρ := ρ)
    (nCt := blockRecNCt (tgtRs out)) (rP := pp.toBlockShape.rulePrefixAt)
    (rds := blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (concl := blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (RecTy := blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
    (pdoms := blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (fdoms := tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
    (es := fun c j => liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
    (ihs := genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ)
    (mk := tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
    (Rb0 := genRbAV g rd)
    (ihv := genIhvT (tgtRs out).length ρ pp.toBlockShape.rulePrefixAt
            (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
            (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ)
            (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ))
    (call := genCallT (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ) ρ
                (fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j))
    (tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ)
    (tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (tgtClsNIdx d pp.toBlockShape out)
    (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ)
    (tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (fun c hc =>
      (recStage_tyPis (V := V) hμ mpC h (List.getElem?_eq_getElem hc)
        ψ).choose_spec.choose_spec.2.2.1)
    (blockRecOneElimLevel ψ (fun c hc => blockRecElimPin_run h hruns ψ hc) (hbitsE ψ))
    (fun c hc => blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc) ψ)
    hsplit hconcl hconclTy hstep huniq hind hrule hdec hchain
  obtain ⟨a, ha, hb⟩ := H
  refine ⟨a, ha, fun e he => hb e ?_⟩
  rw [genClsEqs_eq hμ h (fun ψ' => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd
    (genBit pp ψ') ψ') (fun _ => genRbAV g rd) ψ]
  exact he

end Cand

/-! ## 4. The rows, from the class facts

The producer's rows at the old class data follow from four facts about
the classes and the stored types (stated at one level assignment and
base frame):

* `GenClsSplit` — a fit of recursor `c`'s stored binder data is a major
  of class `c` (its index tuple in the index set, its major in the
  carrier, the index spine recovered from the tuple);
* `GenClsBack` — conversely every major of class `c` spells a fit of
  the stored binder data;
* `GenClsDec` — a spine fitting the rule's prefix and (declared) field
  domains decodes at class `c`: the fields hole-fit the constructor at
  the tuple of the declared index expressions' readings, which is in the
  index set and recovered from its tuple, and the constructor
  application reads to the injection, in the carrier there;
* the conclusion's typing at every fit of the stored binder data (the
  stage record's, `blockRecConcl_univ`). -/

section Rows

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

variable (mpC d Dc mc cvc pp out) in
/-- **The class split** at `(ψ, ρ)`: a fit of recursor `c`'s stored binder
data, split at the rule prefix and the class's index count, is a major of
class `c`, its index spine recovered from its tuple. -/
@[expose] def GenClsSplit (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ c, c < (tgtRs out).length → ∀ (xs is : List V) (x : V),
    xs.length = pp.toBlockShape.rulePrefixAt c → is.length = (tgtMajor out c).nIdx →
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map (·.2.2))
      (xs ++ (is ++ [x])) →
    tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c is
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c ∧
      x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c)
        (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c is) ∧
      isOfW (tgtClsU d Dc mc cvc pp.toBlockShape out ψ c) (tgtClsNIdx d pp.toBlockShape out c)
        (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c is) = is

variable (mpC d Dc mc cvc pp out) in
/-- **The converse**: every major of class `c` spells a fit of recursor
`c`'s stored binder data. -/
@[expose] def GenClsBack (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ c, c < (tgtRs out).length → ∀ (xs : List V) (i x : V),
    i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
    x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) i →
    SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map (·.2.2))
      (xs ++ (isOfW (tgtClsU d Dc mc cvc pp.toBlockShape out ψ c)
        (tgtClsNIdx d pp.toBlockShape out c) i ++ [x]))

variable (mpC d Dc mc cvc pp out) in
/-- **The decoding at the rule frame**: a spine fitting the rule's prefix
and declared field domains hole-fits constructor `j` of class `c` at the
tuple of the declared index expressions' readings — a tuple of the index
set, its spine recovered — and the constructor application reads to the
injection, which lies in the carrier there. -/
@[expose] def GenClsDec (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs fs : List V,
    xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) →
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
        (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
          ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ)))) j fs ∧
      tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
          ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ)))
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c ∧
      isOfW (tgtClsU d Dc mc cvc pp.toBlockShape out ψ c) (tgtClsNIdx d pp.toBlockShape out c)
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) ρ))))
        = (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ)) ∧
      interp V (consList (xs ++ fs) ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j)
        = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs ∧
      tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs
        ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c)
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) ρ))))

/-- The major index of a stored recursor is its rule prefix plus its
stored index count. -/
theorem genRec_mI {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) {c : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)} (hr : (tgtRs out)[c]? = some r) :
    pp.toBlockShape.majorIdxAt c = pp.toBlockShape.rulePrefixAt c + r.2.2.1 := by
  obtain ⟨R⟩ := h
  obtain ⟨rc, u, hrc, hcu, hE⟩ := R.tyGenAt hr
  obtain ⟨E⟩ := hE
  exact ConLeche.RecTyGen.mI_eq E

/-- The stored binder data's length: the rule prefix, the class's
indices, the major. -/
theorem genRds_length (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    {c : Nat} (hc : c < (tgtRs out).length) :
    (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = pp.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx + 1 := by
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨-, -, -, -, -, hlen, -⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
  rw [hlen, genRec_mI h hr]
  congr 2
  have hc' : c < out.length := by simpa [tgtRs] using hc
  simp [tgtRs, tgtMajor, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc']

/-- **Row `hsplit`**, from the class split. -/
theorem genRow_hsplit (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ : Nat → V) (hS : GenClsSplit pp out mpC d Dc mc cvc ψ ρ) :
    ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
          (·.2.2)) ys →
      (prefOf (pp.toBlockShape.rulePrefixAt c) ys).length = pp.toBlockShape.rulePrefixAt c ∧
      ys = prefOf (pp.toBlockShape.rulePrefixAt c) ys
        ++ (idxOf (pp.toBlockShape.rulePrefixAt c) ys ++ [majOf ys]) ∧
      tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c (idxOf (pp.toBlockShape.rulePrefixAt c) ys)
        ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ
          (prefOf (pp.toBlockShape.rulePrefixAt c) ys) c ∧
      majOf ys ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ
          (prefOf (pp.toBlockShape.rulePrefixAt c) ys) c)
        (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
          (idxOf (pp.toBlockShape.rulePrefixAt c) ys)) := by
  intro c hc ys hfit
  have hlen : ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
      (·.2.2)).length = pp.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx + 1 := by
    rw [List.length_map, genRds_length hμ h ψ hc]
  obtain ⟨xs, is, x, rfl, hxl, hisl, -, -, -⟩ := spineFit_split_three hlen hfit
  obtain ⟨hI, hC, -⟩ := hS c hc xs is x hxl hisl hfit
  rw [prefOf_split hxl, idxOf_split hxl, majOf_split]
  exact ⟨hxl, rfl, hI, hC⟩

/-- **Row `hconcl`**, from the class split. -/
theorem genRow_hconcl (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ : Nat → V) (hS : GenClsSplit pp out mpC d Dc mc cvc ψ ρ) :
    ∀ c, c < (tgtRs out).length →
      ∀ ys, SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
          (·.2.2)) ys →
      blockRecMot (tgtRs out).length (blockRecConclAV mpC.base2.acval envC pp.toBlockShape
          (tgtRs out) ψ) (tgtClsU d Dc mc cvc pp.toBlockShape out ψ)
          (tgtClsNIdx d pp.toBlockShape out) ρ (prefOf (pp.toBlockShape.rulePrefixAt c) ys)
          (tagged c (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            (idxOf (pp.toBlockShape.rulePrefixAt c) ys)) (majOf ys))
        = interp V (consList ys ρ)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) := by
  intro c hc ys hfit
  have hlen : ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
      (·.2.2)).length = pp.toBlockShape.rulePrefixAt c + (tgtMajor out c).nIdx + 1 := by
    rw [List.length_map, genRds_length hμ h ψ hc]
  obtain ⟨xs, is, x, rfl, hxl, hisl, -, -, -⟩ := spineFit_split_three hlen hfit
  obtain ⟨-, -, hret⟩ := hS c hc xs is x hxl hisl hfit
  rw [prefOf_split hxl, idxOf_split hxl, majOf_split, blockRecMot_tagged hc, hret]

/-- **The conclusion's typing at every fit of the stored binder data**
(the stage record's inferred sort, `blockRecConcl_univ`, at the pinned
elimination level). -/
theorem genRec_conclTy (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ : Nat → V) :
    ∀ c, c < (tgtRs out).length → ∀ ys,
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
        (·.2.2)) ys →
      interp V (consList ys ρ) (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large)) : V) := by
  intro c hc ys hfit
  obtain ⟨uOf, -, hruns⟩ := blockRecElimLevel_run (V := V) hμ mpC h
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  obtain ⟨fvs, conclE, sty, hop, hinf, hens⟩ := hruns c hc
  have hrd : (tgtRs out).getD c default = (tgtRs out)[c] := by
    rw [List.getD_eq_getElem?_getD, hr]; rfl
  rw [hrd] at hop
  have hsat : Sat V (((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map
      (·.2.2)).reverse) (consList ys ρ) := by
    simpa using sat_of_spineFit (Sat_nil V ρ) hfit
  have hu := blockRecConcl_univ hμ mpC h hr ψ hop hinf hens _ hsat
  rwa [blockRecElimPin_run h hruns ψ hc] at hu

/-- **Row `hconclTy`**, from the converse split. -/
theorem genRow_hconclTy (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ : Nat → V) (hB : GenClsBack pp out mpC d Dc mc cvc ψ ρ) :
    ∀ xs : List V, ∀ c, c < (tgtRs out).length →
      ∀ i, i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      ∀ x, x ∈ˢ app (tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) i →
      interp V (consList (xs ++ (isOfW (tgtClsU d Dc mc cvc pp.toBlockShape out ψ c)
          (tgtClsNIdx d pp.toBlockShape out c) i ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
        ∈ˢ (univ (Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim
          pp.toBlockShape.large)) : V) :=
  fun xs c hc i hi x hx => genRec_conclTy hμ h ψ ρ c hc _ (hB c hc xs i x hi hx)

/-- A spine fitting the chain-lifted prefix and field domains fits the
base ones, and the lifted index expressions and constructor application
read at the chain frame as the base ones at the base frame. -/
theorem genRec_chainBase (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ a : Nat → V) {c j : Nat} (hc : c < (tgtRs out).length) {xs fs : List V}
    (hxl : xs.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length)
    (hsp : SpineFit (chainFrame (tgtRs out).length a ρ)
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
      (xs ++ fs)) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) ∧
    (liftEsK (tgtRs out).length
        ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
        (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)).map
        (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ)))
      = (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
        (interp V (consList (xs ++ fs) ρ)) ∧
    interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
        (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
      = interp V (consList (xs ++ fs) ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j) := by
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hpK : liftDomsK (tgtRs out).length 0
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
      = blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c :=
    blockRecPdomsK_run (V := V) hμ mpC h hr ψ _
  have hbase := chainFit_base hpK hxl hsp
  have hfl : fs.length = (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length := by
    have := hbase.length_eq
    simp only [List.length_append, hxl] at this
    omega
  have hwl : (xs ++ fs).length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length := by
    rw [List.length_append, hxl, hfl]
  refine ⟨hbase, ?_, ?_⟩
  · simp only [liftEsK, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp]
    rw [← hwl, interp_liftN_chainFrame]
  · rw [tgtMkK, ← hwl, interp_liftN_chainFrame]

/-- **Row `hdec`**, from the decoding at the rule frame. -/
theorem genRow_hdec (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ : Nat → V) (hD : GenClsDec pp out mpC d Dc mc cvc ψ ρ) :
    ∀ a : Nat → V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j) (xs ++ fs) →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
          (tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
            ((liftEsK (tgtRs out).length
                ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
                  + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
              (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)).map
              (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))))) j fs ∧
        interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
          = tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs := by
  intro a c hc j hj xs fs hxl hsp
  obtain ⟨hbase, hes, hmk⟩ := genRec_chainBase hμ h ψ ρ a hc hxl hsp
  obtain ⟨hfit, -, -, hmkE, -⟩ := hD c hc j hj xs fs hxl hbase
  rw [hes, hmk]
  exact ⟨hfit, hmkE⟩

/-- **Row `hrule`**, from the decoding at the rule frame and the converse
split. -/
theorem genRow_hrule (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ : Nat → V) (hB : GenClsBack pp out mpC d Dc mc cvc ψ ρ)
    (hD : GenClsDec pp out mpC d Dc mc cvc ψ ρ) :
    ∀ a : Nat → V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j) (xs ++ fs) →
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).map (·.2.2))
        (xs ++ ((liftEsK (tgtRs out).length
              ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
                + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
              (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)).map
            (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)])) := by
  intro a c hc j hj xs fs hxl hsp
  obtain ⟨hbase, hes, hmk⟩ := genRec_chainBase hμ h ψ ρ a hc hxl hsp
  obtain ⟨-, hI, hret, hmkE, hC⟩ := hD c hc j hj xs fs hxl hbase
  have hfit := hB c hc xs _ _ hI hC
  rw [hret, ← hmkE] at hfit
  rw [hes, hmk]
  exact hfit

end Rows

end ConLeche.Model
