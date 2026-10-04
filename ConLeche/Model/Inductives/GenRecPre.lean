module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.ClassGenMinor
import ConLeche.Model.Inductives.ClassGenUniq
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockGradeRowsRun
import ConLeche.Model.Rules.InferSoundKit

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

/-! ## 3′. The `ih` chain and the step, over ANY classes

`genHchain`/`genHstep` (`ClassRecKit`, `ClassGenStep`) are stated at the
classes read off the generated type (`genIs`/`genCr`).  Here the same two
rows over any classes `Is`/`Cr`/`tup` whose majors are the stored binder
data's fits (`hsplitI`), at the generated calls `genCallT` and the graph's
`ih` values `genIhvT`. -/

section Generic

variable {K : Nat} {ρ : Nat → V} {rP nCt : Nat → Nat} {rds : Nat → List (Nat × Nat × AnnotTerm)}
  {Is Cr : List V → Nat → V} {tup : Nat → List V → V} {pdoms : Nat → List AnnotTerm}
  {fdoms : Nat → Nat → List AnnotTerm} {ihd : Nat → Nat → List IhDatum}

/-- The generated calls are the calls `genIhCallAt` names, tagged. -/
theorem genCallT_iff {xs : List V} {c j : Nat} {fs : List V} {v : V} :
    genCallT tup ρ ihd xs c j fs v ↔
      ∃ t is x, genIhCallAt ρ ihd xs c j fs t is x ∧ v = tagged t (tup t is) x := by
  constructor
  · rintro ⟨q, hq, bs, hbs, rfl⟩
    exact ⟨q.1, _, _, ⟨q, hq, rfl, bs, hbs, rfl, rfl⟩, rfl⟩
  · rintro ⟨t, is, x, ⟨q, hq, rfl, bs, hbs, rfl, rfl⟩, rfl⟩
    exact ⟨q, hq, bs, hbs, rfl⟩

set_option maxHeartbeats 1000000 in
/-- **`hchain` over any classes**: the graph's `ih` values are the `ih`
terms read at the chain — the `ih` terms read the chain only at their
calls' spines (`hihRead`), each call's spine fits its callee's stored
binder data (`hcallTy`), so it is a major of the callee's class
(`hsplitI`) and a predecessor, where the graph is the chain's recursor. -/
theorem genHchainG
    (hsplitI : ∀ c, c < K → ∀ (xs is : List V) (x : V), xs.length = rP c →
      SpineFit ρ ((rds c).map (·.2.2)) (xs ++ (is ++ [x])) →
      tup c is ∈ˢ Is xs c ∧ x ∈ˢ app (Cr xs c) (tup c is))
    (hcallTy : ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs fs : List V) (a : Nat → V),
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ∀ t is x, genIhCallAt ρ ihd xs c j fs t is x →
        t < K ∧ xs.length = rP t ∧ SpineFit ρ ((rds t).map (·.2.2)) (xs ++ (is ++ [x])))
    (hihRead : ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs fs : List V) (a a' : Nat → V),
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      (∀ t is x, genIhCallAt ρ ihd xs c j fs t is x →
        (xs ++ (is ++ [x])).foldl SetTheory.app (a t)
          = (xs ++ (is ++ [x])).foldl SetTheory.app (a' t)) →
      ((ihd c j).map (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length))).map
          (interp V (consList (xs ++ fs) (chainFrame K a ρ)))
        = ((ihd c j).map (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length))).map
          (interp V (consList (xs ++ fs) (chainFrame K a' ρ)))) :
    ∀ (a : Nat → V) (xs : List V) (r : V → V),
      (∀ c', c' < K → ∀ (is : List V) (x : V),
        xs.length = rP c' →
        SpineFit ρ ((rds c').map (·.2.2)) (xs ++ (is ++ [x])) →
        r (tagged c' (tup c' is) x) = (xs ++ (is ++ [x])).foldl SetTheory.app (a c')) →
      ∀ c, c < K → ∀ j, j < nCt c → ∀ fs : List V,
        xs.length = (pdoms c).length →
        SpineFit (chainFrame K a ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
        genIhvT K ρ rP rds tup
            (fun c j => (ihd c j).map
              (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length)))
            xs c j fs (graph r (graphPredG Is Cr K (genCallT tup ρ ihd) xs (c, j, fs)))
          = ((ihd c j).map
              (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length))).map
              (interp V (consList (xs ++ fs) (chainFrame K a ρ))) := by
  intro a xs r hr c hc j hj fs hxl hsp
  refine (hihRead c hc j hj xs fs a _ hxl hsp fun t is x hcall => ?_).symm
  obtain ⟨ht, hxlT, hfitT⟩ := hcallTy c hc j hj xs fs a hxl hsp t is x hcall
  have hfold := lamTowerA_fold (m := 1) Nat.one_ne_zero
    (g := fun sp _ => app (graph r (graphPredG Is Cr K (genCallT tup ρ ihd) xs (c, j, fs)))
      (tagged t (tup t (idxOf (rP t) sp)) (majOf sp)))
    (acc := []) hfitT
  rw [List.nil_append, idxOf_split hxlT, majOf_split] at hfold
  show _ = (xs ++ (is ++ [x])).foldl SetTheory.app (genFT ρ rP rds tup _ t)
  rw [genFT, hfold]
  obtain ⟨hi, hxC⟩ := hsplitI t ht xs is x hxlT hfitT
  have hpred : tagged t (tup t is) x ∈ˢ graphPredG Is Cr K (genCallT tup ρ ihd) xs (c, j, fs) :=
    mem_graphPredG.mpr ⟨tagged_mem_unionSet ht hi hxC, genCallT_iff.mpr ⟨t, is, x, hcall, rfl⟩⟩
  rw [app_graph hpred]
  exact (hr t ht is x hxlT hfitT).symm

set_option maxHeartbeats 2000000 in
/-- **`hstep` over any classes** (`genHstep`'s argument): the residue is
the minor premise applied to the fields and the graph's `ih` values; the
`ih` values inhabit their binders' types (each call is typed, hence a
predecessor, where the graph lands in the motive, which is the stored
conclusion, the callee's motive variable applied); the minor premise's
typing (`hminor`) lands the residue in `motive_c e⃗ mk`, which is the
kit's motive at the constructed element (`hdecInv`). -/
theorem genHstepG {uX nIdxX : Nat → Nat} {concl : Nat → AnnotTerm}
    {fit : List V → Nat → V → Nat → List V → Prop} {injX : Nat → Nat → List V → V}
    {es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
    (motPos : Nat → Nat) (minPos : Nat → Nat → Nat)
    (hpdl : ∀ c, c < K → (pdoms c).length = rP c)
    (hlenR : ∀ c, c < K → (rds c).length = rP c + nIdxX c + 1)
    (hmot : ∀ c, c < K → motPos c < rP c)
    (hmin : ∀ c, c < K → ∀ j, j < nCt c → minPos c j < rP c)
    (hIsPre : ∀ xs c i, c < K → i ∈ˢ Is xs c → SpineFit ρ (pdoms c) xs)
    (hsplitI : ∀ c, c < K → ∀ (xs is : List V) (x : V), xs.length = rP c →
      SpineFit ρ ((rds c).map (·.2.2)) (xs ++ (is ++ [x])) →
      tup c is ∈ˢ Is xs c ∧ x ∈ˢ app (Cr xs c) (tup c is) ∧ isOfW (uX c) (nIdxX c) (tup c is) = is)
    (hdecInv : ∀ c, c < K → ∀ j, j < nCt c → ∀ (xs : List V) (i : V) (fs : List V),
      i ∈ˢ Is xs c → fit xs c i j fs →
      SpineFit (consList xs ρ) (fdoms c j) fs ∧
      isOfW (uX c) (nIdxX c) i = (es c j).map (interp V (consList (xs ++ fs) ρ)) ∧
      ((es c j).map (interp V (consList (xs ++ fs) ρ))).length = nIdxX c ∧
      interp V (consList (xs ++ fs) ρ) (mk c j) = injX c j fs)
    (hcallTy : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length → SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs) →
      ∀ q ∈ ihd c j, ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs →
        q.1 < K ∧ xs.length = rP q.1 ∧
        SpineFit ρ ((rds q.1).map (·.2.2))
          (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
            ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2])))
    (hbelow : ∀ c, c < K → ∀ j, j < nCt c → ∀ q ∈ ihd c j,
      IhDatumBelow ((pdoms c).length + (fdoms c j).length) q)
    (hconclMot : ∀ c, c < K → ∀ (xs zs : List V) (x : V), xs.length = rP c →
      zs.length = nIdxX c →
      interp V (consList (xs ++ (zs ++ [x])) ρ) (concl c)
        = (zs ++ [x]).foldl SetTheory.app (xs.getD (motPos c) pt))
    (hminor : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs, SpineFit ρ (pdoms c) xs →
      ∀ fs, SpineFit (consList xs ρ) (fdoms c j) fs →
      ∀ hs : List V, hs.length = (ihd c j).length →
      (∀ (l : Nat) (q : IhDatum) (h : V), (ihd c j)[l]? = some q → hs[l]? = some h →
        h ∈ˢ interp V (consList (xs ++ fs) ρ)
          (genIhDomAV ((pdoms c).length + (fdoms c j).length) (motPos q.1) q)) →
      (fs ++ hs).foldl SetTheory.app (xs.getD (minPos c j) pt)
        ∈ˢ ((es c j).map (interp V (consList (xs ++ fs) ρ))
            ++ [interp V (consList (xs ++ fs) ρ) (mk c j)]).foldl SetTheory.app
            (xs.getD (motPos c) pt)) :
    ∀ xs : List V, ∀ c, c < K → ∀ j, j < nCt c → ∀ (i : V) (fs : List V),
      i ∈ˢ Is xs c → fit xs c i j fs → ∀ g : V,
      (∀ v, v ∈ˢ graphPredG Is Cr K (genCallT tup ρ ihd) xs (c, j, fs) →
        app g v ∈ˢ blockRecMot K concl uX nIdxX ρ xs v) →
      interp V (consList (genIhvT K ρ rP rds tup
            (fun c j => (ihd c j).map
              (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length)))
            xs c j fs g)
          (consList (xs ++ fs) ρ))
          (genRb0 (pdoms c).length (minPos c j) (fdoms c j).length (ihd c j).length)
        ∈ˢ blockRecMot K concl uX nIdxX ρ xs (tagged c i (injX c j fs)) := by
  intro xs c hc j hj i fs hi hfit g hg
  have hxs : SpineFit ρ (pdoms c) xs := hIsPre xs c i hc hi
  have hxl : xs.length = (pdoms c).length := hxs.length_eq
  obtain ⟨hfs, hisOf, hesl, hmkE⟩ := hdecInv c hc j hj xs i fs hi hfit
  have hsp : SpineFit ρ (pdoms c ++ fdoms c j) (xs ++ fs) := SpineFit.append hxs hfs
  have hfl : fs.length = (fdoms c j).length := hfs.length_eq
  generalize hDd : (pdoms c).length + (fdoms c j).length = D at *
  have hDlen : (xs ++ fs).length = D := by simp [hxl, hfl, ← hDd]
  have hagree : ∀ i, i < D →
      consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup g) ρ) i = consList (xs ++ fs) ρ i := by
    intro i hi'
    rw [consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega)]
  -- the graph's `ih` values inhabit their binders' types
  have hih : ∀ q ∈ ihd c j,
      interp V (consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup g) ρ))
          (genIhAV K (pdoms c).length D q)
        ∈ˢ interp V (consList (xs ++ fs) ρ) (genIhDomAV D (motPos q.1) q) := by
    intro q hq
    obtain ⟨hbT, hbA⟩ := hbelow c hc j hj q hq
    rw [hDd] at hbT hbA
    refine lamTower_mem_piTower q.2.1 hbT hagree fun bs hbs => ?_
    have hbl : bs.length = q.2.1.length := by rw [hbs.length_eq, List.length_map]
    have hargR : ∀ e ∈ q.2.2.1 ++ [q.2.2.2],
        interp V (consList bs (consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup g) ρ))) e
          = interp V (consList bs (consList (xs ++ fs) ρ)) e :=
      fun e he => interp_congr_below V e _ _ _ (hbA e he)
        (fun i hi' => consList_congr_below bs hagree i (by rw [hbl]; exact hi'))
    obtain ⟨is, his_def⟩ : ∃ is, is = q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ))) :=
      ⟨_, rfl⟩
    obtain ⟨x, hx_def⟩ : ∃ x, x = interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2 :=
      ⟨_, rfl⟩
    have hbsρ : SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs := hbs
    obtain ⟨ht, hxlT, hfitT⟩ := hcallTy c hc j hj xs fs hxl hsp q hq bs hbsρ
    rw [← his_def, ← hx_def] at hfitT
    have hcall : genIhCallAt ρ ihd xs c j fs q.1 is x := ⟨q, hq, rfl, bs, hbsρ, his_def, hx_def⟩
    -- the body: the chain's recursor at the call's spine, i.e. the graph at the call
    have hbody : interp V (consList bs (consList (xs ++ fs)
          (chainFrame K (genFT ρ rP rds tup g) ρ)))
        (AnnotTerm.mkAppN (.bvar (D + q.2.1.length + (K - 1 - q.1)))
          (prefVarsAV (pdoms c).length (D - (pdoms c).length + q.2.1.length)
            ++ (q.2.2.1 ++ [q.2.2.2])))
        = app g (tagged q.1 (tup q.1 is) x) := by
      rw [interp_mkAppN, ← List.foldl_map]
      have hhead : consList bs (consList (xs ++ fs) (chainFrame K (genFT ρ rP rds tup g) ρ))
          (D + q.2.1.length + (K - 1 - q.1)) = genFT ρ rP rds tup g q.1 := by
        rw [← consList_append, show D + q.2.1.length + (K - 1 - q.1)
          = (K - 1 - q.1) + (xs ++ fs ++ bs).length by simp [hxl, hfl, hbl, ← hDd]; omega,
          consList_apply_add, chainFrame_apply ht]
      rw [show interp V (consList bs (consList (xs ++ fs)
          (chainFrame K (genFT ρ rP rds tup g) ρ)))
          (.bvar (D + q.2.1.length + (K - 1 - q.1))) = genFT ρ rP rds tup g q.1 from hhead]
      have hpv : (prefVarsAV (pdoms c).length (D - (pdoms c).length + q.2.1.length)).map
          (interp V (consList bs (consList (xs ++ fs)
            (chainFrame K (genFT ρ rP rds tup g) ρ)))) = xs := by
        have h := interp_prefVarsAV (V := V) (xs := xs) (bs := fs ++ bs)
          (ρ := chainFrame K (genFT ρ rP rds tup g) ρ) hxl
        rw [← List.append_assoc, consList_append] at h
        simpa [hbl, hfl, ← hDd, Nat.add_sub_cancel_left] using h
      rw [List.map_append, hpv, List.map_congr_left hargR]
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [← his_def, ← hx_def]
      have hfold := lamTowerA_fold (m := 1) Nat.one_ne_zero
        (g := fun sp _ => app g (tagged q.1 (tup q.1 (idxOf (rP q.1) sp)) (majOf sp)))
        (acc := []) hfitT
      rw [List.nil_append, idxOf_split hxlT, majOf_split] at hfold
      rw [genFT, hfold]
    -- the graph lands in the motive at the call
    obtain ⟨hiT, hxC, hretT⟩ := hsplitI q.1 ht xs is x hxlT hfitT
    have hpred : tagged q.1 (tup q.1 is) x ∈ˢ graphPredG Is Cr K (genCallT tup ρ ihd) xs
        (c, j, fs) :=
      mem_graphPredG.mpr ⟨tagged_mem_unionSet ht hiT hxC, genCallT_iff.mpr ⟨_, _, _, hcall, rfl⟩⟩
    have hgv := hg _ hpred
    have hisl : is.length = nIdxX q.1 := by
      have := hfitT.length_eq
      simp only [List.length_append, List.length_singleton, List.length_map, hlenR q.1 ht,
        hxlT] at this
      omega
    rw [blockRecMot_tagged ht, hretT, hconclMot q.1 ht xs is x hxlT hisl] at hgv
    show interp V _ (AnnotTerm.mkAppN
        (.bvar (D + q.2.1.length + (K - 1 - q.1)))
          (prefVarsAV (pdoms c).length (D - (pdoms c).length + q.2.1.length)
            ++ (q.2.2.1 ++ [q.2.2.2])))
      ∈ˢ interp V (consList bs (consList (xs ++ fs) ρ))
      (AnnotTerm.mkAppN (.bvar (D + q.2.1.length - 1 - motPos q.1))
        (q.2.2.1 ++ [q.2.2.2]))
    rw [hbody, interp_mkAppN, ← List.foldl_map]
    have hmt := hmot q.1 ht
    have hhd : interp V (consList bs (consList (xs ++ fs) ρ))
        (.bvar (D + q.2.1.length - 1 - motPos q.1)) = xs.getD (motPos q.1) pt := by
      show consList bs (consList (xs ++ fs) ρ) _ = _
      rw [← consList_append, List.append_assoc,
        show D + q.2.1.length - 1 - motPos q.1
          = (fs ++ bs).length + xs.length - 1 - motPos q.1 by simp [hxl, hfl, hbl, ← hDd]; omega]
      exact consList_prefix_getD (by omega)
    rw [hhd]
    simp only [List.map_append, List.map_cons, List.map_nil]
    rw [← his_def, ← hx_def]
    exact hgv
  -- the residue: the minor premise at the fields and the `ih` values
  obtain ⟨hsV, hhsV⟩ : ∃ hsV, hsV = genIhvT K ρ rP rds tup
      (fun c j => (ihd c j).map (genIhAV K (pdoms c).length ((pdoms c).length + (fdoms c j).length)))
      xs c j fs g := ⟨_, rfl⟩
  rw [← hhsV]
  have hsVl : hsV.length = (ihd c j).length := by rw [hhsV]; simp [genIhvT]
  have hmin' := hmin c hc j hj
  have hpl := hpdl c hc
  have key := interp_genRb0 (ρ := ρ) (xs := xs) (fs := fs) (hs := hsV) (minPos := minPos c j)
    (by omega)
  rw [hxl, hfl, hsVl] at key
  rw [key]
  have hres := hminor c hc j hj xs hxs fs hfs hsV hsVl fun l q h hq hh => by
    rw [hhsV] at hh
    simp only [genIhvT, List.map_map, List.getElem?_map, hq, Option.map_some,
      Option.some.injEq] at hh
    subst hh
    rw [← hDd] at hih
    exact hih q (List.mem_of_getElem? hq)
  -- the motive at the constructor
  rw [blockRecMot_tagged hc, hisOf, hconclMot c hc xs _ _ (by rw [hxl, hpl]) hesl, ← hmkE]
  exact hres

end Generic

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

variable (mpC d Dc mc cvc pp out) in
/-- **The decoding's inverse**: a hole fit of constructor `j` of class `c`
at a tuple of the index set is a fit of the declared field domains, and
the tuple is the declared index expressions' readings'. -/
@[expose] def GenClsDecInv (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ (xs : List V) (i : V) (fs : List V),
    i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c i j fs →
    SpineFit (consList xs ρ) (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) fs ∧
    i = tgtClsTup d Dc mc cvc pp.toBlockShape out ψ c
      ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
        (interp V (consList (xs ++ fs) ρ)))

/-- A class's index set is guarded by the rule prefix's fit. -/
theorem tgtClsIs_prefix {ψ : Name → Nat} {ρ : Nat → V} {xs : List V} {c : Nat} {i : V}
    (hi : i ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) :
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs := by
  classical
  unfold tgtClsIs at hi
  by_cases hg : tgtClsG d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
  · unfold tgtClsG at hg
    by_cases hm : (tgtMajor out c).member.isSome = true
    · rw [ite_eq_left hm] at hg; exact hg.2
    · rw [ite_eq_right hm] at hg; exact hg
  · rw [ite_eq_right hg] at hi; exact absurd hi (not_mem_empty _)

/-- An index tuple's spine has the class's index count. -/
theorem isOfW_length (u n : Nat) (t : V) : (isOfW u n t).length = n := by
  unfold isOfW
  split
  · simp
  · exact ConLeche.SetTheory.Tower.projList_length n t

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

/-- **Row `huniq`**, from the classes' recorded clauses (`genUniq`): the
class fit is the clause's hole fit at the carrier and the injection the
clause's, definitionally; at `ℓ = 0` the conclusion's typing; at a
`Prop`-valued class under a nonzero elimination level, the licence. -/
theorem genRow_huniq (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ : Nat → V) (hB : GenClsBack pp out mpC d Dc mc cvc ψ ρ)
    (hDin : ∀ c, c < (tgtRs out).length → tgtClsD d Dc out c ∈ mpC.lfpBlocks)
    (hmN : ∀ c, c < (tgtRs out).length → tgtClsM mc pp.toBlockShape out c < (tgtClsD d Dc out c).N)
    (hlic : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0 →
      ∀ xs, ∀ c, c < (tgtRs out).length →
      (tgtClsD d Dc out c).w (tgtClsψ cvc out ψ c) = 0 →
      ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      ∀ j fs j' fs',
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c t j fs →
      tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c t j' fs' →
      j = j' ∧ fs = fs') :
    ∀ xs : List V,
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
        v = v' := by
  intro xs
  exact genUniq (acval := mpC.base2.acval) (nCt := blockRecNCt (tgtRs out))
    (fun c => tgtClsD d Dc out c) (fun c => tgtClsψ cvc out ψ c)
    (fun c => tgtClsFr d mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c)
    (fun c => tgtClsM mc pp.toBlockShape out c)
    (fun c hc _ _ => (mpC.lfp_ok _ (hDin c hc)).1) (fun c hc _ _ => hmN c hc)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ hf => hf)
    (genRow_hconclTy hμ h ψ ρ hB xs) (hlic · xs)

section RowsIh

variable {g : ClassGen} {rd : ClassRead}

/-- The generated `ih` terms are the generic ones at the rule frame's
depths: the shared prefix is the rule prefix (`hgpre`), the constructor's
field count the declared fields' (`hnF`). -/
theorem genIhsAV_eq (ψ : Name → Nat) {c j : Nat}
    (hgpre : g.pre.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length)
    (hnF : (genCtorAt g rd c j).nF = (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
    (K : Nat) (fl : Nat)
    (hfl : fl = (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length) :
    genIhsAV mpC.base2.acval envC K g rd (genBit pp ψ) ψ c j
      = (genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j).map
        (genIhAV K (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length + fl)) := by
  rw [genIhsAV, hgpre, hnF, hfl]

set_option maxHeartbeats 2000000 in
/-- **Row `hchain`**, from the `ih` calls' typing at the rule frame
(`hcallTy`), the class split and the `ih` data's bounds. -/
theorem genRow_hchain (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ : Nat → V) (hS : GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    (hgpre : ∀ c, c < (tgtRs out).length → g.pre.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length)
    (hnF : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      (genCtorAt g rd c j).nF = (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
    (hcal : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j, q.1 < (tgtRs out).length)
    (hbelow : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j,
        IhDatumBelow ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length) q)
    (hcallTy : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j,
      ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs →
        q.1 < (tgtRs out).length ∧ xs.length = pp.toBlockShape.rulePrefixAt q.1 ∧
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ q.1).map
            (·.2.2))
          (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
            ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2]))) :
    ∀ (a : Nat → V) (xs : List V) (r : V → V),
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
              (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length a ρ))) := by
  intro a xs r hr c hc j hj fs hxl hsp
  have hih : ∀ c', c' < (tgtRs out).length → ∀ j', j' < blockRecNCt (tgtRs out) c' →
      genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ c' j'
        = (genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c' j').map
          (genIhAV (tgtRs out).length
            (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c').length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c').length
              + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c'
                j').length)) :=
    fun c' hc' j' hj' => genIhsAV_eq ψ (hgpre c' hc') (hnF c' hc' j' hj') _ _
      (by simp [tgtFdomsK, liftDomsK_length])
  -- the chain-frame call typing, from the base one
  have hcallC : ∀ c', c' < (tgtRs out).length → ∀ j', j' < blockRecNCt (tgtRs out) c' →
      ∀ (xs fs : List V) (a : Nat → V),
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c').length →
      SpineFit (chainFrame (tgtRs out).length a ρ)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c'
          ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c' j')
        (xs ++ fs) →
      ∀ t is x, genIhCallAt ρ (fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j)
          xs c' j' fs t is x →
        t < (tgtRs out).length ∧ xs.length = pp.toBlockShape.rulePrefixAt t ∧
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ t).map
          (·.2.2)) (xs ++ (is ++ [x])) := by
    intro c' hc' j' hj' xs fs a hxl hsp t is x hcall
    obtain ⟨hbase, -, -⟩ := genRec_chainBase hμ h ψ ρ a hc' hxl hsp
    obtain ⟨q, hq, rfl, bs, hbs, rfl, rfl⟩ := hcall
    exact hcallTy c' hc' j' hj' xs fs hxl hbase q hq bs hbs
  -- `hihRead`, by construction
  have hpre : ∀ c', (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c')
      = genPdoms (fun c'' => (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ
          c'').map fun D => ((0 : Nat), (0 : Nat), D)) c' := by
    intro c'; simp [genPdoms, List.map_map, Function.comp_def]
  have hread := genIhs_hihRead (K := (tgtRs out).length) (ρ := ρ) (nCt := blockRecNCt (tgtRs out))
    (pre := fun c'' => (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ
          c'').map fun D => ((0 : Nat), (0 : Nat), D))
    (fdoms := tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
    (ihd := fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j) hcal
    (fun c' hc' j' hj' q hq => by
      rw [← hpre c']
      simpa [tgtFdomsK, liftDomsK_length] using hbelow c' hc' j' hj' q hq)
  have H := genHchainG (K := (tgtRs out).length) (ρ := ρ) (rP := pp.toBlockShape.rulePrefixAt)
    (nCt := blockRecNCt (tgtRs out))
    (rds := blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (Is := tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (Cr := tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (tup := tgtClsTup d Dc mc cvc pp.toBlockShape out ψ)
    (pdoms := blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (fdoms := tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
    (ihd := fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j)
    (fun c' hc' xs is x hxl hfit => by
      have hisl : is.length = (tgtMajor out c').nIdx := by
        have := hfit.length_eq
        simp only [List.length_append, List.length_singleton, List.length_map,
          genRds_length hμ h ψ hc', hxl] at this
        omega
      obtain ⟨h1, h2, -⟩ := hS c' hc' xs is x hxl hisl hfit
      exact ⟨h1, h2⟩)
    hcallC
    (fun c' hc' j' hj' xs fs a a' hxl hsp hcall => by
      have := hread c' hc' j' hj' xs fs a a' (by rw [hxl, hpre c']) (by rw [← hpre c']; exact hsp)
        hcall
      rwa [← hpre c'] at this)
    a xs r hr c hc j hj fs hxl hsp
  rw [genIhvT, hih c hc j hj]
  rw [genIhvT] at H
  exact H

set_option maxHeartbeats 2000000 in
/-- **Row `hstep`**, from the minor premise's typing at the rule frame
(`hminor`), the stored conclusion as the motive applied (`hconclMot`), the
`ih` calls' typing, the class split and the decoding both ways. -/
theorem genRow_hstep (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) (ψ : Name → Nat)
    (ρ : Nat → V) (hS : GenClsSplit pp out mpC d Dc mc cvc ψ ρ)
    (hD : GenClsDec pp out mpC d Dc mc cvc ψ ρ) (hDI : GenClsDecInv pp out mpC d Dc mc cvc ψ ρ)
    (hnIdx : ∀ c, c < (tgtRs out).length →
      tgtClsNIdx d pp.toBlockShape out c = (tgtMajor out c).nIdx)
    (hgpre : ∀ c, c < (tgtRs out).length → g.pre.length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length)
    (hnF : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      (genCtorAt g rd c j).nF = (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
    (hmot : ∀ c, c < (tgtRs out).length →
      classMotPos g (genClsOf rd c) < pp.toBlockShape.rulePrefixAt c)
    (hmin : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      g.nP + genMinorSlot g rd c j < pp.toBlockShape.rulePrefixAt c)
    (hbelow : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j,
        IhDatumBelow ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length) q)
    (hcallTy : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ xs fs : List V,
      xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) →
      ∀ q ∈ genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j,
      ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs →
        q.1 < (tgtRs out).length ∧ xs.length = pp.toBlockShape.rulePrefixAt q.1 ∧
        SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ q.1).map
            (·.2.2))
          (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
            ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2])))
    (hconclMot : ∀ c, c < (tgtRs out).length → ∀ (xs zs : List V) (x : V),
      xs.length = pp.toBlockShape.rulePrefixAt c → zs.length = (tgtMajor out c).nIdx →
      interp V (consList (xs ++ (zs ++ [x])) ρ)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
        = (zs ++ [x]).foldl SetTheory.app (xs.getD (classMotPos g (genClsOf rd c)) pt))
    (hminor : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs →
      ∀ fs, SpineFit (consList xs ρ) (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) fs →
      ∀ hs : List V, hs.length = (genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j).length →
      (∀ (l : Nat) (q : IhDatum) (hv : V),
        (genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j)[l]? = some q → hs[l]? = some hv →
        hv ∈ˢ interp V (consList (xs ++ fs) ρ)
          (genIhDomAV ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (classMotPos g (genClsOf rd q.1)) q)) →
      (fs ++ hs).foldl SetTheory.app (xs.getD (g.nP + genMinorSlot g rd c j) pt)
        ∈ˢ ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
              (interp V (consList (xs ++ fs) ρ))
            ++ [interp V (consList (xs ++ fs) ρ)
              (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j)]).foldl SetTheory.app
            (xs.getD (classMotPos g (genClsOf rd c)) pt)) :
    ∀ xs : List V, ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
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
          (tagged c i (tgtClsInj d Dc mc cvc pp.toBlockShape out ψ c j fs)) := by
  intro xs c hc j hj i fs hi hfit gv hg
  have hpdl : ∀ c', c' < (tgtRs out).length →
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c').length
        = pp.toBlockShape.rulePrefixAt c' :=
    fun c' hc' => blockRulePdomsAV_length hμ mpC h (List.getElem?_eq_getElem hc') ψ
  have H := genHstepG (K := (tgtRs out).length) (ρ := ρ) (rP := pp.toBlockShape.rulePrefixAt)
    (nCt := blockRecNCt (tgtRs out))
    (rds := blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (Is := tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (Cr := tgtClsCr d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (tup := tgtClsTup d Dc mc cvc pp.toBlockShape out ψ)
    (pdoms := blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (fdoms := fun c j => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)
    (ihd := fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j)
    (uX := tgtClsU d Dc mc cvc pp.toBlockShape out ψ) (nIdxX := tgtClsNIdx d pp.toBlockShape out)
    (concl := blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (fit := tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
    (injX := tgtClsInj d Dc mc cvc pp.toBlockShape out ψ)
    (es := fun c j => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)
    (mk := fun c j => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j)
    (fun r => classMotPos g (genClsOf rd r)) (fun c j => g.nP + genMinorSlot g rd c j)
    hpdl
    (fun c' hc' => by rw [genRds_length hμ h ψ hc', hnIdx c' hc'])
    hmot hmin
    (fun xs c' i _ hi => tgtClsIs_prefix hi)
    (fun c' hc' xs is x hxl hfit => by
      have hisl : is.length = (tgtMajor out c').nIdx := by
        have := hfit.length_eq
        simp only [List.length_append, List.length_singleton, List.length_map,
          genRds_length hμ h ψ hc', hxl] at this
        omega
      exact hS c' hc' xs is x hxl hisl hfit)
    (fun c' hc' j' hj' xs i fs hi hfit => by
      obtain ⟨hfs, rfl⟩ := hDI c' hc' j' hj' xs i fs hi hfit
      have hxs := tgtClsIs_prefix hi
      obtain ⟨-, -, hret, hmkE, -⟩ := hD c' hc' j' hj' xs fs hxs.length_eq (SpineFit.append hxs hfs)
      refine ⟨hfs, hret, ?_, hmkE⟩
      rw [← hret, isOfW_length])
    hcallTy hbelow
    (fun c' hc' xs zs x hxl hzl => hconclMot c' hc' xs zs x hxl (by rw [hzl, hnIdx c' hc']))
    hminor
    xs c hc j hj i fs hi hfit gv hg
  have hih := genIhsAV_eq (mpC := mpC) (envC := envC) (pp := pp) (out := out) (g := g) (rd := rd)
    ψ (hgpre c hc) (hnF c hc j hj) (tgtRs out).length _ rfl
  have hRb : genRbAV g rd c j = genRb0
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      (g.nP + genMinorSlot g rd c j)
      (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length
      (genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j).length := by
    rw [genRbAV, hgpre c hc, hnF c hc j hj]
    simp [genIhdAV]
  rw [genIhvT, hih, hRb]
  rw [genIhvT] at H
  exact H

end RowsIh

set_option maxHeartbeats 4000000 in
/-- **`hEq`'s grading half at the generated components** (the old
`tgtRecEqs_hEqAny`'s argument): the frame from its grading (`hframe`,
the declared field domains bounded, `hfdB`), the left-hand side an
application chain along the recursor's stored type (the rule's spine
fits it, `genRow_hrule`, its arguments graded, `hargs`), the right-hand
side from the `ih` terms' and the residue's grading at typed tuples
(`hrhs`). -/
theorem genRecEqs_wd (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR) {g : ClassGen}
    {rd : ClassRead} (ψ : Name → Nat) (ρ : Nat → V)
    (hB : GenClsBack pp out mpC d Dc mc cvc ψ ρ) (hD : GenClsDec pp out mpC d Dc mc cvc ψ ρ)
    (hfdB : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      FieldsBelow (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
    (hframe : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
      ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length →
      ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
          ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).take l) ys →
        WellDenoted V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD l default))
    (hargs : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
      (∀ e ∈ tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j,
        WellDenotedV V (consList ys ρ) e) ∧
      WellDenotedV V (consList ys ρ) (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
    (hrhs : ∀ rs : List V, rs.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ ys : List V,
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) ys →
      (∀ v ∈ genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ c j,
        WellDenotedV V (consList ys (consList rs ρ)) v) ∧
      WellDenotedV V (consList ((genIhsAV mpC.base2.acval envC (tgtRs out).length g rd
          (genBit pp ψ) ψ c j).map (interp V (consList ys (consList rs ρ)))) (consList ys ρ))
        (genRbAV g rd c j)) :
    ∀ (rs : List V), rs.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ) (fun _ => genRbAV g rd) ψ,
        WellDenoted V (consList rs ρ) e := by
  intro tup hlen htyp e he
  rw [← genClsEqs_eq hμ h (fun ψ' => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd
    (genBit pp ψ') ψ') (fun _ => genRbAV g rd) ψ] at he
  refine (hEq_iotaEqsAV_of (fun as hl ht c hc j hj => ?_) tup hlen htyp e he).2
  have hr : (tgtRs out)[c]? = some (tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hpl := blockRulePdomsAV_length hμ mpC h hr ψ
  have hfdK : tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j
      = tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j := by
    rw [tgtFdomsK]
    exact liftDomsK_eq_self_of_bounded _ _ (fieldsBelow_getD (hfdB c hc j hj))
  have hch := consList_eq_chainFrame (V := V) hl ρ
  refine ⟨?_, fun ys hys => ?_⟩
  · rw [hfdK]
    exact fieldsOkB_zero_of_spineGrading _ (fun l hl' ys hys =>
      hframe c hc j hj l hl' (consList as ρ) ys hys)
  obtain ⟨xs, fs, rfl, hxs, hfs⟩ := spineFit_append_split hys
  have hxl := hxs.length_eq
  have hsp : SpineFit (chainFrame (tgtRs out).length (fun c => as.getD c pt) ρ)
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)
      (xs ++ fs) := by rw [← hch]; exact hys
  obtain ⟨hbase, hesE, hmkE⟩ := genRec_chainBase hμ h ψ ρ (fun c => as.getD c pt) hc hxl hsp
  have hfl : fs.length = (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length := by
    have := hbase.length_eq
    simp only [List.length_append, hxl] at this
    omega
  have hwl : (xs ++ fs).length
      = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length := by
    rw [List.length_append, hxl, hfl]
  obtain ⟨hE, hMk⟩ := hargs c hc j hj (xs ++ fs) hbase
  refine ⟨?_, ?_⟩
  · -- the left-hand side: an application chain along the recursor's type
    have hfit := genRow_hrule hμ h ψ ρ hB hD (fun c => as.getD c pt) c hc j hj xs fs hxl hsp
    have hflK : (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
        = fs.length := by rw [hfdK, hfl]
    have hpv : (prefVarsAV
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length).map
          (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
            (fun c => as.getD c pt) ρ)))
        = xs := by
      rw [hflK]; exact interp_prefVarsAV hxl
    have hhead : interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
          (fun c => as.getD c pt) ρ))
        (.bvar ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          + ((tgtRs out).length - 1 - c))) = as.getD c pt := by
      show consList (xs ++ fs) _ _ = _
      rw [show (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          + ((tgtRs out).length - 1 - c) = ((tgtRs out).length - 1 - c) + (xs ++ fs).length from by
            rw [List.length_append, hxl, hflK]; omega,
        consList_apply_add, chainFrame_apply hc]
    obtain ⟨-, -, -, -, hTyE, -, -, -, -, hwdTy⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
    have hTF := teleFit_mkPisAV_of_spineFit
      (B := blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) hfit
    rw [← hTyE] at hTF
    have hvals : (prefVarsAV
            (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          ++ liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)
          ++ [tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j]).map
          (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
            (fun c => as.getD c pt) ρ)))
        = xs ++ ((liftEsK (tgtRs out).length
            ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
              + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
            (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j)).map
            (interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
              (fun c => as.getD c pt) ρ)))
          ++ [interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
              (fun c => as.getD c pt) ρ))
            (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j)]) := by
      rw [List.map_append, List.map_append, hpv, List.map_cons, List.map_nil, List.append_assoc]
    rw [← hvals] at hTF
    have hmem' : interp V (consList (xs ++ fs) (chainFrame (tgtRs out).length
          (fun c => as.getD c pt) ρ))
        (.bvar ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          + ((tgtRs out).length - 1 - c)))
        ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c) := by
      rw [hhead]; exact ht c hc
    rw [← hch] at hTF hmem'
    refine (Rules.wellDenotedV_mkAppN_of_fit _
      (f := .bvar ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
          + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c j).length
          + ((tgtRs out).length - 1 - c))) (hwdTy ρ) ⟨trivial, trivial⟩ (fun x hx => ?_)
      hmem' hTF).1.1
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
        exact ⟨trivial, trivial⟩
      · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
        rw [hch, ← hwl, wellDenotedV_liftN_chainFrame]
        exact hE e he
    · rw [List.mem_singleton] at hx
      rw [hx, tgtMkK, hch, ← hwl, wellDenotedV_liftN_chainFrame]
      exact hMk
  · -- the residue, at the `ih` values
    obtain ⟨hIv, hRv⟩ := hrhs as hl ht c hc j hj (xs ++ fs) hbase
    rw [wd_instsAV (fun v hv => (hIv v hv).1)]
    have key := (wellDenotedV_liftN_chainFrame (K := (tgtRs out).length)
      (a := fun c => as.getD c pt) (ρ := ρ)
      ((xs ++ fs) ++ (genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ c
        j).map (interp V (consList (xs ++ fs) (consList as ρ))))
      (genRbAV g rd c j)).mpr (by simpa only [consList_append] using hRv)
    rw [← hch] at key
    simp only [consList_append, List.length_append, List.length_map] at key ⊢
    rw [← hxl, ← hfs.length_eq]
    exact key.1

end Rows

/-! ## 5. The family premise, assembled -/

section Assembly

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V μ envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal} {g : ClassGen} {rd : ClassRead}

variable (pp out mpC d Dc mc cvc g rd) in
/-- **What the candidate still asks**, at one level assignment and base
frame: the class facts (split both ways, decoding both ways), the
classes' recorded clauses, the elimination licence, the generated `ih`s'
data (callees, bounds, calls' typing), the stored conclusion as the
motive applied, the minor premise's typing at the rule frame, the
prefix positions, and the class induction (lane B2's interface). -/
structure GenPreHyps (ψ : Name → Nat) (ρ : Nat → V) : Prop where
  split : GenClsSplit pp out mpC d Dc mc cvc ψ ρ
  back : GenClsBack pp out mpC d Dc mc cvc ψ ρ
  dec : GenClsDec pp out mpC d Dc mc cvc ψ ρ
  decInv : GenClsDecInv pp out mpC d Dc mc cvc ψ ρ
  nIdx : ∀ c, c < (tgtRs out).length →
    tgtClsNIdx d pp.toBlockShape out c = (tgtMajor out c).nIdx
  din : ∀ c, c < (tgtRs out).length → tgtClsD d Dc out c ∈ mpC.lfpBlocks
  mN : ∀ c, c < (tgtRs out).length → tgtClsM mc pp.toBlockShape out c < (tgtClsD d Dc out c).N
  lic : Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) ≠ 0 →
    ∀ xs, ∀ c, c < (tgtRs out).length →
    (tgtClsD d Dc out c).w (tgtClsψ cvc out ψ c) = 0 →
    ∀ t, t ∈ˢ tgtClsIs d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
    ∀ j fs j' fs',
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c t j fs →
    tgtClsFit d Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c t j' fs' →
    j = j' ∧ fs = fs'
  gpre : ∀ c, c < (tgtRs out).length → g.pre.length
    = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
  nF : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    (genCtorAt g rd c j).nF = (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length
  mot : ∀ c, c < (tgtRs out).length →
    classMotPos g (genClsOf rd c) < pp.toBlockShape.rulePrefixAt c
  min : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    g.nP + genMinorSlot g rd c j < pp.toBlockShape.rulePrefixAt c
  cal : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ q ∈ genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j, q.1 < (tgtRs out).length
  below : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ q ∈ genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j,
      IhDatumBelow ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length) q
  callTy : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c →
    ∀ xs fs : List V,
    xs.length = (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length →
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs) →
    ∀ q ∈ genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j,
    ∀ bs, SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs →
      q.1 < (tgtRs out).length ∧ xs.length = pp.toBlockShape.rulePrefixAt q.1 ∧
      SpineFit ρ ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ q.1).map
          (·.2.2))
        (xs ++ (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))
          ++ [interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2]))
  conclMot : ∀ c, c < (tgtRs out).length → ∀ (xs zs : List V) (x : V),
    xs.length = pp.toBlockShape.rulePrefixAt c → zs.length = (tgtMajor out c).nIdx →
    interp V (consList (xs ++ (zs ++ [x])) ρ)
        (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c)
      = (zs ++ [x]).foldl SetTheory.app (xs.getD (classMotPos g (genClsOf rd c)) pt)
  minor : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ xs,
    SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) xs →
    ∀ fs, SpineFit (consList xs ρ) (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) fs →
    ∀ hs : List V, hs.length = (genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j).length →
    (∀ (l : Nat) (q : IhDatum) (hv : V),
      (genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j)[l]? = some q → hs[l]? = some hv →
      hv ∈ˢ interp V (consList (xs ++ fs) ρ)
        (genIhDomAV ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
          (classMotPos g (genClsOf rd q.1)) q)) →
    (fs ++ hs).foldl SetTheory.app (xs.getD (g.nP + genMinorSlot g rd c j) pt)
      ∈ˢ ((tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).map
            (interp V (consList (xs ++ fs) ρ))
          ++ [interp V (consList (xs ++ fs) ρ)
            (tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ c j)]).foldl SetTheory.app
          (xs.getD (classMotPos g (genClsOf rd c)) pt)
  ind : GenClassInd mpC.base2.acval envC pp.toBlockShape out d Dc mc cvc
    (fun c j => genIhdAV mpC.base2.acval envC g rd (genBit pp ψ) ψ c j) ψ ρ

set_option maxHeartbeats 4000000 in
/-- **The candidate, from `GenPreHyps`.** -/
theorem genRecPre_hCandH (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (ψ : Name → Nat) (ρ : Nat → V) (H : GenPreHyps pp out mpC d Dc mc cvc g rd ψ ρ) :
    ∃ a : Nat → V, (∀ c, c < (tgtRs out).length →
        a c ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) ∧
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ') ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun _ => genRbAV g rd) ψ,
        (pt : V) ∈ˢ interp V (chainFrame (tgtRs out).length a ρ) e :=
  genRecPre_hCand hμ h ψ ρ
    (genRow_hsplit hμ h ψ ρ H.split) (genRow_hconcl hμ h ψ ρ H.split)
    (genRow_hconclTy hμ h ψ ρ H.back)
    (genRow_hstep hμ h ψ ρ H.split H.dec H.decInv H.nIdx H.gpre H.nF H.mot H.min H.below
      H.callTy H.conclMot H.minor)
    (genRow_huniq hμ h ψ ρ H.back H.din H.mN H.lic) H.ind
    (genRow_hrule hμ h ψ ρ H.back H.dec) (genRow_hdec hμ h ψ ρ H.dec)
    (genRow_hchain hμ h ψ ρ H.split H.gpre H.nF H.cal H.below H.callTy)

set_option maxHeartbeats 4000000 in
/-- **THE FAMILY PREMISE AT THE GENERATED STAGE** — the skeleton's `hpre`
goal, from the family's level (`hTy`, `blockRecLevel_run`), the equations'
grading at typed tuples (`hEqWd`), and `GenPreHyps` at every level
assignment and base frame. -/
theorem genRecPre (hμ : μ.verifiedChecks = true) {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    {s : (Name → Nat) → Nat}
    (hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V) (c : Nat), c < (tgtRs out).length →
      interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c) ∈ˢ univ (s ψ) ∧
        WellDenoted V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c))
    (hEqWd : ∀ (ψ : Name → Nat) (ρ : Nat → V) (rs : List V), rs.length = (tgtRs out).length →
      (∀ c, c < (tgtRs out).length →
        rs.getD c pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ c)) →
      ∀ e ∈ blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ) (fun _ => genRbAV g rd) ψ,
        WellDenoted V (consList rs ρ) e)
    (H : ∀ (ψ : Name → Nat) (ρ : Nat → V), GenPreHyps pp out mpC d Dc mc cvc g rd ψ ρ) :
    ∀ (ψ : Name → Nat) (ρ : Nat → V),
      BlockRecPre V (s ψ) (tgtRs out).length (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
        (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
          (fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
          (fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length g rd (genBit pp ψ) ψ)
          (fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ) (fun _ => genRbAV g rd) ψ)
        ρ := by
  intro ψ ρ
  refine ⟨fun c hc => hTy ψ ρ c hc, fun rs hl ht e he =>
    ⟨blockRecEqs_univZero _ _ _ _ _ _ _ _ ψ _ e he, hEqWd ψ ρ rs hl ht e he⟩, ?_⟩
  exact genRecPre_hCandH hμ h ψ ρ (H ψ ρ)

end Assembly

end ConLeche.Model
