module

public import ConLeche.Model.Inductives.BlockDeclRun
public import ConLeche.Model.Inductives.TargetOutRows

public section

/-!
# The generated rules' forward fit, at the constructors' environment

`RecRuleFit` (`Model/Env/Laws.lean`) at a generated rule, with the two reading binders
eliminated (the recursor type's reading is `blockRecTyAV`, the constructor type's
`blockRecCtorTy`), the constructor's leaf at the constructors' environment, and the rule's
parameters read at it (`GenPs`).  `GenRecFit.lean` reduces the field to the two statements here
(`GenFit1`, `GenFit2`) and the universe clause.

* `GenPs`: the parameters `ps` the rule applies its constructor to, read at the prefix `xs` —
  the prefix's leading arguments at a member class, the class's parameters (`tgtOutDsa`, the
  rule's pins opened at the prefix) at an outside one;
* `GenFit1`: the parameters fit the constructor's parameter binders;
* `GenFit2`: the prefix, the indices and the constructor application fit the recursor's
  whole telescope, at fields completing the constructor's fit and indices pinned to its
  conclusion.

The constructor's level valuation `ψj` agrees with the class's on the constructor's level
parameters (`hlv`): the recursor's at a member class, the major's levels at it at an outside
one.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantVal BlockShape TargetMajor)

universe w

variable {V : Type w} [SetTheory V]

section Defs

variable {envC : Env} (mpC : EnvModelM V envC) (pp : BlockShape)
  (out : List (ConstantVal × TargetMajor × List Expr))

/-- **The rule's parameters, read at the prefix** (`RuleParamsRead` at the constructors'
environment): the prefix's leading arguments at a member class, the class's parameters read at
the prefix spine at an outside one. -/
@[expose] def GenPs (ψ : Name → Nat) (ρ : Nat → V) (j : Nat) (xs ps : List Term) : Prop :=
  ps.length = (tgtMajor out j).nPc ∧ ∀ q, q < (tgtMajor out j).nPc →
    interp V ρ (ps.getD q default) =
      if (tgtMajor out j).member.isSome then interp V ρ (xs.getD q default)
      else interp V (consList (xs.map (interp V ρ)) ρ)
        ((tgtOutDsa mpC.base2.acval envC pp out ψ j).getD q default)

/-- **The constructor's level valuation is the class's** on the constructor's level
parameters. -/
@[expose] def GenLv (ψ ψj : Name → Nat) (j : Nat) (ctor : ConstantVal × Nat) : Prop :=
  ∀ q ∈ ctor.1.levelParams, ψj q =
    if (tgtMajor out j).member.isSome then ψ q
    else Level.substFn ψ ctor.1.levelParams (tgtMajor out j).lvls q

/-- **Conjunct (1) of `RecRuleFit`** at the generated rule `(j, i)`: the parameters read at a
fitting prefix fit the constructor's parameter binders. -/
@[expose] def GenFit1 (j i : Nat) (ctor : ConstantVal × Nat) : Prop :=
  ∀ (ψ ψj : Name → Nat), GenLv out ψ ψj j ctor →
  ∀ (ρ : Nat → V) (xs ps : List Term) (mid : Term),
    xs.length = pp.rulePrefixAt j → (∀ x ∈ xs, WellDenoted V ρ x) →
    TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j) xs mid →
    (∀ p ∈ ps, WellDenoted V ρ p) → GenPs mpC pp out ψ ρ j xs ps →
    ∃ r, TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) ps r

/-- **Conjunct (2) of `RecRuleFit`, its fit** at the generated rule `(j, i)`: at fields
completing the constructor's fit and indices pinned to its conclusion, the prefix, the indices
and the constructor application fit the recursor's whole telescope. -/
@[expose] def GenFit2 (j i : Nat) (ctor : ConstantVal × Nat) : Prop :=
  ∀ (ψ ψj : Name → Nat), GenLv out ψ ψj j ctor →
  ∀ (ρ : Nat → V) (xs ps : List Term) (mid : Term),
    xs.length = pp.rulePrefixAt j → (∀ x ∈ xs, WellDenoted V ρ x) →
    TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j) xs mid →
    (∀ p ∈ ps, WellDenoted V ρ p) → GenPs mpC pp out ψ ρ j xs ps →
    ∀ (fs is : List Term) (restC : Term),
      fs.length = ctor.2 → is.length = pp.majorIdxAt j - pp.rulePrefixAt j →
      (∀ f ∈ fs, WellDenoted V ρ f) → (∀ i ∈ is, WellDenoted V ρ i) →
      TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) (ps ++ fs) restC →
      IotaIndexPin (V := V) ρ restC (tgtMajor out j).nPc (pp.majorIdxAt j) (pp.rulePrefixAt j)
        (xs ++ is) →
      ∃ restR, TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
        (xs ++ is ++ [Term.mkAppN (mpC.base2.acval ctor.1.name ψj) (ps ++ fs)]) restR

end Defs

end ConLeche.Model
