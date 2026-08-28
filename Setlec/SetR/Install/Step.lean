import Setlec.SetR.Install.ValueKinds
import Setlec.SetR.Install.Axiom

/-!
# The per-declaration install (task #148, T5)

`declStepS` is the `checkDeclR_sound`-shaped lemma T6 consumes: a
`DeclR` derivation extends an `EnvS` to the checked environment.  It is
**pure dispatch** over `DeclR`'s six kinds — the value kinds through
`declDefnS`/`declThmS`/`declOpaqueS`, the axiom kind through
`declAxiomS`, and the two remaining kinds through the obligations
named here.

The `Nonempty` conclusion is `EnvS`'s own convention (a `Prop` carrying
a `TConstVal`, so its inhabitant is data the fold never needs to
name); the obligations follow the house pattern of `DivModPinS` /
`StdAxiomKeyS` — stated where their consumer is, discharged where
their supplier is.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- **The basis-block install obligation**: a checked basis
declaration extends the invariant.  Supplier: the basis install (the
pinned blocks' valuations and their laws — `EqLawV`, `basis_pinned`,
`empty_pinned`, the `Quot` rules). -/
def DeclBasisS (V : Type w) [SetTheory V] : Prop :=
  ∀ {env env₂ : Env} {kind : BasisKind} (_m : EnvS V env),
    DeclBasisR env kind env₂ → Nonempty (EnvS V env₂)

/-- **The modeled-inductive-block install obligation**: a checked
`indDecl` block extends the invariant.  Supplier: the block install —
the member fold, the recursor group (consuming the three iota bottoms
`indBottomPlainS`/`indBottomNestedS`/`indBottomProjS`), the capability
record (consuming `etaLawKeyS`/`unitLawKeyS`), the projection installs
and the elimination templates. -/
def DeclIndS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} (m : EnvS V env),
    DeclIndR μ F env m.cval block env₂ → Nonempty (EnvS V env₂)

/-- **The per-declaration install**, by dispatch: a checked
declaration of any kind extends the invariant. -/
theorem declStepS (hdm : DivModPinS V) (hrp : ReducePinS V)
    (hstd : StdAxiomKeyS V) (hofr : OfReduceKeyS V)
    (hbas : DeclBasisS V) (hind : DeclIndS V)
    {μ : CheckMode} {F : Nat} {env env₂ : Env} {d : Declaration}
    (m : EnvS V env) (h : DeclR μ F m.cval env d env₂) :
    Nonempty (EnvS V env₂) := by
  cases d with
  | defnDecl cv value hint => exact declDefnS hdm m h
  | thmDecl cv value => exact declThmS m h
  | opaqueDecl cv value => exact declOpaqueS hrp m h
  | axiomDecl cv => exact declAxiomS hstd hofr m h
  | basisDecl kind => exact hbas m h
  | indDecl block => exact hind m h

end Setlec.SetR
