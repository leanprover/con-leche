import Setlec.SetR.Install.ValueKinds
import Setlec.SetR.Install.Axiom
import Setlec.SetBase.DeclEta

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
name) — the three value kinds now conclude the *named* extension plus
its valuation agreement, and this dispatch forgets both, because v1
genuinely does not need them and the interp2 tier does; the obligations follow the house pattern of `DivModPinS` /
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
    EtaFamiliesClosed env →
    DeclIndR μ F env m.cval block env₂ →
    Nonempty (EnvS V env₂) ∧ EtaFamiliesClosed env₂

/-! The η-closure kit (`basisIndOk`, `basisIndOk_mem`,
`basisInstallR_etaClosed`, `basisIndOk_declsA`) moved to
`Setlec/SetBase/DeclEta.lean` at task #161 S3, together with the new
model-free `declEtaStep`: none of it mentions `V`, and the P lane
consumes exactly that half of this file's dispatch. -/

/-- The declaration fold's carrier: a model together with the eta
side invariant it needs one declaration later. -/
def EnvSOk (V : Type w) [SetTheory V] (env : Env) : Prop :=
  Nonempty (EnvS V env) ∧ EtaFamiliesClosed env

/-- **The per-declaration install**, by dispatch: a checked
declaration of any kind extends the invariant. -/
theorem declStepS (hdm : DivModPinS V) (hrp : ReducePinS V)
    (hstd : StdAxiomKeyS V)
    (hbas : DeclBasisS V) (hind : DeclIndS V)
    {F : Nat} {env env₂ : Env} {d : Declaration}
    (m : EnvS V env) (hE : EtaFamiliesClosed env)
    (h : DeclR modeR F m.cval env d env₂) :
    Nonempty (EnvS V env₂) ∧ EtaFamiliesClosed env₂ := by
  refine ⟨?_, declEtaStep (fun h' => (hind m hE h').2) hE h⟩
  cases d with
  | defnDecl cv value hint => exact ⟨(declDefnS hdm m h).choose⟩
  | thmDecl cv value => exact ⟨(declThmS m h).choose⟩
  | opaqueDecl cv value => exact ⟨(declOpaqueS hrp m h).choose⟩
  | axiomDecl cv => exact declAxiomS hstd ofReduceKeyS m h
  | basisDecl kind => exact hbas m h
  | indDecl block =>
    exact (hind m hE (declIndDispatchR_eq_ind.mp h)).1

end Setlec.SetR
