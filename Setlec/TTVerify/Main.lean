import Setlec.TTVerify.DivModPin
import Setlec.TTVerify.ReducePin
import Setlec.TTVerify.DeclThm
import Setlec.TTVerify.StdAxiomKey
import Setlec.TTVerify.DeclBasis
import Setlec.TTVerify.DeclFamilies

/-!
# The TT bridge, assembled

The last file of task #119: the six per-kind obligations of
`Setlec/TTVerify/DeclStep.lean` are all discharged, so `CheckDeclTT` —
stated as a hypothesis in `Setlec/TTVerify/Consistency.lean` since the
bridge began — is now a theorem, and with `FamiliesStepTT`
(`Setlec/TTVerify/DeclFamilies.lean`) the acceptance theorem and the
consistency corollary close over it.

The one remaining hypothesis is `CertifiedConfigTT mode`: the bridge
covers the configuration with the direct simple-structure install path
off AND the three-mode setting at `--tt-model` (task #147 — the seven
TT-lane checks the bridge's inversions consume run only there; the
default `--set-model` skips them).  Both conjuncts are real, stated
restrictions, not formalities.
-/

namespace Setlec.TTVerify

open Setlec.TT

variable {F : Nat}

/-- **The per-declaration step, discharged**: checking one declaration
against a derivation-modelled environment (under the certified
configuration, with the stored eta families closed) yields a
derivation-modelled environment. -/
theorem checkDeclTT : CheckDeclTT F :=
  checkDeclTT_of declDefnTT_closed declThmTT declOpaqueTT_closed
    declAxiomTT_closed declBasisTT declIndTT

/-- **The acceptance theorem, closed**: under the certified
configuration, every environment the checker accepts has a derivation
model — every constant it stores has a `HasType` derivation of its
type's denotation in the declarative type theory. -/
theorem checkDecls_TT_closed {mode : CheckMode}
    (hdir : CertifiedConfigTT mode)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls mode (fueledOps mode F) ds = .ok env') :
    Nonempty (EnvTT env') :=
  checkDecls_TT checkDeclTT familiesStepTT hdir h

/-- **No proof of `Empty` is ever accepted** — through the declarative
type theory, with both fold hypotheses discharged.  Parametric in a
model of the `SetTheory` interface, exactly as
`no_proof_of_Empty_TT`. -/
theorem no_proof_of_Empty_TT_closed (V : Type u) [SetTheory V]
    {mode : CheckMode} (hdir : CertifiedConfigTT mode)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls mode (fueledOps mode F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False :=
  no_proof_of_Empty_TT V checkDeclTT familiesStepTT hdir h c hc hty

end Setlec.TTVerify
