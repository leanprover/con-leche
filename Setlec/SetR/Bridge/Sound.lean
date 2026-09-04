import Setlec.SetBase.Bridge.Sound
import Setlec.SetR.Bridge.Decl
import Setlec.SetR.Install.DeclIndS
import Setlec.SetR.DivModPin
import Setlec.SetR.Install.ReducePin
import Setlec.SetR.Install.BasisS
import Setlec.SetR.StdAxiomKey

/-!
# The assembly (task #148, T6): the collapsed lane's fold

The `checkDecls` fold that carries the `EnvS` invariant along
`checkDecl`'s dispatch.  This is the transpose of the TT lane's
`checkDeclTT` / `foldlM_TT` pair
(`Setlec/TTVerify/Consistency.lean`).

**Task #161 S8 — the zero-opener.**  The dispatch itself is model-free
and moved to `Setlec/SetBase/Bridge/Sound.lean`
(`checkDeclR_ofEnvR`/`checkDeclR_ofEnvRE`); what is left here is the
collapsed lane's `EnvS` instance of it and the lane's own fold.  The
graded lane imports the base half and composes it with its own carrier
— which is why the layering whitelist is now empty.

Three per-declaration bridge obligations stay **named hypotheses**
here rather than being discharged: the `Nat` equation certificates,
the div/mod pins and the reduce pins.  Each is stated *attached* — it
quantifies over an `EnvS V env` and speaks at that `m`'s own
valuation — which is what keeps it dischargeable (an unattached
valuation in a semantic hypothesis is the campaign's recorded vacuity
signature).
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory
universe w
variable {V : Type w} [SetTheory V]

theorem checkDeclR_sound
    {F : Nat}
    {env env₂ : Env} (m : EnvS V env) (hE : EtaFamiliesClosed env)
    {d : Declaration}
    (h : checkDecl modeR (fueledOps modeR F) env d = .ok env₂) :
    DeclR modeR F m.cval env d env₂ :=
  checkDeclR_ofEnvRE m.toEnvR hE h

-- **`checkDeclRun_sound` is deleted** (task #161 S11b, the opener).
-- The design census's C3 artifact was `DeclR.toRun` composed *after*
-- `checkDeclR_sound`, and the S10 seal's residual B measured what that
-- composition costs: the projection hides the derivation conjuncts in
-- the *statement* while keeping them in the *proof term*, so it was
-- never a route off the relation tier.  It has had no consumer since
-- the graded fold began calling `checkDeclR_ofEnvRE` directly, and
-- `checkDeclRun_ofEnvRE` (`SetBase/Bridge/Sound.lean`) supersedes it
-- functionally without the weld.  Deleted on the S7 `declIndRS`
-- precedent: a consumer-free statement is not kept for its shape.
-- (`DeclR.toRun` itself stays live — `declEtaStep`,
-- `SetBase/DeclEta.lean`, is its consumer.)

theorem foldlM_R
    {F : Nat} :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvSOk V env →
      ds.foldlM (checkDecl modeR (fueledOps modeR F)) env = .ok env' →
      EnvSOk V env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl modeR (fueledOps modeR F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨m⟩, hE⟩ := hm
      exact foldlM_R ds env1
        (declStepS divModPinS reducePinS stdAxiomKeyS declBasisS
          (declIndS memberKeyS) m hE
            (checkDeclR_sound m hE hd)) h
end Setlec.SetR
