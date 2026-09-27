module

public import ConLeche.Model.Inductives.MemberCtorSem
public import ConLeche.Verify.Inductives.UseOkK
import ConLeche.Model.Inductives.PosRedK
import ConLeche.Model.Inductives.UseBridgeK
import ConLeche.Model.Inductives.PosAccK

public section

/-!
# The key-named walk's producer of `MemberCtorSem` (PRIMREC / NESTKN-M5)

`memberCtorDK_sem`: a member constructor's key-named derivation AT THE USE
HOOK (`MemberCtorDKH … UseOkK`, what `nestBlockCtorsK_derivU` gives from the
run) gives everything the install reads (`MemberCtorSem`) —
`memberCtorDK_red`, `memberCtorDK_open` (`PosRedK.lean`),
`memberCtorDK_monoOk` (`UseBridgeK.lean`), `memberCtorDK_accOk`
(`PosAccK.lean`).  The one producer after the switch.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Model.Rules
open ConLeche (Env Expr NestCtx PosKind fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-- **The key-named walk's member constructor, as the install reads it.** -/
theorem memberCtorDK_sem {env : Env} {ctx : NestCtx} {F nF : Nat}
    {crest : Expr} {ks : List PosKind} {tyN : Expr}
    (hd : ConLeche.MemberCtorDKH (fueledOps .verified F) env ctx
      (ConLeche.UseOkK (fueledOps .verified F) env ctx) nF crest ks tyN) :
    MemberCtorSem V env ctx nF crest ks tyN := by
  obtain ⟨met, nds, cur, htele, htyN, hU4, hhead, hok, hha⟩ := hd
  obtain ⟨-, -, xs, hop, -⟩ := posDK_tele_open htele
  simp only [ConLeche.rootLayoutK, Nat.add_zero] at hop
  refine ⟨nds, cur, htyN, ⟨xs, hop⟩, hU4, hhead, hok, hha,
    fun henv hcl => memberCtorDK_open henv hcl htele htyN,
    fun m φ hin hfr _ _ hC hca hgr =>
      memberCtorDK_red hin ⟨met, nds, cur, htele, htyN, hU4, hhead, hok, hha⟩ hfr hC hca hgr,
    fun mp φ hin hcov hfr _ _ _ hC hca hgr hR =>
      memberCtorDK_monoOk mp hin ⟨met, nds, cur, htele, htyN, hU4, hhead, hok, hha⟩ hcov hfr hC
        hca hgr hR,
    fun mp φ hin _ hw hcov hfr _ _ _ hC hca hgr hR hsm =>
      memberCtorDK_accOk mp hin hw htele hhead hok hcov hfr hC hca hgr hR hsm⟩

end ConLeche.Model
