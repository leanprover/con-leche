module

public import ConLeche.Model.Inductives.MemberCtorSem
public import ConLeche.Verify.Inductives.PosDeriv
import ConLeche.Model.Inductives.NestPosRed
import ConLeche.Model.Inductives.PosDerivShape
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.PosDerivAcc
import ConLeche.Verify.Inductives.PosNodes

public section

/-!
# The path walk's producer of `MemberCtorSem` (PRIMREC / NESTKN-M5)

`memberCtorD_sem`: a member constructor's path derivation (`MemberCtorD`,
today's `nestBlockCtors`) gives everything the install reads
(`MemberCtorSem`) — `memberCtorD_red`, `memberCtorD_open`, `memberCtorD_mono`,
`memberCtorD_acc`.  DELETED at the switch, with the path walk.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.Model.Rules
open ConLeche (Env Expr NestCtx PosKind PosTree fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-- **The path walk's member constructor, as the install reads it.** -/
theorem memberCtorD_sem {env : Env} (henv : ConLeche.EnvWF env) {ctx : NestCtx} {F nF : Nat}
    {crest : Expr} {ks : List PosKind} {tyN : Expr} {ts : List PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env ctx nF crest ks tyN ts) :
    MemberCtorSem V env ctx nF crest ks tyN := by
  obtain ⟨nds, cur, htele, htyN, hU4, hhead, hok, hha⟩ := hd
  obtain ⟨-, -, xs, hop, -⟩ := ConLeche.posD_tele_open htele
  rw [Nat.add_zero] at hop
  refine ⟨nds, cur, htyN, ⟨xs, hop⟩, hU4, hhead, hok, hha,
    fun _ hcl => memberCtorD_open henv hcl htele htyN,
    fun m φ hin hfr _ _ hC hca hgr =>
      memberCtorD_red hin ⟨nds, cur, htele, htyN, hU4, hhead, hok, hha⟩ hfr hC hca hgr,
    fun mp φ hin hcov hfr _ _ _ hC hca hgr hR =>
      memberCtorD_mono mp hin ⟨nds, cur, htele, htyN, hU4, hhead, hok, hha⟩ hcov hfr hC hca hgr hR,
    fun mp φ hin _ hw hcov hfr _ _ _ hC hca hgr hR hsm =>
      memberCtorD_acc mp hin hw htele hhead hok hcov hfr hC hca hgr hR hsm⟩

end ConLeche.Model
