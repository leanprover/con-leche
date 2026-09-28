module

public import ConLeche.Model.Inductives.MemberPosFacts
import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Model.Inductives.BlockHoleGrade
import ConLeche.Model.Inductives.BlockPosRunCont
import ConLeche.Model.Inductives.BlockAccRunCont
import ConLeche.Model.Inductives.BlockAbsRead

public section

/-!
# The member block's positivity facts, from the positivity check's run

`memberPosFacts_of_run`: the producer of `MemberPosFacts` on today's
route — the positivity check (`checkBlockPositivity`, inside the
recursor check's run) at the formers' environment, its walked normal
forms (`posKs.2.1`) the datum's.  Each field is one run theorem:
`canonOcc_of_positivity` (M2′), `blockRunLink` (the walked normal form),
`blockHoleGrade_of_run` (U2), `blockCtorPos_of_run` (positivity),
`blockAcc_of_run` (accessibility).  Deleted with the positivity check
when the class check's producer takes its place.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Expr Name ConstantVal CheckM BlockParts fueledOps)

universe w

variable {V : Type w} [SetTheory V]

/-- **The member block's positivity facts, from the positivity check's
run** at the formers' environment. -/
theorem memberPosFacts_of_run {μ : ConLeche.CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env : Env} {p : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))} {hook : ConLeche.NestHook ConLeche.CheckM}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × List ConLeche.NestKey ×
      List (Nat × Nat × Expr)}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps μ F) env env.find? env.consts
      p cvTas ctorsAs hook = .ok posKs) :
    MemberPosFacts V μ env p cvTas ctorsAs posKs.2.1 where
  occ hfit := canonOcc_of_positivity hrun (V := V) hfit.hnames hfit.hlps hfit.hk hfit.hctorsAs
  link mp _ _ _ _ hfit hN hF ψ hformers _ _ _ hc hcj hD := by
    rw [hfit.hnfs _ _ _ hcj]
    exact blockRunLink hμ mp hN hF hrun hfit.hnames hfit.hlps hfit.hnP hfit.hnIdxs hfit.hk
      hfit.hnd hfit.hctorsAs hfit.hlenCA hfit.hclosed ψ hformers hc hcj hD
  grade mp _ _ _ _ hfit hN hcore ψ _ hc _ hj :=
    blockHoleGrade_of_run hμ mp hN hcore hrun hfit.hnames hfit.hlps hfit.hnP hfit.hnIdxs
      hfit.hres hfit.hk hfit.hinst hfit.hctorsAs hfit.hlenCA hfit.hclosed hfit.hnfs ψ hc hj
  pos mp _ _ _ _ hfit hN hcore hcov :=
    blockCtorPos_of_run hμ mp hN hcore hrun hfit.hnames hfit.hlps hfit.hnP hfit.hnIdxs hfit.hk
      hfit.hinst hfit.hlenCA hfit.hctorsAs hfit.hclosed hfit.hnfs hcov
  acc mp _ _ _ _ hfit hN hcore hH hcov ψ ρp hs hw hIdx hG :=
    blockAcc_of_run hμ mp hN hcore hH hrun hfit.hnames hfit.hlps hfit.hnP hfit.hnIdxs hfit.hres
      hfit.hk hfit.hinst hfit.hlenCA hfit.hctorsAs hfit.hclosed hfit.hnfs hcov ψ ρp hs hw hIdx hG

end ConLeche.Model
