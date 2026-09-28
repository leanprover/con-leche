module

public import ConLeche.Model.Inductives.MemberPosFacts
import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Model.Inductives.BlockHoleGrade
import ConLeche.Model.Inductives.BlockPosRunCont
import ConLeche.Model.Inductives.BlockAccRunCont
import ConLeche.Model.Inductives.BlockAbsRead
import ConLeche.Model.Annot.CanonCrest
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Inductives.ScopeKit

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
open ConLeche (Env Expr Name ConstantInfo ConstantVal CheckM BlockParts fueledOps)

universe w

variable {V : Type w} [SetTheory V]

omit [SetTheory V] in
/-- **M2′ at the canonical holes, from the positivity stage's run**: the
stage checked every constructor's member-abstracted type for a member
constant (`nestNoMemberConst`) at its own holes; the check does not see
the holes' annotations. -/
theorem canonOcc_of_positivity {ops : ConLeche.CheckerOps ConLeche.CheckM} {env₁ : Env}
    {find? : Name → Option ConstantInfo} {consts : List ConstantInfo} {p : BlockParts}
    {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {hook : ConLeche.NestHook ConLeche.CheckM}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × List ConLeche.NestKey ×
      List (Nat × Nat × Expr)}
    (hrun : ConLeche.checkBlockPositivity ops env₁ find? consts p cvTas ctorsAs hook = .ok posKs)
    {d : BlockData V} {lps : List Name}
    (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hk : d.k = d.memberNames.length)
    (hctorsAs : ∀ c, c < d.k → ctorsAs[c]? = some (d.ctorsM c)) :
    ∀ c, c < d.k → ∀ (j : Nat) (cA : ConstantVal × Nat), (d.ctorsM c)[j]? = some cA →
      (canonAbs d.memberNames lps d.nP d.k cA.1.type).nestOcc d.memberNames 0 0 = false := by
  obtain ⟨cvTa0, fvsP, rest, holes, -, -, hholes, hall⟩ :=
    ConLeche.checkBlockPositivity_inv_gen hrun
  intro c hc j cA hcj
  obtain ⟨-, -, -, -, -, -, -, hocc⟩ := hall c (d.ctorsM c) (hctorsAs c hc) j cA hcj
  have hn : (p.nestCtx fvsP find? consts).names = d.memberNames := hnames
  rw [hn] at hocc
  rw [← hocc]
  refine nestOcc_nestAbstract_blind (by rw [hn]; rfl) (by rw [← hlps]; rfl) ?_
    (fun h hm => ?_) (fun h hm => ?_) _ _
  · rw [canonHoles_length, ConLeche.nestHoles_length hholes, hn, hk]
  · obtain ⟨mm, -, rfl⟩ := mem_canonHoles hm
    exact ⟨_, _, rfl⟩
  · obtain ⟨i, cv, caps, -, rfl⟩ := ConLeche.nestHoles_mem hholes h hm
    exact ⟨_, _, rfl⟩

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
