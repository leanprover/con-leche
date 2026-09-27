module

public import ConLeche.Model.Inductives.MemberCtorSem
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Inductives.MemberCtorSemD

public section

/-!
# The install's positivity stage, as the install reads it (PRIMREC / NESTKN-M5)

`BlockPosStage V env F p cvTas ctorsAs kinds nfs`: the canonical
parameters and holes of the stage, and per stored constructor its
member-abstracted crest, the walk's reading of it (`MemberCtorSem`, with the
run's kinds and normal form) and the stage's other checks (U2's typing of the
crest, the normal form's level parameters and fields' sorts, M2′).

It is the one statement the install's consumers
(`blockCtorPos_of_run`, `blockAccTuple_of_run`, `blockHoleGrade_of_run`,
`blockRunLink`) read of a successful positivity stage.  Its producers:
`checkBlockPositivity_stage` (today's path walk, here) and
`checkBlockPositivityK_stage` (the key-named walk, `BlockPosStageK.lean`) —
at the switch the second becomes the first's proof.
-/

namespace ConLeche.Model
open ConLeche (Env Expr Name Level ConstantVal CheckM NestFieldKind BlockParts instPisWith
  nestAbstract nestHoles openPisAtFvars fueledOps)

universe w

/-- **The positivity stage, as the install reads it** (see the module
docstring). -/
@[expose] def BlockPosStage (V : Type w) [SetTheory V] (env : Env) (F : Nat) (p : BlockParts)
    (cvTas : List ConstantVal) (ctorsAs : List (List (ConstantVal × Nat)))
    (kinds : List (List (List NestFieldKind))) (nfs : List (List Expr)) : Prop :=
  ∃ cvTa0 fvsP rest holes, cvTas.head? = some cvTa0 ∧
    openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest) ∧
    nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes ∧
    ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest ks,
        instPisWith fvsP (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type)
          = some crest ∧
        MemberCtorSem V env (p.nestCtx fvsP env.find? env.consts) cA.2 crest (ks.map (·.erase))
          ((nfs.getD c []).getD j default) ∧
        (kinds.getD c []).getD j [] = ks ∧
        (∃ ty, (fueledOps .verified F).inferType env
          ((p.nestCtx fvsP env.find? env.consts).hiAt 0) crest = .ok ty) ∧
        ((nfs.getD c []).getD j default).allLevelParamsDefined p.lps = true ∧
        (∃ xq sorts, openPisAtFvars cA.2 ((nfs.getD c []).getD j default)
            ((p.nestCtx fvsP env.find? env.consts).hiAt 0) = some xq ∧
          ConLeche.checkStructFieldSortsI (fueledOps .verified F) env
            (Level.isEquiv p.resSort .zero == some true) false p.resSort
            ((p.nestCtx fvsP env.find? env.consts).hiAt 0) xq.1 [] cA.2 = .ok sorts) ∧
        (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type).nestOcc
          (p.nestCtx fvsP env.find? env.consts).names 0 0 = false

/-- **The positivity stage, as the install reads it** (`BlockPosStage`),
from today's path walk (`checkBlockPositivity_derivM`, each derivation read
by `memberCtorD_sem`).  At the switch its proof becomes
`checkBlockPositivityK_stage`'s (`BlockPosStageK.lean`); the statement, and
so every consumer, stays. -/
theorem checkBlockPositivity_stage {V : Type w} [SetTheory V] {env : Env}
    (hwf : ConLeche.EnvWF env) {F : Nat}
    {p : BlockParts} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)}
    {nodes : ConLeche.NestNodes}
    (hrun : ConLeche.checkBlockPositivity (m := CheckM) (fueledOps .verified F) env env.find?
      env.consts p cvTas ctorsAs = .ok (kinds, nfs, nodes))
    (hT0 : ∀ cvTa0, cvTas.head? = some cvTa0 → cvTa0.type.hasFvar = false)
    (hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) :
    BlockPosStage V env F p cvTas ctorsAs kinds nfs := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, h⟩ := checkBlockPositivity_derivM hwf hrun hT0 hcl
  refine ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, fun c cs hc j cA hj => ?_⟩
  obtain ⟨crest, ks, ts, hcr, hd, hks, hty, hlp, hsorts, hocc, -⟩ := h c cs hc j cA hj
  exact ⟨crest, ks, hcr, memberCtorD_sem hwf hd, hks, hty, hlp, hsorts, hocc⟩

end ConLeche.Model
