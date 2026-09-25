module

public import ConLeche.Model.Inductives.TargetNodeAdm
public import ConLeche.Model.Inductives.TargetGuardParams
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Annot.BitInst

public section

/-!
# The node presentation's dynamic part: `hAdm`, `top`, `trans` (lane NESTIND, session 23)

At the admissible frames `nodeAdm` (`TargetNodeAdm.lean`):

* `hAdm` — an admissible frame satisfies the node's parameter telescope
  (K.52, `nodeKeyFit`) and reads the true frame's index sets (N2: the
  valuations agree off the holes, `grp_idx_eq`);
* `top` — the TRUE valuation (the holes' constants) is admissible once the
  shallower nodes' true elements satisfy `G`: a constant applied at full
  arity at its owner's parameters is the owner's true carrier (`leaf`);
* `trans` — an admissible valuation is below the true one along a hole
  relation once `G`'s elements are true, so the frame's monotonicity
  (`FrameMono`, `posD_mono` at the node's derivation) moves a fit to the
  true frame (`trans_of_frameConcl`).

Node `0` (the block) is visited at its true frame only (`lfp_trans_self`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx NestHole
  BlockParts BlockShape fueledOps PosTree PosNodeOk PosD)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-! ## Readings -/

/-- A read spine is its terms' readings. -/
theorem DenoteMetaSpine.getD_eq {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      as.map (fun x => (denoteMeta acval env φ d x).getD default) = vs
  | _, _, .nil => rfl
  | _, _, .cons ha hs => by
    rw [List.map_cons, ha, Option.getD_some, DenoteMetaSpine.getD_eq hs]

/-! ## The true valuation -/

section True

variable {envC : Env} (mpC : EnvModelM V μ envC) (ctx : NestCtx) (ψ : Name → Nat) (ρ : Nat → V)
  (xs : List V)

/-- **The true valuation of a stack grown by holes on top**: the new
holes' constants consed on the old stack's. -/
theorem trueVal_append (hs prog : List NestHole) :
    trueVal mpC ctx ψ ρ xs (hs ++ prog)
      = consList ((hs.reverse.map fun h =>
          (denoteMeta mpC.base2.acval envC ψ 0 (.const h.key.cname h.key.lvls)).getD default).map
            (interp V ρ)) (trueVal mpC ctx ψ ρ xs prog) := by
  unfold trueVal nodeTrueVal nodeHv nodeHoleConsts
  rw [← consList_append]
  congr 1
  simp only [List.reverse_append, List.map_append, List.map_map, List.append_assoc]
  rfl

end True

end ConLeche.Model
