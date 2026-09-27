module

public import ConLeche.Model.Inductives.BlockPosStage
public import ConLeche.Verify.Inductives.PositivityKInv
import ConLeche.Model.Inductives.MemberCtorSemK

public section

/-!
# The key-named positivity stage, as the install reads it (PRIMREC / NESTKN-M5)

`checkBlockPositivityK_stage`: a successful run of the key-named stage
(`checkBlockPositivityK`, UNWIRED) gives `BlockPosStage` — the statement
every install consumer reads — with the same hypotheses as today's producer
`checkBlockPositivity_stage` (the two closedness premises are not needed by
the key-named inversion; they are kept so that the switch is a proof swap).

The walk's derivation at the use hook is `checkBlockPositivityK_derivU`
(`nestBlockCtorsK_posPremise`, the one hypothesis `CtxTysClosed` from
`EnvWF`), read by `memberCtorDK_sem`; the stage's other checks are
`checkBlockPositivityK_inv_gen`, verbatim today's.
-/

namespace ConLeche.Model
open ConLeche (Env Expr ConstantVal CheckM NestFieldKind BlockParts fueledOps)

universe w

/-- **The key-named positivity stage, as the install reads it.** -/
theorem checkBlockPositivityK_stage {V : Type w} [SetTheory V] {env : Env}
    (hwf : ConLeche.EnvWF env) {F : Nat}
    {p : BlockParts} {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
    {kinds : List (List (List NestFieldKind))} {nfs : List (List Expr)}
    {nodes : ConLeche.NestNodes}
    (hrun : ConLeche.checkBlockPositivityK (m := CheckM) (fueledOps .verified F) env env.find?
      env.consts p cvTas ctorsAs = .ok (kinds, nfs, nodes))
    (_hT0 : ∀ cvTa0, cvTas.head? = some cvTa0 → cvTa0.type.hasFvar = false)
    (_hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAs[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false) :
    BlockPosStage V env F p cvTas ctorsAs kinds nfs := by
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, hder⟩ :=
    ConLeche.checkBlockPositivityK_derivU hwf hrun
  obtain ⟨cvTa0', fvsP', rest', holes', h1', h2', h3', hall⟩ :=
    ConLeche.checkBlockPositivityK_inv_gen hrun
  rw [h1] at h1'
  obtain rfl := Option.some.inj h1'
  rw [h2] at h2'
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using h2'
  rw [h3] at h3'
  obtain rfl := Option.some.inj h3'
  refine ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, fun c cs hc j cA hj => ?_⟩
  obtain ⟨crest, ks, hcr, hks, hd⟩ := hder c cs hc j cA hj
  obtain ⟨crest', tyN, hcr', hnf, hty, hlp, hsorts, hocc⟩ := hall c cs hc j cA hj
  rw [hcr] at hcr'
  obtain rfl := Option.some.inj hcr'
  subst hnf
  refine ⟨crest, ks, hcr, memberCtorDK_sem hd, ?_, hty, hlp, hsorts, hocc⟩
  rw [List.getD_eq_getElem?_getD, hks]; rfl

end ConLeche.Model
