module

public import ConLeche.Verify.Inductives.StructBody
import ConLeche.Verify.ProjSlots

public section

/-!
# The generated recursor, opened (task #175 S2)

The direct install stores the recursor it *generates* (`structRecTy`,
`structRecRhs`, `ConLeche/Kernel/Inductives/StructParts.lean`): the type former's
parameter binders re-emitted with the elimination datum, the motive,
one minor premise per constructor — the constructor's field telescope
lifted under the motive (and the earlier minors), its data reset —
the major, and `motive t`; the rule is the same telescope as a `λ`
over `minor f⃗`.  The reading side (`Model/Inductives/StructRecRead.lean`)
opens these binder by binder as `denoteMeta` does, and what it needs
from the syntax is collected here:

* the two binder walks commute with instantiation
  (`replacePisPw_instSeq`, `pisToLamsPw_instSeq`) and strip
  (`replacePisPw_stripPis`);
* the lifted field telescope, instantiated at the parameter variables
  and the extra binders' variables, is the constructor telescope's
  residual at the parameter variables alone
  (`instSeq_liftLooseBVars_prefix`, packaged as
  `instSeq_minorTele`), and that residual is the `instPisAt` peel's
  (`instPisAt_of_stripPis`);
* the closed spellings — the family spine `T p⃗`, the constructor
  spine `C p⃗ f⃗`, the rule body `minor f⃗` — instantiate to the
  variables (`map_instSeq_structPsAt`, `instSeq_minorBody`,
  `instSeq_ruleBody`);
* no generated node is a `.proj` node
  (`Expr.NoProjAt.structRecTy`/`.structRecRhs`), for the tower law's
  `NoProjEnv` invariant.
-/

namespace ConLeche

open Expr

/-! ## The binder walks -/

/-- The `instPisAt` peel at a spine is the strip's body instantiated
along the spine (the `∀` twin of `instLamsAt_rest_of_stripLams`). -/
theorem instPisAt_of_stripPis :
    ∀ (sp : List Expr) {e : Expr} {bs : List (Expr × BinderMeta)} {body : Expr},
      e.stripPis sp.length = some (bs, body) →
      ∃ ds, Expr.instPisAt sp e = some (ds, instSeq sp (sp.length - 1) body)
  | [], e, bs, body, h => by
    simp only [List.length_nil, stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact ⟨[], rfl⟩
  | a :: sp, e, bs, body, h => by
    match e, h with
    | .forallE ty rest m, h =>
      simp only [List.length_cons, stripPis] at h
      cases hs : rest.stripPis sp.length with
      | none => rw [hs] at h; exact nomatch h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl⟩ := h
        obtain ⟨bs', hs', -⟩ := stripPis_instantiate1_full (v := a) sp.length 0 hs
        rw [Nat.zero_add] at hs'
        obtain ⟨ds, hds⟩ := instPisAt_of_stripPis sp hs'
        refine ⟨ty :: ds, ?_⟩
        simp only [Expr.instPisAt, hds, Option.map_some, List.length_cons, Nat.add_sub_cancel]
        rfl
    | .bvar _, h | .fvar _ _, h | .sort _, h | .const _ _, h | .app _ _, h
    | .lam _ _ _, h | .letE _ _ _, h | .lit _, h | .proj _ _ _, h =>
      simp [stripPis] at h

end ConLeche
