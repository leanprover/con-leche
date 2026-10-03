module

public import Fragment.IndCommon
public import Fragment.NstBound

@[expose] public section

/-!
# SCAFFOLDING — the nested lane's view of the specification

The nested lane of the fragment (`NestSem.lean` … `NestInstall.lean`)
still consumes the OLD construction of a block's family (the
predicate-level least fixed point bounded by a closure law), which the
plain-block model has left behind (`IndSem.lean`, by the ruling of
2026-10-03, `whitepaper/PLAN.md`).  Until that lane is ported, the old
construction and the old plain-block pipeline it reads are kept
VERBATIM under the namespace `Fragment.IndSpec.Nst` (`NstIndSem.lean`,
`NstRead.lean`, …), and the nested lane's files are wrapped in that
namespace.

This file is the one trick that makes the two pipelines coexist
without renaming a single declaration: inside `Fragment.IndSpec.Nst`, the
names `IndSpec` and `NestInfo` denote the same structures under
local names, so that dot notation (`S.Mem`, `N.KS.Fam`) resolves to
the frozen definitions, while the pieces the two pipelines share
(`IndCommon.lean`, and the generators of `Decl.lean`) are reached by
the namespace prefix `Fragment.IndSpec`, as before.  Delete this file with the
rest of the scaffolding when the nested lane is ported.
-/

namespace Fragment.IndSpec.Nst

/-- The specification, under the frozen lane's name. -/
abbrev IndSpec := Fragment.IndSpec

/-- The class of a nested block, under the frozen lane's name. -/
abbrev NestInfo := Fragment.NestInfo

/-- The container's specification, returned under the frozen lane's
name so that its dot notation resolves to the frozen definitions. -/
abbrev NestInfo.KS (N : NestInfo) : IndSpec := Fragment.NestInfo.KS N

namespace IndSpec

/-! The checker's predicates on a specification, under the frozen
lane's names, so that the lane's lemmas about them (`Ok.fresh`,
`Scoped.mono`, …) are reached by dot notation. -/

/-- `IndSpec.Ok`, under the frozen lane's name. -/
abbrev Ok [LevelOracle] (S : IndSpec) (env : Env) : Prop := Fragment.IndSpec.Ok S env
/-- `IndSpec.OkN`, under the frozen lane's name. -/
abbrev OkN [LevelOracle] (S : IndSpec) (N : NestInfo) (env : Env) : Prop :=
  Fragment.IndSpec.OkN S N env
/-- `IndSpec.Scoped`, under the frozen lane's name. -/
abbrev Scoped (S : IndSpec) (env : Env) : Prop := Fragment.IndSpec.Scoped S env
/-- `IndSpec.fieldScoped`, under the frozen lane's name. -/
abbrev fieldScoped (S : IndSpec) (env : Env) (k : Nat) (f : Field) : Prop :=
  Fragment.IndSpec.fieldScoped S env k f
/-- `IndSpec.NestScoped`, under the frozen lane's name. -/
abbrev NestScoped (S : IndSpec) (env : Env) : Prop := Fragment.IndSpec.NestScoped S env

end IndSpec

end Fragment.IndSpec.Nst
