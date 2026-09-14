module

public import ConLeche.Kernel.Name
public import ConLeche.Kernel.PropWhen
public import ConLeche.Kernel.Expr
public import ConLeche.Kernel.ExprOps
public import ConLeche.Kernel.Level
public import ConLeche.Kernel.Env
public import ConLeche.Kernel.PropRead
public import ConLeche.Kernel.TypeChecker
public import ConLeche.Kernel.CoreIO
public import ConLeche.Kernel.CoreGated
public import ConLeche.Kernel.CheckerGated
public import ConLeche.Kernel.Checker
public import ConLeche.Verify.Level
public import ConLeche.Verify.Shift
public import ConLeche.Verify.InstLevels
public import ConLeche.Verify.EnvWF
public import ConLeche.Verify.InferLemmas
public import ConLeche.Verify.InferIOLemmas
public import ConLeche.Verify.InferIOLeaves
public import ConLeche.Verify.CoreGated
public import ConLeche.Verify.AnnotDefense
public import ConLeche.SetTheory.Basic
public import ConLeche.SetTheory.Core
public import ConLeche.Verify.Mono
public import ConLeche.Verify.Deep
public import ConLeche.Verify.BridgeDecl
public import ConLeche.Verify.OfReducePin
-- ALIVE BY STATEMENT (the task #209 census's class): the nested route's
-- copy-type lemmas (tasks #298/#300, DESIGN K.4/K.5) are proved for the
-- model tier's fold and nothing in the tree consumes them yet, so the
-- base umbrella is what puts them on the build graph — without an edge
-- here `lake build` never checks them and `tests/shake.sh`'s census
-- dies on the missing olean.  `AuxFormers` re-exports `CopyTypes`.
public import ConLeche.Verify.Inductives.AuxFormers
-- ALIVE BY STATEMENT, the same class: the nested route's ledger, its
-- copy-order bridge and the facts behind them (task #279, DESIGN §M.13,
-- §M.22, §M.25) are consumed only by the model lane's off-graph nested
-- modules until the route is wired, so this edge is what makes `lake
-- build` CHECK them (the K.6 merge broke every ledger lemma silently
-- while they were off the graph).  `NestedOrder` re-exports
-- `NestedLedger`, which re-exports `NestedFacts`.
public import ConLeche.Verify.Inductives.NestedOrder
-- the same class: the elimination's leaf invariant (DESIGN §M.28),
-- consumed by the model lane's nested modules
public import ConLeche.Verify.Inductives.NestedLeaves
public import ConLeche.Verify.Inductives.NestedProj
public import ConLeche.Verify.Inductives.NestedWalk
public import ConLeche.Verify.Inductives.NestedFields
public import ConLeche.Verify.Inductives.NestedRestore
public import ConLeche.Verify.Inductives.NestedRestoreWalk
public import ConLeche.Verify.Inductives.NestedCopyStored

@[expose] public section
