module

public import ConLeche.Verify.Driver.ComposeReads
public import ConLeche.Verify.Driver.RouteWorker
import ConLeche.Verify.Driver.Reach

/-!
# The routes: what a module's context stores, and how

At a module of a run (task #501), facts about the records of its context that the routes of the
capture check's pairs (`Routes.lean`) read:

* `ctx_stmt` — a context name whose copy is of a statement kind is stored by its statement,
  read at that copy, of a module of the run;
* `rank_lt` — a name a stored statement's type reads, other than its own, is stored before it;
* `reader_ctx` — a reader of a passed pair stores the name it reads, where the name is loaded at
  it: by the pair's origin (a record's read, an `agreeCheck` partner read, a clash partner read).
-/

public section

namespace ConLeche.Driver.Compose

open ConLeche ConLeche.Modular ConLeche.Cached ConLeche.Frontend.Olean

namespace Run

variable {sp : SearchPath} {fs : FS} (R : Run sp fs)

/-- **A context name whose copy is of a statement kind is stored by its statement**, read at that
copy: its constant is a statement kind of the copy's statement, the copy is on the snapshot, at a
level a load reads, not unsafe or partial, of a module of the run, and the name is not the
tolerated axiom's. -/
theorem ctx_stmt {M : Name} (hM : M ∈ R.names) {y : Name}
    (hy : ((R.dev (R.rk M)).context.find? y).isSome = true) {s : Spot}
    (hs : copyOf (R.envOf M) (R.cap M).1 y = some s) {r : Region} {cv : ConstantVal}
    {k : CKindF Name Unit} (hr : PartRegion sp fs s.part r) (hst : StmtSkel r s.pos.loc cv k)
    (hk : k.tag < 4) :
    ∃ ci, (R.dev (R.rk M)).context.find? y = some ci ∧ ci.toConstantVal = cv ∧
      ci.isStmtKind = true ∧ CopyAt sp fs s ∧ s.part.level ≠ .server ∧
      s.pos.skipped = false ∧ cv.name = y ∧ y ≠ sorryAxName ∧ s.part.mod ∈ R.names := by
  sorry

/-- **A name a stored statement's type reads, other than its own, is stored before it.** -/
theorem rank_lt {M : Name} (hM : M ∈ R.names) {y : Name} {ci : ConstantInfo}
    (hci : (R.dev (R.rk M)).context.find? y = some ci) (hk : ci.isStmtKind = true) {c : Name}
    (hc : c ∈ ci.toConstantVal.type.readNames) (hne : c ≠ y) :
    (R.dev (R.rk M)).rank c < (R.dev (R.rk M)).rank y ∧
      ((R.dev (R.rk M)).context.find? c).isSome = true := by
  sorry

/-- **A reader stores the name it reads, where the name is loaded at it**: by the pair's origin,
a read of one of its own records, the statement of one of its copies an `agreeCheck` compared, or
of one of its copies of a clash's name. -/
theorem reader_ctx {M : Name} (hM : M ∈ R.names) {h y : Name} (hP : (h, y) ∈ (R.cap M).2.2)
    (hl : ((R.w h).reads.index.first[y]?).isSome = true) :
    ((R.dev (R.rk h)).context.find? y).isSome = true := by
  sorry

end Run

end ConLeche.Driver.Compose
