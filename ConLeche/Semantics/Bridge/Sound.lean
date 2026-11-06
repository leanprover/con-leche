module

public import ConLeche.Semantics.Inductives.DeclBlock
public import ConLeche.Semantics.DeclRun
import ConLeche.Verify.Inductives.BlockShapeInv
import ConLeche.Semantics.Bridge.DeclRun

@[expose] public section

/-!
# The assembly (#148): the RUN bridge

`checkDecl` → `DeclRun` by dispatch, off no invariant at all.  The
inductive arm, at k members, is recorded as `DeclBlockRun`
(`DeclIndRunDispatchK`), the dispatch the fold (`Model/Fold.lean`)
takes.
-/

namespace ConLeche.Semantics
open ConLeche.Term ConLeche.Verify

variable {pins : List NatOpPinSet}

/-- **The `.indDecl` dispatch at the run level, at k members**: the
kernel's own case split (`blockShape?`), with the uniform arm recorded
as the k-ary run `DeclBlockRun` (`Semantics/Inductives/DeclBlock.lean`)
at any number of members, nested blocks included.  A block the
recogniser does not read never installs (`checkShapeless` declines), so
its arm is `False`. -/
def DeclIndRunDispatchK (F : Nat) (env : Env)
    (block : List ConstantInfo) (nP : Nat) (env₂ : Env) : Prop :=
  match ConLeche.blockShape? nP block with
  | some p => BlockRun F env block p env₂
  | none => False

/-- **A block the recogniser does not read never installs**:
`checkShapeless` ends in a decline whatever its formers' checks do. -/
theorem checkShapeless_ne_ok {ops : CheckerOps CheckM} {env env₂ : Env}
    {block : List ConstantInfo} : checkShapeless ops env block ≠ .ok env₂ := by
  unfold checkShapeless
  simp only [bind, Except.bind]
  split <;> simp [throw, throwThe, MonadExceptOf.throw]

/-- **The RUN bridge**: `checkDecl` → `DeclRun`, with the
uniform arm recorded as `BlockRun` (`blockRun_of`).  The run
relation records the recursor stage as one opaque conjunct
(`checkBlockRec … = .ok rs`). -/
theorem checkDeclRun_ofEnvFactsK
    {F : Nat} {env env₂ : Env}
    {d : Declaration}
    (h : checkDecl .verified (fueledOps .verified F) pins env d = .ok env₂) :
    DeclRun F (DeclIndRunDispatchK F env) env d env₂ :=
  checkDeclRun_of
    (fun {block nP} hpin hh => by
      -- task #293: the pinned-block recognition came first, and this
      -- block is not one of the five
      simp only [checkDecl, hpin] at hh
      rw [DeclIndRunDispatchK]
      -- the declared parameter count (task #228): a run that reached
      -- the dispatch passed the guard
      by_cases hok : indParamsOk nP block = true
      · rw [ite_eq_left hok] at hh
        revert hh
        cases hdf : blockShape? nP block with
        | some p =>
          intro hh
          exact blockRun_of (ConLeche.blockShape?_declared hdf) hh
        | none =>
          intro hh
          exact checkShapeless_ne_ok hh
      · rw [ite_eq_right hok] at hh
        exact nomatch hh) h

end ConLeche.Semantics
