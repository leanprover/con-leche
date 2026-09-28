module

public import ConLeche.Semantics.Inductives.DeclBlock
public import ConLeche.Semantics.DeclRun
import ConLeche.Verify.EnvGuards
import ConLeche.Semantics.Bridge.DeclRun
import ConLeche.Semantics.Inductives.DeclBlockEtaRun

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
kernel's own case split (`blockParts?`), with the uniform arm recorded
as the k-ary run `DeclBlockRun` (`Semantics/Inductives/DeclBlock.lean`)
at any number of members, nested blocks included.  A block the
recogniser does not read never installs (`checkShapeless` declines), so
its arm is `False`. -/
def DeclIndRunDispatchK (μ : CheckMode) (F : Nat) (env : Env)
    (block : List ConstantInfo) (nP : Nat) (env₂ : Env) : Prop :=
  match ConLeche.blockParts? nP block with
  | some p => DeclBlockRun μ F env block p env₂
  | none => False

/-- **A block the recogniser does not read never installs**:
`checkShapeless` ends in a decline whatever its formers' checks do. -/
theorem checkShapeless_ne_ok {ops : CheckerOps CheckM} {env env₂ : Env}
    {block : List ConstantInfo} : checkShapeless ops env block ≠ .ok env₂ := by
  unfold checkShapeless
  simp only [bind, Except.bind]
  split <;> simp [throw, throwThe, MonadExceptOf.throw]

/-- **The RUN bridge**: `checkDecl` → `DeclRun`, with the
uniform arm recorded as `DeclBlockRun` (`declBlockRun_of`).  The run
relation records the recursor stage as one opaque conjunct
(`checkBlockRec … = .ok rs`). -/
theorem checkDeclRun_ofEnvFactsK
    {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) pins env d = .ok env₂) :
    DeclRun μ F (DeclIndRunDispatchK μ F env) env d env₂ :=
  checkDeclRun_of
    (fun {block nP} hpin hh => by
      -- task #293: the pinned-block recognition came first, and this
      -- block is not one of the five
      simp only [checkDecl, hpin] at hh
      rw [DeclIndRunDispatchK]
      -- the declared parameter count (task #228): a run that reached
      -- the dispatch passed the guard
      by_cases hok : indParamsOk nP block = true
      · rw [if_pos hok] at hh
        revert hh
        cases hdf : blockParts? nP block with
        | some p =>
          intro hh
          exact declBlockRun_of hh
        | none =>
          intro hh
          exact checkShapeless_ne_ok hh
      · rw [if_neg hok] at hh
        exact nomatch hh) h

/-- **The `.indDecl` run dispatch keeps the η-families closed**, by the
kernel's own case split — the uniform arm's
`declBlockRun_etaClosed`; the other arm never runs. -/
theorem declIndRunDispatchKEtaClosed {μ : CheckMode} {F : Nat}
    {env envI : Env} {block : List ConstantInfo} {nP : Nat}
    (hE : EtaFamiliesClosed env)
    (h : DeclIndRunDispatchK μ F env block nP envI) : EtaFamiliesClosed envI := by
  unfold DeclIndRunDispatchK at h
  split at h
  · exact declBlockRun_etaClosed hE h
  · exact h.elim

end ConLeche.Semantics
