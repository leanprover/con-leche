module

public import ConLeche.Semantics.Inductives.DeclNative
public import ConLeche.Semantics.Inductives.DeclBlock
public import ConLeche.Semantics.Bridge.SoundOne
import ConLeche.Semantics.Bridge.DeclRun
import ConLeche.Semantics.Bridge.DeclIndRun

@[expose] public section

/-!
# The assembly (task #148, T6): the RUN bridge

`checkDecl` → `DeclRun` by dispatch, off no invariant at all.

**What this file used to hold, and why it does not (2026-09-05).**  The
assembly had two halves: the *derivation* bridge
(`checkDeclR_ofEnvR`/`checkDeclR_ofEnvRE`, `checkDecl` → `DeclR` off
the V-free `EnvFacts`) and the *run* bridge below.  S11a's whole point was
that the graded fold needs only the second — the run/guard record, with
no derivation on the path — and a proof-term probe at the SetR
removal's Stage C confirmed it at the criterion that matters: the
derivation half was absent from every capstone's closure AND from this
file's own surviving theorem.  It went with the R tier
(`Bridge/{Main,Decl,DeclInd,…}`, `SetBase/{Rel,Weaken,CtxOkR}`) that
built it.

**The uniform route's arm, at k members (lane FLIP1).**  The run
bridge here records it as `DeclBlockRun` (`DeclIndRunDispatchK`), which
holds at every setting of the two gates; the one-member twin the fold
still reads (`checkDeclRun_ofEnvFactsE`, at `DeclIndRunDispatch`) is in
`Bridge/SoundOne.lean`, re-exported from here and deleted at the flip.
-/

namespace ConLeche.Semantics
open ConLeche.Term ConLeche.Verify

variable {pins : List NatOpPinSet}

/-- **The `.indDecl` dispatch at the run level, at k members**: the
kernel's own case split (`blockParts?`), with the uniform arm recorded
as the k-ary run `DeclBlockRun` (`Semantics/Inductives/DeclBlock.lean`)
rather than at the one-member reading of the record
(`DeclIndRunDispatch`).  It reads neither gate: it is the dispatch the
fold takes at the flip. -/
def DeclIndRunDispatchK (μ : CheckMode) (F : Nat) (env : Env)
    (block : List ConstantInfo) (nP : Nat) (env₂ : Env) : Prop :=
  match ConLeche.blockParts? nP block with
  | some p => DeclBlockRun μ F env p env₂
  | none => DeclIndRun μ F env block env₂

/-- **The RUN bridge at k members** (lane FLIP1): `checkDeclRun_ofEnvFactsE`
with the uniform arm recorded as `DeclBlockRun` (`declBlockRun_of`).
Unlike its one-member twin it holds at EVERY setting of both gates
(`blockRecCheckOn`, `blockRouteK1Only`): the run relation records the
recursor stage as one opaque conjunct (`checkBlockRec … = .ok rs`), so
nothing here reads which stage the gate selects. -/
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
          exact declIndRun_of hh
      · rw [if_neg hok] at hh
        exact nomatch hh) h

end ConLeche.Semantics
