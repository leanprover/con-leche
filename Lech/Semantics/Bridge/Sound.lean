import Lech.Semantics.Direct.DeclDirectSum
import Lech.Semantics.Bridge.DeclRun
import Lech.Semantics.Bridge.DeclIndRun

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
-/

namespace Lech.Semantics
open Lech.TT Lech.TTVerify
universe w


/-- **The RUN bridge, whole, from an `EnvFacts`** (task #161 S11a): the
run/guard record, from the checker, with **no derivation on the path
except through the `ind` kind's premise**.

This is `checkDeclR_ofEnvRE`'s run twin and the theorem the graded
lane's fold now imports.  The difference is not cosmetic and is the
batch's whole point (the S10 seal's residual B): the deleted
`checkDeclRun_sound` — `DeclR.toRun` composed *after*
`checkDeclR_sound` — projected the derivation conjuncts away in its
*statement* while keeping them in its *proof term*, so the P lane
inherited `Red.beta` for a record it never reads.  Here the five
non-`ind` kinds never build one
(`checkDeclRun_of`, `SetBase/Bridge/DeclRun.lean`), and the sixth
enters through `declIndRR` alone — one named door, in the parameter
slot S4 built for it, which S11b replaces with the `ind` run bridge.

The collapsed lane's projection route (`checkDeclRun_sound`) is gone:
S11b's opener deleted it, consumer-free. -/
theorem checkDeclRun_ofEnvFactsE
    {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {d : Declaration}
    (h : checkDecl μ (fueledOps μ F) env d = .ok env₂) :
    DeclRun μ F (DeclIndRunDispatch μ F env) env d env₂ :=
  checkDeclRun_of
    -- FLAG-AGNOSTIC (task #175 wiring W4): case on the `.indDecl`
    -- clause's own `directParts?` dispatch — `declDirectRun_of` on the
    -- direct arm, `declIndRun_of` on the modeled one.
    (fun {block} hh => by
      rw [checkDecl] at hh
      rw [DeclIndRunDispatch]
      revert hh
      cases hdp : directParts? env block with
      | some p =>
        intro hh
        exact declDirectRun_of hh
      | none =>
        cases hds : directSumParts? env block with
        | some p =>
          intro hh
          exact declDirectSumRun_of hh
        | none =>
          intro hh
          exact declIndRun_of hh) h

end Lech.Semantics
