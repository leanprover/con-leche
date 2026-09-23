module

public import ConLeche.Semantics.Inductives.DeclNative
import ConLeche.Semantics.Bridge.DeclRun
import ConLeche.Semantics.Bridge.DeclIndRun

@[expose] public section

/-!
# The RUN bridge at the ONE-MEMBER reading of the uniform route

`checkDeclRun_ofEnvFactsE` records the uniform route's arm as a
`DeclNativeRun` at the one-member reading of the record
(`DeclIndRunDispatch`), which only the route's gate
(`blockRouteK1Only`, read through `blockParts?_k1`) makes exact.  It is
the P fold's current input (`Model/Fold.lean`'s `declStep_preserves`).

**This file is deleted at the flip**, with the gate: the k-ary twin
that holds at every setting of both gates is `checkDeclRun_ofEnvFactsK`
(`ConLeche/Semantics/Bridge/Sound.lean`), whose uniform arm is
`DeclBlockRun` and which the fold switches to together with its
`declBlock` endpoint.  It is split out so that `Sound.lean` itself
survives the flip probe (lane FLIP1).
-/

namespace ConLeche.Semantics
open ConLeche.Term ConLeche.Verify

variable {pins : List NatOpPinSet}
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
    (h : checkDecl μ (fueledOps μ F) pins env d = .ok env₂) :
    DeclRun μ F (DeclIndRunDispatch μ F env) env d env₂ :=
  checkDeclRun_of
    -- FLAG-AGNOSTIC (task #175 wiring W4): case on the `.indDecl`
    -- clause's own `blockParts?` dispatch — `declNativeRun_of_block_one`
    -- on the direct arm, `declIndRun_of` on the modeled one.
    (fun {block nP} hpin hh => by
      -- task #293: the pinned-block recognition came first, and this
      -- block is not one of the five
      simp only [checkDecl, hpin] at hh
      rw [DeclIndRunDispatch]
      -- the declared parameter count (task #228): a run that reached
      -- the dispatch passed the guard
      by_cases hok : indParamsOk nP block = true
      · rw [if_pos hok] at hh
        revert hh
        cases hdf : blockParts? nP block with
        | some p =>
          intro hh
          obtain ⟨⟨ms, hms⟩, rc, hrc⟩ := blockParts?_k1 rfl hdf
          exact declNativeRun_of_block_one hms hrc hh
        | none =>
          intro hh
          exact declIndRun_of hh
      · rw [if_neg hok] at hh
        exact nomatch hh) h

end ConLeche.Semantics
