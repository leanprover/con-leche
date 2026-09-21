module

public import ConLeche.Model.Inductives.DeclNative
import ConLeche.Verify.Inductives.BlockOne
public section

/-!
# The uniform block install, assembled (task #315 M3)

`declBlock_one`: **the P carrier survives the UNIFORM install's run at
one member.**  This is the Model tier's half of the milestone-M1 flip
stated over the uniform installer itself (`checkBlock`), not over the
one-member installer it bridges to — the shape `Model/Fold.lean`'s
dispatch will take once the route is ungated.

At `k = 1` it is `declNative` through the two bridges of milestone M1:
the recogniser's (`blockParts?_toNative`: a recognised one-member
block IS a recognised native block at `BlockParts.toNative`, and its
member list is a singleton) and the installer's
(`declNativeRun_of_block_one`: the same `checkBlock … = .ok` is a
`DeclNativeRun` at that reading, because `checkBlock_one` identifies
the two installers).  So no stage is re-proved here, and `declNative`
remains the `k = 1` discharge, exactly as lane V's note says.

**What is NOT here**: `declBlock` for all `k`, and the named fact
`BlockRecStaged` its recursor stage would carry.  Both wait on the
stage theorems (the k-former loop, the constructors' loop over
members, the tables per structure-like member); writing the named fact
before its stage shapes are fixed would be a hypothesis without a
run-level consumer.  What exists of the stage chain today is listed in
`_tmp/uniform-inds/M3-REPORT.md` §3.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockParts BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The P carrier survives the uniform install at one member.**  The
hypothesis is the uniform installer's own success, so the statement
does not mention `nativeParts?`, `checkNative` or `DeclNativeRun` —
only milestone M1's two bridges do, inside the proof. -/
theorem declBlock_one (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.blockParts? nPd block = some p₀)
    (h : ConLeche.checkBlock (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p₀
      = .ok env₂) :
    Nonempty (EnvModelM V μ env₂) :=
  declNative hμ mp hE (ConLeche.blockParts?_toNative hdp).1
    (ConLeche.Semantics.declNativeRun_of_block_one
      (ConLeche.blockParts?_toNative hdp).2.choose_spec h)

end ConLeche.Model
