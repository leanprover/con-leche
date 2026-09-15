module

public import ConLeche.Semantics.Inductives.DeclNative
public import ConLeche.Model.Annot.EnvModelM
import ConLeche.Model.Inductives.DeclNative
import ConLeche.Model.DeclInd
public section

/-!
# `declInductive` — THE model theorem of an inductive block, one statement for every block kind (task #315)

The uniform route's contract: **one** theorem, `declInductive`, says
that the model survives the `.indDecl` dispatch — whatever block the
stream carries (single, mutual, nested, indexed, reflexive,
structure-like, `Prop` or `Type`).  Its premises are the mode, the
pre-block model, the η-family closure and the RUN relation of the
dispatch; its conclusion a model of the post-block environment.

Today the dispatch (`DeclIndRunDispatch`, `Semantics/Inductives/DeclNative.lean`)
has two arms — the ONE fixpoint route (`checkNative`, task #210) for a
recognised single block and the modeled route (`checkModeled`) for the
rest — and the proof below is the fold's own case split
(`declStep_preserves`, `Model/Fold.lean`).  The uniform route
(DESIGN §U.1) changes what stands under this statement, milestone by
milestone — the native arm generalised to `k` members, a nested block's
shape check, the modeled arm deleted — and never the statement.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche (CheckMode Env ConstantInfo)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- **The model survives an inductive block** — ONE statement for every
block kind, over the `.indDecl` dispatch's run relation. -/
theorem declInductive (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nP : Nat} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env)
    (h : ConLeche.Semantics.DeclIndRunDispatch μ F env block nP env₂) :
    Nonempty (EnvModelM V μ env₂) := by
  unfold ConLeche.Semantics.DeclIndRunDispatch at h
  cases hdf : ConLeche.nativeParts? nP block with
  | some p =>
    rw [hdf] at h
    exact declNative hμ mp hE hdf h
  | none =>
    rw [hdf] at h
    exact declInd hμ mp hE h

end ConLeche.Model
