module

public import ConLeche.Model.Annot.EnvModelM
public import ConLeche.Semantics.DeclRun
import ConLeche.Model.AxiomReduce
import ConLeche.Model.BasisEq
import ConLeche.Model.BasisFalse

public section

/-!
# The VALUE KINDS' CARRIER AGREEMENTS (task #315, M8 step 1)

The axiom kind's and the basis kind's steps, each carrying the fact
that the model it hands back values every OLD constant as the prefix
model did (`AcvalAgrees`).  This is what the environment model's
block field is maintained by — `EnvModelB.blocks` is a function of the
carrier at the stored inductives, so an install that leaves the old
carrier alone leaves the assignment alone
(`EnvModelBStages.lean`, `BasisBlocksFold.lean`).

They live HERE, below `Model/Fold.lean`, and not in it (DESIGN §U.56
(g) 1): the fold's own theorems at `EnvModelB` sit ABOVE the two
modules that read these agreements, so as long as the agreements lived
in `Model/Fold.lean` every theorem of the flip was above that module
and the `B` fold had nowhere to go.  Beside the harvests they are just
the two kinds' steps with their agreement kept, and `Model/Fold.lean`
projects them to the `Nonempty` bundles the census reads
(`axiomStepPB_of`, `basisStepPB_of`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (CheckMode Env ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- **The axiom kind's step, WITH THE CARRIER AGREEMENT** (task #315
M7-3): every `DeclAxiomR` branch conses one fresh `axiomInfo` (or, at
the tolerated skip, nothing), so the model it produces values every OLD
constant as the prefix model did — the fact the block-model field
`EnvModelB.blocks` is maintained by (`EnvModelBStages.lean`).
`axiomStepPB_of` is its `Nonempty` projection. -/
theorem axiomStepAgree_of (hμ : μ.verifiedChecks = true) {F : Nat} {env : Env}
    (mp : EnvModelM V μ env) {cv : ConstantVal} {env₂ : Env}
    (hR : DeclAxiomRun μ F env cv env₂) :
    ∃ mp' : EnvModelM V μ env₂, AcvalAgrees mp.base2 mp'.base2 := by
  -- the `Quot.sound` arm (task #293) installs nothing
  rcases hR with ⟨-, rfl⟩ | hR
  · exact ⟨mp, AcvalAgrees.rfl' _⟩
  obtain ⟨type', hcv, hbranch⟩ := hR
  rcases hbranch with ⟨hok, rfl⟩ | ⟨hname, hok, rfl⟩ |
    ⟨hor, hok, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · exact axiomStd hμ mp hcv hok
  · exact axiomTrustCompiler hμ mp hcv hname hok
  · exact axiomOfReduce hμ mp hcv hor hok
  · exact axiomSkip mp

/-- **The basis kind's step, WITH THE CARRIER AGREEMENT** (task #315
M7-3 session 9, DESIGN §U.55 (b)): every pinned block is a chain of
three to five fresh conses, so the model it produces values every OLD
constant as the prefix model did — the fact the block-model field
`EnvModelB.blocks` is maintained by, and the one the basis blocks'
`EnvBlocksOf.extendBasisOf` cannot state about an anonymous model.
`basisStepPB_of` is its `Nonempty` projection.

`quotK` is the one branch whose `DeclBasisRun` guard is not vacuous: it
needs `Eq` in the prefix, which is what the block's `Eq` bridge
consumes. -/
theorem basisStepAgree_of {env : Env} (mp : EnvModelM V μ env)
    {kind : ConLeche.BasisKind} {env₂ : Env} (h : DeclBasisRun env kind env₂) :
    ∃ mp' : EnvModelM V μ env₂, AcvalAgrees mp.base2 mp'.base2 := by
  obtain ⟨hEq, hchain⟩ := h
  cases kind with
  | eqK => exact declBasisPB_eqK mp hchain
  | natK => exact declBasisPB_natK mp hchain
  | punitK => exact declBasisPB_punitK mp hchain
  | emptyK => exact declBasisPB_emptyK mp hchain
  | falseK => exact declBasisPB_falseK mp hchain
  | quotK => exact declBasisPB_quotK mp (hEq rfl) hchain

end ConLeche.Model
