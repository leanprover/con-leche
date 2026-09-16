module

public import ConLeche.Model.Inductives.ContainerCross
import ConLeche.Semantics.DeclRun
import ConLeche.Model.Fold
import ConLeche.Model.Harvest
public section

/-!
# The fold's stages at the model WITH ITS BLOCKS (task #315, M7-3)

`EnvModelB` (`NestedPremise.lean`) is `EnvModelM` plus
`EnvBlockModels` — every stored container's block model at the
carrier.  A field is only as good as its MAINTENANCE, and this module
is the maintenance at the fold's VALUE kinds: definitions, theorems,
opaques and axioms.

Each of them is a `NonIndStep` (`ContainerCross.lean`): the stage
installs nothing at all (the tolerated axiom skip, `Quot.sound`'s
record) or conses ONE fresh constant whose head is a `defnInfo`,
`thmInfo` or `axiomInfo` — never one of the three kinds
`containerInfo?` consults, and never a projection table.  So no
container's block moves, and the only model-facing input is the
carriers' agreement at the stored names (`AcvalAgrees`), which the
stages now hand back: the cons-level step always proved it (its
`acvalWith` equation) and the stage theorems used to drop it
(`exists_agrees_of_cons`, `Model/Install.lean`).

**The INDUCTIVE kinds are not here, and cannot be yet** (DESIGN
§U.31): a route that installs a block must supply the block model of
the block it just installed, AT THE READING `containerInfo?` makes of
it back off the environment — and no route records that reading.  The
kernel request is §U.31's K.34.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal ReducibilityHint)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {F : Nat} {env env₂ : Env}

/-! ## The value kinds are non-inductive steps -/

/-- A definition conses one fresh `defnInfo`. -/
theorem declDefnRun_nonIndStep {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hR : DeclDefnRun μ F env cv value hint env₂) : NonIndStep env env₂ := by
  obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hR
  exact Or.inr ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint, rfl,
    Option.isNone_iff_eq_none.mp hcv.1,
    (fun _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ h => ConstantInfo.noConfusion h)⟩

/-- A theorem conses one fresh `thmInfo`. -/
theorem declThmRun_nonIndStep {cv : ConstantVal} {value : Expr}
    (hR : DeclThmRun μ F env cv value env₂) : NonIndStep env env₂ := by
  obtain ⟨type', -, hcv, -, -, rfl⟩ := hR
  exact Or.inr ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value, rfl,
    Option.isNone_iff_eq_none.mp hcv.1,
    (fun _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ h => ConstantInfo.noConfusion h)⟩

/-- An opaque conses one fresh `axiomInfo` (the store is by statement:
an opaque is opaque to reduction). -/
theorem declOpaqueRun_nonIndStep {cv : ConstantVal} {value : Expr}
    (hR : DeclOpaqueRun μ F env cv value env₂) : NonIndStep env env₂ := by
  obtain ⟨type', -, hcv, -, rfl, -⟩ := hR
  exact Or.inr ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, rfl,
    Option.isNone_iff_eq_none.mp hcv.1,
    (fun _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ h => ConstantInfo.noConfusion h)⟩

/-- An axiom conses one fresh `axiomInfo`, or — at `Quot.sound`'s
record and at the tolerated `sorryAx` skip — nothing. -/
theorem declAxiomRun_nonIndStep {cv : ConstantVal}
    (hR : DeclAxiomRun μ F env cv env₂) : NonIndStep env env₂ := by
  rcases hR with ⟨-, rfl⟩ | ⟨type', hcv, hbranch⟩
  · exact Or.inl rfl
  have hfresh : env.find? cv.name = none := Option.isNone_iff_eq_none.mp hcv.1
  rcases hbranch with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · exact Or.inr ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, rfl, hfresh,
      (fun _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ h => ConstantInfo.noConfusion h)⟩
  · exact Or.inr ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, rfl, hfresh,
      (fun _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ h => ConstantInfo.noConfusion h)⟩
  · exact Or.inr ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, rfl, hfresh,
      (fun _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ h => ConstantInfo.noConfusion h)⟩
  · exact Or.inl rfl

/-! ## The four lifts -/

/-- **A definition keeps the model AND its blocks.** -/
theorem envModelB_defn (hμ : μ.verifiedChecks = true) (mb : EnvModelB V μ env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hR : DeclDefnRun μ F env cv value hint env₂) : Nonempty (EnvModelB V μ env₂) := by
  obtain ⟨mp', hag⟩ := harvestDefn hμ mb.toEnvModelM hR
  exact ⟨EnvModelB.ofNonIndStep mb mp' (declDefnRun_nonIndStep hR) hag⟩

/-- **A theorem keeps the model AND its blocks.** -/
theorem envModelB_thm (hμ : μ.verifiedChecks = true) (mb : EnvModelB V μ env)
    {cv : ConstantVal} {value : Expr}
    (hR : DeclThmRun μ F env cv value env₂) : Nonempty (EnvModelB V μ env₂) := by
  obtain ⟨mp', hag⟩ := harvestThm hμ mb.toEnvModelM hR
  exact ⟨EnvModelB.ofNonIndStep mb mp' (declThmRun_nonIndStep hR) hag⟩

/-- **An opaque keeps the model AND its blocks.** -/
theorem envModelB_opaque (hμ : μ.verifiedChecks = true) (mb : EnvModelB V μ env)
    {cv : ConstantVal} {value : Expr}
    (hR : DeclOpaqueRun μ F env cv value env₂) : Nonempty (EnvModelB V μ env₂) := by
  obtain ⟨mp', hag⟩ := harvestOpaque hμ mb.toEnvModelM hR
  exact ⟨EnvModelB.ofNonIndStep mb mp' (declOpaqueRun_nonIndStep hR) hag⟩

/-- **An axiom keeps the model AND its blocks.** -/
theorem envModelB_axiom (hμ : μ.verifiedChecks = true) (mb : EnvModelB V μ env)
    {cv : ConstantVal}
    (hR : DeclAxiomRun μ F env cv env₂) : Nonempty (EnvModelB V μ env₂) := by
  obtain ⟨mp', hag⟩ := axiomStepAgree_of hμ mb.toEnvModelM hR
  exact ⟨EnvModelB.ofNonIndStep mb mp' (declAxiomRun_nonIndStep hR) hag⟩

/-- **The empty environment carries the blocks vacuously** (the fold's
base case): nothing is stored, so `containerInfo?` reads nothing. -/
noncomputable def EnvModelB.empty (V : Type w) [SetTheory V] (μ : CheckMode) :
    EnvModelB V μ Env.empty where
  toEnvModelM := EnvModelM.empty V μ
  blocks := ⟨fun _ => Classical.choice inferInstance, fun J ci hci => by
    obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci
    exact nomatch hf⟩

end ConLeche.Model
