module

public import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Level
import ConLeche.Model.Annot.Bit
public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.Shift
import ConLeche.Model.BasisEmpty
import ConLeche.Model.Annot.Laws
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Inductives.BlockRecInv
public import ConLeche.Model.Annot.EnvModelM
import ConLeche.Model.Capstone

public section

/-!
# The recursor stage's readings

Facts about how the recursor stage's stored terms read, for
`blockRecStaged_of`'s premises (`Model/Inductives/BlockStageRec.lean`):
the `instPisAtLift` reading
battery, and the stored types' readings with their grading.

The family's level arithmetic rests on the elimination-level PIN
(`checkBlockRecElimPin`): every recursor's conclusion sort — the sort
the kernel's own sort check gave it — is `Level.isEquiv` to the
generated level `structElimLevel p.elim p.large` (the family record's
`RecFamFacts.pin`, `Verify/Inductives/RecStage.lean`).  The model
reads it at a ground assignment (`blockRecElimPin_run`,
`BlockRecPreRun.lean` §38.1): the family eliminates at ONE level, the
checked one.
-/

namespace ConLeche.Model
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)


/-! ## The `instPisAtLift` reading battery

A rule's generated forms are
built with `Expr.instPisAtLift`, and the ih telescope is opened with
`Expr.instantiateList`; both are written for arguments that may mention
the ambient binders, while `denoteMeta_beta` wants a bvar-CLOSED
replacement.  At the frame `denoteMeta` actually reads — the rule body
OPENED at fvars — the arguments ARE bvar-closed, and there both
operations collapse onto ones the model owns
(`instPisAtLift_eq_instPisAt`, `instantiateList_eq_instSeq`,
`Verify/Inductives/BlockRecInv.lean`), so the readings are corollaries,
not new inductions. -/

variable {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}

/-- **The reading of an `instPisAtLift` peel**, at bvar-closed
arguments: `denoteMeta_instPisAt_peel` through
`instPisAtLift_eq_instPisAt`. -/
theorem denoteMeta_instPisAtLift_peel
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {d : Nat} (args : List Expr) {ty rest : Expr} {Ta : AnnotTerm} {vs : List AnnotTerm}
    (hpr : Expr.instPisAtLift args ty = some rest)
    (hw : Expr.WScoped d ty)
    (ha : ∀ a ∈ args, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    (hty : denoteMeta acval env φ d ty = some Ta)
    (hsp : DenoteMetaSpine acval env φ d args vs) :
    ∃ restA, denoteMeta acval env φ d rest = some restA ∧
      ConLeche.Model.AnnotTerm.peelPis Ta vs = some restA := by
  rw [ConLeche.instPisAtLift_eq_instPisAt (fun a hmem => (ha a hmem).2)] at hpr
  cases hpa : Expr.instPisAt args ty with
  | none => rw [hpa] at hpr; exact nomatch hpr
  | some p =>
    rw [hpa] at hpr
    obtain rfl : p.2 = rest := Option.some.inj hpr
    exact ConLeche.Model.Rules.denoteMeta_instPisAt_peel hacl hainst args (ds := p.1) (by rw [hpa]) hw ha hty hsp

/-! ## The stored types READ, and their readings are GRADED

`blockRecStaged_of`'s `hrd` has three components: the recursor's
stored type reads, its reading is graded, and the leaf inhabits it.
The first two are **run facts** — the type's check ran `inferType`
on the STORED type at the constructors' environment, which is
exactly the hypothesis `acceptedReads_of` and the infer claim want —
and this is them.  The third is the recursion theorem and belongs to
the recursor model (`graphRecPre_core`).

The recipe is the one every harvest uses (`harvestDefn`,
`Model/Harvest.lean`): the stored type's own scoping, `acceptedReads_of`
for the reading, and `checkSoundAt`'s
infer claim (through `inferReads_of` for the inferred type's own
reading) for the grading. -/

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **A checked constant's type reads, the reading is graded, AND it
lands in the universe the check's own `ensureSort` named.**

The sort component is one step further into the pair the grading
already runs: the check infers the stored type and `ensureSort`s the
result, and `ensureSortCore_inv` turns that into the `whnf`-to-a-sort
`SortSemAt` asks for — so the same claims (`WhnfClaim` + `InferClaim` +
`InferReads`) that grade the reading also place it in
`univ (u.eval ψ)`.  What it reads of the check (`ConstChecked`) is the
stored type closed and inferred; annotation plays no part, so the
generated stage's `classConstOk` (the type stored as generated) supplies
it as the stream's `checkConstantVal` does.

**This is the `hlvl` route**: the level a recursor's type lives at is
the check's INFERRED one, and it already accounts for the binders'
levels, so nothing has to pin the reading's binder numerals. -/
theorem constChecked_reads {env : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env) {F : Nat} {cv cvA : ConstantVal}
    (h : ConLeche.ConstChecked μ F env cv cvA) :
    ∃ u : Level, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, interp V ρ ta ∈ˢ (univ (u.eval ψ) : V) := by
  obtain ⟨stype, u, hrun, hsort⟩ := h.sorted
  refine ⟨u, fun ψ => ?_⟩
  have htf' := h.noFvar
  have hbt' := h.bounded
  have hwt : Expr.WScoped 0 cvA.type := Expr.WScoped.of_not_hasFvar htf'
  have hnlt : cvA.type.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hLt : Expr.LeavesBounded cvA.type := fun l hl => by
    rw [hnlt] at hl
    exact absurd hl (List.not_mem_nil)
  obtain ⟨ta, hta⟩ := acceptedReads_of mp.base2 ψ hrun hwt hbt' hLt
  obtain ⟨-, ihw, -, ihi⟩ := checkSoundAt (V := V) hμ (Rules.RulesInputs.ofSem mp ψ) F
  have hsem := sortSemAt_of_claims ihw ihi
    (inferReads_of hμ (Rules.RulesInputs.ofSem mp ψ))
    (CtxOk.nil hnlt) hwt hbt' hLt hrun (ConLeche.ensureSortCore_inv hsort) hta
  exact ⟨ta, hta, fun ρ => (hsem ρ (ConLeche.Semantics.Sat_nil V ρ)).1,
    fun ρ => (hsem ρ (ConLeche.Semantics.Sat_nil V ρ)).2⟩

/-- **`hrd`'s first two components, at the whole recursor stage.**
Every stored recursor's type reads at the constructors' environment
and its reading is graded — from the stage's own
type checks (`ConstChecked`), at the type record of each stored recursor
(`RecStage.tyGenAt`, `Verify/Inductives/RecStage.lean`). -/
theorem recStage_tyReads {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR) :
    ∀ r ∈ rs, ∃ u : Level, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, interp V ρ ta ∈ˢ (univ (u.eval ψ) : V) := by
  obtain ⟨R⟩ := id h
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  obtain ⟨rc, u, -, -, ⟨E⟩⟩ := R.tyGenAt hi
  exact constChecked_reads hμ mpC E.hcv

/-- **`blockRecStaged_of`'s `hrd`, reduced to the MEMBERSHIP.**  The
reading and its grading are the run's (`recStage_tyReads`); what
is left is that the leaf inhabits the reading — the recursion theorem,
which the recursor model delivers as `hmem` in this shape. -/
theorem hrd_of_mem {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {acv : Name → (Name → Nat) → AnnotTerm}
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC p cvTas ctorsAs rs memR)
    (hmem : ∀ r ∈ rs, ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta →
      ∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta) :
    ∀ r ∈ rs, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta) := by
  intro r hr ψ
  obtain ⟨_, hru⟩ := recStage_tyReads (V := V) hμ mpC h r hr
  obtain ⟨ta, hta, hok, -⟩ := hru ψ
  exact ⟨ta, hta, hok, hmem r hr ψ ta hta⟩

end ConLeche.Model
