module

import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Level
import ConLeche.Model.Annot.Bit
public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.Shift
import ConLeche.Model.BasisEmpty
import ConLeche.Model.Annot.Laws
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Inductives.BlockRecInv
import ConLeche.Verify.Inductives.BlockRecRun
public import ConLeche.Model.Annot.EnvModelM
import ConLeche.Model.Capstone

public section

/-!
# The recursor stage's readings

Facts about how the recursor stage's stored terms read, for
`blockRecStaged_of`'s premises (`Model/Inductives/BlockStageRec.lean`):
the family's one elimination level, the `instPisAtLift` reading
battery, and the stored types' readings with their grading.

The family's level arithmetic rests on the elimination-level PIN
(`checkBlockRecElimPin`): every recursor's conclusion sort — the sort
the kernel's own sort check gave it — is `Level.isEquiv` to the
generated level `structElimLevel p.elim p.large` (the family record's
`RecFamRun.pin`, `Verify/Inductives/BlockRecRun.lean`).  The model
consumes `Level.eval` at a ground assignment (`Level.isEquiv_sound`),
so a family has ONE elimination level — `OneElimLevel` at the family's
single `ℓ`.
-/

namespace ConLeche.Model
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

/-! ## One elimination level, at the valuation -/

/-- **One elimination level per family, at a ground assignment**, from
the elimination-level PIN: every level of the list is equivalent to
`L`, so every one EVALUATES to the first one's at every `ψ`, and the
Σ'-chain has one level and the candidate one tower bit. -/
theorem blockRecElimPin_eval {L : Level} {us : List Level}
    (h : ∀ u ∈ us, Level.isEquiv u L = some true)
    (ψ : Name → Nat) : ∀ u ∈ us, u.eval ψ = (us.headD .zero).eval ψ := by
  intro u hu
  cases us with
  | nil => exact absurd hu List.not_mem_nil
  | cons u0 rest =>
    rw [List.headD_cons, Level.isEquiv_sound (h u hu) ψ,
      Level.isEquiv_sound (h u0 List.mem_cons_self) ψ]

/-- **The zeroness bit is the family's**, which is exactly the shape
`OneElimLevel` (`Semantics/Tower/BlockRecKitI.lean`) asks for once the
recursors' conclusions' sorts are the readings' binder numerals: at
the family's single `ℓ := (us.headD .zero).eval ψ`, a conclusion sort
is zero iff `ℓ` is. -/
theorem blockRecElimPin_zero_iff {L : Level} {us : List Level}
    (h : ∀ u ∈ us, Level.isEquiv u L = some true)
    (ψ : Name → Nat) {u : Level} (hu : u ∈ us) :
    ((us.headD .zero).eval ψ = 0 ↔ u.eval ψ = 0) := by
  rw [blockRecElimPin_eval h ψ u hu]

/-! ## Why `blockIhCall?` compares EXACTLY

`denoteMeta` does not respect `Expr.resetMeta`: `resetMeta` forces
every binder's datum to `⟨.never⟩`, whose bit is `1`, while a datum
that holds at `φ` reads `0`, and `interp` is not bit-blind —
`lamR`/`piR` take the bit.  So two `resetMeta`-equal expressions can
denote differently.  `blockIhCall?`'s comparison
(`Kernel/Inductives/BlockRec.lean`) is the ONLY tie between the stored
right-hand side's call node and the spine the ι law is stated at, so
it compares EXACTLY, binder data included (`e != expected`), and
`IhCallRun` (`Verify/Inductives/BlockRecInv.lean`) exports
`e = expected`: the call node's annotated index expressions are the
constructor's stored ones, syntactically.  A comparison up to
`resetMeta` would leave a reading that cannot be transported. -/

/-- The witness: two `resetMeta`-equal expressions whose readings
differ (`⟨.never⟩` against `⟨.ifAllZero []⟩` on a λ-binder). -/
theorem not_denoteMeta_resetMeta_invariant :
    ∃ (e₁ e₂ : Expr) (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
      (φ : Name → Nat) (d : Nat),
      Expr.resetMeta e₁ = Expr.resetMeta e₂ ∧
      denoteMeta acval env φ d e₁ ≠ denoteMeta acval env φ d e₂ := by
  refine ⟨.lam (.sort .zero) (.sort .zero) ⟨ConLeche.PropWhen.never⟩,
    .lam (.sort .zero) (.sort .zero) ⟨ConLeche.PropWhen.ifAllZero []⟩,
    (fun _ _ => .prf), ⟨[]⟩, (fun _ => 0), 0, rfl, ?_⟩
  have e1 : ∀ pw : ConLeche.PropWhen,
      denoteMeta (fun _ _ => AnnotTerm.prf) (⟨[]⟩ : Env) (fun _ => 0) 0
          (Expr.lam (.sort .zero) (.sort .zero) ⟨pw⟩)
        = some (.lam (pwBit (fun _ => 0) pw) (.sort 0) (.sort 0)) := by
    intro pw
    rw [denoteMeta]
    simp [denoteMeta_sort, Expr.instantiate1, Level.eval]
  rw [e1, e1, pwBit_never, pwBit_ifAllZero_nil]
  simp

/-! ## The `instPisAtLift` reading battery

`blockIhCall?`, `blockIhPis` and `checkBlockRule`'s conclusion are
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

/-! ## The guarded-call case of the abstraction's inverse

`interp ⟦stored rhs body⟧ = interp (instsAV 0 ihs Rb'')` has one case
that is not structural: the node the abstraction REPLACES, where the
stored node and the generated spine must read alike.  With the exact
comparison above that is `congrArg`: `IhCallRun.heq` exports
`e = expected` as TERMS. -/

/-! ## The stored types READ, and their readings are GRADED

`blockRecStaged_of`'s `hrd` has three components: the recursor's
stored type reads, its reading is graded, and the leaf inhabits it.
The first two are **run facts** — `checkConstantVal` ran `inferType`
on the ANNOTATED type at the constructors' environment, which is
exactly the hypothesis `acceptedReads_of` and the infer claim want —
and this is them.  The third is the recursion theorem and belongs to
the regimes.

The recipe is the one every harvest uses (`harvestDefn`,
`Model/Harvest.lean`): `annotate_syntax` for the primed form's
scoping, `acceptedReads_of` for the reading, and `checkSoundAt`'s
infer claim (through `inferReads_of` for the inferred type's own
reading) for the grading. -/

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **A checked constant's type reads, the reading is graded, AND it
lands in the universe the check's own `ensureSort` named.**

The sort component is one step further into the pair the grading
already runs: `checkConstantVal` infers the annotated type and
`ensureSort`s the result, and `ensureSortCore_inv` turns that into the
`whnf`-to-a-sort `SortSemAt` asks for — so the same claims
(`WhnfClaim` + `InferClaim` + `InferReads`) that grade the reading
also place it in `univ (u.eval ψ)`.

**This is the `hlvl` route**: the level a recursor's type lives at is
the check's INFERRED one, and it already accounts for the binders'
levels, so nothing has to pin the reading's binder numerals. -/
theorem checkConstantVal_reads {env : Env} (hμ : μ.verifiedChecks = true)
    (mp : EnvModelM V μ env) {F : Nat} {cv cvA : ConstantVal}
    (h : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cv = .ok cvA) :
    ∃ u : Level, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, interp V ρ ta ∈ˢ (univ (u.eval ψ) : V) := by
  obtain ⟨-, -, -, -, hlbt, hitf, type, stype, u, hann, -, -, hrun, hsort, rfl⟩ :=
    ConLeche.checkConstantVal_inv h
  refine ⟨u, fun ψ => ?_⟩
  obtain ⟨htf', hbt'⟩ := ConLeche.Semantics.annotate_syntax hann hitf hlbt
  have hwt : Expr.WScoped 0 type := Expr.WScoped.of_not_hasFvar htf'
  have hnlt : type.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar htf'
  have hLt : Expr.LeavesBounded type := fun l hl => by
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
`checkConstantVal` runs, at the type record of each stored recursor
(`RecKRun.tyAt`, `Verify/Inductives/BlockRecRun.lean`). -/
theorem checkBlockRecK_tyReads {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs, ∃ u : Level, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, interp V ρ ta ∈ˢ (univ (u.eval ψ) : V) := by
  obtain ⟨R⟩ := ConLeche.checkBlockRecK_run h
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  obtain ⟨rc, u, -, -, ⟨E⟩⟩ := R.tyAt hi
  exact checkConstantVal_reads hμ mpC E.hcv

/-- **`blockRecStaged_of`'s `hrd`, reduced to the MEMBERSHIP.**  The
reading and its grading are the run's (`checkBlockRecK_tyReads`); what
is left is that the leaf inhabits the reading — the recursion theorem,
which the regimes deliver as `hmem` in this shape. -/
theorem hrd_of_mem {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    {acv : Name → (Name → Nat) → AnnotTerm}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs)
    (hmem : ∀ r ∈ rs, ∀ (ψ : Name → Nat) (ta : AnnotTerm),
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta →
      ∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta) :
    ∀ r ∈ rs, ∀ ψ : Name → Nat, ∃ ta : AnnotTerm,
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      (∀ ρ : Nat → V, interp V ρ (acv r.1.name ψ) ∈ˢ interp V ρ ta) := by
  intro r hr ψ
  obtain ⟨_, hru⟩ := checkBlockRecK_tyReads (V := V) hμ mpC h r hr
  obtain ⟨ta, hta, hok, -⟩ := hru ψ
  exact ⟨ta, hta, hok, hmem r hr ψ ta hta⟩

end ConLeche.Model
