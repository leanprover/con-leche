module

import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Level
import ConLeche.Model.Annot.Bit
public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.Shift
import ConLeche.Model.BasisEmpty
import ConLeche.Model.Annot.Laws
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Verify.Inductives.BlockRecInv
public import ConLeche.Model.Annot.EnvModelM
import ConLeche.Model.Capstone
import ConLeche.Verify.Inductives.BlockWF

public section

/-!
# The recursor stage's READINGS (task #315, milestone M5, the Model half)

What `blockRecStaged_of`'s two open premises
(`Model/Inductives/BlockStageRec.lean`) are made of: the recursors'
stored types read to a Π-tower whose binder data is the semantics
tier's `rds`, the rule's prefix binders read to the SAME data (G2), and
the stored right-hand side's body reads to the residue at the `ih`
openers' values (O-1).

**D-d first**, because it is one line and the whole family's level
arithmetic rests on it: `checkBlockRecElimAgree` compares the sorts the
kernel's own sort check gave the recursors' CONCLUSIONS, and
`blockRecElimAgree_inv` (`Verify/Inductives/BlockRecInv.lean`) exposes
that comparison as `Level.isEquiv`.  The model does not consume
`isEquiv`; it consumes `Level.eval` at a ground assignment, which is
what `Level.isEquiv_sound` turns it into.  With that, a family has ONE
elimination level — `M5m`'s `OneElimLevel` at the family's single `ℓ`.
-/

namespace ConLeche.Model
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Semantics SetTheory
open ConLeche (Env Expr Name Level ConstantVal ConstantInfo)

/-! ## D-d, at the valuation -/

/-- **One elimination level per family, at a ground assignment.**
`blockRecElimAgree_inv` gives the check's own verdict
(`Level.isEquiv`); this is the form the model reads — every recursor's
conclusion sort EVALUATES to the first one's at every `ψ`, so the
Σ'-chain has one level and the candidate one tower bit. -/
theorem blockRecElimAgree_eval {us : List Level}
    (h : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (ψ : Name → Nat) : ∀ u ∈ us, u.eval ψ = (us.headD .zero).eval ψ :=
  fun u hu => Level.isEquiv_sound (ConLeche.blockRecElimAgree_inv h u hu) ψ

/-- The same, between any two of the family's conclusions. -/
theorem blockRecElimAgree_eval_pair {us : List Level}
    (h : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (ψ : Name → Nat) {u v : Level} (hu : u ∈ us) (hv : v ∈ us) :
    u.eval ψ = v.eval ψ :=
  (blockRecElimAgree_eval h ψ u hu).trans (blockRecElimAgree_eval h ψ v hv).symm

/-- **The zeroness bit is the family's**, which is exactly the shape
`OneElimLevel` (`Semantics/Tower/BlockRecKitI.lean`) asks for once the
recursors' conclusions' sorts are the readings' binder numerals: at
the family's single `ℓ := (us.headD .zero).eval ψ`, a conclusion sort
is zero iff `ℓ` is. -/
theorem blockRecElimAgree_zero_iff {us : List Level}
    (h : ConLeche.checkBlockRecElimAgree (m := ConLeche.CheckM) us = .ok ())
    (ψ : Name → Nat) {u : Level} (hu : u ∈ us) :
    ((us.headD .zero).eval ψ = 0 ↔ u.eval ψ = 0) := by
  rw [blockRecElimAgree_eval h ψ u hu]

/-! ## The finding, and its RESOLUTION in the kernel

`denoteMeta` does not respect `Expr.resetMeta`: `resetMeta` forces
every binder's datum to `⟨.never⟩`, whose bit is `1`, while a datum
that holds at `φ` reads `0`, and `interp` is not bit-blind —
`lamR`/`piR` take the bit.  So two `resetMeta`-equal expressions can
denote differently, which `not_denoteMeta_resetMeta_invariant` below
witnesses.

`blockIhCall?` (`Kernel/Inductives/BlockRec.lean`) used to recognise a
guarded recursive call up to exactly that relation, and its
comparison is the ONLY tie between the stored right-hand side's call
node and the spine the ι law is stated at — so a reading could not be
transported across it.  **The kernel comparison was strengthened**
(lane K2): the node and the generated spine are now compared EXACTLY,
binder data included (`e != expected`), and `blockIhCall?_spine`
(`Verify/Inductives/BlockRecInv.lean`) exports `e = expected` — so
the field's ANNOTATED index expressions in the call node are the
constructor's stored ones, syntactically.  The whole arena battery and
the whole e2e suite are unchanged by the strengthening (measured at
the k = 1 probe, with a negative control showing the comparison is
what those fixtures' rules pass).

The witness stays as the record of WHY the comparison is exact. -/
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

/-! ## The two missing `denoteMeta` batteries (O-1's prerequisites)

`blockIhCall?`, `blockIhPis` and `checkBlockRule`'s conclusion are
built with `Expr.instPisAtLift`, and the ih telescope is opened with
`Expr.instantiateList`; neither had a reading lemma, because both are
written for arguments that may mention the ambient binders and
`denoteMeta_beta` wants a bvar-CLOSED replacement.

The way through is not a generalised `denoteMeta_beta` but the
observation that at the frame `denoteMeta` actually reads — the rule
body OPENED at fvars — the arguments ARE bvar-closed, and there both
operations collapse onto ones the model owns
(`instPisAtLift_eq_instPisAt`, `instantiateList_eq_instSeq`,
`Verify/Inductives/BlockRecInv.lean`).  So the batteries are
corollaries, not new inductions. -/

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

/-- **The reading of an `instantiateList` opening**, at bvar-closed
values: `denoteMeta_openRev` through `instantiateList_eq_instSeq`. -/
theorem denoteMeta_instantiateList
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ)
    (hainst : ∀ (n : Name) (ψ : Name → Nat) (y : AnnotTerm) (k : Nat),
      (acval n ψ).inst y k = acval n ψ)
    {vs : List Expr} (hne : vs ≠ []) {e : Expr} {d : Nat}
    (hv : ∀ a ∈ vs, Expr.WScoped d a ∧ a.looseBVarsBounded 0 = true)
    (hfb : Expr.fvarsBelow d e) (hb : e.looseBVarsBounded vs.length = true)
    {xs : List AnnotTerm} (hsp : DenoteMetaSpine acval env φ d vs.reverse xs) :
    denoteMeta acval env φ d (e.instantiateList vs 0)
      = (denoteMeta acval env φ (d + vs.length)
          (ConLeche.Verify.openRev d vs.length e)).map (ConLeche.Model.AnnotTerm.instRevChain xs) := by
  have hlen : vs.reverse.length = vs.length := List.length_reverse
  rw [ConLeche.instantiateList_eq_instSeq hne e]
  have := ConLeche.Model.Rules.denoteMeta_openRev (acval := acval) (env := env) (φ := φ) hacl hainst
    vs.reverse (e := e) (d := d)
    (fun a hmem => hv a (List.mem_reverse.mp hmem)) hfb (by rw [hlen]; exact hb) hsp
  rw [hlen] at this
  exact this

/-! ## O-1's guarded-call case, discharged

O-1 — `interp ⟦stored rhs body⟧ = interp (instsAV 0 ihs Rb'')`, the
abstraction's inverse at the denotation — has one case that is not
structural: the node the abstraction REPLACES.  There the model must
know that the stored node and the generated spine read alike.

With lane K2's comparison that is **free**: `blockIhCall?_spine`
exports `e = expected` as TERMS, binder data included, so the reading
claim is `congrArg`.  (Before K2 it was a premise; the witness above
records why it could not be one.) -/

/-- **Every node the abstraction replaces reads as the generated
spine.**  O-1's guarded-call case, with no premise left. -/
theorem denoteMeta_blockIhCall {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {fr : ConLeche.BlockRuleFrame} {d : Nat} {e : Expr} {r : Nat}
    {as : List Expr} (h : ConLeche.blockIhCall? fr d e = some (r, as)) :
    ∃ (nm : Name) (c' i : Nat) (expected : Expr),
      e.getAppFn = .const nm fr.rlvls ∧
      ConLeche.nameIdxOf? fr.recNames nm = some c' ∧
      ConLeche.pairIdxOf? fr.ihKeys (i, c') = some r ∧
      as.length = (fr.teleOf i).length ∧
      Expr.instPisAtLift as
          (ConLeche.blockIhSpinePis nm fr.rlvls fr.pw fr.nP fr.rP fr.nF i d
            (fr.teleOf i) (fr.idxOf i)) = some expected ∧
      ∀ D : Nat, denoteMeta acval env φ D e = denoteMeta acval env φ D expected := by
  obtain ⟨nm, c', i, expected, h1, h2, h3, -, -, -, h7, -, h9, h10⟩ :=
    ConLeche.blockIhCall?_spine h
  exact ⟨nm, c', i, expected, h1, h2, h3, h7, h9, fun D => congrArg _ h10⟩

/-! ## O-2, part 1 — the stored types READ, and their readings are GRADED

`blockRecStaged_of`'s `hrd` has three components: the recursor's
stored type reads, its reading is graded, and the leaf inhabits it.
The first two are **run facts** — `checkConstantVal` ran `inferType`
on the ANNOTATED type at the constructors' environment, which is
exactly the hypothesis `acceptedReads_of` and the infer claim want —
and this is them.  The third is the recursion theorem and belongs to
the regimes (lane RM3).

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
    (h : ConLeche.checkConstantVal (ConLeche.fueledOps μ F) env cv = .ok cvA)
    (ψ : Name → Nat) :
    ∃ (ta : AnnotTerm) (u : Level),
      denoteMeta mp.base2.acval env ψ 0 cvA.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, interp V ρ ta ∈ˢ (univ (u.eval ψ) : V) := by
  obtain ⟨-, -, -, -, hlbt, hitf, type, stype, u, hann, -, -, hrun, hsort, rfl⟩ :=
    ConLeche.checkConstantVal_inv h
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
  exact ⟨ta, u, hta, fun ρ => (hsem ρ (ConLeche.Semantics.Sat_nil V ρ)).1,
    fun ρ => (hsem ρ (ConLeche.Semantics.Sat_nil V ρ)).2⟩

/-- **`hrd`'s first two components, at the whole recursor stage.**
Every stored recursor's type reads at the constructors' environment
and its reading is graded — from the stage's own
`checkConstantVal` runs.  The identification of the stage's tuple with
the type stage's checked constant is
`checkBlockRecK_reserved`'s (`Verify/Inductives/BlockWF.lean`). -/
theorem checkBlockRecK_tyReads {envC : Env} (hμ : μ.verifiedChecks = true)
    (mpC : EnvModelM V μ envC) {p : ConLeche.BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) envC p cvTas ctorsAs = .ok rs) :
    ∀ r ∈ rs, ∀ ψ : Name → Nat, ∃ (ta : AnnotTerm) (u : Level),
      denoteMeta mpC.base2.acval envC ψ 0 r.1.type = some ta ∧
      (∀ ρ : Nat → V, WellDenotedV V ρ ta) ∧
      ∀ ρ : Nat → V, interp V ρ ta ∈ˢ (univ (u.eval ψ) : V) := by
  unfold ConLeche.checkBlockRecK at h
  obtain ⟨u, hpins, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨cvRus, htys, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨_, _, h⟩ := ConLeche.exceptBind_ok h
  obtain ⟨hlenT, hallT⟩ := ConLeche.checkBlockRecTys_inv htys
  obtain ⟨hlenR, hallR⟩ := ConLeche.checkBlockRecsRules_facts h
  intro r hr ψ
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  have hil : i < p.recs.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1
    omega
  obtain ⟨rc, r', hrc, hr', hcvRa, -⟩ := hallR i hil
  obtain rfl := Option.some.inj (hi.symm.trans hr')
  obtain ⟨rc'', cvRi, nIdx, u', hrc'', hcu, hcv, -, -⟩ := hallT i hil
  obtain rfl := Option.some.inj (hrc.symm.trans hrc'')
  have hcvRa' : (cvRus.map (fun q => (q.1, q.2.1)))[i]? = some (cvRi, nIdx) := by
    rw [List.getElem?_map, hcu]; rfl
  have hr1 : r.1 = cvRi := by
    have := hcvRa
    rw [Nat.zero_add] at this
    exact congrArg Prod.fst (Option.some.inj (this.symm.trans hcvRa'))
  rw [hr1]
  exact checkConstantVal_reads hμ mpC hcv ψ

/-- **`blockRecStaged_of`'s `hrd`, reduced to the MEMBERSHIP.**  The
reading and its grading are the run's (`checkBlockRecK_tyReads`); what
is left is that the leaf inhabits the reading — the recursion theorem,
which is the regimes' deliverable (lane RM3).  This is the seam
between the two halves: RM3 exports `hmem` in this shape and `hrd`
follows. -/
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
  obtain ⟨ta, -, hta, hok, -⟩ := checkBlockRecK_tyReads hμ mpC h r hr ψ
  exact ⟨ta, hta, hok, hmem r hr ψ ta hta⟩

end ConLeche.Model
