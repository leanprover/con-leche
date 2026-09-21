module

import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Level
import ConLeche.Model.Annot.Bit
public import ConLeche.Model.Annot.BitLemmas
import ConLeche.Verify.Shift
import ConLeche.Model.BasisEmpty
public import ConLeche.Model.Annot.Laws
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Verify.Inductives.BlockRecInv

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

/-! ## FINDING — `denoteMeta` does not respect `Expr.resetMeta`

`blockIhCall?` (`Kernel/Inductives/BlockRec.lean`) recognises a guarded
recursive call by comparing the node with the generated spine **at the
parse placeholder's binder data**: `Expr.resetMeta e == Expr.resetMeta
expected`.  `blockIhCall?_spine` exports exactly that equality, and it
is the ONLY tie between the stored right-hand side's call node and the
spine the ι law is stated at.

It does not transport a READING.  `resetMeta` forces every binder's
datum to `⟨.never⟩`, whose bit is `1`, while a datum that holds at `φ`
reads `0`; and `interp` is not bit-blind — `lamR`/`piR` take the bit.
So two `resetMeta`-equal expressions can denote differently, and this
is that fact, witnessed:

the difference is confined to binder data occurring INSIDE the call's
arguments that come from the GENERATED side — the field's index
expressions (`BlockRuleFrame.idxOf`, off the constructor's stored
annotated type) — since the telescope's own `⟨pw⟩` binders are consumed
by `instPisAtLift` and the spine's other arguments are the node's own.
Both sides are outputs of `annotateCore`, so on a well-formed stream
they agree; what is missing is a lemma saying so (the annotation's
binder data is a function of the erased term and the environment), or a
strengthening of the comparison.  See the lane report. -/
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

/-! ## O-1's seam: the guarded call's READING claim

O-1 — `interp ⟦stored rhs body⟧ = interp (instsAV 0 ihs Rb'')`, the
abstraction's inverse at the denotation — has one case that is not
structural: the node the abstraction REPLACES.  There the model must
know that the stored node and the generated spine read alike, and the
check's own comparison (`Expr.resetMeta`) does not give it
(`not_denoteMeta_resetMeta_invariant` above).

`IhCallReads` is that fact, named, in the form O-1 consumes it and
lane K2's strengthened comparison will produce it: **every node
`blockIhCall?` accepts reads exactly as the generated spine does**.
`ihCallReads_of_eq` is the one-line bridge from a SYNTACTIC equality of
the two, which is what an exact comparison exports — so K2's landing
closes this premise by one `exact`. -/

/-- **Every node the abstraction replaces reads as the generated
spine.**  The premise O-1's guarded-call case needs. -/
@[expose] def IhCallReads (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
    (φ : Name → Nat) (fr : ConLeche.BlockRuleFrame) : Prop :=
  ∀ (d : Nat) (e : Expr) (r : Nat) (as : List Expr),
    ConLeche.blockIhCall? fr d e = some (r, as) →
    ∀ (nm : Name) (i : Nat) (expected : Expr),
      e.getAppFn = .const nm fr.rlvls →
      Expr.instPisAtLift as
          (ConLeche.blockIhSpinePis nm fr.rlvls fr.pw fr.nP fr.rP fr.nF i d
            (fr.teleOf i) (fr.idxOf i)) = some expected →
      ∀ D : Nat, denoteMeta acval env φ D e = denoteMeta acval env φ D expected

/-- **The bridge from an exact comparison.**  `blockIhCall?` compares
the node with the generated spine; once that comparison is the
annotated one (lane K2), `blockIhCall?_spine` exports `e = expected`
and the reading claim is `congrArg`. -/
theorem ihCallReads_of_eq {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {fr : ConLeche.BlockRuleFrame}
    (h : ∀ (d : Nat) (e : Expr) (r : Nat) (as : List Expr),
      ConLeche.blockIhCall? fr d e = some (r, as) →
      ∀ (nm : Name) (i : Nat) (expected : Expr),
        e.getAppFn = .const nm fr.rlvls →
        Expr.instPisAtLift as
            (ConLeche.blockIhSpinePis nm fr.rlvls fr.pw fr.nP fr.rP fr.nF i d
              (fr.teleOf i) (fr.idxOf i)) = some expected →
        e = expected) :
    IhCallReads acval env φ fr :=
  fun d e r as hcall nm i expected hfn hexp D =>
    congrArg (denoteMeta acval env φ D) (h d e r as hcall nm i expected hfn hexp)

end ConLeche.Model
