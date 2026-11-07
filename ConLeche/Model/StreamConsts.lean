module

import ConLeche.Verify.Abstract
import ConLeche.Verify.Subst
public import ConLeche.Cached.Decls
public import ConLeche.Model.Fold
public import ConLeche.Verify.Cached.BridgeC
import ConLeche.Verify.EnvBound
import ConLeche.Model.DeclsRun
import ConLeche.Verify.Cached.PushChain

public section

/-!
# What `checkDecls` stores of what it reads

The letters of the fold are about the environment `checkDecls` RETURNS.
This module carries the other direction, for every record kind that
declares a constant: **the record's own name is in that environment,
with the record's own level parameters and the record's own type** —
`checkDecls_consts`.  The checker stores a declaration as declared
(`checkConstantVal` is a guard, `let`s included: it transforms
nothing), so the relation between the declared type and the stored one
is equality.

## Which records are covered, and which are not

`Declaration.Declares` says which constant a record declares.  Definitions,
theorems and opaques declare their header; an axiom declares its header
unless it is the `sorryAx` axiom record, which is checked for
well-formedness and then installs NOTHING (there is no set model for
it), so nothing is stored — and any USE of the name declines.

**An `indDecl` block's members are outside the claim, and the reason is
not laziness.**  Two of the block's constants may be stored as something
other than what the record declares:

* the **recursor**'s stored type is GENERATED; the stream's own record
  is compared against it by `isDefEq` and then discarded, exactly as
  official's replay does;
* the **type former**'s stored type is the *whnf'd* telescope whenever
  the declared type is not already a syntactic Π-telescope ending in a
  sort (`checkSumTele`, `ConLeche/Kernel/Inductives/SumInstall.lean`).

Both are definitional equalities, not syntactic ones, so the claim would be
false of them; a **constructor** is stored as declared, but it is
stored with its block and is left out with it.

## How it is proved

The walk has `declsRun_model`'s hypotheses and threads the model
beside the conclusion; `checkDeclStepC_model`
(`ConLeche/Model/DeclsRun.lean`) is the per-step lemma both walks
share, and its extra conjunct — the step IS a pure `checkDecl` run — is
what lets the per-record reasoning happen entirely at the pure checker's
own run relation (`Semantics.DeclRun`).

`ConLeche/Verify/Cached/StreamThm.lean` proves the bare-constant special
case a second and cheaper way, with no model and no `V`.  That is why
the main corollary at the stream (`no_False_theorem_accepted`) does not
go through this module.
-/
namespace ConLeche

namespace Cached

open ConLeche ConLeche.Semantics ConLeche.Model

variable {pins : List NatOpPinSet}

/-- **What a record of the fold's input declares.**  `checkDecls`'s
input is a list of parsed records, and this says which constant each
kind of record claims a name and a type for:

* a definition, a theorem and an opaque declare their header;
* an axiom declares its header **unless it is the `sorryAx` axiom
  record**, which installs nothing: it is checked for well-formedness
  and then dropped (there is no set model for it), and any later record
  that USES the name declines — **or the `Quot.sound` axiom record**
  (task #293), which is the pinned quotient block's own: it is compared
  with the pin and stores it at its names, as the quotient record
  that declares the type;
* a `quotDecl` declares nothing of its own, for the same reason: what it
  stores is its slot's pin at its names;
* an `indDecl` block's members are NOT covered here.  See the module
  docstring: the recursor's stored type is the generated one, and the
  installer may store a *whnf'd* type former telescope rather than the
  declared one. -/
@[expose] def Declaration.Declares : Declaration → ConstantVal → Prop
  | .defnDecl cv _ _, cv' => cv' = cv
  | .thmDecl cv _, cv' => cv' = cv
  | .opaqueDecl cv _, cv' => cv' = cv
  | .axiomDecl cv, cv' => cv' = cv ∧ cv.name ≠ sorryAxName ∧ cv.name ≠ quotSoundName
  | .indDecl _ _, _ => False
  | .quotDecl _ _, _ => False

/-! ## A name-unique environment finds what it holds -/

theorem find?_name_of_mem : ∀ {cs : List ConstantInfo}, (cs.map (·.name)).Nodup →
    ∀ {c : ConstantInfo}, c ∈ cs → cs.find? (·.name == c.name) = some c := by
  intro cs
  induction cs with
  | nil => intro _ c hc; exact absurd hc List.not_mem_nil
  | cons a t ih =>
    intro hnd c hc
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    by_cases hb : (a.name == c.name) = true
    · simp only [hb]
      rcases List.mem_cons.mp hc with rfl | hc'
      · rfl
      · exact absurd (by rw [eq_of_beq hb]; exact List.mem_map.mpr ⟨c, hc', rfl⟩) hnd.1
    · rw [Bool.not_eq_true] at hb
      simp only [hb]
      rcases List.mem_cons.mp hc with rfl | hc'
      · simp at hb
      · exact ih hnd.2 hc'

/-- A name-unique environment finds every constant it holds. -/
theorem find?_of_mem_nodup {env : Env} (hnd : NodupNames env) {c : ConstantInfo}
    (hc : c ∈ env.consts) : env.find? c.name = some c :=
  find?_name_of_mem hnd hc

/-! ## One declaration's install, at the pure checker -/

/-- **What one accepted declaration stores of what it declares.**  Every
record kind that declares a constant stores it under its own name, with
its own level parameters and its declared type. -/
theorem checkDecl_declares {env env₂ : Env} {F : Nat}
    {pd : Declaration}
    (h : checkDecl .verified (fueledOps .verified F) pins env pd = .ok env₂)
    {cv : ConstantVal} (hcv : Declaration.Declares pd cv) :
    ∃ c ∈ env₂.consts, c.name = cv.name ∧
      c.toConstantVal.levelParams = cv.levelParams ∧
      c.toConstantVal.type = cv.type := by
  have hrun := ConLeche.Semantics.checkDeclRun_ofEnvFactsK h
  cases pd with
  | defnDecl cv₀ value hint =>
    obtain rfl : cv = cv₀ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclDefnRun] at hrun
    obtain ⟨type', value', hcvr, -, henv₂, -, -⟩ := hrun
    obtain ⟨-, -, -, -, -, hann, -, -, -⟩ := hcvr
    refine ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact hann
  | thmDecl cv₀ value =>
    obtain rfl : cv = cv₀ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclThmRun] at hrun
    obtain ⟨-, type', value', hcvr, -, -, henv₂⟩ := hrun
    obtain ⟨-, -, -, -, -, hann, -, -, -⟩ := hcvr
    refine ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact hann
  | opaqueDecl cv₀ value =>
    obtain rfl : cv = cv₀ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclOpaqueRun] at hrun
    obtain ⟨-, type', value', hcvr, -, henv₂, -⟩ := hrun
    obtain ⟨-, -, -, -, -, hann, -, -, -⟩ := hcvr
    refine ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact hann
  | axiomDecl cv₀ =>
    obtain ⟨rfl, htol, hqs⟩ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclAxiomRun] at hrun
    -- the `Quot.sound` arm (task #293) is excluded by `Declares`
    rcases hrun with ⟨hq, -⟩ | hrun
    · exact absurd hq hqs
    obtain ⟨-, type', -, hcvr, hdisj⟩ := hrun
    obtain ⟨-, -, -, -, -, hann, -, -, -⟩ := hcvr
    have henv₂ : env₂ = ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ := by
      rcases hdisj with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
        ⟨-, -, -, -, -, -, htol', -⟩
      · exact he
      · exact he
      · exact he
      · exact absurd htol' htol
    refine ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact hann
  | quotDecl k cv₀ => exact hcv.elim
  | indDecl block nP => exact hcv.elim

/-! ## The walk -/

universe w

variable {V : Type w} [SetTheory V]

/-- **The walk**: along an accepting run whose start environment
carries the model, every record's declared constant is stored — with its
name, its level parameters and its type — and is still there at the
end.  The hypotheses are `declsRun_model`'s. -/
theorem declsRun_declares {ds : List Declaration} {p q : Nat × FEnv}
    (hrun : DeclsRun .verified pins ds p q) :
    p.2 = mkFEnv p.2.env → EnvModelOk V p.2.env →
    ∀ pd ∈ ds, ∀ cv : ConstantVal, Declaration.Declares pd cv →
      ∃ c ∈ q.2.env.consts, c.name = cv.name ∧
        c.toConstantVal.levelParams = cv.levelParams ∧
        c.toConstantVal.type = cv.type := by
  induction hrun with
  | nil p => exact fun _ _ pd hmem => absurd hmem List.not_mem_nil
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hfe hm pd' hmem cv hcv
    obtain ⟨fe₁, s₁, rfl, hstepC⟩ := declStep_ok hstep
    obtain ⟨hm₁, hfe₁, -, F, hF⟩ := checkDeclStepC_model hfe hm CSOKF.empty hstepC
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · obtain ⟨c, hc, h1, h2, h3⟩ := checkDecl_declares hF hcv
      obtain ⟨new, hnew, -⟩ := (declsRun_chain .verified rest (PushChain.self hfe₁)).2.1
      exact ⟨c, by rw [hnew]; exact List.mem_append_right _ hc, h1, h2, h3⟩
    · exact ih hfe₁ hm₁ pd' hmem' cv hcv

/-! ## The theorem -/

/-- **What `checkDecls` stores of what it reads.**  Every record of the
fold's input that declares a constant — a definition, a theorem, an
opaque, or an axiom whose name is not tolerated — leaves in the returned
environment a constant of that very name, with the record's own level
parameters and the record's own type.  An `indDecl`
block's members are outside the claim (see the module docstring). -/
theorem checkDecls_consts (V : Type w) [SetTheory V]
    {ds : Array Declaration} {env : Env} (accepted : checkDecls .verified pins ds = .ok env)
    {pd : Declaration} (hmem : pd ∈ ds) {cv : ConstantVal} (hcv : Declaration.Declares pd cv) :
    ∃ c, env.find? cv.name = some c ∧
      c.toConstantVal.levelParams = cv.levelParams ∧
      c.toConstantVal.type = cv.type := by
  obtain ⟨n, fe, run, rfl⟩ := checkDecls_run _ accepted
  have hnd : NodupNames fe.env :=
    (declsRun_chain _ run (PushChain.refl Env.empty)).2.2.1 List.nodup_nil
  obtain ⟨c, hc, h1, h2, h3⟩ :=
    declsRun_declares (V := V) run rfl EnvModelOk.empty pd (Array.mem_toList_iff.mpr hmem) cv hcv
  exact ⟨c, h1 ▸ find?_of_mem_nodup hnd hc, h2, h3⟩

end Cached

end ConLeche
