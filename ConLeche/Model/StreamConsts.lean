module

import ConLeche.Verify.Abstract
import ConLeche.Verify.Subst
public import ConLeche.Cached.Installed
public import ConLeche.Model.Fold
public import ConLeche.Verify.Cached.BridgeC
import ConLeche.Verify.EnvBound
import ConLeche.Model.InstallRun

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
it), so nothing is stored — and any USE of the name declines.  A
`basisDecl` names one of the checker's pinned basis blocks and declares
nothing of its own.

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
installed with its block and is left out with it.

## How it is proved

The walk has `installRun_model`'s hypotheses and threads the model
beside the conclusion; `installStepC_model`
(`ConLeche/Model/InstallRun.lean`) is the per-step lemma both walks
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
  with the pin and the BLOCK installs the axiom, at the quotient record
  that declares the type;
* a `quotDecl` declares nothing of its own, for the same reason: the
  pinned quotient block installs all five constants at once;
* a `basisDecl` declares nothing of its own — it names one of the
  checker's pinned basis blocks, and the constants installed are the
  pins';
* an `indDecl` block's members are NOT covered here.  See the module
  docstring: the recursor's stored type is the generated one, and the
  installer may store a *whnf'd* type former telescope rather than the
  declared one. -/
@[expose] def Declaration.Declares : Declaration → ConstantVal → Prop
  | .defnDecl cv _ _, cv' => cv' = cv
  | .thmDecl cv _, cv' => cv' = cv
  | .opaqueDecl cv _, cv' => cv' = cv
  | .axiomDecl cv, cv' => cv' = cv ∧ cv.name ≠ sorryAxName ∧ cv.name ≠ quotSoundName ∧
      -- Task #368: a native `bv_decide` axiom is
      -- stored as a `True` stub, not with its declared type
      ConLeche.isBVNativeAxName cv.name = false
  | .basisDecl _, _ => False
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
theorem checkDecl_declares {μ : CheckMode} {env env₂ : Env} {F : Nat}
    {pd : Declaration}
    (h : checkDecl μ (fueledOps μ F) pins env pd = .ok env₂)
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
    obtain ⟨type', value', hcvr, -, -, henv₂⟩ := hrun
    obtain ⟨-, -, -, -, -, hann, -, -, -⟩ := hcvr
    refine ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact hann
  | opaqueDecl cv₀ value =>
    obtain rfl : cv = cv₀ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclOpaqueRun] at hrun
    obtain ⟨type', value', hcvr, -, henv₂, -⟩ := hrun
    obtain ⟨-, -, -, -, -, hann, -, -, -⟩ := hcvr
    refine ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact hann
  | axiomDecl cv₀ =>
    obtain ⟨rfl, htol, hqs, hbvn⟩ := hcv
    simp only [ConLeche.Semantics.DeclRun, ConLeche.Semantics.DeclAxiomRun] at hrun
    -- the `Quot.sound` arm (task #293) is excluded by `Declares`
    rcases hrun with ⟨hq, -⟩ | hrun
    · exact absurd hq hqs
    obtain ⟨type', hcvr, hdisj⟩ := hrun
    obtain ⟨-, -, -, -, -, hann, -, -, -⟩ := hcvr
    have henv₂ : env₂ = ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩ :: env.consts, env.tables⟩ := by
      rcases hdisj with ⟨-, he⟩ | ⟨-, -, he⟩ | ⟨-, -, he⟩ |
        ⟨-, -, -, -, -, -, htol', -⟩ | ⟨hbv, -, -⟩
      · exact he
      · exact he
      · exact he
      · exact absurd htol' htol
      · simp only [ConLeche.bvStubOk, Bool.and_eq_true] at hbv
        exact absurd hbv.2 (by simp [hbvn])
    refine ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, ?_, rfl, rfl, ?_⟩
    · rw [henv₂]; exact List.mem_cons_self
    · exact hann
  | basisDecl kind => exact hcv.elim
  | quotDecl k cv₀ => exact hcv.elim
  | indDecl block nP => exact hcv.elim

/-! ## The walk -/

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **The walk**: along an accepting phase-A run whose start environment
carries the model, every record's declared constant is stored — with its
name, its level parameters and its type — and is still there at the
end.  The hypotheses are `installRun_model`'s. -/
theorem installRun_declares (hμ : μ.isVerified = true) {ds : List Declaration}
    {p : Nat × FEnv × Array PendingCheck}
    {q : Nat × FEnv × Array PendingCheck}
    (hrun : InstallRun μ pins ds p q) :
    p.2.1 = mkFEnv p.2.1.env → EnvModelOk V μ p.2.1.env →
    NodupNames q.2.1.env →
    (∀ pc ∈ q.2.2.toList, ∃ s'', checkPending μ q.2.1 pc {} = .ok ((), s'')) →
    ∀ pd ∈ ds, ∀ cv : ConstantVal, Declaration.Declares pd cv →
      ∃ c ∈ q.2.1.env.consts, c.name = cv.name ∧
        c.toConstantVal.levelParams = cv.levelParams ∧
        c.toConstantVal.type = cv.type := by
  induction hrun with
  | nil p => exact fun _ _ _ _ pd hmem => absurd hmem List.not_mem_nil
  | @cons pd ds p p₁ q hstep rest ih =>
    intro hfe hm hnd hB pd' hmem cv hcv
    obtain ⟨i, fe, pend⟩ := p
    obtain ⟨fe₁, pend₁, s₁, rfl, hstepC⟩ := installDeclStep_ok hstep
    simp only at hfe hstepC
    obtain ⟨hpush₁, -⟩ :=
      installStepC_push μ i (PushChain.self hfe) pend pd {} (fe₁, pend₁) s₁ hstepC
    have hfe₁ : fe₁ = mkFEnv fe₁.env := hpush₁.canon
    obtain ⟨hchainF, new₁, hpend₁⟩ := installRun_trace μ rest (PushChain.self hfe₁)
    obtain ⟨hm₁, -, F, hF⟩ :=
      installStepC_model (V := V) hμ hfe hfe₁ hm CSOKF.empty hstepC hchainF hpend₁ hnd hB
    rcases List.mem_cons.mp hmem with rfl | hmem'
    · obtain ⟨c, hc, h1, h2, h3⟩ := checkDecl_declares hF hcv
      obtain ⟨new, hnew⟩ := hchainF.2.1
      exact ⟨c, by rw [hnew]; exact List.mem_append_right _ hc, h1, h2, h3⟩
    · exact ih hfe₁ hm₁ hnd hB pd' hmem' cv hcv

/-! ## The theorem -/

/-- **What `checkDecls` stores of what it reads.**  Every record of the
fold's input that declares a constant — a definition, a theorem, an
opaque, or an axiom whose name is not tolerated — leaves in the returned
environment a constant of that very name, with the record's own level
parameters and the record's own type.  `basisDecl` records declare nothing, and an `indDecl`
block's members are outside the claim (see the module docstring). -/
theorem checkDecls_consts (V : Type w) [SetTheory V]
    {ds : Array Declaration} {env : Env} (accepted : checkDecls .verified pins ds = .ok env)
    {pd : Declaration} (hmem : pd ∈ ds) {cv : ConstantVal} (hcv : Declaration.Declares pd cv) :
    ∃ c, env.find? cv.name = some c ∧
      c.toConstantVal.levelParams = cv.levelParams ∧
      c.toConstantVal.type = cv.type := by
  obtain ⟨fc, rfl⟩ := checkDecls_fullyChecked _ accepted
  obtain ⟨n, run⟩ := fc.1.run
  have hchain := installRun_trace _ run (PushChain.refl Env.empty)
  have hnd : NodupNames fc.1.fe.env := hchain.1.2.2.1 List.nodup_nil
  obtain ⟨c, hc, h1, h2, h3⟩ :=
    installRun_declares (V := V) rfl run rfl
      EnvModelOk.empty
      hnd fc.records pd (Array.mem_toList_iff.mpr hmem) cv hcv
  exact ⟨c, h1 ▸ find?_of_mem_nodup hnd hc, h2, h3⟩

end Cached

end ConLeche
