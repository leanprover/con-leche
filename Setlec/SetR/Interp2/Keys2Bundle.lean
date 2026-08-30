import Setlec.SetR.Interp2.Keys2Cond

/-!
# The three install keys, in one hypothesis list — the milestone

Seal 49 ran the composition gate and it came back negative **against
an unconditional reading** and exactly on target against the
conditional one — the reading scope ruling (ii) adopted (seal 39).
Seal 50 recorded the perspective: the two leftovers are the residue
set ruling (ii) already priced, not new obstructions.

**So the milestone is not "the keys close outright".  It is "the keys
close on precisely these named residues", and naming them is the
deliverable.**  This file is that naming.

`Keys2Cond.lean` proves the three keys, but a reader has to
reconstruct the hypothesis list from three theorem signatures spread
over 700 lines, and two of the residues (`InferExists2E`,
`EnvExtendStable`) only appear at the *last* of them.  Here the
complete list sits in one structure, every entry with its provenance
and its discharge date.

## The three keys, and what each costs

* **`ReducePin2`** — `ReducePin2Residues`.  One checker run
  (`isDefEqCore` on the pin certificate), four syntactic facts the
  install establishes, and **two `Denote2Total` residues**: the
  operation's value must annotate (`opAnnot`) and its pinned type
  `∀ n : Elem, Elem` must fit (`opFits`).
* **`MemberBlock2`** — `MemberBlock2Residues`.  The front door's own
  `checkConstantVal` record (`ConstantValR`, a *supplied* relation),
  the environment crossing (`EnvExtendStable`, **leftover 2**), the
  stored type's annotation (`Denote2Total`), and `InferExists2E`
  (**leftover 1**).
* **`DeclStep2`** — `DeclStep2Residues`.  A construction: five fields
  extend by `Install2.lean`, and what is left is the collapse-lane
  witness at the extension, the fresh leaf's four laws,
  `Denote2EnvExtend` (frozen on Θ) and `MemberBlock2` **at the new
  axiom** — which is the install-tier half seal 40 measured and which
  no key at the *prefix* can supply.

## Inhabitation, stated up front rather than at the end

A conditional theorem whose hypotheses cannot be met says nothing, so
each field's docstring says whether anything in this tree inhabits it.
The summary:

* `checkStep : CheckStep2E μ V` — **not inhabited in this tree.**
  Assembled from fifteen residues at `Capstone2E.lean`
  (`checkStep2E_of_quarters`); none of the fifteen is discharged here.
  It is the lane's single named residue by design (seal 46).
* `inferExists : InferExists2E` — **not inhabited outright**, but it
  is *not* free-floating: `exists2E_of_checkStep2D` derives it from
  `CheckStep2D μ V`, and `inferExists2E_of_totalR` derives it from
  `Denote2TotalR`.  Both suppliers are themselves residues.
* `envExtend : EnvExtendStable` — **not inhabited in this tree.**
  Defined at `Annot/SortCoh/Discharge.lean:1291` and consumed at
  `Denote2Extend.lean` and here; no supplier anywhere.  Frozen on Θ.
* `constantVal : ConstantValR` — **inhabited from real runs**
  (`constantValR_of`, `Bridge/Decl.lean:97`), and a conjunct of four
  of `DeclR`'s six kinds.  This is the one semantic-looking premise
  that the checker actually pays for.
* `opFits : ReduceOpFits2` — **inhabited at a non-empty domain**
  (`reduceOpFits2_witness`).
* `opAnnot`, `storedAnnot` — `Denote2Total` at named subjects, parked
  at seal 33.  Inhabited at the probes (`piProbe_denote2_ty`), not in
  general.
* the `DeclStep2Residues` block — `newMember` is inhabited at a probe
  (`memberBlock2_piProbe`); `denote2Extend` is frozen on Θ; the rest
  are the fresh leaf's own laws, which an install supplies.

**Nothing here is `rfl`-provable**: every field is either a checker
run at an arbitrary environment, an `∀ρ` semantic fact, or a lookup.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name ConstantInfo ConstantVal
  reduceElemName reduceCertVar isDefEqCore inferTypeCore)

universe w

/-! ## Block 1 — what `ReducePin2` costs -/

/-- **The `ReducePin2` residues.**  `reducePin2_of_checkStep`'s
premise list, named.  The subject is the pinned reduce operation `c`
whose annotated value is `valA` and whose element type is the stored
constant `ciE`. -/
structure ReducePin2Residues (V : Type w) [SetTheory V]
    (μ : CheckMode) {env : Env} (m : EnvS2U V env) (φ : Name → Nat)
    (fuel F : Nat) (c : Name) (valA : Expr) (ciE : ConstantInfo) where
  /-- The element inductive is stored.  *Provenance*: the pin
  install's own freshness/lookup bookkeeping.  *Discharges*: today,
  at every install that reaches the pin. -/
  elemFound : env.find? (reduceElemName c) = some ciE
  /-- The element inductive is level-monomorphic.  *Provenance*:
  syntactic, read off the stored `ConstantInfo`.  *Discharges*:
  today, by computation at each pinned block. -/
  elemMono : ciE.toConstantVal.levelParams = []
  /-- The operation's annotated value is closed.  *Provenance*: the
  annotate pass.  *Discharges*: today. -/
  opNoFvar : valA.hasFvar = false
  /-- …and bvar-closed.  *Provenance*: the same pass.  *Discharges*:
  today. -/
  opBounded : valA.looseBVarsBounded 0 = true
  /-- **`Denote2Total` at the operation's value.**  *Provenance*:
  seal 33's parked existence residue, at this subject.  *Discharges*:
  at junction closure, with the rest of `Denote2Total`. -/
  opAnnot : denote2 μ m.acval env φ F 1 valA = some (m.acval c φ)
  /-- **`Denote2Total` at the operation's pinned type.**  The
  certificate's left side is an application, and generation six's
  defeq claim wants its `AnnotOk2` — which *is* "the head is a
  function and the argument is in its domain".  *Provenance*:
  `Keys2Cond.lean`'s `ReduceOpFits2`, named there rather than hidden
  in a proof.  *Discharges*: from `mem_type2` at `∀ n : Elem, Elem`
  once that type annotates — i.e. with `Denote2Total`.
  **Inhabited** at `reduceOpFits2_witness`. -/
  opFits : ReduceOpFits2 V m.acval φ c
  /-- The install's own `isDefEq` run on the pin certificate.
  *Provenance*: `checkReducePin`.  *Discharges*: today, at every
  accepted stream that installs the pin. -/
  pinRun : isDefEqCore μ env fuel 1
    (.app valA (reduceCertVar c)) (reduceCertVar c) = .ok true

/-! ## Block 2 — what `MemberBlock2` costs -/

/-- **The `MemberBlock2` residues.**  `memberBlock2_of_constantValR`'s
premise list, named.  The subject is the stored constant `c`, whose
type the front door checked at the *prefix* `env₀`. -/
structure MemberBlock2Residues (V : Type w) [SetTheory V]
    (μ : CheckMode) {env : Env} (m : EnvS2U V env) (φ : Name → Nat)
    (fuel F : Nat) (env₀ : Env) (cval : TConstVal) (cv : ConstantVal)
    (c : ConstantInfo) (ta : AVExpr) where
  /-- **Leftover 1 (seal 49).**  The *inferred type* annotates.
  *Provenance*: a generation-six factorization residue
  (`Dual2E.lean`, seal 32); `Denote2Total`'s conclusion moved from a
  run's subject to its result.  *Discharges*: through the claims —
  `exists2E_of_checkStep2D` from `CheckStep2D`, or
  `inferExists2E_of_totalR` from `Denote2TotalR`.  **Beyond the reach
  of any checker-side exposure**: no run the front door makes says
  the inferred type annotates. -/
  inferExists : InferExists2E μ m φ fuel
  /-- **Leftover 2 (seal 49).**  The composition crosses an
  environment: `ConstantValR` records a run at the prefix `env₀`,
  the key needs it where the constant is already stored.
  *Provenance*: the Θ lane's (E), `Annot/SortCoh/Discharge.lean`.
  *Discharges*: when Θ's sorry-free prefix lands.  Its `ConstsBound`
  side condition is free here — `ConstantValR`'s own `constsResolve`
  conjunct supplies it via `constsBound_of_constsResolve`. -/
  envExtend : EnvExtendStable μ env₀ env
  /-- The front door's own record of `checkConstantVal`.
  *Provenance*: `constantValR_of` (`Bridge/Decl.lean:97`), from a real
  run; a conjunct of four of `DeclR`'s six kinds.  *Discharges*:
  today.  Seal 49's exposure is what made this premise reach `hrun`
  on the nose — before it the key demanded
  `inferTypeCore … = .ok (.sort u)`, which `checkConstantVal` never
  produces. -/
  constantVal : ConstantValR μ fuel env₀ cval cv c.toConstantVal.type
  /-- The constant is stored.  *Provenance*: the install.
  *Discharges*: today. -/
  stored : c ∈ env.consts
  /-- **`Denote2Total` at the stored type.**  *Provenance*: seal 33's
  parked residue.  *Discharges*: at junction closure. -/
  storedAnnot : denote2 μ m.acval env φ F 0 c.toConstantVal.type
    = some ta

/-! ## Block 3 — what `DeclStep2` costs

Mode-generic by construction: `denote2Extend` and `newMember` are
quantified over **every** `CheckMode`, so this block carries no mode
premise and seal 10's withdrawal of `μ.verified` is not reintroduced
here. -/

/-- **The `DeclStep2` residues** at a fresh axiom install —
`declStep2_of_axiom`'s premise list, named. -/
structure DeclStep2Residues (V : Type w) [SetTheory V] {env : Env}
    (m : EnvS2U V env) (cvA : ConstantVal)
    (A : (Name → Nat) → AVExpr) where
  /-- The installed name is fresh.  *Provenance*: `ConstantValR`'s
  first conjunct at the install.  *Discharges*: today. -/
  fresh : env.find? cvA.name = none
  /-- The **collapse-lane** witness at the extension.  *Provenance*:
  v1's own install (`declAxiomS`), which this lane does not redo.
  *Discharges*: today, wherever v1's axiom install runs. -/
  baseExt : EnvS V ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩
  /-- …and it agrees with the prefix away from the new name.
  *Provenance*: the same install's extension lemma.  *Discharges*:
  today. -/
  cvalAgree : ∀ n, n ≠ cvA.name → m.base.cval n = baseExt.cval n
  /-- The fresh leaf erases to the collapse-lane valuation.
  *Provenance*: the annotated leaf's construction.  *Discharges*:
  with the interp2 install (`Install2.lean`'s pattern). -/
  aErase : ∀ ψ, (A ψ).erase = baseExt.cval cvA.name ψ
  /-- …is closed, …  *Provenance*: as above. -/
  aClosed : ∀ (ψ : Name → Nat) (k : Nat), (A ψ).liftN 1 k = A ψ
  /-- …reads only its own level parameters, … -/
  aParams : ∀ ψ₁ ψ₂ : Name → Nat,
    (∀ p ∈ cvA.levelParams, ψ₁ p = ψ₂ p) → A ψ₁ = A ψ₂
  /-- …and is truthful. -/
  aOk : ∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ)
  /-- **`denote2` is stable across the install.**  *Provenance*:
  `Keys2.lean`'s `Denote2EnvExtend`, which `Denote2Extend.lean`
  composes out of the Θ lane's (E) plus `FindPreserved` and the
  literal guards.  *Discharges*: when Θ lands — it is the same
  frozen transport as `envExtend`, one level up. -/
  denote2Extend : ∀ (ν : CheckMode) (ψ : Name → Nat),
    Denote2EnvExtend ν env ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩
      (acvalWith m.acval cvA.name A) ψ
  /-- **`MemberBlock2` at the new axiom.**  *Provenance*: the
  install-tier half seal 40 measured — `MemberValR` pins the model
  counterpart by `Expr.eqUpToNames`, a syntactic rename check, and a
  standard axiom has no value to infer, so **no key at the prefix
  supplies this**.  *Discharges*: with the interp2 install of the
  standard-axiom and member blocks.  **Inhabited** at a probe
  environment by `memberBlock2_piProbe`. -/
  newMember : ∀ (ν : CheckMode) (ψ : Name → Nat),
    MemberBlock2 V ν ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩
      (acvalWith m.acval cvA.name A) ψ cvA

/-! ## The bundle -/

/-- **The complete hypothesis list of the interp2 install keys.**
Three blocks plus the lane's single shared residue.  Every entry is
named and carries its provenance; nothing is an anonymous `∃` and
nothing is assumed silently inside a proof. -/
structure InstallKeys2Residues (V : Type w) [SetTheory V]
    (μ : CheckMode) {env : Env} (m : EnvS2U V env) (φ : Name → Nat)
    (fuel Fop Fty : Nat) (c : Name) (valA : Expr)
    (ciE : ConstantInfo) (env₀ : Env) (cval : TConstVal)
    (cv : ConstantVal) (cS : ConstantInfo) (ta : AVExpr)
    (cvA : ConstantVal) (A : (Name → Nat) → AVExpr) where
  /-- **The lane's single named residue.**  *Provenance*: generation
  six's step, assembled from fifteen residues by
  `checkStep2E_of_quarters` (`Capstone2E.lean`).  *Discharges*: at
  junction closure, when the two zips, `SortSubstStable`,
  `RecRulesV2` and the remaining residues land.  **Not inhabited in
  this tree** — that is the sequencing seal 39 adopted, not an
  oversight. -/
  checkStep : CheckStep2E μ V
  /-- Block 1. -/
  reducePin : ReducePin2Residues V μ m φ fuel Fop c valA ciE
  /-- Block 2. -/
  memberBlock :
    MemberBlock2Residues V μ m φ fuel Fty env₀ cval cv cS ta
  /-- Block 3. -/
  declStep : DeclStep2Residues V m cvA A

/-- **The milestone, as one statement: the three interp2 install keys
hold on precisely the named residues.**

Read the signature as the deliverable — the conclusion is the three
keys `Keys2.lean` states, and the hypothesis is exactly
`InstallKeys2Residues`, whose fields are the residue set scope ruling
(ii) priced.  Nothing else enters: no new axiom, no anonymous
existential, no premise whose provenance is unrecorded.

**Mode-generic.**  The one `μ` in the signature is the checker mode
the runs were made in; no field mentions `μ.verified` (seal 10). -/
theorem installKeys2_of_residues {V : Type w} [SetTheory V]
    {μ : CheckMode} {env : Env} (m : EnvS2U V env) {φ : Name → Nat}
    {fuel Fop Fty : Nat} {c : Name} {valA : Expr}
    {ciE : ConstantInfo} {env₀ : Env} {cval : TConstVal}
    {cv : ConstantVal} {cS : ConstantInfo} {ta : AVExpr}
    {cvA : ConstantVal} {A : (Name → Nat) → AVExpr}
    (H : InstallKeys2Residues V μ m φ fuel Fop Fty c valA ciE env₀
      cval cv cS ta cvA A) :
    ReducePin2 V env m.acval φ c ∧
      MemberBlock2 V μ env m.acval φ cS.toConstantVal ∧
      DeclStep2 V ⟨ConstantInfo.axiomInfo cvA :: env.consts⟩ :=
  ⟨reducePin2_of_checkStep m H.checkStep H.reducePin.elemFound
      H.reducePin.elemMono H.reducePin.opNoFvar
      H.reducePin.opBounded H.reducePin.opAnnot H.reducePin.opFits
      H.reducePin.pinRun,
    memberBlock2_of_constantValR m H.checkStep
      H.memberBlock.inferExists H.memberBlock.envExtend
      H.memberBlock.constantVal H.memberBlock.stored
      H.memberBlock.storedAnnot,
    declStep2_of_axiom m H.declStep.fresh H.declStep.baseExt
      H.declStep.cvalAgree H.declStep.aErase H.declStep.aClosed
      H.declStep.aParams H.declStep.aOk H.declStep.denote2Extend
      H.declStep.newMember⟩

/-! ## The three sweeps

**1. Smallest fuel.**  The bundle asserts no `denote2` success as a
conclusion; `opAnnot` and `storedAnnot` are *premises*, at fuels the
structure names (`Fop`, `Fty`) rather than at every fuel — the shape
that refuted `EnvS2.acval_defn` (STOP 2) is absent.
`MemberBlock2`'s own conclusion keeps its existential fuel slack, for
the reason its docstring records.

**2. Vacuity.**  Field by field, above.  The honest summary is that
**three of the fields are not inhabited anywhere in this tree**
(`checkStep`, `inferExists`, `envExtend`), and that is the recorded
sequencing rather than a discovery: seal 39 priced them, seal 50
re-read seal 49's gate against that pricing.  The remaining fields
are inhabited either outright (`constantVal`, the syntactic ones) or
at probes (`opFits`, `newMember`).

Per seal 11 this is not a clean bill of health.  What it *is*: a
statement whose every premise has a name, a source and a date, so a
later consumer can attempt each one and refute it if it is wrong.

**3. Tombstones.**  A file added, none edited. -/

end Setlec.SetR.Interp2
