import Setlec.SetR.Main
import Setlec.SetR.Interp2.Step2Cons

/-!
# The fourteen's conditional swap — the same results over `EnvS2U`

`Setlec/SetR/Main.lean`'s fourteen conclude over `EnvS`.  This file
states their `EnvS2U` counterparts, conditional on the install step
the interp2 tier does not yet have.

**Three things, recorded rather than assumed.**

1. **v1's fourteen are untouched and stay hypothesis-free.**  Nothing
   here edits `Main.lean`; every theorem below is a new name ending in
   `R2`, and the `_R` forms keep their unconditional proofs.  Where a
   swapped form needs an `EnvS` fact it reads it off `EnvS2U.base` —
   *containment*, not re-proof.
2. **Mode-generic.**  Seal 10 withdrew `μ.verified`, so this is a
   swap and not a swap-plus-restriction.  `DeclStep2All` quantifies
   over `μ` exactly as v1's `declStepS` does, and no statement below
   carries a mode premise.
3. **`Nonempty` is not an obstacle** (seal 36's R6): it eliminates
   into `Prop`, so `Nonempty (EnvS2U V env')` is the fold's carrier
   in exactly the way `Nonempty (EnvS V env')` is v1's.

## What the conditional is, and what it is not

The single hypothesis is `DeclStep2All` — the interp2 counterpart of
`Install/Step.lean`'s `declStepS`, at the same `DeclR` currency.  It
is **not** item 1's bundle, and pretending otherwise would be the
honesty rule's own failure mode:

* item 1 (`Keys2Bundle.lean`) closes **three** of the five inputs
  `declStepS` consumes — `ReducePin2`, `MemberBlock2`, `DeclStep2` at
  a fresh axiom.  `DeclBasisS`/`DeclIndS` have no interp2 counterpart
  at all, and `DivModPinS` has one only as a draft (`DivModV2`);
* item 1's `MemberBlock2` lands at a constant already stored in the
  *prefix*, while `declStep2_of_axiom` needs it at the **new** name in
  the extension — the install-tier half seal 40 measured.  So the two
  do not chain, and `DeclStep2Residues.newMember` stays a residue.

`DeclStep2All` is therefore the honest name for "the interp2
dispatch, once it exists", and item 1 is the record of how far its
axiom kind has got.  **It is not inhabited in this tree**, and neither
is `CheckStep2E` behind it; per seals 39 and 50 both discharge at
junction closure, and until then every statement below says "if the
install lane lands, the fourteen swap" and nothing stronger.

## What is no longer a hypothesis

`declStep2All_of` **proves the dispatch** from four per-kind install
obligations (`Step2Cons.lean`), so `DeclStep2All` is not one opaque
residue any more.  What is left of it, split by kind:

| kind | reduces to | inhabited? |
|---|---|---|
| tolerated axiom | nothing — `env₂ = env` | **yes**, here |
| `def` | `Denote2BodyOfRun` + `ValueResidues2` | no |
| `theorem`, `opaque` | the same, plus `hleaf` at `opaque` | no |
| stored axiom | `DeclStep2Residues` | no |
| basis, `indDecl` | nothing in this tree | no |

*A relocation with a finer grain is still a relocation; what stops it
being only that is the tolerated branch, `declStep2_defn`'s
collapse-lane inputs, and the two body clauses `declStep2_of_value`
discharges outright.*

## What the swap actually buys, per theorem

* The four `checkDecls*_sound_R2` and `checkDecl_sound_R2` conclude a
  **strictly stronger** carrier than their `_R` originals: the
  annotated valuation and its five laws, on top of the collapse-lane
  invariant.  This is where the swap has content.
* The eight `no_proof_of_Empty*_R2` conclude `False`, which v1 already
  proves **unconditionally**.  Their content is the *route*, not the
  fact: they show that the interp2 tier reaches the same corollaries
  through its own fold.  Said out loud because a conditional theorem
  with an already-unconditional conclusion is worth exactly that much
  and no more.
* `no_constant_of_Empty_R2` is the tier's own statement of the
  emptiness fact, **and its proof is now interp2-side**: `mem_type2`
  supplies the membership and `acval_empty_pinned` the leaf.  Seal
  51 read the missing `empty_pinned` counterpart as a missing field;
  the check (`EmptyPin2.lean`) found it is a *consequence* —
  `acval_erase` plus the collapse-lane pin plus erasure injectivity
  at the constant clause.  No `EnvS2U` field was added.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory Expr
open Setlec.SetR.Interp2 (EnvS2U DeclValue2S DeclAxiom2S DeclBasis2S
  DeclInd2S ValueResidues2 Denote2BodyOfRun leafEq_defn denote2
  declStep2_of_valueResidues no_constant_of_Empty_2)
open Setlec.SetR.Interp2 (EnvS2UM DeclValue2SM DeclAxiom2SM
  DeclBasis2SM DeclInd2SM ValueResidues2M
  declStep2M_of_valueResidues)
open Setlec.SetR.Interp2 (DeclStep2M AxiomResidues2M
  declStep2M_of_axiomResidues AxiomResidues3M AnnotOk2
  declStep2M_of_axiomResidues3)

universe w
variable {V : Type w} [SetTheory V]

/-! ## The one hypothesis -/

/-- **The interp2 counterpart of `declStepS`.**  A checked
declaration of any kind extends the annotated invariant, at the same
`DeclR` currency v1's dispatch uses.

*Provenance*: `Install/Step.lean`'s `declStepS`, with `EnvS` replaced
by `EnvS2U`.  Its five inputs there are `DivModPinS`, `ReducePinS`,
`StdAxiomKeyS`, `DeclBasisS`, `DeclIndS`; item 1's bundle closes the
interp2 forms of the second and third (and of the axiom-kind
construction itself), and the other two have no interp2 counterpart
yet.

*Discharges*: with the interp2 install lane, at junction closure.
**Not inhabited in this tree.**

*Not `rfl`*: the conclusion is `Nonempty` of a nine-field structure at
an arbitrary extended environment.

**No mode premise.**  `μ` is the checker mode the run was made in,
quantified exactly as in `declStepS`. -/
def DeclStep2All (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env env₂ : Env} {d : Declaration} (m : EnvS2U V env),
    EtaFamiliesClosed env →
    DeclR μ F m.base.cval env d env₂ →
    Nonempty (EnvS2U V env₂)

/-- **The dispatch, proved.**  `DeclStep2All` from the four install
obligations `Step2Cons.lean` names, exactly as `declStepS` proves v1's
dispatch from its five: `DeclR`'s six clauses *are* the dispatch, so
this half of the residue is not a hypothesis and never was.

Two things are settled here rather than assumed:

* **`def`, `theorem` and `opaque` share one obligation.**  They differ
  only in which `ConstantInfo` they store and in whether that
  `ConstantInfo` has a body to identify, and `DeclValue2S` is stated
  at the stored `c₀` with those two body clauses as premises.
* **The axiom kind's tolerated branch is discharged.**  A tolerated
  axiom installs nothing (`env₂ = env`), so the given `EnvS2U`
  answers for it — the one branch of the six kinds that needs no
  install at all.

*What remains uninhabited is the four obligations, not the dispatch.*
`DeclValue2S` reduces to `declStep2_of_value`'s residues,
`DeclAxiom2S` to `DeclStep2Residues`; `DeclBasis2S` and `DeclInd2S`
have no interp2 counterpart in this tree at all. -/
theorem declStep2All_of {μ : CheckMode} (hval : DeclValue2S V μ)
    (hax : DeclAxiom2S V μ) (hbas : DeclBasis2S V)
    (hind : DeclInd2S V μ) : DeclStep2All V μ := by
  intro F env env₂ d m hE h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, hvfr, rfl, -, -⟩ := h
    exact hval m hcv hvfr rfl
      (fun cv2 v2 h2 heq => by
        simp only [ConstantInfo.defnInfo.injEq] at heq
        exact heq.2.1)
      (fun cv2 v2 heq => nomatch heq)
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, hvfr, rfl⟩ := h
    exact hval m hcv hvfr rfl (fun cv2 v2 h2 heq => nomatch heq)
      (fun cv2 v2 heq => by
        simp only [ConstantInfo.thmInfo.injEq] at heq
        exact heq.2)
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, hvfr, rfl, -⟩ := h
    exact hval m hcv hvfr rfl (fun cv2 v2 h2 heq => nomatch heq)
      (fun cv2 v2 heq => nomatch heq)
  | axiomDecl cv =>
    obtain ⟨type', hcv, harm⟩ := h
    rcases harm with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ |
      ⟨-, -, -, -, -, -, -, rfl⟩
    · exact hax m hcv
    · exact hax m hcv
    · exact hax m hcv
    · exact ⟨m⟩
  | basisDecl kind => exact hbas ⟨m⟩ h
  | indDecl block => exact hind m hE (declIndDispatchR_eq_ind.mp h)

/-- **The `def` kind, on the interp2 residues alone.**  Every
collapse-lane input is v1's own and none of them is assumed:

* the extension **and its valuation agreement** come from `declDefnS`,
  which now exposes both (the `Nonempty` conclusion hid the agreement,
  and `acval_erase` cannot be stated without it);
* the leaf equation at the extension is `EnvS.defn_eq`, free;
* freshness is `ConstantValR`'s first conjunct;
* the new leaf itself is named by the run `ValueFrontR` exposes.

So the `def` kind's whole remaining cost is `Denote2BodyOfRun` at the
prefix and `ValueResidues2`'s six fields.  **Neither is inhabited**,
so this is a reduction and not yet an install — but it is a reduction
to six named things rather than to the kind as a whole. -/
theorem declStep2_defn (hdm : DivModPinS V) {F : Nat}
    {env : Env} {cv : ConstantVal} {value type' value' : Expr}
    {hint : ReducibilityHint} (m : EnvS2U V env)
    (h : DeclDefnR modeR F env m.base.cval cv value hint
      ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩)
    (hcvR : ConstantValR modeR F env m.base.cval cv type')
    (hvf : ValueFrontR modeR F env m.base.cval cv value type' value')
    (hrun : ∀ ψ : Name → Nat, Denote2BodyOfRun modeR env m.acval ψ)
    (hres : ∀ A : (Name → Nat) → AVExpr,
      (∀ ψ : Name → Nat, ∃ F' : Nat,
        denote2 modeR m.acval env ψ F' 0 value' = some (A ψ)) →
      ValueResidues2 V modeR m
        (.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
        value' A) :
    Nonempty (EnvS2U V
      ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩) := by
  obtain ⟨hbase, hag⟩ := declDefnS hdm m.base h
  exact declStep2_of_valueResidues m
    (Option.isNone_iff_eq_none.mp hcvR.1)
    (fun _ heq => nomatch heq) hvf hrun hbase hag
    (leafEq_defn hbase)
    (fun cv2 v2 h2 heq => by
      simp only [ConstantInfo.defnInfo.injEq] at heq
      exact heq.2.1)
    (fun cv2 v2 heq => nomatch heq) hres

/-! ## The mode-indexed lane

Seal 53's de-generalization, threaded through the dispatch.  Nothing
here is a new argument: `declStep2AllM_of` is `declStep2All_of`'s
proof verbatim at `EnvS2UM V μ`, and that is the check — the ruling
said the index threads for free because the fourteen already quantify
`μ` outermost, and this is where that is verified rather than
asserted. -/

/-- **`DeclStep2All` at the mode-indexed invariant.**  The mode is
still quantified exactly as in `declStepS`; what changed is that the
invariant on both sides is the one a single checker run can supply. -/
def DeclStep2AllM (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env env₂ : Env} {d : Declaration}
    (m : EnvS2UM V μ env),
    EtaFamiliesClosed env →
    DeclR μ F m.base.cval env d env₂ →
    Nonempty (EnvS2UM V μ env₂)

/-- **The dispatch at one mode, proved.**  `declStep2All_of`'s proof
verbatim: `DeclR`'s six clauses are the dispatch, and the mode index
is inert in every one of them. -/
theorem declStep2AllM_of {μ : CheckMode} (hval : DeclValue2SM V μ)
    (hax : DeclAxiom2SM V μ) (hbas : DeclBasis2SM V μ)
    (hind : DeclInd2SM V μ) : DeclStep2AllM V μ := by
  intro F env env₂ d m hE h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, hvfr, rfl, -, -⟩ := h
    exact hval m hcv hvfr rfl
      (fun cv2 v2 h2 heq => by
        simp only [ConstantInfo.defnInfo.injEq] at heq
        exact heq.2.1)
      (fun cv2 v2 heq => nomatch heq)
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, hvfr, rfl⟩ := h
    exact hval m hcv hvfr rfl (fun cv2 v2 h2 heq => nomatch heq)
      (fun cv2 v2 heq => by
        simp only [ConstantInfo.thmInfo.injEq] at heq
        exact heq.2)
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, hvfr, rfl, -⟩ := h
    exact hval m hcv hvfr rfl (fun cv2 v2 h2 heq => nomatch heq)
      (fun cv2 v2 heq => nomatch heq)
  | axiomDecl cv =>
    obtain ⟨type', hcv, harm⟩ := h
    rcases harm with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ |
      ⟨-, -, -, -, -, -, -, rfl⟩
    · exact hax m hcv
    · exact hax m hcv
    · exact hax m hcv
    · exact ⟨m⟩
  | basisDecl kind => exact hbas ⟨m⟩ h
  | indDecl block => exact hind m hE (declIndDispatchR_eq_ind.mp h)

/-! ### The axiom obligation, at the premise it can actually be met on

`DeclAxiom2SM` asks for the install from `ConstantValR` alone, and
nothing can meet it: an install owes an *inhabitant* of the axiom's
denoted type, and a well-typed type need not have one.  It is
**tombstoned** at its definition (`Step2Cons.lean`) as unprovable by
design — the checker reaches `extendAxiomS` only through
`DeclAxiomR`'s branches, and each storing branch carries a key
(`StdAxiomKeyS`, `trustCompilerKeyS`, `OfReduceKeyS`) whose fourth
conjunct *is* the inhabitant.  The obligation below asks on that
`DeclAxiomR` instead — which is exactly what `declStep2AllM_of`
already had in hand at the axiom clause, and threw away by branching
before calling `hax`.

Both versions stand, and `declAxiom2SMR_of_generic` below records that
the second is a **weakening** of the first.  The dispatch below is
`declStep2AllM_of` with the axiom clause's four-way `rcases`
**removed**, since the obligation now answers for the tolerated branch
too. -/

/-- **The axiom kind's install obligation, at the branch witness.**
*Reduces to*: `AxiomResidues2M`'s five fields, by
`declAxiom2SMR_of_residues` — `DeclStep2Residues`' nine minus `fresh`,
`baseExt`, `cvalAgree` and `closed`. -/
def DeclAxiom2SMR (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env env₂ : Env} {cv : ConstantVal}
    (m : EnvS2UM V μ env),
    DeclAxiomR μ F env m.base.cval cv env₂ → DeclStep2M V μ env₂

/-- **What is left of the axiom obligation once `baseExt` and
`closed` are supplied**: the fresh leaf's three remaining laws
(`erase`, `params`, `ok2`) and the two frozen transports, at the
extension `declAxiomExtS` builds. -/
def AxiomResidues2SM (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop :=
  ∀ {env : Env} {cv : ConstantVal} {type' : Expr}
    (m : EnvS2UM V μ env) (hb : EnvS V ⟨ConstantInfo.axiomInfo
      ⟨cv.name, cv.levelParams, type'⟩ :: env.consts⟩),
    (∀ n, n ≠ cv.name → m.base.cval n = hb.cval n) →
    ∃ A : (Name → Nat) → AVExpr, AxiomResidues2M V μ m
      ⟨cv.name, cv.levelParams, type'⟩ hb A

/-- **The axiom obligation, reduced.**  The install's collapse-lane
half is no longer assumed anywhere: it comes from `declAxiomExtS`,
whose own two keys (`stdAxiomKeyS`, `ofReduceKeyS`) are theorems. -/
theorem declAxiom2SMR_of_residues {μ : CheckMode}
    (hres : AxiomResidues2SM V μ) : DeclAxiom2SMR V μ :=
  fun m h => declStep2M_of_axiomResidues m h
    (fun _ hb hag => hres m hb hag)

/-- **What is left of the axiom obligation once the *leaf* is
supplied.**  `AxiomResidues2SM` minus the two fields the branch keys
now answer for — `erase` and `ok2` — which arrive as the leaf's own
laws (`declStep2M_of_axiomResidues3`, `Interp2/Step2Cons.lean`).  The
extension has vanished from the statement, and that is the point: the
five-field form quantified `hb` over *every* agreeing extension, at
which no annotated leaf exists at all.

Three fields where the ledger said five: the leaf's level-parameter
law (the erase-injectivity wall, seal 61's third answer) and the two
Θ-frozen transports. -/
def AxiomResidues3SM (V : Type w) [SetTheory V] (μ : CheckMode) :
    Prop :=
  ∀ {env : Env} {cv : ConstantVal} {type' : Expr}
    (m : EnvS2UM V μ env) (A : (Name → Nat) → AVExpr),
    (∀ (ψ : Name → Nat) (ρ : Nat → V), AnnotOk2 V ρ (A ψ)) →
    AxiomResidues3M V μ m ⟨cv.name, cv.levelParams, type'⟩ A

/-- **The axiom obligation, reduced again.**  Both halves of the
install's collapse-lane side and the annotated leaf are now theorems
of this tree; what the obligation still asks for is the three. -/
theorem declAxiom2SMR_of_residues3 {μ : CheckMode}
    (hres : AxiomResidues3SM V μ) : DeclAxiom2SMR V μ :=
  fun m h => declStep2M_of_axiomResidues3 m h
    (fun _ A hA => hres m A hA)

/-- **The branch form is a weakening of the tombstoned one.**  The
generic obligation, if anything could ever supply it, supplies the
branch obligation — this is `declStep2AllM_of`'s axiom clause, lifted
out of the dispatch and named.

*Why it is worth naming*: it is the check that re-premising **loses
nothing**.  Everything the tombstoned `DeclAxiom2SM` could install,
`DeclAxiom2SMR` installs; the converse fails, and that asymmetry is
the whole content of the tombstone — the branch witness carries an
inhabitant that `ConstantValR` does not have. -/
theorem declAxiom2SMR_of_generic {μ : CheckMode}
    (hax : DeclAxiom2SM V μ) : DeclAxiom2SMR V μ := by
  intro F env env₂ cv m h
  obtain ⟨type', hcv, harm⟩ := h
  rcases harm with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ |
    ⟨-, -, -, -, -, -, -, rfl⟩
  · exact hax m hcv
  · exact hax m hcv
  · exact hax m hcv
  · exact ⟨m⟩

/-- **The dispatch at one mode, on the reduced axiom obligation.**
`declStep2AllM_of` with `DeclAxiom2SM` replaced by `DeclAxiom2SMR`;
the other five clauses are verbatim. -/
theorem declStep2AllM_ofR {μ : CheckMode} (hval : DeclValue2SM V μ)
    (hax : DeclAxiom2SMR V μ) (hbas : DeclBasis2SM V μ)
    (hind : DeclInd2SM V μ) : DeclStep2AllM V μ := by
  intro F env env₂ d m hE h
  cases d with
  | defnDecl cv value hint =>
    obtain ⟨type', value', hcv, hvfr, rfl, -, -⟩ := h
    exact hval m hcv hvfr rfl
      (fun cv2 v2 h2 heq => by
        simp only [ConstantInfo.defnInfo.injEq] at heq
        exact heq.2.1)
      (fun cv2 v2 heq => nomatch heq)
  | thmDecl cv value =>
    obtain ⟨type', value', hcv, -, -, hvfr, rfl⟩ := h
    exact hval m hcv hvfr rfl (fun cv2 v2 h2 heq => nomatch heq)
      (fun cv2 v2 heq => by
        simp only [ConstantInfo.thmInfo.injEq] at heq
        exact heq.2)
  | opaqueDecl cv value =>
    obtain ⟨type', value', hcv, hvfr, rfl, -⟩ := h
    exact hval m hcv hvfr rfl (fun cv2 v2 h2 heq => nomatch heq)
      (fun cv2 v2 heq => nomatch heq)
  | axiomDecl cv => exact hax m h
  | basisDecl kind => exact hbas ⟨m⟩ h
  | indDecl block => exact hind m hE (declIndDispatchR_eq_ind.mp h)

/-- **The `def` kind at one mode, and the residue is four.**
`declStep2_defn` with `EnvS2UM` in place of `EnvS2U`: every
collapse-lane input is still v1's own, `Denote2BodyOfRun` is still
owed at the prefix, and what is left of the annotated side is
`ValueResidues2M` — `ValueResidues2` minus `modeAgree` (whose demand
seal 53 withdrew) and minus `closed` (which `denote2_closed` proves
from the front door's own syntactic conjuncts). -/
theorem declStep2M_defn (hdm : DivModPinS V) {F : Nat}
    {env : Env} {cv : ConstantVal} {value type' value' : Expr}
    {hint : ReducibilityHint} (m : EnvS2UM V modeR env)
    (h : DeclDefnR modeR F env m.base.cval cv value hint
      ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩)
    (hcvR : ConstantValR modeR F env m.base.cval cv type')
    (hvf : ValueFrontR modeR F env m.base.cval cv value type' value')
    (hrun : ∀ ψ : Name → Nat, Denote2BodyOfRun modeR env m.acval ψ)
    (hres : ∀ A : (Name → Nat) → AVExpr,
      (∀ ψ : Name → Nat, ∃ F' : Nat,
        denote2 modeR m.acval env ψ F' 0 value' = some (A ψ)) →
      ValueResidues2M V modeR m
        (.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint) A) :
    Nonempty (EnvS2UM V modeR
      ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint ::
        env.consts⟩) := by
  obtain ⟨hbase, hag⟩ := declDefnS hdm m.base h
  exact declStep2M_of_valueResidues m
    (Option.isNone_iff_eq_none.mp hcvR.1)
    (fun _ heq => nomatch heq) hvf hrun hbase hag
    (leafEq_defn hbase)
    (fun cv2 v2 h2 heq => by
      simp only [ConstantInfo.defnInfo.injEq] at heq
      exact heq.2.1)
    (fun cv2 v2 heq => nomatch heq) hres

/-- The annotated fold's carrier — `EnvSOk` one tier up.  The eta
side invariant is V-free and is **not** re-proved here: it comes from
v1's own dispatch, run alongside at `m.base`. -/
def EnvS2UOk (V : Type w) [SetTheory V] (env : Env) : Prop :=
  Nonempty (EnvS2U V env) ∧ EtaFamiliesClosed env

/-- The empty environment carries the annotated invariant. -/
theorem EnvS2UOk.empty (V : Type w) [SetTheory V] :
    EnvS2UOk V Env.empty :=
  ⟨⟨EnvS2U.empty V⟩, EtaFamiliesClosed.empty⟩

/-! ## The swap, theorem by theorem -/

/-- **`no_constant_of_Empty_R`, over `EnvS2U` — and now over
`interp2`.**  Seal 51 recorded this as a stall: the proof was v1's at
`m.base`, so the annotated valuation played no part.  It does now.
The membership is `mem_type2`, the leaf is pinned by `acval_erase`
plus `EnvS.empty_pinned` plus erasure injectivity at the constant
clause (`EmptyPin2.lean`), and only the pin itself is still the
collapse lane's — which no annotated field could replace, since
`acval` is *defined* to erase to the pinned valuation. -/
theorem no_constant_of_Empty_R2 {env : Env} (m : EnvS2U V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False :=
  no_constant_of_Empty_2 (EnvS2U.toM V m CheckMode.setModel) c hc hty

/-- **`checkDecl_sound_R`, over `EnvS2U`.**  One checked declaration
extends the annotated invariant. -/
theorem checkDecl_sound_R2 (hstep : DeclStep2All V modeR)
    {F : Nat} {env env₂ : Env} {d : Declaration} (m : EnvS2U V env)
    (hE : EtaFamiliesClosed env)
    (h : checkDecl modeR (fueledOps modeR F) env d = .ok env₂) :
    EnvS2UOk V env₂ :=
  ⟨hstep m hE (checkDeclR_sound m.base hE h),
    (declStepS divModPinS reducePinS stdAxiomKeyS declBasisS
      (declIndS memberKeyS) m.base hE
      (checkDeclR_sound m.base hE h)).2⟩

/-- The pure checker's fold, over `EnvS2U`. -/
theorem foldlM_R2 {F : Nat}
    (hstep : DeclStep2All V modeR) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvS2UOk V env →
      ds.foldlM (checkDecl modeR (fueledOps modeR F)) env = .ok env' →
      EnvS2UOk V env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl modeR (fueledOps modeR F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨m⟩, hE⟩ := hm
      exact foldlM_R2 hstep ds env1
        (checkDecl_sound_R2 hstep m hE hd) h

/-- **The acceptance theorem, over `EnvS2U`.**  `checkDecls_sound_R`
with the annotated carrier. -/
theorem checkDecls_sound_R2 {F : Nat}
    (hstep : DeclStep2All V modeR)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env') :
    Nonempty (EnvS2U V env') :=
  (foldlM_R2 hstep ds Env.empty (EnvS2UOk.empty V) h).1

/-- **No proof of `Empty`**, through the annotated fold. -/
theorem no_proof_of_Empty_R2 (V : Type w) [SetTheory V]
    {F : Nat} (hstep : DeclStep2All V modeR)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound_R2 (V := V) hstep h
  exact no_constant_of_Empty_R2 m c hc hty

/-- Annotating the `Empty` leaf returns it unchanged.  Factored out
of the four input-level folds, where `Main.lean` inlines it; the
statement is v1's, verbatim. -/
theorem annotate_empty_const_eq {μ : CheckMode} {env : Env} {F : Nat}
    {type : Expr}
    (h : annotateCore μ env F 0 (.const emptyName []) = .ok type) :
    Expr.const emptyName [] = type := by
  cases F with
  | zero =>
    rw [annotateCore_zero] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  | succ F' =>
    rw [annotateCore_succ] at h
    simpa [annotateBody, pure, Except.pure] using h

/-! ## The input-level four

Their conclusion is `False`, which v1 proves unconditionally, so what
these add is the route and not the fact.  Stated anyway, because the
route is what the swap is about: the fold that carries them is the
annotated one throughout. -/

/-- The pure checker's input-level fold, over `EnvS2U`. -/
theorem foldlM_no_Empty_R2 {F : Nat}
    (hstep : DeclStep2All V modeR)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hty : cv.type = .const emptyName []) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvS2UOk V env →
      ds.foldlM (checkDecl modeR (fueledOps modeR F)) env = .ok env' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False
  | [], _, _, _, _, hd => by rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, hd => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl modeR (fueledOps modeR F) env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨⟨m⟩, hE⟩ := hm
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hdd hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type :=
        annotate_empty_const_eq hann
      obtain ⟨m1⟩ := (checkDecl_sound_R2 (d := d) hstep m hE hdd).1
      exact no_constant_of_Empty_R2 m1 c hc (by rw [hcv])
    · refine foldlM_no_Empty_R2 (value := value) (hint := hint)
        hstep hty ds env1
        (checkDecl_sound_R2 (d := d) hstep m hE hdd) h ?_
      rcases hd with hd | hd
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inl rfl) hdis
        · exact Or.inl hmem
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inr rfl) hdis
        · exact Or.inr hmem

/-- **No accepted stream declares a proof of `Empty`** — annotated
fold. -/
theorem no_proof_of_Empty_input_R2 (V : Type w) [SetTheory V]
    {F : Nat} (hstep : DeclStep2All V modeR)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_R2 hstep hty ds Env.empty (EnvS2UOk.empty V) h hd

/-! ## The mode-indexed fold — the M lane, to the same fourteen

Seal 54 landed the mode index *beside* the all-mode lane and stopped
at the dispatch (`DeclStep2AllM`).  This section carries it the rest
of the way: every carrier, every fold and every `no_proof_of_Empty*`
above, restated at `EnvS2UM V μ` and conditional on `DeclStep2AllM`.

**Why beside and not in place.**  `DeclStep2AllM` neither implies nor
is implied by `DeclStep2All`: the input class widens (`EnvS2UM` is
weaker, so there are more of them) *and* the output class widens with
it, so the two are incomparable and re-pointing would have deleted a
standing conditional result rather than strengthened it.  That is a
different situation from the claims cone, where the binder is
universally quantified in both statements and widening it is a
strengthening.

**Every proof below is the all-mode proof verbatim**, which is what
makes this a check and not a second development: the mode index is
inert in the fold exactly as `declStep2AllM_of` showed it inert in
the dispatch.  The one place it is *not* inert is the entry point —
`EnvS2UOkM.empty` goes through `EnvS2U.toM`, because the empty
environment's witness is built all-mode and weakened, not built
twice.

**What this buys.**  The M lane now reaches the capstone: with the
four mode-indexed install obligations, `declStep2AllM_of` gives
`DeclStep2AllM`, and `no_proof_of_Empty_R2M` and its seven siblings
follow.  The all-mode lane above still needs `DeclStep2All`, which
the front door's single run cannot supply — that was seal 53's whole
finding. -/

/-- The annotated fold's carrier at one mode. -/
def EnvS2UOkM (V : Type w) [SetTheory V] (μ : CheckMode)
    (env : Env) : Prop :=
  Nonempty (EnvS2UM V μ env) ∧ EtaFamiliesClosed env

/-- The empty environment carries the mode-indexed invariant. -/
theorem EnvS2UOkM.empty (V : Type w) [SetTheory V] (μ : CheckMode) :
    EnvS2UOkM V μ Env.empty :=
  ⟨⟨EnvS2UM.empty V μ⟩, EtaFamiliesClosed.empty⟩

/-- **`no_constant_of_Empty_R`, over `EnvS2UM` — and now over
`interp2`.**  Seal 51 recorded this as a stall: the proof was v1's at
`m.base`, so the annotated valuation played no part.  It does now.
The membership is `mem_type2`, the leaf is pinned by `acval_erase`
plus `EnvS.empty_pinned` plus erasure injectivity at the constant
clause (`EmptyPin2.lean`), and only the pin itself is still the
collapse lane's — which no annotated field could replace, since
`acval` is *defined* to erase to the pinned valuation. -/
theorem no_constant_of_Empty_R2M {μ : CheckMode} {env : Env}
    (m : EnvS2UM V μ env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False :=
  no_constant_of_Empty_2 m c hc hty

/-- **`checkDecl_sound_R`, over `EnvS2UM`.**  One checked declaration
extends the annotated invariant. -/
theorem checkDecl_sound_R2M (hstep : DeclStep2AllM V modeR)
    {F : Nat} {env env₂ : Env} {d : Declaration} (m : EnvS2UM V modeR env)
    (hE : EtaFamiliesClosed env)
    (h : checkDecl modeR (fueledOps modeR F) env d = .ok env₂) :
    EnvS2UOkM V modeR env₂ :=
  ⟨hstep m hE (checkDeclR_sound m.base hE h),
    (declStepS divModPinS reducePinS stdAxiomKeyS declBasisS
      (declIndS memberKeyS) m.base hE
      (checkDeclR_sound m.base hE h)).2⟩

/-- The pure checker's fold, over `EnvS2UM`. -/
theorem foldlM_R2M {F : Nat}
    (hstep : DeclStep2AllM V modeR) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvS2UOkM V modeR env →
      ds.foldlM (checkDecl modeR (fueledOps modeR F)) env = .ok env' →
      EnvS2UOkM V modeR env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl modeR (fueledOps modeR F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨m⟩, hE⟩ := hm
      exact foldlM_R2M hstep ds env1
        (checkDecl_sound_R2M hstep m hE hd) h

/-- **The acceptance theorem, over `EnvS2UM`.**  `checkDecls_sound_R`
with the annotated carrier. -/
theorem checkDecls_sound_R2M {F : Nat}
    (hstep : DeclStep2AllM V modeR)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env') :
    Nonempty (EnvS2UM V modeR env') :=
  (foldlM_R2M hstep ds Env.empty (EnvS2UOkM.empty V modeR) h).1

/-- **No proof of `Empty`**, through the annotated fold. -/
theorem no_proof_of_Empty_R2M (V : Type w) [SetTheory V]
    {F : Nat} (hstep : DeclStep2AllM V modeR)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound_R2M (V := V) hstep h
  exact no_constant_of_Empty_R2M m c hc hty

/-! ## The input-level four

Their conclusion is `False`, which v1 proves unconditionally, so what
these add is the route and not the fact.  Stated anyway, because the
route is what the swap is about: the fold that carries them is the
annotated one throughout. -/

/-- The pure checker's input-level fold, over `EnvS2UM`. -/
theorem foldlM_no_Empty_R2M {F : Nat}
    (hstep : DeclStep2AllM V modeR)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hty : cv.type = .const emptyName []) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvS2UOkM V modeR env →
      ds.foldlM (checkDecl modeR (fueledOps modeR F)) env = .ok env' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False
  | [], _, _, _, _, hd => by rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, hd => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl modeR (fueledOps modeR F) env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨⟨m⟩, hE⟩ := hm
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hdd hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type :=
        annotate_empty_const_eq hann
      obtain ⟨m1⟩ := (checkDecl_sound_R2M (d := d) hstep m hE hdd).1
      exact no_constant_of_Empty_R2M m1 c hc (by rw [hcv])
    · refine foldlM_no_Empty_R2M (value := value) (hint := hint)
        hstep hty ds env1
        (checkDecl_sound_R2M (d := d) hstep m hE hdd) h ?_
      rcases hd with hd | hd
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inl rfl) hdis
        · exact Or.inl hmem
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inr rfl) hdis
        · exact Or.inr hmem

/-- **No accepted stream declares a proof of `Empty`** — annotated
fold. -/
theorem no_proof_of_Empty_input_R2M (V : Type w) [SetTheory V]
    {F : Nat} (hstep : DeclStep2AllM V modeR)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_R2M hstep hty ds Env.empty (EnvS2UOkM.empty V modeR) h hd

/-! ### The M lane, end to end

The composition is stated rather than asserted, because "the M lane
feeds the capstone" is exactly a composition claim and the campaign's
rule is that a claim of that shape is checked by writing it down.

Read it as: the **four mode-indexed install obligations** are all
that stands between this tree and the capstone's conclusion in the M
currency.  Nothing else enters — no bridge, no `EnvS2UInImage`, no
mode-agreement premise.  `Denote2ModeAgree` does not appear anywhere
in the chain, which is seal 53's de-generalization cashed. -/

/-- **No proof of `Empty`, from the four mode-indexed install
obligations.**  `declStep2AllM_of` composed with the M fold.  Still
conditional — the four obligations are not inhabited in this tree —
but conditional on *those four* and on nothing else.

**Reads the tombstoned axiom obligation.**  `DeclAxiom2SM` is
unprovable by design, so this form is vacuously conditional at its
axiom premise; `no_proof_of_Empty_R2M_of_installsR` below is the one
to quote. -/
theorem no_proof_of_Empty_R2M_of_installs (V : Type w) [SetTheory V]
    {F : Nat} (hval : DeclValue2SM V modeR)
    (hax : DeclAxiom2SM V modeR) (hbas : DeclBasis2SM V modeR)
    (hind : DeclInd2SM V modeR)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False :=
  no_proof_of_Empty_R2M V (declStep2AllM_of hval hax hbas hind)
    h c hc hty

/-- **The same, with the axiom obligation reduced.**  Three of the
four premises are unchanged; the axiom one is now
`AxiomResidues2SM` — **five** fields at a *supplied* extension, rather
than an obligation nothing could meet.  Still conditional, and the
other three are still not inhabited in this tree. -/
theorem no_proof_of_Empty_R2M_of_installsR (V : Type w) [SetTheory V]
    {F : Nat} (hval : DeclValue2SM V modeR)
    (hax : AxiomResidues2SM V modeR) (hbas : DeclBasis2SM V modeR)
    (hind : DeclInd2SM V modeR)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False :=
  no_proof_of_Empty_R2M V
    (declStep2AllM_ofR hval (declAxiom2SMR_of_residues hax) hbas hind)
    h c hc hty

/-! ## The three sweeps

**1. Smallest fuel.**  No statement here asserts a `denote2` success;
the annotated existence facts all sit inside `EnvS2U`'s fields, whose
uniqueness form was frozen at seal 36 precisely so that none of them
is a conclusion.

**2. Vacuity — the honest reading.**  Every theorem here is
conditional on `DeclStep2All`, which **nothing in this tree
inhabits**, and behind which sits `CheckStep2E`, which nothing
inhabits either.  So none of these statements is usable today, and
saying so is the point: the sequencing seal 39 adopted is *conditional
now, unconditional at junction closure*, and this file is what
"conditional now" looks like when written down.

Two consequences worth separating:

* the five carrier-strengthening results
  (`checkDecl_sound_R2`, the four `checkDecls*_sound_R2`) would say
  something new the moment `DeclStep2All` lands;
* the eight `no_proof_of_Empty*_R2` would not — v1 already proves
  their conclusions unconditionally.  They are a route check.

**3. Tombstones.**  A file added, none edited; `Main.lean`'s fourteen
are byte-identical and still hypothesis-free. -/

end Setlec.SetR
