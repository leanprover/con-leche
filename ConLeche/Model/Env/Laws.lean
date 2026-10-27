module

public import ConLeche.Model.Currency
public import ConLeche.Semantics.DivModEval
public import ConLeche.Verify.ProjTele
public import ConLeche.Verify.Denote.OpenVars
public import ConLeche.Verify.EnvGuards

public section

/-!
# The environment laws (task #305)

The definitions `EnvModelM`'s fields are stated over — the `Nat`
recurrences, the `Eq` and opaque laws, the structure-capability laws,
the fired modeled-iota contract, the tower projection law — in a
module of their own so that the rules tier's inputs
(`Model/Rules/Inputs.lean`) can name them without importing
`EnvModelM`'s establishment surface.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  ReducibilityHint IndCaps RecRule)

universe w

-- `EnvModelM.lean` declares this variable EXPLICIT, for the structure's
-- sake; here it is implicit, for the residues below and
-- `teleFit_nil_inv`.  The other definitions bind their own `V`.
variable {V : Type w} [SetTheory V]

/-- **The structural-`Nat` recurrence law at the stored-term reading**
(task #161): every stored structural operation's defining
equations read under `denote` and hold as `interp` equalities at
the two-variable `Nat` context, with the level composition normalized
to the plain assignment (the heads are level-monomorphic).

Supplied as an `EnvModelM` field: established at the operation's own
install from the recorded `isDefEqCore` runs (`NatEqsRun`) through
`DefEqClaim` — the run-certificate route (`Model/NatEqs.lean`)
— and preserved across every other fresh cons.  Consumed by the
numeral-transport inductions, which close the literal rows `NatSuccRow`/`NatOpRow` of
`Model/Rules/Inputs.lean` (`Model/NatStep.lean`).  The stored type's pin
(`natOpTyPinned`, checked at the install) is kept as well: the head row
`NatOpHead` reads the operation's domains off it (task #342 L12). -/
@[expose] def NatOps {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ c ∈ ConLeche.natOpNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    ConLeche.natOpGuard env c = true ∧
    ConLeche.natOpTyPinned env c cv.type = true ∧
    ∀ eq ∈ ConLeche.natOpEquations 0 c, ∃ L R,
      denote m.acval env φ 2 eq.1 = some L ∧
      denote m.acval env φ 2 eq.2 = some R ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
        y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
        interp V (cons y (cons x ρ)) L
          = interp V (cons y (cons x ρ)) R

/-- **The pin-certified WF-recursive operations' guarded value
recurrences at the stored-term reading**: `DivModClausesV` is
valuation-generic and is fed the `acval` leaves' values.

Supplied as an `EnvModelM` field: established at the operation's own
install from the recorded certificate runs (`checkDivModCerts`'
verdict) through `InferClaim`/`DefEqClaim` — the run-certificate
route again (`Model/DivModCert.lean`) — and preserved across every
other fresh cons.  Consumed by the WF-op numeral transports.  The stored
type's pin is kept as in `NatOps`. -/
@[expose] def DivMod {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ c ∈ ConLeche.natDivModNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    ConLeche.natOpGuard env c = true ∧
    ConLeche.natOpTyPinned env c cv.type = true ∧
    ∀ (ρ : Nat → V) (x y : V),
      x ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      y ∈ˢ interp V ρ (m.acval ConLeche.natName φ) →
      DivModClausesV V (fun n => interp V ρ (m.acval n φ)) c x y

/-- **The pinned `Eq` spine's value at `interp`**, stated directly at
the three-fold application (the only form the certificate consumers
read).

**This is an environment law**, a field and not a theorem, because
the `Eq` leaf's value is fixed by the basis install (`eqValT` — the
`.eqE` former η-expanded) and by nothing else; its supplier is the
basis install (`BasisStepPB`).  See the task #161 LITERAL TIER
seal III record. -/
@[expose] def EqLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) : Prop :=
  env.find? eqName = some eqA →
  ∀ ψ : Name → Nat,
    -- the spine's **value**: the truth set of the equation
    (∀ (ρ : Nat → V) (A a b : V),
      A ∈ˢ (univ (ψ uN) : V) → a ∈ˢ A → b ∈ˢ A →
      SetTheory.app (SetTheory.app (SetTheory.app
          (interp V ρ (m.acval eqName ψ)) A) a) b = eqv a b) ∧
    -- the spine's **grading**, and that it is a proposition (the
    -- certificate frame reads exactly these)
    ∀ (ρ : Nat → V) (Aa la ra : Term),
      WellDenoted V ρ Aa → WellDenoted V ρ la → WellDenoted V ρ ra →
      interp V ρ Aa ∈ˢ (univ (ψ uN) : V) →
      interp V ρ la ∈ˢ interp V ρ Aa →
      interp V ρ ra ∈ˢ interp V ρ Aa →
      WellDenoted V ρ
          (.app (.app (.app (m.acval eqName ψ) Aa) la) ra) ∧
        interp V ρ (.app (.app (.app (m.acval eqName ψ) Aa) la) ra)
          ∈ˢ (univZero : V)

/-- **The compiler-trust opaques are the identity, at `interp`**: the
stored `Lean.reduceNat`/`Lean.reduceBool` leaf, applied to a member of
its element type's reading, *is* that member.

**This is an environment law, as `EqLaw` is**: the opaque's leaf
value is fixed by its own install (`checkReducePin`'s identity
certificate) and by nothing else, so the only possible supplier is
that install (an erasure factoring is refuted here for the same
reason as at `EqLaw`).

**Establishment**: `reduceOps_install` (`Model/ReduceOps.lean`),
at the opaque cons, from the *recorded* identity-certificate run
(`isDefEqCore μ env F 1 (.app valA (reduceCertVar c))
(reduceCertVar c) = .ok true`) through `DefEqClaim` at the
one-entry element context.  **Preservation**: `reduceOps_cons_fresh`
at every other fresh cons (the law mentions two stored leaves, so it
crosses).  **Consumer**: the `ofReduceNat`/`ofReduceBool` axiom branch
(`Model/AxiomReduce.lean`), whose innermost membership obligation is
exactly `op a = a`. -/
@[expose] def ReduceOps {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) : Prop :=
  ∀ c ∈ ConLeche.reduceOpNames, ∀ cv : ConstantVal,
    env.find? c = some (.axiomInfo cv) →
    ConstantVal.matchesPin cv (ConLeche.reduceOpCvA c) = true →
    (env.find? (ConLeche.reduceElemName c)).isSome = true ∧
    ∀ (ψ : Name → Nat) (ρ : Nat → V) (x : V),
      x ∈ˢ interp V ρ (m.acval (ConLeche.reduceElemName c) ψ) →
      SetTheory.app (interp V ρ (m.acval c ψ)) x = x

/-! ## The structure-capability laws (task #161, caps tier)

The stored families' fired η and unit-like laws at the
`denote` currency, value-level, keyed on the stored
`indInfo`, the capability flag, the non-reserved name, and the
completed family (`EtaFamilyStored`).  They live here because the
`EnvModelM` field must mention them and their preservation file
(`Model/Caps.lean`) imports `EnvModelM`.

* **The telescope fit is `TeleFit`**: memberships only, the peeled
  body read under the extended environment (the `interp` analogue of
  `B.inst a`), no positivity anywhere — a graph-regime-only fit
  (`v ≠ 0` at every Π-type) would exclude a `Prop`-valued family's
  telescope.  Consumers recover residual memberships through
  `app_mem_piR`, whose `v = 0` fibre premise is the type reading's
  grading: no regime positivity is ever needed.
* **The laws carry their readings** (`∃ TVa, …`), the `NatOps`
  pattern: establishment stores the instantiated type's reading at
  its own environment; preservation transfers it *forward*
  (`denote_cons_mono`); consumers identify it with their own
  reading by determinism.  The equality-form crossing is refutable
  at support-completing installs, so no backward transfer ever
  appears.
* **The fired content is value-level**: `ts`, `x`, `y` are bare `V`s.
  The η half is owed only for a fieldless family (`EtaFamilyStored`'s
  `etaFields = 0`), so its fabricated spine is the parameters `ts`; a
  family with fields reads its η law off its projection table's tower
  entries (`TowerEtaLaw`).

**Establishment**: at the inductive install, which re-runs its defeq
certificates through the claims.  Consumers: the structure-η and
unit-like rules' soundness (`DefEq.structEta_sound`/
`DefEq.structUnit_sound`, `Model/Rules/DefEqSound.lean`). -/

/-- **The telescope fit**: each argument value inhabits its progressively-peeled domain, the
peeled body read under the extended environment.  No positivity — the
squash-regime Π-types fit too, and consumers recover memberships
through `app_mem_piR` with the validity fibre facts. -/
inductive TeleFit (V : Type w) [SetTheory V] :
    (Nat → V) → Term → List V → V → Prop where
  | nil {ρ : Nat → V} {T : Term} : TeleFit V ρ T [] (interp V ρ T)
  | cons {ρ : Nat → V} {A B : Term} {a : V}
      {as : List V} {rest : V} :
      a ∈ˢ interp V ρ A →
      TeleFit V (cons a ρ) B as rest →
      TeleFit V ρ (.pi A B) (a :: as) rest

section
variable {V : Type w} [SetTheory V]

/-- The empty fit pins its residual (the inversion `cases` cannot do
in place, because the fit's type index is not a variable there). -/
theorem teleFit_nil_inv {ρ : Nat → V} {T : Term} {rest : V}
    (h : TeleFit V ρ T [] rest) : rest = interp V ρ T := by
  cases h; rfl

end

/-- **The η constructor's telescope coherence** (task #342 L11b): at the
use's levels `us`, a member `x` of the family `T` at parameters `ts`
fitting the former's type reading `TVa` gives a spine `fab ρ ts x`
(the parameters, then `x`'s projections) that fits the η constructor
`C`'s own type reading.  Without it the former's parameter telescope
and the constructor's are unrelated: a parameter compared only where
neither side is the point (structure η's comparison) says nothing
about a point-valued parameter, which only the constructor's telescope
pins (L11's finding 2).  Keyed on the constructor's lookup, so a stage
that has not stored it yet owes nothing. -/
@[expose] def EtaCoherent {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) (T C : Name) (lps : List Name)
    (us : List Level) (TVa : Term) (nP : Nat)
    (fab : (Nat → V) → List V → V → List V) : Prop :=
  ∀ (cvC : ConstantVal) (nPc nFc : Nat),
    env.find? C = some (.ctorInfo cvC nPc nFc) →
    ∃ TCa : Term,
      denote m.acval env φ 0
        (cvC.type.instantiateLevelParams cvC.levelParams us) = some TCa ∧
      ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x : V),
        ts.length = nP →
        TeleFit V ρ TVa ts rest →
        x ∈ˢ ts.foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ lps us))) →
        ∃ restC : V, TeleFit V ρ TCa (fab ρ ts x) restC

/-- **`EtaCoherent` crosses a change of environment** that keeps the
constructor's lookup (backwards), its type's reading (forwards), the
family's leaf and the fabricated spine. -/
theorem EtaCoherent.transport {env env₂ : Env} {m : EnvModel V env}
    {m₂ : EnvModel V env₂} {φ : Name → Nat} {T C : Name} {lps : List Name}
    {us : List Level} {TVa : Term} {nP : Nat}
    {fab fab₂ : (Nat → V) → List V → V → List V}
    (h : EtaCoherent m φ T C lps us TVa nP fab)
    (hfind : ∀ cvC nPc nFc, env₂.find? C = some (.ctorInfo cvC nPc nFc) →
      env.find? C = some (.ctorInfo cvC nPc nFc))
    (hread : ∀ (cvC : ConstantVal) (nPc nFc : Nat) (TCa : Term),
      env.find? C = some (.ctorInfo cvC nPc nFc) →
      denote m.acval env φ 0
        (cvC.type.instantiateLevelParams cvC.levelParams us) = some TCa →
      denote m₂.acval env₂ φ 0
        (cvC.type.instantiateLevelParams cvC.levelParams us) = some TCa)
    (hT : m₂.acval T (Level.substFn φ lps us) = m.acval T (Level.substFn φ lps us))
    (hfab : ∀ ρ ts x, fab₂ ρ ts x = fab ρ ts x) :
    EtaCoherent m₂ φ T C lps us TVa nP fab₂ := by
  intro cvC nPc nFc hf₂
  have hf := hfind cvC nPc nFc hf₂
  obtain ⟨TCa, hTCa, hfit⟩ := h cvC nPc nFc hf
  refine ⟨TCa, hread cvC nPc nFc TCa hf hTCa, fun ρ ts rest x hlen hft hmem => ?_⟩
  rw [hT] at hmem
  rw [hfab]
  exact hfit ρ ts rest x hlen hft hmem

/-- **The fired structural-η law of an η-capable stored family**
(see the section note for the shape), with the η constructor's
telescope coherence (`EtaCoherent`). -/
@[expose] def EtaLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ' : Name → Nat) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ us : List Level, us.length = cvT.levelParams.length →
  ∃ TVa : Term,
    denote m.acval env φ' 0
      (cvT.type.instantiateLevelParams cvT.levelParams us)
      = some TVa ∧
    (∀ ρ : Nat → V, WellDenoted V ρ TVa) ∧
    (∀ (ρ : Nat → V) (ts : List V) (rest : V) (x : V),
      ts.length = caps.etaParams →
      TeleFit V ρ TVa ts rest →
      x ∈ˢ ts.foldl SetTheory.app
        (interp V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      x = ts.foldl SetTheory.app
          (interp V ρ
            (m.acval caps.etaCtor
              (Level.substFn φ' cvT.levelParams us)))) ∧
    EtaCoherent m φ' T caps.etaCtor cvT.levelParams us TVa caps.etaParams
      (fun _ ts _ => ts)

/-- **The fired unit-like law of a unit-like stored family.** -/
@[expose] def UnitLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ' : Name → Nat) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ us : List Level, us.length = cvT.levelParams.length →
  ∃ TVa : Term,
    denote m.acval env φ' 0
      (cvT.type.instantiateLevelParams cvT.levelParams us)
      = some TVa ∧
    (∀ ρ : Nat → V, WellDenoted V ρ TVa) ∧
    ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x y : V),
      ts.length = caps.unitParams →
      TeleFit V ρ TVa ts rest →
      x ∈ˢ ts.foldl SetTheory.app
        (interp V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      y ∈ˢ ts.foldl SetTheory.app
        (interp V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      x = y

/-- **The stored families' capability laws at `interp`**
(established at the inductive install). -/
@[expose] def CapsOk {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) : Prop :=
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    ConLeche.reservedBasisNames.contains T = false →
    ConLeche.EtaFamilyStored env T caps →
    ∀ φ' : Name → Nat, EtaLaw m φ' T cvT caps) ∧
  -- The unit half carries NO `EtaFamilyStored` premise: it would make
  -- the law vacuous at a WF environment with a non-reserved
  -- unitlike-only family.
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.unitlike = true →
    ConLeche.reservedBasisNames.contains T = false →
    ∀ φ' : Name → Nat, UnitLaw m φ' T cvT caps)

/-! ## The fibres of a stored family (task #342 L7)

The real model's counterpart of the fragment's `IndFibLaw` (task #342
F1): an inductive family whose stored sort evaluates to `0` has
truth-value fibres, and one whose sort does not has **strict** fibres.
Every `Sort (n+1)` holds the truth values too (`univ` is cumulative),
so the universe does not say the second half; the inductive
constructions do (a fibre above `Prop` is a set of tagged tuples).

The stored sort is read off the type's reading: a former's type reads
as a Π-tower over its parameters and indices ending in `.sort n`, and
`n` is the stored sort at the reading's assignment (a block member's
`FormerData.read`: `.sort (resSort.eval ψ)`).

* The **field** (`EnvModelM.ind_strict`, `IndStrictOk`) is the strict
  half, per former and at the uninstantiated type, the form every
  install proves.
* The **law** (`IndFibLaw`) is both halves at a use's instantiated
  levels, the form the rules tier reads; it is derived
  (`EnvModelM.indFibLaw`): the truth-value half from the stored
  former's membership in its graded type, the strict half from the
  field. -/

/-- **A stored former's fibres above a proposition are strict**: at every
assignment where its type reads as a Π-tower ending in `.sort n` with
`n ≠ 0`, the former applied to values fitting the tower's domains is
strict (task #342 L7). -/
@[expose] def IndStrictAt {V : Type w} [SetTheory V]
    (acval : Name → (Name → Nat) → Term) (env : Env) (I : Name)
    (cv : ConstantVal) : Prop :=
  ∀ (ψ : Name → Nat) (ab : List Term) (n : Nat),
    denote acval env ψ 0 cv.type = some (mkPisAV ab (.sort n)) → n ≠ 0 →
    ∀ (ρ : Nat → V) (vs : List V), SpineFit ρ ab vs →
      Strict (vs.foldl SetTheory.app (interp V ρ (acval I ψ)))

/-- `IndStrictAt` at a cons's head, if it is a former. -/
@[expose] def IndStrictHead {V : Type w} [SetTheory V]
    (acval : Name → (Name → Nat) → Term) (env : Env) (c₀ : ConstantInfo) : Prop :=
  ∀ (cv : ConstantVal) (caps : IndCaps), c₀ = .indInfo cv caps →
    IndStrictAt (V := V) acval env c₀.name cv

/-- **Every stored former's fibres above a proposition are strict**
(the `EnvModelM` field; established at the formers' installs). -/
@[expose] def IndStrictOk {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) : Prop :=
  ∀ (I : Name) (cv : ConstantVal) (caps : IndCaps),
    env.find? I = some (.indInfo cv caps) → IndStrictAt (V := V) m.acval env I cv

/-- **The fibre law of the stored families** (task #342 L7; the
fragment's `IndFibLaw`, task #342 F1): a stored former `I` at the
use's levels `us`, whose instantiated type reads as a Π-tower ending
in `.sort n`, applied to values fitting the tower's domains, is a
truth value where `n = 0` and strict where `n ≠ 0` (`Fib`).  At any
depth `d`: the type is closed. -/
@[expose] def IndFibLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (I : Name) (cv : ConstantVal) (caps : IndCaps) (us : List Level),
    env.find? I = some (.indInfo cv caps) → us.length = cv.levelParams.length →
    ∀ (ab : List Term) (n : Nat),
      denote m.acval env φ d (cv.type.instantiateLevelParams cv.levelParams us)
        = some (mkPisAV ab (.sort n)) →
      ∀ (ρ : Nat → V) (vs : List V), SpineFit ρ ab vs →
        Fib (decide (n = 0))
          (vs.foldl SetTheory.app
            (interp V ρ (m.acval I (Level.substFn φ cv.levelParams us))))

/-- A Π-tower over a sort determines its domains and its sort. -/
theorem mkPisAV_sort_inj :
    ∀ {ab ab' : List Term} {n n' : Nat},
      mkPisAV ab (.sort n) = mkPisAV ab' (.sort n') →
        ab = ab' ∧ n = n'
  | [], [], _, _, h => ⟨rfl, Term.sort.inj h⟩
  | [], _ :: _, _, _, h => nomatch h
  | _ :: _, [], _, _, h => nomatch h
  | d :: ab, d' :: ab', _, _, h => by
    simp only [mkPisAV, Term.pi.injEq] at h
    obtain ⟨h1, h⟩ := h
    obtain ⟨h2, rfl⟩ := mkPisAV_sort_inj h
    exact ⟨by simp [h1, h2], rfl⟩

/-- **The strict fibres of a former, at its cons** — from its one type
reading: at every assignment the stored type reads as `mkPisAV (ab ψ)
(.sort (s ψ))`, and where `s ψ ≠ 0` the leaf applied along a fitting
spine is strict. -/
theorem indStrictHead_of {acval : Name → (Name → Nat) → Term} {env : Env}
    {cv : ConstantVal} {caps : IndCaps}
    {ab : (Name → Nat) → List Term} {s : (Name → Nat) → Nat}
    (hread : ∀ ψ, denote acval env ψ 0 cv.type = some (mkPisAV (ab ψ) (.sort (s ψ))))
    (h : ∀ ψ, s ψ ≠ 0 → ∀ (ρ : Nat → V) (vs : List V), SpineFit ρ (ab ψ) vs →
      Strict (vs.foldl SetTheory.app (interp V ρ (acval cv.name ψ)))) :
    IndStrictHead (V := V) acval env (.indInfo cv caps) := by
  intro cv' caps' hc ψ ab' n hr hn ρ vs hsp
  obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj hc
  obtain ⟨hab, rfl⟩ := mkPisAV_sort_inj (Option.some.inj ((hread ψ).symm.trans hr))
  exact h ψ hn ρ vs (hab ▸ hsp)

/-! ## The fired modeled-iota contract (task #161, iota tier)

The stored recursors' fired rules, at the stored terms' reading:

* **The law is `Term`-indexed**: the truthfulness transport is
  inherently about the applied reduct's *reading* (the ι step must
  hand the whnf loop a graded reading), and `WellDenoted` is
  `Term`-indexed.  A value-level law, as for the caps, would not
  carry that conjunct.
* **`TeleFitPA` is substitution-peeling** — `B.inst a` at the
  argument's *reading*, one ambient environment — so its residual
  agrees syntactically with the substituted readings the certificate's
  `defEqList` runs compare.  Substitution-peeling is available here
  because the arguments are readings (the caps' `TeleFit` has bare
  values and cannot substitute): `denote_beta` gives the residual
  identity directly, and the index pin decomposes the residual at the
  ambient environment.
* **The law takes no parameter comparison.**  Where the fired
  constructor application is not the point, the major's membership in
  the family at the comparands ties its fields; where it is the point,
  the index pin is the only premise (`RecRuleExtra`'s (U) derives it
  from the step's case-3 comparisons).  It does take the level
  equation; the ι step has it at case 3, and at case 2 reads the fired
  application at the comparand levels first (`RecRuleExtra`'s (T)).  The `.nested` pins' grading
  clause quantifies the pin's own open reading (`denote` at depth
  `rP`), at the reading substituted along the argument prefix —
  `Term.instRevChain`.
* **The fired equality is present**, and the transport clause grades
  the applied reduct.
* The law **carries the RHS reading** (`∃ Ra`), with the bare-`R`
  grading unconditional (the `NatOps`/caps carried-reading pattern —
  establishment stores, preservation transfers forward, consumers
  identify by determinism).

The statements live here because `RecRules` is an `EnvModelM` field.

**Establishment**: the inductive install, where the flagged new
mathematics lives (a `Prop`-valued motive's minors at the squash
regime).  **Consumer**: the ι rule's soundness (`Red.iota_sound`,
`Model/Rules/IotaSound.lean`). -/

/-- **The telescope fit of readings** (substitution-peeling): each argument reading inhabits its
progressively-substituted domain, one ambient environment, the
residual a `Term` at that environment. -/
inductive TeleFitPA (V : Type w) [SetTheory V] (ρ : Nat → V) :
    Term → List Term → Term → Prop where
  | nil {T : Term} : TeleFitPA V ρ T [] T
  | cons {A B rest : Term} {a : Term}
      {as : List Term} :
      interp V ρ a ∈ˢ interp V ρ A →
      TeleFitPA V ρ (B.inst a) as rest →
      TeleFitPA V ρ (.pi A B) (a :: as) rest

/-- A fit's prefix fits, to some intermediate residual. -/
theorem TeleFitPA.take {V : Type w} [SetTheory V] {ρ : Nat → V} :
    ∀ {T rest : Term} {as : List Term}, TeleFitPA V ρ T as rest →
      ∀ n : Nat, ∃ mid, TeleFitPA V ρ T (as.take n) mid := by
  intro T rest as h
  induction h with
  | @nil T' =>
    intro n
    refine ⟨T', ?_⟩
    rw [List.take_nil]
    exact TeleFitPA.nil
  | @cons A B rest' a as' hmem htail ih =>
    intro n
    cases n with
    | zero => exact ⟨_, TeleFitPA.nil⟩
    | succ n =>
      obtain ⟨mid, hm⟩ := ih n
      exact ⟨mid, TeleFitPA.cons hmem hm⟩

/-- The reverse-opening substitution chain of readings (outermost
argument consumed first, each at cut `0`, lifted past the arguments
still to come). -/
@[expose] def _root_.ConLeche.Term.Term.instRevChain :
    List Term → Term → Term
  | [], X => X
  | v :: vs, X =>
    instRevChain vs (X.inst (v.liftN vs.length) 0)

/-- **The constructor residual's index pin**: the residual decomposes as a spine
whose trailing arguments agree with the recursor's index arguments,
all at the ambient environment. -/
@[expose] def IotaIndexPin {V : Type w} [SetTheory V] (ρ : Nat → V)
    (restC : Term) (cnP mI rP : Nat) (xs : List Term) : Prop :=
  ∃ (Ha : Term) (cargsa : List Term),
    restC = Term.mkAppN Ha cargsa ∧
    (mI = rP ∨ cargsa.length = cnP + (mI - rP)) ∧
    ∀ i, i < mI - rP →
      interp V ρ (cargsa.getD (cnP + i) default)
        = interp V ρ (xs.getD (rP + i) default)

/-- **The index pin, compared where neither side is the point** (task
#342 L10): what the ι step's index comparison gives under the
conditional claims. -/
@[expose] def IotaIndexPinC {V : Type w} [SetTheory V] (ρ : Nat → V)
    (restC : Term) (cnP mI rP : Nat) (xs : List Term) : Prop :=
  ∃ (Ha : Term) (cargsa : List Term),
    restC = Term.mkAppN Ha cargsa ∧
    (mI = rP ∨ cargsa.length = cnP + (mI - rP)) ∧
    ∀ i, i < mI - rP →
      interp V ρ (cargsa.getD (cnP + i) default) ≠ pt →
      interp V ρ (xs.getD (rP + i) default) ≠ pt →
      interp V ρ (cargsa.getD (cnP + i) default)
        = interp V ρ (xs.getD (rP + i) default)

/-- **The ι case split's environment facts, one rule**.
`RecRuleLaw`'s main clause takes the levels, parameters and index
comparisons as equations; under the conditional claims the ι step has
them only where neither side is the point, and at a K rule or a family
that is never `Prop` at the comparand levels it runs no check of the
constructor application at all.  What the step consumes instead, at the
recursor's levels:

* **K** (`RecRule.k`): the rule's law at the recursor's own
  parameters, for any major value in the major's domain (the
  fragment's `RecRuleLawK`: inversion of the family's least
  fixed point) — the reduct, the minor, does not mention the major;
* **the constructor's arity**: its stored type binds the spine
  syntactically, so a graded application of it that is not the point
  fits its telescope;
* **(S) case 2**: where the family is never `Prop` at the comparand
  levels (`iotaCtorNeverProp`, the checker's test), the recursor's major
  domain holds no point;
* **(T) case 2, the constructor's levels**: there a fired application
  that is not the point, at the constructor's own levels and spine, is
  also an application of the constructor at the comparand levels, to a
  graded spine with the same fields that fits its telescope there —
  the major's membership in the family at the comparands ties the
  injection's fields (the same argument as for the parameters), so the
  main law applies at the comparand levels;
* **(P) the slot at the point**: where the major domain holds the
  point, every fitting constructor application is the point (the
  family is `Prop` there; the fragment's slot law);
* **(U) coherence**: at a fired spine where the constructor application
  is the point (case 3, where the step compares the levels and
  parameters with the rule's comparands and the indices), the
  conditional index comparison is an equation (read off the
  parameters' conditional comparison).

(P) and (U) are read only at case 3, so they take the level equation. -/
@[expose] def RecRuleExtra {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat)
    (n : Name) (cv : ConstantVal) (mI rP : Nat) (rl : RecRule) : Prop :=
  ∀ us : List Level, us.length = cv.levelParams.length →
    ∀ TVa : Term,
      denote m.acval env φ 0
        (cv.type.instantiateLevelParams cv.levelParams us) = some TVa →
    -- K
    (RecRule.k rl = true → RecRule.nfields rl = 0 ∧
      ∀ Ra : Term,
        denote m.acval env φ 0
          ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us) = some Ra →
      ∀ (ρ : Nat → V) (xs : List Term) (a restR : Term),
        xs.length = mI →
        TeleFitPA V ρ TVa (xs ++ [a]) restR →
        (∀ x ∈ xs, WellDenoted V ρ x) →
        interp V ρ (Term.mkAppN
            (m.acval n (Level.substFn φ cv.levelParams us)) (xs ++ [a]))
          = interp V ρ (Term.mkAppN Ra (xs.take rP)) ∧
        ((∀ x ∈ xs, WellDenoted V ρ x) →
          WellDenoted V ρ (Term.mkAppN Ra (xs.take rP)))) ∧
    ∀ (cvj : ConstantVal) (cnP cnF : Nat),
      env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
    -- the constructor's arity
    (cvj.type.stripPis (RecRule.ctorParams rl + RecRule.nfields rl)).isSome = true ∧
    (RecRule.k rl = false →
    -- (S)
    (ConLeche.iotaCtorNeverProp env.find? cvj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1 = true →
      ∀ (ρ : Nat → V) (xs : List Term) (a restR : Term),
        xs.length = mI → TeleFitPA V ρ TVa (xs ++ [a]) restR →
        interp V ρ a ≠ pt) ∧
    -- (T)
    (ConLeche.iotaCtorNeverProp env.find? cvj
        (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1 = true →
      ∀ (usj : List Level), usj.length = cvj.levelParams.length →
      ∀ TVja : Term,
        denote m.acval env φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
      ∀ (ρ : Nat → V) (xs ys : List Term) (restR restC : Term),
        xs.length = mI →
        ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
        TeleFitPA V ρ TVa
          (xs ++ [Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        TeleFitPA V ρ TVja ys restC →
        (∀ x ∈ xs, WellDenoted V ρ x) → (∀ y ∈ ys, WellDenoted V ρ y) →
        interp V ρ (Term.mkAppN
          (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) ≠ pt →
        ∃ (usj' : List Level) (ys' : List Term) (TVja' restC' : Term),
          usj'.length = cvj.levelParams.length ∧
          Level.substFn φ cvj.levelParams usj'
            = Level.substFn φ cvj.levelParams
                (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1 ∧
          denote m.acval env φ 0
            (cvj.type.instantiateLevelParams cvj.levelParams usj') = some TVja' ∧
          ys'.length = ys.length ∧
          ys'.drop (RecRule.ctorParams rl) = ys.drop (RecRule.ctorParams rl) ∧
          (∀ y ∈ ys', WellDenoted V ρ y) ∧
          TeleFitPA V ρ TVja' ys' restC' ∧
          interp V ρ (Term.mkAppN
              (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj')) ys')
            = interp V ρ (Term.mkAppN
              (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys)) ∧
    ∀ (usj : List Level), usj.length = cvj.levelParams.length →
      Level.substFn φ cvj.levelParams usj
        = Level.substFn φ cvj.levelParams
            (ConLeche.recFireComparands rl cv.levelParams us cvj.levelParams [] rP).1 →
    ∀ TVja : Term,
      denote m.acval env φ 0
        (cvj.type.instantiateLevelParams cvj.levelParams usj) = some TVja →
    -- (P)
    (∀ (ρ : Nat → V) (xs : List Term) (a restR : Term),
        xs.length = mI → TeleFitPA V ρ TVa (xs ++ [a]) restR →
        interp V ρ a = pt →
      ∀ (ys : List Term) (restC : Term), TeleFitPA V ρ TVja ys restC →
        ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
        (∀ y ∈ ys, WellDenoted V ρ y) →
        interp V ρ (Term.mkAppN
          (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt) ∧
    -- (U)
    (∀ (ρ : Nat → V) (xs ys : List Term) (restR restC : Term),
        xs.length = mI →
        ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
        TeleFitPA V ρ TVa
          (xs ++ [Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        TeleFitPA V ρ TVja ys restC →
        (∀ x ∈ xs, WellDenoted V ρ x) → (∀ y ∈ ys, WellDenoted V ρ y) →
        (RecRule.fire rl = .plain →
          interp V ρ (Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          ∀ i, i < RecRule.ctorParams rl → i < mI →
            interp V ρ (ys.getD i default) ≠ pt → interp V ρ (xs.getD i default) ≠ pt →
            interp V ρ (ys.getD i default) = interp V ρ (xs.getD i default)) →
        (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
          interp V ρ (Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          ∀ i, i < RecRule.ctorParams rl →
          ∀ vpa : Term,
            denote m.acval env φ rP
              (ConLeche.Verify.openRev 0 rP
                ((pins.getD i default).instantiateLevelParams
                  cv.levelParams us)) = some vpa →
            interp V ρ (ys.getD i default) ≠ pt →
            interp V ρ (Term.instRevChain (xs.take rP) vpa) ≠ pt →
            interp V ρ (ys.getD i default)
              = interp V ρ (Term.instRevChain (xs.take rP) vpa)) →
        (interp V ρ (Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          IotaIndexPinC (V := V) ρ restC (RecRule.ctorParams rl) mI rP xs) →
        interp V ρ (Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          IotaIndexPin (V := V) ρ restC (RecRule.ctorParams rl) mI rP xs))

/-- **One rule's fired modeled-iota contract at `interp`** (see the
section note). -/
@[expose] def RecRuleLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat)
    (n : Name) (cv : ConstantVal) (mI rP : Nat) (rl : RecRule) :
    Prop :=
  rP ≤ mI ∧
  (∀ us : List Level, us.length = cv.levelParams.length →
    ∃ Ra : Term,
      denote m.acval env φ 0
        ((RecRule.rhs rl).instantiateLevelParams cv.levelParams us)
        = some Ra ∧
      (∀ ρ : Nat → V, WellDenoted V ρ Ra) ∧
      -- The nested pins' open readings are carried with a
      -- CONTEXT-GUARDED chain grading (an unconditional `∀ ρ` form is
      -- refutable: the checker's certificate is about the pins
      -- instantiated at the public frame, and converts only
      -- context-guarded).  The grading is stated of the chained term
      -- at the chain's own environment: `TeleFitPA` is that
      -- environment's `Sat` in closed form.  The consumer reads it to
      -- run the case-3 pin comparison's claim (`RecRuleExtra`'s (U)).
      (∀ lvls pins, RecRule.fire rl = .nested lvls pins →
        ∀ i, i < RecRule.ctorParams rl →
        ∃ vpa : Term,
          denote m.acval env φ rP
            (ConLeche.Verify.openRev 0 rP
              ((pins.getD i default).instantiateLevelParams
                cv.levelParams us)) = some vpa ∧
          ∀ (ρ : Nat → V) (zs : List Term) (TVa restR : Term),
            zs.length = rP →
            (∀ z ∈ zs, WellDenoted V ρ z) →
            denote m.acval env φ 0
              (cv.type.instantiateLevelParams cv.levelParams us)
              = some TVa →
            TeleFitPA V ρ TVa zs restR →
            WellDenoted V ρ
              (Term.instRevChain zs vpa)) ∧
      ∀ (cvj : ConstantVal) (cnP cnF : Nat),
        env.find? (RecRule.ctor rl) = some (.ctorInfo cvj cnP cnF) →
      ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List Term)
        (TVa TVja restR restC : Term),
        xs.length = mI →
        ys.length = RecRule.ctorParams rl + RecRule.nfields rl →
        usj.length = cvj.levelParams.length →
        Level.substFn φ cvj.levelParams usj
          = Level.substFn φ cvj.levelParams
              (ConLeche.recFireComparands rl cv.levelParams us
                cvj.levelParams [] rP).1 →
        -- the fired spine is graded (task #342 S5b: the constructor's own
        -- parameters are not compared outside case 3; its application is
        -- read at them, `genOutCtorOwn`)
        (∀ y ∈ ys, WellDenoted V ρ y) →
        -- the index pin, owed only where the fired constructor application
        -- is the point (task #342 L10: a family never `Prop` at the
        -- instance fires with no index comparison; the law reads the pin
        -- only at a `Prop` valuation)
        (interp V ρ (Term.mkAppN
            (m.acval (RecRule.ctor rl) (Level.substFn φ cvj.levelParams usj)) ys) = pt →
          IotaIndexPin (V := V) ρ restC (RecRule.ctorParams rl) mI rP xs) →
        denote m.acval env φ 0
          (cv.type.instantiateLevelParams cv.levelParams us)
          = some TVa →
        denote m.acval env φ 0
          (cvj.type.instantiateLevelParams cvj.levelParams usj)
          = some TVja →
        TeleFitPA V ρ TVa
          (xs ++ [Term.mkAppN
            (m.acval (RecRule.ctor rl)
              (Level.substFn φ cvj.levelParams usj)) ys]) restR →
        TeleFitPA V ρ TVja ys restC →
        interp V ρ
            (Term.mkAppN
              (m.acval n (Level.substFn φ cv.levelParams us))
              (xs ++ [Term.mkAppN
                (m.acval (RecRule.ctor rl)
                  (Level.substFn φ cvj.levelParams usj)) ys]))
          = interp V ρ
              (Term.mkAppN Ra
                (xs.take rP ++ ys.drop (RecRule.ctorParams rl))) ∧
        ((∀ a ∈ xs, WellDenoted V ρ a) → (∀ b ∈ ys, WellDenoted V ρ b) →
          WellDenoted V ρ
            (Term.mkAppN Ra
              (xs.take rP ++ ys.drop (RecRule.ctorParams rl)))))
  ∧ RecRuleExtra m φ n cv mI rP rl

/-- The fired modeled-iota contract, keyed on every stored recursor. -/
@[expose] def RecRules {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat)
    (rules : List RecRule),
    env.find? n = some (.recInfo cv mI rP rules) →
    ∀ rl ∈ rules, RecRuleLaw m φ n cv mI rP rl

/-! ## The tower projection law (task #175 wiring, W5)

A projection-table entry (the direct-structure install's native
entries — task #175 tower-flag: the only ones) is typed by the checker
generically — the stored `ty` peeled along the parameters and the
subject (`inferBody`'s tower branch) — and reduced by the structural
rule `proj_i (ctor p⃗ x⃗) ↦ x_i`; the reading is the uniform
`projNV (i + 1)` (`denote`'s tower branch: behind the tag).  The P `.proj` rows therefore
need, per stored tower entry, exactly two semantic facts about the
environment: the **typing law** (the projection of a member of the
family lands in the peeled entry type's reading, graded) and the
**iota law** (the projection of a certified constructor spine is the
selected field's reading).  Both are **environment laws** in the sense
of `caps_ok`/`rec_rules` — fixed by the direct install and by nothing
else — so they are a field of `EnvModelM`, established at the install and
transported across every other cons
(`towerOk_cons_fresh`, `Model/RecRulesCons.lean`).

**Why the typing law is stated over a syntactic peel** (`peelPis`)
rather than a `TeleFitPA` fit: the `.proj` infer row holds the
subject's *reduced type* as a graded reading (`WellDenoted` of the family
application) and the subject's membership in it — never a certified
parameter spine, since the family application is a *type* the run
produced, not an application it checked.  Building a fit from the
grading alone would need the leaf's λ-domains pinned to the type
reading's Π-domains at every row; the law takes the grading and the
membership as its premises instead, and the install discharges the
pinning once.  The residual is then the *syntactic* peel of the
entry-type reading along the readings (`denote_instPisAt_peel`,
the fit-free mirror of `TeleFitPA.peelPis`), which the row computes
from the checker's own `instPisAt` run.

The iota law takes the constructor application's grading alone (see
its clause). -/

/-- The syntactic Π-peel along a list of readings: the fit's residual
without the memberships (`TeleFitPA`'s spine, data only). -/
@[expose] def _root_.ConLeche.Term.Term.peelPis : Term → List Term → Option Term
  | T, [] => some T
  | .pi _ B, a :: as => peelPis (B.inst a) as
  | _, _ :: _ => none

/-- A fit's residual is the peel's. -/
theorem TeleFitPA.peelPis {V : Type w} [SetTheory V] {ρ : Nat → V} :
    ∀ {T rest : Term} {as : List Term}, TeleFitPA V ρ T as rest →
      Term.peelPis T as = some rest := by
  intro T rest as h
  induction h with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- **The structural-η law of a tower-backed family** (task #175 W4c;
`EtaLaw`'s twin at the tower kind, keyed on the entry): a member of
the family instance is the constructor at the parameters and the tower
readings (`projS`) of its own projections — the value-level content of
the η certificate's `.proj T j b` fabrication (`etaProjs`).  Keyed on
the entry so that the direct install alone answers it; the η row reads it through slot `0` of
an all-tower family. -/
@[expose] def TowerEtaLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) (T : Name)
    (entry : ProjEntry) : Prop :=
  ∀ (cvT : ConstantVal) (capsT : IndCaps),
    env.find? T = some (.indInfo cvT capsT) →
    ∀ us : List Level, us.length = entry.levelParams.length →
    ∃ TVa : Term,
      denote m.acval env φ 0
        (cvT.type.instantiateLevelParams cvT.levelParams us) = some TVa ∧
      (∀ ρ : Nat → V, WellDenoted V ρ TVa) ∧
      (∀ (ρ : Nat → V) (ts : List V) (rest : V) (x : V),
        ts.length = entry.numParams →
        TeleFit V ρ TVa ts rest →
        x ∈ˢ ts.foldl SetTheory.app
          (interp V ρ (m.acval T (Level.substFn φ entry.levelParams us))) →
        x = (ts ++ (List.range entry.numFields).map fun j =>
              ConLeche.SetTheory.Tower.projS (j + 1) x).foldl SetTheory.app
            (interp V ρ
              (m.acval entry.ctor (Level.substFn φ entry.levelParams us)))) ∧
      (capsT.eta = true →
        EtaCoherent m φ T entry.ctor entry.levelParams us TVa entry.numParams
          (fun _ ts x => ts ++ (List.range entry.numFields).map fun j =>
            ConLeche.SetTheory.Tower.projS (j + 1) x))

/-- **The `Prop` guard at a use's valuation** (task #175 W4c/O4): if
the structure is a proposition there, so is the field's guard level.
The typing and iota laws of a tower entry hold under it — a data
field of a `Prop`-declared structure has no projection law (its value
is not the point).  Consumers discharge it from the kernel's syntactic
guard (`inferTypeCore`'s tower branch, `ProjEntry.fireOk`) through
`towerGuardAt_of`. -/
@[expose] def TowerGuardAt (φ : Name → Nat) (entry : ProjEntry) (us : List Level) :
    Prop :=
  Level.eval (Level.substFn φ entry.levelParams us) entry.structSort = 0 →
    Level.eval (Level.substFn φ entry.levelParams us) entry.fieldSort = 0

/-- **The O5 conjunct**: a non-`Prop` family's guard level is bounded
by its result sort at every valuation (the field sorts are checked
`≤` the result sort, `checkStructFieldSortsI`), so the guard holds
wherever the structure happens to be a proposition. -/
@[expose] def TowerO5 (entry : ProjEntry) : Prop :=
  (Level.isEquiv entry.structSort .zero == some true) = false →
    ∀ ψ : Name → Nat,
      Level.eval ψ entry.structSort = 0 → Level.eval ψ entry.fieldSort = 0

/-- The guard at a valuation, from the kernel's syntactic guard and O5. -/
theorem towerGuardAt_of {entry : ProjEntry} {us : List Level} {φ : Name → Nat}
    (hO5 : TowerO5 entry)
    (hg : (Level.isEquiv entry.structSort .zero == some true) = true →
      (Level.isEquiv (Level.subst entry.levelParams us entry.fieldSort) .zero
        == some true) = true) :
    TowerGuardAt φ entry us := by
  intro hs
  by_cases hp : (Level.isEquiv entry.structSort .zero == some true) = true
  · have h1 := Level.isEquiv_sound (beq_iff_eq.mp (hg hp)) φ
    rw [Level.eval_subst] at h1
    simpa [Level.eval] using h1
  · exact hO5 (by simpa using hp) _ hs

/-- **The guard at a valuation, from the fire guard** (task #175 W6):
`whnfCore`'s tower fire (`ProjEntry.fireOk`) is the tower infer
branch's own guard — a `Prop`-declared family fires only where the
field's guard level is a proposition, any other family unconditionally
— so with O5 it yields `TowerGuardAt` exactly as the infer branch
does.  The squash regime is justified by the certified spine's fit,
see `TowerEntryLaw`'s clause (B). -/
theorem towerGuardAt_of_fireOk {entry : ProjEntry} {us : List Level}
    {φ : Name → Nat} (hO5 : TowerO5 entry)
    (hfire : entry.fireOk us = true) : TowerGuardAt φ entry us := by
  unfold ProjEntry.fireOk at hfire
  refine towerGuardAt_of hO5 (fun hp => ?_)
  rw [hp] at hfire
  simpa using hfire

/-- **One tower-backed entry's projection law** (see the section
docstring): the entry's stored data agrees with the stored former and
constructor (whose η capability is the entry's at a non-`Prop` family
— task #175 W4c/O4), the O5 bound, and at every level instantiation
the typing law and the iota law hold under the `Prop` guard at the
entry's own body reading and the constructor's, and the family's
structural-η law holds (clause (C), `TowerEtaLaw`).

Task #175 S1: the entry stores a *body* scoped at the parameters and
the subject, not a type; the typing law is stated over the reading
of `projTele (nP + 1) body` — the body under `nP + 1` dummy binders
(`ConLeche/Verify/ProjTele.lean`) — whose `instPisAt` peel along the
parameters and the subject is exactly the checker's one
`instantiateList` (`ProjEntry.typeAt`, `instPisAt_typeAt`).  The
dummy binders carry the reading only; the law never reads them. -/
@[expose] def TowerEntryLaw {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat)
    (T : Name) (i : Nat) (entry : ProjEntry) : Prop :=
  entry.structName = T ∧ entry.idx = i ∧
  i < entry.numFields ∧
  (∃ (cvT : ConstantVal) (capsT : IndCaps),
    env.find? T = some (.indInfo cvT capsT) ∧
    cvT.levelParams = entry.levelParams ∧
    -- the η record, IF the family claims η (task #210 Part A: a
    -- recursive structure-like stores a table but claims no η —
    -- official's `is_structure_like` has `!is_rec`): the family is
    -- not a proposition, and the record names this table's shape
    (capsT.eta = true →
      (Level.isEquiv entry.structSort .zero == some true) = false ∧
      capsT.etaCtor = entry.ctor ∧
      capsT.etaParams = entry.numParams ∧
      capsT.etaFields = entry.numFields)) ∧
  TowerO5 entry ∧
  ∃ cvC : ConstantVal,
    env.find? entry.ctor
      = some (.ctorInfo cvC entry.numParams entry.numFields) ∧
    cvC.levelParams = entry.levelParams ∧
    (∀ us : List Level, us.length = entry.levelParams.length →
      -- (A) the typing law
      (∃ Ta : Term,
        denote m.acval env φ 0
          (ConLeche.projTele (entry.numParams + 1)
            (entry.body.instantiateLevelParams entry.levelParams us)) = some Ta ∧
        (TowerGuardAt φ entry us →
        ∀ (ρ : Nat → V) (vs : List Term) (x rest : Term),
          vs.length = entry.numParams →
          WellDenoted V ρ (Term.mkAppN
            (m.acval T (Level.substFn φ entry.levelParams us)) vs) →
          -- the subject's type is not the point (a type, at the caller)
          interp V ρ (Term.mkAppN
            (m.acval T (Level.substFn φ entry.levelParams us)) vs) ≠ pt →
          WellDenoted V ρ x →
          interp V ρ x ∈ˢ interp V ρ (Term.mkAppN
            (m.acval T (Level.substFn φ entry.levelParams us)) vs) →
          Term.peelPis Ta (vs ++ [x]) = some rest →
          WellDenoted V ρ (projNV (i + 1) x) ∧ WellDenotedTy V ρ rest ∧
            interp V ρ (projNV (i + 1) x) ∈ˢ interp V ρ rest)) ∧
      -- (B) the iota law: the projection of a *graded* constructor
      -- application is the selected field, at every valuation under
      -- the guard (task #175 W6).  Two premises: the application's
      -- grading (its slot chain), and the spine's fit against the
      -- constructor's own type reading (`projCert`'s arity check,
      -- `teleArity_sound`), which places the selected field in its
      -- domain where the application is the point.
      (∃ TCa : Term,
        denote m.acval env φ 0
          (cvC.type.instantiateLevelParams cvC.levelParams us) = some TCa ∧
        (TowerGuardAt φ entry us →
        ∀ (ρ : Nat → V) (ys : List Term) (rest : V),
        ys.length = entry.numParams + entry.numFields →
        WellDenoted V ρ (Term.mkAppN
          (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) ys) →
        TeleFit V ρ TCa (ys.map (interp V ρ)) rest →
        interp V ρ (projNV (i + 1) (Term.mkAppN
            (m.acval entry.ctor (Level.substFn φ entry.levelParams us)) ys))
          = interp V ρ (ys.getD (entry.numParams + i) default)))) ∧
    -- (C) the structural-η law (task #175 W4c)
    TowerEtaLaw m φ T entry

/-- **The tower projection law, keyed on every stored entry**
(`RecRules`'s sibling).  Task #175 tower-flag: every stored table is
a real one, so the law is uniform — no flag premise. -/
@[expose] def TowerOk {V : Type w} [SetTheory V] {env : Env}
    (m : EnvModel V env) (φ : Name → Nat) : Prop :=
  ∀ (T : Name) (i : Nat) (entry : ProjEntry),
    env.findProj? T i = some entry →
    TowerEntryLaw m φ T i entry

/-! ## The install-tier residues -/

/-- **The `const` clause's residue, P currency**: a stored constant's
leaf inhabits its type's reading, a graded type. -/
@[expose] def ConstType {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) : Prop :=
  ∀ (d : Nat) (n : Name) (ci : ConLeche.ConstantInfo) (us : List Level),
    env.find? n = some ci →
    us.length = ci.toConstantVal.levelParams.length →
    ∃ ta,
      denote m.acval env φ d
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some ta ∧
      (∀ ρ : Nat → V, WellDenotedTy V ρ ta) ∧
      ∀ ρ : Nat → V,
        interp V ρ (m.acval n
            (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp V ρ ta

/-- **The `Nat`-literal clause's residue, over the core**: the zero's
membership and the successor's, at the leaf valuation's own
`Nat` leaf, which is a type. -/
@[expose] def NatHeads {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) : Prop :=
  ConLeche.natLitSupported env = true →
  ∀ ρ : Nat → V,
    interp V ρ (m.acval natZeroName (Level.substFn φ [] []))
      ∈ˢ interp V ρ (m.acval natName (Level.substFn φ [] [])) ∧
    interp V ρ (m.acval natSuccName (Level.substFn φ [] []))
      ∈ˢ piR 1 (interp V ρ (m.acval natName (Level.substFn φ [] [])))
        (fun _ => interp V ρ
          (m.acval natName (Level.substFn φ [] []))) ∧
    IsTy (interp V ρ (m.acval natName (Level.substFn φ [] [])))

/-- **A definition's leaf against its value's reading**: the reading
itself, or — for a definition of a proposition — the canonical proof
`.prf`, where the reading is a graded proof at every valuation.  The
second arm is what makes every proof's leaf the same term, so that two
proofs of one statement in two modules are one constant of the modular
theorem's world (`ConLeche/Modular.lean`). -/
@[expose] def LeafReads (V : Type w) [SetTheory V] (leaf t : Term) : Prop :=
  t = leaf ∨ (leaf = .prf ∧ ∀ ρ : Nat → V, WellDenoted V ρ t ∧ interp V ρ t = pt)

/-- **The unfolding supplier the P-tier delta exit consumes**: a stored
definition's value reads, at every level assignment, and the reading
is the constant's own leaf or, for a proof, interprets as the leaf
does (`LeafReads`).  Definitions only: a theorem is opaque to
reduction (`unfoldDefinition` has no `thmInfo` arm), so the invariant
keeps no equation between a theorem's value and its leaf — the leaf is
an inhabitant of the statement, and that is all the install
establishes.

The install tier discharges it. -/
@[expose] def AcvalDefnInst {env : Env} (m : EnvModel V env) : Prop :=
  ∀ (ψ : Name → Nat) (cv : ConstantVal) (value : Expr),
    (∃ hint : ReducibilityHint,
      ConstantInfo.defnInfo cv value hint ∈ env.consts) →
    ∃ t, denote m.acval env ψ 0 value = some t ∧ LeafReads V (m.acval cv.name ψ) t

end ConLeche.Model
