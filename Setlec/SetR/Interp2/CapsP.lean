import Setlec.SetR.Annot.EnvS2P

/-!
# The structure-capability laws at `interp2` — statements (task #161,
caps tier; FROZEN by the lane lead)

`CapsOkV`'s mirror at the validated-annotation currency: the stored
families' fired η and unit-like laws, value-level, keyed exactly as
the v1 field (`Sound/Motives.lean:309`) on the stored `indInfo`, the
capability flag, the non-reserved name, and the completed family
(`EtaFamilyStored`).

Design decisions, recorded:

* **The telescope fit is `TeleFitP`, not `TeleFit2`.**  `TeleFit2`
  (`Annot/Spine2.lean`) demands every product in the graph regime
  (`v ≠ 0`), which a `Prop`-valued family's telescope violates.
  `TeleFitP` mirrors `TeleFitV` instead — memberships only, the
  peeled body read under the extended environment (the `interp2`
  analogue of `B.inst a`), no positivity anywhere.  Consumers recover
  residual memberships through `app_mem_piR`, whose `v = 0` fibre
  premise is the type reading's `AnnotValidV` — the literal tier's
  establishment move, reused (`NatEqsP.lean`'s finding: no bit
  positivity is ever needed).
* **The laws carry their readings** (`∃ TVa, …`), the `NatOpsP`
  pattern: establishment stores the instantiated type's reading at
  its own environment; preservation transfers it *forward*
  (`denoteP_cons_fresh_mono`); consumers identify it with their own
  reading by determinism.  The equality-form crossing is refutable
  at support-completing installs (the `LitStabilityP` lesson), so no
  backward transfer ever appears.
* **The fired content is value-level** (the divmod-leg lesson): `ts`,
  `x`, `y` are bare `V`s, and the fabricated η spine is
  `projSpines2`/`etaFabArgs2` — `projSpinesV`/`etaFabArgsV`
  (`Rel.lean:98/106`) with `cval`-leaves replaced by `interp2` values
  of the `acval` leaves at the same assignment.

**Establishment**: at the inductive install — `IndStepPB`'s bill (the
routed bundle already owes the whole `EnvS2PM` at an `indDecl` cons;
this file adds no census entry).  The v1 establishment path is the
capability pipeline (kernel pin → `EtaPins` → rule_fold → `ModeledOk`
law → cert+sound, `Install/EtaLawS.lean`); the P path re-runs its
defeq certificates through the claims — the run-certificate route —
when the ind tier lands.  Consumers: `StructEtaIrrelP` /
`StructUnitIrrelP` (`Step2/StuckP.lean:353/377`), discharged from the
field by the caps batch.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  IndCaps projFnName)

universe w

variable {V : Type w} [SetTheory V]

/-- **The annotated telescope fit** (`TeleFitV`'s `interp2` mirror):
each argument value inhabits its progressively-peeled domain, the
peeled body read under the extended environment.  No positivity — the
squash-regime products fit too, and consumers recover memberships
through `app_mem_piR` with the validity fibre facts. -/
inductive TeleFitP (V : Type w) [SetTheory V] :
    (Nat → V) → AVExpr → List V → V → Prop where
  | nil {ρ : Nat → V} {T : AVExpr} : TeleFitP V ρ T [] (interp2 V ρ T)
  | cons {ρ : Nat → V} {u v : Nat} {A B : AVExpr} {a : V}
      {as : List V} {rest : V} :
      a ∈ˢ interp2 V ρ A →
      TeleFitP V (cons a ρ) B as rest →
      TeleFitP V ρ (.pi u v A B) (a :: as) rest

/-- The projection spines' values: each stored projection function
applied to the type arguments and the stuck member
(`projSpinesV`'s value level). -/
noncomputable def projSpines2 (val : Name → V) (T : Name)
    (ts : List V) (b : V) (nF : Nat) : List V :=
  (List.range nF).map fun j =>
    (ts ++ [b]).foldl SetTheory.app (val (projFnName T j))

/-- The fabricated η spine's values (`etaFabArgsV`'s value level). -/
noncomputable def etaFabArgs2 (val : Name → V) (T : Name)
    (ts : List V) (b : V) (nF : Nat) : List V :=
  ts ++ projSpines2 val T ts b nF

/-- **The fired structural-η law of an η-capable stored family**
(`EtaLawV`'s mirror; see the module docstring for the shape). -/
def EtaLawP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ' : Name → Nat) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ us : List Level, us.length = cvT.levelParams.length →
  ∃ TVa : AVExpr,
    denoteP m.acval env φ' 0
      (cvT.type.instantiateLevelParams cvT.levelParams us)
      = some TVa ∧
    (∀ ρ : Nat → V, AnnotOkP V ρ TVa) ∧
    ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x : V),
      ts.length = caps.etaParams →
      TeleFitP V ρ TVa ts rest →
      x ∈ˢ ts.foldl SetTheory.app
        (interp2 V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      x = (etaFabArgs2
            (fun n => interp2 V ρ
              (m.acval n (Level.substFn φ' cvT.levelParams us)))
            T ts x caps.etaFields).foldl SetTheory.app
          (interp2 V ρ
            (m.acval caps.etaCtor
              (Level.substFn φ' cvT.levelParams us)))

/-- **The fired unit-like law of a unit-like stored family**
(`UnitLawV`'s mirror). -/
def UnitLawP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) (φ' : Name → Nat) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ us : List Level, us.length = cvT.levelParams.length →
  ∃ TVa : AVExpr,
    denoteP m.acval env φ' 0
      (cvT.type.instantiateLevelParams cvT.levelParams us)
      = some TVa ∧
    (∀ ρ : Nat → V, AnnotOkP V ρ TVa) ∧
    ∀ (ρ : Nat → V) (ts : List V) (rest : V) (x y : V),
      ts.length = caps.unitParams →
      TeleFitP V ρ TVa ts rest →
      x ∈ˢ ts.foldl SetTheory.app
        (interp2 V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      y ∈ˢ ts.foldl SetTheory.app
        (interp2 V ρ (m.acval T (Level.substFn φ' cvT.levelParams us))) →
      x = y

/-- **The stored families' capability laws at `interp2`**
(`CapsOkV`'s mirror, keyed identically; established at the inductive
install — `IndStepPB`'s bill). -/
def CapsOkP {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS2Core V env) : Prop :=
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    Setlec.reservedBasisNames.contains T = false →
    Setlec.EtaFamilyStored env T caps →
    ∀ φ' : Name → Nat, EtaLawP m φ' T cvT caps) ∧
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.unitlike = true →
    Setlec.reservedBasisNames.contains T = false →
    Setlec.EtaFamilyStored env T caps →
    ∀ φ' : Name → Nat, UnitLawP m φ' T cvT caps)

end Setlec.SetR.Interp2
