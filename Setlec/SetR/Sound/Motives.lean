import Setlec.SetR.Rel
import Setlec.SetR.AnnotOkV
import Setlec.Verify.Denote.Pinned
import Setlec.Verify.EnvGuards

/-!
# The soundness motives and the environment-hypothesis bundle (task #148, T4)

The five motives of the mutual soundness induction, per the T4
architecture record in `Setlec/SetR/DESIGN.md` (the graded design that
made repair A free):

* the equality/membership lane is unconditional under `Sat` — no
  subject-`AnnotOkV` hypotheses anywhere, which is what closes
  `DefEq.symm`/`DefEq.trans` and the binder congruences;
* `Infer`-sound concludes the *subject's* `AnnotOkV` (the design's
  type-side conjunct is dropped — consumer check in the record);
* `Red`-sound carries the one conditional conjunct: forward `AnnotOkV`
  transport onto the reduct.

`EnvSHyp` is the hypothesis bundle the case lemmas consume — the [set]
shadow of the `EnvTT` fields the design's §2 lists, restricted to what
the 44 cases actually read, at the relations' fixed `(env, cval, φ)`.
T5's `EnvS` discharges it by projection; fields are added batch by
batch (statement-first with their consumer, per the house rule) and the
bundle freezes at the iota batch.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

variable (V : Type w) [SetTheory V]

/-! ## The motives -/

/-- What soundness concludes for a reduction: the interpretation is
preserved (unconditionally), and truthfulness transports forward.
Mirror of `WhnfCoreClaims`/`WhnfClaims` with the equality freed of the
`AnnotOk` hypothesis (T4 architecture record). -/
def RedS (Δ : List VExpr) (v w : VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ →
    interp V ρ v = interp V ρ w ∧ (AnnotOkV V ρ v → AnnotOkV V ρ w)

/-- What soundness concludes for an inference: the subject is truthful
and inhabits its type's interpretation.  Mirror of `InferClaims` minus
the type-side `AnnotOk` conjunct (dropped; see the record). -/
def InfS (Δ : List VExpr) (v T : VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ →
    AnnotOkV V ρ v ∧ interp V ρ v ∈ˢ interp V ρ T

/-- What soundness concludes for a definitional equality: the two
interpretations are equal, unconditionally.  Strictly stronger than
`DefEqClaims`' hypothesis-laden form — forced by the relation's free
`symm`/`trans` (`AnnotOkV` cannot cross a `DefEq`). -/
def DeqS (Δ : List VExpr) (a b : VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ a = interp V ρ b

/-- What soundness concludes for a telescope certification: the spine
fits (`TeleFitV`), every argument is truthful, and the residual is
truthful whenever the telescope is.  The `certs_fit` re-hang. -/
def TeleS (Δ : List VExpr) (T : VExpr) (as : List VExpr)
    (rest : VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ →
    TeleFitV V ρ T as rest ∧ (∀ a ∈ as, AnnotOkV V ρ a) ∧
    (AnnotOkV V ρ T → AnnotOkV V ρ rest)

/-- What soundness concludes for a spine equality: pointwise equal
interpretations (as map equality — the form `interp_mkAppN`
congruences consume).  The `defEqList_values` re-hang. -/
def DeqLS (Δ : List VExpr) (as bs : List VExpr) : Prop :=
  ∀ ρ : Nat → V, Sat V Δ ρ →
    as.map (interp V ρ) = bs.map (interp V ρ)

/-- The map/fold reading of a spine's interpretation — the form the
spine-equality rewrites consume (`DeqLS` conclusions are map
equalities). -/
theorem interp_mkAppN_map (ρ : Nat → V) (f : VExpr) (as : List VExpr) :
    interp V ρ (VExpr.mkAppN f as)
      = (as.map (interp V ρ)).foldl SetTheory.app (interp V ρ f) := by
  rw [interp_mkAppN, List.foldl_map]

/-! ## The capability laws (the [set] `EtaLaw`/`UnitLaw` transposes)

Statement shapes mirror `Setlec/Model/Interp.lean`'s `EtaLaw`/`UnitLaw`
(the model's own fields, *not* the TT lane's re-signed `EtaLawTT` — no
#135/#136/#137 content), with the value-spine fit stated through
`TeleFitV` over the denoted former type, which is exactly what the
`Tele` premises of D10/D11 supply.  T5 derives them from the checked
`_model.eta`/`_model.unitlike` theorems' front doors. -/

/-- The fired structural-eta law of an eta-capable stored family. -/
def EtaLawV (env : Env) (cval : TConstVal) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ (φ' : Name → Nat) (us : List Level) (ρ : Nat → V)
    (xs : List VExpr) (TV rest B : VExpr),
    xs.length = caps.etaParams →
    denoteClosed cval env φ'
      (cvT.type.instantiateLevelParams cvT.levelParams us) = some TV →
    TeleFitV V ρ TV xs rest →
    interp V ρ B ∈ˢ interp V ρ
      (VExpr.mkAppN (cval T (Level.substFn φ' cvT.levelParams us)) xs) →
    interp V ρ B = interp V ρ
      (VExpr.mkAppN
        (cval caps.etaCtor (Level.substFn φ' cvT.levelParams us))
        (etaFabArgsV cval T (Level.substFn φ' cvT.levelParams us) xs B
          caps.etaFields))

/-- The fired unit-like law of a unit-like stored family. -/
def UnitLawV (env : Env) (cval : TConstVal) (T : Name)
    (cvT : ConstantVal) (caps : IndCaps) : Prop :=
  ∀ (φ' : Name → Nat) (us : List Level) (ρ : Nat → V)
    (xs : List VExpr) (TV rest : VExpr) (x y : V),
    xs.length = caps.unitParams →
    denoteClosed cval env φ'
      (cvT.type.instantiateLevelParams cvT.levelParams us) = some TV →
    TeleFitV V ρ TV xs rest →
    x ∈ˢ interp V ρ
      (VExpr.mkAppN (cval T (Level.substFn φ' cvT.levelParams us)) xs) →
    y ∈ˢ interp V ρ
      (VExpr.mkAppN (cval T (Level.substFn φ' cvT.levelParams us)) xs) →
    x = y

/-- A stored structural-`Nat` operation's semantic certificate
(`NatOpsOk` transpose): the literal fast-path guard, and the defining
recurrence equations semantically — the two free variables denote to
the two innermost context slots, valued by members of the stored
`Nat`'s interpretation. -/
def NatOpsV (env : Env) (cval : TConstVal) (φ : Name → Nat) : Prop :=
  ∀ c ∈ natOpNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    natOpGuard env c = true ∧
    ∀ eq ∈ natOpEquations 0 c, ∃ L R,
      denote cval env φ 2 eq.1 = some L ∧
      denote cval env φ 2 eq.2 = some R ∧
      ∀ (ρ : Nat → V) (x y : V),
        x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
        y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
        interp V (cons V y (cons V x ρ)) L
          = interp V (cons V y (cons V x ρ)) R

/-- The `ble`-guarded value-level clauses of a pin-certified
WF-recursive operation, over a value valuation of the level-mono
heads (`DivModClauses` transpose, verbatim — value-level). -/
def DivModClausesV (val : Name → V) (c : Name) (x y : V) : Prop :=
  let vT := val boolTrueName
  let vF := val boolFalseName
  let one : V := SetTheory.app (val natSuccName) (val natZeroName)
  let two : V := SetTheory.app (val natSuccName) one
  let ble2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natBleName) a) b
  let op2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val c) a) b
  let sub2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natSubName) a) b
  let add2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natAddName) a) b
  let mul2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natMulName) a) b
  let div2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natDivName) a) b
  let mod2 : V → V → V :=
    fun a b => SetTheory.app (SetTheory.app (val natModName) a) b
  if c = natGcdName then
    (ble2 one x = vT → op2 x y = op2 (mod2 y x) x) ∧
    (ble2 one x = vF → op2 x y = y)
  else if c = natShiftLeftName then
    (ble2 one y = vT → op2 x y = op2 (mul2 two x) (sub2 y one)) ∧
    (ble2 one y = vF → op2 x y = x)
  else if c = natShiftRightName then
    (ble2 one y = vT → op2 x y = div2 (op2 x (sub2 y one)) two) ∧
    (ble2 one y = vF → op2 x y = x)
  else if c = natLog2Name then
    (ble2 two x = vT →
      SetTheory.app (val c) x
        = SetTheory.app (val natSuccName)
            (SetTheory.app (val c) (div2 x two))) ∧
    (ble2 two x = vF → SetTheory.app (val c) x = val natZeroName)
  else if c = natLandName then
    (ble2 one x = vT →
      op2 x y = add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mul2 (mod2 x two) (mod2 y two))) ∧
    (ble2 one x = vF → op2 x y = val natZeroName)
  else if c = natLorName then
    (ble2 one x = vT →
      op2 x y = add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (sub2 (add2 (mod2 x two) (mod2 y two))
          (mul2 (mod2 x two) (mod2 y two)))) ∧
    (ble2 one x = vF → op2 x y = y)
  else if c = natXorName then
    (ble2 one x = vT →
      op2 x y = add2 (mul2 two (op2 (div2 x two) (div2 y two)))
        (mod2 (add2 (mod2 x two) (mod2 y two)) two)) ∧
    (ble2 one x = vF → op2 x y = y)
  else
    (ble2 y x = vT → ble2 one y = vT →
     op2 x y =
       (if c = natDivName then
          SetTheory.app (val natSuccName) (op2 (sub2 x y) y)
        else op2 (sub2 x y) y)) ∧
    (ble2 y x = vF →
     op2 x y = (if c = natDivName then val natZeroName else x)) ∧
    (ble2 one y = vF →
     op2 x y = (if c = natDivName then val natZeroName else x))

/-- A stored pin-certified WF-recursive operation's guard and guarded
recurrences at the value level (`DivModOk` transpose). -/
def DivModV (env : Env) (cval : TConstVal) (φ : Name → Nat) : Prop :=
  ∀ c ∈ natDivModNames, ∀ cv v hint,
    env.find? c = some (.defnInfo cv v hint) →
    natOpGuard env c = true ∧
    ∀ (ρ : Nat → V) (x y : V),
      x ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      y ∈ˢ interp V ρ (cval natName (Level.substFn φ [] [])) →
      DivModClausesV V
        (fun n => interp V ρ (cval n (Level.substFn φ [] []))) c x y

/-- The stored families' capability laws (`CapsOk` transpose,
provenance-abstract, basis families exempt). -/
def CapsOkV (env : Env) (cval : TConstVal) : Prop :=
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.eta = true →
    reservedBasisNames.contains T = false →
    EtaFamilyStored env T caps →
    EtaLawV V env cval T cvT caps) ∧
  (∀ (T : Name) (cvT : ConstantVal) (caps : IndCaps),
    env.find? T = some (.indInfo cvT caps) → caps.unitlike = true →
    reservedBasisNames.contains T = false →
    UnitLawV V env cval T cvT caps)

/-! ## The environment-hypothesis bundle -/

/-- The semantic environment facts the soundness cases consume, at the
relations' fixed `(env, cval, φ)`.  Each field names its §2
counterpart and its T5 supplier; see the module docstring. -/
structure EnvSHyp (env : Env) (cval : TConstVal) (φ : Name → Nat) :
    Prop where
  /-- Every valuation leaf is closed (`EnvTT.cval_closed`'s shape; the
  ambient hypothesis of M1 and of every closedness rewrite). -/
  cval_closed : ∀ (n : Name) (ψ : Name → Nat), VExpr.Closed (cval n ψ)
  /-- Every valuation leaf is truthful at every environment
  (§2 `annot_okV`; supplier: the value front door's subject
  conjunct). -/
  annot_okV : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOkV V ρ (cval n ψ)
  /-- Every stored constant inhabits its denoted instantiated type,
  which is truthful (§2 `mem_type`; suppliers: the value front door's
  membership through the unconditional defeq, and the *type* front
  door's subject conjunct).  Keyed exactly on I3's side conditions. -/
  mem_type : ∀ (n : Name) (ci : ConstantInfo),
    env.find? n = some ci →
    ∀ us : List Level, us.length = ci.toConstantVal.levelParams.length →
    ∀ T : VExpr,
      denoteClosed cval env φ
        (ci.toConstantVal.type.instantiateLevelParams
          ci.toConstantVal.levelParams us) = some T →
      ∀ ρ : Nat → V,
        interp V ρ
            (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
          ∈ˢ interp V ρ T ∧
        AnnotOkV V ρ T
  /-- The reserved basis constants are the pinned declarations, valued
  by their direct pins (§2 `basis_pinned`; the relocated
  `BasisPinnedTT`, verbatim — supplier: the basis install, identical
  in both lanes). -/
  basis_pinned : BasisPinnedTT env cval
  /-- The stored families' fired capability laws (§2 `caps_ok`;
  supplier: the `_model.eta`/`_model.unitlike` front doors). -/
  caps_ok : CapsOkV V env cval
  /-- Every stored native projection-table entry is a pinned pair
  entry with its block stored (§2 `proj_ok`; the relocated `ProjOkT`,
  verbatim — syntactic, install-supplied). -/
  proj_ok : ProjOkT env
  /-- The structural-`Nat` operations' semantic certificates (§2
  `nat_ops`; supplier: `certifyNatEqs`' derivations through the
  unconditional DefEq-sound). -/
  nat_ops : NatOpsV V env cval φ
  /-- The pin-certified WF-recursive operations' guarded value
  recurrences (§2 `div_mod`; supplier: the div/mod certificate
  pack). -/
  div_mod : DivModV V env cval φ

end Setlec.SetR
