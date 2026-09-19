module

public import ConLeche.Model.Inductives.NestedPremise
public section

/-!
# The pinned `PUnit` block's block model (task #315, M7-4)

The third of the five pinned basis blocks (`BasisBlocksZero.lean`
carries `Empty` and `False`): one member, no parameters, no indices,
ONE constructor with no fields, no pins.

The carrier is the pinned one on the nose — `bval .punit = unitSet`,
whose single element is the proof point `bval .punitUnit = pt` — so
the tuple operator is the CONSTANT one-point family and the injection
is the point.  That is where `PUnit` differs from a block this checker
installs, and why `ContainerModeled.inj`'s tag shape is guarded by
`0 < d.nP` (task #315 M7-4, DESIGN §U.45): `PUnit` has no parameters,
`nestedOccOk` never pins it, and `pt` is no tagged tower
(`BasisBlocksTag.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind RecRule
  ContainerInfo ContainerMember IndCaps)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The block model -/

/-- **`PUnit`'s block model**: one member, no parameters, no indices,
one constructor with no fields, no pins; the operator the constant
one-point family over the one-point index-tuple set, the injection the
proof point. -/
@[expose] noncomputable def punitBlock : BlockModel V where
  nP := 0
  k := 1
  resSort := .param ConLeche.uN
  isProp := (Level.isEquiv (.param ConLeche.uN) .zero == some true)
  large := true
  env₀ := ⟨[]⟩
  memberNames := [ConLeche.punitName]
  nIdxs := [0]
  ppsM := fun _ _ => []
  uM := fun _ _ => 0
  ctorsM := fun _ => [(ConLeche.punitUnitA.toConstantVal, 0)]
  idxF := fun _ _ => []
  dsF := fun _ _ _ => []
  esF := fun _ _ _ => []
  srcsF := fun _ _ => []
  ksF := fun _ _ => []
  tgts := fun _ _ _ => 0
  fvsPF := fun _ _ => []
  xFvsF := fun _ _ => []
  xrestF := fun _ _ => .const ConLeche.punitName [.param ConLeche.uN]
  eissF := fun _ _ _ => []
  tssF := fun _ _ _ => []
  pins := []
  Φ := fun _ _ _ _ => graph (fun _ => unitSet) unitSet
  pinCar := fun _ _ _ _ => pt
  Ψaux := fun _ _ _ _ => graph (fun _ => unitSet) unitSet
  pinCtors := fun _ => default
  inj := fun _ _ _ _ => pt

namespace punitBlock

local notation "D" => (punitBlock (V := V))

/-- The index-tuple set is the one-point set at every frame. -/
theorem idx_eq (ψ : Name → Nat) (ρp : Nat → V) (mm : Nat) : (D).idx ψ ρp mm = unitSet := rfl

/-- The operator's value, spelled at the index-tuple set. -/
theorem Phi_app (ψ : Name → Nat) (ρp X : Nat → V) (mm : Nat) :
    (D).Φ ψ ρp X mm = graph (fun _ => (unitSet : V)) ((D).idx ψ ρp mm) := rfl

/-- The operator maps the tuple space into itself. -/
theorem maps (ψ : Name → Nat) (ρp : Nat → V) :
    MapsTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) :=
  fun _ _ _ _ => graph_mem_famSpace fun _ _ => unitSet_mem_univ _

/-- The operator is monotone: it is constant. -/
theorem mono (ψ : Name → Nat) (ρp : Nat → V) :
    MonoTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) :=
  fun _ _ _ _ _ => TupleLe.refl _ _ _

/-- The operator is its own closed tuple. -/
theorem closed (ψ : Name → Nat) (ρp : Nat → V) :
    ∃ L, IsClosedTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) L :=
  ⟨fun _ => graph (fun _ => unitSet) unitSet,
    ⟨fun _ _ => graph_mem_famSpace fun _ _ => unitSet_mem_univ _, TupleLe.refl _ _ _⟩⟩

/-- **The carrier's fibre is the one-point set** — the pinned value. -/
theorem lfp_app (ψ : Name → Nat) (ρp : Nat → V) {t : V} (ht : t ∈ˢ (D).idx ψ ρp 0) :
    app (lfpTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) 0) t = (unitSet : V) := by
  rw [← app_lfpTuple_eq (closed ψ ρp) (mono ψ ρp) (maps ψ ρp) Nat.one_pos ht, Phi_app]
  exact app_graph ht

/-- The one index tuple is in the index-tuple set. -/
theorem tup_mem (ψ : Name → Nat) (ρp : Nat → V) : (D).tup ψ 0 [] ∈ˢ (D).idx ψ ρp 0 :=
  (D).tupMem (ψ := ψ) (ρp := ρp) (mm' := 0) (is := []) trivial

/-- The constructor's field domains are empty. -/
theorem Fss_eq (ψ : Name → Nat) : ((D).Fss 0 ψ).getD 0 [] = ([] : List AnnotTerm) := rfl

/-- The member's index telescope is empty. -/
theorem IdsM_eq (ψ : Name → Nat) : (D).IdsM 0 ψ = ([] : List AnnotTerm) := rfl

end punitBlock

/-! ## The pinned readings -/

/-- `PUnit`'s leaf is its pin. -/
theorem acval_punit_eq {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA) (ψ : Name → Nat) :
    m.acval ConLeche.punitName ψ = .const .punit [ψ ConLeche.uN] := by
  have hpd : ConLeche.Verify.pinnedStructT ConLeche.punitName ψ
      = some (Term.const .punit [ψ ConLeche.uN]) := by
    simp +decide [ConLeche.Verify.pinnedStructT]
  exact acval_basis_pinned hT (by decide) hpd

/-- `PUnit.unit`'s leaf is its pin. -/
theorem acval_punitUnit_eq {env : Env} {m : EnvModel V env}
    (hU : env.find? ConLeche.punitUnitName = some ConLeche.punitUnitA) (ψ : Name → Nat) :
    m.acval ConLeche.punitUnitName ψ = .const .punitUnit [ψ ConLeche.uN] := by
  have hpd : ConLeche.Verify.pinnedStructT ConLeche.punitUnitName ψ
      = some (Term.const .punitUnit [ψ ConLeche.uN]) := by
    simp +decide [ConLeche.Verify.pinnedStructT]
  exact acval_basis_pinned hU (by decide) hpd

/-- `PUnit`'s value is the one-point set. -/
theorem interp_acval_punit {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (m.acval ConLeche.punitName ψ) = (unitSet : V) := by
  rw [acval_punit_eq hT ψ]; rfl

/-- `PUnit.unit`'s value is the proof point. -/
theorem interp_acval_punitUnit {env : Env} {m : EnvModel V env}
    (hU : env.find? ConLeche.punitUnitName = some ConLeche.punitUnitA)
    (ψ : Name → Nat) (ρ : Nat → V) :
    interp V ρ (m.acval ConLeche.punitUnitName ψ) = (pt : V) := by
  rw [acval_punitUnit_eq hU ψ]; rfl

/-- `PUnit`'s leaf, as the constructor's data reads it: the former at
no parameters and no indices. -/
theorem acval_punit_body {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA) (ψ : Name → Nat) :
    denoteMeta m.acval env ψ 0 (.const ConLeche.punitName [.param ConLeche.uN])
      = some (m.acval ConLeche.punitName ψ) := by
  rw [denoteMeta_const hT (by rfl)]
  show some (m.acval ConLeche.punitName
    (Level.substFn ψ [ConLeche.uN] ([ConLeche.uN].map Level.param))) = _
  rw [Level.substFn_param_self ψ [ConLeche.uN]]

/-! ## The read-back -/

/-- **`PUnit`'s group, read back** — the one-member group with the
single constructor. -/
theorem containerInfo?_punitA {env : Env}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA)
    (hR : env.find? ConLeche.punitRecName = some ConLeche.punitRecA)
    (hU : env.find? ConLeche.punitUnitName = some ConLeche.punitUnitA) :
    ConLeche.containerInfo? env ConLeche.punitName
      = some ⟨0, [⟨ConLeche.punitName, [ConLeche.uN], ConLeche.punitA.toConstantVal.type,
        [⟨ConLeche.punitUnitName, ConLeche.punitUnitA.toConstantVal.type, 0⟩]⟩]⟩ := by
  have hE : ConLeche.punitName = Name.anonymous.str "PUnit" := rfl
  have hUE : ConLeche.punitUnitName = (Name.anonymous.str "PUnit").str "unit" := rfl
  have hRE : ConLeche.punitRecName = (Name.anonymous.str "PUnit").str "rec" := rfl
  rw [hE] at hT
  rw [hRE] at hR
  rw [hUE] at hU
  have hmot : ConLeche.containerMotiveMember? env 0 0
      (Expr.forallE (.const (Name.anonymous.str "PUnit") [.param (Name.anonymous.str "u")])
        (.sort (.param (Name.anonymous.str "u_1"))) { pw := .never })
      = some (Name.anonymous.str "PUnit") := by
    simp +decide [ConLeche.containerMotiveMember?, Expr.piBinders, Expr.getAppFn,
      Expr.getAppArgs, hT]
  have hmot2 : ConLeche.containerMotiveMember? env 0 1
      (Expr.app (.bvar 0) (.const ((Name.anonymous.str "PUnit").str "unit")
        [.param (Name.anonymous.str "u")])) = none := by
    simp [ConLeche.containerMotiveMember?, Expr.piBinders]
  simp +decide [ConLeche.containerInfo?, hT, hR, hU, ConLeche.punitA, ConLeche.punitRecA,
    ConLeche.punitUnitA, Expr.stripPis, ConLeche.containerMembersGo, hmot, hmot2, Option.bind,
    ConLeche.punitUnitName, ConLeche.punitName, ConLeche.uN]

/-! ## The constructor's data -/

/-- **`PUnit.unit`'s reading**: a constructor with no parameters, no
fields and no indices — its stored type IS the former's constant, so
every clause is either the leaf's reading or vacuous. -/
theorem punitBlock_ctorData {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA)
    (hU : env.find? ConLeche.punitUnitName = some ConLeche.punitUnitA) :
    BlockCtorFacts m (punitBlock (V := V)) [ConLeche.uN] 0 0
      (ConLeche.punitUnitA.toConstantVal, 0) := by
  refine ⟨hU, rfl, ?_⟩
  refine
    { resid := ⟨[], [], rfl, rfl⟩
      read := fun ψ => ?_
      len := fun _ => rfl
      lenE := fun _ => rfl
      idxLen := rfl
      idxRead := fun _ => DenoteMetaSpine.nil
      bits := fun _ _ h => nomatch h
      okTy := fun ψ ρ => ?_
      below := fun _ => trivial
      belowE := fun _ _ h => nomatch h
      params := fun _ _ _ => ⟨rfl, rfl⟩
      srcLen := rfl
      srcBnd := fun _ h => nomatch h
      srcIdx := fun j l h => ?_
      srcProp := fun _ _ _ _ _ => trivial
      opened :=
        { residRes := fun e h => ?_
          ord := fun i x h => nomatch h
          recF := fun i x h => nomatch h
          reflF := fun i x h => nomatch h
          nestF := fun i x q h => nomatch h
          nestReflF := fun i x q h => nomatch h
          kinds := fun i h => nomatch h }
      opens := ⟨_, rfl, rfl⟩
      ksLen := rfl
      xLen := rfl
      pLen := rfl
      xIdx := fun k x h => nomatch h
      pIdx := fun k x h => nomatch h
      idxEq := rfl
      domRead := fun _ i x h => nomatch h
      eissLen := fun _ => rfl
      eisRead := fun _ i x h => nomatch h
      eisLen := fun _ i _ _ h => nomatch h
      recEntry := fun _ i _ _ h => nomatch h
      nestEisRead := fun _ i x q h => nomatch h
      nestEisLen := fun _ i q _ _ h => nomatch h
      nestEntry := fun _ i q _ _ h => nomatch h
      eissParams := fun _ _ _ => rfl
      eissBelow := fun _ i E h => nomatch h
      ordNone := fun _ _ _ _ => rfl
      tssLen := fun _ => rfl
      tssNone := fun _ _ _ => rfl
      tssBits := fun _ _ d h => nomatch h
      tssPiBits := fun _ _ d h => nomatch h
      tssBelow := fun _ _ => trivial
      tssParams := fun _ _ _ => rfl
      reflOpen := fun _ i x h => nomatch h
      eisLenRefl := fun _ i _ _ h => nomatch h
      reflEntry := fun _ i _ _ h => nomatch h
      nestReflOpen := fun _ i x q h => nomatch h
      nestEisLenRefl := fun _ i q _ _ h => nomatch h
      nestReflEntry := fun _ i q _ _ h => nomatch h }
  · show denoteMeta m.acval env ψ 0 (.const ConLeche.punitName [.param ConLeche.uN]) = _
    rw [acval_punit_body hT ψ]
    rfl
  · show WellDenotedV V ρ (AnnotTerm.mkAppN (m.acval ConLeche.punitName ψ) [])
    rw [show AnnotTerm.mkAppN (m.acval ConLeche.punitName ψ) [] = m.acval ConLeche.punitName ψ
      from rfl, acval_punit_eq hT ψ]
    exact ⟨trivial, trivial⟩
  · exact nomatch h
  · exact nomatch h

/-! ## The block model's clauses -/

/-- **`PUnit` is represented by its block model**: the syntactic
clauses are the pin's own records (`mI = rP = 2`, one rule, the former
a bare sort), the semantic ones the constant one-point operator —
whose least pre-fixed tuple's fibre IS the pinned `unitSet`, and whose
single injection IS the pinned `pt`. -/
theorem punitBlock_isBlockModel {env : Env} {m : EnvModel V env} {cvR : ConstantVal}
    {rules : List RecRule}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA)
    (hU : env.find? ConLeche.punitUnitName = some ConLeche.punitUnitA)
    (hrules : rules ≠ [] → rules.map (·.ctor) = [ConLeche.punitUnitName]) :
    IsBlockModel m ConLeche.punitName ConLeche.punitA.toConstantVal cvR 2 2 rules
      (punitBlock (V := V)) 0 where
  memberLt := Nat.one_pos
  member := rfl
  strip := ⟨[], .param ConLeche.uN, rfl, fun _ => rfl⟩
  isProp := rfl
  mI := rfl
  rP := rfl
  rules := hrules
  former :=
    { read := fun ψ => by rw [show ConLeche.punitA.toConstantVal.type
        = Expr.sort (.param ConLeche.uN) from rfl, denoteMeta_sort]; rfl
      len := fun _ => rfl
      bits := fun _ _ h => nomatch h
      okTy := fun _ _ => ⟨trivial, trivial⟩
      below := fun _ => trivial
      params := fun _ _ h => ⟨rfl, h ConLeche.uN (List.mem_singleton.mpr rfl)⟩ }
  ctors := fun mm' j cA hmm hj => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    obtain rfl : cA = (ConLeche.punitUnitA.toConstantVal, 0) := by
      match j, hj with
      | 0, hj => exact (Option.some.inj hj).symm
    exact punitBlock_ctorData hT hU
  memsFound := fun mm' hmm => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    exact ⟨_, _, hT⟩
  pinsFound := fun _ h => nomatch h
  tgtsLt := fun _ _ _ _ _ h => nomatch h
  idxRes := fun _ _ _ _ _ _ h => nomatch h
  uParams := fun _ _ _ _ _ => rfl
  paramsIff := fun _ _ _ _ _ _ _ => Iff.rfl
  idxOk := fun _ _ _ _ _ => ⟨trivial, trivial⟩
  functor := fun ψ ρp _ => ⟨punitBlock.mono ψ ρp, punitBlock.maps ψ ρp, punitBlock.closed ψ ρp⟩
  fibre := fun ψ ρp _ X _ mm' hmm t ht x => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    rw [punitBlock.Phi_app ψ ρp X 0, app_graph ht]
    refine ⟨fun hx => ⟨0, [], Nat.one_pos, ⟨trivial, fun l hl => nomatch hl⟩,
      mem_unitSet_iff.mp hx⟩, ?_⟩
    rintro ⟨j, fs, -, -, rfl⟩
    exact pt_mem_unitSet
  pinShape := fun _ h => nomatch h
  pinMem := fun _ _ _ _ _ _ h => nomatch h
  pinMono := fun _ _ _ _ _ _ _ _ _ h => nomatch h
  auxFunctor := fun ψ ρp _ => ⟨punitBlock.mono ψ ρp, punitBlock.maps ψ ρp, punitBlock.closed ψ ρp⟩
  auxCompose := fun _ _ => composeΦ_zero.symm
  auxPinsCar := fun _ _ _ _ h => nomatch h
  auxPinIdx := fun _ h => nomatch h
  auxFibre := BlockModel.auxFibre_of_noPins _ rfl (fun _ _ => rfl)
    (fun _ _ _ _ _ => Nat.one_pos)
    (fun ψ ρp _ X _ mm' hmm t ht x => by
        obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
        rw [punitBlock.Phi_app ψ ρp X 0, app_graph ht]
        refine ⟨fun hx => ⟨0, [], Nat.one_pos, ⟨trivial, fun l hl => nomatch hl⟩,
          mem_unitSet_iff.mp hx⟩, ?_⟩
        rintro ⟨j, fs, -, -, rfl⟩
        exact pt_mem_unitSet)
  pinLeaf := fun _ h => nomatch h
  leaf := fun ψ ρ as is hsp hi => by
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero (SpineFit.length_eq hsp)
    obtain rfl : is = [] := List.eq_nil_of_length_eq_zero (SpineFit.length_eq hi)
    rw [List.append_nil, List.foldl_nil, interp_acval_punit hT,
      punitBlock.lfp_app ψ (consList [] ρ) (punitBlock.tup_mem ψ (consList [] ρ))]
  ctor := fun mm' j cA hmm hj ψ ρ as fs hsp hsp₂ => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    obtain ⟨rfl, rfl⟩ : j = 0 ∧ cA = (ConLeche.punitUnitA.toConstantVal, 0) := by
      match j, hj with
      | 0, hj => exact ⟨rfl, (Option.some.inj hj).symm⟩
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero (SpineFit.length_eq hsp)
    obtain rfl : fs = [] := List.eq_nil_of_length_eq_zero (SpineFit.length_eq hsp₂)
    show ([] ++ []).foldl app (interp V ρ (m.acval ConLeche.punitUnitName ψ)) = _
    rw [List.append_nil, List.foldl_nil, interp_acval_punitUnit hU]
    rfl
  mkZero := fun _ _ _ _ _ => rfl
  mkInj := fun _ _ mm' hmm j fs j' fs' hj hj' hlen hlen' _ => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
    obtain rfl : j' = 0 := Nat.lt_one_iff.mp hj'
    exact ⟨rfl, (List.eq_nil_of_length_eq_zero hlen).trans
      (List.eq_nil_of_length_eq_zero hlen').symm⟩

/-- **`PUnit`'s pins' laws**: no pins, so every clause but `mkZero` is
guarded, and `mkZero` holds of the default `PinCtors`. -/
theorem punitBlock_pinRecLaws {env : Env} {m : EnvModel V env} :
    PinRecLaws m (punitBlock (V := V)) (fun _ => default) where
  tgtsLt := fun _ _ _ _ h => nomatch h
  idxOk := fun _ _ _ _ h => nomatch h
  fibre := fun _ _ _ _ _ _ _ h => nomatch h
  mkZero := fun _ _ _ _ _ => rfl
  mkInj := fun _ _ _ h => nomatch h
  injW := fun _ _ h => nomatch h
  ind := fun _ _ _ _ _ _ _ _ h => nomatch h

/-- **`PUnit`'S OWN-PIN TABLE IS EMPTY** (task #315 M7-3 session 17,
K.49) — `natBlock_ownPins` at the one-constructor block: no mimic
recursor is installed, `checkBasisDecl` certifies that itself
(`basisOwnMimicsOk`), and `containerOwnPinsAt`'s walk stops before its
first step. -/
theorem punitBlock_ownPins {env : Env}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA)
    (hR : env.find? ConLeche.punitRecName = some ConLeche.punitRecA)
    (hU : env.find? ConLeche.punitUnitName = some ConLeche.punitUnitA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.punitName 0 = true) :
    ContainerOwnPinsSyn (V := V) env (punitBlock (V := V)) :=
  ContainerOwnPinsSyn.of_noMimics rfl hmim fun i hi => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp (show i < 1 from hi)
    exact ⟨_, _, containerInfo?_punitA hT hR hU, rfl, rfl⟩

/-- **`PUnit`'s group carries its block model**.  The `inj` clause is
VACUOUS here: `PUnit` has no parameters, so the guard `0 < d.nP`
(task #315 M7-4) is unsatisfiable — which is the whole point, the
pinned injection being `pt` and not a tagged tower. -/
theorem punitBlock_containerModeled {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA)
    (hR : env.find? ConLeche.punitRecName = some ConLeche.punitRecA)
    (hU : env.find? ConLeche.punitUnitName = some ConLeche.punitUnitA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.punitName 0 = true) :
    ContainerModeled m ⟨0, [⟨ConLeche.punitName, [ConLeche.uN],
        ConLeche.punitA.toConstantVal.type,
        [⟨ConLeche.punitUnitName, ConLeche.punitUnitA.toConstantVal.type, 0⟩]⟩]⟩
      (punitBlock (V := V)) where
  k := rfl
  namesLen := rfl
  nP := rfl
  reps := fun c hc => by
    obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
    exact ⟨_, ConLeche.punitA.toConstantVal, 2, 2, [],
      punitBlock_isBlockModel hT hU (fun h => absurd rfl h)⟩
  typed := fun ψ => by
    refine ⟨fun t ht ρ => ?_, ⟨fun c hc j cA hj ρ => ?_,
      PinsTyped.of_noPins (d := punitBlock (V := V)) rfl ψ⟩⟩
    · obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      rw [show (punitBlock (V := V)).memberName 0 = ConLeche.punitName from rfl,
        interp_acval_punit hT]
      exact unitSet_mem_univ _
    · obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
      obtain ⟨rfl, rfl⟩ : j = 0 ∧ cA = (ConLeche.punitUnitA.toConstantVal, 0) := by
        match j, hj with
        | 0, hj => exact ⟨rfl, (Option.some.inj hj).symm⟩
      show interp V ρ (m.acval ConLeche.punitUnitName ψ) ∈ˢ _
      rw [interp_acval_punitUnit hU]
      show (pt : V) ∈ˢ interp V ρ (AnnotTerm.mkAppN (m.acval ConLeche.punitName ψ) [])
      rw [show AnnotTerm.mkAppN (m.acval ConLeche.punitName ψ) [] = m.acval ConLeche.punitName ψ
        from rfl, interp_acval_punit hT]
      exact pt_mem_unitSet
  inj := fun h => absurd h (Nat.lt_irrefl 0)
  member := fun i M hM => by
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ M = ⟨ConLeche.punitName, [ConLeche.uN],
        ConLeche.punitA.toConstantVal.type,
        [⟨ConLeche.punitUnitName, ConLeche.punitUnitA.toConstantVal.type, 0⟩]⟩ := by
      match i, hM with
      | 0, hM => exact ⟨rfl, (Option.some.inj hM).symm⟩
    exact ⟨rfl, rfl, ConLeche.punitA.toConstantVal, 2, 2, [],
      punitBlock_isBlockModel hT hU (fun h => absurd rfl h)⟩
  frame := fun _ _ _ _ => Iff.rfl
  ordFree := fun _ _ _ _ _ _ h => nomatch h
  nestMention := fun _ h => nomatch h
  nestArgsMention := fun _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestArgsMentionAbs := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestArgsMentionAbsRefl := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestPinSpineAbs := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  ctorProjFree := fun i j cA hi hj T hT n => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    obtain rfl := List.mem_singleton.mp hT
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (ConLeche.punitUnitA.toConstantVal, 0) := (Option.some.inj hj).symm
      simp [ConLeche.punitUnitA, ConLeche.ConstantInfo.toConstantVal]
  pinsNotMembers := fun _ h => nomatch h
  pinNP := fun _ h => nomatch h
  pinConts := fun _ h => nomatch h
  ownPins := punitBlock_ownPins hT hR hU hmim
  pinψ := fun _ h => nomatch h
  pinsDistinct := fun _ _ h _ _ => nomatch h
  pinsDistinctAt := fun _ _ _ h _ _ => nomatch h
  pinDsScoped := fun _ h => nomatch h
  pinDsRes := fun _ h => nomatch h
  pinParams := fun _ _ _ => ContainerPinParams.of_noPins rfl

/-- **`PUnit` carries its block's model** at any assignment that sends
its group to `punitBlock`. -/
theorem punitBlockAt {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.punitName = some ConLeche.punitA)
    (hR : env.find? ConLeche.punitRecName = some ConLeche.punitRecA)
    (hU : env.find? ConLeche.punitUnitName = some ConLeche.punitUnitA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.punitName 0 = true)
    {B : ContainerInfo → BlockModel V}
    (hB : B ⟨0, [⟨ConLeche.punitName, [ConLeche.uN], ConLeche.punitA.toConstantVal.type,
        [⟨ConLeche.punitUnitName, ConLeche.punitUnitA.toConstantVal.type, 0⟩]⟩]⟩
      = punitBlock (V := V)) :
    BlockAt m B ⟨0, [⟨ConLeche.punitName, [ConLeche.uN], ConLeche.punitA.toConstantVal.type,
        [⟨ConLeche.punitUnitName, ConLeche.punitUnitA.toConstantVal.type, 0⟩]⟩]⟩ := by
  refine ⟨hB ▸ punitBlock_containerModeled hT hR hU hmim, ⟨fun _ => default, ?_, ?_⟩⟩
  · exact hB ▸ punitBlock_pinRecLaws
  · rw [hB]; exact fun q hq => nomatch hq

end ConLeche.Model


