module

public import ConLeche.Model.Inductives.NestedPremise
public section

/-!
# The pinned `Eq` block's block model (task #315, M7-4)

The last of the five pinned basis blocks, and the only one with
PARAMETERS and an INDEX: `Eq.{u} {α : Sort u} : α → α → Prop` has two
parameters (`α` and the left argument `a`), one index (the right
argument `b`), one constructor `Eq.refl` with no fields, and no pins.

Its carrier is not a fixpoint either — no constructor of `Eq` has a
recursive field — so the tuple operator is CONSTANT in the tuple, and
the whole content of `leaf` is the environment's own `EqLaw`: the
pinned spine's value is the truth set `eqv a b`.  The index equation of
`Eq.refl` (`a = b`) is what the operator's fibre reads, through the
index tuple's first projection.

`Eq` is the one pinned block that KEEPS `ContainerModeled.inj`'s tag
shape (it has parameters, so `nestedOccOk` can pin it): being
`Prop`-valued, `injW 0 j _ = pt`, which IS the pinned value of
`Eq.refl`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  ContainerInfo ContainerMember IndCaps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The opened parameters -/

/-- The first parameter variable `α`, as the elimination opens it. -/
def eqFv0 : Expr := .fvar 0 (.sort (.param ConLeche.uN))

/-- The second parameter variable `a : α`. -/
def eqFv1 : Expr := .fvar 1 eqFv0

/-- `Eq.refl`'s opened residual: `Eq α a a` at the two opened
parameters. -/
def eqResid : Expr :=
  .app (.app (.app (.const ConLeche.eqName [.param ConLeche.uN]) eqFv0) eqFv1) eqFv1

/-! ## The block model -/

/-- **`Eq`'s block model**: one member, two parameters, one index, one
constructor with no fields, no pins; the operator the CONSTANT family
of truth sets `eqv a (projS 0 t)` over the index-tuple set, the
injection the point (the block is `Prop`-valued). -/
@[expose] noncomputable def eqBlock : BlockModel V where
  nP := 2
  k := 1
  resSort := .zero
  isProp := (Level.isEquiv .zero .zero == some true)
  large := true
  env₀ := ⟨[]⟩
  memberNames := [ConLeche.eqName]
  nIdxs := [1]
  ppsM := fun _ ψ => [(0, 1, .sort (ψ ConLeche.uN)), (0, 1, .bvar 0), (0, 1, .bvar 1)]
  uM := fun _ ψ => ψ ConLeche.uN
  ctorsM := fun _ => [(ConLeche.eqReflA.toConstantVal, 0)]
  idxF := fun _ _ => [eqFv1]
  dsF := fun _ _ ψ => [(0, 0, .sort (ψ ConLeche.uN)), (0, 0, .bvar 0)]
  esF := fun _ _ _ => [.bvar 0]
  srcsF := fun _ _ => []
  ksF := fun _ _ => []
  tgts := fun _ _ _ => 0
  fvsPF := fun _ _ => [eqFv0, eqFv1]
  xFvsF := fun _ _ => []
  xrestF := fun _ _ => eqResid
  eissF := fun _ _ _ => []
  tssF := fun _ _ _ => []
  pins := []
  Φ := fun ψ ρp _ _ =>
    graph (fun t => eqv (ρp 0) (projS 0 t)) (idxSet (ψ ConLeche.uN) ρp [.bvar 1])
  pinCar := fun _ _ _ _ => pt
  Ψaux := fun ψ ρp _ _ =>
    graph (fun t => eqv (ρp 0) (projS 0 t)) (idxSet (ψ ConLeche.uN) ρp [.bvar 1])
  inj := fun _ _ _ _ => pt

namespace eqBlock

local notation "D" => (eqBlock (V := V))

/-- The parameter telescope: the sort and the left argument. -/
theorem params_eq (ψ : Name → Nat) :
    (D).params ψ = [AnnotTerm.sort (ψ ConLeche.uN), .bvar 0] := rfl

/-- The index telescope: the right argument, at the parameters' frame. -/
theorem IdsM_eq (ψ : Name → Nat) : (D).IdsM 0 ψ = [AnnotTerm.bvar 1] := rfl

/-- The index-tuple set. -/
theorem idx_eq (ψ : Name → Nat) (ρp : Nat → V) :
    (D).idx ψ ρp 0 = idxSet (ψ ConLeche.uN) ρp [.bvar 1] := rfl

/-- The operator's value, spelled at the index-tuple set. -/
theorem Phi_app (ψ : Name → Nat) (ρp X : Nat → V) (mm : Nat) :
    (D).Φ ψ ρp X mm = graph (fun t => eqv (ρp 0) (projS 0 t)) ((D).idx ψ ρp 0) := rfl

/-- The result sort is `Prop`. -/
theorem w_eq (ψ : Name → Nat) : (D).w ψ = 0 := rfl

/-- **The two facts a satisfying parameter frame carries**: the sort is
a universe member and the left argument is one of its elements. -/
theorem frame_facts {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V ((D).params ψ).reverse ρp) :
    ρp 1 ∈ˢ (univ (ψ ConLeche.uN) : V) ∧ ρp 0 ∈ˢ ρp 1 := by
  refine ⟨?_, ?_⟩
  · have := hρp 1 (.sort (ψ ConLeche.uN)) rfl
    exact this
  · have := hρp 0 (.bvar 0) rfl
    exact this

/-- The index telescope is graded at every satisfying frame. -/
theorem idxOk_of {ψ : Name → Nat} {ρp : Nat → V}
    (hρp : Sat V ((D).params ψ).reverse ρp) :
    IdxOk ((D).uM 0 ψ) ρp ((D).IdsM 0 ψ) := by
  obtain ⟨hA, -⟩ := frame_facts hρp
  exact ⟨⟨trivial, fun _ => hA, fun _ _ => trivial⟩, ⟨hA, fun _ _ => trivial⟩⟩

/-- The operator maps the tuple space into itself. -/
theorem maps (ψ : Name → Nat) (ρp : Nat → V) :
    MapsTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) :=
  fun _ _ _ _ => graph_mem_famSpace fun _ _ => eqv_mem_univ _ _

/-- The operator is monotone: it is constant in the tuple. -/
theorem mono (ψ : Name → Nat) (ρp : Nat → V) :
    MonoTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) :=
  fun _ _ _ _ _ => TupleLe.refl _ _ _

/-- The operator is its own closed tuple. -/
theorem closed (ψ : Name → Nat) (ρp : Nat → V) :
    ∃ L, IsClosedTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) L :=
  ⟨fun _ => graph (fun t => eqv (ρp 0) (projS 0 t)) ((D).idx ψ ρp 0),
    ⟨fun _ _ => graph_mem_famSpace fun _ _ => eqv_mem_univ _ _, TupleLe.refl _ _ _⟩⟩

/-- **The carrier's fibre is the truth set of the index equation.** -/
theorem lfp_app (ψ : Name → Nat) (ρp : Nat → V) {t : V} (ht : t ∈ˢ (D).idx ψ ρp 0) :
    app (lfpTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) 0) t
      = eqv (ρp 0) (projS 0 t) := by
  rw [← app_lfpTuple_eq (closed ψ ρp) (mono ψ ρp) (maps ψ ρp) Nat.one_pos ht, Phi_app]
  exact app_graph ht

/-- **The index tuple's first projection is the index** — at a nonzero
index sort the tuple is a pair, and at a zero one both sides are the
proof point (the index's type is then a proposition, whose only member
is `pt`). -/
theorem projS_tup {u : Nat} {A b : V} (hA : A ∈ˢ (univ u : V)) (hb : b ∈ˢ A) :
    projS 0 (tupW u [b]) = b ∨ (u = 0 ∧ b = pt ∧ projS 0 (tupW u [b]) = pt) := by
  by_cases hu : u = 0
  · subst hu
    refine Or.inr ⟨rfl, ?_, ?_⟩
    · exact mem_unitSet_iff.mp (mem_univZero.mp (univ_zero (V := V) ▸ hA) b hb)
    · rw [tupW_zero]; exact sfst_pt
  · refine Or.inl ?_
    rw [tupW_pos hu]
    show sfst (spair b (mkTower ([] : List V))) = b
    exact sfst_spair _ _

end eqBlock

/-- `eqv` is the truth value of the equation — the spelling the fibre
proof rewrites with. -/
theorem eqv_eq_truthVal (x y : V) : eqv x y = truthVal (x = y) := by unfold eqv; rfl

/-! ## The pinned readings -/

/-- **`Eq`'s type reading**: the three-binder telescope over the sort,
the left argument and the right one, ending in `Prop`. -/
theorem eqA_type_read {env : Env} {m : EnvModel V env} (ψ : Name → Nat) :
    denoteMeta m.acval env ψ 0 ConLeche.eqA.toConstantVal.type
      = some (mkPisAV ((eqBlock (V := V)).ppsM 0 ψ) (.sort ((eqBlock (V := V)).w ψ))) := by
  show denoteMeta m.acval env ψ 0
    (.forallE (.sort (.param ConLeche.uN))
      (.forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero) { pw := .never })
        { pw := .never }) { pw := .never }) = _
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_fvar, Expr.instantiate1,
    pwBit_never, Level.eval]
  rfl

/-- **`Eq.refl`'s type reading**: the two parameters, then the former
at them — `Eq α a a`. -/
theorem eqReflA_type_read {env : Env} {m : EnvModel V env}
    (hE : env.find? ConLeche.eqName = some ConLeche.eqA) (ψ : Name → Nat) :
    denoteMeta m.acval env ψ 0 ConLeche.eqReflA.toConstantVal.type
      = some (mkPisAV ((eqBlock (V := V)).dsF 0 0 ψ)
          (ctorBodyAVI m ConLeche.eqName 2 0 ψ ((eqBlock (V := V)).esF 0 0 ψ))) := by
  have hEc : ∀ d : Nat, denoteMeta m.acval env ψ d
      (.const ConLeche.eqName [.param ConLeche.uN]) = some (m.acval ConLeche.eqName ψ) := by
    intro d
    rw [denoteMeta_const hE (by rfl)]
    show some (m.acval ConLeche.eqName
      (Level.substFn ψ [ConLeche.uN] ([ConLeche.uN].map Level.param))) = _
    rw [Level.substFn_param_self ψ [ConLeche.uN]]
  show denoteMeta m.acval env ψ 0
    (.forallE (.sort (.param ConLeche.uN))
      (.forallE (.bvar 0)
        (.app (.app (.app (.const ConLeche.eqName [.param ConLeche.uN]) (.bvar 1)) (.bvar 0))
          (.bvar 0)) { pw := .ifAllZero [] }) { pw := .ifAllZero [] }) = _
  simp [denoteMeta_forallE, denoteMeta_sort, denoteMeta_fvar, denoteMeta_app,
    Expr.instantiate1, pwBit_ifAllZero_nil, hEc, ctorBodyAVI, paramBvars]
  rfl

/-! ## The constructor's data -/

/-- **`Eq.refl`'s reading**: two parameters, no fields, one index — its
stored type is the former at the two parameters, with the LEFT one
repeated as the index, which is the equation the fibre reads.  The
grading is the environment's own `EqLaw` (the spine's reading is a
proposition), the one clause a pinned `Prop`-valued block cannot get
from its own data. -/
theorem eqBlock_ctorData {env : Env} {m : EnvModel V env}
    (hE : env.find? ConLeche.eqName = some ConLeche.eqA)
    (hR : env.find? ConLeche.eqReflName = some ConLeche.eqReflA)
    (heq : EqLaw m) :
    BlockCtorFacts m (eqBlock (V := V)) [ConLeche.uN] 0 0
      (ConLeche.eqReflA.toConstantVal, 0) := by
  refine ⟨hR, rfl, ?_⟩
  refine
    { resid := ⟨_, [.bvar 0], rfl, rfl⟩
      read := eqReflA_type_read hE
      len := fun _ => rfl
      lenE := fun _ => rfl
      idxLen := rfl
      idxRead := fun ψ => ?_
      bits := fun ψ d hd => ?_
      okTy := fun ψ ρ => ?_
      below := fun _ => ⟨trivial, Nat.zero_lt_one, trivial⟩
      belowE := fun _ E hE' => ?_
      params := fun ψ₁ ψ₂ h => ?_
      srcLen := rfl
      srcBnd := fun _ h => (nomatch h)
      srcIdx := fun j l h => (nomatch h)
      srcProp := fun _ _ _ _ _ => trivial
      opened :=
        { residRes := fun e he => ?_
          ord := fun i x h => (nomatch h)
          recF := fun i x h => (nomatch h)
          reflF := fun i x h => (nomatch h)
          nestF := fun i x q h => (nomatch h)
          nestReflF := fun i x q h => (nomatch h)
          kinds := fun i h => (nomatch h) }
      opens := ⟨_, rfl, rfl⟩
      ksLen := rfl
      xLen := rfl
      pLen := rfl
      xIdx := fun k x h => (nomatch h)
      pIdx := fun k x h => ?_
      idxEq := rfl
      domRead := fun _ i x h => (nomatch h)
      eissLen := fun _ => rfl
      eisRead := fun _ i x h => (nomatch h)
      eisLen := fun _ i _ _ h => (nomatch h)
      recEntry := fun _ i _ _ h => (nomatch h)
      nestEisRead := fun _ i x q h => (nomatch h)
      nestEisLen := fun _ i q _ _ h => (nomatch h)
      nestEntry := fun _ i q _ _ h => (nomatch h)
      eissParams := fun _ _ _ => rfl
      eissBelow := fun _ i E h => (nomatch h)
      ordNone := fun _ _ _ _ => rfl
      tssLen := fun _ => rfl
      tssNone := fun _ _ _ => rfl
      tssBits := fun _ _ d h => (nomatch h)
      tssPiBits := fun _ _ d h => (nomatch h)
      tssBelow := fun _ _ => trivial
      tssParams := fun _ _ _ => rfl
      reflOpen := fun _ i x h => (nomatch h)
      eisLenRefl := fun _ i _ _ h => (nomatch h)
      reflEntry := fun _ i _ _ h => (nomatch h)
      nestReflOpen := fun _ i x q h => (nomatch h)
      nestEisLenRefl := fun _ i q _ _ h => (nomatch h)
      nestReflEntry := fun _ i q _ _ h => (nomatch h) }
  -- the residual's index argument reads as the left parameter
  · show DenoteMetaSpine m.acval env ψ 2 [eqFv1] [AnnotTerm.bvar 0]
    exact DenoteMetaSpine.cons (by rw [show eqFv1 = Expr.fvar 1 eqFv0 from rfl,
      denoteMeta_fvar]) DenoteMetaSpine.nil
  -- both binders are `Prop`-regime, as the block's sort is
  · show ((eqBlock (V := V)).resSort.eval ψ = 0 ↔ d.2.1 = 0)
    have : d ∈ [((0 : Nat), (0 : Nat), AnnotTerm.sort (ψ ConLeche.uN)),
        (0, 0, AnnotTerm.bvar 0)] := hd
    rcases List.mem_cons.mp this with rfl | h2
    · exact Iff.rfl
    · rcases List.mem_cons.mp h2 with rfl | h3
      · exact Iff.rfl
      · exact nomatch h3
  -- the type's grading: the spine's reading is a proposition (`EqLaw`)
  · obtain ⟨-, hgrade⟩ := heq hE ψ
    refine ⟨⟨trivial, fun A hA => ⟨trivial, fun a ha => ?_⟩⟩,
      ⟨trivial, fun A hA => ⟨trivial, fun a ha => ?_, fun _ A' hA' => ?_⟩, fun _ A hA => ?_⟩⟩
    · exact (hgrade (cons a (cons A ρ)) (.bvar 1) (.bvar 0) (.bvar 0)
        ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ hA ha ha).1.1
    · exact (hgrade (cons a (cons A ρ)) (.bvar 1) (.bvar 0) (.bvar 0)
        ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ hA ha ha).1.2
    · exact (hgrade (cons A' (cons A ρ)) (.bvar 1) (.bvar 0) (.bvar 0)
        ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ hA hA' hA').2
    · exact piR_zero_mem_univZero
  -- the index reading is bounded
  · rcases List.mem_singleton.mp hE' with rfl
    exact Nat.zero_lt_two
  -- the readings depend on the level parameter only
  · have hu : ψ₁ ConLeche.uN = ψ₂ ConLeche.uN := h ConLeche.uN (List.mem_singleton.mpr rfl)
    refine ⟨?_, rfl⟩
    show [((0 : Nat), (0 : Nat), AnnotTerm.sort (ψ₁ ConLeche.uN)), (0, 0, AnnotTerm.bvar 0)]
      = [((0 : Nat), (0 : Nat), AnnotTerm.sort (ψ₂ ConLeche.uN)), (0, 0, AnnotTerm.bvar 0)]
    rw [hu]
  -- the residual's index argument resolves
  · rcases List.mem_singleton.mp he with rfl
    rfl
  · match k, h with
    | 0, h => exact ⟨_, (Option.some.inj h).symm⟩
    | 1, h => exact ⟨_, (Option.some.inj h).symm⟩

/-! ## The block model's clauses -/

/-- **`Eq` is represented by its block model**: the syntactic clauses
are the pin's own records (`mI = 5`, `rP = 4`, one rule, the former's
three-binder telescope), the semantic ones the constant operator of
truth sets — whose fibre IS the constructor's index equation and whose
carrier IS the environment's `EqLaw` value `eqv a b`.

The constructor's typing (`hctorTy`, `EnvModelM.mem_type` at
`Eq.refl`) is a premise: `Eq.refl`'s value is not pinned — it is a
proof, and the only thing that says so is its type's reading being a
proposition. -/
theorem eqBlock_isBlockModel {env : Env} {m : EnvModel V env} {cvR : ConstantVal}
    {rules : List RecRule}
    (hE : env.find? ConLeche.eqName = some ConLeche.eqA)
    (hR : env.find? ConLeche.eqReflName = some ConLeche.eqReflA)
    (heq : EqLaw m)
    (hctorTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.acval ConLeche.eqReflName ψ)
        ∈ˢ interp V ρ (mkPisAV ((eqBlock (V := V)).dsF 0 0 ψ)
            (ctorBodyAVI m ConLeche.eqName 2 0 ψ ((eqBlock (V := V)).esF 0 0 ψ))))
    (hrules : rules ≠ [] → rules.map (·.ctor) = [ConLeche.eqReflName]) :
    IsBlockModel m ConLeche.eqName ConLeche.eqA.toConstantVal cvR 5 4 rules
      (eqBlock (V := V)) 0 where
  memberLt := Nat.one_pos
  member := rfl
  strip := ⟨_, .zero, rfl, fun _ => rfl⟩
  isProp := rfl
  mI := rfl
  rP := rfl
  rules := hrules
  former :=
    { read := fun ψ => eqA_type_read ψ
      len := fun _ => rfl
      bits := fun ψ d hd => by
        have hd' : d ∈ [((0 : Nat), (1 : Nat), AnnotTerm.sort (ψ ConLeche.uN)),
            (0, 1, AnnotTerm.bvar 0), (0, 1, AnnotTerm.bvar 1)] := hd
        rcases List.mem_cons.mp hd' with rfl | h2
        · exact Nat.one_ne_zero
        rcases List.mem_cons.mp h2 with rfl | h3
        · exact Nat.one_ne_zero
        rcases List.mem_cons.mp h3 with rfl | h4
        · exact Nat.one_ne_zero
        · exact nomatch h4
      okTy := fun ψ ρ =>
        ⟨⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial⟩⟩⟩,
          ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => ⟨trivial, fun _ _ => trivial,
            fun h => (nomatch h)⟩, fun h => (nomatch h)⟩, fun h => (nomatch h)⟩⟩
      below := fun _ => ⟨trivial, Nat.zero_lt_one, Nat.one_lt_two, trivial⟩
      params := fun ψ₁ ψ₂ h => by
        have hu : ψ₁ ConLeche.uN = ψ₂ ConLeche.uN :=
          h ConLeche.uN (List.mem_singleton.mpr rfl)
        refine ⟨?_, rfl⟩
        show [((0 : Nat), (1 : Nat), AnnotTerm.sort (ψ₁ ConLeche.uN)), (0, 1, AnnotTerm.bvar 0),
            (0, 1, AnnotTerm.bvar 1)]
          = [((0 : Nat), (1 : Nat), AnnotTerm.sort (ψ₂ ConLeche.uN)), (0, 1, AnnotTerm.bvar 0),
            (0, 1, AnnotTerm.bvar 1)]
        rw [hu] }
  ctors := fun mm' j cA hmm hj => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (ConLeche.eqReflA.toConstantVal, 0) := (Option.some.inj hj).symm
      exact eqBlock_ctorData hE hR heq
  memsFound := fun mm' hmm => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    exact ⟨_, _, hE⟩
  pinsFound := fun _ h => (nomatch h)
  tgtsLt := fun _ _ _ _ _ h => (nomatch h)
  idxRes := fun _ _ _ _ _ e he => by
    rcases List.mem_singleton.mp he with rfl
    rfl
  uParams := fun _ _ ψ₁ ψ₂ h => by
    show ψ₁ ConLeche.uN = ψ₂ ConLeche.uN
    exact h ConLeche.uN (List.mem_singleton.mpr rfl)
  paramsIff := fun _ _ _ _ _ _ _ => Iff.rfl
  idxOk := fun ψ ρp hρp mm' hmm => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    exact eqBlock.idxOk_of hρp
  functor := fun ψ ρp _ => ⟨eqBlock.mono ψ ρp, eqBlock.maps ψ ρp, eqBlock.closed ψ ρp⟩
  fibre := fun ψ ρp _ X _ mm' hmm t ht x => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    rw [eqBlock.Phi_app, app_graph ht, eqv_eq_truthVal]
    constructor
    · intro hx
      refine ⟨0, [], Nat.one_pos, ⟨trivial, fun l hl => ?_⟩, eq_pt_of_mem_truthVal hx⟩
      obtain rfl : l = 0 := Nat.lt_one_iff.mp hl
      exact of_mem_truthVal hx
    · rintro ⟨j, fs, hj, ⟨hfit, hidx⟩, rfl⟩
      obtain rfl : j = 0 := Nat.lt_one_iff.mp hj
      obtain rfl : fs = [] := List.eq_nil_of_length_eq_zero (FitsFrom.length_eq hfit)
      have h0 := hidx 0 Nat.one_pos
      show (pt : V) ∈ˢ truthVal (ρp 0 = projS 0 t)
      exact pt_mem_truthVal (by exact h0)
  pinShape := fun _ h => (nomatch h)
  pinMem := fun _ _ _ _ _ _ h => (nomatch h)
  pinMono := fun _ _ _ _ _ _ _ _ _ h => (nomatch h)
  auxFunctor := fun ψ ρp _ => ⟨eqBlock.mono ψ ρp, eqBlock.maps ψ ρp, eqBlock.closed ψ ρp⟩
  auxCompose := fun _ _ => composeΦ_zero.symm
  auxPinsCar := fun _ _ _ _ h => nomatch h
  pinLeaf := fun _ h => (nomatch h)
  leaf := fun ψ ρ as is hsp hi => by
    match as, hsp with
    | [A, a], hsp =>
      match is, hi with
      | [b], hi =>
        obtain ⟨hA, ha⟩ : A ∈ˢ (univ (ψ ConLeche.uN) : V) ∧ a ∈ˢ A := ⟨hsp.1, hsp.2.1⟩
        have hb : b ∈ˢ A := hi.1
        have ht : (eqBlock (V := V)).tup ψ 0 [b] ∈ˢ (eqBlock (V := V)).idx ψ (consList [A, a] ρ) 0 :=
          (eqBlock (V := V)).tupMem (ψ := ψ) (ρp := consList [A, a] ρ) (mm' := 0) (is := [b]) hi
        rw [eqBlock.lfp_app ψ (consList [A, a] ρ) ht]
        show ([A, a] ++ [b]).foldl app (interp V ρ (m.acval ConLeche.eqName ψ)) = _
        rw [show ([A, a] ++ [b]).foldl app (interp V ρ (m.acval ConLeche.eqName ψ))
          = app (app (app (interp V ρ (m.acval ConLeche.eqName ψ)) A) a) b from rfl,
          (heq hE ψ).1 ρ A a b hA ha hb]
        show eqv a b = eqv a (projS 0 ((eqBlock (V := V)).tup ψ 0 [b]))
        rcases eqBlock.projS_tup (u := ψ ConLeche.uN) hA hb with h | ⟨hu, hbpt, hpj⟩
        · show eqv a b = eqv a (projS 0 (tupW (ψ ConLeche.uN) [b]))
          rw [h]
        · show eqv a b = eqv a (projS 0 (tupW (ψ ConLeche.uN) [b]))
          rw [hpj, hbpt]
  ctor := fun mm' j cA hmm hj ψ ρ as fs hsp hsp₂ => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (ConLeche.eqReflA.toConstantVal, 0) := (Option.some.inj hj).symm
      match as, hsp with
      | [A, a], hsp =>
        obtain rfl : fs = [] := by
          have := SpineFit.length_eq hsp₂
          exact List.eq_nil_of_length_eq_zero this
        obtain ⟨hA, ha⟩ : A ∈ˢ (univ (ψ ConLeche.uN) : V) ∧ a ∈ˢ A := ⟨hsp.1, hsp.2.1⟩
        obtain ⟨-, hgrade⟩ := heq hE ψ
        have h1 := hctorTy ψ ρ
        show ([A, a] ++ []).foldl app (interp V ρ (m.acval ConLeche.eqReflName ψ)) = pt
        have h2 : app (interp V ρ (m.acval ConLeche.eqReflName ψ)) A
            ∈ˢ piR 0 A (fun x => interp V (cons x (cons A ρ))
              (ctorBodyAVI m ConLeche.eqName 2 0 ψ ((eqBlock (V := V)).esF 0 0 ψ))) :=
          app_mem_piR h1 hA (fun _ _ _ => piR_zero_mem_univZero)
        have h3 := app_mem_piR h2 ha (fun _ x hx =>
          (hgrade (cons x (cons A ρ)) (.bvar 1) (.bvar 0) (.bvar 0)
            ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ hA hx hx).2)
        exact eq_pt_of_mem_univZero
          ((hgrade (cons a (cons A ρ)) (.bvar 1) (.bvar 0) (.bvar 0)
            ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ hA ha ha).2) h3
  mkZero := fun _ _ _ _ _ => rfl
  mkInj := fun _ hw => (nomatch hw)

/-! ## The read-back -/

/-- **`Eq`'s group, read back**: the one-member group with the single
constructor, two parameters and one index.  Three `Env.find?` results
are the reading's only environment inputs — the former, the recursor
(the parameter count comes off `Eq.refl`'s record, the motive walk off
the recursor's type past its two parameters) and the rule's
constructor. -/
theorem containerInfo?_eqA {env : Env}
    (hT : env.find? ConLeche.eqName = some ConLeche.eqA)
    (hR : env.find? (ConLeche.eqName.str "rec") = some ConLeche.eqRecA)
    (hC : env.find? ConLeche.eqReflName = some ConLeche.eqReflA) :
    ConLeche.containerInfo? env ConLeche.eqName
      = some ⟨2, [⟨ConLeche.eqName, [ConLeche.uN], ConLeche.eqA.toConstantVal.type,
        [⟨ConLeche.eqReflName, ConLeche.eqReflA.toConstantVal.type, 0⟩]⟩]⟩ := by
  have hE : ConLeche.eqName = Name.anonymous.str "Eq" := rfl
  have hCE : ConLeche.eqReflName = (Name.anonymous.str "Eq").str "refl" := rfl
  rw [hE] at hT hR
  rw [hCE] at hC
  have hmot : ConLeche.containerMotiveMember? env 2 0
      (Expr.forallE (.bvar 1)
        (Expr.forallE (.app (.app (.app (.const (Name.anonymous.str "Eq")
              [.param (Name.anonymous.str "u")]) (.bvar 2)) (.bvar 1)) (.bvar 0))
          (.sort (.param (Name.anonymous.str "u_1"))) { pw := .never }) { pw := .never })
      = some (Name.anonymous.str "Eq") := by
    simp +decide [ConLeche.containerMotiveMember?, Expr.piBinders, Expr.getAppFn,
      Expr.getAppArgs, hT]
  have hmot2 : ConLeche.containerMotiveMember? env 2 1
      (Expr.app (.app (.bvar 0) (.bvar 1))
        (.app (.app (.const ((Name.anonymous.str "Eq").str "refl")
          [.param (Name.anonymous.str "u")]) (.bvar 2)) (.bvar 1))) = none := by
    simp [ConLeche.containerMotiveMember?, Expr.piBinders]
  simp +decide [ConLeche.containerInfo?, hT, hR, hC, ConLeche.eqA, ConLeche.eqRecA,
    ConLeche.eqReflA, Expr.stripPis, ConLeche.containerMembersGo, hmot, hmot2, Option.bind,
    ConLeche.eqReflName, ConLeche.eqName, ConLeche.uN]
  exact ⟨rfl, rfl⟩

/-! ## The group -/

/-- **`Eq`'S OWN-PIN TABLE IS EMPTY** (task #315 M7-3 session 17,
K.49) — `natBlock_ownPins` at the two-parameter block.  `Eq` has no
mimic recursor either; `hmim` is `checkBasisDecl`'s own certification
(`basisOwnMimicsOk`, the last conjunct of `DeclBasisRun`) at `Eq`. -/
theorem eqBlock_ownPins {env : Env}
    (hT : env.find? ConLeche.eqName = some ConLeche.eqA)
    (hR : env.find? (ConLeche.eqName.str "rec") = some ConLeche.eqRecA)
    (hC : env.find? ConLeche.eqReflName = some ConLeche.eqReflA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.eqName 0 = true) :
    ContainerOwnPinsSyn (V := V) env (eqBlock (V := V)) :=
  ContainerOwnPinsSyn.of_noMimics hmim fun i hi => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp (show i < 1 from hi)
    exact ⟨_, _, containerInfo?_eqA hT hR hC, rfl, rfl⟩

/-- **`Eq`'s group carries its block model**.  The `inj` clause is the
one a pinned block CAN carry: `Eq` is `Prop`-valued, so `injW 0 j _`
IS the point, which is `Eq.refl`'s value. -/
theorem eqBlock_containerModeled {env : Env} {m : EnvModel V env}
    (hE : env.find? ConLeche.eqName = some ConLeche.eqA)
    (hR : env.find? ConLeche.eqReflName = some ConLeche.eqReflA)
    (hRec : env.find? (ConLeche.eqName.str "rec") = some ConLeche.eqRecA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.eqName 0 = true)
    (heq : EqLaw m)
    (hformerTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.acval ConLeche.eqName ψ)
        ∈ˢ interp V ρ (mkPisAV ((eqBlock (V := V)).ppsM 0 ψ)
            (.sort ((eqBlock (V := V)).w ψ))))
    (hctorTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.acval ConLeche.eqReflName ψ)
        ∈ˢ interp V ρ (mkPisAV ((eqBlock (V := V)).dsF 0 0 ψ)
            (ctorBodyAVI m ConLeche.eqName 2 0 ψ ((eqBlock (V := V)).esF 0 0 ψ)))) :
    ContainerModeled m ⟨2, [⟨ConLeche.eqName, [ConLeche.uN],
        ConLeche.eqA.toConstantVal.type,
        [⟨ConLeche.eqReflName, ConLeche.eqReflA.toConstantVal.type, 0⟩]⟩]⟩
      (eqBlock (V := V)) where
  k := rfl
  namesLen := rfl
  nP := rfl
  reps := fun c hc => by
    obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
    exact ⟨_, ConLeche.eqA.toConstantVal, 5, 4, [],
      eqBlock_isBlockModel hE hR heq hctorTy (fun h => absurd rfl h)⟩
  typed := fun ψ => by
    refine ⟨fun t ht ρ => ?_, ⟨fun c hc j cA hj ρ => ?_,
      PinsTyped.of_noPins (d := eqBlock (V := V)) rfl ψ⟩⟩
    · obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      exact hformerTy ψ ρ
    · obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
      match j, hj with
      | 0, hj =>
        obtain rfl : cA = (ConLeche.eqReflA.toConstantVal, 0) := (Option.some.inj hj).symm
        exact hctorTy ψ ρ
  inj := fun _ ψ _ j fs => by
    show (pt : V) = injW ((eqBlock (V := V)).w ψ) j (mkTower (fs ++ [pt]))
    rw [show (eqBlock (V := V)).w ψ = 0 from rfl, injW_zero]
  member := fun i M hM => by
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ M = ⟨ConLeche.eqName, [ConLeche.uN],
        ConLeche.eqA.toConstantVal.type,
        [⟨ConLeche.eqReflName, ConLeche.eqReflA.toConstantVal.type, 0⟩]⟩ := by
      match i, hM with
      | 0, hM => exact ⟨rfl, (Option.some.inj hM).symm⟩
    exact ⟨rfl, rfl, ConLeche.eqA.toConstantVal, 5, 4, [],
      eqBlock_isBlockModel hE hR heq hctorTy (fun h => absurd rfl h)⟩
  frame := fun _ _ _ _ => Iff.rfl
  ordFree := fun _ _ _ _ _ _ h => (nomatch h)
  nestMention := fun _ h => (nomatch h)
  nestArgsMention := fun _ _ _ _ _ _ _ _ _ h _ => nomatch h
  ctorProjFree := fun i j cA hi hj T hT n => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    obtain rfl := List.mem_singleton.mp hT
    match j, hj with
    | 0, hj =>
      obtain rfl : cA = (ConLeche.eqReflA.toConstantVal, 0) := (Option.some.inj hj).symm
      simp [ConLeche.eqReflA, ConLeche.ConstantInfo.toConstantVal]
  pinsNotMembers := fun _ h => (nomatch h)
  pinNP := fun _ h => (nomatch h)
  pinConts := fun _ h => (nomatch h)
  ownPins := eqBlock_ownPins hE hRec hR hmim
  pinψ := fun _ h => (nomatch h)
  pinParams := fun _ _ _ => ContainerPinParams.of_noPins rfl

/-- **`Eq`'s pins' laws**: no pins. -/
theorem eqBlock_pinRecLaws {env : Env} {m : EnvModel V env} :
    PinRecLaws m (eqBlock (V := V)) (fun _ => default) where
  tgtsLt := fun _ _ _ _ h => (nomatch h)
  idxOk := fun _ _ _ _ h => (nomatch h)
  fibre := fun _ _ _ _ _ _ _ h => (nomatch h)
  mkZero := fun _ _ _ _ _ => rfl
  mkInj := fun _ _ _ h => (nomatch h)
  injW := fun _ _ h => (nomatch h)
  ind := fun _ _ _ _ _ _ _ _ h => (nomatch h)

/-- **`Eq` carries its block's model** at any assignment that sends its
group to `eqBlock`: the two typings come from the environment model's
own `mem_type` at the two stored constants, the carrier's value from
its `eq_law`. -/
theorem eqBlockAt {env : Env} (mp : EnvModelM V μ env)
    (hE : env.find? ConLeche.eqName = some ConLeche.eqA)
    (hR : env.find? ConLeche.eqReflName = some ConLeche.eqReflA)
    (hRec : env.find? (ConLeche.eqName.str "rec") = some ConLeche.eqRecA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.eqName 0 = true)
    {B : ContainerInfo → BlockModel V}
    (hB : B ⟨2, [⟨ConLeche.eqName, [ConLeche.uN], ConLeche.eqA.toConstantVal.type,
        [⟨ConLeche.eqReflName, ConLeche.eqReflA.toConstantVal.type, 0⟩]⟩]⟩
      = eqBlock (V := V)) :
    BlockAt mp.base2 B ⟨2, [⟨ConLeche.eqName, [ConLeche.uN], ConLeche.eqA.toConstantVal.type,
        [⟨ConLeche.eqReflName, ConLeche.eqReflA.toConstantVal.type, 0⟩]⟩]⟩ := by
  have hformerTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (mp.base2.acval ConLeche.eqName ψ)
        ∈ˢ interp V ρ (mkPisAV ((eqBlock (V := V)).ppsM 0 ψ)
            (.sort ((eqBlock (V := V)).w ψ))) := by
    intro ψ ρ
    exact mp.mem_type ConLeche.eqA (ConLeche.find?_mem hE) ψ _ (eqA_type_read ψ) ρ
  have hctorTy : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (mp.base2.acval ConLeche.eqReflName ψ)
        ∈ˢ interp V ρ (mkPisAV ((eqBlock (V := V)).dsF 0 0 ψ)
            (ctorBodyAVI mp.base2 ConLeche.eqName 2 0 ψ ((eqBlock (V := V)).esF 0 0 ψ))) := by
    intro ψ ρ
    exact mp.mem_type ConLeche.eqReflA (ConLeche.find?_mem hR) ψ _ (eqReflA_type_read hE ψ) ρ
  refine ⟨hB ▸ eqBlock_containerModeled hE hR hRec hmim (mp.eq_law) hformerTy hctorTy,
    ⟨fun _ => default, ?_, ?_⟩⟩
  · exact hB ▸ eqBlock_pinRecLaws
  · rw [hB]; exact fun q hq => (nomatch hq)

end ConLeche.Model


