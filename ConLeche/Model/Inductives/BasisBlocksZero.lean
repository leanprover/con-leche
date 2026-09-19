module

public import ConLeche.Model.Inductives.NestedPremise
public section

/-!
# The block models of the ZERO-CONSTRUCTOR pinned basis blocks (task #315, M7-4)

`EnvBlockModels` (`NestedPremise.lean`, the `EnvModelB` field) demands
a block model of EVERY stored container, and the five pinned basis
blocks — `Nat`, `Eq`, `PUnit`, `Empty`, `False` — are stored
inductives that `containerInfo?` reads (DESIGN §U.31 (e) 3).  This
module carries the two blocks with NO constructors, `Empty` and
`False`, whose block model is the same object twice, one universe
apart:

* `k = 1`, `nP = 0`, no indices, no constructors, no pins — the
  `BlockModel.ofNative` shape with an empty constructor list;
* the tuple operator `Φ` is the CONSTANT everywhere-empty family
  `graph (fun _ => empty) unitSet` over the one-point index-tuple set
  (`idxSet u ρp [] = unitSet`), so it is its own closed tuple and its
  least pre-fixed tuple has empty fibres — which is exactly the pinned
  carrier (`bval .empty = empty` at both levels, `False`'s in `Prop`
  where the empty set is the false proposition);
* the injections are the tagged towers `injW (d.w ψ) j (mkTower (fs ++
  [pt]))` (`ContainerModeled.inj`) — vacuously, there being no
  constructor to inject.

The read-back (`containerInfo? env T = some ci` at the environment
that stores the block) is COMPUTED from the two stored records, one
`Env.find?` rewrite per lookup the reading makes, with no case split
inside the unfolded body.
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

/-! ## The block model -/

/-- **The block model of a zero-constructor pinned basis block**: one
member, no parameters, no indices, no constructors, no pins; the
operator the constant everywhere-empty family over the one-point
index-tuple set, the injections the tagged towers. -/
@[expose] noncomputable def zeroCtorBlock (T : Name) (resSort : Level) (env₀ : Env) :
    BlockModel V where
  nP := 0
  k := 1
  resSort := resSort
  isProp := (Level.isEquiv resSort .zero == some true)
  large := true
  env₀ := env₀
  memberNames := [T]
  nIdxs := [0]
  ppsM := fun _ _ => []
  uM := fun _ _ => 0
  ctorsM := fun _ => []
  idxF := fun _ _ => []
  dsF := fun _ _ _ => []
  esF := fun _ _ _ => []
  srcsF := fun _ _ => []
  ksF := fun _ _ => []
  tgts := fun _ _ _ => 0
  fvsPF := fun _ _ => []
  xFvsF := fun _ _ => []
  xrestF := fun _ _ => .sort .zero
  eissF := fun _ _ _ => []
  tssF := fun _ _ _ => []
  pins := []
  Φ := fun _ _ _ _ => graph (fun _ => empty) unitSet
  pinCar := fun _ _ _ _ => pt
  Ψaux := fun _ _ _ _ => graph (fun _ => empty) unitSet
  pinCtors := fun _ => default
  inj := fun ψ _ j fs => injW (resSort.eval ψ) j (mkTower (fs ++ [pt]))

namespace zeroCtorBlock

variable {T : Name} {resSort : Level} {env₀ : Env}

local notation "D" => (zeroCtorBlock (V := V) T resSort env₀)

/-- The index-tuple set is the one-point set at every frame. -/
theorem idx_eq (ψ : Name → Nat) (ρp : Nat → V) (mm : Nat) : (D).idx ψ ρp mm = unitSet := rfl

/-- The parameter telescope is empty. -/
theorem params_eq (ψ : Name → Nat) : (D).params ψ = ([] : List AnnotTerm) := rfl

/-- The member's index telescope is empty. -/
theorem IdsM_eq (mm : Nat) (ψ : Name → Nat) : (D).IdsM mm ψ = ([] : List AnnotTerm) := rfl

/-- The operator maps the tuple space into itself. -/
theorem maps (ψ : Name → Nat) (ρp : Nat → V) :
    MapsTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) :=
  fun _ _ _ _ => graph_mem_famSpace fun _ _ => empty_mem_univ _

/-- The operator is monotone: it is constant. -/
theorem mono (ψ : Name → Nat) (ρp : Nat → V) :
    MonoTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) :=
  fun _ _ _ _ _ => TupleLe.refl _ _ _

/-- The operator is its own closed tuple. -/
theorem closed (ψ : Name → Nat) (ρp : Nat → V) :
    ∃ L, IsClosedTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) L :=
  ⟨fun _ => graph (fun _ => empty) unitSet,
    ⟨fun _ _ => graph_mem_famSpace fun _ _ => empty_mem_univ _, TupleLe.refl _ _ _⟩⟩

/-- **The carrier's fibre is empty**: the least pre-fixed tuple of a
constant empty operator. -/
theorem Phi_app (ψ : Name → Nat) (ρp X : Nat → V) (mm : Nat) :
    (D).Φ ψ ρp X mm = graph (fun _ => (empty : V)) ((D).idx ψ ρp mm) := rfl

theorem lfp_app (ψ : Name → Nat) (ρp : Nat → V) {t : V} (ht : t ∈ˢ (D).idx ψ ρp 0) :
    app (lfpTuple ((D).w ψ) (D).k ((D).idx ψ ρp) ((D).Φ ψ ρp) 0) t = (empty : V) := by
  rw [← app_lfpTuple_eq (closed ψ ρp) (mono ψ ρp) (maps ψ ρp) Nat.one_pos ht, Phi_app]
  exact app_graph ht

/-- The one index tuple is in the index-tuple set. -/
theorem tup_mem (ψ : Name → Nat) (ρp : Nat → V) : (D).tup ψ 0 [] ∈ˢ (D).idx ψ ρp 0 :=
  (D).tupMem (ψ := ψ) (ρp := ρp) (mm' := 0) (is := []) trivial

end zeroCtorBlock

/-! ## The block model's clauses -/

/-- **A zero-constructor pinned basis block is represented by its block
model**: the syntactic clauses are the pin's own record (a bare sort
for the former, `mI = rP = 1` and no rules for the recursor), the
semantic ones the constant empty operator of the section above, and
the leaf is the pinned value `empty` — `Empty`'s in `Type`, `False`'s
in `Prop`. -/
theorem zeroCtorBlock_isBlockModel {env : Env} {m : EnvModel V env}
    {T : Name} {resSort : Level} {cvT cvR : ConstantVal} {caps : IndCaps}
    (hT : env.find? T = some (.indInfo cvT caps))
    (hty : cvT.type = .sort resSort) {env₀ : Env}
    (hval : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (m.acval T ψ) = (empty : V))
    (hsort : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvT.levelParams, ψ₁ p = ψ₂ p) →
      resSort.eval ψ₁ = resSort.eval ψ₂) :
    IsBlockModel m T cvT cvR 1 1 [] (zeroCtorBlock (V := V) T resSort env₀) 0 where
  memberLt := Nat.one_pos
  member := rfl
  strip := ⟨[], resSort, by rw [hty]; rfl, fun _ => rfl⟩
  isProp := rfl
  mI := rfl
  rP := rfl
  rules := fun h => absurd rfl h
  former :=
    { read := fun ψ => by rw [hty, denoteMeta_sort]; rfl
      len := fun _ => rfl
      bits := fun _ _ h => nomatch h
      okTy := fun _ _ => ⟨trivial, trivial⟩
      below := fun _ => trivial
      params := fun ψ₁ ψ₂ h => ⟨rfl, hsort ψ₁ ψ₂ h⟩ }
  ctors := fun _ j _ _ h => nomatch h
  memsFound := fun mm' hmm => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    exact ⟨cvT, caps, hT⟩
  pinsFound := fun _ h => nomatch h
  tgtsLt := fun _ _ _ _ _ h => nomatch h
  idxRes := fun _ j _ _ h => nomatch h
  uParams := fun _ _ _ _ _ => rfl
  paramsIff := fun _ j _ _ h => nomatch h
  idxOk := fun _ _ _ _ _ => ⟨trivial, trivial⟩
  functor := fun ψ ρp _ => ⟨zeroCtorBlock.mono ψ ρp, zeroCtorBlock.maps ψ ρp,
    zeroCtorBlock.closed ψ ρp⟩
  fibre := fun ψ ρp _ X _ mm' hmm t ht x => by
    obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
    rw [zeroCtorBlock.Phi_app ψ ρp X 0, app_graph ht]
    exact ⟨fun hx => absurd hx (not_mem_empty x), fun ⟨j, _, hj, _, _⟩ => nomatch hj⟩
  pinShape := fun _ h => nomatch h
  pinMem := fun _ _ _ _ _ _ h => nomatch h
  pinMono := fun _ _ _ _ _ _ _ _ _ h => nomatch h
  auxFunctor := fun ψ ρp _ => ⟨zeroCtorBlock.mono ψ ρp, zeroCtorBlock.maps ψ ρp, zeroCtorBlock.closed ψ ρp⟩
  auxCompose := fun _ _ => composeΦ_zero.symm
  auxPinsCar := fun _ _ _ _ h => nomatch h
  auxPinIdx := fun _ h => nomatch h
  auxFibre := BlockModel.auxFibre_of_noPins _ rfl (fun _ _ => rfl)
    (fun _ _ _ _ _ => Nat.one_pos)
    (fun ψ ρp _ X _ mm' hmm t ht x => by
        obtain rfl : mm' = 0 := Nat.lt_one_iff.mp hmm
        rw [zeroCtorBlock.Phi_app ψ ρp X 0, app_graph ht]
        exact ⟨fun hx => absurd hx (not_mem_empty x), fun ⟨j, _, hj, _, _⟩ => nomatch hj⟩)
  pinLeaf := fun _ h => nomatch h
  leaf := fun ψ ρ as is hsp hi => by
    obtain rfl : as = [] := List.eq_nil_of_length_eq_zero (SpineFit.length_eq hsp)
    obtain rfl : is = [] := List.eq_nil_of_length_eq_zero (SpineFit.length_eq hi)
    rw [List.append_nil, List.foldl_nil, hval,
      zeroCtorBlock.lfp_app ψ (consList [] ρ) (zeroCtorBlock.tup_mem ψ (consList [] ρ))]
  ctor := fun _ j _ _ h => nomatch h
  mkZero := fun ψ hw _ j fs => by
    show injW (resSort.eval ψ) j (mkTower (fs ++ [pt])) = pt
    rw [show resSort.eval ψ = 0 from hw, injW_zero]
  mkInj := fun _ _ _ hmm _ _ _ _ hj => nomatch hj

/-- **The pins' laws at a block without pins**: every clause but
`mkZero` is guarded by `q < d.nPins`, and `mkZero` holds of the
default `PinCtors` (whose injection is the point). -/
theorem zeroCtorBlock_pinRecLaws {env : Env} {m : EnvModel V env}
    {T : Name} {resSort : Level} {env₀ : Env} :
    PinRecLaws m (zeroCtorBlock (V := V) T resSort env₀) (fun _ => default) where
  tgtsLt := fun _ _ _ _ h => nomatch h
  idxOk := fun _ _ _ _ h => nomatch h
  fibre := fun _ _ _ _ _ _ _ h => nomatch h
  mkZero := fun _ _ _ _ _ => rfl
  mkInj := fun _ _ _ h => nomatch h
  injW := fun _ _ h => nomatch h
  ind := fun _ _ _ _ _ _ _ _ h => nomatch h

/-- **A ZERO-CONSTRUCTOR PINNED BLOCK'S OWN-PIN TABLE IS EMPTY**
(task #315 M7-3 session 17, K.49 and DESIGN §U.74) — the clause
`ContainerOwnPinsSyn` at `Empty`'s and `False`'s block model.

Stated at the READ-BACK rather than at `Env.find?` results because the
block model itself is generic in the former's name: the two
instantiations supply `containerInfo?_emptyA` and
`containerInfo?_falseA`.  `hmim` is `checkBasisDecl`'s own
certification (`basisOwnMimicsOk`, the last conjunct of
`DeclBasisRun`) at the block's former, which is where
`containerOwnPinsAt`'s walk starts. -/
theorem zeroCtorBlock_ownPins {env env₀ : Env} {T : Name} {resSort : Level}
    {lps : List Name} {ty : Expr}
    (hci : ConLeche.containerInfo? env T = some ⟨0, [⟨T, lps, ty, []⟩]⟩)
    (hmim : ConLeche.blockOwnMimicsOk env T 0 = true) :
    ContainerOwnPinsSyn (V := V) env (zeroCtorBlock (V := V) T resSort env₀) :=
  ContainerOwnPinsSyn.of_noMimics rfl hmim fun i hi => by
    obtain rfl : i = 0 := Nat.lt_one_iff.mp (show i < 1 from hi)
    exact ⟨_, _, hci, rfl, rfl⟩

/-- **The container's block model, in the container's own terms**: the
group `containerInfo?` reads for a zero-constructor pinned basis block
is the one-member group with no constructors, and the block model
above matches it clause by clause. -/
theorem zeroCtorBlock_containerModeled {env : Env} {m : EnvModel V env}
    {T : Name} {resSort : Level} {cvT cvR : ConstantVal} {caps : IndCaps}
    (hT : env.find? T = some (.indInfo cvT caps))
    (hnm : cvT.name = T) (hty : cvT.type = .sort resSort) {env₀ : Env}
    (hval : ∀ (ψ : Name → Nat) (ρ : Nat → V), interp V ρ (m.acval T ψ) = (empty : V))
    (hsort : ∀ ψ₁ ψ₂ : Name → Nat, (∀ p ∈ cvT.levelParams, ψ₁ p = ψ₂ p) →
      resSort.eval ψ₁ = resSort.eval ψ₂)
    (hci : ConLeche.containerInfo? env T = some ⟨0, [⟨T, cvT.levelParams, cvT.type, []⟩]⟩)
    (hmim : ConLeche.blockOwnMimicsOk env T 0 = true) :
    ContainerModeled m ⟨0, [⟨T, cvT.levelParams, cvT.type, []⟩]⟩
      (zeroCtorBlock (V := V) T resSort env₀) where
  k := rfl
  namesLen := rfl
  nP := rfl
  reps := fun c hc => by
    obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
    exact ⟨cvT, cvR, 1, 1, [], zeroCtorBlock_isBlockModel hT hty hval hsort⟩
  typed := fun ψ => by
    refine ⟨fun t ht ρ => ?_, ⟨fun _ _ j _ h => ?_,
      PinsTyped.of_noPins (d := zeroCtorBlock (V := V) T resSort env₀) rfl ψ⟩⟩
    · obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      rw [show (zeroCtorBlock (V := V) T resSort env₀).memberName 0 = T from rfl, hval ψ ρ]
      exact empty_mem_univ _
    · exact absurd h (by simp [zeroCtorBlock])
  inj := fun _ _ _ _ _ => rfl
  member := fun i M hM => by
    obtain ⟨rfl, rfl⟩ : i = 0 ∧ M = ⟨T, cvT.levelParams, cvT.type, []⟩ := by
      match i, hM with
      | 0, hM => exact ⟨rfl, (Option.some.inj hM).symm⟩
    refine ⟨rfl, rfl, cvR, 1, 1, [], ?_⟩
    have hcv : (⟨T, cvT.levelParams, cvT.type⟩ : ConstantVal) = cvT := by
      rw [← hnm]
    rw [hcv]
    exact zeroCtorBlock_isBlockModel hT hty hval hsort
  frame := fun _ _ _ _ => Iff.rfl
  ordFree := fun _ _ _ _ _ hj => nomatch hj
  nestMention := fun _ h => nomatch h
  nestArgsMention := fun _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestArgsMentionAbs := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestArgsMentionAbsRefl := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  nestPinSpineAbs := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ => nomatch h
  ctorProjFree := fun _ _ _ _ hj => nomatch hj
  pinsNotMembers := fun _ h => nomatch h
  pinNP := fun _ h => nomatch h
  pinConts := fun _ h => nomatch h
  ownPins := zeroCtorBlock_ownPins hci hmim
  pinψ := fun _ h => nomatch h
  pinsDistinct := fun _ _ h _ _ => nomatch h
  pinsDistinctAt := fun _ _ _ h _ _ => nomatch h
  pinDsScoped := fun _ h => nomatch h
  pinDsRes := fun _ h => nomatch h
  pinDsRead := fun _ h => nomatch h
  pinParams := fun _ _ _ => ContainerPinParams.of_noPins rfl

/-! ## The read-back at `Empty` -/

/-- **`Empty`'s group, read back**: `containerInfo?` at the environment
that stores the pinned `Empty` block reads the one-member group with
no constructors.  Computed: the two `Env.find?` results are the only
environment inputs the reading has (`emptyA` supplies the parameter
count `0 = piArity - (mI - rP)`, `emptyRecA` the motive walk), and
every other step is closed computation on the pinned records. -/
theorem containerInfo?_emptyA {env : Env}
    (hT : env.find? ConLeche.emptyName = some ConLeche.emptyA)
    (hR : env.find? (ConLeche.emptyName.str "rec") = some ConLeche.emptyRecA) :
    ConLeche.containerInfo? env ConLeche.emptyName
      = some ⟨0, [⟨ConLeche.emptyName, [], ConLeche.emptyA.toConstantVal.type, []⟩]⟩ := by
  have hE : ConLeche.emptyName = Name.anonymous.str "Empty" := rfl
  have hu : ConLeche.uN = Name.anonymous.str "u" := rfl
  rw [hE] at hT hR
  have hmot : ConLeche.containerMotiveMember? env 0 0
      (Expr.forallE (.const (Name.anonymous.str "Empty") []) (.sort (.param (Name.anonymous.str "u")))
        { pw := .never }) = some (Name.anonymous.str "Empty") := by
    simp +decide [ConLeche.containerMotiveMember?, Expr.piBinders, Expr.getAppFn,
      Expr.getAppArgs, hT]
  have hmot2 : ConLeche.containerMotiveMember? env 0 1
      (Expr.const (Name.anonymous.str "Empty") []) = none := by
    simp [ConLeche.containerMotiveMember?, Expr.piBinders]
  simp +decide [ConLeche.containerInfo?, hT, hR, ConLeche.emptyA, ConLeche.emptyRecA,
    Expr.piArity, Expr.stripPis, ConLeche.containerMembersGo, hmot, hmot2, Option.bind, hE]

/-- **`False`'s group, read back** — `Empty`'s computation one universe
down (`False : Prop`, the same zero-constructor record). -/
theorem containerInfo?_falseA {env : Env}
    (hT : env.find? ConLeche.falseName = some ConLeche.falseA)
    (hR : env.find? (ConLeche.falseName.str "rec") = some ConLeche.falseRecA) :
    ConLeche.containerInfo? env ConLeche.falseName
      = some ⟨0, [⟨ConLeche.falseName, [], ConLeche.falseA.toConstantVal.type, []⟩]⟩ := by
  have hE : ConLeche.falseName = Name.anonymous.str "False" := rfl
  rw [hE] at hT hR
  have hmot : ConLeche.containerMotiveMember? env 0 0
      (Expr.forallE (.const (Name.anonymous.str "False") [])
        (.sort (.param (Name.anonymous.str "u"))) { pw := .never })
      = some (Name.anonymous.str "False") := by
    simp +decide [ConLeche.containerMotiveMember?, Expr.piBinders, Expr.getAppFn,
      Expr.getAppArgs, hT]
  have hmot2 : ConLeche.containerMotiveMember? env 0 1
      (Expr.const (Name.anonymous.str "False") []) = none := by
    simp [ConLeche.containerMotiveMember?, Expr.piBinders]
  simp +decide [ConLeche.containerInfo?, hT, hR, ConLeche.falseA, ConLeche.falseRecA,
    Expr.piArity, Expr.stripPis, ConLeche.containerMembersGo, hmot, hmot2, Option.bind, hE]

/-! ## The two blocks -/

/-- **`Empty` carries its block's model** at any assignment that sends
`Empty`'s group to the zero-constructor block model: `Empty : Type` is
the empty family over the one-point index set, the pinned value
`bval .empty [1] = empty`. -/
theorem emptyBlockAt {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.emptyName = some ConLeche.emptyA)
    (hR : env.find? (ConLeche.emptyName.str "rec") = some ConLeche.emptyRecA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.emptyName 0 = true)
    {B : ContainerInfo → BlockModel V}
    (hB : B ⟨0, [⟨ConLeche.emptyName, [], ConLeche.emptyA.toConstantVal.type, []⟩]⟩
      = zeroCtorBlock (V := V) ConLeche.emptyName (.succ .zero) ⟨[]⟩) :
    BlockAt m B ⟨0, [⟨ConLeche.emptyName, [], ConLeche.emptyA.toConstantVal.type, []⟩]⟩ := by
  have hval : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.acval ConLeche.emptyName ψ) = (empty : V) := by
    intro ψ ρ
    have hpd : ConLeche.Verify.pinnedStructT ConLeche.emptyName ψ
        = some (Term.const .empty [1]) := by
      simp +decide [ConLeche.Verify.pinnedStructT]
    rw [acval_basis_pinned hT (by decide) hpd]
    rfl
  refine ⟨hB ▸ zeroCtorBlock_containerModeled (cvR := ConLeche.emptyRecA.toConstantVal)
      hT rfl rfl hval (fun _ _ _ => rfl) (containerInfo?_emptyA hT hR) hmim,
    ⟨fun _ => default, ?_, ?_⟩⟩
  · exact hB ▸ zeroCtorBlock_pinRecLaws
  · rw [hB]; exact fun q hq => nomatch hq

/-- **`False` carries its block's model** — the same block model one
universe down (`False : Prop`, the pinned value `bval .empty [0] =
empty`, the false proposition). -/
theorem falseBlockAt {env : Env} {m : EnvModel V env}
    (hT : env.find? ConLeche.falseName = some ConLeche.falseA)
    (hR : env.find? (ConLeche.falseName.str "rec") = some ConLeche.falseRecA)
    (hmim : ConLeche.blockOwnMimicsOk env ConLeche.falseName 0 = true)
    {B : ContainerInfo → BlockModel V}
    (hB : B ⟨0, [⟨ConLeche.falseName, [], ConLeche.falseA.toConstantVal.type, []⟩]⟩
      = zeroCtorBlock (V := V) ConLeche.falseName .zero ⟨[]⟩) :
    BlockAt m B ⟨0, [⟨ConLeche.falseName, [], ConLeche.falseA.toConstantVal.type, []⟩]⟩ := by
  have hval : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      interp V ρ (m.acval ConLeche.falseName ψ) = (empty : V) := by
    intro ψ ρ
    have hpd : ConLeche.Verify.pinnedStructT ConLeche.falseName ψ
        = some (Term.const .empty [0]) := by
      simp +decide [ConLeche.Verify.pinnedStructT]
    rw [acval_basis_pinned hT (by decide) hpd]
    rfl
  refine ⟨hB ▸ zeroCtorBlock_containerModeled (cvR := ConLeche.falseRecA.toConstantVal)
      hT rfl rfl hval (fun _ _ _ => rfl) (containerInfo?_falseA hT hR) hmim,
    ⟨fun _ => default, ?_, ?_⟩⟩
  · exact hB ▸ zeroCtorBlock_pinRecLaws
  · rw [hB]; exact fun q hq => nomatch hq

end ConLeche.Model
