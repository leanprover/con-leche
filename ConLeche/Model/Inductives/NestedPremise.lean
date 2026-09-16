module

public import ConLeche.Semantics.Inductives.DeclNested
public import ConLeche.Model.Inductives.BlockRecWD
public section

/-!
# The nested route's premise and the block model's record (task #315, M6 s3 / M7)

The definitions `declNested_of`'s two named facts are stated over,
split out of `DeclNestedCore.lean` when the tail grew to the CONCRETE
block model (task #315 M7-2, DESIGN §U.29): the containers' block
models as a PREMISE (`ContainerModeled`, `EnvBlockModels`, read at the
elimination's pins as `PinsModeled`) and the record `NestedBlockModelOf`
of the nested run's block model — everything `NestedCore.lean` needs of
the consumer's file, so that the consumer can in turn import
`NestedCore.lean` and name `nestedBlockModel`.

The containers' block models are a PREMISE (`EnvBlockModels`: every
stored inductive is a member of a block whose block model holds at the
pre-block model, with its injections the tagged towers at the
constructors' MEMBER-LOCAL positions) until `EnvModelM` records the
block model of every stored inductive (DESIGN §U.13 (f) 1); at the
pins it is read as `PinsModeled`.  The tag shape is what the pin
identification (`pinLeaf`) needs — a copy's constructors are the
container's, instantiated at the pin, at the SAME member-local
positions (DESIGN §U.15 (a)).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock AuxStored ElimState NestedPin ContainerInfo IndCaps fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The premise: the containers' block models -/

/-- **A container's block model, in the container's own terms** (task
#315 M6 s9, DESIGN §U.21 (a) — the strengthening §U.19 (e) asked for):
the block model `d` of the group `containerInfo?` reads for a stored
inductive has ONE member per `ci.members` entry, IN ORDER, named as
the entry names it, with that entry's constructor count, the group's
parameter count, and `IsBlockModel` at every member at the entry's own
constant; the members and constructors typed, the injections the
tagged towers at the member-local positions, and every member's
parameter telescope the first member's AS A FRAME (official's
cross-member check, `MutualFormersFacts.frame`).  Every clause is true
of every block model this checker builds (`mutualBlockModelOf_ofMutual`:
`memberNames`/`ctors`; `MutualFormersFacts.frame`; the native `k = 1`
instance trivially) and none follows from the abstract clauses (the
recursor's motive ORDER is not one).  The shape of the `EnvModelM`
field to come (M7), which makes it by construction. -/
structure ContainerModeled {env : Env} (m : EnvModel V env) (ci : ContainerInfo)
    (d : BlockModel V) : Prop where
  /-- one member per `all`-group entry -/
  k : d.k = ci.members.length
  /-- the group's parameter count -/
  nP : d.nP = ci.nP
  /-- the block at every member -/
  reps : IsBlockModels m d
  /-- the members, constructors and pins typed -/
  typed : ∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ ∧ PinsTyped m d ψ
  /-- the injections are the tagged towers at the member-local positions -/
  inj : ∀ (ψ : Name → Nat) (mm' j : Nat) (fs : List V),
    d.inj ψ mm' j fs = injW (d.w ψ) j (mkTower (fs ++ [pt]))
  /-- member `i` is the `i`-th entry: its name, its constructor count,
  and `IsBlockModel` at the entry's own constant -/
  member : ∀ (i : Nat) (M : ContainerMember), ci.members[i]? = some M →
    d.memberName i = M.name ∧ (d.ctorsM i).length = M.ctors.length ∧
    ∃ (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IsBlockModel m M.name ⟨M.name, M.lps, M.type⟩ cvR mI rP rules d i
  /-- every member's parameter telescope is the first member's, as a frame -/
  frame : ∀ i, i < d.k → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (d.params ψ).reverse ρ ↔ Sat V (((d.ppsM i ψ).take d.nP).map (·.2.2)).reverse ρ

/-- **Every stored container carries its block's model** at the model
`m`, in the container's own terms (`ContainerModeled` at the group
`containerInfo?` reads).  The shape of the `EnvModelM` field to come
(DESIGN §U.13 (f) 1); a premise on the branch until then. -/
@[expose] def EnvBlockModels {env : Env} (m : EnvModel V env) : Prop :=
  ∀ (J : Name) (ci : ContainerInfo), ConLeche.containerInfo? env J = some ci →
    ∃ d : BlockModel V, ContainerModeled m ci d

/-- **The pins' containers carry their blocks' models** — `EnvBlockModels`
read at the elimination's pins (`ElimState.pins`): the premise the pin
groups' assembly consumes (DESIGN §U.21). -/
@[expose] def PinsModeled {env : Env} (m : EnvModel V env) (pins : List NestedPin) : Prop :=
  ∀ q ∈ pins, ∀ ci : ContainerInfo, ConLeche.containerInfo? env q.container = some ci →
    ∃ d : BlockModel V, ContainerModeled m ci d

/-- A container the elimination read is a stored inductive. -/
theorem containerInfo?_found {env : Env} {I : Name} {ci : ContainerInfo}
    (h : ConLeche.containerInfo? env I = some ci) :
    ∃ (cv : ConstantVal) (caps : IndCaps), env.find? I = some (.indInfo cv caps) := by
  unfold ConLeche.containerInfo? at h
  by_cases hq : (I == ConLeche.quotName) = true
  · rw [if_pos hq] at h; exact nomatch h
  · rw [if_neg hq] at h
    cases hf : env.find? I with
    | none => rw [hf] at h; exact nomatch h
    | some ci' =>
      rw [hf] at h
      cases ci' with
      | indInfo cv caps => exact ⟨cv, caps, rfl⟩
      | _ => simp [bind, Option.bind] at h

/-- **The pins are modelled at an environment whose stored inductives
are** (`EnvBlockModels` read at the pins' containers). -/
theorem pinsModeled_of_env {env : Env} {m : EnvModel V env} (hm : EnvBlockModels m)
    {pins : List NestedPin} (_hok : ConLeche.nestedContainersOk env pins = true) :
    PinsModeled m pins :=
  fun q _ ci hci => hm q.container ci hci

/-! ## The block model of a nested run -/

/-- **The block model is the run's block**: its arities, names and
constructors are the recogniser's and the restore's, its pins the
elimination's (the container, its level arguments and its components
at the block's parameter openers).  The consumer (M7) reads the block
model CONCRETELY (`NestedCoreOut`, `DeclNestedCore.lean`); this record
is what the abstract clauses of the assembly consume. -/
structure NestedBlockModelOf (env : Env) (p : NestedParts) (st : ElimState)
    (ctorsR : List (List (ConstantVal × Nat × Nat))) (d : BlockModel V) : Prop where
  k : d.k = p.k
  nP : d.nP = p.nP
  env₀ : d.env₀ = env
  memberNames : d.memberNames = p.memberNames
  large : d.large = p.large
  nPins : d.nPins = st.pins.length
  /-- pin `q` is the elimination's `q`-th pin: the container, the
  level arguments and the components at the block's parameter openers -/
  pin : ∀ q pin, st.pins[q]? = some pin →
    (d.pinAt q).J = pin.container ∧
    pin.pin = Expr.mkAppN (.const pin.container (d.pinAt q).lvls) (d.pinAt q).DsE
  /-- a member's constructors are its restored ones -/
  ctors : ∀ t, t < p.k → d.ctorsM t = (ctorsR.getD t []).map fun c => (c.1, c.2.2)

end ConLeche.Model
