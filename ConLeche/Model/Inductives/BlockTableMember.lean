module

public import ConLeche.Model.Inductives.FixEntryLaw
public section

/-!
# One structure-like member's table data, flat (task #315, M4 s5)

The projection-table stage of a mutual block conses one table per
STRUCTURE-LIKE member (one constructor, no index; `mutualTables`,
`ConLeche/Kernel/Inductives/MutualInstall.lean`), in member order, each
at the environment the earlier conses have grown.  `TableMember` is
what the P step at ONE such cons reads (`stageBlockTable`,
`BlockStageTable.lean`): the member's and its constructor's lookups
and names, their readings, the fields' sorts, and — the set-level
content — the member's carrier `S` at a parameter frame with its
`FibreAt` shape at the constructor's GLOBAL block position `J`, and
the constructor's value at a fitting spine as the tagged tower
injection.  The bundle is FLAT (no block model inside), because it must
cross the OTHER members' table conses (`TableMember.cross`,
`BlockStageTables.lean`): a table's cons changes the reading of
`.proj` nodes of ITS structure, so the transport is by the
`NoProjEnv` bookkeeping of stored types, not by a block model transport.

The uniform block model (`IsBlockModel`, DESIGN §U.3) instantiates the bundle
once at the recursors' environment (`MutualTables.lean`): `S` is the
member's `lfpTuple` component at the empty index tuple, the fibre is
the block model's `fibre` clause decoded by `mkInj`, the injection the
tower `injW w J (mkTower (fs ++ [pt]))` (`ofMutual_mkInj`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal IndCaps ProjTable
  MutualBlock MutualFormerA MutualCtor projTableName)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **One structure-like member's table data**, flat, at a model of
the environment its table is consed on (see the module docstring).
`T` is the member, `cvCa` its one constructor (`nF` fields, at global
block position `J`), `resSort` the member's OWN declared sort (the
table's), `isProp` the block's `Prop` bit, `sorts` the constructor's
field sorts as the constructor stage read them, `pps`/`ds`/`Es` the
readings, `S ψ ρ'` the carrier at the parameter frame `ρ'`. -/
structure TableMember (m : EnvModel V env) (lps : List Name) (nP : Nat) (T : Name)
    (cvTa cvCa : ConstantVal) (nF J : Nat) (resSort : Level) (isProp : Bool)
    (sorts : List Level) (pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (Es : (Name → Nat) → List AnnotTerm) (S : (Name → Nat) → (Nat → V) → V) : Prop where
  /-- no stored piece mentions the member's projections -/
  nproj : ∀ j, NoProjEnv env T j
  /-- the member is stored with the block's capability record `{}` -/
  fT : env.find? T = some (.indInfo cvTa {})
  lpsT : cvTa.levelParams = lps
  /-- the constructor is stored -/
  fC : env.find? cvCa.name = some (.ctorInfo cvCa nP nF)
  lpsC : cvCa.levelParams = lps
  stripC : (cvCa.type.stripPis (nP + nF)).isSome = true
  /-- the block's `Prop` bit is the member's sort's -/
  prop : isProp = (Level.isEquiv resSort .zero == some true)
  Tshape : T.isProjFnShape = false
  Cshape : cvCa.name.isProjFnShape = false
  resT : ConLeche.reservedBasisNames.contains T = false
  resR : ConLeche.reservedBasisNames.contains (T.str "rec") = false
  resC : ConLeche.reservedBasisNames.contains cvCa.name = false
  /-- the member's type reads as its parameter telescope -/
  FD : FormerData m cvTa nP resSort pps
  /-- the constructor's type reads as the block model says -/
  CDread : ∀ ψ : Name → Nat, denoteMeta m.acval env ψ 0 cvCa.type
    = some (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  CDlen : ∀ ψ : Name → Nat, (ds ψ).length = nP + nF
  CDbelow : ∀ ψ : Name → Nat, DomsBelow 0 (ds ψ)
  /-- the constructor's binder bits follow the sort -/
  CDbits : ∀ (ψ : Name → Nat) (d : Nat × Nat × AnnotTerm), d ∈ ds ψ →
    (resSort.eval ψ = 0 ↔ d.2.1 = 0)
  /-- the fields' sorts are bounded by the member's at a non-`Prop` block -/
  leq : ∀ k, k < nF → isProp = false → Level.leq (sorts.getD k .zero) resSort = some true
  /-- the member inhabits its type's reading -/
  Tmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    interp V ρ (m.acval T ψ) ∈ˢ interp V ρ (mkPisAV (pps ψ) (.sort (resSort.eval ψ)))
  /-- the constructor inhabits its type's reading -/
  Cmem : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    interp V ρ (m.acval cvCa.name ψ)
      ∈ˢ interp V ρ (mkPisAV (ds ψ) (ctorBodyAVI m T nP nF ψ (Es ψ)))
  /-- **the carrier**: the member at a fitting parameter spine -/
  fold : ∀ (ψ : Name → Nat) (ρ : Nat → V) (ts : List V),
    SpineFit ρ ((pps ψ).map (·.2.2)) ts →
    ts.foldl SetTheory.app (interp V ρ (m.acval T ψ)) = S ψ (consList ts ρ)
  /-- **the fibre**: the carrier's members are the tag-`J` injections
  of point-terminated tuples over fitting field spines (the point at
  the squash regime) -/
  fib : ∀ (ψ : Name → Nat) (ρ' : Nat → V),
    Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ' →
    FibreAt (resSort.eval ψ) J (((ds ψ).drop nP).map (·.2.2)) ρ' (S ψ ρ')
  /-- **the constructor** at fitting parameters and fields is the
  tagged tower injection -/
  ctor : ∀ (ψ : Name → Nat) (ρ : Nat → V) (as fs : List V),
    SpineFit ρ (((ds ψ).take nP).map (·.2.2)) as →
    SpineFit (consList as ρ) (((ds ψ).drop nP).map (·.2.2)) fs →
    (as ++ fs).foldl SetTheory.app (interp V ρ (m.acval cvCa.name ψ))
      = injW (resSort.eval ψ) J (mkTower (fs ++ [pt]))
  /-- the member's and the constructor's parameter frames agree -/
  iff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V ((pps ψ).map (·.2.2)).reverse ρ ↔ Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ
  /-- the fields are graded and valid at the parameter frame -/
  fields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
    FieldsOkB (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2)) ∧
    FieldsValid ρ (((ds ψ).drop nP).map (·.2.2))
  /-- the fields are bounded at a non-`Prop` block -/
  boundP : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
    isProp = false → FieldsBound (resSort.eval ψ) ρ (((ds ψ).drop nP).map (·.2.2))
  /-- every field's reading lies in its sort's universe -/
  sortsF : ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Sat V (((ds ψ).take nP).map (·.2.2)).reverse ρ →
    ∀ j, j < nF → ∀ as : List V,
      SpineFit ρ ((((ds ψ).drop nP).map (·.2.2)).take j) as →
      interp V (consList as ρ) ((((ds ψ).drop nP).map (·.2.2)).getD j default)
        ∈ˢ (univ ((sorts.getD j .zero).eval ψ) : V)

/-- **The P step at one table**, as a proposition (`stageBlockTable`
proves it; the members' fold `stageBlockTables` takes it): at a model
carrying a member's table data, the member's table conses a model
whose carrier is the old one with the table's leaf at the table's
name. -/
@[expose] def BlockTableStep (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {env envOut : Env} (mp : EnvModelM V μ env) {lps : List Name} {nP : Nat} {T : Name}
    {cvTa cvCa : ConstantVal} {nF J : Nat} {resSort : Level} {isProp : Bool}
    {sorts : List Level} {pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    {Es : (Name → Nat) → List AnnotTerm} {S : (Name → Nat) → (Nat → V) → V},
    TableMember mp.base2 lps nP T cvTa cvCa nF J resSort isProp sorts pps ds Es S →
    ConLeche.checkStructProjTable (m := ConLeche.CheckM) T cvCa.name lps nP nF resSort
      (ConLeche.structProjGuards cvCa.type nP nF sorts) 1 cvCa env = .ok envOut →
    ∃ mp' : EnvModelM V μ envOut,
      mp'.base2.acval = acvalWith mp.base2.acval (projTableName T) (fun _ => .sort 0)

/-- **A member's table data, when the kernel conses its table**: at a
structure-like member (`ownCtors` one constructor at global position
`J`, no index) the flat bundle at that constructor; at any other
member nothing (`mutualMemberTable` conses nothing there,
`mutualMemberTable_inv`).  `S mIdx` is the member's carrier. -/
@[expose] def MemberTableOk (m : EnvModel V env) (b : MutualBlock)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level)) (isProp : Bool)
    (S : Nat → (Name → Nat) → (Nat → V) → V) (f : MutualFormerA) (mIdx : Nat) : Prop :=
  ∀ (J : Nat) (c : MutualCtor), b.ownCtors mIdx = [(J, c)] → f.nIdx = 0 →
    ∃ (pps ds : (Name → Nat) → List (Nat × Nat × AnnotTerm)) (Es : (Name → Nat) → List AnnotTerm),
      (ctorsA.getD J default).1.name = c.cv.name ∧ (ctorsA.getD J default).2 = c.nF ∧
      TableMember m b.lps b.nP f.cvTa.name f.cvTa (ctorsA.getD J default).1 c.nF J f.s isProp
        (sortss.getD J []) pps ds Es (S mIdx)

end ConLeche.Model
