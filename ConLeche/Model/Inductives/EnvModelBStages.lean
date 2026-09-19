module

public import ConLeche.Model.Inductives.ContainerCross
public import ConLeche.Model.Inductives.MutualTables
public import ConLeche.Model.Inductives.DeclNative
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Verify.Inductives.NestedTablesInv
import ConLeche.Verify.Inductives.NestedRecNames
import ConLeche.Model.Inductives.MutualCore
import ConLeche.Model.Inductives.MutualNoProj
import ConLeche.Model.Inductives.MutualRecsStore
import ConLeche.Model.Inductives.MutualRecsStage
import ConLeche.Semantics.DeclRun
import ConLeche.Model.StepAgree
import ConLeche.Model.Harvest
public section

/-!
# The fold's stages at the model WITH ITS BLOCKS (task #315, M7-3)

`EnvModelB` (`NestedPremise.lean`) is `EnvModelM` plus
`EnvBlockModels` — every stored container's block model at the
carrier.  A field is only as good as its MAINTENANCE, and this module
is the maintenance at the fold's VALUE kinds: definitions, theorems,
opaques and axioms.

Each of them is a `NonIndStep` (`ContainerCross.lean`): the stage
installs nothing at all (the tolerated axiom skip, `Quot.sound`'s
record) or conses ONE fresh constant whose head is a `defnInfo`,
`thmInfo` or `axiomInfo` — never one of the three kinds
`containerInfo?` consults, and never a projection table.  So no
container's block moves, and the only model-facing input is the
carriers' agreement at the stored names (`AcvalAgrees`), which the
stages now hand back: the cons-level step always proved it (its
`acvalWith` equation) and the stage theorems used to drop it
(`exists_agrees_of_cons`, `Model/Install.lean`).

**The INDUCTIVE kinds are not here, and cannot be yet** (DESIGN
§U.31): a route that installs a block must supply the block model of
the block it just installed, AT THE READING `containerInfo?` makes of
it back off the environment — and no route records that reading.  The
kernel request is §U.31's K.34.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal ReducibilityHint
  RecFieldKind RecRule MutualParts MutualBlock MutualFormerA MutualFormer MutualCtor MutualCtor4
  ContainerInfo IndCaps NativeParts fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {F : Nat} {env env₂ : Env}

/-! ## The value kinds are non-inductive steps -/

/-- A definition conses one fresh `defnInfo`. -/
theorem declDefnRun_nonIndStep {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hR : DeclDefnRun μ F env cv value hint env₂) : NonIndStep env env₂ := by
  obtain ⟨type', value', hcv, -, rfl, -, -⟩ := hR
  exact Or.inr ⟨.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint, rfl,
    Option.isNone_iff_eq_none.mp hcv.1,
    (fun _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ h => ConstantInfo.noConfusion h)⟩

/-- A theorem conses one fresh `thmInfo`. -/
theorem declThmRun_nonIndStep {cv : ConstantVal} {value : Expr}
    (hR : DeclThmRun μ F env cv value env₂) : NonIndStep env env₂ := by
  obtain ⟨type', -, hcv, -, -, rfl⟩ := hR
  exact Or.inr ⟨.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value, rfl,
    Option.isNone_iff_eq_none.mp hcv.1,
    (fun _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ h => ConstantInfo.noConfusion h)⟩

/-- An opaque conses one fresh `axiomInfo` (the store is by statement:
an opaque is opaque to reduction). -/
theorem declOpaqueRun_nonIndStep {cv : ConstantVal} {value : Expr}
    (hR : DeclOpaqueRun μ F env cv value env₂) : NonIndStep env env₂ := by
  obtain ⟨type', -, hcv, -, rfl, -⟩ := hR
  exact Or.inr ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, rfl,
    Option.isNone_iff_eq_none.mp hcv.1,
    (fun _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ _ _ h => ConstantInfo.noConfusion h),
    (fun _ h => ConstantInfo.noConfusion h)⟩

/-- An axiom conses one fresh `axiomInfo`, or — at `Quot.sound`'s
record and at the tolerated `sorryAx` skip — nothing. -/
theorem declAxiomRun_nonIndStep {cv : ConstantVal}
    (hR : DeclAxiomRun μ F env cv env₂) : NonIndStep env env₂ := by
  rcases hR with ⟨-, rfl⟩ | ⟨type', hcv, hbranch⟩
  · exact Or.inl rfl
  have hfresh : env.find? cv.name = none := Option.isNone_iff_eq_none.mp hcv.1
  rcases hbranch with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · exact Or.inr ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, rfl, hfresh,
      (fun _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ h => ConstantInfo.noConfusion h)⟩
  · exact Or.inr ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, rfl, hfresh,
      (fun _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ h => ConstantInfo.noConfusion h)⟩
  · exact Or.inr ⟨.axiomInfo ⟨cv.name, cv.levelParams, type'⟩, rfl, hfresh,
      (fun _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ _ _ h => ConstantInfo.noConfusion h),
      (fun _ h => ConstantInfo.noConfusion h)⟩
  · exact Or.inl rfl

/-! ## The four lifts -/

/-- **A definition keeps the model AND its blocks.** -/
theorem envModelB_defn (hμ : μ.verifiedChecks = true) (mb : EnvModelB V μ env)
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hR : DeclDefnRun μ F env cv value hint env₂) : Nonempty (EnvModelB V μ env₂) := by
  obtain ⟨mp', hag⟩ := harvestDefn hμ mb.toEnvModelM hR
  exact ⟨EnvModelB.ofNonIndStep mb mp' (declDefnRun_nonIndStep hR) hag⟩

/-- **A theorem keeps the model AND its blocks.** -/
theorem envModelB_thm (hμ : μ.verifiedChecks = true) (mb : EnvModelB V μ env)
    {cv : ConstantVal} {value : Expr}
    (hR : DeclThmRun μ F env cv value env₂) : Nonempty (EnvModelB V μ env₂) := by
  obtain ⟨mp', hag⟩ := harvestThm hμ mb.toEnvModelM hR
  exact ⟨EnvModelB.ofNonIndStep mb mp' (declThmRun_nonIndStep hR) hag⟩

/-- **An opaque keeps the model AND its blocks.** -/
theorem envModelB_opaque (hμ : μ.verifiedChecks = true) (mb : EnvModelB V μ env)
    {cv : ConstantVal} {value : Expr}
    (hR : DeclOpaqueRun μ F env cv value env₂) : Nonempty (EnvModelB V μ env₂) := by
  obtain ⟨mp', hag⟩ := harvestOpaque hμ mb.toEnvModelM hR
  exact ⟨EnvModelB.ofNonIndStep mb mp' (declOpaqueRun_nonIndStep hR) hag⟩

/-- **An axiom keeps the model AND its blocks.** -/
theorem envModelB_axiom (hμ : μ.verifiedChecks = true) (mb : EnvModelB V μ env)
    {cv : ConstantVal}
    (hR : DeclAxiomRun μ F env cv env₂) : Nonempty (EnvModelB V μ env₂) := by
  obtain ⟨mp', hag⟩ := axiomStepAgree_of hμ mb.toEnvModelM hR
  exact ⟨EnvModelB.ofNonIndStep mb mp' (declAxiomRun_nonIndStep hR) hag⟩

/-- **The empty environment carries the blocks vacuously** (the fold's
base case): nothing is stored, so `containerInfo?` reads nothing. -/
noncomputable def EnvModelB.empty (V : Type w) [SetTheory V] (μ : CheckMode) :
    EnvModelB V μ Env.empty where
  toEnvModelM := EnvModelM.empty V μ
  blocks := ⟨fun _ => Classical.choice inferInstance, fun J ci hci => by
    obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci
    exact nomatch hf⟩


/-! ## The mutual route's block, at the reading its run certifies

(task #315 M7-3 session 6, DESIGN §U.46 (c)). -/

/-- **An ORDINARY field of a mutual constructor mentions no member, at
the OPENED domain, off the run** (task #315 M7-3 session 9, DESIGN
§U.66 (a)).  The Prop is `ConLeche.MutualOrdFree`
(`Verify/Inductives/MutualInv.lean`) at this block's member names and
parameter count.

`ContainerModeled.ordFree` is stated at the block model's opened field
data, while `mutualCtorKinds` decides ordinariness on the RAW
`stripPis` domain with its loose bvars, and the two are NOT the same
statement: `openPisAtFvars` annotates each binder's fvar with its own
domain and `mentionsConst` descends into an fvar's type annotation, so
an opened ordinary domain referring to an earlier field carries that
field's type (DESIGN §U.43 (d)).  This is the OPENED form, the one the
lift consumes, and it is DERIVED: `mutualFieldsOk`'s `.ordinary` cell is
`x.fvarTypeD.constsResolve env` at the PRE-BLOCK environment, where
every member is fresh (`mutualFormers_membersFresh`, read off the
formers' stage).  This is what makes `declMutualB` hypothesis-free —
K.36 was retired as a CHECK because the fact is a consequence of one the
route already runs. -/
theorem mutualOrdFree_of_run {env env₁ : Env} {F : Nat} {b : MutualBlock}
    {fms : List MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
    {kinds : List (List (RecFieldKind × Nat))}
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env
      = .ok (env₁, fms))
    (hfo : ConLeche.mutualFieldsOk env b.members3 b.lps b.nP ctorsA kinds = true) :
    ConLeche.MutualOrdFree (fms.map (·.cvTa.name)) b.nP ctorsA kinds :=
  ConLeche.mutualOrdFree_of (ConLeche.Semantics.mutualFormers_membersFresh hformers) hfo

/-- The kinds without their targets, read at any position. -/
theorem map_fst_getD_ordinary (ks : List (RecFieldKind × Nat)) (l : Nat) :
    (ks.map (·.1)).getD l .ordinary = (ks.getD l (.ordinary, 0)).1 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ks[l]? <;> rfl

/-- **The read-back's constructor list is the block model's**: at a
list of positions that are all in range, `filterMap`-ing the lookup and
`map`-ing the defaulting read agree — the plumbing between the run's
K.34 argument (`(b.ownCtors t).filterMap fun (J, _) => ctorsA[J]?`) and
`MutualBlockModelOf.ctors` (`(b.ownCtors t).map fun q =>
ctorsA.getD q.1 default`), DESIGN §U.46 (c) 2. -/
theorem filterMap_getElem?_eq_map_getD {α β : Type _} [Inhabited β] {A : List β} :
    ∀ l : List (Nat × α), (∀ p ∈ l, p.1 < A.length) →
      (l.filterMap fun q => A[q.1]?) = l.map fun q => A.getD q.1 default
  | [], _ => rfl
  | p :: rest, h => by
    have hp : A[p.1]? = some (A.getD p.1 default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h p List.mem_cons_self)]; rfl
    rw [List.filterMap_cons, hp, List.map_cons,
      filterMap_getElem?_eq_map_getD rest (fun q hq => h q (List.mem_cons_of_mem _ hq))]

/-- The read-back's member list, read at a member. -/
theorem mutualReadBack_getD {b : MutualBlock} {fms : List MutualFormerA}
    {ctorsA : List (ConstantVal × Nat)} {i : Nat} (hi : i < fms.length) :
    (fms.zipIdx.map fun (f, mIdx) =>
        (f.cvTa, (b.ownCtors mIdx).filterMap fun (J, _) => ctorsA[J]?)).getD i default
      = ((fms.getD i default).cvTa,
        (b.ownCtors i).filterMap fun (J, _) => ctorsA[J]?) := by
  have hz : fms.zipIdx[i]? = some (fms[i], i) := by
    rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hi, Nat.zero_add]; rfl
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, hz,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- The read-back's member list, read at a member (the `getElem?` form
`containerInfo?_of_readBack` takes). -/
theorem mutualReadBack_getElem? {b : MutualBlock} {fms : List MutualFormerA}
    {ctorsA : List (ConstantVal × Nat)} {i : Nat} (hi : i < fms.length) :
    (fms.zipIdx.map fun (f, mIdx) =>
        (f.cvTa, (b.ownCtors mIdx).filterMap fun (J, _) => ctorsA[J]?))[i]?
      = some ((fms.getD i default).cvTa,
        (b.ownCtors i).filterMap fun (J, _) => ctorsA[J]?) := by
  rw [List.getElem?_map, List.getElem?_zipIdx, List.getElem?_eq_getElem hi, Nat.zero_add,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- **The block the mutual route installs IS its own container group**
(task #315 M7-3 session 6): `ContainerModeled.of_readBack` at the run's
K.34 conjunct, with every remaining clause the route's own —
`hk`/`hnP`/`hnames`/`hctorNames`/`namesLen` from `MutualBlockModelOf`
and the list plumbing, `reps`/`member` from the AT-form the core hands
back (DESIGN §U.46 (a)), `inj` and `frame` from `MutualTableFacts`, the
PIN clauses VACUOUS (a mutual block has no pins), and `ordFree`
from `MutualOrdFree` by a rewrite through `BlockCtorData.opens` and the
block model's field kinds. -/
theorem mutualContainerModeled {env envR : Env} {m : EnvModel V envR}
    {b : MutualBlock} {fms : List MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))} {d : BlockModel V}
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hlenA : ctorsA.length = b.ctors.length) (hlenF : fms.length = b.k)
    (hd : MutualBlockModelOf env b fms ctorsA d)
    (hks : ∀ mm j, d.ksF mm j = (kinds.getD (b.ownOffset mm + j) []).map (·.1))
    (hOrd : ConLeche.MutualOrdFree (fms.map (·.cvTa.name)) b.nP ctorsA kinds)
    (hrepsAt : IsBlockModelsAt m d (fun mm => (fms.getD mm default).cvTa))
    (htyped : ∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ)
    (htf : MutualTableFacts b fms sortss d)
    (hownPins : ContainerOwnPinsSyn (V := V) envR d)
    (hnpC : ∀ (i j : Nat) (cA : ConstantVal × Nat), i < d.k → (d.ctorsM i)[j]? = some cA →
      ProjFree (fms.map (·.cvTa.name)) cA.1.type) :
    ContainerModeled m
      (ConLeche.blockContainerInfo b.nP (fms.zipIdx.map fun (f, mIdx) =>
        (f.cvTa, (b.ownCtors mIdx).filterMap fun (J, _) => ctorsA[J]?))) d := by
  have hkF : d.k = fms.length := by rw [hd.k, hlenF]
  have hnames : ∀ i, i < d.k →
      d.memberName i = (fms.getD i default).cvTa.name := by
    intro i _
    show d.memberNames.getD i .anonymous = _
    rw [hd.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getD_eq_getElem?_getD]
    cases fms[i]? <;> rfl
  -- the block's own positions are in range
  have hown : ∀ (i : Nat), ∀ p ∈ b.ownCtors i, p.1 < ctorsA.length := by
    intro i p hp
    obtain ⟨J, c⟩ := p
    obtain ⟨hc, -⟩ := ownCtors_mem_iff.mp hp
    rw [hlenA]
    exact (List.getElem?_eq_some_iff.mp hc).1
  have hnoPins : d.nPins = 0 := by show d.pins.length = 0; rw [hd.pins]; rfl
  refine ContainerModeled.of_readBack ?_ hd.nP
    (by rw [hd.memberNames, List.length_map, hkF]) (fun i hi => ?_) (fun i hi => ?_)
    hrepsAt.toIsBlockModels
    (fun ψ => ⟨(htyped ψ).1, (htyped ψ).2, PinsTyped.of_noPins hd.pins ψ⟩)
    htf.inj (fun i hi ψ ρ => (htf.frame i hi ψ ρ).symm) (fun i j l x hi hj hx hk => ?_)
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    (fun _ _ _ _ _ _ _ _ _ hq _ => absurd hq (by rw [hnoPins]; omega))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hq _ => absurd hq (by rw [hnoPins]; omega))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hq _ => absurd hq (by rw [hnoPins]; omega))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq _ => absurd hq (by rw [hnoPins]; omega))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq _ => absurd hq (by rw [hnoPins]; omega))
    (fun i j cA hi hj T hT n => hnpC i j cA hi hj T (hd.memberNames ▸ hT) n)
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    hownPins
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    (fun _ _ => ContainerPinParams.of_noPins hd.pins) (fun i hi => ?_)
    (fun _ _ hq _ _ => absurd hq (by rw [hnoPins]; omega))
    (fun _ _ _ hq _ _ => absurd hq (by rw [hnoPins]; omega))
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
  · rw [List.length_map, List.length_zipIdx, hkF]
  · rw [mutualReadBack_getD (by rw [← hkF]; exact hi), hnames i hi]
  · rw [mutualReadBack_getD (by rw [← hkF]; exact hi)]
    show _ = ((b.ownCtors i).filterMap fun (J, _) => ctorsA[J]?).map (·.1.name)
    rw [filterMap_getElem?_eq_map_getD _ (hown i), hd.ctors i (hd.k ▸ hi)]
  · -- the ordinary field's opened domain mentions no member
    have hik : i < b.k := hd.k ▸ hi
    have hcM := hd.ctors i hik
    rw [hcM, List.length_map] at hj
    obtain ⟨Jc, hJc⟩ : ∃ p, (b.ownCtors i)[j]? = some p := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨J, c⟩ := Jc
    have hJ : J = b.ownOffset i + j := ownCtors_getElem?_idx h3 hJc
    have hJlt : J < ctorsA.length := hown i (J, c) (List.mem_of_getElem? hJc)
    have hcA : ctorsA[J]? = some (ctorsA.getD J default) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hJlt]; rfl
    have hcj : (d.ctorsM i)[j]? = some (ctorsA.getD J default) := by
      rw [hcM, List.getElem?_map, hJc]; rfl
    obtain ⟨cvR, mI, rP, rules, hI⟩ := hrepsAt i hi
    obtain ⟨crest, hop1, hop2⟩ := (hI.ctors i j _ hi hcj).2.2.opens
    rw [hd.nP] at hop1 hop2
    have hkind : ((kinds.getD J []).getD l (.ordinary, 0)).1 = .ordinary := by
      rw [← map_fst_getD_ordinary, hJ, ← hks i j]; exact hk
    rw [hd.memberNames]
    exact hOrd J _ hcA _ _ _ _ hop1 hop2 l x hx hkind
  · obtain ⟨cvR, mI, rP, rules, hI⟩ := hrepsAt i hi
    refine ⟨cvR, mI, rP, rules, ?_⟩
    rw [mutualReadBack_getD (by rw [← hkF]; exact hi)]
    rw [← hnames i hi]
    exact hI

omit [SetTheory V] in
/-- **THE MUTUAL ROUTE'S OWN-PIN TABLE IS EMPTY** (task #315 K.43,
DESIGN §U.74 (c)): the clause `ContainerOwnPinsSyn` at the block this
route installed, from the route's own two Bools and nothing else.

K.43's Bool says the mutual route left no mimic recursor under its
FIRST member (`f₀`, the head of `fms`), and K.34's read-back says every
member of the block reads back the SAME group — whose `members.head?`
is that first member's record.  So `containerOwnPinsAt` stops at its
first step at every member and every instantiation
(`containerOwnPinsAt_nil`), and the table is empty; the block model's
recorded pins are never needed (a mutual block has none).

This is the clause `ContainerModeled.ownPins` at this route's site. -/
theorem mutualOwnPins_of {envB envOut : Env} {b : MutualBlock} {fms : List MutualFormerA}
    {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)} {d : BlockModel V}
    (hlenF : fms.length = b.k) (hd : MutualBlockModelOf (V := V) envB b fms ctorsA d)
    (hf₀ : fms[0]? = some f₀)
    (hrb : ConLeche.blockReadBackOk envOut b.nP (fms.zipIdx.map fun (f, mIdx) =>
      (f.cvTa, (b.ownCtors mIdx).filterMap fun (J, _) => ctorsA[J]?)) = true)
    (hmim : ConLeche.blockOwnMimicsOk envOut f₀.cvTa.name 0 = true) :
    ContainerOwnPinsSyn (V := V) envOut d := by
  refine ContainerOwnPinsSyn.of_noMimics (by
      show d.pins.length = 0
      rw [hd.pins]; rfl) hmim fun i hi => ?_
  have hclt : i < fms.length := by rw [hlenF, ← hd.k]; exact hi
  have hname : d.memberName i = (fms.getD i default).cvTa.name := by
    show d.memberNames.getD i .anonymous = _
    rw [hd.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getD_eq_getElem?_getD]
    cases fms[i]? <;> rfl
  -- the group's first member is the name K.43's Bool was certified at
  obtain ⟨rest, rfl⟩ : ∃ rest, fms = f₀ :: rest := by
    cases fms with
    | nil => exact nomatch hf₀
    | cons a as => exact ⟨as, by rw [Option.some.inj hf₀]⟩
  refine ⟨ConLeche.blockContainerInfo b.nP ((f₀ :: rest).zipIdx.map fun (f, mIdx) =>
      (f.cvTa, (b.ownCtors mIdx).filterMap fun (J, _) => ctorsA[J]?)),
    ⟨f₀.cvTa.name, f₀.cvTa.levelParams, f₀.cvTa.type,
      ((b.ownCtors 0).filterMap fun (J, _) => ctorsA[J]?).map
        fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩, ?_, rfl, rfl⟩
  rw [hname]
  exact containerInfo?_of_readBack (nP := b.nP) hrb (mutualReadBack_getElem? hclt)

/-! ### The install's conses, as the crossing and the field see them

(task #315 M7-3 session 6, DESIGN §U.46 (c) 4.) -/

/-- **What one stage of an install route's conses gives the crossing**:
the new constants sit in front of the old environment, their names are
fresh there, and their KINDS are the route's own — an `indInfo` is a
MEMBER of the block (`Ms`), a `recInfo` is a member's recursor, and a
`projInfo` tables a member.  These are what `EnvBlocksOf.crossIndP`
reads off an extension: `hext`/`hnewN`/`hfreshN` (the first two
clauses), `hrecN` (the recursor clause, with `Name.str` injective), the
new containers' identification (the `indInfo` clause) and the guard
`TableCross` (the table clause). -/
@[expose] def BlockInstallExt (Ms : List Name) (env envOut : Env) (new : List ConstantInfo) :
    Prop :=
  envOut.consts = new ++ env.consts ∧
  (∀ c ∈ new, env.find? c.name = none) ∧
  (∀ c ∈ new, ∀ (cv : ConstantVal) (caps : IndCaps), c = .indInfo cv caps → c.name ∈ Ms) ∧
  (∀ c ∈ new, ∀ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    c = .recInfo cv mI rP rules → ∃ n' ∈ Ms, c.name = n'.str "rec") ∧
  (∀ c ∈ new, ∀ tbl : ConLeche.ProjTable, c = .projInfo tbl → tbl.structName ∈ Ms)

omit [SetTheory V] in
/-- A constant the name lookup finds in a list is in it, under that name. -/
theorem find?_name_mem {new : List ConstantInfo} {n : Name} {c : ConstantInfo}
    (h : List.find? (fun c => c.name == n) new = some c) : c ∈ new ∧ c.name = n := by
  refine ⟨List.mem_of_find?_eq_some h, ?_⟩
  have hh := List.find?_eq_some_iff_getElem.mp h
  simpa using hh.1

omit [SetTheory V] in
/-- A stage that conses nothing. -/
theorem BlockInstallExt.rfl' (Ms : List Name) (env : Env) : BlockInstallExt Ms env env [] :=
  ⟨rfl, by simp, by simp, by simp, by simp⟩

omit [SetTheory V] in
/-- Two such stages compose: the later stage's names are fresh at the
earlier environment, so they are fresh at the base too. -/
theorem BlockInstallExt.trans {Ms : List Name} {env env₁ env₂ : Env}
    {new₁ new₂ : List ConstantInfo}
    (h₁ : BlockInstallExt Ms env env₁ new₁) (h₂ : BlockInstallExt Ms env₁ env₂ new₂) :
    BlockInstallExt Ms env env₂ (new₂ ++ new₁) := by
  obtain ⟨hc₁, hf₁, hi₁, hr₁, hp₁⟩ := h₁
  obtain ⟨hc₂, hf₂, hi₂, hr₂, hp₂⟩ := h₂
  refine ⟨by rw [hc₂, hc₁, List.append_assoc], fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩
  · rcases List.mem_append.mp hc with hc' | hc'
    · exact ConLeche.Semantics.find?_none_of_append hc₁ (hf₂ c hc')
    · exact hf₁ c hc'
  · rcases List.mem_append.mp hc with hc' | hc'
    · exact hi₂ c hc'
    · exact hi₁ c hc'
  · rcases List.mem_append.mp hc with hc' | hc'
    · exact hr₂ c hc'
    · exact hr₁ c hc'
  · rcases List.mem_append.mp hc with hc' | hc'
    · exact hp₂ c hc'
    · exact hp₁ c hc'

/-- **THE LOOKUP HALF of an install's conses**: the new constants in
front of the old environment, their names fresh there.
`BlockInstallExt`'s first two clauses, named on their own because the
crossing's lookup lemmas read ONLY these — and because a block can meet
them without meeting the KIND clauses: the `Quot` install
(`BasisBlocksFold.lean`) conses two recursors whose names are not
`I.rec`, so no `Ms` makes `BlockInstallExt` true of it. -/
@[expose] def ConsExt (env envOut : Env) (new : List ConstantInfo) : Prop :=
  envOut.consts = new ++ env.consts ∧ (∀ c ∈ new, env.find? c.name = none)

namespace ConsExt

variable {env envOut : Env} {new : List ConstantInfo}

omit [SetTheory V] in
/-- A stored lookup survives: a new constant of that name would have to
be fresh at the environment that answers it. -/
theorem ext (h : ConsExt env envOut new) :
    ∀ (n : Name) (c : ConstantInfo), env.find? n = some c → envOut.find? n = some c := by
  intro n c hf
  cases hn : List.find? (fun c => c.name == n) new with
  | none => rw [ConLeche.Semantics.find?_append_of_new_none h.1 hn]; exact hf
  | some c' =>
    obtain ⟨hmem, rfl⟩ := find?_name_mem hn
    rw [h.2 c' hmem] at hf
    exact nomatch hf

omit [SetTheory V] in
/-- A lookup the extension answers is the base's or one of the new
constants'. -/
theorem newOf (h : ConsExt env envOut new) {n : Name} {c : ConstantInfo}
    (hf : envOut.find? n = some c) (hn : env.find? n = none) : c ∈ new ∧ c.name = n := by
  cases hfn : List.find? (fun c => c.name == n) new with
  | none =>
    rw [ConLeche.Semantics.find?_append_of_new_none h.1 hfn, hn] at hf
    exact nomatch hf
  | some c' =>
    have h₂ : envOut.find? n = some c' := by
      rw [ConLeche.Env.find?, h.1, List.find?_append, hfn]; rfl
    rw [hf] at h₂
    obtain rfl : c = c' := Option.some.inj h₂
    exact find?_name_mem hfn

omit [SetTheory V] in
/-- The new names are fresh at the base. -/
theorem freshN (h : ConsExt env envOut new) :
    ∀ n ∈ new.map (·.name), env.find? n = none := by
  intro n hn
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
  exact h.2 c hc

omit [SetTheory V] in
/-- A lookup the extension answers is the base's or at a new name. -/
theorem newN (h : ConsExt env envOut new) :
    ∀ (n : Name) (c : ConstantInfo), envOut.find? n = some c →
      env.find? n = some c ∨ n ∈ new.map (·.name) := by
  intro n c hf
  cases hn : env.find? n with
  | some c' =>
    left
    rw [← hf, ext h n c' hn]
  | none =>
    right
    obtain ⟨hmem, rfl⟩ := newOf h hf hn
    exact List.mem_map_of_mem hmem

omit [SetTheory V] in
/-- **A cons chain that adds no projection table creates no projection
slot**: a slot the extension answers is either the base's own (the same
stored constant, by `ext`) or one of the new constants', and a new
constant is not a `projInfo`. -/
theorem noNewTables (h : ConsExt env envOut new)
    (hnoTbl : ∀ c ∈ new, ∀ tbl : ConLeche.ProjTable, c ≠ .projInfo tbl) :
    ∀ (sn : Name) (i : Nat), env.findProj? sn i = none → envOut.findProj? sn i = none := by
  intro sn i h0
  -- through `findProj?`'s OWN lemmas, never its unfolding: forcing the
  -- equation lemma here would declare it in this module and hand every
  -- capstone that reads a projection table a dependency on it
  cases h₂ : envOut.findProj? sn i with
  | none => rfl
  | some entry =>
    obtain ⟨tbl, hf₂, hi, -⟩ := ConLeche.Env.findProj?_some h₂
    cases hf₁ : env.find? (ConLeche.projTableName sn) with
    | some c =>
      rw [h.ext _ _ hf₁] at hf₂
      obtain rfl : c = .projInfo tbl := Option.some.inj hf₂
      rw [ConLeche.Env.findProj?_of_table hf₁ hi] at h0
      exact nomatch h0
    | none =>
      obtain ⟨hc, -⟩ := h.newOf hf₂ hf₁
      exact absurd rfl (hnoTbl _ hc tbl)

end ConsExt

/-! ## A mimic recursor's name is neither a member's nor an old one's

(task #315 M7-3 session 21: what `ContainerOwnPinsSyn.crossIndOf`'s
`hmimN` needs of each install route.) -/

omit [SetTheory V] in
/-- **A MIMIC RECURSOR'S NAME IS NO MEMBER'S RECURSOR NAME**: the
mimics are `Name.appendIndexAfter (T.str "rec") j`, whose last string
component is `"rec" ++ "_" ++ toString j`, and a member's recursor's is
`"rec"` — the two differ in LENGTH, `toString j` being non-empty.

The whole content of `hmimN` at the routes whose `new` list conses only
members' own recursors (`BlockInstallExt.mimN`, and so the NATIVE and
MUTUAL routes): the premise is then unsatisfiable. -/
theorem appendIndexAfter_rec_ne_rec (n n' : Name) (j : Nat) :
    Name.appendIndexAfter (n.str "rec") j ≠ n'.str "rec" := by
  intro h
  have h' : Name.str n ("rec" ++ "_" ++ toString j) = Name.str n' "rec" := h
  obtain ⟨-, hs⟩ := ConLeche.Name.str.inj h'
  have hlen := congrArg String.length hs
  rw [String.length_append, String.length_append] at hlen
  simp only [show "rec".length = 3 from rfl, show "_".length = 1 from rfl] at hlen
  omega

omit [SetTheory V] in
/-- **A MIMIC RECURSOR'S LAST COMPONENT IS AT LEAST FIVE CHARACTERS
LONG, AND ITS PREFIX IS THE BASE'S**: `Name.appendIndexAfter` writes
`"rec" ++ "_" ++ toString j`, and a natural number's decimal digits are
never empty (`Nat.length_repr_pos`).

The general form of `appendIndexAfter_rec_ne_rec` above, for the one
install whose new names are not all members' own recursors — `Quot`'s,
whose `hmimN` is then decided component by component (`Quot.sound` is
the one name long enough, and its prefix IS a new name). -/
theorem appendIndexAfter_rec_str {n n' : Name} {j : Nat} {s : String}
    (h : Name.appendIndexAfter (n.str "rec") j = n'.str s) : n = n' ∧ 5 ≤ s.length := by
  have h' : Name.str n ("rec" ++ "_" ++ toString j) = Name.str n' s := h
  obtain ⟨hn, hs⟩ := ConLeche.Name.str.inj h'
  refine ⟨hn, ?_⟩
  have hpos : 0 < (toString j).length := Nat.length_repr_pos
  have hlen := congrArg String.length hs
  rw [String.length_append, String.length_append] at hlen
  simp only [show "rec".length = 3 from rfl, show "_".length = 1 from rfl] at hlen
  omega

omit [SetTheory V] in
/-- **TWO MIMIC NAMES UNDER DIFFERENT BASES ARE DIFFERENT NAMES**: the
base is the name's own prefix, which `Name.appendIndexAfter` leaves
alone.  What the NESTED route's `hmimN` needs: its mimics are all named
under the block's FIRST member, so a mimic-shaped name it conses has
that member as its base. -/
theorem appendIndexAfter_rec_base {n n' : Name} {i j : Nat}
    (h : Name.appendIndexAfter (n.str "rec") i = Name.appendIndexAfter (n'.str "rec") j) :
    n = n' := by
  have h' : Name.str n ("rec" ++ "_" ++ toString i)
      = Name.str n' ("rec" ++ "_" ++ toString j) := h
  exact (ConLeche.Name.str.inj h').1

namespace BlockInstallExt

variable {Ms : List Name} {env envOut : Env} {new : List ConstantInfo}

omit [SetTheory V] in
/-- An install's conses are a cons chain: `BlockInstallExt`'s first two
clauses, which is everything the crossing's LOOKUP half reads. -/
theorem toConsExt (h : BlockInstallExt Ms env envOut new) : ConsExt env envOut new :=
  ⟨h.1, h.2.1⟩

omit [SetTheory V] in
/-- A stored lookup survives (`ConsExt.ext`). -/
theorem ext (h : BlockInstallExt Ms env envOut new) :
    ∀ (n : Name) (c : ConstantInfo), env.find? n = some c → envOut.find? n = some c :=
  h.toConsExt.ext

omit [SetTheory V] in
/-- A lookup the extension answers is the base's or one of the new
constants' (`ConsExt.newOf`). -/
theorem newOf (h : BlockInstallExt Ms env envOut new) {n : Name} {c : ConstantInfo}
    (hf : envOut.find? n = some c) (hn : env.find? n = none) : c ∈ new ∧ c.name = n :=
  h.toConsExt.newOf hf hn

omit [SetTheory V] in
/-- The new names are fresh at the base (`ConsExt.freshN`). -/
theorem freshN (h : BlockInstallExt Ms env envOut new) :
    ∀ n ∈ new.map (·.name), env.find? n = none :=
  h.toConsExt.freshN

omit [SetTheory V] in
/-- A lookup the extension answers is the base's or at a new name
(`ConsExt.newN`). -/
theorem newN (h : BlockInstallExt Ms env envOut new) :
    ∀ (n : Name) (c : ConstantInfo), envOut.find? n = some c →
      env.find? n = some c ∨ n ∈ new.map (·.name) :=
  h.toConsExt.newN

omit [SetTheory V] in
/-- **A new recursor's MEMBER is new too** — the clause
`containerInfo?_ext_ind` needs of an inductive extension: a `recInfo`
the extension conses is a member's recursor (`Name.str` injective), and
the members are among the extension's own constants. -/
theorem recN (h : BlockInstallExt Ms env envOut new)
    (hMs : ∀ n ∈ Ms, n ∈ new.map (·.name)) :
    ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      envOut.find? (n.str "rec") = some (.recInfo cv mI rP rules) →
      n.str "rec" ∈ new.map (·.name) → n ∈ new.map (·.name) := by
  intro n cv mI rP rules hf hmem
  obtain ⟨hc, hname⟩ := newOf h hf (freshN h _ hmem)
  obtain ⟨n', hn', heq⟩ := h.2.2.2.1 _ hc cv mI rP rules rfl
  rw [hname] at heq
  obtain rfl : n = n' := (ConLeche.Name.str.inj heq).1
  exact hMs _ hn'

omit [SetTheory V] in
/-- **A new container is a member**: the only `indInfo` the extension
conses are the block's own members. -/
theorem indMs (h : BlockInstallExt Ms env envOut new) {J : Name} {cv : ConstantVal}
    {caps : IndCaps} (hf : envOut.find? J = some (.indInfo cv caps))
    (hJ : J ∈ new.map (·.name)) : J ∈ Ms := by
  obtain ⟨hc, hname⟩ := newOf h hf (freshN h _ hJ)
  rw [← hname]
  exact h.2.2.1 _ hc cv caps rfl

omit [SetTheory V] in
/-- **NO MIMIC RECURSOR IS NEW** — the clause
`ContainerOwnPinsSyn.crossIndOf` needs of an install whose recursors
are all the block's members' own, which is the NATIVE route's
(`nativeInstallExt`) and the MUTUAL route's (`mutualInstallExt`): the
record's recursor clause says a `.recInfo` the install conses is named
`T.rec` at a member `T`, and no `T.rec` is
`Name.appendIndexAfter (n.str "rec") j`
(`appendIndexAfter_rec_ne_rec`).  So the premise is unsatisfiable and
the crossing's walk cannot grow at ANY container, old or new — the
strongest form of `hmimN`, and the reason these two routes need no
mimic bookkeeping of their own. -/
theorem mimN (h : BlockInstallExt Ms env envOut new) :
    ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      envOut.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ new.map (·.name) → n ∈ new.map (·.name) := by
  intro n j cv mI rP rules hf hmem
  obtain ⟨hc, hname⟩ := newOf h hf (freshN h _ hmem)
  obtain ⟨n', -, heq⟩ := h.2.2.2.1 _ hc cv mI rP rules rfl
  rw [hname] at heq
  exact absurd heq (appendIndexAfter_rec_ne_rec n n' j)

end BlockInstallExt

omit [SetTheory V] in
/-- **The literal guards are monotone under any lookup-preserving
extension**: each guard is a predicate on ONE lookup that is `false` at
`none`, so a guard that holds reads a STORED constant and the extension
answers it alike. -/
theorem litGuardsMono_of_findPreserved {env env' : Env} (hF : FindPreserved env env') :
    LitGuardsMono env env' := by
  have hp : ∀ (n : Name) (f : Option ConstantInfo → Bool), f none = false →
      f (env.find? n) = true → f (env'.find? n) = true := by
    intro n f hn hg
    cases hf : env.find? n with
    | none => rw [hf, hn] at hg; exact nomatch hg
    | some c => rw [hF hf]; rw [hf] at hg; exact hg
  have hnat : ConLeche.natLitSupported env = true → ConLeche.natLitSupported env' = true := by
    intro hg
    simp only [ConLeche.natLitSupported, Bool.and_eq_true] at hg ⊢
    exact ⟨⟨hp _ _ rfl hg.1.1, hp _ _ rfl hg.1.2⟩, hp _ _ rfl hg.2⟩
  refine ⟨hnat, fun hg => ?_⟩
  simp only [ConLeche.strLitSupported, Bool.and_eq_true] at hg ⊢
  exact ⟨⟨⟨⟨⟨⟨⟨hnat hg.1.1.1.1.1.1.1, hp _ _ rfl hg.1.1.1.1.1.1.2⟩, hp _ _ rfl hg.1.1.1.1.1.2⟩,
    hp _ _ rfl hg.1.1.1.1.2⟩, hp _ _ rfl hg.1.1.1.2⟩, hp _ _ rfl hg.1.1.2⟩,
    hp _ _ rfl hg.1.2⟩, hp _ _ rfl hg.2⟩

omit [SetTheory V] in
/-- **An install's conses, as the guarded crossing sees them**: the
lookups are preserved, the literal guards monotone, and the only
projection slots created are at the block's own members (the table
clause, with `projTableName` injective). -/
theorem BlockInstallExt.tableCross {Ms : List Name} {env envOut : Env}
    {new : List ConstantInfo} (h : BlockInstallExt Ms env envOut new) :
    TableCross Ms env envOut where
  find := fun hf => h.ext _ _ hf
  lit := litGuardsMono_of_findPreserved (fun hf => h.ext _ _ hf)
  proj := fun sn i entry h0 h1 => by
    obtain ⟨tbl, hf0, hi, -⟩ := ConLeche.Env.findProj?_some h1
    cases hf : env.find? (ConLeche.projTableName sn) with
    | some c =>
      have hpres := h.ext _ _ hf
      rw [hf0] at hpres
      obtain rfl : c = .projInfo tbl := Option.some.inj hpres.symm
      rw [ConLeche.Env.findProj?_of_table hf hi] at h0
      exact nomatch h0
    | none =>
      obtain ⟨hc, hname⟩ := h.newOf hf0 hf
      have hstruct : ConLeche.projTableName tbl.structName = ConLeche.projTableName sn := hname
      obtain rfl : tbl.structName = sn := by
        unfold ConLeche.projTableName at hstruct
        exact (ConLeche.Name.str.inj (ConLeche.Name.num.inj hstruct).1).1
      exact h.2.2.2.2 _ hc tbl rfl

/-! ### The NESTED install's conses — the recursor clause, relaxed

(task #315 M7-3 session 10, DESIGN §U.67 (a).) -/

/-- **The nested install's conses, as the crossing reads them**:
`BlockInstallExt` with its RECURSOR clause weakened to a CONDITIONAL
one.  The nested route conses `k + n` recursors — the members' own
`I.rec` and the MIMIC recursors `T₁.rec_1`, `T₁.rec_2`, … (official's
`mk_aux_rec_name_map`, `ConLeche.NestedParts.mimicRecName`) — and a
mimic's name is no member's `I.rec`, so `BlockInstallExt` is unprovable
for this route at every `Ms`: the `Quot` finding of DESIGN §U.66 (b)
again, at an install that DOES install projection tables.  What the
crossing reads of the recursors is only `hrecN`, and that needs the
conditional form — a new recursor whose name IS `n.str "rec"` has
`n ∈ Ms`, vacuous at a mimic (`"rec_1" ≠ "rec"`). -/
@[expose] def NestedInstallExt (Ms : List Name) (env envOut : Env) (new : List ConstantInfo) :
    Prop :=
  ConsExt env envOut new ∧
  (∀ c ∈ new, ∀ (cv : ConstantVal) (caps : IndCaps), c = .indInfo cv caps → c.name ∈ Ms) ∧
  (∀ c ∈ new, ∀ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
    c = .recInfo cv mI rP rules → ∀ n : Name, c.name = n.str "rec" → n ∈ Ms) ∧
  (∀ c ∈ new, ∀ tbl : ConLeche.ProjTable, c = .projInfo tbl → tbl.structName ∈ Ms)

namespace NestedInstallExt

variable {Ms : List Name} {env envOut : Env} {new : List ConstantInfo}

omit [SetTheory V] in
/-- The lookup half (`ConsExt`). -/
theorem toConsExt (h : NestedInstallExt Ms env envOut new) : ConsExt env envOut new := h.1

omit [SetTheory V] in
/-- An install whose recursors are all members' own is one of these. -/
theorem of_blockInstallExt (h : BlockInstallExt Ms env envOut new) :
    NestedInstallExt Ms env envOut new := by
  refine ⟨h.toConsExt, h.2.2.1, fun c hc cv mI rP rules hr n hn => ?_, h.2.2.2.2⟩
  obtain ⟨n', hn', heq⟩ := h.2.2.2.1 c hc cv mI rP rules hr
  rw [hn] at heq
  obtain rfl : n = n' := (ConLeche.Name.str.inj heq).1
  exact hn'

omit [SetTheory V] in
/-- **A new recursor's MEMBER is new too** (`BlockInstallExt.recN` at
the conditional clause). -/
theorem recN (h : NestedInstallExt Ms env envOut new)
    (hMs : ∀ n ∈ Ms, n ∈ new.map (·.name)) :
    ∀ (n : Name) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      envOut.find? (n.str "rec") = some (.recInfo cv mI rP rules) →
      n.str "rec" ∈ new.map (·.name) → n ∈ new.map (·.name) := by
  intro n cv mI rP rules hf hmem
  obtain ⟨hc, hname⟩ := h.toConsExt.newOf hf (h.toConsExt.freshN _ hmem)
  exact hMs _ (h.2.2.1 _ hc cv mI rP rules rfl n hname)

omit [SetTheory V] in
/-- **A new container is a member** (`BlockInstallExt.indMs`). -/
theorem indMs (h : NestedInstallExt Ms env envOut new) {J : Name} {cv : ConstantVal}
    {caps : IndCaps} (hf : envOut.find? J = some (.indInfo cv caps))
    (hJ : J ∈ new.map (·.name)) : J ∈ Ms := by
  obtain ⟨hc, hname⟩ := h.toConsExt.newOf hf (h.toConsExt.freshN _ hJ)
  rw [← hname]
  exact h.2.1 _ hc cv caps rfl

omit [SetTheory V] in
/-- **The guard** (`BlockInstallExt.tableCross`): the only projection
slots the install creates are at the block's own members. -/
theorem tableCross (h : NestedInstallExt Ms env envOut new) : TableCross Ms env envOut where
  find := fun hf => h.toConsExt.ext _ _ hf
  lit := litGuardsMono_of_findPreserved (fun hf => h.toConsExt.ext _ _ hf)
  proj := fun sn i entry h0 h1 => by
    obtain ⟨tbl, hf0, hi, -⟩ := ConLeche.Env.findProj?_some h1
    cases hf : env.find? (ConLeche.projTableName sn) with
    | some c =>
      have hpres := h.toConsExt.ext _ _ hf
      rw [hf0] at hpres
      obtain rfl : c = .projInfo tbl := Option.some.inj hpres.symm
      rw [ConLeche.Env.findProj?_of_table hf hi] at h0
      exact nomatch h0
    | none =>
      obtain ⟨hc, hname⟩ := h.toConsExt.newOf hf0 hf
      have hstruct : ConLeche.projTableName tbl.structName = ConLeche.projTableName sn := hname
      obtain rfl : tbl.structName = sn := by
        unfold ConLeche.projTableName at hstruct
        exact (ConLeche.Name.str.inj (ConLeche.Name.num.inj hstruct).1).1
      exact h.2.2.2 _ hc tbl rfl

end NestedInstallExt

omit [SetTheory V] in
/-- **A NEW MIMIC RECURSOR'S BASE IS THE BLOCK'S FIRST MEMBER** — the
clause `ContainerOwnPinsSyn.crossIndOf` needs of the NESTED route,
whose install DOES cons mimic recursors and for which
`BlockInstallExt.mimN`'s argument is therefore unavailable
(`NestedInstallExt`'s recursor clause is conditional on `T.rec` and
says nothing about `T₁.rec_j`, by design — DESIGN §U.66 (b)).

The argument is the install's own name list instead of a kind clause:
past the tables' stage (`nestedTables_mem_inv`, which conses only
`projInfo`s) a `.recInfo` the output stores is one of the RESTORED
recursors (`storeNestedRecs_consts`) or one the PRE-BLOCK environment
already had — the two cons stages in between add `indInfo`s and
`ctorInfo`s only.  The pre-block case is excluded by the name's
freshness (`hfreshN` at a name the install claims as new); a restored
recursor's name is the name the restore was ASKED for
(`restoreRecTys_names_of_mem`), which is either a member's `T.rec` (no
mimic's name, `appendIndexAfter_rec_ne_rec`) or `p.mimicRecName i`,
whose base is the block's first former — a member, hence new
(`hMs`).

The two length side conditions are `NestedTailIn.lenM`/`lenN` at the
run (with `hcnt`, the run's own count); `hk` is `nested_kpos`. -/
theorem nestedMimN {envOut envR : Env} {p : ConLeche.NestedParts} {N : List Name}
    {R : ConLeche.RestoreTbl} {stored : List ConLeche.AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {cvRms cvRns : List ConstantVal}
    {rulesM rulesN : List (List RecRule)}
    {l : List (Name × Option ConLeche.ProjTable × List (ConstantVal × Nat × Nat))}
    (hk : 0 < p.k)
    (hrm : ConLeche.restoreRecTys (m := ConLeche.CheckM) (fueledOps μ F) envR R p.lps
      ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
      (stored.take p.k) = .ok cvRms)
    (hrn : ConLeche.restoreRecTys (m := ConLeche.CheckM) (fueledOps μ F) envR R p.lps
      ((List.range p.numNested).map p.mimicRecName) (stored.drop p.k) = .ok cvRns)
    (hlenM : cvRms.length ≤ p.k) (hlenN : cvRns.length ≤ p.numNested)
    (htbl : ConLeche.nestedTables (m := ConLeche.CheckM) l
      (ConLeche.storeNestedRecs
        ((cvRms.zip ((stored.take p.k).zip rulesM)).map
            (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
          ++ (cvRns.zip ((stored.drop p.k).zip rulesN)).map
            (fun (cv, a, rs) => (cv, a.mI, a.rP, rs)))
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))) = .ok envOut)
    (hfreshN : ∀ n ∈ N, env.find? n = none)
    (hMs : ∀ n ∈ p.memberNames, n ∈ N) :
    ∀ (n : Name) (j : Nat) (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      envOut.find? (Name.appendIndexAfter (n.str "rec") j) = some (.recInfo cv mI rP rules) →
      Name.appendIndexAfter (n.str "rec") j ∈ N → n ∈ N := by
  intro n j cv mI rP rules hf hmem
  have hfresh : env.find? (Name.appendIndexAfter (n.str "rec") j) = none := hfreshN _ hmem
  have hnm : cv.name = Name.appendIndexAfter (n.str "rec") j := ConLeche.Env.find?_name hf
  -- the answer is a constant the install's output stores; the tables' stage
  -- conses projection tables only, so the store already had it
  have hmemS := (ConLeche.nestedTables_mem_inv htbl _ (ConLeche.find?_mem hf)).resolve_right
    (fun ⟨_, htblEq⟩ => nomatch htblEq)
  -- the store's constants: the restored recursors, then the two cons stages'
  rw [ConLeche.Semantics.storeNestedRecs_consts, List.mem_append, List.mem_reverse,
    List.mem_map] at hmemS
  rcases hmemS with ⟨x, hx, hxc⟩ | hbase
  · -- a restored recursor: its name is the name the restore was asked for
    have hxname : x.1.name = Name.appendIndexAfter (n.str "rec") j := by
      rw [(ConstantInfo.recInfo.inj hxc).1, hnm]
    have hlenM' : cvRms.length ≤ ((List.range p.k).map fun mIdx =>
        ((p.formers.getD mIdx default).1.name.str "rec")).length := by
      rw [List.length_map, List.length_range]; exact hlenM
    have hlenN' : cvRns.length ≤ ((List.range p.numNested).map p.mimicRecName).length := by
      rw [List.length_map, List.length_range]; exact hlenN
    have hxmem : x.1 ∈ cvRms ∨ x.1 ∈ cvRns := by
      rcases List.mem_append.mp hx with hx' | hx' <;>
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx'
      · exact Or.inl (List.of_mem_zip hy).1
      · exact Or.inr (List.of_mem_zip hy).1
    rcases hxmem with hx' | hx'
    · -- a member's own recursor: no mimic carries that name
      obtain ⟨i, -, hi⟩ :=
        List.mem_map.mp (ConLeche.restoreRecTys_names_of_mem hrm hlenM' _ hx')
      rw [hxname] at hi
      exact absurd hi.symm (appendIndexAfter_rec_ne_rec n _ j)
    · -- a mimic: its base is the block's first former, which is a member
      obtain ⟨i, -, hi⟩ :=
        List.mem_map.mp (ConLeche.restoreRecTys_names_of_mem hrn hlenN' _ hx')
      rw [hxname] at hi
      have hmimEq : p.mimicRecName i
          = Name.appendIndexAfter ((p.formers.headD default).1.name.str "rec") (i + 1) := rfl
      rw [hmimEq] at hi
      refine hMs _ ?_
      rw [appendIndexAfter_rec_base hi.symm]
      show (p.formers.headD default).1.name ∈ p.formers.map (·.1.name)
      have h0 : p.formers[0]? = some (p.formers.headD default) := by
        cases hl : p.formers with
        | nil => simp [ConLeche.NestedParts.k, hl] at hk
        | cons f rest => rfl
      exact List.mem_map_of_mem (List.mem_of_getElem? h0)
  · -- the pre-block environment's own: then the name is not new
    rw [ConLeche.Semantics.consNestedCtors_consts, List.mem_append, List.mem_reverse,
      List.mem_map, ConLeche.Semantics.consNestedFormers_consts, List.mem_append,
      List.mem_reverse, List.mem_map] at hbase
    rcases hbase with ⟨y, -, hy⟩ | hbase'
    · exact nomatch hy
    rcases hbase' with ⟨y, -, hy⟩ | hbase''
    · exact nomatch hy
    refine absurd hfresh ?_
    rw [← hnm]
    exact fun hnone => nomatch (List.find?_eq_none.mp hnone _ hbase'' (by rw [beq_iff_eq]; rfl))

/-! ### The mutual install's four stages -/

omit [SetTheory V] in
/-- One fresh cons, as the crossing sees it. -/
theorem BlockInstallExt.cons {Ms : List Name} {env : Env} {c₀ : ConstantInfo}
    (hfresh : env.find? c₀.name = none)
    (hi : ∀ (cv : ConstantVal) (caps : IndCaps), c₀ = .indInfo cv caps → c₀.name ∈ Ms)
    (hr : ∀ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      c₀ = .recInfo cv mI rP rules → ∃ n' ∈ Ms, c₀.name = n'.str "rec")
    (hp : ∀ tbl : ConLeche.ProjTable, c₀ = .projInfo tbl → tbl.structName ∈ Ms) :
    BlockInstallExt Ms env ⟨c₀ :: env.consts⟩ [c₀] := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> intro c hc <;>
    (obtain rfl := List.mem_singleton.mp hc)
  · exact hfresh
  · exact hi
  · exact hr
  · exact hp

omit [SetTheory V] in
/-- Stage 1: the formers, consed as the block's members. -/
theorem consMutualFormers_installExt {fms : List MutualFormerA} {env : Env}
    (hfresh : ∀ f ∈ fms, env.find? f.cvTa.name = none) :
    BlockInstallExt (fms.map (·.cvTa.name)) env (ConLeche.consMutualFormers fms env)
      ((fms.map fun f => ConstantInfo.indInfo f.cvTa {}).reverse) := by
  refine ⟨consMutualFormers_consts, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩ <;>
    (simp only [List.mem_reverse, List.mem_map] at hc; obtain ⟨f, hf, rfl⟩ := hc)
  · exact hfresh f hf
  · exact fun _ _ _ => List.mem_map_of_mem hf
  · exact fun _ _ _ _ heq => nomatch heq
  · exact fun _ heq => nomatch heq

omit [SetTheory V] in
/-- Stage 3: the constructors' conses — no container, no recursor, no table. -/
theorem consMutualCtors_installExt {Ms : List Name} {nP : Nat}
    {ctorsA : List (ConstantVal × Nat)} {env : Env}
    (hfresh : ∀ c ∈ ctorsA, env.find? c.1.name = none) :
    BlockInstallExt Ms env (ConLeche.consMutualCtors nP ctorsA env)
      ((ctorsA.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse) := by
  refine ⟨consMutualCtors_consts, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩ <;>
    (simp only [List.mem_reverse, List.mem_map] at hc; obtain ⟨cA, hcA, rfl⟩ := hc)
  · exact hfresh cA hcA
  · exact fun _ _ heq => nomatch heq
  · exact fun _ _ _ _ heq => nomatch heq
  · exact fun _ heq => nomatch heq

omit [SetTheory V] in
/-- Stage 4: the recursors' group store — every entry a MEMBER's recursor. -/
theorem storeMutualRecs_installExt {Ms : List Name} {env₂ : Env} {b : MutualBlock}
    {fms : List MutualFormerA} {rulesOf : List (List (MutualCtor × Expr))}
    {l : List (ConstantVal × Nat)} {env : Env}
    (hfresh : ∀ q ∈ l, env.find? (Prod.fst q).name = none)
    (hrec : ∀ q ∈ l, ∃ n' ∈ Ms, (Prod.fst q).name = n'.str "rec") :
    BlockInstallExt Ms env (ConLeche.storeMutualRecs env₂ b fms rulesOf l env)
      ((l.map fun q => ConstantInfo.recInfo q.1
        (b.rulePrefix + (fms.getD q.2 default).nIdx) b.rulePrefix
        (ConLeche.mutualRules env₂.find? q.1.name b.nP
          (b.rulePrefix + (fms.getD q.2 default).nIdx) b.rulePrefix q.1.type
          (rulesOf.getD q.2 []))).reverse) := by
  refine ⟨storeMutualRecs_consts, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩ <;>
    (simp only [List.mem_reverse, List.mem_map] at hc; obtain ⟨q, hq, rfl⟩ := hc)
  · exact hfresh q hq
  · exact fun _ _ heq => nomatch heq
  · exact fun _ _ _ _ _ => hrec q hq
  · exact fun _ heq => nomatch heq

omit [SetTheory V] in
/-- Stage 5: the structure-like members' projection tables — every
table is a MEMBER's. -/
theorem mutualTables_installExt {Ms : List Name} {b : MutualBlock}
    {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} :
    ∀ {l : List (MutualFormerA × Nat)} {env env' : Env},
      ConLeche.mutualTables (m := ConLeche.CheckM) b ctorsA sortss l env = .ok env' →
      (∀ p ∈ l, p.1.cvTa.name ∈ Ms) →
      ∃ new : List ConstantInfo, BlockInstallExt Ms env env' new
  | [], env, env', h, _ => by
    obtain rfl := ConLeche.mutualTables_nil_inv h
    exact ⟨[], BlockInstallExt.rfl' Ms _⟩
  | (f, mIdx) :: rest, env, env', h, hTs => by
    obtain ⟨envI, hI, hrest⟩ := ConLeche.mutualTables_inv h
    obtain ⟨new₂, h₂⟩ := mutualTables_installExt hrest
      (fun q hq => hTs q (List.mem_cons_of_mem _ hq))
    rcases ConLeche.mutualMemberTable_inv hI with rfl | ⟨J, c, -, -, htbl⟩
    · exact ⟨new₂, h₂⟩
    · obtain ⟨bodies, -, -, -, hfreshTbl, rfl⟩ := ConLeche.checkStructProjTable_inv htbl
      refine ⟨_, BlockInstallExt.trans (BlockInstallExt.cons ?_ ?_ ?_ ?_) h₂⟩
      · exact hfreshTbl
      · exact fun _ _ heq => nomatch heq
      · exact fun _ _ _ _ heq => nomatch heq
      · intro tbl heq
        obtain rfl := ConstantInfo.projInfo.inj heq
        exact hTs (f, mIdx) List.mem_cons_self

omit [SetTheory V] in
/-- The generated recursors' names, read off the recursor-type stage
(`checkMutualRecTy_shape`: the constant it hands back IS
`⟨b.recName mIdx, b.rlps, recTy⟩`). -/
theorem checkMutualRecTys_names {env : Env} {b : MutualBlock} {F : Nat}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4} {cvRas : List ConstantVal}
    {streamRecs : Option (List (ConstantVal × List RecRule))}
    (h : ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F) env b formers4 ctors4
      streamRecs b.k = .ok cvRas) :
    ∀ q ∈ cvRas.zipIdx, q.2 < b.k ∧ (Prod.fst q).name = b.recName q.2 := by
  obtain ⟨hlen, hall⟩ := ConLeche.checkMutualRecTys_inv h
  intro q hq
  obtain ⟨cvRa, mIdx⟩ := q
  have hget : cvRas[mIdx]? = some cvRa := List.mk_mem_zipIdx_iff_getElem?.mp hq
  have hlt : mIdx < b.k := by
    have := (List.getElem?_eq_some_iff.mp hget).1
    omega
  obtain ⟨cvRa', hget', hrec⟩ := hall mIdx hlt
  obtain rfl := Option.some.inj (hget.symm.trans hget')
  obtain ⟨recTy, sty, u, -, -, -, -, -, -, -, -, rfl⟩ := ConLeche.checkMutualRecTy_shape hrec
  exact ⟨hlt, rfl⟩

/-! ### The native install's four stages -/

omit [SetTheory V] in
/-- The constructors' conses, listed (the first constructor deepest). -/
theorem consSumCtors_consts {nP : Nat} :
    ∀ {ctorsA : List (ConstantVal × Nat)} {env : Env},
      (ConLeche.consSumCtors nP ctorsA env).consts
        = (ctorsA.map (fun c => ConstantInfo.ctorInfo c.1 nP c.2)).reverse ++ env.consts
  | [], env => by simp [ConLeche.consSumCtors]
  | c :: cs, env => by
    simp only [ConLeche.consSumCtors, List.map_cons, List.reverse_cons]
    rw [consSumCtors_consts]
    simp

omit [SetTheory V] in
/-- Native stage 1: the former, consed as the block's single member. -/
theorem consNativeFormer_installExt {p : NativeParts} {cvTa : ConstantVal} {env : Env}
    (hTname : cvTa.name = p.cvT.name) (hfresh : env.find? p.cvT.name = none) :
    BlockInstallExt [p.cvT.name] env ⟨.indInfo cvTa (ConLeche.nativeCaps p) :: env.consts⟩
      [.indInfo cvTa (ConLeche.nativeCaps p)] :=
  BlockInstallExt.cons (by show env.find? cvTa.name = none; rw [hTname]; exact hfresh)
    (fun _ _ _ => by show cvTa.name ∈ _; rw [hTname]; exact List.mem_singleton_self _)
    (fun _ _ _ _ heq => nomatch heq) (fun _ heq => nomatch heq)

omit [SetTheory V] in
/-- Native stage 2: the constructors' conses — no container, no recursor, no table. -/
theorem consSumCtors_installExt {Ms : List Name} {nP : Nat}
    {ctorsA : List (ConstantVal × Nat)} {env : Env}
    (hfresh : ∀ c ∈ ctorsA, env.find? c.1.name = none) :
    BlockInstallExt Ms env (ConLeche.consSumCtors nP ctorsA env)
      ((ctorsA.map fun c => ConstantInfo.ctorInfo c.1 nP c.2).reverse) := by
  refine ⟨consSumCtors_consts, fun c hc => ?_, fun c hc => ?_, fun c hc => ?_,
    fun c hc => ?_⟩ <;>
    (simp only [List.mem_reverse, List.mem_map] at hc; obtain ⟨cA, hcA, rfl⟩ := hc)
  · exact hfresh cA hcA
  · exact fun _ _ heq => nomatch heq
  · exact fun _ _ _ _ heq => nomatch heq
  · exact fun _ heq => nomatch heq

omit [SetTheory V] in
/-- Native stage 4: the projection table at a structure-like block —
the only table the stage conses is the MEMBER's; at any other block it
conses nothing. -/
theorem nativeTable_installExt {p : NativeParts} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {env envOut : Env}
    (h : ConLeche.checkNativeTable (m := ConLeche.CheckM) p ctorsA sortss env = .ok envOut) :
    ∃ new : List ConstantInfo, BlockInstallExt [p.cvT.name] env envOut new := by
  unfold ConLeche.checkNativeTable at h
  split at h
  · next cA sorts =>
    split at h
    · next =>
      obtain ⟨bodies, -, -, -, hfreshTbl, rfl⟩ := ConLeche.checkStructProjTable_inv h
      refine ⟨_, BlockInstallExt.cons hfreshTbl (fun _ _ heq => nomatch heq)
        (fun _ _ _ _ heq => nomatch heq) (fun tbl heq => ?_)⟩
      obtain rfl := ConstantInfo.projInfo.inj heq
      exact List.mem_singleton_self _
    · next =>
      obtain rfl := Except.ok.inj h
      exact ⟨[], BlockInstallExt.rfl' _ _⟩
  · next =>
    obtain rfl := Except.ok.inj h
    exact ⟨[], BlockInstallExt.rfl' _ _⟩

/-! ### The native block IS its own container group -/

section Native

variable {F : Nat} {env env₁ envC env₂ : Env} {p : NativeParts} {cvTa cvRa : ConstantVal}
  {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)} {rhss : List Expr}
  {bsT : List (Expr × ConLeche.BinderMeta)}
  {ppsAll : (Name → Nat) → List (Nat × Nat × AnnotTerm)} {uAV : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {ksF : Nat → List RecFieldKind} {fvsPF xFvsF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {fssZ : (Name → Nat) → List (List AnnotTerm)}

local notation "DN" => (BlockModel.ofNative (V := V) p.nP p.resSort p.isProp p.large env
  p.cvT.name p.nIdx ppsAll uAV ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF)

/-- **An ordinary field's opened domain mentions no member**, at a
native block: `MutualOrdFree`'s twin at the single-member list
(DESIGN §U.46 (b)).  Unlike the mutual route's, it asks the kernel for
nothing — the native install's own opened-form guard already states it
(`nativeOpenedOk`'s `.ordinary` clause is the domain's resolution at
the PRE-BLOCK environment, where the member is fresh), and the model
tier reads that guard positionally (`FixOpened.ord`). -/
@[expose] def NativeOrdFree (p : NativeParts) (ctorsA : List (ConstantVal × Nat)) : Prop :=
  ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
    ∀ (fvsP xFvs : List Expr) (crest xrest : Expr),
      ConLeche.openPisAtFvars p.nP cA.1.type 0 = some (fvsP, crest) →
      ConLeche.openPisAtFvars cA.2 crest p.nP = some (xFvs, xrest) →
      ∀ (l : Nat) (x : Expr), xFvs[l]? = some x →
        (p.kinds.getD J []).getD l .ordinary = .ordinary →
        ConLeche.mentionsMember [p.cvT.name] x.fvarTypeD = false

/-- `NativeOrdFree` off the install's own record: the opened form is the
constructor data's (`FixCtorDataI.opens`, deterministic, so the
hypothesis' openings ARE the record's), its ordinary domains resolve at
the pre-block environment (`FixOpened.ord`) and the member is fresh
there (`NativeSyntaxFacts.Tfresh`). -/
theorem nativeOrdFree_of {m : EnvModel V envC}
    (hf : NativeSyntaxFacts (μ := μ) (env := env) (env₁ := env₁) (env₂ := env₂) m F p cvTa cvRa
      ctorsA sortss rhss bsT ppsAll uAV idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF
      fssZ) :
    NativeOrdFree p ctorsA := by
  intro J cA hJ fvsP xFvs crest xrest hop1 hop2 l x hx hk
  have hJlt : J < ctorsA.length := (List.getElem?_eq_some_iff.mp hJ).1
  obtain ⟨-, -, hdata⟩ := hf.ctors J cA hJ
  obtain ⟨crest', hop1', hop2'⟩ := hdata.opens
  have heq1 := Option.some.inj (hop1'.symm.trans hop1)
  have hcrest : crest' = crest := congrArg Prod.snd heq1
  subst hcrest
  have heq2 := Option.some.inj (hop2'.symm.trans hop2)
  have hxf : xFvsF J = xFvs := congrArg Prod.fst heq2
  rw [← hxf] at hx
  have hkF : p.kinds.getD J [] = ksF J := by
    rw [List.getD_eq_getElem?_getD, hf.ks J hJlt]; rfl
  rw [hkF] at hk
  show (List.any [p.cvT.name] fun T => x.fvarTypeD.mentionsConst T) = false
  simp only [List.any_cons, List.any_nil, Bool.or_false]
  exact ConLeche.rk_mentionsConst_false_of_constsResolve (hdata.opened.ord l x hx hk) hf.Tfresh

/-- The member and the constructors inhabit their types' readings — the
model's own `mem_type` at the stored constants, with the former's and
the constructors' readings off the record. -/
theorem nativeTyped {mpC : EnvModelM V μ envC}
    (hf : NativeSyntaxFacts (μ := μ) (env := env) (env₁ := env₁) (env₂ := env₂) mpC.base2 F p cvTa
      cvRa ctorsA sortss rhss bsT ppsAll uAV idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF
      fssZ) (ψ : Name → Nat) :
    FormersTyped mpC.base2 DN ψ ∧ CtorsTyped mpC.base2 DN ψ := by
  refine ⟨?_, ?_⟩
  · intro t ht ρ
    obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
    have hname : (ConstantInfo.indInfo cvTa (ConLeche.nativeCaps p)).name = p.cvT.name := hf.Tname
    have := mpC.mem_type _ (ConLeche.Semantics.Env.find?_mem hf.fT) ψ _ (hf.former.read ψ) ρ
    rw [hname] at this
    exact this
  · intro c hc j cA hj ρ
    obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
    obtain ⟨hfind, -, hdata⟩ := hf.ctors j cA hj
    exact mpC.mem_type _ (ConLeche.Semantics.Env.find?_mem hfind) ψ _ (hdata.read ψ) ρ

/-- **The native block IS its own container group** (task #315 M7-3
session 8): `ContainerModeled.of_readBack` at the single-member list
the route's K.34 Bool certifies.  Every DATA clause is the block
model's own shape at `k = 1` (`memberNames = [T]`, `ctorsM _ = ctorsA`,
`pins = []`), the pin clauses are vacuous, `ordFree` is
`nativeOrdFree_of` through the constructor data's openings, and the
representation is the caller's — `nativeIsBlockModel` crossed to the
OUTPUT model. -/
theorem nativeContainerModeled {envO : Env} {m : EnvModel V envO} {mC : EnvModel V envC}
    {rules : List RecRule}
    (hf : NativeSyntaxFacts (μ := μ) (env := env) (env₁ := env₁) (env₂ := env₂) mC F p cvTa cvRa
      ctorsA sortss rhss bsT ppsAll uAV idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF
      fssZ)
    (hI : IsBlockModel m p.cvT.name cvTa cvRa p.majorIdx p.rulePrefix rules DN 0)
    (htyped : ∀ ψ : Name → Nat, FormersTyped m DN ψ ∧ CtorsTyped m DN ψ)
    (hown : ContainerOwnPinsSyn (V := V) envO DN)
    (hnpC : ∀ (j : Nat) (cA : ConstantVal × Nat), ctorsA[j]? = some cA →
      ProjFree [p.cvT.name] cA.1.type) :
    ContainerModeled m (ConLeche.blockContainerInfo p.nP [(cvTa, ctorsA)]) DN := by
  have hord := nativeOrdFree_of hf
  refine ContainerModeled.of_readBack rfl rfl rfl (fun i hi => ?_) (fun i hi => ?_)
    (fun c hc => ?_) (fun ψ => ⟨(htyped ψ).1, (htyped ψ).2, PinsTyped.of_noPins rfl ψ⟩)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => Iff.rfl) (fun i j l x hi hj hx hk => ?_)
    (fun q hq => absurd hq (Nat.not_lt_zero q))
    (fun _ _ _ _ _ _ _ _ _ hq _ => absurd hq (Nat.not_lt_zero _))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hq _ => absurd hq (Nat.not_lt_zero _))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ hq _ => absurd hq (Nat.not_lt_zero _))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq _ => absurd hq (Nat.not_lt_zero _))
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hq _ => absurd hq (Nat.not_lt_zero _))
    (fun i j cA hi hj => by
      obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
      exact hnpC j cA hj)
    (fun q hq => absurd hq (Nat.not_lt_zero q)) (fun q hq => absurd hq (Nat.not_lt_zero q))
    (fun q hq => absurd hq (Nat.not_lt_zero q))
    hown
    (fun q hq => absurd hq (Nat.not_lt_zero q))
    (fun _ _ => ContainerPinParams.of_noPins rfl) (fun i hi => ?_)
    (fun _ _ hq _ _ => absurd hq (Nat.not_lt_zero _))
    (fun _ _ _ hq _ _ => absurd hq (Nat.not_lt_zero _))
    (fun q hq => absurd hq (Nat.not_lt_zero q))
    (fun q hq => absurd hq (Nat.not_lt_zero q))
    (fun q hq => absurd hq (Nat.not_lt_zero q))
  · obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    exact hf.Tname.symm
  · obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    rfl
  · obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
    exact ⟨cvTa, cvRa, p.majorIdx, p.rulePrefix, rules, hI⟩
  · obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    obtain ⟨cA, hjA⟩ : ∃ cA, ctorsA[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj⟩
    obtain ⟨-, -, hdata⟩ := hf.ctors j cA hjA
    obtain ⟨crest, hop1, hop2⟩ := hdata.opens
    have hkF : p.kinds.getD j [] = ksF j := by
      rw [List.getD_eq_getElem?_getD, hf.ks j hj]; rfl
    exact hord j cA hjA _ _ _ _ hop1 hop2 l x hx (by rw [hkF]; exact hk)
  · obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
    refine ⟨cvRa, p.majorIdx, p.rulePrefix, rules, ?_⟩
    show IsBlockModel m cvTa.name cvTa cvRa p.majorIdx p.rulePrefix rules DN 0
    rw [hf.Tname]
    exact hI

/-- **THE NATIVE ROUTE'S OWN-PIN TABLE IS EMPTY** (task #315 K.43,
DESIGN §U.74 (c)): the clause `ContainerOwnPinsSyn` at the block this
route installed, from the route's own two Bools and nothing else.

K.43's Bool (`NativeSyntaxFacts.ownMimics`) says the route left no
mimic recursor under its member, and K.34's read-back says that member
reads back the block's own group — a ONE-member group, so its
`members.head?` is that same member.  `containerOwnPinsAt` therefore
stops at its first step at every instantiation
(`containerOwnPinsAt_nil`) and the table is empty; the block model's
recorded pins are never needed (a native block has none).

This is the clause `ContainerModeled.ownPins` at this route's site. -/
theorem nativeOwnPins_of {mC : EnvModel V envC}
    (hf : NativeSyntaxFacts (μ := μ) (env := env) (env₁ := env₁) (env₂ := env₂) mC F p cvTa cvRa
      ctorsA sortss rhss bsT ppsAll uAV idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF
      fssZ) :
    ContainerOwnPinsSyn (V := V) env₂ DN := by
  refine ContainerOwnPinsSyn.of_noMimics rfl hf.ownMimics fun i hi => ?_
  obtain rfl : i = 0 := Nat.lt_one_iff.mp hi
  refine ⟨ConLeche.blockContainerInfo p.nP [(cvTa, ctorsA)],
    ⟨cvTa.name, cvTa.levelParams, cvTa.type,
      ctorsA.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩, ?_, rfl, rfl⟩
  show ConLeche.containerInfo? env₂ p.cvT.name = _
  rw [← hf.Tname]
  exact containerInfo?_of_readBack (nP := p.nP) hf.readBack (i := 0) (c := (cvTa, ctorsA)) rfl

/-- **A constructor's stored type is guarded at the block's member**:
the annotation pass creates a `.proj T j` node only at a slot that
RESOLVES, and the member's slots are empty at the formers' environment
(`ProjOkT` at the pre-block environment, where the member is fresh).
The install's second guard source (DESIGN §U.41 (f)) on the native
route. -/
theorem nativeCtorProjFree {m : EnvModel V envC} (hproj : ConLeche.ProjOkT env)
    (hf : NativeSyntaxFacts (μ := μ) (env := env) (env₁ := env₁) (env₂ := env₂) m F p cvTa cvRa
      ctorsA sortss rhss bsT ppsAll uAV idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF
      fssZ)
    {j : Nat} {cA : ConstantVal × Nat} (hj : ctorsA[j]? = some cA) :
    ProjFree [p.cvT.name] cA.1.type := by
  obtain ⟨c, -, -, -, -, -, -, sorts, -, hCtor⟩ := hf.runOf j cA hj
  obtain ⟨⟨ty', hccvC⟩, -, -⟩ := ConLeche.checkSumCtor_shape hCtor
  obtain ⟨-, -, -, -, -, hnfC, typeC, -, -, hannC, -, -, -, -, htyC⟩ :=
    ConLeche.checkConstantVal_inv hccvC
  intro T' hT' j'
  obtain rfl := List.mem_singleton.mp hT'
  have hslot : env₁.findProj? p.cvT.name j' = none := by
    rw [hf.env₁eq]
    exact findProj?_none_cons (fun _ hh => nomatch hh)
      (findProj?_none_of_indFresh hproj hf.Tfresh j')
  have hty : cA.1.type = typeC := by rw [htyC]
  rw [hty]
  exact ConLeche.annotateCore_noProjAt μ hannC hnfC hslot


/-- **The native install's conses, as the crossing and the field see
them**: the former's cons as the block's single member, the
constructors' conses, the recursor's cons (at the recursor-name pin,
`checkNativeRec`'s own) and the projection table, at
`Ms := [p.cvT.name]` and in three pieces — the block model is built at
the CONSTRUCTORS' environment and crosses the last two, while the field
`EnvBlocksOf` crosses all of them. -/
theorem nativeInstallExt {m : EnvModel V envC}
    (hf : NativeSyntaxFacts (μ := μ) (env := env) (env₁ := env₁) (env₂ := env₂) m F p cvTa cvRa
      ctorsA sortss rhss bsT ppsAll uAV idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF
      fssZ) :
    ∃ newC newR newT : List ConstantInfo,
      BlockInstallExt [p.cvT.name] env envC newC ∧
      BlockInstallExt [p.cvT.name] envC
        ⟨.recInfo cvRa p.majorIdx p.rulePrefix (ConLeche.sumRules envC.find? cvRa.name p.nP
          p.majorIdx p.rulePrefix cvRa.type ctorsA rhss) :: envC.consts⟩ newR ∧
      BlockInstallExt [p.cvT.name]
        ⟨.recInfo cvRa p.majorIdx p.rulePrefix (ConLeche.sumRules envC.find? cvRa.name p.nP
          p.majorIdx p.rulePrefix cvRa.type ctorsA rhss) :: envC.consts⟩ env₂ newT ∧
      p.cvT.name ∈ newC.map (·.name) := by
  have hE1 : BlockInstallExt [p.cvT.name] env env₁ [.indInfo cvTa (ConLeche.nativeCaps p)] := by
    rw [hf.env₁eq]
    exact consNativeFormer_installExt hf.Tname hf.Tfresh
  have hE2 : BlockInstallExt [p.cvT.name] env₁ envC
      ((ctorsA.map fun c => ConstantInfo.ctorInfo c.1 p.nP c.2).reverse) := by
    rw [hf.envCeq]
    refine consSumCtors_installExt ?_
    intro c hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
    obtain ⟨c', -, -, -, hfresh, -, -, sorts, -, -⟩ := hf.runOf j c hj
    exact hfresh
  have hRname : cvRa.name = p.cvT.name.str "rec" := by
    obtain ⟨cvRi, recTy, sty, u, -, -, -, -, -, -, -, -, -, -, hcvRa⟩ :=
      ConLeche.checkNativeRec_shape hf.recRun
    rw [show cvRa.name = p.cvR.name from by rw [hcvRa]]
    exact hf.Rname
  have hE3 := BlockInstallExt.cons (Ms := [p.cvT.name])
    (c₀ := .recInfo cvRa p.majorIdx p.rulePrefix (ConLeche.sumRules envC.find? cvRa.name p.nP
      p.majorIdx p.rulePrefix cvRa.type ctorsA rhss))
    (nativeRec_fresh hf.recRun) (fun _ _ heq => nomatch heq)
    (fun _ _ _ _ _ => ⟨p.cvT.name, List.mem_singleton_self _, hRname⟩)
    (fun _ heq => nomatch heq)
  obtain ⟨newT, hE4⟩ := nativeTable_installExt hf.table
  refine ⟨_, _, newT, hE1.trans hE2, hE3, hE4, ?_⟩
  rw [List.map_append, List.mem_append]
  right
  show p.cvT.name ∈ [(ConstantInfo.indInfo cvTa (ConLeche.nativeCaps p)).name]
  exact List.mem_singleton.mpr hf.Tname.symm

end Native

/-! ### `declMutualB` — the model WITH ITS BLOCKS survives a mutual block -/

/-- **The mutual install's conses, as `EnvBlocksOf.crossIndP` reads
them**: the formers, the constructors, the recursors' group store and
the structure-like members' projection tables, composed
(`BlockInstallExt.trans`) at the block's own members. -/
theorem mutualInstallExt {F : Nat} {env : Env} {b : MutualBlock}
    {streamRecs : Option (List (ConstantVal × List RecRule))} {fms : List MutualFormerA}
    {f₀ : MutualFormerA} {ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    {formers4 : List MutualFormer} {ctors4 : List MutualCtor4} {cvRas : List ConstantVal}
    {rulesOf : List (List (MutualCtor × Expr))} {envOut : Env} {g : Bool}
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env g
      = .ok (ConLeche.consMutualFormers fms env, fms))
    (hctors : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) false
      b.ctors = .ok (ctorsA, sortss))
    (hrecFresh : ∀ q ∈ cvRas.zipIdx,
      (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)).find?
        (Prod.fst q).name = none)
    (hrectys : ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) b formers4
      ctors4 streamRecs b.k = .ok cvRas)
    (htbl : ConLeche.mutualTables (m := ConLeche.CheckM) b ctorsA sortss fms.zipIdx
      (ConLeche.storeMutualRecs
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) b fms
        rulesOf cvRas.zipIdx
        (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))) = .ok envOut) :
    ∃ new newR : List ConstantInfo,
      BlockInstallExt (fms.map (·.cvTa.name)) env
        (ConLeche.storeMutualRecs
          (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env)) b fms
          rulesOf cvRas.zipIdx
          (ConLeche.consMutualCtors b.nP ctorsA (ConLeche.consMutualFormers fms env))) newR ∧
      BlockInstallExt (fms.map (·.cvTa.name)) env envOut new ∧
      ∀ n ∈ fms.map (·.cvTa.name), n ∈ new.map (·.name) := by
  have hmemFresh : ∀ f ∈ fms, env.find? f.cvTa.name = none := by
    intro f hf
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hf
    exact (mutualMemberNames hformers t f ht).1
  have hrecMs : ∀ q ∈ cvRas.zipIdx,
      ∃ n' ∈ fms.map (·.cvTa.name), (Prod.fst q).name = n'.str "rec" := by
    intro q hq
    obtain ⟨hlt, hname⟩ := checkMutualRecTys_names hrectys q hq
    refine ⟨(b.formers.getD q.2 default).1.name, ?_, hname⟩
    rw [mutualMemberNames_eq hformers]
    show _ ∈ b.formers.map (·.1.name)
    have hlt' : q.2 < b.formers.length := hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt']
    exact List.mem_map_of_mem (List.getElem_mem hlt')
  have hzipTs : ∀ q ∈ fms.zipIdx, q.1.cvTa.name ∈ fms.map (·.cvTa.name) := by
    intro q hq
    exact List.mem_map_of_mem (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hq))
  obtain ⟨newT, E4⟩ := mutualTables_installExt (Ms := fms.map (·.cvTa.name)) htbl hzipTs
  refine ⟨_, _, (((consMutualFormers_installExt hmemFresh).trans
    (consMutualCtors_installExt (nP := b.nP) (checkMutualCtors_fresh hctors))).trans
    (storeMutualRecs_installExt hrecFresh hrecMs)),
    ((((consMutualFormers_installExt hmemFresh).trans
    (consMutualCtors_installExt (nP := b.nP) (checkMutualCtors_fresh hctors))).trans
    (storeMutualRecs_installExt hrecFresh hrecMs)).trans E4), ?_⟩
  intro n hn
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
  rw [List.map_append, List.mem_append]; right
  rw [List.map_append, List.mem_append]; right
  rw [List.map_append, List.mem_append]; right
  rw [List.map_reverse, List.mem_reverse, List.map_map]
  exact List.mem_map_of_mem hf

/-- **EVERY NAME THE MUTUAL BLOCK DECLARES IS FRESH AT THE PRE-BLOCK
ENVIRONMENT** — members, constructors and recursors alike (task #315,
lane M7-3 session 20).

Each third of `blockNames` has its own freshness witness already, at
its own stage's environment, and the point of this theorem is to put
them on ONE list at ONE environment: the members' names are fresh at
`env` by `mutualFormers`' duplicate guard (`mutualMemberNames`); a
constructor's name is fresh at the FORMERS' environment
(`checkMutualCtors_fresh`) and a recursor's at the CONSTRUCTORS'
(`recNames_of`), so both travel back to `env` across the conses
(`find?_none_of_append`).

It is stated off the run's own conjuncts, with no `env₁` on the caller's
side, because the consumers are container-frame lemmas that ask for
exactly this shape — `containerInfo?_ext_ind_eq`'s `hfresh` at the
mutual route's name list — and should not have to redo the inversion. -/
theorem mutualBlockNames_fresh {F : Nat} {env env₁ : Env} {p : MutualParts}
    {fms : List MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {formers4 : List MutualFormer}
    {ctors4 : List MutualCtor4} {cvRas : List ConstantVal} {g isProp : Bool}
    (hpinOk : ConLeche.mutualRecPinOk p = true)
    (h1 : (p.toBlock.formers.all (fun f => f.1.levelParams == p.toBlock.lps) &&
      p.toBlock.ctors.all (fun c => c.cv.levelParams == p.toBlock.lps)) = true)
    (hformers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) p.toBlock.nP
      p.toBlock.formers env g = .ok (env₁, fms))
    (hctors : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F) env₁ p.toBlock
      fms isProp false p.toBlock.ctors = .ok (ctorsA, sortss))
    (hrectys : ConLeche.checkMutualRecTys (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consMutualCtors p.toBlock.nP ctorsA env₁) p.toBlock formers4 ctors4
      (some (p.members.map fun mb => (mb.cvR, mb.rules))) p.toBlock.k = .ok cvRas) :
    ∀ n ∈ p.toBlock.blockNames, env.find? n = none := by
  obtain ⟨-, rfl⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨hlenA, hnamesA⟩ := ctorsA_names_of hctors h1
  have hmemFresh : ∀ T ∈ fms.map (·.cvTa.name), env.find? T = none := by
    intro T hT'
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hT'
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hf
    exact (mutualMemberNames hformers t f ht).1
  intro n hn
  unfold ConLeche.MutualBlock.blockNames at hn
  rcases List.mem_append.mp hn with hn' | hn'
  · rcases List.mem_append.mp hn' with hn'' | hn''
    · exact hmemFresh n (by rw [mutualMemberNames_eq hformers]; exact hn'')
    · obtain ⟨ct, hct, rfl⟩ := List.mem_map.mp hn''
      obtain ⟨J, hJ⟩ := List.getElem?_of_mem hct
      have hJl : J < ctorsA.length := by
        rw [hlenA]; exact (List.getElem?_eq_some_iff.mp hJ).1
      have hcA : ctorsA[J]? = some ctorsA[J] := List.getElem?_eq_getElem hJl
      obtain ⟨hnm, -, -⟩ := hnamesA J _ ct hcA hJ
      rw [← hnm]
      exact ConLeche.Semantics.find?_none_of_append consMutualFormers_consts
        (checkMutualCtors_fresh hctors _ (List.mem_of_getElem? hcA))
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hn'
    exact ConLeche.Semantics.find?_none_of_append consMutualFormers_consts
      (ConLeche.Semantics.find?_none_of_append consMutualCtors_consts
        (recNames_of hpinOk hrectys t (List.mem_range.mp ht)).1)

/-- **The model WITH ITS BLOCKS survives a mutual block** (task #315
M7-3 session 6, DESIGN §U.46 (c)): `declMutual`'s conclusion
strengthened to `EnvModelB` — the block the route installed is read
back as its own container group (`mutualContainerModeled` at the run's
K.34 conjunct, crossed past the projection tables under the guard) and
carries its group's obligation at no pins (`BlockAt.of_noPins`), while
every OLD container's block crosses the whole install
(`EnvBlocksOf.crossIndP` at `mutualInstallExt`).

**No hypothesis beyond the run** (task #315 M7-3 session 9, DESIGN
§U.66 (a)): `MutualOrdFree` is `mutualOrdFree_of_run`, off the run's own
`mutualFieldsOk` conjunct and the members' freshness, so the mutual
route now matches `declNativeB`.  `declMutual`'s statement is untouched. -/
theorem declMutualB (hμ : μ.verifiedChecks = true) {F : Nat} {env envOut : Env}
    {p : MutualParts} (mb : EnvModelB V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hpinOk : ConLeche.mutualRecPinOk p = true)
    (h : ConLeche.Semantics.DeclMutualRun μ F env p envOut) :
    Nonempty (EnvModelB V μ envOut) := by
  classical
  obtain ⟨-, b, streamRecs, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4,
    cvRas, rulesOf, rfl, rfl, h0, h1, h2, h3, hformers, hf₀, htq₀, hcross, hL, hctors, hkinds,
    hfo, hgd, hrectys, hrules, htbl, hrb, hom⟩ := h
  -- K.34's read-back and K.43's own-pin table are CERTIFICATION-ONLY
  -- records (K.35's follow-up), so the run carries `certOnly μ …`; this
  -- theorem is stated under `hμ : μ.verifiedChecks = true`, at which
  -- the gate is the Bool.  `hom` is K.43's `blockOwnMimicsOk` — this
  -- route's own-pin table, which `mutualOwnPins_of` empties below
  replace hrb := ConLeche.certOnly_elim hrb hμ
  replace hom := ConLeche.certOnly_elim hom hμ
  have hOrd' := mutualOrdFree_of_run hformers hfo
  obtain ⟨mp₃, hoff, d, hd, hks, hrepsAt, hT, hstored, htf⟩ :=
    mutualCoreModeled hμ mb.toEnvModelM hE _ _ _ _ _ _ _ _ _ _ _ _ _ _
      h0 h1 h2 h3 hformers hf₀ htq₀ hcross hL hctors hkinds hfo hgd hrectys hrules
      (recNames_of hpinOk hrectys)
  obtain ⟨hchecks, rfl⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨mpOut, hagT⟩ := mutualTablesModeled hμ mb.base2.wf mb.base2.proj_ok
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 hformers hf₀ htq₀ hcross hL hctors hkinds hfo hgd
    hrectys hrules (recNames_of hpinOk hrectys) mp₃ d hd hrepsAt.toIsBlockModels hT hstored htf
    htbl
  -- the block's data
  obtain ⟨hlenA, -⟩ := ctorsA_names_of hctors h1
  have hlenF : fms.length = p.toBlock.k := (mutualFormerChecksG_pos hchecks).1
  -- the block's own-pin table is empty (K.43, DESIGN §U.74 (c)): the
  -- clause `ContainerModeled.ownPins`
  have hown : ContainerOwnPinsSyn (V := V) envOut d :=
    mutualOwnPins_of hlenF hd hf₀ hrb hom
  have hmemFresh : ∀ T ∈ fms.map (·.cvTa.name), env.find? T = none := by
    intro T hT'
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hT'
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hf
    exact (mutualMemberNames hformers t f ht).1
  have hrecFresh := checkMutualRecTys_fresh hpinOk hrectys
  -- the whole install, as the crossing sees it
  obtain ⟨new, newR, ER, E, hMs⟩ := mutualInstallExt hformers hctors hrecFresh hrectys htbl
  -- the tables' stage, as the block model's crossing sees it
  have tcR : TableCross (fms.map (·.cvTa.name))
      (ConLeche.storeMutualRecs
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
        p.toBlock fms rulesOf cvRas.zipIdx
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env)))
      envOut :=
    mutualTables_cross fms.zipIdx htbl (fun q hq =>
      List.mem_map_of_mem (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hq)))
  have hnpR := mutualNoProj mb.base2.wf mb.base2.proj_ok hformers hctors hgd hrectys hrules
  have hnpT : ∀ T ∈ fms.map (·.cvTa.name), ∀ j : Nat,
      NoProjEnv (ConLeche.storeMutualRecs
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
        p.toBlock fms rulesOf cvRas.zipIdx
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))) T j := by
    intro T hT' j
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hT'
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hf
    exact hnpR t f ht j
  have hdeR : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr),
      ProjFree (fms.map (·.cvTa.name)) e → ∀ {ea : AnnotTerm},
      denoteMeta mp₃.base2.acval (ConLeche.storeMutualRecs
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))
        p.toBlock fms rulesOf cvRas.zipIdx
        (ConLeche.consMutualCtors p.toBlock.nP ctorsA (ConLeche.consMutualFormers fms env))) ψ dp e = some ea →
      denoteMeta mpOut.base2.acval envOut ψ dp e = some ea := by
    intro ψ dp e hpf ea hr
    rw [denoteMeta_acval_congr (fun n hn => (hagT n hn).symm) dp e] at hr
    exact denoteMeta_env_mono_projFree tcR.find tcR.lit tcR.proj dp e hpf hr
  -- the block model at the OUTPUT model
  have hrepsOut : IsBlockModelsAt mpOut.base2 d (fun mm => (fms.getD mm default).cvTa) := by
    intro c hc
    obtain ⟨cvR, mI, rP, rules, hI⟩ := hrepsAt c hc
    have hclt : c < fms.length := by rw [hlenF, ← hd.k]; exact hc
    have hft : fms[c]? = some fms[c] := List.getElem?_eq_getElem hclt
    have hgd' : fms.getD c default = fms[c] := by rw [List.getD_eq_getElem?_getD, hft]; rfl
    refine ⟨cvR, mI, rP, rules, hI.crossEnvG (fun n ci _ hf => tcR.find hf)
      (constsResolve_of_findPreserved tcR.find) hagT hdeR ?_ ?_⟩
    · show ProjFree (fms.map (·.cvTa.name)) (fms.getD c default).cvTa.type
      rw [hgd']
      exact ProjFree.of_noProjEnv hnpT
        (ConLeche.Semantics.Env.find?_mem (hstored c fms[c] hft).find)
    · intro mm' j cA hmm' hj
      exact ProjFree.of_noProjEnv hnpT
        (ConLeche.Semantics.Env.find?_mem (hI.ctors mm' j cA hmm' hj).1)
  have hcm : ContainerModeled mpOut.base2
      (ConLeche.blockContainerInfo p.toBlock.nP (fms.zipIdx.map fun (f, mIdx) =>
        (f.cvTa, (p.toBlock.ownCtors mIdx).filterMap fun (J, _) => ctorsA[J]?))) d :=
    mutualContainerModeled h3 hlenA hlenF hd hks hOrd' hrepsOut
      (fun ψ => ⟨(hT ψ).1.crossEnv hagT hrepsAt.toIsBlockModels,
        (hT ψ).2.crossEnv hagT hrepsAt.toIsBlockModels⟩) htf hown
      (fun i j cA hi hj => by
        obtain ⟨cvR, mI, rP, rules, hI⟩ := hrepsAt i hi
        exact ProjFree.of_noProjEnv hnpT
          (ConLeche.Semantics.Env.find?_mem (hI.ctors i j cA hi hj).1))
  -- the carriers agree at every stored name
  have hbnFresh := mutualBlockNames_fresh hpinOk h1 hformers hctors hrectys
  have hagEnv : ∀ n : Name, (env.find? n).isSome = true →
      mpOut.base2.acval n = mb.base2.acval n := by
    intro n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    have hnb : n ∉ p.toBlock.blockNames := by
      intro hmem
      rw [hbnFresh n hmem] at hc
      exact nomatch hc
    rw [hagT n (by rw [ER.ext n c hc]; rfl)]
    funext ψ
    exact hoff n hnb ψ
  -- the old containers cross, the new block is its own group
  obtain ⟨B, hB⟩ := mb.blocks
  refine ⟨⟨mpOut, ⟨fun ci => if ci = ConLeche.blockContainerInfo p.toBlock.nP
      (fms.zipIdx.map fun (f, mIdx) =>
        (f.cvTa, (p.toBlock.ownCtors mIdx).filterMap fun (J, _) => ctorsA[J]?))
      then d else B ci, ?_⟩⟩⟩
  refine hB.crossIndP (Ts := fms.map (·.cvTa.name)) E.ext E.newN E.freshN (E.recN hMs) E.mimN
    mb.base2.wf mb.base2.rec_ctors (fun n c _ hf => E.ext n c hf)
    (constsResolve_of_findPreserved (fun hf => E.ext _ _ hf)) hagEnv ?_ hmemFresh ?_ ?_
  · -- the readings cross the whole install under the guard
    intro ψ dp e hpf ea hr
    rw [denoteMeta_acval_congr (fun n hn => (hagEnv n hn).symm) dp e] at hr
    exact denoteMeta_env_mono_projFree E.tableCross.find E.tableCross.lit E.tableCross.proj
      dp e hpf hr
  · -- an OLD container's group is not the new block's
    intro J ci hJ hci
    have hne : ci ≠ ConLeche.blockContainerInfo p.toBlock.nP
        (fms.zipIdx.map fun (f, mIdx) =>
          (f.cvTa, (p.toBlock.ownCtors mIdx).filterMap fun (J, _) => ctorsA[J]?)) := by
      intro heq
      obtain ⟨M, hM⟩ : ∃ M, ci.members[0]? = some M :=
        ⟨_, List.getElem?_eq_getElem (containerInfo?_members_pos hci)⟩
      obtain ⟨cvT, caps, cvR, mI, rP, rules, H⟩ := ConLeche.containerInfo?_inv hci
      obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfind, -, -, -, -⟩ :=
        H.2.2.2.2 M (List.mem_of_getElem? hM)
      have hMT : M.name ∈ fms.map (·.cvTa.name) := by
        rw [heq] at hM
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_of_getElem? hM)
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
        obtain ⟨g, mIdx⟩ := r
        exact List.mem_map_of_mem
          (List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hr))
      rw [hmemFresh M.name hMT] at hfind
      exact nomatch hfind
    exact if_neg hne
  · -- the new block IS its own group
    intro J hJ ci hci
    obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci
    obtain ⟨f, hf', rfl⟩ := List.mem_map.mp (E.indMs hf hJ)
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hf'
    have hclt : i < fms.length := (List.getElem?_eq_some_iff.mp hi).1
    have hfD : fms.getD i default = f := by rw [List.getD_eq_getElem?_getD, hi]; rfl
    have hread := containerInfo?_of_readBack (nP := p.toBlock.nP) hrb
      (mutualReadBack_getElem? (b := p.toBlock) (ctorsA := ctorsA) hclt)
    rw [hfD] at hread
    rw [hread] at hci
    have hcieq := (Option.some.inj hci).symm
    refine BlockAt.of_noPins ?_ ?_
    · rw [if_pos hcieq, hcieq]; exact hcm
    · rw [if_pos hcieq]; exact hd.pins

/-! ### `declNativeB` — the model WITH ITS BLOCKS survives a native block -/

/-- **The model WITH ITS BLOCKS survives a direct recursive install**
(task #315 M7-3 session 8, DESIGN §U.50 (d)): `declNative`'s conclusion
strengthened to `EnvModelB` — the block the route installed is read back
as its own container group (`nativeContainerModeled` at the run's K.34
conjunct, the representation crossed past the recursor's cons and the
projection table under the guard) and carries its group's obligation at
no pins (`BlockAt.of_noPins`), while every OLD container's block crosses
the whole install (`EnvBlocksOf.crossIndP` at `nativeInstallExt`).

There is NO hypothesis beyond the run: the mutual route's `MutualOrdFree`
has a native twin (`NativeOrdFree`) that the install's own opened-form
guard already proves (`nativeOrdFree_of`).  `declNative`'s statement is
untouched. -/
theorem declNativeB (hμ : μ.verifiedChecks = true) {F : Nat} {env envOut : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : NativeParts} (mb : EnvModelB V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.nativeParts? nPd block = some p₀)
    (h : ConLeche.Semantics.DeclNativeRun μ F env p₀ envOut) :
    Nonempty (EnvModelB V μ envOut) := by
  classical
  obtain ⟨-, env₁, envC, p, cvTa, cvRa, ctorsA, sortss, rhss, bsT, ppsAll, uAV, idxF, dsF, esF,
    srcsF, ksF, fvsPF, xFvsF, xrestF, eissF, tssF, fssZ, mpC, mp₃, mpOut, hagEnvC, hagC3, hag3O,
    hf⟩ := declNative_syntax hμ mb.toEnvModelM hE hdp h
  obtain ⟨newC, newR, newT, EE, E3, E4, hMs⟩ := nativeInstallExt hf
  have EC := E3.trans E4
  have E := EE.trans EC
  -- the carriers agree, from the constructors' environment and from the base
  have hagCO : AcvalAgrees mpC.base2 mpOut.base2 := by
    intro n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    rw [hag3O n (by rw [E3.ext n c hc]; rfl), hagC3 n hn]
  have hagEnv : ∀ n : Name, (env.find? n).isSome = true →
      mpOut.base2.acval n = mb.base2.acval n := by
    intro n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    rw [hagCO n (by rw [EE.ext n c hc]; rfl), hagEnvC n hn]
  -- the block model at the OUTPUT model, crossed under the guard
  have hmemFresh : ∀ T' ∈ [p.cvT.name], env.find? T' = none := by
    intro T' hT'
    obtain rfl := List.mem_singleton.mp hT'
    exact hf.Tfresh
  have hde : ∀ (ψ : Name → Nat) (dp : Nat) (e : Expr), ProjFree [p.cvT.name] e →
      ∀ {ea : AnnotTerm}, denoteMeta mpC.base2.acval envC ψ dp e = some ea →
        denoteMeta mpOut.base2.acval envOut ψ dp e = some ea := by
    intro ψ dp e hpf ea hr
    rw [denoteMeta_acval_congr (fun n hn => (hagCO n hn).symm) dp e] at hr
    exact denoteMeta_env_mono_projFree EC.tableCross.find EC.tableCross.lit EC.tableCross.proj
      dp e hpf hr
  have hnpT : ProjFree [p.cvT.name] cvTa.type :=
    ProjFree.of_constsResolve hmemFresh hf.Tres
  have hIC := nativeIsBlockModel hf (rules := []) (fun hne => absurd rfl hne)
  have hI := hIC.crossEnvG (Ts := [p.cvT.name]) (fun n c _ hff => EC.ext n c hff)
    (constsResolve_of_findPreserved (fun hff => EC.ext _ _ hff)) hagCO hde hnpT
    (fun mm' j cA _ hj => nativeCtorProjFree mb.base2.proj_ok hf hj)
  have hreps : IsBlockModels mpC.base2 (BlockModel.ofNative (V := V) p.nP p.resSort p.isProp
      p.large env p.cvT.name p.nIdx ppsAll uAV ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF
      eissF tssF) := by
    intro c hc
    obtain rfl : c = 0 := Nat.lt_one_iff.mp hc
    exact ⟨cvTa, cvRa, p.majorIdx, p.rulePrefix, [], hIC⟩
  -- the block's own-pin table is empty (K.43, DESIGN §U.74 (c)): the
  -- clause `ContainerModeled.ownPins`
  have hown : ContainerOwnPinsSyn (V := V) envOut
      (BlockModel.ofNative (V := V) p.nP p.resSort p.isProp p.large env p.cvT.name p.nIdx
        ppsAll uAV ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF) :=
    nativeOwnPins_of hf
  have hcm := nativeContainerModeled hf hI (fun ψ =>
    ⟨(nativeTyped hf ψ).1.crossEnv hagCO hreps, (nativeTyped hf ψ).2.crossEnv hagCO hreps⟩) hown
    (fun j cA hj => nativeCtorProjFree mb.base2.proj_ok hf hj)
  -- the old containers cross, the new block is its own group
  obtain ⟨B, hB⟩ := mb.blocks
  refine ⟨⟨mpOut, ⟨fun ci => if ci = ConLeche.blockContainerInfo p.nP [(cvTa, ctorsA)]
      then BlockModel.ofNative (V := V) p.nP p.resSort p.isProp p.large env p.cvT.name p.nIdx
        ppsAll uAV ctorsA idxF dsF esF srcsF ksF fvsPF xFvsF xrestF eissF tssF
      else B ci, ?_⟩⟩⟩
  refine hB.crossIndP (Ts := [p.cvT.name]) E.ext E.newN E.freshN
    (E.recN (fun n hn => by
      obtain rfl := List.mem_singleton.mp hn
      rw [List.map_append, List.mem_append]
      exact Or.inr hMs))
    E.mimN
    mb.base2.wf mb.base2.rec_ctors (fun n c _ hff => E.ext n c hff)
    (constsResolve_of_findPreserved (fun hff => E.ext _ _ hff)) hagEnv ?_ hmemFresh ?_ ?_
  · -- the readings cross the whole install under the guard
    intro ψ dp e hpf ea hr
    rw [denoteMeta_acval_congr (fun n hn => (hagEnv n hn).symm) dp e] at hr
    exact denoteMeta_env_mono_projFree E.tableCross.find E.tableCross.lit E.tableCross.proj
      dp e hpf hr
  · -- an OLD container's group is not the new block's
    intro J ci hJ hci
    have hne : ci ≠ ConLeche.blockContainerInfo p.nP [(cvTa, ctorsA)] := by
      intro heq
      obtain ⟨M, hM⟩ : ∃ M, ci.members[0]? = some M :=
        ⟨_, List.getElem?_eq_getElem (containerInfo?_members_pos hci)⟩
      obtain ⟨cvT, caps, cvR, mI, rP, rules, H⟩ := ConLeche.containerInfo?_inv hci
      obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfind, -, -, -, -⟩ :=
        H.2.2.2.2 M (List.mem_of_getElem? hM)
      rw [heq] at hM
      obtain rfl : M = ⟨cvTa.name, cvTa.levelParams, cvTa.type,
          ctorsA.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ := (Option.some.inj hM).symm
      rw [show (⟨cvTa.name, cvTa.levelParams, cvTa.type,
        ctorsA.map fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ :
          ConLeche.ContainerMember).name = p.cvT.name from hf.Tname, hf.Tfresh] at hfind
      exact nomatch hfind
    exact if_neg hne
  · -- the new block IS its own group
    intro J hJ ci hci
    obtain ⟨cv, caps, hff⟩ := containerInfo?_found hci
    obtain rfl := List.mem_singleton.mp (E.indMs hff hJ)
    have hread := containerInfo?_of_readBack (nP := p.nP) hf.readBack (i := 0)
      (c := (cvTa, ctorsA)) rfl
    rw [← hf.Tname, hread] at hci
    obtain rfl : ci = ConLeche.blockContainerInfo p.nP [(cvTa, ctorsA)] := (Option.some.inj hci).symm
    refine BlockAt.of_noPins ?_ ?_
    · rw [if_pos rfl]; exact hcm
    · rw [if_pos rfl]; rfl

end ConLeche.Model
