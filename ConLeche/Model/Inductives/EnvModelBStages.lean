module

public import ConLeche.Model.Inductives.ContainerCross
public import ConLeche.Model.Inductives.MutualTables
import ConLeche.Semantics.DeclRun
import ConLeche.Model.Fold
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
  ContainerInfo IndCaps fueledOps)

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
the OPENED domain** (task #315 K.36's Prop, DESIGN §U.46 (b)).

`ContainerModeled.ordFree` is stated at the block model's opened field
data, while `mutualCtorKinds` decides ordinariness on the RAW
`stripPis` domain with its loose bvars, and the two are NOT the same
statement: `openPisAtFvars` annotates each binder's fvar with its own
domain and `mentionsConst` descends into an fvar's type annotation, so
an opened ordinary domain referring to an earlier field carries that
field's type (DESIGN §U.43 (d)).  This is the OPENED form, the one the
lift consumes; the kernel lane is landing the Bool that decides it, at
which point the integration swaps this hypothesis for the run's
conjunct.  It cannot fire: a recursive or reflexive field used later is
`.unsupported` (`structUsedLater`), which `classifyMutualKinds` throws
on, so the fvars an opened ordinary domain can refer to are themselves
ordinary and their domains mention no member. -/
@[expose] def MutualOrdFree (b : MutualBlock) (fms : List MutualFormerA)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List (RecFieldKind × Nat))) : Prop :=
  ∀ (J : Nat) (cA : ConstantVal × Nat), ctorsA[J]? = some cA →
    ∀ (fvsP xFvs : List Expr) (crest xrest : Expr),
      ConLeche.openPisAtFvars b.nP cA.1.type 0 = some (fvsP, crest) →
      ConLeche.openPisAtFvars cA.2 crest b.nP = some (xFvs, xrest) →
      ∀ (l : Nat) (x : Expr), xFvs[l]? = some x →
        ((kinds.getD J []).getD l (.ordinary, 0)).1 = .ordinary →
        ConLeche.mentionsMember (fms.map (·.cvTa.name)) x.fvarTypeD = false

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

/-- **The block the mutual route installs IS its own container group**
(task #315 M7-3 session 6): `ContainerModeled.of_readBack` at the run's
K.34 conjunct, with every remaining clause the route's own —
`hk`/`hnP`/`hnames`/`hctorNames`/`namesLen` from `MutualBlockModelOf`
and the list plumbing, `reps`/`member` from the AT-form the core hands
back (DESIGN §U.46 (a)), `inj` and `frame` from `MutualTableFacts`, the
two pin clauses VACUOUS (a mutual block has no pins), and `ordFree`
from `MutualOrdFree` by a rewrite through `BlockCtorData.opens` and the
block model's field kinds. -/
theorem mutualContainerModeled {env envR : Env} {m : EnvModel V envR}
    {b : MutualBlock} {fms : List MutualFormerA} {ctorsA : List (ConstantVal × Nat)}
    {sortss : List (List Level)} {kinds : List (List (RecFieldKind × Nat))} {d : BlockModel V}
    (h3 : ConLeche.mutualCtorsGrouped b.ctors = true)
    (hlenA : ctorsA.length = b.ctors.length) (hlenF : fms.length = b.k)
    (hd : MutualBlockModelOf env b fms ctorsA d)
    (hks : ∀ mm j, d.ksF mm j = (kinds.getD (b.ownOffset mm + j) []).map (·.1))
    (hOrd : MutualOrdFree b fms ctorsA kinds)
    (hrepsAt : IsBlockModelsAt m d (fun mm => (fms.getD mm default).cvTa))
    (htyped : ∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ)
    (htf : MutualTableFacts b fms sortss d) :
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
  refine ContainerModeled.of_readBack (by rw [hkF]; simp) hd.nP
    (by rw [hd.memberNames, List.length_map, hkF]) (fun i hi => ?_) (fun i hi => ?_)
    hrepsAt.toIsBlockModels
    (fun ψ => ⟨(htyped ψ).1, (htyped ψ).2, PinsTyped.of_noPins hd.pins ψ⟩)
    htf.inj (fun i hi ψ ρ => (htf.frame i hi ψ ρ).symm) (fun i j l x hi hj hx hk => ?_)
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    (fun q hq => absurd hq (by rw [hnoPins]; omega)) (fun i hi => ?_)
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

end ConLeche.Model
