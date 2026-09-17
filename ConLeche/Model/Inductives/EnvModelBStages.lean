module

public import ConLeche.Model.Inductives.ContainerCross
public import ConLeche.Model.Inductives.MutualTables
import ConLeche.Model.Inductives.MutualNoProj
import ConLeche.Model.Inductives.MutualRecsStage
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
  refine ContainerModeled.of_readBack ?_ hd.nP
    (by rw [hd.memberNames, List.length_map, hkF]) (fun i hi => ?_) (fun i hi => ?_)
    hrepsAt.toIsBlockModels
    (fun ψ => ⟨(htyped ψ).1, (htyped ψ).2, PinsTyped.of_noPins hd.pins ψ⟩)
    htf.inj (fun i hi ψ ρ => (htf.frame i hi ψ ρ).symm) (fun i j l x hi hj hx hk => ?_)
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    (fun q hq => absurd hq (by rw [hnoPins]; omega))
    (fun q hq => absurd hq (by rw [hnoPins]; omega)) (fun i hi => ?_)
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

namespace BlockInstallExt

variable {Ms : List Name} {env envOut : Env} {new : List ConstantInfo}

omit [SetTheory V] in
/-- A stored lookup survives: a new constant of that name would have to
be fresh at the environment that answers it. -/
theorem ext (h : BlockInstallExt Ms env envOut new) :
    ∀ (n : Name) (c : ConstantInfo), env.find? n = some c → envOut.find? n = some c := by
  intro n c hf
  cases hn : List.find? (fun c => c.name == n) new with
  | none => rw [ConLeche.Semantics.find?_append_of_new_none h.1 hn]; exact hf
  | some c' =>
    obtain ⟨hmem, rfl⟩ := find?_name_mem hn
    rw [h.2.1 c' hmem] at hf
    exact nomatch hf

omit [SetTheory V] in
/-- A lookup the extension answers is the base's or one of the new
constants'. -/
theorem newOf (h : BlockInstallExt Ms env envOut new) {n : Name} {c : ConstantInfo}
    (hf : envOut.find? n = some c) (hn : env.find? n = none) : c ∈ new ∧ c.name = n := by
  cases hfn : List.find? (fun c => c.name == n) new with
  | none =>
    rw [ConLeche.Semantics.find?_append_of_new_none h.1 hfn, hn] at hf
    exact nomatch hf
  | some c' =>
    have : envOut.find? n = some c' := by
      rw [ConLeche.Env.find?, h.1, List.find?_append, hfn]; rfl
    rw [hf] at this
    obtain rfl : c = c' := Option.some.inj this
    exact find?_name_mem hfn

omit [SetTheory V] in
/-- The new names are fresh at the base. -/
theorem freshN (h : BlockInstallExt Ms env envOut new) :
    ∀ n ∈ new.map (·.name), env.find? n = none := by
  intro n hn
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
  exact h.2.1 c hc

omit [SetTheory V] in
/-- A lookup the extension answers is the base's or at a new name. -/
theorem newN (h : BlockInstallExt Ms env envOut new) :
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
    ∃ new : List ConstantInfo,
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
  refine ⟨_, ((((consMutualFormers_installExt hmemFresh).trans
    (consMutualCtors_installExt (nP := b.nP) (checkMutualCtors_fresh hctors))).trans
    (storeMutualRecs_installExt hrecFresh hrecMs)).trans E4), ?_⟩
  intro n hn
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
  rw [List.map_append, List.mem_append]; right
  rw [List.map_append, List.mem_append]; right
  rw [List.map_append, List.mem_append]; right
  rw [List.map_reverse, List.mem_reverse, List.map_map]
  exact List.mem_map_of_mem hf

end ConLeche.Model
