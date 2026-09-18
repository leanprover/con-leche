module

public import ConLeche.Model.Inductives.NestedCore
import ConLeche.Model.Inductives.NestedPinLeafAll
public import ConLeche.Model.Inductives.EnvModelBStages
import ConLeche.Verify.Inductives.NestedAuxFormers
import ConLeche.Verify.Inductives.NestedGroupInv
import ConLeche.Verify.Inductives.NestedRestoreKit
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedElimInv
public section

/-!
# `declNested_of` — the nested assembly's run-level consumer (task #315, M6 s3 / M7-2)

**THE run-level consumer of the nested half**: the model of the
pre-block environment survives the nested install's run
(`DeclNestedRun`, `Semantics/Inductives/DeclNested.lean`), given two
named facts that M6/M7 discharge — `declBlock`'s pattern (DESIGN §U.6)
at the nested block:

* `NestedCoreModeled` (M6): the run's stages through the restored
  constructors keep the model and leave THE BLOCK MODEL of the nested
  block at the constructors' environment — the composed block model
  `nestedBlockModel` (`NestedCore.lean`) CONCRETELY, together with the
  scratch install's formers' facts and the constructors' loop's outputs
  the recursors' stage reads (`NestedCoreOut`, task #315 M7-2, DESIGN
  §U.29: the block model "grows at its consumer" — the recursors' kit
  is stated at `nestedBlockModel` and its pins' constructors, so the
  tail sees the parameters, not an existential `d`);
* `NestedTailModeled` (M7): from there the restored recursors (at
  `k + nPins` motives), their rules, the projection tables and the
  two post-checks keep the model to the post-block environment.

The containers' block models are the pre-block CARRIER'S OWN
(`EnvModelB`, task #315 M7-3: `EnvModelM` with the field
`EnvBlockModels` — every stored inductive is a member of a block whose
block model holds at the model, with its injections the tagged towers
at the constructors' MEMBER-LOCAL positions; DESIGN §U.13 (f) 1's
field); at the pins it is read as `PinsModeled`.  Those definitions and
the run's record live in `NestedPremise.lean`, below `NestedCore.lean`;
the crossing kit that carries a container's block model over an
environment extension is `ContainerCross.lean`.  `nestedCoreModeled_of`
(the core's discharge modulo the restored constructors' loop) lives
here with its statement.
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

/-! ## The core's output: the block model, concretely -/

/-- **The nested core's output** — what the recursors' stage (M7) reads
of the constructors' stage, at the run's data: the scratch install's
formers' run and facts (`MutualFormersFacts` at the `auxRoute` grade),
the scratch constructors' run, the block's shape, the restored
constructors' stage's outputs at the model `mp₂` of the restored
environment (`NestedStageFacts`: the members' leaves, the restored
constructors' leaves and readings, the pin groups, the agreement off
the block), and the CONCRETE block model `nestedBlockModel` at every
member — AT THE MEMBERS' OWN AUXILIARY CONSTANTS (`IsBlockModelsAt`,
task #315 M7-3 session 11: the form the read-back's record demands, so
that the install's tail crosses it instead of rebuilding it) — with the
members, constructors and pins typed and its record. -/
structure NestedCoreOut {env : Env} (F : Nat) (mp : EnvModelM V μ env) (p : NestedParts)
    (st : ElimState) (b : MutualBlock) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR : Nat → Nat → List Expr)
    (pinsS : List PinSyn)
    (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
      (ConLeche.consMutualFormers (fms.take p.k) env))) : Prop where
  formers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env true
    = .ok (ConLeche.consMutualFormers fms env, fms)
  facts : MutualFormersFacts V F true mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
    fvsPF xFvsF xrestF eissF tssF
  ctors : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
    (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) true b.ctors
    = .ok (ctorsA, sortss)
  kindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
    = .ok kinds
  bk : b.k = p.k + pinsS.length
  grouped : ConLeche.mutualCtorsGrouped b.ctors = true
  nodup : b.blockNames.Nodup
  stage : NestedStageFacts (V := V) (mp := mp) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
    (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF) (esF := esF)
    (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF)
    (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) st mp₂
  reps : IsBlockModelsAt mp₂.base2 (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF
    dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)
    (fun mm => (fms.getD mm default).cvTa)
  typed : ∀ ψ : Name → Nat,
    FormersTyped mp₂.base2 (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF
      dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS) ψ ∧
    CtorsTyped mp₂.base2 (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF
      dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS) ψ ∧
    PinsTyped mp₂.base2 (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF
      dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS) ψ
  record : NestedBlockModelOf env p st ctorsR (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env
    ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

/-! ## The tail's output: the model, the install and the block's reading

(task #315 M7-3 session 10, DESIGN §U.67.) -/

section TailOut

variable {p : NestedParts} {b : MutualBlock} {fms : List MutualFormerA} {f₀ : MutualFormerA}
  {ctorsA : List (ConstantVal × Nat)} {kinds : List (List (RecFieldKind × Nat))}
  {ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {W : (Name → Nat) → Nat}
  {idxF : Nat → List Expr} {dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)}
  {esF : Nat → (Name → Nat) → List AnnotTerm} {srcsF : Nat → List (Option Nat)}
  {fvsPF : Nat → List Expr} {xrestF : Nat → Expr}
  {eissF : Nat → (Name → Nat) → List (List AnnotTerm)}
  {tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm))}
  {ctorsR : List (List (ConstantVal × Nat × Nat))}
  {dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)} {xFvsR : Nat → Nat → List Expr}
  {pinsS : List PinSyn} {env : Env}

local notation "D" => (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF dsF esF
  srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

local notation "PG" => NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀)
  (ctorsA := ctorsA) (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF)
  (dsF := dsF) (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
  (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)

local notation "ENV₂" => (ConLeche.consNestedCtors ctorsR.flatten
  (ConLeche.consMutualFormers (fms.take p.k) env))

/-- **The tail's output** — what `NestedTailModeled` hands back beyond
the model of the post-block environment, so that the route can carry
the environment model's BLOCK FIELD across its own install
(`declNested_of` at `EnvModelB`, task #315 M7-3 session 10).  Every
field is a fact about the OUTPUT environment or about a crossing into
it, which is what makes it the tail's and not the core's:

* `install`: the whole install's conses, at the block's members
  (`NestedInstallExt`, the relaxed record the mimic recursors force),
  with the members among the new names — the crossing's lookup half
  and its guard;
* `agree`: the carriers agree at every name the CONSTRUCTORS'
  environment stores, which is where the block model was built;
* `repsAt`: the block model at the OUTPUT model, AT THE MEMBERS' OWN
  STORED CONSTANTS (`IsBlockModelsAt`) — the form
  `ContainerModeled.member` demands, and the one the recursors' stage
  is the first to be able to state (the representation names the
  restored recursor); the core publishes the same form at the
  CONSTRUCTORS' model (`NestedCoreOut.reps`, task #315 M7-3
  session 11), so this field is that one CROSSED;
* `groups`/`conts`: the pins' groups at the constructors' model with
  their container's block model NAMED by the environment model's own
  assignment `blockOf mp.base2` (DESIGN §U.36 (d)'s strengthening) —
  stated here, at the tail, because `NestedCoreOut` cannot be
  strengthened without a new named hypothesis. -/
structure NestedTailOut (mp : EnvModelM V μ env) (stored : List AuxStored)
    (mp₂ : EnvModelM V μ ENV₂) (envOut : Env) (mpOut : EnvModelM V μ envOut) : Prop where
  install : ∃ new : List ConstantInfo, NestedInstallExt p.memberNames env envOut new ∧
    ∀ n ∈ p.memberNames, n ∈ new.map (·.name)
  agree₀ : AcvalAgrees mp.base2 mpOut.base2
  agree : AcvalAgrees mp₂.base2 mpOut.base2
  findR : ∀ (n : Name) (c : ConstantInfo),
    (∀ (cv : ConstantVal) (mI rP : Nat) (rules : List RecRule), c ≠ .recInfo cv mI rP rules) →
    (ENV₂).find? n = some c → envOut.find? n = some c
  repsAt : IsBlockModelsAt mpOut.base2 (D) (fun mm => (stored.getD mm default).cvTa)
  groups : ∀ q, q < pinsS.length → ∀ ci : ContainerInfo,
    ConLeche.containerInfo? (ENV₂) ((D).pinAt q).J = some ci →
    ∃ q₀ kJ i, q = q₀ + i ∧ i < kJ ∧ PG mp₂.base2 q₀ kJ (blockOf mp.base2 ci)
  conts : ∀ q, q < pinsS.length → ∃ ci : ContainerInfo,
    ConLeche.containerInfo? (ENV₂) ((D).pinAt q).J = some ci ∧
    ConLeche.containerInfo? envOut ((D).pinAt q).J = some ci ∧
    ConLeche.containerInfo? env ((D).pinAt q).J = some ci


/-- The read-back's member list of a nested install, read at a member:
the auxiliary record's `ConstantVal` and the member's RESTORED
constructors. -/
theorem nestedReadBack_getElem? {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {k i : Nat}
    (hi : i < k) (hs : k ≤ stored.length) (hc : ctorsR.length = k) :
    (((stored.take k).zip ctorsR).map fun (a, cs) =>
        (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))[i]?
      = some ((stored.getD i default).cvTa, (ctorsR.getD i []).map fun c => (c.1, c.2.2)) := by
  have hsi : (stored.take k)[i]? = some (stored.getD i default) := by
    rw [List.getElem?_take_of_lt hi, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  have hci : ctorsR[i]? = some (ctorsR.getD i []) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hz : ((stored.take k).zip ctorsR)[i]? = some (stored.getD i default, ctorsR.getD i []) := by
    show (List.zipWith Prod.mk (stored.take k) ctorsR)[i]? = _
    rw [List.getElem?_zipWith, hsi, hci]
  rw [List.getElem?_map, hz]
  rfl

/-- `nestedReadBack_getElem?` in the defaulting form the read-back's
data clauses read. -/
theorem nestedReadBack_getD {stored : List AuxStored}
    {ctorsR : List (List (ConstantVal × Nat × Nat))} {k i : Nat}
    (hi : i < k) (hs : k ≤ stored.length) (hc : ctorsR.length = k) :
    (((stored.take k).zip ctorsR).map fun (a, cs) =>
        (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF))).getD i default
      = ((stored.getD i default).cvTa, (ctorsR.getD i []).map fun c => (c.1, c.2.2)) := by
  rw [List.getD_eq_getElem?_getD, nestedReadBack_getElem? hi hs hc]
  rfl

omit [SetTheory V] in
/-- **A member of the auxiliary read-back is fresh at the PRE-BLOCK
environment**: the run's own capability record over the read-back
(`hcaps`), read positionally. -/
theorem nestedStoredFresh {stored : List AuxStored} {k : Nat} {env : Env}
    (hcaps : ((stored.take k).all fun a =>
      !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (hs : k ≤ stored.length) {i : Nat} (hi : i < k) :
    env.find? (stored.getD i default).cvTa.name = none := by
  have hsi : stored[i]? = some stored[i] := List.getElem?_eq_getElem (by omega)
  have hmem : stored[i] ∈ stored.take k :=
    List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi]; exact hsi)
  have hall := List.all_eq_true.mp hcaps _ hmem
  rw [Bool.and_eq_true] at hall
  rw [List.getD_eq_getElem?_getD, hsi]
  exact Option.isNone_iff_eq_none.mp hall.2

/-- **A member of the block IS a member of the auxiliary read-back**:
the formers' stage and the read-back cons the same constants, prefix by
prefix (`consNestedFormers_take_eq`), so a name of the block model's
member list is the `i`-th stored record's. -/
theorem nestedMemberStored {F : Nat} {st : ElimState} {envAux : Env}
    {stored : List AuxStored} {sortss : List (List Level)} {xFvsF : Nat → List Expr}
    {mp : EnvModelM V μ env} {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
    {mp₂ : EnvModelM V μ ENV₂}
    (haux : ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true
      = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (O : NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂) :
    ∀ n ∈ (D).memberNames, ∃ i, i < p.k ∧ (stored.getD i default).cvTa.name = n := by
  have hslen : stored.length = b.k := (ConLeche.auxStoredAll_get hstored).1
  have hkle : p.k ≤ b.k := by rw [O.bk]; omega
  have hcv := (ConLeche.consNestedFormers_take_eq haux O.formers hstored p.k hkle).2
  intro n hn
  have hn' : n ∈ (fms.take p.k).map (·.cvTa.name) := hn
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn'
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hf
  have hilt : i < p.k := by
    have hl := (List.getElem?_eq_some_iff.mp hi).1
    rw [List.length_take] at hl
    omega
  have hfi : fms[i]? = some f := by
    rw [← List.getElem?_take_of_lt hilt]; exact hi
  have hsi : stored[i]? = some stored[i] := List.getElem?_eq_getElem (by omega)
  obtain ⟨f', hf', hcveq, -, -⟩ := hcv i _ hilt hsi
  obtain rfl : f' = f := Option.some.inj (hf'.symm.trans hfi)
  refine ⟨i, hilt, ?_⟩
  rw [List.getD_eq_getElem?_getD, hsi]
  exact congrArg (fun c : ConstantVal => c.name) hcveq

/-- **Every member of a nested block is fresh at the PRE-BLOCK
environment** — what `ordFree`, `pinsNotMembers` and the crossing's
guard all read. -/
theorem nestedMembersFresh {F : Nat} {st : ElimState} {envAux : Env}
    {stored : List AuxStored} {sortss : List (List Level)} {xFvsF : Nat → List Expr}
    {mp : EnvModelM V μ env} {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
    {mp₂ : EnvModelM V μ ENV₂}
    (hcaps : ((stored.take p.k).all fun a =>
      !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (haux : ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true
      = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (O : NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂) :
    ∀ n ∈ (D).memberNames, env.find? n = none := by
  have hslen : stored.length = b.k := (ConLeche.auxStoredAll_get hstored).1
  have hkle : p.k ≤ b.k := by rw [O.bk]; omega
  intro n hn
  obtain ⟨i, hi, rfl⟩ := nestedMemberStored haux hstored O n hn
  exact nestedStoredFresh hcaps (by omega) hi

/-- **The block the NESTED route installs IS its own container group**
(task #315 M7-3 session 10, DESIGN §U.67 (b)):
`ContainerModeled.of_readBack` at the run's K.34 conjunct, the mutual
and native routes' pattern at a block WITH PINS.

Eleven of the fourteen clauses are the route's own, at the data the
core hands back (task #315 M7-3 session 11 moved the last two of them
there — see below): `hk`/`hnP`/`hnamesLen`/`hnames`/`hctorNames` from
`NestedBlockModelOf` and the read-back list's plumbing (the members'
`ConstantVal`s are the auxiliary records', `consNestedFormers_take_eq`),
`inj` definitional at `BlockModel.ofNested` (`ofNested_inj`), `frame`
the scratch block's cross-member identification
(`MutualFormersFacts.frame`), `ordFree` the constructors' own opened
guard at the PRE-BLOCK environment (`BlockOpened.ord` at `d.env₀`,
where every member is fresh — the native route's argument, DESIGN
§U.52 (a), NOT `MutualOrdFree`), and `pinsNotMembers` the containers'
check (`nestedContainersOk_group`) against that same freshness.

The three that remain name the OUTPUT model, and come from the tail
(`NestedTailOut`): the representation at the members' stored constants
(`repsAt`, which also carries `member`) and the typing crossed off it.

`pinNP` and `pinψ` are the core's (task #315 M7-3 session 11, DESIGN
§U.67 (c) 5): the two pin records now travel on `NestedStageFacts`, so
the tail is not asked for them.  Both read an environment the install
has left alone — `pinNP` the pin's container at `d.env₀ = env` and
`pinψ` its record at the members' prefix environment, which is `env`'s
at a name no member takes (`consMutualFormers_find?_of_ne` against the
members' freshness) and `envOut`'s by the install's conses
(`ConsExt.ext`). -/
theorem nestedContainerModeled {F : Nat} {st : ElimState} {envAux : Env}
    {stored : List AuxStored} {sortss : List (List Level)} {xFvsF : Nat → List Expr}
    {mp : EnvModelM V μ env} {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
    {mp₂ : EnvModelM V μ ENV₂} {envOut : Env} {mpOut : EnvModelM V μ envOut}
    (hcaps : ((stored.take p.k).all fun a =>
      !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (hcont : ConLeche.nestedContainersOk env st.pins = true) (hk0 : 0 < p.k)
    (hmn : ConLeche.nestedPinMentionOk p st = true)
    (haux : ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true
      = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hctors : (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors) = .ok ctorsR)
    (O : NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂)
    (T : NestedTailOut (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
      (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF) (esF := esF)
      (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF)
      (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) mp stored mp₂ envOut mpOut) :
    ContainerModeled mpOut.base2 (ConLeche.blockContainerInfo p.nP
        (((stored.take p.k).zip ctorsR).map fun (a, cs) =>
          (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))) (D) := by
  -- the lists' lengths
  have hslen : stored.length = b.k := (ConLeche.auxStoredAll_get hstored).1
  have hkle : p.k ≤ b.k := by rw [O.bk]; omega
  have hkF : fms.length = b.k := O.facts.lenFms
  have hclen : ctorsR.length = p.k := by
    rw [(ConLeche.mapM_except_inv hctors).1, List.length_take]
    omega
  have hdk : (D).k = p.k := rfl
  -- the members' constants are the auxiliary records'
  have hcv := (ConLeche.consNestedFormers_take_eq haux O.formers hstored p.k hkle).2
  have hmemEq : ∀ i, i < p.k → (stored.getD i default).cvTa = (fms.getD i default).cvTa := by
    intro i hi
    have hsi : stored[i]? = some stored[i] := List.getElem?_eq_getElem (by omega)
    obtain ⟨f, hf, hcveq, -, -⟩ := hcv i _ hi hsi
    rw [List.getD_eq_getElem?_getD, hsi, List.getD_eq_getElem?_getD, hf]
    exact hcveq
  have hnamesD : ∀ i, i < p.k → (D).memberName i = (fms.getD i default).cvTa.name := by
    intro i hi
    show ((fms.take p.k).map (·.cvTa.name)).getD i .anonymous = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take_of_lt hi,
      List.getD_eq_getElem?_getD]
    cases fms[i]? <;> rfl
  have hnamesS : ∀ i, i < p.k → (D).memberName i = (stored.getD i default).cvTa.name := by
    intro i hi
    rw [hnamesD i hi, hmemEq i hi]
  have hfreshMem : ∀ n ∈ (D).memberNames, env.find? n = none :=
    nestedMembersFresh hcaps haux hstored O
  -- the pins' containers are stored, hence no member
  have hpinStored : ∀ q, q < (D).nPins →
      ∃ ci : ContainerInfo, ConLeche.containerInfo? env ((D).pinAt q).J = some ci := by
    intro q hq
    have hql : q < st.pins.length := by rw [← O.record.nPins]; exact hq
    have hpq : st.pins[q]? = some st.pins[q] := List.getElem?_eq_getElem hql
    obtain ⟨hJ, -⟩ := O.record.pin q _ hpq
    obtain ⟨ci, hci, -⟩ := (ConLeche.nestedContainersOk_group hcont).2 _ (List.mem_of_getElem? hpq)
    exact ⟨ci, by rw [hJ]; exact hci⟩
  refine ContainerModeled.of_readBack ?_ O.record.nP ?_ ?_ ?_ T.repsAt.toIsBlockModels
    (fun ψ => ⟨(O.typed ψ).1.crossEnv T.agree O.reps.toIsBlockModels,
      (O.typed ψ).2.1.crossEnv T.agree O.reps.toIsBlockModels,
      (O.typed ψ).2.2.crossEnv T.agree O.reps.toIsBlockModels ?_⟩)
    (fun ψ mm' j fs => ofNested_inj ψ mm' j fs) ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- `hk`
    rw [hdk, List.length_map, List.length_zip, List.length_take, hclen]
    omega
  · -- `hnamesLen`
    show ((fms.take p.k).map (·.cvTa.name)).length = (D).k
    rw [List.length_map, List.length_take, hdk]
    omega
  · -- `hnames`
    intro i hi
    rw [nestedReadBack_getD (hdk ▸ hi) (by omega) hclen]
    exact hnamesS i (hdk ▸ hi)
  · -- `hctorNames`
    intro i hi
    rw [O.record.ctors i (hdk ▸ hi),
      nestedReadBack_getD (hdk ▸ hi) (by omega) hclen]
  · -- the block has a member
    rw [hdk]; exact hk0
  · -- `frame`
    intro i hi ψ ρ
    have hilt : i < fms.length := by rw [hkF]; omega
    exact (O.facts.frame i _ (List.getElem?_eq_getElem hilt) ψ ρ).symm
  · -- `ordFree`
    intro i j l x hi hj hx hk
    have hjR : j < (ctorsR.getD i []).length := by
      rw [O.record.ctors i (hdk ▸ hi), List.length_map] at hj
      exact hj
    obtain ⟨c, hc⟩ : ∃ c, (ctorsR.getD i [])[j]? = some c :=
      ⟨_, List.getElem?_eq_getElem hjR⟩
    obtain ⟨cA, -, -, -, -, hdata⟩ := O.stage.ctorFacts i j c (hdk ▸ hi) hc
    show (List.any (D).memberNames fun T => x.fvarTypeD.mentionsConst T) = false
    rw [List.any_eq_false]
    intro n hn
    simp only [Bool.not_eq_true]
    exact ConLeche.rk_mentionsConst_false_of_constsResolve
      (by have hord := hdata.2.2.opened.ord l x hx hk; rwa [O.record.env₀] at hord)
      (hfreshMem n hn)
  · -- `nestMention`: K.44's record (`nestedPinMentionOk`) at the pin's
    -- own components, which is where the clause is spelled (DESIGN
    -- §U.67 (b) B1) — the pin term is its container applied to `DsE`,
    -- and `DsE` IS the parameter part, its length the pin's `nPJ`
    -- (the components' reading at the group, `pinDs`/`pinDsLen`/`pinNP`)
    intro q hq
    have hql : q < st.pins.length := by rw [← O.record.nPins]; exact hq
    have hpq : st.pins[q]? = some st.pins[q] := List.getElem?_eq_getElem hql
    obtain ⟨-, hpin⟩ := O.record.pin q _ hpq
    have hlen : ((D).pinAt q).DsE.length = ((D).pinAt q).nPJ := by
      obtain ⟨ci, h₂, -, -⟩ := T.conts q hq
      obtain ⟨q₀, kJ, i, rfl, hi, G⟩ := T.groups q hq ci h₂
      exact ((O.stage.pinDs _ hq (fun _ => 0)).length.trans
        (G.pinDsLen i hi (fun _ => 0))).trans (G.pinNP i hi).symm
    have hnil : (Expr.const st.pins[q].container ((D).pinAt q).lvls).getAppArgs = [] := rfl
    simp only [ConLeche.nestedPinMentionOk, List.all_eq_true, List.any_eq_true] at hmn
    obtain ⟨e, he, hme⟩ := hmn _ (List.mem_of_getElem? hpq)
    rw [hpin, Expr.getAppArgs_mkAppN, hnil, List.nil_append] at he
    exact ⟨e, by rw [← hlen, List.take_length]; exact he, by rw [O.record.memberNames]; exact hme⟩
  · -- `pinsNotMembers`
    intro q hq hmem
    obtain ⟨ci, hci⟩ := hpinStored q hq
    obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci
    rw [hfreshMem _ hmem] at hf
    exact nomatch hf
  · -- `pinNP`: the core's own (`NestedStageFacts.pinNP`) at the pin's
    -- stored container, which is `d.env₀ = env`
    intro q hq
    obtain ⟨ci, hci⟩ := hpinStored q hq
    exact ⟨ci, hci, O.stage.pinNP q hq ci hci⟩
  · -- `pinψ`: the core's own (`NestedStageFacts.pinψ`) at the members'
    -- PREFIX environment — the pin's container is stored at `env`, so
    -- its record is the same one there (no member is found at `env`,
    -- `consMutualFormers_find?_of_ne`) and at `envOut` (the install's
    -- conses, `ConsExt.ext`)
    intro q hq cvT caps hf
    obtain ⟨ci, hci⟩ := hpinStored q hq
    obtain ⟨cv, caps', hfE⟩ := containerInfo?_found hci
    obtain ⟨new, E, -⟩ := T.install
    have hOut := E.toConsExt.ext _ _ hfE
    rw [hf] at hOut
    rw [(Option.some.inj hOut).symm] at hfE
    have hne : ∀ g ∈ fms.take p.k, g.cvTa.name ≠ ((D).pinAt q).J := by
      intro g hg heq
      have hmem : g.cvTa.name ∈ (D).memberNames := List.mem_map_of_mem hg
      rw [hfreshMem _ (heq ▸ hmem)] at hfE
      exact nomatch hfE
    refine O.stage.pinψ q hq cvT caps ?_
    show (ConLeche.consMutualFormers (fms.take p.k) env).find? ((D).pinAt q).J = _
    rw [ConLeche.consMutualFormers_find?_of_ne hne]
    exact hfE
  · -- `member`
    intro i hi
    obtain ⟨cvR, mI, rP, rules, hI⟩ := T.repsAt i hi
    refine ⟨cvR, mI, rP, rules, ?_⟩
    rw [nestedReadBack_getD (hdk ▸ hi) (by omega) hclen]
    rw [hnamesS i (hdk ▸ hi)] at hI
    exact hI

end TailOut

/-! ## The named facts -/

/-- **The nested run's stages through the restored constructors keep
the model and leave the block model at the constructors'
environment** — `declNested_of`'s first named fact (M6): from a model
of the pre-block environment carrying the containers' block models
(`PinsModeled`) and the run's conjuncts through `restoreCtors`, a
model of the environment holding the restored formers and
constructors, agreeing with the pre-block model off the block, at
which the nested block's CONCRETE block model `nestedBlockModel` holds
at every member (`IsBlockModels`), with the members, the constructors
and the pins' containers typed, together with the scratch install's
and the loop's data (`NestedCoreOut`).  Consumer: `declNested_of`;
discharged modulo the loop by `nestedCoreModeled_of`. -/
@[expose] def NestedCoreModeled (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env : Env} (mp : EnvModelM V μ env), ConLeche.EtaFamiliesClosed env →
  ∀ (p : NestedParts) (st : ElimState) (b : MutualBlock) (envAux : Env)
    (stored : List AuxStored) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (fmsA ctorsA : List ConstantVal),
    PinsModeled mp.base2 st.pins →
    (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true →
    uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true →
    ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA →
    ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA →
    ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st →
    st.pins.length = p.numNested →
    ConLeche.copiesFresh env p.k st = true →
    ConLeche.nestedContainersOk env st.pins = true →
    ConLeche.auxBlock p st = some b →
    ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true = .ok envAux →
    ConLeche.auxStoredAll envAux b b.k = some stored →
    ConLeche.pinsClosed p.nP st.pins = true →
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envAux p.nP st.pins = .ok () →
    (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true →
    ConLeche.nestedCopySrcOk env p st = true →
    ConLeche.nestedGroupsOk env p st = true →
    -- THE PINS' SCOPE (K.30): every pin's free variables are the first
    -- former's openers, annotation included, and no loose bvar
    ConLeche.pinsScoped p.nP st = true →
    -- **THE COPIES' TARGETS** (K.32, task #315 L-E, DESIGN §U.64): a
    -- copy's group-internal recursive field points at the copy of the
    -- container member its own field points at, which the copies'
    -- identities read on the `ordF` arm (lane L-B's `NestedPinsShape`)
    ConLeche.nestedCopyTargetsOk env p b st stored = true →
    ConLeche.nestedPinKindsOk p b st stored = true →
    ConLeche.nestedPinRankOk env p b st stored = true →
    -- **THE POSITIVITY NORMALISATION ON THE MINTED COPY** (K.42, task
    -- #315, lane L-B): at every ORDINARY field of every copy's
    -- constructor, the stored domain IS the positivity normalisation of
    -- the MINTED one, which the copies' identities read on the
    -- `ordF`-LEFT arm (lane L-B's `NestedPinsShape`)
    (∃ (jobs : List (Nat × Expr × Expr)) (ws : List Expr),
      ConLeche.nestedOrdDomPairs env p st stored (ConLeche.nestedPinKinds p b stored) = some jobs ∧
      ConLeche.nestedOrdNorms (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) b.memberNames jobs = .ok ws ∧
      ws = jobs.map (·.2.2)) →
    -- POST-CHECK (a) A THIRD TIME (K.30): the pins typed at the
    -- environment holding the RESTORED formers
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consNestedFormers (stored.take p.k) env) p.nP st.pins = .ok () →
    (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR →
    ∃ (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
      (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
      (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
      (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
      (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
      (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
      (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
      (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
      (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR : Nat → Nat → List Expr)
      (pinsS : List PinSyn)
      (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env))),
      ConLeche.consNestedFormers (stored.take p.k) env
        = ConLeche.consMutualFormers (fms.take p.k) env ∧
      NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
        fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂

/-- **The tail keeps the model**: at a model of the constructors'
environment carrying the nested block's block model, the run's
remaining stages — the restored recursor types at `k + nPins` motives,
their rules at the rule-less provision, the projection tables and the
two post-checks — cons a model of the post-block environment —
`declNested_of`'s second named fact (M7), at the core's CONCRETE output
(`NestedCoreOut`).  Consumer: `declNested_of`; its skeleton
`nestedTailModeled_of` (`NestedRecsStage.lean`). -/
@[expose] def NestedTailModeled (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env : Env} (mp : EnvModelM V μ env), ConLeche.EtaFamiliesClosed env →
  ∀ (p : NestedParts) (envOut : Env) (st : ElimState) (b : MutualBlock) (envAux : Env)
    (stored : List AuxStored) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (cvRms cvRns : List ConstantVal) (rulesM rulesN : List (List RecRule))
    (fmsA ctorsA : List ConstantVal),
    PinsModeled mp.base2 st.pins →
    (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true →
    uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true →
    ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA →
    ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA →
    ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st →
    st.pins.length = p.numNested →
    ConLeche.copiesFresh env p.k st = true →
    ConLeche.nestedContainersOk env st.pins = true →
    ConLeche.auxBlock p st = some b →
    ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true = .ok envAux →
    ConLeche.auxStoredAll envAux b b.k = some stored →
    ConLeche.pinsClosed p.nP st.pins = true →
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envAux p.nP st.pins = .ok () →
    (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true →
    ConLeche.nestedCopySrcOk env p st = true →
    ConLeche.nestedGroupsOk env p st = true →
    ConLeche.nestedPinKindsOk p b st stored = true →
    -- K.35's conjunct, the run's own (lane M7-2's request, session 10): every
    -- copy and copy constructor in the read-back recursor types and rules is
    -- applied to `nP + arity` arguments whose first `nP` are the block's
    -- parameter variables — the restore's `args.drop nP` precondition, which
    -- the recursors' readings stand on (`auxAppsOk_reflect`, and with it
    -- `NestedRecTysAuxOf` is gone)
    ConLeche.nestedAuxAppsOk p st stored = true →
    (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR →
    ConLeche.restoreRecTys (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms →
    ConLeche.restoreRecTys (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.numNested).map p.mimicRecName)
        (stored.drop p.k) = .ok cvRns →
    (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
      = .ok rulesM →
    (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
      = .ok rulesN →
    ConLeche.nestedTables (m := ConLeche.CheckM)
        (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
          ((p.formers.getD mIdx default).1.name, a.tbl, cs))
        (ConLeche.storeNestedRecs
          ((cvRms.zip ((stored.take p.k).zip rulesM)).map
              (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
            ++ (cvRns.zip ((stored.drop p.k).zip rulesN)).map
              (fun (cv, a, rs) => (cv, a.mI, a.rP, rs)))
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env))) = .ok envOut →
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envOut p.nP st.pins = .ok () →
    (p.memberRecs.length == cvRms.length && p.mimicRecs.length == cvRns.length) = true →
    ConLeche.nestedRecsOk (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))
        p.nP b.k b.n
        ((((p.memberRecs.zip cvRms).zip rulesM).zipIdx.map
            (fun (((sr, cv), rs), mIdx) =>
              (sr, (b.ownCtors mIdx).map (fun (J, c) => (J, c.nF)), cv, rs)))
          ++ (((p.mimicRecs.zip cvRns).zip rulesN).zipIdx.map
            (fun (((sr, cv), rs), j) =>
              (sr, (b.ownCtors (p.k + j)).map (fun (J, c) => (J, c.nF)), cv, rs))))
      = .ok () →
    ∀ (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
      (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
      (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
      (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
      (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
      (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
      (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
      (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
      (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR : Nat → Nat → List Expr)
      (pinsS : List PinSyn)
      (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env))),
      ConLeche.consNestedFormers (stored.take p.k) env
        = ConLeche.consMutualFormers (fms.take p.k) env →
      NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
        fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂ →
      ∃ mpOut : EnvModelM V μ envOut,
        NestedTailOut (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
          (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
          (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
          (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
          mp stored mp₂ envOut mpOut

/-! ## The consumer -/

omit [SetTheory V] in
/-- The block has a member (the elimination reads the first type). -/
theorem nested_kpos {F : Nat} {env : Env} {p : NestedParts} {fmsA ctorsA₀ : List ConstantVal}
    {st : ElimState}
    (hfA : ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA₀) = .ok st) :
    0 < p.k := by
  have hlenA : fmsA.length = p.k := ConLeche.nestedAnnotFormers_length hfA
  unfold ConLeche.elimNested at helim
  cases hh : (ConLeche.nestedTypes0 p fmsA ctorsA₀).head? with
  | none => rw [hh] at helim; exact nomatch helim
  | some t₀ =>
    have hlen := ConLeche.nestedTypes0_length p fmsA ctorsA₀
    rw [hlenA] at hlen
    cases hl : ConLeche.nestedTypes0 p fmsA ctorsA₀ with
    | nil => rw [hl] at hh; exact nomatch hh
    | cons x xs => rw [hl] at hlen; simp only [List.length_cons] at hlen; omega

/-- **The model WITH ITS BLOCKS survives a nested block** (the nested
half's run-level consumer): the run's stages through the restored
constructors keep the model and leave the block model
(`NestedCoreModeled`), the tail keeps it from there and hands back the
install's conses, the agreements and the block's representation at the
OUTPUT model (`NestedTailModeled`, DESIGN §U.67); the containers' block
models are the pre-block carrier's own (`EnvModelB.blocks`, task #315
M7-3).

The block just installed is read back as its own container group
(`nestedContainerModeled` at the run's K.34 conjunct) and carries its
group's obligation WITH ITS PINS — `nestedBlockAt_of` at M7-1's pins'
laws (`nestedPinRecLaws_of`, model-free, so they cross for nothing) and
L-E's pins' shapes (`nestedPinShapes_of` at the groups the tail names,
crossed to the output model by `PinShapes.crossEnv`, which reads the
carrier only at the block's members and its pins' containers and so
needs no reading hypothesis at all).  Every OLD container's block
crosses the whole install (`EnvBlocksOf.crossIndP` at
`NestedInstallExt`, under the guard `TableCross`). -/
theorem declNested_of (hμ : μ.verifiedChecks = true) {F : Nat} {env envOut : Env}
    {p : NestedParts} (mp : EnvModelB V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hcore : NestedCoreModeled V μ F) (htail : NestedTailModeled V μ F)
    (h : ConLeche.Semantics.DeclNestedRun μ F env p envOut) :
    Nonempty (EnvModelB V μ envOut) := by
  classical
  obtain ⟨h0, h1, st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, fmsA, ctorsA,
    hfA, hcA, helim, hcount, hfresh, hcont, hb, haux, hstored, hclosed, hpinsAux, hcaps, hsrc,
    -, hgrp, hmn, hsc, -, hK32, hkinds, hauxApps, hrank, -, -, hK42, hpins₁, hctors, hrm, hrn, -, -,
    hrulesM, hrulesN, htbl, hpinsOut, hcnt, hrecs, hrb, -, -⟩ := h
  -- the `-` after `hsrc` is K.31's `pinsDistinct` conjunct: named for the
  -- identities' discharge (`NestedPinsIdent`, lane L-B), not consumed here;
  -- `hmn` after `hgrp` is K.44's `nestedPinMentionOk`, which lane L-E's
  -- `ContainerModeled.nestMention` is discharged from at the block's own
  -- read-back (`nestedContainerModeled`); the `-` after `hsc` is K.48's
  -- `pinsLevelsOk`, which `ContainerModeled.pinParams` reads at the nested
  -- site and nothing here;
  -- `hK32` after THAT is K.32's `nestedCopyTargetsOk`, carried down to
  -- `NestedPinsRun` for the same discharge's `ordF` arm (task #315 L-E,
  -- DESIGN §U.64) and not consumed here; `hauxApps` after `hkinds` is
  -- K.35's `nestedAuxAppsOk`, which the tail consumes, and `hrank` after
  -- it is K.37's `nestedPinRankOk` — the global entry theorem's induction
  -- measure, carried down to `NestedPinsRun` (task #315 L-E, DESIGN
  -- §U.55) — the `-` after THAT is K.40's `nestedPinParentOk` and the one
  -- after THAT K.41's `nestedPinRootPairOk`, neither consumed on this
  -- path; `hK42` after THEM is K.42's second positivity run on the minted
  -- copies, carried down to `NestedPinsRun` for the copies' identities'
  -- `ordF`-LEFT arm (lane L-B's `NestedPinsShape`) and not consumed here;
  -- then K.34's `blockReadBackOk` (`hrb`) — the route's own
  -- read-back, which the block this route stores needs and `mp.blocks`
  -- carries for the rest — and the LAST two `-` are K.47's
  -- `nestedOwnPinsOk` and K.43's `blockOwnMimicsOk`, which
  -- `ContainerModeled.ownPins` reads and nothing here does;
  -- the two `-` after `hrn` are K.39's `Nodup` of the restored recursors'
  -- names and K.45's disjointness of those names from the auxiliary ones,
  -- which the provision loop's conses and the restore's agreement need,
  -- and nothing on this path reads
  -- THE CERTIFICATION-ONLY RECORDS (K.35's follow-up): the run carries them
  -- as `certOnly μ …`; this theorem is stated under `hμ`, at which the gate
  -- is the Bool the consumers below expect — K.34's `blockReadBackOk`
  -- (`hrb`) among them, which is the block's own reading
  replace hcont := ConLeche.certOnly_elim hcont hμ
  replace hsrc := ConLeche.certOnly_elim hsrc hμ
  replace hgrp := ConLeche.certOnly_elim hgrp hμ
  replace hmn := ConLeche.certOnly_elim hmn hμ
  replace hsc := ConLeche.certOnly_elim hsc hμ
  replace hK32 := ConLeche.certOnly_elim hK32 hμ
  replace hkinds := ConLeche.certOnly_elim hkinds hμ
  replace hrank := ConLeche.certOnly_elim hrank hμ
  replace hK42 := hK42 hμ
  replace hauxApps := ConLeche.certOnly_elim hauxApps hμ
  replace hrb := ConLeche.certOnly_elim hrb hμ
  have hPM : PinsModeled mp.base2 st.pins := pinsModeled_of_env mp.blocks hcont
  obtain ⟨fms, f₀, ctorsA', sortss, kinds, mp₁, ppsF, W, idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF,
    eissF, tssF, dsR, xFvsR, pinsS, mp₂, henv, O⟩ := hcore hμ mp.toEnvModelM hE p st b envAux stored
    ctorsR fmsA ctorsA hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux hstored hclosed hpinsAux
    hcaps hsrc hgrp hsc hK32 hkinds hrank hK42 hpins₁ hctors
  obtain ⟨mpOut, T⟩ := htail hμ mp.toEnvModelM hE p envOut st b envAux stored ctorsR cvRms cvRns
    rulesM rulesN fmsA ctorsA hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux hstored hclosed
    hpinsAux hcaps hsrc hgrp hkinds hauxApps hctors hrm hrn hrulesM hrulesN htbl hpinsOut hcnt
    hrecs fms f₀
    ctorsA' sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR
    pinsS mp₂ henv O
  -- the lists' lengths, and the block's own reading
  have hslen : stored.length = b.k := (ConLeche.auxStoredAll_get hstored).1
  have hk0 : 0 < p.k := nested_kpos hfA helim
  have hkle : p.k ≤ b.k := by rw [O.bk]; omega
  have hclen : ctorsR.length = p.k := by
    rw [(ConLeche.mapM_except_inv hctors).1, List.length_take]
    omega
  have hcm := nestedContainerModeled hcaps hcont hk0 hmn haux hstored hctors O T
  have hfreshMs : ∀ n ∈ p.memberNames, env.find? n = none := by
    rw [← O.record.memberNames]
    exact nestedMembersFresh hcaps haux hstored O
  -- an OLD container's group is not the block's
  have hciNe : ∀ (J : Name) (ci : ContainerInfo), ConLeche.containerInfo? env J = some ci →
      ci ≠ ConLeche.blockContainerInfo p.nP (((stored.take p.k).zip ctorsR).map fun (a, cs) =>
        (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF))) := by
    intro J ci hci heq
    obtain ⟨M, hM⟩ : ∃ M, ci.members[0]? = some M :=
      ⟨_, List.getElem?_eq_getElem (containerInfo?_members_pos hci)⟩
    obtain ⟨cvT, caps, cvR, mI, rP, rules, H⟩ := ConLeche.containerInfo?_inv hci
    obtain ⟨cvC, capsC, cvRc, mIc, rulesC, hfind, -, -, -, -⟩ :=
      H.2.2.2.2 M (List.mem_of_getElem? hM)
    rw [heq] at hM
    have h0M : (((stored.take p.k).zip ctorsR).map fun (a, cs) =>
        (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))[0]?
        = some ((stored.getD 0 default).cvTa, (ctorsR.getD 0 []).map fun c => (c.1, c.2.2)) :=
      nestedReadBack_getElem? hk0 (by omega) hclen
    have hM' : (ConLeche.blockContainerInfo p.nP (((stored.take p.k).zip ctorsR).map
        fun (a, cs) => (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))).members[0]?
        = some ⟨(stored.getD 0 default).cvTa.name, (stored.getD 0 default).cvTa.levelParams,
          (stored.getD 0 default).cvTa.type,
          ((ctorsR.getD 0 []).map fun c => (c.1, c.2.2)).map
            fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ := by
      show (List.map _ _)[0]? = _
      rw [List.getElem?_map, h0M]
      rfl
    rw [hM'] at hM
    obtain rfl : M = _ := (Option.some.inj hM).symm
    rw [show (⟨(stored.getD 0 default).cvTa.name, (stored.getD 0 default).cvTa.levelParams,
      (stored.getD 0 default).cvTa.type, ((ctorsR.getD 0 []).map fun c => (c.1, c.2.2)).map
        fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ : ConLeche.ContainerMember).name
        = (stored.getD 0 default).cvTa.name from rfl,
      nestedStoredFresh hcaps (by omega) hk0] at hfind
    exact nomatch hfind
  -- the pins' laws (model-free) and the pins' shapes, crossed to the output model
  have hLaws := (nestedPinRecLaws_of hμ O.facts O.grouped O.bk mp₂.base2 O.stage.groups).cross
    (m₂ := mpOut.base2)
  have hBreps : ∀ q, q < pinsS.length → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env))
        ((nestedBlockModel (V := V) p b fms f₀ ctorsA' kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt q).J = some ci →
      IsBlockModels mp₂.base2 (blockOf mp.base2 ci) := by
    intro q hq ci hci
    obtain ⟨q₀, kJ, i, -, -, G⟩ := T.groups q hq ci hci
    exact G.reps
  have hShapes := (nestedPinShapes_of (B := blockOf mp.base2) mp₂.base2
      (fun q hq ci hci => by
        obtain ⟨q₀, kJ, i, hqe, hi, G⟩ := T.groups q hq ci hci
        exact ⟨q₀, kJ, i, hqe, hi, G, G.sameE⟩)
      (fun q hq => (T.conts q hq).imp fun _ hh => hh.1)).crossEnv T.findR T.agree hk0
    O.reps.toIsBlockModels
    hBreps (fun q hq ci hci => by
      obtain ⟨ci', h₂, hOut, -⟩ := T.conts q hq
      obtain rfl : ci = ci' := Option.some.inj (hci.symm.trans h₂)
      exact hOut)
  refine ⟨⟨mpOut, ⟨fun ci => if ci = ConLeche.blockContainerInfo p.nP
      (((stored.take p.k).zip ctorsR).map fun (a, cs) =>
        (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))
      then nestedBlockModel (V := V) p b fms f₀ ctorsA' kinds env ppsF W idxF dsF esF srcsF fvsPF
        xrestF eissF tssF ctorsR dsR xFvsR pinsS
      else blockOf mp.base2 ci, ?_⟩⟩⟩
  obtain ⟨new, E, hMs⟩ := T.install
  refine (blockOf_of_env mp.blocks).crossIndP (Ts := p.memberNames) E.toConsExt.ext
    E.toConsExt.newN E.toConsExt.freshN (E.recN hMs) mp.base2.wf mp.base2.rec_ctors
    (fun n c _ hf => E.toConsExt.ext n c hf)
    (constsResolve_of_findPreserved (fun hf => E.toConsExt.ext _ _ hf)) T.agree₀ ?_ hfreshMs
    (fun J ci _ hci => if_neg (hciNe J ci hci)) ?_
  · -- the readings cross the whole install under the guard
    intro ψ dp e hpf ea hr
    rw [denoteMeta_acval_congr (fun n hn => (T.agree₀ n hn).symm) dp e] at hr
    exact denoteMeta_env_mono_projFree E.tableCross.find E.tableCross.lit E.tableCross.proj
      dp e hpf hr
  · -- the new block IS its own group
    intro J hJ ci hci
    obtain ⟨cv, caps, hf⟩ := containerInfo?_found hci
    have hJM : J ∈ p.memberNames := E.indMs hf hJ
    rw [← O.record.memberNames] at hJM
    obtain ⟨i, hi, rfl⟩ := nestedMemberStored haux hstored O J hJM
    have hread := containerInfo?_of_readBack (nP := p.nP) hrb
      (nestedReadBack_getElem? hi (by omega) hclen)
    rw [hread] at hci
    obtain rfl : ci = _ := (Option.some.inj hci).symm
    refine nestedBlockAt_of mpOut.base2 (if_pos rfl) ?_ hLaws ?_
    · exact hcm
    · refine hShapes.congrB fun q hq ci' hci' => ?_
      obtain ⟨ci₀, -, hOut, hEnv⟩ := T.conts q hq
      obtain rfl : ci' = ci₀ := Option.some.inj (hci'.symm.trans hOut)
      exact if_neg (hciNe _ ci' hEnv)

/-! ## The core, modulo the restored constructors' loop -/

/-- **The nested core, modulo the restored constructors' loop**: the
scratch run's formers' stage (`mutualFormersStage` at the `auxRoute`
grade), the prefix stage and the loop (`nestedStageFacts_of`), the
block model at every member (`nestedBlockReps_of`), and the block
model's record (`NestedBlockModelOf`: arities off `auxBlock`, names
off the elimination, pins off the loop's records) — the output packaged
CONCRETELY (`NestedCoreOut`). -/
theorem nestedCoreModeled_of {F : Nat} (hst : NestedCtorsStaged V μ F) :
    NestedCoreModeled V μ F := by
  intro hμ env mp hE p st b envAux stored ctorsR fmsA ctorsA₀ hPM h0 h1 hfA hcA helim hcount hfresh
    hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32 hkinds hrank hK42 hpins₁
    hctors
  obtain ⟨hnd, hlp, hmem, h3, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4, cvRas,
    rulesOf, hformers, hf₀, htq₀, hcross, -, hctorsA, hkindsA, hfo, -, -, -, -⟩ :=
    ConLeche.checkMutualCore_inv haux
  obtain ⟨-, rfl⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨mp₁, ppsF, W, idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, eissF, tssF, h⟩ :=
    mutualFormersStage hμ mp hE b hnd hlp hmem hformers hf₀ htq₀ hcross hctorsA hkindsA hfo
  have hbk : b.k = p.k + st.pins.length := ConLeche.auxBlock_k_count hfA helim hb
  obtain ⟨henv, -⟩ := ConLeche.consNestedFormers_take_eq haux hformers hstored p.k (by omega)
  rw [henv] at hctors hpins₁
  obtain ⟨mp₂, dsR, xFvsR, pinsS, S⟩ := nestedStageFacts_of hst hμ hE hPM h0 h1 hfA hcA helim hcount
    hfresh hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32 hkinds hrank hK42 hpins₁
    hnd h3
    hformers hctorsA h hbk hctors
  have hbk' : b.k = p.k + pinsS.length := by rw [hbk, S.pinsLen]
  obtain ⟨hreps, htyped⟩ := nestedBlockReps_of hμ h h3 hbk' mp₂ S.findM S.leafM S.FD S.ctorsLen
    S.ctorFacts S.domFacts S.groups
  refine ⟨fms, f₀, ctorsA, sortss, kinds, mp₁, ppsF, W, idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF,
    eissF, tssF, dsR, xFvsR, pinsS, mp₂, henv, ?_⟩
  exact
    { formers := hformers
      facts := h
      ctors := hctorsA
      kindsRun := hkindsA
      bk := hbk'
      grouped := h3
      nodup := hnd
      stage := S
      reps := hreps
      typed := htyped
      record :=
        { k := rfl
          nP := (ConLeche.auxBlock_fields hb).1
          env₀ := rfl
          memberNames := S.names
          large := (ConLeche.auxBlock_fields hb).2.2.1
          nPins := S.pinsLen
          pin := S.pinRec
          ctors := fun _ _ => rfl } }

end ConLeche.Model
