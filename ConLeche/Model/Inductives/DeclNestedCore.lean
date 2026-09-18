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
* `conts`: the pin's container reads back the SAME group at the
  constructors' environment, at the OUTPUT one and at the pre-block
  one.  The last of the three is what makes it the tail's: the first
  is the core's (`nestedContainersOk_group`) and the second is that
  one crossed by the `containerInfo?` frame
  (`Verify/Inductives/ContainerFrame.lean`).

  (`groups` — the pins' groups at their container's block model NAMED
  by `blockOf mp.base2`, DESIGN §U.36 (d)'s strengthening — was the
  seventh field until task #315 M7-3 session 12 found it to be the
  CORE's: `NestedPinsRun.groupSyn` builds the group at exactly that
  assignment and the pin's own reading is its group's base's, so
  `NestedStageFacts.groupsAt` publishes it and `conts` carries it to
  the constructors' environment.) -/
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

/-- **`allLevelParamsDefined` through an application spine**: the
predicate is a conjunction over the expression tree, so a spine's head
and every one of its arguments satisfy it.  Task #315 K.48 (DESIGN
§U.69 (e)) records the Bool at the PIN TERM, which is its container
applied to the pin's components (`NestedStageFacts.pinRec`), and the
two halves `ContainerModeled.pinParams` needs — the level ARGUMENTS
and the COMPONENTS — are read off that one record here. -/
theorem allLevelParamsDefined_mkAppN {ps : List Name} :
    ∀ (as : List Expr) (f : Expr), (Expr.mkAppN f as).allLevelParamsDefined ps = true →
      f.allLevelParamsDefined ps = true ∧ ∀ a ∈ as, a.allLevelParamsDefined ps = true := by
  intro as
  induction as with
  | nil => intro f h; exact ⟨h, fun _ ha => nomatch ha⟩
  | cons a as ih =>
    intro f h
    rw [Expr.mkAppN] at h
    obtain ⟨hfa, has⟩ := ih (.app f a) h
    rw [Expr.allLevelParamsDefined, Bool.and_eq_true] at hfa
    refine ⟨hfa.1, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hfa.2
    · exact has x hx

/-- **A read spine's ψ-congruence at the expressions' own level
parameters** — `denoteMeta_params_ext` lifted from one expression to a
spine (task #315 K.48, DESIGN §U.69 (e)): two assignments agreeing on
`ps` read one list of `ps`-closed expressions to ONE list of terms.
With `DenoteMetaSpine.det` this is the `Ds` half of
`ContainerModeled.pinParams`, the half DESIGN §U.69 (e) recorded as
"does not reduce at all" — it does, once the kernel records the pin's
levels. -/
theorem denoteMetaSpine_params_ext {env₂ : Env} (m : EnvModel V env₂) {ps : List Name}
    {φ₁ φ₂ : Name → Nat} (hφ : ∀ pp ∈ ps, φ₁ pp = φ₂ pp) {dp : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, (∀ e ∈ as, e.allLevelParamsDefined ps = true) →
      DenoteMetaSpine m.acval env₂ φ₁ dp as vs → DenoteMetaSpine m.acval env₂ φ₂ dp as vs := by
  intro as
  induction as with
  | nil => intro vs _ h; cases h; exact .nil
  | cons a as ih =>
    intro vs hall h
    cases h with
    | cons ha hs =>
      refine .cons ?_ (ih (fun e he => hall e (List.mem_cons_of_mem _ he)) hs)
      rw [← denoteMeta_params_ext m hφ dp a (hall a List.mem_cons_self)]
      exact ha

/-- **A PIN'S DATA DEPEND ON THE ASSIGNMENT ONLY THROUGH THE
CONTAINER'S OWN LEVEL PARAMETERS**, at the nested block's own
read-back — `ContainerModeled.pinParams` (task #315 M7-3 session 14,
DESIGN §U.69 (e)), DISCHARGED from the kernel's K.48 record
`pinsLevelsOk` (`pins.all fun q => q.pin.allLevelParamsDefined p.lps`)
and the containers' block models.  It replaces the named premise
`NestedPinParams`, which said exactly this and which DESIGN §U.69 (e)
recorded as "carried NOWHERE": K.48 is that record.

The three halves, at a pin `q` whose group `[q₀, q₀ + kJ)` the stage
names (`NestedStageFacts.groupsAt`, at the container's OWN
`containerInfo?` reading, so the block model is the pre-block
carrier's `blockOf`):

* K.48 at `q` is read through `pinRec`: the pin TERM is
  `mkAppN (.const J lvls) DsE`, so `allLevelParamsDefined_mkAppN`
  splits the record into "every level argument is `allParamsDefined`
  in `p.lps`" and "every component is";
* the `Ds` half is the components' reading at the two assignments
  (`pinDs`), which `denoteMetaSpine_params_ext` transports and
  `DenoteMetaSpine.det` identifies;
* the `u` and `Ids` halves go through the CONTAINER's block model:
  `NestedStageFacts.pinψ` spells the pin's level assignment as
  `Level.substFn` at the container's level parameters AND gives the
  arity, so `Level.substFn_ext` at the level arguments' record turns
  the agreement on `p.lps` into an agreement on the container's own
  level parameters; `NestedPinGroup.pinU`/`pinPps` read `u` and `Ids`
  off the group's block model at that assignment, and
  `IsBlockModel.uParams` / `FormerData.params` — at the member's own
  constant, which `ContainerModeled.member` NAMES (`⟨M.name, M.lps,
  M.type⟩`, whose level parameters `containerInfo?_inv` identifies
  with the pin's container's) — are their congruences.

The consumer's agreement hypothesis is stated over the `i`-th stored
auxiliary's level parameters, K.48's Bool over `p.lps`; `hlps` is that
identification, which `declNested_of` discharges from
`MutualFormersFacts.lps` and `auxBlock_fields`. -/
theorem nestedPinParams_of {F : Nat} {st : ElimState} {envAux : Env}
    {stored : List AuxStored} {sortss : List (List Level)} {xFvsF : Nat → List Expr}
    {mp : EnvModelM V μ env} {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
    {mp₂ : EnvModelM V μ ENV₂}
    (hcaps : ((stored.take p.k).all fun a =>
      !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (hcont : ConLeche.nestedContainersOk env st.pins = true)
    (hlv : ConLeche.pinsLevelsOk p.lps st.pins = true)
    (hPM : PinsModeled mp.base2 st.pins)
    (hlps : ∀ i, i < p.k → (stored.getD i default).cvTa.levelParams = p.lps)
    (haux : ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true
      = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (O : NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂) :
    ∀ (i : Nat), i < p.k → ∀ q, q < (D).nPins → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ pp ∈ (stored.getD i default).cvTa.levelParams, ψ₁ pp = ψ₂ pp) →
      ((D).pinAt q).u ψ₁ = ((D).pinAt q).u ψ₂ ∧
      ((D).pinAt q).Ds ψ₁ = ((D).pinAt q).Ds ψ₂ ∧
      ((D).pinAt q).Ids ψ₁ = ((D).pinAt q).Ids ψ₂ := by
  intro i hi q hq ψ₁ ψ₂ hag
  rw [hlps i hi] at hag
  -- K.48 at the pin, split through the pin's recorded shape
  have hql : q < st.pins.length := by rw [← O.record.nPins]; exact hq
  have hpq : st.pins[q]? = some st.pins[q] := List.getElem?_eq_getElem hql
  obtain ⟨hJ, hpin⟩ := O.stage.pinRec q _ hpq
  simp only [ConLeche.pinsLevelsOk, List.all_eq_true] at hlv
  have hlvq := hlv _ (List.mem_of_getElem? hpq)
  rw [hpin] at hlvq
  obtain ⟨hhead, hargs⟩ := allLevelParamsDefined_mkAppN _ _ hlvq
  have hlvls : ∀ l ∈ ((D).pinAt q).lvls, l.allParamsDefined p.lps = true := by
    have : ((D).pinAt q).lvls.all (Level.allParamsDefined p.lps) = true := hhead
    exact List.all_eq_true.mp this
  -- the components' readings: one spine, two assignments
  have hDs : ((D).pinAt q).Ds ψ₁ = ((D).pinAt q).Ds ψ₂ :=
    DenoteMetaSpine.det
      (denoteMetaSpine_params_ext mp₂.base2 hag hargs (O.stage.pinDs q hq ψ₁))
      (O.stage.pinDs q hq ψ₂)
  -- the pin's container, its group and its block model
  obtain ⟨ci, hci0, -⟩ := (ConLeche.nestedContainersOk_group hcont).2 _ (List.mem_of_getElem? hpq)
  have hci : ConLeche.containerInfo? env ((D).pinAt q).J = some ci := by rw [hJ]; exact hci0
  obtain ⟨CM, -⟩ := hPM _ (List.mem_of_getElem? hpq) ci hci0
  obtain ⟨q₀, kJ, i', rfl, hi', G⟩ := O.stage.groupsAt q hq ci hci
  have hik : i' < ci.members.length := by rw [← CM.k, G.kEq]; exact hi'
  obtain ⟨M, hM⟩ : ∃ M, ci.members[i']? = some M := ⟨_, List.getElem?_eq_getElem hik⟩
  obtain ⟨-, -, cvR, mI, rP, rules, hI⟩ := CM.member i' M hM
  -- the two assignments agree on the container's own level parameters
  obtain ⟨cvT, caps, _cvR, _mI, _rP, _rules, hfT, -, -, -, hmems⟩ :=
    ConLeche.containerInfo?_inv hci
  obtain ⟨cvC, _capsC, _cvRc, _mIc, _rulesC, -, -, hMlps, -, hlpsEq, -, -⟩ :=
    hmems M (List.mem_of_getElem? hM)
  have hfreshMem : ∀ n ∈ (D).memberNames, env.find? n = none :=
    nestedMembersFresh hcaps haux hstored O
  have hne : ∀ g ∈ fms.take p.k, g.cvTa.name ≠ ((D).pinAt (q₀ + i')).J := by
    intro g hg heq
    have hmem : g.cvTa.name ∈ (D).memberNames := List.mem_map_of_mem hg
    rw [hfreshMem _ (heq ▸ hmem)] at hfT
    exact nomatch hfT
  have hfind₁ : (ConLeche.consMutualFormers (fms.take p.k) env).find? ((D).pinAt (q₀ + i')).J
      = some (.indInfo cvT caps) := by
    rw [ConLeche.consMutualFormers_find?_of_ne hne]; exact hfT
  obtain ⟨hlenL, hψeq⟩ := O.stage.pinψ (q₀ + i') hq cvT caps hfind₁
  have hψ : ∀ ψ : Name → Nat, ((D).pinAt (q₀ + i')).ψJ ψ
      = Level.substFn ψ cvT.levelParams ((D).pinAt (q₀ + i')).lvls := hψeq
  have hagψ : ∀ r ∈ M.lps, ((D).pinAt (q₀ + i')).ψJ ψ₁ r = ((D).pinAt (q₀ + i')).ψJ ψ₂ r := by
    intro r hr
    rw [hψ ψ₁, hψ ψ₂]
    exact Level.substFn_ext hag hlvls hlenL r (by rw [← hlpsEq, ← hMlps]; exact hr)
  refine ⟨?_, hDs, ?_⟩
  · -- `u`: the group's index universe at the container's assignment
    rw [G.pinU i' hi' ψ₁ i' hi', G.pinU i' hi' ψ₂ i' hi']
    exact hI.uParams i' (by rw [G.kEq]; exact hi') _ _ hagψ
  · -- `Ids`: the container's own telescope, past its parameters
    unfold PinSyn.Ids
    rw [G.pinPps i' hi', (hI.former.params _ _ hagψ).1]

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
      (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) mp stored mp₂ envOut mpOut)
    (hpinParams : ∀ (i : Nat), i < p.k → ∀ q, q < (D).nPins → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ pp ∈ (stored.getD i default).cvTa.levelParams, ψ₁ pp = ψ₂ pp) →
      ((D).pinAt q).u ψ₁ = ((D).pinAt q).u ψ₂ ∧
      ((D).pinAt q).Ds ψ₁ = ((D).pinAt q).Ds ψ₂ ∧
      ((D).pinAt q).Ids ψ₁ = ((D).pinAt q).Ids ψ₂) :
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
    (fun ψ mm' j fs => ofNested_inj ψ mm' j fs) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
      obtain ⟨ci, -, -, hEnv⟩ := T.conts q hq
      obtain ⟨q₀, kJ, i, rfl, hi, G⟩ := O.stage.groupsAt q hq ci hEnv
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
  · -- `pinParams`: the premise, at the read-back's member record
    -- (`nestedReadBack_getD`: the group's `i`-th member is the `i`-th
    -- stored auxiliary's `ConstantVal`)
    intro i hi q hq ψ₁ ψ₂ hag
    have hik : i < p.k := by
      rw [List.length_map, List.length_zip, List.length_take, hclen] at hi
      omega
    refine hpinParams i hik q hq ψ₁ ψ₂ fun pp hpp => hag pp ?_
    rw [nestedReadBack_getD hik (by omega) hclen]
    exact hpp
  · -- `member`
    intro i hi
    obtain ⟨cvR, mI, rP, rules, hI⟩ := T.repsAt i hi
    refine ⟨cvR, mI, rP, rules, ?_⟩
    rw [nestedReadBack_getD (hdk ▸ hi) (by omega) hclen]
    rw [hnamesS i (hdk ▸ hi)] at hI
    exact hI

/-- **THE BLOCK'S OWN PINS ARE ITS RECORDED PINS, AT EVERY
INSTANTIATION** (task #315 M7-3 session 18, DESIGN §U.79):
`ContainerOwnPinsSyn` at the nested route — the ninth and last of the
nine `ContainerModeled` construction sites, and the only one whose
block carries a mimic at all (the other eight read the empty table,
`ContainerOwnPinsSyn.of_noMimics`).

The reader's table at a member is the walk at the GROUP's first member
(`containerOwnPinsAt` reads `ci.members.head?`), and the read-back
(K.34) says that group is this block's own — so the walk is the one
K.47 recorded, at the block's own levels (`p.lps.map Level.param`, the
identity substitution) and its parameter OPENERS.  K.43 fixes its
LENGTH (`p.numNested` steps) and K.47 its CONTENT (`st.pins`), so with
one entry per step at most, EVERY step reads a pin there;
`containerOwnPinsAtGo_subst` then moves the whole table to the level
arguments and components the reader asked for, entry by entry, and
`NestedBlockModelOf.pin` reads each entry back as the block model's own
recorded pin — at which `ownSubst` IS `PinSyn.ownAt`, which is the
clause.

Two side conditions are the reader's own and not assumptions: the
components' CLOSEDNESS is the clause's hypothesis (and has to be — see
`ContainerOwnPinsSyn`, whose docstring carries the two real-run
counterexamples), and a reader that asks at the wrong NUMBER of
components gets the empty table, which is vacuous. -/
theorem nestedOwnPins_of {F : Nat} {st : ElimState} {envAux : Env}
    {stored : List AuxStored} {sortss : List (List Level)} {xFvsF : Nat → List Expr}
    {mp : EnvModelM V μ env} {mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env)}
    {mp₂ : EnvModelM V μ ENV₂} {envOut : Env} (mpOut : EnvModelM V μ envOut)
    (hk0 : 0 < p.k) (hcount : st.pins.length = p.numNested)
    (haux : ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true
      = .ok envAux)
    (hstored : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hctors : (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors) = .ok ctorsR)
    (hrb : ConLeche.blockReadBackOk envOut p.nP
      (((stored.take p.k).zip ctorsR).map fun (a, cs) =>
        (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF))) = true)
    (hlps : ∀ i, i < p.k → (stored.getD i default).cvTa.levelParams = p.lps)
    (hown : ConLeche.nestedOwnPinsOk envOut p st = true)
    (hmim : ConLeche.blockOwnMimicsOk envOut (p.formers.headD default).1.name p.numNested = true)
    (O : NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
      fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂) :
    ContainerOwnPinsSyn (V := V) envOut (D) := by
  -- the lists' lengths and the members' names (as `nestedContainerModeled` reads them)
  have hslen : stored.length = b.k := (ConLeche.auxStoredAll_get hstored).1
  have hkle : p.k ≤ b.k := by rw [O.bk]; omega
  have hclen : ctorsR.length = p.k := by
    rw [(ConLeche.mapM_except_inv hctors).1, List.length_take]
    omega
  have hdk : (D).k = p.k := rfl
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
  -- the block's FIRST member is the first former: that is where both walks start
  have hC₀ : (D).memberName 0 = (p.formers.headD default).1.name := by
    show (D).memberNames.getD 0 .anonymous = _
    rw [O.record.memberNames]
    have hk : 0 < p.formers.length := hk0
    show (p.formers.map (·.1.name)).getD 0 .anonymous = (p.formers.headD default).1.name
    cases hform : p.formers with
    | nil => rw [hform] at hk; exact absurd hk (by simp)
    | cons g gs => rfl
  -- the read-back (K.34), packaged: ONE group at every member, its parameter
  -- count the block's, and its first member the first former
  obtain ⟨ciB, hciB, hnPB, hheadB, hheadL⟩ :
      ∃ ciB : ContainerInfo,
        (∀ i, i < p.k → ConLeche.containerInfo? envOut ((D).memberName i) = some ciB) ∧
        ciB.nP = p.nP ∧
        ciB.members.head?.map (·.name) = some ((p.formers.headD default).1.name) ∧
        ciB.members.head?.map (·.lps) = some p.lps := by
    have hmemAt : ∀ i, i < p.k →
        (ConLeche.blockContainerInfo p.nP (((stored.take p.k).zip ctorsR).map fun (a, cs) =>
            (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))).members[i]?
          = some ⟨(stored.getD i default).cvTa.name, (stored.getD i default).cvTa.levelParams,
              (stored.getD i default).cvTa.type,
              ((ctorsR.getD i []).map fun c => (c.1, c.2.2)).map
                fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ := by
      intro i hi
      show (List.map _ _)[i]? = _
      rw [List.getElem?_map, nestedReadBack_getElem? hi (by omega) hclen]
      rfl
    have hciAll : ∀ i, i < p.k → ConLeche.containerInfo? envOut ((D).memberName i)
        = some (ConLeche.blockContainerInfo p.nP (((stored.take p.k).zip ctorsR).map
            fun (a, cs) => (a.cvTa, cs.map fun (cv, _, nF) => (cv, nF)))) := by
      intro i hi
      unfold ConLeche.blockReadBackOk at hrb
      simp only [List.all_eq_true] at hrb
      have hcm := hrb _ (List.mem_of_getElem? (hmemAt i hi))
      rw [show (⟨(stored.getD i default).cvTa.name, (stored.getD i default).cvTa.levelParams,
        (stored.getD i default).cvTa.type,
        ((ctorsR.getD i []).map fun c => (c.1, c.2.2)).map
          fun (cv, nF) => ⟨cv.name, cv.type, nF⟩⟩ : ConLeche.ContainerMember).name
          = (stored.getD i default).cvTa.name from rfl, ← hnamesS i hi] at hcm
      exact eq_of_beq hcm
    refine ⟨_, hciAll, rfl, ?_, ?_⟩
    · rw [List.head?_eq_getElem?, hmemAt 0 hk0, Option.map_some]
      show some (stored.getD 0 default).cvTa.name = _
      rw [← hnamesS 0 hk0, hC₀]
    · rw [List.head?_eq_getElem?, hmemAt 0 hk0, Option.map_some]
      show some (stored.getD 0 default).cvTa.levelParams = _
      rw [hlps 0 hk0]
  -- K.47: the table at the block's own levels and parameter OPENERS IS the
  -- recorded pin list
  obtain ⟨params, rest, hty, ps₀, hbase, hps₀⟩ :
      ∃ (params : List Expr) (rest : Expr),
        st.types.head?.bind (fun t₀ => ConLeche.openPisAtFvars p.nP t₀.type 0)
            = some (params, rest) ∧
          ∃ ps₀, ConLeche.containerOwnPinsAt envOut (p.formers.headD default).1.name
              (p.lps.map Level.param) params = some ps₀ ∧ ps₀ = st.pins.map (·.pin) := by
    unfold ConLeche.nestedOwnPinsOk at hown
    split at hown
    · rename_i params rest hty
      split at hown
      · rename_i ps₀ hbase
        exact ⟨params, rest, hty, ps₀, hbase, eq_of_beq hown⟩
      · exact nomatch hown
    · exact nomatch hown
  -- the openers: one per parameter, at its own index
  obtain ⟨t₀, -, hopen⟩ := Option.bind_eq_some_iff.mp hty
  have hplen : params.length = p.nP := ConLeche.openPisAtFvars_len p.nP hopen
  have hidx : ∀ j, j < p.nP → ∃ t, params[j]? = some (Expr.fvar j t) := by
    intro j hj
    obtain ⟨x, hx⟩ : ∃ x, params[j]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [hplen]; exact hj)⟩
    obtain ⟨t, ht⟩ := ConLeche.openPisAtFvars_index p.nP t₀.type 0 hopen j x hx
    exact ⟨t, by rw [hx, ht, Nat.zero_add]⟩
  -- the base walk, at the group the read-back names
  obtain ⟨cv₀, caps₀, ci₀, M₀, hfc₀, hci₀, hM₀, hps₀Eq⟩ := containerOwnPinsAt_inv hbase
  -- the clause
  intro i cvC caps lvls DsE ps hi hfind hDcl hps e he
  obtain ⟨cv, caps', ci, M, hfc, hci, hM, hpsEq⟩ := containerOwnPinsAt_inv hps
  have hciEq : ci = ciB := Option.some.inj (hci.symm.trans (hciB i (hdk ▸ hi)))
  rw [hciEq] at hci hM hpsEq
  have hcvEq : cv = cvC := (ConstantInfo.indInfo.inj (Option.some.inj (hfc.symm.trans hfind))).1
  rw [hcvEq] at hpsEq
  -- the group's first member is the block's first former, where BOTH walks start
  have hMname : M.name = (p.formers.headD default).1.name := by
    have hh := hheadB
    rw [hM, Option.map_some] at hh
    exact Option.some.inj hh
  have hci₀Eq : ci₀ = ciB :=
    Option.some.inj (hci₀.symm.trans (by rw [← hC₀]; exact hciB 0 hk0))
  rw [hci₀Eq] at hM₀ hps₀Eq
  have hM₀Eq : M₀ = M := Option.some.inj (hM₀.symm.trans hM)
  rw [hM₀Eq] at hps₀Eq
  -- the two walks read at the same level parameters: `containerInfo?` checks
  -- every member's against the queried constant's
  have hMlps : M.lps = p.lps := by
    have hh := hheadL
    rw [hM, Option.map_some] at hh
    exact Option.some.inj hh
  obtain ⟨hlvEq, hlpsC⟩ : cv₀.levelParams = cvC.levelParams ∧ cvC.levelParams = p.lps := by
    obtain ⟨cvT, capsT, cvR, mI, rP, rules, H⟩ := ConLeche.containerInfo?_inv hci
    obtain ⟨cvM, capsM, cvRc, mIc, rulesC, hfM, -, hMl, -, hlp, -⟩ :=
      H.2.2.2.2 M (List.mem_of_mem_head? hM)
    have h1 : cvT = cvC := (ConstantInfo.indInfo.inj (Option.some.inj (H.1.symm.trans hfind))).1
    have h2 : cvM = cv₀ := (ConstantInfo.indInfo.inj (Option.some.inj
      (hfM.symm.trans (by rw [hMname]; exact hfc₀)))).1
    refine ⟨by rw [← h2, ← h1]; exact hlp, ?_⟩
    rw [← h1, ← hlp, ← hMl]
    exact hMlps
  rw [hnPB, hlvEq, hlpsC] at hps₀Eq
  rw [hnPB, hlpsC] at hpsEq
  -- K.47, as a statement about the walk the reader runs
  have hbaseWalk : ConLeche.containerOwnPinsAtGo envOut (M.name.str "rec") p.lps
      (p.lps.map Level.param) params p.nP 64 0 = st.pins.map (·.pin) := by
    rw [← hps₀Eq]; exact hps₀
  -- a reader at the wrong NUMBER of components reads nothing
  by_cases hDlen : DsE.length = p.nP
  · -- K.43: the walk stops after `p.numNested` names
    have hstop : ConLeche.isRecInfoAt envOut
        (Name.appendIndexAfter (M.name.str "rec") (0 + p.numNested + 1)) = false := by
      simp only [ConLeche.blockOwnMimicsOk, Bool.and_eq_true, Bool.not_eq_true'] at hmim
      rw [hMname, Nat.zero_add]
      exact hmim.2
    -- K.47: one entry per name, so every step reads a pin
    have hlen : (ConLeche.containerOwnPinsAtGo envOut (M.name.str "rec") p.lps
        (p.lps.map Level.param) params p.nP 64 0).length = p.numNested := by
      rw [hbaseWalk, List.length_map, hcount]
    rw [hpsEq, containerOwnPinsAtGo_subst mpOut.base2.wf hplen hidx hDlen hDcl
      p.numNested 64 0 hstop hlen, hbaseWalk] at he
    -- every entry is a recorded pin, re-spelled
    obtain ⟨e₀, he₀mem, rfl⟩ := List.mem_map.mp he
    obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp he₀mem
    obtain ⟨q, hq⟩ := List.getElem?_of_mem hpin
    have hqlt : q < st.pins.length := by
      rcases Nat.lt_or_ge q st.pins.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hq; exact nomatch hq
    obtain ⟨hJ, hpinEq⟩ := O.record.pin q _ hq
    refine ⟨q, by rw [O.record.nPins]; exact hqlt, ?_⟩
    rw [hpinEq, ← hJ, hlpsC]
    show ownSubst p.nP p.lps lvls DsE
        (Expr.mkAppN (Expr.const ((D).pinAt q).J ((D).pinAt q).lvls) ((D).pinAt q).DsE) = _
    unfold ownSubst ConLeche.Model.PinSyn.ownAt
    rw [Expr.getAppFn_mkAppN, Expr.getAppArgs_mkAppN, O.record.nP]
    simp only [Expr.getAppFn, Expr.getAppArgs, List.nil_append, Expr.instantiateLevelParams]
  · rw [containerOwnPinsAtGo_nil_of_len hDlen 64 0] at hpsEq
    rw [hpsEq] at he
    exact nomatch he

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
    -- K.39 and K.45, the run's own (lane M7-2's §U.29 (s)/(ll)): the
    -- restored recursors' names are pairwise distinct, and no auxiliary
    -- name is one of them — what the provision loop's conses and
    -- `RestoreAgree.auxFresh` need, and what no freshness report at ONE
    -- environment can give (both families are `.str X (s ++ "_" ++
    -- toString i)`, so separating them needs `toString` injectivity)
    ConLeche.certOnly μ
      (decide ((cvRms.map (·.name) ++ cvRns.map (·.name)).Nodup)) = true →
    ConLeche.certOnly μ ((ConLeche.restoreTbl p st).auxNames.all fun n =>
      !((cvRms.map (·.name) ++ cvRns.map (·.name)).contains n)) = true →
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
    -, hgrp, hmn, hsc, hlv, hK32, hkinds, hauxApps, hrank, -, -, -, hpins₁, hctors, hrm, hrn, hndR,
    hdisj,
    hrulesM, hrulesN, htbl, hpinsOut, hcnt, hrecs, hrb, -, -⟩ := h
  -- the `-` after `hsrc` is K.31's `pinsDistinct` conjunct: named for the
  -- identities' discharge (`NestedPinsIdent`, lane L-B), not consumed here;
  -- `hmn` after `hgrp` is K.44's `nestedPinMentionOk`, which lane L-E's
  -- `ContainerModeled.nestMention` is discharged from at the block's own
  -- read-back (`nestedContainerModeled`);
  -- `hlv` after `hsc` is K.48's `pinsLevelsOk` — the pins' level
  -- arguments are the block's own — from which `nestedPinParams_of`
  -- discharges `ContainerModeled.pinParams` at the nested site;
  -- `hK32` after it is K.32's `nestedCopyTargetsOk`, carried down to
  -- `NestedPinsRun` for the same discharge's `ordF` arm (task #315 L-E,
  -- DESIGN §U.64) and not consumed here; `hauxApps` after `hkinds` is
  -- K.35's `nestedAuxAppsOk`, which the tail consumes, and `hrank` after
  -- it is K.37's `nestedPinRankOk` — the global entry theorem's induction
  -- measure, carried down to `NestedPinsRun` (task #315 L-E, DESIGN
  -- §U.55) — the `-` after THAT is K.40's `nestedPinParentOk`, the one
  -- after THAT K.41's `nestedPinRootPairOk` and the one after THAT K.42's
  -- second positivity run on the minted copies, none consumed on this
  -- path; then K.34's `blockReadBackOk` (`hrb`) — the route's own
  -- read-back, which the block this route stores needs and `mp.blocks`
  -- carries for the rest — and the LAST two `-` are K.47's
  -- `nestedOwnPinsOk` (the mimics' stored types ARE the recorded pins, at
  -- the route's own instantiation) and K.43's `blockOwnMimicsOk` (the
  -- walk's LENGTH), which `ContainerModeled.ownPins` reads at the nested
  -- site and nothing on this path does;
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
  replace hlv := ConLeche.certOnly_elim hlv hμ
  replace hK32 := ConLeche.certOnly_elim hK32 hμ
  replace hkinds := ConLeche.certOnly_elim hkinds hμ
  replace hrank := ConLeche.certOnly_elim hrank hμ
  replace hauxApps := ConLeche.certOnly_elim hauxApps hμ
  replace hrb := ConLeche.certOnly_elim hrb hμ
  have hPM : PinsModeled mp.base2 st.pins := pinsModeled_of_env mp.blocks hcont
  obtain ⟨fms, f₀, ctorsA', sortss, kinds, mp₁, ppsF, W, idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF,
    eissF, tssF, dsR, xFvsR, pinsS, mp₂, henv, O⟩ := hcore hμ mp.toEnvModelM hE p st b envAux stored
    ctorsR fmsA ctorsA hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux hstored hclosed hpinsAux
    hcaps hsrc hgrp hsc hK32 hkinds hrank hpins₁ hctors
  obtain ⟨mpOut, T⟩ := htail hμ mp.toEnvModelM hE p envOut st b envAux stored ctorsR cvRms cvRns
    rulesM rulesN fmsA ctorsA hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux hstored hclosed
    hpinsAux hcaps hsrc hgrp hkinds hauxApps hctors hrm hrn hndR hdisj hrulesM hrulesN htbl
    hpinsOut hcnt hrecs fms f₀
    ctorsA' sortss kinds mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR
    pinsS mp₂ henv O
  -- the lists' lengths, and the block's own reading
  have hslen : stored.length = b.k := (ConLeche.auxStoredAll_get hstored).1
  have hk0 : 0 < p.k := nested_kpos hfA helim
  have hkle : p.k ≤ b.k := by rw [O.bk]; omega
  have hclen : ctorsR.length = p.k := by
    rw [(ConLeche.mapM_except_inv hctors).1, List.length_take]
    omega
  -- the members' level parameters ARE the block's (K.48's Bool is stated
  -- at `p.lps`, `ContainerModeled.pinParams` at the member's own record):
  -- the read-back's members are the auxiliary block's formers
  -- (`consNestedFormers_take_eq`), whose level parameters are `b.lps`
  -- (`MutualFormersFacts.lps`), which `auxBlock` copies from `p.lps`
  have hlps : ∀ i, i < p.k → (stored.getD i default).cvTa.levelParams = p.lps := by
    intro i hik
    have hcv := (ConLeche.consNestedFormers_take_eq haux O.formers hstored p.k hkle).2
    have hsi : stored[i]? = some stored[i] := List.getElem?_eq_getElem (by omega)
    obtain ⟨f, hf, hcveq, -, -⟩ := hcv i _ hik hsi
    rw [List.getD_eq_getElem?_getD, hsi, Option.getD_some, hcveq, O.facts.lps i f hf,
      (ConLeche.auxBlock_fields hb).2.1]
  have hcm := nestedContainerModeled hcaps hcont hk0 hmn haux hstored hctors O T
    (nestedPinParams_of hcaps hcont hlv hPM hlps haux hstored O)
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
  -- the pins' groups at the CONSTRUCTORS' environment's reading: the
  -- core's own keyed groups (`NestedStageFacts.groupsAt`, at the
  -- pre-block reading) carried across by `conts`, which says the two
  -- readings are ONE group (task #315 M7-3 session 12 — the field the
  -- tail used to supply)
  have hGroups : ∀ q, q < pinsS.length → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env))
        ((nestedBlockModel (V := V) p b fms f₀ ctorsA' kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt q).J = some ci →
      ∃ q₀ kJ i, q = q₀ + i ∧ i < kJ ∧
        NestedPinGroup (V := V) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA')
          (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF)
          (esF := esF) (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF)
          (tssF := tssF) (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS)
          mp₂.base2 q₀ kJ (blockOf mp.base2 ci) := by
    intro q hq ci hci
    obtain ⟨ci₀, h₂, -, hEnv⟩ := T.conts q hq
    obtain rfl : ci = ci₀ := Option.some.inj (hci.symm.trans h₂)
    exact O.stage.groupsAt q hq ci hEnv
  have hBreps : ∀ q, q < pinsS.length → ∀ ci : ContainerInfo,
      ConLeche.containerInfo? (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env))
        ((nestedBlockModel (V := V) p b fms f₀ ctorsA' kinds env ppsF W idxF dsF esF srcsF fvsPF
          xrestF eissF tssF ctorsR dsR xFvsR pinsS).pinAt q).J = some ci →
      IsBlockModels mp₂.base2 (blockOf mp.base2 ci) := by
    intro q hq ci hci
    obtain ⟨q₀, kJ, i, -, -, G⟩ := hGroups q hq ci hci
    exact G.reps
  have hShapes := (nestedPinShapes_of (B := blockOf mp.base2) mp₂.base2
      (fun q hq ci hci => by
        obtain ⟨q₀, kJ, i, hqe, hi, G⟩ := hGroups q hq ci hci
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
    hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32 hkinds hrank hpins₁ hctors
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
    hfresh hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32 hkinds hrank hpins₁ hnd h3
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
