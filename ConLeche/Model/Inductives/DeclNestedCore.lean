module

public import ConLeche.Semantics.Inductives.DeclNested
public import ConLeche.Model.Inductives.BlockRecWD
public import ConLeche.Model.Annot.EnvModelM
public section

/-!
# `declNested_of` — the nested assembly's run-level consumer (task #315, M6 s3)

**THE run-level consumer of the nested half**: the model of the
pre-block environment survives the nested install's run
(`DeclNestedRun`, `Semantics/Inductives/DeclNested.lean`), given two
named facts that M6/M7 discharge — `declBlock`'s pattern (DESIGN §U.6)
at the nested block:

* `NestedCoreModeled` (M6): the run's stages through the restored
  constructors keep the model and leave THE BLOCK MODEL of the nested
  block at the constructors' environment — the composed block model
  (`BlockModel.ofNested`, `BlockComposed.lean`) at every member
  (`IsBlockModels`), with the members, the constructors and the
  pins' containers typed (`FormersTyped`, `CtorsTyped`, `PinsTyped`);
* `NestedTailModeled` (M7): from there the restored recursors (at
  `k + nPins` motives), their rules, the projection tables and the
  two post-checks keep the model to the post-block environment.

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

/-- **Every stored inductive carries its block's model** at the model
`m`: it is member `mm` of a block model `d` at which `IsBlockModel`
holds at every member, the members and constructors are typed, and
the injections are the tagged towers at the constructors' member-local
positions.  The shape of the `EnvModelM` field to come (DESIGN §U.13
(f) 1); a premise on the branch until then. -/
@[expose] def EnvBlockModels {env : Env} (m : EnvModel V env) : Prop :=
  ∀ (J : Name) (cv : ConstantVal) (caps : IndCaps), env.find? J = some (.indInfo cv caps) →
    ∃ (d : BlockModel V) (mm : Nat) (cvR : ConstantVal) (mI rP : Nat) (rules : List RecRule),
      IsBlockModel m J cv cvR mI rP rules d mm ∧ IsBlockModels m d ∧
      (∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ) ∧
      ∀ (ψ : Name → Nat) (mm' j : Nat) (fs : List V),
        d.inj ψ mm' j fs = injW (d.w ψ) j (mkTower (fs ++ [pt]))

/-- **The pins' containers carry their blocks' models** — `EnvBlockModels`
read at the elimination's pins (`ElimState.pins`): the premise
`pinLeaf`'s assembly consumes (DESIGN §U.14 (e) 1). -/
@[expose] def PinsModeled {env : Env} (m : EnvModel V env) (pins : List NestedPin) : Prop :=
  ∀ q ∈ pins, ∃ (d : BlockModel V) (mm : Nat) (cvT cvR : ConstantVal) (mI rP : Nat)
      (rules : List RecRule),
    IsBlockModel m q.container cvT cvR mI rP rules d mm ∧ IsBlockModels m d ∧
    (∀ ψ : Name → Nat, FormersTyped m d ψ ∧ CtorsTyped m d ψ) ∧
    ∀ (ψ : Name → Nat) (mm' j : Nat) (fs : List V),
      d.inj ψ mm' j fs = injW (d.w ψ) j (mkTower (fs ++ [pt]))

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
are** (`nestedContainersOk` finds every pin's container). -/
theorem pinsModeled_of_env {env : Env} {m : EnvModel V env} (hm : EnvBlockModels m)
    {pins : List NestedPin} (hok : ConLeche.nestedContainersOk env pins = true) :
    PinsModeled m pins := by
  intro q hq
  unfold ConLeche.nestedContainersOk at hok
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  have hq' := hok.2 q hq
  cases hci : ConLeche.containerInfo? env q.container with
  | none => rw [hci] at hq'; exact nomatch hq'
  | some ci =>
    obtain ⟨cv, caps, hfind⟩ := containerInfo?_found hci
    obtain ⟨d, mm, cvR, mI, rP, rules, hrep, hreps, htyped, hinj⟩ := hm _ _ _ hfind
    exact ⟨d, mm, cv, cvR, mI, rP, rules, hrep, hreps, htyped, hinj⟩

/-! ## The block model of a nested run -/

/-- **The block model is the run's block**: its arities, names and
constructors are the recogniser's and the restore's, its pins the
elimination's (the container, its level arguments and its components
at the block's parameter openers).  Grows at its consumer (M7). -/
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

/-! ## The named facts -/

/-- **The nested run's stages through the restored constructors keep
the model and leave the block model at the constructors'
environment** — `declNested_of`'s first named fact (M6): from a model
of the pre-block environment carrying the containers' block models
(`PinsModeled`) and the run's conjuncts through `restoreCtors`, a
model of the environment holding the restored formers and
constructors, agreeing with the pre-block model off the block, at
which the nested block's block model holds at every member
(`IsBlockModels`, the composed model `BlockModel.ofNested`), with the
members, the constructors and the pins' containers typed.
Consumer: `declNested_of`. -/
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
    ConLeche.nestedPinKindsOk p b st stored = true →
    (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR →
    ∃ mp₂ : EnvModelM V μ
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env)),
      (∀ n, n ∉ p.memberNames ++ p.ctors.map (·.cv.name) →
        ∀ ψ : Name → Nat, mp₂.base2.acval n ψ = mp.base2.acval n ψ) ∧
      ∃ d : BlockModel V, NestedBlockModelOf env p st ctorsR d ∧ IsBlockModels mp₂.base2 d ∧
        ∀ ψ : Name → Nat,
          FormersTyped mp₂.base2 d ψ ∧ CtorsTyped mp₂.base2 d ψ ∧ PinsTyped mp₂.base2 d ψ

/-- **The tail keeps the model**: at a model of the constructors'
environment carrying the nested block's block model, the run's
remaining stages — the restored recursor types at `k + nPins` motives,
their rules at the rule-less provision, the projection tables and the
two post-checks — cons a model of the post-block environment —
`declNested_of`'s second named fact (M7).  Consumer: `declNested_of`. -/
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
    ConLeche.nestedPinKindsOk p b st stored = true →
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
    ∀ (mp₂ : EnvModelM V μ
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env)))
      (d : BlockModel V),
      (∀ n, n ∉ p.memberNames ++ p.ctors.map (·.cv.name) →
        ∀ ψ : Name → Nat, mp₂.base2.acval n ψ = mp.base2.acval n ψ) →
      NestedBlockModelOf env p st ctorsR d → IsBlockModels mp₂.base2 d →
      (∀ ψ : Name → Nat,
        FormersTyped mp₂.base2 d ψ ∧ CtorsTyped mp₂.base2 d ψ ∧ PinsTyped mp₂.base2 d ψ) →
      Nonempty (EnvModelM V μ envOut)

/-! ## The consumer -/

/-- **The model survives a nested block** (the nested half's run-level
consumer): the run's stages through the restored constructors keep the
model and leave the block model (`NestedCoreModeled`), the tail keeps
it from there (`NestedTailModeled`); the containers' block models are
the premise `EnvBlockModels` at the pre-block model. -/
theorem declNested_of (hμ : μ.verifiedChecks = true) {F : Nat} {env envOut : Env}
    {p : NestedParts} (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hpins : EnvBlockModels mp.base2)
    (hcore : NestedCoreModeled V μ F) (htail : NestedTailModeled V μ F)
    (h : ConLeche.Semantics.DeclNestedRun μ F env p envOut) :
    Nonempty (EnvModelM V μ envOut) := by
  obtain ⟨h0, h1, st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, fmsA, ctorsA,
    hfA, hcA, helim, hcount, hfresh, hcont, hb, haux, hstored, hclosed, hpinsAux, hcaps, hkinds,
    hctors, hrm, hrn, hrulesM, hrulesN, htbl, hpinsOut, hcnt, hrecs⟩ := h
  have hPM : PinsModeled mp.base2 st.pins := pinsModeled_of_env hpins hcont
  obtain ⟨mp₂, hag, d, hd, hreps, htyped⟩ := hcore hμ mp hE p st b envAux stored ctorsR fmsA ctorsA
    hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux hstored hclosed hpinsAux hcaps hkinds hctors
  exact htail hμ mp hE p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA ctorsA
    hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux hstored hclosed hpinsAux hcaps hkinds hctors
    hrm hrn hrulesM hrulesN htbl hpinsOut hcnt hrecs mp₂ d hag hd hreps htyped

end ConLeche.Model
