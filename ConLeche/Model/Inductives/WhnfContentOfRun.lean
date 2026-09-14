module

public import ConLeche.Model.Inductives.CopyWalkFactsRunAssembly
public import ConLeche.Model.Inductives.NestedCtorRead
public import ConLeche.Model.Inductives.NestedFormers
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.NestedLeaves
import ConLeche.Verify.Inductives.NestedFacts

public section

/-!
# `WhnfContent` at the run (task #279 M-D′ D2, DESIGN §M.52)

The `whnf` arm's content — the last premise of `copyCtorsRead_of_run'`
— assembled at the formers' model `mp₁` of `env₁ = consNestedFormers
(stored.take p.k) env` from the run's own facts, in the order DESIGN
§M.49 laid out:

* **`paramsRead_of_run`** — the head former's parameter openers read
  at `mp₁` as the datum's parameter entries `d.params ψ`, and those
  entries are graded: the stored former's reading at the scratch model
  (`IndRep.former`) transferred DOWN whole (the checked former resolves
  before the block, `FormerFront.resolve`) and peeled at the openers;
* **`pinsData_of_run`** — every pin's data at `mp₁`: its container's
  stored constant (at `env`, hence at `env₁`), its levels, the
  container's leaf at the pin's level substitution agreeing with the
  auxiliary carrier at the pin's assignment, and its components'
  readings transferred down under the pins' blind mentions (K.15,
  `PinsMentionReal`), the pins' `NoProjAt` at fresh names (task #309)
  and the pins' LITERAL SUPPORT at `env₁` (task #311's
  `pinsLits_of_run`: a `litsResolve` invariant through the
  elimination, `NestedLeaves.lean`'s `LeafInv` style);
* **`whnfContent_of_run`** — per pin, container constructor and
  container-ordinary field the walk `whnf`'d: the group exclusion is
  `CopyCtorSyn.excl`, and the reading conjunct is `whnfContent_field`
  at the container's instantiated field read at `mp₁` (the stored
  constructor's reading transferred down and peeled at the pin,
  `ctor_peel_of_read` + `ctorInst_fields`) and the restored stored
  field's reading (`restoredFieldsRead_of_stored`);
* **`copyCtorsRead_of_run''`** — `copyCtorsRead_of_run'` with
  `WhnfContent` DISCHARGED: `CopyCtorsRead` off `DeclNestedRun` under
  `ContainersRep` alone.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps RecRule MutualBlock
  ContainerMember ContainerInfo AuxType AuxStored NestedPin ElimState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The head former's parameter openers, read at the formers' model -/

/-- **The parameter openers' readings and grading at `mp₁`**: the first
member's stored former is the state's first type (`nestedCopyFormerType_eq`),
whose openers are the ledger's `params`; its reading at the scratch
model (`IndRep.former`) transfers down whole — the checked former
resolves before the block — and peels at the openers to the datum's
parameter entries. -/
theorem paramsRead_of_run {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat}
    (hb : ConLeche.auxBlock p st = some b)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hfreshRec : ∀ t, t < b.k → env.find? (b.recName t) = none)
    (hreps : MutualBlockReps mpAux.base2 b d)
    {pbs : List (Expr × ConLeche.BinderMeta)}
    (hhead : ∃ (t₀ : AuxType) (body body₀ : Expr), st.types[0]? = some t₀ ∧
      ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body) ∧
      t₀.type.stripPis p.nP = some (pbs, body₀) ∧ pbs.length = p.nP ∧ t₀.type.hasFvar = false)
    {env₁ : Env} (mp₁ : EnvModelM V μ env₁) (hF : FindPreserved env₁ envAux)
    (hag : ∀ n : Name, (env₁.find? n).isSome = true → mp₁.base2.acval n = mpAux.base2.acval n)
    (hTbl : ∀ (sn : Name) (i : Nat), env₁.findProj? sn i = none →
      (envAux.findProj? sn i).isSome = true → env.find? sn = none)
    (hup : ∀ n, (env.find? n).isSome = true → (env₁.find? n).isSome = true) :
    (∀ (k : Nat) (y : Expr), params[k]? = some y →
      denoteMeta mp₁.base2.acval env₁ ψ k y.fvarTypeD = some ((d.params ψ).getD k default)) ∧
    (d.params ψ).length = d.nP ∧
    (∀ (k : Nat), k < d.nP → ∀ ρ : Nat → V, Sat V (d.params ψ).reverse ρ →
      WellDenotedV V (fun j => ρ (j + (d.nP - 1 - k) + 1)) ((d.params ψ).getD k default)) := by
  obtain ⟨t₀, body, body₀, ht₀, hop₀, -, -, -⟩ := hhead
  have hrun : DeclMutualCoreRun μ F env b none true envAux := declMutualCoreRun_of hcore
  obtain ⟨fms, hformers, hkF, hposF, hstoredF, -⟩ := auxFormers_stored hrun hfreshRec
  obtain ⟨-, hkb, -, hnPb, -, -, hnames, hall⟩ := hreps
  have hnP : d.nP = p.nP := by rw [hnPb, (ConLeche.auxBlock_inv hb).1]
  have hk0 : 0 < b.k := by
    rw [ConLeche.auxBlock_k hb]; exact (List.getElem?_eq_some_iff.mp ht₀).1
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, hfT₀, -, -, -, hrep₀⟩ := hall 0 hk0
  -- the stored former's type is the state's first type
  obtain ⟨env₁', fms', f, hformers', -, hf, hfty⟩ :=
    ConLeche.nestedCopyFormerType_eq hb hcore 0 t₀ ht₀
  rw [hformers] at hformers'
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj hformers')
  obtain ⟨cv, bs, hl, hff, -⟩ := hposF 0 f hf
  obtain ⟨nIdx, -, hform⟩ := (ConLeche.auxBlock_inv hb).2.2.2.2.2.1 0 t₀ ht₀
  rw [hform] at hl
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hl)
  have hname : d.memberName 0 = t₀.name := by rw [hnames 0 hk0, memberNames_getD hform]
  have hn' : f.cvTa.name = d.memberName 0 := by rw [hname]; exact hff.name
  have hfindT := hstoredF f (List.mem_of_getElem? hf)
  rw [hn'] at hfindT
  obtain ⟨rfl, -⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT₀.symm.trans hfindT))
  have hFD₀ : FormerData mpAux.base2 f.cvTa (d.nP + d.nIdxAt 0) s₀ (d.ppsM 0) (d.lvlsM 0) :=
    hrep₀.former
  -- the reading at the scratch model, transferred down and peeled
  have hread₁ : denoteMeta mp₁.base2.acval env₁ ψ 0 t₀.type
      = some (mkPisAV (d.ppsM 0 ψ) (.sort (s₀.eval ψ))) := by
    rw [← hfty]
    exact down_of_resolve mp₁ mpAux hF hag hTbl hup hff.resolve (hFD₀.read ψ)
  have hle : p.nP ≤ (d.ppsM 0 ψ).length := by rw [hFD₀.len ψ]; omega
  obtain ⟨pps, b', hst, -, -, hbind⟩ := denoteMeta_openPis p.nP hop₀ hread₁
  rw [stripPisAV_mkPisAV_take p.nP _ _ hle] at hst
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
  have hlenP : (d.params ψ).length = d.nP := by
    unfold IndRepData.params
    rw [List.length_map, List.length_take, hFD₀.len ψ]
    omega
  refine ⟨fun k y hy => ?_, hlenP, ?_⟩
  · obtain ⟨q, hq, -, hqr⟩ := hbind k y hy
    rw [Nat.zero_add] at hqr
    rw [hqr]
    unfold IndRepData.params
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hnP, hq]
    rfl
  · have h := params_graded_of_formerData hFD₀ (nP := d.nP) (ψ := ψ) (Nat.le_add_right _ _)
    exact h

/-! ## The pins' data at the formers' model -/

/-- **Every pin's data at `mp₁`** (what `restoredFieldsRead_of_stored`'s
`hpinAll` asks): the pin's shape, its container's stored constant at
`env₁` (the container is stored before the block), the container's
leaf at the pin's level substitution agreeing with the auxiliary
carrier at the pin's assignment (`PinRunFactsAt`'s last clause through
the agreement on `env₁`'s names), the components' scope, and the
components' readings transferred down: their blind mentions are
pre-block names and real members (K.15), their projection nodes sit at
no fresh name's slot (task #309), and their literals' support is
`hpinsLits` — task #311's `pinsLits_of_run`, at the run. -/
theorem pinsData_of_run {μ : CheckMode} {F : Nat} {env envAux : Env}
    {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock} {params : List Expr}
    {pbs : List (Expr × ConLeche.BinderMeta)} {stored : List AuxStored}
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hb : ConLeche.auxBlock p st = some b) (hlenSt : st.types.length = p.k + st.pins.length)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hfreshRec : ∀ t, t < b.k → env.find? (b.recName t) = none)
    (hK20 : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (hmo : PinsMentionReal env st params p.k)
    (hpinsNP : ∀ q ∈ st.pins, ∀ (T : Name) (i : Nat), env.find? T = none →
      Expr.NoProjAt T i q.pin)
    (hreps : MutualBlockReps mpAux.base2 b d)
    (hpins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    -- the pins' literal support at the formers' environment (task #311)
    (hpinsLits : ∀ q ∈ st.pins, ∀ a ∈ q.pin.getAppArgs,
      litsResolve (ConLeche.consNestedFormers (stored.take p.k) env) a = true)
    (mp₁ : EnvModelM V μ (ConLeche.consNestedFormers (stored.take p.k) env))
    (hF : FindPreserved (ConLeche.consNestedFormers (stored.take p.k) env) envAux)
    (hag : ∀ n : Name, ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true →
      mp₁.base2.acval n = mpAux.base2.acval n)
    (hTbl : ∀ (sn : Name) (i : Nat),
      (ConLeche.consNestedFormers (stored.take p.k) env).findProj? sn i = none →
      (envAux.findProj? sn i).isSome = true → env.find? sn = none)
    (hrealStored : ∀ t, t < p.k → ∃ (cv : ConstantVal) (caps : IndCaps),
      (ConLeche.consNestedFormers (stored.take p.k) env).find? (d.memberName t)
        = some (.indInfo cv caps) ∧ cv.levelParams = b.lps) :
    ∀ (jq : Nat) (q : NestedPin), st.pins[jq]? = some q →
      ∃ (J'' : Name) (lvls'' : List Level) (Ds'' : List Expr) (ci : ConstantInfo),
        q.pin = Expr.mkAppN (.const J'' lvls'') Ds'' ∧ (cd jq).dJ.memberName (cd jq).mm = J'' ∧
        (ConLeche.consNestedFormers (stored.take p.k) env).find? J'' = some ci ∧
        lvls''.length = ci.toConstantVal.levelParams.length ∧
        mp₁.base2.acval J'' (Level.substFn ψ ci.toConstantVal.levelParams lvls'')
          = mpAux.base2.acval J'' ((cd jq).ψ') ∧
        (∀ a ∈ Ds'', Expr.WScoped d.nP a) ∧
        DenoteMetaSpine mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ d.nP
          Ds'' ((cd jq).DsA) := by
  intro jq q hq
  have hjq : jq < st.pins.length := (List.getElem?_eq_some_iff.mp hq).1
  have hqmem : q ∈ st.pins := List.mem_of_getElem? hq
  obtain ⟨-, hkb, -, hnPb, -, -, hnames, -⟩ := hreps
  have hnP : d.nP = p.nP := by rw [hnPb, (ConLeche.auxBlock_inv hb).1]
  have hup : ∀ n, (env.find? n).isSome = true →
      ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true := by
    intro n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    rw [(consNestedFormers_freshExt hK20).find?_some hc]; rfl
  obtain ⟨-, -, -, -, -, hfreshAux⟩ := auxFormers_stored (declMutualCoreRun_of hcore) hfreshRec
  obtain ⟨⟨-, -, q', I, ci, J, lvls, Ds, cvTJ, capsJ, hq', hci, hJ, hJn, hmn, -, -, hqp, -, hfJ, -,
    hDsW, hsp, -, -, hlpsAll, hlvlsLen, -, hmemNames⟩, -⟩ := hpins jq hjq
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  -- the container is stored before the block, and its slot is the scratch one's
  obtain ⟨⟨cvC, capsC, hfC, -, -⟩, -⟩ := ConLeche.containerInfo?_stored hci J (List.mem_of_getElem? hJ)
  rw [hJn] at hfC
  have hfAux := hfreshAux.find?_some hfC
  obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfAux.symm.trans hfJ))
  have hf₁ : (ConLeche.consNestedFormers (stored.take p.k) env).find? q.container
      = some (.indInfo cvC capsC) := (consNestedFormers_freshExt hK20).find?_some hfC
  obtain ⟨hnameJ, hacvJ⟩ := hmemNames _ J hJ
  refine ⟨q.container, lvls, Ds, .indInfo cvC capsC, hqp, hmn, hf₁, hlvlsLen, ?_,
    fun a ha => by rw [hnP]; exact (hDsW a ha).1, ?_⟩
  · rw [hag _ (by rw [hf₁]; rfl), ← hJn, hacvJ, hlpsAll _ J hJ]
    rfl
  · -- the components' readings, transferred down
    have hargs : ∀ a ∈ Ds, a ∈ q.pin.getAppArgs := by
      intro a ha
      rw [hqp, Expr.getAppArgs_mkAppN]
      simpa [Expr.getAppArgs] using ha
    have hsp' : DenoteMetaSpine mpAux.base2.acval envAux ψ d.nP Ds (cd jq).DsA := by
      rw [hnP]; exact hsp
    refine DenoteMetaSpine.acval_congr (fun n hn => (hag n hn).symm)
      (DenoteMetaSpine.down_blind hF ?_ ?_ ?_ hsp')
    · intro a ha T hT
      have hokT := (hmo.2 q hqmem).getAppArgs a (hargs a ha) T
        (Expr.mentionsConst_of_mentionsConstE a hT)
      rcases hokT with h | h
      · exact hup T h
      · obtain ⟨t, ht⟩ := List.getElem?_of_mem h
        have htlt : t < p.k := by
          have := (List.getElem?_eq_some_iff.mp ht).1
          rw [List.length_take] at this; omega
        rw [List.getElem?_take_of_lt htlt, List.getElem?_map] at ht
        obtain ⟨ty, hty, rfl⟩ := Option.map_eq_some_iff.mp ht
        have htb : t < b.k := by rw [ConLeche.auxBlock_k hb, hlenSt]; omega
        rw [← memberName_eq_type hb hnames hty htb]
        obtain ⟨cv, caps, hfind, -⟩ := hrealStored t htlt
        rw [hfind]; rfl
    · exact fun a ha => hpinsLits q hqmem a (hargs a ha)
    · intro a ha sn i h1 h2
      exact Expr.noProjAt_blank _
        (Expr.NoProjAt.getAppArgs (hpinsNP q hqmem sn i (hTbl sn i h1 h2)) a (hargs a ha))

/-! ## The `whnf` arm's content, at the run -/

set_option maxHeartbeats 1600000 in
/-- **`WhnfContent` from the run** (M-D′ D2's assembly): at every pin,
container constructor and container-ordinary field the walk `whnf`'d,
the group exclusion is the exported `CopyCtorSyn.excl`, and the reading
conjunct is `whnfContent_field` — the head former's openers read as
the datum's parameters (`paramsRead_of_run`), the container's
instantiated field read at `mp₁` by transferring the container's stored
constructor's reading down and peeling it at the pin
(`ctor_peel_of_read`, `ctorInst_fields`), the container's field graded
(`gradeC_of_okTy`), and the restored stored field read by kind
(`restoredFieldsRead_of_stored` at the pins' data, `pinsData_of_run`).
The pins' literal support at `env₁` (`hpinsLits`) is task #311's, read
off the run by `pinsLits_of_run`. -/
theorem whnfContent_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock}
    {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)} {stored : List AuxStored}
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hb : ConLeche.auxBlock p st = some b) (hlenSt : st.types.length = p.k + st.pins.length)
    (hwf : EnvWF env)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hfreshRec : ∀ t, t < b.k → env.find? (b.recName t) = none)
    (hK20 : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (hparamsLen : params.length = p.nP)
    (hmo : PinsMentionReal env st params p.k)
    (hhead : ∃ (t₀ : AuxType) (body body₀ : Expr), st.types[0]? = some t₀ ∧
      ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body) ∧
      t₀.type.stripPis p.nP = some (pbs, body₀) ∧ pbs.length = p.nP ∧ t₀.type.hasFvar = false)
    (hpinsNP : ∀ q ∈ st.pins, ∀ (T : Name) (i : Nat), env.find? T = none →
      Expr.NoProjAt T i q.pin)
    (hreps : MutualBlockReps mpAux.base2 b d)
    (hpins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hwalk : CopyWalkFacts μ F env (ConLeche.consNestedFormers (stored.take p.k) env) p st
      (ConLeche.restoreTbl p st) params d cd)
    -- the pins' literal support at the formers' environment (task #311)
    (hpinsLits : ∀ q ∈ st.pins, ∀ a ∈ q.pin.getAppArgs,
      litsResolve (ConLeche.consNestedFormers (stored.take p.k) env) a = true)
    (mp₁ : EnvModelM V μ (ConLeche.consNestedFormers (stored.take p.k) env))
    (hF : FindPreserved (ConLeche.consNestedFormers (stored.take p.k) env) envAux)
    (hag : ∀ n : Name, ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true →
      mp₁.base2.acval n = mpAux.base2.acval n)
    (hTbl : ∀ (sn : Name) (i : Nat),
      (ConLeche.consNestedFormers (stored.take p.k) env).findProj? sn i = none →
      (envAux.findProj? sn i).isSome = true → env.find? sn = none)
    (hrealStored : ∀ t, t < p.k → ∃ (cv : ConstantVal) (caps : IndCaps),
      (ConLeche.consNestedFormers (stored.take p.k) env).find? (d.memberName t)
        = some (.indInfo cv caps) ∧ cv.levelParams = b.lps) :
    WhnfContent F (ConLeche.consNestedFormers (stored.take p.k) env) p st
      (ConLeche.restoreTbl p st) params mpAux d ψ cd := by
  intro j' hj' q lvls Ds hq hqp Jc cAJ hJc cI hcI xFvsC xrestC hopen i x xC hx hxC hnr hW
  have hreps' := hreps
  obtain ⟨-, hkb, -, hnPb, -, hviewAll, hnames, hall⟩ := hreps
  have hnP : d.nP = p.nP := by rw [hnPb, (ConLeche.auxBlock_inv hb).1]
  have hup : ∀ n, (env.find? n).isSome = true →
      ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true := by
    intro n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    rw [(consNestedFormers_freshExt hK20).find?_some hc]; rfl
  -- ## the run-level readings at the formers' model
  obtain ⟨hreadP, hpsLen, hokP⟩ :=
    paramsRead_of_run hb hcore hfreshRec hreps' hhead mp₁ hF hag hTbl hup (ψ := ψ)
  have hpinAll := pinsData_of_run hb hlenSt hcore hfreshRec hK20 hmo hpinsNP hreps' hpins hpinsLits
    mp₁ hF hag hTbl hrealStored
  -- ## the walk's export at this constructor
  obtain ⟨xFvsC', xrestC', hopen', -, cA, hsyn⟩ := hwalk j' hj' q lvls Ds hq hqp Jc cAJ hJc cI hcI
  rw [hopen] at hopen'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hopen')
  -- ## the pin's run facts
  obtain ⟨⟨pf, -, q₀, I, ci, J, lvls₀, Ds₀, cvTJ, capsJ, hq₀, hci, hJ, hJn, hmn, hlenM, -, hqp₀,
      -, hfJ, -, hDsW, hsp, hcat, -, hlpsAll, -, hagLvl, hmemNames⟩, -⟩ := hpins j' hj'
  obtain rfl : q = q₀ := Option.some.inj (hq.symm.trans hq₀)
  obtain ⟨rfl, rfl⟩ : lvls = lvls₀ ∧ Ds = Ds₀ := by
    rw [hqp₀] at hqp
    have h1 := congrArg Expr.getAppFn hqp
    have h2 := congrArg Expr.getAppArgs hqp
    rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at h1
    rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at h2
    simp only [Expr.getAppFn, Expr.getAppArgs, List.nil_append, Expr.const.injEq] at h1 h2
    exact ⟨h1.2.symm, h2.symm⟩
  obtain ⟨Jm, c, hJm, hcl, -, htypeC, -⟩ := hcat.fwd Jc cAJ hJc
  have hmemsJ : (cd j').dJ.mems Jc < (cd j').dJ.k := by
    rw [← hlenM]; exact (List.getElem?_eq_some_iff.mp hJm).1
  have hk0 : 0 < d.k := by have := pf.kA _ hmemsJ; omega
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, hsv₀, hrep₀⟩ :=
    hall 0 (by rw [← hkb]; exact hk0)
  -- ## the copy's constructor at the auxiliary datum
  have hDfacts := FixCtorFactsAt.congr_sort hsv₀ (hrep₀.ctors _ cA hsyn.get)
  have hD := hDfacts.2.2
  have hview := hviewAll (auxOfsOf st p.k cd j' Jc)
  -- ## the container's constructor at its own datum
  obtain ⟨cvTm, cvRm, mIm, rPm, rulesm, hrepm⟩ := pf.repAll _ hmemsJ
  have hDJfacts := hrepm.ctors Jc cAJ hJc
  have hDJ := hDJfacts.2.2
  have hgrpOk := pf.grp
  have hfindM : envAux.find? ((cd j').dJ.memberName (cd j').mm) = some (.indInfo cvTJ capsJ) := by
    rw [hmn]; exact hfJ
  have hlpsJ : cvTJ.levelParams = cvTm.levelParams := hrepm.membersLps _ pf.mm cvTJ capsJ hfindM
  have hlpsC : cAJ.1.levelParams = cvTm.levelParams := hDJfacts.2.1
  have hJmLps : Jm.lps = cvTm.levelParams := by rw [hlpsAll _ Jm hJm, hlpsJ]
  have hagJ : ∀ z ∈ cvTm.levelParams, (cd j').ψ' z = Level.substFn ψ cvTm.levelParams lvls z := by
    rw [← hlpsJ]; exact hagLvl
  have hacvJ : mpAux.base2.acval ((cd j').dJ.memberName ((cd j').dJ.mems Jc)) (cd j').ψ'
      = mpAux.base2.acval ((cd j').dJ.memberName ((cd j').dJ.mems Jc))
          (Level.substFn ψ cvTm.levelParams lvls) := by
    obtain ⟨hnm, hac⟩ := hmemNames _ Jm hJm
    rw [hnm, hac, hJmLps]
  have hcI' : Expr.instPis (cAJ.1.type.instantiateLevelParams cvTm.levelParams lvls) Ds
      = some cI := by rw [← hlpsC]; exact hcI
  -- ## the container's stored constructor: closed and resolving before the block
  obtain ⟨-, hctorsC⟩ := ConLeche.containerInfo?_stored hci Jm (List.mem_of_getElem? hJm)
  obtain ⟨cvc, nPc, nFc, hfc, hctyEq⟩ := hctorsC c (List.mem_of_getElem? hcl)
  have hcWF := hwf _ (List.mem_of_find?_eq_some hfc)
  have hJnf : cAJ.1.type.hasFvar = false := by
    rw [htypeC]
    exact (ConLeche.containersClosed_of_wf hwf _ ci hci Jm (List.mem_of_getElem? hJm)).2 c
      (List.mem_of_getElem? hcl)
  have hcTyB : cAJ.1.type.looseBVarsBounded 0 = true := by
    rw [htypeC, hctyEq]; exact hcWF.2.2.2.1
  have hcRes : cAJ.1.type.constsResolve env = true := by
    rw [htypeC, hctyEq]; exact hcWF.2.2.1
  -- ## the container's constructor, read at the formers' model and peeled at the pin
  have hDsLenE : Ds.length = (cd j').dJ.nP := by rw [DenoteMetaSpine.length hsp, pf.len]
  have hagree : ∀ z ∈ cAJ.1.levelParams,
      Level.substFn ψ cvTm.levelParams lvls z = (cd j').ψ' z := by
    rw [hlpsC]; exact fun z hz => (hagJ z hz).symm
  obtain ⟨hds, hEs⟩ := hDJ.params _ _ hagree
  have hreadJ : denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env)
      (Level.substFn ψ cvTm.levelParams lvls) 0 cAJ.1.type
      = some (mkPisAV ((cd j').dJ.dsF Jc (cd j').ψ')
          (ctorBodyAVI mpAux.base2 ((cd j').dJ.memberName ((cd j').dJ.mems Jc)) (cd j').dJ.nP cAJ.2
            (cd j').ψ' ((cd j').dJ.esF Jc (cd j').ψ'))) := by
    have h := hDJ.read (Level.substFn ψ cvTm.levelParams lvls)
    rw [hds, hEs] at h
    unfold ctorBodyAVI at h ⊢
    rw [← hacvJ] at h
    exact down_of_resolve mp₁ mpAux hF hag hTbl hup hcRes h
  obtain ⟨J'', lvls'', Ds'', ci'', hqp'', -, -, -, -, -, hsp₁⟩ := hpinAll j' q hq
  obtain ⟨rfl, rfl⟩ : lvls = lvls'' ∧ Ds = Ds'' := by
    rw [hqp₀] at hqp''
    have h1 := congrArg Expr.getAppFn hqp''
    have h2 := congrArg Expr.getAppArgs hqp''
    rw [Expr.getAppFn_mkAppN, Expr.getAppFn_mkAppN] at h1
    rw [Expr.getAppArgs_mkAppN, Expr.getAppArgs_mkAppN] at h2
    simp only [Expr.getAppFn, Expr.getAppArgs, List.nil_append, Expr.const.injEq] at h1 h2
    exact ⟨h1.2, h2⟩
  have hlenDs := hDJ.len (cd j').ψ'
  have hpeel := ctor_peel_of_read mp₁ hJnf hcTyB (by rw [hlenDs]; omega) hreadJ hDsLenE
    (fun a ha => ⟨by rw [hnP]; exact (hDsW a ha).1, (hDsW a ha).2⟩) hsp₁ hcI'
  have hΓ : (((cd j').dJ.dsF Jc (cd j').ψ').drop (cd j').dJ.nP).length = cAJ.2 := by
    rw [List.length_drop, hlenDs]; omega
  obtain ⟨hreadC₀, -⟩ := ctorInst_fields mp₁ pf.len hΓ hpeel hopen
  have hdropGetD : ∀ i : Nat,
      ((((cd j').dJ.dsF Jc (cd j').ψ').drop (cd j').dJ.nP).getD i default).2.2
        = (((cd j').dJ.dsF Jc (cd j').ψ').getD ((cd j').dJ.nP + i) default).2.2 := by
    intro i
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  have hreadC : ∀ (k : Nat) (yC : Expr), k ≤ i → xFvsC[k]? = some yC →
      denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ (d.nP + k)
          yC.fvarTypeD
        = some (ConLeche.Model.AnnotTerm.instSeq (cd j').DsA ((cd j').dJ.nP - 1 + k)
            (((cd j').dJ.dsF Jc (cd j').ψ').getD ((cd j').dJ.nP + k) default).2.2) := by
    intro k yC _ hyC
    rw [← hdropGetD k]
    exact hreadC₀ k yC hyC
  -- ## the container's field, graded at the record's frames
  have hgradeC := gradeC_of_okTy mpAux hDJ.toCtorDataI (hgrpOk _ pf.mm).ff (hgrpOk _ pf.mm).ls
    (hgrpOk _ pf.mm).pin (hgrpOk _ pf.mm).pIffM (hrepm.paramsIff Jc cAJ hJc (cd j').ψ')
  have hi : i < cAJ.2 := by
    rw [← openPisAtFvars_length _ hopen]; exact (List.getElem?_eq_some_iff.mp hxC).1
  -- ## the restored stored field, read by kind
  have hlpsT : cvT₀.levelParams = p.lps := by rw [← hDfacts.2.1]; exact hsyn.lps
  have hrealStored' : ∀ t, t < p.k →
      ((ConLeche.consNestedFormers (stored.take p.k) env).find? (d.memberName t)).isSome = true := by
    intro t ht
    obtain ⟨cv, caps, hfind, -⟩ := hrealStored t ht
    rw [hfind]; rfl
  have hrealLps' : ∀ t, t < p.k → ∀ ci : ConstantInfo,
      (ConLeche.consNestedFormers (stored.take p.k) env).find? (d.memberName t) = some ci →
      ci.toConstantVal.levelParams = cvT₀.levelParams := by
    intro t ht ci hci'
    obtain ⟨cv, caps, hfind, hlps⟩ := hrealStored t ht
    rw [hfind] at hci'
    rw [← Option.some.inj hci', hlpsT, ← (ConLeche.auxBlock_inv hb).2.1]
    exact hlps
  have hrest := restoredFieldsRead_of_stored mp₁ mpAux hF hag hTbl hup hD hsyn.res hview hsyn.tgtLt
    hsyn.dk hrealStored' hrealLps' hsyn.auxFresh hsyn.named hsyn.RnP hsyn.pinName hsyn.lookS
    hsyn.recS (tgtCont := fun j'' => (cd j'').dJ.memberName (cd j'').mm)
    (tgtLps := fun j'' => (cd j'').ψ') (tgtDsA := fun j'' => (cd j'').DsA)
    (fun jq qq hqq => by
      obtain ⟨J₃, lvls₃, Ds₃, ci₃, h1, h2, h3, h4, h5, h6, h7⟩ := hpinAll jq qq hqq
      exact ⟨J₃, lvls₃, Ds₃, ci₃, h1, h2, h3, h4, h5, h6, h7⟩)
    i x hx
  -- ## the two conjuncts
  refine ⟨?_, ?_⟩
  · rw [hview.1, hview.2.1]
    exact hsyn.excl i hnr
  · exact whnfContent_field hμ mp₁ mpAux hi hlenDs pf.len (by rw [hnP]; exact hparamsLen) hpsLen
      hreadP hreadC hxC hokP hgradeC hW hrest

/-! ## The constructor record off the run, the `whnf` arm's content discharged -/

/-- **`CopyCtorsRead` is a READ off `DeclNestedRun`** (M-D′ D2 complete):
`copyCtorsRead_of_run'` with `WhnfContent` DISCHARGED — the formers'
model from `nestedFormersModel`, the walk's facts from
`copyWalkFacts_of_run`, the `whnf` arm's content from
`whnfContent_of_run`, and the pins' literal support from
`pinsLits_of_run` (task #311), whose environment hypothesis is the
formers' conses against `nestedFormerEnv`: a name of either is a
pre-block name or a real member's, and the real members are stored at
`env₁` (`hrealStored`).  What remains named: `ContainersRep` alone
(M-E's, the containers' representation at the scratch model). -/
theorem copyCtorsRead_of_run'' {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envOut : Env} {p : ConLeche.NestedParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (h : DeclNestedRun μ F env p envOut) :
    ∃ (st : ElimState) (b : MutualBlock) (envAux : Env) (order : List Nat),
      ConLeche.auxBlock p st = some b ∧
      ConLeche.nestedTopoOrder (ElimState.grp st) p.k st = .ok order ∧
      st.types.length = p.k + st.pins.length ∧
      ∃ (mpAux : EnvModelM V μ envAux) (d : IndRepData V), MutualBlockReps mpAux.base2 b d ∧
        CtorsChecked μ F env b true d ∧ AuxBlockAgree F mp mpAux b true d ∧
        ∃ (params : List Expr) (pbs : List (Expr × ConLeche.BinderMeta)),
          (ContainersRep env envAux mpAux.base2 → ∀ ψ : Name → Nat,
            ∃ cd : Nat → CopyData V,
              (∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j) ∧
              CopyCtorsRead mpAux d ψ st p.k st.pins.length cd) := by
  obtain ⟨st, b, envAux, params, pbs, fmsA, ctorsA, stored, order, hb, helim, hord, hlenSt, hfreshC,
    hcontC, hparamsLen, hcore, hstoredA, hpc, hK20, hK23, hK17, hpo, hmo, hhead, hfreshRec, hpinsNP,
    hrest, mpAux, d, hreps, hchk, hag, hpins⟩ := pinFacts_of_run hμ mp hE h
  obtain ⟨-, -, hannF, hannC, -⟩ := hrest
  refine ⟨st, b, envAux, order, hb, hord, hlenSt, mpAux, d, hreps, hchk, hag, params, pbs, ?_⟩
  intro hcr ψ
  obtain ⟨cd, hcd⟩ := hpins hcr ψ
  refine ⟨cd, hcd, ?_⟩
  have hkp : p.k ≤ b.k := by rw [ConLeche.auxBlock_k hb, hlenSt]; omega
  obtain ⟨mp₁, -, -, -, hag₁, hF, hrealStored⟩ := nestedFormersModel mp hE hcore hstoredA
    (fun t ht => (hfreshRec t ht).1) hK20 hkp mpAux d hreps hag
  -- ## the pins' literal support at the formers' environment (task #311)
  have hup : ∀ n : Name, (env.find? n).isSome = true →
      ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true := by
    intro n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    rw [(consNestedFormers_freshExt hK20).find?_some hc]; rfl
  have hfmsLen : fmsA.length = p.k := by
    have h1 := ConLeche.elimNested_length helim
    rw [ConLeche.nestedTypes0_length, hlenSt] at h1
    omega
  have hrepsN := hreps
  obtain ⟨-, -, -, -, -, -, hnames, -⟩ := hrepsN
  have hmono : ∀ n : Name, ((ConLeche.nestedFormerEnv fmsA env).find? n).isSome = true →
      ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true := by
    intro n hn
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hn
    rcases ConLeche.nestedFormerEnv_find? hc with h1 | h1
    · exact hup n h1
    · obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp h1
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcv
      have htf : t < fmsA.length := (List.getElem?_eq_some_iff.mp ht).1
      have htk : t < p.k := by omega
      have htb : t < b.k := by rw [ConLeche.auxBlock_k hb, hlenSt]; omega
      have hnm := ConLeche.elimNested_name_lt helim (t := t)
        (by rw [ConLeche.nestedTypes0_length]; exact htf)
      rw [ConLeche.nestedTypes0_getElem?, ht] at hnm
      simp only [Option.map_some] at hnm
      obtain ⟨ty, hty, htyn⟩ := Option.map_eq_some_iff.mp hnm
      obtain ⟨cv', caps, hfind, -⟩ := hrealStored t htk
      rw [memberName_eq_type hb hnames hty htb, htyn] at hfind
      rw [hfind]; rfl
  have hpinsLits := pinsLits_of_run mp hmono hannF hannC helim
  have hwalk := copyWalkFacts_of_run hb hlenSt hfreshC hcontC mp.base2.wf hcore hstoredA hpc hK20
    hK17 helim hparamsLen hpo hmo hhead hreps hchk hcd (nestedGroupExclusionOk_inv hK23)
    (fun j'' hj'' => (hcd j'' hj'').1.1.ordNotRec)
  have hwhnfC := whnfContent_of_run hμ hb hlenSt mp.base2.wf hcore (fun t ht => (hfreshRec t ht).1)
    hK20 hparamsLen hmo hhead hpinsNP hreps hcd hwalk hpinsLits mp₁ hF hag₁
    (nestedTbl_fresh_of_run hcore hK20) hrealStored
  intro j' hj' Jc cAJ hJc
  exact copyCtorAsRead_of_run hb hlenSt hfreshC hcontC hreps hchk hcd hwalk hwhnfC hj' hJc

end ConLeche.Model
