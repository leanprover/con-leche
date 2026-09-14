module

public import ConLeche.Model.Inductives.NestedCtorKit
public import ConLeche.Model.Inductives.RestoreTblRun
public import ConLeche.Model.Inductives.NestedCtorLeaf
import ConLeche.Verify.Inductives.NestedCtorNames
import ConLeche.Verify.Inductives.NestedInv
import ConLeche.Verify.Inductives.MutualInv
import ConLeche.Verify.Inductives.FormerFront
import ConLeche.Verify.Inductives.NestedFacts

public section

/-!
# The restored constructors at the run (task #279 M-D′ D3, DESIGN §M.54)

The REAL members' constructors, restored (`restoreNested R`: a copy at
the parameters and index arguments put back to its container at the
pin's components, K.19 stores the restore syntactically), read at the
formers' model `mp₁` of `env₁ = consNestedFormers (stored.take p.k) env`
from the run's own facts:

* **`restoredCtor_resid`** — the stored auxiliary constructor's opened
  residual is the member at the constructor's own parameter openers and
  index arguments (`checkMutualCtor_front` at the constructor stage the
  datum records; their resolution before the block is
  `ctorFieldsRes_of_chk`'s, off `mutualFieldsOk`);
* **`restoredCtorRead_of_run`** — every restored constructor
  `c ∈ ctorsR.flatten` is a real member's constructor `cA` at the datum
  (position `J`, `restoredCtor_pos`), and its restored type reads at
  `mp₁` as `mkPisAV dsRestored body` — the auxiliary domains with
  `restoreAV` at the copy positions, ending in the auxiliary body —
  graded (`restoredCtor_read` at: the constructor's OWN parameter
  openers transferred down at `env₁`-resolution, the front door's
  discipline, `down_of_resolve₁`; the fields by kind,
  `restoredFieldsRead_of_stored` at the run's table facts
  (`RestoreTblRun`) and pins' data (`pinsData_of_run`); the residual its
  own restoration, read from its pieces; the grading from the front
  door's inference at `mp₁`, `ClaimsAt.sortRow`).
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

/-! ## The residual, opened -/

/-- **A block constructor's opened residual** is its member at the
constructor's own parameter openers and index arguments: the
constructor stage's front (`checkMutualCtor_front`) at the datum's
constructor list (`CtorsChecked`), the member's name the checked
former's (`mutualFormerChecks_front`). -/
theorem restoredCtor_resid {μ : CheckMode} {F : Nat} {env envAux : Env} {b : MutualBlock}
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V}
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    {J : Nat} {cA : ConstantVal × Nat} (hJ : d.ctorsA[J]? = some cA) (hmem : d.mems J < b.k)
    {crest : Expr}
    (hop₁ : ConLeche.openPisAtFvars d.nP cA.1.type 0 = some (d.fvsPF J, crest))
    (hop₂ : ConLeche.openPisAtFvars cA.2 crest d.nP = some (d.xFvsF J, d.xrestF J)) :
    ∃ idx : List Expr,
      d.xrestF J = Expr.mkAppN (.const (d.memberName (d.mems J)) (b.lps.map .param))
        (d.fvsPF J ++ idx) := by
  obtain ⟨-, -, -, hnPb, -, -, hnames, -⟩ := hreps
  obtain ⟨_env₁, fms, f₀, ctorsA', sortss, hformers, -, hctors', hdA, -, hmems⟩ := hchk
  have hJ' : ctorsA'[J]? = some cA := by rw [← hdA]; exact hJ
  obtain ⟨hlenA, -, hallC⟩ := ConLeche.checkMutualCtors_inv hctors'
  have hJlt : J < b.ctors.length := by
    rw [← hlenA]; exact (List.getElem?_eq_some_iff.mp hJ').1
  obtain ⟨mc, hmc⟩ : ∃ mc, b.ctors[J]? = some mc := ⟨_, List.getElem?_eq_getElem hJlt⟩
  obtain ⟨hnF, sorts, -, hrun⟩ := hallC J mc cA hmc hJ'
  obtain ⟨-, -, fvsP', crest', _tfvs, _trest, xFvs', idxArgs, hop₁', -, -, hop₂', -, -, -, -⟩ :=
    ConLeche.checkMutualCtor_front hrun
  rw [← hnPb] at hop₁' hop₂'
  rw [← hnF] at hop₂'
  obtain ⟨hf1, hc1⟩ := Prod.mk.inj (Option.some.inj (hop₁'.symm.trans hop₁))
  subst hf1 hc1
  obtain ⟨-, hx2⟩ := Prod.mk.inj (Option.some.inj (hop₂'.symm.trans hop₂))
  -- the constructor's member is the datum's, and its name the checked former's
  have hmemJ : d.mems J = mc.member := by
    rw [hmems J, List.getD_eq_getElem?_getD, hmc]; rfl
  obtain ⟨hchecks, -⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨hlenFms, hposF⟩ := ConLeche.mutualFormerChecks_front hchecks
  have hmemLt : mc.member < fms.length := by
    rw [hlenFms]; rw [hmemJ] at hmem; exact hmem
  obtain ⟨f, hf⟩ : ∃ f, fms[mc.member]? = some f := ⟨_, List.getElem?_eq_getElem hmemLt⟩
  obtain ⟨cv, bs, hl, hff, -⟩ := hposF mc.member f hf
  have hname : d.memberName (d.mems J) = (fms.getD mc.member default).cvTa.name := by
    rw [hmemJ, hnames mc.member (by rw [hmemJ] at hmem; exact hmem), memberNames_getD hl,
      List.getD_eq_getElem?_getD, hf]
    exact hff.name.symm
  refine ⟨idxArgs, ?_⟩
  rw [← hx2, hname]

/-! ## The restored constructor, read at the formers' model -/

set_option maxHeartbeats 1600000 in
/-- **Every restored constructor reads at the formers' model** (M-D′
D3's `read`, at the run): `c ∈ ctorsR.flatten` is a real member's
constructor `cA` at datum position `J` (`restoredCtor_pos`), and its
restored type reads at `mp₁` as the Π-tower over `dsRestored` (the
auxiliary domains with `restoreAV` at the copy positions, at the pins'
data `cd`) ending in the auxiliary body, and that reading is graded
(the pre-annotated front door's inference at `env₁`, `ClaimsAt.sortRow`)
— every input of `restoredCtor_read` from the run: the constructor's
own parameter openers read as the auxiliary parameter entries
(`denoteMeta_openPis` at the scratch model, transferred down at
`env₁`-resolution and the projection-table discipline the front door
validated, `down_of_resolve₁`), the fields by kind
(`restoredFieldsRead_of_stored` at `RestoreTblRun`'s table facts,
`ctorFieldsRes_of_chk` and `pinsData_of_run`), the residual — the
member at the openers and index arguments — its own restoration
(`restoreI_eq_self`), read from the auxiliary body transferred down. -/
theorem restoredCtorRead_of_run {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {env envAux : Env} {p : ConLeche.NestedParts} {st : ElimState} {b : MutualBlock}
    {params : List Expr} {pbs : List (Expr × ConLeche.BinderMeta)} {stored : List AuxStored}
    {fmsA ctorsA : List ConstantVal} {ctorsR : List (List (ConstantVal × Nat × Nat))}
    {mpAux : EnvModelM V μ envAux} {d : IndRepData V} {ψ : Name → Nat} {cd : Nat → CopyData V}
    (hb : ConLeche.auxBlock p st = some b) (hlenSt : st.types.length = p.k + st.pins.length)
    (hcopies : ConLeche.copiesFresh env p.k st = true)
    (hcore : ConLeche.checkMutualCore (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env b none
      true = .ok envAux)
    (hstoredA : ConLeche.auxStoredAll envAux b b.k = some stored)
    (hpc : ConLeche.pinsClosed p.nP st.pins = true)
    (helim : ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st)
    (hpo : PinsAtOpeners st params)
    (hhead : ∃ (t₀ : AuxType) (body body₀ : Expr), st.types[0]? = some t₀ ∧
      ConLeche.openPisAtFvars p.nP t₀.type 0 = some (params, body) ∧
      t₀.type.stripPis p.nP = some (pbs, body₀) ∧ pbs.length = p.nP ∧ t₀.type.hasFvar = false)
    (hfreshRec : ∀ t, t < b.k → env.find? (b.recName t) = none)
    (hK20 : (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true)
    (hmo : PinsMentionReal env st params p.k)
    (hpinsNP : ∀ q ∈ st.pins, ∀ (T : Name) (i : Nat), env.find? T = none →
      Expr.NoProjAt T i q.pin)
    (hreps : MutualBlockReps mpAux.base2 b d) (hchk : CtorsChecked μ F env b true d)
    (hpins : ∀ j, j < st.pins.length → PinRunFacts F env p st b params pbs mpAux d ψ cd j)
    (hpinsLits : ∀ q ∈ st.pins, ∀ a ∈ q.pin.getAppArgs,
      litsResolve (ConLeche.consNestedFormers (stored.take p.k) env) a = true)
    (hctors : (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors) = .ok ctorsR)
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
    ∀ c ∈ ctorsR.flatten, ∃ (J : Nat) (cA : ConstantVal × Nat) (lpsT : List Name),
      d.ctorsA[J]? = some cA ∧ d.mems J < p.k ∧
      c.1.name = cA.1.name ∧ c.1.levelParams = p.lps ∧ c.2.1 = d.nP ∧ c.2.2 = cA.2 ∧
      envAux.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) ∧
      FixCtorDataI mpAux.base2 d.env₀ (d.memberName (d.mems J)) lpsT cA.1 d.nP cA.2
        (d.nIdxAt (d.mems J)) d.resSort d.isProp d.large (d.idxF J) (d.dsF J) (d.esF J)
        (d.srcsF J) (d.ksF J) (d.fvsPF J) (d.xFvsF J) (d.xrestF J) (d.eissF J) (d.tssF J)
        (fun i => d.memberName (d.tgts J i)) (fun i => d.nIdxAt (d.tgts J i)) ∧
      denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ 0 c.1.type
        = some (mkPisAV
            (d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
              (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA))
            (ctorBodyAVI mpAux.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))) ∧
      ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV
            (d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
              (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA))
            (ctorBodyAVI mpAux.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))) := by
  intro c hc
  -- ## the constructor's position at the datum
  obtain ⟨t, J, cA, ht, hJ, hmemsJ, hresR, hname, hlps, hnP1, hnF1⟩ :=
    restoredCtor_pos hb hlenSt hstoredA hctors hreps hchk c hc
  have hreps' := hreps
  obtain ⟨-, hkb, -, hnPb, -, hviewAll, -, hall⟩ := hreps
  have hnP : d.nP = p.nP := by rw [hnPb, (ConLeche.auxBlock_inv hb).1]
  have hkp : p.k ≤ b.k := by rw [ConLeche.auxBlock_k hb, hlenSt]; omega
  have hdk : d.k = p.k + st.pins.length := by rw [hkb, ConLeche.auxBlock_k hb, hlenSt]
  have hk0 : 0 < d.k := by omega
  obtain ⟨s₀, cvT₀, cvR₀, caps₀, mI₀, rP₀, rules₀, -, -, -, hsv₀, hrep₀⟩ :=
    hall 0 (by rw [← hkb]; exact hk0)
  have hDfacts := FixCtorFactsAt.congr_sort hsv₀ (hrep₀.ctors J cA hJ)
  have hD := hDfacts.2.2
  have hstoredC : envAux.find? cA.1.name = some (.ctorInfo cA.1 d.nP cA.2) := hDfacts.1
  have hview := hviewAll J
  -- the datum's projections, at the block's datum (the re-sorted record
  -- projects to the same components)
  have hreadA : denoteMeta mpAux.base2.acval envAux ψ 0 cA.1.type
      = some (mkPisAV (d.dsF J ψ)
          (ctorBodyAVI mpAux.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))) := hD.read ψ
  have hpLen : (d.fvsPF J).length = d.nP := hD.pLen
  have hpIdx : ∀ (k : Nat) (x : Expr), (d.fvsPF J)[k]? = some x → ∃ ty, x = Expr.fvar k ty := hD.pIdx
  have hidxEqD : d.idxF J = (d.xrestF J).getAppArgs.drop d.nP := hD.idxEq
  have hidxReadA : DenoteMetaSpine mpAux.base2.acval envAux ψ (d.nP + cA.2) (d.idxF J) (d.esF J ψ) :=
    hD.idxRead ψ
  -- ## the auxiliary constructor's type is closed
  have hcWF := mpAux.base2.wf _ (List.mem_of_find?_eq_some hstoredC)
  have hnf : cA.1.type.hasFvar = false := hcWF.1
  obtain ⟨crest, hop₁, hop₂⟩ : ∃ crest, ConLeche.openPisAtFvars d.nP cA.1.type 0 = some (d.fvsPF J, crest) ∧
      ConLeche.openPisAtFvars cA.2 crest d.nP = some (d.xFvsF J, d.xrestF J) := hD.opens
  -- ## the restored constant's front door at the formers' environment
  have hpre : ConLeche.checkConstantValPre (m := ConLeche.CheckM) (ConLeche.fueledOps μ F)
      (ConLeche.consNestedFormers (stored.take p.k) env) c.1 = .ok c.1 := by
    obtain ⟨cs, hcs, hcin⟩ := List.mem_flatten.mp hc
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcs
    obtain ⟨hlen, hall'⟩ := ConLeche.mapM_except_inv hctors
    obtain ⟨a, cs', ha, hcs', hrun⟩ := hall' j (by
      have := (List.getElem?_eq_some_iff.mp hj).1
      omega)
    rw [hj] at hcs'
    have hcc : cs = cs' := by simpa using hcs'
    rw [hcc] at hcin
    exact ConLeche.restoreCtors_pre hrun c hcin
  obtain ⟨hfreshR, -, -, -, hbtR, hnfR, hlpR, htrR, hptR, hinferR, -⟩ :=
    ConLeche.checkConstantValPre_front hpre
  -- ## the table's facts
  have RT := restoreTblRun_of_run hb hlenSt hcopies hcore hpc helim hpo hhead hreps' hchk
  have hRwf := RT.wf
  have hRnP : (ConLeche.restoreTbl p st).nP = d.nP := RT.nP
  have hfvsPLen : (d.fvsPF J).length = p.nP := by rw [hpLen, hnP]
  obtain ⟨hlookS, hrecS⟩ := RT.at_openers hfvsPLen hpIdx
  have hRS : ((ConLeche.restoreTbl p st).instAt (d.fvsPF J)).Named := hRwf.toNamed.instAt _
  -- ## the restored type opened at the parameters: the openers are the auxiliary ones
  obtain ⟨fvsR, restR, hopR, hlenR, htakeR, -, -⟩ :=
    ConLeche.restoreNested_openPis hRwf hresR hnf (n := d.nP) (by rw [hRnP]; exact Nat.le_refl _) hop₁
  have hfvsR : fvsR = d.fvsPF J := by
    rw [hRnP] at htakeR
    rw [List.take_of_length_le (by omega), List.take_of_length_le (by rw [hpLen]; exact Nat.le_refl _)] at htakeR
    exact htakeR
  rw [hfvsR] at hopR
  -- ## the formers' environment above the pre-block one
  have hup : ∀ n, (env.find? n).isSome = true →
      ((ConLeche.consNestedFormers (stored.take p.k) env).find? n).isSome = true := by
    intro n hn
    obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hn
    rw [(consNestedFormers_freshExt hK20).find?_some hc']; rfl
  -- ## the parameter openers, read at the formers' model
  have hlenD : (d.dsF J ψ).length = d.nP + cA.2 := hD.len ψ
  have hreadP : ∀ (k : Nat) (y : Expr), (d.fvsPF J)[k]? = some y →
      denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ k y.fvarTypeD
        = some ((d.dsF J ψ).getD k default).2.2 := by
    intro k y hy
    obtain ⟨pps, b', hst, -, -, hbind⟩ := denoteMeta_openPis d.nP hop₁ hreadA
    rw [stripPisAV_mkPisAV_take d.nP _ _ (by omega)] at hst
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
    obtain ⟨q, hq, -, hqr⟩ := hbind k y hy
    rw [Nat.zero_add] at hqr
    have hk : k < d.nP := by rw [← hpLen]; exact (List.getElem?_eq_some_iff.mp hy).1
    rw [List.getElem?_take_of_lt hk] at hq
    have hq' : ((d.dsF J ψ).getD k default).2.2 = q.2.2 := by
      rw [List.getD_eq_getElem?_getD, hq]; rfl
    rw [hq']
    exact down_of_resolve₁ mp₁ mpAux hF hag
      (openPisAtFvars_fvarTypeD_constsResolve d.nP hopR htrR y (List.mem_of_getElem? hy))
      ((openPisAtFvars_projTablesOk d.nP hopR hptR).2 y (List.mem_of_getElem? hy)) hqr
  -- ## the fields, read by kind
  obtain ⟨hresidRes, hresK⟩ := ctorFieldsRes_of_chk hchk hnPb hJ hop₁ hop₂
  have htgtLt : ∀ i, d.tgts J i < d.k := by
    intro i
    have := hrep₀.tgtsRLt J i
    rw [hview.2.1] at this
    exact this
  have hrealStored' : ∀ t, t < p.k →
      ((ConLeche.consNestedFormers (stored.take p.k) env).find? (d.memberName t)).isSome = true := by
    intro t ht
    obtain ⟨cv, caps, hfind, -⟩ := hrealStored t ht
    rw [hfind]; rfl
  have hrealLps' : ∀ t, t < p.k → ∀ ci : ConstantInfo,
      (ConLeche.consNestedFormers (stored.take p.k) env).find? (d.memberName t) = some ci →
      ci.toConstantVal.levelParams = cvT₀.levelParams := by
    intro t ht ci hci'
    obtain ⟨cv, caps, hfind, -⟩ := hrealStored t ht
    rw [hfind] at hci'
    rw [← Option.some.inj hci']
    exact hrep₀.membersLps t (by show t < d.k; omega) cv caps (hF hfind)
  have hpinAll := pinsData_of_run hb hlenSt hcore hfreshRec hK20 hmo hpinsNP hreps' hpins hpinsLits
    mp₁ hF hag hTbl hrealStored
  have hfields := restoredFieldsRead_of_stored mp₁ mpAux hF hag hTbl hup hD hresK hview htgtLt
    hdk hrealStored' hrealLps' RT.auxFresh hRS hRnP RT.pinName hlookS hrecS
    (tgtCont := fun j'' => (cd j'').dJ.memberName (cd j'').mm)
    (tgtLps := fun j'' => (cd j'').ψ') (tgtDsA := fun j'' => (cd j'').DsA)
    (fun jq qq hqq => by
      obtain ⟨J₃, lvls₃, Ds₃, ci₃, h1, h2, h3, h4, h5, h6, h7⟩ := hpinAll jq qq hqq
      exact ⟨J₃, lvls₃, Ds₃, ci₃, h1, h2, h3, h4, h5, h6, h7⟩)
  -- ## the residual: its own restoration, read from the auxiliary body
  obtain ⟨idx, hxrest⟩ := restoredCtor_resid hreps' hchk hJ (by omega) hop₁ hop₂
  have hargs : (d.xrestF J).getAppArgs.drop d.nP = idx := by
    rw [hxrest, Expr.getAppArgs_mkAppN]
    simp only [Expr.getAppArgs, List.nil_append]
    rw [List.drop_left' hpLen]
  have hidxRes : ∀ e ∈ idx, e.constsResolve env = true := by
    intro e he
    exact hresidRes e (by rw [hargs]; exact he)
  have hxrestSelf : ConLeche.restoreI ((ConLeche.restoreTbl p st).instAt (d.fvsPF J)) (d.xrestF J)
      = d.xrestF J := by
    refine ConLeche.restoreI_eq_self hRS _ fun n hn => ?_
    rw [hxrest]
    obtain ⟨hnf', hne⟩ := RT.auxFresh n hn
    refine Bool.eq_false_iff.mpr fun hm => ?_
    rcases (ConLeche.mentionsConstE_mkAppN_const_iff _ _ _).mp hm with h | ⟨a, ha, ham⟩
    · exact hne _ (by omega) h
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
        obtain ⟨ty, rfl⟩ := hpIdx k a hk
        exact nomatch ham
      · rw [Expr.mentionsConstE_eq_false_of_fresh (hidxRes a ha) hnf'] at ham
        exact nomatch ham
  have hidxEq : d.idxF J = idx := by rw [hidxEqD, hargs]
  have hidxRead : DenoteMetaSpine mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ
      (d.nP + cA.2) idx (d.esF J ψ) := by
    rw [← hidxEq]
    refine denoteMetaSpine_down_of_resolve mp₁ mpAux hF hag hTbl hup (fun e he => ?_) hidxReadA
    rw [hidxEq] at he
    exact hidxRes e he
  obtain ⟨cvT, capsT, hfindT, hlpsT⟩ := hrealStored (d.mems J) (by omega)
  have hhead : denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ
      (d.nP + cA.2) (.const (d.memberName (d.mems J)) (b.lps.map .param))
      = some (mpAux.base2.acval (d.memberName (d.mems J)) ψ) := by
    rw [denoteMeta_const hfindT (by
      show (b.lps.map Level.param).length = cvT.levelParams.length
      rw [List.length_map, hlpsT])]
    congr 1
    rw [← hag _ (by rw [hfindT]; rfl)]
    refine mp₁.base2.acval_params _ _ hfindT _ _ fun q _ => ?_
    show Level.substFn ψ cvT.levelParams (b.lps.map Level.param) q = ψ q
    rw [hlpsT]
    exact Level.substFn_map_param
  have hresid : denoteMeta mp₁.base2.acval (ConLeche.consNestedFormers (stored.take p.k) env) ψ
      (d.nP + cA.2)
      (ConLeche.restoreI ((ConLeche.restoreTbl p st).instAt (d.fvsPF J)) (d.xrestF J))
      = some (ctorBodyAVI mpAux.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ)) := by
    rw [hxrestSelf, hxrest]
    unfold ctorBodyAVI
    rw [paramBvars_eq_paramBvarsAt]
    exact denoteMeta_mkAppN
      (DenoteMetaSpine.append (denoteMetaSpine_params (d.nP + cA.2) hpLen hpIdx) hidxRead) hhead
  -- ## the reading
  have hread := restoredCtor_read mp₁ mpAux hRwf hRnP hresR hnf hop₁ hop₂ hreadA hlenD hreadP
    hfields hresid
  -- ## the grading: the front door's inference at the formers' model
  have hokTy : ∀ ρ : Nat → V, WellDenotedV V ρ (mkPisAV
      (d.dsRestored mpAux.base2 ψ p.k J (fun j'' => (cd j'').dJ.memberName (cd j'').mm)
        (fun j'' => (cd j'').ψ') (fun j'' => (cd j'').DsA))
      (ctorBodyAVI mpAux.base2 (d.memberName (d.mems J)) d.nP cA.2 ψ (d.esF J ψ))) := by
    intro ρ
    obtain ⟨stype, u, hst, hens⟩ := hinferR
    have hc := claimsAt_of hμ mp₁ ψ F
    have hw : Expr.WScoped 0 c.1.type := Expr.WScoped.of_not_hasFvar hnfR
    have hL : Expr.LeavesBounded c.1.type := Expr.LeavesBounded.of_not_hasFvar hnfR
    have hnil : c.1.type.fvarLeaves = [] := Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfR
    have h := hc.sortRow hst hens hw hbtR hL (CtxOk.nil hnil) hread ρ (Sat_nil V ρ)
    exact h.1
  exact ⟨J, cA, cvT₀.levelParams, hJ, by omega, hname, hlps, hnP1, hnF1, hstoredC, hD, hread, hokTy⟩
