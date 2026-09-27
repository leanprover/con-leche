module

public import ConLeche.Model.Annot.EnvModelM
import ConLeche.Verify.Inductives.HomeTie
public import ConLeche.Kernel.Inductives.RecCheck
import ConLeche.Verify.EnvExt.Base
public import ConLeche.Verify.EnvExt.Fold
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Verify.CheckerF
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Extend.Inversions
import ConLeche.Semantics.FoldScope
import ConLeche.Model.Inductives.BlockDatum
import ConLeche.Model.Inductives.BlockCover

public section

/-!
# The recursor check's own home table is the walk's (PRIMREC / HOMETABLE)

The recursor check computes the home table itself (`homeTableRec`) at
the constructors' environment `envC`; the walk's records the table must
reproduce (`homeTable_good`, `NestHomeReach.lean`) are at the formers'
environment `envI`.  The two environments differ by the block's
constructors, fresh names of the ordinary shape, so the member tie holds
between them at the scope of `envI` (`Agree.ofBase`, no prelude
hypothesis), and the table's own reads agree (`CtxTie`): a container
that is no member reads the same constructors (the new ones are the
members'), every other lookup is scoped.  So the rec check's successful
table IS the table at the walk's own context (`homeTable_install`).

`HomeInstall` collects what the install tells: the formers and
constructors resolve at `envI`, the constructors' cons is a `StepOk`
extension, and the containers' constructors agree.
-/

namespace ConLeche.Model

open ConLeche ConLeche.EnvExt

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **What the install tells the recursor check's home table** (see the
module docstring). -/
structure HomeInstall (envI envC : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat))) : Prop where
  formers : ∀ cv ∈ cvTasR, cv.type.constsResolve envI = true
  step : StepOk envI envC
  ctors : ∀ cs ∈ ctorsAsR, ∀ cA ∈ cs, cA.1.type.constsResolve envI = true
  cont : ∀ (fvsP : List Expr) (C : Name), pp.memberNames.contains C = false →
    (envI.find? C).isSome = true →
    nestContainer (pp.nestCtx fvsP envC.find? envC.consts) C =
      nestContainer (pp.nestCtx fvsP envI.find? envI.consts) C

/-- **The rec check's own home table is the table at the walk's
context** (see the module docstring). -/
theorem homeTable_install {F : Nat} {envI envC : Env} (mk : EnvModelM V μ envI) {pp : BlockParts}
    {cvTasR : List ConstantVal} {ctorsAsR : List (List (ConstantVal × Nat))}
    (HI : HomeInstall envI envC pp cvTasR ctorsAsR) {cvTa0 : ConstantVal} {fvsP : List Expr}
    {rest : Expr} {holes : List Expr}
    (hcv0 : cvTasR.head? = some cvTa0) (hop0 : openPisAtFvars pp.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes0 : nestHoles (pp.nestCtx fvsP envI.find? envI.consts) = some holes)
    {T : List HomeEntry}
    (hT : homeTableRec (fueledOps .verified F) (mkFEnv envC) pp.toBlockShape cvTasR ctorsAsR
      = .ok T) :
    homeTable (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) holes ctorsAsR
      homeTableRounds = .ok T := by
  have hstep := HI.step
  have hwf := mk.base2.wf
  have hA : Agree (InScope envI) envI envC :=
    Agree.ofBase hwf mk.base2.rec_ctors (natOpGuardLaw_of mk) (Extends.refl _)
      (NoNewInScope.refl _) hstep.1 hstep.noNewInScope hstep.1
  have hTie : CtxTie (InScope envI) envI envC (pp.nestCtx fvsP envI.find? envI.consts)
      envC.find? envC.consts := {
    agree := hA
    find := fun h => find?_base hstep.1 hstep.noNewInScope h
    closed := fun _ hf => ciSc_of_base hwf mk.base2.rec_ctors hf
    cont := fun {C} hC hnm => by
      cases hf : envI.find? C with
      | none =>
        have h2 : envC.find? C = envI.find? C := find?_base hstep.1 hstep.noNewInScope hC
        have e1 : ((pp.nestCtx fvsP envI.find? envI.consts).atEnv envC.find? envC.consts).find? C
            = none := by rw [← hf, ← h2]; rfl
        have e2 : (pp.nestCtx fvsP envI.find? envI.consts).find? C = none := hf
        unfold nestContainer
        rw [e1, e2]
      | some ci => exact HI.cont fvsP C hnm (by rw [hf]; rfl)
    contSc := fun _ h =>
      nestContainer_sc (fun ci hci => sc_of_constsResolve (hwf ci hci).2.2.1) h
    params := (sc_openPisAtFvars
      (sc_of_constsResolve (HI.formers cvTa0 (List.mem_of_mem_head? hcv0))) hop0).1
    names := fun n hn => .stored (nestHoles_names hholes0 n hn) }
  have hholesSc := nestHoles_sc hTie hholes0
  have hct : ∀ t, ∀ c ∈ ctorsAsR.getD t [], Sc (InScope envI) c.1.type := by
    intro t c hc
    rw [List.getD_eq_getElem?_getD] at hc
    cases h : ctorsAsR[t]? with
    | none => rw [h] at hc; exact nomatch hc
    | some cs =>
      rw [h, Option.getD_some] at hc
      exact sc_of_constsResolve (HI.ctors cs (List.mem_of_getElem? h) c hc)
  unfold homeTableRec at hT
  obtain ⟨cvTa0', h0, hT⟩ := exceptBind_ok hT
  rw [unwrapOr_ok h0] at hcv0
  obtain rfl := Option.some.inj hcv0
  obtain ⟨pq, h1, hT⟩ := exceptBind_ok hT
  rw [unwrapOr_ok h1] at hop0
  obtain rfl := Option.some.inj hop0
  obtain ⟨holes', h2, hT⟩ := exceptBind_ok hT
  rw [mkFEnv_find?_fun, mkFEnv_env] at h2 hT
  dsimp only at h2 hT
  have hh : nestHoles ((pp.nestCtx fvsP envI.find? envI.consts).atEnv envC.find? envC.consts)
      = some holes' := unwrapOr_ok h2
  obtain rfl := Option.some.inj (hholes0.symm.trans ((nestHoles_at hTie).symm.trans hh))
  exact (homeTable_ok hTie .verified F hholesSc hct homeTableRounds T hT).1

/-! ## The install's facts -/

/-- A checked constant's annotated type resolves where it was checked. -/
theorem checkConstantVal_resolves {F : Nat} {env : Env} {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps μ F) env cv = .ok cv') : cv'.type.constsResolve env = true := by
  obtain ⟨-, -, -, -, -, -, type, stype, u, -, -, hres, -, -, rfl⟩ := checkConstantVal_inv h
  exact hres

/-- **The formers resolve at their environment.** -/
theorem checkBlockInds_resolves {F : Nat} {env env₁ : Env} {p₀ : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape}
    (h : checkBlockInds (fueledOps μ F) env p₀ isRec = .ok (env₁, cvTas, p₁)) :
    ∀ cv ∈ cvTas, cv.type.constsResolve env₁ = true := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, -, rfl, -, henv, h0, hcvs, -⟩ := checkBlockInds_shape h
  have hone : ∀ {ms : MemberShape} {cv : ConstantVal} {s : Level},
      checkBlockTele (fueledOps μ F) env p₀.nP ms = .ok (cv, s) →
      cv.type.constsResolve env₁ = true := by
    intro ms cv s hh
    obtain ⟨cvT, -, -, hcv, -⟩ := checkBlockTele_shape hh
    rw [henv]
    exact consBlockInds_constsResolve _ _ _ _ (checkConstantVal_resolves hcv)
  obtain ⟨hlen, hall⟩ := checkBlockTeles_inv hcvs
  intro cv hcv
  rcases List.mem_cons.mp hcv with rfl | hcv'
  · exact hone h0
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hcv'
    obtain ⟨i, hi⟩ := List.getElem?_of_mem hq
    have hil : i < rest.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.mp hi).1
    obtain ⟨q', hq', hrun⟩ := hall i rest[i] (List.getElem?_eq_getElem hil)
    obtain rfl := Option.some.inj (hi.symm.trans hq')
    exact hone hrun

/-- **One member's constructors**: each resolves at the loop's
environment, and its conclusion is the member applied. -/
theorem checkSumCtors_resolves {F : Nat} {env₀ env : Env} {T : Name} {lps : List Name}
    {nP nIdx : Nat} {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal}
    {cs ctorsA : List (ConstantVal × Nat)} {sortss : List (List Level)}
    (h : checkSumCtors (fueledOps μ F) env₀ env T lps nP nIdx resSort isProp large cvTa cs
      = .ok (ctorsA, sortss)) :
    ∀ cA ∈ ctorsA, cA.1.type.constsResolve env = true ∧
      ∃ cbs args, cA.1.type.stripPis (nP + cA.2) = some (cbs, Expr.mkAppN (.const T (lps.map .param)) args) := by
  obtain ⟨hlen, -, hall⟩ := checkSumCtors_inv h
  intro cA hcA
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hcA
  obtain ⟨hn, sorts, -, hrun⟩ := hall j (cs[j]'(hlen ▸ hj)) (ctorsA[j])
    (List.getElem?_eq_getElem _) (List.getElem?_eq_getElem hj)
  obtain ⟨⟨ty', hccv⟩, ⟨cbs, es, hstrip, -⟩, -⟩ := checkSumCtor_shape hrun
  refine ⟨checkConstantVal_resolves hccv, ?_⟩
  rw [hn]; exact ⟨cbs, _, hstrip⟩

/-- **What the install tells the recursor check's home table**, from the
formers' and the constructors' runs. -/
theorem homeInstall_of {F : Nat} {env env₁ : Env} {p₀ : BlockParts} {isRec : Bool}
    {cvTas : List ConstantVal} {p₁ : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    (hInd : checkBlockInds (fueledOps μ F) env p₀ isRec = .ok (env₁, cvTas, p₁))
    (hCtors : checkBlockCtors (fueledOps μ F) env₁ env₁ p₁ (p₁.members.zip cvTas)
      = .ok (ctorsAs, sortsss)) :
    HomeInstall env₁ (consBlockCtors p₁.nP ctorsAs env₁) (p₀.complete p₁) cvTas ctorsAs := by
  have hC := ConLeche.Semantics.checkBlockCtors_names' hCtors
  have hstep : StepOk env₁ (consBlockCtors p₁.nP ctorsAs env₁) :=
    (StepOk.refl env₁).consBlockCtors fun A hA c hc =>
      ⟨(hC A hA c hc).1, (hC A hA c hc).2.1, (hC A hA c hc).2.2⟩
  obtain ⟨hlenC, -, hallC⟩ := checkBlockCtors_inv hCtors
  -- every stored constructor: resolving, its conclusion a member applied
  have hctor : ∀ cs ∈ ctorsAs, ∀ cA ∈ cs, cA.1.type.constsResolve env₁ = true ∧
      ∃ T cbs args, T ∈ p₁.memberNames ∧ cA.1.type.stripPis (p₁.nP + cA.2) =
        some (cbs, Expr.mkAppN (.const T (p₁.lps.map .param)) args) := by
    intro cs hcs cA hcA
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hcs
    have hil : i < (p₁.members.zip cvTas).length := by rw [← hlenC]; exact hi
    obtain ⟨ctorsA, sortss, hca, -, hrun⟩ := hallC i _ (List.getElem?_eq_getElem hil)
    rw [List.getElem?_eq_getElem hi] at hca
    obtain rfl := Option.some.inj hca
    obtain ⟨hres, cbs, args, hstrip⟩ := checkSumCtors_resolves hrun cA hcA
    refine ⟨hres, _, cbs, args, ?_, hstrip⟩
    rw [List.getElem_zip]
    exact List.mem_map_of_mem (List.getElem_mem _)
  refine ⟨checkBlockInds_resolves hInd, hstep, fun cs hcs cA hcA => (hctor cs hcs cA hcA).1, ?_⟩
  intro fvsP C hnm hC0
  have hfind : (consBlockCtors p₁.nP ctorsAs env₁).find? C = env₁.find? C := by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hC0
    rw [hci, hstep.1 hci]
  unfold nestContainer
  simp only [BlockShape.nestCtx]
  rw [hfind, consBlockCtors_consts, List.filterMap_append, List.filterMap_eq_nil_iff.mpr ?_,
    List.nil_append]
  -- the new constructors name no container
  intro ci hci
  obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hci)
  obtain ⟨cs, hcs, hcAcs⟩ := List.mem_flatten.mp hcA
  obtain ⟨-, T, cbs, args, hT, hstrip⟩ := hctor cs hcs cA hcAcs
  have hne : (T == C) = false := by
    rw [beq_eq_false_iff_ne]
    rintro rfl
    have hnm' : (p₁.memberNames.contains T) = false := hnm
    rw [List.contains_iff_mem.mpr hT] at hnm'
    exact nomatch hnm'
  simp only [hstrip, getAppFn_mkAppN_const, hne]
  rfl

end ConLeche.Model
