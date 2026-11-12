module

public import InLeanProof.IndMembers
public import InLeanProof.PassRecs6
public import InLeanProof.PassNestSeeds
public import InLeanProof.PassPositivity
public import InLeanProof.PassClasses
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Verify.Inductives.RecCheckRun
public import ConLeche.Verify.Inductives.GenRecScoped
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Inductives.NestNfScope
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.Cached.GenRecC
import ConLeche.Verify.Cached.Erase
/- `FEnv.push` (not exposed in `InLean/Push.lean`). -/
import all InLean.Push

/-!
# O7: the pass assembled (task #451, lane PassSim)

InLean's `checkBlockPassS` against master's pure `checkBlockPass`, from the
proved stages in the job's order: the formers (`checkBlockIndsFI_run`, the
environment by `jobEnvI_formers`), the flush, the constructors
(`checkBlockCtorsFI_run`), the walk's context (`blockNestCtxI_run`), the
classes (`checkBlockClassesI_run`), the block's positivity
(`checkBlockPositivityI_run`), the seeds (`classSeedsI_run`) and their walk
(`nestSeedsI_run`).

The relation is `PassRelI PassDataI`: beside the environment, shape and
parameters, `PassDataI` relates the field kinds, the class reading, the
classes and the table by their translations at the final state, and carries
what the tail's stages take of the pass (the readings' facts, the
parameters' scope, the classes' frames, the formers' and constructors'
closedness, the constructors' freshness, distinctness and `sorryAx` clause,
master's well-formedness at their push, the table's entries closed).

The stream recursors' types closed (`checkBlockClassesI_run`'s `hrecs`, through
`classReadI_run`'s opener) is `PassSimI`'s premise, from the generator's output
check (`constClosed`, through `recsClosed_of_block`).
-/

@[expose] public section

namespace InLeanProof

open Lean InLean ConLeche.Cached

/-! ## Small facts -/

theorem consBlockIndsF_pending (p : InLean.BlockShape) (isRec : Bool) :
    ∀ (l : List Lean.ConstantVal) (i : Nat) (fe : InLean.FEnv),
      (InLean.consBlockIndsF p isRec l i fe).pending = fe.pending
  | [], _, _ => rfl
  | _ :: rest, i, fe => by
    unfold InLean.consBlockIndsF
    rw [consBlockIndsF_pending p isRec rest (i + 1)]
    rfl

theorem consBlockIndsF_coreAxioms (p : InLean.BlockShape) (isRec : Bool) :
    ∀ (l : List Lean.ConstantVal) (i : Nat) (fe : InLean.FEnv),
      (InLean.consBlockIndsF p isRec l i fe).coreAxioms = fe.coreAxioms
  | [], _, _ => rfl
  | _ :: rest, i, fe => by
    unfold InLean.consBlockIndsF
    rw [consBlockIndsF_coreAxioms p isRec rest (i + 1)]
    rfl

theorem ctorNamesOf_allCtors (p : InLean.BlockShape) :
    ctorNamesOf p.members = p.allCtors.map (·.1.name) := by
  simp only [ctorNamesOf, InLean.BlockShape.allCtors, List.flatMap, List.map_flatten, List.map_map]
  rfl

theorem checkSumCtorsF_fresh {mode : InLean.CheckMode} {fe₀ fe : InLean.FEnv} {T : Lean.Name}
    {lps : List Lean.Name} {nP nIdx : Nat} {sr : Lean.Level} {isProp large : Bool}
    {cvTa : Lean.ConstantVal} :
    ∀ {l : List (Lean.ConstantVal × Nat)} {s₀ s' : InLean.CState} {u : Unit},
      InLean.checkSumCtorsC mode fe₀ fe T lps nP nIdx sr isProp large cvTa l s₀ = .ok (u, s') →
      ∀ c ∈ l, fe.env.find? c.1.name = none
  | [], _, _, _, _ => by simp
  | c :: cs, s₀, s', u, h => by
    unfold InLean.checkSumCtorsC at h
    obtain ⟨_, _, h1, h⟩ := bindI_ok h
    intro c' hc'
    rcases List.mem_cons.1 hc' with rfl | hc'
    · unfold InLean.checkSumCtorC at h1
      obtain ⟨_, _, h0, _⟩ := bindI_ok h1
      exact checkConstantValC_fresh h0
    · exact checkSumCtorsF_fresh h c' hc'

/-- **The constructors' names are fresh in Lean's environment**, read off an
accepted constructors' stage (each constructor's `checkConstantValC`). -/
theorem checkBlockCtorsF_fresh {mode : InLean.CheckMode} {fe₀ fe : InLean.FEnv}
    {p : InLean.BlockShape} :
    ∀ {l : List InLean.MemberShape} {s₀ s' : InLean.CState} {u : Unit},
      InLean.checkBlockCtorsC mode fe₀ fe p l s₀ = .ok (u, s') →
      ∀ ms ∈ l, ∀ c ∈ ms.ctors, fe.env.find? c.1.name = none
  | [], _, _, _, _ => by simp
  | ms :: rest, s₀, s', u, h => by
    unfold InLean.checkBlockCtorsC at h
    obtain ⟨_, _, h1, h⟩ := bindI_ok h
    intro m hm
    rcases List.mem_cons.1 hm with rfl | hm
    · exact checkSumCtorsF_fresh h1
    · exact checkBlockCtorsF_fresh h m hm

/-- Master's constructors' stage stores closed constructor types. -/
theorem checkBlockCtors_lbb {env₀ env : ConLeche.Env} {q : ConLeche.BlockShape}
    {l : List ConLeche.MemberShape}
    (h : Runs (ConLeche.checkBlockCtors (ConLeche.fueledOpsM .verified) env₀ env q l) ()) :
    ∀ ms ∈ l, ∀ c ∈ ms.ctors, c.1.type.looseBVarsBounded 0 = true := by
  obtain ⟨F, hF⟩ := h
  rw [ConLeche.checkBlockCtors_datF] at hF
  obtain ⟨_, -, hall⟩ := ConLeche.checkBlockCtors_inv hF
  intro ms hms c hc
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hms
  obtain ⟨sortss, -, hcs⟩ := hall i ms hi
  obtain ⟨hlenC, -, hallc⟩ := hcs
  obtain ⟨j, hj⟩ := List.getElem?_of_mem hc
  obtain ⟨-, sorts, -, hrun⟩ := hallc j c c hj hj
  exact (ConLeche.direct_sum_ctor_typeWF hrun).2.2.2.1

/-- Master's constructors' stage: the constructors fresh, their push well formed. -/
theorem checkBlockCtors_push {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
    {q : ConLeche.BlockShape} {l : List ConLeche.MemberShape} {nP : Nat}
    (h : Runs (ConLeche.checkBlockCtors (ConLeche.fueledOpsM .verified) env env q l) ()) :
    ConLeche.EnvWF (ConLeche.consBlockCtors nP (l.map fun ms => (ms.cvT.name, ms.ctors)) env) := by
  obtain ⟨F, hF⟩ := h
  rw [ConLeche.checkBlockCtors_datF] at hF
  obtain ⟨_, hR⟩ := ConLeche.checkBlockCtors_inv hF
  exact ConLeche.direct_block_ctors_wf henv hR

/-- **Master's classes are at the block's parameters**, an outside class's
parameters closed and below them. -/
theorem checkBlockClasses_facts {fe₁ : ConLeche.FEnv} {p : ConLeche.BlockShape}
    {params : List ConLeche.Expr} {rd : ConLeche.ClassRead} {Ms : List ConLeche.TargetMajor}
    (h : Runs (ConLeche.checkBlockClasses (ConLeche.fueledOpsM .verified) fe₁ p params) (rd, Ms)) :
    ∀ M ∈ Ms, M.pfvs = params ∧
      (M.member = none → ∀ x ∈ M.ds, x.bvarB = 0 ∧ x.fvarB ≤ p.nP) := by
  obtain ⟨F, hF⟩ := h
  rw [ConLeche.checkBlockClasses_datF] at hF
  obtain ⟨R⟩ := ConLeche.checkBlockClasses_run hF
  obtain ⟨hlen, hall⟩ := ConLeche.classMajors_run R.hMs
  intro M hM
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hM
  have hik : i < R.keys.length := by
    rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
  obtain ⟨M', hM', ⟨C⟩⟩ := hall i _ (List.getElem?_eq_getElem hik)
  rw [hi] at hM'
  obtain rfl := Option.some.inj hM'
  have hp := (ConLeche.targetMajorOf_run C.hmaj).2
  refine ⟨hp, fun hn => ?_⟩
  cases C.major with
  | member I t ms hfn ht hms hpar' nfs => exact nomatch hn
  | outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hment hinst hsort nfs =>
    exact hdsSc

/-- **Master's walk context's parameters**: one variable per parameter, the
`j`-th at index `j`. -/
theorem blockNestCtx_params {P : ConLeche.BlockShape}
    {find? : ConLeche.Name → Option ConLeche.ConstantInfo} {ctx : ConLeche.NestCtx}
    {holes : List ConLeche.Expr}
    (h : Runs (ConLeche.blockNestCtx (m := ConLeche.FueledM) P find?) (ctx, holes)) :
    ctx.params.length = P.nP ∧ ∀ (j : Nat) x, ctx.params[j]? = some x → ∃ ty, x = .fvar j ty := by
  obtain ⟨F, hF⟩ := h
  rw [ConLeche.blockNestCtx_datF] at hF
  obtain ⟨cvTa0, fvsP, rest, -, hop, rfl, -⟩ := ConLeche.blockNestCtx_inv hF
  refine ⟨ConLeche.Verify.openPisAtFvars_length _ hop, fun j x hx => ?_⟩
  obtain ⟨ty, he⟩ := ConLeche.openPisAtFvars_index _ _ _ hop j x hx
  exact ⟨ty, by simpa using he⟩

theorem trCR_mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {rd : InLean.ClassRead}
    (hok : ∀ x ∈ rd.slots, OkSlot s₀ x) : trCR s₁ rd = trCR s₀ rd := by
  simp only [trCR]
  congr 1
  exact List.map_congr_left fun x hx => trSlot_mono h (hok x hx)

theorem nestOutKinds_tr (s : InLean.CState)
    (outs : List (List (List InLean.NestFieldKind × Lean.Expr))) :
    ConLeche.nestOutKinds (outs.map (trOuts s)) =
      (InLean.nestOutKinds outs).map (·.map (·.map trNK)) := by
  simp [ConLeche.nestOutKinds, InLean.nestOutKinds, trOuts, Function.comp_def]

/-- **The seeds are scoped and closed** (master's facts, as in
`genScoped_of_run`): each outside class's parameters, moved to the walk's
context, are scoped at its root and closed. -/
theorem classSeeds_scoped {cctx : ConLeche.NestCtx} {H : List ConLeche.Expr}
    {Msc : List ConLeche.TargetMajor} (hh : ConLeche.nestHoles cctx = some H)
    (hlen : cctx.params.length = cctx.nP)
    (hparF : ∀ a ∈ cctx.params, ∃ i ty, a = .fvar i ty)
    (hparW : ∀ x ∈ cctx.params, ConLeche.Expr.WScoped (cctx.hiAt 0) x)
    (hHW : ∀ x ∈ H, ConLeche.Expr.WScoped (cctx.hiAt 0) x)
    (hMs : ∀ M ∈ Msc, M.member = none → ∀ x ∈ M.ds, x.bvarB = 0 ∧ x.fvarB ≤ cctx.nP) :
    ∀ k ∈ ConLeche.classSeeds cctx H Msc, ∀ y ∈ k.1.ds,
      ConLeche.Expr.WScoped (cctx.hiAt 0) y ∧ y.looseBVarsBounded 0 = true := by
  intro k hk y hy
  obtain ⟨M, hM, hMn, rfl⟩ := mem_classSeeds hk
  have hds := hMs M hM hMn
  refine ⟨(ConLeche.nestSeedOf_ds hh hlen (fun x hx => ConLeche.Expr.fvarB_le (hds x hx).2) y hy).2
    hHW hparW, ?_⟩
  exact ConLeche.nestSeedOf_closed hh hparF (fun x hx => lbb_of_bvarB (hds x hx).1) y hy

/-! ## Master's side: the major domain's head -/

/-- A class is a member exactly when its inductive is one of the block's
member names. -/
def ClassHead (p : ConLeche.BlockShape) (M : ConLeche.TargetMajor) : Prop :=
  p.memberNames.contains M.ind = M.member.isSome

/-- `targetMajorOf`'s two arms: a member at a member name, an outside
class at a name of none. -/
theorem TargetMajorRun.classHead {ops : ConLeche.CheckerOps ConLeche.CheckM} {fe : ConLeche.FEnv}
    {p : ConLeche.BlockShape} {pfvs fvs : List ConLeche.Expr} {mty : ConLeche.Expr}
    {M : ConLeche.TargetMajor} (R : ConLeche.TargetMajorRun ops fe p pfvs fvs mty M) :
    ClassHead p M := by
  unfold ClassHead
  cases R with
  | member I t ms hfn ht =>
    have : (p.memberNames.findIdx? (· == I)).isSome = true := by rw [ht]; rfl
    rw [List.findIdx?_isSome, List.any_eq_true] at this
    obtain ⟨x, hx, he⟩ := this
    simp only [beq_iff_eq] at he
    subst he
    simpa using hx
  | outside I us nPc nIdx ctors sI hfn ht =>
    rw [List.findIdx?_eq_none_iff] at ht
    simp only [Option.isSome_none]
    cases hc : p.memberNames.contains I with
    | false => rfl
    | true =>
      have hI : I ∈ p.memberNames := by simpa using hc
      have := ht I hI
      simp at this


/-! ## The classes, for the tail (lane TailSim) -/

/-- An outside inductive's constructors (`targetCtorsOf`) have closed readings:
they are the environment's (`nestContainer_ctorOk` at the empty context). -/
theorem targetCtorsOf_ctorOk {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    {I : Lean.Name} {q : Nat × List (Lean.ConstantVal × Nat)}
    (h : InLean.targetCtorsOf fe I = some q) : ∀ c ∈ q.2, CtorOkI c := by
  unfold InLean.targetCtorsOf InLean.nestContainer at h
  split at h
  · rename_i cv caps _
    have hall : ∀ x ∈ caps.ctors.filterMap (fun n =>
        (fe.ctorView? n).bind fun (cv, nPc, nF, _) => InLean.nestCtorEntry I cv nPc nF),
        CtorOkI (x.1, x.2.2) := by
      intro x hx
      obtain ⟨n, -, hn⟩ := List.mem_filterMap.1 hx
      cases hv : fe.ctorView? n with
      | none => rw [hv] at hn; cases hn
      | some p =>
        obtain ⟨cv', nPc, nF⟩ := p
        rw [hv] at hn
        simp only [Option.bind_some] at hn
        have hx1 : x.1 = cv' := by
          unfold InLean.nestCtorEntry at hn
          split at hn
          · split at hn
            · split at hn
              · simp only [Option.some.injEq] at hn; rw [← hn]
              · cases hn
            · cases hn
          · cases hn
        obtain ⟨ccv, hcv, hL⟩ := ctorView_rel hJ.pres hv
        have he := hcv.eq_trCV
        subst he
        have hwf := hJ.wf.consts _ (ConLeche.Env.find?_mem hL)
        rw [hx1]
        exact ⟨(trC_of_toExprC hcv.2.2.2.2 hcv.2.2.2.1).1, hwf.1, hwf.2.2.2.1⟩
    simp only at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      simp
    · simp only [Option.some.injEq] at h
      subst h
      rename_i heq
      intro c hc
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
      exact hall x (by simpa [heq] using hx)
  · cases h

/-- **A major's constructors** (InLean's `targetMajorOf`): a member's are the
member's, an outside inductive's its stored ones. -/
theorem targetMajorOf_ctors {mode : InLean.CheckMode} {fe : InLean.FEnv} {p : InLean.BlockShape}
    {pfvs fvs : List Lean.Expr} {mty : Lean.Expr} {s₀ s' : InLean.CState} {M : InLean.TargetMajor}
    (h : InLean.targetMajorOf mode fe p pfvs fvs mty s₀ = .ok (M, s')) :
    (M.member = none → ∃ I q, InLean.targetCtorsOf fe I = some q ∧ M.ctors = q.2) ∧
      ∀ t, M.member = some t → ∃ ms, p.members[t]? = some ms ∧ M.ctors = ms.ctors := by
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM InLean.TargetMajor}
      {s : InLean.CState}, ¬ ((throw e : InLean.CheckCM α) >>= k) s = .ok (M, s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  unfold InLean.targetMajorOf at h
  cases hg : mty.getAppFnT with
  | const I us =>
    simp only [hg] at h
    cases hfi : p.memberNames.findIdx? (· == I) with
    | some t =>
      simp only [hfi] at h
      obtain ⟨ms, s₁, h1, h⟩ := bind_run h
      obtain ⟨hms, -⟩ := unwrapOrI_run h1
      split at h
      · obtain ⟨rfl, -⟩ := pure_run h
        refine ⟨fun h => by simp at h, fun t' ht' => ?_⟩
        simp only [Option.some.injEq] at ht'
        subst ht'
        exact ⟨ms, hms, rfl⟩
      · exact absurd h hth
    | none =>
      simp only [hfi] at h
      split at h
      · exact absurd h hth
      · cases hct : InLean.targetCtorsOf fe I with
        | none => simp only [hct] at h; exact (throw_run h).elim
        | some q =>
          obtain ⟨nPc, ctors⟩ := q
          simp only [hct] at h
          split at h
          · split at h
            · obtain ⟨⟨nIdx, sI⟩, s₁, h1, h⟩ := bind_run h
              obtain ⟨b, s₂, h2, h⟩ := bind_run h
              split at h
              · obtain ⟨rfl, -⟩ := pure_run h
                exact ⟨fun _ => ⟨I, _, hct, rfl⟩, fun t ht => by simp at ht⟩
              · exact absurd h hth
            · exact absurd h hth
          · exact absurd h hth
  | _ => simp only [hg] at h; exact (throw_run h).elim

/-- **The classes' constructors and member indices** (InLean's `classMajors`). -/
theorem classMajors_ctors {mode : InLean.CheckMode} {fe : InLean.FEnv} {p : InLean.BlockShape}
    {pfvs : List Lean.Expr} :
    ∀ {keys : List InLean.ClassKey} {s₀ s' : InLean.CState} {Ms : List InLean.TargetMajor},
      InLean.classMajors mode fe p pfvs keys s₀ = .ok (Ms, s') → ∀ M ∈ Ms,
        (M.member = none → ∃ I q, InLean.targetCtorsOf fe I = some q ∧ M.ctors = q.2) ∧
        ∀ t, M.member = some t → ∃ ms, p.members[t]? = some ms ∧ M.ctors = ms.ctors
  | [], s₀, s', Ms, h => by
    unfold InLean.classMajors at h
    obtain ⟨rfl, -⟩ := pure_run h
    simp
  | key :: keys, s₀, s', Ms, h => by
    unfold InLean.classMajors at h
    obtain ⟨M, s₁, h1, h⟩ := bind_run h
    obtain ⟨_, s₂, _, h⟩ := bind_run h
    obtain ⟨Ms', s₃, h3, h⟩ := bind_run h
    obtain ⟨rfl, -⟩ := pure_run h
    intro M' hM'
    rcases List.mem_cons.1 hM' with rfl | hM'
    · exact targetMajorOf_ctors h1
    · exact classMajors_ctors h3 M' hM'

/-- **The classes' constructors and member indices** (InLean's
`checkBlockClasses`). -/
theorem checkBlockClasses_ctors {mode : InLean.CheckMode} {fe : InLean.FEnv}
    {p : InLean.BlockShape} {params : List Lean.Expr} {s₀ s' : InLean.CState}
    {rd : InLean.ClassRead} {Ms : List InLean.TargetMajor}
    (h : InLean.checkBlockClasses mode fe p params s₀ = .ok ((rd, Ms), s')) : ∀ M ∈ Ms,
      (M.member = none → ∃ I q, InLean.targetCtorsOf fe I = some q ∧ M.ctors = q.2) ∧
      ∀ t, M.member = some t → ∃ ms, p.members[t]? = some ms ∧ M.ctors = ms.ctors := by
  unfold InLean.checkBlockClasses at h
  obtain ⟨o, s₁, h1, h⟩ := bind_run h
  obtain ⟨rd', s₂, h2, h⟩ := bind_run h
  obtain ⟨keys, s₃, h3, h⟩ := bind_run h
  obtain ⟨Ms', s₄, h4, h⟩ := bind_run h
  have hc := classMajors_ctors h4
  simp only at h
  split at h
  · obtain ⟨he, -⟩ := pure_run h
    cases he
    exact hc
  · obtain ⟨_, _, h5, -⟩ := bind_run h
    exact (throw_run h5).elim

theorem motPosOf_length_classes : ∀ (slots : List ConLeche.ClassSlot),
    (ConLeche.ClassRead.motPosOf slots).length = (ConLeche.ClassRead.mk slots []).classes.length
  | [] => rfl
  | x :: rest => by
    have h := ConLeche.ClassRead.motPosOf_append [x] rest
    simp only [List.singleton_append] at h
    rw [h, List.length_append, List.length_map, motPosOf_length_classes rest]
    unfold ConLeche.ClassRead.classes
    cases x <;> simp [ConLeche.ClassRead.motPosOf] <;> omega

/-- Every recursor's class, as master's pre-pass reads it, is a motive ordinal. -/
theorem classRead_recCls_lt {nP : Nat} {nPc : ConLeche.Name → Nat} {recs : List ConLeche.RecShape}
    {rd : ConLeche.ClassRead} (h : ConLeche.classRead nP nPc recs = some rd) :
    ∀ c ∈ rd.recCls, c < (ConLeche.ClassRead.motPosOf rd.slots).length := by
  unfold ConLeche.classRead at h
  obtain ⟨rc0, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨_, body⟩, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨slots, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨recCls, hrc, h⟩ := Option.bind_eq_some_iff.mp h
  simp only [Option.pure_def, Option.some.injEq] at h
  subst h
  intro c hc
  obtain ⟨rc, -, hf⟩ := ConLeche.option_mapM_mem hrc c hc
  obtain ⟨⟨_, concl⟩, -, hf⟩ := Option.bind_eq_some_iff.mp hf
  simp only at hf
  split at hf
  · exact ConLeche.classOfMotiveVar_lt hf
  · exact nomatch hf

/-- **Master's classes, for the tail**: an outside class's parameters the block's
(`ClassOutParams`), a class a member exactly at a member name (`ClassHead`), its
parameters closed, every recursor's class in range, one class per motive. -/
theorem checkBlockClasses_tailFacts {fe₁ : ConLeche.FEnv} {p : ConLeche.BlockShape}
    {params : List ConLeche.Expr} {rd : ConLeche.ClassRead} {Ms : List ConLeche.TargetMajor}
    (h : Runs (ConLeche.checkBlockClasses (ConLeche.fueledOpsM .verified) fe₁ p params) (rd, Ms))
    (hpc : ∀ x ∈ params, x.looseBVarsBounded 0 = true) :
    (∀ M ∈ Ms, ConLeche.ClassOutParams p.nP M ∧ ClassHead p M ∧
      ∀ x ∈ M.ds, x.looseBVarsBounded 0 = true) ∧
    (∀ c ∈ rd.recCls, c < Ms.length) ∧ (ConLeche.ClassRead.motPosOf rd.slots).length = Ms.length := by
  obtain ⟨F, hF⟩ := h
  rw [ConLeche.checkBlockClasses_datF] at hF
  obtain ⟨R⟩ := ConLeche.checkBlockClasses_run hF
  obtain ⟨hlen, hall⟩ := ConLeche.classMajors_run R.hMs
  have hkl := ConLeche.mapM_ok_length R.hkeys
  have hmp : (ConLeche.ClassRead.motPosOf rd.slots).length = Ms.length := by
    rw [motPosOf_length_classes, hlen, hkl]; rfl
  refine ⟨fun M hM => ?_, fun c hc => ?_, hmp⟩
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hM
    have hik : i < R.keys.length := by
      rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hi).1
    obtain ⟨M', hM', ⟨C⟩⟩ := hall i _ (List.getElem?_eq_getElem hik)
    rw [hi] at hM'
    obtain rfl := Option.some.inj hM'
    have hH := TargetMajorRun.classHead C.major
    refine ⟨?_, hH, ?_⟩
    · intro hn
      cases C.major with
      | member I t ms hfn ht hms hpar' nfs => exact nomatch hn
      | outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hment hinst hsort nfs =>
        exact ⟨hdsLen, hdsSc⟩
    · cases C.major with
      | member I t ms hfn ht hms hpar' nfs =>
        intro x hx
        exact hpc x (List.mem_of_mem_take hx)
      | outside I us nPc nIdx ctors sI hfn ht hnq hctors hdsLen hdsSc hment hinst hsort nfs =>
        intro x hx
        exact lbb_of_bvarB (hdsSc x hx).1
  · rw [← hmp]
    exact classRead_recCls_lt R.hrd c hc

/-! ## The relation's data -/

/-- **The pass's data** (`PassRelI`'s `D`): the field kinds, the class
reading, the classes and the table, each master's by its translation at `s`;
and what the tail's stages read of the pass: the readings' facts (the slots,
the classes, the table's entries), the parameters (readable, one variable per
parameter, scoped below the parameter count, closed), every class at the
block's parameters (its frame, `PassDataI.frameOk`), the members' and
constructors' types closed, the stream recursors' types closed, the
constructors' names fresh at the formers' environment, distinct and not
`sorryAx` unless `coreAxioms` (`jobEnvI_ctors`'s premises), master's
environment with them pushed well formed, and the table's entries closed
(master's `checkBlockPositivity_nfScoped` and `nestSeeds_nfScoped` on its
side of the run); and for the tail (lane TailSim): the result sort's reading,
the members' names, the shape facts (`TailShapeOkI`), the classes' constructors
closed and member indices in range (`checkBlockClasses_ctors`), master's classes'
`ClassOutParams`, `ClassHead` and closed parameters, the recursors' classes in
range and one class per motive (`checkBlockClasses_tailFacts`). -/
structure PassDataI (s : InLean.CState) (q : InLean.BlockPass) (cq : ConLeche.BlockPass ConLeche.Env) :
    Prop where
  kinds : cq.kinds = q.kinds.map (·.map (·.map trNK))
  rd : cq.rd = trCR s q.rd
  cls : cq.cls = q.cls.map (trTM s)
  tbl : cq.tbl = q.tbl.map (trNf s)
  slotsOk : ∀ x ∈ q.rd.slots, OkSlot s x
  clsOk : ∀ M ∈ q.cls, OkTM s M
  tblOk : ∀ e ∈ q.tbl.toList, OkNf s e
  paramsOk : OkSL s q.params = true
  paramsLen : q.params.length = q.p.nP
  paramsVar : ∀ (j : Nat) x, (TrSL s q.params)[j]? = some x → ∃ ty, x = .fvar j ty
  paramsW : ∀ a ∈ q.params,
    ConLeche.Expr.WScoped q.p.nP (TrS s a) ∧ (TrS s a).looseBVarsBounded 0 = true
  clsPfvs : ∀ M ∈ q.cls, TrSL s M.pfvs = TrSL s q.params
  members : ∀ ms ∈ q.p.members, MemberOk ms ∧ (trC ms.cvT.type).looseBVarsBounded 0 = true
  ctors : ∀ cs ∈ q.p.memberCtors, ∀ c ∈ cs, CtorOkI c
  recs : ∀ rc ∈ q.p.recs, okC rc.cvR.type = true ∧ (trC rc.cvR.type).looseBVarsBounded 0 = true
  ctorsFresh : ∀ ms ∈ q.p.members, ∀ c ∈ ms.ctors, q.env₁.env.find? c.1.name = none
  ctorsWF : ConLeche.EnvWF (ConLeche.consBlockCtors cq.p.nP cq.p.ctorGroups cq.env₁)
  tblCl : ∀ e ∈ q.tbl.toList, (TrS s e.ty).looseBVarsBounded 0 = true
  ctorsNodup : (ctorNamesOf q.p.members).Nodup
  ctorsSorry : ∀ m ∈ q.p.members, ∀ c ∈ m.ctors, c.1.name = InLean.sorryAxName →
    q.env₁.coreAxioms = true
  sortOk : okL q.p.resSort = true
  names : ∀ ms ∈ q.p.members, ms.cvT.name = ms.declared.name
  shape : TailShapeOkI q.p
  clsCtors : ∀ M ∈ q.cls, ∀ c ∈ M.ctors, CtorOkI c
  clsMember : ∀ M ∈ q.cls, ∀ t, M.member = some t → t < q.p.members.length
  clsMaster : ∀ M ∈ cq.cls, ConLeche.ClassOutParams cq.p.nP M ∧ ClassHead cq.p M ∧
    ∀ x ∈ M.ds, x.looseBVarsBounded 0 = true
  recCls : ∀ c ∈ cq.rd.recCls, c < cq.cls.length
  motives : (ConLeche.ClassRead.motPosOf cq.rd.slots).length = cq.cls.length

/-- **A class's frame** (`FrameOk`, the recursor stage's hypothesis at every
class): its parameters are the block's, scoped at their count and closed; the
formers' types closed. -/
theorem PassDataI.frameOk {s : InLean.CState} {q : InLean.BlockPass}
    {cq : ConLeche.BlockPass ConLeche.Env} (h : PassDataI s q cq) {M : InLean.TargetMajor}
    (hM : M ∈ q.cls) : FrameOk (TrSL s M.pfvs) (TrSL s (q.p.formers.map (·.type))) := by
  rw [h.clsPfvs M hM]
  refine ⟨fun x hx => ?_, fun t ht => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    rw [TrSL_length, h.paramsLen]
    exact h.paramsW a ha
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.1 he
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.1 hcv
    obtain ⟨hok, hcl⟩ := h.members ms hms
    rw [TrS_of_okC _ hok.1]
    exact ⟨trC_wscoped 0 _, hcl⟩

/-! ## The pass -/

/-- **The pass** (`checkBlockPassS_run`'s twin) at `PassRelI PassDataI`, from
the former's constant check and its reduct. -/
theorem passSimI (hC : CheckConstantValCSimI) (hRF : ReducedFormerSimI) :
    PassSimI (PassRelI PassDataI) := by
  intro fe L p₀ isRec q s₀ s' hJ hs hms hrecs hpre h
  unfold InLean.checkBlockPassS at h
  -- the formers
  obtain ⟨⟨fe₁, p₁⟩, s₁, h1, h⟩ := bindI_ok h
  have hfr := checkBlockIndsF_fresh h1
  obtain ⟨hs₁, -, s0, hl0, rfl, hfe₁, hclF, hR1⟩ :=
    checkBlockIndsFI_run hC hJ hs (fun ms hms' => (hms ms hms').1) h1
  have hJ₁ := jobEnvI_formers hJ hpre hms hfr hR1
  have hpend : ∃ rest, fe₁.pending = InLean.blockMarks (p₀.withSort s0) ++ rest :=
    ⟨fe.pending, by rw [hfe₁, consBlockIndsF_pending]⟩
  have hca : fe₁.coreAxioms = fe.coreAxioms := by rw [hfe₁, consBlockIndsF_coreAxioms]
  rw [← hfe₁] at hJ₁
  generalize ConLeche.consBlockInds (trShape (p₀.withSort s0)) isRec
    ((trShape p₀).members.map (·.declared)) 0 L = E₁ at hJ₁ hR1
  clear hfe₁
  generalize hp₁ : p₀.withSort s0 = p₁ at *
  have hmem : p₁.members = p₀.members := by rw [← hp₁]; rfl
  have hrecs' : p₁.recs = p₀.recs := by rw [← hp₁]; rfl
  have hsr : okL p₁.resSort = true := by rw [← hp₁]; exact hl0
  rw [← hmem] at hms hclF
  rw [← hrecs'] at hrecs
  -- the flush
  obtain ⟨u0, sB, hfl, h⟩ := bindI_ok h
  rw [flushI_run] at hfl
  injection hfl with hfl
  obtain rfl : s₁.flushed = sB := congrArg Prod.snd hfl
  have hsB := flushI_csoki hs₁.residue .verified false E₁
  -- the constructors
  obtain ⟨_, s₂, h2, h⟩ := bindI_ok h
  have hcfr := checkBlockCtorsF_fresh h2
  obtain ⟨hs₂, ht₂, hR2⟩ := checkBlockCtorsFI_run hC hJ₁ hsr hsB
    (fun ms hm => ⟨(hms ms hm).1, hclF ms hm, (hms ms hm).2.2⟩) h2
  have hctl := checkBlockCtors_lbb hR2
  have hct : ∀ cs ∈ p₁.memberCtors, ∀ c ∈ cs, CtorOkI c := by
    intro cs hcs c hc
    obtain ⟨ms, hms', rfl⟩ := List.mem_map.1 hcs
    refine ⟨(hms ms hms').2.2 c hc, trC_hasFvar _, ?_⟩
    exact hctl (trMember ms) (List.mem_map_of_mem hms') (trCtor c) (List.mem_map_of_mem hc)
  -- the walk's context
  obtain ⟨⟨ctx, holes⟩, s₃, h3, h⟩ := bindI_ok h
  simp only at h
  obtain ⟨hs₃, ht₃, fvs, rfl, hokf, hokh, hclf, hwf, hholes, hR3⟩ :=
    blockNestCtxI_run E₁.find? hs₂ (fun ms hm => ⟨(hms ms hm).1, hclF ms hm⟩) h3
  generalize hc : (trShape p₁).nestCtx (TrSL s₃ fvs) E₁.find? = cctx at hholes hR3
  have hcp : cctx.params = TrSL s₃ fvs := by rw [← hc]; rfl
  have hcnP : cctx.nP = p₁.nP := by rw [← hc]; rfl
  obtain ⟨hcl, hcv⟩ := blockNestCtx_params hR3
  have hlenf : fvs.length = p₁.nP := by
    rw [← TrSL_length (s := s₃), ← hcp, hcl]; rfl
  have hCR : CanonRel (p₁.nestCtx fvs fe₁) cctx := by
    subst hc
    exact ⟨trShape_memberNames p₁, trShape_lps p₁, rfl⟩
  -- the classes
  obtain ⟨⟨rd, Ms⟩, s₄, h4, h⟩ := bindI_ok h
  simp only at h
  obtain ⟨hs₄, ht₄, hslots, hMs, hR4⟩ := checkBlockClassesI_run hJ₁ hRF hsr hrecs hs₃ hokf
    (fun i x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 (List.mem_of_getElem? hx)
      exact hwf a ha)
    (by rw [hlenf]; exact Nat.le_refl _) h4
  -- the block's positivity
  obtain ⟨⟨outs, pos⟩, s₅, h5, h⟩ := bindI_ok h
  simp only at h
  obtain ⟨hs₅, ht₅, hos, hst, hR5⟩ := checkBlockPositivityI_run hJ₁ hRF hs₄
    (fun ms hm => ⟨(hms ms hm).1, hclF ms hm⟩) hct hsr h5
  -- the seeds
  have ht35 := ht₄.trans ht₅
  have hMs₅ : ∀ M ∈ Ms, OkTM s₅ M := fun M hM => (OkTM.mono ht₅ (hMs M hM)).1
  have hMtr : Ms.map (trTM s₅) = Ms.map (trTM s₄) :=
    List.map_congr_left fun M hM => (OkTM.mono ht₅ (hMs M hM)).2
  obtain ⟨ks, s₆, h6, h⟩ := bindI_ok h
  obtain ⟨hs₆, ht₆, hks, hkeq⟩ := classSeedsI_run hCR hs₅
    (by rw [hcp]; exact (TrSL_of_tabLe ht35 hokf).symm) (okSL_of_tabLe ht35 hokf)
    (okSL_of_tabLe ht35 hokh) hMs₅ h6
  rw [TrSL_of_tabLe ht35 hokh, hMtr] at hkeq
  -- the context's facts on master's side
  have hctxOk : ConLeche.NestCtxOk cctx := by
    subst hc
    refine ⟨fun n ci hf => (hJ₁.wf.consts ci (List.mem_of_find?_eq_some hf)).1, fun cv hcv => ?_⟩
    simp only [ConLeche.BlockShape.nestCtx, trShape, List.map_map, List.mem_map] at hcv
    obtain ⟨ms, -, rfl⟩ := hcv
    exact trC_hasFvar _
  have hparN : ∀ x ∈ cctx.params, ConLeche.Expr.WScoped cctx.nP x := by
    rw [hcp, hcnP]
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hwf a ha
  have hHok := ConLeche.nestHoles_ok hctxOk hparN hholes
  have hseedsC := classSeeds_scoped hholes (by rw [hcl, hcnP]; rfl)
    (fun a ha => by
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ha
      obtain ⟨ty, he⟩ := hcv j _ (List.getElem?_eq_getElem hj)
      exact ⟨j, ty, he⟩)
    (fun x hx => ConLeche.Expr.WScoped.mono (by simp [ConLeche.NestCtx.hiAt]) (hparN x hx))
    (fun x hx => (hHok x hx).1)
    (Msc := Ms.map (trTM s₄)) (fun M hM hn x hx => by
      rw [hcnP, ← trShape_nP]
      exact (checkBlockClasses_facts hR4 M hM).2 hn x hx)
  have hseeds : ∀ k ∈ ks, SeedOkI s₆ ((p₁.nestCtx fvs fe₁).hiAt 0) k := by
    intro k hk
    refine ⟨(hks k hk).1, fun a ha => ?_⟩
    have hmem : (trKey s₆ k.1, k.2) ∈ ConLeche.classSeeds cctx (TrSL s₃ holes) (Ms.map (trTM s₄)) := by
      rw [hkeq]; exact List.mem_map_of_mem (f := fun q => (trKey s₆ q.1, q.2)) hk
    have hy := hseedsC _ hmem (TrS s₆ a) (by simp only [trKey, TrSL]; exact List.mem_map_of_mem ha)
    rw [hiAt_rel hCR] at hy
    exact ⟨by simp only [OkSL, List.all_eq_true] at hks; exact (hks k hk).2 a ha, hy.1, hy.2⟩
  -- the seeds walked
  have ht36 := ht35.trans ht₆
  have hW : WalkRel fe₁ E₁ s₆ (p₁.nestCtx fvs fe₁) cctx := by
    refine { canon := hCR, fe := rfl, find := by rw [← hc]; rfl, sort := by rw [← hc]; rfl,
             sortOk := hsr, nIdxs := by rw [← hc]; exact trShape_nIdxs p₁, params := ?_,
             paramsOk := okSL_of_tabLe ht36 hokf, paramsCl := closed_of_tabLe ht36 hokf hclf }
    rw [hcp]; exact (TrSL_of_tabLe ht36 hokf).symm
  obtain ⟨hst₆, hstr₆⟩ := StOk.mono ht₆ hst
  obtain ⟨st, s₇, h7, h⟩ := bindI_ok h
  obtain ⟨hs₇, ht₇, hst₇, hR7⟩ := nestSeedsI_run hJ₁ hRF ks pos hs₆ hW hst₆ hseeds h7
  obtain ⟨rfl, rfl⟩ := pureI_ok h
  rw [hstr₆] at hR7
  -- the table closed (master's `genRun_tbl_scoped`, at the pass)
  have hMf : ∀ ms ∈ (trShape p₁).members, ms.cvT.type.hasFvar = false := by
    intro ms hm
    obtain ⟨m, -, rfl⟩ := List.mem_map.1 hm
    exact trC_hasFvar _
  have hTf : ∀ cv ∈ (trShape p₁).formers, ConLeche.ScB 0 cv.type := by
    intro cv hcv
    simp only [ConLeche.BlockShape.formers, trShape, List.map_map, List.mem_map] at hcv
    obtain ⟨m, hm, rfl⟩ := hcv
    exact ConLeche.ScB.of_closed (trC_hasFvar _) (hclF m hm) 0
  have hcf : ∀ cl ∈ (trShape p₁).memberCtors, ∀ c ∈ cl, ConLeche.ScB 0 c.1.type := by
    rw [trShape_memberCtors_trCtor]
    intro cl hcl c hc
    obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hcl
    obtain ⟨c0, hc0, rfl⟩ := List.mem_map.1 hc
    obtain ⟨-, hf, hb⟩ := hct _ (List.mem_map_of_mem hm) c0 hc0
    exact ConLeche.ScB.of_closed hf hb 0
  have hpos : ConLeche.NfStScoped (trShape p₁).nP (trSt s₅ pos) := by
    obtain ⟨F5, hF5⟩ := hR5
    rw [ConLeche.checkBlockPositivity_datF] at hF5
    exact ConLeche.checkBlockPositivity_nfScoped hJ₁.wf hMf hTf hcf ⟨_, hF5, rfl, rfl⟩
  have htblCl : ConLeche.NfStScoped cctx.nP (trSt s₇ st) := by
    obtain ⟨F7, hF7⟩ := hR7
    rw [ConLeche.nestSeeds_datF] at hF7
    have hcb := ConLeche.nestCtx_ok_of_envWF hJ₁.wf (trShape p₁) (TrSL s₃ fvs) hMf
    rw [hc] at hcb
    refine ConLeche.nestSeeds_nfScoped hcb.1 hcb.2
      (fun x hx => ⟨hparN x hx, ?_⟩)
      (fun d e w hw he => ConLeche.whnf_WScoped hJ₁.wf F7 hw he)
      (fun d e w hw he => ConLeche.whnf_looseBVars hJ₁.wf F7 hw he) _ _ _ hF7 ?_
      (by rw [hcnP]; exact hpos)
    · rw [hcp] at hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
      exact hclf a ha
    · rw [← hkeq]
      intro k hk y hy
      exact hseedsC k hk y hy
  -- master's pass
  have ht37 := ht36.trans ht₇
  have hRun : Runs (ConLeche.checkBlockPass (ConLeche.fueledOpsM .verified) L (trShape p₀) isRec)
      ⟨E₁, trShape p₁, ConLeche.nestOutKinds (outs.map (trOuts s₅)), cctx.params, trCR s₄ rd,
        Ms.map (trTM s₄), (trSt s₇ st).ctorNfs⟩ := by
    unfold ConLeche.checkBlockPass
    refine Runs.bind hR1 ?_
    dsimp only
    refine Runs.bind hR2 ?_
    refine Runs.bind hR3 ?_
    dsimp only
    rw [hcp]
    refine Runs.bind hR4 ?_
    dsimp only
    refine Runs.bind hR5 ?_
    dsimp only
    rw [← hcp, hkeq]
    refine Runs.bind hR7 ?_
    exact Runs.pure _
  obtain ⟨F, hF⟩ := hRun
  rw [ConLeche.checkBlockPass_datF] at hF
  refine ⟨F, _, hF, hs₇, ⟨⟨hpend, rfl, hJ₁⟩, ?_, ?_⟩, hmem, by rw [← hp₁]; rfl⟩
  · show cctx.params = fvs.map (TrS s₇)
    rw [hcp]; exact (TrSL_of_tabLe ht37 hokf).symm
  have ht47 := ht₅.trans (ht₆.trans ht₇)
  have hTr : TrSL s₇ fvs = TrSL s₃ fvs := TrSL_of_tabLe ht37 hokf
  have hclsF := checkBlockClasses_facts hR4
  have hcT := checkBlockClasses_tailFacts hR4 (fun x hx => by
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact hclf a ha)
  refine
    { kinds := nestOutKinds_tr s₅ outs
      rd := (trCR_mono ht47 hslots).symm
      cls := List.map_congr_left fun M hM => ((OkTM.mono ht47 (hMs M hM)).2).symm
      tbl := rfl
      slotsOk := fun x hx => OkSlot.mono ht47 (hslots x hx)
      clsOk := fun M hM => (OkTM.mono ht47 (hMs M hM)).1
      tblOk := fun e he => hst₇.2.2 e he
      paramsOk := okSL_of_tabLe ht37 hokf
      paramsLen := hlenf
      paramsVar := fun j x hx => hcv j x (by rw [hcp, ← hTr]; exact hx)
      paramsW := fun a ha => by
        have hoa : OkS s₃ a = true := by
          simp only [OkSL, List.all_eq_true] at hokf; exact hokf a ha
        rw [TrS_of_tabLe ht37 hoa]
        exact ⟨hwf a ha, hclf a ha⟩
      clsPfvs := fun M hM => by
        obtain ⟨-, -, hpf, -⟩ := hMs M hM
        rw [TrSL_of_tabLe ht47 hpf]
        show _ = TrSL s₇ fvs
        rw [hTr]
        exact (hclsF (trTM s₄ M) (List.mem_map_of_mem hM)).1
      members := fun ms hm => ⟨hms ms hm, hclF ms hm⟩
      ctors := hct
      recs := hrecs
      ctorsFresh := hcfr
      ctorsWF := checkBlockCtors_push hJ₁.wf hR2
      ctorsNodup := by rw [ctorNamesOf_allCtors, ← hp₁]; exact hpre.ctorsNodup
      tblCl := fun e he => by
        have := htblCl (trNf s₇ e) (by
          simp only [trSt, Array.toList_map]; exact List.mem_map_of_mem he)
        exact this.2
      ctorsSorry := fun m hm c hc hn => by
        rw [hmem] at hm
        exact hca ▸ hpre.ctorsSorry m hm c hc hn
      sortOk := hsr
      names := fun m hm => hpre.name m (hmem ▸ hm)
      shape := by
        rw [← hp₁]; exact ⟨hpre.shape.steps, hpre.shape.rules⟩
      clsCtors := fun M hM c hc => by
        obtain ⟨hout, hin⟩ := checkBlockClasses_ctors h4 M hM
        cases hmM : M.member with
        | none =>
          obtain ⟨I, q, hq, he⟩ := hout hmM
          exact targetCtorsOf_ctorOk hJ₁ hq c (he ▸ hc)
        | some t =>
          obtain ⟨ms, hms', he⟩ := hin t hmM
          exact hct _ (List.mem_map_of_mem (List.mem_of_getElem? hms')) c (he ▸ hc)
      clsMember := fun M hM t ht => by
        obtain ⟨ms, hms', -⟩ := (checkBlockClasses_ctors h4 M hM).2 t ht
        exact (List.getElem?_eq_some_iff.1 hms').1
      clsMaster := (hcT.1)
      recCls := hcT.2.1
      motives := hcT.2.2 }

end InLeanProof
