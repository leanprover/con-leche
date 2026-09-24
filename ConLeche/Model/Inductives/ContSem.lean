module

public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.ContN2
import ConLeche.SetTheory.Derive.Univ
import ConLeche.SetTheory.Derive.Graphs
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Rules.IotaSoundKit

public section

/-!
# The container case of the positivity theorem (lane CONTSEM, steps 5–6)

`ContSem` — the premise `nestPos_sem` takes for its container case —
PROVED, at the kind predicate `True` and the state invariant `CacheInv`
(every looked-up container's constructor list is the environment's, and
every cached instantiation without a frame hole grows along every hole
relation at the block's own depth), from the frame lemma (`frame_sem`,
`ContWalk.lean`), the container's leaf (`monoOn_of_famLe`, `ContLeaf.lean`)
and coverage (`ContCover`, L8: every stored inductive the walk may meet
as a container is a member of a recorded block whose constructors are
the ones `nestContainer` lists; a named premise until the flip records a
clause for every inductive).  So `nestMemberCtor_sem` holds without the
container premise (`nestMemberCtor_sem_cont`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey NestHole NestState
  NestKeyInfo NestFieldKind CheckError instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Coverage (L8, a named premise) -/

/-- A recorded block, as the container case reads it: its member names
distinct and recorded as their formers' `all`, and each member's
constructor list (`nestContainer`) its recorded constructors, in order,
at one parameter count. -/
structure ContBlockOk (env : Env) (ctx : NestCtx) (D : LfpDatum V) : Prop where
  nodup : D.names.Nodup
  all : ∀ mm, mm < D.k → ∀ cv caps, env.find? (D.member mm) = some (.indInfo cv caps) →
    caps.all = D.names
  ctors : ∀ c, c < D.k → ∃ nP' L, ConLeche.nestContainer ctx (D.member c) = some (nP', L) ∧
    L.length = D.nctors c ∧ ∀ j (hj : j < L.length),
      env.find? (D.ctorName c j) = some (.ctorInfo L[j].1 nP' L[j].2)
  /-- a member WITHOUT constructors (lane RESTRICT-FIX, finding C1): the
  parameter count `nestContainer` reads for it (its former's recorded
  `IndCaps.nparams`) is the block's, and its former's level parameters
  are distinct and the block's — what the first constructor's record
  says of a member with constructors (`LfpCtorReads`, the frame's
  `Name.nodup` check) -/
  noCtors : ∀ c, c < D.k → ∀ nP', ConLeche.nestContainer ctx (D.member c) = some (nP', []) →
    ∃ cv caps, env.find? (D.member c) = some (.indInfo cv caps) ∧ cv.levelParams.Nodup ∧
      (∀ ψ, (D.params ψ).length = nP') ∧
      ∀ mm, mm < D.k → ∃ cvm capsm, env.find? (D.member mm) = some (.indInfo cvm capsm) ∧
        cvm.levelParams = cv.levelParams

/-- **Coverage** (CONTSEM step 6, L8 owed): the walk's context reads the
environment, every stored inductive but `Quot` that is not a member of
the block being checked is a member of a recorded block, and every
recorded block is read as `ContBlockOk` says. -/
structure ContCover {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (ctx : NestCtx) : Prop where
  find : ∀ n, ctx.find? n = env.find? n
  cover : ∀ n cv caps, env.find? n = some (.indInfo cv caps) → ctx.names.contains n = false →
    n ≠ ConLeche.quotName → ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = n
  block : ∀ D ∈ mp.lfpBlocks, ContBlockOk env ctx D

/-! ## The cache invariant -/

/-- **A cached instantiation is positive** at the block's own depth: for
some recorded block holding its container (at the recorded parameter
count, the container's level parameters distinct), along every hole
relation without frames whose pairs satisfy the container's parameter
telescope at the key frames, the container's carrier grows between them;
and — exported for lane NESTIND (lane NESTKERN session 2) — the
per-constructor hole-fit transfer that growth is built from, at every
member of the frame's final group `grp` (`frameIter`, `ctor_transfer`). -/
@[expose] def KeyPos {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat)
    (ctx : NestCtx) (key : NestKey) : Prop :=
  ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = key.cname ∧
    ∀ cv caps, env.find? key.cname = some (.indInfo cv caps) →
      cv.levelParams.Nodup ∧
      (D.params (Level.substFn φ cv.levelParams key.lvls)).length = key.ds.length ∧
      ∀ (Δ0 : List AnnotTerm) (R00 : FrameRel V), HoleRel mp.base2 φ ctx [] (ctx.hiAt 0) Δ0 R00 →
        Δ0.length = ctx.hiAt 0 → (∀ x ∈ key.ds, CtxOkP mp.base2 φ (ctx.hiAt 0) Δ0 x) →
        ∀ dsa, DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt 0) key.ds dsa →
        (∀ ρ ρ', R00 ρ ρ' →
          Sat V (D.params (Level.substFn φ cv.levelParams key.lvls)).reverse
              (keyFrame dsa (ctx.hiAt 0) ρ) ∧
          Sat V (D.params (Level.substFn φ cv.levelParams key.lvls)).reverse
              (keyFrame dsa (ctx.hiAt 0) ρ')) →
        ∀ ρ ρ', R00 ρ ρ' →
          FamLe (D.idx (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ) mm)
            (D.carrier (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ) mm)
            (D.carrier (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ') mm)
          ∧ ∃ grp : List (Name × Expr), InGrp D grp mm ∧ ∀ g, InGrp D grp g → ∀ t j fs,
            D.HFits (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ)
              (grpTuple D (Level.substFn φ cv.levelParams key.lvls) grp
                (keyFrame dsa (ctx.hiAt 0) ρ) (keyFrame dsa (ctx.hiAt 0) ρ')) t g j fs →
            D.HFits (Level.substFn φ cv.levelParams key.lvls) (keyFrame dsa (ctx.hiAt 0) ρ')
              (D.carrier (Level.substFn φ cv.levelParams key.lvls)
                (keyFrame dsa (ctx.hiAt 0) ρ')) t g j fs

/-- **The cache invariant** (CONTSEM step 5). -/
@[expose] def CacheInv {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat)
    (ctx : NestCtx) (st : NestState) : Prop :=
  (∀ c r, st.ctorsOf.lookup c = some r → r = ConLeche.nestContainer ctx c) ∧
  ∀ ki ∈ st.keys.toList, (∀ x ∈ ki.key.ds, x.fvarB ≤ ctx.hiAt 0) → KeyPos mp φ ctx ki.key

theorem cacheInv_empty {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (ctx : NestCtx) :
    CacheInv mp φ ctx {} :=
  ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

theorem cacheInv_ctorsOfOk {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (ctx : NestCtx) :
    CtorsOfOk ctx (CacheInv mp φ ctx) where
  lookup := by
    intro st hst c
    unfold ConLeche.nestContainerC
    split
    · rename_i r hr; exact hst.1 c r hr
    · rfl
  insert := by
    intro st hst c
    unfold ConLeche.nestContainerC
    split
    · exact hst
    · refine ⟨fun c' r h => ?_, hst.2⟩
      simp only [List.lookup] at h
      split at h
      · rename_i heq
        simp only [Option.some.injEq] at h
        rw [← h]
        congr 1
        exact (beq_iff_eq.mp heq).symm
      · exact hst.1 c' r h
  mix := fun _ _ h₀ h => ⟨h.1, h₀.2⟩

/-! ## Pieces -/

/-- The key frame seen through empty frames on top. -/
theorem keyFrame_lift (dsa : List AnnotTerm) (h : Nat) (vs : List V) (ρ : Nat → V) :
    keyFrame (dsa.map (AnnotTerm.liftN vs.length · 0)) (h + vs.length) (consList vs ρ)
      = keyFrame dsa h ρ := by
  unfold keyFrame
  rw [List.map_map]
  congr 1
  · exact List.map_congr_left fun a _ => interp_liftN_consList vs ρ a
  · funext j
    rw [show j + (h + vs.length) = (j + h) + vs.length by omega, consList_apply_add]

/-- **Accepting the reached group-mates keeps the cache invariant**, given
each pushed instantiation's positivity. -/
theorem nestAcceptGroup_sem {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx}
    {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (st st' : NestState),
      ConLeche.nestAcceptGroup (m := CheckM) ctx hi us ds grp st = .ok st' →
      CacheInv mp φ ctx st →
      (∀ p ∈ grp, (∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) → KeyPos mp φ ctx ⟨p.1, us, ds⟩) →
      CacheInv mp φ ctx st'
  | [], st, st', h, hI, _ => by
    simp only [ConLeche.nestAcceptGroup, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hI
  | (c, ty) :: rest, st, st', h, hI, hk => by
    simp only [ConLeche.nestAcceptGroup, bind, Except.bind] at h
    split at h
    · split at h
      · simp at h
      rename_i q hq
      refine nestAcceptGroup_sem mp rest _ st' h ⟨hI.1, fun ki hki hfv => ?_⟩
        (fun p hp => hk p (List.mem_cons_of_mem _ hp))
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hki
      rcases hki with hki | rfl
      · exact hI.2 ki hki hfv
      · exact hk (c, ty) List.mem_cons_self hfv
    · exact nestAcceptGroup_sem mp rest st st' h hI (fun p hp => hk p (List.mem_cons_of_mem _ hp))

/-- A recorded block's names and members, from its record. -/
theorem lfp_namesLen {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) : D.names.length = D.k :=
  (mp.lfp_ok D hD).2.2.2.1

/-- The arguments' leaves are the application's. -/
theorem leaves_mkAppN_arg {l : Nat × Expr} :
    ∀ {xs : List Expr} {f x : Expr}, x ∈ xs → l ∈ x.fvarLeaves → l ∈ (Expr.mkAppN f xs).fvarLeaves
  | [], _, _, hx, _ => nomatch hx
  | y :: ys, f, x, hx, hl => by
    simp only [Expr.mkAppN]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact leaves_mkAppN_head (by simp [Expr.fvarLeaves, hl])
    · exact leaves_mkAppN_arg hx hl
where
  leaves_mkAppN_head : ∀ {xs : List Expr} {f : Expr}, l ∈ f.fvarLeaves →
      l ∈ (Expr.mkAppN f xs).fvarLeaves
    | [], _, h => h
    | y :: ys, f, h => by
      simp only [Expr.mkAppN]
      exact leaves_mkAppN_head (by simp [Expr.fvarLeaves, h])

section Case

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (hin : RulesInputs V mp.base2 φ)
  {ctx : NestCtx} (hcov : ContCover mp ctx) {F : Nat}
  {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
  (hrec : NestPosSem mp.base2 φ ctx (fun _ => True) (CacheInv mp φ ctx) rec)
  {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {n : Name}
  (hn : D.member mm = n) {lps : List Name}
  (hlps : ∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
  {us : List Level} (hul : us.length = lps.length) {prog : List NestHole} {ds : List Expr}
  (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true)
  (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
  (hlenP : ∀ ψ, (D.params ψ).length = ds.length)
  (hnL : (∃ L, ConLeche.nestContainer ctx n = some (ds.length, L) ∧ L ≠ []) ∨ lps.Nodup)
  (hsc : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
      Expr.WScoped (ctx.hiAt prog.length) x)

include hin hcov hrec hD hmm hn hlps hul hdsw hLds hlenP hnL hsc

/-- **The instantiations a frame accepts are positive** (the cache
invariant at a push): for every member of a frame's final group, with
the key's parameters below every frame hole — the frame lemma at any
hole relation without frames, extended by empty enclosing frames. -/
theorem keyPos_of_frame {cty : Expr} {grp' : List (Name × Expr)} {st₀ st₁ : NestState}
    (hrun : ConLeche.nestFrame ctx (fueledOps .verified F) env rec prog (ctx.hiAt prog.length) us ds
      ds.length (ConLeche.nestRestartFuel ctx n) [(n, cty)] st₀ = .ok (grp', st₁))
    (hc₁ : st₁.restart = none) (hI₀ : CacheInv mp φ ctx st₀)
    (hnI : ∃ nI, ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩
      = .ok (nI, cty))
    (hnd : lps.Nodup) (hg' : GrpOk ctx D (ctx.hiAt prog.length) us ds grp')
    (hfree : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) :
    ∀ p ∈ grp', KeyPos mp φ ctx ⟨p.1, us, ds⟩ := by
  intro p hp
  obtain ⟨⟨mc, hmc, hpc⟩, -⟩ := hg'.2.2 p hp
  refine ⟨D, hD, mc, hmc, hpc.symm, fun cv' caps' hf' => ?_⟩
  obtain ⟨cvc, capsc, hfc, hlc⟩ := hlps mc hmc
  change env.find? p.1 = _ at hf'
  rw [hpc, hfc] at hf'
  obtain ⟨rfl, rfl⟩ : cvc = cv' ∧ capsc = caps' := by simpa using hf'
  simp only
  rw [hlc]
  refine ⟨hnd, hlenP _, fun Δ0 R00 hR00 hΔ0 hC0 dsa0 hdsa0 hfit00 ρ ρ' hr => ?_⟩
  have hblk := hcov.block D hD
  have hkN := lfp_namesLen mp hD
  have hle0 : ctx.hiAt 0 ≤ ctx.hiAt prog.length := by simp only [ConLeche.NestCtx.hiAt]; omega
  have hds0 : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt 0) x := fun x hx =>
    ConLeche.WScoped.of_fvarsBelow (hdsw x hx).1 (ConLeche.Expr.fvarB_le (hfree x hx))
  have hlenR : (List.replicate prog.length (empty : V)).length = prog.length := by simp
  have hhiEq : ctx.hiAt prog.length = ctx.hiAt 0 + prog.length := by
    simp only [ConLeche.NestCtx.hiAt]; omega
  -- the enclosing frames, empty
  have hR₀ := HoleRel.extendEmpty hR00 prog hsc
  have hdsaL := DenoteMetaSpine.lift (m := mp.base2) (φ := φ) hle0 hds0 hdsa0
  rw [show ctx.hiAt prog.length - ctx.hiAt 0 = prog.length by rw [hhiEq]; omega] at hdsaL
  have hfit' : ∀ σ σ', (fun σ σ' => ∃ ρ ρ', R00 ρ ρ' ∧
        σ = consList (List.replicate prog.length empty) ρ ∧
        σ' = consList (List.replicate prog.length empty) ρ') σ σ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse
          (keyFrame (dsa0.map (AnnotTerm.liftN prog.length · 0)) (ctx.hiAt prog.length) σ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse
          (keyFrame (dsa0.map (AnnotTerm.liftN prog.length · 0)) (ctx.hiAt prog.length) σ') := by
    rintro _ _ ⟨ρ₁, ρ₁', hr₁, rfl, rfl⟩
    have e := keyFrame_lift dsa0 (ctx.hiAt 0) (List.replicate prog.length (empty : V))
    rw [hlenR, ← hhiEq] at e
    rw [e, e]
    exact hfit00 ρ₁ ρ₁' hr₁
  have hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt prog.length)
      (List.replicate prog.length (.sort 0) ++ Δ0) x := by
    intro x hx
    have := CtxOkP.extend (h := ctx.hiAt 0) (g := prog.length)
      (Ts := List.replicate prog.length (.sort 0)) (by simp) hΔ0
      (fun l hl => Or.inl ((hC0 x hx).2 l hl))
    rwa [← hhiEq] at this
  have hsem := frame_sem mp hin hD hblk.nodup hkN hcov.find hlps hul
    (fun x hx => hdsw x hx) hdsaL (hlenP _) hblk.ctors hblk.all (cacheInv_ctorsOfOk mp ctx) hrec
    rfl hR₀ (by rw [List.length_append, List.length_replicate, hΔ0, hhiEq]; omega) hCds hLds hfit' (n := n)
      (hnL.imp (fun ⟨L, hL, hLne⟩ => ⟨_, L, hL, hLne⟩) id)
    (ConLeche.nestRestartFuel ctx n) [(n, cty)] st₀ grp' st₁
    ⟨by simp, by simp, fun q hq => by
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨⟨mm, hmm, hn.symm⟩, hnI⟩⟩ (by simp) hrun hI₀
  obtain ⟨-, -, -, hle, htr⟩ := hsem.2 hc₁
  have hmcG : InGrp D grp' mc := ⟨hmc, by
    rw [List.contains_iff_mem, List.mem_map]; exact ⟨p, hp, hpc⟩⟩
  have hle' := hle _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ mc hmcG
  have htr' := htr _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
  have e := keyFrame_lift dsa0 (ctx.hiAt 0) (List.replicate prog.length (empty : V))
  rw [hlenR, ← hhiEq] at e
  rw [e, e] at hle' htr'
  exact ⟨hle', grp', hmcG, htr'⟩

/-- **A new (or re-walked) instantiation** (`nestContNew`): the frame
lemma at the enclosing relation seen at the key's depth makes the
container instance positive; the reached group-mates and the
instantiation itself are cached with their positivity. -/
theorem contNew_sem {dep : Nat} (hhid : ctx.hiAt prog.length ≤ dep) {is : List Expr}
    {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep (Expr.mkAppN (.const n us) (ds ++ is)) = some wa)
    {Δa : List AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa (Expr.mkAppN (.const n us) (ds ++ is)))
    (hgr : Graded V Δa wa) (hR : HoleRel mp.base2 φ ctx prog dep Δa R)
    (hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    {nI : Nat} {cty : Expr}
    (hnI : ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩
      = .ok (nI, cty))
    (hisl : is.length = nI) {kb : Nat} {old : Option Nat} {st₀ : NestState}
    {k : NestFieldKind} {st' : NestState}
    (hrun : ConLeche.nestContNew ctx (fueledOps .verified F) env rec prog kb n us ds ds.length old
      st₀ = .ok (k, st'))
    (hI₀ : CacheInv mp φ ctx st₀) :
    CacheInv mp φ ctx st' ∧ (st'.restart = none → MonoOn R wa) := by
  have hblk := hcov.block D hD
  have hkN := lfp_namesLen mp hD
  obtain ⟨cv, caps, hf, hcvl⟩ := hlps mm hmm
  subst hn
  -- the key's parameters read at the key's depth
  obtain ⟨fa, vs, -, hsp, -⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨vs₁, vs₂, -, hsp₁, -⟩ := DenoteMetaSpine.split _ hsp
  obtain ⟨dsa, hdsa, -⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hhid
    (fun x hx => (hdsw x hx).1) hsp₁
  -- the relation at the key's depth
  have hR₀ := hR.drop (Nat.le_refl _) hhid
  have hΔ : (Δa.drop (dep - ctx.hiAt prog.length)).length = ctx.hiAt prog.length := by
    rw [List.length_drop, hC.1]; omega
  have hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt prog.length)
      (Δa.drop (dep - ctx.hiAt prog.length)) x := fun x hx =>
    hC.drop hhid fun l hl => ⟨leaves_mkAppN_arg (List.mem_append_left _ hx) hl,
      ConLeche.Expr.fvarLeaves_lt_of_wscoped (hdsw x hx).1 l hl⟩
  have hfit : ∀ σ σ', R.drop (dep - ctx.hiAt prog.length) σ σ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa (ctx.hiAt prog.length) σ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse (keyFrame dsa (ctx.hiAt prog.length) σ') := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    have k1 := keyParamsFit mp hD hmm hf hhid hwa (by rw [hcvl, hlenP]) (fun x hx => (hdsw x hx).1)
      hdsa ρ (hgr ρ h1)
    have k2 := keyParamsFit mp hD hmm hf hhid hwa (by rw [hcvl, hlenP]) (fun x hx => (hdsw x hx).1)
      hdsa ρ' (hgr ρ' h2)
    rw [hcvl] at k1 k2
    exact ⟨k1, k2⟩
  -- invert the run
  have hrun' := hrun
  simp only [ConLeche.nestContNew, bind, Except.bind] at hrun'
  rw [hnI] at hrun'
  dsimp only at hrun'
  split at hrun'
  · simp at hrun'
  rename_i gs hfr
  obtain ⟨grp', st₁⟩ := gs
  have hsem := frame_sem mp hin hD hblk.nodup hkN hcov.find hlps hul hdsw hdsa (hlenP _) hblk.ctors
    hblk.all (cacheInv_ctorsOfOk mp ctx) hrec rfl hR₀ hΔ hCds hLds hfit (n := D.member mm)
    (hnL.imp (fun ⟨L, hL, hLne⟩ => ⟨_, L, hL, hLne⟩) id)
    (ConLeche.nestRestartFuel ctx (D.member mm)) [(D.member mm, cty)] st₀ grp' st₁
    ⟨by simp, by simp, fun q hq => by
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨⟨mm, hmm, rfl⟩, _, hnI⟩⟩ (by simp) hfr hI₀
  by_cases hrs : st₁.restart.isSome = true
  · rw [if_pos hrs] at hrun'
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun'
    obtain ⟨-, rfl⟩ := hrun'
    exact ⟨hsem.1, fun hc => by rw [hc] at hrs; exact nomatch hrs⟩
  rw [if_neg hrs] at hrun'
  have hc₁ : st₁.restart = none := by simpa using hrs
  obtain ⟨hnd, hg', hhead', hle⟩ := hsem.2 hc₁
  have hheadmem : (D.member mm, (grp'.headD default).2) ∈ grp' := by
    obtain ⟨p₀, ps₀, hp₀⟩ := List.exists_cons_of_ne_nil hg'.1
    rw [hp₀] at hhead' ⊢
    simp only [List.headD_cons] at hhead' ⊢
    rw [← hhead']
    exact List.mem_cons_self
  -- the instance is positive
  have hmono : MonoOn R wa := by
    obtain ⟨-, hids, -⟩ := n2_link mp hD hmm hcov.find hnI hf (by rw [hcvl]; exact hnd)
      (by rw [hcvl]; exact hul) (by rw [hcvl, hlenP]) hdsw hdsa
    refine monoOn_of_famLe mp hD hmm hf hhid hwa (by rw [hcvl, hlenP]) (by rw [hids, hisl])
      (fun x hx => (hdsw x hx).1) hdsa hR.dom hgr hisC fun ρ ρ' hr => ?_
    have := hle.1 _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ mm ⟨hmm, by
      rw [List.contains_iff_mem, List.mem_map]; exact ⟨_, hheadmem, rfl⟩⟩
    rw [hcvl]
    exact this
  -- the cache: the reached group-mates, then the instantiation
  split at hrun'
  · simp at hrun'
  rename_i st₂ hacc
  have hI₂ : CacheInv mp φ ctx st₂ :=
    nestAcceptGroup_sem mp _ _ _ hacc hsem.1 fun p hp hfree =>
      keyPos_of_frame mp hin hcov hrec hD hmm rfl hlps hul hdsw hLds hlenP hnL hsc hfr hc₁ hI₀
        ⟨_, hnI⟩ hnd hg' hfree p (List.mem_of_mem_drop hp)
  split at hrun'
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun'
    obtain ⟨-, rfl⟩ := hrun'
    exact ⟨hI₂, fun _ => hmono⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun'
    obtain ⟨-, rfl⟩ := hrun'
    refine ⟨⟨hI₂.1, fun ki hki hfv => ?_⟩, fun _ => hmono⟩
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hki
    rcases hki with hki | rfl
    · exact hI₂.2 ki hki hfv
    · exact keyPos_of_frame mp hin hcov hrec hD hmm rfl hlps hul hdsw hLds hlenP hnL hsc hfr hc₁
        hI₀ ⟨_, hnI⟩ hnd hg' hfv _ hheadmem

end Case

/-- **A cache hit** (a cached instantiation whose parameters lie below
every frame hole): the cached positivity, at the enclosing relation seen
at the block's own depth, makes the instance positive. -/
theorem contHit {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx}
    (hfind : ∀ n, ctx.find? n = env.find? n) {prog : List NestHole} {dep : Nat}
    (hhid : ctx.hiAt prog.length ≤ dep) {n : Name} {us : List Level} {ds is : List Expr}
    {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep (Expr.mkAppN (.const n us) (ds ++ is)) = some wa)
    {Δa : List AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa (Expr.mkAppN (.const n us) (ds ++ is)))
    (hgr : Graded V Δa wa) (hR : HoleRel mp.base2 φ ctx prog dep Δa R)
    (hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true)
    (hfree : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) {nI : Nat} {cty : Expr}
    (hnI : ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩
      = .ok (nI, cty))
    (hisl : is.length = nI) (hkp : KeyPos mp φ ctx ⟨n, us, ds⟩) : MonoOn R wa := by
  obtain ⟨D, hD, mm, hmm, hn, hk⟩ := hkp
  subst hn
  obtain ⟨cv, caps, hf⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
  obtain ⟨hnd, hlenP, hpos⟩ := hk cv caps hf
  have hle0 : ctx.hiAt 0 ≤ ctx.hiAt prog.length := by simp only [ConLeche.NestCtx.hiAt]; omega
  have hle0d : ctx.hiAt 0 ≤ dep := Nat.le_trans hle0 hhid
  have hds0 : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt 0) x := fun x hx =>
    ConLeche.WScoped.of_fvarsBelow (hdsw x hx).1 (ConLeche.Expr.fvarB_le (hfree x hx))
  -- the parameters' readings at the two depths
  obtain ⟨fa, vs, hfa, hsp, -⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK hf hfa
  change us.length = cv.levelParams.length at hul
  obtain ⟨vs₁, vs₂, -, hsp₁, -⟩ := DenoteMetaSpine.split _ hsp
  obtain ⟨dsa0, hdsa0, -⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hle0d hds0 hsp₁
  obtain ⟨dsa, hdsa, -⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hhid
    (fun x hx => (hdsw x hx).1) hsp₁
  -- the index count
  obtain ⟨-, hids, -⟩ := n2_link mp hD hmm hfind hnI hf hnd hul hlenP hdsw hdsa
  -- the cached positivity at the enclosing relation seen at the block's depth
  have hR00 := hR.dropBase hhid
  have hC0 : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt 0) (Δa.drop (dep - ctx.hiAt 0)) x :=
    fun x hx => hC.drop hle0d fun l hl =>
      ⟨leaves_mkAppN_arg (List.mem_append_left _ hx) hl,
        ConLeche.Expr.fvarLeaves_lt_of_wscoped (hds0 x hx) l hl⟩
  have hfit00 : ∀ σ σ', R.drop (dep - ctx.hiAt 0) σ σ' →
      Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse
          (keyFrame dsa0 (ctx.hiAt 0) σ) ∧
      Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse
          (keyFrame dsa0 (ctx.hiAt 0) σ') := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨keyParamsFit mp hD hmm hf hle0d hwa hlenP.symm hds0 hdsa0 ρ (hgr ρ h1),
      keyParamsFit mp hD hmm hf hle0d hwa hlenP.symm hds0 hdsa0 ρ' (hgr ρ' h2)⟩
  refine monoOn_of_famLe mp hD hmm hf hle0d hwa hlenP.symm (by rw [hids, hisl]) hds0 hdsa0
    hR.dom hgr hisC fun ρ ρ' hr => ?_
  exact (hpos _ _ hR00 (by rw [List.length_drop, hC.1]; omega) hC0 dsa0 hdsa0 hfit00 _ _
    ⟨ρ, ρ', hr, rfl, rfl⟩).1

theorem nestContainer_find {ctx : NestCtx} {C : Name} {q : Nat × List (ConstantVal × Nat)}
    (h : ConLeche.nestContainer ctx C = some q) :
    ∃ cv caps, ctx.find? C = some (.indInfo cv caps) := by
  unfold ConLeche.nestContainer at h
  split at h
  · rename_i cv caps hf; exact ⟨cv, caps, hf⟩
  · exact nomatch h

/-- **THE CONTAINER CASE, PROVED** (CONTSEM step 5): the premise
`nestPos_sem` takes, at the kind predicate `True` and the cache
invariant — under coverage (L8). -/
theorem contSem {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} (hcov : ContCover mp ctx) (F : Nat)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState))
    (hrec : NestPosSem mp.base2 φ ctx (fun _ => True) (CacheInv mp φ ctx) rec) :
    ContSem mp.base2 φ ctx (fun _ => True) (CacheInv mp φ ctx) F rec := by
  intro prog dep kb w n us st k st' hfn hnm hrun _ hhid hfrw hI Δa wa R hC hwa hgr hR
  obtain ⟨nPc, L, hq, hle, hidxfree, hnq, hdsok, nI, cty, hnI, hlen, hkey⟩ :=
    ConLeche.nestCont_inv hrun
  have hIok := cacheInv_ctorsOfOk mp (φ := φ) ctx
  rw [hIok.lookup st hI n] at hq
  have hI₁ := hIok.insert st hI n
  -- the container is a member of a recorded block
  obtain ⟨cv, caps, hfc⟩ := nestContainer_find hq
  rw [hcov.find] at hfc
  obtain ⟨D, hD, mm, hmm, hn⟩ := hcov.cover n cv caps hfc hnm hnq
  have hblk := hcov.block D hD
  obtain ⟨nP', L', hL', hlenL', hfL'⟩ := hblk.ctors mm hmm
  rw [hn, hq] at hL'
  obtain ⟨rfl, rfl⟩ : nPc = nP' ∧ L = L' := by simpa using hL'
  -- the level parameters and the parameter count: off the first
  -- constructor's record, or — a container WITHOUT constructors (lane
  -- RESTRICT-FIX) — off the recorded former (`ContBlockOk.noCtors`)
  obtain ⟨lps, hlps, hlenP0, hcvl, hnL0⟩ : ∃ lps : List Name,
      (∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
        cv.levelParams = lps) ∧
      (∀ ψ, (D.params ψ).length = nPc) ∧ cv.levelParams = lps ∧
      ((∃ L', ConLeche.nestContainer ctx n = some (nPc, L') ∧ L' ≠ []) ∨ lps.Nodup) := by
    by_cases hLne : L = []
    · subst hLne
      obtain ⟨cv', caps', hf', hnd', hlen', hlps'⟩ :=
        hblk.noCtors mm hmm nPc (by rw [hn]; exact hq)
      rw [hn, hfc] at hf'
      obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
      exact ⟨cv.levelParams, hlps', hlen', rfl, Or.inr hnd'⟩
    · have h0 : 0 < L.length := by
        cases L with
        | nil => exact absurd rfl hLne
        | cons => simp
      obtain ⟨-, -, -, -, hrdC⟩ := mp.lfp_ok D hD
      obtain ⟨cv0, nPc0, nF0, hf0, -, hlpsC, -, _A, -, hread0⟩ :=
        hrdC mm hmm 0 (by rw [← hlenL']; exact h0)
      rw [hfL' 0 h0] at hf0
      obtain ⟨rfl, rfl, rfl⟩ : L[0].1 = cv0 ∧ nPc = nPc0 ∧ L[0].2 = nF0 := by
        simp only [Option.some.injEq, ConLeche.ConstantInfo.ctorInfo.injEq] at hf0
        exact ⟨hf0.1, hf0.2.1, hf0.2.2⟩
      have hcvl : cv.levelParams = L[0].1.levelParams := by
        obtain ⟨cvm, capsm, hfm, hlm⟩ := hlpsC mm hmm
        rw [hn, hfc] at hfm
        obtain ⟨rfl, rfl⟩ : cv = cvm ∧ caps = capsm := by simpa using hfm
        exact hlm
      exact ⟨L[0].1.levelParams, hlpsC, fun ψ => (hread0 ψ).1, hcvl, Or.inl ⟨L, hq, hLne⟩⟩
  -- the parameters and the indices
  have hspine := Expr.mkAppN_getApp w
  rw [hfn] at hspine
  generalize hargs : w.getAppArgs = args at hspine hle hidxfree hdsok hlen hkey hnI
  subst hspine
  rw [← List.take_append_drop nPc args] at hwa hC
  have hdl : (args.take nPc).length = nPc := by rw [List.length_take]; omega
  have hlenP : ∀ ψ, (D.params ψ).length = (args.take nPc).length := fun ψ => by
    rw [hdl]; exact hlenP0 ψ
  have hwsargs := (wScoped_mkAppN _ hfrw.1).2
  have hdsw : ∀ x ∈ args.take nPc, Expr.WScoped (ctx.hiAt prog.length) x ∧
      x.looseBVarsBounded 0 = true := by
    intro x hx
    simp only [List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hdsok
    obtain ⟨hb, hfv⟩ := hdsok x hx
    exact ⟨ConLeche.WScoped.of_fvarsBelow (hwsargs x (List.mem_of_mem_take hx))
      (ConLeche.Expr.fvarB_le hfv), ConLeche.Expr.bvarB_le (by omega)⟩
  have hLds : ∀ x ∈ args.take nPc, Expr.LeavesBounded x := fun x hx l hl =>
    hfrw.2.2 l (leaves_mkAppN_arg (List.mem_of_mem_take hx) hl)
  have hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep (args.drop nPc) isa →
      ∀ v ∈ isa, ConstOn R v := fun isa hisa =>
    constOn_spine hR.agree hhid hisa fun a ha => ⟨hwsargs a (List.mem_of_mem_drop ha), by
      simp only [List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hidxfree
      exact hidxfree a ha⟩
  have hisl : (args.drop nPc).length = nI := by rw [List.length_drop]; omega
  -- the levels
  obtain ⟨fa, vs, hfa, -, -⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK hfc hfa
  change us.length = cv.levelParams.length at hul
  rw [hcvl] at hul
  have hnL : (∃ L', ConLeche.nestContainer ctx n = some ((args.take nPc).length, L') ∧
      L' ≠ []) ∨ lps.Nodup := by
    rw [hdl]; exact hnL0
  -- the instantiation met
  unfold ConLeche.nestContKey at hkey
  split at hkey
  · -- a cycle: a restart request
    split at hkey
    · simp [throw, throwThe, MonadExceptOf.throw] at hkey
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hkey
      obtain ⟨-, rfl⟩ := hkey
      exact ⟨⟨hI₁.1, hI₁.2⟩, fun hc => by simp at hc⟩
  · split at hkey
    · rename_i q hfq
      split at hkey
      · -- a hit
        rename_i hfree
        simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hkey
        obtain ⟨-, rfl⟩ := hkey
        refine ⟨hI₁, fun _ => ?_⟩
        obtain ⟨hqs, hqk, -⟩ := Array.findIdx?_eq_some_iff_getElem.mp hfq
        have hkeq : (ConLeche.nestContainerC ctx st n).2.keys[q].key
            = ⟨n, us, args.take nPc⟩ := by simpa using hqk
        have hfree' : ∀ x ∈ args.take nPc, x.fvarB ≤ ctx.hiAt 0 := by
          simpa using hfree
        have hkp := hI₁.2 _ (Array.getElem_mem_toList hqs) (by rw [hkeq]; exact hfree')
        rw [hkeq] at hkp
        exact contHit mp hcov.find hhid hwa hC hgr hR hisC hdsw hfree' hnI hisl hkp
      · exact contNew_sem mp hin hcov hrec hD hmm hn hlps hul hdsw hLds hlenP hnL hR.dsScoped
          hhid hwa hC hgr hR hisC hnI hisl (by rw [hdl]; exact hkey) hI₁
    · exact contNew_sem mp hin hcov hrec hD hmm hn hlps hul hdsw hLds hlenP hnL hR.dsScoped
        hhid hwa hC hgr hR hisC hnI hisl (by rw [hdl]; exact hkey) hI₁

/-! ## The member constructor, without the container premise -/

/-- **A member constructor is positive — containers included** (CONTSEM
step 6): `nestMemberCtor_sem` with its container premise discharged by
`contSem`, under coverage (L8) — every field's reading positive under
the earlier ones along the hole relation, the result's indices hole-free,
and the cache invariant kept (it holds of the empty state,
`cacheInv_empty`). -/
theorem nestMemberCtor_sem_cont {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} (hcov : ContCover mp ctx) (F : Nat)
    {nF : Nat} {crest : Expr} {st : NestState} {ks : List NestFieldKind} {tyN : Expr}
    {st' : NestState}
    (h : ConLeche.nestMemberCtor (fueledOps .verified F) env ctx nF crest st = .ok (ks, tyN, st'))
    (hfr : Frame (ctx.hiAt 0) crest) (hI : CacheInv mp φ ctx st)
    {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta mp.base2.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca)
    (hR : HoleRel mp.base2 φ ctx [] (ctx.hiAt 0) Δa R) :
    PiPosThen (ResultIdxConst ctx.nP) nF R ca ∧ CacheInv mp φ ctx st' :=
  nestMemberCtor_sem hin ctx F (P := fun _ => True) (I := CacheInv mp φ ctx)
    (fun rec hrec => contSem mp hin hcov F rec hrec) h (fun _ _ => trivial) hfr hI hC hca hgr hR

end ConLeche.Model

