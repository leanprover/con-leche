module

public import ConLeche.Model.Inductives.ContWalk
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Verify.Inductives.StructWF
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.SumRecRead
import ConLeche.SetTheory.Derive.Univ
import ConLeche.SetTheory.Derive.Graphs
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.Inductives.NestScope

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
telescope at the key frames, the container's carrier grows between them. -/
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
theorem mem_fvarLeaves_mkAppN_arg {l : Nat × Expr} :
    ∀ {xs : List Expr} {f x : Expr}, x ∈ xs → l ∈ x.fvarLeaves → l ∈ (Expr.mkAppN f xs).fvarLeaves
  | [], _, _, hx, _ => nomatch hx
  | y :: ys, f, x, hx, hl => by
    simp only [Expr.mkAppN]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact mem_fvarLeaves_mkAppN_head (by simp [Expr.fvarLeaves, hl])
    · exact mem_fvarLeaves_mkAppN_arg hx hl
where
  mem_fvarLeaves_mkAppN_head : ∀ {xs : List Expr} {f : Expr}, l ∈ f.fvarLeaves →
      l ∈ (Expr.mkAppN f xs).fvarLeaves
    | [], _, h => h
    | y :: ys, f, h => by
      simp only [Expr.mkAppN]
      exact mem_fvarLeaves_mkAppN_head (by simp [Expr.fvarLeaves, h])

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
  (hnL : ∃ L, ConLeche.nestContainer ctx n = some (ds.length, L) ∧ L ≠ [])
  (hsc : ∀ (i : Nat) (hk : NestHole), prog.reverse[i]? = some hk → ∀ x ∈ hk.key.ds,
      Expr.WScoped (ctx.hiAt prog.length) x)

include hin hcov hrec hD hmm hn hlps hul hdsw hLds hlenP hnL hsc

/-- **The instantiations a frame accepts are positive** (the cache
invariant at a push): for every member of a frame's final group, with
the key's parameters below every frame hole — the frame lemma at any
hole relation without frames, extended by empty enclosing frames. -/
theorem keyPos_of_frame {cty : Expr} {grp' : List (Name × Expr)} {st₀ st₁ : NestState}
    (hrun : ConLeche.nestFrame ctx (fueledOps .verified F) env rec prog (ctx.hiAt prog.length) us ds
      ds.length 64 [(n, cty)] st₀ = .ok (grp', st₁))
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
    rfl hR₀ (by rw [List.length_append, List.length_replicate, hΔ0, hhiEq]; omega) hCds hLds hfit' (n := n) (by
      obtain ⟨L, hL, hLne⟩ := hnL; exact ⟨_, L, hL, hLne⟩)
    64 [(n, cty)] st₀ grp' st₁
    ⟨by simp, by simp, fun q hq => by
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨⟨mm, hmm, hn.symm⟩, hnI⟩⟩ (by simp) hrun hI₀
  obtain ⟨-, -, -, hle⟩ := hsem.2 hc₁
  have hle' := hle _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ mc ⟨hmc, by
    rw [List.contains_iff_mem, List.mem_map]; exact ⟨p, hp, hpc⟩⟩
  have e := keyFrame_lift dsa0 (ctx.hiAt 0) (List.replicate prog.length (empty : V))
  rw [hlenR, ← hhiEq] at e
  rwa [e, e] at hle'

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
    hC.drop hhid fun l hl => ⟨mem_fvarLeaves_mkAppN_arg (List.mem_append_left _ hx) hl,
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
    (by obtain ⟨L, hL, hLne⟩ := hnL; exact ⟨_, L, hL, hLne⟩)
    64 [(D.member mm, cty)] st₀ grp' st₁
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
    have := hle _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ mm ⟨hmm, by
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
  · split at hrun'
    · simp [throw, throwThe, MonadExceptOf.throw] at hrun'
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun'
      obtain ⟨-, rfl⟩ := hrun'
      refine ⟨⟨hI₂.1, fun ki hki hfv => ?_⟩, fun _ => hmono⟩
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hki
      rcases hki with hki | rfl
      · exact hI₂.2 ki hki hfv
      · exact keyPos_of_frame mp hin hcov hrec hD hmm rfl hlps hul hdsw hLds hlenP hnL hsc hfr hc₁
          hI₀ ⟨_, hnI⟩ hnd hg' hfv _ hheadmem

end Case

end ConLeche.Model

