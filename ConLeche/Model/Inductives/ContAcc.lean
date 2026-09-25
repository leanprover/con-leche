module

public import ConLeche.Model.Inductives.ContAccFrame
public import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.NestPosAccKit
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.ContN2
public import ConLeche.Model.Inductives.ContFrame
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Rules.Inputs
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Cached.Erase
import ConLeche.Model.Rules.IotaSoundKit

public section

/-!
# The container case of the accessibility theorem (lane ACCMODEL, session 3)

`ContAcc` — the premise `nestPos_acc` takes for its container case —
PROVED (`contAcc`), at the kind predicate `True` and the state invariant
`CacheInvA` (every looked-up container's constructor list is the
environment's, and every cached instantiation without a frame hole is
ACCESSIBLE along every frameless accessibility hole relation, `KeyAcc`).
The twin of `ContSem.lean`:

* a cycle is a restart request (nothing to show);
* a cache hit reads the cached accessibility at the enclosing relation
  seen at the block's own depth (`HoleRelA.dropBase`);
* a new instantiation walks its frame (`frame_acc`) along the enclosing
  relation seen at the key's depth (`HoleRelA.drop`); the leaf
  (`keyLeaf`) turns the frame's accessibility into the reduct's
  (`accConcl_of_frameAccOut`); the reached group-mates are cached with
  the frame walk read at the frameless relation extended by empty frames
  (`HoleRelA.extendEmpty`, `frameAccOut_unextend`).

The TYPE REGIME of a container instance: the container lives at the
block's level (`n2_sort`, the kernel's N3), so a truth-valued fibre of a
parameterised container is empty (`LfpClause.injNePt`); a container
without parameters reads no hole.
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

/-! ## Moving a frame's accessibility -/

theorem FrameAccOut.mono {w : Nat} {ctx : NestCtx} {prog : List NestHole} {hi : Nat}
    {R₀ : FrameRel V} {D : LfpDatum V} {ψ : Name → Nat} {dsa : List AnnotTerm} {G G' : Nat → Prop}
    (h : FrameAccOut w ctx prog hi R₀ D ψ dsa G) (hG : ∀ c, G' c → G c) :
    FrameAccOut w ctx prog hi R₀ D ψ dsa G' := by
  obtain ⟨A, hA, hinv, hacc⟩ := h
  exact ⟨A, hA, hinv, fun c hc => hacc c (hG c hc)⟩

/-- **A frame's accessibility at empty enclosing frames, read back at the
frameless relation** (the push of a cached key): no item sits at an
empty frame hole, so every item moves down past the frames. -/
theorem frameAccOut_unextend {w : Nat} {ctx : NestCtx} {prog : List NestHole}
    {R00 : FrameRel V} {D : LfpDatum V} {ψ : Name → Nat} {dsa0 : List AnnotTerm} {G : Nat → Prop}
    (h : FrameAccOut w ctx prog (ctx.hiAt prog.length)
      (fun σ σ' => ∃ ρ ρ', R00 ρ ρ' ∧ σ = consList (List.replicate prog.length empty) ρ ∧
        σ' = consList (List.replicate prog.length empty) ρ') D ψ
      (dsa0.map (AnnotTerm.liftN prog.length · 0)) G) :
    FrameAccOut w ctx [] (ctx.hiAt 0) R00 D ψ dsa0 G := by
  obtain ⟨A, hA, hinv, hacc⟩ := h
  have hhi : ctx.hiAt prog.length = ctx.hiAt 0 + prog.length := by
    simp only [NestCtx.hiAt]; omega
  have hkf : ∀ ρ : Nat → V, keyFrame (dsa0.map (AnnotTerm.liftN prog.length · 0))
      (ctx.hiAt prog.length) (consList (List.replicate prog.length empty) ρ)
      = keyFrame dsa0 (ctx.hiAt 0) ρ := by
    intro ρ
    have e := keyFrame_lift dsa0 (ctx.hiAt 0) (List.replicate prog.length (empty : V)) ρ
    rw [List.length_replicate, ← hhi] at e
    exact e
  have hadd : ∀ (σ : Nat → V) (q : Nat),
      consList (List.replicate prog.length empty) σ (q + prog.length) = σ q := by
    intro σ q
    have := consList_apply_add (List.replicate prog.length (empty : V)) σ q
    rwa [List.length_replicate] at this
  refine ⟨fun ρ => A (consList (List.replicate prog.length empty) ρ), fun ρ => hA _,
    fun ρ ρ' hag => hinv _ _ fun p hp => ?_, fun c hc ρ ρ₀ hR i hi x hx => ?_⟩
  · -- a parameter position is past the empty frames
    obtain ⟨hp1, hp2⟩ := hp
    have hge : prog.length ≤ p := by simp only [NestCtx.hiAt] at hp1 hp2 hhi; omega
    obtain ⟨q, rfl⟩ : ∃ q, p = q + prog.length := ⟨p - prog.length, by omega⟩
    rw [hadd, hadd]
    exact hag q ⟨by omega, by omega⟩
  · rw [← hkf] at hi hx
    obtain ⟨B, g, hB, hg, hs⟩ := hacc c hc _ _ ⟨ρ, ρ₀, hR, rfl, rfl⟩ i hi x hx
    -- no item at an empty frame hole
    have hge : ∀ b, b ∈ˢ B → prog.length ≤ (g b).1 := by
      intro b hb
      refine Nat.le_of_not_lt fun hlt => ?_
      have hH := (hg b hb).2
      unfold Holds at hH
      rw [consList_replicate_lt _ _ _ hlt, foldlApp_empty] at hH
      exact not_mem_empty _ hH
    refine ⟨B, fun b => ((g b).1 - prog.length, (g b).2), hB, fun b hb => ⟨?_, ?_⟩,
      fun ρ' hR' hheld => ?_⟩
    · obtain ⟨hQ, -⟩ := hg b hb
      have hgb := hge b hb
      unfold Adm at hQ ⊢
      rcases hQ with ⟨t, ht, hlt, hi', hn⟩ | ⟨j, hk, hj, hlt, hi', hn⟩
      · exact Or.inl ⟨t, ht, by simp only [NestCtx.hiAt] at hlt ⊢; omega,
          by simp only [NestCtx.hiAt] at hi' ⊢; omega, hn⟩
      · exfalso
        have := (List.getElem?_eq_some_iff.mp hj).1
        simp only [List.length_reverse] at this
        simp only [NestCtx.hiAt] at hi'; omega
    · have hH := (hg b hb).2
      have hgb := hge b hb
      unfold Holds at hH ⊢
      obtain ⟨q, hq⟩ : ∃ q, (g b).1 = q + prog.length := ⟨(g b).1 - prog.length, by omega⟩
      rw [hq, hadd] at hH
      simp only [hq, Nat.add_sub_cancel]
      exact hH
    · have := hs _ ⟨ρ, ρ', hR', rfl, rfl⟩ fun b hb => by
        have hH := hheld b hb
        have hgb := hge b hb
        unfold Holds at hH ⊢
        obtain ⟨q, hq⟩ : ∃ q, (g b).1 = q + prog.length := ⟨(g b).1 - prog.length, by omega⟩
        simp only [hq, Nat.add_sub_cancel] at hH
        rw [hq, hadd]
        exact hH
      rwa [hkf] at this

/-- **A frame's accessibility, read at the reduct** (the leaf, `keyLeaf`):
a container instance `C.{us} (ds ++ is)` at depth `dep` whose key's
parameters are read at `b` (the frame's depth), with hole-free indices,
is in the type regime and accessible along the enclosing relation with
the frame's bound read `dep - b` positions down (it reads parameter
positions only). -/
theorem accConcl_of_frameAccOut {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level}
    {dep b : Nat} (hbd : b ≤ dep) {ds is : List Expr} {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hlenI : is.length = (D.ids mm (Level.substFn φ cv.levelParams us)).length)
    (hdsw : ∀ x ∈ ds, Expr.WScoped b x) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ b ds dsa)
    {w : Nat} {ctx : NestCtx} {prog : List NestHole} {Δa : List AnnotTerm} {R : FrameRel V}
    (hR : HoleRelA mp.base2 φ ctx prog dep Δa R) (hgr : Graded V Δa wa)
    (hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    (hw : w ≠ 0) (hwD : D.w (Level.substFn φ cv.levelParams us) = w) {G : Nat → Prop}
    (hacc : FrameAccOut w ctx prog b (FrameRel.drop R (dep - b)) D (Level.substFn φ cv.levelParams us)
      dsa G) (hG : G mm) :
    AccConcl w ctx prog dep (Expr.mkAppN (.const (D.member mm) us) (ds ++ is))
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) R wa := by
  obtain ⟨hL, -, -, -⟩ := mp.lfp_ok D hD
  obtain ⟨-, isa, hisa, hk⟩ := keyLeaf mp hD hmm hf hbd hwa hlenP hlenI hdsw hdsa
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hlenP hlenI hwD hacc hk
  have hmap : ∀ ρ ρ', R ρ ρ' → isa.map (interp V ρ) = isa.map (interp V ρ') := fun ρ ρ' hr =>
    List.map_congr_left fun v hv => hisC isa hisa v hv ρ ρ' hr
  obtain ⟨A, hA, hinv, hacc⟩ := hacc
  refine ⟨?_, ⟨fun ρ => A (dropV (dep - b) ρ), ?_, fun ρ _ _ => hA _, ?_⟩, outMent_self _ _⟩
  · -- the type regime
    intro htv ρ ρ' hr
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    obtain ⟨hs1, hf1, he1⟩ := hk ρ (hgr ρ h1)
    obtain ⟨hs2, hf2, he2⟩ := hk ρ' (hgr ρ' h2)
    by_cases hp0 : (D.params ψ).length = 0
    · -- no parameters: the key frame is the tail, which the relation keeps
      have hds0 : dsa = [] := List.eq_nil_of_length_eq_zero (by
        rw [← DenoteMetaSpine.length_eq hdsa, hlenP, hp0])
      subst hds0
      have hkf : keyFrame [] b (dropV (dep - b) ρ) = keyFrame [] b (dropV (dep - b) ρ') := by
        funext j
        show ρ (j + b + (dep - b)) = ρ' (j + b + (dep - b))
        exact hR.agree ρ ρ' hr _ fun hh => by simp only [holeP] at hh; omega
      rw [he1, he2, hkf, hmap ρ ρ' hr]
    · -- a parameterised container at a positive level: a truth-valued fibre is empty
      have hwψ : D.w ψ ≠ 0 := hwD ▸ hw
      have hemp : ∀ σ, Sat V (D.params ψ).reverse (keyFrame dsa b (dropV (dep - b) σ)) →
          SpineFit (keyFrame dsa b (dropV (dep - b) σ)) (D.ids mm ψ) (isa.map (interp V σ)) →
          interp V σ wa ∈ˢ (univZero : V) →
          interp V σ wa = app (D.carrier ψ (keyFrame dsa b (dropV (dep - b) σ)) mm)
            (tupW (D.u mm ψ) (isa.map (interp V σ))) → interp V σ wa = empty := by
        intro σ hs hfit hz he
        refine ext fun y => ⟨fun hy => ?_, fun hy => absurd hy (not_mem_empty y)⟩
        exfalso
        have hpt := eq_pt_of_mem_univZero hz hy
        rw [he] at hy
        obtain ⟨j, fs, -, rfl⟩ := hL.carrier_case hs (Nat.lt_of_lt_of_le hmm hL.kN)
          (tupW_mem hfit) hy
        exact hL.injNePt ψ hwψ hp0 mm j fs hpt
      rw [hemp ρ hs1 hf1 (htv ρ ρ' hr).1 he1, hemp ρ' hs2 hf2 (htv ρ ρ' hr).2 he2]
  · -- accessibility
    intro ρ ρ₀ hr x _ hx
    obtain ⟨h1, -⟩ := hR.dom ρ ρ₀ hr
    obtain ⟨-, hf1, he1⟩ := hk ρ (hgr ρ h1)
    rw [he1] at hx
    obtain ⟨B, g, hB, hg, hs⟩ := hacc mm hG (dropV (dep - b) ρ) (dropV (dep - b) ρ₀)
      ⟨ρ, ρ₀, hr, rfl, rfl⟩ _ (tupW_mem hf1) x hx
    refine ⟨B, fun q => ((g q).1 + (dep - b), (g q).2), hB, fun q hq => ⟨?_, ?_⟩,
      fun ρ' hr' hheld => ?_⟩
    · have := holeQ_shift (k := dep - b) (hg q hq).1
      rw [show b + (dep - b) = dep by omega] at this
      exact this
    · exact holds_drop.mp (hg q hq).2
    · obtain ⟨-, h2⟩ := hR.dom ρ ρ' hr'
      obtain ⟨-, -, he2⟩ := hk ρ' (hgr ρ' h2)
      rw [he2, ← hmap ρ ρ' hr']
      exact hs (dropV (dep - b) ρ') ⟨ρ, ρ', hr', rfl, rfl⟩ fun q hq => holds_drop.mpr (hheld q hq)
  · -- the bound reads parameter positions only
    intro ρ ρ' hag
    refine hinv _ _ fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := hp
    show ρ (p + (dep - b)) = ρ' (p + (dep - b))
    exact hag _ (Or.inr ⟨by omega, by omega⟩)

/-- A frameless frame's accessibility under any frames: a member hole is
admissible there too. -/
theorem FrameAccOut.progNil {w : Nat} {ctx : NestCtx} {prog : List NestHole} {hi : Nat}
    {R₀ : FrameRel V} {D : LfpDatum V} {ψ : Name → Nat} {dsa : List AnnotTerm} {G : Nat → Prop}
    (h : FrameAccOut w ctx [] hi R₀ D ψ dsa G) : FrameAccOut w ctx prog hi R₀ D ψ dsa G := by
  obtain ⟨A, hA, hinv, hacc⟩ := h
  refine ⟨A, hA, hinv, fun c hc ρ ρ₀ hR i hi x hx => ?_⟩
  obtain ⟨B, g, hB, hg, hs⟩ := hacc c hc ρ ρ₀ hR i hi x hx
  exact ⟨B, g, hB, fun b hb => ⟨holeQ_nil (hg b hb).1, (hg b hb).2⟩, hs⟩

/-! ## The cache invariant -/

/-- **A cached instantiation is accessible** at the block's own depth:
for some recorded block holding its container (at the recorded
parameter count, the container's level parameters distinct, its level
the walk's), along every frameless accessibility hole relation whose
pairs satisfy the container's parameter telescope at the key frames, the
container's carrier is accessible (`FrameAccOut`, at its own member). -/
@[expose] def KeyAcc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat)
    (w : Nat) (ctx : NestCtx) (key : NestKey) : Prop :=
  ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = key.cname ∧
    ∀ cv caps, env.find? key.cname = some (.indInfo cv caps) →
      cv.levelParams.Nodup ∧
      (D.params (Level.substFn φ cv.levelParams key.lvls)).length = key.ds.length ∧
      ∀ (Δ0 : List AnnotTerm) (R00 : FrameRel V),
        HoleRelA mp.base2 φ ctx [] (ctx.hiAt 0) Δ0 R00 →
        Δ0.length = ctx.hiAt 0 → (∀ x ∈ key.ds, CtxOkP mp.base2 φ (ctx.hiAt 0) Δ0 x) →
        ∀ dsa, DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt 0) key.ds dsa →
        (∀ ρ ρ', R00 ρ ρ' →
          Sat V (D.params (Level.substFn φ cv.levelParams key.lvls)).reverse
              (keyFrame dsa (ctx.hiAt 0) ρ) ∧
          Sat V (D.params (Level.substFn φ cv.levelParams key.lvls)).reverse
              (keyFrame dsa (ctx.hiAt 0) ρ')) →
        D.w (Level.substFn φ cv.levelParams key.lvls) = w ∧
        FrameAccOut w ctx [] (ctx.hiAt 0) R00 D (Level.substFn φ cv.levelParams key.lvls) dsa
          (fun c => c = mm)

/-- **The cache invariant** of the accessibility route (twin of
`CacheInv`). -/
@[expose] def CacheInvA {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat)
    (w : Nat) (ctx : NestCtx) (st : NestState) : Prop :=
  (∀ c r, st.ctorsOf.lookup c = some r → r = ConLeche.nestContainer ctx c) ∧
  ∀ ki ∈ st.keys.toList, (∀ x ∈ ki.key.ds, x.fvarB ≤ ctx.hiAt 0) → KeyAcc mp φ w ctx ki.key

theorem cacheInvA_empty {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (w : Nat)
    (ctx : NestCtx) : CacheInvA mp φ w ctx {} :=
  ⟨fun _ _ h => by simp at h, fun _ h => by simp at h⟩

theorem cacheInvA_ctorsOfOk {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (w : Nat)
    (ctx : NestCtx) : CtorsOfOk ctx (CacheInvA mp φ w ctx) where
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

/-- **Accepting the reached group-mates keeps the cache invariant**, given
each pushed instantiation's accessibility. -/
theorem nestAcceptGroup_acc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {w : Nat}
    {ctx : NestCtx} {hi : Nat} {us : List Level} {ds : List Expr} :
    ∀ (grp : List (Name × Expr)) (st st' : NestState),
      ConLeche.nestAcceptGroup (m := CheckM) ctx hi us ds grp st = .ok st' →
      CacheInvA mp φ w ctx st →
      (∀ p ∈ grp, (∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) → KeyAcc mp φ w ctx ⟨p.1, us, ds⟩) →
      CacheInvA mp φ w ctx st'
  | [], st, st', h, hI, _ => by
    simp only [ConLeche.nestAcceptGroup, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hI
  | (c, ty) :: rest, st, st', h, hI, hk => by
    simp only [ConLeche.nestAcceptGroup, bind, Except.bind] at h
    split at h
    · split at h
      · simp at h
      rename_i q hq
      refine nestAcceptGroup_acc mp rest _ st' h ⟨hI.1, fun ki hki hfv => ?_⟩
        (fun p hp => hk p (List.mem_cons_of_mem _ hp))
      simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hki
      rcases hki with hki | rfl
      · exact hI.2 ki hki hfv
      · exact hk (c, ty) List.mem_cons_self hfv
    · exact nestAcceptGroup_acc mp rest st st' h hI (fun p hp => hk p (List.mem_cons_of_mem _ hp))

section Case

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (hin : RulesInputs V mp.base2 φ)
  {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} (hsort : ctx.sort.eval φ = w) (hcov : ContCover mp ctx)
  {F : Nat}
  {rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)}
  (hrec : NestPosAcc mp.base2 φ w ctx (fun _ => True) (CacheInvA mp φ w ctx) rec)
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

include hin hw hsort hcov hrec hD hmm hn hlps hul hdsw hLds hlenP hnL hsc

/-- **The instantiations a frame accepts are accessible** (the cache
invariant at a push): the frame lemma at any frameless relation,
extended by empty enclosing frames. -/
theorem keyAcc_of_frame {cty : Expr} {grp' : List (Name × Expr)} {st₀ st₁ : NestState}
    (hrun : ConLeche.nestFrame ctx (fueledOps .verified F) env rec prog (ctx.hiAt prog.length) us ds
      ds.length (ConLeche.nestRestartFuel ctx n) [(n, cty)] st₀ = .ok (grp', st₁))
    (hc₁ : st₁.restart = none) (hI₀ : CacheInvA mp φ w ctx st₀)
    (hnI : ∃ nI, ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩
      = .ok (nI, cty))
    (hnd : lps.Nodup) (hg' : GrpOk ctx D (ctx.hiAt prog.length) us ds grp')
    (hfree : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) :
    ∀ p ∈ grp', KeyAcc mp φ w ctx ⟨p.1, us, ds⟩ := by
  intro p hp
  obtain ⟨⟨mc, hmc, hpc⟩, -⟩ := hg'.2.2 p hp
  refine ⟨D, hD, mc, hmc, hpc.symm, fun cv' caps' hf' => ?_⟩
  obtain ⟨cvc, capsc, hfc, hlc⟩ := hlps mc hmc
  change env.find? p.1 = _ at hf'
  rw [hpc, hfc] at hf'
  obtain ⟨rfl, rfl⟩ : cvc = cv' ∧ capsc = caps' := by simpa using hf'
  simp only
  rw [hlc]
  have hblk := hcov.block D hD
  have hkN := lfp_namesLen mp hD
  have hle0 : ctx.hiAt 0 ≤ ctx.hiAt prog.length := by simp only [ConLeche.NestCtx.hiAt]; omega
  have hds0 : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt 0) x := fun x hx =>
    ConLeche.WScoped.of_fvarsBelow (hdsw x hx).1 (ConLeche.Expr.fvarB_le (hfree x hx))
  have hhiEq : ctx.hiAt prog.length = ctx.hiAt 0 + prog.length := by
    simp only [ConLeche.NestCtx.hiAt]; omega
  -- the level: the head's instantiation (N3)
  obtain ⟨cvm, capsm, hfm, hlm⟩ := hlps mm hmm
  obtain ⟨nI, hnI'⟩ := hnI
  rw [← hn] at hnI'
  refine ⟨hnd, hlenP _, fun Δ0 R00 hR00 hΔ0 hC0 dsa0 hdsa0 hfit00 => ?_⟩
  -- the enclosing frames, empty
  have hR₀ := HoleRelA.extendEmpty hR00 prog hsc
  have hdsaL := DenoteMetaSpine.lift (m := mp.base2) (φ := φ) hle0 hds0 hdsa0
  rw [show ctx.hiAt prog.length - ctx.hiAt 0 = prog.length by rw [hhiEq]; omega] at hdsaL
  have hwD : D.w (Level.substFn φ lps us) = w := by
    have := n2_sort mp hD hmm hcov.find hnI' hfm (by rw [hlm]; exact hnd) (by rw [hlm]; exact hul)
      (by rw [hlm]; exact hlenP _) hdsw hdsaL
    rw [hlm] at this
    exact this.trans hsort
  have hfit' : ∀ σ σ', (fun σ σ' => ∃ ρ ρ', R00 ρ ρ' ∧
        σ = consList (List.replicate prog.length empty) ρ ∧
        σ' = consList (List.replicate prog.length empty) ρ') σ σ' →
      Sat V (D.params (Level.substFn φ lps us)).reverse
          (keyFrame (dsa0.map (AnnotTerm.liftN prog.length · 0)) (ctx.hiAt prog.length) σ) ∧
      Sat V (D.params (Level.substFn φ lps us)).reverse
          (keyFrame (dsa0.map (AnnotTerm.liftN prog.length · 0)) (ctx.hiAt prog.length) σ') := by
    rintro _ _ ⟨ρ₁, ρ₁', hr₁, rfl, rfl⟩
    have e := keyFrame_lift dsa0 (ctx.hiAt 0) (List.replicate prog.length (empty : V))
    rw [List.length_replicate, ← hhiEq] at e
    rw [e, e]
    exact hfit00 ρ₁ ρ₁' hr₁
  have hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt prog.length)
      (List.replicate prog.length (.sort 0) ++ Δ0) x := by
    intro x hx
    have := CtxOkP.extend (h := ctx.hiAt 0) (g := prog.length)
      (Ts := List.replicate prog.length (.sort 0)) (by simp) hΔ0
      (fun l hl => Or.inl ((hC0 x hx).2 l hl))
    rwa [← hhiEq] at this
  have hsem := frame_acc mp hin hw hD hblk.nodup hkN hcov.find hlps hul
    (fun x hx => hdsw x hx) hdsaL (hlenP _) hblk.ctors hblk.all (cacheInvA_ctorsOfOk mp w ctx) hrec
    (fun _ => hwD) rfl hR₀ (by rw [List.length_append, List.length_replicate, hΔ0, hhiEq]; omega)
    hCds hLds hfit' (n := n)
    (hnL.imp (fun ⟨L, hL, hLne⟩ => ⟨_, L, hL, hLne⟩) id)
    (ConLeche.nestRestartFuel ctx n) [(n, cty)] st₀ grp' st₁
    ⟨by simp, by simp, fun q hq => by
      simp only [List.mem_singleton] at hq
      subst hq
      exact ⟨⟨mm, hmm, hn.symm⟩, nI, by rw [hn] at hnI'; exact hnI'⟩⟩ (by simp) hrun hI₀
  obtain ⟨-, -, -, hacc⟩ := hsem.2 hc₁
  have hmcG : InGrp D grp' mc := ⟨hmc, by
    rw [List.contains_iff_mem, List.mem_map]; exact ⟨p, hp, hpc⟩⟩
  exact ⟨hwD, frameAccOut_unextend (hacc.mono fun c hc => hc ▸ hmcG)⟩

/-- **A new (or re-walked) instantiation** (`nestContNew`): the frame
lemma at the enclosing relation seen at the key's depth makes the
container instance accessible; the reached group-mates and the
instantiation itself are cached with their accessibility. -/
theorem contNew_acc {dep : Nat} (hhid : ctx.hiAt prog.length ≤ dep) {is : List Expr}
    {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep (Expr.mkAppN (.const n us) (ds ++ is)) = some wa)
    {Δa : List AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa (Expr.mkAppN (.const n us) (ds ++ is)))
    (hgr : Graded V Δa wa) (hR : HoleRelA mp.base2 φ ctx prog dep Δa R)
    (hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    {nI : Nat} {cty : Expr}
    (hnI : ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩
      = .ok (nI, cty))
    (hisl : is.length = nI) {kb : Nat} {old : Option Nat} {st₀ : NestState}
    {k : NestFieldKind} {st' : NestState}
    (hrun : ConLeche.nestContNew ctx (fueledOps .verified F) env rec prog kb n us ds ds.length old
      st₀ = .ok (k, st'))
    (hI₀ : CacheInvA mp φ w ctx st₀) :
    CacheInvA mp φ w ctx st' ∧ (st'.restart = none →
      AccConcl w ctx prog dep (Expr.mkAppN (.const n us) (ds ++ is))
        (Expr.mkAppN (.const n us) (ds ++ is)) R wa) := by
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
  have hfit : ∀ σ σ', FrameRel.drop R (dep - ctx.hiAt prog.length) σ σ' →
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
  have hwD : lps.Nodup → D.w (Level.substFn φ lps us) = w := fun hnd => by
    have := n2_sort mp hD hmm hcov.find hnI hf (by rw [hcvl]; exact hnd) (by rw [hcvl]; exact hul)
      (by rw [hcvl]; exact hlenP _) hdsw hdsa
    rw [hcvl] at this
    exact this.trans hsort
  -- invert the run
  have hrun' := hrun
  simp only [ConLeche.nestContNew, bind, Except.bind] at hrun'
  rw [hnI] at hrun'
  dsimp only at hrun'
  split at hrun'
  · simp at hrun'
  rename_i gs hfr
  obtain ⟨grp', st₁⟩ := gs
  have hsem := frame_acc mp hin hw hD hblk.nodup hkN hcov.find hlps hul hdsw hdsa (hlenP _)
    hblk.ctors hblk.all (cacheInvA_ctorsOfOk mp w ctx) hrec hwD rfl hR₀ hΔ hCds hLds hfit
    (n := D.member mm) (hnL.imp (fun ⟨L, hL, hLne⟩ => ⟨_, L, hL, hLne⟩) id)
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
  obtain ⟨hnd, hg', hhead', hacc⟩ := hsem.2 hc₁
  have hheadmem : (D.member mm, (grp'.headD default).2) ∈ grp' := by
    obtain ⟨p₀, ps₀, hp₀⟩ := List.exists_cons_of_ne_nil hg'.1
    rw [hp₀] at hhead' ⊢
    simp only [List.headD_cons] at hhead' ⊢
    rw [← hhead']
    exact List.mem_cons_self
  -- the instance is accessible
  have hconcl : AccConcl w ctx prog dep (Expr.mkAppN (.const (D.member mm) us) (ds ++ is))
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) R wa := by
    obtain ⟨-, hids, -⟩ := n2_link mp hD hmm hcov.find hnI hf (by rw [hcvl]; exact hnd)
      (by rw [hcvl]; exact hul) (by rw [hcvl, hlenP]) hdsw hdsa
    rw [← hcvl] at hacc hwD
    exact accConcl_of_frameAccOut mp hD hmm hf hhid hwa (by rw [hlenP]) (by rw [hids, hisl])
      (fun x hx => (hdsw x hx).1) hdsa hR hgr hisC hw (hwD (by rw [hcvl]; exact hnd)) hacc
      ⟨hmm, by rw [List.contains_iff_mem, List.mem_map]; exact ⟨_, hheadmem, rfl⟩⟩
  -- the cache: the reached group-mates, then the instantiation
  split at hrun'
  · simp at hrun'
  rename_i st₂ hacc'
  have hI₂ : CacheInvA mp φ w ctx st₂ :=
    nestAcceptGroup_acc mp _ _ _ hacc' hsem.1 fun p hp hfree =>
      keyAcc_of_frame mp hin hw hsort hcov hrec hD hmm rfl hlps hul hdsw hLds hlenP hnL hsc hfr hc₁
        hI₀ ⟨_, hnI⟩ hnd hg' hfree p (List.mem_of_mem_drop hp)
  split at hrun'
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun'
    obtain ⟨-, rfl⟩ := hrun'
    exact ⟨hI₂, fun _ => hconcl⟩
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun'
    obtain ⟨-, rfl⟩ := hrun'
    refine ⟨⟨hI₂.1, fun ki hki hfv => ?_⟩, fun _ => hconcl⟩
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hki
    rcases hki with hki | rfl
    · exact hI₂.2 ki hki hfv
    · exact keyAcc_of_frame mp hin hw hsort hcov hrec hD hmm rfl hlps hul hdsw hLds hlenP hnL hsc
        hfr hc₁ hI₀ ⟨_, hnI⟩ hnd hg' hfv _ hheadmem

end Case

/-- **A cache hit** (a cached instantiation whose parameters lie below
every frame hole): the cached accessibility, at the enclosing relation
seen at the block's own depth, makes the instance accessible. -/
theorem contHit_acc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {w : Nat} (hw : w ≠ 0)
    {ctx : NestCtx} (hfind : ∀ n, ctx.find? n = env.find? n) {prog : List NestHole} {dep : Nat}
    (hhid : ctx.hiAt prog.length ≤ dep) {n : Name} {us : List Level} {ds is : List Expr}
    {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ dep (Expr.mkAppN (.const n us) (ds ++ is)) = some wa)
    {Δa : List AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa (Expr.mkAppN (.const n us) (ds ++ is)))
    (hgr : Graded V Δa wa) (hR : HoleRelA mp.base2 φ ctx prog dep Δa R)
    (hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true)
    (hfree : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) {nI : Nat} {cty : Expr}
    (hnI : ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨n, us, ds⟩
      = .ok (nI, cty))
    (hisl : is.length = nI) (hkp : KeyAcc mp φ w ctx ⟨n, us, ds⟩) :
    AccConcl w ctx prog dep (Expr.mkAppN (.const n us) (ds ++ is))
      (Expr.mkAppN (.const n us) (ds ++ is)) R wa := by
  obtain ⟨D, hD, mm, hmm, hn, hk⟩ := hkp
  subst hn
  obtain ⟨cv, caps, hf⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
  obtain ⟨hnd, hlenP, hacc0⟩ := hk cv caps hf
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
  -- the cached accessibility at the enclosing relation seen at the block's depth
  have hR00 := hR.dropBase hhid
  have hC0 : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt 0) (Δa.drop (dep - ctx.hiAt 0)) x :=
    fun x hx => hC.drop hle0d fun l hl =>
      ⟨leaves_mkAppN_arg (List.mem_append_left _ hx) hl,
        ConLeche.Expr.fvarLeaves_lt_of_wscoped (hds0 x hx) l hl⟩
  have hfit00 : ∀ σ σ', FrameRel.drop R (dep - ctx.hiAt 0) σ σ' →
      Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse
          (keyFrame dsa0 (ctx.hiAt 0) σ) ∧
      Sat V (D.params (Level.substFn φ cv.levelParams us)).reverse
          (keyFrame dsa0 (ctx.hiAt 0) σ') := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    exact ⟨keyParamsFit mp hD hmm hf hle0d hwa hlenP.symm hds0 hdsa0 ρ (hgr ρ h1),
      keyParamsFit mp hD hmm hf hle0d hwa hlenP.symm hds0 hdsa0 ρ' (hgr ρ' h2)⟩
  obtain ⟨hwD, hacc⟩ := hacc0 _ _ hR00 (by rw [List.length_drop, hC.1]; omega) hC0 dsa0 hdsa0
    hfit00
  exact accConcl_of_frameAccOut mp hD hmm hf hle0d hwa hlenP.symm (by rw [hids, hisl]) hds0 hdsa0
    hR hgr hisC hw hwD hacc.progNil rfl

/-- **THE CONTAINER CASE OF THE ACCESSIBILITY THEOREM, PROVED** (twin of
`contSem`): the premise `nestPos_acc` takes, at the kind predicate `True`
and the cache invariant `CacheInvA` — under coverage (L8), at a positive
level `w` that is the walk context's sort (the container case's type
regime, N3). -/
theorem contAcc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} (hw : w ≠ 0) {ctx : NestCtx}
    (hsort : ctx.sort.eval φ = w) (hcov : ContCover mp ctx) (F : Nat)
    (rec : List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState))
    (hrec : NestPosAcc mp.base2 φ w ctx (fun _ => True) (CacheInvA mp φ w ctx) rec) :
    ContAcc mp.base2 φ w ctx (fun _ => True) (CacheInvA mp φ w ctx) F rec := by
  intro prog dep kb wt n us st k st' hfn hnm hrun _ hhid hfrw hI Δa wa R hC hwa hgr hR
  obtain ⟨nPc, L, hq, hle, hidxfree, hnq, hdsok, nI, cty, hnI, hlen, hkey⟩ :=
    ConLeche.nestCont_inv hrun
  have hIok := cacheInvA_ctorsOfOk mp (φ := φ) w ctx
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
      obtain ⟨cv0, nPc0, nF0, hf0, -, hlpsC, -, -, _A, -, hread0⟩ :=
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
  have hspine := Expr.mkAppN_getApp wt
  rw [hfn] at hspine
  generalize hargs : wt.getAppArgs = args at hspine hle hidxfree hdsok hlen hkey hnI
  subst hspine
  suffices hres : CacheInvA mp φ w ctx st' ∧ (st'.restart = none →
      AccConcl w ctx prog dep (Expr.mkAppN (.const n us) (args.take nPc ++ args.drop nPc))
        (Expr.mkAppN (.const n us) (args.take nPc ++ args.drop nPc)) R wa) by
    rwa [List.take_append_drop] at hres
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
        exact contHit_acc mp hw hcov.find hhid hwa hC hgr hR hisC hdsw hfree' hnI hisl hkp
      · exact contNew_acc mp hin hw hsort hcov hrec hD hmm hn hlps hul hdsw hLds hlenP hnL
          hR.dsScoped hhid hwa hC hgr hR hisC hnI hisl (by rw [hdl]; exact hkey) hI₁
    · exact contNew_acc mp hin hw hsort hcov hrec hD hmm hn hlps hul hdsw hLds hlenP hnL
        hR.dsScoped hhid hwa hC hgr hR hisC hnI hisl (by rw [hdl]; exact hkey) hI₁

end ConLeche.Model
