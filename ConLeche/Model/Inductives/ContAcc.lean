module

public import ConLeche.Model.Inductives.ContAccFrame
public import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.NestPosAccKit
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.ContN2
public import ConLeche.Model.Inductives.ContFrame
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Verify.Cached.Erase
import ConLeche.Model.Rules.IotaSoundKit

public section

/-!
# A container instance is accessible

The container pieces of the accessibility induction on the positivity
derivation (`posD_acc`, `PosDerivAcc.lean`):

* the leaf (`accConcl_of_frameAccOut`, over `keyLeaf`): a frame's
  accessibility at the key frames makes the container instance
  accessible along the enclosing relation;
* a frame's accessibility at EMPTY enclosing frames, read back at the
  frameless relation (`frameAccOut_unextend`, with
  `HoleRelA.extendEmpty`);
* a key accessible at the block's own depth (`KeyAcc`) makes a cache
  hit's instance accessible (`contHit_acc`, at the enclosing relation
  seen at that depth, `HoleRelA.dropBase`).

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

/-- **What the container rules read**: coverage and the walk
context's sort at the level (the container case's type regime, N3). -/
@[expose] def ContOk {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (w : Nat)
    (ctx : NestCtx) : Prop :=
  ContCover mp ctx ∧ ctx.sort.eval φ = w

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

/-! ## A key, at the block's own depth -/

/-- **A key is accessible** at the block's own depth (a cache hit's
content):
for some recorded block holding its container (at the recorded
parameter count, the container's level parameters distinct, its level
the walk's), along every frameless accessibility hole relation whose
pairs satisfy the container's parameter telescope at the key frames, the
container's carrier is accessible (`FrameAccOut`, at its own member). -/
@[expose] def KeyAcc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat)
    (w : Nat) (ctx : NestCtx) (key : NestKey) : Prop :=
  ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = key.cname ∧
    ∀ cv caps, env.find? key.cname = some (.indInfo cv caps) →
      key.lvls.length = cv.levelParams.length →
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
  have hle0 : ctx.hiAt 0 ≤ ctx.hiAt prog.length := by simp only [ConLeche.NestCtx.hiAt]; omega
  have hle0d : ctx.hiAt 0 ≤ dep := Nat.le_trans hle0 hhid
  have hds0 : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt 0) x := fun x hx =>
    ConLeche.WScoped.of_fvarsBelow (hdsw x hx).1 (ConLeche.Expr.fvarB_le (hfree x hx))
  -- the parameters' readings at the two depths
  obtain ⟨fa, vs, hfa, hsp, -⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK hf hfa
  change us.length = cv.levelParams.length at hul
  obtain ⟨hnd, hlenP, hacc0⟩ := hk cv caps hf hul
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

end ConLeche.Model
