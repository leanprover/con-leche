module

public import ConLeche.Model.Inductives.ContAccFrame
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.NestPosAccKit
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
block's level at every pair fitting it (`grp_sort`, the kernel's N3), so a truth-valued fibre of a
container is empty (`LfpClause.injNePt`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules

open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-! ## Moving a frame's accessibility -/

private noncomputable def downOccN_ca : Nat → V → V
  | 0, o => o
  | n + 1, o => downOcc (downOccN_ca n o)

private theorem defFun_downOccN_ca {k : Nat} :
    ∀ (n : Nat) {O : (Fin k → V) → V}, DefFun k O → DefFun k fun env => downOccN_ca n (O env)
  | 0, _, hO => hO
  | n + 1, _, hO => DefFun.downOcc_apply (defFun_downOccN_ca n hO)

private theorem downOccN_ca_occEncItem :
    ∀ {n i : Nat}, n ≤ i → ∀ (vs : List V) (y : V),
      downOccN_ca n (occEncItem i vs y) = occEncItem (i - n) vs y
  | 0, _, _, _, _ => rfl
  | n + 1, i, hni, vs, y => by
    obtain ⟨q, hq⟩ : ∃ q, i - n = q + 1 := ⟨i - (n + 1), by omega⟩
    unfold downOccN_ca
    rw [downOccN_ca_occEncItem (by omega) vs y, hq, downOcc_occEncItem]
    congr 1; omega

private noncomputable def upOcc_ca (o : V) : V :=
  kpair (vsucc (sfst o)) (ssnd o)

private theorem defFun_upOcc_ca {k : Nat} {O : (Fin k → V) → V} (hO : DefFun k O) :
    DefFun k fun env => upOcc_ca (O env) :=
  DefFun.kpair_apply (DefFun.vsucc_apply (DefFun.sfst_apply hO)) (DefFun.ssnd_apply hO)

private theorem upOcc_ca_occEncItem (i : Nat) (vs : List V) (y : V) :
    upOcc_ca (occEncItem i vs y) = occEncItem (i + 1) vs y := by
  unfold upOcc_ca occEncItem
  rw [sfst_kpair, ssnd_kpair]
  rfl

private noncomputable def upOccN_ca : Nat → V → V
  | 0, o => o
  | n + 1, o => upOcc_ca (upOccN_ca n o)

private theorem defFun_upOccN_ca {k : Nat} :
    ∀ (n : Nat) {O : (Fin k → V) → V}, DefFun k O → DefFun k fun env => upOccN_ca n (O env)
  | 0, _, hO => hO
  | n + 1, _, hO => defFun_upOcc_ca (defFun_upOccN_ca n hO)

private theorem upOccN_ca_occEncItem :
    ∀ (n i : Nat) (vs : List V) (y : V),
      upOccN_ca n (occEncItem i vs y) = occEncItem (i + n) vs y
  | 0, _, _, _ => rfl
  | n + 1, i, vs, y => by
    unfold upOccN_ca
    rw [upOccN_ca_occEncItem n i vs y, upOcc_ca_occEncItem, Nat.add_assoc]

theorem FrameAccOut.mono {w : Nat} {ctx : NestCtx} {prog : List NestHole} {hi : Nat}
    {R₀ : FrameRel V} {D : LfpDatum V} {ψ : Name → Nat} {dsa : List Term} {G G' : Nat → Prop}
    (h : FrameAccOut w ctx prog hi R₀ D ψ dsa G) (hG : ∀ c, G' c → G c) :
    FrameAccOut w ctx prog hi R₀ D ψ dsa G' := by
  obtain ⟨A, hA, hinv, hdef, hacc⟩ := h
  exact ⟨A, hA, hinv, hdef, fun c hc => hacc c (hG c hc)⟩

/-- **A frame's accessibility at empty enclosing frames, read back at the
frameless relation** (the push of a cached key): no item sits at an
empty frame hole, so every item moves down past the frames. -/
theorem frameAccOut_unextend {w : Nat} {ctx : NestCtx} {prog : List NestHole}
    {R00 : FrameRel V} {D : LfpDatum V} {ψ : Name → Nat} {dsa0 : List Term} {G : Nat → Prop}
    (h : FrameAccOut w ctx prog (ctx.hiAt prog.length)
      (fitRel (fun σ σ' => ∃ ρ ρ', R00 ρ ρ' ∧ σ = consList (List.replicate prog.length empty) ρ ∧
        σ' = consList (List.replicate prog.length empty) ρ') D ψ
        (dsa0.map (Term.liftN prog.length · 0)) (ctx.hiAt prog.length)) D ψ
      (dsa0.map (Term.liftN prog.length · 0)) G) :
    FrameAccOut w ctx [] (ctx.hiAt 0) (fitRel R00 D ψ dsa0 (ctx.hiAt 0)) D ψ dsa0 G := by
  obtain ⟨A, hA, hinv, hdef, hacc⟩ := h
  have hhi : ctx.hiAt prog.length = ctx.hiAt 0 + prog.length := by
    simp only [NestCtx.hiAt]; omega
  have hkf : ∀ ρ : Nat → V, keyFrame (dsa0.map (Term.liftN prog.length · 0))
      (ctx.hiAt prog.length) (consList (List.replicate prog.length empty) ρ)
      = keyFrame dsa0 (ctx.hiAt 0) ρ := by
    intro ρ
    have e := keyFrame_lift dsa0 (ctx.hiAt 0) (List.replicate prog.length (empty : V)) ρ
    rw [List.length_replicate, ← hhi] at e
    exact e
  have hkF : ∀ ρ : Nat → V, KeyFit D ψ dsa0 (ctx.hiAt 0) ρ →
      KeyFit D ψ (dsa0.map (Term.liftN prog.length · 0)) (ctx.hiAt prog.length)
        (consList (List.replicate prog.length empty) ρ) := fun ρ h => by
    unfold KeyFit; rw [hkf]; exact h
  have hadd : ∀ (σ : Nat → V) (q : Nat),
      consList (List.replicate prog.length empty) σ (q + prog.length) = σ q := by
    intro σ q
    have := consList_apply_add (List.replicate prog.length (empty : V)) σ q
    rwa [List.length_replicate] at this
  have hdef' : DefBound (ctx.hiAt 0) fun ρ => A (consList (List.replicate prog.length empty) ρ) := by
    intro tail
    let Gs : Fin (ctx.hiAt prog.length) → (Fin (ctx.hiAt 0) → V) → V := fun j xs =>
      if hj : j.val < prog.length then empty else xs ⟨j.val - prog.length, by omega⟩
    have hGs : ∀ j, DefFun (ctx.hiAt 0) (Gs j) := fun j => by
      dsimp only [Gs]
      split
      · exact DefFun.empty
      · exact DefFun.proj _
    refine ((hdef tail).comp hGs).congr fun xs => ?_
    congr 1
    funext j
    by_cases hj : j < prog.length
    · have hj' : j < ctx.hiAt prog.length := by omega
      simp only [Semantics.prepend, hj', ↓reduceDIte, Gs, hj]
      exact (consList_replicate_lt prog.length empty _ hj).symm
    · by_cases hj' : j < ctx.hiAt prog.length
      · obtain ⟨q, rfl⟩ : ∃ q, j = q + prog.length := ⟨j - prog.length, by omega⟩
        have hq : q < ctx.hiAt 0 := by omega
        simp only [Semantics.prepend, hj', hq, ↓reduceDIte, Gs, hj, hadd]
        simp
      · obtain ⟨q, rfl⟩ : ∃ q, j = q + prog.length := ⟨j - prog.length, by omega⟩
        have hnq : ¬ q < ctx.hiAt 0 := by omega
        simp only [Semantics.prepend, hj', hnq, ↓reduceDIte, hadd]
        congr 1; omega
  refine ⟨fun ρ => A (consList (List.replicate prog.length empty) ρ), fun ρ => hA _,
    fun ρ ρ' hag => hinv _ _ fun p hp => ?_, hdef', fun c hc ρ ρ₀ hR i hi x hx => ?_⟩
  · -- a parameter position is past the empty frames
    obtain ⟨hp1, hp2⟩ := hp
    have hge : prog.length ≤ p := by simp only [NestCtx.hiAt] at hp1 hp2 hhi; omega
    obtain ⟨q, rfl⟩ : ∃ q, p = q + prog.length := ⟨p - prog.length, by omega⟩
    rw [hadd, hadd]
    exact hag q ⟨by omega, by omega⟩
  · rw [← hkf] at hi hx
    obtain ⟨B, g, hB, ⟨U, hgU⟩, hitems, hs⟩ := hacc c hc _ _
      ⟨⟨ρ, ρ₀, hR.1, rfl, rfl⟩, hkF ρ hR.2.1, hkF ρ₀ hR.2.2⟩ i hi x hx
    -- no item at an empty frame hole
    have hitem_ok : ∀ b, b ∈ˢ B → ∃ qi vs y, app g b = occEncItem qi vs y ∧
        prog.length ≤ qi ∧ HoleQ ctx prog (ctx.hiAt prog.length) qi vs.length ∧
        NoPtPrefix (consList (List.replicate prog.length empty) ρ qi) vs ∧
        y ∈ˢ vs.foldl app (consList (List.replicate prog.length empty) ρ qi) := by
      intro b hb
      obtain ⟨hQ, hH⟩ := hitems b hb
      obtain ⟨qi, vs, y, heq, hQ'⟩ := hQ
      obtain ⟨qi', vs', y', heq', hnp, hy⟩ := hH
      rw [heq] at heq'
      obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj heq'
      have hge : prog.length ≤ qi := Nat.le_of_not_lt fun hlt => by
        rw [consList_replicate_lt _ _ _ hlt, foldlApp_empty] at hy
        exact not_mem_empty _ hy
      exact ⟨qi, vs, y, heq, hge, hQ', hnp, hy⟩
    let g' : V := graph (fun b => downOccN_ca prog.length (app g b)) B
      (hasGraph_of_defFun1 (defFun_downOccN_ca prog.length
        (DefFun.app_apply (DefFun.const g) (DefFun.proj 0))))
    refine ⟨B, g', hB,
      ⟨image (downOccN_ca prog.length) U
          (hasImage_of_defFun1 (defFun_downOccN_ca prog.length (DefFun.proj 0)) U),
        graph_mem_piSet fun b hb => mem_image.mpr ⟨app g b, app_mem_of_mem_piSet hgU hb, rfl⟩⟩,
      fun b hb => ?_, fun ρ' hR' hheld => ?_⟩
    · obtain ⟨qi, vs, y, heq, hge, hQ, hnp, hy⟩ := hitem_ok b hb
      have hg_app : app g' b = occEncItem (qi - prog.length) vs y := by
        rw [app_graph hb, heq, downOccN_ca_occEncItem hge]
      refine ⟨⟨qi - prog.length, vs, y, hg_app, ?_⟩, ?_⟩
      · unfold HoleQ at hQ ⊢
        rcases hQ with ⟨t, ht, hlt, hi', hn⟩ | ⟨j, hk, hj, hlt, hi', hn⟩
        · exact Or.inl ⟨t, ht, by simp only [NestCtx.hiAt] at hlt ⊢; omega,
            by simp only [NestCtx.hiAt] at hi' ⊢; omega, hn⟩
        · exfalso
          have := (List.getElem?_eq_some_iff.mp hj).1
          simp only [List.length_reverse] at this
          simp only [NestCtx.hiAt] at hi'; omega
      · obtain ⟨q, hq⟩ : ∃ q, qi = q + prog.length := ⟨qi - prog.length, by omega⟩
        rw [hq, hadd] at hnp hy
        refine ⟨qi - prog.length, vs, y, hg_app, ?_, ?_⟩
        · simpa [hq] using hnp
        · simpa [hq] using hy
    · have := hs _ ⟨⟨ρ, ρ', hR'.1, rfl, rfl⟩, hkF ρ hR'.2.1, hkF ρ' hR'.2.2⟩ fun b hb => by
        obtain ⟨qi, vs, y, heq, hge, -, -, -⟩ := hitem_ok b hb
        obtain ⟨qi', vs', y', heq', hy'⟩ := hheld b hb
        rw [app_graph hb, heq, downOccN_ca_occEncItem hge] at heq'
        obtain ⟨rqi, rvs, ry⟩ := occEncItem_inj heq'
        obtain ⟨q, hq⟩ : ∃ q, qi = q + prog.length := ⟨qi - prog.length, by omega⟩
        refine ⟨qi, vs, y, heq, ?_⟩
        rw [hq, hadd]
        subst rvs ry
        rw [← rqi, show qi - prog.length = q by omega] at hy'
        exact hy'
      rwa [hkf] at this

/-- **A frame's accessibility, read at the reduct** (the leaf, `keyLeaf`):
a container instance `C.{us} (ds ++ is)` at depth `dep` whose key's
parameters are read at `b` (the frame's depth), with hole-free indices,
carries the point vacuously and is accessible along the enclosing relation with
the frame's bound read `dep - b` positions down (it reads parameter
positions only). -/
theorem accConcl_of_frameAccOut (mp : EnvModelM V env)
    {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal}
    {caps : IndCaps} (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level}
    {dep b : Nat} (hbd : b ≤ dep) {ds is : List Expr} {wa : Term}
    (hwa : denote mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    (hlenP : ds.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hlenI : is.length = (D.ids mm (Level.substFn φ cv.levelParams us)).length)
    (hdsw : ∀ x ∈ ds, Expr.WScoped b x) {dsa : List Term}
    (hdsa : DenoteSpine mp.base2.acval env φ b ds dsa)
    {w : Nat} {ctx : NestCtx} {prog : List NestHole} {Δa : List Term} {R : FrameRel V}
    (hR : HoleRelA mp.base2 φ w ctx prog dep Δa R) (hgr : GradedTy V Δa wa)
    (hisC : ∀ isa, DenoteSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    (hwD : ∀ σ σ', fitRel (FrameRel.drop R (dep - b)) D (Level.substFn φ cv.levelParams us) dsa b
      σ σ' → D.w (Level.substFn φ cv.levelParams us) = w) {G : Nat → Prop}
    (hacc : FrameAccOut w ctx prog b
      (fitRel (FrameRel.drop R (dep - b)) D (Level.substFn φ cv.levelParams us) dsa b) D
      (Level.substFn φ cv.levelParams us) dsa G) (hG : G mm) :
    AccConcl w ctx prog dep (Expr.mkAppN (.const (D.member mm) us) (ds ++ is))
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) R wa := by
  obtain ⟨hL, -, -, -⟩ := mp.lfp_ok D hD
  obtain ⟨-, isa, hisa, hk⟩ := keyLeaf mp hD hmm hf hbd hwa hlenP hlenI hdsw hdsa
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hlenP hlenI hwD hacc hk
  have hmap : ∀ ρ ρ', R ρ ρ' → isa.map (interp V ρ) = isa.map (interp V ρ') := fun ρ ρ' hr =>
    List.map_congr_left fun v hv => hisC isa hisa v hv ρ ρ' hr
  -- a graded instance's key frame fits the block
  have hkF : ∀ ρ, Sat V Δa ρ → KeyFit D ψ dsa b (dropV (dep - b) ρ) := fun ρ h1 => by
    obtain ⟨hs1, hf1, -⟩ := hk ρ (hgr ρ h1)
    exact ⟨hs1, mm, hmm, _, hf1⟩
  have hpair : ∀ ρ ρ', R ρ ρ' → fitRel (FrameRel.drop R (dep - b)) D ψ dsa b
      (dropV (dep - b) ρ) (dropV (dep - b) ρ') := fun ρ ρ' hr =>
    ⟨⟨ρ, ρ', hr, rfl, rfl⟩, hkF ρ (hR.dom ρ ρ' hr).1, hkF ρ' (hR.dom ρ ρ' hr).2⟩
  obtain ⟨A, hA, hinv, hdef, hacc⟩ := hacc
  have hdef' : DefBound dep fun ρ => A (dropV (dep - b) ρ) := by
    intro tail
    refine ((hdef tail).comp fun j : Fin b => DefFun.proj ⟨j.val + (dep - b), by omega⟩).congr
      fun xs => ?_
    congr 1
    funext i
    by_cases hi : i < b
    · have hid : i + (dep - b) < dep := by omega
      simp [dropV, Semantics.prepend, hi, hid]
    · have hnd : ¬ (i + (dep - b) < dep) := by omega
      simp only [dropV, Semantics.prepend, hi, hnd, ↓reduceDIte]
      congr 1; omega
  refine ⟨?_, ⟨fun ρ => A (dropV (dep - b) ρ), ?_, fun ρ _ _ => hA _, ?_, hdef'⟩,
    outMent_self _ _⟩
  · -- the point (at a `Type`-valued level): the instance is the carrier's
    -- fibre, whose elements are injections, never the point
    intro hw ρ ρ' hr hpt
    exfalso
    obtain ⟨h1, -⟩ := hR.dom ρ ρ' hr
    obtain ⟨hs1, hf1, he1⟩ := hk ρ (hgr ρ h1)
    have hwψ : D.w ψ ≠ 0 := (hwD _ _ (hpair ρ ρ' hr)) ▸ hw
    rw [he1] at hpt
    obtain ⟨j, fs, -, hj⟩ := hL.carrier_case hs1 (Nat.lt_of_lt_of_le hmm hL.kN)
      (tupW_mem hf1) hpt
    exact hL.injNePt ψ hwψ mm j fs hj.symm
  · -- accessibility
    intro ρ ρ₀ hr x _ hx
    obtain ⟨h1, -⟩ := hR.dom ρ ρ₀ hr
    obtain ⟨-, hf1, he1⟩ := hk ρ (hgr ρ h1)
    rw [he1] at hx
    obtain ⟨B, g, hB, ⟨U, hgU⟩, hitems, hs⟩ := hacc mm hG (dropV (dep - b) ρ) (dropV (dep - b) ρ₀)
      (hpair ρ ρ₀ hr) _ (tupW_mem hf1) x hx
    let g' : V := graph (fun q => upOccN_ca (dep - b) (app g q)) B
      (hasGraph_of_defFun1 (defFun_upOccN_ca (dep - b)
        (DefFun.app_apply (DefFun.const g) (DefFun.proj 0))))
    refine ⟨B, g', hB,
      ⟨image (upOccN_ca (dep - b)) U
          (hasImage_of_defFun1 (defFun_upOccN_ca (dep - b) (DefFun.proj 0)) U),
        graph_mem_piSet fun q hq => mem_image.mpr ⟨app g q, app_mem_of_mem_piSet hgU hq, rfl⟩⟩,
      fun q hq => ?_, fun ρ' hr' hheld => ?_⟩
    · obtain ⟨⟨qi, vs, y, heq, hQ⟩, ⟨qi', vs', y', heq', hnp, hy⟩⟩ := hitems q hq
      rw [heq] at heq'
      obtain ⟨rfl, rfl, rfl⟩ := occEncItem_inj heq'
      have hg_app : app g' q = occEncItem (qi + (dep - b)) vs y := by
        rw [app_graph hq, heq, upOccN_ca_occEncItem]
      have hQ' : HoleQ ctx prog dep (qi + (dep - b)) vs.length := by
        have := holeQ_shift (k := dep - b) hQ
        rwa [show b + (dep - b) = dep by omega] at this
      exact ⟨⟨qi + (dep - b), vs, y, hg_app, hQ'⟩, ⟨qi + (dep - b), vs, y, hg_app, hnp, hy⟩⟩
    · obtain ⟨-, h2⟩ := hR.dom ρ ρ' hr'
      obtain ⟨-, -, he2⟩ := hk ρ' (hgr ρ' h2)
      rw [he2, ← hmap ρ ρ' hr']
      exact hs (dropV (dep - b) ρ') (hpair ρ ρ' hr') fun q hq => by
        obtain ⟨⟨qi, vs, y, heq, -⟩, -⟩ := hitems q hq
        obtain ⟨qi', vs', y', heq', hy'⟩ := hheld q hq
        rw [app_graph hq, heq, upOccN_ca_occEncItem] at heq'
        obtain ⟨rqi, rvs, ry⟩ := occEncItem_inj heq'
        refine ⟨qi, vs, y, heq, ?_⟩
        change y ∈ˢ vs.foldl app (ρ' (qi + (dep - b)))
        rwa [rqi, rvs, ry]
  · -- the bound reads parameter positions only
    intro ρ ρ' hag
    refine hinv _ _ fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := hp
    show ρ (p + (dep - b)) = ρ' (p + (dep - b))
    exact hag _ (Or.inr ⟨by omega, by omega⟩)

/-- A frameless frame's accessibility under any frames: a member hole is
admissible there too. -/
theorem FrameAccOut.progNil {w : Nat} {ctx : NestCtx} {prog : List NestHole} {hi : Nat}
    {R₀ : FrameRel V} {D : LfpDatum V} {ψ : Name → Nat} {dsa : List Term} {G : Nat → Prop}
    (h : FrameAccOut w ctx [] hi R₀ D ψ dsa G) : FrameAccOut w ctx prog hi R₀ D ψ dsa G := by
  obtain ⟨A, hA, hinv, hdef, hacc⟩ := h
  refine ⟨A, hA, hinv, hdef, fun c hc ρ ρ₀ hR i hi x hx => ?_⟩
  obtain ⟨B, g, hB, hgU, hitems, hs⟩ := hacc c hc ρ ρ₀ hR i hi x hx
  refine ⟨B, g, hB, hgU, fun b hb => ?_, hs⟩
  obtain ⟨⟨qi, vs, y, heq, hQ⟩, hH⟩ := hitems b hb
  exact ⟨⟨qi, vs, y, heq, holeQ_nil hQ⟩, hH⟩

/-! ## A key, at the block's own depth -/

/-- **A key is accessible** at the block's own depth (a cache hit's
content):
for some recorded block holding its container (at the recorded
parameter count, the container's level parameters distinct, its level
the walk's at every pair fitting the block), along every frameless accessibility hole relation
at the pairs whose key frames fit the block (`fitRel`), the container's carrier is accessible
(`FrameAccOut`, at its own member). -/
@[expose] def KeyAcc (mp : EnvModelM V env) (φ : Name → Nat)
    (w : Nat) (ctx : NestCtx) (key : NestKey) : Prop :=
  ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = key.cname ∧
    ∀ cv caps, env.find? key.cname = some (.indInfo cv caps) →
      key.lvls.length = cv.levelParams.length →
      cv.levelParams.Nodup ∧
      (D.params (Level.substFn φ cv.levelParams key.lvls)).length = key.ds.length ∧
      ∀ (Δ0 : List Term) (R00 : FrameRel V),
        HoleRelA mp.base2 φ w ctx [] (ctx.hiAt 0) Δ0 R00 →
        Δ0.length = ctx.hiAt 0 → (∀ x ∈ key.ds, CtxOkP mp.base2 φ (ctx.hiAt 0) Δ0 x) →
        ∀ dsa, DenoteSpine mp.base2.acval env φ (ctx.hiAt 0) key.ds dsa →
        (∀ ρ ρ', fitRel R00 D (Level.substFn φ cv.levelParams key.lvls) dsa (ctx.hiAt 0) ρ ρ' →
          D.w (Level.substFn φ cv.levelParams key.lvls) = w) ∧
        FrameAccOut w ctx [] (ctx.hiAt 0)
          (fitRel R00 D (Level.substFn φ cv.levelParams key.lvls) dsa (ctx.hiAt 0)) D
          (Level.substFn φ cv.levelParams key.lvls) dsa (fun c => c = mm)

/-- **A cache hit** (a cached instantiation whose parameters lie below
every frame hole): the cached accessibility, at the enclosing relation
seen at the block's own depth, makes the instance accessible. -/
theorem contHit_acc (mp : EnvModelM V env) {w : Nat} {F : Nat}
    {ctx : NestCtx} (hcov : ContCover mp ctx) {prog : List NestHole} {dep : Nat}
    (hhid : ctx.hiAt prog.length ≤ dep) {n : Name} {us : List Level} {ds is : List Expr}
    {wa : Term}
    (hwa : denote mp.base2.acval env φ dep (Expr.mkAppN (.const n us) (ds ++ is)) = some wa)
    {Δa : List Term} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa (Expr.mkAppN (.const n us) (ds ++ is)))
    (hgr : GradedTy V Δa wa) (hR : HoleRelA mp.base2 φ w ctx prog dep Δa R)
    (hisC : ∀ isa, DenoteSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true)
    (hfree : ∀ x ∈ ds, x.fvarB ≤ ctx.hiAt 0) {nI : Nat} {cty : Expr}
    (hnI : ConLeche.nestInstType (m := CheckM) ctx (ConLeche.fueledOps .verified F) env
      (ctx.hiAt prog.length) ⟨n, us, ds⟩ = .ok (nI, cty))
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
  obtain ⟨fa, vs, hfa, hsp, -⟩ := denote_mkAppN_inv hwa
  obtain ⟨hul, -⟩ := Rules.denote_const_arityK hf hfa
  change us.length = cv.levelParams.length at hul
  obtain ⟨hnd, hlenP, hacc0⟩ := hk cv caps hf hul
  obtain ⟨vs₁, vs₂, -, hsp₁, -⟩ := DenoteSpine.split _ hsp
  obtain ⟨dsa0, hdsa0, -⟩ := DenoteSpine.unlift (m := mp.base2) (φ := φ) hle0d hds0 hsp₁
  obtain ⟨dsa, hdsa, -⟩ := DenoteSpine.unlift (m := mp.base2) (φ := φ) hhid
    (fun x hx => (hdsw x hx).1) hsp₁
  -- the index count
  have hids := hcov.idsLen hD hmm hf hnI hlenP hdsw hdsa
  -- the cached accessibility at the enclosing relation seen at the block's depth
  have hR00 := hR.dropBase hhid
  have hC0 : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt 0) (Δa.drop (dep - ctx.hiAt 0)) x :=
    fun x hx => hC.drop hle0d fun l hl =>
      ⟨leaves_mkAppN_arg (List.mem_append_left _ hx) hl,
        ConLeche.Expr.fvarLeaves_lt_of_wscoped (hds0 x hx) l hl⟩
  obtain ⟨hwD, hacc⟩ := hacc0 _ _ hR00 (by rw [List.length_drop, hC.1]; omega) hC0 dsa0 hdsa0
  exact accConcl_of_frameAccOut mp hD hmm hf hle0d hwa hlenP.symm (by rw [hids, hisl]) hds0 hdsa0
    hR hgr hisC hwD hacc.progNil rfl

end ConLeche.Model
