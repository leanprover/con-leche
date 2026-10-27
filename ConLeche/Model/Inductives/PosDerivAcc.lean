module

public import ConLeche.Model.Inductives.ContAcc
import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Model.Inductives.NestPosAccKit
import ConLeche.Model.Inductives.ContN2
import ConLeche.Verify.Cached.Erase
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Semantics.Frame
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Inductives.TypeStep
import ConLeche.Verify.Denote.IndFrame

public section

/-!
# The positivity derivation is ACCESSIBLE in the holes

The twin of `PosDerivMono.lean` for the closure witness (W): joint
accessibility at the instantiation is proved by INDUCTION ON THE
DERIVATION `PosD`, never on the run.  The run is read once, by `nestPos_deriv`.

The motive `AccJ` reads each judgment along an accessibility hole
relation (`HoleRelA`, `NestPosAcc.lean`), carrying the walked subjects'
`GradedTy` (task #342, L12): every field, telescope and crest here is a
constructor's field TYPE, never the point ("not pt" source (1)), so the
whnf step is `red_sound_ty`, not the global `red_sound`:

* `field` — the point's stability, accessibility with a bound of the level
  reading only the non-hole positions the output mentions, and the
  output's facts (`AccConcl`, `OutOk`): the whnf step by `red_sound_ty`;
  `const` (the empty bound); `pi` (a hole-free domain, the body under
  `underBoth`, its fibres types by the grading); `hole` and `frameHole`
  (the bound `{pt}`, never the point at full arity); a container instance by its frame's conclusion at the key
  frames (`accConcl_of_frameAccOut`);
* `tele` — every field accessible under the earlier ones (`PiAccThen`,
  `OutTele`);
* `ctors` — every constructor of the frame's group walked
  (`CtorWalkedA`);
* `frame` — the reached group well formed, at the walk context's level,
  its carriers accessible in the enclosing frame (`FrameAccJ`, from
  `frameIterAcc`).

The container rules are the only place coverage and the walk context's
sort are read (`ContOk`): a field of a FLAT kind never meets one, so a
flat constructor needs neither.  A cache hit (`contHit`) reads its
frame's conclusion under the frames of its first walk, extended by empty
ones and seen at the block's own depth (`KeyAcc`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules

open ConLeche (Env Expr Name Level ConstantVal CheckM NestCtx NestKey NestHole instPisWith fueledOps
  PosD PosJ NestFieldKind PosTree ProgScoped grpNews grpHoles groupCtors)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The motive -/

section Motive

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (w : Nat)
  (ctx : NestCtx) (F : Nat)

/-- **What the container rules read**: coverage and the walk
context's sort at the level (the container case's point, N3). -/
@[expose] def ContOk : Prop := ContCover mp ctx ∧ ctx.sort.eval φ = w

/-- **A frame's conclusion**: at every recorded block holding the frame's
head, the group well formed, the level parameters distinct, the block at
the level, and the group's carriers accessible in the enclosing frame
(`FrameAccOut`). -/
@[expose] def FrameAccJ (prog : List NestHole) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) : Prop :=
  ContOk mp φ w ctx →
  ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks → ∀ {mm : Nat}, mm < D.k →
    D.member mm = (grp.headD default).1 →
  ∀ {lps : List Name},
    (∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = lps) →
    us.length = lps.length →
    (∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true) →
    ∀ {dsa : List Term}, DenoteSpine mp.base2.acval env φ (ctx.hiAt prog.length) ds dsa →
    (D.params (Level.substFn φ lps us)).length = ds.length →
    ((∃ nP' L, ConLeche.nestContainer ctx (D.member mm) = some (nP', L) ∧ L ≠ []) ∨ lps.Nodup) →
    ∀ {Δh : List Term} {R₀ : FrameRel V},
    HoleRelA mp.base2 φ w ctx prog (ctx.hiAt prog.length) Δh R₀ →
    Δh.length = ctx.hiAt prog.length →
    (∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt prog.length) Δh x) →
    (∀ x ∈ ds, Expr.LeavesBounded x) →
    lps.Nodup ∧ GrpOk ctx D (ctx.hiAt prog.length) us ds grp ∧
      D.w (Level.substFn φ lps us) = w ∧
      FrameAccOut w ctx prog (ctx.hiAt prog.length) R₀ D (Level.substFn φ lps us) dsa (InGrp D grp)

/-- **What a derivation proves** of its judgment's reading (see the
module docstring). -/
@[expose] def AccJ : PosJ → Prop
  | .field prog dep _ e k nf =>
    (k.flat = false → ContOk mp φ w ctx) → ctx.hiAt prog.length ≤ dep → Frame dep e →
    ∀ {Δa : List Term} {ea : Term} {R : FrameRel V},
      CtxOkP mp.base2 φ dep Δa e → denote mp.base2.acval env φ dep e = some ea →
      GradedTy V Δa ea → HoleRelA mp.base2 φ w ctx prog dep Δa R →
      AccConcl w ctx prog dep e nf R ea ∧ OutOk mp.base2 φ ctx prog dep Δa k nf ea
  | .tele prog base nF j cur ks nds res =>
    ((∃ k ∈ ks, k.flat = false) → ContOk mp φ w ctx) → ctx.hiAt prog.length ≤ base + j →
    Frame (base + j) cur →
    ∀ {Δa : List Term} {ca : Term} {R : FrameRel V},
      CtxOkP mp.base2 φ (base + j) Δa cur →
      denote mp.base2.acval env φ (base + j) cur = some ca → GradedTy V Δa ca →
      HoleRelA mp.base2 φ w ctx prog (base + j) Δa R →
      PiAccThen w ctx prog (ResultAt mp.base2 φ ctx.nP (ctx.hiAt prog.length) (base + j + nF) res)
        nF (base + j) nds R ca ∧
      OutTele mp.base2 φ ctx prog ks nds (base + j) Δa ca
  | .ctors prog hi us ds names holes cs =>
    ContOk mp φ w ctx → ctx.hiAt prog.length = hi →
    ∀ {Δ : List Term} {R : FrameRel V}, HoleRelA mp.base2 φ w ctx prog hi Δ R →
    ∀ (Q : ConstantVal × Nat → Prop),
    (∀ (x : ConstantVal × Nat) (crest : Expr), Q x →
      ConLeche.nestCrest names us ds holes (x.1.type.instantiateLevelParams x.1.levelParams us)
        = some crest →
      (∃ ty u, ConLeche.inferTypeCore .verified env F hi crest = .ok ty ∧
        ConLeche.ensureSortCore .verified env F hi ty = .ok u) →
      ∃ ca, Frame hi crest ∧ CtxOkP mp.base2 φ hi Δ crest ∧
        denote mp.base2.acval env φ hi crest = some ca ∧ GradedTy V Δ ca) →
    (∀ x ∈ cs, Q x) → ∀ x ∈ cs, CtorWalkedA mp.base2 φ w ctx prog hi us ds names holes Δ R x
  | .frame prog us ds grp => FrameAccJ mp φ w ctx prog us ds grp
  | .seed _ => True

end Motive

variable {φ : Name → Nat}

/-! ## The whnf step -/

/-- **The whnf step** of every field rule: the reduct reads as the term,
so it is enough to prove the reduct's reading accessible (its output
mentioning only the term's leaves).  The subject walked here is always a
TYPE (task #342, L12: "not pt" source (1)), so the step is
`red_sound_ty`. -/
theorem acc_of_whnf {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env}
    (hin : RulesInputs V mp.base2 φ) {F dep : Nat} {e wt : Expr}
    (hw : (fueledOps .verified F).whnf env dep e = .ok wt) (hfr : Frame dep e)
    {Δa : List Term} {ea : Term} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa e) (hea : denote mp.base2.acval env φ dep e = some ea)
    (hgr : GradedTy V Δa ea) (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ')
    {w : Nat} {ctx : NestCtx} {prog : List NestHole} {k : NestFieldKind} {nf : Expr}
    (kont : Frame dep wt → CtxOkP mp.base2 φ dep Δa wt →
      (∀ l ∈ wt.fvarLeaves, l ∈ e.fvarLeaves) → ∀ wa,
      denote mp.base2.acval env φ dep wt = some wa → GradedTy V Δa wa →
      (∀ ρ, Sat V Δa ρ → interp V ρ ea = interp V ρ wa) →
      AccConcl w ctx prog dep e nf R wa ∧ OutOk mp.base2 φ ctx prog dep Δa k nf wa) :
    AccConcl w ctx prog dep e nf R ea ∧ OutOk mp.base2 φ ctx prog dep Δa k nf ea := by
  have hw' : ConLeche.whnf .verified env F dep e = .ok wt := hw
  obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ :=
    red_sound_ty hin (ConLeche.Rules.whnf_bridge hw') hfr hC.toCtxOk hea hgr
  obtain ⟨⟨hTR, ⟨A, hA, hsz, hinv⟩, hout⟩, hok⟩ := kont hfrw (hC.of_subset hsub)
    (ConLeche.whnf_fvarLeaves mp.base2.wf F hw') wa hwa hgw heq
  exact ⟨⟨fun hw => PtOn.of_eqOn (P := Sat V Δa) hdom (fun ρ hρ => heq ρ hρ) (hTR hw),
    ⟨A, AccOn.of_eqOn (P := Sat V Δa) hdom (fun ρ hρ => heq ρ hρ) hA, hsz, hinv⟩, hout⟩,
    hok.congr_read fun ρ hρ => (heq ρ hρ).symm⟩

/-! ## The frame -/

/-- **A frame's conclusion from its derivation**: the group well formed,
the level parameters distinct (`frame_lps_nodup`), the block at the walk
context's level (`n2_sort` at the head), and `frameIterAcc` along the
walked constructors. -/
theorem frame_accD {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} {ctx : NestCtx} {F : Nat}
    {prog : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {ctors : List (ConstantVal × Nat)} (hne : grp ≠ []) (hnd : (grp.map (·.1)).Nodup)
    (hinst : ∀ p ∈ grp, ∃ nI, ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
      ⟨p.1, us, ds⟩ = .ok (nI, p.2))
    (hgrp : grp.map (·.1) = (grp.headD default).1 :: ConLeche.nestFrameMates ctx (grp.headD default).1)
    (hctors : groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    (hkty : ∃ ty, (fueledOps .verified F).inferType env (ctx.hiAt prog.length)
      (Expr.mkAppN (.const (grp.headD default).1 us) ds) = .ok ty)
    {ts : List PosTree}
    (hwalkD : PosD (fueledOps .verified F) env ctx
      (.ctors ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
        (ctx.hiAt prog.length + grp.length) us ds (grp.map (·.1))
        (grpHoles (ctx.hiAt prog.length) grp) ctors) ts)
    (ih : AccJ mp φ w ctx F
      (.ctors ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
        (ctx.hiAt prog.length + grp.length) us ds (grp.map (·.1))
        (grpHoles (ctx.hiAt prog.length) grp) ctors)) :
    FrameAccJ mp φ w ctx prog us ds grp := by
  intro hok D hD mm hmm hhead lps hlps hul hds dsa hdsa hlenP hnL Δh R₀ hR₀ hΔ hCds hLds
  have hcov := hok.1
  have hblkD := hcov.block D hD
  have hkN := lfp_namesLen mp hD
  have hg := frame_grpOk mp hcov hne hnd hinst hgrp hD hmm hhead hlps
  obtain ⟨p₀, ps₀, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.headD_cons] at hhead hkty
  obtain ⟨cv₀, caps₀, hf₀, hlp₀⟩ := hlps mm hmm
  -- the level parameters are distinct, the block at the level (N3 at the head)
  have hndl : lps.Nodup := frame_lps_nodup mp hcov hD hmm hlps (by rw [hhead]; simp) hctors
    (posD_ctors_nodup hwalkD) hnL
  have hwD : D.w (Level.substFn φ lps us) = w := by
    obtain ⟨nI₀, hnI₀⟩ := hinst p₀ List.mem_cons_self
    have := n2_sort mp hD hmm hcov.find (by rw [hhead]; exact hnI₀) hf₀ (by rw [hlp₀]; exact hndl)
      (by rw [hlp₀]; exact hul) (by rw [hlp₀]; exact hlenP) hds hdsa
    rw [hlp₀] at this
    exact this.trans hok.2
  -- the key, graded
  have hkey := frameKey_of_infer mp hin hD hmm hf₀ (by rw [hlp₀]; exact hul) hds hLds hΔ hCds
    hdsa (by rw [hlp₀]; exact hlenP) (by rw [hhead]; exact hkty)
    (frame_head_instPis hcov.find (hinst p₀ List.mem_cons_self) (hhead ▸ hf₀))
  rw [hlp₀] at hkey
  exact ⟨hndl, hg, hwD, frameIterAcc mp hD hblkD.nodup hkN hcov.find hlps hndl hul hds hdsa hlenP
    hg.2 hin hwD hblkD.ctors rfl hR₀ hΔ hCds hLds hkey hctors
    (fun hR Q hprem hQ => ih hok (by simp [grpNews, ConLeche.NestCtx.hiAt]; omega) hR Q hprem hQ)⟩

/-! ## The container instance -/

/-- **A container instance whose frame is derived HERE** (`contNew`): the
frame's conclusion at the enclosing relation seen at the key's depth makes
the instance accessible (the leaf, `accConcl_of_frameAccOut`). -/
theorem contNew_accD {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {w : Nat}
    {ctx : NestCtx} (hok : ContOk mp φ w ctx) {prog : List NestHole} {dep : Nat}
    (hhid : ctx.hiAt prog.length ≤ dep) {D : LfpDatum V} (hD : D ∈ mp.lfpBlocks) {mm : Nat}
    (hmm : mm < D.k) {lps : List Name}
    (hlps : ∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = lps)
    {us : List Level} (hul : us.length = lps.length) {ds is : List Expr}
    (hdsw : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true)
    (hLds : ∀ x ∈ ds, Expr.LeavesBounded x)
    (hlenP : ∀ ψ, (D.params ψ).length = ds.length)
    (hnL : (∃ L', ConLeche.nestContainer ctx (D.member mm) = some (ds.length, L') ∧ L' ≠ []) ∨
      lps.Nodup)
    {wa : Term}
    (hwa : denote mp.base2.acval env φ dep
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) = some wa)
    {Δa : List Term} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)))
    (hgr : GradedTy V Δa wa) (hR : HoleRelA mp.base2 φ w ctx prog dep Δa R)
    (hisC : ∀ isa, DenoteSpine mp.base2.acval env φ dep is isa → ∀ v ∈ isa, ConstOn R v)
    {nI : Nat} {cty : Expr}
    (hnI : ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length) ⟨D.member mm, us, ds⟩
      = .ok (nI, cty))
    (hisl : is.length = nI) {grp : List (Name × Expr)} (hhead : D.member mm = (grp.headD default).1)
    (ihf : FrameAccJ mp φ w ctx prog us ds grp) :
    AccConcl w ctx prog dep (Expr.mkAppN (.const (D.member mm) us) (ds ++ is))
      (Expr.mkAppN (.const (D.member mm) us) (ds ++ is)) R wa := by
  obtain ⟨cv, caps, hf, hcvl⟩ := hlps mm hmm
  -- the key's parameters read at the key's depth
  obtain ⟨fa, vs, -, hsp, -⟩ := denote_mkAppN_inv hwa
  obtain ⟨vs₁, vs₂, -, hsp₁, -⟩ := DenoteSpine.split _ hsp
  obtain ⟨dsa, hdsa, -⟩ := DenoteSpine.unlift (m := mp.base2) (φ := φ) hhid
    (fun x hx => (hdsw x hx).1) hsp₁
  -- the relation at the key's depth
  have hR₀ := hR.drop (Nat.le_refl _) hhid
  have hΔ : (Δa.drop (dep - ctx.hiAt prog.length)).length = ctx.hiAt prog.length := by
    rw [List.length_drop, hC.1]; omega
  have hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt prog.length)
      (Δa.drop (dep - ctx.hiAt prog.length)) x := fun x hx =>
    hC.drop hhid fun l hl => ⟨leaves_mkAppN_arg (List.mem_append_left _ hx) hl,
      ConLeche.Expr.fvarLeaves_lt_of_wscoped (hdsw x hx).1 l hl⟩
  obtain ⟨hnd, hg', hwD, hacc⟩ := ihf hok hD hmm hhead hlps hul hdsw hdsa (hlenP _)
    (hnL.imp (fun ⟨L, hL, hLne⟩ => ⟨_, L, hL, hLne⟩) id) hR₀ hΔ hCds hLds
  have hheadmem : (D.member mm, (grp.headD default).2) ∈ grp := by
    obtain ⟨p₀, ps₀, hp₀⟩ := List.exists_cons_of_ne_nil hg'.1
    rw [hp₀] at hhead ⊢
    simp only [List.headD_cons] at hhead ⊢
    rw [hhead]
    exact List.mem_cons_self
  obtain ⟨-, hids, -⟩ := n2_link mp hD hmm hok.1.find hnI hf (by rw [hcvl]; exact hnd)
    (by rw [hcvl]; exact hul) (by rw [hcvl, hlenP]) hdsw hdsa
  rw [← hcvl] at hacc hwD
  exact accConcl_of_frameAccOut mp hD hmm hf hhid hwa (by rw [hlenP]) (by rw [hids, hisl])
    (fun x hx => (hdsw x hx).1) hdsa hR hgr hisC hwD hacc
    ⟨hmm, by rw [List.contains_iff_mem, List.mem_map]; exact ⟨_, hheadmem, rfl⟩⟩

/-- **A key whose frame is derived is accessible at the block's own
depth** (`KeyAcc`, a cache hit's content): its frame, derived under a
well-scoped frame stack, read along the frameless relation extended by
EMPTY frames for that stack, and back through the empty frames
(`frameAccOut_unextend`). -/
theorem keyAcc_of_frameD {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {w : Nat}
    {ctx : NestCtx} (hok : ContOk mp φ w ctx) {F : Nat} {key : NestKey} {prog' : List NestHole}
    {grp : List (Name × Expr)} (hsc : ProgScoped ctx prog') (hmem : key.cname ∈ grp.map (·.1))
    {ts : List PosTree}
    (hfrD : PosD (fueledOps .verified F) env ctx (.frame prog' key.lvls key.ds grp) ts)
    (ihf : FrameAccJ mp φ w ctx prog' key.lvls key.ds grp)
    (hds : ∀ x ∈ key.ds, Expr.WScoped (ctx.hiAt 0) x ∧ x.looseBVarsBounded 0 = true)
    (hLds : ∀ x ∈ key.ds, Expr.LeavesBounded x) : KeyAcc mp φ w ctx key := by
  have hcov := hok.1
  obtain ⟨D, hD, mm, hmm, hn, hmmG, mm₀, hmm₀, hn₀, lps, hlps, hlenP, hnd, hcvl⟩ :=
    frame_keyBlock mp hcov hmem hfrD
  refine ⟨D, hD, mm, hmm, hn, fun cv caps hf hul => ?_⟩
  rw [hcvl cv caps hf] at hul ⊢
  refine ⟨hnd, hlenP _, fun Δ0 R00 hR00 hΔ0 hC0 dsa0 hdsa0 => ?_⟩
  -- the first walk's frames, empty
  have hle0' : ctx.hiAt 0 ≤ ctx.hiAt prog'.length := by simp only [ConLeche.NestCtx.hiAt]; omega
  have hhiEq : ctx.hiAt prog'.length = ctx.hiAt 0 + prog'.length := by
    simp only [ConLeche.NestCtx.hiAt]; omega
  have hR₀ := HoleRelA.extendEmpty hR00 prog' hsc
  have hdsaL := DenoteSpine.lift (m := mp.base2) (φ := φ) hle0' (fun x hx => (hds x hx).1) hdsa0
  rw [show ctx.hiAt prog'.length - ctx.hiAt 0 = prog'.length by rw [hhiEq]; omega] at hdsaL
  have hCds : ∀ x ∈ key.ds, CtxOkP mp.base2 φ (ctx.hiAt prog'.length)
      (List.replicate prog'.length (.sort 0) ++ Δ0) x := by
    intro x hx
    have := CtxOkP.extend (h := ctx.hiAt 0) (g := prog'.length)
      (Ts := List.replicate prog'.length (.sort 0)) (by simp) hΔ0
      (fun l hl => Or.inl ((hC0 x hx).2 l hl))
    rwa [← hhiEq] at this
  obtain ⟨-, -, hwD, hacc⟩ := ihf hok hD hmm₀ hn₀ hlps hul
    (fun x hx => ⟨Expr.WScoped.mono hle0' (hds x hx).1, (hds x hx).2⟩) hdsaL (hlenP _)
    (Or.inr hnd) hR₀
    (by rw [List.length_append, List.length_replicate, hΔ0, hhiEq]; omega) hCds hLds
  exact ⟨hwD, frameAccOut_unextend (hacc.mono fun c hc => hc ▸ hmmG)⟩

/-! ## THE INDUCTION -/

set_option maxHeartbeats 800000 in
/-- **THE DERIVATION IS ACCESSIBLE** (charter items 2–4): every judgment of a positivity derivation reads
accessibly in the holes, at every level (task #327), by induction on the
derivation (see the module docstring). -/
theorem posD_acc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} {ctx : NestCtx} {F : Nat} :
    ∀ {j : PosJ} {ts : List PosTree}, PosD (fueledOps .verified F) env ctx j ts →
      AccJ mp φ w ctx F j := by
  intro j ts h
  induction h with
  | @const prog dep kb e wt hw' hocc =>
    intro _ hhi hfr Δa ea R hC hea hgr hR
    refine acc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw _ hlw wa hwa _ heq => ?_
    have hco : ConstOn R wa := ConstOn.of_noBVar hR.agree
      (denote_noBVar_of_nestOcc dep wt hfrw.1 hhi hocc hwa)
    refine ⟨⟨fun _ => hco.ptOn, ⟨_, hco.accOn, SizeOn.const (empty_mem_tg w), InvOn.const _ _⟩, ?_⟩, ?_⟩
    · split
      · exact (outMent_self dep wt).trans hlw
      · exact outMent_self dep e
    · split
      · exact ⟨hfrw.2.1, hfrw.1, fun _ => hocc, wa, hwa, fun _ _ => rfl⟩
      · rename_i hne
        exact ⟨hfr.2.1, hfr.1, fun _ => by simpa using hne, ea, hea, fun ρ hρ => heq ρ hρ⟩
  | @pi prog dep kb e a b k nb ts hw' hocc ha hb ihb =>
    intro hcovk hhi hfr Δa ea R hC hea hgr hR
    refine acc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw hCw hlw wa hwa hgw _ => ?_
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_forallE_inv hwa
    obtain ⟨hws, hbb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hholes : NoBVar (holeP dep ctx.nP (ctx.hiAt prog.length)) ta :=
      denote_noBVar_of_nestOcc dep a hws.1 hhi ha hta
    have hA : ConstOn R ta := ConstOn.of_noBVar hR.agree hholes
    obtain ⟨hgAT, hgB⟩ := WellDenoted.hoist_piTy' (V := V) hgw.graded
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgAT
    obtain ⟨⟨hTRb, ⟨Ab, hAb, hszb, hinvb⟩, houtb⟩, hokb⟩ := ihb hcovk (by omega)
      (frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd) hCop hba hgB
      (hR.underBoth hhi ta)
    have hout : OutMent dep e (.forallE a (nb.abstract1 dep 0)) := by
      intro q hq ho
      simp only [ConLeche.Expr.nestOcc, Bool.or_eq_true] at ho
      have hwa' : ∀ l ∈ a.fvarLeaves, l ∈ e.fvarLeaves :=
        fun l hl => hlw l (by simp [Expr.fvarLeaves, hl])
      rcases ho with ho | ho
      · obtain ⟨l, hl, rfl⟩ := leaf_of_nestOcc ho
        exact ⟨l, hwa' l hl, rfl⟩
      · rw [nestOcc_abstract1 (by omega) nb 0] at ho
        obtain ⟨l, hl, hlq⟩ := houtb q (by omega) ho
        rcases ConLeche.Expr.fvarLeaves_instantiate1 b 0 hl with hl' | hl'
        · exact ⟨l, hlw l (by simp [Expr.fvarLeaves, hl']), hlq⟩
        · simp only [Expr.fvarLeaves, List.mem_cons] at hl'
          rcases hl' with rfl | hl'
          · simp at hlq; omega
          · exact ⟨l, hwa' l hl', hlq⟩
    have hokP : OutOk mp.base2 φ ctx prog dep Δa k (.forallE a (nb.abstract1 dep 0))
        (.pi ta ba) := by
      obtain ⟨hnbB, hnbW, hnbO, nba, hnba, hnbr⟩ := hokb
      refine ⟨?_, ?_, fun hk => ?_, .pi ta nba, ?_, fun ρ hρ => ?_⟩
      · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
        exact ⟨hbb.1, ConLeche.looseBVarsBounded_abstract1 nb 0 hnbB⟩
      · simp only [Expr.WScoped]
        exact ⟨hws.1, ConLeche.WScoped.abstract1 0 hnbW⟩
      · simp only [ConLeche.Expr.nestOcc, ha, Bool.false_or]
        rw [nestOcc_abstract1 (by omega) nb 0]
        exact hnbO hk
      · rw [denote_forallE, hta]
        simp only [Option.bind_eq_bind, Option.bind_some]
        rw [denote_erasedEq (erasedEq_abstract1_instantiate1 nb 0 hnbB) (dep + 1), hnba]
        rfl
      · exact interp_pi_congr_body fun x hx => hnbr (cons x ρ) (Sat_cons V hρ hx)
    -- the body's fibres are types at both frames of every related pair
    -- ("not pt" source (1): the walked field is a graded type)
    have hT : FibTyOn R ta ba := fun ρ ρ' hr => by
      obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
      exact ⟨fun x hx => (hgB _ (Sat_cons V h1 hx)).2, fun x hx => (hgB _ (Sat_cons V h2 hx)).2⟩
    refine ⟨⟨fun hw => PtOn.pi hA hT (hTRb hw), ?_, hout⟩, hokP⟩
    have hinvP : InvOn (MentP ctx.nP (ctx.hiAt prog.length) dep
        (.forallE a (nb.abstract1 dep 0))) (piBound w ta Ab) := InvOn.pi (NoBVar.mono (fun i hi hn => hi (Or.inl hn))
        (noBVar_not_mentNH hws.1 hbb.1 hholes (fun s _ hs => by
          simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hs
          exact hs.1) hta)) (InvOn.mono hinvb fun i hi => mentP_body i hi)
    have hAb' := AccOn.congrQ (fun i n => (shiftQ_holeQ hhi i n).symm) hAb
    exact ⟨_, AccOn.pi hA hAb' hT hTRb, SizeOn.pi hA hszb, hinvP⟩
  | @hole prog dep kb e wt i ty hw' hocc hfn hlo hhi' hlen hfree =>
    intro _ hhi hfr Δa ea R hC hea hgr hR
    refine acc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw _ hlw wa hwa _ _ => ?_
    have hspine := Expr.mkAppN_getApp wt
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denote_mkAppN_inv hwa
    rw [denote_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ wt.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    have hlenv := DenoteSpine.length_eq hsp
    have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
    have hQ : HoleQ ctx prog dep (dep - 1 - i) vs.length := by
      refine Or.inl ⟨i - ctx.nP, ?_, ?_, by omega, by rw [← hlenv, hlen]⟩
      · simp only [NestCtx.hiAt] at hhi'; omega
      · simp only [NestCtx.hiAt] at hhi' hhi; omega
    refine ⟨⟨fun hw => PtOn.holeApp (hR.ptFree hw) hQ, ⟨_, AccOn.holeApp hQ hvs,
      SizeOn.const (unitSet_mem_tg w), InvOn.const _ _⟩, (outMent_self dep wt).trans hlw⟩,
      hfrw.2.1, hfrw.1, fun hk => ?_, _, by rw [hspine] at hwa; exact hwa, fun _ _ => rfl⟩
    split at hk <;> cases hk
  | @frameHole prog dep kb e wt i ty h hw' hocc hfn hlo hhi' hk hfree har =>
    intro _ hhi hfr Δa ea R hC hea hgr hR
    refine acc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw _ hlw wa hwa _ _ => ?_
    have hspine := Expr.mkAppN_getApp wt
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denote_mkAppN_inv hwa
    rw [denote_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ wt.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    have hlenv := DenoteSpine.length_eq hsp
    have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
    have hQ : HoleQ ctx prog dep (dep - 1 - i) vs.length := by
      refine Or.inr ⟨i - ctx.hiAt 0, h, hk, by omega, by omega, ?_⟩
      rw [← hlenv, har]
    exact ⟨⟨fun hw => PtOn.holeApp (hR.ptFree hw) hQ, ⟨_, AccOn.holeApp hQ hvs,
      SizeOn.const (unitSet_mem_tg w), InvOn.const _ _⟩, (outMent_self dep wt).trans hlw⟩,
      hfrw.2.1, hfrw.1, nofun, _, by rw [hspine] at hwa; exact hwa, fun _ _ => rfl⟩
  | @contNew prog dep kb e wt n us L nPc nI cty grp ts hw' hocc hfn hnm hq hlen hquot hidx hds _
      hnI hhead _ hfrD ihf =>
    intro hcovk hhid hfr Δa ea R hC hea hgr hR
    have hok := hcovk rfl
    have hcov := hok.1
    refine acc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw hCw hlw wa hwa hgw _ => ?_
    obtain ⟨cv, caps, hfc⟩ := nestContainer_find hq
    rw [hcov.find] at hfc
    obtain ⟨D, hD, mm, hmm, hn⟩ := hcov.cover n cv caps hfc hnm hquot
    subst hn
    obtain ⟨lps, hlps, hlenP0, hcvl, hnL0⟩ := contBlock_facts mp hcov hD hmm hfc hq
    have hwa0 := hwa
    have hspine := Expr.mkAppN_getApp wt
    rw [hfn] at hspine
    generalize hargs : wt.getAppArgs = args at hspine hlen hidx hds hnI hfrD ihf
    subst hspine
    rw [← List.take_append_drop nPc args] at hwa hCw
    have hdl : (args.take nPc).length = nPc := by rw [List.length_take]; omega
    have hwsargs := (wScoped_mkAppN _ hfrw.1).2
    have hdsw : ∀ x ∈ args.take nPc, Expr.WScoped (ctx.hiAt prog.length) x ∧
        x.looseBVarsBounded 0 = true := fun x hx =>
      ⟨ConLeche.WScoped.of_fvarsBelow (hwsargs x (List.mem_of_mem_take hx))
        (ConLeche.Expr.fvarB_le (hds x hx).2), ConLeche.Expr.bvarB_le (Nat.le_of_eq (hds x hx).1)⟩
    have hLds : ∀ x ∈ args.take nPc, Expr.LeavesBounded x := fun x hx l hl =>
      hfrw.2.2 l (leaves_mkAppN_arg (List.mem_of_mem_take hx) hl)
    have hisC : ∀ isa, DenoteSpine mp.base2.acval env φ dep (args.drop nPc) isa →
        ∀ v ∈ isa, ConstOn R v := fun isa hisa =>
      constOn_spine hR.agree hhid hisa fun a ha => ⟨hwsargs a (List.mem_of_mem_drop ha), hidx a ha⟩
    have hisl : (args.drop nPc).length = nI := by rw [List.length_drop]; omega
    obtain ⟨fa, vs, hfa, -, -⟩ := denote_mkAppN_inv hwa
    obtain ⟨hul, -⟩ := Rules.denote_const_arityK hfc hfa
    change us.length = cv.levelParams.length at hul
    rw [hcvl] at hul
    have hhead' : D.member mm = (grp.headD default).1 := by
      cases grp with
      | nil => simp at hhead
      | cons p ps =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        rw [List.headD_cons, hhead]
    have hc := contNew_accD mp hok hhid hD hmm hlps hul hdsw hLds
      (fun ψ => by rw [hdl]; exact hlenP0 ψ) (by rw [hdl]; exact hnL0) hwa hCw hgw hR hisC hnI
      hisl hhead' ihf
    rw [List.take_append_drop] at hc
    exact ⟨⟨hc.1, hc.2.1, hc.2.2.trans hlw⟩, hfrw.2.1, hfrw.1, nofun, wa, hwa0, fun _ _ => rfl⟩
  | @contHit prog dep kb e wt n us L nPc nI cty grp ts hw' hocc hfn hnm hq hlen hquot hidx
      hds _ hnI hmem hfrD ihf =>
    intro hcovk hhid hfr Δa ea R hC hea hgr hR
    have hok := hcovk rfl
    refine acc_of_whnf hin hw' hfr hC hea hgr hR.dom fun hfrw hCw hlw wa hwa hgw _ => ?_
    have hwa0 := hwa
    have hspine := Expr.mkAppN_getApp wt
    rw [hfn] at hspine
    generalize hargs : wt.getAppArgs = args at hspine hlen hidx hds hnI hfrD ihf
    subst hspine
    rw [← List.take_append_drop nPc args] at hwa hCw
    have hwsargs := (wScoped_mkAppN _ hfrw.1).2
    have hle0 : ctx.hiAt 0 ≤ ctx.hiAt prog.length := by simp only [ConLeche.NestCtx.hiAt]; omega
    have hdsw : ∀ x ∈ args.take nPc, Expr.WScoped (ctx.hiAt prog.length) x ∧
        x.looseBVarsBounded 0 = true := fun x hx =>
      ⟨ConLeche.WScoped.of_fvarsBelow (hwsargs x (List.mem_of_mem_take hx))
        (ConLeche.Expr.fvarB_le (Nat.le_trans (hds x hx).2 hle0)),
        ConLeche.Expr.bvarB_le (Nat.le_of_eq (hds x hx).1)⟩
    have hds0 : ∀ x ∈ args.take nPc, Expr.WScoped (ctx.hiAt 0) x ∧
        x.looseBVarsBounded 0 = true := fun x hx =>
      ⟨ConLeche.WScoped.of_fvarsBelow (hdsw x hx).1 (ConLeche.Expr.fvarB_le (hds x hx).2),
        (hdsw x hx).2⟩
    have hLds : ∀ x ∈ args.take nPc, Expr.LeavesBounded x := fun x hx l hl =>
      hfrw.2.2 l (leaves_mkAppN_arg (List.mem_of_mem_take hx) hl)
    have hisC : ∀ isa, DenoteSpine mp.base2.acval env φ dep (args.drop nPc) isa →
        ∀ v ∈ isa, ConstOn R v := fun isa hisa =>
      constOn_spine hR.agree hhid hisa fun a ha => ⟨hwsargs a (List.mem_of_mem_drop ha), hidx a ha⟩
    have hisl : (args.drop nPc).length = nI := by rw [List.length_drop]; omega
    have hkp := keyAcc_of_frameD mp hok (key := ⟨n, us, args.take nPc⟩) (ConLeche.ProgScoped.nil (ctx := ctx)) hmem
      hfrD ihf hds0
      hLds
    have hc := contHit_acc mp hok.1.find hhid hwa hCw hgw hR hisC hdsw (fun x hx => (hds x hx).2)
      hnI hisl hkp
    rw [List.take_append_drop] at hc
    exact ⟨⟨hc.1, hc.2.1, hc.2.2.trans hlw⟩, hfrw.2.1, hfrw.1, nofun, wa, hwa0, fun _ _ => rfl⟩
  | @frame prog us ds grp ctors ts hne hhd hhdC hnd hinst hblk hgrp hctors hkty hwalk ih =>
    exact frame_accD mp hin hne hnd hinst hgrp hctors hkty hwalk ih
  | ctorsNil =>
    intro _ _ Δ R _ Q _ _ x hx
    exact nomatch hx
  | @ctorsCons prog hi us ds names holes cv nF cs crest ty sv ks nds cur ts ts' hnd hcrest hty
      hsort htele hu4 hres hidx hrest ihtele ihrest =>
    intro hok hhi Δ R hR Q hprem hQ x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨ca, hfr, hC, hca, hgr⟩ :=
        hprem (cv, nF) crest (hQ _ List.mem_cons_self) hcrest ⟨ty, sv, hty, hsort⟩
      obtain ⟨-, hnl, xs, hop, -⟩ := posD_tele_open htele
      have hcurcl := (ConLeche.Verify.openPisAtFvars_bounded nF hop hfr.2.1).1
      have := ihtele (fun _ => hok) (by omega) hfr hC hca hgr (by rw [← hhi] at hR ⊢; exact hR)
      rw [hhi] at this
      obtain ⟨hPi, hO⟩ := this
      refine ⟨nodup_of_nameNodup hnd, crest, ca, ks, nds, cur, hcrest, hfr.2.1, hca, hnl, hcurcl,
        fun i hil hne => ?_, hres, hidx, by simpa using hPi, by simpa using hO⟩
      simp only [List.any_eq_false, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
        not_and] at hu4
      cases hU : ConLeche.structUsedLater (ConLeche.closeTelescope nds hi cur) 0 i
      · rfl
      · exact absurd hU (hu4 i hil hne)
    · exact ihrest hok hhi hR Q hprem (fun y hy => hQ y (List.mem_cons_of_mem _ hy)) x hx
  | teleNil =>
    intro _ _ hfr Δa ca R _ hca _ hR
    exact ⟨⟨hR.agree, hca, hfr.1⟩, trivial⟩
  | @teleCons prog base nF j a b k nd ks nds res ts ts' ha hb iha ihb =>
    intro hcovk hhi hfr Δa ca R hC hca hgr hR
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denote_forallE_inv hca
    obtain ⟨hws, hbb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgAT, hgB⟩ := WellDenoted.hoist_piTy' (V := V) hgr.graded
    obtain ⟨⟨-, ⟨Af, hAf, hszf, hinvf⟩, -⟩, hokf⟩ :=
      iha (fun hk => hcovk ⟨k, List.mem_cons_self, hk⟩) hhi ⟨hws.1, hbb.1, hLa⟩ hC.forallE_ty hta
        hgAT hR
    have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgAT
    have hfr' := frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd
    rw [show base + j + 1 = base + (j + 1) by omega] at hCop hfr' hba
    have hR' := hR.underBoth hhi ta
    obtain ⟨hPi, hO⟩ := ihb (fun ⟨k', hk', hkf⟩ => hcovk ⟨k', List.mem_cons_of_mem _ hk', hkf⟩)
      (by omega) hfr' hCop hba hgB
      (by rw [show base + (j + 1) = base + j + 1 by omega]; exact hR')
    rw [show base + (j + 1) + nF = base + j + (nF + 1) by omega,
      show base + (j + 1) = base + j + 1 by omega] at hPi
    rw [show base + (j + 1) = base + j + 1 by omega] at hO
    exact ⟨⟨⟨Af, hAf, hszf, hinvf⟩, hPi⟩, hokf, hO⟩
  | seed => trivial

/-! ## The member constructor -/

/-- **A derived member constructor is accessible** (its telescope's
derivation, at no frames): every field's reading accessible under the
earlier ones along the accessibility hole relation, each bound reading only its field's output's non-hole positions,
the result's indices hole-free — coverage needed only when some field's
kind is not flat. -/
theorem memberCtorD_acc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} {ctx : NestCtx} {F nF : Nat}
    {crest cur : Expr} {ks : List NestFieldKind} {nds : List Expr}
    {ts : List PosTree}
    (htele : PosD (fueledOps .verified F) env ctx (.tele [] (ctx.hiAt 0) nF 0 crest ks nds cur) ts)
    (hhead : ConLeche.nestResHead cur = true)
    (hok : cur.getAppArgs.all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0)) = true)
    (hcov : (∃ k ∈ ks, k.flat = false) → ContOk mp φ w ctx) (hfr : Frame (ctx.hiAt 0) crest)
    {Δa : List Term} {ca : Term} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest)
    (hca : denote mp.base2.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : GradedTy V Δa ca)
    (hR : HoleRelA mp.base2 φ w ctx [] (ctx.hiAt 0) Δa R) :
    PiAccThen w ctx [] ResultIdxConst nF (ctx.hiAt 0) nds R ca :=
  PiAccThen.mono (fun _ _ h => resultIdxConst_of_resultAt (by simp) hhead hok h) nF _ _ R ca
    (posD_acc mp hin htele hcov (by simp) hfr hC hca hgr hR).1

end ConLeche.Model
