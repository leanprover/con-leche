module

public import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Tiers
import ConLeche.Verify.InferLeaves
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Semantics.Frame
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Verify.Leaves
import ConLeche.Verify.Cached.Erase

public section

/-!
# Every node of a positivity derivation is read in its stack context

The node-semantics induction: a third sibling of `posD_mono`/`posD_acc`,
with no hole relation.  From the member constructor's own reading (its type,
framed, in the block's hole context `Δ0`, read and graded),
every node `t` of the derivation's forest has its key's parameters READ at
the depth of the frames it is derived under (`t.anc`), in the STACK CONTEXT
of those frames (`stackCtx`: each frame hole typed by its container's former
at the key's levels, over `Δ0`), with bounded leaves (`NodeSemAt`).

The cases follow `posD_mono`: the whnf step by `red_sound`; a container
instance's key read off the reduct's spine (`contNew`/`contHit`); a
seed's key read off its frame's typing (K.52, `acceptedReads_of`), in the
context by its leaves (the caller's premise); a frame's constructors read at the frame's
depth in the stack context grown by the frame's holes (`crest_frame`,
`crest_read`, the constructor's typing).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey NestHole NestState
  NestFieldKind CheckError instPisWith fueledOps PosD PosJ ProgScoped grpNews grpSub
  groupCtors PosTree)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The stack context -/

/-- **A frame hole's type**: its container's former at the key's levels
(`nestInstType`'s second component). -/
@[expose] def nestHoleTy (ctx : NestCtx) (h : NestHole) : Expr :=
  match ctx.find? h.key.cname with
  | some (.indInfo cv _) => cv.type.instantiateLevelParams cv.levelParams h.key.lvls
  | _ => .sort .zero

/-- **The stack context** of the frames `prog` (innermost first) over the
block's hole context `Δ0`: each frame hole's type, read. -/
@[expose] noncomputable def stackCtx (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (prog : List NestHole) (Δ0 : List AnnotTerm) : List AnnotTerm :=
  prog.map (fun h => (denoteMeta m.acval env φ 0 (nestHoleTy ctx h)).getD .prf) ++ Δ0

section Stack

variable {m : EnvModel V env} {φ : Name → Nat} {ctx : NestCtx} {Δ0 : List AnnotTerm}

theorem stackCtx_length (prog : List NestHole) :
    (stackCtx m φ ctx prog Δ0).length = prog.length + Δ0.length := by
  simp [stackCtx]

theorem stackCtx_nil : stackCtx m φ ctx [] Δ0 = Δ0 := rfl

theorem stackCtx_drop (prog : List NestHole) : (stackCtx m φ ctx prog Δ0).drop prog.length = Δ0 := by
  unfold stackCtx
  rw [List.drop_append_of_le_length (by simp)]
  simp

/-- The stack context at the block's own frames' depth. -/
theorem stackCtx_length_hi (hΔ0 : Δ0.length = ctx.hiAt 0) (prog : List NestHole) :
    (stackCtx m φ ctx prog Δ0).length = ctx.hiAt prog.length := by
  rw [stackCtx_length, hΔ0]; simp only [ConLeche.NestCtx.hiAt]; omega

/-- **A frame's holes on top of the stack**: the frame's new entries' types
are the group's hole types (`grpTys`). -/
theorem stackCtx_frame (hfind : ∀ n, ctx.find? n = env.find? n) {D : LfpDatum V}
    {us : List Level} {grp : List (Name × Expr)} (hgT : GrpTy env D us grp) (ds : List Expr)
    (hi : Nat) (prog : List NestHole) :
    stackCtx m φ ctx ((grpNews us ds hi grp).reverse ++ prog) Δ0
      = (grpTys m φ grp).reverse ++ stackCtx m φ ctx prog Δ0 := by
  unfold stackCtx grpTys grpNews
  rw [List.map_append, List.append_assoc, List.map_reverse, List.map_map]
  congr 2
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨mm, -, hpm, cv, caps, hf, hp2⟩ := hgT.2 p hp
  simp only [Function.comp_apply, nestHoleTy]
  rw [hfind, ← hpm] at *
  rw [hf, hp2]

end Stack

/-! ## What a node's reading is -/

/-- **A node read in its stack context**: its key's parameters read at the
depth of the frames it is derived under, in their stack context over
`Δ0`, with bounded leaves. -/
@[expose] def NodeSemAt (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (Δ0 : List AnnotTerm) (t : PosTree) : Prop :=
  (∃ dsa, DenoteMetaSpine m.acval env φ (ctx.hiAt t.anc.length) t.key.ds dsa) ∧
  (∀ x ∈ t.key.ds, CtxOkP m φ (ctx.hiAt t.anc.length) (stackCtx m φ ctx t.anc Δ0) x) ∧
  (∀ x ∈ t.key.ds, Expr.LeavesBounded x)

/-- Every node of a forest read in its stack context. -/
@[expose] def NodesSem (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx)
    (Δ0 : List AnnotTerm) (ts : List PosTree) : Prop :=
  ∀ t ∈ PosTree.forest ts, NodeSemAt m φ ctx Δ0 t

namespace NodesSem

variable {m : EnvModel V env} {φ : Name → Nat} {ctx : NestCtx} {Δ0 : List AnnotTerm}

theorem nil : NodesSem m φ ctx Δ0 [] := fun _ ht => nomatch ht

theorem append {ts ts' : List PosTree} (h : NodesSem m φ ctx Δ0 ts)
    (h' : NodesSem m φ ctx Δ0 ts') : NodesSem m φ ctx Δ0 (ts ++ ts') := fun t ht => by
  rcases PosTree.mem_forest_append.mp ht with ht | ht
  · exact h t ht
  · exact h' t ht

theorem cons_node {occ anc : List NestHole} {key : NestKey} {grp : List (Name × Expr)}
    {kids ts : List PosTree} (h0 : NodeSemAt m φ ctx Δ0 (.node occ anc key grp kids))
    (hk : NodesSem m φ ctx Δ0 kids) (h' : NodesSem m φ ctx Δ0 ts) :
    NodesSem m φ ctx Δ0 (.node occ anc key grp kids :: ts) := fun t ht => by
  rcases PosTree.mem_forest_cons.mp ht with ht | ht
  · rcases PosTree.mem_nodes.mp ht with rfl | ht
    · exact h0
    · exact hk t ht
  · exact h' t ht

end NodesSem

/-! ## The motive -/

section Motive

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (ctx : NestCtx)
  (F : Nat) (Δ0 : List AnnotTerm)

/-- **A frame's nodes**, read from the key's reading (`FrameMono`'s
premises without the hole relation). -/
@[expose] def FrameNodes (prog : List NestHole) (us : List Level) (ds : List Expr)
    (grp : List (Name × Expr)) (ts : List PosTree) : Prop :=
  ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks → ∀ {mm : Nat}, mm < D.k →
    D.member mm = (grp.headD default).1 →
  ∀ {lps : List Name},
    (∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = lps) →
    us.length = lps.length →
    (∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true) →
    ∀ {dsa : List AnnotTerm}, DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt prog.length) ds dsa →
    (D.params (Level.substFn φ lps us)).length = ds.length →
    ((∃ nP' L, ConLeche.nestContainer ctx (D.member mm) = some (nP', L) ∧ L ≠ []) ∨ lps.Nodup) →
    (∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt prog.length) (stackCtx mp.base2 φ ctx prog Δ0) x) →
    (∀ x ∈ ds, Expr.LeavesBounded x) →
    NodesSem mp.base2 φ ctx Δ0 ts

/-- **What a derivation proves of its nodes** (see the module docstring). -/
@[expose] def NodeJ : PosJ → List PosTree → Prop
  | .field prog dep _ e _ _, ts =>
    ctx.hiAt prog.length ≤ dep → Frame dep e →
    ∀ {Δa : List AnnotTerm} {ea : AnnotTerm},
      CtxOkP mp.base2 φ dep Δa e → denoteMeta mp.base2.acval env φ dep e = some ea →
      Graded V Δa ea → Δa.drop (dep - ctx.hiAt prog.length) = stackCtx mp.base2 φ ctx prog Δ0 →
      NodesSem mp.base2 φ ctx Δ0 ts
  | .tele prog base _ j cur _ _ _, ts =>
    ctx.hiAt prog.length ≤ base + j → Frame (base + j) cur →
    ∀ {Δa : List AnnotTerm} {ca : AnnotTerm},
      CtxOkP mp.base2 φ (base + j) Δa cur →
      denoteMeta mp.base2.acval env φ (base + j) cur = some ca → Graded V Δa ca →
      Δa.drop (base + j - ctx.hiAt prog.length) = stackCtx mp.base2 φ ctx prog Δ0 →
      NodesSem mp.base2 φ ctx Δ0 ts
  | .ctors prog hi us ds sub cs, ts =>
    ctx.hiAt prog.length = hi →
    ∀ (Q : ConstantVal × Nat → Prop),
    (∀ (x : ConstantVal × Nat) (crest : Expr), Q x →
      instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
        = some crest →
      (∃ ty, ConLeche.inferTypeCore .verified env F hi crest = .ok ty) →
      ∃ ca, Frame hi crest ∧ CtxOkP mp.base2 φ hi (stackCtx mp.base2 φ ctx prog Δ0) crest ∧
        denoteMeta mp.base2.acval env φ hi crest = some ca ∧
        Graded V (stackCtx mp.base2 φ ctx prog Δ0) ca) →
    (∀ x ∈ cs, Q x) → NodesSem mp.base2 φ ctx Δ0 ts
  | .frame prog us ds grp, ts => FrameNodes mp φ ctx Δ0 prog us ds grp ts
  | .seed key, ts =>
    (∀ x ∈ key.ds, CtxOkP mp.base2 φ (ctx.hiAt 0) Δ0 x ∧ Expr.LeavesBounded x) →
    NodesSem mp.base2 φ ctx Δ0 ts

end Motive

variable {φ : Name → Nat}

/-! ## Pieces -/

/-- **The whnf step, relation-free**: the reduct is framed, in the
context, read and graded. -/
theorem whnf_facts {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env}
    (hin : RulesInputs V mp.base2 φ) {F dep : Nat} {e w : Expr}
    (hw : (fueledOps .verified F).whnf env dep e = .ok w) (hfr : Frame dep e)
    {Δa : List AnnotTerm} {ea : AnnotTerm}
    (hC : CtxOkP mp.base2 φ dep Δa e) (hea : denoteMeta mp.base2.acval env φ dep e = some ea)
    (hgr : Graded V Δa ea) :
    Frame dep w ∧ CtxOkP mp.base2 φ dep Δa w ∧
      ∃ wa, denoteMeta mp.base2.acval env φ dep w = some wa ∧ Graded V Δa wa := by
  have hw' : ConLeche.whnf .verified env F dep e = .ok w := hw
  obtain ⟨hfrw, hsub, wa, hwa, hgw, -⟩ :=
    red_sound hin (ConLeche.Rules.whnf_bridge hw') hfr hC.toCtxOk hea hgr
  exact ⟨hfrw, hC.of_subset hsub, wa, hwa, hgw⟩

/-- The context seen at a shallower frame stack. -/
theorem drop_stack {m : EnvModel V env} {ctx : NestCtx} {Δ0 : List AnnotTerm}
    {prog : List NestHole} {dep : Nat} {Δa : List AnnotTerm}
    (hle : ctx.hiAt prog.length ≤ dep)
    (hΔ : Δa.drop (dep - ctx.hiAt prog.length) = stackCtx m φ ctx prog Δ0) :
    Δa.drop (dep - ctx.hiAt 0) = Δ0 := by
  have h1 : dep - ctx.hiAt 0 = (dep - ctx.hiAt prog.length) + prog.length := by
    simp only [ConLeche.NestCtx.hiAt] at hle ⊢; omega
  rw [h1, ← List.drop_drop, hΔ, stackCtx_drop]

/-- **A container key's frame premises** at a covered container: its
recorded block, its level parameters and parameter count. -/
theorem key_block {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx}
    (hcov : ContCover mp ctx) {n : Name} {nPc : Nat} {L : List (ConstantVal × Nat)}
    (hq : ConLeche.nestContainer ctx n = some (nPc, L)) (hnm : ctx.names.contains n = false)
    (hquot : n ≠ ConLeche.quotName) :
    ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = n ∧ ∃ cv caps lps,
      env.find? n = some (.indInfo cv caps) ∧
      (∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
        cv.levelParams = lps) ∧
      (∀ ψ, (D.params ψ).length = nPc) ∧ cv.levelParams = lps ∧
      ((∃ nP' L', ConLeche.nestContainer ctx (D.member mm) = some (nP', L') ∧ L' ≠ []) ∨
        lps.Nodup) := by
  obtain ⟨cv, caps, hfc⟩ := nestContainer_find hq
  rw [hcov.find] at hfc
  obtain ⟨D, hD, mm, hmm, hn⟩ := hcov.cover n cv caps hfc hnm hquot
  subst hn
  obtain ⟨lps, hlps, hlenP0, hcvl, hnL0⟩ := contBlock_facts mp hcov hD hmm hfc hq
  exact ⟨D, hD, mm, hmm, rfl, cv, caps, lps, hfc, hlps, hlenP0, hcvl,
    hnL0.imp (fun ⟨L', hL', hne⟩ => ⟨_, L', hL', hne⟩) id⟩


/-! ## The frame -/

/-- **A frame's nodes from its derivation**: the group well formed, the
level parameters distinct, every walked constructor read in the stack
context grown by the frame's holes. -/
theorem frame_nodes {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} (hcov : ContCover mp ctx) {F : Nat}
    {Δ0 : List AnnotTerm} (hΔ0 : Δ0.length = ctx.hiAt 0) {prog : List NestHole}
    {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {ctors : List (ConstantVal × Nat)} (hne : grp ≠ []) (hnd : (grp.map (·.1)).Nodup)
    (hinst : ∀ p ∈ grp, ∃ nI, ConLeche.nestInstType (m := CheckM) ctx (ctx.hiAt prog.length)
      ⟨p.1, us, ds⟩ = .ok (nI, p.2))
    (hblk : ∀ p ∈ grp.tail, (ConLeche.nestBlockOf ctx (grp.headD default).1).contains p.1 = true)
    (hctors : groupCtors ctx ds.length (grp.map (·.1)) = some ctors)
    {ts : List PosTree}
    (hwalkD : PosD (fueledOps .verified F) env ctx
      (.ctors ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
        (ctx.hiAt prog.length + grp.length) us ds (grpSub us (ctx.hiAt prog.length) grp) ctors) ts)
    (ih : NodeJ mp φ ctx F Δ0
      (.ctors ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
        (ctx.hiAt prog.length + grp.length) us ds (grpSub us (ctx.hiAt prog.length) grp) ctors) ts) :
    FrameNodes mp φ ctx Δ0 prog us ds grp ts := by
  intro D hD mm hmm hhead lps hlps hul hds dsa hdsa hlenP hnL hCds hLds
  have hblkD := hcov.block D hD
  have hkN := lfp_namesLen mp hD
  obtain ⟨p₀, ps₀, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.headD_cons] at hhead hblk
  -- the group is well formed
  have hg : GrpOk ctx D (ctx.hiAt prog.length) us ds (p₀ :: ps₀) := by
    refine ⟨hne, hnd, fun p hp => ⟨?_, hinst p hp⟩⟩
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨mm, hmm, hhead.symm⟩
    · have hin' := hblk p (by simpa using hp')
      obtain ⟨cv₀, caps₀, hf₀, -⟩ := hlps mm hmm
      have hblkOf : ConLeche.nestBlockOf ctx p.1 = D.names ∨ True := Or.inr trivial
      clear hblkOf
      have hblkOf : ConLeche.nestBlockOf ctx p₀.1 = D.names := by
        unfold ConLeche.nestBlockOf
        rw [← hhead, hcov.find, hf₀]
        exact hblkD.all mm hmm cv₀ caps₀ hf₀
      rw [hblkOf, List.contains_iff_mem] at hin'
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hin'
      refine ⟨i, by omega, ?_⟩
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hpi]
  have hndl : lps.Nodup := frame_lps_nodup mp hcov hD hmm hlps (by rw [hhead]; simp) hctors
    (posD_ctors_nodup hwalkD) hnL
  have hgT := grpWf_ty mp hD hblkD.nodup hkN hcov.find hlps hndl hul hds hdsa hlenP hg.2
  have hΔ : (stackCtx mp.base2 φ ctx prog Δ0).length = ctx.hiAt prog.length :=
    stackCtx_length_hi hΔ0 prog
  refine ih (by simp [grpNews, ConLeche.NestCtx.hiAt]; omega)
    (fun x => ∃ c j, InGrp D (p₀ :: ps₀) c ∧ j < D.nctors c ∧
      env.find? (D.ctorName c j) = some (.ctorInfo x.1 ds.length x.2))
    (fun x crest hQx hcr hinf => ?_) ?_
  · obtain ⟨c, j, ⟨hc, -⟩, hj, hfc⟩ := hQx
    have hwf := mp.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfc)
    have hcl : (x.1.type.instantiateLevelParams x.1.levelParams us).hasFvar = false := by
      rw [Expr.hasFvar_instantiateLevelParams]; exact hwf.1
    have hbb : (x.1.type.instantiateLevelParams x.1.levelParams us).looseBVarsBounded 0 = true := by
      rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hwf.2.2.2.1
    obtain ⟨hfr, hC⟩ := crest_frame mp hD hblkD.nodup hkN hcov.find hlps hndl hul hds hdsa hlenP
      hg.2 hΔ hCds hLds hcl hbb hcr
    obtain ⟨-, crest', ab, hcr', -, -, hrd⟩ :=
      crest_read mp hD hblkD.nodup hkN hcov.find hlps hndl hul hds hdsa hlenP hg.2 hc hj hfc
    rw [hcr] at hcr'
    obtain rfl := Option.some.inj hcr'
    obtain ⟨ty, hty⟩ := hinf
    have hIS : InferSemFull mp.base2 φ (ctx.hiAt prog.length + (p₀ :: ps₀).length) crest ty :=
      infer_sound hin (ConLeche.Rules.inferTypeCore_bridge hty)
    obtain ⟨-, -, -, -, hgr, -⟩ := hIS hfr hC.toCtxOk hrd
    rw [stackCtx_frame hcov.find hgT]
    exact ⟨_, hfr, hC, hrd, hgr⟩
  · -- every walked constructor is one of the group's constructors
    intro x hx
    obtain ⟨hctorsIn, -⟩ := ConLeche.groupCtors_spec hctors
    obtain ⟨cn, hcn, nP', L, hL, hnP, hxL⟩ := hctorsIn x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcn
    obtain ⟨⟨c, hc, hpc⟩, -⟩ := hg.2.2 p hp
    obtain ⟨nP'', L', hL', hlen', hfL⟩ := hblkD.ctors c hc
    rw [hpc, hL'] at hL
    obtain ⟨rfl, rfl⟩ : nP'' = nP' ∧ L' = L := by simpa using hL
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hxL
    have hnP' : nP'' = ds.length := by
      rcases hnP with h' | h'
      · exact h'
      · rw [h'] at hj; exact absurd hj (Nat.not_lt_zero _)
    refine ⟨c, j, ⟨hc, ?_⟩, by rw [← hlen']; exact hj, by rw [← hnP']; exact hfL j hj⟩
    rw [List.contains_iff_mem, List.mem_map]
    exact ⟨p, hp, hpc⟩

/-- **A derived frame's nodes, from the key's reading alone**: the frame's
head is a covered container (its recorded block, levels and parameter
count read off the derivation's own checks). -/
theorem frameNodes_of {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx}
    (hcov : ContCover mp ctx) {F : Nat} {Δ0 : List AnnotTerm} {prog : List NestHole}
    {us : List Level} {ds : List Expr} {grp : List (Name × Expr)} {ts : List PosTree}
    (hfrD : PosD (fueledOps .verified F) env ctx (.frame prog us ds grp) ts)
    (ihf : FrameNodes mp φ ctx Δ0 prog us ds grp ts)
    (hds : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt prog.length) x ∧ x.looseBVarsBounded 0 = true)
    {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt prog.length) ds dsa)
    (hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt prog.length) (stackCtx mp.base2 φ ctx prog Δ0) x)
    (hLds : ∀ x ∈ ds, Expr.LeavesBounded x) : NodesSem mp.base2 φ ctx Δ0 ts := by
  obtain ⟨hne, ⟨hnm, hquot⟩, ⟨L, hq⟩, hinst, -⟩ := posD_frame_inv hfrD
  obtain ⟨D, hD, mm, hmm, hmn, cv, caps, lps, hfc, hlps, hlenP0, hcvl, hnL⟩ :=
    key_block mp hcov hq hnm hquot
  obtain ⟨p₀, ps₀, rfl⟩ := List.exists_cons_of_ne_nil hne
  simp only [List.headD_cons] at hmn hfc
  obtain ⟨nI, hnI⟩ := hinst p₀ List.mem_cons_self
  obtain ⟨cvC, capsC, hfC, hul⟩ := ConLeche.nestInstType_lvls hnI
  rw [hcov.find, hfc] at hfC
  obtain ⟨rfl, rfl⟩ : cv = cvC ∧ caps = capsC := by simpa using hfC
  rw [hcvl] at hul
  exact ihf hD hmm (by rw [hmn]; rfl) hlps hul hds hdsa (hlenP0 _)
    hnL hCds hLds

/-! ## THE INDUCTION -/

/-- **EVERY NODE OF A DERIVATION IS READ IN ITS STACK CONTEXT** (the
node-semantics induction; see the module docstring). -/
theorem posD_nodeSem {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} (hcov : ContCover mp ctx) {F : Nat}
    {Δ0 : List AnnotTerm} (hΔ0 : Δ0.length = ctx.hiAt 0) :
    ∀ {j : PosJ} {ts : List PosTree}, PosD (fueledOps .verified F) env ctx j ts →
      NodeJ mp φ ctx F Δ0 j ts := by
  intro j ts h
  induction h with
  | const => intro _ _ _ _ _ _ _ _; exact NodesSem.nil
  | @pi prog dep kb e a b bm k nb ts hw hocc ha hb ihb =>
    intro hhi hfr Δa ea hC hea hgr hΔ
    obtain ⟨hfrw, hCw, wa, hwa, hgw⟩ := whnf_facts hin hw hfr hC hea hgr
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
    obtain ⟨hws, hbb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
    refine ihb (by omega) (frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd) hCop hba hgB ?_
    rw [show dep + 1 - ctx.hiAt prog.length = (dep - ctx.hiAt prog.length) + 1 by omega,
      List.drop_succ_cons, hΔ]
  | hole => intro _ _ _ _ _ _ _ _; exact NodesSem.nil
  | frameHole => intro _ _ _ _ _ _ _ _; exact NodesSem.nil
  | @contNew prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds hdsw0
      hnI hhead hsc hfrD ihf =>
    intro hhid hfr Δa ea hC hea hgr hΔ
    obtain ⟨hfrw, hCw, wa, hwa, -⟩ := whnf_facts hin hw hfr hC hea hgr
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    generalize hargs : w.getAppArgs = args at hspine hlen hidx hds hdsw0 hnI hfrD ihf
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
    obtain ⟨fa, vs, -, hsp, -⟩ := denoteMeta_mkAppN_inv hwa
    obtain ⟨vs₁, vs₂, -, hsp₁, -⟩ := DenoteMetaSpine.split _ hsp
    obtain ⟨dsa, hdsa, -⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hhid
      (fun x hx => (hdsw x hx).1) hsp₁
    have hCds : ∀ x ∈ args.take nPc, CtxOkP mp.base2 φ (ctx.hiAt prog.length)
        (stackCtx mp.base2 φ ctx prog Δ0) x := fun x hx => by
      rw [← hΔ]
      exact hCw.drop hhid fun l hl => ⟨leaves_mkAppN_arg (List.mem_append_left _ hx) hl,
        ConLeche.Expr.fvarLeaves_lt_of_wscoped (hdsw x hx).1 l hl⟩
    exact NodesSem.cons_node ⟨⟨dsa, hdsa⟩, hCds, hLds⟩
      (frameNodes_of mp hcov hfrD ihf hdsw hdsa hCds hLds) NodesSem.nil
  | @contHit prog dep kb e w n us L nPc nI cty grp ts hw hocc hfn hnm hq hlen hquot hidx hds
      hdsw0 hnI hmem hfrD ihf =>
    intro hhid hfr Δa ea hC hea hgr hΔ
    obtain ⟨hfrw, hCw, wa, hwa, -⟩ := whnf_facts hin hw hfr hC hea hgr
    have hspine := Expr.mkAppN_getApp w
    rw [hfn] at hspine
    generalize hargs : w.getAppArgs = args at hspine hlen hidx hds hdsw0 hnI hmem hfrD ihf
    subst hspine
    rw [← List.take_append_drop nPc args] at hwa hCw
    have hdl : (args.take nPc).length = nPc := by rw [List.length_take]; omega
    have hle0 : ctx.hiAt 0 ≤ ctx.hiAt prog.length := by simp only [ConLeche.NestCtx.hiAt]; omega
    have hdsw : ∀ x ∈ args.take nPc, Expr.WScoped (ctx.hiAt ([] : List NestHole).length) x ∧
        x.looseBVarsBounded 0 = true := fun x hx =>
      ⟨hdsw0 x hx, ConLeche.Expr.bvarB_le (Nat.le_of_eq (hds x hx).1)⟩
    have hLds : ∀ x ∈ args.take nPc, Expr.LeavesBounded x := fun x hx l hl =>
      hfrw.2.2 l (leaves_mkAppN_arg (List.mem_of_mem_take hx) hl)
    obtain ⟨fa, vs, -, hsp, -⟩ := denoteMeta_mkAppN_inv hwa
    obtain ⟨vs₁, vs₂, -, hsp₁, -⟩ := DenoteMetaSpine.split _ hsp
    obtain ⟨dsa, hdsa, -⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ)
      (show ctx.hiAt ([] : List NestHole).length ≤ dep by simp only [List.length_nil]; omega)
      (fun x hx => (hdsw x hx).1) hsp₁
    have hΔ0' := drop_stack hhid hΔ
    have hCds : ∀ x ∈ args.take nPc, CtxOkP mp.base2 φ (ctx.hiAt ([] : List NestHole).length)
        (stackCtx mp.base2 φ ctx [] Δ0) x := fun x hx => by
      rw [stackCtx_nil, ← hΔ0']
      exact hCw.drop (by simp only [List.length_nil]; omega) fun l hl =>
        ⟨leaves_mkAppN_arg (List.mem_append_left _ hx) hl,
          ConLeche.Expr.fvarLeaves_lt_of_wscoped (hdsw x hx).1 l hl⟩
    exact NodesSem.cons_node ⟨⟨dsa, hdsa⟩, hCds, hLds⟩
      (frameNodes_of mp hcov hfrD ihf hdsw hdsa hCds hLds) NodesSem.nil
  | @frame prog us ds grp ctors ts hne hhd hhdC hnd hinst hblk _ hctors _ hwalk ih =>
    exact frame_nodes mp hin hcov hΔ0 hne hnd hinst hblk hctors hwalk ih
  | ctorsNil => intro _ _ _ _; exact NodesSem.nil
  | @ctorsCons prog hi us ds sub cv nF cs crest ty sv ks nds cur ts ts' hnd hcrest hty hsort htele
      hu4 hres hidx hrest ihtele ihrest =>
    intro hhi Q hprem hQ
    obtain ⟨ca, hfr, hC, hca, hgr⟩ :=
      hprem (cv, nF) crest (hQ _ List.mem_cons_self) hcrest ⟨ty, hty⟩
    refine NodesSem.append ?_ (ihrest hhi Q hprem fun y hy => hQ y (List.mem_cons_of_mem _ hy))
    subst hhi
    exact ihtele (by omega) hfr hC hca hgr (by simp)
  | teleNil => intro _ _ _ _ _ _ _ _; exact NodesSem.nil
  | @teleCons prog base nF j a b bm k nd ks nds res ts ts' ha hb iha ihb =>
    intro hhi hfr Δa ca hC hca hgr hΔ
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
    obtain ⟨hws, hbb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
    have hA := iha hhi ⟨hws.1, hbb.1, hLa⟩ hC.forallE_ty hta hgA hΔ
    have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
    have hfr' := frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd
    rw [show base + j + 1 = base + (j + 1) by omega] at hCop hfr' hba
    have hrest := ihb (by omega) hfr' hCop hba hgB (by
      rw [show base + (j + 1) - ctx.hiAt prog.length = (base + j - ctx.hiAt prog.length) + 1 by
        omega, List.drop_succ_cons, hΔ])
    exact hA.append hrest
  | @seed n us ds L grp ts hnm hquot hC hds hdsw hleaf hmem hfr ihf =>
    intro hpre
    have hdsw' : ∀ x ∈ ds, Expr.WScoped (ctx.hiAt ([] : List NestHole).length) x ∧
        x.looseBVarsBounded 0 = true :=
      fun x hx => ⟨hdsw x hx, ConLeche.Expr.bvarB_le (Nat.le_of_eq (hds x hx).1)⟩
    have hLds : ∀ x ∈ ds, Expr.LeavesBounded x := fun x hx => (hpre x hx).2
    have hCds : ∀ x ∈ ds, CtxOkP mp.base2 φ (ctx.hiAt ([] : List NestHole).length)
        (stackCtx mp.base2 φ ctx [] Δ0) x := fun x hx => by
      rw [stackCtx_nil]; exact (hpre x hx).1
    -- the key's parameters are read: its instance is typed at the root (K.52)
    obtain ⟨ty, hty⟩ : ∃ ty, (fueledOps .verified F).inferType env (ctx.hiAt 0)
        (Expr.mkAppN (.const (grp.headD default).1 us) ds) = .ok ty := by
      cases hfr with
      | frame _ _ _ _ _ _ _ _ hkty _ => exact hkty
    obtain ⟨ea, hea⟩ := acceptedReads_of mp.base2 φ (F := F) hty
      (Expr.WScoped.mkAppN (by simp [Expr.WScoped]) fun x hx => hdsw x hx)
      (ConLeche.looseBVarsBounded_mkAppN (by simp [Expr.looseBVarsBounded])
        fun x hx => (hdsw' x hx).2)
      (fun l hl => by
        rcases ConLeche.fvarLeaves_mkAppN hl with hl | ⟨x, hx, hl⟩
        · simp [Expr.fvarLeaves] at hl
        · exact hLds x hx l hl)
    obtain ⟨-, dsa, -, hdsa, -⟩ := denoteMeta_mkAppN_inv hea
    exact NodesSem.cons_node ⟨⟨dsa, hdsa⟩, hCds, hLds⟩
      (frameNodes_of mp hcov hfr ihf hdsw' hdsa hCds hLds) NodesSem.nil

end ConLeche.Model
