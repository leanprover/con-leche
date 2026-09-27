module

public import ConLeche.Model.Inductives.UseAccK
public import ConLeche.Model.Inductives.UseBridgeK
public import ConLeche.Verify.Inductives.PosShapeK
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Inductives.ContAccRel
import ConLeche.Model.Inductives.NestPosOut
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Rules.InferSoundKit
import ConLeche.Model.Inductives.SumKit
import ConLeche.Verify.Cached.Erase
import ConLeche.Semantics.Frame
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.EnvWF

public section

/-!
# The key-named positivity derivation is accessible (PRIMREC / NESTKN-M4)

The closure witness (W) for the key-named positivity check: every judgment of
its derivation (`PosDKH`) reads ACCESSIBLY in the holes, at a positive level,
by ONE induction on the derivation (`posDK_acc`) — the twin of `posDK_mono`
(`PosMonoK.lean`) and the successor of `posD_acc` (`PosDerivAcc.lean`).  The
motive `AccJK`:

* `field`/`tele` — along every accessibility hole relation at the judgment's
  layout (`HoleRelAK`), the type regime and accessibility with a bound reading
  only the non-hole positions the output mentions (`AccConclG`,
  `PiAccThenG`), and the output's facts (`OutOkG`, `OutTeleG`): the whnf step,
  a hole-free reading, a Π, a member hole, a MET family (bound `{pt}`, rich at
  its index count), an own hole (blind in `DsF`), a container instance by its
  use (`accConclK_of_carrier`);
* `ctors`/`node` — the node's walk and its frame fact (`CtorsAccK`,
  `FrameAccJK`, `posDK_node_acc`: `frameIterAccG` over the frame relation, a
  hole relation at the node's layout by `frameRelAK_holeRelAK`);
* `use` — the used container's carrier accessible at the user's key frames
  (`UseAccConclK`, from `useAccK`: the node's frame fact along the image of
  the user's relation, its supports composed with the MET bindings');
* `bind` — a met family's binding accessible and rich at its index count
  (`ValAcc`, `ValRich`): a family of the user, the user's own hole at `DsF`
  (blind), a key used in turn (`valAcc_key`; rich vacuously, PROOFPLAN R4,
  `rich_of_keyOcc` — at `w ≠ 0` only);
* `syn` — nothing.

The use case reads the match through the relation-free core `UseCoreK`
(`UseBridgeK.lean`), which `useCoreK` proves at the hook `UseOkK`.
`memberCtorDK_acc` is `memberCtorD_acc`'s conclusion — the form
`blockCtorAcc_of_walk` (`BlockAccRunCont.lean`) reads — so the switch swaps
only the producer.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey LayoutK LayoutOutK
  instPisWith fueledOps PosDKH PosJK PosKind UseHookK groupCtors grpSub matchStepK thetaK
  ParamOkK)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The motive -/

section Motive

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (w : Nat)
  (ctx : NestCtx)

/-- What a node's walk leaves of one (constructor, crest), for accessibility:
the crest bvar-closed and read, its telescope's shape and U4, its result
headed by a hole with hole-free indices, its fields accessible along the
relation and their outputs read like the inputs. -/
@[expose] def CtorWalkedAK (m : EnvModel V env) (L : LayoutK) (met : List Nat)
    (Δ : List AnnotTerm) (R : FrameRel V) (x : (ConstantVal × Nat) × Expr) : Prop :=
  x.2.looseBVarsBounded 0 = true ∧ ∃ ca, ∃ ks : List PosKind, ∃ nds cur,
    denoteMeta m.acval env φ L.hi x.2 = some ca ∧ nds.length = x.1.2 ∧
    cur.looseBVarsBounded 0 = true ∧
    (∀ i, i < x.1.2 → ks.getD i .ordinary ≠ .ordinary →
      ConLeche.structUsedLater (ConLeche.closeTelescope nds L.hi cur) 0 i = false) ∧
    ConLeche.nestResHead cur = true ∧
    (cur.getAppArgs.drop L.dsF.length).all (fun a => !a.nestOcc ctx.names ctx.nP L.hi) = true ∧
    PiAccThenG w ctx.nP L.hi (HoleQK ctx L met) (ResultAt m φ ctx.nP L.hi (L.hi + x.1.2) cur)
      x.1.2 L.hi (nds.map (·.1)) R ca ∧
    OutTeleG m φ ctx.names ctx.nP L.hi ks (nds.map (·.1)) L.hi Δ ca

/-- What the walk of a node's crests proves (the `ctors` judgment's motive). -/
@[expose] def CtorsAccK (L : LayoutK) (met : List Nat)
    (cs : List ((ConstantVal × Nat) × Expr)) : Prop :=
  ContOk mp φ w ctx →
  ∀ {Δ : List AnnotTerm} {R : FrameRel V}, HoleRelAK mp.base2 φ ctx L met L.hi Δ R →
    LaySiteK mp.base2 φ ctx L L.hi Δ →
    (∀ x ∈ cs, ∃ ca, Frame L.hi x.2 ∧ CtxOkP mp.base2 φ L.hi Δ x.2 ∧
      denoteMeta mp.base2.acval env φ L.hi x.2 = some ca ∧ Graded V Δ ca ∧ TeleSmall w x.1.2 R ca) →
    ∀ x ∈ cs, CtorWalkedAK φ w ctx mp.base2 L met Δ R x

/-- **What a use proves** at its user (depth `d`, the user's spelling `ps`
read `psa`, along `R`): the used container is a member of a recorded block,
its parameter count the spelling's, its index count the user's N2 count, its
index telescope reading the same at related key frames, the block at the
level, and its carrier accessible at the user's key frames (the user's items,
a bound reading the user's parameters). -/
@[expose] def UseAccConclK (L : LayoutK) (met : List Nat) (kc : NestKey) (ps : List Expr) (d : Nat)
    (psa : List AnnotTerm) (R : FrameRel V) : Prop :=
  ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = kc.cname ∧ ∃ cv caps,
    env.find? kc.cname = some (.indInfo cv caps) ∧
    (D.params (Level.substFn φ cv.levelParams kc.lvls)).length = ps.length ∧
    (∃ nI cty, ConLeche.nestInstType (m := CheckM) ctx L.hi ⟨kc.cname, kc.lvls, ps⟩ = .ok (nI, cty) ∧
      (D.ids mm (Level.substFn φ cv.levelParams kc.lvls)).length = nI) ∧
    (∀ ρ ρ', R ρ ρ' → TeleEq (keyFrame psa d ρ) (keyFrame psa d ρ')
      (D.ids mm (Level.substFn φ cv.levelParams kc.lvls))) ∧
    D.w (Level.substFn φ cv.levelParams kc.lvls) = w ∧
    FrameAccOutG w ctx.nP d (HoleQK ctx L met d) R D (Level.substFn φ cv.levelParams kc.lvls) psa
      (fun c => c = mm)

/-- **What a derivation proves** of its judgment's reading, for accessibility
(see the module docstring). -/
@[expose] def AccJK : PosJK → Prop
  | .field L met dep _ e k nf =>
    (k.flat = false → ContOk mp φ w ctx) → L.hi ≤ dep → Frame dep e →
    ∀ {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ dep Δa e → denoteMeta mp.base2.acval env φ dep e = some ea →
      Graded V Δa ea → HoleRelAK mp.base2 φ ctx L met dep Δa R →
      LaySiteK mp.base2 φ ctx L dep Δa →
      AccConclG w ctx.nP L.hi (HoleQK ctx L met) dep e nf R ea ∧
        OutOkG mp.base2 φ ctx.names ctx.nP L.hi dep Δa k nf ea
  | .tele L met nF j cur ks nds res =>
    ((∃ k ∈ ks, k.flat = false) → ContOk mp φ w ctx) → Frame (L.hi + j) cur →
    ∀ {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V},
      CtxOkP mp.base2 φ (L.hi + j) Δa cur →
      denoteMeta mp.base2.acval env φ (L.hi + j) cur = some ca → Graded V Δa ca →
      HoleRelAK mp.base2 φ ctx L met (L.hi + j) Δa R → LaySiteK mp.base2 φ ctx L (L.hi + j) Δa →
      TeleSmall w nF R ca →
      PiAccThenG w ctx.nP L.hi (HoleQK ctx L met)
        (ResultAt mp.base2 φ ctx.nP L.hi (L.hi + j + nF) res) nF (L.hi + j) (nds.map (·.1)) R ca ∧
      OutTeleG mp.base2 φ ctx.names ctx.nP L.hi ks (nds.map (·.1)) (L.hi + j) Δa ca
  | .ctors L met cs => CtorsAccK mp φ w ctx L met cs
  | .node kc lo met => FrameAccJK mp φ w ctx kc lo met
  | .use L met kc ps =>
    ContOk mp φ w ctx → ∀ {d : Nat}, L.hi ≤ d → ∀ {Δa : List AnnotTerm} {R : FrameRel V},
      HoleRelAK mp.base2 φ ctx L met d Δa R → LaySiteK mp.base2 φ ctx L d Δa → Δa.length = d →
      (∀ x ∈ ps, Expr.WScoped L.hi x ∧ x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
        CtxOkP mp.base2 φ d Δa x) →
      ∀ {psa : List AnnotTerm}, DenoteMetaSpine mp.base2.acval env φ d ps psa →
      ∀ {is : List Expr} {wa : AnnotTerm},
        denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const kc.cname kc.lvls) (ps ++ is))
          = some wa → Graded V Δa wa →
      UseAccConclK mp φ w ctx L met kc ps d psa R
  | .bind L met b =>
    ContOk mp φ w ctx → ∀ {d : Nat}, L.hi ≤ d → ∀ {Δa : List AnnotTerm} {R : FrameRel V},
      HoleRelAK mp.base2 φ ctx L met d Δa R → LaySiteK mp.base2 φ ctx L d Δa → Δa.length = d →
      Expr.WScoped L.hi b → b.looseBVarsBounded 0 = true → Expr.LeavesBounded b →
      CtxOkP mp.base2 φ d Δa b →
      ∀ {ba : AnnotTerm}, denoteMeta mp.base2.acval env φ d b = some ba → Graded V Δa ba →
      ∀ nI, ConLeche.BindArityK ctx L b nI →
      ∃ A : (Nat → V) → V, (∀ ρ, A ρ ∈ˢ (univ w : V)) ∧ InvOn (ParamPos d ctx.nP) A ∧
        ValAcc (HoleQK ctx L met d) R A ba nI ∧ ValRich (HoleQK ctx L met d) R ba nI
  | .syn _ _ _ => True

end Motive

variable {φ : Name → Nat}

/-! ## The whnf step -/

/-- **The whnf step** of every field rule (`acc_of_whnf`, generic). -/
theorem acc_of_whnfK {μ : ConLeche.CheckMode} {mp : EnvModelM V μ env}
    (hin : RulesInputs V mp.base2 φ) {F dep : Nat} {e wt : Expr}
    (hw : (fueledOps .verified F).whnf env dep e = .ok wt) (hfr : Frame dep e)
    {Δa : List AnnotTerm} {ea : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ dep Δa e) (hea : denoteMeta mp.base2.acval env φ dep e = some ea)
    (hgr : Graded V Δa ea) (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ')
    {w nP hb : Nat} {Qd : Nat → Nat → Nat → Prop} {names : List Name} {k : PosKind} {nf : Expr}
    (kont : Frame dep wt → CtxOkP mp.base2 φ dep Δa wt →
      (∀ l ∈ wt.fvarLeaves, l ∈ e.fvarLeaves) → ∀ wa,
      denoteMeta mp.base2.acval env φ dep wt = some wa → Graded V Δa wa →
      (∀ ρ, Sat V Δa ρ → interp V ρ ea = interp V ρ wa) →
      AccConclG w nP hb Qd dep e nf R wa ∧ OutOkG mp.base2 φ names nP hb dep Δa k nf wa) :
    AccConclG w nP hb Qd dep e nf R ea ∧ OutOkG mp.base2 φ names nP hb dep Δa k nf ea := by
  have hw' : ConLeche.whnf .verified env F dep e = .ok wt := hw
  obtain ⟨hfrw, hsub, wa, hwa, hgw, heq⟩ :=
    red_sound hin (ConLeche.Rules.whnf_bridge hw') hfr hC.toCtxOk hea hgr
  obtain ⟨⟨hTR, ⟨A, hA, hsz, hinv⟩, hout⟩, hok⟩ := kont hfrw (hC.of_subset hsub)
    (ConLeche.whnf_fvarLeaves mp.base2.wf F hw') wa hwa hgw heq
  exact ⟨⟨TypeReg.of_eqOn (P := Sat V Δa) hdom (fun ρ hρ => heq ρ hρ) hTR,
    ⟨A, AccOn.of_eqOn (P := Sat V Δa) hdom (fun ρ hρ => heq ρ hρ) hA, hsz, hinv⟩, hout⟩,
    hok.congr_read fun ρ hρ => (heq ρ hρ).symm⟩

/-! ## The node -/

set_option maxHeartbeats 1600000 in
/-- **A node's frame fact for accessibility from its walk**: the layout's spec
gives the group (well formed), its constructors and crests; the block is at
the level (N3 at the head, `n2_sort`); `frameIterAccG` along the frame
relation — a hole relation at the node's layout (`frameRelAK_holeRelAK`) —
with the walk supplied by the crests' walk. -/
theorem posDK_node_acc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} {F : Nat}
    {kc : NestKey} {lo : LayoutOutK} {met : List Nat}
    (hspec : ConLeche.LayoutSpecK (fueledOps .verified F) env ctx kc lo)
    (ih : CtorsAccK mp φ w ctx lo.L met (lo.ctors.zip lo.crests)) :
    FrameAccJK mp φ w ctx kc lo met := by
  obtain ⟨⟨nPc, Lc, hqC, hgcC⟩, hndC, hgrpL, hlvl, hgnames, hhiL, -, hinst, hcrests, -, hcty, -⟩ :=
    hspec
  intro hok hkC hkq D hD mm hmm hhead lps hlps hul hds dsa hdsa hlenP hnL Δh R₀ hR₀ hlay hΔ hCds
    hLds hfit
  have hcov := hok.1
  have hblkD := hcov.block D hD
  have hkN := lfp_namesLen mp hD
  -- the group: the key's canonical group
  have hnames : (grpOfK lo).map (·.1) = ConLeche.groupOfK ctx kc.cname := by
    rw [grpOfK_names, hgnames, hgrpL]
  have hne : grpOfK lo ≠ [] := by
    intro h; rw [h] at hnames; exact ConLeche.groupOfK_ne_nil kc.cname hnames.symm
  have hhd : ((grpOfK lo).headD default).1 = (ConLeche.groupOfK ctx kc.cname).headD kc.cname := by
    rw [← hnames]
    cases h : grpOfK lo with
    | nil => exact absurd h hne
    | cons p ps => simp
  have hhead' := hhead
  rw [hhd] at hhead
  have hndn : ((grpOfK lo).map (·.1)).Nodup := by
    rw [hnames]; exact ConLeche.groupOfK_nodup _
  have hinstG : ∀ p ∈ grpOfK lo, ∃ nI, ConLeche.nestInstType (m := CheckM) ctx
      (ctx.hiAt 0 + lo.L.nF) ⟨p.1, lo.L.lvls, lo.L.dsF⟩ = .ok (nI, p.2) := by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
    refine ⟨g.2.1, ?_⟩
    have := hinst g hg
    rw [hlvl]
    exact this
  -- the key's container is stored
  obtain ⟨cvh, capsh, hfh⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
  obtain ⟨cvk, capsk, hfk⟩ : ∃ cv caps, env.find? kc.cname = some (.indInfo cv caps) := by
    have hmemh : D.member mm ∈ ConLeche.groupOfK ctx kc.cname := by
      rw [hhead]; exact ConLeche.groupOfK_head_mem _
    rcases ConLeche.mem_groupOfK hmemh with h | h
    · exact ⟨cvh, capsh, by rw [← h]; exact hfh⟩
    · unfold ConLeche.nestBlockOf at h
      rw [hcov.find] at h
      split at h
      · rename_i cv caps hf; exact ⟨cv, caps, hf⟩
      · simp at h
  have hgin := groupOfK_in mp hcov hkC hkq hfk hD hmm
    (by rw [hhead]; exact ConLeche.groupOfK_head_mem _)
  have hg : GrpOk ctx D (ctx.hiAt 0 + lo.L.nF) lo.L.lvls lo.L.dsF (grpOfK lo) := by
    refine ⟨hne, hndn, fun p hp => ⟨?_, hinstG p hp⟩⟩
    have hpn : p.1 ∈ ConLeche.groupOfK ctx kc.cname := by
      rw [← hnames]; exact List.mem_map_of_mem hp
    obtain ⟨mm', hmm', he⟩ := hgin p.1 hpn
    exact ⟨mm', hmm', he.symm⟩
  -- the constructors, at the key's parameter count
  obtain ⟨lps', hlps', hlenP', -, -⟩ := contBlock_facts mp hcov hD hmm hfh
    (by rw [hhead]; exact hqC)
  have hnPc : nPc = lo.L.dsF.length := by rw [← hlenP' (Level.substFn φ lps lo.L.lvls), hlenP]
  have hgc : groupCtors ctx lo.L.dsF.length ((grpOfK lo).map (·.1)) = some lo.ctors := by
    rw [hnames, ← hnPc]; exact hgcC
  have hndl : lps.Nodup := frame_lps_nodup mp hcov hD hmm hlps
    (by rw [hnames, hhead]; exact ConLeche.groupOfK_head_mem _) hgc hndC hnL
  -- the block at the level (N3 at the head)
  have hwD : D.w (Level.substFn φ lps lo.L.lvls) = w := by
    obtain ⟨p₀, ps₀, hp₀⟩ := List.exists_cons_of_ne_nil hne
    have hp₀m : p₀ ∈ grpOfK lo := by rw [hp₀]; exact List.mem_cons_self
    have hhp : p₀.1 = D.member mm := by rw [hhead', hp₀]; rfl
    obtain ⟨nI₀, hnI₀⟩ := hinstG p₀ hp₀m
    obtain ⟨cvm, capsm, hfm, hlm⟩ := hlps mm hmm
    have := n2_sort mp hD hmm hcov.find (by rw [← hhp]; exact hnI₀) hfm (by rw [hlm]; exact hndl)
      (by rw [hlm]; exact hul) (by rw [hlm]; exact hlenP) hds hdsa
    rw [hlm] at this
    exact this.trans hok.2
  -- the frame relation is an accessibility hole relation at the layout
  have hlenG : lo.L.hi = ctx.hiAt 0 + lo.L.nF + (grpOfK lo).length := by
    rw [hhiL, grpOfK_length]
  have hLgrp : lo.L.grp = (grpOfK lo).map (·.1) := by rw [hnames, hgrpL]
  have hR' := frameRelAK_holeRelAK mp hD hblkD.nodup hkN hcov.find hlps hndl hul hds hdsa hlenP
    hg.2 (L := lo.L) hLgrp rfl rfl hlenG hR₀ hfit (by rw [hwD]; exact hw)
  have hagree : R₀.AgreesOff (holeP (ctx.hiAt 0 + lo.L.nF) ctx.nP (ctx.hiAt 0 + lo.L.nF)) := by
    have := hR₀.agree; simpa using this
  have hsh : ∀ d, ctx.hiAt 0 + lo.L.nF + (grpOfK lo).length ≤ d → ∀ i n,
      shiftQ (HoleQK ctx lo.L met d) i n ↔ HoleQK ctx lo.L met (d + 1) i n := by
    intro d hd i n
    refine shiftQ_holeQK ?_ i n
    rw [hLgrp, List.length_map]; exact hd
  have hacc := frameIterAccG mp hD hblkD.nodup hkN hcov.find hlps hndl hul hds hdsa hlenP hg.2 hin hw
    hwD (F := F) hblkD.ctors (by simp only [ConLeche.NestCtx.hiAt]; omega) hsh
    (holeQK_split (met := met) hLgrp rfl) hR₀.dom hagree hR₀.symm hR₀.lrefl hΔ hCds hLds hfit hgc
    (fun Q hprem hQ x hx => ?_)
  · exact ⟨hndl, hg, hwD, hacc⟩
  -- the walk: each constructor's crest, walked
  have hsub := crestsK_sub_eq lo.L.lvls (ctx.hiAt 0 + lo.L.nF) lo.ginfo
  rw [← hlvl] at hcrests
  obtain ⟨hlc, hcr⟩ := crestsK_spec hcrests
  obtain ⟨crest, hxc⟩ := mem_zip_of_mem_left hlc hx
  have hcrx := hcr _ hxc
  simp only at hcrx
  rw [hsub] at hcrx
  rw [← hlenG] at hR'
  have hlay' : LaySiteK mp.base2 φ ctx lo.L lo.L.hi
      ((grpTys mp.base2 φ (grpOfK lo)).reverse ++ Δh) := by
    have := hlay.base.weaken (Ts := (grpTys mp.base2 φ (grpOfK lo)).reverse)
      (g := (grpOfK lo).length) (by simp [grpTys])
    rwa [← hlenG] at this
  have hwalkd := ih hok hR' hlay' (fun y hy => ?_) _ hxc
  · obtain ⟨hcrb, ca, ks, nds, cur, hca, hnl, hcurcl, hU4, hres, hidx, hPi, hO⟩ := hwalkd
    refine ⟨nodup_of_nameNodup (hndC x hx), crest, ca, ks, nds, cur, hcrx, hcrb, ?_, hnl, hcurcl,
      ?_, hres, ?_, ?_, ?_⟩
    · rw [hlenG] at hca; exact hca
    · rw [hlenG] at hU4; exact hU4
    · rw [hlenG] at hidx; exact hidx
    · rw [hlenG] at hPi; exact hPi
    · rw [hlenG] at hO; exact hO
  -- every crest reads, graded and small, at the frame's context
  have hyc := hcr _ hy
  rw [hsub] at hyc
  obtain ⟨ty, sv, hty, -⟩ := hcty y.2 (List.of_mem_zip hy).2
  rw [hlenG] at hty ⊢
  exact hprem y.1 y.2 (hQ _ (List.of_mem_zip hy).1) hyc ⟨ty, hty⟩

/-! ## THE INDUCTION -/

set_option maxHeartbeats 1600000 in
/-- **THE KEY-NAMED DERIVATION IS ACCESSIBLE** (see the module docstring),
at a positive level, given the relation-free core of the uses' matches
(`UseCoreK`) at the derivation's hook. -/
theorem posDK_acc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} {F : Nat}
    {hk : UseHookK} (hbr : UseCoreK mp φ ctx (fueledOps .verified F) hk) :
    ∀ {j : PosJK}, PosDKH (fueledOps .verified F) env ctx hk j → AccJK mp φ w ctx j := by
  intro j h
  induction h with
  | @const L met dep kb e wt hw' hocc =>
    intro _ hhi hfr Δa ea R hC hea hgr hR _
    refine acc_of_whnfK hin hw' hfr hC hea hgr hR.dom fun hfrw _ hlw wa hwa _ heq => ?_
    have hco : ConstOn R wa := ConstOn.of_noBVar hR.agree
      (denoteMeta_noBVar_of_nestOcc dep wt hfrw.1 hhi hocc hwa)
    refine ⟨⟨hco.typeReg, ⟨_, hco.accOn, SizeOn.const (empty_mem_univ w), InvOn.const _ _⟩, ?_⟩, ?_⟩
    · split
      · exact (outMent_self dep wt).trans hlw
      · exact outMent_self dep e
    · split
      · exact ⟨hfrw.2.1, hfrw.1, fun _ => hocc, wa, hwa, fun _ _ => rfl⟩
      · rename_i hne
        exact ⟨hfr.2.1, hfr.1, fun _ => by simpa using hne, ea, hea, fun ρ hρ => heq ρ hρ⟩
  | @pi L met dep kb e a b bm k nb hw' hocc ha hb ihb =>
    intro hcovk hhi hfr Δa ea R hC hea hgr hR hlay
    refine acc_of_whnfK hin hw' hfr hC hea hgr hR.dom fun hfrw hCw hlw wa hwa hgw _ => ?_
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hwa
    obtain ⟨hws, hbb, hLb⟩ := hfrw
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hholes : NoBVar (holeP dep ctx.nP L.hi) ta :=
      denoteMeta_noBVar_of_nestOcc dep a hws.1 hhi ha hta
    have hA : ConstOn R ta := ConstOn.of_noBVar hR.agree hholes
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgw
    have hCop := CtxOkP.openS hCw.forallE_ty hCw.forallE_body hta hgA
    obtain ⟨⟨hTRb, ⟨Ab, hAb, hszb, hinvb⟩, houtb⟩, hokb⟩ := ihb hcovk (by omega)
      (frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd) hCop hba hgB
      (hR.underBoth hhi ta (transfer_of_constOn hA)) (hlay.under ta)
    have hout : OutMent dep e (.forallE a (nb.abstract1 dep 0) bm) := by
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
    -- at a `Prop` codomain the body is truth-valued (the grading)
    have hB0 : pwBit φ bm.pw = 0 → ∀ σ σ', R.underBoth ta σ σ' →
        interp V σ ba ∈ˢ (univZero : V) ∧ interp V σ' ba ∈ˢ (univZero : V) := by
      rintro hv0 _ _ ⟨x, ρ, ρ', rfl, rfl, hRr, hx, hx'⟩
      have hval : ∀ σ, Sat V Δa σ → x ∈ˢ interp V σ ta →
          interp V (cons x σ) ba ∈ˢ (univZero : V) := by
        intro σ hσ hxσ
        have := (hgw σ hσ).2
        rw [AnnotValid_pi] at this
        exact this.2.2 hv0 x hxσ
      exact ⟨hval ρ (hR.dom ρ ρ' hRr).1 hx, hval ρ' (hR.dom ρ ρ' hRr).2 hx'⟩
    have hokP : OutOkG mp.base2 φ ctx.names ctx.nP L.hi dep Δa k
        (.forallE a (nb.abstract1 dep 0) bm) (.pi 0 (pwBit φ bm.pw) ta ba) := by
      obtain ⟨hnbB, hnbW, hnbO, nba, hnba, hnbr⟩ := hokb
      refine ⟨?_, ?_, fun hk => ?_, .pi 0 (pwBit φ bm.pw) ta nba, ?_, fun ρ hρ => ?_⟩
      · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
        exact ⟨hbb.1, ConLeche.looseBVarsBounded_abstract1 nb 0 hnbB⟩
      · simp only [Expr.WScoped]
        exact ⟨hws.1, ConLeche.WScoped.abstract1 0 hnbW⟩
      · simp only [ConLeche.Expr.nestOcc, ha, Bool.false_or]
        rw [nestOcc_abstract1 (by omega) nb 0]
        exact hnbO hk
      · rw [denoteMeta_forallE, hta]
        simp only [Option.bind_eq_bind, Option.bind_some]
        rw [denoteMeta_erasedEq (erasedEq_abstract1_instantiate1 nb 0 hnbB) (dep + 1), hnba]
        rfl
      · exact interp_pi_congr_body fun x hx => hnbr (cons x ρ) (Sat_cons V hρ hx)
    refine ⟨⟨TypeReg.pi 0 _ hA hTRb hB0, ?_, hout⟩, hokP⟩
    by_cases hv0 : pwBit φ bm.pw = 0
    · -- hole-free: the body is
      have hco : ConstOn R (.pi 0 (pwBit φ bm.pw) ta ba) := ConstOn.pi 0 _ hA (hTRb (hB0 hv0))
      exact ⟨_, hco.accOn, SizeOn.const (empty_mem_univ w), InvOn.const _ _⟩
    · refine ⟨_, AccOn.pi hw 0 hv0 hA (AccOn.congrQ
          (fun i n => (shiftQ_holeQK (by have := hR.hiEq; omega) i n).symm) hAb),
        SizeOn.pi hw hA hszb, InvOn.pi ?_ (InvOn.mono hinvb fun i hi => mentP_body i hi)⟩
      refine NoBVar.mono (fun i hi hn => hi (Or.inl hn))
        (noBVar_not_mentNH hws.1 hbb.1 hholes (fun s _ hs => ?_) hta)
      simp only [ConLeche.Expr.nestOcc, Bool.or_eq_false_iff] at hs
      exact hs.1
  | @hole L met dep kb e wt i ty hw' hocc hfn hlo hhi' hlen hpar hfree =>
    intro _ hhi hfr Δa ea R hC hea hgr hR _
    refine acc_of_whnfK hin hw' hfr hC hea hgr hR.dom fun hfrw _ hlw wa hwa _ _ => ?_
    have hspine := Expr.mkAppN_getApp wt
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ wt.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    have hlenv := DenoteMetaSpine.length_eq hsp
    have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
    have hL0 : ctx.hiAt 0 ≤ L.hi := by have := hR.hiEq; omega
    have hQ : HoleQK ctx L met dep (dep - 1 - i) vs.length := by
      refine Or.inl ⟨i - ctx.nP, ?_, ?_, by omega, by rw [← hlenv, hlen]⟩
      · simp only [ConLeche.NestCtx.hiAt] at hhi'; omega
      · simp only [ConLeche.NestCtx.hiAt] at hhi' hL0; omega
    refine ⟨⟨TypeReg.holeApp hR.rich hR.symm hQ hvs, ⟨_, AccOn.holeApp hQ hvs,
      SizeOn.const (unitSet_mem_univ w), InvOn.const _ _⟩, (outMent_self dep wt).trans hlw⟩,
      hfrw.2.1, hfrw.1, fun hk => ?_, _, by rw [hspine] at hwa; exact hwa, fun _ _ => rfl⟩
    split at hk <;> cases hk
  | @famHole L met dep kb e wt i ty key nI hw' hocc hfn hlo hhi' hj hfam hlen hfree hmet =>
    intro _ hhi hfr Δa ea R hC hea hgr hR _
    refine acc_of_whnfK hin hw' hfr hC hea hgr hR.dom fun hfrw _ hlw wa hwa _ _ => ?_
    have hspine := Expr.mkAppN_getApp wt
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ wt.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    have hlenv := DenoteMetaSpine.length_eq hsp
    have hvs := constOn_spine hR.agree hhi hsp fun a ha => ⟨hwsargs a ha, hfree a ha⟩
    have hQ : HoleQK ctx L met dep (dep - 1 - i) vs.length := by
      refine Or.inr (Or.inl ⟨i - ctx.hiAt 0, key, hj, ?_, hmet, by omega, by omega⟩)
      rw [← hlenv, hlen]; exact hfam
    exact ⟨⟨TypeReg.holeApp hR.rich hR.symm hQ hvs, ⟨_, AccOn.holeApp hQ hvs,
      SizeOn.const (unitSet_mem_univ w), InvOn.const _ _⟩, (outMent_self dep wt).trans hlw⟩,
      hfrw.2.1, hfrw.1, nofun, _, by rw [hspine] at hwa; exact hwa, fun _ _ => rfl⟩
  | @ownHole L met dep kb e wt i ty g hw' hocc hfn hlo hhi' hj hg hle hpar hfree har =>
    intro _ hhi hfr Δa ea R hC hea hgr hR _
    refine acc_of_whnfK hin hw' hfr hC hea hgr hR.dom fun hfrw _ hlw wa hwa _ _ => ?_
    have hspine := Expr.mkAppN_getApp wt
    rw [hfn] at hspine
    rw [← hspine] at hwa
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hwa
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hwsargs : ∀ a ∈ wt.getAppArgs, Expr.WScoped dep a := by
      have h0 := hfrw.1
      rw [← hspine] at h0
      exact (wScoped_mkAppN _ h0).2
    have hlenv := DenoteMetaSpine.length_eq hsp
    rw [← List.take_append_drop L.dsF.length wt.getAppArgs] at hsp
    obtain ⟨vs₁, vs₂, rfl, hsp₁, hsp₂⟩ := DenoteMetaSpine.split _ hsp
    have hvs₂ := constOn_spine hR.agree hhi hsp₂ fun a ha =>
      ⟨hwsargs a (List.mem_of_mem_drop ha), hfree a ha⟩
    have hsp₁' : DenoteMetaSpine mp.base2.acval env φ dep L.dsF vs₁ := by
      rw [← hpar]; exact hsp₁
    have hh := hR.own (i - ctx.hiAt 0 - L.nF) g hg vs₁ hsp₁'
    rw [show dep - 1 - (ctx.hiAt 0 + L.nF + (i - ctx.hiAt 0 - L.nF)) = dep - 1 - i by omega] at hh
    have hQ : HoleQK ctx L met dep (dep - 1 - i) (vs₁.length + vs₂.length) := by
      refine Or.inr (Or.inr ⟨i - ctx.hiAt 0 - L.nF, g, hg, by omega, by omega, ?_⟩)
      rw [← List.length_append, ← hlenv, har]
    exact ⟨⟨TypeReg.holeAppArgs hR.rich hR.symm hQ hh hvs₂, ⟨_, AccOn.holeAppArgs hQ hh hvs₂,
      SizeOn.const (unitSet_mem_univ w), InvOn.const _ _⟩, (outMent_self dep wt).trans hlw⟩,
      hfrw.2.1, hfrw.1, nofun, _, by rw [hspine] at hwa; exact hwa, fun _ _ => rfl⟩
  | @cont L met dep kb e wt n us Lc nPc nI cty hw' hocc hfn hnm hC hquot hlen hidx hds hnI huse
      ihu =>
    intro hcovk hhid hfr Δa ea R hC' hea hgr hR hlay
    have hok := hcovk rfl
    refine acc_of_whnfK hin hw' hfr hC' hea hgr hR.dom fun hfrw hCw hlw wa hwa hgw _ => ?_
    have hwa0 := hwa
    have hspine := Expr.mkAppN_getApp wt
    rw [hfn] at hspine
    generalize hargs : wt.getAppArgs = args at hspine hlen hidx hds hnI huse ihu
    subst hspine
    have hwsargs := (wScoped_mkAppN _ hfrw.1).2
    have hps : ∀ x ∈ args.take nPc, Expr.WScoped L.hi x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP mp.base2 φ dep Δa x := fun x hx =>
      ⟨ConLeche.WScoped.of_fvarsBelow (hwsargs x (List.mem_of_mem_take hx))
          (ConLeche.Expr.fvarB_le (hds x hx).2),
        ConLeche.Expr.bvarB_le (Nat.le_of_eq (hds x hx).1),
        fun l hl => hfrw.2.2 l (leaves_mkAppN_arg (List.mem_of_mem_take hx) hl),
        hCw.of_subset fun l hl => leaves_mkAppN_arg (List.mem_of_mem_take hx) hl⟩
    rw [← List.take_append_drop nPc args] at hwa
    obtain ⟨fa, vs, hfa, hsp, -⟩ := denoteMeta_mkAppN_inv hwa
    obtain ⟨vs₁, vs₂, -, hsp₁, -⟩ := DenoteMetaSpine.split _ hsp
    obtain ⟨D, hD, mm, hmm, hn, cv, caps, hf, hlenP, ⟨nI', cty', hnI', hids⟩, -, hwD, hacc⟩ :=
      ihu hok hhid hR hlay hC'.1 hps hsp₁ hwa hgw
    change D.member mm = n at hn
    subst hn
    rw [hnI] at hnI'
    obtain ⟨rfl, -⟩ : nI = nI' ∧ cty = cty' := by simpa using hnI'
    have hisC : ∀ isa, DenoteMetaSpine mp.base2.acval env φ dep (args.drop nPc) isa →
        ∀ v ∈ isa, ConstOn R v := fun isa hisa =>
      constOn_spine hR.agree hhid hisa fun a ha => ⟨hwsargs a (List.mem_of_mem_drop ha), hidx a ha⟩
    have hc := accConclK_of_carrier mp hD hmm hf hwa hlenP.symm
      (by rw [List.length_drop, hids]; omega) (fun x hx => hwsargs x (List.mem_of_mem_take hx))
      hsp₁ hR hgw hisC hw hwD hacc (G := fun c => c = mm) rfl
    rw [List.take_append_drop] at hc
    exact ⟨⟨hc.1, hc.2.1, hc.2.2.trans hlw⟩, hfrw.2.1, hfrw.1, nofun, wa, hwa0, fun _ _ => rfl⟩
  | teleNil =>
    intro _ hfr Δa ca R _ hca _ hR _ _
    exact ⟨⟨hR.agree, by simpa using hca, by simpa using hfr.1⟩, trivial⟩
  | @teleCons L met nF j a b bm k nd ks nds res ha hs hb iha _ ihb =>
    intro hcovk hfr Δa ca R hC hca hgr hR hlay hsm
    obtain ⟨ta, ba, hta, hba, rfl⟩ := denoteMeta_forallE_inv hca
    obtain ⟨hws, hbb, hLb⟩ := hfr
    simp only [Expr.WScoped] at hws
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbb
    have hLa : Expr.LeavesBounded a := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    have hLbd : Expr.LeavesBounded b := fun l hl => hLb l (by simp [Expr.fvarLeaves, hl])
    obtain ⟨hgA, hgB⟩ := WellDenotedV.hoist_pi (V := V) hgr
    obtain ⟨⟨-, ⟨Af, hAf, hszf, hinvf⟩, -⟩, hokf⟩ :=
      iha (fun hk => hcovk ⟨k, List.mem_cons_self, hk⟩) (by omega) ⟨hws.1, hbb.1, hLa⟩
        hC.forallE_ty hta hgA hR hlay
    have hCop := CtxOkP.openS hC.forallE_ty hC.forallE_body hta hgA
    have hfr' := frame_open2 hws.1 hbb.1 hws.2 hbb.2 hLa hLbd
    rw [show L.hi + j + 1 = L.hi + (j + 1) by omega] at hCop hfr' hba
    have hR' := hR.underBoth (by omega) ta (transfer_of_accOn hAf hsm.1)
    obtain ⟨hPi, hO⟩ := ihb (fun ⟨k', hk', hkf⟩ => hcovk ⟨k', List.mem_cons_of_mem _ hk', hkf⟩)
      hfr' hCop hba hgB
      (by rw [show L.hi + (j + 1) = L.hi + j + 1 by omega]; exact hR')
      (by rw [show L.hi + (j + 1) = L.hi + j + 1 by omega]; exact hlay.under ta) hsm.2
    rw [show L.hi + (j + 1) + nF = L.hi + j + (nF + 1) by omega,
      show L.hi + (j + 1) = L.hi + j + 1 by omega] at hPi
    rw [show L.hi + (j + 1) = L.hi + j + 1 by omega] at hO
    exact ⟨⟨⟨Af, hAf, hszf, hinvf⟩, hPi⟩, hokf, hO⟩
  | ctorsNil =>
    intro _ Δ R _ _ _ x hx
    exact nomatch hx
  | @ctorsCons L met cv nF crest cs ks nds cur htele hu4 hres hidx hrest ihtele ihrest =>
    intro hok Δ R hR hlay hprem x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · obtain ⟨ca, hfr, hC, hca, hgr, hsm⟩ := hprem _ List.mem_cons_self
      obtain ⟨hnl, xs, hop⟩ := ConLeche.posDK_tele_shape htele
      have hcurcl := (ConLeche.Verify.openPisAtFvars_bounded nF hop hfr.2.1).1
      have := ihtele (fun _ => hok) (by simpa using hfr) (by simpa using hC) (by simpa using hca)
        hgr (by simpa using hR) (by simpa using hlay) hsm
      simp only [Nat.add_zero] at this
      obtain ⟨hPi, hO⟩ := this
      refine ⟨hfr.2.1, ca, ks, nds, cur, hca, hnl, hcurcl, fun i hil hne => ?_, hres, hidx, hPi, hO⟩
      simp only [List.any_eq_false, List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq,
        not_and] at hu4
      cases hU : ConLeche.structUsedLater (ConLeche.closeTelescope nds L.hi cur) 0 i
      · rfl
      · exact absurd hU (hu4 i hil hne)
    · exact ihrest hok hR hlay (fun y hy => hprem y (List.mem_cons_of_mem _ hy)) x hx
  | @node kc lo met hlay hwalk ih =>
    exact posDK_node_acc mp hin hw (ConLeche.nestLayoutK_spec hlay) ih
  | @use L met kc kn ps lo metc rs bs hinst hk52 hnode hgrp hlv hkds hlen hbs hinner hall hpar
      hbind hhook ihnode ihbind =>
    intro hok d hd Δa R hR hlay hΔ hps psa hpsa is wa hwa hgr
    obtain ⟨hhd, hnPc, bsL, xs, tya, dsa, hbl, hxl, htyl, hbf, hsat, hdsw, hLds, hlayc, hdsa, hCds,
      hpos⟩ := hbr hinst hnode hgrp hlv hkds hlen hbs hinner hall hpar hhook hd hR.hiEq hlay hΔ hps
        hpsa
    -- the MET bindings' bounds
    have hex : ∀ j, ∃ A : (Nat → V) → V, (∀ ρ, A ρ ∈ˢ (univ w : V)) ∧
        InvOn (ParamPos d ctx.nP) A ∧
        ∀ (key : NestKey) (nI : Nat), j < lo.L.nF → lo.L.fams[j]? = some (key, nI) → j ∈ metc →
          ∀ hj : j < xs.length,
            ValAcc (HoleQK ctx L met d) R A xs[j] nI ∧ ValRich (HoleQK ctx L met d) R xs[j] nI := by
      intro j
      by_cases hjm : j < lo.L.nF ∧ j ∈ metc
      · have hjb : j < bsL.length := by omega
        have hjx : j < xs.length := by omega
        obtain ⟨⟨p, hp, hp1, hp2⟩, hws, hbb, hLb, hC, hden, hgrj, har⟩ := hbf j hjb hjx
        have hacc := ihbind p hp (by rw [hp1]; exact hjm.2)
        rw [hp2] at hacc
        rcases hfj : lo.L.fams[j]? with _ | ⟨key, nI⟩
        · exact ⟨fun _ => empty, fun _ => empty_mem_univ w, InvOn.const _ _,
            fun key nI _ hk => by cases hk⟩
        · obtain ⟨A, hA, hinv, hva, hvr⟩ := hacc hok hd hR hlay hΔ hws hbb hLb hC hden hgrj nI
            (har hjm.2 key nI hfj)
          refine ⟨A, hA, hinv, fun key' nI' _ hk _ _ => ?_⟩
          obtain ⟨-, rfl⟩ : key = key' ∧ nI = nI' := by simpa using hk
          exact ⟨hva, hvr⟩
      · exact ⟨fun _ => empty, fun _ => empty_mem_univ w, InvOn.const _ _,
          fun key nI hj hk hm => absurd ⟨hj, hm⟩ hjm⟩
    let Aj : Nat → (Nat → V) → V := fun j => Classical.choose (hex j)
    have hAj : ∀ j, (∀ ρ, Aj j ρ ∈ˢ (univ w : V)) ∧ InvOn (ParamPos d ctx.nP) (Aj j) ∧
        ∀ (key : NestKey) (nI : Nat), j < lo.L.nF → lo.L.fams[j]? = some (key, nI) → j ∈ metc →
          ∀ hj : j < xs.length,
            ValAcc (HoleQK ctx L met d) R (Aj j) xs[j] nI ∧
              ValRich (HoleQK ctx L met d) R xs[j] nI :=
      fun j => Classical.choose_spec (hex j)
    have hspec := ConLeche.PosDKH.node_spec hnode
    have hlvl : lo.L.lvls = kc.lvls := by rw [hspec.2.2.2.1, hlv]
    rw [← hlvl] at hwa
    obtain ⟨D, hD, mm, hmm, hn, cv, caps, hf, hnd, hlenP, hwD, hacc⟩ := useAccK mp hw hok hspec hhd
      ihnode hR hd hΔ hgrp hwa hgr (fun x hx => Expr.WScoped.mono hd (hps x hx).1) hnPc hlen hpsa
      hxl htyl hsat (Aj := Aj) (fun j => (hAj j).1) (fun j => (hAj j).2.1)
      (fun j key nI hj hk hm hjx => (hAj j).2.2 key nI hj hk hm hjx) hdsw hLds hlayc hdsa hCds hpos
    rw [hlvl] at hlenP hwD hacc hwa
    obtain ⟨⟨nI, cty⟩, hnI⟩ := hinst
    -- N2 at the user
    obtain ⟨psa0, hpsa0, rfl⟩ := DenoteMetaSpine.unlift (m := mp.base2) (φ := φ) hd
      (fun x hx => (hps x hx).1) hpsa
    obtain ⟨fa, vs, hfa, -, -⟩ := denoteMeta_mkAppN_inv hwa
    rw [← hn] at hfa
    obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK (by rw [hn]; exact hf) hfa
    change kc.lvls.length = cv.levelParams.length at hul
    have hrun : ConLeche.nestInstType (m := CheckM) ctx L.hi ⟨D.member mm, kc.lvls, ps⟩
        = .ok (nI, cty) := by rw [hn]; exact hnI
    obtain ⟨-, hids, hte⟩ := n2_link mp hD hmm hok.1.find hrun (by rw [hn]; exact hf) hnd hul
      hlenP (fun x hx => ⟨(hps x hx).1, (hps x hx).2.1⟩) hpsa0
    have hkf : ∀ σ : Nat → V, keyFrame (psa0.map (AnnotTerm.liftN (d - L.hi) · 0)) d σ
        = keyFrame psa0 L.hi (dropV (d - L.hi) σ) := by
      intro σ
      have := keyFrame_liftN psa0 L.hi (d - L.hi) σ
      rwa [show L.hi + (d - L.hi) = d by omega] at this
    refine ⟨D, hD, mm, hmm, hn, cv, caps, hf, hlenP, ⟨nI, cty, hnI, hids⟩, fun ρ ρ' hr => ?_, hwD,
      hacc⟩
    rw [hkf, hkf]
    refine hte _ _ fun i hi => ?_
    refine hR.agree ρ ρ' hr (i + (d - L.hi)) fun hp => hi ?_
    obtain ⟨h1, h2, h3⟩ := hp
    refine ⟨by omega, ?_, ?_⟩ <;> omega
  | @bindFam L met i ty hlo hhi hmet =>
    intro hok d hd Δa R hR hlay hΔ hws hbb hLb hC ba hba hgr nI har
    rw [denoteMeta_fvar] at hba
    cases hba
    obtain ⟨key, hk⟩ := har.1 i ty rfl hlo hhi
    have hL0 : ctx.hiAt 0 + L.nF ≤ L.hi := by have := hR.hiEq; omega
    have hQ : ∀ vs : List V, vs.length = nI → HoleQK ctx L met d (d - 1 - i) vs.length := by
      intro vs hvl
      refine Or.inr (Or.inl ⟨i - ctx.hiAt 0, key, by omega, by rw [hvl]; exact hk, hmet, by omega,
        by omega⟩)
    refine ⟨fun _ => unitSet, fun _ => unitSet_mem_univ w, InvOn.const _ _, ?_, ?_⟩
    · intro ρ ρ₀ hr vs hvl y hy
      rw [interp_bvar] at hy
      refine ⟨unitSet, fun _ => (d - 1 - i, vs, y), Subset.refl _,
        fun _ _ => ⟨by unfold Adm; exact hQ vs hvl, hy⟩, fun ρ' _ h' => ?_⟩
      rw [interp_bvar]
      exact h' pt pt_mem_unitSet
    · intro ρ ρ₀ hr vs hvl hpt
      rw [interp_bvar] at hpt
      obtain ⟨ρ'', hr'', hle'', z, hz, hzp⟩ := hR.rich ρ ρ₀ hr _ vs (hQ vs hvl) hpt
      exact ⟨ρ'', hr'', hle'', z, by rw [interp_bvar]; exact hz, hzp⟩
  | @bindOwn L met b i ty hfn hlo hhi =>
    intro hok d hd Δa R hR hlay hΔ hws hbb hLb hC ba hba hgr nI har
    obtain ⟨hargs, g, hg, hni⟩ := har.2.1 i ty hfn hlo hhi
    have hspine := Expr.mkAppN_getApp b
    rw [hfn, hargs] at hspine
    rw [← hspine] at hba
    obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hba
    rw [denoteMeta_fvar] at hfa
    cases hfa
    have hbl := hR.own (i - ctx.hiAt 0 - L.nF) g hg vs hsp
    have hpos : d - 1 - (ctx.hiAt 0 + L.nF + (i - ctx.hiAt 0 - L.nF)) = d - 1 - i := by
      have := hR.hiEq; omega
    rw [hpos] at hbl
    have hvsl : vs.length = L.dsF.length := (DenoteMetaSpine.length_eq hsp).symm
    have hQ : ∀ us : List V, us.length = nI →
        HoleQK ctx L met d (d - 1 - i) (vs.length + us.length) := by
      intro us hul
      refine Or.inr (Or.inr ⟨i - ctx.hiAt 0 - L.nF, g, hg, by have := hR.hiEq; omega,
        by have := hR.hiEq; omega, ?_⟩)
      rw [hvsl, hul, ← hni]; omega
    have happ : ∀ (σ : Nat → V) (us : List V),
        us.foldl app (interp V σ (AnnotTerm.mkAppN (.bvar (d - 1 - i)) vs))
          = (vs.map (interp V σ) ++ us).foldl app (σ (d - 1 - i)) := by
      intro σ us
      rw [interp_mkAppN_foldl, interp_bvar, ← List.foldl_append]
    refine ⟨fun _ => unitSet, fun _ => unitSet_mem_univ w, InvOn.const _ _, ?_, ?_⟩
    · intro ρ ρ₀ hr us hul y hy
      rw [happ] at hy
      refine ⟨unitSet, fun _ => (d - 1 - i, vs.map (interp V ρ) ++ us, y), Subset.refl _,
        fun _ _ => ⟨by unfold Adm; simpa using hQ us hul, hy⟩, fun ρ' hr' h' => ?_⟩
      have := h' pt pt_mem_unitSet
      unfold Holds at this
      simp only at this
      rw [hbl ρ ρ' hr' us] at this
      rw [happ]
      exact this
    · intro ρ ρ₀ hr us hul hpt
      rw [happ] at hpt
      obtain ⟨ρ'', hr'', hle'', z, hz, hzp⟩ :=
        hR.rich ρ ρ₀ hr _ (vs.map (interp V ρ) ++ us) (by simpa using hQ us hul) hpt
      refine ⟨ρ'', hr'', hle'', z, ?_, hzp⟩
      rw [happ, ← hbl ρ ρ'' hr'' us]
      exact hz
  | @bindKey L met b n us hfn huse ihu =>
    intro hok d hd Δa R hR hlay hΔ hws hbb hLb hC ba hba hgr nI har
    have hspine := Expr.mkAppN_getApp b
    rw [hfn] at hspine
    have hws' := hws
    rw [← hspine] at hws' hba
    have hbb' := hbb
    rw [← hspine] at hbb'
    have hwsargs := (wScoped_mkAppN _ hws').2
    have hbbargs := (looseBVarsBounded_mkAppN_inv hbb').2
    have hps : ∀ x ∈ b.getAppArgs, Expr.WScoped L.hi x ∧ x.looseBVarsBounded 0 = true ∧
        Expr.LeavesBounded x ∧ CtxOkP mp.base2 φ d Δa x := fun x hx =>
      ⟨hwsargs x hx, hbbargs x hx,
        fun l hl => hLb l (by rw [← hspine]; exact leaves_mkAppN_arg hx hl),
        hC.of_subset fun l hl => by rw [← hspine]; exact leaves_mkAppN_arg hx hl⟩
    obtain ⟨fa, psa, hfa, hpsa, rfl⟩ := denoteMeta_mkAppN_inv hba
    have hba' : denoteMeta mp.base2.acval env φ d
        (Expr.mkAppN (.const n us) (b.getAppArgs ++ [])) = some (AnnotTerm.mkAppN fa psa) := by
      rw [List.append_nil]; exact hba
    obtain ⟨D, hD, mm, hmm, hn, cv, caps, hf, hlenP, ⟨nI', cty', hnI', hids⟩, hte, hwD, hacc⟩ :=
      ihu hok hd hR hlay hΔ hps hpsa hba' hgr
    obtain ⟨hne, cty2, hnI2⟩ := har.2.2 n us hfn
    change ConLeche.nestInstType (m := CheckM) ctx L.hi ⟨n, us, b.getAppArgs⟩ = _ at hnI'
    rw [hnI2] at hnI'
    obtain ⟨rfl, -⟩ : nI = nI' ∧ cty2 = cty' := by simpa using hnI'
    change D.member mm = n at hn
    subst hn
    rw [← hids]
    obtain ⟨A, hA, hinv, hacc'⟩ := hacc
    have hpswd : ∀ x ∈ b.getAppArgs, Expr.WScoped d x :=
      fun x hx => Expr.WScoped.mono hd (hwsargs x hx)
    refine ⟨A, hA, hinv, valAcc_key mp hD hmm hf hba hlenP.symm hpswd hpsa hR.dom hgr hte
      (G := fun c => c = mm) rfl hacc', ?_⟩
    -- rich vacuously: a key occurrence never holds `pt` at a positive level (R4)
    intro ρ ρ₀ hr vs hvl hpt
    exact absurd hpt (rich_of_keyOcc mp hD hmm hf hba hlenP.symm hpswd hpsa hgr (hwD ▸ hw) hne ρ
      (hR.dom ρ ρ₀ hr).1 vs hvl)
  | synNil => trivial
  | synUse => trivial

/-! ## The member constructor -/

/-- **A derived member constructor is accessible** (`memberCtorD_acc`'s
conclusion, for the key-named derivation): every field's reading accessible
under the earlier ones along the frameless accessibility relation, each bound
reading only its field's output's non-hole positions, the result's indices
hole-free — the form `blockCtorAcc_of_walk` reads. -/
theorem memberCtorDK_acc {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} {F nF : Nat}
    {hk : UseHookK} (hbr : UseCoreK mp φ ctx (fueledOps .verified F) hk)
    {crest cur : Expr} {ks : List PosKind} {nds : List (Expr × ConLeche.BinderMeta)}
    {met : List Nat}
    (htele : PosDKH (fueledOps .verified F) env ctx hk
      (.tele (ConLeche.rootLayoutK ctx) met nF 0 crest ks nds cur))
    (hhead : ConLeche.nestResHead cur = true)
    (hok : (cur.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0))
      = true)
    (hcov : (∃ k ∈ ks, k.flat = false) → ContOk mp φ w ctx) (hfr : Frame (ctx.hiAt 0) crest)
    {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta mp.base2.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca)
    (hR : HoleRelA mp.base2 φ ctx [] (ctx.hiAt 0) Δa R) (hsm : TeleSmall w nF R ca) :
    PiAccThen w ctx [] (ResultIdxConst ctx.nP) nF (ctx.hiAt 0) (nds.map (·.1)) R ca := by
  have hroot : (ConLeche.rootLayoutK ctx).hi + 0 = ctx.hiAt 0 := by simp [ConLeche.rootLayoutK]
  have := (posDK_acc mp hin hw hbr htele hcov (by rw [hroot]; exact hfr) (by rw [hroot]; exact hC)
    (by rw [hroot]; exact hca) hgr (by rw [hroot]; exact holeRelAK_root hR)
    (by rw [hroot]; exact laySiteK_root) hsm).1
  have hrh : (ConLeche.rootLayoutK ctx).hi = ctx.hiAt 0 := rfl
  rw [hrh, Nat.add_zero] at this
  exact PiAccThenG.toOld (fun _ _ _ => holeQK_root_iff) _ _ _ _ _
    (PiAccThenG.mono (fun _ _ h => resultIdxConst_of_resultAt (Nat.le_add_right _ _) hhead hok h)
      nF _ _ R ca this)

/-! ## At the hook -/

/-- **THE KEY-NAMED DERIVATION IS ACCESSIBLE** at the hook `UseOkK` (the core
of the uses' matches by `useCoreK`). -/
theorem posDK_accOk {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} {F : Nat} :
    ∀ {j : PosJK}, PosDKH (fueledOps .verified F) env ctx
      (ConLeche.UseOkK (fueledOps .verified F) env ctx) j → AccJK mp φ w ctx j :=
  posDK_acc mp hin hw (useCoreK mp hin)

/-- **A derived member constructor is accessible** (`memberCtorD_acc`'s form)
at the hook `UseOkK`. -/
theorem memberCtorDK_accOk {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {w : Nat} (hw : w ≠ 0) {ctx : NestCtx} {F nF : Nat}
    {crest cur : Expr} {ks : List PosKind} {nds : List (Expr × ConLeche.BinderMeta)}
    {met : List Nat}
    (htele : PosDKH (fueledOps .verified F) env ctx
      (ConLeche.UseOkK (fueledOps .verified F) env ctx)
      (.tele (ConLeche.rootLayoutK ctx) met nF 0 crest ks nds cur))
    (hhead : ConLeche.nestResHead cur = true)
    (hok : (cur.getAppArgs.drop ctx.nP).all (fun a => !a.nestOcc ctx.names ctx.nP (ctx.hiAt 0))
      = true)
    (hcov : (∃ k ∈ ks, k.flat = false) → ContOk mp φ w ctx) (hfr : Frame (ctx.hiAt 0) crest)
    {Δa : List AnnotTerm} {ca : AnnotTerm} {R : FrameRel V}
    (hC : CtxOkP mp.base2 φ (ctx.hiAt 0) Δa crest)
    (hca : denoteMeta mp.base2.acval env φ (ctx.hiAt 0) crest = some ca) (hgr : Graded V Δa ca)
    (hR : HoleRelA mp.base2 φ ctx [] (ctx.hiAt 0) Δa R) (hsm : TeleSmall w nF R ca) :
    PiAccThen w ctx [] (ResultIdxConst ctx.nP) nF (ctx.hiAt 0) (nds.map (·.1)) R ca :=
  memberCtorDK_acc mp hin hw (useCoreK mp hin) htele hhead hok hcov hfr hC hca hgr hR hsm

end ConLeche.Model
