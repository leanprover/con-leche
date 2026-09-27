module

public import ConLeche.Model.Inductives.FrameRelK
public import ConLeche.Model.Inductives.PosDerivMono
public import ConLeche.Verify.Inductives.PosDerivK
public import ConLeche.Verify.Inductives.LayoutKSpec
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Verify.EnvWF

public section

/-!
# The key-named positivity derivation is monotone in the holes (PRIMREC / NESTKN-M2/M3)

The model side of the key-named positivity check (variant E,
`Kernel/Inductives/PositivityK.lean`): every judgment of its derivation
`PosDK` (`Verify/Inductives/PosDerivK.lean`) reads monotonically in the holes,
by ONE induction on the derivation — the analogue of `posD_mono`
(`PosDerivMono.lean`) with the path frames replaced by layouts.

* `field`/`tele` at a layout `L` and a met set: along every hole relation at
  the layout (`HoleRelK`), as today;
* `ctors`: every crest of the node walked (`CtorWalkedK`, the crest given);
* `node`: **the node's frame fact** (`FrameMonoK`): along every hole relation
  at the node's BASE (its flexible families, only the met ones constrained),
  the node's group's carriers grow between the key frames of related pairs,
  with the per-constructor hole-fit transfer — `frameIterGen` over the frame
  relation, which is a hole relation at the node's layout
  (`frameRelK_holeRelK`);
* `use`/`bind`: the use-site instantiation of the child's frame fact (M3).

This file is NEW beside the live `PosDerivMono.lean`: nothing live imports it.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey LayoutK LayoutOutK
  instPisWith fueledOps PosDK PosJK PosKind groupCtors grpSub)

universe w

variable {V : Type w} [SetTheory V] {env : Env}

/-! ## The node's group, as today's frame group -/

/-- A layout's own group as a frame group: each member with its hole's type. -/
@[expose] def grpOfK (lo : LayoutOutK) : List (Name × Expr) :=
  lo.ginfo.map fun g => (g.1, g.2.2)

theorem grpOfK_names (lo : LayoutOutK) : (grpOfK lo).map (·.1) = lo.ginfo.map (·.1) := by
  simp [grpOfK]

theorem grpOfK_length (lo : LayoutOutK) : (grpOfK lo).length = lo.ginfo.length := by
  simp [grpOfK]

/-- **The layout's crest substitution is the frame's** (`crestsK`'s own-group
lookup is `grpSub` at the layout's group). -/
theorem crestsK_sub_eq (us : List Level) (hc : Nat) (ginfo : List (Name × Nat × Expr)) :
    (fun c us' => if us' == us then
        (ginfo.mapIdx fun g (n, _, ty) => (n, Expr.fvar (hc + g) ty)).lookup c else none)
      = grpSub us hc (ginfo.map fun g => (g.1, g.2.2)) := by
  funext c us'
  unfold grpSub
  congr 2
  apply List.ext_getElem (by simp)
  intro i h₁ h₂
  simp

/-- **`crestsK`, read**: one crest per constructor, each the constructor
instantiated at the layout's parameters with its own group abstracted. -/
theorem crestsK_spec {us : List Level} {dsF : List Expr} {grp : List (Name × Expr)} :
    ∀ {ctors : List (ConstantVal × Nat)} {crests : List Expr},
      ConLeche.crestsK us dsF grp ctors = some crests →
      ctors.length = crests.length ∧ ∀ x ∈ ctors.zip crests,
        instPisWith dsF ((x.1.1.type.instantiateLevelParams x.1.1.levelParams us).replaceConsts
          fun c us' => if us' == us then grp.lookup c else none) = some x.2
  | [], crests, h => by
    simp only [ConLeche.crestsK, Option.some.injEq] at h
    subst h
    exact ⟨rfl, fun _ hx => nomatch hx⟩
  | (cv, n) :: cs, crests, h => by
    simp only [ConLeche.crestsK, Option.bind_eq_bind] at h
    rcases ht : instPisWith dsF ((cv.type.instantiateLevelParams cv.levelParams us).replaceConsts
      fun c us' => if us' == us then grp.lookup c else none) with _ | t
    · rw [ht] at h; simp at h
    rw [ht] at h
    simp only [Option.bind_some] at h
    rcases hr : ConLeche.crestsK us dsF grp cs with _ | rest
    · rw [hr] at h; simp at h
    rw [hr] at h
    simp only [Option.bind_some, Option.pure_def, Option.some.injEq] at h
    subst h
    obtain ⟨hl, hall⟩ := crestsK_spec hr
    refine ⟨by simp [hl], fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ht
    · exact hall x hx

theorem mem_zip_of_mem_left {α β : Type} :
    ∀ {as : List α} {bs : List β}, as.length = bs.length → ∀ {a : α}, a ∈ as →
      ∃ b, (a, b) ∈ as.zip bs
  | [], _, _, _, ha => nomatch ha
  | _ :: _, [], h, _, _ => by simp at h
  | a' :: as, b' :: bs, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨b', List.mem_cons_self⟩
    · obtain ⟨b, hb⟩ := mem_zip_of_mem_left (by simpa using h) ha
      exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-! ## What the walk of a node proves -/

variable {φ : Name → Nat}

/-- What a node's walk leaves of one (constructor, crest): the crest reads,
its telescope positive along the relation, its result headed by a hole with
hole-free indices. -/
@[expose] def CtorWalkedK (m : EnvModel V env) (φ : Name → Nat) (ctx : NestCtx) (hi nPc : Nat)
    (R : FrameRel V) (x : (ConstantVal × Nat) × Expr) : Prop :=
  ∃ ca cur, denoteMeta m.acval env φ hi x.2 = some ca ∧ ConLeche.nestResHead cur = true ∧
    (cur.getAppArgs.drop nPc).all (fun a => !a.nestOcc ctx.names ctx.nP hi) = true ∧
    PiPosThen (ResultAt m φ ctx.nP hi (hi + x.1.2) cur) x.1.2 R ca

section Motive

variable {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) (φ : Name → Nat) (ctx : NestCtx)

/-- **A node's frame fact** (`FrameMono` at a layout): at every recorded
block holding the node's head, along every hole relation at the node's BASE
(its flexible families — the MET ones growing — at depth
`hc = hiAt0 + nF`) whose pairs satisfy the container's parameter telescope at
the key frames of `DsF`, the group is well formed, the level parameters
distinct, the group's carriers grow between the key frames, and every
member's hole fits transfer to the larger carrier. -/
@[expose] def FrameMonoK (lo : LayoutOutK) (met : List Nat) : Prop :=
  ContCover mp ctx →
  ∀ {D : LfpDatum V}, D ∈ mp.lfpBlocks → ∀ {mm : Nat}, mm < D.k →
    D.member mm = ((grpOfK lo).headD default).1 →
  ∀ {lps : List Name},
    (∀ mm', mm' < D.k → ∃ cv caps, env.find? (D.member mm') = some (.indInfo cv caps) ∧
      cv.levelParams = lps) →
    lo.L.lvls.length = lps.length →
    (∀ x ∈ lo.L.dsF, Expr.WScoped (ctx.hiAt 0 + lo.L.nF) x ∧ x.looseBVarsBounded 0 = true) →
    ∀ {dsa : List AnnotTerm},
      DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt 0 + lo.L.nF) lo.L.dsF dsa →
    (D.params (Level.substFn φ lps lo.L.lvls)).length = lo.L.dsF.length →
    ((∃ nP' L, ConLeche.nestContainer ctx (D.member mm) = some (nP', L) ∧ L ≠ []) ∨ lps.Nodup) →
    ∀ {Δh : List AnnotTerm} {R₀ : FrameRel V},
    HoleRelK mp.base2 φ ctx (layoutBaseK ctx lo.L) met (ctx.hiAt 0 + lo.L.nF) Δh R₀ →
    LaySiteK mp.base2 φ ctx (layoutBaseK ctx lo.L) (ctx.hiAt 0 + lo.L.nF) Δh →
    Δh.length = ctx.hiAt 0 + lo.L.nF →
    (∀ x ∈ lo.L.dsF, CtxOkP mp.base2 φ (ctx.hiAt 0 + lo.L.nF) Δh x) →
    (∀ x ∈ lo.L.dsF, Expr.LeavesBounded x) →
    (∀ ρ ρ', R₀ ρ ρ' →
      Sat V (D.params (Level.substFn φ lps lo.L.lvls)).reverse
        (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ) ∧
      Sat V (D.params (Level.substFn φ lps lo.L.lvls)).reverse
        (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ')) →
    lps.Nodup ∧ GrpOk ctx D (ctx.hiAt 0 + lo.L.nF) lo.L.lvls lo.L.dsF (grpOfK lo) ∧
    (∀ ρ ρ', R₀ ρ ρ' → ∀ c, InGrp D (grpOfK lo) c →
      FamLe (D.idx (Level.substFn φ lps lo.L.lvls) (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ) c)
        (D.carrier (Level.substFn φ lps lo.L.lvls) (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ) c)
        (D.carrier (Level.substFn φ lps lo.L.lvls) (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ') c)) ∧
    ∀ ρ ρ', R₀ ρ ρ' → ∀ g, InGrp D (grpOfK lo) g → ∀ t j fs,
      D.HFits (Level.substFn φ lps lo.L.lvls) (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ)
        (grpTuple D (Level.substFn φ lps lo.L.lvls) (grpOfK lo)
          (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ) (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ'))
        t g j fs →
      D.HFits (Level.substFn φ lps lo.L.lvls) (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ')
        (D.carrier (Level.substFn φ lps lo.L.lvls) (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) ρ'))
        t g j fs

/-- What the walk of a node's crests proves (the `ctors` judgment's motive). -/
@[expose] def CtorsMonoK (L : LayoutK) (met : List Nat)
    (cs : List ((ConstantVal × Nat) × Expr)) : Prop :=
  ContCover mp ctx →
  ∀ {Δ : List AnnotTerm} {R : FrameRel V}, HoleRelK mp.base2 φ ctx L met L.hi Δ R →
    LaySiteK mp.base2 φ ctx L L.hi Δ →
    (∀ x ∈ cs, ∃ ca, Frame L.hi x.2 ∧ CtxOkP mp.base2 φ L.hi Δ x.2 ∧
      denoteMeta mp.base2.acval env φ L.hi x.2 = some ca ∧ Graded V Δ ca) →
    ∀ x ∈ cs, CtorWalkedK mp.base2 φ ctx L.hi L.dsF.length R x

end Motive

/-! ## The node -/

/-- **A node's frame fact from its walk**: the layout's spec gives the group
(well formed: the head in the block, the mates in the head's recorded block),
its constructors and their crests; `frameIterGen` along the frame relation —
a hole relation at the node's layout (`frameRelK_holeRelK`) — with the walk
supplied by the crests' walk. -/
theorem posDK_node_mono {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env)
    (hin : RulesInputs V mp.base2 φ) {ctx : NestCtx} {F : Nat} {kc : NestKey}
    {lo : LayoutOutK} {met : List Nat}
    (hspec : ConLeche.LayoutSpecK (fueledOps .verified F) env ctx kc lo)
    (ih : CtorsMonoK mp φ ctx lo.L met (lo.ctors.zip lo.crests)) :
    FrameMonoK mp φ ctx lo met := by
  obtain ⟨⟨nPc, Lc, hqC, hgcC⟩, hndC, hgrpL, hlvl, hgnames, hhiL, -, hinst, hcrests, -, hcty⟩ :=
    hspec
  intro hcov D hD mm hmm hhead lps hlps hul hds dsa hdsa hlenP hnL Δh R₀ hR₀ hlay hΔ hCds hLds
    hfit
  have hblkD := hcov.block D hD
  have hkN := lfp_namesLen mp hD
  -- the group
  have hnames : (grpOfK lo).map (·.1) = kc.cname :: ConLeche.nestFrameMates ctx kc.cname := by
    rw [grpOfK_names, hgnames, hgrpL]
  have hhd : ((grpOfK lo).headD default).1 = kc.cname := by
    cases h : grpOfK lo with
    | nil => rw [h] at hnames; simp at hnames
    | cons p ps => rw [h] at hnames; simp only [List.map_cons, List.cons.injEq] at hnames
                   simp [hnames.1]
  rw [hhd] at hhead
  have hne : grpOfK lo ≠ [] := by
    intro h; rw [h] at hnames; simp at hnames
  have hndn : ((grpOfK lo).map (·.1)).Nodup := by
    rw [hnames]; exact ConLeche.nestFrameMates_nodup _
  have hinstG : ∀ p ∈ grpOfK lo, ∃ nI, ConLeche.nestInstType (m := CheckM) ctx
      (ctx.hiAt 0 + lo.L.nF) ⟨p.1, lo.L.lvls, lo.L.dsF⟩ = .ok (nI, p.2) := by
    intro p hp
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hp
    refine ⟨g.2.1, ?_⟩
    have := hinst g hg
    rw [hlvl]
    exact this
  have hg : GrpOk ctx D (ctx.hiAt 0 + lo.L.nF) lo.L.lvls lo.L.dsF (grpOfK lo) := by
    refine ⟨hne, hndn, fun p hp => ⟨?_, hinstG p hp⟩⟩
    have hpn : p.1 ∈ kc.cname :: ConLeche.nestFrameMates ctx kc.cname := by
      rw [← hnames]; exact List.mem_map_of_mem hp
    rcases List.mem_cons.mp hpn with hp1 | hp1
    · exact ⟨mm, hmm, by rw [hp1, hhead]⟩
    · have hin' := (ConLeche.mem_nestFrameMates hp1).1
      obtain ⟨cv₀, caps₀, hf₀, -⟩ := hlps mm hmm
      have hblkOf : ConLeche.nestBlockOf ctx kc.cname = D.names := by
        unfold ConLeche.nestBlockOf
        rw [← hhead, hcov.find, hf₀]
        exact hblkD.all mm hmm cv₀ caps₀ hf₀
      rw [hblkOf] at hin'
      obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hin'
      refine ⟨i, by omega, ?_⟩
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hpi]
  -- the constructors, at the key's parameter count
  obtain ⟨cv, caps, hfc⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
  rw [hhead] at hfc
  obtain ⟨lps', hlps', hlenP', -, -⟩ := contBlock_facts mp hcov hD hmm (by rw [hhead]; exact hfc)
    (by rw [hhead]; exact hqC)
  have hnPc : nPc = lo.L.dsF.length := by rw [← hlenP' (Level.substFn φ lps lo.L.lvls), hlenP]
  have hgc : groupCtors ctx lo.L.dsF.length ((grpOfK lo).map (·.1)) = some lo.ctors := by
    rw [hnames, ← hnPc]; exact hgcC
  have hndl : lps.Nodup := frame_lps_nodup mp hcov hD hmm hlps (by rw [hhead, hnames]; simp) hgc
    hndC hnL
  -- the frame relation is a hole relation at the layout
  have hlenG : lo.L.hi = ctx.hiAt 0 + lo.L.nF + (grpOfK lo).length := by
    rw [hhiL, grpOfK_length]
  have hR' := frameRelK_holeRelK mp hD hblkD.nodup hkN hcov.find hlps hndl hul hds hdsa hlenP
    hg.2 (L := lo.L) (by rw [hnames, hgrpL]) rfl rfl hlenG hR₀ hfit
  have hle := frameIterGen mp hD hblkD.nodup hkN hcov.find hlps hndl hul hds hdsa hlenP hg.2 hin
    (F := F) hblkD.ctors (by have := hR₀.agree; simpa using this) hΔ hCds hLds hfit hgc
    (fun Q hprem hQ x hx => ?_)
  · exact ⟨hndl, hg, hle.1, hle.2⟩
  -- the walk: each constructor's crest, walked
  have hsub := crestsK_sub_eq lo.L.lvls (ctx.hiAt 0 + lo.L.nF) lo.ginfo
  rw [← hlvl] at hcrests
  obtain ⟨hlc, hcr⟩ := crestsK_spec hcrests
  obtain ⟨crest, hxc⟩ := mem_zip_of_mem_left hlc hx
  have hcrx := hcr _ hxc
  simp only at hcrx
  rw [hsub] at hcrx
  rw [← hlenG] at hR'
  have hlay' : LaySiteK mp.base2 φ ctx lo.L lo.L.hi ((grpTys mp.base2 φ (grpOfK lo)).reverse ++ Δh) := by
    have := hlay.base.weaken (Ts := (grpTys mp.base2 φ (grpOfK lo)).reverse)
      (g := (grpOfK lo).length) (by simp [grpTys])
    rwa [← hlenG] at this
  have hwalkd := ih hcov hR' hlay' (fun y hy => ?_) _ hxc
  · obtain ⟨ca, cur, hca, hres, hidx, hpos⟩ := hwalkd
    refine ⟨nodup_of_nameNodup (hndC x hx), crest, ca, cur, hcrx, ?_, hres, ?_, ?_⟩
    · rw [hlenG] at hca; exact hca
    · rw [hlenG] at hidx; exact hidx
    · rw [hlenG] at hpos; exact hpos
  -- every crest reads, graded, at the frame's context
  have hyc := hcr _ hy
  rw [hsub] at hyc
  obtain ⟨ty, sv, hty, -⟩ := hcty y.2 (List.of_mem_zip hy).2
  rw [hlenG] at hty ⊢
  exact hprem y.1 y.2 (hQ _ (List.of_mem_zip hy).1) hyc ⟨ty, hty⟩

end ConLeche.Model
