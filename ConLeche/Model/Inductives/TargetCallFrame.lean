module

public import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContAccRel
import ConLeche.Model.Inductives.NestPosRed
import ConLeche.Model.Inductives.StructStageFormer
import ConLeche.Model.Inductives.StructData
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Inductives.StructRead
import ConLeche.Model.Rules.Sound
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Semantics.Tower.FixRecCoreI
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Inductives.PosFieldLeaf

public section

/-!
# A node's constructor field at an ADMISSIBLE frame (lane NESTIND, session 27)

The calls' landing (`NodeLands`) reads a decoding's fields at an
admissible visit `(ρ, Y)` of its node: the fields fit the node's recorded
clause at the hole frame of `(ρ, Y)` (`LfpDatum.HFits`).  This file moves
that fit onto the positivity WALK of the node's constructor: at the walk
valuation `σW` (the admissible stack valuation `σ`, the node's group holes
at `Y`'s hole values), every field lies in the reading of its walked
normal form (`nds`, the derivation's output) — the recorded fields and the
walk's crest are one substitution apart (`crest_read`,
`spineFit_substTele`), the crest and its normal form read alike field by
field (`posD_red`).

* `dyn_ctorFit` — a derived node `u` (a listed `PosTree`), at every
  admissible stack valuation;
* `blk_ctorFit` — the block itself (node `0`), at its true frame.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx NestHole
  BlockParts BlockShape fueledOps PosTree PosNodeOk PosD PosKind BinderMeta closeTelescope
  openPisAtFvars instPisWith grpNews grpSub)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-! ## A frame's constructors, derived and typed -/

/-- **A frame's constructors, each derived and TYPED** (`posD_frame_teles`
with the constructor's inference at the frame's depth). -/
theorem posD_ctors_typed {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx} :
    ∀ {J : ConLeche.PosJ} {ts : List PosTree}, PosD ops env ctx J ts → match J with
    | .ctors prog hi us ds sub cs => ∀ x ∈ cs, ∃ crest ks nds cur ts' ty,
        instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts sub)
          = some crest ∧ ops.inferType env hi crest = .ok ty ∧
        PosD ops env ctx (.tele prog hi x.2 0 crest ks nds cur) ts' ∧ ∀ t ∈ ts', t ∈ ts
    | .frame prog us ds grp => ∃ ctors, ConLeche.groupCtors ctx ds.length (grp.map (·.1))
          = some ctors ∧
        ∀ x ∈ ctors, ∃ crest ks nds cur ts' ty,
          instPisWith ds ((x.1.type.instantiateLevelParams x.1.levelParams us).replaceConsts
            (grpSub us (ctx.hiAt prog.length) grp)) = some crest ∧
          ops.inferType env (ctx.hiAt prog.length + grp.length) crest = .ok ty ∧
          PosD ops env ctx (.tele ((grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
            (ctx.hiAt prog.length + grp.length) x.2 0 crest ks nds cur) ts' ∧ ∀ t ∈ ts', t ∈ ts
    | _ => True := by
  intro J ts h
  induction h with
  | frame _ _ _ _ _ _ _ hctors _ _ ih => exact ⟨_, hctors, ih⟩
  | ctorsNil => intro x hx; exact nomatch hx
  | @ctorsCons prog hi us ds sub cv nF cs crest ty sv ks nds cur ts ts' _ hcrest hty _ htele _ _ _ _
      _ ihrest =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨crest, ks, nds, cur, ts, ty, hcrest, hty, htele,
        fun t ht => List.mem_append_left _ ht⟩
    · obtain ⟨c', k', n', cu', ts'', ty', h1, h2, h3, h4⟩ := ihrest x hx
      exact ⟨c', k', n', cu', ts'', ty', h1, h2, h3, fun t ht => List.mem_append_right _ (h4 t ht)⟩
  | _ => trivial

/-! ## A telescope's fields, read at a fitting frame -/

/-- **A derived telescope's outputs are closed and scoped** where its
input is: every walked normal form (a whnf reduct, closed back over its
Π-variables) and the result. -/
theorem posD_tele_closed {env : Env} (hwf : ConLeche.EnvWF env) {ctx : NestCtx} {F : Nat}
    {prog : List NestHole} {hi nF : Nat} {cur : Expr} {ks : List PosKind}
    {nds : List (Expr × BinderMeta)} {res : Expr} {ts : List PosTree}
    (hd : PosD (fueledOps .verified F) env ctx (.tele prog hi nF 0 cur ks nds res) ts)
    (hhi : ctx.hiAt prog.length ≤ hi) (hcb : cur.looseBVarsBounded 0 = true)
    (hcw : Expr.WScoped hi cur) :
    res.looseBVarsBounded 0 = true ∧ Expr.WScoped (hi + nF) res ∧
    ∀ (i : Nat) (p : Expr × BinderMeta), nds[i]? = some p →
      p.1.looseBVarsBounded 0 = true ∧ Expr.WScoped (hi + i) p.1 := by
  obtain ⟨-, hnl, xs, hop, hall⟩ := ConLeche.posD_tele_open hd
  rw [Nat.add_zero] at hop
  obtain ⟨hresB, hxB⟩ := ConLeche.Verify.openPisAtFvars_bounded nF hop hcb
  obtain ⟨hxW, hresW⟩ := ConLeche.openPisAtFvars_WScoped nF cur hi hop hcw
  have hxl : xs.length = nF := ConLeche.Verify.openPisAtFvars_length _ hop
  refine ⟨hresB, hresW, fun i p hp => ?_⟩
  have hil : i < xs.length := by rw [hxl, ← hnl]; exact (List.getElem?_eq_some_iff.mp hp).1
  obtain ⟨k, nd, ts', -, hnd, hfd, -⟩ := hall i xs[i] (List.getElem?_eq_getElem hil)
  rw [hp, Option.map_some, Option.some.injEq] at hnd
  subst hnd
  rw [Nat.add_zero] at hfd
  -- the opened domain is closed and scoped below its variable
  have hxi := List.getElem_mem hil
  obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ hop i _ (List.getElem?_eq_getElem hil)
  have hxw := hxW _ hxi
  rw [hty] at hxw
  have htyW : Expr.WScoped (hi + i) ty := by
    unfold Expr.WScoped at hxw; exact hxw.2
  have hxb := hxB _ hxi
  rw [hty] at hxb
  have hfd' : PosD (fueledOps .verified F) env ctx
      (.field prog (hi + i) 0 (Expr.fvar (hi + i) ty).fvarTypeD k p.1) ts' := by
    rw [← hty]; exact hfd
  refine ⟨(posD_field_leaf (fun d e w hw he => ConLeche.whnf_looseBVars hwf F hw he) hfd'
    (by omega) hxb).1, posD_field_scoped (fun d e w hw he => ConLeche.whnf_WScoped hwf F hw he)
    hfd' htyW⟩

/-- A valid Π-tower's domains are valid at a fitting spine's prefixes. -/
theorem annotValid_mkPisAV_dom {B : AnnotTerm} :
    ∀ {tl : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {bs : List V},
      AnnotValid V ρ (mkPisAV tl B) → SpineFit ρ (tl.map (·.2.2)) bs →
      ∀ l, l < tl.length → AnnotValid V (consList (bs.take l) ρ) ((tl.map (·.2.2)).getD l default)
  | [], _, _, _, _, l, hl => absurd hl (Nat.not_lt_zero _)
  | _ :: _, _, [], _, h, _, _ => h.elim
  | d :: tl, ρ, b :: bs, hv, h, l, hl => by
    have hv' : AnnotValid V ρ (.pi d.1 d.2.1 d.2.2 (mkPisAV tl B)) := hv
    rw [AnnotValid_pi] at hv'
    cases l with
    | zero => simpa using hv'.1
    | succ l =>
      simp only [List.map_cons, List.getD_cons_succ, List.take_succ_cons, consList_cons]
      exact annotValid_mkPisAV_dom (hv'.2.1 b h.1) h.2 l (by simpa using hl)

/-- **The fields of a derived telescope lie in their normal forms'
readings**: at a frame satisfying the telescope's context, a spine fitting
the input's domains has its `i`-th value in the reading of the `i`-th
walked normal form, at the frame extended by the earlier values. -/
theorem posD_tele_fieldMem {env : Env} {m : EnvModel V env} {φ : Name → Nat}
    (hin : Rules.RulesInputs V m φ) {ctx : NestCtx} {F : Nat} {prog : List NestHole}
    {hi nF : Nat} {cur : Expr} {ks : List PosKind} {nds : List (Expr × BinderMeta)} {res : Expr}
    {ts : List PosTree}
    (hd : PosD (fueledOps .verified F) env ctx (.tele prog hi nF 0 cur ks nds res) ts)
    (hndC : ∀ (i : Nat) (p : Expr × BinderMeta), nds[i]? = some p → p.1.looseBVarsBounded 0 = true)
    (hresC : res.looseBVarsBounded 0 = true)
    (hfr : Rules.Frame hi cur) {Δa : List AnnotTerm} {ca : AnnotTerm}
    (hC : CtxOkP m φ hi Δa cur) (hca : denoteMeta m.acval env φ hi cur = some ca)
    (hgr : Rules.Graded V Δa ca) {abD : List (Nat × Nat × AnnotTerm)} {B : AnnotTerm}
    (hcaE : ca = mkPisAV abD B) (hlD : abD.length = nF) {σ : Nat → V} (hσ : Sat V Δa σ)
    {fs : List V} (hfit : SpineFit σ (abD.map (·.2.2)) fs) :
    fs.length = nF ∧ nds.length = nF ∧
    ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
      ∃ nda, denoteMeta m.acval env φ (hi + i) nd = some nda ∧
        fs.getD i pt ∈ˢ interp V (consList (fs.take i) σ) nda ∧
        AnnotValid V (consList (fs.take i) σ) nda := by
  have hred := posD_red hin hd (by simpa using hfr) (by simpa using hC) (by simpa using hca) hgr
  simp only [Nat.add_zero] at hred
  obtain ⟨abD', abN, B', hcaE', hNE, hlD', hlN, -, hEq, hgN, -, -⟩ := hred
  rw [hcaE] at hcaE'
  obtain ⟨rfl, rfl⟩ := mkPisAV_inj (by rw [hlD, hlD']) hcaE'
  have hfitN : SpineFit σ (abN.map (·.2.2)) fs := (hEq.spineFit_iff hσ fs).mp hfit
  have hfl : fs.length = nF := by rw [hfitN.length_eq, List.length_map, hlN]
  have hnl : nds.length = nF := (ConLeche.posD_tele_open hd).2.1
  refine ⟨hfl, hnl, fun i nd hnd => ?_⟩
  have hil : i < nds.length := by
    rcases h : nds[i]? with _ | p
    · rw [h] at hnd; exact nomatch hnd
    · exact (List.getElem?_eq_some_iff.mp h).1
  -- the closed normal form, opened back at the walk's variables
  obtain ⟨xs, rest, hop, -, hdoms⟩ := open_of_erasedEq_closeTelescope nds hi res
    (closeTelescope nds hi res)
    (fun p hp => by
      obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem hp
      exact hndC i' _ (List.getElem?_eq_getElem hi'))
    hresC (Expr.ErasedEq.rfl _)
  obtain ⟨pps, b, hst, -, hpl, hbind⟩ := denoteMeta_openPis nds.length hop hNE
  rw [hnl, ← hlN, stripPisAV_mkPisAV] at hst
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hst)
  have hxl : xs.length = nds.length := ConLeche.Verify.openPisAtFvars_length _ hop
  obtain ⟨p, hp, -, hpd⟩ := hbind i (xs[i]'(by omega)) (List.getElem?_eq_getElem (by omega))
  have hE := hdoms i (xs[i]'(by omega)) nd (List.getElem?_eq_getElem (by omega)) hnd
  refine ⟨p.2.2, by rw [← denoteMeta_erasedEq hE]; exact hpd, ?_, ?_⟩
  · have hmem := FixKI.spineFit_getD_mem' hfitN (l := i) (by rw [List.length_map]; omega)
    rw [List.getD_eq_getElem?_getD (l := List.map _ abN), List.getElem?_map, hp] at hmem
    exact hmem
  · have hval := annotValid_mkPisAV_dom (hgN σ hσ).2 hfitN i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, hp] at hval
    exact hval

/-! ## A derived node's constructor, at an admissible frame -/

set_option maxHeartbeats 4000000 in
/-- **A derived node's constructor at an admissible frame** (lane NESTIND,
session 27): the constructor `(m, j)` of a listed node's recorded block is
one of the node's frame constructors (`groupCtors`), walked (`PosD.tele`
at the node's frame stack) with closed, scoped normal forms; and at every
stack valuation `σ` satisfying the node's stack context and every tuple
`Y` of the key frame's tuple space, a spine hole-fitting the constructor
at `(keyFrame σ, Y)` has each field in the reading of its walked normal
form, at the walk valuation `σ` extended by the group's hole values of
`Y` (which satisfies the frame's context). -/
theorem dyn_ctorFit {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI}
    {mpC : EnvModelM V μ envC} {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}
    (H : DynCtx F mk mpC ctx d ns) {u : PosTree} (hu : u ∈ ns) (ψ : Name → Nat)
    {m j : Nat} (hm : m < (lfpSel mpC d.toLfp u.key.cname).k)
    (hj : j < (lfpSel mpC d.toLfp u.key.cname).nctors m) :
    ∃ (cv : ConstantVal) (nF : Nat) (ctors : List (ConstantVal × Nat)) (crest : Expr)
      (ks : List PosKind) (nds : List (Expr × BinderMeta)) (cur : Expr) (ts' : List PosTree),
      envI.find? ((lfpSel mpC d.toLfp u.key.cname).ctorName m j)
        = some (.ctorInfo cv u.key.ds.length nF) ∧
      ConLeche.groupCtors ctx u.key.ds.length (u.grp.map (·.1)) = some ctors ∧ (cv, nF) ∈ ctors ∧
      instPisWith u.key.ds ((cv.type.instantiateLevelParams cv.levelParams u.key.lvls).replaceConsts
        (grpSub u.key.lvls (ctx.hiAt u.anc.length) u.grp)) = some crest ∧
      PosD (fueledOps .verified F) envI ctx
        (.tele ((grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc)
          (ctx.hiAt u.anc.length + u.grp.length) nF 0 crest ks nds cur) ts' ∧
      (∀ t ∈ ts', t ∈ u.kids) ∧ nds.length = nF ∧
      crest.looseBVarsBounded 0 = true ∧ cur.looseBVarsBounded 0 = true ∧
      (∀ (i : Nat) (p : Expr × BinderMeta), nds[i]? = some p →
        p.1.looseBVarsBounded 0 = true ∧
          Expr.WScoped (ctx.hiAt u.anc.length + u.grp.length + i) p.1) ∧
      ∀ σ : Nat → V, Sat V (stackCtx mk.base2 ψ ctx u.anc (d.holeCtx ψ).reverse) σ →
      ∀ Y, InTupleSpace ((lfpSel mpC d.toLfp u.key.cname).w (nodeψ envC ψ u))
          (lfpSel mpC d.toLfp u.key.cname).N
          ((lfpSel mpC d.toLfp u.key.cname).idx (nodeψ envC ψ u)
            (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) σ)) Y →
      ∀ t fs, (lfpSel mpC d.toLfp u.key.cname).HFits (nodeψ envC ψ u)
          (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) σ) Y t m j fs →
        Sat V ((grpTys mk.base2 ψ u.grp).reverse ++ stackCtx mk.base2 ψ ctx u.anc (d.holeCtx ψ).reverse)
          (consList (grpVals (lfpSel mpC d.toLfp u.key.cname) (nodeψ envC ψ u) u.grp
            (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) σ) Y) σ) ∧
        fs.length = nF ∧
        ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
          ∃ nda, denoteMeta mk.base2.acval envI ψ (ctx.hiAt u.anc.length + u.grp.length + i) nd
              = some nda ∧
            fs.getD i pt ∈ˢ interp V (consList (fs.take i)
              (consList (grpVals (lfpSel mpC d.toLfp u.key.cname) (nodeψ envC ψ u) u.grp
                (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) σ) Y) σ)) nda ∧
            AnnotValid V (consList (fs.take i)
              (consList (grpVals (lfpSel mpC d.toLfp u.key.cname) (nodeψ envC ψ u) u.grp
                (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) σ) Y) σ)) nda := by
  classical
  have hok := H.hok u hu
  obtain ⟨hD, hwid, hnN, hkN, hall, mm, hmm, hmmH, cv0, caps0, hfc0, hlps, hlpsOf, hndl, hul, hlenP,
    -, hg⟩ := dyn_nodeBlock H hu
  have hψ : nodeψ envC ψ u = Level.substFn ψ cv0.levelParams u.key.lvls := by
    unfold nodeψ; rw [hlpsOf]
  rw [hψ]
  have hds := posNodeOk_dsAnc hok
  have hdsa := dyn_dsaI H hu ψ
  have hsem := H.hsem u hu ψ
  have hkfit := fun σ hσ => nodeKeyFit mk (H.hΔ0 ψ) hok hsem hD hmm hmmH hfc0 (hlenP _).symm hdsa σ hσ
  generalize nodeDsaI mk ctx ψ u = dsa at hdsa hkfit ⊢
  generalize hDdef : lfpSel mpC d.toLfp u.key.cname = D at *
  -- the frame's constructors
  obtain ⟨ctors, hgc, hallc⟩ := posD_ctors_typed hok.1
  have hG : InGrp D u.grp m := hall m hm
  obtain ⟨nP', L, hL, hlenL, hfL⟩ := (H.hcov.block D hD).ctors m hm
  obtain ⟨-, hctorsAll⟩ := ConLeche.groupCtors_spec hgc
  have hjL : j < L.length := by rw [hlenL]; exact hj
  obtain ⟨hxmem, hnP'⟩ : L[j] ∈ ctors ∧ nP' = u.key.ds.length := by
    obtain ⟨nP'', L'', hL'', hnP'', hallL⟩ :=
      hctorsAll (D.member m) (List.contains_iff_mem.mp hG.2)
    rw [hL] at hL''
    obtain ⟨rfl, rfl⟩ : nP' = nP'' ∧ L = L'' := by simpa using hL''
    refine ⟨hallL _ (List.getElem_mem hjL), ?_⟩
    rcases hnP'' with h' | h'
    · exact h'
    · rw [h'] at hjL; exact absurd hjL (Nat.not_lt_zero _)
  have hfc := hfL j hjL
  rw [hnP'] at hfc
  obtain ⟨crest, ks, nds, cur, ts', ty, hcr, hty, htele, hsub⟩ := hallc _ hxmem
  obtain ⟨-, crest', ab, hcr', ⟨Tys, hlT, hTys, hEqF⟩, hlen, hrd⟩ :=
    crest_read mk hD hnN hkN H.hcov.find hlps hndl hul hds hdsa (hlenP _) hg hG.1 hj hfc
  rw [hcr] at hcr'
  obtain rfl := Option.some.inj hcr'
  -- the crest: framed, in the frame's context, graded
  have hΔ := stackCtx_length_hi (m := mk.base2) (φ := ψ) (H.hΔ0 ψ) u.anc
  obtain ⟨-, hCds, hLds⟩ := hsem
  have hcvwf := mk.base2.wf _ (ConLeche.Semantics.Env.find?_mem hfc)
  have hcl : (L[j].1.type.instantiateLevelParams L[j].1.levelParams u.key.lvls).hasFvar = false := by
    rw [Expr.hasFvar_instantiateLevelParams]; exact hcvwf.1
  have hbb : (L[j].1.type.instantiateLevelParams L[j].1.levelParams u.key.lvls).looseBVarsBounded 0
      = true := by
    rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hcvwf.2.2.2.1
  obtain ⟨hfr, hCP⟩ := crest_frame mk hD hnN hkN H.hcov.find hlps hndl hul hds hdsa (hlenP _) hg hΔ
    hCds hLds hcl hbb hcr
  have hty' : ConLeche.inferTypeCore .verified envI F
      (ctx.hiAt u.anc.length + u.grp.length) crest = .ok ty := hty
  obtain ⟨-, -, -, -, hgr, -, -⟩ :=
    Rules.infer_sound (Rules.RulesInputs.ofSem mk ψ) (ConLeche.Rules.inferTypeCore_bridge hty')
      hfr hCP.toCtxOk hrd
  -- the walked normal forms: closed and scoped
  have hhiP : ctx.hiAt ((grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse
      ++ u.anc).length ≤ ctx.hiAt u.anc.length + u.grp.length := by
    simp [grpNews, ConLeche.NestCtx.hiAt]; omega
  obtain ⟨hresB, -, hndC⟩ := posD_tele_closed mk.base2.wf htele hhiP hfr.2.1 hfr.1
  have hnl : nds.length = L[j].2 := (ConLeche.posD_tele_open htele).2.1
  refine ⟨L[j].1, L[j].2, ctors, crest, ks, nds, cur, ts', hfc, hgc, hxmem, hcr, htele, hsub, hnl,
    hfr.2.1, hresB, hndC, fun σ hσ Y hY t fs hf => ?_⟩
  -- the fit at the substituted walk valuation
  have hs := hkfit σ hσ
  generalize hρ' : keyFrame dsa (ctx.hiAt u.anc.length) σ = ρ' at hs hY hf
  have hS := substE_grp mk hD hnN hkN H.hcov.find hlps hndl hul hds hdsa (hlenP _) hg ρ' Y σ
  rw [hρ'] at hS
  have hagS := holeAgree_instance mk hD hs σ (fun mm => decide (InGrp D u.grp mm)) Y
    (vs := (List.range D.k).map fun mm =>
      if decide (InGrp D u.grp mm) = true then D.holeVal (Level.substFn ψ cv0.levelParams u.key.lvls) ρ' Y mm
      else interp V σ (mk.base2.acval (D.member mm) (Level.substFn ψ cv0.levelParams u.key.lvls)))
    (by simp) (fun m hm => by simp)
  have hf' : D.HFits (Level.substFn ψ cv0.levelParams u.key.lvls) ρ'
      (fun c => if decide (InGrp D u.grp c) = true then Y c
        else D.carrier (Level.substFn ψ cv0.levelParams u.key.lvls) ρ' c) t m j fs :=
    (LfpDatum.hfits_congr_members fun c hc => by simp [hall c hc]).mp hf
  have hha := (mk.lfp_ok D hD).1.holeApp (Level.substFn ψ cv0.levelParams u.key.lvls) m
    (by rw [hwid]; exact hm) j hj
  obtain ⟨-, hsp, -⟩ := (LfpDatum.hfits_iff_of_holeAgree hha hagS).mp hf'
  have hsatS := frameVals_sat mk hD hs hlT hTys (fun mm => decide (InGrp D u.grp mm)) Y hY σ
  have hsp' := (hEqF.spineFit_iff hsatS fs).mpr hsp
  have hW := (spineFit_substTele V _ ab 0 _ fs).mpr (by rw [hS]; exact hsp')
  -- the frame's context is satisfied
  have hsatW : Sat V ((grpTys mk.base2 ψ u.grp).reverse
      ++ stackCtx mk.base2 ψ ctx u.anc (d.holeCtx ψ).reverse)
      (consList (grpVals D (Level.substFn ψ cv0.levelParams u.key.lvls) u.grp ρ' Y) σ) :=
    sat_of_spineFit hσ (grpVals_fit mk hD hnN hkN H.hcov.find hlps hndl hul hds hdsa (hlenP _) hg
      ρ' Y hY σ)
  obtain ⟨hfl, -, hmem⟩ := posD_tele_fieldMem (Rules.RulesInputs.ofSem mk ψ) htele
    (fun i p hp => (hndC i p hp).1) hresB hfr hCP hrd hgr rfl
    (by rw [substTele_length, hlen]) hsatW hW
  exact ⟨hsatW, hfl, hmem⟩

/-! ## The block's own constructor (node `0`) -/

set_option maxHeartbeats 4000000 in
/-- **A member constructor at the block's hole frame** (node `0`): the
constructor's walk (`MemberCtorD`) has closed, scoped normal forms, and at
every parameter frame `ρp` satisfying the block's parameters and every
tuple `Y` of its tuple space, a spine hole-fitting the constructor at
`(ρp, Y)` has each field in the reading of its walked normal form at the
hole frame (which satisfies the hole context) extended by the earlier
fields — the recorded fields and the walk's crest read alike
(`BlockAbsRead`, `canonCrest_of_walk`), the crest and its normal form
field by field (`posD_red`). -/
theorem blk_ctorFit {env : Env} {μ' : ConLeche.CheckMode} (mk : EnvModelM V μ' env)
    (ψ : Name → Nat) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mk.base2 d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : ConLeche.nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes)
    {m j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM m)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (ConLeche.nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type) = some crest)
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find? env.consts).hiAt 0) crest = .ok ty)
    {ks : List PosKind} {tyN : Expr} {ts : List PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts)
      cA.2 crest ks tyN ts) :
    ∃ (nds : List (Expr × BinderMeta)) (cur : Expr),
    PosD (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts)
      (.tele [] ((p.nestCtx fvsP env.find? env.consts).hiAt 0) cA.2 0 crest ks nds cur) ts ∧
    tyN = closeTelescope nds ((p.nestCtx fvsP env.find? env.consts).hiAt 0) cur ∧
    (∀ (i : Nat) (q : Expr × BinderMeta), nds[i]? = some q →
      q.1.looseBVarsBounded 0 = true ∧
        Expr.WScoped ((p.nestCtx fvsP env.find? env.consts).hiAt 0 + i) q.1) ∧
    nds.length = cA.2 ∧
    crest.looseBVarsBounded 0 = true ∧ cur.looseBVarsBounded 0 = true ∧
    (∀ ρp : Nat → V, Sat V (d.params ψ).reverse ρp →
    ∀ Y, InTupleSpace (d.toLfp.w ψ) d.toLfp.N (d.toLfp.idx ψ ρp) Y →
    ∀ t fs, d.toLfp.HFits ψ ρp Y t m j fs →
      Sat V (d.holeCtx ψ).reverse (d.toLfp.frame ψ ρp Y) ∧ fs.length = cA.2 ∧
      ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
        ∃ nda, denoteMeta mk.base2.acval env ψ ((p.nestCtx fvsP env.find? env.consts).hiAt 0 + i) nd
            = some nda ∧
          fs.getD i pt ∈ˢ interp V (consList (fs.take i) (d.toLfp.frame ψ ρp Y)) nda ∧
          AnnotValid V (consList (fs.take i) (d.toLfp.frame ψ ρp Y)) nda) ∧
    -- at ANY valuation of the hole context (node `0`'s patched one)
    ∀ σ : Nat → V, Sat V (d.holeCtx ψ).reverse σ → ∀ fs, SpineFit σ (d.toLfp.fields ψ m j) fs →
      fs.length = cA.2 ∧
      ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
        ∃ nda, denoteMeta mk.base2.acval env ψ ((p.nestCtx fvsP env.find? env.consts).hiAt 0 + i) nd
            = some nda ∧
          fs.getD i pt ∈ˢ interp V (consList (fs.take i) σ) nda ∧
          AnnotValid V (consList (fs.take i) σ) nda := by
  have hin := Rules.RulesInputs.ofSem mk ψ
  have hcN : (p.nestCtx fvsP env.find? env.consts).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find? env.consts).nP = d.nP := hnP
  have hcL : (p.nestCtx fvsP env.find? env.consts).lps = lps := hlps
  have hcPar : (p.nestCtx fvsP env.find? env.consts).params = fvsP := rfl
  have hlenF : fvsP.length = d.nP := by
    rw [← hnP]; exact ConLeche.Verify.openPisAtFvars_length _ hop0
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hop0
  -- the recorded reading, at the canonical crest the walk's is up to erasure
  obtain ⟨-, A, hA, hR⟩ := (hcore.2 m j cA hcj).2
  obtain ⟨ab, -, hAr, -, hlab, -, -, -, hEqA⟩ := hR ψ
  obtain ⟨A', hA', herased⟩ := canonCrest_of_walk (ctx := p.nestCtx fvsP env.find? env.consts)
    (k := d.k)
    (fun i x hx => by rw [hcPar] at hx; simpa using hidxF i x hx)
    (by rw [hcPar, hlenF, hcP])
    (fun t x hx => by
      have ht : t < (p.nestCtx fvsP env.find? env.consts).names.length := by
        rw [← ConLeche.nestHoles_length hholes]; exact (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨cv, caps, -, hget⟩ := ConLeche.nestHoles_getElem? hholes ht
      rw [hget] at hx
      exact ⟨_, (Option.some.inj hx).symm⟩)
    (by rw [ConLeche.nestHoles_length hholes, hcN, hk]) hcrest
  rw [hcN, hcL, hcP, hA] at hA'
  obtain rfl := Option.some.inj hA'
  have hca : denoteMeta mk.base2.acval env ψ (d.nP + d.k) crest
      = some (mkPisAV ab (AnnotTerm.mkAppN (.bvar (cA.2 + (d.k - 1 - m)))
          (paramBvarsAt d.nP (d.nP + d.k + cA.2) ++ d.absE ψ m j))) := by
    rw [denoteMeta_erasedEq herased]; exact hAr
  obtain ⟨abD, -, B, hhi, hcaE, -, hlD, -, -, hfr, hCP, hgr, -, -, -, -, -, -, hsatFrame⟩ :=
    blockWalkCtx hin hN hcore.1 hnames hlps hnP hnIdxs hk hcv0 hop0 hholes hCf hCb hcrest hinf
      hd hca
  obtain ⟨rfl, rfl⟩ := mkPisAV_inj (hlab.trans hlD.symm) hcaE
  obtain ⟨nds, cur, htele, htyN, -⟩ := hd
  have hhi0 : (p.nestCtx fvsP env.find? env.consts).hiAt ([] : List NestHole).length ≤
      (p.nestCtx fvsP env.find? env.consts).hiAt 0 := Nat.le_refl _
  obtain ⟨hresB, -, hndC⟩ := posD_tele_closed mk.base2.wf htele hhi0
    hfr.2.1 (by rw [hhi]; exact hfr.1)
  have hnl : nds.length = cA.2 := (ConLeche.posD_tele_open htele).2.1
  refine ⟨nds, cur, htele, htyN, hndC, hnl, hfr.2.1, hresB, fun ρp hs Y hY t fs hf => ?_,
    fun σ hsat fs hfs => ?_⟩
  · have hsat := hsatFrame ρp hs Y hY
    have hfit := (hEqA.spineFit_iff hsat fs).mpr hf.2.1
    obtain ⟨hfl, -, hmem⟩ := posD_tele_fieldMem hin htele (fun i q hq => (hndC i q hq).1) hresB
      (by rw [hhi]; exact hfr) (by rw [hhi]; exact hCP) (by rw [hhi]; exact hca) hgr rfl hlab hsat
      hfit
    exact ⟨hsat, hfl, hmem⟩
  · have hfit := (hEqA.spineFit_iff hsat fs).mpr hfs
    obtain ⟨hfl, -, hmem⟩ := posD_tele_fieldMem hin htele (fun i q hq => (hndC i q hq).1) hresB
      (by rw [hhi]; exact hfr) (by rw [hhi]; exact hCP) (by rw [hhi]; exact hca) hgr rfl hlab hsat
      hfit
    exact ⟨hfl, hmem⟩

end ConLeche.Model
