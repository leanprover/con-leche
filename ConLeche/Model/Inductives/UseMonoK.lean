module

public import ConLeche.Model.Inductives.PosDerivMonoK
public import ConLeche.Model.Inductives.UseRelK
import ConLeche.Verify.Inductives.PosDerivInv
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Annot.LfpFormer
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.Annot.LfpHoleOp
import ConLeche.Model.Inductives.SumKit

public section

/-!
# A use of a key-named node (PRIMREC / NESTKN-M3)

`useMonoK`: at a use of the node `lo` (its frame fact `FrameMonoK lo metc`
the IH), spelled `ps` at the user's layout, the used container's carrier
grows between the user's key frames of every related pair.  The node's frame
fact is instantiated along the IMAGE of the user's relation at the node's
base (`useRel`, `holeRelK_use`): the members and parameters are the user's,
each flexible family holds its binding's value.  The node's key frame at the
image IS the user's (`keyFrame_useVal`), given the node's parameters read at
the image as the user's spelling (`hpos`, the match's check).

The lemma is stated over the SEMANTIC facts the use needs (the bindings'
readings and fit, the node's parameters at the image context); how they come
out of the derivation is `UseInstK` (`PosDerivMonoK.lean`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Model.Rules
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantVal IndCaps CheckM NestCtx NestKey LayoutK LayoutOutK
  instPisWith fueledOps)

universe w

variable {V : Type w} [SetTheory V] {env : Env} {φ : Name → Nat}

/-- **A group member of a layout is in the head's recorded block**: the
layout's group is its head and the head's frame mates. -/
theorem layout_member_block {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx}
    (hcov : ContCover mp ctx) {h : Name} {cv₀ : ConstantVal} {caps₀ : IndCaps}
    (hf₀ : env.find? h = some (.indInfo cv₀ caps₀)) (hhd : ctx.names.contains h = false)
    (hq : h ≠ ConLeche.quotName) {n : Name} (hn : n ∈ h :: ConLeche.nestFrameMates ctx h) :
    ∃ D ∈ mp.lfpBlocks, ∃ mm₀, mm₀ < D.k ∧ D.member mm₀ = h ∧ ∃ mm, mm < D.k ∧ D.member mm = n := by
  obtain ⟨D, hD, mm₀, hmm₀, hn₀⟩ := hcov.cover h cv₀ caps₀ hf₀ hhd hq
  have hblkD := hcov.block D hD
  refine ⟨D, hD, mm₀, hmm₀, hn₀, ?_⟩
  rcases List.mem_cons.mp hn with rfl | hn'
  · exact ⟨mm₀, hmm₀, hn₀⟩
  · have hin' := (ConLeche.mem_nestFrameMates hn').1
    have hblkOf : ConLeche.nestBlockOf ctx h = D.names := by
      unfold ConLeche.nestBlockOf
      rw [hcov.find, hf₀]
      exact hblkD.all mm₀ hmm₀ cv₀ caps₀ (by rw [hn₀]; exact hf₀)
    rw [hblkOf] at hin'
    obtain ⟨i, hi, hpi⟩ := List.getElem_of_mem hin'
    refine ⟨i, by rw [lfp_namesLen mp hD] at hi; exact hi, ?_⟩
    unfold LfpDatum.member
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, hpi]

/-- **A use of a node** (see the module docstring). -/
theorem useMonoK {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {ctx : NestCtx} {F : Nat}
    (hcov : ContCover mp ctx) {kn : NestKey} {lo : LayoutOutK} {metc : List Nat}
    (hspec : ConLeche.LayoutSpecK (fueledOps .verified F) env ctx kn lo)
    (hhd : ctx.names.contains kn.cname = false ∧ kn.cname ≠ ConLeche.quotName)
    (ihn : FrameMonoK mp φ ctx lo metc)
    {L : LayoutK} {met : List Nat} {d : Nat} {Δa : List AnnotTerm} {R : FrameRel V}
    (hR : HoleRelK mp.base2 φ ctx L met d Δa R) (hd : L.hi ≤ d) (hΔ : Δa.length = d)
    {n : Name} (hgrp : n ∈ lo.ginfo.map (·.1)) {ps is : List Expr} {wa : AnnotTerm}
    (hwa : denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const n lo.L.lvls) (ps ++ is))
      = some wa)
    (hgr : Graded V Δa wa) (hpsw : ∀ x ∈ ps, Expr.WScoped d x)
    (hnPc : ∃ Lc, ConLeche.nestContainer ctx n = some (ps.length, Lc))
    (hlenD : lo.L.dsF.length = ps.length)
    {psa : List AnnotTerm} (hpsa : DenoteMetaSpine mp.base2.acval env φ d ps psa)
    {xs tya : List AnnotTerm} (hxl : xs.length = lo.L.nF) (htyl : tya.length = lo.L.nF)
    (hsat : ∀ ρ, Sat V Δa ρ → SpineFit (dropV (d - ctx.hiAt 0) ρ) tya (xs.map (interp V ρ)))
    (hmet : ∀ (j : Nat) (key : NestKey) (nI : Nat), j < lo.L.nF → lo.L.fams[j]? = some (key, nI) →
      j ∈ metc → ∀ hj : j < xs.length, HoleOnVal R xs[j] nI)
    (hdsw : ∀ x ∈ lo.L.dsF, Expr.WScoped (ctx.hiAt 0 + lo.L.nF) x ∧ x.looseBVarsBounded 0 = true)
    (hLds : ∀ x ∈ lo.L.dsF, Expr.LeavesBounded x) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mp.base2.acval env φ (ctx.hiAt 0 + lo.L.nF) lo.L.dsF dsa)
    (hCds : ∀ x ∈ lo.L.dsF, CtxOkP mp.base2 φ (ctx.hiAt 0 + lo.L.nF)
      (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)) x)
    (hpos : ∀ ρ, Sat V Δa ρ →
      dsa.map (interp V (useVal xs (d - ctx.hiAt 0) ρ)) = psa.map (interp V ρ)) :
    ∃ D ∈ mp.lfpBlocks, ∃ mm, mm < D.k ∧ D.member mm = n ∧ ∃ cv caps,
      env.find? n = some (.indInfo cv caps) ∧ ∀ ρ ρ', R ρ ρ' →
        FamLe (D.idx (Level.substFn φ cv.levelParams lo.L.lvls) (keyFrame psa d ρ) mm)
          (D.carrier (Level.substFn φ cv.levelParams lo.L.lvls) (keyFrame psa d ρ) mm)
          (D.carrier (Level.substFn φ cv.levelParams lo.L.lvls) (keyFrame psa d ρ') mm) := by
  obtain ⟨⟨nPc, Lc, hqC, -⟩, -, hgrpL, hlvl, hgnames, -, -, -, -, -, -⟩ := hspec
  have h0 : ctx.hiAt 0 ≤ L.hi := by have := hR.hiEq; omega
  have h0d : ctx.hiAt 0 ≤ d := Nat.le_trans h0 hd
  -- the head's block holds the used member
  obtain ⟨cv₀, caps₀, hf₀c⟩ := nestContainer_find hqC
  have hf₀ : env.find? kn.cname = some (.indInfo cv₀ caps₀) := by rw [← hcov.find]; exact hf₀c
  have hnG : n ∈ kn.cname :: ConLeche.nestFrameMates ctx kn.cname := by
    rw [← hgrpL, ← hgnames]; exact hgrp
  obtain ⟨D, hD, mm₀, hmm₀, hn₀, mm, hmm, hn⟩ :=
    layout_member_block mp hcov hf₀ hhd.1 hhd.2 hnG
  obtain ⟨cv, caps, hfc⟩ := (mp.lfp_ok D hD).2.1.1 mm hmm
  rw [hn] at hfc
  -- the block's level parameters
  obtain ⟨lps, hlps, hlenP₀, hcvl₀, hnL⟩ := contBlock_facts mp hcov hD hmm₀
    (by rw [hn₀]; exact hf₀) (by rw [hn₀]; exact hqC)
  have hcvl : cv.levelParams = lps := by
    obtain ⟨cv', caps', hf', h'⟩ := hlps mm hmm
    rw [hn, hfc] at hf'
    obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
    exact h'
  obtain ⟨fa, vs, hfa, -, -⟩ := denoteMeta_mkAppN_inv hwa
  obtain ⟨hul, -⟩ := Rules.denoteMeta_const_arityK hfc hfa
  change lo.L.lvls.length = cv.levelParams.length at hul
  rw [hcvl] at hul
  -- the parameter counts
  obtain ⟨Ln, hqn⟩ := hnPc
  obtain ⟨-, -, hlenPn, -, -⟩ := contBlock_facts mp hcov hD hmm (by rw [hn]; exact hfc)
    (by rw [hn]; exact hqn)
  have hlenPs : ∀ ψ, (D.params ψ).length = ps.length := hlenPn
  -- the node's frame fact along the image of the user's relation
  have hR₀ := holeRelK_use hR hd (L' := lo.L) (metc := metc) hxl hsat hmet
    (fun x hx => (hdsw x hx).1)
  have hΔc : (tya.reverse ++ Δa.drop (d - ctx.hiAt 0)).length = ctx.hiAt 0 + lo.L.nF := by
    simp only [List.length_append, List.length_reverse, List.length_drop, hΔ, htyl]; omega
  have hhead : D.member mm₀ = ((grpOfK lo).headD default).1 := by
    have hnames : (grpOfK lo).map (·.1) = kn.cname :: ConLeche.nestFrameMates ctx kn.cname := by
      rw [grpOfK_names, hgnames, hgrpL]
    cases h : grpOfK lo with
    | nil => rw [h] at hnames; simp at hnames
    | cons p ps' =>
      rw [h] at hnames
      simp only [List.map_cons, List.cons.injEq] at hnames
      simp [hnames.1, hn₀]
  have hkf : ∀ ρ, Sat V Δa ρ →
      keyFrame dsa (ctx.hiAt 0 + lo.L.nF) (useVal xs (d - ctx.hiAt 0) ρ) = keyFrame psa d ρ := by
    intro ρ hρ
    have := keyFrame_useVal (xs := xs) h0d ρ (hpos ρ hρ)
    rwa [hxl] at this
  have hdrop : ∀ ρ : Nat → V, dropV (d - d) ρ = ρ := by
    intro ρ; funext i; simp [dropV]
  have hwa' : denoteMeta mp.base2.acval env φ d
      (Expr.mkAppN (.const (D.member mm) lo.L.lvls) (ps ++ is)) = some wa := by rw [hn]; exact hwa
  have hfit : ∀ σ σ', useRel R xs (d - ctx.hiAt 0) σ σ' →
      Sat V (D.params (Level.substFn φ lps lo.L.lvls)).reverse
        (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) σ) ∧
      Sat V (D.params (Level.substFn φ lps lo.L.lvls)).reverse
        (keyFrame dsa (ctx.hiAt 0 + lo.L.nF) σ') := by
    rintro _ _ ⟨ρ, ρ', hr, rfl, rfl⟩
    obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
    rw [hkf ρ h1, hkf ρ' h2]
    have k1 := keyParamsFit mp hD hmm (by rw [hn]; exact hfc) (Nat.le_refl d) hwa'
      (by rw [hcvl, hlenPs]) hpsw hpsa ρ (hgr ρ h1)
    have k2 := keyParamsFit mp hD hmm (by rw [hn]; exact hfc) (Nat.le_refl d) hwa'
      (by rw [hcvl, hlenPs]) hpsw hpsa ρ' (hgr ρ' h2)
    rw [hdrop, hcvl] at k1 k2
    exact ⟨k1, k2⟩
  obtain ⟨-, -, hle, -⟩ := ihn hcov hD hmm₀ hhead hlps hul hdsw hdsa
    (by rw [hlenPs, hlenD]) (hnL.imp (fun ⟨L', hL', hne⟩ => ⟨_, L', hL', hne⟩) id) hR₀ hΔc hCds hLds hfit
  refine ⟨D, hD, mm, hmm, hn, cv, caps, hfc, fun ρ ρ' hr => ?_⟩
  obtain ⟨h1, h2⟩ := hR.dom ρ ρ' hr
  have hG : InGrp D (grpOfK lo) mm := ⟨hmm, by
    rw [List.contains_iff_mem, grpOfK_names, hn]; exact hgrp⟩
  have := hle _ _ ⟨ρ, ρ', hr, rfl, rfl⟩ mm hG
  rw [hkf ρ h1, hkf ρ' h2, ← hcvl] at this
  exact this

/-- **A container key used at a user grows as a value**, at every spine of
its index count: applied to the key's parameters the container's former is
its hole value at the carrier (`former_app_eq`), the λ-tower over the
member's indices at the key frame (`grp_holeVal_apply`); the index telescope
reads the same at the two key frames (N2, `hte`), so the towers compare as
their leaves at the fitting spines — the carriers' growth (`hle`) — and are
empty off them (`holeFam_fold_mono`). -/
theorem holeOnVal_key {μ : ConLeche.CheckMode} (mp : EnvModelM V μ env) {D : LfpDatum V}
    (hD : D ∈ mp.lfpBlocks) {mm : Nat} (hmm : mm < D.k) {cv : ConstantVal} {caps : IndCaps}
    (hf : env.find? (D.member mm) = some (.indInfo cv caps)) {us : List Level} {d : Nat}
    {ps : List Expr} {ba : AnnotTerm}
    (hba : denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const (D.member mm) us) ps) = some ba)
    (hlenP : ps.length = (D.params (Level.substFn φ cv.levelParams us)).length)
    (hpsw : ∀ x ∈ ps, Expr.WScoped d x) {psa : List AnnotTerm}
    (hpsa : DenoteMetaSpine mp.base2.acval env φ d ps psa)
    {Δa : List AnnotTerm} {R : FrameRel V} (hdom : ∀ ρ ρ', R ρ ρ' → Sat V Δa ρ ∧ Sat V Δa ρ')
    (hgr : Graded V Δa ba)
    (hte : ∀ ρ ρ', R ρ ρ' → TeleEq (keyFrame psa d ρ) (keyFrame psa d ρ')
      (D.ids mm (Level.substFn φ cv.levelParams us)))
    (hle : ∀ ρ ρ', R ρ ρ' →
      FamLe (D.idx (Level.substFn φ cv.levelParams us) (keyFrame psa d ρ) mm)
        (D.carrier (Level.substFn φ cv.levelParams us) (keyFrame psa d ρ) mm)
        (D.carrier (Level.substFn φ cv.levelParams us) (keyFrame psa d ρ') mm)) :
    HoleOnVal R ba (D.ids mm (Level.substFn φ cv.levelParams us)).length := by
  intro ρ ρ' hr as has
  obtain ⟨h1, h2⟩ := hdom ρ ρ' hr
  generalize hψ : Level.substFn φ cv.levelParams us = ψ at hlenP hte hle has ⊢
  obtain ⟨fa, vs, hfa, hsp, rfl⟩ := denoteMeta_mkAppN_inv hba
  obtain ⟨-, rfl⟩ := Rules.denoteMeta_const_arityK hf hfa
  have hv : vs = psa := DenoteMetaSpine.unique hsp hpsa
  subst vs
  change denoteMeta mp.base2.acval env φ d (Expr.mkAppN (.const (D.member mm) us) ps)
    = some (AnnotTerm.mkAppN (mp.base2.acval (D.member mm)
      (Level.substFn φ cv.levelParams us)) psa) at hba
  change Graded V Δa (AnnotTerm.mkAppN (mp.base2.acval (D.member mm)
      (Level.substFn φ cv.levelParams us)) psa) at hgr
  change as.foldl app (interp V ρ (AnnotTerm.mkAppN (mp.base2.acval (D.member mm)
      (Level.substFn φ cv.levelParams us)) psa)) ⊆ˢ as.foldl app (interp V ρ'
      (AnnotTerm.mkAppN (mp.base2.acval (D.member mm) (Level.substFn φ cv.levelParams us)) psa))
  have hdrop : ∀ σ : Nat → V, dropV (d - d) σ = σ := by
    intro σ; funext i; simp [dropV]
  have hs : ∀ σ, Sat V Δa σ → Sat V (D.params ψ).reverse (keyFrame psa d σ) := by
    intro σ hσ
    have := keyParamsFit mp hD hmm hf (Nat.le_refl d) (is := []) (by simpa using hba)
      (by rw [hψ]; exact hlenP) hpsw hpsa σ (hgr σ hσ)
    rwa [hdrop, hψ] at this
  have hpl : psa.length = (D.params ψ).length := by
    rw [← DenoteMetaSpine.length_eq hpsa, hlenP]
  -- the applied former is the λ-tower over the indices at the key frame
  have happ : ∀ σ, Sat V Δa σ → as.foldl app (interp V σ (AnnotTerm.mkAppN
      (mp.base2.acval (D.member mm) (Level.substFn φ cv.levelParams us)) psa))
      = as.foldl app (holeFam (keyFrame psa d σ) (D.ids mm ψ)
          fun bs => app (D.carrier ψ (keyFrame psa d σ) mm) (tupW (D.u mm ψ) bs)) := by
    intro σ hσ
    rw [interp_mkAppN_foldl, ← List.foldl_append, hψ]
    have hfi : psa.map (interp V σ) = frameIdx (D.params ψ).length (keyFrame psa d σ) := by
      unfold keyFrame
      rw [← hpl, ← List.length_map (f := interp V σ), frameIdx_consList']
    rw [hfi, former_app_eq mp hD hmm (hs σ hσ) σ as, ← hfi]
    rw [← hψ] at hs ⊢
    exact grp_holeVal_apply mp hD hpsa (by rw [hψ]; exact hlenP.symm) hmm (hs σ hσ) _ as
  rw [happ ρ h1, happ ρ' h2, ← (hte ρ ρ' hr).holeFam]
  exact holeFam_fold_mono (fun vs hvs => hle ρ ρ' hr _ (tupW_mem hvs)) as has

end ConLeche.Model
