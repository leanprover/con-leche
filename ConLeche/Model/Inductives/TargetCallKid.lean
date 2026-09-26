module

public import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContAccRel
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.PosDerivNodes
import ConLeche.Model.Annot.BitInst
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Verify.Level

public section

/-!
# The walked kid's admissible valuation

A container field of a derived node `u`'s constructor lands at a kid `u'`
of `u` (the parent pointer of `u'`'s occurrence is `u`'s, `ParentPtrs`),
whose frame stack is `u`'s group's holes on top of `u`'s stack.  At an
admissible visit `(G, ρ')` of `u` (`ρ'` the key read at an admissible
valuation `σ`) and a hole tuple `Y`, the walk valuation — `u`'s group
holes at `Y`'s hole values on top of `σ` — is ADMISSIBLE for `u'` at the
visit's hypotheses extended by the caller's tuple (`addOwn G b … Y`):

* `holeOwner_kid` — a kid's hole owners: its parent's below the parent's
  stack, the parent itself on the parent's group;
* `admVal_kid` — the admissible valuation.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx NestHole
  BlockParts BlockShape fueledOps PosTree)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-- **A kid's hole owners** (`par b' = b`, an earlier position): below its
parent's stack, the parent's owner; on the parent's group, the parent. -/
theorem holeOwner_kid {ns : List PosTree} {par : Nat → Nat} {b b' : Nat} (hpar : par b' = b)
    (hlt : b < b') {u : PosTree} (hub : ns.getD (b - 1) default = u) (i : Nat) :
    holeOwner ns par b' i = if i < u.anc.length then holeOwner ns par b i else b := by
  unfold holeOwner
  show (if i < (ns.getD (par b' - 1) default).anc.length ∧ par b' < b' then
      holeOwnerF ns par b' (par b') i else par b') = _
  rw [hpar, hub]
  by_cases hi : i < u.anc.length
  · rw [if_pos ⟨hi, hlt⟩, if_pos hi]
    exact holeOwnerF_fuel _ _ _ _ hlt (by omega)
  · rw [if_neg (fun h => hi h.1), if_neg hi]

section Kid

variable {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI} {mpC : EnvModelM V μ envC}
  {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}

set_option maxHeartbeats 4000000 in
/-- **The walked kid's admissible valuation** (see the module docstring), at
any owner function that is the parent's below its stack and the parent on
its group (`holeOwner_kid`: a kid's `holeOwner`; the parent's own
constructor stack's owners). -/
theorem admVal_kid (H : DynCtx F mk mpC ctx d ns) {ψ : Name → Nat} {ρ : Nat → V} {xs : List V}
    {par : Nat → Nat} {b : Nat} (hb0 : 0 < b) (hbl : b ≤ ns.length) {u : PosTree}
    (hub : ns.getD (b - 1) default = u)
    {G : Nat → Nat → V → V → Prop} {σ : Nat → V}
    (hσ : AdmVal mk mpC ctx d ns ψ ρ xs (holeOwner ns par b) G u.anc σ) {Y : Nat → V}
    (hsatN : Sat V ((grpTys mk.base2 ψ u.grp).reverse
        ++ stackCtx mk.base2 ψ ctx u.anc (d.holeCtx ψ).reverse)
      (consList (grpVals (lfpSel mpC d.toLfp u.key.cname) (nodeψ envC ψ u) u.grp
        (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) σ) Y) σ))
    {own' : Nat → Nat}
    (hown : ∀ i, own' i = if i < u.anc.length then holeOwner ns par b i else b) {u' : PosTree}
    (hanc : u'.anc = (ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse
      ++ u.anc) :
    AdmVal mk mpC ctx d ns ψ ρ xs own'
      (addOwn G b (nlDb mpC d ns b).N
        ((nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) Y) u'.anc
      (consList (grpVals (lfpSel mpC d.toLfp u.key.cname) (nodeψ envC ψ u) u.grp
        (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) σ) Y) σ) := by
  classical
  have hu : u ∈ ns := hub ▸ getD_mem_of_lt hb0 hbl
  have hb00 : b ≠ 0 := by omega
  have hok := H.hok u hu
  obtain ⟨hD, hwid, hnN, hkN, hall, mm, hmm, hmmH, cv0, caps0, hfc0, hlps, hlpsOf, hndl, hul,
    hlenP, -, hg⟩ := dyn_nodeBlock H hu
  have hψ : nodeψ envC ψ u = Level.substFn ψ cv0.levelParams u.key.lvls := by
    unfold nodeψ; rw [hlpsOf]
  have hds := posNodeOk_dsAnc hok
  have hdsa := dyn_dsaI H hu ψ
  have hps : ConLeche.ProgScoped ctx u.anc := hok.2.2.2.1
  have hnlDb : nlDb mpC d ns b = lfpSel mpC d.toLfp u.key.cname := by
    unfold nlDb; rw [if_neg hb00, hub]
  have hnlψ : nlψ envC ns ψ b = nodeψ envC ψ u := by
    unfold nlψ; rw [if_neg hb00, hub]
  have hnlFr : nlFr mpC ctx d ns ψ ρ xs b
      = keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) (trueVal mpC ctx ψ ρ xs u.anc) := by
    rw [dyn_nlFr H hb00 (hub ▸ getD_mem_of_lt hb0 hbl) ψ ρ xs, hub]
  rw [hnlDb, hnlψ, hnlFr]
  have hGl := grpNews_length u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp
  generalize hdsaE : nodeDsaI mk ctx ψ u = dsaU at hdsa hsatN ⊢
  generalize hρ' : keyFrame dsaU (ctx.hiAt u.anc.length) σ = ρ' at hsatN ⊢
  generalize hDdef : lfpSel mpC d.toLfp u.key.cname = D at *
  rw [hψ] at hsatN ⊢
  generalize hψu : Level.substFn ψ cv0.levelParams u.key.lvls = ψu at *
  have hVl := grpVals_length D ψu u.grp ρ' Y
  generalize hGV : grpVals D ψu u.grp ρ' Y = GV at hsatN hVl ⊢
  -- the kid's true valuation and depth
  have hhi' : ctx.hiAt u'.anc.length = ctx.hiAt u.anc.length + u.grp.length := by
    rw [hanc, List.length_append, List.length_reverse, hGl]
    simp only [ConLeche.NestCtx.hiAt]; omega
  generalize hVS : ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length)
    u.grp).reverse.reverse.map fun h =>
      (denoteMeta mpC.base2.acval envC ψ 0 (.const h.key.cname h.key.lvls)).getD default).map
        (interp V ρ) = VS
  have hVSl : VS.length = u.grp.length := by rw [← hVS]; simp [hGl]
  have htv : trueVal mpC ctx ψ ρ xs u'.anc = consList VS (trueVal mpC ctx ψ ρ xs u.anc) := by
    rw [hanc, trueVal_append, hVS]
  have hσN : ∀ q, consList GV σ (q + u.grp.length) = σ q := fun q => by
    rw [← hVl]; exact consList_apply_add GV σ q
  have htvq : ∀ q, trueVal mpC ctx ψ ρ xs u'.anc (q + u.grp.length)
      = trueVal mpC ctx ψ ρ xs u.anc q := fun q => by
    rw [htv, ← hVSl]; exact consList_apply_add VS _ q
  have hnh : ctx.nP ≤ ctx.hiAt 0 := by simp only [ConLeche.NestCtx.hiAt]; omega
  have hA0 : ctx.hiAt 0 ≤ ctx.hiAt u.anc.length := by simp only [ConLeche.NestCtx.hiAt]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- the stack context
    rw [hanc, stackCtx_frame H.hcov.find
      (grpWf_ty mk hD hnN hkN H.hcov.find hlps hndl hul hds hdsa (hlenP _) hg)]
    exact hsatN
  · -- off the holes: the parameters and the frame below
    intro p hp
    rw [hhi'] at hp
    by_cases hpg : p < u.grp.length
    · exfalso; exact hp ⟨by omega, by omega, by omega⟩
    · obtain ⟨q, rfl⟩ : ∃ q, p = q + u.grp.length := ⟨p - u.grp.length, by omega⟩
      rw [hσN, htvq]
      exact hσ.agree q fun h => hp ⟨by have := h.1; omega, by have := h.2.1; omega,
        by have := h.2.2; omega⟩
  · -- a member hole: the parent's
    intro t ht as has y hy
    have hlt0 : ctx.nP + t < ctx.hiAt 0 := by simp only [ConLeche.NestCtx.hiAt]; omega
    have hidx : ctx.hiAt u'.anc.length - 1 - (ctx.nP + t)
        = (ctx.hiAt u.anc.length - 1 - (ctx.nP + t)) + u.grp.length := by
      rw [hhi']; omega
    rw [hidx, hσN] at hy
    obtain ⟨h1, h2⟩ := hσ.member t ht as has y hy
    refine ⟨fun a c => Or.inl (h1 a c), fun hn => ?_⟩
    rw [hidx, htvq]; exact h2 hn
  · -- a frame hole
    intro i hk hi
    rw [hanc, List.reverse_append, List.reverse_reverse] at hi
    rw [hown i]
    by_cases hin : i < u.anc.length
    · -- below the parent's group: the parent's owner
      rw [if_pos hin]
      rw [List.getElem?_append_left (by simpa using hin)] at hi
      obtain ⟨h0, hl, hm, hfr⟩ := hσ.frame i hk hi
      refine ⟨h0, hl, hm, fun dsa' hdsa' => ?_⟩
      have hws : ∀ x ∈ hk.key.ds, Expr.WScoped (ctx.hiAt u.anc.length) x := hps i hk hi
      obtain ⟨dsa, hdsaA, rfl⟩ := DenoteMetaSpine.unlift (m := mk.base2) (by rw [hhi']; omega)
        hws hdsa'
      obtain ⟨hkf, hland⟩ := hfr dsa hdsaA
      have hlen' : ctx.hiAt u'.anc.length - ctx.hiAt u.anc.length = VS.length := by
        rw [hhi', hVSl]; omega
      have hlenG : ctx.hiAt u'.anc.length - ctx.hiAt u.anc.length = GV.length := by
        rw [hhi', hVl]; omega
      refine ⟨?_, fun is his y hy => ?_⟩
      · rw [htv, hlen', show ctx.hiAt u'.anc.length = ctx.hiAt u.anc.length + VS.length by
          rw [hhi', hVSl], keyFrame_lift]
        exact hkf
      · have hlt1 : ctx.hiAt 0 + i < ctx.hiAt u.anc.length := by
          simp only [ConLeche.NestCtx.hiAt] at hA0 ⊢; omega
        have hidx : ctx.hiAt u'.anc.length - 1 - (ctx.hiAt 0 + i)
            = (ctx.hiAt u.anc.length - 1 - (ctx.hiAt 0 + i)) + u.grp.length := by
          rw [hhi']; omega
        rw [hidx, hσN, List.map_map, hlenG] at hy
        have hmapσ : List.map (interp V (consList GV σ) ∘ fun x => x.liftN GV.length 0) dsa
            = dsa.map (interp V σ) :=
          List.map_congr_left fun a _ => interp_liftN_consList GV σ a
        rw [hmapσ] at hy
        obtain ⟨g1, g2⟩ := hland is his y hy
        refine ⟨fun f => Or.inl (g1 f), fun nf => ?_⟩
        have hmapT : List.map (interp V (trueVal mpC ctx ψ ρ xs u'.anc)) (dsa.map
            fun x => x.liftN (ctx.hiAt u'.anc.length - ctx.hiAt u.anc.length) 0)
            = dsa.map (interp V (trueVal mpC ctx ψ ρ xs u.anc)) := by
          rw [List.map_map, htv, hlen']
          exact List.map_congr_left fun a _ => interp_liftN_consList VS _ a
        rw [hmapT, hidx, htvq]
        exact g2 nf
    · -- on the parent's group: the parent
      rw [if_neg hin]
      have hge : u.anc.length ≤ i := Nat.le_of_not_lt hin
      rw [List.getElem?_append_right (by simpa using hge), List.length_reverse] at hi
      have hkmem : hk ∈ ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp :=
        List.mem_of_getElem? hi
      have hil : i - u.anc.length < u.grp.length := by
        have := (List.getElem?_eq_some_iff.mp hi).1; rwa [hGl] at this
      have hpi : u.grp[i - u.anc.length] ∈ u.grp := List.getElem_mem _
      have hkeq : hk = NestHole.mk ⟨(u.grp[i - u.anc.length]).1, u.key.lvls, u.key.ds⟩
          (ctx.hiAt u.anc.length) := by
        simp only [ConLeche.grpNews, List.getElem?_map, List.getElem?_eq_getElem hil,
          Option.map_some, Option.some.injEq] at hi
        exact hi.symm
      refine ⟨hb0, hbl, by rw [hub]; exact hkmem, fun dsa' hdsa' => ?_⟩
      have hkf := dyn_ownerFrame H ψ ρ xs hb00 (hub ▸ hu) (prog := u'.anc) (X := [])
        (by rw [hub, hanc, List.nil_append]) (by rw [hub]; exact hkmem) hdsa'
      refine ⟨hkf, fun is his y hy => ?_⟩
      rw [hnlFr, hdsaE]
      -- the hole's value: the group's
      obtain ⟨mm', hmm', hpm, hidx, -, -, -, -, -, hte⟩ :=
        grpMember mk hD hnN hkN H.hcov.find hlps hndl hul hds hdsa (hlenP _) hg hpi
      rw [hψu] at hte
      have hkk : ctx.hiAt u'.anc.length - 1 - (ctx.hiAt 0 + i) < GV.length := by
        rw [hhi', hVl]; simp only [ConLeche.NestCtx.hiAt] at hA0 ⊢; omega
      have hval : consList GV σ (ctx.hiAt u'.anc.length - 1 - (ctx.hiAt 0 + i))
          = D.holeVal ψu ρ' Y mm' := by
        rw [consList_apply_lt GV σ _ hkk,
          show GV.length - 1 - (ctx.hiAt u'.anc.length - 1 - (ctx.hiAt 0 + i))
            = i - u.anc.length by rw [hhi', hVl]; simp only [ConLeche.NestCtx.hiAt]; omega,
          ← hGV]
        simp only [grpVals, List.getElem?_map, List.getElem?_eq_getElem hil, Option.map_some,
          Option.getD_some, hidx]
      rw [hval] at hy
      -- the key's parameters, read at the walk valuation, are the key frame's
      have hdsaL := DenoteMetaSpine.lift (m := mk.base2) (φ := ψ)
        (h := ctx.hiAt u.anc.length) (D := ctx.hiAt u'.anc.length) (by rw [hhi']; omega)
        (fun x hx => (hds x hx).1) hdsa
      rw [hkeq] at hdsa'
      obtain rfl := DenoteMetaSpine.unique hdsa' hdsaL
      have hlenG : ctx.hiAt u'.anc.length - ctx.hiAt u.anc.length = GV.length := by
        rw [hhi', hVl]; omega
      rw [List.map_map, hlenG] at hy
      have hmapσ : List.map (interp V (consList GV σ) ∘ fun x => x.liftN GV.length 0) dsaU
          = dsaU.map (interp V σ) :=
        List.map_congr_left fun a _ => interp_liftN_consList GV σ a
      have hpl := (mk.lfpClause_of_mem hD).parsLen mm' hmm' ψu
      have hdl := DenoteMetaSpine.length_eq hdsa
      have hlenP' := hlenP ψu
      rw [← hψu] at hlenP'
      rw [hψu] at hlenP'
      have hfi : frameIdx (D.params ψu).length ρ' = dsaU.map (interp V σ) := by
        rw [← hρ']
        exact frameIdx_consList (by rw [List.length_map]; omega) _
      rw [hmapσ, ← hfi] at hy
      -- the arity
      have harity := grp_arity mk hD hnN hkN H.hcov.find hg ψu _ hpi
      rw [hidx] at harity
      have hisl : is.length = (D.ids mm' ψu).length := by
        rw [hkeq] at his; simp only at his; omega
      have hsatρ' : Sat V (D.params ψu).reverse ρ' := by
        rw [← hρ', ← hψu]
        exact nodeKeyFit mk (H.hΔ0 ψ) hok (H.hsem u hu ψ) (hDdef ▸ hD) hmm hmmH hfc0 (hlenP _).symm
          (hdsaE ▸ dyn_dsaI H hu ψ) σ hσ.sat
      obtain ⟨hfitA, hyY⟩ := holeVal_foldl_mem (mk.lfpClause_of_mem hD) hmm' hsatρ' hisl hy
      -- the fit at the TRUE frame (the index telescope sees no hole)
      have hfitT : SpineFit (keyFrame dsaU (ctx.hiAt u.anc.length)
          (trueVal mpC ctx ψ ρ xs u.anc)) (D.ids mm' ψu) is := by
        rw [← (hte σ (trueVal mpC ctx ψ ρ xs u.anc) hσ.agree).spineFit is, hρ']
        exact hfitA
      have hcomp : nlComp mpC d ns b hk.key.cname = mm' := by
        unfold nlComp; rw [hnlDb, hkeq]; exact hidx
      rw [hcomp, hnlDb, hnlψ, hψ]
      refine ⟨fun _ => Or.inr ⟨rfl, Nat.lt_of_lt_of_le hmm' (mk.lfpClause_of_mem hD).kN,
        tupW_mem hfitT, hyY⟩, fun hnf => absurd hfitT hnf⟩

/-- **Below the frames**: an admissible valuation of a stack, its frame
holes dropped, is admissible for the empty stack (a cache hit's). -/
theorem AdmVal.drop {ψ : Name → Nat} {ρ : Nat → V} {xs : List V} {own : Nat → Nat}
    {G : Nat → Nat → V → V → Prop} {prog : List NestHole} {σ : Nat → V}
    (hσ : AdmVal mk mpC ctx d ns ψ ρ xs own G prog σ) (own' : Nat → Nat) :
    AdmVal mk mpC ctx d ns ψ ρ xs own' G [] (fun q => σ (q + prog.length)) := by
  generalize hVS : ((prog.reverse.map fun h =>
      (denoteMeta mpC.base2.acval envC ψ 0 (.const h.key.cname h.key.lvls)).getD default).map
        (interp V ρ)) = VS
  have hVSl : VS.length = prog.length := by rw [← hVS]; simp
  have htv : trueVal mpC ctx ψ ρ xs prog = consList VS (trueVal mpC ctx ψ ρ xs []) := by
    have := trueVal_append mpC ctx ψ ρ xs prog []
    rw [List.append_nil] at this
    rw [this, hVS]
  have htvq : ∀ q, trueVal mpC ctx ψ ρ xs prog (q + prog.length)
      = trueVal mpC ctx ψ ρ xs [] q := fun q => by
    rw [htv, ← hVSl]; exact consList_apply_add VS _ q
  have hhi : ctx.hiAt prog.length = ctx.hiAt 0 + prog.length := by
    simp only [ConLeche.NestCtx.hiAt]; omega
  refine ⟨?_, ?_, ?_, fun i hk hi => by simp at hi⟩
  · have := Sat_drop hσ.sat prog.length
    rwa [stackCtx_drop] at this
  · intro p hp
    show σ (p + prog.length) = _
    rw [← htvq]
    simp only [List.length_nil] at hp
    refine hσ.agree _ fun h => hp ?_
    obtain ⟨h1, h2, h3⟩ := h
    rw [hhi] at h1 h2 h3
    exact ⟨by omega, by omega, by omega⟩
  · intro t ht as has y hy
    have hlt0 : ctx.nP + t < ctx.hiAt 0 := by simp only [ConLeche.NestCtx.hiAt]; omega
    have hidx : ctx.hiAt ([] : List NestHole).length - 1 - (ctx.nP + t) + prog.length
        = ctx.hiAt prog.length - 1 - (ctx.nP + t) := by
      simp only [List.length_nil]; omega
    rw [hidx] at hy
    obtain ⟨h1, h2⟩ := hσ.member t ht as has y hy
    refine ⟨h1, fun hn => ?_⟩
    rw [← htvq, hidx]
    exact h2 hn

end Kid

end ConLeche.Model
