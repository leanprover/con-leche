module

public import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContAccRel
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.StructTele
import ConLeche.Model.Inductives.SumStageCtor
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Verify.Level

public section

/-!
# A call landing in an admissible valuation's hole (lane NESTIND, session 27)

A call whose walk leaf is a hole of the node's own frame stack lands in
the hole's value at the admissible valuation `σ` (`AdmVal`).  That value
at full arity either holds an element the visit's hypotheses `G` hold of
— where the index spine fits the owner's telescope — or lies below the
TRUE valuation's constant, whose former, applied, forces the fit
(`former_foldl_mem`).  So the spine fits and `G` holds:

* `admVal_memberLand` — a member hole, owned by node `0`;
* `admVal_frameLand` — a frame hole, owned by its listed owner.
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

section Land

variable {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI} {mpC : EnvModelM V μ envC}
  {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}

/-- **A call landing in a member hole of an admissible valuation**: the
index spine fits the member's telescope at the prefix's parameters and the
target is an element `G` holds of at node `0`. -/
theorem admVal_memberLand (H : DynCtx F mk mpC ctx d ns) {ψ : Name → Nat} {ρ : Nat → V}
    {xs : List V} (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {own : Nat → Nat} {G : Nat → Nat → V → V → Prop} {prog : List NestHole} {σ : Nat → V}
    (hσ : AdmVal mk mpC ctx d ns ψ ρ xs own G prog σ) {t : Nat} (ht : t < ctx.names.length)
    {is : List V} (his : is.length = ctx.nIdxs.getD t 0)
    (hids : (d.toLfp.ids t ψ).length = ctx.nIdxs.getD t 0) {y : V}
    (hy : y ∈ˢ (xs.take ctx.nP ++ is).foldl app
      (σ (ctx.hiAt prog.length - 1 - (ctx.nP + t)))) :
    SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) is ∧
      G 0 t (tupW (d.toLfp.u t ψ) is) y := by
  have hxs' : ctx.nP ≤ xs.length := by rw [H.hnP]; exact hxs
  have htk : (xs.take ctx.nP).length = ctx.nP := by rw [List.length_take]; omega
  obtain ⟨hG, hN⟩ := hσ.member t ht _ (by rw [List.length_append, htk, his]) y hy
  rw [List.take_left' htk, List.drop_left' htk] at hG hN
  by_cases hfit : SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) is
  · exact ⟨hfit, hG rfl hfit⟩
  · exfalso
    have hy' := hN (fun h => hfit h.2)
    have hkN := lfp_namesLen mpC H.hd0
    have htk' : t < d.toLfp.k := by rw [← hkN, ← H.hnames]; exact ht
    obtain ⟨cv, caps, hf, hlps⟩ := H.hlpsM _ (List.getElem_mem ht)
    have hlen : (ctx.lps.map Level.param).length = cv.levelParams.length := by
      rw [List.length_map, hlps]
    rw [trueVal_member mpC ctx ψ ρ xs hxs' prog ht, dyn_constRead H hf hlen, hlps,
      ConLeche.Level.substFn_param_self, ← H.hag _ (by rw [hf]; rfl)] at hy'
    have hmem : d.toLfp.member t = ctx.names[t] := by
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, ← H.hnames, List.getElem?_eq_getElem ht, Option.getD_some]
    rw [← hmem] at hy'
    have hsat : Sat V (d.params ψ).reverse (consList (xs.take d.nP) ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hparams
      rwa [List.append_nil] at this
    have hpl : (xs.take d.nP).length = (d.params ψ).length := hparams.length_eq
    rw [← H.hnP] at hsat hpl
    have hfi : frameIdx (d.toLfp.params ψ).length (consList (xs.take ctx.nP) ρ) = xs.take ctx.nP :=
      frameIdx_consList hpl ρ
    rw [← hfi] at hy'
    exact hfit (former_foldl_mem mpC H.hd0 htk' hsat ρ (by rw [hids]; exact his) hy').1

/-- **A call landing in a frame hole of an admissible valuation**: the
index spine fits the owner's telescope at its true frame and the target
is an element `G` holds of at the owner. -/
theorem admVal_frameLand (H : DynCtx F mk mpC ctx d ns) {ψ : Name → Nat} {ρ : Nat → V}
    {xs : List V} (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {own : Nat → Nat} {G : Nat → Nat → V → V → Prop} {prog : List NestHole} {σ : Nat → V}
    (hσ : AdmVal mk mpC ctx d ns ψ ρ xs own G prog σ) {i : Nat} {hk : NestHole}
    (hi : prog.reverse[i]? = some hk) {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mk.base2.acval envI ψ (ctx.hiAt prog.length) hk.key.ds dsa)
    {is : List V} (his : is.length + hk.key.ds.length = ConLeche.nestArity ctx hk.key.cname)
    {y : V}
    (hy : y ∈ˢ (dsa.map (interp V σ) ++ is).foldl app
      (σ (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i)))) :
    SpineFit (nlFr mpC ctx d ns ψ ρ xs (own i))
        ((nlDb mpC d ns (own i)).ids (nlComp mpC d ns (own i) hk.key.cname)
          (nlψ envC ns ψ (own i))) is ∧
      G (own i) (nlComp mpC d ns (own i) hk.key.cname)
        (tupW ((nlDb mpC d ns (own i)).u (nlComp mpC d ns (own i) hk.key.cname)
          (nlψ envC ns ψ (own i))) is) y := by
  obtain ⟨ho0, hol, hkm, hfr⟩ := hσ.frame i hk hi
  obtain ⟨hkf, hland⟩ := hfr dsa hdsa
  obtain ⟨hG, hN⟩ := hland is his y hy
  by_cases hfit : SpineFit (nlFr mpC ctx d ns ψ ρ xs (own i))
      ((nlDb mpC d ns (own i)).ids (nlComp mpC d ns (own i) hk.key.cname)
        (nlψ envC ns ψ (own i))) is
  · exact ⟨hfit, hG hfit⟩
  · exfalso
    have hy' := hN hfit
    have ho : own i ≠ 0 := by omega
    have hu := getD_mem_of_lt (ns := ns) ho0 hol
    have hfrU := dyn_nlFr H ho hu ψ ρ xs
    unfold nlComp at hfit
    rw [show nlDb mpC d ns (own i) = lfpSel mpC d.toLfp (ns.getD (own i - 1) default).key.cname by
        unfold nlDb; rw [if_neg ho],
      show nlψ envC ns ψ (own i) = nodeψ envC ψ (ns.getD (own i - 1) default) by
        unfold nlψ; rw [if_neg ho]] at hfit
    rw [← hkf] at hfit
    rw [hfrU] at hkf
    generalize ns.getD (own i - 1) default = u at hu hkm hkf hfrU hfit
    obtain ⟨hD, hwid, hnN, hkN, -, mm, hmm, hmmH, cv, caps, hfc, hlps, hlpsOf, -, hul, hlenP, -,
      hg⟩ := dyn_nodeBlock H hu
    generalize lfpSel mpC d.toLfp u.key.cname = D at *
    have hψ : nodeψ envC ψ u = Level.substFn ψ cv.levelParams u.key.lvls := by
      unfold nodeψ; rw [hlpsOf]
    rw [hψ] at hfit
    -- the hole's member of `D`
    simp only [ConLeche.grpNews, List.mem_map] at hkm
    obtain ⟨p, hp, rfl⟩ := hkm
    obtain ⟨mm', hmm', hpm⟩ := (hg.2 p hp).1
    simp only at hfit hdsa hi his hy'
    rw [hpm, idxOf_member hnN hkN hmm'] at hfit
    obtain ⟨cv', caps', hf', hl'⟩ := hlps mm' hmm'
    have hlen : u.key.lvls.length = cv'.levelParams.length := by rw [hl', hul]
    rw [trueVal_frame mpC ctx ψ ρ xs (by rw [H.hnP]; exact hxs) prog hi] at hy'
    simp only at hy'
    rw [hpm, dyn_constRead H hf' hlen, hl', ← H.hag _ (by rw [hf']; rfl)] at hy'
    -- the owner's frame satisfies the telescope (K.52)
    have hsat := nodeKeyFit mk (H.hΔ0 ψ) (H.hok u hu) (H.hsem u hu ψ) hD hmm hmmH hfc
      (hlenP _).symm (dyn_dsaI H hu ψ) _
      (dyn_trueVal_sat H ψ ρ xs hparams u.anc (dyn_stackFound H hu))
    rw [← hkf] at hsat
    -- the index count: the kernel's arity is the member's telescope
    have harity := grp_arity mk hD hnN hkN H.hcov.find hg
      (Level.substFn ψ cv.levelParams u.key.lvls) _ hp
    rw [hpm, idxOf_member hnN hkN hmm'] at harity
    have hpl := (mk.lfpClause_of_mem hD).parsLen mm' hmm' (Level.substFn ψ cv.levelParams u.key.lvls)
    have hdl := DenoteMetaSpine.length_eq hdsa
    have hlenP' := hlenP (Level.substFn ψ cv.levelParams u.key.lvls)
    have hpl2 : (D.pars mm' (Level.substFn ψ cv.levelParams u.key.lvls)).length = dsa.length := by
      rw [hpl, hlenP', hdl]
    have hisl : is.length = (D.ids mm' (Level.substFn ψ cv.levelParams u.key.lvls)).length := by
      rw [hpl2] at harity
      rw [hdl, hpm, harity] at his
      omega
    have hfi : frameIdx (D.params (Level.substFn ψ cv.levelParams u.key.lvls)).length
        (keyFrame dsa (ctx.hiAt prog.length) (trueVal mpC ctx ψ ρ xs prog))
        = dsa.map (interp V (trueVal mpC ctx ψ ρ xs prog)) :=
      frameIdx_consList (by rw [List.length_map]; omega) _
    rw [← hfi] at hy'
    exact hfit (former_foldl_mem mpC (H.hsub D hD) hmm' hsat ρ hisl hy').1

end Land

end ConLeche.Model
