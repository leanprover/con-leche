module

public import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Env.LfpFormer
import ConLeche.Model.Inductives.ContWalk
import ConLeche.Model.Inductives.ContAccRel
import ConLeche.Verify.Level

public section

/-!
# A call landing in an admissible valuation's hole

A call whose walk leaf is a hole of the node's own frame stack lands in
the hole's value at the admissible valuation `σ` (`AdmVal`).  That value
at full arity either holds an element the visit's hypotheses `G` hold of
— where the index spine fits the owner's telescope — or lies below the
TRUE valuation's constant, whose former, applied — where it is not the
point (the caller's: a type) — forces the fit (`former_foldl_mem`).  So
the spine fits and `G` holds:

* `admVal_memberLand` — a member hole, owned by node `0`;
* `admVal_frameLand` — a frame hole, owned by its listed owner.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx NestHole
  BlockParts BlockShape fueledOps PosTree)

universe w

variable {V : Type w} [SetTheory V]

section Land

variable {F : Nat} {envI envC : Env} {mk : EnvModelM V envI} {mpC : EnvModelM V envC}
  {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}

/-- **A call landing in a member hole of an admissible valuation**: the
index spine fits the member's telescope at the prefix's parameters and the
target is an element `G` holds of at node `0` (off the fit the true value,
the member's former at the block's parameters, is its hole value at the
carrier, empty there: `former_app_eq`, `holeVal_foldl_mem`). -/
theorem admVal_memberLand (H : DynCtx F mk mpC ctx d ns) {ψ : Name → Nat} {ρ : Nat → V}
    {xs : List V} (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {own : Nat → Nat} {G : Nat → Nat → V → V → Prop} {prog : List NestHole} {σ : Nat → V}
    (hσ : AdmVal mk mpC ctx d ns ψ ρ xs own G prog σ) {t : Nat} (ht : t < ctx.names.length)
    {is : List V} (his : is.length = ctx.nIdxs.getD t 0)
    (hids : (d.toLfp.ids t ψ).length = ctx.nIdxs.getD t 0)
    (hext : ∀ k, SpineFit (consList (xs.take ctx.nP) ρ) ((d.toLfp.ids t ψ).take k) (is.take k) →
      ∃ ws, SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) ws ∧ ws.take k = is.take k)
    {y : V}
    (hy : y ∈ˢ is.foldl app (σ (ctx.hiAt prog.length - 1 - (ctx.nP + t)))) :
    SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) is ∧
      G 0 t (tupW (d.toLfp.u t ψ) is) y := by
  have hxs' : ctx.nP ≤ xs.length := by rw [H.hnP]; exact hxs
  obtain ⟨hG, hN⟩ := hσ.member t ht is his y hy
  by_cases hfit : SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) is
  · exact ⟨hfit, hG hfit⟩
  · exfalso
    have hy' := hN hfit
    have hkN := lfp_namesLen mpC H.hd0
    have htk' : t < d.toLfp.k := by rw [← hkN, ← H.hnames]; exact ht
    obtain ⟨cv, caps, hf, hlps⟩ := H.hlpsM _ (List.getElem_mem ht)
    have hlen : (ctx.lps.map Level.param).length = cv.levelParams.length := by
      rw [List.length_map, hlps]
    have hc : denote mpC.base2.acval envC ψ xs.length
        (.const (ctx.names[t]'ht) (ctx.lps.map Level.param))
          = some (mpC.base2.acval (ctx.names[t]'ht) ψ) := by
      have h1 := H.htr ψ xs.length _ (denote_const (acval := mk.base2.acval) (φ := ψ)
        (d := xs.length) hf hlen)
      rw [h1, show (ConstantInfo.indInfo cv caps).toConstantVal = cv from rfl, hlps,
        ConLeche.Level.substFn_param_self, H.hag _ (by rw [hf]; rfl)]
    rw [trueVal_member mpC ctx ψ ρ xs H.hparF hxs' prog ht hc] at hy'
    have hmem : d.toLfp.member t = ctx.names[t] := by
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, ← H.hnames, List.getElem?_eq_getElem ht, Option.getD_some]
    rw [← hmem] at hy'
    have hsat : Sat V (d.params ψ).reverse (consList (xs.take d.nP) ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hparams
      rwa [List.append_nil] at this
    have hpl : (xs.take d.nP).length = (d.params ψ).length := hparams.length_eq
    rw [← H.hnP] at hsat hpl
    have hfe := former_app_eq mpC H.hd0 htk' hsat ρ
    have hpl' : (xs.take ctx.nP).length = (d.toLfp.params ψ).length := hpl
    rw [frameIdx_consList hpl' ρ] at hfe
    rw [hfe] at hy'
    -- the true value is not the point: every fitting prefix of the spine
    -- extends (`hext`), and the carrier's fibres are never the point
    have htN : t < d.toLfp.N := Nat.lt_of_lt_of_le htk' (mpC.lfpClause_of_mem H.hd0).kN
    have hne : is.foldl app (d.toLfp.holeVal ψ (consList (xs.take ctx.nP) ρ)
        (d.toLfp.carrier ψ (consList (xs.take ctx.nP) ρ)) t) ≠ pt := by
      unfold LfpDatum.holeVal
      refine holeFam_foldl_ne_pt (fun ws hws => (IsTy_of_mem_strictU (famSpace_app
        ((lfpTuple_mem _ _ _ _ : InTupleSpace (d.toLfp.w ψ) d.toLfp.N
          (d.toLfp.idx ψ (consList (xs.take ctx.nP) ρ))
          (d.toLfp.carrier ψ (consList (xs.take ctx.nP) ρ))) t htN) (tupW_mem hws))).ne_pt)
        (by rw [hids]; exact his) hext
    exact hfit (holeVal_foldl_mem (by rw [hids]; exact his) hne hy').1

/-- **A call landing in a frame hole of an admissible valuation**: the
index spine fits the owner's telescope at its true frame and the target
is an element `G` holds of at the owner (off the fit the true value, the
owner's hole value at its true frame and carrier, is empty:
`trueVal_frameVal`, `holeVal_foldl_mem`). -/
theorem admVal_frameLand (H : DynCtx F mk mpC ctx d ns) {ψ : Name → Nat} {ρ : Nat → V}
    {xs : List V} (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {own : Nat → Nat} {G : Nat → Nat → V → V → Prop} {prog : List NestHole} {σ : Nat → V}
    (hσ : AdmVal mk mpC ctx d ns ψ ρ xs own G prog σ) {i : Nat} {hk : NestHole}
    (hi : prog.reverse[i]? = some hk)
    {is : List V} (his : is.length = hk.nIdx)
    (hext : is.length = ((nlDb mpC d ns (own i)).ids (nlComp mpC d ns (own i) hk.key.cname)
          (nlψ envC ns ψ (own i))).length →
      ∀ k, SpineFit (nlFr mpC ctx d ns ψ ρ xs (own i))
        (((nlDb mpC d ns (own i)).ids (nlComp mpC d ns (own i) hk.key.cname)
          (nlψ envC ns ψ (own i))).take k) (is.take k) →
      ∃ ws, SpineFit (nlFr mpC ctx d ns ψ ρ xs (own i))
        ((nlDb mpC d ns (own i)).ids (nlComp mpC d ns (own i) hk.key.cname)
          (nlψ envC ns ψ (own i))) ws ∧ ws.take k = is.take k)
    {y : V}
    (hy : y ∈ˢ is.foldl app (σ (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i)))) :
    SpineFit (nlFr mpC ctx d ns ψ ρ xs (own i))
        ((nlDb mpC d ns (own i)).ids (nlComp mpC d ns (own i) hk.key.cname)
          (nlψ envC ns ψ (own i))) is ∧
      G (own i) (nlComp mpC d ns (own i) hk.key.cname)
        (tupW ((nlDb mpC d ns (own i)).u (nlComp mpC d ns (own i) hk.key.cname)
          (nlψ envC ns ψ (own i))) is) y := by
  obtain ⟨ho0, hol, hkm, hsuf, -, hland⟩ := hσ.frame i hk hi
  obtain ⟨hG, hN⟩ := hland is his y hy
  by_cases hfit : SpineFit (nlFr mpC ctx d ns ψ ρ xs (own i))
      ((nlDb mpC d ns (own i)).ids (nlComp mpC d ns (own i) hk.key.cname)
        (nlψ envC ns ψ (own i))) is
  · exact ⟨hfit, hG hfit⟩
  · exfalso
    have hy' := hN hfit
    have ho : own i ≠ 0 := by omega
    have hu := getD_mem_of_lt (ns := ns) ho0 hol
    have hxs' : ctx.nP ≤ xs.length := by rw [H.hnP]; exact hxs
    have hfrU := dyn_nlFr H ho hu ψ ρ xs
    unfold nlComp at hfit hext
    rw [show nlDb mpC d ns (own i) = lfpSel mpC d.toLfp (ns.getD (own i - 1) default).key.cname by
        unfold nlDb; rw [ite_eq_right ho],
      show nlψ envC ns ψ (own i) = nodeψ envC ψ (ns.getD (own i - 1) default) by
        unfold nlψ; rw [ite_eq_right ho], hfrU] at hfit hext
    generalize ns.getD (own i - 1) default = u at hu hkm hfit hfrU hsuf hext
    have hsat := dyn_trueVal_sat H ψ ρ xs hparams hxs _ u hu (Nat.le_refl _)
    rw [trueVal_frameVal H ψ ρ xs hxs' hu hsat hi hsuf hkm] at hy'
    -- the arity: the index count is the member's telescope's
    obtain ⟨hD, -, hnN, hkN, -, -, -, -, cv, -, -, -, hlpsOf, -, -, hlenP, -, hg⟩ :=
      dyn_nodeBlock H hu
    have hψ : nodeψ envC ψ u = Level.substFn ψ cv.levelParams u.key.lvls := by
      unfold nodeψ; rw [hlpsOf]
    simp only [ConLeche.grpNews, List.mem_map] at hkm
    obtain ⟨p, hp, rfl⟩ := hkm
    obtain ⟨mm', hmm', hpm⟩ := (hg.2.2 p hp).1
    have harity := grp_arity mk hD hnN hkN H.hcov.find hg (nodeψ envC ψ u) _ hp
    have hpl := (mk.lfpClause_of_mem hD).parsLen mm' hmm' (nodeψ envC ψ u)
    have hlenP' := hlenP (nodeψ envC ψ u)
    simp only at his hfit hy' hext ⊢
    rw [hpm, idxOf_member hnN hkN hmm'] at harity hy' hfit hext
    have hisl : is.length = ((lfpSel mpC d.toLfp u.key.cname).ids mm' (nodeψ envC ψ u)).length := by
      omega
    -- the true value is not the point: every fitting prefix of the spine
    -- extends (`hext`), and the carrier's fibres are never the point
    have hmmN : mm' < (lfpSel mpC d.toLfp u.key.cname).N :=
      Nat.lt_of_lt_of_le hmm' (mk.lfpClause_of_mem hD).kN
    have hne := holeFam_foldl_ne_pt (g := fun ws => app
        ((lfpSel mpC d.toLfp u.key.cname).carrier (nodeψ envC ψ u)
          (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) (trueVal mpC ctx ψ ρ xs u.anc))
          mm') (tupW ((lfpSel mpC d.toLfp u.key.cname).u mm' (nodeψ envC ψ u)) ws))
      (fun ws hws => (IsTy_of_mem_strictU (famSpace_app ((lfpTuple_mem _ _ _ _ : InTupleSpace
        ((lfpSel mpC d.toLfp u.key.cname).w (nodeψ envC ψ u)) (lfpSel mpC d.toLfp u.key.cname).N
        ((lfpSel mpC d.toLfp u.key.cname).idx (nodeψ envC ψ u)
          (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length) (trueVal mpC ctx ψ ρ xs u.anc)))
        ((lfpSel mpC d.toLfp u.key.cname).carrier (nodeψ envC ψ u)
          (keyFrame (nodeDsaI mk ctx ψ u) (ctx.hiAt u.anc.length)
            (trueVal mpC ctx ψ ρ xs u.anc)))) mm' hmmN) (tupW_mem hws))).ne_pt)
      hisl (hext hisl)
    exact hfit (holeVal_foldl_mem hisl hne hy').1

end Land

end ConLeche.Model
