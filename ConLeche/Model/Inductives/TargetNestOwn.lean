module

public import ConLeche.Model.Inductives.TargetNestLand
public import ConLeche.Model.Inductives.TargetNestSyn
import ConLeche.Model.Annot.LfpAcc
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.TargetFlat
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Shift
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Inductives.TargetIhSlot

public section

/-!
# A strict nested call at an own hole lands in the stage (PRIMREC / NESTKN-NL, own leaf)

The node case of the node lemma reads a pair's class's fields at the STAGE `Y` of its
node and must show that a call whose leaf is an OWN hole of the node's group lands in `Y`.
`nestOwn_land` composes, at the call's rule frame (`WalkCtx` at `base`):

1. the relocated holes (`walkCtx_reloc`, graded by `relocG_of_home`) valued `hv` — over
   the instance's key frame, the base holes' values and the stage's group values;
2. the field in its relocated crest domain (`relocField_mem`), from a spine fitting the
   HOME crest's tower at the home valuation `consList hv (keyFrame dsa base τ)` (what
   `crest_stageFit` gives at a stage);
3. the call's typing at the relocated depth (`holeCallDep_gen`) and its hole-headed body
   (`holeCallDep_head`);
4. the own hole's value, a hole value of the stage (`LfpDatum.holeVal`), applied at any
   parameters of the right count: `holeVal_foldl_any` — the target is in `Y` at the
   call's index readings (the parameters' values are not needed: a hole value reads its
   parameters only through their telescope's fit).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

universe w

variable {V : Type w} [SetTheory V]

/-- **A hole value applied at ANY parameters of the right count and an index spine**: an
element lies in the stage's component at the indices' tuple (off the telescope the
application is empty). -/
theorem holeVal_foldl_any {D : LfpDatum V} {ψ : Name → Nat} {ρp Y : Nat → V} {mm : Nat}
    {ps is : List V} (hps : ps.length = (D.pars mm ψ).length)
    (his : is.length = (D.ids mm ψ).length) {y : V}
    (hy : y ∈ˢ (ps ++ is).foldl app (D.holeVal ψ ρp Y mm)) :
    y ∈ˢ app (Y mm) (tupW (D.u mm ψ) is) := by
  unfold LfpDatum.holeVal at hy
  rcases holeFam_foldl_full (ρ := shiftE (D.pars mm ψ).length 0 ρp)
      (Fs := D.pars mm ψ ++ D.ids mm ψ) (vs := ps ++ is)
      (fun vs => app (Y mm) (tupW (D.u mm ψ) (vs.drop (D.pars mm ψ).length)))
      (by simp [hps, his]) with ⟨-, heq⟩ | he
  · rw [heq, List.drop_left' hps] at hy
    exact hy
  · rw [he] at hy
    exact absurd hy (not_mem_empty y)

section Own

variable {μ : CheckMode} {env : Env}

set_option maxHeartbeats 8000000 in
/-- **A strict call at an own hole lands in the stage** (see the module docstring). -/
theorem nestOwn_land (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env) {φ : Name → Nat}
    (hin : Rules.RulesInputs V mp.base2 φ) {F : Nat}
    -- the rule's frame
    {base : Nat} {L : List Expr} (hL : FvarList base L) {Δ : List AnnotTerm} {τ : Nat → V}
    (hW : WalkCtx V mp.base2 φ base τ Δ L)
    -- the instance
    {H : ConLeche.HomeRK} {I : ConLeche.InstRK} (hdl : I.ds.length = H.ctx.nP)
    (hds : ∀ d ∈ I.ds, Expr.WScoped base d ∧ d.looseBVarsBounded 0 = true ∧
      ConstsBound env d ∧ ∀ l ∈ d.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mp.base2.acval env φ base I.ds dsa)
    -- the home's holes, their types and values
    (tysH : List Expr) (THs : List AnnotTerm) (hlen : tysH.length = THs.length)
    (hty : ∀ t, t < tysH.length → Expr.WScoped (H.ctx.nP + t) (tysH.getD t default) ∧
      (tysH.getD t default).looseBVarsBounded 0 = true ∧ ConstsBound env (tysH.getD t default) ∧
      denoteMeta mp.base2.acval env (Level.substFn φ H.ctx.lps I.us) (H.ctx.nP + t)
        (tysH.getD t default) = some (THs.getD t default))
    {Ps : List AnnotTerm}
    (hΔ : ∀ σ : Nat → V, Sat V Δ σ →
      (∀ a ∈ dsa, WellDenotedV V σ a) ∧ Sat V Ps (keyFrame dsa base σ))
    (hH : ∀ t, t < THs.length → ∀ ρ : Nat → V, Sat V ((THs.take t).reverse ++ Ps) ρ →
      WellDenotedV V ρ (THs.getD t default))
    (hv : List V) (hvl : hv.length = THs.length)
    (hmem : ∀ t, t < THs.length →
      hv.getD t pt ∈ˢ interp V (consList (hv.take t) (keyFrame dsa base τ)) (THs.getD t default))
    -- the node's crest, read at the home
    {crest : Expr} (hcw : Expr.WScoped (H.ctx.nP + tysH.length) crest)
    (hcb : crest.looseBVarsBounded 0 = true) (hcc : ConstsBound env crest)
    {ds0 : List (Nat × Nat × AnnotTerm)} {X : AnnotTerm}
    (hread : denoteMeta mp.base2.acval env (Level.substFn φ H.ctx.lps I.us)
      (H.ctx.nP + tysH.length) crest = some (mkPisAV ds0 X))
    {fs : List V} (hfitH : SpineFit (consList hv (keyFrame dsa base τ)) (ds0.map (·.2.2)) fs)
    -- the rule's fields
    {xs : List Expr} (hxs : ∀ x ∈ xs, ∃ j ty, x = .fvar j ty ∧ j < base ∧ Expr.WScoped j ty)
    (hxsL : ∀ x ∈ xs, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (hfsl : fs.length = xs.length)
    (hvals : ∀ l, l < xs.length →
      interp V τ ((denoteMeta mp.base2.acval env φ base (xs.getD l default)).getD default)
        = fs.getD l pt)
    {i : Nat}
    -- the call's typing at the relocated holes
    {fldH : Expr}
    (hfldH : ((ConLeche.targetPiDomsWith xs
      (ConLeche.relocRK H I (holesAt base (relocTys H I base tysH [])) crest)).getD [])[i]?
        = some fldH)
    {tele : List (Expr × ConLeche.BinderMeta)} {g : Nat} (hg : g < THs.length)
    {dsC idx : List Expr} {fldTy wantTy : Expr}
    (hfld : ConLeche.inferTypeCore μ env F (base + THs.length) fldH = .ok fldTy)
    (hwant : ConLeche.inferTypeCore μ env F (base + THs.length)
      (Expr.mkPisOf tele (Expr.mkAppN ((holesAt base (relocTys H I base tysH [])).getD g default)
        (dsC ++ idx))) = .ok wantTy)
    (hdeq : ConLeche.isDefEqCore μ env F (base + THs.length) fldH
      (Expr.mkPisOf tele (Expr.mkAppN ((holesAt base (relocTys H I base tysH [])).getD g default)
        (dsC ++ idx))) = .ok true)
    (hwL : ∀ l ∈ (Expr.mkPisOf tele (Expr.mkAppN
        ((holesAt base (relocTys H I base tysH [])).getD g default) (dsC ++ idx))).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (holesAt base (relocTys H I base tysH [])).reverse ++ L)
    (htL : ∀ b ∈ tele, ∀ l ∈ b.1.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    -- the own hole's value: a hole value of the stage
    {D : LfpDatum V} {ψ' : Name → Nat} {ρp Y : Nat → V} {g' : Nat}
    (hhv : hv.getD g pt = D.holeVal ψ' ρp Y g')
    (hdsCl : dsC.length = (D.pars g' ψ').length) (hidxl : idx.length = (D.ids g' ψ').length)
    (bs : List V)
    (hbs : SpineFit τ ((teleDoms mp.base2.acval env φ base [] (tele.map (·.1))).getD []) bs) :
    bs.length = tele.length ∧
      bs.foldl SetTheory.app (fs.getD i pt) ∈ˢ app (Y g') (tupW (D.u g' ψ')
        (idx.map fun x => interp V (consList bs (consList hv τ))
          ((denoteMeta mp.base2.acval env φ (base + THs.length + tele.length)
            (x.instantiateList (locOpen (base + THs.length) tele.length) 0)).getD default))) := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat),
      (mp.base2.acval n ψ).liftN m k = mp.base2.acval n ψ :=
    fun n ψ m k => liftN_eq_self_of_closed (mp.base2.cval_closedL n ψ) k m
  have hsyn := relocTys_syn (env := env) (H := H) (I := I) (base := base) (L := L) tysH hdl hds
    (fun t ht => ⟨(hty t ht).1, (hty t ht).2.1, (hty t ht).2.2.1⟩)
  -- (1) the relocated holes' context
  obtain ⟨hL1, hW1⟩ := walkCtx_reloc mp.base2 hL hW hdl hds hdsa tysH THs hlen
    (fun t ht => hty t ht) hv hvl
    (relocG_of_home (by rw [← DenoteMetaSpine.length_eq hdsa, hdl]) THs hΔ hH)
    (fun t ht => hmem t ht)
  generalize hk : THs.length = k at *
  have hkH : tysH.length = k := hlen
  have hrl : (relocTys H I base tysH []).length = k := by
    simpa [hkH] using relocTys_length H I base tysH []
  generalize hhs : holesAt base (relocTys H I base tysH []) = hs at *
  have hhsl : hs.length = k := by rw [← hhs]; simp [holesAt, hrl]
  -- (2) the instance map at the relocated depth
  have hdsE := DenoteMetaSpine.lift (m := mp.base2) (show base ≤ base + k by omega)
    (fun x hx => (hds x hx).1) hdsa
  rw [show base + k - base = k by omega] at hdsE
  have hx := relocX_ok (H := H) (I := I) (base := base) (E := base + k)
    (tys := relocTys H I base tysH []) (by rw [hrl]) (fun t ht => (hsyn t (by omega)).2.1) hdl
    (fun d hd => ⟨(hds d hd).1.mono (by omega), (hds d hd).2.1⟩) hdsE
  rw [hhs] at hx
  -- the relocated crest: scoped, its leaves the holes' and the frame's
  have hcsyn := relocTy_syn (env := env) (H := H) (I := I) (base := base) (t := k) (L := L)
    (tysP := relocTys H I base tysH []) hrl
    (fun s hs' => by
      obtain ⟨-, hw, -, hc, hl⟩ := hsyn s (by omega)
      refine ⟨hw, hc, fun l hl' => ?_⟩
      have := hl l hl'
      rcases List.mem_append.mp this with h1 | h1
      · refine List.mem_append_left _ (List.mem_reverse.mpr ?_)
        rw [hhs]
        exact (List.take_sublist _ _).subset (List.mem_reverse.mp h1)
      · exact List.mem_append_right _ h1)
    hdl (fun d hd => by
      obtain ⟨h1, h2, h3, h4⟩ := hds d hd
      exact ⟨h1.mono (by omega), h2, h3, h4⟩)
    (by rw [← hkH]; exact hcw) hcb hcc
  rw [hhs] at hcsyn
  obtain ⟨hcL, -, -, hcW⟩ := hcsyn
  -- the field's domain
  obtain ⟨doms, hdoms⟩ : ∃ doms, ConLeche.targetPiDomsWith xs (ConLeche.relocRK H I hs crest)
      = some doms := by
    cases hd : ConLeche.targetPiDomsWith xs (ConLeche.relocRK H I hs crest) with
    | none => rw [hd] at hfldH; simp at hfldH
    | some doms => exact ⟨doms, rfl⟩
  rw [hdoms, Option.getD_some] at hfldH
  have hfldE : doms.getD i default = fldH := by
    rw [List.getD_eq_getElem?_getD, hfldH, Option.getD_some]
  have hi : i < xs.length := by
    have hdl' : doms.length = xs.length := ConLeche.targetPiDomsWith_length _ _ _ hdoms
    have := (List.getElem?_eq_some_iff.mp hfldH).1
    omega
  -- (3) the field lies in its relocated domain
  have hxsE : ∀ x ∈ xs, ∃ j ty, x = .fvar j ty ∧ j < base + k ∧ Expr.WScoped j ty := by
    intro x hx'
    obtain ⟨j, ty, rfl, hj, hw⟩ := hxs x hx'
    exact ⟨j, ty, rfl, by omega, hw⟩
  have hvalsE : ∀ l, l < xs.length →
      interp V (consList hv τ) ((denoteMeta mp.base2.acval env φ (base + k)
        (xs.getD l default)).getD default) = fs.getD l pt := by
    intro l hl
    have hm : xs.getD l default ∈ xs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
      exact List.getElem_mem _
    obtain ⟨j, ty, hj, hjb, -⟩ := hxs _ hm
    rw [← hvals l hl, hj, denoteMeta_fvar, denoteMeta_fvar, Option.getD_some, Option.getD_some,
      interp_bvar, interp_bvar,
      show base + k - 1 - j = (base - 1 - j) + hv.length by rw [hvl]; omega, consList_apply_add]
  have hfit' : SpineFit (substE V (substTau (H.ctx.nP + hs.length) (base + k)
      (relocX H.ctx.nP (dsa.map (AnnotTerm.liftN k · 0)) base (base + k))) 0 (consList hv τ))
      (ds0.map (·.2.2)) fs := by
    rw [hhsl, substE_relocX (by simp [← DenoteMetaSpine.length_eq hdsa, hdl]) (by rw [hvl]) τ]
    have hkf := keyFrame_lift dsa base hv τ
    rw [hvl] at hkf
    rw [hkf]; exact hfitH
  have hmemF := relocField_mem mp.base2 (acval_inst_self mp.base2) hdl hx
    (by rw [hhsl, ← hkH]; exact hcw.fvarsBelow) (by rw [hhsl, ← hkH]; exact hread)
    hcW.fvarsBelow hxsE hdoms hfsl hvalsE hfit' i hi
  rw [hfldE] at hmemF
  -- (4) the call's typing: the applied field lies in the body
  have hfldL : ∀ l ∈ fldH.fvarLeaves, Expr.fvar l.1 l.2 ∈ hs.reverse ++ L := by
    intro l hl
    have hmd : fldH ∈ doms := List.mem_of_getElem? hfldH
    rcases piDomsWith_fvarLeaves xs _ doms hdoms fldH hmd l hl with h1 | ⟨x, hx', h1⟩
    · exact hcL l h1
    · exact List.mem_append_right _ (hxsL x hx' l h1)
  -- the telescope's domains, deepened past the holes
  have htleL : ∀ t ∈ tele.map (·.1), ∀ l ∈ t.fvarLeaves, l.1 < base := by
    intro t ht l hl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact leaf_lt_of_mem hL (fun l hl => htL b hb l hl) l hl
  have hdeep := teleDoms_deepen (acval := mp.base2.acval) (env := env) (φ := φ) hacl k base _ 0
    [] [] htleL (LocList.nil base) (LocList.nil (base + k))
  have hbs' : SpineFit (consList hv τ)
      ((teleDoms mp.base2.acval env φ (base + k) [] (tele.map (·.1))).getD []) bs := by
    rw [hdeep]
    cases hts : teleDoms mp.base2.acval env φ base [] (tele.map (·.1)) with
    | none =>
      rw [hts] at hbs; simp only [Option.map_none, Option.getD_none] at hbs ⊢
      cases bs with
      | nil => trivial
      | cons _ _ => exact hbs.elim
    | some ts =>
      rw [hts, Option.getD_some] at hbs
      rw [Option.map_some, Option.getD_some, spineFit_liftAt, ← hvl, shiftE_consList]; exact hbs
  obtain ⟨hbl, Xr, hXr, -, hfold⟩ := holeCallDep_gen (mT := mp.base2) (φ := φ) rfl hacl hin hL1
    hW1 hfld hwant hdeq hfldL hwL (a := fs.getD i pt) hmemF bs hbs'
  -- (5) the body: the own hole applied
  have hhole : hs.getD g default
      = Expr.fvar (base + g) ((relocTys H I base tysH []).getD g default) := by
    rw [← hhs]
    simp [holesAt, List.getD_eq_getElem?_getD, List.getElem?_range (show g < (relocTys H I base
      tysH []).length by omega)]
  rw [hhole] at hXr
  have hval := holeCallDep_head (mT := mp.base2) (φ := φ) (show base + g < base + k by omega) hXr
    hbl (consList hv τ)
  rw [hval] at hfold
  have hhead : consList hv τ (base + k - 1 - (base + g)) = D.holeVal ψ' ρp Y g' := by
    rw [consList_getD_of_lt _ _ _ (by omega), hvl, show k - 1 - (base + k - 1 - (base + g)) = g by
      omega, hhv]
  rw [hhead, List.map_append] at hfold
  exact ⟨hbl, holeVal_foldl_any (by rw [List.length_map, hdsCl]) (by rw [List.length_map, hidxl])
    hfold⟩

end Own

end ConLeche.Model
