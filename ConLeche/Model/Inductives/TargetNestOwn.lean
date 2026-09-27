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
import ConLeche.Model.Inductives.TargetDefeqTie
import ConLeche.Verify.Inductives.RecNestKTie
import ConLeche.Model.Rules.IotaSoundKit
import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Model.Inductives.TargetCallKey
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Inductives.StructRecKit

public section

/-!
# A strict nested call lands in its body (PRIMREC / NESTKN-NL, the leaves' common half)

The node case of the node lemma reads a pair's class's fields at the STAGE `Y` of its
node and must show that each strict call lands: in `Y` (own leaf), in the admissible
valuation's member / family values, or in a used child's carrier.  `nestCall_body`
composes, at the call's rule frame (`WalkCtx` at `base`):

1. the relocated holes (`walkCtx_reloc`, graded by `relocG_of_home`) valued `hv` — over
   the instance's key frame, the base holes' values and the stage's group values;
2. the field in its relocated crest domain (`relocField_mem`), from a spine fitting the
   HOME crest's tower at the home valuation `consList hv (keyFrame dsa base τ)` (what
   `crest_stageFit` gives at a stage);
3. the call's typing at the relocated depth (`holeCallDep_gen`): the applied field lies in
   the body's reading.

The leaves then read the body: `nestHole_read` (a hole-headed body: the hole's value
applied to the arguments' readings), and at an OWN hole `holeVal_foldl_any` — a hole
value of the stage applied at any parameters of the right count lies in `Y` at the
index readings (a hole value reads its parameters only through their telescope's fit, so
the callee's parameters need not be shown to be the node's).
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
/-- **A strict call at the relocated holes lands in its body** (see the module docstring):
the applied field lies in the reading of the call's body, at the holes valued `hv`. -/
theorem nestCall_body (hμ : μ.verifiedChecks = true) (mp : EnvModelM V μ env) {φ : Name → Nat}
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
    {tele : List (Expr × ConLeche.BinderMeta)} {body : Expr} {fldTy wantTy : Expr}
    (hfld : ConLeche.inferTypeCore μ env F (base + THs.length) fldH = .ok fldTy)
    (hwant : ConLeche.inferTypeCore μ env F (base + THs.length)
      (Expr.mkPisOf tele body) = .ok wantTy)
    (hdeq : ConLeche.isDefEqCore μ env F (base + THs.length) fldH
      (Expr.mkPisOf tele body) = .ok true)
    (hwL : ∀ l ∈ (Expr.mkPisOf tele body).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (holesAt base (relocTys H I base tysH [])).reverse ++ L)
    (htL : ∀ b ∈ tele, ∀ l ∈ b.1.fvarLeaves, Expr.fvar l.1 l.2 ∈ L)
    (bs : List V)
    (hbs : SpineFit τ ((teleDoms mp.base2.acval env φ base [] (tele.map (·.1))).getD []) bs) :
    bs.length = tele.length ∧
      ∃ Xr, denoteMeta mp.base2.acval env φ (base + THs.length + tele.length)
          (body.instantiateList (locOpen (base + THs.length) tele.length) 0) = some Xr ∧
        WellDenoted V (consList bs (consList hv τ)) Xr ∧
        bs.foldl SetTheory.app (fs.getD i pt) ∈ˢ interp V (consList bs (consList hv τ)) Xr := by
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
  exact holeCallDep_gen (mT := mp.base2) (φ := φ) rfl hacl hin hL1
    hW1 hfld hwant hdeq hfldL hwL (a := fs.getD i pt) hmemF bs hbs'

/-- **A hole-headed body, at the relocated holes**: the applied field lies in the hole's
value applied to the arguments' readings (`holeCallDep_head` at hole `base + g`). -/
theorem nestHole_read {mT : EnvModel V env} {φ : Name → Nat} {base k g : Nat} (hg : g < k)
    {ty : Expr} {args : List Expr} {m : Nat} {Xr : AnnotTerm}
    (hXr : denoteMeta mT.acval env φ (base + k + m)
      ((Expr.mkAppN (.fvar (base + g) ty) args).instantiateList (locOpen (base + k) m) 0) = some Xr)
    {hv bs : List V} (hvl : hv.length = k) (hbl : bs.length = m) (τ : Nat → V) {y : V}
    (hy : y ∈ˢ interp V (consList bs (consList hv τ)) Xr) :
    y ∈ˢ (args.map fun x => interp V (consList bs (consList hv τ))
        ((denoteMeta mT.acval env φ (base + k + m)
          (x.instantiateList (locOpen (base + k) m) 0)).getD default)).foldl SetTheory.app
      (hv.getD g pt) := by
  have hval := holeCallDep_head (mT := mT) (φ := φ) (show base + g < base + k by omega) hXr
    hbl (consList hv τ)
  rw [hval] at hy
  rwa [consList_getD_of_lt _ _ _ (by omega), hvl,
    show k - 1 - (base + k - 1 - (base + g)) = g by omega] at hy

/-- The relocated holes: hole `g` is the variable `base + g`. -/
theorem holesAt_getD {base : Nat} {tys : List Expr} {g : Nat} (hg : g < tys.length) :
    (holesAt base tys).getD g default = Expr.fvar (base + g) (tys.getD g default) := by
  simp [holesAt, List.getD_eq_getElem?_getD, List.getElem?_range hg]


/-- **The per-component parameter check reads alike** at every valuation of the relocated
context (`paramsDefEqRK` as run, `params_read_eq`): the callee's abstracted parameters and
the leaf's relocated ones read to one value list. -/
theorem nestParams_tie (hμ : μ.verifiedChecks = true) {mT : EnvModel V env} {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {F E : Nat} {Lh : List Expr} (hL : FvarList E Lh)
    {σ : Nat → V} {Δ : List AnnotTerm} (hW : WalkCtx V mT φ E σ Δ Lh) {cn : Name}
    {dsC dsL : List Expr}
    (hp : ConLeche.paramsDefEqRK (ConLeche.fueledOps μ F) env E cn dsC dsL = .ok ())
    (hCL : ∀ x ∈ dsC, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lh)
    (hLL : ∀ x ∈ dsL, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lh) :
    ∃ dsa₁ dsa₂, dsC.mapM (denoteMeta mT.acval env φ E) = some dsa₁ ∧
      dsL.mapM (denoteMeta mT.acval env φ E) = some dsa₂ ∧
      dsa₁.map (interp V σ) = dsa₂.map (interp V σ) := by
  obtain ⟨hl, hall⟩ := ConLeche.paramsDefEqRK_ok hp
  exact params_read_eq hμ hacl hin hL hW hl fun i a b ha hb => by
    obtain ⟨h1, h2, h3⟩ := hall i a b ha hb
    exact ⟨h1, h2, h3, hCL a (List.mem_of_getElem? ha), hLL b (List.mem_of_getElem? hb)⟩


/-- **A constant-headed body, read** (the key leaf: the container applied to the callee's
parameters and the call's indices): the applied field lies in the constant's value applied
to the arguments' readings. -/
theorem nestConst_read {mT : EnvModel V env} {φ : Name → Nat} {E m : Nat} {n : Name}
    {us : List Level} {args : List Expr} {Xr : AnnotTerm}
    (hXr : denoteMeta mT.acval env φ (E + m)
      ((Expr.mkAppN (.const n us) args).instantiateList (locOpen E m) 0) = some Xr)
    {ci : ConLeche.ConstantInfo} (hf : env.find? n = some ci) (σ : Nat → V) :
    interp V σ Xr
      = (args.map fun x => interp V σ ((denoteMeta mT.acval env φ (E + m)
          (x.instantiateList (locOpen E m) 0)).getD default)).foldl SetTheory.app
        (interp V σ (mT.acval n (Level.substFn φ ci.toConstantVal.levelParams us))) := by
  rw [instantiateList_mkAppN] at hXr
  simp only [Expr.instantiateList] at hXr
  obtain ⟨fa, vs, hfa, hvs, rfl⟩ := denoteMeta_mkAppN_inv hXr
  obtain ⟨-, rfl⟩ := Rules.denoteMeta_const_arityK hf hfa
  rw [interp_mkAppN_foldl, spine_map_getD hvs, List.map_map]
  rfl


/-- A read spine is the `mapM` of its readings. -/
theorem DenoteMetaSpine.mapM_eq {mT : EnvModel V env} {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine mT.acval env φ d as vs →
      as.mapM (denoteMeta mT.acval env φ d) = some vs
  | _, _, .nil => rfl
  | _, _, .cons ha h => by simp [List.mapM_cons, ha, DenoteMetaSpine.mapM_eq h]

set_option maxHeartbeats 1600000 in
/-- **The member leaf's parameter tie**: the match compares the callee's parameters with
the leaf's READ BACK at the instance (`matchRK`), at the rule prefix; a member leaf's
parameters are the home's parameter variables (the hole rule), read back to the
instance's parameters (`rbInstRK_param`) — so at every valuation of the prefix the
callee's parameters read as the instance's. -/
theorem nestMember_params (hμ : μ.verifiedChecks = true) {mT : EnvModel V env} {φ : Name → Nat}
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ) {F E : Nat} {Lh : List Expr}
    (hL : FvarList E Lh) {σ : Nat → V} {Δ : List AnnotTerm} (hW : WalkCtx V mT φ E σ Δ Lh)
    {H : ConLeche.HomeRK} {I : ConLeche.InstRK} {lay : ConLeche.LayRK} {cn : Name}
    (hdl : I.ds.length = H.ctx.nP)
    (hds : ∀ d ∈ I.ds, ∀ l ∈ d.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lh)
    {ps : List Expr} (hpl : ps.length = H.ctx.nP)
    (hps : ∀ i, i < ps.length → ∃ ty, ps[i]? = some (.fvar i ty))
    {dsC : List Expr}
    (hp : ConLeche.paramsDefEqRK (ConLeche.fueledOps μ F) env E cn dsC
      (ps.map (ConLeche.rbInstRK H I lay [])) = .ok ())
    (hCL : ∀ x ∈ dsC, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lh) :
    ∃ dsCa dsa, dsC.mapM (denoteMeta mT.acval env φ E) = some dsCa ∧
      I.ds.mapM (denoteMeta mT.acval env φ E) = some dsa ∧
      dsCa.map (interp V σ) = dsa.map (interp V σ) := by
  have hdsL : ps.map (ConLeche.rbInstRK H I lay []) = I.ds := by
    apply List.ext_getElem (by simp [hpl, hdl])
    intro i h1 h2
    simp only [List.length_map] at h1
    obtain ⟨ty, hty⟩ := hps i h1
    have hpi : ps[i] = .fvar i ty := by
      rw [List.getElem?_eq_getElem h1] at hty; exact Option.some.inj hty
    rw [List.getElem_map, hpi, ConLeche.rbInstRK_param H I lay [] ty (by omega) (by omega)]
  rw [hdsL] at hp
  exact nestParams_tie hμ hacl hin hL hW hp hCL hds

/-- **A relocated term of the home, read under an opened telescope** (the key leaf's
spelling, `callRK` at a container key): at `consList bs (consList hv τ)` it reads as its
HOME reading (at the instance's levels) at the home valuation `consList hv (keyFrame dsa
base τ)` — `relocSlot`'s value equation at all `k` holes, the telescope's lift dropped. -/
theorem nestKey_read (mT : EnvModel V env) {H : ConLeche.HomeRK} {I : ConLeche.InstRK}
    {base k : Nat} {tysP : List Expr} (htl : tysP.length = k)
    (htys : ∀ s, s < k → Expr.WScoped (base + s) (tysP.getD s default))
    (hdl : I.ds.length = H.ctx.nP)
    (hds : ∀ d ∈ I.ds, Expr.WScoped base d ∧ d.looseBVarsBounded 0 = true)
    {φ : Name → Nat} {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mT.acval env φ base I.ds dsa)
    {x : Expr} (hfb : x.fvarsBelow (H.ctx.nP + k)) {XH : AnnotTerm}
    (hXH : denoteMeta mT.acval env (Level.substFn φ H.ctx.lps I.us) (H.ctx.nP + k) x = some XH)
    (hW : Expr.WScoped (base + k) (ConLeche.relocRK H I (holesAt base tysP) x))
    (hb : (ConLeche.relocRK H I (holesAt base tysP) x).looseBVarsBounded 0 = true)
    (m : Nat) {bs hv : List V} (hvl : hv.length = k) (hbl : bs.length = m) (τ : Nat → V) :
    interp V (consList bs (consList hv τ)) ((denoteMeta mT.acval env φ (base + k + m)
        ((ConLeche.relocRK H I (holesAt base tysP) x).instantiateList
          (locOpen (base + k) m) 0)).getD default)
      = interp V (consList hv (keyFrame dsa base τ)) XH := by
  have hdsE := DenoteMetaSpine.lift (m := mT) (φ := φ) (show base ≤ base + k by omega)
    (fun d hd => (hds d hd).1) hdsa
  rw [show base + k - base = k by omega] at hdsE
  obtain ⟨hrd, hval, -⟩ := relocSlot mT (H := H) (I := I) (base := base) (t := k) (tysP := tysP)
    htl htys hdl (fun d hd => ⟨(hds d hd).1.mono (by omega), (hds d hd).2⟩) hdsE hfb hXH
  rw [ConLeche.Expr.instantiateList_eq_self hb,
    denoteMeta_lift mT.acval_closed hW _ (by omega), hrd, Option.map_some, Option.getD_some,
    show base + k + m - (base + k) = bs.length by omega, interp_liftN_consList,
    hval hv τ hvl]
  have hkf := keyFrame_lift dsa base hv τ
  rw [hvl] at hkf
  rw [hkf]


/-- **The instance frame does not depend on the call** (`ιI`): the instance's parameters,
read at any rule depth `base` above their own scope `nP`, give the key frame of their
reading at `nP`, over the valuation below the rule's extra entries. -/
theorem keyFrame_inst {mT : EnvModel V env} {φ : Name → Nat} {nP base : Nat} (hle : nP ≤ base)
    {ds : List Expr} (hds : ∀ d ∈ ds, Expr.WScoped nP d) {dsa0 dsa : List AnnotTerm}
    (hdsa0 : DenoteMetaSpine mT.acval env φ nP ds dsa0)
    (hdsa : DenoteMetaSpine mT.acval env φ base ds dsa) {vs : List V}
    (hvs : vs.length = base - nP) (σ : Nat → V) :
    keyFrame dsa base (consList vs σ) = keyFrame dsa0 nP σ := by
  have hl := DenoteMetaSpine.lift (m := mT) (φ := φ) hle hds hdsa0
  obtain rfl := DenoteMetaSpine.unique hdsa hl
  have := keyFrame_lift dsa0 nP vs σ
  rwa [hvs, show nP + (base - nP) = base by omega] at this


/-- **The key frame of the canonical parameter variables is the valuation itself** (a seed
at the installing block: its instance's parameters are the variables `0, …, n-1`). -/
theorem keyFrame_vars {mT : EnvModel V env} {φ : Name → Nat} {n : Nat} {ds : List Expr}
    (hn : ds.length = n) (hds : ∀ i, i < ds.length → ∃ ty, ds[i]? = some (.fvar i ty))
    {dsa : List AnnotTerm} (hdsa : DenoteMetaSpine mT.acval env φ n ds dsa) (σ : Nat → V) :
    keyFrame dsa n σ = σ := by
  have hl : dsa.length = n := by rw [← DenoteMetaSpine.length_eq hdsa, hn]
  have hmap : dsa.map (interp V σ) = (List.range n).reverse.map σ := by
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [List.length_map] at h1
    obtain ⟨ty, hty⟩ := hds i (by omega)
    have hr := DenoteMetaSpine.getD hdsa default i (by omega)
    rw [List.getD_eq_getElem?_getD, hty, Option.getD_some, denoteMeta_fvar] at hr
    have hdi : dsa[i] = .bvar (n - 1 - i) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some] at hr
      exact (Option.some.inj hr).symm
    simp only [List.getElem_map, hdi, interp_bvar, List.getElem_reverse, List.getElem_range,
      List.length_range]
  unfold keyFrame
  rw [hmap]
  exact consList_range_reverse n σ

end Own

end ConLeche.Model
