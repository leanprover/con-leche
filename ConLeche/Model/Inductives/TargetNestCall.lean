module

import ConLeche.Model.Inductives.TargetCallGen
public import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Inductives.TargetRecRead
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Model.Inductives.TargetCallKey
import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Annot.BitLemmas
import ConLeche.Model.Inductives.BlockRecRule
import ConLeche.Semantics.Tower.TowerKit
public import ConLeche.Kernel.Inductives.RecNestK
import ConLeche.Model.Levels
import ConLeche.Model.Annot.BitSubstFvars
import ConLeche.Semantics.SubstAV
import ConLeche.Model.Annot.BitRename
import ConLeche.Verify.Inductives.NestCallSyn
import ConLeche.Model.Inductives.ContSubst
public import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Semantics.Tower.BlockTower
import ConLeche.Model.Inductives.BlockHoleValid
import ConLeche.Model.Annot.Valid
import ConLeche.Verify.Level

public section

/-!
# A call typed at DEPENDENTLY typed holes (PRIMREC / NESTKN-NL, piece (ii))

`holeCall_gen` (`TargetFlatCall.lean`) reads a call typed at the installing
block's member holes, each typed by a CLOSED former type.  The nested route
(`Kernel/Inductives/RecNestK.lean`, `callRK`) types a strict call at a node's
RELOCATED holes (`relocHolesRK`): the home's members, the node's flexible
families and its own group, each typed by its home type under the instance
map — over the rule's frame AND the earlier holes.  `holeCallDep_gen` states
the call landing once, generic in the hole context: given the walk's context
extended by the holes at a valuation `hv` (`WalkCtx` at `D + k`, however it was
built — for the nested route, from an admissible valuation of the node), a
field `a` in the reading of `fld` there, `fld` typed and defeq to
`∀ tele, body` at `D + k` (the call's typing, `TypingRunRK`), and a spine `bs`
fitting the telescope's domains at `D + k`: the applied field lies in the
body's reading, the telescope opened by `bs`.

`holeCallDep_head` decodes the body when it is a HOLE applied to arguments
(the member, family and own-hole leaves): the applied field lies in the hole's
value applied to the arguments' readings.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Gen

variable {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}

set_option maxHeartbeats 4000000 in
/-- **A call typed at dependently typed holes lands in the body** (see the
module docstring). -/
theorem holeCallDep_gen (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F E : Nat} {Lh : List Expr} (hL : FvarList E Lh)
    {σ : Nat → V} {Δ : List AnnotTerm} (hW : WalkCtx V mT φ E σ Δ Lh)
    {fld body : Expr} {tele : List (Expr × ConLeche.BinderMeta)} {fldTy wantTy : Expr}
    (hfld : ConLeche.inferTypeCore μ envT F E fld = .ok fldTy)
    (hwant : ConLeche.inferTypeCore μ envT F E (Expr.mkPisOf tele body) = .ok wantTy)
    (hdeq : ConLeche.isDefEqCore μ envT F E fld (Expr.mkPisOf tele body) = .ok true)
    (hfldL : ∀ l ∈ fld.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lh)
    (hwL : ∀ l ∈ (Expr.mkPisOf tele body).fvarLeaves, Expr.fvar l.1 l.2 ∈ Lh)
    {a : V} (ha : ∀ Aty : AnnotTerm, denoteMeta mT.acval envT φ E fld = some Aty →
      a ∈ˢ interp V σ Aty)
    (bs : List V)
    (hbs : SpineFit σ ((teleDoms mT.acval envT φ E [] (tele.map (·.1))).getD []) bs) :
    bs.length = tele.length ∧
      ∃ Xr, denoteMeta mT.acval envT φ (E + tele.length)
          (body.instantiateList (locOpen E tele.length) 0) = some Xr ∧
        WellDenoted V (consList bs σ) Xr ∧
        bs.foldl SetTheory.app a ∈ˢ interp V (consList bs σ) Xr := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  have hWS := hW.2.2.2.2.1
  -- the field's type: framed, read, graded
  have hAb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge hfld)
  obtain ⟨Aty, hAty⟩ := acceptedReads_of mT φ hfld (wscoped_of_leaves_mem hL _ hfldL) hAb
    (fun l hl => hWS _ (hfldL l hl))
  obtain ⟨hFrA, hCA, hGA⟩ := WalkCtx.subjOkL hacl1 hin hL hW hfldL hAb hAty
    ⟨_, Rules.inferTypeCore_bridge hfld⟩
  -- the wanted type: framed, read, graded
  have hWb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge hwant)
  obtain ⟨WA, hWA⟩ := acceptedReads_of mT φ hwant (wscoped_of_leaves_mem hL _ hwL) hWb
    (fun l hl => hWS _ (hwL l hl))
  obtain ⟨hFrW, hCW, hGW⟩ := WalkCtx.subjOkL hacl1 hin hL hW hwL hWb hWA
    ⟨_, Rules.inferTypeCore_bridge hwant⟩
  -- the call's typing: one reading
  have heq := Rules.defeq_sound hin (Rules.isDefEqCore_bridge hdeq) hFrA hFrW hCA hCW hAty hWA
    hGA hGW _ hW.2.1
  have hfW : a ∈ˢ interp V σ WA := by rw [← heq]; exact ha Aty hAty
  -- the wanted type: a Π-tower over the telescope
  have hWA' := hWA
  rw [← ConLeche.Expr.instantiateList_nil (Expr.mkPisOf _ _) 0,
    show E = E + 0 from rfl] at hWA'
  obtain ⟨ds', Xr, os', rfl, hdoms', -, hos', hXr⟩ :=
    denoteMeta_mkPisOf (acval := mT.acval) (env := envT) (φ := φ) (D := E) _ _ 0 []
      _ (LocList.nil _) hWA'
  rw [Nat.zero_add] at hos' hXr
  rw [hdoms', Option.getD_some] at hbs
  have hbl : bs.length = tele.length := by
    rw [hbs.length_eq]
    simpa using teleDoms_length _ _ hdoms'
  -- the openers are the canonical ones
  have hbodyL : ∀ l ∈ body.fvarLeaves, l.1 < E :=
    leaf_lt_of_mem hL fun l hl => hwL l (mkPisOf_fvarLeaves_body tele body l hl)
  have hXr' : denoteMeta mT.acval envT φ (E + tele.length)
      (body.instantiateList (locOpen E tele.length) 0) = some Xr := by
    have h := denoteMeta_open_deepen (acval := mT.acval) (env := envT) (φ := φ) hacl 0 E body
      tele.length os' (locOpen E tele.length) hbodyL hos' (locOpen_locList E tele.length)
    rw [Nat.add_zero, hXr, Option.map_some, AnnotTerm.liftN_zero] at h
    exact h
  have hGWσ := hGW _ hW.2.1
  refine ⟨hbl, Xr, hXr', (WellDenoted_mkPisAV_inv hGWσ.1).2 bs hbs, ?_⟩
  exact foldl_app_mem_mkPisAV hGWσ.2 hbs hfW

/-- **A hole-headed body, read** (the member, family and own-hole leaves): at
`bs` opening the telescope, the body's value is the hole's value applied to the
arguments' readings. -/
theorem holeCallDep_head {E m i : Nat} {ty : Expr} (hi : i < E) {args : List Expr}
    {Xr : AnnotTerm}
    (hXr : denoteMeta mT.acval envT φ (E + m)
      ((Expr.mkAppN (.fvar i ty) args).instantiateList (locOpen E m) 0) = some Xr)
    {bs : List V} (hbl : bs.length = m) (σ : Nat → V) :
    interp V (consList bs σ) Xr
      = (args.map fun x => interp V (consList bs σ)
          ((denoteMeta mT.acval envT φ (E + m) (x.instantiateList (locOpen E m) 0)).getD
            default)).foldl SetTheory.app (σ (E - 1 - i)) := by
  rw [instantiateList_mkAppN] at hXr
  simp only [Expr.instantiateList] at hXr
  obtain ⟨fa, vs, hfa, hvs, rfl⟩ := denoteMeta_mkAppN_inv hXr
  rw [denoteMeta_fvar] at hfa
  obtain rfl := Option.some.inj hfa
  rw [interp_mkAppN_foldl, spine_map_getD hvs, List.map_map, interp_bvar,
    show E + m - 1 - i = (E - 1 - i) + bs.length from by omega, consList_apply_add]
  rfl

/-- The holes: hole `t` at `E + t`, typed `tys[t]`. -/
@[expose] def holesAt (E : Nat) (tys : List Expr) : List Expr :=
  (List.range tys.length).map fun t => Expr.fvar (E + t) (tys.getD t default)

/-- **The walk's context extended by dependently typed holes**: hole `t`'s type
over the frame and the holes before it, read at `E + t` to `Ts[t]`, graded under
the context so far, and filled by `hv[t]` at the valuation so far. -/
theorem walkCtx_holesDep {E : Nat} {L : List Expr} (hL : FvarList E L) {Δ : List AnnotTerm}
    {σ : Nat → V} (hW : WalkCtx V mT φ E σ Δ L)
    (tys : List Expr) (Ts : List AnnotTerm) (hv : List V)
    (hlen1 : tys.length = Ts.length) (hlen2 : hv.length = Ts.length)
    (hslot : ∀ t, t < Ts.length →
      (∀ l ∈ (tys.getD t default).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ ((holesAt E tys).take t).reverse ++ L) ∧
      (tys.getD t default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (tys.getD t default) ∧
      denoteMeta mT.acval envT φ (E + t) (tys.getD t default) = some (Ts.getD t default) ∧
      (∀ ρ : Nat → V, Sat V ((Ts.take t).reverse ++ Δ) ρ →
        WellDenotedV V ρ (Ts.getD t default)) ∧
      hv.getD t pt ∈ˢ interp V (consList (hv.take t) σ) (Ts.getD t default)) :
    FvarList (E + Ts.length) ((holesAt E tys).reverse ++ L) ∧
      WalkCtx V mT φ (E + Ts.length) (consList hv σ) (Ts.reverse ++ Δ)
        ((holesAt E tys).reverse ++ L) := by
  suffices key : ∀ n, n ≤ Ts.length →
      FvarList (E + n) (((holesAt E tys).take n).reverse ++ L) ∧
      WalkCtx V mT φ (E + n) (consList (hv.take n) σ) ((Ts.take n).reverse ++ Δ)
        (((holesAt E tys).take n).reverse ++ L) by
    have h := key Ts.length (Nat.le_refl _)
    have h1 : (holesAt E tys).take Ts.length = holesAt E tys :=
      List.take_of_length_le (by simp [holesAt]; omega)
    have h2 : Ts.take Ts.length = Ts := List.take_of_length_le (by omega)
    have h3 : hv.take Ts.length = hv := List.take_of_length_le (by omega)
    rwa [h1, h2, h3] at h
  intro n
  induction n with
  | zero => intro _; simpa using ⟨hL, hW⟩
  | succ n ih =>
    intro hn
    obtain ⟨hL', hW'⟩ := ih (by omega)
    obtain ⟨hlT, hbT, hcbT, hT, hGT, hvT⟩ := hslot n (by omega)
    have hnT : n < tys.length := by omega
    have hhole : (holesAt E tys).take (n + 1)
        = (holesAt E tys).take n ++ [Expr.fvar (E + n) (tys.getD n default)] := by
      rw [List.take_add_one]
      simp [holesAt, List.getElem?_range hnT]
    have hTs : Ts.take (n + 1) = Ts.take n ++ [Ts.getD n default] := by
      rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    have hvs : hv.take (n + 1) = hv.take n ++ [hv.getD n pt] := by
      rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      rfl
    rw [hhole, hTs, hvs, consList_append]
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append]
    rw [show E + (n + 1) = E + n + 1 from by omega]
    refine ⟨hL'.cons _ (wscoped_of_leaves_mem hL' _ hlT), ?_⟩
    exact hW'.cons hT hbT hcbT hlT hGT hvT

end Gen

/-! ## The instance map, read -/

section Reloc

variable {envT : Env}

/-- The instance map's level part reads at the substituted levels (`lvlRK` substitutes only
when the instance's levels are not the home's own parameters — then it is the identity,
and so is the substitution of the parameters for themselves). -/
theorem denoteMeta_lvlRK {acval : Name → (Name → Nat) → AnnotTerm}
    (hp : AcvalParamsAt envT acval) (H : ConLeche.HomeRK)
    (I : ConLeche.InstRK) (φ : Name → Nat) (d : Nat) (e : Expr) :
    denoteMeta acval envT φ d (ConLeche.lvlRK H I e)
      = denoteMeta acval envT (Level.substFn φ H.ctx.lps I.us) d e := by
  unfold ConLeche.lvlRK
  split
  · rename_i heq
    have hus : I.us = H.ctx.lps.map .param := by simpa using heq
    rw [hus, show Level.substFn φ H.ctx.lps (H.ctx.lps.map .param) = φ from
      funext fun _ => Level.substFn_map_param]
  · exact denoteMeta_instLevels hp φ d e

/-- The instance map as a parallel substitution: the home's parameters to the instance's,
the holes to the relocated ones. -/
@[expose] def relocSubst (H : ConLeche.HomeRK) (I : ConLeche.InstRK) (hs : List Expr) :
    Nat → Expr :=
  fun i => if i < H.ctx.nP then I.ds.getD i (.sort .zero) else hs.getD (i - H.ctx.nP) (.sort .zero)

/-- **The instance map, read** (`relocRK`): a term of the home's context (free variables
below the parameters and the holes) reads, relocated, as its reading at the instance's
levels substituted by the parameters' and holes' readings at the rule's depth `E`. -/
theorem denoteMeta_relocRK (mT : EnvModel V envT) {H : ConLeche.HomeRK}
    {I : ConLeche.InstRK} {hs : List Expr} {E : Nat} {φ : Name → Nat}
    (hdl : I.ds.length = H.ctx.nP) {x : Nat → AnnotTerm}
    (hx : ∀ i, i < H.ctx.nP + hs.length → Expr.WScoped E (relocSubst H I hs i) ∧
      (relocSubst H I hs i).looseBVarsBounded 0 = true ∧
      denoteMeta mT.acval envT φ E (relocSubst H I hs i) = some (x i))
    {e : Expr} (he : e.fvarsBelow (H.ctx.nP + hs.length)) :
    denoteMeta mT.acval envT φ E (ConLeche.relocRK H I hs e)
      = (denoteMeta mT.acval envT (Level.substFn φ H.ctx.lps I.us) (H.ctx.nP + hs.length) e).map
          (AnnotTerm.substAV (substTau (H.ctx.nP + hs.length) E x) · 0) := by
  unfold ConLeche.relocRK
  have hE := ConLeche.Expr.replaceFVars_erasedEq_substFvars (b := H.ctx.nP + hs.length) (D := E)
    (g := fun i => if i < H.ctx.nP then I.ds[i]?
      else if i < H.ctx.nP + hs.length then hs[i - H.ctx.nP]? else none)
    (s := relocSubst H I hs) (fun v hv ty => by
      unfold relocSubst
      by_cases hv0 : v < H.ctx.nP
      · rw [if_pos hv0, if_pos hv0, List.getElem?_eq_getElem (by omega), Option.getD_some,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
        exact ConLeche.Expr.ErasedEq.rfl _
      · rw [if_neg hv0, if_neg hv0, if_pos hv, List.getElem?_eq_getElem (by omega),
          Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
          Option.getD_some]
        exact ConLeche.Expr.ErasedEq.rfl _)
    (ConLeche.lvlRK H I e) (by
      unfold ConLeche.lvlRK
      split
      · exact he
      · exact fvarsBelow_instantiateLevelParams _ _ he)
  rw [denoteMeta_erasedEq hE E]
  have h := denoteMeta_substFvars (φ := φ) mT (b := H.ctx.nP + hs.length) (D := E)
    (s := relocSubst H I hs) (x := x) hx (ConLeche.lvlRK H I e) 0 (by
      unfold ConLeche.lvlRK
      split
      · simpa using he
      · simpa using fvarsBelow_instantiateLevelParams _ _ he)
  simp only [Nat.add_zero] at h
  rw [h, denoteMeta_lvlRK (acvalParamsAt_of_core mT)]

/-- The instance map's substitution, read: the parameters to the instance's parameters'
readings `dsa`, hole `t` (relocated at `base + t`) to its variable at depth `E`. -/
@[expose] def relocX (nP : Nat) (dsa : List AnnotTerm) (base E : Nat) : Nat → AnnotTerm :=
  fun i => if i < nP then dsa.getD i default else .bvar (E - 1 - (base + (i - nP)))

/-- **The instance map's substitution reads as `relocX`** at relocated holes `holesAt base tys`
(each hole type scoped at its own position) and parameters read `dsa` at `E`. -/
theorem relocX_ok {H : ConLeche.HomeRK} {I : ConLeche.InstRK} {base E : Nat} {tys : List Expr}
    (hE : base + tys.length = E) (htys : ∀ t, t < tys.length → Expr.WScoped (base + t) (tys.getD t default))
    (hdl : I.ds.length = H.ctx.nP)
    (hdsS : ∀ d ∈ I.ds, Expr.WScoped E d ∧ d.looseBVarsBounded 0 = true)
    {acval : Name → (Name → Nat) → AnnotTerm} {φ : Name → Nat} {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine acval envT φ E I.ds dsa) :
    ∀ i, i < H.ctx.nP + (holesAt base tys).length →
      Expr.WScoped E (relocSubst H I (holesAt base tys) i) ∧
      (relocSubst H I (holesAt base tys) i).looseBVarsBounded 0 = true ∧
      denoteMeta acval envT φ E (relocSubst H I (holesAt base tys) i)
        = some (relocX H.ctx.nP dsa base E i) := by
  intro i hi
  unfold relocSubst relocX
  by_cases hp : i < H.ctx.nP
  · rw [if_pos hp, if_pos hp]
    have hmem : I.ds.getD i (.sort .zero) ∈ I.ds := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    refine ⟨(hdsS _ hmem).1, (hdsS _ hmem).2, ?_⟩
    have := DenoteMetaSpine.getD hdsa default i (by omega)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this ⊢
    rw [this, List.getD_eq_getElem?_getD]
  · rw [if_neg hp, if_neg hp]
    have hl : (holesAt base tys).length = tys.length := by simp [holesAt]
    have ht : i - H.ctx.nP < tys.length := by omega
    have hg : (holesAt base tys).getD (i - H.ctx.nP) (.sort .zero)
        = Expr.fvar (base + (i - H.ctx.nP)) (tys.getD (i - H.ctx.nP) default) := by
      simp [holesAt, List.getD_eq_getElem?_getD, List.getElem?_range ht]
    rw [hg, denoteMeta_fvar]
    refine ⟨?_, rfl, rfl⟩
    simp only [Expr.WScoped]
    exact ⟨by omega, htys _ ht⟩

/-- **The home valuation of a relocated reading**: at `τ = consList hv σ` (the relocated holes
valued `hv`, `E = base + |hv|`), the instance map's substituted valuation gives the holes
their values `hv` over the instance's key frame. -/
theorem substE_relocX {nP base k : Nat} {dsa : List AnnotTerm} (hdl : dsa.length = nP)
    {hv : List V} (hvl : hv.length = k) (σ : Nat → V) :
    substE V (substTau (nP + k) (base + k) (relocX nP dsa base (base + k))) 0 (consList hv σ)
      = consList hv (keyFrame dsa (base + k) (consList hv σ)) := by
  rw [substE_substTau]
  congr 1
  · apply List.ext_getElem (by simp [hvl])
    intro mm h1 h2
    simp only [List.getElem_map, List.getElem_range, relocX, if_neg (show ¬ nP + mm < nP by omega),
      interp_bvar, show nP + mm - nP = mm by omega]
    rw [show base + k - 1 - (base + mm) = k - 1 - mm by omega]
    exact consList_getElem_pos hvl (by simpa using h1)
  · funext q
    unfold keyFrame
    by_cases hq : q < nP
    · rw [if_pos hq, consList_getD_of_lt _ _ _ (by simp; omega)]
      simp only [relocX, if_pos (show nP - 1 - q < nP by omega), List.length_map, hdl]
      have hlt : nP - 1 - q < dsa.length := by omega
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem hlt, Option.map_some, Option.getD_some, Option.getD_some]
    · rw [if_neg hq, show q = (q - nP) + (dsa.map (interp V (consList hv σ))).length by simp; omega,
        consList_apply_add]
      simp only [List.length_map, hdl]
      congr 1; omega

/-- **One relocated hole slot** (a home hole type `ty` relocated at the `t` holes before it,
`holesAt base tysP`): its reading at `base + t` is the home reading at the instance's levels
substituted by `relocX`; at a valuation `consList vs σ` it reads as the home type at the
holes' values over the instance's key frame; and it is graded wherever the home type is
graded at the substituted valuation. -/
theorem relocSlot (mT : EnvModel V envT) {H : ConLeche.HomeRK} {I : ConLeche.InstRK}
    {base t : Nat} {tysP : List Expr} (htl : tysP.length = t)
    (htys : ∀ s, s < t → Expr.WScoped (base + s) (tysP.getD s default))
    (hdl : I.ds.length = H.ctx.nP)
    (hdsS : ∀ d ∈ I.ds, Expr.WScoped (base + t) d ∧ d.looseBVarsBounded 0 = true)
    {φ : Name → Nat} {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mT.acval envT φ (base + t) I.ds dsa)
    {ty : Expr} (hfb : ty.fvarsBelow (H.ctx.nP + t)) {TH : AnnotTerm}
    (hTH : denoteMeta mT.acval envT (Level.substFn φ H.ctx.lps I.us) (H.ctx.nP + t) ty = some TH) :
    denoteMeta mT.acval envT φ (base + t) (ConLeche.relocRK H I (holesAt base tysP) ty)
        = some (AnnotTerm.substAV (substTau (H.ctx.nP + t) (base + t)
            (relocX H.ctx.nP dsa base (base + t))) TH 0) ∧
      (∀ (vs : List V) (σ : Nat → V), vs.length = t →
        interp V (consList vs σ) (AnnotTerm.substAV (substTau (H.ctx.nP + t) (base + t)
            (relocX H.ctx.nP dsa base (base + t))) TH 0)
          = interp V (consList vs (keyFrame dsa (base + t) (consList vs σ))) TH) ∧
      (∀ ρ : Nat → V, (∀ a ∈ dsa, WellDenotedV V ρ a) →
        WellDenotedV V (substE V (substTau (H.ctx.nP + t) (base + t)
            (relocX H.ctx.nP dsa base (base + t))) 0 ρ) TH →
        WellDenotedV V ρ (AnnotTerm.substAV (substTau (H.ctx.nP + t) (base + t)
            (relocX H.ctx.nP dsa base (base + t))) TH 0)) := by
  have hhl : (holesAt base tysP).length = t := by simp [holesAt, htl]
  have hdl' : dsa.length = H.ctx.nP := by rw [← DenoteMetaSpine.length_eq hdsa, hdl]
  refine ⟨?_, ?_, ?_⟩
  · have hx := relocX_ok (H := H) (I := I) (base := base) (E := base + t) (tys := tysP)
      (by omega) (fun s hs => htys s (by omega)) hdl hdsS hdsa
    have h := denoteMeta_relocRK mT (φ := φ) (hs := holesAt base tysP) hdl hx
      (by rw [hhl]; exact hfb)
    rw [hhl, hTH, Option.map_some] at h
    exact h
  · intro vs σ hvs
    rw [interp_substAV, ← hvs, substE_relocX hdl' rfl σ]
  · intro ρ hds hW
    have hτ : ∀ j, WellDenoted V (shiftE 0 0 ρ) (substTau (H.ctx.nP + t) (base + t)
        (relocX H.ctx.nP dsa base (base + t)) j) ∧
        AnnotValid V (shiftE 0 0 ρ) (substTau (H.ctx.nP + t) (base + t)
        (relocX H.ctx.nP dsa base (base + t)) j) := by
      intro j
      rw [shiftE_zero_zero]
      unfold substTau relocX
      split
      · split
        · rename_i h1 h2
          have hmem : dsa.getD (H.ctx.nP + t - 1 - j) default ∈ dsa := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
            exact List.getElem_mem _
          exact hds _ hmem
        · simp
      · simp
    exact ⟨(WellDenoted_substAV _ TH 0 ρ fun j => (hτ j).1).mpr hW.1,
      (AnnotValid_substAV _ TH 0 ρ fun j => (hτ j).2).mpr hW.2⟩

/-- The relocated holes' types, in `relocHolesRK`'s order: each home hole type relocated
at the holes before it. -/
@[expose] def relocTys (H : ConLeche.HomeRK) (I : ConLeche.InstRK) (base : Nat) :
    List Expr → List Expr → List Expr
  | [], acc => acc
  | ty :: tys, acc => relocTys H I base tys (acc ++ [ConLeche.relocRK H I (holesAt base acc) ty])

omit [SetTheory V] in
theorem holesAt_append (base : Nat) (acc : List Expr) (x : Expr) :
    holesAt base (acc ++ [x]) = holesAt base acc ++ [Expr.fvar (base + acc.length) x] := by
  have hl1 : (holesAt base (acc ++ [x])).length = acc.length + 1 := by simp [holesAt]
  have hl2 : (holesAt base acc).length = acc.length := by simp [holesAt]
  apply List.ext_getElem (by simp [hl1, hl2])
  intro t h1 h2
  rw [hl1] at h1
  rcases Nat.lt_or_ge t acc.length with ht | ht
  · rw [List.getElem_append_left (by omega)]
    simp [holesAt, List.getD_eq_getElem?_getD, List.getElem?_append_left ht]
  · obtain rfl : t = acc.length := by omega
    rw [List.getElem_append_right (by omega)]
    simp [holesAt]

omit [SetTheory V] in
/-- **`relocHolesRK` builds `holesAt base (relocTys …)`**: hole `t` at `base + t`, typed by its
home type relocated at the holes before it. -/
theorem relocHolesRK_eq (H : ConLeche.HomeRK) (I : ConLeche.InstRK) (base : Nat) :
    ∀ (tys acc : List Expr), ConLeche.relocHolesRK H I base tys (holesAt base acc)
      = holesAt base (relocTys H I base tys acc)
  | [], acc => rfl
  | ty :: tys, acc => by
    rw [ConLeche.relocHolesRK, relocTys, ← relocHolesRK_eq H I base tys, holesAt_append]
    have hl : (holesAt base acc).length = acc.length := by simp [holesAt]
    unfold ConLeche.relocRK
    rw [hl]

omit [SetTheory V] in
theorem relocTys_length (H : ConLeche.HomeRK) (I : ConLeche.InstRK) (base : Nat) :
    ∀ (tys acc : List Expr), (relocTys H I base tys acc).length = acc.length + tys.length
  | [], acc => by simp [relocTys]
  | ty :: tys, acc => by
    rw [relocTys, relocTys_length H I base tys]; simp; omega

omit [SetTheory V] in
/-- The relocated types: the accumulated ones first, then each home type relocated at the
holes before it. -/
theorem relocTys_getD (H : ConLeche.HomeRK) (I : ConLeche.InstRK) (base : Nat) :
    ∀ (tys acc : List Expr) (t : Nat), t < acc.length + tys.length →
      (relocTys H I base tys acc).getD t default
        = if t < acc.length then acc.getD t default
          else ConLeche.relocRK H I (holesAt base ((relocTys H I base tys acc).take t))
            (tys.getD (t - acc.length) default)
  | [], acc, t, ht => by simp at ht; simp [relocTys, ht]
  | ty :: tys, acc, t, ht => by
    rw [relocTys]
    have ih := relocTys_getD H I base tys (acc ++ [ConLeche.relocRK H I (holesAt base acc) ty]) t
      (by simp at ht ⊢; omega)
    rw [ih]
    by_cases h1 : t < acc.length
    · rw [if_pos (by simp; omega), if_pos h1, List.getD_eq_getElem?_getD,
        List.getElem?_append_left h1, ← List.getD_eq_getElem?_getD]
    · rw [if_neg h1]
      by_cases h2 : t = acc.length
      · subst h2
        rw [if_pos (by simp), List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_refl _)]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, List.getD_cons_zero]
        congr 2
        have hp : acc <+: relocTys H I base tys (acc ++ [ConLeche.relocRK H I (holesAt base acc) ty]) :=
          (List.prefix_append _ _).trans (relocTys_prefix H I base tys _)
        exact (List.prefix_iff_eq_take.mp hp)
      · rw [if_neg (by simp; omega)]
        obtain ⟨u, hu⟩ : ∃ u, t - acc.length = u + 1 := ⟨t - acc.length - 1, by omega⟩
        rw [hu, List.getD_cons_succ, List.length_append, List.length_singleton,
          show t - (acc.length + 1) = u by omega]
where
  relocTys_prefix (H : ConLeche.HomeRK) (I : ConLeche.InstRK) (base : Nat) :
      ∀ (tys acc : List Expr), acc <+: relocTys H I base tys acc
    | [], acc => List.prefix_refl _
    | ty :: tys, acc => by
      rw [relocTys]
      exact (List.prefix_append _ _).trans (relocTys_prefix H I base tys _)

end Reloc

end ConLeche.Model
