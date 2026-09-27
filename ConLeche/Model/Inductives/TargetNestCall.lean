module

import ConLeche.Model.Inductives.TargetCallGen
public import ConLeche.Model.Inductives.TargetNodeRead
public import ConLeche.Model.Inductives.TargetRecRead
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

end ConLeche.Model
