module

public import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope
public import ConLeche.Model.Inductives.TargetIhSlot
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.InstList

public section

/-!
# A call's target at a valuation of ANY hole list (lane NESTIND, session 13, item 1)

`targetCall_genW` (`TargetCallGen.lean`) reads a call's typing at a
valuation of the block's MEMBER holes: closed hole types (the formers),
one abstraction (`targetAbs`).  Ruling (D) types the calls at an OUTSIDE
class a second time with more holes — the member holes, the container's
own group and the ANCESTOR classes (`targetClassCallsOk`,
`TargetClassCallsRun`) — whose types are OPEN (an ancestor class's hole
has the class's instantiated former, which reads the rule's prefix), and
whose abstraction is a composite (`absM ∘ targetAbsInst …`).

`targetCall_genD` is the reading with every hole-specific fact a
PREMISE, stated at the frame and one run of the typing:

* the holes: a list of hole types `tysH` at the variables past the frame
  (`ihFvarsAt D tysH`), each read at the frame, graded under the frame's
  context and valued by `hv` (the walk context's slot shape,
  `walkCtx_ihs`) — so closed formers and open class formers alike;
* the field's abstract type `A` (read with the holes) and the call's
  typing `A ≡ Π tele, W` at the frame past the holes, `W` the callee's
  major domain abstracted (its leaves the frame's and the holes'), `tele`
  hole-free (its leaves the frame's) — the field's MEMBER-level
  whnf-telescope, the rule frame's (the (D) run's since session 15).

Conclusion (as `targetCall_genW`'s): at every spine `bs` of the
telescope, read at the frame, the applied field lies in `W`'s reading at
the telescope's canonical openers, which is graded there.  The telescope
is a parameter: any the typing was checked against.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section GenD

variable {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}

set_option maxHeartbeats 8000000 in
/-- **A call's target at a valuation of ANY hole list** (ruling (D);
`targetCall_genW` with the holes and the abstraction as premises): the
field value `fv` in its abstract type's reading at the holes' values
`hv`, the typing `A ≡ Π tele, W` past the holes — at every spine `bs` of `tele` (read at the
frame) the applied field lies in `W`'s reading, graded there. -/
theorem targetCall_genD (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F D : Nat} {Lf : List Expr} (hL : FvarList D Lf.reverse)
    {σ : Nat → V} {Δ : List AnnotTerm} (hW : WalkCtx V mT φ D σ Δ Lf.reverse)
    -- the holes
    {tysH : List Expr} {hv : List V} (hvl : hv.length = tysH.length)
    (hH : ∀ r, r < tysH.length →
      (∀ l ∈ (tysH.getD r default).fvarLeaves, Expr.fvar l.1 l.2 ∈ Lf) ∧
      (tysH.getD r default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (tysH.getD r default) ∧
      ∃ T : AnnotTerm, denoteMeta mT.acval envT φ D (tysH.getD r default) = some T ∧
        (∀ σ' : Nat → V, Sat V Δ σ' → WellDenotedV V σ' T) ∧ hv.getD r pt ∈ˢ interp V σ T)
    -- the field's abstract type and the call's typing
    {A W fldTy wantTy : Expr} {tele : List (Expr × BinderMeta)}
    (hAL : ∀ l ∈ A.fvarLeaves, Expr.fvar l.1 l.2 ∈ (ihFvarsAt D tysH).reverse ++ Lf.reverse)
    (hfld : ConLeche.inferTypeCore μ envT F (D + tysH.length) A = .ok fldTy)
    (hWL : ∀ l ∈ W.fvarLeaves, Expr.fvar l.1 l.2 ∈ (ihFvarsAt D tysH).reverse ++ Lf.reverse)
    (htL : ∀ b ∈ tele, ∀ l ∈ b.1.fvarLeaves, Expr.fvar l.1 l.2 ∈ Lf)
    (hwant : ConLeche.inferTypeCore μ envT F (D + tysH.length) (Expr.mkPisOf tele W) = .ok wantTy)
    (hdeq : ConLeche.isDefEqCore μ envT F (D + tysH.length) A (Expr.mkPisOf tele W) = .ok true)
    -- the field's value
    {fv : V}
    (hii : ∀ Aty : AnnotTerm, denoteMeta mT.acval envT φ (D + tysH.length) A = some Aty →
      fv ∈ˢ interp V (consList hv σ) Aty)
    (bs : List V)
    (hbs : SpineFit σ ((teleDoms mT.acval envT φ D [] (tele.map (·.1))).getD []) bs) :
    ∃ (os' : List Expr) (Xr : AnnotTerm),
      LocList (D + tysH.length) tele.length os' ∧
      denoteMeta mT.acval envT φ (D + tysH.length + tele.length) (W.instantiateList os' 0)
        = some Xr ∧
      bs.length = tele.length ∧
      WellDenoted V (consList bs (consList hv σ)) Xr ∧
      bs.foldl SetTheory.app fv ∈ˢ interp V (consList bs (consList hv σ)) Xr := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  generalize hk : tysH.length = k at *
  generalize hm : tele.length = m at *
  -- (1) the holes' readings, and the context past them
  let Ts : List AnnotTerm := (List.range k).map fun r =>
    (denoteMeta mT.acval envT φ D (tysH.getD r default)).getD default
  have hTsLen : Ts.length = k := by simp [Ts]
  have hTsGet : ∀ r, r < k → Ts.getD r default
      = (denoteMeta mT.acval envT φ D (tysH.getD r default)).getD default := by
    intro r hr
    simp [Ts, List.getD_eq_getElem?_getD, List.getElem?_range hr]
  have hL0 : FvarList (D + k) ((ihFvarsAt D tysH).reverse ++ Lf.reverse) := by
    have h := fvarList_ihs hL tysH (fun t ht => by
      obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem ht
      have hl := (hH r (by omega)).1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr, Option.getD_some] at hl
      exact wscoped_of_leaves_mem hL _ fun l hl' => List.mem_reverse.mpr (hl l hl'))
    rw [hk] at h
    exact h
  have hW0 : WalkCtx V mT φ (D + k) (consList hv σ) ((ihDomsLifted Ts).reverse ++ Δ)
      ((ihFvarsAt D tysH).reverse ++ Lf.reverse) := by
    have h := walkCtx_ihs hacl hL hW tysH Ts hv (by rw [hTsLen, hk]) (by rw [hvl, hTsLen])
      (fun r hr => by
        rw [hTsLen] at hr
        obtain ⟨hl, hb, hcb, T, hT, hG, hvT⟩ := hH r (by omega)
        rw [hTsGet r hr, hT, Option.getD_some]
        exact ⟨fun l hl' => List.mem_reverse.mpr (hl l hl'), hb, hcb, rfl, hG, hvT⟩)
    rw [hTsLen] at h
    exact h
  have hWS0 := hW0.2.2.2.2.1
  have hinL0 : ∀ y ∈ Lf, y ∈ (ihFvarsAt D tysH).reverse ++ Lf.reverse :=
    fun y hy => List.mem_append_right _ (List.mem_reverse.mpr hy)
  -- (2) the field's abstract type: framed, read, graded
  have hAb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge hfld)
  obtain ⟨Aty, hAty⟩ := acceptedReads_of mT φ hfld (wscoped_of_leaves_mem hL0 _ hAL) hAb
    (fun l hl => hWS0 _ (hAL l hl))
  obtain ⟨hFrA, hCA, hGA⟩ := WalkCtx.subjOkL hacl1 hin hL0 hW0 hAL hAb hAty
    ⟨_, Rules.inferTypeCore_bridge hfld⟩
  -- (4) the major type: framed, read, graded
  have hPL : ∀ l ∈ (Expr.mkPisOf tele W).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (ihFvarsAt D tysH).reverse ++ Lf.reverse := by
    intro l hl
    rcases ConLeche.mkPisOf_fvarLeaves _ _ l hl with ⟨b, hb, h1⟩ | h1
    · exact hinL0 _ (htL b hb l h1)
    · exact hWL l h1
  have hWb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge hwant)
  obtain ⟨WA, hWA⟩ := acceptedReads_of mT φ hwant (wscoped_of_leaves_mem hL0 _ hPL) hWb
    (fun l hl => hWS0 _ (hPL l hl))
  obtain ⟨hFrW, hCW, hGW⟩ := WalkCtx.subjOkL hacl1 hin hL0 hW0 hPL hWb hWA
    ⟨_, Rules.inferTypeCore_bridge hwant⟩
  -- (5) the call's typing: the two readings are one
  have heq := Rules.defeq_sound hin (Rules.isDefEqCore_bridge hdeq) hFrA hFrW hCA hCW hAty hWA
    hGA hGW _ hW0.2.1
  -- (6) the field lies in the major type's reading
  have hfW : fv ∈ˢ interp V (consList hv σ) WA := by
    rw [← heq]
    exact hii Aty hAty
  -- (7) the major type's reading: a Π-tower over the telescope
  have hWA' := hWA
  rw [← ConLeche.Expr.instantiateList_nil (Expr.mkPisOf _ _) 0,
    show D + k = D + k + 0 from rfl] at hWA'
  obtain ⟨ds', Xr, os', rfl, hdoms', -, hos', hXr⟩ :=
    denoteMeta_mkPisOf (acval := mT.acval) (env := envT) (φ := φ) (D := D + k) _ _ 0 []
      _ (LocList.nil _) hWA'
  rw [Nat.zero_add, hm] at hos' hXr
  -- (8) the telescope's spine fits the major type's binders
  have htleL : ∀ t ∈ tele.map (·.1), ∀ l ∈ t.fvarLeaves, l.1 < D := by
    intro t ht l hl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact leaf_lt_of_mem hL (fun l hl => List.mem_reverse.mpr (htL b hb l hl)) l hl
  have hdeep := teleDoms_deepen (acval := mT.acval) (env := envT) (φ := φ) hacl k D _ 0 [] []
    htleL (LocList.nil D) (LocList.nil (D + k))
  have hdoms'' : teleDoms mT.acval envT φ (D + k) [] (tele.map (·.1))
      = some (ds'.map (·.2.2)) := by simpa using hdoms'
  rw [hdoms''] at hdeep
  obtain ⟨ts, hts, hlift⟩ : ∃ ts, teleDoms mT.acval envT φ D [] (tele.map (·.1))
      = some ts ∧ ds'.map (·.2.2) = liftAt k 0 ts := by
    cases hts : teleDoms mT.acval envT φ D [] (tele.map (·.1)) with
    | none => rw [hts] at hdeep; exact nomatch hdeep
    | some ts => rw [hts] at hdeep; exact ⟨ts, rfl, Option.some.inj hdeep⟩
  rw [hts, Option.getD_some] at hbs
  have hbs' : SpineFit (consList hv σ) (ds'.map (·.2.2)) bs := by
    rw [hlift, spineFit_liftAt, ← hvl, shiftE_consList]; exact hbs
  have hbl : bs.length = m := by
    rw [hbs.length_eq, teleDoms_length _ _ hts, List.length_map, hm]
  -- (9) the applied field lies in the Π's body, which is graded there
  have hGWσ := hGW _ hW0.2.1
  have hfold : bs.foldl SetTheory.app fv ∈ˢ interp V (consList bs (consList hv σ)) Xr :=
    foldl_app_mem_mkPisAV hGWσ.2 hbs' hfW
  have hwdX : WellDenoted V (consList bs (consList hv σ)) Xr :=
    (WellDenoted_mkPisAV_inv hGWσ.1).2 bs hbs'
  exact ⟨os', Xr, hos', hXr, hbl, hwdX, hfold⟩

end GenD

end ConLeche.Model
