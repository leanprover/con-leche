module

public import ConLeche.Model.Inductives.TargetCallGen
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Rules.Sound
import ConLeche.Model.CtxOkKit
import ConLeche.Model.IndFrame
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Semantics.Tower.FixTower
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Model.Inductives.TargetCallKit
import ConLeche.Semantics.Kit
import ConLeche.Verify.Leaves
import ConLeche.Verify.BetaGate

public section

/-!
# A call typed at a hole, at a valuation of the holes (PRIMREC, lane FLATHOME)

`targetCall_gen` (`TargetCallGen.lean`) reads a call typed on the
MEMBER-abstracted terms: the field's abstract type defeq to the callee's
member hole at the prefix's parameters.  A call around a cycle of an
OUTSIDE home is typed at that HOME's holes instead
(`targetIntraCallOk`): a field type `fld` (the constructor's, with the
home abstracted before its instantiation) defeq to `∀ a⃗, hole args⃗`,
with any arguments `args⃗` over the frame and the telescope.
`holeCall_gen` states it once, generic in `fld` and `args⃗`: at every
valuation `hv` of the holes (each in its former's type) where the field
lies in `fld`'s reading, at every spine `bs` of the telescope the
arguments' readings fit the hole's type's binder data and the applied
field lies in the hole applied to them.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche.Term
open ConLeche (Env Expr Name Level ConstantVal CheckMode TargetIh TargetFamily)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

omit [SetTheory V] in
/-- A leaf of an application spine is the head's or an argument's. -/
theorem mkAppN_fvarLeaves_mem : ∀ (as : List Expr) (f : Expr) (l : Nat × Expr),
    l ∈ (Expr.mkAppN f as).fvarLeaves → l ∈ f.fvarLeaves ∨ ∃ a ∈ as, l ∈ a.fvarLeaves
  | [], _, _, h => Or.inl h
  | a :: as, f, l, h => by
    rcases mkAppN_fvarLeaves_mem as (.app f a) l h with h1 | ⟨x, hx, h1⟩
    · simp only [Expr.fvarLeaves, List.mem_append] at h1
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨a, List.mem_cons_self, h1⟩
    · exact Or.inr ⟨x, List.mem_cons_of_mem _ hx, h1⟩

section Gen

variable {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}

set_option maxHeartbeats 8000000 in
/-- **A call typed at a hole, at a valuation of the holes** (see the
module docstring). -/
theorem holeCall_gen (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F rP nF : Nat} {fvsPref fvsF : List Expr} {tele : List (Expr × ConLeche.BinderMeta)}
    {formerTys : List Expr} {args : List Expr} {fld : Expr} {t : Nat} {fldTy wantTy : Expr}
    (hfld : ConLeche.inferTypeCore μ envT F (rP + nF + formerTys.length) fld = .ok fldTy)
    (hwant : ConLeche.inferTypeCore μ envT F (rP + nF + formerTys.length)
      (Expr.mkPisOf tele (Expr.mkAppN (.fvar (rP + nF + t) (formerTys.getD t default)) args))
        = .ok wantTy)
    (hdeq : ConLeche.isDefEqCore μ envT F (rP + nF + formerTys.length) fld
      (Expr.mkPisOf tele (Expr.mkAppN (.fvar (rP + nF + t) (formerTys.getD t default)) args))
        = .ok true)
    -- the frame
    (hL : FvarList (rP + nF) (fvsPref ++ fvsF).reverse)
    {ρ : Nat → V} {xs fs : List V} (hxl : xs.length = rP) (hfl : fs.length = nF)
    {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ (rP + nF) (consList (xs ++ fs) ρ) Δ (fvsPref ++ fvsF).reverse)
    (i : Nat)
    -- the leaves: the field's type over the frame and the holes, the rest over the frame
    (hfldL : ∀ l ∈ fld.fvarLeaves, Expr.fvar l.1 l.2 ∈
      (ConLeche.targetHoles formerTys (rP + nF)).reverse ++ (fvsPref ++ fvsF).reverse)
    (htL : ∀ b ∈ tele, ∀ l ∈ b.1.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF)
    (hargsL : ∀ x ∈ args, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF)
    -- the holes
    {hv : List V} (hvl : hv.length = formerTys.length)
    (hformer : ∀ t, t < formerTys.length →
      (formerTys.getD t default).hasFvar = false ∧
      (formerTys.getD t default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (formerTys.getD t default) ∧
      ∃ T : AnnotTerm, denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
        (∀ σ : Nat → V, WellDenotedV V σ T) ∧ ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T)
    (hii : ∀ Aty : AnnotTerm,
      denoteMeta mT.acval envT φ (rP + nF + formerTys.length) fld = some Aty →
      fs.getD i pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) Aty)
    -- the callee's hole and its type's binders
    (ht : t < formerTys.length) {pds : List (Nat × Nat × AnnotTerm)} {R : AnnotTerm}
    (hTt : denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some (mkPisAV pds R))
    (hpdsNZ : ∀ d ∈ pds, d.2.1 ≠ 0) (hpdsLen : pds.length = args.length)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mT.acval envT φ (rP + nF) [] (tele.map (·.1))).getD []) bs) :
    SpineFit ρ (pds.map (·.2.2))
      (args.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mT.acval envT φ (rP + nF + tele.length)
          (x.instantiateList (locOpen (rP + nF) tele.length) 0)).getD default))) ∧
    bs.length = tele.length ∧
    bs.foldl SetTheory.app (fs.getD i pt)
      ∈ˢ (args.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mT.acval envT φ (rP + nF + tele.length)
          (x.instantiateList (locOpen (rP + nF) tele.length) 0)).getD default))).foldl
          SetTheory.app (hv.getD t pt) := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  -- names
  generalize hD : rP + nF = D at *
  generalize hk : formerTys.length = k at *
  generalize hm : tele.length = m at *
  have hlenS : (xs ++ fs).length = D := by rw [List.length_append, hxl, hfl]; omega
  -- (1) the holes' readings, and the context past them
  let Ts : List AnnotTerm := (List.range k).map fun t =>
    (denoteMeta mT.acval envT φ 0 (formerTys.getD t default)).getD default
  have hTsLen : Ts.length = k := by simp [Ts]
  have hTsGet : ∀ t, t < k → ∃ T, Ts.getD t default = T ∧
      denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
      Term.bvarsBelow 0 T.erase ∧ (∀ σ : Nat → V, WellDenotedV V σ T) ∧
      ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T := by
    intro t ht
    obtain ⟨hf, hb, -, T, hT, hG, hvT⟩ := hformer t (by omega)
    refine ⟨T, ?_, hT, bvarsBelow_of_reading (m := mT) (Expr.WScoped.of_not_hasFvar hf) hb hT,
      hG, hvT⟩
    have hT' := hT
    rw [List.getD_eq_getElem?_getD] at hT'
    simp [Ts, List.getD_eq_getElem?_getD, List.getElem?_range ht, hT']
  have hL0 : FvarList (D + k)
      ((ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse) := by
    have h := fvarList_ihs hL formerTys (fun t ht => by
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
      have := (hformer i (by omega)).1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this
      exact Expr.WScoped.of_not_hasFvar this)
    rw [hk] at h
    exact h
  have hW0 : WalkCtx V mT φ (D + k) (consList hv (consList (xs ++ fs) ρ))
      ((ihDomsLifted Ts).reverse ++ Δ)
      ((ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse) := by
    have h := walkCtx_ihs hacl hL hW formerTys Ts hv (by rw [hTsLen, hk]) (by rw [hvl, hTsLen])
      (fun t ht => by
        rw [hTsLen] at ht
        obtain ⟨T, hTe, hT, hcl, hG, hvT⟩ := hTsGet t ht
        obtain ⟨hf, hb, hcb, -⟩ := hformer t (by omega)
        have hnl : ∀ l ∈ (formerTys.getD t default).fvarLeaves,
            Expr.fvar l.1 l.2 ∈ (fvsPref ++ fvsF).reverse := by
          intro l hl
          rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hf] at hl
          exact nomatch hl
        refine ⟨hnl, hb, hcb, ?_, fun σ _ => by rw [hTe]; exact hG σ, ?_⟩
        · rw [hTe]
          exact denoteMeta_depth_of_closed hacl1 hf (fun j => liftN_eq_self_of_closed hcl j 1) hT D
        · rw [hTe]
          exact hvT _)
    rw [hTsLen] at h
    exact h
  have hinL0 : ∀ y ∈ fvsPref ++ fvsF,
      y ∈ (ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse :=
    fun y hy => List.mem_append_right _ (List.mem_reverse.mpr hy)
  have hWS0 := hW0.2.2.2.2.1
  -- (2) the field's type: framed, read, graded
  have hAb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge hfld)
  obtain ⟨Aty, hAty⟩ := acceptedReads_of mT φ hfld (wscoped_of_leaves_mem hL0 _ hfldL) hAb
    (fun l hl => hWS0 _ (hfldL l hl))
  obtain ⟨hFrA, hCA, hGA⟩ := WalkCtx.subjOkL hacl1 hin hL0 hW0 hfldL hAb hAty
    ⟨_, Rules.inferTypeCore_bridge hfld⟩
  -- (3) the hole type: framed, read, graded
  have hholeMem : Expr.fvar (D + t) (formerTys.getD t default)
      ∈ (ConLeche.targetHoles formerTys D).reverse := by
    rw [List.mem_reverse]
    simp only [ConLeche.targetHoles, List.mem_map, List.mem_range]
    exact ⟨t, by omega, rfl⟩
  have hWL : ∀ l ∈ (Expr.mkPisOf tele
      (Expr.mkAppN (.fvar (D + t) (formerTys.getD t default)) args)).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse := by
    intro l hl
    rcases ConLeche.mkPisOf_fvarLeaves _ _ l hl with ⟨b, hb, h1⟩ | h1
    · exact hinL0 _ (htL b hb l h1)
    · rcases mkAppN_fvarLeaves_mem _ _ l h1 with h2 | ⟨x, hx, h2⟩
      · simp only [Expr.fvarLeaves, List.mem_cons] at h2
        rcases h2 with rfl | h2
        · exact List.mem_append_left _ hholeMem
        · have hcl := (hformer t (by omega)).1
          rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl] at h2
          exact nomatch h2
      · exact hinL0 _ (hargsL x hx l h2)
  have hWb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge hwant)
  obtain ⟨WA, hWA⟩ := acceptedReads_of mT φ hwant (wscoped_of_leaves_mem hL0 _ hWL) hWb
    (fun l hl => hWS0 _ (hWL l hl))
  obtain ⟨hFrW, hCW, hGW⟩ := WalkCtx.subjOkL hacl1 hin hL0 hW0 hWL hWb hWA
    ⟨_, Rules.inferTypeCore_bridge hwant⟩
  -- (4) the call's typing: the two readings are one
  have heq := Rules.defeq_sound hin (Rules.isDefEqCore_bridge hdeq) hFrA hFrW hCA hCW hAty hWA
    hGA hGW _ hW0.2.1
  -- (5) the field lies in the hole type's reading
  have hfW : fs.getD i pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) WA := by
    rw [← heq]
    exact hii Aty hAty
  -- (6) the hole type's reading: a Π-tower over the telescope
  have hWA' := hWA
  rw [← ConLeche.Expr.instantiateList_nil (Expr.mkPisOf _ _) 0,
    show D + k = D + k + 0 from rfl] at hWA'
  obtain ⟨ds', Xr, os', rfl, hdoms', -, hos', hXr⟩ :=
    denoteMeta_mkPisOf (acval := mT.acval) (env := envT) (φ := φ) (D := D + k) _ _ 0 []
      _ (LocList.nil _) hWA'
  rw [Nat.zero_add, hm] at hos' hXr
  -- (7) the telescope's spine fits the hole type's binders
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
  have hbs' : SpineFit (consList hv (consList (xs ++ fs) ρ)) (ds'.map (·.2.2)) bs := by
    rw [hlift, spineFit_liftAt, ← hvl, shiftE_consList]; exact hbs
  have hbl : bs.length = m := by
    rw [hbs.length_eq, teleDoms_length _ _ hts, List.length_map, hm]
  -- (8) the applied field lies in the Π's body, which is graded there
  have hGWσ := hGW _ hW0.2.1
  have hfold : bs.foldl SetTheory.app (fs.getD i pt)
      ∈ˢ interp V (consList bs (consList hv (consList (xs ++ fs) ρ))) Xr :=
    foldl_app_mem_mkPisAV hGWσ.2 hbs' hfW
  have hwdX : WellDenoted V (consList bs (consList hv (consList (xs ++ fs) ρ))) Xr :=
    (WellDenoted_mkPisAV_inv hGWσ.1).2 bs hbs'
  -- (9) the body's syntax: the hole applied to the arguments
  have hosF : ∀ o ∈ os', ∃ i ty, o = Expr.fvar i ty := by
    intro o ho
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem ho
    obtain ⟨ty, hty⟩ := hos'.2 j (by rw [← hos'.1]; exact hj)
    rw [List.getElem?_eq_getElem hj, hget] at hty
    exact ⟨_, _, Option.some.inj hty⟩
  rw [instantiateList_mkAppN] at hXr
  simp only [Expr.instantiateList] at hXr
  obtain ⟨fa, vs, hfa, hvs, rfl⟩ := denoteMeta_mkAppN_inv hXr
  rw [denoteMeta_fvar] at hfa
  obtain rfl := Option.some.inj hfa
  -- (10) the head's value: the hole's
  have hhead : interp V (consList bs (consList hv (consList (xs ++ fs) ρ)))
      (AnnotTerm.bvar (D + k + m - 1 - (D + t))) = hv.getD t pt := by
    rw [interp_bvar, show D + k + m - 1 - (D + t) = (k - 1 - t) + bs.length from by omega,
      consList_apply_add, consList_getD_of_lt _ _ _ (by omega), hvl,
      show k - 1 - (k - 1 - t) = t from by omega]
  -- (11) the spine fits the hole's type's binder data
  obtain ⟨-, -, -, T, hT, -, hvT⟩ := hformer t ht
  obtain rfl : T = mkPisAV pds R := Option.some.inj (hT.symm.trans hTt)
  have hvsLen : vs.length = pds.length := by
    rw [← hvs.length, hpdsLen, List.length_map]
  have hsp := spineFit_of_wellDenoted_mkAppN_pi (σ := ρ) hpdsNZ hwdX (by rw [hhead]; exact hvT ρ)
    hvsLen
  -- (12) the spine's values: the arguments' readings at the telescope's openers
  have hτ : consList bs (consList hv (consList (xs ++ fs) ρ)) = consList (hv ++ bs) (consList (xs ++ fs) ρ) :=
    (consList_append hv bs _).symm
  have hvals : vs.map (interp V (consList bs (consList hv (consList (xs ++ fs) ρ))))
      = args.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mT.acval envT φ (D + m) (x.instantiateList (locOpen D m) 0)).getD
            default)) := by
    rw [spine_map_getD hvs, List.map_map]
    refine List.map_congr_left fun x hx => ?_
    have hxL : ∀ l ∈ x.fvarLeaves, l.1 < D :=
      leaf_lt_of_mem hL (fun l hl => List.mem_reverse.mpr (hargsL x hx l hl))
    have hd := denoteMeta_open_deepen (acval := mT.acval) (env := envT) (φ := φ) hacl k D x m
      (locOpen D m) os' hxL (locOpen_locList D m) hos'
    obtain ⟨A1, hA1⟩ := spine_reads hvs _ (List.mem_map_of_mem hx)
    rw [hA1] at hd
    cases hA0 : denoteMeta mT.acval envT φ (D + m) (x.instantiateList (locOpen D m) 0) with
    | none => rw [hA0] at hd; exact nomatch hd
    | some A0 =>
      rw [hA0, Option.map_some] at hd
      simp only [Function.comp, hA1, Option.getD_some]
      rw [Option.some.inj hd, interp_liftN, shiftE_consList_ih hbl hvl]
  refine ⟨?_, hbl, ?_⟩
  · rw [← hvals]; exact hsp
  · rw [← hvals, ← hhead, ← interp_mkAppN_foldl]
    exact hfold

end Gen

end ConLeche.Model
