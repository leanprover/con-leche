module

public import ConLeche.Model.Inductives.TargetCallKit
public import ConLeche.Model.Inductives.TargetNodeRead
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Rules.Sound
import ConLeche.Model.CtxOkKit
import ConLeche.Model.IndDomGrade
import ConLeche.Model.IndFrame
import ConLeche.Model.Inductives.BlockRecRead
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.StructEntryKit
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Annot.BitClosed
import ConLeche.Model.Inductives.StructFrames
import ConLeche.Semantics.Tower.FixFamI
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.InferLemmas

public section

/-!
# A target call's target at a valuation of the holes (lane RECLIB, B3 (e) + B4)

The target check types a recursive call on the member-ABSTRACTED terms
(`targetCallOk`): the field's abstract whnf-telescope is defeq to
`∀ a⃗, hole x⃗ e⃗` at the frame extended by the block's member holes
(`hdeq`), whose body was inferred (`hwant`).  `targetCall_gen` reads it
at any valuation `hv` of the holes (at their formers' types): the field,
in its abstract type's reading (`hii`), lies in the Π's reading (the
whnf telescope keeps the value, `targetWhnfPis_sem`; the defeq equates
the two readings); the Π's body is the hole applied to the parameters
and the index arguments (K5: the abstraction leaves the index arguments
alone), whose grading makes the arguments fit the hole's type's binder
data — a graph's domain is rigid (`spineFit_of_wellDenoted_mkAppN_pi`).

It is stated at a call's typing run (`TargetCallRun`) and the frame's
walk context, generic in everything the rule data pin;
`TargetCallCore.lean` instantiates it.
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

section Gen

variable {envT : Env} {mT : EnvModel V envT} {φ : Name → Nat}

/-- The value of a frame variable, read above extra slots. -/
theorem interp_frame_fvar {D E i : Nat} {L : List V} {ρ : Nat → V} {extra : List V}
    (hL : L.length = D) (hE : extra.length = E) (hi : i < D) :
    interp V (consList extra (consList L ρ)) (.bvar (D + E - 1 - i)) = L.getD i pt := by
  rw [interp_bvar, show D + E - 1 - i = (D - 1 - i) + extra.length from by omega,
    consList_apply_add, consList_getD_of_lt _ _ _ (by omega), hL,
    show D - 1 - (D - 1 - i) = i from by omega]


omit [SetTheory V] in
theorem targetAbs_mkAppN {names : List Name} {lvls : List Level} {holes : List Expr} :
    ∀ (as : List Expr) (f : Expr),
      ConLeche.targetAbs names lvls holes (Expr.mkAppN f as)
        = Expr.mkAppN (ConLeche.targetAbs names lvls holes f)
            (as.map (ConLeche.targetAbs names lvls holes))
  | [], _ => rfl
  | a :: as, f => by
    show ConLeche.targetAbs names lvls holes (Expr.mkAppN (.app f a) as) = _
    rw [targetAbs_mkAppN as (.app f a)]
    rfl

omit [SetTheory V] in
theorem teleDoms_length {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}
    {D : Nat} : ∀ (tys os : List Expr) {ds : List AnnotTerm},
      teleDoms acval env φ D os tys = some ds → ds.length = tys.length
  | [], _, ds, h => by simp [teleDoms] at h; subst h; rfl
  | ty :: tys, os, ds, h => by
    simp only [teleDoms, Option.bind_eq_bind] at h
    obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨r, hr, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := (Option.some.inj h).symm
    simp [teleDoms_length tys _ hr]


/-- Every subject of a read spine reads. -/
theorem spine_reads {d : Nat} :
    ∀ {es : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine mT.acval envT φ d es vs →
      ∀ e ∈ es, ∃ a, denoteMeta mT.acval envT φ d e = some a
  | _, _, .nil, _, he => nomatch he
  | _, _, .cons (a := a0) ha hr, e, he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨_, ha⟩
    · exact spine_reads hr e he

/-- A read spine's values, entry by entry. -/
theorem spine_map_getD {d : Nat} {τ : Nat → V} :
    ∀ {es : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine mT.acval envT φ d es vs →
      vs.map (interp V τ)
        = es.map fun e => interp V τ ((denoteMeta mT.acval envT φ d e).getD default)
  | _, _, .nil => rfl
  | _, _, .cons ha hr => by
    simp only [List.map_cons, ha, Option.getD_some]
    rw [spine_map_getD hr]

set_option maxHeartbeats 8000000 in
/-- **A call's target at a valuation of the holes, from its typing run.**
At the frame `D = rP + nF` (prefix and fields, `hW`) extended by the
member holes at values `hv` of their formers' types, with the field in
its member-abstracted type's reading (`hii`) and the call's major domain
the callee's member `I` (hole `t`) at the prefix's parameters and the
index arguments (`hmaj`): at every spine `bs` of the field's telescope
the parameters and the index readings fit the hole's type's binder
data, and the applied field lies in the hole applied to them. -/
theorem targetCall_gen (hμ : μ.verifiedChecks = true)
    (hacl : ∀ (n : Name) (ψ : Name → Nat) (m k : Nat), (mT.acval n ψ).liftN m k = mT.acval n ψ)
    (hin : Rules.RulesInputs V mT φ)
    {F rP nF : Nat} {fam : TargetFamily} {fvsPref fvsF fnorm : List Expr}
    {teles : List (List (Expr × ConLeche.BinderMeta))} {names : List Name} {lvls : List Level}
    {formerTys : List Expr} {pw : ConLeche.PropWhen} {ih : TargetIh}
    (C : ConLeche.TargetCallRun μ F envT fam fvsPref fvsF fnorm teles
      (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys (rP + nF))) (rP + nF)
      formerTys.length pw ih)
    (hfnorm : ConLeche.targetWhnfPis (ConLeche.fueledOps μ F) envT (rP + nF + formerTys.length) 1024
      (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys (rP + nF))
        (fvsF.getD ih.field default).fvarTypeD) = .ok (fnorm.getD ih.field default))
    -- the frame
    (hlp : fvsPref.length = rP) (hlf : fvsF.length = nF)
    (hL : FvarList (rP + nF) (fvsPref ++ fvsF).reverse)
    {ρ : Nat → V} {xs fs : List V} (hxl : xs.length = rP) (hfl : fs.length = nF)
    {Δ : List AnnotTerm}
    (hW : WalkCtx V mT φ (rP + nF) (consList (xs ++ fs) ρ) Δ (fvsPref ++ fvsF).reverse)
    (hfi : ih.field < nF)
    -- the telescope's and the index arguments' leaves
    (htL : ∀ b ∈ teles.getD ih.field [], ∀ l ∈ b.1.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF)
    (hidxL : ∀ x ∈ ih.idx, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF)
    -- the holes
    {hv : List V} (hvl : hv.length = formerTys.length)
    (hformer : ∀ t, t < formerTys.length →
      (formerTys.getD t default).hasFvar = false ∧
      (formerTys.getD t default).looseBVarsBounded 0 = true ∧
      ConstsBound envT (formerTys.getD t default) ∧
      ∃ T : AnnotTerm, denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some T ∧
        (∀ σ : Nat → V, WellDenotedV V σ T) ∧ ∀ σ : Nat → V, hv.getD t pt ∈ˢ interp V σ T)
    (hii : ∀ Aty : AnnotTerm,
      denoteMeta mT.acval envT φ (rP + nF + formerTys.length)
        (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys (rP + nF))
          (fvsF.getD ih.field default).fvarTypeD) = some Aty →
      fs.getD ih.field pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) Aty)
    -- the call's major domain: the callee's member at the parameters and the indices
    {I : Name} {t nP : Nat} (hnP : nP ≤ rP)
    (hRf : (fam.recTys.getD ih.callee (.sort .zero)).hasFvar = false)
    (hmaj : ∀ os : List Expr, LocList (rP + nF + formerTys.length) (teles.getD ih.field []).length os →
      C.majDom.instantiateList os 0 = Expr.mkAppN (.const I lvls)
        ((fvsPref.take nP).map (·.instantiateList os 0) ++ ih.idx.map (·.instantiateList os 0)))
    (hI : names.findIdx? (· == I) = some t) (ht : t < formerTys.length)
    {pds : List (Nat × Nat × AnnotTerm)} {R : AnnotTerm}
    (hTt : denoteMeta mT.acval envT φ 0 (formerTys.getD t default) = some (mkPisAV pds R))
    (hpdsNZ : ∀ d ∈ pds, d.2.1 ≠ 0) (hpdsLen : pds.length = nP + ih.idx.length)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((teleDoms mT.acval envT φ (rP + nF) [] ((teles.getD ih.field []).map (·.1))).getD []) bs) :
    SpineFit ρ (pds.map (·.2.2))
      (xs.take nP ++ ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mT.acval envT φ (rP + nF + (teles.getD ih.field []).length)
          (x.instantiateList (locOpen (rP + nF) (teles.getD ih.field []).length) 0)).getD
          default))) ∧
    interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mT.acval envT φ (rP + nF + (teles.getD ih.field []).length)
          ((Expr.mkAppN (fvsF.getD ih.field default)
            (ConLeche.structTeleVars (teles.getD ih.field []).length)).instantiateList
            (locOpen (rP + nF) (teles.getD ih.field []).length) 0)).getD default)
      ∈ˢ (xs.take nP ++ ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
        ((denoteMeta mT.acval envT φ (rP + nF + (teles.getD ih.field []).length)
          (x.instantiateList (locOpen (rP + nF) (teles.getD ih.field []).length) 0)).getD
          default))).foldl SetTheory.app (hv.getD t pt) := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  have hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (mT.acval n ψ).liftN 1 k = mT.acval n ψ :=
    fun n ψ k => hacl n ψ 1 k
  -- names
  generalize hD : rP + nF = D at *
  generalize hk : formerTys.length = k at *
  generalize hm : (teles.getD ih.field []).length = m at *
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
  -- the frame's and the holes' leaves
  have hframeL : ∀ x ∈ fvsPref ++ fvsF, ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF :=
    frame_leaves_mem (Lf := fvsPref ++ fvsF) hL (fun x hx l hl =>
      List.mem_reverse.mp (hW.2.2.2.2.2.2 x (List.mem_reverse.mpr hx) l hl))
  have hinL0 : ∀ y ∈ fvsPref ++ fvsF,
      y ∈ (ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse :=
    fun y hy => List.mem_append_right _ (List.mem_reverse.mpr hy)
  have habsL : ∀ e : Expr, (∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF) →
      ∀ l ∈ (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D) e).fvarLeaves,
        Expr.fvar l.1 l.2 ∈ (ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse := by
    intro e he l hl
    rcases ConLeche.targetAbs_fvarLeaves e l hl with h1 | ⟨h, hh, h1⟩
    · exact hinL0 _ (he l h1)
    · have hh' := hh
      simp only [ConLeche.targetHoles, List.mem_map, List.mem_range] at hh'
      obtain ⟨t', ht', rfl⟩ := hh'
      have hcl := (hformer t' (by omega)).1
      simp only [Expr.fvarLeaves, List.mem_cons,
        ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hcl, List.not_mem_nil, or_false] at h1
      subst h1
      exact List.mem_append_left _ (List.mem_reverse.mpr hh)
  have hWS0 := hW0.2.2.2.2.1
  -- (2) the field's member-abstracted type: framed, read, graded
  have hfmem : fvsF.getD ih.field default ∈ fvsPref ++ fvsF := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.mem_append_right _ (List.getElem_mem _)
  have hftyL : ∀ l ∈ (fvsF.getD ih.field default).fvarTypeD.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF := fun l hl =>
    List.mem_reverse.mp (hW.2.2.2.2.2.2 _ (List.mem_reverse.mpr hfmem) l hl)
  have hAL := habsL _ hftyL
  have hAb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge C.hfld)
  obtain ⟨Aty, hAty⟩ := acceptedReads_of mT φ C.hfld (wscoped_of_leaves_mem hL0 _ hAL) hAb
    (fun l hl => hWS0 _ (hAL l hl))
  obtain ⟨hFrA, hCA, hGA⟩ := WalkCtx.subjOkL hacl1 hin hL0 hW0 hAL hAb hAty
    ⟨_, Rules.inferTypeCore_bridge C.hfld⟩
  -- (3) its telescope through whnf keeps the value
  obtain ⟨hFrN, hLN, fnA, hfnA, hGN, hEN⟩ :=
    targetWhnfPis_sem (μ := .verified) rfl hin 1024 (D + k) _ _ hfnorm hFrA hCA hAty hGA
  have hCN := hCA.of_subset hLN
  -- (4) the major type: framed, read, graded
  have hmajL : ∀ l ∈ C.majDom.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvsPref ++ fvsF := by
    intro l hl
    have hl' : l ∈ C.calleeAt.fvarLeaves := by
      rw [C.hmajDom]; simp [Expr.fvarLeaves, hl]
    rcases ConLeche.instPisAtLift_fvarLeaves _ _ C.hcallee l hl' with h1 | ⟨x, hx, h1⟩
    · rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hRf] at h1; exact nomatch h1
    · rcases List.mem_append.mp hx with hx | hx
      · exact hframeL x (List.mem_append_left _ hx) l h1
      · exact hidxL x hx l h1
  have hWL : ∀ l ∈ (Expr.mkPisOf (teles.getD ih.field [])
      (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D) C.majDom)).fvarLeaves,
      Expr.fvar l.1 l.2 ∈ (ConLeche.targetHoles formerTys D).reverse ++ (fvsPref ++ fvsF).reverse := by
    intro l hl
    rcases ConLeche.mkPisOf_fvarLeaves _ _ l hl with ⟨b, hb, h1⟩ | h1
    · exact hinL0 _ (htL b hb l h1)
    · exact habsL _ hmajL l h1
  have hWb := ConLeche.infer_full_bvarClosed (Rules.inferTypeCore_bridge C.hwant)
  obtain ⟨WA, hWA⟩ := acceptedReads_of mT φ C.hwant (wscoped_of_leaves_mem hL0 _ hWL) hWb
    (fun l hl => hWS0 _ (hWL l hl))
  obtain ⟨hFrW, hCW, hGW⟩ := WalkCtx.subjOkL hacl1 hin hL0 hW0 hWL hWb hWA
    ⟨_, Rules.inferTypeCore_bridge C.hwant⟩
  -- (5) the call's typing: the two readings are one
  have heq := Rules.defeq_sound hin (Rules.isDefEqCore_bridge C.hdeq) hFrN hFrW hCN hCW hfnA hWA
    hGN hGW _ hW0.2.1
  -- (6) the field lies in the major type's reading
  have hfW : fs.getD ih.field pt ∈ˢ interp V (consList hv (consList (xs ++ fs) ρ)) WA := by
    rw [← heq, ← hEN _ hW0.2.1]
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
  have htleL : ∀ t ∈ (teles.getD ih.field []).map (·.1), ∀ l ∈ t.fvarLeaves, l.1 < D := by
    intro t ht l hl
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ht
    exact leaf_lt_of_mem hL (fun l hl => List.mem_reverse.mpr (htL b hb l hl)) l hl
  have hdeep := teleDoms_deepen (acval := mT.acval) (env := envT) (φ := φ) hacl k D _ 0 [] []
    htleL (LocList.nil D) (LocList.nil (D + k))
  have hdoms'' : teleDoms mT.acval envT φ (D + k) [] ((teles.getD ih.field []).map (·.1))
      = some (ds'.map (·.2.2)) := by simpa using hdoms'
  rw [hdoms''] at hdeep
  obtain ⟨ts, hts, hlift⟩ : ∃ ts, teleDoms mT.acval envT φ D [] ((teles.getD ih.field []).map (·.1))
      = some ts ∧ ds'.map (·.2.2) = liftAt k 0 ts := by
    cases hts : teleDoms mT.acval envT φ D [] ((teles.getD ih.field []).map (·.1)) with
    | none => rw [hts] at hdeep; exact nomatch hdeep
    | some ts => rw [hts] at hdeep; exact ⟨ts, rfl, Option.some.inj hdeep⟩
  rw [hts, Option.getD_some] at hbs
  have hbs' : SpineFit (consList hv (consList (xs ++ fs) ρ)) (ds'.map (·.2.2)) bs := by
    rw [hlift, spineFit_liftAt, ← hvl, shiftE_consList]; exact hbs
  have hbl : bs.length = m := by
    rw [hbs.length_eq, teleDoms_length _ _ hts, List.length_map, hm]
  -- (9) the applied field lies in the Π's body, which is graded there
  have hGWσ := hGW _ hW0.2.1
  have hfold : bs.foldl SetTheory.app (fs.getD ih.field pt)
      ∈ˢ interp V (consList bs (consList hv (consList (xs ++ fs) ρ))) Xr :=
    foldl_app_mem_mkPisAV hGWσ.2 hbs' hfW
  have hwdX : WellDenoted V (consList bs (consList hv (consList (xs ++ fs) ρ))) Xr :=
    (WellDenoted_mkPisAV_inv hGWσ.1).2 bs hbs'
  -- (10) the body's syntax: the hole applied to the parameters and the indices
  have hfvPref : ∀ i, i < rP → ∃ ty, (fvsPref ++ fvsF)[i]? = some (Expr.fvar i ty) := by
    intro i hi
    have hlt : i < (fvsPref ++ fvsF).length := by
      simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hL.reverse_idx i _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    exact ⟨ty, by rw [List.getElem?_eq_getElem hlt, hty]⟩
  have hprefAbs : (fvsPref.take nP).map (ConLeche.targetAbs names lvls
      (ConLeche.targetHoles formerTys D)) = fvsPref.take nP := by
    refine (List.map_congr_left (g := id) fun x hx => ?_).trans (List.map_id _)
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (List.mem_of_mem_take hx)
    obtain ⟨ty, hty⟩ := hfvPref i (by omega)
    rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, hget] at hty
    obtain rfl := Option.some.inj hty
    rfl
  have hholeT : ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D) (.const I lvls)
      = Expr.fvar (D + t) (formerTys.getD t default) := by
    simp only [ConLeche.targetAbs, beq_self_eq_true, if_true, hI]
    rw [List.getD_eq_getElem?_getD, ConLeche.targetHoles, List.getElem?_map,
      List.getElem?_range (by omega), Option.map_some, Option.getD_some]
  have hprefInst : (fvsPref.take nP).map (·.instantiateList os' 0) = fvsPref.take nP := by
    refine (List.map_congr_left (g := id) fun x hx => ?_).trans (List.map_id _)
    obtain ⟨i, hi, hget⟩ := List.getElem_of_mem (List.mem_of_mem_take hx)
    obtain ⟨ty, hty⟩ := hfvPref i (by omega)
    rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi, hget] at hty
    obtain rfl := Option.some.inj hty
    simp [Expr.instantiateList]
  have hholesF : ∀ h ∈ ConLeche.targetHoles formerTys D, ∃ i ty, h = Expr.fvar i ty := by
    intro h hh
    simp only [ConLeche.targetHoles, List.mem_map] at hh
    obtain ⟨t', -, rfl⟩ := hh
    exact ⟨_, _, rfl⟩
  have hosF : ∀ o ∈ os', ∃ i ty, o = Expr.fvar i ty := by
    intro o ho
    obtain ⟨j, hj, hget⟩ := List.getElem_of_mem ho
    obtain ⟨ty, hty⟩ := hos'.2 j (by rw [← hos'.1]; exact hj)
    rw [List.getElem?_eq_getElem hj, hget] at hty
    exact ⟨_, _, Option.some.inj hty⟩
  have hAbsMaj : (ConLeche.targetAbs names lvls (ConLeche.targetHoles formerTys D)
      C.majDom).instantiateList os' 0
      = Expr.mkAppN (Expr.fvar (D + t) (formerTys.getD t default))
          (fvsPref.take nP ++ ih.idx.map (·.instantiateList os' 0)) := by
    rw [← targetAbs_instantiateList hholesF hosF, hmaj os' hos', targetAbs_mkAppN, hholeT,
      List.map_append, hprefInst, hprefAbs, List.map_map]
    congr 2
    refine List.map_congr_left fun x hx => ?_
    simp only [Function.comp]
    rw [targetAbs_instantiateList hholesF hosF, C.hidxAbs x hx]
  rw [hAbsMaj] at hXr
  obtain ⟨fa, vs, hfa, hvs, rfl⟩ := denoteMeta_mkAppN_inv hXr
  rw [denoteMeta_fvar] at hfa
  obtain rfl := Option.some.inj hfa
  -- (11) the head's value: the hole's
  have hhead : interp V (consList bs (consList hv (consList (xs ++ fs) ρ)))
      (AnnotTerm.bvar (D + k + m - 1 - (D + t))) = hv.getD t pt := by
    rw [interp_bvar, show D + k + m - 1 - (D + t) = (k - 1 - t) + bs.length from by omega,
      consList_apply_add, consList_getD_of_lt _ _ _ (by omega), hvl,
      show k - 1 - (k - 1 - t) = t from by omega]
  -- (12) the spine fits the hole's type's binder data
  obtain ⟨-, -, -, T, hT, -, hvT⟩ := hformer t ht
  obtain rfl : T = mkPisAV pds R := Option.some.inj (hT.symm.trans hTt)
  have hvsLen : vs.length = pds.length := by
    rw [← hvs.length, hpdsLen, List.length_append, List.length_take, hlp, List.length_map]; omega
  have hsp := spineFit_of_wellDenoted_mkAppN_pi (σ := ρ) hpdsNZ hwdX (by rw [hhead]; exact hvT ρ)
    hvsLen
  -- (13) the spine's values: the parameters and the index readings
  have hτ : consList bs (consList hv (consList (xs ++ fs) ρ)) = consList (hv ++ bs) (consList (xs ++ fs) ρ) :=
    (consList_append hv bs _).symm
  have hvals : vs.map (interp V (consList bs (consList hv (consList (xs ++ fs) ρ))))
      = xs.take nP ++ ih.idx.map (fun x => interp V (consList bs (consList (xs ++ fs) ρ))
          ((denoteMeta mT.acval envT φ (D + m) (x.instantiateList (locOpen D m) 0)).getD
            default)) := by
    rw [spine_map_getD hvs, List.map_append]
    congr 1
    · apply List.ext_getElem (by simp [hlp, hxl])
      intro i h1 h2
      simp only [List.length_map, List.length_take] at h1
      have hi : i < rP := by omega
      obtain ⟨ty, hty⟩ := hfvPref i hi
      rw [List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)] at hty
      simp only [List.getElem_map, List.getElem_take]
      rw [Option.some.inj hty, denoteMeta_fvar, Option.getD_some, hτ,
        show D + k + m - 1 - i = D + (hv ++ bs).length - 1 - i from by
          rw [List.length_append, hvl, hbl]; omega,
        interp_frame_fvar hlenS rfl (by omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega), Option.getD_some]
    · rw [List.map_map]
      refine List.map_congr_left fun x hx => ?_
      have hxL : ∀ l ∈ x.fvarLeaves, l.1 < D :=
        leaf_lt_of_mem hL (fun l hl => List.mem_reverse.mpr (hidxL x hx l hl))
      have hd := denoteMeta_open_deepen (acval := mT.acval) (env := envT) (φ := φ) hacl k D x m
        (locOpen D m) os' hxL (locOpen_locList D m) hos'
      obtain ⟨A1, hA1⟩ := spine_reads hvs _ (List.mem_append_right _ (List.mem_map_of_mem hx))
      rw [hA1] at hd
      cases hA0 : denoteMeta mT.acval envT φ (D + m) (x.instantiateList (locOpen D m) 0) with
      | none => rw [hA0] at hd; exact nomatch hd
      | some A0 =>
        rw [hA0, Option.map_some] at hd
        simp only [Function.comp, hA1, Option.getD_some]
        rw [Option.some.inj hd, interp_liftN, shiftE_consList_ih hbl hvl]
  -- (14) the applied field's value
  have hfvF : ∃ ty, fvsF.getD ih.field default = Expr.fvar (rP + ih.field) ty := by
    have hlt : rP + ih.field < (fvsPref ++ fvsF).length := by simp [hlp, hlf]; omega
    obtain ⟨ty, hty⟩ := hL.reverse_idx (rP + ih.field) _
      (by rw [List.reverse_reverse]; exact List.getElem?_eq_getElem hlt)
    refine ⟨ty, ?_⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    rw [List.getElem_append_right (by omega)] at hty
    simpa [hlp] using hty
  obtain ⟨fty0, hfty0⟩ := hfvF
  have hfap : interp V (consList bs (consList (xs ++ fs) ρ))
      ((denoteMeta mT.acval envT φ (D + m)
        ((Expr.mkAppN (fvsF.getD ih.field default) (ConLeche.structTeleVars m)).instantiateList
          (locOpen D m) 0)).getD default)
      = bs.foldl SetTheory.app (fs.getD ih.field pt) := by
    rw [instantiateList_mkAppN, hfty0]
    simp only [Expr.instantiateList]
    rw [denoteMeta_mkAppN (denoteMetaSpine_teleVars (acval := mT.acval) (env := envT) (φ := φ)
      (locOpen_locList D m) (Nat.le_refl m)) (denoteMeta_fvar _ _ _ _), Option.getD_some,
      interp_mkAppN_foldl, map_teleVarsAV_interp' hbl,
      show D + m - 1 - (rP + ih.field) = D + bs.length - 1 - (rP + ih.field) from by rw [hbl],
      interp_frame_fvar hlenS rfl (by omega), List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega), hxl, Nat.add_sub_cancel_left,
      ← List.getD_eq_getElem?_getD]
  refine ⟨?_, ?_⟩
  · rw [← hvals]; exact hsp
  · rw [hfap, ← hvals, ← hhead, ← interp_mkAppN_foldl]
    exact hfold

end Gen

end ConLeche.Model
