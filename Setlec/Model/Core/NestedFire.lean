import Setlec.Model.Core.Certs
import Setlec.Verify.InstSpine

/-!
# The nested-rule firing premise

`nested_fire_premise` packages the semantic content of `iotaRec`'s
fire-time checks for a `.nested` rule: the level check pins the
constructor's level assignment to the stored instantiations evaluated
under the recursor's, and the parameter `defEqList` (against the
stored instantiations substituted at the argument spine,
`recFireComparands`) pins the constructor's leading argument values to
the instantiations' values — re-expressed over a sanitized
free-variable spine so the fold consumer (`modeled_rule_fold_nested`)
can cross to its own statement frame by value-determinedness.

The annotation truthfulness of the fabricated comparand expressions is
read off the recursor-type telescope walk: its residual after the
non-major arguments is a `∀` over the instantiated major-premise
domain, which *is* (`EnvWF`'s shape clause) the constructor family
applied to the stored instantiations.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

/-- An interpretation spine of well-scoped, bvar-closed arguments is an
argument spine. -/
theorem InstArgs_of_InterpSpine {cval : ConstVal V} {D : Nat}
    {ρ : Nat → V} :
    ∀ {args : List Expr} {vs : List V},
      InterpSpine cval env φ D ρ args vs →
      (∀ a ∈ args, WScoped D a) →
      (∀ a ∈ args, a.looseBVarsBounded 0 = true) →
      InstArgs cval env φ D ρ args vs
  | [], [], _, _, _ => trivial
  | _ :: _, [], h, _, _ => nomatch h
  | [], _ :: _, h, _, _ => nomatch h
  | a :: _as, _v :: _vs, ⟨hi, h'⟩, hw, hb =>
    ⟨⟨hw a List.mem_cons_self, hb a List.mem_cons_self, hi⟩,
      InstArgs_of_InterpSpine h'
        (fun x hx => hw x (List.mem_cons_of_mem _ hx))
        (fun x hx => hb x (List.mem_cons_of_mem _ hx))⟩

/-- The interpretation spine of an argument spine. -/
theorem InstArgs.interpSpine {cval : ConstVal V} {D : Nat}
    {ρ : Nat → V} :
    ∀ {args : List Expr} {vs : List V},
      InstArgs cval env φ D ρ args vs →
      InterpSpine cval env φ D ρ args vs
  | [], [], _ => trivial
  | _ :: _, [], h => nomatch h
  | [], _ :: _, h => nomatch h
  | _ :: _, _ :: _, ⟨⟨_, _, hi⟩, h'⟩ =>
    ⟨hi, InstArgs.interpSpine h'⟩

set_option maxHeartbeats 1600000 in
theorem nested_fire_premise {m : EnvModel V env} {fuel : Nat}
    (ihd : DefEqClaims m φ fuel)
    {d : Nat} {ρ : Nat → V}
    {r : RecRule} {cv cvj : ConstantVal} {mI rP : Nat}
    {us usj : List Level} {fe ae major : Expr}
    {vsi ws : List V} {tvv : V} {restR restR' : Expr}
    {dR : Nat} {ρR : Nat → V} {argsRF : List Expr}
    (hnestWF : ∀ lvls pins, r.fire = .nested lvls pins →
      mI = rP ∧
      (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
      (∀ pin ∈ pins, pin.hasFvar = false ∧
        pin.allLevelParamsDefined cv.levelParams = true ∧
        pin.constsResolve env = true ∧
        pin.looseBVarsBounded mI = true) ∧
      ∃ pre nm dom body bm D,
        cv.type.stripPis mI = some (pre, .forallE nm dom body bm) ∧
        dom.getAppFn = .const D lvls ∧
        dom.getAppArgs = pins)
    (hpeq : defEqListP env fuel d
      (major.getAppArgs.take r.ctorParams)
      (recFireComparands r cv.levelParams us cvj.levelParams
        (Expr.app fe ae).getAppArgs mI).2 = .ok true)
    (hlev : Level.isEquivList usj
      (recFireComparands r cv.levelParams us cvj.levelParams
        (Expr.app fe ae).getAppArgs mI).1 = some true)
    (husjlen : usj.length = cvj.levelParams.length)
    (hml : major.getAppArgs.length = r.ctorParams + r.nfields)
    (hvsilen : vsi.length = mI)
    (har1 : (cv.type.stripPis (mI + 1)).isSome = true)
    (htakelen : ((Expr.app fe ae).getAppArgs.take mI).length = mI)
    (hargsW : ∀ x ∈ (Expr.app fe ae).getAppArgs, WScoped d x)
    (hargsB : ∀ x ∈ (Expr.app fe ae).getAppArgs,
      x.looseBVarsBounded 0 = true)
    (hargsL : ∀ x ∈ (Expr.app fe ae).getAppArgs, Expr.LeavesBounded x)
    (hargsO : ∀ x ∈ (Expr.app fe ae).getAppArgs,
      FvarsOk V m.val env φ d ρ x)
    (hmajW : WScoped d major)
    (hmajB : major.looseBVarsBounded 0 = true)
    (hmajL : Expr.LeavesBounded major)
    (hmajO : FvarsOk V m.val env φ d ρ major)
    (hmxsA : ∀ x ∈ major.getAppArgs, AnnotOk V m.val env φ d ρ x)
    (hmsp : InterpSpine m.val env φ d ρ major.getAppArgs ws)
    (hspi : InterpSpine m.val env φ d ρ
      ((Expr.app fe ae).getAppArgs.take mI) vsi)
    (hRw : WScoped d (cv.type.instantiateLevelParams cv.levelParams us))
    (hRb : (cv.type.instantiateLevelParams cv.levelParams
      us).looseBVarsBounded 0 = true)
    (hRA : AnnotOk V m.val env φ d ρ
      (cv.type.instantiateLevelParams cv.levelParams us))
    (hRhf : (cv.type.instantiateLevelParams cv.levelParams
      us).hasFvar = false)
    (hfitIR : TeleFitI V m.val env φ d ρ
      (cv.type.instantiateLevelParams cv.levelParams us)
      ((Expr.app fe ae).getAppArgs.take mI ++ [major])
      (vsi ++ [tvv]) restR)
    (hdR : d ≤ dR)
    (hagrR : ∀ i, i < d → ρR i = ρ i)
    (hfitRF : TeleFitI V m.val env φ dR ρR
      (cv.type.instantiateLevelParams cv.levelParams us)
      argsRF (vsi ++ [tvv]) restR')
    (hfvRF : ∀ a ∈ argsRF, ∃ i n ty, a = .fvar i n ty) :
    ∀ lvls pins, r.fire = RecRuleFire.nested lvls pins →
      mI = rP ∧
      (∀ p ∈ cvj.levelParams,
        Level.substFn φ cvj.levelParams usj p =
        Level.substFn (Level.substFn φ cv.levelParams us)
          cvj.levelParams lvls p) ∧
      ∃ (dP : Nat) (ρP : Nat → V) (spineP : List Expr),
        FvarSpine dP ρP spineP vsi ∧
        (∀ a ∈ spineP, ∃ i nm, a = Expr.fvar i nm (.sort .zero)) ∧
        (pins.map fun pin => Expr.instSeq spineP (spineP.length - 1)
          (pin.instantiateLevelParams cv.levelParams us)).mapM
          (interpExpr V m.val env φ dP ρP) =
          some (ws.take r.ctorParams) := by
  intro lvls pins hfp
  obtain ⟨hmIrP, hlvlsWF, hpinsWF, pre, nmD, dom, bodyD, bmD, D,
    hstripD, hdomFn, hdomArgs⟩ := hnestWF lvls pins hfp
  -- the kernel comparands specialized to the nested mode
  have hlev' : Level.isEquivList usj
      (lvls.map (Level.subst cv.levelParams us)) = some true := by
    have h0 := hlev
    simp only [recFireComparands, hfp] at h0
    exact h0
  have hpeq' : defEqListP env fuel d
      (major.getAppArgs.take r.ctorParams)
      (pins.map fun pin => Expr.instSeq
        ((Expr.app fe ae).getAppArgs.take mI) (mI - 1)
        (pin.instantiateLevelParams cv.levelParams us)) = .ok true := by
    have h0 := hpeq
    simp only [recFireComparands, hfp] at h0
    rw [show (pins.map fun pin => Expr.instSpine
        ((Expr.app fe ae).getAppArgs.take mI) (mI - 1)
        (pin.instantiateLevelParams cv.levelParams us)) =
        (pins.map fun pin => Expr.instSeq
          ((Expr.app fe ae).getAppArgs.take mI) (mI - 1)
          (pin.instantiateLevelParams cv.levelParams us)) from
      List.map_congr_left fun pin _ =>
        Expr.instSpine_eq_instSeq _ _ _] at h0
    exact h0
  refine ⟨hmIrP, ?_, ?_⟩
  · -- the constructor's level assignment is the stored instantiations
    -- evaluated under the recursor's
    intro p hp
    have hlen1 : lvls.length = cvj.levelParams.length := by
      rw [← husjlen, Level.isEquivList_length hlev', List.length_map]
    have h1 : Level.substFn φ cvj.levelParams usj =
        Level.substFn φ cvj.levelParams
          (lvls.map (Level.subst cv.levelParams us)) :=
      Level.substFn_congr (Level.isEquivList_sound hlev' φ)
    have h3 := Level.substFn_map_subst (φ := φ) (ks := cv.levelParams)
      (vs := us) (ks' := cvj.levelParams) (ws := lvls) hlen1 hp
    rw [h1, h3]
  -- ===== the parameter values =====
  generalize hargsEdef : (Expr.app fe ae).getAppArgs.take mI = argsE
    at hpeq' htakelen hspi hfitIR
  have hargsEW : ∀ x ∈ argsE, WScoped d x := by
    rw [← hargsEdef]
    exact fun x hx => hargsW x (List.mem_of_mem_take hx)
  have hargsEB : ∀ x ∈ argsE, x.looseBVarsBounded 0 = true := by
    rw [← hargsEdef]
    exact fun x hx => hargsB x (List.mem_of_mem_take hx)
  -- the comparand list
  generalize hcmpdef : (pins.map fun pin => Expr.instSeq argsE (mI - 1)
    (pin.instantiateLevelParams cv.levelParams us)) = cmp at hpeq'
  have hpinslen : pins.length = r.ctorParams := by
    have h0 := defEqList_length _ _ hpeq'
    rw [← hcmpdef, List.length_take, hml, List.length_map] at h0
    omega
  -- ===== the recursor walk's residual over the major domain =====
  obtain ⟨prI, hstripI1'⟩ := Option.isSome_iff_exists.mp
    (stripPis_instantiateLevelParams_isSome cv.levelParams us _ har1)
  obtain ⟨bsI, bodyI⟩ := prI
  have hstripI1 : (cv.type.instantiateLevelParams cv.levelParams
      us).stripPis (mI + 1) = some (bsI, bodyI) := hstripI1'
  obtain ⟨nx, dx, mx, hbsImI, hstripImI⟩ := Expr.stripPis_snoc mI hstripI1
  -- transport the `mI`-strip through the level instantiation:
  -- the instantiated major domain is the stored domain's instantiation
  have hstripInst : (cv.type.instantiateLevelParams cv.levelParams
      us).stripPis mI = some (bsI.take mI, .forallE nx dx bodyI mx) :=
    hstripImI
  obtain ⟨hbodyEq, -⟩ := stripPis_instantiateLevelParams_eq
    cv.levelParams us mI hstripD hstripInst
  have hdx : dx = dom.instantiateLevelParams cv.levelParams us := by
    simp only [Expr.instantiateLevelParams] at hbodyEq
    injection hbodyEq
  -- the prefix fit and its residual
  obtain ⟨midM, hfitPre⟩ := TeleFitI.take_prefix hfitIR
  have hvspre : (vsi ++ [tvv]).take argsE.length = vsi := by
    rw [htakelen, List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
  rw [hvspre] at hfitPre
  obtain ⟨mid₂, hmid₂, bs', body', hstrip1, hbody', hdomInst⟩ :=
    telescopeInst_stripPis mI argsE 1 htakelen hstripI1
  have hmidEq : midM = mid₂ := by
    have h0 := TeleFitI.rest_eq hfitPre
    rw [h0] at hmid₂
    exact Option.some.inj hmid₂
  -- `mid₂` is a `∀` over the instantiated domain
  obtain ⟨n0, d0, b0, m0, rfl⟩ :
      ∃ n0 d0 b0 m0, mid₂ = .forallE n0 d0 b0 m0 := by
    match mid₂, hstrip1 with
    | .forallE n0 d0 b0 m0, _ => exact ⟨n0, d0, b0, m0, rfl⟩
  have hbs'0 : bs' = [(n0, d0, m0)] ∧ body' = b0 := by
    simp only [Expr.stripPis, Option.map, Option.some.injEq,
      Prod.mk.injEq] at hstrip1
    exact ⟨hstrip1.1.symm, hstrip1.2.symm⟩
  have hd0 : d0 = Expr.instSeq argsE (mI + 0 - 1) dx := by
    refine hdomInst 0 (nx, dx, mx) (n0, d0, m0) (by simpa using hbsImI)
      ?_
    rw [hbs'0.1]
    rfl
  -- the domain as the constructor family over the comparand
  have hdomEq : dom = Expr.mkAppN (.const D lvls) pins := by
    have h0 := (Expr.mkAppN_getApp dom).symm
    rw [hdomFn, hdomArgs] at h0
    exact h0
  have hd0spine : d0 = Expr.mkAppN
      (.const D (lvls.map (Level.subst cv.levelParams us))) cmp := by
    rw [hd0, hdx, hdomEq,
      instantiateLevelParams_mkAppN cv.levelParams us pins,
      instSeq_mkAppN]
    congr 1
    · show Expr.instSeq argsE (mI + 0 - 1)
        (.const D (lvls.map (Level.subst cv.levelParams us))) = _
      exact instSeq_eq_self _ _ (by simp [Expr.looseBVarsBounded])
    · rw [← hcmpdef, List.map_map]
      refine List.map_congr_left ?_
      intro pin _
      simp only [Function.comp, Nat.add_zero]
  -- annotation truthfulness and interpretations of the comparand,
  -- read off the residual's domain
  obtain ⟨hmidW, hmidB, hmidA, -⟩ := TeleFitI.rest_wf hfitPre hRw hRb hRA
  rw [hmidEq] at hmidW hmidB hmidA
  have hd0A : AnnotOk V m.val env φ d ρ d0 := by
    have h0 := hmidA
    simp only [AnnotOk] at h0
    exact h0.1
  have hd0W : WScoped d d0 := by
    have h0 := hmidW
    simp only [WScoped] at h0
    exact h0.1
  have hd0B : d0.looseBVarsBounded 0 = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hmidB
    exact hmidB.1
  have hd0args : d0.getAppArgs = cmp := by
    rw [hd0spine, Expr.getAppArgs_mkAppN]
    simp [Expr.getAppArgs]
  -- fvar leaves and free-variable facts of the residual (hence of the
  -- domain): the walked type is closed, so leaves come from the spine
  obtain ⟨-, -, -, hmidLv⟩ := TeleFitI.rest_wf hfitPre hRw hRb hRA
  rw [hmidEq] at hmidLv
  have hd0Lsub : ∀ l ∈ d0.fvarLeaves,
      ∃ a ∈ argsE, l ∈ a.fvarLeaves := by
    intro l hl
    have hl' : l ∈ (Expr.forallE n0 d0 b0 m0).fvarLeaves := by
      simp only [Expr.fvarLeaves, List.mem_append]
      exact Or.inl hl
    rcases hmidLv l hl' with hl'' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hRhf] at hl''
      exact absurd hl'' (List.not_mem_nil)
    · exact ⟨a, ha, hla⟩
  have hargsEL : ∀ x ∈ argsE, Expr.LeavesBounded x := by
    rw [← hargsEdef]
    exact fun x hx => hargsL x (List.mem_of_mem_take hx)
  have hargsEO : ∀ x ∈ argsE, FvarsOk V m.val env φ d ρ x := by
    rw [← hargsEdef]
    exact fun x hx => hargsO x (List.mem_of_mem_take hx)
  have hd0L : Expr.LeavesBounded d0 := by
    intro l hl
    obtain ⟨a, ha, hla⟩ := hd0Lsub l hl
    exact hargsEL a ha l hla
  have hd0O : FvarsOk V m.val env φ d ρ d0 := by
    intro l hl
    obtain ⟨a, ha, hla⟩ := hd0Lsub l hl
    exact hargsEO a ha l hla
  -- ===== the sanitized witness spine =====
  have hFvFull : FvarSpine dR ρR argsRF (vsi ++ [tvv]) :=
    FvarSpine_of_fit hfitRF hfvRF
  have hlenRF : argsRF.length = mI + 1 := by
    have h0 := (TeleFitI.vs_length hfitRF).symm
    rw [List.length_append, hvsilen] at h0
    simpa using h0
  have hFvPre : FvarSpine dR ρR (argsRF.take mI) vsi := by
    have h0 := FvarSpine.take (D := dR) (ρ := ρR) mI hFvFull
    rw [show (vsi ++ [tvv]).take mI = vsi from by
      rw [List.take_append_of_le_length (by omega),
        List.take_of_length_le (by omega)]] at h0
    exact h0
  have hFvS : FvarSpine dR ρR ((argsRF.take mI).map sanitizeArg) vsi :=
    FvarSpine.sanitize hFvPre
  have hshS : ∀ a ∈ (argsRF.take mI).map sanitizeArg,
      ∃ i nm, a = Expr.fvar i nm (.sort .zero) :=
    FvarSpine.sanitize_shapes hFvPre
  have hspinePlen : ((argsRF.take mI).map sanitizeArg).length = mI := by
    rw [List.length_map, List.length_take, hlenRF]
    omega
  refine ⟨dR, ρR, (argsRF.take mI).map sanitizeArg, hFvS, hshS, ?_⟩
  by_cases hpins0 : pins = []
  · -- no parameters: the value list is empty
    subst hpins0
    have hctor0 : r.ctorParams = 0 := by simpa using hpinslen.symm
    simp [hctor0]
  -- ===== the comparand's values =====
  have hcmpne : cmp ≠ [] := by
    rw [← hcmpdef]
    simp only [ne_eq, List.map_eq_nil_iff]
    exact hpins0
  have hd0A' : AnnotOk V m.val env φ d ρ (Expr.mkAppN
      (.const D (lvls.map (Level.subst cv.levelParams us))) cmp) :=
    hd0spine ▸ hd0A
  obtain ⟨-, hcmpA, vD, pvals, hivD, hcmpSp, -, -⟩ :=
    annotOk_spine_inv _ _ hcmpne hd0A'
  have hcmpW : ∀ x ∈ cmp, WScoped d x := by
    intro x hx
    exact hd0W.getAppArgs x (hd0args ▸ hx)
  have hcmpB : ∀ x ∈ cmp, x.looseBVarsBounded 0 = true := by
    intro x hx
    exact looseBVarsBounded_getAppArgs hd0B x (hd0args ▸ hx)
  have hcmpL : ∀ x ∈ cmp, Expr.LeavesBounded x := by
    intro x hx
    intro l hl
    exact hd0L l (fvarLeaves_getAppArgs (hd0args ▸ hx) l hl)
  have hcmpO : ∀ x ∈ cmp, FvarsOk V m.val env φ d ρ x := by
    intro x hx
    exact FvarsOk.of_subset
      (fun l hl => fvarLeaves_getAppArgs (hd0args ▸ hx) l hl) hd0O
  -- the comparand's values are the constructor's parameter values
  have hpvals : ws.take r.ctorParams = pvals := by
    refine defEqList_values ihd _ _ _ _ hpeq' ?_ ?_
      (InterpSpine.take _ hmsp) hcmpSp
    · intro x hx
      have hxm := List.mem_of_mem_take hx
      exact ⟨hmajW.getAppArgs _ hxm,
        looseBVarsBounded_getAppArgs hmajB _ hxm,
        fun l hl => hmajL l (fvarLeaves_getAppArgs hxm l hl),
        FvarsOk.of_subset
          (fun l hl => fvarLeaves_getAppArgs hxm l hl) hmajO,
        hmxsA _ hxm⟩
    · intro x hx
      exact ⟨hcmpW x hx, hcmpB x hx, hcmpL x hx, hcmpO x hx, hcmpA x hx⟩
  -- ===== transport to the witness frame =====
  have hcmpInst : InstArgs m.val env φ d ρ cmp pvals :=
    InstArgs_of_InterpSpine hcmpSp hcmpW hcmpB
  have hcmpInstR : InstArgs m.val env φ dR ρR cmp pvals :=
    InstArgs.lift hcmpInst hdR hagrR
  have hargsEInst : InstArgs m.val env φ d ρ argsE vsi :=
    InstArgs_of_InterpSpine hspi hargsEW hargsEB
  have hargsEInstR : InstArgs m.val env φ dR ρR argsE vsi :=
    InstArgs.lift hargsEInst hdR hagrR
  have hspSInst : InstArgs m.val env φ dR ρR
      ((argsRF.take mI).map sanitizeArg) vsi :=
    InstArgs_of_FvarSpine_sanitized hFvS hshS
  -- the mapped instantiations interpret to the parameter values,
  -- elementwise via the value-determinedness of instantiation
  rw [hpvals]
  have hconvP : ∀ (l : List Expr) (vs0 : List V),
      (∀ pin ∈ l, pin ∈ pins) →
      InterpSpine m.val env φ dR ρR
        (l.map fun pin => Expr.instSeq argsE (mI - 1)
          (pin.instantiateLevelParams cv.levelParams us)) vs0 →
      InterpSpine m.val env φ dR ρR
        (l.map fun pin => Expr.instSeq
          ((argsRF.take mI).map sanitizeArg)
          (((argsRF.take mI).map sanitizeArg).length - 1)
          (pin.instantiateLevelParams cv.levelParams us)) vs0 := by
    intro l
    induction l with
    | nil =>
      intro vs0 _ hs
      match vs0, hs with
      | [], _ => trivial
    | cons pin l ihl =>
      intro vs0 hmem hs
      match vs0, hs with
      | v :: vs0, ⟨hix, hrest⟩ =>
        refine ⟨?_, ihl vs0
          (fun y hy => hmem y (List.mem_cons_of_mem _ hy)) hrest⟩
        have hpinmem := hmem pin List.mem_cons_self
        obtain ⟨hpinF, -, -, hpinB⟩ := hpinsWF pin hpinmem
        have hpinF' : (pin.instantiateLevelParams cv.levelParams
            us).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]
          exact hpinF
        have hpinB' : (pin.instantiateLevelParams cv.levelParams
            us).looseBVarsBounded
            ((argsRF.take mI).map sanitizeArg).length = true := by
          rw [hspinePlen, looseBVarsBounded_instantiateLevelParams]
          exact hpinB
        have hcongr := interp_instSeq_congr hspSInst hargsEInstR
          (WScoped.of_not_hasFvar (d := dR) hpinF').fvarsBelow hpinB'
        rw [show argsE.length - 1 = mI - 1 from by rw [htakelen]]
          at hcongr
        rw [hcongr]
        exact hix
  have hspineM : InterpSpine m.val env φ dR ρR
      (pins.map fun pin => Expr.instSeq argsE (mI - 1)
        (pin.instantiateLevelParams cv.levelParams us)) pvals := by
    -- `InstArgs` at the lifted frame projects to the interpretations
    clear hconvP
    rw [hcmpdef]
    exact InstArgs.interpSpine hcmpInstR
  exact InterpSpine.mapM_eq (hconvP pins pvals (fun _ h => h) hspineM)
