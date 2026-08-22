import Setlec.Model.IndInstall
import Setlec.Verify.InstSpine

/-!
# Fold facts for a modeled recursor: nested-auxiliary rules

`modeled_rule_fold_nested` derives the `RecRulesOk` fold obligation of
a *nested-auxiliary* recursor rule (task #48) from the checked
`R._model.iota_j` theorem, mirroring `modeled_rule_fold`
(`Setlec/Model/IndInstall.lean`).  The constructor's parameters are
fixed instantiations (`pins`, opened at the statement's prefix
variables) and its levels the stored `lvls`, so the constructor-side
spine is *not* a free-variable spine: the walks and membership
transfers are generalized from `FvarSpine` to `InstArgs`
(`fit_mem_transferI`, `peel_walkI`), with a fresh-frame detour
(`exists_fvarSpine_ext`) crossing between the fit's opening frame and
the theorem's master frame by value-determinedness.  The pin entries'
annotation truthfulness comes from the recursor type's own walked
residual (the major premise's domain *is* the constructor's type
former applied to the pins).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {cval : ConstVal V} {env : Env}
  {φ : Name → Nat}

open SetTheory Expr

/-- Any value list is carried by a fresh sanitized free-variable spine
on some extension of a given frame. -/
theorem exists_fvarSpine_ext {V : Type u} (D : Nat) (ρ : Nat → V) :
    ∀ vs : List V, ∃ (D' : Nat) (ρ' : Nat → V) (spine : List Expr),
      D ≤ D' ∧ (∀ i, i < D → ρ' i = ρ i) ∧
      (∀ a ∈ spine, ∃ i n, a = Expr.fvar i n (.sort .zero)) ∧
      FvarSpine D' ρ' spine vs
  | [] => by
    refine ⟨D, ρ, [], Nat.le_refl _, fun _ _ => rfl, ?_, trivial⟩
    intro a ha
    exact absurd ha List.not_mem_nil
  | v :: vs => by
    obtain ⟨D', ρ', spine', hle, hag, hsh, hsp⟩ :=
      exists_fvarSpine_ext (D + 1) (fun j => if j = D then v else ρ j) vs
    refine ⟨D', ρ', .fvar D .anonymous (.sort .zero) :: spine',
      by omega, ?_, ?_, ?_⟩
    · intro i hi
      rw [hag i (by omega)]
      exact if_neg (by omega)
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨D, .anonymous, rfl⟩
      · exact hsh a ha
    · refine ⟨⟨D, .anonymous, .sort .zero, rfl, by omega, ?_⟩, hsp⟩
      rw [hag D (by omega)]
      simp

/-- Pointwise construction of an argument spine. -/
theorem InstArgs.of_pointwise {D : Nat} {ρ : Nat → V} :
    ∀ {args : List Expr} {vs : List V},
      args.length = vs.length →
      (∀ (k : Nat) (a : Expr) (v : V), args[k]? = some a →
        vs[k]? = some v →
        WScoped D a ∧ a.looseBVarsBounded 0 = true ∧
        interpExpr V cval env φ D ρ a = some v) →
      InstArgs cval env φ D ρ args vs
  | [], [], _, _ => trivial
  | [], _ :: _, h, _ => nomatch h
  | _ :: _, [], h, _ => nomatch h
  | a :: as, v :: vs, hlen, hpt =>
    ⟨hpt 0 a v rfl rfl,
     InstArgs.of_pointwise (by simpa using hlen)
       (fun k a' v' ha hv => hpt (k + 1) a' v' (by simpa using ha)
         (by simpa using hv))⟩

/-- Concatenate two argument spines. -/
theorem InstArgs.append {D : Nat} {ρ : Nat → V} :
    ∀ {as₁ as₂ : List Expr} {vs₁ vs₂ : List V},
      InstArgs cval env φ D ρ as₁ vs₁ →
      InstArgs cval env φ D ρ as₂ vs₂ →
      InstArgs cval env φ D ρ (as₁ ++ as₂) (vs₁ ++ vs₂)
  | [], _, [], _, _, h₂ => h₂
  | [], _, _ :: _, _, h₁, _ => nomatch h₁
  | _ :: _, _, [], _, h₁, _ => nomatch h₁
  | _ :: _, _, _ :: _, _, h₁, h₂ => ⟨h₁.1, InstArgs.append h₁.2 h₂⟩

/-- A free-variable spine with well-formed entries is an argument
spine. -/
theorem InstArgs_of_FvarSpine {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V}, FvarSpine D ρ as vs →
      (∀ a ∈ as, WScoped D a ∧ a.looseBVarsBounded 0 = true) →
      InstArgs cval env φ D ρ as vs
  | [], [], _, _ => trivial
  | _ :: _, [], h, _ => nomatch h
  | [], _ :: _, h, _ => nomatch h
  | a :: as, v :: vs, h, hwf => by
    obtain ⟨⟨i, n, ty, rfl, hiD, hv⟩, h'⟩ := h
    obtain ⟨hw, hb⟩ := hwf _ List.mem_cons_self
    exact ⟨⟨hw, hb, by simp only [interpExpr]; rw [hv]⟩,
      InstArgs_of_FvarSpine h'
        (fun b hb' => hwf b (List.mem_cons_of_mem _ hb'))⟩

/-- An argument spine interprets pointwise to its values. -/
theorem InstArgs.toInterpSpine {D : Nat} {ρ : Nat → V} :
    ∀ {as : List Expr} {vs : List V},
      InstArgs cval env φ D ρ as vs → InterpSpine cval env φ D ρ as vs
  | [], [], _ => trivial
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | _ :: _, _ :: _, h => ⟨h.1.2.2, InstArgs.toInterpSpine h.2⟩

omit [SetTheory V] in
/-- `instSeq` keeps terms well-scoped (the `instSpine` fact under the
verification spelling). -/
theorem instSeq_wscoped {D : Nat} {args : List Expr} (t : Nat) {e : Expr}
    (he : WScoped D e) (hargs : ∀ a ∈ args, WScoped D a) :
    WScoped D (instSeq args t e) := by
  rw [← Expr.instSpine_eq_instSeq]
  exact instSpine_WScoped t he hargs

omit [SetTheory V] in
/-- A full-telescope `instSeq` at bvar-closed arguments closes a
bounded base. -/
theorem instSeq_bclosed {args : List Expr} {e : Expr}
    (hargs : ∀ a ∈ args, a.looseBVarsBounded 0 = true)
    (he : e.looseBVarsBounded args.length = true) :
    (instSeq args (args.length - 1) e).looseBVarsBounded 0 = true := by
  rw [← Expr.instSpine_eq_instSeq]
  exact instSpine_closed hargs he

/-- Components of an application spine inherit `AnnotOk`. -/
theorem annotOk_appN_parts {D : Nat} {ρ : Nat → V} :
    ∀ (xs : List Expr) (h : Expr),
      AnnotOk V cval env φ D ρ (Expr.mkAppN h xs) →
      AnnotOk V cval env φ D ρ h ∧
        ∀ x ∈ xs, AnnotOk V cval env φ D ρ x
  | [], _, hA => ⟨hA, fun _ hx => nomatch hx⟩
  | x :: xs, h, hA => by
    obtain ⟨hhx, hrest⟩ := annotOk_appN_parts xs (.app h x)
      (show AnnotOk V cval env φ D ρ (Expr.mkAppN (.app h x) xs) from hA)
    have hhx' : AnnotOk V cval env φ D ρ h ∧
        AnnotOk V cval env φ D ρ x := by
      simp only [AnnotOk] at hhx
      exact ⟨hhx.1, hhx.2.1⟩
    refine ⟨hhx'.1, ?_⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hhx'.2
    · exact hrest y hy

/-- Definedness of the head from a defined application-spine
interpretation. -/
theorem interp_mkAppN_head_some {D : Nat} {ρ : Nat → V} :
    ∀ (xs : List Expr) (h : Expr) {w : V},
      interpExpr V cval env φ D ρ (Expr.mkAppN h xs) = some w →
      ∃ vh, interpExpr V cval env φ D ρ h = some vh
  | [], _, w, hi => ⟨w, hi⟩
  | x :: xs, h, w, hi => by
    obtain ⟨v', hv'⟩ := interp_mkAppN_head_some xs (.app h x)
      (show interpExpr V cval env φ D ρ (Expr.mkAppN (.app h x) xs) =
        some w from hi)
    revert hv'
    simp only [interpExpr]
    cases hf : interpExpr V cval env φ D ρ h with
    | none =>
      cases ha : interpExpr V cval env φ D ρ x with
      | none => intro hv'; exact nomatch hv'
      | some va => intro hv'; exact nomatch hv'
    | some vh => intro _; exact ⟨vh, rfl⟩

/-- `fit_mem_transfer` generalized to an arbitrary target spine
(`InstArgs`): pointwise memberships in a closed telescope's
instantiated domains — given at a free-variable frame along the
stripped binders — transfer onto any argument spine with the same
values at another frame.  The frames are bridged through a fresh
free-variable spine carrying the values (`exists_fvarSpine_ext`), the
in-frame swap being `interp_instSeq_congr` (value-determinedness). -/
theorem fit_mem_transferI {D₁ D₂ : Nat} {ρ₁ ρ₂ : Nat → V}
    {ty : Expr} {n : Nat} {bs : List (Name × Expr × BinderMeta)}
    {body : Expr} {spine₁ : List Expr} {ds₁ : List Expr} {rest₁ : Expr}
    {spine₂ : List Expr} {vs : List V}
    (hcl : ty.hasFvar = false)
    (hty0 : ty.looseBVarsBounded 0 = true)
    (hstrip : ty.stripPis n = some (bs, body))
    (hinst₁ : Expr.instPisAt spine₁ ty = some (ds₁, rest₁))
    (hlen₁ : spine₁.length = n)
    (hargs₁ : InstArgs cval env φ D₁ ρ₁ spine₁ vs)
    (hsp₂ : FvarSpine D₂ ρ₂ spine₂ vs)
    (hmem₂ : ∀ (k : Nat) (b : Name × Expr × BinderMeta) (v : V),
      bs[k]? = some b → vs[k]? = some v →
      ∃ B, interpExpr V cval env φ D₂ ρ₂
        (instSeq (spine₂.take k) (k - 1) b.2.1) = some B ∧ v ∈ˢ B) :
    ∀ (k : Nat) (a : Expr) (v : V), ds₁[k]? = some a → vs[k]? = some v →
      ∃ B, interpExpr V cval env φ D₁ ρ₁ a = some B ∧ v ∈ˢ B := by
  have hvslen : vs.length = n := by
    rw [← InstArgs.length hargs₁, hlen₁]
  have hlen₂ : spine₂.length = n := by
    rw [FvarSpine.length hsp₂, hvslen]
  obtain ⟨-, hds₁⟩ := instPisAt_stripPis spine₁ hinst₁
    (by rw [hlen₁]; exact hstrip)
  intro k a v ha hv
  have hkn : k < n := by
    have hdl := instPisAt_length spine₁ hinst₁
    rcases Nat.lt_or_ge k n with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none (by omega)] at ha
      exact nomatch ha
  obtain ⟨b, hb⟩ : ∃ b, bs[k]? = some b := by
    have := Expr.stripPis_length n hstrip
    exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have ha' := hds₁ k b hb
  rw [ha] at ha'
  obtain rfl := Option.some.inj ha'
  obtain ⟨B, hBi, hvB⟩ := hmem₂ k b v hb hv
  have hdomcl : b.2.1.hasFvar = false :=
    stripPis_doms_hasFvar n hstrip hcl b (List.mem_of_getElem? hb)
  have hdombd : b.2.1.looseBVarsBounded k = true := by
    have := stripPis_doms_bounded n 0 hstrip hty0 k b hb
    simpa using this
  obtain ⟨D', ρ', fvsM, hle, hag, hshM, hspM⟩ :=
    exists_fvarSpine_ext D₁ ρ₁ vs
  have hfvsMlen : fvsM.length = n := by
    rw [FvarSpine.length hspM, hvslen]
  have ht1 : (spine₁.take k).length = k := by
    rw [List.length_take]; omega
  have ht2 : (spine₂.take k).length = k := by
    rw [List.length_take]; omega
  have htM : (fvsM.take k).length = k := by
    rw [List.length_take]; omega
  -- cross the source frame to the fresh spine
  have hcross : interpExpr V cval env φ D₂ ρ₂
      (instSeq (spine₂.take k) (k - 1) b.2.1) =
      interpExpr V cval env φ D' ρ'
      (instSeq (fvsM.take k) (k - 1) b.2.1) := by
    have h0 := interp_instSeq_fvarFrames (cval := cval) (env := env)
      (φ := φ) (e := b.2.1) hdomcl (by rw [ht2]; exact hdombd)
      (FvarSpine.take k hsp₂) (FvarSpine.take k hspM)
    rwa [ht2, htM] at h0
  -- swap the fresh spine for the argument spine (same frame, values)
  have hIA1 : InstArgs cval env φ D' ρ' (spine₁.take k) (vs.take k) :=
    InstArgs.lift (InstArgs.take k hargs₁) hle hag
  have hIAM : InstArgs cval env φ D' ρ' (fvsM.take k) (vs.take k) :=
    InstArgs_of_FvarSpine_sanitized (FvarSpine.take k hspM)
      (fun x hx => hshM x (List.mem_of_mem_take hx))
  have hswap : interpExpr V cval env φ D' ρ'
      (instSeq (spine₁.take k) (k - 1) b.2.1) =
      interpExpr V cval env φ D' ρ'
      (instSeq (fvsM.take k) (k - 1) b.2.1) := by
    have h0 := interp_instSeq_congr hIA1 hIAM
      (WScoped.of_not_hasFvar hdomcl).fvarsBelow
      (by rw [ht1]; exact hdombd)
    rwa [ht1, htM] at h0
  -- drop back to the base frame
  have hWinst : WScoped D₁ (instSeq (spine₁.take k) (k - 1) b.2.1) :=
    instSeq_wscoped _ (WScoped.of_not_hasFvar hdomcl)
      (fun x hx => InstArgs.wscoped hargs₁ x (List.mem_of_mem_take hx))
  have hlift : interpExpr V cval env φ D' ρ'
      (instSeq (spine₁.take k) (k - 1) b.2.1) =
      interpExpr V cval env φ D₁ ρ₁
      (instSeq (spine₁.take k) (k - 1) b.2.1) :=
    interp_lift hWinst D' hle ρ₁ ρ' hag
  refine ⟨B, ?_, hvB⟩
  rw [← hlift, hswap, ← hcross]
  exact hBi

/-- `peel_walk` generalized to an arbitrary argument spine
(`InstArgs`) with per-entry annotation truthfulness: build a
`∀`-telescope fit from pointwise memberships in the walk's own
(instantiated) domains. -/
theorem peel_walkI {φ : Name → Nat} {D : Nat} {ρ : Nat → V} :
    ∀ {spine : List Expr} {vs : List V} {ty : Expr} {ds : List Expr}
      {rest : Expr},
      Expr.instPisAt spine ty = some (ds, rest) →
      InstArgs cval env φ D ρ spine vs →
      (∀ a ∈ spine, AnnotOk V cval env φ D ρ a) →
      WScoped D ty →
      AnnotOk V cval env φ D ρ ty →
      (∃ P, interpExpr V cval env φ D ρ ty = some P) →
      (∀ (k : Nat) (a : Expr) (v : V), ds[k]? = some a →
        vs[k]? = some v →
        ∃ B, interpExpr V cval env φ D ρ a = some B ∧ v ∈ˢ B) →
      TeleFitI V cval env φ D ρ ty spine vs rest ∧
      (∃ P', interpExpr V cval env φ D ρ rest = some P') := by
  intro spine
  induction spine with
  | nil =>
    intro vs ty ds rest hop hargs hAs hW hA hI hmem
    simp only [Expr.instPisAt, Option.some.injEq, Prod.mk.injEq] at hop
    obtain ⟨-, rfl⟩ := hop
    match vs, hargs with
    | [], _ => exact ⟨TeleFitI.nil, hI⟩
  | cons a0 spine' ih =>
    intro vs ty ds rest hop hargs hAs hW hA hI hmem
    match vs, hargs with
    | v :: vs', hargs => ?_
    obtain ⟨⟨hwa, hba, hia⟩, hargs'⟩ := hargs
    obtain ⟨n, dom, bodyT, m, ds', rfl, rfl, h0⟩ := instPisAt_cons_inv hop
    have hWd : WScoped D dom ∧ WScoped D bodyT := by
      simpa [WScoped] using hW
    have hA' := hA
    simp only [AnnotOk] at hA'
    obtain ⟨hAdom, ⟨cod, hcod⟩, hcond⟩ := hA'
    obtain ⟨B, hBi, hvB⟩ := hmem 0 dom v rfl rfl
    have hAa0 : AnnotOk V cval env φ D ρ a0 := hAs _ List.mem_cons_self
    obtain ⟨hAop, hfib⟩ := hcond v B hBi hvB
    have hAbody : AnnotOk V cval env φ D ρ (bodyT.instantiate1 a0) :=
      AnnotOk_beta hWd.2.fvarsBelow hwa hba hia hAa0 0 hAop
    obtain ⟨w, hwi, -⟩ := hfib cod hcod
    have hIbody : ∃ P, interpExpr V cval env φ D ρ
        (bodyT.instantiate1 a0) = some P := by
      refine ⟨w, ?_⟩
      rw [interp_beta (n := n) (ty := dom) hWd.2.fvarsBelow hwa hba hia 0]
      exact hwi
    obtain ⟨hfit, hIrest⟩ := ih h0 hargs'
      (fun x hx => hAs x (List.mem_cons_of_mem _ hx))
      (WScoped.instantiate1_gen hwa 0 hWd.2) hAbody hIbody
      (fun k x v' hx hv' => hmem (k + 1) x v'
        (show (dom :: ds')[k + 1]? = some x from by simpa using hx)
        (show (v :: vs')[k + 1]? = some v' from by simpa using hv'))
    exact ⟨TeleFitI.cons hBi hia hvB hWd.2.fvarsBelow hwa hba hAa0 hfit,
      hIrest⟩

set_option maxHeartbeats 12800000 in
/-- The nested-auxiliary analogue of `modeled_rule_fold`: the rule's
constructor is applied at the stored level instantiations `lvls` to
the stored parameter instantiations `pins` (opened at the statement's
prefix variables) instead of the leading telescope variables;
certified only in the index-free shape (`mI = rP`).  The firing
premises (`hleveqN`, `hpinsVal`) are the `RecRulesOk` fold clause's
nested conjunct. -/
theorem modeled_rule_fold_nested
    {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat) {φ' : Name → Nat}
    {f : Name → Name}
    (hro : RenameOk m₀.val env₀ f)
    (hcvp : ConstValParams m₀.val env₀)
    -- the recursor and its model
    {R : Name} {lps : List Name} {tyA : Expr}
    {mI rP : Nat}
    {cim : ConstantInfo}
    (hfRm : env₀.find? (f R) = some cim)
    (hRmlps : cim.toConstantVal.levelParams = lps)
    -- the constructor and its model
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    (hfj : env₀.find? ctor = some (.ctorInfo cvj cnP cnF))
    {cimC : ConstantInfo}
    (hfCm : env₀.find? (f ctor) = some cimC)
    (hCmlps : cimC.toConstantVal.levelParams = cvj.levelParams)
    -- the pinned equality former
    (heqfind : env₀.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'')
    -- the iota theorem's semantic facts
    {cvt : ConstantVal} {thmName : Name}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ P,
      interpClosed V m₀.val env₀ ψ'' cvt.type = some P ∧
      m₀.val thmName ψ'' ∈ˢ P)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    (hSb : cvt.type.looseBVarsBounded 0 = true)
    -- the stored nested-rule pins and their well-formedness
    {lvls : List Level} {pins : List Expr}
    (hmIrP : mI = rP)
    (hpinsF : ∀ pin ∈ pins, pin.hasFvar = false)
    (hpinsB : ∀ pin ∈ pins, pin.looseBVarsBounded mI = true)
    (hpinslen : pins.length = cnP)
    -- the major premise's domain is the inner type former at the pins
    -- (from `nestedRuleShape` at install)
    (hshape : ∃ (pre : List (Name × Expr × BinderMeta)) (nm : Name)
        (dom bodyD : Expr) (bm : BinderMeta),
      tyA.stripPis mI = some (pre, .forallE nm dom bodyD bm) ∧
      dom.getAppArgs = pins)
    -- kernel kit (`NestedChecked` components)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    {cdoms : List Expr} {cres : Expr} {rdoms : List Expr} {rrest : Expr}
    {rhsA : Expr}
    {rbinders : List (Name × Expr × BinderMeta)} {rbody : Expr}
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvsP : List Expr} {crest2 : Expr}
    {ldoms : List Expr} {lrest : Expr}
    (htyStrip : (tyA.stripPis (mI)).isSome = true)
    (_hrPmI : rP ≤ mI)
    (hopen : openPisAtFvars (rP + cnF) cvt.type 0 =
      some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f R) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take (rP) =
      fvs.take (rP))
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop (rP)))
    (hcstrip : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hcinst : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop (rP))
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some (cdoms, cres))
    (_hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (_hdeIdx : DefEqListOk F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop (rP)).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (hdeFld : DefEqListOk F env₀ (rP + cnF)
      ((fvs.drop (rP)).map Expr.fvarTypeD) (cdoms.drop cnP))
    (hrinst : Expr.instPisAt (fvs.take (rP))
      (tyA.renameConsts f) = some (rdoms, rrest))
    (hdePre : DefEqListOk F env₀ (rP + cnF)
      ((fvs.take (rP)).map Expr.fvarTypeD) rdoms)
    (hopenP : openPisAtFvars (rP) tyA 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvsP.take rP) (rP - 1) p))
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) =
      some (cdomsP, crestP))
    (hopenX : openPisAtFvars cnF crestP (rP) =
      some (xFvsP, crest2))
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hdeRhs : isDefEqCore env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    -- rule right-hand-side facts
    (_hstripR : rhsA.stripLams (rP + cnF) =
      some (rbinders, rbody))
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) rhsA)
    (hIrhs : ∀ ψ'' : Name → Nat, ∃ L,
      interpClosed V m₀.val env₀ ψ'' rhsA = some L)
    -- member type wf
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (_htyps : tyA.allLevelParamsDefined lps = true)
    (hAty : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) tyA)
    (hIty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ'' tyA = some T)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hCps : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (hACty : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) cvj.type)
    (hICty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ'' cvj.type = some T)
    -- fold clause inputs
    {us usj : List Level} {args margs : List V} {tv : V}
    (hlena : args.length = mI)
    (hlenm : margs.length = cnP + cnF)
    (htv : tv = SpineFold V (m₀.val ctor
      (Level.substFn φ' cvj.levelParams usj)) margs)
    -- nested firing premises (the fold clause's nested conjunct)
    (hleveqN : ∀ p ∈ cvj.levelParams,
      Level.substFn φ' cvj.levelParams usj p =
      Level.substFn (Level.substFn φ' lps us) cvj.levelParams lvls p)
    {d : Nat} {ρ : Nat → V} {d₁ : Nat} {ρ₁ : Nat → V} {rest₁ : Expr}
    {d₂ : Nat} {ρ₂ : Nat → V} {rest₂ : Expr}
    (hfit1 : TeleFit V m₀.val env₀ φ' d ρ
      (tyA.instantiateLevelParams lps us) (args ++ [tv]) d₁ ρ₁ rest₁)
    (hfit2 : TeleFit V m₀.val env₀ φ' d₁ ρ₁
      (cvj.type.instantiateLevelParams cvj.levelParams usj) margs
      d₂ ρ₂ rest₂)
    (_hidx : (rest₂.getAppArgs.drop cnP).mapM
      (interpExpr V m₀.val env₀ φ' d₂ ρ₂) =
      some (args.drop (rP)))
    (hpinsVal : ∃ (dP : Nat) (ρP : Nat → V) (spineP : List Expr),
      FvarSpine dP ρP spineP args ∧
      (∀ a ∈ spineP, ∃ i nm, a = Expr.fvar i nm (.sort .zero)) ∧
      (pins.map fun pin => Expr.instSeq spineP (spineP.length - 1)
        (pin.instantiateLevelParams lps us)).mapM
        (interpExpr V m₀.val env₀ φ' dP ρP) = some (margs.take cnP)) :
    ∃ Rv, interpClosed V m₀.val env₀ (Level.substFn φ' lps us) rhsA =
        some Rv ∧
      SpineFold V (m₀.val R (Level.substFn φ' lps us)) (args ++ [tv]) =
        SpineFold V Rv (args.take (rP) ++ margs.drop cnP) ∧
      ChainSlots V Rv (args.take (rP) ++ margs.drop cnP) := by
  subst mI
  simp only [Expr.instSpine_eq_instSeq] at hmaj hcinst hcinstP
  -- ===== S0: the master frame =====
  obtain ⟨hfvsInst, hfvsLen, hfvsShape⟩ :=
    openPisAtFvars_spec (rP + cnF) 0 hopen
  have hpreLen : (args.take (rP)).length = rP := by
    rw [List.length_take, hlena]; omega
  have hwsLen : (args.take (rP) ++ margs.drop cnP).length =
      rP + cnF := by
    simp only [List.length_append, List.length_drop, hpreLen, hlenm]
    omega
  have hρWval : ∀ (k : Nat) (v : V),
      (args.take (rP) ++ margs.drop cnP)[k]? = some v →
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) (0 + k) = v := by
    intro k v hv
    show (args.take (rP) ++ margs.drop cnP).getD (0 + k)
      SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD, Nat.zero_add, hv]
    rfl
  have hspW : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) fvs
      (args.take (rP) ++ margs.drop cnP) :=
    FvarSpine_of_open hopen hwsLen (by omega) hρWval
  obtain ⟨hfvsWf, htbodyWf⟩ :=
    openPisAtFvars_wf (rP + cnF) 0 hopen
      (WScoped.of_not_hasFvar hSw) hSb
      (Expr.LeavesBounded.of_not_hasFvar hSw)
  have hfvsW : ∀ a ∈ fvs, WScoped (rP + cnF) a := by
    intro a ha
    have := (hfvsWf a ha).1
    simpa using this
  have hfvsShapes : ∀ a ∈ fvs, ∃ i n t, a = .fvar i n t := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨nm', ha'⟩ := hfvsShape k a hk
    exact ⟨0 + k, nm', _, ha'⟩
  -- ===== S1a: relocate the recursor fit =====
  have hTw : ∀ Dx : Nat, WScoped Dx (tyA.instantiateLevelParams lps us) :=
    fun Dx => WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact htyw)
  obtain ⟨hdd₁, hagr₁, argsR0, hfitL1, hfvR0⟩ :=
    TeleFit.toTeleFitI hfit1 (hTw d)
  have hlenR0 : argsR0.length = rP + 1 := by
    have h1 := TeleFitI.vs_length hfitL1
    simp only [List.length_append, List.length_cons, List.length_nil,
      hlena] at h1
    omega
  -- prefix restriction
  have hfitL1' : TeleFitI V m₀.val env₀ φ' d₁ ρ₁
      (tyA.instantiateLevelParams lps us)
      (argsR0.take (rP) ++ argsR0.drop (rP))
      (args ++ [tv]) rest₁ := by
    rw [List.take_append_drop]
    exact hfitL1
  obtain ⟨midR, hpreR0⟩ := TeleFitI.take_prefix hfitL1'
  have hpreR0len : (argsR0.take (rP)).length = rP := by
    rw [List.length_take, hlenR0]; omega
  have hpreRvals : (args ++ [tv]).take
      ((argsR0.take (rP)).length) = args.take (rP) := by
    rw [hpreR0len, List.take_append_of_le_length (by omega)]
  rw [hpreRvals] at hpreR0
  -- the raw prefix telescope strips
  obtain ⟨⟨bsTy, restTy⟩, htyStripSome⟩ :=
    Option.isSome_iff_exists.mp htyStrip
  obtain ⟨restTyPre, htyPreStrip⟩ :=
    Expr.stripPis_prefix rP (rP - rP)
      (by rw [show rP + (rP - rP) = rP from by omega]; exact htyStripSome)
  -- sanitize and uninstantiate the levels
  obtain ⟨midR2, hpreRS⟩ := TeleFitI.sanitize hpreR0
    (by
      rw [hpreR0len]
      exact Expr.stripPis_instantiateLevelParams_isSome _ _ _
        (by rw [htyPreStrip]; rfl))
    (fun a ha => hfvR0 a (List.mem_of_mem_take ha))
  have hshR : ∀ a ∈ (argsR0.take (rP)).map sanitizeArg,
      ∃ i n, a = Expr.fvar i n (.sort .zero) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, n, t, rfl⟩ := hfvR0 a₀ (List.mem_of_mem_take ha₀)
    exact ⟨i, n, rfl⟩
  obtain ⟨midR3, hfitRawR⟩ := TeleFitI.instLev_down hcvp hpreRS hshR
    (WScoped.of_not_hasFvar htyw (d := d₁)).fvarsBelow
  have hshR' : ∀ a ∈ (argsR0.take (rP)).map sanitizeArg,
      ∃ i n t, a = Expr.fvar i n t := by
    intro a ha
    obtain ⟨i, n, rfl⟩ := hshR a ha
    exact ⟨i, n, _, rfl⟩
  have hspR : FvarSpine d₁ ρ₁
      ((argsR0.take (rP)).map sanitizeArg)
      (args.take (rP)) :=
    FvarSpine_of_fit hfitRawR hshR'
  -- the public prefix walk of the recursor's type
  obtain ⟨⟨dsPubT, restPubT⟩, hpubT⟩ := Option.isSome_iff_exists.mp
    (instPisAt_isSome_of_stripPis (fvs.take (rP))
      (by
        rw [List.length_take, hfvsLen,
          Nat.min_eq_left (by omega), htyPreStrip]
        rfl))
  have hwsTake : (args.take (rP) ++ margs.drop cnP).take
      (rP) = args.take (rP) := by
    rw [List.take_append_of_le_length (by rw [hpreLen]; exact Nat.le_refl _),
      List.take_take, Nat.min_self]
  have hspWpre : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvs.take (rP)) (args.take (rP)) := by
    have h0 := FvarSpine.take (rP) hspW
    rwa [hwsTake] at h0
  -- pointwise packages for the public prefix domains, at the master
  -- frame
  have hmemPubT := fit_mem_transfer (φ := Level.substFn φ' lps us)
    htyw htyb htyPreStrip hpubT
    (by rw [List.length_take, hfvsLen]; omega)
    hspWpre hspR hfitRawR
  -- packages for the renamed prefix domains (`rdoms`)
  have htyPreRen : (tyA.renameConsts f).stripPis (rP) =
      some ((bsTy.take (rP)).map
        (fun b => (b.1, b.2.1.renameConsts f, b.2.2)),
        restTyPre.renameConsts f) :=
    stripPis_renameConsts (rP) htyPreStrip
  have hfvsPreLen : (fvs.take (rP)).length = rP := by
    rw [List.length_take, hfvsLen]; omega
  obtain ⟨-, hrdomsPt⟩ := instPisAt_stripPis _ hrinst
    (by rw [hfvsPreLen]; exact htyPreRen)
  obtain ⟨-, hpubTPt⟩ := instPisAt_stripPis _ hpubT
    (by rw [hfvsPreLen]; exact htyPreStrip)
  have hfvsPreShapes : ∀ a ∈ fvs.take (rP),
      ∃ i n t, a = .fvar i n t :=
    fun a ha => hfvsShapes a (List.mem_of_mem_take ha)
  have hmemR : ∀ (k : Nat) (a : Expr) (v : V), rdoms[k]? = some a →
      (args.take (rP))[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a = some B ∧
        v ∈ˢ B := by
    intro k a v ha hv
    have hk : k < rP := by
      have hl := instPisAt_length _ hrinst
      rcases Nat.lt_or_ge k (rP) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by rw [hl, hfvsPreLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨b, hb⟩ : ∃ b, (bsTy.take (rP))[k]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by
        rw [List.length_take, Expr.stripPis_length rP htyStripSome]
        omega)⟩
    have hbren : ((bsTy.take (rP)).map
        (fun b => (b.1, b.2.1.renameConsts f, b.2.2)))[k]? =
        some (b.1, b.2.1.renameConsts f, b.2.2) := by
      rw [List.getElem?_map, hb]
      rfl
    have ha' := hrdomsPt k _ hbren
    rw [ha] at ha'
    obtain rfl := Option.some.inj ha'
    obtain ⟨dp, hdp⟩ : ∃ dp, dsPubT[k]? = some dp := by
      have hl := instPisAt_length _ hpubT
      exact ⟨_, List.getElem?_eq_getElem (by rw [hl, hfvsPreLen]; omega)⟩
    obtain ⟨B, hBi, hvB⟩ := hmemPubT k dp v hdp hv
    have hdp' := hpubTPt k b hb
    rw [hdp] at hdp'
    obtain rfl := Option.some.inj hdp'
    refine ⟨B, ?_, hvB⟩
    show interpExpr V m₀.val env₀ (Level.substFn φ' lps us) _ _
      (instSeq ((fvs.take (rP)).take k) (k - 1)
        ((b.1, b.2.1.renameConsts f, b.2.2) :
          Name × Expr × BinderMeta).2.1) = some B
    rw [show ((b.1, b.2.1.renameConsts f, b.2.2) :
      Name × Expr × BinderMeta).2.1 = b.2.1.renameConsts f from rfl]
    rw [interp_instSeq_ren hro (fun a ha =>
      hfvsPreShapes a (List.mem_of_mem_take ha))]
    exact hBi
  -- ===== N1: the pin values at the master frame =====
  obtain ⟨dP, ρP, spineP, hspineP, hspineSh, hpinsInterp⟩ := hpinsVal
  have hspPlen : spineP.length = rP := by
    rw [FvarSpine.length hspineP, hlena]
  have hargsTake : args.take rP = args := by
    rw [← hlena, List.take_length]
  have hspWpreSan : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      ((fvs.take rP).map sanitizeArg) (args.take rP) :=
    FvarSpine.sanitize hspWpre
  have hsanWlen : ((fvs.take rP).map sanitizeArg).length = rP := by
    rw [List.length_map, hfvsPreLen]
  have hsanWShapes : ∀ a ∈ (fvs.take rP).map sanitizeArg,
      ∃ i n, a = Expr.fvar i n (.sort .zero) :=
    FvarSpine.sanitize_shapes hspWpre
  have hsanWShapes' : ∀ a ∈ (fvs.take rP).map sanitizeArg,
      ∃ i n t, a = Expr.fvar i n t := by
    intro a ha
    obtain ⟨i, n, rfl⟩ := hsanWShapes a ha
    exact ⟨i, n, _, rfl⟩
  have hsanWInstId : ((fvs.take rP).map sanitizeArg).map
      (·.instantiateLevelParams lps us) =
      (fvs.take rP).map sanitizeArg := by
    have h0 : ((fvs.take rP).map sanitizeArg).map
        (·.instantiateLevelParams lps us) =
        ((fvs.take rP).map sanitizeArg).map id :=
      List.map_congr_left (fun a ha => by
        obtain ⟨i, n, rfl⟩ := hsanWShapes a ha
        rfl)
    rw [h0, List.map_id]
  have hpinValF : ∀ (k : Nat) (a : Expr) (v : V),
      (pins.map (fun p => instSeq (fvs.take rP) (rP - 1)
        (p.renameConsts f)))[k]? = some a →
      (margs.take cnP)[k]? = some v →
      interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a = some v := by
    intro k a v ha hv
    rw [List.getElem?_map] at ha
    cases hpk : pins[k]? with
    | none => rw [hpk] at ha; exact nomatch ha
    | some pin => ?_
    rw [hpk] at ha
    obtain rfl := Option.some.inj ha
    have hpinMem : pin ∈ pins := List.mem_of_getElem? hpk
    have hpincl : pin.hasFvar = false := hpinsF pin hpinMem
    have hpinb : pin.looseBVarsBounded rP = true := hpinsB pin hpinMem
    have hptP := InterpSpine.of_mapM hpinsInterp
    have hvP : interpExpr V m₀.val env₀ φ' dP ρP
        (instSeq spineP (spineP.length - 1)
          (pin.instantiateLevelParams lps us)) = some v := by
      refine InterpSpine.pointwise hptP k ?_ hv
      rw [List.getElem?_map, hpk]
      rfl
    rw [hspPlen] at hvP
    rw [interp_instSeq_ren hro hfvsPreShapes]
    have hcross1 := interp_instSeq_fvarFrames (cval := m₀.val)
      (env := env₀) (φ := Level.substFn φ' lps us) (e := pin) hpincl
      (by rw [hfvsPreLen]; exact hpinb)
      hspWpre hspWpreSan
    rw [hfvsPreLen, hsanWlen] at hcross1
    rw [hcross1]
    rw [show instSeq ((fvs.take rP).map sanitizeArg) (rP - 1) pin =
        (fun e => e) (instSeq ((fvs.take rP).map sanitizeArg) (rP - 1)
          pin) from rfl]
    have hlev : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty)
        (instSeq ((fvs.take rP).map sanitizeArg) (rP - 1) pin) =
        interpExpr V m₀.val env₀ φ' (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty)
        (instSeq ((fvs.take rP).map sanitizeArg) (rP - 1)
          (pin.instantiateLevelParams lps us)) := by
      rw [show instSeq ((fvs.take rP).map sanitizeArg) (rP - 1)
            (pin.instantiateLevelParams lps us) =
          (instSeq ((fvs.take rP).map sanitizeArg) (rP - 1)
            pin).instantiateLevelParams lps us from by
        rw [Expr.instSeq_instantiateLevelParams_fvars _ _ _ _ _
          hsanWShapes', hsanWInstId]]
      rw [interp_instLevels hcvp]
    rw [hlev]
    have hspineP' : FvarSpine dP ρP spineP (args.take rP) := by
      rw [hargsTake]
      exact hspineP
    have hcross2 := interp_instSeq_fvarFrames (cval := m₀.val)
      (env := env₀) (φ := φ')
      (e := pin.instantiateLevelParams lps us)
      (by rw [hasFvar_instantiateLevelParams]; exact hpincl)
      (by
        rw [hsanWlen, looseBVarsBounded_instantiateLevelParams]
        exact hpinb)
      hspWpreSan hspineP'
    rw [hsanWlen, hspPlen] at hcross2
    rw [hcross2]
    exact hvP
  -- the pin entries as an argument spine at the master frame
  have hInstPinsF : InstArgs m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (pins.map (fun p => instSeq (fvs.take rP) (rP - 1)
        (p.renameConsts f))) (margs.take cnP) := by
    refine InstArgs.of_pointwise (by
      rw [List.length_map, hpinslen, List.length_take, hlenm]
      omega) ?_
    intro k a v ha hv
    refine ⟨?_, ?_, hpinValF k a v ha hv⟩
    · rw [List.getElem?_map] at ha
      cases hpk : pins[k]? with
      | none => rw [hpk] at ha; exact nomatch ha
      | some pin => ?_
      rw [hpk] at ha
      obtain rfl := Option.some.inj ha
      exact instSeq_wscoped _
        (WScoped.of_not_hasFvar (by
          rw [hasFvar_renameConsts]
          exact hpinsF pin (List.mem_of_getElem? hpk)))
        (fun x hx => hfvsW x (List.mem_of_mem_take hx))
    · rw [List.getElem?_map] at ha
      cases hpk : pins[k]? with
      | none => rw [hpk] at ha; exact nomatch ha
      | some pin => ?_
      rw [hpk] at ha
      obtain rfl := Option.some.inj ha
      have h0 := instSeq_bclosed (args := fvs.take rP)
        (e := pin.renameConsts f)
        (fun x hx => (hfvsWf x (List.mem_of_mem_take hx)).2.1)
        (by
          rw [hfvsPreLen, looseBVarsBounded_renameConsts]
          exact hpinsB pin (List.mem_of_getElem? hpk))
      rwa [hfvsPreLen] at h0
  -- the field variables as an argument spine at the master frame
  have hspWdrop : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvs.drop (rP)) (margs.drop cnP) := by
    have h0 := FvarSpine.drop (rP) hspW
    have h1 := List.drop_left (l₁ := args.take (rP))
      (l₂ := margs.drop cnP)
    rw [hpreLen] at h1
    rwa [h1] at h0
  have hInstFldW : InstArgs m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvs.drop (rP)) (margs.drop cnP) :=
    InstArgs_of_FvarSpine hspWdrop
      (fun a ha => ⟨hfvsW a (List.mem_of_mem_drop ha),
        (hfvsWf a (List.mem_of_mem_drop ha)).2.1⟩)
  have hInstCtorW : InstArgs m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (pins.map (fun p => instSeq (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop (rP)) margs := by
    have h0 := InstArgs.append hInstPinsF hInstFldW
    rwa [List.take_append_drop] at h0
  have hspineWLen : (pins.map (fun p => instSeq (fvs.take rP) (rP - 1)
      (p.renameConsts f)) ++ fvs.drop (rP)).length = cnP + cnF := by
    rw [List.length_append, List.length_map, hpinslen,
      List.length_drop, hfvsLen]
    omega
  -- ===== S1b: relocate the constructor fit =====
  have hCwI : ∀ Dx : Nat, WScoped Dx
      (cvj.type.instantiateLevelParams cvj.levelParams usj) :=
    fun Dx => WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact hCw)
  obtain ⟨hdd₂, hagr₂, argsC0, hfitL2, hfvC0⟩ :=
    TeleFit.toTeleFitI hfit2 (hCwI d₁)
  have hlenC0 : argsC0.length = cnP + cnF := by
    have h1 := TeleFitI.vs_length hfitL2
    rw [hlenm] at h1
    omega
  obtain ⟨midC2, hfitC2⟩ := TeleFitI.sanitize hfitL2
    (by
      rw [hlenC0]
      exact Expr.stripPis_instantiateLevelParams_isSome _ _ _ hcstrip)
    hfvC0
  have hshC : ∀ a ∈ argsC0.map sanitizeArg,
      ∃ i n, a = Expr.fvar i n (.sort .zero) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, n, t, rfl⟩ := hfvC0 a₀ ha₀
    exact ⟨i, n, rfl⟩
  obtain ⟨midC3, hfitC3⟩ := TeleFitI.instLev_down hcvp hfitC2 hshC
    (WScoped.of_not_hasFvar hCw (d := d₂)).fvarsBelow
  obtain ⟨midC4, hfitC4⟩ := TeleFitI.params_ext hleveqN hcvp hfitC3
    hCps hshC
  have hshC' : ∀ a ∈ argsC0.map sanitizeArg,
      ∃ i n t, a = Expr.fvar i n t := by
    intro a ha
    obtain ⟨i, n, rfl⟩ := hshC a ha
    exact ⟨i, n, _, rfl⟩
  have hspC : FvarSpine d₂ ρ₂ (argsC0.map sanitizeArg) margs :=
    FvarSpine_of_fit hfitC4 hshC'
  have hsanLen : (argsC0.map sanitizeArg).length = cnP + cnF := by
    rw [List.length_map, hlenC0]
  -- ===== N2: the constructor-domain memberships at the master frame =====
  obtain ⟨⟨bsC, cbody⟩, hCstripSome⟩ := Option.isSome_iff_exists.mp hcstrip
  have hbsCLen : bsC.length = cnP + cnF :=
    Expr.stripPis_length _ hCstripSome
  -- memberships along the raw constructor telescope at `ψL`
  obtain ⟨dsL, hinstL, hptL⟩ := TeleFitI.toInstPisAt hfitC4
  obtain ⟨-, hdsLPt⟩ := instPisAt_stripPis _ hinstL
    (by rw [hsanLen]; exact hCstripSome)
  have hmemBase : ∀ (k : Nat) (b : Name × Expr × BinderMeta) (v : V),
      bsC[k]? = some b → margs[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀
        (Level.substFn (Level.substFn φ' lps us) cvj.levelParams lvls)
        d₂ ρ₂
        (instSeq ((argsC0.map sanitizeArg).take k) (k - 1) b.2.1) =
        some B ∧ v ∈ˢ B := by
    intro k b v hb hv
    exact hptL k _ v (hdsLPt k b hb) hv
  -- ... at the level-instantiated telescope, assignment `ψ`
  obtain ⟨⟨bsI, cbodyI⟩, hstripI⟩ := Option.isSome_iff_exists.mp
    (Expr.stripPis_instantiateLevelParams_isSome cvj.levelParams lvls
      _ hcstrip)
  have hbsILen : bsI.length = cnP + cnF :=
    Expr.stripPis_length _ hstripI
  obtain ⟨-, hbsIdoms⟩ := Expr.stripPis_instantiateLevelParams_eq
    cvj.levelParams lvls _ hCstripSome hstripI
  have hsanTakeShapes : ∀ (k : Nat),
      ∀ a ∈ (argsC0.map sanitizeArg).take k, ∃ i n ty,
        a = .fvar i n ty :=
    fun k a ha => hshC' a (List.mem_of_mem_take ha)
  have hsanTakeId : ∀ (k : Nat),
      ((argsC0.map sanitizeArg).take k).map
        (·.instantiateLevelParams cvj.levelParams lvls) =
      (argsC0.map sanitizeArg).take k := by
    intro k
    have h0 : ((argsC0.map sanitizeArg).take k).map
        (·.instantiateLevelParams cvj.levelParams lvls) =
        ((argsC0.map sanitizeArg).take k).map id :=
      List.map_congr_left (fun a ha => by
        obtain ⟨i, n, rfl⟩ := hshC a (List.mem_of_mem_take ha)
        rfl)
    rw [h0, List.map_id]
  have hmemI : ∀ (k : Nat) (b : Name × Expr × BinderMeta) (v : V),
      bsI[k]? = some b → margs[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ (Level.substFn φ' lps us) d₂ ρ₂
        (instSeq ((argsC0.map sanitizeArg).take k) (k - 1) b.2.1) =
        some B ∧ v ∈ˢ B := by
    intro k b v hb hv
    obtain ⟨bC, hbC⟩ : ∃ bC, bsC[k]? = some bC := by
      have hkl : k < bsI.length := by
        rcases Nat.lt_or_ge k bsI.length with h | h
        · exact h
        · rw [List.getElem?_eq_none (by omega)] at hb
          exact nomatch hb
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hbeq : b.2.1 = bC.2.1.instantiateLevelParams cvj.levelParams
        lvls := hbsIdoms k bC b hbC hb
    obtain ⟨B, hB, hvB⟩ := hmemBase k bC v hbC hv
    refine ⟨B, ?_, hvB⟩
    rw [hbeq, show instSeq ((argsC0.map sanitizeArg).take k) (k - 1)
        (bC.2.1.instantiateLevelParams cvj.levelParams lvls) =
        (instSeq ((argsC0.map sanitizeArg).take k) (k - 1)
          bC.2.1).instantiateLevelParams cvj.levelParams lvls from by
      rw [Expr.instSeq_instantiateLevelParams_fvars _ _ _ _ _
        (hsanTakeShapes k), hsanTakeId k]]
    rw [interp_instLevels hcvp]
    exact hB
  -- ... at the renamed telescope
  have hstripRen : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).stripPis (cnP + cnF) =
      some (bsI.map (fun b => (b.1, b.2.1.renameConsts f, b.2.2)),
        cbodyI.renameConsts f) :=
    stripPis_renameConsts (cnP + cnF) hstripI
  have hmemRen : ∀ (k : Nat) (b : Name × Expr × BinderMeta) (v : V),
      (bsI.map (fun b => (b.1, b.2.1.renameConsts f, b.2.2)))[k]? =
        some b →
      margs[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ (Level.substFn φ' lps us) d₂ ρ₂
        (instSeq ((argsC0.map sanitizeArg).take k) (k - 1) b.2.1) =
        some B ∧ v ∈ˢ B := by
    intro k b v hb hv
    rw [List.getElem?_map] at hb
    cases hbI : bsI[k]? with
    | none => rw [hbI] at hb; exact nomatch hb
    | some bI => ?_
    rw [hbI] at hb
    obtain rfl := Option.some.inj hb
    obtain ⟨B, hB, hvB⟩ := hmemI k bI v hbI hv
    refine ⟨B, ?_, hvB⟩
    show interpExpr V m₀.val env₀ (Level.substFn φ' lps us) d₂ ρ₂
      (instSeq ((argsC0.map sanitizeArg).take k) (k - 1)
        (bI.2.1.renameConsts f)) = some B
    rw [interp_instSeq_ren hro (hsanTakeShapes k)]
    exact hB
  -- the renamed level-instantiated constructor type's closure facts
  have hT_Rw : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts, hasFvar_instantiateLevelParams]
    exact hCw
  have hT_Rb : ((cvj.type.instantiateLevelParams cvj.levelParams
      lvls).renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts,
      looseBVarsBounded_instantiateLevelParams]
    exact hCb
  have hmemC : ∀ (k : Nat) (a : Expr) (v : V), cdoms[k]? = some a →
      margs[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a = some B ∧
        v ∈ˢ B :=
    fit_mem_transferI hT_Rw hT_Rb hstripRen hcinst hspineWLen
      hInstCtorW hspC hmemRen
  -- ===== S2: the theorem walk =====
  -- split the theorem's opening at the prefix/field boundary
  have hfvsInst' : Expr.instPisAt
      (fvs.take (rP) ++ fvs.drop (rP)) cvt.type =
      some (fvs.map Expr.fvarTypeD, tbody) := by
    rw [List.take_append_drop]
    exact hfvsInst
  obtain ⟨dsS1, midS, dsS2, hopS1, hopS2, hdsSplit⟩ :=
    instPisAt_append _ _ hfvsInst'
  have hdsS1len : dsS1.length = rP := by
    rw [instPisAt_length _ hopS1, hfvsPreLen]
  obtain ⟨hdsS1eq, hdsS2eq⟩ : dsS1 = (fvs.take (rP)).map
      Expr.fvarTypeD ∧ dsS2 = (fvs.drop (rP)).map
      Expr.fvarTypeD := by
    have hmap : fvs.map Expr.fvarTypeD =
        (fvs.take (rP)).map Expr.fvarTypeD ++
        (fvs.drop (rP)).map Expr.fvarTypeD := by
      rw [← List.map_append, List.take_append_drop]
    rw [hmap] at hdsSplit
    exact List.append_inj hdsSplit.symm (by
      rw [hdsS1len, List.length_map, hfvsPreLen])
  subst hdsS1eq hdsS2eq
  -- the master frame's theorem-side invariants
  have hWS : WScoped (rP + cnF) cvt.type :=
    WScoped.of_not_hasFvar hSw
  have hLS : Expr.LeavesBounded cvt.type :=
    Expr.LeavesBounded.of_not_hasFvar hSw
  have hFS : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) cvt.type :=
    FvarsOk.of_not_hasFvar hSw
  have hAS : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) cvt.type :=
    AnnotOk.closed_invariant hSw _ _
      (hthm_annot (Level.substFn φ' lps us))
  obtain ⟨P, hPc, hPmem⟩ := hthm_mem (Level.substFn φ' lps us)
  have hPI : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) cvt.type = some P := by
    rw [interp_closed_invariant hSw _ _]
    exact hPc
  -- the renamed recursor type's invariants
  have htyRw : (tyA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact htyw
  have htyRb : (tyA.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact htyb
  have hAtyR : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) (tyA.renameConsts f) :=
    AnnotOk.closed_invariant htyRw _ _
      (AnnotOk.renameConsts hro tyA 0 (rho0 V)
        (hAty (Level.substFn φ' lps us)))
  obtain ⟨Tty, hTtyc⟩ := hIty (Level.substFn φ' lps us)
  have hItyR : ∃ TR, interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) (tyA.renameConsts f) =
      some TR := by
    refine ⟨Tty, ?_⟩
    rw [interp_closed_invariant htyRw _ _]
    show interpClosed V m₀.val env₀ _ (tyA.renameConsts f) = some Tty
    unfold interpClosed
    rw [interp_renameConsts hro tyA 0 (rho0 V)]
    exact hTtyc
  -- stage 1: the prefix walk
  obtain ⟨hfitS1, hfitR1, hΘpre⟩ := pi_walk m₀ F hopS1 hrinst hdePre
    hspWpre (fun a ha => hfvsW a (List.mem_of_mem_take ha))
    hWS hSb hLS hFS hAS
    (WScoped.of_not_hasFvar htyRw) htyRb
    (Expr.LeavesBounded.of_not_hasFvar htyRw)
    (FvarsOk.of_not_hasFvar htyRw) hAtyR
    ⟨P, hPI⟩ hItyR hmemR
  -- the mid residual's facts and the partial elimination
  obtain ⟨Qmid, hQmidI, hQmidMem, hAmidS⟩ :=
    TeleFitI.elim hfitS1 hAS hPI hPmem
  obtain ⟨hWmidS, hbmidS, -, hleavesMidS⟩ :=
    TeleFitI.rest_wf hfitS1 hWS hSb hAS
  have hFmidS : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact hΘpre a ha l hla
  have hLmidS : Expr.LeavesBounded midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
  -- ===== N3: pin annotation truthfulness (statement side) =====
  obtain ⟨preD, nmD, domD, bodyDm, bmD, hshapeStrip, hdomArgs⟩ := hshape
  have hrestTyPreEq : restTyPre = .forallE nmD domD bodyDm bmD :=
    congrArg Prod.snd
      (Option.some.inj (htyPreStrip.symm.trans hshapeStrip))
  have hdomEq : domD = Expr.mkAppN domD.getAppFn pins := by
    rw [← hdomArgs]
    exact (Expr.mkAppN_getApp domD).symm
  obtain ⟨-, -, hArrest, -⟩ :=
    TeleFitI.rest_wf hfitR1 (WScoped.of_not_hasFvar htyRw) htyRb hAtyR
  have hrrestEq : rrest = instSeq (fvs.take rP) (rP - 1)
      (restTyPre.renameConsts f) := by
    have h := (instPisAt_stripPis _ hrinst
      (by rw [hfvsPreLen]; exact htyPreRen)).1
    rwa [hfvsPreLen] at h
  obtain ⟨bodyWD, hrrestF⟩ : ∃ bW, rrest = .forallE nmD
      (instSeq (fvs.take rP) (rP - 1) (domD.renameConsts f)) bW bmD := by
    refine ⟨instSeq (fvs.take rP) (rP - 1 + 1)
      (bodyDm.renameConsts f), ?_⟩
    rw [hrrestEq, hrestTyPreEq]
    simp only [Expr.renameConsts]
    exact instSeq_forallE _ _ _ _ _ _ (by rw [hfvsPreLen]; omega)
  rw [hrrestF] at hArrest
  simp only [AnnotOk] at hArrest
  have hAdomW := hArrest.1
  have hdomWSplit : instSeq (fvs.take rP) (rP - 1)
      (domD.renameConsts f) =
      Expr.mkAppN (instSeq (fvs.take rP) (rP - 1)
        (domD.getAppFn.renameConsts f))
      (pins.map (fun p => instSeq (fvs.take rP) (rP - 1)
        (p.renameConsts f))) := by
    have h0 : domD.renameConsts f =
        (Expr.mkAppN domD.getAppFn pins).renameConsts f := by
      rw [← hdomEq]
    rw [h0, renameConsts_mkAppN, instSeq_mkAppN, List.map_map]
    rfl
  rw [hdomWSplit] at hAdomW
  have hApinsF : ∀ a ∈ pins.map (fun p => instSeq (fvs.take rP)
      (rP - 1) (p.renameConsts f)),
      AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a :=
    (annotOk_appN_parts _ _ hAdomW).2
  -- ===== N4: the constructor's parameter walk at the master frame =====
  obtain ⟨cdomsA, midC, cdomsB, hopC1, hopC2, hcdomsSplit⟩ :=
    instPisAt_append _ _ hcinst
  have hcdomsAlen : cdomsA.length = cnP := by
    rw [instPisAt_length _ hopC1, List.length_map, hpinslen]
  have hcdomsBeq : cdoms.drop cnP = cdomsB := by
    rw [hcdomsSplit, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  have hAT_R : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) :=
    AnnotOk.closed_invariant hT_Rw _ _
      (AnnotOk.renameConsts hro _ 0 (rho0 V)
        (AnnotOk.instLevels hcvp _ 0 (rho0 V)
          (hACty (Level.substFn (Level.substFn φ' lps us)
            cvj.levelParams lvls))))
  have hIT_R : ∃ TR, interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some TR := by
    obtain ⟨TC, hTCc⟩ := hICty (Level.substFn (Level.substFn φ' lps us)
      cvj.levelParams lvls)
    refine ⟨TC, ?_⟩
    rw [interp_closed_invariant hT_Rw _ _]
    show interpClosed V m₀.val env₀ _
      ((cvj.type.instantiateLevelParams cvj.levelParams
        lvls).renameConsts f) = some TC
    unfold interpClosed
    rw [interp_renameConsts hro, interp_instLevels hcvp]
    exact hTCc
  obtain ⟨hfitC1, hImidC⟩ := peel_walkI hopC1 hInstPinsF hApinsF
    (WScoped.of_not_hasFvar hT_Rw) hAT_R hIT_R
    (fun k a v ha hv => by
      have hkA : k < cnP := by
        rcases Nat.lt_or_ge k cnP with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at ha
          exact nomatch ha
      refine hmemC k a v ?_ ?_
      · rw [hcdomsSplit, List.getElem?_append_left (by omega)]
        exact ha
      · have hv' : (margs.take cnP)[k]? = some v := hv
        rwa [List.getElem?_take_of_lt hkA] at hv')
  -- the mid constructor residual's facts
  obtain ⟨hWmidC, hbmidC, hAmidC, hleavesMidC⟩ :=
    TeleFitI.rest_wf hfitC1 (WScoped.of_not_hasFvar hT_Rw) hT_Rb hAT_R
  have hFmidC : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hT_Rw] at hl'
      cases hl'
    · obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
      rw [← Expr.instSpine_eq_instSeq] at hla
      rcases fvarLeaves_instSpine (rP - 1) hla with hl'' | ⟨x, hx, hlx⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar (by
          rw [hasFvar_renameConsts]; exact hpinsF pin hpin)] at hl''
        cases hl''
      · exact hΘpre x hx l hlx
  have hLmidC : Expr.LeavesBounded midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hT_Rw] at hl'
      cases hl'
    · obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
      rw [← Expr.instSpine_eq_instSeq] at hla
      rcases fvarLeaves_instSpine (rP - 1) hla with hl'' | ⟨x, hx, hlx⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar (by
          rw [hasFvar_renameConsts]; exact hpinsF pin hpin)] at hl''
        cases hl''
      · exact (hfvsWf x (List.mem_of_mem_take hx)).2.2 l hlx
  -- stage 2: the field walk
  obtain ⟨hfitS2, -, hΘx⟩ := pi_walk m₀ F hopS2
    (by rw [← hcdomsBeq] at hopC2; exact hopC2)
    hdeFld
    hspWdrop (fun a ha => hfvsW a (List.mem_of_mem_drop ha))
    hWmidS hbmidS hLmidS hFmidS hAmidS
    hWmidC hbmidC hLmidC hFmidC hAmidC
    ⟨Qmid, hQmidI⟩ hImidC
    (fun k a v ha hv => by
      refine hmemC (cnP + k) a v ?_ ?_
      · rw [List.getElem?_drop] at ha
        exact ha
      · have hv' : (margs.drop cnP)[k]? = some v := hv
        rwa [List.getElem?_drop] at hv')
  -- combine and finish the elimination
  obtain ⟨Q, hQI, hQmem0, hAtbody⟩ :=
    TeleFitI.elim hfitS2 hAmidS hQmidI hQmidMem
  have hQmem : SpineFold V (m₀.val thmName (Level.substFn φ' lps us))
      (args.take (rP) ++ margs.drop cnP) ∈ˢ Q := by
    rw [SpineFold_append]
    exact hQmem0
  -- ===== S3: the Eq collapse =====
  have htbodyEq : tbody = Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS] := by
    have h0 := Expr.mkAppN_getApp tbody
    rw [hheadEq, hargs3] at h0
    exact h0.symm
  rw [htbodyEq] at hQI hAtbody
  obtain ⟨-, hcompsA, veq, vsE, hveqi, hspE, hchainE, hfoldQ⟩ :=
    annotOk_spine_inv _ (.const eqName [ℓA]) (by simp) hAtbody
  obtain ⟨vα, vl, vr, rfl⟩ : ∃ vα vl vr, vsE = [vα, vl, vr] := by
    match vsE, hspE with
    | [vα, vl, vr], _ => exact ⟨vα, vl, vr, rfl⟩
    | [], h => exact nomatch h
    | [_], h => exact nomatch h.2
    | [_, _], h => exact nomatch h.2.2
    | _ :: _ :: _ :: _ :: _, h => exact nomatch h.2.2.2
  obtain ⟨hiα, hil, hir, -⟩ := hspE
  have hQeq : Q = SpineFold V veq [vα, vl, vr] := by
    rw [hfoldQ] at hQI
    exact Option.some.inj hQI |>.symm
  have hveq : veq = eqVal V (Level.substFn
      (Level.substFn φ' lps us) [uN] [ℓA]) := by
    simp only [interpExpr, heqfind] at hveqi
    rw [if_pos (by simp [eqA, ConstantInfo.toConstantVal])] at hveqi
    rw [← Option.some.inj hveqi, heqval]
    congr 2
  obtain ⟨⟨vE₁, A₁, B₁, hpi₁, hmem₁, -⟩, hchainE'⟩ := hchainE
  obtain ⟨⟨vE₂, A₂, B₂, hpi₂, hmem₂, -⟩, hchainE''⟩ := hchainE'
  obtain ⟨⟨vE₃, A₃, B₃, hpi₃, hmem₃, -⟩, -⟩ := hchainE''
  rw [hveq] at hpi₁ hpi₂ hpi₃
  have hαu : vα ∈ˢ univ (Level.substFn (Level.substFn φ' lps us) [uN]
      [ℓA] uN) := by
    have h1 := hpi₁
    simp only [eqVal] at h1
    refine lam_dom_of_ne h1 ?_ vα hmem₁
    simp [Nat.max_eq_zero_iff]
  have hvlmem : vl ∈ˢ vα := by
    have h2 := hpi₂
    rw [eqVal_app hαu] at h2
    refine lam_dom_of_ne h2 ?_ vl hmem₂
    simp [Nat.max_eq_zero_iff]
  have hvrmem : vr ∈ˢ vα := by
    have h3 := hpi₃
    rw [eqVal_app₂ hαu hvlmem] at h3
    refine lam_dom_of_ne h3 ?_ vr hmem₃
    simp
  have hQeqv : Q = eqv vl vr := by
    rw [hQeq, hveq]
    show SpineFold V _ [vα, vl, vr] = _
    rw [show SpineFold V (eqVal V (Level.substFn
        (Level.substFn φ' lps us) [uN] [ℓA])) [vα, vl, vr] =
      SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn (Level.substFn φ' lps us) [uN] [ℓA]))
        vα) vl) vr from rfl]
    exact eqVal_app₃ hαu hvlmem hvrmem
  have hvlvr : vl = vr := by
    rw [hQeqv] at hQmem
    exact mem_eqv hQmem
  -- ===== S4: the left side is the recursor's spine fold =====
  have hlhsEq : lhsS = Expr.mkAppN (.const (f R) (lps.map .param))
      lhsS.getAppArgs := by
    have h0 := Expr.mkAppN_getApp lhsS
    rw [hlhead] at h0
    exact h0.symm
  have hAlhs : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) lhsS :=
    hcompsA lhsS (by simp)
  rw [hlhsEq] at hAlhs
  obtain ⟨-, hlargsA, vhead, lvals, hheadI, hspL, hchainL, hfoldL⟩ :=
    annotOk_spine_inv _ (.const (f R) (lps.map .param))
      (by
        intro h0
        rw [h0] at hlarity
        exact nomatch hlarity) hAlhs
  have hvlfold : vl = SpineFold V vhead lvals := by
    rw [← hlhsEq] at hfoldL
    rw [hfoldL] at hil
    exact Option.some.inj hil |>.symm
  -- the head is the recursor's value
  have hcRi : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (.const (f R) (lps.map .param)) =
      some (m₀.val R (Level.substFn φ' lps us)) := by
    simp only [interpExpr, hfRm]
    rw [if_pos (by rw [hRmlps]; simp)]
    rw [show cim.toConstantVal.levelParams = lps from hRmlps]
    have h1 : Level.substFn (Level.substFn φ' lps us) lps
        (lps.map .param) = Level.substFn φ' lps us :=
      funext (fun p => Level.substFn_map_param)
    rw [h1, hro.2.2 R]
  have hvhead : vhead = m₀.val R (Level.substFn φ' lps us) := by
    rw [hcRi] at hheadI
    exact Option.some.inj hheadI |>.symm
  -- ===== S4b: component facts =====
  obtain ⟨hWtbody0, hbtbody0, htbodyL0⟩ := htbodyWf
  obtain ⟨-, -, -, hleavesTbody⟩ := TeleFitI.rest_wf hfitS2 hWmidS hbmidS
    hAmidS
  have hFtbody : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) tbody := by
    intro l hl
    rcases hleavesTbody l hl with hl' | ⟨a, ha, hla⟩
    · exact hFmidS l hl'
    · exact hΘx a ha l hla
  -- rhsS component facts
  have hrhsMem : rhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; simp
  have hWrhsS : WScoped (rP + cnF) rhsS := by
    have h0 := hWtbody0.getAppArgs rhsS hrhsMem
    rwa [Nat.zero_add] at h0
  have hbrhsS : rhsS.looseBVarsBounded 0 = true :=
    looseBVarsBounded_getAppArgs hbtbody0 _ hrhsMem
  have hFrhsS : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) rhsS := by
    rw [htbodyEq] at hFtbody
    exact FvarsOk.of_subset
      (fun l hl => fvarLeaves_getAppArgs (htbodyEq ▸ hrhsMem) l hl)
      hFtbody
  have hLrhsS : Expr.LeavesBounded rhsS :=
    fun l hl => htbodyL0 l (fvarLeaves_getAppArgs hrhsMem l hl)
  have hArhsS : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) rhsS :=
    hcompsA rhsS (by simp)
  -- ===== S4d: the major's value =====
  have hlvalsLen : lvals.length = rP + 1 := by
    have h0 := InterpSpine.length hspL
    omega
  obtain ⟨lastE, hlastE⟩ : ∃ x,
      lhsS.getAppArgs.drop (rP) = [x] := by
    have hlen1 : (lhsS.getAppArgs.drop (rP)).length = 1 := by
      rw [List.length_drop, hlarity]
      omega
    cases hdd : lhsS.getAppArgs.drop (rP) with
    | nil => rw [hdd] at hlen1; exact nomatch hlen1
    | cons x xs =>
      rw [hdd] at hlen1
      simp only [List.length_cons] at hlen1
      have : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp at hlen1
      subst this
      exact ⟨x, rfl⟩
  have hlastIdx : lhsS.getAppArgs[rP]? = some lastE := by
    have h0 := congrArg (fun l => l[0]?) hlastE
    simp only [List.getElem?_drop] at h0
    simpa using h0
  have hlastD : lhsS.getAppArgs.getLastD (.bvar 0) = lastE := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    rw [hlarity, show rP + 1 - 1 = rP
      from by omega, hlastIdx]
    rfl
  have hmajE : lastE = Expr.mkAppN (.const (f ctor) lvls)
      (pins.map (fun p => instSeq (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop (rP)) := by
    rw [← hlastD]
    exact hmaj
  -- the constructor head's interpretation, via the statement's own
  -- definedness
  obtain ⟨vlast, hvlastIdx⟩ : ∃ w, lvals[rP]? = some w :=
    ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have hlastI0 := InterpSpine.pointwise hspL rP hlastIdx hvlastIdx
  rw [hmajE] at hlastI0
  obtain ⟨vh, hvhI⟩ := interp_mkAppN_head_some _ _ hlastI0
  have hheadI2 : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (.const (f ctor) lvls) =
      some (m₀.val ctor (Level.substFn φ' cvj.levelParams usj)) := by
    simp only [interpExpr, hfCm] at hvhI ⊢
    by_cases hal : lvls.length = cimC.toConstantVal.levelParams.length
    · rw [if_pos hal]
      rw [show cimC.toConstantVal.levelParams = cvj.levelParams
        from hCmlps]
      rw [hro.2.2 ctor]
      exact congrArg some (hcvp _ _ hfj _ _
        (fun p hp => (hleveqN p hp).symm))
    · rw [if_neg hal] at hvhI
      exact nomatch hvhI
  have hspineWInterp : InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (pins.map (fun p => instSeq (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop (rP)) margs :=
    InstArgs.toInterpSpine hInstCtorW
  have hmajorI' : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) lastE = some tv := by
    rw [hmajE, interp_mkAppN _ _ hheadI2 hspineWInterp, htv]
  -- ===== S4e: the whole left value =====
  have hlargsDecomp : lhsS.getAppArgs =
      lhsS.getAppArgs.take (rP) ++
      ((lhsS.getAppArgs.drop (rP)).take (rP - rP) ++ [lastE]) := by
    have h0 := List.take_append_drop (rP) lhsS.getAppArgs
    rw [show rP - rP = 0 from by omega, List.take_zero,
      List.nil_append, ← hlastE, h0]
  have hspPrefix : InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (lhsS.getAppArgs.take (rP)) (args.take (rP)) := by
    rw [hlpre]
    exact InterpSpine_of_FvarSpine hspWpre
  have hspIdx : InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      ((lhsS.getAppArgs.drop (rP)).take (rP - rP))
      (args.drop (rP)) := by
    have hdropNil : args.drop rP = [] :=
      List.drop_eq_nil_of_le (by omega)
    rw [show rP - rP = 0 from by omega, List.take_zero, hdropNil]
    trivial
  have hspFull : InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      lhsS.getAppArgs
      (args.take (rP) ++ (args.drop (rP) ++ [tv])) := by
    have h0 := InterpSpine.append hspPrefix
      (InterpSpine.append hspIdx
        (show InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
          (rP + cnF)
          (fun j => (args.take (rP) ++
            margs.drop cnP).getD j SetTheory.empty) [lastE] [tv] from
          ⟨hmajorI', trivial⟩))
    rwa [← hlargsDecomp] at h0
  have hlvalsEq : lvals =
      args.take (rP) ++ (args.drop (rP) ++ [tv]) := by
    have h1 := InterpSpine.mapM_eq hspL
    have h2 := InterpSpine.mapM_eq hspFull
    rw [h1] at h2
    exact Option.some.inj h2
  have hvlEq : vl = SpineFold V (m₀.val R (Level.substFn φ' lps us))
      (args ++ [tv]) := by
    rw [hvlfold, hvhead, hlvalsEq]
    congr 1
    rw [← List.append_assoc, List.take_append_drop]
  -- ===== S5: the right side is the applied rule =====
  -- mkAppN closure helpers
  have hWapp : ∀ (xs : List Expr) (h : Expr),
      WScoped (rP + cnF) h →
      (∀ x ∈ xs, WScoped (rP + cnF) x) →
      WScoped (rP + cnF) (Expr.mkAppN h xs) := by
    intro xs
    induction xs with
    | nil => intro h hh _; exact hh
    | cons x xs ih =>
      intro h hh hxs
      show WScoped _ (Expr.mkAppN (.app h x) xs)
      refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      simp only [WScoped]
      exact ⟨hh, hxs x List.mem_cons_self⟩
  have hbapp : ∀ (xs : List Expr) (h : Expr),
      h.looseBVarsBounded 0 = true →
      (∀ x ∈ xs, x.looseBVarsBounded 0 = true) →
      (Expr.mkAppN h xs).looseBVarsBounded 0 = true := by
    intro xs
    induction xs with
    | nil => intro h hh _; exact hh
    | cons x xs ih =>
      intro h hh hxs
      show (Expr.mkAppN (.app h x) xs).looseBVarsBounded 0 = true
      refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hh, hxs x List.mem_cons_self⟩
  have hlapp : ∀ (xs : List Expr) (h : Expr) {l},
      l ∈ (Expr.mkAppN h xs).fvarLeaves →
      l ∈ h.fvarLeaves ∨ ∃ x ∈ xs, l ∈ x.fvarLeaves := by
    intro xs
    induction xs with
    | nil => intro h l hl; exact Or.inl hl
    | cons x xs ih =>
      intro h l hl
      rcases ih (.app h x) hl with hl' | ⟨y, hy, hly⟩
      · simp only [fvarLeaves, List.mem_append] at hl'
        rcases hl' with hl' | hl'
        · exact Or.inl hl'
        · exact Or.inr ⟨x, List.mem_cons_self, hl'⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hly⟩
  -- public prefix Θ
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec (rP) 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf (rP) 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  have hfvsPtake : fvsP.take rP = fvsP := by
    rw [← hfvsPLen, List.take_length]
  simp only [hfvsPtake] at hcinstP
  have hspP : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      fvsP (args.take (rP)) := by
    refine FvarSpine_of_open hopenP (by rw [hpreLen]) (by omega) ?_
    intro k v hkv
    refine hρWval k v ?_
    have hk : k < (args.take (rP)).length := by
      rcases Nat.lt_or_ge k (args.take (rP)).length with h | h
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hkv
        exact nomatch hkv
    rw [List.getElem?_append_left hk]
    exact hkv
  have hmemP := fit_mem_transfer (φ := Level.substFn φ' lps us)
    htyw htyb htyPreStrip hfvsPInst (by rw [hfvsPLen]) hspP hspR hfitRawR
  obtain ⟨hfitP, hΘP⟩ := self_walk hfvsPInst hspP
    (fun a ha => ((hfvsPWf a ha).1).mono (by omega))
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
    (FvarsOk.of_not_hasFvar htyw)
    (AnnotOk.closed_invariant htyw _ _ (hAty (Level.substFn φ' lps us)))
    hmemP
  -- ===== N5: pin annotation truthfulness (public side) =====
  obtain ⟨-, -, hArestP, -⟩ := TeleFitI.rest_wf hfitP
    (WScoped.of_not_hasFvar htyw) htyb
    (AnnotOk.closed_invariant htyw _ _ (hAty (Level.substFn φ' lps us)))
  have hrestPEq : restP = instSeq fvsP (rP - 1) restTyPre := by
    have h := (instPisAt_stripPis fvsP hfvsPInst
      (by rw [hfvsPLen]; exact htyPreStrip)).1
    rwa [hfvsPLen] at h
  obtain ⟨bodyWP, hrestPF⟩ : ∃ bW, restP = .forallE nmD
      (instSeq fvsP (rP - 1) domD) bW bmD := by
    refine ⟨instSeq fvsP (rP - 1 + 1) bodyDm, ?_⟩
    rw [hrestPEq, hrestTyPreEq]
    exact instSeq_forallE _ _ _ _ _ _ (by rw [hfvsPLen]; omega)
  rw [hrestPF] at hArestP
  simp only [AnnotOk] at hArestP
  have hAdomWP := hArestP.1
  have hdomWPSplit : instSeq fvsP (rP - 1) domD =
      Expr.mkAppN (instSeq fvsP (rP - 1) domD.getAppFn)
        (pins.map (fun p => instSeq fvsP (rP - 1) p)) := by
    rw [show instSeq fvsP (rP - 1) domD =
        instSeq fvsP (rP - 1) (Expr.mkAppN domD.getAppFn pins) from by
      rw [← hdomEq]]
    rw [instSeq_mkAppN]
  rw [hdomWPSplit] at hAdomWP
  have hApinsP : ∀ a ∈ pins.map (fun p => instSeq fvsP (rP - 1) p),
      AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a :=
    (annotOk_appN_parts _ _ hAdomWP).2
  -- ===== N6: the public pin values at the master frame =====
  have hfvsPShapes : ∀ a ∈ fvsP, ∃ i n t, a = .fvar i n t := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨nm', ha'⟩ := hfvsPShape k a hk
    exact ⟨0 + k, nm', _, ha'⟩
  have hspPSan : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvsP.map sanitizeArg) (args.take rP) :=
    FvarSpine.sanitize hspP
  have hsanPlen : (fvsP.map sanitizeArg).length = rP := by
    rw [List.length_map, hfvsPLen]
  have hsanPShapes : ∀ a ∈ fvsP.map sanitizeArg,
      ∃ i n, a = Expr.fvar i n (.sort .zero) :=
    FvarSpine.sanitize_shapes hspP
  have hsanPShapes' : ∀ a ∈ fvsP.map sanitizeArg,
      ∃ i n t, a = Expr.fvar i n t := by
    intro a ha
    obtain ⟨i, n, rfl⟩ := hsanPShapes a ha
    exact ⟨i, n, _, rfl⟩
  have hsanPInstId : (fvsP.map sanitizeArg).map
      (·.instantiateLevelParams lps us) = fvsP.map sanitizeArg := by
    have h0 : (fvsP.map sanitizeArg).map
        (·.instantiateLevelParams lps us) =
        (fvsP.map sanitizeArg).map id :=
      List.map_congr_left (fun a ha => by
        obtain ⟨i, n, rfl⟩ := hsanPShapes a ha
        rfl)
    rw [h0, List.map_id]
  have hpinValP : ∀ (k : Nat) (a : Expr) (v : V),
      (pins.map (fun p => instSeq fvsP (rP - 1) p))[k]? = some a →
      (margs.take cnP)[k]? = some v →
      interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a = some v := by
    intro k a v ha hv
    rw [List.getElem?_map] at ha
    cases hpk : pins[k]? with
    | none => rw [hpk] at ha; exact nomatch ha
    | some pin => ?_
    rw [hpk] at ha
    obtain rfl := Option.some.inj ha
    have hpinMem : pin ∈ pins := List.mem_of_getElem? hpk
    have hpincl : pin.hasFvar = false := hpinsF pin hpinMem
    have hpinb : pin.looseBVarsBounded rP = true := hpinsB pin hpinMem
    have hptP := InterpSpine.of_mapM hpinsInterp
    have hvP : interpExpr V m₀.val env₀ φ' dP ρP
        (instSeq spineP (spineP.length - 1)
          (pin.instantiateLevelParams lps us)) = some v := by
      refine InterpSpine.pointwise hptP k ?_ hv
      rw [List.getElem?_map, hpk]
      rfl
    rw [hspPlen] at hvP
    have hcross1 := interp_instSeq_fvarFrames (cval := m₀.val)
      (env := env₀) (φ := Level.substFn φ' lps us) (e := pin) hpincl
      (by rw [hfvsPLen]; exact hpinb)
      hspP hspPSan
    rw [hfvsPLen, hsanPlen] at hcross1
    rw [hcross1]
    have hlev : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty)
        (instSeq (fvsP.map sanitizeArg) (rP - 1) pin) =
        interpExpr V m₀.val env₀ φ' (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty)
        (instSeq (fvsP.map sanitizeArg) (rP - 1)
          (pin.instantiateLevelParams lps us)) := by
      rw [show instSeq (fvsP.map sanitizeArg) (rP - 1)
            (pin.instantiateLevelParams lps us) =
          (instSeq (fvsP.map sanitizeArg) (rP - 1)
            pin).instantiateLevelParams lps us from by
        rw [Expr.instSeq_instantiateLevelParams_fvars _ _ _ _ _
          hsanPShapes', hsanPInstId]]
      rw [interp_instLevels hcvp]
    rw [hlev]
    have hspinePP : FvarSpine dP ρP spineP (args.take rP) := by
      rw [hargsTake]
      exact hspineP
    have hcross2 := interp_instSeq_fvarFrames (cval := m₀.val)
      (env := env₀) (φ := φ')
      (e := pin.instantiateLevelParams lps us)
      (by rw [hasFvar_instantiateLevelParams]; exact hpincl)
      (by
        rw [hsanPlen, looseBVarsBounded_instantiateLevelParams]
        exact hpinb)
      hspPSan hspinePP
    rw [hsanPlen, hspPlen] at hcross2
    rw [hcross2]
    exact hvP
  have hpinsPBnd : ∀ a ∈ pins.map (fun p => instSeq fvsP (rP - 1) p),
      a.looseBVarsBounded 0 = true := by
    intro a ha
    obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
    have h0 := instSeq_bclosed (args := fvsP) (e := pin)
      (fun x hx => (hfvsPWf x hx).2.1)
      (by rw [hfvsPLen]; exact hpinsB pin hpin)
    rwa [hfvsPLen] at h0
  have hpinsPWs : ∀ a ∈ pins.map (fun p => instSeq fvsP (rP - 1) p),
      WScoped rP a := by
    intro a ha
    obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
    refine instSeq_wscoped _
      (WScoped.of_not_hasFvar (hpinsF pin hpin)) ?_
    intro x hx
    have := (hfvsPWf x hx).1
    simpa using this
  have hInstPinsP : InstArgs m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (pins.map (fun p => instSeq fvsP (rP - 1) p))
      (margs.take cnP) := by
    refine InstArgs.of_pointwise (by
      rw [List.length_map, hpinslen, List.length_take, hlenm]
      omega) ?_
    intro k a v ha hv
    exact ⟨(hpinsPWs a (List.mem_of_getElem? ha)).mono (by omega),
      hpinsPBnd a (List.mem_of_getElem? ha), hpinValP k a v ha hv⟩
  have hpinsPlen : (pins.map (fun p => instSeq fvsP (rP - 1)
      p)).length = cnP := by
    rw [List.length_map, hpinslen]
  -- the public field variables
  obtain ⟨hxInst, hxLen, hxShape⟩ :=
    openPisAtFvars_spec cnF (rP) hopenX
  have hspX : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      xFvsP (margs.drop cnP) := by
    refine FvarSpine_of_open hopenX (by rw [List.length_drop, hlenm]; omega)
      (by omega) ?_
    intro k v hkv
    have h0 : (args.take (rP) ++
        margs.drop cnP)[rP + k]? = some v := by
      rw [List.getElem?_append_right (by rw [hpreLen]; omega), hpreLen,
        show rP + k - (rP) = k from by omega]
      exact hkv
    show (args.take (rP) ++
      margs.drop cnP).getD (rP + k) SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD, h0]
    rfl
  -- `crestP`'s facts without the fit
  have hT_Pw : (cvj.type.instantiateLevelParams cvj.levelParams
      lvls).hasFvar = false := by
    rw [hasFvar_instantiateLevelParams]
    exact hCw
  have hT_Pb : (cvj.type.instantiateLevelParams cvj.levelParams
      lvls).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_instantiateLevelParams]
    exact hCb
  obtain ⟨restIP, hstripIPre⟩ := Expr.stripPis_prefix cnP cnF hstripI
  have hcrestPEq : crestP = instSeq (pins.map (fun p =>
      instSeq fvsP (rP - 1) p)) (cnP - 1) restIP := by
    have h := (instPisAt_stripPis _ hcinstP
      (by rw [hpinsPlen]; exact hstripIPre)).1
    rwa [hpinsPlen] at h
  have hWcrestPre : WScoped (rP) crestP :=
    (instPisAt_wscoped _ hcinstP
      (WScoped.of_not_hasFvar hT_Pw) hpinsPWs).2
  have hrestIPcl : restIP.hasFvar = false :=
    stripPis_body_hasFvar cnP hstripIPre hT_Pw
  have hbcrestP : crestP.looseBVarsBounded 0 = true := by
    rw [hcrestPEq]
    have h0 := instSeq_bclosed
      (args := pins.map (fun p => instSeq fvsP (rP - 1) p))
      (e := restIP) hpinsPBnd
      (by
        rw [hpinsPlen]
        have h1 := stripPis_body_bounded cnP hstripIPre hT_Pb
        simpa using h1)
    rwa [hpinsPlen] at h0
  have hLcrestP : Expr.LeavesBounded crestP := by
    rw [hcrestPEq]
    intro l hl
    rw [← Expr.instSpine_eq_instSeq] at hl
    rcases fvarLeaves_instSpine (cnP - 1) hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrestIPcl] at hl'
      cases hl'
    · obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
      rw [← Expr.instSpine_eq_instSeq] at hla
      rcases fvarLeaves_instSpine (rP - 1) hla with hl'' | ⟨x, hx, hlx⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar (hpinsF pin hpin)] at hl''
        cases hl''
      · exact (hfvsPWf x hx).2.2 l hlx
  have hFcrestP : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) crestP := by
    rw [hcrestPEq]
    intro l hl
    rw [← Expr.instSpine_eq_instSeq] at hl
    rcases fvarLeaves_instSpine (cnP - 1) hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrestIPcl] at hl'
      cases hl'
    · obtain ⟨pin, hpin, rfl⟩ := List.mem_map.mp ha
      rw [← Expr.instSpine_eq_instSeq] at hla
      rcases fvarLeaves_instSpine (rP - 1) hla with hl'' | ⟨x, hx, hlx⟩
      · rw [fvarLeaves_eq_nil_of_not_hasFvar (hpinsF pin hpin)] at hl''
        cases hl''
      · exact hΘP x hx l hlx
  obtain ⟨hxWf, -⟩ := openPisAtFvars_wf cnF (rP) hopenX
    hWcrestPre hbcrestP hLcrestP
  -- full public constructor packages at the (pins ++ xFvsP) spine
  have hpubP := instPisAt_append_of
    (pins.map (fun p => instSeq fvsP (rP - 1) p)) hcinstP hxInst
  have hInstX : InstArgs m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      xFvsP (margs.drop cnP) :=
    InstArgs_of_FvarSpine hspX
      (fun a ha => ⟨(hxWf a ha).1, (hxWf a ha).2.1⟩)
  have hInstPubW : InstArgs m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (pins.map (fun p => instSeq fvsP (rP - 1) p) ++ xFvsP) margs := by
    have h0 := InstArgs.append hInstPinsP hInstX
    rwa [List.take_append_drop] at h0
  have hpubWlen : (pins.map (fun p => instSeq fvsP (rP - 1) p) ++
      xFvsP).length = cnP + cnF := by
    rw [List.length_append, hpinsPlen, hxLen]
  -- `T_P`'s facts at the master frame
  have hAT_P : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) :=
    AnnotOk.closed_invariant hT_Pw _ _
      (AnnotOk.instLevels hcvp _ 0 (rho0 V)
        (hACty (Level.substFn (Level.substFn φ' lps us)
          cvj.levelParams lvls)))
  have hIT_P : ∃ TP, interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) =
      some TP := by
    obtain ⟨TC, hTCc⟩ := hICty (Level.substFn (Level.substFn φ' lps us)
      cvj.levelParams lvls)
    refine ⟨TC, ?_⟩
    rw [interp_closed_invariant hT_Pw _ _]
    show interpClosed V m₀.val env₀ _
      (cvj.type.instantiateLevelParams cvj.levelParams lvls) = some TC
    unfold interpClosed
    rw [interp_instLevels hcvp]
    exact hTCc
  have hmemPubP := fit_mem_transferI hT_Pw hT_Pb hstripI hpubP hpubWlen
    hInstPubW hspC hmemI
  have hcdomsPLen : cdomsP.length = cnP := by
    rw [instPisAt_length _ hcinstP, hpinsPlen]
  -- the constructor's public parameter walk
  obtain ⟨hfitCP, hIcrestP⟩ := peel_walkI hcinstP hInstPinsP hApinsP
    (WScoped.of_not_hasFvar hT_Pw) hAT_P hIT_P
    (fun k a v ha hv => by
      have hkA : k < cnP := by
        rcases Nat.lt_or_ge k cnP with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by rw [hcdomsPLen]; omega)] at ha
          exact nomatch ha
      refine hmemPubP k a v ?_ ?_
      · rw [List.getElem?_append_left (by rw [hcdomsPLen]; omega)]
        exact ha
      · rw [List.getElem?_take_of_lt hkA] at hv
        exact hv)
  obtain ⟨-, -, hAcrestP, -⟩ := TeleFitI.rest_wf hfitCP
    (WScoped.of_not_hasFvar hT_Pw) hT_Pb hAT_P
  obtain ⟨hfitXP, hΘX2⟩ := self_walk hxInst hspX
    (fun a ha => ((hxWf a ha).1).mono (by omega))
    (hWcrestPre.mono (by omega)) hbcrestP hLcrestP hFcrestP hAcrestP
    (fun k a v ha hv => by
      refine hmemPubP (cnP + k) a v ?_ ?_
      · rw [List.getElem?_append_right (by rw [hcdomsPLen]; omega),
          hcdomsPLen, show cnP + k - cnP = k from by omega]
        exact ha
      · rw [List.getElem?_drop] at hv
        exact hv)
  -- the λ-tower walk of the rule's right-hand side
  have hΘfull : ∀ a ∈ fvsP ++ xFvsP,
      FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘP a ha
    · exact hΘX2 a ha
  have hLfull : ∀ a ∈ fvsP ++ xFvsP, Expr.LeavesBounded a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsPWf a ha).2.2
    · exact (hxWf a ha).2.2
  have hWfull : ∀ a ∈ fvsP ++ xFvsP,
      WScoped (rP + cnF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ((hfvsPWf a ha).1).mono (by omega)
    · exact ((hxWf a ha).1).mono (by omega)
  have hspPX : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvsP ++ xFvsP)
      (args.take (rP) ++ margs.drop cnP) :=
    FvarSpine.append hspP hspX
  have hArhsW : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) rhsA :=
    AnnotOk.closed_invariant hrhsw _ _ (hArhs (Level.substFn φ' lps us))
  obtain ⟨L0, hL0c⟩ := hIrhs (Level.substFn φ' lps us)
  have hL0 : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) rhsA = some L0 := by
    rw [interp_closed_invariant hrhsw _ _]
    exact hL0c
  have hfitLam := lam_walk m₀ F hlinst hdeLam hspPX hWfull hΘfull hLfull
    (WScoped.of_not_hasFvar hrhsw) hrhsb
    (Expr.LeavesBounded.of_not_hasFvar hrhsw)
    (FvarsOk.of_not_hasFvar hrhsw) hArhsW ⟨L0, hL0⟩
  obtain ⟨Bf, hBfI, hBfold, hchainL2⟩ := TeleFitLam.fold hfitLam hArhsW hL0
  -- the applied form's typing and value
  have hrhsRw : (rhsA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hrhsw
  have hArhsRen : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) (rhsA.renameConsts f) :=
    AnnotOk.closed_invariant hrhsRw _ _
      (AnnotOk.renameConsts hro rhsA 0 (rho0 V)
        (hArhs (Level.substFn φ' lps us)))
  have hLren : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (rhsA.renameConsts f) = some L0 := by
    rw [interp_renameConsts hro]
    exact hL0
  have hfvsA : ∀ x ∈ fvs, AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) x := by
    intro x hx
    obtain ⟨i, n, t, rfl⟩ := hfvsShapes x hx
    simp [AnnotOk]
  obtain ⟨hAappF, hIappF⟩ := annotOk_spine fvs (rhsA.renameConsts f)
    hArhsRen hLren hfvsA (InterpSpine_of_FvarSpine hspW) hchainL2
  -- side conditions for the statement's right side
  have hΘfvs : ∀ a ∈ fvs,
      FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a := by
    intro a ha
    rw [← List.take_append_drop (rP) fvs] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘpre a ha
    · exact hΘx a ha
  have hWappF : WScoped (rP + cnF)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) :=
    hWapp fvs _ (WScoped.of_not_hasFvar hrhsRw) hfvsW
  have hbappF : (Expr.mkAppN (rhsA.renameConsts f)
      fvs).looseBVarsBounded 0 = true := by
    refine hbapp fvs _ ?_ (FvarSpine.bounded hspW)
    rw [looseBVarsBounded_renameConsts]
    exact hrhsb
  have hLappF : Expr.LeavesBounded
      (Expr.mkAppN (rhsA.renameConsts f) fvs) := by
    intro l hl
    rcases hlapp fvs _ hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hl'
      cases hl'
    · exact (hfvsWf x hx).2.2 l hlx
  have hFappF : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) := by
    intro l hl
    rcases hlapp fvs _ hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hl'
      cases hl'
    · exact hΘfvs x hx l hlx
  have hvrFold : vr = SpineFold V L0
      (args.take (rP) ++ margs.drop cnP) :=
    isDefEqCore_sound m₀ F hdeRhs hWrhsS hWappF hbrhsS hbappF hLrhsS
      hLappF hFrhsS hFappF hArhsS hAappF hir hIappF
  -- ===== S6: conclusion =====
  refine ⟨L0, hL0c, ?_, ?_⟩
  · rw [← hvlEq, hvlvr, hvrFold]
  · exact hchainL2

end Setlec
