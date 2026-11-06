module

public import InLeanProof.IotaViews
public import InLeanProof.WalksWhnfLoop

/-!
# InLean's body walks, part 4: the ι step (task #451, lane P2-whnf)

The twins of `Verify/Cached/DiscC3.lean`'s rescue and ι walks:
`majorToCtorI` with its three rescue blocks (K, structure η, `And`),
`prepareMajorI`, the case-3 certificate block, and `iotaRecI`, which
discharges `IotaRecSpecI` (`WalksWhnfLoop.lean`).

As in `WalksIota.lean`, the pure side matches on records con-leche reads
off its environment, InLean on the views it reads off Lean's (`EnvViewI`,
`EnvRecI`), and on heads through `EO.stripTop`/`getAppFnT`: the walks are
proved run by run (`tripleI_iff_run`, `bind_run`), each InLean block named
as its cached twin names it (`mtcKIL`, `mtcEtaIL`, `mtcAndIL`, `mtcBodyIL`,
`iotaCertIL`; `rfl` restatements of `majorToCtorI`'s and `iotaRecI`'s
branches) against master's pure blocks (`mtcKCont`, `mtcEtaCont`,
`mtcAndCont`, `mtcBodyP`, `iotaCertP`, `iotaRecK`).

Two callees are named hypotheses: P2-defeq's `proofIrrelI`
(`ProofIrrelSpecI`), and the leaf guard (`LeafGuardSpecI`,
`LeafGuardI.lean`).
-/

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {eager : Bool} {env : ConLeche.Env}

/-! ## Callee specs owned elsewhere -/

/-- `proofIrrelI`'s spec (`proofIrrelC_spec`'s twin), P2-defeq's to prove. -/
abbrev ProofIrrelSpecI (eager : Bool) (env : ConLeche.Env) (r : InLean.CoreFnsI) : Prop :=
  ∀ {d : Nat} {a b : Expr} {s₀ : InLean.CState},
    CSOKI .verified eager env s₀ → OkS s₀ a = true → OkS s₀ b = true →
    ConLeche.Expr.WScoped d (TrS s₀ a) → ConLeche.Expr.WScoped d (TrS s₀ b) →
    (TrS s₀ a).looseBVarsBounded 0 = true → (TrS s₀ b).looseBVarsBounded 0 = true →
    ⦃fun s => s = s₀⦄ InLean.proofIrrelI r d a b
    ⦃fun v s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.proofIrrel (ConLeche.fueledFns .verified eager env) d (TrS s₀ a) (TrS s₀ b))
        v; ⊤⦄

/-- `leafGuardM`'s spec as a named hypothesis. -/
abbrev LeafGuardSpecI (mode : ConLeche.CheckMode) (eager : Bool) (env : ConLeche.Env) : Prop :=
  ∀ {s₀ : InLean.CState} {fab base : Expr}, CSOKI mode eager env s₀ → OkS s₀ fab = true →
    OkS s₀ base = true →
    ⦃fun s => s = s₀⦄ InLean.leafGuardM fab base
    ⦃fun v s' => s' = s₀ ∧ v = ConLeche.Cached.leafGuardP (TrS s₀ fab) (TrS s₀ base); ⊤⦄

/-! ## Lists through the translation -/

section Lists
variable (s : InLean.CState)

theorem TrSL_take (l : List Expr) (k : Nat) : TrSL s (l.take k) = (TrSL s l).take k := by
  simp [TrSL, List.map_take]

theorem TrSL_drop (l : List Expr) (k : Nat) : TrSL s (l.drop k) = (TrSL s l).drop k := by
  simp [TrSL, List.map_drop]

theorem TrSL_append (l l' : List Expr) : TrSL s (l ++ l') = TrSL s l ++ TrSL s l' := by
  simp [TrSL]

theorem TrSL_length (l : List Expr) : (TrSL s l).length = l.length := by simp [TrSL]

theorem OkSL_take {l : List Expr} (h : OkSL s l = true) (k : Nat) : OkSL s (l.take k) = true := by
  simp only [OkSL, List.all_eq_true] at h ⊢; exact fun x hx => h x (List.mem_of_mem_take hx)

theorem OkSL_drop {l : List Expr} (h : OkSL s l = true) (k : Nat) : OkSL s (l.drop k) = true := by
  simp only [OkSL, List.all_eq_true] at h ⊢; exact fun x hx => h x (List.mem_of_mem_drop hx)

theorem OkSL_append {l l' : List Expr} (h : OkSL s l = true) (h' : OkSL s l' = true) :
    OkSL s (l ++ l') = true := by
  simp only [OkSL] at h h' ⊢; rw [List.all_append, h, h']; rfl

end Lists

theorem AllClosed_take {l : List ConLeche.Expr} (h : AllClosed l = true) (k : Nat) :
    AllClosed (l.take k) = true := by
  simp only [AllClosed, List.all_eq_true] at h ⊢; exact fun x hx => h x (List.mem_of_mem_take hx)

theorem AllClosed_drop {l : List ConLeche.Expr} (h : AllClosed l = true) (k : Nat) :
    AllClosed (l.drop k) = true := by
  simp only [AllClosed, List.all_eq_true] at h ⊢; exact fun x hx => h x (List.mem_of_mem_drop hx)

theorem AllClosed_append {l l' : List ConLeche.Expr} (h : AllClosed l = true)
    (h' : AllClosed l' = true) : AllClosed (l ++ l') = true := by
  simp only [AllClosed] at h h' ⊢; rw [List.all_append, h, h']; rfl

/-! ## The rescue's blocks, named -/

section Blocks
variable (mode : InLean.CheckMode)

/-- The K rescue past its syntactic gates (`majorToCtorI`'s K branch). -/
@[expose] def mtcKIL (r : InLean.CoreFnsI) (depth : Nat) (major : Expr) (rl : RecursorRule)
    (cvj : Lean.ConstantVal) (cnP : Nat) (T : Name) : InLean.CheckCM Expr := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  match tmaj.getAppFnT with
  | .const T' ust =>
    if T' == T ∧ cvj.levelParams.length = ust.length then do
      let margs := appArgs tmaj
      if cnP ≤ margs.length then do
        let fab ← mkAppNM (.const rl.ctor ust) (margs.take cnP)
        if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then do
          let tfab ← r.inferIO depth fab
          if ← r.defeq depth tmaj tfab then
            if ← certAtI mode (proofIrrelI r depth fab major) then pure fab
            else pure major
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- The structure-η rescue past its syntactic gates. -/
@[expose] def mtcEtaIL (r : InLean.CoreFnsI) (fe : InLean.FEnv) (depth : Nat) (major : Expr) (T : Name)
    (cvT : Lean.ConstantVal) (caps : InLean.IndCaps) : InLean.CheckCM Expr := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  match tmaj.getAppFnT with
  | .const T' ust => do
    let margs := appArgs tmaj
    if T' == T ∧ margs.length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        InLean.reservedBasisNames.contains T = false ∧
        InLean.reservedBasisNames.contains caps.etaCtor = false ∧
        fe.towerSlotsAllF T caps.etaFields = true then do
      if ← formerNeverZeroI r.whnf cvT caps ust then do
        let fab ← mkAppNM (.const caps.etaCtor ust)
          (margs ++ projNodesI T major (List.range caps.etaFields))
        if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then
          pure fab
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- The `And` rescue past its syntactic gates. -/
@[expose] def mtcAndIL (r : InLean.CoreFnsI) (fe : InLean.FEnv) (depth : Nat) (major : Expr)
    (rl : RecursorRule) (cvj : Lean.ConstantVal) (cnP : Nat) (T : Name) : InLean.CheckCM Expr := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  match tmaj.getAppFnT with
  | .const T' ust => do
    let margs := appArgs tmaj
    if T' == T ∧ margs.length = cnP ∧
        cvj.levelParams.length = ust.length ∧
        fe.andRescueSlotsF rl.ctor cnP = true then do
      let fab ← mkAppNM (.const rl.ctor ust) (margs ++ projNodesI T major [0, 1])
      if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then do
        let tfab ← r.inferIO depth fab
        if ← r.defeq depth tmaj tfab then
          if ← certAtI mode (proofIrrelI r depth fab major) then pure fab
          else pure major
        else pure major
      else pure major
    else pure major
  | _ => pure major

/-- The rescue past its syntactic gates. -/
@[expose] def mtcBodyIL (r : InLean.CoreFnsI) (fe : InLean.FEnv) (depth : Nat) (major : Expr) (isK : Bool)
    (rl : RecursorRule) (cvj : Lean.ConstantVal) (cnP : Nat) (T : Name) (cvT : Lean.ConstantVal)
    (caps : InLean.IndCaps) : InLean.CheckCM Expr :=
  if isK = true then mtcKIL mode r depth major rl cvj cnP T
  else if etaRescueOk rl.ctor cvj cvT caps = true then mtcEtaIL r fe depth major T cvT caps
  else if T == andName then mtcAndIL mode r fe depth major rl cvj cnP T
  else pure major

/-- `majorToCtorI` with its blocks named. -/
theorem majorToCtorI_eq (r : InLean.CoreFnsI) (fe : InLean.FEnv) (depth : Nat) (isK : Bool)
    (rules : List RecursorRule) (major : Expr) :
    majorToCtorI mode r fe depth isK rules major =
    (if isCtorAppC fe major then pure major else
    match rules with
    | [rl] =>
      match fe.ctorView? rl.ctor with
      | some (cvj, cnP, _) =>
        match EO.stripTop ((piResult cvj.type).getAppFnT) with
        | .const T _ =>
          match fe.indView? T with
          | some (cvT, caps) => mtcBodyIL mode r fe depth major isK rl cvj cnP T cvT caps
          | none => pure major
        | _ => pure major
      | none => pure major
    | _ => pure major) := rfl

end Blocks

/-! ## The rescue's walks -/

/-- The two syntactic guards of a fabrication, at a reading that is scoped
and closed (the fork's `LeafGuardI.lean` proves both). -/
abbrev GuardBridges : Prop :=
  (∀ {s : InLean.CState} {e : Expr} {d : Nat}, OkS s e = true →
    ConLeche.Expr.WScoped d (TrS s e) → InLean.Expr.wscopedBC d e = true) ∧
  (∀ {s : InLean.CState} {e : Expr}, OkS s e = true → (TrS s e).looseBVarsBounded 0 = true →
    InLean.Expr.closedBV e = true)

/-- The post at a term read at an earlier state. -/
theorem post_of {mode : ConLeche.CheckMode} {s₀ s' : InLean.CState} {d : Nat} {e : Expr}
    {P : ConLeche.FueledM ConLeche.Expr} (hs' : CSOKI mode eager env s') (ht : TabLe s₀ s')
    (hok : OkS s₀ e = true) (hw : ConLeche.Expr.WScoped d (TrS s₀ e))
    (hc : (TrS s₀ e).looseBVarsBounded 0 = true) (hP : Runs P (TrS s₀ e)) :
    CSOKI mode eager env s' ∧ TabLe s₀ s' ∧ OkS s' e = true ∧ Runs P (TrS s' e) ∧
      ConLeche.Expr.WScoped d (TrS s' e) ∧ (TrS s' e).looseBVarsBounded 0 = true := by
  rw [TrS_of_tabLe ht hok]; exact ⟨hs', ht, okS_of_tabLe ht hok, hP, hw, hc⟩

/-- The K and `And` rescues' tail past the fabrication (InLean). -/
@[expose] def fabTailIL (r : InLean.CoreFnsI) (depth : Nat) (tmaj fab major : Expr) :
    InLean.CheckCM Expr := do
  if Expr.wscopedBC depth fab && (Expr.closedBV fab) && (← leafGuardM fab major) then do
    let tfab ← r.inferIO depth fab
    if ← r.defeq depth tmaj tfab then
      if ← certAtI .verified (proofIrrelI r depth fab major) then pure fab
      else pure major
    else pure major
  else pure major

/-- The K and `And` rescues' tail past the fabrication (pure). -/
@[expose] def fabTailP (F : ConLeche.CoreFns ConLeche.FueledM) (depth : Nat)
    (tmaj fab major : ConLeche.Expr) : ConLeche.FueledM ConLeche.Expr :=
  if fab.wscopedB depth && fab.looseBVarsBounded 0 && leafGuardP fab major then
    F.inferIO depth fab >>= fun tfab => F.defeq depth tmaj tfab >>= fun rd =>
      if rd then
        proofIrrelGate .verified F depth fab major >>= fun ok =>
          if ok then pure fab else pure major
      else pure major
  else pure major

section Walks
variable {r : InLean.CoreFnsI} {fe : InLean.FEnv}

theorem fabTailIL_specI (ih : KnotSpecI .verified eager env r) (hpi : ProofIrrelSpecI eager env r)
    (hlg : LeafGuardSpecI .verified eager env) (hgb : GuardBridges) {d : Nat}
    {tmaj fab major : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hokt : OkS s₀ tmaj = true) (hwt : ConLeche.Expr.WScoped d (TrS s₀ tmaj))
    (hct : (TrS s₀ tmaj).looseBVarsBounded 0 = true)
    (hokf : OkS s₀ fab = true) (hwf : ConLeche.Expr.WScoped d (TrS s₀ fab))
    (hcf : (TrS s₀ fab).looseBVarsBounded 0 = true)
    (hokm : OkS s₀ major = true) (hwm : ConLeche.Expr.WScoped d (TrS s₀ major))
    (hcm : (TrS s₀ major).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ fabTailIL r d tmaj fab major
    ⦃fun m s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' m = true ∧
      Runs (fabTailP (ConLeche.fueledFns .verified eager env) d (TrS s₀ tmaj) (TrS s₀ fab)
        (TrS s₀ major)) (TrS s' m) ∧
      ConLeche.Expr.WScoped d (TrS s' m) ∧ (TrS s' m).looseBVarsBounded 0 = true; ⊤⦄ := by
  refine tripleI_iff_run.2 fun m s' hr => ?_
  unfold fabTailIL at hr
  obtain ⟨g, s₁, hg, hr⟩ := bind_run hr
  obtain ⟨rfl, rfl⟩ := tripleI_iff_run.1 (hlg hs hokf hokm) g s₁ hg
  unfold fabTailP
  rw [hgb.1 hokf hwf, hgb.2 hokf hcf, Bool.true_and, Bool.true_and] at hr
  rw [hwf.to_wscopedB, hcf, Bool.true_and, Bool.true_and]
  by_cases hl : leafGuardP (TrS s₁ fab) (TrS s₁ major) = true
  · simp only [hl, ↓reduceIte] at hr ⊢
    obtain ⟨tfab, s₂, h2, hr⟩ := bind_run hr
    obtain ⟨hs₂, ht₂, hok₂, hrun₂, hw₂, hc₂⟩ :=
      tripleI_iff_run.1 (ih.inferIO hs hokf hwf hcf) tfab s₂ h2
    rw [Runs.bind_eq _ hrun₂]
    obtain ⟨rd, s₃, h3, hr⟩ := bind_run hr
    have hokt₂ := okS_of_tabLe ht₂ hokt
    have htt₂ := TrS_of_tabLe ht₂ hokt
    obtain ⟨hs₃, ht₃, hrun₃⟩ := tripleI_iff_run.1
      (ih.defeq hs₂ hokt₂ hok₂ (htt₂ ▸ hwt) hw₂ (htt₂ ▸ hct) hc₂) rd s₃ h3
    rw [htt₂] at hrun₃
    rw [Runs.bind_eq _ hrun₃]
    cases rd with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
      obtain ⟨rfl, rfl⟩ := pure_run hr
      exact post_of hs₃ (ht₂.trans ht₃) hokm hwm hcm (Runs.pure _)
    | true =>
      simp only [↓reduceIte] at hr ⊢
      obtain ⟨ok, s₄, h4, hr⟩ := bind_run hr
      have ht₂₃ := ht₂.trans ht₃
      simp only [InLean.certAtI, InLean.CheckMode.verifiedChecks, ↓reduceIte] at h4
      obtain ⟨hs₄, ht₄, hrun₄⟩ := tripleI_iff_run.1
        (hpi hs₃ (okS_of_tabLe ht₂₃ hokf) (okS_of_tabLe ht₂₃ hokm)
          (by rw [TrS_of_tabLe ht₂₃ hokf]; exact hwf) (by rw [TrS_of_tabLe ht₂₃ hokm]; exact hwm)
          (by rw [TrS_of_tabLe ht₂₃ hokf]; exact hcf) (by rw [TrS_of_tabLe ht₂₃ hokm]; exact hcm))
        ok s₄ h4
      rw [TrS_of_tabLe ht₂₃ hokf, TrS_of_tabLe ht₂₃ hokm] at hrun₄
      rw [proofIrrelGate_of, Runs.bind_eq _ hrun₄]
      cases ok with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
        obtain ⟨rfl, rfl⟩ := pure_run hr
        exact post_of hs₄ (ht₂₃.trans ht₄) hokm hwm hcm (Runs.pure _)
      | true =>
        simp only [↓reduceIte] at hr ⊢
        obtain ⟨rfl, rfl⟩ := pure_run hr
        exact post_of hs₄ (ht₂₃.trans ht₄) hokf hwf hcf (Runs.pure _)
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hr ⊢
    obtain ⟨rfl, rfl⟩ := pure_run hr
    exact post_of hs (TabLe.refl _) hokm hwm hcm (Runs.pure _)

/-- A head constant's levels have readings. -/
theorem okLv_of_getAppFnT {s : InLean.CState} {e : Expr} {n : Name} {us : List Level}
    (he : OkS s e = true) (h : Expr.getAppFnT e = .const n us) : us.all okLv = true := by
  have := OkS_getAppFnT s he
  rw [h, OkS_const] at this
  exact this

/-- The fabricated constructor application's facts. -/
theorem fab_facts {s : InLean.CState} {d : Nat} {c : Name} {us : List Level} {xs : List Expr}
    (hus : us.all okLv = true) (hxs : OkSL s xs = true) (hw : AllWS d (TrSL s xs))
    (hcl : AllClosed (TrSL s xs) = true) :
    OkS s (mkAppN (.const c us) xs.toArray) = true ∧
      TrS s (mkAppN (.const c us) xs.toArray) =
        ConLeche.Expr.mkAppN (.const (toName c) (us.map trL)) (TrSL s xs) ∧
      ConLeche.Expr.WScoped d (TrS s (mkAppN (.const c us) xs.toArray)) ∧
      (TrS s (mkAppN (.const c us) xs.toArray)).looseBVarsBounded 0 = true := by
  rw [OkS_mkAppN, TrS_mkAppN, OkS_const, TrS_const, hus, hxs]
  exact ⟨rfl, rfl, wscoped_mkAppN_const hw, lbb_mkAppN_closed rfl hcl⟩

theorem mtcKIL_specI (ih : KnotSpecI .verified eager env r) (hpi : ProofIrrelSpecI eager env r)
    (hlg : LeafGuardSpecI .verified eager env) (hgb : GuardBridges) {d : Nat} {major : Expr}
    {rl : RecursorRule} {cvj : Lean.ConstantVal} {cnP : Nat} {T : Name} {crl : ConLeche.RecRule}
    {ccvj : ConLeche.ConstantVal} (hrl : crl.ctor = toName rl.ctor) (hcvj : CVRel cvj ccvj)
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hok : OkS s₀ major = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ major))
    (hc : (TrS s₀ major).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ mtcKIL .verified r d major rl cvj cnP T
    ⦃fun m s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' m = true ∧
      Runs ((ConLeche.fueledFns .verified eager env).inferIO d (TrS s₀ major) >>= fun tm =>
        (ConLeche.fueledFns .verified eager env).whnf d tm >>=
          mtcKCont .verified (ConLeche.fueledFns .verified eager env) d (TrS s₀ major) crl ccvj cnP
            (toName T)) (TrS s' m) ∧
      ConLeche.Expr.WScoped d (TrS s' m) ∧ (TrS s' m).looseBVarsBounded 0 = true; ⊤⦄ := by
  refine tripleI_iff_run.2 fun m s' hr => ?_
  unfold mtcKIL at hr
  obtain ⟨tm, s₁, h1, hr⟩ := bind_run hr
  obtain ⟨hs₁, ht₁, hok₁, hrun₁, hw₁, hc₁⟩ := tripleI_iff_run.1 (ih.inferIO hs hok hw hc) tm s₁ h1
  obtain ⟨tmaj, s₂, h2, hr⟩ := bind_run hr
  obtain ⟨hs₂, ht₂, hok₂, hrun₂, hw₂, hc₂⟩ :=
    tripleI_iff_run.1 (ih.whnf hs₁ hok₁ hw₁ hc₁) tmaj s₂ h2
  have ht02 := ht₁.trans ht₂
  rw [Runs.bind_eq _ hrun₁, Runs.bind_eq _ hrun₂]
  unfold mtcKCont
  dsimp only at hr
  by_cases hconst : ∃ T' ust, Expr.getAppFnT tmaj = .const T' ust
  · obtain ⟨T', ust, hfn⟩ := hconst
    rw [hfn] at hr
    dsimp only at hr
    rw [TrS_getAppFn_const s₂ hfn]
    dsimp only
    have hust := okLv_of_getAppFnT hok₂ hfn
    by_cases hcond : (T' == T) = true ∧ cvj.levelParams.length = ust.length
    · have hcond' : toName T' = toName T ∧ ccvj.levelParams.length = (ust.map trL).length := by
        refine ⟨by rw [eq_of_beq hcond.1], ?_⟩
        rw [hcvj.2.1, List.length_map, List.length_map, hcond.2]
      simp only [hcond, hcond', and_self, ↓reduceIte] at hr ⊢
      have hlen : (appArgs tmaj).length = (TrS s₂ tmaj).getAppArgs.length := by
        rw [← TrSL_appArgs, TrSL_length]
      by_cases hle : cnP ≤ (appArgs tmaj).length
      · have hle' : cnP ≤ (TrS s₂ tmaj).getAppArgs.length := hlen ▸ hle
        simp only [hle, hle', ↓reduceIte] at hr ⊢
        obtain ⟨fab, s₃, h3, hr⟩ := bind_run hr
        obtain ⟨rfl, rfl⟩ := pure_run h3
        have hxs := OkSL_take s₂ (OkSL_appArgs s₂ hok₂) cnP
        have hTx : TrSL s₂ ((appArgs tmaj).take cnP) = (TrS s₂ tmaj).getAppArgs.take cnP := by
          rw [TrSL_take, TrSL_appArgs]
        obtain ⟨hokf, htrf, hwf, hcf⟩ := fab_facts (c := rl.ctor) hust hxs
          (by rw [hTx]; exact (allWS_getAppArgs hw₂).take cnP)
          (by rw [hTx]; exact AllClosed_take (allClosed_getAppArgs hc₂) cnP)
        have hr' : fabTailIL r d tmaj (mkAppN (.const rl.ctor ust) ((appArgs tmaj).take cnP).toArray)
            major s₂ = .ok (m, s') := hr
        have hokm := okS_of_tabLe ht02 hok
        have htm := TrS_of_tabLe ht02 hok
        obtain ⟨hs', ht', hokm', hrun', hw', hc'⟩ := tripleI_iff_run.1
          (fabTailIL_specI ih hpi hlg hgb hs₂ hok₂ hw₂ hc₂ hokf hwf hcf hokm (htm ▸ hw) (htm ▸ hc))
          m s' hr'
        refine ⟨hs', ht02.trans ht', hokm', ?_, hw', hc'⟩
        rw [htrf, hTx, htm] at hrun'
        rw [hrl]; exact hrun'
      · have hle' : ¬ cnP ≤ (TrS s₂ tmaj).getAppArgs.length := hlen ▸ hle
        simp only [hle, hle', ↓reduceIte] at hr ⊢
        obtain ⟨rfl, rfl⟩ := pure_run hr
        exact post_of hs₂ ht02 hok hw hc (Runs.pure _)
    · have hcond' : ¬ (toName T' = toName T ∧ ccvj.levelParams.length = (ust.map trL).length) := by
        rintro ⟨h1, h2⟩
        apply hcond
        refine ⟨by rw [toName_inj h1]; exact beq_self_eq_true _, ?_⟩
        rw [hcvj.2.1, List.length_map, List.length_map] at h2; exact h2
      simp only [hcond, hcond', ↓reduceIte] at hr ⊢
      obtain ⟨rfl, rfl⟩ := pure_run hr
      exact post_of hs₂ ht02 hok hw hc (Runs.pure _)
  · have hfn : ∀ n us, Expr.getAppFnT tmaj ≠ .const n us := fun n us h => hconst ⟨n, us, h⟩
    have hn := TrS_getAppFn_notConst s₂ hfn
    have hr' : (pure major : InLean.CheckCM Expr) s₂ = .ok (m, s') := by
      rw [← hr]
      generalize hx : Expr.getAppFnT tmaj = x at hfn
      cases x with
      | const a b => exact absurd rfl (hfn a b)
      | _ => rfl
    obtain ⟨rfl, rfl⟩ := pure_run hr'
    split
    · rename_i c us' h'; exact absurd h' (hn c us')
    · exact post_of hs₂ ht02 hok hw hc (Runs.pure _)

/-- The fabricated projections through the translation. -/
theorem projNodesI_facts (s : InLean.CState) (T : Name) {b : Expr} {d : Nat} (hb : OkS s b = true)
    (hw : ConLeche.Expr.WScoped d (TrS s b)) (hc : (TrS s b).looseBVarsBounded 0 = true) :
    ∀ js : List Nat, OkSL s (InLean.projNodesI T b js) = true ∧
      TrSL s (InLean.projNodesI T b js) = js.map (fun j => ConLeche.Expr.proj (toName T) j (TrS s b)) ∧
      AllWS d (TrSL s (InLean.projNodesI T b js)) ∧
      AllClosed (TrSL s (InLean.projNodesI T b js)) = true
  | [] => ⟨rfl, rfl, by intro x hx; simp [InLean.projNodesI, TrSL] at hx, rfl⟩
  | j :: js => by
    obtain ⟨h1, h2, h3, h4⟩ := projNodesI_facts s T hb hw hc js
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [InLean.projNodesI, OkSL_cons, OkS_proj, hb, h1, Bool.and_self]
    · rw [InLean.projNodesI, TrSL_cons, h2, TrS_proj, List.map_cons]
    · rw [InLean.projNodesI, TrSL_cons, TrS_proj]
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · simpa [ConLeche.Expr.WScoped] using hw
      · exact h3 x hx
    · rw [InLean.projNodesI, TrSL_cons, AllClosed_cons, h4, TrS_proj, lbb_proj, hc]; rfl

theorem mtcEtaIL_specI (ih : KnotSpecI .verified eager env r) (hlg : LeafGuardSpecI .verified eager env)
    (hgb : GuardBridges) (hv : EnvViewI fe env) {d : Nat} {major : Expr} {T : Name}
    {cvT : Lean.ConstantVal} {ccvT : ConLeche.ConstantVal} (hcvT : CVRel cvT ccvT)
    (hcl : ccvT.type.hasFvar = false) (hlbb : ccvT.type.looseBVarsBounded 0 = true)
    {caps : InLean.IndCaps}
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hok : OkS s₀ major = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ major))
    (hc : (TrS s₀ major).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ mtcEtaIL r fe d major T cvT caps
    ⦃fun m s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' m = true ∧
      Runs ((ConLeche.fueledFns .verified eager env).inferIO d (TrS s₀ major) >>= fun tm =>
        (ConLeche.fueledFns .verified eager env).whnf d tm >>=
          mtcEtaCont (ConLeche.fueledFns .verified eager env) env d (TrS s₀ major) (toName T) ccvT
            (toCaps caps)) (TrS s' m) ∧
      ConLeche.Expr.WScoped d (TrS s' m) ∧ (TrS s' m).looseBVarsBounded 0 = true; ⊤⦄ := by
  refine tripleI_iff_run.2 fun m s' hr => ?_
  unfold mtcEtaIL at hr
  obtain ⟨tm, s₁, h1, hr⟩ := bind_run hr
  obtain ⟨hs₁, ht₁, hok₁, hrun₁, hw₁, hc₁⟩ := tripleI_iff_run.1 (ih.inferIO hs hok hw hc) tm s₁ h1
  obtain ⟨tmaj, s₂, h2, hr⟩ := bind_run hr
  obtain ⟨hs₂, ht₂, hok₂, hrun₂, hw₂, hc₂⟩ :=
    tripleI_iff_run.1 (ih.whnf hs₁ hok₁ hw₁ hc₁) tmaj s₂ h2
  have ht02 := ht₁.trans ht₂
  rw [Runs.bind_eq _ hrun₁, Runs.bind_eq _ hrun₂]
  unfold mtcEtaCont
  dsimp only at hr
  by_cases hconst : ∃ T' ust, Expr.getAppFnT tmaj = .const T' ust
  · obtain ⟨T', ust, hfn⟩ := hconst
    rw [hfn] at hr
    dsimp only at hr
    rw [TrS_getAppFn_const s₂ hfn]
    dsimp only
    have hust := okLv_of_getAppFnT hok₂ hfn
    have hlen : (appArgs tmaj).length = (TrS s₂ tmaj).getAppArgs.length := by
      rw [← TrSL_appArgs, TrSL_length]
    have hiff : ((T' == T) = true ∧ (appArgs tmaj).length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        InLean.reservedBasisNames.contains T = false ∧
        InLean.reservedBasisNames.contains caps.etaCtor = false ∧
        fe.towerSlotsAllF T caps.etaFields = true) ↔
        (toName T' = toName T ∧ (TrS s₂ tmaj).getAppArgs.length = (toCaps caps).etaParams ∧
        (ust.map trL).length = ccvT.levelParams.length ∧
        ConLeche.reservedBasisNames.contains (toName T) = false ∧
        ConLeche.reservedBasisNames.contains (toCaps caps).etaCtor = false ∧
        ConLeche.towerSlotsAll env (toName T) (toCaps caps).etaFields = true) := by
      simp only [toCaps, reserved_contains, ← towerSlotsAllF_V hv, hcvT.2.1, List.length_map,
        ← hlen, toName_eq_iff, beq_iff_eq]
    by_cases hcond : (T' == T) = true ∧ (appArgs tmaj).length = caps.etaParams ∧
        ust.length = cvT.levelParams.length ∧
        InLean.reservedBasisNames.contains T = false ∧
        InLean.reservedBasisNames.contains caps.etaCtor = false ∧
        fe.towerSlotsAllF T caps.etaFields = true
    · have hcond' := hiff.1 hcond
      simp only [hcond, hcond', and_self, ↓reduceIte] at hr ⊢
      obtain ⟨nz, s₃, h3, hr⟩ := bind_run hr
      obtain ⟨hs₃, ht₃, hrun₃⟩ := tripleI_iff_run.1
        (formerNeverZeroI_specI ih hcvT hcl hlbb caps hust hs₂) nz s₃ h3
      rw [Runs.bind_eq _ hrun₃]
      have ht03 := ht02.trans ht₃
      cases nz with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
        obtain ⟨rfl, rfl⟩ := pure_run hr
        exact post_of hs₃ ht03 hok hw hc (Runs.pure _)
      | true =>
        simp only [↓reduceIte] at hr ⊢
        obtain ⟨fab, s₄, h4, hr⟩ := bind_run hr
        obtain ⟨rfl, rfl⟩ := pure_run h4
        have hok₃ := okS_of_tabLe ht₃ hok₂
        have htt₃ := TrS_of_tabLe ht₃ hok₂
        have hokm := okS_of_tabLe ht03 hok
        have htm := TrS_of_tabLe ht03 hok
        obtain ⟨hp1, hp2, hp3, hp4⟩ := projNodesI_facts s₃ T hokm (htm ▸ hw) (htm ▸ hc)
          (List.range caps.etaFields)
        have hxs : OkSL s₃ (appArgs tmaj ++ InLean.projNodesI T major (List.range caps.etaFields))
            = true := OkSL_append s₃ (OkSL_appArgs s₃ hok₃) hp1
        have hTx : TrSL s₃ (appArgs tmaj ++ InLean.projNodesI T major (List.range caps.etaFields))
            = ConLeche.etaFabArgsE (toName T) (TrS s₂ tmaj).getAppArgs (TrS s₀ major)
                (toCaps caps).etaFields := by
          rw [TrSL_append, TrSL_appArgs, hp2, htt₃, htm]; rfl
        have hws1 : AllWS d (TrSL s₃ (appArgs tmaj)) := by
          rw [TrSL_appArgs, htt₃]; exact allWS_getAppArgs hw₂
        have hcl1 : AllClosed (TrSL s₃ (appArgs tmaj)) = true := by
          rw [TrSL_appArgs, htt₃]; exact allClosed_getAppArgs hc₂
        obtain ⟨hokf, htrf, hwf, hcf⟩ := fab_facts (c := caps.etaCtor) hust hxs
          (by rw [TrSL_append]; exact AllWS.append hws1 hp3)
          (by rw [TrSL_append]; exact AllClosed_append hcl1 hp4)
        obtain ⟨g, s₅, h5, hr⟩ := bind_run hr
        obtain ⟨hst, rfl⟩ := tripleI_iff_run.1 (hlg hs₃ hokf hokm) g s₅ h5
        rw [hst] at hr
        rw [hgb.1 hokf hwf, hgb.2 hokf hcf, Bool.true_and, Bool.true_and] at hr
        have hwf' := hwf
        have hcf' := hcf
        rw [htrf, hTx] at hwf' hcf'
        have hec : (toCaps caps).etaCtor = toName caps.etaCtor := rfl
        rw [hec, hwf'.to_wscopedB, hcf', Bool.true_and, Bool.true_and]
        rw [htrf, hTx, htm] at hr
        by_cases hl : leafGuardP (ConLeche.Expr.mkAppN
            (.const (toName caps.etaCtor) (ust.map trL))
            (ConLeche.etaFabArgsE (toName T) (TrS s₂ tmaj).getAppArgs (TrS s₀ major)
              (toCaps caps).etaFields)) (TrS s₀ major) = true
        · simp only [hl, ↓reduceIte] at hr ⊢
          obtain ⟨rfl, rfl⟩ := pure_run hr
          refine ⟨hs₃, ht03, hokf, ?_, hwf, hcf⟩
          rw [htrf, hTx]; exact Runs.pure _
        · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hr ⊢
          obtain ⟨rfl, rfl⟩ := pure_run hr
          exact post_of hs₃ ht03 hok hw hc (Runs.pure _)
    · have hcond' := mt hiff.2 hcond
      simp only [hcond, hcond', ↓reduceIte] at hr ⊢
      obtain ⟨rfl, rfl⟩ := pure_run hr
      exact post_of hs₂ ht02 hok hw hc (Runs.pure _)
  · have hfn : ∀ n us, Expr.getAppFnT tmaj ≠ .const n us := fun n us h => hconst ⟨n, us, h⟩
    have hn := TrS_getAppFn_notConst s₂ hfn
    have hr' : (pure major : InLean.CheckCM Expr) s₂ = .ok (m, s') := by
      rw [← hr]
      generalize hx : Expr.getAppFnT tmaj = x at hfn
      cases x with
      | const a b => exact absurd rfl (hfn a b)
      | _ => rfl
    obtain ⟨rfl, rfl⟩ := pure_run hr'
    split
    · rename_i c us' h'; exact absurd h' (hn c us')
    · exact post_of hs₂ ht02 hok hw hc (Runs.pure _)

end Walks

end InLeanProof
