module

public import InLeanProof.IotaViews
public import InLeanProof.WalksWhnfLoop
public import InLeanProof.LeafGuardI

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
    (hlg : LeafGuardSpecI .verified eager env) {d : Nat}
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
  rw [wscopedBC_of_WScoped hokf hwf, closedBV_of_lbb hokf hcf, Bool.true_and, Bool.true_and] at hr
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
    (hlg : LeafGuardSpecI .verified eager env) {d : Nat} {major : Expr}
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
          (fabTailIL_specI ih hpi hlg hs₂ hok₂ hw₂ hc₂ hokf hwf hcf hokm (htm ▸ hw) (htm ▸ hc))
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

theorem mtcEtaIL_specI (ih : KnotSpecI .verified eager env r) (hlg : LeafGuardSpecI .verified eager env) (hv : EnvViewI fe env) {d : Nat} {major : Expr} {T : Name}
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
        rw [wscopedBC_of_WScoped hokf hwf, closedBV_of_lbb hokf hcf, Bool.true_and, Bool.true_and] at hr
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

theorem mtcAndIL_specI (ih : KnotSpecI .verified eager env r) (hpi : ProofIrrelSpecI eager env r)
    (hlg : LeafGuardSpecI .verified eager env) (hv : EnvViewI fe env) {d : Nat} {major : Expr}
    {rl : RecursorRule} {cvj : Lean.ConstantVal} {cnP : Nat} {T : Name} {crl : ConLeche.RecRule}
    {ccvj : ConLeche.ConstantVal} (hrl : crl.ctor = toName rl.ctor) (hcvj : CVRel cvj ccvj)
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hok : OkS s₀ major = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ major))
    (hc : (TrS s₀ major).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ mtcAndIL .verified r fe d major rl cvj cnP T
    ⦃fun m s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' m = true ∧
      Runs ((ConLeche.fueledFns .verified eager env).inferIO d (TrS s₀ major) >>= fun tm =>
        (ConLeche.fueledFns .verified eager env).whnf d tm >>=
          mtcAndCont .verified (ConLeche.fueledFns .verified eager env) env d (TrS s₀ major) crl ccvj
            cnP (toName T)) (TrS s' m) ∧
      ConLeche.Expr.WScoped d (TrS s' m) ∧ (TrS s' m).looseBVarsBounded 0 = true; ⊤⦄ := by
  refine tripleI_iff_run.2 fun m s' hr => ?_
  unfold mtcAndIL at hr
  obtain ⟨tm, s₁, h1, hr⟩ := bind_run hr
  obtain ⟨hs₁, ht₁, hok₁, hrun₁, hw₁, hc₁⟩ := tripleI_iff_run.1 (ih.inferIO hs hok hw hc) tm s₁ h1
  obtain ⟨tmaj, s₂, h2, hr⟩ := bind_run hr
  obtain ⟨hs₂, ht₂, hok₂, hrun₂, hw₂, hc₂⟩ :=
    tripleI_iff_run.1 (ih.whnf hs₁ hok₁ hw₁ hc₁) tmaj s₂ h2
  have ht02 := ht₁.trans ht₂
  rw [Runs.bind_eq _ hrun₁, Runs.bind_eq _ hrun₂]
  unfold mtcAndCont
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
    have hiff : ((T' == T) = true ∧ (appArgs tmaj).length = cnP ∧
        cvj.levelParams.length = ust.length ∧ fe.andRescueSlotsF rl.ctor cnP = true) ↔
        (toName T' = toName T ∧ (TrS s₂ tmaj).getAppArgs.length = cnP ∧
        ccvj.levelParams.length = (ust.map trL).length ∧
        ConLeche.andRescueSlots env crl.ctor cnP = true) := by
      simp only [hrl, ← andRescueSlotsF_V hv, hcvj.2.1, List.length_map, ← hlen, toName_eq_iff,
        beq_iff_eq]
    by_cases hcond : (T' == T) = true ∧ (appArgs tmaj).length = cnP ∧
        cvj.levelParams.length = ust.length ∧ fe.andRescueSlotsF rl.ctor cnP = true
    · have hcond' := hiff.1 hcond
      simp only [hcond, hcond', and_self, ↓reduceIte] at hr ⊢
      obtain ⟨fab, s₃, h3, hr⟩ := bind_run hr
      obtain ⟨rfl, rfl⟩ := pure_run h3
      have hokm := okS_of_tabLe ht02 hok
      have htm := TrS_of_tabLe ht02 hok
      obtain ⟨hp1, hp2, hp3, hp4⟩ := projNodesI_facts s₂ T hokm (htm ▸ hw) (htm ▸ hc) [0, 1]
      have hxs : OkSL s₂ (appArgs tmaj ++ InLean.projNodesI T major [0, 1]) = true :=
        OkSL_append s₂ (OkSL_appArgs s₂ hok₂) hp1
      have hTx : TrSL s₂ (appArgs tmaj ++ InLean.projNodesI T major [0, 1]) =
          (TrS s₂ tmaj).getAppArgs ++
            [.proj (toName T) 0 (TrS s₀ major), .proj (toName T) 1 (TrS s₀ major)] := by
        rw [TrSL_append, TrSL_appArgs, hp2, htm]; rfl
      have hws1 : AllWS d (TrSL s₂ (appArgs tmaj)) := by
        rw [TrSL_appArgs]; exact allWS_getAppArgs hw₂
      have hcl1 : AllClosed (TrSL s₂ (appArgs tmaj)) = true := by
        rw [TrSL_appArgs]; exact allClosed_getAppArgs hc₂
      obtain ⟨hokf, htrf, hwf, hcf⟩ := fab_facts (c := rl.ctor) hust hxs
        (by rw [TrSL_append]; exact AllWS.append hws1 hp3)
        (by rw [TrSL_append]; exact AllClosed_append hcl1 hp4)
      have hr' : fabTailIL r d tmaj
          (mkAppN (.const rl.ctor ust) (appArgs tmaj ++ InLean.projNodesI T major [0, 1]).toArray)
          major s₂ = .ok (m, s') := hr
      obtain ⟨hs', ht', hokm', hrun', hw', hc'⟩ := tripleI_iff_run.1
        (fabTailIL_specI ih hpi hlg hs₂ hok₂ hw₂ hc₂ hokf hwf hcf hokm (htm ▸ hw) (htm ▸ hc))
        m s' hr'
      refine ⟨hs', ht02.trans ht', hokm', ?_, hw', hc'⟩
      rw [htrf, hTx, htm] at hrun'
      rw [hrl]; exact hrun'
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

/-- A stored record's type is closed (`EnvWF`'s). -/
theorem stored_closed (henv : ConLeche.EnvWF env) {n : ConLeche.Name} {ci : ConLeche.ConstantInfo}
    (h : env.find? n = some ci) :
    ci.toConstantVal.type.hasFvar = false ∧ ci.toConstantVal.type.looseBVarsBounded 0 = true := by
  have hw := henv.consts _ (ConLeche.Env.find?_mem h)
  exact ⟨hw.1, hw.2.2.2.1⟩

theorem mtcBodyIL_specI (ih : KnotSpecI .verified eager env r) (hpi : ProofIrrelSpecI eager env r)
    (hlg : LeafGuardSpecI .verified eager env) (henv : ConLeche.EnvWF env) (hv : EnvViewI fe env)
    {d : Nat} {major : Expr} {isK : Bool} {rl : RecursorRule} {cvj : Lean.ConstantVal} {cnP : Nat}
    {T : Name} {cvT : Lean.ConstantVal} {caps : InLean.IndCaps} {crl : ConLeche.RecRule}
    {ccvj ccvT : ConLeche.ConstantVal} (hrl : crl.ctor = toName rl.ctor) (hcvj : CVRel cvj ccvj)
    (hcvT : CVRel cvT ccvT) (hfT : env.find? (toName T) = some (.indInfo ccvT (toCaps caps)))
    {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hok : OkS s₀ major = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ major))
    (hc : (TrS s₀ major).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ mtcBodyIL .verified r fe d major isK rl cvj cnP T cvT caps
    ⦃fun m s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' m = true ∧
      Runs (mtcBodyP .verified (ConLeche.fueledFns .verified eager env) env d (TrS s₀ major) isK
        crl ccvj cnP (toName T) ccvT (toCaps caps)) (TrS s' m) ∧
      ConLeche.Expr.WScoped d (TrS s' m) ∧ (TrS s' m).looseBVarsBounded 0 = true; ⊤⦄ := by
  unfold mtcBodyIL mtcBodyP
  cases isK with
  | true => exact mtcKIL_specI ih hpi hlg hrl hcvj hs hok hw hc
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [hrl, etaRescueOk_CV hcvj hcvT]
    by_cases he : InLean.etaRescueOk rl.ctor cvj cvT caps = true
    · simp only [he, ↓reduceIte]
      obtain ⟨hcl, hlbb⟩ := stored_closed henv hfT
      exact mtcEtaIL_specI ih hlg hv hcvT hcl hlbb hs hok hw hc
    · simp only [he, Bool.false_eq_true, ↓reduceIte]
      have hand : (toName T = ConLeche.andName) ↔ (T == InLean.andName) = true := by
        rw [cl_andName, toName_eq_iff, beq_iff_eq]
      by_cases ha : (T == InLean.andName) = true
      · have hT := hand.2 ha
        simp only [ha, hT, ↓reduceIte]
        rw [← hT]
        exact mtcAndIL_specI ih hpi hlg hv hrl hcvj hs hok hw hc
      · simp only [ha, mt hand.1 ha, Bool.false_eq_true, ↓reduceIte]
        refine tripleI_iff_run.2 fun m s' hr => ?_
        obtain ⟨rfl, rfl⟩ := pure_run hr
        exact post_of hs (TabLe.refl _) hok hw hc (Runs.pure _)

/-- **The stuck-major rescue** (`majorToCtorC_spec`'s twin). -/
theorem majorToCtorI_specI (ih : KnotSpecI .verified eager env r) (hpi : ProofIrrelSpecI eager env r)
    (hlg : LeafGuardSpecI .verified eager env) (henv : ConLeche.EnvWF env) (hv : EnvViewI fe env)
    {d : Nat} {recName : ConLeche.Name} {isK : Bool} {fire : InLean.RecRuleFire}
    {rules : List RecursorRule} {crules : List ConLeche.RecRule}
    (hrules : LRel (RuleRel fire) rules crules)
    {i : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i)) (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.majorToCtorI .verified r fe d isK rules i
    ⦃fun m s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' m = true ∧
      Runs (ConLeche.majorToCtor .verified (ConLeche.fueledFns .verified eager env) env d recName
        isK crules (TrS s₀ i)) (TrS s' m) ∧
      ConLeche.Expr.WScoped d (TrS s' m) ∧ (TrS s' m).looseBVarsBounded 0 = true; ⊤⦄ := by
  rw [majorToCtorI_eq]
  have hpost : ∀ {P : ConLeche.FueledM ConLeche.Expr}, P = pure (TrS s₀ i) →
      ⦃fun s => s = s₀⦄ (pure i : InLean.CheckCM Expr)
      ⦃fun m s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' m = true ∧
        Runs P (TrS s' m) ∧
        ConLeche.Expr.WScoped d (TrS s' m) ∧ (TrS s' m).looseBVarsBounded 0 = true; ⊤⦄ := by
    intro P hP
    refine tripleI_iff_run.2 fun m s' hr => ?_
    obtain ⟨rfl, rfl⟩ := pure_run hr
    exact post_of hs (TabLe.refl _) hok hw hc (by rw [hP]; exact Runs.pure _)
  rw [isCtorAppC_TrS hv s₀]
  by_cases hct : ConLeche.isCtorApp env (TrS s₀ i) = true
  · simp only [hct, ↓reduceIte]
    exact hpost (mtc_isCtor hct)
  · have hct' : ConLeche.isCtorApp env (TrS s₀ i) = false := by simpa using hct
    simp only [hct', Bool.false_eq_true, ↓reduceIte]
    cases hrules with
    | nil => exact hpost (mtc_notSingle hct' (fun _ h => nomatch h))
    | @cons rl crl rules' crules' hrl hrest =>
      cases hrest with
      | cons _ _ => exact hpost (mtc_notSingle hct' (fun _ h => by simp at h))
      | nil =>
        dsimp only
        cases hcv : fe.ctorView? rl.ctor with
        | none =>
          dsimp only
          exact hpost (mtc_notCtor hct' rfl (fun cvj nP nF h => by
            rw [hrl.1] at h; exact hv.ctorNone _ hcv _ _ _ h))
        | some p =>
          obtain ⟨cvj, cnP, nF⟩ := p
          obtain ⟨ccvj, hcvj, hfj⟩ := hv.ctor _ cvj cnP nF hcv
          rw [← hrl.1] at hfj
          dsimp only
          have hty : ccvj.type = TrS s₀ cvj.type := (hcvj.2.2.trS s₀).symm
          have hhead : (ccvj.type.piResult).getAppFn =
              TrS s₀ (EO.stripTop ((InLean.piResult cvj.type).getAppFnT)) := by
            rw [stripTop_getAppFnT, TrS_getAppFnT, TrS_piResult, hty]
          generalize hx : EO.stripTop ((InLean.piResult cvj.type).getAppFnT) = x at hhead
          cases x with
          | const T lus =>
            dsimp only
            rw [TrS_const] at hhead
            cases hind : fe.indView? T with
            | none =>
              dsimp only
              exact hpost (mtc_notInd hct' rfl hfj hhead (fun cvT caps h =>
                hv.indNone T hind cvT caps h))
            | some q =>
              obtain ⟨cvT, caps⟩ := q
              obtain ⟨ccvT, hcvT, hfT⟩ := hv.ind T cvT caps hind
              dsimp only
              rw [mtc_body hct' rfl hfj hhead hfT]
              exact mtcBodyIL_specI ih hpi hlg henv hv hrl.1 hcvj hcvT hfT hs hok hw hc
          | fvar id =>
            have hnc : ∀ T lus, (ccvj.type.piResult).getAppFn ≠ .const T lus := by
              intro T lus h
              rw [hhead] at h
              simp only [TrS, trE] at h
              cases hf : FVarTable.trans (tableOf s₀) id with
              | none => simp [hf] at h
              | some c =>
                obtain ⟨d', ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf
                simp [hf] at h
            exact hpost (mtc_notConst hct' rfl hfj hnc)
          | mdata _ y => exact (stripTop_ne_mdata hx).elim
          | _ =>
            exact hpost (mtc_notConst hct' rfl hfj (fun T lus h => by
              rw [hhead] at h; simp [TrS, trE] at h))

/-- A `String` literal through the translation. -/
theorem isStrLitI_TrS (s : InLean.CState) : ∀ e : Expr,
    InLean.Expr.isStrLitI e = ConLeche.Expr.isStrLit (TrS s e)
  | .mdata _ e => by rw [InLean.Expr.isStrLitI, TrS_mdata, isStrLitI_TrS s e]
  | .lit (.strVal _) => rfl
  | .lit (.natVal _) => rfl
  | .fvar id => by
    simp only [InLean.Expr.isStrLitI, TrS, trE]
    cases hf : FVarTable.trans (tableOf s) id with
    | none => rfl
    | some c => obtain ⟨d, ty, rfl⟩ := FVarTable.trans_fvarsOnly _ id c hf; rfl
  | .bvar _ | .mvar _ | .sort _ | .const .. | .app .. | .lam .. | .forallE .. | .letE ..
  | .proj .. => rfl

/-- The preparation off K past the first rescue. -/
theorem prepTailI_specI (ih : KnotSpecI .verified eager env r)
    (hpi : ProofIrrelSpecI eager env r) (hlg : LeafGuardSpecI .verified eager env)
    (henv : ConLeche.EnvWF env) (hv : EnvViewI fe env) (hdom : EnvDomI fe env)
    {d : Nat} {recName : ConLeche.Name} {fire : InLean.RecRuleFire}
    {rules : List RecursorRule} {crules : List ConLeche.RecRule}
    (hrules : LRel (RuleRel fire) rules crules)
    {me : Expr} {s₁ : InLean.CState} (hs₁ : CSOKI .verified eager env s₁) (hok₁ : OkS s₁ me = true)
    (hw₁ : ConLeche.Expr.WScoped d (TrS s₁ me)) (hc₁ : (TrS s₁ me).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₁⦄ (if InLean.isCtorAppC fe me = true then pure me else do
        let major₀ ← r.whnf d me
        let major₁ ← InLean.litMajorToCtorI r fe d major₀
        InLean.majorToCtorI .verified r fe d false rules major₁ : InLean.CheckCM Expr)
    ⦃fun m s' => CSOKI .verified eager env s' ∧ TabLe s₁ s' ∧ OkS s' m = true ∧
      Runs (if ConLeche.isCtorApp env (TrS s₁ me) = true then pure (TrS s₁ me) else do
        let major₀ ← (ConLeche.fueledFns .verified eager env).whnf d (TrS s₁ me)
        let major₁ ← ConLeche.litMajorToCtor (ConLeche.fueledFns .verified eager env) env d major₀
        ConLeche.majorToCtor .verified (ConLeche.fueledFns .verified eager env) env d recName false
          crules major₁) (TrS s' m) ∧
      ConLeche.Expr.WScoped d (TrS s' m) ∧ (TrS s' m).looseBVarsBounded 0 = true; ⊤⦄ := by
  refine tripleI_iff_run.2 fun m s' hr => ?_
  rw [isCtorAppC_TrS hv s₁] at hr
  by_cases hct : ConLeche.isCtorApp env (TrS s₁ me) = true
  · simp only [hct, ↓reduceIte] at hr ⊢
    obtain ⟨rfl, rfl⟩ := pure_run hr
    exact ⟨hs₁, TabLe.refl _, hok₁, Runs.pure _, hw₁, hc₁⟩
  · simp only [hct, Bool.false_eq_true, ↓reduceIte] at hr ⊢
    obtain ⟨m₀, s₂, h2, hr⟩ := bind_run hr
    obtain ⟨hs₂, ht₂, hok₂, hrun₂, hw₂, hc₂⟩ :=
      tripleI_iff_run.1 (ih.whnf hs₁ hok₁ hw₁ hc₁) m₀ s₂ h2
    rw [Runs.bind_eq _ hrun₂]
    obtain ⟨m₁, s₃, h3, hr⟩ := bind_run hr
    obtain ⟨hs₃, ht₃, hok₃, hrun₃, hw₃, hc₃⟩ :=
      tripleI_iff_run.1 (litMajorToCtorI_specI ih hdom hs₂ hok₂ hw₂ hc₂) m₁ s₃ h3
    rw [Runs.bind_eq _ hrun₃]
    obtain ⟨hs₄, ht₄, hok₄, hrun₄, hw₄, hc₄⟩ := tripleI_iff_run.1
      (majorToCtorI_specI (recName := recName) ih hpi hlg henv hv hrules hs₃ hok₃ hw₃ hc₃) m s' hr
    exact ⟨hs₄, ht₂.trans (ht₃.trans ht₄), hok₄, hrun₄, hw₄, hc₄⟩

/-- **The major's preparation** (`prepareMajorC_spec`'s twin). -/
theorem prepareMajorI_specI (ih : KnotSpecI .verified eager env r)
    (hpi : ProofIrrelSpecI eager env r) (hlg : LeafGuardSpecI .verified eager env)
    (henv : ConLeche.EnvWF env) (hv : EnvViewI fe env) (hdom : EnvDomI fe env)
    {d : Nat} {recName : ConLeche.Name} {isK : Bool} {fire : InLean.RecRuleFire}
    {rules : List RecursorRule} {crules : List ConLeche.RecRule}
    (hrules : LRel (RuleRel fire) rules crules)
    {i : Expr} {s₀ : InLean.CState} (hs : CSOKI .verified eager env s₀) (hok : OkS s₀ i = true)
    (hw : ConLeche.Expr.WScoped d (TrS s₀ i)) (hc : (TrS s₀ i).looseBVarsBounded 0 = true) :
    ⦃fun s => s = s₀⦄ InLean.prepareMajorI .verified r fe d isK rules i
    ⦃fun m s' => CSOKI .verified eager env s' ∧ TabLe s₀ s' ∧ OkS s' m = true ∧
      Runs (ConLeche.prepareMajor .verified (ConLeche.fueledFns .verified eager env) env d recName
        isK crules (TrS s₀ i)) (TrS s' m) ∧
      ConLeche.Expr.WScoped d (TrS s' m) ∧ (TrS s' m).looseBVarsBounded 0 = true; ⊤⦄ := by
  refine tripleI_iff_run.2 fun m s' hr => ?_
  unfold InLean.prepareMajorI at hr
  unfold ConLeche.prepareMajor
  cases isK with
  | true =>
    simp only [↓reduceIte] at hr ⊢
    obtain ⟨mk, s₁, h1, hr⟩ := bind_run hr
    obtain ⟨hs₁, ht₁, hok₁, hrun₁, hw₁, hc₁⟩ := tripleI_iff_run.1
      (majorToCtorI_specI (recName := recName) ih hpi hlg henv hv hrules hs hok hw hc) mk s₁ h1
    rw [Runs.bind_eq _ hrun₁]
    rw [isCtorAppC_TrS hv s₁] at hr
    by_cases hct : ConLeche.isCtorApp env (TrS s₁ mk) = true
    · simp only [hct, ↓reduceIte] at hr ⊢
      obtain ⟨hs₂, ht₂, hok₂, hrun₂, hw₂, hc₂⟩ := tripleI_iff_run.1
        (litMajorToCtorI_specI ih hdom hs₁ hok₁ hw₁ hc₁) m s' hr
      exact ⟨hs₂, ht₁.trans ht₂, hok₂, hrun₂, hw₂, hc₂⟩
    · simp only [hct, Bool.false_eq_true, ↓reduceIte] at hr ⊢
      obtain ⟨rfl, rfl⟩ := pure_run hr
      exact ⟨hs₁, ht₁, hok₁, Runs.pure _, hw₁, hc₁⟩
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr ⊢
    rw [isStrLitI_TrS s₀] at hr
    by_cases hsl : (TrS s₀ i).isStrLit = true
    · simp only [hsl, ↓reduceIte] at hr ⊢
      obtain ⟨me, s₁, h1, hr⟩ := bind_run hr
      obtain ⟨rfl, rfl⟩ := pure_run h1
      rw [Runs.pure_bind_eq]
      exact tripleI_iff_run.1
        (prepTailI_specI (recName := recName) ih hpi hlg henv hv hdom hrules hs hok hw hc) m s' hr
    · simp only [hsl, Bool.false_eq_true, ↓reduceIte] at hr ⊢
      obtain ⟨me, s₁, h1, hr⟩ := bind_run hr
      obtain ⟨hs₁, ht₁, hok₁, hrun₁, hw₁, hc₁⟩ := tripleI_iff_run.1
        (majorToCtorI_specI (recName := recName) ih hpi hlg henv hv hrules hs hok hw hc) me s₁ h1
      rw [Runs.bind_eq _ hrun₁]
      obtain ⟨hs₂, ht₂, hok₂, hrun₂, hw₂, hc₂⟩ := tripleI_iff_run.1
        (prepTailI_specI (recName := recName) ih hpi hlg henv hv hdom hrules hs₁ hok₁ hw₁ hc₁) m s' hr
      exact ⟨hs₂, ht₁.trans ht₂, hok₂, hrun₂, hw₂, hc₂⟩

/-! ## The case-3 certificate block -/

/-- The comparand levels (the certificate's first step). -/
@[expose] def cmpLvlsIL (rv : RecursorVal) (us : List Level) (cvj : Lean.ConstantVal)
    (fire : InLean.RecRuleFire) : InLean.CheckCM (List Level) :=
  match fire with
  | .nested lvls _ => InLean.substLevelTreesM rv.levelParams us lvls
  | .plain => InLean.substLevelTreesM rv.levelParams us (cvj.levelParams.map Level.param)
  | .levels lvls => InLean.substLevelTreesM rv.levelParams us lvls

/-- The comparand arguments. -/
@[expose] def cmpArgsIL (rv : RecursorVal) (us : List Level) (args : List Expr) (cnP : Nat)
    (fire : InLean.RecRuleFire) : InLean.CheckCM (List Expr) :=
  match fire with
  | .nested _ pins =>
    match InLean.pinArgsI rv.levelParams us (args.take (rulePrefixOf rv)) pins with
    | some ps => pure ps
    | none => throw (.internal "universe level too deep")
  | .plain => pure (args.take cnP)
  | .levels _ => pure (args.take cnP)

/-- The certificate past the comparands. -/
@[expose] def certRestIL (r : InLean.CoreFnsI) (fe : InLean.FEnv) (depth : Nat) (rv : RecursorVal)
    (args : List Expr) (cj : Name) (usj : List Level) (cnP : Nat) (margs cmpArgs : List Expr) :
    InLean.CheckCM Bool := do
  if ← defEqListI r depth (margs.take cnP) cmpArgs then do
    let tyCtor ← constTyAtM fe cj usj
    if ← iotaCertsFullI r depth tyCtor margs then
      iotaIndexOkI r depth (majorIdxOf rv) (rulePrefixOf rv) cnP tyCtor margs
        ((args.take (majorIdxOf rv)).drop (rulePrefixOf rv))
    else pure false
  else pure false

/-- The case-3 certificate block of `iotaRecI` (the argument of `certAtI`). -/
@[expose] def iotaCertIL (r : InLean.CoreFnsI) (fe : InLean.FEnv) (depth : Nat) (rv : RecursorVal)
    (isQuot : Bool) (us : List Level) (args : List Expr) (cj : Name) (usj : List Level)
    (cvj : Lean.ConstantVal) (cnP : Nat) (margs : List Expr) : InLean.CheckCM Bool := do
  let cmpLvls ← cmpLvlsIL rv us cvj (recFireAt rv isQuot)
  if ← iotaCase3I r.whnf fe rv.k cvj cmpLvls then do
    if ← liftFueled "level comparison" (← isEquivListLM usj cmpLvls) then do
      let cmpArgs ← cmpArgsIL rv us args cnP (recFireAt rv isQuot)
      certRestIL r fe depth rv args cj usj cnP margs cmpArgs
    else pure false
  else pure true

theorem okLv_param (n : Name) : okLv (Level.param n) = true := by
  simp [okLv, okL, depthS]

theorem cmpLvlsIL_run {rv : RecursorVal} {us : List Level} {cvj : Lean.ConstantVal}
    {ccvj : ConLeche.ConstantVal} (hcvj : CVRel cvj ccvj) {fire : InLean.RecRuleFire}
    {cfire : ConLeche.RecRuleFire} (hfire : FireRel fire cfire) (hus : us.all okLv = true)
    {cnP : Nat} {cargs : List ConLeche.Expr} {rP : Nat}
    {mode : ConLeche.CheckMode} {s₀ s₁ : InLean.CState} (hs : CSOKI mode eager env s₀)
    {ls : List Level} (h : cmpLvlsIL rv us cvj fire s₀ = .ok (ls, s₁)) :
    CSOKI mode eager env s₁ ∧ TabLe s₀ s₁ ∧ ls.all okLv = true ∧
      ls.map trL = (fireCmp cfire cnP (rv.levelParams.map toName) (us.map trL) ccvj.levelParams
        cargs rP).1 := by
  unfold cmpLvlsIL at h
  cases fire with
  | plain =>
    cases cfire with
    | plain =>
      have hp : (cvj.levelParams.map Level.param).all okLv = true := by
        simp [List.all_map, okLv_param]
      obtain ⟨h1, h2, h3, h4⟩ := tripleI_iff_run.1 (substLevelTreesM_specI hs hus hp) ls s₁ h
      refine ⟨h1, h2, h3, ?_⟩
      rw [h4, fireCmp_plain, hcvj.2.1]
      simp [List.map_map, Function.comp_def, trL]
    | _ => exact hfire.elim
  | nested lvls pins =>
    cases cfire with
    | nested clvls cpins =>
      obtain ⟨hl, rfl, -⟩ := hfire
      obtain ⟨h1, h2, h3, h4⟩ := tripleI_iff_run.1 (substLevelTreesM_specI hs hus hl) ls s₁ h
      exact ⟨h1, h2, h3, by rw [h4, fireCmp_nested]⟩
    | _ => exact hfire.elim
  | levels lvls =>
    cases cfire with
    | levels clvls =>
      obtain ⟨hl, rfl⟩ := hfire
      obtain ⟨h1, h2, h3, h4⟩ := tripleI_iff_run.1 (substLevelTreesM_specI hs hus hl) ls s₁ h
      exact ⟨h1, h2, h3, by rw [h4, fireCmp_levels]⟩
    | _ => exact hfire.elim

theorem cmpArgsIL_run {rv : RecursorVal} {us : List Level} (hus : us.all okLv = true)
    {args : List Expr} {cnP d : Nat} {fire : InLean.RecRuleFire} {cfire : ConLeche.RecRuleFire}
    (hfire : FireRel fire cfire)
    (hpins : ∀ lvls pins, cfire = .nested lvls pins →
      ∀ p ∈ pins, p.hasFvar = false ∧ p.looseBVarsBounded (rulePrefixOf rv) = true)
    {cvjLps : List ConLeche.Name} {s₀ s₁ : InLean.CState} (hargs : OkSL s₀ args = true)
    (hwa : AllWS d (TrSL s₀ args)) (hca : AllClosed (TrSL s₀ args) = true)
    (hlen : rulePrefixOf rv ≤ args.length)
    {ps : List Expr} (h : cmpArgsIL rv us args cnP fire s₀ = .ok (ps, s₁)) :
    s₁ = s₀ ∧ OkSL s₀ ps = true ∧
      TrSL s₀ ps = (fireCmp cfire cnP (rv.levelParams.map toName) (us.map trL) cvjLps
        (TrSL s₀ args) (rulePrefixOf rv)).2 ∧
      AllWS d (TrSL s₀ ps) ∧ AllClosed (TrSL s₀ ps) = true := by
  unfold cmpArgsIL at h
  have hplain : (pure (args.take cnP) : InLean.CheckCM (List Expr)) s₀ = .ok (ps, s₁) →
      s₁ = s₀ ∧ OkSL s₀ ps = true ∧ TrSL s₀ ps = (TrSL s₀ args).take cnP ∧
      AllWS d (TrSL s₀ ps) ∧ AllClosed (TrSL s₀ ps) = true := by
    intro h
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨rfl, OkSL_take s₀ hargs cnP, TrSL_take s₀ args cnP, ?_, ?_⟩
    · rw [TrSL_take]; exact hwa.take cnP
    · rw [TrSL_take]; exact AllClosed_take hca cnP
  cases fire with
  | plain =>
    cases cfire with
    | plain => obtain ⟨h1, h2, h3, h4, h5⟩ := hplain h; exact ⟨h1, h2, by rw [h3]; rfl, h4, h5⟩
    | _ => exact hfire.elim
  | levels lvls =>
    cases cfire with
    | levels clvls =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hplain h; exact ⟨h1, h2, by rw [h3]; rfl, h4, h5⟩
    | _ => exact hfire.elim
  | nested lvls pins =>
    cases cfire with
    | nested clvls cpins =>
      obtain ⟨-, -, hst⟩ := hfire
      have hpc := hpins clvls cpins rfl
      dsimp only at h
      have hargs' := OkSL_take s₀ hargs (rulePrefixOf rv)
      have hca' : AllClosed (TrSL s₀ (args.take (rulePrefixOf rv))) = true := by
        rw [TrSL_take]; exact AllClosed_take hca _
      cases hp : InLean.pinArgsI rv.levelParams us (args.take (rulePrefixOf rv)) pins with
      | none =>
        rw [hp] at h
        simp [throw, throwThe, MonadExceptOf.throw, StateT.lift, Functor.map, Except.map] at h
      | some qs =>
        rw [hp] at h
        obtain ⟨rfl, rfl⟩ := pure_run h
        obtain ⟨hok, htr⟩ := pinArgsI_TrS hus hargs' hca' hst hp
        have hl : (args.take (rulePrefixOf rv)).length = rulePrefixOf rv := by
          simp [List.length_take, hlen]
        rw [hl, TrSL_take] at htr
        refine ⟨rfl, hok, by rw [htr, fireCmp_nested], ?_, ?_⟩
        · rw [htr]
          exact allWS_pinInst _ _ _ (fun p hp => (hpc p hp).1) (hwa.take _)
        · rw [htr]
          simp only [AllClosed, List.all_eq_true, List.mem_map]
          rintro _ ⟨p, hp, rfl⟩
          have hcl := AllClosed_take hca (rulePrefixOf rv)
          simp only [AllClosed, List.all_eq_true] at hcl
          have hlt : ((TrSL s₀ args).take (rulePrefixOf rv)).length = rulePrefixOf rv := by
            simp [TrSL_length, List.length_take, hlen]
          unfold pinInst
          have := ConLeche.instSpine_closed (args := (TrSL s₀ args).take (rulePrefixOf rv))
            (e := p.instantiateLevelParams (rv.levelParams.map toName) (us.map trL)) hcl
            (by rw [hlt, ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact (hpc p hp).2)
          rw [hlt] at this
          exact this
    | _ => exact hfire.elim

/-- The pure certificate past the comparands (`iotaCertP`'s tail). -/
@[expose] def certRestP (F : ConLeche.CoreFns ConLeche.FueledM) (env : ConLeche.Env) (depth : Nat)
    (mI rP cnP : Nat) (args : List ConLeche.Expr) (usj : List ConLeche.Level)
    (cvj : ConLeche.ConstantVal) (margs cmp2 : List ConLeche.Expr) : ConLeche.FueledM Bool := do
  if ← ConLeche.defEqList F env depth (margs.take cnP) cmp2 then
    if ← ConLeche.iotaCertsFull F env depth
        (cvj.type.instantiateLevelParams cvj.levelParams usj)
        margs then
      ConLeche.iotaIndexOk F env depth mI rP cnP
        (cvj.type.instantiateLevelParams cvj.levelParams usj)
        margs ((args.take mI).drop rP)
    else pure false
  else pure false

theorem certRestIL_run (ih : KnotSpecI .verified eager env r) (henv : ConLeche.EnvWF env)
    (hfe : EnvRelI fe env) {d : Nat} {rv : RecursorVal} {args : List Expr} {cj : Name}
    {usj : List Level} (husj : usj.all okLv = true) {cnP nF : Nat} {ccvj : ConLeche.ConstantVal}
    (hfj : env.find? (toName cj) = some (.ctorInfo ccvj cnP nF))
    {margs cmpArgs : List Expr} {s₀ s₁ : InLean.CState} (hs : CSOKI .verified eager env s₀)
    (hargs : OkSL s₀ args = true) (hwa : AllWS d (TrSL s₀ args))
    (hca : AllClosed (TrSL s₀ args) = true)
    (hm : OkSL s₀ margs = true) (hwm : AllWS d (TrSL s₀ margs))
    (hcm : AllClosed (TrSL s₀ margs) = true)
    (hc : OkSL s₀ cmpArgs = true) (hwc : AllWS d (TrSL s₀ cmpArgs))
    (hcc : AllClosed (TrSL s₀ cmpArgs) = true) {b : Bool}
    (h : certRestIL r fe d rv args cj usj cnP margs cmpArgs s₀ = .ok (b, s₁)) :
    CSOKI .verified eager env s₁ ∧ TabLe s₀ s₁ ∧
      Runs (certRestP (ConLeche.fueledFns .verified eager env) env d (majorIdxOf rv)
        (rulePrefixOf rv) cnP (TrSL s₀ args) (usj.map trL) ccvj (TrSL s₀ margs)
        (TrSL s₀ cmpArgs)) b := by
  unfold certRestIL at h
  unfold certRestP
  obtain ⟨ok, s₂, h2, h⟩ := bind_run h
  obtain ⟨hs₂, ht₂, hrun₂⟩ := tripleI_iff_run.1
    (defEqListI_spec ih hs (OkSL_take s₀ hm cnP) hc (by rw [TrSL_take]; exact hwm.take cnP) hwc
      (by rw [TrSL_take]; exact AllClosed_take hcm cnP) hcc) ok s₂ h2
  rw [TrSL_take] at hrun₂
  rw [Runs.bind_eq _ hrun₂]
  cases ok with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs₂, ht₂, Runs.pure _⟩
  | true =>
    simp only [↓reduceIte] at h ⊢
    obtain ⟨ty, s₃, h3, h⟩ := bind_run h
    obtain ⟨hs₃, ht₃, hokty, htrty⟩ := tripleI_iff_run.1
      (constTyAtM_specI hfe hs₂ cj husj) ty s₃ h3
    obtain ⟨hcl, hlbb⟩ := stored_closed henv hfj
    have hty : TrS s₃ ty = ccvj.type.instantiateLevelParams ccvj.levelParams (usj.map trL) := by
      rw [htrty]; simp only [constTyOf, hfj, ConLeche.ConstantInfo.toConstantVal]
    have hwty : ConLeche.Expr.WScoped d (TrS s₃ ty) := by
      rw [hty]; exact ConLeche.Expr.WScoped.of_not_hasFvar
        (by rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hcl)
    have hcty : (TrS s₃ ty).looseBVarsBounded 0 = true := by
      rw [hty, ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]; exact hlbb
    have ht03 := ht₂.trans ht₃
    have hm₃ := okSL_of_tabLe ht03 hm
    have htm := TrSL_of_tabLe ht03 hm
    obtain ⟨ok2, s₄, h4, h⟩ := bind_run h
    obtain ⟨hs₄, ht₄, hrun₄⟩ := tripleI_iff_run.1
      (iotaCertsFullI_specI ih hs₃ hokty hwty hcty hm₃ (htm ▸ hwm) (htm ▸ hcm)) ok2 s₄ h4
    rw [hty, htm] at hrun₄
    rw [Runs.bind_eq _ hrun₄]
    cases ok2 with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl⟩ := pure_run h
      exact ⟨hs₄, ht03.trans ht₄, Runs.pure _⟩
    | true =>
      simp only [↓reduceIte] at h ⊢
      have hokty₄ := okS_of_tabLe ht₄ hokty
      have htty₄ := TrS_of_tabLe ht₄ hokty
      have ht04 := ht03.trans ht₄
      have hm₄ := okSL_of_tabLe ht04 hm
      have htm₄ := TrSL_of_tabLe ht04 hm
      have hidx : OkSL s₀ ((args.take (majorIdxOf rv)).drop (rulePrefixOf rv)) = true :=
        OkSL_drop s₀ (OkSL_take s₀ hargs _) _
      have hidx₄ := okSL_of_tabLe ht04 hidx
      have htidx : TrSL s₄ ((args.take (majorIdxOf rv)).drop (rulePrefixOf rv)) =
          ((TrSL s₀ args).take (majorIdxOf rv)).drop (rulePrefixOf rv) := by
        rw [TrSL_of_tabLe ht04 hidx, TrSL_drop, TrSL_take]
      obtain ⟨hs₅, ht₅, hrun₅⟩ := tripleI_iff_run.1
        (iotaIndexOkI_specI ih hs₄ hokty₄ (htty₄ ▸ hwty) (htty₄ ▸ hcty) hm₄ (htm₄ ▸ hwm)
          (htm₄ ▸ hcm) hidx₄ (by rw [htidx]; exact (hwa.take _).drop _)
          (by rw [htidx]; exact AllClosed_drop (AllClosed_take hca _) _)) b s₁ h
      rw [htty₄, htm₄, htidx, hty] at hrun₅
      exact ⟨hs₅, ht04.trans ht₅, hrun₅⟩

end Walks

end InLeanProof
