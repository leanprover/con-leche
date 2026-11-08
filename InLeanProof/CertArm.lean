module

public import InLeanProof.DeclPins
/- `ConstantInfo.name`/`levelParams`/`type` are read as projections of `toConstantVal`. -/
import all Lean.Declaration
/- `FEnv.push` (core's private add, behind `InLean/Push.lean`) is read to find the pushed definition. -/
import all InLean.Push
/- `Expr.updateApp!` & co. are read to see the strip walk's rebuilt nodes. -/
import all Lean.Expr

/-!
# CertArm: the certified `Nat` operations' arm (task #451, lane CertArm)

InLean's `checkDefnC` at a certified operation's name (`InLean/CheckerC.lean`:
`natOpGuard`, `natOpStoredOk`, `natVars`, `certifyNatEqs`; `checkDivModPin`)
against master's `.defnDecl` arm of `checkDeclKind`
(`ConLeche/Kernel/CheckDecl.lean`: `natOpGuard`, `natOpStoredOk`,
`certifyNatEqs` over `natOpEquations 0`; `checkDivModPin`).

* **The guards at the pushed environment**: `natOpStoredOk_tr`,
  `natOpGuard_tr`, `divModEnvGuard_tr` (`EO.stripMData` keeps the reading,
  `erase_stripMData`).  InLean's `natOpGuard` reads the `Nat` names stored
  (`natLitStoredF`), master's their kinds and shapes (`natLitSupported`): the
  shapes are `EnvWF.shapes`', the kinds are `NatKinds`, which no premise of
  the declaration step gives (master's model reads it off `BasisPinnedTT`), so
  it is a premise here.
* **The equations**: `natOpEquations` over the two interned variables, with
  the operation's self-references substituted (`substConst0`), translate to
  master's over `fvar 0`/`fvar 1` (`natOpEqs_tr`); the defeq loop at depth 2
  (`certifyNatEqs_sim`).
* **The structural operations' arm**: `checkDefnC_struct_sim`.
* **The WF operations** (`checkDivModPin`): the pin variants InLean decodes,
  as master's list (`trPinSet`, `loadedPins`); the arm itself is named
  (`DivModArmSimI`), and `checkDeclKindC_sim_nk`/`checkDecl_sim_nk` are
  `checkDeclKindC_sim_full`/`checkDecl_sim_full` from it and `NatKinds L`.
-/
set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## `stripMData` keeps the reading -/

section strip
/- The strip walk's memo compares nodes exactly, as `InLean/ExprOps.lean` elaborates it. -/
attribute [local instance 2000] instBEqExprExact
local instance : LawfulBEq Expr := instBEqExprExact_lawful
local instance : LawfulHashable (Expr × Nat) := ⟨fun _ _ h => by rw [eq_of_beq h]⟩

/-- The strip memo's invariant: every entry erases as its key. -/
def StripMemoInv (memo : EO.Memo) : Prop :=
  ∀ (k : Expr × Nat) (r : Expr), memo[k]? = some r → erase r = erase k.1

theorem StripMemoInv.insert {memo : EO.Memo} (hm : StripMemoInv memo) {e r : Expr}
    (he : erase r = erase e) : StripMemoInv (memo.insert (e, 0) r) := by
  intro k r' hl
  rw [Std.HashMap.getElem?_insert] at hl
  split at hl
  · rename_i heq
    have : (e, 0) = k := eq_of_beq heq
    subst this
    simp only [Option.some.injEq] at hl
    exact hl ▸ he
  · exact hm k r' hl

theorem stripMDataGo_spec : ∀ (e : Expr) (memo : EO.Memo), StripMemoInv memo →
    erase (EO.stripMDataGo e memo).1 = erase e ∧ StripMemoInv (EO.stripMDataGo e memo).2 := by
  intro e
  induction e with
  | mdata m x ih => intro memo hm; rw [EO.stripMDataGo]; simpa [erase] using ih memo hm
  | app f a ihf iha =>
    intro memo hm
    rw [EO.stripMDataGo, EO.withMemo]
    cases hl : memo[(Expr.app f a, 0)]? with
    | some r => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := ihf memo hm
      obtain ⟨h3, h4⟩ := iha _ h2
      have hv : erase ((Expr.app f a).updateApp! (EO.stripMDataGo f memo).1
          (EO.stripMDataGo a (EO.stripMDataGo f memo).2).1) = erase (.app f a) := by
        simp only [Expr.updateApp!, erase, h1, h3]
      exact ⟨hv, h4.insert hv⟩
  | lam n t b bi iht ihb =>
    intro memo hm
    rw [EO.stripMDataGo, EO.withMemo]
    cases hl : memo[(Expr.lam n t b bi, 0)]? with
    | some r => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : erase ((Expr.lam n t b bi).updateLambdaE! (EO.stripMDataGo t memo).1
          (EO.stripMDataGo b (EO.stripMDataGo t memo).2).1) = erase (.lam n t b bi) := by
        simp only [Expr.updateLambdaE!, Expr.updateLambda!, mkLambda, erase, h1, h3]
      exact ⟨hv, h4.insert hv⟩
  | forallE n t b bi iht ihb =>
    intro memo hm
    rw [EO.stripMDataGo, EO.withMemo]
    cases hl : memo[(Expr.forallE n t b bi, 0)]? with
    | some r => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihb _ h2
      have hv : erase ((Expr.forallE n t b bi).updateForallE! (EO.stripMDataGo t memo).1
          (EO.stripMDataGo b (EO.stripMDataGo t memo).2).1) = erase (.forallE n t b bi) := by
        simp only [Expr.updateForallE!, Expr.updateForall!, mkForall, erase, h1, h3]
      exact ⟨hv, h4.insert hv⟩
  | letE n t v b nd iht ihv ihb =>
    intro memo hm
    rw [EO.stripMDataGo, EO.withMemo]
    cases hl : memo[(Expr.letE n t v b nd, 0)]? with
    | some r => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := iht memo hm
      obtain ⟨h3, h4⟩ := ihv _ h2
      obtain ⟨h5, h6⟩ := ihb _ h4
      have hv : erase ((Expr.letE n t v b nd).updateLetE! (EO.stripMDataGo t memo).1
          (EO.stripMDataGo v (EO.stripMDataGo t memo).2).1
          (EO.stripMDataGo b (EO.stripMDataGo v (EO.stripMDataGo t memo).2).2).1) =
          erase (.letE n t v b nd) := by
        simp only [Expr.updateLetE!, Expr.updateLet!, erase, h1, h3, h5]
      exact ⟨hv, h6.insert hv⟩
  | proj s i x ih =>
    intro memo hm
    rw [EO.stripMDataGo, EO.withMemo]
    cases hl : memo[(Expr.proj s i x, 0)]? with
    | some r => exact ⟨hm _ _ hl, hm⟩
    | none =>
      obtain ⟨h1, h2⟩ := ih memo hm
      have hv : erase ((Expr.proj s i x).updateProj! (EO.stripMDataGo x memo).1) =
          erase (.proj s i x) := by
        simp only [Expr.updateProj!, mkProj, erase, h1]
      exact ⟨hv, h2.insert hv⟩
  | bvar | fvar | mvar | sort | const | lit => intro memo hm; unfold EO.stripMDataGo; exact ⟨rfl, hm⟩

theorem erase_stripMData (e : Expr) : erase (EO.stripMData e) = erase e :=
  (stripMDataGo_spec e _ (fun k r h => by simp [EO.freshFor] at h)).1

end strip

theorem toExpr_stripMData (fv : FVarId → Option ConLeche.Expr) (e : Expr) :
    toExpr fv (EO.stripMData e) = toExpr fv e := by
  rw [← toExpr_erase fv (EO.stripMData e), erase_stripMData, toExpr_erase]

theorem toExprC_stripMData (e : Expr) : toExprC (EO.stripMData e) = toExprC e :=
  toExpr_stripMData _ e

theorem toExprC_stripTop (e : Expr) : toExprC (EO.stripTop e) = toExprC e :=
  toExpr_stripTop _ e

/-! ## The certified operations' guards -/

/-- `tyIs` against a closed shape: the reading is the shape's. -/
theorem tyIs_tr {t shape : Expr} {c : ConLeche.Expr} (ht : toExprC t = some c)
    (hs : okC shape = true) (h : InLean.tyIs t shape = true) : c = trC shape := by
  have := toExpr_of_clEq (fun _ => none) h
  rw [show toExpr (fun _ => none) t = some c from ht,
    show toExpr (fun _ => none) shape = some (trC shape) from toExprC_of_okC hs] at this
  exact Option.some.inj this

set_option linter.unusedSimpArgs false in
theorem natDeps_tr (c : Name) : ConLeche.natOpDeps (toName c) = (InLean.natOpDeps c).map toName := by
  by_cases hc : c ∈ [InLean.natPredName, InLean.natAddName, InLean.natSubName, InLean.natMulName,
      InLean.natPowName, InLean.natBeqName, InLean.natBleName, InLean.natDivName, InLean.natModName,
      InLean.natGcdName, InLean.natLandName, InLean.natLorName, InLean.natXorName,
      InLean.natShiftLeftName, InLean.natShiftRightName]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl <;>
    (simp only [InLean.natOpDeps, ← toName_beq, List.map_cons, List.map_nil, ← cl_natPredName,
      ← cl_natAddName, ← cl_natSubName, ← cl_natMulName, ← cl_natPowName, ← cl_natDivName,
      ← cl_natModName, ← cl_natGcdName, ← cl_natLandName, ← cl_natLorName, ← cl_natXorName,
      ← cl_natShiftLeftName, ← cl_natShiftRightName, ← cl_natBeqName, ← cl_natBleName]; decide)
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := hc
    have t : ∀ {X : Name}, c ≠ X → toName c ≠ toName X := fun h e => h (toName_inj e)
    simp only [InLean.natOpDeps, ConLeche.natOpDeps, beq_iff_eq, h1, h2, h3, h4, h5, h6, h7, h8, h9,
      h10, h11, h12, h13, h14, h15, t h1, t h2, t h3, t h4, t h5, t h6, t h7, t h8, t h9, t h10,
      t h11, t h12, t h13, t h14, t h15, cl_natPredName, cl_natAddName, cl_natSubName,
      cl_natMulName, cl_natPowName, cl_natDivName, cl_natModName, cl_natGcdName, cl_natLandName,
      cl_natLorName, cl_natXorName, cl_natShiftLeftName, cl_natShiftRightName, cl_natBeqName,
      cl_natBleName, ↓reduceIte, List.map_nil, not_false_eq_true]

/-- A stored entry's name, levels and type, through the relation. -/
theorem find_cv_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Name}
    {ci : Lean.ConstantInfo} (h : fe.find? n = some ci) :
    ∃ cci, L.find? (toName n) = some cci ∧
      cci.toConstantVal.levelParams = ci.levelParams.map toName ∧
      toExprC ci.type = some cci.toConstantVal.type := by
  obtain ⟨cci, hc, hr⟩ := find_rel hP h
  obtain ⟨-, h2, h3⟩ := hr.cv
  exact ⟨cci, hc, by rw [h2, ci_cv_lps], by rw [ci_cv_type]; exact h3.2.2⟩

/-- A level-free entry of a closed type, through the relation. -/
theorem find_shape_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Name}
    {shape : Expr} (hs : okC shape = true)
    (h : (match fe.find? n with
      | some ci => ci.levelParams.isEmpty && InLean.tyIs ci.type shape
      | none => false) = true) :
    (match L.find? (toName n) with
      | some ci => ci.toConstantVal.levelParams.isEmpty && ci.toConstantVal.type == trC shape
      | none => false) = true := by
  split at h
  · rename_i ci hf
    obtain ⟨cci, hc, hl, ht⟩ := find_cv_tr hP hf
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    rw [hc]
    simp [hl, h.1, tyIs_tr ht hs h.2]
  · exact nomatch h

theorem natOpCod_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {c : Name}
    {e : Expr} {ce : ConLeche.Expr} (he : toExprC e = some ce)
    (h : InLean.natOpCod fe c e = true) : ConLeche.natOpCod L (toName c) ce = true := by
  have t : ∀ {X : Name}, c ≠ X → toName c ≠ toName X := fun h e => h (toName_inj e)
  unfold InLean.natOpCod at h
  unfold ConLeche.natOpCod
  by_cases hb : c = InLean.natBeqName ∨ c = InLean.natBleName
  · have hb1 : (c == InLean.natBeqName || c == InLean.natBleName) = true := by
      rcases hb with rfl | rfl <;> simp
    have hb2 : (toName c = ConLeche.natBeqName ∨ toName c = ConLeche.natBleName) := by
      rcases hb with rfl | rfl <;> simp [cl_natBeqName, cl_natBleName]
    simp only [hb1, ↓reduceIte, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    have hif : (decide (toName c = ConLeche.natBeqName) || decide (toName c = ConLeche.natBleName))
        = true := by simpa using hb2
    simp only [hif, ↓reduceIte, Bool.and_eq_true]
    refine ⟨by rw [tyIs_tr he (by decide) h1]; rfl, ?_⟩
    split at h2
    · rename_i ci hf
      obtain ⟨cci, hc, hl, ht⟩ := find_cv_tr hP hf
      rw [show toName InLean.boolName = ConLeche.boolName from rfl] at hc
      rw [hc]
      simp only [InLean.Pin.matches, Bool.and_eq_true, beq_iff_eq] at h2
      obtain ⟨⟨-, hlen⟩, hcl⟩ := h2
      have hbl : InLean.boolPin.lps = [] := by decide
      have hl0 : ci.levelParams = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hbl]; rfl)
      simp only [hl0, hbl, InLean.canonAt, InLean.stripMData, List.map_nil, BEq.rfl, ↓reduceIte]
        at hcl hl
      have := toExpr_of_clEq (fun _ => none) hcl
      rw [show toExpr (fun _ => none) (EO.stripMData ci.type) = toExprC ci.type from
          toExpr_stripMData _ _, ht] at this
      simp only [hl, List.isEmpty_nil, Bool.true_and]
      rw [show toExpr (fun _ => none) InLean.boolPin.type = some (.sort (.succ .zero)) by decide]
        at this
      simp [Option.some.inj this]
    · exact nomatch h2
  · simp only [not_or] at hb
    have hb1 : (c == InLean.natBeqName || c == InLean.natBleName) = false := by simp [hb.1, hb.2]
    have hif : (decide (toName c = ConLeche.natBeqName) || decide (toName c = ConLeche.natBleName))
        = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨t hb.1, t hb.2⟩
    simp only [hb1, Bool.false_eq_true, ↓reduceIte] at h
    simp only [hif, Bool.false_eq_true, ↓reduceIte]
    rw [tyIs_tr he (by decide) h]; rfl

theorem natOpTyPinned_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {c : Name}
    {e : Expr} {ce : ConLeche.Expr} (he : toExprC e = some ce)
    (h : InLean.natOpTyPinned fe c e = true) : ConLeche.natOpTyPinned L (toName c) ce = true := by
  rw [← toExprC_stripTop] at he
  unfold InLean.natOpTyPinned at h
  unfold ConLeche.natOpTyPinned
  simp only [cl_natPredName, toName_eq_iff]
  split at h
  · rename_i hp
    simp only [beq_iff_eq] at hp
    simp only [hp, ↓reduceIte]
    split at h
    · rename_i n dom body bi hx
      rw [hx] at he
      obtain ⟨cd, cb, hd, hb, rfl⟩ := toExpr_forallE_inv he
      simp only [Bool.and_eq_true] at h
      subst hp
      simp only [tyIs_tr hd (by decide) h.1, natOpCod_tr hP hb h.2, Bool.and_true]
      rfl
    · exact nomatch h
  · rename_i hp
    simp only [beq_iff_eq] at hp
    simp only [hp, ↓reduceIte]
    split at h
    · rename_i n dom b bi hx
      rw [hx] at he
      obtain ⟨cd, cb, hd, hb, rfl⟩ := toExpr_forallE_inv he
      split at h
      · rename_i n2 dom2 body bi2 hx2
        have hb' : toExprC (EO.stripTop b) = some cb := by rw [toExprC_stripTop]; exact hb
        rw [hx2] at hb'
        obtain ⟨cd2, cb2, hd2, hb2, rfl⟩ := toExpr_forallE_inv hb'
        simp only [Bool.and_eq_true] at h
        simp only [tyIs_tr hd (by decide) h.1.1, tyIs_tr hd2 (by decide) h.1.2,
          natOpCod_tr hP hb2 h.2, Bool.and_true]
        rfl
      · exact nomatch h
    · exact nomatch h

/-- **InLean's stored-operation guard is master's.** -/
theorem natOpStoredOk_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Name}
    (h : InLean.natOpStoredOk fe n = true) : ConLeche.natOpStoredOk L (toName n) = true := by
  unfold InLean.natOpStoredOk at h
  split at h
  · rename_i v hf
    obtain ⟨cci, hc, hr⟩ := find_rel hP hf
    cases cci with
    | defnInfo ccv cval hh =>
      obtain ⟨⟨-, hl, ht⟩, -, -⟩ := hr
      simp only [Bool.and_eq_true, List.isEmpty_iff] at h
      unfold ConLeche.natOpStoredOk
      rw [hc]
      have ht' : toExprC (EO.stripMData v.type) = some ccv.type := by
        rw [toExprC_stripMData]; exact ht.2.2
      simp only [hl, h.1, List.map_nil, List.isEmpty_nil, Bool.true_and]
      exact natOpTyPinned_tr hP ht' h.2
    | _ => simp [EntryRelI] at hr
  · exact nomatch h

theorem trC_boolConst : trC (.const InLean.boolName []) = .const ConLeche.boolName [] := rfl

/-- **InLean's operation guard is master's**, where the `Nat` names hold
master's kinds and shapes (`natLitSupported`; InLean reads them stored). -/
theorem natOpGuard_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (hsh : ∀ n c, L.find? n = some c → ConLeche.litShapeOk c = true) (hk : ConLeche.NatKinds L)
    {c : Name} (h : InLean.natOpGuard fe c = true) : ConLeche.natOpGuard L (toName c) = true := by
  have t : ∀ {X : Name}, c ≠ X → toName c ≠ toName X := fun h e => h (toName_inj e)
  unfold InLean.natOpGuard at h
  unfold ConLeche.natOpGuard
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have g1 : ConLeche.natLitSupported L = true :=
    ConLeche.natLitSupported_of_shapes hsh hk (by rw [← natLitStoredF_I (envDomI_of hP)]; exact h1)
  have g2 : (ConLeche.natOpDeps (toName c)).all (fun n => match L.find? n with
      | some (.defnInfo cv _ _) => cv.levelParams.isEmpty
      | _ => false) = true := by
    rw [natDeps_tr, List.all_map]
    rw [List.all_eq_true] at h2 ⊢
    intro n hn
    have := h2 n hn
    simp only [Function.comp_apply]
    split at this
    · rename_i v hf
      obtain ⟨cci, hc, hr⟩ := find_rel hP hf
      cases cci with
      | defnInfo ccv cval hh =>
        rw [hc]; obtain ⟨⟨-, hl, -⟩, -⟩ := hr
        simp only [List.isEmpty_iff] at this ⊢
        rw [hl, this]; rfl
      | _ => simp [EntryRelI] at hr
    · exact nomatch this
  simp only [g1, Bool.true_and]
  by_cases hb : (c == InLean.natBeqName || c == InLean.natBleName ||
      InLean.natDivModNames.contains c) = true
  · simp only [hb, ↓reduceIte, Bool.and_eq_true] at h3
    have e1 := find_shape_tr hP (by decide) h3.1
    have e2 := find_shape_tr hP (by decide) h3.2
    rw [trC_boolConst] at e1 e2
    rw [← cl_boolTrueName] at e1
    rw [← cl_boolFalseName] at e2
    have hif : (decide (toName c = ConLeche.natBeqName) || decide (toName c = ConLeche.natBleName) ||
        ConLeche.natDivModNames.contains (toName c)) = true := by
      simp only [Bool.or_eq_true, beq_iff_eq] at hb
      rw [natDivModNames_tr, cl_natBeqName, cl_natBleName]
      simp only [Bool.or_eq_true, decide_eq_true_eq, toName_eq_iff]
      exact hb
    simp only [hif, ↓reduceIte, Bool.and_eq_true]
    exact ⟨g2, e1, e2⟩
  · have hif : (decide (toName c = ConLeche.natBeqName) || decide (toName c = ConLeche.natBleName) ||
        ConLeche.natDivModNames.contains (toName c)) = false := by
      simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at hb
      rw [natDivModNames_tr, cl_natBeqName, cl_natBleName]
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, toName_eq_iff]
      exact ⟨⟨hb.1.1, hb.1.2⟩, hb.2⟩
    simp only [hif, Bool.false_eq_true, ↓reduceIte, Bool.and_true]
    exact g2

/-! ## The recurrence equations -/

theorem substConst0_fvarlike {s : InLean.CState} {x : Expr} {d : Nat} {t : ConLeche.Expr}
    (hx : TrS s x = .fvar d t) (n : Name) (r : Expr) : InLean.substConst0 n r x = x := by
  cases x with
  | const c us => simp [TrS_const] at hx
  | app f a => simp [TrS_app] at hx
  | _ => rfl

theorem OkS_substConst0 {s : InLean.CState} {n : Name} {r : Expr} (hr : OkS s r = true) :
    ∀ e : Expr, OkS s e = true → OkS s (InLean.substConst0 n r e) = true := by
  intro e
  induction e with
  | const c us =>
    intro h
    cases us with
    | nil => simp only [InLean.substConst0]; split <;> assumption
    | cons => exact h
  | app f a ihf iha =>
    intro h
    simp only [OkS_app, Bool.and_eq_true, InLean.substConst0] at h ⊢
    exact ⟨ihf h.1, iha h.2⟩
  | _ => intro h; exact h

/-- **The equations over the interned variables are master's over `fvar 0`/`fvar 1`**, the
operation's self-references substituted on both sides. -/
theorem natOpEqs_tr {s : InLean.CState} {x y : Expr}
    (hx : TrS s x = .fvar 0 (.const ConLeche.natName []))
    (hy : TrS s y = .fvar 1 (.const ConLeche.natName [])) {c : Name}
    (hc : InLean.natOpNames.contains c = true) (r : Expr) :
    ((InLean.natOpEquations x y c).map fun x =>
        (InLean.substConst0 c r x.1, InLean.substConst0 c r x.2)).map
      (fun p => (TrS s p.1, TrS s p.2)) =
    (ConLeche.natOpEquations 0 (toName c)).map fun eq =>
      (ConLeche.Expr.substConst0 (toName c) (TrS s r) eq.1,
       ConLeche.Expr.substConst0 (toName c) (TrS s r) eq.2) := by
  have sx := substConst0_fvarlike hx c r
  have sy := substConst0_fvarlike hy c r
  simp only [InLean.natOpNames, List.contains_cons, List.contains_nil, Bool.or_false,
    Bool.or_eq_true, beq_iff_eq] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (config := { decide := true }) only [InLean.natOpEquations, ConLeche.natOpEquations,
    ← toName_beq, ← cl_natPredName, ← cl_natAddName, ← cl_natSubName, ← cl_natMulName,
    ← cl_natPowName, ← cl_natBeqName, ← cl_natBleName, ← cl_natZeroName, ← cl_natSuccName,
    ← cl_boolTrueName, ← cl_boolFalseName, List.map_cons, List.map_nil, InLean.substConst0, sx, sy,
    TrS_app, TrS_const, hx, hy, ConLeche.Expr.substConst0, ↓reduceIte]

theorem natOpEquations_okS {s : InLean.CState} {x y : Expr} (hx : OkS s x = true)
    (hy : OkS s y = true) (c : Name) :
    ∀ p ∈ InLean.natOpEquations x y c, OkS s p.1 = true ∧ OkS s p.2 = true := by
  unfold InLean.natOpEquations
  repeat' split
  all_goals simp [OkS_app, OkS_const, hx, hy]

/-- A closed replacement keeps the bound (master's `looseBVarsBounded_substConst0`,
`ConLeche/Semantics/DivModEval.lean`, restated off the semantic tier). -/
theorem lbb_substConst0 {n : ConLeche.Name} {r : ConLeche.Expr}
    (hr : r.looseBVarsBounded 0 = true) :
    ∀ (e : ConLeche.Expr) {k : Nat}, e.looseBVarsBounded k = true →
      (ConLeche.Expr.substConst0 n r e).looseBVarsBounded k = true
  | .const c us, k, he => by
    simp only [ConLeche.Expr.substConst0]
    split
    · exact ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le k) hr
    · exact he
  | .app f a, k, he => by
    simp only [ConLeche.Expr.substConst0, ConLeche.Expr.looseBVarsBounded,
      Bool.and_eq_true] at he ⊢
    exact ⟨lbb_substConst0 hr f he.1, lbb_substConst0 hr a he.2⟩
  | .bvar _, _, he | .fvar _ _, _, he | .sort _, _, he | .lit _, _, he
  | .lam _ _, _, he | .forallE _ _, _, he
  | .letE _ _ _, _, he | .proj _ _ _, _, he => he

set_option linter.unusedSimpArgs false in
theorem natOpEquations_lbb {c : ConLeche.Name} (hc : c ∈ ConLeche.natOpNames) :
    ∀ eq ∈ ConLeche.natOpEquations 0 c,
      eq.1.looseBVarsBounded 0 = true ∧ eq.2.looseBVarsBounded 0 = true := by
  simp only [ConLeche.natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (intro eq heq
     simp +decide [ConLeche.natOpEquations] at heq
     first
       | (rcases heq with rfl | rfl | rfl | rfl) <;>
           simp +decide [ConLeche.Expr.looseBVarsBounded]
       | (rcases heq with rfl | rfl | rfl) <;>
           simp +decide [ConLeche.Expr.looseBVarsBounded]
       | (rcases heq with rfl | rfl) <;>
           simp +decide [ConLeche.Expr.looseBVarsBounded])

/-- **The defeq loop at depth 2** (`certifyNatEqs`, master's): each equation's
sides read in range, scoped at the two variables and closed. -/
theorem certifyNatEqs_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L) :
    ∀ (eqs : List (Expr × Expr)) {s₀ s' : InLean.CState} {b : Bool},
      CSOKI .verified false L s₀ →
      (∀ p ∈ eqs, OkS s₀ p.1 = true ∧ OkS s₀ p.2 = true ∧
        ConLeche.Expr.WScoped 2 (TrS s₀ p.1) ∧ ConLeche.Expr.WScoped 2 (TrS s₀ p.2) ∧
        (TrS s₀ p.1).looseBVarsBounded 0 = true ∧ (TrS s₀ p.2).looseBVarsBounded 0 = true) →
      InLean.certifyNatEqs .verified fe eqs s₀ = .ok (b, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.certifyNatEqs (ConLeche.fueledOpsM .verified) L
          (eqs.map fun p => (TrS s₀ p.1, TrS s₀ p.2))) b := by
  intro eqs
  induction eqs with
  | nil =>
    intro s₀ s' b hs _ h
    unfold InLean.certifyNatEqs at h
    obtain ⟨rfl, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, by simp only [List.map_nil, ConLeche.certifyNatEqs]; exact Runs.pure _⟩
  | cons p rest ih =>
    intro s₀ s' b hs hp h
    obtain ⟨l, r⟩ := p
    unfold InLean.certifyNatEqs at h
    obtain ⟨b1, s₁, hD, h⟩ := bindI_ok h
    obtain ⟨o1, o2, w1, w2, c1, c2⟩ := hp (l, r) (List.mem_cons_self ..)
    obtain ⟨hs₁, ht₁, hRD⟩ := tripleI_iff_run.1 (hJ.ops.defeq (s₀ := s₀) (d := 2) (i := l) (j := r)
      hs o1 o2 w1 w2 c1 c2) b1 s₁ hD
    simp only [List.map_cons, ConLeche.certifyNatEqs]
    refine ⟨?_, ?_, Runs.bind hRD ?_⟩ <;> cases b1
    all_goals simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    · exact (pureI_ok h).2 ▸ hs₁
    · have hp' : ∀ q ∈ rest, OkS s₁ q.1 = true ∧ OkS s₁ q.2 = true ∧
          ConLeche.Expr.WScoped 2 (TrS s₁ q.1) ∧ ConLeche.Expr.WScoped 2 (TrS s₁ q.2) ∧
          (TrS s₁ q.1).looseBVarsBounded 0 = true ∧ (TrS s₁ q.2).looseBVarsBounded 0 = true := by
        intro q hq
        obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hp q (List.mem_cons_of_mem _ hq)
        rw [TrS_of_tabLe ht₁ q1, TrS_of_tabLe ht₁ q2]
        exact ⟨okS_of_tabLe ht₁ q1, okS_of_tabLe ht₁ q2, q3, q4, q5, q6⟩
      exact (ih hs₁ hp' h).1
    · exact (pureI_ok h).2 ▸ ht₁
    · have hp' : ∀ q ∈ rest, OkS s₁ q.1 = true ∧ OkS s₁ q.2 = true ∧
          ConLeche.Expr.WScoped 2 (TrS s₁ q.1) ∧ ConLeche.Expr.WScoped 2 (TrS s₁ q.2) ∧
          (TrS s₁ q.1).looseBVarsBounded 0 = true ∧ (TrS s₁ q.2).looseBVarsBounded 0 = true := by
        intro q hq
        obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hp q (List.mem_cons_of_mem _ hq)
        rw [TrS_of_tabLe ht₁ q1, TrS_of_tabLe ht₁ q2]
        exact ⟨okS_of_tabLe ht₁ q1, okS_of_tabLe ht₁ q2, q3, q4, q5, q6⟩
      exact ht₁.trans (ih hs₁ hp' h).2.1
    · obtain ⟨rfl, -⟩ := pureI_ok h; exact Runs.pure _
    · have hp' : ∀ q ∈ rest, OkS s₁ q.1 = true ∧ OkS s₁ q.2 = true ∧
          ConLeche.Expr.WScoped 2 (TrS s₁ q.1) ∧ ConLeche.Expr.WScoped 2 (TrS s₁ q.2) ∧
          (TrS s₁ q.1).looseBVarsBounded 0 = true ∧ (TrS s₁ q.2).looseBVarsBounded 0 = true := by
        intro q hq
        obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hp q (List.mem_cons_of_mem _ hq)
        rw [TrS_of_tabLe ht₁ q1, TrS_of_tabLe ht₁ q2]
        exact ⟨okS_of_tabLe ht₁ q1, okS_of_tabLe ht₁ q2, q3, q4, q5, q6⟩
      have := (ih hs₁ hp' h).2.2
      have he : (rest.map fun p => (TrS s₁ p.1, TrS s₁ p.2)) =
          rest.map fun p => (TrS s₀ p.1, TrS s₀ p.2) := by
        refine List.map_congr_left fun q hq => ?_
        obtain ⟨q1, q2, -⟩ := hp q (List.mem_cons_of_mem _ hq)
        rw [TrS_of_tabLe ht₁ q1, TrS_of_tabLe ht₁ q2]
      rwa [he] at this

/-! ## The structural operations' arm -/

theorem natOpNames_cases {c : Name} (hc : InLean.natOpNames.contains c = true) :
    c = InLean.natPredName ∨ c = InLean.natAddName ∨ c = InLean.natSubName ∨
      c = InLean.natMulName ∨ c = InLean.natPowName ∨ c = InLean.natBeqName ∨
      c = InLean.natBleName := by
  simpa [InLean.natOpNames] using hc

theorem natOp_off {c : Name} (hc : InLean.natOpNames.contains c = true) :
    InLean.natDivModNames.contains c = false ∧
      ConLeche.litGuardNames.contains (toName c) = false ∧
      toName c ≠ ConLeche.natName ∧ toName c ≠ ConLeche.natZeroName ∧
      toName c ≠ ConLeche.natSuccName ∧ c ≠ InLean.sorryAxName := by
  rw [← natDivModNames_tr]
  rcases natOpNames_cases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨by decide, by decide, by decide, by decide, by decide,
      ne_of_toName (by decide)⟩

/-- **A definition at a structural operation's name** (`checkDefnC`'s
certification by `certifyNatEqs`, master's `.defnDecl` arm with its
`natOpNames` branch), where the `Nat` names hold master's kinds. -/
theorem checkDefnC_struct_sim {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L)
    (hk : ConLeche.NatKinds L) {pins : List ConLeche.NatOpPinSet} {v : DefinitionVal}
    {a : InLean.Added} {s₀ s' : InLean.CState}
    (hs : CSOKI .verified false L s₀) (hr : Expr.RangeOk v.type) (hrv : Expr.RangeOk v.value)
    (hsafe : v.safety = .safe) (hn : InLean.natOpNames.contains v.name = true)
    (h : InLean.checkDefnC .verified InLeanProof.theoremConfig fe v s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ a.consts = #[.defnInfo v] ∧
      ∃ d, toDecl [.defnInfo v] = some d ∧ KindRuns pins L d := by
  obtain ⟨hnd, hlit, hN0, hN1, hN2, hso⟩ := natOp_off hn
  unfold InLean.checkDefnC at h
  simp only [hsafe, show (DefinitionSafety.safe == DefinitionSafety.unsafe) = false from rfl,
    Bool.false_eq_true, ↓reduceIte, hn, Bool.true_or,
    show InLeanProof.theoremConfig.uncertifiedNatOps = false from rfl] at h
  obtain ⟨_, s₁, hC, h⟩ := bindI_ok h
  have hfresh := checkConstantValC_fresh hC
  obtain ⟨hs₁, ht₁, hok, hlbb, hRC⟩ := checkConstantValC_sim hJ hs hr hC
  obtain ⟨_, s₂, hV, h⟩ := bindI_ok h
  obtain ⟨hs₂, ht₂, hokv, hVR⟩ := checkValueC_sim hJ hs₁ hrv hok hlbb hV
  obtain ⟨_, s₃, hCert, h⟩ := bindI_ok h
  obtain ⟨rfl, rfl⟩ := pureI_ok h
  simp only [hnd, Bool.false_eq_true, ↓reduceIte] at hCert
  split at hCert
  rotate_left
  · exact (throw_bindI_ok hCert).elim
  rename_i hg
  simp only [Bool.and_eq_true] at hg
  obtain ⟨xy, sN, hX, hCert⟩ := bindI_ok hCert
  unfold InLean.natVars at hX
  obtain ⟨x, s₃', hX1, hX⟩ := bindI_ok hX
  obtain ⟨y, s₄, hX2, hX⟩ := bindI_ok hX
  obtain ⟨rfl, hss⟩ := pureI_ok hX
  subst hss
  have hnat : ∀ s : InLean.CState, OkS s InLean.natTy = true ∧
      TrS s InLean.natTy = .const ConLeche.natName [] := fun _ => ⟨rfl, rfl⟩
  obtain ⟨hs₃', ht₃', hokx, hTx⟩ := tripleI_iff_run.1 (mkFVarM_specI hs₂ 0 (hnat s₂).1
    (by rw [(hnat s₂).2]; rfl)) x s₃' hX1
  obtain ⟨hs₄, ht₄, hoky, hTy⟩ := tripleI_iff_run.1 (mkFVarM_specI hs₃' 1 (hnat s₃').1
    (by rw [(hnat s₃').2]; rfl)) y s₄ hX2
  rw [(hnat s₂).2] at hTx
  rw [(hnat s₃').2] at hTy
  have hTx' : TrS s₄ x = .fvar 0 (.const ConLeche.natName []) := by rw [TrS_of_tabLe ht₄ hokx, hTx]
  have hokx' := okS_of_tabLe ht₄ hokx
  have hokv' : OkS s₄ v.value = true := OkS_of_okC _ hokv
  have hTv : TrS s₄ v.value = trC v.value := TrS_of_okC _ hokv
  obtain ⟨b, s₅, hE, hCert⟩ := bindI_ok hCert
  simp only at hE
  have htr := natOpEqs_tr (s := s₄) hTx' hTy hn v.value
  rw [hTv] at htr
  have hmem : ∀ q ∈ ConLeche.natOpEquations 0 (toName v.name),
      (ConLeche.Expr.substConst0 (toName v.name) (trC v.value) q.1).WScoped 2 ∧
      (ConLeche.Expr.substConst0 (toName v.name) (trC v.value) q.2).WScoped 2 ∧
      (ConLeche.Expr.substConst0 (toName v.name) (trC v.value) q.1).looseBVarsBounded 0 = true ∧
      (ConLeche.Expr.substConst0 (toName v.name) (trC v.value) q.2).looseBVarsBounded 0 = true := by
    intro q hq
    have hcn : toName v.name ∈ ConLeche.natOpNames := by
      rw [← List.contains_iff_mem, natOpNames_tr]; exact hn
    obtain ⟨w1, w2⟩ := ConLeche.natOpEquations_wscopedB hcn q hq
    obtain ⟨l1, l2⟩ := natOpEquations_lbb hcn q hq
    exact ⟨ConLeche.Expr.WScoped.of_wscopedB (ConLeche.wscopedB_substConst0 (trC_hasFvar _) _ w1),
      ConLeche.Expr.WScoped.of_wscopedB (ConLeche.wscopedB_substConst0 (trC_hasFvar _) _ w2),
      lbb_substConst0 hVR.1 _ l1, lbb_substConst0 hVR.1 _ l2⟩
  have hpre : ∀ p ∈ (InLean.natOpEquations x y v.name).map (fun x =>
      (InLean.substConst0 v.name v.value x.1, InLean.substConst0 v.name v.value x.2)),
      OkS s₄ p.1 = true ∧ OkS s₄ p.2 = true ∧
        ConLeche.Expr.WScoped 2 (TrS s₄ p.1) ∧ ConLeche.Expr.WScoped 2 (TrS s₄ p.2) ∧
        (TrS s₄ p.1).looseBVarsBounded 0 = true ∧ (TrS s₄ p.2).looseBVarsBounded 0 = true := by
    intro p hp
    have hp' : (TrS s₄ p.1, TrS s₄ p.2) ∈ (ConLeche.natOpEquations 0 (toName v.name)).map fun eq =>
        (ConLeche.Expr.substConst0 (toName v.name) (trC v.value) eq.1,
         ConLeche.Expr.substConst0 (toName v.name) (trC v.value) eq.2) := by
      rw [← htr]; exact List.mem_map_of_mem hp
    obtain ⟨q, hq, hqe⟩ := List.mem_map.1 hp'
    simp only [Prod.mk.injEq] at hqe
    obtain ⟨w1, w2, l1, l2⟩ := hmem q hq
    rw [← hqe.1, ← hqe.2]
    obtain ⟨lr, hlr, rfl⟩ := List.mem_map.1 hp
    obtain ⟨o1, o2⟩ := natOpEquations_okS hokx' hoky v.name lr hlr
    exact ⟨OkS_substConst0 hokv' _ o1, OkS_substConst0 hokv' _ o2, w1, w2, l1, l2⟩
  obtain ⟨hs₅, ht₅, hRE⟩ := certifyNatEqs_sim hJ _ hs₄ hpre hE
  rw [htr] at hRE
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at hCert; exact (throw_bindI_ok hCert).elim
  simp only [↓reduceIte] at hCert
  obtain ⟨-, rfl⟩ := pureI_ok hCert
  -- master's environment with the definition pushed, against InLean's
  have hd : toDecl [.defnInfo v] = some (.defnDecl (trCVn v.name v.levelParams v.type)
      (trC v.value) (toHint v.hints)) := by
    simp [toDecl, toCV_of_okC (v := v.toConstantVal) hok, toExprC_of_okC hokv]
  have hP2 := presI_defn hJ.laws hJ.pres hd hfresh hr hrv hsafe (fun h => (hso h).elim)
  have hfe2 : fe.push (.defnInfo v) = { fe with env := InLean.addConst fe.env (.defnInfo v) } := rfl
  rw [← hfe2] at hP2
  simp only [ConLeche.declConstants, ConLeche.declTables, ConLeche.Env.pushDelta, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.singleton_append] at hP2
  have hsh2 : ∀ n c, ConLeche.Env.find? ⟨.defnInfo (trCVn v.name v.levelParams v.type)
      (trC v.value) (toHint v.hints) :: L.consts, L.tables⟩ n = some c →
      ConLeche.litShapeOk c = true := by
    intro n c hc
    rw [env_find_cons] at hc
    split at hc
    · cases hc; exact ConLeche.litShapeOk_of_not_lit hlit
    · exact hJ.wf.shapes _ (ConLeche.Env.find?_mem hc)
  have hk2 : ConLeche.NatKinds ⟨.defnInfo (trCVn v.name v.levelParams v.type)
      (trC v.value) (toHint v.hints) :: L.consts, L.tables⟩ := by
    refine ⟨fun c hc => hk.1 c ?_, fun c hc => hk.2.1 c ?_, fun c hc => hk.2.2 c ?_⟩ <;>
      rw [env_find_cons] at hc <;>
      simpa [ConLeche.ConstantInfo.name, ConLeche.ConstantInfo.toConstantVal, trCVn, hN0, hN1, hN2] using hc
  have g1 := natOpGuard_tr hP2 hsh2 hk2 hg.1
  have g2 : (ConLeche.natOpDeps (toName v.name)).all (ConLeche.natOpStoredOk
      ⟨.defnInfo (trCVn v.name v.levelParams v.type) (trC v.value) (toHint v.hints) :: L.consts,
        L.tables⟩) = true := by
    have := hg.2
    rw [natDeps_tr, List.all_map]
    rw [List.all_eq_true] at this ⊢
    intro n hn'
    exact natOpStoredOk_tr hP2 (this n hn')
  have hself : ConLeche.Env.find? ⟨.defnInfo (trCVn v.name v.levelParams v.type) (trC v.value)
      (toHint v.hints) :: L.consts, L.tables⟩ (toName v.name) =
      some (.defnInfo (trCVn v.name v.levelParams v.type) (trC v.value) (toHint v.hints)) := by
    rw [env_find_cons]; simp [ConLeche.ConstantInfo.name, ConLeche.ConstantInfo.toConstantVal, trCVn]
  refine ⟨hs₅, ht₁.trans (ht₂.trans (ht₃'.trans (ht₄.trans ht₅))), rfl, _, hd,
    ⟨.defnInfo (trCVn v.name v.levelParams v.type) (trC v.value) (toHint v.hints) :: L.consts,
      L.tables⟩, Runs.bind hRC (Runs.bind (checkDefnVal_runs hVR) ?_)⟩
  have hn' : ConLeche.natOpNames.contains (toName v.name) = true := by rw [natOpNames_tr]; exact hn
  have hnd' : ConLeche.natDivModNames.contains (toName v.name) = false := by
    rw [natDivModNames_tr]; exact hnd
  simp only [trCVn] at g1 g2 hself ⊢
  simp only [hn', g1, g2, hself, hnd', Bool.and_self, Bool.false_eq_true, ↓reduceIte]
  exact Runs.bind hRE (by simp only [↓reduceIte]; exact Runs.pure _)

/-! ## The WF operations' environment guard -/

/-- A stored entry at a closed type, through the relation. -/
theorem find_type_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L) {n : Name}
    {shape : Expr} (hs : okC shape = true)
    (h : (match fe.find? n with
      | some ci => InLean.tyIs ci.type shape
      | none => false) = true) :
    (match L.find? (toName n) with
      | some ci => ci.toConstantVal.type == trC shape
      | none => false) = true := by
  split at h
  · rename_i ci hf
    obtain ⟨cci, hc, -, ht⟩ := find_cv_tr hP hf
    rw [hc]
    simp [tyIs_tr ht hs h]
  · exact nomatch h

/-- **InLean's WF operations' environment guard is master's** (at the pushed
environment), where the `Nat` names hold master's kinds and shapes. -/
theorem divModEnvGuard_tr {fe : InLean.FEnv} {L : ConLeche.Env} (hP : EnvPresI fe L)
    (hsh : ∀ n c, L.find? n = some c → ConLeche.litShapeOk c = true) (hk : ConLeche.NatKinds L)
    {c : Name} (h : InLean.divModEnvGuard fe c = true) :
    ConLeche.divModEnvGuard L (toName c) = true := by
  unfold InLean.divModEnvGuard at h
  unfold ConLeche.divModEnvGuard
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  have e1 := natOpGuard_tr hP hsh hk h1
  have e2 : (ConLeche.natOpDeps (toName c)).all (ConLeche.natOpStoredOk L) = true := by
    rw [natDeps_tr, List.all_map]
    rw [List.all_eq_true] at h2 ⊢
    intro n hn'
    exact natOpStoredOk_tr hP (h2 n hn')
  have e3 := find_isSome_of_pres hP h3
  have e4 := find_type_tr hP (by decide) h4
  have e5 := find_type_tr hP (by decide) h5
  rw [trC_boolConst, ← cl_boolTrueName] at e4
  rw [trC_boolConst, ← cl_boolFalseName] at e5
  rw [show toName InLean.eqName = ConLeche.eqName from rfl] at e3
  simp only [e1, e2, e3, Bool.and_true, Bool.true_and, Bool.and_eq_true]
  exact ⟨e4, e5⟩

/-! ## The pin variants InLean loads, as master's

InLean decodes its pin variants at run time (`loadPinSets ()`, the embedded
dumps); master takes its list as a parameter (`pins`, task #304).  The
statement instantiates `pins` with the translation of what InLean decodes:
an operation a variant lacks maps to a pin master's guard refuses (a loose
bound variable, `divModPinGuard`'s first conjunct), as InLean skips the
variant. -/

/-- One operation's pin in a variant, translated (refused where absent). -/
@[expose] def trOpPin (ps : InLean.PinSet) (c : Name) : ConLeche.Expr :=
  match ps.op? c with
  | some op => trC op.pin
  | none => .bvar 0

/-- One operation's certificate proofs in a variant, translated. -/
@[expose] def trOpProofs (ps : InLean.PinSet) (c : Name) : List ConLeche.Expr :=
  match ps.op? c with
  | some op => op.proofs.toList.map trC
  | none => []

/-- One operation's type pins in a variant, translated. -/
@[expose] def trOpTypePins (ps : InLean.PinSet) (c : Name) : List (ConLeche.Name × ConLeche.Expr) :=
  match ps.op? c with
  | some op => op.typePins.toList.map fun p => (toName p.1, trC p.2)
  | none => []

/-- **A pin variant, translated** (`InLean.PinSet` → `NatOpPinSet`). -/
@[expose] def trPinSet (ps : InLean.PinSet) : ConLeche.NatOpPinSet where
  toolchain := ps.toolchain
  divPin := trOpPin ps InLean.natDivName
  modPin := trOpPin ps InLean.natModName
  gcdPin := trOpPin ps InLean.natGcdName
  landPin := trOpPin ps InLean.natLandName
  lorPin := trOpPin ps InLean.natLorName
  xorPin := trOpPin ps InLean.natXorName
  shiftLeftPin := trOpPin ps InLean.natShiftLeftName
  shiftRightPin := trOpPin ps InLean.natShiftRightName
  divProofs := trOpProofs ps InLean.natDivName
  modProofs := trOpProofs ps InLean.natModName
  gcdProofs := trOpProofs ps InLean.natGcdName
  landProofs := trOpProofs ps InLean.natLandName
  lorProofs := trOpProofs ps InLean.natLorName
  xorProofs := trOpProofs ps InLean.natXorName
  shiftLeftProofs := trOpProofs ps InLean.natShiftLeftName
  shiftRightProofs := trOpProofs ps InLean.natShiftRightName
  divTypePins := trOpTypePins ps InLean.natDivName
  modTypePins := trOpTypePins ps InLean.natModName
  gcdTypePins := trOpTypePins ps InLean.natGcdName
  landTypePins := trOpTypePins ps InLean.natLandName
  lorTypePins := trOpTypePins ps InLean.natLorName
  xorTypePins := trOpTypePins ps InLean.natXorName
  shiftLeftTypePins := trOpTypePins ps InLean.natShiftLeftName
  shiftRightTypePins := trOpTypePins ps InLean.natShiftRightName

/-- **The variants InLean runs with, as master's list.**  Where the dumps do
not decode, InLean declines every pin-certified operation (an internal
error), so any list serves; the empty one is taken. -/
@[expose] def loadedPins : List ConLeche.NatOpPinSet :=
  match InLean.loadPinSets () with
  | .ok sets => sets.toList.map trPinSet
  | .error _ => []

/-! ## The certified operations' arm, from the WF operations' -/

/-- **The WF operations' arm** (named, not proved here): a definition at a
pin-certified operation's name (`checkDivModPin`), at `pins`, where the `Nat`
names hold master's kinds. -/
@[expose] def DivModArmSimI (pins : List ConLeche.NatOpPinSet) : Prop :=
  ∀ (fe : InLean.FEnv) (L : ConLeche.Env) (v : DefinitionVal) (a : InLean.Added)
    (s₀ s' : InLean.CState),
    JobEnvI fe L → ConLeche.NatKinds L → fe.safety = .safe → fe.coreAxioms = false →
    CSOKI .verified false L s₀ →
    Expr.RangeOk v.type → Expr.RangeOk v.value → v.safety = .safe →
    InLean.natDivModNames.contains v.name = true →
    InLean.checkDefnC .verified InLeanProof.theoremConfig fe v s₀ = .ok (a, s') →
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ a.consts = #[.defnInfo v] ∧
      ∃ d, toDecl [.defnInfo v] = some d ∧ KindRuns pins L d

/-- **`CertArmSimI`'s conclusion, from the WF operations' arm**, where the
`Nat` names hold master's kinds (the structural operations by
`checkDefnC_struct_sim`). -/
theorem certArm_of {pins : List ConLeche.NatOpPinSet} (hW : DivModArmSimI pins)
    {fe : InLean.FEnv} {L : ConLeche.Env} {v : DefinitionVal} {a : InLean.Added}
    {s₀ s' : InLean.CState} (hJ : JobEnvI fe L) (hk : ConLeche.NatKinds L)
    (hfs : fe.safety = .safe) (hfc : fe.coreAxioms = false) (hs : CSOKI .verified false L s₀)
    (hr : Expr.RangeOk v.type) (hrv : Expr.RangeOk v.value) (hsafe : v.safety = .safe)
    (hn : (InLean.natOpNames.contains v.name || InLean.natDivModNames.contains v.name) = true)
    (h : InLean.checkDefnC .verified InLeanProof.theoremConfig fe v s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ a.consts = #[.defnInfo v] ∧
      ∃ d, toDecl [.defnInfo v] = some d ∧ KindRuns pins L d := by
  cases hs1 : InLean.natOpNames.contains v.name
  · simp only [hs1, Bool.false_or] at hn
    exact hW fe L v a s₀ s' hJ hk hfs hfc hs hr hrv hsafe hn h
  · exact checkDefnC_struct_sim hJ hk hs hr hrv hsafe hs1 h

/-- **The declaration step for every non-inductive kind**, from the WF
operations' arm, where the `Nat` names hold master's kinds. -/
theorem checkDeclKindC_sim_nk {pins : List ConLeche.NatOpPinSet} (hW : DivModArmSimI pins)
    {fe : InLean.FEnv} {L : ConLeche.Env} (hJ : JobEnvI fe L) (hk : ConLeche.NatKinds L)
    {decl : Declaration} {a : InLean.Added} {s₀ s' : InLean.CState}
    (hfs : fe.safety = .safe) (hfc : fe.coreAxioms = false)
    (hs : CSOKI .verified false L s₀) (hd : SafeDecl decl) (hr : DeclRangeOk decl)
    (hnI : ∀ lps nP ts u, decl ≠ .inductDecl lps nP ts u)
    (hbn : InLean.basisNamesOk decl a = true)
    (h : InLean.checkDeclKindC .verified InLeanProof.theoremConfig fe decl s₀ = .ok (a, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      ∃ ds, a.consts.toList.mapM (fun ci => toDecl [ci]) = some ds ∧
        ∃ F L', ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
          .ok L' := by
  cases decl with
  | defnDecl v =>
    cases hn : (InLean.natOpNames.contains v.name || InLean.natDivModNames.contains v.name)
    · exact checkDeclKindC_sim hJ hfs hfc hs hd hr hn hbn h
    · obtain ⟨h1, h2, h3, d, hd', hR⟩ := certArm_of hW hJ hk hfs hfc hs hr.1 hr.2 hd hn h
      exact ⟨h1, h2, [d], by rw [h3]; exact single_mapM hd',
        single_fold hR (by rw [basisNamesOk_toDecl (fun _ h => by cases h) hd']; exact hbn)⟩
  | axiomDecl v =>
    by_cases hq : v.name = InLean.quotSoundName
    · exact checkDeclKindC_sim hJ hfs hfc hs hd hr (.inr hq) hbn h
    by_cases hso : v.name = InLean.sorryAxName
    · exact checkDeclKindC_sim hJ hfs hfc hs hd hr (.inl hso) hbn h
    obtain ⟨h1, h2, h3, -, d, hd', hR⟩ :=
      checkAxiomC_pinned_sim (pins := pins) hJ hfs hfc hs hr hd.1 hq hso h
    exact ⟨h1, h2, [d], by rw [h3]; exact single_mapM hd',
      single_fold hR (by rw [basisNamesOk_toDecl (fun _ h => by cases h) hd']; exact hbn)⟩
  | opaqueDecl v =>
    cases hn : InLean.reduceOpNames.contains v.name
    · exact checkDeclKindC_sim hJ hfs hfc hs hd hr hn hbn h
    · obtain ⟨h1, h2, h3, -, d, hd', hR⟩ :=
        checkOpaqueC_reduce_sim (pins := pins) hJ hs hr.1 hr.2 hn h
      exact ⟨h1, h2, [d], by rw [h3]; exact single_mapM hd',
      single_fold hR (by rw [basisNamesOk_toDecl (fun _ h => by cases h) hd']; exact hbn)⟩
  | thmDecl v => exact checkDeclKindC_sim hJ hfs hfc hs hd hr trivial hbn h
  | quotDecl => exact checkDeclKindC_sim hJ hfs hfc hs hd hr trivial hbn h
  | mutualDefnDecl vs => exact hd.elim
  | inductDecl lps nP ts u => exact (hnI lps nP ts u rfl).elim

/-- **O6 at the entry point, every non-inductive kind**, from the WF
operations' arm, where the `Nat` names hold master's kinds (`checkDecl_sim_full`
with the structural operations proved). -/
theorem checkDecl_sim_nk {pins : List ConLeche.NatOpPinSet} (hW : DivModArmSimI pins)
    {E : Kernel.Environment} {L : ConLeche.Env}
    (hJ : JobEnvI { env := E, coreAxioms := false } L) (hk : ConLeche.NatKinds L)
    {decl : Declaration} {a : InLean.Added}
    (hd : SafeDecl decl) (hr : DeclRangeOk decl) (hnI : ∀ lps nP ts u, decl ≠ .inductDecl lps nP ts u)
    (h : InLean.checkDecl InLeanProof.theoremConfig E decl = .ok a) :
    (∀ ci ∈ a.consts.toList, ci.name = InLean.sorryAxName → ∃ v, ci = .axiomInfo v) ∧
      ∃ ds, a.consts.toList.mapM (fun ci => toDecl [ci]) = some ds ∧
        ∃ F L', ds.foldlM (ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pins) L =
          .ok L' :=
  checkDecl_sim_of (fun hK hbn =>
    (checkDeclKindC_sim_nk hW hJ hk rfl rfl (CSOKI_empty L) hd hr hnI hbn hK).2.2) h

end InLeanProof
