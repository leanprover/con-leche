module

public import InLeanProof.PassRecs
import ConLeche.Verify.Cached.TargetRecC
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Inductives.NestScope

/-!
# O7-recursors: the class match and the classes' normal forms (task #451, lane O7-recursors)

The recursor stage (`genRecCheck`) against master's, continued bottom-up:

* `isDefEq_self_runs`: master's fueled definitional equality answers `true`
  on equal terms (its first test is `a == b`).  InLean's syntactic test
  (`clEq`) may fail where the readings agree (two variables at one depth with
  other annotations); InLean then infers and compares where master recurses at
  once, and this lemma rules out InLean's `false` there.
* `targetParamsDefEqI_run`, `targetHolesI_run`, `targetClassMatchI_run`,
  `targetMajorNfsI_run`, `classesNfsI_run`.

The scoping the inferences need is the frame's: the openers scoped at their
count, the formers' types closed (master's `targetClassMatchS_spec`).
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached

/-! ## Master's definitional equality on equal terms -/

/-- **Master's fueled definitional equality answers `true` on equal terms.** -/
theorem isDefEq_self_runs {L : ConLeche.Env} {d : Nat} {a : ConLeche.Expr} {v : Bool}
    (h : Runs ((ConLeche.fueledOpsM .verified).isDefEq L d a a) v) : v = true := by
  obtain ⟨F, hF⟩ := h
  cases F with
  | zero => cases hF
  | succ F =>
    simp only [ConLeche.fueledOpsM, ConLeche.isDefEqCore, ConLeche.pureFns, ConLeche.coreKnot, id,
      ConLeche.defeqBody, beq_self_eq_true, ↓reduceIte] at hF
    cases hF; rfl

/-! ## The per-component parameter match -/

/-- The parameter match's guard, read. -/
theorem tpdGuard_tr {s : InLean.CState} {a b : Lean.Expr} (ha : OkS s a = true)
    (hb : OkS s b = true) (n : Nat) :
    (!a.hasLooseBVars && !b.hasLooseBVars && decide (InLean.fvarB a ≤ n) &&
        decide (InLean.fvarB b ≤ n)) =
      ((TrS s a).bvarB == 0 && (TrS s b).bvarB == 0 && decide ((TrS s a).fvarB ≤ n) &&
        decide ((TrS s b).fvarB ≤ n)) := by
  rw [hasLooseBVars_TrS ha, hasLooseBVars_TrS hb, fvarB_tr ha, fvarB_tr hb,
    ConLeche.Expr.fvarB_eq, ConLeche.Expr.fvarB_eq]

/-- **The per-component parameter match** (`targetParamsDefEq`): InLean's
answer is master's on the readings, the abstraction `absM` read as `absC`
from the base state `sb` on, the compared terms scoped at `d` (`hW`). -/
theorem targetParamsDefEqI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L) {d : Nat}
    {absM : Lean.Expr → Lean.Expr} {absC : ConLeche.Expr → ConLeche.Expr} {pfvs : List Lean.Expr}
    {sb : InLean.CState} (hp : OkSL sb pfvs = true)
    (habs : ∀ s, TabLe sb s → ∀ e, OkS s e = true →
      OkS s (absM e) = true ∧ TrS s (absM e) = absC (TrS s e))
    (hW : ∀ x : ConLeche.Expr, x.bvarB = 0 → x.fvarB ≤ pfvs.length →
      ConLeche.Expr.WScoped d (absC (ConLeche.targetCanonParams (TrSL sb pfvs) x)) ∧
        (absC (ConLeche.targetCanonParams (TrSL sb pfvs) x)).looseBVarsBounded 0 = true) :
    ∀ (as bs : List Lean.Expr) {s₀ s' : InLean.CState} {v : Bool},
      CSOKI .verified false L s₀ → TabLe sb s₀ → OkSL s₀ as = true → OkSL s₀ bs = true →
      InLean.targetParamsDefEq (sharedOpsC .verified fe) fe d absM pfvs as bs s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.targetParamsDefEq (ConLeche.fueledOpsM .verified) L d absC (TrSL sb pfvs)
          (TrSL s₀ as) (TrSL s₀ bs)) v
  | [], [], s₀, s', v, hs, _, _, _, h => by
    unfold InLean.targetParamsDefEq at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by unfold ConLeche.targetParamsDefEq; exact Runs.pure _⟩
  | [], _ :: _, s₀, s', v, hs, _, _, _, h => by
    simp only [InLean.targetParamsDefEq] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by
      simp only [TrSL, List.map_nil]; exact Runs.pure _⟩
  | _ :: _, [], s₀, s', v, hs, _, _, _, h => by
    simp only [InLean.targetParamsDefEq] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by
      simp only [TrSL, List.map_nil]; exact Runs.pure _⟩
  | a :: as, b :: bs, s₀, s', v, hs, hb₀, hoa, hob, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at hoa hob
    have hp₀ := okSL_of_tabLe hb₀ hp
    have hpC : TrSL s₀ pfvs = TrSL sb pfvs := TrSL_of_tabLe hb₀ hp
    have hlen : (TrSL sb pfvs).length = pfvs.length := by simp [TrSL]
    unfold InLean.targetParamsDefEq at h
    simp only [TrSL_cons]
    unfold ConLeche.targetParamsDefEq
    rw [tpdGuard_tr hoa.1 hob.1] at h
    rw [hlen]
    cases hg : ((TrS s₀ a).bvarB == 0 && (TrS s₀ b).bvarB == 0 &&
        decide ((TrS s₀ a).fvarB ≤ pfvs.length) && decide ((TrS s₀ b).fvarB ≤ pfvs.length)) with
    | false =>
      simp only [hg, Bool.false_eq_true, ↓reduceIte] at h ⊢
      obtain ⟨rfl, rfl⟩ := pure_run h
      exact ⟨hs, TabLe.refl _, Runs.pure _⟩
    | true =>
      simp only [hg, ↓reduceIte] at h ⊢
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
      obtain ⟨⟨⟨hga, hgb⟩, hfa⟩, hfb⟩ := hg
      obtain ⟨hca, hcaT⟩ := targetCanonParamsI_tr hp₀ hoa.1
      obtain ⟨hcb, hcbT⟩ := targetCanonParamsI_tr hp₀ hob.1
      obtain ⟨hA, hAT⟩ := habs s₀ hb₀ _ hca
      obtain ⟨hB, hBT⟩ := habs s₀ hb₀ _ hcb
      rw [hcaT, hpC] at hAT
      rw [hcbT, hpC] at hBT
      rw [← hAT, ← hBT]
      obtain ⟨hWa, hLa⟩ := hW _ hga hfa
      obtain ⟨hWb, hLb⟩ := hW _ hgb hfb
      rw [← hAT] at hWa hLa
      rw [← hBT] at hWb hLb
      have hrec : ∀ {s₁ : InLean.CState} {w : Bool}, CSOKI .verified false L s₁ → TabLe s₀ s₁ →
          InLean.targetParamsDefEq (sharedOpsC .verified fe) fe d absM pfvs as bs s₁ =
            .ok (w, s') →
          CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
            Runs (ConLeche.targetParamsDefEq (ConLeche.fueledOpsM .verified) L d absC
              (TrSL sb pfvs) (TrSL s₀ as) (TrSL s₀ bs)) w := by
        intro s₁ w hs₁ ht₁ hr
        obtain ⟨hs', ht', hR⟩ := targetParamsDefEqI_run hO hp habs hW as bs hs₁ (hb₀.trans ht₁)
          (okSL_of_tabLe ht₁ hoa.2) (okSL_of_tabLe ht₁ hob.2) hr
        rw [TrSL_of_tabLe ht₁ hoa.2, TrSL_of_tabLe ht₁ hob.2] at hR
        exact ⟨hs', ht₁.trans ht', hR⟩
      cases hq : (absM (InLean.targetCanonParams pfvs a) == absM (InLean.targetCanonParams pfvs b)) with
      | true =>
        simp only [hq, ↓reduceIte] at h
        have he : TrS s₀ (absM (InLean.targetCanonParams pfvs a)) =
            TrS s₀ (absM (InLean.targetCanonParams pfvs b)) := TrS_of_clEq hA (TransS_of_ok hB) hq
        rw [he, beq_self_eq_true]; simp only [↓reduceIte]
        exact hrec hs (TabLe.refl _) h
      | false =>
        simp only [hq, Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨t₁, s₁, h1, h⟩ := bind_run h
        obtain ⟨hs₁, ht₁, -, hR1, -, -⟩ :=
          tripleI_iff_run.1 (hO.infer hs hA hWa hLa) t₁ s₁ h1
        obtain ⟨t₂, s₂, h2, h⟩ := bind_run h
        have hB₁ := okS_of_tabLe ht₁ hB
        rw [← TrS_of_tabLe ht₁ hB] at hWb hLb
        obtain ⟨hs₂, ht₂, -, hR2, -, -⟩ :=
          tripleI_iff_run.1 (hO.infer hs₁ hB₁ hWb hLb) t₂ s₂ h2
        rw [TrS_of_tabLe ht₁ hB] at hR2 hWb hLb
        have ht₀₂ := ht₁.trans ht₂
        obtain ⟨c, s₃, h3, h⟩ := bind_run h
        have hA₂ := okS_of_tabLe ht₀₂ hA
        have hB₂ := okS_of_tabLe ht₀₂ hB
        rw [← TrS_of_tabLe ht₀₂ hA] at hWa hLa
        rw [← TrS_of_tabLe ht₀₂ hB] at hWb hLb
        obtain ⟨hs₃, ht₃, hR3⟩ :=
          tripleI_iff_run.1 (hO.defeq hs₂ hA₂ hB₂ hWa hWb hLa hLb) c s₃ h3
        rw [TrS_of_tabLe ht₀₂ hA, TrS_of_tabLe ht₀₂ hB] at hR3
        have ht₀₃ := ht₀₂.trans ht₃
        cases hq' : (TrS s₀ (absM (InLean.targetCanonParams pfvs a)) ==
            TrS s₀ (absM (InLean.targetCanonParams pfvs b))) with
        | true =>
          simp only [↓reduceIte]
          have he := eq_of_beq hq'
          rw [he] at hR3
          have hc := isDefEq_self_runs hR3
          subst hc
          simp only [↓reduceIte] at h
          exact hrec hs₃ ht₀₃ h
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          cases c with
          | true =>
            simp only [↓reduceIte] at h
            obtain ⟨hs', ht', hR⟩ := hrec hs₃ ht₀₃ h
            exact ⟨hs', ht', Runs.bind hR1 (Runs.bind hR2 (Runs.bind hR3 (by
              simp only [↓reduceIte]; exact hR)))⟩
          | false =>
            simp only [Bool.false_eq_true, ↓reduceIte] at h
            obtain ⟨rfl, rfl⟩ := pure_run h
            exact ⟨hs₃, ht₀₃, Runs.bind hR1 (Runs.bind hR2 (Runs.bind hR3 (by
              simp only [Bool.false_eq_true, ↓reduceIte]; exact Runs.pure _)))⟩

/-! ## The holes and the class match -/

theorem getD_TrSL {s : InLean.CState} {l : List Lean.Expr} {t : Nat} (ht : t < l.length) :
    (TrSL s l).getD t default = TrS s (l.getD t default) := by
  simp [TrSL, List.getD_eq_getElem?_getD, ht]

/-- **The frame's holes** (`targetHoles`), interned: their readings are
master's holes over the formers' readings. -/
theorem targetHolesI_run {L : ConLeche.Env} {formerTys : List Lean.Expr} (base : Nat) :
    ∀ (l : List Nat) {s₀ s' : InLean.CState} {xs : List Lean.Expr},
      CSOKI .verified false L s₀ → OkSL s₀ formerTys = true →
      (∀ t ∈ TrSL s₀ formerTys, t.looseBVarsBounded 0 = true) →
      (∀ t ∈ l, t < formerTys.length) →
      l.mapM (fun t => InLean.mkFVarM (base + t) (formerTys.getD t default)) s₀ = .ok (xs, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ OkSL s' xs = true ∧
        TrSL s' xs = l.map fun t => .fvar (base + t) ((TrSL s₀ formerTys).getD t default)
  | [], s₀, s', xs, hs, _, _, _, h => by
    simp only [List.mapM_nil] at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, rfl, rfl⟩
  | i :: l, s₀, s', xs, hs, hfo, hfc, hl, h => by
    simp only [List.mapM_cons] at h
    have hi : i < formerTys.length := hl i List.mem_cons_self
    have hoi : OkS s₀ (formerTys.getD i default) = true := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      exact okS_getElem? hfo (List.getElem?_eq_getElem hi)
    have hci : (TrS s₀ (formerTys.getD i default)).looseBVarsBounded 0 = true := by
      rw [← getD_TrSL hi]
      refine hfc _ ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [TrSL, hi]),
        Option.getD_some]
      exact List.getElem_mem _
    obtain ⟨x, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hokx, htx⟩ :=
      tripleI_iff_run.1 (mkFVarM_specI hs (base + i) hoi hci) x s₁ h1
    obtain ⟨xs', s₂, h2, h⟩ := bind_run h
    obtain ⟨hs₂, ht₂, hok₂, htr₂⟩ := targetHolesI_run base l hs₁ (okSL_of_tabLe ht₁ hfo)
      (by rw [TrSL_of_tabLe ht₁ hfo]; exact hfc) (fun t ht => hl t (List.mem_cons_of_mem _ ht)) h2
    obtain ⟨rfl, rfl⟩ := pure_run h
    refine ⟨hs₂, ht₁.trans ht₂, ?_, ?_⟩
    · simp only [OkSL_cons, okS_of_tabLe ht₂ hokx, hok₂, Bool.and_self]
    · rw [TrSL_cons, htr₂, TrS_of_tabLe ht₂ hokx, htx, TrSL_of_tabLe ht₁ hfo, ← getD_TrSL hi]
      rfl

/-- The member abstraction keeps the loose-bvar bound, its holes closed. -/
theorem targetAbs_lbb {names : List ConLeche.Name} {lvls : List ConLeche.Level}
    {holes : List ConLeche.Expr} (hh : ∀ h ∈ holes, h.looseBVarsBounded 0 = true) :
    ∀ (e : ConLeche.Expr) (k : Nat), e.looseBVarsBounded k = true →
      (ConLeche.targetAbs names lvls holes e).looseBVarsBounded k = true := by
  intro e
  induction e with
  | const n us =>
    intro k h
    simp only [ConLeche.targetAbs]
    split
    · split
      · rw [List.getD_eq_getElem?_getD]
        cases hx : holes[‹Nat›]? with
        | none => exact h
        | some y =>
          exact ConLeche.Expr.looseBVarsBounded_mono (Nat.zero_le k)
            (hh y (List.mem_of_getElem? hx))
      · exact h
    · exact h
  | app a b iha ihb =>
    intro k h
    simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [ConLeche.targetAbs, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iha k h.1, ihb k h.2⟩
  | lam ty b iht ihb =>
    intro k h
    simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [ConLeche.targetAbs, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | forallE ty b iht ihb =>
    intro k h
    simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [ConLeche.targetAbs, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨iht k h.1, ihb (k + 1) h.2⟩
  | letE ty v b iht ihv ihb =>
    intro k h
    simp only [ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [ConLeche.targetAbs, ConLeche.Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨iht k h.1.1, ihv k h.1.2⟩, ihb (k + 1) h.2⟩
  | proj s i e ihe =>
    intro k h
    simp only [ConLeche.Expr.looseBVarsBounded] at h
    simp only [ConLeche.targetAbs, ConLeche.Expr.looseBVarsBounded]
    exact ihe k h
  | bvar _ | fvar _ _ | sort _ | lit _ => intro k h; exact h

theorem map_param_trL (lps : List Lean.Name) :
    (lps.map Lean.Level.param).map trL = (lps.map toName).map ConLeche.Level.param := by
  induction lps with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, ih]; rfl

/-- The frame's scoping facts: the openers scoped at their count and closed,
the formers' types closed. -/
@[expose] def FrameOk (pfvs formerTys : List ConLeche.Expr) : Prop :=
  (∀ x ∈ pfvs, ConLeche.Expr.WScoped pfvs.length x ∧ x.looseBVarsBounded 0 = true) ∧
    ∀ t ∈ formerTys, ConLeche.Expr.WScoped 0 t ∧ t.looseBVarsBounded 0 = true

/-- **The class match** (`targetClassMatch`): InLean's answer is master's on
the readings, in the frame `FrameOk`. -/
theorem targetClassMatchI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} {formerTys pfvs ds eds : List Lean.Expr} {us lvls : List Lean.Level}
    {s₀ s' : InLean.CState} {v : Bool} (hs : CSOKI .verified false L s₀)
    (hfo : OkSL s₀ formerTys = true) (hpo : OkSL s₀ pfvs = true)
    (hF : FrameOk (TrSL s₀ pfvs) (TrSL s₀ formerTys))
    (hus : us.all okLv = true) (hlv : lvls.all okLv = true)
    (hds : OkSL s₀ ds = true) (heds : OkSL s₀ eds = true)
    (h : InLean.targetClassMatch (sharedOpsC .verified fe) fe p formerTys pfvs us ds lvls eds s₀ =
      .ok (v, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.targetClassMatch (ConLeche.fueledOpsM .verified) L (trShape p)
        (TrSL s₀ formerTys) (TrSL s₀ pfvs) (us.map trL) (TrSL s₀ ds) (lvls.map trL)
        (TrSL s₀ eds)) v := by
  unfold InLean.targetClassMatch at h
  unfold ConLeche.targetClassMatch
  rw [← isEquivList_tr hus hlv]
  cases hq : (InLean.isEquivList us lvls == some true) with
  | false =>
    simp only [hq, Bool.false_eq_true, ↓reduceIte] at h ⊢
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | true =>
    simp only [hq, ↓reduceIte] at h ⊢
    unfold InLean.targetHoles at h
    obtain ⟨holes, s₁, h1, h⟩ := bind_run h
    obtain ⟨hF1, hF2⟩ := hF
    obtain ⟨hs₁, ht₁, hho, hhT⟩ := targetHolesI_run pfvs.length (List.range formerTys.length) hs
      hfo (fun t ht => (hF2 t ht).2) (fun t ht => List.mem_range.1 ht) h1
    have hlenF : (TrSL s₀ formerTys).length = formerTys.length := by simp [TrSL]
    have hlenP : (TrSL s₀ pfvs).length = pfvs.length := by simp [TrSL]
    have hhC : TrSL s₁ holes =
        ConLeche.targetHoles (TrSL s₀ formerTys) (TrSL s₀ pfvs).length := by
      rw [hhT, ConLeche.targetHoles, hlenF, hlenP]
    have hpC : TrSL s₁ pfvs = TrSL s₀ pfvs := TrSL_of_tabLe ht₁ hpo
    have habs : ∀ s, TabLe s₁ s → ∀ e, OkS s e = true →
        OkS s (InLean.targetAbs p.memberNames (p.lps.map .param) holes e) = true ∧
          TrS s (InLean.targetAbs p.memberNames (p.lps.map .param) holes e) =
            ConLeche.targetAbs (trShape p).memberNames ((trShape p).lps.map .param)
              (ConLeche.targetHoles (TrSL s₀ formerTys) (TrSL s₀ pfvs).length) (TrS s e) := by
      intro s hts e he
      rw [targetAbs_eq, trShape_memberNames, trShape_lps, ← map_param_trL, ← hhC,
        ← TrSL_of_tabLe hts hho]
      exact targetAbsI_tr _ (params_okLv _) (okSL_of_tabLe hts hho) e 0 he
    have hhW : ∀ x ∈ ConLeche.targetHoles (TrSL s₀ formerTys) (TrSL s₀ pfvs).length,
        ConLeche.Expr.WScoped ((TrSL s₀ pfvs).length + (TrSL s₀ formerTys).length) x :=
      targetHoles_WScoped (fun t ht => (hF2 t ht).1) _
    have hhL : ∀ x ∈ ConLeche.targetHoles (TrSL s₀ formerTys) (TrSL s₀ pfvs).length,
        x.looseBVarsBounded 0 = true := by
      intro x hx
      simp only [ConLeche.targetHoles, List.mem_map] at hx
      obtain ⟨_, _, rfl⟩ := hx
      rfl
    have hW : ∀ x : ConLeche.Expr, x.bvarB = 0 → x.fvarB ≤ pfvs.length →
        ConLeche.Expr.WScoped (pfvs.length + formerTys.length)
            (ConLeche.targetAbs (trShape p).memberNames ((trShape p).lps.map .param)
              (ConLeche.targetHoles (TrSL s₀ formerTys) (TrSL s₀ pfvs).length)
              (ConLeche.targetCanonParams (TrSL s₁ pfvs) x)) ∧
          (ConLeche.targetAbs (trShape p).memberNames ((trShape p).lps.map .param)
              (ConLeche.targetHoles (TrSL s₀ formerTys) (TrSL s₀ pfvs).length)
              (ConLeche.targetCanonParams (TrSL s₁ pfvs) x)).looseBVarsBounded 0 = true := by
      intro x hb hf
      rw [hpC]
      refine ⟨?_, ?_⟩
      · rw [← hlenF, ← hlenP]
        refine ConLeche.targetAbs_WScoped hhW _ (ConLeche.targetCanonParams_WScoped
          (fun y hy => (hF1 y hy).1.mono (by omega)) x (ConLeche.Expr.fvarsBelow_iff.2 (by rw [hlenP, ← ConLeche.Expr.fvarB_eq]; exact hf)))
      · refine targetAbs_lbb hhL _ 0 (ConLeche.looseBVarsBounded_replaceFVars ?_ x 0 ?_)
        · intro i r hr
          exact (hF1 r (List.mem_of_getElem? hr)).2
        · exact lbb_of_bvarB hb
    obtain ⟨hs', ht', hR⟩ := targetParamsDefEqI_run hO (okSL_of_tabLe ht₁ hpo) habs hW ds eds
      hs₁ (TabLe.refl _) (okSL_of_tabLe ht₁ hds) (okSL_of_tabLe ht₁ heds) h
    rw [hpC, TrSL_of_tabLe ht₁ hds, TrSL_of_tabLe ht₁ heds] at hR
    refine ⟨hs', ht₁.trans ht', ?_⟩
    rw [hlenP] at hR
    rw [hlenP, hlenF]
    exact hR

/-! ## The classes' recorded normal forms -/

/-- A recorded normal form has a reading. -/
@[expose] def OkNf (s : InLean.CState) (e : InLean.NestCtorNf) : Prop :=
  e.lvls.all okLv = true ∧ OkSL s e.ds = true ∧ OkS s e.ty = true

theorem OkNf.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {e : InLean.NestCtorNf}
    (he : OkNf s₀ e) : OkNf s₁ e ∧ trNf s₁ e = trNf s₀ e := by
  obtain ⟨h1, h2, h3⟩ := he
  refine ⟨⟨h1, okSL_of_tabLe h h2, okS_of_tabLe h h3⟩, ?_⟩
  unfold trNf
  rw [TrSL_of_tabLe h h2, TrS_of_tabLe h h3]

theorem map_trNf_mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {es : List InLean.NestCtorNf}, (∀ e ∈ es, OkNf s₀ e) → es.map (trNf s₁) = es.map (trNf s₀)
  | [], _ => rfl
  | e :: es, he => by
    rw [List.map_cons, List.map_cons, (OkNf.mono h (he e List.mem_cons_self)).2,
      map_trNf_mono h fun x hx => he x (List.mem_cons_of_mem _ hx)]

theorem ctorsAny_tr (ctors : List (Lean.ConstantVal × Nat)) (n : Lean.Name) :
    (ctors.map trCtor).any (·.1.name == toName n) = ctors.any (·.1.name == n) := by
  induction ctors with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, List.any_cons, ih]
    show ((toName c.1.name == toName n) || _) = _
    rw [toName_beq]

/-- **A class's recorded normal forms** (`targetMajorNfs`): the entries kept
are master's on the readings. -/
theorem targetMajorNfsI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} {formerTys pfvs ds : List Lean.Expr} {us : List Lean.Level}
    {ctors : List (Lean.ConstantVal × Nat)} (hus : us.all okLv = true) :
    ∀ (es : List InLean.NestCtorNf) {s₀ s' : InLean.CState} {v : List InLean.NestCtorNf},
      CSOKI .verified false L s₀ → OkSL s₀ formerTys = true → OkSL s₀ pfvs = true →
      FrameOk (TrSL s₀ pfvs) (TrSL s₀ formerTys) → OkSL s₀ ds = true → (∀ e ∈ es, OkNf s₀ e) →
      InLean.targetMajorNfs (sharedOpsC .verified fe) fe p formerTys pfvs us ds ctors es s₀ =
        .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ (∀ e ∈ v, e ∈ es) ∧
        Runs (ConLeche.targetMajorNfs (ConLeche.fueledOpsM .verified) L (trShape p)
          (TrSL s₀ formerTys) (TrSL s₀ pfvs) (us.map trL) (TrSL s₀ ds) (ctors.map trCtor)
          (es.map (trNf s₀))) (v.map (trNf s₀))
  | [], s₀, s', v, hs, _, _, _, _, _, h => by
    unfold InLean.targetMajorNfs at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, fun _ h => h, by unfold ConLeche.targetMajorNfs; exact Runs.pure _⟩
  | e :: es, s₀, s', v, hs, hfo, hpo, hF, hds, hes, h => by
    unfold InLean.targetMajorNfs at h
    rw [List.map_cons]
    unfold ConLeche.targetMajorNfs
    have he := hes e List.mem_cons_self
    have hes' := fun x hx => hes x (List.mem_cons_of_mem _ hx)
    obtain ⟨rest, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hsub, hR1⟩ := targetMajorNfsI_run hO hus es hs hfo hpo hF hds hes' h1
    cases hc : ctors.any (·.1.name == e.ctor) with
    | false =>
      simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨rfl, rfl⟩ := pure_run h
      refine ⟨hs₁, ht₁, fun x hx => List.mem_cons_of_mem _ (hsub x hx), Runs.bind hR1 ?_⟩
      simp only [trNf, ctorsAny_tr, hc, Bool.false_eq_true, ↓reduceIte]
      exact Runs.pure _
    | true =>
      simp only [hc, ↓reduceIte] at h
      obtain ⟨b, s₂, h2, h⟩ := bind_run h
      obtain ⟨he₁, -⟩ := OkNf.mono ht₁ he
      have hF₁ : FrameOk (TrSL s₁ pfvs) (TrSL s₁ formerTys) := by
        rw [TrSL_of_tabLe ht₁ hpo, TrSL_of_tabLe ht₁ hfo]; exact hF
      obtain ⟨hs₂, ht₂, hR2⟩ := targetClassMatchI_run hO hs₁ (okSL_of_tabLe ht₁ hfo)
        (okSL_of_tabLe ht₁ hpo) hF₁ hus he₁.1 (okSL_of_tabLe ht₁ hds) he₁.2.1 h2
      rw [TrSL_of_tabLe ht₁ hpo, TrSL_of_tabLe ht₁ hfo, TrSL_of_tabLe ht₁ hds,
        TrSL_of_tabLe ht₁ he.2.1] at hR2
      have ht₀₂ := ht₁.trans ht₂
      cases b with
      | true =>
        simp only [↓reduceIte] at h
        obtain ⟨rfl, rfl⟩ := pure_run h
        refine ⟨hs₂, ht₀₂, fun x hx => ?_, Runs.bind hR1 ?_⟩
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (hsub x hx)
        · simp only [trNf, ctorsAny_tr, hc, ↓reduceIte]
          exact Runs.bind hR2 (by simp only [↓reduceIte]; exact Runs.pure _)
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨rfl, rfl⟩ := pure_run h
        refine ⟨hs₂, ht₀₂, fun x hx => List.mem_cons_of_mem _ (hsub x hx), Runs.bind hR1 ?_⟩
        simp only [trNf, ctorsAny_tr, hc, ↓reduceIte]
        exact Runs.bind hR2 (by simp only [Bool.false_eq_true, ↓reduceIte]; exact Runs.pure _)

/-- A class with its recorded normal forms has a reading. -/
@[expose] def OkTMN (s : InLean.CState) (M : InLean.TargetMajor) : Prop :=
  M.lvls.all okLv = true ∧ OkSL s M.ds = true ∧ OkSL s M.pfvs = true ∧ ∀ e ∈ M.nfs, OkNf s e

theorem OkTMN.mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) {M : InLean.TargetMajor}
    (hM : OkTMN s₀ M) : OkTMN s₁ M ∧ trTM s₁ M = trTM s₀ M := by
  obtain ⟨h1, h2, h3, h4⟩ := hM
  refine ⟨⟨h1, okSL_of_tabLe h h2, okSL_of_tabLe h h3, fun e he => (OkNf.mono h (h4 e he)).1⟩, ?_⟩
  unfold trTM
  rw [TrSL_of_tabLe h h2, TrSL_of_tabLe h h3, map_trNf_mono h h4]

theorem map_trTM_mono {s₀ s₁ : InLean.CState} (h : TabLe s₀ s₁) :
    ∀ {Ms : List InLean.TargetMajor}, (∀ M ∈ Ms, OkTMN s₀ M) → Ms.map (trTM s₁) = Ms.map (trTM s₀)
  | [], _ => rfl
  | M :: Ms, hM => by
    rw [List.map_cons, List.map_cons, (OkTMN.mono h (hM M List.mem_cons_self)).2,
      map_trTM_mono h fun x hx => hM x (List.mem_cons_of_mem _ hx)]

/-- **The classes' recorded normal forms** (`classesNfs`): each class gets
master's entries of the table, read; nothing else of a class changes. -/
theorem classesNfsI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {p : InLean.BlockShape} {formerTys : List Lean.Expr} {tbl : List InLean.NestCtorNf} :
    ∀ (Ms : List InLean.TargetMajor) {s₀ s' : InLean.CState} {v : List InLean.TargetMajor},
      CSOKI .verified false L s₀ → OkSL s₀ formerTys = true → (∀ e ∈ tbl, OkNf s₀ e) →
      (∀ M ∈ Ms, OkTM s₀ M ∧ FrameOk (TrSL s₀ M.pfvs) (TrSL s₀ formerTys)) →
      InLean.classesNfs (sharedOpsC .verified fe) fe p formerTys tbl Ms s₀ = .ok (v, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧ (∀ M ∈ v, OkTMN s' M) ∧
        v.map (fun M => { M with nfs := [] }) = Ms ∧
        Runs (ConLeche.classesNfs (ConLeche.fueledOpsM .verified) L (trShape p)
          (TrSL s₀ formerTys) (tbl.map (trNf s₀)) (Ms.map (trTM s₀))) (v.map (trTM s'))
  | [], s₀, s', v, hs, _, _, _, h => by
    unfold InLean.classesNfs at h
    obtain ⟨rfl, rfl⟩ := pure_run h
    exact ⟨hs, TabLe.refl _, by simp, rfl, by unfold ConLeche.classesNfs; exact Runs.pure _⟩
  | M :: Ms, s₀, s', v, hs, hfo, htb, hMs, h => by
    unfold InLean.classesNfs at h
    rw [List.map_cons]
    unfold ConLeche.classesNfs
    obtain ⟨⟨hlv, hds, hpf, hnf⟩, hF⟩ := hMs M List.mem_cons_self
    obtain ⟨es, s₁, h1, h⟩ := bind_run h
    obtain ⟨hs₁, ht₁, hsub, hR1⟩ :=
      targetMajorNfsI_run hO hlv tbl hs hfo hpf hF hds htb h1
    obtain ⟨rest, s₂, h2, h⟩ := bind_run h
    obtain ⟨rfl, rfl⟩ := pure_run h
    have hMs' : ∀ M ∈ Ms, OkTM s₁ M ∧ FrameOk (TrSL s₁ M.pfvs) (TrSL s₁ formerTys) := by
      intro M' hM'
      obtain ⟨h1', h2'⟩ := hMs M' (List.mem_cons_of_mem _ hM')
      refine ⟨(OkTM.mono ht₁ h1').1, ?_⟩
      rw [TrSL_of_tabLe ht₁ h1'.2.2.1, TrSL_of_tabLe ht₁ hfo]; exact h2'
    obtain ⟨hs₂, ht₂, hok₂, hmap₂, hR2⟩ := classesNfsI_run hO Ms hs₁ (okSL_of_tabLe ht₁ hfo)
      (fun e he => (OkNf.mono ht₁ (htb e he)).1) hMs' h2
    have hMs₀ : ∀ M ∈ Ms, OkTM s₀ M := fun M' hM' => (hMs M' (List.mem_cons_of_mem _ hM')).1
    have hes : ∀ e ∈ es, OkNf s₀ e := fun e he => htb e (hsub e he)
    have hM' : OkTMN s₀ { M with nfs := es } := ⟨hlv, hds, hpf, hes⟩
    have hM₂ := (OkTMN.mono (ht₁.trans ht₂) hM').1
    refine ⟨hs₂, ht₁.trans ht₂, ?_, ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hM₂
      · exact hok₂ x hx
    · simp only [List.map_cons, hmap₂]
      congr 1
      cases M; simp_all
    · refine Runs.bind hR1 ?_
      rw [TrSL_of_tabLe ht₁ hfo, map_trNf_mono ht₁ htb,
        List.map_congr_left (fun M' hM' => (OkTM.mono ht₁ (hMs₀ M' hM')).2)] at hR2
      refine Runs.bind hR2 ?_
      rw [List.map_cons, (OkTMN.mono (ht₁.trans ht₂) hM').2]
      exact Runs.pure _

/-! ## The recursor records' pins -/

theorem blockRecLpsOk_tr (p : InLean.BlockShape) :
    ConLeche.blockRecLpsOk (trShape p) = InLean.blockRecLpsOk p := by
  unfold ConLeche.blockRecLpsOk InLean.blockRecLpsOk
  rw [trShape_lps]
  simp only [trShape, List.all_map, Function.comp_def, trRec, trCV]
  congr 1
  funext rc
  by_cases hl : p.large = true <;> simp only [hl, Bool.false_eq_true, ↓reduceIte, ← List.map_cons, map_toName_beq]

theorem reservedRecName_tr (n : Lean.Name) :
    ConLeche.reservedRecName (toName n) = InLean.reservedRecName n := by
  unfold ConLeche.reservedRecName InLean.reservedRecName
  have h1 : ConLeche.litGuardNames = InLean.litGuardNames.map toName := rfl
  have h2 : ConLeche.natOpNames = InLean.natOpNames.map toName := rfl
  have h3 : ConLeche.natDivModNames = InLean.natDivModNames.map toName := rfl
  have h4 : ConLeche.boolName = toName InLean.boolName := rfl
  have h5 : ConLeche.boolTrueName = toName InLean.boolTrueName := rfl
  have h6 : ConLeche.boolFalseName = toName InLean.boolFalseName := rfl
  rw [h1, h2, h3, h4, h5, h6, contains_map_toName, contains_map_toName, contains_map_toName,
    toName_beq, toName_beq, toName_beq]

theorem blockRecNamesUnreserved_tr (p : InLean.BlockShape) :
    ConLeche.blockRecNamesUnreserved (trShape p) = InLean.blockRecNamesUnreserved p := by
  unfold ConLeche.blockRecNamesUnreserved InLean.blockRecNamesUnreserved
  simp only [trShape, List.all_map, Function.comp_def, trRec, trCV, reservedRecName_tr]

theorem nameSet_tr (got want : List Lean.Name) :
    ((got.map toName).length == (want.map toName).length &&
        (want.map toName).all (fun n => (got.map toName).contains n) &&
        (got.map toName).all (fun n => (want.map toName).contains n)) =
      (got.length == want.length && want.all (fun n => got.contains n) &&
        got.all (fun n => want.contains n)) := by
  simp only [List.length_map, List.all_map, Function.comp_def, contains_map_toName]

theorem blockRecNameSetOk_tr (p : InLean.BlockShape) (recs : List InLean.RecShape) :
    ConLeche.blockRecNameSetOk { trShape p with recs := recs.map trRec } =
      InLean.blockRecNameSetOk { p with recs := recs } := by
  unfold ConLeche.blockRecNameSetOk InLean.blockRecNameSetOk
  have hw : (trShape p).members.map (fun ms => ms.cvT.name.str "rec") =
      (p.members.map fun ms => ms.cvT.name.str "rec").map toName := by
    simp only [trShape, List.map_map, Function.comp_def, trMember, trCV]; rfl
  have hg : (recs.map trRec).map (fun rc => rc.cvR.name) = (recs.map fun rc => rc.cvR.name).map toName := by
    simp only [List.map_map, Function.comp_def, trRec, trCV]
  simp only at hw hg ⊢
  rw [hw, hg, nameSet_tr]

theorem filter_own_tr (p : InLean.BlockShape) :
    (trShape p).recs.filter (fun rc => decide (rc.tgt < (trShape p).k)) =
      (p.recs.filter fun rc => decide (rc.tgt < p.k)).map trRec := by
  rw [trShape_k]
  simp only [trShape, List.filter_map, Function.comp_def, trRec]
  rfl

theorem filter_aux_tr (p : InLean.BlockShape) :
    (trShape p).recs.filter (fun rc => !decide (rc.tgt < (trShape p).k)) =
      (p.recs.filter fun rc => !decide (rc.tgt < p.k)).map trRec := by
  rw [trShape_k]
  simp only [trShape, List.filter_map, Function.comp_def, trRec]
  rfl

theorem trShape_recs (p : InLean.BlockShape) : (trShape p).recs = p.recs.map trRec := rfl

theorem names_trRec (l : List InLean.RecShape) :
    (l.map trRec).map (fun x => x.cvR.name) = (l.map fun x => x.cvR.name).map toName := by
  simp only [List.map_map, Function.comp_def, trRec, trCV]

theorem names_trCtorParts (l : List (Lean.ConstantVal × Nat × Nat)) :
    (l.map trCtorParts).map (fun x => x.fst.name) = (l.map fun x => x.fst.name).map toName := by
  simp only [List.map_map, Function.comp_def, trCtorParts, trCV]

theorem wantAux_tr (n0 : Lean.Name) (n : Nat) :
    (List.range n).map (fun i => (toName n0).str (toString "rec_" ++ toString (i + 1))) =
      ((List.range n).map fun i => n0.str (toString "rec_" ++ toString (i + 1))).map toName := by
  simp only [List.map_map, Function.comp_def]; rfl

theorem trShape_n0 (p : InLean.BlockShape) :
    ((trShape p).memberNames.head?).getD .anonymous =
      toName ((p.memberNames.head?).getD .anonymous) := by
  rw [trShape_memberNames]
  cases p.memberNames <;> rfl

/-- **The recursor records' pins** (`targetRecPins`): pure guards, read. -/
theorem targetRecPinsI_run {p : InLean.BlockShape} {block : List Lean.ConstantInfo}
    {s₀ s' : InLean.CState} {v : Unit} (h : InLean.targetRecPins p block s₀ = .ok (v, s')) :
    s' = s₀ ∧ Runs (ConLeche.targetRecPins (trShape p) (block.map trCI) : ConLeche.FueledM Unit) () := by
  unfold InLean.targetRecPins at h
  have hth : ∀ {α : Type} {e : InLean.CheckError} {k : α → InLean.CheckCM Unit},
      ¬ ((throw e : InLean.CheckCM α) >>= k) s₀ = .ok (v, s') := fun h => by
    obtain ⟨_, _, h1, -⟩ := bind_run h; exact throw_run h1
  cases g1 : InLean.blockRecLpsOk p <;> simp only [g1] at h
  · exact absurd h hth
  cases g2 : InLean.blockRecNamesUnreserved p <;> simp only [g2, ↓reduceIte] at h
  · exact absurd h hth
  split at h
  rotate_left
  · exact absurd h hth
  rename_i g3
  split at h
  rotate_left
  · exact absurd h hth
  rename_i g4
  split at h
  rotate_left
  · exact absurd h hth
  rename_i g5
  cases hsp : InLean.blockSplit block with
  | none => simp only [hsp] at h; exact (throw_run h).elim
  | some q =>
  obtain ⟨cvTs, cs, rs⟩ := q
  simp only [hsp] at h
  split at h
  rotate_left
  · exact (throw_run h).elim
  rename_i g6
  obtain ⟨-, rfl⟩ := pure_run h
  refine ⟨rfl, 0, ?_⟩
  unfold ConLeche.targetRecPins
  simp only [ConLeche.FueledM.atF_bind, ConLeche.FueledM.atF_ite,
    ConLeche.FueledM.atF_throw]
  have g5' := (namesNodup_iff _).1 g5
  simp only [blockRecLpsOk_tr, blockRecNamesUnreserved_tr, filter_own_tr, filter_aux_tr,
    blockRecNameSetOk_tr, trShape_n0]
  simp only [List.length_map, List.all_map, Function.comp_def] at g4
  simp only [names_trRec, List.length_map, wantAux_tr, List.all_map, Function.comp_def,
    contains_map_toName,
    trShape_recs, g1, g2, g3, g4, g5', ↓reduceIte, blockSplit_tr, hsp, Option.map_some,
    trShape_k, trShape_allCtorNames, names_trCtorParts, map_toName_beq, g6]
  rfl

end InLeanProof
