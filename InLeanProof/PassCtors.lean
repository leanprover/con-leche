module

public import InLeanProof.PassEnv
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.Cached.IndWalksC

/-!
# O7-stages: the constructors' stage against master's (task #451, lane O7-stages)

`checkBlockCtorsFI_run` (`checkBlockCtorsS_spec`'s twin): InLean's
`checkBlockCtorsC` at the formers' environment answers master's pure
`checkBlockCtors` at its formers' environment, from the constructor's constant
check (`CheckConstantValFSimI`, O6's) and the job's operations (`OpsSimI`,
from `JobEnvI` at the formers' push, `jobEnvI_formers`).

* **The resolution guards** (`constsResolveF` on the field domains and the
  index expressions) are not simulated: master's run at `env₀ = env` passes
  them whatever InLean's answered, because the constructor's constant check
  already resolved its type (`checkConstantVal_typeWF`) and opening a
  telescope keeps resolution (`openPisAtFvars_resolve`).  InLean's walks read
  no state there (`constsResolveF_noSt`).
* **The comparisons** (the result's head, its parameters, the index count, the
  field's membership among the indices) are InLean's checker equality
  (`Expr.clEq`), which gives equal readings (`TrS_of_clEq`).

The proofs are functional (`bindI_ok`, `pureI_ok`), as O7's.
-/

set_option experimental.vcgen true

public section

namespace InLeanProof

open Lean InLean Std.WP ConLeche.Cached
open scoped Lean.Order

variable {mode : ConLeche.CheckMode} {eager : Bool} {env : ConLeche.Env}

/-! ## Master's resolution through an opened telescope -/

theorem openPisAtFvars_resolve {E : ConLeche.Env} :
    ∀ (n : Nat) {e : ConLeche.Expr} {i : Nat} {fvs : List ConLeche.Expr} {b : ConLeche.Expr},
      ConLeche.openPisAtFvars n e i = some (fvs, b) → e.constsResolve E = true →
      (∀ x ∈ fvs, x.constsResolve E = true ∧ x.fvarTypeD.constsResolve E = true) ∧
        b.constsResolve E = true
  | 0, e, i, fvs, b, h, he => by
    simp only [ConLeche.openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp, he⟩
  | n + 1, .forallE dom body, i, fvs, b, h, he => by
    simp only [ConLeche.openPisAtFvars] at h
    simp only [ConLeche.Expr.constsResolve, Bool.and_eq_true] at he
    cases hr : ConLeche.openPisAtFvars n (body.instantiate1 (.fvar i dom)) (i + 1) with
    | none => rw [hr] at h; cases h
    | some q =>
      obtain ⟨fvs', b'⟩ := q
      rw [hr] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨ih1, ih2⟩ := openPisAtFvars_resolve n hr
        (ConLeche.Expr.constsResolve_instantiate1 he.1 0 he.2)
      refine ⟨fun x hx => ?_, ih2⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨by simpa [ConLeche.Expr.constsResolve] using he.1, by simpa [ConLeche.Expr.fvarTypeD] using he.1⟩
      · exact ih1 x hx
  | _ + 1, .bvar _, _, _, _, h, _ | _ + 1, .fvar _ _, _, _, _, h, _
  | _ + 1, .sort _, _, _, _, h, _ | _ + 1, .const _ _, _, _, _, h, _
  | _ + 1, .app _ _, _, _, _, h, _ | _ + 1, .lam _ _, _, _, _, h, _
  | _ + 1, .letE _ _ _, _, _, _, h, _ | _ + 1, .lit _, _, _, _, h, _
  | _ + 1, .proj _ _ _, _, _, _, h, _ => by simp [ConLeche.openPisAtFvars] at h

theorem constsResolve_getAppArgs {E : ConLeche.Env} :
    ∀ {e : ConLeche.Expr}, e.constsResolve E = true → ∀ a ∈ e.getAppArgs, a.constsResolve E = true
  | .app f x, h => by
    simp only [ConLeche.Expr.constsResolve, Bool.and_eq_true] at h
    intro a ha
    simp only [ConLeche.Expr.getAppArgs, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact constsResolve_getAppArgs h.1 a ha
    · exact h.2
  | .bvar _, _ | .fvar _ _, _ | .sort _, _ | .const _ _, _ | .lam _ _, _ | .forallE _ _, _
  | .letE _ _ _, _ | .lit _, _ | .proj _ _ _, _ => by simp [ConLeche.Expr.getAppArgs]

/-! ## Programs that read the state only -/

theorem NoSt.get : NoSt (get : InLean.CheckCM InLean.CState) := by
  intro s a s' h
  exact (Prod.mk.inj (Except.ok.inj h)).2.symm

theorem fvarTypeD_noSt (x : Lean.Expr) : NoSt (InLean.fvarTypeD x) := by
  unfold InLean.fvarTypeD InLean.fvarTypeM?
  repeat' (first
    | exact NoSt.pure _
    | exact NoSt.get
    | (apply NoSt.bind <;> intros)
    | split)

theorem constsResolveF_noSt (fe : InLean.FEnv) (e : Lean.Expr) : NoSt (InLean.constsResolveF fe e) := by
  unfold InLean.constsResolveF InLean.withAnnotations InLean.fvarClosureM
  repeat' (first
    | exact NoSt.pure _
    | exact NoSt.get
    | (apply NoSt.bind <;> intros)
    | apply NoSt.ite
    | split)

theorem NoSt.allM {α : Type} {f : α → InLean.CheckCM Bool} (hf : ∀ a, NoSt (f a)) :
    ∀ (l : List α), NoSt (l.allM f)
  | [] => by rw [List.allM_nil]; exact NoSt.pure true
  | a :: l => by
    rw [List.allM_cons]
    refine NoSt.bind (hf a) fun b => ?_
    cases b
    · exact NoSt.pure _
    · exact NoSt.allM hf l

/-! ## The checker's equality, read -/

theorem TrS_of_clEq {s : InLean.CState} {a b : Lean.Expr} (ha : OkS s a = true)
    (hb : TransS s b = some (TrS s b)) (h : Expr.clEq a b = true) : TrS s a = TrS s b := by
  have he := toExpr_of_clEq (FVarTable.trans (tableOf s)) h
  have h1 := TransS_of_ok ha
  have h2 := hb
  unfold TransS at h1 h2
  rw [he, h2] at h1
  exact (Option.some.inj h1).symm

theorem TrSL_of_beq {s : InLean.CState} :
    ∀ {l₁ l₂ : List Lean.Expr}, OkSL s l₁ = true → (∀ b ∈ l₂, TransS s b = some (TrS s b)) →
      (l₁ == l₂) = true → TrSL s l₁ = TrSL s l₂
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: l₁, b :: l₂, h₁, h₂, h => by
    simp only [OkSL_cons, Bool.and_eq_true] at h₁
    simp only [List.cons_beq_cons, Bool.and_eq_true] at h
    rw [TrSL_cons, TrSL_cons, TrS_of_clEq h₁.1 (h₂ b List.mem_cons_self) h.1,
      TrSL_of_beq h₁.2 (fun c hc => h₂ c (List.mem_cons_of_mem _ hc)) h.2]

theorem contains_TrSL {s : InLean.CState} {l : List Lean.Expr} {x : Lean.Expr} (hl : OkSL s l = true)
    (hx : OkS s x = true) (h : l.contains x = true) : (TrSL s l).contains (TrS s x) = true := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [OkSL_cons, Bool.and_eq_true] at hl
    simp only [List.contains_cons, Bool.or_eq_true] at h
    rw [TrSL_cons, List.contains_cons]
    rcases h with h | h
    · have : TrS s x = TrS s a := TrS_of_clEq hx (TransS_of_ok hl.1) h
      simp [this]
    · exact Bool.or_eq_true_iff.2 (.inr (ih hl.2 h))

/-! ## The constructor's result shape -/

theorem TrSL_structPsAt {s : InLean.CState} (o nP : Nat) :
    TrSL s (InLean.structPsAt o nP) = ConLeche.structPsAt o nP := by
  simp [TrSL, InLean.structPsAt, ConLeche.structPsAt, TrS, trE]

theorem TrS_const_params {s : InLean.CState} (T : Lean.Name) (lps : List Lean.Name) :
    TrS s (.const T (lps.map .param)) =
      .const (toName T) ((lps.map toName).map ConLeche.Level.param) := by
  simp [TrS, trE, List.map_map, Function.comp_def, trL]

/-- **The constructor's declared result** read at a state: InLean's
acceptance is master's on the reading. -/
theorem structCtorResidOk_TrS {s : InLean.CState} {T : Lean.Name} {lps : List Lean.Name}
    {nP o nIdx : Nat} {cbody : Lean.Expr} (hok : OkS s cbody = true)
    (h : InLean.structCtorResidOk T lps nP o nIdx cbody = true) :
    ConLeche.structCtorResidOk (toName T) (lps.map toName) nP o nIdx (TrS s cbody) = true := by
  unfold InLean.structCtorResidOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  unfold ConLeche.structCtorResidOk
  have hf := TrS_of_clEq (OkS_getAppFnT s hok)
    (TransS_of_ok (by simp [OkS, okE, okLv_param])) h1
  rw [TrS_getAppFnT, TrS_const_params] at hf
  have hn : (TrS s cbody).getAppArgs.length = nP + nIdx := by
    rw [← numArgs_TrS hok]; simpa using h2
  have ht := TrSL_of_beq (OkSL_take s (OkSL_appArgs s hok) nP)
    (by
      intro b hb
      simp only [InLean.structPsAt, List.mem_map] at hb
      obtain ⟨k, -, rfl⟩ := hb
      rw [mkBvar_eq]; rfl) h3
  rw [TrSL_take, TrSL_appArgs, TrSL_structPsAt] at ht
  simp [hf, hn, ht]

/-! ## The parameter domains against the former's -/

/-- **The constructor's parameter domains against the former's**
(`checkStructDomsAtS_spec`'s twin; `checkBlockDomsAtFI_run`'s script). -/
theorem checkStructDomsAtFI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {off : Nat} {fvs doms : List Lean.Expr} {cfvs cdoms : List ConLeche.Expr}
    (hcf : ∀ (i : Nat) (x : ConLeche.Expr), cfvs[i]? = some x →
      (∃ k ty, x = .fvar k ty) ∧ ConLeche.Expr.WScoped (off + i) x.fvarTypeD)
    (hcd : ∀ (i : Nat) (x : ConLeche.Expr), cdoms[i]? = some x →
      ConLeche.Expr.WScoped (off + i) x ∧ x.looseBVarsBounded 0 = true) :
    ∀ (j : Nat) {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ → OkSL s₀ fvs = true → OkSL s₀ doms = true →
      TrSL s₀ fvs = cfvs → TrSL s₀ doms = cdoms →
      InLean.checkStructDomsAtF (sharedOpsC .verified fe) fe off fvs.toArray doms.toArray j s₀ =
        .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkStructDomsAt (ConLeche.fueledOpsM .verified) L off cfvs cdoms j) ()
  | 0, s₀, s', u, hs, _, _, _, _, h => by
    unfold InLean.checkStructDomsAtF at h
    obtain ⟨-, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | j + 1, s₀, s', u, hs, hokf, hokd, htf, htd, h => by
    unfold InLean.checkStructDomsAtF at h
    obtain ⟨a, s₁, h1, hk1⟩ := bindI_ok h
    cases ha : fvs[j]? with
    | none => simp only [List.getElem?_toArray, ha, InLean.unwrapOr] at h1; exact (throwI_ok h1).elim
    | some a' =>
    simp only [List.getElem?_toArray, ha, InLean.unwrapOr] at h1
    obtain ⟨rfl, rfl⟩ := pureI_ok h1
    obtain ⟨b, s₂, h2, hk2⟩ := bindI_ok hk1
    cases hb : doms[j]? with
    | none => simp only [List.getElem?_toArray, hb, InLean.unwrapOr] at h2; exact (throwI_ok h2).elim
    | some b' =>
    simp only [List.getElem?_toArray, hb, InLean.unwrapOr] at h2
    obtain ⟨rfl, rfl⟩ := pureI_ok h2
    have hoka := okS_getElem? hokf ha
    have hokb := okS_getElem? hokd hb
    have hca : cfvs[j]? = some (TrS s₀ a') := htf ▸ TrSL_getElem? ha
    have hcb : cdoms[j]? = some (TrS s₀ b') := htd ▸ TrSL_getElem? hb
    obtain ⟨⟨k, ty, hfa⟩, hwa⟩ := hcf j _ hca
    obtain ⟨hwb, hcbb⟩ := hcd j _ hcb
    obtain ⟨t, s₄, h4, hk4⟩ := bindI_ok hk2
    obtain ⟨rfl, hokt, htt, hct⟩ := fvarTypeDI_run hs hoka hfa h4
    obtain ⟨c, s₃, h3, hk3⟩ := bindI_ok hk4
    rw [hfa] at hwa
    have hD := tripleI_iff_run.1 (hO.defeq (d := off + j) (i := t) (j := b') hs hokt hokb
      (by rw [htt]; exact hwa) hwb (by rw [htt]; exact hct) hcbb) c s₃ h3
    obtain ⟨hs₃, ht₃, hR3⟩ := hD
    rw [htt] at hR3
    cases c with
    | false =>
      simp only at hk3
      obtain ⟨_, _, h5, -⟩ := bindI_ok hk3
      exact (throwI_ok h5).elim
    | true =>
    simp only [↓reduceIte] at hk3
    obtain ⟨hs', ht', hR⟩ := checkStructDomsAtFI_run hO hcf hcd j hs₃ (okSL_of_tabLe ht₃ hokf)
      (okSL_of_tabLe ht₃ hokd) (by rw [TrSL_of_tabLe ht₃ hokf, htf])
      (by rw [TrSL_of_tabLe ht₃ hokd, htd]) hk3
    refine ⟨hs', ht₃.trans ht', ?_⟩
    unfold ConLeche.checkStructDomsAt
    simp only [hca, hcb, ConLeche.unwrapOr]
    refine Runs.bind (Runs.pure _) (Runs.bind (Runs.pure _) ?_)
    rw [hfa]
    simp only [ConLeche.Expr.fvarTypeD]
    refine Runs.bind hR3 ?_
    simp only [↓reduceIte]
    exact Runs.bind (Runs.pure _) hR

/-! ## The fields' sorts -/

theorem leq_trL {l r : Lean.Level} (hl : okL l = true) (hr : okL r = true) :
    Lvl.leq l r = ConLeche.Level.leq (trL l) (trL r) := by
  unfold Lvl.leq ConLeche.Level.leq
  rw [leqCore_trL _ _ _ _ (okL_simplify hl) (okL_simplify hr), trL_simplify hl, trL_simplify hr,
    defaultFuel_eq]

/-- **The fields' sorts** (`checkStructFieldSortsIS_spec`'s twin). -/
theorem checkStructFieldSortsIFI_run {fe : InLean.FEnv} {L : ConLeche.Env} (hO : OpsSimI fe L)
    {isProp large : Bool} {sr : Lean.Level} (hsr : okL sr = true) {nP : Nat}
    {fvs idx : List Lean.Expr} {cfvs cidx : List ConLeche.Expr}
    (hcf : ∀ (i : Nat) (x : ConLeche.Expr), cfvs[i]? = some x →
      (∃ k ty, x = .fvar k ty) ∧ ConLeche.Expr.WScoped (nP + i) x.fvarTypeD ∧
        x.fvarTypeD.looseBVarsBounded 0 = true) :
    ∀ (j : Nat) {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ → OkSL s₀ fvs = true → OkSL s₀ idx = true →
      TrSL s₀ fvs = cfvs → TrSL s₀ idx = cidx →
      InLean.checkStructFieldSortsIC (sharedOpsC .verified fe) fe isProp large sr nP fvs idx j s₀ =
        .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkStructFieldSortsI (ConLeche.fueledOpsM .verified) L isProp large (trL sr)
          nP cfvs cidx j) ()
  | 0, s₀, s', u, hs, _, _, _, _, h => by
    unfold InLean.checkStructFieldSortsIC at h
    obtain ⟨-, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | j + 1, s₀, s', u, hs, hokf, hoki, htf, hti, h => by
    unfold InLean.checkStructFieldSortsIC at h
    obtain ⟨a, s₁, h1, hk1⟩ := bindI_ok h
    cases ha : fvs[j]? with
    | none => simp only [ha, InLean.unwrapOr] at h1; exact (throwI_ok h1).elim
    | some a' =>
    simp only [ha, InLean.unwrapOr] at h1
    obtain ⟨rfl, rfl⟩ := pureI_ok h1
    have hoka := okS_getElem? hokf ha
    have hca : cfvs[j]? = some (TrS s₀ a') := htf ▸ TrSL_getElem? ha
    obtain ⟨⟨k, ty, hfa⟩, hwa, hcla⟩ := hcf j _ hca
    rw [hfa] at hwa hcla
    simp only [ConLeche.Expr.fvarTypeD] at hwa hcla
    obtain ⟨d, s₃, h3, hk2⟩ := bindI_ok hk1
    obtain ⟨hs3, hokd, htd, -⟩ := fvarTypeDI_run hs hoka hfa h3
    rw [hs3] at hk2
    obtain ⟨t, s₂, h2, hk3⟩ := bindI_ok hk2
    obtain ⟨hs₂, ht₂, hokt, hRt, hwt, hclt⟩ := tripleI_iff_run.1
      (hO.infer (d := nP + j) (i := d) hs hokd (by rw [htd]; exact hwa) (by rw [htd]; exact hcla))
      t s₂ h2
    obtain ⟨w, s₄, h4, hk4⟩ := bindI_ok hk3
    obtain ⟨hs₄, ht₄, hokw, hRw⟩ := tripleI_iff_run.1 (hO.sort hs₂ hokt hwt hclt) w s₄ h4
    rw [htd] at hRt
    have hwl : okL w = true := okL_of_okLv_level hokw
    have ht04 : TabLe s₀ s₄ := ht₂.trans ht₄
    have hrec : ∀ {s₅ : InLean.CState}, CSOKI .verified false L s₅ → TabLe s₄ s₅ →
        InLean.checkStructFieldSortsIC (sharedOpsC .verified fe) fe isProp large sr nP fvs idx j s₅ =
          .ok (u, s') →
        CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
          Runs (ConLeche.checkStructFieldSortsI (ConLeche.fueledOpsM .verified) L isProp large
            (trL sr) nP cfvs cidx j) () := by
      intro s₅ hs₅ ht₅ hk
      have ht05 := ht04.trans ht₅
      obtain ⟨hs', ht', hR⟩ := checkStructFieldSortsIFI_run hO hsr hcf j hs₅
        (okSL_of_tabLe ht05 hokf) (okSL_of_tabLe ht05 hoki) (by rw [TrSL_of_tabLe ht05 hokf, htf])
        (by rw [TrSL_of_tabLe ht05 hoki, hti]) hk
      exact ⟨hs', ht05.trans ht', hR⟩
    cases isProp with
    | false =>
      simp only [Bool.not_false, ↓reduceIte] at hk4 ⊢
      obtain ⟨b, s₆, h6, hk6⟩ := bindI_ok hk4
      obtain ⟨hs₆, ht₆, hb⟩ := tripleI_iff_run.1 (liftFueled_specI hs₄ _ _) b s₆ h6
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hk6
        obtain ⟨_, _, h7, -⟩ := bindI_ok hk6
        exact (throwI_ok h7).elim
      | true =>
        simp only [↓reduceIte] at hk6
        obtain ⟨hs', ht', hR⟩ := hrec hs₆ ht₆ hk6
        refine ⟨hs', ht', ?_⟩
        unfold ConLeche.checkStructFieldSortsI
        simp only [hca, ConLeche.unwrapOr, hfa]
        refine Runs.bind (Runs.pure _) ?_
        try dsimp only
        refine Runs.bind hRt (Runs.bind hRw ?_)
        simp only [Bool.not_false, ↓reduceIte]
        rw [leq_trL hwl hsr] at hb
        refine Runs.bind (a := true) ?_ ?_
        · rw [hb]; exact Runs.pure _
        · simpa using hR
    | true =>
      cases large with
      | false =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hk4 ⊢
        obtain ⟨hs', ht', hR⟩ := hrec hs₄ (TabLe.refl _) hk4
        refine ⟨hs', ht', ?_⟩
        unfold ConLeche.checkStructFieldSortsI
        simp only [hca, ConLeche.unwrapOr, hfa]
        refine Runs.bind (Runs.pure _) ?_
        try dsimp only
        refine Runs.bind hRt (Runs.bind hRw ?_)
        simpa using hR
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hk4 ⊢
        split at hk4
        · rename_i hc
          obtain ⟨hs', ht', hR⟩ := hrec hs₄ (TabLe.refl _) hk4
          refine ⟨hs', ht', ?_⟩
          unfold ConLeche.checkStructFieldSortsI
          simp only [hca, ConLeche.unwrapOr, hfa]
          refine Runs.bind (Runs.pure _) ?_
          try dsimp only
          refine Runs.bind hRt (Runs.bind hRw ?_)
          have hc' : (ConLeche.Level.isEquiv (trL w) .zero == some true ||
              cidx.contains (TrS s₀ a')) = true := by
            simp only [Bool.or_eq_true] at hc ⊢
            rcases hc with hc | hc
            · left; rw [isEquiv_zero_tr hwl]; exact hc
            · right
              rw [← hti]
              exact contains_TrSL hoki hoka hc
          rw [← hfa]
          simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hc']
          exact hR
        · obtain ⟨_, _, h7, -⟩ := bindI_ok hk4
          exact (throwI_ok h7).elim

/-- InLean's field loop over an array is its loop over the list. -/
theorem checkStructFieldSortsC_toArray (ops : InLean.CheckerOps) (fe : InLean.FEnv)
    (isProp large : Bool) (sr : Lean.Level) (nP : Nat) (fvs idx : List Lean.Expr) :
    ∀ j, InLean.checkStructFieldSortsC ops fe isProp large sr nP fvs.toArray idx j =
      InLean.checkStructFieldSortsIC ops fe isProp large sr nP fvs idx j
  | 0 => rfl
  | j + 1 => by
    simp only [InLean.checkStructFieldSortsC, InLean.checkStructFieldSortsIC, List.getElem?_toArray,
      checkStructFieldSortsC_toArray ops fe isProp large sr nP fvs idx j]

/-! ## One constructor -/

/-- **One constructor** (`checkSumCtorS_spec`'s twin), at master's `env₀ = env`
(the pass checks the constructors at the formers' environment on both
sides). -/
theorem checkSumCtorFI_run (hC : CheckConstantValFSimI) {fe fe₀ : InLean.FEnv} {L : ConLeche.Env}
    (hJ : JobEnvI fe L) {T : Lean.Name} {lps : List Lean.Name} {nP nIdx : Nat} {sr : Lean.Level}
    (hsr : okL sr = true) {isProp large : Bool} {cvC : Lean.ConstantVal} {nF : Nat}
    {cvTa : Lean.ConstantVal} (hokC : okC cvC.type = true) (hokT : okC cvTa.type = true)
    (hcT : (trC cvTa.type).looseBVarsBounded 0 = true)
    {s₀ s' : InLean.CState} {u : Unit} (hs : CSOKI .verified false L s₀)
    (h : InLean.checkSumCtorC (sharedOpsC .verified fe) fe₀ fe T lps nP nIdx sr isProp large cvC nF
      cvTa s₀ = .ok (u, s')) :
    CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
      Runs (ConLeche.checkSumCtor (ConLeche.fueledOpsM .verified) L L (toName T) (lps.map toName)
        nP nIdx (trL sr) isProp large (trCV cvC) nF (trCV cvTa)) () := by
  unfold InLean.checkSumCtorC at h
  obtain ⟨_, s₁, h1, h⟩ := bindI_ok h
  obtain ⟨hs₁, ht₁, hcl, hR1⟩ := hC fe L cvC s₀ s₁ hJ hs hokC h1
  have hres : (trC cvC.type).constsResolve L = true := by
    obtain ⟨F, hF⟩ := hR1
    rw [ConLeche.checkConstantVal_datF] at hF
    exact (ConLeche.checkConstantVal_typeWF hF).2.2.1
  obtain ⟨q, s₂, h2, h⟩ := bindI_ok h
  cases hsp : InLean.stripPis (nP + nF) cvC.type with
  | none => rw [hsp] at h2; exact (throwI_ok h2).elim
  | some pr =>
  obtain ⟨ds, cbody⟩ := pr
  rw [hsp] at h2
  simp only [InLean.unwrapOr] at h2
  obtain ⟨rfl, rfl⟩ := pureI_ok h2
  simp only at h
  have hokb : okC cbody = true := stripPis_okC hokC hsp
  have hsp' : (trC cvC.type).stripPis (nP + nF) = some (ds.map trC, trC cbody) := by
    rw [stripPis_tr, hsp]; rfl
  -- the declared result
  split at h
  case isFalse => obtain ⟨_, _, h', -⟩ := bindI_ok h; exact (throwI_ok h').elim
  rename_i hresid
  have hresid' : ConLeche.structCtorResidOk (toName T) (lps.map toName) nP nF nIdx (trC cbody) =
      true := by
    rw [← TrS_of_okC s₁ hokb]; exact structCtorResidOk_TrS (OkS_of_okC _ hokb) hresid
  -- the constructor's telescope
  obtain ⟨r1, s₃, h3, h⟩ := bindI_ok h
  obtain ⟨cqv, s₄, h4, h⟩ := bindI_ok h
  cases r1 with
  | none => exact (throwI_ok h4).elim
  | some cq =>
  simp only [InLean.unwrapOr] at h4
  obtain ⟨rfl, rfl⟩ := pureI_ok h4
  obtain ⟨hs₃, ht₃, hokq, hmC, hfvC⟩ := openClosedI_run hs₁ hokC hcl h3 (TabLe.refl _)
  rw [ConLeche.Cached.openPisAtFvarsC_eq] at hmC
  -- the former's telescope
  obtain ⟨r2, s₅, h5, h⟩ := bindI_ok h
  obtain ⟨tqv, s₆, h6, h⟩ := bindI_ok h
  cases r2 with
  | none => exact (throwI_ok h6).elim
  | some tq =>
  simp only [InLean.unwrapOr] at h6
  obtain ⟨rfl, rfl⟩ := pureI_ok h6
  obtain ⟨hs₅, ht₅, hokt, hmT, hfvT⟩ := openClosedI_run hs₃ hokT hcT h5 (TabLe.refl _)
  rw [ConLeche.Cached.openPisAtFvarsC_eq] at hmT
  have hokq₅ : OkSL s₅ cq.1 = true := okSL_of_tabLe ht₅ hokq
  have hTq₅ : TrSL s₅ cq.1 = TrSL s₃ cq.1 := TrSL_of_tabLe ht₅ hokq
  -- the parameter domains
  obtain ⟨dsT, s₇, h7, h⟩ := bindI_ok h
  obtain ⟨hs7, hokds, htds⟩ := mapM_fvarTypeDI_run hs₅ hokt
    (fun x hx => by
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
      exact (hfvT i x hi).1) h7
  rw [hs7] at h
  obtain ⟨_, s₈, h8, h⟩ := bindI_ok h
  obtain ⟨hs₈, ht₈, hR8⟩ := checkStructDomsAtFI_run hJ.ops
    (cfvs := TrSL s₃ cq.1) (cdoms := (TrSL s₅ tq.1).map ConLeche.Expr.fvarTypeD)
    (fun i x hx => by
      obtain ⟨h1, h2, -⟩ := hfvC i x hx
      exact ⟨h1, by rw [Nat.zero_add]; exact h2⟩)
    (fun i x hx => by
      rw [List.getElem?_map] at hx
      cases hy : (TrSL s₅ tq.1)[i]? with
      | none => rw [hy] at hx; cases hx
      | some y =>
        rw [hy] at hx
        obtain rfl := Option.some.inj hx
        obtain ⟨-, h2, h3⟩ := hfvT i y hy
        exact ⟨by rw [Nat.zero_add]; exact h2, h3⟩)
    nP hs₅ hokq₅ hokds hTq₅ htds h8
  -- the fields' telescope
  have ht38 : TabLe s₃ s₈ := ht₅.trans ht₈
  have hokb₃ : OkS s₃ cq.2 := by
    obtain ⟨-, hb, -⟩ := (openPisAtFvarsI_run nP 0 hs₁ (OkS_of_okC _ hokC)
      (by rw [TrS_of_okC _ hokC]; exact hcl) (by unfold InLean.openPisAtFvars at h3; exact h3)).2.2
      cq.1 cq.2 rfl
    exact hb
  have hclb : (TrS s₃ cq.2).looseBVarsBounded 0 = true :=
    (ConLeche.Verify.openPisAtFvars_bounded nP hmC hcl).1
  have hwb : ConLeche.Expr.WScoped nP (TrS s₃ cq.2) := by
    have := openers_body_WScoped hmC (trC_wscoped 0 _)
    rwa [Nat.zero_add] at this
  have hresb : (TrS s₃ cq.2).constsResolve L = true := (openPisAtFvars_resolve nP hmC hres).2
  obtain ⟨r3, s₉, h9, h⟩ := bindI_ok h
  obtain ⟨xqv, s₁₀, h10, h⟩ := bindI_ok h
  unfold InLean.openPisAtFvars at h9
  obtain ⟨hs₉, ht₉, hR9⟩ := openPisAtFvarsI_run nF nP hs₈ (okS_of_tabLe ht38 hokb₃)
    (by rw [TrS_of_tabLe ht38 hokb₃]; exact hclb) h9
  cases r3 with
  | none => exact (throwI_ok h10).elim
  | some xq =>
  simp only [InLean.unwrapOr] at h10
  obtain ⟨rfl, rfl⟩ := pureI_ok h10
  obtain ⟨hokx, hokxb, hmX⟩ := hR9 xq.1 xq.2 rfl
  rw [TrS_of_tabLe ht38 hokb₃] at hmX
  rw [ConLeche.Cached.openPisAtFvarsC_eq] at hmX
  have hfvX : ∀ (i : Nat) (x : ConLeche.Expr), (TrSL s₉ xq.1)[i]? = some x →
      (∃ k ty, x = .fvar k ty) ∧ ConLeche.Expr.WScoped (nP + i) x.fvarTypeD ∧
        x.fvarTypeD.looseBVarsBounded 0 = true := by
    intro i x hx
    refine ⟨?_, openers_fvarTypeD_WScoped hmX hwb hx,
      (ConLeche.Verify.openPisAtFvars_bounded nF hmX hclb).2 x (List.mem_of_getElem? hx)⟩
    obtain ⟨ty, rfl⟩ := ConLeche.openPisAtFvars_index nF _ nP hmX i x hx
    exact ⟨_, _, rfl⟩
  have hresX := openPisAtFvars_resolve nF hmX hresb
  have hokq₉ : OkSL s₉ cq.1 = true := okSL_of_tabLe (ht38.trans ht₉) hokq
  have hTq₉ : TrSL s₉ cq.1 = TrSL s₃ cq.1 := TrSL_of_tabLe (ht38.trans ht₉) hokq
  -- the opened residual
  split at h
  case isFalse => obtain ⟨_, _, h', -⟩ := bindI_ok h; exact (throwI_ok h').elim
  rename_i hres2
  simp only [Bool.and_eq_true] at hres2
  obtain ⟨⟨hr1, hr2⟩, hr3⟩ := hres2
  have hres2' : ((TrS s₉ xq.2).getAppFn ==
        ConLeche.Expr.const (toName T) ((lps.map toName).map ConLeche.Level.param) &&
      (TrS s₉ xq.2).getAppArgs.take nP == TrSL s₃ cq.1 &&
      (TrS s₉ xq.2).getAppArgs.length == nP + nIdx) = true := by
    have hf := TrS_of_clEq (OkS_getAppFnT s₉ hokxb)
      (TransS_of_ok (by simp [OkS, okE, okLv_param])) hr1
    rw [TrS_getAppFnT, TrS_const_params] at hf
    have ht := TrSL_of_beq (OkSL_take s₉ (OkSL_appArgs s₉ hokxb) nP)
      (fun b hb => TransS_of_ok (by
        simp only [OkSL, List.all_eq_true] at hokq₉; exact hokq₉ b hb)) hr2
    rw [TrSL_take, TrSL_appArgs, hTq₉] at ht
    have hn : (TrS s₉ xq.2).getAppArgs.length = nP + nIdx := by
      rw [← length_appArgs s₉ xq.2]; simpa using hr3
    simp [hf, ht, hn]
  -- the resolution guards: InLean's read no state, master's hold
  obtain ⟨fok, s₁₁, h11, h⟩ := bindI_ok h
  have hs11 : s₁₁ = s₉ := NoSt.allM (fun x => NoSt.bind (fvarTypeD_noSt x)
    fun d => constsResolveF_noSt fe₀ d) _ _ _ _ h11
  rw [hs11] at h
  split at h
  case isFalse => obtain ⟨_, _, h', -⟩ := bindI_ok h; exact (throwI_ok h').elim
  obtain ⟨iok, s₁₂, h12, h⟩ := bindI_ok h
  have hs12 : s₁₂ = s₉ := NoSt.allM (constsResolveF_noSt fe₀) _ _ _ _ h12
  rw [hs12] at h
  split at h
  case isFalse => obtain ⟨_, _, h', -⟩ := bindI_ok h; exact (throwI_ok h').elim
  have hfields : ((TrSL s₉ xq.1).all fun x => x.fvarTypeD.constsResolve L) = true := by
    simp only [List.all_eq_true]
    exact fun x hx => (hresX.1 x hx).2
  have hidx : (((TrS s₉ xq.2).getAppArgs.drop nP).all fun e => e.constsResolve L) = true := by
    simp only [List.all_eq_true]
    exact fun x hx => constsResolve_getAppArgs hresX.2 x (List.mem_of_mem_drop hx)
  -- the fields' sorts
  rw [checkStructFieldSortsC_toArray] at h
  obtain ⟨hs', ht', hR⟩ := checkStructFieldSortsIFI_run hJ.ops hsr hfvX nF hs₉ hokx
    (OkSL_drop s₉ (OkSL_appArgs s₉ hokxb) nP) rfl rfl h
  refine ⟨hs', ht₁.trans (ht₃.trans (ht38.trans (ht₉.trans ht'))), ?_⟩
  rw [TrSL_drop, TrSL_appArgs] at hR
  -- master's run
  unfold ConLeche.checkSumCtor
  refine Runs.bind hR1 ?_
  simp only [trCV_type, hsp', ConLeche.unwrapOr]
  refine Runs.bind (Runs.pure _) ?_
  simp only [hresid', ↓reduceIte, hmC, hmT]
  refine Runs.bind (Runs.pure _) (Runs.bind (Runs.pure _) (Runs.bind hR8 ?_))
  simp only [hmX]
  refine Runs.bind (Runs.pure _) ?_
  simp only [hres2', hfields, hidx, ↓reduceIte]
  exact hR

/-! ## The constructors -/

/-- **One member's constructors** (`checkSumCtorsS_spec`'s twin). -/
theorem checkSumCtorsFI_run (hC : CheckConstantValFSimI) {fe fe₀ : InLean.FEnv} {L : ConLeche.Env}
    (hJ : JobEnvI fe L) {T : Lean.Name} {lps : List Lean.Name} {nP nIdx : Nat} {sr : Lean.Level}
    (hsr : okL sr = true) {isProp large : Bool} {cvTa : Lean.ConstantVal}
    (hokT : okC cvTa.type = true) (hcT : (trC cvTa.type).looseBVarsBounded 0 = true) :
    ∀ {cs : List (Lean.ConstantVal × Nat)} {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ → (∀ c ∈ cs, okC c.1.type = true) →
      InLean.checkSumCtorsC (sharedOpsC .verified fe) fe₀ fe T lps nP nIdx sr isProp large cvTa cs s₀ =
        .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkSumCtors (ConLeche.fueledOpsM .verified) L L (toName T) (lps.map toName)
          nP nIdx (trL sr) isProp large (trCV cvTa) (cs.map trCtor)) ()
  | [], s₀, s', u, hs, _, h => by
    unfold InLean.checkSumCtorsC at h
    obtain ⟨-, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | c :: cs, s₀, s', u, hs, hok, h => by
    unfold InLean.checkSumCtorsC at h
    obtain ⟨_, s₁, h1, h⟩ := bindI_ok h
    obtain ⟨hs₁, ht₁, hR1⟩ := checkSumCtorFI_run hC hJ hsr (hok c List.mem_cons_self) hokT hcT hs h1
    obtain ⟨hs', ht', hR⟩ := checkSumCtorsFI_run hC hJ hsr hokT hcT hs₁
      (fun c' hc' => hok c' (List.mem_cons_of_mem _ hc')) h
    refine ⟨hs', ht₁.trans ht', ?_⟩
    simp only [List.map_cons]
    unfold ConLeche.checkSumCtors
    exact Runs.bind hR1 hR

theorem trShape_lps (p : InLean.BlockShape) : (trShape p).lps = p.lps.map toName := by
  unfold ConLeche.BlockShape.lps InLean.BlockShape.lps trShape
  cases p.members <;> simp [trMember]

/-- **The constructors' stage** (`checkBlockCtorsS_spec`'s twin): InLean's
run at `fe` answers master's pure `checkBlockCtors` at `L`, both at the one
environment (the pass checks the constructors at the formers'). -/
theorem checkBlockCtorsFI_run (hC : CheckConstantValFSimI) {fe fe₀ : InLean.FEnv} {L : ConLeche.Env}
    (hJ : JobEnvI fe L) {p : InLean.BlockShape} (hsr : okL p.resSort = true) :
    ∀ {l : List InLean.MemberShape} {s₀ s' : InLean.CState} {u : Unit},
      CSOKI .verified false L s₀ →
      (∀ ms ∈ l, okC ms.cvT.type = true ∧ (trC ms.cvT.type).looseBVarsBounded 0 = true ∧
        ∀ c ∈ ms.ctors, okC c.1.type = true) →
      InLean.checkBlockCtorsC (sharedOpsC .verified fe) fe₀ fe p l s₀ = .ok (u, s') →
      CSOKI .verified false L s' ∧ TabLe s₀ s' ∧
        Runs (ConLeche.checkBlockCtors (ConLeche.fueledOpsM .verified) L L (trShape p)
          (l.map trMember)) ()
  | [], s₀, s', u, hs, _, h => by
    unfold InLean.checkBlockCtorsC at h
    obtain ⟨-, rfl⟩ := pureI_ok h
    exact ⟨hs, TabLe.refl _, Runs.pure _⟩
  | ms :: rest, s₀, s', u, hs, hok, h => by
    unfold InLean.checkBlockCtorsC at h
    obtain ⟨hk1, hk2, hk3⟩ := hok ms List.mem_cons_self
    obtain ⟨_, s₁, h1, h⟩ := bindI_ok h
    obtain ⟨hs₁, ht₁, hR1⟩ := checkSumCtorsFI_run hC hJ hsr hk1 hk2 hs hk3 h1
    obtain ⟨hs', ht', hR⟩ := checkBlockCtorsFI_run hC hJ hsr hs₁
      (fun m hm => hok m (List.mem_cons_of_mem _ hm)) h
    refine ⟨hs', ht₁.trans ht', ?_⟩
    simp only [List.map_cons]
    unfold ConLeche.checkBlockCtors
    rw [trShape_lps]
    exact Runs.bind hR1 hR

end InLeanProof
