import Setlec.SetR.Bridge.Main
import Setlec.SetR.Install.Step
import Setlec.Verify.IotaWalkInv
import Setlec.Verify.Extend.Iota
import Setlec.Verify.Denote.IndFrame
import Setlec.Verify.Extend.Proj
import Setlec.Verify.NatOpFrag
import Setlec.Verify.ReducePinInv
import Setlec.Verify.DivModInv

/-!
# The declaration-level bridge (task #148, T6)

`Setlec/SetR/Bridge/*` bridges the checker's *inference* steps into the
`[set]` relation family; this file bridges its **declarations**.  Each
of `checkDecl`'s six branches is inverted into the corresponding
`Decl*R` clause of `Setlec/SetR/Decl.lean`, and `checkDeclR_of`
assembles them.  Composed with `declStepS` (`Install/Step.lean`) that
gives the `EnvS`-extension step the consistency fold runs.

Nothing semantic happens here: every lemma is V-free inversion of the
checker's own control flow.  The valuation enters only where a clause
mentions `cval`, and there it is carried, never chosen.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify SetTheory

universe w

/-! ## `EnvS` is an `EnvR`

The bridge runs against `EnvR` — the weakest V-free invariant its
steps need — and the install layer produces `EnvS`.  The assembly
needs the projection, and building it is what exposed **finding 7**
(recorded in `DESIGN.md`): as landed, two of `EnvR`'s fields were
stated more strongly than `EnvS.rec_rules` can supply.

`EnvS.rec_rules` is `RecRulesV`, which speaks only of rules whose
`fire ≠ .inert` and only at level arguments of the declared length;
`EnvR.rec_rhs_denotes`/`rec_params_le` quantified over *all* rules and
*all* level lists.  The gap is not cosmetic: `Empty.rec` stores **no
rules at all**, so no install could ever supply an unguarded
`rP ≤ mI`, and adding an unguarded `EnvS` field would have been owed
by every install for a fact the bridge never uses.  Both fields are
consumed at exactly one place — the iota fire site in
`Bridge/Iota.lean` — where the fired rule, its non-inertness (`hfire`)
and the level-length check (`hlenU`) are all already in scope.  The
repair is therefore to narrow the fields to their consumption, which
is what `Bridge/Env.lean` now states. -/

/-- **The bridge invariant, from the install invariant.** -/
def EnvS.toEnvR {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) : EnvR env where
  cval := m.cval
  cval_closed := m.cval_closed
  wf := m.wf
  val_params := m.val_params
  ty_denotes := fun c hc ψ => by
    obtain ⟨t, ht, -⟩ := m.mem_type c hc ψ
    exact ⟨t, ht⟩
  defn_eq := m.defn_eq
  rec_rhs_denotes := fun n cv mI rP rules hf r hr hfire us ψ hlen => by
    obtain ⟨-, hR⟩ := m.rec_rules ψ n cv mI rP rules hf r hr hfire
    obtain ⟨R, hR0, -⟩ := hR us hlen
    exact ⟨R, hR0⟩
  rec_params_le := fun n cv mI rP rules hf r hr hfire =>
    (m.rec_rules (fun _ => 0) n cv mI rP rules hf r hr hfire).1
  proj_ok := m.proj_ok
  thm_ok := m.thm_ok

/-! ## The shared front doors

`ConstantValR` and `ValueFrontR` are the two relations four of the six
branches are built from, and neither had a producer.  Both are the
same script: `checkConstantVal_inv` (or the branch's own `annotate`
inversion) for the syntactic conjuncts, then `checkBridge` at
`EnvS.toEnvR` for the `Infer`/`DefEq` ones, at an **arbitrary** `φ` —
which is what both relations quantify over. -/

/-- The frame conditions of a closed, `fvar`-free expression at depth
`0` — the shape every declaration-level claim is applied at ([set]
transpose of the TT lane's `closed0_frames`). -/
theorem closed0_framesR {μ : CheckMode} {cval : TConstVal} {env : Env}
    {φ : Name → Nat} {e : Expr} (hnf : e.hasFvar = false)
    (hb : e.looseBVarsBounded 0 = true) :
    Expr.WScoped 0 e ∧ e.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e ∧ CtxOkR μ cval env φ 0 [] e :=
  ⟨Expr.WScoped.of_not_hasFvar hnf, hb,
    Expr.LeavesBounded.of_not_hasFvar hnf,
    CtxOkR.nil (Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf)⟩

/-- **`checkConstantVal`, bridged.**  Beside `ConstantValR` the caller
gets the annotated type's two closedness facts, which every branch
then needs for its own value front door and for `EnvWF`. -/
theorem constantValR_of {env : Env} (m : EnvR env) {μ : CheckMode} {F :
  Nat} {cv cv' : ConstantVal}
    (h : checkConstantVal (fueledOps μ F) env cv = .ok cv') :
    ∃ type', cv' = { cv with type := type' } ∧
      type'.hasFvar = false ∧ type'.looseBVarsBounded 0 = true ∧
      ConstantValR μ F env m.cval cv type' := by
  obtain ⟨hfind, hres, hpsh, hnd, hlbt, hitf, type, stype, u, hann, htp,
    htr, hst, hsort, rfl⟩ := checkConstantVal_inv h
  have htf : type.hasFvar = false :=
    Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F cv.type hann
        (Expr.WScoped.of_not_hasFvar hitf)).fvarsBelow)
  have hbt' : type.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F cv.type hann hlbt
  refine ⟨type, rfl, htf, hbt',
    Option.isNone_iff_eq_none.mpr hfind, hres, hpsh, hnd, hlbt, hitf,
    hann, htp, htr, ⟨stype, u, hst, hsort⟩, fun φ => ?_⟩
  obtain ⟨-, ihw, -, ihi⟩ := checkBridge m φ F
  obtain ⟨hwt, hbt, hLt, hCt⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      htf hbt'
  obtain ⟨Tv, tv, hTv, htv, T', hI, hD⟩ := ihi hst hwt hbt hLt hCt
  obtain ⟨hws, hbs, hLs, hCs⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      (Expr.not_hasFvar_of_fvarsBelow_zero
        (inferTypeCore_WScoped m.wf F hst hwt).fvarsBelow)
      (inferTypeCore_looseBVars m.wf F hst hwt hbt hLt)
  obtain ⟨sv, hsv, hRed⟩ :=
    ihw (ensureSortCore_inv hsort) hws hbs hLs hCs htv
  rw [denote_sort] at hsv
  obtain rfl := (Option.some.inj hsv).symm
  exact ⟨Tv, T', u.eval φ, hTv, hI, DefEq.trans hD (DefEq.ofRed hRed)⟩

/-- **The value front door, bridged** — the [set] transpose of the TT
lane's `value_key`, in the relation's own vocabulary: `Infer` of the
value's denotation up to `DefEq`, then the checker's own
`vtype ≡ type` verdict composed on. -/
theorem valueFrontR_of {env : Env} (m : EnvR env) {μ : CheckMode} {F :
  Nat} {cv : ConstantVal}
    {value type' value' vtype : Expr}
    (htf : type'.hasFvar = false)
    (hbt' : type'.looseBVarsBounded 0 = true)
    (hlbv : value.looseBVarsBounded 0 = true)
    (hivf : value.hasFvar = false)
    (hannv : annotateCore μ env F 0 value = .ok value')
    (hvp : value'.allLevelParamsDefined cv.levelParams = true)
    (hvr : value'.constsResolve env = true)
    (hvt : inferTypeCore μ env F 0 value' = .ok vtype)
    (hde : isDefEqCore μ env F 0 vtype type' = .ok true)
    (hcv : ConstantValR μ F env m.cval cv type') :
    ValueFrontR μ F env m.cval cv value type' value' := by
  refine ⟨hlbv, hivf, hannv, hvp, hvr, ⟨vtype, hvt, hde⟩, fun φ => ?_⟩
  obtain ⟨-, -, ihd, ihi⟩ := checkBridge m φ F
  have hvf' : value'.hasFvar = false :=
    Expr.not_hasFvar_of_fvarsBelow_zero
      ((annotateCore_WScoped F value hannv
        (Expr.WScoped.of_not_hasFvar hivf)).fvarsBelow)
  have hbv' : value'.looseBVarsBounded 0 = true :=
    annotateCore_looseBVars F value hannv hlbv
  obtain ⟨hwv, hbv, hLv, hCv⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      hvf' hbv'
  obtain ⟨hwt, hbt, hLt, hCt⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      htf hbt'
  obtain ⟨Vv, vt, hVv, hvt', T', hI, hD⟩ := ihi hvt hwv hbv hLv hCv
  obtain ⟨Tv, -, -, hTv, -, -⟩ :=
    hcv.2.2.2.2.2.2.2.2.2.2 φ
  obtain ⟨hwvt, hbvt, hLvt, hCvt⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      (Expr.not_hasFvar_of_fvarsBelow_zero
        (inferTypeCore_WScoped m.wf F hvt hwv).fvarsBelow)
      (inferTypeCore_looseBVars m.wf F hvt hwv hbv hLv)
  exact ⟨Tv, Vv, T', hTv, hVv, hI,
    DefEq.trans hD
      (ihd hde hwvt hbvt hLvt hwt hbt hLt hCvt hCt hvt' hTv)⟩

/-! ## `thmDecl`

The value front doors plus one extra: the type's sort is `Prop`.  The
checker states that as `Level.isEquiv u .zero`; the relation states it
as `DefEq … sT (.sort 0)`, and `Level.isEquiv_sound` is the whole
distance between them. -/

/-- **The depth crossing.**  `openPisAtFvars` delivers the `i`-th
opener's annotation denoted at *its own* depth `i`; every statement
walk runs at the opening depth (`rP + cnF`).  `denote_lift` crosses
the gap, and this is the form the walks consume it in — definedness
only, since `DefEqAtW` names the value existentially. -/
theorem opener_denotes_at {env : Env} (m : EnvR env) {φ : Name → Nat}
    {i D : Nat} {e : Expr} {v : VExpr}
    (hfb : Expr.fvarsBelow i e) (hle : i ≤ D)
    (h : denote m.cval env φ i e = some v) :
    ∃ w, denote m.cval env φ D e = some w := by
  refine ⟨VExpr.liftN (D - i) v 0, ?_⟩
  rw [denote_lift m.cval_closed hfb D hle, h]
  rfl

/-- The frame package one side of a certified `Nat` recurrence needs:
the three syntactic facts, the `Nat`-annotated-leaf shape that the
canonical context matches, and the denotation. -/
def NatEqFrameR (cval : TConstVal) (env : Env) (e : Expr) : Prop :=
  Expr.WScoped 2 e ∧ e.looseBVarsBounded 0 = true ∧
  Expr.LeavesBounded e ∧
  (∀ l ∈ e.fvarLeaves, l.1 < 2 ∧ l.2.2 = .const natName []) ∧
  ∀ φ : Name → Nat, ∃ v, denote cval env φ 2 e = some v

/-- **`certifyNatEqs`, bridged.**  The verdict is `isDefEqCore` at
depth `2` on each pair; `DefEqClaimsR` turns it into the relation
family's `DefEq` once both sides have a frame package and a context.
The context is `CtxOkR.constCtx` at the pinned `Nat` entries — which
is exactly what the leaf-shape conjunct of `NatEqFrameR` is for. -/
theorem natEqsBridge_of {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) {μ : CheckMode}
    {F : Nat} {ciN : ConstantInfo}
    (hnatE : env.find? natName = some ciN)
    (hnatL : ciN.toConstantVal.levelParams = [])
    : ∀ (eqs : List (Expr × Expr)),
      (∀ eq ∈ eqs, NatEqFrameR m.cval env eq.1 ∧
        NatEqFrameR m.cval env eq.2) →
      certifyNatEqs (m := CheckM) (fueledOps μ F) env eqs = .ok true →
      NatEqsR μ env m.cval eqs := by
  have hden : ∀ φ : Name → Nat, ∀ d : Nat,
      denote m.cval env φ d (.const natName [])
        = some (natVR m.cval φ) := by
    intro φ d
    rw [denote_const, hnatE]
    dsimp only
    rw [if_pos (by rw [hnatL]; rfl), hnatL]
    rfl
  intro eqs
  induction eqs with
  | nil => intro _ _ eq heq; exact nomatch heq
  | cons e rest ih =>
    intro hfr h eq heq φ
    simp only [certifyNatEqs, fueledOps_isDefEq, Bind.bind,
      Except.bind] at h
    by_cases hde : isDefEqCore μ env F 2 e.1 e.2 = .ok true
    case neg =>
      exfalso
      cases hx : isDefEqCore μ env F 2 e.1 e.2 with
      | error err => rw [hx] at h; exact nomatch h
      | ok b =>
        cases b with
        | true => exact hde hx
        | false =>
          rw [hx] at h
          simp only [Bool.false_eq_true, if_false, pure, Except.pure,
            Except.ok.injEq] at h
    rcases List.mem_cons.mp heq with rfl | heq'
    · obtain ⟨⟨hw1, hb1, hL1, hl1, hd1⟩, ⟨hw2, hb2, hL2, hl2, hd2⟩⟩ :=
        hfr eq List.mem_cons_self
      obtain ⟨L, hL⟩ := hd1 φ
      obtain ⟨R, hR⟩ := hd2 φ
      refine ⟨L, R, hL, hR, ?_⟩
      obtain ⟨-, -, ihd, -⟩ := checkBridge m.toEnvR φ F
      have hC1 : CtxOkR μ m.cval env φ 2
          (List.replicate 2 (natVR m.cval φ)) eq.1 :=
        CtxOkR.constCtx (m.cval_closed _ _) (hden φ 2) trivial hl1
      have hC2 : CtxOkR μ m.cval env φ 2
          (List.replicate 2 (natVR m.cval φ)) eq.2 :=
        CtxOkR.constCtx (m.cval_closed _ _) (hden φ 2) trivial hl2
      have := ihd hde hw1 hb1 hL1 hw2 hb2 hL2 hC1 hC2 hL hR
      exact this
    · rw [hde] at h
      simp only [if_true] at h
      exact ih (fun q hq => hfr q (List.mem_cons_of_mem _ hq)) h eq
        heq' φ

/-- **The fragment gives the frame package**, in one induction over
`natFragOk`'s four constructors.  The operation `c` is the one being
defined, so it is *not* stored: its occurrences are the ones
`substConst0` replaces, and the substituted value's own facts stand in
for them. -/
theorem natEqFrame_of_frag {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) {c : Name}
    {v : Expr} (hvf : v.hasFvar = false)
    (hvb : v.looseBVarsBounded 0 = true)
    (hvd : ∀ φ : Name → Nat, ∃ V0, denote m.cval env φ 0 v = some V0) :
    ∀ {e : Expr}, natFragOk env c e = true →
      NatEqFrameR m.cval env (Expr.substConst0 c v e)
  | .sort u, _ => by
    rw [show Expr.substConst0 c v (Expr.sort u) = Expr.sort u from rfl]
    refine ⟨by rw [Expr.WScoped]; trivial, rfl, ?_, ?_,
      fun φ => ⟨_, by rw [denote_sort]⟩⟩
    · intro l hl; simp [Expr.fvarLeaves] at hl
    · intro l hl; simp [Expr.fvarLeaves] at hl
  | .fvar i n ty, h => by
    simp only [natFragOk, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨hi, rfl⟩ := h
    have hilt : i < 2 := by rcases hi with rfl | rfl <;> omega
    rw [show Expr.substConst0 c v (Expr.fvar i n (.const natName []))
      = Expr.fvar i n (.const natName []) from rfl]
    refine ⟨?_, rfl, ?_, ?_, fun φ => ⟨_, by rw [denote_fvar]⟩⟩
    · rw [Expr.WScoped]
      exact ⟨hilt, by rw [Expr.WScoped]; trivial⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · rfl
      · simp [Expr.fvarLeaves] at hl'
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact ⟨hilt, rfl⟩
      · simp [Expr.fvarLeaves] at hl'
  | .const n us, h => by
    rw [show Expr.substConst0 c v (Expr.const n us)
      = (if n = c ∧ us = [] then v else Expr.const n us) from rfl]
    by_cases hn : n = c ∧ us.isEmpty = true
    · rw [if_pos (show n = c ∧ us = [] from
        ⟨hn.1, List.isEmpty_iff.mp hn.2⟩)]
      refine ⟨Expr.WScoped.mono (Nat.zero_le 2)
          (Expr.WScoped.of_not_hasFvar hvf), hvb,
        Expr.LeavesBounded.of_not_hasFvar hvf, ?_, fun φ => ?_⟩
      · intro l hl
        rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvf] at hl
        exact nomatch hl
      · obtain ⟨V0, hV0⟩ := hvd φ
        exact opener_denotes_at m.toEnvR
          (Expr.WScoped.of_not_hasFvar hvf).fvarsBelow
          (Nat.zero_le 2) hV0
    · rw [if_neg (fun hh => hn ⟨hh.1, by rw [hh.2]; rfl⟩)]
      simp only [natFragOk, Bool.or_eq_true, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rcases h with h' | h'
      · exact absurd h' hn
      · refine ⟨by rw [Expr.WScoped]; trivial, rfl, ?_, ?_,
          fun φ => ?_⟩
        · intro l hl; simp [Expr.fvarLeaves] at hl
        · intro l hl; simp [Expr.fvarLeaves] at hl
        revert h'
        cases hf : env.find? n with
        | none => intro hx; exact nomatch hx
        | some ci =>
          intro hx
          refine ⟨m.cval n (Level.substFn φ
            ci.toConstantVal.levelParams us), ?_⟩
          rw [denote_const, hf]
          dsimp only
          rw [if_pos (by simpa using hx)]
  | .app f a, h => by
    simp only [natFragOk, Bool.and_eq_true] at h
    obtain ⟨hwf, hbf, hLf, hlf, hdf⟩ :=
      natEqFrame_of_frag m hvf hvb hvd h.1
    obtain ⟨hwa, hba, hLa, hla, hda⟩ :=
      natEqFrame_of_frag m hvf hvb hvd h.2
    rw [show Expr.substConst0 c v (Expr.app f a)
      = Expr.app (Expr.substConst0 c v f) (Expr.substConst0 c v a)
      from rfl]
    refine ⟨by rw [Expr.WScoped]; exact ⟨hwf, hwa⟩, ?_, ?_, ?_,
      fun φ => ?_⟩
    · simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hbf, hba⟩
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h' | h'
      · exact hLf l h'
      · exact hLa l h'
    · intro l hl
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h' | h'
      · exact hlf l h'
      · exact hla l h'
    · obtain ⟨vf, hvf'⟩ := hdf φ
      obtain ⟨va, hva'⟩ := hda φ
      exact ⟨_, by rw [denote_app, hvf', hva']⟩
  | .bvar _, h | .lam _ _ _ _, h | .forallE _ _ _ _, h
  | .letE _ _ _ _, h | .proj _ _ _, h | .lit _, h => by
    simp [natFragOk] at h

/-- **`certifyNatEqs`, discharged.**  The obligation `declDefnR` used
to carry: the guard pins every constant the fragment admits, the
fragment gives each substituted side its frame package, and
`natEqsBridge_of` turns the verdicts into `NatEqsR`.  The descent from
the post-insertion guard to the pre-insertion environment is
`storedNoLevels_of_cons` at names `ne_of_mem_natOpNames` separates
from the operation — the TT lane's `natOpPinTT` runs the same block. -/
theorem natEqsR_of_certs {V : Type w} [SetTheory V] {env : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
    {value' : Expr} {hint : ReducibilityHint}
    (hmem : cv.name ∈ natOpNames)
    (hvf : value'.hasFvar = false)
    (hbv : value'.looseBVarsBounded 0 = true)
    (hden : ∀ φ : Name → Nat,
      ∃ V0, denoteClosed m.cval env φ value' = some V0)
    (hguard : natOpGuard
      ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ cv.name
      = true)
    (hcerts : certifyNatEqs (m := CheckM) (fueledOps μ F) env
      ((natOpEquations 0 cv.name).map fun eq =>
        (Expr.substConst0 cv.name value' eq.1,
         Expr.substConst0 cv.name value' eq.2)) = .ok true) :
    NatEqsR μ env m.cval ((natOpEquations 0 cv.name).map fun eq =>
      (Expr.substConst0 cv.name value' eq.1,
       Expr.substConst0 cv.name value' eq.2)) := by
  obtain ⟨hN', hz', hs', hdeps', hbool'⟩ := natOpGuard_stored hguard
  have tr : ∀ {n : Name}, n ≠ cv.name →
      storedNoLevels
        ⟨ConstantInfo.defnInfo cv value' hint :: env.consts⟩ n →
      storedNoLevels env n := fun hne h =>
    storedNoLevels_of_cons (ci := .defnInfo cv value' hint)
      (c := cv.name) rfl hne h
  have hnN : natName ≠ cv.name := ne_of_mem_natOpNames (by decide) hmem
  have hnz : natZeroName ≠ cv.name :=
    ne_of_mem_natOpNames (by decide) hmem
  have hns : natSuccName ≠ cv.name :=
    ne_of_mem_natOpNames (by decide) hmem
  have hnT : boolTrueName ≠ cv.name :=
    ne_of_mem_natOpNames (by decide) hmem
  have hnF : boolFalseName ≠ cv.name :=
    ne_of_mem_natOpNames (by decide) hmem
  obtain ⟨ciN, hfN, hlpN⟩ := storedNoLevels_exists (tr hnN hN')
  refine natEqsBridge_of m hfN hlpN _ (fun eq hq => ?_) hcerts
  obtain ⟨eq0, hq0, rfl⟩ := List.mem_map.mp hq
  obtain ⟨hf1, hf2⟩ := natOpEquations_frag (env := env) (c := cv.name)
    (tr hnz hz') (tr hns hs') (fun n hn hne => tr hne (hdeps' n hn))
    (fun hc => tr hnT (hbool' (by
      rcases hc with h | h <;> rw [h] <;> simp)).1)
    (fun hc => tr hnF (hbool' (by
      rcases hc with h | h <;> rw [h] <;> simp)).2) eq0 hq0
  have hden0 : ∀ φ : Name → Nat,
      ∃ V0, denote m.cval env φ 0 value' = some V0 := hden
  exact ⟨natEqFrame_of_frag m hvf hbv hden0 hf1,
    natEqFrame_of_frag m hvf hbv hden0 hf2⟩

/-- **`checkReducePin`, discharged.**  The obligation `declOpaqueR`
used to carry.  The element type is a stored level-free constant, so
it denotes to the pinned valuation and the certificate's context is
`CtxOkR.constCtx` at one entry; `DefEqClaimsR` then transports the
depth-`1` identity verdict. -/
theorem reducePinR_of {V : Type w} [SetTheory V] {env env' : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {c : Name}
    {value : Expr}
    (hvfacts : ∀ a : Expr, annotateCore μ env F 0 value = .ok a →
      a.hasFvar = false ∧ a.looseBVarsBounded 0 = true ∧
      ∀ φ : Name → Nat, ∃ V0, denoteClosed m.cval env φ a = some V0)
    (h : checkReducePin (m := CheckM) (fueledOps μ F) env env' c value
      = .ok ()) :
    ReducePinR μ F env env' m.cval c value := by
  obtain ⟨hstored, helem, hpg, valA, pinA, hva, hpa, hp1, hp2⟩ :=
    checkReducePin_inv h
  obtain ⟨hvAf, hvAb, hvden⟩ := hvfacts valA hva
  obtain ⟨ciE, hfE, hlpE⟩ := reduceElem_shape helem
  have hEty : reduceElemTy c = .const (reduceElemName c) [] := by
    unfold reduceElemTy reduceElemName
    split <;> rfl
  refine ⟨hstored, helem, hpg, valA, pinA, hva, hpa, fun φ => ?_⟩
  -- the element type denotes to the pinned valuation, at any depth
  have hE : ∀ d, denote m.cval env φ d (reduceElemTy c)
      = some (m.cval (reduceElemName c) φ) := by
    intro d
    rw [hEty, denote_const, hfE]
    dsimp only
    rw [if_pos (by rw [hlpE]; rfl), hlpE]
    rfl
  obtain ⟨V0, hV0⟩ := hvden φ
  have hV0d : ∀ d, denote m.cval env φ d valA = some V0 :=
    (denote_closedExprR m.cval_closed hvAf hvAb hV0).2
  refine ⟨_, V0, hE 0, hV0, ?_⟩
  obtain ⟨-, -, ihd, -⟩ := checkBridge m.toEnvR φ F
  -- the certificate variable and the two compared sides
  have hcv : reduceCertVar c
      = Expr.fvar 0 (.str .anonymous "a") (.const (reduceElemName c) []) := by
    rw [reduceCertVar, hEty]
  have hnil : (Expr.const (reduceElemName c) []).fvarLeaves = [] :=
    Expr.fvarLeaves_eq_nil_of_not_hasFvar rfl
  have hxleaf : ∀ l ∈ (reduceCertVar c).fvarLeaves,
      l.1 < 1 ∧ l.2.2 = reduceElemTy c := by
    intro l hl
    rw [hcv, Expr.fvarLeaves] at hl
    rcases List.mem_cons.mp hl with rfl | hl'
    · exact ⟨by omega, hEty.symm⟩
    · rw [hnil] at hl'
      exact nomatch hl'
  have hCx : CtxOkR μ m.cval env φ 1
      (List.replicate 1 (m.cval (reduceElemName c) φ))
      (reduceCertVar c) :=
    CtxOkR.constCtx (m.cval_closed _ _) (hE 1)
      (by rw [hEty]; trivial) hxleaf
  have hCap : CtxOkR μ m.cval env φ 1
      (List.replicate 1 (m.cval (reduceElemName c) φ))
      (.app valA (reduceCertVar c)) := by
    refine ⟨hCx.1, fun l hl => ?_⟩
    rw [Expr.fvarLeaves] at hl
    rcases List.mem_append.mp hl with h' | h'
    · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvAf] at h'
      exact nomatch h'
    · exact hCx.2 l h'
  have hdx : denote m.cval env φ 1 (reduceCertVar c)
      = some (.bvar 0) := by
    rw [hcv, denote_fvar]
  have hdap : denote m.cval env φ 1 (.app valA (reduceCertVar c))
      = some (.app V0 (.bvar 0)) := by
    rw [denote_app, hV0d 1, hdx]
  exact ihd hp2
    (by
      rw [Expr.WScoped]
      refine ⟨Expr.WScoped.mono (Nat.zero_le 1)
        (Expr.WScoped.of_not_hasFvar hvAf), ?_⟩
      rw [hcv, Expr.WScoped]
      exact ⟨by omega, by rw [Expr.WScoped]; trivial⟩)
    (by
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hvAb, rfl⟩)
    (fun l hl => by
      rw [Expr.fvarLeaves] at hl
      rcases List.mem_append.mp hl with h' | h'
      · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hvAf] at h'
        exact nomatch h'
      · rw [hcv, Expr.fvarLeaves] at h'
        rcases List.mem_cons.mp h' with rfl | h''
        · rfl
        · rw [hnil] at h''; exact nomatch h'')
    (by rw [hcv, Expr.WScoped]
        exact ⟨by omega, by rw [Expr.WScoped]; trivial⟩)
    rfl
    (fun l hl => by
      rw [hcv, Expr.fvarLeaves] at hl
      rcases List.mem_cons.mp hl with rfl | hl'
      · rfl
      · rw [hnil] at hl'; exact nomatch hl')
    hCap hCx hdap hdx

/-- **`checkDivModPin`, discharged.**  With the certificate list
entering as the checker's own verdict, the whole pack is
`checkDivModPin_inv`'s output re-associated: the guards, the pin
annotate, and the certs run.  The stored value the pack is about is
the one `env'` holds, which the inversion produces — that is the
`v`-freeness repair's supplier. -/
theorem divModPinR_of {V : Type w} [SetTheory V] {env env' : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {c : Name}
    {cv0 : ConstantVal} {v : Expr} {hint0 : ReducibilityHint}
    (hstore : env'.find? c = some (.defnInfo cv0 v hint0))
    (h : checkDivModPin (m := CheckM) (fueledOps μ F) env env' c
      = .ok ()) :
    DivModPinR μ F env env' m.cval c v := by
  obtain ⟨henv, cv', value', hint', hfind, hguards, ⟨pinA, hpa, -⟩,
    hcerts⟩ := checkDivModPin_inv h
  obtain rfl : value' = v := by
    rw [hstore] at hfind
    exact (ConstantInfo.defnInfo.inj (Option.some.inj hfind)).2.1.symm
  obtain ⟨hpin, hcertsG⟩ := by
    simpa only [Bool.and_eq_true] using hguards
  exact ⟨henv, hpin, hcertsG, pinA, hpa, hcerts⟩

/-- **`thmDecl`, bridged.** -/
theorem declThmR {V : Type w} [SetTheory V] {env env₂ : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
    {value : Expr}
    (h : checkDecl μ (fueledOps μ F) env (.thmDecl cv value)
      = .ok env₂) :
    DeclThmR μ F env m.cval cv value env₂ := by
  simp only [checkDecl, checkThmVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, fueledOps_ensureSort,
    Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, htf, hbt', hcv⟩ := constantValR_of m.toEnvR hccv
  simp only [Pure.pure, Except.pure] at h
  cases hst2 : inferTypeCore μ env F 0 type with
  | error e => rw [hst2] at h; exact nomatch h
  | ok stype2 =>
  rw [hst2] at h
  try dsimp only at h
  cases hsort2 : ensureSortCore μ env F 0 stype2 with
  | error e => rw [hsort2] at h; exact nomatch h
  | ok u2 =>
  rw [hsort2] at h
  try dsimp only at h
  cases hpz : Level.isEquiv u2 Level.zero with
  | none => rw [hpz] at h; simp [liftFueled] at h
  | some bz =>
  rw [hpz] at h
  cases bz with
  | false => simp [liftFueled, pure, Except.pure] at h
  | true =>
  simp only [liftFueled, pure, Except.pure] at h
  try dsimp only at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  cases hannv : annotateCore μ env F 0 value with
  | error e => rw [hannv] at h; exact nomatch h
  | ok value' =>
  rw [hannv] at h
  try dsimp only at h
  by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value'.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  cases hvt : inferTypeCore μ env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore μ env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
  refine ⟨type, value', hcv, fun φ => ?_,
    valueFrontR_of m.toEnvR htf hbt' hlbv hivf' hannv hvp hvr hvt hde
      hcv,
    h.symm⟩
  obtain ⟨-, ihw, -, ihi⟩ := checkBridge m.toEnvR φ F
  obtain ⟨hwt, hbt, hLt, hCt⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      htf hbt'
  obtain ⟨Tv, tv2, hTv, htv2, T', hI, hD⟩ := ihi hst2 hwt hbt hLt hCt
  obtain ⟨hws, hbs, hLs, hCs⟩ :=
    closed0_framesR (μ := μ) (cval := m.cval) (env := env) (φ := φ)
      (Expr.not_hasFvar_of_fvarsBelow_zero
        (inferTypeCore_WScoped m.wf F hst2 hwt).fvarsBelow)
      (inferTypeCore_looseBVars m.wf F hst2 hwt hbt hLt)
  obtain ⟨sv, hsv, hRed⟩ :=
    ihw (ensureSortCore_inv hsort2) hws hbs hLs hCs htv2
  rw [denote_sort, Level.isEquiv_sound hpz φ] at hsv
  obtain rfl := (Option.some.inj hsv).symm
  exact ⟨Tv, T', hTv, hI, DefEq.trans hD (DefEq.ofRed hRed)⟩

/-! ## `axiomDecl`

A pure dispatch on Boolean shape gates: the two standard axioms, the
compiler-trust family, and the tolerated skip.  Nothing semantic
happens past `ConstantValR` — the axioms' *content* is the install
layer's `StdAxiomKeyS`/`OfReduceKeyS`, not the bridge's. -/

/-- **`axiomDecl`, bridged.** -/
theorem declAxiomR {V : Type w} [SetTheory V] {env env₂ : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
    (h : checkDecl μ (fueledOps μ F) env (.axiomDecl cv) = .ok env₂) :
    DeclAxiomR μ F env m.cval cv env₂ := by
  simp only [checkDecl, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cvA =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, -, -, hcv⟩ := constantValR_of m.toEnvR hccv
  refine ⟨type, hcv, ?_⟩
  by_cases hstd : stdAxiomOk env { cv with type := type } = true
  · rw [if_pos hstd] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    exact Or.inl ⟨hstd, h.symm⟩
  rw [if_neg hstd] at h
  have hstdF : stdAxiomOk env { cv with type := type } = false := by
    revert hstd; cases stdAxiomOk env { cv with type := type } <;> simp
  by_cases htc : cv.name = trustCompilerName
  · rw [if_pos htc] at h
    by_cases htco : trustCompilerOk env { cv with type := type } = true
    · rw [if_pos htco] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr (Or.inl ⟨htc, htco, h.symm⟩)
    · rw [if_neg htco] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg htc] at h
  by_cases hofr : cv.name = ofReduceNatName ∨ cv.name = ofReduceBoolName
  · rw [if_pos hofr] at h
    by_cases hofro : ofReduceAxOk env { cv with type := type } = true
    · rw [if_pos hofro] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h
      exact Or.inr (Or.inr (Or.inl ⟨hofr, hofro, h.symm⟩))
    · rw [if_neg hofro] at h
      simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg hofr] at h
  by_cases hpc : cv.name = propextName ∨ cv.name = choiceName
  · rw [if_pos hpc] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg hpc] at h
  by_cases htol : toleratedAxiomNames.contains cv.name = true
  · rw [if_pos htol] at h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    refine Or.inr (Or.inr (Or.inr ⟨hstdF, htc, ?_, ?_, ?_, ?_, htol,
      h.symm⟩))
    · exact fun hh => hofr (Or.inl hh)
    · exact fun hh => hofr (Or.inr hh)
    · exact fun hh => hpc (Or.inl hh)
    · exact fun hh => hpc (Or.inr hh)
  · rw [if_neg htol] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## `opaqueDecl` and `defnDecl`

The same value front doors, and then each kind's own conditional pin
pack.  Those packs are taken as **parameters** here, exactly as the TT
lane parameterises `declDefnTT` on `NatOpPinTT`/`DivModPinTT`: each is
its own inversion of its own checker routine, and keeping them out of
the branch script is what stops the branch from growing a second
subject. -/

/-- **`opaqueDecl`, bridged**, parametric in the compiler-trust pin's
own inversion. -/
theorem declOpaqueR {V : Type w} [SetTheory V] {env env₂ : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
    {value : Expr}
    (h : checkDecl μ (fueledOps μ F) env (.opaqueDecl cv value)
      = .ok env₂) :
    DeclOpaqueR μ F env m.cval cv value env₂ := by
  simp only [checkDecl, checkOpaqueVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, htf, hbt', hcv⟩ := constantValR_of m.toEnvR hccv
  simp only [Pure.pure, Except.pure] at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  cases hannv : annotateCore μ env F 0 value with
  | error e => rw [hannv] at h; exact nomatch h
  | ok value' =>
  rw [hannv] at h
  try dsimp only at h
  by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value'.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  cases hvt : inferTypeCore μ env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore μ env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  refine ⟨type, value', hcv,
    valueFrontR_of m.toEnvR htf hbt' hlbv hivf' hannv hvp hvr hvt hde
      hcv,
    ?_, ?_⟩
  · by_cases hro : reduceOpNames.contains cv.name = true
    · rw [if_pos hro] at h
      cases hrpin : checkReducePin (m := CheckM) (fueledOps μ F) env
          ⟨.axiomInfo { cv with type := type } :: env.consts⟩ cv.name
          value with
      | error e => rw [hrpin] at h; exact nomatch h
      | ok u =>
        rw [hrpin] at h
        simp only [Except.ok.injEq] at h
        exact h.symm
    · rw [if_neg hro] at h
      simp only [Except.ok.injEq] at h
      exact h.symm
  · intro hro
    rw [if_pos hro] at h
    cases hrpin : checkReducePin (m := CheckM) (fueledOps μ F) env
        ⟨.axiomInfo { cv with type := type } :: env.consts⟩ cv.name
        value with
    | error e => rw [hrpin] at h; exact nomatch h
    | ok u =>
      rw [hrpin] at h
      simp only [Except.ok.injEq] at h
      subst h
      refine reducePinR_of m (fun a hann => ?_) hrpin
      refine ⟨Expr.not_hasFvar_of_fvarsBelow_zero
          ((annotateCore_WScoped F value hann
            (Expr.WScoped.of_not_hasFvar hivf')).fvarsBelow),
        annotateCore_looseBVars F value hann hlbv, fun φ => ?_⟩
      obtain rfl : a = value' := by
        rw [hannv] at hann; exact (Except.ok.inj hann).symm
      obtain ⟨-, -, -, -, -, -, hf⟩ :=
        valueFrontR_of m.toEnvR htf hbt' hlbv hivf' hannv hvp hvr hvt
          hde hcv
      obtain ⟨-, Vv, -, -, hVv, -⟩ := hf φ
      exact ⟨Vv, hVv⟩

/-- **`defnDecl`, bridged**, parametric in the two structural-`Nat`
pin inversions.  Both packs are phrased over the **annotated** value
the environment actually stores (`value'`), not over the stream's
`value`. -/
theorem declDefnR {V : Type w} [SetTheory V] {env env₂ : Env}
    (m : EnvS V env) {μ : CheckMode} {F : Nat} {cv : ConstantVal}
    {value : Expr} {hint : ReducibilityHint}
    (h : checkDecl μ (fueledOps μ F) env (.defnDecl cv value hint)
      = .ok env₂) :
    DeclDefnR μ F env m.cval cv value hint env₂ := by
  simp only [checkDecl, checkDefnVal, fueledOps_annotate,
    fueledOps_inferType, fueledOps_isDefEq, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, htf, hbt', hcv⟩ := constantValR_of m.toEnvR hccv
  simp only [Pure.pure, Except.pure] at h
  by_cases hlbv : value.looseBVarsBounded 0 = true
  case neg => simp [hlbv] at h
  simp only [hlbv] at h
  by_cases hivf : value.hasFvar = true
  case pos => simp [hivf] at h
  simp only [hivf] at h
  have hivf' : value.hasFvar = false := by
    revert hivf; cases value.hasFvar <;> simp
  cases hannv : annotateCore μ env F 0 value with
  | error e => rw [hannv] at h; exact nomatch h
  | ok value' =>
  rw [hannv] at h
  try dsimp only at h
  by_cases hvp : value'.allLevelParamsDefined cv.levelParams = true
  case neg => simp [hvp] at h
  simp only [hvp] at h
  by_cases hvr : value'.constsResolve env = true
  case neg => simp [hvr] at h
  simp only [hvr] at h
  cases hvt : inferTypeCore μ env F 0 value' with
  | error e => rw [hvt] at h; exact nomatch h
  | ok vtype =>
  rw [hvt] at h
  try dsimp only at h
  cases hde : isDefEqCore μ env F 0 vtype type with
  | error e => rw [hde] at h; exact nomatch h
  | ok b =>
  rw [hde] at h
  cases b with
  | false => exact nomatch h
  | true =>
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  -- the environment the two pin blocks run against, and its own lookup
  have hfind2 : (⟨ConstantInfo.defnInfo { cv with type := type } value'
        hint :: env.consts⟩ : Env).find? cv.name
      = some (.defnInfo { cv with type := type } value' hint) := by
    rw [Env.find?_cons]; exact if_pos rfl
  -- **the dispatch, once**: the stored environment and the two packs
  have key : env₂ = ⟨ConstantInfo.defnInfo { cv with type := type }
        value' hint :: env.consts⟩ ∧
      (natOpNames.contains cv.name = true →
        natOpGuard ⟨ConstantInfo.defnInfo { cv with type := type }
            value' hint :: env.consts⟩ cv.name = true ∧
        (natOpDeps cv.name).all (natOpStoredOk
          ⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
            env.consts⟩) = true ∧
        certifyNatEqs (m := CheckM) (fueledOps μ F) env
          ((natOpEquations 0 cv.name).map fun eq =>
            (Expr.substConst0 cv.name value' eq.1,
             Expr.substConst0 cv.name value' eq.2)) = .ok true) ∧
      (natDivModNames.contains cv.name = true →
        checkDivModPin (m := CheckM) (fueledOps μ F) env
          ⟨ConstantInfo.defnInfo { cv with type := type } value' hint ::
            env.consts⟩ cv.name = .ok ()) := by
    by_cases hno : natOpNames.contains cv.name = true
    · rw [if_pos hno] at h
      by_cases hg : (natOpGuard ⟨ConstantInfo.defnInfo
            { cv with type := type } value' hint :: env.consts⟩ cv.name
          && (natOpDeps cv.name).all (natOpStoredOk
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩)) = true
      · rw [if_pos hg] at h
        rw [hfind2] at h
        dsimp only at h
        cases hcert : certifyNatEqs (m := CheckM) (fueledOps μ F) env
            ((natOpEquations 0 cv.name).map fun eq =>
              (Expr.substConst0 cv.name value' eq.1,
               Expr.substConst0 cv.name value' eq.2)) with
        | error e => rw [hcert] at h; exact nomatch h
        | ok v =>
        rw [hcert] at h
        cases v with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, throw, throwThe,
            MonadExceptOf.throw] at h
          exact nomatch h
        | true =>
        simp only [↓reduceIte] at h
        obtain ⟨hg1, hg2⟩ := Bool.and_eq_true _ _ |>.mp hg
        by_cases hdn : natDivModNames.contains cv.name = true
        · rw [if_pos hdn] at h
          cases hpin : checkDivModPin (m := CheckM) (fueledOps μ F) env
              ⟨ConstantInfo.defnInfo { cv with type := type } value'
                hint :: env.consts⟩ cv.name with
          | error e => rw [hpin] at h; exact nomatch h
          | ok u =>
            rw [hpin] at h
            simp only [Except.ok.injEq] at h
            subst h
            exact ⟨rfl, fun _ => ⟨hg1, hg2, rfl⟩, fun _ => rfl⟩
        · rw [if_neg hdn] at h
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨rfl, fun _ => ⟨hg1, hg2, rfl⟩, fun hc => absurd hc hdn⟩
      · rw [if_neg hg] at h
        simp only [throw, throwThe, MonadExceptOf.throw] at h
        exact nomatch h
    · rw [if_neg hno] at h
      by_cases hdn : natDivModNames.contains cv.name = true
      · rw [if_pos hdn] at h
        cases hpin : checkDivModPin (m := CheckM) (fueledOps μ F) env
            ⟨ConstantInfo.defnInfo { cv with type := type } value'
              hint :: env.consts⟩ cv.name with
        | error e => rw [hpin] at h; exact nomatch h
        | ok u =>
          rw [hpin] at h
          simp only [Except.ok.injEq] at h
          subst h
          exact ⟨rfl, fun hc => absurd hc hno, fun _ => rfl⟩
      · rw [if_neg hdn] at h
        simp only [Except.ok.injEq] at h
        subst h
        exact ⟨rfl, fun hc => absurd hc hno, fun hc => absurd hc hdn⟩
  obtain ⟨rfl, hnatK, hdmK⟩ := key
  exact ⟨type, value', hcv,
    valueFrontR_of m.toEnvR htf hbt' hlbv hivf' hannv hvp hvr hvt hde
      hcv,
    rfl,
    fun hc => ⟨(hnatK hc).1, (hnatK hc).2.1,
      natEqsR_of_certs m
        (cv := { cv with type := type }) (hint := hint)
        (by simpa using hc)
        (Expr.not_hasFvar_of_fvarsBelow_zero
          ((annotateCore_WScoped F value hannv
            (Expr.WScoped.of_not_hasFvar hivf')).fvarsBelow))
        (annotateCore_looseBVars F value hannv hlbv)
        (fun φ => by
          obtain ⟨-, -, -, -, -, -, hf⟩ :=
            valueFrontR_of m.toEnvR htf hbt' hlbv hivf' hannv hvp hvr
              hvt hde hcv
          obtain ⟨-, Vv, -, -, hVv, -⟩ := hf φ
          exact ⟨Vv, hVv⟩)
        (hnatK hc).1 (hnatK hc).2.2⟩,
    fun hc => divModPinR_of m
      (by rw [Env.find?_cons]; exact if_pos rfl) (hdmK hc)⟩

/-! ## The opened statement's frame

D6's quantified-context walk, entered.  Every walk element of an
`iota_j` statement is a piece of that statement's *opened* type, so
what the walk layer needs per element — a denotation and three frame
facts — all descends from one fact: the stored theorem's type denotes.
`EnvR.ty_denotes` supplies that, and
`openPisAtFvars_denoteTele` (`Verify/Denote/IndFrame.lean`) turns it
into the opened body's denotation together with each opener's
annotation denoted at its own depth. -/

/-- **A stored constant's type denotes** — `EnvR.ty_denotes` at a
`find?` rather than a membership, which is how every statement pin
reaches it. -/
theorem stmtType_denotes {env : Env} (m : EnvR env) {φ : Name → Nat}
    {n : Name} {ci : ConstantInfo} {cvt : ConstantVal}
    (hfind : env.find? n = some ci) (hcv : ci.toConstantVal = cvt) :
    ∃ T, denote m.cval env φ 0 cvt.type = some T := by
  obtain ⟨t, ht⟩ := m.ty_denotes ci (find?_mem hfind) φ
  rw [hcv, denoteClosed] at ht
  exact ⟨t, ht⟩

/-- **The opened statement, denoted.**  The composite the walks
consume: the opened body denotes at the opening depth, and every
opener's annotation denotes at its own. -/
theorem stmtOpened_denotes {env : Env} (m : EnvR env) {φ : Name → Nat}
    {n : Name} {ci : ConstantInfo} {cvt : ConstantVal} {k : Nat}
    {fvs : List Expr} {tbody : Expr}
    (hfind : env.find? n = some ci) (hcv : ci.toConstantVal = cvt)
    (hopen : openPisAtFvars k cvt.type 0 = some (fvs, tbody)) :
    ∃ (Γ : List VExpr) (R : VExpr),
      denote m.cval env φ k tbody = some R ∧
      ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
        denote m.cval env φ i (Expr.fvarTypeD x)
          = some (Γ.getD (k - 1 - i) default) := by
  obtain ⟨T, hT⟩ := stmtType_denotes m (φ := φ) hfind hcv
  obtain ⟨Γ, R, -, hbody, hfv⟩ :=
    openPisAtFvars_denoteTele k hopen hT
  rw [Nat.zero_add] at hbody
  refine ⟨Γ, R, hbody, fun i x hx => ?_⟩
  have h := hfv i x hx
  rwa [Nat.zero_add] at h


/-- **The openers' walk package.**  Everything `defEqListW_of` needs
about a statement walk's *left*-hand list, for a telescope opened from
a stored, closed subject at depth `0`: the three frame facts and the
denotation, all at the walk's depth `D`.

Assembled from four existing frame lemmas plus `opener_denotes_at`;
the subject being `hasFvar`-free is what makes
`openPisAtFvars_leaves` conclude that *every* leaf of an opener's
annotation is itself an opener, hence `looseBVarsBounded 0`. -/
theorem opener_walk_pack {env : Env} (m : EnvR env) {φ : Name → Nat}
    {n : Name} {ci : ConstantInfo} {cvt : ConstantVal} {k D : Nat}
    {fvs : List Expr} {tbody : Expr}
    (hfind : env.find? n = some ci) (hcv : ci.toConstantVal = cvt)
    (hnf : cvt.type.hasFvar = false)
    (hb : cvt.type.looseBVarsBounded 0 = true)
    (hopen : openPisAtFvars k cvt.type 0 = some (fvs, tbody))
    (hle : k ≤ D) :
    ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      Expr.WScoped D (Expr.fvarTypeD x) ∧
      (Expr.fvarTypeD x).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Expr.fvarTypeD x) ∧
      ∃ v, denote m.cval env φ D (Expr.fvarTypeD x) = some v := by
  intro i x hx
  have hmem : x ∈ fvs := List.mem_of_getElem? hx
  obtain ⟨-, hbfv⟩ := openPisAtFvars_bounded k hopen hb
  obtain ⟨hwfv, -⟩ := openPisAtFvars_WScoped k cvt.type 0 hopen
    (Expr.WScoped.of_not_hasFvar hnf)
  obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index k cvt.type 0 hopen i x hx
  have hwx := hwfv _ hmem
  rw [Expr.WScoped] at hwx
  obtain ⟨hlt, hwty⟩ := hwx
  rw [Nat.zero_add] at hlt hwty
  obtain ⟨Γ, R, -, hfvd⟩ :=
    stmtOpened_denotes m (φ := φ) hfind hcv hopen
  refine ⟨Expr.WScoped.mono (by omega) hwty, hbfv _ hmem, ?_,
    opener_denotes_at m hwty.fvarsBelow (by omega) (hfvd i _ hx)⟩
  -- every leaf of an opener's annotation is itself an opener
  intro l hl
  have hlx : l ∈ (Expr.fvar (0 + i) nm ty).fvarLeaves := by
    simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
    exact List.mem_cons_of_mem _ hl
  rcases openPisAtFvars_leaves k hopen l (Or.inr ⟨_, hmem, hlx⟩) with
    h' | h'
  · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at h'
    exact nomatch h'
  · exact hbfv _ h'

/-- **The `instPisAt` walk package** — the right-hand list's twin of
`opener_walk_pack`, and by the same economy: every statement walk's
right list is an `instPisAt` output, so one lemma covers all six.
Assembled from `instPisAt_WScoped`, `instPisAt_bounded`,
`instPisAt_leaves` and `instPisAt_denote_doms`. -/
theorem instPisAt_walk_pack {env : Env} (m : EnvR env)
    {φ : Name → Nat} {D : Nat} {sp : List Expr} {ty : Expr}
    {ds : List Expr} {rs : Expr}
    (hinst : Expr.instPisAt sp ty = some (ds, rs))
    (hwty : Expr.WScoped D ty) (hbty : ty.looseBVarsBounded 0 = true)
    (hLty : Expr.LeavesBounded ty)
    (hsp : ∀ a ∈ sp, Expr.WScoped D a ∧ a.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a)
    (hspd : ∀ (j : Nat) (x : Expr), sp[j]? = some x →
      ∃ w, denote m.cval env φ D x = some w)
    {T : VExpr} (hT : denote m.cval env φ D ty = some T) :
    ∀ x ∈ ds, Expr.WScoped D x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧
      ∃ v, denote m.cval env φ D x = some v := by
  intro x hx
  obtain ⟨hw, -⟩ :=
    instPisAt_WScoped sp ty hinst hwty (fun a ha => (hsp a ha).1)
  obtain ⟨hb, -⟩ :=
    instPisAt_bounded sp hinst hbty (fun a ha => (hsp a ha).2.1)
  refine ⟨hw x hx, hb x hx, ?_, ?_⟩
  · intro l hl
    rcases instPisAt_leaves sp hinst l (Or.inl ⟨x, hx, hl⟩) with
      h' | ⟨a, ha, hla⟩
    · exact hLty l h'
    · exact (hsp a ha).2.2 l hla
  · exact instPisAt_denote_doms m.cval_closed sp hinst
      (fun j y hy => ⟨hspd j y hy,
        (hsp y (List.mem_of_getElem? hy)).1,
        (hsp y (List.mem_of_getElem? hy)).2.1⟩)
      hwty.fvarsBelow hbty hT x hx

/-- **The `instPisAt` residual, packaged** — `instPisAt_walk_pack`'s
other half, at identical premises.  Every frame lemma the domains
pack calls already produces the residual conjunct and discards it;
`IotaWalksR`'s λ-row opens this residual, so it is collected here
rather than re-derived at the use site (task #148 T6). -/
theorem instPisAt_res_pack {env : Env} (m : EnvR env)
    {φ : Name → Nat} {D : Nat} {sp : List Expr} {ty : Expr}
    {ds : List Expr} {rs : Expr}
    (hinst : Expr.instPisAt sp ty = some (ds, rs))
    (hwty : Expr.WScoped D ty) (hbty : ty.looseBVarsBounded 0 = true)
    (hLty : Expr.LeavesBounded ty)
    (hsp : ∀ a ∈ sp, Expr.WScoped D a ∧ a.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a)
    (hspd : ∀ (j : Nat) (x : Expr), sp[j]? = some x →
      ∃ w, denote m.cval env φ D x = some w)
    {T : VExpr} (hT : denote m.cval env φ D ty = some T) :
    Expr.WScoped D rs ∧ rs.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded rs ∧
      ∃ v, denote m.cval env φ D rs = some v := by
  obtain ⟨-, hw⟩ :=
    instPisAt_WScoped sp ty hinst hwty (fun a ha => (hsp a ha).1)
  obtain ⟨-, hb⟩ :=
    instPisAt_bounded sp hinst hbty (fun a ha => (hsp a ha).2.1)
  refine ⟨hw, hb, ?_, ?_⟩
  · intro l hl
    rcases instPisAt_leaves sp hinst l (Or.inr hl) with
      h' | ⟨a, ha, hla⟩
    · exact hLty l h'
    · exact (hsp a ha).2.2 l hla
  · exact instPisAt_denote_res m.cval_closed sp hinst
      (fun j y hy => ⟨hspd j y hy,
        (hsp y (List.mem_of_getElem? hy)).1,
        (hsp y (List.mem_of_getElem? hy)).2.1⟩)
      hwty.fvarsBelow hbty hT

/-- **The `instLamsAt` domains, packaged** — the λ-side counterpart of
`instPisAt_walk_pack`, and `IotaWalksR`'s fourth row's right-hand
side.  The denotation comes from `instLamsAt_denoteTele`, which places
domain `i` at depth `i`; `opener_denotes_at` lifts each to the common
walk depth `D`, which is what makes the opener-shape premise
(`sp[i]? = some (.fvar i …)`) load-bearing. -/
theorem instLamsAt_walk_pack {env : Env} (m : EnvR env)
    {φ : Name → Nat} {D : Nat} {sp : List Expr} {e : Expr}
    {ds : List Expr} {rs : Expr}
    (hinst : Expr.instLamsAt sp e = some (ds, rs))
    (hshape : ∀ (i : Nat) (x : Expr), sp[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty)
    (hwe : Expr.WScoped 0 e) (hbe : e.looseBVarsBounded 0 = true)
    (hLe : Expr.LeavesBounded e)
    (hsp : ∀ a ∈ sp, Expr.WScoped D a ∧ a.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a)
    {V : VExpr} (hV : denote m.cval env φ 0 e = some V)
    (hle : sp.length ≤ D) :
    ∀ x ∈ ds, Expr.WScoped D x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧
      ∃ v, denote m.cval env φ D x = some v := by
  intro x hx
  obtain ⟨hw, -⟩ :=
    instLamsAt_WScoped sp e hinst (Expr.WScoped.mono (Nat.zero_le D)
      hwe) (fun a ha => (hsp a ha).1)
  obtain ⟨hb, -⟩ :=
    instLamsAt_bounded sp hinst hbe (fun a ha => (hsp a ha).2.1)
  have hLx : Expr.LeavesBounded x := by
    intro l hl
    rcases instLamsAt_leaves sp hinst l (Or.inl ⟨x, hx, hl⟩) with
      h' | ⟨a, ha, hla⟩
    · exact hLe l h'
    · exact (hsp a ha).2.2 l hla
  refine ⟨hw x hx, hb x hx, hLx, ?_⟩
  obtain ⟨Γ, C, -, -, -, hds⟩ :=
    instLamsAt_denoteTele (j := 0) sp hinst
      (fun i y hy => by
        obtain ⟨nm, ty, rfl⟩ := hshape i y hy
        exact ⟨nm, ty, by rw [Nat.zero_add]⟩) hV
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  have hilt : i < ds.length := by
    rcases Nat.lt_or_ge i ds.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hi; exact nomatch hi
  have hdlen : ds.length = sp.length := instLamsAt_length sp hinst
  -- domain `i` is scoped at `i`, so its depth-`i` denotation lifts
  have hxW : Expr.WScoped i x := by
    have h0 := instLamsAt_index_WScoped sp (d := 0) hinst hwe
      (fun k a hk => by
        obtain ⟨nm, ty, rfl⟩ := hshape k a hk
        have h1 := (hsp _ (List.mem_of_getElem? hk)).1
        rw [Expr.WScoped] at h1 ⊢
        exact ⟨by omega, h1.2⟩) i x hi
    rwa [Nat.zero_add] at h0
  have hden : denote m.cval env φ i x =
      some (Γ.getD (sp.length - 1 - i) default) := by
    simpa using hds i x hi
  exact opener_denotes_at m hxW.fvarsBelow
    (show i ≤ D from by omega) hden

/-- **The openers themselves**, packaged.  `instPisAt_walk_pack`'s
spine hypothesis is about the opener *fvars*, not their annotations,
so it needs this rather than `opener_walk_pack`.  Two of the four
conjuncts are free (`looseBVarsBounded` is `true` at an `.fvar` by
computation, and `denote_fvar` is unconditional); the other two are
the same two frame lemmas. -/
theorem opener_fvar_pack {env : Env} (m : EnvR env) {φ : Name → Nat}
    {cvt : ConstantVal} {k D : Nat} {fvs : List Expr} {tbody : Expr}
    (hnf : cvt.type.hasFvar = false)
    (hb : cvt.type.looseBVarsBounded 0 = true)
    (hopen : openPisAtFvars k cvt.type 0 = some (fvs, tbody))
    (hle : k ≤ D) :
    ∀ x ∈ fvs, Expr.WScoped D x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧
      ∃ v, denote m.cval env φ D x = some v := by
  intro x hx
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  obtain ⟨-, hbfv⟩ := openPisAtFvars_bounded k hopen hb
  obtain ⟨hwfv, -⟩ := openPisAtFvars_WScoped k cvt.type 0 hopen
    (Expr.WScoped.of_not_hasFvar hnf)
  obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index k cvt.type 0 hopen i x hi
  refine ⟨Expr.WScoped.mono (by omega) (hwfv _ hx), rfl, ?_,
    ⟨_, denote_fvar _ _ _ _ _ _ _⟩⟩
  intro l hl
  rcases openPisAtFvars_leaves k hopen l (Or.inr ⟨_, hx, hl⟩) with
    h' | h'
  · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at h'
    exact nomatch h'
  · exact hbfv _ h'

/-- **A stored constant's type, packaged** at any depth — the third
walk input, and the one the `instPisAt` packs need for their subject.
`EnvR.wf` supplies the closedness, `EnvR.ty_denotes` the denotation at
depth `0`, and `opener_denotes_at` lifts it. -/
theorem storedType_pack {env : Env} (m : EnvR env) {φ : Name → Nat}
    {n : Name} {ci : ConstantInfo} (hfind : env.find? n = some ci)
    (D : Nat) :
    Expr.WScoped D ci.toConstantVal.type ∧
    ci.toConstantVal.type.looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded ci.toConstantVal.type ∧
    ∃ v, denote m.cval env φ D ci.toConstantVal.type = some v := by
  obtain ⟨hnf, -, -, hb, -⟩ := m.wf ci (find?_mem hfind)
  obtain ⟨t, ht⟩ := m.ty_denotes ci (find?_mem hfind) φ
  rw [denoteClosed] at ht
  exact ⟨Expr.WScoped.mono (Nat.zero_le D)
      (Expr.WScoped.of_not_hasFvar hnf), hb,
    Expr.LeavesBounded.of_not_hasFvar hnf,
    opener_denotes_at m (Expr.WScoped.of_not_hasFvar hnf).fvarsBelow
      (Nat.zero_le D) ht⟩

/-- **A stored constant's type under the block renaming**, packaged —
what `IotaWalksR`'s renamed rows need, and the reason
`storedType_pack` alone does not reach them.  Every conjunct is its
unrenamed twin composed with a preservation lemma; the denotation is
`denote_renameConsts`, whose `RenameOkT` premise the recursor group's
fold already builds. -/
theorem renamedType_pack {env : Env} (m : EnvR env) {φ : Name → Nat}
    {f : Name → Name} (hro : RenameOkT m.cval env f)
    {n : Name} {ci : ConstantInfo} (hfind : env.find? n = some ci)
    (D : Nat) :
    Expr.WScoped D (ci.toConstantVal.type.renameConsts f) ∧
    (ci.toConstantVal.type.renameConsts f).looseBVarsBounded 0 = true ∧
    Expr.LeavesBounded (ci.toConstantVal.type.renameConsts f) ∧
    ∃ v, denote m.cval env φ D (ci.toConstantVal.type.renameConsts f)
      = some v := by
  obtain ⟨hw, hb, hL, v, hv⟩ := storedType_pack m (φ := φ) hfind D
  exact ⟨wscoped_renameConsts _ hw,
    by rw [looseBVarsBounded_renameConsts]; exact hb,
    leavesBounded_renameConsts _ hL,
    v, by rw [denote_renameConsts hro]; exact hv⟩

/-- **The openers' pack, generalised.**  `opener_walk_pack` assumed a
*stored* subject opened at depth `0`; `IotaWalksR`'s λ-row opens an
`instPisAt` **residual** at depth `rP`, so the specialised form does
not reach it — the same over-specialisation `stmtWalk_of` showed.

The general form takes the subject's own package.  It is also
*simpler*: the specialised proof used the subject's `hasFvar`-freeness
to argue that every leaf of an opener's annotation must itself be an
opener, and here `hL` covers the subject's own leaves directly. -/
theorem opener_walk_pack_gen {env : Env} (m : EnvR env)
    {φ : Name → Nat} {e : Expr} {d₀ k D : Nat} {fvs : List Expr}
    {body : Expr}
    (hw : Expr.WScoped d₀ e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e)
    {T : VExpr} (hT : denote m.cval env φ d₀ e = some T)
    (hopen : openPisAtFvars k e d₀ = some (fvs, body))
    (hle : d₀ + k ≤ D) :
    ∀ (i : Nat) (x : Expr), fvs[i]? = some x →
      Expr.WScoped D (Expr.fvarTypeD x) ∧
      (Expr.fvarTypeD x).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Expr.fvarTypeD x) ∧
      ∃ v, denote m.cval env φ D (Expr.fvarTypeD x) = some v := by
  intro i x hx
  have hmem : x ∈ fvs := List.mem_of_getElem? hx
  obtain ⟨-, hbfv⟩ := openPisAtFvars_bounded k hopen hb
  obtain ⟨hwfv, -⟩ := openPisAtFvars_WScoped k e d₀ hopen hw
  obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index k e d₀ hopen i x hx
  have hwx := hwfv _ hmem
  rw [Expr.WScoped] at hwx
  obtain ⟨hlt, hwty⟩ := hwx
  obtain ⟨Γ, R, -, -, hfvd⟩ := openPisAtFvars_denoteTele k hopen hT
  refine ⟨Expr.WScoped.mono (by omega) hwty, hbfv _ hmem, ?_,
    opener_denotes_at m hwty.fvarsBelow (by omega) (hfvd i _ hx)⟩
  intro l hl
  have hlx : l ∈ (Expr.fvar (d₀ + i) nm ty).fvarLeaves := by
    simp only [Expr.fvarLeaves, Expr.fvarTypeD] at hl ⊢
    exact List.mem_cons_of_mem _ hl
  rcases openPisAtFvars_leaves k hopen l (Or.inr ⟨_, hmem, hlx⟩) with
    h' | h'
  · exact hL l h'
  · exact hbfv _ h'

/-- **The opened body, packaged.**  `opener_walk_pack_gen` and
`opener_fvar_pack_gen` deliver a telescope opening's *annotations* and
*variables*; `IotaWalksR`'s index row and its `IotaSidesTyR` row are
about the opened **body** (the statement's `Eq` application), so the
third component needs its own pack.  Each conjunct is the residual
half of the frame lemma whose domain half the other two packs use. -/
theorem opener_body_pack_gen {env : Env} (m : EnvR env)
    {φ : Name → Nat} {e : Expr} {d₀ k D : Nat} {fvs : List Expr}
    {body : Expr}
    (hw : Expr.WScoped d₀ e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e)
    {T : VExpr} (hT : denote m.cval env φ d₀ e = some T)
    (hopen : openPisAtFvars k e d₀ = some (fvs, body))
    (hle : d₀ + k ≤ D) :
    Expr.WScoped D body ∧ body.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded body ∧
      ∃ v, denote m.cval env φ D body = some v := by
  obtain ⟨hbbody, hbfv⟩ := openPisAtFvars_bounded k hopen hb
  obtain ⟨hwfv, hwbody⟩ := openPisAtFvars_WScoped k e d₀ hopen hw
  obtain ⟨Γ, R, -, hRbody, -⟩ := openPisAtFvars_denoteTele k hopen hT
  refine ⟨Expr.WScoped.mono (by omega) hwbody, hbbody, ?_,
    opener_denotes_at m hwbody.fvarsBelow (by omega) hRbody⟩
  intro l hl
  rcases openPisAtFvars_leaves k hopen l (Or.inl hl) with h' | h'
  · exact hL l h'
  · exact hbfv _ h'

/-- **An application spine, packaged** from its head and arguments —
`spine_walk_pack` run backwards.  `IotaWalksR`'s `rhs` row compares
the statement's right side against the rule's right-hand side
*applied to the whole opening*, which is built, not found. -/
theorem mkAppN_walk_pack {env : Env} (m : EnvR env) {φ : Name → Nat}
    {D : Nat} {g : Expr} {as : List Expr}
    (hwg : Expr.WScoped D g) (hbg : g.looseBVarsBounded 0 = true)
    (hLg : Expr.LeavesBounded g)
    (has : ∀ a ∈ as, Expr.WScoped D a ∧ a.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded a ∧ ∃ w, denote m.cval env φ D a = some w)
    {vg : VExpr} (hg : denote m.cval env φ D g = some vg) :
    Expr.WScoped D (Expr.mkAppN g as) ∧
      (Expr.mkAppN g as).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Expr.mkAppN g as) ∧
      ∃ v, denote m.cval env φ D (Expr.mkAppN g as) = some v := by
  have hsp : ∀ (bs : List Expr),
      (∀ a ∈ bs, ∃ w, denote m.cval env φ D a = some w) →
      ∃ vs, DenoteSpine m.cval env φ D bs vs := by
    intro bs
    induction bs with
    | nil => intro _; exact ⟨[], DenoteSpine.nil⟩
    | cons b bs ih =>
      intro hb2
      obtain ⟨w, hw⟩ := hb2 b List.mem_cons_self
      obtain ⟨vs, hvs⟩ :=
        ih (fun a ha => hb2 a (List.mem_cons_of_mem _ ha))
      exact ⟨w :: vs, DenoteSpine.cons hw hvs⟩
  obtain ⟨vs, hvs⟩ := hsp as (fun a ha => (has a ha).2.2.2)
  refine ⟨Expr.WScoped.mkAppN hwg (fun x hx => (has x hx).1),
    looseBVarsBounded_mkAppN hbg (fun x hx => (has x hx).2.1),
    ?_, _, denote_mkAppN hvs hg⟩
  intro l hl
  rcases fvarLeaves_mkAppN hl with h' | ⟨x, hx, hlx⟩
  · exact hLg l h'
  · exact (has x hx).2.2.1 l hlx

/-- **The two side-typing obligations, bridged** — `IotaWalksR`'s
sixth row.  Each side's `inferTypeCore` verdict becomes an `Infer`
derivation up to `DefEq` (`InferClaimsR`); the *inferred* type's own
context correspondence, which `DefEqClaimsR` then needs, is not
supplied by the caller and is not meant to be: it follows from the
subject's by `CtxOkR.of_subset` and `inferTypeCore_fvarLeaves`. -/
theorem iotaSidesTyR_of {env : Env} (m : EnvR env) {μ : CheckMode}
    {F : Nat} {φ : Name → Nat} {d : Nat} {αS lhsS rhsS : Expr}
    (hwA : Expr.WScoped d αS) (hbA : αS.looseBVarsBounded 0 = true)
    (hLA : Expr.LeavesBounded αS)
    (hwL : Expr.WScoped d lhsS) (hbL : lhsS.looseBVarsBounded 0 = true)
    (hLL : Expr.LeavesBounded lhsS)
    (hwR : Expr.WScoped d rhsS) (hbR : rhsS.looseBVarsBounded 0 = true)
    (hLR : Expr.LeavesBounded rhsS)
    {Av Lv Rv : VExpr}
    (hAv : denote m.cval env φ d αS = some Av)
    (hLv : denote m.cval env φ d lhsS = some Lv)
    (hRv : denote m.cval env φ d rhsS = some Rv)
    {tl tr : Expr}
    (hil : inferTypeCore μ env F d lhsS = .ok tl)
    (hdl : isDefEqCore μ env F d tl αS = .ok true)
    (hir : inferTypeCore μ env F d rhsS = .ok tr)
    (hdr : isDefEqCore μ env F d tr αS = .ok true) :
    IotaSidesTyR μ env m.cval φ d αS lhsS rhsS := by
  refine ⟨Av, Lv, Rv, hAv, hLv, hRv, fun Δ hCA hCL hCR => ?_⟩
  obtain ⟨-, -, ihd, ihi⟩ := checkBridge m φ F
  constructor
  · obtain ⟨v, tv, hv, htv, T', hI, hD⟩ := ihi hil hwL hbL hLL hCL
    obtain rfl : v = Lv := by rw [hv] at hLv; exact Option.some.inj hLv
    refine ⟨T', hI, DefEq.trans hD (ihd hdl
      (inferTypeCore_WScoped m.wf F hil hwL)
      (inferTypeCore_looseBVars m.wf F hil hwL hbL hLL)
      (fun l hl =>
        hLL l (inferTypeCore_fvarLeaves m.wf F hil hwL l hl))
      hwA hbA hLA
      (CtxOkR.of_subset
        (inferTypeCore_fvarLeaves m.wf F hil hwL) hCL) hCA htv hAv)⟩
  · obtain ⟨v, tv, hv, htv, T', hI, hD⟩ := ihi hir hwR hbR hLR hCR
    obtain rfl : v = Rv := by rw [hv] at hRv; exact Option.some.inj hRv
    refine ⟨T', hI, DefEq.trans hD (ihd hdr
      (inferTypeCore_WScoped m.wf F hir hwR)
      (inferTypeCore_looseBVars m.wf F hir hwR hbR hLR)
      (fun l hl =>
        hLR l (inferTypeCore_fvarLeaves m.wf F hir hwR l hl))
      hwA hbA hLA
      (CtxOkR.of_subset
        (inferTypeCore_fvarLeaves m.wf F hir hwR) hCR) hCA htv hAv)⟩

/-- The generalised twin of `opener_fvar_pack`: the opener *fvars*
themselves at a general subject and opening depth. -/
theorem opener_fvar_pack_gen {env : Env} (m : EnvR env)
    {φ : Name → Nat} {e : Expr} {d₀ k D : Nat} {fvs : List Expr}
    {body : Expr}
    (hw : Expr.WScoped d₀ e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e)
    {T : VExpr} (_hT : denote m.cval env φ d₀ e = some T)
    (hopen : openPisAtFvars k e d₀ = some (fvs, body))
    (hle : d₀ + k ≤ D) :
    ∀ x ∈ fvs, Expr.WScoped D x ∧ x.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded x ∧
      ∃ v, denote m.cval env φ D x = some v := by
  intro x hx
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
  obtain ⟨-, hbfv⟩ := openPisAtFvars_bounded k hopen hb
  obtain ⟨hwfv, -⟩ := openPisAtFvars_WScoped k e d₀ hopen hw
  obtain ⟨nm, ty, rfl⟩ := openPisAtFvars_index k e d₀ hopen i x hi
  refine ⟨Expr.WScoped.mono (by omega) (hwfv _ hx), rfl, ?_,
    ⟨_, denote_fvar _ _ _ _ _ _ _⟩⟩
  intro l hl
  rcases openPisAtFvars_leaves k hopen l
    (Or.inr ⟨_, hx, hl⟩) with h' | h'
  · exact hL l h'
  · exact hbfv _ h'

/-! ## The comparison walks

Every `iota_j` statement walk the checker runs is a `checkDefEqList`
or a single `isDefEq`, and every one of them lands in the relation as
`DefEqAtW`/`DefEqListW`.  Those differ from what `DefEqClaimsR`
delivers in exactly one respect: they assert the two **denotations
exist**, where the claim takes them as inputs.  Everything else — the
`∀ Δ` quantification over correlating contexts, the two `CtxOkR`
premises — matches the claim's shape verbatim.

So the whole walk layer factors through one lemma, and what is left to
supply per element is a denotation and three frame facts, both of
which the opened statement's own type carries. -/

/-- **One comparison, bridged.** -/
theorem defEqAtW_of {env : Env} (m : EnvR env) {μ : CheckMode}
    {F : Nat} {φ : Name → Nat} {d : Nat} {a b : Expr}
    (hwa : Expr.WScoped d a) (hba : a.looseBVarsBounded 0 = true)
    (hLa : Expr.LeavesBounded a)
    (hwb : Expr.WScoped d b) (hbb : b.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded b)
    {Av Bv : VExpr}
    (hAv : denote m.cval env φ d a = some Av)
    (hBv : denote m.cval env φ d b = some Bv)
    (h : isDefEqCore μ env F d a b = .ok true) :
    DefEqAtW μ env m.cval φ d a b := by
  refine ⟨Av, Bv, hAv, hBv, fun Δ hCa hCb => ?_⟩
  obtain ⟨-, -, ihd, -⟩ := checkBridge m φ F
  exact ihd h hwa hba hLa hwb hbb hLb hCa hCb hAv hBv

/-- **A comparison list, bridged** — `checkDefEqList`'s verdict pack
(`DefEqListOk`) against the relation's pointwise quantified walk.  The
per-element frames and denotations are the caller's; the fold itself
is this induction. -/
theorem defEqListW_of {env : Env} (m : EnvR env) {μ : CheckMode}
    {F : Nat} {φ : Name → Nat} {d : Nat} :
    ∀ (as bs : List Expr),
      (∀ e ∈ as ++ bs, Expr.WScoped d e ∧
        e.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded e ∧
        ∃ v, denote m.cval env φ d e = some v) →
      DefEqListOk μ F env d as bs →
      DefEqListW μ env m.cval φ d as bs
  | [], [], _, _ => trivial
  | a :: as, b :: bs, hfr, h => by
    obtain ⟨hwa, hba, hLa, Av, hAv⟩ := hfr a (by simp)
    obtain ⟨hwb, hbb, hLb, Bv, hBv⟩ := hfr b (by simp)
    exact ⟨defEqAtW_of m hwa hba hLa hwb hbb hLb hAv hBv h.1,
      defEqListW_of m as bs
        (fun e he => hfr e (by
          rcases List.mem_append.mp he with h' | h'
          · exact List.mem_append.mpr
              (Or.inl (List.mem_cons_of_mem _ h'))
          · exact List.mem_append.mpr
              (Or.inr (List.mem_cons_of_mem _ h'))))
        h.2⟩
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

/-- **Denotability descends** along the depth index, for anything the
depth's own frame already scopes.  `opener_denotes_at` lifts a
denotation up; the nested pack needs a pin denoted at the *walk* depth
to be denoted at the shallower opening depth its residual is taken
at, which is the same equation read backwards. -/
theorem opener_denotes_below {env : Env} (m : EnvR env) {φ : Name → Nat}
    {i D : Nat} {e : Expr} {w : VExpr}
    (hfb : Expr.fvarsBelow i e) (hle : i ≤ D)
    (h : denote m.cval env φ D e = some w) :
    ∃ v, denote m.cval env φ i e = some v := by
  rw [denote_lift m.cval_closed hfb D hle] at h
  cases hv : denote m.cval env φ i e with
  | none => rw [hv] at h; exact nomatch h
  | some v => exact ⟨v, rfl⟩

/-- A denoted spine denotes each of its members.  (Plain identifier,
not `DenoteSpine.…`: the dotted form would resolve against the
enclosing `Setlec.SetR` and be reachable under neither path.) -/
theorem denoteSpine_mem_denotes {env : Env} {cval : TConstVal}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List VExpr},
      DenoteSpine cval env φ d as vs →
      ∀ x ∈ as, ∃ w, denote cval env φ d x = some w := by
  intro as vs h
  induction h with
  | nil => intro x hx; exact nomatch hx
  | cons hda _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨_, hda⟩
    · exact ih x hx'

/-- A nonempty list's `getLastD` is a member. -/
theorem getLastD_mem {as : List Expr} {n : Nat} {d : Expr}
    (hlen : as.length = n + 1) : as.getLastD d ∈ as := by
  have hx : as[n]? = some as[n] :=
    List.getElem?_eq_getElem (by omega)
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hlen,
    Nat.add_sub_cancel, hx]
  exact List.getElem_mem _

/-- `checkTypedList`'s per-element inference verdict, extracted.  The
nested pack needs the verdicts *before* it can call `typedListW_of`,
because the pins' denotations — which that fold takes as inputs — are
exactly what the verdicts produce (`denote_of_inferR`). -/
theorem typedListOk_infer {μ : CheckMode} {F : Nat} {env : Env}
    {d : Nat} :
    ∀ {es doms : List Expr}, TypedListOk μ F env d es doms →
      ∀ a ∈ es, ∃ ty, inferTypeCore μ env F d a = .ok ty
  | [], [], _ => fun a ha => nomatch ha
  | a :: as, b :: bs, h => by
    intro x hx
    obtain ⟨ty, hi, -⟩ := h.1
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ⟨ty, hi⟩
    · exact typedListOk_infer h.2 x hx'
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h

/-- **A stored pin's three syntactic facts**, at the opener spine that
closes it.  A pin is fvar-free and bounded by exactly the prefix's
binder count (`nestedRuleShape_inv`), so instantiating it at that many
openers closes it and leaves it scoped and leaf-bounded wherever the
openers are.  Used at *both* pin spellings — the statement's openers
(renamed) and the recursor type's (not) — which is why it is stated
over an abstract spine. -/
theorem instSpine_pin_pack {D : Nat} {sp : List Expr} {p : Expr}
    (hnf : p.hasFvar = false)
    (hbp : p.looseBVarsBounded sp.length = true)
    (hsp : ∀ a ∈ sp, Expr.WScoped D a ∧
      a.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded a) :
    Expr.WScoped D (Expr.instSpine sp (sp.length - 1) p) ∧
      (Expr.instSpine sp (sp.length - 1) p).looseBVarsBounded 0
        = true ∧
      Expr.LeavesBounded (Expr.instSpine sp (sp.length - 1) p) := by
  refine ⟨instSpine_WScoped _ (Expr.WScoped.of_not_hasFvar hnf)
      (fun a ha => (hsp a ha).1),
    instSpine_closed (fun a ha => (hsp a ha).2.1) hbp, ?_⟩
  intro l hl
  rcases fvarLeaves_instSpine _ hl with h' | ⟨a, ha, hla⟩
  · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar hnf] at h'
    exact nomatch h'
  · exact (hsp a ha).2.2 l hla

/-- **Inference success plus *any* context yields denotability.**  The
campaign's only source of a denotation for an expression that is
neither a stored type nor an opener nor built from them: a *pin*, for
which the checker's sole verdict is that it inferred a type.  The
denotation `InferClaimsR` returns does not mention `Δ`, so the context
is scaffolding — supply one with `openPisAtFvars_ctxOkR` and
`CtxOkR.of_cover` and discard it. -/
theorem denote_of_inferR {env : Env} (m : EnvR env) {μ : CheckMode}
    {F : Nat} {φ : Name → Nat} {d : Nat} {e t : Expr}
    {Δ : List VExpr}
    (hi : inferTypeCore μ env F d e = .ok t)
    (hw : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e)
    (hC : CtxOkR μ m.cval env φ d Δ e) :
    ∃ v, denote m.cval env φ d e = some v := by
  obtain ⟨-, -, -, ihi⟩ := checkBridge m φ F
  obtain ⟨v, -, hv, -⟩ := ihi hi hw hb hL hC
  exact ⟨v, hv⟩

/-- **One typed comparison, bridged** — `checkTypedList`'s element, the
`Infer`-side twin of `defEqAtW_of`.  Both denotations are premises:
`TypedAtW` states them outside its `∀ Δ` (the soundness side reads the
values back), so they cannot be produced inside. -/
theorem typedAtW_of {env : Env} (m : EnvR env) {μ : CheckMode}
    {F : Nat} {φ : Name → Nat} {d : Nat} {e dom : Expr}
    (hwe : Expr.WScoped d e) (hbe : e.looseBVarsBounded 0 = true)
    (hLe : Expr.LeavesBounded e)
    (hwd : Expr.WScoped d dom) (hbd : dom.looseBVarsBounded 0 = true)
    (hLd : Expr.LeavesBounded dom)
    {Ev Dv : VExpr}
    (hEv : denote m.cval env φ d e = some Ev)
    (hDv : denote m.cval env φ d dom = some Dv)
    {ty : Expr}
    (hi : inferTypeCore μ env F d e = .ok ty)
    (hde : isDefEqCore μ env F d ty dom = .ok true) :
    TypedAtW μ env m.cval φ d e dom := by
  refine ⟨Ev, Dv, hEv, hDv, fun Δ hCe hCd => ?_⟩
  obtain ⟨-, -, ihd, ihi⟩ := checkBridge m φ F
  obtain ⟨v, tv, hv, htv, T', hI, hD⟩ := ihi hi hwe hbe hLe hCe
  obtain rfl : v = Ev := by rw [hv] at hEv; exact Option.some.inj hEv
  exact ⟨T', hI, DefEq.trans hD (ihd hde
    (inferTypeCore_WScoped m.wf F hi hwe)
    (inferTypeCore_looseBVars m.wf F hi hwe hbe hLe)
    (fun l hl => hLe l (inferTypeCore_fvarLeaves m.wf F hi hwe l hl))
    hwd hbd hLd
    (CtxOkR.of_subset (inferTypeCore_fvarLeaves m.wf F hi hwe) hCe)
    hCd htv hDv)⟩

/-- **A typed walk, bridged** — `checkTypedList`'s verdict pack, the
`Infer`-side twin of `defEqListW_of`. -/
theorem typedListW_of {env : Env} (m : EnvR env) {μ : CheckMode}
    {F : Nat} {φ : Name → Nat} {d : Nat} :
    ∀ (es doms : List Expr),
      (∀ x ∈ es ++ doms, Expr.WScoped d x ∧
        x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x ∧
        ∃ v, denote m.cval env φ d x = some v) →
      TypedListOk μ F env d es doms →
      TypedListW μ env m.cval φ d es doms
  | [], [], _, _ => trivial
  | a :: as, b :: bs, hfr, h => by
    obtain ⟨hwa, hba, hLa, Av, hAv⟩ := hfr a (by simp)
    obtain ⟨hwb, hbb, hLb, Bv, hBv⟩ := hfr b (by simp)
    obtain ⟨ty, hi, hde⟩ := h.1
    exact ⟨typedAtW_of m hwa hba hLa hwb hbb hLb hAv hBv hi hde,
      typedListW_of m as bs
        (fun e he => hfr e (by
          rcases List.mem_append.mp he with h' | h'
          · exact List.mem_append.mpr
              (Or.inl (List.mem_cons_of_mem _ h'))
          · exact List.mem_append.mpr
              (Or.inr (List.mem_cons_of_mem _ h'))))
        h.2⟩
  | [], _ :: _, _, h => nomatch h
  | _ :: _, [], _, h => nomatch h

/-- **A statement walk, closed.**  The shape every `iota_j` walk has:
a prefix of an opened telescope's annotations against the domains an
`instPisAt` run collects from a stored type.  The two packs supply
both sides; `defEqListW_of` does the fold. -/
theorem stmtWalk_of {env : Env} (m : EnvR env) {μ : CheckMode}
    {F : Nat} {φ : Name → Nat} {D : Nat}
    {nR : Name} {ciR : ConstantInfo} {cvR : ConstantVal}
    {nC : Name} {ciC : ConstantInfo} {cvj : ConstantVal}
    {k cnP : Nat} {fvsP : List Expr} {restP : Expr}
    {cdomsP : List Expr} {crestP : Expr}
    (hfR : env.find? nR = some ciR) (hcvR : ciR.toConstantVal = cvR)
    (hfC : env.find? nC = some ciC) (hcvC : ciC.toConstantVal = cvj)
    (hopenP : openPisAtFvars k cvR.type 0 = some (fvsP, restP))
    (hle : k ≤ D)
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type
      = some (cdomsP, crestP))
    (hde : DefEqListOk μ F env D ((fvsP.take cnP).map Expr.fvarTypeD)
      cdomsP) :
    DefEqListW μ env m.cval φ D
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP := by
  obtain ⟨hnfR, -, -, hbR, -⟩ := m.wf ciR (find?_mem hfR)
  rw [hcvR] at hnfR hbR
  have hLeft := opener_walk_pack m (φ := φ) hfR hcvR hnfR hbR hopenP hle
  have hFvar := opener_fvar_pack m (φ := φ) hnfR hbR hopenP hle
  obtain ⟨hwC, hbC, hLC, TC, hTC⟩ :=
    storedType_pack m (φ := φ) hfC D
  rw [hcvC] at hwC hbC hLC hTC
  have hRight := instPisAt_walk_pack m (φ := φ) hcinstP hwC hbC hLC
    (fun a ha => ⟨(hFvar a (List.mem_of_mem_take ha)).1,
      (hFvar a (List.mem_of_mem_take ha)).2.1,
      (hFvar a (List.mem_of_mem_take ha)).2.2.1⟩)
    (fun j y hy => (hFvar y
      (List.mem_of_mem_take (List.mem_of_getElem? hy))).2.2.2) hTC
  refine defEqListW_of m _ _ (fun e he => ?_) hde
  rcases List.mem_append.mp he with h' | h'
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h'
    obtain ⟨i, hi⟩ := List.getElem?_of_mem (List.mem_of_mem_take hx)
    exact hLeft i x hi
  · exact hRight e h'

/-- **The spine package** — the walk layer's *third* shape (the
convergence file's correction).  The index walk compares application
spine arguments, whose denotations come neither from an opening nor
from an `instPisAt` run but from `denote_mkAppN_inv`, which inverts a
denoting application into its head and a `DenoteSpine`.  The three
frames descend from the application's own by
`Expr.WScoped.getAppArgs`, `looseBVarsBounded_getAppArgs` and
`fvarLeaves_getAppArgs`. -/
theorem spine_walk_pack {env : Env} (m : EnvR env) {φ : Name → Nat}
    {D : Nat} {e : Expr} {v : VExpr}
    (hw : Expr.WScoped D e) (hb : e.looseBVarsBounded 0 = true)
    (hL : Expr.LeavesBounded e)
    (hd : denote m.cval env φ D e = some v) :
    ∀ a ∈ e.getAppArgs, Expr.WScoped D a ∧
      a.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded a ∧
      ∃ w, denote m.cval env φ D a = some w := by
  intro a ha
  refine ⟨hw.getAppArgs a ha, looseBVarsBounded_getAppArgs hb a ha,
    fun l hl => hL l (fvarLeaves_getAppArgs ha l hl), ?_⟩
  rw [← Expr.mkAppN_getApp e] at hd
  obtain ⟨vf, vs, -, hsp, -⟩ := denote_mkAppN_inv hd
  exact denoteSpine_mem_denotes hsp a ha

/-! ## `indDecl`, the front half: the member fold

`checkMemberVal` is `checkConstantVal` plus the model-artifact
conjuncts, so `memberValR_of` is `constantValR_of` plus four
inversions.  The fold's threaded valuation is **determined** —
`cvalModeled` at each member — so the bridge chooses nothing; it only
has to keep the recursion's `cval` in step with the environment. -/

set_option maxHeartbeats 2000000 in
/-- **A canonical rule's `iota_j` theorem, bridged** — the transpose
of `checkIotaThm` at the *stored* environment.  The shape pins are
pure equations on the destructured data and transcribe; the content is
`IotaWalksR`'s six rows, and each row is one `defEqListW_of` (or
`defEqAtW_of`) over a *left* package and a *right* package:

* *index* — the statement's `lhs` spine against the ctor residual's
  (`instPisAt_res_pack`, then `spine_walk_pack` on each);
* *field* — the statement's openers' annotations against the renamed
  ctor type's `instPisAt` domains;
* *prefix* — the same openers, taken, against the renamed
  *recursor* type's domains;
* *λ* — the rule telescope's openers (two openings, appended)
  against `instLamsAt`'s domains (`instLamsAt_walk_pack`);
* *rhs* — the statement's `rhs` against the renamed rule rhs applied
  to the whole opening (`mkAppN_walk_pack`);
* *sides* — `iotaSidesTyR_of`.

The recursor is taken at its **stored `recInfo`** rather than at a
bare `ConstantInfo`: the λ-row needs the rule's right-hand side to
*denote*, which is `EnvR.rec_rhs_denotes` and therefore needs the rule
to be a stored fireable one.  That is not a strengthening of what the
caller has — the iota fold walks exactly the stored rules. -/
theorem iotaThmR_of {env' envSelf : Env} (m : EnvR envSelf)
    {μ : CheckMode} {F : Nat} {f : Name → Name} {cvA cvj : ConstantVal}
    {mI rP cnP cnF j : Nat} {r : RecRule} {rhsA : Expr}
    {ciR ciC : ConstantInfo}
    (hrecSelf : envSelf.find? cvA.name = some ciR)
    (hcvRR : ciR.toConstantVal = cvA)
    (hrhsnf : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hrhsDen : ∀ φ : Name → Nat,
      ∃ V, denoteClosed m.cval envSelf φ rhsA = some V)
    (hctorSelf : envSelf.find? r.ctor = some ciC)
    (hcvC : ciC.toConstantVal = cvj)
    (hro : RenameOkT m.cval envSelf f)
    (htransfer : ∀ n ci, env'.find? n = some ci →
      ∃ ci', envSelf.find? n = some ci' ∧
        ci'.toConstantVal = ci.toConstantVal)
    (h : PlainChecked μ F env' envSelf f cvA mI rP cnP cnF j
      { r with rhs := rhsA } cvj) :
    IotaThmR μ F env' envSelf m.cval f cvA.name cvA.levelParams
      cvA.type mI rP j r cvj cnP cnF rhsA := by
  obtain ⟨thmName, cvt, ci, fvs, tbody, ℓA, αS, lhsS, rhsS, cdoms, cres,
    rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP, crest2, ldoms,
    lrest, hfthm, hcvt, hpin, hlpt, hopen, hheadEq, hargs3, hlhead,
    hlarity, hlpre, hmaj, hcstrip, hcinst, hclen, hdeIdx, hdeFld,
    hrinst, hdePre, hopenP, hcinstP, hdeP, hopenX, hlinst, hdeLam,
    hdeRhs, hty1, hty2, hty3⟩ := h
  subst hpin
  refine ⟨cvt, fvs, tbody, ?_, hlpt, hopen, ?_, ?_, ?_⟩
  · rw [Env.findCV?, hfthm, Option.map_some, hcvt]
  · rw [hheadEq]; rfl
  · rw [hargs3]; rfl
  · rw [hargs3]
    dsimp only
    refine ⟨by simpa using hlhead, by simpa using hlarity,
      by simpa using hlpre, by simpa using hmaj,
      hcstrip, cdoms, cres, rdoms, fvsP, cdomsP, crestP, xFvsP, restP,
      crest2, rrest, hcinst, hclen, hrinst, hopenP, hcinstP, hopenX,
      ldoms, lrest, hlinst, fun φ => ?_, ?_⟩
    · exact stmtWalk_of m hrecSelf hcvRR hctorSelf hcvC hopenP
        (by omega) hcinstP hdeP
    · intro φ
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      ---------------------------------------------------------------
      -- (a) the statement, transferred, and its opening at rP + cnF
      ---------------------------------------------------------------
      obtain ⟨ciT, hciT, hciTcv⟩ := htransfer _ _ hfthm
      have hTty : ciT.toConstantVal.type = cvt.type := by
        rw [hciTcv, hcvt]
      obtain ⟨hwS0, hbS0, hLS0, TS, hTS0⟩ :=
        storedType_pack m (φ := φ) hciT 0
      rw [hTty] at hwS0 hbS0 hLS0 hTS0
      have hstmt := opener_walk_pack_gen m (φ := φ) (D := rP + cnF)
        hwS0 hbS0 hLS0 hTS0 hopen (by omega)
      have hstmtF := opener_fvar_pack_gen m (φ := φ) (D := rP + cnF)
        hwS0 hbS0 hLS0 hTS0 hopen (by omega)
      obtain ⟨hwB, hbB, hLB, vB, hvB⟩ :=
        opener_body_pack_gen m (φ := φ) (D := rP + cnF)
          hwS0 hbS0 hLS0 hTS0 hopen (by omega)
      have hargs := spine_walk_pack m hwB hbB hLB hvB
      rw [hargs3] at hargs
      obtain ⟨hwα, hbα, hLα, vα, hvα⟩ := hargs αS (by simp)
      obtain ⟨hwl, hbl, hLl, vl, hvl⟩ := hargs lhsS (by simp)
      obtain ⟨hwr, hbr, hLr, vr, hvr⟩ := hargs rhsS (by simp)
      have hlhsA := spine_walk_pack m hwl hbl hLl hvl
      ---------------------------------------------------------------
      -- (b) the constructor type, renamed, at the statement's spine
      ---------------------------------------------------------------
      have hspF : ∀ a ∈ fvs.take cnP ++ fvs.drop rP,
          Expr.WScoped (rP + cnF) a ∧
          a.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded a ∧
          ∃ v, denote m.cval envSelf φ (rP + cnF) a = some v := by
        intro a ha
        rcases List.mem_append.mp ha with h' | h'
        · exact hstmtF a (List.mem_of_mem_take h')
        · exact hstmtF a (List.mem_of_mem_drop h')
      obtain ⟨hwC, hbC, hLC, TC, hTC⟩ :=
        renamedType_pack m (φ := φ) hro hctorSelf (rP + cnF)
      rw [hcvC] at hwC hbC hLC hTC
      obtain ⟨hwCr, hbCr, hLCr, vCr, hvCr⟩ :=
        instPisAt_res_pack m (φ := φ) hcinst hwC hbC hLC
          (fun a ha => ⟨(hspF a ha).1, (hspF a ha).2.1,
            (hspF a ha).2.2.1⟩)
          (fun _ y hy => (hspF y (List.mem_of_getElem? hy)).2.2.2) hTC
      have hcresA := spine_walk_pack m hwCr hbCr hLCr hvCr
      have hcdoms := instPisAt_walk_pack m (φ := φ) hcinst hwC hbC hLC
        (fun a ha => ⟨(hspF a ha).1, (hspF a ha).2.1,
          (hspF a ha).2.2.1⟩)
        (fun _ y hy => (hspF y (List.mem_of_getElem? hy)).2.2.2) hTC
      ---------------------------------------------------------------
      -- (c) the recursor type, at the statement's prefix (renamed)
      --     and at its own opening (unrenamed)
      ---------------------------------------------------------------
      obtain ⟨hwA, hbA, hLA, TA, hTA⟩ :=
        renamedType_pack m (φ := φ) hro hrecSelf (rP + cnF)
      rw [hcvRR] at hwA hbA hLA hTA
      have hrdoms := instPisAt_walk_pack m (φ := φ) hrinst hwA hbA hLA
        (fun a ha => ⟨(hstmtF a (List.mem_of_mem_take ha)).1,
          (hstmtF a (List.mem_of_mem_take ha)).2.1,
          (hstmtF a (List.mem_of_mem_take ha)).2.2.1⟩)
        (fun _ y hy =>
          (hstmtF y (List.mem_of_mem_take
            (List.mem_of_getElem? hy))).2.2.2) hTA
      obtain ⟨hwA0, hbA0, hLA0, TA0, hTA0⟩ :=
        storedType_pack m (φ := φ) hrecSelf 0
      rw [hcvRR] at hwA0 hbA0 hLA0 hTA0
      have hPF := opener_fvar_pack_gen m (φ := φ) (D := rP + cnF)
        hwA0 hbA0 hLA0 hTA0 hopenP (by omega)
      have hPFlow := opener_fvar_pack_gen m (φ := φ) (D := rP)
        hwA0 hbA0 hLA0 hTA0 hopenP (by omega)
      have hP := opener_walk_pack_gen m (φ := φ) (D := rP + cnF)
        hwA0 hbA0 hLA0 hTA0 hopenP (by omega)
      ---------------------------------------------------------------
      -- (d) the public field residual, opened at rP
      ---------------------------------------------------------------
      obtain ⟨hwC0, hbC0, hLC0, TC0, hTC0⟩ :=
        storedType_pack m (φ := φ) hctorSelf rP
      rw [hcvC] at hwC0 hbC0 hLC0 hTC0
      obtain ⟨hwX, hbX, hLX, vX, hvX⟩ :=
        instPisAt_res_pack m (φ := φ) hcinstP hwC0 hbC0 hLC0
          (fun a ha => ⟨(hPFlow a (List.mem_of_mem_take ha)).1,
            (hPFlow a (List.mem_of_mem_take ha)).2.1,
            (hPFlow a (List.mem_of_mem_take ha)).2.2.1⟩)
          (fun _ y hy => (hPFlow y (List.mem_of_mem_take
            (List.mem_of_getElem? hy))).2.2.2) hTC0
      have hX := opener_walk_pack_gen m (φ := φ) (D := rP + cnF)
        hwX hbX hLX hvX hopenX (by omega)
      have hXF := opener_fvar_pack_gen m (φ := φ) (D := rP + cnF)
        hwX hbX hLX hvX hopenX (by omega)
      ---------------------------------------------------------------
      -- (e) the rule's right-hand side, and its renamed application
      ---------------------------------------------------------------
      obtain ⟨VR0, hVR0⟩ := hrhsDen φ
      have hVR : ∀ D, denote m.cval envSelf φ D rhsA = some VR0 :=
        (denote_closedExprR m.cval_closed hrhsnf hrhsb hVR0).2
      have hRnf := hrhsnf
      have hRbd := hrhsb
      have hlamSp : ∀ a ∈ fvsP ++ xFvsP,
          Expr.WScoped (rP + cnF) a ∧
          a.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded a ∧
          ∃ v, denote m.cval envSelf φ (rP + cnF) a = some v := by
        intro a ha
        rcases List.mem_append.mp ha with h' | h'
        · exact hPF a h'
        · exact hXF a h'
      have hlamShape : ∀ (i : Nat) (x : Expr),
          (fvsP ++ xFvsP)[i]? = some x →
          ∃ nm ty, x = Expr.fvar i nm ty := by
        intro i x hx
        have hlenP : fvsP.length = rP := openPisAtFvars_length rP hopenP
        rcases Nat.lt_or_ge i rP with hlt | hge
        · rw [List.getElem?_append_left (by omega)] at hx
          obtain ⟨nm, ty, hxe⟩ :=
            openPisAtFvars_index rP cvA.type 0 hopenP i x hx
          exact ⟨nm, ty, by rw [hxe, Nat.zero_add]⟩
        · rw [List.getElem?_append_right (by omega), hlenP] at hx
          obtain ⟨nm, ty, hxe⟩ :=
            openPisAtFvars_index cnF crestP rP hopenX (i - rP) x hx
          refine ⟨nm, ty, ?_⟩
          rw [hxe, show rP + (i - rP) = i from by omega]
      have hldoms := instLamsAt_walk_pack m (φ := φ) (D := rP + cnF)
        hlinst hlamShape
        (Expr.WScoped.of_not_hasFvar hRnf) hRbd
        (Expr.LeavesBounded.of_not_hasFvar hRnf)
        (fun a ha => ⟨(hlamSp a ha).1, (hlamSp a ha).2.1,
          (hlamSp a ha).2.2.1⟩) (hVR 0)
        (by
          rw [List.length_append,
            openPisAtFvars_length rP hopenP,
            openPisAtFvars_length cnF hopenX]
          omega)

      obtain ⟨hwRhs, hbRhs, hLRhs, vRhs, hvRhs⟩ :=
        mkAppN_walk_pack m (φ := φ) (g := Expr.renameConsts f rhsA)
          (as := fvs)
          (wscoped_renameConsts _
            (Expr.WScoped.mono (Nat.zero_le (rP + cnF))
              (Expr.WScoped.of_not_hasFvar hRnf)))
          (by rw [looseBVarsBounded_renameConsts]; exact hRbd)
          (leavesBounded_renameConsts _
            (Expr.LeavesBounded.of_not_hasFvar hRnf))
          (fun a ha => hstmtF a ha)
          (by rw [denote_renameConsts hro]; exact hVR (rP + cnF))
      ---------------------------------------------------------------
      -- the six rows
      ---------------------------------------------------------------
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- 1. the index arguments against the residual's canonical tuple
        refine defEqListW_of m _ _ (fun e he => ?_) hdeIdx
        rcases List.mem_append.mp he with h' | h'
        · exact hlhsA e (List.mem_of_mem_drop (List.mem_of_mem_take h'))
        · exact hcresA e (List.mem_of_mem_drop h')
      · -- 2. the field annotations against the constructor domains
        refine defEqListW_of m _ _ (fun e he => ?_) hdeFld
        rcases List.mem_append.mp he with h' | h'
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h'
          obtain ⟨i, hi⟩ :=
            List.getElem?_of_mem (List.mem_of_mem_drop hx)
          exact hstmt i x hi
        · exact hcdoms e (List.mem_of_mem_drop h')
      · -- 3. the prefix annotations against the recursor's domains
        refine defEqListW_of m _ _ (fun e he => ?_) hdePre
        rcases List.mem_append.mp he with h' | h'
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h'
          obtain ⟨i, hi⟩ :=
            List.getElem?_of_mem (List.mem_of_mem_take hx)
          exact hstmt i x hi
        · exact hrdoms e h'
      · -- 4. the rule telescope's annotations against its λ domains
        refine defEqListW_of m _ _ (fun e he => ?_) hdeLam
        rcases List.mem_append.mp he with h' | h'
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h'
          rcases List.mem_append.mp hx with h'' | h''
          · obtain ⟨i, hi⟩ := List.getElem?_of_mem h''
            exact hP i x hi
          · obtain ⟨i, hi⟩ := List.getElem?_of_mem h''
            exact hX i x hi
        · exact hldoms e h'
      · -- 5. the statement's right side against the applied rhs
        exact defEqAtW_of m hwr hbr hLr hwRhs hbRhs hLRhs hvr hvRhs
          hdeRhs
      · -- 6. the two sides' types against the statement's `α`
        obtain ⟨tl, hil, hdl⟩ := hty1
        obtain ⟨tr, hir, hdr⟩ := hty2
        exact iotaSidesTyR_of m hwα hbα hLα hwl hbl hLl hwr hbr hLr
          hvα hvl hvr hil hdl hir hdr

set_option maxHeartbeats 4000000 in
/-- **A nested-auxiliary rule's `iota_j` theorem, bridged** — the
transpose of `checkIotaThmN`.  Structurally `iotaThmR_of` at a
different constructor spine and a level-instantiated constructor type,
plus a seventh walk (`TypedListW`, not `DefEqListW`) over the stored
parameter pins.

The pins are the only inputs that are neither stored types nor
openers, and they appear at **two spellings** that no transport
relates — `denote` is `none` on a loose `.bvar`, so the `instSpine`
that closes a pin is load-bearing and it closes it at two different
spines:

* `pinsP` (recursor-type openers, unrenamed) denotes because the
  checker *inferred its type*: `typedListOk_infer` extracts the
  verdict, `denote_of_inferR` converts it, at the context
  `openPisAtFvars_ctxOkR` builds and `CtxOkR.of_cover` transfers;
* `pinsF` (statement openers, renamed) denotes because the statement's
  own **major** does: `hmaj` is an `ErasedEq` to the constructor
  applied to `pinsF ++ xFvs`, and `denote_erasedEq` moves the
  major's denotation across.

Their three *syntactic* facts are not `ErasedEq`-transportable
(erasure drops `fvar` annotations, `WScoped` does not), so both
spellings take them directly from `instSpine_pin_pack`. -/
theorem iotaThmNR_of {env' envSelf : Env} (m : EnvR envSelf)
    {μ : CheckMode} {F : Nat} {f : Name → Name} {cvA cvj : ConstantVal}
    {mI rP cnP cnF j : Nat} {r : RecRule} {rhsA : Expr}
    {ciR ciC : ConstantInfo}
    {lvls : List Level} {pins : List Expr}
    (hrecSelf : envSelf.find? cvA.name = some ciR)
    (hcvRR : ciR.toConstantVal = cvA)
    (hrhsnf : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hrhsDen : ∀ φ : Name → Nat,
      ∃ V, denoteClosed m.cval envSelf φ rhsA = some V)
    (hctorSelf : envSelf.find? r.ctor = some ciC)
    (hcvC : ciC.toConstantVal = cvj)
    (hro : RenameOkT m.cval envSelf f)
    (htransfer : ∀ n ci, env'.find? n = some ci →
      ∃ ci', envSelf.find? n = some ci' ∧
        ci'.toConstantVal = ci.toConstantVal)
    (hshape : nestedRuleShape env' envSelf cvA.name cvA.levelParams
      cvA.type mI rP cnP j = some (lvls, pins))
    (h : NestedChecked μ F env' envSelf f cvA mI rP cnP cnF j
      { r with rhs := rhsA } cvj lvls pins) :
    IotaThmNR μ F env' envSelf m.cval f cvA.name cvA.levelParams
      cvA.type mI rP j r cvj cnP cnF rhsA lvls pins := by
  obtain ⟨thmName, cvt, ci, fvs, tbody, ℓA, αS, lhsS, rhsS, cdoms, cres,
    rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP, crest2, ldoms,
    lrest, hfthm, hcvt, hpin, hlpt, hopen, hheadEq, hargs3, hlhead,
    hlarity, hlpre, hmaj, hcstrip, hcinst, hclen, hdeIdx, hdeFld,
    hrinst, hdePre, hopenP, hannP, hcinstP, htypedP, hopenX, hcrestLen,
    hlinst, hdeLam, hdeRhs, hty1, hty2, hty3⟩ := h
  subst hpin
  refine ⟨hshape, cvt, fvs, tbody, ?_, hlpt, hopen, ?_, ?_, ?_⟩
  · rw [Env.findCV?, hfthm, Option.map_some, hcvt]
  · rw [hheadEq]; rfl
  · rw [hargs3]; rfl
  · rw [hargs3]
    dsimp only
    refine ⟨by simpa using hlhead, by simpa using hlarity,
      by simpa using hlpre, hmaj, ?_,
      cdoms, cres, rdoms, rrest, fvsP, restP, cdomsP, crestP, xFvsP,
      crest2, hcinst, hclen, hrinst, hopenP,
      ⟨hannP, hcinstP, hopenX, by simpa using hcrestLen⟩,
      ldoms, lrest, hlinst, ?_, ?_⟩
    · obtain ⟨bsC0, cbody0, Dc, usc, hs1, hs2⟩ := hcstrip
      exact ⟨bsC0, cbody0, hs1, by rw [hs2]⟩
    · -- the pins' typed walk
      intro φ
      obtain ⟨hwA0, hbA0, hLA0, TA0, hTA0⟩ :=
        storedType_pack m (φ := φ) hrecSelf 0
      rw [hcvRR] at hwA0 hbA0 hLA0 hTA0
      obtain ⟨hAnf, -, -, hAbd, -⟩ := m.wf _ (find?_mem hrecSelf)
      rw [hcvRR] at hAnf hAbd
      have hPF := opener_fvar_pack_gen m (φ := φ) (D := rP + cnF)
        hwA0 hbA0 hLA0 hTA0 hopenP (by omega)
      have hfvsPlen : fvsP.length = rP :=
        openPisAtFvars_length rP hopenP
      have htkP : (fvsP.take rP).length = rP := by
        rw [List.length_take, hfvsPlen]; omega
      obtain ⟨-, -, hpinsWf, -⟩ := nestedRuleShape_inv hshape
      have hpinPsyn : ∀ x ∈ pins.map (fun p =>
          Expr.instSpine (fvsP.take rP) (rP - 1) p),
          Expr.WScoped (rP + cnF) x ∧
          x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        have h1 := instSpine_pin_pack (D := rP + cnF)
          (sp := fvsP.take rP) (p := p) (hpinsWf p hp).1
          (by rw [htkP]; exact (hpinsWf p hp).2.2.2)
          (fun a ha => ⟨(hPF a (List.mem_of_mem_take ha)).1,
            (hPF a (List.mem_of_mem_take ha)).2.1,
            (hPF a (List.mem_of_mem_take ha)).2.2.1⟩)
        rw [htkP] at h1
        exact h1
      obtain ⟨Δ₀, hΔ₀len, -, hΔ₀fvs⟩ :=
        openPisAtFvars_ctxOkR (μ := μ) (cval := m.cval)
          (env := envSelf) (φ := φ) m.cval_closed rP (Δ := [])
          hopenP (CtxOkR.nil
            (Expr.fvarLeaves_eq_nil_of_not_hasFvar hAnf)) hTA0 hwA0
      have hΔlen : (List.replicate cnF (VExpr.sort .zero)
          ++ (Δ₀ ++ [])).length = rP + cnF := by
        rw [List.length_append, List.length_replicate,
          List.length_append, hΔ₀len]
        simp
        omega
      have hΔfvs : ∀ x ∈ fvsP,
          CtxOkR μ m.cval envSelf φ (rP + cnF)
            (List.replicate cnF (VExpr.sort .zero)
              ++ (Δ₀ ++ [])) x := by
        intro x hx
        have h1 := CtxOkR.weakenN (cval := m.cval) m.cval_closed
          (List.replicate cnF (VExpr.sort .zero)) (hΔ₀fvs x hx)
        rw [List.length_replicate] at h1
        rw [show rP + cnF = 0 + rP + cnF from by omega]
        exact h1
      have hpinPden : ∀ x ∈ pins.map (fun p =>
          Expr.instSpine (fvsP.take rP) (rP - 1) p),
          ∃ v, denote m.cval envSelf φ (rP + cnF) x = some v := by
        intro x hx
        obtain ⟨ty, hi⟩ := typedListOk_infer htypedP x hx
        obtain ⟨p, hp, hxe⟩ := List.mem_map.mp hx
        refine denote_of_inferR m hi (hpinPsyn x hx).1
          (hpinPsyn x hx).2.1 (hpinPsyn x hx).2.2
          (CtxOkR.of_cover (L := fvsP.take rP) hΔlen
            (fun y hy => hΔfvs y (List.mem_of_mem_take hy))
            (fun l hl => ?_))
        rw [← hxe] at hl
        rcases fvarLeaves_instSpine _ hl with h' | ⟨a, ha, hla⟩
        · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
            (hpinsWf p hp).1] at h'
          exact nomatch h'
        · exact ⟨a, ha, hla⟩
      obtain ⟨hwCl, hbCl, hLCl, -⟩ :=
        frame_declTypeR (cval := m.cval) (φ := φ) (mode := μ) m.wf
          hctorSelf lvls (rP + cnF)
          (Δ := List.replicate (rP + cnF) (VExpr.sort .zero))
          (by rw [List.length_replicate])
      rw [hcvC] at hwCl hbCl hLCl
      obtain ⟨TCl, -, -, hTCl⟩ :=
        denote_declTypeR m φ m.cval_closed hctorSelf lvls (rP + cnF)
      rw [hcvC] at hTCl
      have hcdomsP := instPisAt_walk_pack m (φ := φ) hcinstP
        hwCl hbCl hLCl hpinPsyn
        (fun _ y hy => hpinPden y (List.mem_of_getElem? hy)) hTCl
      exact typedListW_of m _ _ (fun e he => by
        rcases List.mem_append.mp he with h' | h'
        · exact ⟨(hpinPsyn e h').1, (hpinPsyn e h').2.1,
            (hpinPsyn e h').2.2, hpinPden e h'⟩
        · exact hcdomsP e h') htypedP
    · -- the six rows
      intro φ
      obtain ⟨-, -, hpinsWf, -⟩ := nestedRuleShape_inv hshape
      obtain ⟨hAnf, -, -, hAbd, -⟩ := m.wf _ (find?_mem hrecSelf)
      rw [hcvRR] at hAnf hAbd
      ---------------------------------------------------------------
      -- (a) the statement, transferred, and its opening
      ---------------------------------------------------------------
      obtain ⟨ciT, hciT, hciTcv⟩ := htransfer _ _ hfthm
      have hTty : ciT.toConstantVal.type = cvt.type := by
        rw [hciTcv, hcvt]
      obtain ⟨hwS0, hbS0, hLS0, TS, hTS0⟩ :=
        storedType_pack m (φ := φ) hciT 0
      rw [hTty] at hwS0 hbS0 hLS0 hTS0
      have hstmt := opener_walk_pack_gen m (φ := φ) (D := rP + cnF)
        hwS0 hbS0 hLS0 hTS0 hopen (by omega)
      have hstmtF := opener_fvar_pack_gen m (φ := φ) (D := rP + cnF)
        hwS0 hbS0 hLS0 hTS0 hopen (by omega)
      obtain ⟨hwB, hbB, hLB, vB, hvB⟩ :=
        opener_body_pack_gen m (φ := φ) (D := rP + cnF)
          hwS0 hbS0 hLS0 hTS0 hopen (by omega)
      have hargs := spine_walk_pack m hwB hbB hLB hvB
      rw [hargs3] at hargs
      obtain ⟨hwα, hbα, hLα, vα, hvα⟩ := hargs αS (by simp)
      obtain ⟨hwl, hbl, hLl, vl, hvl⟩ := hargs lhsS (by simp)
      obtain ⟨hwr, hbr, hLr, vr, hvr⟩ := hargs rhsS (by simp)
      have hlhsA := spine_walk_pack m hwl hbl hLl hvl
      have hfvslen : fvs.length = rP + cnF :=
        openPisAtFvars_length (rP + cnF) hopen
      have htkS : (fvs.take rP).length = rP := by
        rw [List.length_take, hfvslen]; omega
      ---------------------------------------------------------------
      -- (b) the major, and the renamed pins it denotes
      ---------------------------------------------------------------
      obtain ⟨-, -, -, vM, hvM⟩ :=
        hlhsA _ (getLastD_mem (d := Expr.bvar 0) hlarity)
      rw [denote_erasedEq hmaj (rP + cnF)] at hvM
      obtain ⟨-, vs, -, hspM, -⟩ := denote_mkAppN_inv hvM
      have hpinFden := denoteSpine_mem_denotes hspM
      have hpinFsyn : ∀ x ∈ pins.map (fun p =>
          Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)),
          Expr.WScoped (rP + cnF) x ∧
          x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        have h1 := instSpine_pin_pack (D := rP + cnF)
          (sp := fvs.take rP) (p := p.renameConsts f)
          (by rw [hasFvar_renameConsts]; exact (hpinsWf p hp).1)
          (by rw [looseBVarsBounded_renameConsts, htkS]
              exact (hpinsWf p hp).2.2.2)
          (fun a ha => ⟨(hstmtF a (List.mem_of_mem_take ha)).1,
            (hstmtF a (List.mem_of_mem_take ha)).2.1,
            (hstmtF a (List.mem_of_mem_take ha)).2.2.1⟩)
        rw [htkS] at h1
        exact h1
      have hspF : ∀ a ∈ pins.map (fun p =>
            Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f))
            ++ fvs.drop rP,
          Expr.WScoped (rP + cnF) a ∧
          a.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded a ∧
          ∃ v, denote m.cval envSelf φ (rP + cnF) a = some v := by
        intro a ha
        rcases List.mem_append.mp ha with h' | h'
        · exact ⟨(hpinFsyn a h').1, (hpinFsyn a h').2.1,
            (hpinFsyn a h').2.2, hpinFden a (by
              exact List.mem_append_left _ h')⟩
        · exact hstmtF a (List.mem_of_mem_drop h')
      ---------------------------------------------------------------
      -- (c) the constructor type at `lvls`, renamed
      ---------------------------------------------------------------
      obtain ⟨hwC1, hbC1, hLC1, -⟩ :=
        frame_declTypeR (cval := m.cval) (φ := φ) (mode := μ) m.wf
          hctorSelf lvls (rP + cnF)
          (Δ := List.replicate (rP + cnF) (VExpr.sort .zero))
          (by rw [List.length_replicate])
      rw [hcvC] at hwC1 hbC1 hLC1
      obtain ⟨TC1, -, -, hTC1⟩ :=
        denote_declTypeR m φ m.cval_closed hctorSelf lvls (rP + cnF)
      rw [hcvC] at hTC1
      have hwCR := wscoped_renameConsts (f := f) _ hwC1
      have hbCR : ((cvj.type.instantiateLevelParams cvj.levelParams
          lvls).renameConsts f).looseBVarsBounded 0 = true := by
        rw [looseBVarsBounded_renameConsts]; exact hbC1
      have hLCR := leavesBounded_renameConsts (f := f) _ hLC1
      have hTCR : denote m.cval envSelf φ (rP + cnF)
          ((cvj.type.instantiateLevelParams cvj.levelParams
            lvls).renameConsts f) = some TC1 := by
        rw [denote_renameConsts hro]; exact hTC1
      obtain ⟨hwCr, hbCr, hLCr, vCr, hvCr⟩ :=
        instPisAt_res_pack m (φ := φ) hcinst hwCR hbCR hLCR
          (fun a ha => ⟨(hspF a ha).1, (hspF a ha).2.1,
            (hspF a ha).2.2.1⟩)
          (fun _ y hy => (hspF y (List.mem_of_getElem? hy)).2.2.2) hTCR
      have hcresA := spine_walk_pack m hwCr hbCr hLCr hvCr
      have hcdoms := instPisAt_walk_pack m (φ := φ) hcinst
        hwCR hbCR hLCR
        (fun a ha => ⟨(hspF a ha).1, (hspF a ha).2.1,
          (hspF a ha).2.2.1⟩)
        (fun _ y hy => (hspF y (List.mem_of_getElem? hy)).2.2.2) hTCR
      ---------------------------------------------------------------
      -- (d) the recursor type: renamed at the prefix, own opening
      ---------------------------------------------------------------
      obtain ⟨hwA, hbA, hLA, TA, hTA⟩ :=
        renamedType_pack m (φ := φ) hro hrecSelf (rP + cnF)
      rw [hcvRR] at hwA hbA hLA hTA
      have hrdoms := instPisAt_walk_pack m (φ := φ) hrinst hwA hbA hLA
        (fun a ha => ⟨(hstmtF a (List.mem_of_mem_take ha)).1,
          (hstmtF a (List.mem_of_mem_take ha)).2.1,
          (hstmtF a (List.mem_of_mem_take ha)).2.2.1⟩)
        (fun _ y hy =>
          (hstmtF y (List.mem_of_mem_take
            (List.mem_of_getElem? hy))).2.2.2) hTA
      obtain ⟨hwA0, hbA0, hLA0, TA0, hTA0⟩ :=
        storedType_pack m (φ := φ) hrecSelf 0
      rw [hcvRR] at hwA0 hbA0 hLA0 hTA0
      have hPF := opener_fvar_pack_gen m (φ := φ) (D := rP + cnF)
        hwA0 hbA0 hLA0 hTA0 hopenP (by omega)
      have hPFlow := opener_fvar_pack_gen m (φ := φ) (D := rP)
        hwA0 hbA0 hLA0 hTA0 hopenP (by omega)
      have hP := opener_walk_pack_gen m (φ := φ) (D := rP + cnF)
        hwA0 hbA0 hLA0 hTA0 hopenP (by omega)
      have hfvsPlen : fvsP.length = rP :=
        openPisAtFvars_length rP hopenP
      have htkP : (fvsP.take rP).length = rP := by
        rw [List.length_take, hfvsPlen]; omega
      ---------------------------------------------------------------
      -- (e) the public pins at depth rP, and the field residual
      ---------------------------------------------------------------
      have hpinPlow : ∀ x ∈ pins.map (fun p =>
          Expr.instSpine (fvsP.take rP) (rP - 1) p),
          Expr.WScoped rP x ∧
          x.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded x := by
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        have h1 := instSpine_pin_pack (D := rP)
          (sp := fvsP.take rP) (p := p) (hpinsWf p hp).1
          (by rw [htkP]; exact (hpinsWf p hp).2.2.2)
          (fun a ha => ⟨(hPFlow a (List.mem_of_mem_take ha)).1,
            (hPFlow a (List.mem_of_mem_take ha)).2.1,
            (hPFlow a (List.mem_of_mem_take ha)).2.2.1⟩)
        rw [htkP] at h1
        exact h1
      have hpinPhigh : ∀ x ∈ pins.map (fun p =>
          Expr.instSpine (fvsP.take rP) (rP - 1) p),
          ∃ v, denote m.cval envSelf φ (rP + cnF) x = some v := by
        intro x hx
        obtain ⟨ty, hi⟩ := typedListOk_infer htypedP x hx
        obtain ⟨p, hp, hxe⟩ := List.mem_map.mp hx
        obtain ⟨Δ₀, hΔ₀len, -, hΔ₀fvs⟩ :=
          openPisAtFvars_ctxOkR (μ := μ) (cval := m.cval)
            (env := envSelf) (φ := φ) m.cval_closed rP (Δ := [])
            hopenP (CtxOkR.nil
              (Expr.fvarLeaves_eq_nil_of_not_hasFvar hAnf)) hTA0 hwA0
        have hΔlen : (List.replicate cnF (VExpr.sort .zero)
            ++ (Δ₀ ++ [])).length = rP + cnF := by
          rw [List.length_append, List.length_replicate,
            List.length_append, hΔ₀len]
          simp
          omega
        refine denote_of_inferR m hi
          (Expr.WScoped.mono (by omega) (hpinPlow x hx).1)
          (hpinPlow x hx).2.1 (hpinPlow x hx).2.2
          (CtxOkR.of_cover (L := fvsP.take rP) hΔlen
            (fun y hy => ?_) (fun l hl => ?_))
        · have h1 := CtxOkR.weakenN (cval := m.cval) m.cval_closed
            (List.replicate cnF (VExpr.sort .zero))
            (hΔ₀fvs y (List.mem_of_mem_take hy))
          rw [List.length_replicate] at h1
          rw [show rP + cnF = 0 + rP + cnF from by omega]
          exact h1
        · rw [← hxe] at hl
          rcases fvarLeaves_instSpine _ hl with h' | ⟨a, ha, hla⟩
          · rw [Expr.fvarLeaves_eq_nil_of_not_hasFvar
              (hpinsWf p hp).1] at h'
            exact nomatch h'
          · exact ⟨a, ha, hla⟩
      have hpinPden : ∀ x ∈ pins.map (fun p =>
          Expr.instSpine (fvsP.take rP) (rP - 1) p),
          ∃ v, denote m.cval envSelf φ rP x = some v := fun x hx =>
        opener_denotes_below m (hpinPlow x hx).1.fvarsBelow
          (by omega) (hpinPhigh x hx).choose_spec
      obtain ⟨hwC0, hbC0, hLC0, -⟩ :=
        frame_declTypeR (cval := m.cval) (φ := φ) (mode := μ) m.wf
          hctorSelf lvls rP
          (Δ := List.replicate rP (VExpr.sort .zero))
          (by rw [List.length_replicate])
      rw [hcvC] at hwC0 hbC0 hLC0
      obtain ⟨TC0, -, -, hTC0⟩ :=
        denote_declTypeR m φ m.cval_closed hctorSelf lvls rP
      rw [hcvC] at hTC0
      obtain ⟨hwX, hbX, hLX, vX, hvX⟩ :=
        instPisAt_res_pack m (φ := φ) hcinstP hwC0 hbC0 hLC0
          hpinPlow
          (fun _ y hy => hpinPden y (List.mem_of_getElem? hy)) hTC0
      have hX := opener_walk_pack_gen m (φ := φ) (D := rP + cnF)
        hwX hbX hLX hvX hopenX (by omega)
      have hXF := opener_fvar_pack_gen m (φ := φ) (D := rP + cnF)
        hwX hbX hLX hvX hopenX (by omega)
      ---------------------------------------------------------------
      -- (f) the rule's right-hand side, and its renamed application
      ---------------------------------------------------------------
      obtain ⟨VR0, hVR0⟩ := hrhsDen φ
      have hVR : ∀ D, denote m.cval envSelf φ D rhsA = some VR0 :=
        (denote_closedExprR m.cval_closed hrhsnf hrhsb hVR0).2
      have hRnf := hrhsnf
      have hRbd := hrhsb
      have hlamSp : ∀ a ∈ fvsP ++ xFvsP,
          Expr.WScoped (rP + cnF) a ∧
          a.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded a ∧
          ∃ v, denote m.cval envSelf φ (rP + cnF) a = some v := by
        intro a ha
        rcases List.mem_append.mp ha with h' | h'
        · exact hPF a h'
        · exact hXF a h'
      have hlamShape : ∀ (i : Nat) (x : Expr),
          (fvsP ++ xFvsP)[i]? = some x →
          ∃ nm ty, x = Expr.fvar i nm ty := by
        intro i x hx
        rcases Nat.lt_or_ge i rP with hlt | hge
        · rw [List.getElem?_append_left (by omega)] at hx
          obtain ⟨nm, ty, hxe⟩ :=
            openPisAtFvars_index rP cvA.type 0 hopenP i x hx
          exact ⟨nm, ty, by rw [hxe, Nat.zero_add]⟩
        · rw [List.getElem?_append_right (by omega), hfvsPlen] at hx
          obtain ⟨nm, ty, hxe⟩ :=
            openPisAtFvars_index cnF crestP rP hopenX (i - rP) x hx
          refine ⟨nm, ty, ?_⟩
          rw [hxe, show rP + (i - rP) = i from by omega]
      have hldoms := instLamsAt_walk_pack m (φ := φ) (D := rP + cnF)
        hlinst hlamShape
        (Expr.WScoped.of_not_hasFvar hRnf) hRbd
        (Expr.LeavesBounded.of_not_hasFvar hRnf)
        (fun a ha => ⟨(hlamSp a ha).1, (hlamSp a ha).2.1,
          (hlamSp a ha).2.2.1⟩) (hVR 0)
        (by
          rw [List.length_append, hfvsPlen,
            openPisAtFvars_length cnF hopenX]
          omega)
      obtain ⟨hwRhs, hbRhs, hLRhs, vRhs, hvRhs⟩ :=
        mkAppN_walk_pack m (φ := φ) (g := Expr.renameConsts f rhsA)
          (as := fvs)
          (wscoped_renameConsts _
            (Expr.WScoped.mono (Nat.zero_le (rP + cnF))
              (Expr.WScoped.of_not_hasFvar hRnf)))
          (by rw [looseBVarsBounded_renameConsts]; exact hRbd)
          (leavesBounded_renameConsts _
            (Expr.LeavesBounded.of_not_hasFvar hRnf))
          (fun a ha => hstmtF a ha)
          (by rw [denote_renameConsts hro]; exact hVR (rP + cnF))
      ---------------------------------------------------------------
      -- the six rows
      ---------------------------------------------------------------
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · refine defEqListW_of m _ _ (fun e he => ?_) hdeIdx
        rcases List.mem_append.mp he with h' | h'
        · exact hlhsA e (List.mem_of_mem_drop (List.mem_of_mem_take h'))
        · exact hcresA e (List.mem_of_mem_drop h')
      · refine defEqListW_of m _ _ (fun e he => ?_) hdeFld
        rcases List.mem_append.mp he with h' | h'
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h'
          obtain ⟨i, hi⟩ :=
            List.getElem?_of_mem (List.mem_of_mem_drop hx)
          exact hstmt i x hi
        · exact hcdoms e (List.mem_of_mem_drop h')
      · refine defEqListW_of m _ _ (fun e he => ?_) hdePre
        rcases List.mem_append.mp he with h' | h'
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h'
          obtain ⟨i, hi⟩ :=
            List.getElem?_of_mem (List.mem_of_mem_take hx)
          exact hstmt i x hi
        · exact hrdoms e h'
      · refine defEqListW_of m _ _ (fun e he => ?_) hdeLam
        rcases List.mem_append.mp he with h' | h'
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h'
          rcases List.mem_append.mp hx with h'' | h''
          · obtain ⟨i, hi⟩ := List.getElem?_of_mem h''
            exact hP i x hi
          · obtain ⟨i, hi⟩ := List.getElem?_of_mem h''
            exact hX i x hi
        · exact hldoms e h'
      · exact defEqAtW_of m hwr hbr hLr hwRhs hbRhs hLRhs hvr hvRhs
          hdeRhs
      · obtain ⟨tl, hil, hdl⟩ := hty1
        obtain ⟨tr, hir, hdr⟩ := hty2
        exact iotaSidesTyR_of m hwα hbα hLα hwl hbl hLl hwr hbr hLr
          hvα hvl hvr hil hdl hir hdr

set_option maxHeartbeats 1600000 in
/-- **One modeled recursor rule, bridged** (`checkIotaRule`).  The
shape data comes from `checkIotaRule_inv`'s kit; the fire-mode
dispatch runs on `RuleChecked`'s `plain ↔ recRulePlain` equivalence
and its nested clause, into `iotaThmR_of` / `iotaThmNR_of`.

The rule's annotated right-hand side denotes *because the fold
inferred its type* — `RuleChecked` carries the verdict at depth `0`
and `InferClaimsR` converts it at the empty context.  It is emphatically
not `EnvR.rec_rhs_denotes`: the rules are being checked against the
**provisional** environment, where they are not yet stored. -/
theorem iotaRuleR_of {env' envSelf : Env} (m : EnvR envSelf)
    {μ : CheckMode} {F : Nat} {f : Name → Name} {cvA : ConstantVal}
    {mI rP j : Nat} {r r' : RecRule} {ciR : ConstantInfo}
    (hrecSelf : envSelf.find? cvA.name = some ciR)
    (hcvRR : ciR.toConstantVal = cvA)
    (hro : RenameOkT m.cval envSelf f)
    (htransfer : ∀ n ci, env'.find? n = some ci →
      ∃ ci', envSelf.find? n = some ci' ∧
        ci'.toConstantVal = ci.toConstantVal)
    (h : checkIotaRule μ (fueledOps μ F) env' envSelf f cvA.name
      cvA.levelParams cvA.type mI rP j r = .ok r') :
    IotaRuleR μ F env' envSelf m.cval f cvA.name cvA.levelParams
      cvA.type mI rP j r r' := by
  obtain ⟨hkit, hrnf, hrb, cnP0, fire0, rhsA0, hann0, hr'eq,
    hinert, hnestShape⟩ := checkIotaRule_inv (cvA := cvA) h
  obtain ⟨cvj, cnP, cnF, raw, rhsTy, rbinders, rbody, hfc, hnf, hcp,
    hplainIff, hnested, hrawnf, hrawb, hrawann, hrhsnf, hrhsb, hrlp,
    hrres, hstripEq, hity, hplainKit⟩ := hkit
  subst hr'eq
  dsimp only at hfc hnf hcp hplainIff hnested hrhsnf hrhsb hplainKit
  dsimp only at hrlp hrres hstripEq hity
  subst hcp
  -- the annotated right-hand side denotes, and infers, at the empty
  -- context: the fold's own inference verdict, not a stored rule
  have hRden : ∀ φ : Name → Nat, ∃ Rv t,
      denoteClosed m.cval envSelf φ rhsA0 = some Rv ∧
      Infer μ envSelf m.cval φ [] Rv t := by
    intro φ
    obtain ⟨-, -, -, ihi⟩ := checkBridge m φ F
    obtain ⟨hw, hb, hL, hC⟩ :=
      closed0_framesR (μ := μ) (cval := m.cval) (env := envSelf)
        (φ := φ) hrhsnf hrhsb
    obtain ⟨v, tv, hv, -, T', hI, -⟩ := ihi hity hw hb hL hC
    exact ⟨v, T', hv, hI⟩
  have hrhsDen : ∀ φ : Name → Nat,
      ∃ V, denoteClosed m.cval envSelf φ rhsA0 = some V := by
    intro φ
    obtain ⟨Rv, t, hv, -⟩ := hRden φ
    exact ⟨Rv, hv⟩
  obtain ⟨ciC, hciC, hcvC⟩ := htransfer _ _ hfc
  have hcvC' : ciC.toConstantVal = cvj := hcvC
  refine ⟨cvj, cnP0, cnF, rhsA0, hfc, hnf, hrb, hrnf,
    hann0, hrlp, hrres, (by rw [hstripEq]; rfl), hRden,
    fire0, rfl, ?_⟩
  by_cases hplain :
      Expr.recRulePlain cvA.type mI rP cnP0 = true
  · refine Or.inl ⟨hplain, hplainIff.mpr hplain, ?_⟩
    exact iotaThmR_of m hrecSelf hcvRR hrhsnf hrhsb hrhsDen
      hciC hcvC' hro htransfer (hplainKit hplain)
  · have hplainF : Expr.recRulePlain cvA.type mI rP cnP0 = false := by
      revert hplain
      cases Expr.recRulePlain cvA.type mI rP cnP0 <;> simp
    refine Or.inr ⟨hplainF, ?_⟩
    cases hf : fire0 with
    | plain =>
      exact absurd (hplainIff.mp hf) (by rw [hplainF]; simp)
    | inert => exact Or.inl ⟨rfl, hinert hf⟩
    | nested lvls pins =>
      refine Or.inr ⟨lvls, pins, rfl, ?_⟩
      obtain ⟨-, -, -, -, -, hkitN⟩ := hnested lvls pins hf
      exact iotaThmNR_of m hrecSelf hcvRR hrhsnf hrhsb hrhsDen
        hciC hcvC' hro htransfer (hnestShape lvls pins hf) hkitN

theorem iotaRulesR_of {env' envSelf : Env} (m : EnvR envSelf)
    {μ : CheckMode} {F : Nat} {f : Name → Name} {cvA : ConstantVal}
    {mI rP : Nat} {ciR : ConstantInfo}
    (hrecSelf : envSelf.find? cvA.name = some ciR)
    (hcvRR : ciR.toConstantVal = cvA)
    (hro : RenameOkT m.cval envSelf f)
    (htransfer : ∀ n ci, env'.find? n = some ci →
      ∃ ci', envSelf.find? n = some ci' ∧
        ci'.toConstantVal = ci.toConstantVal) :
    ∀ (j : Nat) (rules rules' : List RecRule),
      checkIotaRules μ (fueledOps μ F) env' envSelf f cvA.name
        cvA.levelParams cvA.type mI rP j rules = .ok rules' →
      IotaRulesR μ F env' envSelf m.cval f cvA.name cvA.levelParams
        cvA.type mI rP j rules rules' := by
  intro j rules
  induction rules generalizing j with
  | nil =>
    intro rules' h
    simp only [checkIotaRules, pure, Except.pure,
      Except.ok.injEq] at h
    exact h.symm
  | cons r rest ih =>
    intro rules' h
    simp only [checkIotaRules, Bind.bind, Except.bind] at h
    revert h
    cases hr1 : checkIotaRule μ (fueledOps μ F) env' envSelf f
        cvA.name cvA.levelParams cvA.type mI rP j r with
    | error e => intro h; exact nomatch h
    | ok r₁ => ?_
    intro h
    try dsimp only at h
    revert h
    cases hrest : checkIotaRules μ (fueledOps μ F) env' envSelf f
        cvA.name cvA.levelParams cvA.type mI rP (j + 1) rest with
    | error e => intro h; exact nomatch h
    | ok rest' => ?_
    intro h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨r₁, rest',
      iotaRuleR_of m hrecSelf hcvRR hro htransfer hr1,
      ih (j + 1) rest' hrest, rfl⟩

/-- **`checkMemberVal`, bridged.** -/
theorem memberValR_of {env' : Env} (m : EnvR env') {μ : CheckMode} {F :
  Nat} {blockNames : List Name}
    {cv cvA : ConstantVal}
    (h : checkMemberVal (m := CheckM) (fueledOps μ F) blockNames env' cv
      = .ok cvA) :
    MemberValR μ F env' m.cval blockNames cv cvA := by
  simp only [checkMemberVal, Bind.bind, Except.bind] at h
  cases hccv : checkConstantVal (fueledOps μ F) env' cv with
  | error e => rw [hccv] at h; exact nomatch h
  | ok cv' =>
  rw [hccv] at h
  try dsimp only at h
  obtain ⟨type, rfl, -, -, hcv⟩ := constantValR_of m hccv
  by_cases hms : cv.name.isModelSuffix = true
  · rw [if_pos hms] at h
    simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_neg hms] at h
  have hmsF : cv.name.isModelSuffix = false := by
    revert hms; cases cv.name.isModelSuffix <;> simp
  revert h
  cases hfm : env'.find? (cv.name.str "_model") with
  | none => intro h; simp [throw, throwThe, MonadExceptOf.throw] at h
  | some ci =>
    match ci with
    | .defnInfo cvm mval hint =>
      intro h
      dsimp only at h
      by_cases hlp : cvm.levelParams = cv.levelParams
      · rw [if_pos hlp] at h
        by_cases het : Expr.eqUpToNames
            (type.renameConsts fun n =>
              if blockNames.contains n then n.str "_model" else n)
            cvm.type = true
        · rw [if_pos het] at h
          simp only [pure, Except.pure, Except.ok.injEq] at h
          subst h
          exact ⟨type, hcv, rfl, hmsF, cvm, mval, hint, hfm, hlp, het⟩
        · rw [if_neg het] at h
          simp [throw, throwThe, MonadExceptOf.throw] at h
      · rw [if_neg hlp] at h
        simp [throw, throwThe, MonadExceptOf.throw] at h
    | .axiomInfo _ | .thmInfo _ _ | .indInfo _ _ | .ctorInfo _ _ _
    | .recInfo _ _ _ _ | .projInfo _ =>
      intro h
      dsimp only at h
      simp [throw, throwThe, MonadExceptOf.throw] at h

/-! ## `indDecl`, the back half: the two projection-phase folds

`checkIndDecl`'s last two steps are folds over `List.range nF`.  The
template fold is a pure stored-data install and inverts outright; the
projection-function fold is parametric in `ProjFnR`'s own inversion,
for the same reason the value branches' pin packs are — one subject
per lemma. -/

/-- **The elimination-template fold, inverted.** -/
theorem templatesR_of {T ctorName : Name} {lps : List Name}
    {nP nF : Nat} :
    ∀ (l : List Nat) {env' env₂ : Env},
      l.foldlM (installProjTemplateStep (m := CheckM) T ctorName lps
        nP nF) env' = .ok env₂ →
      DeclIndR.TemplatesR T ctorName lps nP nF env' l env₂
  | [], env', env₂, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | i :: l, env', env₂, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hstep : installProjTemplateStep (m := CheckM) T ctorName lps
        nP nF env' i with
    | error e => intro h; exact nomatch h
    | ok env'' =>
      intro h
      refine ⟨env'', ?_, templatesR_of l h⟩
      simp only [installProjTemplateStep] at hstep
      by_cases hfr : (env'.find? (projFnName T i)).isNone = true
      · rw [if_pos hfr] at hstep
        simp only [installProjTemplate] at hstep
        revert hstep
        cases hrec : env'.find? (T.str "rec") with
        | none =>
          intro hstep
          dsimp only at hstep
          simp only [pure, Except.pure, Except.ok.injEq] at hstep
          exact Or.inl hstep.symm
        | some ci =>
          match ci with
          | .recInfo cvR mI rP [rule] =>
            intro hstep
            dsimp only at hstep
            by_cases hcond :
                (env'.find? (projFnName T i)).isNone = true ∧
                  mI = rP ∧ rP = nP + 2 ∧ rule.ctor = ctorName ∧
                  i < nF
            · rw [if_pos hcond] at hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              exact Or.inr ⟨_, rfl, rfl, rfl, rfl, rfl, hfr, hstep.symm⟩
            · rw [if_neg hcond] at hstep
              simp only [pure, Except.pure, Except.ok.injEq] at hstep
              exact Or.inl hstep.symm
          | .recInfo cvR mI rP [] | .recInfo cvR mI rP (_ :: _ :: _)
          | .axiomInfo _ | .defnInfo _ _ _ | .thmInfo _ _
          | .indInfo _ _ | .ctorInfo _ _ _ | .projInfo _ =>
            intro hstep
            dsimp only at hstep
            simp only [pure, Except.pure, Except.ok.injEq] at hstep
            exact Or.inl hstep.symm
      · rw [if_neg hfr] at hstep
        simp only [pure, Except.pure, Except.ok.injEq] at hstep
        exact Or.inl hstep.symm

set_option maxHeartbeats 2000000 in
/-- **One projection-function install, bridged** (`checkProjFn`) —
the last of the six `DeclR` front doors.  Five stage inversions
transcribe; the two semantic conjuncts are the ones the campaign
already has machinery for:

* the rule's front door is `checkProjRule`'s own `inferTypeCore`
  verdict at depth `0`, converted by `InferClaimsR` at the empty
  context (`closed0_framesR`) — the same three lines as
  `iotaRuleR_of`'s;
* the `proj_i.iota` sides pack is `iotaSidesTyR_of`, fed by
  `projStmtParts`, which turns the statement's *pin* into its opened
  spine — a three-element list, so the `getD 0/1/2` slots the
  relation names are literally its entries. -/
theorem projFnR_of {env' env₁ : Env} (m : EnvR env') {μ : CheckMode}
    {F : Nat} {T ctorName : Name} {lps : List Name} {nP nF i : Nat}
    (h : checkProjFn μ (fueledOps μ F) env' T ctorName lps nP nF i
      = .ok env₁) :
    ProjFnR μ F env' m.cval T ctorName lps nP nF i env₁ := by
  obtain ⟨cvj, mcv, hlk, pty, hty, ⟨u0, hshape⟩, hilt, rhsA, hrule,
    ⟨u, hio⟩, henv⟩ := checkProjFn_inv h
  obtain ⟨mval, mhint, hctor, hfm, hmlps, hpnone, hTf, heqf⟩ :=
    checkProjLookups_inv hlk
  obtain ⟨hptyB, hround, hptyres, hptyb, hptyf, hptylp, hstrip1⟩ :=
    checkProjTy_inv hty
  obtain ⟨abinders, arest, cbindersR, cbody, hstripP, hCstrip,
    hcbodyHead, hcbodyArity⟩ := checkProjShape_inv hshape
  obtain ⟨raw, rbinders, cbindersR2, cbody2, hraw, hrawnf, hrawb,
    hrawann, hrlp, hrres, hrhsb, hrhsnf, hrhsAstrip, hCstrip2,
    hdomsR, fvsP, rest0, cdomsP, crestP, xFvs, crest2X, ldoms, lrestL,
    hopenP, hcinstP, hdeP, hopenX, hlinst, hdeLam, rhsTy, hity⟩ :=
    checkProjRule_inv hrule
  obtain ⟨tcv, tval, sbinders, cbindersR3, cbody3, tySlot, ℓA,
    hthmE, htlps, hCstrip3, hdomsS, hSstrip, fvsO, sbodyO, hopenO,
    hsty1, hsty2, hsty3⟩ := checkProjIota_inv hio
  have hcb2 : cbindersR2 = cbindersR :=
    (Prod.mk.inj (Option.some.inj (hCstrip2.symm.trans hCstrip))).1
  have hcb3 : cbindersR3 = cbindersR :=
    (Prod.mk.inj (Option.some.inj (hCstrip3.symm.trans hCstrip))).1
  rw [hcb2] at hdomsR
  rw [hcb3] at hdomsS
  refine ⟨cvj, mcv, mval, mhint, pty, rhsA, hctor, hfm, hmlps,
    (by rw [hpnone]; rfl), hTf, heqf, hptyB, (by rw [hround]; simp),
    hptyres, hptyb, hptyf, hptylp, hstrip1, hilt,
    (by rw [hstripP]; rfl),
    ⟨cbindersR, cbody, hCstrip, hcbodyArity, hcbodyHead, hrhsnf,
      hrhsb, hrlp, hrres, ⟨rbinders, hrhsAstrip, ?_⟩, ?_,
      tcv, tval, hthmE, htlps,
      ⟨sbinders, ℓA, tySlot, hSstrip, ?_⟩, fvsO, sbodyO, hopenO, ?_⟩,
    henv⟩
  · -- the rule's domains are the constructor's
    intro i0 b b' hlt hb hb'
    exact domsMatchAux_inv hdomsR hlt (o₁ := 0) (o₂ := 0)
      (by simpa using hb) (by simpa using hb')
  · -- the rule's front door
    intro φ
    obtain ⟨-, -, -, ihi⟩ := checkBridge m φ F
    obtain ⟨hw, hb, hL, hC⟩ :=
      closed0_framesR (μ := μ) (cval := m.cval) (env := env')
        (φ := φ) hrhsnf hrhsb
    obtain ⟨v, tv, hv, -, T', hI, -⟩ := ihi hity hw hb hL hC
    exact ⟨v, T', hv, hI⟩
  · -- the statement's domains are the constructor's, renamed
    intro i0 b b' hlt hb hb'
    exact domsMatchAux_inv hdomsS hlt (o₁ := 0) (o₂ := 0)
      (by simpa using hb) (by simpa using hb')
  · -- the two equation sides' types
    intro φ
    obtain ⟨hwS0, hbS0, hLS0, TS, hTS0⟩ :=
      storedType_pack m (φ := φ) hthmE 0
    dsimp only [ConstantInfo.toConstantVal] at hwS0 hbS0 hLS0 hTS0
    obtain ⟨hwB, hbB, hLB, vB, hvB⟩ :=
      opener_body_pack_gen m (φ := φ) (D := nP + nF)
        hwS0 hbS0 hLS0 hTS0 hopenO (by omega)
    have hargs := spine_walk_pack m hwB hbB hLB hvB
    obtain ⟨tl, hil, hdl⟩ := hsty1
    obtain ⟨tr, hir, hdr⟩ := hsty2
    obtain ⟨-, -, αS0, hargs3⟩ :=
      projStmtParts hilt hbS0 hopenO hSstrip
    rw [hargs3] at hargs hil hdl hir hdr ⊢
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hil hdl
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hir hdr ⊢
    obtain ⟨hwα, hbα, hLα, vα, hvα⟩ := hargs αS0 (by simp)
    obtain ⟨hwl, hbl, hLl, vl, hvl⟩ :=
      hargs (Expr.mkAppN (.const (projModelName T i)
        (lps.map .param)) (fvsO.take nP ++
          [Expr.mkAppN (.const (ctorName.str "_model")
            (cvj.levelParams.map .param))
            (fvsO.take nP ++ fvsO.drop nP)])) (by simp)
    obtain ⟨hwr, hbr, hLr, vr, hvr⟩ :=
      hargs (fvsO.getD (nP + i) default) (by simp)
    exact iotaSidesTyR_of m hwα hbα hLα hwl hbl hLl hwr hbr hLr
      hvα hvl hvr hil hdl hir hdr

/-! ## `basisDecl`

The simplest branch: a guard on the pinned `Eq` former, then a fold of
duplicate checks.  `BasisInstallR` records exactly the fold's output —
each constant fresh, then consed — so the inversion is one induction
over `installBasisDecl_inv`. -/

/-- **The pinned-block fold, inverted** into `BasisInstallR`. -/
theorem foldlM_installBasisDecl_invR :
    ∀ (l : List ConstantInfo) {env env₁ : Env},
      l.foldlM (installBasisDecl (m := CheckM)) env = .ok env₁ →
      BasisInstallR env l env₁
  | [], env, env₁, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h.symm
  | ci :: l, env, env₁, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    revert h
    cases hi : installBasisDecl (m := CheckM) env ci with
    | error e => intro h; exact nomatch h
    | ok env' =>
      intro h
      obtain ⟨hfresh, rfl⟩ := installBasisDecl_inv hi
      exact ⟨Option.isNone_iff_eq_none.mpr hfresh,
        foldlM_installBasisDecl_invR l h⟩

/-- **`basisDecl`, bridged.** -/
theorem declBasisR {μ : CheckMode} {F : Nat} {env env₂ : Env}
    {kind : BasisKind}
    (h : checkDecl μ (fueledOps μ F) env (.basisDecl kind) = .ok env₂) :
    DeclBasisR env kind env₂ := by
  simp only [checkDecl, Bind.bind, Except.bind] at h
  by_cases hk : kind = .quotK
  · subst hk
    by_cases hEq : env.find? eqName = some eqA
    · simp only [hEq, if_true] at h
      exact ⟨fun _ => hEq, foldlM_installBasisDecl_invR _ h⟩
    · simp [hEq] at h
  · simp only [if_neg hk] at h
    exact ⟨fun hh => absurd hh hk, foldlM_installBasisDecl_invR _ h⟩

end Setlec.SetR
