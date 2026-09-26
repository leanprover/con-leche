module

public import ConLeche.Verify.BridgeDecl
import ConLeche.Verify.Inductives.NestedRuleSyn

public section

/-!
# `wfOpsM mode` runs to pure runs, per declaration-checker function

With the memo operations unguarded, part B's entry-point bridges carry
the arguments' well-scopedness, so `wfOpsM mode`'s condition is per call
(`EnvWF env ∧ wscopedB`) and can no longer be discharged wholesale per
function.  This module proves the run-level implications instead: a
successful `wfOpsM mode` run of each declaration-checker function over a
well-formed environment is the pure `fueledOps` run at the same fuel.
At each operation call site the argument's well-scopedness comes from

* the checker's own input validation (`looseBVarsBounded`/`hasFvar`
  guards precede every `annotate` of raw input — at depth 0
  fvar-freedom *is* well-scopedness),
* the scoping-preservation lemmas for the operations' outputs
  (`annotateCore_WScoped`, `inferTypeCore_WScoped`), and
* scoping of the iota-theorem check's opened telescopes
  (`openPisAtFvars_WScoped`, `instPisAt_WScoped`, `instLamsAt_WScoped`
  — the defeq comparisons run at the opened depth, over variables of
  that frame).

The cached tier's bridge composes these with the intermediate `EnvWF`
facts into the per-declaration bridge: `ConLeche/Verify/Cached/BridgeCS1.lean`
through `BridgeCS3.lean` mirror the `_wfimp` walks per call site,
`BridgeCS4.lean` and `BridgeCSDecl.lean` chain them along the phase
drivers into `checkDeclSharedF_bridge`.
-/

set_option linter.unusedSimpArgs false

namespace ConLeche

variable {mode : CheckMode}
variable {pins : List NatOpPinSet}

open Expr

/-! ## Small syntactic toolkit -/

theorem wscopedB_of_not_hasFvar {e : Expr} (h : e.hasFvar = false)
    {d : Nat} : e.wscopedB d = true :=
  (WScoped.of_not_hasFvar h).to_wscopedB

theorem stripLams_not_hasFvar :
    ∀ (k : Nat) {e : Expr} {bs : List (Expr × BinderMeta)}
      {body : Expr}, Expr.stripLams k e = some (bs, body) →
      e.hasFvar = false →
      (∀ b ∈ bs, (b.1).hasFvar = false) ∧ body.hasFvar = false
  | 0, e, bs, body, h, hf => by
    simp only [Expr.stripLams, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ : [] = bs ∧ e = body :=
      ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    exact ⟨(fun b hb => nomatch hb), hf⟩
  | k + 1, e, bs, body, h, hf => by
    match e, h with
    | .lam ty b m, h =>
      simp only [Expr.stripLams, Option.map_eq_some_iff] at h
      obtain ⟨⟨bs', body'⟩, hstrip, heq⟩ := h
      obtain ⟨rfl, rfl⟩ : (ty, m) :: bs' = bs ∧ body' = body :=
        ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [Expr.hasFvar, Bool.or_eq_false_iff] at hf
      obtain ⟨hrest, hbody⟩ := stripLams_not_hasFvar k hstrip hf.2
      refine ⟨?_, hbody⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hf.1
      · exact hrest b hb

/-! ## The leaf checker functions, `wfOpsM mode` runs to pure runs -/

/-- `openPisAtFvars` puts the variable it creates for binder `j` at
index `i + j` — the positional companion of `openPisAtFvars_WScoped`,
needed wherever a check runs at each binder's *own* frame. -/
theorem openPisAtFvars_index :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i = some (fvs, body) →
      ∀ (j : Nat) (x : Expr), fvs[j]? = some x →
        ∃ ty, x = Expr.fvar (i + j) ty := by
  intro n
  induction n with
  | zero =>
    intro e i fvs body h j x hx
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1] at hx
    exact nomatch hx
  | succ n ih =>
    intro e i fvs body h j x hx
    cases e with
    | forallE dom bodyE mb =>
      simp only [openPisAtFvars] at h
      revert h
      cases hrec : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i dom)) (i + 1) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨fvs', bodyR⟩ := p
        intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
          exact ⟨dom, by rw [← hx, Nat.add_zero]⟩
        | succ j =>
          simp only [List.getElem?_cons_succ] at hx
          obtain ⟨ty', hx'⟩ := ih _ (i + 1) hrec j x hx
          exact ⟨ty', by rw [hx']; congr 1; omega⟩
    | bvar _ | fvar _ _ | sort _ | const _ _ | app _ _
    | lam _ _ _ | letE _ _ _ | lit _ | proj _ _ _ =>
      exact nomatch h

/-- Opening a `∀`-telescope at fresh free variables produces variables
and a body scoped at the extended frame. -/
theorem openPisAtFvars_WScoped :
    ∀ (n : Nat) (e : Expr) (i : Nat) {fvs : List Expr} {body : Expr},
      openPisAtFvars n e i = some (fvs, body) → WScoped i e →
      (∀ x ∈ fvs, WScoped (i + n) x) ∧ WScoped (i + n) body := by
  intro n
  induction n with
  | zero =>
    intro e i fvs body h hw
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hw⟩
  | succ n ih =>
    intro e i fvs body h hw
    cases e with
    | forallE dom bodyE mb =>
      simp only [openPisAtFvars] at h
      revert h
      cases hrec : openPisAtFvars n
          (bodyE.instantiate1 (.fvar i dom)) (i + 1) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨fvs', bodyR⟩ := p
        intro h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [WScoped] at hw
        obtain ⟨hdom, hbody⟩ := hw
        have hinst : WScoped (i + 1)
            (bodyE.instantiate1 (.fvar i dom)) :=
          WScoped.instantiate1 hdom 0 hbody
        obtain ⟨hfvs', hbody'⟩ := ih _ _ hrec hinst
        have harith : i + 1 + n = i + (n + 1) := by omega
        rw [harith] at hfvs' hbody'
        refine ⟨?_, hbody'⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp only [WScoped]
          exact ⟨by omega, hdom⟩
        · exact hfvs' x hx
    | bvar k => exact nomatch h
    | fvar a c => exact nomatch h
    | sort u => exact nomatch h
    | const c us => exact nomatch h
    | app f a => exact nomatch h
    | lam b c d => exact nomatch h
    | letE b c d => exact nomatch h
    | lit l => exact nomatch h
    | proj s k e => exact nomatch h

/-- `instPisAt` for `λ`-binders, scoped. -/
theorem instLamsAt_WScoped {d : Nat} :
    ∀ (args : List Expr) (ty : Expr) {doms : List Expr} {res : Expr},
      Expr.instLamsAt args ty = some (doms, res) → WScoped d ty →
      (∀ a ∈ args, WScoped d a) →
      (∀ x ∈ doms, WScoped d x) ∧ WScoped d res
  | [], ty, doms, res, h, hty, _ => by
    simp only [Expr.instLamsAt, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(fun x hx => nomatch hx), hty⟩
  | a :: as, ty, doms, res, h, hty, hargs => by
    cases ty with
    | lam dom body mb =>
      simp only [Expr.instLamsAt] at h
      revert h
      cases hrec : Expr.instLamsAt as (body.instantiate1 a) with
      | none => intro h; exact nomatch h
      | some p =>
        obtain ⟨ds, rest⟩ := p
        intro h
        simp only [Option.map_some, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp only [WScoped] at hty
        obtain ⟨hdom, hbody⟩ := hty
        have hinst : WScoped d (body.instantiate1 a) :=
          WScoped.instantiate1_gen (hargs a List.mem_cons_self) 0 hbody
        obtain ⟨hds, hres⟩ := instLamsAt_WScoped as _ hrec hinst
          (fun x hx => hargs x (List.mem_cons_of_mem _ hx))
        refine ⟨?_, hres⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hdom
        · exact hds x hx
    | bvar k => exact nomatch h
    | fvar a' c => exact nomatch h
    | sort u => exact nomatch h
    | const c us => exact nomatch h
    | app f a' => exact nomatch h
    | forallE b c d' => exact nomatch h
    | letE b c d' => exact nomatch h
    | lit l => exact nomatch h
    | proj s k e => exact nomatch h

/-- The read-off type of an opened variable is scoped. -/
theorem fvarTypeD_WScoped {d : Nat} {e : Expr} (h : WScoped d e) :
    WScoped d (Expr.fvarTypeD e) := by
  cases e with
  | fvar idx ty =>
    simp only [WScoped] at h
    exact WScoped.mono (Nat.le_of_lt h.1) h.2
  | bvar k => exact h
  | sort u => exact h
  | const c us => exact h
  | app f a => exact h
  | lam b c d' => exact h
  | forallE b c d' => exact h
  | letE b c d' => exact h
  | lit l => exact h
  | proj s k e => exact h

/-! ## Scoping of the structural-Nat certification equations -/

/-- The recurrence equations' sides are well-scoped at depth 2 (their
free variables are `fvar 0`/`fvar 1` with closed annotations). -/
theorem natOpEquations_wscopedB {c : Name} (hc : c ∈ natOpNames) :
    ∀ eq ∈ natOpEquations 0 c,
      eq.1.wscopedB 2 = true ∧ eq.2.wscopedB 2 = true := by
  simp only [natOpNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (intro eq heq
     simp +decide [natOpEquations] at heq
     first
       | (rcases heq with rfl | rfl | rfl | rfl) <;>
           simp +decide [Expr.wscopedB]
       | (rcases heq with rfl | rfl | rfl) <;>
           simp +decide [Expr.wscopedB]
       | (rcases heq with rfl | rfl) <;>
           simp +decide [Expr.wscopedB])

/-- Substituting a closed value for a constant preserves scoping. -/
theorem wscopedB_substConst0 {n : Name} {r : Expr}
    (hr : r.hasFvar = false) :
    ∀ (e : Expr) {d : Nat}, e.wscopedB d = true →
      (Expr.substConst0 n r e).wscopedB d = true
  | .const c us, d, he => by
    simp only [Expr.substConst0]
    split
    · exact wscopedB_of_not_hasFvar hr
    · exact he
  | .app f a, d, he => by
    simp only [Expr.substConst0, Expr.wscopedB, Bool.and_eq_true] at he ⊢
    exact ⟨wscopedB_substConst0 hr f he.1, wscopedB_substConst0 hr a he.2⟩
  | .bvar _, _, he | .fvar _ _, _, he | .sort _, _, he | .lit _, _, he
  | .lam _ _ _, _, he | .forallE _ _ _, _, he
  | .letE _ _ _, _, he | .proj _ _ _, _, he => he

/-! ## The div/mod pin gate, `wfOpsM mode` runs to pure runs -/

/-- The pinned open certificate statements are well-scoped at the
certificate frame: hypotheses at their own binder index (they ride as
the `fvar 2`/`fvar 3` annotations), the equation at the full frame. -/
theorem divModCertStmts_wscopedB {c : Name} (hc : c ∈ natDivModNames) :
    ∀ st ∈ divModCertStmts c,
      (∀ hyp ∈ st.1, hyp.wscopedB 2 = true) ∧ st.2.wscopedB 4 = true := by
  simp only [natDivModNames, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide +kernel

/-- The applied certificate proof is well-scoped at the frame. -/
theorem divModCertApplied_wscopedB {proofS : Expr} {hyps : List Expr}
    (hp : proofS.hasFvar = false)
    (hh : ∀ hyp ∈ hyps, hyp.wscopedB 2 = true) :
    (divModCertApplied proofS hyps).wscopedB 4 = true := by
  have hpw : proofS.wscopedB 4 = true := wscopedB_of_not_hasFvar hp
  unfold divModCertApplied
  match hyps, hh with
  | [], hh => simp [Expr.wscopedB, hpw]
  | [h1], hh =>
    have h1w := hh h1 (by simp)
    simp [Expr.wscopedB, hpw, h1w]
  | [h1, h2], hh =>
    have h1w := hh h1 (by simp)
    have h2w3 : h2.wscopedB 3 = true :=
      (WScoped.mono (by omega) (WScoped.of_wscopedB
        (hh h2 (by simp)))).to_wscopedB
    simp [Expr.wscopedB, hpw, h1w, h2w3]
  | _ :: _ :: _ :: _, hh => simp [Expr.wscopedB, hpw]

/-! ## The direct simple-structure path (task #82)

Run-level implications for the checks `checkStruct` composes.
The fabricated terms whose scoping has to be established here are the
openings of the recursor and constructor telescopes (at the pin frame
`nP + 2 + nF`), the generated projection type and the rule's
right-hand side — the last two are checked closed by the checker's own
`!hasFvar && looseBVarsBounded 0` guards before they are annotated. -/

/-- Close a goal whose hypothesis is a pure run that begins with a
`throw`: such a run never succeeds. -/
macro "throwM_elim" h:ident : tactic =>
  `(tactic| simp only [throw, throwThe, MonadExceptOf.throw, Bind.bind,
      Except.bind, reduceCtorEq] at $h:ident)

/-- The type-slot `ConstWF` facts of a successfully checked constant:
level parameters and constant resolution are checked outright, and the
annotated type inherits closedness and fvar-freedom from the raw
checks through `annotate`. -/
theorem checkConstantVal_typeWF {env : Env} {cv cvA : ConstantVal}
    {F : Nat} (h : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
    cvA.type.hasFvar = false ∧
    cvA.type.allLevelParamsDefined cvA.levelParams = true ∧
    cvA.type.constsResolve env = true ∧
    cvA.type.looseBVarsBounded 0 = true := by
  unfold checkConstantVal at h
  by_cases h1 : (env.find? cv.name).isSome = true
  · rw [if_pos h1] at h; throwM_elim h
  rw [if_neg h1] at h
  by_cases h2 : reservedBasisNames.contains cv.name = true
  · rw [if_pos h2] at h; throwM_elim h
  rw [if_neg h2] at h
  by_cases h3 : cv.name.isProjFnShape = true
  · rw [if_pos h3] at h; throwM_elim h
  rw [if_neg h3] at h
  by_cases h4 : Name.nodup cv.levelParams = true
  case neg => rw [if_neg h4] at h; throwM_elim h
  rw [if_pos h4] at h
  by_cases h5 : Expr.looseBVarsBounded 0 cv.type = true
  case neg => rw [if_neg h5] at h; throwM_elim h
  rw [if_pos h5] at h
  by_cases h6 : cv.type.hasFvar = true
  · rw [if_pos h6] at h; throwM_elim h
  rw [if_neg h6] at h
  revert h
  match hann : (fueledOps mode F).annotate env 0 cv.type with
  | .error e => intro h; exact nomatch h
  | .ok type => ?_
  intro h
  simp only [Bind.bind, Except.bind] at h
  have hann' : annotateCore mode env F 0 cv.type = .ok type := hann
  by_cases h7 : Expr.allLevelParamsDefined cv.levelParams type = true
  case neg => rw [if_neg h7] at h; exact nomatch h
  rw [if_pos h7] at h
  by_cases h8 : Expr.constsResolve env type = true
  case neg => rw [if_neg h8] at h; exact nomatch h
  rw [if_pos h8] at h
  revert h
  match hity : (fueledOps mode F).inferType env 0 type with
  | .error e => intro h; exact nomatch h
  | .ok stype => ?_
  intro h
  simp only [Bind.bind, Except.bind] at h
  revert h
  match hsty : (fueledOps mode F).ensureSort env 0 stype with
  | .error e => intro h; exact nomatch h
  | .ok u => ?_
  intro h
  simp only [Bind.bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at h
  subst h
  refine ⟨?_, h7, h8, annotateCore_looseBVars F cv.type hann' h5⟩
  exact not_hasFvar_of_fvarsBelow_zero
    ((annotateCore_WScoped F cv.type hann'
      (WScoped.of_not_hasFvar (Bool.not_eq_true _ |>.mp h6))).fvarsBelow)

end ConLeche
