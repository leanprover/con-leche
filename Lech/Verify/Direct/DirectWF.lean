import Lech.Verify.BridgeWfImp
import Lech.Verify.ExceptBind

/-!
# The direct simple-structure install: environment well-formedness

`EnvWF` for the environments `checkDirectStruct` walks through — one
per installed constant — at the pure fueled run.  The consumer is the
cached driver's run bridge (`Lech/Verify/Cached/BridgeCSDecl.lean`,
`checkDirectStructS_run`), which threads the well-formedness of every
intermediate environment through the per-stage simulations.

Every fact is read off the stage's own guards: each install stores an
annotated constant whose type (and, for the recursor, whose rule's
right-hand side; for a projection entry, whose stored type) was
checked closed, level-defined, resolving and bound *by the stage
itself*, so the inversions here are shape walks (`exceptBind_ok` /
`split`) that keep exactly those guards.
-/

namespace Lech

variable {mode : CheckMode}

/-- A thrown step never succeeds. -/
private theorem directThrow_ne_ok {α : Type} {e : CheckError} {a : α}
    (h : (throw e : CheckM α) = .ok a) : False := by
  simp [throw, throwThe, MonadExceptOf.throw] at h

/-- The shape walk's closers: every non-surviving goal holds a
`throw … = .ok _` (possibly under a join point's zeta step). -/
local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact directThrow_ne_ok (by assumption))
        | (exfalso; exact directThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-- A successful `unwrapOr` names its option. -/
theorem unwrapOr_ok {α : Type} {x : Option α} {e : CheckError} {a : α}
    (h : (unwrapOr x e : CheckM α) = .ok a) : x = some a := by
  cases x with
  | none => exact absurd h (by simp [unwrapOr, throw, throwThe, MonadExceptOf.throw])
  | some b =>
    simp only [unwrapOr, pure, Except.pure, Except.ok.injEq] at h
    rw [h]

/-- Introduction for `ConstWF` with the clause types spelled out (the
`thmInfo` clause defaulted, as every constant installed by the direct
path is an inductive-kind one). -/
theorem directConstWF {env : Env} {c : ConstantInfo}
    (h1 : c.toConstantVal.type.hasFvar = false)
    (h2 : c.toConstantVal.type.allLevelParamsDefined
      c.toConstantVal.levelParams = true)
    (h3 : c.toConstantVal.type.constsResolve env = true)
    (h4 : c.toConstantVal.type.looseBVarsBounded 0 = true)
    (h5 : ∀ cv value hint, c = .defnInfo cv value hint →
      value.hasFvar = false ∧
      value.allLevelParamsDefined cv.levelParams = true ∧
      value.constsResolve env = true ∧
      value.looseBVarsBounded 0 = true)
    (h6 : ∀ cv mI rP rules, c = .recInfo cv mI rP rules →
      ∀ r, r ∈ rules →
        (RecRule.rhs r).hasFvar = false ∧
        (RecRule.rhs r).allLevelParamsDefined cv.levelParams = true ∧
        (RecRule.rhs r).constsResolve env = true ∧
        (RecRule.rhs r).looseBVarsBounded 0 = true ∧
        ∀ lvls pins, RecRule.fire r = .nested lvls pins →
          rP ≤ mI ∧
          (∀ l ∈ lvls, l.allParamsDefined cv.levelParams = true) ∧
          (∀ pin ∈ pins, pin.hasFvar = false ∧
            pin.allLevelParamsDefined cv.levelParams = true ∧
            pin.constsResolve env = true ∧
            pin.looseBVarsBounded rP = true) ∧
          ∃ pre nm dom body bm D,
            cv.type.stripPis mI = some (pre, .forallE nm dom body bm) ∧
            dom.getAppFn = .const D lvls ∧
            dom.getAppArgs =
              pins.map (Expr.liftLooseBVars (mI - rP) 0) ++
                (List.range (mI - rP)).map
                  (fun i => Expr.bvar (mI - rP - 1 - i)))
    (h7 : ∀ cv value, c = .thmInfo cv value →
      value.hasFvar = false ∧
      value.allLevelParamsDefined cv.levelParams = true ∧
      value.constsResolve env = true ∧
      value.looseBVarsBounded 0 = true := by
        intro cv value h
        exact ConstantInfo.noConfusion h)
    (h8 : ∀ tbl, c = .projInfo tbl →
      tbl.bodies.size = tbl.numFields ∧
      ∀ (i : Nat) (b : Expr), tbl.bodies[i]? = some b →
        b.hasFvar = false ∧
        b.allLevelParamsDefined tbl.levelParams = true ∧
        b.constsResolve env = true ∧
        b.looseBVarsBounded (tbl.numParams + 1) = true := by
        intro tbl h
        exact ConstantInfo.noConfusion h) :
    ConstWF env c := ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A checked inductive-kind cons is well-formed (its `ConstWF` is the
four type-slot facts; every value clause is refuted by the kind). -/
theorem envWF_cons_ind {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {caps : IndCaps} {F : Nat} {cv : ConstantVal}
    (hccv : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
    EnvWF ⟨.indInfo cvA caps :: env.consts⟩ := by
  obtain ⟨htf, htp, htr, htb⟩ := checkConstantVal_typeWF hccv
  exact EnvWF.cons henv (directConstWF htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq))

/-- A checked constructor cons is well-formed. -/
theorem envWF_cons_ctor {env : Env} (henv : EnvWF env)
    {cvA : ConstantVal} {nP nF F : Nat} {cv : ConstantVal}
    (hccv : checkConstantVal (fueledOps mode F) env cv = .ok cvA) :
    EnvWF ⟨.ctorInfo cvA nP nF :: env.consts⟩ := by
  obtain ⟨htf, htp, htr, htb⟩ := checkConstantVal_typeWF hccv
  exact EnvWF.cons henv (directConstWF htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq)
    (fun _ _ _ _ heq => nomatch heq))

/-- Stage 1 at the run level: the environment it produces is
well-formed and the stored type is closed. -/
theorem direct_ind_wf {env env₁ : Env} (henv : EnvWF env)
    {p : DirectParts} {cvTa : ConstantVal} {F : Nat}
    (h : checkDirectInd (fueledOps mode F) env p = .ok (env₁, cvTa)) :
    EnvWF env₁ ∧ cvTa.type.hasFvar = false := by
  unfold checkDirectInd at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl⟩ := h
       exact ⟨envWF_cons_ind henv (by assumption),
         (checkConstantVal_typeWF (by assumption)).1⟩)
    | close_throw

/-- Stage 2 at the run level. -/
theorem direct_ctor_wf {env₀ env env₂ : Env} (henv : EnvWF env)
    {p : DirectParts} {cvTa cvCa : ConstantVal} {sorts : List Level}
    {F : Nat}
    (h : checkDirectCtor (fueledOps mode F) env₀ env p cvTa
      = .ok (env₂, cvCa, sorts)) :
    EnvWF env₂ ∧ cvCa.type.hasFvar = false ∧
      cvCa.type.looseBVarsBounded 0 = true := by
  unfold checkDirectCtor at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, rfl, rfl⟩ := h
       obtain ⟨htf, -, -, htb⟩ := checkConstantVal_typeWF (by assumption)
       exact ⟨envWF_cons_ctor henv (by assumption), htf, htb⟩)
    | close_throw

/-- The recursor stage's stored pieces, as its own guards checked
them (task #175 S2): the stored type is the generated recursor type
at the stream's name and level parameters, and both it and the
generated rule pass the four scoping clauses. -/
theorem checkDirectRec_facts {env : Env} {p : DirectParts}
    {cvTa cvCa cvRa : ConstantVal} {rhsA : Expr} {F : Nat}
    (h : checkDirectRec (fueledOps mode F) env p cvTa cvCa = .ok (cvRa, rhsA)) :
    cvRa.name = p.cvR.name ∧ cvRa.levelParams = p.cvR.levelParams ∧
    (cvRa.type.hasFvar = false ∧
      cvRa.type.allLevelParamsDefined cvRa.levelParams = true ∧
      cvRa.type.constsResolve env = true ∧
      cvRa.type.looseBVarsBounded 0 = true) ∧
    (rhsA.hasFvar = false ∧
      rhsA.allLevelParamsDefined cvRa.levelParams = true ∧
      rhsA.constsResolve env = true ∧
      rhsA.looseBVarsBounded 0 = true) := by
  unfold checkDirectRec at h
  obtain ⟨cvRi, -, h⟩ := exceptBind_ok h
  try dsimp only at h
  obtain ⟨recTy, -, h⟩ := exceptBind_ok h
  obtain ⟨rhs, -, h⟩ := exceptBind_ok h
  try dsimp only at h
  split at h
  · try dsimp only at h
    have hg1 : (Expr.allLevelParamsDefined p.cvR.levelParams recTy &&
        Expr.constsResolve env recTy && Expr.looseBVarsBounded 0 recTy &&
        !recTy.hasFvar) = true := by assumption
    split at h
    · try dsimp only at h
      have hg2 : (Expr.allLevelParamsDefined p.cvR.levelParams rhs &&
          Expr.constsResolve env rhs && Expr.looseBVarsBounded 0 rhs &&
          !rhs.hasFvar) = true := by assumption
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hg1 hg2
      have hret : cvRa = ⟨p.cvR.name, p.cvR.levelParams, recTy⟩ ∧ rhsA = rhs := by
        repeat' first
          | (obtain ⟨_, _, h⟩ := exceptBind_ok h)
          | split at h
        all_goals first
          | (try dsimp only at h
             simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
             exact ⟨h.1.symm, h.2.symm⟩)
          | close_throw
      obtain ⟨rfl, rfl⟩ := hret
      exact ⟨rfl, rfl, ⟨hg1.2, hg1.1.1.1, hg1.1.1.2, hg1.1.2⟩,
        ⟨hg2.2, hg2.1.1.1, hg2.1.1.2, hg2.1.2⟩⟩
    · close_throw
  · close_throw

/-- Stage 3 at the run level: the recursor cons carrying its single
rule is well-formed — the stored type's and the rule's four clauses are
the stage's own guards; the fire mode is never `.nested`. -/
theorem direct_rec_wf {env : Env} (henv : EnvWF env)
    {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {rhsA : Expr} {F : Nat}
    (h : checkDirectRec (fueledOps mode F) env p cvTa cvCa = .ok (cvRa, rhsA)) :
    EnvWF ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
      [⟨p.cvC.name, p.nF, p.nP,
        if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
          .plain else .inert, rhsA⟩] :: env.consts⟩ := by
  obtain ⟨-, -, ⟨htf, htp, htr, htb⟩, ⟨hrfv, hrlp, hrres, hrbv⟩⟩ :=
    checkDirectRec_facts h
  refine EnvWF.cons henv (directConstWF htf htp
    (Expr.constsResolve_mono htr) htb
    (fun _ _ _ heq => nomatch heq) ?_)
  intro cvR' mI' rP' rules' heq r hr
  injection heq with e1 e2 e3 e4
  subst e1
  subst e4
  rcases List.mem_singleton.mp hr with rfl
  refine ⟨hrfv, hrlp, Expr.constsResolve_mono hrres, hrbv, ?_⟩
  intro lvls pins hf
  cases hcond : Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP <;>
    simp [hcond] at hf

/-! ## Stage 5: the projection table (task #175 S1) -/

/-- The table stage's run, inverted: the bodies are the generator's,
they pass the scoping guard, the table name is fresh, and the output
is the table consed. -/
theorem checkDirectProjTable_inv {env envOut : Env} {T C : Name}
    {lps : List Name} {nP nF : Nat} {rs : Level} {guards : List Level}
    {cvCa : ConstantVal}
    (h : checkDirectProjTable (m := CheckM) T C lps nP nF rs guards cvCa env
      = .ok envOut) :
    ∃ bodies : Array Expr,
      directProjBodies T nP nF cvCa.type = some bodies ∧
      (bodies.size = nF ∧ bodies.all (fun b => !b.hasFvar &&
        b.allLevelParamsDefined lps && b.constsResolve env &&
        b.looseBVarsBounded (nP + 1)) = true) ∧
      (List.range nF).all (fun j => (env.find? (projFnName T j)).isNone) = true ∧
      env.find? (projTableName T) = none ∧
      envOut = ⟨.projInfo ⟨T, lps, nP, C, nF, rs, bodies, guards⟩
        :: env.consts⟩ := by
  unfold checkDirectProjTable at h
  obtain ⟨bodies, hb, h⟩ := exceptBind_ok h
  have hb' := unwrapOr_ok hb
  repeat' first
    | (obtain ⟨_, _, h⟩ := exceptBind_ok h)
    | split at h
  all_goals first
    | (try dsimp only at h
       simp only [pure, Except.pure, Except.ok.injEq] at h
       refine ⟨bodies, hb', by assumption, by assumption,
         Option.isNone_iff_eq_none.mp (by assumption), h.symm⟩)
    | close_throw

/-- The projection-table stage at the run level (task #175 S1): the
environment it produces is well-formed — the table's constant type is
the closed `Sort 1`, and the bodies' scoping is the stage's own guard. -/
theorem direct_table_wf {env envOut : Env} (henv : EnvWF env)
    {T C : Name} {lps : List Name} {nP nF : Nat} {rs : Level}
    {guards : List Level} {cvCa : ConstantVal}
    (h : checkDirectProjTable (m := CheckM) T C lps nP nF rs guards cvCa env
      = .ok envOut) :
    EnvWF envOut := by
  obtain ⟨bodies, -, ⟨hsize, hall⟩, -, -, rfl⟩ := checkDirectProjTable_inv h
  refine EnvWF.cons henv (directConstWF rfl rfl rfl rfl
    (fun _ _ _ heq => nomatch heq) (fun _ _ _ _ heq => nomatch heq)
    (fun _ _ heq => nomatch heq) ?_)
  intro tbl heq
  obtain rfl := ConstantInfo.projInfo.inj heq
  refine ⟨hsize, fun i b hb => ?_⟩
  have hmem : b ∈ bodies := Array.mem_of_getElem? hb
  have hb' := (Array.all_eq_true_iff_forall_mem.mp hall) b hmem
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hb'
  exact ⟨hb'.1.1.1, hb'.1.1.2, Expr.constsResolve_mono hb'.1.2, hb'.2⟩

end Lech
