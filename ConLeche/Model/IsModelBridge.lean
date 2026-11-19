module

public import ConLeche.Denotes
public import ConLeche.Model.OfEnvModelM

public section

/-!
# From a model of the checker's environment to a model of its input (task #617)

`Model V env` (`ConLeche/Denotes.lean`) is the proofs' model of the environment the checker
builds; `IsModel V model ds` (`ConLeche/IsModel.lean`) is the public notion, over the input.
This module carries the first to the second.

* `posModel`: the internal valuation `cval`, which reads a level ASSIGNMENT, made positional
  through the stored constant's level parameters.
* `eval_of_Denotes`: wherever the relation `Denotes` reads a term, the total reading
  `Expr.eval` at `posModel` agrees with it.  The one fact this needs of `cval` is that a
  constant reads only its own level parameters (`CvalLocal`; the invariant's `acval_params`).
* `isModel_of_model`: the clauses, from `Model`'s fields, given what the checker establishes
  about the records (`RecordsStored`, `CtorsStored`) and that every stored ι equation is read
  (`RuleEqsRead`).
-/

namespace ConLeche

open SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- The internal valuation, positional: a stored constant's level values go to its level
parameters in order. -/
noncomputable def posModel (cval : Name → (LevelParam → Nat) → V) (env : Env) :
    Name → List Nat → V := fun n vals =>
  match env.find? n with
  | some ci => cval n (Level.assign ci.toConstantVal.levelParams vals)
  | none => empty

/-- A stored constant reads only its own level parameters. -/
def CvalLocal (cval : Name → (LevelParam → Nat) → V) (env : Env) : Prop :=
  ∀ n ci, env.find? n = some ci → ∀ ψ₁ ψ₂ : LevelParam → Nat,
    (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) → cval n ψ₁ = cval n ψ₂

/-- On a constant's own parameters, the positional assignment is the substitution's. -/
theorem assign_map_eval (φ : LevelParam → Nat) :
    ∀ (ps : List Name) (us : List Level), us.length = ps.length → ∀ p ∈ ps,
      Level.assign ps (us.map (Level.eval φ)) p = Level.substFn φ ps us p
  | [], _, _, p, hp => nomatch hp
  | q :: ps, [], h, _, _ => nomatch h
  | q :: ps, u :: us, h, p, hp => by
    simp only [List.map_cons, Level.assign, Level.substFn]
    by_cases hq : q = p
    · simp [hq]
    · simp only [hq, ↓reduceIte]
      exact assign_map_eval φ ps us (by simpa using h) p
        (by rcases List.mem_cons.mp hp with h' | h'; exact absurd h'.symm hq; exact h')

/-- A literal's constructor form reads as the literal. -/
theorem eval_natLitToConstructor (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (n : Nat) :
    Expr.eval model φ ρ (natLitToConstructor n) = Expr.eval model φ ρ (.lit (.natVal n)) := by
  cases n <;> rfl

theorem eval_strLitToConstructor (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (s : String) :
    Expr.eval model φ ρ (strLitToConstructor s) = Expr.eval model φ ρ (.lit (.strVal s)) := by
  show SetTheory.app _ _ = strLitVal model s
  unfold strLitVal
  congr 1
  induction s.toList with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldr_cons]
    show SetTheory.app (SetTheory.app _ _) (Expr.eval model φ ρ (List.foldr _ _ cs)) = _
    rw [ih]
    rfl

/-- **The total reading agrees with `Denotes`** wherever that reads. -/
theorem eval_of_Denotes {cval : Name → (LevelParam → Nat) → V} {env : Env}
    (hloc : CvalLocal cval env) {φ : LevelParam → Nat} {ρ : BVarIdx → V} {e : Expr} {v : V}
    (h : Denotes cval env φ ρ e v) : Expr.eval (posModel cval env) φ ρ e = v := by
  induction h with
  | bvar => rfl
  | sort => rfl
  | @const ρ n us ci hf hlen =>
    show posModel cval env n (us.map (Level.eval φ)) = _
    unfold posModel
    rw [hf]
    exact hloc n ci hf _ _ (assign_map_eval φ _ us hlen)
  | app _ _ ihf iha =>
    show SetTheory.app _ _ = _
    rw [ihf, iha]
  | lam _ _ ihA ihF =>
    show lamV _ _ = _
    rw [ihA]
    exact lamV_congr fun x hx => ihF x hx
  | pi _ _ ihA ihB =>
    show piV _ _ = _
    rw [ihA]
    exact piV_congr fun x hx => ihB x hx
  | letE _ _ ihv ihb =>
    show Expr.eval _ φ (push (Expr.eval _ φ _ _) _) _ = _
    rw [ihv]
    exact ihb
  | proj_table _ _ ih =>
    show field _ _ = _
    rw [ih]
  | @natLit ρ n X _ ih =>
    rw [← eval_natLitToConstructor]
    exact ih
  | @strLit ρ s X _ ih =>
    rw [← eval_strLitToConstructor]
    exact ih

/-! ## The clauses -/

/-- **Every record of the input is stored**, under its name: with its level parameters and
type, a definition with its value, a recursor with its rules (firing modes included). -/
def RecordsStored (ds : List Declaration) (env : Env) : Prop :=
  ∀ d ∈ ds, ∀ c ∈ d.records, ∃ ci, ci ∈ env.consts ∧ env.find? c.name = some ci ∧
    ci.toConstantVal = c.toConstantVal ∧
    (∀ cv v h, c = .defnInfo cv v h → ci = c) ∧
    (∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules →
      ∃ isK', ci = .recInfo cv mI rP isK' rules)

/-- **Every constructor record of the input is stored** as a constructor with its parameter
count. -/
def CtorsStored (ds : List Declaration) (env : Env) : Prop :=
  ∀ d ∈ ds, ∀ cvj cnP nF T, ConstantInfo.ctorInfo cvj cnP nF T ∈ d.records →
    ∃ nF' T', env.find? cvj.name = some (.ctorInfo cvj cnP nF' T')

/-- **Every stored ι equation is read** by `Denotes`, at every level assignment. -/
def RuleEqsRead (cval : Name → (LevelParam → Nat) → V) (env : Env) : Prop :=
  ∀ e ∈ ruleEqs env, ∀ φ (ρ : BVarIdx → V), ∃ P, Denotes cval env φ ρ e P

theorem find?_name {env : Env} {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci) :
    ci.name = n := by
  have := List.find?_some h
  simpa using this

/-- **The bridge**: a model of the stored environment, local in its levels, is a model of the
input, given that the records are stored and the stored ι equations are read. -/
theorem isModel_of_model {ds : List Declaration} {env : Env} (M : Model V env)
    (hloc : CvalLocal M.cval env) (hrec : RecordsStored ds env) (hctor : CtorsStored ds env)
    (hread : RuleEqsRead M.cval env) :
    IsModel V (posModel M.cval env) ds := by
  intro d hd c hc vals hl
  obtain ⟨ci, hmem, hf, hcv, hdef, hrc⟩ := hrec d hd c hc
  have hname : c.name = ci.name := (find?_name hf).symm
  have hval : posModel M.cval env c.name vals =
      M.cval c.name (Level.assign c.toConstantVal.levelParams vals) := by
    unfold posModel; rw [hf]; dsimp only; rw [hcv]
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT, hmT⟩ := M.mem ci hmem (Level.assign c.toConstantVal.levelParams vals) ρ₀
    rw [hcv] at hT
    rw [hval, eval_of_Denotes hloc hT, hname]
    exact hmT
  · cases c with
    | defnInfo cv value hint =>
      obtain rfl := hdef cv value hint rfl
      have hD := M.defn_eq cv value hint hmem (Level.assign cv.levelParams vals) ρ₀
      show posModel M.cval env cv.name vals =
        Expr.eval (posModel M.cval env) (Level.assign cv.levelParams vals) ρ₀ value
      rw [eval_of_Denotes hloc hD]
      exact hval
    | recInfo cv mI rP isK rules =>
      obtain ⟨isK', rfl⟩ := hrc cv mI rP isK rules rfl
      intro rl hrl d' hd' cvj cnP nF T hcj hcn e he
      obtain ⟨nF', T', hfj⟩ := hctor d' hd' cvj cnP nF T hcj
      have hiota : iotaEq env.find? cv mI rP rl = some e := by
        unfold iotaEq
        rw [← hcn, hfj]
        exact he
      have hin : e ∈ ruleEqs env := by
        unfold ruleEqs
        refine List.mem_flatMap.mpr ⟨_, hmem, ?_⟩
        have hf' : env.find? (ConstantInfo.recInfo cv mI rP isK' rules).name =
            some (.recInfo cv mI rP isK' rules) := by
          exact hf
        rw [hf']
        exact List.mem_filterMap.mpr ⟨rl, hrl, hiota⟩
      obtain ⟨P, hP⟩ := hread e hin (Level.assign cv.levelParams vals) ρ₀
      show ∃ x, x ∈ˢ Expr.eval _ (Level.assign cv.levelParams vals) ρ₀ e
      rw [eval_of_Denotes hloc hP]
      exact M.rule_eqs e hin _ ρ₀ P hP
    | _ => trivial

/-- **The invariant's model is local in its levels** (`acval_params`). -/
theorem cvalLocal_ofEnvModelM {env : Env} (m : Model.EnvModelM V env) :
    CvalLocal (Model.Model.ofEnvModelM m).cval env := by
  intro n ci hf ψ₁ ψ₂ h
  rw [Model.Model.ofEnvModelM_cval]
  unfold Model.cvalOf
  rw [m.base2.acval_params n ci hf ψ₁ ψ₂ h]

end ConLeche
