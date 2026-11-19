module

public import ConLeche.Denotes
public import ConLeche.Model.OfEnvModelM
public import ConLeche.Verify.IsModelRecords
public import ConLeche.Verify.Resolves
import ConLeche.Verify.EnvGuards
import ConLeche.Verify.InstLevels

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
  about the records (`RecordsStored`, `ConLeche/Verify/IsModelRecords.lean`) and that every
  stored ι equation is read (`RuleEqsRead`).
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

/-! ## A resolving term denotes -/

/-- A `Nat` literal denotes, where its constants are stored. -/
theorem Denotes_natLit {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    (hs : natLitSupported env = true) (ρ : BVarIdx → V) :
    ∀ n, ∃ X, Denotes cval env φ ρ (.lit (.natVal n)) X := by
  obtain ⟨_, _, cv0, _, _, _, cv1, _, _, _, -, hz, hsu, -, h0, h1, -⟩ := natLitSupported_inv hs
  intro n
  induction n with
  | zero => exact ⟨_, .natLit (.const hz (by show 0 = cv0.levelParams.length; rw [h0]; rfl))⟩
  | succ n ih =>
    obtain ⟨X, hX⟩ := ih
    exact ⟨_, .natLit (.app (.const hsu (by show 0 = cv1.levelParams.length; rw [h1]; rfl)) hX)⟩

/-- A `String` literal denotes, where its constants are stored. -/
theorem Denotes_strLit {cval : Name → (LevelParam → Nat) → V} {env : Env} {φ : LevelParam → Nat}
    (hs : strLitSupported env = true) (ρ : BVarIdx → V) (s : String) :
    ∃ X, Denotes cval env φ ρ (.lit (.strVal s)) X := by
  obtain ⟨hnat, _, ciO, _, ciN, ciC, ciH, ciF, _, pN, pC,
    -, hO, -, hN, hC, hH, hF, -, hO0, -, hN1, hC1, hH0, hF0, -⟩ := strLitSupported_inv hs
  have hNc : Denotes cval env φ ρ (.const listNilName [.zero]) _ :=
    .const hN (by rw [hN1]; rfl)
  have hCc : Denotes cval env φ ρ (.const listConsName [.zero]) _ :=
    .const hC (by rw [hC1]; rfl)
  have hHc : Denotes cval env φ ρ (.const charName []) _ := .const hH (by rw [hH0]; rfl)
  have hFc : Denotes cval env φ ρ (.const charOfNatName []) _ := .const hF (by rw [hF0]; rfl)
  have hOc : Denotes cval env φ ρ (.const stringOfListName []) _ := .const hO (by rw [hO0]; rfl)
  have hlist : ∀ cs : List Char, ∃ X, Denotes cval env φ ρ
      (cs.foldr
        (init := .app (.const listNilName [.zero]) (.const charName []))
        fun c e =>
          .app (.app (.app (.const listConsName [.zero]) (.const charName []))
            (.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e) X := by
    intro cs
    induction cs with
    | nil => exact ⟨_, .app hNc hHc⟩
    | cons c cs ih =>
      obtain ⟨X, hX⟩ := ih
      obtain ⟨Y, hY⟩ := Denotes_natLit (cval := cval) (φ := φ) hnat ρ c.toNat
      exact ⟨_, .app (.app (.app hCc hHc) (.app hFc hY)) hX⟩
  obtain ⟨X, hX⟩ := hlist s.toList
  exact ⟨_, .strLit (.app hOc hX)⟩

/-- **A resolving term denotes**, at every variable environment: `Denotes` asks only that its
parts read (`Expr.Resolves`). -/
theorem Denotes_of_resolves {cval : Name → (LevelParam → Nat) → V} {env : Env}
    (φ : LevelParam → Nat) :
    ∀ (e : Expr) (ρ : BVarIdx → V), e.Resolves env → ∃ v, Denotes cval env φ ρ e v
  | .bvar _, _, _ => ⟨_, .bvar⟩
  | .sort _, _, _ => ⟨_, .sort⟩
  | .fvar _ _, _, h => h.elim
  | .const _ _, _, ⟨_, hf, hlen⟩ => ⟨_, .const hf hlen⟩
  | .app f a, ρ, ⟨hf, ha⟩ => by
    obtain ⟨F, hF⟩ := Denotes_of_resolves φ f ρ hf
    obtain ⟨X, hX⟩ := Denotes_of_resolves φ a ρ ha
    exact ⟨_, .app hF hX⟩
  | .lam ty b, ρ, ⟨hty, hb⟩ => by
    obtain ⟨A, hA⟩ := Denotes_of_resolves φ ty ρ hty
    have hB := fun x => Denotes_of_resolves (cval := cval) φ b (push x ρ) hb
    exact ⟨_, .lam hA (F := fun x => (hB x).choose) fun x _ => (hB x).choose_spec⟩
  | .forallE ty b, ρ, ⟨hty, hb⟩ => by
    obtain ⟨A, hA⟩ := Denotes_of_resolves φ ty ρ hty
    have hB := fun x => Denotes_of_resolves (cval := cval) φ b (push x ρ) hb
    exact ⟨_, .pi hA (B := fun x => (hB x).choose) fun x _ => (hB x).choose_spec⟩
  | .letE _ v b, ρ, ⟨hv, hb⟩ => by
    obtain ⟨Y, hY⟩ := Denotes_of_resolves φ v ρ hv
    obtain ⟨X, hX⟩ := Denotes_of_resolves φ b (push Y ρ) hb
    exact ⟨_, .letE hY hX⟩
  | .proj _ _ e, ρ, ⟨ht, he⟩ => by
    obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp ht
    obtain ⟨P, hP⟩ := Denotes_of_resolves φ e ρ he
    exact ⟨_, .proj_table hentry hP⟩
  | .lit (.natVal n), ρ, h => Denotes_natLit h ρ n
  | .lit (.strVal s), ρ, h => Denotes_strLit h ρ s

/-! ## The clauses -/

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
    (hloc : CvalLocal M.cval env) (hrec : RecordsStored ds env)
    (hread : RuleEqsRead M.cval env) :
    IsModel V (posModel M.cval env) ds := by
  intro d hd c hc vals hl
  obtain ⟨ci, hf, hcv, hdef, hrc, -⟩ := hrec d hd c hc
  have hmem : ci ∈ env.consts := Env.find?_mem hf
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
      obtain ⟨cj, hfj, hcjv, -, -, hcjc⟩ := hrec d' hd' _ hcj
      obtain ⟨nF', T', rfl⟩ := hcjc cvj cnP nF T rfl
      have hnj : (ConstantInfo.ctorInfo cvj cnP nF T).name = cvj.name := rfl
      rw [hnj] at hfj
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

theorem ctorLevels_length (rl : RecRule) (lps : List Name) :
    (rl.ctorLevels lps).length = recFireLevelCount rl lps := by
  unfold RecRule.ctorLevels recFireLevelCount
  cases rl.fire <;> simp

/-- **Every stored ι equation is read**, in the model the invariant carries, where `Eq` is
stored: each equation resolves (`iotaEqAt_resolves`) — the stored types because the invariant
reads them (`type_reads`), the right-hand side because the rule's law reads it, the nested pins as
arguments of the recursor type's major, the constructor at the rule's levels by the rule's fit
(`RecRuleLevels`), `Eq` at one level by its pin. -/
theorem ruleEqsRead_ofEnvModelM {env : Env} (m : Model.EnvModelM V env)
    (heq : (env.find? eqName).isSome = true) :
    RuleEqsRead (Model.Model.ofEnvModelM m).cval env := by
  intro e he φ ρ
  refine Denotes_of_resolves φ e ρ ?_
  have htype : ∀ ci ∈ env.consts, ci.toConstantVal.type.Resolves env := fun ci hci => by
    obtain ⟨ta, hta⟩ := m.type_reads ci hci (fun _ => 0)
    obtain ⟨hnf, -, -, hlb, -⟩ := m.base2.wf.consts ci hci
    exact resolves_of_denote_closed hta hnf hlb
  -- the recursor and the rule
  simp only [ruleEqs, List.mem_flatMap] at he
  obtain ⟨c, -, he⟩ := he
  split at he
  rotate_left
  · exact absurd he List.not_mem_nil
  rename_i cv mI rP isK rules hf
  obtain ⟨rl, hrl, hiota⟩ := List.mem_filterMap.mp he
  unfold iotaEq at hiota
  simp only [bind, Option.bind_eq_some_iff] at hiota
  obtain ⟨cj, hcj, hiota⟩ := hiota
  cases cj with
  | ctorInfo cvj cnP cnF iT =>
    have hrecmem := Env.find?_mem hf
    have hnm : cv.name = c.name := find?_name hf
    have hfR : env.find? cv.name = some (.recInfo cv mI rP isK rules) := by rw [hnm]; exact hf
    obtain ⟨-, -, -, -, -, hrec'⟩ := m.base2.wf.consts _ hrecmem
    obtain ⟨hnf, -, -, hlb, hnest⟩ := hrec' cv mI rP isK rules rfl rl hrl
    have hcv : cv.type.Resolves env := htype _ hrecmem
    have hlaw := m.rec_rules φ c.name cv mI rP isK rules hf rl hrl
    -- the right-hand side, read by the rule's law
    have hrhs : rl.rhs.Resolves env := by
      obtain ⟨Ra, hRa, -⟩ := hlaw.2.1 (cv.levelParams.map .param) (by simp)
      refine (Expr.resolves_instantiateLevelParams _ _ _).mp
        (resolves_of_denote_closed hRa ?_ ?_)
      · rw [Expr.hasFvar_instantiateLevelParams]; exact hnf
      · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hlb
    -- the nested pins, arguments of the major's domain
    have hpins : ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, p.Resolves env := by
      intro lvls pins hfire p hp
      obtain ⟨-, -, -, pre, dom, body, D, hstrip, -, hargs, -⟩ := hnest lvls pins hfire
      obtain ⟨-, hfa⟩ := Expr.resolves_stripPis _ _ hstrip hcv
      obtain ⟨-, hda⟩ := Expr.resolves_getApp dom hfa.1
      refine (Expr.resolves_liftLooseBVars (mI - rP) p 0).mp (hda _ ?_)
      rw [hargs]
      exact List.mem_append_left _ (List.mem_map_of_mem hp)
    -- the three constants
    have hcount := hlaw.2.2.2.1 cvj cnP cnF iT hcj
    obtain ⟨ciE, hfE⟩ := Option.isSome_iff_exists.mp heq
    obtain ⟨-, -, hlE⟩ := (m.base2.basis_pinned _ _ hfE (by decide)).1
    exact iotaEqAt_resolves hcv (htype _ (Env.find?_mem hcj)) hrhs hpins
      ⟨_, hfR, rfl⟩ ⟨_, hcj, by rw [ctorLevels_length]; exact hcount⟩ ⟨ciE, hfE, hlE.symm⟩ hiota
  | _ => exact nomatch hiota

/-- **The invariant's model is local in its levels** (`acval_params`). -/
theorem cvalLocal_ofEnvModelM {env : Env} (m : Model.EnvModelM V env) :
    CvalLocal (Model.Model.ofEnvModelM m).cval env := by
  intro n ci hf ψ₁ ψ₂ h
  rw [Model.Model.ofEnvModelM_cval]
  unfold Model.cvalOf
  rw [m.base2.acval_params n ci hf ψ₁ ψ₂ h]

end ConLeche
