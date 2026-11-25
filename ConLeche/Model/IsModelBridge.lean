module

import ConLeche.Denotes
public import ConLeche.Model.RuleEqsSound
import ConLeche.Model.OfEnvModelM
public import ConLeche.Verify.IsModelRecords
public import ConLeche.Verify.Resolves
import ConLeche.Model.IotaReadSem
import ConLeche.Verify.EnvGuards
import ConLeche.Verify.InstLevels

public section

/-!
# From a model of the checker's environment to a model of its input (task #617)

The proofs' invariant `EnvModelM V env` carries a model of the environment the checker builds,
read by the relation `Denotes` (`Model.ofEnvModelM`); `IsModel V model R`
(`ConLeche/IsModel.lean`) is the public notion, over the input.  This module carries the first to
the second.

* `posModel`: the internal valuation `cval`, which reads a level ASSIGNMENT, made positional
  through the stored constant's level parameters.  A stream need not declare `Eq`; where it does
  not, the model gives the name `Eq` the equality relation (`eqRel`), which is what the
  recursors' rules are equations of.
* `eval_of_Denotes`: wherever the relation `Denotes` reads a term, the total reading
  `Expr.eval` at `posModel` agrees with it.  The one fact this needs of `cval` is that a
  constant reads only its own level parameters (`CvalLocal`; the invariant's `acval_params`).
* `Denotes_of_resolves`: a term every part of which reads (`Expr.Resolves`) denotes.
* `isModel_of_agree`: the clauses, from the invariant, given what the checker establishes
  about the records (`RecordsStored`, `ConLeche/Verify/IsModelRecords.lean`), at every model that
  agrees with `posModel` on the stored names (`AgreesOn`) and reads `Eq` as equality
  (`EqReads`): what a model gives a name the environment does not store is free.  At `posModel`
  itself, `isModel_of_envModelM`.  A recursor rule
  holds because at every fit of its equation's telescope the two sides are one member of a type
  (`Model.ruleEq_sides`), and `Eq` — stored or not — reads as equality there.
-/

namespace ConLeche

open SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- **Equality at the universe `k`**: `@Eq.{k} A a b` is the truth value of `a = b`. -/
noncomputable def eqRel (k : Nat) : V :=
  lamV (univ k)
    (fun A => lamV A
      (fun a => lamV A (fun b => eqv a b)
        (hasGraph_of_defFun1 (DefFun.eqv_apply (DefFun.const a) (DefFun.proj 0))))
      (hasGraph_of_defFun1 (DefFun.lamV_apply_curry
        (DefFun.eqv_apply (DefFun.proj 1) (DefFun.proj 0)) (DefFun.const A))))
    (hasGraph_of_defFun1 (DefFun.lamV_apply_curry
      (DefFun.lamV_apply_curry
        (DefFun.eqv_apply (DefFun.proj 1) (DefFun.proj 0)) (DefFun.proj 1))
      (DefFun.proj 0)))

/-- The internal valuation, positional: a stored constant's level values go to its level
parameters in order.  An undeclared `Eq` is equality (`eqRel`); any other undeclared name is
`∅`. -/
noncomputable def posModel (cval : Name → (LevelParam → Nat) → V) (env : Env) :
    Name → List Nat → V := fun n vals =>
  match env.find? n with
  | some ci => cval n (Level.assign ci.toConstantVal.levelParams vals)
  | none => if n = eqName then eqRel (vals.headD 0) else empty

/-- A stored constant's value, positionally: through its own level parameters. -/
theorem posModel_of_find {cval : Name → (LevelParam → Nat) → V} {env : Env} {n : Name}
    {ci : ConstantInfo} (h : env.find? n = some ci) (vals : List Nat) :
    posModel cval env n vals = cval n (Level.assign ci.toConstantVal.levelParams vals) := by
  unfold posModel; rw [h]

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
  cases n with
  | zero =>
    simp only [natLitToConstructor, eval_const, eval_lit_nat, natLitVal, List.map_nil]
  | succ n =>
    simp only [natLitToConstructor, eval_app, eval_const, eval_lit_nat, natLitVal, List.map_nil]

theorem eval_strLitToConstructor (model : Name → List Nat → V) (φ : LevelParam → Nat)
    (ρ : BVarIdx → V) (s : String) :
    Expr.eval model φ ρ (strLitToConstructor s) = Expr.eval model φ ρ (.lit (.strVal s)) := by
  simp only [strLitToConstructor, eval_app, eval_const, eval_lit_str,
    strLitVal, List.map_nil]
  congr 1
  induction s.toList with
  | nil => simp only [List.foldr_nil, eval_app, eval_const, List.map_cons,
      List.map_nil, Level.eval]
  | cons c cs ih =>
    simp only [List.foldr_cons, eval_app, eval_const, eval_lit_nat,
      List.map_cons, List.map_nil, Level.eval, ih]

/-- **A model agreeing with `posModel` on the stored names**: it reads every stored constant
as the positional valuation does (what it gives an unstored name is free). -/
@[expose] def AgreesOn (model : Name → List Nat → V) (cval : Name → (LevelParam → Nat) → V) (env : Env) :
    Prop :=
  ∀ n ci, env.find? n = some ci → model n = posModel cval env n

theorem agreesOn_posModel (cval : Name → (LevelParam → Nat) → V) (env : Env) :
    AgreesOn (posModel cval env) cval env := fun _ _ _ => rfl

/-- **The total reading agrees with `Denotes`** wherever that reads, at every model agreeing
with `posModel` on the stored names. -/
theorem eval_of_Denotes {cval : Name → (LevelParam → Nat) → V} {env : Env}
    (hloc : CvalLocal cval env) {model : Name → List Nat → V} (hag : AgreesOn model cval env)
    {φ : LevelParam → Nat} {ρ : BVarIdx → V} {e : Expr} {v : V}
    (h : Denotes cval env φ ρ e v) : Expr.eval model φ ρ e = v := by
  induction h with
  | bvar => rw [eval_bvar]
  | sort => rw [eval_sort]
  | @const ρ n us ci hf hlen =>
    rw [eval_const, hag n ci hf]
    unfold posModel
    rw [hf]
    exact hloc n ci hf _ _ (assign_map_eval φ _ us hlen)
  | app _ _ ihf iha =>
    rw [eval_app, ihf, iha]
  | lam _ _ _ ihA ihF =>
    rw [eval_lam]
    exact lamV_ext ihA _ _ fun x hx => ihF x (ihA ▸ hx)
  | pi _ _ _ ihA ihB =>
    rw [eval_forallE]
    exact piV_ext ihA _ _ fun x hx => ihB x (ihA ▸ hx)
  | letE _ _ ihv ihb =>
    rw [eval_letE, ihv]
    exact ihb
  | proj_table _ _ ih =>
    rw [eval_proj, ih]
  | @natLit ρ n X _ ih =>
    rw [← eval_natLitToConstructor]
    exact ih
  | @strLit ρ s X _ ih =>
    rw [← eval_strLitToConstructor]
    exact ih

/-- **The invariant's model is local in its levels** (`acval_params`). -/
theorem cvalLocal_ofEnvModelM {env : Env} (m : Model.EnvModelM V env) :
    CvalLocal (Model.cvalOf (V := V) m.base2.acval) env := by
  intro n ci hf ψ₁ ψ₂ h
  unfold Model.cvalOf
  rw [m.base2.acval_params n ci hf ψ₁ ψ₂ h]

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

def assignWith (φ : LevelParam → Nat) : List Name → List Nat → LevelParam → Nat
  | k :: ks, v :: vs, p => if k = p then v else assignWith φ ks vs p
  | _, _, p => φ p

theorem assignWith_map_eval (φ : LevelParam → Nat) :
    ∀ (ps : List Name) (us : List Level),
      assignWith φ ps (us.map (Level.eval φ)) = Level.substFn φ ps us
  | [], _ => rfl
  | _ :: _, [] => rfl
  | k :: ks, u :: us => by
    funext p
    simp only [List.map_cons, assignWith, Level.substFn]
    split
    · rfl
    · exact congrFun (assignWith_map_eval φ ks us) p

noncomputable def cvalModel (cval : Name → (LevelParam → Nat) → V) (env : Env)
    (φ : LevelParam → Nat) : Name → List Nat → V := fun n vals =>
  match env.find? n with
  | some ci => cval n (assignWith φ ci.toConstantVal.levelParams vals)
  | none => empty

theorem cvalModel_const {cval : Name → (LevelParam → Nat) → V} {env : Env}
    {φ : LevelParam → Nat} {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) (us : List Level) :
    cvalModel cval env φ n (us.map (Level.eval φ)) =
      cval n (Level.substFn φ ci.toConstantVal.levelParams us) := by
  simp only [cvalModel, hf, assignWith_map_eval]

theorem Denotes_natLit_eval {cval : Name → (LevelParam → Nat) → V} {env : Env}
    {φ : LevelParam → Nat} (hs : natLitSupported env = true) (ρ : BVarIdx → V) :
    ∀ n, Denotes cval env φ ρ (.lit (.natVal n))
      (Expr.eval (cvalModel cval env φ) φ ρ (.lit (.natVal n))) := by
  obtain ⟨_, _, cv0, _, _, _, cv1, _, _, _, -, hz, hsu, -, h0, h1, -⟩ := natLitSupported_inv hs
  intro n
  induction n with
  | zero =>
    rw [← eval_natLitToConstructor, natLitToConstructor, eval_const, List.map_nil,
      show ([] : List Nat) = ([] : List Level).map (Level.eval φ) from rfl,
      cvalModel_const hz []]
    exact .natLit (.const hz (by show 0 = cv0.levelParams.length; rw [h0]; rfl))
  | succ n ih =>
    rw [← eval_natLitToConstructor, natLitToConstructor, eval_app, eval_const, List.map_nil,
      show ([] : List Nat) = ([] : List Level).map (Level.eval φ) from rfl,
      cvalModel_const hsu []]
    exact .natLit (.app (.const hsu (by show 0 = cv1.levelParams.length; rw [h1]; rfl)) ih)

theorem Denotes_strLit_eval {cval : Name → (LevelParam → Nat) → V} {env : Env}
    {φ : LevelParam → Nat} (hs : strLitSupported env = true) (ρ : BVarIdx → V) (s : String) :
    Denotes cval env φ ρ (.lit (.strVal s))
      (Expr.eval (cvalModel cval env φ) φ ρ (.lit (.strVal s))) := by
  obtain ⟨hnat, _, ciO, _, ciN, ciC, ciH, ciF, _, pN, pC,
    -, hO, -, hN, hC, hH, hF, -, hO0, -, hN1, hC1, hH0, hF0, -⟩ := strLitSupported_inv hs
  have hNc : Denotes cval env φ ρ (.const listNilName [.zero])
      (Expr.eval (cvalModel cval env φ) φ ρ (.const listNilName [.zero])) := by
    rw [eval_const, cvalModel_const hN [.zero]]
    exact .const hN (by rw [hN1]; rfl)
  have hCc : Denotes cval env φ ρ (.const listConsName [.zero])
      (Expr.eval (cvalModel cval env φ) φ ρ (.const listConsName [.zero])) := by
    rw [eval_const, cvalModel_const hC [.zero]]
    exact .const hC (by rw [hC1]; rfl)
  have hHc : Denotes cval env φ ρ (.const charName [])
      (Expr.eval (cvalModel cval env φ) φ ρ (.const charName [])) := by
    rw [eval_const, cvalModel_const hH []]
    exact .const hH (by rw [hH0]; rfl)
  have hFc : Denotes cval env φ ρ (.const charOfNatName [])
      (Expr.eval (cvalModel cval env φ) φ ρ (.const charOfNatName [])) := by
    rw [eval_const, cvalModel_const hF []]
    exact .const hF (by rw [hF0]; rfl)
  have hOc : Denotes cval env φ ρ (.const stringOfListName [])
      (Expr.eval (cvalModel cval env φ) φ ρ (.const stringOfListName [])) := by
    rw [eval_const, cvalModel_const hO []]
    exact .const hO (by rw [hO0]; rfl)
  let tailE : List Char → Expr := fun cs => cs.foldr
    (init := Expr.app (.const listNilName [.zero]) (.const charName []))
    fun c e =>
      Expr.app (Expr.app (Expr.app (.const listConsName [.zero]) (.const charName []))
        (Expr.app (.const charOfNatName []) (.lit (.natVal c.toNat)))) e
  have hlist : ∀ cs : List Char, Denotes cval env φ ρ (tailE cs)
      (Expr.eval (cvalModel cval env φ) φ ρ (tailE cs)) := by
    intro cs
    induction cs with
    | nil => exact .app hNc hHc
    | cons c cs ih =>
      exact .app (.app (.app hCc hHc) (.app hFc (Denotes_natLit_eval hnat ρ c.toNat))) ih
  rw [← eval_strLitToConstructor]
  exact .strLit (.app hOc (hlist s.toList))

theorem Denotes_eval_of_resolves {cval : Name → (LevelParam → Nat) → V} {env : Env}
    (φ : LevelParam → Nat) :
    ∀ (e : Expr) (ρ : BVarIdx → V), e.Resolves env →
      Denotes cval env φ ρ e (Expr.eval (cvalModel cval env φ) φ ρ e)
  | .bvar i, ρ, _ => by rw [eval_bvar]; exact .bvar
  | .sort u, ρ, _ => by rw [eval_sort]; exact .sort
  | .fvar _ _, _, h => h.elim
  | .const n us, ρ, ⟨ci, hf, hlen⟩ => by
    rw [eval_const, cvalModel_const hf us]
    exact .const hf hlen
  | .app f a, ρ, ⟨hf, ha⟩ => by
    rw [eval_app]
    exact .app (Denotes_eval_of_resolves φ f ρ hf) (Denotes_eval_of_resolves φ a ρ ha)
  | .lam ty b, ρ, ⟨hty, hb⟩ => by
    rw [eval_lam]
    exact .lam (Denotes_eval_of_resolves φ ty ρ hty)
      (fun x _ => Denotes_eval_of_resolves φ b (push x ρ) hb)
      (eval_hasGraph_push (cvalModel cval env φ) φ ρ _ b)
  | .forallE ty b, ρ, ⟨hty, hb⟩ => by
    rw [eval_forallE]
    exact .pi (Denotes_eval_of_resolves φ ty ρ hty)
      (fun x _ => Denotes_eval_of_resolves φ b (push x ρ) hb)
      (eval_hasSigmaPairs_push (cvalModel cval env φ) φ ρ _ b)
  | .letE _ v b, ρ, ⟨hv, hb⟩ => by
    rw [eval_letE]
    exact .letE (Denotes_eval_of_resolves φ v ρ hv)
      (Denotes_eval_of_resolves φ b (push _ ρ) hb)
  | .proj _ _ e, ρ, ⟨ht, he⟩ => by
    obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp ht
    rw [eval_proj]
    exact .proj_table hentry (Denotes_eval_of_resolves φ e ρ he)
  | .lit (.natVal n), ρ, h => Denotes_natLit_eval h ρ n
  | .lit (.strVal s), ρ, h => Denotes_strLit_eval h ρ s

/-- **A resolving term denotes**, at every variable environment: `Denotes` asks only that its
parts read (`Expr.Resolves`). -/
theorem Denotes_of_resolves {cval : Name → (LevelParam → Nat) → V} {env : Env}
    (φ : LevelParam → Nat) (e : Expr) (ρ : BVarIdx → V) (h : e.Resolves env) :
    ∃ v, Denotes cval env φ ρ e v :=
  ⟨_, Denotes_eval_of_resolves φ e ρ h⟩

/-! ## The clauses -/

theorem find?_name {env : Env} {n : Name} {ci : ConstantInfo} (h : env.find? n = some ci) :
    ci.name = n := by
  have := List.find?_some h
  simpa using this

theorem ctorLevels_length (rl : RecRule) (lps : List Name) :
    (rl.ctorLevels lps).length = recFireLevelCount rl lps := by
  unfold RecRule.ctorLevels recFireLevelCount
  cases rl.fire <;> simp

/-- **A telescope of resolving domains reads as a true proposition** where its body does at every
fit of the domains. -/
theorem eval_tele {cval : Name → (LevelParam → Nat) → V} {env : Env} (hloc : CvalLocal cval env)
    {model : Name → List Nat → V} (hag : AgreesOn model cval env) {φ : LevelParam → Nat} {B : Expr} :
    ∀ (ds : List Expr) (ρ : BVarIdx → V), (∀ d ∈ ds, d.Resolves env) →
      (∀ (vs : List V) (ρ' : BVarIdx → V), vs.length = ds.length →
        Model.Fits cval env φ ρ (ds.foldr .forallE B) vs ρ' B →
        Expr.eval model φ ρ' B ∈ˢ (univZero : V) ∧
          (pt : V) ∈ˢ Expr.eval model φ ρ' B) →
      Expr.eval model φ ρ (ds.foldr .forallE B) ∈ˢ (univZero : V) ∧
        (pt : V) ∈ˢ Expr.eval model φ ρ (ds.foldr .forallE B)
  | [], ρ, _, h => h [] ρ rfl .nil
  | d :: ds, ρ, hr, h => by
    obtain ⟨A, hA⟩ := Denotes_of_resolves (cval := cval) φ d ρ (hr d List.mem_cons_self)
    have hz : ∀ x, x ∈ˢ A →
        Expr.eval model φ (push x ρ) (ds.foldr .forallE B) ∈ˢ (univZero : V) ∧
          (pt : V) ∈ˢ Expr.eval model φ (push x ρ) (ds.foldr .forallE B) :=
      fun x hx => eval_tele hloc hag ds (push x ρ) (fun d' h' => hr d' (List.mem_cons_of_mem _ h'))
        fun vs ρ' hl hf => h (x :: vs) ρ' (by simp [hl]) (.cons hA hx hf)
    rw [show (d :: ds).foldr .forallE B = .forallE d (ds.foldr .forallE B) from rfl,
      eval_forallE]
    have hdom : Expr.eval model φ ρ d = A := eval_of_Denotes hloc hag hA
    refine ⟨?_, ?_⟩
    · rw [piV_eq_zero fun x hx => (hz x (hdom ▸ hx)).1]; exact piR_zero_mem_univZero
    · exact (pt_mem_piV_iff (hS := eval_hasSigmaPairs_push model φ ρ (Expr.eval model φ ρ d)
          (ds.foldr .forallE B))
        fun x hx => Or.inl (hz x (hdom ▸ hx)).1).mpr fun x hx => (hz x (hdom ▸ hx)).2

/-- **`Eq` reads as equality** in the model the invariant carries, declared or not: at a type of
the universe and two of its members, its triple application is the truth value of their
equality. -/
theorem eval_eq {env : Env} (m : Model.EnvModelM V env) {φ : LevelParam → Nat}
    {ρ : BVarIdx → V} {u : Level} {T L R : V}
    (hT : T ∈ˢ (univ (Level.eval φ u) : V)) (hL : L ∈ˢ T) (hR : R ∈ˢ T) :
    app (app (app (Expr.eval (posModel (Model.cvalOf m.base2.acval) env) φ ρ
      (.const eqName [u])) T) L) R = eqv L R := by
  show app (app (app (posModel _ env eqName [Level.eval φ u]) T) L) R = _
  cases hfe : env.find? eqName with
  | none =>
    unfold posModel
    rw [hfe]
    simp only [↓reduceIte, List.headD_cons, eqRel]
    rw [app_lamV hT, app_lamV hL, app_lamV hR]
  | some ci =>
    obtain ⟨-, -, hl⟩ := (m.base2.basis_pinned _ _ hfe (by decide)).1
    have hD : Denotes (Model.cvalOf m.base2.acval) env φ ρ (.const eqName [u]) _ :=
      .const hfe (by rw [hl]; rfl)
    have hE : posModel (Model.cvalOf m.base2.acval) env eqName [Level.eval φ u] = _ :=
      eval_of_Denotes (cvalLocal_ofEnvModelM m) (agreesOn_posModel _ _) hD
    rw [hE]
    exact Model.eq_equality_of m u φ ρ _ T L R hD hT hL hR

/-- **`Eq` reads as equality** in `model`: at a type of a universe and two of its members, the
triple application of `Eq`'s value at that universe is the truth value of their equality. -/
@[expose] def EqReads (model : Name → List Nat → V) : Prop :=
  ∀ (k : Nat) (T L R : V), T ∈ˢ (univ k : V) → L ∈ˢ T → R ∈ˢ T →
    app (app (app (model eqName [k]) T) L) R = eqv L R

/-- The invariant's model reads `Eq` as equality. -/
theorem eqReads_envModelM {env : Env} (m : Model.EnvModelM V env) :
    EqReads (V := V) (posModel (Model.cvalOf m.base2.acval) env) := by
  intro k T L R hT hL hR
  exact eval_eq m (φ := fun _ => k) (ρ := ρ₀) (u := .param .anonymous) hT hL hR

/-- **A fit of the statement's ι telescope is a fit of the proofs'** (the checker's rule): the
prefix is shared; the fields' domains are the constructor's up to equivalent levels, or up to
consumed annotations, whose meaning — the identity on a type — is read in the constructor's own
telescope (graded by the invariant, `type_wellDenotedTy`), which a plain rule's parameters fit
through the recursor's parameter domains (`paramsAnnEq`). -/
theorem fits_rule_transfer {env : Env} (m : Model.EnvModelM V env)
    {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (hf : env.find? cv.name = some (.recInfo cv mI rP isK rules))
    {rl : RecRule} {cvj : ConstantVal} {cnP nF0 : Nat} {T0 : Name}
    (hfj : env.find? rl.ctor = some (.ctorInfo cvj cnP nF0 T0))
    {pre : List Expr} {rest : Expr} (hpre : cv.type.stripPis rP = some (pre, rest))
    {p' p : IotaParts} (hp : iotaPartsAt cvj cnP mI rP rl = some p)
    (hfd : listRel Expr.lvlEq p'.fieldDoms p.fieldDoms = true ∨
      (rl.fire = .plain ∧ paramsAnnEq env.find? cvj cnP cv rl = true ∧
        listRel (annEq env.find?) p'.fieldDoms p.fieldDoms = true))
    (hfdR : ∀ d ∈ p.fieldDoms, d.Resolves env) {B : Expr} {φ : LevelParam → Nat}
    {ρ ρ' : Nat → V} {vs : List V} (hvl : vs.length = (pre ++ p'.fieldDoms).length)
    (hvf : Model.Fits (Model.cvalOf m.base2.acval) env φ ρ
      ((pre ++ p'.fieldDoms).foldr .forallE B) vs ρ' B) :
    Model.Fits (Model.cvalOf m.base2.acval) env φ ρ ((pre ++ p.fieldDoms).foldr .forallE B)
      vs ρ' B := by
  let M := Model.Model.ofEnvModelM m
  have hcl := m.base2.cval_closed
  obtain ⟨hpreEq, hprel⟩ := Model.stripPis_eq_foldr rP hpre
  have hl' : p'.fieldDoms.length = p.fieldDoms.length := by
    rcases hfd with h | h
    · exact listRel_length h
    · exact listRel_length h.2.2
  simp only [List.length_append] at hvl
  rw [← List.take_append_drop rP vs] at hvf ⊢
  obtain ⟨ρ₁, R₁, h1, h2⟩ := hvf.split
  obtain ⟨hR₁, hρ₁, hxfit⟩ := h1.foldr_prefix (pre ++ p'.fieldDoms) _ rfl
    (by rw [List.length_take, List.length_append]; omega)
  have hxl : (vs.take rP).length = rP := by rw [List.length_take]; omega
  rw [hxl, List.drop_left' hprel] at hR₁
  rw [hxl, List.take_left' hprel] at hxfit
  subst hR₁ hρ₁
  have hfl : (vs.drop rP).length = p'.fieldDoms.length := by rw [List.length_drop]; omega
  generalize hxs : vs.take rP = xs at *
  generalize vs.drop rP = fs at *
  suffices h2' : Model.Fits (Model.cvalOf m.base2.acval) env φ (Model.consN xs ρ)
      (p.fieldDoms.foldr .forallE B) fs ρ' B by
    have := (hxfit (p.fieldDoms.foldr .forallE B)).append h2'
    rwa [List.foldr_append]
  rcases hfd with hfd | ⟨hplain, hpar, hfd⟩
  · exact Model.fits_lvlEq _ _ _ _ hfd hfl h2
  -- the annotated case: the constructor's telescope, graded, at the parameters' values
  have hdef : ∀ n cv v hint, env.find? n = some (.defnInfo cv v hint) →
      ∀ ψ (ρ : Nat → V), Denotes (Model.cvalOf m.base2.acval) env ψ ρ v
        (Model.cvalOf m.base2.acval n ψ) := by
    intro n cv v hint hn ψ ρ
    have := M.defn_eq cv v hint (Env.find?_mem hn) ψ ρ
    rwa [show cv.name = n from find?_name hn, Model.Model.ofEnvModelM_cval m] at this
  have hmem : ∀ n ci, env.find? n = some ci → ∀ ψ (ρ : Nat → V), ∃ T,
      Denotes (Model.cvalOf m.base2.acval) env ψ ρ ci.toConstantVal.type T ∧
        Model.cvalOf m.base2.acval n ψ ∈ˢ T := by
    intro n ci hn ψ ρ
    have := M.mem ci (Env.find?_mem hn) ψ ρ
    rwa [show ci.name = n from find?_name hn, Model.Model.ofEnvModelM_cval m] at this
  have htype : ∀ ci ∈ env.consts, ci.toConstantVal.type.Resolves env := fun ci hci => by
    obtain ⟨ta, hta⟩ := m.type_reads ci hci (fun _ => 0)
    obtain ⟨hnf, -, -, hlb, -⟩ := m.base2.wf.consts ci hci
    exact resolves_of_denote_closed hta hnf hlb
  obtain ⟨pd, ctorBody, concl, hcb, hfdS, hplen, -, -⟩ := iotaPartsAt_inv hp
  obtain ⟨rd, r, pd', c, hrd, hpd', hpar'⟩ := paramsAnnEq_inv hpar
  rw [hcb] at hpd'
  cases hpd'
  have hps : rl.iotaParams rP cnP = (List.range (min cnP rP)).map fun i => .bvar (rP - 1 - i) := by
    unfold RecRule.iotaParams; rw [hplain]
  have hcr : cnP ≤ rP := by
    have := hplen; rw [hps, List.length_map, List.length_range] at this; omega
  have hlv : rl.ctorLevels cvj.levelParams = cvj.levelParams.map .param := by
    unfold RecRule.ctorLevels; rw [hplain]
  rw [hlv, Expr.instantiateLevelParams_self] at hcb
  have hrd' := Model.stripPis_take hpre hcr
  rw [hrd] at hrd'
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hrd')
  -- the constructor's stored type: closed, read, graded
  have hmemC := Env.find?_mem hfj
  obtain ⟨hnfC, -, -, hlbC, -⟩ := m.base2.wf.consts _ hmemC
  simp only [ConstantInfo.toConstantVal] at hnfC hlbC
  obtain ⟨hcbEq, hpdl⟩ := Model.stripPis_eq_foldr cnP hcb
  obtain ⟨ta, hta⟩ := m.type_reads _ hmemC φ
  have hG : Model.GradedTele (Model.cvalOf m.base2.acval) env φ (Model.consN xs ρ)
      (cnP + p.fieldDoms.length) (pd.foldr .forallE ctorBody) := by
    have := Model.gradedTele_of_wd hcl (cnP + p.fieldDoms.length) cvj.type hta
      (Model.fvarsBelow_zero_of_not_hasFvar hnfC) hlbC
      (m.type_wellDenotedTy _ hmemC φ ta hta (Model.consN xs ρ)).1
    rwa [Expr.closeN_of_hasFvar _ 0 0 hnfC, hcbEq] at this
  have hpdR : ∀ d ∈ pd, d.Resolves env :=
    (Expr.resolves_stripPis cnP _ hcb (htype _ hmemC)).1
  -- the parameters' values fit the recursor's parameter domains, at any environment
  have hPfit : Model.Fits (Model.cvalOf m.base2.acval) env φ ρ
      ((pre.take cnP).foldr .forallE (.sort .zero)) (xs.take cnP)
      (Model.consN (xs.take cnP) ρ) (.sort .zero) := by
    have h := hxfit (.sort .zero)
    rw [← List.take_append_drop cnP xs] at h
    obtain ⟨ρ₂, R₂, h3, -⟩ := h.split
    obtain ⟨-, hρ₂, h5⟩ := h3.foldr_prefix pre _ rfl (by rw [List.length_take]; omega)
    subst hρ₂
    have := h5 (.sort .zero)
    rwa [List.length_take, Nat.min_eq_left (by omega)] at this
  have hlbR : cv.type.looseBVarsBounded 0 = true := (m.base2.wf.consts _ (Env.find?_mem hf)).2.2.2.1
  rw [hpreEq] at hlbR
  have hPfit' := Model.Fits_shift (pre.take cnP) (.sort .zero) (k := 0) (σ := Model.consN xs ρ)
    (by rw [List.length_take, List.length_take]; omega)
    (fun i hi => by
      rw [List.getElem_take]
      simpa using Model.looseBVarsBounded_foldr_dom pre hlbR i (by
        rw [List.length_take] at hi; omega))
    (fun i hi => absurd hi (Nat.not_lt_zero _)) hPfit
  -- … hence the constructor's parameter domains
  have hPc := Model.fits_annEq hdef hmem (pre.take cnP) pd (.sort .zero) ctorBody hpar'
    (by rw [List.length_take, List.length_take]; omega)
    (Model.gradedTele_le (by omega) hG)
    (fun d hd σ => Denotes_of_resolves φ d σ (hpdR d hd)) hPfit'
  -- the constructor's field domains are graded past them, and so, instantiated, are the rule's
  have hGf := Model.gradedTele_descend pd (n := p.fieldDoms.length)
    (by rw [List.length_take, hpdl]; omega) (by rw [hpdl]; exact hG) hPc
  obtain ⟨hfdEq, -⟩ := Model.stripPis_eq_foldr _ hfdS
  have hlenP : (xs.take cnP).reverse.length = (rl.iotaParams rP cnP).reverse.length := by
    rw [List.length_reverse, List.length_reverse, hplen, List.length_take]; omega
  have hGi := Model.gradedTele_inst (cval := Model.cvalOf m.base2.acval) (env := env) (φ := φ)
    (σ := Model.consN xs ρ) hlenP (fun j hj => by
      have hj' : j < cnP := by rw [List.length_reverse, hplen] at hj; exact hj
      rw [List.getElem_reverse, List.getElem_reverse]
      simp only [hps, List.getElem_map, List.getElem_range]
      have e1 : (xs.take cnP)[(xs.take cnP).length - 1 - j]'(by simp; omega)
          = xs[min cnP rP - 1 - j]'(by omega) := by
        rw [List.getElem_take]; congr 1; simp; omega
      have e2 : Model.consN xs ρ (rP - 1 - (min cnP rP - 1 - j))
          = xs[min cnP rP - 1 - j]'(by omega) := by
        rw [Model.consN_lt xs ρ (by omega)]; congr 1; omega
      simp only [List.length_map, List.length_range] at *
      rw [e1, ← e2]
      exact .bvar)
    (fun v hv => by
      rw [List.mem_reverse, hps] at hv
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hv
      exact ⟨_, rfl⟩)
    p.fieldDoms.length ctorBody (d := 0) (ρ := Model.consN xs ρ) (fun i => rfl)
    (by rw [Model.insAt_zero_reverse]; exact hGf)
  rw [hfdEq] at hGi
  exact Model.fits_annEq hdef hmem _ _ _ _ hfd hfl
    (Model.gradedTele_rebody _ (Nat.le_refl _) hGi)
    (fun d hd σ => Denotes_of_resolves φ d σ (hfdR d hd)) h2

/-- **A rule that reads holds**: its ι equation read off the recursor's type is the stored one
up to the fields' domains, whose fits are the stored one's (`fits_rule_transfer`), where the two
sides are one member of a type (`Model.ruleEq_sides`); `Eq` reads as equality. -/
theorem iotaEqOf_holds {env : Env} (m : Model.EnvModelM V env) {model : Name → List Nat → V}
    (hag : AgreesOn model (Model.cvalOf m.base2.acval) env) (heq : EqReads model)
    {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (hf : env.find? cv.name = some (.recInfo cv mI rP isK rules))
    {i : Nat} {rl : RecRule} (hrl : rules[i]? = some rl)
    (hread : ruleReadsB env.find? cv mI rP i rl = true) {e' : Expr}
    (he' : iotaEqOf cv mI rP i rl = some e') (φ : LevelParam → Nat) :
    ∃ x, x ∈ˢ Expr.eval model φ ρ₀ e' := by
  have hloc := cvalLocal_ofEnvModelM m
  have hmem := Env.find?_mem hf
  have hrlm : rl ∈ rules := List.mem_of_getElem? hrl
  obtain ⟨p', cvj, cnP, nF0, T0, p, hp', hfj, hp, hidx, hus, hps, hfd⟩ := ruleReadsB_inv hread
  obtain ⟨pre, doms, body, u, p'', hfr, hp'', rfl⟩ := iotaEqOf_inv he'
  rw [hp'] at hp''
  cases hp''
  have heAt := iotaEqAt_of (cvj := cvj) (cnP := cnP) hfr hp
  obtain ⟨ty, lhs, rhs, he'B, heB⟩ := iotaEqMk_sides cv rP (mI - rP) pre body u rl hidx hus hps
  rw [heB] at heAt
  -- the stored equation
  have hin : (pre ++ p.fieldDoms).foldr .forallE
      (.app (.app (.app (.const eqName [u]) ty) lhs) rhs) ∈ ruleEqs env := by
    unfold ruleEqs
    refine List.mem_flatMap.mpr ⟨_, hmem, ?_⟩
    rw [show env.find? (ConstantInfo.recInfo cv mI rP isK rules).name =
      some (.recInfo cv mI rP isK rules) from hf]
    refine List.mem_filterMap.mpr ⟨rl, hrlm, ?_⟩
    unfold iotaEq
    rw [hfj]
    exact heAt
  obtain ⟨ds', u', ty', lhs', rhs', he1, H⟩ := Model.ruleEq_sides m
    (fun φ n cv mI rP isK rules hf rl hrl =>
      (m.rec_rules φ n cv mI rP isK rules hf rl hrl).2.2.2) hin
  -- its parts resolve
  have htype : ∀ ci ∈ env.consts, ci.toConstantVal.type.Resolves env := fun ci hci => by
    obtain ⟨ta, hta⟩ := m.type_reads ci hci (fun _ => 0)
    obtain ⟨hnf, -, -, hlb, -⟩ := m.base2.wf.consts ci hci
    exact resolves_of_denote_closed hta hnf hlb
  obtain ⟨-, -, -, -, -, hrec'⟩ := m.base2.wf.consts _ hmem
  obtain ⟨hnf, -, -, hlb, hnest⟩ := hrec' cv mI rP isK rules rfl rl hrlm
  have hcvR : cv.type.Resolves env := htype _ hmem
  have hlaw := m.rec_rules (fun _ => 0) _ cv mI rP isK rules hf rl hrlm
  have hrhs : rl.rhs.Resolves env := by
    obtain ⟨Ra, hRa, -⟩ := hlaw.2.1 (cv.levelParams.map .param) (by simp)
    refine (Expr.resolves_instantiateLevelParams _ _ _).mp
      (resolves_of_denote_closed hRa ?_ ?_)
    · rw [Expr.hasFvar_instantiateLevelParams]; exact hnf
    · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hlb
  have hpins : ∀ lvls pins, rl.fire = .nested lvls pins → ∀ q ∈ pins, q.Resolves env := by
    intro lvls pins hfire q hq
    obtain ⟨-, -, -, pre, dom, body, D, hstrip, -, hargs, -⟩ := hnest lvls pins hfire
    obtain ⟨-, hfa⟩ := Expr.resolves_stripPis _ _ hstrip hcvR
    obtain ⟨-, hda⟩ := Expr.resolves_getApp dom hfa.1
    refine (Expr.resolves_liftLooseBVars (mI - rP) q 0).mp (hda _ ?_)
    rw [hargs]
    exact List.mem_append_left _ (List.mem_map_of_mem hq)
  have hcount := hlaw.2.2.2.1 cvj cnP nF0 T0 hfj
  obtain ⟨ds'', u'', ty'', lhs'', rhs'', he2, hdsR, htyR, hlhsR, hrhsR⟩ :=
    iotaEqAt_parts hcvR (htype _ (Env.find?_mem hfj)) hrhs hpins
      ⟨_, hf, rfl⟩ ⟨_, hfj, by rw [ctorLevels_length]; exact hcount⟩ heAt
  rw [he2] at he1
  obtain ⟨rfl, h1, rfl⟩ := foldr_forallE_app_inj he1
  injection h1 with h2 h3
  subst h3
  injection h2 with h4 h5
  subst h5
  injection h4 with h6 h7
  injection h7 with h8
  subst h8
  have he3 := he2
  obtain ⟨hds, h1', rfl⟩ := foldr_forallE_app_inj he3
  injection h1' with h2' h3'
  subst h3'
  injection h2' with h4' h5'
  subst h5'
  injection h4' with h6' h7'
  injection h7' with h8'
  subst h8'
  subst hds
  -- the statement's fields resolve where the constructor's do
  have hfdR : ∀ d ∈ p.fieldDoms, d.Resolves env := fun d hd => hdsR d (List.mem_append_right _ hd)
  have hfd'R : ∀ d ∈ p'.fieldDoms, d.Resolves env := by
    rcases hfd with h | ⟨-, -, h⟩
    · exact listRel_forall (P := fun a => a.Resolves env) (Q := fun b => b.Resolves env)
        (fun a b hab hb => Expr.resolves_of_lvlEq a b hab hb) h hfdR
    · exact listRel_forall (P := fun a => a.Resolves env) (Q := fun b => b.Resolves env)
        (fun a b hab hb => Expr.resolves_of_annEq hab hb) h hfdR
  have hl' : p'.fieldDoms.length = p.fieldDoms.length := by
    rcases hfd with h | h
    · exact listRel_length h
    · exact listRel_length h.2.2
  obtain ⟨rest, hpre, -⟩ : ∃ rest, cv.type.stripPis rP = some (pre, rest) ∧ True := by
    unfold iotaFrame at hfr
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hfr
    obtain ⟨⟨pre0, rest⟩, h, _, _, _, _, he⟩ := hfr
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact ⟨rest, h, trivial⟩
  rw [he'B]
  -- the telescope reads as a true proposition
  refine ⟨pt, (eval_tele hloc hag (pre ++ p'.fieldDoms) ρ₀
    (fun d hd => (List.mem_append.mp hd).elim (fun h => hdsR d (List.mem_append_left _ h))
      (hfd'R d)) fun vs ρ' hvl hvf => ?_).2⟩
  have hvf' := fits_rule_transfer m hf hfj hpre hp hfd hfdR
    (by rw [hvl]) hvf
  have hvl' : vs.length = (pre ++ p.fieldDoms).length := by
    rw [hvl, List.length_append, List.length_append, hl']
  obtain ⟨T₀, hT₀⟩ := Denotes_of_resolves (cval := Model.cvalOf m.base2.acval) φ ty
    ρ' htyR
  obtain ⟨L₀, hL₀⟩ := Denotes_of_resolves (cval := Model.cvalOf m.base2.acval) φ
    lhs ρ' hlhsR
  obtain ⟨R₀, hR₀⟩ := Denotes_of_resolves (cval := Model.cvalOf m.base2.acval) φ
    rhs ρ' hrhsR
  obtain ⟨hTu, hLT, hRT, hLR⟩ := H φ ρ₀ vs ρ' hvl' hvf' T₀ L₀ R₀ hT₀ hL₀ hR₀
  have hbody : Expr.eval model φ ρ'
      (.app (.app (.app (.const eqName [u]) ty) lhs) rhs) = eqv L₀ L₀ := by
    show app (app (app (Expr.eval _ φ ρ' (.const eqName [u])) (Expr.eval _ φ ρ' ty))
      (Expr.eval _ φ ρ' lhs)) (Expr.eval _ φ ρ' rhs) = _
    rw [eval_of_Denotes hloc hag hT₀, eval_of_Denotes hloc hag hL₀, eval_of_Denotes hloc hag hR₀]
    exact (heq _ _ _ _ hTu hLT hRT).trans (by rw [← hLR])
  rw [hbody]
  exact ⟨eqv_mem_univZero _ _, pt_mem_eqv_self _⟩

/-- **A quotient eliminator's rule reads**: a stored quotient constant is its pin at its own
names (`basis_pinned`), and so is the stored `Quot.mk`; the pins' rules read
(`quotLift_reads`, `quotInd_reads`). -/
theorem quot_reads {env : Env} (m : Model.EnvModelM V env)
    {cv : ConstantVal} {mI rP : Nat} {isK : Bool} {rules : List RecRule}
    (hf : env.find? cv.name = some (.recInfo cv mI rP isK rules)) {k : QuotKind}
    {cvq : ConstantVal} (hq : ConstantInfo.recInfo cv mI rP isK rules = quotAt k cvq)
    {i : Nat} {rl : RecRule} (hrl : rules[i]? = some rl) :
    ruleReadsB env.find? cv mI rP i rl = true := by
  have hrlm := List.mem_of_getElem? hrl
  -- the stored `Quot.mk` is its pin at one name
  have hmk : rl.ctor = quotMkName → ∃ c, env.find? quotMkName = some (quotMkA.atLps [c]) := by
    intro hcn
    obtain ⟨cvj, cnP, cnF, T, hc⟩ := m.base2.rec_ctors _ cv mI rP isK rules hf rl hrlm
    rw [hcn] at hc
    obtain ⟨⟨hcopy, -, hlen⟩, -⟩ := m.base2.basis_pinned _ _ hc (by decide)
    have hp : pinnedInfo quotMkName = quotMkA := by decide
    rw [hp] at hcopy hlen
    match hl : (ConstantInfo.ctorInfo cvj cnP cnF T).toConstantVal.levelParams, hlen with
    | [c], _ => exact ⟨c, by rw [hc, hcopy, hl]⟩
  -- the stored eliminator is its pin at its own names
  have hpin : ∀ (n : Name) (pin : ConstantInfo), cv.name = n → pinnedInfo n = pin →
      reservedBasisNames.contains n = true →
      cv.levelParams.length = pin.toConstantVal.levelParams.length := by
    intro n pin hn hp hr
    rw [← hn] at hr
    obtain ⟨⟨-, -, hlen⟩, -⟩ := m.base2.basis_pinned _ _ hf hr
    rw [hn, hp] at hlen
    exact hlen
  cases k with
  | type | ctor | sound =>
    simp [quotAt, quotPin, BasisKind.decls, quotBasis, QuotKind.slot, quotA, quotMkA, quotSoundA,
      ConstantInfo.atLps] at hq
  | lift =>
    have hq' : ConstantInfo.recInfo cv mI rP isK rules = quotLiftA.atLps cvq.levelParams := hq
    have hcv : cv.name = quotLiftName ∧ cv.levelParams = cvq.levelParams := by
      simp only [quotLiftA, ConstantInfo.atLps, ConstantInfo.recInfo.injEq,
        ConstantVal.atLps] at hq'
      exact ⟨by rw [hq'.1], by rw [hq'.1]⟩
    have hlen := hpin _ quotLiftA hcv.1 (by decide) (by decide)
    rw [hcv.2] at hlen
    match hl : cvq.levelParams, hlen with
    | [a, b], _ =>
      rw [hl] at hq'
      obtain ⟨c, hcm⟩ := hmk (by
        simp only [quotLiftA, ConstantInfo.atLps, ConstantInfo.recInfo.injEq] at hq'
        rw [hq'.2.2.2.2] at hrl
        match i, hrl with
        | 0, hrl => simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero,
            Option.some.injEq] at hrl; rw [← hrl]; rfl)
      have hr := quotLift_reads a b c hcm
      rw [← hq'] at hr
      match rules, hr, i, hrl with
      | [r], hr, 0, hrl =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hrl
        subst hrl
        exact hr
  | ind =>
    have hq' : ConstantInfo.recInfo cv mI rP isK rules = quotIndA.atLps cvq.levelParams := hq
    have hcv : cv.name = quotIndName ∧ cv.levelParams = cvq.levelParams := by
      simp only [quotIndA, ConstantInfo.atLps, ConstantInfo.recInfo.injEq,
        ConstantVal.atLps] at hq'
      exact ⟨by rw [hq'.1], by rw [hq'.1]⟩
    have hlen := hpin _ quotIndA hcv.1 (by decide) (by decide)
    rw [hcv.2] at hlen
    match hl : cvq.levelParams, hlen with
    | [a], _ =>
      rw [hl] at hq'
      obtain ⟨c, hcm⟩ := hmk (by
        simp only [quotIndA, ConstantInfo.atLps, ConstantInfo.recInfo.injEq] at hq'
        rw [hq'.2.2.2.2] at hrl
        match i, hrl with
        | 0, hrl => simp only [List.map_cons, List.map_nil, List.getElem?_cons_zero,
            Option.some.injEq] at hrl; rw [← hrl]; rfl)
      have hr := quotInd_reads a c hcm
      rw [← hq'] at hr
      match rules, hr, i, hrl with
      | [r], hr, 0, hrl =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hrl
        subst hrl
        exact hr

/-- **The bridge**: a model agreeing with the invariant's on the stored names, and reading `Eq` as
equality, is a model of the input, given that the records are stored. -/
theorem isModel_of_agree {R : ConstantInfo → Prop} {env : Env} (m : Model.EnvModelM V env)
    (hrec : RecordsStored R env) {model : Name → List Nat → V}
    (hag : AgreesOn model (Model.cvalOf m.base2.acval) env) (heq : EqReads model) :
    IsModel V model R := by
  let M := Model.Model.ofEnvModelM m
  have hloc := cvalLocal_ofEnvModelM m
  rw [← Model.Model.ofEnvModelM_cval m] at hloc hag
  intro c hc vals hl
  obtain ⟨ci, hf, ⟨hcv, hdef, hrc, -⟩, hreads⟩ := hrec c hc
  have hmem : ci ∈ env.consts := Env.find?_mem hf
  have hname : c.name = ci.name := (find?_name hf).symm
  have hval : model c.name vals =
      M.cval c.name (Level.assign c.toConstantVal.levelParams vals) := by
    rw [hag c.name ci hf]
    unfold posModel; rw [hf]; dsimp only; rw [hcv]
  refine ⟨?_, ?_⟩
  · obtain ⟨T, hT, hmT⟩ := M.mem ci hmem (Level.assign c.toConstantVal.levelParams vals) ρ₀
    rw [hcv] at hT
    rw [hval, eval_of_Denotes hloc hag hT, hname]
    exact hmT
  · cases c with
    | defnInfo cv value hint =>
      obtain rfl := hdef cv value hint rfl
      have hD := M.defn_eq cv value hint hmem (Level.assign cv.levelParams vals) ρ₀
      show model cv.name vals =
        Expr.eval model (Level.assign cv.levelParams vals) ρ₀ value
      rw [eval_of_Denotes hloc hag hD]
      exact hval
    | recInfo cv mI rP isK rules =>
      obtain ⟨isK', rules', rfl, hrules⟩ := hrc cv mI rP isK rules rfl
      intro i rl hrl e' he'
      rw [Model.Model.ofEnvModelM_cval m] at hloc hag
      generalize Level.assign _ vals = φ
      -- the stored rule at the same position: the same up to its firing mode
      have hi := congrArg (·[i]?) hrules
      simp only [List.getElem?_map, hrl, Option.map_some] at hi
      obtain ⟨rl', hrl', hu⟩ : ∃ rl', rules'[i]? = some rl' ∧ rl'.unfired = rl.unfired := by
        cases h : rules'[i]? with
        | none => rw [h] at hi; exact nomatch hi
        | some rl' => rw [h] at hi; exact ⟨rl', rfl, Option.some.inj hi⟩
      have he'' : iotaEqOf cv mI rP i rl' = some e' := by
        rw [← iotaEqOf_unfired, show { rl' with fire := .plain } = rl'.unfired from rfl, hu]
        exact he'
      rcases hreads cv mI rP isK rules rfl with hR | ⟨k, cvq, hq⟩
      · exact iotaEqOf_holds m hag heq hf hrl' (hR cv mI rP isK' rules' rfl i rl' hrl') he'' φ
      · exact iotaEqOf_holds m hag heq hf hrl' (quot_reads m hf hq hrl') he'' φ
    | _ => trivial

/-- **The bridge**, at the invariant's own model. -/
theorem isModel_of_envModelM {R : ConstantInfo → Prop} {env : Env} (m : Model.EnvModelM V env)
    (hrec : RecordsStored R env) :
    IsModel V (posModel (Model.cvalOf m.base2.acval) env) R :=
  isModel_of_agree m hrec (agreesOn_posModel _ _) (eqReads_envModelM m)

end ConLeche
