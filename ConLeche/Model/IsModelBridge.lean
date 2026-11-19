module

import ConLeche.Denotes
public import ConLeche.Model.RuleEqsSound
import ConLeche.Model.OfEnvModelM
public import ConLeche.Verify.IsModelRecords
public import ConLeche.Verify.Resolves
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
* `isModel_of_envModelM`: the clauses, from the invariant, given what the checker establishes
  about the records (`RecordsStored`, `ConLeche/Verify/IsModelRecords.lean`).  A recursor rule
  holds because at every fit of its equation's telescope the two sides are one member of a type
  (`Model.ruleEq_sides`), and `Eq` — stored or not — reads as equality there.
-/

namespace ConLeche

open SetTheory ConLeche.SetModel

universe w

variable {V : Type w} [SetTheory V]

/-- **Equality at the universe `k`**: `@Eq.{k} A a b` is the truth value of `a = b`. -/
noncomputable def eqRel (k : Nat) : V :=
  lamV (univ k) fun A => lamV A fun a => lamV A fun b => eqv a b

/-- The internal valuation, positional: a stored constant's level values go to its level
parameters in order.  An undeclared `Eq` is equality (`eqRel`); any other undeclared name is
`∅`. -/
noncomputable def posModel (cval : Name → (LevelParam → Nat) → V) (env : Env) :
    Name → List Nat → V := fun n vals =>
  match env.find? n with
  | some ci => cval n (Level.assign ci.toConstantVal.levelParams vals)
  | none => if n = eqName then eqRel (vals.headD 0) else empty

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
    {φ : LevelParam → Nat} {B : Expr} :
    ∀ (ds : List Expr) (ρ : BVarIdx → V), (∀ d ∈ ds, d.Resolves env) →
      (∀ (vs : List V) (ρ' : BVarIdx → V), vs.length = ds.length →
        Model.Fits cval env φ ρ (ds.foldr .forallE B) vs ρ' B →
        Expr.eval (posModel cval env) φ ρ' B ∈ˢ (univZero : V) ∧
          (pt : V) ∈ˢ Expr.eval (posModel cval env) φ ρ' B) →
      Expr.eval (posModel cval env) φ ρ (ds.foldr .forallE B) ∈ˢ (univZero : V) ∧
        (pt : V) ∈ˢ Expr.eval (posModel cval env) φ ρ (ds.foldr .forallE B)
  | [], ρ, _, h => h [] ρ rfl .nil
  | d :: ds, ρ, hr, h => by
    obtain ⟨A, hA⟩ := Denotes_of_resolves (cval := cval) φ d ρ (hr d List.mem_cons_self)
    have hz : ∀ x, x ∈ˢ A →
        Expr.eval (posModel cval env) φ (push x ρ) (ds.foldr .forallE B) ∈ˢ (univZero : V) ∧
          (pt : V) ∈ˢ Expr.eval (posModel cval env) φ (push x ρ) (ds.foldr .forallE B) :=
      fun x hx => eval_tele hloc ds (push x ρ) (fun d' h' => hr d' (List.mem_cons_of_mem _ h'))
        fun vs ρ' hl hf => h (x :: vs) ρ' (by simp [hl]) (.cons hA hx hf)
    show piV (Expr.eval _ φ ρ d) _ ∈ˢ (univZero : V) ∧ (pt : V) ∈ˢ piV (Expr.eval _ φ ρ d) _
    rw [eval_of_Denotes hloc hA]
    refine ⟨?_, ?_⟩
    · rw [piV_eq_zero fun x hx => (hz x hx).1]; exact piR_zero_mem_univZero
    · exact (pt_mem_piV_iff fun x hx => Or.inl (hz x hx).1).mpr fun x hx => (hz x hx).2

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
      eval_of_Denotes (cvalLocal_ofEnvModelM m) hD
    rw [hE]
    exact Model.eq_equality_of m u φ ρ _ T L R hD hT hL hR

/-- **The bridge**: the invariant's model is a model of the input, given that the records are
stored. -/
theorem isModel_of_envModelM {R : Records} {env : Env} (m : Model.EnvModelM V env)
    (hrec : RecordsStored R env) :
    IsModel V (posModel (Model.cvalOf m.base2.acval) env) R := by
  let M := Model.Model.ofEnvModelM m
  have hloc := cvalLocal_ofEnvModelM m
  rw [← Model.Model.ofEnvModelM_cval m] at hloc ⊢
  intro c hc vals hl
  obtain ⟨ci, hf, hcv, hdef, hrc, -⟩ := hrec c hc
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
      intro rl hrl cvj cnP nF T hcj hcn e he
      rw [Model.Model.ofEnvModelM_cval m] at hloc ⊢
      generalize Level.assign _ vals = φ
      obtain ⟨cj, hfj, -, -, -, hcjc⟩ := hrec _ hcj
      obtain ⟨nF', T', rfl⟩ := hcjc cvj cnP nF T rfl
      have hnj : (ConstantInfo.ctorInfo cvj cnP nF T).name = cvj.name := rfl
      rw [hnj, hcn] at hfj
      -- the equation is stored
      have hin : e ∈ ruleEqs env := by
        unfold ruleEqs
        refine List.mem_flatMap.mpr ⟨_, hmem, ?_⟩
        rw [show env.find? (ConstantInfo.recInfo cv mI rP isK' rules).name =
          some (.recInfo cv mI rP isK' rules) from hf]
        refine List.mem_filterMap.mpr ⟨rl, hrl, ?_⟩
        unfold iotaEq
        rw [hfj]
        exact he
      -- its sides at every fit, by the invariant
      obtain ⟨ds', u, ty, lhs, rhs, he', H⟩ := Model.ruleEq_sides m
        (fun φ n cv mI rP isK rules hf rl hrl =>
          (m.rec_rules φ n cv mI rP isK rules hf rl hrl).2.2.2) hin
      -- its parts resolve
      have htype : ∀ ci ∈ env.consts, ci.toConstantVal.type.Resolves env := fun ci hci => by
        obtain ⟨ta, hta⟩ := m.type_reads ci hci (fun _ => 0)
        obtain ⟨hnf, -, -, hlb, -⟩ := m.base2.wf.consts ci hci
        exact resolves_of_denote_closed hta hnf hlb
      obtain ⟨-, -, -, -, -, hrec'⟩ := m.base2.wf.consts _ hmem
      obtain ⟨hnf, -, -, hlb, hnest⟩ := hrec' cv mI rP isK' rules rfl rl hrl
      have hcvR : cv.type.Resolves env := htype _ hmem
      have hlaw := m.rec_rules (fun _ => 0) _ cv mI rP isK' rules hf rl hrl
      have hrhs : rl.rhs.Resolves env := by
        obtain ⟨Ra, hRa, -⟩ := hlaw.2.1 (cv.levelParams.map .param) (by simp)
        refine (Expr.resolves_instantiateLevelParams _ _ _).mp
          (resolves_of_denote_closed hRa ?_ ?_)
        · rw [Expr.hasFvar_instantiateLevelParams]; exact hnf
        · rw [Expr.looseBVarsBounded_instantiateLevelParams]; exact hlb
      have hpins : ∀ lvls pins, rl.fire = .nested lvls pins → ∀ p ∈ pins, p.Resolves env := by
        intro lvls pins hfire p hp
        obtain ⟨-, -, -, pre, dom, body, D, hstrip, -, hargs, -⟩ := hnest lvls pins hfire
        obtain ⟨-, hfa⟩ := Expr.resolves_stripPis _ _ hstrip hcvR
        obtain ⟨-, hda⟩ := Expr.resolves_getApp dom hfa.1
        refine (Expr.resolves_liftLooseBVars (mI - rP) p 0).mp (hda _ ?_)
        rw [hargs]
        exact List.mem_append_left _ (List.mem_map_of_mem hp)
      have hcount := hlaw.2.2.2.1 cvj cnP nF' T' hfj
      obtain ⟨ds'', u', ty', lhs', rhs', he'', hdsR, htyR, hlhsR, hrhsR⟩ :=
        iotaEqAt_parts hcvR (htype _ (Env.find?_mem hfj)) hrhs hpins
          ⟨_, hf, rfl⟩ ⟨_, hfj, by rw [ctorLevels_length]; exact hcount⟩ he
      rw [he'] at he''
      obtain ⟨rfl, h1, rfl⟩ := foldr_forallE_app_inj he''
      injection h1 with h2 h3
      subst h3
      injection h2 with h4 h5
      subst h5
      injection h4 with h6 h7
      injection h7 with h8
      subst h8 he'
      -- the telescope reads as a true proposition
      refine ⟨pt, (eval_tele hloc ds' ρ₀ hdsR fun vs ρ' hvl hvf => ?_).2⟩
      obtain ⟨T₀, hT₀⟩ := Denotes_of_resolves (cval := Model.cvalOf m.base2.acval) φ ty
        ρ' htyR
      obtain ⟨L₀, hL₀⟩ := Denotes_of_resolves (cval := Model.cvalOf m.base2.acval) φ
        lhs ρ' hlhsR
      obtain ⟨R₀, hR₀⟩ := Denotes_of_resolves (cval := Model.cvalOf m.base2.acval) φ
        rhs ρ' hrhsR
      obtain ⟨hTu, hLT, hRT, hLR⟩ := H φ ρ₀ vs ρ' hvl hvf T₀ L₀ R₀ hT₀ hL₀ hR₀
      have hbody : Expr.eval (posModel (Model.cvalOf m.base2.acval) env) φ ρ'
          (.app (.app (.app (.const eqName [u]) ty) lhs) rhs) = eqv L₀ L₀ := by
        show app (app (app (Expr.eval _ φ ρ' (.const eqName [u])) (Expr.eval _ φ ρ' ty))
          (Expr.eval _ φ ρ' lhs)) (Expr.eval _ φ ρ' rhs) = _
        rw [eval_of_Denotes hloc hT₀, eval_of_Denotes hloc hL₀, eval_of_Denotes hloc hR₀,
          eval_eq m hTu hLT hRT, ← hLR]
      rw [hbody]
      exact ⟨eqv_mem_univZero _ _, pt_mem_eqv_self _⟩
    | _ => trivial

end ConLeche
