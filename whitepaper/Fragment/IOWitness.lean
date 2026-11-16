module

public import Fragment.IOGrade
public import Fragment.Probe
import Fragment.Hygiene

public section

/-!
# Where the io grade cannot go (task #346)

`IOGrade.lean` proves the hereditary claim of the io grade and two
consumers.  This file shows the consumers it cannot serve, and why no
claim about io-inferred types can serve them in this model.

* **λ-congruence with io-inferred bodies' types is unsound**
  (`lam_congr_io_unsound`).  The environment `ioEnv` stores
  `g := fun (x : Prop) (h : E x) => n : (x : Prop) → E x → Prop`, a
  *typed* definition, beside the opaque `E : Prop → Type` (`True ↦
  Prop`, `False ↦ ∅`) and `n : Prop` (`True`).  Under `x : Prop`, the
  body `g x n` (its argument `n` is no member of `E x`) io-infers
  `Prop`, as `n` does; `g x n` reduces to `n` by δ, β, β; so every
  premise of λ-congruence holds, with the bodies' types io-inferred.
  Yet `fun x => g x n` is the point at `False` (an abstraction over
  `E False = ∅` applied) and `True` at `True`, while `fun x => n` is
  `True` everywhere: two well-denoted λs, neither the point, different.
  The rule's conclusion is false, so **no claim** about `InferIO` makes
  the rule sound: the premises are derivations, not claims.  The body
  is headed by a constant, so a guard "the bodies are in weak-head
  normal form" does not help either.
* **η with the λ's body type io-inferred is unsound**
  (`eta_body_io_unsound`): the same body against `k := fun _ => n`.
* **η with the other side's type io-inferred is unsound when that side
  is a λ** (`eta_lam_io_unsound`); for a side with a variable or
  constant head it is sound (`IOGrade.lean`, `etaIO_sound`).
* **The claim must read the type's syntax** (`io_type_value_collision`):
  `fun (x : Prop) => (fun (h : E x) => h) n` io-infers
  `(x : Prop) → E x`, whose value is a truth value (it is empty: the
  fibre at `False` is), and the term is not the point.  A claim read off
  the type's value alone would have to allow a non-point inhabitant of
  a truth value, and could then not give proof irrelevance; the
  hereditary claim reads the `∀` and its body's sort instead.

What the model lacks is a typing of the body `g x n`: the invariant
`WellDenoted` asks of an application only that its argument lie in the
domain of *some* function space holding the head, and where the head is the
point (here, at `x = False`) that is no constraint.  Every typed term
of Lean's has a correct io-inferred type (subject reduction and
uniqueness of types); the semantic proof does not have that, and
strengthening the invariant to "the argument lies in the domain of the
head's io-inferred type" is not closed under β (informally, with
`c : True → Nat`: `(fun (y : Nat → True) => c (y 5)) a` with
`a : Bool → True` meets it — `a` denotes the point, a member of
`Nat → True` — and is not the point, and its reduct `c (a 5)` does
not meet it, `5` being no `Bool`).
-/

namespace Fragment

open SetLib Expr Classical

universe w

variable {V : Type w} [SetLib V]

/-! ## The environment and its model -/

/-- `g : (x : Prop) → E x → Prop`. -/
@[expose] def gName : Name := "g"

/-- `k : Prop → Prop`. -/
@[expose] def kName : Name := "k"

/-- `E x`, under one binder. -/
@[expose] def ex : Expr := .app (.const eName []) (.bvar 0)

/-- `(x : Prop) → E x → Prop`. -/
@[expose] def gType : Expr := .pi (.sort .zero) (.pi ex (.sort .zero))

/-- `fun (x : Prop) (h : E x) => n`. -/
@[expose] def gValE : Expr := .lam (.sort .zero) (.lam ex (.const nName []))

/-- `g x n`, under `x : Prop`. -/
@[expose] def gxn : Expr := .app (.app (.const gName []) (.bvar 0)) (.const nName [])

/-- `fun (x : Prop) => g x n`. -/
@[expose] def lamG : Expr := .lam (.sort .zero) gxn

/-- The environment: `E`, `n` opaque, `g` and `k := fun _ => n`
defined.  Both definitions are typed. -/
@[expose] def ioEnv : Env :=
  ⟨[(gName, ⟨[], gType, .defn gValE⟩),
    (kName, ⟨[], .pi (.sort .zero) (.sort .zero), .defn lamConst⟩),
    (nName, ⟨[], .sort .zero, .ctor "X" 0 0⟩),
    (eName, ⟨[], propToType, .ctor "X" 0 0⟩)]⟩

/-- `E x`'s value. -/
noncomputable def exVal (x : V) : V := if x = one then typeU 0 else truthVal False

/-- `g x`'s value: `fun (h : E x) => True`. -/
noncomputable def gVal (x : V) : V := lamV (SetLib.app (mixedM eName []) x) fun _ => one

/-- The model: `mixedM` with `g` and `k` added. -/
noncomputable def ioM : Name → List Nat → V := fun c ls =>
  if c = gName then lamV (typeU 0) gVal
  else if c = kName then lamV (typeU 0) (fun _ => one)
  else mixedM c ls

theorem ioM_g (ls : List Nat) : (ioM gName ls : V) = lamV (typeU 0) gVal := by
  simp [ioM]

theorem ioM_k (ls : List Nat) : (ioM kName ls : V) = lamV (typeU 0) (fun _ => one) := by
  simp [ioM, gName, kName]

theorem ioM_E (ls : List Nat) : (ioM eName ls : V) = mixedM eName ls := by
  simp [ioM, gName, kName, eName]

theorem ioM_n (ls : List Nat) : (ioM nName ls : V) = one := by
  have h := mixedM_n (V := V) ls
  simp only [ioM, gName, kName, nName] at h ⊢
  simpa using h

theorem ioM_agree {e : Expr} (h : ∀ c ∈ e.consts, c = eName ∨ c = nName) :
    ∀ c ∈ e.consts, ∀ ls, (ioM c ls : V) = mixedM c ls := by
  intro c hc ls
  rcases h c hc with rfl | rfl
  · exact ioM_E ls
  · rw [ioM_n, mixedM_n]

theorem consts_ex : ∀ c ∈ ex.consts, c = eName ∨ c = nName := by
  intro c hc; simp [ex, Expr.consts] at hc; exact Or.inl hc

theorem app_E_val {x : V} (hx : x ∈ˢ typeU 0) :
    SetLib.app (mixedM eName [] : V) x = exVal x := by
  rw [mixedM_E, app_graph hx]; rfl

theorem gVal_mem (x : V) : gVal x ∈ˢ piV (SetLib.app (mixedM eName [] : V) x) (fun _ => typeU 0) :=
  lamV_mem (fun _ _ => one_mem_typeU_zero) fun _ _ => IsTy_typeU 0

theorem g_mem : lamV (typeU 0 : V) gVal ∈ˢ
    piV (typeU 0) (fun x => piV (SetLib.app (mixedM eName [] : V) x) (fun _ => typeU 0)) :=
  lamV_mem (fun x _ => gVal_mem x) fun _ _ => IsTy_piV

theorem lamV_g_val {x : V} (hx : x ∈ˢ typeU 0) :
    SetLib.app (gVal x) (one : V) = dVal x := by
  unfold gVal dVal
  rw [app_E_val hx]
  unfold exVal
  split
  · exact app_lamV one_mem_typeU_zero
  · rw [lamV_of_empty fun z hz => of_mem_truthVal hz, app_pt]

section
variable (φ : Name → Nat)

theorem interp_ex_io {ρ : Nat → V} {x : V} (hx : x ∈ˢ typeU 0) :
    interp ioM φ (cons x ρ) ex = exVal x := by
  rw [interp_consts (ioM_agree consts_ex)]
  exact interp_Ex φ ρ hx

theorem WellDenoted_ex_io {ρ : Nat → V} {x : V} (hx : x ∈ˢ typeU 0) :
    WellDenoted ioM φ (cons x ρ) ex :=
  (WellDenoted_consts (ioM_agree consts_ex)).mpr (WellDenoted_Ex φ ρ hx)

theorem IsTy_ex_io {ρ : Nat → V} {x : V} (hx : x ∈ˢ typeU 0) :
    IsTy (interp ioM φ (cons x ρ) ex) := by
  rw [interp_consts (ioM_agree consts_ex)]
  exact IsTy_interp_Ex φ ρ hx

theorem interp_gx {ρ : Nat → V} {x : V} (hx : x ∈ˢ typeU 0) :
    interp ioM φ (cons x ρ) (.app (.const gName []) (.bvar 0)) = gVal x := by
  rw [interp_app, interp_const, interp_bvar, cons_zero, List.map_nil, ioM_g, app_lamV hx]

theorem interp_gxn {ρ : Nat → V} {x : V} (hx : x ∈ˢ typeU 0) :
    interp ioM φ (cons x ρ) gxn = dVal x := by
  rw [gxn, interp_app, interp_gx φ hx, interp_const, List.map_nil, ioM_n, lamV_g_val hx]

theorem WellDenoted_gxn {ρ : Nat → V} {x : V} (hx : x ∈ˢ typeU 0) :
    WellDenoted ioM φ (cons x ρ) gxn := by
  have hgx : WellDenoted ioM φ (cons x ρ) (.app (.const gName []) (.bvar 0)) := by
    rw [WellDenoted_app]
    refine ⟨trivial, trivial, appliesTo_of_mem_piV (A := typeU 0)
      (B := fun y => piV (SetLib.app (mixedM eName [] : V) y) (fun _ => typeU 0)) ?_
      (IsTy_typeU 0) hx⟩
    rw [interp_const, List.map_nil, ioM_g]; exact g_mem
  rw [gxn, WellDenoted_app]
  refine ⟨hgx, trivial, appliesTo_of_mem_piV (A := typeU 0)
    (B := fun _ => if x = one then typeU 0 else one) ?_ (IsTy_typeU 0)
    (by rw [interp_const, List.map_nil, ioM_n]; exact one_mem_typeU_zero)⟩
  show _ ∈ˢ piV _ _
  rw [interp_gx φ hx]
  unfold gVal
  rw [app_E_val hx]
  unfold exVal
  by_cases h1 : x = one
  · simp only [h1, ite_true]
    exact lamV_mem (fun _ _ => one_mem_typeU_zero) fun _ _ => IsTy_typeU 0
  · simp only [h1, ite_false]
    rw [lamV_of_empty fun z hz => of_mem_truthVal hz,
      ← lamV_eq_pt (A := (typeU 0 : V)) (F := fun _ => pt) fun _ _ => rfl]
    exact lamV_mem (fun _ _ => mem_one.mpr rfl) fun _ _ => IsTy_one

theorem WellDenoted_lamG (ρ : Nat → V) : WellDenoted ioM φ ρ lamG := by
  rw [lamG, WellDenoted_lam]
  refine ⟨trivial, IsTy_typeU 0, fun x hx => WellDenoted_gxn φ hx, fVal, fun x hx => ?_,
    fun x _ => IsTy_fVal x⟩
  rw [interp_gxn φ hx]; exact dVal_mem x

theorem interp_lamG (ρ : Nat → V) : interp ioM φ ρ lamG = lamV (typeU 0) dVal := by
  rw [lamG, interp_lam, interp_sort, Level.eval_zero]
  exact lamV_congr fun x hx => interp_gxn φ hx

theorem WellDenoted_lamConst_io (ρ : Nat → V) : WellDenoted ioM φ ρ lamConst := by
  rw [lamConst, WellDenoted_lam]
  refine ⟨trivial, IsTy_typeU 0, fun _ _ => trivial, fun _ => typeU 0, fun x _ => ?_,
    fun _ _ => IsTy_typeU 0⟩
  rw [interp_const, List.map_nil, ioM_n]; exact one_mem_typeU_zero

theorem interp_lamConst_io (ρ : Nat → V) :
    interp ioM φ ρ lamConst = lamV (typeU 0) (fun _ => one) := by
  rw [lamConst, interp_lam, interp_sort, Level.eval_zero]
  exact lamV_congr fun x _ => by rw [interp_const, List.map_nil, ioM_n]

theorem WellDenoted_gType (ρ : Nat → V) : WellDenoted ioM φ ρ gType := by
  rw [gType, WellDenoted_pi]
  refine ⟨trivial, IsTy_typeU 0, fun x hx => ?_, fun x _ => IsTy_piV⟩
  rw [WellDenoted_pi]
  exact ⟨WellDenoted_ex_io φ hx, IsTy_ex_io φ hx, fun _ _ => trivial, fun _ _ => IsTy_typeU 0⟩

theorem interp_gType (ρ : Nat → V) :
    interp ioM φ ρ gType =
      piV (typeU 0) (fun x => piV (SetLib.app (mixedM eName [] : V) x) (fun _ => typeU 0)) := by
  simp [gType, ex, ioM_E]

theorem WellDenoted_gValE (ρ : Nat → V) : WellDenoted ioM φ ρ gValE := by
  rw [gValE, WellDenoted_lam]
  refine ⟨trivial, IsTy_typeU 0, fun x hx => ?_,
    fun x => piV (interp ioM φ (cons x ρ) ex) (fun _ => typeU 0), fun x _ => ?_,
    fun _ _ => IsTy_piV⟩
  · rw [WellDenoted_lam]
    refine ⟨WellDenoted_ex_io φ hx, IsTy_ex_io φ hx, fun _ _ => trivial, fun _ => typeU 0,
      fun _ _ => ?_, fun _ _ => IsTy_typeU 0⟩
    rw [interp_const, List.map_nil, ioM_n]; exact one_mem_typeU_zero
  · rw [interp_lam]
    refine lamV_mem (fun _ _ => ?_) fun _ _ => IsTy_typeU 0
    rw [interp_const, List.map_nil, ioM_n]; exact one_mem_typeU_zero

theorem interp_gValE (ρ : Nat → V) : interp ioM φ ρ gValE = lamV (typeU 0) gVal := by
  simp [gValE, ex, ioM_E, ioM_n]; rfl

end

/-- **The environment has a model** (`ioM`). -/
noncomputable def ioModel : EnvModel V ioEnv where
  M := ioM
  type_ok := by
    intro c ci h φ ρ ls hls
    simp only [ioEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      rw [instL_nil_nil, interp_gType]
      refine ⟨WellDenoted_gType _ ρ, IsTy_piV, ?_⟩
      rw [List.map_nil, ioM_g]; exact g_mem
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      rw [instL_nil_nil]
      refine ⟨by rw [WellDenoted_pi]; exact ⟨trivial, IsTy_typeU 0, fun _ _ => trivial,
        fun _ _ => IsTy_typeU 0⟩, IsTy_piV, ?_⟩
      rw [List.map_nil, ioM_k, interp_pi, interp_sort, Level.eval_zero]
      exact lamV_mem (fun _ _ => one_mem_typeU_zero) fun _ _ => IsTy_typeU 0
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      rw [instL_nil_nil, interp_sort, Level.eval_zero]
      exact ⟨trivial, IsTy_typeU 0, by rw [ioM_n]; exact one_mem_typeU_zero⟩
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      rw [instL_nil_nil]
      refine ⟨by rw [propToType, WellDenoted_pi]; exact ⟨trivial, IsTy_typeU 0,
        fun _ _ => trivial, fun _ _ => IsTy_typeU 1⟩, IsTy_piV, ?_⟩
      rw [List.map_nil, ioM_E, propToType, interp_pi, interp_sort, Level.eval_zero]
      exact E_mem _
    · cases h
  unfold := by
    intro c ci v h hv φ ρ ls hls
    simp only [ioEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      cases hv
      rw [instL_nil_nil, List.map_nil, ioM_g]
      exact ⟨WellDenoted_gValE φ ρ, interp_gValE φ ρ⟩
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      cases hv
      rw [instL_nil_nil, List.map_nil, ioM_k]
      exact ⟨WellDenoted_lamConst_io φ ρ, interp_lamConst_io φ ρ⟩
    split at h
    · cases h; cases hv
    split at h
    · cases h; cases hv
    · cases h
  rec_rules := by
    intro c ci _ _ _ _ _ h hk
    simp only [ioEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    · cases h
  rec_rules_nested := by
    intro c ci _ _ _ _ _ h hk
    simp only [ioEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    · cases h
  ind_fib := by
    intro c ci _ _ _ _ h hk
    simp only [ioEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    · cases h
  rec_rules_k := by
    intro c ci _ _ _ _ _ h hk
    simp only [ioEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    · cases h
  rec_rules_slot := by
    intro c ci _ _ _ _ _ h hk
    simp only [ioEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    · cases h

/-! ## The derivations -/

theorem ioEnv_g : ioEnv.find? gName = some ⟨[], gType, .defn gValE⟩ := by
  simp [ioEnv, Env.find?]

theorem ioEnv_k : ioEnv.find? kName = some ⟨[], .pi (.sort .zero) (.sort .zero), .defn lamConst⟩ := by
  simp [ioEnv, Env.find?, List.lookup, gName, kName]

theorem ioEnv_n : ioEnv.find? nName = some ⟨[], .sort .zero, .ctor "X" 0 0⟩ := by
  simp [ioEnv, Env.find?, List.lookup, gName, kName, nName]

section
variable [LevelOracle]

/-- `g x n : Prop`, io-inferred: no argument is checked. -/
theorem inferIO_gxn : InferIO ioEnv [.sort .zero] gxn (.sort .zero) := by
  have h1 : InferIO ioEnv [.sort .zero] (.const gName []) gType := by
    have := InferIO.const (env := ioEnv) (Γ := [.sort .zero]) (ls := []) ioEnv_g rfl
    rwa [instL_nil_nil] at this
  have h2 : InferIO ioEnv [.sort .zero] (.app (.const gName []) (.bvar 0)) (.pi ex (.sort .zero)) :=
    InferIO.app (a := .bvar 0) (A := .sort .zero) (B := .pi ex (.sort .zero)) h1 .refl
  exact InferIO.app (a := .const nName []) (A := ex) (B := .sort .zero) h2 .refl

theorem inferIO_n (Γ : List Expr) : InferIO ioEnv Γ (.const nName []) (.sort .zero) := by
  have := InferIO.const (env := ioEnv) (Γ := Γ) (ls := []) ioEnv_n rfl
  rwa [instL_nil_nil] at this

theorem infer_n (Γ : List Expr) : Infer ioEnv Γ (.const nName []) (.sort .zero) := by
  have := Infer.const (env := ioEnv) (Γ := Γ) (ls := []) ioEnv_n rfl
  rwa [instL_nil_nil] at this

/-- `g x n` reduces to `n`: δ, β, β. -/
theorem red_gxn : Red ioEnv [.sort .zero] gxn (.const nName []) := by
  have hδ : Red ioEnv [.sort .zero] gxn (.app (.app gValE (.bvar 0)) (.const nName [])) := by
    have := Red.appFn (a := .const nName []) (Red.appFn (a := .bvar 0)
      (Red.delta (env := ioEnv) (Γ := [.sort .zero]) (ls := []) ioEnv_g rfl rfl))
    rwa [instL_nil_nil] at this
  have hβ₁ : Red ioEnv [.sort .zero] (.app (.app gValE (.bvar 0)) (.const nName []))
      (.app (.lam ex (.const nName [])) (.const nName [])) :=
    Red.appFn Red.beta
  exact .trans hδ (.trans hβ₁ Red.beta)

/-- `k x` reduces to `n`: δ, β. -/
theorem red_kx : Red ioEnv [.sort .zero] (.app (.const kName []) (.bvar 0)) (.const nName []) := by
  have hδ : Red ioEnv [.sort .zero] (.app (.const kName []) (.bvar 0)) (.app lamConst (.bvar 0)) := by
    have := Red.appFn (a := .bvar 0)
      (Red.delta (env := ioEnv) (Γ := [.sort .zero]) (ls := []) ioEnv_k rfl rfl)
    rwa [instL_nil_nil] at this
  exact .trans hδ Red.beta

end

/-! ## The values -/

theorem lamV_dVal_ne_pt : lamV (typeU 0 : V) dVal ≠ pt := by
  refine lamV_ne_pt_of one_mem_typeU_zero ?_
  simp only [dVal]; exact one_ne_pt

theorem lamV_one_ne_pt : lamV (typeU 0 : V) (fun _ => one) ≠ pt :=
  lamV_ne_pt_of one_mem_typeU_zero one_ne_pt

theorem lamV_dVal_ne_one : lamV (typeU 0 : V) dVal ≠ lamV (typeU 0) (fun _ => one) := by
  intro heq
  have happ := congrArg (fun f => SetLib.app f (truthVal False)) heq
  simp only [app_lamV false_mem_typeU_zero, dVal,
    ite_eq_right one_ne_truthVal_false.symm] at happ
  exact one_ne_pt happ.symm

/-! ## The witnesses -/

/-- **Lambda congruence with io-inferred bodies' types is unsound.**  In a
model of `ioEnv` (both definitions typed): the domains by `refl`, the
bodies `g x n` and `n` by δ, β, β and `refl`, both bodies io-infer
`Prop`, `Prop ≡ Prop` by `refl` — every premise of `DefEq.lam` with
`InferIO` in place of `Infer`; the lambdas are well-denoted, not the point,
and different. -/
theorem lam_congr_io_unsound [LevelOracle] (φ : Name → Nat) :
    DefEq ioEnv [] (.sort .zero) (.sort .zero) ∧
    DefEq ioEnv [.sort .zero] gxn (.const nName []) ∧
    InferIO ioEnv [.sort .zero] gxn (.sort .zero) ∧
    InferIO ioEnv [.sort .zero] (.const nName []) (.sort .zero) ∧
    DefEq ioEnv [.sort .zero] (.sort .zero) (.sort .zero) ∧
    ¬ DefEqSem (ioModel (V := V)) φ [] lamG lamConst := by
  refine ⟨.refl, .redL red_gxn .refl, inferIO_gxn, inferIO_n _, .refl, fun h => ?_⟩
  have heq := h (fun _ => pt) trivial (WellDenoted_lamG φ _) (WellDenoted_lamConst_io φ _)
    (by rw [ioModel, interp_lamG]; exact lamV_dVal_ne_pt)
    (by rw [ioModel, interp_lamConst_io]; exact lamV_one_ne_pt)
  simp only [ioModel] at heq
  rw [interp_lamG, interp_lamConst_io] at heq
  exact lamV_dVal_ne_one heq

/-- **η with the λ's body type io-inferred is unsound**: `fun x => g x n`
against `k`, whose type is `Prop → Prop` (inferred at the full grade,
`k` a constant); the λ's body io-infers `Prop`, the `∀`'s body. -/
theorem eta_body_io_unsound [LevelOracle] (φ : Name → Nat) :
    Infer ioEnv [] (.const kName []) (.pi (.sort .zero) (.sort .zero)) ∧
    DefEq ioEnv [] (.sort .zero) (.sort .zero) ∧
    DefEq ioEnv [.sort .zero] gxn (.app ((Expr.const kName []).liftN 1) (.bvar 0)) ∧
    InferIO ioEnv [.sort .zero] gxn (.sort .zero) ∧
    DefEq ioEnv [.sort .zero] (.sort .zero) (.sort .zero) ∧
    ¬ DefEqSem (ioModel (V := V)) φ [] lamG (.const kName []) := by
  refine ⟨?_, .refl, .redL red_gxn (.symm (.redL red_kx .refl)), inferIO_gxn, .refl,
    fun h => ?_⟩
  · have := Infer.const (env := ioEnv) (Γ := []) (ls := []) ioEnv_k rfl
    rwa [instL_nil_nil] at this
  have heq := h (fun _ => pt) trivial (WellDenoted_lamG φ _) trivial
    (by rw [ioModel, interp_lamG]; exact lamV_dVal_ne_pt)
    (by simp only [ioModel, interp_const, List.map_nil, ioM_k]; exact lamV_one_ne_pt)
  simp only [ioModel, interp_const, List.map_nil, ioM_k] at heq
  rw [interp_lamG] at heq
  exact lamV_dVal_ne_one heq

/-- **η with the other side's type io-inferred is unsound when that
side is a λ**: `fun x => n` against `fun x => g x n`, whose type
io-infers `Prop → Prop`. -/
theorem eta_lam_io_unsound [LevelOracle] (φ : Name → Nat) :
    InferIO ioEnv [] lamG (.pi (.sort .zero) (.sort .zero)) ∧
    DefEq ioEnv [] (.sort .zero) (.sort .zero) ∧
    DefEq ioEnv [.sort .zero] (.const nName []) (.app (lamG.liftN 1) (.bvar 0)) ∧
    Infer ioEnv [.sort .zero] (.const nName []) (.sort .zero) ∧
    DefEq ioEnv [.sort .zero] (.sort .zero) (.sort .zero) ∧
    ¬ DefEqSem (ioModel (V := V)) φ [] lamConst lamG := by
  refine ⟨.lam inferIO_gxn, .refl, ?_, infer_n _, .refl, fun h => ?_⟩
  · show DefEq ioEnv [.sort .zero] (.const nName []) (.app (.lam (.sort .zero) gxn) (.bvar 0))
    exact .symm (.redL (.trans Red.beta red_gxn) .refl)
  have heq := h (fun _ => pt) trivial (WellDenoted_lamConst_io φ _) (WellDenoted_lamG φ _)
    (by rw [ioModel, interp_lamConst_io]; exact lamV_one_ne_pt)
    (by rw [ioModel, interp_lamG]; exact lamV_dVal_ne_pt)
  simp only [ioModel] at heq
  rw [interp_lamG, interp_lamConst_io] at heq
  exact lamV_dVal_ne_one heq.symm

/-- **An io-inferred type whose value is a truth value, inhabited by a
term that is not the point.**  `fun (x : Prop) => (fun (h : E x) => h) n`
io-infers `(x : Prop) → E x` (its sort is `Type`); that `∀` has an
empty fibre, so its value is empty — a truth value. -/
theorem io_type_value_collision [LevelOracle] (φ : Name → Nat) (ρ : Nat → V) :
    InferIO sortEnv [] lamMixed (.pi (.sort .zero) ex) ∧
    interp sortM φ ρ (.pi (.sort .zero) ex) ∈ˢ univ 0 ∧
    interp sortM φ ρ lamMixed ≠ pt := by
  refine ⟨?_, ?_, ?_⟩
  · exact InferIO.lam (InferIO.app (A := ex) (B := .app (.const eName []) (.bvar 1))
      (InferIO.lam (InferIO.bvar rfl)) .refl)
  · rw [interp_pi]
    unfold piV
    rcases Bool.eq_false_or_eq_true
      (propB (interp sortM φ ρ (.sort .zero)) (fun x => interp sortM φ (cons x ρ) ex)) with hp | hp <;>
      rw [hp]
    · exact piR_true_mem_univ_zero
    · rw [piR_false]
      refine mem_univ_zero.mpr fun z hz => ?_
      have := app_mem_piSet hz false_mem_typeU_zero
      rw [interp_consts (sortM_agree consts_ex), ex, interp_Ex φ ρ false_mem_typeU_zero,
        ite_eq_right one_ne_truthVal_false.symm] at this
      exact absurd (of_mem_truthVal this) id
  · rw [interp_consts (sortM_agree consts_lamMixed), interp_lamMixed]
    exact lamV_dVal_ne_pt

end Fragment
