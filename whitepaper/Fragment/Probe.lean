module

public import Fragment.ValueReading
import Fragment.Hygiene

public section

/-!
# The λ-congruence type check, probed (task #345)

Two findings about the check `DefEq.lam`/`DefEq.eta` under the
value-driven regimes (`ValueReading.lean`), each as a witness.

* **Point-denoting non-proofs** are the members of the types that
  denote `{pt}` at the valuation: `False → Nat` (`piV_of_empty`),
  `Nat → False → Nat` (`piV_const_one`: every fibre is `{pt}`), whose
  inhabitants `fun h => h.elim` and `fun n h => h.elim` are the point
  (`lamV_of_empty`, `lamV_const_pt`); and partial applications of
  functions that are not the point (`mixed_lam`: `fun P (h : P) => c`
  is a graph, its application at `False` the point, at `True` not).
  The soundness proof never asks whether a term is a *syntactic*
  proof (a member of a type of sort `Prop`) except in proof
  irrelevance; everywhere else it asks whether the value is the
  point, and it knows that only through a type the term lies in.

* **Comparing the bodies' sorts is not enough**
  (`lam_congr_sorts_unsound`).  The witness of `ValueReading.lean` has an
  ill-typed body; here both λs and both bodies are typed by the
  checker in the empty context, both bodies' types have sort `Type`,
  and the rule without the type comparison still equates two λs with
  different denotations.  The ill-typed redex is moved into the
  environment: a definition `d : (x : Prop) → F x` whose value is
  `fun x => (fun (h : E x) => h) n`, with `E`, `F`, `n` stored as
  opaque constants.  The environment has a model (`sortModel`, all
  laws of `EnvModel`), but `d`'s value is not typed, so the
  installation (`install_def`) would not accept it.  Every rule of the
  witness's derivations runs on typed terms except the δ step's
  reduct: the distance to a counterexample against an accepted
  environment is a typed term whose reduct holds an ill-typed redex.
-/

namespace Fragment

open SetLib Expr Classical

universe w

variable {V : Type w} [SetLib V]

/-! ## Point-denoting non-proofs -/

/-- `Nat → False → Nat`: every fibre is `{pt}`, so the function space is the
truth value `{pt}`, although its sort is `Type`. -/
theorem piV_const_one {A : V} : piV A (fun _ => one) = one := by
  unfold piV
  rw [propB_eq_true.mpr fun _ _ => one_mem_univ_zero, piR_true]
  exact ext fun z => by
    rw [mem_truthVal, mem_one]
    exact ⟨fun h => h.1, fun h => ⟨h, fun _ _ => rfl⟩⟩

/-- `fun n (h : False) => h.elim`: every body value is the point, so the
abstraction is. -/
theorem lamV_const_pt {A : V} : lamV A (fun _ => pt) = pt := lamV_eq_pt fun _ _ => rfl

/-- `fun (P : Prop) (h : P) => c`, for `c` not the point: a graph, whose
application at `False` is the point (an abstraction over an empty
domain) and at `True` is not — a body whose point-ness varies with the
variable. -/
theorem mixed_lam {c : V} (hc : c ≠ pt) :
    lamV (typeU 0) (fun P => lamV P fun _ => c) ≠ pt ∧
    SetLib.app (lamV (typeU 0) (fun P => lamV P fun _ => c)) (truthVal False) = pt ∧
    SetLib.app (lamV (typeU 0) (fun P => lamV P fun _ => c)) one ≠ pt := by
  have hone : lamV (one : V) (fun _ => c) ≠ pt :=
    lamV_ne_pt_of (mem_one.mpr rfl) hc
  refine ⟨lamV_ne_pt_of one_mem_typeU_zero hone, ?_, ?_⟩
  · rw [app_lamV false_mem_typeU_zero]
    exact lamV_of_empty fun z hz => of_mem_truthVal hz
  · rw [app_lamV one_mem_typeU_zero]; exact hone

/-! ## Comparing the bodies' sorts is not enough -/

/-- The family `F : Prop → Type`. -/
@[expose] def fName : Name := "F"

/-- The definition `d : (x : Prop) → F x`. -/
@[expose] def dName : Name := "d"

/-- `F x`. -/
@[expose] def fx : Expr := .app (.const fName []) (.bvar 0)

/-- `d x`. -/
@[expose] def dx : Expr := .app (.const dName []) (.bvar 0)

/-- `Prop → Type`. -/
@[expose] def propToType : Expr := .pi (.sort .zero) (.sort (.succ .zero))

/-- The environment: `E`, `n`, `F` opaque (constructor-kind constants,
which carry no law beyond their type), and `d := lamMixed`. -/
@[expose] def sortEnv : Env :=
  ⟨[(dName, ⟨[], .pi (.sort .zero) fx, .defn lamMixed⟩),
    (fName, ⟨[], propToType, .ctor "X" 0 0⟩),
    (nName, ⟨[], .sort .zero, .ctor "X" 0 0⟩),
    (eName, ⟨[], propToType, .ctor "X" 0 0⟩)]⟩

/-- `F`'s value: `Prop` at `True`, `{pt}` elsewhere. -/
@[expose] noncomputable def fVal : V → V := fun x => if x = one then typeU 0 else one

/-- `d`'s value at `x`: `True` at `True`, the point elsewhere. -/
@[expose] noncomputable def dVal : V → V := fun x => if x = one then one else pt

/-- The model: `mixedM` with `F` and `d` added. -/
noncomputable def sortM : Name → List Nat → V := fun c ls =>
  if c = fName then lamV (typeU 0) fVal
  else if c = dName then lamV (typeU 0) dVal
  else mixedM c ls

theorem sortM_F (ls : List Nat) : (sortM fName ls : V) = lamV (typeU 0) fVal := by
  simp [sortM]

theorem sortM_d (ls : List Nat) : (sortM dName ls : V) = lamV (typeU 0) dVal := by
  simp [sortM, fName, dName]

theorem sortM_n (ls : List Nat) : (sortM nName ls : V) = one := by
  have h := mixedM_n (V := V) ls
  simp only [sortM, fName, dName, nName] at h ⊢
  simpa using h

theorem sortM_E (ls : List Nat) : (sortM eName ls : V) = mixedM eName ls := by
  simp [sortM, fName, dName, eName]

/-- `sortM` agrees with `mixedM` on `E` and `n`, the constants of
`lamMixed` and `lamConst`. -/
theorem sortM_agree {e : Expr} (h : ∀ c ∈ e.consts, c = eName ∨ c = nName) :
    ∀ c ∈ e.consts, ∀ ls, (sortM c ls : V) = mixedM c ls := by
  intro c hc ls
  rcases h c hc with rfl | rfl
  · exact sortM_E ls
  · rw [sortM_n, mixedM_n]

theorem consts_lamMixed : ∀ c ∈ lamMixed.consts, c = eName ∨ c = nName := by
  intro c hc
  simp [lamMixed, mixedBody, Expr.consts] at hc
  rcases hc with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fVal_mem (x : V) : fVal x ∈ˢ (typeU 1 : V) := by
  unfold fVal
  split
  · exact typeU_mem_typeU_succ 0
  · exact (mem_typeU_pos (by omega)).mpr
      ⟨univ_mono (Nat.zero_le 1) one_mem_univ_zero, IsTy_one⟩

theorem IsTy_fVal (x : V) : IsTy (fVal x) := by
  unfold fVal; split
  · exact IsTy_typeU 0
  · exact IsTy_one

theorem dVal_mem (x : V) : dVal x ∈ˢ fVal x := by
  unfold dVal fVal; split
  · exact one_mem_typeU_zero
  · exact mem_one.mpr rfl

theorem F_mem : lamV (typeU 0 : V) fVal ∈ˢ piV (typeU 0) (fun _ => typeU 1) :=
  lamV_mem (fun x _ => fVal_mem x) fun _ _ => IsTy_typeU 1

theorem d_mem : lamV (typeU 0 : V) dVal ∈ˢ piV (typeU 0) fVal :=
  lamV_mem (fun x _ => dVal_mem x) fun x _ => IsTy_fVal x

/-- `E`'s value is an abstraction (its graph is not the point). -/
theorem mixedM_E_lamV (ls : List Nat) :
    (mixedM eName ls : V) =
      lamV (typeU 0) (fun x => if x = one then typeU 0 else truthVal False) := by
  rw [mixedM_E, eq_comm]
  apply lamV_eq_graph
  refine lamV_ne_pt_of one_mem_typeU_zero ?_
  rw [ite_eq_left rfl]; exact (IsTy_typeU 0).ne_pt

theorem E_mem (ls : List Nat) : (mixedM eName ls : V) ∈ˢ piV (typeU 0) (fun _ => typeU 1) := by
  rw [mixedM_E_lamV]
  refine lamV_mem (fun x _ => ?_) fun _ _ => IsTy_typeU 1
  split
  · exact typeU_mem_typeU_succ 0
  · exact (mem_typeU_pos (by omega)).mpr
      ⟨univ_mono (Nat.zero_le 1) (truthVal_mem_univ_zero False), Or.inl (truthVal_mem_univ_zero False)⟩

section
variable (φ : Name → Nat)

theorem interp_fx {ρ : Nat → V} (hx : ρ 0 ∈ˢ typeU 0) : interp sortM φ ρ fx = fVal (ρ 0) := by
  rw [fx, interp_app, interp_const, interp_bvar, sortM_F, app_lamV hx]

theorem interp_dx {ρ : Nat → V} (hx : ρ 0 ∈ˢ typeU 0) : interp sortM φ ρ dx = dVal (ρ 0) := by
  rw [dx, interp_app, interp_const, interp_bvar, sortM_d, app_lamV hx]

theorem WellDenoted_propToType (ρ : Nat → V) : WellDenoted sortM φ ρ propToType := by
  rw [propToType, WellDenoted_pi]
  exact ⟨trivial, IsTy_typeU 0, fun _ _ => trivial, fun _ _ => IsTy_typeU 1⟩

theorem interp_propToType (ρ : Nat → V) :
    interp sortM φ ρ propToType = piV (typeU 0) (fun _ => typeU 1) := by
  simp [propToType]

theorem WellDenoted_fx {ρ : Nat → V} (hx : ρ 0 ∈ˢ typeU 0) : WellDenoted sortM φ ρ fx := by
  rw [fx, WellDenoted_app]
  refine ⟨trivial, trivial, appliesTo_of_mem_piV (A := typeU 0) (B := fun _ => typeU 1) ?_
    (IsTy_typeU 0) hx⟩
  rw [interp_const, sortM_F]; exact F_mem

theorem WellDenoted_dx {ρ : Nat → V} (hx : ρ 0 ∈ˢ typeU 0) : WellDenoted sortM φ ρ dx := by
  rw [dx, WellDenoted_app]
  refine ⟨trivial, trivial, appliesTo_of_mem_piV (A := typeU 0) (B := fVal) ?_
    (IsTy_typeU 0) hx⟩
  rw [interp_const, sortM_d]; exact d_mem

theorem WellDenoted_dType (ρ : Nat → V) : WellDenoted sortM φ ρ (.pi (.sort .zero) fx) := by
  rw [WellDenoted_pi]
  refine ⟨trivial, IsTy_typeU 0, fun x hx => WellDenoted_fx φ hx, fun x hx => ?_⟩
  rw [interp_fx φ hx]; exact IsTy_fVal x

theorem interp_dType (ρ : Nat → V) : interp sortM φ ρ (.pi (.sort .zero) fx) = piV (typeU 0) fVal := by
  rw [interp_pi, interp_sort, Level.eval_zero]
  exact piV_congr fun x hx => interp_fx φ hx

/-- `lamMixed` (`d`'s value) is well-denoted under `mixedM`. -/
theorem WellDenoted_lamMixed (ρ : Nat → V) : WellDenoted mixedM φ ρ lamMixed := by
  rw [lamMixed, WellDenoted_lam]
  exact ⟨trivial, IsTy_typeU 0, fun x hx => WellDenoted_mixedBody φ ρ hx⟩

theorem interp_lamMixed (ρ : Nat → V) : interp mixedM φ ρ lamMixed = lamV (typeU 0) dVal := by
  rw [lamMixed, interp_lam, interp_sort, Level.eval_zero]
  exact lamV_congr fun x hx => interp_mixedBody φ ρ hx

end

theorem subst_nil_nil : ∀ u : Level, u.subst [] [] = u
  | .zero => rfl
  | .succ u => by simp [Level.subst, subst_nil_nil u]
  | .max a b => by simp [Level.subst, subst_nil_nil a, subst_nil_nil b]
  | .imax a b => by simp [Level.subst, subst_nil_nil a, subst_nil_nil b]
  | .param _ => rfl

theorem instL_nil_nil : ∀ e : Expr, e.instL [] [] = e
  | .bvar _ => rfl
  | .sort u => by simp [Expr.instL, subst_nil_nil]
  | .const c us => by
    have h : Level.subst [] [] = id := funext subst_nil_nil
    simp [Expr.instL, h]
  | .app f a => by simp [Expr.instL, instL_nil_nil f, instL_nil_nil a]
  | .lam A b => by simp [Expr.instL, instL_nil_nil A, instL_nil_nil b]
  | .pi A B => by simp [Expr.instL, instL_nil_nil A, instL_nil_nil B]
  | .letE T v b => by simp [Expr.instL, instL_nil_nil T, instL_nil_nil v, instL_nil_nil b]

/-- **The environment has a model.** -/
noncomputable def sortModel : EnvModel V sortEnv where
  M := sortM
  type_ok := by
    intro c ci h φ ρ ls hls
    simp only [sortEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      rw [instL_nil_nil, interp_dType]
      refine ⟨WellDenoted_dType _ ρ, IsTy_piV, ?_⟩
      rw [List.map_nil, sortM_d]; exact d_mem
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      rw [instL_nil_nil, interp_propToType]
      exact ⟨WellDenoted_propToType _ ρ, IsTy_piV, by rw [List.map_nil, sortM_F]; exact F_mem⟩
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      rw [instL_nil_nil, interp_sort, Level.eval_zero]
      exact ⟨trivial, IsTy_typeU 0, by rw [sortM_n]; exact one_mem_typeU_zero⟩
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      rw [instL_nil_nil, interp_propToType]
      exact ⟨WellDenoted_propToType _ ρ, IsTy_piV, by rw [List.map_nil, sortM_E]; exact E_mem _⟩
    · cases h
  unfold := by
    intro c ci v h hv φ ρ ls hls
    simp only [sortEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h
      simp only [List.length_nil, List.length_eq_zero_iff] at hls; subst hls
      rename_i hc; simp at hc; subst hc
      cases hv
      rw [instL_nil_nil, List.map_nil, sortM_d]
      refine ⟨(WellDenoted_consts (sortM_agree consts_lamMixed)).mpr (WellDenoted_lamMixed φ ρ), ?_⟩
      rw [interp_consts (sortM_agree consts_lamMixed), interp_lamMixed]
    split at h
    · cases h; cases hv
    split at h
    · cases h; cases hv
    split at h
    · cases h; cases hv
    · cases h
  rec_rules := by
    intro c ci _ _ _ _ _ h hk
    simp only [sortEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
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
    simp only [sortEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
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
    simp only [sortEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
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
    simp only [sortEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
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
    simp only [sortEnv, Env.find?, List.lookup_cons, List.lookup_nil] at h
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    split at h
    · cases h; cases hk
    · cases h

/-- `fun (x : Prop) => d x`. -/
@[expose] def lamD : Expr := .lam (.sort .zero) dx

/-- **Comparing the bodies' sorts is not enough.**  In a model of
`sortEnv`: both λs are typed in the empty context; the premises of
λ-congruence hold — the domains by `refl`, the bodies by δ, β, β and
`refl` — and so do the bodies' inferences, under the binder; the
bodies' types `F x` and `Prop` both have sort `Type`, so a check of
their sorts' zero-ness passes; the λs are well-denoted, not the point,
and different.  Only the comparison `F x ≡ Prop` fails. -/
theorem lam_congr_sorts_unsound [LevelOracle] (φ : Name → Nat) :
    Infer sortEnv [] lamD (.pi (.sort .zero) fx) ∧
    Infer sortEnv [] lamConst (.pi (.sort .zero) (.sort .zero)) ∧
    DefEq sortEnv [] (.sort .zero) (.sort .zero) ∧
    DefEq sortEnv [.sort .zero] dx (.const nName []) ∧
    Infer sortEnv [.sort .zero] dx fx ∧
    Infer sortEnv [.sort .zero] (.const nName []) (.sort .zero) ∧
    Infer sortEnv [.sort .zero] fx (.sort (.succ .zero)) ∧
    Infer sortEnv [.sort .zero] (.sort .zero) (.sort (.succ .zero)) ∧
    ¬ DefEqSem (sortModel (V := V)) φ [] lamD lamConst := by
  have hd : sortEnv.find? dName = some ⟨[], .pi (.sort .zero) fx, .defn lamMixed⟩ := by
    simp [sortEnv, Env.find?]
  have hF : sortEnv.find? fName = some ⟨[], propToType, .ctor "X" 0 0⟩ := by
    simp [sortEnv, Env.find?, List.lookup, fName, dName]
  have hn : sortEnv.find? nName = some ⟨[], .sort .zero, .ctor "X" 0 0⟩ := by
    simp [sortEnv, Env.find?, List.lookup, fName, dName, nName]
  have hIdx : Infer sortEnv [.sort .zero] dx fx := by
    have := Infer.app (env := sortEnv) (Γ := [.sort .zero]) (f := .const dName [])
      (a := .bvar 0) (A := .sort .zero) (B := fx)
      (by have := Infer.const (env := sortEnv) (Γ := [.sort .zero]) (ls := []) hd rfl
          rwa [instL_nil_nil] at this) .refl (.bvar rfl) .refl
    exact this
  have hIfx : Infer sortEnv [.sort .zero] fx (.sort (.succ .zero)) := by
    have := Infer.app (env := sortEnv) (Γ := [.sort .zero]) (f := .const fName [])
      (a := .bvar 0) (A := .sort .zero) (B := .sort (.succ .zero))
      (by have := Infer.const (env := sortEnv) (Γ := [.sort .zero]) (ls := []) hF rfl
          rwa [instL_nil_nil] at this) .refl (.bvar rfl) .refl
    exact this
  have hIn : ∀ Γ, Infer sortEnv Γ (.const nName []) (.sort .zero) := by
    intro Γ
    have := Infer.const (env := sortEnv) (Γ := Γ) (ls := []) hn rfl
    rwa [instL_nil_nil] at this
  refine ⟨.lam .sort .refl hIdx, .lam .sort .refl (hIn _), .refl, ?_, hIdx, hIn _, hIfx, .sort, ?_⟩
  · -- `d x` unfolds, then two β steps reach `n`
    have hδ : Red sortEnv [.sort .zero] dx (.app lamMixed (.bvar 0)) := by
      have := Red.appFn (a := .bvar 0) (Red.delta (env := sortEnv) (Γ := [.sort .zero])
        (ls := []) hd rfl rfl)
      rwa [instL_nil_nil] at this
    refine .redL (.trans hδ .beta) (.redL ?_ .refl)
    exact .beta
  · intro h
    have hw₁ : WellDenoted (sortM (V := V)) φ (fun _ => (pt : V)) lamD := by
      rw [lamD, WellDenoted_lam]
      exact ⟨trivial, IsTy_typeU 0, fun x hx => WellDenoted_dx φ hx⟩
    have hw₂ : WellDenoted (sortM (V := V)) φ (fun _ => (pt : V)) lamConst := by
      rw [lamConst, WellDenoted_lam]
      exact ⟨trivial, IsTy_typeU 0, fun _ _ => trivial⟩
    have hv₁ : interp (sortM (V := V)) φ (fun _ => (pt : V)) lamD = lamV (typeU 0) dVal := by
      rw [lamD, interp_lam, interp_sort, Level.eval_zero]
      exact lamV_congr fun x hx => interp_dx φ hx
    have hv₂ : interp (sortM (V := V)) φ (fun _ => (pt : V)) lamConst = lamV (typeU 0) (fun _ => one) := by
      rw [lamConst, interp_lam, interp_sort, Level.eval_zero]
      exact lamV_congr fun x _ => by rw [interp_const, sortM_n]
    have hn₁ : interp (sortM (V := V)) φ (fun _ => (pt : V)) lamD ≠ pt := by
      rw [hv₁]; refine lamV_ne_pt_of one_mem_typeU_zero ?_
      simp only [dVal]; exact one_ne_pt
    have hn₂ : interp (sortM (V := V)) φ (fun _ => (pt : V)) lamConst ≠ pt := by
      rw [hv₂]; exact lamV_ne_pt_of one_mem_typeU_zero one_ne_pt
    have heq : interp (sortM (V := V)) φ (fun _ => (pt : V)) lamD = interp (sortM (V := V)) φ (fun _ => (pt : V)) lamConst :=
      h (fun _ => pt) trivial hw₁ hw₂ hn₁ hn₂
    rw [hv₁, hv₂] at heq
    have happ := congrArg (fun f => SetLib.app f (truthVal False)) heq
    simp only [app_lamV false_mem_typeU_zero, dVal,
      ite_eq_right one_ne_truthVal_false.symm] at happ
    exact one_ne_pt happ.symm

end Fragment
