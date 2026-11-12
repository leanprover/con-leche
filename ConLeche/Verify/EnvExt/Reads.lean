module

public import ConLeche.Verify.EnvWF
import ConLeche.Verify.InferLemmas
public import ConLeche.Verify.EnvPreds
import ConLeche.Verify.PropRead
import ConLeche.Verify.StrLitExpr
import ConLeche.Verify.InstSpine

/-!
# A run does not see an extension of the environment: the reads (task #480)

`env₂` extends `env₁`.  A term all of whose constants and literals resolve in `env₁` reads the
two environments alike.  This module has the vocabulary (`StoredFacts`, `EnvExt`, `Res`), the
closure of resolution under the term operations the knot uses, and the knot's pure readers.  The
knot itself is `Verify/EnvExt.lean`.
-/

@[expose] public section

namespace ConLeche.Verify

open ConLeche

/-- **What the knot reads of an environment past the term in hand**, which every declaration
boundary has: stored terms resolve, `Nat`'s block is stored at once, a recursor's rules and a
table's entries name stored constructors, and the `Bool` constructors are stored below the
comparison operations. -/
structure StoredFacts (env : Env) : Prop where
  wf : EnvWF env
  natTrio : (env.find? natName).isSome = true ∨ (env.find? natZeroName).isSome = true ∨
      (env.find? natSuccName).isSome = true →
    (env.find? natName).isSome = true ∧ (env.find? natZeroName).isSome = true ∧
      (env.find? natSuccName).isSome = true
  recCtors : RecCtorsStored env
  tableCtors : ∀ T tbl, env.findTable? T = some tbl → (env.find? tbl.ctor).isSome = true
  boolCtors : isDefinitionAt env natBeqName = true ∨ isDefinitionAt env natBleName = true →
    (env.find? boolTrueName).isSome = true ∧ (env.find? boolFalseName).isSome = true
  opDefn : OpDefn env

/-- An entry's constructor is its table's. -/
theorem StoredFacts.entryCtors {env : Env} (h : StoredFacts env) {T : Name} {i : Nat}
    {e : ProjEntry} (hf : env.findProj? T i = some e) : (env.find? e.ctor).isSome = true := by
  obtain ⟨tbl, hT, -, rfl⟩ := Env.findProj?_some hf
  exact h.tableCtors T tbl hT

/-- **`env₂` extends `env₁`**: every stored constant stays and a stored structure's table stays. -/
structure EnvExt (env₁ env₂ : Env) : Prop where
  find : ∀ n ci, env₁.find? n = some ci → env₂.find? n = some ci
  table : ∀ T, (env₁.find? T).isSome = true → env₂.findTable? T = env₁.findTable? T
  facts : StoredFacts env₁

/-- Resolution in `env`. -/
abbrev Res (env : Env) (e : Expr) : Prop := e.constsResolve env = true

variable {env₁ env₂ : Env}

theorem EnvExt.find_of_isSome (h : EnvExt env₁ env₂) {n : Name}
    (hn : (env₁.find? n).isSome = true) : env₂.find? n = env₁.find? n := by
  cases hf : env₁.find? n with
  | none => rw [hf] at hn; exact nomatch hn
  | some ci => exact h.find n ci hf

theorem EnvExt.findProj (h : EnvExt env₁ env₂) {T : Name} (hT : (env₁.find? T).isSome = true)
    (i : Nat) : env₂.findProj? T i = env₁.findProj? T i := by
  unfold Env.findProj?
  rw [h.table T hT]

/-! ## Resolution under the term operations -/

theorem res_of_find {env : Env} {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci) :
    (env.find? n).isSome = true := by
  rw [hf]; rfl

theorem res_instantiate1 {env : Env} {v : Expr} (hv : Res env v) :
    ∀ (e : Expr) (k : Nat), Res env e → Res env (e.instantiate1 v k) := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.instantiate1, Expr.constsResolve, Res]
  case bvar i =>
    split
    · exact hv
    · split <;> simp [Expr.constsResolve]

theorem res_abstract1 {env : Env} (d : Nat) :
    ∀ (e : Expr) (k : Nat), Res env e → Res env (e.abstract1 d k) := by
  intro e
  induction e <;> intro k h <;> simp_all [Expr.abstract1, Expr.constsResolve, Res]
  case fvar i ty =>
    split
    · simp [Expr.constsResolve]
    · simpa [Expr.constsResolve] using h

theorem res_mkAppN {env : Env} :
    ∀ {xs : List Expr} {f : Expr}, Res env f → (∀ x ∈ xs, Res env x) → Res env (Expr.mkAppN f xs)
  | [], _, hf, _ => hf
  | x :: xs, f, hf, hxs => by
    simp only [Expr.mkAppN]
    refine res_mkAppN ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
    simp only [Res, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨hf, hxs x List.mem_cons_self⟩

theorem res_getAppArgs {env : Env} :
    ∀ {e : Expr}, Res env e → ∀ x ∈ e.getAppArgs, Res env x := by
  intro e
  induction e with
  | app f a ihf _ =>
    intro h x hx
    simp only [Res, Expr.constsResolve, Bool.and_eq_true] at h
    simp only [Expr.getAppArgs, List.mem_append, List.mem_singleton] at hx
    rcases hx with hx | rfl
    · exact ihf h.1 x hx
    · exact h.2
  | _ => intro _ x hx; simp [Expr.getAppArgs] at hx

theorem res_instSpine {env : Env} :
    ∀ {args : List Expr} (t : Nat) {e : Expr}, Res env e → (∀ a ∈ args, Res env a) →
      Res env (Expr.instSpine args t e)
  | [], _, _, he, _ => he
  | a :: _as, t, e, he, hargs =>
    res_instSpine (t - 1) (res_instantiate1 (hargs a List.mem_cons_self) e t he)
      (fun a' ha' => hargs a' (List.mem_cons_of_mem _ ha'))

theorem res_instantiateList {env : Env} :
    ∀ {vs : List Expr}, (∀ v ∈ vs, Res env v) → ∀ {e : Expr} (d : Nat), Res env e →
      Res env (e.instantiateList vs d)
  | [], _, e, d, he => by rw [Expr.instantiateList_nil]; exact he
  | v :: _vs, hvs, e, d, he => by
    rw [Expr.instantiateList_cons]
    exact res_instantiate1 (hvs v List.mem_cons_self) _ d
      (res_instantiateList (fun w hw => hvs w (List.mem_cons_of_mem _ hw)) (d + 1) he)

theorem res_inst {env : Env} (ks : List Name) (us : List Level) {e : Expr} (h : Res env e) :
    Res env (e.instantiateLevelParams ks us) := by
  simpa [Res, Expr.constsResolve_instantiateLevelParams] using h

theorem res_getAppFn {env : Env} {e : Expr} (h : Res env e) : Res env e.getAppFn :=
  Expr.constsResolve_getAppFn h

theorem res_piResult {env : Env} {e : Expr} (h : Res env e) : Res env e.piResult :=
  Expr.constsResolve_piResult h

/-- A constant at a resolved head is stored. -/
theorem res_head {env : Env} {e : Expr} {c : Name} {us : List Level} (h : Res env e)
    (hfn : e.getAppFn = .const c us) : (env.find? c).isSome = true := by
  have := res_getAppFn h
  rw [hfn] at this
  simpa [Res, Expr.constsResolve] using this

theorem res_app {env : Env} {f a : Expr} : Res env (.app f a) ↔ Res env f ∧ Res env a := by
  simp [Res, Expr.constsResolve]

theorem res_forall {env : Env} {t b : Expr} : Res env (.forallE t b) ↔ Res env t ∧ Res env b := by
  simp [Res, Expr.constsResolve]

theorem res_lam {env : Env} {t b : Expr} : Res env (.lam t b) ↔ Res env t ∧ Res env b := by
  simp [Res, Expr.constsResolve]

theorem res_let {env : Env} {t v b : Expr} :
    Res env (.letE t v b) ↔ Res env t ∧ Res env v ∧ Res env b := by
  simp [Res, Expr.constsResolve, and_assoc]

theorem res_proj {env : Env} {s : Name} {i : Nat} {e : Expr} :
    Res env (.proj s i e) ↔ (env.find? s).isSome = true ∧ Res env e := by
  simp [Res, Expr.constsResolve]

theorem res_const {env : Env} {n : Name} {us : List Level} :
    Res env (.const n us) ↔ (env.find? n).isSome = true := by
  simp [Res, Expr.constsResolve]

theorem res_fvar {env : Env} {i : Nat} {t : Expr} : Res env (.fvar i t) ↔ Res env t := by
  simp [Res, Expr.constsResolve]

theorem res_sort {env : Env} {u : Level} : Res env (.sort u) := rfl

theorem res_bvar {env : Env} {i : Nat} : Res env (.bvar i) := rfl

/-- Opening a binder at a variable of a resolved domain. -/
theorem res_open {env : Env} {d : Nat} {t b : Expr} (ht : Res env t) (hb : Res env b) :
    Res env (b.instantiate1 (.fvar d t)) :=
  res_instantiate1 (res_fvar.mpr ht) b 0 hb

theorem res_natLit {env : Env} (h : StoredFacts env)
    (hs : (env.find? natName).isSome = true ∨ (env.find? natZeroName).isSome = true ∨
      (env.find? natSuccName).isSome = true) (n : Nat) : Res env (.lit (.natVal n)) := by
  obtain ⟨h₁, h₂, h₃⟩ := h.natTrio hs
  simp [Res, Expr.constsResolve, h₁, h₂, h₃]

/-- What a stored constant's record gives. -/
theorem StoredFacts.type {env : Env} (h : StoredFacts env) {n : Name} {ci : ConstantInfo}
    (hf : env.find? n = some ci) : Res env ci.toConstantVal.type :=
  (h.wf.consts ci (Env.find?_mem hf)).2.2.1

theorem StoredFacts.value {env : Env} (h : StoredFacts env) {n : Name} {cv : ConstantVal}
    {v : Expr} {hint : ReducibilityHint} (hf : env.find? n = some (.defnInfo cv v hint)) :
    Res env v :=
  ((h.wf.consts _ (Env.find?_mem hf)).2.2.2.2.1 cv v hint rfl).2.2.1

theorem StoredFacts.rhs {env : Env} (h : StoredFacts env) {n : Name} {cv : ConstantVal}
    {mI rP : Nat} {isK : Bool} {rules : List RecRule} {r : RecRule}
    (hf : env.find? n = some (.recInfo cv mI rP isK rules)) (hr : r ∈ rules) :
    Res env (RecRule.rhs r) :=
  ((h.wf.consts _ (Env.find?_mem hf)).2.2.2.2.2 cv mI rP isK rules rfl r hr).2.2.1

/-- The body of a table's entry. -/
theorem StoredFacts.entryBody {env : Env} (h : StoredFacts env) {T : Name} {i : Nat}
    {e : ProjEntry} (hf : env.findProj? T i = some e) : Res env e.body := by
  obtain ⟨tbl, hT, hi, rfl⟩ := Env.findProj?_some hf
  obtain ⟨-, hsz, hb⟩ := h.wf.table hT
  have hlt : i < tbl.bodies.size := hsz ▸ hi
  have hget : tbl.bodies[i]? = some (tbl.bodies.getD i default) := by
    rw [Array.getElem?_eq_getElem hlt, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt]
    rfl
  exact (hb i _ hget).2.2.1

/-! ## The readers of a term's head -/

section Readers

variable (hx : EnvExt env₁ env₂)
include hx

theorem isCtorApp_ext {e : Expr} (he : Res env₁ e) : isCtorApp env₂ e = isCtorApp env₁ e := by
  unfold isCtorApp
  cases hfn : e.getAppFn <;> try rfl
  dsimp only
  rw [hx.find_of_isSome (res_head he hfn)]

theorem etaCtorShape_ext {e : Expr} (he : Res env₁ e) :
    etaCtorShape env₂ e = etaCtorShape env₁ e := by
  unfold etaCtorShape
  cases hfn : e.getAppFn <;> try rfl
  dsimp only
  rw [hx.find_of_isSome (res_head he hfn)]

/-- `etaCtorPartial` reads the head constructor, the family its stored
type ends in, both resolved, and the family's table. -/
theorem etaCtorPartial_ext {e : Expr} (he : Res env₁ e) :
    etaCtorPartial env₂ e = etaCtorPartial env₁ e := by
  unfold etaCtorPartial
  cases hfn : e.getAppFn <;> try rfl
  rename_i c us
  dsimp only
  have hc := res_head he hfn
  rw [hx.find_of_isSome hc]
  cases hfc : env₁.find? c with
  | none => rfl
  | some ci =>
    cases ci <;> try rfl
    rename_i cvc cnP cnF T
    dsimp only
    have hty : Res env₁ cvc.type :=
      (hx.facts.wf.consts _ (Env.find?_mem hfc)).2.2.1
    split
    case isFalse => rfl
    obtain ⟨_, hft⟩ := hx.facts.wf.ctorHead hfc
    have hT := res_head (res_piResult hty) hft
    rw [hx.find_of_isSome hT, hx.table _ hT]

omit hx in
/-- A peel of a resolved telescope resolves. -/
theorem res_peelPis : ∀ {n : Nat} {e r : Expr}, Res env₁ e → Expr.peelPis n e = some r →
    Res env₁ r
  | 0, e, r, he, h => by
    simp only [Expr.peelPis, Option.some.injEq] at h; exact h ▸ he
  | n + 1, .forallE _ b, r, he, h => res_peelPis (res_forall.mp he).2 h
  | _ + 1, .bvar _, _, _, h | _ + 1, .fvar _ _, _, _, h | _ + 1, .sort _, _, _, h
  | _ + 1, .const _ _, _, _, h | _ + 1, .app _ _, _, _, h | _ + 1, .lam _ _, _, _, h
  | _ + 1, .letE _ _ _, _, _, h | _ + 1, .lit _, _, _, h
  | _ + 1, .proj _ _ _, _, _, h => nomatch h

omit hx in
/-- The field telescope of a resolved constructor type at resolved
arguments resolves. -/
theorem res_unitFieldTele {cty tele : Expr} {n : Nat} {args : List Expr}
    (hc : Res env₁ cty) (hargs : ∀ a ∈ args, Res env₁ a)
    (h : unitFieldTele cty n args = some tele) : Res env₁ tele := by
  rw [unitFieldTele_eq] at h
  cases hb : Expr.peelPis n cty with
  | none => rw [hb] at h; exact nomatch h
  | some body =>
    rw [hb] at h
    obtain rfl := Option.some.inj h
    exact res_instSpine _ (res_peelPis hc hb) hargs
theorem unfoldDefinition_ext {e : Expr} (he : Res env₁ e) :
    unfoldDefinition env₂ e = unfoldDefinition env₁ e := by
  unfold unfoldDefinition
  cases hfn : e.getAppFn <;> try rfl
  dsimp only
  rw [hx.find_of_isSome (res_head he hfn)]

theorem unfoldableHead_ext {e : Expr} (he : Res env₁ e) :
    unfoldableHead env₂ e = unfoldableHead env₁ e := by
  unfold unfoldableHead
  cases hfn : e.getAppFn <;> try rfl
  dsimp only
  rw [hx.find_of_isSome (res_head he hfn)]

theorem headHint_ext {e : Expr} (he : Res env₁ e) : headHint env₂ e = headHint env₁ e := by
  unfold headHint
  cases hfn : e.getAppFn <;> try rfl
  dsimp only
  rw [hx.find_of_isSome (res_head he hfn)]

/-- `unitLikeShape` reads the head family, its table and the table's
constructor, all stored. -/
theorem unitLikeShape_ext {w : Expr} (hw : Res env₁ w) :
    unitLikeShape env₂ w = unitLikeShape env₁ w := by
  unfold unitLikeShape
  cases hft : w.getAppFn <;> try rfl
  rename_i S us
  dsimp only
  have hS := res_head hw hft
  rw [hx.find_of_isSome hS, hx.table S hS]
  cases hT : env₁.findTable? S with
  | none => rfl
  | some tbl =>
    dsimp only
    rw [hx.find_of_isSome (hx.facts.tableCtors S tbl hT)]

/-- The field telescope of a resolved instance resolves. -/
theorem res_unitLikeShape {w tele : Expr} {n : Nat} (hw : Res env₁ w)
    (h : unitLikeShape env₁ w = some (tele, n)) : Res env₁ tele := by
  obtain ⟨S, us, _, _, _, cvC, _, _, _, -, -, -, -, -, -, hfC, -, ht⟩ := unitLikeShape_some h
  have hc : Res env₁ (cvC.type.instantiateLevelParams cvC.levelParams us) :=
    res_inst _ _ (hx.facts.wf.consts _ (Env.find?_mem hfC)).2.2.1
  exact res_unitFieldTele hc (res_getAppArgs hw) ht

theorem natLit_ext (hn : (env₁.find? natName).isSome = true ∨
    (env₁.find? natZeroName).isSome = true ∨ (env₁.find? natSuccName).isSome = true) :
    natLitStored env₂ = natLitStored env₁ := by
  obtain ⟨h₁, h₂, h₃⟩ := hx.facts.natTrio hn
  unfold natLitStored
  rw [hx.find_of_isSome h₁, hx.find_of_isSome h₂, hx.find_of_isSome h₃]

/-- A resolved `Nat` literal's support. -/
theorem natLit_of_res {n : Nat} (h : Res env₁ (.lit (.natVal n))) :
    natLitStored env₂ = natLitStored env₁ := by
  simp only [Res, Expr.constsResolve, Bool.and_eq_true] at h
  exact natLit_ext hx (.inl h.1.1)

/-- A resolved `String` literal's support. -/
theorem strLit_of_res {s : String} (h : Res env₁ (.lit (.strVal s))) :
    strLitStored env₂ = strLitStored env₁ := by
  simp only [Res, Expr.constsResolve, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩, h₅⟩, h₆⟩, h₇⟩, h₈⟩, h₉⟩, h₁₀⟩ := h
  unfold strLitStored natLitStored
  rw [hx.find_of_isSome h₁, hx.find_of_isSome h₂, hx.find_of_isSome h₃, hx.find_of_isSome h₄,
    hx.find_of_isSome h₅, hx.find_of_isSome h₆, hx.find_of_isSome h₇, hx.find_of_isSome h₈,
    hx.find_of_isSome h₉, hx.find_of_isSome h₁₀]

omit hx in
/-- A constructor form's constants, off a resolved literal. -/
theorem res_strLitToConstructor {s : String} (h : Res env₁ (.lit (.strVal s))) :
    Res env₁ (strLitToConstructor s) := by
  simp only [Res, Expr.constsResolve, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h₁, h₂⟩, h₃⟩, -⟩, h₅⟩, -⟩, h₇⟩, h₈⟩, h₉⟩, h₁₀⟩ := h
  rw [strLitToConstructor_eq]
  refine res_app.mpr ⟨res_const.mpr h₅, ?_⟩
  generalize s.toList = cs
  induction cs with
  | nil => simp [strLitList, Res, Expr.constsResolve, h₇, h₉]
  | cons c cs ih =>
    simp only [strLitList, Res, Expr.constsResolve, Bool.and_eq_true]
    exact ⟨⟨⟨h₈, h₉⟩, h₁₀, ⟨⟨h₁, h₂⟩, h₃⟩⟩, ih⟩

omit hx in
/-- The literal's one-layer constructor form. -/
theorem res_litToCtorIfNat {e : Expr} (he : Res env₁ e) : Res env₁ (litToCtorIfNat env₁ e) := by
  match e with
  | .lit (.natVal n) =>
    rw [litToCtorIfNat]
    split
    · simp only [Res, Expr.constsResolve, Bool.and_eq_true] at he
      cases n with
      | zero => exact res_const.mpr he.1.2
      | succ k =>
        refine res_app.mpr ⟨res_const.mpr he.2, ?_⟩
        simp [Res, Expr.constsResolve, he.1.1, he.1.2, he.2]
    · exact he
  | .lit (.strVal _) | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ | .forallE _ _ | .letE _ _ _ | .proj _ _ _ => exact he

theorem litToCtorIfNat_ext {e : Expr} (he : Res env₁ e) :
    litToCtorIfNat env₂ e = litToCtorIfNat env₁ e := by
  match e with
  | .lit (.natVal n) => simp only [litToCtorIfNat, natLit_of_res hx he]
  | .lit (.strVal _) | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .app _ _
  | .lam _ _ | .forallE _ _ | .letE _ _ _ | .proj _ _ _ => rfl

/-- What `unfoldDefinition` returns resolves. -/
theorem res_unfoldDefinition {e e' : Expr} (he : Res env₁ e)
    (h : unfoldDefinition env₁ e = some e') : Res env₁ e' := by
  unfold unfoldDefinition at h
  cases hfn : e.getAppFn with
  | const n us =>
    rw [hfn] at h
    dsimp only at h
    cases hf : env₁.find? n with
    | none => rw [hf] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      cases ci with
      | defnInfo cv v hint =>
        dsimp only at h
        split at h
        · obtain rfl := Option.some.inj h
          exact res_mkAppN (res_inst _ _ (hx.facts.value hf)) (res_getAppArgs he)
        · exact nomatch h
      | _ => exact nomatch h
  | _ => rw [hfn] at h; exact nomatch h

/-! ## The head-symbol readers of proofs -/

omit hx in
theorem res_getD {l : List Expr} (hl : ∀ a ∈ l, Res env₁ a) {i : Nat} {d : Expr}
    (hd : Res env₁ d) : Res env₁ (l.getD i d) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : l[i]? with
  | none => exact hd
  | some a => exact hl a (List.mem_of_getElem? h)

theorem unwrapIdDefs_ext : ∀ (fuel : Nat) {e : Expr}, Res env₁ e →
    unwrapIdDefs env₂.find? fuel e = unwrapIdDefs env₁.find? fuel e ∧
      Res env₁ (unwrapIdDefs env₁.find? fuel e)
  | 0, _, he => ⟨rfl, he⟩
  | fuel + 1, e, he => by
    unfold unwrapIdDefs
    cases hfn : e.getAppFn with
    | const c us =>
      dsimp only
      rw [hx.find_of_isSome (res_head he hfn)]
      cases env₁.find? c with
      | none => exact ⟨rfl, he⟩
      | some ci =>
        cases ci with
        | defnInfo _ v _ =>
          dsimp only
          cases lamProj? 0 v with
          | none => exact ⟨rfl, he⟩
          | some kj =>
            dsimp only
            split
            · exact unwrapIdDefs_ext fuel (res_getD (res_getAppArgs he) he)
            · exact ⟨rfl, he⟩
        | _ => exact ⟨rfl, he⟩
    | _ => exact ⟨rfl, he⟩

theorem peelPisW_ext : ∀ (k : Nat) {e : Expr}, Res env₁ e →
    peelPisW env₂.find? k e = peelPisW env₁.find? k e ∧
      ∀ r, peelPisW env₁.find? k e = some r → Res env₁ r
  | 0, e, he => by
    obtain ⟨h₁, h₂⟩ := unwrapIdDefs_ext hx 4 he
    simp only [peelPisW, h₁, true_and]
    exact fun r hr => Option.some.inj hr ▸ h₂
  | k + 1, e, he => by
    cases e with
    | forallE _ b =>
      simp only [peelPisW]
      exact peelPisW_ext k (res_forall.mp he).2
    | _ =>
      obtain ⟨h₁, h₂⟩ := unwrapIdDefs_ext hx 4 he
      simp only [peelPisW, h₁]
      generalize unwrapIdDefs env₁.find? 4 _ = u at h₂ ⊢
      cases u with
      | forallE _ b => exact peelPisW_ext k (res_forall.mp h₂).2
      | _ => exact ⟨rfl, fun _ h => nomatch h⟩

omit hx in
theorem res_binderDom : ∀ (k : Nat) {e d : Expr}, Res env₁ e → e.binderDom k = some d → Res env₁ d
  | 0, e, _, he, h => by
    cases e <;> first
      | (obtain rfl := Option.some.inj h; exact (res_forall.mp he).1)
      | simp [Expr.binderDom] at h
  | k + 1, e, _, he, h => by
    cases e <;> first
      | exact res_binderDom k (res_forall.mp he).2 h
      | simp [Expr.binderDom] at h

theorem residualPeel_ext {k : Nat} {e : Expr} (he : Res env₁ e) :
    residualPW (peelPisW env₂.find? k e) = residualPW (peelPisW env₁.find? k e) := by
  rw [(peelPisW_ext hx k he).1]

theorem headTypePW_ext {root : Expr} (hr : Res env₁ root) (d : Nat) {h : Expr} (n : Nat)
    (hh : Res env₁ h) :
    headTypePW env₂.find? root d h n = headTypePW env₁.find? root d h n := by
  match h, hh with
  | .const I us, hh =>
    have hs := res_const.mp hh
    simp only [headTypePW]
    rw [hx.find_of_isSome hs]
    cases hf : env₁.find? I with
    | none => rfl
    | some ci =>
      dsimp only
      rw [residualPeel_ext hx (hx.facts.type hf)]
  | .fvar _ ty, hh =>
    simp only [headTypePW]
    exact residualPeel_ext hx (res_fvar.mp hh)
  | .bvar i, _ =>
    simp only [headTypePW]
    split
    · cases hD : root.binderDom (d - 1 - i) with
      | none => rfl
      | some D =>
        dsimp only
        exact residualPeel_ext hx (res_binderDom _ hr hD)
    · rfl
  | .sort _, _ | .app _ _, _ | .lam _ _, _ | .forallE _ _, _ | .letE _ _ _, _
  | .lit _, _ | .proj _ _ _, _ => rfl

theorem typeSortPWGo_ext {root : Expr} (hr : Res env₁ root) :
    ∀ {R : Expr} (d : Nat), Res env₁ R →
      typeSortPWGo env₂.find? root R d = typeSortPWGo env₁.find? root R d
  | .forallE _ b, d, hR => by
    simp only [typeSortPWGo]
    exact typeSortPWGo_ext hr (d + 1) (res_forall.mp hR).2
  | .sort _, _, _ => rfl
  | .bvar _, d, hR | .const _ _, d, hR | .app _ _, d, hR | .lam _ _, d, hR | .letE _ _ _, d, hR
  | .lit _, d, hR | .proj _ _ _, d, hR | .fvar _ _, d, hR => by
    simp only [typeSortPWGo]
    exact headTypePW_ext hx hr d _ (res_getAppFn hR)

theorem typeSortPW_ext {T : Expr} (hT : Res env₁ T) :
    typeSortPW env₂.find? T = typeSortPW env₁.find? T :=
  typeSortPWGo_ext hx hT 0 hT

theorem headProofPW_ext {h : Expr} (hh : Res env₁ h) :
    headProofPW env₂.find? env₂.findTable? h = headProofPW env₁.find? env₁.findTable? h := by
  match h, hh with
  | .const c us, hh =>
    have hs := res_const.mp hh
    simp only [headProofPW]
    rw [hx.find_of_isSome hs]
    cases hf : env₁.find? c with
    | none => rfl
    | some ci =>
      dsimp only
      rw [typeSortPW_ext hx (hx.facts.type hf)]
  | .fvar _ ty, hh =>
    simp only [headProofPW]
    exact typeSortPW_ext hx (res_fvar.mp hh)
  | .sort _, _ | .forallE _ _, _ | .lit _, _ | .bvar _, _ | .app _ _, _ | .lam _ _, _
  | .letE _ _ _, _ => rfl
  | .proj S i _, hh =>
    have hs := (res_proj.mp hh).1
    simp only [headProofPW]
    rw [hx.table S hs]
    cases hT : env₁.findTable? S with
    | none => rfl
    | some tbl =>
      dsimp only
      split
      · rename_i hi
        have hp : env₁.findProj? S i = some (tbl.entry i) := by
          unfold Env.findProj?
          rw [hT]
          exact ite_eq_left hi
        rw [typeSortPW_ext hx (hx.facts.entryBody hp)]
      · rfl

theorem proofPW_ext : ∀ {a : Expr}, Res env₁ a →
    proofPW env₂.find? env₂.findTable? a = proofPW env₁.find? env₁.findTable? a
  | .lam _ b, h => by
    simp only [proofPW]
    exact proofPW_ext (res_lam.mp h).2
  | .letE _ _ b, h => by
    simp only [proofPW]
    exact proofPW_ext (res_let.mp h).2.2
  | .app f _, h => by
    simp only [proofPW]
    exact proofPW_ext (res_app.mp h).1
  | .bvar _, h | .sort _, h | .const _ _, h | .forallE _ _, h | .lit _, h
  | .proj _ _ _, h | .fvar _ _, h => by
    simp only [proofPW]
    exact headProofPW_ext hx h

theorem notProofFast_ext {a : Expr} (h : Res env₁ a) :
    notProofFast env₂.find? env₂.findTable? a = notProofFast env₁.find? env₁.findTable? a := by
  unfold notProofFast
  rw [proofPW_ext hx h]

theorem isProofFast_ext {a : Expr} (h : Res env₁ a) :
    isProofFast env₂.find? env₂.findTable? a = isProofFast env₁.find? env₁.findTable? a := by
  unfold isProofFast
  rw [proofPW_ext hx h]

end Readers

end ConLeche.Verify
