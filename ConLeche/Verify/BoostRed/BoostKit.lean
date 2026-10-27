module

public import ConLeche.Verify.BoostRed.Kit

@[expose] public section

/-!
# Boost: the boost translation's library (task #367, used by #368)

The fixed vocabulary the boost translation (`Boost.lean`) instantiates.
Nothing here is searched for: every generated proof is a term built from
these definitions and lemmas by structural recursion over the shallow
kernel term.

* **Saturated relations.** A relation between deep closed terms and
  shallow values of a data type `A` is carried as data, `SatRel env d A`:
  the relation and its closure under backward reduction (`sat`).  A
  δ/β/ι/ζ step on the deep side is then free: `sat` along the step.
  `SatOf core` saturates any `core` by `∃ e₀, Red e e₀ ∧ core e₀ a`.
* **Substitution by a context.** The deep counterpart of a shallow
  subterm under the entered binders `x₁ … xₙ` is `substS σ (enc t) 0`
  with `σ = [xₙd, …, x₁d]` (innermost first): a variable occurrence
  computes to its deep variable, definitionally.  β with a closed
  argument extends the context (`Red.betaS`), ζ likewise (`Red.zetaS`),
  and a spine of β steps over a λ-telescope is `Red.betaSpine`.
* **The primitives.** `Nat` (literal readings), `Bool` (constructor
  constants), their constructors, the recursor views, the literal, and
  the `natOp` operations.
-/

namespace ConLeche.Rules.BoostRed

open ConLeche

/-! ## Saturated relations -/

/-- A relation between deep terms and shallow values of `A`, closed under
backward reduction. -/
structure SatRel (env : Env) (d : Nat) (A : Sort u) : Type u where
  rel : Expr → A → Prop
  sat : ∀ (e e' : Expr) (a : A), Red env d e e' → rel e' a → rel e a

/-- The saturation of a core relation. -/
def SatOf {env : Env} {d : Nat} {A : Sort u} (core : Expr → A → Prop) : SatRel env d A where
  rel e a := ∃ e₀, Red env d e e₀ ∧ core e₀ a
  sat _ _ _ h := fun ⟨e₀, h', hc⟩ => ⟨e₀, Red.trans h h', hc⟩

/-- Closedness, as the generated statements write it. -/
abbrev Closed (e : Expr) : Prop := e.looseBVarsBounded 0 = true

/-! ## Substitution by a context -/

/-- Simultaneous substitution of the context `σ` (innermost first) for
the loose bound variables at and above `k`.  Structural, so it computes
on a concrete term with abstract context entries. -/
def substS (σ : List Expr) : Expr → Nat → Expr
  | .bvar j, k => if j < k then .bvar j else σ.getD (j - k) (.bvar j)
  | .fvar i t, _ => .fvar i t
  | .sort u, _ => .sort u
  | .const n us, _ => .const n us
  | .app f a, k => .app (substS σ f k) (substS σ a k)
  | .lam t b, k => .lam (substS σ t k) (substS σ b (k + 1))
  | .forallE t b, k => .forallE (substS σ t k) (substS σ b (k + 1))
  | .letE t v b, k => .letE (substS σ t k) (substS σ v k) (substS σ b (k + 1))
  | .lit l, _ => .lit l
  | .proj s i e, k => .proj s i (substS σ e k)

/-- Every context entry is closed. -/
def AllClosed : List Expr → Prop
  | [] => True
  | v :: vs => v.looseBVarsBounded 0 = true ∧ AllClosed vs

theorem AllClosed.getD : ∀ {σ : List Expr} (_ : AllClosed σ) {i : Nat} (_ : i < σ.length)
    (dflt : Expr), (σ.getD i dflt).looseBVarsBounded 0 = true
  | [], _, i, hi, _ => absurd hi (Nat.not_lt_zero i)
  | _ :: _, h, 0, _, _ => h.1
  | _ :: vs, h, i + 1, hi, dflt => by
    have := AllClosed.getD (σ := vs) h.2 (i := i) (by simp at hi; omega) dflt
    simpa using this

theorem AllClosed.append : ∀ {σ τ : List Expr}, AllClosed σ → AllClosed τ → AllClosed (σ ++ τ)
  | [], _, _, h => h
  | _ :: _, _, h, h' => ⟨h.1, AllClosed.append h.2 h'⟩

theorem AllClosed.reverse : ∀ {σ : List Expr}, AllClosed σ → AllClosed σ.reverse
  | [], _ => trivial
  | v :: vs, h => by
    rw [List.reverse_cons]
    exact AllClosed.append (AllClosed.reverse h.2) ⟨h.1, trivial⟩

/-- β at the context's next slot: substituting at `k` after the context
at `k + 1` is the context extended by the argument. -/
theorem substS_inst {σ : List Expr} {x : Expr} (hσ : AllClosed σ) (hx : x.looseBVarsBounded 0 = true) :
    ∀ (C : Expr) (k : Nat), C.looseBVarsBounded (k + 1 + σ.length) = true →
      (substS σ C (k + 1)).instantiate1 x k = substS (x :: σ) C k
  | .bvar j, k, h => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    by_cases h1 : j < k
    · simp [substS, Expr.instantiate1, h1, show j < k + 1 by omega, show j ≠ k by omega,
        show ¬ j > k by omega]
    · by_cases h2 : j = k
      · subst h2; simp [substS, Expr.instantiate1]
      · have hj : j - (k + 1) < σ.length := by omega
        have hc := AllClosed.getD hσ hj (.bvar j)
        have hsub : j - k = (j - (k + 1)) + 1 := by omega
        simp only [substS, show ¬ j < k + 1 by omega, h1, ite_false]
        rw [instantiate1_closed x _ k hc, hsub]
        simp
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [substS, Expr.instantiate1]
    rw [substS_inst hσ hx f k h.1, substS_inst hσ hx a k h.2]
  | .lam t b, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [substS, Expr.instantiate1]
    rw [substS_inst hσ hx t k h.1, substS_inst hσ hx b (k + 1) (by
      have := h.2; rwa [show k + 1 + σ.length + 1 = k + 1 + 1 + σ.length by omega] at this)]
  | .forallE t b, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [substS, Expr.instantiate1]
    rw [substS_inst hσ hx t k h.1, substS_inst hσ hx b (k + 1) (by
      have := h.2; rwa [show k + 1 + σ.length + 1 = k + 1 + 1 + σ.length by omega] at this)]
  | .letE t v b, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [substS, Expr.instantiate1]
    rw [substS_inst hσ hx t k h.1.1, substS_inst hσ hx v k h.1.2,
      substS_inst hσ hx b (k + 1) (by
        have := h.2; rwa [show k + 1 + σ.length + 1 = k + 1 + 1 + σ.length by omega] at this)]
  | .proj _ _ e, k, h => by
    simp only [Expr.looseBVarsBounded] at h
    simp only [substS, Expr.instantiate1]
    rw [substS_inst hσ hx e k h]

/-- A substituted term is closed down to its depth. -/
theorem substS_lbb {σ : List Expr} (hσ : AllClosed σ) :
    ∀ (C : Expr) (k : Nat), C.looseBVarsBounded (k + σ.length) = true →
      (substS σ C k).looseBVarsBounded k = true
  | .bvar j, k, h => by
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at h
    by_cases h1 : j < k
    · simp [substS, h1, Expr.looseBVarsBounded]
    · simp only [substS, h1, ite_false]
      exact lbb_atom _ k (AllClosed.getD hσ (by omega) _)
  | .fvar _ _, _, _ | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => rfl
  | .app f a, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [substS, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨substS_lbb hσ f k h.1, substS_lbb hσ a k h.2⟩
  | .lam t b, k, h | .forallE t b, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [substS, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨substS_lbb hσ t k h.1, substS_lbb hσ b (k + 1) (by
      have := h.2; rwa [show k + σ.length + 1 = k + 1 + σ.length by omega] at this)⟩
  | .letE t v b, k, h => by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at h
    simp only [substS, Expr.looseBVarsBounded, Bool.and_eq_true]
    exact ⟨⟨substS_lbb hσ t k h.1.1, substS_lbb hσ v k h.1.2⟩, substS_lbb hσ b (k + 1) (by
      have := h.2; rwa [show k + σ.length + 1 = k + 1 + σ.length by omega] at this)⟩
  | .proj _ _ e, k, h => by
    simp only [Expr.looseBVarsBounded] at h
    simp only [substS, Expr.looseBVarsBounded]
    exact substS_lbb hσ e k h

/-- The deep counterpart of a subterm is closed. -/
theorem substS_closed {σ : List Expr} (hσ : AllClosed σ) (C : Expr)
    (h : C.looseBVarsBounded σ.length = true) : (substS σ C 0).looseBVarsBounded 0 = true :=
  substS_lbb hσ C 0 (by simpa using h)

/-- **β** with a closed argument, at the context. -/
theorem Red.betaS {env : Env} {d : Nat} {σ : List Expr} (hσ : AllClosed σ) (x : Expr)
    (hx : x.looseBVarsBounded 0 = true) (T C : Expr)
    (hC : C.looseBVarsBounded (σ.length + 1) = true) :
    Red env d (.app (substS σ (.lam T C) 0) x) (substS (x :: σ) C 0) := by
  have h := substS_inst hσ hx C 0 (by simpa [Nat.add_comm] using hC)
  rw [← h]
  exact Red.beta

/-- **ζ** with a closed value, at the context. -/
theorem Red.zetaS {env : Env} {d : Nat} {σ : List Expr} (hσ : AllClosed σ) (T V B : Expr)
    (hV : (substS σ V 0).looseBVarsBounded 0 = true)
    (hB : B.looseBVarsBounded (σ.length + 1) = true) :
    Red env d (substS σ (.letE T V B) 0) (substS (substS σ V 0 :: σ) B 0) := by
  have h := substS_inst hσ hV B 0 (by simpa [Nat.add_comm] using hB)
  rw [← h]
  exact Red.zeta

/-- A λ-telescope. -/
def lamN : List Expr → Expr → Expr
  | [], b => b
  | t :: ts, b => .lam t (lamN ts b)

/-- **A spine of β steps** over a λ-telescope with closed arguments. -/
theorem Red.betaSpine {env : Env} {d : Nat} :
    ∀ (tys args σ : List Expr) (body : Expr), tys.length = args.length → AllClosed σ →
      AllClosed args → (lamN tys body).looseBVarsBounded σ.length = true →
      Red env d (Expr.mkAppN (substS σ (lamN tys body) 0) args)
        (substS (args.reverse ++ σ) body 0)
  | [], [], σ, body, _, _, _, _ => by
    show Red env d (substS σ body 0) (substS ([] ++ σ) body 0)
    exact Red.refl
  | [], _ :: _, _, _, h, _, _, _ => by simp at h
  | _ :: _, [], _, _, h, _, _, _ => by simp at h
  | t :: ts, a :: as, σ, body, hlen, hσ, hargs, hlb => by
    simp only [lamN, Expr.looseBVarsBounded, Bool.and_eq_true] at hlb
    have hstep : Red env d (.app (substS σ (.lam t (lamN ts body)) 0) a)
        (substS (a :: σ) (lamN ts body) 0) := Red.betaS hσ a hargs.1 t _ hlb.2
    have ih := Red.betaSpine (env := env) (d := d) ts as (a :: σ) body (by simpa using hlen) ⟨hargs.1, hσ⟩ hargs.2
      (by simpa using hlb.2)
    have heq : (a :: as).reverse ++ σ = as.reverse ++ (a :: σ) := by simp
    rw [heq]
    exact Red.trans (Red.appFnN as hstep) ih

/-! ## `Nat`: literal readings -/

/-- The core of the `Nat` relation: the deep term *is* a literal reading. -/
def natCore (e₀ : Expr) (n : Nat) : Prop := rawNatLit? e₀ = some n

/-- **The `Nat` relation**: the deep term reduces to a literal reading
of the value. -/
def Nat_R (env : Env) (d : Nat) : SatRel env d Nat := SatOf natCore

theorem natLit_R (env : Env) (d : Nat) (n : Nat) :
    (Nat_R env d).rel (.lit (.natVal n)) n := ⟨_, Red.refl, rfl⟩

theorem Nat.zero_R (env : Env) (d : Nat) :
    (Nat_R env d).rel (.const natZeroName []) Nat.zero := ⟨_, Red.refl, rfl⟩

theorem Nat.succ_R (env : Env) (d : Nat) (hs : natLitSupported env = true) :
    ∀ (nd : Expr), nd.looseBVarsBounded 0 = true → ∀ (n : Nat), (Nat_R env d).rel nd n →
      (Nat_R env d).rel (.app (.const natSuccName []) nd) (Nat.succ n) :=
  fun _ _ _ ⟨_, h, hr⟩ => ⟨_, Red.natSucc hs h hr, rfl⟩

/-- The recursor's view of a `Nat` major at `0`. -/
theorem natView0 {env : Env} {d : Nat} (hs : natLitSupported env = true) {td : Expr}
    (h : (Nat_R env d).rel td Nat.zero) : Red env d td (.const natZeroName []) := by
  obtain ⟨e₀, hr, hc⟩ := h
  unfold natCore rawNatLit? at hc
  split at hc
  · cases hc; exact Red.trans hr (Red.natLit (n := 0) hs)
  · rename_i c
    by_cases hz : c = natZeroName
    · subst hz; exact hr
    · simp [hz] at hc
  · cases hc

/-- The recursor's view of a `Nat` major at `n + 1`: its field is the
literal `n`. -/
theorem natViewS {env : Env} {d : Nat} (hs : natLitSupported env = true) {td : Expr} {n : Nat}
    (h : (Nat_R env d).rel td (Nat.succ n)) :
    Red env d td (Expr.mkAppN (.const natSuccName []) [.lit (.natVal n)]) := by
  obtain ⟨e₀, hr, hc⟩ := h
  unfold natCore rawNatLit? at hc
  split at hc
  · cases hc; exact Red.trans hr (Red.natLit (n := n + 1) hs)
  · rename_i c
    by_cases hz : c = natZeroName
    · simp [hz] at hc
    · simp [hz] at hc
  · cases hc

/-! ## `Bool`: constructor constants -/

def boolCore (e₀ : Expr) (b : Bool) : Prop := e₀ = boolE b

/-- **The `Bool` relation**: the deep term reduces to the value's
constructor constant. -/
def Bool_R (env : Env) (d : Nat) : SatRel env d Bool := SatOf boolCore

theorem Bool.true_R (env : Env) (d : Nat) :
    (Bool_R env d).rel (.const boolTrueName []) Bool.true := ⟨_, Red.refl, rfl⟩

theorem Bool.false_R (env : Env) (d : Nat) :
    (Bool_R env d).rel (.const boolFalseName []) Bool.false := ⟨_, Red.refl, rfl⟩

theorem boolViewT {env : Env} {d : Nat} {td : Expr} (h : (Bool_R env d).rel td Bool.true) :
    Red env d td (Expr.mkAppN (.const boolTrueName []) []) := by
  obtain ⟨e₀, hr, hc⟩ := h; cases hc; exact hr

theorem boolViewF {env : Env} {d : Nat} {td : Expr} (h : (Bool_R env d).rel td Bool.false) :
    Red env d td (Expr.mkAppN (.const boolFalseName []) []) := by
  obtain ⟨e₀, hr, hc⟩ := h; cases hc; exact hr

/-! ## The `natOp` primitives -/

theorem natOp_R {env : Env} {d : Nat} (c : Name) (op : Nat → Nat → Nat)
    (hc : c ∈ natBinOpNames) (hst : natOpStored env c = true)
    (hres : ∀ a b, natOpResult c a b = some (.lit (.natVal (op a b)))) :
    ∀ (ad : Expr), ad.looseBVarsBounded 0 = true → ∀ (a : Nat), (Nat_R env d).rel ad a →
    ∀ (bd : Expr), bd.looseBVarsBounded 0 = true → ∀ (b : Nat), (Nat_R env d).rel bd b →
      (Nat_R env d).rel (.app (.app (.const c []) ad) bd) (op a b) :=
  fun _ _ _ ⟨_, ha, hra⟩ _ _ _ ⟨_, hb, hrb⟩ =>
    ⟨_, Red.natOp hc hst ha hra hb hrb (hres _ _), rfl⟩

theorem natOpB_R {env : Env} {d : Nat} (c : Name) (op : Nat → Nat → Bool)
    (hc : c ∈ natBinOpNames) (hst : natOpStored env c = true)
    (hres : ∀ a b, natOpResult c a b = some (boolE (op a b))) :
    ∀ (ad : Expr), ad.looseBVarsBounded 0 = true → ∀ (a : Nat), (Nat_R env d).rel ad a →
    ∀ (bd : Expr), bd.looseBVarsBounded 0 = true → ∀ (b : Nat), (Nat_R env d).rel bd b →
      (Bool_R env d).rel (.app (.app (.const c []) ad) bd) (op a b) :=
  fun _ _ _ ⟨_, ha, hra⟩ _ _ _ ⟨_, hb, hrb⟩ =>
    ⟨_, Red.natOp hc hst ha hra hb hrb (hres _ _), rfl⟩

/-- The statement shape of a binary `Nat → Nat → Nat` primitive. -/
def NatOpStmt (env : Env) (d : Nat) (c : Name) (op : Nat → Nat → Nat) : Prop :=
  ∀ (ad : Expr), ad.looseBVarsBounded 0 = true → ∀ (a : Nat), (Nat_R env d).rel ad a →
  ∀ (bd : Expr), bd.looseBVarsBounded 0 = true → ∀ (b : Nat), (Nat_R env d).rel bd b →
    (Nat_R env d).rel (.app (.app (.const c []) ad) bd) (op a b)

/-- The statement shape of a binary `Nat → Nat → Bool` primitive. -/
def NatOpBStmt (env : Env) (d : Nat) (c : Name) (op : Nat → Nat → Bool) : Prop :=
  ∀ (ad : Expr), ad.looseBVarsBounded 0 = true → ∀ (a : Nat), (Nat_R env d).rel ad a →
  ∀ (bd : Expr), bd.looseBVarsBounded 0 = true → ∀ (b : Nat), (Nat_R env d).rel bd b →
    (Bool_R env d).rel (.app (.app (.const c []) ad) bd) (op a b)

private theorem mem_ops {c : Name} (h : c ∈ [natAddName, natSubName, natMulName, natPowName,
    natBeqName, natBleName] ∨ c ∈ natDivModNames) : c ∈ natBinOpNames := by
  unfold natBinOpNames; simp only [List.mem_append]; exact h

theorem Nat.add_R (env : Env) (d : Nat) (hst : natOpStored env natAddName = true) :
    NatOpStmt env d natAddName Nat.add :=
  natOp_R (env := env) (d := d) natAddName Nat.add (mem_ops (by simp)) hst
    (fun _ _ => rfl)

theorem Nat.sub_R (env : Env) (d : Nat) (hst : natOpStored env natSubName = true) :
    NatOpStmt env d natSubName Nat.sub :=
  natOp_R (env := env) (d := d) natSubName Nat.sub (mem_ops (by simp)) hst
    (fun _ _ => rfl)

theorem Nat.mul_R (env : Env) (d : Nat) (hst : natOpStored env natMulName = true) :
    NatOpStmt env d natMulName Nat.mul :=
  natOp_R (env := env) (d := d) natMulName Nat.mul (mem_ops (by simp)) hst
    (fun _ _ => rfl)

theorem Nat.div_R (env : Env) (d : Nat) (hst : natOpStored env natDivName = true) :
    NatOpStmt env d natDivName Nat.div :=
  natOp_R (env := env) (d := d) natDivName Nat.div (mem_ops (by simp [natDivModNames])) hst
    (fun _ _ => rfl)

theorem Nat.mod_R (env : Env) (d : Nat) (hst : natOpStored env natModName = true) :
    NatOpStmt env d natModName Nat.mod :=
  natOp_R (env := env) (d := d) natModName Nat.mod (mem_ops (by simp [natDivModNames])) hst
    (fun _ _ => rfl)

private theorem beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

private theorem ble_false {a b : Nat} (h : ¬ a ≤ b) : Nat.ble a b = false := by
  cases hb : Nat.ble a b
  · rfl
  · exact absurd (Nat.le_of_ble_eq_true hb) h

theorem Nat.beq_R (env : Env) (d : Nat) (hst : natOpStored env natBeqName = true) :
    NatOpBStmt env d natBeqName Nat.beq :=
  natOpB_R (env := env) (d := d) natBeqName Nat.beq (mem_ops (by simp)) hst
    (fun a b => by
      show some (Expr.const (if a = b then boolTrueName else boolFalseName) []) = _
      by_cases h : a = b
      · subst h; simp [boolE, Nat.beq_refl]
      · simp [h, boolE, beq_false h])

theorem Nat.ble_R (env : Env) (d : Nat) (hst : natOpStored env natBleName = true) :
    NatOpBStmt env d natBleName Nat.ble :=
  natOpB_R (env := env) (d := d) natBleName Nat.ble (mem_ops (by simp)) hst
    (fun a b => by
      show some (Expr.const (if a <= b then boolTrueName else boolFalseName) []) = _
      by_cases h : a ≤ b
      · simp [h, boolE, Nat.ble_eq_true_of_le h]
      · simp [h, boolE, ble_false h])

end ConLeche.Rules.BoostRed
