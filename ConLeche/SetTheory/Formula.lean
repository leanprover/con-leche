module

@[expose] public section

/-!
# First-order syntax over membership and equality

Countable deep embedding `Formula : Nat → Type` (living in `Type 0`,
independent of any universe parameter on the set model `V : Type u`),
together with `Init`-only finite-tuple helpers (`fcons`, `ftail`,
`fappend`) and `ExistsUnique` (which are absent from Lean `v4.36.0` `Init`).

Used by `ConLeche.SetTheory.Core` to state the first-order replacement
schema (`SetTheory.replacement`) and by `ConLeche.SetTheory.Definable`
to build compositional first-order definability witnesses (`DefRel`,
`DefFun`).
-/

namespace ConLeche

universe u

/-- Unique existence: some `x` satisfies `P` and every `y` satisfying
`P` equals `x`. -/
def ExistsUnique {α : Sort u} (P : α → Prop) : Prop :=
  ∃ x, P x ∧ ∀ y, P y → y = x

theorem ExistsUnique.intro {α : Sort u} {P : α → Prop} (x : α) (hx : P x)
    (huniq : ∀ y, P y → y = x) : ExistsUnique P :=
  ⟨x, hx, huniq⟩

theorem ExistsUnique.elim {α : Sort u} {P : α → Prop} {Q : Prop}
    (h : ExistsUnique P) (k : ∀ x, P x → (∀ y, P y → y = x) → Q) : Q :=
  let ⟨x, hx, hu⟩ := h
  k x hx hu

theorem ExistsUnique.exists {α : Sort u} {P : α → Prop} (h : ExistsUnique P) :
    ∃ x, P x :=
  let ⟨x, hx, _⟩ := h
  ⟨x, hx⟩

theorem ExistsUnique.unique {α : Sort u} {P : α → Prop} (h : ExistsUnique P)
    {x y : α} (hx : P x) (hy : P y) : x = y :=
  let ⟨_, _, hu⟩ := h
  (hu x hx).trans (hu y hy).symm

theorem ExistsUnique.congr {α : Sort u} {P Q : α → Prop}
    (h : ∀ x, P x ↔ Q x) : ExistsUnique P ↔ ExistsUnique Q := by
  constructor
  · rintro ⟨x, hx, hu⟩
    exact ⟨x, (h x).mp hx, fun y hy => hu y ((h y).mpr hy)⟩
  · rintro ⟨x, hx, hu⟩
    exact ⟨x, (h x).mpr hx, fun y hy => hu y ((h y).mp hy)⟩

theorem existsUnique_eq {α : Sort u} (x : α) : ExistsUnique fun y => y = x :=
  ⟨x, rfl, fun _ hy => hy⟩

theorem existsUnique_eq' {α : Sort u} (x : α) : ExistsUnique fun y => x = y :=
  ⟨x, rfl, fun _ hy => hy.symm⟩

/-! ### Finite-tuple operations (`Fin n → α`) -/

/-- Prepend `x` at index `0` to an `n`-tuple. -/
def fcons {α : Sort u} {n : Nat} (x : α) (env : Fin n → α) : Fin (n + 1) → α
  | ⟨0, _⟩ => x
  | ⟨i + 1, h⟩ => env ⟨i, Nat.lt_of_succ_lt_succ h⟩

/-- Drop index `0` from an `(n + 1)`-tuple. -/
@[reducible] def ftail {α : Sort u} {n : Nat} (env : Fin (n + 1) → α) : Fin n → α :=
  fun i => env i.succ

/-- Concatenate `xs : Fin k → α` and `ps : Fin p → α` into `Fin (k + p) → α`,
keeping `k + p` canonical. -/
def fappend {α : Sort u} {k p : Nat} (xs : Fin k → α) (ps : Fin p → α) :
    Fin (k + p) → α :=
  fun i =>
    if h : i.val < k then xs ⟨i.val, h⟩
    else ps ⟨i.val - k, Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) i.isLt⟩

@[simp] theorem fcons_zero {α : Sort u} {n : Nat} (x : α) (env : Fin n → α) :
    fcons x env 0 = x := rfl

@[simp] theorem fcons_succ {α : Sort u} {n : Nat} (x : α) (env : Fin n → α)
    (i : Fin n) : fcons x env i.succ = env i := rfl

@[simp] theorem ftail_fcons {α : Sort u} {n : Nat} (x : α) (env : Fin n → α) :
    ftail (fcons x env) = env := rfl

@[simp] theorem ftail_apply {α : Sort u} {n : Nat} (env : Fin (n + 1) → α)
    (i : Fin n) : ftail env i = env i.succ := rfl

theorem fcons_zero_ftail {α : Sort u} {n : Nat} (env : Fin (n + 1) → α) :
    fcons (env 0) (ftail env) = env := by
  funext ⟨k, hk⟩
  cases k with
  | zero => rfl
  | succ k => rfl

@[simp] theorem fappend_left {α : Sort u} {k p : Nat}
    (xs : Fin k → α) (ps : Fin p → α) (i : Fin k) :
    fappend xs ps ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right k p)⟩ = xs i := by
  simp [fappend, i.isLt]

@[simp] theorem fappend_right {α : Sort u} {k p : Nat}
    (xs : Fin k → α) (ps : Fin p → α) (j : Fin p) :
    fappend xs ps ⟨k + j.val, Nat.add_lt_add_left j.isLt k⟩ = ps j := by
  simp [fappend, Nat.not_lt_of_le (Nat.le_add_right k j.val)]

theorem fappend_lt {α : Sort u} {k p : Nat} (xs : Fin k → α) (ps : Fin p → α)
    {i : Fin (k + p)} (hi : i.val < k) :
    fappend xs ps i = xs ⟨i.val, hi⟩ := by
  simp [fappend, hi]

theorem fappend_ge {α : Sort u} {k p : Nat} (xs : Fin k → α) (ps : Fin p → α)
    {i : Fin (k + p)} (hi : k ≤ i.val) :
    fappend xs ps i =
      ps ⟨i.val - k, Nat.sub_lt_left_of_lt_add hi i.isLt⟩ := by
  simp [fappend, Nat.not_lt_of_le hi]

theorem fcons_fappend {α : Sort u} {k p : Nat} (x : α)
    (xs : Fin k → α) (ps : Fin p → α) (i : Fin (k + p + 1)) :
    fcons x (fappend xs ps) i =
      fappend (fcons x xs) ps ⟨i.val, Nat.lt_of_lt_of_eq i.isLt (Nat.succ_add k p).symm⟩ := by
  rcases i with ⟨v, hv⟩
  cases v with
  | zero =>
    change x = fappend (fcons x xs) ps ⟨0, _⟩
    rw [fappend_lt (hi := Nat.zero_lt_succ k)]
    rfl
  | succ v =>
    change fappend xs ps ⟨v, Nat.lt_of_succ_lt_succ hv⟩ =
      fappend (fcons x xs) ps ⟨v + 1, _⟩
    by_cases hvk : v < k
    · rw [fappend_lt (hi := hvk), fappend_lt (hi := Nat.succ_lt_succ hvk)]
      rfl
    · have hle : k ≤ v := Nat.le_of_not_lt hvk
      rw [fappend_ge (hi := hle), fappend_ge (hi := Nat.succ_le_succ hle)]
      have hsub : v - k = v + 1 - (k + 1) := (Nat.succ_sub_succ v k).symm
      congr 1
      exact Fin.ext hsub

@[simp] theorem fappend_zero_right {α : Sort u} {k : Nat}
    (xs : Fin k → α) (ps : Fin 0 → α) : fappend xs ps = xs := by
  funext i
  exact fappend_lt xs ps i.isLt

/-! ### First-order formulas -/

/-- First-order formulas in `n` free variables over set membership and
equality.  Lives in `Type 0`, independent of any set model `V`. -/
inductive Formula : Nat → Type
  | mem     (i j : Fin n) : Formula n
  | eq      (i j : Fin n) : Formula n
  | not     : Formula n → Formula n
  | and     : Formula n → Formula n → Formula n
  | exists_ : Formula (n + 1) → Formula n

namespace Formula

/-- Tarski satisfaction of a `Formula n` in a structure `(V, Mem)` at
variable assignment `env : Fin n → V`. -/
def eval {V : Type u} (Mem : V → V → Prop) :
    {n : Nat} → Formula n → (Fin n → V) → Prop
  | _, .mem i j, env   => Mem (env i) (env j)
  | _, .eq i j, env    => env i = env j
  | _, .not φ, env     => ¬ φ.eval Mem env
  | _, .and φ ψ, env   => φ.eval Mem env ∧ ψ.eval Mem env
  | _, .exists_ φ, env => ∃ x : V, φ.eval Mem (fcons x env)

@[simp] theorem eval_mem {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (i j : Fin n) (env : Fin n → V) :
    (Formula.mem i j).eval Mem env = Mem (env i) (env j) := rfl

@[simp] theorem eval_eq {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (i j : Fin n) (env : Fin n → V) :
    (Formula.eq i j).eval Mem env = (env i = env j) := rfl

@[simp] theorem eval_not {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (φ : Formula n) (env : Fin n → V) :
    (Formula.not φ).eval Mem env = ¬ φ.eval Mem env := rfl

@[simp] theorem eval_and {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (φ ψ : Formula n) (env : Fin n → V) :
    (Formula.and φ ψ).eval Mem env = (φ.eval Mem env ∧ ψ.eval Mem env) := rfl

@[simp] theorem eval_exists {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (φ : Formula (n + 1)) (env : Fin n → V) :
    (Formula.exists_ φ).eval Mem env = ∃ x : V, φ.eval Mem (fcons x env) := rfl

/-- Lift a variable renaming `Fin m → Fin n` under one binder. -/
def liftFin {m n : Nat} (f : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1)
  | ⟨0, _⟩ => 0
  | ⟨i + 1, h⟩ => (f ⟨i, Nat.lt_of_succ_lt_succ h⟩).succ

@[simp] theorem liftFin_zero {m n : Nat} (f : Fin m → Fin n) :
    liftFin f 0 = 0 := rfl

@[simp] theorem liftFin_succ {m n : Nat} (f : Fin m → Fin n) (i : Fin m) :
    liftFin f i.succ = (f i).succ := rfl

theorem fcons_comp_liftFin {α : Sort u} {m n : Nat} (x : α)
    (env : Fin n → α) (f : Fin m → Fin n) :
    (fun i => fcons x env (liftFin f i)) = fcons x (fun i => env (f i)) := by
  funext ⟨k, hk⟩
  cases k with
  | zero => rfl
  | succ k => rfl

/-- Rename free variables along `f : Fin m → Fin n`. -/
def rename {m n : Nat} (f : Fin m → Fin n) : Formula m → Formula n
  | .mem i j   => .mem (f i) (f j)
  | .eq i j    => .eq (f i) (f j)
  | .not φ     => .not (φ.rename f)
  | .and φ ψ   => .and (φ.rename f) (ψ.rename f)
  | .exists_ φ => .exists_ (φ.rename (liftFin f))

theorem eval_rename {V : Type u} (Mem : V → V → Prop) {m n : Nat}
    (f : Fin m → Fin n) (φ : Formula m) (env : Fin n → V) :
    (φ.rename f).eval Mem env ↔ φ.eval Mem (fun i => env (f i)) := by
  induction φ generalizing n with
  | mem i j => rfl
  | eq i j => rfl
  | not φ ih => exact not_congr (ih f env)
  | and φ ψ ih1 ih2 => exact and_congr (ih1 f env) (ih2 f env)
  | exists_ φ ih =>
    simp only [rename, eval_exists]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨x, ?_⟩
      have h := (ih (liftFin f) (fcons x env)).mp hx
      rwa [fcons_comp_liftFin] at h
    · rintro ⟨x, hx⟩
      refine ⟨x, (ih (liftFin f) (fcons x env)).mpr ?_⟩
      rwa [fcons_comp_liftFin]

/-! ### Derived connectives and quantifiers -/

/-- Always-false formula in `n` free variables (even over an empty domain). -/
def falsity {n : Nat} : Formula n := .exists_ (.not (.eq 0 0))

/-- Always-true formula in `n` free variables (even over an empty domain). -/
def truth {n : Nat} : Formula n := .not falsity

/-- Disjunction. -/
def or {n : Nat} (φ ψ : Formula n) : Formula n := .not (.and (.not φ) (.not ψ))

/-- Implication. -/
def imp {n : Nat} (φ ψ : Formula n) : Formula n := .not (.and φ (.not ψ))

/-- Bi-implication. -/
def iff {n : Nat} (φ ψ : Formula n) : Formula n := .and (imp φ ψ) (imp ψ φ)

/-- Universal quantifier. -/
def forall_ {n : Nat} (φ : Formula (n + 1)) : Formula n := .not (.exists_ (.not φ))

@[simp] theorem eval_falsity {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (env : Fin n → V) : (falsity : Formula n).eval Mem env ↔ False := by
  simp [falsity]

@[simp] theorem eval_truth {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (env : Fin n → V) : (truth : Formula n).eval Mem env ↔ True := by
  simp [truth]

@[simp] theorem eval_or {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (φ ψ : Formula n) (env : Fin n → V) :
    (or φ ψ).eval Mem env ↔ φ.eval Mem env ∨ ψ.eval Mem env := by
  simp only [or, eval_not, eval_and]
  exact ⟨fun h => Classical.byContradiction fun hno =>
    h ⟨fun hp => hno (Or.inl hp), fun hq => hno (Or.inr hq)⟩,
    fun h ⟨hnp, hnq⟩ => h.elim hnp hnq⟩

@[simp] theorem eval_imp {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (φ ψ : Formula n) (env : Fin n → V) :
    (imp φ ψ).eval Mem env ↔ (φ.eval Mem env → ψ.eval Mem env) := by
  simp only [imp, eval_not, eval_and]
  exact ⟨fun h hp => Classical.byContradiction fun hnq => h ⟨hp, hnq⟩,
    fun h ⟨hp, hnq⟩ => hnq (h hp)⟩

@[simp] theorem eval_iff {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (φ ψ : Formula n) (env : Fin n → V) :
    (iff φ ψ).eval Mem env ↔ (φ.eval Mem env ↔ ψ.eval Mem env) := by
  simp only [iff, eval_and, eval_imp]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun h => ⟨h.mp, h.mpr⟩⟩

@[simp] theorem eval_forall {V : Type u} (Mem : V → V → Prop) {n : Nat}
    (φ : Formula (n + 1)) (env : Fin n → V) :
    (forall_ φ).eval Mem env ↔ ∀ x : V, φ.eval Mem (fcons x env) := by
  simp only [forall_, eval_not, eval_exists]
  exact ⟨fun h x => Classical.byContradiction fun hnx => h ⟨x, hnx⟩,
    fun h ⟨x, hnx⟩ => hnx (h x)⟩

end Formula

end ConLeche
