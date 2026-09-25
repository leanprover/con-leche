module

@[expose] public section

/-!
# Universe levels and the level oracle

The fragment keeps Lean's universe levels in full: `zero`, `succ`, `max`,
`imax` and level *parameters*, so that declarations stay universe
polymorphic and the annotation datum (`PropWhen.lean`) can refer to
parameters.  A level means a natural number once every parameter is
given a value — `Level.eval` below — and everything semantic about
levels is stated through `eval`.

**The oracle.**  The checker decides `u ≤ v` and `u = v` between levels
with an algorithm (`Level.isLeq`/`Level.isEquiv` in
`ConLeche/Kernel/Level.lean`).  The fragment does not define it: the
class `LevelOracle` is a *parameter of the development*, assumed sound
and complete for the semantics — exactly what the consistency proof
uses of it and nothing more.  `Level.zeroness`, the one level function
the annotation design needs, IS defined (`PropWhen.lean`), because it
is small and exact.
-/

namespace Fragment

/-- Names, of constants and of level parameters.  Any type with
decidable equality and a decidable total order would do; strings are
the readable choice. -/
abbrev Name := String

/-- Universe levels (`Lean.Level` without `mvar`). -/
inductive Level where
  /-- `Prop`'s level, `0`. -/
  | zero
  /-- The successor level `u + 1`. -/
  | succ (l : Level)
  /-- The maximum `max u v`. -/
  | max (a b : Level)
  /-- The impredicative maximum: `imax u v` is `0` when `v` is `0`,
  else `max u v` — so a `∀` whose codomain is a proposition is a
  proposition whatever its domain's level. -/
  | imax (a b : Level)
  /-- A level parameter of the enclosing declaration. -/
  | param (n : Name)
  deriving DecidableEq, Repr

namespace Level

/-- `imax` on numbers. -/
def imaxNat (a b : Nat) : Nat := if b = 0 then 0 else Max.max a b

/-- The value of a level under a *valuation* `φ` of its parameters. -/
def eval (φ : Name → Nat) : Level → Nat
  | zero => 0
  | succ l => eval φ l + 1
  | max a b => Max.max (eval φ a) (eval φ b)
  | imax a b => imaxNat (eval φ a) (eval φ b)
  | param n => φ n

@[simp] theorem eval_zero (φ : Name → Nat) : eval φ zero = 0 := rfl
@[simp] theorem eval_succ (φ : Name → Nat) (l : Level) :
    eval φ (succ l) = eval φ l + 1 := rfl
@[simp] theorem eval_max (φ : Name → Nat) (a b : Level) :
    eval φ (max a b) = Max.max (eval φ a) (eval φ b) := rfl
@[simp] theorem eval_imax (φ : Name → Nat) (a b : Level) :
    eval φ (imax a b) = imaxNat (eval φ a) (eval φ b) := rfl
@[simp] theorem eval_param (φ : Name → Nat) (n : Name) : eval φ (param n) = φ n := rfl

/-- `imax`'s zero test is its second argument's — the arithmetic behind
the annotation of a `∀`. -/
theorem imaxNat_eq_zero_iff (a b : Nat) : imaxNat a b = 0 ↔ b = 0 := by
  unfold imaxNat
  split <;> omega

theorem imaxNat_of_ne_zero {a b : Nat} (hb : b ≠ 0) : imaxNat a b = Max.max a b :=
  if_neg hb

/-! ## Level substitution

A declaration's level parameters `ps` are instantiated at levels `ls`
when the constant is used (`Infer.const` in `Rules.lean`, the δ step).
A parameter outside `ps` is left alone. -/

/-- The level `ls` assigns to the parameter `n` of `ps` (positionally;
the first occurrence wins), or `param n` itself when `n ∉ ps`. -/
def lookupLevel (ps : List Name) (ls : List Level) (n : Name) : Level :=
  match (ps.zip ls).lookup n with
  | some l => l
  | none => param n

/-- Substitute the parameters `ps` by the levels `ls`. -/
def subst (ps : List Name) (ls : List Level) : Level → Level
  | zero => zero
  | succ l => succ (subst ps ls l)
  | max a b => max (subst ps ls a) (subst ps ls b)
  | imax a b => imax (subst ps ls a) (subst ps ls b)
  | param n => lookupLevel ps ls n

/-- The valuation a substitution amounts to: evaluate each parameter's
substitute under `φ`. -/
def substVal (φ : Name → Nat) (ps : List Name) (ls : List Level) : Name → Nat :=
  fun n => eval φ (lookupLevel ps ls n)

/-- Substitution then evaluation is evaluation under the composed
valuation. -/
theorem eval_subst (φ : Name → Nat) (ps : List Name) (ls : List Level) :
    ∀ l : Level, eval φ (subst ps ls l) = eval (substVal φ ps ls) l
  | zero => rfl
  | succ l => by simp [subst, eval_subst φ ps ls l]
  | max a b => by simp [subst, eval_subst φ ps ls a, eval_subst φ ps ls b]
  | imax a b => by simp [subst, eval_subst φ ps ls a, eval_subst φ ps ls b]
  | param _ => rfl

end Level

/-- **The level oracle** — the checker's decision procedures for `≤` and
`=` on levels, assumed sound and complete with respect to `eval`: a
parameter of the development, never defined here.  (`le` is what the
inductive installs of the environment section consume; the env-free
fragment uses `eq` alone.) -/
class LevelOracle where
  /-- `le u v = true` decides `u ≤ v` at every valuation. -/
  le : Level → Level → Bool
  /-- `eq u v = true` decides `u = v` at every valuation. -/
  eq : Level → Level → Bool
  /-- Soundness and completeness of `le`. -/
  le_iff : ∀ a b : Level, le a b = true ↔ ∀ φ : Name → Nat, Level.eval φ a ≤ Level.eval φ b
  /-- Soundness and completeness of `eq`. -/
  eq_iff : ∀ a b : Level, eq a b = true ↔ ∀ φ : Name → Nat, Level.eval φ a = Level.eval φ b

namespace Level

variable [LevelOracle]

/-- Pairwise oracle equality of two level lists (the level
instantiations of two occurrences of one constant). -/
def eqList : List Level → List Level → Bool
  | [], [] => true
  | a :: as, b :: bs => LevelOracle.eq a b && eqList as bs
  | _, _ => false

/-- What `eqList` decides: the two lists evaluate alike at every
valuation. -/
theorem eqList_iff : ∀ (as bs : List Level),
    eqList as bs = true ↔ ∀ φ : Name → Nat, as.map (eval φ) = bs.map (eval φ)
  | [], [] => by simp [eqList]
  | [], _ :: _ => by simp [eqList]
  | _ :: _, [] => by simp [eqList]
  | a :: as, b :: bs => by
    simp only [eqList, Bool.and_eq_true, List.map_cons, List.cons.injEq,
      LevelOracle.eq_iff, eqList_iff as bs]
    constructor
    · intro ⟨h1, h2⟩ φ
      exact ⟨h1 φ, h2 φ⟩
    · intro h
      exact ⟨fun φ => (h φ).1, fun φ => (h φ).2⟩

end Level

end Fragment
